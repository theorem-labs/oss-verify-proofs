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
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/A/Prog/CPgWalk.v; 312 of its 358 lines of code are new or changed and 587 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/A/Prog/check_bytes_A.v, with its module paths and module names changed; 198 of its 243 lines of code are new or changed and 313 lines of the source are left out. *)
(* diginet_fader_encode at image B 0x8540c (116 instructions, frame 16, no call) against lib/AU/Prog/CPgEncU.v's
   cdcU_fader_specX. a0 = p, a1 = strip, a2 = value (both as lw loads them), a3 = out.
   The image-A walk's paths (lib/A/Prog/diginet_fader_encode_A.v) with image B's addresses; image B adds three UBSan
   checks, each decided by the engine from the entry facts:
   - 0x85424 andi a0,a4,7; bnez a0 (p not 8-aligned): atom 10's fact in pers_AF says p mod 8 = 0;
   - 0x85460 andi a0,a3,3; bnez a0 (out not 4-aligned): out's atom fact ceo_fact says out mod 4 = 0;
   - 0x854d4 bgeu a3,a4 with a4 = -4 (out + 4 wraps): out's atom fact puts out at or below 0x7fffff800000.
   Each traps at 0x8555c (unimp), which no path reaches.
   0x8540c addi sp,sp,-16; sd ra,8(sp): the only store outside out, into the save area [sp - 16, sp).
   pd = None (p = 0): 0x8541c beqz a4 is undecided (atom 10 has no fact); TAKEN it returns a0 = -1 = E_ARG with
     nothing written; not taken is refuted by p = 0 (pers_beqz0).
   pd = Some d: the entry facts decide both beqz, the alignment check of p and the check of p + 17 (shadow entry
   mkSHE 10 16 20); the engine stops at
   B1 0x85454 bltu a6,a2 (1023 < value). Before it the two loads of the shadow offset are done, so the walk drops the
     two cells and adds the byte p + 17 (pers_swap_tac). TAKEN: a0 = -11 = E_RANGE, nothing written.
   B2 0x8545c bgeu a1,a4 with a4 = the byte p->strips (atom 33): strips <= strip (pers_strip_ltu).
     TAKEN: a0 = -11, nothing written. not taken: the three write windows of out enter the state (ceo_add3) and the
     run reaches `ret` with out[0..5) = 0xb0, strip, value >> 3, strip + 32, (value mod 8) << 4, out[24] = 5,
     out[25] = 0, out[28..32) = strip | 0x10000 = KEY 1 strip and a0 = 0. Every instrumented check of out is decided
     by the shadow entry mkSHE 13 0 32 of cenc_out's cdst_ok. *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
(* the spec first: DgnLib's st_ok (a running status) must not hide the engine's st_ok *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw0 YCef YF0l YCej YCeh YCem YCep.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw1 AWalkFw2 YCfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase CPgEncC.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import CPgBaseU CPgEncU CPgWalkU CPgEncOutU CPgEncPersU.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ================================ the arithmetic of the bytes ================================ *)
Lemma fd_s32 : forall v, 0 <= v < 2 ^ 31 -> DgnLib.s32 v = v.
Proof. intros v Hv. unfold DgnLib.s32. destruct (Z.ltb_spec v (2 ^ 31)); [reflexivity | lia]. Qed.
(* `bltu c, a2` with c a small constant and a2 the lw register of value: taken exactly when c < value *)
Lemma fd_ltu_val : forall v c, 0 <= v < 2 ^ 32 -> 0 <= c < 2 ^ 31 ->
(c <? (if v <? 2 ^ 31 then v else v + (2 ^ 64 - 2 ^ 32))) = (c <? v).
Proof.
intros v c Hv Hc. destruct (Z.ltb_spec v (2 ^ 31)); [reflexivity|].
destruct (Z.ltb_spec c (v + (2 ^ 64 - 2 ^ 32))); destruct (Z.ltb_spec c v); first [reflexivity | lia].
Qed.
(* out[1] = strip, out[3] = strip + 32 *)
Lemma fd_byte_strip : forall E strip c, ew E 11 = w64 (DgnLib.s32 strip) -> 0 <= strip < 256 ->
U E (SOff 11 c) mod 256 = u8 (strip + c) mod 256.
Proof.
intros E strip c H Hs. unfold w64 in H. rewrite (fd_s32 strip) in H by lia.
rewrite (ceo_U_off E 11 strip c H). unfold u8. rewrite Z.mod_mod by lia. reflexivity.
Qed.
(* out[2] = value >> 3 (srliw of the lw register) *)
Lemma fd_byte_v8 : forall E value, ew E 12 = w64 (DgnLib.s32 value) -> 0 <= value <= 1023 ->
U E (SAluw ALU_SRL (SOff 12 0) (SLit 3)) mod 256 = u8 (value / 8) mod 256.
Proof.
intros E value H Hv. unfold w64 in H. rewrite (fd_s32 value) in H by lia.
rewrite U_of_S, S_SAluw. cbn [zalu_raw]. rewrite (U_atom E 12 value H), U_lit by lia.
rewrite (Z.mod_small value), (Z.mod_small 3) by lia. change (Z.land 3 31) with 3.
rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
pose proof (Z.div_pos value 8 ltac:(lia) ltac:(lia)) as Q0.
assert (Q1 : value / 8 < 128) by (apply Z.div_lt_upper_bound; lia).
rewrite bv_swrap_small by (change (bv_half_modulus 32) with (2 ^ 31); lia).
unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite (Z.mod_small (value / 8)) by lia.
unfold u8. rewrite Z.mod_mod by lia. reflexivity.
Qed.
(* out[4] = (value mod 8) << 4 (slli 61; srli 57) *)
Lemma fd_byte_v4 : forall E value, ew E 12 = w64 (DgnLib.s32 value) -> 0 <= value <= 1023 ->
U E (SAlu ALU_SRL (SAlu ALU_SLL (SOff 12 0) (SLit 61)) (SLit 57)) mod 256 = u8 ((value mod 8) * 16) mod 256.
Proof.
intros E value H Hv. unfold w64 in H. rewrite (fd_s32 value) in H by lia.
rewrite !U_SAlu. cbn [zalu_raw]. rewrite (U_atom E 12 value H), !U_lit by lia.
change (Z.land 61 63) with 61. change (Z.land 57 63) with 57. unfold zcanon, M64.
rewrite Z.shiftl_mul_pow2 by lia.
assert (X : (value * 2 ^ 61) mod 2 ^ 64 = (value mod 8) * 2 ^ 61)
by (change (2 ^ 64) with (8 * 2 ^ 61); apply Z.mul_mod_distr_r; lia).
rewrite X. rewrite Z.shiftr_div_pow2 by lia.
pose proof (Z.mod_pos_bound value 8 ltac:(lia)) as M.
replace ((value mod 8) * 2 ^ 61) with ((value mod 8) * 16 * 2 ^ 57) by lia.
rewrite Z.div_mul by lia. rewrite (Z.mod_small ((value mod 8) * 16)) by lia.
unfold u8. rewrite Z.mod_mod by lia. reflexivity.
Qed.
(* out[28..32) = strip | 0x10000 = KEY 1 strip *)
Lemma fd_key : forall E strip, ew E 11 = w64 (DgnLib.s32 strip) -> 0 <= strip < 256 ->
U E (SAlu ALU_OR (SOff 11 0) (SLit 65536)) mod 2 ^ 32 = KEY 1 strip mod 2 ^ 32.
Proof.
intros E strip H Hs. unfold w64 in H. rewrite (fd_s32 strip) in H by lia.
rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E 11 strip H), U_lit by lia.
unfold KEY, zcanon, M64. change (1 * 65536) with 65536.
change 0xffff with (Z.ones 16). rewrite Z.land_ones by lia. rewrite (Z.mod_small strip (2 ^ 16)) by lia.
rewrite (Z.lor_comm strip 65536).
apply Z.mod_mod_divide. exists (2 ^ 32). reflexivity.
Qed.
Lemma fd_spec_ok : forall d strip value, strip < d_strips d -> value <= 1023 ->
fader_spec (Some d) strip value =
(0, Some ([0xb0; u8 strip; u8 (value / 8); u8 (0x20 + strip); u8 ((value mod 8) * 16)], KEY 1 strip, 0)).
Proof.
intros d strip value Hs Hv. cbn [fader_spec].
rewrite (proj2 (Z.leb_gt _ _) Hs), (proj2 (Z.ltb_ge _ _) Hv). reflexivity.
Qed.
Lemma fd_spec_fail : forall d strip value, d_strips d <= strip \/ 1023 < value ->
fader_spec (Some d) strip value = (E_RANGE, None).
Proof.
intros d strip value H. cbn [fader_spec].
destruct (Z.leb_spec (d_strips d) strip); [reflexivity|]. destruct (Z.ltb_spec 1023 value); [reflexivity | lia].
Qed.

(* ================================ the walk's tactics ================================ *)
(* one run, with sp read in the run's env (through the layers of earlier runs) for the save-area window *)
Ltac fd_run awr :=
repeat match goal with H : bv_unsigned (ew (ewset _ _ _) 2) = _ |- _ => clear H end;
lazymatch goal with HS : st_ok _ ?E _ _, B2 : bv_unsigned (ew _ 2) = spZ ?rg |- _ =>
lazymatch goal with _ : bv_unsigned (ew E 2) = _ |- _ => idtac | _ =>
let B2r := fresh "B2r" in assert (B2r : bv_unsigned (ew E 2) = spZ rg) by (pers_ew_base; exact B2) end end;
cw_run awr.
(* a failing return: run to `ret`, nothing written; Hspec : fader_spec .. = (rc, None) *)
Ltac fd_fail HJ0 KE eimg Hspec Hcw HG HL :=
fd_run cw_awr_stk; cw_keep cw_kwr_stk;
repeat match goal with H : bv_unsigned (ew (ewset _ _ _) 2) = _ |- _ => clear H end;
cw_leaf ltac:(idtac; cw_kept HJ0 KE eimg ltac:(intros ? Ha; cbv beta in Ha; unfold cenc_wr; lia)) idtac;
rewrite Hspec;
lazymatch goal with R10 : getr _ _ = _ |- cenc_res _ ?o ?bf (?rcv, None) ?W _ _ =>
  apply (ceo_res_fail W _ _ _ o bf _ rcv HG HL ltac:(lia) ltac:(lia) Hcw KE); ceo_a0 R10 end.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.

Theorem diginet_fader_encode_B_holds : cdcU_fader_specX tfibsegs B MT 0x8540c.
Proof using MTL TL LAWS.
unfold cdcU_fader_specX.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs pd p strip value out before
HE H10 HP Hpal H11 H12 H13 Hoal HO HD.
pose proof Hwx_tfa as Hwx. pose proof tfib_segs_low as Hsegs.
pose proof HE as HE0.
destruct HE as (HJ0 & Hra & Hra4 & Hgp & Htp & Hal16 & Hwlo & Hwhi & Hev & Hlive).
(* the entry journal stays as HJ0 (older); the runs take the newest journal, HJ *)
pose proof (proj1 HJ0) as HAR. pose proof HJ0 as HJ.
unfold TB_fader in *.
destruct H11 as (Hs0 & H11). destruct H12 as (Hv0 & H12).
pose proof HO as (Hdst & Hbef & Hlen).
pose proof Hdst as (Hout0 & Hout1 & Htd & Htw & _ & _ & Hoam & Hocw).
unfold coff_win in Hocw.
change (w64 out) with (Z_to_bv 64 out) in H13.
destruct pd as [d|].
- (* ======== pd = Some d ======== *)
  pose proof (pers_some B W memc (spZ regs) 16 p d HP) as (Hp & Hstr & Hbyte & Hpwin & Hcimg).
  pose proof (pers_off_zone B W memc (spZ regs) 16 p d out 32 HP HD) as [Zp1 Zp2].
  cbn [cpers_disj] in HD.
  change (w64 p) with (Z_to_bv 64 p) in H10.
  set (xs := [d_strips d]).
  assert (HAF : atoms_ok (Ereg regs (cw_extra xs)) (pers_AF 33)).
  { apply (pers_atoms_ok _ 33 p (d_strips d)); [rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10
    | exact (cw_ew_x regs xs 0) | exact Hp | exact Hpal | exact Hstr]. }
  pose proof (ceo_entry B TL LAWS 0x8540c xs 13 (13%bv) (pers_AF 33) STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc
    k regs 16 out HE0 ltac:(lia) eq_refl H13 Hoal Hdst HAF) as HS.
  remember (Ereg regs (cw_extra xs)) as E eqn:HEE.
  assert (HAE : env_agree 32 (Ereg regs (cw_extra xs)) E) by (subst E; apply env_agree_refl).
  assert (E1 : ew E 1 = getr regs 1%bv) by (subst E; exact (cw_ew_reg regs _ 1 1%bv eq_refl)).
  assert (B2 : bv_unsigned (ew E 2) = spZ regs) by (subst E; rewrite (cw_ew_reg regs _ 2 2%bv eq_refl); reflexivity).
  assert (E10 : ew E 10 = Z_to_bv 64 p) by (subst E; rewrite (cw_ew_reg regs _ 10 10%bv eq_refl); exact H10).
  assert (E11 : ew E 11 = w64 (DgnLib.s32 strip)) by (subst E; rewrite (cw_ew_reg regs _ 11 11%bv eq_refl); exact H11).
  assert (E12 : ew E 12 = w64 (DgnLib.s32 value)) by (subst E; rewrite (cw_ew_reg regs _ 12 12%bv eq_refl); exact H12).
  assert (E13 : ew E 13 = Z_to_bv 64 out) by (subst E; rewrite (cw_ew_reg regs _ 13 13%bv eq_refl); exact H13).
  assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; apply cw_ew_SB).
  assert (E33 : ew E 33 = Z_to_bv 64 (d_strips d)) by (subst E; exact (cw_ew_x regs xs 0)).
  assert (B10 : bv_unsigned (ew E 10) = p) by (rewrite E10; apply unsigned_lit_small; unfold PERS_HI in Hp; lia).
  assert (BO : bv_unsigned (ew E 13) = out) by (rewrite E13; apply unsigned_lit_small; lia).
  clear HEE.
  assert (SHOK : sh_ok tfibsegs CW_Bx [mkSHE 13 0 32; pers_SH] E (mrestrict (w_H W) memc)).
  { apply Forall_cons; [exact (cw_shent_cdst B STK sp0 FP ly S lyc Sc own W memc (spZ regs) 16 E 13 out 32 Hdst E13 E32 ltac:(lia))|].
    apply Forall_cons; [exact (pers_shent B lyc Sc W memc mdc (spZ regs) 16 E p d HAR HP E10 E32) | apply Forall_nil]. }
  assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 16 <= a < spZ regs) ->
    aview tfibsegs (w_H W) memc a = aview tfibsegs (w_H W) memc a) by (intros; reflexivity).
  unfold cfg_at. change (w64 0x8540c) with (Z_to_bv 64 0x8540c).
  (* 0x8540c .. 0x85450: the save of ra, both beqz and the alignment check of p decided, the shadow offset through
     the .got slot and the cell, the check of p + 17 (mkSHE 10 16 20); stop at 0x85454 bltu a6,a2 *)
  fd_run cw_awr_stk. cw_keep cw_kwr_stk.
  (* the two cells for the byte p + 17 *)
  pers_swap_tac E10 E33 Hbyte ltac:(apply KE; unfold PERS_HI in Hp; lia) pers_disj.
  cw_branch Hb1.
  all: rewrite branch_ltu_U, U_lit in Hb1 by lia.
  all: lazymatch type of Hb1 with context [U ?Ex (SOff 12 0)] =>
    rewrite (pers_U_u32 Ex 12 value ltac:(pers_ew_base; exact E12) Hv0), fd_ltu_val in Hb1 by lia end.
  + (* TAKEN: 1023 < value, to 0x85550 with a0 = -11 *)
    apply Z.ltb_lt in Hb1.
    fd_fail HJ0 KE
      ltac:(intros a Ha Him; exact (ceo_eimg B LAWS STK sp0 FP ly S lyc Sc own W memc mdc (spZ regs) 16 out a HAR Hdst Ha Him))
      (fd_spec_fail d strip value (or_intror Hb1)) Hocw Hbef Hlen.
  + (* value <= 1023: lbu a4 of p + 17 (atom 33), stop at 0x8545c bgeu a1,a4 *)
    apply Z.ltb_ge in Hb1.
    fd_run cw_awr_stk. cw_keep cw_kwr_stk.
    cw_branch Hb2.
    all: rewrite branch_geu_U in Hb2.
    all: lazymatch type of Hb2 with context [U ?Ex (SOff 11 0) <? U ?Ex ?x] =>
      rewrite (pers_strip_ltu Ex 11 strip x (d_strips d) ltac:(pers_ew_base; exact E11) Hs0
        (proj2 (pers_U_byte Ex 33 _ ltac:(pers_ew_base; exact E33) Hstr)) Hstr) in Hb2 end.
    * (* TAKEN: strips <= strip, to 0x85550 with a0 = -11 *)
      apply negb_true_iff, Z.ltb_ge in Hb2.
      fd_fail HJ0 KE
        ltac:(intros a Ha Him; exact (ceo_eimg B LAWS STK sp0 FP ly S lyc Sc own W memc mdc (spZ regs) 16 out a HAR Hdst Ha Him))
        (fd_spec_fail d strip value (or_introl Hb2)) Hocw Hbef Hlen.
    * (* strip < strips: out's three windows enter the state, then the stores *)
      apply negb_false_iff, Z.ltb_lt in Hb2.
      lazymatch goal with HS0 : st_ok _ ?Ex ?ss (restrict (w_H W) ?ms) |- _ =>
        pose proof (ceo_add3 B LAWS STK sp0 FP ly S lyc Sc own W memc mdc (spZ regs) 16 Ex ss ms 13 out 5 HAR Hdst HS0
          ltac:(pers_ew_base; exact BO) ltac:(lia) ltac:(intros a Ha; apply KE; lia)
          ltac:(ceo_disj ltac:(lia)) ltac:(ceo_disj ltac:(lia)) ltac:(ceo_disj ltac:(lia))) as HS1;
        clear HS0; rename HS1 into HS end.
      pose proof (ceo_KE_widen _ _ _ (spZ regs) out 5 KE) as KE1. clear KE. rename KE1 into KE.
      (* 0x85460 .. 0x85558: the alignment check of out, the overflow check of out + 4 and the checks of out (decided by
         ceo_fact and mkSHE 13 0 32), the eight stores; stop at ret *)
      fd_run ltac:(ceo_awr Htw). cw_keep ceo_kwr.
      repeat match goal with H : bv_unsigned (ew (ewset _ _ _) 2) = _ |- _ => clear H end.
      cw_leaf ltac:(idtac; cw_kept HJ0 KE
          ltac:(intros a Ha Him; exact (ceo_eimg B LAWS STK sp0 FP ly S lyc Sc own W memc mdc (spZ regs) 16 out a HAR Hdst Ha Him))
          ltac:(intros a Ha; cbv beta in Ha; unfold cenc_wr; unfold ceo_zone in Ha; lia))
        idtac.
      rewrite (fd_spec_ok d strip value Hb2 Hb1). unfold cenc_res. cbn [fst snd].
      split; [ceo_a0 R10|].
      lazymatch goal with HS0 : st_ok _ _ _ _ |- _ => ceo_chunks HS0 end.
      eapply (ceo_res_ok _ memc _ out before [0xb0; u8 strip; u8 (value / 8); u8 (0x20 + strip); u8 ((value mod 8) * 16)]
        (KEY 1 strip) 0 Hlen ltac:(cbn; lia) Hbef).
      -- intros j Hj. cbn [length] in Hj.
         destruct j as [|[|[|[|[|j]]]]]; [| | | | | lia]; cbn [nth Z.of_nat Pos.of_succ_nat Pos.succ];
         (eapply ceo_chunk1; [eassumption|]).
         ++ rewrite U_lit by lia. reflexivity.
         ++ lazymatch goal with |- U ?Ex _ mod _ = _ =>
              rewrite (fd_byte_strip Ex strip 0 E11 ltac:(lia)), Z.add_0_r; reflexivity end.
         ++ lazymatch goal with |- U ?Ex _ mod _ = _ => exact (fd_byte_v8 Ex value E12 ltac:(lia)) end.
         ++ lazymatch goal with |- U ?Ex _ mod _ = _ =>
              rewrite (fd_byte_strip Ex strip 32 E11 ltac:(lia)); replace (strip + 32) with (0x20 + strip) by lia;
              reflexivity end.
         ++ lazymatch goal with |- U ?Ex _ mod _ = _ => exact (fd_byte_v4 Ex value E12 ltac:(lia)) end.
      -- eapply ceo_chunk1; [eassumption|]. rewrite U_lit by lia. reflexivity.
      -- eapply ceo_chunk1; [eassumption|]. rewrite U_lit by lia. reflexivity.
      -- intros j Hj. eapply ceo_chunk4; [eassumption | | exact Hj].
         lazymatch goal with |- U ?Ex _ mod _ = _ => exact (fd_key Ex strip E11 ltac:(lia)) end.
      -- intros a Ha.
         change (Z.of_nat (length [0xb0; u8 strip; u8 (value / 8); u8 (0x20 + strip); u8 ((value mod 8) * 16)])) with 5 in Ha.
         apply KE; [lia | unfold ceo_zone; lia].
- (* ======== pd = None: p = 0 ======== *)
  pose proof (pers_none_p tfibsegs B W memc (spZ regs) 16 p HP) as Hp0. subst p.
  pose proof (cw_entry_base B TL LAWS 0x8540c 16 [] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs 16
    HE0 ltac:(lia) eq_refl) as HS.
  remember (Ereg regs (cw_extra [])) as E eqn:HEE.
  assert (HAE : env_agree 32 (Ereg regs (cw_extra [])) E) by (subst E; apply env_agree_refl).
  assert (E1 : ew E 1 = getr regs 1%bv) by (subst E; exact (cw_ew_reg regs _ 1 1%bv eq_refl)).
  assert (B2 : bv_unsigned (ew E 2) = spZ regs) by (subst E; rewrite (cw_ew_reg regs _ 2 2%bv eq_refl); reflexivity).
  assert (E10 : ew E 10 = Z_to_bv 64 0) by (subst E; rewrite (cw_ew_reg regs _ 10 10%bv eq_refl); exact H10).
  clear HEE.
  assert (SHOK : sh_ok tfibsegs CW_Bx [] E (mrestrict (w_H W) memc)) by constructor.
  assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 16 <= a < spZ regs) ->
    aview tfibsegs (w_H W) memc a = aview tfibsegs (w_H W) memc a) by (intros; reflexivity).
  unfold cfg_at. change (w64 0x8540c) with (Z_to_bv 64 0x8540c).
  (* 0x8540c .. 0x85418; stop at 0x8541c beqz a4 *)
  fd_run cw_awr_stk. cw_keep cw_kwr_stk.
  cw_branch Hb0.
  + (* TAKEN (p = 0): to 0x85550, a0 = -1 *)
    clear Hb0.
    fd_fail HJ0 KE
      ltac:(intros a Ha Him; exact (ceo_eimg B LAWS STK sp0 FP ly S lyc Sc own W memc mdc (spZ regs) 16 out a HAR Hdst Ha Him))
      (@eq_refl _ (E_ARG, None) : fader_spec None strip value = (E_ARG, None)) Hocw Hbef Hlen.
  + (* not taken: refuted, atom 10 is p = 0 *)
    exfalso. lazymatch type of Hb0 with branch_taken _ (sv_denot ?Ex _) _ = _ =>
    rewrite (pers_beqz0 Ex ltac:(pers_ew_base; exact E10)) in Hb0; discriminate Hb0 end.
Qed.
End d.
End b.
