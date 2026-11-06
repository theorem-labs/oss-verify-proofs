(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: proofs/libreac/fuzz_knock/lib/A/APgRt.v (rt_hand, fs_roF / fs_rwF) and
   APgStep.v (same_io_wvb) at 6ebe35ba632; adapted to the class-0 frame and the exit of reac_box_pin_parse. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_pin/lib/A/PPgParse4.v, with its module paths and module names changed; 262 of its 291 lines of code are new or changed and 251 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/A/Prog/check_personality_A.v, with its module paths and module names changed; 185 of its 215 lines of code are new or changed and 261 lines of the source are left out. *)
(* diginet_vpot_encode, image B 0x85914, 94 instructions, against lib/AU/Prog/CPgEncU.v's cdcU_vpot_specX.
   a0 = p (the personality), a1 = strip (arg_u32A: w64 (s32 strip)), a2 = delta (arg_s32A), a3 = out. The walk
   starts from `Ereg regs (cw_extra xs)` (atom 32 = SB, the shadow offset; atom 33 = p->strips when pd = Some d)
   with the base regions of lib/AU/Prog/CPgWalkU.v and no region for out or the personality. The image-A walk's
   paths (lib/A/Prog/diginet_vpot_encode_A.v) with image B's addresses; image B adds two UBSan checks, each trapping
   at 0x85a24 (unimp), each decided by the engine from the entry facts: 0x8592c andi a0,a4,7; bnez a0 (p not
   8-aligned; atom 10's fact in pers_AF) and 0x8596c andi a0,a3,3; bnez a0 (out not 4-aligned; ceo_fact 13).
   Paths of the listing:
   0x85914 addi sp,sp,-16; sd ra,8(sp) (the save slot [sp - 16, sp), the only stack write); mv a4,a0; li a0,-1.
   0x85924 beqz a4 -- p = 0 (pd = None): TAKEN to 0x85a18, a0 = -1 = E_ARG, out unchanged. With pd = Some d the
      engine decides it not taken (atom 10 >= 1).
   0x85928 beqz a3 -- out = 0: the engine decides it not taken (out's atom fact, from cdst_ok).
   0x85934-0x8593c the shadow offset: ld of the .got slot 0x9e430, ld of the cell it holds (holds SB).
   0x85940-0x85950 the instrumented check before the 1-byte load of p + 17: the engine decides it from the shadow
      entry of [p + 16, p + 20) (pers_argA's cimg_range); errpath_load1 is not reached.
   0x85954 addiw a6,a2,-64; li a7,-128; li a0,-11; 0x85960 bltu a6,a7 -- the delta test, the first stop: TAKEN
      exactly when delta < -64 or 63 < delta (vp_delta_U), to 0x85a18 with a0 = -11 = E_RANGE, out unchanged.
      At this stop the regions of the .got slot and the cell are dropped and the byte p + 17 is added
      (pers_swap_tac): the personality may lie on those two cells.
   0x85964 lbu a4,0(a4) -- p->strips = d_strips d (atom 33); 0x85968 bgeu a1,a4 -- the strip test: TAKEN exactly
      when d_strips d <= strip (pers_strip_ltu; a strip >= 2 ^ 31 is sign-extended, so the unsigned compare sees it
      as large), to 0x85a18 with a0 = -11, out unchanged.
   Not taken: the three write windows of out are added (ceo_add3: out[0..3), out[24..26), out[28..32)).
   0x8596c-0x85a14 the alignment check of out, the six instrumented checks of out, out + 1, out + 2, out + 24,
      out + 25 (1-byte stores) and out + 28 (4-byte store), each decided from out's shadow entry (cenc_out's
      cdst_ok), and the stores: out[0] = 0xb0, out[1] = (strip | 0x40) mod 256 (vp_or64_U), out[2] = (delta + 64)
      mod 256 (ceo_U_off), out[24] = 3 (len), out[25] = 0 (display), out[28..32) = 0x80000 = KEY 8 0. a0 = 0.
   0x85a18 ld ra,8(sp); addi sp,sp,16; ret. Every path ends there. *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation Znumtheory.
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
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw0 YCef YF0l YCej YCeh YCem YCep.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw1 AWalkFw2 YCfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase CPgEncC.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import CPgBaseU CPgEncU CPgWalkU CPgEncPersU CPgEncOutU.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the arithmetic of the function, over the engine's symbolic values ---- *)
Local Ltac vp_consts :=
unfold zcanon, M64, bv_swrap, bv_wrap in *;
change (bv_half_modulus 32) with 2147483648 in *; change (bv_modulus 32) with 4294967296 in *;
change (bv_modulus 64) with 18446744073709551616 in *; change (2 ^ 32) with 4294967296 in *;
change (2 ^ 64) with 18446744073709551616 in *; change (2 ^ 31) with 2147483648 in *.
(* 0x85954 `addiw a6, a2, -64` and 0x85960 `bltu a6, a7` with a7 = -128: taken exactly when delta is out of
   [-64, 63] *)
Lemma vp_delta_U : forall E n delta, ew E n = Z_to_bv 64 delta -> - 2 ^ 31 <= delta < 2 ^ 31 ->
(U E (SAluw ALU_ADD (SOff n 0) (SLit (-64))) <? U E (SLit 18446744073709551488)) = (delta <? -64) || (63 <? delta).
Proof.
intros E n delta Hn Hd.
rewrite U_of_S, S_SAluw, U_SOff, Hn, !U_SLit, unsigned_lit, Z.add_0_r. cbn [zalu_raw].
vp_consts.
change ((-64) mod 18446744073709551616) with 18446744073709551552.
change (18446744073709551552 mod 4294967296) with 4294967232.
change (18446744073709551488 mod 18446744073709551616) with 18446744073709551488.
rewrite Z.mod_mod by lia.
destruct (Z.ltb_spec delta (-64)); destruct (Z.ltb_spec 63 delta); cbn [orb];
match goal with |- (?x <? ?y) = _ => destruct (Z.ltb_spec x y) end; try reflexivity; exfalso;
Z.to_euclidean_division_equations; lia.
Qed.
(* 0x859a0 `ori a1, a1, 64`, stored by `sb` at out + 1: the byte (strip | 0x40) mod 256 *)
Lemma vp_or64_U : forall E n strip, ew E n = Z_to_bv 64 (s32 strip) -> 0 <= strip < 2 ^ 31 ->
U E (SAlu ALU_OR (SOff n 0) (SLit 64)) mod 256 = u8 (Z.lor 0x40 strip).
Proof.
intros E n strip Hn Hs. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SOff, Hn, unsigned_lit, Z.add_0_r, U_SLit.
unfold s32. rewrite (proj2 (Z.ltb_lt strip (2 ^ 31))) by lia.
unfold zcanon, M64. rewrite !(Z.mod_small strip) by lia. change (64 mod 2 ^ 64) with 64.
unfold u8. rewrite Z.lor_comm. apply Z.mod_mod_divide. exists (2 ^ 56). reflexivity.
Qed.

(* ---- the Gallina result on each path ---- *)
Lemma vp_spec_arg : forall strip delta, vpot_spec None strip delta = (E_ARG, None).
Proof. reflexivity. Qed.
Lemma vp_spec_delta : forall d strip delta, delta < -64 \/ 63 < delta -> vpot_spec (Some d) strip delta = (E_RANGE, None).
Proof.
intros d strip delta H. unfold vpot_spec.
destruct (d_strips d <=? strip); [reflexivity|]. cbn [orb].
destruct H as [H|H]; [rewrite (proj2 (Z.ltb_lt _ _) H) | rewrite (proj2 (Z.ltb_lt _ _) H), orb_true_r]; reflexivity.
Qed.
Lemma vp_spec_strip : forall d strip delta, d_strips d <= strip -> vpot_spec (Some d) strip delta = (E_RANGE, None).
Proof. intros d strip delta H. unfold vpot_spec. rewrite (proj2 (Z.leb_le _ _) H). reflexivity. Qed.
Lemma vp_spec_ok : forall d strip delta, strip < d_strips d -> -64 <= delta <= 63 ->
vpot_spec (Some d) strip delta = (0, Some ([0xb0; u8 (Z.lor 0x40 strip); u8 (delta + 64)], KEY 8 0, 0)).
Proof.
intros d strip delta H1 H2. unfold vpot_spec.
rewrite (proj2 (Z.leb_gt _ _) H1), (proj2 (Z.ltb_ge delta (-64))), (proj2 (Z.ltb_ge 63 delta)) by lia. reflexivity.
Qed.

(* ---- the walk ---- *)
(* an atom of the walk's env after runs (the entry env under ewset / havoc), from the entry fact H *)
Local Ltac vp_ew H := cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; exact H.
(* the write-range obligation of a run, paid by cenc_out's write right on out *)
Local Ltac vp_awr :=
idtac; lazymatch goal with Htw : twr_ok _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => ceo_awr Htw end.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Theorem diginet_vpot_encode_B_holds : cdcU_vpot_specX tfibsegs B MT 0x85914.
Proof using MTL TL LAWS.
unfold cdcU_vpot_specX.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs pd p strip delta out before
  HE H10 HP Hpal H11 H12 H13 Hoal HO HD.
pose proof HE as HE0.
destruct HE as (HJ0 & Hra & Hra4 & Hgp & Htp & Hal16 & Hwlo & Hwhi & Hev & Hlive).
(* the entry journal HJ0 stays older than the walk's HJ: each run takes the newest *)
pose proof HJ0 as HJ.
unfold TB_vpot in *.
destruct H11 as [Hs H11]. destruct H12 as [Hd H12].
destruct HO as (HDST & Hbefore & Hlen).
pose proof HDST as (Hout0 & Hout63 & Htdst & Htwr & _ & _ & Hoam & Howin).
unfold coff_win in Howin.
pose proof Hwx_tfa as Hwx. pose proof tfib_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hoapp : out + 32 <= 2 ^ 47 - 1) by (unfold amem_range in Hoam; rewrite C4, C5 in Hoam; unfold kHighMemBeg in Hoam; lia).
assert (KEIMG : forall a, cenc_wr out a -> in_img tfibsegs a -> False)
  by (intros a Ha Himg; exact (cw_tdst_not_img tfibsegs B LAWS tfib_segs_low lyc Sc W memc mdc out 32 a (proj1 HJ0) Htdst Ha Himg)).
unfold cfg_at. change (w64 0x85914) with (Z_to_bv 64 0x85914).
destruct pd as [d|].
- (* pd = Some d *)
  pose proof (pers_some B W memc (spZ regs) 16 p d HP) as (Hp & Hstr & Hpv & Hpwin & Hcimg).
  pose proof (pers_off_zone B W memc (spZ regs) 16 p d out 32 HP HD) as [Hpz1 Hpz2].
  unfold PERS_HI in Hp. cbn [cpers_disj] in HD.
  set (xs := [d_strips d]).
  pose proof (ceo_entry B TL LAWS 0x85914 xs 13 13%bv (pers_AF 33) STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
    regs 16 out HE0 ltac:(lia) eq_refl H13 Hoal HDST
    ltac:(apply (pers_atoms_ok _ 33 p (d_strips d));
      [rewrite (cw_ew_reg regs xs 10 10%bv eq_refl); exact H10 | exact (cw_ew_x regs xs 0) | unfold PERS_HI; lia | exact Hpal | exact Hstr]))
    as HS.
  remember (Ereg regs (cw_extra xs)) as E eqn:HE.
  assert (E1 : ew E 1 = getr regs 1) by (subst E; exact (cw_ew_reg regs xs 1 1%bv eq_refl)).
  assert (B2 : bv_unsigned (ew E 2) = spZ regs) by (subst E; rewrite (cw_ew_reg regs xs 2 2%bv eq_refl); reflexivity).
  assert (E10 : ew E 10 = Z_to_bv 64 p) by (subst E; rewrite (cw_ew_reg regs xs 10 10%bv eq_refl); exact H10).
  assert (E11 : ew E 11 = w64 (s32 strip)) by (subst E; rewrite (cw_ew_reg regs xs 11 11%bv eq_refl); exact H11).
  assert (E12 : ew E 12 = Z_to_bv 64 delta) by (subst E; rewrite (cw_ew_reg regs xs 12 12%bv eq_refl); exact H12).
  assert (E13 : ew E 13 = Z_to_bv 64 out) by (subst E; rewrite (cw_ew_reg regs xs 13 13%bv eq_refl); exact H13).
  assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; apply cw_ew_SB).
  assert (E33 : ew E 33 = Z_to_bv 64 (d_strips d)) by (subst E; exact (cw_ew_x regs xs 0)).
  assert (B10 : bv_unsigned (ew E 10) = p) by (rewrite E10; apply unsigned_lit_small; lia).
  assert (B13 : bv_unsigned (ew E 13) = out) by (rewrite E13; apply unsigned_lit_small; lia).
  assert (HAE : env_agree 32 (Ereg regs (cw_extra xs)) E) by (subst E; apply env_agree_refl).
  clear HE.
  (* the shadow entries of out (cdst_ok) and of the personality bytes (cimg_range) *)
  assert (SHOK : sh_ok tfibsegs CW_Bx [mkSHE 13 0 32; pers_SH] E (mrestrict (w_H W) memc)).
  { constructor; [exact (cw_shent_cdst B STK sp0 FP ly S lyc Sc own W memc (spZ regs) 16 E 13 out 32 HDST E13 E32 ltac:(lia))|].
    constructor; [exact (pers_shent B lyc Sc W memc mdc (spZ regs) 16 E p d (proj1 HJ0) HP E10 E32)|].
    constructor. }
  assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 16 <= a < spZ regs) ->
    aview tfibsegs (w_H W) memc a = aview tfibsegs (w_H W) memc a) by (intros; reflexivity).
  (* 0x85914 .. the delta test 0x85960 *)
  cw_run vp_awr. cw_keep ceo_kwr.
  (* drop the .got slot and the cell, add the byte p + 17 *)
  pers_swap_tac E10 E33 Hpv ltac:(idtac; apply KE; [lia | exact Hpz1]) pers_disj.
  cw_branch Hb1; rewrite branch_ltu_U in Hb1;
  lazymatch type of Hb1 with context [U ?E' (SAluw _ _ _)] =>
    rewrite (vp_delta_U E' 12 delta ltac:(vp_ew E12) Hd) in Hb1 end.
  + (* delta out of [-64, 63]: a0 = -11, out unchanged *)
    assert (Hdr : delta < -64 \/ 63 < delta)
      by (apply orb_true_iff in Hb1; destruct Hb1 as [X|X]; apply Z.ltb_lt in X; lia).
    rewrite (vp_spec_delta d strip delta Hdr).
    cw_run vp_awr. cw_keep ceo_kwr.
    cw_leaf ltac:(idtac; cw_kept HJ0 KE ltac:(exact KEIMG) ltac:(intros a Ha; left; exact Ha))
      ltac:(idtac; exact (ceo_res_fail W memc _ _ out before (spZ regs) E_RANGE Hbefore Hlen ltac:(lia) ltac:(lia) Howin KE
        ltac:(ceo_a0 R10))).
  + (* delta in [-64, 63] *)
    assert (Hdr : -64 <= delta <= 63)
      by (apply orb_false_iff in Hb1; destruct Hb1 as [X1 X2]; apply Z.ltb_ge in X1; apply Z.ltb_ge in X2; lia).
    cw_run vp_awr. cw_keep ceo_kwr.
    cw_branch Hb2; rewrite branch_geu_U in Hb2;
    lazymatch type of Hb2 with context [U ?E' (SOff 11 0) <? U ?E' ?x] =>
      rewrite (pers_strip_ltu E' 11 strip x (d_strips d) ltac:(vp_ew E11) Hs
        (proj2 (pers_U_byte E' 33 (d_strips d) ltac:(vp_ew E33) Hstr)) Hstr) in Hb2 end.
    * (* d_strips d <= strip: a0 = -11, out unchanged *)
      apply negb_true_iff, Z.ltb_ge in Hb2.
      rewrite (vp_spec_strip d strip delta Hb2).
      cw_run vp_awr. cw_keep ceo_kwr.
      cw_leaf ltac:(idtac; cw_kept HJ0 KE ltac:(exact KEIMG) ltac:(intros a Ha; left; exact Ha))
        ltac:(idtac; exact (ceo_res_fail W memc _ _ out before (spZ regs) E_RANGE Hbefore Hlen ltac:(lia) ltac:(lia) Howin KE
          ltac:(ceo_a0 R10))).
    * (* strip < d_strips d: the windows of out, then the stores *)
      apply negb_false_iff, Z.ltb_lt in Hb2.
      rewrite (vp_spec_ok d strip delta Hb2 Hdr).
      lazymatch goal with HS0 : st_ok _ ?E' ?ss (restrict (w_H W) ?ms0) |- _ =>
        pose proof (ceo_add3 B LAWS STK sp0 FP ly S lyc Sc own W memc mdc (spZ regs) 16 E' ss ms0 13 out 3
          (proj1 HJ0) HDST HS0 ltac:(vp_ew B13) ltac:(lia) ltac:(intros a Ha; apply KE; lia)
          ltac:(ceo_disj lia) ltac:(ceo_disj lia) ltac:(ceo_disj lia)) as HS1;
        clear HS0;
        lazymatch type of HS1 with st_ok _ _ ?ss2 _ =>
          let ss3 := eval vm_compute in ss2 in change (st_ok tfibsegs E' ss3 (restrict (w_H W) ms0)) in HS1 end;
        rename HS1 into HS
      end.
      pose proof (ceo_KE_widen (w_H W) _ memc (spZ regs) out 3 KE) as KE2. clear KE. rename KE2 into KE.
      cw_run vp_awr. cw_keep ceo_kwr.
      cw_leaf ltac:(idtac; cw_kept HJ0 KE ltac:(exact KEIMG)
          ltac:(intros a Ha; cbv beta in Ha; unfold ceo_zone, cenc_wr in *; lia))
        idtac.
      unfold cenc_res. cbn [fst snd].
      split; [ceo_a0 R10|].
      lazymatch goal with HS0 : st_ok _ _ _ _ |- _ => ceo_chunks HS0 end.
      eapply (ceo_res_ok _ memc _ out before [0xb0; u8 (Z.lor 0x40 strip); u8 (delta + 64)] (KEY 8 0) 0 Hlen
        ltac:(cbn; lia) Hbefore).
      -- (* out[0..3) *)
        intros j Hj. cbn [length] in Hj.
        destruct j as [|[|[|j]]]; [| | | lia]; cbn [nth Z.of_nat]; (eapply ceo_chunk1; [eassumption|]).
        ++ rewrite U_lit by lia. reflexivity.
        ++ lazymatch goal with |- context [U ?E' (SAlu ALU_OR _ _)] =>
             rewrite (vp_or64_U E' 11 strip ltac:(vp_ew E11) ltac:(lia)) end.
           unfold u8. rewrite Z.mod_mod by lia. reflexivity.
        ++ erewrite ceo_U_off by exact E12. unfold u8. rewrite Z.mod_mod by lia. reflexivity.
      -- (* out[24] = 3 *)
        eapply ceo_chunk1; [eassumption|]. rewrite U_lit by lia. reflexivity.
      -- (* out[25] = 0 *)
        eapply ceo_chunk1; [eassumption|]. rewrite U_lit by lia. reflexivity.
      -- (* out[28..32) = KEY 8 0 *)
        intros j Hj. eapply ceo_chunk4; [eassumption | rewrite U_lit by lia; vm_compute; reflexivity | exact Hj].
      -- (* out[3..24) and out[26..28) kept *)
        intros a Ha. change (Z.of_nat (length [0xb0; u8 (Z.lor 0x40 strip); u8 (delta + 64)])) with 3 in Ha.
        apply KE; [lia | unfold ceo_zone; lia].
- (* pd = None: p = 0; 0x85924 beqz a4 is taken, a0 = -1, out unchanged *)
  apply pers_none_p in HP. subst p.
  pose proof (cw_entry_base B TL LAWS 0x85914 16 [] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs 16 HE0
    ltac:(lia) ltac:(vm_compute; reflexivity)) as HS.
  remember (Ereg regs (cw_extra [])) as E eqn:HE.
  assert (E1 : ew E 1 = getr regs 1) by (subst E; exact (cw_ew_reg regs [] 1 1%bv eq_refl)).
  assert (B2 : bv_unsigned (ew E 2) = spZ regs) by (subst E; rewrite (cw_ew_reg regs [] 2 2%bv eq_refl); reflexivity).
  assert (E10 : ew E 10 = Z_to_bv 64 0) by (subst E; rewrite (cw_ew_reg regs [] 10 10%bv eq_refl); exact H10).
  assert (HAE : env_agree 32 (Ereg regs (cw_extra [])) E) by (subst E; apply env_agree_refl).
  clear HE.
  assert (SHOK : sh_ok tfibsegs CW_Bx [] E (mrestrict (w_H W) memc)) by constructor.
  assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 16 <= a < spZ regs) ->
    aview tfibsegs (w_H W) memc a = aview tfibsegs (w_H W) memc a) by (intros; reflexivity).
  cw_run vp_awr. cw_keep ceo_kwr.
  cw_branch Hb0.
  + rewrite vp_spec_arg.
    cw_run vp_awr. cw_keep ceo_kwr.
    cw_leaf ltac:(idtac; cw_kept HJ0 KE ltac:(exact KEIMG) ltac:(intros a Ha; left; exact Ha))
      ltac:(idtac; exact (ceo_res_fail W memc _ _ out before (spZ regs) E_ARG Hbefore Hlen ltac:(lia) ltac:(lia) Howin KE
        ltac:(ceo_a0 R10))).
  + (* not taken would need p <> 0 *)
    exfalso. rewrite (pers_beqz0 _ ltac:(vp_ew E10)) in Hb0. discriminate Hb0.
Qed.
End b.
