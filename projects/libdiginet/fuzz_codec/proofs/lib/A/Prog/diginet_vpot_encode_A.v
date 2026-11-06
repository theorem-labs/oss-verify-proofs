(* diginet_vpot_encode, image A 0x8502c, 89 instructions, against lib/A/Prog/CPgEncC.v's cdc_vpot_specX.
   a0 = p (the personality), a1 = strip (arg_u32A: w64 (s32 strip)), a2 = delta (arg_s32A), a3 = out. The walk
   starts from `Ereg regs (cw_extra xs)` (atom 32 = SB, the shadow offset; atom 33 = p->strips when pd = Some d)
   with the base regions of lib/A/Prog/CPgWalk.v and no region for out or the personality. Paths of the listing:
   0x8502c addi sp,sp,-16; sd ra,8(sp) (the save slot [sp - 16, sp), the only stack write); mv a4,a0; li a0,-1.
   0x8503c beqz a4 -- p = 0 (pd = None): TAKEN to 0x85120, a0 = -1 = E_ARG, out unchanged. With pd = Some d the
      engine decides it not taken (atom 10 >= 1).
   0x85040 beqz a3 -- out = 0: the engine decides it not taken (out's atom fact, from cdst_ok).
   0x85044-0x8504c the shadow offset: ld of the .got slot 0x9db10 (holds 0xa6478), ld of 0xa6478 (holds SB).
   0x85050-0x85060 the instrumented check before the 1-byte load of p + 17: the engine decides it from the shadow
      entry of [p + 16, p + 20) (pers_argA's cimg_range); errpath_load1 at 0x85138 is not reached.
   0x85064 addiw a6,a2,-64; li a7,-128; li a0,-11; 0x85070 bltu a6,a7 -- the delta test, the first stop: TAKEN
      exactly when delta < -64 or 63 < delta (vp_delta_U), to 0x85120 with a0 = -11 = E_RANGE, out unchanged.
      At this stop the regions of the .got slot and the cell are dropped and the byte p + 17 is added
      (CPgEncPers.pers_swap_at): the personality may lie on those two cells.
   0x85074 lbu a4,0(a4) -- p->strips = d_strips d (atom 33); 0x85078 bgeu a1,a4 -- the strip test: TAKEN exactly
      when d_strips d <= strip (CPgEncPers.pers_strip_ltu; a strip >= 2 ^ 31 is sign-extended, so the unsigned
      compare sees it as large), to 0x85120 with a0 = -11, out unchanged.
   Not taken: the three write windows of out are added (CPgEncOut.ceo_add3: out[0..3), out[24..26), out[28..32)).
   0x8507c-0x85110 the six instrumented checks of out, out + 1, out + 2, out + 24, out + 25 (1-byte stores) and
      out + 28 (4-byte store), each decided from out's shadow entry (cenc_out's cdst_ok), and the stores:
      out[0] = 0xb0, out[1] = (strip | 0x40) mod 256 (vp_or64_U), out[2] = (delta + 64) mod 256
      (CPgEncOut.ceo_U_off), out[24] = 3 (len), out[25] = 0 (display), out[28..32) = 0x80000 = KEY 8 0. a0 = 0.
   0x85120 ld ra,8(sp); addi sp,sp,16; ret. Every path ends there. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw0 ACef AF0l ACej ACeh ACem ACep.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw1 AWalkFw2 ACfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase CPgEncC CPgWalk CPgEncPers CPgEncOut.
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
(* 0x85064 `addiw a6, a2, -64` and 0x85070 `bltu a6, a7` with a7 = -128: taken exactly when delta is out of
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
(* 0x850a8 `ori a1, a1, 64`, stored by `sb` at out + 1: the byte (strip | 0x40) mod 256 *)
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
Theorem diginet_vpot_encode_A_holds : cdc_vpot_specX tfibsegs B MT 0x8502c.
Proof using MTL TL LAWS.
unfold cdc_vpot_specX.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs pd p strip delta out before
  HE H10 HP H11 H12 H13 HO HD.
pose proof HE as HE0.
destruct HE as (HJ0 & Hra & Hra4 & Hgp & Htp & Hal16 & Hwlo & Hwhi & Hev & Hlive).
(* the entry journal HJ0 stays older than the walk's HJ: each run takes the newest *)
pose proof HJ0 as HJ.
unfold T_vpot in *.
destruct H11 as [Hs H11]. destruct H12 as [Hd H12].
destruct HO as (HDST & Hbefore & Hlen).
pose proof HDST as (Hout0 & Hout63 & Htdst & Htwr & _ & _ & Hoam & Howin).
unfold coff_win in Howin.
pose proof Hwx_tfa as Hwx. pose proof tfib_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hoapp : out + 32 <= 2 ^ 47 - 1) by (unfold amem_range in Hoam; rewrite C4, C5 in Hoam; unfold kHighMemBeg in Hoam; lia).
assert (KEIMG : forall a, cenc_wr out a -> in_img tfibsegs a -> False)
  by (intros a Ha Himg; exact (cw_tdst_not_img tfibsegs B LAWS tfib_segs_low lyc Sc W memc mdc out 32 a (proj1 HJ0) Htdst Ha Himg)).
unfold cfg_at. change (w64 0x8502c) with (Z_to_bv 64 0x8502c).
destruct pd as [d|].
- (* pd = Some d *)
  pose proof (pers_some B W memc (spZ regs) 16 p d HP) as (Hp & Hstr & Hpv & Hpwin & Hcimg).
  pose proof (pers_off_zone B W memc (spZ regs) 16 p d out 32 HP HD) as [Hpz1 Hpz2].
  unfold PERS_HI in Hp. cbn [cpers_disj] in HD.
  set (xs := [d_strips d]).
  pose proof (ceo_entry B TL LAWS 0x8502c xs 13 13%bv (pers_AF 33) STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
    regs 16 out HE0 ltac:(lia) eq_refl H13 HDST
    ltac:(apply (pers_atoms_ok _ 33 p (d_strips d));
      [rewrite (cw_ew_reg regs xs 10 10%bv eq_refl); exact H10 | exact (cw_ew_x regs xs 0) | unfold PERS_HI; lia | exact Hstr]))
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
  (* 0x8502c .. the delta test 0x85070 *)
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
- (* pd = None: p = 0; 0x8503c beqz a4 is taken, a0 = -1, out unchanged *)
  apply pers_none_p in HP. subst p.
  pose proof (cw_entry_base B TL LAWS 0x8502c 16 [] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs 16 HE0
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
