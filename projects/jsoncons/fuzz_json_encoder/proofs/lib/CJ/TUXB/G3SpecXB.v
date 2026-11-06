(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Lib Require Import Tac ZBridge FP.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.TU Require Import G3Pure G3Lem.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.TUXB Require Import DgWalkXB G3PureXB CeilXB G3WalkXB.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import AsanUbsan.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Notation rsegs := DgWalkXB.rsegs.

Section G3B2.
Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word.
Variable F : bvmap 5 word.
Variable m0 : word -> option byte.
Variables buf lenp kp : Z.
Local Notation GSP := (G3WalkXB.GSP sp).
Hypothesis BUFR : (4096 <= buf /\ buf + 22 <= 2^47)%Z.
Hypothesis SPR0 : (2^41 <= GSP /\ GSP + 40 <= 2^47)%Z.   (* [comment removed for export] *)
Hypothesis SPA : (GSP mod 16 = 0)%Z.
Hypothesis KP : kp = (GSP + 32)%Z.   (* [comment removed for export] *)
Hypothesis KL : lenp = (kp + 4)%Z.
Hypothesis SEP_B : (buf + 22 <= GSP - 192 \/ GSP + 40 <= buf)%Z.   (* [comment removed for export] *)
Local Notation app_buf22 := (G3WalkXB.app_buf22 buf).
Hypothesis APP_B : app_buf22.
Hypothesis APP_S : (0x10007fff8000 <= GSP - 192)%Z.
Hypothesis SHL : mrd rsegs m0 (wa (Z.shiftr lenp 3 + 2147450880)) = Some (Z_to_bv 8 0).
Hypothesis SHK : mrd rsegs m0 (wa (Z.shiftr kp 3 + 2147450880)) = Some (Z_to_bv 8 0).
Hypothesis SHBUF : forall k, (0 <= k < 22)%Z -> mrd rsegs m0 (wa (Z.shiftr (buf + k) 3 + 2147450880)) = Some (Z_to_bv 8 0).
Hypothesis SHPT : forall i, (0 <= i < 687)%Z -> mrd rsegs m0 (wa (Z.shiftr (G3PureXB.PT_BASE + 8 * i) 3 + 2147450880)) = Some (Z_to_bv 8 0).
Hypothesis SHPE : forall i, (0 <= i < 686)%Z -> mrd rsegs m0 (wa (Z.shiftr (G3PureXB.PE_BASE + 4 * i) 3 + 2147450880)) = Some (Z_to_bv 8 0).   (* [comment removed for export] *)

Local Notation G3_W := (G3WalkXB.G3_W sp buf lenp kp).
Local Notation g3_post := (G3WalkXB.g3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 buf lenp kp).
Local Notation L x := (x ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m0 buf lenp kp BUFR SPR0 SPA KP KL SEP_B APP_B APP_S SHL SHK SHBUF SHPT SHPE).
Local Notation g3_sh_read := (L G3WalkXB.g3_sh_read).
Local Notation g3_mul := (L G3WalkXB.g3_mul).
Ltac pgoal := match goal with |- ?G => idtac "GOAL:" G end.
Lemma swrap32_mod64L : forall x y, (- 2 ^ 31 <= x + y < 2 ^ 31)%Z -> bv_swrap 32 (x mod 18446744073709551616 + y mod 18446744073709551616) = (x + y)%Z.
Proof. intros x y H. change 18446744073709551616%Z with (2 ^ 64)%Z. apply swrap32_mod64. exact H. Qed.
(* [comment removed for export] *)
Ltac ubr K := zify_cond K;
  repeat first [ rewrite swrap32_modl in K by lia | rewrite swrap32_mod64 in K by lia | rewrite swrap32_small in K by lia ];
  rewrite ?sgn_small in K by lia; ub_norm_in K;
  first [ lia | unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus in K; cbn -[Z.pow] in K; change (2 ^ 32 / 2)%Z with (2 ^ 31)%Z in K; lia ].
Ltac ubg := repeat first [ rewrite swrap32_modl by lia | rewrite swrap32_mod64 by lia | rewrite swrap32_small by lia ].

(* [comment removed for export] *)
Lemma g3_tail3 : forall a3' a4' a7' t0' t1' t2' t3' t4' t5' t6' (F3 : bvmap 5 word) fc (m : word -> option byte) (plf ple wf we mif x cf ce mk s : Z) (bs : list byte) lj kj j8,
  frm0 fc ->
  stk rsegs m (GSP - 192) (GSP - 96) ->
  rw_cells rsegs m (GSP - 96) [CB 8 j8; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  munch G3_W m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
  u8arr rsegs m buf bs -> length bs = 22%nat -> rw_cells rsegs m lenp [C4 lj] -> rw_cells rsegs m kp [C4 kj] ->
  ro_cells rsegs m 0x164518 [C8 (Z_to_bv 64 0x16d7b8)] -> ro_cells rsegs m 0x16d7b8 [C8 (Z_to_bv 64 2147450880)] ->
  (-1127 <= ple <= 971)%Z -> (2 ^ 53 <= plf < 2 ^ 54)%Z -> (2 ^ 52 <= wf < 2 ^ 53)%Z ->
  (9 <= x <= 62)%Z -> (1 <= mif < 2 ^ 54)%Z -> (2 ^ 61 <= mif * 2 ^ x <= wf * 2 ^ 11)%Z -> (wf * 2 ^ 11 <= plf * 2 ^ 10)%Z ->
  (2 ^ 63 <= cf < 2 ^ 64)%Z -> (-307 <= mk <= 325)%Z -> s = (- (ce + ple + 54))%Z -> (56 <= s <= 59)%Z ->
  evt rsegs g3_post (MS (mkR (Z_to_bv 64 0xcb358) (Z_to_bv 64 (GSP - 96)) gp tp t0' t1' t2' (Z_to_bv 64 buf) (Z_to_bv 64 lenp)
                             (Z_to_bv 64 (- s)) (Z_to_bv 64 (- s)) (Z_to_bv 64 (- mk)) a3' a4' (Z_to_bv 64 (- mk)) (Z_to_bv 64 cf) a7'
                             (Z_to_bv 64 kp) (Z_to_bv 64 2147450880) (Z_to_bv 64 wf) (Z_to_bv 64 plf)
                             (Z_to_bv 64 x) (Z_to_bv 64 mif) (Z_to_bv 64 (ple - 10)) (Z_to_bv 64 we) s10 s11 t3' t4' t5' t6')
                        F3 (Z_to_bv 64 0xcb420) fc None m (seg_rom rsegs)).
Proof using All.
  intros until j8. intros FRM ST FR MU WM MI BU BL LE KC GOT SHV Hple Hplf Hwf Hx Hmif Hxm Hxw HPT Hmk Hs Hsr.
  unfold G3WalkXB.G3_W in MU. unfold G3WalkXB.GSP in *.
  assert (Hpx : (2 ^ 9 <= 2 ^ x <= 2 ^ 62)%Z) by (split; apply Z.pow_le_mono_r; lia).
  assert (KA : (kp mod 4 = 0)%Z) by (rewrite KP; unfold G3WalkXB.GSP; pose proof (Z_div_mod_eq_full (bv_unsigned sp) 16) as D; rewrite SPA in D;
                                      replace (bv_unsigned sp + 32)%Z with ((bv_unsigned sp / 16 * 4 + 8) * 4)%Z by lia; apply Z_mod_mult).   (* [comment removed for export] *)
  (* [comment removed for export] *)
  zstep. if_cases Kz; [zify_cond Kz; lia | ]. clear Kz.
  zstep. zstep. if_cases Ka; [zify_cond Ka; rewrite (land3_0 kp KA) in Ka; lia | ]. clear Ka.
  pose proof (g3_sh_read m kp (Z.shiftr kp 3 + 2147450880) MU ltac:(lia) eq_refl SHK) as SHk.
  do 4 zstep. if_cases KT2; [cbv in KT2; discriminate | ]. clear KT2. clear SHk.
  (* [comment removed for export] *)
  set (xw := (wf * 2048)%Z) in *. set (xp := (plf * 1024)%Z) in *. set (xm := (mif * 2 ^ x)%Z) in *.
  assert (Rxw : (2 ^ 63 <= xw < 2 ^ 64)%Z) by (unfold xw; lia).
  assert (Rxp : (2 ^ 63 <= xp < 2 ^ 64)%Z) by (unfold xp; lia).
  assert (Rxm : (2 ^ 61 <= xm <= xw)%Z) by (unfold xm, xw in *; lia).
  do 3 zstep.
  rewrite (Z.shiftl_mul_pow2 plf 10), (Z.shiftl_mul_pow2 wf 11) by lia. rewrite (Z.mod_small x 64) by lia. rewrite (Z.shiftl_mul_pow2 mif x) by lia.
  replace (plf * 2 ^ 10)%Z with xp by (unfold xp; lia). replace (wf * 2 ^ 11)%Z with xw by (unfold xw; lia). fold xm.
  (* [comment removed for export] *)
  do 8 zstep.
  set (ch := Z.shiftr cf 32) in *. set (cl := (cf mod 4294967296)%Z) in *.
  set (wh := Z.shiftr xw 32) in *. set (wl := (xw mod 4294967296)%Z) in *.
  set (ph := Z.shiftr xp 32) in *. set (pl := (xp mod 4294967296)%Z) in *.
  set (mh := Z.shiftr xm 32) in *. set (ml := (xm mod 4294967296)%Z) in *.
  assert (Rch : (0 <= ch < 2 ^ 32)%Z) by (apply hi32; clear - HPT; lia). assert (Rcl : (0 <= cl < 2 ^ 32)%Z) by (apply Z.mod_pos_bound; clear; lia).
  assert (Rwh : (0 <= wh < 2 ^ 32)%Z) by (apply hi32; clear - Rxw; lia). assert (Rwl : (0 <= wl < 2 ^ 32)%Z) by (apply Z.mod_pos_bound; clear; lia).
  assert (Rph : (0 <= ph < 2 ^ 32)%Z) by (apply hi32; clear - Rxp; lia). assert (Rpl : (0 <= pl < 2 ^ 32)%Z) by (apply Z.mod_pos_bound; clear; lia).
  assert (Rmh : (0 <= mh < 2 ^ 32)%Z) by (apply hi32; clear - Rxm Rxw; lia). assert (Rml : (0 <= ml < 2 ^ 32)%Z) by (apply Z.mod_pos_bound; clear; lia).
  assert (Xc : (ch * 2 ^ 32 + cl = cf)%Z) by (unfold ch, cl; apply split32; clear - HPT; lia).
  assert (Xw : (wh * 2 ^ 32 + wl = xw)%Z) by (unfold wh, wl; apply split32; clear - Rxw; lia).
  assert (Xp : (ph * 2 ^ 32 + pl = xp)%Z) by (unfold ph, pl; apply split32; clear - Rxp; lia).
  assert (Xm : (mh * 2 ^ 32 + ml = xm)%Z) by (unfold mh, ml; apply split32; clear - Rxm; lia).
  assert (Ewl : Z.land xw 4294965248 = wl) by (unfold wl; apply (land_mask_low xw 11); [clear; lia | clear - Rxw; lia | unfold xw; replace 2048%Z with (2 ^ 11)%Z by reflexivity; apply Z.mod_mul; clear; lia]).
  assert (Epl : Z.land xp 4294966272 = pl) by (unfold pl; apply (land_mask_low xp 10); [clear; lia | clear - Rxp; lia | unfold xp; replace 1024%Z with (2 ^ 10)%Z by reflexivity; apply Z.mod_mul; clear; lia]).
  assert (Eml : Z.land xm 4294967295 = ml) by (unfold ml; change 4294967295%Z with (Z.ones 32); rewrite Z.land_ones by (clear; lia); reflexivity).
  assert (Hwl11 : (wl mod 2 ^ 11 = 0)%Z).
  { clear - Hwf. unfold wl, xw. replace 4294967296%Z with (2 ^ 21 * 2048)%Z by reflexivity. rewrite Z.mul_mod_distr_r by lia.
    replace (2 ^ 11)%Z with 2048%Z by reflexivity. apply Z.mod_mul. lia. }
  assert (Hpl10 : (pl mod 2 ^ 10 = 0)%Z).
  { clear - Hplf. unfold pl, xp. replace 4294967296%Z with (2 ^ 22 * 1024)%Z by reflexivity. rewrite Z.mul_mod_distr_r by lia.
    replace (2 ^ 10)%Z with 1024%Z by reflexivity. apply Z.mod_mul. lia. }
  assert (Lxw : (xw <= xp)%Z) by (unfold xw, xp; clear - Hxw; lia).
  clearbody ch cl wh wl ph pl mh ml. clearbody xm xw xp.
  assert (Eb : Z.land (ch * wl) 4294965248 = ((ch * wl) mod 4294967296)%Z).
  { clear - Rch Rwl Hwl11. apply (land_mask_low (ch * wl) 11); [lia | apply Z.mul_nonneg_nonneg; lia | ].
    rewrite Z.mul_mod by lia. rewrite Hwl11. rewrite Z.mul_0_r. reflexivity. }
  assert (Ep : Z.land (ch * pl) 4294966272 = ((ch * pl) mod 4294967296)%Z).
  { clear - Rch Rpl Hpl10. apply (land_mask_low (ch * pl) 10); [lia | apply Z.mul_nonneg_nonneg; lia | ].
    rewrite Z.mul_mod by lia. rewrite Hpl10. rewrite Z.mul_0_r. reflexivity. }
  (* [comment removed for export] *)
  pose proof (prod32b ch wh Rch Rwh) as Pacw. pose proof (prod32b cl wh Rcl Rwh) as Padw. pose proof (prod32b ch ph Rch Rph) as Pacp. pose proof (prod32b cl ph Rcl Rph) as Padp.
  pose proof (prod32b ch mh Rch Rmh) as Pacm. pose proof (prod32b cl mh Rcl Rmh) as Padm.
  do 8 zstep.
  clear Pacw Padw Pacp Padp Pacm Padm.
  (* [comment removed for export] *)
  zstep. rewrite Eml. zstep. rewrite Ewl. zstep. rewrite Epl.
  pose proof (prod32b ch ml Rch Rml) as Pbcm. pose proof (prod32b cl ml Rcl Rml) as Pbdm. pose proof (prod32b ch wl Rch Rwl) as Pbcw. pose proof (prod32b cl wl Rcl Rwl) as Pbdw.
  pose proof (prod32b ch pl Rch Rpl) as Pbcp. pose proof (prod32b cl pl Rcl Rpl) as Pbdp.
  do 6 zstep.
  pose proof (prod32b ch wh Rch Rwh) as Pacw. pose proof (prod32b cl wh Rcl Rwh) as Padw. pose proof (prod32b ch ph Rch Rph) as Pacp. pose proof (prod32b cl ph Rcl Rph) as Padp.
  pose proof (prod32b ch mh Rch Rmh) as Pacm. pose proof (prod32b cl mh Rcl Rmh) as Padm.
  pose proof (mcode_mult wh wl ch cl Rwh Rwl Rch Rcl) as Mw. rewrite Xw, Xc in Mw.
  pose proof (mcode_mult ph pl ch cl Rph Rpl Rch Rcl) as Mp. rewrite Xp, Xc in Mp.
  pose proof (mcode_mult mh ml ch cl Rmh Rml Rch Rcl) as Mm. rewrite Xm, Xc in Mm.
  pose proof (mult_lo xm cf ltac:(clear - Rxm; lia) ltac:(clear - HPT; lia)) as L1.
  pose proof (mult_mono xm xw cf ltac:(clear - Rxm; lia) ltac:(clear - HPT; lia)) as L2.
  pose proof (mult_mono xw xp cf ltac:(clear - Lxw Rxw; lia) ltac:(clear - HPT; lia)) as L3.
  pose proof (mult_hi xp cf ltac:(clear - Rxp; lia) ltac:(clear - HPT; lia)) as L4.
  pose proof (mult_lo62 xp cf ltac:(clear - Rxp; lia) ltac:(clear - HPT; lia)) as L5.
  eapply (g3_mul (ch * wh)%Z (ch * wl)%Z (cl * wh)%Z (cl * wl)%Z (ch * ph)%Z (ch * pl)%Z (cl * ph)%Z (cl * pl)%Z (ch * mh)%Z (ch * ml)%Z (cl * mh)%Z (cl * ml)%Z s mk).
  all: try eassumption.
  - rewrite Mm. clear - L1. lia.
  - rewrite Mm, Mw. clear - L2. lia.
  - rewrite Mw, Mp. clear - L3. lia.
  - rewrite Mp. clear - L4. lia.
  - rewrite Mp. clear - L5. lia.
Qed.

(* [comment removed for export] *)
Lemma g3_tail2 : forall a0' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' (F2 : bvmap 5 word) fc (m : word -> option byte) (plf ple wf we mif x : Z) (bs : list byte) lj kj j8,
  frm0 fc -> reg_get F2 10 = ceil_m (KCX (-50 - ple)) ->
  stk rsegs m (GSP - 192) (GSP - 96) ->
  rw_cells rsegs m (GSP - 96) [CB 8 j8; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  munch G3_W m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
  u8arr rsegs m buf bs -> length bs = 22%nat -> rw_cells rsegs m lenp [C4 lj] -> rw_cells rsegs m kp [C4 kj] ->
  ro_cells rsegs m 0x164518 [C8 (Z_to_bv 64 0x16d7b8)] -> ro_cells rsegs m 0x16d7b8 [C8 (Z_to_bv 64 2147450880)] ->
  (-1127 <= ple <= 971)%Z -> we = (ple + 1)%Z -> (2 ^ 53 <= plf < 2 ^ 54)%Z -> (2 ^ 52 <= wf < 2 ^ 53)%Z ->
  (9 <= x <= 62)%Z -> (1 <= mif < 2 ^ 54)%Z -> (2 ^ 61 <= mif * 2 ^ x <= wf * 2 ^ 11)%Z -> (wf * 2 ^ 11 <= plf * 2 ^ 10)%Z ->
  evt rsegs g3_post (MS (mkR (Z_to_bv 64 0xcb358) (Z_to_bv 64 (GSP - 96)) gp tp t0' t1' t2' (Z_to_bv 64 buf) (Z_to_bv 64 lenp)
                             a0' a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 kp) (Z_to_bv 64 2147450880) (Z_to_bv 64 wf) (Z_to_bv 64 plf)
                             (Z_to_bv 64 x) (Z_to_bv 64 mif) (Z_to_bv 64 (ple - 10)) (Z_to_bv 64 (we + -11)) s10 s11 t3' t4' t5' t6')
                        F2 (Z_to_bv 64 0xcb358) fc None m (seg_rom rsegs)).
Proof using All.
  intros until j8. intros FRM HF2 ST FR MU WM MI BU BL LE KC GOT SHV Hple Hwe Hplf Hwf Hx Hmif Hxm Hxw.
  unfold G3WalkXB.G3_W in MU. unfold G3WalkXB.GSP in *.
  assert (Hpx : (2 ^ 9 <= 2 ^ x <= 2 ^ 62)%Z) by (split; apply Z.pow_le_mono_r; lia).
  change (fmul_d RNE (fcvt_d_w RNE (Z_to_bv 64 (-50 - ple))) (Z_to_bv 64 4599094494223104510)) with (KCX (-50 - ple)) in HF2.
  destruct (kcb_facts ple Hple) as (KR1 & KR2 & KR3).
  (* [comment removed for export] *)
  do 3 zstep.
  set (f10 := reg_get F2 10) in *. rewrite HF2.
  change (Z_to_bv 64 13970166044105375744) with FLO. rewrite KR1.
  zstep. if_cases Kr1; [cbv in Kr1; discriminate | ]. clear Kr1.
  do 3 zstep.
  set (f10b := reg_get F2 10). change f10b with f10. rewrite HF2.
  change (Z_to_bv 64 4746794007248502784) with FHI. rewrite KR2.
  zstep. if_cases Kr2; [cbv in Kr2; discriminate | ]. clear Kr2.
  zstep.
  set (f10c := reg_get F2 10). change f10c with f10. rewrite HF2.
  change (fcvt_w_d RTZ (ceil_m (KCX (-50 - ple)))) with (KCWB (-50 - ple)).
  replace (KCWB (-50 - ple)) with (Z_to_bv 64 (KCZ (-50 - ple))) by (rewrite <- KR3; apply zbv_signed).
  destruct (kc_facts ple Hple) as (Hidx & Hse).
  set (mk := KCZ (-50 - ple)) in *. clearbody mk.
  (* [comment removed for export] *)
  zstep. zstep. if_cases Ki1; [ubr Ki1 | ]. clear Ki1. ubg.
  zstep. zstep. if_cases Ki2; [ubr Ki2 | ]. clear Ki2.
  set (idx := (mk + 343)%Z) in *.
  do 5 zstep. if_cases Kp1; [zify_cond Kp1; rewrite Z.shiftl_mul_pow2 in Kp1 by lia; rewrite Z.mod_small in Kp1 by lia; lia | ]. clear Kp1.
  zstep.
  replace (Z_to_bv 64 (154944 + idx ≪ 3)) with (Z_to_bv 64 (G3PureXB.PT_BASE + 8 * idx)) by (f_equal; rewrite Z.shiftl_mul_pow2 by lia; unfold G3PureXB.PT_BASE; lia).
  pose proof (g3_sh_read m (G3PureXB.PT_BASE + 8 * idx) (Z.shiftr (G3PureXB.PT_BASE + 8 * idx) 3 + 2147450880) MU ltac:(unfold G3PureXB.PT_BASE; lia) eq_refl (SHPT idx ltac:(lia))) as SHp.
  do 2 zstep. rewrite (Z.mod_small (G3PureXB.PT_BASE + 8 * idx)) by (unfold G3PureXB.PT_BASE; lia).
  do 2 zstep. if_cases KT0; [cbv in KT0; discriminate | ]. clear KT0. clear SHp.
  do 5 zstep. if_cases Kp2; [zify_cond Kp2; rewrite Z.shiftl_mul_pow2 in Kp2 by lia; rewrite Z.mod_small in Kp2 by lia; lia | ]. clear Kp2.
  zstep.
  replace (Z_to_bv 64 (161792 + idx ≪ 2)) with (Z_to_bv 64 (G3PureXB.PE_BASE + 4 * idx)) by (f_equal; rewrite Z.shiftl_mul_pow2 by lia; unfold G3PureXB.PE_BASE; lia).
  pose proof (g3_sh_read m (G3PureXB.PE_BASE + 4 * idx) (Z.shiftr (G3PureXB.PE_BASE + 4 * idx) 3 + 2147450880) MU ltac:(unfold G3PureXB.PE_BASE; lia) eq_refl (SHPE idx ltac:(lia))) as SHe.
  zstep. rewrite (Z.mod_small (G3PureXB.PE_BASE + 4 * idx)) by (unfold G3PureXB.PE_BASE; lia).
  do 2 zstep.
  pose proof (G3PureXB.pt_read m idx MI ltac:(lia)) as RDPT.
  zstep. unfold le_bytes_to_word. rewrite extract64_id. change (bytes_le_to_Z (firstn 8 (skipn (Z.to_nat (8 * idx)) G3Pure.PT_BYTES))) with (PTZ idx).
  pose proof (pt_facts idx ltac:(lia)) as HPT. set (cf := PTZ idx) in *. clearbody cf. clear RDPT.
  zstep. if_cases KT1; [cbv in KT1; discriminate | ]. clear KT1. clear SHe.
  pose proof (G3PureXB.pe_read m idx MI ltac:(lia)) as RDPE.
  zstep. unfold le_bytes_to_word. rewrite sext_extract32. change (bv_swrap 32 (bytes_le_to_Z (firstn 4 (skipn (Z.to_nat (4 * idx)) G3Pure.PE_BYTES)))) with (PEZ idx).
  set (ce := PEZ idx) in *. clearbody ce. clear RDPE.
  (* [comment removed for export] *)
  assert (HR1 : (- 2 ^ 31 <= we + -11 + ce < 2 ^ 31 - 64)%Z) by (clear - Hwe Hple Hse; lia).
  assert (HR2 : (- 2 ^ 31 <= ple - 10 + ce < 2 ^ 31 - 64)%Z) by (clear - Hple Hse; lia).
  do 3 zstep. if_cases Ke1; [zify_cond Ke1; rewrite (swrap32_mod64L (we + -11) ce) in Ke1 by (clear - HR1; lia); exfalso; exact (Ke1 eq_refl) | ]. clear Ke1.
  rewrite (swrap32_mod64L (we + -11) ce) by (clear - HR1; lia).
  do 3 zstep. if_cases Ke2; [zify_cond Ke2; rewrite (swrap32_modl (we + -11 + ce) 64), (swrap32_modl (we + -11 + ce) 0) in Ke2 by (clear - HR1; lia);
                              rewrite !sgn_small in Ke2 by (clear - HR1; lia); clear - Ke2; lia | ]. clear Ke2.
  rewrite (swrap32_modl (we + -11 + ce) 64), (swrap32_modl (we + -11 + ce) 0) by (clear - HR1; lia).
  do 3 zstep. if_cases Ke3; [zify_cond Ke3; rewrite (swrap32_mod64L (ple - 10) ce) in Ke3 by (clear - HR2; lia); exfalso; exact (Ke3 eq_refl) | ]. clear Ke3.
  rewrite (swrap32_mod64L (ple - 10) ce) by (clear - HR2; lia).
  do 3 zstep. if_cases Ke4; [zify_cond Ke4; rewrite (swrap32_modl (ple - 10 + ce) 64), (swrap32_modl (ple - 10 + ce) 0) in Ke4 by (clear - HR2; lia);
                              rewrite !sgn_small in Ke4 by (clear - HR2; lia); clear - Ke4; lia | ]. clear Ke4.
  rewrite (swrap32_modl (ple - 10 + ce) 64), (swrap32_modl (ple - 10 + ce) 0) by (clear - HR2; lia).
  do 3 zstep. if_cases Ke5; [zify_cond Ke5; rewrite (negw_small mk Hidx) in Ke5; rewrite Zminus_mod_idemp_r in Ke5; replace (0 - mk)%Z with (- mk)%Z in Ke5 by ring; exfalso; exact (Ke5 eq_refl) | ]. clear Ke5.
  rewrite (negw_small mk Hidx).
  replace (Z_to_bv 64 (0 - mk mod 18446744073709551616)) with (Z_to_bv 64 (- mk)) by (apply zbv_eqm; rewrite Zminus_mod_idemp_r; f_equal; ring).
  set (s := (- (ce + ple + 54))%Z).
  replace (Z_to_bv 64 (we + -11 + ce + 64)) with (Z_to_bv 64 (- s)) by (f_equal; unfold s; clear - Hwe; lia).
  replace (Z_to_bv 64 (ple - 10 + ce + 64)) with (Z_to_bv 64 (- s)) by (f_equal; unfold s; clear; lia).
  replace (Z_to_bv 64 (we + -11)) with (Z_to_bv 64 (we + -11)) by reflexivity.
  eapply (g3_tail3 _ _ _ _ _ _ _ _ _ _ _ _ m plf ple wf (we + -11) mif x cf ce mk s); try eassumption; try reflexivity; unfold s; clear - Hse Hidx; lia.
Qed.


End G3B2.
