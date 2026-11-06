(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib Require Import Tac ZBridge FP.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.TU Require Import G3Pure G3Lem.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.TUA Require Import DgWalkA DgSpecA G3PureA G3WalkA.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Asan.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Notation rsegs := DgWalkA.rsegs.

Section G3B.
Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word.
Variable F : bvmap 5 word.
Variable m0 : word -> option byte.
Variables buf lenp kp : Z.
Local Notation GSP := (G3WalkA.GSP sp).
Hypothesis BUFR : (4096 <= buf /\ buf + 22 <= 2^47)%Z.
Hypothesis SPR0 : (2^41 <= GSP /\ GSP + 16 <= 2^47)%Z.
Hypothesis KP : kp = (GSP + 8)%Z.
Hypothesis KL : lenp = (kp + 4)%Z.
Hypothesis SEP_B : (buf + 22 <= GSP - 160 \/ GSP + 16 <= buf)%Z.
Local Notation app_buf22 := (G3WalkA.app_buf22 buf).
Hypothesis APP_B : app_buf22.
Hypothesis APP_S : (0x10007fff8000 <= GSP - 160)%Z.
Hypothesis SHL : mrd rsegs m0 (wa (Z.shiftr lenp 3 + 2147450880)) = Some (Z_to_bv 8 0).
Hypothesis SHK : mrd rsegs m0 (wa (Z.shiftr kp 3 + 2147450880)) = Some (Z_to_bv 8 0).
Hypothesis SHBUF : forall k, (0 <= k < 22)%Z -> mrd rsegs m0 (wa (Z.shiftr (buf + k) 3 + 2147450880)) = Some (Z_to_bv 8 0).
Hypothesis SHPT : forall i, (0 <= i < 687)%Z -> mrd rsegs m0 (wa (Z.shiftr (G3PureA.PT_BASE + 8 * i) 3 + 2147450880)) = Some (Z_to_bv 8 0).
Hypothesis SHPE : forall i, (0 <= i < 686)%Z -> mrd rsegs m0 (wa (Z.shiftr (G3PureA.PE_BASE + 4 * i) 3 + 2147450880)) = Some (Z_to_bv 8 0).

Local Notation G3_W := (G3WalkA.G3_W sp buf lenp kp).
Local Notation g3_post := (G3WalkA.g3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 buf lenp kp).
Local Notation L x := (x ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m0 buf lenp kp BUFR SPR0 KP KL SEP_B APP_B APP_S SHL SHK SHBUF SHPT SHPE).
Local Notation g3_sh_read := (L G3WalkA.g3_sh_read).
Local Notation g3_mul := (L G3WalkA.g3_mul).

Lemma g3_tail : forall a0' a1' a5' t2' t3' t4' t5' t6' fc (m : word -> option byte) (plf ple wf we mif mie : Z) (bs : list byte) lj kj j8,
  frm0 fc ->
  stk rsegs m (GSP - 160) (GSP - 80) ->
  rw_cells rsegs m (GSP - 80) [CB 8 j8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  munch G3_W m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
  u8arr rsegs m buf bs -> length bs = 22%nat -> rw_cells rsegs m lenp [C4 lj] -> rw_cells rsegs m kp [C4 kj] ->
  ro_cells rsegs m 0x153138 [C8 (Z_to_bv 64 0x15c9b8)] -> ro_cells rsegs m 0x15c9b8 [C8 (Z_to_bv 64 2147450880)] ->
  (-1127 <= ple <= 971)%Z -> we = (ple + 1)%Z -> (2 ^ 53 <= plf < 2 ^ 54)%Z -> (2 ^ 52 <= wf < 2 ^ 53)%Z ->
  (9 <= mie - ple + 10 <= 62)%Z -> (1 <= mif < 2 ^ 54)%Z -> (2 ^ 61 <= mif * 2 ^ (mie - ple + 10) <= wf * 2 ^ 11)%Z -> (wf * 2 ^ 11 <= plf * 2 ^ 10)%Z ->
  evt rsegs g3_post (MS (mkR ra (Z_to_bv 64 (GSP - 80)) gp tp (Z_to_bv 64 plf) (Z_to_bv 64 ple) t2' (Z_to_bv 64 lenp) (Z_to_bv 64 buf)
                             a0' a1' (Z_to_bv 64 kp) (Z_to_bv 64 mie) (Z_to_bv 64 we) a5' (Z_to_bv 64 wf) (Z_to_bv 64 mif)
                             (Z_to_bv 64 2147450880) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                        F (Z_to_bv 64 0xcf92c) fc None m (seg_rom rsegs)).
Proof using All.
  intros until j8. intros FRM ST FR MU WM MI BU BL LE KC GOT SHV Hple Hwe Hplf Hwf Hx Hmif Hxm Hxw.
  set (x := (mie - ple + 10)%Z) in *.
  assert (Hpx : (2 ^ 9 <= 2 ^ x <= 2 ^ 62)%Z) by (split; apply Z.pow_le_mono_r; lia).
  do 8 zstep.
  rewrite (kc_arg ple Hple).
  change (fcvt_w_d RUP (fmul_d RNE (fcvt_d_w RNE (Z_to_bv 64 (-50 - ple))) (Z_to_bv 64 4599094494223104510))) with (KCW (-50 - ple)).
  destruct (kc_facts ple Hple) as (Hidx & Hse).
  replace (KCW (-50 - ple)) with (Z_to_bv 64 (KCZ (-50 - ple))) by (unfold KCZ; apply zbv_signed).
  set (mk := KCZ (-50 - ple)) in *. clearbody mk.
  zstep. replace (Z_to_bv 64 (mk mod 2 ^ 64 + 343)) with (Z_to_bv 64 (mk + 343)) by (apply zbv_eqm; rewrite Z.add_mod_idemp_l by lia; reflexivity).
  set (idx := (mk + 343)%Z) in *.
  do 3 zstep.
  replace (Z_to_bv 64 (155968 + idx ≪ 3)) with (Z_to_bv 64 (G3PureA.PT_BASE + 8 * idx)) by (f_equal; rewrite Z.shiftl_mul_pow2 by lia; unfold G3PureA.PT_BASE; lia).
  pose proof (g3_sh_read m (G3PureA.PT_BASE + 8 * idx) (Z.shiftr (G3PureA.PT_BASE + 8 * idx) 3 + 2147450880) MU ltac:(unfold G3PureA.PT_BASE; lia) eq_refl (SHPT idx ltac:(lia))) as SHp.
  do 2 zstep. rewrite (Z.mod_small (G3PureA.PT_BASE + 8 * idx)) by (unfold G3PureA.PT_BASE; lia).
  do 2 zstep. if_cases KT0; [cbv in KT0; discriminate | ]. clear SHp.
  do 4 zstep.
  replace (Z_to_bv 64 (162816 + idx ≪ 2)) with (Z_to_bv 64 (G3PureA.PE_BASE + 4 * idx)) by (f_equal; rewrite Z.shiftl_mul_pow2 by lia; unfold G3PureA.PE_BASE; lia).
  pose proof (g3_sh_read m (G3PureA.PE_BASE + 4 * idx) (Z.shiftr (G3PureA.PE_BASE + 4 * idx) 3 + 2147450880) MU ltac:(unfold G3PureA.PE_BASE; lia) eq_refl (SHPE idx ltac:(lia))) as SHe.
  zstep. rewrite (Z.mod_small (G3PureA.PE_BASE + 4 * idx)) by (unfold G3PureA.PE_BASE; lia).
  do 2 zstep.
  pose proof (G3PureA.pt_read m idx MI ltac:(lia)) as RDPT.
  zstep. unfold le_bytes_to_word. rewrite extract64_id. change (bytes_le_to_Z (firstn 8 (skipn (Z.to_nat (8 * idx)) G3Pure.PT_BYTES))) with (PTZ idx).
  pose proof (pt_facts idx ltac:(lia)) as HPT. set (cf := PTZ idx) in *. clearbody cf. clear RDPT.
  zstep. if_cases KT1; [cbv in KT1; discriminate | ]. clear SHe.
  pose proof (g3_sh_read m kp (Z.shiftr kp 3 + 2147450880) MU ltac:(lia) eq_refl SHK) as SHk.
  zstep. try rewrite (Z.mod_small kp) by lia.
  do 2 zstep.
  pose proof (G3PureA.pe_read m idx MI ltac:(lia)) as RDPE.
  zstep. unfold le_bytes_to_word. rewrite sext_extract32. change (bv_swrap 32 (bytes_le_to_Z (firstn 4 (skipn (Z.to_nat (4 * idx)) G3Pure.PE_BYTES)))) with (PEZ idx).
  set (ce := PEZ idx) in *. clearbody ce. clear RDPE.
  zstep. if_cases KT2; [cbv in KT2; discriminate | ]. clear SHk.

  set (xw := (wf * 2048)%Z) in *. set (xp := (plf * 1024)%Z) in *. set (xm := (mif * 2 ^ x)%Z) in *.
  assert (Rxw : (2 ^ 63 <= xw < 2 ^ 64)%Z) by (unfold xw; lia).
  assert (Rxp : (2 ^ 63 <= xp < 2 ^ 64)%Z) by (unfold xp; lia).
  assert (Rxm : (2 ^ 61 <= xm <= xw)%Z) by (unfold xm, xw in *; lia).
  do 3 zstep.
  rewrite (Z.shiftl_mul_pow2 plf 10) by lia. rewrite (Z.shiftl_mul_pow2 wf 11) by lia.
  replace (plf * 2 ^ 10)%Z with xp by (unfold xp; lia). replace (wf * 2 ^ 11)%Z with xw by (unfold xw; lia).
  do 12 zstep.
  rewrite (mi_shift mie ple Hple Hx). fold x. rewrite (Z.shiftl_mul_pow2 mif x) by (clear - Hx Hmif; lia). fold xm.
  set (ch := Z.shiftr cf 32) in *. set (cl := (cf mod 4294967296)%Z) in *.
  replace (Z_to_bv 64 (cf ≪ 32)) with (Z_to_bv 64 (cl * 4294967296)) by (apply zbv_eqm; rewrite shl32_mod by (clear - HPT; lia); rewrite Z.mod_small; [reflexivity | pose proof (Z.mod_pos_bound cf 4294967296 ltac:(clear; lia)); clear - H; lia]).
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
  assert (Hwl11 : (wl mod 2 ^ 11 = 0)%Z).
  { clear - Hwf. unfold wl, xw. replace 4294967296%Z with (2 ^ 21 * 2048)%Z by reflexivity. rewrite Z.mul_mod_distr_r by lia.
    replace (2 ^ 11)%Z with 2048%Z by reflexivity. apply Z.mod_mul. lia. }
  assert (Hpl10 : (pl mod 2 ^ 10 = 0)%Z).
  { clear - Hplf. unfold pl, xp. replace 4294967296%Z with (2 ^ 22 * 1024)%Z by reflexivity. rewrite Z.mul_mod_distr_r by lia.
    replace (2 ^ 10)%Z with 1024%Z by reflexivity. apply Z.mod_mul. lia. }
  assert (EMH : Z.shiftr xm 32 = mh) by reflexivity.
  assert (EXM : Z_to_bv 64 (xm ≪ 32) = Z_to_bv 64 (ml * 4294967296)) by (apply zbv_eqm; rewrite shl32_mod by (clear - Rxm; lia); rewrite (Z.mod_small (ml * 4294967296)) by (clear - Rml; lia); reflexivity).
  assert (Lxw : (xw <= xp)%Z) by (unfold xw, xp; clear - Hxw; lia).
  clearbody ch cl wh wl ph pl mh ml. clearbody xm xw xp.
  assert (Eb : Z.land (ch * wl) 4294965248 = ((ch * wl) mod 4294967296)%Z).
  { clear - Rch Rwl Hwl11. apply (land_mask_low (ch * wl) 11); [lia | apply Z.mul_nonneg_nonneg; lia | ].
    rewrite Z.mul_mod by lia. rewrite Hwl11. rewrite Z.mul_0_r. reflexivity. }
  assert (Ep : Z.land (ch * pl) 4294966272 = ((ch * pl) mod 4294967296)%Z).
  { clear - Rch Rpl Hpl10. apply (land_mask_low (ch * pl) 10); [lia | apply Z.mul_nonneg_nonneg; lia | ].
    rewrite Z.mul_mod by lia. rewrite Hpl10. rewrite Z.mul_0_r. reflexivity. }

  pose proof (prod32b ch wh Rch Rwh) as Pacw. pose proof (prod32b cl wh Rcl Rwh) as Padw. pose proof (prod32b ch ph Rch Rph) as Pacp. pose proof (prod32b cl ph Rcl Rph) as Padp.
  do 6 zstep. rewrite Ewl. zstep. rewrite Epl. clear Pacw Padw Pacp Padp.
  do 2 zstep. rewrite EMH, EXM.
  pose proof (prod32b ch wl Rch Rwl) as Pbcw. pose proof (prod32b cl wl Rcl Rwl) as Pbdw. pose proof (prod32b ch pl Rch Rpl) as Pbcp. pose proof (prod32b cl pl Rcl Rpl) as Pbdp.
  do 4 zstep. clear Pbcw Pbdw Pbcp Pbdp.
  step. rewrite (unsigned_lit (cl * 4294967296)) by (clear - Rcl; lia). rewrite (unsigned_lit (ml * 4294967296)) by (clear - Rml; lia). rewrite mulhu_shl32 by (clear - Rcl Rml; lia).
  zstep. replace (Z.shiftr (ml * 4294967296) 32) with ml by (rewrite Z.shiftr_div_pow2 by (clear; lia); change (2 ^ 32)%Z with 4294967296%Z; rewrite Z.div_mul by (clear; lia); reflexivity).
  pose proof (prod32b cl mh Rcl Rmh) as Padm. pose proof (prod32b ch mh Rch Rmh) as Pacm. pose proof (prod32b ch ml Rch Rml) as Pbcm.
  do 3 zstep.
  pose proof (prod32b ch wh Rch Rwh) as Pacw. pose proof (prod32b ch wl Rch Rwl) as Pbcw. pose proof (prod32b ch ph Rch Rph) as Pacp. pose proof (prod32b ch pl Rch Rpl) as Pbcp.
  pose proof (prod32b cl wh Rcl Rwh) as Padw. pose proof (prod32b cl wl Rcl Rwl) as Pbdw.
  pose proof (prod32b cl ph Rcl Rph) as Padp. pose proof (prod32b cl pl Rcl Rpl) as Pbdp. pose proof (prod32b cl ml Rcl Rml) as Pbdm.
  set (s := (- (ce + ple + 54))%Z).
  assert (E1 : Z_to_bv 64 (ce + we) = Z_to_bv 64 (- s - 53)) by (f_equal; unfold s; clear - Hwe; lia).
  assert (E2 : Z_to_bv 64 (ce + (ple + -10)) = Z_to_bv 64 (- s - 64)) by (f_equal; unfold s; clear; lia).
  rewrite E1, E2. clear E1 E2.
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
  - unfold s. clear - Hse. lia.
  - rewrite Mm. clear - L1. lia.
  - rewrite Mm, Mw. clear - L2. lia.
  - rewrite Mw, Mp. clear - L3. lia.
  - rewrite Mp. clear - L4. lia.
  - rewrite Mp. clear - L5. lia.
Qed.

Lemma g3_join : forall t2' a5' t3' t4' t5' t6' fc (m : word -> option byte) (vf ve k t0v t1v a1v a3v a4v a6v a7v : Z) (bs : list byte) lj kj j8,
  frm0 fc ->
  stk rsegs m (GSP - 160) (GSP - 80) ->
  rw_cells rsegs m (GSP - 80) [CB 8 j8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  munch G3_W m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
  u8arr rsegs m buf bs -> length bs = 22%nat -> rw_cells rsegs m lenp [C4 lj] -> rw_cells rsegs m kp [C4 kj] ->
  ro_cells rsegs m 0x153138 [C8 (Z_to_bv 64 0x15c9b8)] -> ro_cells rsegs m 0x15c9b8 [C8 (Z_to_bv 64 2147450880)] ->
  (0 <= k <= 52)%Z -> (1 <= vf < 2 ^ 53)%Z -> (2 ^ 53 <= (2 * vf + 1) * 2 ^ k < 2 ^ 54)%Z -> (2 ^ 52 <= vf * 2 ^ k < 2 ^ 53)%Z ->
  (-1127 <= ve - 1 - k <= 971)%Z -> (vf = 2 ^ 52 -> k = 0)%Z ->
  t0v = ((2 * vf + 1) * 2 ^ k)%Z -> t1v = (ve - 1 - k)%Z -> a1v = ve -> a3v = (ve - 1)%Z -> a4v = (ve - k)%Z -> a6v = (vf * 2 ^ k)%Z -> a7v = (2 * vf)%Z ->
  evt rsegs g3_post (MS (mkR ra (Z_to_bv 64 (GSP - 80)) gp tp (Z_to_bv 64 t0v) (Z_to_bv 64 t1v) t2' (Z_to_bv 64 lenp) (Z_to_bv 64 buf)
                             (Z_to_bv 64 vf) (Z_to_bv 64 a1v) (Z_to_bv 64 kp) (Z_to_bv 64 a3v) (Z_to_bv 64 a4v) a5' (Z_to_bv 64 a6v)
                             (Z_to_bv 64 a7v) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                        F (Z_to_bv 64 0xcf8fc) fc None m (seg_rom rsegs)).
Proof using All.
  intros until j8. intros FRM ST FR MU WM MI BU BL LE KC GOT SHV HK Hvf Hpl Hw Hple Hz E0 E1 E2 E3 E4 E6 E7. subst t0v t1v a1v a3v a4v a6v a7v.
  assert (Pk : (1 <= 2 ^ k <= 2 ^ 52)%Z) by (split; [apply (Z.pow_le_mono_r 2 0 k) | apply Z.pow_le_mono_r]; lia).
  do 5 zstep.
  if_cases K1; zify_cond K1.
  -
    do 3 zstep. if_cases K2; zify_cond K2; [ | exfalso; clear - K1 K2; lia ].
    eapply g3_tail; try eassumption.
    all: try (clear - Hple; lia).
    all: try (clear - HK Hvf Hpl; lia).
    all: try (replace (ve - 1 - (ve - 1 - k) + 10)%Z with (k + 10)%Z by (clear; lia); rewrite Z.pow_add_r by lia;
              set (P := (2 ^ k)%Z) in *; clear - Hw Pk Hvf; nia).
    all: try (set (P := (2 ^ k)%Z) in *; clear - Hw Pk Hvf Hpl; nia).
  -
    do 5 zstep. if_cases K2; zify_cond K2; [ exfalso; clear - K1 K2; lia | ].
    zstep.
    assert (k = 0)%Z by (apply Hz; exact K1). subst k. subst vf.
    eapply g3_tail; try eassumption.
    all: try (clear; lia).
    all: try (clear - Hple; lia).
    replace (ve + -2 - (ve - 1 - 0) + 10)%Z with 9%Z by (clear; lia). clear. lia.
Qed.

Lemma g3_loopB : forall (n : nat) (i kA vf a4v a6v : Z) a5' t2' t3' t4' t5' t6' fc (m : word -> option byte) (bs : list byte) lj kj j8,
  Z.to_nat (52 - i) = n ->
  frm0 fc ->
  stk rsegs m (GSP - 160) (GSP - 80) ->
  rw_cells rsegs m (GSP - 80) [CB 8 j8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  munch G3_W m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
  u8arr rsegs m buf bs -> length bs = 22%nat -> rw_cells rsegs m lenp [C4 lj] -> rw_cells rsegs m kp [C4 kj] ->
  ro_cells rsegs m 0x153138 [C8 (Z_to_bv 64 0x15c9b8)] -> ro_cells rsegs m 0x15c9b8 [C8 (Z_to_bv 64 2147450880)] ->
  (1 <= vf < 2 ^ 52)%Z -> (0 <= i)%Z -> a6v = (vf * 2 ^ i)%Z -> a4v = (-1074 - i)%Z -> (a6v < 2 ^ 52)%Z ->
  (1 <= kA <= 52)%Z -> (2 ^ 53 <= (2 * vf + 1) * 2 ^ kA < 2 ^ 54)%Z ->
  evt rsegs g3_post (MS (mkR ra (Z_to_bv 64 (GSP - 80)) gp tp (Z_to_bv 64 ((2 * vf + 1) * 2 ^ kA)) (Z_to_bv 64 (-1075 - kA)) t2' (Z_to_bv 64 lenp) (Z_to_bv 64 buf)
        (Z_to_bv 64 vf) (Z_to_bv 64 (-1074)) (Z_to_bv 64 kp) (Z_to_bv 64 (-1075)) (Z_to_bv 64 a4v) a5' (Z_to_bv 64 a6v)
        (Z_to_bv 64 (2 * vf)) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
     F (Z_to_bv 64 0xcf8ec) fc None m (seg_rom rsegs)).
Proof using All.
  induction n as [n IH] using lt_wf_ind.
  intros i kA vf a4v a6v a5' t2' t3' t4' t5' t6' fc m bs lj kj j8 Hn FRM ST FR MU WM MI BU BL LE KC GOT SHV Hvf Hi E6 E4 H6 HkA HpA.
  assert (Pi : (1 <= 2 ^ i)%Z) by (apply (Z.pow_le_mono_r 2 0 i); lia).
  subst a6v a4v.
  do 4 zstep.
  rewrite (Z.shiftl_mul_pow2 (vf * 2 ^ i) 12), (Z.shiftl_mul_pow2 (vf * 2 ^ i) 1) by lia.
  if_cases K; zify_cond K.
  -
    assert (Hi51 : (i < 51)%Z).
    { destruct (Z_lt_le_dec i 51) as [?|L]; [lia|]. assert (2 ^ 51 <= 2 ^ i)%Z by (apply Z.pow_le_mono_r; lia). clear - K H Hvf. nia. }
    eapply (IH (Z.to_nat (52 - (i + 1)))); [lia | reflexivity | eassumption .. | | | | | | | ].
    all: try (clear - Hvf; lia).
    all: try (clear - Hi; lia).
    all: try (clear - HkA; lia).
    all: try exact HpA.
    + rewrite Z.pow_add_r by lia. ring.
    + clear - K. lia.
  -
    assert (Hw : (2 ^ 52 <= vf * 2 ^ (i + 1) < 2 ^ 53)%Z) by (rewrite Z.pow_add_r by lia; clear - K H6; lia).
    assert (EkA : kA = (i + 1)%Z) by (apply (nrm_unique vf); lia).
    subst kA.
    eapply (g3_join _ _ _ _ _ _ fc m vf (-1074) (i + 1)); try eassumption.
    all: try (clear - HkA; lia).
    all: try (clear - Hvf; lia).
    all: try reflexivity.
    all: try (rewrite Z.pow_add_r by lia; ring).
    all: try (clear; lia).
Qed.

Lemma g3_loopA : forall (n : nat) (i vf t0v t1v : Z) a4' t2' t3' t4' t5' t6' fc (m : word -> option byte) (bs : list byte) lj kj j8,
  Z.to_nat (52 - i) = n ->
  frm0 fc ->
  stk rsegs m (GSP - 160) (GSP - 80) ->
  rw_cells rsegs m (GSP - 80) [CB 8 j8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  munch G3_W m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
  u8arr rsegs m buf bs -> length bs = 22%nat -> rw_cells rsegs m lenp [C4 lj] -> rw_cells rsegs m kp [C4 kj] ->
  ro_cells rsegs m 0x153138 [C8 (Z_to_bv 64 0x15c9b8)] -> ro_cells rsegs m 0x15c9b8 [C8 (Z_to_bv 64 2147450880)] ->
  (1 <= vf < 2 ^ 52)%Z -> (0 <= i)%Z -> t0v = ((2 * vf + 1) * 2 ^ i)%Z -> t1v = (-1075 - i)%Z -> (t0v < 2 ^ 53)%Z ->
  evt rsegs g3_post (MS (mkR ra (Z_to_bv 64 (GSP - 80)) gp tp (Z_to_bv 64 t0v) (Z_to_bv 64 t1v) t2' (Z_to_bv 64 lenp) (Z_to_bv 64 buf)
        (Z_to_bv 64 vf) (Z_to_bv 64 (-1074)) (Z_to_bv 64 kp) (Z_to_bv 64 (-1075)) a4' (Z_to_bv 64 4503599627370496) (Z_to_bv 64 vf)
        (Z_to_bv 64 (2 * vf)) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
     F (Z_to_bv 64 0xcf8d8) fc None m (seg_rom rsegs)).
Proof using All.
  induction n as [n IH] using lt_wf_ind.
  intros i vf t0v t1v a4' t2' t3' t4' t5' t6' fc m bs lj kj j8 Hn FRM ST FR MU WM MI BU BL LE KC GOT SHV Hvf Hi E0 E1 H0.
  assert (Pi : (1 <= 2 ^ i)%Z) by (apply (Z.pow_le_mono_r 2 0 i); lia).
  assert (Hi51 : (i <= 51)%Z).
  { destruct (Z_le_gt_dec i 51) as [?|L]; [lia|]. assert (2 ^ 52 <= 2 ^ i)%Z by (apply Z.pow_le_mono_r; lia). clear - E0 H0 H Hvf. nia. }
  subst t0v t1v.
  do 4 zstep.
  rewrite (Z.shiftl_mul_pow2 ((2 * vf + 1) * 2 ^ i) 1) by lia.
  assert (LB := land_bit ((2 * vf + 1) * 2 ^ i) 52 ltac:(lia) ltac:(split; [lia | exact H0])).
  change (2 ^ 52)%Z with 4503599627370496%Z in LB.
  if_cases K; zify_cond K.
  -
    apply LB in K.
    eapply (IH (Z.to_nat (52 - (i + 1)))); [lia | reflexivity | eassumption .. | | | | | ].
    all: try (clear - Hvf; lia).
    all: try (clear - Hi; lia).
    + rewrite Z.pow_add_r by lia. ring.
    + clear - K. lia.
  -
    assert (K' : (4503599627370496 <= (2 * vf + 1) * 2 ^ i)%Z) by (destruct (Z_lt_le_dec ((2 * vf + 1) * 2 ^ i) 4503599627370496) as [L|L]; [exfalso; apply K; apply LB; exact L | exact L]).
    zstep.
    replace (Z_to_bv 64 ((2 * vf + 1) * 2 ^ i * 2)) with (Z_to_bv 64 ((2 * vf + 1) * 2 ^ (i + 1))) by (f_equal; rewrite Z.pow_add_r by lia; ring).
    replace (Z_to_bv 64 (-1075 - i + -1)) with (Z_to_bv 64 (-1075 - (i + 1))) by (f_equal; lia).
    eapply (g3_loopB (Z.to_nat (52 - 0)) 0 (i + 1) vf (-1074) vf); try reflexivity; try eassumption.
    all: try (clear - Hvf; lia).
    all: try (clear - Hi Hi51; lia).
    rewrite Z.pow_add_r by lia. clear - K' H0. lia.
Qed.

Lemma g3_spec : forall t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 fc (m : word -> option byte) (b : Z) (bs : list byte) lj kj,
  bv_unsigned (reg_get F 10) = b -> (1 <= b < 2 ^ 63)%Z -> frm0 fc ->
  stk rsegs m (GSP - 160) GSP -> u8arr rsegs m buf bs -> length bs = 22%nat ->
  rw_cells rsegs m lenp [C4 lj] -> rw_cells rsegs m kp [C4 kj] ->
  ro_cells rsegs m 0x153138 [C8 (Z_to_bv 64 0x15c9b8)] -> ro_cells rsegs m 0x15c9b8 [C8 (Z_to_bv 64 2147450880)] ->
  mem_inv rsegs m -> m = m0 ->
  evt rsegs g3_post (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 buf) (Z_to_bv 64 lenp) (Z_to_bv 64 kp) a3 a4 a5 a6 a7
                             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 0xcf84c) fc None m (seg_rom rsegs)).
Proof using All.
  intros until kj. intros Hb HbR FRM ST BU BL LE KC GOT SHV MI ->.
  pose proof (munch_refl G3_W m0) as MU. pose proof (wmono_refl rsegs m0) as WM. unfold G3WalkA.G3_W in MU.
  unfold G3WalkA.GSP in *.
  carve_frame 80%nat ST.
  do 10 zstep.
  do 4 zstep.
  set (bw := reg_get F 10) in *.
  do 7 zstep.
  rewrite Hb. rewrite exp_bits by lia. rewrite mant_bits.
  rewrite lor_hidden by (apply Z.mod_pos_bound; lia).
  assert (Eb : (b = Z.shiftr b 52 * 2 ^ 52 + b mod 2 ^ 52)%Z) by (rewrite Z.shiftr_div_pow2 by lia; pose proof (Z.div_mod b (2 ^ 52)); lia).
  assert (RE : (0 <= Z.shiftr b 52 <= 2047)%Z) by (rewrite Z.shiftr_div_pow2 by lia; split; [apply Z.div_pos; lia | apply Z.lt_succ_r, Z.div_lt_upper_bound; lia]).
  assert (Rmm : (0 <= b mod 2 ^ 52 < 2 ^ 52)%Z) by (apply Z.mod_pos_bound; lia).
  set (E := Z.shiftr b 52) in *. set (mm := (b mod 2 ^ 52)%Z) in *. clearbody E mm.
  replace (bv_unsigned sp + -80)%Z with (bv_unsigned sp - 80)%Z in * by lia.
  zstep. if_cases K0; zify_cond K0.
  -
    subst E.
    do 3 zstep. if_cases K1; zify_cond K1; [exfalso; lia | ].
    do 5 zstep. if_cases K2; zify_cond K2; [ | exfalso; lia ].
    zstep.
    rewrite !(Z.shiftl_mul_pow2 mm 1) by lia.
    replace (Z_to_bv 64 (mm * 2 ^ 1)) with (Z_to_bv 64 (2 * mm)) by (f_equal; ring).
    assert (Hmm : (1 <= mm)%Z) by (clear - Eb HbR; lia).
    eapply (g3_loopA (Z.to_nat (52 - 0)) 0 mm); try reflexivity; try eassumption.
    all: rewrite ?Z.pow_0_r.
    all: try (clear - Hmm Rmm; lia).
  -
    do 4 zstep. if_cases K1; zify_cond K1; [ | exfalso; lia ].
    do 4 zstep. if_cases K2; zify_cond K2; [exfalso; lia | ].
    do 3 zstep.
    rewrite !(Z.shiftl_mul_pow2 (mm + 4503599627370496) 1) by lia.
    eapply (g3_join _ _ _ _ _ _ fc _ (mm + 4503599627370496) (E + -1075) 0); try eassumption.
    all: rewrite ?Z.pow_0_r.
    all: try (clear - Rmm; lia).
    all: try (clear - RE K0; lia).
    all: try (clear; lia).
Qed.
End G3B.
