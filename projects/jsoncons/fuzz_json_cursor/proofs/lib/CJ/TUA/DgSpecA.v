(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib Require Import Tac ZBridge.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.TUA Require Import DgWalkA.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section DGB.

Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word.
Variable F : bvmap 5 word.
Variable fc : bv 32.
Variable m0 : word -> option byte.
Variables buf lenp kp : Z.

Local Notation SP0 := (DgWalkA.SP0 sp).

Hypothesis BUFR : (4096 <= buf /\ buf + 21 <= 2^47)%Z.
Hypothesis SPR0 : (2^40 <= SP0 /\ SP0 + 8 <= 2^47)%Z.

Hypothesis KL : lenp = (kp + 4)%Z.
Hypothesis KS : (SP0 + 8 <= kp /\ kp + 8 <= 2^47)%Z.
Hypothesis SEP_B : (buf + 21 <= SP0 - 80 \/ lenp + 4 <= buf)%Z.

Local Notation app_buf := (DgWalkA.app_buf buf).
Hypothesis APP_B : app_buf.
Hypothesis APP_S : (0x10007fff8000 <= SP0 - 80)%Z.

Hypothesis SHL : mrd rsegs m0 (wa (Z.shiftr lenp 3 + 2147450880)) = Some (Z_to_bv 8 0).
Hypothesis SHK : mrd rsegs m0 (wa (Z.shiftr kp 3 + 2147450880)) = Some (Z_to_bv 8 0).
Hypothesis SHBUF : forall k, (0 <= k < 21)%Z -> mrd rsegs m0 (wa (Z.shiftr (buf + k) 3 + 2147450880)) = Some (Z_to_bv 8 0).

Local Notation DG_W := (DgWalkA.DG_W sp buf lenp kp).
Local Notation dg_post := (DgWalkA.dg_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 buf lenp kp).
Local Notation dg_mem := (DgWalkA.dg_mem ra sp s0 s1 s2 s3 s4 s5 s6 s7 m0 buf lenp kp).
Local Notation L x := (x ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 buf lenp kp BUFR SPR0 KL KS SEP_B APP_B APP_S SHL SHK SHBUF).
Local Notation sh_read := (L DgWalkA.sh_read).
Local Notation dg_rw1_entry := (L DgWalkA.dg_rw1_entry).
Local Notation dg_loop2 := (L DgWalkA.dg_loop2).
Ltac dg_mem_intro H := destruct H as (ST & FR & MU & WM & MI & BU & BL & LE & KC); unfold DgWalkA.DG_W in MU.

Lemma dg_l1_k1 : forall (p1 len p2 D s Wp1 Ks : Z) t2' a1' a2' a5' s5' s6' s7' (m : word -> option byte) j8 (bs : list byte),
  dg_mem m j8 len Ks bs -> (0 <= len <= 2)%Z -> (- 2 ^ 31 + 18 <= Ks <= 2 ^ 31 - 3)%Z ->
  (56 <= s <= 59)%Z -> (0 <= p1 < 10)%Z -> (0 <= p2 < 2 ^ s)%Z -> (2 <= D < 2 ^ 64)%Z ->
  (len = 0 -> p1 * 2 ^ s + p2 = Wp1 /\ D <= Wp1 /\ 8 <= p1)%Z ->
  evt rsegs (dg_post Ks) (MS (mkR ra (Z_to_bv 64 (SP0 - 80)) gp tp (Z_to_bv 64 2147450880) (Z_to_bv 64 (Z.shiftr lenp 3 + 2147450880)) t2' (Z_to_bv 64 2) (Z_to_bv 64 1)
                                  (Z_to_bv 64 kp) a1' a2' (Z_to_bv 64 D) (Z_to_bv 64 (2 ^ s)) a5' (Z_to_bv 64 buf) (Z_to_bv 64 lenp)
                                  (Z_to_bv 64 1) (Z_to_bv 64 p1) (Z_to_bv 64 (0xcccccccd * 2 ^ 32)) s5' s6' s7' s8 s9 s10 s11
                                  (Z_to_bv 64 p2) (Z_to_bv 64 s) (Z_to_bv 64 (2 ^ 32 - 1)) (Z_to_bv 64 (2 ^ s - 1)))
                              F (Z_to_bv 64 0xd0378) fc None m (seg_rom rsegs)).
Proof using All.
  intros until bs. intros HM LR KsR Hs Hp1 Hp2 HD Hinv.
  pose proof HM as HM0. dg_mem_intro HM.
  assert (H2s : (2 ^ 56 <= 2 ^ s <= 2 ^ 59)%Z) by (split; apply Z.pow_le_mono_r; lia).
  pose proof (sh_read m lenp (Z.shiftr lenp 3 + 2147450880) MU ltac:(lia) eq_refl SHL) as SHl.
  assert (BODY : (1 <= p1 \/ 1 <= len)%Z -> forall a1x, evt rsegs (dg_post Ks)
     (MS (mkR ra (Z_to_bv 64 (SP0 - 80)) gp tp (Z_to_bv 64 2147450880) (Z_to_bv 64 (Z.shiftr lenp 3 + 2147450880)) t2' (Z_to_bv 64 2) (Z_to_bv 64 1)
              (Z_to_bv 64 kp) a1x a2' (Z_to_bv 64 D) (Z_to_bv 64 (2 ^ s)) a5' (Z_to_bv 64 buf) (Z_to_bv 64 lenp)
              (Z_to_bv 64 1) (Z_to_bv 64 p1) (Z_to_bv 64 14757395259826634752) (Z_to_bv 64 p1) s6' s7' s8 s9 s10 s11
              (Z_to_bv 64 p2) (Z_to_bv 64 s) (Z_to_bv 64 4294967295) (Z_to_bv 64 (2 ^ s - 1)))
         F (Z_to_bv 64 0xd0394) fc None m (seg_rom rsegs))).
  { intros Hem a1x.
    zstep; zstep; if_cases K0b; [cbv in K0b; discriminate | ].
    zstep; rewrite sx32_small by lia.
    do 3 zstep.
    clear SHl.
    pose proof (sh_read m1 (buf + len) (Z.shiftr (buf + len) 3 + 2147450880) ltac:(unfold DgWalkA.DG_W; exact MU) ltac:(lia) eq_refl (SHBUF len ltac:(lia))) as SHb.
    do 4 zstep; if_cases K0c; [cbv in K0c; discriminate | ].
    clear SHb.
    zstep.
    pose proof (u8arr_store_ok rsegs m1 buf bs len (Z_to_bv 64 (buf + len)) BU ltac:(lia) ltac:(unfold wa; f_equal; lia)) as SOK.
    zstep.
    replace (write_to_mem m1 (Z_to_bv 64 (buf + len)) (le1 (Z_to_bv 64 (p1 + 48)))) with (write_to_mem m1 (wa (buf + len)) [Z_to_bv 8 (p1 + 48)])
      by (f_equal; symmetry; apply le1_lit).
    pose proof (u8arr_write rsegs m1 buf bs len (Z_to_bv 8 (p1 + 48)) BU ltac:(lia)) as BU'.
    clear BU; store_done.
    assert (HM2 : dg_mem m2 j8 (len + 1) Ks (upd bs (Z.to_nat len) (Z_to_bv 8 (p1 + 48))))
      by (unfold DgWalkA.dg_mem; split; [exact ST|]; split; [exact FR|]; split; [exact MU|]; split; [exact WM|]; split; [exact MI|]; split; [exact BU'|];
          split; [rewrite upd_length; exact BL|]; split; [exact LE | exact KC]).
    do 4 zstep.
    rewrite Z.mul_1_r, Z.sub_diag, swrap32_small, Z.mod_0_l, Z.shiftl_0_l, Z.add_0_l by lia.
    zstep; if_cases K3; zify_cond K3.
    - eapply (dg_rw1_entry D p2 1 2 s (len + 1) Ks); [exact HM2 | lia | lia | lia | left; reflexivity | lia | lia | lia].
    - do 5 zstep.
      if_cases K4; zify_cond K4; [lia | ].
      do 4 zstep.
      eapply (dg_loop2 (Z.to_nat (17 - 0)) 0 p2 D s (len + 1) Ks); [reflexivity | exact HM2 | lia | lia | lia | lia | lia | cbn; lia]. }
  zstep. rewrite Z.add_0_r, swrap32_small by lia.
  zstep. rewrite v_divuw_small by lia. rewrite Z.div_1_r.
  zstep. if_cases K1; zify_cond K1.
  - apply BODY. lia.
  - zstep; zstep; if_cases K0a; [cbv in K0a; discriminate | ]; zstep; rewrite sx32_small by lia; zstep; if_cases K2; zify_cond K2.
    + exfalso; destruct (Hinv ltac:(lia)) as (_ & _ & H8); lia.
    + apply BODY. lia.
Qed.

Lemma dg_l1_k2 : forall (p1 len p2 D s Wp1 Ks : Z) t2' a1' a2' a5' s5' s6' s7' (m : word -> option byte) j8 (bs : list byte),
  dg_mem m j8 len Ks bs -> (0 <= len <= 1)%Z -> (- 2 ^ 31 + 18 <= Ks <= 2 ^ 31 - 3)%Z ->
  (56 <= s <= 59)%Z -> (0 <= p1 < 100)%Z -> (0 <= p2 < 2 ^ s)%Z -> (2 <= D < 2 ^ 64)%Z ->
  (len = 0 -> p1 * 2 ^ s + p2 = Wp1 /\ D <= Wp1 /\ 8 <= p1)%Z ->
  evt rsegs (dg_post Ks) (MS (mkR ra (Z_to_bv 64 (SP0 - 80)) gp tp (Z_to_bv 64 2147450880) (Z_to_bv 64 (Z.shiftr lenp 3 + 2147450880)) t2' (Z_to_bv 64 3) (Z_to_bv 64 10)
                                  (Z_to_bv 64 kp) a1' a2' (Z_to_bv 64 D) (Z_to_bv 64 (2 ^ s)) a5' (Z_to_bv 64 buf) (Z_to_bv 64 lenp)
                                  (Z_to_bv 64 1) (Z_to_bv 64 p1) (Z_to_bv 64 (0xcccccccd * 2 ^ 32)) s5' s6' s7' s8 s9 s10 s11
                                  (Z_to_bv 64 p2) (Z_to_bv 64 s) (Z_to_bv 64 (2 ^ 32 - 1)) (Z_to_bv 64 (2 ^ s - 1)))
                              F (Z_to_bv 64 0xd0378) fc None m (seg_rom rsegs)).
Proof using All.
  intros until bs. intros HM LR KsR Hs Hp1 Hp2 HD Hinv.
  pose proof HM as HM0. dg_mem_intro HM.
  assert (H2s : (2 ^ 56 <= 2 ^ s <= 2 ^ 59)%Z) by (split; apply Z.pow_le_mono_r; lia).
  pose proof (Z.mod_pos_bound p1 10 ltac:(lia)) as Hpm.
  assert (Hprod : (0 <= p1 mod 10 * 2 ^ s <= 9 * 2 ^ s)%Z) by (split; [apply Z.mul_nonneg_nonneg; lia | apply Z.mul_le_mono_nonneg_r; lia]).
  pose proof (sh_read m lenp (Z.shiftr lenp 3 + 2147450880) MU ltac:(lia) eq_refl SHL) as SHl.
  assert (BODY : forall a1x, evt rsegs (dg_post Ks)
     (MS (mkR ra (Z_to_bv 64 (SP0 - 80)) gp tp (Z_to_bv 64 2147450880) (Z_to_bv 64 (Z.shiftr lenp 3 + 2147450880)) t2' (Z_to_bv 64 3) (Z_to_bv 64 10)
              (Z_to_bv 64 kp) a1x a2' (Z_to_bv 64 D) (Z_to_bv 64 (2 ^ s)) a5' (Z_to_bv 64 buf) (Z_to_bv 64 lenp)
              (Z_to_bv 64 1) (Z_to_bv 64 p1) (Z_to_bv 64 14757395259826634752) (Z_to_bv 64 (p1 / 10)) s6' s7' s8 s9 s10 s11
              (Z_to_bv 64 p2) (Z_to_bv 64 s) (Z_to_bv 64 4294967295) (Z_to_bv 64 (2 ^ s - 1)))
         F (Z_to_bv 64 0xd0394) fc None m (seg_rom rsegs))).
  { intros a1x.
    zstep; zstep; if_cases K0b; [cbv in K0b; discriminate | ].
    zstep; rewrite sx32_small by lia.
    do 3 zstep.
    clear SHl.
    pose proof (sh_read m1 (buf + len) (Z.shiftr (buf + len) 3 + 2147450880) ltac:(unfold DgWalkA.DG_W; exact MU) ltac:(lia) eq_refl (SHBUF len ltac:(lia))) as SHb.
    do 4 zstep; if_cases K0c; [cbv in K0c; discriminate | ].
    clear SHb.
    zstep.
    pose proof (u8arr_store_ok rsegs m1 buf bs len (Z_to_bv 64 (buf + len)) BU ltac:(lia) ltac:(unfold wa; f_equal; lia)) as SOK.
    zstep.
    replace (write_to_mem m1 (Z_to_bv 64 (buf + len)) (le1 (Z_to_bv 64 (p1 / 10 + 48)))) with (write_to_mem m1 (wa (buf + len)) [Z_to_bv 8 (p1 / 10 + 48)])
      by (f_equal; symmetry; apply le1_lit).
    pose proof (u8arr_write rsegs m1 buf bs len (Z_to_bv 8 (p1 / 10 + 48)) BU ltac:(lia)) as BU'.
    clear BU; store_done.
    assert (HM2 : dg_mem m2 j8 (len + 1) Ks (upd bs (Z.to_nat len) (Z_to_bv 8 (p1 / 10 + 48))))
      by (unfold DgWalkA.dg_mem; split; [exact ST|]; split; [exact FR|]; split; [exact MU|]; split; [exact WM|]; split; [exact MI|]; split; [exact BU'|];
          split; [rewrite upd_length; exact BL|]; split; [exact LE | exact KC]).
    do 4 zstep.
    rewrite subw_mod, shl_s by lia.
    zstep; if_cases K3; zify_cond K3.
    - eapply (dg_rw1_entry D (p1 mod 10 * 2 ^ s + p2) 10 3 s (len + 1) Ks); [exact HM2 | lia | lia | lia | right; left; reflexivity | lia | lia | lia].
    - do 5 zstep.
      if_cases K4; zify_cond K4; [ | lia].
      eapply (dg_l1_k1 (p1 mod 10) (len + 1) p2 D s Wp1 Ks); [exact HM2 | lia | lia | lia | lia | lia | lia | lia]. }
  zstep. rewrite Z.add_0_r, swrap32_small by lia.
  zstep. rewrite v_divuw_small by lia.
  zstep. if_cases K1; zify_cond K1.
  - apply BODY.
  - zstep; zstep; if_cases K0a; [cbv in K0a; discriminate | ]; zstep; rewrite sx32_small by lia; zstep; if_cases K2; zify_cond K2.
    +
      destruct (Hinv ltac:(lia)) as (Hw & HDw & H8).
      do 4 zstep; rewrite (Z.div_small p1 10), Z.mul_0_l, Z.sub_0_r, swrap32_small, shl_s by lia.
      zstep; if_cases K3; zify_cond K3; [lia | ].
      do 5 zstep; if_cases K4; zify_cond K4; [ | lia].
      eapply (dg_l1_k1 p1 len p2 D s Wp1 Ks); [exact HM0 | lia | lia | lia | lia | lia | lia | intros _; lia].
    + apply BODY.
Qed.

Lemma dg_l1_k3 : forall (p1 len p2 D s Wp1 Ks : Z) t2' a1' a2' a5' s5' s6' s7' (m : word -> option byte) j8 (bs : list byte),
  dg_mem m j8 len Ks bs -> (0 <= len <= 0)%Z -> (- 2 ^ 31 + 18 <= Ks <= 2 ^ 31 - 3)%Z ->
  (56 <= s <= 59)%Z -> (0 <= p1 < 256)%Z -> (0 <= p2 < 2 ^ s)%Z -> (2 <= D < 2 ^ 64)%Z ->
  (len = 0 -> p1 * 2 ^ s + p2 = Wp1 /\ D <= Wp1 /\ 8 <= p1)%Z -> (p1 * 2 ^ s + p2 < 2 ^ 64)%Z ->
  evt rsegs (dg_post Ks) (MS (mkR ra (Z_to_bv 64 (SP0 - 80)) gp tp (Z_to_bv 64 2147450880) (Z_to_bv 64 (Z.shiftr lenp 3 + 2147450880)) t2' (Z_to_bv 64 4) (Z_to_bv 64 100)
                                  (Z_to_bv 64 kp) a1' a2' (Z_to_bv 64 D) (Z_to_bv 64 (2 ^ s)) a5' (Z_to_bv 64 buf) (Z_to_bv 64 lenp)
                                  (Z_to_bv 64 1) (Z_to_bv 64 p1) (Z_to_bv 64 (0xcccccccd * 2 ^ 32)) s5' s6' s7' s8 s9 s10 s11
                                  (Z_to_bv 64 p2) (Z_to_bv 64 s) (Z_to_bv 64 (2 ^ 32 - 1)) (Z_to_bv 64 (2 ^ s - 1)))
                              F (Z_to_bv 64 0xd0378) fc None m (seg_rom rsegs)).
Proof using All.
  intros until bs. intros HM LR KsR Hs Hp1 Hp2 HD Hinv HX.
  pose proof HM as HM0. dg_mem_intro HM.
  assert (H2s : (2 ^ 56 <= 2 ^ s <= 2 ^ 59)%Z) by (split; apply Z.pow_le_mono_r; lia).
  pose proof (Z.mod_pos_bound p1 100 ltac:(lia)) as Hpm.
  assert (Hprod : (0 <= p1 mod 100 * 2 ^ s <= p1 * 2 ^ s)%Z)
    by (split; [apply Z.mul_nonneg_nonneg; lia | apply Z.mul_le_mono_nonneg_r; [lia | apply Z.mod_le; lia]]).
  pose proof (sh_read m lenp (Z.shiftr lenp 3 + 2147450880) MU ltac:(lia) eq_refl SHL) as SHl.
  zstep. rewrite Z.add_0_r, swrap32_small by lia.
  zstep. rewrite v_divuw_small by lia.
  zstep. if_cases K1; zify_cond K1;
    [ | zstep; zstep; if_cases K0a; [cbv in K0a; discriminate | ]; zstep; rewrite sx32_small by lia; zstep; if_cases K2; zify_cond K2; [ | lia] ].
  2:
     destruct (Hinv ltac:(lia)) as (Hw & HDw & H8);
     do 4 zstep; rewrite (Z.div_small p1 100), Z.mul_0_l, Z.sub_0_r, swrap32_small, shl_s by lia;
     zstep; if_cases K3; zify_cond K3; [lia | ];
     do 5 zstep; if_cases K4; zify_cond K4; [ | lia];
     eapply (dg_l1_k2 p1 len p2 D s Wp1 Ks); [exact HM0 | lia | lia | lia | lia | lia | lia | intros _; lia].

  zstep; zstep; if_cases K0b; [cbv in K0b; discriminate | ].
  zstep; rewrite sx32_small by lia.
  do 3 zstep.
  clear SHl.
  pose proof (sh_read m1 (buf + len) (Z.shiftr (buf + len) 3 + 2147450880) ltac:(unfold DgWalkA.DG_W; exact MU) ltac:(lia) eq_refl (SHBUF len ltac:(lia))) as SHb.
  do 4 zstep; if_cases K0c; [cbv in K0c; discriminate | ].
  clear SHb.
  zstep.
  pose proof (u8arr_store_ok rsegs m1 buf bs len (Z_to_bv 64 (buf + len)) BU ltac:(lia) ltac:(unfold wa; f_equal; lia)) as SOK.
  zstep.
  replace (write_to_mem m1 (Z_to_bv 64 (buf + len)) (le1 (Z_to_bv 64 (p1 / 100 + 48)))) with (write_to_mem m1 (wa (buf + len)) [Z_to_bv 8 (p1 / 100 + 48)])
    by (f_equal; symmetry; apply le1_lit).
  pose proof (u8arr_write rsegs m1 buf bs len (Z_to_bv 8 (p1 / 100 + 48)) BU ltac:(lia)) as BU'.
  clear BU; store_done.
  assert (HM2 : dg_mem m2 j8 (len + 1) Ks (upd bs (Z.to_nat len) (Z_to_bv 8 (p1 / 100 + 48))))
    by (unfold DgWalkA.dg_mem; split; [exact ST|]; split; [exact FR|]; split; [exact MU|]; split; [exact WM|]; split; [exact MI|]; split; [exact BU'|];
        split; [rewrite upd_length; exact BL|]; split; [exact LE | exact KC]).
  do 4 zstep.
  rewrite subw_mod, shl_s by lia.
  zstep; if_cases K3; zify_cond K3.
  - eapply (dg_rw1_entry D (p1 mod 100 * 2 ^ s + p2) 100 4 s (len + 1) Ks); [exact HM2 | lia | lia | lia | right; right; reflexivity | lia | lia | lia].
  - do 5 zstep.
    if_cases K4; zify_cond K4; [ | lia].
    eapply (dg_l1_k2 (p1 mod 100) (len + 1) p2 D s Wp1 Ks); [exact HM2 | lia | lia | lia | lia | lia | lia | lia].
Qed.

Lemma dg_spec : forall t0 t1 t2 t3 t4 t5 t6 (m : word -> option byte) (Wm dW dP s Ks : Z) (bs : list byte) lj,
  (56 <= s <= 59)%Z -> (1 <= Wm)%Z -> (0 <= dW)%Z -> (0 <= dP)%Z -> (Wm + dW + dP <= 2 ^ 64 - 2)%Z -> (2 ^ 62 <= Wm + dW + dP + 1)%Z ->
  (- 2 ^ 31 + 18 <= Ks <= 2 ^ 31 - 3)%Z ->
  stk rsegs m (SP0 - 80) SP0 -> rw_cells rsegs m SP0 [C8 (Z_to_bv 64 kp)] ->
  u8arr rsegs m buf bs -> length bs = 21%nat -> rw_cells rsegs m lenp [C4 lj] -> rw_cells rsegs m kp [C4 (Z_to_bv 64 Ks)] ->
  ro_cells rsegs m 0x153138 [C8 (Z_to_bv 64 0x15c9b8)] -> ro_cells rsegs m 0x15c9b8 [C8 (Z_to_bv 64 2147450880)] ->
  mem_inv rsegs m -> m = m0 ->
  evt rsegs (dg_post Ks) (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Wm) (Z_to_bv 64 (2 ^ 32 - s)) (Z_to_bv 64 (Wm + dW)) (Z_to_bv 64 (2 ^ 32 - s))
                                  (Z_to_bv 64 (Wm + dW + dP)) (Z_to_bv 64 (2 ^ 32 - s)) (Z_to_bv 64 buf) (Z_to_bv 64 lenp)
                                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                              F (Z_to_bv 64 0xd02b8) fc None m (seg_rom rsegs)).
Proof using All.
  intros until lj. intros Hs HWm HdW HdP Hsum HWp HKs ST KPc BU BL LE KC GOT SHV MI ->.
  pose proof (munch_refl DG_W m0) as MU. pose proof (wmono_refl rsegs m0) as WM.
  pose proof (munch_refl [((SP0 - 80)%Z, SP0)] m0) as MUf. pose proof (wmono_refl rsegs m0) as WMf.
  assert (H2s : (2 ^ 56 <= 2 ^ s <= 2 ^ 59)%Z) by (split; apply Z.pow_le_mono_r; lia).

  assert (BOX : rw_cells rsegs m0 SP0 [C8 (Z_to_bv 64 kp)] /\ u8arr rsegs m0 buf bs /\ rw_cells rsegs m0 lenp [C4 lj] /\ rw_cells rsegs m0 kp [C4 (Z_to_bv 64 Ks)] /\
                ro_cells rsegs m0 0x153138 [C8 (Z_to_bv 64 0x15c9b8)] /\ ro_cells rsegs m0 0x15c9b8 [C8 (Z_to_bv 64 2147450880)])
    by exact (conj KPc (conj BU (conj LE (conj KC (conj GOT SHV))))).
  clear KPc BU LE KC GOT SHV.
  unfold DgWalkA.DG_W in MU. unfold DgWalkA.SP0 in *.
  carve_frame 80%nat ST.
  do 10 zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    destruct BOX as (KPc0 & BU0 & LE0 & KC0 & GOT0 & SHV0);
    pose proof (rw_cells_transport rsegs _ m0 mm _ _ KPc0 MUf WMf ltac:(cbn [disjoint_from]; cbn; lia)) as KPc;
    pose proof (u8arr_transport rsegs _ m0 mm _ _ BU0 MUf WMf ltac:(cbn [disjoint_from]; rewrite BL; cbn; lia)) as BU;
    pose proof (rw_cells_transport rsegs _ m0 mm _ _ LE0 MUf WMf ltac:(cbn [disjoint_from]; cbn; lia)) as LE;
    pose proof (rw_cells_transport rsegs _ m0 mm _ _ KC0 MUf WMf ltac:(cbn [disjoint_from]; cbn; lia)) as KC;
    pose proof (ro_cells_transport rsegs _ m0 mm _ _ GOT0 MUf ltac:(cbn [disjoint_from]; cbn; lia)) as GOT;
    pose proof (ro_cells_transport rsegs _ m0 mm _ _ SHV0 MUf ltac:(cbn [disjoint_from]; cbn; lia)) as SHV;
    clear KPc0 BU0 LE0 KC0 GOT0 SHV0
  end.
  clear MUf WMf.
  do 3 zstep. if_cases K0; [rewrite bv_eqb_refl in K0; discriminate | ].
  do 2 zstep. if_cases K1; zify_cond K1; [lia | ].
  do 2 zstep. if_cases K0b; [rewrite bv_eqb_refl in K0b; discriminate | ].
  zstep. if_cases K2; zify_cond K2; [lia | ].
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (sh_read mm lenp (Z.shiftr lenp 3 + 2147450880) ltac:(unfold DgWalkA.DG_W, DgWalkA.SP0; exact MU) ltac:(lia) eq_refl SHL) as SHl end.
  do 8 zstep. if_cases K3; [cbv in K3; discriminate | ].
  clear SHl.
  do 22 zstep.
  assert (HsE : (bv_swrap 32 (0 - (4294967296 - s)) mod 18446744073709551616)%Z = s).
  { unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. cbn -[Z.pow]. change (2 ^ 32 / 2)%Z with (2 ^ 31)%Z.
    replace (0 - (4294967296 - s) + 2 ^ 31)%Z with ((s + 2 ^ 31) + (-1) * 2 ^ 32)%Z by lia. rewrite Z.mod_add by lia.
    rewrite Z.mod_small by lia. rewrite Z.mod_small by lia. lia. }
  rewrite HsE. rewrite (Z.mod_small s 64), (Z.mod_small s 4294967296) by lia.
  rewrite Z.shiftl_1_l. rewrite (Z.mod_small (2 ^ s + -1)) by lia. rewrite Z.shiftr_div_pow2 by lia.
  replace (Z.land (2 ^ s + -1) (Wm + dW + dP + 1)) with ((Wm + dW + dP + 1) mod 2 ^ s)%Z
    by (rewrite Z.land_comm; replace (2 ^ s + -1)%Z with (Z.ones s) by (rewrite Z.ones_equiv; lia); rewrite Z.land_ones by lia; reflexivity).
  replace (Z_to_bv 64 (bv_unsigned sp + -80)) with (Z_to_bv 64 (SP0 - 80)) by (unfold DgWalkA.SP0; f_equal; lia).
  replace (2 ^ s + -1)%Z with (2 ^ s - 1)%Z by lia.
  set (Wp1 := (Wm + dW + dP + 1)%Z).
  eassert (HM : dg_mem m1 _ 0 Ks bs).
  { unfold DgWalkA.dg_mem, DgWalkA.DG_W, DgWalkA.SP0. replace (bv_unsigned sp - 80)%Z with (bv_unsigned sp + -80)%Z by lia.
    split; [exact ST|]. split; [exact FR|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact BU|].
    split; [exact BL|]. split; [exact LE | exact KC]. }
  pose proof (Z.div_mod Wp1 (2 ^ s) ltac:(lia)) as DM. pose proof (Z.mod_pos_bound Wp1 (2 ^ s) ltac:(lia)) as MB.
  assert (P1lo : (8 <= Wp1 / 2 ^ s)%Z).
  { apply Z.div_le_lower_bound; [lia|]. assert (8 * 2 ^ s <= 8 * 2 ^ 59)%Z by lia. lia. }
  assert (P1hi : (Wp1 / 2 ^ s < 256)%Z) by (apply Z.div_lt_upper_bound; lia).
  eapply (dg_l1_k3 (Wp1 / 2 ^ s) 0 (Wp1 mod 2 ^ s) (Wm + dW + dP - Wm + 2) s Wp1 Ks); [exact HM | lia | lia | lia | lia | lia | lia | | lia].
  intros _. split; [lia | split; lia].
Qed.

End DGB.
