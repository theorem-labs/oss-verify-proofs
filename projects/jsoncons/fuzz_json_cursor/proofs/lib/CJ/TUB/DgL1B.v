(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib Require Import Tac ZBridge.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.TUB Require Import DgWalkB DgWalkB2.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section DGB3.
Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word.
Variable F : bvmap 5 word.
Variable fc : bv 32.
Variable m0 : word -> option byte.
Variables buf lenp kp : Z.

Local Notation SP0 := (DgWalkB.SP0 sp).
Hypothesis BUFR : (4096 <= buf /\ buf + 21 <= 2^47)%Z.
Hypothesis SPR0 : (2^40 <= SP0 /\ SP0 + 8 <= 2^47)%Z.
Hypothesis KL : lenp = (kp + 4)%Z.
Hypothesis KS : (SP0 + 8 <= kp /\ kp + 8 <= 2^47)%Z.
Hypothesis KA : (kp mod 4 = 0)%Z.
Hypothesis SEP_B : (buf + 21 <= SP0 - 96 \/ lenp + 4 <= buf)%Z.
Local Notation app_buf := (DgWalkB.app_buf buf).
Hypothesis APP_B : app_buf.
Hypothesis APP_S : (0x10007fff8000 <= SP0 - 96)%Z.
Hypothesis SHL : mrd rsegs m0 (wa (Z.shiftr lenp 3 + 2147450880)) = Some (Z_to_bv 8 0).
Hypothesis SHK : mrd rsegs m0 (wa (Z.shiftr kp 3 + 2147450880)) = Some (Z_to_bv 8 0).
Hypothesis SHBUF : forall k, (0 <= k < 21)%Z -> mrd rsegs m0 (wa (Z.shiftr (buf + k) 3 + 2147450880)) = Some (Z_to_bv 8 0).

Local Notation DG_W := (DgWalkB.DG_W sp buf lenp kp).
Local Notation dg_post := (DgWalkB.dg_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 buf lenp kp).
Local Notation dg_mem := (DgWalkB.dg_mem ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 m0 buf lenp kp).
Local Notation L x := (x ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 buf lenp kp BUFR SPR0 KL KS KA SEP_B APP_B APP_S SHL SHK SHBUF).
Local Notation sh_read := (L DgWalkB.sh_read).
Local Notation dg_weed1 := (L DgWalkB.dg_weed1).
Local Notation dg_rw1_loop := (L DgWalkB.dg_rw1_loop).
Local Notation dg_l2exit := (L DgWalkB.dg_l2exit).
Local Notation dg_loop2 := (L DgWalkB2.dg_loop2).
Local Notation dg_rw1_entry := (L DgWalkB2.dg_rw1_entry).
Ltac dg_mem_intro H := destruct H as (ST & FR & MU & WM & MI & BU & BL & LE & KC); unfold DgWalkB.DG_W in MU.

Lemma dg_l1_k1 : forall (p1 len p2 D s Wp1 Ks : Z) t2' t4' a1' a2' s4' s6' s7' s8' s9' (m : word -> option byte) j8 (bs : list byte),
  dg_mem m j8 len Ks bs -> (0 <= len <= 2)%Z -> (- 2 ^ 31 + 18 <= Ks <= 2 ^ 31 - 3)%Z ->
  (56 <= s <= 59)%Z -> (0 <= p1 < 10)%Z -> (0 <= p2 < 2 ^ s)%Z -> (2 <= D < 2 ^ 64)%Z ->
  (len = 0 -> p1 * 2 ^ s + p2 = Wp1 /\ D <= Wp1 /\ 8 <= p1)%Z ->
  evt rsegs (dg_post Ks) (MS (mkR ra (Z_to_bv 64 (SP0 - 96)) gp tp (Z_to_bv 64 1) (Z_to_bv 64 (Z.shiftr lenp 3 + 2147450880)) t2' (Z_to_bv 64 1) (Z_to_bv 64 2)
                                  (Z_to_bv 64 kp) a1' a2' (Z_to_bv 64 D) (Z_to_bv 64 (2 ^ s)) (Z_to_bv 64 2147450880) (Z_to_bv 64 buf) (Z_to_bv 64 lenp)
                                  (Z_to_bv 64 1) (Z_to_bv 64 p1) s4' (Z_to_bv 64 (0xcccccccd * 2 ^ 32)) s6' s7' s8' s9' s10 s11
                                  (Z_to_bv 64 s) t4' (Z_to_bv 64 p2) (Z_to_bv 64 (2 ^ s - 1)))
                              F (Z_to_bv 64 0xd16f4) fc None m (seg_rom rsegs)).
Proof using All.
  intros until bs. intros HM LR KsR Hs Hp1 Hp2 HD Hinv.
  pose proof HM as HM0. dg_mem_intro HM.
  assert (H2s : (2 ^ 56 <= 2 ^ s <= 2 ^ 59)%Z) by (split; apply Z.pow_le_mono_r; lia).
  pose proof (sh_read m lenp (Z.shiftr lenp 3 + 2147450880) MU ltac:(lia) eq_refl SHL) as SHl.
  assert (BODY : (1 <= p1 \/ 1 <= len)%Z -> forall a1x, evt rsegs (dg_post Ks)
     (MS (mkR ra (Z_to_bv 64 (SP0 - 96)) gp tp (Z_to_bv 64 1) (Z_to_bv 64 (Z.shiftr lenp 3 + 2147450880)) t2' (Z_to_bv 64 1) (Z_to_bv 64 2)
              (Z_to_bv 64 kp) a1x a2' (Z_to_bv 64 D) (Z_to_bv 64 (2 ^ s)) (Z_to_bv 64 2147450880) (Z_to_bv 64 buf) (Z_to_bv 64 lenp)
              (Z_to_bv 64 1) (Z_to_bv 64 p1) (Z_to_bv 64 p1) (Z_to_bv 64 14757395259826634752) s6' s7' s8' s9' s10 s11
              (Z_to_bv 64 s) t4' (Z_to_bv 64 p2) (Z_to_bv 64 (2 ^ s - 1)))
         F (Z_to_bv 64 0xd1710) fc None m (seg_rom rsegs))).
  { intros Hem a1x.
    zstep. zstep. if_cases Kd; [zify_cond Kd; rewrite (swrap32_small (p1 + 48)) in Kd by lia; rewrite !sgn_small in Kd by lia; lia | ].
    rewrite (swrap32_small (p1 + 48)) by lia.
    zstep; zstep; if_cases K0b; [cbv in K0b; discriminate | ].
    zstep; rewrite sx32_small by lia.
    zstep. zstep. if_cases Kl; [zify_cond Kl; rewrite (swrap32_small (len + 1)) in Kl by lia; rewrite !sgn_small in Kl by lia; lia | ].
    rewrite (swrap32_small (len + 1)) by lia.
    zstep; zstep; if_cases K0c; [cbv in K0c; discriminate | ].
    clear SHl.
    zstep. zstep. zstep.
    zstep. if_cases Kn; [zify_cond Kn; ub_norm_in Kn; lia | ].
    do 4 zstep. zstep. if_cases Kp; [zify_cond Kp; ub_norm_in Kp; cbv in Kp; discriminate | ].
    zstep. if_cases Kb; [zify_cond Kb; lia | ].
    pose proof (sh_read m1 (buf + len) (Z.shiftr (buf + len) 3 + 2147450880) ltac:(unfold DgWalkB.DG_W; exact MU) ltac:(lia) eq_refl (SHBUF len ltac:(lia))) as SHb.
    do 3 zstep. zstep. if_cases K0d; [cbv in K0d; discriminate | ].
    clear SHb.
    pose proof (u8arr_store_ok rsegs m1 buf bs len (Z_to_bv 64 (buf + len)) BU ltac:(lia) ltac:(unfold wa; f_equal; lia)) as SOK.
    zstep.
    replace (write_to_mem m1 (Z_to_bv 64 (buf + len)) (le1 (Z_to_bv 64 (p1 + 48)))) with (write_to_mem m1 (wa (buf + len)) [Z_to_bv 8 (p1 + 48)])
      by (f_equal; symmetry; apply le1_lit).
    pose proof (u8arr_write rsegs m1 buf bs len (Z_to_bv 8 (p1 + 48)) BU ltac:(lia)) as BU'.
    clear BU; store_done.
    assert (HM2 : dg_mem m2 j8 (len + 1) Ks (upd bs (Z.to_nat len) (Z_to_bv 8 (p1 + 48))))
      by (unfold DgWalkB.dg_mem; split; [exact ST|]; split; [exact FR|]; split; [exact MU|]; split; [exact WM|]; split; [exact MI|]; split; [exact BU'|];
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

Lemma dg_l1_k2 : forall (p1 len p2 D s Wp1 Ks : Z) t2' t4' a1' a2' s4' s6' s7' s8' s9' (m : word -> option byte) j8 (bs : list byte),
  dg_mem m j8 len Ks bs -> (0 <= len <= 1)%Z -> (- 2 ^ 31 + 18 <= Ks <= 2 ^ 31 - 3)%Z ->
  (56 <= s <= 59)%Z -> (0 <= p1 < 100)%Z -> (0 <= p2 < 2 ^ s)%Z -> (2 <= D < 2 ^ 64)%Z ->
  (len = 0 -> p1 * 2 ^ s + p2 = Wp1 /\ D <= Wp1 /\ 8 <= p1)%Z ->
  evt rsegs (dg_post Ks) (MS (mkR ra (Z_to_bv 64 (SP0 - 96)) gp tp (Z_to_bv 64 1) (Z_to_bv 64 (Z.shiftr lenp 3 + 2147450880)) t2' (Z_to_bv 64 10) (Z_to_bv 64 3)
                                  (Z_to_bv 64 kp) a1' a2' (Z_to_bv 64 D) (Z_to_bv 64 (2 ^ s)) (Z_to_bv 64 2147450880) (Z_to_bv 64 buf) (Z_to_bv 64 lenp)
                                  (Z_to_bv 64 1) (Z_to_bv 64 p1) s4' (Z_to_bv 64 (0xcccccccd * 2 ^ 32)) s6' s7' s8' s9' s10 s11
                                  (Z_to_bv 64 s) t4' (Z_to_bv 64 p2) (Z_to_bv 64 (2 ^ s - 1)))
                              F (Z_to_bv 64 0xd16f4) fc None m (seg_rom rsegs)).
Proof using All.
  intros until bs. intros HM LR KsR Hs Hp1 Hp2 HD Hinv.
  pose proof HM as HM0. dg_mem_intro HM.
  assert (H2s : (2 ^ 56 <= 2 ^ s <= 2 ^ 59)%Z) by (split; apply Z.pow_le_mono_r; lia).
  pose proof (Z.mod_pos_bound p1 10 ltac:(lia)) as Hpm.
  assert (Hprod : (0 <= p1 mod 10 * 2 ^ s <= 9 * 2 ^ s)%Z) by (split; [apply Z.mul_nonneg_nonneg; lia | apply Z.mul_le_mono_nonneg_r; lia]).
  pose proof (sh_read m lenp (Z.shiftr lenp 3 + 2147450880) MU ltac:(lia) eq_refl SHL) as SHl.
  assert (BODY : forall a1x, evt rsegs (dg_post Ks)
     (MS (mkR ra (Z_to_bv 64 (SP0 - 96)) gp tp (Z_to_bv 64 1) (Z_to_bv 64 (Z.shiftr lenp 3 + 2147450880)) t2' (Z_to_bv 64 10) (Z_to_bv 64 3)
              (Z_to_bv 64 kp) a1x a2' (Z_to_bv 64 D) (Z_to_bv 64 (2 ^ s)) (Z_to_bv 64 2147450880) (Z_to_bv 64 buf) (Z_to_bv 64 lenp)
              (Z_to_bv 64 1) (Z_to_bv 64 p1) (Z_to_bv 64 (p1 / 10)) (Z_to_bv 64 14757395259826634752) s6' s7' s8' s9' s10 s11
              (Z_to_bv 64 s) t4' (Z_to_bv 64 p2) (Z_to_bv 64 (2 ^ s - 1)))
         F (Z_to_bv 64 0xd1710) fc None m (seg_rom rsegs))).
  { intros a1x.
    zstep. zstep. if_cases Kd; [zify_cond Kd; rewrite (swrap32_small (p1 / 10 + 48)) in Kd by lia; rewrite !sgn_small in Kd by lia; lia | ].
    rewrite (swrap32_small (p1 / 10 + 48)) by lia.
    zstep; zstep; if_cases K0b; [cbv in K0b; discriminate | ].
    zstep; rewrite sx32_small by lia.
    zstep. zstep. if_cases Kl; [zify_cond Kl; rewrite (swrap32_small (len + 1)) in Kl by lia; rewrite !sgn_small in Kl by lia; lia | ].
    rewrite (swrap32_small (len + 1)) by lia.
    zstep; zstep; if_cases K0c; [cbv in K0c; discriminate | ].
    clear SHl.
    zstep. zstep. zstep.
    zstep. if_cases Kn; [zify_cond Kn; ub_norm_in Kn; lia | ].
    do 4 zstep. zstep. if_cases Kp; [zify_cond Kp; ub_norm_in Kp; cbv in Kp; discriminate | ].
    zstep. if_cases Kb; [zify_cond Kb; lia | ].
    pose proof (sh_read m1 (buf + len) (Z.shiftr (buf + len) 3 + 2147450880) ltac:(unfold DgWalkB.DG_W; exact MU) ltac:(lia) eq_refl (SHBUF len ltac:(lia))) as SHb.
    do 3 zstep. zstep. if_cases K0d; [cbv in K0d; discriminate | ].
    clear SHb.
    pose proof (u8arr_store_ok rsegs m1 buf bs len (Z_to_bv 64 (buf + len)) BU ltac:(lia) ltac:(unfold wa; f_equal; lia)) as SOK.
    zstep.
    replace (write_to_mem m1 (Z_to_bv 64 (buf + len)) (le1 (Z_to_bv 64 (p1 / 10 + 48)))) with (write_to_mem m1 (wa (buf + len)) [Z_to_bv 8 (p1 / 10 + 48)])
      by (f_equal; symmetry; apply le1_lit).
    pose proof (u8arr_write rsegs m1 buf bs len (Z_to_bv 8 (p1 / 10 + 48)) BU ltac:(lia)) as BU'.
    clear BU; store_done.
    assert (HM2 : dg_mem m2 j8 (len + 1) Ks (upd bs (Z.to_nat len) (Z_to_bv 8 (p1 / 10 + 48))))
      by (unfold DgWalkB.dg_mem; split; [exact ST|]; split; [exact FR|]; split; [exact MU|]; split; [exact WM|]; split; [exact MI|]; split; [exact BU'|];
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

End DGB3.
