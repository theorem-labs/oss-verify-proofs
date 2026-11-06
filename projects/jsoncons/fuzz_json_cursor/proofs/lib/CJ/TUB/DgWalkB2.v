(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib Require Import Tac ZBridge.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.TUB Require Import DgWalkB.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section DGB2.
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
Ltac dg_mem_intro H := destruct H as (ST & FR & MU & WM & MI & BU & BL & LE & KC); unfold DgWalkB.DG_W in MU.

Lemma dg_loop2 : forall (n : nat) (i p2 D s len Ks : Z) t2' t4' s0' a2' s3' s4' s5' s6' s7' s8' s9' (m : word -> option byte) j8 (bs : list byte),
  Z.to_nat (17 - i) = n ->
  dg_mem m j8 len Ks bs -> (1 <= len <= 3 + i)%Z -> (0 <= i <= 17)%Z -> (- 2 ^ 31 + 18 <= Ks <= 2 ^ 31 - 3)%Z ->
  (56 <= s <= 59)%Z -> (D <= p2 < 2 ^ s)%Z -> (2 * 10 ^ i <= D)%Z ->
  evt rsegs (dg_post Ks) (MS (mkR ra (Z_to_bv 64 (SP0 - 96)) gp tp (Z_to_bv 64 1) (Z_to_bv 64 (Z.shiftr lenp 3 + 2147450880)) t2' s0' (Z_to_bv 64 10)
                                  (Z_to_bv 64 kp) (Z_to_bv 64 (10 ^ i)) a2' (Z_to_bv 64 D) (Z_to_bv 64 (2 ^ s)) (Z_to_bv 64 2147450880) (Z_to_bv 64 buf) (Z_to_bv 64 lenp)
                                  (Z_to_bv 64 (- i)) s3' s4' s5' s6' s7' s8' s9' s10 s11 (Z_to_bv 64 s) t4' (Z_to_bv 64 p2) (Z_to_bv 64 (2 ^ s - 1)))
                              F (Z_to_bv 64 0xd18b4) fc None m (seg_rom rsegs)).
Proof using All.
  induction n as [n IH] using lt_wf_ind.
  intros i p2 D s len Ks t2' t4' s0' a2' s3' s4' s5' s6' s7' s8' s9' m j8 bs Hn HM LR IR KsR Hs HP HD.
  pose proof HM as HM0. dg_mem_intro HM.
  assert (H2s : (2 ^ 56 <= 2 ^ s <= 2 ^ 59)%Z) by (split; apply Z.pow_le_mono_r; lia).
  assert (H10 : (1 <= 10 ^ i < 2 ^ 58)%Z) by (pose proof (Z.pow_pos_nonneg 10 i ltac:(lia) ltac:(lia)); lia).
  pose proof (sh_read m lenp (Z.shiftr lenp 3 + 2147450880) MU ltac:(lia) eq_refl SHL) as SHl.
  set (dd := ((p2 * 10) ≫ (s mod 64))%Z).
  assert (Hdd : (0 <= dd < 10)%Z).
  { unfold dd. rewrite (Z.mod_small s 64) by lia. rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }

  assert (BODY : forall a1x, evt rsegs (dg_post Ks)
     (MS (mkR ra (Z_to_bv 64 (SP0 - 96)) gp tp (Z_to_bv 64 1) (Z_to_bv 64 (Z.shiftr lenp 3 + 2147450880)) t2' (Z_to_bv 64 D) (Z_to_bv 64 10)
              (Z_to_bv 64 kp) a1x a2' (Z_to_bv 64 D) (Z_to_bv 64 (2 ^ s)) (Z_to_bv 64 2147450880) (Z_to_bv 64 buf) (Z_to_bv 64 lenp)
              (Z_to_bv 64 (- i)) (Z_to_bv 64 dd) (Z_to_bv 64 dd) s5' s6' s7' s8' s9' s10 s11
              (Z_to_bv 64 s) (Z_to_bv 64 (10 ^ i)) (Z_to_bv 64 (p2 * 10)) (Z_to_bv 64 (2 ^ s - 1)))
         F (Z_to_bv 64 0xd18dc) fc None m (seg_rom rsegs))).
  { intros a1x.
    zstep. zstep. if_cases Kd; [zify_cond Kd; rewrite (swrap32_small (dd + 48)) in Kd by lia; rewrite !sgn_small in Kd by lia; lia | ].
    rewrite (swrap32_small (dd + 48)) by lia.
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
    set (dch := (dd + 48)%Z).
    replace (write_to_mem m1 (Z_to_bv 64 (buf + len)) (le1 (Z_to_bv 64 dch))) with (write_to_mem m1 (wa (buf + len)) [Z_to_bv 8 dch])
      by (f_equal; symmetry; apply le1_lit).
    pose proof (u8arr_write rsegs m1 buf bs len (Z_to_bv 8 dch) BU ltac:(lia)) as BU'.
    clear BU; store_done.
    assert (HM2 : dg_mem m2 j8 (len + 1) Ks (upd bs (Z.to_nat len) (Z_to_bv 8 dch)))
      by (unfold DgWalkB.dg_mem; split; [exact ST|]; split; [exact FR|]; split; [exact MU|]; split; [exact WM|]; split; [exact MI|]; split; [exact BU'|];
          split; [rewrite upd_length; exact BL|]; split; [exact LE | exact KC]).
    zstep. zstep. if_cases Kk; [zify_cond Kk; rewrite (swrap32_modl (- i) (-1)) in Kk by lia; rewrite !sgn_small in Kk by lia; lia | ].
    rewrite (swrap32_modl (- i) (-1)) by lia.
    do 5 zstep.
    assert (HLm : (Z.land (p2 * 10) (2 ^ s - 1) < 2 ^ s)%Z)
      by (replace (2 ^ s - 1)%Z with (Z.ones s) by (rewrite Z.ones_equiv; lia); rewrite Z.land_ones by lia; apply Z.mod_pos_bound; lia).
    assert (HL0 : (0 <= Z.land (p2 * 10) (2 ^ s - 1))%Z) by (apply Z.land_nonneg; lia).
    if_cases K3; zify_cond K3.
    -
      assert (Hi1 : (i + 1 <= 17)%Z).
      { destruct (Z_le_gt_dec (i + 1) 17) as [?|Hg]; [lia|]. assert (H18 : (10 ^ 18 <= 10 ^ (i + 1))%Z) by (apply Z.pow_le_mono_r; lia).
        rewrite Z.pow_add_r in * by lia. lia. }
      replace (Z_to_bv 64 (10 ^ i * 10)) with (Z_to_bv 64 (10 ^ (i + 1))) by (f_equal; rewrite Z.pow_add_r by lia; lia).
      replace (Z_to_bv 64 (- i + -1)) with (Z_to_bv 64 (- (i + 1))) by (f_equal; lia).
      eapply (IH (Z.to_nat (17 - (i + 1)))); [lia | reflexivity | exact HM2 | lia | lia | lia | lia | lia | rewrite Z.pow_add_r by lia; lia].
    -
      zstep.
      replace (Z_to_bv 64 (D * 10)) with (Z_to_bv 64 (10 * D)) by (f_equal; lia).
      eapply dg_l2exit; [exact HM2 | lia | lia | lia | lia | lia | lia]. }
  do 6 zstep.
  replace (bv_swrap 32 ((p2 * 10) ≫ (s mod 64) + 0)) with dd by (unfold dd in *; rewrite Z.add_0_r; symmetry; apply swrap32_small; lia).
  fold dd.
  if_cases K1.
  - apply BODY.
  - zstep; zstep; if_cases K0a; [cbv in K0a; discriminate | ]; zstep; rewrite sx32_small by lia; zstep; if_cases K2; zify_cond K2; [lia | ].
    apply BODY.
Qed.

Lemma dg_rw1_entry : forall (D r dv cnt s len Ks : Z) t2' t4' t5' t6' a1' a2' a4' s2' s3' s5' s6' s7' s8' s9' (m : word -> option byte) j8 (bs : list byte),
  dg_mem m j8 len Ks bs -> (1 <= len <= 3)%Z -> (2 <= cnt <= 4)%Z -> (- 2 ^ 31 + 18 <= Ks <= 2 ^ 31 - 3)%Z ->
  (dv = 1 \/ dv = 10 \/ dv = 100)%Z -> (56 <= s <= 59)%Z -> (0 <= r < D)%Z -> (D < 2 ^ 64)%Z ->
  evt rsegs (dg_post Ks) (MS (mkR ra (Z_to_bv 64 (SP0 - 96)) gp tp (Z_to_bv 64 1) (Z_to_bv 64 (Z.shiftr lenp 3 + 2147450880)) t2' (Z_to_bv 64 dv) (Z_to_bv 64 cnt)
                                  (Z_to_bv 64 kp) a1' a2' (Z_to_bv 64 D) a4' (Z_to_bv 64 2147450880) (Z_to_bv 64 buf) (Z_to_bv 64 lenp)
                                  s2' s3' (Z_to_bv 64 r) s5' s6' s7' s8' s9' s10 s11 (Z_to_bv 64 s) t4' t5' t6')
                              F (Z_to_bv 64 0xd17c4) fc None m (seg_rom rsegs)).
Proof using All.
  intros until bs. intros HM LR KR KsR Hdv Hs Hr HD.
  pose proof HM as HM0. dg_mem_intro HM.
  pose proof (sh_read m kp (Z.shiftr kp 3 + 2147450880) MU ltac:(lia) eq_refl SHK) as SHk.
  zstep. if_cases Kz; [zify_cond Kz; lia | ].
  zstep. zstep. if_cases Ka; [zify_cond Ka; rewrite (land3_0 kp KA) in Ka; lia | ].
  do 4 zstep. if_cases K0; [cbv in K0; discriminate | ].
  zstep. rewrite sx32_small by lia.
  zstep. rewrite (swrap32_small (cnt + -2)) by lia.
  zstep. zstep. zstep. if_cases Kov; [zify_cond Kov; rewrite (swrap32_modl Ks (cnt + -2)) in Kov by lia; exfalso; exact (Kov eq_refl) | ].
  zstep. zstep. if_cases K0b; [cbv in K0b; discriminate | ].
  clear SHk.
  zstep.
  assert (KC' : rw_cells rsegs m1 kp [C4 (Z_to_bv 64 (Ks + (cnt - 2)))]) by (replace (Ks + (cnt - 2))%Z with (Ks + (cnt + -2))%Z by lia; exact KC).
  assert (HM1 : dg_mem m1 j8 len (Ks + (cnt - 2)) bs).
  { unfold DgWalkB.dg_mem. split; [exact ST|]. split; [exact FR|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact BU|].
    split; [exact BL|]. split; [exact LE | exact KC']. }
  zstep.
  set (tk := ((dv ≪ (s mod 64)) mod 2 ^ 64)%Z).
  assert (Htk : (1 <= tk < 2 ^ 64)%Z).
  { assert (Hc : (s = 56 \/ s = 57 \/ s = 58 \/ s = 59)%Z) by lia. unfold tk.
    destruct Hdv as [-> | [-> | ->]]; destruct Hc as [-> | [-> | [-> | ->]]]; vm_compute; split; congruence. }
  replace (Z_to_bv 64 (dv ≪ (s mod 64))) with (Z_to_bv 64 tk) by (unfold tk; apply Z_to_bv_mod64).
  do 3 zstep. if_cases K1.
  - zstep. eapply dg_weed1; [exact HM1 | lia | lia].
  - zstep. if_cases K2; zify_cond K2.
    + zstep. eapply dg_weed1; [exact HM1 | lia | lia].
    + pose proof (sh_read m1 lenp (Z.shiftr lenp 3 + 2147450880) ltac:(unfold DgWalkB.DG_W; exact MU) ltac:(lia) eq_refl SHL) as SHl.
      zstep. zstep. if_cases K5; [cbv in K5; discriminate | ].
      clear SHl.
      zstep. rewrite sx32_small by lia. do 14 zstep.
      rewrite (swrap32_small (len + -1)) by lia.
      ub_norm.
      replace (len + -1 + buf)%Z with (buf + len + -1)%Z by lia.
      eapply (dg_rw1_loop (Z.to_nat (D - r)) D r tk len); [reflexivity | exact HM1 | lia | lia | lia | lia | | lia].
      revert K2; unfold tk; rewrite ?Z.mod_small by lia; intros K2; lia.
Qed.

End DGB2.
