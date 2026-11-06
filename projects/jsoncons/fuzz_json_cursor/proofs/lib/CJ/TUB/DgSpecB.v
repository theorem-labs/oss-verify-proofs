(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib Require Import Tac ZBridge.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.TUB Require Import DgWalkB DgWalkB2 DgL1B.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section DGB4.
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
Local Notation dg_l1_k2 := (L DgL1B.dg_l1_k2).
Ltac dg_mem_intro H := destruct H as (ST & FR & MU & WM & MI & BU & BL & LE & KC); unfold DgWalkB.DG_W in MU.

Lemma dg_l1_k3 : forall (p1 len p2 D s Wp1 Ks : Z) t2' t4' a1' a2' s4' s6' s7' s8' s9' (m : word -> option byte) j8 (bs : list byte),
  dg_mem m j8 len Ks bs -> (0 <= len <= 0)%Z -> (- 2 ^ 31 + 18 <= Ks <= 2 ^ 31 - 3)%Z ->
  (56 <= s <= 59)%Z -> (0 <= p1 < 256)%Z -> (0 <= p2 < 2 ^ s)%Z -> (2 <= D < 2 ^ 64)%Z ->
  (len = 0 -> p1 * 2 ^ s + p2 = Wp1 /\ D <= Wp1 /\ 8 <= p1)%Z -> (p1 * 2 ^ s + p2 < 2 ^ 64)%Z ->
  evt rsegs (dg_post Ks) (MS (mkR ra (Z_to_bv 64 (SP0 - 96)) gp tp (Z_to_bv 64 1) (Z_to_bv 64 (Z.shiftr lenp 3 + 2147450880)) t2' (Z_to_bv 64 100) (Z_to_bv 64 4)
                                  (Z_to_bv 64 kp) a1' a2' (Z_to_bv 64 D) (Z_to_bv 64 (2 ^ s)) (Z_to_bv 64 2147450880) (Z_to_bv 64 buf) (Z_to_bv 64 lenp)
                                  (Z_to_bv 64 1) (Z_to_bv 64 p1) s4' (Z_to_bv 64 (0xcccccccd * 2 ^ 32)) s6' s7' s8' s9' s10 s11
                                  (Z_to_bv 64 s) t4' (Z_to_bv 64 p2) (Z_to_bv 64 (2 ^ s - 1)))
                              F (Z_to_bv 64 0xd16f4) fc None m (seg_rom rsegs)).
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

  zstep. zstep. if_cases Kd; [zify_cond Kd; rewrite (swrap32_small (p1 / 100 + 48)) in Kd by lia; rewrite !sgn_small in Kd by lia; lia | ].
  rewrite (swrap32_small (p1 / 100 + 48)) by lia.
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
  replace (write_to_mem m1 (Z_to_bv 64 (buf + len)) (le1 (Z_to_bv 64 (p1 / 100 + 48)))) with (write_to_mem m1 (wa (buf + len)) [Z_to_bv 8 (p1 / 100 + 48)])
    by (f_equal; symmetry; apply le1_lit).
  pose proof (u8arr_write rsegs m1 buf bs len (Z_to_bv 8 (p1 / 100 + 48)) BU ltac:(lia)) as BU'.
  clear BU; store_done.
  assert (HM2 : dg_mem m2 j8 (len + 1) Ks (upd bs (Z.to_nat len) (Z_to_bv 8 (p1 / 100 + 48))))
    by (unfold DgWalkB.dg_mem; split; [exact ST|]; split; [exact FR|]; split; [exact MU|]; split; [exact WM|]; split; [exact MI|]; split; [exact BU'|];
        split; [rewrite upd_length; exact BL|]; split; [exact LE | exact KC]).
  do 4 zstep.
  rewrite subw_mod, shl_s by lia.
  zstep; if_cases K3; zify_cond K3.
  - eapply (dg_rw1_entry D (p1 mod 100 * 2 ^ s + p2) 100 4 s (len + 1) Ks); [exact HM2 | lia | lia | lia | right; right; reflexivity | lia | lia | lia].
  - do 5 zstep.
    if_cases K4; zify_cond K4; [ | lia].
    eapply (dg_l1_k2 (p1 mod 100) (len + 1) p2 D s Wp1 Ks); [exact HM2 | lia | lia | lia | lia | lia | lia | lia].
Qed.

Lemma swrap32_neg : forall s, (0 < s <= 2 ^ 31)%Z -> bv_swrap 32 (4294967296 - s + 0) = (- s)%Z.
Proof.
  intros s H. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. cbn -[Z.pow]. change (2 ^ 32 / 2)%Z with (2 ^ 31)%Z.
  replace (4294967296 - s + 0 + 2 ^ 31)%Z with ((2 ^ 31 - s) + 1 * 2 ^ 32)%Z by lia. rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
Qed.
Lemma negmod64 : forall s, (0 < s < 2 ^ 64)%Z -> ((- s) mod 18446744073709551616 = 18446744073709551616 - s)%Z.
Proof. intros s H. rewrite <- (Z.mod_add (- s) 1) by lia. rewrite Z.mod_small by lia. lia. Qed.
Lemma swrap32_sub64 : forall s, (- 2 ^ 31 <= s < 2 ^ 31)%Z -> bv_swrap 32 (s - 18446744073709551616) = s.
Proof.
  intros s H. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. cbn -[Z.pow]. change (2 ^ 32 / 2)%Z with (2 ^ 31)%Z.
  replace (s - 18446744073709551616 + 2 ^ 31)%Z with ((s + 2 ^ 31) + (- 4294967296) * 2 ^ 32)%Z by lia. rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
Qed.

Lemma zbv_sub64 : forall x, Z_to_bv 64 (x - 18446744073709551616) = Z_to_bv 64 x.
Proof.
  intros x. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64)%Z with 18446744073709551616%Z.
  replace (x - 18446744073709551616)%Z with (x + (-1) * 18446744073709551616)%Z by lia. apply Z.mod_add. lia.
Qed.

Lemma dg_spec : forall t0 t1 t2 t3 t4 t5 t6 (m : word -> option byte) (Wm dW dP s Ks : Z) (bs : list byte) lj,
  (56 <= s <= 59)%Z -> (1 <= Wm)%Z -> (0 <= dW)%Z -> (0 <= dP)%Z -> (Wm + dW + dP <= 2 ^ 64 - 2)%Z -> (2 ^ 62 <= Wm + dW + dP + 1)%Z ->
  (- 2 ^ 31 + 18 <= Ks <= 2 ^ 31 - 3)%Z ->
  stk rsegs m (SP0 - 96) SP0 -> rw_cells rsegs m SP0 [C8 (Z_to_bv 64 kp)] ->
  u8arr rsegs m buf bs -> length bs = 21%nat -> rw_cells rsegs m lenp [C4 lj] -> rw_cells rsegs m kp [C4 (Z_to_bv 64 Ks)] ->
  ro_cells rsegs m 0x154500 [C8 (Z_to_bv 64 0x15dcf8)] -> ro_cells rsegs m 0x15dcf8 [C8 (Z_to_bv 64 2147450880)] ->
  mem_inv rsegs m -> m = m0 ->
  evt rsegs (dg_post Ks) (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Wm) (Z_to_bv 64 (2 ^ 32 - s)) (Z_to_bv 64 (Wm + dW)) (Z_to_bv 64 (2 ^ 32 - s))
                                  (Z_to_bv 64 (Wm + dW + dP)) (Z_to_bv 64 (2 ^ 32 - s)) (Z_to_bv 64 buf) (Z_to_bv 64 lenp)
                                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                              F (Z_to_bv 64 0xd1614) fc None m (seg_rom rsegs)).
Proof using All.
  intros until lj. intros Hs HWm HdW HdP Hsum HWp HKs ST KPc BU BL LE KC GOT SHV MI ->.
  pose proof (munch_refl DG_W m0) as MU. pose proof (wmono_refl rsegs m0) as WM.
  pose proof (munch_refl [((SP0 - 96)%Z, SP0)] m0) as MUf. pose proof (wmono_refl rsegs m0) as WMf.
  assert (H2s : (2 ^ 56 <= 2 ^ s <= 2 ^ 59)%Z) by (split; apply Z.pow_le_mono_r; lia).

  assert (BOX : rw_cells rsegs m0 SP0 [C8 (Z_to_bv 64 kp)] /\ u8arr rsegs m0 buf bs /\ rw_cells rsegs m0 lenp [C4 lj] /\ rw_cells rsegs m0 kp [C4 (Z_to_bv 64 Ks)] /\
                ro_cells rsegs m0 0x154500 [C8 (Z_to_bv 64 0x15dcf8)] /\ ro_cells rsegs m0 0x15dcf8 [C8 (Z_to_bv 64 2147450880)])
    by exact (conj KPc (conj BU (conj LE (conj KC (conj GOT SHV))))).
  clear KPc BU LE KC GOT SHV.
  unfold DgWalkB.DG_W in MU. unfold DgWalkB.SP0 in *.
  carve_frame 96%nat ST.
  do 12 zstep.
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
  rewrite (swrap32_neg s) by lia.
  zstep. zstep. rewrite ?(negmod64 s) by lia.
  replace (0 - (18446744073709551616 - s))%Z with (s - 18446744073709551616)%Z by lia.
  rewrite ?(swrap32_sub64 s) by lia.
  zstep. if_cases Kng; [zify_cond Kng; rewrite <- (Z.mod_add (s - 18446744073709551616) 1) in Kng by lia; rewrite Z.mod_small in Kng by lia; lia | ].
  rewrite zbv_sub64.
  zstep. rewrite (swrap32_small (s + 0)) by lia. rewrite Z.add_0_r.
  zstep. zstep. if_cases Ksh; [zify_cond Ksh; lia | ].
  zstep. if_cases Klz; [zify_cond Klz; lia | ].
  zstep. zstep. if_cases Kla; [zify_cond Kla; rewrite (land3_0 lenp ltac:(rewrite KL; rewrite <- Zplus_mod_idemp_l, KA; reflexivity)) in Kla; lia | ].
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (sh_read mm lenp (Z.shiftr lenp 3 + 2147450880) ltac:(unfold DgWalkB.DG_W, DgWalkB.SP0; exact MU) ltac:(lia) eq_refl SHL) as SHl end.
  do 8 zstep. if_cases K3; [cbv in K3; discriminate | ].
  clear SHl.
  do 19 zstep.
  replace (0 <? buf)%Z with true by (symmetry; apply Z.ltb_lt; lia). cbn [Z.b2z].
  rewrite (Z.mod_small s 64) by lia.
  rewrite Z.shiftl_1_l. rewrite (Z.mod_small (2 ^ s + -1)) by lia. rewrite Z.shiftr_div_pow2 by lia.
  replace (Z.land (2 ^ s + -1) (Wm + dW + dP + 1)) with ((Wm + dW + dP + 1) mod 2 ^ s)%Z
    by (rewrite Z.land_comm; replace (2 ^ s + -1)%Z with (Z.ones s) by (rewrite Z.ones_equiv; lia); rewrite Z.land_ones by lia; reflexivity).
  replace (Z_to_bv 64 (bv_unsigned sp + -96)) with (Z_to_bv 64 (SP0 - 96)) by (unfold DgWalkB.SP0; f_equal; lia).
  replace (2 ^ s + -1)%Z with (2 ^ s - 1)%Z by lia.
  set (Wp1 := (Wm + dW + dP + 1)%Z).
  eassert (HM : dg_mem m1 _ 0 Ks bs).
  { unfold DgWalkB.dg_mem, DgWalkB.DG_W, DgWalkB.SP0. replace (bv_unsigned sp - 96)%Z with (bv_unsigned sp + -96)%Z by lia.
    split; [exact ST|]. split; [exact FR|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact BU|].
    split; [exact BL|]. split; [exact LE | exact KC]. }
  pose proof (Z.div_mod Wp1 (2 ^ s) ltac:(lia)) as DM. pose proof (Z.mod_pos_bound Wp1 (2 ^ s) ltac:(lia)) as MB.
  assert (P1lo : (8 <= Wp1 / 2 ^ s)%Z).
  { apply Z.div_le_lower_bound; [lia|]. assert (8 * 2 ^ s <= 8 * 2 ^ 59)%Z by lia. lia. }
  assert (P1hi : (Wp1 / 2 ^ s < 256)%Z) by (apply Z.div_lt_upper_bound; lia).
  eapply (dg_l1_k3 (Wp1 / 2 ^ s) 0 (Wp1 mod 2 ^ s) (Wm + dW + dP - Wm + 2) s Wp1 Ks); [exact HM | lia | lia | lia | lia | lia | lia | | lia].
  intros _. split; [lia | split; lia].
Qed.

End DGB4.
