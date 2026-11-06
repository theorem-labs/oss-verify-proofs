(* rp_slot_width walk, fuzz_egress plain 530b259d7622 0x132cc..0x1332c (repace_wire.c:101-109); ported from reac-repacer/fuzz_wire proofs/reac-repacer/fuzz_wire/lib/Prog/rp_slot_width.v at d876dac3b12: module path and the in-function pc literals moved by the function's shift; nothing else changed.
   rp_frame_channels is the named Section hypothesis HFC (its contract, rp_frame_channels_c.v). *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.Lib Require Import Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib Require Import Img0.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.Prog Require Import FrameBytes reac_frame_clean_len_c
  rp_frame_channels_c rp_slot_width_c rp_frame_channels.
Import ListNotations.
Open Scope Z_scope.

Lemma fc_model_range : forall len, rp_frame_channels_model len = -1 \/ 2 <= rp_frame_channels_model len <= 40.
Proof.
  intros len. unfold rp_frame_channels_model. cbv zeta.
  destruct (len <? 0); [left; reflexivity|].
  destruct ((reac_frame_clean_len_model len <? 52) || negb ((reac_frame_clean_len_model len - 52) mod 36 =? 0));
    [left; reflexivity|].
  set (v := bv_swrap 32 ((reac_frame_clean_len_model len - 52) / 36)).
  destruct (Z.ltb_spec v 2); [left; reflexivity|].
  destruct (Z.ltb_spec 40 v); [left; reflexivity|].
  destruct (Z.odd v); [left; reflexivity|]. right. cbn [orb]. lia.
Qed.

(* Bit 63 of a 64-bit value is its sign. *)
Lemma hi_bit : forall y, 0 <= y < 2^64 -> Z.testbit y 63 = (2^63 <=? y).
Proof.
  intros y Hy. destruct (Z.leb_spec (2^63) y) as [H|H].
  - apply Z.testbit_true; [lia|].
    assert (E : y / 2^63 = 1) by (symmetry; apply Z.div_unique with (r := y - 2^63); lia). rewrite E. reflexivity.
  - apply Z.testbit_false; [lia|]. rewrite Z.div_small by lia. reflexivity.
Qed.

Lemma lor_hi : forall a b, 0 <= a < 2^63 -> 0 <= b < 2^64 -> (2^63 <= Z.lor a b <-> 2^63 <= b).
Proof.
  intros a b Ha Hb. pose proof (lor_lt_pow2 a b 64 ltac:(lia) ltac:(lia)) as R.
  assert (E : (2^63 <=? Z.lor a b) = (2^63 <=? b)).
  { rewrite <- (hi_bit (Z.lor a b)) by lia. rewrite <- (hi_bit b) by lia.
    rewrite Z.lor_spec, (hi_bit a) by lia. rewrite (proj2 (Z.leb_gt (2^63) a)) by lia. reflexivity. }
  destruct (Z.leb_spec (2^63) (Z.lor a b)); destruct (Z.leb_spec (2^63) b); try discriminate E; lia.
Qed.

Lemma signed_lit : forall z, -2^63 <= z < 2^63 -> bv_signed (Z_to_bv 64 z) = z.
Proof.
  intros z Hz. rewrite zb_signed, unsigned_lit_wrap.
  destruct (Z.ltb_spec (z mod 2^64) (2^63)); cbv beta iota; Z.div_mod_to_equations; lia.
Qed.

Lemma ones_m1 : Z_to_bv 64 18446744073709551615 = Z_to_bv 64 (-1).
Proof. apply bv_eq. vm_compute. reflexivity. Qed.

(* slt a2, s0, a0 with a0 = nch. *)
Lemma slt_lit : forall (S : word) nch, -2^63 <= nch < 2^63 ->
  v_slt S (Z_to_bv 64 nch) = Z_to_bv 64 (if bv_signed S <? nch then 1 else 0).
Proof.
  intros S nch Hn. unfold v_slt, c_lts, bv_lts. rewrite (signed_lit nch Hn).
  destruct (bv_signed S <? nch); reflexivity.
Qed.

(* or a1, a0, s0; slti a1, a1, 0: nch < 0 or slot < 0. *)
Lemma slti_lor : forall (S : word) nch, (nch = -1 \/ 2 <= nch <= 40) ->
  v_slti (Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 nch)) (bv_unsigned S))) 0
  = Z_to_bv 64 (if (nch <? 0) || (bv_signed S <? 0) then 1 else 0).
Proof.
  intros S nch Hn. pose proof (u64_range S) as RS. unfold v_slti, zsig.
  destruct Hn as [-> | Hn].
  - change (bv_unsigned (Z_to_bv 64 (-1))) with 18446744073709551615.
    rewrite lor_ones64 by lia. reflexivity.
  - rewrite (unsigned_lit nch) by lia.
    pose proof (lor_lt_pow2 nch (bv_unsigned S) 64 ltac:(lia) ltac:(lia)) as RL.
    destruct (lor_hi nch (bv_unsigned S) ltac:(lia) ltac:(lia)) as [LH1 LH2].
    rewrite (zb_signed (Z_to_bv 64 (Z.lor nch (bv_unsigned S)))).
    rewrite (unsigned_lit (Z.lor nch (bv_unsigned S))) by lia.
    rewrite (zb_signed S). rewrite (proj2 (Z.ltb_ge nch 0)) by lia. cbn [orb].
    destruct (Z.ltb_spec (bv_unsigned S) (2^63)) as [HS|HS].
    + rewrite (proj2 (Z.ltb_lt (Z.lor nch (bv_unsigned S)) (2^63))) by lia. cbv beta iota.
      rewrite (proj2 (Z.ltb_ge (Z.lor nch (bv_unsigned S)) 0)), (proj2 (Z.ltb_ge (bv_unsigned S) 0)) by lia.
      reflexivity.
    + rewrite (proj2 (Z.ltb_ge (Z.lor nch (bv_unsigned S)) (2^63))) by lia. cbv beta iota.
      rewrite (proj2 (Z.ltb_lt (Z.lor nch (bv_unsigned S) - 2^64) 0)), (proj2 (Z.ltb_lt (bv_unsigned S - 2^64) 0))
        by lia.
      reflexivity.
Qed.

(* 0x13304..0x1331c: the width test on nch (register a0, N) and slot (register s0, S). *)
Lemma sw_tail : forall (N S : word) nch, N = Z_to_bv 64 nch -> (nch = -1 \/ 2 <= nch <= 40) ->
  Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64
     (Z.land (bv_unsigned (v_slt S N))
             (bv_unsigned (Z_to_bv 64 (Z.lxor (bv_unsigned (v_slti (Z_to_bv 64 (Z.lor (bv_unsigned N) (bv_unsigned S))) 0)) 1))))) + -1))))
     (bv_unsigned N))
  = Z_to_bv 64 (if (nch <? 0) || (bv_signed S <? 0) || (nch <=? bv_signed S) then -1 else nch).
Proof.
  intros N S nch -> Hn.
  pose proof (u64_range (Z_to_bv 64 nch)) as RN.
  rewrite (slti_lor S nch Hn), (slt_lit S nch) by (destruct Hn; lia).
  destruct ((nch <? 0) || (bv_signed S <? 0)) eqn:B1; destruct (Z.ltb_spec (bv_signed S) nch) as [B2|B2];
    cbv beta iota; fold_closed_in_goal.
  - rewrite lor_ones64 by lia. rewrite ones_m1. reflexivity.
  - rewrite lor_ones64 by lia. rewrite ones_m1. reflexivity.
  - rewrite Z.lor_0_l, Z_to_bv_lit_self. rewrite (proj2 (Z.leb_gt nch (bv_signed S))) by lia. reflexivity.
  - rewrite lor_ones64 by lia. rewrite ones_m1. rewrite (proj2 (Z.leb_le nch (bv_signed S))) by lia. reflexivity.
Qed.

Section SW.
Hypothesis HFC : rp_frame_channels_contract.

Ltac sw_finish sp :=
  lazymatch goal with
  | FR : rw_cells _ _ _ _, ST : stk _ _ _ _, MU : munch _ _ _, WM : wmono _ _ _, MI : mem_inv _ _ |- _ =>
      release_frame FR ST (bv_unsigned sp);
      apply evt_done; do 4 eexists; split; [reflexivity|];
      split; [exact MU|]; split; [exact WM|]; split; [exact MI|exact ST]
  end.

Ltac sw_minus1 a1 HN :=
  f_equal; unfold rp_slot_width_model, slot_byte;
  first [ rewrite (proj2 (Z.ltb_lt (bv_unsigned a1) 50) HN); reflexivity
        | rewrite (proj2 (Z.ltb_ge (bv_unsigned a1) 50) HN) ].

Theorem rp_slot_width_holds : rp_slot_width_contract.
Proof.
  unfold rp_slot_width_contract, RP_SLOT_WIDTH.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m bs lo
    MI ST LO HB.
  pose proof (u64_range sp) as Rsp. pose proof (u64_range a0) as Ra0. pose proof (u64_range a1) as Ra1.
  assert (Hlo : 0 <= lo) by (destruct ST as [? _]; lia).
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  destruct (Z.ltb_spec (bv_unsigned a1) 50) as [HN|HN].
  - (* n < 50 *)
    clear HB. carve_frame 16%nat ST. do 8 step. if_true. do 4 step.
    set_a0 (Z_to_bv 64 (rp_slot_width_model (bv_unsigned a1) bs (bv_signed a2))).
    2: { sw_minus1 a1 HN. }
    sw_finish sp.
  - destruct (HB HN) as (L18 & BB & DJ). clear HB.
    carve_frame 16%nat ST. do 8 step. if_false.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (rd1 mm _ bs 16 BB ltac:(lia)) as R16; pose proof (rd1 mm _ bs 17 BB ltac:(lia)) as R17 end.
    change (Z.of_nat 16) with 16 in R16. change (Z.of_nat 17) with 17 in R17.
    remember (nth 16 bs (Z_to_bv 8 0)) as b16 eqn:E16.
    remember (nth 17 bs (Z_to_bv 8 0)) as b17 eqn:E17.
    step. step. if_cases H16.
    + (* f[16] != 0 *)
      zify_cond H16. try rewrite zxb_u in H16. do 4 step.
      set_a0 (Z_to_bv 64 (rp_slot_width_model (bv_unsigned a1) bs (bv_signed a2))).
      2: { sw_minus1 a1 HN. rewrite <- E16. rewrite (proj2 (Z.eqb_neq _ 0) H16). reflexivity. }
      sw_finish sp.
    + zify_cond H16. try rewrite zxb_u in H16. step. step. if_cases H17.
      * (* f[17] != 0 *)
        zify_cond H17. try rewrite zxb_u in H17. do 4 step.
        set_a0 (Z_to_bv 64 (rp_slot_width_model (bv_unsigned a1) bs (bv_signed a2))).
        2: { sw_minus1 a1 HN. rewrite <- E16, <- E17.
             rewrite (proj2 (Z.eqb_eq _ 0) H16), (proj2 (Z.eqb_neq _ 0) H17). reflexivity. }
        sw_finish sp.
      * zify_cond H17. try rewrite zxb_u in H17. step. step.
        lazymatch goal with
        | FR : rw_cells _ ?m1 _ _, ST : stk _ _ _ _, MU : munch _ _ _, WM : wmono _ _ _, MI : mem_inv _ _ |- _ =>
          eapply evt_cut;
          [ eapply HFC with (lo := lo);
            [ exact MI | rewrite unsigned_lit by lia; exact ST | rewrite unsigned_lit by lia; lia ] |];
          intros ms' (a1' & a2' & a3' & m2 & -> & MU2 & WM2 & MI2 & ST2);
          rewrite (unsigned_lit (bv_unsigned sp + -16)) in MU2, ST2 by lia;
          pose proof (rw_cells_transport rsegs _ _ _ _ _ FR MU2 WM2
                        ltac:(cbn [disjoint_from cells_size csize Nat.add]; split; [lia | exact I])) as FR2;
          assert (MU3 : munch [(bv_unsigned sp - 32, bv_unsigned sp)] m m2)
            by (eapply munch_trans; [exact MU|];
                apply (munch_weaken [(bv_unsigned sp + -16 - 16, bv_unsigned sp + -16)]); [|exact MU2];
                intros x Hx; cbn [outside] in *; destruct Hx as [Hx _]; split; [lia | exact I]);
          pose proof (wmono_trans _ _ _ _ WM WM2) as WM3;
          clear FR MU WM MI MU2 WM2 ST
        end.
        replace (ret_pc (Z_to_bv 64 78596)) with (Z_to_bv 64 78596) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
        do 7 step. do 4 step.
        set_a0 (Z_to_bv 64 (rp_slot_width_model (bv_unsigned a1) bs (bv_signed a2))).
        2: { transitivity (Z_to_bv 64
               (if (rp_frame_channels_model (bv_signed a1) <? 0) || (bv_signed a2 <? 0)
                   || (rp_frame_channels_model (bv_signed a1) <=? bv_signed a2)
                then -1 else rp_frame_channels_model (bv_signed a1))).
             - sw_minus1 a1 HN. rewrite <- E16, <- E17.
               rewrite (proj2 (Z.eqb_eq _ 0) H16), (proj2 (Z.eqb_eq _ 0) H17). reflexivity.
             - symmetry. apply sw_tail; [reflexivity | apply fc_model_range]. }
        sw_finish sp.
Qed.

End SW.
