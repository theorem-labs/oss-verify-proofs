(* model_decide (fuzz_link.c:423-431) and reac_served_decide (reac_served_mark.c:26-36), PLAIN build:
   the walk of their one contract (lib/Prog/model_decide_c.v), at both entries.

   The two functions are byte-identical (link/donors/REPORT.md section 5): 27 instructions at
   0x15eac and at 0x16404. `decide_walk` walks the code at MODEL_DECIDE; `decide_code_same` checks
   by computation over the image that the 27 words at REAC_SERVED_DECIDE are the same, with every
   pc-relative operand (two auipc for the .rodata strings and the two calls) giving the same target. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem mk_leaf mk_str model_decide_c strncmp_c strcmp_c strncmp strcmp.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Spec Require Import StrFun.
Local Open Scope Z_scope.

Definition decide_pre (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  exists k a,
    str_arg m (arg regs 0) k /\ str_arg m (arg regs 1) a /\
    (forall t, k = Some t -> apart_frame regs 16 (arg regs 0) (Z.of_nat (length t) + 1)) /\
    (forall t, a = Some t -> apart_frame regs 16 (arg regs 1) (Z.of_nat (length t) + 1)) /\
    cstr_at m A_PREFIX S_PREFIX /\ cstr_at m A_VLAN S_VLAN.

Definition decide_post (regs : bvmap 5 word) (m : word -> option byte)
    (regs' : bvmap 5 word) (m' : word -> option byte) : Prop :=
  forall k a, str_arg m (arg regs 0) k -> str_arg m (arg regs 1) a -> getr regs' 10 = wz (decide k a).

Ltac dec_finish Hk' Ha' :=
  apply evt_done; eexists; eexists; split; [reflexivity|];
  split; [eapply regs_preserved_mkR|];
  split; [cbv [writes_nothing];
          lazymatch goal with MU : munch [(?l1, _)] ?m ?m1 |- munch [(?l2, _)] ?m ?m1 =>
            replace l2 with l1 by lia; exact MU end|];
  split; [eassumption|]; split; [eassumption|]; split; [eassumption|];
  let k0 := fresh "k0" in let a' := fresh "a'" in let H0 := fresh "H0" in let H1 := fresh "H1" in
  intros k0 a' H0 H1;
  rewrite (str_arg_unique _ _ _ _ H0 Hk'), (str_arg_unique _ _ _ _ H1 Ha').

Theorem model_decide_walk : strncmp_contract -> strcmp_contract ->
  leaf_walk MODEL_DECIDE 16 decide_pre writes_nothing decide_post.
Proof.
  intros HSN HSC. unfold leaf_walk, MODEL_DECIDE, decide_pre, decide_post.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo.
  cbv zeta. intros (k & al & Hk & Ha & Fk & Fa & _ & _) MI ST LO SP.
  pose proof Hk as Hk'. pose proof Ha as Ha'.
  rewrite mkR_a0 in Hk. rewrite mkR_a1 in Ha.
  unfold apart_frame in Fk, Fa. rewrite mkR_sp, mkR_a0 in Fk. rewrite mkR_sp, mkR_a1 in Fa.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  assert (L0 : 0 <= lo) by (destruct ST as [? _]; lia).
  carve_frame 16%nat ST.
  zstep. zstep. zstep.
  (* the kind path, from 0x15ee4, shared by a NULL and an empty alias *)
  assert (KIND : forall x12 : word,
    decide k al = match k with Some t => if bl_eqb t S_VLAN then V_LEAVE_VLAN else V_MARK | None => V_MARK end ->
    evt rsegs
      (fun ms' => exists (regs' : bvmap 5 word) (m' : word -> option byte),
         ms' = MS regs' F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         regs_preserved (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) regs' /\
         munch ((bv_unsigned sp - 16, bv_unsigned sp)
                :: writes_nothing (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) m) m m' /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp) /\
         (forall k0 a', str_arg m (arg (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) 0) k0 ->
              str_arg m (arg (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) 1) a' ->
              getr regs' 10 = wz (decide k0 a')))
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 s0 s1 a0 a1 x12 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 89828) fc None m0 (seg_rom rsegs))).
  { intros x12 Hd. zstep.
    destruct k as [t|].
    - destruct Hk as [Hk0 Hkt]. if_false.
      pose proof (Fk t eq_refl) as Ft.
      assert (Bt : bytes_at rsegs m0 (bv_unsigned a0) (t ++ [zb 0])).
      { eapply bytes_at_transport; [exact (proj1 Hkt) | exact MU |].
        cbn [disjoint_from]. rewrite length_app. cbn [length]. lia. }
      zstep. zstep. zstep.
      eapply evt_cut.
      { eapply HSC with (sx := t) (sy := S_VLAN); [exact Bt | exact (proj2 Hkt) | | exact S_VLAN_no_nul].
        rewrite unsigned_lit by lia. exact (vlan_at m0 MI). }
      intros ms' (r & x11 & x12' & x13 & -> & Hr).
      rewrite ret_pc_even by (lia || reflexivity).
      zstep.
      case_eq (bv_eqb r (Z_to_bv 64 0)); intros Er.
      + cbv iota. zstep. zstep. zstep. release_frame FR ST (bv_unsigned sp). zstep.
        dec_finish Hk' Ha'. rewrite Hd. apply bv_eqb_true in Er.
        replace (bl_eqb t S_VLAN) with true by (symmetry; apply bl_eqb_iff, Hr, Er). reflexivity.
      + cbv iota. zstep. zstep. zstep. zstep. release_frame FR ST (bv_unsigned sp). zstep.
        dec_finish Hk' Ha'. rewrite Hd. destruct (bl_eqb t S_VLAN) eqn:Hb; [|reflexivity].
        exfalso. apply (bv_eqb_false _ _ Er). apply bl_eqb_iff in Hb. rewrite (proj2 Hr Hb). reflexivity.
    - cbn in Hk. if_true. zstep. zstep. zstep. zstep. release_frame FR ST (bv_unsigned sp). zstep.
      dec_finish Hk' Ha'. rewrite Hd. reflexivity. }
  destruct al as [s|].
  - destruct Ha as [Ha0 Has]. if_false.
    pose proof (Fa s eq_refl) as Fs.
    assert (Bs : bytes_at rsegs m0 (bv_unsigned a1) (s ++ [zb 0])).
    { eapply bytes_at_transport; [exact (proj1 Has) | exact MU |].
      cbn [disjoint_from]. rewrite length_app. cbn [length]. lia. }
    destruct s as [|x s'].
    + pose proof (bytes_at_read1 m0 a1 (zb 0) [] Bs) as HR.
      zstep. unfold zb. zstep. if_true. apply KIND. reflexivity.
    + assert (Hx : bv_unsigned x <> 0).
      { intros E. apply (proj2 Has). left. apply byte_zero. exact E. }
      pose proof (bytes_at_read1 m0 a1 x (s' ++ [zb 0]) Bs) as HR.
      zstep. zstep.
      assert (Ex : bv_eqb (Z_to_bv 64 (bv_unsigned x)) (Z_to_bv 64 0) = false).
      { rewrite bv_eqb_lit by (pose proof (byte_range x); lia). apply Z.eqb_neq. exact Hx. }
      rewrite Ex. cbv iota.
      zstep. zstep. zstep. zstep. zstep. zstep.
      destruct (strncmp_prefix (x :: s') (proj2 Has)) as (v & Hv & Rv & Iv).
      eapply evt_cut.
      { eapply HSN with (ls := (x :: s') ++ [zb 0]) (rs := S_PREFIX ++ [zb 0]) (v := v).
        - exact Bs.
        - rewrite unsigned_lit by lia. exact (prefix_at m0 MI).
        - rewrite unsigned_lit by lia. exact Hv.
        - exact MI. }
      intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1
                  & -> & MU1 & WM1 & MI1 & _ & _).
      pose proof (rw_cells_transport rsegs [] m0 m1 _ _ FR MU1 WM1 I) as FR1.
      pose proof (stk_transport_disjoint rsegs [] m0 m1 lo _ ST MU1 WM1 I) as ST1.
      pose proof (munch_trans _ m m0 m1 MU (munch_weaken [] _ m0 m1 (fun x _ => I) MU1)) as MU2.
      pose proof (wmono_trans rsegs m m0 m1 WM WM1) as WM2.
      clear FR ST MU WM MI MU1 WM1. rename FR1 into FR, ST1 into ST, MU2 into MU, WM2 into WM, MI1 into MI.
      rewrite ret_pc_even by (lia || reflexivity).
      zstep.
      rewrite bv_eqb_z0 by lia.
      destruct (Z.eqb_spec v 0) as [E0|N0].
      * subst v. cbv iota. zstep. zstep. zstep. zstep.
        release_frame FR ST (bv_unsigned sp). zstep.
        dec_finish Hk' Ha'.
        cbn [decide length Nat.eqb negb]. replace (has_prefix (x :: s')) with true by (symmetry; apply Iv; reflexivity).
        reflexivity.
      * cbv iota.
        zstep. zstep. zstep. zstep.
        release_frame FR ST (bv_unsigned sp). zstep.
        dec_finish Hk' Ha'.
        cbn [decide length Nat.eqb negb].
        destruct (has_prefix (x :: s')) eqn:Hh; [exfalso; apply N0, Iv; first [exact Hh | reflexivity] | reflexivity].
  - cbn in Ha. if_true. apply KIND. reflexivity.
Qed.

(* The same script walks the second copy: the code at REAC_SERVED_DECIDE (0x16404) is the code at
   MODEL_DECIDE (0x15eac) shifted by 0x558, so only the literal pc of the kind path moves
   (0x15ee4 = 89828 -> 0x1643c = 91196); `zstep` decodes every instruction from the image at its own
   address, so each step of this second walk is checked against the bytes at 0x16404. *)

Theorem reac_served_decide_walk : strncmp_contract -> strcmp_contract ->
  leaf_walk REAC_SERVED_DECIDE 16 decide_pre writes_nothing decide_post.
Proof.
  intros HSN HSC. unfold leaf_walk, REAC_SERVED_DECIDE, decide_pre, decide_post.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo.
  cbv zeta. intros (k & al & Hk & Ha & Fk & Fa & _ & _) MI ST LO SP.
  pose proof Hk as Hk'. pose proof Ha as Ha'.
  rewrite mkR_a0 in Hk. rewrite mkR_a1 in Ha.
  unfold apart_frame in Fk, Fa. rewrite mkR_sp, mkR_a0 in Fk. rewrite mkR_sp, mkR_a1 in Fa.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  assert (L0 : 0 <= lo) by (destruct ST as [? _]; lia).
  carve_frame 16%nat ST.
  zstep. zstep. zstep.
  (* the kind path, from 0x15ee4, shared by a NULL and an empty alias *)
  assert (KIND : forall x12 : word,
    decide k al = match k with Some t => if bl_eqb t S_VLAN then V_LEAVE_VLAN else V_MARK | None => V_MARK end ->
    evt rsegs
      (fun ms' => exists (regs' : bvmap 5 word) (m' : word -> option byte),
         ms' = MS regs' F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         regs_preserved (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) regs' /\
         munch ((bv_unsigned sp - 16, bv_unsigned sp)
                :: writes_nothing (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) m) m m' /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp) /\
         (forall k0 a', str_arg m (arg (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) 0) k0 ->
              str_arg m (arg (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) 1) a' ->
              getr regs' 10 = wz (decide k0 a')))
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 s0 s1 a0 a1 x12 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 91196) fc None m0 (seg_rom rsegs))).
  { intros x12 Hd. zstep.
    destruct k as [t|].
    - destruct Hk as [Hk0 Hkt]. if_false.
      pose proof (Fk t eq_refl) as Ft.
      assert (Bt : bytes_at rsegs m0 (bv_unsigned a0) (t ++ [zb 0])).
      { eapply bytes_at_transport; [exact (proj1 Hkt) | exact MU |].
        cbn [disjoint_from]. rewrite length_app. cbn [length]. lia. }
      zstep. zstep. zstep.
      eapply evt_cut.
      { eapply HSC with (sx := t) (sy := S_VLAN); [exact Bt | exact (proj2 Hkt) | | exact S_VLAN_no_nul].
        rewrite unsigned_lit by lia. exact (vlan_at m0 MI). }
      intros ms' (r & x11 & x12' & x13 & -> & Hr).
      rewrite ret_pc_even by (lia || reflexivity).
      zstep.
      case_eq (bv_eqb r (Z_to_bv 64 0)); intros Er.
      + cbv iota. zstep. zstep. zstep. release_frame FR ST (bv_unsigned sp). zstep.
        dec_finish Hk' Ha'. rewrite Hd. apply bv_eqb_true in Er.
        replace (bl_eqb t S_VLAN) with true by (symmetry; apply bl_eqb_iff, Hr, Er). reflexivity.
      + cbv iota. zstep. zstep. zstep. zstep. release_frame FR ST (bv_unsigned sp). zstep.
        dec_finish Hk' Ha'. rewrite Hd. destruct (bl_eqb t S_VLAN) eqn:Hb; [|reflexivity].
        exfalso. apply (bv_eqb_false _ _ Er). apply bl_eqb_iff in Hb. rewrite (proj2 Hr Hb). reflexivity.
    - cbn in Hk. if_true. zstep. zstep. zstep. zstep. release_frame FR ST (bv_unsigned sp). zstep.
      dec_finish Hk' Ha'. rewrite Hd. reflexivity. }
  destruct al as [s|].
  - destruct Ha as [Ha0 Has]. if_false.
    pose proof (Fa s eq_refl) as Fs.
    assert (Bs : bytes_at rsegs m0 (bv_unsigned a1) (s ++ [zb 0])).
    { eapply bytes_at_transport; [exact (proj1 Has) | exact MU |].
      cbn [disjoint_from]. rewrite length_app. cbn [length]. lia. }
    destruct s as [|x s'].
    + pose proof (bytes_at_read1 m0 a1 (zb 0) [] Bs) as HR.
      zstep. unfold zb. zstep. if_true. apply KIND. reflexivity.
    + assert (Hx : bv_unsigned x <> 0).
      { intros E. apply (proj2 Has). left. apply byte_zero. exact E. }
      pose proof (bytes_at_read1 m0 a1 x (s' ++ [zb 0]) Bs) as HR.
      zstep. zstep.
      assert (Ex : bv_eqb (Z_to_bv 64 (bv_unsigned x)) (Z_to_bv 64 0) = false).
      { rewrite bv_eqb_lit by (pose proof (byte_range x); lia). apply Z.eqb_neq. exact Hx. }
      rewrite Ex. cbv iota.
      zstep. zstep. zstep. zstep. zstep. zstep.
      destruct (strncmp_prefix (x :: s') (proj2 Has)) as (v & Hv & Rv & Iv).
      eapply evt_cut.
      { eapply HSN with (ls := (x :: s') ++ [zb 0]) (rs := S_PREFIX ++ [zb 0]) (v := v).
        - exact Bs.
        - rewrite unsigned_lit by lia. exact (prefix_at m0 MI).
        - rewrite unsigned_lit by lia. exact Hv.
        - exact MI. }
      intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1
                  & -> & MU1 & WM1 & MI1 & _ & _).
      pose proof (rw_cells_transport rsegs [] m0 m1 _ _ FR MU1 WM1 I) as FR1.
      pose proof (stk_transport_disjoint rsegs [] m0 m1 lo _ ST MU1 WM1 I) as ST1.
      pose proof (munch_trans _ m m0 m1 MU (munch_weaken [] _ m0 m1 (fun x _ => I) MU1)) as MU2.
      pose proof (wmono_trans rsegs m m0 m1 WM WM1) as WM2.
      clear FR ST MU WM MI MU1 WM1. rename FR1 into FR, ST1 into ST, MU2 into MU, WM2 into WM, MI1 into MI.
      rewrite ret_pc_even by (lia || reflexivity).
      zstep.
      rewrite bv_eqb_z0 by lia.
      destruct (Z.eqb_spec v 0) as [E0|N0].
      * subst v. cbv iota. zstep. zstep. zstep. zstep.
        release_frame FR ST (bv_unsigned sp). zstep.
        dec_finish Hk' Ha'.
        cbn [decide length Nat.eqb negb]. replace (has_prefix (x :: s')) with true by (symmetry; apply Iv; reflexivity).
        reflexivity.
      * cbv iota.
        zstep. zstep. zstep. zstep.
        release_frame FR ST (bv_unsigned sp). zstep.
        dec_finish Hk' Ha'.
        cbn [decide length Nat.eqb negb].
        destruct (has_prefix (x :: s')) eqn:Hh; [exfalso; apply N0, Iv; first [exact Hh | reflexivity] | reflexivity].
  - cbn in Ha. if_true. apply KIND. reflexivity.
Qed.

Lemma decide_pre_ext : pre_ext decide_pre.
Proof. intros r1 r2 m E H. unfold decide_pre, apart_frame, arg, spZ in *. rewrite <- !E. exact H. Qed.

Lemma decide_post_ext : post_ext decide_post.
Proof.
  intros r1 r2 m q1 q2 m' E1 E2 H k a Hk Ha. unfold decide_post, arg in *. rewrite <- E2.
  apply H; rewrite E1; assumption.
Qed.

Theorem model_decide_holds : strncmp_contract -> strcmp_contract -> model_decide_contract.
Proof.
  intros HSN HSC. unfold model_decide_contract, decide_contract. apply leaf_intro.
  - exact decide_pre_ext.
  - intros r1 r2 m _. reflexivity.
  - exact decide_post_ext.
  - exact (model_decide_walk HSN HSC).
Qed.

Theorem reac_served_decide_holds : strncmp_contract -> strcmp_contract -> reac_served_decide_contract.
Proof.
  intros HSN HSC. unfold reac_served_decide_contract, decide_contract. apply leaf_intro.
  - exact decide_pre_ext.
  - intros r1 r2 m _. reflexivity.
  - exact decide_post_ext.
  - exact (reac_served_decide_walk HSN HSC).
Qed.

(* closed: the two callees by their released walks (lib/Prog/strncmp.v, lib/Prog/strcmp.v) *)
Theorem model_decide_closed : model_decide_contract.
Proof. exact (model_decide_holds strncmp_holds strcmp_holds). Qed.
Theorem reac_served_decide_closed : reac_served_decide_contract.
Proof. exact (reac_served_decide_holds strncmp_holds strcmp_holds). Qed.
