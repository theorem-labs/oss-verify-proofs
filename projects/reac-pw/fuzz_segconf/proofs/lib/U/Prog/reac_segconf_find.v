(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 3817 of its 3853 lines of code are new or changed and 212 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/ctrl_lay_block.v, with its module names changed; 85 of its 151 lines of code are new or changed and 3787 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/reac_box_catalogue_match_lib.v, with its module paths changed; 255 of its 299 lines of code are new or changed and 107 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_pin/lib/Prog/fuzz_catalogue_row.v, with its module paths, module names, addresses and numbers changed; 142 of its 211 lines of code are new or changed and 230 lines of the source are left out. *)
(** reac_segconf_find (UBSan build, 0x15ff0): proof of [reac_segconf_find_contract] (U/Prog/reac_segconf_find_c.v)
    from the contract of its callee strcmp (U/Prog/strcmp_c.v). Written new; the plain walk is
    lib/Prog/reac_segconf_find.v.

    Code (the UBSan binary):
      0x15ff0-0x1600c  frame of 64: ra s0 s1 s2 s3 s4 s5 at sp+56 .. sp+8 (sp+0 unused)
      0x16010 mv s0,a0; mv a0,zero; 0x16018 beqz s0 -> EPI; mv s1,a1; 0x16020 beqz a1 -> EPI
      0x16024 andi a0,s0,7; 0x16028 bnez a0 -> TRAP (c 8-aligned)
      0x1602c lui a0,3; add a0,s0,a0; 0x16034 lw a0,-0x380(a0) (n = c->n); 0x16038 blez a0 -> NONE
      0x1603c s2 = 0; s3 = ~c; s4 = (n > 0 ? n : 0) = n; s5 = 32
      LOOP 0x16054 beqz s5 -> TRAP (i = 32); 0x16058 bltu s3,s2 -> TRAP (c + 356 i wraps)
           mv a0,s0; mv a1,s1; 0x16064 jal strcmp; 0x16068 beqz a0 -> HIT
           s4 -= 1; s0 += 0x164; s2 += 0x164; s5 -= 1; 0x1607c bnez s4 -> LOOP
      NONE 0x16080 mv a0,zero; j EPI.  HIT 0x16088 mv a0,s0
      EPI  0x1608c restore ra s0-s5; addi sp,sp,64; ret.  TRAP 0x160b0 unimp
    The traps are not reached: c mod 16 = 0, i < n <= 32 (rconf_enc), c + 16616 <= 2^64 (bytes_at). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac ZBridge.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec seg_query_facts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require Import strcmp_c reac_segconf_find_c.
Import ListNotations.
Open Scope Z_scope.

(** The values the prologue computes. *)
Lemma fu_andi7 : forall c, 0 <= c < 2^64 -> c mod 16 = 0 -> Z.land (bv_unsigned (Z_to_bv 64 c)) 7 = 0.
Proof.
  intros c Hc H. rewrite unsigned_lit by lia. change 7 with (Z.ones 3).
  rewrite Z.land_ones by lia. change (2 ^ 3) with 8. Z.div_mod_to_equations. lia.
Qed.

(** s3 = ~c (`not s3,s0`, as the step leaves it). *)
Lemma fu_not : forall c, 0 <= c < 2^64 ->
  bv_unsigned (Z_to_bv 64 (Z.lxor (bv_unsigned (Z_to_bv 64 c)) 18446744073709551615)) = 18446744073709551615 - c.
Proof.
  intros c Hc. rewrite (unsigned_lit c) by lia. rewrite zb_lxor_ones by lia. apply unsigned_lit. lia.
Qed.

Lemma fu_slt_pos : forall n, 0 < n < 2^63 -> v_slt (Z_to_bv 64 0) (Z_to_bv 64 n) = Z_to_bv 64 1.
Proof.
  intros n Hn. unfold v_slt, c_lts. rewrite bv_lts_zero_l, unsigned_lit by lia.
  replace ((0 <? n) && (n <? 2^63)) with true by (symmetry; apply andb_true_iff; split; apply Z.ltb_lt; lia).
  reflexivity.
Qed.

(** s4 = (n > 0 ? n : 0) = n (`sgtz a1,a0; neg a1,a1; and s4,a1,a0`, as the steps leave it). *)
Lemma fu_s4 : forall n, 0 < n < 2^63 ->
  Z.land (bv_unsigned (Z_to_bv 64 (0 - bv_unsigned (v_slt (Z_to_bv 64 0) (Z_to_bv 64 n))))) (bv_unsigned (Z_to_bv 64 n))
  = n.
Proof.
  intros n Hn. rewrite fu_slt_pos by lia. rewrite (unsigned_lit 1), (unsigned_lit n) by lia.
  change (bv_unsigned (Z_to_bv 64 (0 - 1))) with (Z.ones 64).
  rewrite Z.land_comm, Z.land_ones by lia. apply Z.mod_small. lia.
Qed.

(** A branch that the facts in the context say is not taken. *)
Ltac fu_ntk := let K := fresh "K" in if_cases K; [exfalso; zify_cond K; Z.div_mod_to_equations; lia | clear K].

Section Find.
Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
  (m0 : word -> option byte) (c name Sp lo : Z) (bs sy : list byte) (rc : rconf) (nm : list Z).
Hypothesis HSC : strcmp_contract.
Hypothesis HB0 : bytes_at rsegs m0 c bs.
Hypothesis HE : rconf_enc rc bs.
Hypothesis HL : Z.of_nat (length bs) = 16616.
Hypothesis Hc : 0 < c.
Hypothesis Hc16 : c mod 16 = 0.
Hypothesis Hcb : c + 16616 <= 2^64.
Hypothesis HcA : c + 16616 <= lo \/ Sp <= c.
Hypothesis HN0 : bytes_at rsegs m0 name (sy ++ [Z_to_bv 8 0]).
Hypothesis HNZ : ~ In (Z_to_bv 8 0) sy.
Hypothesis HZY : zs sy = nm.
Hypothesis HNN : ~ In 0 nm.
Hypothesis Hname : 0 < name < 2^64.
Hypothesis HnA : name + Z.of_nat (length sy) + 1 <= lo \/ Sp <= name.
Hypothesis Hlo : 0 <= lo.
Hypothesis HK : lo + 64 <= Sp.
Hypothesis HS : Sp < 2^64.

Local Abbreviation Post := (fun ms' : machine_state =>
  exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
    ms' = MS (mkR ra (Z_to_bv 64 Sp) gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (find_ptr c rc nm))
                  a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom rsegs) /\
    munch [(Sp - 64, Sp)] m0 m' /\ wmono rsegs m0 m' /\ mem_inv rsegs m' /\ stk rsegs m' lo Sp).

(** The frame between the prologue and the epilogue (sp+0 .. sp+8 is not written). *)
Definition frm (m : word -> option byte) : Prop :=
  (exists j0, rw_cells rsegs m (Sp + -64) [CB 8 j0; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]) /\
  stk rsegs m lo (Sp + -64) /\ munch [(Sp - 64, Sp)] m0 m /\ wmono rsegs m0 m /\ mem_inv rsegs m.

Lemma frm_blk : forall m, frm m -> bytes_at rsegs m c bs.
Proof.
  intros m (_ & _ & MU & _ & _). eapply bytes_at_transport; [exact HB0 | exact MU |].
  cbn [disjoint_from]. split; [lia | exact I].
Qed.

Lemma frm_name : forall m, frm m -> bytes_at rsegs m name (sy ++ [Z_to_bv 8 0]).
Proof.
  intros m (_ & _ & MU & _ & _). eapply bytes_at_transport; [exact HN0 | exact MU |].
  rewrite length_app. cbn [length disjoint_from]. split; [lia | exact I].
Qed.

Lemma fu_nlt : (length (rc_seg rc) <= 32)%nat.
Proof. exact (proj2 (sq_rconf_len rc bs HE)). Qed.

(** The exit 0x1608c: restore ra and s0-s5, return with a0 = r. *)
Lemma epi : forall r m (x1 y0 y1 y2 w8 w9 z1 z2 z3 z4 z5 z6 z7 w18 w19 w20 w21 u3 u4 u5 u6 : word),
  r = find_ptr c rc nm -> frm m ->
  evt rsegs Post
    (MS (mkR x1 (Z_to_bv 64 (Sp + -64)) gp tp y0 y1 y2 w8 w9 (Z_to_bv 64 r) z1 z2 z3 z4 z5 z6 z7 w18
             w19 w20 w21 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
        F (Z_to_bv 64 0x1608c) fc None m (seg_rom rsegs)).
Proof.
  intros r m x1 y0 y1 y2 w8 w9 z1 z2 z3 z4 z5 z6 z7 w18 w19 w20 w21 u3 u4 u5 u6 Er ((j0 & FR) & ST & MU & WM & MI).
  do 9 step.
  apply evt_done. exists y0, y1, y2, z1, z2, z3, z4, z5, z6, z7, u3, u4, u5, u6, m.
  split; [subst r; unfold mkR; repeat f_equal; lia|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
  pose proof (stk_release rsegs m lo (Sp + -64) _ ST FR ltac:(lia)) as R. cbn [cells_size csize Nat.add] in R.
  replace (Sp + -64 + Z.of_nat 64) with Sp in R by lia. exact R.
Qed.

(** The loop head 0x16054 with k entries done (none of them named nm) and j = n - k left: s0 = &c->seg[k],
    s2 = 356 k, s3 = ~c, s4 = j, s5 = 32 - k. *)
Lemma loop : forall j k m (x1 y0 y1 y2 w10 z1 z2 z3 z4 z5 z6 z7 u3 u4 u5 u6 w8 w18 w19 w20 w21 : word),
  w8 = Z_to_bv 64 (c + 356 * Z.of_nat k) -> w18 = Z_to_bv 64 (356 * Z.of_nat k) ->
  bv_unsigned w19 = 18446744073709551615 - c -> w20 = Z_to_bv 64 (Z.of_nat j) ->
  w21 = Z_to_bv 64 (32 - Z.of_nat k) ->
  (k + j = length (rc_seg rc))%nat -> (0 < j)%nat ->
  r_find rc nm = r_find_go (skipn k (rc_seg rc)) nm k -> frm m ->
  evt rsegs Post
    (MS (mkR x1 (Z_to_bv 64 (Sp + -64)) gp tp y0 y1 y2 w8 (Z_to_bv 64 name) w10 z1 z2 z3 z4 z5 z6 z7
             w18 w19 w20 w21 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
        F (Z_to_bv 64 0x16054) fc None m (seg_rom rsegs)).
Proof.
  induction j as [|j IH];
    intros k m x1 y0 y1 y2 w10 z1 z2 z3 z4 z5 z6 z7 u3 u4 u5 u6 w8 w18 w19 w20 w21 E8 E18 E19 E20 E21 Hkj Hj RF FRM;
    [lia|].
  subst w8 w18 w20 w21. pose proof fu_nlt as NL.
  assert (Hk : (k < length (rc_seg rc))%nat) by lia.
  destruct (sq_seg_name rsegs m c bs rc k (frm_blk m FRM) HE Hk) as (sx & HX & HXZ & HXN & HSN).
  pose proof (sq_name_cmp sx sy _ nm HXN HZY HSN HNN) as CMP.
  rewrite (sq_find_go_step _ nm k Hk) in RF. fold (r_seg rc k) in RF.
  step. fu_ntk.
  step. fu_ntk.
  step. step. step.
  eapply evt_cut.
  { eapply HSC with (sx := sx) (sy := sy); rewrite ?unsigned_lit by lia.
    - exact HX.
    - exact HXZ.
    - exact (frm_name m FRM).
    - exact HNZ. }
  intros ms' (r & x11 & x12 & x13 & -> & Hr).
  rewrite ret_pc_even by (try lia; reflexivity).
  step.
  destruct (bv_eqb r (Z_to_bv 64 0)) eqn:K; cbv iota.
  - (* strcmp = 0: the entry is nm's *)
    apply sq_eqb_true in K. apply Hr, CMP in K.
    rewrite K, Z.eqb_refl in RF.
    step.
    eapply epi; [|exact FRM].
    unfold find_ptr. rewrite RF. unfold rseg_addr, RSEG_SIZE. reflexivity.
  - (* strcmp <> 0: the next entry *)
    apply sq_eqb_false in K.
    assert (NE : (strcmp (rs_name (r_seg rc k)) nm =? 0) = false).
    { apply Z.eqb_neq. intros E. apply K, Hr, CMP, E. }
    rewrite NE in RF.
    step. step. step. step. step.
    rewrite sq_eqb_lit by lia.
    destruct (Z.eqb_spec (Z.of_nat (S j) + -1) 0) as [J0|J0]; cbn [negb]; cbv iota.
    + (* that was the last entry: NULL *)
      assert (j = 0%nat) by lia. subst j.
      replace (S k) with (length (rc_seg rc)) in RF by lia. rewrite sq_find_go_end in RF.
      step. step.
      eapply epi; [|exact FRM].
      unfold find_ptr. rewrite RF. reflexivity.
    + eapply (IH (S k)); [f_equal; lia | f_equal; lia | exact E19 | f_equal; lia | f_equal; lia | lia | lia
                         | exact RF | exact FRM].
Qed.

(** The whole function from its entry. *)
Lemma body : forall (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
  stk rsegs m0 lo Sp -> mem_inv rsegs m0 ->
  evt rsegs Post
    (MS (mkR ra (Z_to_bv 64 Sp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 c) (Z_to_bv 64 name)
             a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x15ff0) fc None m0 (seg_rom rsegs)).
Proof.
  intros t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 ST MI.
  (* The prologue's stores transport (and so replace) the section hypotheses [loop] and [epi] use: take them
     first. *)
  pose proof (loop (length (rc_seg rc)) 0) as LP. pose proof epi as EP. pose proof fu_nlt as NL.
  pose proof (munch_refl [(Sp - 64, Sp)] m0) as MU. pose proof (wmono_refl rsegs m0) as WM.
  destruct (stk_carve rsegs m0 lo Sp 64 ST ltac:(lia)) as [ST1 [junk FR]]. clear ST.
  change (Z.of_nat 64) with 64 in ST1, FR.
  replace (Sp - 64) with (Sp + -64) in ST1, FR by lia.
  do 8 step.
  pose proof (sq_rc_n rsegs _ c bs rc HB0 HE) as RN. unfold RC_N in RN.
  step. step. step.
  rewrite sq_eqb_lit by lia. replace (c =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbv iota.
  step. step.
  rewrite sq_eqb_lit by lia. replace (name =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbv iota.
  step. rewrite fu_andi7 by lia.
  step. rewrite sq_eqb_lit by lia. rewrite Z.eqb_refl. cbn [negb]. cbv iota.
  step. step. step.
  rewrite sq_sx32 by lia.
  step.
  rewrite bv_lts_zero_l, unsigned_lit by lia.
  replace (Z.of_nat (length (rc_seg rc)) <? 2^63) with true by (symmetry; apply Z.ltb_lt; lia).
  rewrite andb_true_r.
  destruct (Z.ltb_spec 0 (Z.of_nat (length (rc_seg rc)))) as [P|P]; cbn [negb]; cbv iota.
  - do 6 step.
    eapply LP; [ f_equal; lia | reflexivity | apply fu_not; lia | f_equal; apply fu_s4; lia | reflexivity | lia | lia
               | reflexivity | ].
    refine (conj _ (conj _ (conj _ (conj _ _)))); [eexists|..]; eassumption.
  - (* no entry: NULL *)
    step. step.
    eapply EP; [|refine (conj _ (conj _ (conj _ (conj _ _)))); [eexists|..]; eassumption].
    unfold find_ptr, r_find. destruct (rc_seg rc) as [|e l] eqn:Eq; [reflexivity|].
    cbn [length] in P. lia.
Qed.

End Find.

Theorem reac_segconf_find_holds : strcmp_contract -> reac_segconf_find_contract.
Proof.
  intros HSC. unfold reac_segconf_find_contract, query_pre, FIND_STACK, REAC_SEGCONF_FIND.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo rc nm
    (Hc0 & Hc16 & (bs & HB & HE) & HcA & Hn0 & (sy & HN & HZY & HNN) & HnA & (ST & HK & H16 & HW) & MI).
  unfold apart, SEG_C_SIZE in *.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. pose proof (bv_unsigned_in_range 64 a0) as Ra0.
  pose proof (bv_unsigned_in_range 64 a1) as Ra1.
  change (bv_modulus 64) with (2^64) in Rsp, Ra0, Ra1.
  destruct (sq_rconf_len rc bs HE) as [HL _].
  pose proof (bytes_at_bound _ _ _ _ HB) as Bc.
  pose proof (proj1 ST) as Hlo.
  assert (HNZ : ~ In (Z_to_bv 8 0) sy) by (apply sq_zs_nul; rewrite HZY; exact HNN).
  assert (Ly : length sy = length nm) by (rewrite <- HZY; unfold zs; symmetry; apply length_map).
  pose proof (Z_to_bv_bv_unsigned sp) as Esp. pose proof (Z_to_bv_bv_unsigned a0) as Ea0.
  pose proof (Z_to_bv_bv_unsigned a1) as Ea1.
  set (Sp := bv_unsigned sp) in *. set (c := bv_unsigned a0) in *. set (name := bv_unsigned a1) in *.
  rewrite <- Esp, <- Ea0, <- Ea1. clearbody Sp c name. clear Esp Ea0 Ea1.
  eapply evt_mono.
  - eapply (body ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m c name Sp lo bs sy rc nm);
      first [eassumption | lia].
  - intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
                -> & MU & WM & MI' & ST').
    unfold ret_post. rewrite unsigned_lit by lia.
    exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [exact ST' | exact I].
Qed.
