(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 3817 of its 3853 lines of code are new or changed and 212 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/ctrl_lay_block.v, with its module names changed; 85 of its 151 lines of code are new or changed and 3787 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/reac_box_catalogue_match_lib.v, with its module paths changed; 255 of its 299 lines of code are new or changed and 107 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_pin/lib/Prog/fuzz_catalogue_row.v, with its module paths, module names, addresses and numbers changed; 136 of its 194 lines of code are new or changed and 241 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/U/Prog/name_ok.v, with its module paths, addresses and numbers changed; 17 of its 186 lines of code are new or changed and 25 lines of the source are left out. *)
(** name_ok (plain build, 0x15bc0): proof of [name_ok_contract] (name_ok_c.v) from the contract of its callee
    isalnum (isalnum_c.v). Written new; the UBSan walk is U/Prog/name_ok.v.

    Code (the plain build's disassembly):
      0x15bc0-0x15bd4  frame of 48: ra s0 s1 s2 s3 at sp+40 .. sp+8 (sp+0 unused)
      0x15bd8 lbu s3,0(a0); 0x15bdc beqz s3 -> ZERO
      0x15be0 s0 = a0 + 1; s1 = 0x32; 0x15be8-0x15bf8 s2 = ((1 << 37) + 1) << 13 + 3 = 2^50 + 2^13 + 3
      LOOP 0x15bfc andi a0,s3,0xff; 0x15c00 jal isalnum; 0x15c04 bnez a0 -> NEXT
           0x15c08 a1 = s3 - 0x2d; 0x15c0c bltu s1,a1 -> EPI (a0 = 0);
           0x15c10 srl a1,s2,a1; andi a1,a1,1; 0x15c18 beqz a1 -> EPI (a0 = 0)
      NEXT 0x15c1c lbu s3,0(s0); s0++; 0x15c24 bnez s3 -> LOOP; 0x15c28 a0 = 1; j EPI
      ZERO 0x15c30 mv a0,zero.  EPI 0x15c34 restore ra s0-s3; addi sp,sp,48; ret
    Shape as reac_segconf_find.v: [epi] the shared exit, [loop] an induction on the bytes left (s0 = s + k + 1,
    s3 = s[k], k < length), with the invariant name_ok nm = forallb nok_ch (skipn k nm): every byte before k is
    alnum or one of "-.:_", [body] the prologue. Model side: name_ok_facts.v (the nok_ lemmas) and
    SegBridge.bridge_isalnum (alnum_b is SegModel.isalnum on a byte). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac ZBridge Arr.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require SegBridge.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec seg_query_facts isalnum_c name_ok_c name_ok_facts.
Import ListNotations.
Open Scope Z_scope.

Section NameOk.
Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
  (m0 : word -> option byte) (a Sp lo : Z) (bs : list byte).
Hypothesis HIS : isalnum_contract.
Hypothesis HB0 : bytes_at rsegs m0 a (bs ++ [Z_to_bv 8 0]).
Hypothesis HNZ : ~ In (Z_to_bv 8 0) bs.
Hypothesis HNN : ~ In 0 (zs bs).
Hypothesis Ha : 0 < a.
Hypothesis HaA : a + Z.of_nat (length bs) + 1 <= lo \/ Sp <= a.
Hypothesis Hlo : 0 <= lo.
Hypothesis HK : lo + 48 <= Sp.
Hypothesis HS : Sp < 2^64.

Local Abbreviation Post := (fun ms' : machine_state =>
  exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
    ms' = MS (mkR ra (Z_to_bv 64 Sp) gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (b2z (name_ok (zs bs))))
                  a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom rsegs) /\
    munch [(Sp - 48, Sp)] m0 m' /\ wmono rsegs m0 m' /\ mem_inv rsegs m' /\ stk rsegs m' lo Sp).

(** The frame between the prologue and the epilogue (sp+0 .. sp+8 is not written). *)
Definition frm (m : word -> option byte) : Prop :=
  (exists j0, rw_cells rsegs m (Sp + -48) [CB 8 j0; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]) /\
  stk rsegs m lo (Sp + -48) /\ munch [(Sp - 48, Sp)] m0 m /\ wmono rsegs m0 m /\ mem_inv rsegs m.

Lemma frm_str : forall m, frm m -> bytes_at rsegs m a (bs ++ [Z_to_bv 8 0]).
Proof.
  intros m (_ & _ & MU & _ & _). eapply bytes_at_transport; [exact HB0 | exact MU |].
  rewrite length_app. cbn [length disjoint_from]. split; [lia | exact I].
Qed.

Lemma frm_read : forall m k b, frm m -> nth_error (bs ++ [Z_to_bv 8 0]) k = Some b ->
  ov_read_bytes rsegs m (Z_to_bv 64 (a + Z.of_nat k)) 1 = Some [b].
Proof.
  intros m k b FRM E.
  apply (u8ro_read rsegs m a (bs ++ [Z_to_bv 8 0]) (Z.of_nat k) b _ (frm_str m FRM));
    [rewrite Nat2Z.id; exact E | lia | reflexivity].
Qed.

(** The exit 0x15c34: restore ra and s0-s3, return with a0 = r. *)
Lemma epi : forall r m (x1 y0 y1 y2 w8 w9 z1 z2 z3 z4 z5 z6 z7 w18 w19 u3 u4 u5 u6 : word),
  r = b2z (name_ok (zs bs)) -> frm m ->
  evt rsegs Post
    (MS (mkR x1 (Z_to_bv 64 (Sp + -48)) gp tp y0 y1 y2 w8 w9 (Z_to_bv 64 r) z1 z2 z3 z4 z5 z6 z7 w18 w19
             s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
        F (Z_to_bv 64 0x15c34) fc None m (seg_rom rsegs)).
Proof.
  intros r m x1 y0 y1 y2 w8 w9 z1 z2 z3 z4 z5 z6 z7 w18 w19 u3 u4 u5 u6 Er ((j0 & FR) & ST & MU & WM & MI).
  do 7 step.
  apply evt_done. exists y0, y1, y2, z1, z2, z3, z4, z5, z6, z7, u3, u4, u5, u6, m.
  split; [subst r; unfold mkR; repeat f_equal; lia|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
  pose proof (stk_release rsegs m lo (Sp + -48) _ ST FR ltac:(lia)) as R. cbn [cells_size csize Nat.add] in R.
  replace (Sp + -48 + Z.of_nat 48) with Sp in R by lia. exact R.
Qed.

(** The loop head 0x15bfc with the bytes before k passed and j = length bs - k left: s0 = s + k + 1, s3 = s[k]
    (not the NUL), s1 = 0x32, s2 = the mask. *)
Lemma loop : forall j k m (b : byte) (x1 y0 y1 y2 w10 z1 z2 z3 z4 z5 z6 z7 u3 u4 u5 u6 w8 w19 : word),
  w8 = Z_to_bv 64 (a + Z.of_nat k + 1) -> w19 = Z_to_bv 64 (bv_unsigned b) ->
  (k + j = length bs)%nat -> (0 < j)%nat -> nth_error bs k = Some b ->
  name_ok (zs bs) = forallb nok_ch (skipn k (zs bs)) -> frm m ->
  evt rsegs Post
    (MS (mkR x1 (Z_to_bv 64 (Sp + -48)) gp tp y0 y1 y2 w8 (Z_to_bv 64 50) w10 z1 z2 z3 z4 z5 z6 z7
             (Z_to_bv 64 1125899906850819) w19 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
        F (Z_to_bv 64 0x15bfc) fc None m (seg_rom rsegs)).
Proof.
  induction j as [|j IH];
    intros k m b x1 y0 y1 y2 w10 z1 z2 z3 z4 z5 z6 z7 u3 u4 u5 u6 w8 w19 E8 E19 Hkj Hj Eb RF FRM; [lia|].
  subst w8 w19.
  pose proof (nok_byte_range b) as Rb.
  assert (Ex : nth_error (zs bs) k = Some (bv_unsigned b)).
  { unfold zs. rewrite nth_error_map, Eb. reflexivity. }
  rewrite (nok_skipn_cons _ _ _ Ex) in RF. cbn [forallb] in RF.
  (* NEXT 0x15c1c: byte k passed; read byte k + 1. *)
  assert (NEXT : nok_ch (bv_unsigned b) = true -> forall (x1' w10' z1' : word),
    evt rsegs Post
      (MS (mkR x1' (Z_to_bv 64 (Sp + -48)) gp tp y0 y1 y2 (Z_to_bv 64 (a + Z.of_nat k + 1)) (Z_to_bv 64 50) w10'
               z1' z2 z3 z4 z5 z6 z7 (Z_to_bv 64 1125899906850819) (Z_to_bv 64 (bv_unsigned b)) s4 s5 s6 s7 s8 s9 s10 s11
               u3 u4 u5 u6)
          F (Z_to_bv 64 0x15c1c) fc None m (seg_rom rsegs))).
  { intros OK x1' w10' z1'. rewrite OK in RF. cbn [andb] in RF.
    destruct (nok_nth_full bs (S k) ltac:(lia)) as [b' E'].
    assert (RD : ov_read_bytes rsegs m (Z_to_bv 64 (a + Z.of_nat k + 1)) 1 = Some [b']).
    { replace (a + Z.of_nat k + 1) with (a + Z.of_nat (S k)) by lia. exact (frm_read m (S k) b' FRM E'). }
    step. step. step.
    if_cases K; zify_cond K; rewrite ?nok_u_zxb, ?nok_u_byte in K; cbv iota.
    - (* not the NUL: the next byte *)
      assert (Il : (S k < length bs)%nat).
      { destruct (Nat.eq_dec (S k) (length bs)) as [Ei|]; [|lia]. exfalso. apply K.
        apply (nok_nth_full_zero bs (S k) b' HNZ E'). exact Ei. }
      rewrite nth_error_app1 in E' by lia.
      eapply (IH (S k)); [f_equal; lia | reflexivity | lia | lia | exact E' | exact RF | exact FRM].
    - (* the NUL: every byte passed *)
      apply (nok_nth_full_zero bs (S k) b' HNZ E') in K.
      step. step.
      eapply epi; [|exact FRM].
      rewrite RF, nok_forallb_end by (unfold zs; rewrite length_map; lia). reflexivity. }
  step. step.
  eapply evt_cut.
  { eapply HIS with (c := bv_unsigned b); [exact Rb | rewrite ?nok_u_zxb, ?nok_u_byte, nok_land255; reflexivity]. }
  intros ms' (a1' & ->).
  rewrite ret_pc_even by (try lia; reflexivity).
  destruct (alnum_b (bv_unsigned b)) eqn:AL.
  - (* alnum *)
    pose proof (SegBridge.bridge_isalnum _ Rb) as BR. rewrite AL in BR.
    step. if_true.
    apply NEXT. apply nok_ch_alnum. rewrite <- BR. reflexivity.
  - (* not alnum: one of "-.:_" or out *)
    pose proof (SegBridge.bridge_isalnum _ Rb) as BR. rewrite AL in BR.
    assert (NC : nok_ch (bv_unsigned b) = nok_sp (bv_unsigned b)) by (apply nok_ch_sp; rewrite <- BR; reflexivity).
    step. if_false. step. step.
    if_cases K; zify_cond K; rewrite ?nok_u_zxb, ?nok_u_byte in K; cbv iota.
    + (* below '-' or above '_' *)
      assert (SP : nok_sp (bv_unsigned b) = false) by (apply nok_sp_out; exact (nok_rng_out _ Rb K)).
      eapply epi; [|exact FRM]. rewrite RF, NC, SP. reflexivity.
    + apply (nok_rng_in _ Rb) in K.
      step. step. step.
      if_cases K2; zify_cond K2; rewrite ?nok_u_zxb, ?nok_u_byte in K2; cbv iota;
        rewrite ?(Z.mod_small (bv_unsigned b + -45) 18446744073709551616), ?(Z.mod_small (bv_unsigned b + -45) 64)
          in K2 by lia.
      * (* bit clear: not one of "-.:_" *)
        apply (proj1 (nok_bit_z _ K)) in K2.
        eapply epi; [|exact FRM]. rewrite RF, NC, K2. reflexivity.
      * (* bit set *)
        apply NEXT. rewrite NC.
        destruct (nok_sp (bv_unsigned b)) eqn:E; [reflexivity|].
        exfalso. apply K2. apply (proj2 (nok_bit_z _ K)). exact E.
Qed.

(** The whole function from its entry. *)
Lemma body : forall (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
  stk rsegs m0 lo Sp -> mem_inv rsegs m0 ->
  evt rsegs Post
    (MS (mkR ra (Z_to_bv 64 Sp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 a) a1
             a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x15bc0) fc None m0 (seg_rom rsegs)).
Proof.
  intros t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 ST MI.
  (* The prologue's stores transport (and so replace) the section hypotheses [loop], [epi] and [frm_read] use:
     take them first. *)
  pose proof (loop (length bs) 0) as LP. pose proof epi as EP. pose proof frm_read as FRD.
  pose proof (munch_refl [(Sp - 48, Sp)] m0) as MU. pose proof (wmono_refl rsegs m0) as WM.
  destruct (stk_carve rsegs m0 lo Sp 48 ST ltac:(lia)) as [ST1 [junk FR]]. clear ST.
  change (Z.of_nat 48) with 48 in ST1, FR.
  replace (Sp - 48) with (Sp + -48) in ST1, FR by lia.
  do 6 step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into M1 end.
  assert (FRM : frm M1) by (refine (conj _ (conj _ (conj _ (conj _ _)))); [eexists|..]; eassumption).
  destruct (nok_nth_full bs 0 ltac:(lia)) as [b0 E0]. pose proof (nok_byte_range b0) as R0.
  assert (RD0 : ov_read_bytes rsegs M1 (Z_to_bv 64 a) 1 = Some [b0]).
  { pose proof (FRD M1 0%nat b0 FRM E0) as R. change (Z.of_nat 0) with 0 in R. rewrite Z.add_0_r in R. exact R. }
  step. step.
  if_cases K; zify_cond K; rewrite ?nok_u_zxb, ?nok_u_byte in K; cbv iota.
  - (* the empty string *)
    apply (nok_nth_full_zero bs 0 b0 HNZ E0) in K.
    step.
    eapply EP; [|exact FRM].
    replace bs with (@nil byte) by (symmetry; apply length_zero_iff_nil; lia). reflexivity.
  - assert (Il : (0 < length bs)%nat).
    { destruct (Nat.eq_dec 0 (length bs)) as [Ei|]; [|lia]. exfalso. apply K.
      apply (nok_nth_full_zero bs 0 b0 HNZ E0). exact Ei. }
    rewrite nth_error_app1 in E0 by lia.
    do 7 step.
    eapply LP; [f_equal; lia | reflexivity | lia | lia | exact E0 | | exact FRM].
    rewrite skipn_O. apply nok_name_ok; [|exact HNN].
    intros E. apply (f_equal (@length Z)) in E. unfold zs in E. rewrite length_map in E. cbn in E. lia.
Qed.

End NameOk.

Theorem name_ok_holds : isalnum_contract -> name_ok_contract.
Proof.
  intros HIS. unfold name_ok_contract, name_ok_pre, NAME_OK_STACK, NAME_OK.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo nm
    (Hs0 & (bs & HB & HZ & HNN) & HA & (ST & HK & H16 & HW) & MI).
  unfold apart in HA. unfold ZERO in HB. subst nm.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. pose proof (bv_unsigned_in_range 64 a0) as Ra0.
  change (bv_modulus 64) with (2^64) in Rsp, Ra0.
  pose proof (proj1 ST) as Hlo.
  assert (HNZ : ~ In (Z_to_bv 8 0) bs) by (apply sq_zs_nul; exact HNN).
  assert (Ly : Z.of_nat (length (zs bs)) = Z.of_nat (length bs)) by (unfold zs; rewrite length_map; reflexivity).
  pose proof (Z_to_bv_bv_unsigned sp) as Esp. pose proof (Z_to_bv_bv_unsigned a0) as Ea0.
  set (Sp := bv_unsigned sp) in *. set (a := bv_unsigned a0) in *.
  rewrite <- Esp, <- Ea0. clearbody Sp a. clear Esp Ea0.
  eapply evt_mono.
  - eapply (body ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m a Sp lo bs);
      first [eassumption | lia].
  - intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
                -> & MU & WM & MI' & ST').
    unfold ret_post. rewrite unsigned_lit by lia.
    exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [exact ST' | exact I].
Qed.
