(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 3817 of its 3853 lines of code are new or changed and 212 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/ctrl_lay_block.v, with its module names changed; 85 of its 151 lines of code are new or changed and 3787 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/reac_box_catalogue_match_lib.v, with its module paths changed; 255 of its 299 lines of code are new or changed and 107 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_pin/lib/Prog/fuzz_catalogue_row.v, with its module paths, module names, addresses and numbers changed; 142 of its 211 lines of code are new or changed and 230 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/U/Prog/reac_segconf_find.v, with its module names, addresses and numbers changed; 471 of its 545 lines of code are new or changed and 137 lines of the source are left out. *)
(** reac_segconf_declared (UBSan build, 0x16210): proof of [reac_segconf_declared_contract]
    (U/Prog/reac_segconf_declared_c.v) from the contracts of its callees reac_declared_vlan_split and
    reac_declared_vlan_add (U/Prog/reac_declared_vlan_split_c.v, U/Prog/reac_declared_vlan_add_c.v). Written new;
    the plain walk is lib/Prog/reac_segconf_declared.v, whose shape this one follows.

    Code (the UBSan binary):
      0x16210-0x1623c  frame of 112: ra s0-s9 at sp+0x68 .. sp+0x18; parent[16] at sp+8, vid at sp+6
      0x16240 beqz a0 -> ZERO; mv s3,a0; 0x1624c andi/bnez -> TRAP (c 8-aligned); s5 = c + 0x2c80;
      0x1625c lw a0,0(s5) (c->n); 0x16260 blez a0 -> ZERO
      mv s0,a3; mv s1,a2; mv s2,a1; s6 = 0 (356 i); s4 = 0 (added); s7 = 0 (i); s8 = ~c; s9 = 32
      LOOP 0x16284 beq s7,s9 -> TRAP (i = 32); 0x16288 bltu s8,s6 -> TRAP (c + 356 i wraps)
           lw a0,0x18(s3) (seg[i].ignore); bnez a0 -> RELOAD
           a1 = sp+8; a2 = 16; a3 = sp+6; a0 = s3; 0x162a4 jal split; beqz a0 -> RELOAD
           0x162ac lhu a4,6(sp); a3 = sp+8; a0 = s2; a1 = s1; a2 = s0; 0x162c0 jal add
           0x162c4 bltz a0 -> FULL; a1 = sext.w s4; s4 = a1 + a0; a0 = addw a1,a0; 0x162d4 bne a0,s4 -> TRAP
      RELOAD 0x162d8 lw a0,0(s5); s7 += 1; s3 += 0x164; s6 += 0x164; 0x162e8 blt s7,a0 -> LOOP; j EPI
      ZERO 0x162f0 s4 = 0.  EPI 0x162f4 a0 = sext.w s4; restore ra s0-s9; ret.  FULL 0x1632c s4 = -1; j EPI
      TRAP 0x16334 unimp.
    The traps are not reached: c mod 16 = 0; i < c->n <= 32 (rconf_enc); c + 16616 <= 2^64 (bytes_at), so
    ~c >= 356 i; added <= i < 32 and add answers 0 or 1 on that path, so added + r is its 32-bit sign extension.
    The loop invariant and the memory argument are the plain walk's ([frm]), with this frame's offsets. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac ZBridge.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec seg_query_facts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import reac_segconf_declared_facts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require Import seg_env.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require Import reac_declared_vlan_split_c reac_declared_vlan_add_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require Import reac_segconf_declared_c.
Import ListNotations.
Open Scope Z_scope.

(** ** Image and word facts *)
Lemma dp_readable : forallb seg_readable rsegs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma dp_sa_low : sa_got_guard SA + 8 <= sa_img_end SA /\ sa_guard SA + 8 <= sa_img_end SA.
Proof. unfold SA, SEG_UBSAN. cbn. lia. Qed.

(** The stack-protector GOT cell and guard lie in reserved segments 2 and 3 of the image. *)
Lemma dp_got_res : exists r, In r (segments_reserved rsegs) /\ bv_unsigned (fst r) <= sa_got_guard SA /\
  sa_got_guard SA + 8 <= bv_unsigned (fst r) + bv_unsigned (snd r).
Proof.
  exists (nth 2 (segments_reserved rsegs) (Z_to_bv 64 0, Z_to_bv 64 0)).
  split; [apply nth_In; apply Nat.ltb_lt; vm_compute; reflexivity|].
  split; apply Z.leb_le; vm_compute; reflexivity.
Qed.

Lemma dp_guard_res : exists r, In r (segments_reserved rsegs) /\ bv_unsigned (fst r) <= sa_guard SA /\
  sa_guard SA + 8 <= bv_unsigned (fst r) + bv_unsigned (snd r).
Proof.
  exists (nth 3 (segments_reserved rsegs) (Z_to_bv 64 0, Z_to_bv 64 0)).
  split; [apply nth_In; apply Nat.ltb_lt; vm_compute; reflexivity|].
  split; apply Z.leb_le; vm_compute; reflexivity.
Qed.

Lemma dp_lts : forall x y, 0 <= x < 2 ^ 63 -> 0 <= y < 2 ^ 63 -> bv_lts (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y).
Proof.
  intros x y Hx Hy. unfold bv_lts. rewrite !zb_signed, !unsigned_lit by lia.
  replace (x <? 2 ^ 63) with true by (symmetry; apply Z.ltb_lt; lia).
  replace (y <? 2 ^ 63) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.

Lemma dp_zx16 : forall v, 0 <= v < 65536 -> zx16 (Z_to_bv 64 v) = Z_to_bv 64 v.
Proof. intros v Hv. unfold zx16. rewrite unsigned_lit by lia. rewrite Z.mod_small by lia. reflexivity. Qed.

(** split copies at most 15 bytes and the NUL. *)
Lemma dp_split_copy_le : forall s di, split_copy s = Some di -> (di + 1 <= 16)%nat.
Proof.
  intros s di. unfold split_copy. destruct (strrchr s DOT) as [d|]; [|discriminate]. cbv zeta.
  repeat match goal with |- context [if ?b then _ else _] => let E := fresh "E" in destruct b eqn:E end;
    intros H; try discriminate H.
  injection H as <-.
  repeat match goal with H : (_ || _)%bool = false |- _ => apply orb_false_iff in H as [? ?] end.
  match goal with H : (16 <? d + 1)%nat = false |- _ => apply Nat.ltb_ge in H end. lia.
Qed.

(** The values the prologue computes and the epilogue's sext.w. *)
Lemma du_andi7 : forall c, 0 <= c < 2^64 -> c mod 16 = 0 -> Z.land (bv_unsigned (Z_to_bv 64 c)) 7 = 0.
Proof.
  intros c Hc H. rewrite unsigned_lit by lia. change 7 with (Z.ones 3).
  rewrite Z.land_ones by lia. change (2 ^ 3) with 8. Z.div_mod_to_equations. lia.
Qed.

Lemma du_not : forall c, 0 <= c < 2^64 ->
  bv_unsigned (Z_to_bv 64 (Z.lxor (bv_unsigned (Z_to_bv 64 c)) 18446744073709551615)) = 18446744073709551615 - c.
Proof.
  intros c Hc. rewrite (unsigned_lit c) by lia. rewrite zb_lxor_ones by lia. apply unsigned_lit. lia.
Qed.

Lemma du_sext : forall r, -1 <= r < 2 ^ 31 -> Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 r) + 0)) = Z_to_bv 64 r.
Proof.
  intros r Hr. destruct (Z.eq_dec r (-1)) as [->|Hn].
  - apply bv_eq. vm_compute. reflexivity.
  - rewrite unsigned_lit by lia. rewrite Z.add_0_r.
    rewrite bv_swrap_small by (change (bv_half_modulus 32) with (2 ^ 31); lia). reflexivity.
Qed.

(** A branch to the trap that the facts in the context say is not taken. *)
Ltac du_ntk := let K := fresh "K" in if_cases K; [exfalso; zify_cond K; Z.div_mod_to_equations; lia | clear K].
(** The registers the overflow check computes, as small integers. *)
Ltac rsimp := repeat rewrite unsigned_lit by lia;
  repeat rewrite bv_swrap_small by (change (bv_half_modulus 32) with (2 ^ 31); lia).

Ltac ua H H' := pose proof H as H'; unfold apart, SEG_C_SIZE, RVLAN_SIZE in H'.
Ltac out_split Hx := repeat match type of Hx with _ /\ _ => let X := fresh "X" in destruct Hx as [X Hx] end.
Ltac weq := rewrite ?unsigned_lit by lia;
  rewrite ?bv_swrap_small by (change (bv_half_modulus 32) with (2 ^ 31); lia); word_eq_tac.

Section Declared.
Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
  (m0 : word -> option byte) (c tab max n Sp lo : Z) (bs free0 : list byte) (rc : rconf)
  (tb : list (list Z * Z)) (ev : word).
Hypothesis HSP : reac_declared_vlan_split_contract.
Hypothesis HAD : reac_declared_vlan_add_contract.
Hypothesis HB0 : bytes_at rsegs m0 c bs.
Hypothesis HE : rconf_enc rc bs.
Hypothesis Hc : 0 < c.
Hypothesis Hc16 : c mod 16 = 0.
Hypothesis Hcb : c + 16616 <= 2 ^ 64.
Hypothesis HcA : apart c SEG_C_SIZE lo Sp.
Hypothesis Ht : 0 < tab.
Hypothesis Ht16 : tab mod 16 = 0.
Hypothesis HRT0 : rtab_at rsegs m0 tab tb.
Hypothesis Hmax : Z.of_nat (length tb) <= max < 2 ^ 31.
Hypothesis HFR0 : rw_cells rsegs m0 (tab + RVLAN_SIZE * Z.of_nat (length tb))
                    [CB (Z.to_nat (RVLAN_SIZE * (max - Z.of_nat (length tb)))) free0].
Hypothesis HtA : apart tab (RVLAN_SIZE * (max + 1)) lo Sp.
Hypothesis Hn : 0 < n.
Hypothesis Hn4 : n mod 4 = 0.
Hypothesis HN0 : rw_cells rsegs m0 n [C4 (Z_to_bv 64 (Z.of_nat (length tb)))].
Hypothesis HnA : apart n 4 lo Sp.
Hypothesis HntA : apart n 4 tab (tab + RVLAN_SIZE * (max + 1)).
Hypothesis HctA : apart c SEG_C_SIZE tab (tab + RVLAN_SIZE * (max + 1)).
Hypothesis HncA : apart n 4 c (c + SEG_C_SIZE).
Hypothesis HEV0 : rw_cells rsegs m0 (bv_unsigned tp - 164) [C4 ev].
Hypothesis HeA : apart (bv_unsigned tp - 164) 4 lo Sp.
Hypothesis HeG : apart (bv_unsigned tp - 164) 4 (sa_guard SA) (sa_guard SA + 8).
Hypothesis HecA : apart (bv_unsigned tp - 164) 4 c (c + SEG_C_SIZE).
Hypothesis HetA : apart (bv_unsigned tp - 164) 4 tab (tab + RVLAN_SIZE * (max + 1)).
Hypothesis HenA : apart (bv_unsigned tp - 164) 4 n (n + 4).
Hypothesis HSSP0 : ssp_ok m0.
Hypothesis HIl : sa_img_end SA <= lo.
Hypothesis HIt : blk_noimg rsegs tab (RVLAN_SIZE * (max + 1)).
Hypothesis HIn : sa_img_end SA <= n.
Hypothesis HK : lo + DECLARED_STACK <= Sp.
Hypothesis HS16 : Sp mod 16 = 0.
Hypothesis HRO : forall a, lo <= a < Sp -> seg_rom rsegs (wa a) = None.
Hypothesis Hlo : 0 <= lo.
Hypothesis HSp : Sp < 2 ^ 64.
Hypothesis Htb : tab < 2 ^ 64.
Hypothesis Hnb : n < 2 ^ 64.

Local Abbreviation Post := (fun ms' : machine_state =>
  exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
    ms' = MS (mkR ra (Z_to_bv 64 Sp) gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (fst (r_declared rc tb max)))
                  a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom rsegs) /\
    munch (declared_W Sp (bv_unsigned tp) tab n tb (snd (r_declared rc tb max))) m0 m' /\ wmono rsegs m0 m' /\
    mem_inv rsegs m' /\ stk rsegs m' lo Sp /\
    rtab_at rsegs m' tab (snd (r_declared rc tb max)) /\
    rw_cells rsegs m' n [C4 (Z_to_bv 64 (Z.of_nat (length (snd (r_declared rc tb max)))))] /\
    rw_cells rsegs m' (bv_unsigned tp - 164) [C4 ev]).

(** The saved registers, sp+0x18 .. sp+0x68. *)
Definition sav : list cell := [C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

(** The state between the prologue and the epilogue with the table ti in memory. *)
Definition frm (m : word -> option byte) (ti : list (list Z * Z)) : Prop :=
  rw_cells rsegs m (Sp + -88) sav /\ wr_at rsegs m (Sp + -112) 24 /\ stk rsegs m lo (Sp + -112) /\
  munch (declared_W Sp (bv_unsigned tp) tab n tb ti) m0 m /\ wmono rsegs m0 m /\ mem_inv rsegs m /\
  rtab_at rsegs m tab ti /\ rw_cells rsegs m n [C4 (Z_to_bv 64 (Z.of_nat (length ti)))] /\
  rw_cells rsegs m (bv_unsigned tp - 164) [C4 ev] /\
  (length tb <= length ti)%nat /\ Z.of_nat (length ti) <= max.

Lemma dp_bl : Z.of_nat (length bs) = 16616.
Proof. exact (proj1 (sq_rconf_len rc bs HE)). Qed.

Lemma dp_nlt : (length (rc_seg rc) <= 32)%nat.
Proof. exact (proj2 (sq_rconf_len rc bs HE)). Qed.

Lemma dp_kk : lo + 544 <= Sp.
Proof. pose proof HK as K. unfold DECLARED_STACK, SPLIT_STACK in K. lia. Qed.

(** The stack bytes [a, a + k) are not image bytes. *)
Lemma dp_rom : forall a k, lo <= a -> a + Z.of_nat k <= Sp ->
  forall i, 0 <= i < Z.of_nat k -> seg_rom rsegs (wa (a + i)) = None.
Proof. intros a k H1 H2 i Hi. apply HRO. lia. Qed.

Lemma got_tab : sa_got_guard SA + 8 <= tab \/ tab + RVLAN_SIZE * (max + 1) <= sa_got_guard SA.
Proof.
  destruct dp_got_res as (r & Hr & H1 & H2).
  eapply (dc_noimg_apart rsegs); [exact HIt | exact Hr | exact H1 | exact H2 | lia | unfold RVLAN_SIZE; lia].
Qed.

Lemma guard_tab : sa_guard SA + 8 <= tab \/ tab + RVLAN_SIZE * (max + 1) <= sa_guard SA.
Proof.
  destruct dp_guard_res as (r & Hr & H1 & H2).
  eapply (dc_noimg_apart rsegs); [exact HIt | exact Hr | exact H1 | exact H2 | lia | unfold RVLAN_SIZE; lia].
Qed.

(** c's block, as the footprint leaves it. *)
Lemma frm_blk : forall m ti, frm m ti -> bytes_at rsegs m c bs.
Proof.
  intros m ti (_ & _ & _ & MU & _ & _ & _ & _ & _ & L1 & L2).
  eapply bytes_at_transport; [exact HB0 | exact MU |]. rewrite dp_bl.
  ua HcA A1. ua HctA A2. ua HncA A3. ua HecA A4. pose proof dp_kk as K.
  unfold declared_W, vtab_W, DECLARED_STACK, SPLIT_STACK, RVLAN_SIZE.
  destruct (length tb <? length ti)%nat; cbn [app disjoint_from]; repeat split; lia.
Qed.

(** The stack-protector cells: the footprint misses them but for the errno cell, which holds ev again. *)
Lemma frm_ssp : forall m ti, frm m ti -> ssp_ok m.
Proof.
  intros m ti (_ & _ & _ & MU & _ & _ & _ & _ & EC & L1 & L2).
  pose proof HSSP0 as [G1 [g G2]].
  pose proof (dc_c4_bytes rsegs _ _ _ HEV0) as E0. pose proof (dc_c4_bytes rsegs _ _ _ EC) as E1.
  unfold declared_W in MU. pose proof got_tab as T1. pose proof guard_tab as T2. pose proof dp_sa_low as SL.
  pose proof dp_kk as K. unfold RVLAN_SIZE in T1, T2.
  split; [|exists g].
  - refine (dc_bat_keep rsegs _ [] _ 4 (le4 ev) m0 m _ _ G1 MU E0 E1 _ _); [rewrite length_le4; reflexivity|].
    rewrite app_nil_r, length_le8. unfold vtab_W, DECLARED_STACK, SPLIT_STACK, RVLAN_SIZE.
    destruct (length tb <? length ti)%nat; cbn [app disjoint_from]; repeat split; lia.
  - refine (dc_bat_keep rsegs _ [] _ 4 (le4 ev) m0 m _ _ G2 MU E0 E1 _ _); [rewrite length_le4; reflexivity|].
    rewrite app_nil_r, length_le8. unfold vtab_W, DECLARED_STACK, SPLIT_STACK, RVLAN_SIZE.
    destruct (length tb <? length ti)%nat; cbn [app disjoint_from]; repeat split; lia.
Qed.

(** The free entries of the table ti: the caller's, past the entries appended so far. *)
Lemma frm_free : forall m ti, frm m ti -> exists free, rw_cells rsegs m (tab + RVLAN_SIZE * Z.of_nat (length ti))
  [CB (Z.to_nat (RVLAN_SIZE * (max - Z.of_nat (length ti)))) free].
Proof.
  intros m ti (_ & _ & _ & MU & WM & _ & _ & _ & _ & L1 & L2).
  pose proof (dc_rwc_bytes rsegs _ _ _ HFR0) as FB. cbn [cells_bytes cbytes] in FB. rewrite app_nil_r in FB.
  pose proof (dc_rwc_wr rsegs _ _ _ HFR0) as FW. cbn [cells_size csize] in FW. rewrite Nat.add_0_r in FW.
  pose proof HFR0 as [[[FL _] _] _]. cbn [cell_wf] in FL. unfold RVLAN_SIZE in *.
  exists (firstn (Z.to_nat (18 * (max - Z.of_nat (length ti)))) (skipn (18 * (length ti - length tb)) free0)).
  assert (Lk : (18 * (length ti - length tb) + Z.to_nat (18 * (max - Z.of_nat (length ti))) <= length free0)%nat)
    by (rewrite FL; lia).
  split; [split|].
  - cbn [cells_wf cell_wf]. split; [rewrite length_firstn, length_skipn; lia | exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r.
    pose proof (sq_bytes_at_sub rsegs m0 _ free0 _ _ FB Lk) as S.
    replace (tab + 18 * Z.of_nat (length tb) + Z.of_nat (18 * (length ti - length tb)))
      with (tab + 18 * Z.of_nat (length ti)) in S by lia.
    eapply bytes_at_transport; [exact S | exact MU |]. rewrite length_firstn, length_skipn.
    ua HtA A1. ua HntA A2. ua HetA A3. pose proof dp_kk as K.
    unfold declared_W, vtab_W, DECLARED_STACK, SPLIT_STACK, RVLAN_SIZE.
    destruct (length tb <? length ti)%nat; cbn [app disjoint_from]; repeat split; lia.
  - cbn [cells_size csize]. rewrite Nat.add_0_r. apply (wr_at_transport rsegs m0 m); [|exact WM].
    replace (tab + 18 * Z.of_nat (length ti))
      with (tab + 18 * Z.of_nat (length tb) + 18 * (Z.of_nat (length ti) - Z.of_nat (length tb))) by lia.
    apply (dc_wr_sub rsegs m0 _ _ _ _ FW); lia.
Qed.

(** After split: its footprint is the frames below sp - 112, the errno cell (which it leaves holding ev), and
    parent and vid in this frame. *)
Lemma frm_split : forall m m1 ti s sp' par vd, frm m ti ->
  munch (split_W sp' (bv_unsigned tp) par vd s) m m1 -> wmono rsegs m m1 -> mem_inv rsegs m1 ->
  stk rsegs m1 lo sp' -> rw_cells rsegs m1 (bv_unsigned tp - 164) [C4 ev] ->
  sp' = Sp - 112 -> par = Sp - 104 -> vd = Sp - 106 -> frm m1 ti.
Proof.
  intros m m1 ti s sp' par vd (SV & JW & ST & MU & WM & MI & RT & NC & EC & L1 & L2) MU1 WM1 MI1 ST1 EC1 -> -> ->.
  pose proof dp_kk as K. ua HeA AE.
  refine (conj _ (conj (wr_at_transport rsegs m m1 _ _ JW WM1) (conj _ (conj _ (conj (wmono_trans rsegs m0 m m1 WM WM1)
    (conj MI1 (conj _ (conj _ (conj EC1 (conj L1 L2)))))))))).
  - eapply rw_cells_transport; [exact SV | exact MU1 | exact WM1 |].
    unfold sav. cbn [cells_size csize Nat.add]. unfold split_W, SPLIT_STACK.
    destruct (split_copy s) as [di|] eqn:SC; [pose proof (dp_split_copy_le s di SC)|];
      destruct (vlan_split s) as [[p v]|]; cbn [app disjoint_from]; repeat split; lia.
  - replace (Sp + -112) with (Sp - 112) by lia. exact ST1.
  - eapply munch_trans; [exact MU|]. eapply munch_weaken; [|exact MU1].
    intros x Hx. revert Hx. unfold declared_W, vtab_W, split_W, DECLARED_STACK, SPLIT_STACK, RVLAN_SIZE.
    destruct (length tb <? length ti)%nat;
      destruct (split_copy s) as [di|] eqn:SC; [pose proof (dp_split_copy_le s di SC)| | pose proof (dp_split_copy_le s di SC)|];
      destruct (vlan_split s) as [[p v]|]; intros Hx; cbn [app outside] in Hx |- *; out_split Hx; repeat split; lia.
  - destruct RT as (bt & BT & ET). exists bt. split; [|exact ET].
    eapply bytes_at_transport; [exact BT | exact MU1 |]. rewrite (proj1 ET).
    ua HtA AT. ua HetA AET.
    unfold split_W, SPLIT_STACK.
    destruct (split_copy s) as [di|] eqn:SC; [pose proof (dp_split_copy_le s di SC)|];
      destruct (vlan_split s) as [[p v]|]; cbn [app disjoint_from]; repeat split; lia.
  - eapply rw_cells_transport; [exact NC | exact MU1 | exact WM1 |]. cbn [cells_size csize Nat.add].
    ua HnA AN. ua HenA AEN.
    unfold split_W, SPLIT_STACK.
    destruct (split_copy s) as [di|] eqn:SC; [pose proof (dp_split_copy_le s di SC)|];
      destruct (vlan_split s) as [[p v]|]; cbn [app disjoint_from]; repeat split; lia.
Qed.

(** After add: its footprint is its frames below sp - 112, the entry it appends and *n when it appends. *)
Lemma frm_add : forall m1 m2 ti ti' sp' a0' a2', frm m1 ti ->
  munch (vtab_W ADD_STACK sp' a0' a2' ti ti') m1 m2 -> wmono rsegs m1 m2 -> mem_inv rsegs m2 -> stk rsegs m2 lo sp' ->
  rtab_at rsegs m2 a0' ti' -> rw_cells rsegs m2 a2' [C4 (Z_to_bv 64 (Z.of_nat (length ti')))] ->
  (length ti <= length ti')%nat -> Z.of_nat (length ti') <= max ->
  sp' = Sp - 112 -> a0' = tab -> a2' = n -> frm m2 ti'.
Proof.
  intros m1 m2 ti ti' sp' a0' a2' (SV & JW & ST & MU & WM & MI & RT & NC & EC & L1 & L2) MU2 WM2 MI2 ST2 RT2 NC2
    M1 M2 -> -> ->.
  pose proof dp_kk as K. ua HtA AT. ua HnA AN. ua HntA ANT.
  refine (conj _ (conj (wr_at_transport rsegs m1 m2 _ _ JW WM2) (conj _ (conj _ (conj (wmono_trans rsegs m0 m1 m2 WM WM2)
    (conj MI2 (conj RT2 (conj NC2 (conj _ (conj _ M2)))))))))).
  - eapply rw_cells_transport; [exact SV | exact MU2 | exact WM2 |].
    unfold sav. cbn [cells_size csize Nat.add]. unfold vtab_W, ADD_STACK, RVLAN_SIZE.
    destruct (length ti <? length ti')%nat; cbn [app disjoint_from]; repeat split; lia.
  - replace (Sp + -112) with (Sp - 112) by lia. exact ST2.
  - eapply munch_trans; [eapply munch_weaken; [|exact MU] | eapply munch_weaken; [|exact MU2]].
    + intros x Hx. revert Hx. unfold declared_W, vtab_W, DECLARED_STACK, SPLIT_STACK, RVLAN_SIZE.
      destruct (Nat.ltb_spec (length tb) (length ti)); destruct (Nat.ltb_spec (length tb) (length ti'));
        intros Hx; cbn [app outside] in Hx |- *; out_split Hx; repeat split; lia.
    + intros x Hx. revert Hx. unfold declared_W, vtab_W, ADD_STACK, DECLARED_STACK, SPLIT_STACK, RVLAN_SIZE.
      destruct (Nat.ltb_spec (length ti) (length ti')); destruct (Nat.ltb_spec (length tb) (length ti'));
        intros Hx; cbn [app outside] in Hx |- *; out_split Hx; repeat split; lia.
  - eapply rw_cells_transport; [exact EC | exact MU2 | exact WM2 |]. cbn [cells_size csize Nat.add].
    ua HeA AE. ua HetA AET. ua HenA AEN.
    unfold vtab_W, ADD_STACK, RVLAN_SIZE.
    destruct (length ti <? length ti')%nat; cbn [app disjoint_from]; repeat split; lia.
  - lia.
Qed.

(** split's premise at 0x162a4: segment = &c->seg[i].name, parent and vid in this frame. *)
Lemma split_pre_ok : forall m ti i sp' seg par cap vd, frm m ti -> (i < length (rc_seg rc))%nat ->
  sp' = Sp - 112 -> seg = c + 356 * Z.of_nat i -> par = Sp - 104 -> cap = 16 -> vd = Sp - 106 ->
  split_pre m sp' lo (bv_unsigned tp) seg par cap vd (rs_name (r_seg rc i)) ev.
Proof.
  intros m ti i sp' seg par cap vd FRM Hi -> -> -> -> ->.
  pose proof (frm_blk m ti FRM) as HBm. pose proof (frm_ssp m ti FRM) as SS.
  destruct FRM as (SV & JW & ST & MU & WM & MI & RT & NC & EC & L1 & L2).
  pose proof dp_nlt as NL. pose proof dp_bl as BL. pose proof dp_kk as K.
  destruct (sq_seg_name rsegs m c bs rc i HBm HE Hi) as (sx & HX & HXZ & HXN & HSN).
  destruct (sq_rseg rc bs i HE Hi) as (_ & (_ & Hlt & _) & _).
  assert (Lx : length sx = length (rs_name (r_seg rc i))) by (rewrite <- HXN; unfold zs; symmetry; apply length_map).
  pose proof (sq_bytes_at_sub rsegs m c bs (356 * i + length (rs_name (r_seg rc i)) + 1) 7 HBm ltac:(lia)) as SL.
  assert (CS : cstr_at rsegs m (c + 356 * Z.of_nat i) (rs_name (r_seg rc i))).
  { apply (dc_cstr_of_cstrz rsegs m _ _ (firstn 7 (skipn (356 * i + length (rs_name (r_seg rc i)) + 1) bs))).
    - exists sx. split; [exact HX | split; [exact HXN | exact HSN]].
    - replace (c + 356 * Z.of_nat i + Z.of_nat (length (rs_name (r_seg rc i))) + 1)
        with (c + Z.of_nat (356 * i + length (rs_name (r_seg rc i)) + 1)) by lia. exact SL.
    - rewrite length_firstn, length_skipn.
      pose proof (Z.mod_pos_bound (- (c + 356 * Z.of_nat i + Z.of_nat (length (rs_name (r_seg rc i))) + 1)) 8
        ltac:(lia)). lia. }
  assert (JWp : wr_at rsegs m (Sp - 104) (Z.of_nat 16)).
  { replace (Sp - 104) with (Sp + -112 + 8) by lia. apply (dc_wr_sub rsegs m _ 24 8 16 JW); lia. }
  assert (JWv : wr_at rsegs m (Sp - 106) 2).
  { replace (Sp - 106) with (Sp + -112 + 6) by lia. apply (dc_wr_sub rsegs m _ 24 6 2 JW); lia. }
  destruct (dc_rwc_of_wr rsegs m (Sp - 104) 16 dp_readable (dp_rom (Sp - 104) 16 ltac:(lia) ltac:(lia)) JWp)
    as [pb PB].
  ua HcA AC. ua HeA AE. ua HecA AEC. ua HeG AG.
  unfold split_pre, errno_ok, stack_ok, apart, SPLIT_STACK.
  split; [lia|]. split; [exact CS|]. split; [exact Hlt|]. split; [lia|]. split; [lia|].
  split; [lia|]. split; [reflexivity|]. split; [exists pb; exact PB|]. split; [lia|]. split; [lia|].
  split; [lia|]. split; [Z.div_mod_to_equations; lia|]. split; [exact JWv|]. split; [lia|]. split; [lia|].
  split; [split; [exact EC | split; [lia | exact AG]]|].
  split; [lia|]. split; [lia|]. split; [lia|]. split; [exact SS|]. split; [exact HIl|].
  split; [|exact MI].
  split; [replace (Sp - 112) with (Sp + -112) by lia; exact ST|].
  split; [lia|]. split; [Z.div_mod_to_equations; lia|]. intros a Ha. apply HRO. lia.
Qed.

(** add's premise at 0x162c0: the table ti, parent the C string p split left, its slack from this frame. *)
Lemma add_pre_ok : forall m1 ti p v sp' a0' a1' a2' par vd pp, frm m1 ti -> cstrz_at rsegs m1 pp p ->
  (length p <= 15)%nat -> 0 <= v < 65536 -> pp = Sp - 104 -> sp' = Sp - 112 -> a0' = tab -> a1' = max -> a2' = n ->
  par = Sp - 104 -> vd = v -> add_pre m1 sp' lo a0' a1' a2' par vd ti p.
Proof.
  intros m1 ti p v sp' a0' a1' a2' par vd pp FRM CZ Lp Hv -> -> -> -> -> -> ->.
  destruct (frm_free m1 ti FRM) as [fr FR].
  destruct FRM as (SV & JW & ST & MU & WM & MI & RT & NC & EC & L1 & L2).
  pose proof dp_kk as K.
  assert (JWs : wr_at rsegs m1 (Sp - 104 + Z.of_nat (length p) + 1) (Z.of_nat (15 - length p))).
  { replace (Sp - 104 + Z.of_nat (length p) + 1) with (Sp + -112 + (9 + Z.of_nat (length p))) by lia.
    apply (dc_wr_sub rsegs m1 _ 24 _ _ JW); lia. }
  destruct (dc_bytes_of_wr rsegs m1 (15 - length p) _ dp_readable
    (dp_rom (Sp - 104 + Z.of_nat (length p) + 1) (15 - length p) ltac:(lia) ltac:(lia)) JWs) as (sl & Lsl & SL).
  assert (CS : cstr_at rsegs m1 (Sp - 104) p).
  { apply (dc_cstr_of_cstrz rsegs m1 _ p sl CZ SL). rewrite Lsl. Z.div_mod_to_equations. lia. }
  ua HtA AT. ua HnA AN. ua HntA ANT.
  unfold add_pre, vtab_pre, stack_ok, apart, ADD_STACK, RVLAN_SIZE.
  split.
  { split; [lia|]. split; [exact Ht16|]. split; [exact RT|]. split; [lia|]. split; [exists fr; exact FR|].
    split; [lia|]. split; [lia|]. split; [exact Hn4|]. split; [exact NC|]. split; [lia | exact ANT]. }
  split; [lia|]. split; [exact CS|]. split; [lia|]. split; [lia|]. split; [lia|].
  split; [|exact MI].
  split; [replace (Sp - 112) with (Sp + -112) by lia; exact ST|].
  split; [lia|]. split; [Z.div_mod_to_equations; lia|]. intros a Ha. apply HRO. lia.
Qed.

(** The exit 0x162f4: a0 = sext.w s4, restore ra and s0-s9, return. *)
Lemma epi : forall r ti m (x1 y0 y1 y2 w8 w9 w10 z1 z2 z3 z4 z5 z6 z7 w18 w19 w21 w22 w23 w24 w25 u3 u4 u5 u6 w20
    : word),
  w20 = Z_to_bv 64 r -> -1 <= r < 2 ^ 31 -> r = fst (r_declared rc tb max) -> ti = snd (r_declared rc tb max) ->
  frm m ti ->
  evt rsegs Post
    (MS (mkR x1 (Z_to_bv 64 (Sp + -112)) gp tp y0 y1 y2 w8 w9 w10 z1 z2 z3 z4 z5 z6 z7 w18 w19 w20 w21 w22
             w23 w24 w25 s10 s11 u3 u4 u5 u6)
        F (Z_to_bv 64 0x162f4) fc None m (seg_rom rsegs)).
Proof.
  intros r ti m x1 y0 y1 y2 w8 w9 w10 z1 z2 z3 z4 z5 z6 z7 w18 w19 w21 w22 w23 w24 w25 u3 u4 u5 u6 w20 -> Hr Er Et
    (SV & JW & ST & MU & WM & MI & RT & NC & EC & L1 & L2).
  pose proof dp_kk as K.
  destruct (dc_rwc_of_wr rsegs m (Sp + -112) 24 dp_readable (dp_rom (Sp + -112) 24 ltac:(lia) ltac:(lia)) JW)
    as [j FJ].
  assert (FR : rw_cells rsegs m (Sp + -112) (CB 24 j :: sav)).
  { apply (dc_rwc_app rsegs m (Sp + -112) [CB 24 j] sav FJ). cbn [cells_size csize Nat.add].
    replace (Sp + -112 + Z.of_nat 24) with (Sp + -88) by lia. exact SV. }
  unfold sav in FR. clear SV JW FJ.
  step. rewrite ?du_sext by lia.
  do 13 step.
  apply evt_done. exists y0, y1, y2, z1, z2, z3, z4, z5, z6, z7, u3, u4, u5, u6, m.
  split; [subst r; unfold mkR; repeat f_equal; lia|].
  subst ti. split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
  split; [|split; [exact RT | split; [exact NC | exact EC]]].
  pose proof (stk_release rsegs m lo (Sp + -112) _ ST FR ltac:(lia)) as R. cbn [cells_size csize Nat.add] in R.
  replace (Sp + -112 + Z.of_nat 112) with Sp in R by lia. exact R.
Qed.

(** The loop head 0x16284 with i entries done and j left: s3 = &c->seg[i], s4 = added, s6 = 356 i, s7 = i,
    s8 = ~c, s9 = 32. *)
Lemma loop : forall j i ti added m (x1 y0 y1 y2 w10 z1 z2 z3 z4 z5 z6 z7 u3 u4 u5 u6 w19 w20 w21 w22 w23 w24 w25
    : word),
  (i + j = length (rc_seg rc))%nat -> (0 < j)%nat ->
  w19 = Z_to_bv 64 (c + 356 * Z.of_nat i) -> w20 = Z_to_bv 64 added -> w21 = Z_to_bv 64 (c + 11392) ->
  w22 = Z_to_bv 64 (356 * Z.of_nat i) -> w23 = Z_to_bv 64 (Z.of_nat i) ->
  bv_unsigned w24 = 18446744073709551615 - c -> w25 = Z_to_bv 64 32 ->
  0 <= added <= Z.of_nat i -> r_decl_go (skipn i (rc_seg rc)) ti max added = r_declared rc tb max -> frm m ti ->
  evt rsegs Post
    (MS (mkR x1 (Z_to_bv 64 (Sp + -112)) gp tp y0 y1 y2 (Z_to_bv 64 n) (Z_to_bv 64 max) w10 z1 z2 z3 z4 z5 z6 z7
             (Z_to_bv 64 tab) w19 w20 w21 w22 w23 w24 w25 s10 s11 u3 u4 u5 u6)
        F (Z_to_bv 64 0x16284) fc None m (seg_rom rsegs)).
Proof.
  induction j as [|j IH];
    intros i ti added m x1 y0 y1 y2 w10 z1 z2 z3 z4 z5 z6 z7 u3 u4 u5 u6 w19 w20 w21 w22 w23 w24 w25 Hij Hj E19 E20
      E21 E22 E23 E24 E25 Had RG FRM; [lia|].
  subst w19 w20 w21 w22 w23 w25. pose proof dp_nlt as NL. pose proof dp_kk as K.
  assert (Hi : (i < length (rc_seg rc))%nat) by lia.
  (* RELOAD 0x162d8: i done *)
  assert (NEXT : forall ti' added' m' (x1' y0' y1' y2' w10' z1' z2' z3' z4' z5' z6' z7' u3' u4' u5' u6' w20' : word),
    w20' = Z_to_bv 64 added' -> 0 <= added' <= Z.of_nat (S i) ->
    r_decl_go (skipn (S i) (rc_seg rc)) ti' max added' = r_declared rc tb max -> frm m' ti' ->
    evt rsegs Post
      (MS (mkR x1' (Z_to_bv 64 (Sp + -112)) gp tp y0' y1' y2' (Z_to_bv 64 n) (Z_to_bv 64 max) w10'
               z1' z2' z3' z4' z5' z6' z7' (Z_to_bv 64 tab)
               (Z_to_bv 64 (c + 356 * Z.of_nat i)) w20' (Z_to_bv 64 (c + 11392)) (Z_to_bv 64 (356 * Z.of_nat i))
               (Z_to_bv 64 (Z.of_nat i)) w24 (Z_to_bv 64 32) s10 s11 u3' u4' u5' u6')
          F (Z_to_bv 64 0x162d8) fc None m' (seg_rom rsegs))).
  { intros ti' added' m' x1' y0' y1' y2' w10' z1' z2' z3' z4' z5' z6' z7' u3' u4' u5' u6' w20' -> Ha' RG' FRM'.
    pose proof (sq_rc_n rsegs m' c bs rc (frm_blk m' ti' FRM') HE) as RN. unfold RC_N in RN.
    step. rewrite ?sq_sx32 by lia.
    step. step. step. step.
    rewrite dp_lts by lia.
    match goal with |- context [if (?x <? ?y) then _ else _] => destruct (Z.ltb_spec x y) as [LT|GE] end;
      cbv iota.
    - eapply (IH (S i)); [lia | lia | weq | reflexivity | reflexivity | weq | weq | exact E24 | reflexivity | lia
                         | exact RG' | exact FRM'].
    - step.
      assert (Es : S i = length (rc_seg rc)) by lia. rewrite Es, dc_go_end in RG'.
      eapply epi; [reflexivity | lia | rewrite <- RG'; reflexivity | rewrite <- RG'; reflexivity | exact FRM']. }
  (* the two UBSan checks at the head: i = 32 and c + 356 i wrapping *)
  step. du_ntk.
  step. du_ntk.
  pose proof (frm_blk m ti FRM) as HBm.
  pose proof (sq_ignore rsegs m c bs rc i HBm HE Hi) as RI. unfold RS_IGNORE in RI. clear HBm.
  revert RI. destruct (rs_ignore (r_seg rc i)) eqn:IG; intros RI; cbn [b2z] in RI.
  - (* seg[i].ignore: skip it *)
    rewrite (dc_go_ignore _ i ti max added Hi IG) in RG.
    step. rewrite ?sq_sx32 by lia. step. if_true.
    eapply NEXT; [reflexivity | lia | exact RG | exact FRM].
  - step. rewrite ?sq_sx32 by lia. step. if_false.
    do 5 step.
    eapply evt_cut.
    { eapply HSP with (s := rs_name (r_seg rc i)) (ev := ev) (lo := lo).
      eapply split_pre_ok; [exact FRM | exact Hi | ..]; rewrite ?unsigned_lit by lia; lia. }
    intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 &
                -> & MU1 & WM1 & MI1 & ST1 & EC1 & Q1).
    rewrite ret_pc_even by (try lia; reflexivity).
    repeat rewrite unsigned_lit in MU1 by lia. repeat rewrite unsigned_lit in ST1 by lia.
    repeat rewrite unsigned_lit in Q1 by lia.
    assert (FRM1 : frm m1 ti).
    { eapply (frm_split m m1 ti _ _ _ _ FRM MU1 WM1 MI1 ST1 EC1); lia. }
    clear RI MU1 ST1 EC1.
    destruct (vlan_split (rs_name (r_seg rc i))) as [[p v]|] eqn:VS; try rewrite VS in Q1.
    + (* split answered 1: add (p, v) *)
      destruct Q1 as [CZ VB].
      pose proof (dc_read_all rsegs m1 _ _ VB) as RV. rewrite length_le2 in RV.
      destruct (dc_split_some _ p v VS) as [Hv Lp].
      step. if_false.
      step. rewrite ?dp_zx16 by lia.
      do 5 step.
      eapply evt_cut.
      { eapply HAD with (t := ti) (p := p) (lo := lo).
        eapply add_pre_ok; [exact FRM1 | exact CZ | exact Lp | exact Hv | ..]; rewrite ?unsigned_lit by lia; lia. }
      intros ms' (t0'' & t1'' & t2'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' &
                  m2 & -> & MU2 & WM2 & MI2 & ST2 & RT2 & NC2).
      rewrite ret_pc_even by (try lia; reflexivity).
      repeat rewrite unsigned_lit in MU2 by lia. repeat rewrite unsigned_lit in ST2 by lia.
      repeat rewrite unsigned_lit in RT2 by lia. repeat rewrite unsigned_lit in NC2 by lia.
      repeat rewrite unsigned_lit by lia.
      pose proof FRM1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & L2).
      destruct (vlan_add_len ti max p v L2) as [VL1 VL2].
      assert (FRM2 : frm m2 (snd (vlan_add ti max p v))).
      { eapply (frm_add m1 m2 ti _ _ _ _ FRM1 MU2 WM2 MI2 ST2 RT2 NC2 VL1 VL2); lia. }
      clear MU2 ST2 RT2 NC2 RV.
      rewrite (dc_go_split _ i ti max added p v Hi IG VS) in RG.
      destruct (dc_add_rv ti max p v) as [R|[R|R]]; rewrite R in RG |- *.
      * (* duplicate: 0; the overflow check added + 0 falls through *)
        replace (0 <? 0) with false in RG by reflexivity. cbv iota in RG.
        step. if_false.
        step. rsimp. step. rsimp. step. rsimp.
        step. rewrite ?sq_eqb_lit by lia. if_false.
        eapply NEXT with (added' := added + 0); [weq | lia | exact RG | exact FRM2].
      * (* appended: 1; the overflow check added + 1 falls through (added <= i < 32) *)
        replace (1 <? 0) with false in RG by reflexivity. cbv iota in RG.
        step. if_false.
        step. rsimp. step. rsimp. step. rsimp.
        step. rewrite ?sq_eqb_lit by lia. if_false.
        eapply NEXT with (added' := added + 1); [weq | lia | exact RG | exact FRM2].
      * (* full: -1 *)
        replace (-1 <? 0) with true in RG by reflexivity. cbv iota in RG.
        step. if_true. step. step.
        eapply epi with (r := -1) (ti := snd (vlan_add ti max p v));
          [weq | lia | rewrite <- RG; reflexivity | rewrite <- RG; reflexivity | exact FRM2].
    + (* split answered 0 *)
      rewrite (dc_go_nosplit _ i ti max added Hi IG VS) in RG.
      step. if_true.
      eapply NEXT; [reflexivity | lia | exact RG | exact FRM1].
Qed.

(** The memory the prologue leaves: c's block and the loop's frame. *)
Lemma blk_entry : forall m, munch [(Sp + -112, Sp)] m0 m -> bytes_at rsegs m c bs.
Proof.
  intros m MU. eapply bytes_at_transport; [exact HB0 | exact MU |]. rewrite dp_bl.
  ua HcA A1. pose proof dp_kk as K. cbn [disjoint_from]. split; [lia | exact I].
Qed.

Lemma frm_entry : forall m j, rw_cells rsegs m (Sp + -112) [CB 24 j; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  stk rsegs m lo (Sp + -112) -> munch [(Sp + -112, Sp)] m0 m -> wmono rsegs m0 m -> mem_inv rsegs m -> frm m tb.
Proof.
  intros m j FR ST MU WM MI. pose proof dp_kk as K.
  destruct (dc_rwc_split rsegs m (Sp + -112) [CB 24 j] sav FR) as [FJ SV].
  cbn [cells_size csize Nat.add] in SV. replace (Sp + -112 + Z.of_nat 24) with (Sp + -88) in SV by lia.
  pose proof (dc_rwc_wr rsegs _ _ _ FJ) as JW. cbn [cells_size csize Nat.add] in JW.
  assert (MUd : munch (declared_W Sp (bv_unsigned tp) tab n tb tb) m0 m).
  { eapply munch_weaken; [|exact MU]. intros x Hx. unfold declared_W, vtab_W, DECLARED_STACK, SPLIT_STACK in Hx.
    rewrite Nat.ltb_irrefl in Hx. cbn [app outside] in Hx |- *. out_split Hx. split; [lia | exact I]. }
  ua HtA AT. ua HnA AN. ua HeA AE.
  refine (conj SV (conj JW (conj ST (conj MUd (conj WM (conj MI (conj _ (conj _ (conj _ (conj (le_n _) _)))))))))).
  - destruct HRT0 as (bt & BT & ET). exists bt. split; [|exact ET].
    eapply bytes_at_transport; [exact BT | exact MU |]. rewrite (proj1 ET). cbn [disjoint_from].
    split; [lia | exact I].
  - eapply rw_cells_transport; [exact HN0 | exact MU | exact WM |]. cbn [cells_size csize Nat.add disjoint_from].
    split; [lia | exact I].
  - eapply rw_cells_transport; [exact HEV0 | exact MU | exact WM |]. cbn [cells_size csize Nat.add disjoint_from].
    split; [lia | exact I].
  - lia.
Qed.

(** The whole function from its entry. *)
Lemma body : forall (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word),
  stk rsegs m0 lo Sp -> mem_inv rsegs m0 ->
  evt rsegs Post
    (MS (mkR ra (Z_to_bv 64 Sp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 c) (Z_to_bv 64 tab) (Z_to_bv 64 max) (Z_to_bv 64 n)
             a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16210) fc None m0 (seg_rom rsegs)).
Proof.
  intros t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 ST MI.
  (* The prologue's stores transport (and so replace) the section hypotheses the later lemmas use: take them
     first. *)
  pose proof (loop (length (rc_seg rc)) 0 tb 0) as LP. pose proof epi as EP. pose proof frm_entry as FE.
  pose proof blk_entry as BE. pose proof dp_nlt as NL. pose proof dp_kk as K.
  pose proof (munch_refl [(Sp + -112, Sp)] m0) as MU. pose proof (wmono_refl rsegs m0) as WM.
  clear HB0 HRT0 HFR0 HN0 HEV0 HSSP0.
  destruct (stk_carve rsegs m0 lo Sp 112 ST ltac:(lia)) as [ST1 [junk FR]]. clear ST.
  change (Z.of_nat 112) with 112 in ST1, FR.
  replace (Sp - 112) with (Sp + -112) in ST1, FR by lia.
  do 12 step.
  step. rewrite sq_eqb_lit by lia. replace (c =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbv iota.
  step. step. rewrite du_andi7 by lia.
  step. rewrite sq_eqb_lit by lia. rewrite Z.eqb_refl. cbn [negb]. cbv iota.
  do 3 step.
  pose proof (BE _ MU) as HBm. pose proof (sq_rc_n rsegs _ c bs rc HBm HE) as RN. unfold RC_N in RN. clear HBm.
  step. rewrite sq_sx32 by lia.
  step.
  rewrite bv_lts_zero_l, unsigned_lit by lia.
  replace (Z.of_nat (length (rc_seg rc)) <? 2^63) with true by (symmetry; apply Z.ltb_lt; lia).
  rewrite andb_true_r.
  destruct (Z.ltb_spec 0 (Z.of_nat (length (rc_seg rc)))) as [P|P]; cbn [negb]; cbv iota.
  - do 8 step.
    eapply LP; [lia | lia | weq | weq | weq | weq | weq | apply du_not; lia | weq | lia | reflexivity |].
    eapply FE; eassumption.
  - step.
    assert (S0 : rc_seg rc = []) by (destruct (rc_seg rc); [reflexivity | cbn [length] in P; lia]).
    eapply EP with (r := 0) (ti := tb); [weq | lia | unfold r_declared; rewrite S0; reflexivity
                                        | unfold r_declared; rewrite S0; reflexivity |].
    eapply FE; eassumption.
Qed.

End Declared.

Theorem reac_segconf_declared_holds :
  reac_declared_vlan_split_contract -> reac_declared_vlan_add_contract -> reac_segconf_declared_contract.
Proof.
  intros HSP HAD. unfold reac_segconf_declared_contract, declared_pre, REAC_SEGCONF_DECLARED.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo rc tb ev
    (Hc0 & Hc16 & (bs & HB & HE) & HcA & (Ht0 & Ht16 & HRT & Hmax & (free & HFR) & HtA & Hn0 & Hn4 & HN & HnA & HntA) &
     HctA & HncA & (HEV & HeA & HeG) & HecA & HetA & HenA & HSSP & HIl & HIt & HIn & (ST & HK & H16 & HRO) & MI).
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. pose proof (bv_unsigned_in_range 64 a0) as Ra0.
  pose proof (bv_unsigned_in_range 64 a1) as Ra1. pose proof (bv_unsigned_in_range 64 a2) as Ra2.
  pose proof (bv_unsigned_in_range 64 a3) as Ra3.
  change (bv_modulus 64) with (2^64) in Rsp, Ra0, Ra1, Ra2, Ra3.
  destruct (sq_rconf_len rc bs HE) as [HL _].
  pose proof (bytes_at_bound _ _ _ _ HB) as Bc.
  pose proof (proj1 ST) as Hlo.
  pose proof (Z_to_bv_bv_unsigned sp) as Esp. pose proof (Z_to_bv_bv_unsigned a0) as Ea0.
  pose proof (Z_to_bv_bv_unsigned a1) as Ea1. pose proof (Z_to_bv_bv_unsigned a2) as Ea2.
  pose proof (Z_to_bv_bv_unsigned a3) as Ea3.
  set (Sp := bv_unsigned sp) in *. set (c := bv_unsigned a0) in *. set (tab := bv_unsigned a1) in *.
  set (max := bv_unsigned a2) in *. set (n := bv_unsigned a3) in *.
  rewrite <- Esp, <- Ea0, <- Ea1, <- Ea2, <- Ea3. clearbody Sp c tab max n. clear Esp Ea0 Ea1 Ea2 Ea3.
  eapply evt_mono.
  - eapply (body ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m c tab max n Sp lo bs free rc tb ev);
      first [eassumption | lia].
  - intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
                -> & MU & WM & MI' & ST' & RT' & NC' & EC').
    unfold ret_post. rewrite !unsigned_lit by lia.
    exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [exact ST'|].
    split; [exact RT' | split; [exact NC' | exact EC']].
Qed.
