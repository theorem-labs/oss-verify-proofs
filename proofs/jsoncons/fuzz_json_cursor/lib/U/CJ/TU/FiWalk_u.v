(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib Require Import Tac ZBridge FP.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Bridge Require Import BrMem.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.TUB Require Import DgWalkB_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.TU Require Import G3Lem_u PbWalk_u.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition FM1 : Z := 0xCCCCCCCCCCCCCCCD.
Definition FM2 : Z := 0x6666666666666667.
Lemma mulhu10 : forall x, (0 <= x < 2 ^ 64)%Z -> (((x * (FM1 mod 18446744073709551616)) ≫ 64 mod 18446744073709551616) ≫ 3 = x / 10)%Z.
Proof.
  intros x Hx. unfold FM1. rewrite (Z.mod_small 0xCCCCCCCCCCCCCCCD) by lia.
  rewrite !Z.shiftr_div_pow2 by lia.
  assert (Hq : (x * 0xCCCCCCCCCCCCCCCD / 2 ^ 64 < 2 ^ 64)%Z) by (apply Z.div_lt_upper_bound; lia).
  rewrite (Z.mod_small (x * 0xCCCCCCCCCCCCCCCD / 2 ^ 64)) by (split; [apply Z.div_pos; lia | lia]).
  rewrite Z.div_div by lia.
  pose proof (Z.div_mod x 10 ltac:(lia)) as Hd. pose proof (Z.mod_pos_bound x 10 ltac:(lia)) as Hr.
  set (q := x / 10) in *. set (r := x mod 10) in *.
  symmetry. apply (Z.div_unique _ _ _ (2 * q + r * 0xCCCCCCCCCCCCCCCD)); [left; lia | lia].
Qed.

Lemma magic10 : forall xs, (-2^63 <= xs <= -10)%Z -> ((xs * 7378697629483820647) / 2^64 / 4 + 1 = - ((- xs) / 10))%Z.
Proof.
  intros xs Hx. rewrite Z.div_div by lia.
  assert (Hd : (- xs = 10 * ((- xs) / 10) + (- xs) mod 10)%Z) by (apply Z.div_mod; lia).
  pose proof (Z.mod_pos_bound (- xs) 10 ltac:(lia)) as Hr.
  set (k := ((- xs) / 10)%Z) in *. set (r := ((- xs) mod 10)%Z) in *.
  assert (Hk : (1 <= k)%Z) by lia.
  assert (Q : (xs * 7378697629483820647 / (2 ^ 64 * 4) = - k - 1)%Z).
  { symmetry. apply (Z.div_unique _ _ _ (xs * 7378697629483820647 + 2 ^ 66 * (k + 1))); [left; lia | lia]. }
  rewrite Q. lia.
Qed.
Lemma sgn_hi : forall w, (2 ^ 63 <= w < 2 ^ 64)%Z -> bv_signed (Z_to_bv 64 w) = (w - 2 ^ 64)%Z.
Proof.
  intros w Hw. rewrite Z_to_bv_signed. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. cbn -[Z.pow]. change (2 ^ 64 / 2)%Z with (2 ^ 63)%Z.
  rewrite (Z.mod_eq (w + 2 ^ 63) (2 ^ 64)) by lia. replace ((w + 2 ^ 63) / 2 ^ 64)%Z with 1%Z; [lia|]. apply (Z.div_unique_pos _ _ _ (w + 2 ^ 63 - 2 ^ 64)); lia.
Qed.
Lemma sgn_lo : forall w, (- 2 ^ 63 <= w < 2 ^ 63)%Z -> bv_signed (Z_to_bv 64 w) = w.
Proof.
  intros w Hw. rewrite Z_to_bv_signed. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. cbn -[Z.pow]. change (2 ^ 64 / 2)%Z with (2 ^ 63)%Z.
  rewrite Z.mod_small by lia. lia.
Qed.
Lemma nq_val : forall w, (2 ^ 63 <= w <= 2 ^ 64 - 10)%Z ->
  Z_to_bv 64 (bv_signed (Z_to_bv 64 ((bv_signed (Z_to_bv 64 w) * bv_signed (Z_to_bv 64 FM2)) ≫ 64)) ≫ 2 +
              ((bv_signed (Z_to_bv 64 w) * bv_signed (Z_to_bv 64 FM2)) ≫ 64 mod 18446744073709551616) ≫ 63)
  = Z_to_bv 64 (2 ^ 64 - (2 ^ 64 - w) / 10).
Proof.
  intros w Hw. rewrite (sgn_hi w) by lia. unfold FM2. rewrite (sgn_lo 7378697629483820647) by lia.
  set (xs := (w - 2 ^ 64)%Z). pose proof (magic10 xs ltac:(unfold xs; lia)) as MG.
  rewrite !Z.shiftr_div_pow2 by lia.
  set (hz := (xs * 7378697629483820647 / 2 ^ 64)%Z) in *.
  assert (Hh : (-2^62 <= hz <= -1)%Z) by (unfold hz; split; [apply Z.div_le_lower_bound; lia | apply Z.div_le_upper_bound; lia]).
  rewrite (sgn_lo hz) by lia.
  assert (Uh : (hz mod 18446744073709551616 = hz + 2 ^ 64)%Z).
  { change 18446744073709551616%Z with (2 ^ 64)%Z. symmetry. apply (Z.mod_unique hz (2 ^ 64) (-1) (hz + 2 ^ 64)); lia. }
  rewrite Uh.
  replace ((hz + 2 ^ 64) / 2 ^ 63)%Z with 1%Z by (apply (Z.div_unique_pos _ _ _ (hz + 2 ^ 64 - 2 ^ 63)); lia).
  change (2 ^ 2)%Z with 4%Z. apply Z_to_bv_eqm. rewrite MG. unfold xs. replace (- (w - 2 ^ 64))%Z with (2 ^ 64 - w)%Z by lia.
  replace (2 ^ 64 - (2 ^ 64 - w) / 10)%Z with (- ((2 ^ 64 - w) / 10) + 1 * 2 ^ 64)%Z by lia. rewrite Z_mod_plus_full. reflexivity.
Qed.

Lemma fi_u8arr_rw : forall m A bs, u8arr rsegs m A bs -> rw_cells rsegs m A [CB (length bs) bs].
Proof.
  intros m A bs [Hb Hw]. split; [split|].
  - cbn. tauto.
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact Hb.
  - cbn [cells_size csize]. rewrite Nat.add_0_r. exact Hw.
Qed.

Section FI.

Variables ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word.
Variable F : bvmap 5 word.
Variable fc : bv 32.
Variable SP o : Z.
Variable m0 : word -> option byte.
Hypothesis SPR : (2 ^ 41 + 384 <= SP /\ SP <= 2 ^ 47)%Z.
Hypothesis ORNG : (SP <= o /\ o + 24 <= 2 ^ 47)%Z.
Definition FSP : Z := (SP - 320)%Z.
Definition BUF : Z := (FSP + 25)%Z.
Definition FI_W : list (Z * Z) := [(SP - 384, SP); (o, o + 24)]%Z.

Definition fi_mem (m : word -> option byte) (jl bsb bs : list byte) : Prop :=
  rw_cells rsegs m FSP [CB 25 jl] /\ u8arr rsegs m BUF bsb /\ length bsb = 255%nat
  /\ rw_cells rsegs m (FSP + 280) [C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
  /\ u8arr rsegs m o bs /\ length bs = 24%nat
  /\ stk rsegs m (SP - 384) FSP /\ munch FI_W m0 m /\ wmono rsegs m0 m /\ mem_inv rsegs m.

Definition fi_post : machine_state -> Prop :=
  fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' (c : Z) (bs : list byte),
    ms' = MS (mkR ra (Z_to_bv 64 SP) gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 c) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ (1 <= c <= 20)%Z /\ u8arr rsegs m' o bs /\ length bs = 24%nat /\ nth_error bs 0 = Some (Z_to_bv 8 (2 * c)) /\ nth_error bs (Z.to_nat (1 + c)) = Some (Z_to_bv 8 0)
    /\ stk rsegs m' (SP - 384) SP /\ munch FI_W m0 m' /\ wmono rsegs m0 m' /\ mem_inv rsegs m'.

Lemma fi_epi : forall rav t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2' s3' t3 t4 t5 t6 (m : word -> option byte) (c : Z) (jl bsb bs : list byte),
  (1 <= c <= 20)%Z -> fi_mem m jl bsb bs -> nth_error bs 0 = Some (Z_to_bv 8 (2 * c)) -> nth_error bs (Z.to_nat (1 + c)) = Some (Z_to_bv 8 0) ->
  evt rsegs fi_post (MS (mkR rav (Z_to_bv 64 FSP) gp tp t0 t1 t2 (Z_to_bv 64 o) (Z_to_bv 64 c) a0 a1 a2 a3 a4 a5 a6 a7 s2' s3' s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 0x43424) fc None m (seg_rom rsegs)).
Proof.
  intros until bs. intros Hc (FR0 & BB & BBL & FRS & BU & BL & ST & MU & WM & MI) B0 BN.
  unfold BUF, FSP in *.
  do 8 zstep.
  replace (Z_to_bv 64 (SP - 320 + 320)) with (Z_to_bv 64 SP) by (f_equal; lia).
  pose proof (fi_u8arr_rw m _ bsb BB) as FRB. rewrite BBL in FRB.
  assert (FR : rw_cells rsegs m (SP - 320) ([CB 25 jl] ++ [CB 255 bsb] ++ [C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])).
  { apply (proj2 (rw_cells_app m _ _ _)). split; [exact FR0|]. cbn [cells_size csize Nat.add].
    apply (proj2 (rw_cells_app m _ _ _)). cbn [cells_size csize Nat.add].
    split; [replace (SP - 320 + Z.of_nat 25)%Z with (SP - 320 + 25)%Z by lia; exact FRB|].
    replace (SP - 320 + Z.of_nat 25 + Z.of_nat 255)%Z with (SP - 320 + 280)%Z by lia. exact FRS. }
  cbn [app] in FR. clear FR0 BB FRB FRS.
  release_frame FR ST SP.
  finish. all: first [exact BU | exact BL | exact B0 | exact BN | lia].
Qed.

Lemma fi_rloop : forall (n : nat) (k c sz : Z) rav t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (m : word -> option byte) (jl bsb bs : list byte),
  Z.to_nat k = n -> (1 <= k)%Z -> sz = (c - k)%Z -> (0 <= sz)%Z -> (c <= 20)%Z ->
  fi_mem m jl bsb bs -> nth_error bs 0 = Some (Z_to_bv 8 (2 * sz)) -> nth_error bs (Z.to_nat (1 + sz)) = Some (Z_to_bv 8 0) ->
  evt rsegs fi_post (MS (mkR rav (Z_to_bv 64 FSP) gp tp t0 t1 t2 (Z_to_bv 64 o) (Z_to_bv 64 c) a0 a1 a2 a3 a4 a5 a6 a7
                              (Z_to_bv 64 (BUF + k - 1)) (Z_to_bv 64 BUF) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 0x4340c) fc None m (seg_rom rsegs)).
Proof.
  induction n as [n IH] using lt_wf_ind.
  intros k c sz rav t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m jl bsb bs Hn Hk Hsz Hsz0 Hc (FR0 & BB & BBL & FRS & BU & BL & ST & MU & WM & MI) B0 BN.
  assert (FSPr : bv_unsigned (Z_to_bv 64 FSP) = FSP) by (unfold FSP; apply unsigned_lit; lia).
  destruct (nth_error bsb (Z.to_nat (k - 1))) as [b|] eqn:Hb; [| apply nth_error_None in Hb; lia].
  pose proof (u8arr_read rsegs m BUF bsb (k - 1) b (Z_to_bv 64 (BUF + k - 1)) BB Hb ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
  zstep. zstep. zstep.
  destruct (stk_split rsegs m (SP - 384) (FSP - 64) FSP ST ltac:(unfold FSP; lia)) as [STlo SThi].
  eapply evt_cut.
  { eapply (pb_inplace (Z_to_bv 64 0x43418) (Z_to_bv 64 FSP) gp tp (Z_to_bv 64 o) (Z_to_bv 64 c) (Z_to_bv 64 (BUF + k - 1)) (Z_to_bv 64 BUF)
                       s4 s5 s6 s7 s8 s9 s10 s11 F fc m o)
      with (n := sz) (c := b) (bs := bs); unfold PSP; rewrite ?FSPr; try (unfold FSP in *; lia); try eassumption; try reflexivity. }
  cbv beta. intros ms' P. unfold pb_post, PB_W, PSP in P. rewrite FSPr in P.
  destruct P as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & -> & MUc & WMc & MI2 & ST2 & BU2).
  replace (ret_pc (Z_to_bv 64 0x43418)) with (Z_to_bv 64 0x43418) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  clear SThi BU RD. unfold FI_W in MU. unfold BUF, FSP in *.
  transport_after_call rsegs m m2 MUc WMc. clear MUc WMc.
  assert (ST3 : stk rsegs m2 (SP - 384) (SP - 320)) by (apply (stk_merge rsegs m2 (SP - 384) (SP - 320 - 64) (SP - 320)); [exact STlo | exact ST2 | lia]).
  clear STlo ST2.
  set (bs' := upd (upd (upd bs 0 (Z_to_bv 8 (2 * sz + 2))) (Z.to_nat (sz + 1)) b) (Z.to_nat (sz + 2)) (Z_to_bv 8 0)) in *.
  assert (BL' : length bs' = 24%nat) by (unfold bs'; rewrite !upd_length; exact BL).
  assert (B0' : nth_error bs' 0 = Some (Z_to_bv 8 (2 * (sz + 1)))).
  { unfold bs'. rewrite nth_error_upd_other by lia. rewrite nth_error_upd_other by lia. rewrite nth_error_upd_same by lia. f_equal. f_equal. lia. }
  assert (BN' : nth_error bs' (Z.to_nat (1 + (sz + 1))) = Some (Z_to_bv 8 0)).
  { unfold bs'. replace (Z.to_nat (1 + (sz + 1))) with (Z.to_nat (sz + 2)) by lia. rewrite nth_error_upd_same by (rewrite !upd_length; lia). reflexivity. }
  assert (HM : fi_mem m2 jl bsb bs') by exact (conj FR0 (conj BB (conj BBL (conj FRS (conj BU2 (conj BL' (conj ST3 (conj MU (conj WM MI2))))))))).
  clear B0 BN.
  zstep. zstep. if_cases K1; zify_cond K1; [|lia]. zstep. if_cases K2; zify_cond K2.
  -
    replace (Z_to_bv 64 (SP - 320)) with (Z_to_bv 64 FSP) by reflexivity.
    assert (Hk1 : k = 1%Z) by lia. subst k.
    replace c with (sz + 1)%Z in * by lia.
    eapply fi_epi; [lia | exact HM | exact B0' | exact BN'].
  -
    replace (Z_to_bv 64 (SP - 320 + 25 + k - 1 + -1)) with (Z_to_bv 64 (BUF + (k - 1) - 1)) by (unfold BUF, FSP; f_equal; lia).
    replace (Z_to_bv 64 (SP - 320 + 25)) with (Z_to_bv 64 BUF) by reflexivity.
    replace (Z_to_bv 64 (SP - 320)) with (Z_to_bv 64 FSP) by reflexivity.
    eapply (IH (Z.to_nat (k - 1)) ltac:(lia) (k - 1)%Z c (sz + 1)%Z); [lia | lia | lia | lia | lia | exact HM | exact B0' | exact BN'].
Qed.

Lemma fi_after : forall t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (m : word -> option byte) (v c : Z) (jl bsb bs : list byte),
  (0 <= v < 2 ^ 64)%Z -> (1 <= c <= 19)%Z -> fi_mem m jl bsb bs -> nth_error bs 0 = Some (Z_to_bv 8 0) -> nth_error bs 1 = Some (Z_to_bv 8 0) ->
  evt rsegs fi_post (MS (mkR ra (Z_to_bv 64 FSP) gp tp t0 t1 t2 (Z_to_bv 64 o) s1 (Z_to_bv 64 v) a1 a2 a3 a4 a5 a6 a7
                              (Z_to_bv 64 c) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 0x433cc) fc None m (seg_rom rsegs)).
Proof.
  intros until bs. intros Hv Hc HM B0 B1.
  assert (FSPr : bv_unsigned (Z_to_bv 64 FSP) = FSP) by (unfold FSP; apply unsigned_lit; lia).
  zstep. zstep. if_cases K1; zify_cond K1; [lia|].
  do 4 zstep. if_cases K2; zify_cond K2.
  -
    zstep. zstep. if_cases K3; zify_cond K3; [unfold FSP in *; lia|]. do 4 zstep. if_cases K4; zify_cond K4; [unfold BUF, FSP in *; lia|].
    replace (Z_to_bv 64 (c + (FSP + 25) + -1)) with (Z_to_bv 64 (BUF + c - 1)) by (unfold BUF; f_equal; lia).
    replace (Z_to_bv 64 (FSP + 25)) with (Z_to_bv 64 BUF) by reflexivity.
    eapply (fi_rloop (Z.to_nat c) c c 0); [reflexivity | lia | lia | lia | lia | exact HM | exact B0 | exact B1].
  -
    destruct HM as (FR0 & BB & BBL & FRS & BU & BL & ST & MU & WM & MI).
    do 3 zstep.
    destruct (stk_split rsegs m (SP - 384) (FSP - 64) FSP ST ltac:(unfold FSP; lia)) as [STlo SThi].
    eapply evt_cut.
    { eapply (pb_inplace (Z_to_bv 64 0x433f0) (Z_to_bv 64 FSP) gp tp (Z_to_bv 64 o) (Z_to_bv 64 c) (Z_to_bv 64 c) (Z_to_bv 64 (FSP + 25 + c))
                         s4 s5 s6 s7 s8 s9 s10 s11 F fc m o)
        with (n := 0%Z) (c := Z_to_bv 8 45) (bs := bs); unfold PSP; rewrite ?FSPr; try (unfold FSP in *; lia); try eassumption; try reflexivity. }
    cbv beta. intros ms' P. unfold pb_post, PB_W, PSP in P. rewrite FSPr in P.
    destruct P as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & -> & MUc & WMc & MI2 & ST2 & BU2).
    replace (ret_pc (Z_to_bv 64 0x433f0)) with (Z_to_bv 64 0x433f0) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
    clear SThi BU. unfold FI_W in MU. unfold BUF, FSP in *.
    transport_after_call rsegs m m2 MUc WMc. clear MUc WMc.
    assert (ST3 : stk rsegs m2 (SP - 384) (SP - 320)) by (apply (stk_merge rsegs m2 (SP - 384) (SP - 320 - 64) (SP - 320)); [exact STlo | exact ST2 | lia]).
    clear STlo ST2.
    set (bs' := upd (upd (upd bs 0 (Z_to_bv 8 (2 * 0 + 2))) (Z.to_nat (0 + 1)) (Z_to_bv 8 45)) (Z.to_nat (0 + 2)) (Z_to_bv 8 0)) in *.
    assert (BL' : length bs' = 24%nat) by (unfold bs'; rewrite !upd_length; exact BL).
    assert (B0' : nth_error bs' 0 = Some (Z_to_bv 8 (2 * 1))) by (unfold bs'; cbn [Z.to_nat Z.add Pos.to_nat]; rewrite nth_error_upd_other by lia; rewrite nth_error_upd_other by lia;
                                                              rewrite nth_error_upd_same by lia; reflexivity).
    assert (BN' : nth_error bs' (Z.to_nat (1 + 1)) = Some (Z_to_bv 8 0)) by (unfold bs'; rewrite nth_error_upd_same by (rewrite !upd_length; lia); reflexivity).
    assert (HM : fi_mem m2 jl bsb bs') by exact (conj FR0 (conj BB (conj BBL (conj FRS (conj BU2 (conj BL' (conj ST3 (conj MU (conj WM MI2))))))))).
    do 3 zstep. if_cases K3; zify_cond K3; [lia|]. do 4 zstep. if_cases K4; zify_cond K4; [lia|].
    replace (Z_to_bv 64 (c + (SP - 320 + 25) + -1)) with (Z_to_bv 64 (BUF + c - 1)) by (unfold BUF, FSP; f_equal; lia).
    replace (Z_to_bv 64 (SP - 320 + 25)) with (Z_to_bv 64 BUF) by reflexivity.
    replace (Z_to_bv 64 (SP - 320)) with (Z_to_bv 64 FSP) by reflexivity.
    eapply (fi_rloop (Z.to_nat c) c (c + 1) 1); [reflexivity | lia | lia | lia | lia | exact HM | exact B0' | exact BN'].
Qed.

Lemma fi_ploop : forall (n : nat) (x i : Z) t0 t1 t2 a6 a7 t3 t4 t5 t6 (m : word -> option byte) (v : Z) (jl bsb bs : list byte),
  Z.to_nat (18 - i) = n -> (0 <= i <= 18)%Z -> (0 <= x < 10 ^ (19 - i))%Z -> (0 <= v < 2 ^ 64)%Z ->
  fi_mem m jl bsb bs -> nth_error bs 0 = Some (Z_to_bv 8 0) -> nth_error bs 1 = Some (Z_to_bv 8 0) ->
  evt rsegs fi_post (MS (mkR ra (Z_to_bv 64 FSP) gp tp t0 t1 t2 (Z_to_bv 64 o) s1 (Z_to_bv 64 v) (Z_to_bv 64 FM1) (Z_to_bv 64 BUF)
                              (Z_to_bv 64 10) (Z_to_bv 64 254) (Z_to_bv 64 x) a6 a7 (Z_to_bv 64 i) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 0x43340) fc None m (seg_rom rsegs)).
Proof.
  induction n as [n IH] using lt_wf_ind.
  intros x i t0 t1 t2 a6 a7 t3 t4 t5 t6 m v jl bsb bs Hn Hi Hx Hv (FR0 & BB & BBL & FRS & BU & BL & ST & MU & WM & MI) B0 B1.
  assert (P19 : (10 ^ (19 - i) <= 10 ^ 19)%Z) by (apply Z.pow_le_mono_r; lia).
  unfold FI_W in MU. unfold BUF, FSP in *.
  do 9 zstep. rewrite !mulhu10 by lia.
  pose proof (u8arr_store_ok rsegs m (SP - 320 + 25) bsb i (Z_to_bv 64 (SP - 320 + 25 + i)) BB ltac:(rewrite BBL; lia) ltac:(unfold wa; f_equal; lia)) as SOK.
  zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mm ?ad (le1 (Z_to_bv 64 ?e))) _) =>
    replace (write_to_mem mm ad (le1 (Z_to_bv 64 e))) with (write_to_mem mm (wa (SP - 320 + 25 + i)) [Z_to_bv 8 e]) by (f_equal; try (unfold wa; f_equal; lia); try (symmetry; apply le1_lit); try apply le1_lit);
    pose proof (u8arr_write rsegs mm (SP - 320 + 25) bsb i (Z_to_bv 8 e) BB ltac:(rewrite BBL; lia)) as BB' end.
  clear BB. store_done.
  lazymatch type of BB' with u8arr _ _ _ ?l => assert (BBL' : length l = 255%nat) by (rewrite upd_length; exact BBL) end.
  zstep. if_cases K1; zify_cond K1.
  -
    eapply fi_after; [exact Hv | lia | | exact B0 | exact B1].
    exact (conj FR0 (conj BB' (conj BBL' (conj FRS (conj BU (conj BL (conj ST (conj MU (conj WM MI))))))))).
  - zstep. if_cases K2; zify_cond K2; [|lia].
    assert (Hi1 : (i <= 17)%Z).
    { destruct (Z_le_gt_dec i 17) as [?|Hg]; [lia|]. replace (19 - i)%Z with 1%Z in Hx by lia. lia. }
    eapply (IH (Z.to_nat (18 - (i + 1))) ltac:(lia) (x / 10)%Z (i + 1)%Z); [lia | lia | | exact Hv | | exact B0 | exact B1].
    + split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|].
      replace (19 - i)%Z with (1 + (19 - (i + 1)))%Z in Hx by lia. rewrite Z.pow_add_r in Hx by lia. lia.
    + exact (conj FR0 (conj BB' (conj BBL' (conj FRS (conj BU (conj BL (conj ST (conj MU (conj WM MI))))))))).
Qed.

Lemma fi_nloop : forall (n : nat) (w i : Z) t0 t1 t2 a6 t3 t4 t5 t6 (m : word -> option byte) (v : Z) (jl bsb bs : list byte),
  Z.to_nat (18 - i) = n -> (0 <= i <= 18)%Z -> (2 ^ 63 <= w < 2 ^ 64)%Z -> (2 ^ 64 - w < 10 ^ (19 - i))%Z -> (0 <= v < 2 ^ 64)%Z ->
  fi_mem m jl bsb bs -> nth_error bs 0 = Some (Z_to_bv 8 0) -> nth_error bs 1 = Some (Z_to_bv 8 0) ->
  evt rsegs fi_post (MS (mkR ra (Z_to_bv 64 FSP) gp tp t0 t1 t2 (Z_to_bv 64 o) s1 (Z_to_bv 64 v) (Z_to_bv 64 BUF) (Z_to_bv 64 FM2)
                              (Z_to_bv 64 10) (Z_to_bv 64 (-20)) (Z_to_bv 64 254) a6 (Z_to_bv 64 w) (Z_to_bv 64 i) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 0x43390) fc None m (seg_rom rsegs)).
Proof.
  induction n as [n IH] using lt_wf_ind.
  intros w i t0 t1 t2 a6 t3 t4 t5 t6 m v jl bsb bs Hn Hi Hw Hq Hv (FR0 & BB & BBL & FRS & BU & BL & ST & MU & WM & MI) B0 B1.
  assert (P19 : (10 ^ (19 - i) <= 10 ^ 19)%Z) by (apply Z.pow_le_mono_r; lia).
  unfold FI_W in MU. unfold BUF, FSP in *.
  do 12 zstep.
  pose proof (u8arr_store_ok rsegs m (SP - 320 + 25) bsb i (Z_to_bv 64 (SP - 320 + 25 + i)) BB ltac:(rewrite BBL; lia) ltac:(unfold wa; f_equal; lia)) as SOK.
  zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mm ?ad (le1 (Z_to_bv 64 ?e))) _) =>
    replace (write_to_mem mm ad (le1 (Z_to_bv 64 e))) with (write_to_mem mm (wa (SP - 320 + 25 + i)) [Z_to_bv 8 e])
      by (f_equal; try (unfold wa; f_equal; lia); try (symmetry; apply le1_lit); try apply le1_lit);
    pose proof (u8arr_write rsegs mm (SP - 320 + 25) bsb i (Z_to_bv 8 e) BB ltac:(rewrite BBL; lia)) as BB' end.
  clear BB. store_done.
  lazymatch type of BB' with u8arr _ _ _ ?l => assert (BBL' : length l = 255%nat) by (rewrite upd_length; exact BBL) end.
  zstep. if_cases K1; zify_cond K1.
  -
    eapply fi_after; [exact Hv | lia | | exact B0 | exact B1].
    exact (conj FR0 (conj BB' (conj BBL' (conj FRS (conj BU (conj BL (conj ST (conj MU (conj WM MI))))))))).
  - zstep. if_cases K2; zify_cond K2; [|lia].
    assert (Hw10 : (2 ^ 63 <= w <= 2 ^ 64 - 10)%Z) by lia.
    rewrite (nq_val w Hw10).
    assert (Hi1 : (i <= 17)%Z).
    { destruct (Z_le_gt_dec i 17) as [?|Hg]; [lia|]. replace (19 - i)%Z with 1%Z in Hq by lia. lia. }
    assert (D1 : (1 <= (2 ^ 64 - w) / 10)%Z) by (apply Z.div_le_lower_bound; lia).
    assert (D2 : ((2 ^ 64 - w) / 10 <= 2 ^ 63 / 10)%Z) by (apply Z.div_le_mono; lia).
    eapply (IH (Z.to_nat (18 - (i + 1))) ltac:(lia) (2 ^ 64 - (2 ^ 64 - w) / 10)%Z (i + 1)%Z); [lia | lia | lia | | exact Hv | | exact B0 | exact B1].
    + replace (2 ^ 64 - (2 ^ 64 - (2 ^ 64 - w) / 10))%Z with ((2 ^ 64 - w) / 10)%Z by lia. apply Z.div_lt_upper_bound; [lia|].
      replace (19 - i)%Z with (1 + (19 - (i + 1)))%Z in Hq by lia. rewrite Z.pow_add_r in Hq by lia. lia.
    + exact (conj FR0 (conj BB' (conj BBL' (conj FRS (conj BU (conj BL (conj ST (conj MU (conj WM MI))))))))).
Qed.

Lemma fi_entry : forall t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (m : word -> option byte) (v : Z) (bs : list byte),
  (0 <= v < 2 ^ 64)%Z -> u8arr rsegs m o bs -> length bs = 24%nat -> nth_error bs 0 = Some (Z_to_bv 8 0) -> nth_error bs 1 = Some (Z_to_bv 8 0) ->
  stk rsegs m (SP - 384) SP -> mem_inv rsegs m -> m = m0 ->
  evt rsegs fi_post (MS (mkR ra (Z_to_bv 64 SP) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 v) (Z_to_bv 64 o) a2 a3 a4 a5 a6 a7
                              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 0x432fc) fc None m (seg_rom rsegs)).
Proof.
  intros until bs. intros Hv BU BL B0 B1 ST MI ->.
  pose proof (munch_refl FI_W m0) as MU. pose proof (wmono_refl rsegs m0) as WM. unfold FI_W in MU.
  carve_frame 320%nat ST.
  do 6 zstep.
  lazymatch type of FR with rw_cells _ _ _ (CB 280 ?j :: ?rest) =>
    apply (rw_cells_split_CB rsegs m (SP + -320) [] 280 j rest [25; 255]%nat) in FR; [| reflexivity] end.
  cbn [mk_CB_cells app] in FR.
  change (?c1 :: ?c2 :: ?rest) with ([c1] ++ [c2] ++ rest) in FR.
  apply (proj1 (rw_cells_app m _ _ _)) in FR. destruct FR as [FR0 FR]. cbn [cells_size csize Nat.add] in FR.
  apply (proj1 (rw_cells_app m _ _ _)) in FR. destruct FR as [FRB FRS]. cbn [cells_size csize Nat.add] in FRS.
  pose proof FRB as FRB'. destruct FRB' as [[[HLB _] _] _].
  apply (u8arr_of_rw_cells rsegs) in FRB.
  replace (SP + -320 + Z.of_nat 25 + Z.of_nat 255)%Z with (FSP + 280)%Z in FRS by (unfold FSP; lia).
  replace (SP + -320 + Z.of_nat 25)%Z with BUF in FRB by (unfold BUF, FSP; lia).
  replace (SP + -320)%Z with FSP in FR0, ST by (unfold FSP; lia).
  lazymatch type of FRB with u8arr _ _ _ ?l => assert (HM : fi_mem m _ l bs) by exact (conj FR0 (conj FRB (conj HLB (conj FRS (conj BU (conj BL (conj ST (conj MU (conj WM MI))))))))) end.
  clear FR0 FRB HLB FRS BU ST MU WM.
  do 4 zstep. if_cases K0; zify_cond K0; [lia|]. zstep. zstep. if_cases K1; zify_cond K1.
  -
    do 7 zstep.
    replace (Z_to_bv 64 (SP + -295)) with (Z_to_bv 64 BUF) by (unfold BUF, FSP; f_equal; lia).
    replace (Z_to_bv 64 (SP + -320)) with (Z_to_bv 64 FSP) by (unfold FSP; f_equal; lia).
    eapply (fi_nloop (Z.to_nat (18 - 0)) v 0); [reflexivity | lia | lia | cbn -[Z.pow]; lia | lia | exact HM | exact B0 | exact B1].
  -
    do 5 zstep.
    replace (Z_to_bv 64 (SP + -295)) with (Z_to_bv 64 BUF) by (unfold BUF, FSP; f_equal; lia).
    replace (Z_to_bv 64 (SP + -320)) with (Z_to_bv 64 FSP) by (unfold FSP; f_equal; lia).
    eapply (fi_ploop (Z.to_nat (18 - 0)) v 0); [reflexivity | lia | cbn -[Z.pow]; lia | lia | exact HM | exact B0 | exact B1].
Qed.
End FI.
