(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.bignum.lib.Lib Require Import Tac Arr.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import BnBase.
From OSSVerify.Proofs.openssl.bignum.lib.BnW Require Import BnTac BnMem BnArith.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Section Model.
  Variables (fl fcy : Z -> Z -> Z -> Z).
  Fixpoint gen_words_c (la lb : list Z) (c : Z) : list Z * Z :=
    match la, lb with
    | x :: la', y :: lb' => let '(r, c') := gen_words_c la' lb' (fcy x y c) in (fl x y c :: r, c')
    | _, _ => ([], c)
    end.
  Lemma gen_words_c_cons : forall x y la lb c,
    gen_words_c (x :: la) (y :: lb) c =
    (fl x y c :: fst (gen_words_c la lb (fcy x y c)), snd (gen_words_c la lb (fcy x y c))).
  Proof. intros. cbn [gen_words_c]. destruct (gen_words_c la lb (fcy x y c)). reflexivity. Qed.
  End Model.

Definition wl_post (segs : list Segment) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (rp n fs : Z) (res : list Z) (cy : Z) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3' a4' a5' a6' a7' t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 cy) a1' a2' a3' a4' a5' a6' a7'
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom segs)
    /\ munch [(rp, rp + 8 * n); (bv_unsigned sp - fs, bv_unsigned sp)]%Z m m'
    /\ wmono segs m m' /\ mem_inv segs m'
    /\ limbs_at segs m' rp res
    /\ stk segs m' lo (bv_unsigned sp).

Section Kit.
  Variable segs : list Segment.
  Variables (fl fcy : Z -> Z -> Z -> Z) (CB : Z).
  Hypothesis fcy_range : forall x y c, (0 <= x < 18446744073709551616)%Z -> (0 <= y < 18446744073709551616)%Z -> (0 <= c <= CB)%Z ->
    (0 <= fcy x y c <= CB)%Z.

  Variables (m : word -> option byte) (rp ap bp SP lo : Z) (a b : list Z).

  Variables (FS FB : Z) (FCELLS : list cell).
  Hypothesis FS_ok : Z.of_nat (cells_size FCELLS) = FS.
  Hypothesis FB_eq : (FB = SP - FS)%Z.
  Notation n := (Z.of_nat (length a)).
  Notation W := [(rp, rp + 8 * Z.of_nat (length a)); (SP - FS, SP)]%Z.
  Hypothesis LEN : length b = length a.
  Hypothesis ALA : alias_ok rp ap n.
  Hypothesis ALB : alias_ok rp bp n.
  Hypothesis SEPR : (rp + 8 * n <= SP - FS \/ SP <= rp)%Z.
  Hypothesis SEPA : (ap + 8 * n <= SP - FS \/ SP <= ap)%Z.
  Hypothesis SEPB : (bp + 8 * n <= SP - FS \/ SP <= bp)%Z.
  Variables (res : list Z) (cy : Z).

  Definition INV (m1 : word -> option byte) (pre la lb : list Z) (c pa pb pr : Z) : Prop :=
    limbs_at segs m1 pa la /\ limbs_at segs m1 pb lb /\ limbs_at segs m1 rp pre /\
    wr_at segs m1 rp (8 * n) /\
    rw_cells segs m1 FB FCELLS /\ stk segs m1 lo FB /\
    mem_inv segs m1 /\ munch W m m1 /\ wmono segs m m1 /\
    (pa = ap + 8 * Z.of_nat (length pre) /\ pb = bp + 8 * Z.of_nat (length pre) /\ pr = rp + 8 * Z.of_nat (length pre) /\
     Z.of_nat (length pre) + Z.of_nat (length la) = n /\ length lb = length la /\ 0 <= c <= CB /\
     rp + 8 * n <= 140737488355328)%Z /\
    limbs la /\ limbs lb /\
    res = pre ++ fst (gen_words_c fl fcy la lb c) /\ cy = snd (gen_words_c fl fcy la lb c).

  Ltac open_inv H := destruct H as (HA & HB & HP & HW & FR & ST & MI & MU & WM & AR & LLA & LLB & RES & CY).

  Lemma INV_rdA : forall m1 pre x la lb c pa pb pr ad,
    INV m1 pre (x :: la) lb c pa pb pr -> ad = wa pa -> ov_read_bytes segs m1 ad 8 = Some (le8 (Z_to_bv 64 x)).
  Proof using All. intros m1 pre x la lb c pa pb pr ad I E. open_inv I. eapply limbs_at_read_hd; eauto. Qed.
  Lemma INV_rdB : forall m1 pre la y lb c pa pb pr ad,
    INV m1 pre la (y :: lb) c pa pb pr -> ad = wa pb -> ov_read_bytes segs m1 ad 8 = Some (le8 (Z_to_bv 64 y)).
  Proof using All. intros m1 pre la y lb c pa pb pr ad I E. open_inv I. eapply limbs_at_read_hd; eauto. Qed.

  Lemma INV_rdB_k : forall m1 pre la lb c pa pb pr k y ad,
    INV m1 pre la lb c pa pb pr -> nth_error lb k = Some y -> ad = wa (pb + 8 * Z.of_nat k) ->
    ov_read_bytes segs m1 ad 8 = Some (le8 (Z_to_bv 64 y)).
  Proof using All. intros m1 pre la lb c pa pb pr k y ad I Hn E. open_inv I. exact (limbs_at_read_nth segs m1 pb lb k y ad HB Hn E). Qed.

  Lemma INV_rangeA : forall m1 pre x la lb c pa pb pr, INV m1 pre (x :: la) lb c pa pb pr -> (0 <= x < 18446744073709551616)%Z.
  Proof using All. intros m1 pre x la lb c pa pb pr I. open_inv I. apply limbs_cons_lit in LLA. tauto. Qed.
  Lemma INV_rangeB : forall m1 pre la y lb c pa pb pr, INV m1 pre la (y :: lb) c pa pb pr -> (0 <= y < 18446744073709551616)%Z.
  Proof using All. intros m1 pre la y lb c pa pb pr I. open_inv I. apply limbs_cons_lit in LLB. tauto. Qed.
  Lemma INV_carry : forall m1 pre la lb c pa pb pr, INV m1 pre la lb c pa pb pr -> (0 <= c <= CB)%Z.
  Proof using All. intros m1 pre la lb c pa pb pr I. open_inv I. tauto. Qed.
  Lemma INV_len : forall m1 pre la lb c pa pb pr, INV m1 pre la lb c pa pb pr ->
    length lb = length la /\ (Z.of_nat (length pre) + Z.of_nat (length la) = n)%Z /\ (pr = rp + 8 * Z.of_nat (length pre))%Z /\
    (rp + 8 * n <= 140737488355328)%Z /\ (0 <= rp)%Z.
  Proof using All.
    intros m1 pre la lb c pa pb pr I. open_inv I. pose proof (limbs_at_bound _ _ _ _ HP) as BP.
    destruct AR as (Epa & Epb & Epr & En & El & Hc & TOP).
    split; [exact El|]. split; [exact En|]. split; [exact Epr|]. split; [exact TOP|]. lia.
  Qed.

  Lemma INV_ptrs : forall m1 pre la lb c pa pb pr, INV m1 pre la lb c pa pb pr ->
    (pa = ap + 8 * Z.of_nat (length pre))%Z /\ (pb = bp + 8 * Z.of_nat (length pre))%Z /\
    (ap + 8 * n <= 18446744073709551616)%Z.
  Proof using All.
    intros m1 pre la lb c pa pb pr I. open_inv I. pose proof (limbs_at_bound _ _ _ _ HA) as BA.
    destruct AR as (Epa & Epb & Epr & En & El & Hc & TOP).
    split; [exact Epa|]. split; [exact Epb|]. change (2 ^ 64)%Z with 18446744073709551616%Z in BA. lia.
  Qed.

  Lemma INV_store : forall m1 pre x la y lb c pa pb pr ad pa' pb' pr' (w : word),
    INV m1 pre (x :: la) (y :: lb) c pa pb pr ->
    w = Z_to_bv 64 (fl x y c) -> ad = pr -> pa' = (pa + 8)%Z -> pb' = (pb + 8)%Z -> pr' = (pr + 8)%Z ->
    store_ok segs m1 (Z_to_bv 64 ad) 8 = true /\
    INV (write_to_mem m1 (Z_to_bv 64 ad) (le8 w)) (pre ++ [fl x y c]) la lb (fcy x y c) pa' pb' pr'.
  Proof using All.
    intros m1 pre x la y lb c pa pb pr ad pa' pb' pr' w I -> -> -> -> ->. open_inv I.
    destruct AR as (Epa & Epb & Epr & En & El & Hc & TOP).
    apply limbs_cons_lit in LLA. destruct LLA as [Rx LLA']. apply limbs_cons_lit in LLB. destruct LLB as [Ry LLB'].
    pose proof (limbs_at_bound _ _ _ _ HA) as BA. pose proof (limbs_at_bound _ _ _ _ HB) as BB.
    pose proof (limbs_at_bound _ _ _ _ HP) as BP.
    destruct HW as (W0 & W1 & HW'). pose proof (conj W0 (conj W1 HW')) as HW.
    cbn [length] in *.
    assert (SOK : store_ok segs m1 (Z_to_bv 64 pr) 8 = true).
    { change (Z_to_bv 64 pr) with (wa pr). rewrite Epr. apply (wr_at_store_ok segs m1 rp (8 * n)); [exact HW | lia | lia]. }
    split; [exact SOK|].
    change (Z_to_bv 64 pr) with (wa pr).
    assert (L8 : length (le8 (Z_to_bv 64 (fl x y c))) = 8%nat) by apply length_le8.
    unfold alias_ok in *. unfold INV.
    split. { apply limbs_at_write_other; [eapply limbs_at_cons_inv; exact HA | lia | rewrite L8; lia | rewrite L8; lia]. }
    split. { apply limbs_at_write_other; [eapply limbs_at_cons_inv; exact HB | lia | rewrite L8; lia | rewrite L8; lia]. }
    split. { rewrite Epr. apply limbs_at_snoc_write; [exact HP | lia]. }
    split. { apply wr_at_write. exact HW. }
    split. { apply rw_cells_frame; [exact FR | lia | rewrite L8; lia | rewrite L8, FS_ok; lia]. }
    split. { apply stk_write; [exact ST | lia | rewrite L8; lia]. }
    split. { apply mem_inv_store; [exact MI | rewrite L8; exact SOK]. }
    split. { apply munch_write; [exact MU | lia | rewrite L8; lia | rewrite L8; cbn [inside]; left; lia]. }
    split. { apply wmono_write. exact WM. }
    split. { pose proof (fcy_range x y c Rx Ry Hc). rewrite length_app. cbn [length]. lia. }
    split. { exact LLA'. }
    split. { exact LLB'. }
    split. { rewrite RES, gen_words_c_cons. cbn [fst]. rewrite <- app_assoc. reflexivity. }
    rewrite CY, gen_words_c_cons. reflexivity.
  Qed.

  Lemma INV_store_ok : forall m1 pre x la y lb c pa pb pr ad,
    INV m1 pre (x :: la) (y :: lb) c pa pb pr -> ad = pr -> store_ok segs m1 (Z_to_bv 64 ad) 8 = true.
  Proof using All.
    intros. eapply (proj1 (INV_store m1 pre x la y lb c pa pb pr ad _ _ _ _ H eq_refl H0 eq_refl eq_refl eq_refl)).
  Qed.

  Lemma INV_init : forall m1 c0,
    limbs a -> limbs b -> (0 < n)%Z -> (0 <= c0 <= CB)%Z ->
    limbs_at segs m ap a -> limbs_at segs m bp b -> wr_at segs m1 rp (8 * n) ->
    rw_cells segs m1 FB FCELLS -> stk segs m1 lo FB -> mem_inv segs m1 ->
    munch [(rp, rp + 8 * n); (FB, SP)]%Z m m1 -> munch [(FB, SP)]%Z m m1 -> wmono segs m m1 ->
    res = fst (gen_words_c fl fcy a b c0) -> cy = snd (gen_words_c fl fcy a b c0) ->
    INV m1 [] a b c0 ap bp rp.
  Proof using All.
    intros m1 c0 LA LB Hn Hc0 RA RB WR FR STK MI MU MUF WM RES CY.
    rewrite FB_eq in MU, MUF.
    pose proof (wr_at_below segs m1 rp (8 * n) MI WR ltac:(lia)) as TOP. unfold UTOP in TOP.
    pose proof (limbs_at_bound _ _ _ _ RA) as BA. pose proof (limbs_at_bound _ _ _ _ RB) as BB. rewrite LEN in BB.
    destruct WR as (W0 & W1 & WR'). pose proof (conj W0 (conj W1 WR')) as WR.
    unfold INV.
    split. { eapply limbs_at_transport; [exact RA | exact MUF | cbn [disjoint_from]; lia]. }
    split. { eapply limbs_at_transport; [exact RB | exact MUF | cbn [disjoint_from]; rewrite LEN; lia]. }
    split. { apply limbs_at_nil. lia. }
    split. { exact WR. }
    split. { exact FR. }
    split. { exact STK. }
    split. { exact MI. }
    split. { exact MU. }
    split. { exact WM. }
    split. { cbn [length]. lia. }
    split. { exact LA. }
    split. { exact LB. }
    split; assumption.
  Qed.

  Lemma INV_done : forall m1 pre c pa pb pr,
    INV m1 pre [] [] c pa pb pr ->
    limbs_at segs m1 rp res /\ cy = c /\
    rw_cells segs m1 FB FCELLS /\ stk segs m1 lo FB /\
    mem_inv segs m1 /\ munch W m m1 /\ wmono segs m m1.
  Proof using All.
    intros m1 pre c pa pb pr I. open_inv I. cbn [gen_words_c fst snd] in RES, CY. rewrite app_nil_r in RES. subst res.
    split; [exact HP|]. split; [exact CY|]. split; [exact FR|]. split; [exact ST|]. split; [exact MI|]. split; [exact MU|]. exact WM.
  Qed.
End Kit.

Ltac bump8 p :=
  lazymatch p with
  | Z.add ?b (Zpos ?k) => let s := eval vm_compute in (Zpos k + 8)%Z in constr:(Z.add b s)
  | _ => constr:(Z.add p 8%Z)
  end.

Ltac ldA_with RDA I := let ad := cur_mem_addr in let RD := fresh "RD" in
  pose proof (RDA _ _ _ _ _ _ _ _ _ ad I ltac:(addr_tac)) as RD; zstep; clear RD.
Ltac ldB_with RDB I := let ad := cur_mem_addr in let RD := fresh "RD" in
  pose proof (RDB _ _ _ _ _ _ _ _ _ ad I ltac:(addr_tac)) as RD; zstep; clear RD.

Ltac ldB_k_with RDBK I k := let ad := cur_mem_addr in let RD := fresh "RD" in
  pose proof (RDBK _ _ _ _ _ _ _ _ k _ ad I eq_refl ltac:(unfold wa; f_equal; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia)) as RD; zstep; clear RD.
Ltac ldA_k_with RDAK I k := let ad := cur_mem_addr in let RD := fresh "RD" in
  pose proof (RDAK _ _ _ _ _ _ _ _ k _ ad I eq_refl ltac:(unfold wa; f_equal; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia)) as RD; zstep; clear RD.

Ltac st_limb_with STOK STORE wtac I l cn Ecn :=
  lazymatch type of I with
  | INV _ ?fl ?fcy _ _ _ _ _ _ _ _ _ _ _ _ _ ?m1 ?pre (?x :: ?la) (?y :: ?lb) ?c ?pa ?pb ?pr =>
      let ad := cur_mem_addr in
      let E := lazymatch ad with Z_to_bv 64 ?E => E end in
      let SOK := fresh "SOK" in
      pose proof (STOK m1 pre x la y lb c pa pb pr E I ltac:(clear; lia)) as SOK;
      zstep; clear SOK;
      lazymatch goal with
      | |- evt _ _ (MS _ _ _ _ _ (write_to_mem m1 ?ad' (le8 ?w)) _) =>
          let pa' := bump8 pa in let pb' := bump8 pb in let pr' := bump8 pr in
          let I' := fresh "I" in
          pose proof (proj2 (STORE m1 pre x la y lb c pa pb pr E pa' pb' pr' w I ltac:(wtac) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia))) as I';
          clear I; rename I' into I;
          let m' := fresh "m" in
          gen_mem (write_to_mem m1 ad' (le8 w)) m';
          repeat match goal with H : context [m1] |- _ => clear H end; try clear m1;
          set (l := fl x y c) in I; clearbody l;
          remember (fcy x y c) as cn eqn:Ecn in I
      end
  end.

Ltac fin_with DONE I :=
  let D := fresh "D" in
  pose proof (DONE _ _ _ _ _ _ I) as D;
  destruct D as (HP & CY & FR & ST & MI & MU & WM);
  lazymatch type of ST with stk _ _ _ (?spz + -16)%Z => release_frame FR ST spz end;
  subst; finish.
