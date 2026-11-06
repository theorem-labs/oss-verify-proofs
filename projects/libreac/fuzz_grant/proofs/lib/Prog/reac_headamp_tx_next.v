From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Lib Require Import PropExec MState Mem Exec Frame Tac Bytes ZBridge Step.
From OSSVerify.Proofs.libreac.fuzz_grant.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import HeadampModel GrantModel NextModel NextLemmas
  TxStore reac_headamp_tx_next_c.
Import ListNotations.
Open Scope Z_scope.

Section Next.
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
  (m0 : word -> option byte) (t chp parp valp : Z).
Hypothesis Ht : 0 < t.
Hypothesis Ht2 : t + 460 <= 2^64.
Hypothesis Hc : 0 <= chp /\ chp + 1 <= 2^64.
Hypothesis Hp : 0 <= parp /\ parp + 1 <= 2^64.
Hypothesis Hv : 0 <= valp /\ valp + 1 <= 2^64.
Hypothesis Dc : chp + 1 <= t \/ t + 460 <= chp.
Hypothesis Dp : parp + 1 <= t \/ t + 460 <= parp.
Hypothesis Dv : valp + 1 <= t \/ t + 460 <= valp.
Hypothesis Ncp : chp <> parp.
Hypothesis Ncv : chp <> valp.
Hypothesis Npv : parp <> valp.

Definition QQ (res : nres) : machine_state -> Prop :=
  next_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 t chp parp valp res.

Definition SS (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (pc : Z) (m : word -> option byte) : machine_state :=
  MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
     F (Z_to_bv 64 pc) fc None m (seg_rom rsegs).

Definition cur (m : word -> option byte) (Tc : list byte) : Prop :=
  bytes_at rsegs m t Tc /\ length Tc = 460%nat /\ wr_at rsegs m t 460 /\
  wr_at rsegs m chp 1 /\ wr_at rsegs m parp 1 /\ wr_at rsegs m valp 1 /\
  munch [(t, t + 460)] m0 m /\ wmono rsegs m0 m.

Definition cur4 (m : word -> option byte) (Tc : list byte) : Prop :=
  bytes_at rsegs m t Tc /\ length Tc = 460%nat /\ wr_at rsegs m t 460 /\
  wr_at rsegs m chp 1 /\ wr_at rsegs m parp 1 /\ wr_at rsegs m valp 1 /\
  munch [(t, t + 460); (chp, chp + 1); (parp, parp + 1); (valp, valp + 1)] m0 m /\ wmono rsegs m0 m.

Lemma cur_cur4 : forall m Tc, cur m Tc -> cur4 m Tc.
Proof.
  intros m Tc (HB & HL & HW & HWc & HWp & HWv & MU & WM).
  refine (conj HB (conj HL (conj HW (conj HWc (conj HWp (conj HWv (conj _ WM))))))).
  eapply munch_weaken; [|exact MU]. intros x Hx. cbn [outside] in *. tauto.
Qed.

Ltac unpack H := destruct H as (HB & HL & HW & HWc & HWp & HWv & MU & WM).
Ltac pack := first [ unfold cur | unfold cur4 ];
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))); assumption.

Ltac xlen := rewrite ?length_le1, ?length_le4; cbn [length Z.of_nat Pos.of_succ_nat]; lia.

Ltac xport m a bs :=
  repeat match goal with
  | H : bytes_at rsegs m ?A2 ?bs2 |- _ =>
      apply (bytes_at_write_other rsegs m a bs A2 bs2) in H; [ | lia | xlen | rewrite ?length_le1, ?length_le4; cbn [length Z.of_nat Pos.of_succ_nat]; lia ]
  | H : wr_at rsegs m ?A2 ?n2 |- _ => apply (wr_at_write rsegs m A2 n2 (wa a) bs) in H
  | H : munch ?W ?mq m |- _ =>
      apply (munch_write W mq m a bs) in H; [ | lia | xlen | cbn [inside]; rewrite ?length_le1, ?length_le4; cbn [length Z.of_nat Pos.of_succ_nat]; lia ]
  | H : wmono rsegs ?mq m |- _ => apply (wmono_write rsegs mq m (wa a) bs) in H
  end.

Ltac sst k n :=
  lazymatch goal with
  | HW : wr_at rsegs ?m t 460, HB : bytes_at rsegs ?m t ?Tc, HL : length ?Tc = 460%nat |- evt _ _ (MS _ _ _ _ _ ?m _) =>
    let HS := fresh "HS" in
    assert (HS : store_ok rsegs m (wa (t + k)) n = true) by (apply (wr_at_store_ok rsegs m t 460 k n HW); lia);
    zstep;
    lazymatch goal with
    | |- evt _ _ (MS _ _ _ _ _ (write_to_mem m ?a ?bs) _) =>
      change (write_to_mem m a bs) with (write_to_mem m (wa (t + k)) bs);
      let HB' := fresh "HB" in let HL' := fresh "HL" in
      pose proof (bytes_at_struct m t Tc k bs HB HL ltac:(lia) ltac:(xlen)) as HB';
      assert (HL' : length (upd_bytes Tc (Z.to_nat k) bs) = 460%nat)
        by (rewrite upd_bytes_length; rewrite ?HL, ?length_le1, ?length_le4; lia);
      clear HB HL HS;
      xport m (t + k) bs;
      try clear m
    end
  end.

Ltac ost p :=
  lazymatch goal with
  | HWo : wr_at rsegs ?m p 1 |- evt _ _ (MS _ _ _ _ _ ?m _) =>
    let HS := fresh "HS" in
    assert (HS : store_ok rsegs m (wa p) 1 = true)
      by (rewrite <- (Z.add_0_r p); apply (wr_at_store_ok rsegs m p 1 0 1 HWo); lia);
    zstep;
    lazymatch goal with
    | |- evt _ _ (MS _ _ _ _ _ (write_to_mem m ?a ?bs) _) =>
      change (write_to_mem m a bs) with (write_to_mem m (wa p) bs);
      let HO := fresh "HO" in
      pose proof (bytes_at_write_same rsegs m p bs ltac:(lia) ltac:(xlen)) as HO;
      clear HS;
      xport m p bs;
      try clear m
    end
  end.

Ltac r1 Tc k :=
  lazymatch goal with
  | HB : bytes_at rsegs ?m t Tc, HL : length Tc = 460%nat |- _ =>
      let H := fresh "R" in pose proof (rd1 m t Tc k HB HL ltac:(lia)) as H;
      pose proof (tb_range Tc k)
  end.

Ltac r4 Tc k :=
  lazymatch goal with
  | HB : bytes_at rsegs ?m t Tc, HL : length Tc = 460%nat |- _ =>
      let H := fresh "R" in pose proof (rd4 m t Tc k HB HL ltac:(lia) ltac:(lia)) as H;
      pose proof (s32_range Tc k); pose proof (u32_range Tc k)
  end.

Ltac zl := zstep; cbv beta; rewrite ?ub8_tb, ?sx32_u32.


Lemma L_ret : forall t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m Tc,
  a1 = Z_to_bv 64 0 -> cur m Tc ->
  evt rsegs (QQ (silent Tc)) (SS t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 0x14d10 m).
Proof.
  intros t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m Tc -> HC. unpack HC. unfold SS.
  zstep. zstep.
  apply evt_done. unfold QQ, next_post, silent. do 14 eexists. exists m. split; [reflexivity|].
  split; [exact HB|]. split; [exact WM|]. exact MU.
Qed.

Lemma L_ret0 : forall t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m Tc,
  cur m Tc ->
  evt rsegs (QQ (silent Tc)) (SS t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 0x14d0c m).
Proof.
  intros t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m Tc HC. unfold SS.
  zstep. eapply L_ret; [reflexivity | exact HC].
Qed.

Lemma L_rs : forall t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m Tc,
  a0 = Z_to_bv 64 t -> cur m Tc ->
  evt rsegs (QQ (resweep Tc)) (SS t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 0x14cec m).
Proof.
  intros t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m Tc -> HC. unpack HC. unfold SS. pose proof HL as HLT.
  r4 Tc 452. zl. zstep.
  if_cases HC1; zify_cond HC1.
  - assert (E : u32 Tc 452 = 0) by (apply s32_zero; Z.div_mod_to_equations; lia).
    replace (resweep Tc) with (silent Tc) by (unfold resweep; rewrite E; reflexivity).
    rewrite (proj2 (s32_zero Tc 452) E).
    eapply L_ret; [reflexivity | pack].
  - assert (N1 : u32 Tc 452 <> 0)
      by (intro E; apply (proj2 (s32_zero _ _)) in E; rewrite E in HC1; cbn in HC1; lia).
    r1 Tc 450. zl. zstep.
    if_cases HC2; zify_cond HC2.
    + replace (resweep Tc) with (silent Tc)
        by (unfold resweep; rewrite (proj2 (Z.eqb_neq _ 0) N1), (proj2 (Z.eqb_eq (tb Tc 450) 0)) by lia; reflexivity).
      eapply L_ret0; pack.
    + r4 Tc 456. zl. zstep. rewrite swrap32_mod64.
      sst 456 4%nat.
      rewrite (le4_eqm (bv_swrap 32 (s32 Tc 456 + 1)) (u32 Tc 456 + 1)) in *
        by (rewrite swrap32_mod32; apply s32p1).
      change (upd_bytes Tc (Z.to_nat 456) (le4 (Z_to_bv 64 (u32 Tc 456 + 1)))) with (set4 Tc 456 (u32 Tc 456 + 1)) in *.
      zstep.
      pose proof (cmp32 (bv_swrap 32 (s32 Tc 456 + 1)) (s32 Tc 452) (swrap32_range _) (s32_range Tc 452)) as Hcm.
      rewrite swrap32_mod32, s32_mod32, s32p1 in Hcm.
      if_cases HC3; zify_cond HC3.
      * assert (G : u32 Tc 452 <= (u32 Tc 456 + 1) mod 4294967296) by lia.
        set (T1 := set4 Tc 456 (u32 Tc 456 + 1)) in *.
        assert (Em : resweep Tc = silent (set4 (set4 (setb (setb (set4 (setb T1 448 1) 456 0) 436 (tb Tc 449)) 437 (tb Tc 450)) 440 0) 444 0)).
        { unfold resweep. rewrite (proj2 (Z.eqb_neq _ 0) N1), (proj2 (Z.eqb_neq (tb Tc 450) 0)) by lia.
          rewrite (proj2 (Z.leb_le _ _) G). reflexivity. }
        rewrite Em.
        zstep. r1 T1 449. zl.
        replace (tb T1 449) with (tb Tc 449) by (unfold T1; symmetry; apply tb_set4_out; lia).
        zstep.
        sst 448 1%nat. sst 456 4%nat. sst 436 1%nat. sst 437 1%nat. sst 440 4%nat. sst 444 4%nat.
        zstep.
        eapply L_ret; [reflexivity | pack].
      * assert (G : (u32 Tc 456 + 1) mod 4294967296 < u32 Tc 452) by lia.
        assert (Em : resweep Tc = silent (set4 Tc 456 (u32 Tc 456 + 1))).
        { unfold resweep. rewrite (proj2 (Z.eqb_neq _ 0) N1), (proj2 (Z.eqb_neq (tb Tc 450) 0)) by lia.
          rewrite (proj2 (Z.leb_gt _ _) G). reflexivity. }
        rewrite Em. eapply L_ret0; pack.
Qed.

Ltac widen :=
  match goal with
  | MU : munch [(t, t + 460)] m0 ?m |- _ =>
      apply (munch_weaken [(t, t + 460)] [(t, t + 460); (chp, chp + 1); (parp, parp + 1); (valp, valp + 1)]) in MU;
      [ | intros x Hx; cbn [outside] in *; tauto ]
  end.

Lemma L_tail : forall t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m Tc c p v,
  a0 = Z_to_bv 64 t -> cur4 m Tc ->
  bytes_at rsegs m chp (le1 (Z_to_bv 64 c)) -> bytes_at rsegs m parp (le1 (Z_to_bv 64 p)) ->
  bytes_at rsegs m valp (le1 (Z_to_bv 64 v)) ->
  evt rsegs (QQ (1, (c, p, v), set4 Tc 456 0)) (SS t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 0x14c68 m).
Proof.
  intros t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m Tc c p v -> HC Bc Bp Bv. unpack HC. unfold SS.
  sst 456 4%nat. zstep. zstep. zstep. zstep.
  apply evt_done. unfold QQ, next_post. do 15 eexists. split; [reflexivity|].
  split; [eassumption|]. split; [eassumption|].
  split; [eassumption|]. split; [eassumption|]. split; eassumption.
Qed.

Ltac wnorm j :=
  rewrite ?Z.shiftr_div_pow2 by lia; change (2 ^ 32) with 4294967296; change (2 ^ 63) with 9223372036854775808;
  rewrite (div3_hi j), (div3_sign j) by lia; rewrite ?Z.add_0_r;
  repeat match goal with
  | |- context [Z.shiftl ?x 1] => rewrite (Z.shiftl_mul_pow2 x 1) by lia; change (2 ^ 1) with 2
  | |- context [?x mod 18446744073709551616] => rewrite (Z.mod_small x 18446744073709551616) by (Z.div_mod_to_equations; lia)
  | |- context [bv_swrap 32 ?x] => rewrite (swrap32_id x) by (Z.div_mod_to_equations; lia)
  end.

Lemma L_emitv : forall t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m T1 c p v j total,
  0 <= j -> j + 1 <= total -> total <= 765 -> s32 T1 440 = j + 1 -> 0 <= v < 256 ->
  a0 = Z_to_bv 64 t -> a1 = Z_to_bv 64 v -> a3 = Z_to_bv 64 valp -> a4 = Z_to_bv 64 total ->
  cur4 m T1 -> bytes_at rsegs m chp (le1 (Z_to_bv 64 c)) -> bytes_at rsegs m parp (le1 (Z_to_bv 64 p)) ->
  evt rsegs (QQ (1, (c, p, v), set4 (if j + 1 <? total then set4 T1 444 11 else setb T1 437 0) 456 0))
    (SS t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 0x14d98 m).
Proof.
  intros t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m T1 c p v j total Hj Hjt Htot HX Hv0 -> -> -> -> HC Bc Bp.
  unpack HC. unfold SS. pose proof HL as HLT.
  ost valp.
  r4 T1 440. zl. rewrite HX. zstep.
  if_cases HC1; zify_cond HC1; rewrite ?signed64_small in HC1 by lia.
  - rewrite (proj2 (Z.ltb_ge (j + 1) total)) by lia.
    sst 437 1%nat. zstep.
    eapply L_tail; [reflexivity | pack | eassumption | eassumption | eassumption].
  - rewrite (proj2 (Z.ltb_lt (j + 1) total)) by lia.
    zstep. sst 444 4%nat. zstep.
    eapply L_tail; [reflexivity | pack | eassumption | eassumption | eassumption].
Qed.

Lemma L_emitw : forall t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m T1 c p j total,
  0 <= c < 2147483648 -> 0 <= p < 3 -> 0 <= j -> j + 1 <= total -> total <= 765 -> s32 T1 440 = j + 1 ->
  a0 = Z_to_bv 64 t -> a1 = Z_to_bv 64 chp -> a2 = Z_to_bv 64 parp -> a3 = Z_to_bv 64 valp ->
  a4 = Z_to_bv 64 total -> a5 = Z_to_bv 64 (t + 144) -> t4 = Z_to_bv 64 c -> t0 = Z_to_bv 64 p ->
  cur m T1 ->
  evt rsegs (QQ (emit_res T1 t c p j total)) (SS t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 0x14d40 m).
Proof.
  intros t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m T1 c p j total Hc0 Hp0 Hj Hjt Htot HX
    -> -> -> -> -> -> -> -> HC.
  unpack HC. unfold SS. pose proof HL as HLT. widen.
  ost chp. ost parp.
  rewrite (le1_eqm c (c mod 256)) in * by (rewrite Z.mod_mod; lia).
  zstep.
  if_cases HC1; zify_cond HC1; [exfalso; Z.div_mod_to_equations; lia|].
  zstep. rewrite land_mod256. zstep. zstep.
  if_cases HC2; zify_cond HC2.
  - replace (emit_res T1 t c p j total)
      with (1, (c mod 256, p, dflt p), set4 (if j + 1 <? total then set4 T1 444 11 else setb T1 437 0) 456 0)
      by (unfold emit_res; rewrite eff_ch by lia; reflexivity).
    zstep. zstep. zstep. zstep.
    rewrite (swrap32_id (p + -2)) by lia. rewrite (dflt_code_all p) by lia.
    eapply L_emitv; [lia | lia | lia | exact HX | apply dflt_range | reflexivity .. | pack | eassumption | eassumption].
  - zstep. rewrite land_mod64. replace (c mod 64) with (c mod 256) by (Z.div_mod_to_equations; lia).
    zstep. zstep. zstep. zstep.
    rewrite ?Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
    r1 T1 (144 + 3 * (c mod 256) + p). zl. zstep.
    if_cases HC3; zify_cond HC3.
    + replace (emit_res T1 t c p j total)
        with (1, (c mod 256, p, dflt p), set4 (if j + 1 <? total then set4 T1 444 11 else setb T1 437 0) 456 0)
        by (unfold emit_res; rewrite eff_cell by lia; rewrite (proj2 (Z.eqb_eq _ 0)) by lia; reflexivity).
      zstep. zstep. zstep. zstep.
      rewrite (swrap32_id (p + -2)) by lia. rewrite (dflt_code_all p) by lia.
      eapply L_emitv; [lia | lia | lia | exact HX | apply dflt_range | reflexivity .. | pack | eassumption | eassumption].
    + replace (emit_res T1 t c p j total)
        with (1, (c mod 256, p, tb T1 (3 * (c mod 256) + p)),
              set4 (if j + 1 <? total then set4 T1 444 11 else setb T1 437 0) 456 0)
        by (unfold emit_res; rewrite eff_cell by lia; rewrite (proj2 (Z.eqb_neq _ 0)) by lia; reflexivity).
      zstep. zstep. r1 T1 (3 * (c mod 256) + p). zl. zstep.
      eapply L_emitv; [lia | lia | lia | exact HX | apply tb_range | reflexivity .. | pack | eassumption | eassumption].
Qed.

Lemma L_walk : forall n j t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m Tc bs o total,
  n = Z.to_nat (total - j) -> 0 <= j < total -> total <= 765 -> 0 <= bs < 256 -> 0 <= o < 256 ->
  a0 = Z_to_bv 64 t -> a1 = Z_to_bv 64 chp -> a2 = Z_to_bv 64 parp -> a3 = Z_to_bv 64 valp ->
  a4 = Z_to_bv 64 total -> a5 = Z_to_bv 64 (t + 144) -> a6 = Z_to_bv 64 bs -> a7 = Z_to_bv 64 o ->
  t1 = Z_to_bv 64 j -> t2 = Z_to_bv 64 1431655766 -> t3 = Z_to_bv 64 47 ->
  cur m Tc ->
  evt rsegs (QQ (walk Tc t bs o total j n)) (SS t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 0x14c9c m).
Proof.
  induction n as [|n IH];
    intros j t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m Tc bs o total En Hj Htot Hbs Ho
      -> -> -> -> -> -> -> -> -> -> -> HC; [lia|].
  rewrite walk_step. cbv zeta. unpack HC. unfold SS. pose proof HL as HLT.
  zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
  wnorm j.
  replace (j - j / 3 - j / 3 * 2) with (j mod 3) by (Z.div_mod_to_equations; lia).
  replace (j / 3 + bs) with (bs + j / 3) by lia.
  sst 440 4%nat.
  change (upd_bytes Tc (Z.to_nat 440) (le4 (Z_to_bv 64 (j + 1)))) with (set4 Tc 440 (j + 1)) in *.
  assert (HX1 : s32 (set4 Tc 440 (j + 1)) 440 = j + 1) by (apply s32_set4; lia).
  set (T1 := set4 Tc 440 (j + 1)) in *.
  assert (HC0 : cur (write_to_mem m (wa (t + 440)) (le4 (Z_to_bv 64 (j + 1)))) T1) by pack.
  zstep.
  if_cases HC1; zify_cond HC1.
  - replace (carried T1 bs o j) with true by (unfold carried; rewrite (proj2 (Z.eqb_eq o 0)) by lia; reflexivity).
    eapply L_emitw; [lia | lia | lia | lia | lia | exact HX1 | reflexivity .. | exact HC0].
  - zstep.
    if_cases HC2; zify_cond HC2; rewrite ?signed64_small in HC2 by lia.
    + replace (carried T1 bs o j) with false
        by (unfold carried; rewrite (proj2 (Z.eqb_neq o 0)), (proj2 (Z.leb_gt _ 47)) by lia; reflexivity).
      cbv iota. zstep.
      if_cases HC4; zify_cond HC4.
      * rewrite (proj2 (Z.eqb_neq (j + 1) total)) by lia.
        eapply IH; [lia | lia | lia | lia | lia | reflexivity .. | exact HC0].
      * rewrite (proj2 (Z.eqb_eq (j + 1) total)) by lia.
        sst 437 1%nat. eapply L_rs; [reflexivity | pack].
    + zstep. zstep. zstep. zstep.
      rewrite ?Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
      r1 T1 (144 + 3 * (bs + j / 3) + j mod 3). zl. zstep.
      if_cases HC3; zify_cond HC3.
      * replace (carried T1 bs o j) with true
          by (unfold carried; rewrite (proj2 (Z.eqb_neq o 0)), (proj2 (Z.leb_le _ 47)),
                (proj2 (Z.eqb_neq (tb T1 (144 + 3 * (bs + j / 3) + j mod 3)) 0)) by lia; reflexivity).
        eapply L_emitw; [lia | lia | lia | lia | lia | exact HX1 | reflexivity .. | exact HC0].
      * replace (carried T1 bs o j) with false
          by (unfold carried; rewrite (proj2 (Z.eqb_neq o 0)), (proj2 (Z.leb_le _ 47)),
                (proj2 (Z.eqb_eq (tb T1 (144 + 3 * (bs + j / 3) + j mod 3)) 0)) by lia; reflexivity).
        cbv iota. zstep.
        if_cases HC4; zify_cond HC4.
        -- rewrite (proj2 (Z.eqb_neq (j + 1) total)) by lia.
           eapply IH; [lia | lia | lia | lia | lia | reflexivity .. | exact HC0].
        -- rewrite (proj2 (Z.eqb_eq (j + 1) total)) by lia.
           sst 437 1%nat. eapply L_rs; [reflexivity | pack].
Qed.

Lemma L_after_scan : forall t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m T,
  a0 = Z_to_bv 64 t -> a1 = Z_to_bv 64 chp -> a2 = Z_to_bv 64 parp -> a3 = Z_to_bv 64 valp ->
  cur m T -> (tb T 437 <> 0 -> 0 <= s32 T 440) ->
  evt rsegs (QQ (after_scan T t)) (SS t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 0x14c2c m).
Proof.
  intros t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m T -> -> -> -> HC HX.
  pose proof HC as HC0. unpack HC. unfold SS. pose proof HL as HLT.
  r1 T 437. zl. zstep.
  if_cases HC1; zify_cond HC1.
  - replace (after_scan T t) with (resweep T)
      by (unfold after_scan; rewrite (proj2 (Z.eqb_eq (tb T 437) 0)) by lia; reflexivity).
    eapply L_rs; [reflexivity | exact HC0].
  - assert (N437 : (tb T 437 =? 0) = false) by (apply Z.eqb_neq; lia).
    specialize (HX ltac:(lia)).
    r4 T 444. zl. zstep.
    if_cases HC2; zify_cond HC2.
    + assert (Wle : s32 T 444 <= 0)
        by (apply andb_false_iff in HC2; destruct HC2 as [HC2|HC2]; apply Z.ltb_ge in HC2; Z.div_mod_to_equations; lia).
      r4 T 440. zl. zstep. zstep.
      rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
      replace (tb T 437 * 2 + tb T 437) with (3 * tb T 437) by lia.
      zstep.
      if_cases HC3; zify_cond HC3; rewrite ?signed64_small in HC3 by lia.
      * replace (after_scan T t) with (resweep (setb T 437 0))
          by (unfold after_scan; rewrite N437, (proj2 (Z.ltb_ge 0 _) Wle), (proj2 (Z.leb_le _ _)) by lia; reflexivity).
        sst 437 1%nat. eapply L_rs; [reflexivity | pack].
      * replace (after_scan T t)
          with (walk T t (tb T 436) (tb T 448) (3 * tb T 437) (s32 T 440) (Z.to_nat (3 * tb T 437 - s32 T 440)))
          by (unfold after_scan; rewrite N437, (proj2 (Z.ltb_ge 0 _) Wle), (proj2 (Z.leb_gt _ _)) by lia; reflexivity).
        r1 T 436. zl. r1 T 448. zl. zstep. zstep. zstep. zstep.
        eapply L_walk; [reflexivity | lia | lia | lia | lia | reflexivity .. | exact HC0].
    + assert (Wgt : 0 < s32 T 444) by (Z.div_mod_to_equations; lia).
      replace (after_scan T t) with (silent (set4 T 444 (s32 T 444 - 1)))
        by (unfold after_scan; rewrite N437, (proj2 (Z.ltb_lt 0 _) Wgt); reflexivity).
      zstep. zstep.
      sst 444 4%nat.
      match goal with |- context [le4 (Z_to_bv 64 ?E)] =>
        rewrite (le4_eqm E (s32 T 444 - 1)) in * by (Z.div_mod_to_equations; lia) end.
      zstep. eapply L_ret; [reflexivity | pack].
Qed.

Ltac scan_norm i :=
  rewrite ?Z.shiftr_div_pow2 by lia; change (2 ^ 9) with 512;
  rewrite (div3_171 i) by lia;
  repeat match goal with
  | |- context [Z.shiftl ?x 1] => rewrite (Z.shiftl_mul_pow2 x 1) by lia; change (2 ^ 1) with 2
  | |- context [Z.land ?x 255] => rewrite (land255 x) by (Z.div_mod_to_equations; lia)
  | |- context [?x mod 18446744073709551616] => rewrite (Z.mod_small x 18446744073709551616) by (Z.div_mod_to_equations; lia)
  end;
  replace (i - (i / 3 * 2 + i / 3)) with (i mod 3) by (Z.div_mod_to_equations; lia);
  replace (i / 3 * 2 + i / 3) with (3 * (i / 3)) by lia.

Lemma L_scan : forall n i t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m T,
  n = Z.to_nat (144 - i) -> 0 <= i < 144 ->
  a0 = Z_to_bv 64 t -> a1 = Z_to_bv 64 chp -> a2 = Z_to_bv 64 parp -> a3 = Z_to_bv 64 valp ->
  a4 = Z_to_bv 64 i -> a5 = Z_to_bv 64 (t + 288) -> a6 = Z_to_bv 64 171 -> a7 = Z_to_bv 64 144 ->
  cur m T -> (tb T 437 <> 0 -> 0 <= s32 T 440) ->
  evt rsegs (QQ (match first_dirty_from T i n with Some k => edge_res T k | None => after_scan T t end))
    (SS t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 0x14bf8 m).
Proof.
  induction n as [|n IH];
    intros i t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m T En Hi -> -> -> -> -> -> -> -> HC HX; [lia|].
  rewrite fd_step. pose proof HC as HC0. unpack HC. unfold SS. pose proof HL as HLT.
  zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
  scan_norm i.
  r1 T (288 + i). zstep. zl. zstep.
  if_cases HC1; zify_cond HC1.
  - rewrite (proj2 (Z.eqb_neq _ 0)) by lia. cbv iota.
    widen.
    sst (288 + i) 1%nat.
    ost chp. ost parp.
    zstep. zstep.
    match goal with H : bytes_at rsegs ?mm t ?X |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      let HL2 := fresh "HL2" in
      assert (HL2 : length X = 460%nat) by (eassumption);
      let R := fresh "R" in pose proof (rd1 mm t X i H HL2 ltac:(lia)) as R
    end.
    zl.
    match goal with |- context [tb ?X i] =>
      replace (tb X i) with (tb T i) by (symmetry; apply (tb_setb_out T (288 + i) 0 i); lia) end.
    ost valp.
    eapply L_tail; [reflexivity | pack | eassumption | eassumption | eassumption].
  - rewrite (proj2 (Z.eqb_eq _ 0)) by lia. cbv iota.
    zstep. rewrite swrap32_id by lia. zstep.
    if_cases HC2; zify_cond HC2.
    + eapply IH; [lia | lia | reflexivity .. | exact HC0 | exact HX].
    + assert (n = 0%nat) by lia. subst n. cbn [first_dirty_from].
      eapply L_after_scan; [reflexivity .. | exact HC0 | exact HX].
Qed.

Lemma L_main : forall t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 T,
  a0 = Z_to_bv 64 t -> a1 = Z_to_bv 64 chp -> a2 = Z_to_bv 64 parp -> a3 = Z_to_bv 64 valp ->
  cur m0 T -> (tb T 437 <> 0 -> 0 <= s32 T 440) ->
  evt rsegs (QQ (next_model T t)) (SS t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 0x14bd8 m0).
Proof.
  intros t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 T -> -> -> -> HC HX.
  pose proof HC as HC0. unpack HC. unfold SS. pose proof HL as HLT.
  r4 T 432. zl. zstep.
  if_cases HC1; zify_cond HC1.
  - assert (NA : u32 T 432 <> 0)
      by (intro E; apply (proj2 (s32_zero _ _)) in E; rewrite E in HC1; cbn in HC1; lia).
    replace (next_model T t)
      with (match first_dirty_from T 0 144 with Some k => edge_res T k | None => after_scan T t end)
      by (unfold next_model; rewrite (proj2 (Z.eqb_neq _ 0) NA); reflexivity).
    zstep. zstep. zstep. zstep.
    eapply L_scan; [reflexivity | lia | reflexivity .. | exact HC0 | exact HX].
  - assert (ZA : u32 T 432 = 0) by (apply s32_zero; Z.div_mod_to_equations; lia).
    r1 T 437. zl. zstep.
    if_cases HC2; zify_cond HC2.
    + replace (next_model T t) with (silent T)
        by (unfold next_model; rewrite ZA, (proj2 (Z.eqb_eq (tb T 437) 0)) by lia; reflexivity).
      eapply L_ret0; exact HC0.
    + replace (next_model T t)
        with (match first_dirty_from T 0 144 with Some k => edge_res T k | None => after_scan T t end)
        by (unfold next_model; rewrite ZA, (proj2 (Z.eqb_neq (tb T 437) 0)) by lia; reflexivity).
      zstep. zstep. zstep. zstep.
      eapply L_scan; [reflexivity | lia | reflexivity .. | exact HC0 | exact HX].
Qed.

End Next.

Theorem reac_headamp_tx_next_holds : reac_headamp_tx_next_contract.
Proof.
  unfold reac_headamp_tx_next_contract, REAC_HEADAMP_TX_NEXT.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m t chp parp valp T E0 E1 E2 E3 Ht HL HB HW HWc HWp HWv Dc Dp Dv Ncp Ncv Npv HX.
  pose proof (bytes_at_bound rsegs m t T HB) as Hb. rewrite HL in Hb. change (Z.of_nat 460) with 460 in Hb.
  pose proof HWc as (Hc1 & Hc2 & _). pose proof HWp as (Hp1 & Hp2 & _). pose proof HWv as (Hv1 & Hv2 & _).
  assert (HC : cur m t chp parp valp m T).
  { unfold cur. refine (conj HB (conj HL (conj HW (conj HWc (conj HWp (conj HWv (conj _ _))))))).
    - apply munch_refl.
    - apply wmono_refl. }
  eapply L_main; try eassumption; try lia.
Qed.
