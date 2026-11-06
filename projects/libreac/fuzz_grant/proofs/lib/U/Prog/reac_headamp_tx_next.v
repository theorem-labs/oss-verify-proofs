From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U.Prog Require Import HeadampModel GrantModel NextModel NextLemmas
  reac_headamp_tx_effective_c reac_headamp_tx_next_c.
Import ListNotations.
Open Scope Z_scope.

Lemma enum_Z : forall (P : Z -> bool) n, forallb (fun k => P (Z.of_nat k)) (seq 0 n) = true ->
  forall i, 0 <= i < Z.of_nat n -> P i = true.
Proof.
  intros P n H i Hi. rewrite forallb_forall in H. replace i with (Z.of_nat (Z.to_nat i)) by lia.
  apply H. apply in_seq. lia.
Qed.

Lemma scan_q : forall i, 0 <= i < 144 ->
  Z.shiftr ((Z.shiftr ((Z.shiftl i 32 mod 18446744073709551616) * 12297829383904690176) 64) mod 18446744073709551616) 33
  = i / 3.
Proof.
  intros i Hi. apply Z.eqb_eq.
  apply (enum_Z (fun i => Z.shiftr ((Z.shiftr ((Z.shiftl i 32 mod 18446744073709551616) * 12297829383904690176) 64)
                                    mod 18446744073709551616) 33 =? i / 3) 144); [vm_compute; reflexivity | lia].
Qed.

Lemma scan_r : forall i, 0 <= i < 144 ->
  (288 + i - (Z.land (Z.shiftr (i * 12297829382473034411) 64 mod 18446744073709551616) 18446744073709551614 +
              Z.shiftr (Z.shiftr (i * 12297829382473034411) 64 mod 18446744073709551616) 1)
             mod 18446744073709551616 + -288) mod 18446744073709551616 = i mod 3.
Proof.
  intros i Hi. apply Z.eqb_eq.
  apply (enum_Z (fun i => (288 + i - (Z.land (Z.shiftr (i * 12297829382473034411) 64 mod 18446744073709551616)
                                         18446744073709551614 +
                                       Z.shiftr (Z.shiftr (i * 12297829382473034411) 64 mod 18446744073709551616) 1)
                                      mod 18446744073709551616 + -288) mod 18446744073709551616 =? i mod 3) 144);
    [vm_compute; reflexivity | lia].
Qed.

Section Next.
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
  (m0 : word -> option byte) (lo t chp parp valp : Z) (jk : list byte).
Hypothesis Ht : 0 < t.
Hypothesis Ht2 : t + 460 <= 18446744073709551616.
Hypothesis H4 : t mod 4 = 0.
Hypothesis Hc : 0 < chp /\ chp + 1 <= 18446744073709551616.
Hypothesis Hp : 0 < parp /\ parp + 1 <= 18446744073709551616.
Hypothesis Hv : 0 < valp /\ valp + 1 <= 18446744073709551616.
Hypothesis Hlo : 0 <= lo.
Hypothesis LO : lo + 48 <= bv_unsigned sp.
Hypothesis Rsp : bv_unsigned sp < 18446744073709551616.

Definition SEPP : Prop :=
  (chp + 1 <= t \/ t + 460 <= chp) /\ (parp + 1 <= t \/ t + 460 <= parp) /\ (valp + 1 <= t \/ t + 460 <= valp) /\
  chp <> parp /\ chp <> valp /\ parp <> valp /\
  (t + 460 <= lo \/ bv_unsigned sp <= t) /\ (chp + 1 <= lo \/ bv_unsigned sp <= chp) /\
  (parp + 1 <= lo \/ bv_unsigned sp <= parp) /\ (valp + 1 <= lo \/ bv_unsigned sp <= valp).
Hypothesis SEP : SEPP.

Lemma sep_Dc : chp + 1 <= t \/ t + 460 <= chp. Proof. unfold SEPP in SEP. tauto. Qed.
Lemma sep_Dp : parp + 1 <= t \/ t + 460 <= parp. Proof. unfold SEPP in SEP. tauto. Qed.
Lemma sep_Dv : valp + 1 <= t \/ t + 460 <= valp. Proof. unfold SEPP in SEP. tauto. Qed.
Lemma sep_Ncp : chp <> parp. Proof. unfold SEPP in SEP. tauto. Qed.
Lemma sep_Ncv : chp <> valp. Proof. unfold SEPP in SEP. tauto. Qed.
Lemma sep_Npv : parp <> valp. Proof. unfold SEPP in SEP. tauto. Qed.
Lemma sep_Kt : t + 460 <= lo \/ bv_unsigned sp <= t. Proof. unfold SEPP in SEP. tauto. Qed.
Lemma sep_Kc : chp + 1 <= lo \/ bv_unsigned sp <= chp. Proof. unfold SEPP in SEP. tauto. Qed.
Lemma sep_Kp : parp + 1 <= lo \/ bv_unsigned sp <= parp. Proof. unfold SEPP in SEP. tauto. Qed.
Lemma sep_Kv : valp + 1 <= lo \/ bv_unsigned sp <= valp. Proof. unfold SEPP in SEP. tauto. Qed.

Ltac dlia := first [ lia
  | pose proof sep_Dc; lia | pose proof sep_Dp; lia | pose proof sep_Dv; lia
  | pose proof sep_Ncp; lia | pose proof sep_Ncv; lia | pose proof sep_Npv; lia
  | pose proof sep_Kt; lia | pose proof sep_Kc; lia | pose proof sep_Kp; lia | pose proof sep_Kv; lia ].

Definition FC : list cell := [CB 8 jk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Definition QQ (res : nres) : machine_state -> Prop :=
  next_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 lo t chp parp valp res.

Definition SS (ra' t0 t1 t2 s0' s1' s2' s3' a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (pc : Z)
    (m : word -> option byte) : machine_state :=
  MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 s0' s1' a0 a1 a2 a3 a4 a5 a6 a7 s2' s3'
          s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
     F (Z_to_bv 64 pc) fc None m (seg_rom rsegs).

Definition cur (m : word -> option byte) (Tc : list byte) : Prop :=
  bytes_at rsegs m t Tc /\ length Tc = 460%nat /\ wr_at rsegs m t 460 /\
  wr_at rsegs m chp 1 /\ wr_at rsegs m parp 1 /\ wr_at rsegs m valp 1 /\
  rw_cells rsegs m (bv_unsigned sp + -48) FC /\ stk rsegs m lo (bv_unsigned sp + -48) /\ mem_inv rsegs m /\
  munch [(bv_unsigned sp + -48, bv_unsigned sp); (t, t + 460)] m0 m /\ wmono rsegs m0 m.

Definition cur4 (m : word -> option byte) (Tc : list byte) : Prop :=
  bytes_at rsegs m t Tc /\ length Tc = 460%nat /\ wr_at rsegs m t 460 /\
  wr_at rsegs m chp 1 /\ wr_at rsegs m parp 1 /\ wr_at rsegs m valp 1 /\
  rw_cells rsegs m (bv_unsigned sp + -48) FC /\ stk rsegs m lo (bv_unsigned sp + -48) /\ mem_inv rsegs m /\
  munch [(bv_unsigned sp + -48, bv_unsigned sp); (t, t + 460); (chp, chp + 1); (parp, parp + 1); (valp, valp + 1)]
    m0 m /\ wmono rsegs m0 m.

Ltac unpack H := destruct H as (HB & HL & HW & HWc & HWp & HWv & FR & ST & HI & MU & WM).
Ltac pack := first [ unfold cur | unfold cur4 ];
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))))); assumption.

Ltac xlen := rewrite ?length_le1, ?length_le4; cbn [length Z.of_nat Pos.of_succ_nat]; lia.

Ltac xport m a bs :=
  repeat match goal with
  | H : bytes_at rsegs m ?A2 ?bs2 |- _ =>
      apply (bytes_at_write_other rsegs m a bs A2 bs2) in H; [ | lia | xlen | rewrite ?length_le1, ?length_le4; cbn [length Z.of_nat Pos.of_succ_nat]; dlia ]
  | H : wr_at rsegs m ?A2 ?n2 |- _ => apply (wr_at_write rsegs m A2 n2 (wa a) bs) in H
  | H : rw_cells rsegs m ?A2 ?cs2 |- _ =>
      apply (rw_cells_frame rsegs m A2 cs2 a bs) in H; [ | lia | xlen | unfold FC; simpl_sizes; dlia ]
  | H : stk rsegs m ?l2 ?h2 |- _ => apply (stk_write rsegs m l2 h2 a bs) in H; [ | lia | xlen ]
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
      lazymatch goal with HI : mem_inv rsegs m |- _ =>
        apply (mem_inv_store rsegs m (wa (t + k)) bs) in HI; [ | rewrite ?length_le1, ?length_le4; exact HS ] end;
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
      lazymatch goal with HI : mem_inv rsegs m |- _ =>
        apply (mem_inv_store rsegs m (wa p) bs) in HI; [ | rewrite ?length_le1, ?length_le4; exact HS ] end;
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

Ltac trap_off H :=
  exfalso; rewrite ?Z.shiftl_mul_pow2 in H by lia; try change (2 ^ 1) with 2 in H;
  rewrite ?Z.mod_small in H by lia; rewrite ?zb_lxor_ones in H by lia; lia.

Lemma L_epi : forall ra' t0 t1 t2 s0' s1' s2' s3' a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m,
  rw_cells rsegs m (bv_unsigned sp + -48) FC ->
  evt rsegs (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3
                                      s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m (seg_rom rsegs))
    (SS ra' t0 t1 t2 s0' s1' s2' s3' a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 0x157d8 m).
Proof.
  intros ra' t0 t1 t2 s0' s1' s2' s3' a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m FR. unfold SS, FC in *.
  zstep. zstep. zstep. zstep. zstep. zstep. zstep.
  apply evt_done. reflexivity.
Qed.

Lemma rel_stk : forall m, stk rsegs m lo (bv_unsigned sp + -48) -> rw_cells rsegs m (bv_unsigned sp + -48) FC ->
  stk rsegs m lo (bv_unsigned sp).
Proof.
  intros m S R. pose proof (stk_release rsegs m lo _ FC S R ltac:(lia)) as H.
  unfold FC in H. cbn [cells_size csize Nat.add] in H.
  replace (bv_unsigned sp) with (bv_unsigned sp + -48 + Z.of_nat 48) by lia. exact H.
Qed.

Lemma E_silent : forall ra' t0 t1 t2 s0' s1' s2' s3' a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m Tc,
  cur m Tc ->
  evt rsegs (QQ (silent Tc)) (SS ra' t0 t1 t2 s0' s1' s2' s3' (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 0x157d8 m).
Proof.
  intros ra' t0 t1 t2 s0' s1' s2' s3' a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m Tc HC. unpack HC.
  eapply evt_mono; [apply L_epi; exact FR|]. intros ms' ->.
  unfold QQ, next_post, silent. do 14 eexists. exists m. split; [reflexivity|].
  split; [exact HB|]. split; [exact WM|]. split; [apply rel_stk; assumption|]. split; [exact HI|]. exact MU.
Qed.

Lemma E_emit : forall ra' t0 t1 t2 s1' s2' s3' a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m Tc c p v,
  cur4 m Tc ->
  bytes_at rsegs m chp (le1 (Z_to_bv 64 c)) -> bytes_at rsegs m parp (le1 (Z_to_bv 64 p)) ->
  bytes_at rsegs m valp (le1 (Z_to_bv 64 v)) ->
  evt rsegs (QQ (1, (c, p, v), set4 Tc 456 0))
    (SS ra' t0 t1 t2 (Z_to_bv 64 t) s1' s2' s3' a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 0x157d0 m).
Proof.
  intros ra' t0 t1 t2 s1' s2' s3' a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m Tc c p v HC Bc Bp Bv.
  unpack HC. unfold SS.
  sst 456 4%nat. zstep.
  eapply evt_mono; [eapply L_epi; eassumption|]. intros ms' ->.
  unfold QQ, next_post. do 15 eexists. split; [reflexivity|].
  split; [eassumption|]. split; [eassumption|]. split; [apply rel_stk; assumption|]. split; [eassumption|].
  split; [eassumption|]. split; [eassumption|]. split; eassumption.
Qed.

Lemma L_rs : forall ra' t0 t1 t2 s1' s2' s3' a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m Tc,
  cur m Tc ->
  evt rsegs (QQ (resweep Tc)) (SS ra' t0 t1 t2 (Z_to_bv 64 t) s1' s2' s3' a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 0x15890 m).
Proof.
  intros ra' t0 t1 t2 s1' s2' s3' a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m Tc HC.
  pose proof HC as HC0. unpack HC. unfold SS. pose proof HL as HLT.
  r4 Tc 452. zl. zstep.
  if_cases HC1; zify_cond HC1.
  - assert (E : u32 Tc 452 = 0) by (apply s32_zero; Z.div_mod_to_equations; lia).
    replace (resweep Tc) with (silent Tc) by (unfold resweep; rewrite E; reflexivity).
    rewrite (proj2 (s32_zero Tc 452) E).
    eapply E_silent; exact HC0.
  - assert (N1 : u32 Tc 452 <> 0)
      by (intro E; apply (proj2 (s32_zero _ _)) in E; rewrite E in HC1; cbn in HC1; lia).
    r1 Tc 450. zl. zstep.
    if_cases HC2; zify_cond HC2.
    + replace (resweep Tc) with (silent Tc)
        by (unfold resweep; rewrite (proj2 (Z.eqb_neq _ 0) N1), (proj2 (Z.eqb_eq (tb Tc 450) 0)) by lia; reflexivity).
      zstep. zstep. eapply E_silent; exact HC0.
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
        eapply E_silent; pack.
      * assert (G : (u32 Tc 456 + 1) mod 4294967296 < u32 Tc 452) by lia.
        assert (Em : resweep Tc = silent (set4 Tc 456 (u32 Tc 456 + 1))).
        { unfold resweep. rewrite (proj2 (Z.eqb_neq _ 0) N1), (proj2 (Z.eqb_neq (tb Tc 450) 0)) by lia.
          rewrite (proj2 (Z.leb_gt _ _) G). reflexivity. }
        rewrite Em. zstep. zstep. eapply E_silent; pack.
Qed.

Ltac widen :=
  match goal with
  | MU : munch [(bv_unsigned sp + -48, bv_unsigned sp); (t, t + 460)] m0 ?m |- _ =>
      apply (munch_weaken [(bv_unsigned sp + -48, bv_unsigned sp); (t, t + 460)]
               [(bv_unsigned sp + -48, bv_unsigned sp); (t, t + 460); (chp, chp + 1); (parp, parp + 1); (valp, valp + 1)]) in MU;
      [ | intros x Hx; cbn [outside] in *; tauto ]
  end.

Variable EFF : reac_headamp_tx_effective_contract.

Lemma L_emitc : forall ra' t0 t1 t4 t5 t6 s3' a0 a3 a4 a5 a6 a7 m T1 c p j total,
  0 <= c < 2147483648 -> 0 <= p < 3 -> 0 <= j -> j + 1 <= total -> total <= 765 -> s32 T1 440 = j + 1 ->
  cur m T1 ->
  evt rsegs (QQ (emit_res T1 t c p j total))
    (SS ra' t0 t1 (Z_to_bv 64 c) (Z_to_bv 64 t) (Z_to_bv 64 valp) (Z_to_bv 64 total) s3' a0
        (Z_to_bv 64 chp) (Z_to_bv 64 parp) a3 a4 a5 a6 a7 (Z_to_bv 64 p) t4 t5 t6 0x158e0 m).
Proof.
  intros ra' t0 t1 t4 t5 t6 s3' a0 a3 a4 a5 a6 a7 m T1 c p j total Hc0 Hp0 Hj Hjt Htot HX HC.
  unpack HC. unfold SS. pose proof HL as HLT. widen.
  zstep. if_cases HT1; zify_cond HT1; [ exfalso; rewrite ?Z.mod_small in HT1 by lia; lia | try clear HT1 ].
  ost chp.
  zstep. if_cases HT2; zify_cond HT2; [ exfalso; rewrite ?Z.mod_small in HT2 by lia; lia | try clear HT2 ].
  ost parp.
  rewrite (le1_eqm c (c mod 256)) in * by (rewrite Z.mod_mod; lia).
  zstep. rewrite ?land_mod256. zstep. rewrite ?land_mod256. rewrite ?(Z.mod_small p 256) by lia.
  zstep. zstep.
  eapply evt_cut.
  { eapply EFF; [reflexivity | reflexivity | reflexivity | apply Z.mod_pos_bound; lia | lia |
                 right; split; [exact HL | split; [exact HB | exact H4]]]. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & ->).
  replace (ret_pc (Z_to_bv 64 88320)) with (Z_to_bv 64 88320) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  zstep. if_cases HT3; zify_cond HT3; [ exfalso; rewrite ?Z.mod_small in HT3 by lia; lia | try clear HT3 ].
  ost valp.
  r4 T1 440. zl. rewrite HX. zstep.
  if_cases HC1; zify_cond HC1; rewrite ?signed64_small in HC1 by lia.
  - replace (emit_res T1 t c p j total) with (1, (c mod 256, p, eff T1 t (c mod 256) p), set4 (setb T1 437 0) 456 0)
      by (unfold emit_res; rewrite (proj2 (Z.ltb_ge (j + 1) total)) by lia; reflexivity).
    sst 437 1%nat. zstep.
    eapply E_emit; [pack | eassumption | eassumption | eassumption].
  - replace (emit_res T1 t c p j total) with (1, (c mod 256, p, eff T1 t (c mod 256) p), set4 (set4 T1 444 11) 456 0)
      by (unfold emit_res; rewrite (proj2 (Z.ltb_lt (j + 1) total)) by lia; reflexivity).
    zstep. sst 444 4%nat. zstep.
    eapply E_emit; [pack | eassumption | eassumption | eassumption].
Qed.

Ltac wnorm j :=
  rewrite ?Z.shiftr_div_pow2 by lia; change (2 ^ 32) with 4294967296; change (2 ^ 63) with 9223372036854775808;
  rewrite (div3_hi j), (div3_sign j) by lia; rewrite ?Z.add_0_r;
  repeat match goal with
  | |- context [Z.shiftl ?x 1] => rewrite (Z.shiftl_mul_pow2 x 1) by lia; change (2 ^ 1) with 2
  | |- context [?x mod 18446744073709551616] => rewrite (Z.mod_small x 18446744073709551616) by (Z.div_mod_to_equations; lia)
  | |- context [bv_swrap 32 ?x] => rewrite (swrap32_id x) by (Z.div_mod_to_equations; lia)
  end.

Lemma L_walk : forall n j ra' t2 s3' t3 t4 t5 t6 m Tc bs o total,
  n = Z.to_nat (total - j) -> 0 <= j < total -> total <= 765 -> 0 <= bs < 256 -> 0 <= o < 256 ->
  cur m Tc ->
  evt rsegs (QQ (walk Tc t bs o total j n))
    (SS ra' (Z_to_bv 64 1431655766) (Z_to_bv 64 47) t2 (Z_to_bv 64 t) (Z_to_bv 64 valp) (Z_to_bv 64 total) s3'
        (Z_to_bv 64 total) (Z_to_bv 64 chp) (Z_to_bv 64 parp) (Z_to_bv 64 j) (Z_to_bv 64 (t + 144))
        (Z_to_bv 64 bs) (Z_to_bv 64 o) (Z_to_bv 64 (18446744073709551615 - (t + 144))) t3 t4 t5 t6 0x1582c m).
Proof.
  induction n as [|n IH];
    intros j ra' t2 s3' t3 t4 t5 t6 m Tc bs o total En Hj Htot Hbs Ho HC; [lia|].
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
    eapply L_emitc; [lia | lia | lia | lia | lia | exact HX1 | exact HC0].
  - zstep.
    if_cases HC2; zify_cond HC2; rewrite ?signed64_small in HC2 by lia.
    + replace (carried T1 bs o j) with false
        by (unfold carried; rewrite (proj2 (Z.eqb_neq o 0)), (proj2 (Z.leb_gt _ 47)) by lia; reflexivity).
      cbv iota. zstep.
      if_cases HC4; zify_cond HC4.
      * rewrite (proj2 (Z.eqb_neq (j + 1) total)) by lia.
        eapply IH; [lia | lia | lia | lia | lia | exact HC0].
      * rewrite (proj2 (Z.eqb_eq (j + 1) total)) by lia.
        sst 437 1%nat. eapply L_rs; pack.
    + zstep. if_cases HT1; zify_cond HT1; [ trap_off HT1 | try clear HT1 ].
      zstep. zstep. zstep. if_cases HT2; zify_cond HT2; [ trap_off HT2 | try clear HT2 ].
      zstep. if_cases HT3; zify_cond HT3; [ trap_off HT3 | try clear HT3 ].
      zstep. zstep. zstep. if_cases HT4; zify_cond HT4; [ trap_off HT4 | try clear HT4 ].
      zstep.
      rewrite ?Z.shiftl_mul_pow2 by lia. try change (2 ^ 1) with 2.
      r1 T1 (144 + 3 * (bs + j / 3) + j mod 3). zl. zstep.
      if_cases HC3; zify_cond HC3.
      * replace (carried T1 bs o j) with true
          by (unfold carried; rewrite (proj2 (Z.eqb_neq o 0)), (proj2 (Z.leb_le _ 47)),
                (proj2 (Z.eqb_neq (tb T1 (144 + 3 * (bs + j / 3) + j mod 3)) 0)) by lia; reflexivity).
        eapply L_emitc; [lia | lia | lia | lia | lia | exact HX1 | exact HC0].
      * replace (carried T1 bs o j) with false
          by (unfold carried; rewrite (proj2 (Z.eqb_neq o 0)), (proj2 (Z.leb_le _ 47)),
                (proj2 (Z.eqb_eq (tb T1 (144 + 3 * (bs + j / 3) + j mod 3)) 0)) by lia; reflexivity).
        cbv iota. zstep.
        if_cases HC4; zify_cond HC4.
        -- rewrite (proj2 (Z.eqb_neq (j + 1) total)) by lia.
           eapply IH; [lia | lia | lia | lia | lia | exact HC0].
        -- rewrite (proj2 (Z.eqb_eq (j + 1) total)) by lia.
           sst 437 1%nat. eapply L_rs; pack.
Qed.

Lemma L_after_scan : forall ra' t0 t1 t2 s2' s3' a0 a3 a4 a5 a6 a7 t3 t4 t5 t6 m T,
  cur m T -> (tb T 437 <> 0 -> 0 <= s32 T 440) ->
  evt rsegs (QQ (after_scan T t))
    (SS ra' t0 t1 t2 (Z_to_bv 64 t) (Z_to_bv 64 valp) s2' s3' a0 (Z_to_bv 64 chp) (Z_to_bv 64 parp)
        a3 a4 a5 a6 a7 t3 t4 t5 t6 0x1575c m).
Proof.
  intros ra' t0 t1 t2 s2' s3' a0 a3 a4 a5 a6 a7 t3 t4 t5 t6 m T HC HX.
  pose proof HC as HC0. unpack HC. unfold SS. pose proof HL as HLT.
  r1 T 437. zl. zstep.
  if_cases HC1; zify_cond HC1.
  - replace (after_scan T t) with (resweep T)
      by (unfold after_scan; rewrite (proj2 (Z.eqb_eq (tb T 437) 0)) by lia; reflexivity).
    eapply L_rs; exact HC0.
  - assert (N437 : (tb T 437 =? 0) = false) by (apply Z.eqb_neq; lia).
    specialize (HX ltac:(lia)).
    r4 T 444. zl. zstep.
    if_cases HC2; zify_cond HC2.
    + assert (Wle : s32 T 444 <= 0)
        by (apply andb_false_iff in HC2; destruct HC2 as [HC2|HC2]; apply Z.ltb_ge in HC2; Z.div_mod_to_equations; lia).
      r4 T 440. zl. zstep. zstep.
      rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
      replace (tb T 437 * 2 + tb T 437) with (3 * tb T 437) by lia.
      zstep. zstep.
      if_cases HC5; zify_cond HC5; rewrite ?signed64_small in HC5 by lia.
      * zstep.
        if_cases HC3; zify_cond HC3; rewrite ?signed64_small in HC3 by lia; [|exfalso; lia].
        replace (after_scan T t) with (resweep (setb T 437 0))
          by (unfold after_scan; rewrite N437, (proj2 (Z.ltb_ge 0 _) Wle), (proj2 (Z.leb_le _ _)) by lia; reflexivity).
        sst 437 1%nat. eapply L_rs; pack.
      * zstep. zstep.
        if_cases HC3; zify_cond HC3; rewrite ?signed64_small in HC3 by lia.
        -- replace (after_scan T t) with (resweep (setb T 437 0))
             by (unfold after_scan; rewrite N437, (proj2 (Z.ltb_ge 0 _) Wle), (proj2 (Z.leb_le _ _)) by lia; reflexivity).
           sst 437 1%nat. eapply L_rs; pack.
        -- replace (after_scan T t)
             with (walk T t (tb T 436) (tb T 448) (3 * tb T 437) (s32 T 440) (Z.to_nat (3 * tb T 437 - s32 T 440)))
             by (unfold after_scan; rewrite N437, (proj2 (Z.ltb_ge 0 _) Wle), (proj2 (Z.leb_gt _ _)) by lia; reflexivity).
           zstep. r1 T 436. zl. r1 T 448. zl. zstep. zstep. zstep. zstep.
           rewrite ?(zb_lxor_ones (t + 144)) by lia.
           eapply L_walk; [reflexivity | lia | lia | lia | lia | exact HC0].
    + assert (Wgt : 0 < s32 T 444) by (Z.div_mod_to_equations; lia).
      replace (after_scan T t) with (silent (set4 T 444 (s32 T 444 - 1)))
        by (unfold after_scan; rewrite N437, (proj2 (Z.ltb_lt 0 _) Wgt); reflexivity).
      zstep. zstep.
      sst 444 4%nat.
      match goal with |- context [le4 (Z_to_bv 64 ?E)] =>
        rewrite (le4_eqm E (s32 T 444 - 1)) in * by (Z.div_mod_to_equations; lia) end.
      zstep. eapply E_silent; pack.
Qed.

Ltac weq := first [ reflexivity | f_equal; lia | f_equal; rewrite zb_lxor_ones by lia; lia
                  | apply Z_to_bv_eqm; vm_compute; reflexivity ].

Lemma L_scan : forall n i ra' t0 t1 t2 s2' s3' a0 a3 a4 a5 a6 a7 t3 t4 t5 t6 m T,
  n = Z.to_nat (144 - i) -> 0 <= i < 144 ->
  a0 = Z_to_bv 64 i -> a3 = Z_to_bv 64 (t + i) -> a4 = Z_to_bv 64 i -> a5 = Z_to_bv 64 (t + 288) ->
  a6 = Z_to_bv 64 (288 + i) -> a7 = Z_to_bv 64 (18446744073709551615 - (t + 288)) ->
  t0 = Z_to_bv 64 12297829382473034411 -> t1 = Z_to_bv 64 12297829383904690176 -> t2 = Z_to_bv 64 144 ->
  cur m T -> (tb T 437 <> 0 -> 0 <= s32 T 440) ->
  evt rsegs (QQ (match first_dirty_from T i n with Some k => edge_res T k | None => after_scan T t end))
    (SS ra' t0 t1 t2 (Z_to_bv 64 t) (Z_to_bv 64 valp) s2' s3' a0 (Z_to_bv 64 chp) (Z_to_bv 64 parp)
        a3 a4 a5 a6 a7 t3 t4 t5 t6 0x156fc m).
Proof.
  induction n as [|n IH];
    intros i ra' t0 t1 t2 s2' s3' a0 a3 a4 a5 a6 a7 t3 t4 t5 t6 m T En Hi -> -> -> -> -> -> -> -> -> HC HX; [lia|].
  rewrite fd_step. pose proof HC as HC0. unpack HC. unfold SS. pose proof HL as HLT.
  zstep. zstep. zstep. zstep. zstep. zstep.
  rewrite ?(scan_q i) by lia.
  if_cases HT1; zify_cond HT1; [ trap_off HT1 | try clear HT1 ].
  zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
  if_cases HT2; zify_cond HT2; [ rewrite (scan_r i) in HT2 by lia; trap_off HT2 | try clear HT2 ].
  zstep.
  r1 T (288 + i). zl. zstep.
  if_cases HC1; zify_cond HC1.
  - rewrite (proj2 (Z.eqb_neq _ 0)) by lia. cbv iota. clear HC1.
    widen.
    sst (288 + i) 1%nat.
    zstep. if_cases HE1; zify_cond HE1; [ exfalso; rewrite ?Z.mod_small in HE1 by lia; lia | try clear HE1 ].
    ost chp.
    zstep. if_cases HE2; zify_cond HE2; [ exfalso; rewrite ?Z.mod_small in HE2 by lia; lia | try clear HE2 ].
    zstep. zstep. zstep. zstep. zstep. rewrite ?(scan_q i) by lia.
    zstep. zstep. zstep.
    rewrite ?Z.shiftl_mul_pow2 by lia. try change (2 ^ 1) with 2.
    repeat match goal with
    | |- context [?x mod 18446744073709551616] => rewrite (Z.mod_small x 18446744073709551616) by (Z.div_mod_to_equations; lia)
    | |- context [bv_swrap 32 ?x] => rewrite (swrap32_id x) by (Z.div_mod_to_equations; lia)
    end.
    replace (i - i / 3 - i / 3 * 2) with (i mod 3) by (Z.div_mod_to_equations; lia).
    zstep.
    ost parp.
    zstep. if_cases HE3; zify_cond HE3; [ exfalso; rewrite ?Z.shiftl_mul_pow2 in HE3 by lia; rewrite ?Z.mod_small in HE3 by (Z.div_mod_to_equations; lia); Z.div_mod_to_equations; lia | try clear HE3 ].
    zstep. if_cases HE4; zify_cond HE4; [ exfalso; rewrite ?Z.shiftl_mul_pow2 in HE4 by lia; rewrite ?Z.mod_small in HE4 by (Z.div_mod_to_equations; lia); Z.div_mod_to_equations; lia | try clear HE4 ].
    zstep. if_cases HE5; zify_cond HE5; [ exfalso; rewrite ?Z.mod_small in HE5 by lia; lia | try clear HE5 ].
    zstep. if_cases HE6; zify_cond HE6; [ exfalso; rewrite ?Z.shiftl_mul_pow2 in HE6 by lia; rewrite ?Z.mod_small in HE6 by (Z.div_mod_to_equations; lia); Z.div_mod_to_equations; lia | try clear HE6 ].
    zstep. if_cases HE7; zify_cond HE7; [ exfalso; rewrite ?Z.mod_small in HE7 by lia; lia | try clear HE7 ].
    match goal with H : bytes_at rsegs ?mm t ?X |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      let HL2 := fresh "HL2" in
      assert (HL2 : length X = 460%nat) by (eassumption);
      let R := fresh "R" in pose proof (rd1 mm t X i H HL2 ltac:(lia)) as R
    end.
    zl.
    match goal with |- context [tb ?X i] =>
      replace (tb X i) with (tb T i) by (symmetry; apply (tb_setb_out T (288 + i) 0 i); lia) end.
    ost valp.
    eapply E_emit; [pack | eassumption | eassumption | eassumption].
  - rewrite (proj2 (Z.eqb_eq _ 0)) by lia. cbv iota.
    zstep. rewrite swrap32_id by lia. zstep. zstep. zstep. zstep.
    if_cases HC2; zify_cond HC2.
    + eapply IH; [lia | lia | weq .. | exact HC0 | exact HX].
    + assert (n = 0%nat) by lia. subst n. cbn [first_dirty_from].
      eapply L_after_scan; [exact HC0 | exact HX].
Qed.

Ltac scan_setup :=
  zstep; zstep; zstep; zstep; zstep; zstep; zstep; zstep; zstep; zstep; zstep; zstep.

Lemma L_body : forall t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 m T,
  cur m T -> (tb T 437 <> 0 -> 0 <= s32 T 440) ->
  evt rsegs (QQ (next_model T t))
    (SS ra t0 t1 t2 s0 s1 s2 s3 (Z_to_bv 64 t) (Z_to_bv 64 chp) (Z_to_bv 64 parp) (Z_to_bv 64 valp)
        a4 a5 a6 a7 t3 t4 t5 t6 0x156a8 m).
Proof.
  intros t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 m T HC HX.
  pose proof HC as HC0. unpack HC. unfold SS. pose proof HL as HLT.
  zstep. if_cases HT1; zify_cond HT1; [ exfalso; rewrite ?Z.mod_small in HT1 by lia; lia | try clear HT1 ].
  zstep. zstep. zstep. if_cases HT2; zify_cond HT2;
  [ exfalso; replace (Z.land t 3) with (t mod 4) in HT2
      by (symmetry; change 3 with (Z.ones 2); rewrite Z.land_ones by lia; reflexivity); lia | try clear HT2 ].
  zstep.
  r4 T 432. zl. zstep.
  if_cases HC1; zify_cond HC1.
  - assert (NA : u32 T 432 <> 0)
      by (intro E; apply (proj2 (s32_zero _ _)) in E; rewrite E in HC1; cbn in HC1; lia).
    replace (next_model T t)
      with (match first_dirty_from T 0 144 with Some k => edge_res T k | None => after_scan T t end)
      by (unfold next_model; rewrite (proj2 (Z.eqb_neq _ 0) NA); reflexivity).
    scan_setup.
    eapply (L_scan _ 0); [reflexivity | lia | weq .. | exact HC0 | exact HX].
  - assert (ZA : u32 T 432 = 0) by (apply s32_zero; Z.div_mod_to_equations; lia).
    r1 T 437. zl. zstep.
    if_cases HC2; zify_cond HC2.
    + replace (next_model T t) with (silent T)
        by (unfold next_model; rewrite ZA, (proj2 (Z.eqb_eq (tb T 437) 0)) by lia; reflexivity).
      assert (E0 : tb T 437 = 0) by lia. rewrite E0.
      eapply E_silent; exact HC0.
    + replace (next_model T t)
        with (match first_dirty_from T 0 144 with Some k => edge_res T k | None => after_scan T t end)
        by (unfold next_model; rewrite ZA, (proj2 (Z.eqb_neq (tb T 437) 0)) by lia; reflexivity).
      scan_setup.
      eapply (L_scan _ 0); [reflexivity | lia | weq .. | exact HC0 | exact HX].
Qed.

End Next.

Theorem reac_headamp_tx_next_holds : reac_headamp_tx_effective_contract -> reac_headamp_tx_next_contract.
Proof.
  intros EFF.
  unfold reac_headamp_tx_next_contract, REAC_HEADAMP_TX_NEXT, REAC_HEADAMP_TX_NEXT_FRAME.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo t chp parp valp T E0 E1 E2 E3 Ht H4 HL HB HW HWc HWp HWv HI Zc Zp Zv Dc Dp Dv Ncp Ncv Npv
    ST LO Kt Kc Kp Kv HX.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. change (2 ^ Z.of_N 64) with 18446744073709551616 in Rsp.
  pose proof ST as (Hlo & _ & _).
  pose proof (bytes_at_bound rsegs m t T HB) as Hb. rewrite HL in Hb. change (Z.of_nat 460) with 460 in Hb.
  pose proof HWc as (Hc1 & Hc2 & _). pose proof HWp as (Hp1 & Hp2 & _). pose proof HWv as (Hv1 & Hv2 & _).
  assert (SEP : SEPP sp lo t chp parp valp) by (unfold SEPP; tauto).
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (t, t + 460)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 48%nat ST.
  subst a0 a1 a2 a3.
  zstep. zstep. zstep. zstep. zstep. zstep.
  clear Dc Dp Dv Ncp Ncv Npv Kt Kc Kp Kv.
  eapply L_body.
  all: try eassumption.
  all: try lia.
  unfold cur, FC.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))))); eassumption.
Qed.
