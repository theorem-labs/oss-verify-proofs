From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Lib Require Import PropExec MState Mem Cells Exec Frame Tac Bytes ZBridge Step Arr Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U.Prog Require Import HeadampModel SlotNeeds_c LLVMFuzzerTestOneInput_c GrantSlotPlan SlotBridge SegSetModel.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U.Prog Require Import reac_headamp_tx_set_c reac_headamp_tx_effective_c reac_headamp_default_c.
Import ListNotations.
Open Scope Z_scope.

Ltac fix_ret :=
  match goal with |- context [ret_pc (Z_to_bv 64 ?n)] => rewrite (ret_pc_even n) by (first [lia | reflexivity]) end.

Ltac bool_prop H :=
  repeat first [ rewrite andb_true_iff in H | rewrite andb_false_iff in H | rewrite orb_true_iff in H
               | rewrite orb_false_iff in H | rewrite Z.ltb_lt in H | rewrite Z.ltb_ge in H
               | rewrite Z.leb_le in H | rewrite Z.leb_gt in H | rewrite Z.eqb_eq in H | rewrite Z.eqb_neq in H ].

Lemma pl_read : forall m p pl k, bytes_at rsegs m p pl -> (k < length pl)%nat ->
  ov_read_bytes rsegs m (wa (p + Z.of_nat k)) 1 = Some [nth k pl (Z_to_bv 8 0)].
Proof.
  intros m p pl k H Hk. rewrite (bytes_at_read rsegs m p pl (Z.of_nat k) 1 H) by lia. rewrite Nat2Z.id.
  rewrite (firstn1_skipn_nth pl k (Z_to_bv 8 0)) by lia. reflexivity.
Qed.

Lemma byte_range : forall b : byte, 0 <= bv_unsigned b < 256.
Proof. intros b. pose proof (bv_unsigned_in_range 8 b) as R. replace (bv_modulus 8) with 256 in R by reflexivity. exact R. Qed.

Ltac callS SET HTl HTB HTW HT4 :=
  eapply evt_cut;
  [ eapply SET; [reflexivity | reflexivity | reflexivity | reflexivity | lia | lia | lia | exact HTl | exact HTB | exact HTW
                | lia | exact HT4]
  | let ms' := fresh "ms" in let PO := fresh "PO" in let EL := fresh "EL" in let mm := fresh "m" in
    let rr := fresh "r" in
    intros ms' (? & ? & ? & rr & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & mm & -> & PO);
    fix_ret;
    lazymatch type of PO with
    | (if ?B then _ else _) =>
        destruct B eqn:EL;
        [ destruct PO as [-> PO] | destruct PO as [-> PO]; subst mm ];
        let ELp := fresh "ELp" in pose proof EL as ELp; unfold legalb in ELp; bool_prop ELp;
        try (exfalso; lia)
    end ].

Ltac callE EFF HTl HTB HT4 :=
  eapply evt_cut;
  [ eapply EFF; [reflexivity | reflexivity | reflexivity | lia | lia | right; split; [exact HTl | split; [exact HTB | exact HT4]]]
  | let ms' := fresh "ms" in
    intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->); fix_ret;
    rewrite ?eff_p3 by lia ].

Ltac callD DFL :=
  eapply evt_cut;
  [ eapply DFL; [reflexivity | lia]
  | let ms' := fresh "ms" in
    intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->); fix_ret;
    unfold dflt; ncond ].

Ltac drv SET EFF DFL HTl HTB HTW HT4 :=
  repeat (lazymatch goal with
    | |- evt _ _ (MS _ _ (Z_to_bv 64 78892) _ _ _ _) => fail
    | |- evt _ _ (MS _ _ (Z_to_bv 64 81108) _ _ _ _) => fail
    | |- evt _ _ (MS _ _ (Z_to_bv 64 81184) _ _ _ _) => fail
    | |- evt _ _ (MS _ _ (Z_to_bv 64 87240) _ _ _ _) => callS SET HTl HTB HTW HT4
    | |- evt _ _ (MS _ _ (Z_to_bv 64 87448) _ _ _ _) => callE EFF HTl HTB HT4
    | |- evt _ _ (MS _ _ (Z_to_bv 64 87432) _ _ _ _) => callD DFL
    | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => brx
    | |- evt _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => zstep
    end).

Ltac fin_r :=
  apply evt_done; do 25 eexists; split; [reflexivity|];
  try (match goal with H : (_ && legalb _ _) = _ |- _ => rewrite H end);
  do 6 (split; [first [reflexivity | word_eq_tac] |]);
  split; [intros ?; first [reflexivity | word_eq_tac | discriminate] |];
  first [ assumption | reflexivity ].

Ltac qprem := first [ reflexivity | word_eq_tac | lia | eassumption ].

Section R.
Hypothesis SET : reac_headamp_tx_set_contract.
Hypothesis EFF : reac_headamp_tx_effective_contract.
Hypothesis DFL : reac_headamp_default_contract.

Lemma read_block : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (t p : Z) (pl : list byte) (pos : nat) (T : list byte),
  s0 = Z_to_bv 64 t -> s11 = Z_to_bv 64 (p + Z.of_nat pos) -> s9 = Z_to_bv 64 (Z.of_nat (length pl) - Z.of_nat pos) ->
  s1 = Z_to_bv 64 2 -> s10 = Z_to_bv 64 1 ->
  (pos <= length pl)%nat -> 0 < p -> p + Z.of_nat (length pl) < 2 ^ 63 -> bytes_at rsegs m p pl ->
  0 < t -> t mod 4 = 0 -> length T = 460%nat -> bytes_at rsegs m t T -> wr_at rsegs m t 460 ->
  evt rsegs (fun ms' =>
    let '((c, q, v), pos') := cell_rd pl pos in
    exists ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' m',
      ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                    s2 s3' s4' s5' s6' s7' s8' s9' s10 s11' t3' t4' t5' t6')
               F (Z_to_bv 64 0x1342c) fc None m' (seg_rom rsegs) /\
      s11' = Z_to_bv 64 (p + Z.of_nat pos') /\ s9' = Z_to_bv 64 (Z.of_nat (length pl) - Z.of_nat pos') /\
      s4' = Z_to_bv 64 c /\ s6' = Z_to_bv 64 v /\ s5' = Z_to_bv 64 q /\
      s7' = Z_to_bv 64 (if (c <? 48) && legalb q v then 0 else -1) /\
      ((c <? 48) && legalb q v = true -> s3' = Z_to_bv 64 1) /\
      (if (c <? 48) && legalb q v
       then bytes_at rsegs m' t (set_T T c q v) /\ munch [(t, t + 460)] m m' /\ wmono rsegs m m'
       else m' = m))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x132f0) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m t p pl pos T -> -> -> -> -> Hpos Hp0 Hpn HPB Ht HT4 HTl HTB HTW.
  pose proof (bytes_at_bound _ _ _ _ HTB) as Htb. rewrite HTl in Htb.
  destruct (Nat.le_gt_cases (pos + 3) (length pl)) as [H3|H3].
  - rewrite cell_rd_3 by lia. cbv beta iota zeta.
    pose proof (pl_read m p pl pos HPB ltac:(lia)) as HR0.
    pose proof (pl_read m p pl (S pos) HPB ltac:(lia)) as HR1.
    pose proof (pl_read m p pl (S (S pos)) HPB ltac:(lia)) as HR2.
    pose proof (byte_range (nth pos pl (Z_to_bv 8 0))) as B0.
    pose proof (byte_range (nth (S pos) pl (Z_to_bv 8 0))) as B1.
    pose proof (byte_range (nth (S (S pos)) pl (Z_to_bv 8 0))) as B2.
    unfold pbz.
    drv SET EFF DFL HTl HTB HTW HT4.
    all: fin_r.
  - assert (length pl = pos \/ length pl = (pos + 1)%nat \/ length pl = (pos + 2)%nat) as [E|[E|E]] by lia.
    + rewrite cell_rd_0 by lia. cbv beta iota zeta.
      drv SET EFF DFL HTl HTB HTW HT4.
      all: fin_r.
    + rewrite cell_rd_1 by lia. cbv beta iota zeta.
      pose proof (pl_read m p pl pos HPB ltac:(lia)) as HR0.
      pose proof (byte_range (nth pos pl (Z_to_bv 8 0))) as B0.
      unfold pbz.
      drv SET EFF DFL HTl HTB HTW HT4.
      all: fin_r.
    + rewrite cell_rd_2 by lia. cbv beta iota zeta.
      pose proof (pl_read m p pl pos HPB ltac:(lia)) as HR0.
      pose proof (pl_read m p pl (S pos) HPB ltac:(lia)) as HR1.
      pose proof (byte_range (nth pos pl (Z_to_bv 8 0))) as B0.
      pose proof (byte_range (nth (S pos) pl (Z_to_bv 8 0))) as B1.
      unfold pbz.
      drv SET EFF DFL HTl HTB HTW HT4.
      all: fin_r.
Qed.

End R.
