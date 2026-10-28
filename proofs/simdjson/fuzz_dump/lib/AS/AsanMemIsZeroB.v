(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.AS Require Import SumsLib Sums_codeB.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.AS Require Import PropExec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition memisz_words : list (bv 32) :=
  [W_64f28; W_64f2c; W_64f30; W_64f34; W_64f38; W_64f3c; W_64f40; W_64f44;
   W_64f48; W_64f4c; W_64f50; W_64f54; W_64f58; W_64f5c; W_64f60; W_64f64;
   W_64f68; W_64f6c; W_64f70; W_64f74; W_64f78; W_64f7c; W_64f80; W_64f84;
   W_64f88; W_64f8c; W_64f90; W_64f94; W_64f98; W_64f9c; W_64fa0; W_64fa4;
   W_64fa8; W_64fac; W_64fb0; W_64fb4; W_64fb8; W_64fbc; W_64fc0].

Definition memisz_clob : list reg := [10; 11; 12; 13; 14; 15; 16].

Definition memisz_clob' : list reg := [1; 2; 10; 11; 12; 13; 14; 15; 16].

Lemma land_m8 : forall a, (0 <= a < 2 ^ 64)%Z -> Z.land a (2 ^ 64 - 2 ^ 3) = (a - a mod 8)%Z.
Proof.
  intros a Ha.
  replace (2 ^ 64 - 2 ^ 3)%Z with (Z.ldiff (Z.ones 64) (Z.ones 3)).
  2:{ rewrite Z.ldiff_land, <- Z.sub_land_same_l, Z.land_ones by lia.
      rewrite Z.ones_mod_pow2 by lia. rewrite !Z.ones_equiv. lia. }
  rewrite Z.ldiff_land, Z.land_assoc, Z.land_ones by lia.
  rewrite Z.mod_small by lia.
  rewrite <- Z.ldiff_land, Z.ldiff_ones_r by lia.
  rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia.
  pose proof (Z.div_mod a (2 ^ 3) ltac:(lia)). change (2 ^ 3)%Z with 8%Z in *. lia.
Qed.

Lemma v_andi_m8 : forall (a : word) d,
  (0 <= bv_unsigned a + d < 2 ^ 64)%Z ->
  v_andi (at_ a d) (-8) = at_ a (d - (bv_unsigned a + d) mod 8).
Proof.
  intros a d Hd. unfold v_andi, at_. f_equal.
  change (bv_wrap 64 (-8)) with (2 ^ 64 - 2 ^ 3)%Z.
  rewrite u_Z2bv by lia. rewrite land_m8 by lia. lia.
Qed.

Lemma rdn_all1 : forall segs m n (a : word) b,
  (bv_unsigned a + Z.of_nat n <= 2 ^ 64)%Z ->
  (forall x : word, (bv_unsigned a <= bv_unsigned x < bv_unsigned a + Z.of_nat n)%Z ->
     rdn segs m x 1 = Some [b]) ->
  rdn segs m a n = Some (repeat b n).
Proof.
  intros segs m n; induction n as [|n IH]; intros a b Hnw Hall; [reflexivity|].
  pose proof (Hall a ltac:(lia)) as R. cbn [rdn repeat] in R |- *.
  destruct (match m a with Some b0 => Some b0 | None => seg_rom segs a end) as [b0|]; [|discriminate].
  injection R as ->.
  destruct n as [|n'].
  - reflexivity.
  - assert (Hu1 : bv_unsigned (a + 1) = (bv_unsigned a + 1)%Z) by (apply u_add1; lia).
    rewrite (IH (a + 1) b) by (rewrite Hu1; first [lia | intros x Hx; apply Hall; lia]).
    reflexivity.
Qed.

Lemma regs_agree_upd_same : forall (C : regset) regs regs' (r : reg) v,
  regs_agree C regs regs' -> getr regs r = v -> r <> 0 -> regs_agree C regs (regupd regs' r v).
Proof.
  intros C regs regs' r v AG Hv Hnz x Hx.
  destruct (decide (x = r)) as [->|Hne].
  - rewrite getr_same by exact Hnz. symmetry. exact Hv.
  - rewrite getr_other by exact Hne. apply AG, Hx.
Qed.

Lemma regs_agree_strengthen : forall (l l' : list reg) regs regs',
  regs_agree (fun r => In r l') regs regs' ->
  (forall r, In r l' -> ~ In r l -> getr regs' r = getr regs r) ->
  regs_agree (fun r => In r l) regs regs'.
Proof.
  intros l l' regs regs' AG E r Hr.
  destruct (In_dec (fun x y : reg => decide (x = y)) r l') as [Hin|Hnin].
  - apply E; assumption.
  - apply AG, Hnin.
Qed.

Section MEMISZERO.
  Variable segs : list Segment.
  Variable base : word.
  Variable mem : word -> option byte.
  Variables beg sp : word.
  Variable N : Z.
  Variable rom : word -> option byte.
  Hypothesis HCODE : code_at segs base 0 memisz_words.
  Hypothesis HN : (0 <= N <= 2 ^ 40)%Z.
  Hypothesis Hnw : (bv_unsigned beg + N + 8 <= 2 ^ 64)%Z.
  Hypothesis Hsp : (16 <= bv_unsigned sp)%Z.
  Hypothesis Hstk : store_ok segs mem (at_ sp (-8)) 8 = true.
  Hypothesis Hdisj : (bv_unsigned beg + N <= bv_unsigned sp - 8 \/ bv_unsigned sp <= bv_unsigned beg)%Z.
  Hypothesis Hz : forall a : word,
      (bv_unsigned beg <= bv_unsigned a < bv_unsigned beg + N)%Z -> rdn segs mem a 1 = Some [Z_to_bv 8 0].

  #[local] Abbreviation B := (bv_unsigned beg).
  #[local] Abbreviation Z0 := (Z_to_bv 64 0).
  #[local] Abbreviation CL := (fun r => In r memisz_clob').

  Definition dAB : Z := 7 - (B + 7) mod 8.
  Definition dAE : Z := N - (B + N) mod 8.

  Definition mem1 (ra : word) : word -> option byte := wbytes mem (at_ sp (-8)) (word_to_le_bytes 8 ra).

  Lemma dAB_range : (0 <= dAB <= 7)%Z.
  Proof. unfold dAB. pose proof (Z.mod_pos_bound (B + 7) 8 ltac:(lia)). lia. Qed.

  Lemma dAE_range : (N - 7 <= dAE <= N)%Z /\ (0 <= B + dAE)%Z.
  Proof.
    unfold dAE. pose proof (u64_range beg). pose proof (Z.mod_pos_bound (B + N) 8 ltac:(lia)).
    pose proof (Z.div_mod (B + N) 8 ltac:(lia)). nia.
  Qed.

  Lemma rd1 : forall ra j, (0 <= j < N)%Z -> rdn segs (mem1 ra) (at_ beg j) 1 = Some [Z_to_bv 8 0].
  Proof.
    intros ra j Hj. pose proof (u64_range beg). pose proof (u64_range sp). unfold mem1.
    rewrite rdn_wbytes_out; rewrite ?length_N_to_le_bytes, ?at_u; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; try lia.
    apply Hz. rewrite at_u; lia.
  Qed.

  Lemma rd8 : forall ra j, (0 <= j)%Z -> (j + 8 <= N)%Z -> rdn segs (mem1 ra) (at_ beg j) 8 = Some (zeros 8).
  Proof.
    intros ra j Hj H8. pose proof (u64_range beg). unfold zeros. apply rdn_all1; [rewrite at_u; cbn; lia|].
    intros x Hx. rewrite at_u in Hx by lia. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hx.
    replace x with (at_ beg (bv_unsigned x - B)).
    - apply rd1. lia.
    - unfold at_. rewrite <- (Z_to_bv_bv_unsigned 64 x) at 2. f_equal. lia.
  Qed.

  Lemma rd_ra : forall ra, rdn segs (mem1 ra) (at_ sp (-8)) 8 = Some (word_to_le_bytes 8 ra).
  Proof. intros ra. unfold mem1. apply rdn_wbytes_hit8. pose proof (u64_range sp). rewrite at_u; lia. Qed.

  Ltac get_code :=
    let HC := fresh "HC" in
    pose proof HCODE as HC; cbn [code_at memisz_words Z.add Pos.add Pos.succ] in HC;
    destruct HC as (C0 & C4 & C8 & C12 & C16 & C20 & C24 & C28 & C32 & C36 & C40 & C44 & C48 & C52 & C56
                    & C60 & C64 & C68 & C72 & C76 & C80 & C84 & C88 & C92 & C96 & C100 & C104 & C108 & C112
                    & C116 & C120 & C124 & C128 & C132 & C136 & C140 & C144 & C148 & C152 & _).

  Ltac mlbu F D :=
    chain_step; [reflexivity
      | eapply step_lbu with (b := Z_to_bv 8 0);
        [exact F | reflexivity | exact D
        | gres; rwH; imm_norm; rewrite ?at_addi; apply rd1; lia]
      | step_simpl]; vn.

  Ltac mld F D :=
    chain_step; [reflexivity
      | eapply step_ld with (bs := zeros 8) (v := Z_to_bv 64 0);
        [exact F | reflexivity | exact D
        | gres; rwH; imm_norm; rewrite ?at_addi; apply rd8; lia
        | reflexivity]
      | step_simpl]; vn.

  Ltac ra_solve :=
    repeat (first [ apply regs_agree_upd; [in_list|]
                  | apply regs_agree_upd_same; [| rwH; rewrite ?at_0; reflexivity | let X := fresh in intros X; discriminate X] ]);
    first [apply regs_agree_refl | assumption].

  Lemma fin_run : forall regs (ret : word),
    ret_ok ret -> getr regs 2 = at_ sp (-16) -> getr regs 11 = Z0 ->
    exists regs',
      msteps segs (mkst regs (at_ base 140) (mem1 ret) rom) (mkst regs' ret (mem1 ret) rom)
      /\ regs_agree CL regs regs' /\ getr regs' 10 = Z_to_bv 64 1 /\ getr regs' 2 = sp /\ getr regs' 1 = ret.
  Proof.
    get_code. intros regs ret Hret H2 H11. pose proof (u64_range sp).
    eexists. split; [|split; [|split; [|split]]].
    - an C140 D_64fb4.
      chain_step; [reflexivity
        | eapply step_ld with (v := ret);
          [exact C144 | reflexivity | exact D_64fb8
          | gres; rwH; imm_norm; rewrite ?at_addi; zlit_at; apply rd_ra
          | apply bytes_le_to_Z_8]
        | step_simpl]; vn.
      an C148 D_64fbc.
      aret C152 D_64fc0 ret.
      apply mst_refl.
    - unfold memisz_clob'. solve_regs_agree.
    - gres. reflexivity.
    - gres. rewrite ?at_0. reflexivity.
    - gres. reflexivity.
  Qed.

  Lemma ep_loop : forall (i : nat) regs (ret : word) q cnt,
    ret_ok ret -> getr regs 2 = at_ sp (-16) -> getr regs 11 = Z0 ->
    getr regs 12 = at_ beg q -> getr regs 14 = Z_to_bv 64 cnt ->
    (0 <= q)%Z -> (1 <= cnt)%Z -> (q + cnt <= N)%Z -> Z.of_nat i = (cnt - 1)%Z ->
    exists regs',
      msteps segs (mkst regs (at_ base 120) (mem1 ret) rom) (mkst regs' ret (mem1 ret) rom)
      /\ regs_agree CL regs regs' /\ getr regs' 10 = Z_to_bv 64 1 /\ getr regs' 2 = sp /\ getr regs' 1 = ret.
  Proof.
    get_code. pose proof (u64_range beg) as Hb.
    induction i as [|i IH]; intros regs ret q cnt Hret H2 H11 H12 H14 Hq Hc Hqc Hi.
    - eapply (runs_trans segs _ (fun r => mkst r (at_ base 140) (mem1 ret) rom)
               (fun r => getr r 2 = at_ sp (-16) /\ getr r 11 = Z0 /\ regs_agree CL regs r)).
      + eexists. split.
        * mlbu C120 D_64fa0.
          av C124 D_64fa4 (Z_to_bv 64 (cnt - 1)) ltac:(unfold v_addi; unorm; f_equal; lia).
          an C128 D_64fa8.
          an C132 D_64fac.
          ab_ft C136 D_64fb0 ltac:(condz).
          apply mst_refl.
        * post. unfold memisz_clob'. solve_regs_agree.
      + cbv beta. intros r1 (R2 & R11 & AG).
        destruct (fin_run r1 ret Hret R2 R11) as (r2 & RUN & AG2 & P). exists r2.
        split; [exact RUN | split; [eapply regs_agree_trans; eassumption | exact P]].
    - eapply (runs_trans segs _ (fun r => mkst r (at_ base 120) (mem1 ret) rom)
               (fun r => getr r 2 = at_ sp (-16) /\ getr r 11 = Z0 /\ getr r 12 = at_ beg (q + 1)
                         /\ getr r 14 = Z_to_bv 64 (cnt - 1) /\ regs_agree CL regs r)).
      + eexists. split.
        * mlbu C120 D_64fa0.
          av C124 D_64fa4 (Z_to_bv 64 (cnt - 1)) ltac:(unfold v_addi; unorm; f_equal; lia).
          an C128 D_64fa8.
          an C132 D_64fac.
          ab_tk C136 D_64fb0 ltac:(condz).
          apply mst_refl.
        * post. unfold memisz_clob'. solve_regs_agree.
      + cbv beta. intros r1 (R2 & R11 & R12 & R14 & AG).
        destruct (IH r1 ret (q + 1)%Z (cnt - 1)%Z Hret R2 R11 R12 R14 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
          as (r2 & RUN & AG2 & P). exists r2.
        split; [exact RUN | split; [eapply regs_agree_trans; eassumption | exact P]].
  Qed.

  Lemma tail_run : forall regs (ret : word),
    ret_ok ret -> getr regs 2 = at_ sp (-16) -> getr regs 10 = beg -> getr regs 11 = Z0 ->
    getr regs 12 = at_ beg dAE -> getr regs 14 = at_ beg N ->
    exists regs',
      msteps segs (mkst regs (at_ base 108) (mem1 ret) rom) (mkst regs' ret (mem1 ret) rom)
      /\ regs_agree CL regs regs' /\ getr regs' 10 = Z_to_bv 64 1 /\ getr regs' 2 = sp /\ getr regs' 1 = ret.
  Proof.
    get_code. intros regs ret Hret H2 H10 H11 H12 H14.
    pose proof (u64_range beg) as Hb. pose proof dAE_range as HdAE.
    destruct (Z.lt_ge_cases dAE 0) as [Hneg|Hnn].
    -
      eapply (runs_trans segs _ (fun r => mkst r (at_ base 140) (mem1 ret) rom)
               (fun r => getr r 2 = at_ sp (-16) /\ getr r 11 = Z0 /\ regs_agree CL regs r)).
      + eexists. split.
        * ab_tk C108 D_64f94 ltac:(rewrite <- (at_0 beg) at 2; condz).
          apply mst_refl.
        * post; apply regs_agree_refl.
      + cbv beta. intros r1 (R2 & R11 & AG).
        destruct (fin_run r1 ret Hret R2 R11) as (r2 & RUN & AG2 & P). exists r2.
        split; [exact RUN | split; [eapply regs_agree_trans; eassumption | exact P]].
    - destruct (Z.lt_ge_cases dAE N) as [Hlt|Hge].
      +
        eapply (runs_trans segs _ (fun r => mkst r (at_ base 120) (mem1 ret) rom)
                 (fun r => getr r 2 = at_ sp (-16) /\ getr r 11 = Z0 /\ getr r 12 = at_ beg dAE
                           /\ getr r 14 = Z_to_bv 64 (N - dAE) /\ regs_agree CL regs r)).
        * eexists. split.
          -- ab_ft C108 D_64f94 ltac:(rewrite <- (at_0 beg) at 2; condz).
             ab_ft C112 D_64f98 ltac:(condz).
             av C116 D_64f9c (Z_to_bv 64 (N - dAE)) ltac:(unfold v_sub, at_; unorm; f_equal; lia).
             apply mst_refl.
          -- post. unfold memisz_clob'. solve_regs_agree.
        * cbv beta. intros r1 (R2 & R11 & R12 & R14 & AG).
          destruct (ep_loop (Z.to_nat (N - dAE - 1)) r1 ret dAE (N - dAE) Hret R2 R11 R12 R14
                      ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (r2 & RUN & AG2 & P). exists r2.
          split; [exact RUN | split; [eapply regs_agree_trans; eassumption | exact P]].
      +
        eapply (runs_trans segs _ (fun r => mkst r (at_ base 140) (mem1 ret) rom)
                 (fun r => getr r 2 = at_ sp (-16) /\ getr r 11 = Z0 /\ regs_agree CL regs r)).
        * eexists. split.
          -- ab_ft C108 D_64f94 ltac:(rewrite <- (at_0 beg) at 2; condz).
             ab_tk C112 D_64f98 ltac:(condz).
             apply mst_refl.
          -- post; apply regs_agree_refl.
        * cbv beta. intros r1 (R2 & R11 & AG).
          destruct (fin_run r1 ret Hret R2 R11) as (r2 & RUN & AG2 & P). exists r2.
          split; [exact RUN | split; [eapply regs_agree_trans; eassumption | exact P]].
  Qed.

  Lemma w_loop : forall (i : nat) regs (ret : word) p,
    ret_ok ret -> getr regs 2 = at_ sp (-16) -> getr regs 10 = beg -> getr regs 11 = Z0 ->
    getr regs 12 = at_ beg dAE -> getr regs 14 = at_ beg N -> getr regs 15 = at_ beg p ->
    (0 <= p)%Z -> (p + 8 <= dAE)%Z -> (Z.of_nat i * 8 = dAE - p - 8)%Z ->
    exists regs',
      msteps segs (mkst regs (at_ base 92) (mem1 ret) rom) (mkst regs' ret (mem1 ret) rom)
      /\ regs_agree CL regs regs' /\ getr regs' 10 = Z_to_bv 64 1 /\ getr regs' 2 = sp /\ getr regs' 1 = ret.
  Proof.
    get_code. pose proof (u64_range beg) as Hb. pose proof dAE_range as HdAE.
    induction i as [|i IH]; intros regs ret p Hret H2 H10 H11 H12 H14 H15 Hp Hp8 Hi.
    - eapply (runs_trans segs _ (fun r => mkst r (at_ base 108) (mem1 ret) rom)
               (fun r => getr r 2 = at_ sp (-16) /\ getr r 10 = beg /\ getr r 11 = Z0 /\ getr r 12 = at_ beg dAE
                         /\ getr r 14 = at_ beg N /\ regs_agree CL regs r)).
      + eexists. split.
        * mld C92 D_64f84.
          an C96 D_64f88.
          an C100 D_64f8c.
          ab_ft C104 D_64f90 ltac:(condz).
          apply mst_refl.
        * post. unfold memisz_clob'. solve_regs_agree.
      + cbv beta. intros r1 (R2 & R10 & R11 & R12 & R14 & AG).
        destruct (tail_run r1 ret Hret R2 R10 R11 R12 R14) as (r2 & RUN & AG2 & P). exists r2.
        split; [exact RUN | split; [eapply regs_agree_trans; eassumption | exact P]].
    - eapply (runs_trans segs _ (fun r => mkst r (at_ base 92) (mem1 ret) rom)
               (fun r => getr r 2 = at_ sp (-16) /\ getr r 10 = beg /\ getr r 11 = Z0 /\ getr r 12 = at_ beg dAE
                         /\ getr r 14 = at_ beg N /\ getr r 15 = at_ beg (p + 8) /\ regs_agree CL regs r)).
      + eexists. split.
        * mld C92 D_64f84.
          an C96 D_64f88.
          an C100 D_64f8c.
          ab_tk C104 D_64f90 ltac:(condz).
          apply mst_refl.
        * post. unfold memisz_clob'. solve_regs_agree.
      + cbv beta. intros r1 (R2 & R10 & R11 & R12 & R14 & R15 & AG).
        destruct (IH r1 ret (p + 8)%Z Hret R2 R10 R11 R12 R14 R15 ltac:(lia) ltac:(lia) ltac:(lia))
          as (r2 & RUN & AG2 & P). exists r2.
        split; [exact RUN | split; [eapply regs_agree_trans; eassumption | exact P]].
  Qed.

  Lemma mid_run : forall regs (ret : word),
    ret_ok ret -> getr regs 2 = at_ sp (-16) -> getr regs 10 = beg -> getr regs 11 = Z0 ->
    getr regs 12 = at_ beg dAE -> getr regs 14 = at_ beg N -> getr regs 15 = at_ beg dAB ->
    exists regs',
      msteps segs (mkst regs (at_ base 88) (mem1 ret) rom) (mkst regs' ret (mem1 ret) rom)
      /\ regs_agree CL regs regs' /\ getr regs' 10 = Z_to_bv 64 1 /\ getr regs' 2 = sp /\ getr regs' 1 = ret.
  Proof.
    get_code. intros regs ret Hret H2 H10 H11 H12 H14 H15.
    pose proof (u64_range beg) as Hb. pose proof dAE_range as HdAE. pose proof dAB_range as HdAB.
    destruct (Z.lt_ge_cases dAB dAE) as [Hlt|Hge].
    -
      assert (Hi : exists i : nat, (Z.of_nat i * 8 = dAE - dAB - 8)%Z).
      { unfold dAB, dAE in *.
        pose proof (Z.div_mod (B + 7) 8 ltac:(lia)). pose proof (Z.div_mod (B + N) 8 ltac:(lia)).
        pose proof (Z.mod_pos_bound (B + 7) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (B + N) 8 ltac:(lia)).
        exists (Z.to_nat ((B + N) / 8 - (B + 7) / 8 - 1)). nia. }
      destruct Hi as (i & Hi).
      eapply (runs_trans segs _ (fun r => mkst r (at_ base 92) (mem1 ret) rom)
               (fun r => getr r 2 = at_ sp (-16) /\ getr r 10 = beg /\ getr r 11 = Z0 /\ getr r 12 = at_ beg dAE
                         /\ getr r 14 = at_ beg N /\ getr r 15 = at_ beg dAB /\ regs_agree CL regs r)).
      + eexists. split.
        * ab_ft C88 D_64f80 ltac:(condz).
          apply mst_refl.
        * post; apply regs_agree_refl.
      + cbv beta. intros r1 (R2 & R10 & R11 & R12 & R14 & R15 & AG).
        destruct (w_loop i r1 ret dAB Hret R2 R10 R11 R12 R14 R15 ltac:(lia) ltac:(lia) Hi)
          as (r2 & RUN & AG2 & P). exists r2.
        split; [exact RUN | split; [eapply regs_agree_trans; eassumption | exact P]].
    - eapply (runs_trans segs _ (fun r => mkst r (at_ base 108) (mem1 ret) rom)
               (fun r => getr r 2 = at_ sp (-16) /\ getr r 10 = beg /\ getr r 11 = Z0 /\ getr r 12 = at_ beg dAE
                         /\ getr r 14 = at_ beg N /\ regs_agree CL regs r)).
      + eexists. split.
        * ab_tk C88 D_64f80 ltac:(condz).
          apply mst_refl.
        * post; apply regs_agree_refl.
      + cbv beta. intros r1 (R2 & R10 & R11 & R12 & R14 & AG).
        destruct (tail_run r1 ret Hret R2 R10 R11 R12 R14) as (r2 & RUN & AG2 & P). exists r2.
        split; [exact RUN | split; [eapply regs_agree_trans; eassumption | exact P]].
  Qed.

  Lemma pro_loop : forall (i : nat) regs (ret : word) j,
    ret_ok ret -> getr regs 2 = at_ sp (-16) -> getr regs 10 = beg -> getr regs 11 = Z0 ->
    getr regs 12 = at_ beg dAE -> getr regs 13 = at_ beg (j + 1) -> getr regs 14 = at_ beg N ->
    getr regs 15 = at_ beg dAB ->
    (0 <= j)%Z -> (j < dAB)%Z -> (j < N)%Z -> Z.of_nat i = (Z.min dAB N - 1 - j)%Z ->
    exists regs',
      msteps segs (mkst regs (at_ base 64) (mem1 ret) rom) (mkst regs' ret (mem1 ret) rom)
      /\ regs_agree CL regs regs' /\ getr regs' 10 = Z_to_bv 64 1 /\ getr regs' 2 = sp /\ getr regs' 1 = ret.
  Proof.
    get_code. pose proof (u64_range beg) as Hb. pose proof dAE_range as HdAE. pose proof dAB_range as HdAB.
    induction i as [|i IH]; intros regs ret j Hret H2 H10 H11 H12 H13 H14 H15 Hj HjA HjN Hi.
    -
      destruct (Z.eq_dec (j + 1) dAB) as [HA|HA].
      + eapply (runs_trans segs _ (fun r => mkst r (at_ base 88) (mem1 ret) rom)
                 (fun r => getr r 2 = at_ sp (-16) /\ getr r 10 = beg /\ getr r 11 = Z0 /\ getr r 12 = at_ beg dAE
                           /\ getr r 14 = at_ beg N /\ getr r 15 = at_ beg dAB /\ regs_agree CL regs r)).
        * eexists. split.
          -- an C64 D_64f68.
             mlbu C68 D_64f6c.
             an C72 D_64f70.
             ab_tk C76 D_64f74 ltac:(condz).
             apply mst_refl.
          -- post. unfold memisz_clob'. solve_regs_agree.
        * cbv beta. intros r1 (R2 & R10 & R11 & R12 & R14 & R15 & AG).
          destruct (mid_run r1 ret Hret R2 R10 R11 R12 R14 R15) as (r2 & RUN & AG2 & P). exists r2.
          split; [exact RUN | split; [eapply regs_agree_trans; eassumption | exact P]].
      + eapply (runs_trans segs _ (fun r => mkst r (at_ base 88) (mem1 ret) rom)
                 (fun r => getr r 2 = at_ sp (-16) /\ getr r 10 = beg /\ getr r 11 = Z0 /\ getr r 12 = at_ beg dAE
                           /\ getr r 14 = at_ beg N /\ getr r 15 = at_ beg dAB /\ regs_agree CL regs r)).
        * eexists. split.
          -- an C64 D_64f68.
             mlbu C68 D_64f6c.
             an C72 D_64f70.
             ab_ft C76 D_64f74 ltac:(condz).
             an C80 D_64f78.
             ab_ft C84 D_64f7c ltac:(condz).
             apply mst_refl.
          -- post. unfold memisz_clob'. solve_regs_agree.
        * cbv beta. intros r1 (R2 & R10 & R11 & R12 & R14 & R15 & AG).
          destruct (mid_run r1 ret Hret R2 R10 R11 R12 R14 R15) as (r2 & RUN & AG2 & P). exists r2.
          split; [exact RUN | split; [eapply regs_agree_trans; eassumption | exact P]].
    - eapply (runs_trans segs _ (fun r => mkst r (at_ base 64) (mem1 ret) rom)
               (fun r => getr r 2 = at_ sp (-16) /\ getr r 10 = beg /\ getr r 11 = Z0 /\ getr r 12 = at_ beg dAE
                         /\ getr r 13 = at_ beg (j + 1 + 1) /\ getr r 14 = at_ beg N /\ getr r 15 = at_ beg dAB
                         /\ regs_agree CL regs r)).
      + eexists. split.
        * an C64 D_64f68.
          mlbu C68 D_64f6c.
          an C72 D_64f70.
          ab_ft C76 D_64f74 ltac:(condz).
          an C80 D_64f78.
          ab_tk C84 D_64f7c ltac:(condz).
          apply mst_refl.
        * post. unfold memisz_clob'. solve_regs_agree.
      + cbv beta. intros r1 (R2 & R10 & R11 & R12 & R13 & R14 & R15 & AG).
        destruct (IH r1 ret (j + 1)%Z Hret R2 R10 R11 R12 R13 R14 R15 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
          as (r2 & RUN & AG2 & P). exists r2.
        split; [exact RUN | split; [eapply regs_agree_trans; eassumption | exact P]].
  Qed.

  Theorem mem_is_zero_run : forall regs (ret : word),
    ret_ok ret -> getr regs 1 = ret -> getr regs 2 = sp ->
    getr regs 10 = beg -> getr regs 11 = Z_to_bv 64 N ->
    exists regs',
      msteps segs (mkst regs (at_ base 0) mem rom) (mkst regs' ret (mem1 ret) rom)
      /\ regs_agree (fun r => In r memisz_clob) regs regs'
      /\ getr regs' 10 = Z_to_bv 64 1 /\ getr regs' 2 = sp /\ getr regs' 1 = ret.
  Proof.
    get_code. intros regs ret Hret H1 H2 H10 H11.
    pose proof (u64_range beg) as Hb. pose proof (u64_range sp) as Hs.
    pose proof dAE_range as HdAE. pose proof dAB_range as HdAB.

    eapply (runs_trans segs _ (fun r => mkst r (at_ base 48) (mem1 ret) rom)
             (fun r => getr r 2 = at_ sp (-16) /\ getr r 10 = beg /\ getr r 11 = Z0 /\ getr r 12 = at_ beg dAE
                       /\ getr r 13 = Z_to_bv 64 N /\ getr r 14 = at_ beg N /\ getr r 15 = at_ beg dAB
                       /\ regs_agree CL regs r)).
    { eexists. split.
      - an C0 D_64f28.
        chain_step; [reflexivity
          | eapply step_sd_at with (a := at_ sp (-8)) (v := ret);
            [exact C4 | reflexivity | exact D_64f2c
            | gres; rwH; imm_norm; rewrite ?at_addi; zlit_at; reflexivity
            | gres; rwH; reflexivity
            | exact Hstk]
          | step_simpl]; change (wbytes mem (at_ sp (-8)) (word_to_le_bytes 8 ret)) with (mem1 ret); vn.

        an C8 D_64f30.
        an C12 D_64f34.
        an C16 D_64f38.
        an C20 D_64f3c.
        ab_ft C24 D_64f40 ltac:(condz).
        an C28 D_64f44.
        av C32 D_64f48 (at_ beg N) ltac:(apply v_add_at; lia).
        an C36 D_64f4c.
        av C40 D_64f50 (at_ beg dAB) ltac:(rewrite v_andi_m8 by lia; unfold dAB; f_equal; lia).
        av C44 D_64f54 (at_ beg dAE) ltac:(rewrite v_andi_m8 by lia; unfold dAE; reflexivity).
        apply mst_refl.
      - post. unfold memisz_clob'. solve_regs_agree. }
    cbv beta. intros r0 (R2 & R10 & R11 & R12 & R13 & R14 & R15 & AG0).

    enough (G : exists regs',
      msteps segs (mkst r0 (at_ base 48) (mem1 ret) rom) (mkst regs' ret (mem1 ret) rom)
      /\ regs_agree CL regs regs' /\ getr regs' 10 = Z_to_bv 64 1 /\ getr regs' 2 = sp /\ getr regs' 1 = ret).
    { destruct G as (r' & RUN & AG & P10 & P2 & P1). exists r'. split; [exact RUN|]. split; [|repeat split; assumption].
      apply (regs_agree_strengthen memisz_clob memisz_clob'); [exact AG|].
      intros r Hr Hnr. unfold memisz_clob', memisz_clob in *. cbn [In] in Hr.
      destruct Hr as [<-|[<-|Hr]]; [rewrite P1, H1; reflexivity | rewrite P2, H2; reflexivity |].
      exfalso. apply Hnr. cbn [In]. tauto. }
    destruct (Z.eq_dec dAB 0) as [HA0|HA0].
    -
      eapply (runs_trans segs _ (fun r => mkst r (at_ base 88) (mem1 ret) rom)
               (fun r => getr r 2 = at_ sp (-16) /\ getr r 10 = beg /\ getr r 11 = Z0 /\ getr r 12 = at_ beg dAE
                         /\ getr r 14 = at_ beg N /\ getr r 15 = at_ beg dAB /\ regs_agree CL regs r)).
      + eexists. split.
        * ab_tk C48 D_64f58 ltac:(rewrite <- (at_0 beg) at 1; condz).
          apply mst_refl.
        * post; exact AG0.
      + cbv beta. intros r1 (S2 & S10 & S11 & S12 & S14 & S15 & AG).
        destruct (mid_run r1 ret Hret S2 S10 S11 S12 S14 S15) as (r2 & RUN & AG2 & P). exists r2.
        split; [exact RUN | split; [eapply regs_agree_trans; eassumption | exact P]].
    - destruct (Z.eq_dec N 0) as [HN0|HN0].
      +
        eapply (runs_trans segs _ (fun r => mkst r (at_ base 88) (mem1 ret) rom)
                 (fun r => getr r 2 = at_ sp (-16) /\ getr r 10 = beg /\ getr r 11 = Z0 /\ getr r 12 = at_ beg dAE
                           /\ getr r 14 = at_ beg N /\ getr r 15 = at_ beg dAB /\ regs_agree CL regs r)).
        * eexists. split.
          -- ab_ft C48 D_64f58 ltac:(rewrite <- (at_0 beg) at 1; condz).
             ab_tk C52 D_64f5c ltac:(condz).
             apply mst_refl.
          -- post; exact AG0.
        * cbv beta. intros r1 (S2 & S10 & S11 & S12 & S14 & S15 & AG).
          destruct (mid_run r1 ret Hret S2 S10 S11 S12 S14 S15) as (r2 & RUN & AG2 & P). exists r2.
          split; [exact RUN | split; [eapply regs_agree_trans; eassumption | exact P]].
      +
        eapply (runs_trans segs _ (fun r => mkst r (at_ base 64) (mem1 ret) rom)
                 (fun r => getr r 2 = at_ sp (-16) /\ getr r 10 = beg /\ getr r 11 = Z0 /\ getr r 12 = at_ beg dAE
                           /\ getr r 13 = at_ beg (0 + 1) /\ getr r 14 = at_ beg N /\ getr r 15 = at_ beg dAB
                           /\ regs_agree CL regs r)).
        * eexists. split.
          -- ab_ft C48 D_64f58 ltac:(rewrite <- (at_0 beg) at 1; condz).
             ab_ft C52 D_64f5c ltac:(condz).
             an C56 D_64f60.
             an C60 D_64f64.
             apply mst_refl.
          -- post. unfold memisz_clob'. ra_chain.
        * cbv beta. intros r1 (S2 & S10 & S11 & S12 & S13 & S14 & S15 & AG).
          destruct (pro_loop (Z.to_nat (Z.min dAB N - 1)) r1 ret 0 Hret S2 S10 S11 S12 S13 S14 S15
                      ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (r2 & RUN & AG2 & P). exists r2.
          split; [exact RUN | split; [eapply regs_agree_trans; eassumption | exact P]].
  Qed.
End MEMISZERO.

Lemma slot_at : forall sp : word, (16 <= bv_unsigned sp)%Z ->
  at_ sp (-8) = Z_to_bv 64 (bv_unsigned sp - 8).
Proof. intros sp Hsp. unfold at_. f_equal; lia. Qed.

Theorem mem_is_zero_summary : forall segs (base : word) mem (beg sp : word) N rom regs (ret : word),
  code_at segs base 0 memisz_words ->
  (0 <= N <= 2 ^ 40)%Z ->
  (bv_unsigned beg + N + 8 <= 2 ^ 64)%Z ->
  (16 <= bv_unsigned sp)%Z ->
  store_ok segs mem (Z_to_bv 64 (bv_unsigned sp - 8)) 8 = true ->
  (bv_unsigned beg + N <= bv_unsigned sp - 8 \/ bv_unsigned sp <= bv_unsigned beg)%Z ->
  (forall a : word, (bv_unsigned beg <= bv_unsigned a < bv_unsigned beg + N)%Z ->
     rdn segs mem a 1 = Some [Z_to_bv 8 0]) ->
  ret_ok ret -> getr regs 1 = ret -> getr regs 2 = sp ->
  getr regs 10 = beg -> getr regs 11 = Z_to_bv 64 N ->
  exists regs',
    msteps segs (mkst regs base mem rom)
                (mkst regs' ret (wbytes mem (Z_to_bv 64 (bv_unsigned sp - 8)) (word_to_le_bytes 8 ret)) rom)
    /\ regs_agree (fun r => In r memisz_clob) regs regs'
    /\ getr regs' 10 = Z_to_bv 64 1 /\ getr regs' 2 = sp /\ getr regs' 1 = ret.
Proof.
  intros segs base mem beg sp N rom regs ret HC HN Hnw Hsp Hstk Hdisj Hz.
  rewrite <- (slot_at sp Hsp) in Hstk |- *. rewrite <- (at_0 base).
  apply (mem_is_zero_run segs base mem beg sp N rom HC HN Hnw Hsp Hstk Hdisj Hz).
Qed.

From OssFuzzTheorems.simdjson.fuzz_dump.images Require Import AsanUbsan.

Definition asan_mem_is_zero_entry : word := 0x92050.

Lemma asan_mem_is_zero_code :
  code_at AsanUbsan.M.loaded_segments asan_mem_is_zero_entry 0 memisz_words.
Proof. unfold memisz_words. code_at_vm. Qed.

Theorem asan_mem_is_zero : forall mem (beg sp : word) N rom regs (ret : word),
  (0 <= N <= 2 ^ 40)%Z ->
  (bv_unsigned beg + N + 8 <= 2 ^ 64)%Z ->
  (16 <= bv_unsigned sp)%Z ->
  store_ok AsanUbsan.M.loaded_segments mem (Z_to_bv 64 (bv_unsigned sp - 8)) 8 = true ->
  (bv_unsigned beg + N <= bv_unsigned sp - 8 \/ bv_unsigned sp <= bv_unsigned beg)%Z ->
  (forall a : word, (bv_unsigned beg <= bv_unsigned a < bv_unsigned beg + N)%Z ->
     rdn AsanUbsan.M.loaded_segments mem a 1 = Some [Z_to_bv 8 0]) ->
  ret_ok ret -> getr regs 1 = ret -> getr regs 2 = sp ->
  getr regs 10 = beg -> getr regs 11 = Z_to_bv 64 N ->
  exists regs',
    msteps AsanUbsan.M.loaded_segments
           (mkst regs asan_mem_is_zero_entry mem rom)
           (mkst regs' ret (wbytes mem (Z_to_bv 64 (bv_unsigned sp - 8)) (word_to_le_bytes 8 ret)) rom)
    /\ regs_agree (fun r => In r memisz_clob) regs regs'
    /\ getr regs' 10 = Z_to_bv 64 1 /\ getr regs' 2 = sp /\ getr regs' 1 = ret.
Proof.
  intros mem beg sp N rom regs ret.
  apply (mem_is_zero_summary _ _ mem beg sp N rom regs ret asan_mem_is_zero_code).
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
