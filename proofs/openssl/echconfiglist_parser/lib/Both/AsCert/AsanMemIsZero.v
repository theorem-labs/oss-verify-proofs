(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import SumsLib Sums_code.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Definition memisz_words : list (bv 32) :=
  [W_aa054; W_aa058; W_aa05c; W_aa060; W_aa064; W_aa068; W_aa06c; W_aa070;
   W_aa074; W_aa078; W_aa07c; W_aa080; W_aa084; W_aa088; W_aa08c; W_aa090;
   W_aa094; W_aa098; W_aa09c; W_aa0a0; W_aa0a4; W_aa0a8; W_aa0ac; W_aa0b0;
   W_aa0b4; W_aa0b8; W_aa0bc; W_aa0c0; W_aa0c4; W_aa0c8; W_aa0cc; W_aa0d0;
   W_aa0d4; W_aa0d8; W_aa0dc; W_aa0e0; W_aa0e4; W_aa0e8; W_aa0ec].

(* [comment removed for export] *)
Definition memisz_clob : list reg := [10; 11; 12; 13; 14; 15; 16].
(* [comment removed for export] *)
Definition memisz_clob' : list reg := [1; 2; 10; 11; 12; 13; 14; 15; 16].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

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

(* [comment removed for export] *)
Lemma v_andi_m8 : forall (a : word) d,
  (0 <= bv_unsigned a + d < 2 ^ 64)%Z ->
  v_andi (at_ a d) (-8) = at_ a (d - (bv_unsigned a + d) mod 8).
Proof.
  intros a d Hd. unfold v_andi, at_. f_equal.
  change (bv_wrap 64 (-8)) with (2 ^ 64 - 2 ^ 3)%Z.
  rewrite u_Z2bv by lia. rewrite land_m8 by lia. lia.
Qed.

(* [comment removed for export] *)
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

(* [comment removed for export] *)
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
  Variable N : Z.            (* [comment removed for export] *)
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
  (* [comment removed for export] *)
  Definition dAB : Z := 7 - (B + 7) mod 8.
  Definition dAE : Z := N - (B + N) mod 8.
  (* [comment removed for export] *)
  Definition mem1 (ra : word) : word -> option byte := wbytes mem (at_ sp (-8)) (word_to_le_bytes 8 ra).

  Lemma dAB_range : (0 <= dAB <= 7)%Z.
  Proof. unfold dAB. pose proof (Z.mod_pos_bound (B + 7) 8 ltac:(lia)). lia. Qed.

  Lemma dAE_range : (N - 7 <= dAE <= N)%Z /\ (0 <= B + dAE)%Z.
  Proof.
    unfold dAE. pose proof (u64_range beg). pose proof (Z.mod_pos_bound (B + N) 8 ltac:(lia)).
    pose proof (Z.div_mod (B + N) 8 ltac:(lia)). nia.
  Qed.

  (* [comment removed for export] *)
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
    (* [comment removed for export] *)
    code_nth HC HCODE memisz_words 0%nat C0; code_nth HC HCODE memisz_words 1%nat C4; code_nth HC HCODE memisz_words 2%nat C8;
    code_nth HC HCODE memisz_words 3%nat C12; code_nth HC HCODE memisz_words 4%nat C16; code_nth HC HCODE memisz_words 5%nat C20;
    code_nth HC HCODE memisz_words 6%nat C24; code_nth HC HCODE memisz_words 7%nat C28; code_nth HC HCODE memisz_words 8%nat C32;
    code_nth HC HCODE memisz_words 9%nat C36; code_nth HC HCODE memisz_words 10%nat C40; code_nth HC HCODE memisz_words 11%nat C44;
    code_nth HC HCODE memisz_words 12%nat C48; code_nth HC HCODE memisz_words 13%nat C52; code_nth HC HCODE memisz_words 14%nat C56;
    code_nth HC HCODE memisz_words 15%nat C60; code_nth HC HCODE memisz_words 16%nat C64; code_nth HC HCODE memisz_words 17%nat C68;
    code_nth HC HCODE memisz_words 18%nat C72; code_nth HC HCODE memisz_words 19%nat C76; code_nth HC HCODE memisz_words 20%nat C80;
    code_nth HC HCODE memisz_words 21%nat C84; code_nth HC HCODE memisz_words 22%nat C88; code_nth HC HCODE memisz_words 23%nat C92;
    code_nth HC HCODE memisz_words 24%nat C96; code_nth HC HCODE memisz_words 25%nat C100; code_nth HC HCODE memisz_words 26%nat C104;
    code_nth HC HCODE memisz_words 27%nat C108; code_nth HC HCODE memisz_words 28%nat C112; code_nth HC HCODE memisz_words 29%nat C116;
    code_nth HC HCODE memisz_words 30%nat C120; code_nth HC HCODE memisz_words 31%nat C124; code_nth HC HCODE memisz_words 32%nat C128;
    code_nth HC HCODE memisz_words 33%nat C132; code_nth HC HCODE memisz_words 34%nat C136; code_nth HC HCODE memisz_words 35%nat C140;
    code_nth HC HCODE memisz_words 36%nat C144; code_nth HC HCODE memisz_words 37%nat C148; code_nth HC HCODE memisz_words 38%nat C152;
    clear HC.

  (* [comment removed for export] *)
  Ltac mlbu F D :=
    chain_step; [reflexivity
      | eapply step_lbu with (b := Z_to_bv 8 0);
        [exact F | reflexivity | exact D
        | gres; rwH; imm_norm; rewrite ?at_addi; apply rd1; lia]
      | step_simpl]; vn.
  (* [comment removed for export] *)
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

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma fin_run : forall regs (ret : word),
    ret_ok ret -> getr regs 2 = at_ sp (-16) -> getr regs 11 = Z0 ->
    exists regs',
      msteps segs (mkst regs (at_ base 140) (mem1 ret) rom) (mkst regs' ret (mem1 ret) rom)
      /\ regs_agree CL regs regs' /\ getr regs' 10 = Z_to_bv 64 1 /\ getr regs' 2 = sp /\ getr regs' 1 = ret.
  Proof.
    get_code. intros regs ret Hret H2 H11. pose proof (u64_range sp).
    eexists. split; [|split; [|split; [|split]]].
    - an C140 D_aa0e0.                            (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_ld with (v := ret);
          [exact C144 | reflexivity | exact D_aa0e4
          | gres; rwH; imm_norm; rewrite ?at_addi; zlit_at; apply rd_ra
          | apply bytes_le_to_Z_8]
        | step_simpl]; vn.                         (* [comment removed for export] *)
      an C148 D_aa0e8.                            (* [comment removed for export] *)
      aret C152 D_aa0ec ret.
      apply mst_refl.
    - unfold memisz_clob'. solve_regs_agree.
    - gres. reflexivity.
    - gres. rewrite ?at_0. reflexivity.
    - gres. reflexivity.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
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
        * mlbu C120 D_aa0cc.                      (* [comment removed for export] *)
          av C124 D_aa0d0 (Z_to_bv 64 (cnt - 1)) ltac:(unfold v_addi; unorm; f_equal; lia).  (* [comment removed for export] *)
          an C128 D_aa0d4.                        (* [comment removed for export] *)
          an C132 D_aa0d8.                        (* [comment removed for export] *)
          ab_ft C136 D_aa0dc ltac:(condz).        (* [comment removed for export] *)
          apply mst_refl.
        * post. unfold memisz_clob'. solve_regs_agree.
      + cbv beta. intros r1 (R2 & R11 & AG).
        destruct (fin_run r1 ret Hret R2 R11) as (r2 & RUN & AG2 & P). exists r2.
        split; [exact RUN | split; [eapply regs_agree_trans; eassumption | exact P]].
    - eapply (runs_trans segs _ (fun r => mkst r (at_ base 120) (mem1 ret) rom)
               (fun r => getr r 2 = at_ sp (-16) /\ getr r 11 = Z0 /\ getr r 12 = at_ beg (q + 1)
                         /\ getr r 14 = Z_to_bv 64 (cnt - 1) /\ regs_agree CL regs r)).
      + eexists. split.
        * mlbu C120 D_aa0cc.
          av C124 D_aa0d0 (Z_to_bv 64 (cnt - 1)) ltac:(unfold v_addi; unorm; f_equal; lia).
          an C128 D_aa0d4.
          an C132 D_aa0d8.
          ab_tk C136 D_aa0dc ltac:(condz).        (* [comment removed for export] *)
          apply mst_refl.
        * post. unfold memisz_clob'. solve_regs_agree.
      + cbv beta. intros r1 (R2 & R11 & R12 & R14 & AG).
        destruct (IH r1 ret (q + 1)%Z (cnt - 1)%Z Hret R2 R11 R12 R14 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
          as (r2 & RUN & AG2 & P). exists r2.
        split; [exact RUN | split; [eapply regs_agree_trans; eassumption | exact P]].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
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
    - (* [comment removed for export] *)
      eapply (runs_trans segs _ (fun r => mkst r (at_ base 140) (mem1 ret) rom)
               (fun r => getr r 2 = at_ sp (-16) /\ getr r 11 = Z0 /\ regs_agree CL regs r)).
      + eexists. split.
        * ab_tk C108 D_aa0c0 ltac:(rewrite <- (at_0 beg) at 2; condz).   (* [comment removed for export] *)
          apply mst_refl.
        * post; apply regs_agree_refl.
      + cbv beta. intros r1 (R2 & R11 & AG).
        destruct (fin_run r1 ret Hret R2 R11) as (r2 & RUN & AG2 & P). exists r2.
        split; [exact RUN | split; [eapply regs_agree_trans; eassumption | exact P]].
    - destruct (Z.lt_ge_cases dAE N) as [Hlt|Hge].
      + (* [comment removed for export] *)
        eapply (runs_trans segs _ (fun r => mkst r (at_ base 120) (mem1 ret) rom)
                 (fun r => getr r 2 = at_ sp (-16) /\ getr r 11 = Z0 /\ getr r 12 = at_ beg dAE
                           /\ getr r 14 = Z_to_bv 64 (N - dAE) /\ regs_agree CL regs r)).
        * eexists. split.
          -- ab_ft C108 D_aa0c0 ltac:(rewrite <- (at_0 beg) at 2; condz).  (* [comment removed for export] *)
             ab_ft C112 D_aa0c4 ltac:(condz).                              (* [comment removed for export] *)
             av C116 D_aa0c8 (Z_to_bv 64 (N - dAE)) ltac:(unfold v_sub, at_; unorm; f_equal; lia).  (* [comment removed for export] *)
             apply mst_refl.
          -- post. unfold memisz_clob'. solve_regs_agree.
        * cbv beta. intros r1 (R2 & R11 & R12 & R14 & AG).
          destruct (ep_loop (Z.to_nat (N - dAE - 1)) r1 ret dAE (N - dAE) Hret R2 R11 R12 R14
                      ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (r2 & RUN & AG2 & P). exists r2.
          split; [exact RUN | split; [eapply regs_agree_trans; eassumption | exact P]].
      + (* [comment removed for export] *)
        eapply (runs_trans segs _ (fun r => mkst r (at_ base 140) (mem1 ret) rom)
                 (fun r => getr r 2 = at_ sp (-16) /\ getr r 11 = Z0 /\ regs_agree CL regs r)).
        * eexists. split.
          -- ab_ft C108 D_aa0c0 ltac:(rewrite <- (at_0 beg) at 2; condz).  (* [comment removed for export] *)
             ab_tk C112 D_aa0c4 ltac:(condz).                              (* [comment removed for export] *)
             apply mst_refl.
          -- post; apply regs_agree_refl.
        * cbv beta. intros r1 (R2 & R11 & AG).
          destruct (fin_run r1 ret Hret R2 R11) as (r2 & RUN & AG2 & P). exists r2.
          split; [exact RUN | split; [eapply regs_agree_trans; eassumption | exact P]].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
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
        * mld C92 D_aa0b0.                        (* [comment removed for export] *)
          an C96 D_aa0b4.                         (* [comment removed for export] *)
          an C100 D_aa0b8.                        (* [comment removed for export] *)
          ab_ft C104 D_aa0bc ltac:(condz).        (* [comment removed for export] *)
          apply mst_refl.
        * post. unfold memisz_clob'. solve_regs_agree.
      + cbv beta. intros r1 (R2 & R10 & R11 & R12 & R14 & AG).
        destruct (tail_run r1 ret Hret R2 R10 R11 R12 R14) as (r2 & RUN & AG2 & P). exists r2.
        split; [exact RUN | split; [eapply regs_agree_trans; eassumption | exact P]].
    - eapply (runs_trans segs _ (fun r => mkst r (at_ base 92) (mem1 ret) rom)
               (fun r => getr r 2 = at_ sp (-16) /\ getr r 10 = beg /\ getr r 11 = Z0 /\ getr r 12 = at_ beg dAE
                         /\ getr r 14 = at_ beg N /\ getr r 15 = at_ beg (p + 8) /\ regs_agree CL regs r)).
      + eexists. split.
        * mld C92 D_aa0b0.
          an C96 D_aa0b4.
          an C100 D_aa0b8.
          ab_tk C104 D_aa0bc ltac:(condz).        (* [comment removed for export] *)
          apply mst_refl.
        * post. unfold memisz_clob'. solve_regs_agree.
      + cbv beta. intros r1 (R2 & R10 & R11 & R12 & R14 & R15 & AG).
        destruct (IH r1 ret (p + 8)%Z Hret R2 R10 R11 R12 R14 R15 ltac:(lia) ltac:(lia) ltac:(lia))
          as (r2 & RUN & AG2 & P). exists r2.
        split; [exact RUN | split; [eapply regs_agree_trans; eassumption | exact P]].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
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
    - (* [comment removed for export] *)
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
        * ab_ft C88 D_aa0ac ltac:(condz).         (* [comment removed for export] *)
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
        * ab_tk C88 D_aa0ac ltac:(condz).         (* [comment removed for export] *)
          apply mst_refl.
        * post; apply regs_agree_refl.
      + cbv beta. intros r1 (R2 & R10 & R11 & R12 & R14 & AG).
        destruct (tail_run r1 ret Hret R2 R10 R11 R12 R14) as (r2 & RUN & AG2 & P). exists r2.
        split; [exact RUN | split; [eapply regs_agree_trans; eassumption | exact P]].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
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
    - (* [comment removed for export] *)
      destruct (Z.eq_dec (j + 1) dAB) as [HA|HA].
      + eapply (runs_trans segs _ (fun r => mkst r (at_ base 88) (mem1 ret) rom)
                 (fun r => getr r 2 = at_ sp (-16) /\ getr r 10 = beg /\ getr r 11 = Z0 /\ getr r 12 = at_ beg dAE
                           /\ getr r 14 = at_ beg N /\ getr r 15 = at_ beg dAB /\ regs_agree CL regs r)).
        * eexists. split.
          -- an C64 D_aa094.                      (* [comment removed for export] *)
             mlbu C68 D_aa098.                    (* [comment removed for export] *)
             an C72 D_aa09c.                      (* [comment removed for export] *)
             ab_tk C76 D_aa0a0 ltac:(condz).      (* [comment removed for export] *)
             apply mst_refl.
          -- post. unfold memisz_clob'. solve_regs_agree.
        * cbv beta. intros r1 (R2 & R10 & R11 & R12 & R14 & R15 & AG).
          destruct (mid_run r1 ret Hret R2 R10 R11 R12 R14 R15) as (r2 & RUN & AG2 & P). exists r2.
          split; [exact RUN | split; [eapply regs_agree_trans; eassumption | exact P]].
      + eapply (runs_trans segs _ (fun r => mkst r (at_ base 88) (mem1 ret) rom)
                 (fun r => getr r 2 = at_ sp (-16) /\ getr r 10 = beg /\ getr r 11 = Z0 /\ getr r 12 = at_ beg dAE
                           /\ getr r 14 = at_ beg N /\ getr r 15 = at_ beg dAB /\ regs_agree CL regs r)).
        * eexists. split.
          -- an C64 D_aa094.                      (* [comment removed for export] *)
             mlbu C68 D_aa098.                    (* [comment removed for export] *)
             an C72 D_aa09c.                      (* [comment removed for export] *)
             ab_ft C76 D_aa0a0 ltac:(condz).      (* [comment removed for export] *)
             an C80 D_aa0a4.                      (* [comment removed for export] *)
             ab_ft C84 D_aa0a8 ltac:(condz).      (* [comment removed for export] *)
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
        * an C64 D_aa094.
          mlbu C68 D_aa098.
          an C72 D_aa09c.
          ab_ft C76 D_aa0a0 ltac:(condz).         (* [comment removed for export] *)
          an C80 D_aa0a4.
          ab_tk C84 D_aa0a8 ltac:(condz).         (* [comment removed for export] *)
          apply mst_refl.
        * post. unfold memisz_clob'. solve_regs_agree.
      + cbv beta. intros r1 (R2 & R10 & R11 & R12 & R13 & R14 & R15 & AG).
        destruct (IH r1 ret (j + 1)%Z Hret R2 R10 R11 R12 R13 R14 R15 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
          as (r2 & RUN & AG2 & P). exists r2.
        split; [exact RUN | split; [eapply regs_agree_trans; eassumption | exact P]].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
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
    (* [comment removed for export] *)
    eapply (runs_trans segs _ (fun r => mkst r (at_ base 48) (mem1 ret) rom)
             (fun r => getr r 2 = at_ sp (-16) /\ getr r 10 = beg /\ getr r 11 = Z0 /\ getr r 12 = at_ beg dAE
                       /\ getr r 13 = Z_to_bv 64 N /\ getr r 14 = at_ beg N /\ getr r 15 = at_ beg dAB
                       /\ regs_agree CL regs r)).
    { eexists. split.
      - an C0 D_aa054.                            (* [comment removed for export] *)
        chain_step; [reflexivity
          | eapply step_sd_at with (a := at_ sp (-8)) (v := ret);
            [exact C4 | reflexivity | exact D_aa058
            | gres; rwH; imm_norm; rewrite ?at_addi; zlit_at; reflexivity
            | gres; rwH; reflexivity
            | exact Hstk]
          | step_simpl]; change (wbytes mem (at_ sp (-8)) (word_to_le_bytes 8 ret)) with (mem1 ret); vn.
                                                  (* [comment removed for export] *)
        an C8 D_aa05c.                            (* [comment removed for export] *)
        an C12 D_aa060.                           (* [comment removed for export] *)
        an C16 D_aa064.                           (* [comment removed for export] *)
        an C20 D_aa068.                           (* [comment removed for export] *)
        ab_ft C24 D_aa06c ltac:(condz).           (* [comment removed for export] *)
        an C28 D_aa070.                           (* [comment removed for export] *)
        av C32 D_aa074 (at_ beg N) ltac:(apply v_add_at; lia).              (* [comment removed for export] *)
        an C36 D_aa078.                           (* [comment removed for export] *)
        av C40 D_aa07c (at_ beg dAB) ltac:(rewrite v_andi_m8 by lia; unfold dAB; f_equal; lia).  (* [comment removed for export] *)
        av C44 D_aa080 (at_ beg dAE) ltac:(rewrite v_andi_m8 by lia; unfold dAE; reflexivity).    (* [comment removed for export] *)
        apply mst_refl.
      - post. unfold memisz_clob'. solve_regs_agree. }
    cbv beta. intros r0 (R2 & R10 & R11 & R12 & R13 & R14 & R15 & AG0).
    (* [comment removed for export] *)
    enough (G : exists regs',
      msteps segs (mkst r0 (at_ base 48) (mem1 ret) rom) (mkst regs' ret (mem1 ret) rom)
      /\ regs_agree CL regs regs' /\ getr regs' 10 = Z_to_bv 64 1 /\ getr regs' 2 = sp /\ getr regs' 1 = ret).
    { destruct G as (r' & RUN & AG & P10 & P2 & P1). exists r'. split; [exact RUN|]. split; [|repeat split; assumption].
      apply (regs_agree_strengthen memisz_clob memisz_clob'); [exact AG|].
      intros r Hr Hnr. unfold memisz_clob', memisz_clob in *. cbn [In] in Hr.
      destruct Hr as [<-|[<-|Hr]]; [rewrite P1, H1; reflexivity | rewrite P2, H2; reflexivity |].
      exfalso. apply Hnr. cbn [In]. tauto. }
    destruct (Z.eq_dec dAB 0) as [HA0|HA0].
    - (* [comment removed for export] *)
      eapply (runs_trans segs _ (fun r => mkst r (at_ base 88) (mem1 ret) rom)
               (fun r => getr r 2 = at_ sp (-16) /\ getr r 10 = beg /\ getr r 11 = Z0 /\ getr r 12 = at_ beg dAE
                         /\ getr r 14 = at_ beg N /\ getr r 15 = at_ beg dAB /\ regs_agree CL regs r)).
      + eexists. split.
        * ab_tk C48 D_aa084 ltac:(rewrite <- (at_0 beg) at 1; condz).   (* [comment removed for export] *)
          apply mst_refl.
        * post; exact AG0.
      + cbv beta. intros r1 (S2 & S10 & S11 & S12 & S14 & S15 & AG).
        destruct (mid_run r1 ret Hret S2 S10 S11 S12 S14 S15) as (r2 & RUN & AG2 & P). exists r2.
        split; [exact RUN | split; [eapply regs_agree_trans; eassumption | exact P]].
    - destruct (Z.eq_dec N 0) as [HN0|HN0].
      + (* [comment removed for export] *)
        eapply (runs_trans segs _ (fun r => mkst r (at_ base 88) (mem1 ret) rom)
                 (fun r => getr r 2 = at_ sp (-16) /\ getr r 10 = beg /\ getr r 11 = Z0 /\ getr r 12 = at_ beg dAE
                           /\ getr r 14 = at_ beg N /\ getr r 15 = at_ beg dAB /\ regs_agree CL regs r)).
        * eexists. split.
          -- ab_ft C48 D_aa084 ltac:(rewrite <- (at_0 beg) at 1; condz).  (* [comment removed for export] *)
             ab_tk C52 D_aa088 ltac:(condz).                              (* [comment removed for export] *)
             apply mst_refl.
          -- post; exact AG0.
        * cbv beta. intros r1 (S2 & S10 & S11 & S12 & S14 & S15 & AG).
          destruct (mid_run r1 ret Hret S2 S10 S11 S12 S14 S15) as (r2 & RUN & AG2 & P). exists r2.
          split; [exact RUN | split; [eapply regs_agree_trans; eassumption | exact P]].
      + (* [comment removed for export] *)
        eapply (runs_trans segs _ (fun r => mkst r (at_ base 64) (mem1 ret) rom)
                 (fun r => getr r 2 = at_ sp (-16) /\ getr r 10 = beg /\ getr r 11 = Z0 /\ getr r 12 = at_ beg dAE
                           /\ getr r 13 = at_ beg (0 + 1) /\ getr r 14 = at_ beg N /\ getr r 15 = at_ beg dAB
                           /\ regs_agree CL regs r)).
        * eexists. split.
          -- ab_ft C48 D_aa084 ltac:(rewrite <- (at_0 beg) at 1; condz).  (* [comment removed for export] *)
             ab_ft C52 D_aa088 ltac:(condz).                              (* [comment removed for export] *)
             an C56 D_aa08c.                                              (* [comment removed for export] *)
             an C60 D_aa090.                                              (* [comment removed for export] *)
             apply mst_refl.
          -- post. unfold memisz_clob'. ra_chain.
        * cbv beta. intros r1 (S2 & S10 & S11 & S12 & S13 & S14 & S15 & AG).
          destruct (pro_loop (Z.to_nat (Z.min dAB N - 1)) r1 ret 0 Hret S2 S10 S11 S12 S13 S14 S15
                      ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (r2 & RUN & AG2 & P). exists r2.
          split; [exact RUN | split; [eapply regs_agree_trans; eassumption | exact P]].
  Qed.
End MEMISZERO.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

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

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From OssFuzzTheorems.openssl.echconfiglist_parser.images Require Import AsanUbsan.

(* [comment removed for export] *)
Definition asan_mem_is_zero_entry : word := 0x1d154c.

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
