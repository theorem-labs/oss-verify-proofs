(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Require OSSVerify.Proofs.fast_float.from_chars.lib.Ox.F112_010.   (* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require PropExec CatExec CatSim SeqExec.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require StepTac.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require StepTac.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require StepTac.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.PropExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.CatExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.CatSim OSSVerify.Proofs.fast_float.from_chars.lib.Common.SeqExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.StepTac.MmapSim OSSVerify.Proofs.fast_float.from_chars.lib.Common.StepTac OSSVerify.Proofs.fast_float.from_chars.lib.Common.StepTac.Hoare.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require Import Asan_code_m2s Asan_code_rpz.

Module AsanMemIsZ.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require Import AsanSumsLib Asan_code_miz.
Import ListNotations.
Local Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Section WithFP1.
Context {fx : FPState}.
Definition memisz_words : list (bv 32) :=
  [W_73964; W_73968; W_7396c; W_73970; W_73974; W_73978; W_7397c; W_73980;
   W_73984; W_73988; W_7398c; W_73990; W_73994; W_73998; W_7399c; W_739a0;
   W_739a4; W_739a8; W_739ac; W_739b0; W_739b4; W_739b8; W_739bc; W_739c0;
   W_739c4; W_739c8; W_739cc; W_739d0; W_739d4; W_739d8; W_739dc; W_739e0;
   W_739e4; W_739e8; W_739ec; W_739f0; W_739f4; W_739f8; W_739fc].

(* [comment removed for export] *)
Definition memisz_clob : list reg := [10; 11; 12; 13; 14; 15; 16].
(* [comment removed for export] *)
Definition memisz_clob' : list reg := [1; 2; 10; 11; 12; 13; 14; 15; 16].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma land_m8 : forall a, (0 <= a < 2 ^ 64)%Z -> Z.land a (2 ^ 64 - 2 ^ 3) = (a - a mod 8)%Z.
Proof. LiaFast.lf_pins LiaFast.u0.
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
#[using="Type"] Lemma v_andi_m8 : forall (a : word) d,
  (0 <= bv_unsigned a + d < 2 ^ 64)%Z ->
  v_andi (at_ a d) (-8) = at_ a (d - (bv_unsigned a + d) mod 8).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros a d Hd. unfold v_andi, at_. f_equal.
  change (bv_wrap 64 (-8)) with (2 ^ 64 - 2 ^ 3)%Z.
  rewrite u_Z2bv by lia. rewrite land_m8 by lia. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rdn_all1 : forall segs m n (a : word) b,
  (bv_unsigned a + Z.of_nat n <= 2 ^ 64)%Z ->
  (forall x : word, (bv_unsigned a <= bv_unsigned x < bv_unsigned a + Z.of_nat n)%Z ->
     rdn segs m x 1 = Some [b]) ->
  rdn segs m a n = Some (repeat b n).
Proof. LiaFast.lf_pins LiaFast.u0.
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

#[using="Type"] Lemma regs_agree_upd_same : forall (C : regset) regs regs' (r : reg) v,
  regs_agree C regs regs' -> getr regs r = v -> r <> 0 -> regs_agree C regs (regupd regs' r v).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros C regs regs' r v AG Hv Hnz x Hx.
  destruct (decide (x = r)) as [->|Hne].
  - rewrite getr_same by exact Hnz. symmetry. exact Hv.
  - rewrite getr_other by exact Hne. apply AG, Hx.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma regs_agree_strengthen : forall (l l' : list reg) regs regs',
  regs_agree (fun r => In r l') regs regs' ->
  (forall r, In r l' -> ~ In r l -> getr regs' r = getr regs r) ->
  regs_agree (fun r => In r l) regs regs'.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros l l' regs regs' AG E r Hr.
  destruct (In_dec (fun x y : reg => decide (x = y)) r l') as [Hin|Hnin].
  - apply E; assumption.
  - apply AG, Hnin.
Qed.

End WithFP1.
Section MEMISZERO.
Context {fx : FPState}.
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

  #[using="Type"] Lemma dAB_range : (0 <= dAB <= 7)%Z.
  Proof. LiaFast.lf_pins LiaFast.u0. unfold dAB. pose proof (Z.mod_pos_bound (B + 7) 8 ltac:(lia)). lia. Qed.

  #[using="sp HN Hsp"] Lemma dAE_range : (N - 7 <= dAE <= N)%Z /\ (0 <= B + dAE)%Z.
  Proof. LiaFast.lf_pins (fun (sp HN Hsp : LiaFast.U) => LiaFast.u0).
    unfold dAE. pose proof (u64_range beg). pose proof (Z.mod_pos_bound (B + N) 8 ltac:(lia)).
    pose proof (Z.div_mod (B + N) 8 ltac:(lia)). nia.
  Qed.

  (* [comment removed for export] *)
  #[using="Hnw Hsp Hdisj Hz"] Lemma rd1 : forall ra j, (0 <= j < N)%Z -> rdn segs (mem1 ra) (at_ beg j) 1 = Some [Z_to_bv 8 0].
  Proof. LiaFast.lf_pins (fun (Hnw Hsp Hdisj Hz : LiaFast.U) => LiaFast.u0).
    intros ra j Hj. pose proof (u64_range beg). pose proof (u64_range sp). unfold mem1.
    rewrite rdn_wbytes_out; rewrite ?length_N_to_le_bytes, ?at_u; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; try lia.
    apply Hz. rewrite at_u; lia.
  Qed.

  #[using="Hnw Hsp Hdisj Hz"] Lemma rd8 : forall ra j, (0 <= j)%Z -> (j + 8 <= N)%Z -> rdn segs (mem1 ra) (at_ beg j) 8 = Some (zeros 8).
  Proof. LiaFast.lf_pins (fun (Hnw Hsp Hdisj Hz : LiaFast.U) => LiaFast.u0).
    intros ra j Hj H8. pose proof (u64_range beg). unfold zeros. apply rdn_all1; [rewrite at_u; cbn; lia|].
    intros x Hx. rewrite at_u in Hx by lia. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hx.
    replace x with (at_ beg (bv_unsigned x - B)).
    - apply rd1. lia.
    - unfold at_. rewrite <- (Z_to_bv_bv_unsigned 64 x) at 2. f_equal. lia.
  Qed.

  #[using="Hsp"] Lemma rd_ra : forall ra, rdn segs (mem1 ra) (at_ sp (-8)) 8 = Some (word_to_le_bytes 8 ra).
  Proof. LiaFast.lf_pins (fun (Hsp : LiaFast.U) => LiaFast.u0). intros ra. unfold mem1. apply rdn_wbytes_hit8. pose proof (u64_range sp). rewrite at_u; lia. Qed.

  Ltac get_code :=
    let HC := fresh "HC" in
    pose proof HCODE as HC; cbn [code_at memisz_words Z.add Pos.add Pos.succ] in HC;
    destruct HC as (C0 & C4 & C8 & C12 & C16 & C20 & C24 & C28 & C32 & C36 & C40 & C44 & C48 & C52 & C56
                    & C60 & C64 & C68 & C72 & C76 & C80 & C84 & C88 & C92 & C96 & C100 & C104 & C108 & C112
                    & C116 & C120 & C124 & C128 & C132 & C136 & C140 & C144 & C148 & C152 & _).

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
  #[using="HCODE Hsp"] Lemma fin_run : forall regs (ret : word),
    ret_ok ret -> getr regs 2 = at_ sp (-16) -> getr regs 11 = Z0 ->
    exists regs',
      msteps segs (mkst regs (at_ base 140) (mem1 ret) rom) (mkst regs' ret (mem1 ret) rom)
      /\ regs_agree CL regs regs' /\ getr regs' 10 = Z_to_bv 64 1 /\ getr regs' 2 = sp /\ getr regs' 1 = ret.
  Proof. LiaFast.lf_pins (fun (HCODE Hsp : LiaFast.U) => LiaFast.u0).
    get_code. intros regs ret Hret H2 H11. pose proof (u64_range sp).
    eexists. split; [|split; [|split; [|split]]].
    - an C140 D_739f0.                            (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_ld with (v := ret);
          [exact C144 | reflexivity | exact D_739f4
          | gres; rwH; imm_norm; rewrite ?at_addi; zlit_at; apply rd_ra
          | apply bytes_le_to_Z_8]
        | step_simpl]; vn.                         (* [comment removed for export] *)
      an C148 D_739f8.                            (* [comment removed for export] *)
      aret C152 D_739fc ret.
      apply mst_refl.
    - unfold memisz_clob'. solve_regs_agree.
    - gres. reflexivity.
    - gres. rewrite ?at_0. reflexivity.
    - gres. reflexivity.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="HCODE HN Hnw Hsp Hdisj Hz"] Lemma ep_loop : forall (i : nat) regs (ret : word) q cnt,
    ret_ok ret -> getr regs 2 = at_ sp (-16) -> getr regs 11 = Z0 ->
    getr regs 12 = at_ beg q -> getr regs 14 = Z_to_bv 64 cnt ->
    (0 <= q)%Z -> (1 <= cnt)%Z -> (q + cnt <= N)%Z -> Z.of_nat i = (cnt - 1)%Z ->
    exists regs',
      msteps segs (mkst regs (at_ base 120) (mem1 ret) rom) (mkst regs' ret (mem1 ret) rom)
      /\ regs_agree CL regs regs' /\ getr regs' 10 = Z_to_bv 64 1 /\ getr regs' 2 = sp /\ getr regs' 1 = ret.
  Proof. LiaFast.lf_pins (fun (HCODE HN Hnw Hsp Hdisj Hz : LiaFast.U) => LiaFast.u0).
    get_code. pose proof (u64_range beg) as Hb.
    induction i as [|i IH]; intros regs ret q cnt Hret H2 H11 H12 H14 Hq Hc Hqc Hi.
    - eapply (runs_trans segs _ (fun r => mkst r (at_ base 140) (mem1 ret) rom)
               (fun r => getr r 2 = at_ sp (-16) /\ getr r 11 = Z0 /\ regs_agree CL regs r)).
      + eexists. split.
        * mlbu C120 D_739dc.                      (* [comment removed for export] *)
          av C124 D_739e0 (Z_to_bv 64 (cnt - 1)) ltac:(unfold v_addi; unorm; f_equal; lia).  (* [comment removed for export] *)
          an C128 D_739e4.                        (* [comment removed for export] *)
          an C132 D_739e8.                        (* [comment removed for export] *)
          ab_ft C136 D_739ec ltac:(condz).        (* [comment removed for export] *)
          apply mst_refl.
        * post. unfold memisz_clob'. solve_regs_agree.
      + cbv beta. intros r1 (R2 & R11 & AG).
        destruct (fin_run r1 ret Hret R2 R11) as (r2 & RUN & AG2 & P). exists r2.
        split; [exact RUN | split; [eapply regs_agree_trans; eassumption | exact P]].
    - eapply (runs_trans segs _ (fun r => mkst r (at_ base 120) (mem1 ret) rom)
               (fun r => getr r 2 = at_ sp (-16) /\ getr r 11 = Z0 /\ getr r 12 = at_ beg (q + 1)
                         /\ getr r 14 = Z_to_bv 64 (cnt - 1) /\ regs_agree CL regs r)).
      + eexists. split.
        * mlbu C120 D_739dc.
          av C124 D_739e0 (Z_to_bv 64 (cnt - 1)) ltac:(unfold v_addi; unorm; f_equal; lia).
          an C128 D_739e4.
          an C132 D_739e8.
          ab_tk C136 D_739ec ltac:(condz).        (* [comment removed for export] *)
          apply mst_refl.
        * post. unfold memisz_clob'. solve_regs_agree.
      + cbv beta. intros r1 (R2 & R11 & R12 & R14 & AG).
        destruct (IH r1 ret (q + 1)%Z (cnt - 1)%Z Hret R2 R11 R12 R14 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
          as (r2 & RUN & AG2 & P). exists r2.
        split; [exact RUN | split; [eapply regs_agree_trans; eassumption | exact P]].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="HCODE HN Hnw Hsp Hdisj Hz"] Lemma tail_run : forall regs (ret : word),
    ret_ok ret -> getr regs 2 = at_ sp (-16) -> getr regs 10 = beg -> getr regs 11 = Z0 ->
    getr regs 12 = at_ beg dAE -> getr regs 14 = at_ beg N ->
    exists regs',
      msteps segs (mkst regs (at_ base 108) (mem1 ret) rom) (mkst regs' ret (mem1 ret) rom)
      /\ regs_agree CL regs regs' /\ getr regs' 10 = Z_to_bv 64 1 /\ getr regs' 2 = sp /\ getr regs' 1 = ret.
  Proof. LiaFast.lf_pins (fun (HCODE HN Hnw Hsp Hdisj Hz : LiaFast.U) => LiaFast.u0).
    get_code. intros regs ret Hret H2 H10 H11 H12 H14.
    pose proof (u64_range beg) as Hb. pose proof dAE_range as HdAE.
    destruct (Z.lt_ge_cases dAE 0) as [Hneg|Hnn].
    - (* [comment removed for export] *)
      eapply (runs_trans segs _ (fun r => mkst r (at_ base 140) (mem1 ret) rom)
               (fun r => getr r 2 = at_ sp (-16) /\ getr r 11 = Z0 /\ regs_agree CL regs r)).
      + eexists. split.
        * ab_tk C108 D_739d0 ltac:(rewrite <- (at_0 beg) at 2; condz).   (* [comment removed for export] *)
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
          -- ab_ft C108 D_739d0 ltac:(rewrite <- (at_0 beg) at 2; condz).  (* [comment removed for export] *)
             ab_ft C112 D_739d4 ltac:(condz).                              (* [comment removed for export] *)
             av C116 D_739d8 (Z_to_bv 64 (N - dAE)) ltac:(unfold v_sub, at_; unorm; f_equal; lia).  (* [comment removed for export] *)
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
          -- ab_ft C108 D_739d0 ltac:(rewrite <- (at_0 beg) at 2; condz).  (* [comment removed for export] *)
             ab_tk C112 D_739d4 ltac:(condz).                              (* [comment removed for export] *)
             apply mst_refl.
          -- post; apply regs_agree_refl.
        * cbv beta. intros r1 (R2 & R11 & AG).
          destruct (fin_run r1 ret Hret R2 R11) as (r2 & RUN & AG2 & P). exists r2.
          split; [exact RUN | split; [eapply regs_agree_trans; eassumption | exact P]].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="HCODE HN Hnw Hsp Hdisj Hz"] Lemma w_loop : forall (i : nat) regs (ret : word) p,
    ret_ok ret -> getr regs 2 = at_ sp (-16) -> getr regs 10 = beg -> getr regs 11 = Z0 ->
    getr regs 12 = at_ beg dAE -> getr regs 14 = at_ beg N -> getr regs 15 = at_ beg p ->
    (0 <= p)%Z -> (p + 8 <= dAE)%Z -> (Z.of_nat i * 8 = dAE - p - 8)%Z ->
    exists regs',
      msteps segs (mkst regs (at_ base 92) (mem1 ret) rom) (mkst regs' ret (mem1 ret) rom)
      /\ regs_agree CL regs regs' /\ getr regs' 10 = Z_to_bv 64 1 /\ getr regs' 2 = sp /\ getr regs' 1 = ret.
  Proof. LiaFast.lf_pins (fun (HCODE HN Hnw Hsp Hdisj Hz : LiaFast.U) => LiaFast.u0).
    get_code. pose proof (u64_range beg) as Hb. pose proof dAE_range as HdAE.
    induction i as [|i IH]; intros regs ret p Hret H2 H10 H11 H12 H14 H15 Hp Hp8 Hi.
    - eapply (runs_trans segs _ (fun r => mkst r (at_ base 108) (mem1 ret) rom)
               (fun r => getr r 2 = at_ sp (-16) /\ getr r 10 = beg /\ getr r 11 = Z0 /\ getr r 12 = at_ beg dAE
                         /\ getr r 14 = at_ beg N /\ regs_agree CL regs r)).
      + eexists. split.
        * mld C92 D_739c0.                        (* [comment removed for export] *)
          an C96 D_739c4.                         (* [comment removed for export] *)
          an C100 D_739c8.                        (* [comment removed for export] *)
          ab_ft C104 D_739cc ltac:(condz).        (* [comment removed for export] *)
          apply mst_refl.
        * post. unfold memisz_clob'. solve_regs_agree.
      + cbv beta. intros r1 (R2 & R10 & R11 & R12 & R14 & AG).
        destruct (tail_run r1 ret Hret R2 R10 R11 R12 R14) as (r2 & RUN & AG2 & P). exists r2.
        split; [exact RUN | split; [eapply regs_agree_trans; eassumption | exact P]].
    - eapply (runs_trans segs _ (fun r => mkst r (at_ base 92) (mem1 ret) rom)
               (fun r => getr r 2 = at_ sp (-16) /\ getr r 10 = beg /\ getr r 11 = Z0 /\ getr r 12 = at_ beg dAE
                         /\ getr r 14 = at_ beg N /\ getr r 15 = at_ beg (p + 8) /\ regs_agree CL regs r)).
      + eexists. split.
        * mld C92 D_739c0.
          an C96 D_739c4.
          an C100 D_739c8.
          ab_tk C104 D_739cc ltac:(condz).        (* [comment removed for export] *)
          apply mst_refl.
        * post. unfold memisz_clob'. solve_regs_agree.
      + cbv beta. intros r1 (R2 & R10 & R11 & R12 & R14 & R15 & AG).
        destruct (IH r1 ret (p + 8)%Z Hret R2 R10 R11 R12 R14 R15 ltac:(lia) ltac:(lia) ltac:(lia))
          as (r2 & RUN & AG2 & P). exists r2.
        split; [exact RUN | split; [eapply regs_agree_trans; eassumption | exact P]].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="HCODE HN Hnw Hsp Hdisj Hz"] Lemma mid_run : forall regs (ret : word),
    ret_ok ret -> getr regs 2 = at_ sp (-16) -> getr regs 10 = beg -> getr regs 11 = Z0 ->
    getr regs 12 = at_ beg dAE -> getr regs 14 = at_ beg N -> getr regs 15 = at_ beg dAB ->
    exists regs',
      msteps segs (mkst regs (at_ base 88) (mem1 ret) rom) (mkst regs' ret (mem1 ret) rom)
      /\ regs_agree CL regs regs' /\ getr regs' 10 = Z_to_bv 64 1 /\ getr regs' 2 = sp /\ getr regs' 1 = ret.
  Proof. LiaFast.lf_pins (fun (HCODE HN Hnw Hsp Hdisj Hz : LiaFast.U) => LiaFast.u0).
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
        * ab_ft C88 D_739bc ltac:(condz).         (* [comment removed for export] *)
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
        * ab_tk C88 D_739bc ltac:(condz).         (* [comment removed for export] *)
          apply mst_refl.
        * post; apply regs_agree_refl.
      + cbv beta. intros r1 (R2 & R10 & R11 & R12 & R14 & AG).
        destruct (tail_run r1 ret Hret R2 R10 R11 R12 R14) as (r2 & RUN & AG2 & P). exists r2.
        split; [exact RUN | split; [eapply regs_agree_trans; eassumption | exact P]].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="HCODE HN Hnw Hsp Hdisj Hz"] Lemma pro_loop : forall (i : nat) regs (ret : word) j,
    ret_ok ret -> getr regs 2 = at_ sp (-16) -> getr regs 10 = beg -> getr regs 11 = Z0 ->
    getr regs 12 = at_ beg dAE -> getr regs 13 = at_ beg (j + 1) -> getr regs 14 = at_ beg N ->
    getr regs 15 = at_ beg dAB ->
    (0 <= j)%Z -> (j < dAB)%Z -> (j < N)%Z -> Z.of_nat i = (Z.min dAB N - 1 - j)%Z ->
    exists regs',
      msteps segs (mkst regs (at_ base 64) (mem1 ret) rom) (mkst regs' ret (mem1 ret) rom)
      /\ regs_agree CL regs regs' /\ getr regs' 10 = Z_to_bv 64 1 /\ getr regs' 2 = sp /\ getr regs' 1 = ret.
  Proof. LiaFast.lf_pins (fun (HCODE HN Hnw Hsp Hdisj Hz : LiaFast.U) => LiaFast.u0).
    get_code. pose proof (u64_range beg) as Hb. pose proof dAE_range as HdAE. pose proof dAB_range as HdAB.
    induction i as [|i IH]; intros regs ret j Hret H2 H10 H11 H12 H13 H14 H15 Hj HjA HjN Hi.
    - (* [comment removed for export] *)
      destruct (Z.eq_dec (j + 1) dAB) as [HA|HA].
      + eapply (runs_trans segs _ (fun r => mkst r (at_ base 88) (mem1 ret) rom)
                 (fun r => getr r 2 = at_ sp (-16) /\ getr r 10 = beg /\ getr r 11 = Z0 /\ getr r 12 = at_ beg dAE
                           /\ getr r 14 = at_ beg N /\ getr r 15 = at_ beg dAB /\ regs_agree CL regs r)).
        * eexists. split.
          -- an C64 D_739a4.                      (* [comment removed for export] *)
             mlbu C68 D_739a8.                    (* [comment removed for export] *)
             an C72 D_739ac.                      (* [comment removed for export] *)
             ab_tk C76 D_739b0 ltac:(condz).      (* [comment removed for export] *)
             apply mst_refl.
          -- post. unfold memisz_clob'. solve_regs_agree.
        * cbv beta. intros r1 (R2 & R10 & R11 & R12 & R14 & R15 & AG).
          destruct (mid_run r1 ret Hret R2 R10 R11 R12 R14 R15) as (r2 & RUN & AG2 & P). exists r2.
          split; [exact RUN | split; [eapply regs_agree_trans; eassumption | exact P]].
      + eapply (runs_trans segs _ (fun r => mkst r (at_ base 88) (mem1 ret) rom)
                 (fun r => getr r 2 = at_ sp (-16) /\ getr r 10 = beg /\ getr r 11 = Z0 /\ getr r 12 = at_ beg dAE
                           /\ getr r 14 = at_ beg N /\ getr r 15 = at_ beg dAB /\ regs_agree CL regs r)).
        * eexists. split.
          -- an C64 D_739a4.                      (* [comment removed for export] *)
             mlbu C68 D_739a8.                    (* [comment removed for export] *)
             an C72 D_739ac.                      (* [comment removed for export] *)
             ab_ft C76 D_739b0 ltac:(condz).      (* [comment removed for export] *)
             an C80 D_739b4.                      (* [comment removed for export] *)
             ab_ft C84 D_739b8 ltac:(condz).      (* [comment removed for export] *)
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
        * an C64 D_739a4.
          mlbu C68 D_739a8.
          an C72 D_739ac.
          ab_ft C76 D_739b0 ltac:(condz).         (* [comment removed for export] *)
          an C80 D_739b4.
          ab_tk C84 D_739b8 ltac:(condz).         (* [comment removed for export] *)
          apply mst_refl.
        * post. unfold memisz_clob'. solve_regs_agree.
      + cbv beta. intros r1 (R2 & R10 & R11 & R12 & R13 & R14 & R15 & AG).
        destruct (IH r1 ret (j + 1)%Z Hret R2 R10 R11 R12 R13 R14 R15 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
          as (r2 & RUN & AG2 & P). exists r2.
        split; [exact RUN | split; [eapply regs_agree_trans; eassumption | exact P]].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="HCODE HN Hnw Hsp Hstk Hdisj Hz"] Theorem mem_is_zero_run : forall regs (ret : word),
    ret_ok ret -> getr regs 1 = ret -> getr regs 2 = sp ->
    getr regs 10 = beg -> getr regs 11 = Z_to_bv 64 N ->
    exists regs',
      msteps segs (mkst regs (at_ base 0) mem rom) (mkst regs' ret (mem1 ret) rom)
      /\ regs_agree (fun r => In r memisz_clob) regs regs'
      /\ getr regs' 10 = Z_to_bv 64 1 /\ getr regs' 2 = sp /\ getr regs' 1 = ret.
  Proof. LiaFast.lf_pins (fun (HCODE HN Hnw Hsp Hstk Hdisj Hz : LiaFast.U) => LiaFast.u0).
    get_code. intros regs ret Hret H1 H2 H10 H11.
    pose proof (u64_range beg) as Hb. pose proof (u64_range sp) as Hs.
    pose proof dAE_range as HdAE. pose proof dAB_range as HdAB.
    (* [comment removed for export] *)
    eapply (runs_trans segs _ (fun r => mkst r (at_ base 48) (mem1 ret) rom)
             (fun r => getr r 2 = at_ sp (-16) /\ getr r 10 = beg /\ getr r 11 = Z0 /\ getr r 12 = at_ beg dAE
                       /\ getr r 13 = Z_to_bv 64 N /\ getr r 14 = at_ beg N /\ getr r 15 = at_ beg dAB
                       /\ regs_agree CL regs r)).
    { eexists. split.
      - an C0 D_73964.                            (* [comment removed for export] *)
        chain_step; [reflexivity
          | eapply step_sd_at with (a := at_ sp (-8)) (v := ret);
            [exact C4 | reflexivity | exact D_73968
            | gres; rwH; imm_norm; rewrite ?at_addi; zlit_at; reflexivity
            | gres; rwH; reflexivity
            | exact Hstk]
          | step_simpl]; change (wbytes mem (at_ sp (-8)) (word_to_le_bytes 8 ret)) with (mem1 ret); vn.
                                                  (* [comment removed for export] *)
        an C8 D_7396c.                            (* [comment removed for export] *)
        an C12 D_73970.                           (* [comment removed for export] *)
        an C16 D_73974.                           (* [comment removed for export] *)
        an C20 D_73978.                           (* [comment removed for export] *)
        ab_ft C24 D_7397c ltac:(condz).           (* [comment removed for export] *)
        an C28 D_73980.                           (* [comment removed for export] *)
        av C32 D_73984 (at_ beg N) ltac:(apply v_add_at; lia).              (* [comment removed for export] *)
        an C36 D_73988.                           (* [comment removed for export] *)
        av C40 D_7398c (at_ beg dAB) ltac:(rewrite v_andi_m8 by lia; unfold dAB; f_equal; lia).  (* [comment removed for export] *)
        av C44 D_73990 (at_ beg dAE) ltac:(rewrite v_andi_m8 by lia; unfold dAE; reflexivity).    (* [comment removed for export] *)
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
        * ab_tk C48 D_73994 ltac:(rewrite <- (at_0 beg) at 1; condz).   (* [comment removed for export] *)
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
          -- ab_ft C48 D_73994 ltac:(rewrite <- (at_0 beg) at 1; condz).  (* [comment removed for export] *)
             ab_tk C52 D_73998 ltac:(condz).                              (* [comment removed for export] *)
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
          -- ab_ft C48 D_73994 ltac:(rewrite <- (at_0 beg) at 1; condz).  (* [comment removed for export] *)
             ab_ft C52 D_73998 ltac:(condz).                              (* [comment removed for export] *)
             an C56 D_7399c.                                              (* [comment removed for export] *)
             an C60 D_739a0.                                              (* [comment removed for export] *)
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

Section WithFP2.
Context {fx : FPState}.
#[using="Type"] Lemma slot_at : forall sp : word, (16 <= bv_unsigned sp)%Z ->
  at_ sp (-8) = Z_to_bv 64 (bv_unsigned sp - 8).
Proof. LiaFast.lf_pins LiaFast.u0. intros sp Hsp. unfold at_. f_equal; lia. Qed.

#[using="Type"] Theorem mem_is_zero_summary : forall segs (base : word) mem (beg sp : word) N rom regs (ret : word),
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
Proof. LiaFast.lf_pins LiaFast.u0.
  intros segs base mem beg sp N rom regs ret HC HN Hnw Hsp Hstk Hdisj Hz.
  rewrite <- (slot_at sp Hsp) in Hstk |- *. rewrite <- (at_0 base).
  apply (mem_is_zero_run segs base mem beg sp N rom HC HN Hnw Hsp Hstk Hdisj Hz).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

End WithFP2.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.

(* [comment removed for export] *)
Section WithFP3.
Context {fx : FPState}.
Definition asan_mem_is_zero_entry : word := 0x73964.

#[using="Type"] Lemma asan_mem_is_zero_code :
  code_at AsanUbsan.M.loaded_segments asan_mem_is_zero_entry 0 memisz_words.
Proof. LiaFast.lf_pins LiaFast.u0. unfold memisz_words. code_at_vm. Qed.

#[using="Type"] Theorem asan_mem_is_zero : forall mem (beg sp : word) N rom regs (ret : word),
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
Proof. LiaFast.lf_pins LiaFast.u0.
  intros mem beg sp N rom regs ret.
  apply (mem_is_zero_summary _ _ mem beg sp N rom regs ret asan_mem_is_zero_code).
Qed.

End WithFP3.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
(* [comment removed for export] *)
End AsanMemIsZ.

Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Abbreviation SEGS := AsanUbsan.M.loaded_segments.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithFP1.
Context {fx : FPState}.
#[using="Type"] Lemma zbv_u : forall z, (0 <= z < 2 ^ 64)%Z -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. LiaFast.lf_pins LiaFast.u0. intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64)%Z. exact Hz. Qed.

#[using="Type"] Lemma zbv_self : forall (x : word), Z_to_bv 64 (bv_unsigned x) = x.
Proof. LiaFast.lf_pins LiaFast.u0. intros x. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.

#[using="Type"] Lemma v_addi_zbv : forall z i, (0 <= z < 2 ^ 64)%Z -> v_addi (Z_to_bv 64 z) i = Z_to_bv 64 (z + i).
Proof. LiaFast.lf_pins LiaFast.u0. intros z i Hz. unfold v_addi. rewrite zbv_u by exact Hz. reflexivity. Qed.

#[using="Type"] Lemma v_add_zbv : forall a b, (0 <= a < 2 ^ 64)%Z -> (0 <= b < 2 ^ 64)%Z ->
  v_add (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a + b).
Proof. LiaFast.lf_pins LiaFast.u0. intros a b Ha Hb. unfold v_add. rewrite !zbv_u by assumption. reflexivity. Qed.

#[using="Type"] Lemma v_sub_zbv : forall a b, (0 <= a < 2 ^ 64)%Z -> (0 <= b < 2 ^ 64)%Z ->
  v_sub (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a - b).
Proof. LiaFast.lf_pins LiaFast.u0. intros a b Ha Hb. unfold v_sub. rewrite !zbv_u by assumption. reflexivity. Qed.

#[using="Type"] Lemma v_or_zero : forall (x : word), v_or x (Z_to_bv 64 0) = x.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros x. unfold v_or. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. rewrite Z.lor_0_r. apply zbv_self.
Qed.

#[using="Type"] Lemma v_or_zero_l : forall (x : word), v_or (Z_to_bv 64 0) x = x.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros x. unfold v_or. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. rewrite Z.lor_0_l. apply zbv_self.
Qed.

#[using="Type"] Lemma land_m8 : forall z, (0 <= z < 2 ^ 64)%Z -> Z.land z (2 ^ 64 - 8) = (z / 8 * 8)%Z.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros z Hz.
  assert (E : (2 ^ 64 - 8)%Z = Z.ldiff (Z.ones 64) (Z.ones 3)) by reflexivity.
  rewrite E. transitivity (Z.ldiff (Z.land z (Z.ones 64)) (Z.ones 3)).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, !Z.ldiff_spec, Z.land_spec.
    destruct (Z.testbit z i), (Z.testbit (Z.ones 64) i), (Z.testbit (Z.ones 3) i); reflexivity. }
  rewrite Z.land_ones by lia. rewrite Z.mod_small by lia. rewrite Z.ldiff_ones_r by lia.
  rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia. reflexivity.
Qed.

#[using="Type"] Lemma v_andi_m8 : forall z, (0 <= z < 2 ^ 64)%Z -> v_andi (Z_to_bv 64 z) (-8) = Z_to_bv 64 (z / 8 * 8).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros z Hz. unfold v_andi. rewrite zbv_u by exact Hz.
  change (bv_wrap 64 (-8)) with (2 ^ 64 - 8)%Z. rewrite land_m8 by exact Hz. reflexivity.
Qed.

#[using="Type"] Lemma c_ltu_zbv : forall a b, (0 <= a < 2 ^ 64)%Z -> (0 <= b < 2 ^ 64)%Z ->
  c_ltu (Z_to_bv 64 a) (Z_to_bv 64 b) = (a <? b)%Z.
Proof. LiaFast.lf_pins LiaFast.u0. intros a b Ha Hb. unfold c_ltu, bv_ltu. rewrite !zbv_u by assumption. reflexivity. Qed.

#[using="Type"] Lemma c_eq_zbv : forall a b, (0 <= a < 2 ^ 64)%Z -> (0 <= b < 2 ^ 64)%Z ->
  c_eq (Z_to_bv 64 a) (Z_to_bv 64 b) = (a =? b)%Z.
Proof. LiaFast.lf_pins LiaFast.u0. intros a b Ha Hb. unfold c_eq, bv_eqb. rewrite !zbv_u by assumption. reflexivity. Qed.

#[using="Type"] Lemma v_sltiu_zero1 : v_sltiu (Z_to_bv 64 0) 1 = Z_to_bv 64 1.
Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.

#[using="Type"] Lemma zbv_add1 : forall a, Z_to_bv 64 a + 1 = Z_to_bv 64 (a + 1).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros a. apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_unsigned (1 : word)) with 1%Z. change (bv_modulus 64) with (2 ^ 64)%Z.
  apply Zplus_mod_idemp_l.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma wbytes_none_back : forall bs m a x, wbytes m a bs x = None -> m x = None.
Proof. LiaFast.lf_pins LiaFast.u0.
  induction bs as [|b bs IH]; intros m a x H; cbn [wbytes] in H; [exact H|].
  apply IH in H. destruct (bv_eqb x a); [discriminate | exact H].
Qed.
#[using="Type"] Lemma store_ok1_wbytes : forall m a bs x,
  store_ok SEGS m x 1 = true -> store_ok SEGS (wbytes m a bs) x 1 = true.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros m a bs x H. cbn [store_ok] in H |- *. unfold wview in H |- *.
  destruct (wbytes m a bs x) eqn:E; [reflexivity|].
  rewrite (wbytes_none_back _ _ _ _ E) in H. exact H.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma store_ok_bytes : forall nb m (a : Z),
  (0 <= a)%Z -> (a + Z.of_nat nb < 2 ^ 64)%Z ->
  (forall j, (0 <= j < Z.of_nat nb)%Z -> store_ok SEGS m (Z_to_bv 64 (a + j)) 1 = true) ->
  store_ok SEGS m (Z_to_bv 64 a) nb = true.
Proof. LiaFast.lf_pins LiaFast.u0.
  induction nb as [|nb IH]; intros m a Ha Hw H; [reflexivity|].
  cbn [store_ok]. pose proof (H 0%Z ltac:(lia)) as H0. cbn [store_ok] in H0. rewrite Z.add_0_r in H0.
  destruct (wview SEGS m (Z_to_bv 64 a)); [|discriminate].
  rewrite zbv_add1. apply IH; [lia|lia|].
  intros j Hj. replace (a + 1 + j)%Z with (a + (1 + j))%Z by lia. apply H. lia.
Qed.
#[using="Type"] Lemma store_ok8_bytes : forall m (a : Z),
  (0 <= a)%Z -> (a + 8 < 2 ^ 64)%Z ->
  (forall j, (0 <= j < 8)%Z -> store_ok SEGS m (Z_to_bv 64 (a + j)) 1 = true) ->
  store_ok SEGS m (Z_to_bv 64 a) 8 = true.
Proof. LiaFast.lf_pins LiaFast.u0. intros m a Ha Hw H. apply store_ok_bytes; [exact Ha | cbn; lia | exact H]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Record mzH (mem : word -> option byte) (ub n usp : Z) : Prop := {
  mz_n    : (0 <= n <= 2 ^ 40)%Z;
  mz_ub   : (0 <= ub)%Z;
  mz_nw   : (ub + n + 8 < 2 ^ 64)%Z;
  mz_sp   : (16 <= usp < 2 ^ 64)%Z;
  mz_disj : (ub + n <= usp - 8 \/ usp <= ub)%Z;
  mz_zero : forall i, (0 <= i < n)%Z -> mem (Z_to_bv 64 (ub + i)) = Some (Z_to_bv 8 0);
  mz_stk  : store_ok SEGS mem (Z_to_bv 64 (usp - 8)) 8 = true
}.
Definition mz_clob (r : reg) : bool :=
  (bv_eqb r 10 || bv_eqb r 11 || bv_eqb r 12 || bv_eqb r 13 || bv_eqb r 14 || bv_eqb r 15 || bv_eqb r 16)%bool.

#[using="Type"] Lemma rdn1 : forall m (a : word) b, m a = Some b -> rdn SEGS m a 1 = Some [b].
Proof. LiaFast.lf_pins LiaFast.u0. intros m a b H. cbn [rdn]. rewrite H. reflexivity. Qed.

#[using="Type"] Theorem as_mem_is_zero : forall (mem rom : word -> option byte) (ub n usp : Z) (ra : word),
  mzH mem ub n usp ->
  forall regs,
    ret_ok ra ->
    getr regs 1 = ra -> getr regs 2 = Z_to_bv 64 usp ->
    getr regs 10 = Z_to_bv 64 ub -> getr regs 11 = Z_to_bv 64 n ->
    exists regs',
      msteps SEGS (mkst regs (0x73964 : word) mem rom)
                  (mkst regs' ra (wbytes mem (Z_to_bv 64 (usp - 8)) (word_to_le_bytes 8 ra)) rom)
      /\ getr regs' 10 = Z_to_bv 64 1
      /\ getr regs' 2 = Z_to_bv 64 usp
      /\ getr regs' 1 = ra
      /\ (forall r, mz_clob r = false -> r <> 2 -> r <> 1 -> getr regs' r = getr regs r).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros mem rom ub n usp ra H regs Hret H1 H2 H10 H11.
  destruct H as [Hn Hub Hnw Hsp Hdisj Hz Hstk].
  assert (U1 : bv_unsigned (Z_to_bv 64 ub) = ub) by (apply zbv_u; lia).
  assert (U2 : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply zbv_u; lia).
  destruct (AsanMemIsZ.asan_mem_is_zero mem (Z_to_bv 64 ub) (Z_to_bv 64 usp) n rom regs ra) as (regs' & Hms & Hag & Ha0 & Hsp' & Hra');
    rewrite ?U1, ?U2; try assumption; try lia.
  - intros a Ha. apply rdn1. replace a with (Z_to_bv 64 (ub + (bv_unsigned a - ub))) by (rewrite <- (zbv_self a) at 2; f_equal; lia).
    apply Hz. lia.
  - rewrite U2 in Hms. exists regs'. split; [exact Hms|]. split; [exact Ha0|]. split; [exact Hsp'|]. split; [exact Hra'|].
    intros r Hr N2 N1. apply Hag. unfold AsanMemIsZ.memisz_clob. cbn [In].
    unfold mz_clob in Hr. repeat (apply orb_false_iff in Hr; destruct Hr as [Hr ?]).
    intros [E|[E|[E|[E|[E|[E|[E|[]]]]]]]]; subst r;
      match goal with H : bv_eqb ?x ?x = false |- _ => rewrite bv_eqb_refl in H; discriminate H | _ => idtac end.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition SB : Z := 0x7fff8000.           (* [comment removed for export] *)
Definition kLowEnd : Z := 0x7fff7fff.      (* [comment removed for export] *)
Definition kHighBeg : Z := 0x10007fff8000. (* [comment removed for export] *)
Definition kHighEnd : Z := 0x7fffffffffff. (* [comment removed for export] *)

#[using="Type"] Lemma SB_val : SB = 0x7fff8000%Z. Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.

#[using="Type"] Lemma v_srli_3 : forall z, (0 <= z < 2 ^ 64)%Z -> v_srli (Z_to_bv 64 z) 3 = Z_to_bv 64 (z / 8).
Proof. LiaFast.lf_pins LiaFast.u0. intros z Hz. unfold v_srli. rewrite zbv_u by exact Hz. rewrite Z.shiftr_div_pow2 by lia. reflexivity. Qed.

#[using="Type"] Lemma v_andi_7 : forall z, (0 <= z < 2 ^ 64)%Z -> v_andi (Z_to_bv 64 z) 7 = Z_to_bv 64 (z mod 8).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros z Hz. unfold v_andi. rewrite zbv_u by exact Hz. change (bv_wrap 64 7) with (Z.ones 3).
  rewrite Z.land_ones by lia. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma k_low_val :
  v_and (v_addi (v_sltu (Z_to_bv 64 SB) (Z_to_bv 64 (SB + -1))) (-1)) (Z_to_bv 64 (SB + -1)) = Z_to_bv 64 kLowEnd.
Proof. LiaFast.lf_pins LiaFast.u0. apply bv_eq. vm_compute. reflexivity. Qed.

#[using="Type"] Lemma k_m1_val : v_addi (Z_to_bv 64 0) (-1) = Z_to_bv 64 (2 ^ 64 - 1).
Proof. LiaFast.lf_pins LiaFast.u0. apply bv_eq. vm_compute. reflexivity. Qed.

#[using="Type"] Lemma k_hse_val : v_add (v_srli (Z_to_bv 64 kHighEnd) 3) (Z_to_bv 64 SB) = Z_to_bv 64 (kHighBeg - 1).
Proof. LiaFast.lf_pins LiaFast.u0. apply bv_eq. vm_compute. reflexivity. Qed.

#[using="Type"] Lemma lit_d9ec4 : v_addi (0x63ab8 : word) 4 = (0x63abc : word).
Proof. LiaFast.lf_pins LiaFast.u0. apply bv_eq. vm_compute. reflexivity. Qed.
#[using="Type"] Lemma lit_d9ed0 : v_addi (0x63ac4 : word) 4 = (0x63ac8 : word).
Proof. LiaFast.lf_pins LiaFast.u0. apply bv_eq. vm_compute. reflexivity. Qed.
#[using="Type"] Lemma lit_d9f50 : v_addi (0x63b44 : word) 4 = (0x63b48 : word).
Proof. LiaFast.lf_pins LiaFast.u0. apply bv_eq. vm_compute. reflexivity. Qed.
#[using="Type"] Lemma ret_ok_d9ec4 : ret_ok (0x63abc : word). Proof. LiaFast.lf_pins LiaFast.u0. apply ret_ok_even. vm_compute. reflexivity. Qed.
#[using="Type"] Lemma ret_ok_d9ed0 : ret_ok (0x63ac8 : word). Proof. LiaFast.lf_pins LiaFast.u0. apply ret_ok_even. vm_compute. reflexivity. Qed.
#[using="Type"] Lemma ret_ok_d9f50 : ret_ok (0x63b48 : word). Proof. LiaFast.lf_pins LiaFast.u0. apply ret_ok_even. vm_compute. reflexivity. Qed.
#[using="Type"] Lemma ret_ok_zbv : forall z, (0 <= z < 2 ^ 64)%Z -> (z mod 2 = 0)%Z -> ret_ok (Z_to_bv 64 z).
Proof. LiaFast.lf_pins LiaFast.u0. intros z Hz He. apply ret_ok_even. rewrite zbv_u by exact Hz. exact He. Qed.

#[using="Type"] Lemma bv_signed_small8 : forall (b : byte), (bv_unsigned b < 128)%Z -> bv_signed b = bv_unsigned b.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros b Hb. pose proof (bv_unsigned_in_range 8 b) as Hr.
  unfold bv_signed. apply bv_swrap_small. change (bv_half_modulus 8) with 128%Z. lia.
Qed.

#[using="Type"] Lemma c_lts_zbv : forall a b, (0 <= a < 2 ^ 63)%Z -> (0 <= b < 2 ^ 63)%Z ->
  c_lts (Z_to_bv 64 a) (Z_to_bv 64 b) = (a <? b)%Z.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros a b Ha Hb. unfold c_lts, bv_lts. rewrite !Z_to_bv_signed.
  rewrite !bv_swrap_small by (change (bv_half_modulus 64) with (2 ^ 63)%Z; lia). reflexivity.
Qed.

#[using="Type"] Lemma bv_eq_dec : forall n (a b : bv n), {a = b} + {a <> b}.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros n0 a b. destruct (Z.eq_dec (bv_unsigned a) (bv_unsigned b)) as [E|NE].
  - left. apply bv_eq. exact E.
  - right. intros ->. apply NE. reflexivity.
Qed.

(* [comment removed for export] *)
Definition cell (m : word -> option byte) (a v : Z) : Prop :=
  rdn SEGS m (Z_to_bv 64 a) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 v)).

Definition cells (m : word -> option byte) : Prop :=
  cell m 0xde490 0xe6678 /\ cell m 0xe6678 SB
  /\ cell m 0xde498 0xe7368 /\ cell m 0xe7368 0
  /\ cell m 0xde4a0 0xe7370 /\ cell m 0xe7370 0
  /\ cell m 0xde4a8 0xe7360 /\ cell m 0xe7360 kHighEnd.

Definition in_mem (p : Z) : Prop := (p <= kLowEnd)%Z \/ (kHighBeg <= p <= kHighEnd)%Z.

End WithFP1.
Ltac mstep L := eapply mst_step; [reflexivity | L | ]; step_simpl; imm_norm.
Ltac gr := repeat (first [ rewrite getr_same by (intros E; discriminate E)
                          | rewrite getr_other by (intros E; discriminate E) ]);
           rewrite ?Z.add_0_r, ?Z.add_0_l.
Ltac zn := rewrite ?v_addi_zbv by lia.
Ltac br_lt := gr; rewrite c_ltu_zbv by lia; first [apply Z.ltb_lt | apply Z.ltb_ge]; lia.
Ltac br_eq := gr; rewrite c_eq_zbv by lia; first [apply Z.eqb_eq | apply Z.eqb_neq]; lia.
Ltac ne := intros E; discriminate E.
(* [comment removed for export] *)
Ltac mld F D v Hcell Hbase :=
  mstep ltac:(eapply (@step_ld _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 v) F eq_refl D);
               [ gr; rewrite ?Hbase; imm_norm; zn;
                 match goal with |- rdn _ _ (Z_to_bv 64 ?a) 8 = _ =>
                   first [ exact Hcell
                         | replace a with (ltac:(match type of Hcell with cell _ ?c _ => exact c end)) by lia; exact Hcell ] end
               | apply bytes_le_to_Z_8 ]).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section WithFP2.
Context {fx : FPState}.
Definition m2s_clob (r : reg) : bool :=
  (bv_eqb r 5 || bv_eqb r 10 || bv_eqb r 11 || bv_eqb r 12 || bv_eqb r 13 || bv_eqb r 14
   || bv_eqb r 15 || bv_eqb r 16 || bv_eqb r 17)%bool.

#[using="Type"] Lemma mem_to_shadow : forall rom regs m (p : Z) (ra : word),
  cells m -> (0 <= p)%Z -> in_mem p ->
  getr regs 10 = Z_to_bv 64 p -> getr regs 1 = ra -> ret_ok ra ->
  exists regs',
    msteps SEGS (mkst regs (0x63548 : word) m rom) (mkst regs' ra m rom)
    /\ getr regs' 10 = Z_to_bv 64 (SB + p / 8)
    /\ (forall r, m2s_clob r = false -> getr regs' r = getr regs r).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros rom regs m p ra (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8) Hp Hin H10 H1 Hret.
  unfold in_mem, kLowEnd, kHighBeg, kHighEnd in Hin.
  assert (Hp64 : (p < 2 ^ 64)%Z) by lia. pose proof SB_val as HSB.
  pose proof (Z.div_mod p 8 ltac:(lia)) as Hdm. pose proof (Z.mod_pos_bound p 8 ltac:(lia)) as Hmb.
  destruct (Z.le_gt_cases p 0x7fff7fff) as [Hlow | Hhigh].
  - eexists. split; [|split].
    + mstep ltac:(eapply (step_auipc_at _ _ _ _ _ _ _ _ (Z_to_bv 64 0xde548) F_63548 eq_refl D_63548);
                   [reflexivity | apply bv_eq; vm_compute; reflexivity]).
      mld F_6354c D_6354c 0xe6678%Z C1 H10.
      mld F_63550 D_63550 SB C2 H10.
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_63554 eq_refl D_63554)). gr. zn.
      mstep ltac:(exact (step_sltu _ _ _ _ _ _ _ _ _ F_63558 eq_refl D_63558)). gr.
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_6355c eq_refl D_6355c)). gr.
      mstep ltac:(exact (step_and _ _ _ _ _ _ _ _ _ F_63560 eq_refl D_63560)). gr.
      rewrite k_low_val. unfold kLowEnd.
      mstep ltac:(eapply (step_bgeu_tk _ _ _ _ _ _ _ _ _ F_63564 eq_refl D_63564); gr; rewrite ?H10; br_lt).
      mstep ltac:(exact (PropExec.step_srli _ _ _ _ _ _ _ _ _ F_635a8 eq_refl D_635a8)). gr. rewrite H10, (v_srli_3 p) by lia.
      mstep ltac:(exact (step_add _ _ _ _ _ _ _ _ _ F_635ac eq_refl D_635ac)). gr. rewrite v_add_zbv by lia.
      eapply mst_step; [reflexivity | eapply (step_jalr_x0 _ _ _ _ _ _ _ _ ra F_635b0 eq_refl D_635b0); gr; exact H1 |].
      imm_norm. rewrite Hret. apply mst_refl.
    + gr. apply (f_equal (Z_to_bv 64)). lia.
    + intros r Hr. unfold m2s_clob in Hr.
      repeat (rewrite getr_other by (intros ->; cbn in Hr; discriminate)). reflexivity.
  - eexists. split; [|split].
    + mstep ltac:(eapply (step_auipc_at _ _ _ _ _ _ _ _ (Z_to_bv 64 0xde548) F_63548 eq_refl D_63548);
                   [reflexivity | apply bv_eq; vm_compute; reflexivity]).
      mld F_6354c D_6354c 0xe6678%Z C1 H10.
      mld F_63550 D_63550 SB C2 H10.
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_63554 eq_refl D_63554)). gr. zn.
      mstep ltac:(exact (step_sltu _ _ _ _ _ _ _ _ _ F_63558 eq_refl D_63558)). gr.
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_6355c eq_refl D_6355c)). gr.
      mstep ltac:(exact (step_and _ _ _ _ _ _ _ _ _ F_63560 eq_refl D_63560)). gr.
      rewrite k_low_val. unfold kLowEnd.
      mstep ltac:(eapply (step_bgeu_ft _ _ _ _ _ _ _ _ _ F_63564 eq_refl D_63564); gr; rewrite ?H10; br_lt).
      mstep ltac:(eapply (step_auipc_at _ _ _ _ _ _ _ _ (Z_to_bv 64 0xde568) F_63568 eq_refl D_63568);
                   [reflexivity | apply bv_eq; vm_compute; reflexivity]).
      mld F_6356c D_6356c 0xe7368%Z C3 H10.
      mstep ltac:(eapply (step_auipc_at _ _ _ _ _ _ _ _ (Z_to_bv 64 0xde570) F_63570 eq_refl D_63570);
                   [reflexivity | apply bv_eq; vm_compute; reflexivity]).
      mld F_63574 D_63574 0xe7370%Z C5 H10.
      mld F_63578 D_63578 0%Z C4 H10.
      mld F_6357c D_6357c 0%Z C6 H10.
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_63580 eq_refl D_63580)). gr. rewrite k_m1_val.
      mstep ltac:(eapply (step_bgeu_tk _ _ _ _ _ _ _ _ _ F_63584 eq_refl D_63584); gr; rewrite ?H10; br_lt).
      mstep ltac:(eapply (step_auipc_at _ _ _ _ _ _ _ _ (Z_to_bv 64 0xde58c) F_6358c eq_refl D_6358c);
                   [reflexivity | apply bv_eq; vm_compute; reflexivity]).
      mld F_63590 D_63590 0xe7360%Z C7 H10.
      mld F_63594 D_63594 kHighEnd C8 H10.
      mstep ltac:(exact (PropExec.step_srli _ _ _ _ _ _ _ _ _ F_63598 eq_refl D_63598)). gr.
      mstep ltac:(exact (step_add _ _ _ _ _ _ _ _ _ F_6359c eq_refl D_6359c)). gr. rewrite k_hse_val. unfold kHighBeg.
      replace (17594333495296 - 1)%Z with 17594333495295%Z by reflexivity.
      mstep ltac:(eapply (step_bltu_ft _ _ _ _ _ _ _ _ _ F_635a0 eq_refl D_635a0); gr; rewrite ?H10; unfold kHighEnd; br_lt).
      mstep ltac:(eapply (step_bgeu_ft _ _ _ _ _ _ _ _ _ F_635a4 eq_refl D_635a4); gr; rewrite ?H10; br_lt).
      mstep ltac:(exact (PropExec.step_srli _ _ _ _ _ _ _ _ _ F_635a8 eq_refl D_635a8)). gr. rewrite H10, (v_srli_3 p) by lia.
      mstep ltac:(exact (step_add _ _ _ _ _ _ _ _ _ F_635ac eq_refl D_635ac)). gr. rewrite v_add_zbv by lia.
      eapply mst_step; [reflexivity | eapply (step_jalr_x0 _ _ _ _ _ _ _ _ ra F_635b0 eq_refl D_635b0); gr; exact H1 |].
      imm_norm. rewrite Hret. apply mst_refl.
    + gr. apply (f_equal (Z_to_bv 64)). lia.
    + intros r Hr. unfold m2s_clob in Hr.
      repeat (rewrite getr_other by (intros ->; cbn in Hr; discriminate)). reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Record rpH (mem : word -> option byte) (beg n usp : Z) (b1 : byte) : Prop := {
  rp_n    : (1 <= n <= 2 ^ 40)%Z;
  rp_beg  : (0 <= beg)%Z;
  rp_rng  : (beg + n + 8 <= kLowEnd)%Z \/ (kHighBeg <= beg /\ beg + n + 8 <= kHighEnd)%Z;
  rp_sp   : (80 <= usp < 2 ^ 64)%Z;
  (* [comment removed for export] *)
  rp_disj : (SB + (beg + n - 1) / 8 < usp - 72)%Z;
  (* [comment removed for export] *)
  rp_zero : forall g, (beg / 8 <= g < (beg + n - 1) / 8)%Z -> mem (Z_to_bv 64 (SB + g)) = Some (Z_to_bv 8 0);
  (* [comment removed for export] *)
  rp_last : mem (Z_to_bv 64 (SB + (beg + n - 1) / 8)) = Some b1;
  rp_b1   : bv_unsigned b1 = 0%Z \/ ((beg + n - 1) mod 8 < bv_unsigned b1 <= 7)%Z;   (* [comment removed for export] *)
  (* [comment removed for export] *)
  rp_stk  : forall a, (usp - 72 <= a < usp)%Z -> store_ok SEGS mem (Z_to_bv 64 a) 1 = true;
  rp_cells : cells mem
}.

Definition rp_clob (r : reg) : bool :=
  (bv_eqb r 5 || bv_eqb r 10 || bv_eqb r 11 || bv_eqb r 12 || bv_eqb r 13 || bv_eqb r 14
   || bv_eqb r 15 || bv_eqb r 16 || bv_eqb r 17)%bool.

(* [comment removed for export] *)
Definition rp_tmp (r : reg) : bool :=
  (rp_clob r || bv_eqb r 1 || bv_eqb r 2 || bv_eqb r 8 || bv_eqb r 9 || bv_eqb r 18 || bv_eqb r 19
   || bv_eqb r 20 || bv_eqb r 21)%bool.

(* [comment removed for export] *)
Definition rp_frame (mem : word -> option byte) (usp : Z) (ra s0 s1 s2 s3 s4 s5 : word) : word -> option byte :=
  let w (o : Z) (v : word) (m : word -> option byte) := wbytes m (Z_to_bv 64 (usp - o)) (word_to_le_bytes 8 v) in
  w 72%Z (Z_to_bv 64 0x63b48) (w 56%Z s5 (w 48%Z s4 (w 40%Z s3 (w 32%Z s2 (w 24%Z s1 (w 16%Z s0 (w 8%Z ra mem))))))).
(* [comment removed for export] *)
Definition rp_frame7 (mem : word -> option byte) (usp : Z) (ra s0 s1 s2 s3 s4 s5 : word) : word -> option byte :=
  let w (o : Z) (v : word) (m : word -> option byte) := wbytes m (Z_to_bv 64 (usp - o)) (word_to_le_bytes 8 v) in
  w 56%Z s5 (w 48%Z s4 (w 40%Z s3 (w 32%Z s2 (w 24%Z s1 (w 16%Z s0 (w 8%Z ra mem)))))).

End WithFP2.
Section RP.
Context {fx : FPState}.
  Variables (mem rom : word -> option byte) (beg n usp : Z) (b1 : byte).
  Hypothesis H : rpH mem beg n usp b1.
  Variable regs0 : bvmap 5 word.   (* [comment removed for export] *)
  Variable ra : word.
  Hypothesis Hret : ret_ok ra.
  Hypothesis H01 : getr regs0 1 = ra.
  Hypothesis H02 : getr regs0 2 = Z_to_bv 64 usp.
  Hypothesis H010 : getr regs0 10 = Z_to_bv 64 beg.
  Hypothesis H011 : getr regs0 11 = Z_to_bv 64 n.

  Let en : Z := (beg + n)%Z.
  Let g0 : Z := (beg / 8)%Z.
  Let g1 : Z := ((en - 1) / 8)%Z.
  Let gu : Z := ((beg + 7) / 8)%Z.
  Let ge : Z := (en / 8)%Z.

  Let Hn := rp_n _ _ _ _ _ H.
  Let Hbeg := rp_beg _ _ _ _ _ H.
  Let Hsp := rp_sp _ _ _ _ _ H.

  #[using="mem usp b1 H g0 g1 gu ge Hbeg"] Lemma rng : (en + 8 <= kHighEnd)%Z /\ ((en + 8 <= kLowEnd)%Z \/ (kHighBeg <= beg)%Z).
  Proof. LiaFast.lf_pins (fun (mem usp b1 H g0 g1 gu ge Hbeg : LiaFast.U) => LiaFast.u0). pose proof (rp_rng _ _ _ _ _ H) as R. unfold en, kLowEnd, kHighBeg, kHighEnd in *. lia. Qed.

  #[using="mem usp b1 H Hn Hbeg"] Lemma divfacts :
    (8 * g0 <= beg < 8 * g0 + 8)%Z /\ (8 * g1 <= en - 1 < 8 * g1 + 8)%Z
    /\ (8 * gu <= beg + 7 < 8 * gu + 8)%Z /\ (8 * ge <= en < 8 * ge + 8)%Z
    /\ ((en - 1) mod 8 = en - 1 - 8 * g1)%Z.
  Proof. LiaFast.lf_pins (fun (mem usp b1 H Hn Hbeg : LiaFast.U) => LiaFast.u0).
    unfold g0, g1, gu, ge, en.
    pose proof (Z.div_mod beg 8 ltac:(lia)). pose proof (Z.mod_pos_bound beg 8 ltac:(lia)).
    pose proof (Z.div_mod (beg + n - 1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (beg + n - 1) 8 ltac:(lia)).
    pose proof (Z.div_mod (beg + 7) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (beg + 7) 8 ltac:(lia)).
    pose proof (Z.div_mod (beg + n) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (beg + n) 8 ltac:(lia)).
    lia.
  Qed.

  Definition m7 : word -> option byte :=
    let w (o : Z) (v : word) (m : word -> option byte) := wbytes m (Z_to_bv 64 (usp - o)) (word_to_le_bytes 8 v) in
    w 56%Z (getr regs0 21) (w 48%Z (getr regs0 20) (w 40%Z (getr regs0 19) (w 32%Z (getr regs0 18)
      (w 24%Z (getr regs0 9) (w 16%Z (getr regs0 8) (w 8%Z ra mem)))))).
  Definition m8 : word -> option byte :=
    wbytes m7 (Z_to_bv 64 (usp - 72)) (word_to_le_bytes 8 (Z_to_bv 64 0x63b48)).

  #[using="Type"] Lemma m8_frame : m8 = rp_frame mem usp ra (getr regs0 8) (getr regs0 9) (getr regs0 18)
                                 (getr regs0 19) (getr regs0 20) (getr regs0 21).
  Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.
  #[using="Type"] Lemma m7_frame : m7 = rp_frame7 mem usp ra (getr regs0 8) (getr regs0 9) (getr regs0 18)
                                 (getr regs0 19) (getr regs0 20) (getr regs0 21).
  Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.

  Ltac len8 := rewrite ?length_N_to_le_bytes; change (Z.of_nat 8) with 8%Z.

  #[using="beg n b1 H en g0 g1 gu ge Hbeg Hsp"] Lemma m7_below : forall x : word, (bv_unsigned x < usp - 72)%Z -> m7 x = mem x.
  Proof. LiaFast.lf_pins (fun (beg n b1 H en g0 g1 gu ge Hbeg Hsp : LiaFast.U) => LiaFast.u0).
    intros x Hx. unfold m7. rewrite !wbytes_below; try reflexivity; len8; rewrite ?zbv_u by lia; lia.
  Qed.
  #[using="beg n b1 H en g0 g1 gu ge Hbeg Hsp"] Lemma m8_below : forall x : word, (bv_unsigned x < usp - 72)%Z -> m8 x = mem x.
  Proof. LiaFast.lf_pins (fun (beg n b1 H en g0 g1 gu ge Hbeg Hsp : LiaFast.U) => LiaFast.u0).
    intros x Hx. unfold m8. rewrite wbytes_below; [apply m7_below; exact Hx| |]; len8; rewrite ?zbv_u by lia; lia.
  Qed.

  #[using="beg n b1 H en g0 g1 gu ge Hn Hbeg Hsp"] Lemma rdn_m7_below : forall (a : Z) k, (0 <= a)%Z -> (a + Z.of_nat k <= usp - 72)%Z ->
    rdn SEGS m7 (Z_to_bv 64 a) k = rdn SEGS mem (Z_to_bv 64 a) k.
  Proof. LiaFast.lf_pins (fun (beg n b1 H en g0 g1 gu ge Hn Hbeg Hsp : LiaFast.U) => LiaFast.u0).
    intros a k Ha Hk. apply rdn_ext; [rewrite zbv_u by lia; lia|].
    intros x Hx. rewrite zbv_u in Hx by lia. apply m7_below. lia.
  Qed.
  #[using="beg n b1 H en g0 g1 gu ge Hn Hbeg Hsp"] Lemma rdn_m8_below : forall (a : Z) k, (0 <= a)%Z -> (a + Z.of_nat k <= usp - 72)%Z ->
    rdn SEGS m8 (Z_to_bv 64 a) k = rdn SEGS mem (Z_to_bv 64 a) k.
  Proof. LiaFast.lf_pins (fun (beg n b1 H en g0 g1 gu ge Hn Hbeg Hsp : LiaFast.U) => LiaFast.u0).
    intros a k Ha Hk. apply rdn_ext; [rewrite zbv_u by lia; lia|].
    intros x Hx. rewrite zbv_u in Hx by lia. apply m8_below. lia.
  Qed.

  #[using="mem beg n b1 H en g0 g1 gu ge Hn Hbeg"] Lemma SB_lt : (0x1877c0 <= usp - 72)%Z.
  Proof. LiaFast.lf_pins (fun (mem beg n b1 H en g0 g1 gu ge Hn Hbeg : LiaFast.U) => LiaFast.u0). pose proof (rp_disj _ _ _ _ _ H). pose proof divfacts. pose proof SB_val. lia. Qed.

  #[using="beg n b1 H en g0 g1 gu ge Hn Hbeg Hsp"] Lemma cells_m7 : cells m7.
  Proof. LiaFast.lf_pins (fun (beg n b1 H en g0 g1 gu ge Hn Hbeg Hsp : LiaFast.U) => LiaFast.u0).
    pose proof (rp_cells _ _ _ _ _ H) as C. pose proof SB_lt. unfold cells, cell in *.
    rewrite !rdn_m7_below by (cbn; lia). exact C.
  Qed.
  #[using="beg n b1 H en g0 g1 gu ge Hn Hbeg Hsp"] Lemma cells_m8 : cells m8.
  Proof. LiaFast.lf_pins (fun (beg n b1 H en g0 g1 gu ge Hn Hbeg Hsp : LiaFast.U) => LiaFast.u0).
    pose proof (rp_cells _ _ _ _ _ H) as C. pose proof SB_lt. unfold cells, cell in *.
    rewrite !rdn_m8_below by (cbn; lia). exact C.
  Qed.

  #[using="beg n b1 H en g0 g1 gu ge Hn Hbeg Hsp"] Lemma stk8 : forall m a, (usp - 72 <= a)%Z -> (a + 8 <= usp)%Z ->
    (forall x, store_ok SEGS mem x 1 = true -> store_ok SEGS m x 1 = true) ->
    store_ok SEGS m (Z_to_bv 64 a) 8 = true.
  Proof. LiaFast.lf_pins (fun (beg n b1 H en g0 g1 gu ge Hn Hbeg Hsp : LiaFast.U) => LiaFast.u0).
    intros m a H1 H2 Hm. apply store_ok8_bytes; [lia|lia|].
    intros j Hj. apply Hm. apply (rp_stk _ _ _ _ _ H). lia.
  Qed.

  (* [comment removed for export] *)
  Ltac rd_side := len8; rewrite !zbv_u by lia; lia.
  Ltac rd_slot := unfold m8, m7;
    repeat (first [ apply rdn_wbytes_hit8; rewrite zbv_u by lia; lia
                  | rewrite rdn_wbytes_out; [| rd_side | rd_side | rd_side] ]).

  #[using="beg n b1 H en g0 g1 gu ge Hbeg Hsp"] Lemma rd_ra : rdn SEGS m8 (Z_to_bv 64 (usp - 8)) 8 = Some (word_to_le_bytes 8 ra).            Proof. LiaFast.lf_pins (fun (beg n b1 H en g0 g1 gu ge Hbeg Hsp : LiaFast.U) => LiaFast.u0). rd_slot. Qed.
  #[using="beg n b1 H en g0 g1 gu ge Hbeg Hsp"] Lemma rd_s0 : rdn SEGS m8 (Z_to_bv 64 (usp - 16)) 8 = Some (word_to_le_bytes 8 (getr regs0 8)). Proof. LiaFast.lf_pins (fun (beg n b1 H en g0 g1 gu ge Hbeg Hsp : LiaFast.U) => LiaFast.u0). rd_slot. Qed.
  #[using="beg n b1 H en g0 g1 gu ge Hbeg Hsp"] Lemma rd_s1 : rdn SEGS m8 (Z_to_bv 64 (usp - 24)) 8 = Some (word_to_le_bytes 8 (getr regs0 9)). Proof. LiaFast.lf_pins (fun (beg n b1 H en g0 g1 gu ge Hbeg Hsp : LiaFast.U) => LiaFast.u0). rd_slot. Qed.
  #[using="beg n b1 H en g0 g1 gu ge Hbeg Hsp"] Lemma rd_s2 : rdn SEGS m8 (Z_to_bv 64 (usp - 32)) 8 = Some (word_to_le_bytes 8 (getr regs0 18)). Proof. LiaFast.lf_pins (fun (beg n b1 H en g0 g1 gu ge Hbeg Hsp : LiaFast.U) => LiaFast.u0). rd_slot. Qed.
  #[using="beg n b1 H en g0 g1 gu ge Hbeg Hsp"] Lemma rd_s3 : rdn SEGS m8 (Z_to_bv 64 (usp - 40)) 8 = Some (word_to_le_bytes 8 (getr regs0 19)). Proof. LiaFast.lf_pins (fun (beg n b1 H en g0 g1 gu ge Hbeg Hsp : LiaFast.U) => LiaFast.u0). rd_slot. Qed.
  #[using="beg n b1 H en g0 g1 gu ge Hbeg Hsp"] Lemma rd_s4 : rdn SEGS m8 (Z_to_bv 64 (usp - 48)) 8 = Some (word_to_le_bytes 8 (getr regs0 20)). Proof. LiaFast.lf_pins (fun (beg n b1 H en g0 g1 gu ge Hbeg Hsp : LiaFast.U) => LiaFast.u0). rd_slot. Qed.
  #[using="beg n b1 H en g0 g1 gu ge Hbeg Hsp"] Lemma rd_s5 : rdn SEGS m8 (Z_to_bv 64 (usp - 56)) 8 = Some (word_to_le_bytes 8 (getr regs0 21)). Proof. LiaFast.lf_pins (fun (beg n b1 H en g0 g1 gu ge Hbeg Hsp : LiaFast.U) => LiaFast.u0). rd_slot. Qed.

  Definition keep (regs : bvmap 5 word) : Prop :=
    forall r, rp_tmp r = false -> getr regs r = getr regs0 r.

  Ltac solve_keep Hk :=
    intros r Hr; unfold rp_tmp, rp_clob in Hr;
    repeat (rewrite getr_other by (intros ->; cbn in Hr; discriminate));
    apply Hk; unfold rp_tmp, rp_clob; exact Hr.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac msd F D o v Hbase Hm :=
    mstep ltac:(eapply (step_sd_at _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (usp - o)) v F eq_refl D);
                 [ gr; rewrite ?Hbase; imm_norm; zn; apply (f_equal (Z_to_bv 64)); lia
                 | gr; first [reflexivity | assumption | symmetry; assumption]
                 | apply stk8; [lia | lia | intros x Hx; repeat apply store_ok1_wbytes; exact Hx] ]).

  #[using="b1 H H01 H02 H010 H011 en g0 g1 gu ge Hn Hbeg Hsp"] Lemma blk_P :
    exists regs,
      msteps SEGS (mkst regs0 (0x639d4 : word) mem rom) (mkst regs (0x63a00 : word) m7 rom)
      /\ getr regs 2 = Z_to_bv 64 (usp - 64) /\ getr regs 8 = Z_to_bv 64 beg /\ getr regs 9 = Z_to_bv 64 n
      /\ getr regs 1 = ra /\ keep regs.
  Proof. LiaFast.lf_pins (fun (b1 H H01 H02 H010 H011 en g0 g1 gu ge Hn Hbeg Hsp : LiaFast.U) => LiaFast.u0).
    pose proof rng as HR. unfold kLowEnd, kHighBeg, kHighEnd in HR.
    eexists. split.
    - mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_639d4 eq_refl D_639d4)). rewrite H02. zn.
      msd F_639d8 D_639d8 8%Z ra H02 mem.
      msd F_639dc D_639dc 16%Z (getr regs0 8) H02 mem.
      msd F_639e0 D_639e0 24%Z (getr regs0 9) H02 mem.
      msd F_639e4 D_639e4 32%Z (getr regs0 18) H02 mem.
      msd F_639e8 D_639e8 40%Z (getr regs0 19) H02 mem.
      msd F_639ec D_639ec 48%Z (getr regs0 20) H02 mem.
      msd F_639f0 D_639f0 56%Z (getr regs0 21) H02 mem.
      mstep ltac:(eapply (step_beq_ft _ _ _ _ _ _ _ _ _ F_639f4 eq_refl D_639f4); gr; rewrite ?H011, ?getr_zero; br_eq).
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_639f8 eq_refl D_639f8)). gr. rewrite H011. zn.
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_639fc eq_refl D_639fc)). gr. rewrite H010. zn.
      apply mst_refl.
    - gr. repeat split; try (apply (f_equal (Z_to_bv 64)); lia); try assumption.
      intros r Hr. unfold rp_tmp, rp_clob in Hr.
      repeat (rewrite getr_other by (intros ->; cbn in Hr; discriminate)). reflexivity.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="n b1 H en g0 g1 gu ge Hn Hbeg Hsp"] Lemma blk_A : forall regs,
    getr regs 8 = Z_to_bv 64 beg ->
    exists regs',
      msteps SEGS (mkst regs (0x63a00 : word) m7 rom) (mkst regs' (0x63a60 : word) m7 rom)
      /\ getr regs' 21 = Z_to_bv 64 0xe6678 /\ getr regs' 11 = Z_to_bv 64 SB /\ getr regs' 12 = Z_to_bv 64 kLowEnd
      /\ (forall r, m2s_clob r = false -> r <> 21 -> getr regs' r = getr regs r).
  Proof. LiaFast.lf_pins (fun (n b1 H en g0 g1 gu ge Hn Hbeg Hsp : LiaFast.U) => LiaFast.u0).
    intros regs H8.
    pose proof rng as HR. unfold kLowEnd, kHighBeg, kHighEnd in HR. pose proof SB_val as HSB.
    pose proof cells_m7 as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8).
    destruct (Z.le_gt_cases beg 0x7fff7fff) as [Hlow | Hhigh].
    - eexists. split.
      + mstep ltac:(eapply (step_auipc_at _ _ _ _ _ _ _ _ (Z_to_bv 64 0xdea00) F_63a00 eq_refl D_63a00);
                     [reflexivity | apply bv_eq; vm_compute; reflexivity]).
        mld F_63a04 D_63a04 0xe6678%Z C1 H8.
        mld F_63a08 D_63a08 SB C2 H8.
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_63a0c eq_refl D_63a0c)). gr. zn.
        mstep ltac:(exact (step_sltu _ _ _ _ _ _ _ _ _ F_63a10 eq_refl D_63a10)). gr.
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_63a14 eq_refl D_63a14)). gr.
        mstep ltac:(exact (step_and _ _ _ _ _ _ _ _ _ F_63a18 eq_refl D_63a18)). gr. rewrite k_low_val. unfold kLowEnd.
        mstep ltac:(eapply (step_bgeu_tk _ _ _ _ _ _ _ _ _ F_63a1c eq_refl D_63a1c); gr; rewrite ?H8; br_lt).
        apply mst_refl.
      + gr. repeat split; try reflexivity.
        intros r Hr Hr21. unfold m2s_clob in Hr.
        repeat (rewrite getr_other by (intros ->; cbn in Hr; first [discriminate | congruence])). reflexivity.
    - eexists. split.
      + mstep ltac:(eapply (step_auipc_at _ _ _ _ _ _ _ _ (Z_to_bv 64 0xdea00) F_63a00 eq_refl D_63a00);
                     [reflexivity | apply bv_eq; vm_compute; reflexivity]).
        mld F_63a04 D_63a04 0xe6678%Z C1 H8.
        mld F_63a08 D_63a08 SB C2 H8.
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_63a0c eq_refl D_63a0c)). gr. zn.
        mstep ltac:(exact (step_sltu _ _ _ _ _ _ _ _ _ F_63a10 eq_refl D_63a10)). gr.
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_63a14 eq_refl D_63a14)). gr.
        mstep ltac:(exact (step_and _ _ _ _ _ _ _ _ _ F_63a18 eq_refl D_63a18)). gr. rewrite k_low_val. unfold kLowEnd.
        mstep ltac:(eapply (step_bgeu_ft _ _ _ _ _ _ _ _ _ F_63a1c eq_refl D_63a1c); gr; rewrite ?H8; br_lt).
        mstep ltac:(eapply (step_auipc_at _ _ _ _ _ _ _ _ (Z_to_bv 64 0xdea20) F_63a20 eq_refl D_63a20);
                     [reflexivity | apply bv_eq; vm_compute; reflexivity]).
        mld F_63a24 D_63a24 0xe7368%Z C3 H8.
        mstep ltac:(eapply (step_auipc_at _ _ _ _ _ _ _ _ (Z_to_bv 64 0xdea28) F_63a28 eq_refl D_63a28);
                     [reflexivity | apply bv_eq; vm_compute; reflexivity]).
        mld F_63a2c D_63a2c 0xe7370%Z C5 H8.
        mld F_63a30 D_63a30 0%Z C4 H8.
        mld F_63a34 D_63a34 0%Z C6 H8.
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_63a38 eq_refl D_63a38)). gr. rewrite k_m1_val.
        mstep ltac:(eapply (step_bgeu_tk _ _ _ _ _ _ _ _ _ F_63a3c eq_refl D_63a3c); gr; rewrite ?H8; br_lt).
        mstep ltac:(eapply (step_auipc_at _ _ _ _ _ _ _ _ (Z_to_bv 64 0xdea44) F_63a44 eq_refl D_63a44);
                     [reflexivity | apply bv_eq; vm_compute; reflexivity]).
        mld F_63a48 D_63a48 0xe7360%Z C7 H8.
        mld F_63a4c D_63a4c kHighEnd C8 H8.
        mstep ltac:(exact (PropExec.step_srli _ _ _ _ _ _ _ _ _ F_63a50 eq_refl D_63a50)). gr.
        mstep ltac:(exact (step_add _ _ _ _ _ _ _ _ _ F_63a54 eq_refl D_63a54)). gr. rewrite k_hse_val. unfold kHighBeg.
        replace (17594333495296 - 1)%Z with 17594333495295%Z by reflexivity.
        mstep ltac:(eapply (step_bltu_ft _ _ _ _ _ _ _ _ _ F_63a58 eq_refl D_63a58); gr; rewrite ?H8; unfold kHighEnd; br_lt).
        mstep ltac:(eapply (step_bgeu_ft _ _ _ _ _ _ _ _ _ F_63a5c eq_refl D_63a5c); gr; rewrite ?H8; br_lt).
        apply mst_refl.
      + gr. repeat split; try reflexivity.
        intros r Hr Hr21. unfold m2s_clob in Hr.
        repeat (rewrite getr_other by (intros ->; cbn in Hr; first [discriminate | congruence])). reflexivity.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition b_clob (r : reg) : bool :=
    (bv_eqb r 12 || bv_eqb r 13 || bv_eqb r 14 || bv_eqb r 15 || bv_eqb r 16 || bv_eqb r 17 || bv_eqb r 18)%bool.

  #[using="b1 H g0 g1 gu ge Hn Hbeg Hsp"] Lemma blk_B : forall regs,
    getr regs 8 = Z_to_bv 64 beg -> getr regs 9 = Z_to_bv 64 n ->
    getr regs 11 = Z_to_bv 64 SB -> getr regs 12 = Z_to_bv 64 kLowEnd ->
    exists regs',
      msteps SEGS (mkst regs (0x63a60 : word) m7 rom) (mkst regs' (0x63aa8 : word) m7 rom)
      /\ getr regs' 18 = Z_to_bv 64 en
      /\ (forall r, b_clob r = false -> getr regs' r = getr regs r).
  Proof. LiaFast.lf_pins (fun (b1 H g0 g1 gu ge Hn Hbeg Hsp : LiaFast.U) => LiaFast.u0).
    intros regs H8 H9 H11 H12.
    pose proof rng as HR. unfold kLowEnd, kHighBeg, kHighEnd in HR. pose proof SB_val as HSB.
    pose proof cells_m7 as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8).
    destruct HR as [HR1 [Hlow | Hhigh]].
    - eexists. split.
      + mstep ltac:(exact (step_add _ _ _ _ _ _ _ _ _ F_63a60 eq_refl D_63a60)). gr. rewrite H9, H8, v_add_zbv by lia.
        mstep ltac:(eapply (step_bgeu_tk _ _ _ _ _ _ _ _ _ F_63a64 eq_refl D_63a64); gr; rewrite ?H12; unfold kLowEnd; br_lt).
        apply mst_refl.
      + gr. split; [apply (f_equal (Z_to_bv 64)); lia|].
        intros r Hr. unfold b_clob in Hr.
        repeat (rewrite getr_other by (intros ->; cbn in Hr; discriminate)). reflexivity.
    - eexists. split.
      + mstep ltac:(exact (step_add _ _ _ _ _ _ _ _ _ F_63a60 eq_refl D_63a60)). gr. rewrite H9, H8, v_add_zbv by lia.
        mstep ltac:(eapply (step_bgeu_ft _ _ _ _ _ _ _ _ _ F_63a64 eq_refl D_63a64); gr; rewrite ?H12; unfold kLowEnd; br_lt).
        mstep ltac:(eapply (step_auipc_at _ _ _ _ _ _ _ _ (Z_to_bv 64 0xdea68) F_63a68 eq_refl D_63a68);
                     [reflexivity | apply bv_eq; vm_compute; reflexivity]).
        mld F_63a6c D_63a6c 0xe7368%Z C3 H8.
        mstep ltac:(eapply (step_auipc_at _ _ _ _ _ _ _ _ (Z_to_bv 64 0xdea70) F_63a70 eq_refl D_63a70);
                     [reflexivity | apply bv_eq; vm_compute; reflexivity]).
        mld F_63a74 D_63a74 0xe7370%Z C5 H8.
        mld F_63a78 D_63a78 0%Z C4 H8.
        mld F_63a7c D_63a7c 0%Z C6 H8.
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_63a80 eq_refl D_63a80)). gr. rewrite k_m1_val.
        mstep ltac:(eapply (step_bgeu_tk _ _ _ _ _ _ _ _ _ F_63a84 eq_refl D_63a84); gr; br_lt).
        mstep ltac:(eapply (step_auipc_at _ _ _ _ _ _ _ _ (Z_to_bv 64 0xdea8c) F_63a8c eq_refl D_63a8c);
                     [reflexivity | apply bv_eq; vm_compute; reflexivity]).
        mld F_63a90 D_63a90 0xe7360%Z C7 H8.
        mld F_63a94 D_63a94 kHighEnd C8 H8.
        mstep ltac:(exact (PropExec.step_srli _ _ _ _ _ _ _ _ _ F_63a98 eq_refl D_63a98)). gr.
        mstep ltac:(exact (step_add _ _ _ _ _ _ _ _ _ F_63a9c eq_refl D_63a9c)). gr. rewrite H11, k_hse_val. unfold kHighBeg.
        replace (17594333495296 - 1)%Z with 17594333495295%Z by reflexivity.
        mstep ltac:(eapply (step_bltu_ft _ _ _ _ _ _ _ _ _ F_63aa0 eq_refl D_63aa0); gr; unfold kHighEnd; br_lt).
        mstep ltac:(eapply (step_bgeu_ft _ _ _ _ _ _ _ _ _ F_63aa4 eq_refl D_63aa4); gr; br_lt).
        apply mst_refl.
      + gr. split; [apply (f_equal (Z_to_bv 64)); lia|].
        intros r Hr. unfold b_clob in Hr.
        repeat (rewrite getr_other by (intros ->; cbn in Hr; discriminate)). reflexivity.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="b1 H g0 g1 Hn Hbeg Hsp"] Lemma blk_C : forall regs,
    getr regs 8 = Z_to_bv 64 beg -> getr regs 18 = Z_to_bv 64 en ->
    exists regs',
      msteps SEGS (mkst regs (0x63aa8 : word) m7 rom) (mkst regs' (0x63ac8 : word) m7 rom)
      /\ getr regs' 19 = Z_to_bv 64 (SB + gu) /\ getr regs' 10 = Z_to_bv 64 (SB + ge)
      /\ (forall r, m2s_clob r = false -> r <> 1 -> r <> 19 -> r <> 20 -> getr regs' r = getr regs r).
  Proof. LiaFast.lf_pins (fun (b1 H g0 g1 Hn Hbeg Hsp : LiaFast.U) => LiaFast.u0).
    intros regs H8 H18.
    pose proof rng as HR. unfold kLowEnd, kHighBeg, kHighEnd in HR. pose proof SB_val as HSB.
    pose proof divfacts as (D0 & D1 & DU & DE & DM).
    evar (rr1 : bvmap 5 word).
    edestruct (mem_to_shadow rom rr1 m7 (gu * 8)%Z (0x63abc : word) cells_m7) as (r1 & M1 & R1 & K1); cycle -1.
    { evar (rr2 : bvmap 5 word).
      edestruct (mem_to_shadow rom rr2 m7 (ge * 8)%Z (0x63ac8 : word) cells_m7) as (r2 & M2 & R2 & K2); cycle -1.
      { rewrite Z.div_mul in R1 by lia. rewrite Z.div_mul in R2 by lia.
        exists r2. split; [|split; [|split]].
        - mstep ltac:(eapply (step_bgeu_ft _ _ _ _ _ _ _ _ _ F_63aa8 eq_refl D_63aa8); gr; rewrite ?H8, ?H18; br_lt).
          mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_63aac eq_refl D_63aac)). gr. rewrite H8. zn.
          mstep ltac:(exact (step_andi _ _ _ _ _ _ _ _ _ F_63ab0 eq_refl D_63ab0)). gr. rewrite v_andi_m8 by lia.
          mstep ltac:(exact (step_andi _ _ _ _ _ _ _ _ _ F_63ab4 eq_refl D_63ab4)). gr. rewrite H18, v_andi_m8 by lia.
          mstep ltac:(exact (step_jal_link _ _ _ _ _ _ _ _ F_63ab8 eq_refl D_63ab8)). rewrite lit_d9ec4.
          eapply msteps_trans; [subst rr1; exact M1|].
          mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_63abc eq_refl D_63abc)). rewrite R1. zn. rewrite Z.add_0_r.
          mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_63ac0 eq_refl D_63ac0)). gr.
          rewrite (K1 20) by (reflexivity || discriminate). subst rr1. gr. zn. rewrite Z.add_0_r.
          mstep ltac:(exact (step_jal_link _ _ _ _ _ _ _ _ F_63ac4 eq_refl D_63ac4)). rewrite lit_d9ed0.
          subst rr2. exact M2.
        - subst rr1 rr2. rewrite (K2 19) by (reflexivity || discriminate). gr. reflexivity.
        - exact R2.
        - subst rr1 rr2. intros r Hr Hr1 Hr19 Hr20. unfold m2s_clob in Hr. rewrite (K2 r Hr).
          rewrite !getr_other by first [congruence | (intros ->; cbn in Hr; discriminate)].
          rewrite (K1 r Hr).
          rewrite !getr_other by first [congruence | (intros ->; cbn in Hr; discriminate)]. reflexivity. }
      all: subst rr1 rr2; gr; try reflexivity; try lia; try apply ret_ok_d9ed0;
           try (unfold in_mem, kLowEnd, kHighBeg, kHighEnd; lia); try (apply (f_equal (Z_to_bv 64)); lia). }
    all: subst rr1; gr; try reflexivity; try lia; try apply ret_ok_d9ec4;
           try (unfold in_mem, kLowEnd, kHighBeg, kHighEnd; lia); try (apply (f_equal (Z_to_bv 64)); lia).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="mem usp b1 H gu ge Hn Hbeg"] Lemma g0_le_g1 : (g0 <= g1)%Z.
  Proof. LiaFast.lf_pins (fun (mem usp b1 H gu ge Hn Hbeg : LiaFast.U) => LiaFast.u0). pose proof divfacts. lia. Qed.

  (* [comment removed for export] *)
  Definition b0 : byte := if Z.ltb g0 g1 then Z_to_bv 8 0 else b1.
  #[using="H gu ge Hn Hbeg Hsp"] Lemma shadow_beg : m7 (Z_to_bv 64 (SB + g0)) = Some b0.
  Proof. LiaFast.lf_pins (fun (H gu ge Hn Hbeg Hsp : LiaFast.U) => LiaFast.u0).
    pose proof (rp_disj _ _ _ _ _ H). pose proof divfacts. pose proof SB_val. pose proof g0_le_g1.
    pose proof rng as HR. unfold kLowEnd, kHighBeg, kHighEnd in HR.
    rewrite m7_below by (rewrite zbv_u by lia; unfold g1, en in *; lia).
    unfold b0. destruct (Z.ltb_spec g0 g1) as [Hlt|Hge].
    - apply (rp_zero _ _ _ _ _ H). unfold g0, g1, en in *. lia.
    - replace g0 with g1 by lia. unfold g1, en. exact (rp_last _ _ _ _ _ H).
  Qed.

  #[using="H g0 gu ge Hn Hbeg Hsp"] Lemma shadow_last : m7 (Z_to_bv 64 (SB + g1)) = Some b1.
  Proof. LiaFast.lf_pins (fun (H g0 gu ge Hn Hbeg Hsp : LiaFast.U) => LiaFast.u0).
    pose proof (rp_disj _ _ _ _ _ H). pose proof divfacts. pose proof SB_val.
    pose proof rng as HR. unfold kLowEnd, kHighBeg, kHighEnd in HR.
    rewrite m7_below by (rewrite zbv_u by lia; unfold g1, en in *; lia).
    apply (rp_last _ _ _ _ _ H).
  Qed.

  #[using="Type"] Lemma v_lb_0 : v_lb (Z_to_bv 8 0) = Z_to_bv 64 0.
  Proof. LiaFast.lf_pins LiaFast.u0. apply bv_eq. vm_compute. reflexivity. Qed.
  #[using="mem beg n usp b1 H en g0 g1 gu ge Hbeg"] Lemma v_lb_small : forall (b : byte), (bv_unsigned b <= 7)%Z -> v_lb b = Z_to_bv 64 (bv_unsigned b).
  Proof. LiaFast.lf_pins (fun (mem beg n usp b1 H en g0 g1 gu ge Hbeg : LiaFast.U) => LiaFast.u0). intros b Hb. unfold v_lb. rewrite bv_signed_small8 by lia. reflexivity. Qed.
  #[using="mem beg n usp H en g0 g1 gu ge Hbeg"] Lemma b1_small : (0 <= bv_unsigned b1 <= 7)%Z.
  Proof. LiaFast.lf_pins (fun (mem beg n usp H en g0 g1 gu ge Hbeg : LiaFast.U) => LiaFast.u0). pose proof (bv_unsigned_in_range 8 b1). destruct (rp_b1 _ _ _ _ _ H); lia. Qed.
  #[using="mem usp H gu ge Hn Hbeg"] Lemma b0_cases : bv_unsigned b0 = 0%Z \/ (beg mod 8 < bv_unsigned b0 <= 7)%Z.
  Proof. LiaFast.lf_pins (fun (mem usp H gu ge Hn Hbeg : LiaFast.U) => LiaFast.u0).
    unfold b0. destruct (Z.ltb_spec g0 g1) as [Hlt|Hge]; [left; reflexivity|].
    destruct (rp_b1 _ _ _ _ _ H) as [Hz|Hp]; [left; exact Hz|]. right.
    pose proof divfacts as (D0 & D1 & _ & _ & DM). pose proof g0_le_g1.
    assert (Eg : g0 = g1) by lia. fold en in Hp.
    pose proof (Z.div_mod beg 8 ltac:(lia)) as Eb. fold g0 in Eb.
    assert (beg <= en - 1)%Z by (unfold en; lia). lia.
  Qed.

  Definition d_clob (r : reg) : bool := (bv_eqb r 11 || bv_eqb r 12 || bv_eqb r 13 || bv_eqb r 18)%bool.
  Definition d1_clob (r : reg) : bool := (bv_eqb r 11 || bv_eqb r 12 || bv_eqb r 13)%bool.
  #[using="Type"] Lemma d1_of_d : forall r, d_clob r = false -> d1_clob r = false.
  Proof. LiaFast.lf_pins LiaFast.u0. intros r Hr. unfold d_clob in Hr. unfold d1_clob. apply orb_false_iff in Hr as [Hr _]. exact Hr. Qed.

  (* [comment removed for export] *)
  #[using="n b1 H en g0 g1 gu ge Hn Hbeg Hsp"] Lemma blk_D1 : forall regs,
    getr regs 21 = Z_to_bv 64 0xe6678 -> getr regs 8 = Z_to_bv 64 beg ->
    exists regs',
      msteps SEGS (mkst regs (0x63ac8 : word) m7 rom) (mkst regs' (0x63ae4 : word) m7 rom)
      /\ getr regs' 11 = Z_to_bv 64 SB
      /\ (forall r, d1_clob r = false -> getr regs' r = getr regs r).
  Proof. LiaFast.lf_pins (fun (n b1 H en g0 g1 gu ge Hn Hbeg Hsp : LiaFast.U) => LiaFast.u0).
    intros regs H21 H8.
    pose proof rng as HR. unfold kLowEnd, kHighBeg, kHighEnd in HR. pose proof SB_val as HSB.
    pose proof divfacts as (D0 & D1 & DU & DE & DM). pose proof g0_le_g1 as Hg.
    pose proof cells_m7 as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8).
    assert (Hrd0 : rdn SEGS m7 (Z_to_bv 64 (SB + beg / 8)) 1 = Some [b0]) by (apply rdn1; apply shadow_beg).
    pose proof (Z.mod_pos_bound beg 8 ltac:(lia)) as Hbm.
    destruct b0_cases as [Hz|Hp].
    - (* [comment removed for export] *)
      eexists. split; [|split].
      + mld F_63ac8 D_63ac8 SB C2 H21.
        mstep ltac:(exact (PropExec.step_srli _ _ _ _ _ _ _ _ _ F_63acc eq_refl D_63acc)). gr. rewrite H8, (v_srli_3 beg) by lia.
        mstep ltac:(exact (step_add _ _ _ _ _ _ _ _ _ F_63ad0 eq_refl D_63ad0)). gr. rewrite v_add_zbv by lia.
        mstep ltac:(eapply (@step_lb _ _ _ _ _ _ _ _ _ _ b0 F_63ad4 eq_refl D_63ad4);
                     gr; imm_norm; zn; rewrite Z.add_0_r; exact Hrd0).
        rewrite (v_lb_small b0) by lia. rewrite Hz.
        mstep ltac:(eapply (step_beq_tk _ _ _ _ _ _ _ _ _ F_63ad8 eq_refl D_63ad8); gr; rewrite ?getr_zero; br_eq).
        apply mst_refl.
      + gr. reflexivity.
      + intros r Hr. unfold d1_clob in Hr.
        repeat (rewrite getr_other by (intros ->; cbn in Hr; discriminate)). reflexivity.
    - (* [comment removed for export] *)
      eexists. split; [|split].
      + mld F_63ac8 D_63ac8 SB C2 H21.
        mstep ltac:(exact (PropExec.step_srli _ _ _ _ _ _ _ _ _ F_63acc eq_refl D_63acc)). gr. rewrite H8, (v_srli_3 beg) by lia.
        mstep ltac:(exact (step_add _ _ _ _ _ _ _ _ _ F_63ad0 eq_refl D_63ad0)). gr. rewrite v_add_zbv by lia.
        mstep ltac:(eapply (@step_lb _ _ _ _ _ _ _ _ _ _ b0 F_63ad4 eq_refl D_63ad4);
                     gr; imm_norm; zn; rewrite Z.add_0_r; exact Hrd0).
        rewrite (v_lb_small b0) by lia.
        mstep ltac:(eapply (step_beq_ft _ _ _ _ _ _ _ _ _ F_63ad8 eq_refl D_63ad8); gr; rewrite ?getr_zero; br_eq).
        mstep ltac:(exact (step_andi _ _ _ _ _ _ _ _ _ F_63adc eq_refl D_63adc)). gr. rewrite H8, (v_andi_7 beg) by lia.
        mstep ltac:(eapply (step_bge_ft _ _ _ _ _ _ _ _ _ F_63ae0 eq_refl D_63ae0); gr; rewrite c_lts_zbv by lia; apply Z.ltb_lt; lia).
        apply mst_refl.
      + gr. reflexivity.
      + intros r Hr. unfold d1_clob in Hr.
        repeat (rewrite getr_other by (intros ->; cbn in Hr; discriminate)). reflexivity.
  Qed.

  (* [comment removed for export] *)
  #[using="b1 H g0 g1 gu ge Hn Hbeg Hsp"] Lemma blk_D2 : forall regs,
    getr regs 11 = Z_to_bv 64 SB -> getr regs 18 = Z_to_bv 64 en ->
    exists regs',
      msteps SEGS (mkst regs (0x63ae4 : word) m7 rom) (mkst regs' (0x63b38 : word) m7 rom)
      /\ (forall r, d_clob r = false -> getr regs' r = getr regs r).
  Proof. LiaFast.lf_pins (fun (b1 H g0 g1 gu ge Hn Hbeg Hsp : LiaFast.U) => LiaFast.u0).
    intros regs H11 H18.
    pose proof rng as HR. unfold kLowEnd, kHighBeg, kHighEnd in HR. pose proof SB_val as HSB.
    pose proof divfacts as (D0 & D1 & DU & DE & DM). pose proof g0_le_g1 as Hg.
    pose proof b1_small as Hb1s.
    assert (Hrd1 : rdn SEGS m7 (Z_to_bv 64 (SB + (en - 1) / 8)) 1 = Some [b1]) by (apply rdn1; apply shadow_last).
    pose proof (Z.mod_pos_bound (en - 1) 8 ltac:(lia)) as Hem.
    destruct (rp_b1 _ _ _ _ _ H) as [Hz|Hp].
    - (* [comment removed for export] *)
      eexists. split.
      + mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_63ae4 eq_refl D_63ae4)). gr. rewrite H18. zn.
        replace (en + -1)%Z with (en - 1)%Z by lia.
        mstep ltac:(exact (PropExec.step_srli _ _ _ _ _ _ _ _ _ F_63ae8 eq_refl D_63ae8)). gr. rewrite (v_srli_3 (en - 1)) by lia.
        mstep ltac:(exact (step_add _ _ _ _ _ _ _ _ _ F_63aec eq_refl D_63aec)). gr. rewrite H11, v_add_zbv by lia.
        mstep ltac:(eapply (@step_lb _ _ _ _ _ _ _ _ _ _ b1 F_63af0 eq_refl D_63af0);
                     gr; imm_norm; zn; rewrite Z.add_0_r; exact Hrd1).
        rewrite (v_lb_small b1) by lia. rewrite Hz.
        mstep ltac:(eapply (step_beq_tk _ _ _ _ _ _ _ _ _ F_63af4 eq_refl D_63af4); gr; rewrite ?getr_zero; br_eq).
        apply mst_refl.
      + intros r Hr. unfold d_clob in Hr.
        repeat (rewrite getr_other by (intros ->; cbn in Hr; discriminate)). reflexivity.
    - (* [comment removed for export] *)
      fold en in Hp.
      eexists. split.
      + mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_63ae4 eq_refl D_63ae4)). gr. rewrite H18. zn.
        replace (en + -1)%Z with (en - 1)%Z by lia.
        mstep ltac:(exact (PropExec.step_srli _ _ _ _ _ _ _ _ _ F_63ae8 eq_refl D_63ae8)). gr. rewrite (v_srli_3 (en - 1)) by lia.
        mstep ltac:(exact (step_add _ _ _ _ _ _ _ _ _ F_63aec eq_refl D_63aec)). gr. rewrite H11, v_add_zbv by lia.
        mstep ltac:(eapply (@step_lb _ _ _ _ _ _ _ _ _ _ b1 F_63af0 eq_refl D_63af0);
                     gr; imm_norm; zn; rewrite Z.add_0_r; exact Hrd1).
        rewrite (v_lb_small b1) by lia.
        mstep ltac:(eapply (step_beq_ft _ _ _ _ _ _ _ _ _ F_63af4 eq_refl D_63af4); gr; rewrite ?getr_zero; br_eq).
        mstep ltac:(exact (step_andi _ _ _ _ _ _ _ _ _ F_63af8 eq_refl D_63af8)). gr. rewrite (v_andi_7 (en - 1)) by lia.
        mstep ltac:(eapply (step_blt_tk _ _ _ _ _ _ _ _ _ F_63afc eq_refl D_63afc); gr; rewrite c_lts_zbv by lia; apply Z.ltb_lt; lia).
        apply mst_refl.
      + intros r Hr. unfold d_clob in Hr.
        repeat (rewrite getr_other by (intros ->; cbn in Hr; discriminate)). reflexivity.
  Qed.

  #[using="b1 H g0 g1 gu ge Hn Hbeg Hsp"] Lemma blk_D : forall regs,
    getr regs 21 = Z_to_bv 64 0xe6678 -> getr regs 8 = Z_to_bv 64 beg -> getr regs 18 = Z_to_bv 64 en ->
    exists regs',
      msteps SEGS (mkst regs (0x63ac8 : word) m7 rom) (mkst regs' (0x63b38 : word) m7 rom)
      /\ (forall r, d_clob r = false -> getr regs' r = getr regs r).
  Proof. LiaFast.lf_pins (fun (b1 H g0 g1 gu ge Hn Hbeg Hsp : LiaFast.U) => LiaFast.u0).
    intros regs H21 H8 H18.
    destruct (blk_D1 regs H21 H8) as (r1 & M1 & R11 & K1).
    destruct (blk_D2 r1 R11 ltac:(rewrite (K1 18) by reflexivity; exact H18)) as (r2 & M2 & K2).
    exists r2. split; [exact (msteps_trans _ _ _ _ M1 M2)|].
    intros r Hr. rewrite (K2 r Hr). exact (K1 r (d1_of_d r Hr)).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="b1 H g0 g1 Hn Hbeg Hsp"] Lemma mz_pre : (gu < ge)%Z -> mzH m7 (SB + gu) (ge - gu) (usp - 64).
  Proof. LiaFast.lf_pins (fun (b1 H g0 g1 Hn Hbeg Hsp : LiaFast.U) => LiaFast.u0).
    intros Hgg.
    pose proof rng as HR. unfold kLowEnd, kHighBeg, kHighEnd in HR. pose proof SB_val as HSB.
    pose proof divfacts as (D0 & D1 & DU & DE & DM). pose proof (rp_disj _ _ _ _ _ H) as Hdisj.
    pose proof (rp_b1 _ _ _ _ _ H) as Hb1.
    constructor.
    - unfold ge, gu, en in *. lia.
    - lia.
    - lia.
    - lia.
    - left. unfold g1, ge, en in *. lia.
    - intros i Hi. rewrite m7_below by (rewrite zbv_u by lia; unfold g1, ge, en in *; lia).
      destruct (Z.lt_ge_cases (gu + i) g1) as [Hlt | Hge'].
      + replace (SB + gu + i)%Z with (SB + (gu + i))%Z by lia. apply (rp_zero _ _ _ _ _ H). unfold g0, g1, gu, en in *. lia.
      + assert (Ei : (gu + i)%Z = g1) by (unfold g1, ge, en in *; lia).
        assert (Hz : bv_unsigned b1 = 0%Z).
        { destruct Hb1 as [Hz|Hp]; [exact Hz|]. exfalso. fold en in Hp.
          (* [comment removed for export] *)
          assert (Hlt : (g1 < ge)%Z) by lia. lia. }
        replace (SB + gu + i)%Z with (SB + g1)%Z by lia.
        unfold g1, en. rewrite (rp_last _ _ _ _ _ H). f_equal. apply bv_eq. rewrite Hz. reflexivity.
    - apply stk8; [lia | lia |]. intros x Hx. unfold m7. repeat apply store_ok1_wbytes. exact Hx.
  Qed.

  Definition e_clob (r : reg) : bool := (mz_clob r || bv_eqb r 1)%bool.

  #[using="b1 H g0 g1 Hn Hbeg Hsp"] Lemma blk_E : forall regs, (gu < ge)%Z ->
    getr regs 19 = Z_to_bv 64 (SB + gu) -> getr regs 10 = Z_to_bv 64 (SB + ge) -> getr regs 2 = Z_to_bv 64 (usp - 64) ->
    exists regs',
      msteps SEGS (mkst regs (0x63b38 : word) m7 rom) (mkst regs' (0x63b4c : word) m8 rom)
      /\ getr regs' 2 = Z_to_bv 64 (usp - 64)
      /\ (forall r, e_clob r = false -> getr regs' r = getr regs r).
  Proof. LiaFast.lf_pins (fun (b1 H g0 g1 Hn Hbeg Hsp : LiaFast.U) => LiaFast.u0).
    intros regs Hgg H19 H10 H2.
    pose proof rng as HR. unfold kLowEnd, kHighBeg, kHighEnd in HR. pose proof SB_val as HSB.
    pose proof divfacts as (D0 & D1 & DU & DE & DM).
    evar (rr : bvmap 5 word).
    edestruct (as_mem_is_zero m7 rom (SB + gu) (ge - gu) (usp - 64) (0x63b48 : word) (mz_pre Hgg) rr ret_ok_d9f50)
      as (r1 & M1 & R10 & R2 & R1 & K1); cycle -1.
    { exists r1. split; [|split].
      - mstep ltac:(eapply (step_bgeu_ft _ _ _ _ _ _ _ _ _ F_63b38 eq_refl D_63b38); gr; rewrite ?H19, ?H10;
                     unfold ge, gu, en in *; br_lt).
        mstep ltac:(exact (step_sub _ _ _ _ _ _ _ _ _ F_63b3c eq_refl D_63b3c)). gr. rewrite H10, H19, v_sub_zbv by lia.
        replace (SB + ge - (SB + gu))%Z with (ge - gu)%Z by lia.
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_63b40 eq_refl D_63b40)). gr. rewrite H19. zn. rewrite Z.add_0_r.
        mstep ltac:(exact (step_jal_link _ _ _ _ _ _ _ _ F_63b44 eq_refl D_63b44)). rewrite lit_d9f50.
        eapply msteps_trans; [subst rr; exact M1|].
        mstep ltac:(eapply (step_beq_ft _ _ _ _ _ _ _ _ _ F_63b48 eq_refl D_63b48); gr; rewrite ?R10, ?getr_zero; br_eq).
        unfold m8. replace (usp - 64 - 8)%Z with (usp - 72)%Z by lia. apply mst_refl.
      - exact R2.
      - subst rr. intros r Hr. unfold e_clob in Hr. apply orb_false_iff in Hr. destruct Hr as [Hr Hr1'].
        destruct (bv_eq_dec _ r 2) as [-> | Hr2].
        { rewrite R2. symmetry. exact H2. }
        rewrite (K1 r Hr Hr2) by (intros ->; cbn in Hr1'; discriminate).
        unfold mz_clob in Hr.
        repeat (rewrite getr_other by (intros ->; cbn in Hr, Hr1'; discriminate)). reflexivity. }
    all: subst rr; gr; try reflexivity; try assumption.
  Qed.

  (* [comment removed for export] *)
  #[using="b1 H g0 g1 Hn Hbeg"] Lemma blk_E0 : forall regs, (ge <= gu)%Z ->
    getr regs 19 = Z_to_bv 64 (SB + gu) -> getr regs 10 = Z_to_bv 64 (SB + ge) ->
    msteps SEGS (mkst regs (0x63b38 : word) m7 rom) (mkst regs (0x63b4c : word) m7 rom).
  Proof. LiaFast.lf_pins (fun (b1 H g0 g1 Hn Hbeg : LiaFast.U) => LiaFast.u0).
    intros regs Hgg H19 H10.
    pose proof rng as HR. unfold kLowEnd, kHighBeg, kHighEnd in HR. pose proof SB_val as HSB.
    pose proof divfacts as (D0 & D1 & DU & DE & DM).
    mstep ltac:(eapply (step_bgeu_tk _ _ _ _ _ _ _ _ _ F_63b38 eq_refl D_63b38); gr; rewrite ?H19, ?H10;
                 unfold ge, gu, en in *; br_lt).
    apply mst_refl.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac mld2 F D v Hrd Hbase :=
    mstep ltac:(eapply (@step_ld _ _ _ _ _ _ _ _ _ _ _ v F eq_refl D);
                 [ gr; rewrite ?Hbase; imm_norm; zn;
                   match goal with |- rdn _ _ (Z_to_bv 64 ?a) 8 = _ =>
                     match type of Hrd with rdn _ _ (Z_to_bv 64 ?c) 8 = _ =>
                       replace a with c by lia end end; exact Hrd
                 | apply bytes_le_to_Z_8 ]).

  Definition f_clob (r : reg) : bool :=
    (bv_eqb r 1 || bv_eqb r 2 || bv_eqb r 8 || bv_eqb r 9 || bv_eqb r 10 || bv_eqb r 18 || bv_eqb r 19
     || bv_eqb r 20 || bv_eqb r 21)%bool.

  #[using="beg n b1 H en g0 g1 gu ge Hbeg Hsp"] Lemma rd7_ra : rdn SEGS m7 (Z_to_bv 64 (usp - 8)) 8 = Some (word_to_le_bytes 8 ra).            Proof. LiaFast.lf_pins (fun (beg n b1 H en g0 g1 gu ge Hbeg Hsp : LiaFast.U) => LiaFast.u0). rd_slot. Qed.
  #[using="beg n b1 H en g0 g1 gu ge Hbeg Hsp"] Lemma rd7_s0 : rdn SEGS m7 (Z_to_bv 64 (usp - 16)) 8 = Some (word_to_le_bytes 8 (getr regs0 8)). Proof. LiaFast.lf_pins (fun (beg n b1 H en g0 g1 gu ge Hbeg Hsp : LiaFast.U) => LiaFast.u0). rd_slot. Qed.
  #[using="beg n b1 H en g0 g1 gu ge Hbeg Hsp"] Lemma rd7_s1 : rdn SEGS m7 (Z_to_bv 64 (usp - 24)) 8 = Some (word_to_le_bytes 8 (getr regs0 9)). Proof. LiaFast.lf_pins (fun (beg n b1 H en g0 g1 gu ge Hbeg Hsp : LiaFast.U) => LiaFast.u0). rd_slot. Qed.
  #[using="beg n b1 H en g0 g1 gu ge Hbeg Hsp"] Lemma rd7_s2 : rdn SEGS m7 (Z_to_bv 64 (usp - 32)) 8 = Some (word_to_le_bytes 8 (getr regs0 18)). Proof. LiaFast.lf_pins (fun (beg n b1 H en g0 g1 gu ge Hbeg Hsp : LiaFast.U) => LiaFast.u0). rd_slot. Qed.
  #[using="beg n b1 H en g0 g1 gu ge Hbeg Hsp"] Lemma rd7_s3 : rdn SEGS m7 (Z_to_bv 64 (usp - 40)) 8 = Some (word_to_le_bytes 8 (getr regs0 19)). Proof. LiaFast.lf_pins (fun (beg n b1 H en g0 g1 gu ge Hbeg Hsp : LiaFast.U) => LiaFast.u0). rd_slot. Qed.
  #[using="beg n b1 H en g0 g1 gu ge Hbeg Hsp"] Lemma rd7_s4 : rdn SEGS m7 (Z_to_bv 64 (usp - 48)) 8 = Some (word_to_le_bytes 8 (getr regs0 20)). Proof. LiaFast.lf_pins (fun (beg n b1 H en g0 g1 gu ge Hbeg Hsp : LiaFast.U) => LiaFast.u0). rd_slot. Qed.
  #[using="beg n b1 H en g0 g1 gu ge Hbeg Hsp"] Lemma rd7_s5 : rdn SEGS m7 (Z_to_bv 64 (usp - 56)) 8 = Some (word_to_le_bytes 8 (getr regs0 21)). Proof. LiaFast.lf_pins (fun (beg n b1 H en g0 g1 gu ge Hbeg Hsp : LiaFast.U) => LiaFast.u0). rd_slot. Qed.

  #[using="beg n b1 H Hret en g0 g1 gu ge Hbeg Hsp"] Lemma blk_F : forall m regs, (m = m8 \/ m = m7) ->
    getr regs 2 = Z_to_bv 64 (usp - 64) ->
    exists regs',
      msteps SEGS (mkst regs (0x63b4c : word) m rom) (mkst regs' ra m rom)
      /\ getr regs' 10 = Z_to_bv 64 0 /\ getr regs' 2 = Z_to_bv 64 usp /\ getr regs' 1 = ra
      /\ getr regs' 8 = getr regs0 8 /\ getr regs' 9 = getr regs0 9 /\ getr regs' 18 = getr regs0 18
      /\ getr regs' 19 = getr regs0 19 /\ getr regs' 20 = getr regs0 20 /\ getr regs' 21 = getr regs0 21
      /\ (forall r, f_clob r = false -> getr regs' r = getr regs r).
  Proof. LiaFast.lf_pins (fun (beg n b1 H Hret en g0 g1 gu ge Hbeg Hsp : LiaFast.U) => LiaFast.u0).
    intros m regs Hm H2.
    assert (RD1 : rdn SEGS m (Z_to_bv 64 (usp - 8)) 8 = Some (word_to_le_bytes 8 ra)) by (destruct Hm as [->| ->]; [exact rd_ra | exact rd7_ra]).
    assert (RD8 : rdn SEGS m (Z_to_bv 64 (usp - 16)) 8 = Some (word_to_le_bytes 8 (getr regs0 8))) by (destruct Hm as [->| ->]; [exact rd_s0 | exact rd7_s0]).
    assert (RD9 : rdn SEGS m (Z_to_bv 64 (usp - 24)) 8 = Some (word_to_le_bytes 8 (getr regs0 9))) by (destruct Hm as [->| ->]; [exact rd_s1 | exact rd7_s1]).
    assert (RD18 : rdn SEGS m (Z_to_bv 64 (usp - 32)) 8 = Some (word_to_le_bytes 8 (getr regs0 18))) by (destruct Hm as [->| ->]; [exact rd_s2 | exact rd7_s2]).
    assert (RD19 : rdn SEGS m (Z_to_bv 64 (usp - 40)) 8 = Some (word_to_le_bytes 8 (getr regs0 19))) by (destruct Hm as [->| ->]; [exact rd_s3 | exact rd7_s3]).
    assert (RD20 : rdn SEGS m (Z_to_bv 64 (usp - 48)) 8 = Some (word_to_le_bytes 8 (getr regs0 20))) by (destruct Hm as [->| ->]; [exact rd_s4 | exact rd7_s4]).
    assert (RD21 : rdn SEGS m (Z_to_bv 64 (usp - 56)) 8 = Some (word_to_le_bytes 8 (getr regs0 21))) by (destruct Hm as [->| ->]; [exact rd_s5 | exact rd7_s5]).
    eexists. split.
    - mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_63b4c eq_refl D_63b4c)). rewrite getr_zero. zn. rewrite Z.add_0_r.
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_63b50 eq_refl D_63b50)). gr. zn. rewrite Z.add_0_r.
      mld2 F_63b54 D_63b54 ra RD1 H2.
      mld2 F_63b58 D_63b58 (getr regs0 8) RD8 H2.
      mld2 F_63b5c D_63b5c (getr regs0 9) RD9 H2.
      mld2 F_63b60 D_63b60 (getr regs0 18) RD18 H2.
      mld2 F_63b64 D_63b64 (getr regs0 19) RD19 H2.
      mld2 F_63b68 D_63b68 (getr regs0 20) RD20 H2.
      mld2 F_63b6c D_63b6c (getr regs0 21) RD21 H2.
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_63b70 eq_refl D_63b70)). gr. rewrite H2. zn.
      replace (usp - 64 + 64)%Z with usp by lia.
      eapply mst_step; [reflexivity | eapply (step_jalr_x0 _ _ _ _ _ _ _ _ ra F_63b74 eq_refl D_63b74); gr; reflexivity |].
      imm_norm. rewrite Hret. apply mst_refl.
    - gr. repeat split; try reflexivity.
      intros r Hr. unfold f_clob in Hr.
      repeat (rewrite getr_other by (intros ->; cbn in Hr; discriminate)). reflexivity.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="beg n b1 H Hret H01 H02 H010 H011 en g0 g1 gu ge Hn Hbeg Hsp"] Theorem as_region_is_poisoned_RP :
    exists regs' mm,
      msteps SEGS (mkst regs0 (0x639d4 : word) mem rom) (mkst regs' ra mm rom) /\ (mm = m8 \/ mm = m7)
      /\ getr regs' 10 = Z_to_bv 64 0 /\ getr regs' 2 = Z_to_bv 64 usp /\ getr regs' 1 = ra
      /\ (forall r, rp_clob r = false -> getr regs' r = getr regs0 r).
  Proof. LiaFast.lf_pins (fun (beg n b1 H Hret H01 H02 H010 H011 en g0 g1 gu ge Hn Hbeg Hsp : LiaFast.U) => LiaFast.u0).
    destruct blk_P as (q1 & MP & P2 & P8 & P9 & P1 & PK).
    destruct (blk_A q1 P8) as (q2 & MA & A21 & A11 & A12 & AK).
    assert (AK' : forall r, m2s_clob r = false -> r <> 21 -> getr q2 r = getr q1 r) by exact AK.
    destruct (blk_B q2) as (q3 & MB & B18 & BK);
      [rewrite AK by (reflexivity || discriminate); exact P8
      |rewrite AK by (reflexivity || discriminate); exact P9 | exact A11 | exact A12 |].
    destruct (blk_C q3) as (q4 & MC & C19 & C10 & CK);
      [rewrite BK, AK by (reflexivity || discriminate); exact P8 | exact B18 |].
    destruct (blk_D q4) as (q5 & MD & DK);
      [rewrite CK, BK by (reflexivity || discriminate); exact A21
      |rewrite CK, BK, AK by (reflexivity || discriminate); exact P8
      |rewrite CK by (reflexivity || discriminate); exact B18 |].
    assert (HE : exists q6 mm, msteps SEGS (mkst q5 (0x63b38 : word) m7 rom) (mkst q6 (0x63b4c : word) mm rom) /\ (mm = m8 \/ mm = m7)
                   /\ getr q6 2 = Z_to_bv 64 (usp - 64) /\ (forall r, e_clob r = false -> getr q6 r = getr q5 r)).
    { destruct (Z.lt_ge_cases gu ge) as [Hgg|Hgg].
      - destruct (blk_E q5 Hgg) as (q6 & ME & E2 & EK);
          [rewrite DK by reflexivity; exact C19 | rewrite DK by reflexivity; exact C10
          |rewrite DK, CK, BK, AK by (reflexivity || discriminate); exact P2 |].
        exists q6, m8. split; [exact ME|]. split; [left; reflexivity|]. split; [exact E2 | exact EK].
      - exists q5, m7. split; [apply (blk_E0 q5 Hgg); [rewrite DK by reflexivity; exact C19 | rewrite DK by reflexivity; exact C10]|].
        split; [right; reflexivity|]. split; [rewrite DK, CK, BK, AK by (reflexivity || discriminate); exact P2 | intros; reflexivity]. }
    destruct HE as (q6 & mm & ME & Hmm & E2 & EK).
    destruct (blk_F mm q6 Hmm E2) as (q7 & MF & F10 & F2 & F1 & F8 & F9 & F18 & F19 & F20 & F21 & FK).
    exists q7, mm. split; [|split; [exact Hmm | split; [exact F10 | split; [exact F2 | split; [exact F1|]]]]].
    - eapply msteps_trans; [exact MP|]. eapply msteps_trans; [exact MA|]. eapply msteps_trans; [exact MB|].
      eapply msteps_trans; [exact MC|]. eapply msteps_trans; [exact MD|]. eapply msteps_trans; [exact ME|]. exact MF.
    - intros r Hr.
      destruct (bv_eq_dec _ r 1) as [-> | N1]; [rewrite F1; symmetry; exact H01|].
      destruct (bv_eq_dec _ r 2) as [-> | N2]; [rewrite F2; symmetry; exact H02|].
      destruct (bv_eq_dec _ r 8) as [-> | N8]; [exact F8|].
      destruct (bv_eq_dec _ r 9) as [-> | N9]; [exact F9|].
      destruct (bv_eq_dec _ r 18) as [-> | N18]; [exact F18|].
      destruct (bv_eq_dec _ r 19) as [-> | N19]; [exact F19|].
      destruct (bv_eq_dec _ r 20) as [-> | N20]; [exact F20|].
      destruct (bv_eq_dec _ r 21) as [-> | N21]; [exact F21|].
      assert (Hm2s : m2s_clob r = false) by exact Hr.
      unfold rp_clob in Hr.
      repeat match type of Hr with (?a || ?b)%bool = false =>
        apply orb_false_iff in Hr; destruct Hr as [Hr ?] end.
      Ltac clobside N1 N2 N8 N9 N18 N19 N20 N21 :=
        unfold f_clob, e_clob, d_clob, b_clob, mz_clob, m2s_clob;
        rewrite ?(bv_eqb_neq _ _ N1), ?(bv_eqb_neq _ _ N2), ?(bv_eqb_neq _ _ N8), ?(bv_eqb_neq _ _ N9),
                ?(bv_eqb_neq _ _ N18), ?(bv_eqb_neq _ _ N19), ?(bv_eqb_neq _ _ N20), ?(bv_eqb_neq _ _ N21);
        repeat match goal with H : bv_eqb _ _ = false |- _ => rewrite H end; reflexivity.
      rewrite FK by clobside N1 N2 N8 N9 N18 N19 N20 N21.
      rewrite EK by clobside N1 N2 N8 N9 N18 N19 N20 N21.
      rewrite DK by clobside N1 N2 N8 N9 N18 N19 N20 N21.
      rewrite CK by first [exact Hm2s | assumption].
      rewrite BK by clobside N1 N2 N8 N9 N18 N19 N20 N21.
      rewrite AK by first [exact Hm2s | assumption].
      apply PK. unfold rp_tmp, rp_clob.
      rewrite (bv_eqb_neq _ _ N1), (bv_eqb_neq _ _ N2), (bv_eqb_neq _ _ N8), (bv_eqb_neq _ _ N9),
              (bv_eqb_neq _ _ N18), (bv_eqb_neq _ _ N19), (bv_eqb_neq _ _ N20), (bv_eqb_neq _ _ N21).
      repeat match goal with H : bv_eqb r ?k = false |- _ => rewrite H end. reflexivity.
  Qed.
End RP.

(* [comment removed for export] *)
Section WithFP3.
Context {fx : FPState}.
#[using="Type"] Theorem as_region_is_poisoned :
  forall (mem rom : word -> option byte) (beg n usp : Z) (b1 : byte),
  rpH mem beg n usp b1 ->
  forall regs (ra : word),
  ret_ok ra -> getr regs 1 = ra -> getr regs 2 = Z_to_bv 64 usp ->
  getr regs 10 = Z_to_bv 64 beg -> getr regs 11 = Z_to_bv 64 n ->
  exists regs' mm,
    msteps SEGS (mkst regs (0x639d4 : word) mem rom) (mkst regs' ra mm rom)
    /\ (mm = rp_frame mem usp ra (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) \/
        mm = rp_frame7 mem usp ra (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21))
    /\ getr regs' 10 = Z_to_bv 64 0 /\ getr regs' 2 = Z_to_bv 64 usp /\ getr regs' 1 = ra
    /\ (forall r, rp_clob r = false -> getr regs' r = getr regs r).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros mem rom beg n usp b1 H regs ra Hret H1 H2 H10 H11.
  rewrite <- (m8_frame mem usp regs ra), <- (m7_frame mem usp regs ra).
  exact (as_region_is_poisoned_RP mem rom beg n usp b1 H regs ra Hret H1 H2 H10 H11).
Qed.

(* [comment removed for export] *)

End WithFP3.
(* [comment removed for export] *)
