(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "bool"; "option"; "andb"; "nat"; "true"; "list"; "prod"; "Some"; "snd"; "None"; "fst"; "length"; "false"; "negb"; "pair"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "N"; "@Corelib.Init.Logic"; "eq"; "and"; "or"; "True"; "not"; "ex"; "iff"; "False"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "tfact"; "eval"; "valuation"; "agree_below"; "sv_below"; "odefault"; "sprop"; "tf_holds"; "rl"; "sobj"; "c_off"; "c_width"; "cell"; "fldv"; "holds"; "ob_base"; "rm"; "tf_expr"; "zrel"; "SLit"; "c_val"; "enc_bytes"; "ob_cells"; "ob_dflt"; "osxn_eqb"; "rw"; "soff"; "sprop_below"; "sv_eqb"; "tf_below"; "TF2le"; "TFge"; "TFle"; "ext_low"; "extv"; "oaddr"; "ob_hi"; "ob_lo"; "sprop_eqb"; "tf_eqb"; "tf_eqb_with"; "tf_with_expr"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"; "bv_extract"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "to_nat"; "pow"; "mul"; "sub"; "eqb"; "leb"; "ltb"; "modulo"; "of_nat"; "@Corelib.Lists.ListDef"; "Forall"; "nth"; "firstn"; "skipn"; "@Stdlib.Lists.List"; "forallb"; "Exists"; "nth_error"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "ms_mem"; "find_segment"; "machine_state"; "memory_read"; "ms_fcsr"; "ms_fregs"; "ms_pc"; "ms_regs"; "ms_resv"; "ms_rom"; "ms_svc_pending"; "wview"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState.WithSegs"; "sfcsr"; "image_byte"; "obj_hi_of"; "obj_lo_of"; "rd_bytes"; "ss_facts"; "ss_fcsr"; "ss_fregs"; "ss_objs"; "ss_regs"; "ss_resv"; "cell_holds"; "cell_wf"; "covered"; "dflt_holds"; "dflt_inv"; "dflt_wf"; "dflt_writable"; "elem_holds"; "fcsr_match"; "fld_ok"; "freg_sv"; "fregs_match"; "in_cell"; "mem_frame"; "mem_match"; "obj_holds"; "obj_range"; "obj_wf"; "outside_all"; "pairwise_disjoint"; "rd"; "reg_sv"; "regs_match"; "resv_match"; "ro_addr"; "ro_clear"; "rom_ok"; "ss_next"; "ss_pc"; "swf"; "@Stdlib.Arith.PeanoNat.Nat"; "eqb"; "@LinuxProcessSemantics.LinuxProcessSem.MemImageType"; "Segment"; "seg_writable"; "@LinuxProcessSemantics.Riscv.Sem"; "reg_get"; "@Stdlib.Bool.Bool"; "eqb"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "cfg_model"; "cfg_ms"; "config"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@LinuxProcessSemantics.Riscv.Prelude"; "sext"; "zext"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "model_idle"; "@Stdlib.NArith.BinNat.N"; "eqb"; "@Stdlib.PArith.BinPos.Pos"; "le"; "lt"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import PArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Inductive sv : Type :=
| SLit  (z : Z)
| SVar  (i : positive)
| SAlu  (op : aluop) (a b : sv)
| SAluW (op : aluop) (a b : sv)
| SMd   (op : mulop) (a b : sv)
| SMdW  (op : mulop) (a b : sv)
| SExt  (sgn : bool) (w : N) (a : sv)
| SLBytes (l : positive) (i : sv) (k : Z).

Record valuation := mkVal {
  rw : positive -> word;
  rl : positive -> list byte;
  rm : word -> option byte
}.

Definition sublist (i k : Z) (l : list byte) : list byte := ltac2:(tb__ "0|1|
S57S45Q8A1M0S4cVk;A1S58G0S4cVi;A1Vl;A3A3").

Definition ext_low (sgn : bool) (w : N) (v : word) : word := ltac2:(tb__ "0|2|
S0S45Q40M0A1Lsgn;Vsgn;S9bVw;G0S48G0Q0Vw;Vv;A4M1A3S9cVw;G0G1A3X0x2").

Fixpoint eval (rho : valuation) (e : sv) : word :=
  match e with
  | SLit z => Z_to_bv 64 z
  | SVar i => rw rho i
  | SAlu op a b => alu64 op (eval rho a) (eval rho b)
  | SAluW op a b => sext 64 (alu32 op (low32 (eval rho a)) (low32 (eval rho b)))
  | SMd op a b => mul_div op (eval rho a) (eval rho b)
  | SMdW op a b => sext 64 (mul_div op (low32 (eval rho a)) (low32 (eval rho b)))
  | SExt sgn w a => ext_low sgn w (eval rho a)
  | SLBytes l i k => le_bytes_to_word (sublist (bv_unsigned (eval rho i)) k (rl rho l))
  end.

Fixpoint sv_eqb (a b : sv) : bool :=
  match a, b with
  | SLit x, SLit y => Z.eqb x y
  | SVar i, SVar j => Pos.eqb i j
  | SAlu o1 a1 b1, SAlu o2 a2 b2 =>
      if aluop_eq_dec o1 o2 then sv_eqb a1 a2 && sv_eqb b1 b2 else false
  | SAluW o1 a1 b1, SAluW o2 a2 b2 =>
      if aluop_eq_dec o1 o2 then sv_eqb a1 a2 && sv_eqb b1 b2 else false
  | SMd o1 a1 b1, SMd o2 a2 b2 =>
      if mulop_eq_dec o1 o2 then sv_eqb a1 a2 && sv_eqb b1 b2 else false
  | SMdW o1 a1 b1, SMdW o2 a2 b2 =>
      if mulop_eq_dec o1 o2 then sv_eqb a1 a2 && sv_eqb b1 b2 else false
  | SExt s1 w1 a1, SExt s2 w2 a2 => Bool.eqb s1 s2 && N.eqb w1 w2 && sv_eqb a1 a2
  | SLBytes l1 i1 k1, SLBytes l2 i2 k2 => Pos.eqb l1 l2 && sv_eqb i1 i2 && Z.eqb k1 k2
  | _, _ => false
  end.

Lemma sv_eqb_sound : ltac2:(tb__ "0|0|
S1aS1aS12S0S37R2R1A2S4A3S12S1aR3R2A3F_;Fb;Fa;").
Proof.
  induction a; destruct b; cbn; intros H; try discriminate.
  - apply Z.eqb_eq in H. congruence.
  - apply Pos.eqb_eq in H. congruence.
  - destruct (aluop_eq_dec op op0); [|discriminate].
    apply andb_prop in H as [H1 H2]. rewrite (IHa1 _ H1), (IHa2 _ H2). congruence.
  - destruct (aluop_eq_dec op op0); [|discriminate].
    apply andb_prop in H as [H1 H2]. rewrite (IHa1 _ H1), (IHa2 _ H2). congruence.
  - destruct (mulop_eq_dec op op0); [|discriminate].
    apply andb_prop in H as [H1 H2]. rewrite (IHa1 _ H1), (IHa2 _ H2). congruence.
  - destruct (mulop_eq_dec op op0); [|discriminate].
    apply andb_prop in H as [H1 H2]. rewrite (IHa1 _ H1), (IHa2 _ H2). congruence.
  - apply andb_prop in H as [H12 H3]. apply andb_prop in H12 as [H1 H2].
    apply Bool.eqb_prop in H1. apply N.eqb_eq in H2. rewrite (IHa _ H3). congruence.
  - apply andb_prop in H as [H12 H3]. apply andb_prop in H12 as [H1 H2].
    apply Pos.eqb_eq in H1. rewrite (IHa _ H2). apply Z.eqb_eq in H3. congruence.
Qed.

Lemma sv_eqb_eval : ltac2:(tb__ "0|0|
S1dS1aS1aS12S0S37R2R1A2S4A3S12S45Q40A1S1cR4R3A2S1cR4R2A2A3F_;Fb;Fa;Frho;").
Proof. intros rho a b H. rewrite (sv_eqb_sound _ _ H). reflexivity. Qed.

Fixpoint sv_below (n : positive) (e : sv) : bool :=
  match e with
  | SLit _ => true
  | SVar i => Pos.ltb i n
  | SAlu _ a b | SAluW _ a b | SMd _ a b | SMdW _ a b => sv_below n a && sv_below n b
  | SExt _ _ a => sv_below n a
  | SLBytes _ i _ => sv_below n i
  end.

Definition agree_below (n : positive) (rho rho' : valuation) : Prop := ltac2:(tb__ "0|2|
S13S10Sa0R1Vn;A2S12S45Q40A1M0S34Vrho;R2A2S34Vrho';R2A2A3F_;Fi;S13S10S12S5S45Q8A1M1A1S23Vrho;R1A2S23Vrho';R1A2A3Fl;G0S12S1G1A1S2bVrho;R1A2S2bVrho';R1A2A3Fa;A2A2").

Lemma agree_below_refl : ltac2:(tb__ "0|0|
S10S1dS1eR2R1R1A3Frho;Fn;").
Proof. intros n rho. repeat split; intros; reflexivity. Qed.

Lemma agree_below_trans : ltac2:(tb__ "0|0|
S10S1dS1dS1dS1eR4R3R2A3S1eR5R3R2A3S1eR6R5R3A3F_;F_;Frho3;Frho2;Frho1;Fn;").
Proof.
  intros n r1 r2 r3 (A1 & B1 & C1) (A2 & B2 & C2). repeat split; intros.
  - rewrite A1 by lia. apply A2. lia.
  - rewrite B1. apply B2.
  - rewrite C1. apply C2.
Qed.

Lemma agree_below_le : ltac2:(tb__ "0|0|
S10S10S1dS1dS9fR3R4A2S1eR5R3R2A3S1eR5R4R3A3F_;F_;Frho';Frho;Fm;Fn;").
Proof. intros n m rho rho' Hle (A & B & C). repeat split; auto. intros i Hi. apply A. lia. Qed.

Lemma eval_agree : ltac2:(tb__ "0|0|
S10S1dS1dS1aS1eR4R3R2A3S12S0S1fR5R2A2S4A3S12S45Q40A1S1cR5R3A2S1cR4R3A2A3F_;F_;Fe;Frho';Frho;Fn;").
Proof.
  intros n rho rho' e Hag. pose proof Hag as (A & B & C). induction e; cbn; intros Hb;
    try (apply andb_prop in Hb as [Hb1 Hb2]);
    try rewrite (IHe1 Hb1); try rewrite (IHe2 Hb2); try reflexivity.
  - apply A. apply Pos.ltb_lt, Hb.
  - rewrite (IHe Hb). reflexivity.
  - rewrite B, (IHe Hb). reflexivity.
Qed.

Inductive sprop : Type :=
| SPBranch (c : branch_cond) (a b : sv)
| SPNot (p : sprop)
| SPUlt (a b : sv)
| SPUle (a b : sv)
| SPEq (a b : sv)
| SPTrue
| SPAlign (i : positive) (a : Z).

Fixpoint holds (rho : valuation) (p : sprop) : Prop :=
  match p with
  | SPBranch c a b => branch_taken c (eval rho a) (eval rho b) = true
  | SPNot p => ~ holds rho p
  | SPUlt a b => (bv_unsigned (eval rho a) < bv_unsigned (eval rho b))%Z
  | SPUle a b => (bv_unsigned (eval rho a) <= bv_unsigned (eval rho b))%Z
  | SPEq a b => eval rho a = eval rho b
  | SPTrue => True
  | SPAlign i a => (0 <= a /\ bv_unsigned (rw rho i) mod 2 ^ a = 0)%Z
  end.

Fixpoint sprop_below (n : positive) (p : sprop) : bool :=
  match p with
  | SPBranch _ a b | SPUlt a b | SPUle a b | SPEq a b => sv_below n a && sv_below n b
  | SPNot p => sprop_below n p
  | SPTrue => true
  | SPAlign i _ => Pos.ltb i n
  end.

Lemma holds_agree : ltac2:(tb__ "0|0|
S10S1dS1dS21S1eR4R3R2A3S12S0S36R5R2A2S4A3S18S29R5R3A2S29R4R3A2A2F_;F_;Fp;Frho';Frho;Fn;").
Proof.
  intros n rho rho' p Hag. induction p; cbn; intros Hb;
    try (apply andb_prop in Hb as [Hb1 Hb2];
         rewrite (eval_agree _ _ _ _ Hag Hb1), (eval_agree _ _ _ _ Hag Hb2)); try tauto.
  all: try (specialize (IHp Hb); tauto).
  destruct Hag as (A & _ & _). rewrite (A i) by (apply Pos.ltb_lt; exact Hb). tauto.
Qed.

Fixpoint sprop_eqb (p q : sprop) : bool :=
  match p, q with
  | SPBranch c1 a1 b1, SPBranch c2 a2 b2 =>
      if branch_cond_eq_dec c1 c2 then sv_eqb a1 a2 && sv_eqb b1 b2 else false
  | SPNot p, SPNot q => sprop_eqb p q
  | SPUlt a1 b1, SPUlt a2 b2 => sv_eqb a1 a2 && sv_eqb b1 b2
  | SPUle a1 b1, SPUle a2 b2 => sv_eqb a1 a2 && sv_eqb b1 b2
  | SPEq a1 b1, SPEq a2 b2 => sv_eqb a1 a2 && sv_eqb b1 b2
  | SPTrue, SPTrue => true
  | SPAlign i1 a1, SPAlign i2 a2 => Pos.eqb i1 i2 && Z.eqb a1 a2
  | _, _ => false
  end.

Lemma sprop_eqb_sound : ltac2:(tb__ "0|0|
S21S21S12S0S41R2R1A2S4A3S12S21R3R2A3F_;Fq;Fp;").
Proof.
  induction p; destruct q; cbn; intros H; try discriminate; try reflexivity;
  try (apply andb_prop in H as [H1 H2];
       rewrite (sv_eqb_sound _ _ H1), (sv_eqb_sound _ _ H2); reflexivity).
  - destruct (branch_cond_eq_dec c c0); [|discriminate].
    apply andb_prop in H as [H1 H2]. rewrite (sv_eqb_sound _ _ H1), (sv_eqb_sound _ _ H2). congruence.
  - rewrite (IHp _ H). reflexivity.
  - apply andb_prop in H as [H1 H2]. apply Pos.eqb_eq in H1. apply Z.eqb_eq in H2. congruence.
Qed.

Inductive tfact : Type :=
| TFle (strict : bool) (i : nat) (sx : option (bool * N)) (e : sv)
| TFge (strict : bool) (i : nat) (sx : option (bool * N)) (e : sv)
| TF2le (strict : bool) (i j : nat) (e : sv).

Definition extv (sx : option (bool * N)) (v : word) : word := ltac2:(tb__ "0|2|
S1S6S0S11A2M0A1S45Q40A1M1Lsx;Vsx;G0G0G1Lp;R1S0S11S3cR2R1Vv;A3Lw;Lsgn;X6x1Lp;Vv;X1x2").

Definition fldv (vals : list word) (i : nat) : word := nth i vals (Z_to_bv 64 0).

Definition zrel (strict : bool) (a b : Z) : Prop := ltac2:(tb__ "0|0|
S0OLstrict;Vstrict;S4bVa;Vb;A2S49Va;Vb;A2X0x2").

Definition tf_holds (rho : valuation) (vals : list word) (t : tfact) : Prop := ltac2:(tb__ "0|5|
S1bOLt;Vt;S0S3S1S6S0S11A2A1M0S1aS2dR4S46Q40M1S3dR2S28Vvals;R3A2M2A2A2M3S46G1S1cVrho;R1A2A2M4A3Le;Lsx;Li;Ls;S0S3G0S1aS2dR4G4G3A3Le;Lsx;Li;Ls;S0S3S3S1aS2dR4S4aS46G1G2A2S46G1S28Vvals;R2A2A2A2G4A3Le;Lj;Li;Ls;X1bx3").

Definition tf_expr (t : tfact) : sv :=
  match t with TFle _ _ _ e | TFge _ _ _ e | TF2le _ _ _ e => e end.

Definition tf_with_expr (t : tfact) (e : sv) : tfact := ltac2:(tb__ "0|1|
S1bS1bLt;Vt;S0S3S1S6S0S11A2A1M0S1aS3bR4R3R2Ve;A4Le0;Lsx;Li;Ls;S0S3G0S1aS3aR4R3R2Ve;A4Le0;Lsx;Li;Ls;S0S3S3S1aS39R4R3R2Ve;A4Le0;Lj;Li;Ls;X1bx3").

Definition tf_below (n : positive) (t : tfact) : bool := sv_below n (tf_expr t).

Lemma tf_holds_expr : ltac2:(tb__ "0|2|
S1dS1dS5S45Q40A1M0A1S1bS12G0S1cR4S2cR1A1M1A2S1cR3G1A2A3S18S22R5R3R2A3S22R4R3R2A3A2F_;Ft;Fvals;Frho';Frho;").
Proof. intros rho rho' vals t H. destruct t; cbn in H |- *; rewrite H; tauto. Qed.

Lemma tf_holds_agree : ltac2:(tb__ "0|0|
S10S1dS1dS5S45Q40A1A1S1bS1eR5R4R3A3S12S0S38R6R2A2S4A3S18S22R6R4R3A3S22R5R4R3A3A2F_;F_;Ft;Fvals;Frho';Frho;Fn;").
Proof. intros n rho rho' vals t Hag Hb. apply tf_holds_expr. eapply eval_agree; eauto. Qed.

Definition osxn_eqb (a b : option (bool * N)) : bool := ltac2:(tb__ "0|3|
S1S6S0S11A2M0A1M1S0La;Va;G0G0S0Lp;R1S0S11G1S0Lb;M2Vb;G0G0S0Lp0;R1S0S11S2S95R5R2A2S9eR4R1A2A2Lw2;Ls2;X6x1Lp0;ScX1x2Lw1;Ls1;X6x1Lp;G2Vb;G0ScLp;S4X1x2X1x2").

Lemma osxn_eqb_sound : ltac2:(tb__ "0|1|
S1S6S0S11A2A1M0G0S12S0S33R2R1A2S4A3S12G0R3R2A3F_;Fb;Fa;").
Proof.
  intros [[s1 w1]|] [[s2 w2]|] H; cbn in H; try discriminate; try reflexivity.
  apply andb_prop in H as [H1 H2]. apply Bool.eqb_prop in H1. apply N.eqb_eq in H2. congruence.
Qed.

Definition tf_eqb_with (eqe : sv -> sv -> bool) (t u : tfact) : bool := ltac2:(tb__ "0|8|
S1bS0Lt;Vt;S0S3S1S6S0S11A2A1M0S1aS1bS0Lu;M1Vu;S0S3G0S1aS2S2S2S95R8R4A2S91R7R3A2A2M2S33R6R2A2A2Veqe;R5R1A2M3A2Le2;Lx2;Li2;Ls2;M4S0S3G0S1aScLe;M5Lsx;Li;Lstrict;M6S0S3S3G5Lj;Li;Lstrict;M7X1bx3Le1;Lx1;Li1;Ls1;S0S3G0S1aG1Vu;G6G4G7X1bx3Le1;Lx1;Li1;Ls1;S0S3S3S1aG1Vu;G6G6S0S3S3S1aS2S2G2S91R6R2A2A2G3A2Le2;Lj2;Li2;Ls2;X1bx3Le1;Lj1;Li1;Ls1;X1bx3").

Lemma tf_eqb_with_sound : ltac2:(tb__ "0|1|
S1aS1aS0F_;F_;S1bS1bS12S0S43R3R2R1A3S4A3S13S12S0R4S2cR3A1S2cR2A1M0A2S4A3S12S1bR2S44R3G0A2A3A2F_;Fu;Ft;Feqe;").
Proof.
  intros eqe t u H. destruct t, u; cbn in H |- *; try discriminate;
    repeat (apply andb_prop in H; destruct H as [H ?]);
    apply Bool.eqb_prop in H; apply Nat.eqb_eq in H2; subst.
  - apply osxn_eqb_sound in H1. subst. auto.
  - apply osxn_eqb_sound in H1. subst. auto.
  - apply Nat.eqb_eq in H1. subst. auto.
Qed.

Definition tf_eqb (t u : tfact) : bool := tf_eqb_with sv_eqb t u.

Lemma tf_eqb_sound : ltac2:(tb__ "0|0|
S1bS1bS12S0S42R2R1A2S4A3S12S1bR3R2A3F_;Fu;Ft;").
Proof.
  intros t u H. destruct (tf_eqb_with_sound sv_eqb t u H) as [E ->].
  apply sv_eqb_sound in E. rewrite <- E. destruct t; reflexivity.
Qed.

Inductive odefault : Type :=
| DUnknown
| DZero
| DImage
| DList (l : positive)

| DRom (l : positive)

| DArr (esz : Z) (cnt : sv) (flds : list (Z * Z)) (tmpl : list tfact).

Definition soff (rho : valuation) (e : sv) : Z := bv_signed (eval rho e).

Record cell := mkCell { c_off : sv; c_width : Z; c_val : sv }.

Record sobj := mkObj {
  ob_base  : sv;
  ob_lo    : sv;
  ob_hi    : sv;
  ob_cells : list cell;
  ob_dflt  : odefault
}.

Definition oaddr (rho : valuation) (base : sv) (off : Z) : word := ltac2:(tb__ "0|1|
S47Q40M0S4aS46G0S1cVrho;Vbase;A2A2Voff;A2A2").

Definition enc_bytes (k : nat) (v : word) : list byte := Z_to_le_bytes k (bv_unsigned v).

Section WithSegs.
Variable segs : list Segment.

Definition rd (ms : machine_state) (a : word) : option byte := ms_read_byte ms a.

Fixpoint rd_bytes (ms : machine_state) (a : word) (k : nat) : option (list byte) :=
  match k with
  | O => Some []
  | S k' => match rd ms a, rd_bytes ms (a + 1)%bv k' with
            | Some b, Some bs => Some (b :: bs)
            | _, _ => None
            end
  end.

Definition cell_holds (rho : valuation) (base : sv) (lo hi : Z) (ms : machine_state) (c : cell) : Prop := ltac2:(tb__ "0|4|
S13S49Vlo;S35Vrho;S25Vc;A1A2M0A2S13S49S4aG0S26Vc;A1M1A2Vhi;A2S12S1S5S45Q8A1A1M2A1S6cVms;S3eVrho;Vbase;G0A3S4cG1A1M3A3S7G2S30G3S1cVrho;S2fVc;A1A2A2A2A3A2A2").

Definition in_cell (rho : valuation) (off : Z) (c : cell) : Prop := ltac2:(tb__ "0|1|
S13S49S35Vrho;S25Vc;A1A2M0Voff;A2S4bVoff;S4aG0S26Vc;A1A2A2A2").

Definition covered (rho : valuation) (cells : list cell) (off : Z) : Prop := ltac2:(tb__ "0|0|
S5aS27S7fVrho;Voff;A2Vcells;A3").

Definition image_byte (a : word) : option byte := ltac2:(tb__ "0|4|
S1S5S45Q8A1M0A1M1A1S1G0A1M2Lx;S5fVsegs;Va;Q1A3G1G1G2Ll;R1S9G0A1M3G0G1S7G0R2A2Ll0;Lb;X5x2Ll;G3X1x2").

Definition dflt_holds (rho : valuation) (d : odefault) (lo off : Z) (ms : machine_state) (a : word) : Prop := ltac2:(tb__ "0|8|
S20OLd;Vd;S17S45Q8M0A1M1G1S12S1G1A1M2S87Vms;Va;A2M3S7G1R1A2M4A3Lb;A2M5S12G2G3S7G1S47G0Z0A2M6A2A3S13S12G2S5cVms;Va;A2S9G1A1A3S17G1G1S12G2S69Va;A1G4A3Lb;A2A2S10S12G2G3S7G1S56G1S4cS4fVoff;Vlo;A2A1S23Vrho;R1A2G6A4A2A3Ll;M7G7SfS1aS5S6SfSfA2A1S5S1bA1G5Ltmpl;Lflds;Lcnt;Lesz;X20x6").

Definition fld_ok (esz : Z) (f : Z * Z) : Prop := ltac2:(tb__ "0|2|
S13S49Z0SaSfSfVf;A3M0A2S13S49S4aG0S8SfSfVf;A3M1A2Vesz;A2S14S12SfG1Z1A3S14S12SfG1Z2A3S14S12SfG1Z4A3S12SfG1Z8A3A2A2A2A2A2").

Definition elem_holds (rho : valuation) (ms : machine_state) (a0 : Z) (flds : list (Z * Z)) (tmpl : list tfact) : Prop := ltac2:(tb__ "0|8|
S17S5S45Q40M0A1M1A1M2G2S13S12S3SbG1R1A2SbS6SfSfA2M3Vflds;A2A3S13S3G3S12S1G3A1S5bG3Vflds;R2A3S7G3R1A2A3S13S12S1S5S45Q8A1A1M4A1S6cVms;S47G0S4aVa0;SaSfSfR2A3A2A2S4cS8SfSfR2A3M5A1M6A3S7G4S30G6S28R4R3A2M7A2A2A3S4bS46G0G7A2S4dZ2S4eZ8G5A2A2A2A2F_;Ff;Fi;S55S1bS22Vrho;R1A2Vtmpl;A3A2A2Lvals;A2").

Definition dflt_inv (rho : valuation) (d : odefault) (b lo hi : Z) (ms : machine_state) : Prop := ltac2:(tb__ "0|4|
S20OLd;Vd;S15S15S15S10S12SfS54SbS45Q8A1S23Vrho;R1A2A2A1S4fVhi;Vlo;A2A3Ll;M0G0SfS1aS5S6SfSfA2M1A1S5S1bA1S13S4bZ0M2R4A2S13S55G1S7cR4A1R2A3S13S49S4aVlo;S4eR4S46Q40M3S1cVrho;R3A2A2A2A2Vhi;A2SfS13S49G2R1A2S4bR1S46G3S1cVrho;R4A2A2A2A2S7aVrho;Vms;S4aS4aVb;Vlo;A2S4eR6R2A2A2R4R3A5F_;Fk;A2A2A2Ltmpl;Lflds;Lcnt;Lesz;X20x6").

Definition dflt_writable (d : odefault) : bool :=
  match d with DRom _ => false | _ => true end.

Definition is_arr (d : odefault) : bool :=
  match d with DArr _ _ _ _ => true | _ => false end.

Definition obj_lo_of (rho : valuation) (o : sobj) : Z := soff rho (ob_lo o).
Definition obj_hi_of (rho : valuation) (o : sobj) : Z := soff rho (ob_hi o).

Definition obj_holds (rho : valuation) (ms : machine_state) (o : sobj) : Prop := ltac2:(tb__ "0|8|
S46Q40M0S1cVrho;S2aVo;A1M1A2A2SfS6bVrho;Vo;A2SfS6aVrho;Vo;A2SfS13S13S49Z0S4aR3R2A2A2S13S49S4aR3R1A2S4dZ2M2Z40A2A2S13S49R2R1A2S4bS4fR1R2A2S4dG2Z3fA2A2A2A2A2S13SfS13S49R3R1A2S4bR1R2A2A2M3S12S0S79S32Vo;A1M4A1S4A3S16S12S1S45Q8A1M5A1S67Vsegs;S5cVms;A1S47G0S4aR6R3A2A2M6A3S9G5A1A3A1F_;F_;Foff;S13S55S27S73Vrho;G1R2R1Vms;A5S31Vo;A1M7A3S13SfG3S16S75Vrho;G7R2A3A1S76Vrho;G4R5R3Vms;G6A6F_;F_;Foff;S77Vrho;G4R3R2R1Vms;A6A2A2A2A2Thi;Tlo;Tb;").

Definition obj_range (rho : valuation) (o : sobj) : Z * Z := ltac2:(tb__ "0|0|
S46Q40S1cVrho;S2aVo;A1A2A2SfSeSfSfS4aR1S6bVrho;Vo;A2A2S4aR1S6aVrho;Vo;A2A2A4Tb;").

Definition ranges_disjoint (r1 r2 : Z * Z) : Prop := ltac2:(tb__ "0|4|
S14S49S8SfSfVr1;A3M0SaSfSfVr1;A3M1A2S14S49S8SfSfVr2;A3M2SaSfSfVr2;A3M3A2S14S49G0G3A2S49G2G1A2A2A2A2").

Fixpoint pairwise_disjoint (rho : valuation) (objs : list sobj) : Prop :=
  match objs with
  | [] => True
  | o :: rest => Forall (fun o' => ranges_disjoint (obj_range rho o) (obj_range rho o')) rest
                 /\ pairwise_disjoint rho rest
  end.

Inductive sfcsr : Type :=
| FcsrFrm0
| FcsrVal (v : sv).

Record sstate := mkSS {
  ss_pc    : Z;
  ss_regs  : list sv;
  ss_fregs : list sv;
  ss_fcsr  : sfcsr;
  ss_resv  : option sv;
  ss_objs  : list sobj;
  ss_facts : list sprop;
  ss_next  : positive;
  ss_lenient : bool
}.

Definition reg_sv (S : sstate) (r : Z) : sv := ltac2:(tb__ "0|2|
S0S1aL_;S50Vr;Z0M0A2S2eG0A1M1S56S1aS4cVr;A1S71VS;A1G1A4X0x2").

Definition freg_sv (S : sstate) (r : Z) : sv := ltac2:(tb__ "0|0|
S56S1aS4cVr;A1S6fVS;A1S2eZ0A1A4").

Definition regs_match (rho : valuation) (S : sstate) (ms : machine_state) : Prop := ltac2:(tb__ "0|1|
S45Q5M0A1S16S12SfS46G0R1A2Z0A3A1S12S45Q40A1S94S63Vms;A1R2A2S1cVrho;S88VS;S46G0R2A2A2A2A3F_;Fr;").

Definition fregs_match (rho : valuation) (S : sstate) (ms : machine_state) : Prop := ltac2:(tb__ "0|1|
S45Q5M0A1S12S45Q40A1S94S61Vms;A1R1A2S1cVrho;S7dVS;S46G0R1A2A2A2A3Fr;").

Definition fcsr_match (rho : valuation) (f : sfcsr) (ms : machine_state) : Prop := ltac2:(tb__ "0|2|
S68OLf;Vf;S4bS46Q20S60Vms;A1A2M0Z20M1A2S1aS12SfG0S53S46Q40S1cVrho;R1A2A2S4dZ2G1A2A2A3Lv;X68x2").

Definition resv_match (rho : valuation) (r : option sv) (ms : machine_state) : Prop := ltac2:(tb__ "0|4|
S1S1aA1OLr;Vr;S1aS1S45Q40M0A1M1A1OLx;M2S64Vms;A1M3G1S12SfS46G0R1A2S46G0S1cVrho;R2A2A2A3La;S19X1x2Le;G2G3G1S19Lb;S15X1x2X1x2").

Definition outside_all (rho : valuation) (objs : list sobj) (a : word) : Prop := ltac2:(tb__ "0|1|
S55S24S24S83Vrho;R1A2S6SfSfA2S16S13S49SaSfSfR1A3S46Q40Va;A2M0A2S4bG0S8SfSfR1A3A2A2A1Tr;Lo;Vobjs;A3").

Definition mem_frame (rho : valuation) (objs : list sobj) (ms : machine_state) : Prop := ltac2:(tb__ "0|0|
S45Q40A1S85Vrho;Vobjs;R1A3S12S1S45Q8A1A1S5cVms;R2A2S2bVrho;R2A2A3F_;Fa;").

Definition mem_match (rho : valuation) (objs : list sobj) (ms : machine_state) : Prop := ltac2:(tb__ "0|0|
S13S55S24S82Vrho;Vms;A2Vobjs;A3S13S86Vrho;Vobjs;A2S80Vrho;Vobjs;Vms;A3A2A2").

Definition rom_ok (ms : machine_state) : Prop := ltac2:(tb__ "0|0|
S45Q40A1S12S1S45Q8A1A1S65Vms;R1A2S69R1A1A3Fa;").

Definition ro_addr (a : word) : bool := ltac2:(tb__ "0|0|
S1S92A1S0Lx;S5dVsegs;S46Q40Va;A2Z1A3S92SdS93R1A1A1Lseg;ScX1x2").

Definition ro_clear (ms : machine_state) : Prop := ltac2:(tb__ "0|1|
S45Q40A1S12S0S8bR1A1S4A3S12S1S45Q8A1M0A1S5cVms;R2A2S9G0A1A3F_;Fa;").

Definition cell_wf (n : positive) (c : cell) : bool := ltac2:(tb__ "0|1|
S2S2S2S52Z0S26Vc;A1M0A2S51G0Z8A2A2S1fVn;S25Vc;A1A2A2S1fVn;S2fVc;A1A2A2").

Definition dflt_wf (n : positive) (d : odefault) : bool := ltac2:(tb__ "0|1|
S20S0Ld;Vd;S4S4S4S10S4Ll;M0G0SfS1aS5S6SfSfA2A1S5S1bA1S2S1fVn;R3A2S59S1bS38Vn;A1R1A3A2Ltmpl;Lflds;Lcnt;Lesz;X20x6").

Definition obj_wf (n : positive) (o : sobj) : bool := ltac2:(tb__ "0|0|
S2S2S2S2S1fVn;S2aVo;A1A2S1fVn;S40Vo;A1A2A2S1fVn;S3fVo;A1A2A2S59S27S74Vn;A1S31Vo;A1A3A2S78Vn;S32Vo;A1A2A2").

Definition swf (S : sstate) : bool := ltac2:(tb__ "0|6|
S2S2S2S2S2S2S2S91SbS1aS71VS;A1M0A2U20M1A2S91SbS1aS6fVS;A1M2A2G1A2A2S59S1aS1fS8eVS;A1M3A1M4G0A3A2S59S1aG4G2A3A2S68S0Lx;S6eVS;A1S4S1aS1fG3R1A2Lv;M5X68x2A2S1S1aA1S0Lx;S72VS;A1G5S4X1x2A2S59S24S84G3A1S70VS;A1A3A2S59S21S36G3A1S6dVS;A1A3A2").

Definition smatch (rho : valuation) (S : sstate) (w : list event * config) : Prop := ltac2:(tb__ "0|3|
S97S8S5S9aA1S98Vw;A3M0A1S5eS96G0A1S99S13S12S0S90VS;A1S4A3S13S12S45Q40M1A1M2S62R2A1S47G1S8fVS;A1A2A3S13S12S1G2A1S66R2A1S9G2A1A3S13S9dR1A1S13S8dR2A1S13S8cR2A1S13S89Vrho;VS;R2A3S13S7eVrho;VS;R2A3S13S7bVrho;S6eVS;A1R2A3S13S8aVrho;S72VS;A1R2A3S13S81Vrho;S70VS;A1R2A3S55S21S29Vrho;A1S6dVS;A1A3A2A2A2A2A2A2A2A2A2A2A2Tmd;Tms;").

End WithSegs.
