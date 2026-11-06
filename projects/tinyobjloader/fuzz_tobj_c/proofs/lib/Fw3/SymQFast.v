(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Datatypes"; "bool"; "prod"; "option"; "andb"; "false"; "list"; "true"; "pair"; "nil"; "None"; "Some"; "fst"; "nat"; "snd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sprop"; "sobj"; "@Stdlib.ZArith.BinInt.Z"; "leb"; "add"; "sub"; "ltb"; "min"; "pow"; "@Corelib.Init.Logic"; "eq"; "and"; "ex"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "fdig"; "dg_facts"; "DFalse"; "DTrue"; "decision"; "itv_t"; "same_atoms"; "DUnknown_"; "smax"; "smin"; "wnorm_t"; "atoms_of"; "sitv_d"; "uleq_d"; "M64"; "align_sum"; "dg_urels"; "in_bounds_d"; "itv_sum"; "sleq_d"; "snorm"; "strip_zext"; "uleq_by_rel2"; "ctx0"; "decide_t"; "dg_srels"; "find_obj_d"; "itv_decide_t"; "itv_lin"; "mk_ctx"; "mk_dig"; "prover_decide"; "remove_atoms"; "remu_lt"; "sel_case"; "shr_mono"; "sitv_of"; "sleq_lin"; "tbl_init"; "uleq_by_rel"; "uleq_core"; "uleq_lin"; "uleq_same"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymQFast"; "urel"; "upre"; "u2memo"; "uleq_d_q"; "mk_u2"; "ib_core"; "sitv_d_q"; "sleq_d_q"; "u2_ok"; "uleq_by_rel2_p"; "uleq_core_q"; "upre_of"; "prover_decide_q"; "sleq_by_rel_q"; "sleq_same_q"; "aligned_tighten_q"; "decide_t_q"; "find_obj_d_m"; "ib_cheap"; "in_bounds_d_q"; "sleq_by_rel_q0"; "sleq_same_q0"; "uleq_d_o"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymDigFast"; "stv_t_x"; "sf_ok"; "snorm_h"; "@Stdlib.Lists.List"; "existsb"; "@LinuxProcessSemantics.Riscv.Instr"; "branch_cond"; "@Corelib.Lists.ListDef"; "map"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool.
From Stdlib Require Import PArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymDigFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition urel : Type := ltac2:(tb__ "0|0|
S2S2SfS0A2SfA2").

Definition upre : Type := ltac2:(tb__ "0|1|
S2S2S2S6SfA1S0A2S2S0S0A2M0A2G0A2").

Definition upre_of (dg : fdig) (r : urel) : upre := ltac2:(tb__ "0|4|
S2S2SfS0A2M0SfA2S48Lr;Vr;G0SfG0S48Lp;R2SfS0S27R2S9SfA1Z0A3S2S6SfA1M1S0A2M2S8S2G2S2S0S0A2M3A2G3S8G2G3R1S2eVdg;ScG1S0R1A3A2A4S21Vdg;R4A2A4Txa;Ld;Lx;X2x1Ly;Lp;X2x1").

Definition u2memo : Type := list (upre * urel).
Definition mk_u2 (dg : fdig) : u2memo := ltac2:(tb__ "0|0|
S63S47S2S48S47A2S47S8S48S47S52Vdg;R1A2R1A4Lr;S2cVdg;A1A4").

Definition uleq_by_rel2_p (dg : fdig) (pa : list sv * Z) (ia ib : Z * Z) (k : Z) (b : sv) (pr : upre * urel) : bool := ltac2:(tb__ "0|7|
S2S48S47A2S1Lpr;Vpr;S48S47S2S2SfS0A2M0SfA2S1Lr;R1G0SfG0S1Lp0;R2SfS0S2S2S2S6SfA1M1S0A2M2S2S0S0A2M3A2M4G3A2S1Lp;R6G4G3G4S1Lp0;R2G2G3G2S1Lpa;Vpa;G1S0G2S1Lxa_cx;R4G1S0S3G1A1S1Lx;S3cR4R2A2G1S14R4R2A2S0G3S1Lia;Via;S0S0G3S1Lx;G1G3Laa;R8R9SfG1S2eVdg;R6A2Ll;Ls;X6x2S0S0G3S1Liy;RdS0S0S1S1L_;S4S4S4S4S12R6R5A2S12R4R3A2A2S12Z0M5S14S13R6R4A2R7A2A2A2S15S14S13R5R3A2R7A2S2aA2A2S12R2R1A2M6A2S3S0A1S1Lx;S22Vb;R13A2S0S4S4S12G5S13R3R1A2A2S15S13R2R1A2S2aA2A2S12S13S14R8R5A2Vk;A2S13R1R12A2A2A2Ldb;G3S1Lib;Vib;S0S0S4G6S12S13S14S13S14R3R13A2R9A2R6A2Vk;A2R2A2A2Lhb;Llb;X2x1X3x2S5X1x2Lhy;Lly;X2x1Leh;Lel;X2x1Lha;Lla;X2x1Tda;Lextra;S5X3x2Lcx;Lxa;X2x1Lca;Laa;X2x1Lsumx;Lxa_cx;X2x1Liy;Lp0;X2x1Ld;Lx;X2x1Ly;Lp0;X2x1Lr;Lp;X2x1").

Lemma lazy_andb_eq : ltac2:(tb__ "0|0|
S1S1S18S1S1S1L_;R2R1S5X1x2S4R2R1A2A3Fb;Fa;").
Proof. intros [|] b; reflexivity. Qed.

Lemma uleq_by_rel2_p_eq : ltac2:(tb__ "0|0|
S1cSfS0SfS47S18S1S50R5S27R4S9SfA1Z0A3S21R5R4A2S21R5R2A2R3R2S8S48S47S52R5R1A2R1A4A7S32R5R4R3R2R1A5A3Fr;Fb;Fk;Fa;Fdg;").
Proof.
  intros dg a k b [[x d] y]. unfold uleq_by_rel2_p, uleq_by_rel2, upre_of, sub_atoms. cbv zeta.
  destruct (atoms_of a [] 0) as [aa ca]. destruct (atoms_of x [] 0) as [xa cx]. cbn [fst snd].
  destruct aa as [|a0 aa'].
  - cbn [remove_atoms]. destruct (itv_t dg a) as [la ha]. destruct (itv_sum dg xa) as [el eh].
    destruct (itv_t dg y) as [ly hy]. apply lazy_andb_eq.
  - destruct (remove_atoms (a0 :: aa') xa) as [extra|]; [|reflexivity].
    destruct (itv_t dg a) as [la ha]. destruct (itv_sum dg extra) as [el eh].
    destruct (itv_t dg y) as [ly hy]. apply lazy_andb_eq.
Qed.

Lemma existsb_u2 : ltac2:(tb__ "0|1|
S1cSfS0SfS6S47A1S18S1S61S2S48S47A2M0S50R5S27R4S9SfA1Z0A3S21R5R4A2S21R5R2A2R3R2A6S63S47G0S47S8S48S47S52R6R1A2R1A4Lr;R1A4A3S61S2S2SfS0A2SfA2S32R5R4R3R2A4R1A3A3Frels;Fb;Fk;Fa;Fdg;").
Proof.
  intros dg a k b rels. induction rels as [|r t IH]; [reflexivity|].
  cbn [map existsb]. rewrite uleq_by_rel2_p_eq, IH. reflexivity.
Qed.

Definition uleq_core_q (u2 : u2memo) (dg : fdig) (a : sv) (k : Z) (b : sv) : bool := ltac2:(tb__ "0|2|
S21Vdg;Va;A2S2S0S0A2M0S21Vdg;Vb;A2G0G0S1Lia;R2S0S0G0S1Lib;R3S0S0S1S1L_;M1S4S4S12R4R3A2S12R2R1A2A2S12S13R3Vk;A2R2A2A2S7G1S46Vdg;Va;Vk;Vb;A4S7G1S45Vdg;Va;Vk;Vb;A4S7G1S61S2S2SfS0A2SfA2S43Vdg;Va;Vk;Vb;A4S2cVdg;A1A3S7G1S61S2S48S47A2S50Vdg;S27Va;S9SfA1Z0A3R6R5Vk;Vb;A6Vu2;A3S7G1S12Vk;Z1A2S3dVdg;S31Vdg;Va;A2Vb;A3S5X1x2X1x2X1x2X1x2X1x2X1x2Lhb;Llb;X2x1Lha;Lla;X2x1Tib;Tia;").

Lemma uleq_core_q_eq : ltac2:(tb__ "0|0|
S1cSfS0SfS18S1S51S4bR4A1R4R3R2R1A5S44R4R3R2R1A4A3Fb;Fk;Fa;Fdg;").
Proof.
  intros dg a k b. unfold uleq_core_q, uleq_core, mk_u2. cbv zeta.
  rewrite existsb_u2. destruct (itv_t dg a) as [la ha]. destruct (itv_t dg b) as [lb hb]. reflexivity.
Qed.

Definition aligned_tighten_q (u2 : u2memo) (dg : fdig) (a : sv) (k : Z) (b : sv) : bool := ltac2:(tb__ "0|3|
S16S2bS1dVdg;A1M0Va;A2S2bG0Vb;A2A2S0S1S1L_;M1S12Z1M2R1A2G1S12Vk;S17Z2R1A2A2S51Vu2;Vdg;Va;G2Vb;A5S5X1x2S5X1x2Tj;").

Definition uleq_d_q (u2 : u2memo) (dg : fdig) (a : sv) (k : Z) (b : sv) : bool := ltac2:(tb__ "0|1|
S31Vdg;Va;A2SfS1S1L_;M0S51Vu2;Vdg;R1Vk;Vb;A5S7G0S3fVdg;R1Vk;Vb;A4S7G0S3eVdg;R1Vk;Vb;A4S7S56Vu2;Vdg;R1Vk;Vb;A5X1x2X1x2X1x2Ta;").

Lemma uleq_d_q_eq : ltac2:(tb__ "0|0|
S1cSfS0SfS18S1S4aS4bR4A1R4R3R2R1A5S29R4R3R2R1A4A3Fb;Fk;Fa;Fdg;").
Proof.
  intros dg a k b. unfold uleq_d_q, uleq_d, aligned_tighten_q, aligned_tighten. cbv zeta.
  rewrite !uleq_core_q_eq. reflexivity.
Qed.

Definition sleq_same_q (sf : list sprop) (dg : fdig) (a : sv) (k : Z) (b : sv) : bool := ltac2:(tb__ "0|0|
S3S0A1S1Lx;S22Va;Vb;A2S0S60R1A1S0S2S0S0A2S1Lx;S5eVsf;Vdg;Vb;A3S0S0S4S4S4S12R2R1A2S12S25S13R2R3A2A2A2S12S13R1R3A2S24A2A2S12S13R3Vk;A2Z0A2A2Lhb;Llb;X2x1Td;Ld0;S5X3x2").

Definition sleq_by_rel_q (sf : list sprop) (dg : fdig) (a : sv) (k : Z) (b : sv) (r : sv * Z * sv) : bool := ltac2:(tb__ "0|4|
S2S2SfS0A2M0SfA2S1Lr;Vr;G0SfG0S1Lp;R2SfS0S26Vdg;R2A2SfS26Vdg;R4A2SfS3S0A1S1Lx;M1S22Va;R2A2S0G1S22Vb;R2A2S0S60R2A1M2S0G2S0S2S0S0A2S1Lx;M3S5eVsf;Vdg;R6A3S0S0G3S5eVsf;Vdg;R7A3S0S0S4S4S4S4S4S4S12R4R3A2S12R2R1A2A2S12S25S13R4R6A2A2A2S12S13R3R6A2S24A2A2S12S25S13R2R5A2A2A2S12S13R1R5A2S24A2A2S12S13R6Vk;A2S13R5RbA2A2A2Lhy;Lly;X2x1Lhx;Llx;X2x1Tdb;Tda;Ldb0;S5X3x2Lda0;S5X3x2Ty;Tx;Ld;Lx;X2x1Ly;Lp;X2x1").

Definition sleq_same_q0 (sf : list sprop) (dg : fdig) (a : sv) (k : Z) (b : sv) : bool := ltac2:(tb__ "0|0|
S3S0A1S1Lx;S22Va;Vb;A2S0S30R1A1S0S2S0S0A2S1Lx;S5eVsf;Vdg;Vb;A3S0S0S4S4S4S12R2R1A2S12S25S13R2R3A2A2A2S12S13R1R3A2S24A2A2S12S13R3Vk;A2Z0A2A2Lhb;Llb;X2x1Td;Ld0;S5X3x2").
Lemma sleq_same_q_eq0 : ltac2:(tb__ "0|0|
S6S10A1S1cSfS0SfS18S1S55R5R4R3R2R1A5S5cR5R4R3R2R1A5A3Fb;Fk;Fa;Fdg;Fsf;").
Proof. intros. unfold sleq_same_q, sleq_same_q0. destruct (same_atoms a b); [rewrite snorm_h_eq|]; reflexivity. Qed.
Definition sleq_by_rel_q0 (sf : list sprop) (dg : fdig) (a : sv) (k : Z) (b : sv) (r : sv * Z * sv) : bool := ltac2:(tb__ "0|4|
S2S2SfS0A2M0SfA2S1Lr;Vr;G0SfG0S1Lp;R2SfS0S26Vdg;R2A2SfS26Vdg;R4A2SfS3S0A1S1Lx;M1S22Va;R2A2S0G1S22Vb;R2A2S0S30R2A1M2S0G2S0S2S0S0A2S1Lx;M3S5eVsf;Vdg;R6A3S0S0G3S5eVsf;Vdg;R7A3S0S0S4S4S4S4S4S4S12R4R3A2S12R2R1A2A2S12S25S13R4R6A2A2A2S12S13R3R6A2S24A2A2S12S25S13R2R5A2A2A2S12S13R1R5A2S24A2A2S12S13R6Vk;A2S13R5RbA2A2A2Lhy;Lly;X2x1Lhx;Llx;X2x1Tdb;Tda;Ldb0;S5X3x2Lda0;S5X3x2Ty;Tx;Ld;Lx;X2x1Ly;Lp;X2x1").
Lemma sleq_by_rel_q_eq0 : ltac2:(tb__ "0|0|
S6S10A1S1cSfS0SfS2S2SfS0A2SfA2S18S1S54R6R5R4R3R2R1A6S5bR6R5R4R3R2R1A6A3Fr;Fb;Fk;Fa;Fdg;Fsf;").
Proof.
  intros sf dg a k b [[x d] y]. unfold sleq_by_rel_q, sleq_by_rel_q0.
  destruct (same_atoms a (wnorm_t dg x)); [|reflexivity]. destruct (same_atoms b (wnorm_t dg y)); [|reflexivity].
  rewrite !snorm_h_eq. reflexivity.
Qed.

Definition sleq_d_q (sf : list sprop) (dg : fdig) (a0 : sv) (k : Z) (b0 : sv) : bool := ltac2:(tb__ "0|2|
S26Vdg;Va0;A2SfS26Vdg;Vb0;A2SfS2S0S0A2S1Lx;M0S5eVsf;Vdg;R2A3S0S0G0S5eVsf;Vdg;R3A3S0S0S1S1L_;M1S4S4S12R4R3A2S12R2R1A2A2S12S13R3Vk;A2R2A2A2S7G1S55Vsf;Vdg;R6Vk;R5A5S7G1S41Vdg;Va0;Vk;Vb0;A4S7S61S2S2SfS0A2SfA2S54Vsf;Vdg;R6Vk;R5A5S35Vdg;A1A3X1x2X1x2X1x2Lhb;Llb;X2x1Lha;Lla;X2x1Tb;Ta;").

Lemma existsb_ext_eq : forall {A} (f g : A -> bool) (l : list A),
  (forall x, f x = g x) -> existsb f l = existsb g l.
Proof.
  intros A f g l H. induction l as [|x t IH]; cbn [existsb]; [reflexivity|]. rewrite (H x), IH. reflexivity.
Qed.

Lemma sleq_d_q_eq : ltac2:(tb__ "0|0|
S6S10A1S1cSfS0SfS5fR5S1dR4A1A2S18S1S4eR6R5R4R3R2A5S2fR5R4R3R2A4A3F_;Fb;Fk;Fa;Fdg;Fsf;").
Proof.
  intros sf dg a k b H. unfold sleq_d_q. cbv zeta. rewrite sleq_same_q_eq0.
  rewrite (existsb_ext_eq (sleq_by_rel_q sf dg (wnorm_t dg a) k (wnorm_t dg b)) (sleq_by_rel_q0 sf dg (wnorm_t dg a) k (wnorm_t dg b))) by apply sleq_by_rel_q_eq0.
  unfold sleq_d, sleq_same_q0, sleq_same. cbv zeta.
  rewrite !(stv_t_x_eq sf dg _ H).
  rewrite (existsb_ext_eq (sleq_by_rel_q0 sf dg (wnorm_t dg a) k (wnorm_t dg b))
                          (sleq_by_rel dg (wnorm_t dg a) k (wnorm_t dg b))); [reflexivity|].
  intros [[x d] y]. unfold sleq_by_rel_q0, sleq_by_rel. cbv zeta. rewrite !(stv_t_x_eq sf dg _ H). reflexivity.
Qed.

Definition sitv_d_q (sf : list sprop) (dg : fdig) (e : sv) : option (Z * Z) := ltac2:(tb__ "0|3|
S3S2S0S0A2M0A1M1G1Lx;S40S38Vdg;Ve;A2A1G0SbG0R1A2M2Lp;S5eVsf;Vdg;Ve;A3G0S1G1L_;S12ScS0S0R1A3SeS0S0R1A3A2G2SaG0A1X1x2Tp;X3x2").

Lemma sitv_d_q_eq : ltac2:(tb__ "0|0|
S6S10A1S1cSfS5fR3S1dR2A1A2S18S3S2S0S0A2A1S4dR4R3R2A3S28R3R2A2A3F_;Fe;Fdg;Fsf;").
Proof. intros sf dg e H. unfold sitv_d_q, sitv_d. rewrite (stv_t_x_eq sf dg _ H). reflexivity. Qed.

Definition ib_core (uq sq : sv -> Z -> sv -> bool) (s1 s2 s3 : option (Z * Z)) (lo hi off : sv) (k : Z) : bool := ltac2:(tb__ "0|5|
S3S2S0S0A2M0A1M1S1Ls1;Vs1;G0G0S1Lp;R1S0S0G1S1Ls2;Vs2;G0G0S1Lp0;R1S0S0G1S1Ls3;Vs3;G0G0S1Lp1;R1S0S0S1S1L_;M2G2S12R7R2A2S7G2G2S4S12Z0M3R8A2S12G3R2A2M4A2Vuq;Vlo;G3Voff;A3S5X1x2S7Vsq;Vlo;G3Voff;A3X1x2X1x2G2S12S13R1Vk;A2R5A2S7G2G2S4G4S12G3R5A2A2Vuq;Voff;Vk;Vhi;A3S5X1x2S7Vsq;Voff;Vk;Vhi;A3X1x2X1x2S5X1x2Lh3;Ll3;X2x1Lp1;S5X3x2Lh2;Ll2;X2x1Lp0;S5X3x2Lh1;Ll1;X2x1Lp;S5X3x2").

Definition ib_cheap (s1 s2 s3 : option (Z * Z)) (k : Z) : bool := ltac2:(tb__ "0|2|
S3S2S0S0A2M0A1M1S1Ls1;Vs1;G0G0S1Lp;R1S0S0G1S1Ls2;Vs2;G0G0S1Lp0;R1S0S0G1S1Ls3;Vs3;G0G0S1Lp1;R1S0S0S1S1L_;S12R7R2A2S12S13R1Vk;A2R5A2S5X1x2Lh3;Ll3;X2x1Lp1;S5X3x2Lh2;Ll2;X2x1Lp0;S5X3x2Lh1;Ll1;X2x1Lp;S5X3x2").

Lemma ib_cheap_core : ltac2:(tb__ "0|2|
SfS0SfS1F_;F_;F_;M0G0S3S2S0S0A2A1M1G1G1SfSfSfS0S18S1S59R7R6R5R1A4S7A3S18S1S4cRaR9R8R7R6R5R4R3R2A9S7A3F_;Fk;Foff;Fhi;Flo;Fs3;Fs2;Fs1;Fsq;Fuq;").
Proof.
  intros uq sq [[l1 h1]|] [[l2 h2]|] [[l3 h3]|] lo hi off k; cbn [ib_cheap ib_core]; try discriminate.
  destruct (h1 <=? l3); [|discriminate]. intros ->. reflexivity.
Qed.

Lemma in_bounds_d_core : ltac2:(tb__ "0|0|
S1cSfSfSfS0S18S1S2dR5R4R3R2R1A5S4cS29R5A1S2fR5A1S28R5R4A2S28R5R3A2S28R5R2A2R4R3R2R1A9A3Fk;Foff;Fhi;Flo;Fdg;").
Proof. intros. reflexivity. Qed.

Definition in_bounds_d_q (sf : list sprop) (u2 : u2memo) (dg : fdig) (lo hi off : sv) (k : Z) : bool := ltac2:(tb__ "0|0|
S4cS4aVu2;Vdg;A2S4eVsf;Vdg;A2S4dVsf;Vdg;Vlo;A3S4dVsf;Vdg;Vhi;A3S4dVsf;Vdg;Voff;A3Vlo;Vhi;Voff;Vk;A9").

Lemma ib_core_ext : ltac2:(tb__ "0|3|
SfS0SfS1Fx1;Fx0;Fx;M0G0G0G0S3S2S0S0A2A1M1G1G1SfSfSfS0SfS0SfS18S1ReR3R2R1A3RdR3R2R1A3M2A3Fb;Fk;Fa;SfS0SfS18S1G2RcR3R2R1A3A3Fb;Fk;Fa;S18S1S4cRdRbR9R8R7R6R5R4R3A9S4cRcRaR9R8R7R6R5R4R3A9A3F_;F_;Fk;Foff;Fhi;Flo;Fs3;Fs2;Fs1;Fsq';Fsq;Fuq';Fuq;").
Proof.
  intros uq uq' sq sq' [[l1 h1]|] [[l2 h2]|] [[l3 h3]|] lo hi off k Hu Hs; cbn [ib_core]; try reflexivity.
  rewrite !Hu, !Hs. reflexivity.
Qed.

Lemma in_bounds_d_q_eq : ltac2:(tb__ "0|0|
S6S10A1S1cSfSfSfS0S5fR6S1dR5A1A2S18S1S5aR7S4bR6A1R6R5R4R3R2A7S2dR6R5R4R3R2A5A3F_;Fk;Foff;Fhi;Flo;Fdg;Fsf;").
Proof.
  intros sf dg lo hi off k H. unfold in_bounds_d_q. rewrite in_bounds_d_core, !(sitv_d_q_eq sf dg _ H).
  apply ib_core_ext; [intros; apply uleq_d_q_eq | intros; apply sleq_d_q_eq; exact H].
Qed.

Definition prover_decide_q (sf : list sprop) (u2 : u2memo) (dg : fdig) (c : branch_cond) (a b : sv) : decision := ltac2:(tb__ "0|a|
S62S20Lc;Vc;S1S20L_;M0S1S1L_;M1S4aVu2;Vdg;Va;Z1M2Vb;A5M3S7S4aVu2;Vdg;Vb;G2Va;A5X1x2M4S1eG0G1S4aVu2;Vdg;Va;Z0M5Vb;A5S4aVu2;Vdg;Vb;G5Va;A5M6S5X1x2M7S1fS23X1x2X1x2G0G4S1fG0G7S1eS23X1x2X1x2G0S4eVsf;Vdg;Va;G2Vb;A5M8S1fG0S4eVsf;Vdg;Vb;G5Va;A5M9S1eS23X1x2X1x2G0G8S1eG0G9S1fS23X1x2X1x2G0G3S1fG0G6S1eS23X1x2X1x2G0G3S1eG0G6S1fS23X1x2X1x2X62x6").

Lemma prover_decide_q_eq : ltac2:(tb__ "0|0|
S6S10A1S1cS62SfSfS5fR5S1dR4A1A2S18S20S53R6S4bR5A1R5R4R3R2A6S3bR5R4R3R2A4A3F_;Fb;Fa;Fc;Fdg;Fsf;").
Proof.
  intros sf dg c a b H. unfold prover_decide_q, prover_decide.
  rewrite !uleq_d_q_eq, !(sleq_d_q_eq sf dg _ _ _ H). reflexivity.
Qed.

Definition decide_t_q (sf : list sprop) (u2 : u2memo) (dg : fdig) (c : branch_cond) (a b : sv) : decision := ltac2:(tb__ "0|0|
S20S20Lx;S37Vdg;Vc;Va;Vb;A4S1fS1eS53Vsf;Vu2;Vdg;Vc;Va;Vb;A6X20x3").

Lemma decide_t_q_eq : ltac2:(tb__ "0|0|
S6S10A1S1cS62SfSfS5fR5S1dR4A1A2S18S20S57R6S4bR5A1R5R4R3R2A6S34R5R4R3R2A4A3F_;Fb;Fa;Fc;Fdg;Fsf;").
Proof.
  intros sf dg c a b H. unfold decide_t_q, decide_t. rewrite (prover_decide_q_eq sf dg c a b H). reflexivity.
Qed.

Definition u2_ok (ou : option u2memo) (dg : fdig) : Prop := ltac2:(tb__ "0|1|
S1bS18S3S49A1M0Vou;SaS49A1A3S18G0Vou;SbS49S4bVdg;A1A2A3A2").

Definition uleq_d_o (ou : option u2memo) (dg : fdig) (a : sv) (k : Z) (b : sv) : bool := ltac2:(tb__ "0|0|
S3S49A1S1Lou;Vou;S49S4aR1Vdg;Va;Vk;Vb;A5Lu2;S29Vdg;Va;Vk;Vb;A4X3x2").

Lemma uleq_d_o_eq : ltac2:(tb__ "0|0|
S3S49A1S1cSfS0SfS4fR5R4A2S18S1S5dR6R5R4R3R2A5S29R5R4R3R2A4A3F_;Fb;Fk;Fa;Fdg;Fou;").
Proof. intros ou dg a k b [->| ->]; cbn [uleq_d_o]; [reflexivity | apply uleq_d_q_eq]. Qed.

Fixpoint find_obj_d_m (sf : list sprop) (ou : option u2memo) (objs : list sobj) (dg : fdig) (ae : sv) (k : Z) (n : nat)
  : option (nat * sobj * sv) * option u2memo :=
  match objs with
  | [] => (None, ou)
  | o :: rest =>
      match rel_offset (ob_base o) ae with
      | Some off =>
          let s1 := sitv_d_q sf dg (ob_lo o) in
          let s2 := sitv_d_q sf dg (ob_hi o) in
          let s3 := sitv_d_q sf dg off in
          if ib_cheap s1 s2 s3 k then (Some (n, o, off), ou)
          else
            let u2 := match ou with Some u => u | None => mk_u2 dg end in
            if ib_core (uleq_d_q u2 dg) (sleq_d_q sf dg) s1 s2 s3 (ob_lo o) (ob_hi o) off k
            then (Some (n, o, off), Some u2)
            else find_obj_d_m sf (Some u2) rest dg ae k (S n)
      | None => find_obj_d_m sf ou rest dg ae k (S n)
      end
  end.

Lemma find_obj_d_m_ok : ltac2:(tb__ "0|2|
S6S10A1S1cSfS0S5fR4S1dR3A1A2S6S11A1S3S49A1M0SdS4fR2R7A2S1aG0G0S19S18S2S3S2S2SdS11A2SfA2A1M1G0A2S58RaR4R5R9R8R7R3A7S8G1G0S36R5R9R8R7R3A5R1A4A3S4fR1R9A2A2Lou';A2F_;Fn;Fou;Fobjs;F_;Fk;Fae;Fdg;Fsf;").
Proof.
  intros sf dg ae k H. induction objs as [|o rest IH]; intros ou n Hou; cbn [find_obj_d_m find_obj_d].
  - exists ou. split; [reflexivity | exact Hou].
  - destruct (rel_offset (ob_base o) ae) as [off|]; [|apply IH; exact Hou].
    cbv zeta. rewrite in_bounds_d_core, !(sitv_d_q_eq sf dg _ H).
    destruct (ib_cheap (sitv_d dg (ob_lo o)) (sitv_d dg (ob_hi o)) (sitv_d dg off) k) eqn:C.
    + rewrite (ib_cheap_core (uleq_d dg) (sleq_d dg) _ _ _ (ob_lo o) (ob_hi o) off k C).
      exists ou. split; [reflexivity | exact Hou].
    + assert (U : match ou with Some u => u | None => mk_u2 dg end = mk_u2 dg) by (destruct Hou as [->| ->]; reflexivity).
      rewrite U.
      rewrite (ib_core_ext (uleq_d_q (mk_u2 dg) dg) (uleq_d dg) (sleq_d_q sf dg) (sleq_d dg));
        [|intros; apply uleq_d_q_eq | intros; apply sleq_d_q_eq; exact H].
      destruct (ib_core (uleq_d dg) (sleq_d dg) (sitv_d dg (ob_lo o)) (sitv_d dg (ob_hi o)) (sitv_d dg off)
                        (ob_lo o) (ob_hi o) off k).
      * exists (Some (mk_u2 dg)). split; [reflexivity | right; reflexivity].
      * apply IH. right; reflexivity.
Qed.

Lemma dg_facts_tbl_init : ltac2:(tb__ "0|0|
S6SfA1S1cS18S6S10A1S1dS42R1R2A2A1S1dR1A1A3Fdg;Fes;").
Proof. induction es as [|e rest IH]; intros dg; cbn [tbl_init]; [reflexivity|]. cbv zeta. rewrite IH. reflexivity. Qed.

Lemma dg_facts_mk_ctx : ltac2:(tb__ "0|1|
S6S10A1M0S18G0S1dS39R1A1A1R1A3Ffacts;").
Proof.
  intros facts. unfold mk_ctx. cbv zeta.
  destruct (endpoints (srels_of facts) (endpoints (rels_of facts) [])) as [|e0 es]; [reflexivity|].
  cbn [dg_with_tbl dg_facts]. rewrite dg_facts_tbl_init. reflexivity.
Qed.

Lemma dg_facts_mk_dig : ltac2:(tb__ "0|1|
S6S10A1M0S18G0S1dS3aR1A1A1R1A3Ffacts;").
Proof. intros facts. unfold mk_dig. cbv zeta. cbn [dg_with_pool dg_facts]. apply dg_facts_mk_ctx. Qed.

Lemma dg_facts_ctx0 : ltac2:(tb__ "0|1|
S6S10A1M0S18G0S1dS33R1A1A1R1A3Ffacts;").
Proof. reflexivity. Qed.
