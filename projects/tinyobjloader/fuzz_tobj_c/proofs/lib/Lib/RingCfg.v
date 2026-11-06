(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "valuation"; "sprop"; "sv_below"; "sv_eqb"; "sstate"; "holds"; "ss_next"; "SLit"; "eval"; "rl"; "agree_below"; "rm"; "rw"; "sprop_below"; "ss_lenient"; "SVar"; "ss_facts"; "@Corelib.Init.Logic"; "eq"; "and"; "True"; "not"; "or"; "ex"; "@Corelib.Init.Datatypes"; "bool"; "option"; "andb"; "false"; "true"; "prod"; "list"; "pair"; "snd"; "orb"; "cons"; "fst"; "nat"; "nil"; "app"; "length"; "Some"; "implb"; "negb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.RingCfg"; "rnode"; "rghost"; "rn_state"; "rn_ph"; "rn_ring"; "rg_cur"; "rn_lex"; "rn_sub"; "rg_R"; "rn_dist"; "rn_init"; "rg_eqs"; "rn_gfacts"; "rg_roots"; "rn_alln"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "N"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.RingCfg.RC"; "Uv"; "lex3"; "rmeas"; "node_okb"; "rn_ghost"; "Rn"; "nval"; "ring_sem"; "NXf"; "live_term"; "to_enodeR"; "cmp3"; "M32"; "live_by"; "pair_eqb"; "rg_below"; "src_state"; "ueq"; "alln"; "distv"; "eq_by"; "gfact_ok"; "lex_cmp"; "neq_fact"; "rcheck"; "subst_lex"; "NXT"; "PVf"; "alln_check"; "base_ok"; "check_rcfg"; "dist_check"; "init_check"; "initok"; "meas_check"; "ring_check"; "sv_ht"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "vdir"; "lex_val"; "B64"; "comp_val"; "edge"; "enode"; "SPfamE"; "Vdown"; "cuts_edges"; "eedge_ok"; "add_facts"; "e_leaf"; "e_src"; "e_sub"; "e_tgt"; "@Stdlib.ZArith.BinInt.Z"; "lt"; "pow"; "add"; "mul"; "le"; "ltb"; "eqb"; "leb"; "modulo"; "of_nat"; "sub"; "min"; "to_nat"; "@Stdlib.Lists.List"; "forallb"; "In"; "existsb"; "nth_error"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "sv_subst"; "wsub"; "rho_sub"; "wsub_id_below"; "@Corelib.Lists.ListDef"; "map"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "etriple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "SP"; "@LinuxProcessSemantics.Riscv.Instr"; "branch_cond"; "aluop"; "mulop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.Ring"; "live"; "ring_ok"; "findex"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "uleq"; "@Stdlib.PArith.BinPos.Pos"; "lt"; "eqb"; "le"; "leb"; "ltb"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.RingBuf"; "lget"; "LD4"; "@Corelib.Init.Peano"; "lt"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia Zwf Wellfounded.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import CursorGlue RingBuf Ring.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Record rghost := mkRG { rg_R : sv; rg_cur : sv; rg_roots : list sv; rg_eqs : list (sv * sv) }.
Record rnode := mkRN {
  rn_state : sstate;
  rn_gfacts : list sprop;
  rn_alln : bool;
  rn_init : option sv;
  rn_ring : option rghost;
  rn_ph : Z;
  rn_lex : list (vdir * sv);
  rn_sub : Z;
  rn_dist : option (sv * sv) }.

Section RC.
Variable segs : list Segment.
Variable g : positive.
Variable vn : positive.
Variable ln lp : positive.

Definition NXT (e : sv) : sv := LD4 ln e.
Definition PRV (e : sv) : sv := LD4 lp e.

Definition Uv (rho : valuation) (e : sv) : Z := bv_unsigned (eval rho e).
Definition nval (rho : valuation) : Z := bv_unsigned (rw rho vn).
Definition NXf (rho : valuation) : Z -> Z := lget (rl rho ln).
Definition PVf (rho : valuation) : Z -> Z := lget (rl rho lp).
Definition Rn (rho : valuation) (rg : rghost) : nat := ltac2:(tb__ "0|0|
S7dS3dVrho;S33Vrg;A1A2A1").

Definition alln (n : Z) (L : list byte) : Prop := ltac2:(tb__ "0|0|
S3aS13S75Z0R1A2S71R1Vn;A2A2S71S9aVL;R2A2Vn;A2F_;Fi;").
Definition initok (n I : Z) (NX PV : list byte) : Prop := ltac2:(tb__ "0|1|
S3aS13S75Z0R1A2S71R1VI;A2A2S13S12S3aS9aVNX;R2A2S79S73R2Z1M0A2Vn;A2A3S12S3aS9aVPV;R2A2S79S7bS73R2Vn;A2G0A2Vn;A2A3A2F_;Fj;").

Definition base_ok (rho0 rho : valuation) : Prop := ltac2:(tb__ "0|2|
S13S3bS94R1Vg;A2S12S99Q40A1M0SdVrho0;R2A2SdVrho;R2A2A3F_;Fi;S13G0S12S19S99Q8A1M1A1ScVrho0;R1A2ScVrho;R1A2A3Fa;S13S3bS15S12S3bR1Vln;A3A1S15S12S3bR2Vlp;A3A1S12S1eG1A1SaVrho0;R3A2SaVrho;R3A2A3F_;F_;Fl;S71S43Vrho;A1S72Z2Z20A2A2A2A2A2").

Definition ring_sem (rg : rghost) (rho : valuation) : Prop := ltac2:(tb__ "0|4|
S13S8fS43Vrho;A1S42Vrho;Vrg;A2M0S3dVrho;S30Vrg;A1A2M1S45Vrho;A1M2S58Vrho;A1A5S13S87S0S0S8eG0G1G2S3dVrho;R1A2A4Lr;S38Vrg;A1A3S87S1dS0S0A2M3G3S12S99Q40A1S9Vrho;S23S0S0R1A3A2S9Vrho;S20S0S0R1A3A2A3Lab;S36Vrg;A1A3A2A2").

Definition rn_ghost (rho0 : valuation) (nd : rnode) (rho : valuation) : Prop := ltac2:(tb__ "0|3|
S13S5aVrho0;Vrho;A2S13S12S18S39Vnd;A1S1cA3S13S4fS43Vrho;A1M0SaVrho;Vln;A2M1A2S4fG0SaVrho;Vlp;A2M2A2A2F_;S13S19S0A1OLx;S35Vnd;A1S0S5eG0S3dVrho;R1A2G1G2A4Lei;S14X19x2S19S2cA1OLx;S2fVnd;A1S2cS44R1Vrho;A2Lrg;S14X19x2A2A2A2").

Definition pad3 : list (vdir * sv) := ltac2:(tb__ "0|2|
S22S1dS62S0A2M0S1fS62S0S69S1bA1S8Z0A1A4M1S22G0G1S22G0G1S25G0A1A3A3A3").
Definition lex3 (l : list (vdir * sv)) : list (vdir * sv) := firstn 3 (l ++ pad3).
Definition M32 : Z := 2 ^ 32.
Definition distv (nd : rnode) (rho : valuation) : Z := ltac2:(tb__ "0|2|
S19S1dS0S0A2M0A1S3aLx;S34Vnd;A1G0G0S3aLp0;R1S0S0S19S2cA1S3aLx;S2fVnd;A1S2cS7cS7aS90S45Vrho;A1S3dVrho;R3A2S3dVrho;R2A2S42Vrho;R1A2A4A1S7bS49Z1A2A2Lrg;Z0M1X19x2Lp;Lr;X1dx1Lp0;G1X19x2").
Definition rmeas (nd : rnode) (rho : valuation) : Z := ltac2:(tb__ "0|0|
S73S74S73S74S73S74S2eVnd;A1S72S64Z3A2A2S63Vrho;S3eS31Vnd;A1A1A2A2Z10A2S32Vnd;A1A2S49A2S50Vnd;Vrho;A2A2").

Definition to_enodeR (rho0 : valuation) (nd : rnode) : enode := ltac2:(tb__ "0|1|
S1fS1dS5S1OFrho;M0A2S1S3aFrho;S1fS5G0S2dVnd;A1S41Vrho0;Vnd;A2A4S3fVnd;A1A4").

Lemma lex3_length : ltac2:(tb__ "0|1|
S1eS1dS62S0A2M0A1S12S24S27G0S3eR1A1A2U3A3Fl;").
Proof using . intros l. unfold lex3, pad3. rewrite length_firstn, length_app. cbn [length]. lia. Qed.

Lemma distv_range : ltac2:(tb__ "0|1|
S2bS1S13S75Z0S50R2R1A2M0A2S71G0S49A2A2Frho;Fnd;").
Proof using . intros nd rho. unfold distv, M32. destruct (rn_dist nd) as [[r p]|]; [destruct (rn_ring nd)|]; lia. Qed.

Lemma lex3_range : ltac2:(tb__ "0|1|
S1S1eS1dS62S0A2A1S13S75Z0S63R2S3eR1A1A2M0A2S71G0S72S64Z3A2A2A2Fl;Frho;").
Proof using . intros rho l. pose proof (lex_val_range rho (lex3 l)) as H. rewrite lex3_length in H. exact H. Qed.

Fixpoint live_term (rg : rghost) (e : sv) {struct e} : bool :=
  existsb (sv_eqb e) (rg_cur rg :: rg_roots rg)
  || match e with
     | SLBytes l (SAlu ALU_SLL e' (SLit c)) k => (Pos.eqb l ln || Pos.eqb l lp) && (c =? 2) && (k =? 4) && live_term rg e'
     | _ => false
     end.

Fixpoint sv_ht (e : sv) : nat :=
  match e with
  | SAlu _ a b | SAluW _ a b | SMd _ a b | SMdW _ a b => S (Nat.max (sv_ht a) (sv_ht b))
  | SExt _ _ a => S (sv_ht a)
  | SLBytes _ i _ => S (sv_ht i)
  | _ => O
  end.

Definition gfact_ok (nd : rnode) (f : sprop) : bool := ltac2:(tb__ "0|4|
S19S2cA1S18Lx;S2fVnd;A1S2cS2S18Lf;Vf;S8bS0S0S1bLb;La;M0Lc;S2S1bLp;S0S0S0S18Lb;R1S3aS1bLz;S3bS1aS95R1Vvn;A2S46R4R3A2A2Lv;S8cS0S0S1bLb0;La;M1Lop;M2G2S8dG1Lop;M3G3S18S3cS0S1bLa;Lw;Lsgn;S3bS0S3aS1bLk;Li;Ll;X0x8Lb;Le;G0G0S1bS3bS3aS1bLa;Li;X2x7Lrg;S1bX19x2").

Definition rg_below (k : positive) (rg : rghost) : bool := ltac2:(tb__ "0|1|
S1aS1aS1aS3Vk;S33Vrg;A1A2S3Vk;S30Vrg;A1A2A2S7eS0S3Vk;A1S38Vrg;A1A3A2S7eS1dS0S0A2M0G0S1aS3Vk;S23S0S0R1A3A2S3Vk;S20S0S0R1A3A2A2Lab;S36Vrg;A1A3A2").

Definition node_okb (nd : rnode) : bool := ltac2:(tb__ "0|a|
S1aS1aS1aS1aS1aS1aS1aS1aS1aS1aS1aS2aSfS2dVnd;A1M0A1A1S97Vg;S7G0A1M1A2A2S98Vvn;Vg;A2A2S7eS2S52Vnd;A1S37Vnd;A1M2A3A2S7eS2SeG1A1G2A3A2S78Z0M3S2eVnd;A1A2A2S78G3S32Vnd;A1M4A2A2S76G4Z10A2A2S7eS1dS62S0A2M5G5S3G1S20S62S0R1A3A2Lc;S3eS31Vnd;A1A1A3A2S19S2cA1S18Lx;M6S2fVnd;A1M7S2cS4cG1R1A2Lrg;S1cX19x2A2S19S0A1S18Lx;S35Vnd;A1S0S3G1R1A2M8Lei;S1cX19x2A2S19S1dS0S0A2M9A1S18Lx;S34Vnd;A1G9G9S18Lp0;R1S0S0S1aS1aS3G1R2A2G8A2G6G7S2cS1cLr0;S1bX19x2A2Lp;Lr;X1dx1Lp0;S1cX19x2A2").

Lemma ring_R_le_n : ltac2:(tb__ "0|1|
S3aS24S3aS3aS3aF_;M0G0S8fR5R4R3R2R1A5S75S7aR5A1R6A2F_;Fpv;Fnx;Fcur;FR;Fn;").
Proof using .
  intros n R cur nx pv (HR1 & Hnd & Hb & _ & _).
  assert (Hincl : incl (chain nx cur R) (map Z.of_nat (seq 0 (Z.to_nat n)))).
  { intros y Hy. pose proof (proj1 (Forall_forall _ _) Hb y Hy) as By. cbn beta in By.
    apply in_map_iff. exists (Z.to_nat y). split; [lia|]. apply in_seq. lia. }
  pose proof (NoDup_incl_length Hnd Hincl) as L. rewrite chain_length, length_map, length_seq in L.
  destruct (Z.le_gt_cases 0 n); lia.
Qed.

Lemma live_LD4 : ltac2:(tb__ "0|0|
S2cS1S3bS0S44R4R3A2S71S43R4A1S72Z2Z20A2A2S16S12S3bR4Vln;A3S12S3bR4Vlp;A3A2S8eS42R6R7A2S3dR6S30R7A1A2S45R6A1S3dR6R4A2A4S8eS42R7R8A2S3dR7S30R8A1A2S45R7A1S3dR7S9bR6R5A2A2A4F_;F_;F_;F_;Fa;Fl;Frho;Frg;").
Proof using .
  intros rg rho l a (HR & _ & _) Hn Hl Ha.
  pose proof (live_lt _ _ _ _ _ _ HR Ha) as Ba.
  unfold Uv. rewrite U_LD4 by (unfold Uv in Ba; lia). fold (Uv rho a).
  destruct Hl as [-> | ->].
  - change (lget (rl rho ln)) with (NXf rho). eapply live_nx; [exact HR | exact Ha].
  - change (lget (rl rho lp)) with (PVf rho). apply (live_pv _ _ _ _ _ _ HR Ha).
Qed.

Lemma live_term_sound_ht : ltac2:(tb__ "0|0|
S2cS1S24S0S44R4R3A2S71S43R4A1S72Z2Z20A2A2S9cS61R3A1R4A2S12S18S46R7R4A2S1cA3S8eS42R7R8A2S3dR7S30R8A1A2S45R7A1S3dR7R5A2A4F_;F_;F_;F_;Fe;Fh;Frho;Frg;").
Proof using .
  intros rg rho h. induction h as [|h IH]; intros e HS Hn Hh H; [lia|].
  assert (BASE : existsb (sv_eqb e) (rg_cur rg :: rg_roots rg) = true ->
                 live (Rn rho rg) (Uv rho (rg_cur rg)) (NXf rho) (Uv rho e)).
  { intros B. cbn [existsb] in B. apply orb_prop in B. destruct B as [B|B].
    - apply sv_eqb_sound in B. rewrite B. eapply live_cur. exact (proj1 HS).
    - apply existsb_exists in B as (r & Hr & E). apply sv_eqb_sound in E. rewrite E.
      exact (proj1 (Forall_forall _ _) (proj1 (proj2 HS)) r Hr). }
  destruct e as [z|v|op0 a0 b0|op0 a0 b0|op0 a0 b0|op0 a0 b0|sg w a0|l i k]; cbn [live_term] in H; apply orb_prop in H; (destruct H as [H|H]; [exact (BASE H)|try discriminate]).
  destruct i as [| |op a b| | | | |]; try discriminate. destruct op; try discriminate.
  destruct b as [c| | | | | | |]; try discriminate.
  apply andb_prop in H as [H Ha]. apply andb_prop in H as [H Hk]. apply andb_prop in H as [Hl Hc].
  apply Z.eqb_eq in Hk. apply Z.eqb_eq in Hc. subst k c.
  change (SLBytes l (SAlu ALU_SLL a (SLit 2)) 4) with (LD4 l a).
  apply live_LD4; [exact HS | exact Hn | | apply IH; [exact HS | exact Hn | cbn in Hh; lia | exact Ha]].
  apply orb_prop in Hl. destruct Hl as [Hl|Hl]; apply Pos.eqb_eq in Hl; auto.
Qed.

Lemma live_term_sound : ltac2:(tb__ "0|0|
S2cS1S0S44R3R2A2S71S43R3A1S72Z2Z20A2A2S12S18S46R5R3A2S1cA3S8eS42R5R6A2S3dR5S30R6A1A2S45R5A1S3dR5R4A2A4F_;F_;F_;Fe;Frho;Frg;").
Proof using . intros rg rho e HS Hn H. eapply (live_term_sound_ht rg rho (S (sv_ht e))); eauto. Qed.

Lemma node_okb_spec : ltac2:(tb__ "0|a|
S2bS12S18S40R1A1S1cA3S13S12S18SfS2dR2A1M0A1S1bA3S13S96Vg;S7G0A1M1A2S13S94Vvn;Vg;A2S13S12S18S7eS2S52R2A1S37R2A1M2A3S1cA3S13S12S18S7eS2SeG1A1G2A3S1cA3S13S75Z0M3S2eR2A1A2S13S75G3S32R2A1M4A2S13S71G4Z10A2S13S12S18S7eS1dS62S0A2M5G5S3S7S2dR3A1A1M6S20S62S0R1A3A2Lc;S3eS31R2A1A1A3S1cA3S13S19S2cA1M7OLx;S2fR2A1S2cS12S18S4cG6R1A2S1cA3Lrg;S14X19x2S13S19S0A1OLx;S35R2A1S0S12S18S3G6R1A2S1cA3Lei;S14X19x2S19S1dS0S0A2M8A1OLx;S34R2A1G8G8OLp0;R1S0S0S13S12S18S3S7S2dR5A1A1M9R2A2S1cA3S13S12S18S3G9R1A2S1cA3S17S2cS2cS12G7S2fR6A1S28S2cR1A2A3Lrg;A2A2A2Lp;Lr;X1dx1Lp0;S14X19x2A2A2A2A2A2A2A2A2A2A2A2F_;Fnd;").
Proof using .
  intros nd H. unfold node_okb in H.
  apply andb_prop in H as [H Hdist]. apply andb_prop in H as [H Hinit]. apply andb_prop in H as [H Hring].
  apply andb_prop in H as [H Hlex]. apply andb_prop in H as [H Hsub2]. apply andb_prop in H as [H Hsub1].
  apply andb_prop in H as [H Hph]. apply andb_prop in H as [H Hbelow]. apply andb_prop in H as [H Hgf].
  apply andb_prop in H as [H Hvn]. apply andb_prop in H as [Hlen Hg].
  split. { destruct (ss_lenient (rn_state nd)); [discriminate|reflexivity]. }
  split. { apply Pos.leb_le. exact Hg. } split. { apply Pos.ltb_lt. exact Hvn. }
  split; [exact Hgf|]. split; [exact Hbelow|].
  split. { apply Z.leb_le. exact Hph. } split. { apply Z.leb_le. exact Hsub1. } split. { apply Z.ltb_lt. exact Hsub2. }
  split; [exact Hlex|]. split.
  { destruct (rn_ring nd); [exact Hring|exact I]. }
  split. { destruct (rn_init nd); [exact Hinit|exact I]. }
  destruct (rn_dist nd) as [[r p]|]; [|exact I].
  apply andb_prop in Hdist as [Hdist Hrg]. apply andb_prop in Hdist as [Hr Hp].
  split; [exact Hr|]. split; [exact Hp|]. destruct (rn_ring nd) as [rg|]; [exists rg; reflexivity|discriminate].
Qed.

Lemma gfacts_sound : ltac2:(tb__ "0|0|
S1S2bS1S12S18S40R2A1S1cA3S41R4R3R2A3S87S2S6R3A1S37R4A1A3F_;F_;Frho;Fnd;Frho0;").
Proof using .
  intros rho0 nd rho Hok (Hbase & _ & _ & Hring).
  destruct (node_okb_spec nd Hok) as (_ & _ & _ & Hgf & _).
  apply Forall_forall. intros f Hf. pose proof (proj1 (forallb_forall _ _) Hgf f Hf) as G.
  unfold gfact_ok in G. destruct (rn_ring nd) as [rg|]; [|discriminate].
  destruct f as [| |e b| | | |]; try discriminate. destruct b as [|v| | | | | |]; try discriminate.
  apply andb_prop in G as [Hv He]. apply Pos.eqb_eq in Hv. subst v.
  pose proof Hbase as (_ & _ & _ & Hn).
  pose proof (live_term_sound rg rho e Hring Hn He) as L.
  pose proof (live_lt _ _ _ _ _ _ (proj1 Hring) L) as B.
  cbn [holds eval]. unfold Uv, nval in B. lia.
Qed.

Definition src_state (nd : rnode) : sstate := ltac2:(tb__ "0|0|
S6cS37Vnd;A1S2dVnd;A1A2").

Lemma SP_src_state : ltac2:(tb__ "0|0|
S1S1eS92A1S91OF_;F_;S2bS1S88S12S18S40R3A1S1cA3S41R6R4R3A3S8aVsegs;R6S2dR5A1R4R3A5S8aVsegs;R7S4dR6A1R5R4A5F_;F_;F_;Fw;Frho;Fnd;FK;Frho0;").
Proof using .
  intros rho0 K nd rho w Hok Hg [Hsm Hk]. split; [|exact Hk].
  unfold src_state. apply smatch_add_facts; [exact Hsm | eapply gfacts_sound; eauto |].
  exact (proj1 (proj2 (proj2 (proj2 (proj2 (node_okb_spec nd Hok)))))).
Qed.

Theorem rcfg_complete : ltac2:(tb__ "0|3|
S1S24S1eS3aA1S1eS2bA1M0G0S1eS66A1M1S1eS92A1S91OF_;F_;S88OF_;S12S18S7eS2bS40R5A3S1cA3S12S19G1A1S6aVsegs;R8R7Vg;U0S86S2bS5S4dR6A4S86S2bS5S2dS26S2bR6R5A3A4A7S28G1R4A2A3S87S66S6bS86S2bS67S47RaA1S26S2bR7R6A3A4A1R5A3S2bS1S7fS2bR2R9A3S41ReR3R2A3S89Vsegs;S8aVsegs;R9S2dR4A1M2R3A4S88S16S68Vsegs;RaS86S2bS67S47R10A1RdA4S3fR5R4A2R1A5R9R1A1A2Lw;A3F_;F_;Frho;FE;S2bS1S7fS2bR2RbA3S41RfR3R2A3S89Vsegs;S8aVsegs;RaG2R3A4R9A3F_;F_;Frho;Fn;F_;F_;F_;F_;FQ;FK;Fes;Fexits;Fcuts;Fcutpcs;Ffuel;Frho0;").
Proof using .
  intros rho0 fuel cutpcs cuts exits es K Q Hok Hes Hedges Hexits n rho Hin Hg.
  set (nodes := map (to_enodeR rho0) (cuts ++ exits)).
  set (I := fun (a : Z) (w : world) =>
              exists nd rho, In nd (cuts ++ exits) /\ rn_ghost rho0 nd rho /\ SP segs K (rn_state nd) rho w /\ rmeas nd rho = a /\ 0 <= a).
  assert (EDGE : forall n0 rho1 w, In n0 cuts -> rn_ghost rho0 n0 rho1 -> SP segs K (rn_state n0) rho1 w ->
            exists w' nj rhoj, wsteps segs w w' /\ In nj (cuts ++ exits) /\ rn_ghost rho0 nj rhoj /\ SP segs K (rn_state nj) rhoj w'
                               /\ 0 <= rmeas nj rhoj < rmeas n0 rho1).
  { intros n0 rho1 w Hcut Hg0 Hsp0.
    destruct (In_nth_error _ _ Hcut) as [k Hk].
    pose proof (proj1 (forallb_forall _ _) Hok n0 Hcut) as Hok0.
    assert (HkT : nth_error (map src_state cuts) k = Some (src_state n0)) by (rewrite nth_error_map, Hk; reflexivity).
    destruct (cuts_edges_spec segs fuel cutpcs g (map src_state cuts) 0 (map rn_state (cuts ++ exits)) es Hes k _ HkT)
      as (Hle & leaves & Hrun & HL).
    pose proof (node_okb_spec n0 Hok0) as (Hlen & _).
    pose proof (SP_src_state rho0 K n0 rho1 w Hok0 Hg0 Hsp0) as Hsp1.
    destruct (sym_run_etriple segs fuel cutpcs (src_state n0) leaves K rho1 Hlen Hrun w Hsp1) as (w' & Hsteps & HLQ).
    destruct HLQ as (L & rho'' & HinL & Hag & Hsm & Hkk).
    destruct (HL L HinL) as (j & s & X & HinE & HnX & Hid & Hent). rewrite Nat.add_0_l in HinE.
    pose proof (proj1 (Forall_forall _ _) Hedges _ HinE) as EOK. unfold eedge_ok in EOK. cbn [e_src e_tgt e_leaf e_sub] in EOK.
    rewrite nth_error_map in HnX.
    destruct (nth_error (cuts ++ exits) j) as [nj|] eqn:HnXG; cbn in HnX; [|discriminate]. injection HnX as HX.
    assert (FACTS : Forall (holds rho'') (ss_facts (lf_state L))).
    { destruct w' as [tr [ms md]]. exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 Hsm))))))))))). }
    assert (Hni : nth_error nodes k = Some (to_enodeR rho0 n0)).
    { unfold nodes. rewrite nth_error_map, nth_error_app1, Hk; [reflexivity|]. apply nth_error_Some. congruence. }
    assert (Hnj : nth_error nodes j = Some (to_enodeR rho0 nj)).
    { unfold nodes. rewrite nth_error_map, HnXG. reflexivity. }
    destruct (EOK (to_enodeR rho0 n0) (to_enodeR rho0 nj) Hni Hnj rho1 rho'' Hag Hg0 FACTS) as [HGj HMj].
    cbn [to_enodeR en_state en_ghost en_meas fst snd] in HGj, HMj.
    pose proof (SP_entails segs K (lf_state L) X s rho'' w' Hent (conj Hsm Hkk)) as HSPX. rewrite <- HX in HSPX.
    exists w', nj, (rho_sub rho'' s). split; [exact Hsteps|]. split; [eapply nth_error_In; exact HnXG|].
    split; [exact HGj|]. split; [exact HSPX|]. exact HMj. }
  assert (BODY : forall a, etriple segs (I a) (fun w => (exists a', (Zwf 0 a' a) /\ I a' w) \/ Q w)).
  { intros a w (n0 & rho1 & Hin0 & Hg0 & Hsp0 & Hm0 & Ha0).
    apply in_app_or in Hin0 as [Hcut|Hexit].
    - destruct (EDGE n0 rho1 w Hcut Hg0 Hsp0) as (w' & nj & rhoj & Hsteps & Hinj & Hgj & Hspj & Hmj).
      exists w'. split; [exact Hsteps|]. left. exists (rmeas nj rhoj). split; [unfold Zwf; lia|].
      exists nj, rhoj. split; [exact Hinj|]. split; [exact Hgj|]. split; [exact Hspj|]. split; [reflexivity|lia].
    - destruct (Hexits n0 rho1 Hexit Hg0 w Hsp0) as (w' & Hsteps & [Hfam|Hq]).
      + destruct Hfam as (n1 & rho2 & Hin1 & Hg1 & Hsp1 & Hm1).
        apply in_map_iff in Hin1 as (nd1 & <- & Hnd1).
        cbn [to_enodeR en_state en_ghost en_meas fst snd] in Hg1, Hsp1, Hm1.
        exists w'. split; [exact Hsteps|]. left. exists (rmeas nd1 rho2). split; [unfold Zwf; lia|].
        exists nd1, rho2. split; [apply in_or_app; left; exact Hnd1|]. split; [exact Hg1|]. split; [exact Hsp1|]. split; [reflexivity|lia].
      + exists w'. split; [exact Hsteps|]. right. exact Hq. }
  pose proof (@etriple_loop segs Z (Zwf 0) (Zwf_well_founded 0) I Q BODY) as LOOP.
  intros w Hw.
  destruct (Z_lt_le_dec (rmeas n rho) 0) as [Hneg|Hnn].
  - exfalso. destruct (EDGE n rho w Hin Hg Hw) as (w' & nj & rhoj & _ & _ & _ & _ & Hm). lia.
  - apply (LOOP (rmeas n rho)). exists n, rho. split; [apply in_or_app; left; exact Hin|].
    split; [exact Hg|]. split; [exact Hw|]. split; [reflexivity|lia].
Qed.

Definition ueq (FL : list sprop) (a b : sv) : bool := ltac2:(tb__ "0|1|
S21S4Va;Vb;A2S1aS93VFL;Va;Z0M0Vb;A4S93VFL;Vb;G0Va;A4A2A2").
Definition live_by (rs : rghost) (FL : list sprop) (e : sv) : bool := ltac2:(tb__ "0|1|
S21S46Vrs;Ve;A2S1aS4S33Vrs;A1S10Vvn;A1M0A2S93VFL;Ve;Z1G0A4A2A2").
Definition pair_eqb (p q : sv * sv) : bool := ltac2:(tb__ "0|0|
S1aS4S23S0S0Vp;A3S23S0S0Vq;A3A2S4S20S0S0Vp;A3S20S0S0Vq;A3A2A2").
Definition eq_by (rs : rghost) (p : sv * sv) : bool := ltac2:(tb__ "0|4|
S21S21S4S23S0S0Vp;A3M0S20S0S0Vp;A3M1A2S80S1dS0S0A2M2S4bVp;A1S36Vrs;A1M3A3A2S80G2S4bS1fS0S0G1G0A4A1G3A3A2").

Definition ring_check (FL : list sprop) (s : wsub) (src tgt : rnode) : bool := ltac2:(tb__ "0|2|
S19S2cA1S18Lx;M0S2fVtgt;A1S2cG0S2fVsrc;A1S2cS1aS1aS1aS4eVFL;S82Vs;S33R2A1A2S33R1A1A3S4aR1VFL;S82Vs;S30R2A1A2A3A2S7eS0S0S4aR2VFL;S82Vs;R1A2A3Lr;S38R2A1A3A2S7eS1dS0S0A2M1G1S51R2S1fS0S0S82Vs;S23S0S0R1A3A2S82Vs;S20S0S0R1A3A2A4A2Lab;S36R2A1A3A2Lrs;S1bX19x2Lrt;S1cX19x2").
Definition init_check (FL : list sprop) (s : wsub) (src tgt : rnode) : bool := ltac2:(tb__ "0|2|
S19S0A1S18Lx;M0S35Vtgt;A1S0S21S93VFL;S82Vs;R1A2Z0M1S8G1A1A4G0S35Vsrc;A1S0S4eVFL;S82Vs;R2A2R1A3Lej;S1bX19x2A2Lei;S1cX19x2").
Definition alln_check (src tgt : rnode) : bool := ltac2:(tb__ "0|0|
S29S39Vtgt;A1S39Vsrc;A1A2").

Inductive cmp3 := CLt | CLe | CUnk.
Fixpoint lex_cmp (FL : list sprop) (tgt src : list (vdir * sv)) : cmp3 :=
  match tgt, src with
  | [], [] => CLe
  | (dt, et) :: tr, (ds, es) :: sr =>
      if negb (vdir_eqb dt ds) then CUnk
      else if xlt FL ds et es then CLt
      else if xle FL ds et es then lex_cmp FL tr sr else CUnk
  | _, _ => CUnk
  end.
Definition neq_fact (a b : sv) (f : sprop) : bool := ltac2:(tb__ "0|4|
S2S18Lf;Vf;S8bS0S0S8bS18Lc;M0R3S1bS21S1aS4R2Va;A2S4R1Vb;A2A2S1aS4R2Vb;A2S4R1Va;A2A2A2M1S1bS1bS1bS1bX8bx6Ly;Lx;Lc;S2S2S18Lp;R1S8bS0S0G0R3G1S1bS1bS1bS1bS1bX8bx6Ly;Lx;Lc;S2S1bLp0;S0S0S1bLb0;La0;M2G2S0S0G1Ly;Lx;S1bS3bS3aS1bLa0;Li;M3X2x7Lp;G2G2G2S1bG3X2x7").
Definition dist_check (FL : list sprop) (s : wsub) (src tgt : rnode) : bool := ltac2:(tb__ "0|3|
S19S1dS0S0A2M0A1S18Lx;M1S34Vtgt;A1G0G0S18Lp;R1S0S0G1S34Vsrc;A1G0G0S18Lp0;R1S0S0S19S2cA1S18Lx;M2S2fVsrc;A1S2cG2S2fVtgt;A1S2cS1aS1aS1aS1aS4S82Vs;R7A2S57R4A1A2S4S82Vs;R6A2R3A2A2S46R2R4A2A2S46R2R3A2A2S80S2S54R4R3A2VFL;A3A2Lr;S1bX19x2Lrg;S1bX19x2Lps;Lrs_;X1dx1Lp0;S1bX19x2Lpt;Lrt;X1dx1Lp;S1bX19x2").
Definition subst_lex (s : wsub) (l : list (vdir * sv)) : list (vdir * sv) := ltac2:(tb__ "0|1|
S86S1dS62S0A2M0G0G0S1fS62S0S23S62S0R1A3S82Vs;S20S62S0R1A3A2A4Lc;Vl;A4").
Definition meas_check (FL : list sprop) (s : wsub) (src tgt : rnode) : bool := ltac2:(tb__ "0|4|
S21S76S2eVtgt;A1M0S2eVsrc;A1M1A2S1aS77G0G1A2S48S18Lx;S53VFL;S56Vs;S3eS31Vtgt;A1A1A2S3eS31Vsrc;A1A1A3S1cS21S76S32Vtgt;A1M2S32Vsrc;A1M3A2S1aS77G2G3A2S5cVFL;Vs;Vsrc;Vtgt;A4A2A2S1bX48x3A2A2").
Definition rcheck (nodes : list rnode) (e : edge) : bool := ltac2:(tb__ "0|1|
S19S2bA1S18Lx;M0S81S2bVnodes;S6eVe;A1A3S2bG0S81S2bVnodes;S70Ve;A1A3S2bS11S6dVe;A1A1S1eS2A1S6fVe;A1S83S1aS1aS1aS1aS1aS1aS40R4A1S40R3A1A2S85R1Vg;A2A2S59R4R3A2A2S5dR2R1R4R3A4A2S60R2R1R4R3A4A2S5fR2R1R4R3A4A2Ts;TFL;Ltgt;S1bX19x2Lsrc;S1bX19x2").

Lemma Uv_sub : ltac2:(tb__ "0|0|
S1S83S0S12S3aS3dS84R3R2A2R1A2S3dR3S82R2R1A2A2A3Fe;Fs;Frho;").
Proof using . intros. unfold Uv. rewrite eval_subst. reflexivity. Qed.

Lemma nval_sub : ltac2:(tb__ "0|0|
S1S83S12S18S85R1Vg;A2S1cA3S94Vvn;Vg;A2S12S3aS43S84R4R3A2A1S43R4A1A3F_;F_;Fs;Frho;").
Proof using .
  intros rho s Hid Hvn. unfold nval. cbn [rw rho_sub]. rewrite (wsub_get_id s g vn Hid Hvn). reflexivity.
Qed.

Lemma ueq_sound : ltac2:(tb__ "0|0|
S1S1eS2A1S0S0S87S2S6R4A1R3A3S12S18S4eR4R3R2A3S1cA3S12S3aS3dR6R4A2S3dR6R3A2A3F_;F_;Fb;Fa;FFL;Frho;").
Proof using .
  intros rho FL a b HF H. unfold ueq in H. apply orb_prop in H. destruct H as [H|H].
  - apply sv_eqb_sound in H. subst. reflexivity.
  - apply andb_prop in H as [H1 H2]. pose proof (uleq_sound rho FL a 0 b HF H1). pose proof (uleq_sound rho FL b 0 a HF H2).
    unfold U in *. unfold Uv. lia.
Qed.

Lemma live_by_sound : ltac2:(tb__ "0|0|
S2cS1S1eS2A1S0S44R4R3A2S71S43R4A1S72Z2Z20A2A2S87S2S6R5A1R4A3S12S18S4aR7R5R4A3S1cA3S8eS42R7R8A2S3dR7S30R8A1A2S45R7A1S3dR7R5A2A4F_;F_;F_;F_;Fe;FFL;Frho;Frs;").
Proof using .
  intros rs rho FL e HS Hn HF H. unfold live_by in H. apply orb_prop in H. destruct H as [H|H].
  - eapply live_term_sound; eauto.
  - apply andb_prop in H as [HR Hu]. apply sv_eqb_sound in HR.
    pose proof (uleq_sound rho FL e 1 (SVar vn) HF Hu) as U1. unfold U in U1. cbn [eval] in U1.
    eapply ring_full; [exact (proj1 HS)| |unfold Uv, nval in *; pose proof (urange (eval rho e)); lia].
    unfold Rn. rewrite HR. unfold Uv, nval. cbn [eval]. pose proof (urange (rw rho vn)). lia.
Qed.

Lemma pair_eqb_sound : ltac2:(tb__ "0|1|
S1dS0S0A2M0G0S12S18S4bR2R1A2S1cA3S12G0R3R2A3F_;Fq;Fp;").
Proof using .
  intros [a b] [c d] H. unfold pair_eqb in H. cbn in H. apply andb_prop in H as [H1 H2].
  apply sv_eqb_sound in H1. apply sv_eqb_sound in H2. congruence.
Qed.

Lemma eq_by_sound : ltac2:(tb__ "0|0|
S2cS1S0S0S44R4R3A2S12S18S51R5S1fS0S0R3R2A4A2S1cA3S12S99Q40A1S9R5R4A2S9R5R3A2A3F_;F_;Fb;Fa;Frho;Frs;").
Proof using .
  intros rs rho a b (_ & _ & Heqs) H. unfold eq_by in H. cbn [fst snd] in H.
  apply orb_prop in H. destruct H as [H|H]; [apply orb_prop in H; destruct H as [H|H]|].
  - apply sv_eqb_sound in H. congruence.
  - apply existsb_exists in H as (q & Hq & E). apply pair_eqb_sound in E. subst q.
    exact (proj1 (Forall_forall _ _) Heqs _ Hq).
  - apply existsb_exists in H as (q & Hq & E). apply pair_eqb_sound in E. subst q.
    symmetry. exact (proj1 (Forall_forall _ _) Heqs _ Hq).
Qed.

Lemma neq_fact_sound : ltac2:(tb__ "0|0|
S1S1eS2A1S0S0S87S2S6R4A1R3A3S12S18S80S2S54R3R2A2R4A3S1cA3S15S12S3aS3dR6R4A2S3dR6R3A2A3A1F_;F_;Fb;Fa;FFL;Frho;").
Proof using .
  intros rho FL a b HF H. apply existsb_exists in H as (f & Hf & E).
  pose proof (proj1 (Forall_forall _ _) HF f Hf) as Hh.
  assert (GEN : forall x y, (sv_eqb x a && sv_eqb y b) || (sv_eqb x b && sv_eqb y a) = true ->
                bv_unsigned (eval rho x) <> bv_unsigned (eval rho y) -> Uv rho a <> Uv rho b).
  { intros x y Hxy Hne. unfold Uv. apply orb_prop in Hxy. destruct Hxy as [Hxy|Hxy]; apply andb_prop in Hxy as [H1 H2];
      apply sv_eqb_sound in H1; apply sv_eqb_sound in H2; subst; congruence. }
  destruct f as [c x y|p| | | | |]; try discriminate.
  - destruct c; try discriminate. apply (GEN x y E). apply holds_bne. exact Hh.
  - destruct p as [c x y| | | |x y| |]; try discriminate.
    + destruct c; try discriminate. apply (GEN x y E). apply holds_nbeq. exact Hh.
    + apply (GEN x y E). apply holds_neq. exact Hh.
Qed.

Lemma lex_val_subst : ltac2:(tb__ "0|0|
S1S83S1eS1dS62S0A2A1S12S3aS63S84R3R2A2R1A2S63R3S56R2R1A2A2A3Fl;Fs;Frho;").
Proof using .
  intros rho s l. induction l as [|[d e] t IH]; cbn [lex_val subst_lex map fst snd]; [reflexivity|].
  unfold subst_lex in IH. rewrite IH, length_map.
  unfold comp_val, base_val. cbn [fst snd]. rewrite !eval_subst. reflexivity.
Qed.

Lemma lex_cmp_sound : ltac2:(tb__ "0|4|
S1S1eS2A1S1eS1dS62S0A2M0A1M1G1S87S2S6R4A1R3A3S12S24S27G0R3A2S27G0R2A2A3S48OLx;S53R5R4R3A3S75S73S63R6R4A2M2Z1A2S63R6R3A2M3A2S75G2G3A2S14X48x3F_;F_;Fsrc;Ftgt;FFL;Frho;").
Proof using .
  intros rho FL tgt. induction tgt as [|[dt et] tr IH]; intros src HF Hlen.
  - destruct src; cbn; [lia|exact I].
  - destruct src as [|[ds es] sr]; [discriminate|]. cbn [lex_cmp]. cbn in Hlen. apply Nat.succ_inj in Hlen.
    destruct (vdir_eqb dt ds) eqn:Hd; cbn [negb]; [|exact I]. apply vdir_eqb_sound in Hd. subst dt.
    cbn [lex_val length]. rewrite Hlen.
    pose proof (lex_val_range rho tr) as Rt. pose proof (lex_val_range rho sr) as Rs. rewrite Hlen in Rt.
    pose proof (B64_pos (length sr)) as P.
    destruct (xlt FL ds et es) eqn:Hlt.
    + pose proof (xlt_sound rho FL ds et es HF Hlt). nia.
    + destruct (xle FL ds et es) eqn:Hle; [|exact I].
      pose proof (xle_sound rho FL ds et es HF Hle). specialize (IH sr HF Hlen).
      destruct (lex_cmp FL tr sr); [nia|nia|exact I].
Qed.

Lemma ring_sem_agree : ltac2:(tb__ "0|1|
S3bS2cS1S1SbR4R2R1A3S12S18S4cR5R4A2S1cA3S44R5R4A2S94Vvn;R7A2S13S44R7R5A2S13S12S24S42R5R7A2S42R6R7A2A3S12S3aS3dR5S30R7A1M0A2S3dR6G0A2A3A2A2F_;F_;F_;F_;Frho';Frho;Frg;Fk;").
Proof using .
  intros k rg rho rho' Hag Hb HS Hvn. unfold rg_below in Hb.
  apply andb_prop in Hb as [Hb Heqs]. apply andb_prop in Hb as [Hb Hroots]. apply andb_prop in Hb as [HR Hcur].
  pose proof Hag as (Hrw & Hrl & _).
  assert (En : nval rho' = nval rho) by (unfold nval; rewrite Hrw by exact Hvn; reflexivity).
  assert (ENX : NXf rho' = NXf rho) by (unfold NXf; rewrite Hrl; reflexivity).
  assert (EPV : PVf rho' = PVf rho) by (unfold PVf; rewrite Hrl; reflexivity).
  assert (ER : Rn rho' rg = Rn rho rg) by (unfold Rn, Uv; rewrite (eval_agree k rho rho' _ Hag HR); reflexivity).
  assert (EC : Uv rho' (rg_cur rg) = Uv rho (rg_cur rg)) by (unfold Uv; rewrite (eval_agree k rho rho' _ Hag Hcur); reflexivity).
  destruct HS as (HRing & Hro & Heq). split; [|split; [exact ER|exact EC]].
  split; [|split].
  - rewrite En, ER, EC, ENX, EPV. exact HRing.
  - apply Forall_forall. intros r Hr. pose proof (proj1 (Forall_forall _ _) Hro r Hr) as L. cbn beta in L.
    rewrite ER, EC, ENX. unfold Uv. rewrite <- (eval_agree k rho rho' r Hag (proj1 (forallb_forall _ _) Hroots r Hr)). exact L.
  - apply Forall_forall. intros ab Hab. pose proof (proj1 (forallb_forall _ _) Heqs ab Hab) as B. cbn beta in B.
    apply andb_prop in B as [B1 B2].
    rewrite <- (eval_agree k rho rho' _ Hag B1), <- (eval_agree k rho rho' _ Hag B2).
    exact (proj1 (Forall_forall _ _) Heq ab Hab).
Qed.

Lemma ghost_agree : ltac2:(tb__ "0|0|
S1S2bS1S1S12S18S40R3A1S1cA3SbS7S2dR4A1A1R3R2A3S41R6R5R4A3S13S41R7R6R4A3S12S3aS3fR6R4A2S3fR6R5A2A3A2F_;F_;F_;Frho';Frho;Fnd;Frho0;").
Proof using .
  intros rho0 nd rho rho' Hok Hag HG.
  destruct (node_okb_spec nd Hok) as (_ & Hg & Hvn & _ & _ & _ & _ & _ & Hlex & Hring & Hinit & Hdist).
  pose proof Hag as (Hrw & Hrl & Hrm).
  destruct HG as (Hbase & Halln & Hini & Hrg).
  assert (En : nval rho' = nval rho) by (unfold nval; rewrite Hrw by lia; reflexivity).
  assert (Hbase' : base_ok rho0 rho').
  { destruct Hbase as (B1 & B2 & B3 & B4). split; [|split; [|split]].
    - intros i Hi. rewrite B1 by exact Hi. apply Hrw. lia.
    - intros a. rewrite B2. apply Hrm.
    - intros l H1 H2. rewrite B3 by assumption. apply Hrl.
    - rewrite En. exact B4. }
  split.
  - split; [exact Hbase'|]. split; [|split].
    + intros Ha. rewrite En, <- !Hrl. exact (Halln Ha).
    + destruct (rn_init nd) as [ei|]; [|exact I]. rewrite En, <- !Hrl.
      unfold Uv. rewrite <- (eval_agree _ rho rho' ei Hag Hinit). exact Hini.
    + destruct (rn_ring nd) as [rg|]; [|exact I].
      exact (proj1 (ring_sem_agree _ rg rho rho' Hag Hring Hrg ltac:(lia))).
  - unfold rmeas. rewrite (lex_val_agree _ rho rho' (lex3 (rn_lex nd)) Hag Hlex). f_equal.
    unfold distv. destruct (rn_dist nd) as [[r p]|]; [|reflexivity].
    destruct Hdist as (Hr & Hp & [rg Erg]). rewrite Erg in Hrg, Hring |- *.
    destruct (ring_sem_agree _ rg rho rho' Hag Hring Hrg ltac:(lia)) as (_ & ER & _).
    rewrite ER. unfold NXf, Uv. rewrite Hrl, (eval_agree _ rho rho' r Hag Hr), (eval_agree _ rho rho' p Hag Hp). reflexivity.
Qed.

Theorem rcheck_sound : ltac2:(tb__ "0|0|
S1S1eS2bA1S66S12S18S55R2R1A2S1cA3S6bS86S2bS67S47R4A1R3A4R2A2F_;Fe;Fnodes;Frho0;").
Proof using .
  intros rho0 nodes e H. unfold rcheck in H. unfold eedge_ok.
  intros Ti Tj Hi Hj rho rho' Hag HGi HF.
  rewrite nth_error_map in Hi, Hj.
  destruct (nth_error nodes (e_src e)) as [src|] eqn:Es; [|discriminate].
  destruct (nth_error nodes (e_tgt e)) as [tgt|] eqn:Et; [|discriminate].
  cbn in Hi, Hj. injection Hi as <-. injection Hj as <-.
  cbn [to_enodeR en_state en_ghost en_meas fst snd] in *.
  set (FL := ss_facts (e_leaf e)) in *. set (s := e_sub e) in *.
  apply andb_prop in H as [H Hmeas]. apply andb_prop in H as [H Hring]. apply andb_prop in H as [H Hinit].
  apply andb_prop in H as [H Halln]. apply andb_prop in H as [H Hid]. apply andb_prop in H as [Hoks Hokt].

  destruct (ghost_agree rho0 src rho rho' Hoks Hag HGi) as [HG EM]. rewrite <- EM. clear HGi EM Hag rho.
  destruct (node_okb_spec src Hoks) as (_ & Hgs & Hvn & _ & _ & Hph_s & Hsub_s & Hsub_s2 & Hlex_s & Hring_s & Hinit_s & Hdist_s).
  destruct (node_okb_spec tgt Hokt) as (_ & Hgt & _ & _ & _ & Hph_t & Hsub_t & Hsub_t2 & Hlex_t & Hring_t & Hinit_t & Hdist_t).
  destruct HG as (Hbase & HA & HI & HR).
  pose proof Hbase as (B1 & B2 & B3 & Bn).
  assert (En : nval (rho_sub rho' s) = nval rho') by (apply nval_sub; assumption).
  assert (Erl : forall l, rl (rho_sub rho' s) l = rl rho' l) by reflexivity.
  split.
  -
    split; [|split; [|split]].
    + split; [|split; [|split]].
      * intros i Hi. cbn [rw rho_sub]. rewrite (wsub_get_id s g i Hid Hi). cbn [eval]. apply B1. exact Hi.
      * exact B2.
      * intros l H1 H2. rewrite Erl. apply B3; assumption.
      * rewrite En. exact Bn.
    + intros Ha. unfold alln_check in Halln. rewrite Ha in Halln. cbn in Halln. rewrite En, !Erl. exact (HA Halln).
    + unfold init_check in Hinit. destruct (rn_init tgt) as [ei|]; [|exact I]. rewrite En, !Erl, Uv_sub.
      apply orb_prop in Hinit. destruct Hinit as [H0|Heq].
      * pose proof (uleq_sound rho' FL _ 0 (SLit 0) HF H0) as U0. unfold U in U0. cbn [eval] in U0.
        rewrite lit_unsigned in U0. change (0 mod 2 ^ 64) with 0 in U0.
        intros j Hj. unfold Uv in Hj. pose proof (urange (eval rho' (sv_subst s ei))). lia.
      * destruct (rn_init src) as [ej|]; [|discriminate]. rewrite (ueq_sound rho' FL _ _ HF Heq). exact HI.
    + unfold ring_check in Hring. destruct (rn_ring tgt) as [rt|]; [|exact I].
      destruct (rn_ring src) as [rs|]; [|discriminate].
      apply andb_prop in Hring as [Hring Heqs]. apply andb_prop in Hring as [Hring Hroots]. apply andb_prop in Hring as [HRR Hcur].
      pose proof HR as (HRok & _ & _).
      assert (ER : Rn (rho_sub rho' s) rt = Rn rho' rs) by (unfold Rn; rewrite Uv_sub, (ueq_sound rho' FL _ _ HF HRR); reflexivity).
      pose proof (live_by_sound rs rho' FL _ HR Bn HF Hcur) as Lcur.
      split; [|split].
      * rewrite En, ER. unfold NXf, PVf. rewrite !Erl. rewrite Uv_sub. fold (NXf rho') (PVf rho').
        eapply ring_rotate; [exact HRok | exact Lcur].
      * apply Forall_forall. intros r Hr. rewrite ER. unfold NXf. rewrite Erl, !Uv_sub. fold (NXf rho').
        apply (proj2 (live_rotate _ _ _ _ _ _ (Uv rho' (sv_subst s r)) HRok Lcur)).
        eapply live_by_sound; eauto. exact (proj1 (forallb_forall _ _) Hroots r Hr).
      * apply Forall_forall. intros [a b] Hab. cbn [fst snd]. rewrite <- !eval_subst.
        eapply (eq_by_sound rs rho'); [exact HR|]. exact (proj1 (forallb_forall _ _) Heqs (a, b) Hab).
  -
    unfold rmeas. rewrite lex_val_subst.
    pose proof (lex3_range (rho_sub rho' s) (rn_lex tgt)) as Rt. rewrite lex_val_subst in Rt.
    pose proof (lex3_range rho' (rn_lex src)) as Rs.
    pose proof (distv_range tgt (rho_sub rho' s)) as Dt. pose proof (distv_range src rho') as Ds.
    assert (P3 : 0 < B64 ^ 3) by (apply (B64_pos 3)).
    unfold meas_check in Hmeas. apply orb_prop in Hmeas. destruct Hmeas as [Hlt|H].
    + apply Z.ltb_lt in Hlt. unfold M32 in *. nia.
    + apply andb_prop in H as [Heq H]. apply Z.eqb_eq in Heq. rewrite Heq.
      pose proof (lex_cmp_sound rho' FL (subst_lex s (lex3 (rn_lex tgt))) (lex3 (rn_lex src)) HF
                    ltac:(unfold subst_lex; rewrite length_map, !lex3_length; reflexivity)) as LC.
      destruct (lex_cmp FL (subst_lex s (lex3 (rn_lex tgt))) (lex3 (rn_lex src))); [| |discriminate].
      * unfold M32 in *. nia.
      * apply orb_prop in H. destruct H as [Hs|H].
        -- apply Z.ltb_lt in Hs. unfold M32 in *. nia.
        -- apply andb_prop in H as [Hs Hd]. apply Z.eqb_eq in Hs. rewrite Hs.

           unfold dist_check in Hd.
           destruct (rn_dist tgt) as [[rt pt]|] eqn:Edt; [|discriminate].
           destruct (rn_dist src) as [[rs_ ps]|] eqn:Eds; [|discriminate].
           destruct (rn_ring src) as [rg|] eqn:Ers; [|discriminate].
           destruct (rn_ring tgt) as [rgt|] eqn:Ert; [|discriminate].
           apply andb_prop in Hd as [Hd Hne]. apply andb_prop in Hd as [Hd Hlp]. apply andb_prop in Hd as [Hd Hlr].
           apply andb_prop in Hd as [Hrt Hpt]. apply sv_eqb_sound in Hrt. apply sv_eqb_sound in Hpt.
           assert (DT : distv tgt (rho_sub rho' s) < distv src rho'); [|unfold M32 in *; nia].
           unfold distv. rewrite Edt, Eds, Ert, Ers. rewrite !Uv_sub, Hrt, Hpt. unfold NXf. rewrite Erl. fold (NXf rho').

           unfold ring_check in Hring. rewrite Ert, Ers in Hring.
           apply andb_prop in Hring as [Hring _]. apply andb_prop in Hring as [Hring _]. apply andb_prop in Hring as [HRR _].
           assert (ER : Rn (rho_sub rho' s) rgt = Rn rho' rg) by (unfold Rn; rewrite Uv_sub, (ueq_sound rho' FL _ _ HF HRR); reflexivity).
           rewrite ER.
           pose proof HR as (HRok & _ & _).
           pose proof (live_term_sound rg rho' rs_ HR Bn Hlr) as La.
           pose proof (live_term_sound rg rho' ps HR Bn Hlp) as Lb.
           pose proof (neq_fact_sound rho' FL rs_ ps HF Hne) as NE.
           pose proof (live_lt _ _ _ _ _ _ HRok La) as Ba.
           assert (EN : Uv rho' (NXT rs_) = NXf rho' (Uv rho' rs_)).
           { unfold NXT, Uv, NXf. apply U_LD4. unfold Uv, nval in *. lia. }
           rewrite EN.
           destruct (findex_step _ _ _ _ _ _ _ HRok La Lb NE) as [S1 S2].
           pose proof (ring_R_le_n _ _ _ _ _ HRok) as RN. unfold nval in *. unfold M32. lia.
Qed.

Definition check_rcfg (fuel : nat) (cutpcs : list Z) (cuts exits : list rnode) : bool := ltac2:(tb__ "0|2|
S1aS7eS2bS40Vcuts;A3S19S1eS66A1M0A1S18Lx;S6aVsegs;Vfuel;Vcutpcs;Vg;U0S86S2bS5S4dVcuts;A4S86S2bS5S2dS26S2bVcuts;Vexits;A3M1A4A7G0S7eS66S55G1A1R1A3Les;S1bX19x2A2").

Theorem rcfg_complete_auto : ltac2:(tb__ "0|2|
S1S24S1eS3aA1S1eS2bA1M0G0S1eS92A1S91OF_;F_;S88OF_;S12S18S5bR6R5R4R3A4S1cA3S2bS1S7fS2bR2R6A3S41RbR3R2A3S89Vsegs;S8aVsegs;R7S2dR4A1M1R3A4S88S16S68Vsegs;R8S86S2bS67S47RdA1RaA4S3fR5R4A2R1A5R7R1A1A2Lw;A3F_;F_;Frho;FE;S2bS1S7fS2bR2R8A3S41RcR3R2A3S89Vsegs;S8aVsegs;R8G1R3A4R7A3F_;F_;Frho;Fn;F_;F_;FQ;FK;Fexits;Fcuts;Fcutpcs;Ffuel;Frho0;").
Proof using .
  intros rho0 fuel cutpcs cuts exits K Q Hchk Hexits n rho Hin Hg.
  unfold check_rcfg in Hchk. apply andb_prop in Hchk as [Hok Hchk].
  destruct (cuts_edges segs fuel cutpcs g 0 (map src_state cuts) (map rn_state (cuts ++ exits))) as [es|] eqn:Hes; [|discriminate].
  eapply (rcfg_complete rho0 fuel cutpcs cuts exits es K Q Hok Hes); [|exact Hexits|exact Hin|exact Hg].
  apply Forall_forall. intros e He. apply rcheck_sound. exact (proj1 (forallb_forall _ _) Hchk e He).
Qed.

Lemma rmeas_nonneg : ltac2:(tb__ "0|0|
S2bS1S12S18S40R2A1S1cA3S75Z0S3fR3R2A2A2F_;Frho;Fnd;").
Proof using .
  intros nd rho Hok. destruct (node_okb_spec nd Hok) as (_ & _ & _ & _ & _ & Hph & Hs1 & Hs2 & _).
  unfold rmeas. pose proof (lex3_range rho (rn_lex nd)). pose proof (distv_range nd rho). pose proof (B64_pos 3).
  unfold M32 in *. nia.
Qed.

Lemma rmeas_lt_ph : ltac2:(tb__ "0|1|
S2bS2bS1S1S12S18S40R4A1S1cA3M0G0S71S2eR6A1S2eR5A1A2S71S3fR7R5A2S3fR6R4A2A2F_;F_;F_;Fr2;Fr1;Fb;Fa;").
Proof using .
  intros a b r1 r2 Ha Hb Hlt.
  destruct (node_okb_spec a Ha) as (_ & _ & _ & _ & _ & Hpha & Hs1a & Hs2a & _).
  destruct (node_okb_spec b Hb) as (_ & _ & _ & _ & _ & Hphb & Hs1b & Hs2b & _).
  unfold rmeas. pose proof (lex3_range r1 (rn_lex a)). pose proof (lex3_range r2 (rn_lex b)).
  pose proof (distv_range a r1). pose proof (distv_range b r2). pose proof (B64_pos 3). unfold M32 in *. nia.
Qed.

Lemma rmeas_lt_lex : ltac2:(tb__ "0|1|
S2bS2bS1S1S12S18S40R4A1S1cA3M0G0S12S3aS2eR6A1S2eR5A1A3S71S63R5S3eS31R7A1A1A2S63R4S3eS31R6A1A1A2A2S71S3fR8R6A2S3fR7R5A2A2F_;F_;F_;F_;Fr2;Fr1;Fb;Fa;").
Proof using .
  intros a b r1 r2 Ha Hb Heq Hlt.
  destruct (node_okb_spec a Ha) as (_ & _ & _ & _ & _ & Hpha & Hs1a & Hs2a & _).
  destruct (node_okb_spec b Hb) as (_ & _ & _ & _ & _ & Hphb & Hs1b & Hs2b & _).
  unfold rmeas. rewrite Heq. pose proof (lex3_range r1 (rn_lex a)). pose proof (lex3_range r2 (rn_lex b)).
  pose proof (distv_range a r1). pose proof (distv_range b r2). pose proof (B64_pos 3). unfold M32 in *. nia.
Qed.

Lemma rmeas_lt_sub : ltac2:(tb__ "0|1|
S2bS2bS1S1S12S18S40R4A1S1cA3M0G0S12S3aS2eR6A1S2eR5A1A3S12S3aS63R5S3eS31R7A1A1A2S63R4S3eS31R6A1A1A2A3S71S32R8A1S32R7A1A2S71S3fR9R7A2S3fR8R6A2A2F_;F_;F_;F_;F_;Fr2;Fr1;Fb;Fa;").
Proof using .
  intros a b r1 r2 Ha Hb Heq Hlex Hlt.
  unfold rmeas. rewrite Heq, Hlex.
  pose proof (distv_range a r1). pose proof (distv_range b r2). unfold M32 in *. nia.
Qed.

Lemma lex3_val1 : ltac2:(tb__ "0|4|
S1S62S0S12S3aS63R3S3eS22S1dS62S0A2M0S1fS62S0R2R1A4M1S25G0A1A3A1A2S73S73S74S65R3G1A2S72S64Z2A2A2S74S65R3S1fS62S0S69S1bA1S8Z0M2A1A4A2M3S72S64Z1A2A2A2S74G3S72S64G2A2A2A2A3Fe;Fd;Frho;").
Proof using . intros. unfold lex3, pad3. cbn [firstn app lex_val length Z.of_nat Pos.of_succ_nat Pos.succ]. lia. Qed.

Lemma lex3_val3 : ltac2:(tb__ "0|1|
S1S1dS62S0A2M0G0G0S12S3aS63R4S3eS22G0R3S22G0R2S22G0R1S25G0A1A3A3A3A1A2S73S73S74S65R4R3A2S72S64Z2A2A2S74S65R4R2A2S72S64Z1A2A2A2S74S65R4R1A2S72S64Z0A2A2A2A3Fc3;Fc2;Fc1;Frho;").
Proof using . intros. unfold lex3, pad3. cbn [firstn app lex_val length Z.of_nat Pos.of_succ_nat Pos.succ]. lia. Qed.

Lemma lex3_val0 : ltac2:(tb__ "0|2|
S1S12S3aS63R1S3eS25S1dS62S0A2A1A1A2S73S73S74S65R1S1fS62S0S69S1bA1S8Z0M0A1A4A2M1S72S64Z2A2A2S74G1S72S64Z1A2A2A2S74G1S72S64G0A2A2A2A3Frho;").
Proof using . intros. unfold lex3, pad3. cbn [firstn app lex_val length Z.of_nat Pos.of_succ_nat Pos.succ]. lia. Qed.

Lemma etriple_now : ltac2:(tb__ "0|1|
S88OF_;M0G0S88R3R1A1R3R2A1F_;Fw;S89Vsegs;R3R2A3F_;FQ;FP;").
Proof using . intros P Q H w Hw. exists w. split; [apply wsteps_refl | apply H; exact Hw]. Qed.

Lemma reenter_cut : ltac2:(tb__ "0|0|
S1eS92A1S91OF_;F_;S1S1eS2bA1S2bS1S3aS88S7fS2bR4R5A3S41R7R5R4A3S8aVsegs;R9S2dR6A1R5R3A5S75Z0S3fR7R6A2A2S71S3fR8R7A2R6A2S68Vsegs;RcS86S2bS67S47RbA1RaA4R7R6A5F_;F_;F_;F_;F_;Fw;Fbound;Frho';FN;Fcuts;Frho0;FK;").
Proof using .
  intros K rho0 cuts N rho' bound w Hin Hg Hsp H0 Hlt.
  exists (to_enodeR rho0 N), rho'. split; [apply in_map; exact Hin|].
  cbn [to_enodeR en_state en_ghost en_meas fst snd]. split; [exact Hg|]. split; [exact Hsp|]. lia.
Qed.

End RC.
