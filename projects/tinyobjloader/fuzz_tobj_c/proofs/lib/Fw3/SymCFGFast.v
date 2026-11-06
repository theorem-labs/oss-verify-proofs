(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "bool"; "list"; "option"; "andb"; "nat"; "false"; "prod"; "true"; "fst"; "snd"; "app"; "pair"; "None"; "Some"; "orb"; "length"; "negb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast"; "pcache"; "pc_ok"; "cleaf"; "cres"; "get_d"; "pc_0"; "uleq_r"; "cleaf_ok"; "force_d"; "sym_run_lc"; "@Corelib.Init.Logic"; "eq"; "and"; "True"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sstate"; "ss_facts"; "sv"; "sprop"; "ss_next"; "ss_lenient"; "ss_pc"; "sv_below"; "sv_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "edge"; "lnode"; "vnode"; "vdir"; "ln_state"; "vn_state"; "e_leaf"; "LMAX"; "check_cfg"; "check_cut"; "check_ecfg"; "check_ecfg2"; "e_src"; "e_sub"; "e_tgt"; "forallb_lazy"; "infer_sub"; "ln_rank"; "ln_vars"; "vn_rank"; "vn_var"; "cfg_edges"; "cuts_edges"; "echeck"; "echeck2"; "first_match"; "leaf_matches"; "leaf_matches1"; "leaves_edges"; "lex_check"; "xle"; "xleq"; "xlt"; "@Corelib.Numbers.BinNums"; "positive"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFGFast"; "cedge"; "cedge_ok"; "oall_ok_e"; "omap_fst_e"; "entails_c"; "leaf_matches_c"; "pf_of"; "sleq_r"; "first_match_c"; "leaf_matches1_c"; "leaves_edges_c"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub"; "wsub_id_below"; "sv_subst"; "@Stdlib.Lists.List"; "forallb"; "nth_error"; "@Corelib.Lists.ListDef"; "map"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "leaf"; "sleq_d"; "lf_state"; "sleq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFGFast.WithSegs"; "xleq_r"; "cfg_edges_c"; "check_cut_fast"; "check_cfg_fast"; "check_ecfg2_fast"; "check_ecfg_fast"; "cuts_edges_c"; "echeck2_c"; "echeck_c"; "lex_check_r"; "xle_r"; "xlt_r"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@Stdlib.ZArith.BinInt.Z"; "eqb"; "leb"; "ltb"; "@Stdlib.Arith.PeanoNat.Nat"; "leb"; "eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "entails"; "entails_cheap"; "entails_pfx"; "mkPF"; "mk_pf"; "pfacts"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool.
From Stdlib Require Import PArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymCFG SymStepFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition pf_of (ch : pcache) (facts : list sprop) : pfacts := ltac2:(tb__ "0|0|
S75Vfacts;S16Vch;A1S15Vch;Vfacts;A2A3").

Lemma pf_of_ok : ltac2:(tb__ "0|0|
S11S1S21A1S12R2R1A2S1bS77S50R3R2A2S76R2A1A3F_;Ffacts;Fch;").
Proof. intros ch facts H. unfold pf_of, mk_pf. rewrite (pc_0_ok _ _ H), (get_d_ok _ _ H). reflexivity. Qed.

Definition entails_c (ch : pcache) (L T : sstate) (s : wsub) : bool * pcache := ltac2:(tb__ "0|1|
S0S6S0S11A2L_;S73VL;VT;Vs;A3S19Vch;S1fVL;A1M0A2S11SbS0S11S74S50R1G0A2VL;VT;Vs;A4R1A4Tch1;SbS0S11S5Vch;A4X0x2").

Lemma entails_c_ok : ltac2:(tb__ "0|0|
S11S1eS1eS55S12R4S1fR3A1A2S14S0S1fR4A1S4eR5R4R3R2A4S72R4R3R2A3A4F_;Fs;FT;FL;Fch;").
Proof.
  intros ch L T s H. unfold entails_c, entails.
  destruct (entails_cheap L T s); [|apply cres_ret; exact H].
  cbv zeta. rewrite (pf_of_ok _ _ (force_d_ok _ _ H)). apply cres_ret. apply force_d_ok; exact H.
Qed.

Definition sleq_r (ch : pcache) (facts : list sprop) (a : sv) (k : Z) (b : sv) : bool := ltac2:(tb__ "0|0|
S0S0L_;S5dS16Vch;A1Va;Vk;Vb;A4S7S5dS15Vch;Vfacts;A2Va;Vk;Vb;A4X0x2").
Lemma sleq_r_ok : ltac2:(tb__ "0|0|
S11S1S21A1S20S49S20S12R5R4A2S1bS0S51R6R5R4R3R2A5S5fR5R4R3R2A4A3F_;Fb;Fk;Fa;Ffacts;Fch;").
Proof. intros ch facts a k b H. unfold sleq_r, sleq. rewrite (pc_0_ok _ _ H), (get_d_ok _ _ H). reflexivity. Qed.

Definition leaf_matches1_c (g : positive) (ch : pcache) (L X : sstate) : option wsub * pcache := ltac2:(tb__ "0|5|
S0S6S2S55A1M0S11A2M1L_;M2S6dS24VL;A1S24VX;A1A2S37Vg;VL;VX;A3S55G2S56R1Vg;A2S6S0S11A2G1Lx;S4eVch;VL;VX;R1A4S0S11SbG0S11S0G0Lb;R2SdS55R3A2ScS55A1M3X0x2R1A4Lch1;Lb;X6x1SbG0S11G3Vch;A4M4X0x2Ts;G4X0x2").

Lemma leaf_matches1_c_ok : ltac2:(tb__ "0|1|
S48S11S1eS1eS12R3S1fR2A1A2S14S2S55A1M0S1fR3A1S53R5R4R3R2A4S0G0L_;S42R5R3R2A3SdS55S37R5R3R2A3A2ScS55A1X0x2A4F_;FX;FL;Fch;Fg;").
Proof.
  intros g ch L X H. unfold leaf_matches1_c, leaf_matches1.
  destruct (ss_pc L =? ss_pc X); [|apply cres_ret; exact H]. cbv zeta.
  destruct (wsub_id_below (infer_sub g L X) g); [|apply cres_ret; exact H].
  destruct (entails_c_ok ch L X (infer_sub g L X) H) as (ch1 & -> & H1).
  apply cres_ret; exact H1.
Qed.

Fixpoint leaf_matches_c (g : positive) (ch : pcache) (L : sstate) (targets : list sstate) : bool :=
  match targets with
  | [] => false
  | X :: t => let '(r, ch1) := leaf_matches1_c g ch L X in
              match r with Some _ => true | None => leaf_matches_c g ch1 L t end
  end.

Lemma leaf_matches_c_eq : ltac2:(tb__ "0|0|
S48S1eS1S1eA1S11S12R1S1fR3A1A2S1bS0S4fR5R2R4R3A4S41R5R4R3A3A3F_;Fch;Ftargets;FL;Fg;").
Proof.
  intros g L targets. unfold leaf_matches.
  induction targets as [|X t IH]; intros ch H; cbn [leaf_matches_c existsb_lazy]; [reflexivity|].
  destruct (leaf_matches1_c_ok g ch L X H) as (ch1 & -> & H1).
  destruct (leaf_matches1 g L X); [reflexivity | apply IH; exact H1].
Qed.

Fixpoint first_match_c (g : positive) (ch : pcache) (L : sstate) (targets : list sstate) (j : nat)
  : option (nat * wsub) * pcache :=
  match targets with
  | [] => (None, ch)
  | X :: rest =>
      let '(r, ch1) := leaf_matches1_c g ch L X in
      match r with
      | Some s => (Some (j, s), ch1)
      | None => first_match_c g ch1 L rest (S j)
      end
  end.

Lemma first_match_c_ok : ltac2:(tb__ "0|0|
S48S1eS1S1eA1S11S4S12R2S1fR4A1A2S14S2S6S4S55A2A1S1fR5A1S52R6R3R5R4R2A5S40R6R5R4R2A4A4F_;Fj;Fch;Ftargets;FL;Fg;").
Proof.
  intros g L targets. induction targets as [|X rest IH]; intros ch j H; cbn [first_match_c first_match].
  - apply cres_ret; exact H.
  - destruct (leaf_matches1_c_ok g ch L X H) as (ch1 & -> & H1).
    destruct (leaf_matches1 g L X); [apply cres_ret; exact H1 | apply IH; exact H1].
Qed.

Lemma forallb_lazy_fst : forall {A} (ok : A * pcache -> Prop) (fc : A * pcache -> bool) (f : A -> bool) l,
  Forall ok l -> (forall x, ok x -> fc x = f (fst x)) ->
  forallb_lazy fc l = forallb_lazy f (map fst l).
Proof.
  intros A ok fc f l Hall Hf. induction Hall as [|x t Hx _ IH]; cbn [forallb_lazy map]; [reflexivity|].
  rewrite (Hf x Hx), IH. reflexivity.
Qed.

Lemma forallb_fst : forall {A} (ok : A * pcache -> Prop) (fc : A * pcache -> bool) (f : A -> bool) l,
  Forall ok l -> (forall x, ok x -> fc x = f (fst x)) ->
  forallb fc l = forallb f (map fst l).
Proof.
  intros A ok fc f l Hall Hf. induction Hall as [|x t Hx _ IH]; cbn [forallb map]; [reflexivity|].
  rewrite (Hf x Hx), IH. reflexivity.
Qed.

Definition cedge : Type := (edge * pcache)%type.
Definition cedge_ok (ec : cedge) : Prop := ltac2:(tb__ "0|0|
S12S9S27S11Vec;A3S1fS2dS8S27S11Vec;A3A1A1A2").

Definition omap_fst_e (r : option (list cedge)) : option (list edge) := ltac2:(tb__ "0|2|
S2S1S4aA1M0A1S2S1S27A1M1A1Lr;Vr;G0SdG1S5aS6S27S11A2S27S8S27S11A2R1A4A2Ll;ScG1A1X2x2").
Definition oall_ok_e (r : option (list cedge)) : Prop := ltac2:(tb__ "0|1|
S2S1S4aA1M0A1OLr;Vr;G0S5bS4aS4bR1A3Ll;S1dX2x2").

Fixpoint leaves_edges_c (g : positive) (i : nat) (lcs : list cleaf) (targets : list sstate) : option (list cedge) :=
  match lcs with
  | [] => Some []
  | lc :: rest =>
      let '(r, ch1) := first_match_c g (snd lc) (lf_state (fst lc)) targets 0 in
      match r, leaves_edges_c g i rest targets with
      | Some (j, s), Some es => Some ((mkEdge i (lf_state (fst lc)) j s, ch1) :: es)
      | _, _ => None
      end
  end.

Lemma leaves_edges_c_ok : ltac2:(tb__ "0|1|
S48S4S1S1eA1S1S13A1S5bS13S18R1A3S1cS1bS2S1S27A1A1S4dS54R5R4R2R3A4M0A1S43R5R4S5aS6S5cS11A2S5cS8S5cS11A2R2A4R3A4A3S4cG0A1A2F_;Flcs;Ftargets;Fi;Fg;").
Proof.
  intros g i targets lcs Hall. induction Hall as [|lc rest Hlc _ IH]; cbn [leaves_edges_c leaves_edges map].
  - split; [reflexivity | constructor].
  - destruct (first_match_c_ok g (lf_state (fst lc)) targets (snd lc) 0 Hlc) as (ch1 & -> & H1).
    destruct IH as [IE IO]. rewrite <- IE.
    destruct (first_match g (lf_state (fst lc)) targets 0) as [[j s]|]; [|split; [reflexivity | exact I]].
    destruct (leaves_edges_c g i rest targets) as [es|]; [|split; [reflexivity | exact I]].
    cbn [omap_fst_e oall_ok_e map fst] in *. split; [reflexivity|].
    constructor; [exact H1 | exact IO].
Qed.

Section WithSegs.
Variable segs : list Segment.

Definition check_cut_fast (fuel : nat) (cutpcs : list Z) (g : positive)
           (targets : list sstate) (T : sstate) : bool := ltac2:(tb__ "0|2|
S0S0L_;S6cVg;S22VT;A1A2S2S1S13A1M0A1S0Lx;S1aVsegs;Vfuel;Vcutpcs;VT;S7A5G0S36S6S5cS11A2M1G1S4fVg;S9S5cS11R1A3S5eS8S5cS11R1A3A1Vtargets;A4Llc;R1A3Llcs;S5X2x2S5X0x2").

Theorem check_cut_fast_eq : ltac2:(tb__ "0|0|
S4S1S49A1S48S1S1eA1S1eS1bS0S62R5R4R3R2R1A5S30Vsegs;R5R4R3R2R1A6A3FT;Ftargets;Fg;Fcutpcs;Ffuel;").
Proof.
  intros fuel cutpcs g targets T. unfold check_cut_fast, check_cut.
  destruct (Pos.leb g (ss_next T)); [|reflexivity].
  rewrite <- (sym_run_lc_eq segs fuel cutpcs T true).
  destruct (sym_run_lc segs fuel cutpcs T true) as [lcs|] eqn:E; [|reflexivity]. cbn [omap_fst].
  apply (forallb_lazy_fst (cleaf_ok)); [exact (sym_run_lc_ok segs _ _ _ _ _ E)|].
  intros lc Hlc. apply leaf_matches_c_eq. exact Hlc.
Qed.

Definition check_cfg_fast (fuel : nat) (cutpcs : list Z) (g : positive)
           (cuts exits : list sstate) : bool := ltac2:(tb__ "0|0|
S36S1eS62Vfuel;Vcutpcs;Vg;SaS1eVcuts;Vexits;A3A4Vcuts;A3").

Lemma forallb_lazy_ext : forall {A} (f h : A -> bool) l, (forall x, f x = h x) -> forallb_lazy f l = forallb_lazy h l.
Proof. intros A f h l H. induction l as [|x t IH]; cbn [forallb_lazy]; [reflexivity|]. rewrite (H x), IH. reflexivity. Qed.

Theorem check_cfg_fast_eq : ltac2:(tb__ "0|1|
S4S1S49A1S48S1S1eA1M0G0S1bS0S63R5R4R3R2R1A5S2fVsegs;R5R4R3R2R1A6A3Fexits;Fcuts;Fg;Fcutpcs;Ffuel;").
Proof.
  intros. unfold check_cfg_fast, check_cfg. apply forallb_lazy_ext. intros T. apply check_cut_fast_eq.
Qed.

Corollary check_cut_fast_ok : ltac2:(tb__ "0|0|
S4S1S49A1S48S1S1eA1S1eS1bS0S62R5R4R3R2R1A5S7A3S1bS0S30Vsegs;R6R5R4R3R2A6S7A3F_;FT;Ftargets;Fg;Fcutpcs;Ffuel;").
Proof. intros fuel cutpcs g targets T H. rewrite <- check_cut_fast_eq. exact H. Qed.

Corollary check_cfg_fast_ok : ltac2:(tb__ "0|1|
S4S1S49A1S48S1S1eA1M0G0S1bS0S63R5R4R3R2R1A5S7A3S1bS0S2fVsegs;R6R5R4R3R2A6S7A3F_;Fexits;Fcuts;Fg;Fcutpcs;Ffuel;").
Proof. intros fuel cutpcs g cuts exits H. rewrite <- check_cfg_fast_eq. exact H. Qed.

Fixpoint cuts_edges_c (fuel : nat) (cutpcs : list Z) (g : positive) (i : nat)
         (cuts : list sstate) (targets : list sstate) : option (list cedge) :=
  match cuts with
  | [] => Some []
  | T :: rest =>
      if negb (Pos.leb g (ss_next T)) then None else
      match sym_run_lc segs fuel cutpcs T true with
      | Some lcs =>
          match leaves_edges_c g i lcs targets, cuts_edges_c fuel cutpcs g (S i) rest targets with
          | Some es, Some es' => Some (es ++ es')
          | _, _ => None
          end
      | None => None
      end
  end.

Lemma cuts_edges_c_ok : ltac2:(tb__ "0|2|
S4S1S49A1S48S1S1eA1M0G0S4S1cS1bS2S1S27A1A1S4dS66R6R5R4R1R2R3A6M1A1S3dVsegs;R6R5R4R1R2R3A7A3S4cG1A1A2Fi;Fcuts;Ftargets;Fg;Fcutpcs;Ffuel;").
Proof.
  intros fuel cutpcs g targets. induction cuts as [|T rest IH]; intros i; cbn [cuts_edges_c cuts_edges].
  - split; [reflexivity | constructor].
  - destruct (negb (Pos.leb g (ss_next T))); [split; [reflexivity | exact I]|].
    rewrite <- (sym_run_lc_eq segs fuel cutpcs T true).
    destruct (sym_run_lc segs fuel cutpcs T true) as [lcs|] eqn:E; [|split; [reflexivity | exact I]].
    cbn [omap_fst].
    destruct (leaves_edges_c_ok g i targets lcs (sym_run_lc_ok segs _ _ _ _ _ E)) as [LE LO].
    destruct (IH (S i)) as [IE IO]. rewrite <- LE, <- IE.
    destruct (leaves_edges_c g i lcs targets) as [es|]; [|split; [reflexivity | exact I]].
    destruct (cuts_edges_c fuel cutpcs g (S i) rest targets) as [es'|]; [|split; [reflexivity | exact I]].
    cbn [omap_fst_e oall_ok_e] in *. split; [rewrite map_app; reflexivity | apply Forall_app; split; assumption].
Qed.

Definition cfg_edges_c (fuel : nat) (cutpcs : list Z) (g : positive) (cuts exits : list sstate) : option (list cedge) := ltac2:(tb__ "0|0|
S66Vfuel;Vcutpcs;Vg;U0Vcuts;SaS1eVcuts;Vexits;A3A6").

Lemma cfg_edges_c_ok : ltac2:(tb__ "0|2|
S4S1S49A1S48S1S1eA1M0G0S1cS1bS2S1S27A1A1S4dS61R5R4R3R2R1A5M1A1S3cVsegs;R5R4R3R2R1A6A3S4cG1A1A2Fexits;Fcuts;Fg;Fcutpcs;Ffuel;").
Proof. intros. apply cuts_edges_c_ok. Qed.

Lemma edges_check_eq : ltac2:(tb__ "0|3|
S2S1S4aA1M0A1M1S27S0F_;S4aS0F_;S4cR3A1S4aS4bR1A1S1bS0R4R2A1R5S8S27S11R2A3A1A3F_;Fec;S1bS0G1S0Lr;R5G0S58S4aR4R1A3Les;S5X2x2S2S1S27A1M2A1S0Lx;S4dR5A1G2S58S27R5R1A3Les;S5X2x2A3F_;F_;FPc;FP;Fr;").
Proof.
  intros [es|] P Pc Hok HP; cbn [omap_fst_e oall_ok_e] in *; [|reflexivity].
  apply (forallb_fst cedge_ok); assumption.
Qed.

Definition echeck_c (g : positive) (nodes : list vnode) (ec : cedge) : bool := ltac2:(tb__ "0|6|
S8S27S11Vec;A3S27S2S29A1S0Lx;M0S59S29Vnodes;S33R1A1A3S29G0S59S29Vnodes;S35R2A1A3S29S3S3S3S3S56S34R3A1M1Vg;A2S6cVg;S22S2cR2A1A1M2A2A2S25G2S3bR2A1M3A2A2S6eZ0S3aR1A1M4A2A2SeS6fG4S3aR2A1M5A2S3S6dG4G5A2S17S9S27S11Vec;A3S1fS2dR3A1A1S57G1S3bR1A1A2Z1G3A5A2A2A2Lnj;S5X2x2Lni;S5X2x2Te;").

Lemma echeck_c_eq : ltac2:(tb__ "0|0|
S48S1S29A1S4aS4bR1A1S1bS0S68R4R3R2A3S3eR4R3S8S27S11R2A3A3A3F_;Fec;Fnodes;Fg;").
Proof.
  intros g nodes ec H. unfold echeck_c, echeck. cbv zeta.
  destruct (nth_error nodes (e_src (fst ec))); [|reflexivity].
  destruct (nth_error nodes (e_tgt (fst ec))); [|reflexivity].
  rewrite (uleq_r_ok _ _ _ _ _ H). reflexivity.
Qed.

Definition check_ecfg_fast (fuel : nat) (cutpcs : list Z) (g : positive) (cuts exits : list vnode) : bool := ltac2:(tb__ "0|1|
S3S58S29S29S10S23S2cR1A1A1A1Ln;Vcuts;A3S2S1S4aA1M0A1S0Lx;S61Vfuel;Vcutpcs;Vg;S5aS29S1eS2cVcuts;A4S5aS29S1eS2cVexits;A4A5G0S58S4aS68Vg;SaS29Vcuts;Vexits;A3A2R1A3Les;S5X2x2A2").

Theorem check_ecfg_fast_eq : ltac2:(tb__ "0|1|
S4S1S49A1S48S1S29A1M0G0S1bS0S65R5R4R3R2R1A5S31Vsegs;R5R4R3R2R1A6A3Fexits;Fcuts;Fg;Fcutpcs;Ffuel;").
Proof.
  intros. unfold check_ecfg_fast, check_ecfg. f_equal.
  destruct (cfg_edges_c_ok fuel cutpcs g (map vn_state cuts) (map vn_state exits)) as [E O].
  rewrite <- E. apply edges_check_eq; [exact O|]. intros ec Hec. apply echeck_c_eq; exact Hec.
Qed.

Corollary check_ecfg_fast_ok : ltac2:(tb__ "0|1|
S4S1S49A1S48S1S29A1M0G0S1bS0S65R5R4R3R2R1A5S7A3S1bS0S31Vsegs;R6R5R4R3R2A6S7A3F_;Fexits;Fcuts;Fg;Fcutpcs;Ffuel;").
Proof. intros fuel cutpcs g cuts exits H. rewrite <- check_ecfg_fast_eq. exact H. Qed.

Definition xleq_r (ch : pcache) (facts : list sprop) (sgn : bool) (a : sv) (k : Z) (b : sv) : bool := ltac2:(tb__ "0|0|
S0S0Lsgn;Vsgn;S51Vch;Vfacts;Va;Vk;Vb;A5S17Vch;Vfacts;Va;Vk;Vb;A5X0x2").
Definition xlt_r (ch : pcache) (facts : list sprop) (d : vdir) (tgt src : sv) : bool := ltac2:(tb__ "0|1|
S2aS0Ld;Vd;S0S60Vch;Vfacts;R1Vtgt;Z1M0Vsrc;A6Lsgn;S0S60Vch;Vfacts;R1Vsrc;G0Vtgt;A6Lsgn;X2ax2").
Definition xle_r (ch : pcache) (facts : list sprop) (d : vdir) (tgt src : sv) : bool := ltac2:(tb__ "0|1|
SeS26Vtgt;Vsrc;A2S2aS0Ld;Vd;S0S60Vch;Vfacts;R1Vtgt;Z0M0Vsrc;A6Lsgn;S0S60Vch;Vfacts;R1Vsrc;G0Vtgt;A6Lsgn;X2ax2A2").
Fixpoint lex_check_r (ch : pcache) (facts : list sprop) (s : wsub) (tgt src : list (vdir * sv)) : bool :=
  match tgt, src with
  | (dt, et) :: trest, (ds, es) :: srest =>
      vdir_eqb dt ds
      && (xlt_r ch facts ds (sv_subst s et) es
          || (xle_r ch facts ds (sv_subst s et) es && lex_check_r ch facts s trest srest))
  | _, _ => false
  end.

Lemma xleq_r_ok : ltac2:(tb__ "0|0|
S11S1S21A1S0S20S49S20S12R6R5A2S1bS0S60R7R6R5R4R3R2A6S46R6R5R4R3R2A5A3F_;Fb;Fk;Fa;Fsgn;Ffacts;Fch;").
Proof. intros ch facts sgn a k b H. unfold xleq_r, xleq. rewrite (sleq_r_ok _ _ _ _ _ H), (uleq_r_ok _ _ _ _ _ H). reflexivity. Qed.
Lemma xlt_r_ok : ltac2:(tb__ "0|0|
S11S1S21A1S2aS20S20S12R5R4A2S1bS0S6bR6R5R4R3R2A5S47R5R4R3R2A4A3F_;Fs;Ft;Fd;Ffacts;Fch;").
Proof. intros ch facts d t s H. unfold xlt_r, xlt. destruct d; apply xleq_r_ok; exact H. Qed.
Lemma xle_r_ok : ltac2:(tb__ "0|0|
S11S1S21A1S2aS20S20S12R5R4A2S1bS0S6aR6R5R4R3R2A5S45R5R4R3R2A4A3F_;Fs;Ft;Fd;Ffacts;Fch;").
Proof. intros ch facts d t s H. unfold xle_r, xle. destruct d; rewrite (xleq_r_ok _ _ _ _ _ _ H); reflexivity. Qed.
Lemma lex_check_r_ok : ltac2:(tb__ "0|1|
S11S1S21A1S55S1S6S2aS20A2A1M0G0S12R5R4A2S1bS0S69R6R5R4R3R2A5S44R5R4R3R2A4A3F_;Fsrc;Ftgt;Fs;Ffacts;Fch;").
Proof.
  intros ch facts s tgt. induction tgt as [|[dt et] trest IH]; intros src H; cbn [lex_check_r lex_check]; [reflexivity|].
  destruct src as [|[ds es] srest]; [reflexivity|].
  rewrite (xlt_r_ok _ _ _ _ _ H), (xle_r_ok _ _ _ _ _ H), (IH srest H). reflexivity.
Qed.

Definition echeck2_c (g : positive) (nodes : list lnode) (ec : cedge) : bool := ltac2:(tb__ "0|9|
S8S27S11Vec;A3S27S2S28A1S0Lx;M0S59S28Vnodes;S33R1A1A3S28G0S59S28Vnodes;S35R2A1A3S28S3S3S3S3S3S3S56S34R3A1M1Vg;A2S6cVg;S22S2bR2A1A1A2A2S58S6S2aS20A2M2G2S25S22S2bR3A1A1S9S2aS20R1A3A2Lc;S39R2A1M3A3A2S70SfG2G3A2M4S2eA2A2S70SfG2S39R1A1M5A2M6S2eA2A2S6eZ0S38R1A1M7A2A2SeS6fG7S38R2A1M8A2S3S3S6dG7G8A2S71G6G4A2A2S69S9S27S11Vec;A3S1fS2dR3A1A1G1G5G3A5A2A2A2Lnj;S5X2x2Lni;S5X2x2Te;").

Lemma echeck2_c_eq : ltac2:(tb__ "0|0|
S48S1S28A1S4aS4bR1A1S1bS0S67R4R3R2A3S3fR4R3S8S27S11R2A3A3A3F_;Fec;Fnodes;Fg;").
Proof.
  intros g nodes ec H. unfold echeck2_c, echeck2. cbv zeta.
  destruct (nth_error nodes (e_src (fst ec))); [|reflexivity].
  destruct (nth_error nodes (e_tgt (fst ec))); [|reflexivity].
  rewrite (lex_check_r_ok _ _ _ _ _ H). reflexivity.
Qed.

Definition check_ecfg2_fast (fuel : nat) (cutpcs : list Z) (g : positive) (cuts exits : list lnode) : bool := ltac2:(tb__ "0|1|
S3S58S28S28S10S23S2bR1A1A1A1Ln;Vcuts;A3S2S1S4aA1M0A1S0Lx;S61Vfuel;Vcutpcs;Vg;S5aS28S1eS2bVcuts;A4S5aS28S1eS2bVexits;A4A5G0S58S4aS67Vg;SaS28Vcuts;Vexits;A3A2R1A3Les;S5X2x2A2").

Theorem check_ecfg2_fast_eq : ltac2:(tb__ "0|1|
S4S1S49A1S48S1S28A1M0G0S1bS0S64R5R4R3R2R1A5S32Vsegs;R5R4R3R2R1A6A3Fexits;Fcuts;Fg;Fcutpcs;Ffuel;").
Proof.
  intros. unfold check_ecfg2_fast, check_ecfg2. f_equal.
  destruct (cfg_edges_c_ok fuel cutpcs g (map ln_state cuts) (map ln_state exits)) as [E O].
  rewrite <- E. apply edges_check_eq; [exact O|]. intros ec Hec. apply echeck2_c_eq; exact Hec.
Qed.

Corollary check_ecfg2_fast_ok : ltac2:(tb__ "0|1|
S4S1S49A1S48S1S28A1M0G0S1bS0S64R5R4R3R2R1A5S7A3S1bS0S32Vsegs;R6R5R4R3R2A6S7A3F_;Fexits;Fcuts;Fg;Fcutpcs;Ffuel;").
Proof. intros fuel cutpcs g cuts exits H. rewrite <- check_ecfg2_fast_eq. exact H. Qed.

End WithSegs.
