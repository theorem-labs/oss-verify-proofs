(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "bool"; "list"; "false"; "prod"; "option"; "andb"; "nat"; "true"; "Some"; "fst"; "None"; "snd"; "app"; "length"; "S"; "cons"; "negb"; "nil"; "orb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sstate"; "sv"; "ss_facts"; "sobj"; "sprop"; "ss_next"; "SLit"; "SAlu"; "cell"; "ss_objs"; "sv_below"; "SVar"; "SMd"; "ob_base"; "ob_hi"; "ob_lo"; "sprop_below"; "sv_eqb"; "SAluW"; "SExt"; "SLBytes"; "SMdW"; "c_off"; "is_arr"; "mkObj"; "ob_cells"; "ob_dflt"; "swf"; "@Corelib.Init.Logic"; "eq"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "N"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVA"; "amode"; "aedesc"; "am_eqb"; "am_below"; "am_subst"; "ad_am"; "ad_rank"; "ad_state"; "ad_tv"; "ad_var"; "amL_ok"; "new_objs_okA"; "pl_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "mk_pf"; "uleq_pf"; "pfacts"; "select"; "entails"; "entails_cheap"; "entails_fr"; "entails_pfx"; "pf_dg"; "complement"; "nodupN"; "pf_d0"; "witnesses_pf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub"; "wsub_id_below"; "sv_subst"; "obj_subst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObjFast"; "mk_pf_x"; "shift_ok_p"; "merge_objs_at_p"; "rebase_obj_at_p"; "split_obj_at_p"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVAx"; "nstep"; "run_nsteps"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform"; "xform"; "apply_xforms"; "apply_xform"; "select_ok"; "@Stdlib.ZArith.BinInt.Z"; "leb"; "ltb"; "opp"; "pow"; "eqb"; "add"; "min"; "@Stdlib.Lists.List"; "forallb"; "existsb"; "nth_error"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "tv_below"; "svT"; "tv_sub_eqb"; "robjs_check"; "T_afterN"; "call_checkT"; "import_tv"; "robj_stack"; "robj_tracked"; "tvL_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast"; "entails_p"; "sleq_pf"; "norm_xu_p"; "entails_fr_p"; "run_nsteps_p"; "apply_xforms_p"; "contK_check_fast"; "entA_check_p"; "entE_check_p"; "reent_check_p"; "robjs_check_p"; "unbase_obj_at_p"; "entE_check_fast"; "landAs_check_fast"; "nz_entry_check_p"; "posts_check_p"; "pposts_check_p"; "pure_site_check_fast"; "renormK_fast"; "robj_stack_p"; "run_nsteps_fast"; "site_check_fast"; "apply_xform_p"; "apply_xforms_fast"; "contA_check_fast"; "contEJ_check_fast"; "contE_check_fast"; "cont_check_fast"; "entA_check_fast"; "entails_fast"; "entails_fr_fast"; "landA_check_fast"; "norm_xu_fast"; "post_check_p"; "ppost_check_p"; "robjs_check_fast"; "unbase_obj_at_fast"; "unbase_obj_p"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "leaf"; "set_objs"; "sleq_d"; "itv_lin"; "lf_state"; "mk_addk"; "snorm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVAy"; "cdesc"; "entA_check"; "gcS"; "pure_site_check"; "site_check"; "subsetb"; "contA_check"; "cont_check"; "gc_facts"; "landA_check"; "landAs_check"; "permb"; "post_check"; "posts_check"; "ppost_check"; "pposts_check"; "reent_check"; "renormK"; "@Corelib.Lists.ListDef"; "map"; "firstn";
"skipn"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "aluop"; "mulop"; "M_MUL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVx"; "norm_xu"; "entE_check"; "contEJ_check"; "contE_check"; "cont_check"; "nz_entry_check"; "nz_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "with_facts"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj"; "shift_off"; "shift_cell"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase"; "unbase_obj_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "mconsts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "call_check"; "import_post"; "import_sub"; "wsub_dom_below"; "@Stdlib.Arith.PeanoNat.Nat"; "ltb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import MallocModel MallocInv MallocLayout MallocIface MallocLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymEntail SymCFG SymSummary SymObj Glue3 SymDigFast SymObjFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import ObjUnbase ObjXform TobjJV TobjJVx TobjJVA TobjJVAx TobjJVAy.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Lemma forallb_ext_p : forall {A} (f g : A -> bool) (l : list A), (forall a, f a = g a) -> forallb f l = forallb g l.
Proof. intros A f g l H. induction l as [|a r IH]; cbn [forallb]; [reflexivity|]. rewrite H, IH. reflexivity. Qed.

Definition apply_xform_p (pf : pfacts) (S : sstate) (x : xform) : option sstate := ltac2:(tb__ "0|2|
S58S4S13A1M0Lx;Vx;S6S14S55Vpf;VS;R2R1A4Lmid;Li;S6S53Vpf;VS;R1A3Li;S6S54Vpf;VS;R1A3Li;S1S6A1S0G0L_;S5bSdS16S1cVS;A1M1A2R1A2S8S13S9bVS;S43G1R1A2A2A2SaS13A1X0x2Lidxs;X58x4").
Lemma apply_xform_p_eq : ltac2:(tb__ "0|0|
S13S58S2fS4S13A1S86S40S15R2A1A1R2R1A3S5aR2R1A2A3Fx;FS;").
Proof. intros S [i mid|i|i|idxs]; reflexivity. Qed.
Lemma apply_xform_facts : ltac2:(tb__ "0|0|
S13S58S13S2fS4S13A1S5aR3R2A2S8S13R1A2A3S2fS1S17A1S15R2A1S15R4A1A3F_;FS';Fx;FS;").
Proof.
  intros S [i mid|i|i|idxs] S' H; cbn [apply_xform] in H.
  - exact (split_obj_at_facts _ _ _ _ H).
  - exact (merge_objs_at_facts _ _ _ H).
  - exact (rebase_obj_at_facts _ _ _ H).
  - destruct (select_ok (length (ss_objs S)) idxs); [|discriminate]. injection H as <-. reflexivity.
Qed.

Fixpoint apply_xforms_p (pf : pfacts) (S : sstate) (xs : list xform) : option sstate :=
  match xs with
  | [] => Some S
  | x :: r => match apply_xform_p pf S x with Some S' => apply_xforms_p pf S' r | None => None end
  end.
Lemma apply_xforms_p_eq : ltac2:(tb__ "0|0|
S1S58A1S13S2fS4S13A1S75S40S15R1A1A1R1R2A3S59R1R2A2A3FS;Fxs;").
Proof.
  induction xs as [|x r IH]; intros S; cbn [apply_xforms_p apply_xforms]; [reflexivity|].
  rewrite apply_xform_p_eq. destruct (apply_xform S x) as [S'|] eqn:E; [|reflexivity].
  rewrite <- (apply_xform_facts _ _ _ E). apply IH.
Qed.
Lemma apply_xforms_facts : ltac2:(tb__ "0|0|
S1S58A1S13S13S2fS4S13A1S59R2R3A2S8S13R1A2A3S2fS1S17A1S15R2A1S15R3A1A3F_;FS';FS;Fxs;").
Proof.
  induction xs as [|x r IH]; intros S S' H; cbn [apply_xforms] in H; [injection H as <-; reflexivity|].
  destruct (apply_xform S x) as [S1|] eqn:E; [|discriminate].
  rewrite (IH _ _ H). exact (apply_xform_facts _ _ _ E).
Qed.
Definition apply_xforms_fast (S : sstate) (xs : list xform) : option sstate := ltac2:(tb__ "0|0|
S75S51S15VS;A1A1VS;Vxs;A3").
Lemma apply_xforms_fast_eq : ltac2:(tb__ "0|0|
S13S1S58A1S2fS4S13A1S87R2R1A2S59R2R1A2A3Fxs;FS;").
Proof. intros. unfold apply_xforms_fast. rewrite mk_pf_x_eq. apply apply_xforms_p_eq. Qed.

Definition unbase_obj_p (pf : pfacts) (o : sobj) (c0 : Z) : option sobj := ltac2:(tb__ "0|7|
Sa0Vc0;A1S30S3S30S30A2S4S16A1M0Lx;S9dS48Vpf;A1S20Vo;A1M1A2S30S30S0G0L_;S5S5S5S5S5S5S5cR2R1A2S5cZ0S61R2R3A2A2A2S5dS61R1R3A2S5fZ2Z40A2A2A2S52Vpf;S22Vo;A1M2S5eR3A1M3A3A2S52Vpf;S21Vo;A1M4G3A3A2S63S1bS1bS52Vpf;S29R1A1S5eR4A1A3Lcl;S2cVo;A1M5A3A2S10S2aS2dVo;A1M6A1A1A2S8S16S2bS9fG1Vc0;A2Sc3G2G3A2Sc3G4G3A2Sb3S1bS1bSc4G3A1G5A4G6A5A2SaS16A1X0x2Lh;Ll;X3x1Tc;").
Definition unbase_obj_at_p (pf : pfacts) (S : sstate) (i : nat) (c0 : Z) : option sstate := ltac2:(tb__ "0|3|
S4S16A1S4S13A1Lx;M0S65S16S1cVS;A1M1Vi;A3S16G0S95Vpf;R1Vc0;A3S16S8S13S9bVS;ScS16Sb4S16Vi;G1A3SfS16R1Sb5S16SeVi;A1G1A3A3A3A2A2Lo';SaS13A1M2X4x2Lo;G2X4x2").
Lemma unbase_obj_at_p_eq : ltac2:(tb__ "0|0|
S13S6S30S2fS4S13A1S7bS40S15R3A1A1R3R2R1A4Sc5R3R2R1A3A3Fc0;Fi;FS;").
Proof. reflexivity. Qed.
Definition unbase_obj_at_fast (S : sstate) (i : nat) (c0 : Z) : option sstate := ltac2:(tb__ "0|0|
S7bS51S15VS;A1A1VS;Vi;Vc0;A4").
Lemma unbase_obj_at_fast_eq : ltac2:(tb__ "0|0|
S13S6S30S2fS4S13A1S94R3R2R1A3Sc5R3R2R1A3A3Fc0;Fi;FS;").
Proof. intros. unfold unbase_obj_at_fast. rewrite mk_pf_x_eq. apply unbase_obj_at_p_eq. Qed.

Definition norm_xu_p (pf : pfacts) (xs : list xform) (i : nat) (c : Z) (T : sstate) : option sstate := ltac2:(tb__ "0|1|
S4S13A1M0G0Lx;S75Vpf;VT;Vxs;A3S13S7bVpf;R1Vi;Vc;A4LT1;SaS13A1X4x2").
Lemma norm_xu_p_eq : ltac2:(tb__ "0|0|
S1S58A1S6S30S13S2fS4S13A1S72S40S15R1A1A1R4R3R2R1A5SbaR4R3R2R1A4A3FT;Fc;Fi;Fxs;").
Proof.
  intros. unfold norm_xu_p, norm_xu. rewrite apply_xforms_p_eq.
  destruct (apply_xforms T xs) as [T1|] eqn:E; [|reflexivity].
  rewrite <- (apply_xforms_facts _ _ _ E). apply unbase_obj_at_p_eq.
Qed.
Lemma norm_xu_facts : ltac2:(tb__ "0|0|
S1S58A1S6S30S13S13S2fS4S13A1SbaR5R4R3R2A4S8S13R1A2A3S2fS1S17A1S15R2A1S15R3A1A3F_;FX;FT;Fc;Fi;Fxs;").
Proof.
  intros xs i c T X H. unfold norm_xu in H. destruct (apply_xforms T xs) as [T1|] eqn:E; [|discriminate].
  rewrite (proj1 (unbase_facts _ _ _ _ H)). exact (apply_xforms_facts _ _ _ E).
Qed.
Definition norm_xu_fast (xs : list xform) (i : nat) (c : Z) (T : sstate) : option sstate := ltac2:(tb__ "0|0|
S72S51S15VT;A1A1Vxs;Vi;Vc;VT;A5").
Lemma norm_xu_fast_eq : ltac2:(tb__ "0|0|
S1S58A1S6S30S13S2fS4S13A1S90R4R3R2R1A4SbaR4R3R2R1A4A3FT;Fc;Fi;Fxs;").
Proof. intros. unfold norm_xu_fast. rewrite mk_pf_x_eq. apply norm_xu_p_eq. Qed.

Fixpoint run_nsteps_p (pf : pfacts) (S : sstate) (l : list nstep) : option sstate :=
  match l with
  | [] => Some S
  | NX xs :: r => match apply_xforms_p pf S xs with Some S' => run_nsteps_p pf S' r | None => None end
  | NU i c :: r => match unbase_obj_at_p pf S i c with Some S' => run_nsteps_p pf S' r | None => None end
  end.
Lemma run_nsteps_p_eq : ltac2:(tb__ "0|0|
S1S56A1S13S2fS4S13A1S74S40S15R1A1A1R1R2A3S57R1R2A2A3FS;Fl;").
Proof.
  induction l as [|[xs|i c] r IH]; intros S; cbn [run_nsteps_p run_nsteps]; [reflexivity| |].
  - rewrite apply_xforms_p_eq. destruct (apply_xforms S xs) as [S'|] eqn:E; [|reflexivity].
    rewrite <- (apply_xforms_facts _ _ _ E). apply IH.
  - rewrite unbase_obj_at_p_eq. destruct (unbase_obj_at S i c) as [S'|] eqn:E; [|reflexivity].
    rewrite <- (proj1 (unbase_facts _ _ _ _ E)). apply IH.
Qed.
Lemma run_nsteps_facts : ltac2:(tb__ "0|0|
S1S56A1S13S13S2fS4S13A1S57R2R3A2S8S13R1A2A3S2fS1S17A1S15R2A1S15R3A1A3F_;FS';FS;Fl;").
Proof.
  induction l as [|[xs|i c] r IH]; intros S S' H; cbn [run_nsteps] in H; [injection H as <-; reflexivity| |].
  - destruct (apply_xforms S xs) as [S1|] eqn:E; [|discriminate]. rewrite (IH _ _ H). exact (apply_xforms_facts _ _ _ E).
  - destruct (unbase_obj_at S i c) as [S1|] eqn:E; [|discriminate]. rewrite (IH _ _ H). exact (proj1 (unbase_facts _ _ _ _ E)).
Qed.
Definition run_nsteps_fast (S : sstate) (l : list nstep) : option sstate := ltac2:(tb__ "0|0|
S74S51S15VS;A1A1VS;Vl;A3").
Lemma run_nsteps_fast_eq : ltac2:(tb__ "0|0|
S13S1S56A1S2fS4S13A1S84R2R1A2S57R2R1A2A3Fl;FS;").
Proof. intros. unfold run_nsteps_fast. rewrite mk_pf_x_eq. apply run_nsteps_p_eq. Qed.

Definition entails_p (pf : pfacts) (L T : sstate) (s : wsub) : bool := ltac2:(tb__ "0|0|
S0S0L_;S45VL;VT;Vs;A3S47Vpf;VL;VT;Vs;A4S2X0x2").
Lemma entails_p_eq : ltac2:(tb__ "0|0|
S13S13S4dS2fS0S70S40S15R3A1A1R3R2R1A4S44R3R2R1A3A3Fs;FT;FL;").
Proof. reflexivity. Qed.
Definition entails_fast (L T : sstate) (s : wsub) : bool := ltac2:(tb__ "0|0|
S70S51S15VL;A1A1VL;VT;Vs;A4").
Lemma entails_fast_eq : ltac2:(tb__ "0|0|
S13S13S4dS2fS0S8dR3R2R1A3S44R3R2R1A3A3Fs;FT;FL;").
Proof. intros. unfold entails_fast. rewrite mk_pf_x_eq. reflexivity. Qed.

Definition entails_fr_p (pf : pfacts) (L T : sstate) (s : wsub) : option (list sobj) := ltac2:(tb__ "0|6|
S4S1S6A1M0A1S4S1S16A1M1A1M2Lx;S4cVpf;S1cVL;A1M3Sb3S16S16S50Vs;A1S1cVT;A1A4A3G0SdS16G3A2S6S0G2L_;S5S5S4aR2A1S63S6S6ScbR1R2A2Li;R2A3A2S0S0L_;S45S9bVL;S43G3R2A2A2M4VT;Vs;A3S47Vpf;G4VT;Vs;A4S2X0x2A2S8G1S43G3S49R2R1A2A2A2SaG1A1M5X0x2Tn;Lns;G5X4x2").
Lemma entails_fr_p_eq : ltac2:(tb__ "0|0|
S13S13S4dS2fS4S1S16A1A1S73S40S15R3A1A1R3R2R1A4S46R3R2R1A3A3Fs;FT;FL;").
Proof. reflexivity. Qed.
Definition entails_fr_fast (L T : sstate) (s : wsub) : option (list sobj) := ltac2:(tb__ "0|0|
S73S51S15VL;A1A1VL;VT;Vs;A4").
Lemma entails_fr_fast_eq : ltac2:(tb__ "0|0|
S13S13S4dS2fS4S1S16A1A1S8eR3R2R1A3S46R3R2R1A3A3Fs;FT;FL;").
Proof. intros. unfold entails_fr_fast. rewrite mk_pf_x_eq. reflexivity. Qed.

Definition cont_check_fast (NP : positive) (xs : list xform) (i : nat) (c : Z) (T A : sstate) (tvi tvj : list (sv * sv)) : bool := ltac2:(tb__ "0|2|
S51S15VT;A1A1S42S4S13A1S0Lx;S72R1Vxs;Vi;Vc;VT;A5S13S98VNP;R1VA;A3S4dS0S0L_;M0S70R3R2VA;R1A4G0S4eR1VNP;A2G0S96VNP;S18R2A1M1A2G0S66G1Vtvi;A2S68R1Vtvi;Vtvj;A3S2X0x2S2X0x2S2X0x2S2X0x2Ts;LT';S2X4x2Tpf;").
Lemma cont_check_fast_eq : ltac2:(tb__ "0|1|
S31S1S58A1S6S30S13S13S1S3S14S14A2A1M0G0S2fS0S8bR8R7R6R5R4R3R2R1A8SbeR8R7R6R5R4R3R2R1A8A3Ftvj;Ftvi;FA;FT;Fc;Fi;Fxs;FNP;").
Proof.
  intros. unfold cont_check_fast, TobjJVx.cont_check. cbv zeta. rewrite mk_pf_x_eq, norm_xu_p_eq.
  destruct (norm_xu xs i c T) as [X|] eqn:E; [|reflexivity].
  rewrite <- (norm_xu_facts _ _ _ _ _ E). reflexivity.
Qed.

Definition entE_check_p (pf : pfacts) (NP n : positive) (X A : sstate) (tvi tvj : list (sv * sv)) (vA : sv) (rA rE : Z) (vE : sv) : bool := ltac2:(tb__ "0|2|
S98VNP;VX;VA;A3S4dS0S0L_;M0S70Vpf;VX;VA;R1A4G0S4eR1VNP;A2G0S96VNP;S18VX;A1M1A2G0S66G1Vtvi;A2G0S68R1Vtvi;Vtvj;A3G0S1dVn;VvE;A2G0S5cZ0VrA;A2G0S5dVrA;VrE;A2S7G0S60VrA;VrE;A2S41Vpf;S4fR1VvA;A2Z1VvE;A4S2X0x2X0x2S2X0x2S2X0x2S2X0x2S2X0x2S2X0x2S2X0x2S2X0x2Ts;").
Lemma entE_check_p_eq : ltac2:(tb__ "0|1|
S31S31S13S13S1S3S14S14A2A1M0G0S14S30S30S14S2fS0S78S40S15R8A1A1RaR9R8R7R6R5R4R3R2R1AbSbbRaR9R8R7R6R5R4R3R2R1AaA3FvE;FrE;FrA;FvA;Ftvj;Ftvi;FA;FX;Fn;FNP;").
Proof. reflexivity. Qed.
Definition entE_check_fast (NP n : positive) (X A : sstate) (tvi tvj : list (sv * sv)) (vA : sv) (rA rE : Z) (vE : sv) : bool := ltac2:(tb__ "0|0|
S78S51S15VX;A1A1VNP;Vn;VX;VA;Vtvi;Vtvj;VvA;VrA;VrE;VvE;Ab").
Lemma entE_check_fast_eq : ltac2:(tb__ "0|1|
S31S31S13S13S1S3S14S14A2A1M0G0S14S30S30S14S2fS0S7cRaR9R8R7R6R5R4R3R2R1AaSbbRaR9R8R7R6R5R4R3R2R1AaA3FvE;FrE;FrA;FvA;Ftvj;Ftvi;FA;FX;Fn;FNP;").
Proof. intros. unfold entE_check_fast. rewrite mk_pf_x_eq. reflexivity. Qed.

Definition contE_check_fast (NP : positive) (xs : list xform) (i : nat) (c : Z) (n : positive) (T A : sstate) (tvi tvj : list (sv * sv))
           (vA : sv) (rA rE : Z) (vE : sv) : bool := ltac2:(tb__ "0|0|
S51S15VT;A1A1S42S4S13A1S0Lx;S72R1Vxs;Vi;Vc;VT;A5S13S78R2VNP;Vn;R1VA;Vtvi;Vtvj;VvA;VrA;VrE;VvE;AbLX;S2X4x2Tpf;").
Lemma contE_check_fast_eq : ltac2:(tb__ "0|1|
S31S1S58A1S6S30S31S13S13S1S3S14S14A2A1M0G0S14S30S30S14S2fS0S8aRdRcRbRaR9R8R7R6R5R4R3R2R1AdSbdRdRcRbRaR9R8R7R6R5R4R3R2R1AdA3FvE;FrE;FrA;FvA;Ftvj;Ftvi;FA;FT;Fn;Fc;Fi;Fxs;FNP;").
Proof.
  intros. unfold contE_check_fast, contE_check. cbv zeta. rewrite mk_pf_x_eq, norm_xu_p_eq.
  destruct (norm_xu xs i c T) as [X|] eqn:E; [|reflexivity].
  rewrite <- (norm_xu_facts _ _ _ _ _ E). reflexivity.
Qed.

Definition nz_entry_check_p (pf : pfacts) (tvi : list (sv * sv)) (x : positive * Z * positive) : bool := ltac2:(tb__ "0|6|
S3S3S31S30A2M0S31A2S0Lx;Vx;G0S31G0S0Lp;R2S31S30S0S0L_;M1S64S3S14S14A2M2G2S5S24S9S14S14R1A3S1eR3A1M3A2S24SbS14S14R1A3S1fSb9S19R2A1S1eR4A1A3A2A2Lt;Vtvi;A3G1S41Vpf;S19Z1M4A1Z0M5G3A4G1S41Vpf;G3G5S19S5fZ2Z2fA2A1A4S5S5cG4R1A2S5cR1Z1000A2A2S2X0x2S2X0x2S2X0x2Le;Ldv;X3x1Lkv;Lp;X3x1").
Lemma nz_entry_check_p_eq : ltac2:(tb__ "0|0|
S1S17A1S1S3S14S14A2A1S3S3S31S30A2S31A2S2fS0S7eS40R3A1R2R1A3SbfR3R2R1A3A3Fx;Ftvi;Ffacts;").
Proof. intros facts tvi [[dv e] kv]. reflexivity. Qed.

Definition contEJ_check_fast (NP : positive) (xs : list xform) (i : nat) (c : Z) (n : positive) (T A : sstate) (tvi tvj : list (sv * sv))
           (vA : sv) (rA rE : Z) (vE : sv) (nzs : list (positive * Z * positive)) : bool := ltac2:(tb__ "0|2|
S51S15VT;A1A1S42S4S13A1S0Lx;S72R1Vxs;Vi;Vc;VT;A5S13S0S0L_;M0S63S3S3S31S30A2S31A2S7eR2Vtvi;A2Vnzs;A3G0S63S17S23S18R1A1A1Sc0Vnzs;A1M1A3S7cVNP;Vn;S99G1R1A2VA;Vtvi;Vtvj;VvA;VrA;VrE;VvE;AaS2X0x2S2X0x2LX;S2X4x2Tpf;").
Lemma contEJ_check_fast_eq : ltac2:(tb__ "0|1|
S31S1S58A1S6S30S31S13S13S1S3S14S14A2A1M0G0S14S30S30S14S1S3S3S31S30A2S31A2A1S2fS0S89ReRdRcRbRaR9R8R7R6R5R4R3R2R1AeSbcReRdRcRbRaR9R8R7R6R5R4R3R2R1AeA3Fnzs;FvE;FrE;FrA;FvA;Ftvj;Ftvi;FA;FT;Fn;Fc;Fi;Fxs;FNP;").
Proof.
  intros. unfold contEJ_check_fast, contEJ_check. cbv zeta. rewrite mk_pf_x_eq, norm_xu_p_eq.
  destruct (norm_xu xs i c T) as [X|] eqn:E; [|reflexivity].
  rewrite <- (norm_xu_facts _ _ _ _ _ E), entE_check_fast_eq.
  rewrite (forallb_ext_p _ _ nzs (nz_entry_check_p_eq (ss_facts X) tvi)). reflexivity.
Qed.

Definition sleq_pf (pf : pfacts) (a : sv) (k : Z) (b : sv) : bool := ltac2:(tb__ "0|0|
S0S0L_;S9cS4bVpf;A1Va;Vk;Vb;A4S7S9cS48Vpf;A1Va;Vk;Vb;A4X0x2").

Definition robj_stack_p (pf : pfacts) (o : sobj) : bool := ltac2:(tb__ "0|e|
S14S0Lx;M0S22Vo;A1S30S19R1A1S14G0S21Vo;A1S30S0S0L_;M1S5cS5eS5fZ2M2Z3eA2M3A1R3A2G1S5cR3R1A2G1S5dR1G3A2S41Vpf;S67S5eS62R3Z0M4A2A1S20Vo;A1M5A4S2X0x2S2X0x2S2X0x2Lhi;S31G1S41Vpf;S67G4S1aSb6G5R2A3A4G1S41Vpf;S67G4G5A4M6G1S71Vpf;S19S5eS5fG2Z2eA2A1A1M7G4R2A4S71Vpf;R2G4S19G4A1M8A4S2X0x2S2X0x2S2X0x2Li;Sb7S14S14G1S41Vpf;S67G4S1aSb6G5R4A3A4G1G6G1S71Vpf;G7G4R4A4S71Vpf;R4G4G8A4S2X0x2S2X0x2S2X0x2M9Lb;La;MaLop;MbGbSb8GaLop;McGcS0S32S14G9La;Lw;Lsgn;S31S14S30G9Lk;Li;Ll;X14x8Tlo;Llo;S31S1eR1A1S14G1S41Vpf;S67G4S1aSb6G5R1A3A4G1G6G1S71Vpf;G7G4R1A4S71Vpf;R1G4G8A4S2X0x2S2X0x2S2X0x2MdTlo;Li;Sb7S14S14S1aR3R2R1A3S14GdTlo;Lb;La;Lop;Sb7S14S14S25R3R2R1A3S14GdTlo;Lb;La;Lop;Sb8S14S14S1fR3R2R1A3S14GdTlo;Lb;La;Lop;Sb8S14S14S28R3R2R1A3S14GdTlo;Lb;La;Lop;S0S32S14S26R3R2R1A3S14GdTlo;La;Lw;Lsgn;S31S14S30S27R3R2R1A3S14GdTlo;Lk;Li;Ll;X14x8").
Lemma robj_stack_p_eq : ltac2:(tb__ "0|0|
S1S17A1S16S2fS0S83S40R2A1R1A2S6dR2R1A2A3Fo;Ffacts;").
Proof.
  intros facts o. unfold robj_stack_p, robj_stack, uleq_pf, sleq_pf, uleq, sleq, mk_pf. cbn [pf_d0 pf_dg]. reflexivity.
Qed.
Definition robjs_check_p (pf : pfacts) (tv : list (sv * sv)) (skip : option nat) (extra : sobj -> bool) (R : list sobj) : bool := ltac2:(tb__ "0|1|
S63S16S16S0S0L_;M0S83Vpf;R1A2S7G0S6eVtv;Vskip;R1A3S7Vextra;R1A1X0x2X0x2Lo;VR;A3").
Lemma robjs_check_p_eq : ltac2:(tb__ "0|0|
S1S17A1S1S3S14S14A2A1S4S6A1S16S0F_;S1S16A1S2fS0S7aS40R5A1R4R3R2R1A5S69R5R4R3R2R1A5A3FR;Fextra;Fskip;Ftv;Ffacts;").
Proof.
  intros. unfold robjs_check_p, robjs_check. apply forallb_ext_p. intros o. rewrite robj_stack_p_eq. reflexivity.
Qed.
Definition robjs_check_fast (facts : list sprop) (tv : list (sv * sv)) (skip : option nat) (extra : sobj -> bool) (R : list sobj) : bool := ltac2:(tb__ "0|0|
S7aS51Vfacts;A1Vtv;Vskip;Vextra;VR;A5").
Lemma robjs_check_fast_eq : ltac2:(tb__ "0|0|
S1S17A1S1S3S14S14A2A1S4S6A1S16S0F_;S1S16A1S2fS0S93R5R4R3R2R1A5S69R5R4R3R2R1A5A3FR;Fextra;Fskip;Ftv;Ffacts;").
Proof. intros. unfold robjs_check_fast. rewrite mk_pf_x_eq. apply robjs_check_p_eq. Qed.

Definition entA_check_p (pf : pfacts) (NP n : positive) (X A : sstate) (tvi tvj : list (sv * sv)) (ami amj : amode) (vA : sv) (rA rE : Z) (vE : sv) : bool := ltac2:(tb__ "0|2|
S98VNP;VX;VA;A3S4dS0S0L_;M0S70Vpf;VX;VA;R1A4G0S4eR1VNP;A2G0S96VNP;S18VX;A1M1A2G0S66G1Vtvi;A2G0S68R1Vtvi;Vtvj;A3G0S36G1Vami;A2G0S35S37R1Vamj;A2Vami;A2G0S1dVn;VvE;A2G0S5cZ0VrA;A2G0S5dVrA;VrE;A2S7G0S60VrA;VrE;A2S41Vpf;S4fR1VvA;A2Z1VvE;A4S2X0x2X0x2S2X0x2S2X0x2S2X0x2S2X0x2S2X0x2S2X0x2S2X0x2S2X0x2S2X0x2Ts;").
Lemma entA_check_p_eq : ltac2:(tb__ "0|1|
S31S31S13S13S1S3S14S14A2A1M0G0S33S33S14S30S30S14S2fS0S77S40S15RaA1A1RcRbRaR9R8R7R6R5R4R3R2R1AdSa2RcRbRaR9R8R7R6R5R4R3R2R1AcA3FvE;FrE;FrA;FvA;Famj;Fami;Ftvj;Ftvi;FA;FX;Fn;FNP;").
Proof. reflexivity. Qed.
Definition entA_check_fast (NP n : positive) (X A : sstate) (tvi tvj : list (sv * sv)) (ami amj : amode) (vA : sv) (rA rE : Z) (vE : sv) : bool := ltac2:(tb__ "0|0|
S77S51S15VX;A1A1VNP;Vn;VX;VA;Vtvi;Vtvj;Vami;Vamj;VvA;VrA;VrE;VvE;Ad").
Lemma entA_check_fast_eq : ltac2:(tb__ "0|1|
S31S31S13S13S1S3S14S14A2A1M0G0S33S33S14S30S30S14S2fS0S8cRcRbRaR9R8R7R6R5R4R3R2R1AcSa2RcRbRaR9R8R7R6R5R4R3R2R1AcA3FvE;FrE;FrA;FvA;Famj;Fami;Ftvj;Ftvi;FA;FX;Fn;FNP;").
Proof. intros. unfold entA_check_fast. rewrite mk_pf_x_eq. reflexivity. Qed.

Definition contA_check_fast (NP : positive) (ns : list nstep) (n : positive) (T A : sstate) (tvi tvj : list (sv * sv)) (ami amj : amode)
           (vA : sv) (rA rE : Z) (vE : sv) : bool := ltac2:(tb__ "0|0|
S51S15VT;A1A1S42S4S13A1S0Lx;S74R1VT;Vns;A3S13S77R2VNP;Vn;R1VA;Vtvi;Vtvj;Vami;Vamj;VvA;VrA;VrE;VvE;AdLX;S2X4x2Tpf;").
Lemma contA_check_fast_eq : ltac2:(tb__ "0|1|
S31S1S56A1S31S13S13S1S3S14S14A2A1M0G0S33S33S14S30S30S14S2fS0S88RdRcRbRaR9R8R7R6R5R4R3R2R1AdSa7RdRcRbRaR9R8R7R6R5R4R3R2R1AdA3FvE;FrE;FrA;FvA;Famj;Fami;Ftvj;Ftvi;FA;FT;Fn;Fns;FNP;").
Proof.
  intros. unfold contA_check_fast, contA_check. cbv zeta. rewrite mk_pf_x_eq, run_nsteps_p_eq.
  destruct (run_nsteps T ns) as [X|] eqn:E; [|reflexivity].
  rewrite <- (run_nsteps_facts _ _ _ E). reflexivity.
Qed.

Definition landAs_check_fast (NP : positive) (ns : list nstep) (s0 : wsub) (T A : sstate) (tvi tvj : list (sv * sv)) (ami amj : amode) : bool := ltac2:(tb__ "0|3|
S51S15VT;A1A1S42S4S13A1S0Lx;S74R1VT;Vns;A3S13ScS3S31S14A2M0Vs0;S98VNP;R1VA;A3A3S1G0A1S0S0L_;M1S70R3R2VA;R1A4G1S4eR1VNP;A2G1S96VNP;S18R2A1M2A2G1S66G2Vtvi;A2G1S68R1Vtvi;Vtvj;A3G1S36G2Vami;A2S35S37R1Vamj;A2Vami;A2S2X0x2S2X0x2S2X0x2S2X0x2S2X0x2S2X0x2Ts;LX;S2X4x2Tpf;").
Lemma landAs_check_fast_eq : ltac2:(tb__ "0|1|
S31S1S56A1S4dS13S13S1S3S14S14A2A1M0G0S33S33S2fS0S7dR9R8R7R6R5R4R3R2R1A9SabR9R8R7R6R5R4R3R2R1A9A3Famj;Fami;Ftvj;Ftvi;FA;FT;Fs0;Fns;FNP;").
Proof.
  intros. unfold landAs_check_fast, landAs_check. cbv zeta. rewrite mk_pf_x_eq, run_nsteps_p_eq.
  destruct (run_nsteps T ns) as [X|] eqn:E; [|reflexivity].
  rewrite <- (run_nsteps_facts _ _ _ E). reflexivity.
Qed.
Definition landA_check_fast (NP : positive) (ns : list nstep) (T A : sstate) (tvi tvj : list (sv * sv)) (ami amj : amode) : bool := ltac2:(tb__ "0|0|
S7dVNP;Vns;S11S3S31S14A2A1VT;VA;Vtvi;Vtvj;Vami;Vamj;A9").
Lemma landA_check_fast_eq : ltac2:(tb__ "0|1|
S31S1S56A1S13S13S1S3S14S14A2A1M0G0S33S33S2fS0S8fR8R7R6R5R4R3R2R1A8SaaR8R7R6R5R4R3R2R1A8A3Famj;Fami;Ftvj;Ftvi;FA;FT;Fns;FNP;").
Proof. intros. unfold landA_check_fast, landA_check. apply landAs_check_fast_eq. Qed.

Definition renormK_fast (F0 : list sprop) (prog : list nstep) (T : sstate) : option sstate := ltac2:(tb__ "0|2|
S4S13A1M0G0Lx;S84Sc1Sa3VT;A1M1VF0;A2Vprog;A2S13S8S13Sc1R1S15G1A1A2A2LX;SaS13A1X4x2").
Lemma renormK_fast_eq : ltac2:(tb__ "0|0|
S1S17A1S1S56A1S13S2fS4S13A1S82R3R2R1A3Sb2R3R2R1A3A3FT;Fprog;FF0;").
Proof. intros. unfold renormK_fast, renormK. rewrite run_nsteps_fast_eq. reflexivity. Qed.

Definition contK_check_fast (F0 : list sprop) (prog : list nstep) (T A : sstate) : bool := ltac2:(tb__ "0|5|
S4S13A1S0Lx;S82VF0;Vprog;VT;A3S13S5S5S5S5Sa6Sa9S15VT;A1M0A1G0A2Sa6VF0;S15Sa3VT;A1A1A2A2S97S18R1A1S18VT;A1A2A2S2eVA;A1A2S4S3S1S3S14S14A2M1A1M2S1S17A1M3A2M4A1S0Lx;Sc2R1VA;A2G4G4S0Lp;R1G2G3G2S0Ll;R2G3S0Ll0;R1S7S17G3S2Ll1;Ls;X1x2G1G2S2Ll1;Lp0;X1x2Ll0;Ll;X3x1Lp;S2X4x2A2LX;S2X4x2").
Lemma contK_check_fast_eq : ltac2:(tb__ "0|0|
S1S17A1S1S56A1S13S13S2fS0S76R4R3R2R1A4Sa8R4R3R2R1A4A3FA;FT;Fprog;FF0;").
Proof. intros. unfold contK_check_fast, TobjJVAy.cont_check. rewrite renormK_fast_eq. reflexivity. Qed.

Definition reent_check_p (pf : pfacts) (n : positive) (vA : sv) (rA rE : Z) (vE : sv) : bool := ltac2:(tb__ "0|0|
S5S5S5S1dVn;VvA;A2S1dVn;VvE;A2A2S5cZ0VrA;A2A2S12S5dVrA;VrE;A2S5S60VrA;VrE;A2S41Vpf;VvA;Z1VvE;A4A2A2A2").
Lemma reent_check_p_eq : ltac2:(tb__ "0|0|
S1S17A1S31S14S30S30S14S2fS0S79S40R6A1R5R4R3R2R1A6Sb1R6R5R4R3R2R1A6A3FvE;FrE;FrA;FvA;Fn;FF;").
Proof. reflexivity. Qed.

Definition post_check_p (pf : pfacts) (NPc : positive) (F0 : list sprop) (Cl : sstate) (s : wsub) (R : list sobj) (kept : list (sv * sv)) (rE : Z) (vE : sv)
           (d : sstate * (list (sv * sv) * amode)) (c : cdesc) : bool := ltac2:(tb__ "0|9|
Sc9Vs;VNPc;S9S13S3S1S3S14S14A2M0A1M1S33A2M2Vd;A3M3S18VCl;A1M4A4S4dS0S0L_;M5S76VF0;S9S1S56A1M6S34Vc;A3S6aVNPc;VCl;Vs;VR;G3A5S3aSbG6S34Vc;A3M7A1A4G5SacScG0Vkept;S6cR1S9G1S33SbS13G2Vd;A3M8A3A2A3S3bG7A1A2G5S35S37R1SbG1S33G8A3A2S38G7A1A2S79Vpf;G4S3cG7A1S39G7A1VrE;VvE;A6S2X0x2S2X0x2S2X0x2Tisub;").
Lemma post_check_p_eq : ltac2:(tb__ "0|1|
S31S1S17A1S13S4dS1S16A1S1S3S14S14A2A1M0S30S14S3S13S3G0S33A2A2Sa1S2fS0S91S40S15R8A1A1RaR9R8R7R6R5R4R3R2R1AbSadRaR9R8R7R6R5R4R3R2R1AaA3Fc;Fd;FvE;FrE;Fkept;FR;Fs;FCl;FF0;FNPc;").
Proof. intros. unfold post_check_p, post_check. cbv zeta. rewrite contK_check_fast_eq, reent_check_p_eq. reflexivity. Qed.

Fixpoint posts_check_p (pf : pfacts) (NPc : positive) (F0 : list sprop) (Cl : sstate) (s : wsub) (R : list sobj) (kept : list (sv * sv)) (rE : Z) (vE : sv)
         (ds : list (sstate * (list (sv * sv) * amode))) (cs : list cdesc) : bool :=
  match ds, cs with
  | [], [] => true
  | d :: ds', c :: cs' => post_check_p pf NPc F0 Cl s R kept rE vE d c &&& posts_check_p pf NPc F0 Cl s R kept rE vE ds' cs'
  | _, _ => false
  end.
Lemma posts_check_p_eq : ltac2:(tb__ "0|1|
S31S1S17A1S13S4dS1S16A1S1S3S14S14A2A1M0S30S14S1S3S13S3G0S33A2A2A1S1Sa1A1S2fS0S7fS40S15R8A1A1RaR9R8R7R6R5R4R3R2R1AbSaeRaR9R8R7R6R5R4R3R2R1AaA3Fcs;Fds;FvE;FrE;Fkept;FR;Fs;FCl;FF0;FNPc;").
Proof.
  intros NPc F0 Cl s R kept rE vE ds. induction ds as [|d ds IH]; intros [|c cs]; cbn [posts_check_p posts_check]; try reflexivity.
  rewrite post_check_p_eq, IH. reflexivity.
Qed.

Definition site_check_fast (C : mconsts) (NP : positive) (PreC : sstate) (tvC : list (sv * sv)) (amC : amode)
           (PDA : list (sstate * (list (sv * sv) * amode))) (NPc : positive) (F0 : list sprop) (extra : sobj -> bool)
           (Cl : sstate) (s : wsub) (kept passed : list (sv * sv)) (am : amode)
           (rE : Z) (vE : sv) (conts : list cdesc) : bool := ltac2:(tb__ "0|b|
S51S15VCl;A1A1S42S4S1S16A1M0A1S0Lx;S73R1VCl;VPreC;Vs;A4G0S0S0L_;M1S6bVC;VNP;VCl;VPreC;Vs;R1Sb3S3S13S3S1S3S14S14A2M2A1M3S33A2M4A2M5S13S9S13G4A2VPDA;A4A7G1ScaVs;VNPc;A2G1S96VNP;S18VCl;A1M6A2G1S66G6ScG2Vkept;Vpassed;A3A2G1S36G6Vam;A2G1S68Vs;Vpassed;VtvC;A3G1S35S37Vs;VamC;A2Vam;A2G1S63G5G5S5S5S6fVNPc;Vs;G6S9S13G4R1A3M7S9G3S33SbS13G4R1A3M8A3M9A5S3dVNPc;Vs;G6G7SbG3S33G8A3MaA5A2S3eVPreC;G7G9GaA4A2Ld;VPDA;A3G1S7aR2Vkept;SaS6A1Vextra;R1A5S7fR2VNPc;VF0;VCl;Vs;R1Vkept;VrE;VvE;VPDA;Vconts;AbS2X0x2S2X0x2S2X0x2S2X0x2S2X0x2S2X0x2S2X0x2S2X0x2S2X0x2LR;S2X4x2Tpf;").
Lemma site_check_fast_eq : ltac2:(tb__ "0|1|
Sc6S31S13S1S3S14S14A2A1M0S33S1S3S13S3G0S33A2A2A1S31S1S17A1S16S0F_;S13S4dG0G0S33S30S14S1Sa1A1S2fS0S85R11R10RfReRdRcRbRaR9R8R7R6R5R4R3R2R1A11Sa5R11R10RfReRdRcRbRaR9R8R7R6R5R4R3R2R1A11A3Fconts;FvE;FrE;Fam;Fpassed;Fkept;Fs;FCl;Fextra;FF0;FNPc;FPDA;FamC;FtvC;FPreC;FNP;FC;").
Proof.
  intros. unfold site_check_fast, site_check. cbv zeta. rewrite mk_pf_x_eq, entails_fr_p_eq.
  destruct (entails_fr Cl PreC s) as [R|]; [|reflexivity].
  rewrite robjs_check_p_eq, posts_check_p_eq. reflexivity.
Qed.
Lemma site_check_fast_ok : ltac2:(tb__ "0|1|
Sc6S31S13S1S3S14S14A2A1M0S33S1S3S13S3G0S33A2A2A1S31S1S17A1S16S0F_;S13S4dG0G0S33S30S14S1Sa1A1S2fS0S85R11R10RfReRdRcRbRaR9R8R7R6R5R4R3R2R1A11S7A3S2fS0Sa5R12R11R10RfReRdRcRbRaR9R8R7R6R5R4R3R2A11S7A3F_;Fconts;FvE;FrE;Fam;Fpassed;Fkept;Fs;FCl;Fextra;FF0;FNPc;FPDA;FamC;FtvC;FPreC;FNP;FC;").
Proof. intros *. rewrite site_check_fast_eq. exact (fun H => H). Qed.

Definition ppost_check_p (pf : pfacts) (PreC : sstate) (F0 : list sprop) (Cl : sstate) (s : wsub) (R : list sobj) (tv : list (sv * sv)) (am : amode) (rE : Z) (vE : sv)
           (L : leaf) (c : list nstep * aedesc) : bool := ltac2:(tb__ "0|4|
S0S0L_;M0S76VF0;S9S1S56A1M1S34Vc;A3S99S15VCl;A1Sc8Vs;S18VPreC;A1S9eVL;A1S18VCl;A1M2VR;A5A2S3aSbG1S34Vc;A3M3A1A4G0S3fVtv;S3bG3A1A2G0S35Vam;S38G3A1A2S79Vpf;G2S3cG3A1S39G3A1VrE;VvE;A6S2X0x2S2X0x2S2X0x2").
Lemma ppost_check_p_eq : ltac2:(tb__ "0|0|
S13S1S17A1S13S4dS1S16A1S1S3S14S14A2A1S33S30S14S9aS3S1S56A1S34A2S2fS0S92S40S15R9A1A1RbRaR9R8R7R6R5R4R3R2R1AcSafRbRaR9R8R7R6R5R4R3R2R1AbA3Fc;FL;FvE;FrE;Fam;Ftv;FR;Fs;FCl;FF0;FPreC;").
Proof. intros. unfold ppost_check_p, ppost_check. rewrite contK_check_fast_eq, reent_check_p_eq. reflexivity. Qed.
Fixpoint pposts_check_p (pf : pfacts) (PreC : sstate) (F0 : list sprop) (Cl : sstate) (s : wsub) (R : list sobj) (tv : list (sv * sv)) (am : amode) (rE : Z) (vE : sv)
         (ls : list leaf) (cs : list (list nstep * aedesc)) : bool :=
  match ls, cs with
  | [], [] => true
  | L :: ls', c :: cs' => ppost_check_p pf PreC F0 Cl s R tv am rE vE L c &&& pposts_check_p pf PreC F0 Cl s R tv am rE vE ls' cs'
  | _, _ => false
  end.
Lemma pposts_check_p_eq : ltac2:(tb__ "0|0|
S13S1S17A1S13S4dS1S16A1S1S3S14S14A2A1S33S30S14S1S9aA1S1S3S1S56A1S34A2A1S2fS0S80S40S15R9A1A1RbRaR9R8R7R6R5R4R3R2R1AcSb0RbRaR9R8R7R6R5R4R3R2R1AbA3Fcs;Fls;FvE;FrE;Fam;Ftv;FR;Fs;FCl;FF0;FPreC;").
Proof.
  intros PreC F0 Cl s R tv am rE vE ls. induction ls as [|L ls IH]; intros [|c cs]; cbn [pposts_check_p pposts_check]; try reflexivity.
  rewrite ppost_check_p_eq, IH. reflexivity.
Qed.

Definition pure_site_check_fast (NP : positive) (PreC : sstate) (PostsC : list leaf) (F0 : list sprop)
           (Cl : sstate) (s : wsub) (tv : list (sv * sv)) (am : amode) (rE : Z) (vE : sv)
           (conts : list (list nstep * aedesc)) : bool := ltac2:(tb__ "0|4|
S51S15VCl;A1M0A1S42S4S1S16A1M1A1S0Lx;S73R1VCl;VPreC;Vs;A4G1S0S0L_;M2Sc7VCl;VPreC;Vs;R1VPostsC;A5G2S96VNP;S18VCl;A1M3A2G2S66G3Vtv;A2G2S36G3Vam;A2G2S63S17S23G3A1G0A3S80R2VPreC;VF0;VCl;Vs;R1Vtv;Vam;VrE;VvE;VPostsC;Vconts;AcS2X0x2S2X0x2S2X0x2S2X0x2S2X0x2LR;S2X4x2Tpf;").
Lemma pure_site_check_fast_eq : ltac2:(tb__ "0|0|
S31S13S1S9aA1S1S17A1S13S4dS1S3S14S14A2A1S33S30S14S1S3S1S56A1S34A2A1S2fS0S81RbRaR9R8R7R6R5R4R3R2R1AbSa4RbRaR9R8R7R6R5R4R3R2R1AbA3Fconts;FvE;FrE;Fam;Ftv;Fs;FCl;FF0;FPostsC;FPreC;FNP;").
Proof.
  intros. unfold pure_site_check_fast, pure_site_check. cbv zeta. rewrite mk_pf_x_eq, entails_fr_p_eq.
  destruct (entails_fr Cl PreC s) as [R|]; [|reflexivity].
  rewrite pposts_check_p_eq. reflexivity.
Qed.
Lemma pure_site_check_fast_ok : ltac2:(tb__ "0|0|
S31S13S1S9aA1S1S17A1S13S4dS1S3S14S14A2A1S33S30S14S1S3S1S56A1S34A2A1S2fS0S81RbRaR9R8R7R6R5R4R3R2R1AbS7A3S2fS0Sa4RcRbRaR9R8R7R6R5R4R3R2AbS7A3F_;Fconts;FvE;FrE;Fam;Ftv;Fs;FCl;FF0;FPostsC;FPreC;FNP;").
Proof. intros *. rewrite pure_site_check_fast_eq. exact (fun H => H). Qed.

Lemma opt_match_eq2 : forall {A B} (o' o : option A) (g f : A -> B) (d : B),
  o' = o -> (forall a, g a = f a) ->
  match o' with Some a => g a | None => d end = match o with Some a => f a | None => d end.
Proof. intros A B o' o g f d -> H. destruct o as [a|]; [apply H | reflexivity]. Qed.
Lemma if_eq3 : forall {B} (c' c : bool) (x' x y' y : B),
  c' = c -> x' = x -> y' = y -> (if c' then x' else y') = (if c then x else y).
Proof. intros B c' c x' x y' y -> -> ->. reflexivity. Qed.
Lemma app_eq2 : forall {A B} (f g : A -> B) (a b : A), f = g -> a = b -> f a = g b.
Proof. intros A B f g a b -> ->. reflexivity. Qed.
Lemma let_eq2 : forall {A B} (a' a : A) (b' b : A -> B),
  a' = a -> (forall x, b' x = b x) -> (let x := a' in b' x) = (let x := a in b x).
Proof. intros A B a' a b' b -> H. cbv zeta. apply H. Qed.
Lemma fast_cut : ltac2:(tb__ "0|1|
S0S0S2fS0R2R1A3S2fS0R3S7A3M0G0F_;F_;Ft;Ft';").
Proof. intros t' t ->. exact (fun H => H). Qed.

Ltac swap_c F c c' :=
  lazymatch (eval pattern c in F) with
  | ?P _ => lazymatch P with
            | (fun _ => ?B) => F
            | _ => constr:(P c')
            end
  end.
Ltac swap_all F :=
  let F := swap_c F (@entails_fr) (@entails_fr_fast) in
  let F := swap_c F (@entails) (@entails_fast) in
  let F := swap_c F (@TobjJVx.cont_check) (@cont_check_fast) in
  let F := swap_c F (@entE_check) (@entE_check_fast) in
  let F := swap_c F (@contE_check) (@contE_check_fast) in
  let F := swap_c F (@contEJ_check) (@contEJ_check_fast) in
  let F := swap_c F (@entA_check) (@entA_check_fast) in
  let F := swap_c F (@contA_check) (@contA_check_fast) in
  let F := swap_c F (@landAs_check) (@landAs_check_fast) in
  let F := swap_c F (@landA_check) (@landA_check_fast) in
  let F := swap_c F (@TobjJVAy.cont_check) (@contK_check_fast) in
  let F := swap_c F (@robjs_check) (@robjs_check_fast) in
  let F := swap_c F (@norm_xu) (@norm_xu_fast) in
  let F := swap_c F (@run_nsteps) (@run_nsteps_fast) in
  let F := swap_c F (@apply_xforms) (@apply_xforms_fast) in
  let F := swap_c F (@unbase_obj_at) (@unbase_obj_at_fast) in
  F.

Ltac fast_leaf :=
  lazymatch goal with
  | |- entails_fr_fast ?a ?b ?c = _ => refine (eq_trans (entails_fr_fast_eq a b c) _)
  | |- entails_fast ?a ?b ?c = _ => refine (eq_trans (entails_fast_eq a b c) _)
  | |- cont_check_fast ?a ?b ?c ?d ?e ?f ?g ?h = _ => refine (eq_trans (cont_check_fast_eq a b c d e f g h) _)
  | |- entE_check_fast ?a ?b ?c ?d ?e ?f ?g ?h ?i ?j = _ => refine (eq_trans (entE_check_fast_eq a b c d e f g h i j) _)
  | |- contE_check_fast ?a ?b ?c ?d ?e ?f ?g ?h ?i ?j ?k ?l ?m = _ => refine (eq_trans (contE_check_fast_eq a b c d e f g h i j k l m) _)
  | |- contEJ_check_fast ?a ?b ?c ?d ?e ?f ?g ?h ?i ?j ?k ?l ?m ?n = _ => refine (eq_trans (contEJ_check_fast_eq a b c d e f g h i j k l m n) _)
  | |- entA_check_fast ?a ?b ?c ?d ?e ?f ?g ?h ?i ?j ?k ?l = _ => refine (eq_trans (entA_check_fast_eq a b c d e f g h i j k l) _)
  | |- contA_check_fast ?a ?b ?c ?d ?e ?f ?g ?h ?i ?j ?k ?l ?m = _ => refine (eq_trans (contA_check_fast_eq a b c d e f g h i j k l m) _)
  | |- landAs_check_fast ?a ?b ?c ?d ?e ?f ?g ?h ?i = _ => refine (eq_trans (landAs_check_fast_eq a b c d e f g h i) _)
  | |- landA_check_fast ?a ?b ?c ?d ?e ?f ?g ?h = _ => refine (eq_trans (landA_check_fast_eq a b c d e f g h) _)
  | |- contK_check_fast ?a ?b ?c ?d = _ => refine (eq_trans (contK_check_fast_eq a b c d) _)
  | |- robjs_check_fast ?a ?b ?c ?d ?e = _ => refine (eq_trans (robjs_check_fast_eq a b c d e) _)
  | |- norm_xu_fast ?a ?b ?c ?d = _ => refine (eq_trans (norm_xu_fast_eq a b c d) _)
  | |- run_nsteps_fast ?a ?b = _ => refine (eq_trans (run_nsteps_fast_eq a b) _)
  | |- apply_xforms_fast ?a ?b = _ => refine (eq_trans (apply_xforms_fast_eq a b) _)
  | |- unbase_obj_at_fast ?a ?b ?c = _ => refine (eq_trans (unbase_obj_at_fast_eq a b c) _)
  end.

Ltac fast_eq_core :=
  lazymatch goal with
  | |- ?l = ?r =>
      first [ constr_eq l r; exact (@eq_refl _ r)
            | fast_leaf; fast_eq_core
            | lazymatch goal with
              | |- (let x := ?a' in @?b' x) = (let y := ?a in @?b y) =>
                  refine (let_eq2 a' a b' b _ _); [ fast_eq_core | intro; cbv beta; fast_eq_core ]
              | |- match _ with Some _ => _ | None => _ end = match _ with Some _ => _ | None => _ end =>
                  apply opt_match_eq2; [ fast_eq_core | intro; cbv beta; fast_eq_core ]
              | |- (if _ then _ else _) = (if _ then _ else _) =>
                  apply if_eq3; fast_eq_core
              | |- ?f ?a = ?g ?b =>
                  apply app_eq2; fast_eq_core
              end ]
  end.
Ltac fast_eq := cbv beta; fast_eq_core.

Ltac fast_site :=
  lazymatch goal with
  | |- ?t = true =>
      let t' := swap_all t in
      let H := fresh "Hfast" in let H2 := fresh "Hvm" in
      assert (H : t' = t) by fast_eq;

      assert (H2 : t' = true) by (clear H; vm_cast_no_check (@eq_refl bool true));
      exact_no_check (fast_cut t' t H H2)
  end.

Ltac fast_lit :=
  lazymatch goal with
  | |- @eq ?T ?t ?v =>
      let t' := swap_all t in
      let H := fresh "Hfast" in let H2 := fresh "Hvm" in
      assert (H : t' = t) by fast_eq;
      assert (H2 : t' = v) by (clear H; vm_cast_no_check (@eq_refl T v));
      exact_no_check (@eq_trans T t t' v (@eq_sym T t' t H) H2)
  end.

Ltac fast_memo M Mf :=
  lazymatch goal with
  | |- @eq ?T _ ?r =>
      let H := fresh "Hfast" in let H2 := fresh "Hvm" in
      assert (H : Mf = M) by (cbv delta [M Mf]; fast_eq);
      assert (H2 : Mf = r) by (clear H; vm_cast_no_check (@eq_refl T Mf));
      exact_no_check (@eq_trans T M Mf r (@eq_sym T Mf M H) H2)
  end.

Ltac share_app F :=
  lazymatch goal with
  | |- ?t = true =>
      lazymatch t with
      | context [F ?a] =>
          lazymatch (eval pattern (F a) in t) with
          | ?P _ => let t2 := constr:(let shared := F a in P shared) in
                    let t3 := (eval cbv beta in t2) in
                    change_no_check (t3 = true)
          end
      end
  end.
