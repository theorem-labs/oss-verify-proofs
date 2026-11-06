(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "list"; "bool"; "option"; "andb"; "nat"; "true"; "false"; "fst"; "prod"; "negb"; "app"; "orb"; "snd"; "None"; "@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sstate"; "ss_lenient"; "sv"; "ss_next"; "ss_facts"; "sv_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "edge"; "vnode"; "lnode"; "vn_state"; "e_leaf"; "e_src"; "e_sub"; "e_tgt"; "leaves_edges"; "ln_state"; "vn_rank"; "vn_var"; "cfg_edges"; "cuts_edges"; "@Corelib.Numbers.BinNums"; "positive"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFGFast"; "cedge"; "cedge_ok"; "cfg_edges_c"; "omap_fst_e"; "cuts_edges_c"; "echeck2_c"; "leaves_edges_c"; "oall_ok_e"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVA"; "aedesc"; "ad_state"; "andesc"; "ad_rank"; "ad_var"; "echeckA"; "ejcertA"; "jcertA"; "adrop"; "amode"; "eecheckA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "edesc"; "ed_state"; "ed_rank"; "ed_tv"; "ed_var"; "ejcert"; "jcert"; "echeckJ"; "eecheckJ"; "tv_below"; "tv_sub_eqb"; "@Stdlib.Lists.List"; "forallb"; "nth_error"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast"; "pcache"; "uleq_r"; "cleaf"; "sym_run_lc"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@Stdlib.ZArith.BinInt.Z"; "ltb"; "leb"; "eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.S"; "cut_edges_c"; "cfg_edges_fast"; "eecheckA_c"; "eecheckJ_c"; "check_ecfgI_fast"; "echeckI_c"; "ejcertA_fast"; "ejcert_fast"; "ejcutA_fast"; "ejcut_fast"; "jcertA_fast"; "jcert_fast"; "cuts_edges_fast"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "sv_subst"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "leaf"; "sym_run"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.L"; "elcut_fast"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgGlue"; "check_ecfgI"; "echeckI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ECfgCuts"; "elcut"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVAy"; "ejcutA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVx"; "ejcut"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast"; "cut_edges_c"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymCFG SymStepFast SymCFGFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import CfgGlue TobjJV TobjJVx TobjJVA TobjJVAy ECfgCuts.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section S.
Variable segs : list Segment.

Definition cuts_edges_fast (fuel : nat) (cutpcs : list Z) (g : positive) (i : nat)
           (cuts targets : list sstate) : option (list edge) := ltac2:(tb__ "0|0|
S29S2aVsegs;Vfuel;Vcutpcs;Vg;Vi;Vcuts;Vtargets;A7A1").
Theorem cuts_edges_fast_eq : ltac2:(tb__ "0|1|
S4S0S25A1S24S4S0S10A1M0G0SeS2S0S16A1A1S5bR6R5R4R3R2R1A6S23Vsegs;R6R5R4R3R2R1A7A3Ftargets;Fcuts;Fi;Fg;Fcutpcs;Ffuel;").
Proof. intros. apply cuts_edges_c_ok. Qed.

Definition cfg_edges_fast (fuel : nat) (cutpcs : list Z) (g : positive) (cuts exits : list sstate) : option (list edge) := ltac2:(tb__ "0|0|
S29S28Vsegs;Vfuel;Vcutpcs;Vg;Vcuts;Vexits;A6A1").
Theorem cfg_edges_fast_eq : ltac2:(tb__ "0|1|
S4S0S25A1S24S0S10A1M0G0SeS2S0S16A1A1S50R5R4R3R2R1A5S22Vsegs;R5R4R3R2R1A6A3Fexits;Fcuts;Fg;Fcutpcs;Ffuel;").
Proof. intros. apply cfg_edges_c_ok. Qed.

Definition cut_edges_c (fuel : nat) (cutpcs : list Z) (g : positive) (i : nat) (T : sstate) (targets : list sstate)
  : option (list cedge) := ltac2:(tb__ "0|2|
S2S0S49A1M0A1S2S0S26A1M1A1Lx;S4aVsegs;Vfuel;Vcutpcs;VT;S5A5G0S2cVg;Vi;R1Vtargets;A4Llcs;SdG1A1X2x2").

Lemma cut_edges_c_ok : ltac2:(tb__ "0|4|
S4S0S25A1S24S4S10S0S10A1SfSeS2S0S16A1M0A1M1S29S4fR6R5R4R3R2R1A6M2A1S2S0S5eA1M3A1G1Lx;S5fVsegs;R6R5R2S5A5G3S1eR5R4R1R2A4Lleaves;SdG0A1X2x2A3S2dG2A1A2Ftargets;FT;Fi;Fg;Fcutpcs;Ffuel;").
Proof.
  intros. unfold cut_edges_c. rewrite <- (sym_run_lc_eq segs fuel cutpcs T true).
  destruct (sym_run_lc segs fuel cutpcs T true) as [lcs|] eqn:E; [|split; [reflexivity | exact I]].
  cbn [omap_fst]. apply leaves_edges_c_ok. exact (sym_run_lc_ok segs _ _ _ _ _ E).
Qed.

Lemma cut_check_eq : ltac2:(tb__ "0|3|
S4S0S25A1S24S4S10S0S10A1S16S1F_;S26S1F_;S26S27R1A1SeS1R3R2A1R4S7S16S47R2A3A1A3F_;Fec;SeS1S2S0S26A1M0A1S1Lx;S4fR9R8R7R6R5R4A6G0S44S26R3R1A3Les;S6X2x2S2S0S5eA1M1A1S1Lx;S5fVsegs;R9R8R5S5A5G1S2S0S16A1M2A1S1Lx;S1eR8R7R1R5A4G2S44S16R5R1A3Les;S6X2x2Lleaves;S6X2x2A3F_;FPc;FP;Ftargets;FT;Fi;Fg;Fcutpcs;Ffuel;").
Proof.
  intros fuel cutpcs g i T targets P Pc HP.
  destruct (cut_edges_c_ok fuel cutpcs g i T targets) as [E O].
  rewrite (edges_check_eq _ P Pc O HP), E.
  destruct (sym_run segs fuel cutpcs T true); reflexivity.
Qed.

Definition echeckI_c (g : positive) (nodes : list vnode) (ec : cedge) : bool := ltac2:(tb__ "0|b|
S7S16S47Vec;A3S16S2S17A1S1Lx;M0S45S17Vnodes;S1bR1A1A3S17G0S45S17Vnodes;S1dR2A1A3S17S3S3S3S3S3S3S3S5dS1cR3A1M1Vg;A2S4bVg;S13S19R2A1A1M2A2A2S15G2S21R2A1M3A2A2S4dZ0M4S20R1A1M5A2A2S4cG5Z100M6A2A2S4dG4S20R2A1M7A2A2S4cG7G6A2A2SbS48ScS16S47Vec;A3M8S14S1aR3A1A1M9G3Z1S5cG1S21R1A1A2MaA5S3S48G8G9G3G4GaA5S4cG5G7A2A2A2A2Lnj;S6X2x2Lni;S6X2x2Te;").

Lemma echeckI_c_eq : ltac2:(tb__ "0|0|
S24S0S17A1S26S27R1A1SeS1S54R4R3R2A3S62R4R3S7S16S47R2A3A3A3F_;Fec;Fnodes;Fg;").
Proof.
  intros g nodes ec H. unfold echeckI_c, echeckI. cbv zeta.
  destruct (nth_error nodes (e_src (fst ec))); [|reflexivity].
  destruct (nth_error nodes (e_tgt (fst ec))); [|reflexivity].
  rewrite !(uleq_r_ok _ _ _ _ _ H). reflexivity.
Qed.

Definition check_ecfgI_fast (fuel : nat) (cutpcs : list Z) (g : positive) (cuts exits : list vnode) : bool := ltac2:(tb__ "0|1|
S3S44S17S17S9S11S19R1A1A1A1Ln;Vcuts;A3S2S0S26A1M0A1S1Lx;S28Vsegs;Vfuel;Vcutpcs;Vg;S46S17S10S19Vcuts;A4S46S17S10S19Vexits;A4A6G0S44S26S54Vg;SaS17Vcuts;Vexits;A3A2R1A3Les;S6X2x2A2").

Theorem check_ecfgI_fast_eq : ltac2:(tb__ "0|1|
S4S0S25A1S24S0S17A1M0G0SeS1S53R5R4R3R2R1A5S61Vsegs;R5R4R3R2R1A6A3Fexits;Fcuts;Fg;Fcutpcs;Ffuel;").
Proof.
  intros. unfold check_ecfgI_fast, check_ecfgI. f_equal.
  destruct (cfg_edges_c_ok segs fuel cutpcs g (map vn_state cuts) (map vn_state exits)) as [E O].
  rewrite <- E. apply edges_check_eq; [exact O|]. intros ec Hec. apply echeckI_c_eq; exact Hec.
Qed.
Corollary check_ecfgI_fast_ok : ltac2:(tb__ "0|1|
S4S0S25A1S24S0S17A1M0G0SeS1S53R5R4R3R2R1A5S5A3SeS1S61Vsegs;R6R5R4R3R2A6S5A3F_;Fexits;Fcuts;Fg;Fcutpcs;Ffuel;").
Proof. intros fuel cutpcs g cuts exits H. rewrite <- check_ecfgI_fast_eq. exact H. Qed.

Variable NP : positive.

Definition eecheckJ_c (nodes : list edesc) (ec : cedge) : bool := ltac2:(tb__ "0|7|
S7S16S47Vec;A3S16S2S39A1S1Lx;M0S45S39Vnodes;S1bR1A1A3S39G0S45S39Vnodes;S1dR2A1A3S39S3S3S3S3S3S3S5dS1cR3A1M1VNP;A2S4bVNP;S13S3aR2A1A1M2A2A2S42G2S3cR2A1M3A2A2S43G1G3S3cR1A1A3A2S15G2S3dR2A1M4A2A2S4dZ0S3bR1A1M5A2A2SbS4cG5S3bR2A1M6A2S3S4eG5G6A2S48ScS16S47Vec;A3S14S1aR3A1A1S5cG1S3dR1A1A2Z1G4A5A2A2A2Lnj;S6X2x2Lni;S6X2x2Te;").

Lemma eecheckJ_c_eq : ltac2:(tb__ "0|0|
S0S39A1S26S27R1A1SeS1S52R3R2A2S41VNP;R3S7S16S47R2A3A3A3F_;Fec;Fnodes;").
Proof.
  intros nodes ec H. unfold eecheckJ_c, eecheckJ. cbv zeta.
  destruct (nth_error nodes (e_src (fst ec))); [|reflexivity].
  destruct (nth_error nodes (e_tgt (fst ec))); [|reflexivity].
  rewrite (uleq_r_ok _ _ _ _ _ H). reflexivity.
Qed.

Definition ejcert_fast (fuel : nat) (cutpcs : list Z) (g : positive) (cutsE exitsE : list edesc) : bool := ltac2:(tb__ "0|1|
S3S44S39S39S9S11S3aR1A1A1A1Ln;VcutsE;A3S2S0S26A1M0A1S1Lx;S28Vsegs;Vfuel;Vcutpcs;Vg;S46S39S10S3aVcutsE;A4S46S39S10S3aVexitsE;A4A6G0S44S26S52SaS39VcutsE;VexitsE;A3A1R1A3Les;S6X2x2A2").

Theorem ejcert_fast_eq : ltac2:(tb__ "0|1|
S4S0S25A1S24S0S39A1M0G0SeS1S56R5R4R3R2R1A5S3eVsegs;VNP;R5R4R3R2R1A7A3FexitsE;FcutsE;Fg;Fcutpcs;Ffuel;").
Proof.
  intros. unfold ejcert_fast, ejcert. f_equal.
  destruct (cfg_edges_c_ok segs fuel cutpcs g (map ed_state cutsE) (map ed_state exitsE)) as [E O].
  rewrite <- E. apply edges_check_eq; [exact O|]. intros ec Hec. apply eecheckJ_c_eq; exact Hec.
Qed.
Corollary ejcert_fast_ok : ltac2:(tb__ "0|1|
S4S0S25A1S24S0S39A1M0G0SeS1S56R5R4R3R2R1A5S5A3SeS1S3eVsegs;VNP;R6R5R4R3R2A7S5A3F_;FexitsE;FcutsE;Fg;Fcutpcs;Ffuel;").
Proof. intros fuel cutpcs g cutsE exitsE H. rewrite <- ejcert_fast_eq. exact H. Qed.

Definition ejcut_fast (fuel : nat) (cutpcs : list Z) (g : positive) (nodes : list edesc) (i : nat) (n : edesc) : bool := ltac2:(tb__ "0|2|
S3S9S11S3aVn;A1M0A1A1S3S4bVg;S13G0A1A2S2S0S26A1M1A1S1Lx;S4fVfuel;Vcutpcs;Vg;Vi;G0S46S39S10S3aVnodes;A4A6G1S44S26S52Vnodes;A1R1A3Les;S6X2x2A2A2").

Theorem ejcut_fast_eq : ltac2:(tb__ "0|0|
S4S0S25A1S24S0S39A1S4S39SeS1S58R6R5R4R3R2R1A6S65Vsegs;VNP;R6R5R4R3R2R1A8A3Fn;Fi;Fnodes;Fg;Fcutpcs;Ffuel;").
Proof.
  intros. unfold ejcut_fast, ejcut. f_equal. f_equal.
  apply cut_check_eq. intros ec Hec. apply eecheckJ_c_eq; exact Hec.
Qed.
Corollary ejcut_fast_ok : ltac2:(tb__ "0|0|
S4S0S25A1S24S0S39A1S4S39SeS1S58R6R5R4R3R2R1A6S5A3SeS1S65Vsegs;VNP;R7R6R5R4R3R2A8S5A3F_;Fn;Fi;Fnodes;Fg;Fcutpcs;Ffuel;").
Proof. intros fuel cutpcs g nodes i n H. rewrite <- ejcut_fast_eq. exact H. Qed.

Definition eecheckA_c (nodes : list aedesc) (ec : cedge) : bool := ltac2:(tb__ "0|4|
S7S16S47Vec;A3S16S2S2eA1S1Lx;M0S45S2eVnodes;S1bR1A1A3S2eG0S45S2eVnodes;S1dR2A1A3S2eS3S3S3S33VNP;S46S2eS30S36Vnodes;A4R3A3S15S13S2fR2A1A1S32R2A1M1A2A2S4dZ0S31R1A1M2A2A2SbS4cG2S31R2A1M3A2S3S4eG2G3A2S48ScS16S47Vec;A3S14S1aR3A1A1S5cS1cR3A1S32R1A1A2Z1G1A5A2A2A2Lnj;S6X2x2Lni;S6X2x2Te;").

Lemma eecheckA_c_eq : ltac2:(tb__ "0|0|
S0S2eA1S26S27R1A1SeS1S51R3R2A2S38VNP;R3S7S16S47R2A3A3A3F_;Fec;Fnodes;").
Proof.
  intros nodes ec H. unfold eecheckA_c, eecheckA. cbv zeta.
  destruct (nth_error nodes (e_src (fst ec))); [|reflexivity].
  destruct (nth_error nodes (e_tgt (fst ec))); [|reflexivity].
  rewrite (uleq_r_ok _ _ _ _ _ H). reflexivity.
Qed.

Definition ejcertA_fast (fuel : nat) (cutpcs : list Z) (g : positive) (cutsE exitsE : list aedesc) : bool := ltac2:(tb__ "0|1|
S3S44S2eS2eS9S11S2fR1A1A1A1Ln;VcutsE;A3S2S0S26A1M0A1S1Lx;S28Vsegs;Vfuel;Vcutpcs;Vg;S46S2eS10S2fVcutsE;A4S46S2eS10S2fVexitsE;A4A6G0S44S26S51SaS2eVcutsE;VexitsE;A3A1R1A3Les;S6X2x2A2").

Theorem ejcertA_fast_eq : ltac2:(tb__ "0|1|
S4S0S25A1S24S0S2eA1M0G0SeS1S55R5R4R3R2R1A5S34Vsegs;VNP;R5R4R3R2R1A7A3FexitsE;FcutsE;Fg;Fcutpcs;Ffuel;").
Proof.
  intros. unfold ejcertA_fast, ejcertA. f_equal.
  destruct (cfg_edges_c_ok segs fuel cutpcs g (map ad_state cutsE) (map ad_state exitsE)) as [E O].
  rewrite <- E. apply edges_check_eq; [exact O|]. intros ec Hec. apply eecheckA_c_eq; exact Hec.
Qed.
Corollary ejcertA_fast_ok : ltac2:(tb__ "0|1|
S4S0S25A1S24S0S2eA1M0G0SeS1S55R5R4R3R2R1A5S5A3SeS1S34Vsegs;VNP;R6R5R4R3R2A7S5A3F_;FexitsE;FcutsE;Fg;Fcutpcs;Ffuel;").
Proof. intros fuel cutpcs g cutsE exitsE H. rewrite <- ejcertA_fast_eq. exact H. Qed.

Definition ejcutA_fast (fuel : nat) (cutpcs : list Z) (g : positive) (nodes : list aedesc) (i : nat) (n : aedesc) : bool := ltac2:(tb__ "0|2|
S3S9S11S2fVn;A1M0A1A1S3S4bVg;S13G0A1A2S2S0S26A1M1A1S1Lx;S4fVfuel;Vcutpcs;Vg;Vi;G0S46S2eS10S2fVnodes;A4A6G1S44S26S51Vnodes;A1R1A3Les;S6X2x2A2A2").

Theorem ejcutA_fast_eq : ltac2:(tb__ "0|0|
S4S0S25A1S24S0S2eA1S4S2eSeS1S57R6R5R4R3R2R1A6S64Vsegs;VNP;R6R5R4R3R2R1A8A3Fn;Fi;Fnodes;Fg;Fcutpcs;Ffuel;").
Proof.
  intros. unfold ejcutA_fast, ejcutA. f_equal. f_equal.
  apply cut_check_eq. intros ec Hec. apply eecheckA_c_eq; exact Hec.
Qed.
Corollary ejcutA_fast_ok : ltac2:(tb__ "0|0|
S4S0S25A1S24S0S2eA1S4S2eSeS1S57R6R5R4R3R2R1A6S5A3SeS1S64Vsegs;VNP;R7R6R5R4R3R2A8S5A3F_;Fn;Fi;Fnodes;Fg;Fcutpcs;Ffuel;").
Proof. intros fuel cutpcs g nodes i n H. rewrite <- ejcutA_fast_eq. exact H. Qed.

Definition jcert_fast (fuel : nat) (cutpcs : list Z) (g : positive) (cutsD exitsD : list (sstate * list (sv * sv))) : bool := ltac2:(tb__ "0|4|
S3S44S8S10S0S8S12S12A2A1M0A2M1G1S9S11S7S10G0R1A3A1A1Ln;VcutsD;A3S2S0S16A1M2A1S1Lx;S50Vfuel;Vcutpcs;Vg;S46G1S10S7S10G0A2M3VcutsD;A4S46G1S10G3VexitsD;A4A5G2S44S16S40VNP;SaG1VcutsD;VexitsD;A3A2R1A3Les;S6X2x2A2").
Theorem jcert_fast_eq : ltac2:(tb__ "0|1|
S4S0S25A1S24S0S8S10S0S8S12S12A2A1A2A1M0G0SeS1S5aR5R4R3R2R1A5S3fVsegs;VNP;R5R4R3R2R1A7A3FexitsD;FcutsD;Fg;Fcutpcs;Ffuel;").
Proof. intros. unfold jcert_fast, jcert. rewrite cfg_edges_fast_eq. reflexivity. Qed.
Corollary jcert_fast_ok : ltac2:(tb__ "0|1|
S4S0S25A1S24S0S8S10S0S8S12S12A2A1A2A1M0G0SeS1S5aR5R4R3R2R1A5S5A3SeS1S3fVsegs;VNP;R6R5R4R3R2A7S5A3F_;FexitsD;FcutsD;Fg;Fcutpcs;Ffuel;").
Proof. intros fuel cutpcs g cutsD exitsD H. rewrite <- jcert_fast_eq. exact H. Qed.

Definition jcertA_fast (fuel : nat) (cutpcs : list Z) (g : positive) (cutsD exitsD : list andesc) : bool := ltac2:(tb__ "0|4|
S3S44S8S10S8S0S8S12S12A2A1S37A2M0A2M1G1S9S11S7S10G0R1A3A1A1Ln;VcutsD;A3S2S0S16A1M2A1S1Lx;S50Vfuel;Vcutpcs;Vg;S46G1S10S7S10G0A2M3VcutsD;A4S46G1S10G3VexitsD;A4A5G2S44S16S33VNP;SaS30VcutsD;VexitsD;A3A2R1A3Les;S6X2x2A2").
Theorem jcertA_fast_eq : ltac2:(tb__ "0|1|
S4S0S25A1S24S0S30A1M0G0SeS1S59R5R4R3R2R1A5S35Vsegs;VNP;R5R4R3R2R1A7A3FexitsD;FcutsD;Fg;Fcutpcs;Ffuel;").
Proof. intros. unfold jcertA_fast, jcertA. rewrite cfg_edges_fast_eq. reflexivity. Qed.
Corollary jcertA_fast_ok : ltac2:(tb__ "0|1|
S4S0S25A1S24S0S30A1M0G0SeS1S59R5R4R3R2R1A5S5A3SeS1S35Vsegs;VNP;R6R5R4R3R2A7S5A3F_;FexitsD;FcutsD;Fg;Fcutpcs;Ffuel;").
Proof. intros fuel cutpcs g cutsD exitsD H. rewrite <- jcertA_fast_eq. exact H. Qed.

End S.

Section L.
Variable segs : list Segment.

Definition elcut_fast (fuel : nat) (cutpcs : list Z) (g : positive) (nodes : list lnode) (i : nat) (n : lnode) : bool := ltac2:(tb__ "0|2|
S3S9S11S1fVn;A1M0A1A1S3S4bVg;S13G0A1A2S2S0S26A1M1A1S1Lx;S66Vsegs;Vfuel;Vcutpcs;Vg;Vi;G0S46S18S10S1fVnodes;A4A7G1S44S26S2bVg;Vnodes;A2R1A3Les;S6X2x2A2A2").

Theorem elcut_fast_eq : ltac2:(tb__ "0|0|
S4S0S25A1S24S0S18A1S4S18SeS1S60R6R5R4R3R2R1A6S63Vsegs;R6R5R4R3R2R1A7A3Fn;Fi;Fnodes;Fg;Fcutpcs;Ffuel;").
Proof.
  intros. unfold elcut_fast, elcut. f_equal. f_equal.
  apply cut_check_eq. intros ec Hec. apply echeck2_c_eq; exact Hec.
Qed.
Corollary elcut_fast_ok : ltac2:(tb__ "0|0|
S4S0S25A1S24S0S18A1S4S18SeS1S60R6R5R4R3R2R1A6S5A3SeS1S63Vsegs;R7R6R5R4R3R2A7S5A3F_;Fn;Fi;Fnodes;Fg;Fcutpcs;Ffuel;").
Proof. intros fuel cutpcs g nodes i n H. rewrite <- elcut_fast_eq. exact H. Qed.

End L.

Ltac swap_in F c c' :=
  lazymatch (eval pattern c in F) with
  | ?P _ => eval cbv beta in (P c')
  end.

Ltac fast_forallb :=
  lazymatch goal with
  | |- forallb ?F ?l = true =>
      let F1 := swap_in F (@sym_run) (@sym_run_fast) in
      let F2 := swap_in F1 (@ejcert) (@ejcert_fast) in
      let F3 := swap_in F2 (@jcert) (@jcert_fast) in
      let F4 := swap_in F3 (@ejcertA) (@ejcertA_fast) in
      let F5 := swap_in F4 (@jcertA) (@jcertA_fast) in
      let F6 := swap_in F5 (@check_cfg) (@check_cfg_fast) in
      let F7 := swap_in F6 (@check_cut) (@check_cut_fast) in
      rewrite (SymStepFast.forallb_ext_eq F F7);
      [ vm_cast_no_check (@eq_refl bool true)
      | let x := fresh "x" in
        intros x; cbv beta;
        rewrite ?sym_run_fast_eq, ?ejcert_fast_eq, ?jcert_fast_eq, ?ejcertA_fast_eq, ?jcertA_fast_eq,
                ?check_cfg_fast_eq, ?check_cut_fast_eq;
        reflexivity ]
  end.
