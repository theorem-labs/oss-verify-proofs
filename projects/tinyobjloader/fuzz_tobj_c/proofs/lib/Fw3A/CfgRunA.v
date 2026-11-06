(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "list"; "bool"; "true"; "option"; "nat"; "false"; "cons"; "nil"; "app"; "Some"; "andb"; "negb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "leafA"; "sym_runA"; "ax_S"; "axwf"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "vna_state"; "edgeA"; "check_cfgA"; "check_cutA"; "check_ecfgA"; "cuts_edgesA"; "echeckA"; "leaf_okA"; "vna_var"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.CfgRun"; "runsA"; "check_cuts_r"; "runlA"; "check_ecfg_r"; "cuts_edges_r"; "nonnil"; "check_cut_r"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "forallb_lazy"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "ss_next"; "ss_lenient"; "sv_below"; "@Stdlib.Lists.List"; "forallb"; "@Stdlib.PArith.BinPos.Pos"; "leb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymCFG.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA CFGA.
Import ListNotations.
Open Scope Z_scope.

Section CfgRun.
Variable segs : list Segment.

Definition runsA (fuel : nat) (cutpcs : list Z) (cuts : list axst) : list (option (list leafA)) := ltac2:(tb__ "0|0|
S1eScS3S0SdA1A1ScSeVsegs;Vfuel;Vcutpcs;R1S2A5LT;Vcuts;A4").

Definition runlA (fuel : nat) (cutpcs : list Z) (T : axst) : list leafA := ltac2:(tb__ "0|1|
S3S0SdA1M0A1G0Lx;SeVsegs;Vfuel;Vcutpcs;VT;S2A5G0R1Ll;S7SdA1X3x2").

Definition check_cut_r (g : positive) (targets : list axst) (T : axst) (r : option (list leafA)) : bool := ltac2:(tb__ "0|2|
S1S1L_;SaSaS2bVg;S27SfVT;A1M0A1A2SbS28G0A1A1A2S10VT;A1A2S3S0SdA1M1A1S1Lr;Vr;G1S26SdS1aVg;Vtargets;A2R1A3Lleaves;S5X3x2S5X1x2").

Fixpoint check_cuts_r (g : positive) (targets cuts : list axst) (runs : list (option (list leafA))) : bool :=
  match cuts with
  | [] => true
  | T :: cs =>
      match runs with
      | r :: rs => if check_cut_r g targets T r then check_cuts_r g targets cs rs else false
      | [] => false
      end
  end.

Lemma check_cut_r_eq : ltac2:(tb__ "0|0|
S4S0S1cA1S1dS0ScA1ScS11S1S25R3R2R1SeVsegs;R5R4R1S2A5A4S16Vsegs;R5R4R3R2R1A6A3FT;Ftargets;Fg;Fcutpcs;Ffuel;").
Proof using . reflexivity. Qed.

Lemma check_cuts_r_eq : ltac2:(tb__ "0|1|
S4S0S1cA1S1dS0ScA1M0G0S11S1S20R3R2R1S1fR5R4R1A3A4S26ScS16Vsegs;R5R4R3R2A5R1A3A3Fcuts;Ftargets;Fg;Fcutpcs;Ffuel;").
Proof using .
  intros fuel cutpcs g targets cuts. induction cuts as [|T cs IH]; [reflexivity|].
  cbn [runsA map check_cuts_r forallb_lazy]. rewrite check_cut_r_eq. fold (runsA fuel cutpcs cs). rewrite IH. reflexivity.
Qed.

Theorem check_cfgA_of_runs : ltac2:(tb__ "0|2|
S4S0S1cA1S1dS0ScA1M0G0S0S3S0SdA1A1A1M1S11G1S1fR6R5R3A3R1A3S11S1S20R5S8ScR4R3A3R4R2A4S2A3S11S1S15Vsegs;R8R7R6R5R4A6S2A3F_;F_;Fruns;Fexits;Fcuts;Fg;Fcutpcs;Ffuel;").
Proof using . intros fuel cutpcs g cuts exits runs <- H. unfold check_cfgA. rewrite <- check_cuts_r_eq. exact H. Qed.

Fixpoint cuts_edges_r (g : positive) (i : nat) (cuts : list axst) (runs : list (option (list leafA)))
         (targets : list axst) : option (list edgeA) :=
  match cuts with
  | [] => Some []
  | T :: rest =>
      match runs with
      | r :: rs =>
          if negb (Pos.leb g (ss_next (ax_S T)) && negb (ss_lenient (ax_S T)) && axwf T) then None else
          match r with
          | Some leaves =>
              match leaves_edgesA g i leaves targets, cuts_edges_r g (S i) rest rs targets with
              | Some es, Some es' => Some (es ++ es')
              | _, _ => None
              end
          | None => None
          end
      | [] => None
      end
  end.

Lemma cuts_edges_r_eq : ltac2:(tb__ "0|1|
S4S0S1cA1S1dS0ScA1M0S4G0S11S3S0S14A1A1S23R4R2R3S1fR6R5R3A3R1A5S18Vsegs;R6R5R4R2R3R1A7A3Ftargets;Fi;Fcuts;Fg;Fcutpcs;Ffuel;").
Proof using .
  intros fuel cutpcs g cuts. induction cuts as [|T rest IH]; intros i targets; [reflexivity|].
  cbn [runsA map cuts_edges_r cuts_edgesA]. fold (runsA fuel cutpcs rest). rewrite IH. reflexivity.
Qed.

Definition check_ecfg_r (g : positive) (cuts exits : list vnodeA) (runs : list (option (list leafA))) : bool := ltac2:(tb__ "0|2|
SaS2aS12S12S29S27SfS13R1A1A1A1S1bR1A1A2Ln;Vcuts;A3S3S0S14A1M0A1S1Lx;S23Vg;U0S1eS12ScS13Vcuts;A4M1Vruns;S8ScG1S1eS12ScS13Vexits;A4A3A5G0S2aS14S19Vg;S8S12Vcuts;Vexits;A3A2R1A3Les;S5X3x2A2").

Theorem check_ecfgA_of_runs : ltac2:(tb__ "0|2|
S4S0S1cA1S1dS0S12A1M0G0S0S3S0SdA1A1A1M1S11G1S1fR6R5S1eS12ScS13R3A4A3R1A3S11S1S22R5R4R3R2A4S2A3S11S1S17Vsegs;R8R7R6R5R4A6S2A3F_;F_;Fruns;Fexits;Fcuts;Fg;Fcutpcs;Ffuel;").
Proof using .
  intros fuel cutpcs g cuts exits runs <- H. unfold check_ecfgA, cfg_edgesA. unfold check_ecfg_r in H.
  rewrite cuts_edges_r_eq in H. exact H.
Qed.

Lemma run_of_runl : ltac2:(tb__ "0|1|
S4S0S1cA1ScS0SdA1M0S11G0S21R4R3R2A3R1A3S11S1G0S1Ll;R2S5SdG0S2Ll1;Ll0;X0x2S2A3S11S3G0A1SeVsegs;R6R5R4S2A5S9G0R3A2A3F_;F_;Fl;FT;Fcutpcs;Ffuel;").
Proof using .
  intros fuel cutpcs T l E N. unfold runlA in E. destruct (sym_runA segs fuel cutpcs T true) as [l0|].
  - subst l0. reflexivity.
  - subst l. discriminate.
Qed.

Definition nonnil (l : list leafA) : bool := ltac2:(tb__ "0|1|
S0SdA1M0S1Ll;Vl;S5SdG0S2Ll1;Ll0;X0x2").

Theorem check_cfgA_of_runl : ltac2:(tb__ "0|4|
S4S0S1cA1S1dScS0ScA1S0SdA1M0S11G0S21R6R5R3A3R1A3S11S1S1S1L_;S24R2A1S20R5S8ScS6ScR4S7ScA1M1A3M2R3A3G2S6S3G0A1M3S9G0R2A2S7G3A1A3A4S5X1x2S2A3S11S1S15Vsegs;R8R7R6S6ScR5G1A3R4A6S2A3F_;F_;Fl;Fexits;FT;Fg;Fcutpcs;Ffuel;").
Proof using .
  intros fuel cutpcs g T exits l E H. destruct (nonnil l) eqn:N; [|discriminate].
  apply (check_cfgA_of_runs fuel cutpcs g [T] exits [Some l]); [|exact H].
  cbn [runsA map]. rewrite (run_of_runl fuel cutpcs T l E N). reflexivity.
Qed.

Theorem check_ecfgA_of_runl : ltac2:(tb__ "0|3|
S4S0S1cA1S1dS12S0S12A1S0SdA1M0S11G0S21R6R5S13R3A1A3R1A3S11S1S1S1L_;S24R2A1S22R5S6S12R4S7S12A1M1A3R3S6S3G0A1M2S9G0R2A2S7G2A1A3A4S5X1x2S2A3S11S1S17Vsegs;R8R7R6S6S12R5G1A3R4A6S2A3F_;F_;Fl;Fexits;FvT;Fg;Fcutpcs;Ffuel;").
Proof using .
  intros fuel cutpcs g vT exits l E H. destruct (nonnil l) eqn:N; [|discriminate].
  apply (check_ecfgA_of_runs fuel cutpcs g [vT] exits [Some l]); [|exact H].
  cbn [runsA map]. rewrite (run_of_runl fuel cutpcs (vna_state vT) l E N). reflexivity.
Qed.

End CfgRun.
