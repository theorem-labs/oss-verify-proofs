(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "N"; "Zneg"; "Zpos"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "valuation"; "SPUle"; "sobj"; "SAlu"; "SLit"; "rm"; "ss_next"; "sprop"; "ss_facts"; "ss_objs"; "holds"; "obj_range"; "sstate"; "agree_below"; "eval"; "ob_base"; "ob_hi"; "ob_lo"; "obj_holds"; "ranges_disjoint"; "sprop_below"; "sv_eqb"; "SAluW"; "SExt"; "SLBytes"; "SMd"; "SMdW"; "SVar"; "enc_bytes"; "mkSS"; "smatch"; "ss_fcsr"; "ss_fregs"; "ss_lenient"; "ss_pc"; "ss_regs"; "ss_resv"; "swf"; "@Corelib.Init.Datatypes"; "prod"; "list"; "bool"; "andb"; "nat"; "true"; "pair"; "option"; "orb"; "Some"; "false"; "fst"; "snd"; "app"; "None"; "@Corelib.Init.Logic"; "eq"; "and"; "ex"; "not"; "or"; "iff"; "@Stdlib.ZArith.BinInt.Z"; "le"; "leb"; "lt"; "add"; "pow"; "of_nat"; "ltb"; "sub"; "mul"; "div"; "eqb"; "to_nat"; "opp"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "prove_sprop"; "set_objs"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "bv_unsigned"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "aluop"; "mulop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "acell"; "mkACell"; "c_addr"; "c_w"; "c_val"; "cells_ok"; "in_rangesZ"; "view"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "leafA"; "la_state"; "ax_setS"; "ax_X"; "ax_base"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvJ"; "lcarve"; "lcell"; "lc_obj"; "acell_eqb"; "all_coveredb"; "cells_insideb"; "lc_cells"; "lc_acells"; "obj_clear_litb"; "obj_clear_litb2"; "xr_clear_litb"; "carve_okb"; "coveredb"; "in_bandb"; "lc_okb"; "lc_spec"; "lcs_disjb"; "presentb"; "tracked_objb"; "@Corelib.Lists.ListDef"; "map"; "Forall"; "nth"; "@Stdlib.Lists.List"; "In"; "forallb"; "existsb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "KcA"; "Kc_ok"; "alloc_lawsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "LQA"; "smatchA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "ndesc"; "nd_below"; "JA"; "ANone"; "JAi"; "amode"; "nd_am"; "nd_tv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue"; "rd_of"; "wok_of"; "carved"; "cells_inside"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "SHADOW_OFF"; "SHADOW_BAND_HI"; "SHADOW_BAND_LO"; "Sh"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvJ.WithSegs.JAcarve"; "JAiK"; "JAK"; "uncarve_okb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_absorb"; "rho_sub"; "wsub"; "in_ranges"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM"; "carve_spec"; "carve_obj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "vms"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkA"; "entails_frA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "uval"; "@Stdlib.Arith.PeanoNat.Nat"; "leb"; "eqb"; "@Corelib.Init.Peano"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvJ.WithSegs"; "tv_bandfree"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "tnz"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundL SymSoundV SymSoundW SymSoundM SymSoundR SymComplete SymFrame SymObj SymEntail SymCFG SymSummary Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA SummaryA GlueA CFGA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require BudA TobjJA TobjJAR.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.CertGlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import ImageFacts Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition law_view_stmt (AInvA : AA -> valuation -> list word -> Model -> Prop) : Prop := ltac2:(tb__ "0|1|
S93S6S6S2dS50Q40A1M0A1S65VAInvA;R5R4R2R1A4G0S3bS33S50Q8A1A1S8fSaaSbR5A1R1A3S8fSaaSbR6A1R1A3A3Fa;VAInvA;R7R5R4R3A4F_;F_;Fmd;Ftp;Frho';Frho;FA;").

Definition lcell : Type := (Z * nat * Z)%type.
Definition lcarve : Type := ltac2:(tb__ "0|0|
S2cS2cS0S0A2S2dS68A1A2").
Definition lc_cells (cs : list lcell) : list (Z * nat * sv) := ltac2:(tb__ "0|3|
S7aS2cS2cS0S30A2M0S0A2M1S2cG0S5A2M2G1G1G2Lc;R1G0S0G0G2Ly;R2S0S30S32G0S5S32S0S30R2R1A4SaR3A1A4Lk;La;X2cx1Lv;Ly;X2cx1Lc;Vcs;A4").
Definition lc_obj (c : lcarve) : sobj := ltac2:(tb__ "0|2|
S2cS2cS0S0A2M0S2dS68A1M1A2S8Lc;Vc;G0G1G0S8Lp;R2S0S0S91SaZ0A1R2R1S6dR3A1A4Lhi;Llo;X2cx1Lcs;Lp;X2cx1").
Definition lc_acells (cs : list lcell) : list acell := ltac2:(tb__ "0|2|
S7aS2cS2cS0S30A2M0S0A2M1S56G1G1S56Lc;R1G0S0G0S56Ly;R2S0S30S57R2R1R3A3Lk;La;X2cx1Lv;Ly;X2cx1Lc;Vcs;A4").
Definition lc_spec (c : lcarve) : carve_spec := ltac2:(tb__ "0|3|
S2cS2cS0S0A2M0S2dS68A1M1A2Sa2Lc;Vc;G0G1G0Sa2Lp;R2S0S0S32S2cS2cS5S0A2M2S0A2S2dS2cS2cS0S30A2S5A2A1S32G2S0S32S5S0SaZ0A1R2A4R1A4S6dR3A1A4Lhi;Llo;X2cx1Lcs;Lp;X2cx1").

Definition acell_eqb (c d : acell) : bool := ltac2:(tb__ "0|0|
S2fS2fS4bS58Vc;A1S58Vd;A1A2Sb1S59Vc;A1S59Vd;A1A2A2S4bS5aVc;A1S5aVd;A1A2A2").
Lemma acell_eqb_sound : ltac2:(tb__ "0|0|
S56S56S3bS2eS6aR2R1A2S31A3S3bS56R3R2A3F_;Fd;Fc;").
Proof.
  intros [a k v] [a' k' v'] H. unfold acell_eqb in H. cbn in H.
  apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply Z.eqb_eq in H1. apply Nat.eqb_eq in H2. apply Z.eqb_eq in H3. subst. reflexivity.
Qed.

Definition cells_insideb (lo hi : Z) (cs : list lcell) : bool := ltac2:(tb__ "0|2|
S7eS2cS2cS0S30A2M0S0A2M1G1G1S2eLc;R1G0S0G0S2eLy;R2S0S30S2fS2fS2fS42Vlo;R2A2S42S44R2S46R1A1A2Vhi;A2A2Sb0U1R1A2A2Sb0R1U8A2A2Lk;La;X2cx1Ly0;Ly;X2cx1Lc;Vcs;A3").

Definition coveredb (cs : list lcell) (z : Z) : bool := ltac2:(tb__ "0|2|
S7fS2cS2cS0S30A2M0S0A2M1G1G1S2eLc;R1G0S0G0S2eLy;R2S0S30S2fS42R2Vz;A2S47Vz;S44R2S46R1A1A2A2A2Lk;La;X2cx1Ly0;Ly;X2cx1Lc;Vcs;A3").
Fixpoint all_coveredb (cs : list lcell) (z : Z) (n : nat) : bool :=
  match n with O => true | S n' => coveredb cs z && all_coveredb cs (z + 1) n' end.

Definition obj_clear_litb (facts : list sprop) (lo hi : Z) (o : sobj) : bool := ltac2:(tb__ "0|f|
S5S2eLx;M0S15Vo;A1S0S0S2eLz;R1SaZ0A1S5G0S17Vo;A1M1S0SaR1A1S5G0S16Vo;A1S0S2fS2fS2fS42S4dS45Z2Z3eA2M2A1R3A2S42R3R1A2A2S47R1G2A2A2S34S42R1Vlo;A2S42Vhi;R3A2A2A2Lh;S1S4eVfacts;S7SaVhi;A1M3S9S53R4R2A3A2A2Li;S54S5S5S4eVfacts;S7G3S9S53R6R4A3A2A2M4Lb0;La;M5Lop;M6G6S55G5Lop;M7G7S2eS2S5G4La;Lw;Lsgn;S1S5S0G4Lk;Li;Ll0;X5x8Tl;Ll;S1S4eVfacts;S7G3S9S53R2S21R1A1M8A3A2A2Li;S54S5S5S4eVfacts;S7G3S9S53R4S9R3R2R1A3M9A3A2A2Lb0;La;Lop;S54S5S5S4eVfacts;S7G3S9S53R4S1cR3R2R1A3MaA3A2A2Lb0;La;Lop;S55S5S5S4eVfacts;S7G3S9S53R4S1fR3R2R1A3MbA3A2A2Lb0;La;Lop;S55S5S5S4eVfacts;S7G3S9S53R4S20R3R2R1A3McA3A2A2Lb0;La;Lop;S2eS2S5S4eVfacts;S7G3S9S53R4S1dR3R2R1A3MdA3A2A2La;Lw;Lsgn;S1S5S0S4eVfacts;S7G3S9S53R4S1eR3R2R1A3MeA3A2A2Lk;Li;Ll0;X5x8Tb;S1S4eVfacts;S7G3S9S53SaS4R1A1A1G1A3A2A2Lp;S1S4eVfacts;S7G3S9S53SaS3R1A1A1G1A3A2A2Lp;X0x3Lz;S1S4eVfacts;S7G3S9S53G8G1A3A2A2Li;S54S5S5S4eVfacts;S7G3S9S53G9G1A3A2A2Lb0;La;Lop;S54S5S5S4eVfacts;S7G3S9S53GaG1A3A2A2Lb0;La;Lop;S55S5S5S4eVfacts;S7G3S9S53GbG1A3A2A2Lb0;La;Lop;S55S5S5S4eVfacts;S7G3S9S53GcG1A3A2A2Lb0;La;Lop;S2eS2S5S4eVfacts;S7G3S9S53GdG1A3A2A2La;Lw;Lsgn;S1S5S0S4eVfacts;S7G3S9S53GeG1A3A2A2Lk;Li;Ll0;X5x8").

Definition xr_clear_litb (facts : list sprop) (lo hi : Z) (r : sv * sv) : bool := ltac2:(tb__ "0|8|
S44S49Z8M0S48Vhi;S95A2A2Z40M1A2S0S48S49G0S48Vlo;S95A2A2G1A2S0S34S34S42Vhi;S48S95G0A2A2S2fS2fS42Z0M2R2A2S47R2S45Z2M3G1A2M4A2A2S4eVfacts;S7SaR2A1S37S5S5Vr;A3M5A2A2A2A2S2fS2fS2fS2fS42G2R1A2S47R1G4A2A2S4eVfacts;S7S9S53G5S38S5S5Vr;A3M6A3SaR1A1A2A2A2S4eVfacts;S7G6SaS45G3Z30A2A1M7A2A2A2S4eVfacts;S7G5G7A2A2A2A2Ta3;Ta2;").

Definition presentb (KP : list (Z * Z)) (lo hi : Z) : bool := ltac2:(tb__ "0|1|
S7fS2cS0S0A2M0G0S2fS42S37S0S0R1A3Vlo;A2S42Vhi;S38S0S0R1A3A2A2Lr;VKP;A3").

Definition in_bandb (lo hi : Z) : bool := ltac2:(tb__ "0|0|
S2fS42S97Vlo;A2S42Vhi;S96A2A2").
Definition tracked_objb (facts : list sprop) (tv : list (sv * sv)) (o : sobj) : bool := ltac2:(tb__ "0|7|
S5S2eLx;S17Vo;A1S0S0S2eLz;R1S2fS2fS7fS2cS5S5A2M0G0S2fS1bS37S5S5R1A3S15Vo;A1M1A2S1bS38S5S5R1A3S16Vo;A1M2A2A2Lt;Vtv;A3S4eVfacts;S7SaZ1A1G1A2A2A2S4eVfacts;S7G2SaS45Z2Z3eA2A1A2A2A2S1S36Lp;M3G3X0x3Lz;S1S36Li;S54S5S5S36Lb;La;M4Lop;M5G5S55G4Lop;M6G6S2eS2S5S36La;Lw;Lsgn;S1S5S0S36Lk;Li;Ll;X5x8").
Definition obj_clear_litb2 (facts : list sprop) (tv : list (sv * sv)) (lo hi : Z) (o : sobj) : bool := ltac2:(tb__ "0|0|
S34S6fVfacts;Vlo;Vhi;Vo;A4S2fS74Vlo;Vhi;A2S79Vfacts;Vtv;Vo;A3A2A2").

Definition lc_okb (facts : list sprop) (objs : list sobj) (X : list (sv * sv)) (KV : list acell) (KP : list (Z * Z)) (tv : list (sv * sv)) (c : lcarve) : bool := ltac2:(tb__ "0|2|
S2cS2cS0S0A2M0S2dS68A1M1A2S2eLc;Vc;G0G1G0S2eLp;R2S0S0S2fS2fS2fS2fS2fS2fS2fS42Z0R2A2S42R2R1A2A2S47R1S45Z2Z3eA2A2A2S6cR2R1R3A3A2S34S6bR3R2S4cS48R1R2A2A1A3S78VKP;R2R1A3A2A2S7eS56S56S7fS56S6aR1A1VKV;A3Lc;S6eR3A1A3A2S7eS8S70Vfacts;Vtv;R2R1A4Vobjs;A3A2S7eS2cS5S5A2S71Vfacts;R2R1A3VX;A3A2Lhi;Llo;X2cx1Lcs;Lp;X2cx1").

Definition lc_disjb (c d : lcarve) : bool := ltac2:(tb__ "0|3|
S2cS2cS0S0A2M0S2dS68A1M1A2M2S2eLc;Vc;G0G1G0S2eLp;R2S0S0G2S2eLd;Vd;G0G1G0S2eLp0;R2S0S0S34S42R5R2A2S42R1R6A2A2Lhi';Llo';X2cx1Ll0;Lp0;X2cx1Lhi;Llo;X2cx1Ll;Lp;X2cx1").
Fixpoint lcs_disjb (N : list lcarve) : bool :=
  match N with [] => true | c :: r => forallb (lc_disjb c) r && lcs_disjb r end.

Definition carve_okb (facts : list sprop) (objs : list sobj) (X : list (sv * sv)) (KV : list acell) (KP : list (Z * Z)) (tv : list (sv * sv)) (N : list lcarve) : bool := ltac2:(tb__ "0|0|
S2fS7eS67S75Vfacts;Vobjs;VX;VKV;VKP;Vtv;A6VN;A3S77VN;A1A2").

Section WithSegs.
Let segs := segs.

Lemma cells_insideb_sound : ltac2:(tb__ "0|0|
S0S0S2dS68A1S3bS2eS6cR3R2R1A3S31A3S92R4R3S6dR2A1A3F_;Fcs;Fhi;Flo;").
Proof.
  intros lo hi cs H. unfold cells_inside, lc_cells. apply Forall_forall. intros x Hx.
  apply in_map_iff in Hx as ([[a k] v] & <- & Hin).
  pose proof (proj1 (forallb_forall _ _) H _ Hin) as Hb. cbn beta iota in Hb.
  apply andb_prop in Hb as [Hb H4]. apply andb_prop in Hb as [Hb H3]. apply andb_prop in Hb as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2. apply Nat.leb_le in H3. apply Nat.leb_le in H4. cbn. lia.
Qed.

Lemma coveredb_sound : ltac2:(tb__ "0|1|
S2dS68A1S0S3bS2eS73R2R1A2S31A3S3dS0S0S3dS30S30S3dS0S0S3cS7dS2cS2cS0S30A2M0S0A2S32G0S0S32S0S30R3R2A4R1A4R6A3S3cS41R3R5A2S43R5S44R3S46R2A1A2A2A2A2Lv;A2Lk;A2La;A2F_;Fz;Fcs;").
Proof.
  intros cs z H. unfold coveredb in H. apply existsb_exists in H as ([[a k] v] & Hin & Hb).
  apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. exists a, k, v. auto.
Qed.

Lemma all_coveredb_sound : ltac2:(tb__ "0|1|
S2dS68A1S30S0S0S3bS2eS6bR4R2R3A3S31A3S3cS41R3R2A2S43R2S44R3S46R4A1A2A2A2S3dS0S0S3dS30S30S3dS0S0S3cS7dS2cS2cS0S30A2M0S0A2S32G0S0S32S0S30R3R2A4R1A4R9A3S3cS41R3R6A2S43R6S44R3S46R2A1A2A2A2A2Lv;A2Lk;A2La;A2F_;F_;Fz;Fz0;Fn;Fcs;").
Proof.
  intros cs n. induction n as [|n IH]; intros z0 z H Hz; [lia|].
  cbn [all_coveredb] in H. apply andb_prop in H as [H1 H2].
  destruct (Z.eq_dec z z0) as [->|Hne]; [apply coveredb_sound; exact H1|].
  apply (IH (z0 + 1) z H2). lia.
Qed.

Lemma obj_clear_litb_sound : ltac2:(tb__ "0|0|
S6S94S2dSdA1S0S0S8S18Vsegs;R6R5R1A4S7bSdS10R7A1R5A3S3cS41Z0R5A2S41R5R4A2A2S43R5S45Z2Z3eA2A2S3bS2eS6fR8R7R6R5A4S31A3S19S11RbR6A2S32S0S0R8R7A4A2F_;F_;F_;F_;F_;Fo;Fhi;Flo;Ffacts;Fms;Frho;").
Proof.
  intros rho ms facts lo hi o Ho HF Hlh Hh62 H.
  destruct Ho as ((B1 & B2 & B3 & B4) & _).
  unfold obj_range. unfold obj_lo_of, obj_hi_of in *.
  unfold obj_clear_litb in H.
  assert (GEN : prove_sprop facts (SPUle (SLit hi) (SAlu ALU_ADD (ob_base o) (ob_lo o))) = true ->
                ranges_disjoint (bv_unsigned (eval rho (ob_base o)) + soff rho (ob_lo o), bv_unsigned (eval rho (ob_base o)) + soff rho (ob_hi o)) (lo, hi)).
  { intros HP. pose proof (prove_sprop_sound rho facts _ HF HP) as HH. cbn [holds] in HH.
    rewrite U_lit, U_add in HH. rewrite <- !M64v_eq in HH.
    set (b := bv_unsigned (eval rho (ob_base o))) in *.
    assert (EQ : bv_unsigned (eval rho (ob_lo o)) mod 2 ^ 64 = soff rho (ob_lo o) mod 2 ^ 64).
    { unfold soff. pose proof (urange (eval rho (ob_lo o))).
      destruct (Z.ltb_spec (bv_unsigned (eval rho (ob_lo o))) (2 ^ 63)).
      - rewrite signed_small by lia. reflexivity.
      - rewrite signed_big by lia. replace (bv_unsigned (eval rho (ob_lo o)) - 2 ^ 64) with (bv_unsigned (eval rho (ob_lo o)) + (-1) * 2 ^ 64) by lia.
        rewrite Z.mod_add by lia. reflexivity. }
    assert (E2 : (b + bv_unsigned (eval rho (ob_lo o))) mod 2 ^ 64 = (b + soff rho (ob_lo o)) mod 2 ^ 64).
    { rewrite <- Zplus_mod_idemp_r. rewrite EQ. rewrite Zplus_mod_idemp_r. reflexivity. }
    rewrite E2 in HH. rewrite (Z.mod_small hi) in HH by lia.
    unfold ranges_disjoint. cbn [fst snd].
    destruct (Z.eq_dec (b + soff rho (ob_lo o)) (2 ^ 64)) as [E|E].
    - rewrite E in HH. rewrite Z_mod_same_full in HH. lia.
    - rewrite Z.mod_small in HH by lia. lia. }
  destruct (ob_base o) eqn:EB; try (apply GEN; exact H).
  destruct (Z.eq_dec z 0) as [->|Hz].
  2: { destruct z; try (apply GEN; exact H); try lia. all: destruct (ob_lo o); try (apply GEN; exact H); destruct (ob_hi o); apply GEN; exact H. }
  destruct (ob_lo o) eqn:EL; try (apply GEN; exact H).
  destruct (ob_hi o) eqn:EH; try (apply GEN; exact H).
  apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.ltb_lt in H3.
  rewrite !soff_lit_small by lia. cbn [eval]. rewrite lit_unsigned, Z.mod_small by lia.
  unfold ranges_disjoint. cbn [fst snd]. apply orb_prop in H4 as [H4|H4]; apply Z.leb_le in H4; lia.
Qed.

Definition tv_bandfree (rho : valuation) (tv : list (sv * sv)) : Prop := ltac2:(tb__ "0|2|
S2cS5S5A2M0S7dG0R1Vtv;A3Sb4Vrho;R2A2S0S3cS41SafVrho;S37S5S5R4A3A2M1R1A2S43R1S44G1SafVrho;S38S5S5R4A3A2A2A2A2S3fS43R2S97A2S41S96R2A2A2F_;Fa;F_;F_;Ft;").

Lemma obj_clear_litb2_sound : ltac2:(tb__ "0|0|
S6S94S2dSdA1S2dS2cS5S5A2A1S0S0S8S18Vsegs;R7R6R1A4S7bSdS10R8A1R6A3S3cS41Z0R5A2S41R5R4A2A2S43R5S45Z2Z3eA2A2Sb3RbR8A2S3bS2eS70RaR9R8R7R6A5S31A3S19S11RdR7A2S32S0S0R9R8A4A2F_;F_;F_;F_;F_;F_;Fo;Fhi;Flo;Ftv;Ffacts;Fms;Frho;").
Proof.
  intros rho ms facts tv lo hi o Ho HF Hlh Hh62 HTV H. unfold obj_clear_litb2 in H.
  apply orb_prop in H as [H|H]; [exact (obj_clear_litb_sound rho ms facts lo hi o Ho HF Hlh Hh62 H)|].
  apply andb_prop in H as [HB HT]. unfold in_bandb in HB. apply andb_prop in HB as [HB1 HB2]. apply Z.leb_le in HB1. apply Z.leb_le in HB2.
  unfold tracked_objb in HT. destruct (ob_lo o) as [zlo| | | | | | |] eqn:EL; try discriminate.
  destruct zlo; try discriminate.
  apply andb_prop in HT as [HT HP2]. apply andb_prop in HT as [HT HP1].
  apply existsb_exists in HT as ([tb tn] & Hin & Heq). cbn [fst snd] in Heq. apply andb_prop in Heq as [E1 E2].
  apply sv_eqb_sound in E1. apply sv_eqb_sound in E2.
  pose proof (prove_sprop_sound rho facts _ HF HP1) as Q1. pose proof (prove_sprop_sound rho facts _ HF HP2) as Q2.
  cbn [holds] in Q1, Q2. rewrite U_lit, <- M64v_eq in Q1. rewrite U_lit, <- M64v_eq in Q2.
  change (1 mod 2 ^ 64) with 1 in Q1. change (2 ^ 62 mod 2 ^ 64) with (2 ^ 62) in Q2.
  assert (Hz : TobjJV.tnz rho (tb, tn)) by (unfold TobjJV.tnz; cbn [fst]; rewrite E1; lia).
  pose proof (HTV (tb, tn) Hin Hz) as HA. cbn [fst snd] in HA. unfold uval in HA. rewrite E1, E2 in HA.
  unfold obj_range, obj_lo_of, obj_hi_of. rewrite EL. rewrite soff_lit_small by lia.
  unfold soff at 1. rewrite signed_small by lia.
  set (x := bv_unsigned (eval rho (ob_base o))) in *. set (n := bv_unsigned (eval rho (ob_hi o))) in *.
  unfold ranges_disjoint. cbn [fst snd].
  destruct (Z_le_gt_dec (x + n) lo); [lia|]. destruct (Z_le_gt_dec hi x); [lia|].
  destruct (Z_le_gt_dec (x + n) (x + 0)); [lia|]. destruct (Z_le_gt_dec hi lo); [lia|].
  exfalso. pose proof (HA (Z.max x lo) ltac:(lia)). lia.
Qed.

Lemma xr_clear_litb_sound : ltac2:(tb__ "0|5|
S6S2dSdA1S0S0S2cS5S5A2S0S0S0S7bSdS10R8A1R7A3S3cS41Z0M0R7A2S41R7R6A2A2S3bS0R5S95A3S3bS2eS71RaR9R8R7A4S31A3S3cS41S52Q40M1S14RcS37S5S5R8A3A2A2M2R6A2S43R6S44G2S52G1S14RcS38S5S5R8A3A2A2A2A2A2S3cS41G0R6A2S43R6Z8M3A2A2S3eS3cS41RcS44S49S4aS44R9S4aR8G3A2A2G3A2G3A2R7A2M4A2S43G4RbA2A2A1F_;F_;F_;F_;F_;F_;Fj;Fy;Fbase;Fr;Fhi;Flo;Ffacts;Frho;").
Proof.
  intros rho facts lo hi r base y j HF Hlh -> H Hy Hj.
  pose proof (urange (eval rho (fst r))) as R1. pose proof (urange (eval rho (snd r))) as R2.
  unfold xr_clear_litb in H. cbn zeta in H. unfold SHADOW_OFF in *.
  pose proof (Z.div_mod y 8 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound y 8 ltac:(lia)) as M1.
  pose proof (Z.div_mod (140737219919872 + y / 8) 8 ltac:(lia)) as D2. pose proof (Z.mod_pos_bound (140737219919872 + y / 8) 8 ltac:(lia)) as M2.
  apply orb_prop in H as [H|H]; [apply orb_prop in H as [H|H]|].
  - apply Z.leb_le in H. lia.
  - apply andb_prop in H as [H HP]. apply andb_prop in H as [Ha Hb]. apply Z.leb_le in Ha. apply Z.ltb_lt in Hb.
    pose proof (prove_sprop_sound rho facts _ HF HP) as HH. cbn [holds] in HH. rewrite U_lit in HH. rewrite <- !M64v_eq in HH.
    rewrite Z.mod_small in HH by lia. lia.
  - apply andb_prop in H as [H HP3]. apply andb_prop in H as [H HP2]. apply andb_prop in H as [H HP1]. apply andb_prop in H as [Ha Hb].
    apply Z.leb_le in Ha. apply Z.ltb_lt in Hb.
    pose proof (prove_sprop_sound rho facts _ HF HP1) as H1. cbn [holds] in H1. rewrite U_lit, U_add in H1. rewrite <- !M64v_eq in H1.
    pose proof (prove_sprop_sound rho facts _ HF HP2) as H2. cbn [holds] in H2. rewrite U_lit in H2. rewrite <- !M64v_eq in H2.
    pose proof (prove_sprop_sound rho facts _ HF HP3) as H3. cbn [holds] in H3. rewrite U_lit in H3. rewrite <- !M64v_eq in H3.
    rewrite (Z.mod_small (2 ^ 48)) in H2, H3 by lia.
    rewrite (Z.mod_small (bv_unsigned (eval rho (fst r)) + bv_unsigned (eval rho (snd r)))) in H1 by lia.
    rewrite Z.mod_small in H1 by lia. lia.
Qed.

Lemma wok_of_imageA : ltac2:(tb__ "0|1|
S50Q40M0A1S33S50Q8A1A1F_;S0S3cS41Ze1000R1A2S43R1Z643000A2A2S3bS2eS90Vsegs;R3S51G0R2A2A3S31A3F_;Fz;Fm;").
Proof.
  intros m z Hz. unfold wok_of. destruct (m (Z_to_bv 64 z)); [reflexivity|].
  unfold wseg_addr. rewrite u64_lit by lia.
  destruct (byte_cond_A z Hz) as [_ (seg & b & Hf & Hw & _)].
  change ImageFacts.segsA with segs in Hf. rewrite Hf. exact Hw.
Qed.
Lemma rd_of_imageA : ltac2:(tb__ "0|3|
S50Q40M0A1S33S50Q8A1M1A1M2F_;S0S3cS41Ze1000R1A2S43R1Z643000A2A2S3dG1G1S3bG2S8fVsegs;R4S51G0R3A2A3S35G1R1A2A3Lx;A2F_;Fz;Fm;").
Proof.
  intros m z Hz. unfold rd_of. destruct (m (Z_to_bv 64 z)) as [b|]; [exists b; reflexivity|].
  destruct (byte_cond_A z Hz) as [[b Hb] _]. exists b. exact Hb.
Qed.
Lemma segs_topA : InitState.segs_top segs <= IMG_HI.
Proof. apply Z.leb_le. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma rd_of_high : ltac2:(tb__ "0|3|
S50Q40M0A1S33S50Q8A1A1M1F_;S0S3cS41Z643000R1A2S43R1S45Z2Z40A2A2A2S3bG1S8fVsegs;R3S51G0R2A2M2A3R3G2A1A3F_;Fz;Fm;").
Proof.
  intros m z Hz. apply (TobjJAR.rd_of_high segs segs_topA). rewrite u64_lit by lia. unfold IMG_HI. lia.
Qed.

Lemma map_lc : ltac2:(tb__ "0|0|
S2dS67A1S3bS2dS8A1S7aSa2S8Sa3S7aS67Sa2S76R1A4A4S7aS67S8S69R1A4A3FN;").
Proof. induction N as [|[[lo hi] cs] N IH]; [reflexivity|]. cbn [map]. rewrite IH. reflexivity. Qed.

Lemma lc_obj_range : ltac2:(tb__ "0|3|
S6S0S0S2dS68A1M0S41Z0R3A2S41R4R3A2S43R4S45Z2Z3eA2A2S3bS2cS0S0A2M1S11R7S69S32G1G0S32S0S0R6R5A4M2R4A4A1A2G2A3F_;F_;F_;Fcs;Fhi;Flo;Frho;").
Proof.
  intros rho lo hi cs H1 H2 H3. unfold lc_obj, carved, obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi eval].
  rewrite lit_unsigned, Z.mod_small by lia. rewrite !soff_lit_small by lia. reflexivity.
Qed.

Section JAcarve.
Variable AInv : ltac2:(tb__ "0|0|
S93S6S2dS50Q40A1A1S65OF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : ltac2:(tb__ "0|0|
S82Vsegs;VAInv;VCST;A3").
Hypothesis HLV : law_view_stmt AInv.
Variable NP : positive.
Variable rho0 : valuation.
Variable P0f : valuation -> Prop.
Variable FB : list (Z * Z).
Variable FF : ltac2:(tb__ "0|0|
S2dS2cS2cS0S0A2S0A2A1").
Variable BX : bxt.
Variable PA : AA -> Prop.

Variable KV : list acell.
Definition JAK (Kc : KcA) (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
S89VAInv;VCST;VXGL;VNP;VKc;Vrho0;VP0f;VFB;VFF;VBX;VPA;Vnd;Ac").
Definition JAiK (Kc : KcA) (nd : ndesc) (Ai : AA) (kc : Z) : jpredA := ltac2:(tb__ "0|0|
S8bVAInv;VCST;VXGL;VNP;VKc;Vrho0;VP0f;VFB;VFF;VBX;VPA;Vnd;VAi;Vkc;Ae").
Hypothesis HKV : ltac2:(tb__ "0|0|
S80S87S93S0S6S2dS50Q40A1A1S2dS66A1S65S9bR8R7R6R5R4R3R2R1A8S5bS5dVsegs;SbR5A1A2VKV;A2F_;Fmd;Ftr;Ftp;Frho;Fkc;FAi;Fnd;FKc;").
Hypothesis HKVrng : ltac2:(tb__ "0|3|
S56S7dS56R1VKV;A3S3fS3cS41Ze1000S58R2A1M0A2S41S44G0S46S59R2A1A1A2M1Z643000M2A2A2S3cS41G2G0A2S41G1S45Z2Z3eA2A2A2A2F_;Fc;").

Variable KP : list (Z * Z).
Hypothesis HKP : ltac2:(tb__ "0|2|
S80S87S93S0S6S2dS50Q40M0A1A1S2dS66A1S65S0S0S0S9bRbRaR9R8R7R6R5R4A8S7dS2cS0S0A2S32S0S0R4R3A4VKP;A3S3cS41R5R3A2S43R3R4A2A2S3cS3cS41Z643000R4A2S43R4S45Z2Z40A2A2A2S3eS3bS33S50Q8A1M1A1SbRaS51G0R4A2A2S3aG1A1A3A1A2F_;F_;F_;Fz;Fhi;Flo;Fmd;Ftr;Ftp;Frho;Fkc;FAi;Fnd;FKc;").

Lemma KV_cell : ltac2:(tb__ "0|3|
S80S87S93S0S6S2dS50Q40M0A1A1S2dS66A1S65S0S30S0S9bRbRaR9R8R7R6R5R4A8S7dS56S57R4R3R2A3VKV;A3S30Sb2R1R5A2S3bS33S50Q8M1A1M2A1S8fVsegs;SbRbA1S51G0S44R7S46R2A1A2A2A3S35G2S7cG2R2S22R6S51G0R5A2A2S51G1Z0A2A4A2A3F_;Fj;F_;F_;Fv;Fk;Fa;Fmd;Ftr;Ftp;Frho;Fkc;FAi;Fnd;FKc;").
Proof using HKV HKVrng.
  intros Kc nd Ai kc rho tp tr md a k v HJ Hin j Hj.
  pose proof (proj1 (Forall_forall _ _) (HKV _ _ _ _ _ _ _ _ HJ) _ Hin j Hj) as C. cbn [c_addr c_w c_val] in C.
  destruct (HKVrng _ Hin) as [R|R]; cbn [c_addr c_w] in R; rewrite view_in in C by lia; exact C.
Qed.

Lemma KV_byte : ltac2:(tb__ "0|2|
S80S87S93S0S6S2dS50Q40M0A1A1S2dS66A1S65S0S30S0S0S9bRcRbRaR9R8R7R6R5A8S7dS56S57R5R4R3A3VKV;A3S3cS41R6R3A2S43R3S44R6S46R5A1A2A2A2S3cS3bS2eS90Vsegs;SbRbA1S51G0R4A2A3S31A3S3dS50Q8A1M1G1S3bS33G1A1S8fVsegs;SbRcA1S51G0R5A2A3S35G1R1A2A3Lx;A2A2F_;F_;F_;Fz;Fv;Fk;Fa;Fmd;Ftr;Ftp;Frho;Fkc;FAi;Fnd;FKc;").
Proof using HKV HKVrng.
  intros Kc nd Ai kc rho tp tr md a k v z HJ Hin Hz.
  pose proof (KV_cell _ _ _ _ _ _ _ _ _ _ _ HJ Hin (Z.to_nat (z - a)) ltac:(lia)) as C.
  replace (a + Z.of_nat (Z.to_nat (z - a))) with z in C by lia.
  destruct (HKVrng _ Hin) as [R|R]; cbn [c_addr c_w] in R.
  - split; [apply wok_of_imageA; lia | apply rd_of_imageA; lia].
  - rewrite rd_of_high in C by lia. split; [| rewrite rd_of_high by lia; eexists; exact C].
    unfold wok_of. rewrite C. reflexivity.
Qed.

Theorem JA_carve : ltac2:(tb__ "0|0|
S80S87S5fS6S2dS50Q40A1A1Sa6S2dS67A1S1S83Vsegs;S9cR8R7A2R6R5R4R3A6S5eR7A1S12S23S28R1A1S29R1A1S26R1A1S25R1A1S2aR1A1S39S8SfR1A1S7aS67S8S69R4A4A3SeR1A1R3S27R1A1A9S12S3bS2eS2bR1A1S31A3S3bS2eSa9ScR3A1R5A2S31A3S3bS5S64RbA1SaS95A1A3S3bS2eS72SeR5A1SfR5A1S63RcA1VKV;VKP;S8eRdA1R8A7S31A3S83Vsegs;S9cRfReA2S62RdR5A2RcRbRaA6F_;F_;F_;F_;TS';TS;F_;Fnx;FN;Fw;Ftp;Frho;FA;Fnd;FKc;").
Proof using ALA HKV HKVrng HKP.
  intros Kc nd A rho tp w N nx HS S S' Hwf Hnx Hb Hok. apply Pos.leb_le in Hnx.
  pose proof HS as [(Hsm & _) (Ai & kc & HJ)].

  assert (TVB : tv_bandfree rho (nd_tv nd)).
  { intros t Ht Hz a Ha. pose proof HJ as (Hav & Hk & HM & HT & HB & HFF & (HN & HD & HZ) & _).
    destruct (proj1 (Forall_forall _ _) HN t Ht Hz) as (Hpos & Hlive & _).
    unfold TobjJV.tvv in Hpos, Hlive. cbn [fst snd] in Hpos, Hlive.
    pose proof (law_client_app _ _ _ ALA Ai rho tp (cfg_model (w_cfg w)) a HM) as X. pose proof (topG_range (aa_geom Ai)) as TG.
    assert (HC : client_addrA CST Ai a).
    { left. right. left. exists (uval rho (fst t)), (uval rho (snd t)). split; [exact Hlive | exact Ha]. }
    specialize (X HC). clear - X TG Ha.
    unfold IMG_HI, SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in *. lia. }
  assert (HF : Forall (holds rho) (ss_facts S)) by exact (smatch_facts_hold _ _ _ _ Hsm).
  assert (Hall : Forall (obj_holds segs rho (cfg_ms (snd (virt tp w)))) (ss_objs S)).
  { destruct Hsm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hall & _ & _) & _). exact Hall. }
  unfold carve_okb in Hok. apply andb_prop in Hok as [HokN Hdis].
  subst S'. rewrite <- map_lc.
  apply (SPA_carve_list segs (JAK Kc nd) rho A tp w (map lc_spec N) nx HS); [rewrite map_lc; exact Hwf | exact Hnx | | |].
  -
    apply Forall_forall. intros x Hx. apply in_map_iff in Hx as ([[lo hi] cs] & <- & Hin). cbn [lc_spec].
    pose proof (proj1 (forallb_forall _ _) HokN _ Hin) as Hc. unfold lc_okb in Hc.
    apply andb_prop in Hc as [Hc HX]. apply andb_prop in Hc as [Hc HO]. apply andb_prop in Hc as [Hc HKv].
    apply andb_prop in Hc as [Hc Hcov]. apply andb_prop in Hc as [Hc Hins]. apply andb_prop in Hc as [Hc H3]. apply andb_prop in Hc as [H1 H2].
    apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.ltb_lt in H3.
    cbn [eval]. rewrite lit_unsigned, (Z.mod_small 0) by lia. rewrite !Z.add_0_l.
    split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
    split; [apply cells_insideb_sound; exact Hins|]. split; [|split].
    + intros off Hoff. rewrite !Z.add_0_l. apply orb_prop in Hcov as [Hcov|Hpres].
      * destruct (all_coveredb_sound cs (Z.to_nat (hi - lo)) lo off Hcov ltac:(lia)) as (a & k & v & Hcin & Hrng).
        pose proof (proj1 (forallb_forall _ _) HKv (mkACell a k v) ltac:(unfold lc_acells; apply in_map_iff; exists (a, k, v); auto)) as HinKV.
        apply existsb_exists in HinKV as (c' & Hc'in & Heq). apply acell_eqb_sound in Heq. subst c'.
        exact (KV_byte _ _ _ _ _ _ _ _ _ _ _ off HJ Hc'in Hrng).
      * unfold presentb in Hpres. apply existsb_exists in Hpres as ([plo phi] & HinP & Hb2). cbn [fst snd] in Hb2.
        apply andb_prop in Hb2 as [Q1 Q2]. apply Z.leb_le in Q1. apply Z.leb_le in Q2.
        destruct (HKP _ _ _ _ _ _ _ _ plo phi off HJ HinP ltac:(lia)) as [R1 R2].
        destruct (rm rho (Z_to_bv 64 off)) as [b|] eqn:Eb; [|exfalso; exact (R2 eq_refl)].
        split; [unfold wok_of; rewrite Eb; reflexivity | rewrite rd_of_high by lia; rewrite Eb; eexists; reflexivity].
    + unfold cells_in_view, lc_cells. apply Forall_forall. intros x Hx. apply in_map_iff in Hx as ([[a k] v] & <- & Hcin).
      intros j Hj. cbn [eval]. rewrite Z.add_0_l.
      pose proof (proj1 (forallb_forall _ _) HKv (mkACell a k v) ltac:(unfold lc_acells; apply in_map_iff; exists (a, k, v); auto)) as HinKV.
      apply existsb_exists in HinKV as (c' & Hc'in & Heq). apply acell_eqb_sound in Heq. subst c'.
      exact (KV_cell _ _ _ _ _ _ _ _ _ _ _ HJ Hc'in j Hj).
    + unfold xwords_clear. intros rr y j Hrr Hy Hj. rewrite Hb. cbn [eval]. rewrite lit_unsigned, Z.mod_small by (unfold SHADOW_OFF; lia).
      apply (xr_clear_litb_sound rho (ss_facts S) lo hi rr SHADOW_OFF y j HF ltac:(lia) eq_refl); [| exact Hy | exact Hj].
      exact (proj1 (forallb_forall _ _) HX rr Hrr).
  -
    rewrite map_lc. apply Forall_forall. intros o Ho. apply in_map_iff in Ho as ([[lo hi] cs] & <- & Hin).
    pose proof (proj1 (forallb_forall _ _) HokN _ Hin) as Hc. unfold lc_okb in Hc.
    apply andb_prop in Hc as [Hc HX]. apply andb_prop in Hc as [Hc HO]. apply andb_prop in Hc as [Hc _].
    apply andb_prop in Hc as [Hc _]. apply andb_prop in Hc as [Hc _]. apply andb_prop in Hc as [Hc H3]. apply andb_prop in Hc as [H1 H2].
    apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.ltb_lt in H3.
    rewrite (lc_obj_range rho lo hi cs) by lia.
    apply Forall_forall. intros o' Ho'.
    apply (obj_clear_litb2_sound rho _ (ss_facts S) (nd_tv nd) lo hi o' (proj1 (Forall_forall _ _) Hall o' Ho') HF ltac:(lia) H3 TVB).
    exact (proj1 (forallb_forall _ _) HO o' Ho').
  -
    rewrite map_lc. clear -Hdis HokN. revert Hdis HokN. induction N as [|[[lo hi] cs] N IH]; intros Hdis HokN; [exact I|].
    cbn [map pairwise_disjoint]. cbn [lcs_disjb] in Hdis. apply andb_prop in Hdis as [Hd1 Hd2].
    cbn [forallb] in HokN. apply andb_prop in HokN as [Hc HokN].
    assert (B : 0 <= lo /\ lo <= hi /\ hi < 2 ^ 62).
    { unfold lc_okb in Hc. apply andb_prop in Hc as [Hc _]. apply andb_prop in Hc as [Hc _]. apply andb_prop in Hc as [Hc _].
      apply andb_prop in Hc as [Hc _]. apply andb_prop in Hc as [Hc _]. apply andb_prop in Hc as [Hc H3]. apply andb_prop in Hc as [H1 H2].
      apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.ltb_lt in H3. lia. }
    split; [| apply IH; assumption].
    apply Forall_forall. intros o Ho. apply in_map_iff in Ho as ([[lo' hi'] cs'] & <- & Hin).
    pose proof (proj1 (forallb_forall _ _) Hd1 _ Hin) as Hd. cbn in Hd.
    pose proof (proj1 (forallb_forall _ _) HokN _ Hin) as Hc'.
    assert (B' : 0 <= lo' /\ lo' <= hi' /\ hi' < 2 ^ 62).
    { unfold lc_okb in Hc'. apply andb_prop in Hc' as [Hc' _]. apply andb_prop in Hc' as [Hc' _]. apply andb_prop in Hc' as [Hc' _].
      apply andb_prop in Hc' as [Hc' _]. apply andb_prop in Hc' as [Hc' _]. apply andb_prop in Hc' as [Hc' H3]. apply andb_prop in Hc' as [H1 H2].
      apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.ltb_lt in H3. lia. }
    rewrite !lc_obj_range by lia. unfold ranges_disjoint. cbn [fst snd].
    apply orb_prop in Hd as [Hd|Hd]; apply Z.leb_le in Hd; lia.
Qed.

Definition lc_unokb (c : lcarve) : bool := ltac2:(tb__ "0|2|
S2cS2cS0S0A2M0S2dS68A1M1A2S2eLc;Vc;G0G1G0S2eLp;R2S0S0S2fS2fS2fS2fS2fS42Z0R2A2S42R2R1A2A2S47R1S45Z2Z3eA2A2A2S6cR2R1R3A3A2S6bR3R2S4cS48R1R2A2A1A3A2S7eS56S56S7fS56S6aR1A1VKV;A3Lc;S6eR3A1A3A2Lhi;Llo;X2cx1Lcs;Lp;X2cx1").
Definition uncarve_okb (N : list lcarve) : bool := forallb lc_unokb N.

Hypothesis HCSTKV : ltac2:(tb__ "0|0|
S0S30S0S0S7dS56S57R4R3R2A3VKV;A3S41S44R5S46R4A1A2Z643000A2S3cS41R6R3A2S43R3S44R6S46R5A1A2A2A2S3eS5cVCST;R4A2A1F_;F_;F_;Fz;Fv;Fk;Fa;").

Lemma in_ranges_lc : ltac2:(tb__ "0|4|
S6S2dS67A1S50Q40M0A1S3bS2eS9dR2A1S31A3S40Sa1R4S7aS67S8S69R3A4R2A3S3dS0S0S3dS0S0S3dS2dS68A1M1G1S3cS7dS2cS2cS0S0A2M2G1A2S32G2G1S32S0S0R3R2A4R1A4R6A3S3cS41R3S52G0R5A2M3A2S43G3R2A2A2A2Lcs;A2Lhi;A2Llo;A2A2F_;Fa;FN;Frho;").
Proof.
  intros rho N a Hok. unfold in_ranges. split.
  - intros (o & Ho & Hr). apply in_map_iff in Ho as ([[lo hi] cs] & <- & Hin).
    pose proof (proj1 (forallb_forall _ _) Hok _ Hin) as Hc. unfold lc_unokb in Hc.
    apply andb_prop in Hc as [Hc _]. apply andb_prop in Hc as [Hc _]. apply andb_prop in Hc as [Hc _]. apply andb_prop in Hc as [Hc H3]. apply andb_prop in Hc as [H1 H2].
    apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.ltb_lt in H3.
    rewrite lc_obj_range in Hr by lia. cbn [fst snd] in Hr. exists lo, hi, cs. auto.
  - intros (lo & hi & cs & Hin & Hr). exists (lc_obj (lo, hi, cs)). split; [apply in_map_iff; exists (lo, hi, cs); auto|].
    pose proof (proj1 (forallb_forall _ _) Hok _ Hin) as Hc. unfold lc_unokb in Hc.
    apply andb_prop in Hc as [Hc _]. apply andb_prop in Hc as [Hc _]. apply andb_prop in Hc as [Hc _]. apply andb_prop in Hc as [Hc H3]. apply andb_prop in Hc as [H1 H2].
    apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.ltb_lt in H3.
    rewrite lc_obj_range by lia. cbn [fst snd]. exact Hr.
Qed.

Lemma absorb_lc_view : ltac2:(tb__ "0|8|
S80S87S93S0S6S2dS50Q40M0A1M1A1S2dS66A1M2S94S65G2S65S12S2dS8A1M3S2dS67A1S24Vsegs;RaR3S32G2S99R8S9aR7R6A2A4A4S3bG3SfR4A1S39S8R3S7aS67S8S69R2A4A3A3S3bS2eS9dR3A1S31A3S9bR11R10RfReRdRcR8R7A8S9eReS7aS67S8S69R5A4RbA3S6S3cG1S3bS33S50Q8A1A1M4S8fVsegs;SbR2A1R1A3S8fVsegs;SbR10A1R1A3A3Fa;S3cG1S41Z643000M5S52G0R1A2A2S3bG4SbR3R2A2SbR11R2A2A3F_;Fa;G1S3eS3bG4SbR2R1A2SbR10R1A2A3A1S3dS30S30S3dS0S0S3dS0S0S3cS7dS56S57R1R3R2A3VKV;A3S3cS3cS41R1S52G0R5A2M6A2S43G6S44R1S46R3A1A2M7A2A2S41G7G5A2A2A2Lc;A2Lv;A2Lk;A2F_;Fa;A2A2Trho';F_;F_;F_;F_;FN;Fobjs;FS;Fmd';Ftr';Fmd;Fms;Ftr;Ftp;Frho;Fkc;FAi;Fnd;FKc;").
Proof using HKV HKVrng.
  intros Kc nd Ai kc rho tp tr ms md tr' md' S objs N Hsm Hobjs Hok HJ rho'.
  pose proof Hsm as (_ & _ & _ & _ & Hrom & _).  cbn [fst snd cfg_ms cfg_model] in Hrom.
  assert (RD : forall a, in_ranges rho (map lc_obj N) a -> rd_of segs (rm rho') a = rd_of segs (rm rho) a
                        /\ (0x643000 <= bv_unsigned a -> rm rho' a = rm rho a)
                        /\ exists k v c, In (mkACell c k v) KV /\ c <= bv_unsigned a < c + Z.of_nat k /\ (0x643000 <= bv_unsigned a \/ c + Z.of_nat k <= 0x643000)).
  { intros a Hin. destruct (proj1 (in_ranges_lc rho N a Hok) Hin) as (lo & hi & cs & HinN & Hr).
    pose proof (proj1 (forallb_forall _ _) Hok _ HinN) as Hc. unfold lc_unokb in Hc.
    apply andb_prop in Hc as [Hc HKv]. apply andb_prop in Hc as [Hc Hcov]. apply andb_prop in Hc as [Hc Hins]. apply andb_prop in Hc as [Hc H3]. apply andb_prop in Hc as [H1 H2].
    apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.ltb_lt in H3.
    destruct (all_coveredb_sound cs (Z.to_nat (hi - lo)) lo (bv_unsigned a) Hcov ltac:(lia)) as (c & k & v & Hcin & Hrng).
    pose proof (proj1 (forallb_forall _ _) HKv (mkACell c k v) ltac:(unfold lc_acells; apply in_map_iff; exists (c, k, v); auto)) as HinKV.
    apply existsb_exists in HinKV as (c' & Hc'in & Heq). apply acell_eqb_sound in Heq. subst c'.

    destruct (absorb_carved_cells segs rho S tr ms md objs (map lc_obj N) (SLit 0) lo hi (lc_cells cs) Hsm Hobjs
                ltac:(apply in_map_iff; exists (lo, hi, cs); auto) ltac:(lia) ltac:(lia) ltac:(lia) (cells_insideb_sound _ _ _ Hins)) as [CV _].
    cbn zeta in CV. fold rho' in CV. cbn [eval] in CV. rewrite lit_unsigned, (Z.mod_small 0) in CV by lia.
    unfold cells_in_view, lc_cells in CV.
    pose proof (proj1 (Forall_forall _ _) CV (c, k, SLit v) ltac:(apply in_map_iff; exists (c, k, v); auto)) as CVc. cbn beta iota in CVc.
    specialize (CVc (Z.to_nat (bv_unsigned a - c)) ltac:(lia)). cbn [eval] in CVc.
    replace (0 + c + Z.of_nat (Z.to_nat (bv_unsigned a - c))) with (bv_unsigned a) in CVc by lia. rewrite Z_to_bv_bv_unsigned in CVc.

    pose proof (KV_cell _ _ _ _ _ _ _ _ _ _ _ HJ Hc'in (Z.to_nat (bv_unsigned a - c)) ltac:(lia)) as OV.
    replace (c + Z.of_nat (Z.to_nat (bv_unsigned a - c))) with (bv_unsigned a) in OV by lia. rewrite Z_to_bv_bv_unsigned in OV.
    assert (E1 : rd_of segs (rm rho') a = rd_of segs (rm rho) a) by (rewrite CVc, OV; reflexivity).
    split; [exact E1|]. split.
    - intros Hhi. pose proof (urange a). pose proof E1 as E2. rewrite <- (Z_to_bv_bv_unsigned 64 a) in E2.
      rewrite (rd_of_high (rm rho') (bv_unsigned a)) in E2 by lia. rewrite (rd_of_high (rm rho) (bv_unsigned a)) in E2 by lia.
      rewrite Z_to_bv_bv_unsigned in E2. exact E2.
    - exists k, v, c. split; [exact Hc'in|]. split; [exact Hrng|].
      destruct (HKVrng _ Hc'in) as [R|R]; cbn [c_addr c_w] in R; lia. }
  assert (OUT : forall a, ~ in_ranges rho (map lc_obj N) a -> rm rho' a = rm rho a).
  { intros a Hn. unfold rho'. apply rm_absorb_out. exact Hn. }
  split; [|split].
  - intros a. destruct (in_ranges_dec rho (map lc_obj N) a) as [Hin|Hn]; [exact (proj1 (RD a Hin))|].
    pose proof (OUT a Hn) as E. unfold rd_of. rewrite E. destruct (rm rho a); reflexivity.
  - intros a Ha. destruct (in_ranges_dec rho (map lc_obj N) a) as [Hin|Hn]; [exact (proj1 (proj2 (RD a Hin)) Ha) | exact (OUT a Hn)].
  - intros a Hne. destruct (in_ranges_dec rho (map lc_obj N) a) as [Hin|Hn]; [|exfalso; exact (Hne (OUT a Hn))].
    destruct (RD a Hin) as (_ & HI & k & v & c & HcK & Hr & Hcase).
    destruct Hcase as [Hhi|Hhi]; [exfalso; exact (Hne (HI Hhi))|].
    exists k, v, c. auto.
Qed.

Lemma Sh_ge : ltac2:(tb__ "0|0|
S0S41Z0R1A2S41S95S98R2A1A2F_;Fx;").
Proof. intros x Hx. unfold Sh. pose proof (Z.div_pos x 8). lia. Qed.

Theorem JA_uncarve : ltac2:(tb__ "0|2|
S80S87S5fS6S2dS50Q40A1A1S2dS66A1M0S94S65S2dS8A1M1S2dS67A1S81RaA1S3bG1SfS5eR9A1A1S39S8R3S7aS67S8S69R2A4A3A3S3bS2eS9dR3A1S31A3S3bS8cS8dRcA1S8aA3S3bS2eS88ScS5eRcA1A1RdA2S31A3S83Vsegs;S9cRfReA2RdRcRbS32G0S99RaS9aR9R8A2A4A6S83Vsegs;S9cR10RfA2S62ReS4fS5eReA1R8A2A2S9eRdS7aS67S8S69R7A4Sa8R9RcRaA3A3RcS32G0S99RbS9aRaR9A2A4A6F_;F_;F_;F_;F_;F_;FN;Fobjs;Fmd;Fms;Ftr;Ftp;Frho;FA;Fnd;FKc;").
Proof using ALA HLV HKV HKVrng HCSTKV.
  intros Kc nd A rho tp tr ms md objs N HKc Hobjs Hok Ham Hnb HS.
  apply (SPA_unobj segs (JAK Kc nd) rho A objs (map lc_obj N) tp tr ms md Hobjs HS).
  intros (Ai & kc & HJ). exists Ai, kc.
  pose proof (proj1 (proj1 HS)) as Hsm. unfold virt in Hsm. cbn [w_tr w_cfg cfg_ms cfg_model fst snd] in Hsm.
  destruct (absorb_lc_view Kc nd Ai kc rho tp tr (vms md tp ms) (vmd md) tr md (ax_S A) objs N Hsm Hobjs Hok HJ) as (HV & HHI & HCH).
  set (rho' := rho_absorb rho (map lc_obj N) (vms md tp ms)) in *.
  destruct (nd_below_split _ _ Hnb) as (Hbt & Hbf & Hbb & Hba).
  pose proof HJ as (Hav & Hk & HM & HT & HB & HFF & (HN & HD & HZ) & HFR & HK0 & HP0 & HXA & HBU & HPA).
  assert (AG : agree_vals (ss_next (ax_S A)) rho rho') by (split; intros; reflexivity).
  split; [split; [intros i Hi; rewrite (proj1 Hav i Hi); reflexivity | intros l; rewrite (proj2 Hav l); reflexivity]|].
  split; [exact Hk|].
  split; [exact (HLV Ai rho rho' tp md HM HV)|].
  split; [exact HT|]. split; [exact HB|]. split; [exact HFF|].
  split; [split; [eapply tvinA_agree; eauto | split; [eapply TobjJV.tvd_agree; eauto | eapply TobjJV.tvz_agree; eauto]]|].
  split; [eapply frinA_agree; eauto|].
  split.
  {
    destruct (law_blocks _ _ _ ALA Ai rho tp md HM) as (_ & HBl & HFl).

    pose proof (TPA_top _ Ai HT) as HTOPG. pose proof (topG_range (aa_geom Ai)) as TGR.
    assert (NOPCL : forall a, 0 <= a < 2 ^ 64 -> rm rho' (Z_to_bv 64 a) <> rm rho (Z_to_bv 64 a) ->
                    ~ (pclFA CST rho0 FB FF a \/ pclSA CST XGL rho0 FB FF a)).
    { intros a Ha Hne Hp. destruct (HCH _ Hne) as (k & v & c & HcK & Hr & Hck). rewrite u64_lit in Hr by lia.
      destruct Hp as [Hp|Hp].
      - destruct Hp as [Hs|[Hc|[(b & n & Hin & Hbn)|(f & sz & fl & Hin & Hf)]]].
        + rewrite <- HTOPG in Hs. lia.
        + exact (HCSTKV c k v a HcK Hck Hr (proj1 Hc)).
        + destruct (HBl b n (HB _ Hin)) as (_ & _ & _ & _ & G5). unfold IMG_HI in G5. lia.
        + destruct (HFF f sz fl Hin) as [Hfr Hfl].
          destruct (HFl f sz Hfr) as (_ & _ & _ & G4 & _ & G6 & _). rewrite <- Hfl in G6. unfold IMG_HI in G4, G6. lia.
      - destruct Hp as (x & Hx & _ & ->). pose proof (Sh_ge x Hx). unfold SHADOW_OFF in *. lia. }
    destruct HK0 as [K1 K2]. split.
    - intros a Ha Hp. destruct (decide (rm rho' (Z_to_bv 64 a) = rm rho (Z_to_bv 64 a))) as [E|NE]; [rewrite E; apply K1; assumption|].
      exfalso. apply (NOPCL a Ha NE). destruct Hp as [Hp|[Hp _]]; [left | right]; exact Hp.
    - intros a j Ha Hp Hj Hm0. pose proof (K2 a j Ha Hp Hj Hm0) as X.
      destruct Hp as (x & Hx & _ & ->). pose proof (Sh_ge x Hx).
      unfold word_byte in *. rewrite HHI; [exact X|]. rewrite u64_lit; unfold SHADOW_OFF in *; [lia|].
      pose proof (Z.div_mod (Sh x) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (Sh x) 8 ltac:(lia)). lia. }
  split; [exact HP0|].
  rewrite Ham in HXA, HBU |- *. split; [unfold XA in HXA |- *; cbn [am_eval] in HXA |- *; rewrite (tvals_agree _ rho rho' _ AG Hbt); exact HXA|].
  assert (HCNT : cntS rho (nd_tv nd) <= cntS rho' (nd_tv nd)) by (rewrite (cntS_agree _ rho rho' _ AG Hbt); lia).
  split; [|exact (JA_tail_le _ _ _ rho rho' _ _ HCNT HPA)].
  cbn [apot am_eval apotz] in HBU |- *. eapply BUD_agree; [exact AG | exact Hbb | exact HBU].
Qed.
End JAcarve.

Section PureCall.
Variable AInv : ltac2:(tb__ "0|0|
S93S6S2dS50Q40A1A1S65OF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : ltac2:(tb__ "0|0|
S82Vsegs;VAInv;VCST;A3").
Variable NP : positive.
Variable rho0 : valuation.
Variable P0f : valuation -> Prop.
Variable FB : list (Z * Z).
Variable FF : ltac2:(tb__ "0|0|
S2dS2cS2cS0S0A2S0A2A1").
Variable BX : bxt.
Variable PA : AA -> Prop.
Let JAK (Kc : KcA) (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
S89VAInv;VCST;VXGL;VNP;VKc;Vrho0;VP0f;VFB;VFF;VBX;VPA;Vnd;Ac").

Theorem pure_callJ : ltac2:(tb__ "0|4|
Sa6OF_;S80S80S5fS5fSa0S2dS8A1M0S2dS60A1S6S2dS50Q40A1A1M1S87S84S84Sa7S81RcA1S6G1Sa5Vsegs;R11S83Vsegs;R6RdR2R1A5S85Vsegs;R5ScS5eRdA1A1R2R1RaA6A4Ftp1;Frho1;S3bS33G0A1SadRdRcRbA3S35G0RaA2A3S3bS2eSacReRdRcRbS7aS60S5fS61RaA4A5S31A3S3bS2eSa9VNP;ScS5eRfA1A1A2S31A3S3bS2eS88ScS5eR10A1A1R9A2S31A3S3bS2eS7eSdS1aScS5eR11A1M2A1A1SeG2A1A3S31A3S2dS66A1M3S94S65S86Vsegs;R10RfR15S32G3S99R3S9aR2R1A2A4A5VJAK;R18RfR11R10R4R2A6RfS9fS9eR12R14Sa8R3R11R4A3A3R15A2R11R5R3A4F_;F_;Fmd;Fms;Ftr;S6G3S65RdR3R10R2R1A4VJAK;R18R10R12R11R3R2A6F_;Fmd';Ftr';FrhoL;S60S6S7dS60R2R12A3S13ScS5eR17A1A1R12R2A3Sa5Vsegs;R1bS83Vsegs;VJAK;R19R11A2SabSeS5eR18A1A1SaeR16R17S61R4A1R18R15A5A2R3R12A5ReA4F_;F_;Frho';FL;Sa5Vsegs;R18S83Vsegs;VJAK;R17ReA2R15R10RfA5RbA4F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;FJp';FJp;Fnd;Ftp;Frho;FPosts;FR;Fs;FPre;FCl;FKc';FKc;Fok;").
Proof using ALA.
  intros ok Kc Kc' Cl Pre s R Posts rho tp nd Jp Jp' Q HKc' Hsum He Hchk Hnf Hnb Hfb HIN HOUT Hcont. apply Pos.leb_le in Hnf.
  apply triple_factsA. intros HF.
  intros n HgQ w [Hsm Hk]. destruct w as [tr [ms md]].
  destruct (entails_frA_sound segs Cl Pre s R rho tp tr ms md He Hsm) as (HsmPre & _).
  apply (Hsum (rho_sub (rho_absorb rho R (vms md tp ms)) s) tp n); [|split; [exact HsmPre|exact (HIN tr ms md Hsm Hk)]].
  intros w' (L & rhoL & HinL & HagL & HsmL & Hk'). destruct w' as [tr' [ms' md']].
  cbn [w_tr w_cfg fst snd cfg_model] in Hk'.
  destruct (import_post_linkA segs Cl Pre s R (map la_state Posts) rho tp tr ms md tr' ms' md' (la_state L) rhoL tp He Hchk Hsm
              ltac:(apply in_map_iff; exists L; auto) HagL HsmL) as (rho' & HLK & HSP).
  pose proof (proj1 HLK) as HAG.
  apply (Hcont L rho' HinL HAG n HgQ). split.
  - apply smatchA_add_facts; [exact HSP | |].
    + apply Forall_forall. intros q Hq.
      apply (holds_agree_vals (ss_next (ax_S Cl)) rho rho' q (agree_below_vals _ _ _ HAG)).
      * exact (proj1 (forallb_forall _ _) Hfb q Hq).
      * exact (proj1 (Forall_forall _ _) HF q Hq).
    + apply forallb_forall. intros q Hq.
      eapply sprop_below_mono; [| exact (proj1 (forallb_forall _ _) Hfb q Hq)].
      unfold import_postA, import_post. cbn [ax_S ss_next set_objs subst_state]. unfold import_next, pos_add_nat. lia.
  - destruct (HOUT rhoL tr' md' Hk') as (Ai & kc & HJ'). exists Ai, kc.
    eapply (JAi_stable segs AInv CST XGL NP Kc' rho0 P0f FB FF BX PA HKc' ALA (ss_next (ax_S Cl)) nd Ai kc rho rho' tp tr' md' md' Hnf Hnb HAG (mat_equiv_refl _ _ _) HJ').
Qed.

Theorem pure_callJ_ex : ltac2:(tb__ "0|4|
S80S80S5fS5fSa0S2dS8A1M0S2dS60A1S6S2dS50Q40A1A1M1S87S84S84Sa6OF_;S81RcA1S6G1Sa4Vsegs;S83Vsegs;R6RdR2R1A5S85Vsegs;R5ScS5eRdA1A1R2R1RaA6A3Ftp1;Frho1;S3bS33G0A1SadRdRcRbA3S35G0RaA2A3S3bS2eSacReRdRcRbS7aS60S5fS61RaA4A5S31A3S3bS2eSa9VNP;ScS5eRfA1A1A2S31A3S3bS2eS88ScS5eR10A1A1R9A2S31A3S3bS2eS7eSdS1aScS5eR11A1M2A1A1SeG2A1A3S31A3S2dS66A1M3S94S65S86Vsegs;R10RfR15S32G3S99R3S9aR2R1A2A4A5VJAK;R18RfR11R10R4R2A6RfS9fS9eR12R14Sa8R3R11R4A3A3R15A2R11R5R3A4F_;F_;Fmd;Fms;Ftr;S6G3S65RdR3R10R2R1A4VJAK;R18R10R12R11R3R2A6F_;Fmd';Ftr';FrhoL;S60S6S7dS60R2R12A3S13ScS5eR17A1A1R12R2A3Sa4Vsegs;S83Vsegs;VJAK;R19R11A2SabSeS5eR18A1A1SaeR16R17S61R4A1R18R15A5A2R3R12A5ReA3F_;F_;Frho';FL;Sa4Vsegs;S83Vsegs;VJAK;R17ReA2R15R10RfA5RbA3F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;FJp';FJp;Fnd;Ftp;Frho;FPosts;FR;Fs;FPre;FCl;FKc';FKc;").
Proof using ALA.
  intros Kc Kc' Cl Pre s R Posts rho tp nd Jp Jp' Q HKc' Hsum He Hchk Hnf Hnb Hfb HIN HOUT Hcont. apply Pos.leb_le in Hnf.
  apply etriple_factsA. intros HF.
  intros w [Hsm Hk]. destruct w as [tr [ms md]].
  destruct (entails_frA_sound segs Cl Pre s R rho tp tr ms md He Hsm) as (HsmPre & _).
  destruct (Hsum (rho_sub (rho_absorb rho R (vms md tp ms)) s) tp _ (conj HsmPre (HIN tr ms md Hsm Hk))) as (w' & Hsteps & HLQ).
  destruct HLQ as (L & rhoL & HinL & HagL & HsmL & Hk'). destruct w' as [tr' [ms' md']].
  cbn [w_tr w_cfg fst snd cfg_model] in Hk'.
  destruct (import_post_linkA segs Cl Pre s R (map la_state Posts) rho tp tr ms md tr' ms' md' (la_state L) rhoL tp He Hchk Hsm
              ltac:(apply in_map_iff; exists L; auto) HagL HsmL) as (rho' & HLK & HSP).
  pose proof (proj1 HLK) as HAG.
  destruct (Hcont L rho' HinL HAG (tr', mkCfg ms' md')) as (w'' & Hsteps' & HQ).
  { split.
    - apply smatchA_add_facts; [exact HSP | |].
      + apply Forall_forall. intros q Hq.
        apply (holds_agree_vals (ss_next (ax_S Cl)) rho rho' q (agree_below_vals _ _ _ HAG)).
        * exact (proj1 (forallb_forall _ _) Hfb q Hq).
        * exact (proj1 (Forall_forall _ _) HF q Hq).
      + apply forallb_forall. intros q Hq.
        eapply sprop_below_mono; [| exact (proj1 (forallb_forall _ _) Hfb q Hq)].
        unfold import_postA, import_post. cbn [ax_S ss_next set_objs subst_state]. unfold import_next, pos_add_nat. lia.
    - destruct (HOUT rhoL tr' md' Hk') as (Ai & kc & HJ'). exists Ai, kc.
      eapply (JAi_stable segs AInv CST XGL NP Kc' rho0 P0f FB FF BX PA HKc' ALA (ss_next (ax_S Cl)) nd Ai kc rho rho' tp tr' md' md' Hnf Hnb HAG (mat_equiv_refl _ _ _) HJ'). }
  exists w''. split; [eapply wsteps_trans; eauto | exact HQ].
Qed.
End PureCall.

End WithSegs.
