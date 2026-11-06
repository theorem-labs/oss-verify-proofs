(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e8.

(* [comment removed for export] *)
Module Start4FailCut.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "cell"; "SAlu"; "SLit"; "sobj"; "c_off"; "mkObj"; "ob_base"; "ob_cells"; "ob_hi"; "ob_lo"; "sprop"; "ob_dflt"; "SPUle"; "SVar"; "DUnknown"; "c_width"; "mkCell"; "mkSS"; "ss_facts"; "ss_fcsr"; "ss_fregs"; "ss_objs"; "ss_regs"; "ss_resv"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "N"; "@Corelib.Init.Datatypes"; "cons"; "list"; "bool"; "false"; "option"; "nat"; "nil"; "pair"; "true"; "andb"; "app"; "negb"; "prod"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e5.Start4FailCut"; "C2"; "vP"; "RUN2"; "FUEL2"; "drop_cells"; "e_cur"; "v1"; "zsn"; "C2_facts"; "C2_objs"; "drop_sym_cells"; "e_nbp"; "lit_in"; "set_cell_val"; "set_dflt"; "upd_obj0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "leafA"; "axst"; "ax_S"; "la_state"; "sym_runA"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "aluop"; "mulop"; "ALU_SLL"; "ALU_SUB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Start4FailStates"; "PC_OUT"; "L1a"; "PC_SPIN"; "F0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts"; "segsA"; "@Stdlib.Lists.List"; "filter"; "@Stdlib.ZArith.BinInt.Z"; "leb"; "pow"; "eqb"; "ltb"; "modulo"; "sub"; "@Corelib.Init.Logic"; "eq"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.StartALib"; "axA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "setregs"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymCFG SymHeap.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA CFGA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Start4States.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.StartALib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Start4States.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Start4FailStates.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition zsn (z : Z) : Z := ltac2:(tb__ "0|3|
S1eS19L_;S49S4aZ2M0Z3fA2S4dVz;S4aG0Z40A2M1A2M2A2S4eG2G1A2G2X1ex2").
Definition lit_in (lo hi : Z) (e : sv) : bool := ltac2:(tb__ "0|4|
S0S1eLe;Ve;S19S25S49Vlo;S30R1A1M0A2S4cG0Vhi;A2A2Lz;S1aS1fLi;S3fS0S0S1fLb;La;M1Lop;M2G2S40G1Lop;M3G3S1eS1bS0S1fLa;Lw;Lsgn;S1aS0S19S1fLk;Li;Ll;X0x8").
Definition drop_cells (lo hi : Z) (o : sobj) : sobj := ltac2:(tb__ "0|0|
S6S7Vo;A1SaVo;A1S9Vo;A1S48S1S1S27S35Vlo;Vhi;S5R1A1A3A1Lc;S8Vo;A1A3ScVo;A1A5").
Definition drop_sym_cells (o : sobj) : sobj := ltac2:(tb__ "0|3|
S6S7Vo;A1SaVo;A1S9Vo;A1S48S1S1S0S1eLx;S5R1A1S19S24Lz;S1aS1fLi;S3fS0S0S1fLb;La;M0Lop;M1G1S40G0Lop;M2G2S1eS1bS0S1fLa;Lw;Lsgn;S1aS0S19S1fLk;Li;Ll;X0x8Lc;S8Vo;A1A3ScVo;A1A5").
Definition set_cell_val (off : Z) (v : sv) (o : sobj) : sobj := ltac2:(tb__ "0|3|
S6S7Vo;A1SaVo;A1S9Vo;A1S50S1S1S1S0S1Lx;S5R1A1S19S1eS1L_;S4bS30R1A1Voff;A2S11S5R2A1S10R2A1Vv;A3R2X1ex2Lz;S1aR2Li;S3fS0S0R4Lb;La;M0Lop;M1G1S40G0Lop;M2G2S1eS1bS0R4La;Lw;Lsgn;S1aS0S19R4Lk;Li;Ll;X0x8Lc;S8Vo;A1A4ScVo;A1A5").
Definition set_dflt (d : odefault) (o : sobj) : sobj := ltac2:(tb__ "0|0|
S6S7Vo;A1SaVo;A1S9Vo;A1S8Vo;A1Vd;A5").
Definition upd_obj0 (f : sobj -> sobj) (objs : list sobj) : list sobj := ltac2:(tb__ "0|1|
S1dS4A1M0G0Lobjs;Vobjs;S22S4A1S4G0S1cS4Vf;R2A1R1A3Lrest;Lo;X1dx2").

Definition vP := SVar 31.
Definition v1 := SVar 1.
Definition e_cur : sv := ltac2:(tb__ "0|0|
S2S3eS2S42S2fS2aA3S3N180A1A3").
Definition e_nbp : sv := ltac2:(tb__ "0|0|
S2S3eS2S3eS2fS2S41S2aS3Z3A1A3A3S3N3b0A1A3").
Definition C2_facts : list sprop := ltac2:(tb__ "0|0|
S26SbS1cSbSdS3Z1A1S2aA2S1cSbSdS2aS3ZcA1A2S22SbA1A3A3S13S3bS46A1A1A3").
Definition C2_objs : list sobj := ltac2:(tb__ "0|0|
S38S4S37SfS36N250S2eS2dN18cN178S2dN3a8N2b8S33R1A1A3A3A3A2Lo;S16S3bS44A1A1A2").
Definition C2 : axst := ltac2:(tb__ "0|2|
S51S12S43S52S17S3bS44A1M0A1S1cS28S21S0A2M1S23S21S0UbS2aA4S1cG1S23S21S0UdS2eA4S1cG1S23S21S0UeS34A4S1cG1S23S21S0U10SeP20A1A4S1cG1S23S21S0U11SeP21A1A4S22G1A1A3A3A3A3A3A2S15G0A1S14G0A1S18G0A1S32S31P22S1fA9A1").

Definition FUEL2 : nat := 400%nat.
Definition RUN2_eq__R : option (list leafA) := ltac2:(tb__ "0|0|
S3dS47S2cS1cS19S43S1cS19S45S22S19A1A3A3S29S24A5").
Local Strategy expand [RUN2_eq__R].
Definition RUN2 : option (list leafA) := Eval vm_compute in ((fun ro1__ : option (list leafA) => ro1__) RUN2_eq__R).
Lemma RUN2_eq : ltac2:(tb__ "0|0|
S4fS20S1dS39A1A1S3dS47S2cS1cS19S43S1cS19S45S22S19A1A3A3S29S24A5S2bA3").
Proof. exact (@eq_refl (option (list leafA)) RUN2_eq__R <: RUN2_eq__R = RUN2). Qed.

Definition E_spin : axst := ltac2:(tb__ "0|1|
S20S1dS39A1M0A1S3aLx;S2bG0G0S3aLl0;R1S29S39G0S3cR2A1Ll1;Ll;X1dx2Ll0;S29X20x2").
Definition L2b : axst := ltac2:(tb__ "0|1|
S20S1dS39A1M0A1S3aLx;S2bG0G0S3aLl0;R1S29S39G0G0S3aLl2;R1S29S39G0S3cR2A1Ll3;Ll;X1dx2Ll2;Ll1;X1dx2Ll0;S29X20x2").
Definition L2c : axst := ltac2:(tb__ "0|1|
S20S1dS39A1M0A1S3aLx;S2bG0G0S3aLl0;R1S29S39G0G0S3aLl2;R1S29S39G0G0S3aLl4;R1S29S39G0S3cR2A1Ll5;Ll;X1dx2Ll4;Ll3;X1dx2Ll2;Ll1;X1dx2Ll0;S29X20x2").
End Start4FailCut.

(* [comment removed for export] *)
Module Lib_handle_f_fastcert.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "bool"; "list"; "false"; "prod"; "option"; "andb"; "true"; "app"; "nat"; "cons"; "nil"; "orb"; "pair"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "bitem"; "lform"; "batom"; "bd_wpos"; "item_nn"; "lf_nonneg"; "wformK"; "wformV"; "ASv"; "bd_subst"; "bud_le"; "bud_le_pos"; "bud_pay"; "item_le"; "item_nonneg"; "lf_neg"; "@Corelib.Init.Logic"; "eq"; "True"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "edescA"; "ndesc"; "eda_rank"; "eda_var"; "nd_am"; "nd_bd"; "nd_fr"; "nd_tv"; "am_eqb"; "am_subst"; "echeckJA"; "eda_state"; "edropA"; "eecheckJA"; "fr_sub_eqb"; "nd_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "ss_facts"; "ss_next"; "SLit"; "SPUlt"; "sv"; "sv_below"; "@Stdlib.Lists.List"; "In"; "nth_error"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "edgeA"; "ea_leaf"; "ea_src"; "ea_sub"; "ea_tgt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e5.Lib_handle_f_fastcert"; "bud_le'"; "bud_le_pos'"; "bud_pay'"; "echeckJA'"; "items_nn'"; "eecheckJA'"; "item_nn'"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.JcertCutA"; "cut_okE"; "@Stdlib.ZArith.BinInt.Z"; "leb"; "sub"; "eqb"; "ltb"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "existsb_lazy"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "sv_subst"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "prove_sprop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "tv_sub_eqb"; "@Stdlib.PArith.BinPos.Pos"; "leb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymCFG SymSummary.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA EntailA CFGA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import TobjJV.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA TobjJA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h0.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.JcertCutA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Open Scope Z_scope.

Definition item_nn' (facts : list sprop) (bfrom : list bitem) (hint : option bitem) (i : bitem) : bool := ltac2:(tb__ "0|2|
S0S0L_;M0S4SdA1S0Lhint;Vhint;SdS1aVfacts;R1Vi;A3Lj;M1S2X4x2S6G0S1bVfacts;Vi;A2S6S4fSdG1Vbfrom;A3X0x2X0x2").

Lemma item_nn'_eq : ltac2:(tb__ "0|1|
S1S33A1S1SdA1S4SdA1M0SdG0OLhint;R2SdS3aSdR1R4A3Lj;S1eX4x2S1dS0S48R5R4R3R2A4S11R5R4R2A3A3F_;Fi;Fhint;Fbfrom;Ffacts;").
Proof.
  intros facts bfrom hint i Hh. unfold item_nn', item_nn.
  assert (X : existsb_lazy (fun j => item_le facts j i) bfrom = existsb (fun j => item_le facts j i) bfrom) by apply existsb_lazy_eq.
  destruct hint as [j|].
  - destruct (item_le facts j i) eqn:E.
    + cbn. symmetry. apply orb_true_intro. right. apply existsb_exists. exists j. auto.
    + cbn. rewrite <- X. destruct (item_nonneg facts i); reflexivity.
  - cbn. rewrite <- X. destruct (item_nonneg facts i); reflexivity.
Qed.

Fixpoint bud_le_pos' (facts : list sprop) (ball bto bfrom : list bitem) : bool :=
  match bto, bfrom with
  | [], _ => bd_wpos bfrom
  | i :: r, j :: r' =>
      ((0 <=? bi_v i) && (bi_v i <=? bi_v j) && (0 <=? bi_k i) && (bi_k i <=? bi_k j))
      &&& (item_nn' facts ball (Some j) i &&& (item_le facts i j &&& bud_le_pos' facts ball r r'))
  | _ :: _, [] => false
  end.

Lemma lazy_andb_eq : ltac2:(tb__ "0|0|
S0S0S1dS0S0S0L_;R2R1S2X0x2S5R2R1A2A3Fb;Fa;"). Proof. intros [|] b; reflexivity. Qed.
Lemma lazy_orb_eq : ltac2:(tb__ "0|0|
S0S0S1dS0S0S0L_;R2S6R1X0x2SbR2R1A2A3Fb;Fa;"). Proof. intros [|] b; reflexivity. Qed.

Lemma bud_le_pos'_eq : ltac2:(tb__ "0|1|
S1S33A1S1SdA1M0G0G0SdS3aSdR1R2A3S3aSdR2R5A3F_;Fj;S1dS0S43R5R4R3R2A4S18R5R4R3R2A4A3F_;Fbfrom;Fbto;Fball;Ffacts;").
Proof.
  intros facts ball bto. induction bto as [|i r IH]; intros [|j r'] Hsub; cbn [bud_le_pos' bud_le_pos]; try reflexivity.
  rewrite !lazy_andb_eq. rewrite (item_nn'_eq facts ball (Some j) i) by (apply Hsub; left; reflexivity).
  rewrite (IH r') by (intros x Hx; apply Hsub; right; exact Hx).
  destruct ((0 <=? bi_v i) && (bi_v i <=? bi_v j) && (0 <=? bi_k i) && (bi_k i <=? bi_k j)); [|reflexivity].
  destruct (item_nn facts ball i); [|reflexivity]. destruct (item_le facts i j); reflexivity.
Qed.

Fixpoint items_nn' (facts : list sprop) (bfrom : list bitem) (bto hints : list bitem) : bool :=
  match bto with
  | [] => true
  | i :: r => match hints with
              | j :: h' => item_nn' facts bfrom (Some j) i &&& items_nn' facts bfrom r h'
              | [] => item_nn' facts bfrom None i &&& items_nn' facts bfrom r []
              end
  end.
Lemma items_nn'_eq : ltac2:(tb__ "0|1|
S1S33A1S1SdA1M0G0G0SdS3aSdR1R2A3S3aSdR2R5A3F_;Fj;S1dS0S46R5R4R3R2A4S3cSdS11R5R4A2R3A3A3F_;Fhints;Fbto;Fbfrom;Ffacts;").
Proof.
  intros facts bfrom bto. induction bto as [|i r IH]; intros hints Hh; cbn [items_nn' forallb]; [reflexivity|].
  destruct hints as [|j h'].
  - rewrite lazy_andb_eq, (item_nn'_eq facts bfrom None i I), (IH [] Hh). reflexivity.
  - rewrite lazy_andb_eq. rewrite (item_nn'_eq facts bfrom (Some j) i) by (apply Hh; left; reflexivity).
    rewrite (IH h') by (intros x Hx; apply Hh; right; exact Hx). reflexivity.
Qed.

Definition bud_pay' (facts : list sprop) (costV : sv) (costK : Z) (bfrom bto : list bitem) : bool := ltac2:(tb__ "0|5|
S0S0L_;M0S5S5S10Vbfrom;A1S10Vbto;A1A2S4aZ0VcostK;A2A2G0S46Vfacts;Vbfrom;Vbto;Vbfrom;A4G0S3SeS1fA2S0Lx;M1S14Vbfrom;A1SeS1fG1S14Vbto;A1SeS1fS12Vfacts;S7S3S1fSfA2M2R4S7G2S1cR2A1M3S9G2ScS1fSfN1S15VcostV;A1A4SaG2A1A3A3A3S4bR3R1A2M4A3Ltc;Ltf;X3x1Lfc;Lff;X3x1G1S13Vbfrom;A1SeS1fG1S13Vbto;A1SeS1fS12Vfacts;S7G2R4G3A3S4bG4VcostK;A2A3Ltc;Ltf;X3x1Lfc;Lff;X3x1S2X0x2S2X0x2S2X0x2").
Lemma bud_pay'_eq : ltac2:(tb__ "0|1|
S1S33A1S38S1fS1SdA1M0G0S1dS0S44R5R4R3R2R1A5S19R5R4R3R2R1A5A3Fbto;Fbfrom;FcostK;FcostV;Ffacts;").
Proof.
  intros. unfold bud_pay', bud_pay. rewrite !lazy_andb_eq. rewrite (items_nn'_eq facts bfrom bto bfrom) by (intros j H; exact H).
  destruct (bd_wpos bfrom), (bd_wpos bto), (forallb (item_nn facts bfrom) bto), (0 <=? costK); cbn; try reflexivity;
    destruct (wformV bfrom) as [ff fc]; destruct (wformV bto) as [tf tc]; destruct (lf_nonneg _ _ _); reflexivity.
Qed.

Definition bud_le' (facts : list sprop) (bto bfrom : list bitem) : bool := ltac2:(tb__ "0|1|
S0S0L_;S43Vfacts;Vbfrom;Vbto;Vbfrom;A4S6S44Vfacts;S36Z0M0A1G0Vbfrom;Vbto;A5X0x2").
Lemma bud_le'_eq : ltac2:(tb__ "0|1|
S1S33A1S1SdA1M0G0S1dS0S42R3R2R1A3S17R3R2R1A3A3Fbfrom;Fbto;Ffacts;").
Proof.
  intros. unfold bud_le'. rewrite lazy_orb_eq, bud_pay'_eq. rewrite (bud_le_pos'_eq facts bfrom bto bfrom) by (intros j H; exact H). rewrite bud_le_ref_eq. reflexivity.
Qed.

Definition echeckJA' (NP : positive) (nodes : list (axst * ndesc)) (e : edgeA) : bool := ltac2:(tb__ "0|5|
S4S3S21S24A2M0A1S0Lx;M1S3bG0Vnodes;S3fVe;A1A3G0G0S0Lp;R1S21S24G1S3bG0Vnodes;S41Ve;A1A3G0G0S0Lp0;R1S21S24S0S0L_;M2S5S5S5S5S51S40Ve;A1M3VNP;A2S54VNP;S35S22R5A1A1M4A2A2S32G4R4A2A2S53G3S2aR4A1S2aR1A1A3A2S31G3S29R4A1S29R1A1A3A2G2S42S34S22S3eVe;A1A1A1S16G3S28R1A1A2S28R4A1A3S2bS2cG3S27R1A1A2S27R4A1A2S2X0x2S2X0x2Lndj;LTj;X3x1Lp0;S2X4x2Lndi;LTi;X3x1Lp;S2X4x2").
Lemma echeckJA'_eq : ltac2:(tb__ "0|0|
S20S1S3S21S24A2A1S3dS1dS0S45R3R2R1A3S2dR3R2R1A3A3Fe;Fnodes;FNP;").
Proof.
  intros. unfold echeckJA', echeckJA.
  destruct (nth_error nodes (ea_src e)) as [[Ti ndi]|]; [|reflexivity]. destruct (nth_error nodes (ea_tgt e)) as [[Tj ndj]|]; [|reflexivity].
  rewrite !lazy_andb_eq, bud_le'_eq. rewrite <- !andb_assoc. reflexivity.
Qed.

Definition eecheckJA' (NP : positive) (nodes : list edescA) (e : edgeA) : bool := ltac2:(tb__ "0|5|
S0S0L_;M0S45VNP;S4eS23S3S21S24A2S2fVnodes;A4Ve;A3S4S23A1S0Lx;M1S3bS23Vnodes;S3fVe;A1A3S23G1S3bS23Vnodes;S41Ve;A1A3S23S5S5S39S35S22S2eR2A1A1A1S26R2A1M2A2S4aZ0S25R1A1M3A2A2G0S4dG3S25R2A1M4A2S6G0S4cG3G4A2S52S34S22S3eVe;A1A1A1S37S50S40Ve;A1S26R1A1A2G2A2A2S2X0x2X0x2A2Lnj;S2X4x2Lni;S2X4x2S2X0x2").
Lemma eecheckJA'_eq : ltac2:(tb__ "0|0|
S20S1S23A1S3dS1dS0S47R3R2R1A3S30R3R2R1A3A3Fe;Fnodes;FNP;").
Proof.
  intros. rewrite eecheckJA_ref_eq. unfold eecheckJA', eecheckJA_ref. rewrite lazy_andb_eq, echeckJA'_eq.
  destruct (nth_error nodes (ea_src e)) as [ni|]; [|reflexivity]. destruct (nth_error nodes (ea_tgt e)) as [nj|]; [|reflexivity].
  rewrite !lazy_andb_eq, !lazy_orb_eq. reflexivity.
Qed.

Section C.
Variable segs : list Segment.
Lemma cut_okE_ext : ltac2:(tb__ "0|1|
S8S1S1fA1S20S3dS0F_;M0G0S8S21S1S21A1S3dS1dS0R6R1A1R5R1A1A3Fe;S1dS0S49Vsegs;R9R8R7R6R4R3R2A8S49Vsegs;R9R8R7R5R4R3R2A8A3F_;Ftargets;FT;Fi;FP';FP;Fg;Fcutpcs;Ffuel;").
Proof.
  intros fuel cutpcs g P P' i T targets HP. unfold cut_okE.
  destruct (sym_runA segs fuel cutpcs T true) as [leaves|]; [|reflexivity].
  destruct (leaves_edgesA g i leaves targets) as [es|]; [|reflexivity].
  f_equal. induction es as [|e r IH]; cbn; [reflexivity|]. rewrite HP, IH. reflexivity.
Qed.
End C.
End Lib_handle_f_fastcert.

(* [comment removed for export] *)
Module StartGlueB.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "cell"; "valuation"; "sobj"; "mkObj"; "eval"; "obj_holds"; "odefault"; "SLit"; "mkCell"; "ob_dflt"; "sprop"; "ss_next"; "DUnknown"; "holds"; "rd"; "ss_objs"; "agree_below"; "cell_holds"; "oaddr"; "ob_base"; "ob_cells"; "ob_hi"; "ob_lo"; "rd_bytes"; "ss_facts"; "sstate"; "swf"; "@Corelib.Init.Logic"; "eq"; "and"; "ex"; "not"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Datatypes"; "list"; "Some"; "option"; "nat"; "bool"; "cons"; "length"; "true"; "app"; "nil"; "prod"; "pair"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "ax_setS"; "axst"; "@Stdlib.ZArith.BinInt.Z"; "modulo"; "add"; "le"; "of_nat"; "lt"; "opp"; "pow"; "mul"; "shiftr"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "@Stdlib.Lists.List"; "nth_error"; "filter"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartDefsA"; "replace_obj_at"; "@Corelib.Lists.ListDef"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e5.StartGlueB"; "byte_cells"; "drop_cells"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "same_but_objs"; "diffs_ok"; "state_diff"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e8.StartGlueA"; "bump_next"; "@Stdlib.PArith.BinPos.Pos"; "le"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymCall Glue3 SymHeap SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt LedgerA StepA SoundA EntailA GlueA GlueA2 SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts KxA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require StartDefsA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e8.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.KxA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e7.StartNodes OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartDefsA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e8.StartGlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition drop_cells (keep : cell -> bool) (o : sobj) : sobj := ltac2:(tb__ "0|0|
S4S14Vo;A1S17Vo;A1S16Vo;A1S41S1Vkeep;S15Vo;A1A3SaVo;A1A5").

Lemma obj_holds_drop_cells_unknown : ltac2:(tb__ "0|0|
S2S42S1S26F_;S3S1cS7SaR1A1SdA3S6S2eR5R4R2A4S6S2eR6R5S46R4R3A2A4F_;F_;Fo;Fkeep;Fms;Frho;").
Proof.
  intros rho ms keep o Hu (Hb & Hw & Hc & Hd & Hi). unfold drop_cells. rewrite Hu in *.
  split; [exact Hb|]. split; [exact Hw|]. split.
  - apply Forall_forall. intros c Hcin. apply filter_In in Hcin as [Hcin _]. exact (proj1 (Forall_forall _ _) Hc c Hcin).
  - split; [|exact I]. cbn [ob_dflt ob_cells ob_base ob_lo ob_hi]. intros off Hoff Hnc.
    assert (DEC : forall c, {in_cell rho off c} + {~ in_cell rho off c}).
    { intros c0. unfold in_cell. destruct (Z_le_dec (soff rho (c_off c0)) off); [destruct (Z_lt_dec off (soff rho (c_off c0) + c_width c0)); [left; lia | right; lia] | right; lia]. }
    destruct (Exists_dec (in_cell rho off) (ob_cells o) DEC) as [Hcov|Hncov]; [|exact (Hd off Hoff Hncov)].
    unfold SymState.covered in Hcov. apply Exists_exists in Hcov as (c & Hcin & Hin).
    pose proof (proj1 (Forall_forall _ _) Hc c Hcin) as (C1 & C2 & C3). unfold in_cell in Hin.
    assert (Hnw : bv_unsigned (oaddr rho (ob_base o) (soff rho (c_off c))) + Z.of_nat (Z.to_nat (c_width c)) <= 2 ^ 64).
    { unfold oaddr. rewrite Z_to_bv_unsigned. unfold obj_lo_of, obj_hi_of in *.
      rewrite bv_wrap_small by (change (bv_modulus 64) with (2 ^ 64); lia). lia. }
    pose proof (rd_bytes_nth _ _ _ _ (Z.to_nat (off - soff rho (c_off c))) C3 ltac:(lia) Hnw) as R.
    unfold dflt_holds.
    replace (Z_to_bv 64 (bv_unsigned (eval rho (ob_base o)) + off))
      with (Z_to_bv 64 (bv_unsigned (oaddr rho (ob_base o) (soff rho (c_off c))) + Z.of_nat (Z.to_nat (off - soff rho (c_off c))))).
    2:{ unfold oaddr. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
        rewrite Z2Nat.id by lia. rewrite Zplus_mod_idemp_l. f_equal. lia. }
    eexists. exact R.
Qed.

Lemma SPA_drop_cells_unknown : ltac2:(tb__ "0|1|
S3fS2S31S25S3S1S26F_;S22S3bQ40A1A1S47S1cS24S3A1S40S3S10S2fR6A1A1R5A3S23S3R4A2A3S1cS7SaR5A1SdA3S1cS26S48S2fR8A1M0S43G0R7S46R5R6A2A3A2S29A3S3eS2eRbR9RaR5R4A6S3eS2eRcS30RaS43S2fRaA1R9S46R7R8A2A3A2RbR6R5A6F_;F_;F_;F_;Fw;Ftp;Fkeep;Fo;Fi;FA;Frho;FJ;").
Proof.
  intros J rho A i o keep tp w Hn Hu Hsame Hsp.
  apply (SPA_replace_obj J rho A i o); try assumption.
  - reflexivity.
  - intros ms _ Ho. apply obj_holds_drop_cells_unknown; assumption.
Qed.

Lemma SPA_ghosts : ltac2:(tb__ "0|4|
S3fS2S2S31S1aS21S22S3bQ40A1A1M0S47S22S2cS0S0A2A1M1S22SbA1M2S2S2G0S22S4cA1S4bRfR5R3R2R1A4R10R5R4R3R2A4F_;Fmd;Ftr;Ft;Fr';Fr;S11ScS2fR8A1A1RaR9A3S4eScS2fR9A1A1R7A2S1cS26S1bR9A1S29A3S1cS24S2cG1G2A2M3A1S4aS4dS2fRbA1R9A2RaA2S23G3S2dG1G2R6R5A4A2A3S1cS21ScRbA1RaA3S49ReR8A2S44SbSeRfA1R8A3S3eS2eR12RfR11RcRbA6S3eS2eR13S30R10RfA2R11RdRcA6F_;F_;F_;F_;F_;F_;F_;F_;F_;Fnf;Fd;Fw;Ftp;Fnx;FS';FA;Frho';Frho;FJ;").
Proof.
  intros J rho rho' A S' nx tp w d nf HJ Hag Hnx Hwf Hsd HnS Hd Hnf Hsp.
  pose proof (SPA_bump_agree J rho rho' A nx tp w HJ Hag Hnx Hsp) as H1.
  replace (ax_setS A S') with (ax_setS (ax_setS A (bump_next (ax_S A) nx)) S') by (destruct A; reflexivity).
  eapply (SPA_restate segsA J rho' (ax_setS A (bump_next (ax_S A) nx)) S' tp w d nf Hwf); [exact Hsd | cbn; rewrite HnS; reflexivity | exact Hd | exact Hnf | exact H1].
Qed.

Lemma rd_bytes_1 : ltac2:(tb__ "0|2|
S42S3bQ40A1S3bQ8A1M0S1cS24S22G0A1M1A1S18R3R2U1A3S23G1S27G0R1S2bG0A1A3A2A3S1cS24G0A1SfR4R3A2S23G0R2A2A3F_;Fb;Fa;Fms;").
Proof. intros ms a b H. cbn in H. destruct (rd ms a); [|discriminate]. inversion H. reflexivity. Qed.

Lemma Z_to_bv8_mod : ltac2:(tb__ "0|2|
S20S20S1cS20S32R2Z100M0A2S32R1G0A2A3S1cS3bQ8M1A1S3dG1R3A2S3dG1R2A2A3F_;Fb;Fa;").
Proof. intros a b H. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. exact H. Qed.

Fixpoint byte_cells (off : Z) (es : list sv) : list cell :=
  match es with [] => [] | e :: r => byte_cells (off + 1) r ++ [mkCell (SLit off) 1 e] end.

Lemma byte_cells_rd : ltac2:(tb__ "0|5|
S2S42S0S20S20S22S0A1M0S20S44S1S12R7R5R4R3R6A5S45R1R2A2A3S34S37S38Z2Z3fA2M1A1R2A2S36S33R3S35S28S0R4A2A1A2G1A2S1dS25S0S1cS24S0A1S40S0R7R2A3S23S0R1A2A3S1eS20S20S1dS1cS20S32S3cQ40S5ReR3A2A2Z100M2A2S32R1G2A2A3S1cS24S3bQ8M3A1M4A1SfRdS13ReRcS33R8S35R4A1A2A3A2S23G4S3dG3R1A2A2A3A2Lz;A2F_;Fe;Fk;S1fS1cG0R5S2bS0A1A3A1S1dS34R8R5A2S34S33R5S35S28S0R6A2A1A2R7A2A2F_;A2F_;F_;F_;Foff;Fes;Fhi;Flo;Fbase;Fms;Frho;").
Proof.
  intros rho ms base lo hi es. induction es as [|e es IH]; intros off HF Hlo Hhi.
  - split; [intros [|k] e0 H; discriminate | intros X; exfalso; exact (X eq_refl)].
  - cbn [byte_cells] in HF. apply Forall_app in HF as [HF1 HF2]. inversion HF2 as [|c l (C1 & C2 & C3) _]; subst. cbn [c_off c_width c_val] in C1, C2, C3.
    rewrite soff_lit_small in C1, C2, C3 by lia. cbn [length] in Hhi |- *.
    destruct (IH (off + 1) HF1 ltac:(lia) ltac:(lia)) as [IH1 IH2]. split.
    + intros [|k] e0 H.
      * cbn in H. inversion H; subst. exists (bv_unsigned (eval rho e0)). split; [reflexivity|].
        rewrite Z.add_0_r. apply rd_bytes_1 in C3. rewrite C3. unfold enc_bytes. cbn [Z_to_le_bytes Z.to_nat Pos.to_nat]. reflexivity.
      * cbn in H. destruct (IH1 k e0 H) as (z & Hz & Hr). exists z. split; [exact Hz|].
        replace (off + Z.of_nat (S k)) with (off + 1 + Z.of_nat k) by lia. exact Hr.
    + intros _. destruct es as [|e' es']; [cbn; lia|]. specialize (IH2 ltac:(discriminate)). cbn [length] in IH2 |- *. lia.
Qed.

Lemma obj_holds_merge8 : ltac2:(tb__ "0|4|
S2S42S0S0S0S7S20S22S0A1S0S22S1A1S1cS25S28S0R3A2U8A3S34S37S38Z2Z3fA2M0A1R5A2S36S33R6Z8M1A2G0A2S25S0S1cS24S0A1S40S0R8R2A3S23S0R1A2A3S1cS20S32S3cQ40M2S5R10R2A2A2Z100M3A2S32S3aS3cG2S5R10R8A2A2S39G1S35R3A1A2A2G3A2A3F_;Fe;Fk;S6S2eReRdS4RcRbRaS2aS1S45R8R7A2R5A3R9A5A4S6S2eRfReS4RdRcRbS27S1S9S8R9A1G1R7A3R6A3RaA5A4F_;F_;F_;F_;F_;Frest;Fev;Fes;Foff;Fd;Fhi;Flo;Fbase;Fms;Frho;").
Proof.
  intros rho ms base lo hi d off es ev rest Hlen Hlo Hhi Hbytes (Hb & Hw & Hc & Hd & Hi).
  cbn [ob_base ob_lo ob_hi ob_cells ob_dflt] in *. unfold obj_lo_of, obj_hi_of in *. cbn [ob_lo ob_hi] in *.
  apply Forall_app in Hc as [HcB HcR].
  destruct (byte_cells_rd rho ms base _ _ es off HcB Hlo ltac:(rewrite Hlen; cbn; lia)) as [RD BND].
  specialize (BND ltac:(destruct es; [discriminate|discriminate])). rewrite Hlen in BND. change (Z.of_nat 8) with 8 in BND.
  split; [exact Hb|]. split; [exact Hw|]. split; [|split; [|exact Hi]].
  - constructor; [|exact HcR]. unfold cell_holds, obj_lo_of, obj_hi_of. cbn [ob_lo ob_hi c_off c_width c_val]. rewrite soff_lit_small by lia.
    split; [lia|]. split; [lia|].

    assert (STEP : forall k, (k <= 8)%nat ->
              rd_bytes ms (oaddr rho base (off + Z.of_nat (8 - k))) k = Some (Z_to_le_bytes k (Z.shiftr (bv_unsigned (eval rho ev)) (8 * Z.of_nat (8 - k))))).
    { induction k as [|k IHk]; intros Hk; [reflexivity|].
      cbn [rd_bytes Z_to_le_bytes].
      destruct (nth_error es (8 - S k)) as [e|] eqn:En.
      2:{ exfalso. apply nth_error_None in En. rewrite Hlen in En. lia. }
      destruct (RD _ _ En) as (z & Hz & Hr). rewrite Hr.
      replace (oaddr rho base (off + Z.of_nat (8 - S k)) + 1)%bv with (oaddr rho base (off + Z.of_nat (8 - k))).
      2:{ unfold oaddr. apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. rewrite Zplus_mod_idemp_l. f_equal. change (bv_unsigned 1%bv) with 1. lia. }
      rewrite (IHk ltac:(lia)). f_equal. f_equal.
      + apply Z_to_bv8_mod. rewrite <- Hz. apply Hbytes. exact En.
      + f_equal. rewrite Z.shiftr_shiftr by lia. f_equal. lia. }
    specialize (STEP 8%nat ltac:(lia)). rewrite Nat.sub_diag in STEP. cbn [Z.of_nat] in STEP. rewrite Z.add_0_r, Z.mul_0_r, Z.shiftr_0_r in STEP.
    exact STEP.
  - intros off' Hoff' Hnc. apply Hd; [exact Hoff'|]. intros Hcov. apply Hnc.
    unfold SymState.covered in Hcov |- *. apply Exists_app in Hcov as [Hcov|Hcov]; [|apply Exists_cons_tl; exact Hcov].
    apply Exists_cons_hd. unfold in_cell. cbn [c_off c_width]. rewrite soff_lit_small by lia.
    apply Exists_exists in Hcov as (c & Hcin & Hin).

    assert (GEN : forall es' o', In c (byte_cells o' es') -> exists j, (j < length es')%nat /\ c = mkCell (SLit (o' + Z.of_nat j)) 1 (nth j es' ev)).
    { induction es' as [|e' es' IH']; intros o' Hc'; [destruct Hc'|]. cbn [byte_cells] in Hc'. apply in_app_iff in Hc' as [Hc'|[<-|[]]].
      - destruct (IH' (o' + 1) Hc') as (j & Hj & ->). exists (S j). split; [cbn; lia|]. cbn [nth]. f_equal. f_equal. lia.
      - exists 0%nat. split; [cbn; lia|]. rewrite Z.add_0_r. reflexivity. }
    destruct (GEN es off Hcin) as (j & Hj & ->). unfold in_cell in Hin. cbn [c_off c_width] in Hin. rewrite soff_lit_small in Hin by lia.
    rewrite Hlen in Hj. lia.
Qed.

Lemma SPA_merge8 : ltac2:(tb__ "0|5|
S3fS2S31S25S0S0S0S7S20S22S0A1S0S22S1A1S22S3bQ40M0A1A1S47S1cS24S3A1S40S3S10S2fRcA1A1RbA3S23S3S4RaR9R8S2aS1S45R6R5A2R3A3R7A5A2A3S1cS25S28S0R6A2U8A3S34S37S38Z2Z3fA2M1A1R8A2S36S33R9Z8M2A2G1A2S44SbSeR11A1S19S2fR10A1A1A3S25S0S1cS24S0A1S40S0RcR2A3S23S0R1A2A3S1cS20S32S3cG0S5R15R2A2A2Z100M3A2S32S3aS3cG0S5R15RcA2A2S39G2S35R3A1A2A2G3A2A3F_;Fe;Fk;F_;S1cS26S48S2fR11A1M4S43G4R10S4RfReRdS27S1S9S8RbA1G2R9A3R8A3RcA5A3A2S29A3S3eS2eR14R12R13R8R7A6S3eS2eR15S30R13S43S2fR13A1R12S4R11R10RfS27S1S9S8RdA1G2RbA3RaA3ReA5A3A2R14R9R8A6F_;F_;F_;F_;F_;F_;F_;Fw;Ftp;Frest;Fev;Fes;Foff;Fd;Fhi;Flo;Fbase;Fi;FA;Frho;FJ;").
Proof.
  intros J rho A i base lo hi d off es ev rest tp w Hn Hlen Hlo Hhi Hbytes Hsame Hsp.
  pose proof (SPA_facts_hold segsA _ _ _ _ _ Hsp) as HF.
  apply (SPA_replace_obj J rho A i _ _ tp w Hn); [reflexivity | | exact Hsame | exact Hsp].
  intros ms _ Ho. apply (obj_holds_merge8 rho ms base lo hi d off es ev rest Hlen Hlo Hhi (Hbytes HF) Ho).
Qed.
End StartGlueB.

(* [comment removed for export] *)
Module StartGlueE.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e8.StartGlueA"; "bump_next"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts"; "segsA"; "@Corelib.Init.Datatypes"; "bool"; "true"; "list"; "prod"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "ax_setS"; "axst"; "axwf"; "@Corelib.Numbers.BinNums"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "smatch"; "swf"; "valuation"; "sstate"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "@stdpp.bitvector.definitions"; "bv"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymCall Glue3 SymHeap SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt LedgerA StepA SoundA EntailA GlueA GlueA2 SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts KxA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require StartDefsA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e8.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.KxA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e7.StartNodes OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartDefsA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e8.StartGlueA.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Lemma smatch_set_next : ltac2:(tb__ "0|0|
SeSfSbS5S4S13A1S12A2S6S2SdS0R3R2A2A1S3A3ScS1R5R4R2A4ScS1R6S0R5R4A2R3A4F_;F_;Fw;Fnx;FS;Frho;").
Proof.
  intros rho S nx [tr [ms md]] Hwf' Hsm.
  destruct Hsm as (Hwf & Hpc & Hpend & Hhalt & Hrom & Hroc & Hregs & Hfregs & Hfcsr & Hresv & Hmem & Hfacts).
  unfold smatch, bump_next in *. cbn [fst snd cfg_ms cfg_model ss_pc ss_regs ss_fregs ss_fcsr ss_resv ss_objs ss_facts ss_next ss_lenient] in *.
  split; [exact Hwf'|]. repeat (split; [assumption|]). exact Hfacts.
Qed.

Lemma SPA_set_next : ltac2:(tb__ "0|0|
S11SeS9SbS4S15Q40A1A1S14S6S2SdS0S7R4A1R3A2A1S3A3S6S2SaS8R5S0S7R5A1R4A2A2A1S3A3S10S1R8R6R7R4R3A6S10S1R9S8R7S0S7R7A1R6A2A2R8R5R4A6F_;F_;F_;Fw;Ftp;Fnx;FA;Frho;FJ;").
Proof.
  intros J rho A nx tp w Hwf' Hax' [(Hsm & HMI & Hwf & Hsh & Hhz) Hk]. split; [|exact Hk].
  split; [|split; [exact HMI | split; [exact Hax' | split; [|exact Hhz]]]].
  - unfold virt in Hsm |- *. cbn [ax_S ax_setS]. apply smatch_set_next; assumption.
  - unfold shadow_ok in Hsh |- *. cbn [ax_S ax_setS ax_X ax_base bump_next ss_objs] in Hsh |- *. exact Hsh.
Qed.
End StartGlueE.

(* [comment removed for export] *)
Module StartGlueD.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SLit"; "mkCell"; "sobj"; "cell"; "ob_cells"; "obj_holds"; "rd_bytes"; "valuation"; "ss_objs"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "pow"; "lt"; "mul"; "of_nat"; "modulo"; "opp"; "shiftr"; "@Corelib.Init.Datatypes"; "nat"; "Some"; "list"; "bool"; "option"; "true"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts"; "segsA"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartDefsA"; "add_cell_front"; "replace_obj_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e5.StartGlueD"; "subcell_val"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "ax_setS"; "axst"; "cell_eqb"; "@Corelib.Init.Nat"; "add"; "@Corelib.Init.Peano"; "le"; "@Corelib.Lists.ListDef"; "firstn"; "skipn"; "@LinuxProcessSemantics.LinuxProcessSem.BvBase"; "Z_to_le_bytes"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "same_but_objs"; "@Stdlib.Lists.List"; "In"; "existsb"; "nth_error"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR SymSoundW
  SymComplete SymFrame SymEntail SymCFG SymCall Glue3 SymHeap SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SoundA EntailA GlueA GlueA2 SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts KxA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require StartDefsA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e8.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.KxA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.StartALib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e7.StartNodes OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartDefsA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e8.StartGlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Lemma rd_bytes_sub : ltac2:(tb__ "0|4|
S2aS1bQ40M0A1S13S15S1bQ8A1M1A1M2S13S13S19S17G2A1M3S7R6R5R4A3S14G2R3A2A3S26S25R3R2A2R5A2SaSbS1cG0R7A2SfR6A1A2ScZ2Z40A2A2S19G3S7R9S1dG0SbS1cG0R8A2SfR5A1A2A2R4A3S14G2S27G1R4S28G1R5R6A3A3A2A3F_;F_;F_;Fk';Fd;Fbs;Fk;Fa;Fms;").
Proof.
  intros ms a k bs d k' H Hdk Hnw. pose proof (rd_bytes_length _ _ _ _ H) as L.
  pose proof (urange a) as Ua.
  destruct (Nat.eq_dec k' 0) as [->|Hk'].
  { cbn. reflexivity. }
  assert (U : bv_unsigned (Z_to_bv 64 (bv_unsigned a + Z.of_nat d)) = bv_unsigned a + Z.of_nat d).
  { rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64). lia. }
  apply rd_bytes_of_nth.
  - rewrite length_firstn, length_skipn, L. lia.
  - rewrite U. lia.
  - intros j Hj. rewrite U.
    replace (bv_unsigned a + Z.of_nat d + Z.of_nat j) with (bv_unsigned a + Z.of_nat (d + j)) by lia.
    rewrite (rd_bytes_nth ms k a bs (d + j) H ltac:(lia) Hnw). f_equal.
    rewrite nth_firstn. replace (PeanoNat.Nat.ltb _ _) with true by (symmetry; apply PeanoNat.Nat.ltb_lt; lia). rewrite nth_skipn. reflexivity.
Qed.

Lemma Z_to_le_bytes_sub : ltac2:(tb__ "0|1|
S13S0S13S13S26S25R2R1A2R4A2S19S15S1bQ8A1M0A1S27G0R2S28G0R3S29R5R4A2A3A3S29R2S12R4SeZ8SfR3A1A2A2A2A3F_;Fk';Fd;Fz;Fk;").
Proof.
  intros k z d k' H. apply nth_ext with (d := Z_to_bv 8 0) (d' := Z_to_bv 8 0).
  - rewrite length_firstn, length_skipn, !Z_to_le_bytes_length. lia.
  - intros n Hn. rewrite length_firstn, length_skipn, Z_to_le_bytes_length in Hn.
    rewrite nth_firstn. replace (PeanoNat.Nat.ltb _ _) with true by (symmetry; apply PeanoNat.Nat.ltb_lt; lia). rewrite nth_skipn. rewrite !Z_to_le_bytes_nth by lia.
    rewrite Z.shiftr_shiftr by lia. f_equal. f_equal. lia.
Qed.

Definition subcell_val (v : Z) (d k' : Z) : Z := ltac2:(tb__ "0|2|
S10S12S10Vv;ScZ2M0Z40A2A2SeZ8M1Vd;A2A2ScG0SeG1Vk';A2A2A2").

Lemma obj_holds_add_subcell : ltac2:(tb__ "0|3|
S8S2aS3S0S0S0S0S0S6S1aR8R7R6A4S2fS4S2S1R6A1R5S1R4A1A3S5R7A1A3SaS11ScZ2Z3fA2M0A1R7A2SdSbR8R7A2M1G0A2SaZ0M2R6A2SdG2R6A2SaG1RaA2SaRbZ8A2S6S1aR10RfS1eReS2S1SbRdRaA2A1R9S1S20RbRaR9A3A1A3A2A4F_;F_;F_;F_;F_;F_;F_;F_;Fk';Fd;Fv;Fk;Foff;Fo;Fms;Frho;").
Proof.
  intros rho ms o off k v d k' Ho Hin Hlo Hhi Hd Hk' Hdk Hk8.
  unfold add_cell_front. change (mkObj (ob_base o) (ob_lo o) (ob_hi o) (?c :: ob_cells o) (ob_dflt o)) with (obj_add_cell o (SLit (off + d)) k' (SLit (subcell_val v d k'))). apply (obj_holds_add_cell segsA rho ms o). { exact Ho. }
  destruct Ho as (Hb & Hw & Hc & Hdf & Hi).
  pose proof (proj1 (Forall_forall _ _) Hc _ Hin) as (C1 & C2 & C3). cbn [c_off c_width c_val] in C1, C2, C3.
  rewrite soff_lit_small in C1, C2, C3 by lia.
  unfold cell_holds. cbn [c_off c_width c_val]. rewrite soff_lit_small by lia.
  split; [lia|]. split; [lia|].
  destruct Hb as (B1 & B2 & B3 & B4). unfold obj_lo_of, obj_hi_of in *. pose proof (urange (eval rho (ob_base o))) as UB.
  assert (UO : bv_unsigned (oaddr rho (ob_base o) off) = bv_unsigned (eval rho (ob_base o)) + off).
  { unfold oaddr. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64). lia. }
  assert (Hnw : bv_unsigned (oaddr rho (ob_base o) off) + Z.of_nat (Z.to_nat k) <= 2 ^ 64) by (rewrite UO; lia).
  pose proof (rd_bytes_sub ms (oaddr rho (ob_base o) off) (Z.to_nat k) _ (Z.to_nat d) (Z.to_nat k') C3 ltac:(lia) Hnw) as R.
  replace (Z_to_bv 64 (bv_unsigned (oaddr rho (ob_base o) off) + Z.of_nat (Z.to_nat d))) with (oaddr rho (ob_base o) (off + d)) in R.
  2:{ unfold oaddr. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. rewrite Zplus_mod_idemp_l. f_equal. lia. }
  rewrite R. f_equal. cbn [eval]. unfold enc_bytes. rewrite Z_to_le_bytes_sub by lia.
  rewrite <- (Z_to_le_bytes_mod (Z.to_nat k')). rewrite <- (Z_to_le_bytes_mod (Z.to_nat k') (bv_unsigned (Z_to_bv 64 (subcell_val v d k')))). f_equal.
  unfold subcell_val. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  rewrite !Z2Nat.id by lia.
  pose proof (Z.mod_pos_bound (Z.shiftr (v mod 2 ^ 64) (8 * d)) (2 ^ (8 * k')) ltac:(apply Z.pow_pos_nonneg; lia)) as MB.
  assert (LT : 2 ^ (8 * k') <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia).
  rewrite (Z.mod_small ((Z.shiftr (v mod 2 ^ 64) (8 * d)) mod 2 ^ (8 * k')) (2 ^ 64)) by lia. rewrite Z.mod_mod by lia. reflexivity.
Qed.

Lemma SPA_add_subcell : ltac2:(tb__ "0|4|
S2cS8S23S13S3S0S0S0S0S0S15S1bQ40A1A1S2dS19S17S3A1S31S3S9S21RaA1A1R9A3S14S3R8A2A3S19S16S30S4S24S2S1R8A1R7S1R6A1A3A1S5R9A1A3S18A3SaS11ScZ2Z3fA2M0A1R9A2SdSbRaR9A2M1G0A2SaZ0M2R8A2SdG2R8A2SaG1RcA2SaRdZ8A2S19S16S2eS21R12A1M3S1fG3R11S1eR10S2S1SbRfRcA2A1RbS1S20RdRcRbA3A1A3A2A3A2S18A3S2bS1aR15R13R14RbRaA6S2bS1aR16S22R14S1fS21R14A1R13S1eR12S2S1SbR11ReA2A1RdS1S20RfReRdA3A1A3A2A3A2R15RcRbA6F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fw;Ftp;Fk';Fd;Fv;Fk;Foff;Fo;Fi;FA;Frho;FJ;").
Proof.
  intros J rho A i o off k v d k' tp w Hn Hex Hlo Hhi Hd Hk' Hdk Hk8 Hsame Hsp.
  apply existsb_exists in Hex as (c & Hc & Heq). apply cell_eqb_sound in Heq. subst c.
  apply (SPA_replace_obj J rho A i o); try assumption.
  - reflexivity.
  - intros ms _ Ho. eapply obj_holds_add_subcell; eauto.
Qed.
End StartGlueD.

