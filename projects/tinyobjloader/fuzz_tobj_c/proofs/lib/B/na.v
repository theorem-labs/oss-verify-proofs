(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require GlueZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require ZeroObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require MuslWLA DrvGlueB.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3 n5.
From Stdlib Require Logic.FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require StackLayout Fs Monad Specs.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Mmap.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Uapi.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require ExecutableSpecs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require RegGlobIface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p1.

(* [comment removed for export] *)
Module Str_memsetZ.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SLit"; "sobj"; "valuation"; "sstate"; "sprop"; "rw"; "SVar"; "SAlu"; "ss_next"; "agree_below"; "cell"; "mkObj"; "ss_lenient"; "sv_eqb"; "eval"; "mkSS"; "swf"; "FcsrFrm0"; "SPUle"; "DUnknown"; "DZero"; "ss_facts"; "ss_pc"; "ss_objs"; "holds"; "mkCell"; "obj_range"; "ss_regs"; "SAluW"; "ob_base"; "ob_hi"; "ob_lo"; "sprop_below"; "ss_fcsr"; "ss_fregs"; "ss_resv"; "@Corelib.Init.Datatypes"; "bool"; "cons"; "prod"; "option"; "false"; "andb"; "pair"; "list"; "nat"; "nil"; "true"; "None"; "Some"; "fst"; "snd"; "app"; "negb"; "@Corelib.Init.Logic"; "eq"; "and"; "or"; "False"; "ex"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "sub"; "opp"; "modulo"; "eqb"; "mul"; "of_nat"; "lt"; "to_nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "leafA"; "ax_S"; "la_state"; "axst"; "ax_setS"; "ax_base"; "entailsA"; "ax_X"; "la_reason"; "sym_runA"; "mkLeafA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "pre_fregs"; "setregs"; "pre_regs"; "NPOST"; "post_regs"; "two62"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "LQA"; "@Stdlib.Lists.List"; "In"; "forallb"; "flat_map"; "nth_error"; "existsb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy"; "liftA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.na.Str_memsetZ"; "u_range"; "zvC"; "CZ"; "run1"; "zvN"; "P_msz"; "addl"; "Posts_mszA"; "is_cut"; "setreg"; "zvD"; "ZBODY"; "noX"; "restate_okb"; "Pre_mszA"; "PC_K"; "PC_T"; "ex_okb"; "factsCZ"; "factsZ"; "fin_okb"; "is_ret"; "it_okb"; "lit_okb"; "r_range"; "s_en"; "zfold_at"; "KX"; "L1_MAX"; "L2_MIN"; "P_lit"; "T4X"; "ZRET"; "diff_isb"; "eT"; "en_okb"; "kut_range"; "lit_range"; "s_it"; "ur_range"; "NAk"; "NXk"; "O_du"; "O_dz"; "PC_N"; "Pre_big"; "Pre_lit"; "ZB"; "eX"; "factsN"; "guard"; "regsCZ"; "remC"; "tail_cells"; "CZX"; "CZi"; "M4"; "Pre_msz"; "pair_inb"; "stage2"; "stage3"; "xdiffs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "world"; "etriple"; "triple"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_AND"; "ALU_SUB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "wsub"; "rho_sub"; "wsub_get"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "same_but_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "stop_reason"; "list_set"; "set_objs"; "RsSymJump"; "@Corelib.Lists.ListDef"; "map"; "Forall"; "seq"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj"; "merge_objs_at"; "split_obj_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CursorGlue"; "M64v"; "@Stdlib.PArith.BinPos.Pos"; "le"; "eqb"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueZ"; "zero_covered"; "zobj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ZeroObj"; "zero_obj"; "zero_obj_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.MuslMemset"; "N14"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymObj SymEntail SymCFG SymSummary Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA CFGA GlueA GlueZ SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv MuslMemset CursorGlue ZeroObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import CfgGlueA MuslWLA DrvGlueB.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition ZB : Z := memset_entryA.
Definition ZRET : Z := memset_entryA + 0xf4.
Definition O_du (hi : sv) : sobj := ltac2:(tb__ "0|0|
SeS9PcA1S3Z0A1Vhi;S30SdA1S16A5").
Definition O_dz (hi : sv) : sobj := ltac2:(tb__ "0|0|
SeS9PcA1S3Z0A1Vhi;S30SdA1S17A5").
Definition factsZ : list sprop := [N14].

Definition Pre_msz : sstate := ltac2:(tb__ "0|1|
S12S93S54S55S28S29S2fS2A2M0S2dS2fS2UbS3Z0A1A4S30G0A1A3A2S53S14S32S2A1S28S4S8eS9PeA1A1S30S4A1A3S77S52S2bA9").

Definition P_msz : sstate := ltac2:(tb__ "0|1|
S12S84S54S57S52A1S28S29S2fS2A2M0S2dS2fS2UaS9PcA1A4S30G0A1A3A2S53S14S32S2A1S28S4S8fS9PeA1A1S30S4A1A3S77S56S2bA9").
Definition Pre_mszA : axst := liftA Pre_msz.
Definition Posts_mszA : list leafA := ltac2:(tb__ "0|0|
S28S47S51S63S69A1Sb2A2S30S47A1A3").

Definition KX : sv := ltac2:(tb__ "0|0|
SaSa7S1fSa8S3Z0A1S9PcA1A3S3Z3A1A3").
Definition M4 : Z := 18446744073709551612.
Definition NXk (k : Z) : sv := ltac2:(tb__ "0|2|
S27S2L_;S42Vk;Z0A2SaSa7S9PeA1M0S3S9cA1M1A3SaSa7SaSa6G0S3S40Vk;A1A1A3G1A3X27x2").
Definition NAk (k u : Z) : sv := ltac2:(tb__ "0|2|
S27S2L_;S42S3eVk;Vu;A2M0Z0A2S9PeA1M1SaSa6G1S3S40G0A1A1A3X27x2").
Definition T4X (k : Z) : sv := ltac2:(tb__ "0|2|
S27S2L_;S42Vk;Z0A2SaSa7S9PcA1M0S3Z4A1M1A3SaSa7SaSa6G0S3Vk;A1A3G1A3X27x2").
Definition PC_K : Z := ZB + 0x50.
Definition PC_N : Z := ZB + 0x64.
Definition PC_T : Z := ZB + 0xa4.
Definition ZBODY : Z := ZB + 0xd8.

Definition setreg (A : axst) (r : nat) (e : sv) : axst := ltac2:(tb__ "0|0|
S48VA;A1S6S4bVA;S12S19R1A1Sb0S2S1eR1A1Vr;Ve;A4S25R1A1S24R1A1S26R1A1S1aR1A1S18R1A1SbR1A1SfR1A1A9A2TS;").

Definition run1 (fuel : nat) (cuts : list Z) (A : axst) : option leafA := ltac2:(tb__ "0|3|
S2aS2eS47A1M0A1S2aS47A1M1Lx;S50S59Vfuel;Vcuts;VA;S31A5G0G0G1Ll;R1S32S47A1M2S47G0G0G1Ll0;R1S33S47R2A2S47G0G2Ll2;Ll1;X2ex2Ll0;LL;X2ex2Ll;G2X2ax2").

Definition restate_okb (A : axst) (r : nat) (e e' : sv) : bool := ltac2:(tb__ "0|6|
S2cS2cS10Sb6S2Vr;S1eS48VA;A1M0A1S3Z0A1A4Ve;A2S13S48S6dVA;Vr;Ve';A3A1M1A1A2S2aS29S2eS29S2S2A2M2A1M3S2eS7A1M4A2M5A1S27Lx;SadG0G1A2G5G5S27Lp;R1G3G4G4S27Ll;R1S5fG2G2S2cS10S34S2S2R1A3Ve;A2S10S35S2S2R1A3Ve';A2A2Lp;R2A3S7G4S2bLl0;Ls;X2ex2Ll;Ld;X29x1Lp;S2bX2ax2A2").
Definition is_ret (L : leafA) : bool := ltac2:(tb__ "0|0|
S2cS42S19S48S49VL;A1A1A1S84A2SafS27Lx;S4fVL;A1S2bS2bS2bS2bS31S2bS2bXafx7A2").
Definition is_cut (L : leafA) (pc : Z) : bool := ltac2:(tb__ "0|1|
S2cS2cS2cS42S19S48S49VL;A1A1M0A1Vpc;A2SafS27Lx;S4fVL;A1S2bS31S2bS2bS2bS2bS2bXafx7A2S37SfG0A1A1A2SbcS52SbG0A1A2A2").
Definition noX (A : axst) : bool := ltac2:(tb__ "0|2|
S2cS2eS29S2S2A2M0A1M1S27Lx;S4eVA;A1S31G0G1S2bLl;Lp;X2ex2S10S4cVA;A1S4cS63S69A1A1A2A2").
Definition diff_isb (a b : sv) (d : list (sv * sv)) : bool := ltac2:(tb__ "0|1|
S5fS29S2S2A2M0G0S2cS10S34S2S2R1A3Va;A2S10S35S2S2R1A3Vb;A2A2Lp;Vd;A3").

Definition Pre_lit (n : Z) : sstate := ltac2:(tb__ "0|2|
S12S93S54S55S28S29S2fS2A2M0S2dS2fS2UbS3Z0A1A4S28G0S2dS2fS2UcS3Vn;A1M1A4S30G0A1A3A3A2S53S14S32S2A1S28S4S8eG1A1S30S4A1A3S77S52S2bA9").
Definition P_lit (n : Z) : sstate := ltac2:(tb__ "0|1|
S12S84S54S57S52A1S28S29S2fS2A2M0S2dS2fS2UaS9PcA1A4S30G0A1A3A2S53S14S32S2A1S28S4S8fS3Vn;A1A1S30S4A1A3S77S56S2bA9").

Definition fin_okb (n : Z) (L : leafA) : bool := ltac2:(tb__ "0|3|
S2cS2cS79VL;A1S70S49VL;A1M0A1A2S2aS6A1S27Lx;Sc1S48G0A1M1U0A2S6SbdS52R1S82Vn;A1M2A3SaaS2cS2cSaeG1R2A2S4dS63R2A1S63G2A1R1A3A2Sa9R1S52A2A2Ts;LSz;S2bX2ax2A2").
Definition stage3 (fuel : nat) (n k t4 : Z) (E2 : axst) : bool := ltac2:(tb__ "0|2|
S2cS71VE2;UfM0S83Vk;A1S3Vt4;A1M1A4S2aS47A1S27Lx;S67Vfuel;S30S0A1S6dVE2;G0G1A3A3S47S78Vn;R1A2LL;S2bX2ax2A2").
Definition stage2 (fuel : nat) (n k t4 : Z) (E1 : axst) : bool := ltac2:(tb__ "0|2|
S2cS71VE1;UdM0S7fS3Vk;A1M1A4S2aS47A1S27Lx;S67Vfuel;S28S0S74S30S0A1A3S6dVE1;G0G1A3A3S47S27S27L_;S79R1A1S78Vn;R1A2S2cS6cR1S74A2Sa0Vfuel;Vn;Vk;Vt4;S49R1A1A5A2X27x2LL;S2bX2ax2A2").
Definition lit_okb (fuel : nat) (c : Z * Z * Z) : bool := ltac2:(tb__ "0|8|
S29S29S0S0A2M0S0A2S27Lc;Vc;G0S0G0S27Lp;R2S0S0S2aS29S2eS29S2S2A2A1M1S2eS7A1M2A2M3A1S27Lx;M4SadS9dS92R2A1A2G3G3S27Lp;R1G1G2G2S27Ll;R1G4SadS82R5A1S69A2G3G3S27Lp0;R1G1G2G2S27Ll0;R1S2cS2cS2cS2cS85S9PeA1M5S3R8A1M6R5A3S85G6G5R2A3A2S13S92R8A1M7A1A2S13S69A1A2S2aS47A1S27Lx;S67Vfuel;S28S0S73S30S0A1A3S63G7A1A3S47S27S27L_;S79R1A1S78R9R1A2S2cS6cR1S73A2S9fVfuel;R9R8RaS49R1A1A5A2X27x2LL;S2bX2ax2A2S7G2S2bLl1;Ls;X2ex2Ll0;Ld2;X29x1Lp0;S2bX2ax2S7G2S2bLl0;Ls;X2ex2Ll;Ld1;X29x1Lp;S2bX2ax2Lk;Ln;X29x1Lt4;Lp;X29x1").

Definition L1_MAX : Z := 103.
Definition lit_range : list (Z * Z * Z) := ltac2:(tb__ "0|4|
S60S2fS29S29S0S0A2M0S0A2M1S2fS60S2fG1S2fS28G1S2dG0S0S2dS0S0S44R2A1S44R1A1A4M2Z0A4S28G1S2dG0S0G2Z4A4S30G1A1A3A3Lk;Sb5U0M3U4A2A4Ln;Sb5G3S46S3eS80Z1A2A1A2A4").
Lemma lit_allb : ltac2:(tb__ "0|0|
S38S27S5fS29S29S0S0A2S0A2S7bU190A1S89A3S31A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma lit_range_in : ltac2:(tb__ "0|3|
S0S0S0S39S3dZ0M0R3A2M1S3dR3S80A2A2S39G1S3dR3Z3A2A2S3aS38S0R3G0A3S38S0R3Z4A3A2S5eS29S29S0S0A2M2S0A2S2dG2S0S2dS0S0R6R5A4R4A4S89A3F_;F_;F_;Ft4;Fk;Fn;").
Proof.
  intros n k t4 Hn Hk Ht. unfold lit_range. apply in_flat_map. exists (Z.to_nat n). split; [apply in_seq; unfold L1_MAX in *; lia|].
  apply in_flat_map. exists (Z.to_nat k). split; [apply in_seq; lia|]. rewrite !Z2Nat.id by lia.
  destruct Ht as [-> | ->]; [left; reflexivity | right; left; reflexivity].
Qed.
Lemma lit_ok : ltac2:(tb__ "0|2|
S0S0S0S39S3dZ0M0R3A2M1S3dR3S80A2A2S39G1S3dR3Z3A2A2S3aS38S0R3G0A3S38S0R3Z4A3A2S38S27S7bU190S2dS29S0S0A2S0S2dS0S0R6R5A4R4A4A2S31A3F_;F_;F_;Ft4;Fk;Fn;").
Proof. intros n k t4 Hn Hk Ht. exact (proj1 (forallb_forall _ _) lit_allb _ (lit_range_in n k t4 Hn Hk Ht)). Qed.

Definition L2_MIN : Z := 104.
Definition zvD : sv := SVar 12.
Definition zvN : sv := SVar 14.
Definition zvC : sv := SVar 100.
Definition addl (a : sv) (z : Z) : sv := ltac2:(tb__ "0|0|
SaSa6Va;S3Vz;A1A3").
Definition eT : sv := addl zvN (-32).
Definition factsN : list sprop := ltac2:(tb__ "0|0|
S28S7Sc3S28S7S15S3S81A1S68A2S30S7A1A3A3").
Definition tail_cells (u : Z) : list cell := ltac2:(tb__ "0|6|
S36SdSb3S0SdS0S1cS6aS68S3fS40Vu;A1S43Z4M0R1A2A2A2G0S3Z0A1M1A3Lj;S28S0Z1M2S28S0Z2M3S28S0Z3M4S28S0G0S28S0Z5S28S0Z6S28S0Z7S30S0A1M5A3A3A3A3A3A3A3A4Sb3S0SdS0S1cS6aS68S40R1A1A2G2G1A3Lj;S28S0G2S28S0G3S28S0G4S28S0G0G5A3A3A3A3A4A3").
Definition regsCZ (cur rem a5 : sv) : list sv := ltac2:(tb__ "0|1|
S54S55S28S29S2fS2A2M0S2dS2fS2UbSaSa6S6eVcur;A3A4S28G0S2dS2fS2UcS3Z0A1A4S28G0S2dS2fS2UdS3Z1fA1A4S28G0S2dS2fS2UeVrem;A4S28G0S2dS2fS2UfVa5;A4S28G0S2dS2fS2U10S3Z20A1A4S30G0A1A3A3A3A3A3A3A2").
Definition remC (u : Z) : sv := ltac2:(tb__ "0|0|
SaSa8S6aS68S40Vu;A1A2S65A3").
Definition factsCZ (u : Z) : list sprop := ltac2:(tb__ "0|0|
S36S7S95S28S7S15S65S68A2S28S7S15S6aS65S3eZ20Vu;A2A2S68A2S28S7S15S3Z18A1S65A2S30S7A1A3A3A3A3").

Definition CZ (u : Z) : sstate := ltac2:(tb__ "0|1|
S12S6fS97S65S98Vu;A1S9P65A1A3S53S14S32S2A1S28S4SeS6eS3Z0A1S65S30SdA1M0S17A5S28S4SeS6eS65S86G0S16A5S28S4SeS6eS86S68S99Vu;A1S16A5S30S4A1A3A3A3S76Vu;A1P66S2bA9").

Definition CZi (u : Z) : axst := ltac2:(tb__ "0|0|
Sc2S63S66Vu;A1A1S28S7S15S6aS65S3eZ40Vu;A2A2S68A2S76Vu;A1A3A2").

Definition eX (u r : Z) : sv := ltac2:(tb__ "0|0|
S6aS68S40S3eS3eVu;Z20A2Vr;A2A1A2").
Definition CZX (u r : Z) : sstate := ltac2:(tb__ "0|1|
S12S6fS97S94Vu;Vr;A2M0S3S3eZ20Vr;A2A1S9P65A1A3S53S14S32S2A1S28S4SeS6eS3Z0A1G0S30SdA1S17A5S28S4SeS6eG0S68S99Vu;A1S16A5S30S4A1A3A3S95P66S2bA9").
Definition xdiffs (u r : Z) : list (sv * sv) := ltac2:(tb__ "0|2|
S28S29S2S2A2M0S2dS2S2SaSa6S6eS65A3SaSa6S6eS94Vu;Vr;A2M1A3A4S28G0S2dS2S2S98Vu;A1S3S3eZ20Vr;A2A1A4S28G0S2dS2S2S65G1A4S30G0A1A3A3A3").
Definition pair_inb (l : list (sv * sv)) (p : sv * sv) : bool := ltac2:(tb__ "0|1|
S62S29S2S2A2M0G0S2cS10S34S2S2Vp;A3S34S2S2R1A3A2S10S35S2S2Vp;A3S35S2S2R1A3A2A2Lq;Vl;A3").

Definition s_it : wsub := ltac2:(tb__ "0|2|
S28S29S1S2A2M0S2dS1S2P64S6aS65Z20A2A4S28G0S2dS1S2P65M1S9G1A1A4S30G0A1A3A3").
Definition s_en (k t4 : Z) : wsub := ltac2:(tb__ "0|1|
S28S29S1S2A2M0S2dS1S2P64S3S3eS3eVk;Z38A2Vt4;A2A1A4S28G0S2dS1S2P65S3S3eZ18Vt4;A2A1A4S30G0A1A3A3").

Definition guard {T} (fuel : nat) (x : option T) : option T := match fuel with O => None | S _ => x end.
Lemma guard_Some : forall {T} fuel (x : option T) y, guard fuel x = Some y -> x = Some y.
Proof. intros T [|f] x y H; [discriminate H | exact H]. Qed.

Definition zfold_at (S : sstate) (i : nat) : option sstate := ltac2:(tb__ "0|3|
S2aS4A1S2aS6A1M0Lx;S61S4S1aVS;A1M1Vi;A3S4S27G0L_;SbeS18VS;A1R1A2S33S6Sb1VS;Sb0S4G1Vi;SbfR1A1A4A2A2S32S6A1M2X27x2Lo;G2X2ax2").

Definition it_okb (fuel : nat) (u : Z) : bool := ltac2:(tb__ "0|3|
S2cS5fS7S23P66A1S28S7S15S6aS65S3eZ40Vu;A2A2S68A2S76Vu;A1A3A3S2aS47A1S27Lx;S67Vfuel;S28S0S6fS30S0A1A3S9bVu;A1A3S47S2cS2cS6cR1S6fA2S70S49R1A1M0A1A2S2aS6A1S27Lx;M1Sb8S48G0A1U1M2S6aS65Z20A2A3S6G1S7eR1G2A2S6G1Sb7R1U0A2S6S4dS4bS49R4A1R1A2S63S66Vu;A1A1S8aA3LS3;S2bX2ax2LS2;S2bX2ax2LS1;S2bX2ax2A2LL;S2bX2ax2A2").

Definition ex_okb (fuel : nat) (ur : Z * Z) : bool := ltac2:(tb__ "0|8|
S29S0S0A2S27Lur;Vur;S0S0S2aS6A1S27Lx;M0S96S6Vfuel;Sb7S66R2A1U1M1A2A3S6S2cS2cS2cSbbSbR1A1P66A2S13S9aR3R2A2M2A1A2S2aS29S2eS29S2S2A2M3A1M4S2eS7A1M5A2M6A1S27Lx;SadR1G2A2G6G6S27Lp;R1G4G5G5S27Ll;R1S5fG3S9eSa1R6R5A2A1R2A3S7G5S2bLl0;Ls;X2ex2Ll;Ld;X29x1Lp;S2bX2ax2A2S2aS47A1S27Lx;S67Vfuel;S30S0A1S63G2A1A3S47S2cS2cS79R1A1S70S49R1A1M7A1A2G0S7eS48G7A1G1A2S6G0Sb7R1U0A2S6SbdS52R1S69A3SaaS2cS4dS4bS49R4A1R2A2S63S69A1R1A3Sa9R1S52A2A2Ts;LS3;S2bX2ax2LS2;S2bX2ax2A2LL;S2bX2ax2A2LSm;S2bX2ax2Lr;Lu;X29x1").

Definition Pre_big : axst := ax_with_facts Pre_mszA factsN.
Definition en_okb (fuel : nat) (c : Z * Z * Z) : bool := ltac2:(tb__ "0|e|
S29S29S0S0A2M0S0A2S27Lc;Vc;G0S0G0S27Lp;R2S0S0S2aS6A1S27Lx;M1S96S6Vfuel;Sb8S48S91A1U0M2S86A3A3S6S2cS2cSbbSbR1A1S52A2S37SfR1A1A1A2S2aS47A1S27Lx;M3S67Vfuel;S28S0S73S30S0A1M4A3S4bS91R1A2A3S47S2cS2cS6cR1S73A2S71S49R1A1M5UdM6S7fS3R4A1M7A4A2G3S67Vfuel;S28S0S90G4A3S6dG5G6G7A3A3S47S2cS2cS6cR1S90A2S71G5UeM8S8dR5A1S8cR5R4A2M9A4A2G3S67Vfuel;S28S0S74G4A3S6dG5G8G9A3A3S47S2cS2cS6cR1S74A2S71G5UfMaS83R6A1S3R7A1MbA4A2G3S67Vfuel;S28S0S6fG4A3McS6dG5GaGbA3A3S47S2cS6cR1S6fA2MdG3S67Vfuel;GcG5A3S47S2cS2cGdS70G5A1A2G1Sb8S48G5A1G2S3S3eS3eR8Z38A2R9A2A1A3S6G1S7eR1G2A2S6S4dS4bS49R3A1R1A2S63S66R9A1A1S7dRaRbA2A3LS6;S2bX2ax2LS5;S2bX2ax2A2LL5;S2bX2ax2A2LL4;S2bX2ax2A2LL3;S2bX2ax2A2LL2;S2bX2ax2A2LL1;S2bX2ax2A2LS0;S2bX2ax2Lu;Lk;X29x1Lt4;Lp;X29x1").

Definition u_range : list Z := ltac2:(tb__ "0|0|
S28S0Z0S28S0Z1S28S0Z2S28S0Z3S30S0A1A3A3A3A3").
Definition r_range : list Z := ltac2:(tb__ "0|0|
S28S0Z0S28S0Z4S28S0Z8S28S0ZcS28S0Z10S28S0Z14S28S0Z18S28S0Z1cS30S0A1A3A3A3A3A3A3A3A3").
Definition ur_range : list (Z * Z) := ltac2:(tb__ "0|1|
S60S0S29S0S0A2M0S0Sb3S0G0S0S2dS0S0R2R1A4Lr;S7cA4Lu;S64A4").
Definition kut_range : list (Z * Z * Z) := ltac2:(tb__ "0|3|
S60S0S29S29S0S0A2M0S0A2M1S0S60S0G1S0S28G1S2dG0S0S2dS0S0R2R1A4M2Z0A4S28G1S2dG0S0G2Z4A4S30G1A1A3A3Lu;S64A4Lk;S64A4").

Lemma it_allb : ltac2:(tb__ "0|0|
S38S27S5fS0S7aU28A1S64A3S31A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ex_allb : ltac2:(tb__ "0|0|
S38S27S5fS29S0S0A2S75U28A1S8bA3S31A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma en_allb : ltac2:(tb__ "0|0|
S38S27S5fS29S29S0S0A2S0A2S87U78A1S88A3S31A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma swf_CZ : ltac2:(tb__ "0|0|
S38S27S5fS0S0S2cS2cS13S66R1A1A1Sa9S8aS52A2A2S5fS0S0S2cSa9S7dR1Z0A2S52A2Sa9S7dR1Z4A2S52A2A2Lk;S64A3A2Lu;S64A3S31A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Local Notation "'U' rho i" := (bv_unsigned (rw rho i)) (at level 10, rho at level 9, i at level 9).

Lemma U_KX_range : ltac2:(tb__ "0|1|
S5S39S3dZ0S5aQ40S11R1S7fA2A2M0A2S3dG0Z3A2A2Frho;").
Proof.
  intros rho. unfold KX. cbn [eval]. rewrite and_val, lit_unsigned. change (3 mod 2 ^ 64) with (Z.ones 2).
  rewrite Z.land_ones by lia. pose proof (Z.mod_pos_bound (bv_unsigned (sext 64 (alu32 ALU_SUB (low32 (Z_to_bv 64 0)) (low32 (rw rho 12))))) (2 ^ 2) ltac:(lia)). lia.
Qed.
Lemma U_T4X_cases : ltac2:(tb__ "0|1|
S5S0S3aS38S0S5aQ40S11R2S83R1A1A2A2M0Z0A3S38S0G0Z4A3A2Fk;Frho;").
Proof.
  intros rho k.
  assert (G : forall x : word, Z.land (bv_unsigned x) 4 = 0 \/ Z.land (bv_unsigned x) 4 = 4).
  { intros x. destruct (Z.testbit (bv_unsigned x) 2) eqn:B.
    - right. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec.
      destruct (Z.eq_dec i 2) as [->|Hne]; [rewrite B; reflexivity|].
      replace (Z.testbit 4 i) with false; [rewrite andb_false_r; reflexivity|].
      symmetry. change 4 with (2 ^ 2). rewrite Z.pow2_bits_eqb by lia. apply Z.eqb_neq. lia.
    - left. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
      destruct (Z.eq_dec i 2) as [->|Hne]; [rewrite B; reflexivity|].
      replace (Z.testbit 4 i) with false; [rewrite andb_false_r; reflexivity|].
      symmetry. change 4 with (2 ^ 2). rewrite Z.pow2_bits_eqb by lia. apply Z.eqb_neq. lia. }
  unfold T4X. destruct (k =? 0); cbn [eval]; rewrite and_val, lit_unsigned; change (4 mod 2 ^ 64) with 4; apply G.
Qed.

Lemma add_neg_lit : ltac2:(tb__ "0|0|
S0S0S39S3dZ0R1A2S3dR1R2A2A2S45R3Sb9A2S38S0S41S3eR4S41S40R3A1Sb9A2A2Sb9A2S3fR4R3A2A3F_;F_;Fc;Fx;").
Proof.
  intros x c Hc Hx. rewrite Z.add_mod_idemp_r by (cbv; discriminate).
  rewrite Z.mod_small; unfold M64v in *; lia.
Qed.
Lemma U_NX : ltac2:(tb__ "0|2|
S5S0S39S3dZ0R1A2S3dR1Z3A2A2S3dR2S5aQ40M0S8R3PeM1A2A2A2S38S5bG0A1S11R4S8dR3A1A2S11R4S8cR3S41S3fS5aG0S8R4G1A2A2R3A2Z4A2A2A2A3F_;F_;Fk;Frho;").
Proof.
  intros rho k Hk Hle. pose proof (urange (rw rho 14)) as Hr. rewrite M64v_eq in Hr.
  pose proof (Z.mod_pos_bound (U rho 14 - k) 4 ltac:(lia)) as Hm.
  pose proof (Z_div_mod_eq_full (U rho 14 - k) 4) as Hdm.
  assert (HM4 : forall x, 0 <= x < M64v -> Z.land x M4 = x - x mod 4).
  { intros x Hx. unfold M4. apply land_m4. rewrite M64v_eq. exact Hx. }
  apply bv_eq. unfold NXk, NAk.
  destruct (Z.eqb_spec k 0) as [->|Hk0].
  - rewrite Z.sub_0_r in *. cbn [eval]. rewrite and_val. change (bv_unsigned (Z_to_bv 64 M4)) with M4.
    rewrite HM4 by lia.
    destruct (Z.eqb_spec (0 + U rho 14 mod 4) 0) as [E0|NE].
    + cbn [eval]. lia.
    + change (bv_unsigned (eval rho (SAlu ALU_ADD (SVar 14) (SLit (- (0 + U rho 14 mod 4))))))
        with (bv_unsigned (eval rho (SAlu ALU_ADD (SVar 14) (SLit (- (0 + U rho 14 mod 4)))))).
      rewrite U_add, U_lit. cbn [eval]. rewrite add_neg_lit; lia.
  - cbn [eval]. rewrite and_val. change (bv_unsigned (Z_to_bv 64 M4)) with M4.
    rewrite add_val, lit_unsigned, M64v_eq, add_neg_lit by lia.
    rewrite HM4 by lia.
    destruct (Z.eqb_spec (k + (U rho 14 - k) mod 4) 0) as [E0|NE]; [lia|].
    change (bv_unsigned (eval rho (SAlu ALU_ADD (SVar 14) (SLit (- (k + (U rho 14 - k) mod 4))))))
      with (bv_unsigned (eval rho (SAlu ALU_ADD (SVar 14) (SLit (- (k + (U rho 14 - k) mod 4)))))).
    rewrite U_add, U_lit. cbn [eval]. rewrite add_neg_lit; lia.
Qed.

Lemma restate_keeps : ltac2:(tb__ "0|2|
S4aS2fS2S39S38S1SbS48S6dR3R2R1A3A1M0A1SbS48R3A1M1A1A3S38S27SfG0A1SfG1A1A3A2Fe;Fr;FA;").
Proof. intros. split; reflexivity. Qed.
Lemma is_cut_sound : ltac2:(tb__ "0|1|
S47S0S38S27S6cR2R1A2S31A3S39S38S0S19S48S49R3A1A1M0A1R2A3S39S38S27SfG0A1S2bA3SbaS52SbG0A1A2A2A2F_;Fpc;FL;").
Proof.
  intros L pc H. unfold is_cut in H. apply andb_prop in H as [H H3]. apply andb_prop in H as [H H2]. apply andb_prop in H as [H1 _].
  apply Z.eqb_eq in H1. apply Pos.leb_le in H3. destruct (ss_lenient (ax_S (la_state L))); [discriminate|]. auto.
Qed.
Lemma noX_sound : ltac2:(tb__ "0|1|
S4aS38S27S70R1A1S31A3S39S38S2eS29S2S2A2M0A1S4eR2A1S30G0A1A3S38S2S4cR2A1S4cS63S69A1A1A3A2F_;FA;").
Proof.
  intros A H. unfold noX in H. apply andb_prop in H as [H1 H2]. apply sv_eqb_sound in H2.
  destruct (ax_X A); [auto | discriminate].
Qed.
Lemma noX_lift : ltac2:(tb__ "0|0|
S4aS6S38S27S70R2A1S31A3S38S4aS4bR3R2A2S63R2A1A3F_;FS;FA;").
Proof. intros [SA XA bA] S H. destruct (noX_sound _ H) as [H1 H2]. cbn in H1, H2 |- *. subst. reflexivity. Qed.
Lemma zfold_at_spec : ltac2:(tb__ "0|1|
S6S2fS6S38S2aS6A1S7eR3R2A2S33S6R1A2A3S3cS4S4S39S38S2aS4A1S61S4S1aR5A1M0R4A3S33S4R1A2A3S39S38S27SbeS18R5A1R1A2S31A3S38S6R3Sb1R5Sb0S4G0R4SbfR1A1A4A2A3A2A2Lo;A2F_;FS';Fi;FS;").
Proof.
  intros S i S' H. unfold zfold_at in H. destruct (nth_error (ss_objs S) i) as [o|]; [|discriminate].
  destruct (zero_covered (ss_facts S) o) eqn:Z0; [|discriminate]. injection H as <-. exists o. auto.
Qed.
Lemma rw_rho_sub : ltac2:(tb__ "0|0|
S5SaaS1S38S5bQ40A1S8SabR3R2A2R1A2S11R3SacR2R1A2A2A3Fv;Fs;Frho;").
Proof. intros. reflexivity. Qed.

Lemma in_u_range : ltac2:(tb__ "0|0|
S0S39S3dZ0R1A2S3dR1Z3A2A2S5eS0R2S64A3F_;Fu;").
Proof. intros u Hu. unfold u_range. assert (u = 0 \/ u = 1 \/ u = 2 \/ u = 3) as [-> | [-> | [-> | ->]]] by lia; cbn; tauto. Qed.
Lemma in_ur_range : ltac2:(tb__ "0|0|
S0S0S5eS0R2S64A3S5eS0R2S7cA3S5eS29S0S0A2S2dS0S0R4R3A4S8bA3F_;F_;Fr;Fu;").
Proof. intros u r Hu Hr. unfold ur_range. apply in_flat_map. exists u. split; [exact Hu|]. apply in_map_iff. exists r. auto. Qed.
Lemma in_r_range : ltac2:(tb__ "0|0|
S0S39S3dZ0R1A2S3dR1Z7A2A2S5eS0S43Z4R2A2S7cA3F_;Fm;").
Proof.
  intros m Hm. unfold r_range.
  assert (m = 0 \/ m = 1 \/ m = 2 \/ m = 3 \/ m = 4 \/ m = 5 \/ m = 6 \/ m = 7) as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]] by lia; cbn; tauto.
Qed.
Lemma in_kut_range : ltac2:(tb__ "0|3|
S0S0S0S39S3dZ0M0R3A2S3dR3Z3A2A2M1G1S3aS38S0R3G0A3S38S0R3Z4A3A2S5eS29S29S0S0A2M2S0A2S2dG2S0S2dS0S0R6R5A4R4A4S88A3F_;F_;F_;Ft4;Fu;Fk;").
Proof.
  intros k u t4 Hk Hu Ht. unfold kut_range. apply in_flat_map. exists k. split; [apply in_u_range; lia|].
  apply in_flat_map. exists u. split; [apply in_u_range; lia|]. destruct Ht as [-> | ->]; cbn; tauto.
Qed.
Lemma u_range_bound : ltac2:(tb__ "0|0|
S0S5eS0R1S64A3S39S3dZ0R2A2S3dR2Z3A2A2F_;Fu;").
Proof. intros u Hu. unfold u_range in Hu. cbn in Hu. lia. Qed.

Lemma swf_CZ_u : ltac2:(tb__ "0|0|
S0S5eS0R1S64A3S38S27S13S66R2A1A1S31A3F_;Fu;").
Proof.
  intros u Hu. pose proof (proj1 (forallb_forall _ _) swf_CZ u Hu) as X. cbn beta in X.
  apply andb_prop in X as [X _]. apply andb_prop in X as [X _]. exact X.
Qed.
Lemma s_it_id : ltac2:(tb__ "0|0|
S38S27Sa9S8aS52A2S31A3").
Proof. reflexivity. Qed.
Lemma s_en_id : ltac2:(tb__ "0|0|
S0S0S38S27Sa9S7dR2R1A2S52A2S31A3Ft4;Fk;").
Proof. reflexivity. Qed.

Lemma factsCZ_num : ltac2:(tb__ "0|2|
S0S5Sb4S7S1bR1A1S76R2A1A3S39S3dS5aQ40M0S8R2PeA2A2M1S58A2S39S3dS81G1A2S3dS5aG0S8R2P64A2A2G1A2A2A2F_;Frho;Fu;").
Proof.
  intros u rho HF. unfold factsCZ, factsN in HF. cbn [app] in HF.
  apply Forall_cons_iff in HF as [H1 HF]. apply Forall_cons_iff in HF as [H2 HF]. apply Forall_cons_iff in HF as [H3 _].
  cbn [holds eval zvN zvC N14] in H1, H2, H3. rewrite lit_unsigned in H1, H2.
  change (two62 mod 2 ^ 64) with two62 in H1. change (L2_MIN mod 2 ^ 64) with L2_MIN in H2. auto.
Qed.

Lemma mod4_entry : ltac2:(tb__ "0|2|
S0S0S0S3aS38S0R1Z0M0A3S38S0R1Z4M1A3A2S38S0S41S3fS3fR4S41S3fR4R3A2G1A2A2S3eS3eR3Z38A2R2A2A2G1A2G0A3F_;Ft4;Fk;Fn;").
Proof.
  intros n k t4 Ht. pose proof (Z_div_mod_eq_full (n - k) 4) as E.
  destruct Ht as [-> | ->].
  - replace (n - (n - k) mod 4 - (k + 56 + 0)) with (((n - k) / 4 - 14) * 4) by lia. apply Z_mod_mult.
  - replace (n - (n - k) mod 4 - (k + 56 + 4)) with (((n - k) / 4 - 15) * 4) by lia. apply Z_mod_mult.
Qed.

Section Sound.
Variable J : jpredA.
Hypothesis Hst : stableA segs NF J.
Variable TR : assn -> assn -> Prop.
Hypothesis TR_pre : ltac2:(tb__ "0|0|
Sa2Sa2Sa2Sa3R3R1A1R5R2A1F_;Fw;VTR;R4R2A2VTR;R4R3A2F_;F_;FQ;FP';FP;").
Hypothesis TR_run : ltac2:(tb__ "0|1|
S2fS2eS0A1S4aS2eS47A1M0S5S2eS5bQ40A1A1Sa2S38S2aG0A1S50S59R7R6R5S31A5S33G0R4A2A3S38S27SfS48R6A1A1S2bA3SbaS52SbS48R7A1A1A2S47S5S5eS47R2R9A3ScSbS48RbA1A1R9R2A3VTR;S5cS59VJ;S49R4A1R3R9A5R8A2F_;F_;Frho';FL;VTR;S5cS59VJ;R9R7R6A5R5A2F_;F_;F_;F_;FQ;Ftp;Frho;Fleaves;FA;Fcuts;Ffuel;").
Hypothesis TR_refl : ltac2:(tb__ "0|0|
Sa2VTR;R1R1A2FP;").
Hypothesis TR_facts : ltac2:(tb__ "0|1|
S4aS5S2eS5bQ40A1A1Sa2Sb4S7S1bR3A1S18S48R4A1A1A3VTR;S5cS59VJ;R5R4R3A5R2A2M0F_;G0F_;FQ;Ftp;Frho;FA;").

Lemma run1_TR : ltac2:(tb__ "0|0|
S2fS2eS0A1S4aS47S5S2eS5bQ40A1A1Sa2S38S2aS47A1S67R7R6R5A3S33S47R4A2A3S38S27SfS48R6A1A1S2bA3SbaS52SbS48R7A1A1A2S5ScSbS48R9A1A1R7R1A3VTR;S5cS59VJ;S49R9A1R2R7A5R6A2F_;Frho';VTR;S5cS59VJ;R9R7R6A5R5A2F_;F_;F_;F_;FQ;Ftp;Frho;FL;FA;Fcuts;Ffuel;").
Proof using TR_run.
  intros fuel cuts A L rho tp Q H Hl Hn HQ. unfold run1 in H.
  destruct (sym_runA segs fuel cuts A true) as [[|L' [|]]|] eqn:E; try discriminate H. injection H as ->.
  eapply (TR_run fuel cuts A [L] rho tp Q E Hl Hn). intros L0 rho' [<-|[]] Hag. exact (HQ rho' Hag).
Qed.

Lemma SPA_setreg : ltac2:(tb__ "0|1|
S4aS2fS2S2S5S2eS5bQ40A1M0A1Sa3S38S27S71R7R6R5R4A4S31A3S38G0S11R4R6A2S11R4R5A2A3S5cS59VJ;R9R5R4R3A6S5cS59VJ;S6dRaR9R7A3R6R5R4A6F_;F_;F_;Fw;Ftp;Frho;Fe';Fe;Fr;FA;").
Proof using .
  intros A r e e' rho tp w H He HS. unfold restate_okb in H. apply andb_prop in H as [H Hd]. apply andb_prop in H as [_ Hwf].
  destruct (state_diff (ax_S A) (ax_S (setreg A r e'))) as [[d [|]]|] eqn:E; try discriminate Hd.
  unfold setreg. apply (SPA_restate segs J rho A _ tp w d [] Hwf E); [reflexivity | | constructor | exact HS].
  unfold diffs_ok. apply Forall_forall. intros [a b] Hin. pose proof (proj1 (forallb_forall _ _) Hd _ Hin) as X. cbn [fst snd] in X |- *.
  apply andb_prop in X as [X1 X2]. apply sv_eqb_sound in X1. apply sv_eqb_sound in X2. subst a b. exact He.
Qed.

Lemma TR_post : ltac2:(tb__ "0|0|
S5S5S2eS5bQ40A1A1ScS52R3R2A3VTR;S5cS59VJ;S63S69A1R3R2A5S5dS59VJ;S52R4R2S6bA6A2F_;Ftp;Frho;Frho0;").
Proof using TR_pre TR_refl.
  intros rho0 rho tp Hag. eapply TR_pre; [|apply TR_refl]. intros w Hw.
  apply (LQA_intro segs J NF rho0 tp (mkLeafA (liftA P_msz) RsSymJump) Posts_mszA rho w); [left; reflexivity | exact Hag | exact Hw].
Qed.

Lemma zero_obj_shape : ltac2:(tb__ "0|0|
S4S4S38S2aS4A1Sc0R2A1S33S4R1A2A3S38S4R2SeS20R3A1S22R3A1S21R3A1S30SdA1S17A5A3F_;Fo';Fo;").
Proof.
  intros o o' H. unfold zero_obj in H.
  destruct (ob_lo o) eqn:El; try discriminate H. destruct (ob_hi o) eqn:Eh; try discriminate H. destruct (ob_dflt o); try discriminate H.
  destruct (zcover_from _ _ _); [|discriminate H]. injection H as <-. reflexivity.
Qed.
Lemma zero_obj_range : ltac2:(tb__ "0|0|
S5S4S4S38S2aS4A1Sc0R2A1S33S4R1A2A3S38S29S0S0A2S1dR4R2A2S1dR4R3A2A3F_;Fo';Fo;Frho;").
Proof. intros rho o o' H. rewrite (zero_obj_shape o o' H). unfold obj_range, obj_lo_of, obj_hi_of. reflexivity. Qed.

Lemma fin_sound : ltac2:(tb__ "0|5|
S0S47S5S5S2eS5bQ40M0A1A1S38S27S78R5R4A2S31A3S2aS29S2eS29S2S2A2A1M1S2eS7A1M2A2M3A1OLx;SadS82R6A1S69A2G3G3OLp;R1G1G2G2OLl;R1S38S27S85S3R9A1S9PeM4A1R2A3S31A3S7G2S3bLl0;Ls;X2ex2Ll;Ld2;X29x1Lp;S3bX2ax2S38S27S13S69A1S31A3S38S0S5aG0S8R6G4A2A2R8A3ScS52R7R6A3VTR;S5cS59VJ;S49R9A1R7R6A5S5dS59VJ;S52R8R6S6bA6A2F_;F_;F_;F_;F_;Ftp;Frho;Frho0;FL;Fn;").
Proof using Hst TR_pre TR_refl.
  intros n L rho0 rho tp H Hd2 Hwf2 Hn Hag.
  unfold fin_okb in H. apply andb_prop in H as [H Hz]. apply andb_prop in H as [Hret HX].
  destruct (zero_obj_at (ax_S (la_state L)) 0) as [Sz|] eqn:EZ; [|discriminate Hz].
  apply andb_prop in Hz as [Hz Hid]. apply andb_prop in Hz as [Hsame He].
  set (rho2 := rho_sub rho (infer_sub NF Sz (P_lit n))).
  assert (Hag2 : agree_below NF rho rho2) by (apply rho_sub_agree; exact Hid).
  apply (TR_pre (SPA segs J (liftA P_msz) rho2 tp)); [|apply TR_post; eapply agree_below_trans; [exact Hag | exact Hag2]].
  intros w [Hsm HJ].

  assert (HS1 : SPA segs J (liftA Sz) rho tp w).
  { unfold zero_obj_at in EZ. destruct (nth_error (ss_objs (ax_S (la_state L))) 0) as [o|] eqn:En; [|discriminate EZ].
    destruct (zero_obj o) as [o'|] eqn:Eo; [|discriminate EZ].
    assert (ESz : Sz = replace_obj_at (ax_S (la_state L)) 0 o') by (injection EZ as <-; reflexivity).
    assert (HS0 : SPA segs J (ax_setS (la_state L) Sz) rho tp w).
    { rewrite ESz. apply (SPA_replace_obj segs J rho (la_state L) 0 o o' tp w En).
      - exact (zero_obj_range rho o o' Eo).
      - intros ms _ Ho. exact (zero_obj_holds segs rho ms o o' Eo Ho).
      - rewrite <- ESz. exact Hsame.
      - split; [exact Hsm | exact HJ]. }
    rewrite (noX_lift _ _ HX) in HS0. exact HS0. }

  pose proof (SPA_entails segs J NF (liftA Sz) (liftA (P_lit n)) _ rho tp w He Hid Hst HS1) as HS2. fold rho2 in HS2.

  destruct (state_diff (P_lit n) P_msz) as [[d2 [|]]|] eqn:E2; try contradiction.
  change (liftA P_msz) with (ax_setS (liftA (P_lit n)) P_msz).
  apply (SPA_restate segs J rho2 (liftA (P_lit n)) P_msz tp w d2 [] Hwf2 E2); [reflexivity | | constructor | exact HS2].
  unfold diffs_ok. apply Forall_forall. intros [a b] Hin. pose proof (proj1 (forallb_forall _ _) Hd2 _ Hin) as X. cbn [fst snd] in X |- *.
  apply andb_prop in X as [X1 X2]. apply sv_eqb_sound in X1. apply sv_eqb_sound in X2. subst a b. cbn [eval].
  destruct Hag2 as (Hv & _ & _). rewrite <- (Hv 14%positive ltac:(cbv; reflexivity)).
  destruct Hag as (Hv0 & _ & _). rewrite <- (Hv0 14%positive ltac:(cbv; reflexivity)). apply bv_eq. rewrite Z_to_bv_unsigned, Hn.
  pose proof (urange (rw rho0 14)). rewrite bv_wrap_small; [reflexivity|]. rewrite two64. lia.
Qed.

Theorem memsetZ_small : ltac2:(tb__ "0|2|
S2fS5S2eS5bQ40M0A1A1S0S0S39S3dZ0M1R2A2S3dR2Z3A2A2S3aS38S0R2G1A3S38S0R2Z4A3A2S38S27S7bR7S2dS29S0S0A2S0S2dS0S0S5aG0S8R6PeA2A2R4A4R3A4A2S31A3F_;F_;Ft4;Fk;VTR;S5cS59VJ;S72R3R2A5S5dS59VJ;S52R3R2S6bA6A2F_;Ftp;Frho;FfuelL;").
Proof using Hst TR_pre TR_refl TR_run.
  intros fuelL rho tp HLn. pose proof (urange (rw rho 14)) as Hr. set (n := U rho 14) in *.
  assert (C0 : lit_okb fuelL (n, 0, 0) = true) by (apply HLn; lia).
  unfold lit_okb in C0.
  destruct (state_diff Pre_msz (Pre_lit n)) as [[d1 [|]]|] eqn:E1; try discriminate C0.
  destruct (state_diff (P_lit n) P_msz) as [[d2 [|]]|] eqn:E2; try discriminate C0.
  apply andb_prop in C0 as [C0 R1]. apply andb_prop in C0 as [C0 W2]. apply andb_prop in C0 as [C0 W1]. apply andb_prop in C0 as [D1 D2].
  assert (HD2 : match state_diff (P_lit n) P_msz with Some (d0, []) => diff_isb (SLit n) (SVar 14) d0 = true | _ => False end) by (rewrite E2; exact D2).

  apply (TR_pre (SPA segs J (liftA (Pre_lit n)) rho tp)).
  { intros w HS. change (liftA (Pre_lit n)) with (ax_setS Pre_mszA (Pre_lit n)).
    apply (SPA_restate segs J rho Pre_mszA (Pre_lit n) tp w d1 [] W1 E1); [reflexivity | | constructor | exact HS].
    unfold diffs_ok. apply Forall_forall. intros [a b] Hin. pose proof (proj1 (forallb_forall _ _) D1 _ Hin) as X. cbn [fst snd] in X |- *.
    apply andb_prop in X as [X1 X2]. apply sv_eqb_sound in X1. apply sv_eqb_sound in X2. subst a b. cbn [eval].
    apply bv_eq. rewrite Z_to_bv_unsigned. subst n. rewrite bv_wrap_small; [reflexivity | rewrite two64; lia]. }

  destruct (run1 fuelL [PC_K] (liftA (Pre_lit n))) as [L1|] eqn:RUN1; [|discriminate R1].
  apply (run1_TR fuelL [PC_K] (liftA (Pre_lit n)) L1 rho tp _ RUN1 eq_refl (Pos.le_refl _)).
  intros rho1 Hag1. cbn [ax_S liftA mkA ss_next] in Hag1.
  destruct (is_ret L1) eqn:RET1.
  { apply (fin_sound n L1 rho rho1 tp R1 HD2 W2 eq_refl Hag1). }
  apply andb_prop in R1 as [CUT1 _]. destruct (is_cut_sound L1 PC_K CUT1) as (_ & Hl1 & Hn1).
  set (k := bv_unsigned (eval rho1 KX)). pose proof (U_KX_range rho1) as Hk. fold k in Hk.
  assert (C1 : lit_okb fuelL (n, k, 0) = true) by (apply HLn; lia).
  unfold lit_okb in C1. rewrite E1, E2, RUN1, RET1 in C1.
  apply andb_prop in C1 as [_ C1]. apply andb_prop in C1 as [_ S2]. unfold stage2 in S2. apply andb_prop in S2 as [RS1 S2].
  apply (TR_pre (SPA segs J (setreg (la_state L1) 13 (SLit k)) rho1 tp)).
  { intros w HS. apply (SPA_setreg (la_state L1) 13 KX (SLit k) rho1 tp w RS1); [|exact HS]. cbn [eval]. apply bv_eq. rewrite Z_to_bv_unsigned. subst k.
    pose proof (urange (eval rho1 KX)). rewrite bv_wrap_small; [reflexivity | rewrite two64; lia]. }
  destruct (run1 fuelL [PC_T] (setreg (la_state L1) 13 (SLit k))) as [L2|] eqn:RUN2; [|discriminate S2].
  destruct (restate_keeps (la_state L1) 13 (SLit k)) as [Kn Kl].
  apply (run1_TR fuelL [PC_T] _ L2 rho1 tp _ RUN2 ltac:(rewrite Kl; exact Hl1) ltac:(rewrite Kn; exact Hn1)).
  intros rho2 Hag2. rewrite Kn in Hag2.
  assert (Hag02 : agree_below NF rho rho2) by (eapply agree_below_trans; [exact Hag1 | eapply agree_below_le; [exact Hn1 | exact Hag2]]).
  destruct (is_ret L2) eqn:RET2.
  { apply (fin_sound n L2 rho rho2 tp S2 HD2 W2 eq_refl Hag02). }
  apply andb_prop in S2 as [CUT2 _]. destruct (is_cut_sound L2 PC_T CUT2) as (_ & Hl2 & Hn2).
  set (t4 := bv_unsigned (eval rho2 (T4X k))). pose proof (U_T4X_cases rho2 k) as Ht. fold t4 in Ht.
  assert (C2 : lit_okb fuelL (n, k, t4) = true) by (apply HLn; lia).
  unfold lit_okb in C2. rewrite E1, E2, RUN1, RET1 in C2.
  apply andb_prop in C2 as [_ C2]. apply andb_prop in C2 as [_ S3]. unfold stage2 in S3. apply andb_prop in S3 as [_ S3].
  rewrite RUN2, RET2 in S3. apply andb_prop in S3 as [_ S3]. unfold stage3 in S3. apply andb_prop in S3 as [RS2 S3].
  apply (TR_pre (SPA segs J (setreg (la_state L2) 15 (SLit t4)) rho2 tp)).
  { intros w HS. apply (SPA_setreg (la_state L2) 15 (T4X k) (SLit t4) rho2 tp w RS2); [|exact HS]. cbn [eval]. apply bv_eq. rewrite Z_to_bv_unsigned. subst t4.
    pose proof (urange (eval rho2 (T4X k))). rewrite bv_wrap_small; [reflexivity | rewrite two64; lia]. }
  destruct (run1 fuelL [] (setreg (la_state L2) 15 (SLit t4))) as [L3|] eqn:RUN3; [|discriminate S3].
  destruct (restate_keeps (la_state L2) 15 (SLit t4)) as [Kn2 Kl2].
  apply (run1_TR fuelL [] _ L3 rho2 tp _ RUN3 ltac:(rewrite Kl2; exact Hl2) ltac:(rewrite Kn2; exact Hn2)).
  intros rho3 Hag3. rewrite Kn2 in Hag3.
  assert (Hag03 : agree_below NF rho rho3) by (eapply agree_below_trans; [exact Hag02 | eapply agree_below_le; [exact Hn2 | exact Hag3]]).
  apply (fin_sound n L3 rho rho3 tp S3 HD2 W2 eq_refl Hag03).
Qed.

Lemma it_TR : ltac2:(tb__ "0|2|
S2fS0S5S2eS5bQ40M0A1A1Sa2S5eS0R4S64A3S38S27S7aR6R5A2S31A3S3dS3eS3eS5aG0S8R5P64M1A2A2Z40A2R6A2S5aG0S8R5PeA2A2A2S5ScS52R7R1A3S38S0S5aG0S8R2G1A2A2S3eS5aG0S8R8G1A2A2Z20A2A3VTR;S5cS59VJ;S63S66RaA1A1R3R8A5R7A2F_;F_;Frho';VTR;S5cS59VJ;S63S66R8A1A1R7R6A5R5A2F_;F_;F_;F_;FQ;Ftp;Frho;Fu;FfuelI;").
Proof using Hst TR_pre TR_run TR_facts.
  intros fuelI u rho tp Q Hu C HR HK. pose proof (u_range_bound u Hu) as Hub. unfold it_okb in C.
  apply andb_prop in C as [FB C].
  destruct (run1 fuelI [ZBODY] (CZi u)) as [L|] eqn:RUN; [|discriminate C].
  apply andb_prop in C as [C1 C]. apply andb_prop in C1 as [CUT NX].
  destruct (split_obj_at (ax_S (la_state L)) 1 (addl zvC 32)) as [S1|] eqn:SP; [|discriminate C].
  destruct (zfold_at S1 1) as [S2|] eqn:ZF; [|discriminate C].
  destruct (merge_objs_at S2 0) as [S3|] eqn:MG; [|discriminate C].
  apply TR_facts. intros HF. cbn [ax_S liftA mkA ss_facts CZ] in HF. destruct (factsCZ_num u rho HF) as (B1 & B2 & B3).
  pose proof (urange (rw rho 100)) as H100. unfold two62 in B1.

  apply (TR_pre (SPA segs J (CZi u) rho tp)).
  { intros w HS. unfold CZi. apply (SPA_refacts segs J rho (liftA (CZ u)) _ tp w HS FB).
    intros HF0. constructor; [|exact HF0]. cbn [holds eval zvN zvC addl]. rewrite add_val, lit_unsigned.
    rewrite (Z.mod_small (64 + u)) by lia. rewrite Z.mod_small; lia. }
  apply (run1_TR fuelI [ZBODY] (CZi u) L rho tp Q RUN eq_refl ltac:(apply Pos.leb_le; reflexivity)).
  intros rho1 Hag1. cbn [CZi ax_with_facts ax_S ax_setS liftA mkA with_facts ss_next CZ] in Hag1.
  destruct (is_cut_sound L ZBODY CUT) as (_ & Hl & Hn).
  destruct (zfold_at_spec S1 1 S2 ZF) as (o & Ho & Hz & ->).
  apply (TR_pre (SPA segs J (liftA (CZ u)) (rho_sub rho1 s_it) tp)).
  { intros w HS.
    pose proof (SPA_split segs J rho1 (la_state L) 1 (addl zvC 32) S1 tp w SP HS) as HS1.
    pose proof (SPA_zero_fold segs J rho1 (ax_setS (la_state L) S1) tp w 1 o Ho Hz HS1) as HS2.
    pose proof (SPA_merge segs J rho1 (ax_setS (la_state L) (set_objs S1 (list_set (ss_objs S1) 1 (zobj o)))) 0 S3 tp w MG HS2) as HS3.
    exact (SPA_entails segs J NF _ _ s_it rho1 tp w C s_it_id Hst HS3). }
  apply HK.
  - eapply agree_below_trans; [eapply agree_below_le; [|exact Hag1]; apply Pos.leb_le; reflexivity | apply rho_sub_agree; exact s_it_id].
  - rewrite rw_rho_sub. change (wsub_get s_it 100) with (SAlu ALU_ADD (SVar 100) (SLit 32)). rewrite U_add, U_lit. cbn [eval].
    destruct Hag1 as (Hv & _ & _). rewrite <- (Hv 100%positive ltac:(cbv; reflexivity)).
    change (32 mod M64v) with 32. rewrite Z.mod_small; [reflexivity|]. unfold M64v. lia.
Qed.

Lemma ex_TR : ltac2:(tb__ "0|1|
S2fS0S0S5S5S2eS5bQ40M0A1A1S5eS0R5S64A3S38S27S75R7S2dS0S0R6R5A4A2S31A3S3dZ0R6A2ScS52R6R5A3S38S0S3fS3fS5aG0S8R6PeA2A2R9A2S5aG0S8R6P64A2A2A2S3eZ20R8A2A3VTR;S5cS59VJ;S63S66RaA1A1R7R6A5S5dS59VJ;S52R8R6S6bA6A2F_;F_;F_;F_;F_;Ftp;Frho;Frho0;Fr;Fu;FfuelX;").
Proof using Hst TR_pre TR_run TR_facts TR_refl.
  intros fuelX u r rho0 rho tp Hu C Hr Hag0 HR. pose proof (u_range_bound u Hu) as Hub. unfold ex_okb in C.
  destruct (guard fuelX (merge_objs_at (CZ u) 1)) as [Sm|] eqn:MG1; [|discriminate C]. apply guard_Some in MG1.
  apply andb_prop in C as [C RN]. apply andb_prop in C as [WF DF]. apply andb_prop in WF as [NXM WF]. apply Pos.eqb_eq in NXM.
  destruct (state_diff Sm (CZX u r)) as [[d [|]]|] eqn:SD; try discriminate DF.
  destruct (run1 fuelX [] (liftA (CZX u r))) as [L|] eqn:RUN; [|discriminate RN].
  apply andb_prop in RN as [C1 RN]. apply andb_prop in C1 as [RET NX].
  destruct (zfold_at (ax_S (la_state L)) 1) as [S2|] eqn:ZF; [|discriminate RN].
  destruct (merge_objs_at S2 0) as [S3|] eqn:MG; [|discriminate RN].
  apply andb_prop in RN as [EN ID].
  apply TR_facts. intros HF. cbn [ax_S liftA mkA ss_facts CZ] in HF. destruct (factsCZ_num u rho HF) as (B1 & B2 & B3).
  pose proof (urange (rw rho 100)) as H100. unfold two62 in B1.

  apply (TR_pre (SPA segs J (liftA (CZX u r)) rho tp)).
  { intros w HS.
    pose proof (SPA_merge segs J rho (liftA (CZ u)) 1 Sm tp w MG1 HS) as HS1.
    change (liftA (CZX u r)) with (ax_setS (ax_setS (liftA (CZ u)) Sm) (CZX u r)).
    apply (SPA_restate segs J rho (ax_setS (liftA (CZ u)) Sm) (CZX u r) tp w d [] WF SD); [ | | constructor | exact HS1].
    -
      cbn [ax_S ax_setS]. rewrite NXM. reflexivity.
    - unfold diffs_ok. apply Forall_forall. intros [a b] Hin.
      pose proof (proj1 (forallb_forall _ _) DF _ Hin) as X. unfold pair_inb, xdiffs in X. cbn [existsb fst snd] in X.
      assert (E3 : eval rho zvC = eval rho (eX u r)).
      { apply bv_eq. unfold eX, addl, zvC, zvN. rewrite U_add, U_lit. cbn [eval]. rewrite add_neg_lit; unfold M64v in *; lia. }
      rewrite !Bool.orb_false_r in X.
      apply Bool.orb_prop in X as [X|X]; [|apply Bool.orb_prop in X as [X|X]];
        apply andb_prop in X as [X1 X2]; apply sv_eqb_sound in X1; apply sv_eqb_sound in X2; subst a b; cbn [fst snd].
      + cbn [eval]. rewrite E3. reflexivity.
      + apply bv_eq. unfold remC, addl, zvN, zvC. rewrite U_sub, U_add, !U_lit. cbn [eval].
        rewrite (add_neg_lit (U rho 14) u) by (unfold M64v in *; lia). rewrite !Z.mod_small; unfold M64v in *; lia.
      + exact E3. }
  apply (run1_TR fuelX [] (liftA (CZX u r)) L rho tp _ RUN eq_refl ltac:(apply Pos.leb_le; reflexivity)).
  intros rho1 Hag1. cbn [ax_S liftA mkA ss_next CZX] in Hag1.
  destruct (zfold_at_spec _ 1 S2 ZF) as (o & Ho & Hz & ->).
  set (s := infer_sub NF S3 P_msz) in *.
  apply (TR_pre (SPA segs J (liftA P_msz) (rho_sub rho1 s) tp)).
  { intros w HS.
    pose proof (SPA_zero_fold segs J rho1 (la_state L) tp w 1 o Ho Hz HS) as HS2.
    pose proof (SPA_merge segs J rho1 (ax_setS (la_state L) (set_objs (ax_S (la_state L)) (list_set (ss_objs (ax_S (la_state L))) 1 (zobj o)))) 0 S3 tp w MG HS2) as HS3.
    exact (SPA_entails segs J NF _ _ s rho1 tp w EN ID Hst HS3). }
  apply TR_post. eapply agree_below_trans; [exact Hag0|].
  eapply agree_below_trans; [eapply agree_below_le; [|exact Hag1]; apply Pos.leb_le; reflexivity | apply rho_sub_agree; exact ID].
Qed.

Lemma loop_TR : ltac2:(tb__ "0|1|
S2fS2fS0S5eS0R1S64A3S38S27S7aR4R2A2S31A3S0S5eS0R1S7cA3S38S27S75R6S2dS0S0R5R2A4A2S31A3F_;Fr;S2fS0S5S5S2eS5bQ40M0A1A1S3dZ0R4A2S45R5S43Z8S44R6A1A2A2ScS52R5R4A3S38S0S3fS3fS5aG0S8R5PeA2A2RcA2S5aG0S8R5P64A2A2A2S3eZ20S43Z4R7A2A2A3VTR;S5cS59VJ;S63S66RdA1A1R6R5A5S5dS59VJ;S52R7R5S6bA6A2F_;F_;F_;F_;Ftp;Frho;Frho0;Fm;Fc;F_;F_;F_;Fu;FfuelX;FfuelI;").
Proof using Hst TR_pre TR_run TR_facts TR_refl.
  intros fuelI fuelX u Hu HIu HXu c. induction c as [|c IH]; intros m rho0 rho tp Hm Hc Hag HR; [lia|].
  pose proof (u_range_bound u Hu) as Hub.
  destruct (Z.le_gt_cases 8 m) as [Hbig|Hsmall].
  - apply (it_TR fuelI u rho tp _ Hu HIu); [lia|]. intros rho' Hag' H100.
    assert (E14 : U rho' 14 = U rho 14) by (destruct Hag' as (Hv & _ & _); rewrite <- (Hv 14%positive ltac:(cbv; reflexivity)); reflexivity).
    apply (IH (m - 8) rho0 rho' tp); [lia | lia | eapply agree_below_trans; [exact Hag | exact Hag'] | rewrite E14, H100; lia].
  - apply (ex_TR fuelX u (4 * m) rho0 rho tp Hu); [apply HXu; apply in_r_range; lia | lia | exact Hag | lia].
Qed.

Lemma en_TR : ltac2:(tb__ "0|7|
S2fS5S2eS5bQ40M0A1A1Sa2S0S0S0S39S3dZ0M1R3A2S3dR3Z3A2A2M2G2S3aS38S0R3G1A3S38S0R3Z4M3A3A2S38S27S87RaS2dS29S0S0A2S0S2dS0S0R6R5A4R4A4A2S31A3F_;F_;F_;Ft4;Fu;Fk;S3dS81S5aG0S8R4PeM4A2A2M5A2S0S5S5eS0R2S64A3ScS52R8R2A3S38S0S41S3fS3fS5aG0S8R3G4A2A2R4A2S5aG0S8R3P64M6A2A2A2G3A2G1A3S3dZ20S3fS3fG5R5A2S5aG0S8R4G6A2A2A2A2VTR;S5cS59VJ;S63S66R6A1A1R5RaA5R9A2F_;F_;F_;F_;Frho';Fu;VTR;S5cS59VJ;S72R6R5A5R4A2F_;F_;F_;FQ;Ftp;Frho;FfuelE;").
Proof using Hst TR_pre TR_run TR_facts.
  intros fuelE rho tp Q HEf Hn HK. pose proof (urange (rw rho 14)) as Hr.
  apply TR_facts. intros HF0. cbn [ax_S Pre_mszA liftA mkA ss_facts Pre_msz] in HF0.
  assert (B62 : U rho 14 <= two62).
  { apply Forall_cons_iff in HF0 as [H1 _]. cbn [holds eval N14] in H1. rewrite lit_unsigned in H1. change (two62 mod 2 ^ 64) with two62 in H1. exact H1. }
  unfold two62 in B62.

  pose proof (HEf 0 0 0 ltac:(lia) ltac:(lia) ltac:(lia)) as C0. unfold en_okb in C0.
  destruct (guard fuelE (split_obj_at (ax_S Pre_big) 0 eT)) as [S0|] eqn:SP0; [|discriminate C0].
  pose proof (guard_Some _ _ _ SP0) as SP0'.
  apply andb_prop in C0 as [NS0 C0]. apply andb_prop in NS0 as [NXT0 LEN0]. apply Pos.eqb_eq in NXT0.
  assert (LEN0' : ss_lenient S0 = false) by (destruct (ss_lenient S0); [discriminate LEN0 | reflexivity]). clear LEN0. rename LEN0' into LEN0.
  destruct (run1 fuelE [PC_K] (ax_setS Pre_big S0)) as [L1|] eqn:RUN1; [|discriminate C0].
  apply andb_prop in C0 as [C0 _]. apply andb_prop in C0 as [CUT1 _]. destruct (is_cut_sound L1 PC_K CUT1) as (_ & Hl1 & Hn1).

  apply (TR_pre (SPA segs J (ax_setS Pre_big S0) rho tp)).
  { intros w HS. apply (SPA_split segs J rho Pre_big 0 eT S0 tp w SP0').
    unfold Pre_big. apply (SPA_refacts segs J rho Pre_mszA factsN tp w HS ltac:(reflexivity)).
    intros HF. constructor; [apply Forall_cons_iff in HF as [H1 _]; exact H1|]. constructor; [|constructor].
    cbn [holds eval zvN]. rewrite lit_unsigned. change (L2_MIN mod 2 ^ 64) with L2_MIN. exact Hn. }
  apply (run1_TR fuelE [PC_K] (ax_setS Pre_big S0) L1 rho tp Q RUN1 LEN0 ltac:(cbn [ax_S ax_setS]; rewrite NXT0; apply Pos.le_refl)).
  intros rho1 Hag1. cbn [ax_S ax_setS] in Hag1. rewrite NXT0 in Hag1.
  assert (E14a : U rho1 14 = U rho 14) by (destruct Hag1 as (Hv & _ & _); rewrite <- (Hv 14%positive ltac:(cbv; reflexivity)); reflexivity).

  set (k := bv_unsigned (eval rho1 KX)). pose proof (U_KX_range rho1) as Hk. fold k in Hk.
  set (u := (U rho 14 - k) mod 4). pose proof (Z.mod_pos_bound (U rho 14 - k) 4 ltac:(lia)) as Hu. fold u in Hu.
  pose proof (HEf k u 0 ltac:(lia) ltac:(lia) ltac:(lia)) as C1. unfold en_okb in C1.
  rewrite SP0, RUN1 in C1. apply andb_prop in C1 as [_ C1]. apply andb_prop in C1 as [C1a C1]. apply andb_prop in C1a as [_ RS1].
  apply (TR_pre (SPA segs J (setreg (la_state L1) 13 (SLit k)) rho1 tp)).
  { intros w HS. apply (SPA_setreg (la_state L1) 13 KX (SLit k) rho1 tp w RS1); [|exact HS]. cbn [eval]. apply bv_eq. rewrite Z_to_bv_unsigned. subst k.
    pose proof (urange (eval rho1 KX)). rewrite bv_wrap_small; [reflexivity | rewrite two64; lia]. }
  destruct (run1 fuelE [PC_N] (setreg (la_state L1) 13 (SLit k))) as [L2|] eqn:RUN2; [|discriminate C1].
  destruct (restate_keeps (la_state L1) 13 (SLit k)) as [Kn1 Kl1].
  apply (run1_TR fuelE [PC_N] _ L2 rho1 tp _ RUN2 ltac:(rewrite Kl1; exact Hl1) ltac:(rewrite Kn1; exact Hn1)).
  intros rho2 Hag2. rewrite Kn1 in Hag2.
  assert (Hag02 : agree_below NF rho rho2) by (eapply agree_below_trans; [exact Hag1 | eapply agree_below_le; [exact Hn1 | exact Hag2]]).
  assert (E14b : U rho2 14 = U rho 14) by (destruct Hag02 as (Hv & _ & _); rewrite <- (Hv 14%positive ltac:(cbv; reflexivity)); reflexivity).
  apply andb_prop in C1 as [C1a C1]. apply andb_prop in C1a as [CUT2 RS2]. destruct (is_cut_sound L2 PC_N CUT2) as (_ & Hl2 & Hn2).
  apply (TR_pre (SPA segs J (setreg (la_state L2) 14 (NAk k u)) rho2 tp)).
  { intros w HS. apply (SPA_setreg (la_state L2) 14 (NXk k) (NAk k u) rho2 tp w RS2); [|exact HS].
    subst u. rewrite <- E14b. apply U_NX; [lia|]. rewrite E14b. unfold L2_MIN in Hn. lia. }
  destruct (run1 fuelE [PC_T] (setreg (la_state L2) 14 (NAk k u))) as [L3|] eqn:RUN3; [|discriminate C1].
  destruct (restate_keeps (la_state L2) 14 (NAk k u)) as [Kn2 Kl2].
  apply (run1_TR fuelE [PC_T] _ L3 rho2 tp _ RUN3 ltac:(rewrite Kl2; exact Hl2) ltac:(rewrite Kn2; exact Hn2)).
  intros rho3 Hag3. rewrite Kn2 in Hag3.
  assert (Hag03 : agree_below NF rho rho3) by (eapply agree_below_trans; [exact Hag02 | eapply agree_below_le; [exact Hn2 | exact Hag3]]).
  apply andb_prop in C1 as [C1a _]. apply andb_prop in C1a as [CUT3 _]. destruct (is_cut_sound L3 PC_T CUT3) as (_ & Hl3 & Hn3).

  set (t4 := bv_unsigned (eval rho3 (T4X k))). pose proof (U_T4X_cases rho3 k) as Ht. fold t4 in Ht.
  pose proof (HEf k u t4 ltac:(lia) ltac:(lia) ltac:(lia)) as C2. unfold en_okb in C2.
  rewrite SP0, RUN1, RUN2, RUN3 in C2.
  apply andb_prop in C2 as [_ C2]. apply andb_prop in C2 as [_ C2]. apply andb_prop in C2 as [_ C2]. apply andb_prop in C2 as [C2a C2]. apply andb_prop in C2a as [_ RS3].
  apply (TR_pre (SPA segs J (setreg (la_state L3) 15 (SLit t4)) rho3 tp)).
  { intros w HS. apply (SPA_setreg (la_state L3) 15 (T4X k) (SLit t4) rho3 tp w RS3); [|exact HS]. cbn [eval]. apply bv_eq. rewrite Z_to_bv_unsigned. subst t4.
    pose proof (urange (eval rho3 (T4X k))). rewrite bv_wrap_small; [reflexivity | rewrite two64; lia]. }
  destruct (run1 fuelE [ZBODY] (setreg (la_state L3) 15 (SLit t4))) as [L4|] eqn:RUN4; [|discriminate C2].
  destruct (restate_keeps (la_state L3) 15 (SLit t4)) as [Kn3 Kl3].
  apply (run1_TR fuelE [ZBODY] _ L4 rho3 tp _ RUN4 ltac:(rewrite Kl3; exact Hl3) ltac:(rewrite Kn3; exact Hn3)).
  intros rho4 Hag4. rewrite Kn3 in Hag4.
  assert (Hag04 : agree_below NF rho rho4) by (eapply agree_below_trans; [exact Hag03 | eapply agree_below_le; [exact Hn3 | exact Hag4]]).
  apply andb_prop in C2 as [CUT4 C2]. destruct (is_cut_sound L4 ZBODY CUT4) as (_ & Hl4 & Hn4).
  destruct (run1 fuelE [ZBODY] (la_state L4)) as [L5|] eqn:RUN5; [|discriminate C2].
  apply (run1_TR fuelE [ZBODY] _ L5 rho4 tp _ RUN5 Hl4 Hn4).
  intros rho5 Hag5.
  assert (Hag05 : agree_below NF rho rho5) by (eapply agree_below_trans; [exact Hag04 | eapply agree_below_le; [exact Hn4 | exact Hag5]]).
  apply andb_prop in C2 as [C2a C2]. apply andb_prop in C2a as [CUT5 NX5].
  destruct (split_obj_at (ax_S (la_state L5)) 0 (SLit (k + 56 + t4))) as [S5|] eqn:SP5; [|discriminate C2].
  destruct (zfold_at S5 0) as [S6|] eqn:ZF; [|discriminate C2].
  destruct (zfold_at_spec S5 0 S6 ZF) as (o & Ho & Hz & ->).
  apply (TR_pre (SPA segs J (liftA (CZ u)) (rho_sub rho5 (s_en k t4)) tp)).
  { intros w HS.
    pose proof (SPA_split segs J rho5 (la_state L5) 0 _ S5 tp w SP5 HS) as HS1.
    pose proof (SPA_zero_fold segs J rho5 (ax_setS (la_state L5) S5) tp w 0 o Ho Hz HS1) as HS2.
    exact (SPA_entails segs J NF _ _ (s_en k t4) rho5 tp w C2 (s_en_id k t4) Hst HS2). }
  assert (E14c : U (rho_sub rho5 (s_en k t4)) 14 = U rho 14).
  { rewrite rw_rho_sub. cbn [wsub_get s_en Pos.eqb eval]. destruct Hag05 as (Hv & _ & _). rewrite <- (Hv 14%positive ltac:(cbv; reflexivity)). reflexivity. }
  assert (E100 : U (rho_sub rho5 (s_en k t4)) 100 = k + 56 + t4).
  { rewrite rw_rho_sub. cbn [wsub_get s_en Pos.eqb eval]. rewrite lit_unsigned. apply Z.mod_small. lia. }
  apply (HK u); [apply in_u_range; lia | | |].
  - eapply agree_below_trans; [exact Hag05 | apply rho_sub_agree; apply s_en_id].
  - rewrite E14c, E100. subst u. apply mod4_entry. exact Ht.
  - rewrite E14c, E100. unfold L2_MIN in Hn. lia.
Qed.

Theorem memsetZ_TR : ltac2:(tb__ "0|2|
S2fS2fS2fS2fS29S29S0S0A2M0S0A2M1S5eG1R1S89A3S38S27S7bR6R2A2S31A3F_;Fc;S0S5eS0R1S64A3S38S27S7aR6R2A2S31A3F_;Fu;G0S5eG0R1S8bA3S38S27S75R6R2A2S31A3F_;Fur;G1S5eG1R1S88A3S38S27S87R6R2A2S31A3F_;Fc;S5S2eS5bQ40A1A1VTR;S5cS59VJ;S72R2R1A5S5dS59VJ;S52R2R1S6bA6A2Ftp;Frho;F_;F_;F_;F_;FfuelE;FfuelX;FfuelI;FfuelL;").
Proof using Hst TR_pre TR_run TR_facts TR_refl.
  intros fuelL fuelI fuelX fuelE HL HI HX HE rho tp.
  destruct (Z.le_gt_cases (U rho 14) L1_MAX) as [Hs|Hb].
  { apply (memsetZ_small fuelL). intros k t4 Hk Ht. apply HL. apply lit_range_in; [pose proof (urange (rw rho 14)); lia | exact Hk | exact Ht]. }
  apply (en_TR fuelE); [intros k u t4 Hk Hu Ht; apply HE; apply in_kut_range; [exact Hk | exact Hu | exact Ht] | unfold L1_MAX, L2_MIN in *; lia|].
  intros u rho' Hu Hag Hmod Hge.
  pose proof (Z_div_mod_eq_full (U rho' 14 - u - U rho' 100 - 32) 4) as Hdm.
  pose proof (Z.mod_pos_bound (U rho' 14 - u - U rho' 100 - 32) 4 ltac:(lia)) as Hmb.
  set (m := (U rho' 14 - u - U rho' 100 - 32) / 4) in *.
  assert (Hm4 : (U rho' 14 - u - U rho' 100 - 32) mod 4 = 0).
  { rewrite Zminus_mod, Hmod. reflexivity. }
  apply (loop_TR fuelI fuelX u Hu (HI u Hu) ltac:(intros r Hr; apply HX; apply in_ur_range; [exact Hu | exact Hr]) (S (Z.to_nat m)) m rho rho' tp);
    [lia | rewrite Nat2Z.inj_succ, Z2Nat.id by lia; lia | exact Hag | lia].
Qed.
End Sound.

Section Inst.
Variable ok : assn.
Variable J : jpredA.
Hypothesis Hok : ok_frameA segs ok J.
Hypothesis Hst : stableA segs NF J.

Theorem memsetZ_sumA : ltac2:(tb__ "0|0|
S5S2eS5bQ40A1A1Sa5S59Vok;S5cS59VJ;S72R2R1A5S5dS59VJ;S52R2R1S6bA6A4Ftp;Frho;").
Proof.
  eapply (memsetZ_TR J Hst (triple segs ok)).
  - intros P P' Q HP HT. eapply triple_conseq; [exact HP | intros w Hw; exact Hw | exact HT].
  - intros fuel cuts A leaves rho tp Q Hrun Hl Hn HQ. eapply (runA_tr segs ok fuel cuts A leaves J rho tp Q Hrun Hl Hok (stableA_mono segs _ _ _ Hn Hst)). exact HQ.
  - apply triple_refl.
  - intros A rho tp Q H. apply triple_factsA. exact H.
  - exact (proj1 (forallb_forall _ _) lit_allb).
  - exact (proj1 (forallb_forall _ _) it_allb).
  - exact (proj1 (forallb_forall _ _) ex_allb).
  - exact (proj1 (forallb_forall _ _) en_allb).
Qed.
End Inst.

Section InstEx.
Variable J : jpredA.
Hypothesis Hst : stableA segs NF J.
Theorem memsetZ_sumA_ex : ltac2:(tb__ "0|0|
S5S2eS5bQ40A1A1Sa4S59S5cS59VJ;S72R2R1A5S5dS59VJ;S52R2R1S6bA6A3Ftp;Frho;").
Proof.
  eapply (memsetZ_TR J Hst (etriple segs)).
  - intros P P' Q HP HT. eapply etriple_conseq; [exact HP | intros w Hw; exact Hw | exact HT].
  - intros fuel cuts A leaves rho tp Q Hrun Hl Hn HQ. eapply (erunA_tr segs fuel cuts A leaves J rho tp Q Hrun Hl (stableA_mono segs _ _ _ Hn Hst)). exact HQ.
  - apply etriple_refl.
  - intros A rho tp Q H. apply etriple_factsA. exact H.
  - exact (proj1 (forallb_forall _ _) lit_allb).
  - exact (proj1 (forallb_forall _ _) it_allb).
  - exact (proj1 (forallb_forall _ _) ex_allb).
  - exact (proj1 (forallb_forall _ _) en_allb).
Qed.
End InstEx.
End Str_memsetZ.

(* [comment removed for export] *)
Module StartGlueB.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "cell"; "valuation"; "sobj"; "mkObj"; "eval"; "obj_holds"; "odefault"; "SLit"; "mkCell"; "ob_dflt"; "sprop"; "ss_next"; "DUnknown"; "holds"; "rd"; "ss_objs"; "agree_below"; "cell_holds"; "oaddr"; "ob_base"; "ob_cells"; "ob_hi"; "ob_lo"; "rd_bytes"; "ss_facts"; "sstate"; "swf"; "@Corelib.Init.Logic"; "eq"; "and"; "ex"; "not"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Datatypes"; "list"; "Some"; "option"; "nat"; "bool"; "cons"; "length"; "true"; "app"; "nil"; "prod"; "pair"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "ax_setS"; "axst"; "@Stdlib.ZArith.BinInt.Z"; "modulo"; "add"; "le"; "of_nat"; "lt"; "opp"; "pow"; "mul"; "shiftr"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "@Stdlib.Lists.List"; "nth_error"; "filter"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartDefsA"; "replace_obj_at"; "@Corelib.Lists.ListDef"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.na.StartGlueB"; "byte_cells"; "drop_cells"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "same_but_objs"; "diffs_ok"; "state_diff"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n5.StartGlueA"; "bump_next"; "@Stdlib.PArith.BinPos.Pos"; "le"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ImageFacts KxA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n1.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.KxA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.StartNodes.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import StartDefsA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n5.StartGlueA.
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
Module StartGlueD.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SLit"; "mkCell"; "sobj"; "cell"; "ob_cells"; "obj_holds"; "rd_bytes"; "valuation"; "ss_objs"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "pow"; "lt"; "mul"; "of_nat"; "modulo"; "opp"; "shiftr"; "@Corelib.Init.Datatypes"; "nat"; "Some"; "list"; "bool"; "option"; "true"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts"; "segsA"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartDefsA"; "add_cell_front"; "replace_obj_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.na.StartGlueD"; "subcell_val"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "ax_setS"; "axst"; "cell_eqb"; "@Corelib.Init.Nat"; "add"; "@Corelib.Init.Peano"; "le"; "@Corelib.Lists.ListDef"; "firstn"; "skipn"; "@LinuxProcessSemantics.LinuxProcessSem.BvBase"; "Z_to_le_bytes"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "same_but_objs"; "@Stdlib.Lists.List"; "In"; "existsb"; "nth_error"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ImageFacts KxA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n1.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.KxA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n8.StartALib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.StartNodes.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import StartDefsA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n5.StartGlueA.
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

(* [comment removed for export] *)
Module StartNodes3E.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "ex"; "and"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "ax_base"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SLit"; "reg_sv"; "valuation"; "ss_next"; "eval"; "rw"; "agree_below"; "rm"; "ss_pc"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts"; "segsA"; "@Corelib.Init.Datatypes"; "prod"; "list"; "pair"; "Some"; "app"; "bool"; "option"; "true"; "@Corelib.Numbers.BinNums"; "Z"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "m_vmmaps"; "vm_maps"; "vm_reserved"; "Model"; "vm_init_sp"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec"; "mmap_place_ok_none"; "mmap_place_ok"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "@LinuxProcessSemantics.Riscv.Instr"; "instr"; "Ecall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.KxA"; "KxA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@Stdlib.Lists.List"; "In"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "segments_reserved"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Placement"; "SHADOW_BAND_HI"; "SHADOW_BAND_LO"; "band_covered"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n8.StartALib"; "SHB"; "objs_clear_e"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.StartNodes"; "LB_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n5.StartNodes3"; "null_rw_model"; "null_rw_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysStep"; "unmap_range"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "set_rm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "instr_at"; "@Stdlib.PArith.BinPos.Pos"; "lt"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import Logic.FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uapi.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymCall Glue3 SymHeap.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt LedgerA StepA SoundA EntailA CompleteA GlueA SysCallA MmapA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import ImageFacts StartLib KxA Placement.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import SysSpecStart.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n8.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n8.StartALib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import SysStartA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.StartNodes OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n5.StartNodes3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section LazyNullRwE.

Variables (E : axst) (lenZ : Z) (m : Model) (B : Z) (Gl : list (sv * Z)) (nxt : positive).
Let n : word := Z_to_bv 64 lenZ.
Local Notation null_rw_model := (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n5.StartNodes3.null_rw_model lenZ) (only parsing).
Local Notation null_rw_h := (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n5.StartNodes3.null_rw_h lenZ) (only parsing).
Local Notation null_rw_facts := (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n5.StartNodes3.null_rw_facts E lenZ) (only parsing).
Local Notation null_rw_ok := (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n5.StartNodes3.null_rw_ok E lenZ nxt) (only parsing).

Hypothesis HX : ax_X E = [].
Hypothesis Hbase : ltac2:(tb__ "0|0|
S0S6S5VE;A1S7S2fA1A3").
Hypothesis Hecall : ltac2:(tb__ "0|0|
S0S1aS26A1S38S13SfS4VE;A1A1A2S17S26S27A2A3").
Hypothesis R17 : ltac2:(tb__ "0|0|
S0S6S8S4VE;A1Z11A2S7ZdeA1A3").
Hypothesis R10 : ltac2:(tb__ "0|0|
S0S6S8S4VE;A1ZaA2S7Z0A1A3").
Hypothesis R11 : ltac2:(tb__ "0|0|
S0S6S8S4VE;A1ZbA2S7VlenZ;A1A3").
Hypothesis R12 : ltac2:(tb__ "0|0|
S0S6S8S4VE;A1ZcA2S7Z3A1A3").
Hypothesis R13 : ltac2:(tb__ "0|0|
S0S6S8S4VE;A1ZdA2S7Z4022A1A3").
Hypothesis R14 : ltac2:(tb__ "0|0|
S0S6S8S4VE;A1ZeA2S7ZffffffffffffffffA1A3").
Hypothesis R15 : ltac2:(tb__ "0|0|
S0S6S8S4VE;A1ZfA2S7Z0A1A3").
Hypothesis Hnl : lenZ mod 4096 = 0.
Hypothesis Hpos : 0 < lenZ.
Hypothesis Hsmall : lenZ < 2 ^ 62.
Hypothesis Hnxt : ltac2:(tb__ "0|0|
S39SaS4VE;A1A1Vnxt;A2").
Hypothesis Hclear : ltac2:(tb__ "0|0|
S0S19S30VGl;S4VE;A1A2S1bA3").
Hypothesis Hres : ltac2:(tb__ "0|1|
S0S15S14S10Q40A1M0G0A2A1S1fS1dVm;A1A1S2bS13A1A3").
Hypothesis Htop : init_sp_ok (m_vmmaps m).
Hypothesis Hband : ltac2:(tb__ "0|2|
S2eS18S14S10Q40A1M0G0A2S1fS1dVm;A1M1A1S1eG1A1A3S2dS2cA3").

Variable rho_of : ltac2:(tb__ "0|0|
S9S10Q40A1S9F_;F_;").
Hypothesis Hrho_ag : ltac2:(tb__ "0|0|
S9S10Q40A1SdSaS4VE;A1A1S37R2S36SeR2A1R1Vn;A3A2Vrho_of;R2R1A2A3Fa;Frho;").
Hypothesis Hrho_at : ltac2:(tb__ "0|1|
S9S10Q40A1M0S0G0ScVrho_of;R2R1A2SaS4VE;A1A1A2R1A3Fa;Frho;").

Lemma n_valW : bv_unsigned n = lenZ.
Proof using Hpos Hsmall. unfold n. apply u64_of_lit. clear -Hpos Hsmall. lia. Qed.

Lemma place_ok_none_of : ltac2:(tb__ "0|3|
S10Q40M0A1M1S20G1G1S23S12G0Z0A2M2R4R3R2R1A5S22G2R4R3R2A4F_;Fa;Flen;Fmd;Fflags;").
Proof. intros flags md len a (P1 & P2 & P3 & P4 & _). unfold mmap_place_ok_none. repeat split; assumption. Qed.

Hypothesis Hwit : ltac2:(tb__ "0|2|
S1S10Q40M0A1M1G1S22S12G0Z0A2Vm;Vn;R1A4La;A2").

Theorem lazy_null_rw_enode : ltac2:(tb__ "0|5|
S9S15S10Q40M0A1M1A1S6S1cS2aS14S6S1cA2S16S6S1cR2R1A4VGl;A3S3S1G1G1S1G1G1S2S2aS14G1G1A2S16G1G1R2R1A4S1eS1dVm;A1M2A1A3S2S25S11G0R2A2M3S11G0SbR7R5A2A2M4A2S25S24G4R4A2S24G3S11G0R1A2A2A2A2A2Ls;A2Lb;A2S25S24S11G0SbR5R3A2A2R2A2S31VlenZ;A1A2A2F_;Fsz;Fe;S0S1cS11G0ScR3P1A2A2S11G0S21G2A1A2A3S34S13S29S13S28Vm;VB;A2VE;R4R3A5S35S1G1G1S2S22S12G0Z0A2Vm;Vn;R1A4S29S13S28S32VlenZ;Vm;R1A3VB;A2S33VE;VlenZ;Vnxt;A3Vrho_of;R6R1A2R5R2A6A2La;A2Lw;A3F_;F_;Ftp;Frho;").
Proof using All.
  intros rho tp HG Hv1.
  pose proof n_valW as Nv. pose proof (alloc_top_lt (m_vmmaps m)) as CL.
  apply etriple_ecall_detA; [apply stableA_KxA | exact Hecall |].
  intros tr ms md Hsp (Htr & Hem & Hpaid). subst tr.
  pose proof (erase_mat_eq_fields md m Hem) as (Evm & Elz & Efds & Ehalt & Etid & Efs & Estdin).
  pose proof (smatch_pendingA_pending segsA _ _ _ _ _ _ Hsp) as Hp. rewrite R17 in Hp. cbn [eval] in Hp.
  pose proof (smatch_pendingA_halted segsA _ _ _ _ _ _ Hsp) as Hh.
  pose proof (smatch_pendingA_MI segsA _ _ _ _ _ _ Hsp) as HMI.
  pose proof (smatch_pendingA_swf segsA _ _ _ _ Hsp) as Hswf.
  destruct (pending_argsA segsA rho tp E [] ms md Hsp) as (G0 & G1 & G2 & G3 & G4 & G5).
  rewrite R10 in G0. rewrite R11 in G1. rewrite R12 in G2. rewrite R13 in G3. rewrite R14 in G4. rewrite R15 in G5.
  cbn [eval] in G0, G1, G2, G3, G4, G5. fold n in G1.
  assert (H222 : bv_unsigned (Z_to_bv 64 222) = 222%Z) by reflexivity.
  assert (Hlen : ms_gpr ms 1 <> Z_to_bv 64 0).
  { rewrite G1. intros X. apply (f_equal bv_unsigned) in X. rewrite Nv in X. change (bv_unsigned (Z_to_bv 64 0)) with 0 in X. lia. }
  assert (Hshape : mmap_modeled_b (ms_gpr ms 2) (ms_gpr ms 3) (ms_gpr ms 5) = true).
  { apply mmap_modeled_b_intro_core; [rewrite G2; reflexivity | rewrite G3; apply mmap_flags_core_16418; reflexivity | rewrite G5; reflexivity]. }
  assert (HnZ' : mmap_nZ (ms_gpr ms 1) = lenZ).
  { rewrite G1. unfold mmap_nZ, page_round_up_Z, page_size. rewrite Nv.
    pose proof Hnl as Hnl'. apply Z.mod_divide in Hnl' as [q Hq]; [|lia]. rewrite Hq.
    replace (q * 4096 + 4096 - 1) with (4095 + q * 4096) by lia. rewrite Z.div_add by lia. change (4095 / 4096) with 0. lia. }
  assert (HnZ : mmap_n (ms_gpr ms 1) = n) by (unfold mmap_n; rewrite HnZ'; reflexivity).
  destruct Hwit as [a Hwa].
  assert (Hpl : mmap_place_ok (ms_gpr ms 0) (ms_gpr ms 3) md (ms_gpr ms 1) a).
  { rewrite G0, G1. destruct Hwa as (W1 & W2 & W3 & W4). unfold mmap_place_ok. rewrite Evm.
    split; [exact W1|]. split; [exact W2|]. split; [exact W3|]. split; [exact W4|].
    unfold mmap_noreserve_backed_ok. rewrite G3, (mmap_noreserve_b_16418 (Z_to_bv 64 16418) eq_refl). reflexivity. }
  exists ([], mkCfg (after_sys_mem ms a (zero_range (ms_mem ms) a (mmap_n (ms_gpr ms 1)))) (mmap_rw_model (ms_gpr ms 3) md (ms_gpr ms 1) a)).
  split; [exact (wstep_mmap_intro_okA segsA ms md _ Hh H222 Hlen Hshape [] a Hp Hpl)|].
  exists a.
  rewrite G0, G1 in Hpl.
  assert (HnZn : mmap_nZ n = lenZ) by (rewrite <- G1; exact HnZ').
  assert (Hmn : mmap_n n = n) by (rewrite <- G1 at 1; exact HnZ).
  assert (Hplm : mmap_place_ok_none (Z_to_bv 64 0) m n a).
  { apply (place_ok_none_of (ms_gpr ms 3) m n a). unfold mmap_place_ok in Hpl |- *. rewrite Evm in Hpl.
    destruct Hpl as (P1 & P2 & P3 & P4 & P5). repeat split; try assumption.
    unfold mmap_noreserve_backed_ok in P5 |- *. rewrite G3 in P5 |- *. rewrite (mmap_noreserve_b_16418 (Z_to_bv 64 16418) eq_refl) in P5 |- *. exact P5. }
  split; [exact Hplm|].
  pose proof Hplm as (Pal & Ppos & Pceil & Pfree). rewrite HnZn in Pceil. rewrite Hmn in Pfree.
  pose proof (place_LB_A m lenZ a Htop Hres Hband ltac:(lia) Hnl Hplm) as (PLB & Pimg & Pband & Ptop & Phi).
  assert (Hfree_m : region_free (vm_maps (m_vmmaps md)) a n = true) by (rewrite Evm; exact (region_free_app_r _ _ _ _ Pfree)).
  assert (Enr : mmap_noreserve_b (ms_gpr ms 3) = true) by (rewrite G3; apply mmap_noreserve_b_16418; reflexivity).
  unfold mmap_rw_model, mmap_rw_vm, with_mmap_backing. rewrite Enr, HnZ.
  set (rho' := rho_of rho a).
  split.
  * unfold null_rw_ok.
    assert (SM : smatchA segsA rho' tp (ax_setS E (S_after (ax_S E) (SVar (ss_next (ax_S E))) (ss_objs (ax_S E)) nxt))
                   ([], mkCfg (after_sys_mem ms a (zero_range (ms_mem ms) a n)) (vm_add_lazy a n (with_vmmaps (null_rw_h md a) md)))).
    { eapply (smatchA_after_grant_lazy segsA rho rho' tp E [] ms md [] (null_rw_h md a)); try exact Hsp.
      -- reflexivity.
      -- reflexivity.
      -- reflexivity.
      -- exact Pal.
      -- rewrite Nv. exact Hnl.
      -- rewrite Nv. exact Hpos.
      -- rewrite Nv. unfold two_pow_64 in CL. lia.
      -- exact Hfree_m.
      -- intros z Hz. apply find_segment_none_A. rewrite Nv in Hz. lia.
      -- intros o Ho. rewrite Nv.
         apply (objs_clear_e_sound rho Gl (ax_S E) a lenZ (smatch_pending_facts segsA _ _ _ _ _ (smatch_pendingA_sp segsA _ _ _ _ _ _ Hsp)) Hclear).
         ++ lia.
         ++ right. revert Pceil. unfold alloc_top. rewrite stack_max_size_val, <- Hv1. intros Pceil. exact Pceil.
         ++ intros x Hx. lia.
         ++ intros e sz Hin x Hx Hblk. destruct (HG e sz Hin) as [(b & s0 & Hm & Hb1 & Hb2) | Hlow]; [|lia].
            pose proof (region_free_In _ _ _ _ _ Hfree_m ltac:(rewrite Evm; exact Hm)) as R.
            unfold iv_overlap in R. rewrite Nv in R.
            apply andb_false_iff in R. destruct R as [R|R]; apply Z.ltb_ge in R; lia.
         ++ exact Ho.
      -- rewrite HX. intros rr y [] _.
      -- subst rho'. apply Hrho_ag.
      -- lia.
      -- cbn. apply Pos.ltb_lt. exact Hnxt.
      -- subst rho'. cbn [eval]. apply Hrho_at. }

    replace E with (mkAX (ax_S E) [] (SLit SHB)) in SM by (destruct E as [S0 X0 b0]; cbn in HX, Hbase |- *; rewrite HX, Hbase; reflexivity).
    destruct SM as (Ssm & SMI & Swf & Ssh & Shz). cbn [ax_S ax_setS ax_X ax_base] in Ssm, Swf, Ssh.
    split; [|split; [exact SMI|split; [|split; [|exact Shz]]]].
    -- cbn [ax_S]. apply smatch_add_facts; [exact Ssm| |].
       ++ unfold null_rw_facts. assert (E1 : rw rho' (ss_next (ax_S E)) = a) by (subst rho'; apply Hrho_at).
          repeat apply Forall_cons; try apply Forall_nil; cbn [holds eval]; rewrite ?E1.
          ** change (2 ^ 12) with 4096. split; [lia|exact Pal].
          ** rewrite u64_of_lit by (pose proof (LB_of_range lenZ); lia). exact PLB.
          ** unfold alloc_ceiling_hi in *. rewrite u64_of_lit by lia. lia.
       ++ assert (X : (ss_next (ax_S E) <? nxt)%positive = true) by (apply Pos.ltb_lt; exact Hnxt). cbn. rewrite !X. reflexivity.
    -- unfold axwf in Swf |- *. cbn [ax_S ax_X ax_base ss_next add_facts] in Swf |- *. exact Swf.
    -- unfold shadow_ok. cbn. constructor.
  * assert (Hclr : tp_clear_of tp (lazy_interior a n)).
    { eapply (tp_clear_of_region_free md); [exact (MI_tp_in_maps segsA _ _ HMI) | exact (proj1 (MI_ivs_wf segsA _ _ HMI)) | exact Hfree_m |].
      rewrite Nv. unfold two_pow_64 in CL. lia. }
    assert (Hpaid' : paid (null_rw_model md a) tp <= B).
    { unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n5.StartNodes3.null_rw_model. change (Z_to_bv 64 lenZ) with n. rewrite (paid_add_lazy (with_vmmaps (null_rw_h md a) md) a n tp Hclr), paid_with_vmmaps.
      pose proof (used_rw_noreserve_le md (null_rw_h md a) a n (MI_ivs_wf segsA _ _ HMI)
                    Pal ltac:(rewrite Nv; exact Hnl) ltac:(rewrite Nv; exact Hpos)
                    ltac:(rewrite Nv; unfold two_pow_64 in CL; lia) eq_refl eq_refl) as U.
      lia. }
    assert (Hem' : erase_mat (null_rw_model md a) = erase_mat (null_rw_model m a)).
    { unfold null_rw_model, null_rw_h. rewrite <- Evm. apply erase_mat_cong_lazy. exact Hem. }
    split; [reflexivity|split; [exact Hem'|exact Hpaid']].
Qed.
End LazyNullRwE.
End StartNodes3E.

(* [comment removed for export] *)
Module DrvExitIface.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SLit"; "cell"; "sobj"; "mkObj"; "sv"; "DUnknown"; "DImage"; "SVar"; "sprop"; "mkCell"; "SPUle"; "swf"; "FcsrFrm0"; "SPAlign"; "mkSS"; "@Corelib.Init.Datatypes"; "cons"; "nat"; "nil"; "bool"; "pair"; "true"; "prod"; "list"; "None"; "app"; "false"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.na.DrvExitIface"; "cz"; "ATX"; "FERR"; "vSPx"; "TRI"; "vTID"; "CALL_THUNK"; "COV_HANDLER"; "Pre_exitP_S"; "AEF_GUARD"; "D_X"; "O_afl2b"; "O_afl2p"; "O_atx0"; "O_atx1"; "O_cfl2"; "O_cov"; "O_dso"; "O_dtf"; "O_ferr"; "O_fin"; "O_fina"; "O_glx"; "O_nlkx"; "O_ofile"; "O_ofl"; "O_osbuf"; "O_pgAx"; "O_pgBx"; "O_regf"; "O_tid"; "O_trix"; "O_uerr"; "O_uout"; "O_xlk"; "O_xstk"; "Pre_exit"; "Pre_exit0"; "Pre_exit0_S"; "Pre_exitP"; "Pre_exit_S"; "atx_cells0"; "axX"; "exit_entry"; "facts_exit"; "fregs_X"; "objs_exitP"; "regs_X"; "supportedP"; "@Stdlib.ZArith.BinInt.Z"; "add"; "pow"; "eqb"; "sub"; "opp"; "@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axwf"; "mkAX"; "@Stdlib.Lists.List"; "In"; "@Corelib.Init.Nat"; "add"; "@Stdlib.PArith.BinPos.Pos"; "of_nat"; "@Corelib.Lists.ListDef"; "map"; "seq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "O_got"; "O_rtc"; "SHB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Drv_printf"; "O_file0"; "O_file_after"; "O_realm"; "O_rtc3w"; "O_sbuf0"; "O_sbuf_after"; "O_ssp"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.RegGlobIface"; "O_afl1"; "O_aglob"; "O_ph"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundR SymComplete SymFrame SymEntail SymCFG SymSummary.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SoundA EntailA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require RegGlobIface.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Drv_printf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.RegGlobIface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Import PFAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Definition exit_entry : Z := 0xd11c8.
Definition exit_ecall : Z := 0xd0fa0.
Definition wl_ecallA  : Z := 0xd6760.
Definition FERR : Z := 0xe8ef0.
Definition D_X : Z := 1024.

Definition vSPx : sv := SVar 10.
Definition vTID : sv := SVar 16.

Definition cz (a : Z) (w : Z) (v : sv) : cell := ltac2:(tb__ "0|0|
S9S0Va;A1Vw;Vv;A3").
Definition O_xstk : sobj := ltac2:(tb__ "0|0|
S3S1eS0S50S25A1A1S0Z0A1S11S1A1S5A5").

Definition O_pgAx : sobj := ltac2:(tb__ "0|0|
S3S0Z7fffc570A1S0Z0A1S0Z1e8A1S11S1A1S5A5").
Definition O_pgBx : sobj := ltac2:(tb__ "0|0|
S3S0Z80015238A1S0Z0A1S0Z308A1S11S1A1S5A5").
Definition O_ferr : sobj := ltac2:(tb__ "0|3|
S3S0Z0A1S0S1dA1S0S4cS1dZe8A2A1SfS1S1bS4cS1dZ28A2Z8M0S7P11A1M1A3SfS1S1bS4cS1dZ38A2G0G1A3SfS1S1bS4cS1dG0A2G0S7P12A1M2A3SfS1S1bS4cS1dZ10A2G0G2A3SfS1S1bS4cS1dZ8cA2Z4S0S4fS4dZ2Z20A2Z1A2A1A3S11S1A1A3A3A3A3A3S5A5").
Definition O_uerr : sobj := ltac2:(tb__ "0|0|
S3S0Z0A1S0Ze8fd8A1S0Ze8fe0A1S11S1A1S6A5").
Definition O_uout : sobj := ltac2:(tb__ "0|0|
S3S0Z0A1S0Ze90c8A1S0Ze90d0A1S11S1A1S6A5").
Definition O_fin  : sobj := ltac2:(tb__ "0|0|
S3S0Z0A1S0Ze90d0A1S0Ze91c0A1S11S1A1S6A5").
Definition O_ofl  : sobj := ltac2:(tb__ "0|0|
S3S0Z0A1S0Z641968A1S0Z641978A1S11S1A1S6A5").
Definition O_tid  : sobj := ltac2:(tb__ "0|1|
S3S0Z0A1S0Z6211d0M0A1S0Z6211d4A1SfS1S1bG0Z4S20A3S11S1A1A3S5A5").

Definition ATX : Z := 0x6412c8.
Definition CALL_THUNK : Z := 0xd1174.
Definition COV_HANDLER : Z := 0x7bf84.
Definition AEF_GUARD : Z := 0x8c94c.
Definition atx_cells0 : list cell := ltac2:(tb__ "0|5|
SfS1S1bS4cS1cZ4M0A2G0S0Z0A1M1A3SfS1S1bS4cS1cZ8M2A2G0S0Z1M3A1A3SfS1S1bS4cS1cZ10A2G2S0S4cS1cZ18A2M4A1A3SfS1S1bG4G2G1A3SfS1S1bS4cS1cZ20A2G2S0S21A1A3SfS1S1bS4cS1cZ120A2G2S0S22A1A3SfS1S1bS1cG3G1A3S11S1A1A3A3A3A3A3A3A3").
Definition O_atx0 : sobj := ltac2:(tb__ "0|0|
S3S0Z0A1S0S1cA1S0S4cS1cZ220A2A1S44S5A5").
Definition O_atx1 : sobj := ltac2:(tb__ "0|5|
S3S0Z0A1M0S0S1cA1S0S4cS1cZ220A2A1SfS1S1bS4cS1cZ4M1A2G1G0A3SfS1S1bS4cS1cZ8M2A2G1S0Z2A1A3SfS1S1bS4cS1cZ10A2G2S0S4cS1cZ18A2M3A1A3SfS1S1bG3G2G0A3SfS1S1bS4cS1cZ20A2G2S0S21A1M4A3SfS1S1bS4cS1cZ120A2G2S0S22A1A3SfS1S1bS1cZ1G0A3SfS1S1bS4cS1cZ28A2G2G4A3SfS1S1bS4cS1cZ128A2G2S0S24A1A3S11S1A1A3A3A3A3A3A3A3A3A3S5A5").

Definition TRI : Z := 0x620710.
Definition O_trix : sobj := ltac2:(tb__ "0|3|
S3S0Z0A1M0S0S1fA1M1S0S4cS1fZ14A2A1SfS1S9G1Z1M2S0G2A1A3SfS1S9S0S4cS1fZ4A2A1G2G0A3S11S1A1A3A3S6A5").
Definition O_xlk  : sobj := ltac2:(tb__ "0|0|
S3S0Z0A1S0Z6414e8A1S0Z6414ecA1S11S1A1S6A5").
Definition O_nlkx : sobj := ltac2:(tb__ "0|0|
S3S0Z0A1S0Z64150bA1S0Z64150cA1S11S1A1S6A5").
Definition O_regf : sobj := ltac2:(tb__ "0|1|
S3S0Z0A1S0Zeaa00M0A1S0Zeaa08A1SfS1S1bG0Z8S0Z1A1A3S11S1A1A3S5A5").
Definition O_dtf  : sobj := ltac2:(tb__ "0|0|
S3S0Z0A1S0Zeaa50A1S0Zeaa51A1S11S1A1S6A5").
Definition O_dso  : sobj := ltac2:(tb__ "0|0|
S3S0Z0A1S0Ze6608A1S0Ze6610A1S11S1A1S6A5").
Definition O_fina : sobj := ltac2:(tb__ "0|0|
S3S0Z0A1S0Ze1488A1S0Ze1498A1S11S1A1S6A5").
Definition O_glx  : sobj := ltac2:(tb__ "0|2|
S3S0Z0A1M0S0Zeb930A1S0Zeb980A1SfS1S1bZeb938Z8M1S0Z60A1A3SfS1S1bZeb940G1S7PcA1A3SfS1S1bZeb948G1S7PdA1A3SfS1S1bZeb970G1G0A3S11S1A1A3A3A3A3S5A5").
Definition O_cfl2 : sobj := ltac2:(tb__ "0|1|
S3S0Z0A1S0Z17fc60M0A1S0Z17fc68A1SfS1S1bG0Z8S0ZffffffffffffffffA1A3S11S1A1A3S5A5").
Definition O_cov  : sobj := ltac2:(tb__ "0|0|
S3S0Z0A1S0Z17ff60A1S0Z17ff61A1S11S1A1S6A5").

Definition O_ofile (n : Z) : sobj := ltac2:(tb__ "0|0|
S12S2L_;S4eVn;Z0A2S5dS5eVn;A1X12x2").
Definition O_osbuf (n : Z) : sobj := ltac2:(tb__ "0|0|
S12S2L_;S4eVn;Z0A2S61S62Vn;A1X12x2").

Definition O_afl2p : sobj := ltac2:(tb__ "0|2|
S3S0Z0A1S0Zeb90dA1M0S0Zeb90eA1SfS1S9G0Z1M1S0G1A1A3S11S1A1A3S5A5").
Definition O_afl2b : sobj := ltac2:(tb__ "0|0|
S3S0Z0A1S0Zeb90eA1S0Zeb930A1SfS1S9S0Zeb91cA1Z4S0Z2A1A3S11S1A1A3S5A5").
Definition objs_exitP (ph : bool) (n : Z) : list sobj := ltac2:(tb__ "0|1|
S18S2SfS2S3eSfS2S36SfS2S37SfS2S33Vn;A1SfS2S35Vn;A1SfS2S2eSfS2S3bSfS2S3cSfS2S2fSfS2S34SfS2S39SfS2S63SfS2S12S2Lph;Vph;S29S28X12x2SfS2S3dSfS2S32SfS2S38SfS2S2dSfS2S2cSfS2S30SfS2S64SfS2S26SfS2S31SfS2S65SfS2S66SfS2S60SfS2S2aSfS2S2bSfS2S5fSfS2S5aSfS2S5bSfS2S27S11S2A1M0A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3S12S16S2A1Lph;Vph;SfS2S3aG0A3G0X12x2A3").
Definition objs_exit (n : Z) : list sobj := objs_exitP true n.
Definition objs_exit0 (n : Z) : list sobj := objs_exitP false n.

Definition facts_exit : list sprop := ltac2:(tb__ "0|1|
SfS8SdPaZ4A2SfS8SaS0Z7fff7ff01000A1S1eA2SfS8SaS1eS0S4fS4dZ2M0Z2fA2Ze0A2A1A2SfS8SaS0Z1A1S20A2SfS8SaS20S0S4dG0Z16A2A1A2S11S8A1A3A3A3A3A3").

Definition reg_X (c : Z) (r : nat) : sv := ltac2:(tb__ "0|1|
S10S4Lr;Vr;S0Z0A1S10S10S4Ln;R1S7S57S56U3cVr;A2A1A1M0S10S10S4Ln0;R1S1eS10S10S4Ln1;R1S0Z10800A1S10S10S4Ln2;R1S0Z621278A1S10S10S4Ln3;R1G0S10S10S4Ln4;R1G0S10S10S4Ln5;R1G0S10S10S4Ln6;R1G0S10S10S4Ln7;R1G0S10S10S4Ln8;R1S0Vc;A1S10G0Ln9;X10x2Ln8;X10x2Ln7;X10x2Ln6;X10x2Ln5;X10x2Ln4;X10x2Ln3;X10x2Ln2;X10x2Ln1;X10x2Ln0;X10x2Ln;X10x2").
Definition regs_X (c : Z) : list sv := map (reg_X c) (seq 0 32).
Definition fregs_X : list sv := ltac2:(tb__ "0|0|
S58S10S4S10S7S57S56U14R1A2A1A1Lr;S59U0U20A2A4").

Definition axX (S : sstate) : axst := ltac2:(tb__ "0|0|
S54VS;S11S15S4S4A2A1S0S5cA1A3").
Definition Pre_exitP_S (ph : bool) (n c : Z) : sstate := ltac2:(tb__ "0|0|
SeS46S4aVc;A1S48ScS17S4A1S49Vph;Vn;A2S47S67S19A9").
Definition Pre_exitP (ph : bool) (n c : Z) : axst := ltac2:(tb__ "0|0|
S45S23Vph;Vn;Vc;A3A1").
Definition Pre_exit_S (n c : Z) : sstate := Pre_exitP_S true n c.
Definition Pre_exit (n c : Z) : axst := Pre_exitP true n c.
Definition Pre_exit0_S (n c : Z) : sstate := Pre_exitP_S false n c.
Definition Pre_exit0 (n c : Z) : axst := Pre_exitP false n c.
Definition supportedP (ph : bool) : list (Z * Z) := ltac2:(tb__ "0|5|
S12S16S15S1aS1aA2M0A1Lph;Vph;SfG0S13S1aS1aZ0M1G1A4SfG0S13S1aS1aG1Z2M2A4M3SfG0S13S1aS1aZ1G1A4SfG0S13S1aS1aG2G1A4SfG0S13S1aS1aZ3G1A4SfG0S13S1aS1aZ4G1A4S11G0A1M4A3A3A3A3A3A3SfG0G3G4A3X12x2").

Lemma Pre_exitP_wf : ltac2:(tb__ "0|0|
S12S1aS1aS55S15S1aS1aA2S13S1aS1aR2R1A4S4bR3A1A3S52S51S12SbS23R4R3R2A3A1S14A3S51S12S53S42R4R3R2A3A1S14A3A2F_;Fc;Fn;Fph;").
Proof.
  intros [|] n c H; repeat (destruct H as [H|H]; [injection H as <- <-; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2|]); destruct H.
Qed.
Lemma Pre_exit_wf : ltac2:(tb__ "0|3|
S1aS1aS55S15S1aS1aA2M0S13S1aS1aR2R1A4SfG0S13S1aS1aZ0M1G1A4SfG0S13S1aS1aG1Z2M2A4SfG0S13S1aS1aZ1G1A4SfG0S13S1aS1aG2G1A4SfG0S13S1aS1aZ3G1A4SfG0S13S1aS1aZ4G1A4S11G0A1A3A3A3A3A3A3A3S52S51S12SbS43R3R2A2A1S14A3S51S12S53S3fR3R2A2A1S14A3A2F_;Fc;Fn;").
Proof. intros n c H. exact (Pre_exitP_wf true n c H). Qed.
Lemma Pre_exit0_wf : ltac2:(tb__ "0|1|
S1aS1aS55S15S1aS1aA2M0S13S1aS1aR2R1A4SfG0S13S1aS1aZ0Z2A4S11G0A1A3A3S52S51S12SbS41R3R2A2A1S14A3S51S12S53S40R3R2A2A1S14A3A2F_;Fc;Fn;").
Proof. intros n c H. exact (Pre_exitP_wf false n c H). Qed.

Fixpoint zn_bytes (k : nat) : list byte :=
  match k with O => [] | S k' => Z_to_bv 8 48 :: Z_to_bv 8 10 :: zn_bytes k' end.
Definition PEND (n : Z) : list byte := zn_bytes (Z.to_nat (n - 1)).
End DrvExitIface.

(* [comment removed for export] *)
Module Lib_handle_f_fastcert.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "bool"; "list"; "false"; "prod"; "option"; "andb"; "true"; "app"; "nat"; "cons"; "nil"; "orb"; "pair"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "bitem"; "lform"; "batom"; "bd_wpos"; "item_nn"; "lf_nonneg"; "wformK"; "wformV"; "ASv"; "bd_subst"; "bud_le"; "bud_le_pos"; "bud_pay"; "item_le"; "item_nonneg"; "lf_neg"; "@Corelib.Init.Logic"; "eq"; "True"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "edescA"; "ndesc"; "eda_rank"; "eda_var"; "nd_am"; "nd_bd"; "nd_fr"; "nd_tv"; "am_eqb"; "am_subst"; "echeckJA"; "eda_state"; "edropA"; "eecheckJA"; "fr_sub_eqb"; "nd_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "ss_facts"; "ss_next"; "SLit"; "SPUlt"; "sv"; "sv_below"; "@Stdlib.Lists.List"; "In"; "nth_error"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "edgeA"; "ea_leaf"; "ea_src"; "ea_sub"; "ea_tgt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.na.Lib_handle_f_fastcert"; "bud_le'"; "bud_le_pos'"; "bud_pay'"; "echeckJA'"; "items_nn'"; "eecheckJA'"; "item_nn'"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.JcertCutA"; "cut_okE"; "@Stdlib.ZArith.BinInt.Z"; "leb"; "sub"; "eqb"; "ltb"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "existsb_lazy"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "sv_subst"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "prove_sprop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "tv_sub_eqb"; "@Stdlib.PArith.BinPos.Pos"; "leb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymCFG SymSummary.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA EntailA CFGA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import TobjJV.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require BudA TobjJA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p1.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.JcertCutA.
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

