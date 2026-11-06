(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e2.

(* [comment removed for export] *)
Module RegGlobIface.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "nat"; "cons"; "nil"; "bool"; "true"; "None"; "app"; "false"; "prod"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SLit"; "sv"; "cell"; "sobj"; "mkCell"; "mkObj"; "DUnknown"; "SVar"; "sprop"; "DImage"; "DZero"; "SPAlign"; "FcsrFrm0"; "mkSS"; "swf"; "@Corelib.Init.Nat"; "add"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.MuslMallocIface"; "addk"; "O_flg"; "O_real"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e3.RegGlobIface"; "vB1"; "vS0"; "D_G"; "FRAME_G"; "O_afl1"; "O_afl2"; "O_aglob"; "O_b1"; "O_gl"; "O_gstk"; "O_lla"; "O_llmin"; "O_pgA"; "O_pgB"; "O_ph"; "Pre_G"; "Pre_G_S"; "facts_G"; "fregs_G"; "objs_G"; "regglob_entry"; "regs_G"; "saved_cells"; "vRA"; "@Stdlib.PArith.BinPos.Pos"; "of_nat"; "@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Lists.ListDef"; "map"; "seq"; "@Stdlib.ZArith.BinInt.Z"; "opp"; "pow"; "mul"; "of_nat"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "O_got"; "O_rtc"; "SHB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axwf"; "mkAX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymCall SymSummary Glue3 SymHeap.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SoundA EntailA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv InitState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts Init Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Init OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.MuslMallocIface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition regglob_entry : Z := 0x49fec.
Definition regglob_ret : Z := 0x4a88c.
Definition FRAME_G : Z := 4336.
Definition D_G : Z := 4432.

Definition vB1 : sv := SVar 1.
Definition vS0 : sv := SVar 2.
Definition vRA : sv := SVar 3.

Definition saved_cells : list cell := ltac2:(tb__ "0|1|
S37S0SbS0SdS9S3dN10S3bZ8M0S3cR1A1A2A2A1G0S10S34S18U4R1A2A1A1A3Lk;S38U0UcA2A4").
Definition O_gstk : sobj := ltac2:(tb__ "0|1|
SeS1dS9S39S1eA1A1S9Z0A1S6SbS1SbSdS9N10e0A1Z8M0S9Z17c0A1A3S1SbSdS9N10b0A1G0S9Z5fA1A3S1SbSdS9N8A1G0S33A3S2SbA1A3A3A3S32A3SfA5").
Definition O_pgA : sobj := ltac2:(tb__ "0|0|
SeS9Z7fffc000A1S9Z0A1S9Z1000A1S2SbA1S13A5").
Definition O_pgB : sobj := ltac2:(tb__ "0|0|
SeS9Z80015000A1S9Z0A1S9Z1000A1S2SbA1S13A5").
Definition O_b1 : sobj := ltac2:(tb__ "0|0|
SeS1cS9Z0A1S9Z10000A1S2SbA1SfA5").

Definition O_lla : sobj := ltac2:(tb__ "0|2|
SeS9Z0A1S9Z173648A1M0S9Z173658A1S1SbSdG0Z8M1S19S1cZ10000A2A3S1SbSdS9Z173650A1G1S19S1cZ4dc0A2A3S2SbA1A3A3SfA5").
Definition O_gl : sobj := ltac2:(tb__ "0|2|
SeS9Z0A1M0S9Zeec70A1S9Zeecc0A1S1SbSdS9Zeec78A1Z8M1G0A3S1SbSdS9Zeecb0A1G1S9S3aZ2Z3cA2A1A3S2SbA1A3A3SfA5").

Definition O_afl1 : sobj := ltac2:(tb__ "0|0|
SeS9Z0A1S9Zeebf8A1S9Zeec24A1S1SbSdS9Zeec10A1Z4S9Z1A1A3S2SbA1A3SfA5").
Definition O_afl2 : sobj := ltac2:(tb__ "0|1|
SeS9Z0A1S9Zeec30A1S9Zeec70A1S1SbSdS9Zeec4dA1Z1M0S9G0A1A3S1SbSdS9Zeec5cA1Z4S9Z2A1A3S2SbA1A3A3SfA5").
Definition O_aglob : sobj := ltac2:(tb__ "0|0|
SeS9Z0A1S9Zec560A1S9Zedd20A1S2SbA1S12A5").

Definition O_llmin : sobj := ltac2:(tb__ "0|0|
SeS9Z0A1S9Ze9b30A1S9Ze9b38A1S2SbA1S12A5").
Definition O_ph : sobj := ltac2:(tb__ "0|2|
SeS9Z0A1S9Zf0c5cA1M0S9Zf0c5dA1S1SbSdG0Z1M1S9G1A1A3S2SbA1A3SfA5").

Definition objs_G : list sobj := ltac2:(tb__ "0|0|
S1ScS25S1ScS28S1ScS29S1ScS23S1ScS26S1ScS24S1ScS20S1ScS21S1ScS22S1ScS27S1ScS2aS1ScS1aS1ScS1bS1ScS3eS1ScS3fS2ScA1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").

Definition facts_G : list sprop := ltac2:(tb__ "0|0|
S1S11S14P2Z4A2S1S11S14P1ZcA2S2S11A1A3A3").

Definition reg_G (r : nat) : sv := ltac2:(tb__ "0|1|
S0SaLr;Vr;S9Z0A1S0S0SaLn;R1S10S34S18U3cVr;A2A1A1M0S0S0SaLn0;R1S19S1dS39S1fA1A2S0S0SaLn1;R1S9Z10800A1S0S0SaLn2;R1S9Z6245b8A1S0S0SaLn3;R1G0S0S0SaLn4;R1G0S0S0SaLn5;R1G0S0S0SaLn6;R1S1dS0S0SaLn7;R1S9Zec560A1S0S0SaLn8;R1G0S0S0SaLn9;R1G0S0S0SaLn10;R1G0S0S0SaLn11;R1G0S0S0SaLn12;R1G0S0S0SaLn13;R1G0S0S0SaLn14;R1G0S0S0SaLn15;R1G0S0S0SaLn16;R1G0S0S0SaLn17;R1S9S3aZ2Z3cA2A1S0S0SaLn18;R1G0S0S0SaLn19;R1G0S0S0SaLn20;R1G0S0S0SaLn21;R1G0S0S0SaLn22;R1S9Zeebf8A1S0S0SaLn23;R1S9Zeec70A1S0S0SaLn24;R1S9Zeecb0A1S0G0Ln25;X0x2Ln24;X0x2Ln23;X0x2Ln22;X0x2Ln21;X0x2Ln20;X0x2Ln19;X0x2Ln18;X0x2Ln17;X0x2Ln16;X0x2Ln15;X0x2Ln14;X0x2Ln13;X0x2Ln12;X0x2Ln11;X0x2Ln10;X0x2Ln9;X0x2Ln8;X0x2Ln7;X0x2Ln6;X0x2Ln5;X0x2Ln4;X0x2Ln3;X0x2Ln2;X0x2Ln1;X0x2Ln0;X0x2Ln;X0x2").
Definition regs_G : list sv := map reg_G (seq 0 32).
Definition fregs_G : list sv := ltac2:(tb__ "0|0|
S37S0SaS0S10S34S18U14R1A2A1A1Lr;S38U0U20A2A4").

Definition axG (S : sstate) : axst := ltac2:(tb__ "0|0|
S42VS;S2S8SaSaA2A1S9S40A1A3").
Definition Pre_G_S : sstate := ltac2:(tb__ "0|0|
S16S30S31S2eS15S5SaA1S2fS2dS43S7A9").
Definition Pre_G : axst := axG Pre_G_S.

Lemma Pre_G_wf : ltac2:(tb__ "0|0|
S36S35S3S17S2cA1S4A3S35S3S41S2bA1S4A3A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
End RegGlobIface.

(* [comment removed for export] *)
Module MuslMalloc40States.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SLit"; "sobj"; "sprop"; "ss_pc"; "ss_regs"; "cell"; "ss_next"; "SAlu"; "ss_objs"; "SPUle"; "SPAlign"; "mkObj"; "mkSS"; "ob_cells"; "ss_fcsr"; "ss_fregs"; "ss_resv"; "sstate"; "DZero"; "ob_base"; "ob_dflt"; "ob_hi"; "ob_lo"; "ss_facts"; "ss_lenient"; "SVar"; "c_off"; "swf"; "@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "leafA"; "sym_runA"; "ax_S"; "mkLeafA"; "ax_setS"; "axst"; "entailsA"; "cell_eqb"; "la_state"; "@Corelib.Lists.ListDef"; "nth"; "@Corelib.Init.Datatypes"; "cons"; "nil"; "true"; "option"; "Some"; "list"; "bool"; "prod"; "app"; "pair"; "false"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e3.MuslMalloc40States"; "CUTS_M"; "FUEL_M"; "N18"; "vBRK"; "cont"; "refuse"; "E20f"; "E21f"; "E22f"; "E22g"; "U24"; "E19"; "E20g"; "vRES"; "E18t"; "N22f"; "N22g"; "U24c"; "vGRPf"; "vGRPg"; "E18"; "L24ko"; "L24ok"; "RET0a"; "RET0b"; "RET0f"; "RET0g"; "RETPf"; "RETPg"; "S18"; "S19f"; "S19g"; "S20f"; "S20g_ko"; "S20g_ok"; "S21f"; "S22f"; "S22g"; "F18"; "F20f"; "F22f"; "F22g"; "O_area_f"; "O_brk_hi"; "common_cells"; "leaf1"; "live_cell"; "set_obj_cells"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "N"; "@Stdlib.PArith.BinPos.Pos"; "succ"; "@LinuxProcessSemantics.Riscv.Instr"; "instr"; "ALU_ADD"; "Ecall"; "aluop"; "mulop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsCut"; "instr_at"; "RsSymJump"; "list_set"; "@Stdlib.ZArith.BinInt.Z"; "sub"; "pow"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.MuslMallocIface"; "malloc_ret_null"; "O_stk"; "Pre_M"; "malloc_ret_ok"; "O_errno"; "facts_M"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "mmap_obj"; "S_after"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymHeap"; "enomem_ret"; "@Stdlib.Bool.Bool"; "Is_true"; "@stdpp.base"; "filter"; "@stdpp.decidable"; "Is_true_dec"; "@stdpp.list_basics.list"; "list_filter"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "A_after"; "@Stdlib.Lists.List"; "existsb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymCall SymSummary Glue3 SymHeap.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv InitState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts Init Code KxA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Init OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.KxA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.MuslMallocIface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition leaf1 (A : axst) (o : option (list leafA)) : axst := ltac2:(tb__ "0|1|
S2cS2eS1fA1M0A1S24Lo;Vo;G0G0S24Ll0;R1VA;S1fG0G0S24Ll1;R1S27R2A1S1fG0VA;Ll3;Ll2;X2ex2Ll1;Ll;X2ex2Ll0;VA;X2cx2").
Definition run_to (fuel : nat) (cuts : list Z) (A : axst) : axst := ltac2:(tb__ "0|0|
S62VA;S20S34Vfuel;Vcuts;VA;S2bA5A2").

Definition cont (E : axst) (e : sv) (newobjs : list sobj) (newfacts : list sprop) (nx : positive) : axst := ltac2:(tb__ "0|1|
S23VE;S82Vnewfacts;S7cS21VE;A1M0Ve;S31S2S9G0A1Vnewobjs;A3Vnx;A4A2A2").

Definition refuse (E : axst) : axst := ltac2:(tb__ "0|0|
S83VE;S1S7dA1A2").

Definition CUTS_M : list Z := ltac2:(tb__ "0|0|
S29S65Zd596cS29S65Zd5990S29S65Zd5954S29S65Zd8d60S29S65Zd8db8S29S65Zd4228S29S65Zde844S2aS65A1A3A3A3A3A3A3A3").
Definition FUEL_M : nat := 3000%nat.

Definition run_I__R : option (list leafA) := ltac2:(tb__ "0|0|
S20S34S36S35S77S2bA5").
Local Strategy expand [run_I__R].
Definition E18 : axst := Eval vm_compute in ((fun ro1__ : option (list leafA) => ((leaf1 Pre_M (ro1__)))) run_I__R).
Lemma run_I : ltac2:(tb__ "0|1|
S1dS2cS2eS1fA1M0A1S20S34S36S35S77S2bA5S2dG0S29S1fS22S49S6eA2S2aS1fA1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) run_I__R <: run_I__R = Some [mkLeafA E18 RsCut]). Qed.

Definition live_cell (minoff : Z) (c : cell) : bool := ltac2:(tb__ "0|3|
S0S2fLx;S1bVc;A1S65S74Vminoff;R1A2Lz;S66S2bLi;S6cS0S0S2bLb;La;M0Lop;M1G1S6dG0Lop;M2G2S2fS67S0S2bLa;Lw;Lsgn;S66S0S65S2bLk;Li;Ll;X0x8").
Definition trim (A : axst) (minoff : Z) : axst := ltac2:(tb__ "0|2|
S21VA;A1S12S28S2U0M0S9R1A1S76A4S2ScS14R1A1S17R1A1S16R1A1S7fS6S2eS6A1S81S6A1S6S7eS63Vminoff;R1A2M1A1Lc;S6S80G1A1Lx;SeR1A1A6S15R1A1A5S2S23VA;SdS4R3A1S5R3A1S10R3A1SfR3A1S11R3A1S71S2S9R3A1G0R1A4S7aS7R3A1S19R3A1A9A2Tstk';Tstk;TS;").
Definition E18t : axst := Eval vm_compute in (trim E18 (-256)).
Lemma ent_18 : ltac2:(tb__ "0|0|
S1dS2fS25S49S43S2aS30S66S0A2A1A3S2bA3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition N18 : positive := Eval vm_compute in (ss_next (ax_S E18t)).
Lemma E18_at : ltac2:(tb__ "0|4|
S1eS1dS65S4S21S43A1M0A1M1Zd596cA3S1eS1dS2cS69A1S6fS34G1A2S2dS69S6bA2A3S1eS1dS0S28S0U11S5G0A1M2S1Z0A1M3A4S1Zd6A1A3S1dS0S28S0UaG2G3A4G3A3A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition vBRK : sv := SVar N18.
Definition F18 : list sprop := ltac2:(tb__ "0|0|
S29S3SbS37ZcA2S29S3SaS1Z646000A1S38A2S29S3SaS38S1Z80646000A1A2S2aS3A1A3A3A3").
Definition S18 : axst := ltac2:(tb__ "0|0|
S39S43S38S2aS2A1S5bS68S37A1A5").

Definition run_18__R : option (list leafA) := ltac2:(tb__ "0|0|
S20S34S36S35S52S2bA5").
Local Strategy expand [run_18__R].
Definition E19 : axst := Eval vm_compute in ((fun ro2__ : option (list leafA) => ((leaf1 S18 (ro2__)))) run_18__R).
Lemma run_18 : ltac2:(tb__ "0|1|
S1dS2cS2eS1fA1M0A1S20S34S36S35S52S2bA5S2dG0S29S1fS22S40S6eA2S2aS1fA1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) run_18__R <: run_18__R = Some [mkLeafA E19 RsCut]). Qed.
Lemma E19_at : ltac2:(tb__ "0|4|
S1eS1dS65S4S21S40A1M0A1M1Zd5990A3S1eS1dS2cS69A1S6fS34G1A2S2dS69S6bA2A3S1eS1dS0S28S0U11S5G0A1M2S1Z0A1M3A4S1Zd6A1A3S1eS1dS0S28S0UaG2G3A4S8S6aS38S1Z2000A1A3A3S1dS66S7G0A1S68S37A1A3A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition S19g : axst := ltac2:(tb__ "0|0|
S39S40S8S6aS38S1Z2000A1A3S2aS2A1S2aS3A1S68S37A1A5").

Definition S19f : axst := ltac2:(tb__ "0|0|
S39S40S38S2aS2A1S2aS3A1S68S37A1A5").

Definition run_19g__R : option (list leafA) := ltac2:(tb__ "0|0|
S20S34S36S35S54S2bA5").
Local Strategy expand [run_19g__R].
Definition E20g : axst := Eval vm_compute in ((fun ro3__ : option (list leafA) => ((leaf1 S19g (ro3__)))) run_19g__R).
Lemma run_19g : ltac2:(tb__ "0|1|
S1dS2cS2eS1fA1M0A1S20S34S36S35S54S2bA5S2dG0S29S1fS22S41S6eA2S2aS1fA1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) run_19g__R <: run_19g__R = Some [mkLeafA E20g RsCut]). Qed.
Lemma E20g_at : ltac2:(tb__ "0|4|
S1eS1dS65S4S21S41A1M0A1M1Zd8d60A3S1eS1dS2cS69A1S6fS34G1A2S2dS69S6bA2A3S1eS1dS0S28S0U11S5G0A1M2S1Z0A1M3A4S1ZdeA1A3S1eS1dS0S28S0UaG2G3A4S38A3S1eS1dS0S28S0UbG2G3A4S1Z1000A1A3S1eS1dS0S28S0UcG2G3A4G3A3S1eS1dS0S28S0UdG2G3A4S1Z32A1A3S1eS1dS0S28S0UeG2G3A4S1S72S73Z2Z40A2Z1A2A1A3S1eS1dS0S28S0UfG2G3A4G3A3S1dS66S7G0A1S68S37A1A3A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition S20g_ok : axst := ltac2:(tb__ "0|0|
S39S41S38S2aS2A1S2aS3A1S68S37A1A5").
Definition S20g_ko : axst := ltac2:(tb__ "0|0|
S39S41S1S7dA1S2aS2A1S2aS3A1S68S37A1A5").
Definition run_20g_ok__R : option (list leafA) := ltac2:(tb__ "0|0|
S20S34S36S29S65Zd59b4S35A3S57S2bA5").
Local Strategy expand [run_20g_ok__R].
Definition L24ok : axst := Eval vm_compute in ((fun ro4__ : option (list leafA) => ((leaf1 S20g_ok (ro4__)))) run_20g_ok__R).
Definition run_20g_ko__R : option (list leafA) := ltac2:(tb__ "0|0|
S20S34S36S29S65Zd59b4S35A3S56S2bA5").
Local Strategy expand [run_20g_ko__R].
Definition L24ko : axst := Eval vm_compute in ((fun ro5__ : option (list leafA) => ((leaf1 S20g_ko (ro5__)))) run_20g_ko__R).
Lemma run_20g_ok : ltac2:(tb__ "0|1|
S1dS2cS2eS1fA1M0A1S20S34S36S29S65Zd59b4S35A3S57S2bA5S2dG0S29S1fS22S4bS6eA2S2aS1fA1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) run_20g_ok__R <: run_20g_ok__R = Some [mkLeafA L24ok RsCut]). Qed.
Lemma run_20g_ko : ltac2:(tb__ "0|1|
S1dS2cS2eS1fA1M0A1S20S34S36S29S65Zd59b4S35A3S56S2bA5S2dG0S29S1fS22S4aS6eA2S2aS1fA1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) run_20g_ko__R <: run_20g_ko__R = Some [mkLeafA L24ko RsCut]). Qed.

Definition common_cells (a b : list cell) : list cell := ltac2:(tb__ "0|1|
S7fS6S2eS6A1S81S6A1S6S7eS84S6S26R1A1Vb;A3M0A1Lc;S6S80G0A1Lx;Va;A6").
Definition set_obj_cells (o : sobj) (cs : list cell) : sobj := ltac2:(tb__ "0|0|
ScS14Vo;A1S17Vo;A1S16Vo;A1Vcs;S15Vo;A1A5").
Definition join24 (A B : axst) : axst := ltac2:(tb__ "0|3|
S21VA;A1S12S21VB;A1S12S64S28S2U0M0S9R2A1S76A4M1S61SeG1A1SeS28S2G0S9R1A1S76A4A1A2A2S2S71S2S71S2S9R3A1G0R1A4U6S79A4S2eS2A1S23VA;SdS4R4A1S71S0S5R4A1UaS1aS7R4A1M2A1A4S10R4A1SfR4A1S11R4A1R1S18R4A1S68G2A1S33A9A2Tobjs;Tstk;TSB;TSA;").
Definition U24 : axst := Eval vm_compute in (join24 L24ok L24ko).
Lemma ent_24ok : ltac2:(tb__ "0|1|
S1dS2fS25S4bS3fS29S30S66S0A2M0S32S66S0S68S37A1S38A4S2aG0A1A3A3S2bA3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ent_24ko : ltac2:(tb__ "0|1|
S1dS2fS25S4aS3fS29S30S66S0A2M0S32S66S0S68S37A1S1S72S73Z2Z40A2Z1A2A1A4S2aG0A1A3A3S2bA3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition O_brk_hi : sobj := ltac2:(tb__ "0|1|
ScS8S6aS38S1Z1000A1M0A3S1Z0A1G0S2aS6A1S13A5").
Definition U24c : axst := ltac2:(tb__ "0|1|
S23S3fSdS4S21S3fA1M0A1S5G0A1S10G0A1SfG0A1S11G0A1S31S2S9G0A1S29S2S60S2aS2A1A3A3S18G0A1S7G0A1S19G0A1A9A2").
Lemma U24c_wf : ltac2:(tb__ "0|0|
S1eS1dS2fS1cS21S46A1A1S2bA3S1dS66S7S21S3fA1A1S68S68S37A1A1A3A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition run_24__R : option (list leafA) := ltac2:(tb__ "0|0|
S20S34S36S35S46S2bA5").
Local Strategy expand [run_24__R].
Definition E22g : axst := Eval vm_compute in ((fun ro6__ : option (list leafA) => ((leaf1 U24c (ro6__)))) run_24__R).
Lemma run_24 : ltac2:(tb__ "0|1|
S1dS2cS2eS1fA1M0A1S20S34S36S35S46S2bA5S2dG0S29S1fS22S3eS6eA2S2aS1fA1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) run_24__R <: run_24__R = Some [mkLeafA E22g RsCut]). Qed.
Definition N22g : positive := Eval vm_compute in (ss_next (ax_S E22g)).
Lemma E22g_at : ltac2:(tb__ "0|4|
S1eS1dS65S4S21S3eA1M0A1M1Zd8d60A3S1eS1dS2cS69A1S6fS34G1A2S2dS69S6bA2A3S1eS1dS0S28S0U11S5G0A1M2S1Z0A1M3A4S1ZdeA1A3S1eS1dS0S28S0UaG2G3A4G3A3S1eS1dS0S28S0UbG2G3A4S1Z1000A1A3S1eS1dS0S28S0UcG2G3A4S1Z3A1A3S1eS1dS0S28S0UdG2G3A4S1Z22A1A3S1eS1dS0S28S0UeG2G3A4S1S72S73Z2Z40A2Z1A2A1A3S1dS0S28S0UfG2G3A4G3A3A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition run_22g_fail__R : option (list leafA) := ltac2:(tb__ "0|0|
S20S34S36S35S3aS3eA1S2bA5").
Local Strategy expand [run_22g_fail__R].
Definition RET0g : axst := Eval vm_compute in ((fun ro7__ : option (list leafA) => ((leaf1 (refuse E22g) (ro7__)))) run_22g_fail__R).
Lemma run_22g_fail : ltac2:(tb__ "0|1|
S1dS2cS2eS1fA1M0A1S20S34S36S35S3aS3eA1S2bA5S2dG0S29S1fS22S4fS70A2S2aS1fA1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) run_22g_fail__R <: run_22g_fail__R = Some [mkLeafA RET0g RsSymJump]). Qed.
Definition vGRPg : sv := SVar N22g.
Definition F22g : list sprop := ltac2:(tb__ "0|0|
S29S3SbS45ZcA2S29S3SaS48S1S72Z7fffff800000Z1000A2A1A2S2aS3A1A3A3").
Definition S22g : axst := ltac2:(tb__ "0|0|
S39S3eS48S29S2S7bS45Z1000A2S2aS2A1A3S5eS68S45A1A5").
Definition run_22g__R : option (list leafA) := ltac2:(tb__ "0|0|
S20S34S36S35S5aS2bA5").
Local Strategy expand [run_22g__R].
Definition RETPg : axst := Eval vm_compute in ((fun ro8__ : option (list leafA) => ((leaf1 S22g (ro8__)))) run_22g__R).
Lemma run_22g : ltac2:(tb__ "0|1|
S1dS2cS2eS1fA1M0A1S20S34S36S35S5aS2bA5S2dG0S29S1fS22S51S70A2S2aS1fA1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) run_22g__R <: run_22g__R = Some [mkLeafA RETPg RsSymJump]). Qed.
Lemma RETg_at : ltac2:(tb__ "0|4|
S1eS1dS65S4S21S4fA1M0A1S75A3S1eS1dS0S28S0UaM1S5G0A1S1Z0A1M2A4G2A3S1eS1dS65S4S21S51A1M3A1S78A3S1dS0S28S0G1S5G3A1G2A4S8S6aS48S1Z40A1A3A3A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition run_19f__R : option (list leafA) := ltac2:(tb__ "0|0|
S20S34S36S35S53S2bA5").
Local Strategy expand [run_19f__R].
Definition E20f : axst := Eval vm_compute in ((fun ro9__ : option (list leafA) => ((leaf1 S19f (ro9__)))) run_19f__R).
Lemma run_19f : ltac2:(tb__ "0|1|
S1dS2cS2eS1fA1M0A1S20S34S36S35S53S2bA5S2dG0S29S1fS22S3bS6eA2S2aS1fA1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) run_19f__R <: run_19f__R = Some [mkLeafA E20f RsCut]). Qed.
Lemma E20f_at : ltac2:(tb__ "0|4|
S1eS1dS65S4S21S3bA1M0A1M1Zd8d60A3S1eS1dS2cS69A1S6fS34G1A2S2dS69S6bA2A3S1eS1dS0S28S0U11S5G0A1M2S1Z0A1M3A4S1ZdeA1A3S1eS1dS0S28S0UaG2G3A4G3A3S1eS1dS0S28S0UbG2G3A4S1Z2000A1A3S1eS1dS0S28S0UcG2G3A4G3A3S1eS1dS0S28S0UdG2G3A4S1Z22A1A3S1eS1dS0S28S0UeG2G3A4S1S72S73Z2Z40A2Z1A2A1A3S1eS1dS0S28S0UfG2G3A4G3A3S1dS66S7G0A1S68S37A1A3A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition run_20f_fail__R : option (list leafA) := ltac2:(tb__ "0|0|
S20S34S36S35S3aS3bA1S2bA5").
Local Strategy expand [run_20f_fail__R].
Definition RET0a : axst := Eval vm_compute in ((fun ro10__ : option (list leafA) => ((leaf1 (refuse E20f) (ro10__)))) run_20f_fail__R).
Lemma run_20f_fail : ltac2:(tb__ "0|1|
S1dS2cS2eS1fA1M0A1S20S34S36S35S3aS3bA1S2bA5S2dG0S29S1fS22S4cS70A2S2aS1fA1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) run_20f_fail__R <: run_20f_fail__R = Some [mkLeafA RET0a RsSymJump]). Qed.

Definition vRES : sv := SVar (Pos.succ N18).
Definition F20f : list sprop := ltac2:(tb__ "0|0|
S29S3SbS68S37A1ZcA2S29S3SaS42S1S72Z7fffff800000Z2000A2A1A2S2aS3A1A3A3").
Definition S20f : axst := ltac2:(tb__ "0|0|
S39S3bS42S2aS2A1S5cS68S68S37A1A1A5").
Definition run_20f__R : option (list leafA) := ltac2:(tb__ "0|0|
S20S34S36S35S55S2bA5").
Local Strategy expand [run_20f__R].
Definition E21f : axst := Eval vm_compute in ((fun ro11__ : option (list leafA) => ((leaf1 S20f (ro11__)))) run_20f__R).
Lemma run_20f : ltac2:(tb__ "0|1|
S1dS2cS2eS1fA1M0A1S20S34S36S35S55S2bA5S2dG0S29S1fS22S3cS6eA2S2aS1fA1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) run_20f__R <: run_20f__R = Some [mkLeafA E21f RsCut]). Qed.
Lemma E21f_at : ltac2:(tb__ "0|5|
S1eS1dS65S4S21S3cA1M0A1M1Zd8db8A3S1eS1dS2cS69A1S6fS34G1A2S2dS69S6bA2A3S1eS1dS0S28S0U11S5G0A1M2S1Z0A1M3A4S1Ze2A1A3S1eS1dS0S28S0UaG2G3A4S8S6aS42S1Z1000A1M4A3A3S1eS1dS0S28S0UbG2G3A4G4A3S1eS1dS0S28S0UcG2G3A4S1Z3A1A3S1dS66S7G0A1S68S68S37A1A1A3A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition run_21f_fail__R : option (list leafA) := ltac2:(tb__ "0|0|
S20S34S36S35S3aS3cA1S2bA5").
Local Strategy expand [run_21f_fail__R].
Definition RET0b : axst := Eval vm_compute in ((fun ro12__ : option (list leafA) => ((leaf1 (refuse E21f) (ro12__)))) run_21f_fail__R).
Lemma run_21f_fail : ltac2:(tb__ "0|1|
S1dS2cS2eS1fA1M0A1S20S34S36S35S3aS3cA1S2bA5S2dG0S29S1fS22S4dS70A2S2aS1fA1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) run_21f_fail__R <: run_21f_fail__R = Some [mkLeafA RET0b RsSymJump]). Qed.

Definition O_area_f : sobj := ltac2:(tb__ "0|1|
ScS8S6aS42S1Z1000A1M0A3S1Z0A1G0S2aS6A1S13A5").
Definition S21f : axst := ltac2:(tb__ "0|0|
S39S3cS1Z0A1S29S2S5fS2aS2A1A3S2aS3A1S68S68S37A1A1A5").

Definition run_21f__R : option (list leafA) := ltac2:(tb__ "0|0|
S20S34S36S35S58S2bA5").
Local Strategy expand [run_21f__R].
Definition E22f : axst := Eval vm_compute in ((fun ro13__ : option (list leafA) => ((leaf1 S21f (ro13__)))) run_21f__R).
Lemma run_21f : ltac2:(tb__ "0|1|
S1dS2cS2eS1fA1M0A1S20S34S36S35S58S2bA5S2dG0S29S1fS22S3dS6eA2S2aS1fA1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) run_21f__R <: run_21f__R = Some [mkLeafA E22f RsCut]). Qed.
Definition N22f : positive := Eval vm_compute in (ss_next (ax_S E22f)).
Lemma E22f_at : ltac2:(tb__ "0|4|
S1eS1dS65S4S21S3dA1M0A1M1Zd8d60A3S1eS1dS2cS69A1S6fS34G1A2S2dS69S6bA2A3S1eS1dS0S28S0U11S5G0A1M2S1Z0A1M3A4S1ZdeA1A3S1eS1dS0S28S0UaG2G3A4G3A3S1eS1dS0S28S0UbG2G3A4S1Z1000A1A3S1eS1dS0S28S0UcG2G3A4S1Z3A1A3S1eS1dS0S28S0UdG2G3A4S1Z22A1A3S1eS1dS0S28S0UeG2G3A4S1S72S73Z2Z40A2Z1A2A1A3S1dS0S28S0UfG2G3A4G3A3A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition run_22f_fail__R : option (list leafA) := ltac2:(tb__ "0|0|
S20S34S36S35S3aS3dA1S2bA5").
Local Strategy expand [run_22f_fail__R].
Definition RET0f : axst := Eval vm_compute in ((fun ro14__ : option (list leafA) => ((leaf1 (refuse E22f) (ro14__)))) run_22f_fail__R).
Lemma run_22f_fail : ltac2:(tb__ "0|1|
S1dS2cS2eS1fA1M0A1S20S34S36S35S3aS3dA1S2bA5S2dG0S29S1fS22S4eS70A2S2aS1fA1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) run_22f_fail__R <: run_22f_fail__R = Some [mkLeafA RET0f RsSymJump]). Qed.
Definition vGRPf : sv := SVar N22f.
Definition F22f : list sprop := ltac2:(tb__ "0|0|
S29S3SbS44ZcA2S29S3SaS47S1S72Z7fffff800000Z1000A2A1A2S2aS3A1A3A3").
Definition S22f : axst := ltac2:(tb__ "0|0|
S39S3dS47S29S2S7bS44Z1000A2S2aS2A1A3S5dS68S44A1A5").
Definition run_22f__R : option (list leafA) := ltac2:(tb__ "0|0|
S20S34S36S35S59S2bA5").
Local Strategy expand [run_22f__R].
Definition RETPf : axst := Eval vm_compute in ((fun ro15__ : option (list leafA) => ((leaf1 S22f (ro15__)))) run_22f__R).
Lemma run_22f : ltac2:(tb__ "0|1|
S1dS2cS2eS1fA1M0A1S20S34S36S35S59S2bA5S2dG0S29S1fS22S50S70A2S2aS1fA1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) run_22f__R <: run_22f__R = Some [mkLeafA RETPf RsSymJump]). Qed.
Lemma RETf_at : ltac2:(tb__ "0|4|
S1eS1dS65S4S21S4eA1M0A1S75A3S1eS1dS0S28S0UaM1S5G0A1S1Z0A1M2A4G2A3S1eS1dS65S4S21S50A1M3A1S78A3S1eS1dS0S28S0G1S5G3A1G2A4S8S6aS47S1Z40A1A3A3S1eS1dS65S4S21S4cA1A1S75A3S1dS65S4S21S4dA1A1S75A3A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
End MuslMalloc40States.

(* [comment removed for export] *)
Module StartArgF.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "N"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "Z_to_bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sobj"; "rw"; "sprop"; "SLit"; "valuation"; "SAlu"; "SVar"; "obj_range"; "cell"; "holds"; "mkObj"; "odefault"; "eval"; "ob_base"; "ob_hi"; "ob_lo"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "leb"; "pow"; "mul"; "opp"; "sub"; "@Corelib.Init.Datatypes"; "false"; "bool"; "list"; "nat"; "andb"; "fst"; "snd"; "true"; "Some"; "length"; "option"; "orb"; "prod"; "@Corelib.Init.Logic"; "and"; "eq"; "not"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_SLL"; "aluop"; "mulop"; "branch_cond"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e3.StartArgF"; "ARG_LIM"; "arg_layout"; "fact_ule_lit"; "obj_below_b"; "objs_below_except_b"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.StartALib"; "ARGF"; "@Corelib.Lists.ListDef"; "Forall"; "seq"; "@LinuxProcessSemantics.Riscv.Sem"; "alu64"; "@Stdlib.Lists.List"; "existsb"; "In"; "combine"; "forallb"; "nth_error"; "@Stdlib.PArith.BinPos.Pos"; "eqb"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "in_ranges"; "@Stdlib.Arith.PeanoNat.Nat"; "eqb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundV SymSoundR SymFrame Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.StartALib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition ARG_LIM : Z := 0x7fff80000000.

Definition fact_ule_lit (facts : list sprop) (k : positive) (lim : Z) : bool := ltac2:(tb__ "0|6|
S3dS9S9S9S20Lf;R1S33S6S6S1fLb;La;M0Lc;S9S1fLp;G0S6S6S6S20La;R2S0S1fLz;S1S6S20Lb;R2S0S23S23S42R2Vk;A2S1aZ0R1A2A2S1aR1Vlim;A2A2Lc;S1S1fLi;S31S6S6S1fLb0;La0;M1Lop;M2G2S32G1Lop;M3G3S20S2S6S1fLa0;Lw;Lsgn;M4S1S6S0S1fLk0;Li;Ll;M5X6x8Lk';G2G2G3G3G4G5X6x8Lb;La;G0S1fS1S0S1fLa;Li;X9x7Lf;Vfacts;A3").

Lemma fact_ule_lit_sound : ltac2:(tb__ "0|0|
SbS21S9A1S1S0S3aS9S10R4A1R3A3S2dS20S36R4R3R2A3S26A3S17S3Q40S8R6R4A2A2R3A2F_;F_;Flim;Fk;Ffacts;Frho;").
Proof.
  intros rho facts k lim HF Hb. unfold fact_ule_lit in Hb. apply existsb_exists in Hb as (f & Hin & Hf).
  destruct f as [ | | |a b| | | ]; try discriminate. destruct a as [|k'| | | | | |]; try discriminate. destruct b as [z| | | | | | |]; try discriminate.
  apply andb_prop in Hf as [Hf H2]. apply andb_prop in Hf as [H0 H1].
  apply Pos.eqb_eq in H0. subst k'. apply Z.leb_le in H1. apply Z.leb_le in H2.
  pose proof (proj1 (Forall_forall _ _) HF _ Hin) as X. cbn [holds eval] in X. rewrite Z_to_bv_unsigned in X.
  pose proof (urange (rw rho k)). unfold bv_wrap in X. change (bv_modulus 64) with (2 ^ 64) in X.
  destruct (Z_lt_dec z (2 ^ 64)); [rewrite Z.mod_small in X by lia; lia | lia].
Qed.

Definition obj_below_b (facts : list sprop) (o : sobj) : bool := ltac2:(tb__ "0|8|
S6S20Lx;M0S16Vo;A1S0G0S15Vo;A1S0S23S23S23S1aS1dS1bZ2Z3eA2M1A1R2A2S1aR2R1A2A2S1aR1G1A2A2G0S14Vo;A1S0S23S1aZ0R1A2S1aS18R1R2A2S34A2A2Lb;S1S20S20L_;S42R1P1A2S1aR2Z10A2S36Vfacts;R1S1eS34R2A2A3X20x2Lk;S31S6S6S1fLb;La;M2Lop;M3G3S32G2Lop;M4G4S20S2S6S1fLa;Lw;Lsgn;M5S1S6S0S1fLk;Li;Ll;M6X6x8A2Lhi;S1S1fLi;M7G3G3G4G4G5G6X6x8Llo;G7G3G3G4G4G5G6X6x8").

Lemma obj_below_sound : ltac2:(tb__ "0|3|
SbS21S9A1S7S4Q40M0A1S3aS9S10R4A1R3A3S17S34S3G0S8R5P1A2A2A2S2dS20S37R5R4A2S26A3S39R7R4A2S2eS2cS17S24S0S0SeR8R6A2M1A3S3G0R5A2M2A2S19G2S25S0S0G1A3A2A2A1F_;F_;F_;F_;Fa;Fo;Ffacts;Frho;").
Proof.
  intros rho facts o a HF H1 Hb [Ha _] Hr.
  unfold obj_below_b in Hb. destruct o as [base lo hi cells dflt]. cbn [ob_lo ob_hi ob_base] in Hb.
  destruct lo as [lo| | | | | | |]; try discriminate. destruct hi as [hi| | | | | | |]; try discriminate.
  apply andb_prop in Hb as [Hb Hbase]. apply andb_prop in Hb as [Hb Hhi]. apply andb_prop in Hb as [Hlo Hlohi].
  apply Z.leb_le in Hlo. apply Z.leb_le in Hlohi. apply Z.leb_le in Hhi.
  unfold obj_range, obj_lo_of, obj_hi_of in Hr. cbn [ob_base ob_lo ob_hi fst snd] in Hr.
  rewrite !soff_lit_small in Hr by lia. unfold ARG_LIM in *.
  destruct base as [b|k| | | | | |]; try discriminate.
  - apply andb_prop in Hbase as [Hb0 Hbh]. apply Z.leb_le in Hb0. apply Z.leb_le in Hbh.
    cbn [eval] in Hr. rewrite Z_to_bv_unsigned in Hr. unfold bv_wrap in Hr. change (bv_modulus 64) with (2 ^ 64) in Hr.
    rewrite Z.mod_small in Hr by lia. lia.
  - cbn [eval] in Hr. destruct (Pos.eqb_spec k 1) as [->|Hk].
    + apply Z.leb_le in Hbase. lia.
    + pose proof (fact_ule_lit_sound rho facts k _ HF Hbase). lia.
Qed.

Definition objs_below_except_b (facts : list sprop) (skip : list nat) (objs : list sobj) : bool := ltac2:(tb__ "0|1|
S40S2bS22S7A2M0G0S2aS3dS22S45S24S22S7R1A3A1Vskip;A3S37Vfacts;S25S22S7R1A3A2A2Lio;S3fS22S7S3bU0S28S7Vobjs;A2A2Vobjs;A4A3").

Lemma combine_seq_In : forall {A} (l : list A) (s : nat) x, In x l -> exists i, In (i, x) (combine (seq s (length l)) l).
Proof.
  intros A l. induction l as [|y l IH]; intros s x Hin; [destruct Hin|].
  destruct Hin as [<-|Hin]; [exists s; left; reflexivity|].
  destruct (IH (S s) x Hin) as [i Hi]. exists i. right. exact Hi.
Qed.
Lemma combine_seq_nth : forall {A} (l : list A) (s i : nat) x, In (i, x) (combine (seq s (length l)) l) -> nth_error l (i - s) = Some x /\ (s <= i)%nat.
Proof.
  intros A l. induction l as [|y l IH]; intros s i x Hin; [destruct Hin|].
  destruct Hin as [E|Hin].
  - injection E as <- <-. rewrite Nat.sub_diag. split; [reflexivity | lia].
  - destruct (IH (S s) i x Hin) as [Hn Hle]. replace (i - s)%nat with (S (i - S s))%nat by lia. cbn. split; [exact Hn | lia].
Qed.

Lemma objs_below_except_sound : ltac2:(tb__ "0|3|
SbS21S9A1S21S22A1S21S7A1S4Q40M0A1S3aS9S10R5A1R4A3S17S34S3G0S8R6P1A2A2A2S2dS20S38R6R5R4A3S26A3S39R8R4A2S22S7S3eS22R2R9A3S2dS29S7A1S41S7R9R3A3S27S7R2A2A3S2eS2cS17S24S0S0SeRdR3A2M1A3S3G0R9A2M2A2S19G2S25S0S0G1A3A2A2A1F_;F_;Fo;Fi;S2eS44RaR7R6A3A1F_;F_;F_;F_;F_;Fa;Fobjs;Fskip;Ffacts;Frho;").
Proof.
  intros rho facts skip objs a HF H1 Hb Ha Hskip (o & Ho & Hr).
  destruct (combine_seq_In objs 0 o Ho) as [i Hi].
  pose proof (proj1 (forallb_forall _ _) Hb _ Hi) as X. cbn [fst snd] in X.
  apply Bool.orb_prop in X as [X|X].
  - apply existsb_exists in X as (j & Hj & Hij). apply Nat.eqb_eq in Hij. subst j.
    destruct (combine_seq_nth objs 0 i o Hi) as [Hn _]. rewrite Nat.sub_0_r in Hn. exact (Hskip i o Hj Hn Hr).
  - exact (obj_below_sound rho facts o a HF H1 X Ha Hr).
Qed.

Lemma U_add_small : ltac2:(tb__ "0|1|
S4Q40M0A1S0S17Z0R1A2S19S18S3G0R3A2R2A2S1bZ2Z40A2A2S2dS0S3G0S3cS2fR4S5G0R3A2A3A2S18S3G0R4A2R3A2A3F_;F_;Fc;Fx;").
Proof.
  intros x c Hc Hb. unfold alu64, alu. rewrite bv_add_unsigned, Z_to_bv_unsigned. pose proof (urange x).
  rewrite (bv_wrap_small 64 c) by (change (bv_modulus 64) with (2 ^ 64); lia).
  apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64). lia.
Qed.
Lemma U_add_words : ltac2:(tb__ "0|3|
S4Q40M0A1M1G1S19S18S3G0R2A2M2S3G0R1A2A2S1bZ2Z40A2A2S2dS0S3G0S3cS2fR3R2A3A2S18S3G0R3A2G2A2A3F_;Fy;Fx;").
Proof.
  intros x y Hb. unfold alu64, alu. rewrite bv_add_unsigned. pose proof (urange x). pose proof (urange y).
  apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64). lia.
Qed.
Lemma U_sll3 : ltac2:(tb__ "0|1|
S4Q40M0A1S19S3G0R1A2S1bZ2Z3cA2A2S2dS0S3G0S3cS30R2S5G0Z3A2A3A2S1cZ8S3G0R2A2A2A3F_;Fx;").
Proof.
  intros x Hx. rewrite sll_val. change (3 mod 64) with 3. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8.
  pose proof (urange x). rewrite Z.mod_small by lia. lia.
Qed.

Definition arg_layout (rho : valuation) : Prop := ltac2:(tb__ "0|5|
S2cS17S3Q40M0S8Vrho;P1A2A2M1S1bZ2Z2fA2A2S2cS17S3G0S8Vrho;P2A2A2M2Z400A2S2cS17S3G0S8Vrho;P3A2A2M3Z100A2S2cS17S3G0S8Vrho;P5A2A2Z1ffffA2S2dS0S3G0S8Vrho;P4A2A2S18S18S18G1Zb8A2S1cZ8M4G2A2A2S1cG4G3A2A2A3A2A2A2A2").

Lemma arg_layout_ext : ltac2:(tb__ "0|1|
SbSbS1S43R1P7A2S2dS4Q40A1S8R3R2A2S8R4R2A2A3F_;Fi;S35R3A1M0G0F_;F_;Frho';Frho;").
Proof. intros rho rho' E H. unfold arg_layout in *. rewrite !E by lia. exact H. Qed.

Lemma argf_not_env : ltac2:(tb__ "0|4|
SbS21SfA1S12S4Q40M0A1S35R4A1S39R5R2A2S11ScS2fScS2fSdP1A1ScS30SdP2A1SaZ3A1M1A3A3SaZ10A1A3SaZ0A1ScS2fScS30SdP3A1G1A3SaZ8A1A3R5R4A5S7S2eS2cS17S24S0S0SeR7R1A2M2A3S3G0R4A2M3A2S19G3S25S0S0G2A3A2A2A1To;F_;F_;Fa;Fd;Fcs;Frho;").
Proof.
  intros rho cs d a (L1 & L2 & L3 & L5 & L4) [Ha Hor]. cbv zeta.
  unfold obj_range, obj_lo_of, obj_hi_of, soff. cbn [ob_base ob_lo ob_hi fst snd eval].
  pose proof (urange (rw rho 1%positive)) as U1. pose proof (urange (rw rho 2%positive)) as U2. pose proof (urange (rw rho 3%positive)) as U3.
  pose proof (urange (rw rho 5%positive)) as U5.
  rewrite (U_add_small _ 16); [| lia | rewrite U_add_words; rewrite ?U_sll3; lia].
  rewrite U_add_words by (rewrite U_sll3; lia). rewrite !U_sll3 by lia.
  replace (bv_signed (Z_to_bv 64 0)) with 0 by reflexivity.
  rewrite signed_small by (rewrite U_add_small; rewrite ?U_sll3; lia). rewrite U_add_small by (rewrite ?U_sll3; lia). rewrite U_sll3 by lia.
  lia.
Qed.

Lemma argf_not_str0 : ltac2:(tb__ "0|3|
SbS21SfA1S12S4Q40M0A1S35R4A1S39R5R2A2S11SdP4A1SaZ0A1ScS2fSdP5A1SaZ1A1A3R5R4A5S7S2eS2cS17S24S0S0SeR7R1A2M1A3S3G0R4A2M2A2S19G2S25S0S0G1A3A2A2A1To;F_;F_;Fa;Fd;Fcs;Frho;").
Proof.
  intros rho cs d a (L1 & L2 & L3 & L5 & L4) [Ha Hor]. cbv zeta.
  unfold obj_range, obj_lo_of, obj_hi_of, soff. cbn [ob_base ob_lo ob_hi fst snd eval].
  pose proof (urange (rw rho 5%positive)) as U5. pose proof (urange (rw rho 4%positive)) as U4.
  pose proof (urange (rw rho 1%positive)) as U1. pose proof (urange (rw rho 2%positive)) as U2. pose proof (urange (rw rho 3%positive)) as U3.
  replace (bv_signed (Z_to_bv 64 0)) with 0 by reflexivity.
  rewrite signed_small by (rewrite U_add_small; lia). rewrite U_add_small by lia. lia.
Qed.

Lemma argf_not_based : ltac2:(tb__ "0|3|
SbS6S0S0S21SfA1S12S4Q40M0A1S0S2dS0S3G0S13R8R7A2A2R1A3S2cS17Z0R7A2S17R7R6A2A2S19R7S1bZ2Z3eA2A2S17S18R4R8A2S34A2S17S34S3G0S8RcP1A2A2A2S39RdR7A2S2eS2cS17S24S0S0SeReS11RdSaRcA1SaRbA1RaR9A5A2M1A3S3G0R8A2M2A2S19G2S25S0S0G1A3A2A2A1F_;F_;F_;F_;F_;F_;Fb;Fa;Fd;Fcs;Fhi;Flo;Fe;Frho;").
Proof.
  intros rho e lo hi cs d a b He Hlh Hhi Hb H1 [Ha _].
  unfold obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi fst snd]. rewrite He, !soff_lit_small by lia. lia.
Qed.
End StartArgF.

