(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "nat"; "nil"; "pair"; "app"; "bool"; "prod"; "false"; "list"; "true"; "None"; "andb"; "option"; "fst"; "length"; "snd"; "negb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sprop"; "SLit"; "SVar"; "sobj"; "SPUle"; "sstate"; "cell"; "valuation"; "FcsrFrm0"; "SPUlt"; "mkSS"; "DUnknown"; "mkObj"; "SPBranch"; "SPAlign"; "eval"; "mkCell"; "SAlu"; "SAluW"; "agree_below"; "ss_lenient"; "sprop_eqb"; "ss_facts"; "sv_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "lnode"; "edge"; "mkLN"; "vnode"; "mkVN"; "vdir"; "ln_state"; "enode"; "to_enodeL"; "check_cfg"; "eedge_ok"; "SPfamE"; "Vdown"; "Vup"; "cfg_edges"; "e_leaf"; "e_src"; "e_sub"; "e_tgt"; "echeck2"; "lmeas"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_scan__G1.Lib_scan_double"; "pB"; "v172"; "v173"; "v174"; "vE"; "sd_state"; "vI"; "P_num"; "skip_facts"; "O_out"; "O_pp"; "O_stk"; "O_txt"; "Pre_sd"; "base_facts"; "cur_lt"; "two40"; "vB"; "vL"; "cur_le"; "C1"; "Ce"; "Cm"; "Cn"; "Cp"; "Cs"; "Cx"; "FUEL_sd"; "F_sd"; "NXP"; "P_none"; "Posts_sd"; "X_sd"; "check_ecfg2X"; "cutpcs_sd"; "cuts_sd"; "exits_sd"; "lcuts_sd"; "lexits_sd"; "post_fregs"; "NXC"; "cut_fregs"; "fcallee_saved"; "manual_sd"; "two47"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "setregs"; "pre_fregs"; "post_regs"; "cut_regs"; "pre_regs"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_scan__G1.Lib_scan_int"; "pB"; "v120"; "vE"; "v121"; "vI"; "vL"; "O_out"; "O_pp"; "O_txt"; "Pre_si"; "base_facts"; "v141"; "P_none"; "P_num"; "si_state"; "two40"; "vB"; "C1"; "C2"; "C3"; "FUEL_si"; "Posts_si"; "cutpcs_si"; "cuts_si"; "exits_si"; "imax"; "regs1"; "regs2"; "two47"; "vcuts_si"; "vexits_si"; "@Corelib.Init.Logic"; "eq"; "or"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "leaf"; "RsSymJump"; "mkLeaf"; "@Corelib.Lists.ListDef"; "map"; "seq"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "SP"; "LQ"; "ok_frame"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "etriple"; "triple"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "@LinuxProcessSemantics.Riscv.Instr"; "BC_LTU"; "ALU_ADD"; "ALU_SRL"; "BC_GE"; "@Stdlib.Arith.PeanoNat.Nat"; "eqb"; "@Stdlib.Lists.List"; "In"; "existsb"; "forallb"; "combine"; "nth_error"; "@Stdlib.ZArith.BinInt.Z"; "lt"; "le"; "modulo"; "pow"; "shiftr"; "@Corelib.Init.Nat"; "add"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CursorGlue"; "vTop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_scan__G1.Lib_scan_double.ScanDoubleAddr"; "sd_L1"; "sd_Le"; "sd_Lm"; "sd_Ln"; "sd_Lp"; "sd_Ls"; "sd_Lx"; "sd_ret_inf"; "sd_ret_nan"; "sd_ret_num"; "sd_entry"; "sd_ret0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_scan__G1.Lib_scan_int.ScanIntAddr"; "si_L1"; "si_L2"; "si_L3"; "si_entry"; "si_ret1"; "si_ret2"; "@Stdlib.PArith.BinPos.Pos"; "of_nat";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgGlue"; "check_ecfgI"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
Require Stdlib.ZArith.ZArith.
Require Stdlib.NArith.NArith.
Require Stdlib.Lists.List.
Require Stdlib.Bool.Bool.
Require Stdlib.PArith.PArith.
Require Stdlib.micromega.Lia.
Require stdpp.bitvector.bitvector.
Require LinuxProcessSemantics.LinuxProcessSem.BvBase.
Require LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Require LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Require LinuxProcessSemantics.LinuxProcessSem.State.
Require LinuxProcessSemantics.LinuxProcessSem.Run.
Require LinuxProcessSemantics.Riscv.Prelude.
Require LinuxProcessSemantics.Riscv.Instr.
Require LinuxProcessSemantics.Riscv.Decode.
Require LinuxProcessSemantics.Riscv.DecodeC.
Require LinuxProcessSemantics.Riscv.Sem.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundV.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundL.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymComplete.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgGlue.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CursorGlue.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Code.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFGFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Lib_scan_int.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundV OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundL OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymComplete OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CursorGlue.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Code.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Module ScanIntAddr.
  Definition si_entry : Z := 0x1ba14.
  Definition si_L1 : Z := 0x1ba30.
  Definition si_L3 : Z := 0x1ba7c.
  Definition si_L2 : Z := 0x1bab0.
  Definition si_ret1 : Z := 0x1ba70.
  Definition si_ret2 : Z := 0x1bb04.
End ScanIntAddr.
Import ScanIntAddr.

Definition FUEL_si : nat := 300%nat.

Definition vB : sv := SVar 15.
Definition vI : sv := SVar 16.
Definition vE : sv := SVar 17.
Definition vL : sv := SVar 18.
Definition pB (off : sv) : sv := SAlu ALU_ADD vB off.
Definition two40 : Z := 2 ^ 40.
Definition two47 : Z := 2 ^ 47.
Definition imax : Z := 0x7fffffff.

Definition base_facts : list sprop := ltac2:(tb__ "0|0|
S0S12S16S79S77A2S0S12S16S77S7aA2S0S12S16S7aS13S84A1A2S0S12S16S85S13S91A1A2S0S12S16S13Z1A1S85A2S0S12S20PcZ3A2S0S12S20PeZ2A2S2S12A1A3A3A3A3A3A3A3").

Definition O_pp (c0 : sv) : sobj := ltac2:(tb__ "0|2|
S1eS14PcA1S13Z0A1M0S13Z8M1A1S0S18S22G0G1Vc0;A3S2S18A1A3S1dA5").
Definition O_txt (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S1eS85S13Z0A1S7aVcells;S1dA5").
Definition O_out (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S1eS14PeA1S13Z0A1S13Z4A1Vcells;S1dA5").

Definition Pre_si : sstate := ltac2:(tb__ "0|2|
S1cSc6S6eS72S0S6S1S11A2M0S3S1S11UbS75S77A1A4S2G0A1A3A2S6fS1aSaS11A1S0S15S7cS75S79A1A1S0S15S7dS2S18A1M1A1S0S15S7bG1A1S2S15A1A3A3A3S7fS6dS7A9").

Definition v120 : sv := SVar 120.
Definition v121 : sv := SVar 121.
Definition plus1 (e : sv) : sv := SAlu ALU_ADD e (SLit 1).

Definition inv1 : list sprop := ltac2:(tb__ "0|0|
S0S12S1bS76S77A2S0S12S1bS76S7aA2S0S12S16S79S76A2S0S12S16S76S13S84A1A2S0S12S1fSa6S75S76A1S75S77A1A3S2S12A1A3A3A3A3A3").
Definition inv3 : list sprop := ltac2:(tb__ "0|1|
S0S12S1bS78S77A2S0S12S1bS78S7aA2S0S12S16S79S78A2S0S12S16S78S13S84A1M0A2S0S12S1fSa6S75S78A1S75S77A1A3S0S12S1bS76S77A2S0S12S16S79S76A2S0S12S16S76G0A2S2S12A1A3A3A3A3A3A3A3A3").

Definition si_state (pc : Z) (regs : list (nat * sv)) (c0 : sv) (txt out : list cell)
           (facts : list sprop) (nx : positive) : sstate := ltac2:(tb__ "0|1|
S1cVpc;S6eS71S6dA1S4S6S1S11A2M0S0G0S3S1S11UaS14PcA1A4S0G0S3S1S11UbS75S77A1A4S0G0S3S1S11UcS14PeA1A4S2G0A1A3A3A3Vregs;A3A2S6fS1aSaS11A1S0S15S7cVc0;A1S0S15S7dVtxt;A1S0S15S7bVout;A1S2S15A1A3A3A3S4S12Vfacts;S7fA3Vnx;S7A9").

Definition regs1 (c : sv) : list (nat * sv) := ltac2:(tb__ "0|1|
S0S6S1S11A2M0S3S1S11UdVc;A4S0G0S3S1S11UeS13Z20A1A4S0G0S3S1S11UfS13Z9A1A4S2G0A1A3A3A3").
Definition C1_0 : sstate := ltac2:(tb__ "0|1|
S83Sc3S8fS75S76A1A1S75S79A1S2S18A1M0G0S2S12A1P87A7").
Definition C1 : sstate := add_facts inv1 C1_0.

Definition C3_0 : sstate := ltac2:(tb__ "0|2|
S83Sc5S0S6S1S11A2M0S3S1S11UdS75S78A1A4S0G0S3S1S11UeS14P7aA1A4S2G0A1A3A3S75S76A1S2S18A1M1G1S2S12A1P87A7").
Definition C3 : sstate := add_facts inv3 C3_0.

Definition regs2 (c : sv) : list (nat * sv) := ltac2:(tb__ "0|1|
S0S6S1S11A2M0S3S1S11UdVc;A4S0G0S3S1S11UeS14P7aA1A4S0G0S3S1S11UfS14P7bA1A4S0G0S3S1S11U10S13Z9A1A4S0G0S3S1S11U11S13ZaA1A4S0G0S3S1S11U5S13S8eA1A4S0G0S3S1S11U6S14P7cA1A4S2G0A1A3A3A3A3A3A3A3").
Definition C2_0 : sstate := ltac2:(tb__ "0|1|
S83Sc4S90S75S78A1A1S75S76A1S2S18A1M0G0S2S12A1P87A7").
Definition C2 : sstate := add_facts inv3 C2_0.

Definition v141 : sv := SVar 141.
Definition F_si : list sprop := ltac2:(tb__ "0|0|
S0S12S16S79S80A2S0S12S16S80S77A2S2S12A1A3A3").
Definition P_none_0 : sstate := ltac2:(tb__ "0|1|
S1cSc7S70S6dA1S6fS1aSaS11A1S0S15S7cS75S80A1A1S0S15S7dS2S18A1M0A1S0S15S7bG0A1S2S15A1A3A3A3S7fP8fS7A9").
Definition P_num_0 : sstate := ltac2:(tb__ "0|1|
S1cSc8S70S6dA1S6fS1aSaS11A1S0S15S7cS75S80A1A1S0S15S7dS2S18A1M0A1S0S15S7bS0S18S22S13Z0A1Z4S14P8eA1A3G0A3A1S2S15A1A3A3A3S7fP8fS7A9").
Definition P_none : sstate := add_facts F_si P_none_0.
Definition P_num : sstate := add_facts F_si P_num_0.
Definition Posts_si : list leaf := ltac2:(tb__ "0|0|
S0S97S99S81S98A2S0S97S99S82S98A2S2S97A1A3A3").

Definition cuts_si : list sstate := ltac2:(tb__ "0|0|
S0S17S7eS0S17S86S0S17S88S0S17S87S2S17A1A3A3A3A3").
Definition exits_si : list sstate := ltac2:(tb__ "0|0|
S0S17S81S0S17S82S2S17A1A3A3").
Definition cutpcs_si : list Z := ltac2:(tb__ "0|0|
S0S73Sc3S0S73Sc5S0S73Sc4S2S73A1A3A3A3").

Lemma check_si : ltac2:(tb__ "0|0|
S94S5S34S2aS89S8bS6dS8cS8dA6S9A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFGFast.check_cfg_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cuts_si_strict : ltac2:(tb__ "0|0|
S94S5SacS17S26S8cA3S7A3").
Proof. vm_compute. reflexivity. Qed.

Theorem scan_int_sum : ltac2:(tb__ "0|0|
Sa2OF_;S8Sa1A1Sa0OF_;F_;S19S9fS2aR3R2A3Sa4S2aR4S9dS2aR3S7eR2A4S9eS2aR3S6dR2S8aA5A4F_;Frho;FK;Fok;").
Proof.
  intros ok K rho Hok.
  apply (cfg_sound segs FUEL_si cutpcs_si NF cuts_si exits_si
           (fun rho' => agree_below NF rho rho') ok K (LQ segs K NF rho Posts_si) Hok).
  - rewrite cuts_si_strict. intros; discriminate.
  - intros r1 r2 H1 H2. eapply agree_below_trans; eauto.
  - exact check_si.
  - intros E rhoE HinE HagE.
    destruct HinE as [<-|[<-|[]]]; revert HagE.
    + apply exit_post. in_nth 0.
    + apply exit_post. in_nth 1.
  - left; reflexivity.
  - apply agree_below_refl.
Qed.

Definition vcuts_si : list vnode := ltac2:(tb__ "0|0|
S0S2eS2fS7eZ1eS13Z0A1A3S0S2eS2fS86Z14S76A3S0S2eS2fS88ZfS78A3S0S2eS2fS87ZaS78A3S2S2eA1A3A3A3A3").
Definition vexits_si : list vnode := ltac2:(tb__ "0|1|
S0S2eS2fS81Z1M0Sb6A3S0S2eS2fS82G0Sb6A3S2S2eA1A3A3").

Lemma echeck_si : ltac2:(tb__ "0|0|
S94S5SccS2aS89S8bS6dS92S93A6S9A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.check_ecfgI_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.

Theorem scan_int_sum_ex : ltac2:(tb__ "0|0|
S8Sa1A1Sa0OF_;F_;S19Sa3S2aS9dS2aR2S7eR1A4S9eS2aR2S6dR1S8aA5A3Frho;FK;").
Proof.
  intros K rho.
  change Pre_si with (vn_state (mkVN Pre_si 30 (SLit 0))).
  apply (cfg_complete_autoI segs FUEL_si cutpcs_si NF vcuts_si vexits_si
           (fun rho' => agree_below NF rho rho') K (LQ segs K NF rho Posts_si)).
  - intros r1 r2 H1 H2. eapply agree_below_trans; eauto.
  - exact echeck_si.
  - intros E rhoE HinE HgE.
    destruct HinE as [<-|[<-|[]]]; revert HgE.
    + apply (eexit_post_I0 segs K NF rho vcuts_si Posts_si (mkVN P_none 1 vTop)). in_nth 0.
    + apply (eexit_post_I0 segs K NF rho vcuts_si Posts_si (mkVN P_num 1 vTop)). in_nth 1.
  - left; reflexivity.
  - apply agree_below_refl.
Qed.
End Lib_scan_int.

Module Lib_scan_double.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundV OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundL OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymComplete OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CursorGlue.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Code.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Module ScanDoubleAddr.
  Definition sd_entry : Z := 0x19b90.
  Definition sd_L1 : Z := 0x19bb4.
  Definition sd_Ls : Z := 0x19c08.
  Definition sd_Lm : Z := 0x19ea8.
  Definition sd_Le : Z := 0x19fa8.
  Definition sd_Lx : Z := 0x19fdc.
  Definition sd_Ln : Z := 0x1a00c.
  Definition sd_Lp : Z := 0x1a050.
  Definition sd_ret0 : Z := 0x19f9c.
  Definition sd_ret_nan : Z := 0x19cc8.
  Definition sd_ret_num : Z := 0x1a0a8.
  Definition sd_ret_inf : Z := 0x1a0cc.
End ScanDoubleAddr.
Import ScanDoubleAddr.

Definition FUEL_sd : nat := 400%nat.

Definition fcallee_saved (r : nat) : bool :=
  match r with 8 | 9 | 18 | 19 | 20 | 21 | 22 | 23 | 24 | 25 | 26 | 27 => true | _ => false end%nat.
Definition cut_fregs : list sv := ltac2:(tb__ "0|0|
S9aS1S11S1S5S11L_;S6aR1A1S14Sc9Sb5U3cR1A2A1A1S14Sc9Sb5U8cR1A2A1A1X5x2Lr;S9bU0U20A2A4").
Definition post_fregs : list sv := cut_fregs.
Definition NXC : positive := 192%positive.
Definition NXP : positive := 174%positive.

Definition vB : sv := SVar 15.
Definition vI : sv := SVar 16.
Definition vE : sv := SVar 17.
Definition vL : sv := SVar 18.
Definition pB (off : sv) : sv := ltac2:(tb__ "0|0|
S23Sa7S51Voff;A3").
Definition two40 : Z := 2 ^ 40.
Definition two47 : Z := 2 ^ 47.

Definition base_facts : list sprop := ltac2:(tb__ "0|1|
S0S12S16S46S44A2S0S12S16S44S52A2S0S12S16S52S13S50A1A2S0S12S16S51S13S6cA1A2S0S12S16S13Z1A1S51A2S0S12S20PcZ3M0A2S0S12S20PeG0A2S0S12S20PaZ4A2S2S12A1A3A3A3A3A3A3A3A3").

Definition O_stk (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S1eS14PaA1S13N10A1S13Z0A1Vcells;S1dA5").
Definition O_pp (c0 : sv) : sobj := ltac2:(tb__ "0|2|
S1eS14PcA1S13Z0A1M0S13Z8M1A1S0S18S22G0G1Vc0;A3S2S18A1A3S1dA5").
Definition O_txt (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S1eS51S13Z0A1S52Vcells;S1dA5").
Definition O_out (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S1eS14PeA1S13Z0A1S13Z8A1Vcells;S1dA5").

Definition Pre_sd : sstate := ltac2:(tb__ "0|2|
S1cSc1S6eS72S0S6S1S11A2M0S3S1S11UbS40S44A1A4S2G0A1A3A2S6fS1aSaS11A1S0S15S4bS2S18A1M1A1S0S15S4aS40S46A1A1S0S15S4cG1A1S0S15S49G1A1S2S15A1A3A3A3A3S4eS6dS7A9").

Definition cur_lt (c : sv) : list sprop := ltac2:(tb__ "0|0|
S0S12S1bVc;S44A2S0S12S1bVc;S52A2S0S12S16S46Vc;A2S0S12S16Vc;S13S50A1A2S0S12S1fSa6S40Vc;A1S40S44A1A3S2S12A1A3A3A3A3A3").
Definition cur_le (c : sv) : list sprop := ltac2:(tb__ "0|0|
S0S12S16S46Vc;A2S0S12S16Vc;S44A2S0S12S16Vc;S13S50A1A2S2S12A1A3A3A3").

Definition v172 : sv := SVar 172.
Definition v173 : sv := SVar 173.
Definition v174 : sv := SVar 174.

Definition sd_state (pc : Z) (regs : list (nat * sv)) (c0 : sv) (out : list cell) (facts : list sprop) : sstate := ltac2:(tb__ "0|2|
S1cVpc;S6eS71S6dA1S4S6S1S11A2M0S0G0S3S1S11U2S23Sa7S14PaA1S13N10A1A3A4S0G0S3S1S11U8S14P6cA1A4S0G0S3S1S11UaS14PcA1A4S0G0S3S1S11UbS40S44A1A4S0G0S3S1S11UcS14PeA1A4S2G0A1A3A3A3A3A3Vregs;A3A2S69S1aSaS11A1S0S15S4bS0S18S22S13N8A1Z8S14P1cA1A3S2S18A1M1A3A1S0S15S4aVc0;A1S0S15S4cG1A1S0S15S49Vout;A1S2S15A1A3A3A3A3S4S12Vfacts;S4eA3S68S7A9").

Definition C1 : sstate := ltac2:(tb__ "0|1|
S45Sb7S0S6S1S11A2M0S3S1S11UeS40S41A1A4S0G0S3S1S11UdS13Z20A1A4S0G0S3S1S11UfS13Z9A1A4S2G0A1A3A3A3S40S46A1S2S18A1S4fS41A1A5").

Definition skip_facts : list sprop := ltac2:(tb__ "0|0|
S0S12S1bS41S44A2S0S12S16S46S41A2S0S12S16S41S13S50A1A2S2S12A1A3A3A3").
Definition Cs : sstate := ltac2:(tb__ "0|1|
S45SbcS0S6S1S11A2M0S3S1S11UeS40S42A1A4S0G0S3S1S11UdS43A4S2G0A1A3A3S40S41A1S2S18A1S4S12S4fS42A1S4S12S0S12S16S43S13Z1A1A2S2S12A1A3S48A3A3A5").

Definition Cm : sstate := ltac2:(tb__ "0|3|
S45Sb9S0S6S1S11A2M0S3S1S11UeS40S42A1M1A4S0G0S3S1S11U1fS23Sa7G1S13Z1A1M2A3A4S0G0S3S1S11UdS43A4S0G0S3S1S11U5S14PafA1A4S0G0S3S1S11U1eS14Pb0A1A4S0G0S3S1S11UfS14Pb1A1A4S0G0S3S1S11U10S14Pb2A1A4S0G0S3S1S11U6S14Pb3A1A4S0G0S3S1S11U11S14Pb4A1A4S0G0S3S1S11U7S13Z9A1A4S0G0S3S1S11U1cS13Z12A1A4S0G0S3S1S11U1dS13ZaA1A4S2G0A1A3A3A3A3A3A3A3A3A3A3A3A3S40S41A1S2S18A1S4S12S4fS42A1S4S12S0S12S16S43G2A2S2S12A1A3S48A3A3A5").

Definition Ce : sstate := ltac2:(tb__ "0|1|
S45Sb8S0S6S1S11A2M0S3S1S11UeS40S42A1A4S0G0S3S1S11UdS43A4S0G0S3S1S11U6S14Pb3A1A4S0G0S3S1S11U5S14PafA1A4S0G0S3S1S11UfS14Pb1A1A4S0G0S3S1S11U10S14Pb2A1A4S0G0S3S1S11U11S14Pb4A1A4S0G0S3S1S11U7S13Z9A1A4S0G0S3S1S11U1cS13ZaA1A4S0G0S3S1S11U1dS13Z186a0A1A4S2G0A1A3A3A3A3A3A3A3A3A3A3S40S41A1S2S18A1S4S12S4fS42A1S4S12S0S12S16S43S13Z1A1A2S2S12A1A3S48A3A3A5").

Definition Cp : sstate := ltac2:(tb__ "0|2|
S45SbbS0S6S1S11A2M0S3S1S11UbS40S42A1A4S0G0S3S1S11UdS43A4S0G0S3S1S11UeS14Pb7A1A4S0G0S3S1S11U11S14Pb8A1A4S0G0S3S1S11UfS13Z1A1M1A4S2G0A1A3A3A3A3A3S40S41A1S2S18A1S4S12S53S42A1S4S12S0S12S16S43G1A2S2S12A1A3S48A3A3A5").

Definition Cx : sstate := ltac2:(tb__ "0|1|
S45SbdS0S6S1S11A2M0S3S1S11UbS40S42A1A4S0G0S3S1S11UdS43A4S0G0S3S1S11UeS14Pb7A1A4S2G0A1A3A3A3S40S41A1S2S18A1S4S12S53S42A1S4S12S0S12S16S43S13Z1A1A2S2S12A1A3S48A3A3A5").

Definition Cn : sstate := ltac2:(tb__ "0|3|
S45SbaS0S6S1S11A2M0S3S1S11UbS40S42A1A4S0G0S3S1S11UdS43A4S0G0S3S1S11UeS14Pb9A1M1A4S0G0S3S1S11UfS13N16A1A4S2G0A1A3A3A3A3S40S41A1S2S18A1S4S12S53S42A1S4S12S0S12S16S43S13Z1A1M2A2S0S12S1fSa9G1G2A3S0S12S1fSa9S13Z16A1G1A3S2S12A1A3A3A3S48A3A3A5").

Definition F_sd : list sprop := ltac2:(tb__ "0|0|
S0S12S16S46S41A2S0S12S16S41S44A2S2S12A1A3A3").
Definition P_none : sstate := ltac2:(tb__ "0|2|
S1cSc2S6eS70S6dA1S0S6S1S11A2M0S3S1S11UaS13Z0A1A4S2G0A1A3A2S67S1aSaS11A1S0S15S4bS2S18A1M1A1S0S15S4aS40S41A1A1S0S15S4cG1A1S0S15S49G1A1S2S15A1A3A3A3A3S4S12S5cS4eA3S5dS7A9").
Definition P_num (pc : Z) : sstate := ltac2:(tb__ "0|2|
S1cVpc;S6eS70S6dA1S0S6S1S11A2M0S3S1S11UaS13Z1A1A4S2G0A1A3A2S67S1aSaS11A1S0S15S4bS2S18A1M1A1S0S15S4aS40S41A1A1S0S15S4cG1A1S0S15S49S0S18S22S13Z0A1Z8S14PadA1A3G1A3A1S2S15A1A3A3A3A3S4S12S5cS4eA3S5dS7A9").
Definition Posts_sd : list leaf := ltac2:(tb__ "0|0|
S0S97S99S5eS98A2S0S97S99S47SbfA1S98A2S0S97S99S47Sc0A1S98A2S0S97S99S47SbeA1S98A2S2S97A1A3A3A3A3").

Definition cuts_sd : list sstate := ltac2:(tb__ "0|0|
S0S17S4dS0S17S54S0S17S59S0S17S56S0S17S55S0S17S5aS0S17S57S0S17S58S2S17A1A3A3A3A3A3A3A3A3").
Definition exits_sd : list sstate := ltac2:(tb__ "0|0|
S0S17S5eS0S17S47SbfA1S0S17S47Sc0A1S0S17S47SbeA1S2S17A1A3A3A3A3").
Definition cutpcs_sd : list Z := ltac2:(tb__ "0|0|
S0S73Sb7S0S73SbcS0S73Sb9S0S73Sb8S0S73SbdS0S73SbaS0S73SbbS2S73A1A3A3A3A3A3A3A3").

Definition lcuts_sd : list lnode := ltac2:(tb__ "0|5|
S0S2bS2dS4dZ9S2S6S30S11A2M0A1M1A3S0S2bS2dS54Z8S0G0S3S30S11S38S7A1M2S41A4G1A3A3S0S2bS2dS59Z7G1A3S0S2bS2dS56Z6S0G0S3S30S11G2S42A4G1A3M3A3S0S2bS2dS55Z5G3A3S0S2bS2dS5aZ4G1A3S0S2bS2dS57Z3M4G1A3S0S2bS2dS58G4S0G0S3S30S11S37S7A1S14Pb8A1A4G1A3A3S2S2bA1A3A3A3A3A3A3A3A3").
Definition lexits_sd : list lnode := ltac2:(tb__ "0|0|
S9aS17S2bS17S2dR1Z0S2S6S30S11A2A1A3LP;S64A4").

Lemma check_sd : ltac2:(tb__ "0|0|
S94S5S34S2aS5bS62S6dS63S64A6S9A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFGFast.check_cfg_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cuts_sd_strict : ltac2:(tb__ "0|0|
S94S5SacS17S26S63A3S7A3").
Proof. vm_cast_no_check (@eq_refl bool false). Qed.

Theorem scan_double_sum : ltac2:(tb__ "0|0|
Sa2OF_;S8Sa1A1Sa0OF_;F_;S19S9fS2aR3R2A3Sa4S2aR4S9dS2aR3S4dR2A4S9eS2aR3S6dR2S5fA5A4F_;Frho;FK;Fok;").
Proof.
  intros ok K rho Hok.
  apply (cfg_sound segs FUEL_sd cutpcs_sd NF cuts_sd exits_sd
           (fun rho' => agree_below NF rho rho') ok K (LQ segs K NF rho Posts_sd) Hok).
  - rewrite cuts_sd_strict. intros; discriminate.
  - intros r1 r2 H1 H2. eapply agree_below_trans; eauto.
  - exact check_sd.
  - intros E rhoE HinE HagE.
    destruct HinE as [<-|[<-|[<-|[<-|[]]]]]; revert HagE.
    + apply exit_post. in_nth 0.
    + apply exit_post. in_nth 1.
    + apply exit_post. in_nth 2.
    + apply exit_post. in_nth 3.
  - left; reflexivity.
  - apply agree_below_refl.
Qed.

Definition manual_sd : list nat := [141; 154]%nat.

Lemma Forall_by_index {A} (P : A -> Prop) (f : nat -> A -> bool) : ltac2:(tb__ "0|1|
S8VA;A1S1S94S5SadS6S1VA;A2M0G0Vf;SdS1VA;R1A3SfS1VA;R1A3A2Lke;SaeS1VA;S9bR1SeVA;R2A2A2R2A4A3S9A3S1VA;S94S5Vf;R2R1A2S9A3VP;R2A1F_;Fe;Fk;S9cVA;VP;R4A3F_;F_;Fk0;Fl;").
Proof.
  intros l. induction l as [|x t IH]; intros k0 H HP; [constructor|].
  cbn in H. apply andb_prop in H as [H1 H2]. constructor; [exact (HP k0 x H1) | exact (IH (S k0) H2 HP)].
Qed.

Lemma U_srlw_lit : ltac2:(tb__ "0|2|
S19S11S73S96Sb1Z1R1A2Sb0R1Z20M0A2A2S94S73Sa5Q40M1S21R4S24Sa8R3S13R2A1A3A2A2Sb4Sb2Sa5G1S21R4R3A2A2Sb3Z2G0A2A2R2A2A3F_;Fk;Fa;Frho;").
Proof.
  intros rho a k Hk. cbn [eval]. unfold alu32, alu.
  pose proof (urange (eval rho a)) as R1.
  assert (M : bv_unsigned (bv_and (low32 (Z_to_bv 64 k)) (Z_to_bv 32 31)) = k).
  { rewrite bv_and_unsigned, low32_umod. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
    change (bv_modulus 64) with (2 ^ 64). change (bv_modulus 32) with (2 ^ 32).
    rewrite (Z.mod_small k (2 ^ 64)) by lia. rewrite (Z.mod_small k (2 ^ 32)) by lia.
    change (31 mod 2 ^ 32) with (Z.ones 5). rewrite Z.land_ones by lia. apply Z.mod_small. lia. }
  assert (B0 : 0 <= bv_unsigned (eval rho a) mod 2 ^ 32 < 2 ^ 32) by (apply Z.mod_pos_bound; lia).
  assert (R : bv_unsigned (bv_shiftr (low32 (eval rho a)) (bv_and (low32 (Z_to_bv 64 k)) (Z_to_bv 32 31)))
              = Z.shiftr (bv_unsigned (eval rho a) mod 2 ^ 32) k).
  { rewrite bv_shiftr_unsigned, M, low32_umod. reflexivity. }
  assert (B : 0 <= Z.shiftr (bv_unsigned (eval rho a) mod 2 ^ 32) k < 2 ^ 31).
  { split; [apply Z.shiftr_nonneg; lia|].
    rewrite Z.shiftr_div_pow2 by lia. apply Z.div_lt_upper_bound; [apply Z.pow_pos_nonneg; lia|].
    apply (Z.lt_le_trans _ (2 ^ 32)); [lia|]. rewrite <- Z.pow_add_r by lia. apply Z.pow_le_mono_r; lia. }
  rewrite sext64_32_small by (rewrite R; lia). exact R.
Qed.

Lemma srlw1_lt : ltac2:(tb__ "0|2|
S19S11Sb0Z1M0Sa5Q40M1S21R2R1A2A2A2Sb0Sa5G1S21R3S24Sa8R2S13G0A1A3A2A2Sa5G1S21R3R2A2A2A2F_;Fa;Frho;").
Proof.
  intros rho a H. rewrite U_srlw_lit by lia. pose proof (urange (eval rho a)) as R.
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 1) with 2.
  assert (B0 : 0 <= bv_unsigned (eval rho a) mod 2 ^ 32 <= bv_unsigned (eval rho a)) by (split; [apply Z.mod_pos_bound; lia | apply Z.mod_le; lia]).
  apply Z.div_lt_upper_bound; lia.
Qed.

Lemma sprop_eqb_true : ltac2:(tb__ "0|0|
S12S12S94S5S27R2R1A2S9A3S94S12R3R2A3F_;Fq;Fp;").
Proof. intros p q H. apply sprop_eqb_sound in H. exact H. Qed.

Definition check_ecfg2X (fuel : nat) (cutpcs : list Z) (g : positive) (cuts exits : list lnode)
           (X : nat -> edge -> bool) : bool := ltac2:(tb__ "0|3|
SbSadS2bS2bS10S26S31R1A1A1A1Ln;Vcuts;A3ScS8S2cA1M0A1S5Lx;S39S2aVfuel;Vcutpcs;Vg;S9aS2bS17S31Vcuts;A4S9aS2bS17S31Vexits;A4A6G0SadS6S1S2cA2M1G1S5S5L_;VX;SdS1S2cR1A3SfS1S2cR1A3M2A2S9S3eVg;S4S2bVcuts;Vexits;A3G2A3X5x2Lke;SaeS1S2cS9bU0SeS2cR1A2A2R1A4A3Les;S7Xcx2A2").

Lemma cfg_complete_auto2X : ltac2:(tb__ "0|2|
S1S8S73A1S74S8S2bA1M0G0S19OF_;S1S2cS5F_;F_;S8Sa1A1Sa0OF_;F_;Sa2OF_;S19S19R6R2A1S25RaR3R2A3R8R3A1F_;F_;Fr2;Fr1;S94S5S61RaR9R8R7R6R4A6S9A3S1S2cS94S5R7R2R1A2S9A3S35S9aS2bS32S33R9A1S4S2bRbRaA3A4R2A2F_;Fe;Fk;S2bS19SabS2bR2RaA3RaR2A1Sa3S2aS9dS2aR9S31R4A1M1R3A4Sa2S95S36S2aRaS9aS2bS32S33RcA1ReA4S3fR5R4A2R1A5R9R1A1A2Lw;A3F_;F_;Frho;FE;S2bS19SabS2bR2RcA3RbR2A1Sa3S2aS9dS2aRaG1R3A4R9A3F_;F_;Frho;Fn;F_;F_;F_;F_;FQ;FK;FX;FG;Fexits;Fcuts;Fg;Fcutpcs;Ffuel;").
Proof.
  intros fuel cutpcs g cuts exits G X K Q HG Hchk HX Hexits n rho Hin Hg.
  unfold check_ecfg2X in Hchk. apply andb_prop in Hchk as [Hstrict Hchk].
  destruct (cfg_edges segs fuel cutpcs g (map ln_state cuts) (map ln_state exits)) as [es|] eqn:Hes; [|discriminate].
  change (ln_state n) with (en_state (to_enodeL G n)).
  apply (cfg_complete_gen segs fuel cutpcs g (map (to_enodeL G) cuts) (map (to_enodeL G) exits) es K Q).
  - rewrite forallb_forall in Hstrict |- *. intros x Hx. apply in_map_iff in Hx as (n' & <- & Hn'). exact (Hstrict n' Hn').
  - rewrite !map_map. exact Hes.
  - rewrite <- map_app. apply (Forall_by_index _ (fun k e => if X k e then true else echeck2 g (cuts ++ exits) e) es 0 Hchk).
    intros k e H. destruct (X k e) eqn:Hx.
    + exact (HX k e Hx).
    + exact (echeck2_sound g G _ e HG H).
  - intros E rho' HinE HgE. apply in_map_iff in HinE as (n' & <- & Hn'). exact (Hexits n' rho' Hn' HgE).
  - apply in_map. exact Hin.
  - exact Hg.
Qed.

Definition X_sd (k : nat) (e : edge) : bool := ltac2:(tb__ "0|5|
SbSbSbSbSbSacS1SaaVk;A1S6bA3SaaS3bVe;A1U7M0A2A2SaaS3dVe;A1G0A2A2ScbS3cVe;A1M1S6dA2A2S29ScaG1Pb8M2A2S24Sa8S14G2A1M3S13Z1A1M4A3A2A2ScS12A1S5Lx;SafS12S28S3aVe;A1A1U0A3S12S27R1S1fSa6G4G3A3A2Lf;S7Xcx2A2").

Lemma echeck_sd : ltac2:(tb__ "0|0|
S94S5S61S5bS62S6dS65S66S60A6S9A3").
Proof. unfold check_ecfg2X. rewrite <- (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.cfg_edges_fast_eq segs). vm_cast_no_check (@eq_refl bool true). Qed.

Lemma cp_edge_ok : ltac2:(tb__ "0|0|
S19OF_;S1S2cS19S19R5R2A1S25S6dR3R2A3R7R3A1F_;F_;Fr2;Fr1;S94S5S60R3R2A2S9A3S35S9aS2bS32S33R5A1S4S2bS65S66A3A4R3A2F_;F_;Fe;Fk;FG;").
Proof.
  intros G k e HG H. unfold X_sd in H.
  apply andb_prop in H as [H Hf]. apply andb_prop in H as [H Hs]. apply andb_prop in H as [H Hid]. apply andb_prop in H as [H Htgt]. apply andb_prop in H as [Hk Hsrc].
  apply Nat.eqb_eq in Hsrc. apply Nat.eqb_eq in Htgt. apply sv_eqb_sound in Hs.
  destruct (nth_error (ss_facts (e_leaf e)) 0) as [f|] eqn:Ef; [|discriminate]. apply sprop_eqb_true in Hf. subst f.
  unfold eedge_ok. intros Ti Tj Hi Hj rho rho' Hag Hg HF.
  rewrite nth_error_map, Hsrc in Hi. rewrite nth_error_map, Htgt in Hj. cbn in Hi, Hj.
  injection Hi as <-. injection Hj as <-. cbn [to_enodeL en_state en_ghost en_meas fst snd] in *.
  split.
  - eapply HG; [exact Hg|]. eapply agree_below_trans.
    + eapply (agree_below_le _ NF); [| exact Hag]. cbn. unfold NF, NXC. lia.
    + apply rho_sub_agree. exact Hid.
  - assert (H1 : 1 < bv_unsigned (rw rho' 184%positive)).
    { pose proof (Forall_pick _ _ 0 _ HF Ef) as X. apply holds_bltu in X. rewrite U_lit, eval_var in X.
      unfold M64v in X. rewrite Z.mod_small in X by lia. exact X. }
    assert (E184 : eval rho (SVar 184) = eval rho' (SVar 184)).
    { apply (eval_agree _ rho rho' (SVar 184) Hag). vm_compute. reflexivity. }
    unfold lmeas. cbn [ln_rank ln_vars length lex_val comp_val fst snd base_val Z.of_nat Pos.of_succ_nat Pos.succ Nat.sub LMAX].
    rewrite <- eval_subst. change (sv_subst (e_sub e) (SVar 184)) with (wsub_get (e_sub e) 184). rewrite Hs, E184.
    change (Z.of_nat LMAX) with 4. change (Z.of_nat 0) with 0. change (Z.of_nat 3) with 3.
    pose proof (srlw1_lt rho' (SVar 184) ltac:(rewrite eval_var; exact H1)) as LT.
    pose proof (urange (eval rho' (SAluW ALU_SRL (SVar 184) (SLit 1)))) as R1.
    pose proof (urange (eval rho' (SVar 184))) as R2.
    unfold B64. nia.
Qed.

Lemma eexit_post_L0 : ltac2:(tb__ "0|0|
S8Sa1A1Sa0OF_;F_;S74S19Sa2OF_;S8S97A1S17SabS97S99R1S98A2R2A3S19S25R7R6R1A3Sa3S2aS9dS2aR9R4R2A4Sa2S95R7R1A1S9eS2aRaR9R8R6R1A6A2Lw;A3F_;Frho;F_;FP;Fposts;FX;Frho0;Fn;FK;").
Proof.
  intros K n rho0 X posts P Hin rho Hag w [Hsm Hk]. exists w. split; [apply wsteps_refl|].
  right. exists (mkLeaf P RsSymJump), rho. auto.
Qed.

Theorem scan_double_sum_ex : ltac2:(tb__ "0|0|
S8Sa1A1Sa0OF_;F_;S19Sa3S2aS9dS2aR2S4dR1A4S9eS2aR2S6dR1S5fA5A3Frho;FK;").
Proof.
  intros K rho.
  set (G := fun r => agree_below NF rho r).
  assert (HG : forall r1 r2, G r1 -> agree_below NF r1 r2 -> G r2) by (intros r1 r2 H1 H2; eapply agree_below_trans; eauto).
  change Pre_sd with (ln_state (mkLN Pre_sd 9 [])).
  apply (cfg_complete_auto2X FUEL_sd cutpcs_sd NF lcuts_sd lexits_sd G X_sd K (LQ segs K NF rho Posts_sd) HG echeck_sd).
  - intros k e Hx. exact (cp_edge_ok G k e HG Hx).
  - intros E rhoE HinE HgE.
    unfold lexits_sd, exits_sd in HinE. cbn [map] in HinE.
    destruct HinE as [<-|[<-|[<-|[<-|[]]]]]; cbn [ln_state]; revert HgE.
    + apply eexit_post_L0. in_nth 0.
    + apply eexit_post_L0. in_nth 1.
    + apply eexit_post_L0. in_nth 2.
    + apply eexit_post_L0. in_nth 3.
  - left; reflexivity.
  - apply agree_below_refl.
Qed.
End Lib_scan_double.
