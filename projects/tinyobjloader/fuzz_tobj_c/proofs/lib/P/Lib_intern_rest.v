(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "pair"; "prod"; "nat"; "nil"; "list"; "bool"; "false"; "None"; "true"; "app"; "option"; "Some"; "fst"; "snd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sprop"; "sstate"; "SLit"; "SPUle"; "SVar"; "sobj"; "valuation"; "cell"; "mkCell"; "ss_next"; "SAlu"; "FcsrFrm0"; "mkSS"; "mkObj"; "ss_objs"; "DUnknown"; "ss_regs"; "ss_facts"; "sv_eqb"; "SPUlt"; "holds"; "ob_base"; "smatch"; "SPAlign"; "SPBranch"; "eval"; "ob_hi"; "ob_lo"; "rw"; "ss_pc"; "ob_dflt"; "obj_range"; "sv_below"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVA"; "amode"; "AOpen"; "JGA"; "JLGA"; "JGA_pre"; "ameas"; "drop_last_state"; "PostsCA"; "XA"; "am_below"; "ejcertA"; "malloc_callAT"; "nodeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_intern_rest"; "tv0"; "ahd"; "vJ"; "P0_ir"; "vK"; "cur"; "vE"; "base_facts"; "szq"; "vAR"; "vHD"; "vP"; "vB"; "vDp"; "vH"; "vI"; "vIX"; "vKK"; "vL"; "C_m"; "E_malloc"; "O_D"; "P_fail"; "P_ok"; "am_ok"; "am_open"; "O_ar"; "O_txt"; "P_hdr"; "Pre_ir"; "am_cp"; "am_w"; "am_w2"; "drop_txt"; "fit_facts"; "len"; "tv_m"; "vB_"; "vCAP"; "vN"; "FUEL_ir"; "O_F"; "X_K0"; "X_cp0"; "X_fit"; "X_fnull"; "X_m0"; "X_nofit1"; "X_open"; "X_push"; "X_ret"; "X_ret0"; "X_ret2"; "X_slow0"; "X_tl0"; "X_tr0"; "cutpcs_ir"; "ir_K"; "ir_cp"; "ir_m"; "ir_ret"; "ir_slow"; "ir_tl"; "ir_tr"; "p_fit"; "p_new"; "post_objs"; "spo"; "vNX"; "vU"; "C_K"; "C_cp"; "C_open"; "C_slow"; "C_tl"; "C_tr"; "C_w"; "C_w2"; "O_hdr"; "O_slot"; "T_mnull"; "T_mok"; "T_mok0"; "X_fit3"; "X_push3"; "ar_cells"; "blkN"; "cp_regs"; "drop_cells"; "ir_entry"; "ir_open"; "ir_w"; "ir_w2"; "is_txt"; "pre_regsI"; "run_of"; "two47"; "vCFG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "SPJ"; "jpred"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "C_P"; "topL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "pre_fregs"; "setregs"; "post_regs"; "pre_regs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_intern_rest.Sum"; "z0"; "Posts_ir"; "cutsE"; "exitsE"; "PDA_ir"; "@Stdlib.ZArith.BinInt.Z"; "pow"; "le"; "mul"; "add"; "lt"; "eqb"; "opp"; "@Corelib.Init.Logic"; "eq"; "and"; "ex"; "iff"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract"; "EC_P"; "Pre_malloc"; "J_alloc_pre"; "Posts_malloc"; "L_malloc_null"; "L_malloc_ok"; "MInvR"; "NPOSTM"; "V_RES"; "ec_malloc"; "ok_sideK"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_SUB"; "BC_GE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "jpost"; "LQP"; "agree_vals"; "pos_add_nat"; "J_ofP"; "call_checkP"; "call_linkP"; "import_okP"; "import_post"; "import_sub"; "@Stdlib.Lists.List"; "In"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "etriple"; "triple"; "world"; "@Corelib.Lists.ListDef"; "map"; "firstn"; "Forall"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_absorb"; "rho_sub"; "wsub_get";
"wsub"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "add_facts"; "infer_sub"; "jnode"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface"; "MA"; "ma_L"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "entails_fr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "leaf"; "lf_state"; "sym_run"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "T_after"; "T_ok"; "call_checkT"; "fbin"; "malloc_contracts"; "malloc_contracts_ex"; "pclF"; "robjs_ok"; "tv_below"; "tv_facts"; "tvd"; "tvin"; "tvz"; "@Stdlib.Bool.Bool"; "Is_true"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@stdpp.base"; "filter"; "@stdpp.decidable"; "Is_true_dec"; "@stdpp.list_basics.list"; "list_filter"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import MallocModel MallocInv MallocLayout MallocIface MallocLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymSummary SymObj ExampleMemcpy Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Contract Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CfgGlue CursorGlue ObjXform TobjJV TobjArena TobjJVA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P Require Import Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition ir_entry : Z := 0x1a4e8.
Definition ir_tl : Z := 0x1a520.
Definition ir_tr : Z := 0x1a54c.
Definition ir_m : Z := 0x1a560.
Definition ir_open : Z := 0x1a57c.
Definition ir_slow : Z := 0x1a58c.
Definition ir_K : Z := 0x1a5a4.
Definition ir_w : Z := 0x1a5e4.
Definition ir_w2 : Z := 0x1a668.
Definition ir_cp : Z := 0x1a5ec.
Definition ir_ret : Z := 0x1a624.
Definition FUEL_ir : nat := 300%nat.

Definition vB_ : sv := SVar 12.  Definition vAR : sv := SVar 13.  Definition vHD : sv := SVar 14.  Definition vCFG : sv := SVar 52.
Definition vB : sv := SVar 15.  Definition vI : sv := SVar 16.  Definition vE : sv := SVar 17.  Definition vL : sv := SVar 18.
Definition vDp : sv := SVar 19.
Definition spo (k : Z) : sv := ltac2:(tb__ "0|0|
S1aSc8S14PaA1S12Vk;A1A3").
Definition two47 : Z := 2 ^ 47.
Definition cur (off : sv) : sv := SAlu ALU_ADD vB off.

Definition base_facts : list sprop := ltac2:(tb__ "0|9|
S0S10S27PaM0Z4M1A2S0S10S28ScaS12N310A1S4eA3S0S10S28ScaS4eS12Sb7Sb1Z2M2Z28A2A1A1A3S0S10S13S14P1eA1M3S1aSc8S84N40A1M4S4eA3A2S0S10S13G3G4A2S0S10S13G3S14G0A1M5A2S0S10S13G5S12Sa1A1M6A2S0S10S13S50S47A2S0S10S13S47S53A2S0S10S13S53S12Sb1G2Z20A2A1A2S0S10S13S12Z1000A1M7S4dA2S0S10S13S4dG6A2S0S10S13G3S66A2S0S10S13S66G6A2S0S10S13G7S4aA2S0S10S13S1aSc8S4aS12Z40A1A3S12Z7fffff800000A1M8A2S0S10S13S4aG8A2S0S10S27PdG1A2S0S10S13S4bG8A2S0S10S13S12Z7fff7f800000A1G3A2S0S10S13G3G8A2S4S10A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").

Definition pre_regsI : list sv := ltac2:(tb__ "0|1|
Sa9SabS0S2S3SfA2M0S1S3SfUbS46S50A1A4S0G0S1S3SfUcS46S47A1A4S4G0A1A3A3A2").
Definition O_F (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S1dS14PaA1S12N40A1S12Z0A1Vcells;S1fA5").
Definition O_D : sobj := ltac2:(tb__ "0|0|
S1dS84N40A1S4eS12Z0A1S4S17A1S1fA5").

Definition P_hdr : sobj := ltac2:(tb__ "0|2|
S1dS66S12Z8M0A1M1S12Z20A1S0S17S18G1G0S4aA3S0S17S18S12Z10A1G0S12Z0A1A3S0S17S18S12Z18A1G0Sa2A3S4S17A1A3A3A3S1fA5").
Definition ar_cells (hd : sv) : list cell := ltac2:(tb__ "0|2|
S0S17S18S12Z0A1M0Z8M1S12Z13858A1A3S0S17S18S12G1A1G1S12Z13864A1A3S0S17S18S12Z10A1G1G0A3S0S17S18S12Z18A1G1S12Z13878A1A3S0S17S18S12Z20A1G1G0A3S0S17S18S12Z28A1G1G0A3S0S17S18S12Z30A1G1Vhd;A3S0S17S18S12Z38A1G1S12Z10000A1A3S4S17A1A3A3A3A3A3A3A3A3").
Definition O_ar (hd : sv) : sobj := ltac2:(tb__ "0|0|
S1dS4aS12Z0A1S12Z40A1S96Vhd;A1S1fA5").
Definition O_txt : sobj := ltac2:(tb__ "0|0|
S1dS4dS12Z0A1S53S4S17A1S1fA5").
Definition O_hdr (hd nx cap u : sv) : sobj := ltac2:(tb__ "0|2|
S1dVhd;S12Z0A1M0S12Z18A1S0S17S18G0Z8M1Vnx;A3S0S17S18S12G1A1G1Vcap;A3S0S17S18S12Z10A1G1Vu;A3S4S17A1A3A3A3S1fA5").
Definition O_slot (p sz : sv) : sobj := ltac2:(tb__ "0|0|
S1dVp;S12Z0A1Vsz;S4S17A1S1fA5").

Definition Pre_ir : sstate := ltac2:(tb__ "0|0|
S1cS9aS9fSa8S1bS8SfA1S0S15S6aS4S17A1A1S0S15S56S0S15S5dS0S15S5bS4bA1S0S15S5cS4S15A1A3A3A3A3A3S48Sa7S7A9").
Definition tv0 : list (sv * sv) := ltac2:(tb__ "0|1|
S0S2SfSfA2M0S1SfSfS4aS12Z40A1A4S4G0A1A3").
Definition ahd : amode := AHead vHD.

Definition cutpcs_ir : list Z := ltac2:(tb__ "0|0|
S0S31S7fS0S31S80S0S31S7cS0S31S9bS0S31S7eS0S31S7aS0S31S9cS0S31S9dS0S31S7bS0S31Sc6SbdA1S4S31A1A3A3A3A3A3A3A3A3A3A3").
Definition run_of (S : sstate) : list sstate := ltac2:(tb__ "0|1|
SbS5SefA1M0A1S5S11A1Lx;Sf1S33S69S79VS;S9A5G0SdcSefS11Sf0R1A4Lls;S4S11A1Xbx2").
Definition leaves_at (S : sstate) (pc : Z) : list sstate := ltac2:(tb__ "0|1|
S101S11S5S11A1S103S11A1S11SffSb6S2dR1A1Vpc;A2M0A1Ll;S11S102G0A1Lx;Sa0VS;A1A6").
Definition optR (x : option (list sobj)) : list sobj := match x with Some r => r | None => [] end.
Definition drop_cells (o : sobj) : sobj := ltac2:(tb__ "0|0|
S1dS25Vo;A1S2bVo;A1S2aVo;A1S4S17A1S2eVo;A1A5").
Definition drop_txt (o : sobj) : sobj := ltac2:(tb__ "0|0|
S6S15L_;S22S25Vo;A1S4dA2S99Vo;A1Vo;X6x2").
Definition show (l : sstate) : ltac2:(tb__ "0|0|
S2S2S2S31S32A2S5SfA1A2S5S10A1A2") := ltac2:(tb__ "0|2|
S1S2S2S31S32A2M0S5SfA1M1A2S5S10A1S1G0G1S1S31S32S2dVl;A1S19Vl;A1A4SddSfU14S20Vl;A1A3A4SddS10U4S21Vl;A1A3A4").

Definition vJ : sv := SVar 100.  Definition vK : sv := SVar 101.
Definition X_tl0 : sstate := Eval vm_compute in nth 0 (leaves_at Pre_ir ir_tl) Pre_ir.
Definition C_tl : sstate := ltac2:(tb__ "0|1|
S1cS7fSa9S20S77A1S0S2S3SfA2M0S1S3SfUbS46S43A1A4S0G0S1S3SfUfS14P66A1A4S4G0A1A3A3A2Sa8S1bS8SfA1SdcS15S15S62S1eS77A1A4SaS10S0S10S23S43S47A2S0S10S13S50S43A2S0S10S13S43S12Sb1Z2Z20A2A1A2S4S10A1A3A3A3S48A3P67S7A9").

Definition X_tr0 : sstate := Eval vm_compute in nth 0 (leaves_at C_tl ir_tr) Pre_ir.
Definition C_tr : sstate := ltac2:(tb__ "0|2|
S1cS80Sa9S20S78A1S0S2S3SfA2M0S1S3SfUbS46S43A1A4S0G0S1S3SfUcS46S45A1A4S0G0S1S3SfUfS14P66A1A4S4G0A1A3A3A3A2Sa8S1bS8SfA1SdcS15S15S62S1eS78A1A4SaS10S0S10S23S43S45A2S0S10S13S45S47A2S0S10S13S50S43A2S0S10S13S43S12Sb1Z2Z20A2A1M1A2S0S10S13S45G1A2S4S10A1A3A3A3A3A3S48A3P67S7A9").

Definition X_m0 : sstate := Eval vm_compute in nth 0 (leaves_at Pre_ir ir_m) Pre_ir.
Definition C_m : sstate := ltac2:(tb__ "0|2|
S1cS7cSa9S20S6fA1S0S2S3SfA2M0S1S3SfUbS46S43A1A4S0G0S1S3SfUcS46S45A1A4S0G0S1S3SfUdS14P66A1A4S0G0S1S3SfUeS14P67A1A4S0G0S1S3SfUfS14P68A1A4S4G0A1A3A3A3A3A3A2Sa8S1bS8SfA1SdcS15S15S62S1eS6fA1A4SaS10S0S10S13S43S45A2S0S10S13S45S47A2S0S10S13S50S43A2S0S10S13S43S12Sb1Z2Z20A2A1M1A2S0S10S13S45G1A2S4S10A1A3A3A3A3A3S48A3P69S7A9").
Definition len : sv := SAlu ALU_SUB vK vJ.
Definition szq : sv := SAlu ALU_ADD len (SLit 1).

Definition X_open : sstate := Eval vm_compute in nth 0 (leaves_at C_m ir_open) Pre_ir.
Definition C_open : sstate := Eval vm_compute in open_state X_open vHD.
Definition am_open : amode := ltac2:(tb__ "0|0|
S35S4bS14P69A1S14P6aA1S4S2SfSfA2A1A4").
Definition X_fit : sstate := Eval vm_compute in nth 0 (leaves_at C_open ir_w) Pre_ir.
Definition n_nofit : nat := Eval vm_compute in length (leaves_at C_open ir_slow).
Definition X_nofit1 : sstate := Eval vm_compute in nth 0 (leaves_at C_open ir_slow) Pre_ir.
Definition X_nofit1c : sstate := Eval vm_compute in drop_last_state X_nofit1 (firstn 5 (ss_objs X_nofit1)).

Definition p_fit : sv := Eval vm_compute in nth 10 (ss_regs X_fit) (SLit 0).
Definition X_fit3 : sstate := Eval vm_compute in carve_state X_fit p_fit szq.
Definition fit_facts (p : sv) : list sprop := ltac2:(tb__ "0|1|
S0S10S13S12Z1000A1Vp;A2S0S10S13Vp;S12Z7fffff800000A1M0A2S0S10S13S1aSc8Vp;S49A3G0A2S4S10A1A3A3A3").
Definition X_fit4 : sstate := ltac2:(tb__ "0|0|
Se8S63S81A1S94A2").

Definition X_slow0 : sstate := Eval vm_compute in nth 0 (leaves_at C_m ir_slow) Pre_ir.
Definition C_slow : sstate := ltac2:(tb__ "0|1|
S1cS7eSa9S20S76A1S0S2S3SfA2M0S1S3SfUdS14P6cA1A4S0G0S1S3SfUeS14P6dA1A4S0G0S1S3SfUfS14P6eA1A4S0G0S1S3SfU10S14P6fA1A4S4G0A1A3A3A3A3A2Sa8S1bS8SfA1S1eS76A1S21S54A1P70S7A9").
Definition X_K0 : sstate := Eval vm_compute in nth 0 (leaves_at C_slow ir_K) Pre_ir.
Definition vKK : sv := SVar 112.
Definition C_K : sstate := ltac2:(tb__ "0|1|
S1cS7aSa9S20S6bA1S0S2S3SfA2M0S1S3SfU13S52A4S4G0A1A3A2Sa8S1bS8SfA1S1eS6bA1SaS10S0S10S13S1aSc8S49S12Z1A1A3S52A2S0S10S13S52S12Sb1Z2Z29A2A1A2S4S10A1A3A3S21S54A1A3P71S7A9").
Definition E_malloc : sstate := Eval vm_compute in nth 0 (leaves_at C_K (ec_malloc EC_P)) Pre_ir.
Definition s_malloc : wsub := ltac2:(tb__ "0|0|
S0S2S32SfA2S1S32SfPfS4eA4Se9PaS55SbeSbdA1A3A3").
Definition R_malloc : list sobj := Eval vm_compute in optR (entails_fr E_malloc (Pre_malloc EC_P) s_malloc).
Definition vN : positive := 123.
Definition blkN : sv * sv := ltac2:(tb__ "0|0|
S1SfSfS14S68A1S1aSc8S52S12Z20A1A3A4").
Definition tv_m : list (sv * sv) := blkN :: tv0.
Definition T_mnull : sstate := Eval vm_compute in T_after E_malloc s_malloc R_malloc (L_malloc_null EC_P).
Definition T_mok0 : sstate := Eval vm_compute in T_after E_malloc s_malloc R_malloc (L_malloc_ok EC_P).
Definition T_mok : sstate := ltac2:(tb__ "0|0|
Se8SfbS97A1S93A2").

Definition X_push : sstate := Eval vm_compute in nth 0 (leaves_at T_mok ir_w2) Pre_ir.
Definition sel_push : list nat := ltac2:(tb__ "0|0|
S0S3U2S0S3U0S0S3U3S0S3U4S0S3U5S0S3U1S4S3A1A3A3A3A3A3A3").
Definition X_push1 : sstate :=
  Eval vm_compute in match apply_xforms X_push [XSelect sel_push; XSplit 5 (SLit 24)] with Some St => St | None => Pre_ir end.
Definition X_push2 : sstate := Eval vm_compute in drop_last_state X_push1 (firstn 6 (ss_objs X_push1)).
Definition p_new : sv := ltac2:(tb__ "0|0|
S1aSc8S14S68A1S12Z20A1A3").
Definition X_push3 : sstate := Eval vm_compute in carve_state X_push2 p_new szq.
Definition used_new : sv := Eval vm_compute in c_val (nth 0 (ob_cells (nth 5 (ss_objs X_push1) O_D)) (mkCell (SLit 0) 8 (SLit 0))).
Definition X_push4 : sstate := ltac2:(tb__ "0|0|
Se8S63S82A1S95A2").

Definition C_w : sstate := Eval vm_compute in X_fit4.
Definition am_w : amode := ltac2:(tb__ "0|1|
S35S4bS14P69A1S14P6aA1S0S2SfSfA2M0S1SfSfS81S49A4S4G0A1A3A4").
Definition C_w2 : sstate := Eval vm_compute in X_push4.
Definition am_w2 : amode := ltac2:(tb__ "0|1|
S35S14S68A1S4bS52S0S2SfSfA2M0S1SfSfS82S49A4S4G0A1A3A4").

Definition vH : sv := SVar 160.  Definition vNX : sv := SVar 161.  Definition vCAP : sv := SVar 162.
Definition vU : sv := SVar 163.  Definition vP : sv := SVar 164.   Definition vIX : sv := SVar 165.
Definition am_cp : amode := ltac2:(tb__ "0|1|
S35S4fS85S67S0S2SfSfA2M0S1SfSfS4cS49A4S4G0A1A3A4").
Definition X_cp0 : sstate := Eval vm_compute in nth 0 (leaves_at C_w ir_cp) Pre_ir.
Definition cp_regs : list sv := ltac2:(tb__ "0|1|
Sa9S20S6cA1S0S2S3SfA2M0S1S3SfU1S14Pa6A1A4S0G0S1S3SfU8S1aSc8S4cS64A3A4S0G0S1S3SfUaS4cA4S0G0S1S3SfUbS1aSc8S46S43A1S51A3A4S0G0S1S3SfUcS1aSc8S4cS51A3A4S0G0S1S3SfUdS14Pa7A1A4S0G0S1S3SfUeS14Pa8A1A4S0G0S1S3SfUfS14Pa9A1A4S0G0S1S3SfU10S14PaaA1A4S0G0S1S3SfU11S14PabA1A4S0G0S1S3SfU5S14PacA1A4S0G0S1S3SfU6S14PadA1A4S0G0S1S3SfU7S14PaeA1A4S0G0S1S3SfU1cS14PafA1A4S0G0S1S3SfU1dS14Pb0A1A4S0G0S1S3SfU1eS14Pb1A1A4S0G0S1S3SfU1fS14Pb2A1A4S0G0S1S3SfU13S14Pb3A1A4S0G0S1S3SfU14S14Pb4A1A4S0G0S1S3SfU15S14Pb5A1A4S4G0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A2").
Definition C_cp : sstate := ltac2:(tb__ "0|0|
S1cS7bS98Sa8S1bS8SfA1S0S15SdfS15U0S1eS6cA1S56A4S0S15S56S0S15S5dS0S15S5bS4fA1S0S15S5cS0S15S8fS4fS85S67S86A4S0S15S90S4cS49A2S4S15A1A3A3A3A3A3A3A3SaS10S0S10S23S51S64A2S0S10S13S51S12Sb1Z2Z20A2A1A2S0S10S13S86S67A2S0S10S13S12Z1000A1S4fA2S0S10S13S4fS12Z7fffff800000A1A2S4S10A1A3A3A3A3A3SaS10S63S4cA1S21S54A1A3A3Pb6S7A9").

Definition X_ret : sstate := Eval vm_compute in nth 0 (leaves_at C_cp ir_ret) Pre_ir.
Definition X_ret0 : sstate := Eval vm_compute in nth 0 (leaves_at C_w ir_ret) Pre_ir.
Definition X_ret2 : sstate := Eval vm_compute in nth 0 (leaves_at C_w2 ir_ret) Pre_ir.
Definition glue2 (X : sstate) : sstate := ltac2:(tb__ "0|0|
S3aVX;SddS15U6S1eVX;A1A3A2").
Definition glue3 (X : sstate) : sstate := ltac2:(tb__ "0|0|
S3aVX;SddS15U5S1eVX;A1A3A2").
Definition X_ret_b : sstate := Eval vm_compute in glue2 X_ret.    Definition X_ret_c : sstate := Eval vm_compute in glue3 X_ret_b.
Definition X_ret0_b : sstate := Eval vm_compute in glue2 X_ret0.  Definition X_ret0_c : sstate := Eval vm_compute in glue3 X_ret0_b.
Definition X_ret2_b : sstate := Eval vm_compute in glue2 X_ret2.  Definition X_ret2_c : sstate := Eval vm_compute in glue3 X_ret2_b.

Definition X_fnull : sstate := Eval vm_compute in nth 0 (leaves_at T_mnull ir_ret) Pre_ir.
Definition X_fnull1 : sstate :=
  Eval vm_compute in match apply_xforms X_fnull [XSelect [1; 0; 2; 3; 4]%nat] with Some St => St | None => Pre_ir end.

Definition post_objs (hd : sv) : list sobj := ltac2:(tb__ "0|0|
S0S15S6aS4S17A1A1S0S15S56S0S15S5dS0S15S5bVhd;A1S0S15S5cS4S15A1A3A3A3A3A3").
Definition P_fail : sstate := ltac2:(tb__ "0|1|
S1cS7dSa9SaaSa7A1S0S2S3SfA2M0S1S3SfUaS12Z0A1A4S4G0A1A3A2Sa8S1bS8SfA1S83S4bA1S48Sc4S7A9").
Definition P_ok : sstate := ltac2:(tb__ "0|5|
S1cS7dSa9SaaSa7A1S0S2S3SfA2M0S1S3SfUaS14P8cA1M1A4S4G0A1A3A2Sa8S1bS8SfA1S83S14P8dA1M2A1SaS10S0S10S13S12Z1000A1M3G1A2S0S10S13G1S12Z7fffff800000A1M4A2S0S10S13G3G2A2S0S10S13G2G4A2S4S10A1A3A3A3A3S48A3P8eS7A9").
Definition am_ok : amode := AHead (SVar 141).

Definition s_ret : wsub := infer_sub 100 X_ret_c P_ok.
Definition s_ret0 : wsub := infer_sub 100 X_ret0_c P_ok.
Definition s_ret2 : wsub := infer_sub 100 X_ret2_c P_ok.
Definition s_fnull : wsub := infer_sub 100 X_fnull1 P_fail.
Definition s_nofit1 : wsub := infer_sub 100 X_nofit1c C_slow.

Definition is_txt (o : sobj) : bool := ltac2:(tb__ "0|1|
S6S6L_;M0S22S25Vo;A1S4dA2G0S22S2bVo;A1S12Z0A1A2S22S2aVo;A1S53A2S7X6x2S7X6x2").

Goal call_checkP E_malloc (Pre_malloc EC_P) s_malloc R_malloc [L_malloc_null EC_P; L_malloc_ok EC_P] = true /\ length R_malloc = 4%nat
     /\ ss_next E_malloc = 113%positive /\ wsub_get (import_sub s_malloc NF (L_malloc_ok EC_P) (ss_next E_malloc)) V_RES = SVar vN.
Proof. vm_compute. repeat split; reflexivity. Qed.
Goal n_nofit = 1%nat /\ length (run_of C_open) = 2%nat /\ length (run_of T_mok) = 1%nat /\ length (run_of C_w) = 2%nat /\ length (run_of C_w2) = 2%nat.
Proof. vm_compute. repeat split; reflexivity. Qed.
Goal entails X_ret_c P_ok s_ret = true /\ entails X_ret0_c P_ok s_ret0 = true /\ entails X_ret2_c P_ok s_ret2 = true
     /\ entails X_fnull1 P_fail s_fnull = true /\ entails X_nofit1c C_slow s_nofit1 = true.
Proof. vm_compute. repeat split; reflexivity. Qed.

Definition P0_ir (FB : list (Z * Z)) (r : valuation) : Prop := ltac2:(tb__ "0|2|
SbaS31S31SbaS31S31Sb9Sd5S2S31S31A2S1S31S31R2R1A4VFB;A3Sb9Sb2R2Se4Q40M0S2cVr;PfA2A2M1A2Sb2Sb4G1Se4G0S2cVr;P12A2A2A2Sb4R2R1A2A2A2A2Ln;A2Lb;A2").

Section Sum.
Variable ok : world -> Prop.
Variable Kc : ltac2:(tb__ "0|0|
S5Sd7A1Sd6OF_;F_;").
Variable FB : list (Z * Z).
Variable rho0 : valuation.
Hypothesis HS : ltac2:(tb__ "0|0|
Sc7S33Vok;VKc;A3").
Hypothesis ML : malloc_laws segs C_P.
Hypothesis MC : ltac2:(tb__ "0|0|
Sf6S33Sa5SbdA3").

Definition Posts_ir : list (sstate * jpost) := ltac2:(tb__ "0|2|
S0S2S11ScbA2M0S1S11ScbS57S37S33Sa5VKc;S44VFB;A1M1VFB;S41S42A7A4S0G0S1S11ScbS58S37S33Sa5VKc;G1VFB;S41S59A7A4S4G0A1A3A3").
Definition PDA_ir : list (sstate * (list (sv * sv) * amode)) := ltac2:(tb__ "0|3|
S0S2S11S2S5S2SfSfA2A1M0S34A2M1A2M2S1S11G1S57S1G0S34S41S42A4A4S0G2S1S11G1S58S1G0S34S41S59A4A4S4G2A1A3A3").
Lemma Posts_ir_PDA : ltac2:(tb__ "0|0|
Sb8S5S2S11ScbA2A1SadS3bS33Sa5VKc;S44Sb0VFB;A6A3").
Proof using . reflexivity. Qed.

Let nA : ltac2:(tb__ "0|0|
S2S11S2S5S2SfSfA2A1S34A2A2SeaFn;") := ltac2:(tb__ "0|0|
S40S33Sa5Sa7VKc;Vrho0;S44VFB;A1VFB;A7").
Let JGv (tv : list (sv * sv)) (am : amode) : jpred := ltac2:(tb__ "0|0|
S36S33Sa5Sa7VKc;Vrho0;S44VFB;A1VFB;Vtv;Vam;A9").
Let Q : assn := ltac2:(tb__ "0|0|
SccS33Sa7Vrho0;SadA4").

Definition z0 : sv := SLit 0.
Definition cutsE : list aedesc := ltac2:(tb__ "0|7|
S0S2S2S11S2S5S2SfSfA2A1M0S34A2M1A2M2S2S31SfA2M3A2M4S1G2G3S1S11G1S5eS1G0S34S41S42A4M5A4S1S31SfZ64SacA4A4S0G4S1G2G3S1S11G1S8bG5A4S1S31SfZ60S1aSc9S47S43A3A4A4S0G4S1G2G3S1S11G1S8cG5A4S1S31SfZ5eS45A4A4S0G4S1G2G3S1S11G1S54G5A4S1S31SfZ5cSacA4A4S0G4S1G2G3S1S11G1S89S1G0S34S41S5aA4A4S1S31SfZ5aSacA4A4S0G4S1G2G3S1S11G1S8aG5A4S1S31SfZ50SacA4A4S0G4S1G2G3S1S11G1S87G5A4S1S31SfZ4bSacA4A4S0G4S1G2G3S1S11G1S91G5A4S1S31SfZ41SacA4M6A4S0G4S1G2G3S1S11G1S92S1G0S34S65S42A4A4G6A4S0G4S1G2G3S1S11G1S8dS1G0S34S41S60A4A4S1S31SfZ54SacA4A4S0G4S1G2G3S1S11G1S8eS1G0S34S41S61A4A4S1S31SfZ3aSacA4A4S0G4S1G2G3S1S11G1S88S1G0S34S41S5fA4A4S1S31SfZ32S1aSc9S64S51A3A4A4S4G4A1A3A3A3A3A3A3A3A3A3A3A3A3").
Definition exitsE : list aedesc := ltac2:(tb__ "0|a|
S0S2S2S11S2S5S2SfSfA2A1M0S34A2M1A2M2S2S31SfA2M3A2M4S1G2G3S1S11G1S71S1G0S34S41S42A4M5A4S1S31SfZ5bSacA4A4S0G4S1G2G3S1S11G1S6dS1G0S34S41S5aA4M6A4S1S31SfZ55SacA4M7A4S0G4S1G2G3S1S11G1S70G6A4G7A4S0G4S1G2G3S1S11G1S55G5A4S1S31SfZ46SacA4A4S0G4S1G2G3S1S11G1S72S1G0S34S65S42A4A4S1S31SfZ3cSacA4A4S0G4S1G2G3S1S11G1S73S1G0S34S41S5fA4A4S1S31SfZaSacA4M8A4S0G4S1G2G3S1S11G1S74S1G0S34S41S60A4A4G8A4S0G4S1G2G3S1S11G1S75S1G0S34S41S61A4A4G8A4S0G4S1G2G3S1S11G1S6eG5A4G8A4S0G4S1G2G3S1S11G1S57G5A4S1S31SfZ0SacA4M9A4S0G4S1G2G3S1S11G1S58S1G0S34S41S59A4A4G9A4S4G4A1A3A3A3A3A3A3A3A3A3A3A3").
Lemma ejcert_ok : ltac2:(tb__ "0|0|
Sb8S6S3eS33Sa7S69S79P64SaeSafA7S9A3").
Proof using . vm_cast_no_check (@eq_refl bool true). Qed.

Lemma P0_at : ltac2:(tb__ "0|0|
S16ScdSa7Vrho0;R1A3S44VFB;Vrho0;A2S44VFB;R3A2F_;F_;Frho;").
Proof using .
  intros rho Hav HP0.
  assert (E15 : rw rho 15%positive = rw rho0 15%positive) by (symmetry; apply (proj1 Hav); reflexivity).
  assert (E18 : rw rho 18%positive = rw rho0 18%positive) by (symmetry; apply (proj1 Hav); reflexivity).
  unfold P0_ir. rewrite E15, E18. exact HP0.
Qed.

Lemma txt_pclF : ltac2:(tb__ "0|1|
S5S15A1S5S10A1S16S15S31Sd5S15R2R5A3Sb8S6S9eR3A1S9A3S44VFB;Vrho0;A2ScdSa7Vrho0;R6A3SdeS10S24R7A1R8A3Sd5S10S13S53S12Sb1Z2Z20A2A1A2R9A3Sb9Sb2SdS31S31S2fR9R8A2M0A3R7A2Sb5R7SeS31S31G0A3A2A2Sf8S33Sa5Vrho0;VFB;R8A5F_;F_;F_;F_;F_;F_;F_;Fa;Fo;Frho;Ffacts;FR;").
Proof using .
  intros R facts rho o a _ Ho HP0 Hav HF Hin Hr. unfold is_txt in Ho.
  apply lazy_andb_prop in Ho as [Hb Ho]. apply lazy_andb_prop in Ho as [Hl Hh].
  apply sv_eqb_sound in Hb. apply sv_eqb_sound in Hl. apply sv_eqb_sound in Hh.
  destruct (P0_at rho Hav HP0) as (b & n & Hbin & H1 & H2).
  unfold obj_range, obj_lo_of, obj_hi_of in Hr. rewrite Hb, Hl, Hh in Hr. cbn [fst snd] in Hr.
  rewrite soff_lit_small in Hr by lia. unfold soff in Hr. rewrite bv_signed_U in Hr.
  pose proof (proj1 (Forall_forall _ _) HF _ Hin) as HL. cbn [holds] in HL. rewrite U_lit in HL. unfold vL, vB in *. rewrite !eval_var in *.
  unfold M64v in HL. rewrite Z.mod_small in HL by lia.
  destruct (Zsigned_spec (bv_unsigned (rw rho 18%positive))) as [[_ X]|[X _]]; [|lia]. rewrite X in Hr.
  right; right. exists b, n. split; [exact Hbin | lia].
Qed.
Ltac in_list := cbn; repeat (first [left; reflexivity | right]).
Ltac by_txt := intros o a Ho Hx HP0 Hav HF Hr; eapply (txt_pclF _ _ _ o a Ho Hx HP0 Hav HF); [in_list | exact Hr].

Section SumT.
Variable TR : assn -> assn -> Prop.
Variable FAM : Z -> assn.
Hypothesis TR_facts : ltac2:(tb__ "0|1|
Sa4S11S16Sd8SdeS10S24R2A1S21R3A1A3VTR;Sa3S33R5R4R3A4R2A2M0F_;G0F_;FQ';Frho;FS;FJ;").
Hypothesis TR_ex : forall (A : Type) (J : A -> jpred) S rho (Q' : assn),
  (forall x, TR (SPJ segs (J x) S rho) Q') -> TR (SPJ segs (fun r t m => exists x, J x r t m) S rho) Q'.
Hypothesis TR_pre : ltac2:(tb__ "0|0|
Sd8Sd8Sd8SdbR3R1A1R5R2A1F_;Fw;VTR;R4R2A2VTR;R4R3A2F_;F_;FQ';FP';FP;").
Hypothesis TR_exw : forall (A : Type) (P : A -> assn) (Q' : assn), (forall a, TR (P a) Q') -> TR (fun w => exists a, P a w) Q'.
Hypothesis TR_callP : ltac2:(tb__ "0|3|
Sa4Sa4S11S11Se3S5S15A1M0S5S2S11ScbA2M1A1Sd8S16Sb8SbG0A1SeeR7R6R5A3ScG0R4A2A3Sb8S6Sd0R8R7R6R5SdcG1S11SdS11ScbA2R4A4A5S9A3S16VTR;Sa3S33RbR9R1A4SccS33S19R9A1R1R6A4A2Frho1;S5Sd7A1M2Se5Sd6S26S33R7RdS1G2Se6R3Se7R2R1A2A4A4R10R8R4R2A3R10Se1Se0R9RcR4A3RdA2R5R3A3F_;F_;Fmd;Fms;Ftr;S11ScbG2Se5Sd6S16G2Se5Sd6Sd5G1S1S11ScbR9R8A4R10A3S26S33RfR15S1G2Se6R8Se7R7R6A2A4A4R18R10R9R7A3ScdS19R16A1Se1Se0R11R14R9A3R15A2R7A3S26S33R8RdS1G2Se6R7Se7R6R5A2A4A4RdSe1Se0R13R16RbA3R17A2R9R8R6A4Sb9Sd2R14RcR17R18R19RfRaA7S16Sd1R15RdR18R19R1aR1bR10R1RbA9VTR;Sa3S33ScfR10Se1Se0R16R19ReA3R1aA2RcA3Sd3R1aS19R1bA1R11S19R1cA1R19A5R2A4R17A2F_;Frho';A2F_;F_;F_;F_;F_;F_;Fmd';Fms';Ftr';FrhoL;Fmd;Fms;Ftr;FJL;FL;VTR;Sa3S33ReRcR6A4R7A2F_;F_;F_;F_;F_;Frho;FQ';FPosts;FR;Fs;FPre;FC;FJp;FJ;").
Hypothesis CMALLOC : ltac2:(tb__ "0|0|
SebS16VTR;Sa3S33SbfS33Sa5R2VKc;A4SbeSbdA1R1A4SccS33Sa7R1Sc0S33Sa5SbdR2VKc;A5A4A2Frho1;FAi;").
Hypothesis REENTER : ltac2:(tb__ "0|4|
S11S5S2SfSfA2A1M0S34S31SfS16S31Sd5S2S2S11S2G0S34A2M1A2M2S2S31SfA2M3A2S1G2G3S1S11G1R7S1G0S34R6R5A4A4S1S31SfR4R3A4A4SaeA3Sb2Z0R5A2Sb2Sb3Sb4R6Z1A2Sb1Z2Z40A2A2R3A2VTR;Sa3S33VJGv;R9R8A2RaR5A4VFAM;R4A1A2F_;F_;F_;Fb;Frho;FvT;FrT;Fam;Ftv;FT;").
Hypothesis POST : ltac2:(tb__ "0|0|
S11S5S2SfSfA2A1S34S16S31Sd5S2S11ScbA2S1S11ScbR5S37S33Sa5VKc;S44VFB;A1VFB;R4R3A7A4SadA3VTR;Sa3S33VJGv;R5R4A2R6R3A4VFAM;R2A1A2F_;Fb;Frho;Fam;Ftv;FP;").

Let MALLOC : ltac2:(tb__ "0|a|
S11Se3S5S15A1M0S16S5S2SfSfA2M1A1S34Sd8SebS16VTR;Sa3S33SbfS33Sa5R2VKc;A4SbeSbdA1M2R1A4SccS33SedR1Sc0S33Sa5SbdR2VKc;A5A4A2Frho1;FAi;Sb8SbG0A1SeeR8G2R7A3ScG0R6A2A3Sb8S6Sf4Sa5Sa7R9G2R8R7S0S11Sc1SbdA1M3S0S11Sc2SbdA1M4S4S11A1A3A3A7S9A3Sb8S6S100Sa7S19RaA1A2S9A3Sb8S6SfaS19RbA1R7A2S9A3Sb8S6S3dS19RcA1R7A2S9A3Sb8S6S30S19RdA1Se2RcPcM5A2A2S9A3Sb8SfSe2Sd4RdSedG4S19ReA1M6A4Sc5A2S14SceG6UaM7A2A1A3SebSdeS10S24RdA1S21R10A1A3S44VFB;Vrho0;A2ScdSa7Vrho0;RfA3Sf5VFB;R4A2SfdVFB;R5R11R10A4SfcR12R11A2SfeR13R12A2S3cVFB;R12R8R14R13A5SbaS16S16SbaSd6Sd6Sc3S33Sa5RbR2R1A5Lmd;A2LrhoM;A2Sf3R16Sa6SecRaA1A1A2Sb9Sf9S33Sa5RbS8S31A1R17R18A6Sb5Z0Se4Q40S29R17Se2R19G5A2A2A2A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FAi;S16ScdS19R11A1ReR1A3VTR;Sa3S33S36S33Sa5Sa7VKc;Vrho0;S44VFB;A1M8VFB;ReRdA9M9Sf2R12R11R10G3A4R2A4RcA2F_;Frho';S16ScdS19R12A1RfR1A3VTR;Sa3S33S36S33Sa5Sa7VKc;Vrho0;G8VFB;S0G1S1SfSfS14SceS19R13A1G7A2A1Se2R12G5A2A4RfA3ReA9Sf2R13R12R11G4A4R2A4RdA2F_;Frho';VTR;Sa3S33G9R12RfA4RcA2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Fam;Ftv;Frho;FR;Fs;FCl;") := ltac2:(tb__ "0|0|
S3fS33Sa5SbdSa7VKc;Vrho0;S44VFB;A1VFB;VML;VTR;VTR_facts;VTR_ex;VTR_pre;VTR_callP;Ae").

Lemma bound_ge : ltac2:(tb__ "0|3|
S31S31S16SfSbbSb2Sb3Sb4R4Z1A2M0Sb1Z2Z40A2M1A2Sb4Sb3R3G1A2Se4Q40S29R2R1A2A2A2A2M2SbcSb2G0R3A2G2A2A2Fv;Frho;Fb;Fr;").
Proof using . intros. pose proof (urange (eval rho v)). nia. Qed.
Ltac reenter T tv am rT vT := apply (REENTER T tv am rT vT); [cbn; tauto | lia | first [lia | unfold ameas, ad_rank, ad_var; cbn [fst snd]; apply bound_ge; left; lia]].
Ltac via_ex T tv am rT vT :=
  apply (TR_pre (fun w => exists r, SPJ segs (JGv tv am) T r w)); [ | apply TR_exw; intros r; reenter T tv am rT vT ].

Lemma X_P_fail : ltac2:(tb__ "0|0|
S16S31VTR;Sa3S33VJGv;S41S42A2S57R2A4VFAM;R1A1A2Fb;Frho;").
Proof using POST nA. intros rho b. apply POST. cbn. tauto. Qed.
Lemma X_P_ok : ltac2:(tb__ "0|0|
S16S31VTR;Sa3S33VJGv;S41S59A2S58R2A4VFAM;R1A1A2Fb;Frho;").
Proof using POST nA. intros rho b. apply POST. cbn. tauto. Qed.

Lemma X_open_ok : ltac2:(tb__ "0|0|
S16S31Sb2Sb3Z5bSb1Z2Z40A2A2R1A2VTR;Sa3S33VJGv;S41S42A2S71R3A4VFAM;R2A1A2F_;Fb;Frho;").
Proof using ML REENTER TR_exw TR_pre nA.
  intros rho b Hb. via_ex C_open tv0 am_open 90 z0.
  intros w Hw.
  destruct (JGA_open segs C_P NF Kc rho0 (P0_ir FB) FB ML TobjJVA.NP_ok_NF tv0 vHD X_open is_txt rho w) as (rho' & _ & Hw');
    [vm_compute; reflexivity | reflexivity | reflexivity | reflexivity | vm_compute; reflexivity | by_txt | vm_compute; reflexivity | exact Hw |].
  exists rho'. exact Hw'.
Qed.

Lemma X_nofit1_ok : ltac2:(tb__ "0|0|
S16S31Sb2Sb3Z51Sb1Z2Z40A2A2R1A2VTR;Sa3S33VJGv;S41S5aA2S70R3A4VFAM;R2A1A2F_;Fb;Frho;").
Proof using ML REENTER TR_exw TR_pre nA.
  intros rho b Hb; via_ex C_slow tv0 ahd 80 z0.
  intros w Hw.
  destruct (JGA_close segs C_P NF Kc rho0 (P0_ir FB) FB ML tv0 vHD (SVar 105) (SVar 106) (SVar 107) X_nofit1
              (firstn 5 (ss_objs X_nofit1)) (nth 5 (ss_objs X_nofit1) O_D) rho w) as (rho' & _ & Hw');
    [vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | exact Hw |].
  change (drop_last_state X_nofit1 (firstn 5 (ss_objs X_nofit1))) with X_nofit1c in Hw'.
  exists (rho_sub rho' s_nofit1).
  eapply (SPJ_entails_JGA segs C_P NF Kc rho0 (P0_ir FB) FB ML X_nofit1c C_slow s_nofit1 tv0 tv0 ahd ahd);
    [vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | exact Hw'].
Qed.

Lemma X_fit_ok : ltac2:(tb__ "0|0|
S16S31Sb2Sb3Z55Sb1Z2Z40A2A2R1A2VTR;Sa3S33VJGv;S41S5aA2S6dR3A4VFAM;R2A1A2F_;Fb;Frho;").
Proof using ML REENTER TR_exw TR_pre nA.
  intros rho b Hb. via_ex C_w tv0 am_w 84 z0.
  intros w Hw. exists rho. change C_w with X_fit4. unfold X_fit4.
  apply SPJ_refacts_J; [| reflexivity |].
  { apply (JGA_carve segs C_P NF Kc rho0 (P0_ir FB) FB ML TobjJVA.NP_ok_NF tv0 vHD (SVar 105) (SVar 106) p_fit szq X_fit is_txt rho w);
      [vm_compute; reflexivity | reflexivity | vm_compute; reflexivity | by_txt | | exact Hw].
    intros HP0 Hav HF. clear - HF. cbv beta. unfold p_fit, szq, len, vHD, vK, vJ, HDR.
    pick_facts HF [0%nat; 1%nat; 2%nat; 3%nat; 4%nat; 5%nat; 8%nat; 11%nat; 12%nat]. zfacts; lia. }
  intros tr md _ HF. clear - HF. unfold fit_facts, p_fit, szq, len, vK, vJ, aceil.
  pick_facts HF [0%nat; 1%nat; 2%nat; 3%nat; 4%nat; 5%nat; 8%nat; 11%nat; 12%nat]. zfacts; lia.
Qed.

Lemma X_E_malloc : ltac2:(tb__ "0|2|
S16VTR;Sa3S33VJGv;S41S42A2S55R1A4VFAM;S39S1S2S11S2S5S2SfSfA2A1M0S34A2M1A2S2S31SfA2S1S11G1S55S1G0S34S41S42A4A4S1S31SfZ46SacA4A4R1A2A1A2Frho;").
Proof using CMALLOC MALLOC REENTER nA.
  intros rho.
  apply (MALLOC E_malloc s_malloc R_malloc rho tv0 ahd _ CMALLOC).
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - intros Ai HF HP0 Hav HP HN HD HZ HXA (rhoM & md & HM) HT. split.
    + eapply (robjs_check_sound segs C_P FB Ai rho (ss_facts E_malloc) tv0 None is_txt R_malloc None rhoM md HM HT HF HN HD HZ); [vm_compute; reflexivity | | exact I].
      intros o a Ho Hx Hr. apply (pclF_caddrT segs C_P NF rho0 FB TobjJVA.NP_ok_NF rho Ai a Hav HT HP). eapply (txt_pclF _ _ rho o a Ho Hx HP0 Hav HF); [in_list | exact Hr].
    + change (wsub_get s_malloc 12) with (SAlu ALU_ADD vKK (SLit 32)). clear - HF. unfold vKK. pick_facts HF [1%nat]. zfacts; lia.
  - intros rho' _.
    replace (T_after E_malloc s_malloc R_malloc (L_malloc_null EC_P)) with T_mnull by (vm_compute; reflexivity).
    reenter T_mnull tv0 ahd 65 z0.
  - intros rho' _.
    replace (T_after E_malloc s_malloc R_malloc (L_malloc_ok EC_P)) with T_mok0 by (vm_compute; reflexivity).
    change (pos_add_nat (ss_next E_malloc) 10) with vN.
    change (wsub_get s_malloc 12) with (SAlu ALU_ADD vKK (SLit 32)).
    eapply TR_pre; [ | reenter T_mok tv_m ahd 65 z0 ].
    intros w Hw. unfold T_mok. apply SPJ_refacts_J; [exact Hw | reflexivity |].
    intros tr md HJ HF.
    eapply (JGA_tv_facts segs C_P NF Kc rho0 (P0_ir FB) FB); [exact HJ | left; reflexivity |].
    eapply (tnz_of_fact rho' (SVar vN)). pick_facts HF [29%nat]. assumption.
Qed.

Lemma X_push_ok : ltac2:(tb__ "0|0|
S16S31Sb2Sb3Z3bSb1Z2Z40A2A2R1A2VTR;Sa3S33VJGv;S65S42A2S72R3A4VFAM;R2A1A2F_;Fb;Frho;").
Proof using ML REENTER TR_exw TR_pre nA.
  intros rho b Hb. via_ex C_w2 tv0 am_w2 58 z0.
  intros w Hw.
  pose proof (SPJ_xforms segs (JGv tv_m ahd) [XSelect sel_push; XSplit 5 (SLit 24)] rho X_push X_push1 w
                ltac:(vm_compute; reflexivity) Hw) as Hw1.
  destruct (JGA_push_open segs C_P NF Kc rho0 (P0_ir FB) FB ML tv_m 0%nat blkN vHD vKK used_new X_push1
              (firstn 5 (ss_objs X_push1)) (nth 5 (ss_objs X_push1) O_D) (nth 6 (ss_objs X_push1) O_D) rho w)
    as (rho1 & _ & Hw2);
    [vm_compute; reflexivity | reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
    | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
    | vm_compute; reflexivity | exact Hw1 |].
  change (drop_last_state X_push1 (firstn 5 (ss_objs X_push1) ++ [nth 5 (ss_objs X_push1) O_D])) with X_push2 in Hw2.
  change (remove_nth 0 tv_m) with tv0 in Hw2. change (fst blkN) with (SVar vN) in Hw2.
  exists rho1. change C_w2 with X_push4. unfold X_push4.
  apply SPJ_refacts_J; [| reflexivity |].
  { apply (JGA_carve segs C_P NF Kc rho0 (P0_ir FB) FB ML TobjJVA.NP_ok_NF tv0 (SVar vN) vHD vKK p_new szq X_push2 is_txt rho1 w);
      [vm_compute; reflexivity | reflexivity | vm_compute; reflexivity | by_txt | | exact Hw2].
    intros HP0 Hav HF. clear - HF. cbv beta. unfold p_new, szq, len, vHD, vK, vJ, vKK, vN, HDR.
    pick_facts HF [0%nat; 1%nat; 2%nat; 3%nat; 5%nat; 6%nat; 7%nat; 10%nat; 11%nat]. zfacts; lia. }
  intros tr md _ HF. clear - HF. unfold fit_facts, p_new, szq, len, vK, vJ, vKK, vN, aceil.
  pick_facts HF [0%nat; 1%nat; 2%nat; 3%nat; 5%nat; 6%nat; 7%nat; 10%nat; 11%nat]. zfacts; lia.
Qed.

Lemma X_fnull_ok : ltac2:(tb__ "0|0|
S16S31VTR;Sa3S33VJGv;S41S42A2S6eR2A4VFAM;R1A1A2Fb;Frho;").
Proof using ML POST TR_exw TR_pre nA.
  intros rho b.
  apply (TR_pre (fun w => exists r, SPJ segs (JGv tv0 ahd) P_fail r w)); [ | apply TR_exw; intros r; apply X_P_fail ].
  intros w Hw. exists (rho_sub rho s_fnull).
  eapply (SPJ_entails_JGA segs C_P NF Kc rho0 (P0_ir FB) FB ML X_fnull1 P_fail s_fnull tv0 tv0 ahd ahd);
    [vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | vm_compute; reflexivity |].
  exact (SPJ_xforms segs _ [XSelect [1; 0; 2; 3; 4]%nat] rho X_fnull X_fnull1 w ltac:(vm_compute; reflexivity) Hw).
Qed.

Ltac ret_glue X hd nx cap u p Xb Xc sX :=
  intros rho b;
  apply (TR_pre (fun w => exists r, SPJ segs (JGv tv0 am_ok) P_ok r w)); [ | apply TR_exw; intros r; apply X_P_ok ];
  intros w Hw;
  destruct (JGA_unslot segs C_P NF Kc rho0 (P0_ir FB) FB ML tv0 hd nx cap p szq X (firstn 6 (ss_objs X)) (nth 6 (ss_objs X) O_D) rho w)
    as (rho1 & _ & Hw2); [vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | exact Hw |];
  change (drop_last_state X (firstn 6 (ss_objs X))) with Xb in Hw2;
  destruct (JGA_close segs C_P NF Kc rho0 (P0_ir FB) FB ML tv0 hd nx cap u Xb (firstn 5 (ss_objs Xb)) (nth 5 (ss_objs Xb) O_D) rho1 w)
    as (rho2 & _ & Hw3); [vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | exact Hw2 |];
  change (drop_last_state Xb (firstn 5 (ss_objs Xb))) with Xc in Hw3;
  exists (rho_sub rho2 sX);
  eapply (SPJ_entails_JGA segs C_P NF Kc rho0 (P0_ir FB) FB ML Xc P_ok sX tv0 tv0 (AHead hd) am_ok);
    [vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | vm_compute; reflexivity | exact Hw3].
Definition u_fit : sv := Eval vm_compute in c_val (nth 0 (ob_cells (nth 5 (ss_objs C_w) O_D)) (mkCell (SLit 0) 8 (SLit 0))).
Lemma X_ret_ok : ltac2:(tb__ "0|0|
S16S31VTR;Sa3S33VJGv;S41S5fA2S73R2A4VFAM;R1A1A2Fb;Frho;").
Proof using ML POST TR_exw TR_pre nA. ret_glue X_ret vH vNX vCAP vU vP X_ret_b X_ret_c s_ret. Qed.
Lemma X_ret0_ok : ltac2:(tb__ "0|0|
S16S31VTR;Sa3S33VJGv;S41S60A2S74R2A4VFAM;R1A1A2Fb;Frho;").
Proof using ML POST TR_exw TR_pre nA. ret_glue X_ret0 vHD (SVar 105) (SVar 106) u_fit p_fit X_ret0_b X_ret0_c s_ret0. Qed.
Lemma X_ret2_ok : ltac2:(tb__ "0|0|
S16S31VTR;Sa3S33VJGv;S41S61A2S75R2A4VFAM;R1A1A2Fb;Frho;").
Proof using ML POST TR_exw TR_pre nA. ret_glue X_ret2 (SVar vN) vHD vKK szq p_new X_ret2_b X_ret2_c s_ret2. Qed.

Lemma exits_okT : ltac2:(tb__ "0|4|
S11S5S2SfSfA2A1M0S34S2S31SfA2M1S16Sd5S2S2S11S2G0S34A2M2A2M3G1A2S1G3G1S1S11G2R5S1G0S34R4R3A4A4R2A4SafA3VTR;Sa3S33VJGv;R5R4A2R6R2A4VFAM;S39S1G3G1S1S11G2R6S1G0S34R5R4A4A4R3A4R2A2A1A2F_;Frho;FrvX;FamX;FtvX;FX;").
Proof using CMALLOC MALLOC POST REENTER TR_exw nA.
  intros X tvX amX rvX rho Hin. cbn [exitsE In] in Hin.
  destruct Hin as [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[]]]]]]]]]]]]; injection H as <- <- <- <-;
    unfold ameas, ad_rank, ad_var; cbn [fst snd].
  - apply X_open_ok. pose proof (urange (eval rho z0)). lia.
  - apply X_fit_ok. pose proof (urange (eval rho z0)). lia.
  - apply X_nofit1_ok. pose proof (urange (eval rho z0)). lia.
  - apply X_E_malloc.
  - apply X_push_ok. pose proof (urange (eval rho z0)). lia.
  - apply X_ret_ok.
  - apply X_ret0_ok.
  - apply X_ret2_ok.
  - apply X_fnull_ok.
  - apply X_P_fail.
  - apply X_P_ok.
Qed.
End SumT.

Section Safety.
Theorem intern_rest_sum : ltac2:(tb__ "0|0|
SdaS33Vok;Sa3S33S38S33Sa5VKc;S44VFB;A1VFB;S41S42A7S5eVrho0;A4SccS33Sa7Vrho0;SadA4A4").
Proof using HS MC ML.
  eapply triple_conseq; [ | intros w Hw; exact Hw | ].
  2: { apply (cfg_sound_JGAE segs C_P NF Kc rho0 (P0_ir FB) FB ML FUEL_ir cutpcs_ir 100 cutsE exitsE ok Q (proj1 HS)
                (ejcertA_jcertA segs NF _ _ _ _ _ ejcert_ok)) with (rvT := (100, z0)); [|left; reflexivity].
       apply (exits_okT (triple segs ok) (fun _ w => SPfamGJ segs (map nA (map (@adrop) cutsE)) w \/ Q w)
                (triple_factsJ segs ok) (triple_SPJ_ex segs ok)
                (fun P P' Q' HP H => @triple_conseq segs ok P P' Q' Q' HP (fun w Hw => Hw) H)
                (fun A P Q' H => @triple_ex segs ok A P Q' H)
                (call_soundP segs ok)).
       - intros Ai rho1. apply (mc_malloc _ _ _ MC). exact HS.
       - intros T tv am rT vT rho b Hin _ _. exact (reenter_cutGAE segs C_P NF Kc rho0 (P0_ir FB) FB ok cutsE T tv am (rT, vT) Q rho Hin).
       - intros P tv am rho b Hin. apply (exit_postGA segs C_P NF Kc (P0_ir FB) FB ok rho0 tv am Posts_ir P). exact Hin. }
  intros w Hw. apply JGA_pre_intro. exact Hw.
Qed.
End Safety.

Section Existence.
Hypothesis Hvi : vm_insensitive Kc.
Hypothesis MCX : ltac2:(tb__ "0|0|
Sf7S33Sa5SbdA3").

Theorem intern_rest_sum_ex : ltac2:(tb__ "0|0|
Sd9S33Sa3S33S38S33Sa5VKc;S44VFB;A1VFB;S41S42A7S5eVrho0;A4SccS33Sa7Vrho0;SadA4A3").
Proof using Hvi MCX ML.
  eapply etriple_conseq; [ | intros w Hw; exact Hw | ].
  2: { apply (cfg_complete_JGA segs C_P NF Kc rho0 (P0_ir FB) FB ML FUEL_ir cutpcs_ir 100 cutsE exitsE Q ejcert_ok) with (rvT := (100, z0)); [|left; reflexivity].
       apply (exits_okT (etriple segs) (fun b w => SPfamEJ segs (map (enodeA segs C_P NF Kc rho0 (P0_ir FB) FB) cutsE) b w \/ Q w)
                (etriple_factsJ segs) (etriple_SPJ_ex segs)
                (fun P P' Q' HP H => @etriple_conseq segs P P' Q' Q' HP (fun w Hw => Hw) H)
                (fun A P Q' H => @etriple_ex segs A P Q' H)
                (call_completeP segs)).
       - intros Ai rho1. apply (mcx_malloc _ _ _ MCX). exact Hvi.
       - intros T tv am rT vT rho b Hin H0 Hb. apply (ereenter_cutAE segs C_P NF Kc rho0 (P0_ir FB) FB cutsE T tv am (rT, vT) Q b rho Hin).
         unfold ameas, ad_rank, ad_var. cbn [fst snd]. pose proof (urange (eval rho vT)). nia.
       - intros P tv am rho b Hin. apply (eexit_postGA segs C_P NF Kc (P0_ir FB) FB rho0 tv am Posts_ir P). exact Hin. }
  intros w Hw. apply JGA_pre_intro. exact Hw.
Qed.
End Existence.
End Sum.
