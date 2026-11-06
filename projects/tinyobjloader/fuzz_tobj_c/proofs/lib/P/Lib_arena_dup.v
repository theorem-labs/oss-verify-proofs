(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "pair"; "prod"; "nil"; "list"; "bool"; "nat"; "true"; "false"; "None"; "option"; "app"; "Some"; "fst"; "snd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sstate"; "SLit"; "sprop"; "SVar"; "SPUle"; "valuation"; "cell"; "sobj"; "mkCell"; "ss_next"; "SAlu"; "DUnknown"; "FcsrFrm0"; "mkObj"; "mkSS"; "holds"; "smatch"; "sv_eqb"; "SPAlign"; "SPBranch"; "eval"; "rw"; "ss_facts"; "ss_objs"; "ss_regs"; "SPUlt"; "ob_base"; "ob_hi"; "ob_lo"; "obj_range"; "ss_pc"; "sv_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Code"; "segs"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVA"; "amode"; "JGA"; "JLGA"; "AHead"; "AOpen"; "JGA_pre"; "ameas"; "PostsCA"; "XA"; "am_below"; "ejcertA"; "malloc_callAT"; "nodeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "SPJ"; "jpred"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_arena_dup"; "tv0"; "P0_ad"; "vSZ"; "vP"; "base_facts"; "vAR"; "vHD"; "am_open"; "vDp"; "vH"; "vLS"; "vSRC"; "E_malloc"; "P_fail"; "P_ok"; "am_ok"; "two47"; "vI"; "vK"; "O_D"; "O_F"; "O_ar"; "O_src"; "Pre_ad"; "am_loop"; "p_fit"; "spo"; "tv_m"; "vCAP"; "FUEL_ad"; "X_K0"; "X_fit"; "X_nofit1"; "X_nofit2"; "X_open"; "X_push"; "X_ret"; "X_slow0"; "ad_K"; "ad_loop"; "ad_ret"; "ad_slow"; "cutpcs_ad"; "post_objs"; "vN"; "vNX"; "vU"; "C_K"; "C_loop"; "C_open"; "C_slow"; "F_cells"; "O_hdr"; "O_slot"; "T_mnull"; "T_mok"; "ad_entry"; "ad_open"; "ar_cells"; "is_src"; "loop_facts"; "loop_regs"; "run_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "C_P"; "topL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "pre_fregs"; "setregs"; "post_regs"; "pre_regs"; "@Corelib.Init.Logic"; "eq"; "and"; "ex"; "iff"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_arena_dup.Sum"; "z0"; "ahd"; "Posts_ad"; "cutsE"; "exitsE"; "PDA_ad"; "cp_var"; "@Stdlib.ZArith.BinInt.Z"; "le"; "mul"; "pow"; "add"; "lt"; "eqb"; "opp"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_GE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract"; "EC_P"; "Pre_malloc"; "J_alloc_pre"; "Posts_malloc"; "L_malloc_null"; "L_malloc_ok"; "MInvR"; "NPOSTM"; "V_RES"; "ec_malloc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "jpost"; "LQP"; "agree_vals"; "pos_add_nat"; "J_ofP"; "call_checkP"; "call_linkP"; "import_okP"; "import_post"; "import_sub"; "@Stdlib.Lists.List"; "In"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_absorb"; "rho_sub"; "wsub_get"; "wsub"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface"; "MA"; "ma_L"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "entails_fr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "leaf"; "lf_state"; "sym_run"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "T_after"; "T_ok"; "call_checkT"; "fbin"; "malloc_contracts"; "malloc_contracts_ex"; "pclF"; "robjs_ok"; "tv_below"; "tvd"; "tvin"; "tvz"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "jnode"; "@Stdlib.Bool.Bool"; "Is_true"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@stdpp.base"; "filter"; "@stdpp.decidable"; "Is_true_dec"; "@stdpp.list_basics.list"; "list_filter"].
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

Definition ad_entry : Z := 0x1c840.
Definition ad_open : Z := 0x1c870.
Definition ad_slow : Z := 0x1c8a0.
Definition ad_K : Z := 0x1c8b8.
Definition ad_loop : Z := 0x1c91c.
Definition ad_ret : Z := 0x1c900.
Definition FUEL_ad : nat := 300%nat.

Definition vAR : sv := SVar 12.  Definition vSRC : sv := SVar 13.  Definition vSZ : sv := SVar 14.
Definition vHD : sv := SVar 15.  Definition vLS : sv := SVar 16.  Definition vDp : sv := SVar 19.
Definition spo (k : Z) : sv := ltac2:(tb__ "0|0|
S1aS9bS13PaA1S11Vk;A1A3").
Definition two47 : Z := 2 ^ 47.

Definition base_facts : list sprop := ltac2:(tb__ "0|8|
S0S12S22PaM0Z4M1A2S0S12S23S9cS11N310A1S4aA3S0S12S23S9cS4aS11S9aS96Z2Z28A2A1A1A3S0S12S14S13P1eA1M2S1aS9bS5cN30A1M3S4aA3A2S0S12S14G2G3A2S0S12S14G2S13G0A1M4A2S0S12S14G4S11S52A1M5A2S0S12S14S11Z1A1M6S44A2S0S12S14S44S4cA2S0S12S14S4cG5A2S0S12S14G6S4dA2S0S12S14S4dG5A2S0S12S14S11Z1000A1S47A2S0S12S14S1aS9bS47S11Z40A1A3S11Z7fffff800000A1M7A2S0S12S14S47G7A2S0S12S22PcG1A2S0S12S14S48G7A2S0S12S14S11Z7fff7f800000A1G2A2S0S12S14G2G7A2S3S12A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").

Definition F_cells : list cell := ltac2:(tb__ "0|1|
S0S16S18S11N30A1Z8M0S13P28A1A3S0S16S18S11N28A1G0S13P27A1A3S0S16S18S11N20A1G0S13P26A1A3S0S16S18S11N18A1G0S13P1dA1A3S0S16S18S11N10A1G0S13P1cA1A3S0S16S18S11N8A1G0S13PbA1A3S3S16A1A3A3A3A3A3A3").
Definition O_F (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S1dS13PaA1S11N30A1S11Z0A1Vcells;S1bA5").
Definition O_D : sobj := ltac2:(tb__ "0|0|
S1dS5cN30A1S4aS11Z0A1S3S16A1S1bA5").
Definition ar_cells (hd : sv) : list cell := ltac2:(tb__ "0|2|
S0S16S18S11Z0A1M0Z8M1S11Z13858A1A3S0S16S18S11G1A1G1S11Z13864A1A3S0S16S18S11Z10A1G1G0A3S0S16S18S11Z18A1G1S11Z13878A1A3S0S16S18S11Z20A1G1G0A3S0S16S18S11Z28A1G1G0A3S0S16S18S11Z30A1G1Vhd;A3S0S16S18S11Z38A1G1S11Z10000A1A3S3S16A1A3A3A3A3A3A3A3A3").
Definition O_ar (hd : sv) : sobj := ltac2:(tb__ "0|0|
S1dS47S11Z0A1S11Z40A1S7cVhd;A1S1bA5").
Definition O_src : sobj := ltac2:(tb__ "0|0|
S1dS4dS11Z0A1S4cS3S16A1S1bA5").

Definition Pre_ad : sstate := ltac2:(tb__ "0|0|
S1eS7aS87S84S1cS9SfA1S0S17S56S3S16A1A1S0S17S55S0S17S57S48A1S0S17S58S3S17A1A3A3A3A3S46S83S8A9").

Definition tv0 : list (sv * sv) := ltac2:(tb__ "0|1|
S0S2SfSfA2M0S1SfSfS47S11Z40A1A4S3G0A1A3").

Definition cutpcs_ad : list Z := ltac2:(tb__ "0|0|
S0S31S7bS0S31S6bS0S31S68S0S31S69S0S31Sa6S9dA1S3S31A1A3A3A3A3A3").
Definition run_of (S : sstate) : list sstate := ltac2:(tb__ "0|1|
SaS4Sc6A1M0A1S4S10A1Lx;Sc8S30S5fS6cVS;S7A5G0SbeSc6S10Sc7R1A4Lls;S3S10A1Xax2").
Definition leaves_at (S : sstate) (pc : Z) : list sstate := ltac2:(tb__ "0|1|
Sd9S10S4S10A1SdbS10A1S10Sd7S99S2eR1A1Vpc;A2M0A1Ll;S10SdaG0A1Lx;S80VS;A1A6").
Definition optR (x : option (list sobj)) : list sobj := match x with Some r => r | None => [] end.

Definition X_open : sstate := Eval vm_compute in nth 0 (leaves_at Pre_ad ad_open) Pre_ad.
Definition C_open : sstate := Eval vm_compute in open_state X_open vHD.
Definition am_open : amode := ltac2:(tb__ "0|0|
S37S48S13P64A1S13P65A1S3S2SfSfA2A1A4").

Definition X_fit : sstate := Eval vm_compute in nth 0 (leaves_at C_open ad_loop) Pre_ad.
Definition X_nofit1 : sstate := Eval vm_compute in nth 0 (leaves_at C_open ad_slow) Pre_ad.
Definition X_nofit2 : sstate := Eval vm_compute in nth 1 (leaves_at C_open ad_slow) Pre_ad.

Definition X_slow0 : sstate := Eval vm_compute in nth 0 (leaves_at Pre_ad ad_slow) Pre_ad.
Definition C_slow : sstate := ltac2:(tb__ "0|1|
S1eS6bS85S28S67A1S0S2S6SfA2M0S1S6SfUaS13P64A1A4S0G0S1S6SfUeS13P65A1A4S0G0S1S6SfUfS13P66A1A4S0G0S1S6SfU10S13P67A1A4S3G0A1A3A3A3A3A2S84S1cS9SfA1S27S67A1S46P68S8A9").

Definition X_K0 : sstate := Eval vm_compute in nth 0 (leaves_at C_slow ad_K) Pre_ad.
Definition vK : sv := SVar 104.
Definition C_K : sstate := ltac2:(tb__ "0|2|
S1eS68S85S28S60A1S0S2S6SfA2M0S1S6SfU12S54A4S3G0A1A3A2S84S1cS9SfA1S27S60A1SbS12S0S12S14S1aS9bS44S11Z10M1A1A3S54A2S0S12S14S54S11S97S52G1A2A1A2S3S12A1A3A3S46A3P69S8A9").

Definition E_malloc : sstate := Eval vm_compute in nth 0 (leaves_at C_K (ec_malloc EC_P)) Pre_ad.
Definition s_malloc : wsub := ltac2:(tb__ "0|0|
S0S2S32SfA2S1S32SfPfS4aA4Sd5PaS4eS9eS9dA1A3A3").
Definition R_malloc : list sobj := Eval vm_compute in optR (entails_fr E_malloc (Pre_malloc EC_P) s_malloc).
Definition vN : positive := 115.
Definition blkN : sv * sv := ltac2:(tb__ "0|0|
S1SfSfS13S6eA1S1aS9bS54S11Z20A1A3A4").
Definition tv_m : list (sv * sv) := blkN :: tv0.
Definition T_mnull : sstate := Eval vm_compute in T_after E_malloc s_malloc R_malloc (L_malloc_null EC_P).
Definition T_mok0 : sstate := Eval vm_compute in T_after E_malloc s_malloc R_malloc (L_malloc_ok EC_P).
Definition T_mok : sstate := add_facts (tv_facts blkN) T_mok0.

Definition X_push : sstate := Eval vm_compute in nth 0 (leaves_at T_mok ad_loop) Pre_ad.
Definition X_push1 : sstate :=
  Eval vm_compute in match apply_xforms X_push [XSelect [2; 0; 3; 4; 1]%nat; XSplit 4 (SLit 24)] with Some St => St | None => Pre_ad end.
Definition X_push2 : sstate := Eval vm_compute in drop_last_state X_push1 (firstn 5 (ss_objs X_push1)).
Definition p_new : sv := ltac2:(tb__ "0|0|
S1aS9bS13S6eA1S11Z20A1A3").
Definition X_push3 : sstate := Eval vm_compute in carve_state X_push2 p_new vSZ.
Definition used_new : sv := Eval vm_compute in c_val (nth 0 (ob_cells (nth 4 (ss_objs X_push1) O_D)) (mkCell (SLit 0) 8 (SLit 0))).

Definition vH : sv := SVar 110.  Definition vNX : sv := SVar 111.  Definition vCAP : sv := SVar 112.
Definition vU : sv := SVar 113.  Definition vP : sv := SVar 114.   Definition vI : sv := SVar 115.
Definition am_loop : amode := ltac2:(tb__ "0|1|
S37S4bS6fS5eS0S2SfSfA2M0S1SfSfS45S44A4S3G0A1A3A4").
Definition O_hdr (hd nx cap u : sv) : sobj := ltac2:(tb__ "0|2|
S1dVhd;S11Z0A1M0S11Z18A1S0S16S18G0Z8M1Vnx;A3S0S16S18S11G1A1G1Vcap;A3S0S16S18S11Z10A1G1Vu;A3S3S16A1A3A3A3S1bA5").
Definition O_slot (p : sv) : sobj := ltac2:(tb__ "0|0|
S1dVp;S11Z0A1S44S3S16A1S1bA5").
Definition loop_regs : list sv := ltac2:(tb__ "0|0|
S0SfS13P84A1S0SfS13P74A1S0SfS5cN30A1S0SfS13P17A1S0SfS13P18A1S0SfS13P76A1S0SfS13P77A1S0SfS13P78A1S0SfS47S0SfS13P75A1S0SfS45S0SfS1aS9bS4dS53A3S0SfS1aS9bS45S44A3S0SfS1aS9bS45S53A3S0SfS13P79A1S0SfS13P7aA1S0SfS13P7bA1S0SfS13P7cA1S0SfS13P7dA1S0SfS13P7eA1S0SfS13P7fA1S0SfS13P29A1S0SfS13P2aA1S0SfS13P2bA1S0SfS13P2cA1S0SfS13P2dA1S0SfS13P2eA1S0SfS13P2fA1S0SfS13P80A1S0SfS13P81A1S0SfS13P82A1S0SfS13P83A1S3SfA1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition loop_facts : list sprop := ltac2:(tb__ "0|2|
S0S12S29S53S44A2S0S12S14S53S11S52A1A2S0S12S14S70S5eA2S0S12S14S11Z1000A1M0S45A2S0S12S14S45S11Z7fffff800000A1M1A2S0S12S14S1aS9bS45S44A3G1A2S0S12S14G0S4bA2S0S12S14S4bG1A2S3S12A1A3A3A3A3A3A3A3A3").
Definition C_loop : sstate := ltac2:(tb__ "0|0|
S1eS69S7fS84S1cS9SfA1S0S17S56S75A1S0S17S55S0S17S57S4bA1S0S17S58S0S17S76S4bS6fS5eS70A4S0S17S77S45A1S3S17A1A3A3A3A3A3A3SbS12S7eS46A3P85S8A9").
Definition X_ret : sstate := Eval vm_compute in nth 0 (leaves_at C_loop ad_ret) Pre_ad.
Definition X_ret1 : sstate := Eval vm_compute in drop_last_state X_ret (firstn 5 (ss_objs X_ret)).
Definition X_ret2 : sstate := Eval vm_compute in drop_last_state X_ret1 (firstn 4 (ss_objs X_ret1)).

Definition p_fit : sv := Eval vm_compute in nth 10 (ss_regs X_fit) (SLit 0).
Definition X_fit3 : sstate := Eval vm_compute in carve_state X_fit p_fit vSZ.
Definition fit_facts : list sprop := ltac2:(tb__ "0|1|
S0S12S14S11Z1000A1S5bA2S0S12S14S5bS11Z7fffff800000A1M0A2S0S12S14S1aS9bS5bS44A3G0A2S3S12A1A3A3A3").
Definition X_fit4 : sstate := add_facts fit_facts X_fit3.

Definition X_nofit1c : sstate := Eval vm_compute in drop_last_state X_nofit1 (firstn 4 (ss_objs X_nofit1)).
Definition X_nofit2c : sstate := Eval vm_compute in drop_last_state X_nofit2 (firstn 4 (ss_objs X_nofit2)).

Definition post_objs (hd : sv) : list sobj := ltac2:(tb__ "0|0|
S0S17S56S3S16A1A1S0S17S55S0S17S57Vhd;A1S0S17S58S3S17A1A3A3A3A3").
Definition P_fail : sstate := ltac2:(tb__ "0|1|
S1eS6aS85S86S83A1S0S2S6SfA2M0S1S6SfUaS11Z0A1A4S3G0A1A3A2S84S1cS9SfA1S6dS48A1S46Sa4S8A9").
Definition P_ok : sstate := ltac2:(tb__ "0|5|
S1eS6aS85S86S83A1S0S2S6SfA2M0S1S6SfUaS13P8cA1M1A4S3G0A1A3A2S84S1cS9SfA1S6dS13P8dA1M2A1SbS12S0S12S14S11Z1000A1M3G1A2S0S12S14G1S11Z7fffff800000A1M4A2S0S12S14G3G2A2S0S12S14G2G4A2S3S12A1A3A3A3A3S46A3P8eS8A9").
Definition am_ok : amode := AHead (SVar 141).

Definition s_fit : wsub := infer_sub 100 X_fit3 C_loop.
Definition s_push : wsub := infer_sub 100 X_push3 C_loop.
Definition s_nofit1 : wsub := infer_sub 100 X_nofit1c C_slow.
Definition s_nofit2 : wsub := infer_sub 100 X_nofit2c C_slow.
Definition s_ret : wsub := infer_sub 100 X_ret2 P_ok.

Definition is_src (o : sobj) : bool := ltac2:(tb__ "0|1|
S5S5L_;M0S21S2aVo;A1S4dA2G0S21S2cVo;A1S11Z0A1A2S21S2bVo;A1S4cA2S8X5x2S8X5x2").

Goal call_checkP E_malloc (Pre_malloc EC_P) s_malloc R_malloc [L_malloc_null EC_P; L_malloc_ok EC_P] = true.
Proof. vm_compute. reflexivity. Qed.
Goal ss_next E_malloc = 105%positive /\ wsub_get (import_sub s_malloc NF (L_malloc_ok EC_P) (ss_next E_malloc)) V_RES = SVar vN.
Proof. split; [reflexivity | vm_compute; reflexivity]. Qed.
Goal length (leaves_at C_open ad_slow) = 2%nat /\ length (leaves_at C_open ad_loop) = 1%nat /\ length (run_of C_open) = 3%nat.
Proof. vm_compute. repeat split; reflexivity. Qed.

Definition P0_ad (FB : list (Z * Z)) (r : valuation) : Prop := ltac2:(tb__ "0|2|
S8aS31S31S8aS31S31S89Sb1S2S31S31A2S1S31S31R2R1A4VFB;A3S89S94R2SbcQ40M0S25Vr;PdA2A2M1A2S94S97G1SbcG0S25Vr;P10A2A2A2S97R2R1A2A2A2A2Ln;A2Lb;A2").

Section Sum.
Variable ok : world -> Prop.
Variable Kc : ltac2:(tb__ "0|0|
S4Sb3A1Sb2OF_;F_;").
Variable FB : list (Z * Z).
Variable rho0 : valuation.
Hypothesis HS : ok_sideK segs ok Kc.
Hypothesis ML : malloc_laws segs C_P.
Hypothesis MC : ltac2:(tb__ "0|0|
ScdS30S81S9dA3").

Definition Posts_ad : list (sstate * jpost) := ltac2:(tb__ "0|2|
S0S2S10Sa7A2M0S1S10Sa7S4fS35S30S81VKc;S43VFB;A1M1VFB;S42S36S48A1A7A4S0G0S1S10Sa7S50S35S30S81VKc;G1VFB;S42S51A7A4S3G0A1A3A3").

Definition PDA_ad : list (sstate * (list (sv * sv) * amode)) := ltac2:(tb__ "0|3|
S0S2S10S2S4S2SfSfA2A1M0S33A2M1A2M2S1S10G1S4fS1G0S33S42S36S48A1A4A4S0G2S1S10G1S50S1G0S33S42S51A4A4S3G2A1A3A3").
Lemma Posts_ad_PDA : ltac2:(tb__ "0|0|
S88S4S2S10Sa7A2A1S8fS3aS30S81VKc;S43S92VFB;A6A3").
Proof using . reflexivity. Qed.

Let nA : ltac2:(tb__ "0|0|
S2S10S2S4S2SfSfA2A1S33A2A2Sd6Fn;") := ltac2:(tb__ "0|0|
S3fS30S81S83VKc;Vrho0;S43VFB;A1VFB;A7").
Let JGv (tv : list (sv * sv)) (am : amode) : jpred := ltac2:(tb__ "0|0|
S34S30S81S83VKc;Vrho0;S43VFB;A1VFB;Vtv;Vam;A9").
Let Q : assn := ltac2:(tb__ "0|0|
Sa8S30S83Vrho0;S8fA4").

Definition z0 : sv := SLit 0.
Definition cp_var : sv := SAlu ALU_SUB vSZ vI.
Definition ahd : amode := AHead vHD.
Definition cutsE : list aedesc := ltac2:(tb__ "0|7|
S0S2S2S10S2S4S2SfSfA2A1M0S33A2M1A2M2S2S31SfA2M3A2M4S1G2G3S1S10G1S59S1G0S33S42S8eA4M5A4S1S31SfZ64S8dA4A4S0G4S1G2G3S1S10G1S73S1G0S33S42S49A4A4S1S31SfZ5aS8dA4A4S0G4S1G2G3S1S10G1S74G5A4S1S31SfZ50S8dA4A4S0G4S1G2G3S1S10G1S71G5A4S1S31SfZ4bS8dA4A4S0G4S1G2G3S1S10G1S78G5A4S1S31SfZ41S8dA4M6A4S0G4S1G2G3S1S10G1S79S1G0S33S5dS8eA4A4G6A4S0G4S1G2G3S1S10G1S72S1G0S33S42S5aA4A4S1S31SfZ32S93A4A4S3G4A1A3A3A3A3A3A3A3").
Definition exitsE : list aedesc := ltac2:(tb__ "0|9|
S0S2S2S10S2S4S2SfSfA2A1M0S33A2M1A2M2S2S31SfA2M3A2M4S1G2G3S1S10G1S64S1G0S33S42S8eA4M5A4S1S31SfZ5fS8dA4A4S0G4S1G2G3S1S10G1S61S1G0S33S42S49A4M6A4S1S31SfZ55S8dA4M7A4S0G4S1G2G3S1S10G1S62G6A4G7A4S0G4S1G2G3S1S10G1S63G6A4G7A4S0G4S1G2G3S1S10G1S4eG5A4S1S31SfZ46S8dA4A4S0G4S1G2G3S1S10G1S65S1G0S33S5dS8eA4A4S1S31SfZ3cS8dA4A4S0G4S1G2G3S1S10G1S66S1G0S33S42S5aA4A4S1S31SfZaS8dA4A4S0G4S1G2G3S1S10G1S4fG5A4S1S31SfZ0S8dA4M8A4S0G4S1G2G3S1S10G1S50S1G0S33S42S51A4A4G8A4S3G4A1A3A3A3A3A3A3A3A3A3").
Lemma ejcert_ok : ltac2:(tb__ "0|0|
S88S5S3dS30S83S5fS6cP64S90S91A7S7A3").
Proof using . vm_cast_no_check (@eq_refl bool true). Qed.

Lemma P0_at : ltac2:(tb__ "0|0|
S15Sa9S83Vrho0;R1A3S43VFB;Vrho0;A2S43VFB;R3A2F_;F_;Frho;").
Proof using .
  intros rho Hav HP0.
  assert (E13 : rw rho 13%positive = rw rho0 13%positive) by (symmetry; apply (proj1 Hav); reflexivity).
  assert (E16 : rw rho 16%positive = rw rho0 16%positive) by (symmetry; apply (proj1 Hav); reflexivity).
  unfold P0_ad. rewrite E13, E16. exact HP0.
Qed.

Lemma src_pclF : ltac2:(tb__ "0|1|
S4S17A1S4S12A1S15S17S31Sb1S17R2R5A3S88S5S7dR3A1S7A3S43VFB;Vrho0;A2Sa9S83Vrho0;R6A3SbdS12S1fR7A1R8A3Sb1S12S14S4cS11S52A1A2R9A3S89S94SdS31S31S2dR9R8A2M0A3R7A2S98R7SeS31S31G0A3A2A2ScfS30S81Vrho0;VFB;R8A5F_;F_;F_;F_;F_;F_;F_;Fa;Fo;Frho;Ffacts;FR;").
Proof using .
  intros R facts rho o a _ Ho HP0 Hav HF Hin Hr. unfold is_src in Ho.
  apply lazy_andb_prop in Ho as [Hb Ho]. apply lazy_andb_prop in Ho as [Hl Hh].
  apply sv_eqb_sound in Hb. apply sv_eqb_sound in Hl. apply sv_eqb_sound in Hh.
  destruct (P0_at rho Hav HP0) as (b & n & Hbin & H1 & H2).
  unfold obj_range, obj_lo_of, obj_hi_of in Hr. rewrite Hb, Hl, Hh in Hr. cbn [fst snd] in Hr.
  rewrite soff_lit_small in Hr by lia. unfold soff in Hr. rewrite bv_signed_U in Hr.
  pose proof (proj1 (Forall_forall _ _) HF _ Hin) as HL. cbn [holds] in HL. rewrite U_lit in HL. unfold vLS, vSRC in *. rewrite !eval_var in *.
  unfold M64v, two47 in HL. rewrite Z.mod_small in HL by lia.
  destruct (Zsigned_spec (bv_unsigned (rw rho 16%positive))) as [[_ X]|[X _]]; [|lia]. rewrite X in Hr.
  right; right. exists b, n. split; [exact Hbin | lia].
Qed.
Ltac in_list := cbn; repeat (first [left; reflexivity | right]).
Ltac by_src := intros o a Ho Hx HP0 Hav HF Hr; eapply (src_pclF _ _ _ o a Ho Hx HP0 Hav HF); [in_list | exact Hr].

Section SumT.
Variable TR : assn -> assn -> Prop.
Variable FAM : Z -> assn.
Hypothesis TR_facts : ltac2:(tb__ "0|1|
S41S10S15Sb4SbdS12S1fR2A1S26R3A1A3VTR;S40S30R5R4R3A4R2A2M0F_;G0F_;FQ';Frho;FS;FJ;").
Hypothesis TR_ex : forall (A : Type) (J : A -> jpred) S rho (Q' : assn),
  (forall x, TR (SPJ segs (J x) S rho) Q') -> TR (SPJ segs (fun r t m => exists x, J x r t m) S rho) Q'.
Hypothesis TR_pre : ltac2:(tb__ "0|0|
Sb4Sb4Sb4Sb7R3R1A1R5R2A1F_;Fw;VTR;R4R2A2VTR;R4R3A2F_;F_;FQ';FP';FP;").
Hypothesis TR_exw : forall (A : Type) (P : A -> assn) (Q' : assn), (forall a, TR (P a) Q') -> TR (fun w => exists a, P a w) Q'.
Hypothesis TR_callP : ltac2:(tb__ "0|3|
S41S41S10S10SbbS4S17A1M0S4S2S10Sa7A2M1A1Sb4S15S88SaG0A1Sc5R7R6R5A3ScG0R4A2A3S88S5SacR8R7R6R5SbeG1S10SdS10Sa7A2R4A4A5S7A3S15VTR;S40S30RbR9R1A4Sa8S30S19R9A1R1R6A4A2Frho1;S4Sb3A1M2SbfSb2S20S30R7RdS1G2Sc0R3Sc1R2R1A2A4A4R10R8R4R2A3R10Sb9Sb8R9RcR4A3RdA2R5R3A3F_;F_;Fmd;Fms;Ftr;S10Sa7G2SbfSb2S15G2SbfSb2Sb1G1S1S10Sa7R9R8A4R10A3S20S30RfR15S1G2Sc0R8Sc1R7R6A2A4A4R18R10R9R7A3Sa9S19R16A1Sb9Sb8R11R14R9A3R15A2R7A3S20S30R8RdS1G2Sc0R7Sc1R6R5A2A4A4RdSb9Sb8R13R16RbA3R17A2R9R8R6A4S89SaeR14RcR17R18R19RfRaA7S15SadR15RdR18R19R1aR1bR10R1RbA9VTR;S40S30SabR10Sb9Sb8R16R19ReA3R1aA2RcA3SafR1aS19R1bA1R11S19R1cA1R19A5R2A4R17A2F_;Frho';A2F_;F_;F_;F_;F_;F_;Fmd';Fms';Ftr';FrhoL;Fmd;Fms;Ftr;FJL;FL;VTR;S40S30ReRcR6A4R7A2F_;F_;F_;F_;F_;Frho;FQ';FPosts;FR;Fs;FPre;FC;FJp;FJ;").
Hypothesis CMALLOC : ltac2:(tb__ "0|0|
Sc2S15VTR;S40S30S9fS30S81R2VKc;A4S9eS9dA1R1A4Sa8S30S83R1Sa0S30S81S9dR2VKc;A5A4A2Frho1;FAi;").
Hypothesis REENTER : ltac2:(tb__ "0|4|
S10S4S2SfSfA2A1M0S33S31SfS15S31Sb1S2S2S10S2G0S33A2M1A2M2S2S31SfA2M3A2S1G2G3S1S10G1R7S1G0S33R6R5A4A4S1S31SfR4R3A4A4S90A3S94Z0R5A2S94S95S97R6Z1A2S96Z2Z40A2A2R3A2VTR;S40S30VJGv;R9R8A2RaR5A4VFAM;R4A1A2F_;F_;F_;Fb;Frho;FvT;FrT;Fam;Ftv;FT;").
Hypothesis POST : ltac2:(tb__ "0|0|
S10S4S2SfSfA2A1S33S15S31Sb1S2S10Sa7A2S1S10Sa7R5S35S30S81VKc;S43VFB;A1VFB;R4R3A7A4S8fA3VTR;S40S30VJGv;R5R4A2R6R3A4VFAM;R2A1A2F_;Fb;Frho;Fam;Ftv;FP;").

Let MALLOC : ltac2:(tb__ "0|a|
S10SbbS4S17A1M0S15S4S2SfSfA2M1A1S33Sb4Sc2S15VTR;S40S30S9fS30S81R2VKc;A4S9eS9dA1M2R1A4Sa8S30Sc4R1Sa0S30S81S9dR2VKc;A5A4A2Frho1;FAi;S88SaG0A1Sc5R8G2R7A3ScG0R6A2A3S88S5ScbS81S83R9G2R8R7S0S10Sa1S9dA1M3S0S10Sa2S9dA1M4S3S10A1A3A3A7S7A3S88S5Sd8S83S19RaA1A2S7A3S88S5Sd1S19RbA1R7A2S7A3S88S5S3cS19RcA1R7A2S7A3S88S5S2fS19RdA1SbaRcPcM5A2A2S7A3S88SfSbaSb0RdSc4G4S19ReA1M6A4Sa5A2S13SaaG6UaM7A2A1A3Sc2SbdS12S1fRdA1S26R10A1A3S43VFB;Vrho0;A2Sa9S83Vrho0;RfA3SccVFB;R4A2Sd3VFB;R5R11R10A4Sd2R12R11A2Sd4R13R12A2S3bVFB;R12R8R14R13A5S8aS15S15S8aSb2Sb2Sa3S30S81RbR2R1A5Lmd;A2LrhoM;A2ScaR16S82Sc3RaA1A1A2S89Sd0S30S81RbS9S31A1R17R18A6S98Z0SbcQ40S24R17SbaR19G5A2A2A2A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FAi;S15Sa9S19R11A1ReR1A3VTR;S40S30S34S30S81S83VKc;Vrho0;S43VFB;A1M8VFB;ReRdA9M9Sc9R12R11R10G3A4R2A4RcA2F_;Frho';S15Sa9S19R12A1RfR1A3VTR;S40S30S34S30S81S83VKc;Vrho0;G8VFB;S0G1S1SfSfS13SaaS19R13A1G7A2A1SbaR12G5A2A4RfA3ReA9Sc9R13R12R11G4A4R2A4RdA2F_;Frho';VTR;S40S30G9R12RfA4RcA2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Fam;Ftv;Frho;FR;Fs;FCl;") := ltac2:(tb__ "0|0|
S3eS30S81S9dS83VKc;Vrho0;S43VFB;A1VFB;VML;VTR;VTR_facts;VTR_ex;VTR_pre;VTR_callP;Ae").

Lemma bound_ge : ltac2:(tb__ "0|3|
S31S31S15SfS8bS94S95S97R4Z1A2M0S96Z2Z40A2M1A2S97S95R3G1A2SbcQ40S24R2R1A2A2A2A2M2S8cS94G0R3A2G2A2A2Fv;Frho;Fb;Fr;").
Proof using . intros. pose proof (urange (eval rho v)). nia. Qed.
Ltac reenter T tv am rT vT := apply (REENTER T tv am rT vT); [cbn; tauto | lia | first [lia | unfold ameas, ad_rank, ad_var; cbn [fst snd]; apply bound_ge; left; lia]].

Ltac via_ex T tv am rT vT :=
  apply (TR_pre (fun w => exists r, SPJ segs (JGv tv am) T r w)); [ | apply TR_exw; intros r; reenter T tv am rT vT ].

Lemma X_P_fail : ltac2:(tb__ "0|0|
S15S31VTR;S40S30VJGv;S42S8eA2S4fR2A4VFAM;R1A1A2Fb;Frho;").
Proof using POST nA. intros rho b. apply POST. cbn. tauto. Qed.
Lemma X_P_ok : ltac2:(tb__ "0|0|
S15S31VTR;S40S30VJGv;S42S51A2S50R2A4VFAM;R1A1A2Fb;Frho;").
Proof using POST nA. intros rho b. apply POST. cbn. tauto. Qed.

Lemma X_open_ok : ltac2:(tb__ "0|0|
S15S31S94S95Z5bS96Z2Z40A2A2R1A2VTR;S40S30VJGv;S42S8eA2S64R3A4VFAM;R2A1A2F_;Fb;Frho;").
Proof using ML REENTER TR_exw TR_pre nA.
  intros rho b Hb. via_ex C_open tv0 am_open 90 z0.
  intros w Hw.
  destruct (JGA_open segs C_P NF Kc rho0 (P0_ad FB) FB ML TobjJVA.NP_ok_NF tv0 vHD X_open is_src rho w) as (rho' & _ & Hw');
    [vm_compute; reflexivity | reflexivity | reflexivity | reflexivity | vm_compute; reflexivity | | vm_compute; reflexivity | exact Hw |].
  - by_src.
  - exists rho'. exact Hw'.
Qed.

Ltac nofit X Xc s :=
  intros rho b Hb; via_ex C_slow tv0 ahd 80 z0;
  intros w Hw;
  destruct (JGA_close segs C_P NF Kc rho0 (P0_ad FB) FB ML tv0 vHD (SVar 100) (SVar 101) (SVar 102) X
              (firstn 4 (ss_objs X)) (nth 4 (ss_objs X) O_D) rho w) as (rho' & _ & Hw');
    [vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | exact Hw |];
  change (drop_last_state X (firstn 4 (ss_objs X))) with Xc in Hw';
  exists (rho_sub rho' s);
  eapply (SPJ_entails_JGA segs C_P NF Kc rho0 (P0_ad FB) FB ML Xc C_slow s tv0 tv0 ahd ahd);
    [vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | exact Hw'].
Lemma X_nofit1_ok : ltac2:(tb__ "0|0|
S15S31S94S95Z51S96Z2Z40A2A2R1A2VTR;S40S30VJGv;S42S49A2S62R3A4VFAM;R2A1A2F_;Fb;Frho;").
Proof using ML REENTER TR_exw TR_pre nA. nofit X_nofit1 X_nofit1c s_nofit1. Qed.
Lemma X_nofit2_ok : ltac2:(tb__ "0|0|
S15S31S94S95Z51S96Z2Z40A2A2R1A2VTR;S40S30VJGv;S42S49A2S63R3A4VFAM;R2A1A2F_;Fb;Frho;").
Proof using ML REENTER TR_exw TR_pre nA. nofit X_nofit2 X_nofit2c s_nofit2. Qed.

Lemma X_fit_ok : ltac2:(tb__ "0|0|
S15S31S94S95Z33S96Z2Z40A2A2R1A2VTR;S40S30VJGv;S42S49A2S61R3A4VFAM;R2A1A2F_;Fb;Frho;").
Proof using ML REENTER TR_exw TR_pre nA.
  intros rho b Hb. via_ex C_loop tv0 am_loop 50 cp_var.
  intros w Hw. exists (rho_sub rho s_fit).
  eapply (SPJ_entails_JGA segs C_P NF Kc rho0 (P0_ad FB) FB ML X_fit4 C_loop s_fit tv0 tv0 (AOpen vHD (SVar 100) (SVar 101) [(p_fit, vSZ)]) am_loop);
    [vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | vm_compute; reflexivity |].
  apply SPJ_refacts_J; [| reflexivity |].
  { apply (JGA_carve segs C_P NF Kc rho0 (P0_ad FB) FB ML TobjJVA.NP_ok_NF tv0 vHD (SVar 100) (SVar 101) p_fit vSZ X_fit is_src rho w);
      [vm_compute; reflexivity | reflexivity | vm_compute; reflexivity | | | exact Hw].
    - by_src.
    - intros HP0 Hav HF. clear - HF. cbv beta. unfold p_fit, vHD, vSZ, HDR.
      pick_facts HF [0%nat; 2%nat; 3%nat; 4%nat; 5%nat; 6%nat; 7%nat; 16%nat; 17%nat; 18%nat]. zfacts; lia. }
  intros tr md _ HF. clear - HF. unfold fit_facts, p_fit, vSZ, aceil.
  pick_facts HF [0%nat; 2%nat; 3%nat; 4%nat; 5%nat; 6%nat; 7%nat; 16%nat; 17%nat; 18%nat]. zfacts; lia.
Qed.

Lemma X_E_malloc : ltac2:(tb__ "0|2|
S15VTR;S40S30VJGv;S42S8eA2S4eR1A4VFAM;S39S1S2S10S2S4S2SfSfA2A1M0S33A2M1A2S2S31SfA2S1S10G1S4eS1G0S33S42S8eA4A4S1S31SfZ46S8dA4A4R1A2A1A2Frho;").
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
    + eapply (robjs_check_sound segs C_P FB Ai rho (ss_facts E_malloc) tv0 None is_src R_malloc None rhoM md HM HT HF HN HD HZ); [vm_compute; reflexivity | | exact I].
      intros o a Ho Hx Hr. apply (pclF_caddrT segs C_P NF rho0 FB TobjJVA.NP_ok_NF rho Ai a Hav HT HP). eapply (src_pclF _ _ rho o a Ho Hx HP0 Hav HF); [in_list | exact Hr].
    + change (wsub_get s_malloc 12) with (SAlu ALU_ADD vK (SLit 32)). clear - HF. unfold vK. pick_facts HF [0%nat; 1%nat]. zfacts; lia.
  - intros rho' _.
    replace (T_after E_malloc s_malloc R_malloc (L_malloc_null EC_P)) with T_mnull by (vm_compute; reflexivity).
    reenter T_mnull tv0 ahd 65 z0.
  - intros rho' _.
    replace (T_after E_malloc s_malloc R_malloc (L_malloc_ok EC_P)) with T_mok0 by (vm_compute; reflexivity).
    change (pos_add_nat (ss_next E_malloc) 10) with vN.
    change (wsub_get s_malloc 12) with (SAlu ALU_ADD vK (SLit 32)).
    eapply TR_pre; [ | reenter T_mok tv_m ahd 65 z0 ].
    intros w Hw. unfold T_mok. apply SPJ_refacts_J; [exact Hw | reflexivity |].
    intros tr md HJ HF.
    eapply (JGA_tv_facts segs C_P NF Kc rho0 (P0_ad FB) FB); [exact HJ | left; reflexivity |].
    eapply (tnz_of_fact rho' (SVar vN)). pick_facts HF [22%nat]. assumption.
Qed.

Lemma X_push_ok : ltac2:(tb__ "0|0|
S15S31S94S95Z33S96Z2Z40A2A2R1A2VTR;S40S30VJGv;S5dS8eA2S65R3A4VFAM;R2A1A2F_;Fb;Frho;").
Proof using ML REENTER TR_exw TR_pre nA.
  intros rho b Hb. via_ex C_loop tv0 am_loop 50 cp_var.
  intros w Hw.
  pose proof (SPJ_xforms segs (JGv tv_m ahd) [XSelect [2; 0; 3; 4; 1]%nat; XSplit 4 (SLit 24)] rho X_push X_push1 w
                ltac:(vm_compute; reflexivity) Hw) as Hw1.
  destruct (JGA_push_open segs C_P NF Kc rho0 (P0_ad FB) FB ML tv_m 0%nat blkN vHD vK used_new X_push1
              (firstn 4 (ss_objs X_push1)) (nth 4 (ss_objs X_push1) O_D) (nth 5 (ss_objs X_push1) O_D) rho w)
    as (rho1 & _ & Hw2);
    [vm_compute; reflexivity | reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
    | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
    | vm_compute; reflexivity | exact Hw1 |].
  change (drop_last_state X_push1 (firstn 4 (ss_objs X_push1) ++ [nth 4 (ss_objs X_push1) O_D])) with X_push2 in Hw2.
  change (remove_nth 0 tv_m) with tv0 in Hw2. change (fst blkN) with (SVar vN) in Hw2.
  exists (rho_sub rho1 s_push).
  eapply (SPJ_entails_JGA segs C_P NF Kc rho0 (P0_ad FB) FB ML X_push3 C_loop s_push tv0 tv0 (AOpen (SVar vN) vHD vK [(p_new, vSZ)]) am_loop);
    [vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | vm_compute; reflexivity |].
  apply (JGA_carve segs C_P NF Kc rho0 (P0_ad FB) FB ML TobjJVA.NP_ok_NF tv0 (SVar vN) vHD vK p_new vSZ X_push2 is_src rho1 w);
    [vm_compute; reflexivity | reflexivity | vm_compute; reflexivity | | | exact Hw2].
  - by_src.
  - intros HP0 Hav HF. clear - HF. cbv beta. unfold p_new, vHD, vSZ, vK, vN, HDR.
    pick_facts HF [0%nat; 1%nat; 5%nat; 6%nat; 14%nat; 15%nat; 16%nat]. zfacts; lia.
Qed.

Lemma X_ret_ok : ltac2:(tb__ "0|0|
S15S31VTR;S40S30VJGv;S42S5aA2S66R2A4VFAM;R1A1A2Fb;Frho;").
Proof using ML POST TR_exw TR_pre nA.
  intros rho b.
  apply (TR_pre (fun w => exists r, SPJ segs (JGv tv0 am_ok) P_ok r w)); [ | apply TR_exw; intros r; apply X_P_ok ].
  intros w Hw.
  destruct (JGA_unslot segs C_P NF Kc rho0 (P0_ad FB) FB ML tv0 vH vNX vCAP vP vSZ X_ret (firstn 5 (ss_objs X_ret)) (nth 5 (ss_objs X_ret) O_D) rho w)
    as (rho1 & _ & Hw1); [vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | exact Hw |].
  change (drop_last_state X_ret (firstn 5 (ss_objs X_ret))) with X_ret1 in Hw1.
  destruct (JGA_close segs C_P NF Kc rho0 (P0_ad FB) FB ML tv0 vH vNX vCAP vU X_ret1 (firstn 4 (ss_objs X_ret1)) (nth 4 (ss_objs X_ret1) O_D) rho1 w)
    as (rho2 & _ & Hw2); [vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | exact Hw1 |].
  change (drop_last_state X_ret1 (firstn 4 (ss_objs X_ret1))) with X_ret2 in Hw2.
  exists (rho_sub rho2 s_ret).
  eapply (SPJ_entails_JGA segs C_P NF Kc rho0 (P0_ad FB) FB ML X_ret2 P_ok s_ret tv0 tv0 (AHead vH) am_ok);
    [vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | vm_compute; reflexivity | exact Hw2].
Qed.

Lemma exits_okT : ltac2:(tb__ "0|4|
S10S4S2SfSfA2A1M0S33S2S31SfA2M1S15Sb1S2S2S10S2G0S33A2M2A2M3G1A2S1G3G1S1S10G2R5S1G0S33R4R3A4A4R2A4S91A3VTR;S40S30VJGv;R5R4A2R6R2A4VFAM;S39S1G3G1S1S10G2R6S1G0S33R5R4A4A4R3A4R2A2A1A2F_;Frho;FrvX;FamX;FtvX;FX;").
Proof using CMALLOC MALLOC POST REENTER TR_exw nA.
  intros X tvX amX rvX rho Hin. cbn [exitsE In] in Hin.
  destruct Hin as [H|[H|[H|[H|[H|[H|[H|[H|[H|[]]]]]]]]]]; injection H as <- <- <- <-;
    unfold ameas, ad_rank, ad_var; cbn [fst snd].
  - apply X_open_ok. pose proof (urange (eval rho z0)). lia.
  - apply X_fit_ok. pose proof (urange (eval rho z0)). lia.
  - apply X_nofit1_ok. pose proof (urange (eval rho z0)). lia.
  - apply X_nofit2_ok. pose proof (urange (eval rho z0)). lia.
  - apply X_E_malloc.
  - apply X_push_ok. pose proof (urange (eval rho z0)). lia.
  - apply X_ret_ok.
  - apply X_P_fail.
  - apply X_P_ok.
Qed.
End SumT.

Section Safety.
Theorem arena_dup_sum : ltac2:(tb__ "0|0|
Sb6S30Vok;S40S30S38S30S81VKc;S43VFB;A1VFB;S42S8eA7S59Vrho0;A4Sa8S30S83Vrho0;S8fA4A4").
Proof using HS MC ML.
  eapply triple_conseq; [ | intros w Hw; exact Hw | ].
  2: { apply (cfg_sound_JGAE segs C_P NF Kc rho0 (P0_ad FB) FB ML FUEL_ad cutpcs_ad 100 cutsE exitsE ok Q (proj1 HS)
                (ejcertA_jcertA segs NF _ _ _ _ _ ejcert_ok)) with (rvT := (100, z0)); [|left; reflexivity].
       apply (exits_okT (triple segs ok) (fun _ w => SPfamGJ segs (map nA (map (@adrop) cutsE)) w \/ Q w)
                (triple_factsJ segs ok) (triple_SPJ_ex segs ok)
                (fun P P' Q' HP H => @triple_conseq segs ok P P' Q' Q' HP (fun w Hw => Hw) H)
                (fun A P Q' H => @triple_ex segs ok A P Q' H)
                (call_soundP segs ok)).
       - intros Ai rho1. apply (mc_malloc _ _ _ MC). exact HS.
       - intros T tv am rT vT rho b Hin _ _. exact (reenter_cutGAE segs C_P NF Kc rho0 (P0_ad FB) FB ok cutsE T tv am (rT, vT) Q rho Hin).
       - intros P tv am rho b Hin. apply (exit_postGA segs C_P NF Kc (P0_ad FB) FB ok rho0 tv am Posts_ad P). exact Hin. }
  intros w Hw. apply JGA_pre_intro. exact Hw.
Qed.
End Safety.

Section Existence.
Hypothesis Hvi : vm_insensitive Kc.
Hypothesis MCX : ltac2:(tb__ "0|0|
SceS30S81S9dA3").

Theorem arena_dup_sum_ex : ltac2:(tb__ "0|0|
Sb5S30S40S30S38S30S81VKc;S43VFB;A1VFB;S42S8eA7S59Vrho0;A4Sa8S30S83Vrho0;S8fA4A3").
Proof using Hvi MCX ML.
  eapply etriple_conseq; [ | intros w Hw; exact Hw | ].
  2: { apply (cfg_complete_JGA segs C_P NF Kc rho0 (P0_ad FB) FB ML FUEL_ad cutpcs_ad 100 cutsE exitsE Q ejcert_ok) with (rvT := (100, z0)); [|left; reflexivity].
       apply (exits_okT (etriple segs) (fun b w => SPfamEJ segs (map (enodeA segs C_P NF Kc rho0 (P0_ad FB) FB) cutsE) b w \/ Q w)
                (etriple_factsJ segs) (etriple_SPJ_ex segs)
                (fun P P' Q' HP H => @etriple_conseq segs P P' Q' Q' HP (fun w Hw => Hw) H)
                (fun A P Q' H => @etriple_ex segs A P Q' H)
                (call_completeP segs)).
       - intros Ai rho1. apply (mcx_malloc _ _ _ MCX). exact Hvi.
       - intros T tv am rT vT rho b Hin H0 Hb. apply (ereenter_cutAE segs C_P NF Kc rho0 (P0_ad FB) FB cutsE T tv am (rT, vT) Q b rho Hin).
         unfold ameas, ad_rank, ad_var. cbn [fst snd]. pose proof (urange (eval rho vT)). nia.
       - intros P tv am rho b Hin. apply (eexit_postGA segs C_P NF Kc (P0_ad FB) FB rho0 tv am Posts_ad P). exact Hin. }
  intros w Hw. apply JGA_pre_intro. exact Hw.
Qed.
End Existence.
End Sum.
