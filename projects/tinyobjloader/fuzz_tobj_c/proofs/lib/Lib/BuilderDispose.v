(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "pair"; "prod"; "nat"; "bool"; "andb"; "nil"; "true"; "list"; "false"; "S"; "app"; "option"; "fst"; "snd"; "Some"; "None"; "length"; "negb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sstate"; "SLit"; "sobj"; "cell"; "sprop"; "mkCell"; "valuation"; "sv_eqb"; "SVar"; "SPUle"; "SPBranch"; "DUnknown"; "mkObj"; "ss_next"; "sprop_eqb"; "ss_facts"; "FcsrFrm0"; "SPNot"; "mkSS"; "ss_objs"; "SAlu"; "ob_base"; "ob_hi"; "ob_lo"; "SMd"; "SPAlign"; "ss_pc"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.BuilderDispose.BuilderDispose"; "NP"; "tvL"; "lives"; "z0"; "rL"; "E_"; "NV"; "C_"; "FUEL_bd"; "K_"; "cutpcs_bd"; "s_of"; "tvE"; "cutsE"; "L_"; "R_of"; "vB"; "P0_bd"; "P_bd"; "live"; "vAl"; "vDp"; "Pre_bd"; "bd_facts"; "chkE"; "chkK"; "exitsE"; "objs_at"; "vd"; "NXC"; "O_Db"; "O_dead"; "bd_jalrs"; "isSomeb"; "live_from"; "spo"; "voff"; "vsz"; "F_cells_bd"; "bd_entry"; "bd_vecs"; "cutsD"; "exitsD"; "in_regs"; "leaf_at"; "pcL"; "vel"; "vk"; "Cnode"; "O_Fb"; "O_alb"; "O_dat"; "O_palloc"; "O_piece"; "bd_ret"; "chkE'"; "chkK'"; "dats"; "dead_cells"; "oget"; "pcJ"; "piece_cells"; "pieces"; "run_of"; "src_"; "two47"; "@Corelib.Init.Logic"; "eq"; "and"; "or"; "ex"; "@Stdlib.Lists.List"; "In"; "existsb"; "filter"; "forallb"; "last"; "removelast"; "concat"; "rev"; "@Corelib.Lists.ListDef"; "map"; "seq"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "SPJ"; "@Stdlib.ZArith.BinInt.Z"; "sub"; "add"; "opp"; "le"; "eqb"; "mul"; "of_nat"; "pow"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "tv_below"; "ejcert"; "emeas"; "remove_nth"; "edesc"; "T_after"; "call_checkT"; "jcert"; "robjs_check"; "JG_pre"; "tv_sub_eqb"; "JG"; "JLG"; "ed_rank"; "enodeI"; "malloc_contracts"; "malloc_contracts_ex"; "nodeI"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "of_nat"; "@LinuxProcessSemantics.Riscv.Instr"; "BC_EQ"; "ALU_ADD"; "BC_GE"; "M_MUL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "entails_fr"; "entails"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "wsub"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract"; "L_free"; "Pre_free"; "ec_free"; "ok_sideK"; "@Corelib.Init.Peano"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.BuilderDispose"; "FRAME_bd"; "bc_free"; "bc_alloc"; "bc_calloc"; "bc_xfacts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform"; "xform"; "XSelect"; "apply_xforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "pre_fregs"; "setregs"; "cut_regs"; "post_regs"; "pre_regs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "enodeJ"; "jnode"; "SPfamEJ"; "SPfamGJ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "LQP"; "jpost"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.BuilderDispose.BuilderDispose.Sum"; "Posts_bd"; "@Stdlib.Arith.PeanoNat.Nat"; "ltb"; "eqb"; "@Corelib.Init.Nat"; "add"; "mul"; "sub";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "leaf"; "set_objs"; "lf_state"; "sym_run"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "free_stack"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Contract.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CfgGlue CursorGlue ObjUnbase ObjXform TobjJV.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Record bd_code := BDC {
  bc_entry : Z;
  bc_ret : Z;
  bc_jalrs : list Z;
  bc_alloc : Z; bc_calloc : Z; bc_free : Z;
  bc_xfacts : list sprop
}.
Definition FRAME_bd : Z := 32.

Section BuilderDispose.
Variable segs : list Segment.
Variable bc : bd_code.
Variable Cb : mconsts.
Variable ECb : entry_consts.
Definition bd_entry : Z := bc_entry bc.
Definition bd_ret : Z := bc_ret bc.
Definition bd_jalrs : list Z := bc_jalrs bc.

Definition NV : nat := 33%nat.
Definition bd_vecs : list (Z * Z) := ltac2:(tb__ "0|4|
S0S2S2fS2fA2M0S1S2fS2fZ78Z4M1A4S0G0S1S2fS2fZ98G1A4S0G0S1S2fS2fZb8G1A4S0G0S1S2fS2fZd8G1A4S0G0S1S2fS2fZf8G1A4S0G0S1S2fS2fZ118G1A4S0G0S1S2fS2fZ140Z490A4S0G0S1S2fS2fZ160Z8A4S0G0S1S2fS2fZ180G1A4S0G0S1S2fS2fZ1a0Z18A4S0G0S1S2fS2fZ1c0Z80M2A4S0G0S1S2fS2fZ1f0ZcM3A4S0G0S1S2fS2fZ210G1A4S0G0S1S2fS2fZ230G1A4S0G0S1S2fS2fZ250G1A4S0G0S1S2fS2fZ270G3A4S0G0S1S2fS2fZ290G1A4S0G0S1S2fS2fZ2b0G3A4S0G0S1S2fS2fZ2d0G3A4S0G0S1S2fS2fZ2f0G1A4S0G0S1S2fS2fZ310G1A4S0G0S1S2fS2fZ330Z1A4S0G0S1S2fS2fZ350G1A4S0G0S1S2fS2fZ3a8G1A4S0G0S1S2fS2fZ3c8G3A4S0G0S1S2fS2fZ3e8G1A4S0G0S1S2fS2fZ408G1A4S0G0S1S2fS2fZ428G3A4S0G0S1S2fS2fZ448G3A4S0G0S1S2fS2fZ468G3A4S0G0S1S2fS2fZ488Z38A4S0G0S1S2fS2fZ4a8Z30A4S0G0S1S2fS2fZ4c8G2A4S6G0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition bd_live : list bool := ltac2:(tb__ "0|0|
S0S4S7S0S4S7S0S4S7S0S4S7S0S4S7S0S4S7S0S4S9S0S4S9S0S4S9S0S4S9S0S4S7S0S4S7S0S4S7S0S4S7S0S4S7S0S4S7S0S4S7S0S4S7S0S4S7S0S4S7S0S4S7S0S4S7S0S4S9S0S4S9S0S4S9S0S4S9S0S4S9S0S4S9S0S4S9S0S4S9S0S4S9S0S4S9S0S4S9S6S4A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition live (j : nat) : bool := nth j bd_live false.
Definition voff (j : nat) : Z := ltac2:(tb__ "0|1|
SdS2fS2fS81S2S2fS2fA2Vj;S59S1S2fS2fZ0M0G0A4A4A3").
Definition vel (j : nat) : Z := ltac2:(tb__ "0|1|
SeS2fS2fS81S2S2fS2fA2Vj;S59S1S2fS2fZ0M0G0A4A4A3").

Definition pcL (i : nat) : Z := ltac2:(tb__ "0|0|
S81S2fVi;S0S2fS58S7fS2fS2fS2fS84R1Z4A2La;S51A4A3Z0A4").
Definition pcJ (i : nat) : Z := nth i bd_jalrs 0.

Definition NP : positive := 200%positive.
Definition NXC : positive := 232%positive.
Definition vB : sv := SVar 12.
Definition vAl : sv := SVar 16.
Definition vDp : sv := SVar 19.
Definition vd (j : nat) : sv := ltac2:(tb__ "0|0|
S1cSa2Sc8U64Sc9U2Vj;A2A2A1A1").
Definition vk (j : nat) : sv := ltac2:(tb__ "0|0|
S1cSa2Sc8U65Sc9U2Vj;A2A2A1A1").
Definition vsz (j : nat) : sv := ltac2:(tb__ "0|0|
S2cSa6S15S5fVj;A1A1S60Vj;A1A3").
Definition tvE (j : nat) : sv * sv := ltac2:(tb__ "0|0|
S1S13S13S4dVj;A1S56Vj;A1A4").
Definition spo (k : Z) : sv := ltac2:(tb__ "0|0|
S28Sa4S1cPaA1S15Vk;A1A3").
Definition two47 : Z := 2 ^ 47.

Definition bd_facts : list sprop := ltac2:(tb__ "0|4|
SbS18S0S18S2dPaM0Z4A2S0S18S1eSa5S15S85Sd1A1A1S46A3S0S18S1eSa5S46S15S85S8aZ2Z28A2A1A1A3S0S18S1dS1cP1eA1M1S28Sa4S54S85Sb1A1A1S46A3A2S0S18S1dS28Sa4G1S15Sb1A1A3S1cG0A1M2A2S0S18S1dG2S15S72A1M3A2S0S18S1dG1S41A2S0S18S1dS41G3A2S0S18S1dG1S45A2S0S18S1dS45G3A2S0S18S1dS15Z7fff7f800000A1G1A2S0S18S1dG1S15Z7fffff800000A1A2S6S18A1A3A3A3A3A3A3A3A3A3A3A3A3Sb5Vbc;A1A3").

Definition O_Fb (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S20S1cPaA1S15S85Sb1A1A1S15Z0A1Vcells;S1fA5").
Definition F_cells_bd : list cell := ltac2:(tb__ "0|1|
S0S17S19S15N8A1Z8M0S1cPbA1A3S0S17S19S15N10A1G0S1cP1cA1A3S0S17S19S15N18A1G0S1cP1dA1A3S6S17A1A3A3A3").
Definition O_Db : sobj := ltac2:(tb__ "0|0|
S20S54S85Sb1A1A1S46S15Z0A1S6S17A1S1fA5").
Definition O_palloc : sobj := ltac2:(tb__ "0|2|
S20S41S15Z0A1M0S15Z8M1A1S0S17S19G0G1S45A3S6S17A1A3S1fA5").
Definition O_alb : sobj := ltac2:(tb__ "0|2|
S20S45S15Z0A1M0S15Z30A1S0S17S19G0Z8M1S15Sb3Vbc;A1A1A3S0S17S19S15G1A1G1S15Sb4Vbc;A1A1A3S0S17S19S15Z10A1G1G0A3S0S17S19S15Z18A1G1S15Sb2Vbc;A1A1A3S0S17S19S15Z20A1G1G0A3S0S17S19S15Z28A1G1G0A3S6S17A1A3A3A3A3A3A3S1fA5").

Definition piece_cells (zeroed : bool) (j : nat) : list cell := ltac2:(tb__ "0|6|
S4S8S17A1Lzeroed;Vzeroed;S0S17S19S15S55Vj;A1M0A1M1Z8M2S15Z0A1M3A3S0S17S19S15S84G0G2A2A1G2G3A3S0S17S19S15S84G0Z10A2A1M4G2G3A3S0S17S19S15S84G0Z18A2A1G2S15S5fVj;A1A1A3S6S17A1A3M5A3A3A3S0S17S19G1G2S4dVj;A1A3S0S17S19G4G2S60Vj;A1A3G5A3A3X4x2").
Definition O_piece (nz : nat) (j : nat) : sobj := ltac2:(tb__ "0|1|
S20S41S15S55Vj;A1M0A1S15S84G0Z20A2A1S6eSc6Vj;Vnz;A2Vj;A2S1fA5").

Definition dead_cells (nz : nat) (j : nat) : list cell := ltac2:(tb__ "0|5|
S4S8S17A1L_;Sc6Vj;Vnz;A2S0S17S19S15S55Vj;A1M0A1Z8M1S15Z0A1M2A3M3S0S17S19S15S84G0G1A2A1G1G2A3S0S17S19S15S84G0Z10A2A1G1G2A3S6S17A1M4A3A3A3S0S17G3G4A3X4x2").
Definition O_dead (nz : nat) (lo hi : Z) (js : list nat) : sobj := ltac2:(tb__ "0|0|
S20S41S15Vlo;A1S15Vhi;A1S7dS17S7fS3S8S17A1S6bVnz;A1Vjs;A4A2S1fA5").
Definition pieces (nz : nat) : list sobj := ltac2:(tb__ "0|1|
SbS16S7fS3S16S66Vnz;A1S79S3S44S80U0S37A2A3A4S0S16S50Vnz;Z140Z1c0S0S3U6S0S3U7S0S3U8S0S3U9S6S3A1M0A3A3A3A3A4S0S16S50Vnz;Z350Z370S0S3U16G0A3A4S0S16S50Vnz;Z3a8Z4e8S80U17UaA2A4S6S16A1A3A3A3A3").
Definition O_dat (j : nat) : sobj := ltac2:(tb__ "0|0|
S20S4dVj;A1S15Z0A1S56Vj;A1S6S17A1S1fA5").

Definition live_from (i : nat) : list nat := ltac2:(tb__ "0|0|
S79S3S44S80Vi;ScaS37Vi;A2A2A3").
Definition dats (i : nat) : list sobj := ltac2:(tb__ "0|0|
S7fS3S16S64S7eS3S53Vi;A1A2A4").
Definition tvL (i : nat) : list (sv * sv) := map tvE (live_from i).
Definition objs_at (nz i : nat) (fcells : list cell) : list sobj := ltac2:(tb__ "0|0|
SbS16S0S16S4fS0S16S62Vfcells;A1S0S16S65S0S16S63S6S16A1A3A3A3A3SbS16S6fVnz;A1S6aVi;A1A3A3").

Definition Pre_bd : sstate := ltac2:(tb__ "0|2|
S26S58SbaSbdS0S2S3S13A2M0S1S3S13UaS41A4S6G0A1A3A2Sb9S24S10S13A1S4cU0M1G1S6S17A1A3S48S31S9A9").
Definition in_regs : list sv := ltac2:(tb__ "0|1|
SbaSbbS31A1S0S2S3S13A2M0S1S3S13U1S1cPc8A1A4S0G0S1S3S13U2S54S85Sb1A1A1A4S0G0S1S3S13U8S41A4S0G0S1S3S13U9S45A4S6G0A1A3A3A3A3A2").

Definition L_ (i : nat) : sstate := ltac2:(tb__ "0|0|
S26S5eVi;A1S5cSb9S24S10S13A1S4cScaVi;U1A2Vi;S57A3S48S4eS9A9").

Definition C_ (i : nat) : sstate := ltac2:(tb__ "0|3|
S26S6dVi;A1SbaS5cS0S2S3S13A2M0S1S3S13UaS15Z0A1M1A4S0G0S1S3S13UbS4dVi;A1M2A4S0G0S1S3S13UdS15Sb2Vbc;A1A1A4S6G0A1A3A3A3A2Sb9S24S10S13A1S4cVi;Vi;S57A3S0S18S25S1eSa3G2G1A3A1S48A3S4eS9A9").
Definition P_bd : sstate := ltac2:(tb__ "0|0|
S26S67SbcS31A1Sb9S24S10S13A1S4cS37S37S6S17A1A3S48S4eS9A9").

Definition FUEL_bd : nat := 200%nat.
Definition cutpcs_bd : list Z := ltac2:(tb__ "0|0|
S0S2fSaeVECb;A1SbS2fS51S7fS2fS2fS2fS84R1Z4A2La;S51A4A3A3").
Definition run_of (S : sstate) : list sstate := ltac2:(tb__ "0|1|
ScS8ScbA1M0A1S8S14A1Lx;SceVsegs;S39S3bVS;S7A5G0S7fScbS14ScdR1A4Lls;S6S14A1Xcx2").
Definition leaf_at (S : sstate) (pc : Z) : sstate := ltac2:(tb__ "0|0|
S81S14U0S79S14S14S87S2eR1A1Vpc;A2Ll;S70VS;A1A3VS;A4").
Definition src_ (i : nat) : sstate := ltac2:(tb__ "0|0|
S3S14Li;Vi;S47S3S3fVi;A1Ln;X3x2").

Definition E_ (i : nat) : sstate := ltac2:(tb__ "0|0|
S5dS38Vi;A1SaeVECb;A1A2").
Definition K_ (i : nat) : sstate := ltac2:(tb__ "0|0|
S5dS71Vi;A1S5eSaVi;A1A1A2").

Definition oget {A} (o : option (list A)) : list A := match o with Some l => l | None => [] end.
Definition s_of (i : nat) (E : sstate) : wsub := ltac2:(tb__ "0|1|
S0S2S30S13A2M0S1S30S13PfS46A4S0G0S1S30S13PdS56Vi;A1A4SbePaVE;SadVECb;A1A3A3A3").
Definition R_of (i : nat) (E : sstate) : list sobj := ltac2:(tb__ "0|0|
S6cS16Sa7VE;SadVECb;A1S3cVi;VE;A2A3A2").

Definition T_ (i : nat) : sstate := ltac2:(tb__ "0|1|
S94S36Vi;A1M0S3cVi;G0A2S40Vi;G0A2SacVECb;A1A4").
Definition tvT (i : nat) : list (sv * sv) := ltac2:(tb__ "0|1|
S92S2S13S13A2M0U0S0G0S3dVi;A1S32SaVi;A1A1A3A3").

Definition lives : list nat := live_from 0.

Definition rL (i : nat) : Z := ltac2:(tb__ "0|0|
S84S88ZaS83Z22S89Vi;A1A2A2Z5A2").
Definition z0 : sv := SLit 0.
Definition cutsE : list edesc := ltac2:(tb__ "0|8|
S0S2S2S14S8S2S13S13A2M0A1M1A2M2S2S2fS13A2M3A2M4S1G2G3S1S14G1S47S32U0M5A1A4S1S2fS13S35G5A1S34A4A4SbG4S7fS3G4S3S1G2G3S1S14G1S3fR1A1S32R1A1A4S1S2fS13S35R1A1M6S34A4A4Li;S80U1S37A2A4S7fS3G4S3S1G2G3S1S14G1S94S36R1A1M7S3cR1G7A2S40R1G7A2SacVECb;A1A4S92G0G5S0G0S3dR1A1S32SaR1A1A1A3A3A4S1S2fS13S83G6Z3A2S34A4A4Li;S33A4A3A3").

Definition exitsE : list edesc := ltac2:(tb__ "0|7|
SbS2S2S14S8S2S13S13A2M0A1M1A2M2S2S2fS13A2M3A2M4S7fS3G4S3S1G2G3S1S14G1S38R1A1S32R1A1M5A4S1S2fS13S83S35R1A1Z1A2S34A4M6A4Li;S33A4SbG4S7fS3G4S3S1G2G3S1S14G1S3aR1A1G5A4G6A4Li;S33A4S0G4S1G2G3S1S14G1S43S6G0A1A4S1S2fS13Z0S34A4A4S6G4A1A3A3A3").
Definition Cnode (i : nat) : edesc := ltac2:(tb__ "0|1|
S1S2S14S8S2S13S13A2A1M0A2S2S2fS13A2S1S14G0S38Vi;A1S32Vi;A1A4S1S2fS13S83S35Vi;A1Z1A2S34A4A4").
Definition Enode (i : nat) : edesc := ltac2:(tb__ "0|1|
S1S2S14S8S2S13S13A2A1M0A2S2S2fS13A2S1S14G0S36Vi;A1S32Vi;A1A4S1S2fS13S83S35Vi;A1Z2A2S34A4A4").

Definition cutsD : list (sstate * list (sv * sv)) := map (@edrop) cutsE.
Definition exitsD : list (sstate * list (sv * sv)) := map (@edrop) exitsE.

Definition isSomeb {A} (o : option A) : bool := match o with Some _ => true | None => false end.

Definition chkE' (i : nat) (E : sstate) : bool := ltac2:(tb__ "0|8|
S5S5S5S5S5S5S5S52S8S16A1Sa7VE;SadVECb;A1M0S3cVi;VE;A2M1A3A2S95VCb;S31VE;G0G1S40Vi;VE;A2M2S0S14SacVECb;A1S6S14A1A3A7A2Sa1S31S21VE;A1M3A2A2S8fG3S0S2S13S13A2S3dVi;A1M4S32SaVi;A1A1A3M5A2A2S1bSdS13S13G4A3M6Sa9G1PcA2A2A2S1bSeS13S13G4A3Sa9G1PdA2A2A2S78S18S22S25S1eSa3G6S15Z0A1A3A1A1S23VE;A1M7A3A2S97G7G5SfS3U0A2S16S9L_;G2A5A2").
Definition chkE (i : nat) : bool := ltac2:(tb__ "0|0|
S68Vi;S36Vi;A1A2").

Definition chkK' (i : nat) (K : sstate) : bool := ltac2:(tb__ "0|c|
ScS14A1S4Lx;Sb8VK;S0Sb6Sb7S80U0M0S11S16S27VK;A1A2A2A1S6Sb6A1A3A2S14S27R1A1S8S16A1S7bS16R1S4fA3S16SccR3S7cS16R2A2A2S14SbeS31R1S3fSaVi;A1M1A1M2A3SaaS5S5S5S5S5S5S5S5S5S5S5S12Sc7S11S16R4A2G0A2A1S1bS29R3A1SdS13S13S3dVi;A1M3A3M4A2A2S1bS2bR3A1S15Z0A1M5A2A2S1bS2aR3A1SeS13S13G3A3A2A2S78S18S22S1eSa3G4G5A3A1S23VK;A1A3A2Sa1S31S21R5A1M6A2A2S8fG6S0S2S13S13A2M7G3S32G1A1M8A3M9A2A2Sa8R2G2R1A3A2SabR1S31A2A2Sa1S31S21R2A1MaA2A2S8fGaS92G7G0G9A3MbA2A2S99R1GbG8A3A2TsK;TK1;To;Tos;LX1;S9Xcx2").
Definition chkK (i : nat) : bool := ltac2:(tb__ "0|0|
S69Vi;S3aVi;A1A2").

Definition bd_chk_stmt : Prop := ltac2:(tb__ "0|a|
S73S4S7aS3S3S5S5S96Vsegs;S31S39S3bS31S0S2S14S8S2S13S13A2A1M0A2M1S1S14G0S38R1A1S32R1A1M2A4M3S6G1A1M4A3S0G1S1S14G0S36R1A1G2A4M5G4A3A7S90Vsegs;S31S39S3bS31S0S2G1S2S2fS13A2M6A2M7S1G1G6G3S1S2fS13S83S35R1A1M8Z1A2S34A4A4S6G7A1M9A3S0G7S1G1G6G5S1S2fS13S83G8Z2A2S34A4A4G9A3A7A2S5S49R1A1S4aR1A1A2A2Li;S33A3S7A3").
Definition bd_ejcert_stmt : Prop := ltac2:(tb__ "0|0|
S73S4S90Vsegs;S31S39S3bS31S3eS4bA7S7A3").
Hypothesis bd_chk_ok : ltac2:(tb__ "0|a|
S73S4S7aS3S3S5S5S96Vsegs;S31S39S3bS31S0S2S14S8S2S13S13A2A1M0A2M1S1S14G0S38R1A1S32R1A1M2A4M3S6G1A1M4A3S0G1S1S14G0S36R1A1G2A4M5G4A3A7S90Vsegs;S31S39S3bS31S0S2G1S2S2fS13A2M6A2M7S1G1G6G3S1S2fS13S83S35R1A1M8Z1A2S34A4A4S6G7A1M9A3S0G7S1G1G6G5S1S2fS13S83G8Z2A2S34A4A4G9A3A7A2S5S49R1A1S4aR1A1A2A2Li;S33A3S7A3").
Hypothesis ejcert_ok : ltac2:(tb__ "0|0|
S73S4S90Vsegs;S31S39S3bS31S3eS4bA7S7A3").

Lemma chkE_unfold : ltac2:(tb__ "0|9|
S3S73S4S49R1A1S5S5S5S5S5S5S5S52S8S16A1Sa7S36R1A1M0SadVECb;A1M1S3cR1G0A2M2A3A2S95VCb;S31G0G1G2S40R1G0A2M3S0S14SacVECb;A1S6S14A1A3A7A2Sa1S31S21G0A1M4A2A2S8fG4S0S2S13S13A2S3dR1A1M5S32SaR1A1A1A3M6A2A2S1bSdS13S13G5A3M7Sa9G2PcA2A2A2S1bSeS13S13G5A3Sa9G2PdA2A2A2S78S18S22S25S1eSa3G7S15Z0A1A3A1A1S23G0A1M8A3A2S97G8G6SfS3U0A2S16S9L_;G3A5A2A3Fi;").
Proof using . intros i. match goal with |- _ = ?b => exact (@eq_refl bool b) end. Qed.
Lemma chkK_unfold : forall i, chkK i = ltac:(let b := eval cbv beta delta [chkK chkK'] in (chkK i) in exact b).
Proof using . intros i. match goal with |- _ = ?b => exact (@eq_refl bool b) end. Qed.

Lemma lives_specb : ltac2:(tb__ "0|0|
S73S4S7aS3S3S5Sc6R1S37A2S44R1A1A2Li;S33A3S7A3").
Proof using . vm_cast_no_check (@eq_refl bool true). Qed.

Lemma lives_spec : ltac2:(tb__ "0|0|
S3S77S3R1S33A3S74Sb0R2S37A2S73S4S44R2A1S7A3A2F_;Fi;").
Proof using .
  intros i H. pose proof (proj1 (forallb_forall _ _) lives_specb i H) as X. cbn beta in X.
  apply andb_prop in X as [A B]. apply Nat.ltb_lt in A. split; [exact A | exact B].
Qed.

Lemma live_from_cons : ltac2:(tb__ "0|0|
S3Sb0R1S37A2S73S4S44R2A1S7A3S73S8S3A1S53R3A1S0S3R3S53SaR3A1A1A3A3F_;F_;Fi;").
Proof using .
  intros i Hi Hl. unfold live_from.
  replace (NV - i)%nat with (S (NV - S i))%nat by lia. cbn [seq List.filter]. rewrite Hl. reflexivity.
Qed.

Lemma tvL_cons : ltac2:(tb__ "0|1|
S3Sb0R1S37A2S73S4S44R2A1S7A3S73S8S2S13S13A2M0A1S32R3A1S0G0S3dR3A1S32SaR3A1A1A3A3F_;F_;Fi;").
Proof using . intros i Hi Hl. unfold tvL. rewrite (live_from_cons i Hi Hl). reflexivity. Qed.

Lemma chk_at : ltac2:(tb__ "0|a|
S3S77S3R1S33A3S74S74S73S4S96Vsegs;S31S39S3bS31S0S2S14S8S2S13S13A2A1M0A2M1S1S14G0S38R2A1S32R2A1M2A4M3S6G1A1M4A3S0G1S1S14G0S36R2A1G2A4M5G4A3A7S7A3S73S4S90Vsegs;S31S39S3bS31S0S2G1S2S2fS13A2M6A2M7S1G1G6G3S1S2fS13S83S35R2A1M8Z1A2S34A4A4S6G7A1M9A3S0G7S1G1G6G5S1S2fS13S83G8Z2A2S34A4A4G9A3A7S7A3A2S74S73S4S49R2A1S7A3S73S4S4aR2A1S7A3A2A2F_;Fi;").
Proof using bd_chk_ok.
  intros i Hin. pose proof (proj1 (forallb_forall _ _) bd_chk_ok i Hin) as H. cbn beta in H.
  apply andb_prop in H as [H H3]. apply andb_prop in H as [H0 H2].
  apply andb_prop in H3 as [H3 H4].

  split; [split; [exact H0 | exact H2]|]. split; [exact H3 | exact H4].
Qed.

Lemma R_of_spec : ltac2:(tb__ "0|2|
S3S14S73S4S52S8S16A1M0Sa7R1SadVECb;A1M1S3cR2R1A2A3A2S7A3S73ScG0A1Sa7R2G1S3cR3R2A2A3SfG0S40R3R2A2A2A3F_;FE;Fi;").
Proof using . intros i E H. unfold R_of. destruct (entails_fr E (Pre_free ECb) (s_of i E)); [reflexivity | discriminate]. Qed.

Lemma exitsE_eq : ltac2:(tb__ "0|7|
S73S8S93A1S4bSbS2S2S14S8S2S13S13A2M0A1M1A2M2S2S2fS13A2M3A2M4S7fS3G4S3S1G2G3S1S14G1S38R1A1S32R1A1M5A4S1S2fS13S83S35R1A1Z1A2S34A4M6A4Li;S33A4SbG4S7fS3G4S3S1G2G3S1S14G1S3aR1A1G5A4G6A4Li;S33A4S0G4S1G2G3S1S14G1S43S6G0A1A4S1S2fS13Z0S34A4A4S6G4A1A3A3A3A3").
Proof using . match goal with |- _ = ?b => exact (@eq_refl _ b) end. Qed.

Lemma L_in_cutsE : ltac2:(tb__ "0|4|
S3Sb0R1S37A2S77S2S2S14S8S2S13S13A2A1M0A2M1S2S2fS13A2M2A2S1G1G2S1S14G0S3fSaR2A1M3A1S32G3A1A4S1S2fS13S35G3A1S34A4A4S3eA3F_;Fi;").
Proof using .
  intros i Hi. unfold cutsE. right. apply in_or_app. left.
  apply (in_map (fun j => (L_ j, tvL j, (rL j, z0))) (seq 1 NV) (S i)). apply in_seq. lia.
Qed.

Lemma T_in_cutsE : ltac2:(tb__ "0|5|
S3S77S3R1S33A3S77S2S2S14S8S2S13S13A2M0A1M1A2M2S2S2fS13A2M3A2S1G2G3S1S14G1S94S36R2A1M4S3cR2G4A2S40R2G4A2SacVECb;A1A4S92G0U0S0G0S3dR2A1S32SaR2A1A1A3A3A4S1S2fS13S83S35R2A1Z3A2S34A4A4S3eA3F_;Fi;").
Proof using .
  intros i Hin. unfold cutsE. right. apply in_or_app. right.
  exact (in_map (fun j => (T_after (E_ j) (s_of j (E_ j)) (R_of j (E_ j)) (L_free ECb), remove_nth 0 (tvE j :: tvL (S j)), (rL j - 3, z0))) lives i Hin).
Qed.

Lemma in_cutsD : ltac2:(tb__ "0|3|
S14S8S2S13S13A2A1M0S2S2fS13A2M1S77S2S2S14G0A2M2G1A2S1G2G1S1S14G0R3R2A4R1A4S3eA3S77G2S1S14G0R4R3A4S5aA3F_;Frv;Ftv;FT;").
Proof using . intros T tv rv H. exact (in_map (@edrop) cutsE (T, tv, rv) H). Qed.

Lemma exitsD_eq : ltac2:(tb__ "0|4|
S73S8S2S14S8S2S13S13A2M0A1M1A2M2A1S5bSbG2S7fS3G2S3S1S14G1S38R1A1S32R1A1M3A4Li;S33A4SbG2S7fS3G2S3S1S14G1S3aR1A1G3A4Li;S33A4S0G2S1S14G1S43S6G0A1A4S6G2A1A3A3A3A3").
Proof using . unfold exitsD. rewrite exitsE_eq, !map_app, !map_map. reflexivity. Qed.

Definition P0_bd : valuation -> Prop := fun _ => True.

Section Sum.
Variable ok : world -> Prop.
Variable Kc : ltac2:(tb__ "0|0|
S8Sd0A1ScfOF_;F_;").
Variable FB : list (Z * Z).
Variable rho0 : valuation.
Hypothesis ML : malloc_laws segs Cb.

Definition Posts_bd : list (sstate * jpost) := ltac2:(tb__ "0|1|
S0S2S14Sc4A2M0S1S14Sc4S43S9bVsegs;VCb;VKc;S42VFB;S6S2S13S13A2A1A6A4S6G0A1A3").

Let nI : ltac2:(tb__ "0|0|
S2S14S8S2S13S13A2A1A2Sc0Fn;") := ltac2:(tb__ "0|0|
Sa0Vsegs;VCb;S31VKc;Vrho0;S42VFB;A7").
Let eI : ltac2:(tb__ "0|0|
S93SbfFn;") := ltac2:(tb__ "0|0|
S9dVsegs;VCb;S31VKc;Vrho0;S42VFB;A7").
Let JGv (tv : list (sv * sv)) : jpred := ltac2:(tb__ "0|0|
S9aVsegs;VCb;S31VKc;Vrho0;S42VFB;Vtv;A8").
Let Q : assn := ltac2:(tb__ "0|0|
Sc3Vsegs;S31Vrho0;Sc5A4").
Let QX : assn := ltac2:(tb__ "0|0|
S8dS75Sc2Vsegs;S7fS2S14S8S2S13S13A2A1A2Sc0VnI;S5aA4R1A3VQ;R1A1A2Lw;").

Let QE (bound : Z) : assn := ltac2:(tb__ "0|0|
S8dS75Sc1Vsegs;S7fS93SbfVeI;S3eA4Vbound;R1A4VQ;R1A1A2Lw;").

Lemma reenterD : ltac2:(tb__ "0|3|
S14S8S2S13S13A2A1M0S2S2fS13A2M1S1aS77S2S2S14G0A2M2G1A2S1G2G1S1S14G0R4R3A4R2A4S3eA3S8cVsegs;Vok;S82Vsegs;VJGv;R4A1R5R2A4VQX;A4F_;Frho;Frv;Ftv;FT;").
Proof using Q nI.
  intros T tv rv rho H. apply (reenter_cutG segs ok (map nI cutsD) T (JGv tv) Q rho).
  exact (in_map nI cutsD (T, tv) (in_cutsD T tv rv H)).
Qed.
Lemma ereenterD : ltac2:(tb__ "0|3|
S14S8S2S13S13A2A1M0S2fS1aS93S1aS77S2S2S14G0A2M1S2S2fS13A2M2A2S1G1G2S1S14G0R6R5A4S1S2fS13R4S34A4A4S3eA3S86Z0R5A2S86S84R6Z1A2S9cR4A1A2S8bVsegs;S82Vsegs;VJGv;R8A1R9R6A4VQE;S91R5R4A2A1A3F_;F_;F_;FrhoX;FX;Frho;FrT;Ftv;FT;").
Proof using Q eI.
  intros T tv rT rho X rhoX H H0 Hr. exact (ereenter_rank segs Cb NP Kc rho0 P0_bd FB cutsE T tv rT z0 Q X rhoX rho H H0 Hr).
Qed.

Lemma K_step : ltac2:(tb__ "0|1|
S3S77S3R1S33A3S1aS8dS82Vsegs;VJGv;S32R4A1A1S3aR4A1R2R1A5S76S1aS1aS82Vsegs;VJGv;S32SaR6A1M0A1A1S3fG0A1R1R3A5Lr;A2F_;Fw;Frho;F_;Fi;").
Proof using FB Kc ML bd_chk_ok rho0.
  intros i Hin rho w Hw. destruct (lives_spec i Hin) as [Hi Hl]. destruct (chk_at i Hin) as (_ & _ & HK).
  rewrite (chkK_unfold i) in HK.
  destruct (apply_xforms (K_ i) [XSelect (seq 0 (length (ss_objs (K_ i))))]) as [X1|] eqn:HX; [|discriminate].
  cbv zeta in HK.
  apply andb_prop in HK as [HK Htse]. apply andb_prop in HK as [HK Hnb1]. apply andb_prop in HK as [HK Hnp1].
  apply andb_prop in HK as [HK Hid]. apply andb_prop in HK as [HK Hent]. apply andb_prop in HK as [HK Hnb].
  apply andb_prop in HK as [HK Hnp]. apply andb_prop in HK as [HK Hz]. apply andb_prop in HK as [HK Hhi].
  apply andb_prop in HK as [HK Hlo]. apply andb_prop in HK as [Hlen Hb].
  set (os := ss_objs X1) in *. set (o := last os O_Db) in *. set (K1 := set_objs X1 (removelast os)) in *.
  assert (Hos : ss_objs X1 = removelast os ++ [o]).
  { subst o. unfold os. apply app_removelast_last. intros E0. unfold os in Hlen. rewrite E0 in Hlen. discriminate. }
  rewrite (tvL_cons i Hi Hl) in Hw.
  destruct (JG_drop_null_vec segs Cb NP Kc rho0 P0_bd FB ML (tvE i :: tvL (S i)) 0%nat (tvE i) (K_ i) X1 _ _ o rho w
              HX Hos (@eq_refl _ (Some (tvE i))) Hb Hlo Hhi Hz Hnp Hnb Hw) as [rho1 Hw1].
  exists (rho_sub rho1 (infer_sub NP K1 (L_ (S i)))).
  exact (SPJ_entails_JG segs Cb NP Kc rho0 P0_bd FB ML K1 (L_ (S i)) _ _ (tvL (S i)) rho1 w Hent Hid Hnp1 Hnb1 Htse Hw1).
Qed.

Lemma E_prems : ltac2:(tb__ "0|a|
S3S77S3R1S33A3S74S73ScS8S16A1M0A1Sa7S36R2A1M1SadVECb;A1M2S3cR2G1A2M3A3SfG0S40R2G1A2M4A2A3S74S73S4S95VCb;S31G1G2G3G4S0S14SacVECb;A1S6S14A1A3A7S7A3S74S73S4Sa1S31S21G1A1M5A2S7A3S74S73S4S8fG5S0S2S13S13A2S3dR2A1M6S32SaR2A1A1A3M7A2S7A3S74S73S4S1bSdS13S13G6A3M8Sa9G3PcA2A2S7A3S74S73S4S1bSeS13S13G6A3Sa9G3PdA2A2S7A3S74S73S4S78S18S22S25S1eSa3G8S15Z0A1A3A1A1S23G1A1M9A3S7A3S73S4S97G9G7SfS3U0A2S16S9L_;G4A5S7A3A2A2A2A2A2A2A2F_;Fi;").
Proof using bd_chk_ok.
  intros i Hin. destruct (chk_at i Hin) as (_ & HE & _). rewrite (chkE_unfold i) in HE.
  apply andb_prop in HE as [HE Hrc]. apply andb_prop in HE as [HE Hnz]. apply andb_prop in HE as [HE H13].
  apply andb_prop in HE as [HE H12]. apply andb_prop in HE as [HE Hnb]. apply andb_prop in HE as [HE Hnp].
  apply andb_prop in HE as [Hsome Hcc]. apply (R_of_spec i (E_ i)) in Hsome. repeat (split; [assumption|]). assumption.
Qed.

Section Safety.
Hypothesis HS : ltac2:(tb__ "0|0|
SafVsegs;Vok;VKc;A3").
Hypothesis MC : ltac2:(tb__ "0|0|
S9eVsegs;VCb;VECb;A3").

Lemma X_P : ltac2:(tb__ "0|0|
S1aS8cVsegs;Vok;S82Vsegs;VJGv;S6S2S13S13A2A1A1S43R1A4VQX;A4Frho;").
Proof using ECb Q nI. intros rho. apply (exit_postG segs Cb NP Kc P0_bd FB ok rho0 [] Posts_bd P_bd). left. reflexivity. Qed.

Lemma X_K : ltac2:(tb__ "0|0|
S3S77S3R1S33A3S1aS8cVsegs;Vok;S82Vsegs;VJGv;S32R3A1A1S3aR3A1R1A4VQX;A4Frho;F_;Fi;").
Proof using ML Q bd_chk_ok nI.
  intros i Hin rho. destruct (lives_spec i Hin) as [Hi Hl].
  eapply (triple_conseq (P := fun w => exists r, SPJ segs (JGv (tvL (S i))) (L_ (S i)) r w));
    [ exact (K_step i Hin rho) | intros w Hw; exact Hw
    | apply triple_ex; intros r; exact (reenterD (L_ (S i)) (tvL (S i)) _ r (L_in_cutsE i Hi)) ].
Qed.

Lemma X_E : ltac2:(tb__ "0|0|
S3S77S3R1S33A3S1aS8eS8cVsegs;Vok;S82Vsegs;VJGv;S32R4A1A1S36R4A1R2A4S8dS75R2R1A1VQX;R1A1A2Lw;A4FQC;Frho;F_;Fi;").
Proof using HS MC ML Q bd_chk_ok nI.
  intros i Hin rho QC. destruct (lives_spec i Hin) as [Hi Hl].
  destruct (E_prems i Hin) as (Hsome & Hcc & Hnp & Hnb & H12 & H13 & Hnz & Hrc).
  eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw |].
  rewrite (tvL_cons i Hi Hl).
  apply (free_site_auto segs Cb ECb NP Kc rho0 P0_bd FB ML ok (E_ i) (s_of i (E_ i)) (R_of i (E_ i)) rho
           (tvE i :: tvL (S i)) 0%nat (tvE i) QX HS MC Hsome Hcc Hnp Hnb (@eq_refl _ (Some (tvE i))) H12 H13 Hnz Hrc).
  intros rho'. exact (reenterD _ _ _ rho' (T_in_cutsE i Hin)).
Qed.

Lemma X_C : ltac2:(tb__ "0|0|
S3S77S3R1S33A3S1aS8cVsegs;Vok;S82Vsegs;VJGv;S32R3A1A1S38R3A1R1A4VQX;A4Frho;F_;Fi;").
Proof using HS MC ML Q bd_chk_ok nI.
  intros i Hin rho. destruct (chk_at i Hin) as ([HC _] & _ & _).
  apply (cfg_sound_JG segs Cb NP Kc rho0 P0_bd FB ML FUEL_bd cutpcs_bd NP [(C_ i, tvL i)] [(E_ i, tvL i)] ok QX (proj1 HS) HC).
  - intros X tvX r [H|[]]. injection H as <- <-. apply X_E. exact Hin.
  - left. reflexivity.
Qed.

Lemma exits_ok : ltac2:(tb__ "0|1|
S14S8S2S13S13A2A1M0S1aS77S2S14G0A2S1S14G0R3R2A4S5bA3S8cVsegs;Vok;S82Vsegs;VJGv;R3A1R4R2A4VQX;A4F_;Frho;FtvX;FX;").
Proof using HS MC ML Q bd_chk_ok nI.
  intros X tvX rho Hin. rewrite exitsD_eq in Hin.
  apply in_app_or in Hin as [Hin|Hin]; [|apply in_app_or in Hin as [Hin|Hin]].
  - apply in_map_iff in Hin as (i & Heq & Hi). injection Heq as <- <-. apply X_C. exact Hi.
  - apply in_map_iff in Hin as (i & Heq & Hi). injection Heq as <- <-. apply X_K. exact Hi.
  - destruct Hin as [Heq|[]]. injection Heq as <- <-. apply X_P.
Qed.

Theorem builder_dispose_sum : ltac2:(tb__ "0|0|
S8cVsegs;Vok;S82Vsegs;S98Vsegs;VCb;VKc;S42VFB;S32U0A1A6S47Vrho0;A4Sc3Vsegs;S31Vrho0;Sc5A4A4").
Proof using HS MC ML QX bd_chk_ok ejcert_ok.
  eapply triple_conseq; [ | intros w Hw; exact Hw | ].
  2: { apply (cfg_sound_JG segs Cb NP Kc rho0 P0_bd FB ML FUEL_bd cutpcs_bd NP cutsD exitsD ok Q (proj1 HS)
                (ejcert_jcert segs NP _ _ _ _ _ ejcert_ok) exits_ok Pre_bd (tvL 0)).
       left. reflexivity. }
  intros w Hw. apply JG_pre_intro. exact Hw.
Qed.
End Safety.

Section Existence.
Hypothesis Hvi : vm_insensitive Kc.
Hypothesis MCX : ltac2:(tb__ "0|0|
S9fVsegs;VCb;VECb;A3").

Lemma X_P_ex : ltac2:(tb__ "0|0|
S1aS2fS8bVsegs;S82Vsegs;VJGv;S6S2S13S13A2A1A1S43R2A4VQE;R1A1A3Fb;Frho;").
Proof using ECb Q eI. intros rho b. apply (eexit_postG segs Cb NP Kc P0_bd FB rho0 [] Posts_bd P_bd). left. reflexivity. Qed.

Lemma rL_S : ltac2:(tb__ "0|0|
S3S73S2fS35SaR1A1A1S83S35R1A1ZaA2A3Fi;").
Proof using . intros i. unfold rL. rewrite Nat2Z.inj_succ. lia. Qed.
Lemma rL_pos : ltac2:(tb__ "0|0|
S3Sb0R1S37A2S86ZfS35SaR2A1A1A2F_;Fi;").
Proof using . intros i Hi. unfold rL, NV in *. rewrite Nat2Z.inj_succ. lia. Qed.

Lemma X_K_ex : ltac2:(tb__ "0|3|
S3S77S3R1S33A3S1aS8bVsegs;S82Vsegs;VJGv;S32R3A1M0A1S3aR3A1M1R1A4VQE;S91S1S2S14S8S2S13S13A2A1M2A2S2S2fS13A2S1S14G2G1G0A4S1S2fS13S83S35R3A1Z1A2S34A4A4R1A2A1A3Frho;F_;Fi;").
Proof using ML Q bd_chk_ok eI.
  intros i Hin rho. destruct (lives_spec i Hin) as [Hi Hl].
  eapply (@etriple_conseq segs (fun w => exists r, SPJ segs (JGv (tvL (S i))) (L_ (S i)) r w));
    [ exact (K_step i Hin rho) | intros w Hw; exact Hw | ].
  apply etriple_ex. intros r. apply (ereenterD (L_ (S i)) (tvL (S i)) (rL (S i)) r _ rho (L_in_cutsE i Hi)).
  - pose proof (rL_pos i Hi). lia.
  - unfold ed_rank. cbn [fst snd]. rewrite rL_S. lia.
Qed.

Lemma X_E_ex : ltac2:(tb__ "0|0|
S3S77S3R1S33A3S1aS1aS8eS8bVsegs;S82Vsegs;VJGv;S32R5A1A1S36R5A1R3A4S8dS75R2R1A1VQE;S91S61R6A1R3A2R1A2A2Lw;A3FQC;FrhoC;Frho;F_;Fi;").
Proof using Hvi MCX ML Q bd_chk_ok eI.
  intros i Hin rho rhoC QC. destruct (lives_spec i Hin) as [Hi Hl].
  destruct (E_prems i Hin) as (Hsome & Hcc & Hnp & Hnb & H12 & H13 & Hnz & Hrc).
  eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw |].
  rewrite (tvL_cons i Hi Hl).
  apply (free_site_auto_ex segs Cb ECb NP Kc rho0 P0_bd FB ML (E_ i) (s_of i (E_ i)) (R_of i (E_ i)) rho
           (tvE i :: tvL (S i)) 0%nat (tvE i) (QE (emeas (Cnode i) rhoC)) Hvi MCX Hsome Hcc Hnp Hnb (@eq_refl _ (Some (tvE i))) H12 H13 Hnz Hrc).
  intros rho'. apply (ereenterD _ _ _ rho' (Cnode i) rhoC (T_in_cutsE i Hin)).
  - pose proof (rL_pos i Hi). rewrite rL_S in *. lia.
  - unfold Cnode, ed_rank. cbn [fst snd]. lia.
Qed.

Lemma X_C_ex : ltac2:(tb__ "0|3|
S3S77S3R1S33A3S1aS8bVsegs;S82Vsegs;VJGv;S32R3A1M0A1S38R3A1M1R1A4VQE;S91S1S2S14S8S2S13S13A2A1M2A2S2S2fS13A2S1S14G2G1G0A4S1S2fS13S83S35R3A1Z1A2S34A4A4R1A2A1A3Frho;F_;Fi;").
Proof using Hvi MCX ML Q bd_chk_ok eI.
  intros i Hin rho. destruct (chk_at i Hin) as ([_ HC] & _ & _).
  apply (cfg_complete_JG segs Cb NP Kc rho0 P0_bd FB ML FUEL_bd cutpcs_bd NP _ _ (QE (emeas (Cnode i) rho)) HC) with (rvT := (rL i - 1, z0)).
  - intros X tvX rvX r [H|[]]. injection H as <- <- <-. apply X_E_ex. exact Hin.
  - left. reflexivity.
Qed.

Lemma exits_ok_ex : ltac2:(tb__ "0|3|
S14S8S2S13S13A2A1M0S2S2fS13A2M1S1aS77S2S2S14G0A2M2G1A2S1G2G1S1S14G0R4R3A4R2A4S4bA3S8bVsegs;S82Vsegs;VJGv;R4A1R5R2A4VQE;S91S1G2G1S1S14G0R5R4A4R3A4R2A2A1A3F_;Frho;FrvX;FtvX;FX;").
Proof using Hvi MCX ML Q bd_chk_ok eI.
  intros X tvX rvX rho Hin. rewrite exitsE_eq in Hin.
  apply in_app_or in Hin as [Hin|Hin]; [|apply in_app_or in Hin as [Hin|Hin]].
  - apply in_map_iff in Hin as (i & Heq & Hi). injection Heq as <- <- <-. apply X_C_ex. exact Hi.
  - apply in_map_iff in Hin as (i & Heq & Hi). injection Heq as <- <- <-. apply X_K_ex. exact Hi.
  - destruct Hin as [Heq|[]]. injection Heq as <- <- <-. apply X_P_ex.
Qed.

Theorem builder_dispose_sum_ex : ltac2:(tb__ "0|0|
S8bVsegs;S82Vsegs;S98Vsegs;VCb;VKc;S42VFB;S32U0A1A6S47Vrho0;A4Sc3Vsegs;S31Vrho0;Sc5A4A3").
Proof using Hvi MCX ML QE bd_chk_ok ejcert_ok.
  eapply etriple_conseq; [ | intros w Hw; exact Hw | ].
  2: { apply (cfg_complete_JG segs Cb NP Kc rho0 P0_bd FB ML FUEL_bd cutpcs_bd NP cutsE exitsE Q ejcert_ok exits_ok_ex Pre_bd (tvL 0) (rL 0, z0)).
       left. reflexivity. }
  intros w Hw. apply JG_pre_intro. exact Hw.
Qed.
End Existence.
End Sum.
End BuilderDispose.
