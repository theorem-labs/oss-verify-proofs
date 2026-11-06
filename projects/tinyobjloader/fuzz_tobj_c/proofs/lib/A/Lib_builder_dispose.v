(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "pair"; "nat"; "bool"; "prod"; "andb"; "nil"; "false"; "true"; "app"; "S"; "option"; "None"; "fst"; "list"; "snd"; "orb"; "Some"; "length"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "N"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SLit"; "cell"; "sprop"; "sobj"; "SPUle"; "SVar"; "sv_eqb"; "DUnknown"; "mkObj"; "FcsrFrm0"; "SPBranch"; "mkSS"; "ss_facts"; "SAlu"; "ss_next"; "SPAlign"; "SPNot"; "ob_base"; "ob_hi"; "ob_lo"; "sprop_eqb"; "SMd"; "ss_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_X"; "entailsA"; "ax_setS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builder_dispose"; "NP"; "c8"; "vB"; "vAl"; "NV"; "bdK"; "nlive"; "z0"; "ndL"; "rL"; "tvL"; "bd_facts"; "objs_at"; "vDp"; "voff"; "E_"; "L_"; "M_"; "NXC"; "Pre_ms"; "lives"; "s_of"; "spm"; "tvE"; "vd"; "FUEL_bd"; "F_cells"; "Pre_bd"; "R_of"; "X_bd"; "cutpcs_bd"; "in_regs"; "s_ms"; "vsz"; "C_"; "Cnode"; "L_ms"; "N_"; "Nd_"; "bd_vecs"; "bofs"; "didx"; "fr_obj"; "fr_xr"; "leaf_at"; "lit_in"; "live"; "live_from"; "pidx"; "raM"; "vUD"; "vel"; "vk"; "C_S"; "Enode"; "L_S"; "Lnode"; "M_S"; "Mnode"; "Nnode"; "O_D"; "O_F"; "O_al"; "O_dat"; "O_palloc"; "O_piece"; "P_bd"; "Tnode"; "bd_chk_live"; "chkC"; "chkE"; "chkE'"; "chkM"; "chkN"; "chkN'"; "cutsE"; "dats"; "exitsE"; "isSomeb"; "ndP"; "nobj"; "optR"; "pcJ"; "perm_back"; "piece_cells"; "pieces"; "sL"; "sN"; "src_"; "tvT"; "two47"; "xf_back"; "xf_ms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "ndesc"; "edescA"; "nd_below"; "ND"; "ANone"; "NDA"; "ejcertA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "AE_A"; "UStopLe"; "Pre_free"; "ulink"; "L_free"; "@Corelib.Lists.ListDef"; "map"; "seq"; "nth"; "firstn"; "skipn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "apply_axforms"; "AXMerge"; "AXRebase"; "AXSelect"; "AXSplit"; "AXUnbase"; "drop_obj_at"; "@Stdlib.ZArith.BinInt.Z"; "add"; "sub"; "leb"; "opp"; "mul"; "of_nat"; "pow"; "@Corelib.Init.Nat"; "add"; "sub"; "mul"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builder_dispose.BDAddr"; "FR"; "memset_pc"; "bd_ret"; "bd_entry"; "bd_jalrs"; "memset_ret"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "pre_fregs"; "setregs"; "cut_regs"; "post_regs"; "pre_regs"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_EQ"; "BC_GE"; "M_MUL"; "aluop"; "mulop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@Stdlib.Lists.List"; "forallb"; "existsb"; "filter"; "nth_error"; "rev"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "of_nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "mkA"; "segs"; "A_globals"; "SHB"; "leavesA_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "entails_frA"; "call_checkPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "remove_nth"; "tv_sub_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM"; "T_afterA"; "call_checkTA"; "robjs_checkA"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builder_dispose.RA.ReallocAddr"; "free_pc"; "thunk_free";
"thunk_alloc"; "thunk_calloc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "KU"; "bd_below"; "bd_subst"; "bitem"; "bud_le"; "BIc"; "bd_wpos"; "bud_pay"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "IMG_HI"; "@Stdlib.Arith.PeanoNat.Nat"; "ltb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymSummary SymObj ExampleMemcpy Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CFGA GlueA SummaryA SummaryA2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue TobjJV ObjXform ObjUnbase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA CfgGenTA SummaryA3 TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h0.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e9.
Module RA. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.Lib_realloc. End RA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import RA.ReallocAddr.
Definition c8 := RA.c8. Definition spm := RA.spm. Definition vUD := RA.vUD. Definition two47 := RA.two47.

Module BDAddr.
  Definition bd_entry : Z := 0x90ef0.
  Definition bd_ret : Z := 0x92be8.

  Definition bd_jalrs : list Z := ltac2:(tb__ "0|0|
S0S13Z91004S0S13Z910ecS0S13Z911d4S0S13Z912bcS0S13Z913a4S0S13Z9148cS0S13Z91574S0S13Z9165cS0S13Z91744S0S13Z9182cS0S13Z91914S0S13Z919fcS0S13Z91ae4S0S13Z91bccS0S13Z91cb4S0S13Z91d98S0S13Z91e7cS0S13Z91f60S0S13Z9203cS0S13Z92118S0S13Z921f0S0S13Z922c8S0S13Z9239cS0S13Z9246cS0S13Z9253cS0S13Z9260cS0S13Z926dcS0S13Z927acS0S13Z9287cS0S13Z9294cS0S13Z92a1cS0S13Z92aecS0S13Z92bbcS6S13A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
  Definition memset_pc : Z := 0x5cce8.
  Definition memset_ret : Z := 0x5cda8.
  Definition FR : Z := 48.
End BDAddr.
Import BDAddr.

Definition NV : nat := 33%nat.
Definition bd_vecs : list (Z * Z) := ltac2:(tb__ "0|4|
S0S4S13S13A2M0S1S13S13Z78Z4M1A4S0G0S1S13S13Z98G1A4S0G0S1S13S13Zb8G1A4S0G0S1S13S13Zd8G1A4S0G0S1S13S13Zf8G1A4S0G0S1S13S13Z118G1A4S0G0S1S13S13Z140Z490A4S0G0S1S13S13Z160Z8A4S0G0S1S13S13Z180G1A4S0G0S1S13S13Z1a0Z18A4S0G0S1S13S13Z1c0Z80M2A4S0G0S1S13S13Z1f0ZcM3A4S0G0S1S13S13Z210G1A4S0G0S1S13S13Z230G1A4S0G0S1S13S13Z250G1A4S0G0S1S13S13Z270G3A4S0G0S1S13S13Z290G1A4S0G0S1S13S13Z2b0G3A4S0G0S1S13S13Z2d0G3A4S0G0S1S13S13Z2f0G1A4S0G0S1S13S13Z310G1A4S0G0S1S13S13Z330Z1A4S0G0S1S13S13Z350G1A4S0G0S1S13S13Z3a8G1A4S0G0S1S13S13Z3c8G3A4S0G0S1S13S13Z3e8G1A4S0G0S1S13S13Z408G1A4S0G0S1S13S13Z428G3A4S0G0S1S13S13Z448G3A4S0G0S1S13S13Z468G3A4S0G0S1S13S13Z488Z38A4S0G0S1S13S13Z4a8Z30A4S0G0S1S13S13Z4c8G2A4S6G0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition bd_live : list bool := ltac2:(tb__ "0|0|
S0S3S8S0S3S8S0S3S8S0S3S8S0S3S8S0S3S8S0S3S7S0S3S7S0S3S7S0S3S7S0S3S8S0S3S8S0S3S8S0S3S8S0S3S8S0S3S8S0S3S8S0S3S8S0S3S8S0S3S8S0S3S8S0S3S8S0S3S7S0S3S7S0S3S7S0S3S7S0S3S7S0S3S7S0S3S7S0S3S7S0S3S7S0S3S7S0S3S7S6S3A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition live (j : nat) : bool := nth j bd_live false.
Definition voff (j : nat) : Z := ltac2:(tb__ "0|1|
SdS13S13S9eS4S13S13A2Vj;S5aS1S13S13Z0M0G0A4A4A3").
Definition vel (j : nat) : Z := ltac2:(tb__ "0|1|
SfS13S13S9eS4S13S13A2Vj;S5aS1S13S13Z0M0G0A4A4A3").
Definition pcJ (j : nat) : Z := nth j bd_jalrs 0.
Definition pcM (j : nat) : Z := pcJ j + 16.
Definition raM (j : nat) : Z := pcJ j + 20.

Definition NP : positive := 200%positive.
Definition NXC : positive := 240%positive.
Definition vB : sv := SVar 12.
Definition vAl : sv := SVar 16.
Definition vDp : sv := SVar 19.
Definition vd (j : nat) : sv := ltac2:(tb__ "0|0|
S1cScbSb0U64Sb2U2Vj;A2A2A1A1").
Definition vk (j : nat) : sv := ltac2:(tb__ "0|0|
S1cScbSb0U65Sb2U2Vj;A2A2A1A1").
Definition vsz (j : nat) : sv := ltac2:(tb__ "0|0|
S2cSc1S17S66Vj;A1A1S67Vj;A1A3").
Definition tvE (j : nat) : sv * sv := ltac2:(tb__ "0|0|
S1S16S16S4bVj;A1S54Vj;A1A4").
Definition bofs (k : Z) : sv := ltac2:(tb__ "0|0|
S24SbeS35S17Vk;A1A3").

Definition bd_facts : list sprop := ltac2:(tb__ "0|8|
S0S19S26PaM0Z4A2S0S19S1bS1cG0A1M1S17S8dA1M2A2S0S19S1bS1cP1eA1M3S24SbeS49Sb3A1M4S40A3A2S0S19S1bG3S49Sa9Sb3Z1000A2A1A2S0S19S1bG3G4A2S0S19S1bG3G1A2S0S19S21Sc0S17N1000A1S40A3S0S19S21Sc0S40S17SacSafZ2Z26A2A1A1A3S0S19S26PcZ3M5A2S0S19S1bS17Se7A1M6S35A2S0S19S1bS24SbeS35S17Z518A1A3G3A2S0S19S1bS35G2A2S0S19S26P10G5A2S0S19S1bG6S36A2S0S19S1bS24SbeS36S17Z30A1A3G3A2S0S19S1bS36G2A2S0S19S1bS17Z7fff7f800000A1M7G3A2S0S19S1bG3S17Z7fffff800000A1A2S0S19S1bG7G1A2S6S19A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").

Definition O_F (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S1fS1cPaA1S17SacSb3A1A1S17Z0A1Vcells;S1eA5").
Definition F_cells : list cell := ltac2:(tb__ "0|0|
S0S18S34N8S1cPbA1A2S0S18S34N10S1cP1cA1A2S0S18S34N18S1cP1dA1A2S0S18S34N20S1cP26A1A2S0S18S34N28S1cP27A1A2S6S18A1A3A3A3A3A3").
Definition O_D : sobj := ltac2:(tb__ "0|0|
S1fS49Sb3A1S40S17Z0A1S6S18A1S1eA5").
Definition O_palloc : sobj := ltac2:(tb__ "0|1|
S1fS35S17Z0M0A1S17Z8A1S0S18S34G0S36A2S6S18A1A3S1eA5").
Definition O_al : sobj := ltac2:(tb__ "0|2|
S1fS36S17Z0M0A1M1S17Z30A1S0S18S34G0S17SdbA1A2S0S18S34Z8S17SdcA1A2S0S18S34Z10G1A2S0S18S34Z18S17SdaA1A2S0S18S34Z20G1A2S0S18S34Z28S65A2S6S18A1A3A3A3A3A3A3S1eA5").

Definition piece_cells (zeroed : bool) (j : nat) : list cell := ltac2:(tb__ "0|6|
S3SeS18A1M0Lzeroed;Vzeroed;S3G0L_;M1S61Vj;A1M2S0S18S34Sa9S41Vj;A1M3Z18A2S17S66Vj;A1A1A2S6S18A1M4A3M5G4X3x2G1G2S0S18S34G3S4bVj;A1A2S0S18S34Sa9G3Z10A2S67Vj;A1A2G5A3A3S0S18S34G3S17Z0A1A2G4A3X3x2X3x2").
Definition O_piece (nz : nat) (j : nat) : sobj := ltac2:(tb__ "0|1|
S1fS35S17S41Vj;A1M0A1S17Sa9G0Z20A2A1S87Se8Vj;Vnz;A2Vj;A2S1eA5").
Definition pieces (nz : nat) : list sobj := ltac2:(tb__ "0|0|
S9cS2S1aS74Vnz;A1S9dU0S37A2A4").
Definition O_dat (j : nat) : sobj := ltac2:(tb__ "0|0|
S1fS4bVj;A1S17Z0A1S54Vj;A1S6S18A1S1eA5").

Definition live_from (i : nat) : list nat := ltac2:(tb__ "0|0|
Sc7S2S61S9dVi;Sb1S37Vi;A2A2A3").
Definition dats (i : nat) : list sobj := ltac2:(tb__ "0|0|
S9cS2S1aS72Sc9S2S62Vi;A1A2A4").
Definition tvL (i : nat) : list (sv * sv) := map tvE (live_from i).
Definition nlive (i : nat) : Z := Z.of_nat (length (live_from i)).

Definition objs_at (nz i : nat) (fcells : list cell) : list sobj := ltac2:(tb__ "0|0|
S9S1aS0S1aS6fS0S1aS70Vfcells;A1S0S1aS73S0S1aS71S6S1aA1A3A3A3A3S9S1aS88Vnz;A1S9S1aS7fVi;A1SceA3A3A3").
Definition X_bd : list (sv * sv) := ltac2:(tb__ "0|1|
S0S4S16S16A2M0S1S16S16S35S17Z518A1A4S0G0S1S16S16S36S17Z30A1A4S6G0A1A3A3").

Definition bdK (n : Z) : list bitem := ltac2:(tb__ "0|0|
S0Se2Se4Z0SdfVn;A3S6Se2A1A3").
Definition ndL (i : nat) : ndesc := ltac2:(tb__ "0|0|
S93S3dVi;A1S6S4S4S16S13A2S16A2A1S38S39Vi;A1A1A3").

Definition Pre_bd_S : sstate := ltac2:(tb__ "0|1|
S22Sb6SbdSb9S20ScS16A1S3fU0M0G0S6S18A1A3S3eS33S7A9").
Definition Pre_bd : axst := mkA Pre_bd_S X_bd.

Definition in_regs : list sv := ltac2:(tb__ "0|1|
SbaSbbS33A1S0S4S2S16A2M0S1S2S16U1S1cPe8A1A4S0G0S1S2S16U2S49Sb3A1A4S0G0S1S2S16U8S36A4S0G0S1S2S16U9S35A4S0G0S1S2S16U12S17ScfA1A4S0G0S1S2S16U13S1cPe9A1A4S6G0A1A3A3A3A3A3A3A2").

Definition L_S (i : nat) : sstate := ltac2:(tb__ "0|2|
S22Sb8SbaS52S0S4S2S16A2M0S1S2S16U1M1S17S64Sb1Vi;G1A2A1A1A4S6G0A1A3A2Sb9S20ScS16A1S3fVi;Vi;S4dA3S3eS45S7A9").
Definition L_ (i : nat) : axst := ltac2:(tb__ "0|0|
SccS6aVi;A1S50A2").
Definition src_ (i : nat) : axst := ltac2:(tb__ "0|0|
S2S2eLi;Vi;S4eS2S43Vi;A1Ln;X2x2").

Definition C_S (j : nat) : sstate := ltac2:(tb__ "0|2|
S22S85Vj;A1SbaS52S0S4S2S16A2M0S1S2S16UaS65A4S0G0S1S2S16UbS4bVj;A1M1A4S0G0S1S2S16UdS17SdaA1A4S0G0S1S2S16U13S5bS41Vj;A1A1A4S6G0A1A3A3A3A3A2Sb9S20ScS16A1S3fVj;Vj;S4dA3S0S19S27S21SbfG1S17Z0A1A3A1S3eA3S45S7A9").
Definition C_ (j : nat) : axst := ltac2:(tb__ "0|0|
SccS68Vj;A1S50A2").

Definition M_S (j : nat) : sstate := ltac2:(tb__ "0|1|
S22Sb4SbaS52S0S4S2S16A2M0S1S2S16U1S17S64Vj;A1A1A4S0G0S1S2S16UaS5bS41Vj;A1A1A4S0G0S1S2S16UbS17Z0A1A4S0G0S1S2S16UcS17Z18A1A4S6G0A1A3A3A3A3A2Sb9S20ScS16A1S3fVj;SaVj;A1S4dA3S3eS45S7A9").
Definition M_ (j : nat) : axst := ltac2:(tb__ "0|0|
SccS6cVj;A1S50A2").
Definition P_bd_S : sstate := ltac2:(tb__ "0|0|
S22Sb5SbcS33A1Sb9S20ScS16A1S3fS37S37S6S18A1A3S3eS45S7A9").
Definition P_bd : axst := mkA P_bd_S X_bd.

Definition FUEL_bd : nat := 300%nat.
Definition cutpcs_bd : list Z := ltac2:(tb__ "0|0|
S9S13S0S13Sd9S0S13Sb4S0S13Sb5S6S13A1A3A3A3Sb7A3").
Definition leaf_at (S : axst) (pc : Z) : axst := ltac2:(tb__ "0|0|
S9eS2eU0Sd0S4cS51VS;Vpc;A4S4eA4").
Definition optA (x : option axst) : axst := match x with Some s => s | None => Pre_bd end.
Definition optR (x : option (list sobj)) : list sobj := match x with Some r => r | None => [] end.

Definition E_ (j : nat) : axst := ltac2:(tb__ "0|0|
S5fS55Vj;A1Sd9A2").
Definition N_ (j : nat) : axst := ltac2:(tb__ "0|0|
S5fS8bVj;A1Sb4A2").

Definition s_of (j : nat) (E : axst) : wsub := ltac2:(tb__ "0|1|
S0S4S14S16A2M0S1S14S16PfS40A4S0G0S1S14S16PdS54Vj;A1A4Sc4PaS2fVE;A1S2fS99S97S6S9aA1S98A3A1A3A3A3").
Definition R_of (j : nat) (E : axst) : list sobj := ltac2:(tb__ "0|0|
S84Sd1VE;S99S97S6S9aA1S98A3S48Vj;VE;A2A3A1").

Definition T_ (j : nat) : axst := ltac2:(tb__ "0|2|
Sd5S99S97S6S9aA1M0S98A3S42Vj;A1M1S48Vj;G1A2S4fVj;G1A2S9bS97G0S98A3A5").
Definition tvT (j : nat) : list (sv * sv) := ltac2:(tb__ "0|1|
Sd3S4S16S16A2M0U0S0G0S4aVj;A1S3dSaVj;A1A1A3A3").
Definition ndT (j : nat) : ndesc := ltac2:(tb__ "0|0|
S95S8cVj;A1S6S4S4S16S13A2S16A2A1S38S39SaVj;A1A1A1S94A4").

Definition pidx (j : nat) : nat := (4 + j)%nat.
Definition xf_ms (j : nat) : list axform := ltac2:(tb__ "0|2|
S0Sa1Sa6S63Vj;A1M0S17Sa9S41Vj;A1M1Z18A2A1A2S0Sa1Sa7G0G1A2S6Sa1A1A3A3").
Definition Pre_ms : axst := Pre_memset memset_pc.
Definition L_ms : axst := L_memset memset_ret.
Definition s_ms (Mx : axst) : wsub := ltac2:(tb__ "0|1|
S0S4S14S16A2M0S1S14S16P35S35A4S0G0S1S14S16P36S17Z518A1A4Sc4PaS2fVMx;A1S2fS46A1A3A3A3").

Definition nobj (A : axst) : nat := length (ss_objs (ax_S A)).
Definition perm_back (j : nat) (n : nat) : list nat := ltac2:(tb__ "0|5|
S9dU4M0Sb1Vn;G0A2A2SeS2A1M1S9fS2Sb0U3M2Vj;A2M3R1A3G1Sa0S2G3R2A3G1S9S2S0S2U0S6S2A1M4A3S9S2R2S9S2S0S2U1G4A3S9S2R1S0S2U2S0S2G2G4A3A3A3A3A3A3Tpost;Tpre;Trest;").
Definition xf_back (j : nat) (n : nat) : list axform := ltac2:(tb__ "0|0|
S0Sa1Sa4U1A1S0Sa1Sa5S86Vj;Vn;A2A1S0Sa1Sa3S63Vj;A1A1S6Sa1A1A3A3A3").

Definition lives : list nat := live_from 0.
Definition rL (i : nat) : Z := ltac2:(tb__ "0|0|
Sa9SadZaSaaZ22SaeVi;A1A2A2Z8A2").
Definition z0 : sv := SLit 0.
Definition ndP : ndesc := ND [] [] [].
Definition Lnode (i : nat) : edescA := ltac2:(tb__ "0|0|
S1S4S2eS90A2S4S13S16A2S1S2eS90S43Vi;A1S3bVi;A1A4S1S13S16S3cVi;A1S3aA4A4").
Definition Tnode (j : nat) : edescA := ltac2:(tb__ "0|4|
S1S4S2eS90A2S4S13S16A2S1S2eS90Sd5S99S97S6S9aA1M0S98A3S42Vj;A1M1S48Vj;G1A2S4fVj;G1A2S9bS97G0S98A3A5S95Sd3S4S16S16A2M2U0S0G2S4aVj;A1S3dSaVj;A1M3A1A3A3S6S4S4S16S13A2S16A2A1S38S39G3A1A1S94A4A4S1S13S16SaaS3cVj;A1Z3A2S3aA4A4").
Definition Cnode (j : nat) : edescA := ltac2:(tb__ "0|0|
S1S4S2eS90A2S4S13S16A2S1S2eS90S55Vj;A1S3bVj;A1A4S1S13S16SaaS3cVj;A1Z1A2S3aA4A4").
Definition Enode (j : nat) : edescA := ltac2:(tb__ "0|0|
S1S4S2eS90A2S4S13S16A2S1S2eS90S42Vj;A1S3bVj;A1A4S1S13S16SaaS3cVj;A1Z2A2S3aA4A4").
Definition Nnode (j : nat) : edescA := ltac2:(tb__ "0|0|
S1S4S2eS90A2S4S13S16A2S1S2eS90S58Vj;A1S3bVj;A1A4S1S13S16SaaS3cVj;A1Z1A2S3aA4A4").
Definition Mnode (j : nat) : edescA := ltac2:(tb__ "0|0|
S1S4S2eS90A2S4S13S16A2S1S2eS90S44Vj;A1S3bSaVj;A1A1A4S1S13S16SaaS3cVj;A1Z5A2S3aA4A4").
Definition cutsE : list edescA := ltac2:(tb__ "0|3|
S0S4S4S2eS90A2M0S4S13S16A2M1A2S1G0G1S1S2eS90S4eS3bU0M2A1A4S1S13S16S3cG2A1S3aA4A4S9S91S9cS2S91S6bS9dU1S37A2A4S9cS2S91S76S47A4A3A3").
Definition exitsE : list edescA := ltac2:(tb__ "0|3|
S9S91S9cS2S91S56S47A4S9S91S9cS2S91S6eS47A4S9S91S9cS2S91S6dS9dU0S37A2A4S0S4S4S2eS90A2M0S4S13S16A2M1A2M2S1G0G1S1S2eS90S75S82A4S1S13S16Z0S3aA4A4S6G2A1A3A3A3A3").

Definition isSomeb {A} (o : option A) : bool := match o with Some _ => true | None => false end.

Definition lit_in (lo hi : sv) (n : Z) : bool := ltac2:(tb__ "0|6|
S16S3Llo;Vlo;S13S16S3Lhi;Vhi;S13S5S5SabZ0R2A2SabR2R1A2A2SabR1Vn;A2A2Lh;S14S7Li;M0Sc2S16S16S7Lb;La;M1Lop;M2G2Sc3G1Lop;M3G3S3S15S16S7La;Lw;Lsgn;M4S14S16S13S7Lk;Li;M5Ll0;X16x8Ll;G0G2G2G3G3G4S14G5Ll;X16x8").
Definition fr_obj (o : sobj) : bool := ltac2:(tb__ "0|3|
S10S5S1dS28Vo;A1M0S35A2S60S2aVo;A1M1S29Vo;A1M2Z518A3A2S5S1dG0S36A2S60G1G2Z30A3A2A2").
Definition fr_xr (r : sv * sv) : bool := ltac2:(tb__ "0|2|
S10S5S1dSdS16S16Vr;A3M0S35A2S1dSfS16S16Vr;A3M1S17Z518A1A2A2S5S1dG0S36A2S1dG1S17Z30A1A2A2A2").

Definition chkE' (j : nat) (E : axst) : bool := ltac2:(tb__ "0|f|
S5S5S5S5S5S5S5S5S5S5S5S81SeS1aA1Sd1VE;S99S97S6S9aA1M0S98A3M1S48Vj;VE;A2M2A3A2Sd2VE;G1G2S4fVj;VE;A2M3S0S2eS9bS97G0S98A3S6S2eA1A3A5A2Sd6S33G2A2A2ScaS33S25S2fVE;A1M4A1M5A2A2S92G5S93S0S4S16S16A2M6S4aVj;A1M7S3dSaVj;A1M8A1A3M9S6S4S4S16S13A2S16A2A1S38S39Vj;A1A1MaA3A2A2Se0G5S38S39G8A1A1MbA2A2Se6S23G4A1McS17Z0A1MdSdfGaGbA5A2S1dSdS16S16G7A3MeSddG2PcA2A2A2S1dSfS16S16G7A3SddG2PdA2A2A2Sc6S19S2bS27S21SbfGeGdA3A1A1GcA3A2Sd7GcG9S11S2U0A2S5dG3A5A2Sc5G6S5eS30VE;A1A3A2").
Definition chkE (j : nat) : bool := ltac2:(tb__ "0|0|
S7aVj;S42Vj;A1A2").

Definition didx (j : nat) : nat := ltac2:(tb__ "0|0|
Sb0Sb0U4S37A2S12S2S62SaVj;A1A1A2A2").
Definition Nd_ (j : nat) (N : axst) : axst := ltac2:(tb__ "0|0|
S32VN;Sa8S2fVN;A1S5cVj;A1A2A2").
Definition sN (j : nat) (N : axst) : wsub := ltac2:(tb__ "0|0|
Sc4S33S2fS59Vj;VN;A2A1S2fS44Vj;A1A1A3").
Definition chkN' (j : nat) (N : axst) : bool := ltac2:(tb__ "0|d|
SbS1aA1S3Lx;Sc8S1aS2dS2fVN;A1M0A1S5cVj;A1A3S1aS5S5S5S5S5S5S5S5S5S1dS28R1A1SdS16S16S4aVj;A1M1A3M2A2S1dS2aR1A1S17Z0A1M3A2A2S1dS29R1A1SfS16S16G1A3A2A2Sc6S19S2bS21SbfG2G3A3A1S23G0A1A3A2S31S59Vj;VN;A2M4S44Vj;A1S8aVj;VN;A2M5A3A2SdeG5S33A2A2ScaS33S25S2fG4A1M6A1M7A2A2S92G7S93Sd3S4S16S16A2M8U0S0G8G1S3dSaVj;A1M9A1MaA3A3MbS6S4S4S16S13A2S16A2A1S38S39Vj;A1A1McA3A2A2Sd4G5GbGaA3A2Se3S23G6A1Se1G5S38S39G9A1A1A2GcA3A2Lo;S7Xbx2").
Definition chkN (j : nat) : bool := ltac2:(tb__ "0|0|
S7dVj;S58Vj;A1A2").

Definition sL (j : nat) (T : axst) : wsub := ltac2:(tb__ "0|0|
Sc4S33S2fVT;A1S2fS43SaVj;A1A1A1A3").
Definition chkM (j : nat) : bool := ltac2:(tb__ "0|c|
SbS2eA1S3Lx;M0Sa2S44Vj;A1S8fVj;A1A2S2eSbSeS1aA1M1A1S3Lx;Sd1R1S46S53R1A1A3G1Sd5S46R2S53R2A1R1S57A5S2eS5S5S5S5S5S5S5S5Sd2R3S46S53R3A1M2R2S0S2eS57S6S2eA1A3A5Sd6S33G2A2A2ScaS33S25S2fR3A1M3A1M4A2A2S92G4S3bSaVj;A1M5A1M6A2A2Se0G4S38S39G5A1A1M7A2A2Se5G7A1A2Sd7S23G3A1S3dG5A1M8ScS2A1S5dR2A5A2Sc5S4S16S16A2S5eS30R3A1A3A2G0Sa2R1S8eVj;S83R1A1A2A2S2eS5S5S5S5S5S31R1S43G5A1S89Vj;R1A2M9A3SdeG9S33A2A2ScaS33S25S2fR1A1MaA1MbA2A2S92GbG6A2A2Sd4G9G8G8A3A2Se3S23GaA1Se1G9G7A2G7A3A2LT';S7Xbx2A2TT;LR;S7Xbx2LMx;S7Xbx2").

Definition chkC (j : nat) : bool := ltac2:(tb__ "0|1|
S96ScdS33S4cS51S33S0S91S56Vj;A1S6S91A1M0A3S0S91S69Vj;A1G0A3A7").

Definition bd_chk_live (j : nat) : bool := ltac2:(tb__ "0|0|
S5S78Vj;A1S5S79Vj;A1S7cVj;A1A2A2").

Definition bd_chk_stmt : Prop := ltac2:(tb__ "0|0|
Sd8S3S5Sc5S2S7bS9dU0S37A2A3Sc5S2S77S47A3A2S8A3").
Definition bd_ejcert_stmt : Prop := ltac2:(tb__ "0|0|
Sd8S3S96ScdS33S4cS51S33S7eS80A7S8A3").
