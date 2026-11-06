(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "pair"; "bool"; "prod"; "nil"; "nat"; "andb"; "false"; "true"; "app"; "S"; "None"; "fst"; "snd"; "list"; "option"; "orb"; "Some"; "length"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "N"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SLit"; "sprop"; "cell"; "SPUle"; "SVar"; "sobj"; "sv_eqb"; "DUnknown"; "SAlu"; "mkObj"; "SPBranch"; "FcsrFrm0"; "mkSS"; "SPAlign"; "ss_facts"; "SPNot"; "ob_base"; "ob_hi"; "ob_lo"; "sprop_eqb"; "ss_next"; "SMd"; "SPEq"; "ss_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builder_dispose"; "c8"; "vB"; "NP"; "vAl"; "bdK"; "nlive"; "z0"; "NV"; "rL"; "ndL"; "tvL"; "vDp"; "E_"; "L_"; "bd_facts"; "lives"; "objs_at"; "s_of"; "spm"; "tvE"; "vd"; "FUEL_bd"; "NXC"; "Pre_bd"; "R_of"; "cutpcs_bd"; "voff"; "vsz"; "C_"; "Cnode"; "F_cells"; "N_"; "Nd_"; "X_bd"; "bd_vecs"; "bofs"; "didx"; "in_regs"; "leaf_at"; "lit_in"; "live"; "live_from"; "pGb"; "pcL"; "vUD"; "vel"; "vk"; "C_S"; "Enode"; "FEb"; "L_S"; "Lnode"; "Nnode"; "O_D"; "O_F"; "O_al"; "O_dat"; "O_palloc"; "O_piece"; "P_bd"; "Tnode"; "bd_chk_live"; "chkC"; "chkE"; "chkE'"; "chkN"; "chkN'"; "cutsE"; "dats"; "exitsE"; "fr_obj"; "fr_xr"; "isSomeb"; "ndP"; "optR"; "pcJ"; "piece_cells"; "pieces"; "sN"; "shB"; "src_"; "tvT"; "two47"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_X"; "ax_setS"; "entailsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "ndesc"; "edescA"; "ND"; "ANone"; "NDA"; "ejcertA"; "nd_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "AE_A"; "UStopLe"; "Pre_free"; "ulink"; "L_free"; "@Stdlib.ZArith.BinInt.Z"; "add"; "sub"; "leb"; "opp"; "pow"; "div"; "mul"; "of_nat"; "@Corelib.Lists.ListDef"; "map"; "nth"; "seq"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_EQ"; "BC_GE"; "ALU_SLL"; "M_MUL"; "aluop"; "mulop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builder_dispose.BDAddr"; "FR"; "bd_ret"; "bd_entry"; "bd_jalrs"; "bd_starts"; "@Corelib.Init.Nat"; "add"; "mul"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "pre_fregs"; "setregs"; "cut_regs"; "post_regs"; "pre_regs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "remove_nth"; "tv_sub_eqb"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "SHB"; "mkA"; "segs"; "A_globals"; "leavesA_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builder_dispose.RA.ReallocAddr"; "free_pc"; "thunk_free"; "thunk_alloc"; "thunk_calloc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "entails_frA"; "call_checkPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "KU"; "bitem"; "BIc"; "bd_below"; "bd_subst"; "bud_le"; "bud_pay"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM"; "T_afterA"; "call_checkTA"; "robjs_checkA"; "@Stdlib.Lists.List"; "existsb"; "forallb"; "filter"; "nth_error"; "rev"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "of_nat";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "drop_obj_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "IMG_HI"; "@Stdlib.Arith.PeanoNat.Nat"; "ltb"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require Import BudA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import CfgGenTA SummaryA3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p1.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.TobjJAX.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ng.
Module RA. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ng.Lib_realloc. End RA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import RA.ReallocAddr.
Definition c8 := RA.c8. Definition spm := RA.spm. Definition vUD := RA.vUD. Definition two47 := RA.two47.

Module BDAddr.
  Definition bd_entry : Z := 0x91de8.
  Definition bd_ret : Z := 0x9428c.

  Definition bd_jalrs : list Z := ltac2:(tb__ "0|0|
S0S13Z91f18S0S13Z9203cS0S13Z92160S0S13Z92284S0S13Z923a8S0S13Z924ccS0S13Z925f0S0S13Z92714S0S13Z92838S0S13Z9295cS0S13Z92a80S0S13Z92ba4S0S13Z92cc8S0S13Z92decS0S13Z92f10S0S13Z93034S0S13Z93158S0S13Z9327cS0S13Z9339cS0S13Z934bcS0S13Z935dcS0S13Z936fcS0S13Z9380cS0S13Z9391cS0S13Z93a2cS0S13Z93b34S0S13Z93c3cS0S13Z93d40S0S13Z93e40S0S13Z93f3cS0S13Z94038S0S13Z94134S0S13Z94230S4S13A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").

  Definition bd_starts : list Z := ltac2:(tb__ "0|0|
S0S13Z91f60S0S13Z92084S0S13Z921a8S0S13Z922ccS0S13Z923f0S0S13Z92514S0S13Z92638S0S13Z9275cS0S13Z92880S0S13Z929a4S0S13Z92ac8S0S13Z92becS0S13Z92d10S0S13Z92e34S0S13Z92f58S0S13Z9307cS0S13Z931a0S0S13Z932c4S0S13Z933e4S0S13Z93504S0S13Z93624S0S13Z93738S0S13Z93848S0S13Z93958S0S13Z93a68S0S13Z93b70S0S13Z93c78S0S13Z93d7cS0S13Z93e7cS0S13Z93f78S0S13Z94074S0S13Z94170S0S13Z9426cS4S13A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
  Definition FR : Z := 64.
End BDAddr.
Import BDAddr.

Definition NV : nat := 33%nat.
Definition bd_vecs : list (Z * Z) := ltac2:(tb__ "0|4|
S0S3S13S13A2M0S1S13S13Z78Z4M1A4S0G0S1S13S13Z98G1A4S0G0S1S13S13Zb8G1A4S0G0S1S13S13Zd8G1A4S0G0S1S13S13Zf8G1A4S0G0S1S13S13Z118G1A4S0G0S1S13S13Z140Z490A4S0G0S1S13S13Z160Z8A4S0G0S1S13S13Z180G1A4S0G0S1S13S13Z1a0Z18A4S0G0S1S13S13Z1c0Z80M2A4S0G0S1S13S13Z1f0ZcM3A4S0G0S1S13S13Z210G1A4S0G0S1S13S13Z230G1A4S0G0S1S13S13Z250G1A4S0G0S1S13S13Z270G3A4S0G0S1S13S13Z290G1A4S0G0S1S13S13Z2b0G3A4S0G0S1S13S13Z2d0G3A4S0G0S1S13S13Z2f0G1A4S0G0S1S13S13Z310G1A4S0G0S1S13S13Z330Z1A4S0G0S1S13S13Z350G1A4S0G0S1S13S13Z3a8G1A4S0G0S1S13S13Z3c8G3A4S0G0S1S13S13Z3e8G1A4S0G0S1S13S13Z408G1A4S0G0S1S13S13Z428G3A4S0G0S1S13S13Z448G3A4S0G0S1S13S13Z468G3A4S0G0S1S13S13Z488Z38A4S0G0S1S13S13Z4a8Z30A4S0G0S1S13S13Z4c8G2A4S4G0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition bd_live : list bool := ltac2:(tb__ "0|0|
S0S2S8S0S2S8S0S2S8S0S2S8S0S2S8S0S2S8S0S2S7S0S2S7S0S2S7S0S2S7S0S2S8S0S2S8S0S2S8S0S2S8S0S2S8S0S2S8S0S2S8S0S2S8S0S2S8S0S2S8S0S2S8S0S2S8S0S2S7S0S2S7S0S2S7S0S2S7S0S2S7S0S2S7S0S2S7S0S2S7S0S2S7S0S2S7S0S2S7S4S2A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition live (j : nat) : bool := nth j bd_live false.
Definition voff (j : nat) : Z := ltac2:(tb__ "0|1|
ScS13S13S9cS3S13S13A2Vj;S51S1S13S13Z0M0G0A4A4A3").
Definition vel (j : nat) : Z := ltac2:(tb__ "0|1|
SdS13S13S9cS3S13S13A2Vj;S51S1S13S13Z0M0G0A4A4A3").
Definition pcJ (j : nat) : Z := nth j bd_jalrs 0.
Definition pcL (i : nat) : Z := nth (i - 1) bd_starts 0.

Definition NP : positive := 200%positive.
Definition NXC : positive := 240%positive.
Definition vB : sv := SVar 12.
Definition vAl : sv := SVar 16.
Definition vDp : sv := SVar 19.
Definition vd (j : nat) : sv := ltac2:(tb__ "0|0|
S1bSd3SaaU64SabU2Vj;A2A2A1A1").
Definition vk (j : nat) : sv := ltac2:(tb__ "0|0|
S1bSd3SaaU65SabU2Vj;A2A2A1A1").
Definition vsz (j : nat) : sv := ltac2:(tb__ "0|0|
S2cSa2S17S5cVj;A1A1S5dVj;A1A3").
Definition tvE (j : nat) : sv * sv := ltac2:(tb__ "0|0|
S1S16S16S43Vj;A1S4aVj;A1A4").
Definition bofs (k : Z) : sv := ltac2:(tb__ "0|0|
S1fS9eS30S17Vk;A1A3").

Definition bd_facts : list sprop := ltac2:(tb__ "0|8|
S0S18S24PaM0Z4A2S0S18S1aS1bG0A1M1S17S81A1M2A2S0S18S1aS1bP1eA1M3S1fS9eS41Sa5A1M4S3aA3A2S0S18S1aG3S41S93Sa5Z1000A2A1A2S0S18S1aG3G4A2S0S18S1aG3G1A2S0S18S21Sa0S17N1000A1S3aA3S0S18S21Sa0S3aS17S96S97Z2Z26A2A1A1A3S0S18S24PcZ3M5A2S0S18S1aS17Sd5A1M6S30A2S0S18S1aS1fS9eS30S17Z518A1A3G3A2S0S18S1aS30G2A2S0S18S24P10G5A2S0S18S1aG6S32A2S0S18S1aS1fS9eS32S17Z30A1A3G3A2S0S18S1aS32G2A2S0S18S1aS17Z7fff7f800000A1M7G3A2S0S18S1aG3S17Z7fffff800000A1A2S0S18S1aG7G1A2S4S18A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").

Definition O_F (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S20S1bPaA1S17S96Sa5A1A1S17Z0A1Vcells;S1eA5").
Definition F_cells : list cell := ltac2:(tb__ "0|0|
S0S19S2fN8S1bPbA1A2S0S19S2fN10S1bP1cA1A2S0S19S2fN18S1bP1dA1A2S0S19S2fN20S1bP26A1A2S0S19S2fN28S1bP27A1A2S0S19S2fN30S1bP28A1A2S0S19S2fN38S1bP29A1A2S4S19A1A3A3A3A3A3A3A3").
Definition O_D : sobj := ltac2:(tb__ "0|0|
S20S41Sa5A1S3aS17Z0A1S4S19A1S1eA5").
Definition O_palloc : sobj := ltac2:(tb__ "0|1|
S20S30S17Z0M0A1S17Z8A1S0S19S2fG0S32A2S4S19A1A3S1eA5").
Definition O_al : sobj := ltac2:(tb__ "0|2|
S20S32S17Z0M0A1M1S17Z30A1S0S19S2fG0S17SbcA1A2S0S19S2fZ8S17SbdA1A2S0S19S2fZ10G1A2S0S19S2fZ18S17SbbA1A2S0S19S2fZ20G1A2S0S19S2fZ28S5bA2S4S19A1A3A3A3A3A3A3S1eA5").

Definition piece_cells (zeroed : bool) (j : nat) : list cell := ltac2:(tb__ "0|6|
S2SeS19A1M0Lzeroed;Vzeroed;S2G0L_;M1S57Vj;A1M2S0S19S2fS93S49Vj;A1M3Z18A2S17S5cVj;A1A1A2S4S19A1M4A3M5G4X2x2G1G2S0S19S2fG3S43Vj;A1A2S0S19S2fS93G3Z10A2S5dVj;A1A2G5A3A3S0S19S2fG3S17Z0A1A2G4A3X2x2X2x2").
Definition O_piece (nz : nat) (j : nat) : sobj := ltac2:(tb__ "0|1|
S20S30S17S49Vj;A1M0A1S17S93G0Z20A2A1S7bSd6Vj;Vnz;A2Vj;A2S1eA5").
Definition pieces (nz : nat) : list sobj := ltac2:(tb__ "0|0|
S9bS5S1cS69Vnz;A1S9dU0S36A2A4").
Definition O_dat (j : nat) : sobj := ltac2:(tb__ "0|0|
S20S43Vj;A1S17Z0A1S4aVj;A1S4S19A1S1eA5").

Definition live_from (i : nat) : list nat := ltac2:(tb__ "0|0|
ScfS5S57S9dVi;SacS36Vi;A2A2A3").
Definition dats (i : nat) : list sobj := ltac2:(tb__ "0|0|
S9bS5S1cS67Sd1S5S58Vi;A1A2A4").
Definition tvL (i : nat) : list (sv * sv) := map tvE (live_from i).
Definition nlive (i : nat) : Z := Z.of_nat (length (live_from i)).

Definition objs_at (nz i : nat) (fcells : list cell) : list sobj := ltac2:(tb__ "0|0|
S9S1cS0S1cS64S0S1cS65Vfcells;A1S0S1cS68S0S1cS66S4S1cA1A3A3A3A3S9S1cS7cVnz;A1S9S1cS73Vi;A1Sb8A3A3A3").
Definition X_bd : list (sv * sv) := ltac2:(tb__ "0|1|
S0S3S16S16A2M0S1S16S16S30S17Z518A1A4S0G0S1S16S16S32S17Z30A1A4S4G0A1A3A3").

Definition bdK (n : Z) : list bitem := ltac2:(tb__ "0|0|
S0Sc4Sc5Z0Sc3Vn;A3S4Sc4A1A3").
Definition ndL (i : nat) : ndesc := ltac2:(tb__ "0|0|
S89S39Vi;A1S4S3S3S16S13A2S16A2A1S33S34Vi;A1A1A3").

Definition Pre_bd_S : sstate := ltac2:(tb__ "0|1|
S23Sa7Sb1SadS22SbS16A1S3fU0M0G0S4S19A1A3S3dS31S7A9").
Definition Pre_bd : axst := mkA Pre_bd_S X_bd.

Definition in_regs : list sv := ltac2:(tb__ "0|1|
SaeSafS31A1S0S3S5S16A2M0S1S5S16U1S1bPe8A1A4S0G0S1S5S16U2S41Sa5A1A4S0G0S1S5S16U8S32A4S0G0S1S5S16U9S30A4S0G0S1S5S16U12S1bPeaA1A4S0G0S1S5S16U13S1bPe9A1A4S0G0S1S5S16U14S17Sb5A1A4S0G0S1S5S16U15S1bPebA1A4S4G0A1A3A3A3A3A3A3A3A3A2").

Definition L_S (i : nat) : sstate := ltac2:(tb__ "0|0|
S23S5aVi;A1S54SadS22SbS16A1S3fVi;Vi;S4dA3S3dS45S7A9").
Definition L_ (i : nat) : axst := ltac2:(tb__ "0|0|
Sb6S61Vi;A1S50A2").
Definition src_ (i : nat) : axst := ltac2:(tb__ "0|0|
S5S82Li;Vi;S46S5S3cVi;A1Ln;X5x2").

Definition pGb : sv := SVar 236.
Definition FEb (g : sv) : list sprop := ltac2:(tb__ "0|1|
S0S18S2dS1fSa1Vg;S17Z3A1A3M0S30A2S0S18S1aVg;S17S94S97Z2Z3dA2Z1A2A1A2S0S18S1aG0S30A2S0S18S1aS30G0A2S4S18A1A3A3A3A3").
Definition shB (k : Z) : sv := ltac2:(tb__ "0|0|
S1fS9eS59S17S93Sb5S98Vk;Z8A2A2A1A3").
Definition C_S (j : nat) : sstate := ltac2:(tb__ "0|3|
S23S7aVj;A1SaeS54S0S3S5S16A2M0S1S5S16UaS5bA4S0G0S1S5S16UbS43Vj;A1M1A4S0G0S1S5S16UdS17SbbA1A4S0G0S1S5S16U12S52S49Vj;A1M2A1A4S0G0S1S5S16U13S52S93G2Z10A2A1A4S0G0S1S5S16U15S7eG2A1A4S4G0A1A3A3A3A3A3A3A2SadS22SbS16A1S3fVj;Vj;S4dA3S0S18S26S21S9fG1S17Z0A1A3A1S9S18S60S59A1S3dA3A3S45S7A9").
Definition C_ (j : nat) : axst := ltac2:(tb__ "0|0|
Sb6S5eVj;A1S50A2").
Definition P_bd_S : sstate := ltac2:(tb__ "0|0|
S23Sa6Sb0S31A1SadS22SbS16A1S3fS36S36S4S19A1A3S3dS45S7A9").
Definition P_bd : axst := mkA P_bd_S X_bd.

Definition FUEL_bd : nat := 300%nat.
Definition cutpcs_bd : list Z := ltac2:(tb__ "0|0|
S9S13S0S13SbaS0S13Sa6S4S13A1A3A3S9S13Sa8Sa9A3A3").
Definition leaf_at (S : axst) (pc : Z) : axst := ltac2:(tb__ "0|0|
S9cS82U0Sb9S44S48VS;Vpc;A4S46A4").
Definition optA (x : option axst) : axst := match x with Some s => s | None => Pre_bd end.
Definition optR (x : option (list sobj)) : list sobj := match x with Some r => r | None => [] end.

Definition E_ (j : nat) : axst := ltac2:(tb__ "0|0|
S55S4bVj;A1SbaA2").
Definition N_ (j : nat) : axst := ltac2:(tb__ "0|0|
S55S7fVj;A1S5aSaVj;A1A1A2").

Definition s_of (j : nat) (E : axst) : wsub := ltac2:(tb__ "0|1|
S0S3S14S16A2M0S1S14S16PfS3aA4S0G0S1S14S16PdS4aVj;A1A4SbePaS83VE;A1S83S90S8eS4S91A1S8fA3A1A3A3A3").
Definition R_of (j : nat) (E : axst) : list sobj := ltac2:(tb__ "0|0|
S79Sc1VE;S90S8eS4S91A1S8fA3S40Vj;VE;A2A3A1").

Definition T_ (j : nat) : axst := ltac2:(tb__ "0|2|
ScaS90S8eS4S91A1M0S8fA3S3bVj;A1M1S40Vj;G1A2S47Vj;G1A2S92S8eG0S8fA3A5").
Definition tvT (j : nat) : list (sv * sv) := ltac2:(tb__ "0|1|
Sb2S3S16S16A2M0U0S0G0S42Vj;A1S39SaVj;A1A1A3A3").
Definition ndT (j : nat) : ndesc := ltac2:(tb__ "0|0|
S8bS80Vj;A1S4S3S3S16S13A2S16A2A1S33S34SaVj;A1A1A1S8aA4").

Definition lives : list nat := live_from 0.
Definition rL (i : nat) : Z := ltac2:(tb__ "0|0|
S93S99ZaS94Z22S9aVi;A1A2A2Z8A2").
Definition z0 : sv := SLit 0.
Definition ndP : ndesc := ND [] [] [].
Definition Lnode (i : nat) : edescA := ltac2:(tb__ "0|0|
S1S3S82S87A2S3S13S16A2S1S82S87S3cVi;A1S38Vi;A1A4S1S13S16S37Vi;A1S35A4A4").
Definition Tnode (j : nat) : edescA := ltac2:(tb__ "0|4|
S1S3S82S87A2S3S13S16A2S1S82S87ScaS90S8eS4S91A1M0S8fA3S3bVj;A1M1S40Vj;G1A2S47Vj;G1A2S92S8eG0S8fA3A5S8bSb2S3S16S16A2M2U0S0G2S42Vj;A1S39SaVj;A1M3A1A3A3S4S3S3S16S13A2S16A2A1S33S34G3A1A1S8aA4A4S1S13S16S94S37Vj;A1Z3A2S35A4A4").
Definition Cnode (j : nat) : edescA := ltac2:(tb__ "0|0|
S1S3S82S87A2S3S13S16A2S1S82S87S4bVj;A1S38Vj;A1A4S1S13S16S94S37Vj;A1Z1A2S35A4A4").
Definition Enode (j : nat) : edescA := ltac2:(tb__ "0|0|
S1S3S82S87A2S3S13S16A2S1S82S87S3bVj;A1S38Vj;A1A4S1S13S16S94S37Vj;A1Z2A2S35A4A4").
Definition Nnode (j : nat) : edescA := ltac2:(tb__ "0|0|
S1S3S82S87A2S3S13S16A2S1S82S87S4eVj;A1S38Vj;A1A4S1S13S16S94S37Vj;A1Z1A2S35A4A4").
Definition cutsE : list edescA := ltac2:(tb__ "0|3|
S0S3S3S82S87A2M0S3S13S16A2M1A2S1G0G1S1S82S87S46S38U0M2A1A4S1S13S16S37G2A1S35A4A4S9S88S9bS5S88S62S9dU1S36A2A4S9bS5S88S6bS3eA4A3A3").
Definition exitsE : list edescA := ltac2:(tb__ "0|3|
S9S88S9bS5S88S4cS3eA4S9S88S9bS5S88S63S3eA4S0S3S3S82S87A2M0S3S13S16A2M1A2M2S1G0G1S1S82S87S6aS78A4S1S13S16Z0S35A4A4S4G2A1A3A3A3").

Definition isSomeb {A} (o : option A) : bool := match o with Some _ => true | None => false end.

Definition lit_in (lo hi : sv) (n : Z) : bool := ltac2:(tb__ "0|6|
S16S2Llo;Vlo;S13S16S2Lhi;Vhi;S13S6S6S95Z0R2A2S95R2R1A2A2S95R1Vn;A2A2Lh;S14S7Li;M0Sa3S16S16S7Lb;La;M1Lop;M2G2Sa4G1Lop;M3G3S2S15S16S7La;Lw;Lsgn;M4S14S16S13S7Lk;Li;M5Ll0;X16x8Ll;G0G2G2G3G3G4S14G5Ll;X16x8").
Definition fr_obj (o : sobj) : bool := ltac2:(tb__ "0|3|
S10S6S1dS27Vo;A1M0S30A2S56S29Vo;A1M1S28Vo;A1M2Z518A3A2S6S1dG0S32A2S56G1G2Z30A3A2A2").
Definition fr_xr (r : sv * sv) : bool := ltac2:(tb__ "0|2|
S10S6S1dScS16S16Vr;A3M0S30A2S1dSdS16S16Vr;A3M1S17Z518A1A2A2S6S1dG0S32A2S1dG1S17Z30A1A2A2A2").

Definition chkE' (j : nat) (E : axst) : bool := ltac2:(tb__ "0|f|
S6S6S6S6S6S6S6S6S6S6S6S77SeS1cA1Sc1VE;S90S8eS4S91A1M0S8fA3M1S40Vj;VE;A2M2A3A2Sc2VE;G1G2S47Vj;VE;A2M3S0S82S92S8eG0S8fA3S4S82A1A3A5A2ScbS31G2A2A2Sd2S31S2bS83VE;A1M4A1M5A2A2S8dG5S89S0S3S16S16A2M6S42Vj;A1M7S39SaVj;A1M8A1A3M9S4S3S3S16S13A2S16A2A1S33S34Vj;A1A1MaA3A2A2Sc6G5S33S34G8A1A1MbA2A2Sc9S25G4A1McS17Z0A1MdSc3GaGbA5A2S1dScS16S16G7A3MeSbfG2PcA2A2A2S1dSdS16S16G7A3SbfG2PdA2A2A2ScdS18S2aS26S21S9fGeGdA3A1A1GcA3A2SccGcG9S11S5U0A2S75G3A5A2SceG6S76S84VE;A1A3A2").
Definition chkE (j : nat) : bool := ltac2:(tb__ "0|0|
S6fVj;S3bVj;A1A2").

Definition didx (j : nat) : nat := ltac2:(tb__ "0|0|
SaaSaaU4S36A2S12S5S58SaVj;A1A1A2A2").
Definition Nd_ (j : nat) (N : axst) : axst := ltac2:(tb__ "0|0|
S85VN;Sd4S83VN;A1S53Vj;A1A2A2").
Definition sN (j : nat) (N : axst) : wsub := ltac2:(tb__ "0|0|
SbeS31S83S4fVj;VN;A2A1S83S3cSaVj;A1A1A1A3").
Definition chkN' (j : nat) (N : axst) : bool := ltac2:(tb__ "0|d|
SfS1cA1S2Lx;Sd0S1cS2eS83VN;A1M0A1S53Vj;A1A3S1cS6S6S6S6S6S6S6S6S6S1dS27R1A1ScS16S16S42Vj;A1M1A3M2A2S1dS29R1A1S17Z0A1M3A2A2S1dS28R1A1SdS16S16G1A3A2A2ScdS18S2aS21S9fG2G3A3A1S25G0A1A3A2S86S4fVj;VN;A2M4S3cSaVj;A1M5A1S7dVj;VN;A2M6A3A2Sc0G6S31A2A2Sd2S31S2bS83G4A1M7A1M8A2A2S8dG8S89Sb2S3S16S16A2M9U0S0G9G1S39G5A1MaA3A3MbS4S3S3S16S13A2S16A2A1S33S34Vj;A1A1McA3A2A2Sb3G6GbGaA3A2Sc8S25G7A1Sc7G6S33S34G5A1A1A2GcA3A2Lo;S7Xfx2").
Definition chkN (j : nat) : bool := ltac2:(tb__ "0|0|
S71Vj;S4eVj;A1A2").

Definition chkC (j : nat) : bool := ltac2:(tb__ "0|1|
S8cSb7S31S44S48S31S0S88S4cVj;A1S4S88A1M0A3S0S88S5fVj;A1G0A3A7").

Definition bd_chk_live (j : nat) : bool := ltac2:(tb__ "0|0|
S6S6dVj;A1S6S6eVj;A1S70Vj;A1A2A2").

Definition bd_chk_stmt : Prop := ltac2:(tb__ "0|0|
Sb4S2SceS5S6cS3eA3S8A3").
Definition bd_ejcert_stmt : Prop := ltac2:(tb__ "0|0|
Sb4S2S8cSb7S31S44S48S31S72S74A7S8A3").
