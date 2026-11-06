(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "nat"; "pair"; "nil"; "app"; "prod"; "bool"; "None"; "false"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SLit"; "sv"; "sprop"; "SVar"; "cell"; "SAlu"; "mkCell"; "SPUle"; "sobj"; "DUnknown"; "mkObj"; "SPBranch"; "SPAlign"; "SPEq"; "SPNot"; "FcsrFrm0"; "SMd"; "mkSS"; "tfact"; "TFle"; "DArr"; "DZero"; "SExt"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_SLL"; "BC_EQ"; "M_MUL"; "ALU_AND"; "ALU_SRL"; "BC_GE"; "BC_GEU"; "BC_NE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_tess_polygon_states"; "pN"; "poutK"; "pcut"; "pobjs"; "pOUT"; "vF"; "pSCR"; "pPTS"; "stk2"; "n3"; "shR2"; "stk3"; "nm2"; "F4"; "pre2"; "ff"; "pobjs0"; "psp"; "X_pg"; "ext_facts"; "ext_regs"; "loc_cells0"; "pNXT"; "pPRV"; "pg_base_facts"; "regs4e"; "NXC"; "pRFX"; "vFL"; "A16"; "M16"; "O_resH"; "O_resL"; "PG_DF"; "V_DEPTH"; "fin_facts"; "gD"; "gF"; "gR"; "loc_cells1"; "n12"; "nw_facts"; "o12"; "ppost_fregs"; "ppost_regs"; "pstk_cells"; "regs4"; "res2"; "res_ok"; "shD"; "shF"; "w_cells"; "C_b6cI"; "C_b6cK"; "C_c84"; "DBLMAX"; "F3"; "FZERO_S"; "F_cap"; "F_scr"; "K708"; "K830"; "Kaa4"; "Kb08"; "Kb14"; "Kb64"; "Kbbp"; "Kcm"; "Kd10"; "Kd60"; "Ke1"; "Ke2"; "Ke3"; "Kext"; "Kfin"; "Knw"; "Knw2"; "Kproj"; "Ktail"; "M32"; "O_desc"; "O_flag"; "O_frame"; "O_pbelow"; "O_pnxt"; "O_pout"; "O_pp2d"; "O_pprv"; "O_prfx"; "O_pstk"; "O_pts"; "O_res"; "PG_DEPTH"; "frame_facts"; "gl_facts"; "hdr_cells"; "out3"; "pfregs"; "pregs"; "ptmpl3"; "spo"; "@Corelib.Numbers.BinNums"; "Z"; "N"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "FE"; "@Stdlib.ZArith.BinInt.Z"; "pow"; "opp"; "add"; "@Corelib.Init.Nat"; "add"; "@Stdlib.PArith.BinPos.Pos"; "of_nat"; "@Corelib.Lists.ListDef"; "map"; "seq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "A_globals"; "mkA"; "SHB"; "shb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e1.Lib_tess_run2d_states"; "ptr_facts"; "fcallee_saved"; "flds3"; "two20"; "two47"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "setregs"; "NF"; "callee_saved"; "pre_fregs"; "pre_reg"; "pre_regs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_tess_polygon_states.TessPolygonAddr"; "pg_inv"; "pg_ret"; "pg_J708"; "pg_J830"; "pg_Jaa4"; "pg_Jb08"; "pg_Jb14"; "pg_Jb64"; "pg_Jd10"; "pg_Jd60"; "pg_Jtail"; "pg_Lbbp"; "pg_Lcm"; "pg_Le1"; "pg_Le2"; "pg_Le3"; "pg_Lext"; "pg_Lfin"; "pg_Lnw"; "pg_Lnw2"; "pg_Lproj"; "pg_entry"; "pg_f8"; "pg_ms"; "pg_run2d"; "pg_s00"; "pg_scale2d"; "pg_sf"; "pg_sm"; "@Stdlib.Arith.PeanoNat.Nat"; "eqb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymSummary.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code Lib_tess_scale2d.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e1.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_tess_scale2d OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e1.Lib_tess_run2d_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Module TessPolygonAddr.
  Definition pg_entry : Z := 0xac5f4.
  Definition pg_ret : Z := 0xac840.
  Definition pg_inv : Z := 0xac7c4.
  Definition pg_sm : Z := 0x48214.
  Definition pg_sm_ret : Z := 0xac678.
  Definition pg_f8 : Z := 0x603a8.
  Definition pg_f8a_ret : Z := 0xac708.
  Definition pg_ms : Z := 0x5cce8.
  Definition pg_ms_ret : Z := 0xac760.
  Definition pg_Lfin : Z := 0xac884.
  Definition pg_s00 : Z := 0x60288.
  Definition pg_s00_ret : Z := 0xaca0c.
  Definition pg_Lcm : Z := 0xacc60.
  Definition pg_Lnw : Z := 0xaccd0.
  Definition pg_Lnw2 : Z := 0xacd48.
  Definition pg_Lext : Z := 0xacf14.
  Definition pg_Le1 : Z := 0xacf58.
  Definition pg_Le2 : Z := 0xacf9c.
  Definition pg_Le3 : Z := 0xacef0.
  Definition pg_Lbbp : Z := 0xad068.
  Definition pg_Lproj : Z := 0xad238.
  Definition pg_J708 : Z := 0xad360.
  Definition pg_J830 : Z := 0xad488.
  Definition pg_Jaa4 : Z := 0xad6fc.
  Definition pg_Jb08 : Z := 0xad760.
  Definition pg_Jb14 : Z := 0xad76c.
  Definition pg_Jd10 : Z := 0xad968.
  Definition pg_Jb64 : Z := 0xad7bc.
  Definition pg_Jd60 : Z := 0xad9b8.
  Definition pg_Jtail : Z := 0xada10.
  Definition pg_scale2d : Z := 0xadf68.
  Definition pg_ra_sc3 : Z := 0xad494.
  Definition pg_ra_sc4 : Z := 0xad4e0.
  Definition pg_run2d : Z := 0xae04c.
  Definition pg_ra_r2 : Z := 0xad628.
  Definition pg_f8b_ret : Z := 0xadae4.
  Definition pg_sf : Z := 0x483b0.
  Definition pg_sf_ret : Z := 0xac7e4.
  Definition musl_memset_ret : Z := 0xde46c.
  Definition asan_memset_ret : Z := 0x5cda8.
  Definition sm_ret : Z := 0x48390.
  Definition sf_ret : Z := 0x483f4.
End TessPolygonAddr.
Import TessPolygonAddr.

Definition V_DEPTH : positive := 19%positive.
Definition PG_DEPTH : Z := 2304.
Definition pN : sv := SVar 14. Definition pPTS : sv := SVar 15. Definition pOUT : sv := SVar 16. Definition pSCR : sv := SVar 17.
Definition vF : sv := SVar 110.
Definition vFL : sv := SVar 120.
Definition gF : positive := 140%positive.  Definition gD : positive := 141%positive.  Definition gR : positive := 142%positive.
Definition M16 : sv := SLit 18446744073709551600. Definition M32 : sv := SLit 18446744073709551584.
Definition A16 : sv := ltac2:(tb__ "0|0|
SfS25SfS21SfS22S2aSaZ2A1A3SaZfA1A3S48A3").
Definition pNXT : sv := ltac2:(tb__ "0|0|
SfS21S30SfS22S2aSaZ4A1A3A3").
Definition pPRV : sv := ltac2:(tb__ "0|0|
SfS21S40S47A3").
Definition pRFX : sv := ltac2:(tb__ "0|0|
SfS21S41S47A3").
Definition n3 : sv := ltac2:(tb__ "0|0|
SfS21SfS22S2aSaZ1A1A3S2aA3").
Definition n12 : sv := SMd M_MUL pN (SLit 12).
Definition nm2 : sv := SAlu ALU_ADD pN (SLit (-2)).
Definition o12 : sv := SMd M_MUL nm2 (SLit 12).
Definition spo (k : Z) : sv := ltac2:(tb__ "0|0|
SfS21SdPaA1SaVk;A1A3").
Definition psp : sv := spo (-320).
Definition HSE : Z := 0x10007fff8000.

Definition O_pstk (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S14SdPaA1SaN140A1SaZ0A1Vcells;S13A5").
Definition O_pbelow : sobj := ltac2:(tb__ "0|0|
S14S3bSdS4cA1SaZ0A1S3SeA1S13A5").
Definition O_desc : sobj := ltac2:(tb__ "0|3|
S14SdPcA1SaZ0A1M0SaZ48A1S0SeS10G0Z8M1S31A3S0SeS10SaG1A1Z4M2S2aA3S0SeS10SaZ10A1G1G0A3S0SeS10SaZ18A1G2G0A3S0SeS10SaZ20A1G1S2eA3S0SeS10SaZ28A1G2SdP14A1A3S0SeS10SaZ30A1G1S30A3S0SeS10SaZ38A1G1SdP12A1A3S0SeS10SaZ40A1G1G0A3S3SeA1A3A3A3A3A3A3A3A3A3S13A5").
Definition O_res (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S14SdPdA1SaZ0A1SaZ18A1Vcells;S13A5").
Definition O_pts (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S14S31SaZ0A1S52Vcells;S13A5").
Definition ptmpl3 : list tfact := ltac2:(tb__ "0|1|
S0S1cS1dS9U0S7S5S6S90A2A1M0S2aA4S0S1cS1dS9U1G0S2aA4S0S1cS1dS9U2G0S2aA4S3S1cA1A3A3A3").
Definition poutK (k : sv) : odefault := ltac2:(tb__ "0|0|
S1eZcVk;Sa0S8dA4").
Definition O_pout (d : odefault) (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S14S2eSaZ0A1S54Vcells;Vd;A5").
Definition O_pp2d (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S14S30SaZ0A1SfS22S2aSaZ4A1A3Vcells;S13A5").
Definition O_pnxt (d : odefault) : sobj := ltac2:(tb__ "0|0|
S14S40SaZ0A1SfS22S2aSaZ2A1A3S3SeA1Vd;A5").
Definition O_pprv (d : odefault) : sobj := ltac2:(tb__ "0|0|
S14S41SaZ0A1SfS22S2aSaZ2A1A3S3SeA1Vd;A5").
Definition O_prfx : sobj := ltac2:(tb__ "0|0|
S14S45SaZ0A1SfS26SfS21S2aSaZ7A1A3SaZ3A1A3S3SeA1S13A5").

Definition hdr_cells : list cell := ltac2:(tb__ "0|1|
S0SeS10SaZ0A1Z8M0SaZ41b58ab3A1A3S0SeS10SaG0A1G0SaZ11defA1A3S0SeS10SaZ10A1G0SaZac5f4A1A3S3SeA1A3A3A3").
Definition O_frame (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S14S2fSaZ0A1SaZff8A1Vcells;S13A5").
Definition O_flag : sobj := ltac2:(tb__ "0|1|
S14S2fSaZff8A1M0SaZ1000A1S0SeS10G0Z8S46A3S3SeA1A3S13A5").

Definition PG_DF : Z := 320.
Definition X_pg : list (sv * sv) := ltac2:(tb__ "0|2|
S0S5SbSbA2M0S2SbSbSdPcA1SaZ48A1A4S0G0S2SbSbSdPdA1SaZ18A1A4S0G0S2SbSbS31S52A4S0G0S2SbSbS2eS54A4S0G0S2SbSbS30SfS22S2aSaZ4A1A3A4S0G0S2SbSbS40SfS22S2aSaZ2A1A3M1A4S0G0S2SbSbS41G1A4S0G0S2SbSbS45SfS26SfS21S2aSaZ7A1A3SaZ3A1A3A4S0G0S2SbSbS8eS94S4bA1A1SaS4bA1A4S3G0A1A3A3A3A3A3A3A3A3A3").

Definition F_cap : sprop := ltac2:(tb__ "0|0|
S15S28S20S9Q20SdP14A1A3SfS21SfS22S36SaZ1A1A3S36A3A3").
Definition F_scr : sprop := ltac2:(tb__ "0|1|
S15S28SdP12A1SfS21SfS21SfS25SfS21SfS22S2aSaZ3A1M0A3SaZ1eA1A3S79A3SfS22S2aSaZ4A1A3A3SfS25SfS21SfS26SfS21S2aSaZ7A1A3G0A3SaZfA1A3S48A3A3A3").
Definition pg_base_facts : list sprop := ltac2:(tb__ "0|10|
S4ScS0ScS11SaZ3M0A1S2aA2S0ScS11S2aSaSa1A1A2S0ScS15S27SaS94S86A1A1SdS4cA1M1A3S0ScS15S27G1SaS94S93Z2M2Z28A2A1A1A3S0ScS16PaM3Z5A2S0ScS11SaZ20000A1SdG3A1M4A2S0ScS11G4SaSa2A1A2S0ScS11SdP1eA1M5SfS21S3bG1A3A2S0ScS11G5S3bA2S0ScS18S15S23S31SaZ0A1M6A3A1S0ScS18S15S23S2eG6A3A1S0ScS18S15S23S30G6A3A1S0ScS64S0ScS65S3ScA1M7A3A3A3A3A3A3A3A3A3A3A3A3A3A3S4ScS9ePcG0A2S4ScS9ePdM8G0A2S4ScS9ePfG2A2S4ScS9eP10Z4M9A2S0ScS11SaZ646000A1SdG8A1MaA2S0ScS11SfS21GaSaZ18A1A3SaZ7fffff800000A1MbA2S0ScS11SaZ1000A1SdP11McA1MdA2S0ScS11GdGbA2S0ScS11SdP12A1MeSaS93G2Z1aA2A1A2S0ScS11SfS21GdGeA3GbA2S0ScS16GcG9A2S0ScS11SaZ7fff7f800000A1MfG5A2S0ScS11G5GbA2S0ScS11GfG4A2G7A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").

Definition frame_facts : list sprop := ltac2:(tb__ "0|1|
S4ScS0ScS16P6eZ5A2S0ScS18S15S23S2fSaZ0A1A3A1S0ScS11SaZ646000A1M0S2fA2S0ScS11SfS21S2fSaZ1000A1A3SdP1eA1A2S0ScS11G0S46A2S0ScS11SfS21S46SaZ1A1A3SaZ7fffff800000A1A2S3ScA1A3A3A3A3A3A3S92S4fS2fA2A3").
Definition gl_facts : list sprop := ltac2:(tb__ "0|0|
S4ScS92S4eSdPcA1A2S92S50SdPdA1A2A3").

Definition O_resL (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S14SdPdA1SaZ0A1SaZ10A1Vcells;S1fA5").
Definition O_resH (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S14SdPdA1SaZ10A1SaZ18A1Vcells;S13A5").
Definition res2 : list sobj := ltac2:(tb__ "0|1|
S0S12S4aS3SeA1M0A1S0S12S49S0SeS10SaZ10A1Z4SaZ2A1A3G0A3A1S3S12A1A3A3").
Definition pobjs0 (dout dn dp : odefault) (ptsc outc p2dc stkc : list cell) (res : list sobj) : list sobj := ltac2:(tb__ "0|1|
S4S12S0S12S83Vstkc;A1S0S12S7dS0S12S7aS3S12A1M0A3A3A3S4S12Vres;S0S12S84Vptsc;A1S0S12S7fVdout;Voutc;A2S0S12S80Vp2dc;A1S0S12S7eVdn;A1S0S12S81Vdp;A1S0S12S82G0A3A3A3A3A3A3A3A3").
Definition Pre_pg : axst := ltac2:(tb__ "0|2|
S9bS1bSbeSa3Sa8S0S5S1SbA2M0S2S1SbUcSdP16A1A4S3G0A1A3A2Sa6S19S7SbA1S4S12S3aS2bSaZ0A1A1S13S13S3SeA1M1G1G1G1S0S12S85G1A1S3S12A1A3A8S9aA3S42Sa4S8A9S3cA2").

Definition ppost_fregs : list sv := ltac2:(tb__ "0|0|
S98S1SbS1S6SbL_;S9fR1A1SdS97S96U3cR1A2A1A1SdS97S96Ue8R1A2A1A1X6x2Lr;S99U0U20A2A4").
Definition ppost_regs (l : list (nat * sv)) : list sv := ltac2:(tb__ "0|0|
Sa3S98S1SbS1S6SbL_;Sa5R1A1Sa7R1A1SdS97S96Uc8R1A2A1A1X6x2Lr;S99U0U20A2A4Vl;A2").
Definition NXC : positive := 300%positive.

Definition P_inv : axst := ltac2:(tb__ "0|2|
S9bS1bSaaS56S0S5S1SbA2M0S2S1SbUaSaZ2A1A4S3G0A1A3A1S55S19S7SbA1S4S12S3aS2bSaZ0A1A1S13S13S3SeA1M1G1G1G1S59A8S9aA3S42S44S8A9S3cA2").

Definition res_ok : list sobj := ltac2:(tb__ "0|4|
S0S12S4aS0SeS10SaZ0A1M0Z8M1S2eA3S0SeS10SaG1A1Z4M2S36A3S0SeS10SaZcA1G2G0A3S3SeA1M3A3A3A3A1S0S12S49S0SeS10SaZ10A1G2SdPa1A1A3G3A3A1S3S12A1A3A3").
Definition P_ok : axst := ltac2:(tb__ "0|2|
S9bS1bSaaS56S0S5S1SbA2M0S2S1SbUaSdPa1A1A4S3G0A1A3A1S55S19S7SbA1S4S12S3aS2bS36A1S13S13S3SeA1M1G1G1G1S5aA8S9aA3S42S44S8A9S3cA2").

Definition pstk_cells : list cell := ltac2:(tb__ "0|1|
S0SeS10SaN8A1Z8M0SdPbA1A3S0SeS10SaN10A1G0SdP1cA1A3S0SeS10SaN18A1G0SdP1dA1A3S0SeS10SaN20A1G0SdP26A1A3S0SeS10SaN28A1G0SdP27A1A3S0SeS10SaN30A1G0SdP28A1A3S0SeS10SaN38A1G0SdP29A1A3S0SeS10SaN40A1G0SdP2aA1A3S0SeS10SaN48A1G0SdP2bA1A3S0SeS10SaN50A1G0SdP2cA1A3S0SeS10SaN58A1G0SdP2dA1A3S0SeS10SaN60A1G0SdP2eA1A3S0SeS10SaN68A1G0SdP2fA1A3S0SeS10SaN70A1G0SdP44A1A3S0SeS10SaN78A1G0SdP45A1A3S0SeS10SaN80A1G0SdP4eA1A3S3SeA1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition shF (k : Z) : sv := ltac2:(tb__ "0|0|
SfS21SdS4fA1SaS95S9cVk;A2A1A3").
Definition shD : sv := ltac2:(tb__ "0|0|
SfS21SdS4eA1SaS9cA1A3").
Definition shR2 : sv := ltac2:(tb__ "0|0|
SfS21SdS50A1SaS95S9cZ2A2A1A3").

Definition loc_cells0 : list cell := ltac2:(tb__ "0|1|
S0SeS10SaNd0A1Z8M0S5cZ4A1A3S0SeS10SaNc8A1G0SfS21SdPdA1SaZ10A1A3A3S0SeS10SaNc0A1G0S2fA3S3SeA1A3A3A3").
Definition loc_cells1 (c224 : sv) : list cell := ltac2:(tb__ "0|2|
S0SeS10SaN110A1Z8M0SaZ1A1A3S0SeS10SaN108A1G0SfS21S2fSaZ20A1A3A3S0SeS10SaN100A1G0SaZ0A1A3S0SeS10SaNf8A1G0SfS21SdPdA1M1SaG0A1A3A3S0SeS10SaNf0A1G0SfS21G1SaZcA1A3A3S0SeS10SaNe8A1G0S36A3S0SeS10SaNe0A1G0Vc224;A3S0SeS10SaNd8A1G0S2eA3S3SeA1A3A3A3A3A3A3A3A3").
Definition w_cells : list cell := ltac2:(tb__ "0|1|
S0SeS10SaNb8A1Z8M0S30A3S0SeS10SaNb0A1G0S40A3S0SeS10SaNa8A1G0S41A3S0SeS10SaNa0A1G0S45A3S3SeA1A3A3A3A3").

Definition pregs (l : list (nat * sv)) : list sv := ltac2:(tb__ "0|1|
Sa3S98S1SbS1SdS97S96Uc8R1A2A1A1Lr;S99U0U20A2A4S4S5S1SbA2M0S0G0S2S1SbU2S3bA4S0G0S2S1SbU3SdP17A1A4S0G0S2S1SbU4SdP18A1A4S0G0S2S1SbU8SdPaA1A4S0G0S2S1SbU9S3bA4S0G0S2S1SbU12S2fA4S0G0S2S1SbU13S5cZ0A1A4S0G0S2S1SbU16SdPdA1A4S0G0S2S1SbU17SdPcA1A4S0G0S2S1SbU19S9dA4S0G0S2S1SbU1aS2fA4S3G0A1A3A3A3A3A3A3A3A3A3A3A3Vl;A3A2").

Definition pfregs (l : list (nat * sv)) : list sv := ltac2:(tb__ "0|1|
Sa3S98S1SbS1S6SbL_;M0Sc6R1U8A2SdPacA1G0Sc6R1U9A2SdPadA1G0Sc6R1U12A2SdPaeA1G0S9fR1A1SdS97S96U3cR1A2A1A1SdS97S96Ue8R1A2A1A1X6x2X6x2X6x2X6x2Lr;S99U0U20A2A4Vl;A2").
Definition pcut (pc : Z) (regs : list (nat * sv)) (fregs : list (nat * sv)) (ob : list sobj) (facts : list sprop) : axst := ltac2:(tb__ "0|0|
S9bS1bVpc;S8cVregs;A1S8bVfregs;A1S19S7SbA1S4S12Vob;S4S12S9aS0S12S7cS89A1S0S12S7bS3S12A1A3A3A3A3S4ScVfacts;S4ScS87S4ScS88S42A3A3A3S44S8A9S3cA2").
Definition pobjs (dout : odefault) (ptsc outc p2dc : list cell) (stk : list cell) : list sobj := ltac2:(tb__ "0|0|
S3aVdout;S13S13Vptsc;Voutc;Vp2dc;S4SeVstk;S57A3S59A8").
Definition FZERO_S : sv := SLit 18446744069414584320. Definition DBLMAX : sv := SLit 0x7fe1ccf385ebc8a0.
Definition ff : list (nat * sv) := ltac2:(tb__ "0|1|
S0S5S1SbA2M0S2S1SbU8S63A4S0G0S2S1SbU9S61A4S3G0A1A3A3").

Definition fin_facts : list sprop := ltac2:(tb__ "0|5|
S0ScS17SfS21SdP96M0A1M1SfS22SdP97A1M2SaZ2M3A1M4A3A3SfS22S33G4A3A2S0ScS11SaZ1A1G2A2S0ScS11G2S33A2S0ScS16G0G3A2S0ScS11G1SaS93G3Z18A2A1A2S3ScA1A3A3A3A3A3").
Definition Kfin : axst := ltac2:(tb__ "0|4|
S2cSbaS0S5S1SbA2M0S2S1SbU5S2aA4S0G0S2S1SbU6SfS21S2fSaZ20A1A3A4S0G0S2S1SbUaSfS21S31SdP96A1A3M1A4S0G0S2S1SbUbG1A4S0G0S2S1SbUcSdP97A1A4S0G0S2S1SbUfS34A4S0G0S2S1SbU10SfS21SdPdA1M2SaZcA1A3A4S0G0S2S1SbU11SfS21G2SaZ8A1A3A4S0G0S2S1SbU14S2aA4S0G0S2S1SbU15S5bA4S0G0S2S1SbU18SaZ2A1A4S0G0S2S1SbU1bS33A4S3G0A1A3A3A3A3A3A3A3A3A3A3A3A3S39S2dS2bSaZ0A1A1S3SeA1M3G3G3S3fA5S4dA5").

Definition C_c84 : axst := ltac2:(tb__ "0|3|
S2cZac8dcS0S5S1SbA2M0S2S1SbU5S2aA4S0G0S2S1SbU6SfS21S2fSaZ20A1A3A4S0G0S2S1SbUfS34A4S0G0S2S1SbU10SfS21SdPdA1M1SaZcA1A3A4S0G0S2S1SbU11SfS21G1SaZ8A1A3A4S0G0S2S1SbU14S2aA4S0G0S2S1SbU15S5bA4S0G0S2S1SbU18SaZ2A1A4S0G0S2S1SbU1bS33A4S3G0A1A3A3A3A3A3A3A3A3A3S39S2dS2bSaZ0A1A1S3SeA1M2G2G2S3fA5S3ScA1A5").

Definition C_b6cI : axst := ltac2:(tb__ "0|3|
S2cSa9S0S5S1SbA2M0S2S1SbU18SaZ2A1A4S3G0A1M1A3G1S2dS2bSaZ0A1A1S3SeA1M2G2G2G2A5S3ScA1A5").

Definition pre2 : list (nat * sv) := ltac2:(tb__ "0|1|
S0S5S1SbA2M0S2S1SbU5S30A4S0G0S2S1SbU6SaZ1A1A4S0G0S2S1SbU7S2aA4S0G0S2S1SbUdSaZ0A1A4S0G0S2S1SbU11S34A4S0G0S2S1SbU14S2aA4S0G0S2S1SbU15S2eA4S0G0S2S1SbU18S31A4S3G0A1A3A3A3A3A3A3A3A3").
Definition stk2 : list cell := ltac2:(tb__ "0|0|
S4SeS51S2aA1S4SeS5dS3fA3A3").

Definition Kcm : axst := ltac2:(tb__ "0|4|
S2cSb5S4S5S1SbA2M0S38S0G0S2S1SbUaSaZ0A1M1A4S0G0S2S1SbUbSfS21S31SdP96A1A3M2A4S0G0S2S1SbUcG2A4S0G0S2S1SbU1bSdP97A1A4S3G0A1A3A3A3A3A3S39S2dS2bG1A1S3SeA1M3G3G3S32A5S4dA5").

Definition nw_facts : list sprop := ltac2:(tb__ "0|2|
S0ScS17SfS21SdP98A1M0S1aS24SdP99A1M1SaZ3A1A3A3S33A2S0ScS11SaZ1A1G1A2S0ScS11G1S2aA2S0ScS11G0SaS93Z2Z16A2A1A2S3ScA1A3A3A3A3").
Definition Knw : axst := ltac2:(tb__ "0|2|
S2cSbbS4S5S1SbA2M0S38S0G0S2S1SbUcSdP98A1A4S0G0S2S1SbUeSdP99A1A4S3G0A1A3A3A3S39S2dS2bSaZ0A1A1S3SeA1M1G1G1S32A5S53A5").

Definition Knw2 : axst := ltac2:(tb__ "0|7|
S2cSbcS4S5S1SbA2M0S38S0G0S2S1SbUcSfS21SdP98A1M1SaZ3A1M2A3A4S0G0S2S1SbUeSfS21SdP99A1SaN1A1A3A4S0G0S2S1SbUfSdP9aA1M3A4S0G0S2S1SbUaSfS21S31SfS22SfS21G1SaZ2M4A1M5A3G5A3A3A4S3G0A1A3A3A3A3A3S39S2dS2bSaZ0A1A1S3SeA1M6G6G6S32A5S4ScS53S0ScS11SfS21G3G2A3S33A2S0ScS11G3SaS93G4Z16A2A1A2S3ScA1A3A3A3A5").

Definition ext_regs : list (nat * sv) := ltac2:(tb__ "0|1|
S4S5S1SbA2M0S38S0G0S2S1SbUbSdP98A1A4S0G0S2S1SbUcSdP99A1A4S3G0A1A3A3A3").
Definition ext_facts : list sprop := ltac2:(tb__ "0|4|
S0ScS17SfS21SdP98A1M0S1aS24SdP99A1M1SaZ3A1A3A3SfS21S33SaZ2M2A1M3A3A2S0ScS11SaZ1A1G1A2S0ScS11G1S2aA2S0ScS11G3G0A2S0ScS11G0SaS93G2Z16A2A1A2S3ScA1A3A3A3A3A3").
Definition Kext : axst := ltac2:(tb__ "0|1|
S2cSb9S3eS3S5S1SbA2A1S2dS2bSaZ0A1A1S3SeA1M0G0G0S32A5S3dA5").
Definition Ke1 : axst := ltac2:(tb__ "0|1|
S2cSb6S3eS3S5S1SbA2A1S2dS2bSaZ0A1A1S3SeA1M0G0G0S32A5S3dA5").
Definition Ke2 : axst := ltac2:(tb__ "0|1|
S2cSb7S3eS3S5S1SbA2A1S2dS2bSaZ0A1A1S3SeA1M0G0G0S32A5S3dA5").
Definition Ke3 : axst := ltac2:(tb__ "0|1|
S2cSb8S3eS3S5S1SbA2A1S2dS2bSaZ0A1A1S3SeA1M0G0G0S32A5S3dA5").

Definition Kproj : axst := ltac2:(tb__ "0|c|
S2cSbdS4S5S1SbA2M0S38S0G0S2S1SbUfSdP9aA1M1A4S0G0S2S1SbUeSfS21SaZ1M2A1M3SdP9cM4A1M5A3A4S0G0S2S1SbU14SdP99A1M6A4S3G0A1M7A3A3A3A3G7S2dS2bSaZ0A1A1S3SeA1M8G8G8S32A5S0ScS17SfS21G1S1aS24G6SaZ3A1A3A3SfS21S33SaZ2M9A1MaA3A2S0ScS17SfS21G5SfS22G6G3A3A3SfS22S2aG3A3A2S0ScS11G3G6A2S0ScS11G6S2aA2S0ScS16G4G2A2S0ScS11GaG1A2S0ScS11G1SaS93G9Z16A2A1MbA2S0ScS11G5GbA2S3ScA1A3A3A3A3A3A3A3A3A5").

Definition Kbbp : axst := ltac2:(tb__ "0|14|
S2cSb4S4S5S1SbA2M0S38S0G0S2S1SbUcSdP98A1M1A4S0G0S2S1SbUeSdP9aA1M2A4S0G0S2S1SbUfSfS21SaZ1M3A1M4SdP9cM5A1M6A3A4S0G0S2S1SbU14SdP99A1M7A4S3G0A1M8A3A3A3A3A3G8S2dS2bSaZ0A1A1S3SeA1M9G9G9S32A5S0ScS17SfS21G6SfS22G7G4A3A3SfS22S2aG4A3MaA2S0ScS11S1aS24G6SaZ3A1A3MbSfS22G1G4A3McA2S0ScS11GcSfS21GbSaZ2MdA1MeA3MfA2S0ScS11GfSfS22G2G4A3M10A2S0ScS11G10SfS21GbSaZ4A1A3A2S0ScS11SfS21G6GeA3GaA2S0ScS11G4G7A2S0ScS11G7S2aA2S0ScS16G5G3A2S0ScS11G6SaS93GdZ15A2A1A2S0ScS11SfS21G1G7A3SfS21SfS21G6S2aA3M11G4A3M12A2S0ScS11G1G12A2S0ScS11SfS21G2G7A3SfS21G11GeA3M13A2S0ScS11G2G13A2S3ScA1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A5").

Definition stk3 : list cell := ltac2:(tb__ "0|0|
S4SeS51S30A1S4SeS5dS3fA3A3").
Definition F3 : sprop := ltac2:(tb__ "0|0|
S18S15S29S2aSaZ3A1A3A1").
Definition F4 : sprop := ltac2:(tb__ "0|0|
S15S23S2aSaZ4A1A3").

Definition K708 : axst := ltac2:(tb__ "0|4|
S2cSabS0S5S1SbA2M0S2S1SbU5S30A4S0G0S2S1SbU6SaZ1A1A4S0G0S2S1SbU7S2aA4S0G0S2S1SbUdSaZ0A1M1A4S0G0S2S1SbU11S34A4S0G0S2S1SbU15S2eA4S0G0S2S1SbU18S31A4S0G0S2S1SbU1bSdP9dA1A4S3G0A1M2A3A3A3A3A3A3A3A3G2S2dS2bG1A1S3SeA1M3G3G3S32A5S3ScA1A5").

Definition out3 : list cell := ltac2:(tb__ "0|2|
S0SeS10SaZ0A1M0Z4M1G0A3S0SeS10SaG1A1G1SaZ1A1A3S0SeS10SaZ8A1G1SaZ2A1A3S3SeA1A3A3A3").
Definition K830 : axst := ltac2:(tb__ "0|3|
S2cSacS0S5S1SbA2M0S2S1SbU5S30A4S0G0S2S1SbU14SaZ1A1A4S0G0S2S1SbU15SdP9dA1A4S0G0S2S1SbU1bS34A4S3G0A1M1A3A3A3A3G1S2dS2bSaZ0A1A1S3SeA1M2S8aG2S35A5S0ScS62S3ScA1A3A5").

Definition regs4 : list (nat * sv) := ltac2:(tb__ "0|2|
S0S5S1SbA2M0S2S1SbU5S30A4S0G0S2S1SbU6SaZ1A1A4S0G0S2S1SbUfS34A4S0G0S2S1SbU10SfS21SdPdA1M1SaZcA1A3A4S0G0S2S1SbU11SfS21G1SaZ8A1A3A4S0G0S2S1SbU15S2eA4S0G0S2S1SbU18S31A4S0G0S2S1SbU1bSdP9dA1A4S3G0A1A3A3A3A3A3A3A3A3").
Definition Kaa4 : axst := ltac2:(tb__ "0|3|
S2cSadS4S5S1SbA2M0S58S0G0S2S1SbUbSdPa2A1A4S3G0A1M1A3A3G1S2dS2bSaZ0A1A1S3SeA1M2G2G2S35A5S0ScS37S3ScA1A3A5").
Definition Kb08 : axst := ltac2:(tb__ "0|3|
S2cSaeS4S5S1SbA2M0S58S0G0S2S1SbUbSdPa2A1A4S0G0S2S1SbUcSdPa3A1A4S3G0A1M1A3A3A3G1S2dS2bSaZ0A1A1S3SeA1M2G2G2S35A5S0ScS37S3ScA1A3A5").

Definition regs4e : list (nat * sv) := ltac2:(tb__ "0|2|
S0S5S1SbA2M0S2S1SbU6SaZ1A1A4S0G0S2S1SbUfS34A4S0G0S2S1SbU10SfS21SdPdA1M1SaZcA1A3A4S0G0S2S1SbU11SfS21G1SaZ8A1A3A4S0G0S2S1SbU15S2eA4S0G0S2S1SbU18SdPa1A1A4S0G0S2S1SbU1bSdP9dA1A4S3G0A1A3A3A3A3A3A3A3").
Definition Kb14 : axst := ltac2:(tb__ "0|1|
S2cSafS43S3S5S1SbA2A1S2dS2bSaZ0A1A1S3SeA1M0G0G0S35A5S0ScS37S3ScA1A3A5").
Definition Kd10 : axst := ltac2:(tb__ "0|1|
S2cSb1S43S3S5S1SbA2A1S2dS2bSaZ0A1A1S3SeA1M0G0G0S35A5S0ScS37S3ScA1A3A5").

Definition Kb64 : axst := ltac2:(tb__ "0|3|
S2cSb0S4S5S1SbA2M0S43S0G0S2S1SbUaSfS21S2eSaZcA1A3A4S3G0A1M1A3A3G1S2dS2bSaZ1A1A1S3SeA1M2G2G2S35A5S0ScS37S3ScA1A3A5").
Definition Kd60 : axst := ltac2:(tb__ "0|3|
S2cSb2S4S5S1SbA2M0S43S0G0S2S1SbUaSfS21S2eSaZcA1A3A4S3G0A1M1A3A3G1S2dS2bSaZ1A1A1S3SeA1M2G2G2S35A5S0ScS37S3ScA1A3A5").

Definition Ktail : axst := ltac2:(tb__ "0|4|
S2cSb3S0S5S1SbA2M0S2S1SbU6SaZ1A1A4S0G0S2S1SbUfS34A4S0G0S2S1SbU10SfS21SdPdA1M1SaZcA1A3A4S0G0S2S1SbU11SfS21G1SaZ8A1A3A4S0G0S2S1SbU15S2eA4S0G0S2S1SbU18SdPa1A1A4S3G0A1M2A3A3A3A3A3A3G2S2dS2bS36A1S3SeA1M3G3G3S35A5S3ScA1A5").

Definition C_b6cK : axst := ltac2:(tb__ "0|3|
S2cSa9S0S5S1SbA2M0S2S1SbU18SdPa1A1A4S3G0A1M1A3G1S3aS2bS36A1S13S13S3SeA1M2G2G2S57S5aA8S3ScA1A5").

Definition FUEL_pg : nat := 2000%nat.
Definition cutpcs_pg : list Z := ltac2:(tb__ "0|0|
S0S8fSc5S0S8fSbfS0S8fSc0S0S8fSbaS0S8fSc2S0S8fSb5S0S8fSbbS0S8fSbcS0S8fSb9S0S8fSb6S0S8fSb7S0S8fSb8S0S8fSb4S0S8fSbdS0S8fSabS0S8fSacS0S8fSadS0S8fSaeS0S8fSafS0S8fSb1S0S8fSb0S0S8fSb2S0S8fSb3S0S8fSc3S0S8fSc1S0S8fSc4S0S8fSaaS0S8fSa9S0S8fZac8dcS3S8fA1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").

Definition hcuts_pg : list axst := ltac2:(tb__ "0|0|
S0S91S74S0S91S60S0S91S5eS0S91S6dS0S91S75S0S91S76S0S91S73S0S91S70S0S91S71S0S91S72S0S91S77S0S91S6cS0S91S66S0S91S67S0S91S68S0S91S69S0S91S6aS0S91S6eS0S91S6bS0S91S6fS0S91S78S0S91S5fS3S91A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
