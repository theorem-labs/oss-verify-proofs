(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "nat"; "nil"; "pair"; "app"; "prod"; "bool"; "None"; "false"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SLit"; "sv"; "cell"; "sprop"; "SVar"; "SAlu"; "mkCell"; "SPUle"; "sobj"; "DUnknown"; "mkObj"; "SPBranch"; "SPAlign"; "SPEq"; "SPNot"; "FcsrFrm0"; "SMd"; "mkSS"; "tfact"; "TFle"; "DArr"; "SExt"; "SPUlt"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_SLL"; "BC_EQ"; "M_MUL"; "ALU_AND"; "ALU_SRL"; "BC_GE"; "BC_GEU"; "ALU_XOR"; "BC_NE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_tess_polygon_states"; "pN"; "poutK"; "pcut"; "pobjs"; "shR"; "vF"; "pOUT"; "stk2"; "pPTS"; "pSCR"; "nm2"; "pobjsN"; "pre2"; "F4"; "n3"; "pobjs0"; "stk4"; "ff"; "psp"; "shD"; "A16"; "X_pg"; "ext_facts"; "ext_regs"; "pNXT"; "pg_base_facts"; "regs4e"; "xr3"; "A16n16"; "NXC"; "gR"; "loc_cells0"; "n3x4"; "pPRV"; "res2"; "shF"; "vFL"; "w_cells"; "M16"; "NOTPTS"; "O_resH"; "O_resL"; "PG_DF"; "V_DEPTH"; "fin_facts"; "gD"; "gF"; "loc_cells0b"; "loc_cells1"; "n12"; "nw_facts"; "o12"; "pRFX"; "ppost_fregs"; "ppost_regs"; "pre1"; "pstk_np"; "regs4"; "res_ok"; "stkT"; "C_b6cI"; "C_b6cK"; "C_c84"; "DBLMAX"; "F3"; "FZERO_S"; "F_cap"; "F_scr"; "K708"; "K830"; "Kaa4"; "Kb08"; "Kb14"; "Kb64"; "Kbbp"; "Kcm"; "Kd10"; "Kd60"; "Ke1"; "Ke2"; "Ke3"; "Kext"; "Kfin"; "Knw"; "Knw2"; "Kproj"; "Ktail"; "M32"; "O_desc"; "O_flag"; "O_frame"; "O_pbelow"; "O_pnxt"; "O_pout"; "O_pp2d"; "O_pprv"; "O_prfx"; "O_pstk"; "O_pts"; "O_res"; "PG_DEPTH"; "frame_facts"; "gl_facts"; "hdr_cells"; "kcell"; "loc_cellsT"; "out3"; "pPRVb"; "pRFXb"; "pfregs"; "pregs"; "pstk_cells"; "ptmpl3"; "spo"; "stk3"; "zres_cells"; "@Corelib.Numbers.BinNums"; "Z"; "N"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "FE"; "@Stdlib.ZArith.BinInt.Z"; "pow"; "add"; "opp"; "@Corelib.Init.Nat"; "add"; "@Stdlib.PArith.BinPos.Pos"; "of_nat"; "@Corelib.Lists.ListDef"; "map"; "seq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "A_globals"; "SHB"; "mkA"; "shb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n2.Lib_tess_run2d_states"; "ptr_facts"; "fcallee_saved"; "flds3"; "two20"; "two47"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "setregs"; "NF"; "callee_saved"; "pre_fregs"; "pre_reg"; "pre_regs"; "@Stdlib.Arith.PeanoNat.Nat"; "eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_tess_polygon_states.TessPolygonAddr"; "pg_inv"; "pg_ret"; "pg_J708"; "pg_J830"; "pg_Jaa4"; "pg_Jb08"; "pg_Jb14"; "pg_Jb64"; "pg_Jd10"; "pg_Jd60"; "pg_Jtail"; "pg_Lbbp"; "pg_Lc84"; "pg_Lcm"; "pg_Le1"; "pg_Le2"; "pg_Le3"; "pg_Lext"; "pg_Lfin"; "pg_Lnw"; "pg_Lnw2"; "pg_Lproj"; "pg_entry"; "pg_f8"; "pg_rel"; "pg_run2d"; "pg_s00"; "pg_scale2d"; "pg_sf"; "pg_sm"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code Lib_tess_scale2d.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_tess_scale2d OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n2.Lib_tess_run2d_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Module TessPolygonAddr.
  Definition pg_entry : Z := 0xa8e6c.
  Definition pg_ret : Z := 0xa911c.
  Definition pg_inv : Z := 0xa909c.
  Definition pg_sm : Z := 0x483a8.
  Definition pg_sm_ret : Z := 0xa8ef4.
  Definition pg_f8 : Z := 0x6053c.
  Definition pg_f8a_ret : Z := 0xa8f84.

  Definition pg_Lfin : Z := 0xa9174.
  Definition pg_s00 : Z := 0x6041c.
  Definition pg_s00_ret : Z := 0xa9304.
  Definition pg_Lcm : Z := 0xa95c8.
  Definition pg_Lnw : Z := 0xa9638.
  Definition pg_Lnw2 : Z := 0xa96d4.
  Definition pg_Lext : Z := 0xa9904.
  Definition pg_Le1 : Z := 0xa9984.
  Definition pg_Le2 : Z := 0xa99ec.
  Definition pg_Le3 : Z := 0xa98f8.
  Definition pg_Lbbp : Z := 0xa9b18.
  Definition pg_Lproj : Z := 0xa9eb4.
  Definition pg_J708 : Z := 0xa9c38.
  Definition pg_J830 : Z := 0xa9ca0.
  Definition pg_Jaa4 : Z := 0xaa0a8.
  Definition pg_Jb08 : Z := 0xaa0f8.
  Definition pg_Jb14 : Z := 0xaa104.
  Definition pg_Jd10 : Z := 0xaa354.
  Definition pg_Jb64 : Z := 0xaa120.
  Definition pg_Jd60 : Z := 0xaa370.
  Definition pg_Jtail : Z := 0xaa3ac.
  Definition pg_scale2d : Z := 0xaab20.
  Definition pg_ra_sc3 : Z := 0xa9cac.
  Definition pg_ra_sc4 : Z := 0xa9d14.
  Definition pg_run2d : Z := 0xaac28.
  Definition pg_ra_r2 : Z := 0xa9dc8.
  Definition pg_f8b_ret : Z := 0xaa468.
  Definition pg_sf : Z := 0x48544.
  Definition pg_sf_ret : Z := 0xa90bc.
  Definition musl_memset_ret : Z := 0xdb0f8.
  Definition sm_ret : Z := 0x48524.
  Definition sf_ret : Z := 0x48588.
  Definition pg_rel : Z := 0xa8fc8.
  Definition pg_Lc84 : Z := 0xa91cc.
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
SfS25SfS21SfS22S2bSaZ2A1A3SaZfA1A3S51A3").
Definition pNXT : sv := ltac2:(tb__ "0|0|
SfS21S34SfS22S2bSaZ4A1A3A3").
Definition pPRV : sv := ltac2:(tb__ "0|0|
SfS21S43S3fA3").
Definition pRFX : sv := ltac2:(tb__ "0|0|
SfS21S4cS3fA3").
Definition n3 : sv := ltac2:(tb__ "0|0|
SfS21SfS22S2bSaZ1A1A3S2bA3").
Definition n12 : sv := SMd M_MUL pN (SLit 12).
Definition nm2 : sv := SAlu ALU_ADD pN (SLit (-2)).
Definition o12 : sv := SMd M_MUL nm2 (SLit 12).
Definition spo (k : Z) : sv := ltac2:(tb__ "0|0|
SfS21SePaA1SaVk;A1A3").
Definition psp : sv := spo (-384).
Definition HSE : Z := 0x10007fff8000.

Definition O_pstk (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S14SePaA1SaN180A1SaZ0A1Vcells;S13A5").
Definition O_pbelow : sobj := ltac2:(tb__ "0|0|
S14S3dSeS56A1SaZ0A1S2ScA1S13A5").
Definition O_desc : sobj := ltac2:(tb__ "0|3|
S14SePcA1SaZ0A1M0SaZ48A1S0ScS10G0Z8M1S33A3S0ScS10SaG1A1Z4M2S2bA3S0ScS10SaZ10A1G1G0A3S0ScS10SaZ18A1G2G0A3S0ScS10SaZ20A1G1S31A3S0ScS10SaZ28A1G2SeP14A1A3S0ScS10SaZ30A1G1S34A3S0ScS10SaZ38A1G1SeP12A1A3S0ScS10SaZ40A1G1G0A3S2ScA1A3A3A3A3A3A3A3A3A3S13A5").
Definition O_res (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S14SePdA1SaZ0A1SaZ18A1Vcells;S13A5").
Definition O_pts (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S14S33SaZ0A1S5cVcells;S13A5").
Definition ptmpl3 : list tfact := ltac2:(tb__ "0|1|
S0S1cS1dS9U0S7S5S6Sa0A2A1M0S2bA4S0S1cS1dS9U1G0S2bA4S0S1cS1dS9U2G0S2bA4S2S1cA1A3A3A3").
Definition poutK (k : sv) : odefault := ltac2:(tb__ "0|0|
S1eZcVk;Sb0S9bA4").
Definition O_pout (d : odefault) (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S14S31SaZ0A1S5eVcells;Vd;A5").
Definition O_pp2d (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S14S34SaZ0A1SfS22S2bSaZ4A1A3Vcells;S13A5").
Definition O_pnxt (d : odefault) : sobj := ltac2:(tb__ "0|0|
S14S43SaZ0A1SfS22S2bSaZ2A1A3S2ScA1Vd;A5").
Definition O_pprv (d : odefault) : sobj := ltac2:(tb__ "0|0|
S14S4cSaZ0A1SfS22S2bSaZ2A1A3S2ScA1Vd;A5").
Definition O_prfx : sobj := ltac2:(tb__ "0|0|
S14S5fSaZ0A1SfS26SfS21S2bSaZ7A1A3SaZ3A1A3S2ScA1S13A5").

Definition hdr_cells : list cell := ltac2:(tb__ "0|1|
S0ScS10SaZ0A1Z8M0SaZ41b58ab3A1A3S0ScS10SaG0A1G0SaZ11e15A1A3S0ScS10SaZ10A1G0SaZa8e6cA1A3S2ScA1A3A3A3").
Definition O_frame (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S14S30SaZ0A1SaZff8A1Vcells;S13A5").
Definition O_flag : sobj := ltac2:(tb__ "0|1|
S14S30SaZff8A1M0SaZ1000A1S0ScS10G0Z8S4fA3S2ScA1A3S13A5").

Definition PG_DF : Z := 384.
Definition X_pg : list (sv * sv) := ltac2:(tb__ "0|2|
S0S5SbSbA2M0S3SbSbSePcA1SaZ48A1A4S0G0S3SbSbSePdA1SaZ18A1A4S0G0S3SbSbS33S5cA4S0G0S3SbSbS31S5eA4S0G0S3SbSbS34SfS22S2bSaZ4A1A3A4S0G0S3SbSbS43SfS22S2bSaZ2A1A3M1A4S0G0S3SbSbS4cG1A4S0G0S3SbSbS5fSfS26SfS21S2bSaZ7A1A3SaZ3A1A3A4S0G0S3SbSbS9cSa5S55A1A1SaS55A1A4S2G0A1A3A3A3A3A3A3A3A3A3").

Definition F_cap : sprop := ltac2:(tb__ "0|0|
S15S28S1fS9Q20SeP14A1A3SfS21SfS22S35SaZ1A1A3S35A3A3").
Definition F_scr : sprop := ltac2:(tb__ "0|1|
S15S28SeP12A1SfS21SfS21SfS25SfS21SfS22S2bSaZ3A1M0A3SaZ1eA1A3S82A3SfS22S2bSaZ4A1A3A3SfS25SfS21SfS26SfS21S2bSaZ7A1A3G0A3SaZfA1A3S51A3A3A3").
Definition pg_base_facts : list sprop := ltac2:(tb__ "0|10|
S4SdS0SdS11SaZ3M0A1S2bA2S0SdS11S2bSaSb1A1A2S0SdS15S27SaSa5S8fA1A1SeS56A1M1A3S0SdS15S27G1SaSa5Sa3Z2M2Z28A2A1A1A3S0SdS16PaM3Z5A2S0SdS11SaZ20000A1SeG3A1M4A2S0SdS11G4SaSb2A1A2S0SdS11SeP1eA1M5SfS21S3dG1A3A2S0SdS11G5S3dA2S0SdS18S15S23S33SaZ0A1M6A3A1S0SdS18S15S23S31G6A3A1S0SdS18S15S23S34G6A3A1S0SdS6dS0SdS6eS2SdA1M7A3A3A3A3A3A3A3A3A3A3A3A3A3A3S4SdSaePcG0A2S4SdSaePdM8G0A2S4SdSaePfG2A2S4SdSaeP10Z4M9A2S0SdS11SaZ643000A1SeG8A1MaA2S0SdS11SfS21GaSaZ18A1A3SaZ7fffff800000A1MbA2S0SdS11SaZ1000A1SeP11McA1MdA2S0SdS11GdGbA2S0SdS11SeP12A1MeSaSa3G2Z1aA2A1A2S0SdS11SfS21GdGeA3GbA2S0SdS16GcG9A2S0SdS11SaZ7fff7f800000A1MfG5A2S0SdS11G5GbA2S0SdS11GfG4A2G7A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").

Definition frame_facts : list sprop := ltac2:(tb__ "0|1|
S4SdS0SdS16P6eZ5A2S0SdS18S15S23S30SaZ0A1A3A1S0SdS11SaZ643000A1M0S30A2S0SdS11SfS21S30SaZ1000A1A3SeP1eA1A2S0SdS11G0S4fA2S0SdS11SfS21S4fSaZ1A1A3SaZ7fffff800000A1A2S2SdA1A3A3A3A3A3A3Sa2S59S30A2A3").
Definition gl_facts : list sprop := ltac2:(tb__ "0|0|
S4SdSa2S58SePcA1A2Sa2S49SePdA1A2A3").

Definition O_resL (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S14SePdA1SaZ0A1SaZ10A1Vcells;S13A5").
Definition O_resH (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S14SePdA1SaZ10A1SaZ18A1Vcells;S13A5").
Definition zres_cells : list cell := ltac2:(tb__ "0|3|
S0ScS10SaZ0A1M0Z8M1G0A3S0ScS10SaG1A1Z4M2G0A3S0ScS10SaZcA1G2G0A3S2ScA1A3A3A3").
Definition res2 : list sobj := ltac2:(tb__ "0|0|
S0S12S54S9eA1S0S12S53S0ScS10SaZ10A1Z4SaZ2A1A3S2ScA1A3A1S2S12A1A3A3").
Definition pobjs0 (dout dn dp : odefault) (ptsc outc p2dc stkc : list cell) (res : list sobj) : list sobj := ltac2:(tb__ "0|1|
S4S12S0S12S8cVstkc;A1S0S12S86S0S12S83S2S12A1M0A3A3A3S4S12Vres;S0S12S8dVptsc;A1S0S12S88Vdout;Voutc;A2S0S12S89Vp2dc;A1S0S12S87Vdn;A1S0S12S8aVdp;A1S0S12S8bG0A3A3A3A3A3A3A3A3").
Definition Pre_pg : axst := ltac2:(tb__ "0|2|
SacS1bSd0Sb3Sb8S0S5S1SbA2M0S3S1SbUcSeP16A1A4S2G0A1A3A2Sb6S19S7SbA1S4S12S3aS2cSaZ0A1A1S13S13S2ScA1M1G1G1G1S0S12S8eG1A1S2S12A1A3A8SaaA3S44Sb4S8A9S40A2").

Definition ppost_fregs : list sv := ltac2:(tb__ "0|0|
Sa8S1SbS1S6SbL_;SafR1A1SeSa7Sa6U3cR1A2A1A1SeSa7Sa6Ue8R1A2A1A1X6x2Lr;Sa9U0U20A2A4").
Definition ppost_regs (l : list (nat * sv)) : list sv := ltac2:(tb__ "0|0|
Sb3Sa8S1SbS1S6SbL_;Sb5R1A1Sb7R1A1SeSa7Sa6Uc8R1A2A1A1X6x2Lr;Sa9U0U20A2A4Vl;A2").
Definition NXC : positive := 300%positive.

Definition P_inv : axst := ltac2:(tb__ "0|2|
SacS1bSbbS61S0S5S1SbA2M0S3S1SbUaSaZ2A1A4S2G0A1A3A1S60S19S7SbA1S4S12S3aS2cSaZ0A1A1S13S13S2ScA1M1G1G1G1S4dA8SaaA3S44S48S8A9S40A2").

Definition res_ok : list sobj := ltac2:(tb__ "0|4|
S0S12S54S0ScS10SaZ0A1M0Z8M1S31A3S0ScS10SaG1A1Z4M2S35A3S0ScS10SaZcA1G2G0A3S2ScA1M3A3A3A3A1S0S12S53S0ScS10SaZ10A1G2SePa1A1A3G3A3A1S2S12A1A3A3").
Definition P_ok : axst := ltac2:(tb__ "0|2|
SacS1bSbbS61S0S5S1SbA2M0S3S1SbUaSePa1A1A4S2G0A1A3A1S60S19S7SbA1S4S12S3aS2cS35A1S13S13S2ScA1M1G1G1G1S65A8SaaA3S44S48S8A9S40A2").

Definition pstk_cells : list cell := ltac2:(tb__ "0|1|
S0ScS10SaN8A1Z8M0SePbA1A3S0ScS10SaN10A1G0SeP1cA1A3S0ScS10SaN18A1G0SeP1dA1A3S0ScS10SaN20A1G0SeP26A1A3S0ScS10SaN28A1G0SeP27A1A3S0ScS10SaN30A1G0SeP28A1A3S0ScS10SaN38A1G0SeP29A1A3S0ScS10SaN40A1G0SeP2aA1A3S0ScS10SaN48A1G0SeP2bA1A3S0ScS10SaN50A1G0SeP2cA1A3S0ScS10SaN58A1G0SeP2dA1A3S0ScS10SaN60A1G0SeP2eA1A3S0ScS10SaN68A1G0SeP2fA1A3S0ScS10SaN70A1G0SeP44A1A3S0ScS10SaN78A1G0SeP45A1A3S0ScS10SaN80A1G0SeP4eA1A3S0ScS10SaN88A1G0SeP4fA1A3S0ScS10SaN180A1G0SaZ0A1A3S2ScA1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition shF (k : Z) : sv := ltac2:(tb__ "0|0|
SfS21SeS59A1SaSa4SabVk;A2A1A3").
Definition shD : sv := ltac2:(tb__ "0|0|
SfS21SeS58A1SaSabA1A3").
Definition shR2 : sv := ltac2:(tb__ "0|0|
SfS21SeS49A1SaSa4SabZ2A2A1A3").
Definition FUEL_pg : nat := 4000%nat.

Definition loc_cells0 : list cell := ltac2:(tb__ "0|1|
S0ScS10SaNf8A1Z8M0S30A3S0ScS10SaN108A1G0S4eZ4A1A3S0ScS10SaN110A1G0SfS21S30SaZ20A1A3A3S2ScA1A3A3A3").

Definition pregs (l : list (nat * sv)) : list sv := ltac2:(tb__ "0|1|
Sb3Sa8S1SbS1SeSa7Sa6Uc8R1A2A1A1Lr;Sa9U0U20A2A4S4S5S1SbA2M0S0G0S3S1SbU2S3dA4S0G0S3S1SbU3SeP17A1A4S0G0S3S1SbU4SeP18A1A4S0G0S3S1SbU8SePaA1A4S0G0S3S1SbU9S3dA4S0G0S3S1SbU12S30A4S0G0S3S1SbU13S4eZ0A1A4S0G0S3S1SbU14S30A4S0G0S3S1SbU15SePdA1A4S0G0S3S1SbU17SePcA1A4S0G0S3S1SbU18SadA4S2G0A1A3A3A3A3A3A3A3A3A3A3A3Vl;A3A2").

Definition pfregs (l : list (nat * sv)) : list sv := ltac2:(tb__ "0|1|
Sb3Sa8S1SbS1S6SbL_;M0Sb9R1U8A2SePacA1G0Sb9R1U9A2SePadA1G0Sb9R1U12A2SePaeA1G0Sb9R1U13A2SePafA1G0SafR1A1SeSa7Sa6U3cR1A2A1A1SeSa7Sa6Ue8R1A2A1A1X6x2X6x2X6x2X6x2X6x2Lr;Sa9U0U20A2A4Vl;A2").
Definition pcut (pc : Z) (regs : list (nat * sv)) (fregs : list (nat * sv)) (ob : list sobj) (facts : list sprop) : axst := ltac2:(tb__ "0|0|
SacS1bVpc;S99Vregs;A1S98Vfregs;A1S19S7SbA1S4S12Vob;S4S12SaaS0S12S85S92A1S0S12S84S2S12A1A3A3A3A3S4SdVfacts;S4SdS90S4SdS91S44A3A3A3S48S8A9S40A2").
Definition pobjs (dout : odefault) (ptsc outc p2dc : list cell) (stk : list cell) : list sobj := ltac2:(tb__ "0|0|
S3aVdout;S13S13Vptsc;Voutc;Vp2dc;S4ScVstk;S9aA3S4dA8").
Definition FZERO_S : sv := SLit 18446744069414584320. Definition DBLMAX : sv := SLit 0x7fe1ccf385ebc8a0.
Definition ff : list (nat * sv) := ltac2:(tb__ "0|1|
S0S5S1SbA2M0S3S1SbU8S6aA4S0G0S3S1SbU9S6cA4S2G0A1A3A3").
Definition shR (k : Z) : sv := ltac2:(tb__ "0|0|
SfS21SeS49A1SaSa4SabVk;A2A1A3").
Definition NOTPTS : sv := ltac2:(tb__ "0|0|
SfS29S33SaZffffffffffffffffA1A3").
Definition n3x4 : sv := SAlu ALU_SLL n3 (SLit 2).

Definition pre1 : list (nat * sv) := ltac2:(tb__ "0|4|
S0S5S1SbA2M0S3S1SbU1S39A4S0G0S3S1SbU5S2fZ2M1A1A4S0G0S3S1SbU6SfS21SePdA1M2SaZ8A1A3A4S0G0S3S1SbU7S2fZ0A1A4S0G0S3S1SbU16SfS21G2SaZ10A1A3A4S0G0S3S1SbU19SfS21G2SaZcA1A3A4S0G0S3S1SbU1aS2bA4S0G0S3S1SbU1bSaG1A1A4S0G0S3S1SbU1cS2fZ1A1M3A4S0G0S3S1SbU1dG3A4S0G0S3S1SbU1eS3eA4S0G0S3S1SbU1fS2bA4S2G0A1A3A3A3A3A3A3A3A3A3A3A3A3").

Definition fin_facts : list sprop := ltac2:(tb__ "0|3|
S0SdS20SeP96M0A1M1S4bA2S0SdS16G0Z2M2A2S0SdS11G1SaSa3G2Z18A2A1A2S2SdA1A3A3A3").
Definition Kfin : axst := ltac2:(tb__ "0|5|
S2dSccS4S5S1SbA2M0S62S0G0S3S1SbUaSfS21S33SeP96A1M1A3M2A4S0G0S3S1SbUbG2A4S0G0S3S1SbUcG1A4S0G0S3S1SbUdS52A4S0G0S3S1SbUeSaZ0A1M3A4S0G0S3S1SbUfS4bA4S2G0A1A3A3A3A3A3A3A3S3cS2eS2cG3A1S2ScA1M4G4G4S4aA5S57A5").

Definition C_c84 : axst := ltac2:(tb__ "0|1|
S2dSc6S62S3cS2eS2cSaZ0A1A1S2ScA1M0G0G0S4aA5S2SdA1A5").

Definition C_b6cI : axst := ltac2:(tb__ "0|3|
S2dSbaS0S5S1SbA2M0S3S1SbU1bSaZ2A1A4S2G0A1M1A3G1S2eS2cSaZ0A1A1S2ScA1M2G2G2G2A5S2SdA1A5").

Definition A16n16 : sv := ltac2:(tb__ "0|0|
SfS21S3fSfS22S2bSaZ4A1A3A3").
Definition pPRVb : sv := ltac2:(tb__ "0|0|
SfS21S34S47A3").
Definition pRFXb : sv := ltac2:(tb__ "0|0|
SfS21S34SfS21S47S3fA3A3").
Definition w_cells : list cell := ltac2:(tb__ "0|1|
S0ScS10SaNf0A1Z8M0S34A3S0ScS10SaNe8A1G0S43A3S0ScS10SaNe0A1G0S96A3S0ScS10SaNd8A1G0S97A3S2ScA1A3A3A3A3").
Definition loc_cells1 : list cell := ltac2:(tb__ "0|4|
S0ScS10SaN170A1Z8M0SaZ1M1A1A3S0ScS10SaN168A1G0SaZ0M2A1A3S0ScS10SaN160A1G0S39A3S0ScS10SaN158A1G0S34A3S0ScS10SaN150A1G0S31A3S0ScS10SaN148A1G0S35A3S0ScS10SaN140A1G0S3eA3S0ScS10SaN138A1G0S2fG1A1M3A3S0ScS10SaN130A1G0G3A3S0ScS10SaN128A1G0S2fG2A1A3S0ScS10SaN120A1G0SfS21SePdA1SaG0A1A3A3S0ScS10SaN118A1G0S2fZ2A1A3S2ScA1A3A3A3A3A3A3A3A3A3A3A3A3").
Definition stk2 : list cell := ltac2:(tb__ "0|0|
S4ScS5bS4ScS50S4aA3A3").

Definition pre2 : list (nat * sv) := ltac2:(tb__ "0|2|
S0S5S1SbA2M0S3S1SbUaS33A4S0G0S3S1SbUdSaZ0A1A4S0G0S3S1SbUfS52A4S0G0S3S1SbU16SfS21SePdA1M1SaZ10A1A3A4S0G0S3S1SbU19SfS21G1SaZcA1A3A4S0G0S3S1SbU1aS2bA4S0G0S3S1SbU1bS47A4S0G0S3S1SbU1cS31A4S0G0S3S1SbU1dSaZ1A1A4S0G0S3S1SbU1eS3eA4S0G0S3S1SbU1fS2bA4S2G0A1A3A3A3A3A3A3A3A3A3A3A3").

Definition Kcm : axst := ltac2:(tb__ "0|3|
S2dSc7S4S5S1SbA2M0S37S0G0S3S1SbUcSfS21S33SeP96A1M1A3A4S0G0S3S1SbUeG1A4S0G0S3S1SbU10S4bA4S2G0A1A3A3A3A3S3cS2eS2cSaZ0A1A1S2ScA1M2G2G2S32A5S57A5").

Definition nw_facts : list sprop := ltac2:(tb__ "0|2|
S0SdS17SfS21SeP98A1M0S1aS24SeP99A1M1SaZ3A1A3A3S39A2S0SdS11SaZ1A1G1A2S0SdS11G1S2bA2S0SdS11G0SaSa3Z2Z16A2A1A2S2SdA1A3A3A3A3").
Definition Knw : axst := ltac2:(tb__ "0|2|
S2dScdS4S5S1SbA2M0S37S0G0S3S1SbUeSeP98A1A4S0G0S3S1SbU10SeP99A1A4S2G0A1A3A3A3S3cS2eS2cSaZ0A1A1S2ScA1M1G1G1S32A5S5dA5").

Definition Knw2 : axst := ltac2:(tb__ "0|7|
S2dSceS4S5S1SbA2M0S37S0G0S3S1SbUeSfS21SeP98A1M1SaZ3A1M2A3A4S0G0S3S1SbU10SfS21SeP99A1SaN1A1A3A4S0G0S3S1SbU11SeP9aA1M3A4S0G0S3S1SbUcSfS21S33SfS22SfS21G1SaZ2M4A1M5A3G5A3A3A4S2G0A1A3A3A3A3A3S3cS2eS2cSaZ0A1A1S2ScA1M6G6G6S32A5S4SdS5dS0SdS11SfS21G3G2A3S39A2S0SdS11G3SaSa3G4Z16A2A1A2S2SdA1A3A3A3A5").

Definition ext_regs : list (nat * sv) := ltac2:(tb__ "0|1|
S4S5S1SbA2M0S37S0G0S3S1SbUcSeP98A1A4S0G0S3S1SbUeSeP99A1A4S2G0A1A3A3A3").
Definition ext_facts : list sprop := ltac2:(tb__ "0|4|
S0SdS17SfS21SeP98A1M0S1aS24SeP99A1M1SaZ3A1A3A3SfS21S39SaZ2M2A1M3A3A2S0SdS11SaZ1A1G1A2S0SdS11G1S2bA2S0SdS11G3G0A2S0SdS11G0SaSa3G2Z16A2A1A2S2SdA1A3A3A3A3A3").
Definition Kext : axst := ltac2:(tb__ "0|1|
S2dScbS42S2S5S1SbA2A1S2eS2cSaZ0A1A1S2ScA1M0G0G0S32A5S41A5").
Definition Ke1 : axst := ltac2:(tb__ "0|3|
S2dSc8S4S5S1SbA2M0S42S0G0S3S1SbUbSfS22SfS21SeP98A1SaN1A1A3SaZ20A1A3A4S2G0A1M1A3A3G1S2eS2cSaZ0A1A1S2ScA1M2G2G2S32A5S41A5").
Definition Ke2 : axst := ltac2:(tb__ "0|3|
S2dSc9S4S5S1SbA2M0S42S0G0S3S1SbUbSfS22SeP98A1SaZ20A1A3A4S2G0A1M1A3A3G1S2eS2cSaZ0A1A1S2ScA1M2G2G2S32A5S41A5").
Definition Ke3 : axst := ltac2:(tb__ "0|1|
S2dScaS42S2S5S1SbA2A1S2eS2cSaZ0A1A1S2ScA1M0G0G0S32A5S41A5").

Definition Kproj : axst := ltac2:(tb__ "0|c|
S2dScfS4S5S1SbA2M0S37S0G0S3S1SbU10SeP9aA1M1A4S0G0S3S1SbUeSfS21SaZ1M2A1M3SeP9cM4A1M5A3A4S0G0S3S1SbU1aSeP99A1M6A4S2G0A1M7A3A3A3A3G7S2eS2cSaZ0A1A1S2ScA1M8G8G8S32A5S0SdS17SfS21G1S1aS24G6SaZ3A1A3A3SfS21S39SaZ2M9A1MaA3A2S0SdS17SfS21G5SfS22G6G3A3A3SfS22S2bG3A3A2S0SdS11G3G6A2S0SdS11G6S2bA2S0SdS16G4G2A2S0SdS11GaG1A2S0SdS11G1SaSa3G9Z16A2A1MbA2S0SdS11G5GbA2S2SdA1A3A3A3A3A3A3A3A3A5").

Definition Kbbp : axst := ltac2:(tb__ "0|14|
S2dSc5S4S5S1SbA2M0S37S0G0S3S1SbUeSeP98A1M1A4S0G0S3S1SbU10SeP9aA1M2A4S0G0S3S1SbU11SfS21SaZ1M3A1M4SeP9cM5A1M6A3A4S0G0S3S1SbU1aSeP99A1M7A4S2G0A1M8A3A3A3A3A3G8S2eS2cSaZ0A1A1S2ScA1M9G9G9S32A5S0SdS17SfS21G6SfS22G7G4A3A3SfS22S2bG4A3MaA2S0SdS11S1aS24G6SaZ3A1A3MbSfS22G1G4A3McA2S0SdS11GcSfS21GbSaZ2MdA1MeA3MfA2S0SdS11GfSfS22G2G4A3M10A2S0SdS11G10SfS21GbSaZ4A1A3A2S0SdS11SfS21G6GeA3GaA2S0SdS11G4G7A2S0SdS11G7S2bA2S0SdS16G5G3A2S0SdS11G6SaSa3GdZ15A2A1A2S0SdS11SfS21G1G7A3SfS21SfS21G6S2bA3M11G4A3M12A2S0SdS11G1G12A2S0SdS11SfS21G2G7A3SfS21G11GeA3M13A2S0SdS11G2G13A2S2SdA1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A5").

Definition K708 : axst := ltac2:(tb__ "0|3|
S2dSbcS4S5S1SbA2M0S37S0G0S3S1SbU1aSeP9dA1A4S2G0A1M1A3A3G1S2eS2cSaZ0A1A1S2ScA1M2G2G2S32A5S2SdA1A5").

Definition loc_cells0b : list cell := ltac2:(tb__ "0|1|
S0ScS10SaNf8A1Z8M0S30A3S0ScS10SaN108A1G0S4eZ4A1A3S0ScS10SaN110A1G0SaZ1A1A3S2ScA1A3A3A3").
Definition stk3 : list cell := ltac2:(tb__ "0|0|
S4ScS5bS4ScS50S5aA3A3").
Definition kcell (k : Z) : list cell := ltac2:(tb__ "0|0|
S0ScS10SaNa0A1Z4SaVk;A1A3S2ScA1A3").
Definition F3 : sprop := ltac2:(tb__ "0|0|
S18S15S2aS2bSaZ3A1A3A1").
Definition F4 : sprop := ltac2:(tb__ "0|0|
S15S23S2bSaZ4A1A3").

Definition xr3 : list (nat * sv) := ltac2:(tb__ "0|2|
S0S5S1SbA2M0S3S1SbU16SfS21SePdA1M1SaZ10A1A3A4S0G0S3S1SbU19SfS21G1SaZcA1A3A4S2G0A1A3A3").

Definition out3 : list cell := ltac2:(tb__ "0|2|
S0ScS10SaZ0A1M0Z4M1G0A3S0ScS10SaG1A1G1SaZ1A1A3S0ScS10SaZ8A1G1SaZ2A1A3S2ScA1A3A3A3").
Definition K830 : axst := ltac2:(tb__ "0|3|
S2dSbdS4S5S1SbA2M0S46S0G0S3S1SbU1aSeP9dA1A4S2G0A1M1A3A3G1S2eS2cSaZ0A1A1S2ScA1M2S95G2S9dA5S0SdS6bS2SdA1A3A5").

Definition pstk_np : list cell := removelast pstk_cells.
Definition pobjsN (dout : odefault) (ptsc outc p2dc : list cell) (stk : list cell) : list sobj := ltac2:(tb__ "0|0|
S3aVdout;S13S13Vptsc;Voutc;Vp2dc;S4ScVstk;S63A3S4dA8").
Definition loc_cellsT : list cell := ltac2:(tb__ "0|3|
S0ScS10SaN168A1Z8M0SaZ0M1A1A3S0ScS10SaN150A1G0S31A3S0ScS10SaN148A1G0S35A3S0ScS10SaN138A1G0S2fZ1A1M2A3S0ScS10SaN130A1G0G2A3S0ScS10SaN128A1G0S2fG1A1A3S0ScS10SaN120A1G0SfS21SePdA1SaG0A1A3A3S0ScS10SaN118A1G0S2fZ2A1A3S2ScA1A3A3A3A3A3A3A3A3").
Definition stkT : list cell := ltac2:(tb__ "0|0|
S4ScS94S4ScS50S5aA3A3").
Definition stk4 (k : Z) : list cell := ltac2:(tb__ "0|1|
S4ScS93Vk;A1S4ScS0ScS10SaN170A1Z8M0SeP9dA1A3S0ScS10SaN140A1G0S3eA3S2ScA1A3A3S66A3A3").

Definition regs4 : list (nat * sv) := ltac2:(tb__ "0|1|
S4S5S1SbA2M0S46S0G0S3S1SbUcS3eA4S0G0S3S1SbUdSePa2A1A4S2G0A1A3A3A3").
Definition Kaa4 : axst := ltac2:(tb__ "0|2|
S2dSbeS64S2S5S1SbA2A1S36S2cSaZ0M0A1A1S2ScA1M1G1G1S3bG0A1A5S0SdS38S2SdA1A3A5").
Definition Kb08 : axst := ltac2:(tb__ "0|4|
S2dSbfS4S5S1SbA2M0S64S0G0S3S1SbUeSePa3A1A4S2G0A1M1A3A3G1S36S2cSaZ0M2A1A1S2ScA1M3G3G3S3bG2A1A5S0SdS38S2SdA1A3A5").

Definition regs4e : list (nat * sv) := ltac2:(tb__ "0|1|
S4S5S1SbA2M0S46S0G0S3S1SbU1bSePa1A1A4S2G0A1A3A3").
Definition Kb14 : axst := ltac2:(tb__ "0|2|
S2dSc0S45S2S5S1SbA2A1S36S2cSaZ0M0A1A1S2ScA1M1G1G1S3bG0A1A5S0SdS38S2SdA1A3A5").
Definition Kd10 : axst := ltac2:(tb__ "0|2|
S2dSc2S45S2S5S1SbA2A1S36S2cSaZ0M0A1A1S2ScA1M1G1G1S3bG0A1A5S0SdS38S2SdA1A3A5").

Definition Kb64 : axst := ltac2:(tb__ "0|4|
S2dSc1S4S5S1SbA2M0S45S0G0S3S1SbU1aS31A4S2G0A1M1A3A3G1S36S2cSaZ1M2A1A1S2ScA1M3G3G3S3bG2A1A5S0SdS38S2SdA1A3A5").
Definition Kd60 : axst := ltac2:(tb__ "0|4|
S2dSc3S4S5S1SbA2M0S45S0G0S3S1SbU1aS31A4S2G0A1M1A3A3G1S36S2cSaZ1M2A1A1S2ScA1M3G3G3S3bG2A1A5S0SdS38S2SdA1A3A5").

Definition Ktail : axst := ltac2:(tb__ "0|5|
S2dSc4S4S5S1SbA2M0S46S0G0S3S1SbUaSfS21SePdA1SaZ8A1A3A4S0G0S3S1SbUbS2fZ0A1A4S0G0S3S1SbUcS2fZ2A1A4S0G0S3S1SbUdS2fZ1M1A1M2A4S0G0S3S1SbUeG2A4S0G0S3S1SbUfSaG1A1A4S0G0S3S1SbU1bSePa1A1A4S2G0A1M3A3A3A3A3A3A3A3A3G3S36S2cS35A1S2ScA1M4G4G4S66A5S2SdA1A5").

Definition C_b6cK : axst := ltac2:(tb__ "0|3|
S2dSbaS0S5S1SbA2M0S3S1SbU1bSePa1A1A4S2G0A1M1A3G1S3aS2cS35A1S13S13S2ScA1M2G2G2S63S65A8S2SdA1A5").

Definition cutpcs_pg : list Z := ltac2:(tb__ "0|0|
S0S9fSd7S0S9fSd1S0S9fSd2S0S9fSccS0S9fSd4S0S9fSc7S0S9fScdS0S9fSceS0S9fScbS0S9fSc8S0S9fSc9S0S9fScaS0S9fSc5S0S9fScfS0S9fSbcS0S9fSbdS0S9fSbeS0S9fSbfS0S9fSc0S0S9fSc2S0S9fSc1S0S9fSc3S0S9fSc4S0S9fSd5S0S9fSd3S0S9fSd6S0S9fSbbS0S9fSbaS0S9fSc6S2S9fA1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").

Definition hcuts_pg : list axst := ltac2:(tb__ "0|0|
S0Sa1S7dS0Sa1S69S0Sa1S67S0Sa1S76S0Sa1S7eS0Sa1S7fS0Sa1S7cS0Sa1S79S0Sa1S7aS0Sa1S7bS0Sa1S80S0Sa1S75S0Sa1S6fS0Sa1S70S0Sa1S71S0Sa1S72S0Sa1S73S0Sa1S77S0Sa1S74S0Sa1S78S0Sa1S81S0Sa1S68S2Sa1A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
