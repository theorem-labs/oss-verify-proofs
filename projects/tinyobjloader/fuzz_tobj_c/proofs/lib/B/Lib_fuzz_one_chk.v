(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Init.Datatypes"; "bool"; "true"; "nil"; "false"; "app"; "prod"; "cons"; "list"; "fst"; "pair"; "snd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SLit"; "sprop"; "SVar"; "sprop_eqb"; "SPUle"; "sv_eqb"; "sobj"; "ss_objs"; "valuation"; "DUnknown"; "SPAlign"; "SPBranch"; "SPEq"; "SPNot"; "cell"; "ob_base"; "ob_hi"; "ob_lo"; "ss_facts"; "ss_next"; "sv_below"; "swf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_fuzz_one"; "Fx"; "fr_fz"; "nx"; "s_lo"; "E_lo"; "pF"; "vF"; "E_sm0"; "T_sm1"; "gF"; "X_rel"; "pH"; "C_pro0"; "X_al"; "Xk_lo"; "C0"; "C_ms1"; "E_ms"; "L_alF"; "L_sm"; "Pre_sm"; "R_lo"; "R_sm"; "objs_rel"; "objs_sm1"; "pAR"; "pFL"; "s_al"; "s_sm"; "vCFG"; "vFL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "nd_below"; "nd_am"; "nd_bd"; "nd_tv"; "am_subst"; "NDA"; "nd_fr"; "ndesc"; "AHeadN"; "ANone"; "am_eqb"; "amode"; "fr_sub_eqb"; "AHead"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "bitem"; "bd_subst"; "KU"; "bd_below"; "BIc"; "bd_wpos"; "bud_le"; "bud_pay"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_fuzz_one_eqs"; "tvA"; "KU1"; "nd_e"; "nd_fa"; "gp"; "nd_CL"; "nd_p"; "nd_A2"; "nd_B2"; "ndT"; "nd_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_fuzz_one_chk"; "ent_chk"; "extraFZ"; "xextraFZ"; "isub_err"; "isub_ok"; "PDk_lo"; "ndA1p"; "@Stdlib.Lists.List"; "existsb"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "add"; "ltb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_X"; "ax_S"; "ax_base"; "has_facts"; "axst"; "entailsA"; "g8"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "wsub_id_below"; "sv_subst"; "wsub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nk.Lib_fuzz_iface"; "bd_fz"; "nd_fz0"; "vDAT"; "vLEN"; "nd_fz1"; "fz_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_fuzz_one_ad"; "vG"; "X_A1"; "X_B"; "E_fa"; "E_fd"; "C_L"; "K_fa"; "L_L3"; "s_L3"; "vNx"; "L_L1"; "L_sxE"; "L_sxK"; "R_fa"; "R_fd"; "X_A"; "X_fa0"; "X_fa1"; "gA"; "nB"; "s_L1"; "s_fa0"; "s_fa1"; "vNd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_fuzz_one_chk.K2"; "xrs_chkC"; "robjs_chkC"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_fuzz_one_chk.HK"; "robjs_chkR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_fuzz_one_epi"; "K_sx3"; "K_sx"; "K_sx2"; "X_fin"; "X_rl1"; "s_fin"; "s_sxE"; "s_sxK"; "@Stdlib.ZArith.BinInt.Z"; "sub"; "pow"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_fuzz_one.LD"; "Pre_lo"; "NP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_fuzz_one.LI"; "nd_lo0"; "nd_lo_err"; "nd_lo_ok"; "P_err"; "P_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "import_subA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "tv_sub_eqb"; "import_tv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAF"; "xrs47_chk"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "SHADOW_OFF"; "fs_frame_size"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC"; "pdescA"; "pd_okA"; "xrs_inclb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p4.TobjJAD"; "two52";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR"; "e32"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@LinuxProcessSemantics.Riscv.Instr"; "BC_EQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ny.Lib_builder_pf"; "frameF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_fuzz_iface2"; "P_fz"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_fuzz_one_glue"; "al_facts"; "vDN"; "vG10"; "vH"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS"; "frame_open_stateA"; "shobj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "V_FLAG"; "V_RES"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymCFG SymSummary SymObj SymFrame.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA EntailA CFGA GlueA SummaryA SummaryA2 MemoFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv ObjXform ObjUnbase TobjJV.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require Import BudA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import CfgGenTA SummaryA3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJAR TobjJAS TobjJAT TobjJAF.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAT OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p4.TobjJAD.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_load_obj_armkit2 Lib_load_obj_hvkit.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ny.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Lib_fuzz_iface2 Lib_fuzz_one_glue Lib_fuzz_one Lib_fuzz_one_ad Lib_fuzz_one_epi Lib_fuzz_one_eqs.
Import ListNotations. Close Scope bv_scope. Open Scope Z_scope. Import FZAddr.
Module K2. Include Lib_load_obj_armkit2. End K2. Module HK. Include Lib_load_obj_hvkit. End HK.

Definition extraFZ (o : sobj) : bool := ltac2:(tb__ "0|1|
S2S2L_;M0S13S1dVo;A1S7eA2G0S13S1fVo;A1SeZ0A1A2S13S1eVo;A1S7fA2S5X2x2S5X2x2").
Definition xextraFZ (r : sv * sv) : bool := ltac2:(tb__ "0|0|
S2S2L_;S13SaSdSdVr;A3S7eA2S13ScSdSdVr;A3S7fA2S5X2x2").

Definition ent_chk (L T : axst) (s : wsub) (ndi ndj : ndesc) : bool := ltac2:(tb__ "0|2|
S2S2L_;M0S76VL;VT;Vs;A3G0S79Vs;S6dA2G0S6eS6dS26VL;A1M1A2G0S43G1Vndi;A2G0SafVs;S46Vndi;A1S46Vndj;A1A3G0S4fVs;S49Vndi;A1S49Vndj;A1A3G0S57S24VL;A1S52Vs;S45Vndj;A1A2S45Vndi;A1A3S4dS47Vs;S44Vndj;A1A2S44Vndi;A1A2S5X2x2S5X2x2S5X2x2S5X2x2S5X2x2S5X2x2S5X2x2").
Lemma ent_chk_unf : ltac2:(tb__ "0|2|
S75S75S7bS4aS4aS0S2S64R5R4R3R2R1A5S3A3S1S0S2S76R6R5R4A3S3A3S1S0S2S79R4S6dA2S3A3S1S0S2S6eS6dS21S72R6A1M0A1M1A2S3A3S1S0S2S43G1R3A2S3A3S1S0S2SafR4S46R3A1S46R2A1A3S3A3S1S0S2S4fR4S49R3A1S49R2A1A3S3A3S1S0S2S57S20G0A1S52R4S45R2A1A2S45R3A1A3S3A3S0S2S4dS47R4S44R2A1A2S44R3A1A2S3A3A2A2A2A2A2A2A2F_;Fndj;Fndi;Fs;FT;FL;").
Proof.
  intros L T s ndi ndj H. unfold ent_chk in H.
  apply lazy_andb_prop in H as [H1 H]. apply lazy_andb_prop in H as [H2 H]. apply lazy_andb_prop in H as [H3 H]. apply lazy_andb_prop in H as [H4 H].
  apply lazy_andb_prop in H as [H5 H]. apply lazy_andb_prop in H as [H6 H]. apply lazy_andb_prop in H as [H7 H8]. repeat split; assumption.
Qed.

Lemma fz_chk_al : ltac2:(tb__ "0|0|
S0S2S64S36S33S3fS7dS7dA5S3A3").
Proof. vmc1. Qed.

Lemma fz_chk_sm : ltac2:(tb__ "0|7|
S1S0S2S9bS24S2bA1M0S4S7SdSdA2M1A1M2S4S7S7SdSb9A2SdA2A1M3S65S3aA5S3A3S1S0S2S9aG0G2G3S66S71S2bA1A5S3A3S1S0S2S43S26S2bA1M4S7dA2S3A3S1S0S2S56S7cA1S3A3S1S0SdS78SaeS40S38S37S2bA4M5Sc5A2S2aA3S1S0S2S6eG4S29A2S3A3S1S0SdS78G5Sc4A2S42A3S1S0S2S6eG4S3eA2S3A3S1S0SdS73S2cA1SeSb2A1A3S1S0S2S23S72Sc2S2cS3cS6G1S31G2A3S29Sb3Z2A1A5A1A1S3A3S1S0S2S6eS6dS26S2cA1M6A2S3A3S1S0S2S43G6S5fA2S3A3S1S0S2S9aS24S2cA1G2G3S66S31A5S3A3S1S0S2S6bSfS11S18S29Z5A2A1S24S30A1A3S3A3S0S2S70S29S26S30A1A2S3A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. conj_vmc. Qed.

Lemma fz_chk_rel : ltac2:(tb__ "0|2|
S1S0SdS73S2eA1SeSb2A1A3S1S0S2S74S8SfS1aS77S2dA1S2aA2S8SfS12S10S2dA1SeSa5Sa6Z2Z3dA2Z1A2A1A2S4SfA1A3A3S24S2eA1M0A2S3A3S1S0S2S43S26S2eA1S5fA2S3A3S1S0S2S9cG0S4S7SdSdA2A1S25S65S3bA5S3A3S1S0S2S6bSfS11S12S2aSeSa5Z7fffff800000Z100A2A1A2A1S24S34A1A3S3A3S1S0S2S43S26S35A1M1S5fA2S3A3S0S2S54G1S7cA2S3A3A2A2A2A2A2A2").
Proof. conj_vmc. Qed.

Definition PDk_lo : list pdescK := liftPD LI.PD_lo.
Definition isub_err : wsub := ltac2:(tb__ "0|0|
SaeS27Sa7SacS28A4").
Definition isub_ok : wsub := ltac2:(tb__ "0|0|
SaeS27Sa7SadS28A4").
Lemma fz_chk_lo : ltac2:(tb__ "0|9|
S1S0S2S9bS24S28A1M0S4S7SdSdA2M1A1M2S25S65S39A5S3A3S1S0S2S9aG0G2S25S66S32A5S3A3S1S0S2Sb6S32S71S28A1A2S3A3S1S0S2S43S26S28A1M3S48S6G1G2G2A3S25S7cS4cA4A2S3A3S1S0S2S54G3S4S51A1M4A2S3A3S1S0S2SafS27G2S46Sa9A1A3S3A3S1S0S2S4dS47S27S44Sa9A1A2S4cA2S3A3S1S0S9S51A1M5S6S51S52S27S45Sa9A1A2G4A3S7cA3S1S0S2S56S7cA1S3A3S1S0S2S6cS7Sb4S16S16OF_;F_;M6A2M7G7Sb5Sa7Sa8S27G3SaSb4G6R1A3A5Ld;S69A3S3A3S1S0SdS78S27PdA2S7eA3S1S0SdS78S27PeA2S7fA3S1S0SdS78S27PfA2S41A3S1S0SdS78S27P1cA2S10PaA1A3S1S0S2S6bSfS11S12S2aSeSa5Z7fffff800000Z100A2A1A2A1G0A3S3A3S1S0S2S74S81G0A2S3A3S1S0S2S74SbeSc1SbfSc0A3G0A2S3A3S1S0S9G1A1M8S6G1G2Sb0S67S46SaaA1A2A3G2A3S1S0G5S6S51S52S67S45SaaA1A2G4A3G4A3S1S0S4eS47S67S44SaaA1A2S4cA3S1S0G8S6G1G2Sb0S68S46SabA1A2A3S59A3S1S0G5S6S51S52S68S45SabA1A2G4A3S5aA3S0S4eS47S68S44SabA1A2S50S2fS5A2A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. conj_vmc. Qed.

Definition ndA1p : ndesc := ltac2:(tb__ "0|0|
S48S59S25S5aS4bS2fS94A2A4").
Lemma fz_chk_loop : ltac2:(tb__ "0|e|
S1S0S2S64S92S88S97S5cS5cA5S3A3S1S0S2S64S93S88S98S5cS5cA5S3A3S1S0S2S64S8cS87S96S60S5eA5S3A3S1S0S2S64S89S87S8aS61S5eA5S3A3S1S0S2S6eS6dS26S91A1M0A2S3A3S1S0S2S43G0S63A2S3A3S1S0S2S6eS6dS26S83A1M1A2S3A3S1S0S2S43G1S6aA2S3A3S1S0S2S9cS24S83A1M2S59S25S65S15S72S83A1A1A5S3A3S1S0S2Sb1G2S59S71S83A1A3S3A3S1S0S4aS48S8S7SdSdA2M3SbSdSdS2fSb8S10S6fG1P1M4A2A1A1A4S59A3S25S6S51S5aS8S51S55Z0Z1S53A3S4S51A1A3A3M5S4bS10G1A1S10S6fG1P3M6A2A1A2A4S60A3S1S0S2S6eS6dS26S84A1M7A2S3A3S1S0S2S43G7S62S8bS82A2A2S3A3S1S0S2S9cS24S84A1M8S59S25S65S15S72S84A1A1A5S3A3S1S0S2Sb1G8S59S71S84A1A3S3A3S1S0S4aS48S8G3SbSdSdS8bSb8S10S6fG7G4A2A1A1A4S59A3S25G5S4bS10G7A1S10S6fG7G6A2M9A1A2A4S61A3S1S0SbaG9S6fS95G6A2MaA3S1S0S2S6bSfS11S12S82SeSb7A1MbA2A1G8A3S3A3S1S0S2S6bSfS11S12S10GaA1McGbA2A1S24S89A1A3S3A3S0SdS7aS8aS5dS82Z8MdA2A2S5dGcGdA2A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. conj_vmc. Qed.

Lemma fz_chk_fd : ltac2:(tb__ "0|4|
S1S0S2S9bS24S86A1M0S59S25S65S90A5S3A3S1S0S2S9aG0S59S25S66S71S86A1A5S3A3S1S0S2S6bSfS11S1bS19SbbS99SeZ0M1A1M2A3A1A1G0A3S3A3S1S0S2S58G0G2S53S6S51S5aS8S51S55G1Z1S53A3S4S51A1A3A3S5aA5S3A3S1S0S2S54S26S86A1M3S5aA2S3A3S1S0S2S43G3S5eA2S3A3S1S0S2S6bSfS11S12S82SeSb7A1A2A1G0A3S3A3S0S2S22G3S5dS82Z6A2A2S3A3A2A2A2A2A2A2A2").
Proof. conj_vmc. Qed.

Lemma fz_chk_fa : ltac2:(tb__ "0|2|
S1S0S2S9bS24S85A1M0S4S7SdSdA2A1M1S25S65S8fA5S3A3S1S0S2S9aG0G1S25S66S71S85A1A5S3A3S1S0S2S6bSfS11S12SeZ1000A1S3dA2A1G0A3S3A3S1S0S2S58G0SeZ0A1S53S5aS4S51A1A5S3A3S0S2S43S26S85A1S5cA2S3A3A2A2A2A2").
Proof. conj_vmc. Qed.

Lemma fz_chk_sx : ltac2:(tb__ "0|5|
S1S0S2S64S8dS9eSa3S5bS5bA5S3A3S1S0S2S64S8eS9eSa4S5bS5bA5S3A3S1S0S2S6bSfS11S12S2aSeSa5Z7fffff800000Z100M0A2A1A2A1S24S9eA1A3S3A3S1S0S2S9cS24S9fA1M1S4S7SdSdA2A1M2S25S65S15S72S9fA1A1M3A5S3A3S1S0S2SbcS2dS29G0G1A4S3A3S1S0S2Sb1S24S9dA1M4G2S71S9dA1A3S3A3S1S0SdS73S9dA1SeSb2A1A3S1S0S9S14A1S15S72S9dA1A1S6S14G3S8S14Sc3S2dZ0Z20S4S1cA1S17A5S4S14A1A3A3A3S0S9SfA1G4G1A3A2A2A2A2A2A2A2A2").
Proof. conj_vmc. Qed.

Lemma fz_chk_rl : ltac2:(tb__ "0|0|
S1S0S2S43S26Sa1A1S5bA2S3A3S0S2S64Sa0SbdSa2S80S80A5S3A3A2").
Proof. conj_vmc. Qed.
