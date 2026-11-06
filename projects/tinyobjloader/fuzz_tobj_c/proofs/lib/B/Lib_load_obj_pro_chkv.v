(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_setS"; "ax_X"; "@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Init.Datatypes"; "bool"; "true"; "andb"; "Some"; "option"; "cons"; "nil"; "S"; "false"; "list"; "nat"; "orb"; "prod"; "@Corelib.Lists.ListDef"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_defs"; "BAD"; "Pre_ms"; "L_ms"; "NP"; "bslot"; "vF"; "z24"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv_eqb"; "sobj"; "sv"; "SLit"; "sprop"; "sprop_eqb"; "sstate"; "SVar"; "ob_base"; "ob_hi"; "ob_lo"; "obj_wf"; "ss_objs"; "swf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "axform"; "AXRebase"; "@Stdlib.ZArith.BinInt.Z"; "leb"; "add"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_pro"; "fr_lo"; "ax_tidy"; "blkAR"; "vs_E"; "vs_R"; "vs_T"; "vs_b"; "vs_off"; "vs_s"; "vsn"; "vstep"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_pro_eqs"; "Fx"; "nx"; "bd_pro"; "bk_xf3"; "bk_xf4"; "bk_xf5"; "cv_i"; "cv_xf"; "nd_r2"; "vl"; "@Stdlib.Lists.List"; "existsb"; "nth_error"; "@Corelib.Init.Peano"; "lt"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_lglue"; "extraLO"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_pro_chk"; "fUle"; "wr_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_pro_chkv.K2"; "robjs_chkC"; "xextraLO"; "xrs_chkC"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_pro_chkv"; "VB1"; "VB2"; "VB3"; "VB4"; "VB5"; "VC1"; "VT0"; "pc_chk"; "rng_chk"; "spLo"; "vstep_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkPA"; "entails_frA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase"; "reshape_obj_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "bd_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.ObjZeroA"; "zero_cells_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "nd_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM"; "T_afterA"; "call_checkTA"; "@Stdlib.PArith.BinPos.Pos"; "leb"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAT OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p4.TobjJAD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.ObjZeroA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code Asan_set_shadow_iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_scan_double Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_builderH_defs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Asan_set_shadow_iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n8.Asan_memcpy48_iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Lib_load_obj_defs Lib_load_obj_pro Lib_load_obj_lglue Lib_load_obj_pro_eqs Lib_load_obj_pro_chk.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_load_obj_armkit2 Lib_load_obj_hvkit.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ny.
Import ListNotations. Close Scope bv_scope. Open Scope Z_scope. Import ScanDoubleAddr LOAddr.
Module K2. Include Lib_load_obj_armkit2. End K2. Module HK. Include Lib_load_obj_hvkit. End HK.

Definition VC1 : list axst := Eval vm_compute in map (fun j => cv_1 (vl j) (vs_b (vsn j)) (vs_off (vsn j)) 24) (seq 0 1).
Definition VT0 : list axst := Eval vm_compute in map (fun j => T_afterA Pre_ms (vs_E (vsn j)) (vs_s (vsn j)) (vs_R (vsn j)) L_ms) (seq 0 1).
Definition VB1 : list axst := Eval vm_compute in map bk_1 VT0.
Definition VB2 : list axst := Eval vm_compute in map bk_2 VB1.
Definition VB3 : list axst := Eval vm_compute in map (fun j => bk_3 (nth j VB2 BAD) (vs_b (vsn j)) (vs_off (vsn j))) (seq 0 1).
Definition VB4 : list axst := Eval vm_compute in map (fun j => bk_4 (nth j VB3 BAD) (vs_b (vsn j)) (vs_off (vsn j))) (seq 0 1).
Definition VB5 : list axst := Eval vm_compute in map bk_5 VB4.

Definition spLo : sprop := SPUle (SLit 140735332483072) (SVar 10).
Definition rng_chk (A : axst) (b : sv) (off : Z) : bool := ltac2:(tb__ "0|2|
S11S8S8S8S1bVb;S19A2S43S1fS20S48A1S39VA;A1M0A3A2S2cZ0M1Voff;A2A2S2cVoff;Z800A2A2S8S8S8S1bVb;S22PaA1A2S43S1fS20S56A1G0A3A2S2cN1000Voff;A2A2S2cVoff;G1A2A2A2").
Definition pc_chk (A : axst) (i : nat) (b : sv) (off n : Z) : bool := ltac2:(tb__ "0|0|
SaS1cA1S6Lx;S44S1cS27S1VA;A1A1Vi;A3S1cS8S8S1bS23R1A1Vb;A2S1bS25R1A1S1eVoff;A1A2A2S1bS24R1A1S1eS2dVoff;Vn;A2A1A2A2Lo;SeXax2").

Definition vstep_ok (j : nat) : Prop := ltac2:(tb__ "0|b|
S37Vj;A1S38S42Vj;A1S0S34R2A1S1dS35R3A1S46S31R4A1S0S36R5A1S58S32R6A1SfS1cA1M0S13S0Vj;S52S14A4S0S13S0Vj;S53S14A4S0S13S0Vj;S4dS14A4S0S13S0Vj;S4eS14A4S0S13S0Vj;S4fS14A4S0S13S0Vj;S50S14A4S0S13S0Vj;S51S14A4S0S5S4SaS0A1M1S29RdS40RdRcRbZ18M2A4A2S9S0R7A2A3S5S4S6S49R7SdS3fRdRcRbA3A1M3A2S7A3S5S4S6S26S3aR7A1S18RcRbG2A3M4A2S7A3S5S4S6S54R7G3RcRbG2A5S7A3S5S4S6S55R7RcRbA3S7A3S5S4S0S2R7S5bS1R7A1G3G4A3A2RaA3S5S4SaG0A1S5aRaS15R9A3S9G0R8A2A3S5S4S6S59RaS15R9R8SbS0S16ScS0A1A3A5S7A3S5S4S6S60S17R9A2S7A3S5S4S6S61S17S3aRaA1M5A2S7A3S5S4S6S5eG5S41A2S7A3S5S4S6S5cG5S3bA2S7A3S5S4S6S4aS39RaA1M6SbS12S1dS1dA2M7S30ScG7A1A3M8S2eS47R8A5S7A3S5S4S6S4cG6G8S2eS4bS3RaA1A5S7A3S5S4S0S5fS15RaR9R8S16A5R6A3S5S4SaS21A1S5dS1R6A1U1M9S1aA3S9S21S1R5A1MaA2A3S5S4S6S28GaA1S7A3S5S4S0S2R6GaA2R5A3S5S4G1S29R5SbS2aS2bG9A1ScS2aA1A3A2S9S0R4A2A3S5S4G1S29R4S3cR4RcRbA3A2S9S0R3A2A3S5S4G1S29R3S3dR3RcRbA3A2S9S0R2A2A3S5S4G1S29R2S3eR2A1A2S9S0R1A2A3S4S0S2fR1A1S33ReA1A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2TB5;TB4;TB3;TB2;TB1;TT0;TC1;TR;Ts;TE;Toff;Tb;TL;Tv;").
Lemma vq_0 : vstep_ok 0. Proof. unfold vstep_ok. conj_vmc. Qed.
Lemma vq_all : ltac2:(tb__ "0|0|
S10S45R1U1A2S57R2A1F_;Fj;").
Proof.
  intros j H.
  destruct j as [|j]; [exact vq_0|].
  lia.
Qed.
