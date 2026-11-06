(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "ex"; "not"; "@Corelib.Init.Datatypes"; "cons"; "true"; "bool"; "Some"; "app"; "nil"; "option"; "S"; "list"; "prod"; "length"; "nat"; "None"; "pair"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "apply_axforms"; "AXSplit"; "AXMerge"; "AXUnbase"; "AXSelect"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_setS"; "entailsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sstate"; "SLit"; "cell"; "swf"; "sv"; "rm"; "ss_next"; "sv_eqb"; "SVar"; "sobj"; "ss_objs"; "@Corelib.Numbers.BinNums"; "positive"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.ObjZeroA"; "zero_cells_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_defs"; "idxB"; "NP"; "optL"; "vF"; "sel2last"; "vLEN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_land"; "s_landA"; "s_landB"; "K1a"; "K1b"; "M_after0"; "M_bodyN"; "XR_after1"; "XR_body1"; "iD"; "splits_from"; "iK"; "rt_at"; "rt_drop"; "rt_news"; "bb_hi"; "fofs"; "iC"; "tv_site"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs"; "c1"; "c4"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_lglue"; "frL"; "tvL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "bitem"; "uval"; "BIc"; "bd_subst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "AHead"; "am_eqb"; "am_subst"; "fr_below"; "fr_sub_eqb"; "nd_bd"; "AK0"; "AV0"; "@Stdlib.Lists.List"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_land_chk"; "Rt_a1"; "Rt_b1"; "Za1_a1"; "Za1_b1"; "Za2_a1"; "Za2_b1"; "Za3_a1"; "Za3_b1"; "Za4_a1"; "Za4_b1"; "Zs1_a1"; "Zs1_b1"; "Zs2_a1"; "Zs2_b1"; "Zs3_a1"; "Zs3_b1"; "Zs4_a1"; "Zs4_b1"; "i1256_a1"; "i1256_b1"; "i480_a1"; "i480_b1"; "i880_a1"; "i880_b1"; "i96_a1"; "i96_b1"; "tvLand_a1"; "tvLand_b1"; "C10_a1"; "C10_b1"; "C11_a1"; "C11_b1"; "C12_a1"; "C12_b1"; "C13_a1"; "C13_b1"; "C9_a1"; "C9_b1"; "add_objs"; "add_objs_wf"; "nulls_a1"; "nulls_b1"; "tv1"; "PhiP0"; "XF_a1"; "XF_b1"; "bdLand_a1"; "bdLand_b1"; "unb_list"; "@Corelib.Lists.ListDef"; "map"; "seq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_bud"; "ndA1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_loop"; "datasA"; "pH"; "vsP"; "X_bodyN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_pro"; "vARn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve"; "c8"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "tv_below"; "tv_sub_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVAy"; "null_entry"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p0.ObjRetileB"; "retile_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAG"; "tv_permb"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "of_nat"; "@Corelib.Init.Nat"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_rom_defs"; "decodes"; "lines_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs"; "kb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_exits"; "K_after0"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "lt"; "mul"; "of_nat";
"@stdpp.bitvector.definitions"; "Z_to_bv"; "bv"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia Permutation.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymSummary SymObj ExampleMemcpy Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CFGA GlueA SummaryA SummaryA2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue TobjJV TobjJVAy TobjArena ObjXform ObjUnbase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TobjJVA InitState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require Import BudA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import CfgGenTA SummaryA3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAM2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJAR TobjJAS TobjJAF.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p4.TobjJAD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.CertGlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import ResidualA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.ObjZeroA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import DrvGlueC ObjEmptyA PinA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code Asan_set_shadow_iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_scan_double Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_builderH_defs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Asan_set_shadow_iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n8.Asan_memcpy48_iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import Lib_rom_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ng.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ny.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ns.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require oc.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o9.Lib_build_line_index_rom OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oc.Lib_build_line_index_rom_pf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Lib_load_obj_defs Lib_load_obj_pro Lib_load_obj_pro2 Lib_load_obj_loop Lib_load_obj_lglue Lib_load_obj_bud Lib_load_obj_exits Lib_load_obj_land.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p0.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p0.ObjRetileB.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Module BLR. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o9.Lib_build_line_index_rom. End BLR.
Module BLRP. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oc.Lib_build_line_index_rom_pf. End BLRP.
Import ScanDoubleAddr VRAddr RA.ReallocAddr LOAddr LOLAddr.

Definition PhiP0 (rho : valuation) : Prop := ltac2:(tb__ "0|2|
S28S1S9cS47Vrho;S38A2M0R1A2S9dR1S9bG0S9eZ10S47Vrho;S3aA2A2A2A2A2S3S0SaSa1Q8A1M1A1S21Vrho;Sa0Q40R2A2A2S10G1A1A3A1F_;Fz;").
Definition PhiP1 (rho : valuation) : Prop := ltac2:(tb__ "0|2|
S1S2ScSdS28S28A2M0A1M1G1S1S0S28S9fSeG0R1A2A1S47Vrho;S40A2A3S1S97S21Vrho;A1S47Vrho;S38A2R1A3S98R1S47Vrho;S2fA2A2A2A2LT;A2S7eVrho;A1A2").
Definition V_P : list positive := ltac2:(tb__ "0|0|
S4S27P1a8S4S27P1a9S4S27P1aaS4S27PeS9S27A1A3A3A3A3").
Lemma PhiP0_reads : phi_reads V_P PhiP0.
Proof.
  intros rho rho' HV _ HM H z Hz. rewrite <- HM. apply H.
  rewrite <- (uval_rw rho rho' 424 iD eq_refl ltac:(apply HV; cbn; tauto)), <- (uval_rw rho rho' 426 iK eq_refl ltac:(apply HV; cbn; tauto)). exact Hz.
Qed.
Lemma PhiP1_reads : phi_reads V_P PhiP1.
Proof.
  intros rho rho' HV HL HM [(T & H1 & H2 & H3) HD]. split; [exists T | exact (PhiP0_reads rho rho' HV HL HM HD)].
  rewrite (uval_rw rho rho' 425 iC eq_refl ltac:(apply HV; cbn; tauto)), (uval_rw rho rho' 424 iD eq_refl ltac:(apply HV; cbn; tauto)),
          (uval_rw rho rho' 14 vLEN eq_refl ltac:(apply HV; cbn; tauto)).
  split; [exact H1|]. split; [|exact H3]. eapply decodes_ext; [|exact H2]. intros z _. symmetry. apply HM.
Qed.

Definition tv1 : list (sv * sv) := ltac2:(tb__ "0|1|
S8SdS20S20A2M0S41S4G0S11S20S20S38S99Z10S3aA2A4S9G0A1A3A3").

Definition ENDOW : list bitem := ltac2:(tb__ "0|2|
S4S46S48Z1M0Z0M1S51A3S4S46S48G1G0S50A3S9S46A1A3A3").

Fixpoint unb_list (n : nat) (A : axst) : list axform :=
  match n with O => [] | S n' =>
    let i := find_idxb (fun o => sv_eqb (ob_base o) vF && match ob_lo o with SLit l => (448 <=? l) && (l <? 1752) | _ => false end) (ss_objs (ax_S A)) 0%nat in
    if (i <? length (ss_objs (ax_S A)))%nat then AXUnbase i 448 :: unb_list n' (optL (apply_axforms A [AXUnbase i 448])) else [] end.
Definition canon_xf (A0 : axst) : list axform := ltac2:(tb__ "0|8|
S39S2aVA0;S2dZ220A3S3fS3eA1A2ScS12A1M0S2cS13VA0;R1A2A1S18S39S2aR1S2dZ1c0A3S4S28Z1c8S4S28Z1e0S9S28A1M1A3A3A2G0S2cS13R2R1A2A1M2S18S39S2aR1S24PaA1M3N128A3S4S28N88M4S4S28N80M5S4S28N78G1A3A3A3A2G0G2S18S4S12S14S2aR1S2dZ0M6A3S1dZ20A1A2S9S12A1M7A3G0G2S18S83U2dR1A2G0G2S18S4S12S16S2aR1G3G4A3G4A2G7A3G0G2S18S4S12S16S2aR1G3G5A3G4A2G7A3G0G2S18S4S12S17S2eR1S2aR1S8bG6A3S2aR1S8bZ30A3A3A1G7A3G0G2S18S4S12S15S96SeS25S26S19R1A1A1A2U2A2A1G7A3G0S8S12R11S8S12RfS8S12RdS8S12RbS8S12R9S8S12R7S8S12R5S8S12R3R1A3A3A3A3A3A3A3A3Tx9;TA8;Tx8;TA7;Tx7;TA6;Tx6;TA5;Tx5;TA4;Tx4;TA3;Tx3;TA2;Tx2;TA1;Tx1;").

Definition zs1 (A : axst) (i : nat) (mid : Z) : axst := ltac2:(tb__ "0|0|
S2cS13VA;S4S12S14Vi;S1dVmid;A1A2S9S12A1A3A2A1").
Definition zs2 (A1 : axst) (j : nat) (cs : list cell) : sstate := ltac2:(tb__ "0|1|
SaS1cA1S1cLx;S29S19VA1;A1M0Vj;Vcs;A3S1cR1LSt;G0Xax2").

Fixpoint add_objs (A : axst) (ds : list sobj) : axst :=
  match ds with [] => A | o :: r => add_objs (ax_setS A (add_obj (ax_S A) o)) r end.
Fixpoint add_objs_wf (A : axst) (ds : list sobj) : bool :=
  match ds with [] => true | o :: r => swf (add_obj (ax_S A) o) && obj_wf (ss_next (ax_S A)) o && add_objs_wf (ax_setS A (add_obj (ax_S A) o)) r end.

Definition tvLand_b1 : list (sv * sv) := Eval vm_compute in map (xr_subst s_landB) tvL.
Definition nulls_b1 : list (sv * sv) := Eval vm_compute in firstn 18 tvLand_b1.
Definition bdLand_b1 : list bitem := Eval vm_compute in bd_subst s_landB (nd_bd ndA1).

Definition Rt_b1 : sstate := Eval vm_compute in match retile_at (ax_S XR_body1) (rt_at XR_body1) rt_drop rt_news with Some S1 => S1 | None => ax_S XR_body1 end.
Definition XF_b1 : list axform := Eval vm_compute in canon_xf (ax_setS XR_body1 Rt_b1).
Definition C9_b1 : axst := Eval vm_compute in optL (apply_axforms (ax_setS XR_body1 Rt_b1) XF_b1).
Definition i96_b1 : nat := Eval vm_compute in idxB C9_b1 bA 96.
Definition Za1_b1 : axst := Eval vm_compute in zs1 C9_b1 i96_b1 112.
Definition Zs1_b1 : sstate := Eval vm_compute in zs2 Za1_b1 i96_b1 [c4 96 (SLit 0); c8 104 (SLit 0)].
Definition C10_b1 : axst := Eval vm_compute in optL (apply_axforms (ax_setS Za1_b1 Zs1_b1) [AXMerge i96_b1]).
Definition i480_b1 : nat := Eval vm_compute in idxB C10_b1 bA 480.
Definition Za2_b1 : axst := Eval vm_compute in zs1 C10_b1 i480_b1 488.
Definition Zs2_b1 : sstate := Eval vm_compute in zs2 Za2_b1 (S i480_b1) [c1 488 (SLit 0)].
Definition C11_b1 : axst := Eval vm_compute in optL (apply_axforms (ax_setS Za2_b1 Zs2_b1) [AXMerge i480_b1]).
Definition i1256_b1 : nat := Eval vm_compute in idxB C11_b1 bA 1256.
Definition Za3_b1 : axst := Eval vm_compute in zs1 C11_b1 i1256_b1 1264.
Definition Zs3_b1 : sstate := Eval vm_compute in zs2 Za3_b1 (S i1256_b1) [c1 1264 (SLit 0)].
Definition C12_b1 : axst := Eval vm_compute in optL (apply_axforms (ax_setS Za3_b1 Zs3_b1) [AXMerge i1256_b1]).
Definition i880_b1 : nat := Eval vm_compute in idxB C12_b1 bA 880.
Definition Za4_b1 : axst := Eval vm_compute in zs1 C12_b1 i880_b1 900.
Definition Zs4_b1 : sstate := Eval vm_compute in zs2 Za4_b1 i880_b1 [c1 885 (SLit 0)].
Definition C13_b1 : axst := Eval vm_compute in optL (apply_axforms (ax_setS Za4_b1 Zs4_b1) [AXMerge i880_b1]).

Lemma pipe_b1 : ltac2:(tb__ "0|7|
S1S0SaS1cA1M0S92S19S37A1S3bS37A1S3cS3dA4S7S1cS54A2A3S1S0S6S1fS54A1S5A3S1S0SaS18A1M1S13S1aS37S54A2S80A2S7S18S78A2A3S1S0G1S13S78S4S12S14S6cS1dZ70A1A2S9S12A1M2A3A2S7S18S56A2A3S1S0G0S29S19S56A1S6cS4S1eS43Z60S1dZ0A1M3A2S4S1eS8cZ68G3A2S9S1eA1M4A3A3A3S7S1cS5eA2A3S1S0S6S1fS5eA1S5A3S1S0G1S13S1aS56S5eA2S4S12S15S6cA1G2A3A2S7S18S70A2A3S1S0G1S13S70S4S12S14S68S1dZ1e8M5A1A2G2A3A2S7S18S58A2A3S1S0G0S29S19S58A1SbS68A1S4S1eS42G5G3A2G4A3A3S7S1cS60A2A3S1S0S6S1fS60A1S5A3S1S0G1S13S1aS58S60A2S4S12S15S68A1G2A3A2S7S18S72A2A3S1S0G1S13S72S4S12S14S66S1dZ4f0M6A1A2G2A3A2S7S18S5aA2A3S1S0G0S29S19S5aA1SbS66A1S4S1eS42G6G3A2G4A3A3S7S1cS62A2A3S1S0S6S1fS62A1S5A3S1S0G1S13S1aS5aS62A2S4S12S15S66A1G2A3A2S7S18S74A2A3S1S0G1S13S74S4S12S14S6aS1dZ384A1A2G2A3A2S7S18S5cA2A3S1S0G0S29S19S5cA1S6aS4S1eS42Z375G3A2G4A3A3S7S1cS64A2A3S1S0S6S1fS64A1S5A3S1S0G1S13S1aS5cS64A2S4S12S15S6aA1G2A3A2S7S18S76A2A3S0S18S76S33A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma add_datas_b1 : ltac2:(tb__ "0|1|
S1S0S18S79S35S87S89A1M0A2S8aA3S0S6S7aS35G0A2S5A3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma land_checks_b1 : ltac2:(tb__ "0|3|
S1S0S6S1bS33S35S31A3S5A3S1S0S6S8eS31S2bA2S5A3S1S0S6S94S2bS22S19S33A1A1M0A2S5A3S1S0S6S90S31S6eS45A3S5A3S1S0S6S4eS31S44S44A3S5A3S1S0S6S4bS4cS31S4aS88S5A2A2S4aS1dZ0A1M1S5A2A2S5A3S1S0S6S93S8SdS20S20A2M2S7dS7cA3S6eA2S5A3S1S0S6S52G2S91S7cA3S5A3S1S0S6S8fG0S6eA2S5A3S1S0S6S4dG0S44A2S5A3S1S0ScS46A1S49S31S4fS86A1A2S82A3S0S6S52S27S27S23S8dS31R1A2G1A2Lx;S84SfS27S95S85U190U36A2A4A3S5A3A2A2A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition tvLand_a1 : list (sv * sv) := Eval vm_compute in map (xr_subst s_landA) tvL.
Definition nulls_a1 : list (sv * sv) := Eval vm_compute in firstn 18 tvLand_a1.
Definition bdLand_a1 : list bitem := Eval vm_compute in bd_subst s_landA (nd_bd ndA1).

Definition Rt_a1 : sstate := Eval vm_compute in match retile_at (ax_S XR_after1) (rt_at XR_after1) rt_drop rt_news with Some S1 => S1 | None => ax_S XR_after1 end.
Definition XF_a1 : list axform := Eval vm_compute in canon_xf (ax_setS XR_after1 Rt_a1).
Definition C9_a1 : axst := Eval vm_compute in optL (apply_axforms (ax_setS XR_after1 Rt_a1) XF_a1).
Definition i96_a1 : nat := Eval vm_compute in idxB C9_a1 bA 96.
Definition Za1_a1 : axst := Eval vm_compute in zs1 C9_a1 i96_a1 112.
Definition Zs1_a1 : sstate := Eval vm_compute in zs2 Za1_a1 i96_a1 [c4 96 (SLit 0); c8 104 (SLit 0)].
Definition C10_a1 : axst := Eval vm_compute in optL (apply_axforms (ax_setS Za1_a1 Zs1_a1) [AXMerge i96_a1]).
Definition i480_a1 : nat := Eval vm_compute in idxB C10_a1 bA 480.
Definition Za2_a1 : axst := Eval vm_compute in zs1 C10_a1 i480_a1 488.
Definition Zs2_a1 : sstate := Eval vm_compute in zs2 Za2_a1 (S i480_a1) [c1 488 (SLit 0)].
Definition C11_a1 : axst := Eval vm_compute in optL (apply_axforms (ax_setS Za2_a1 Zs2_a1) [AXMerge i480_a1]).
Definition i1256_a1 : nat := Eval vm_compute in idxB C11_a1 bA 1256.
Definition Za3_a1 : axst := Eval vm_compute in zs1 C11_a1 i1256_a1 1264.
Definition Zs3_a1 : sstate := Eval vm_compute in zs2 Za3_a1 (S i1256_a1) [c1 1264 (SLit 0)].
Definition C12_a1 : axst := Eval vm_compute in optL (apply_axforms (ax_setS Za3_a1 Zs3_a1) [AXMerge i1256_a1]).
Definition i880_a1 : nat := Eval vm_compute in idxB C12_a1 bA 880.
Definition Za4_a1 : axst := Eval vm_compute in zs1 C12_a1 i880_a1 900.
Definition Zs4_a1 : sstate := Eval vm_compute in zs2 Za4_a1 i880_a1 [c1 885 (SLit 0)].
Definition C13_a1 : axst := Eval vm_compute in optL (apply_axforms (ax_setS Za4_a1 Zs4_a1) [AXMerge i880_a1]).

Lemma pipe_a1 : ltac2:(tb__ "0|7|
S1S0SaS1cA1M0S92S19S36A1S3bS36A1S3cS3dA4S7S1cS53A2A3S1S0S6S1fS53A1S5A3S1S0SaS18A1M1S13S1aS36S53A2S7fA2S7S18S77A2A3S1S0G1S13S77S4S12S14S6bS1dZ70A1A2S9S12A1M2A3A2S7S18S55A2A3S1S0G0S29S19S55A1S6bS4S1eS43Z60S1dZ0A1M3A2S4S1eS8cZ68G3A2S9S1eA1M4A3A3A3S7S1cS5dA2A3S1S0S6S1fS5dA1S5A3S1S0G1S13S1aS55S5dA2S4S12S15S6bA1G2A3A2S7S18S6fA2A3S1S0G1S13S6fS4S12S14S67S1dZ1e8M5A1A2G2A3A2S7S18S57A2A3S1S0G0S29S19S57A1SbS67A1S4S1eS42G5G3A2G4A3A3S7S1cS5fA2A3S1S0S6S1fS5fA1S5A3S1S0G1S13S1aS57S5fA2S4S12S15S67A1G2A3A2S7S18S71A2A3S1S0G1S13S71S4S12S14S65S1dZ4f0M6A1A2G2A3A2S7S18S59A2A3S1S0G0S29S19S59A1SbS65A1S4S1eS42G6G3A2G4A3A3S7S1cS61A2A3S1S0S6S1fS61A1S5A3S1S0G1S13S1aS59S61A2S4S12S15S65A1G2A3A2S7S18S73A2A3S1S0G1S13S73S4S12S14S69S1dZ384A1A2G2A3A2S7S18S5bA2A3S1S0G0S29S19S5bA1S69S4S1eS42Z375G3A2G4A3A3S7S1cS63A2A3S1S0S6S1fS63A1S5A3S1S0G1S13S1aS5bS63A2S4S12S15S69A1G2A3A2S7S18S75A2A3S0S18S75S32A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma add_datas_a1 : ltac2:(tb__ "0|1|
S1S0S18S79S34S87S89A1M0A2S9aA3S0S6S7aS34G0A2S5A3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma land_checks_a1 : ltac2:(tb__ "0|3|
S1S0S6S1bS32S34S30A3S5A3S1S0S6S8eS30S2bA2S5A3S1S0S6S94S2bS22S19S32A1A1M0A2S5A3S1S0S6S90S30S6dS45A3S5A3S1S0S6S4eS30S44S44A3S5A3S1S0S6S4bS4cS30S4aS88S5A2A2S4aS1dZ0A1M1S5A2A2S5A3S1S0S6S93S8SdS20S20A2M2S7dS7bA3S6dA2S5A3S1S0S6S52G2S91S7bA3S5A3S1S0S6S8fG0S6dA2S5A3S1S0S6S4dG0S44A2S5A3S1S0ScS46A1S49S30S4fS86A1A2S81A3S0S6S52S27S27S23S8dS30R1A2G1A2Lx;S84SfS27S95S85U190U36A2A4A3S5A3A2A2A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

