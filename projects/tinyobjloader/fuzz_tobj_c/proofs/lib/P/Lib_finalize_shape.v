(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "sstate"; "sv"; "ss_next"; "SVar"; "sobj"; "holds"; "SLit"; "sprop"; "ss_facts"; "smatch"; "SPUle"; "eval"; "SMd"; "sv_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "SPJ"; "jpred"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Datatypes"; "prod"; "list"; "pair"; "bool"; "true"; "app"; "cons"; "fst"; "snd"; "Some"; "andb"; "nil"; "option"; "None"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "C_P"; "topL"; "@Corelib.Init.Logic"; "eq"; "ex"; "and"; "eq_refl"; "iff"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_finalize__G1.Lib_finalize_shape_defs"; "tv0"; "NP"; "apH"; "ahd"; "hVP"; "nd"; "amq"; "PD_vp"; "P_fail"; "P_failz"; "P_nop"; "P_ok"; "tvOK"; "E_ad1"; "E_ad2"; "E_ad3"; "E_ad4"; "E_ad5"; "E_ad6"; "E_ad7"; "E_m0"; "E_vp0"; "Pre_fs"; "am_nul"; "am_open"; "tv_vpre"; "X_fit"; "X_mfail"; "X_nA"; "X_nB"; "X_nofit"; "X_open"; "X_push"; "X_vf"; "X_vg"; "X_vk"; "cutsE"; "exitsE"; "no_extra"; "tvK"; "tv_m"; "tv_vg"; "two47"; "xAR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVA"; "amode"; "ameas"; "JGA"; "JGA_pre"; "AHead"; "PDAh"; "PostsCA"; "JLGA"; "am_subst"; "XA"; "am_below"; "amL_ok"; "am_eqb"; "client_callAT"; "new_objs_okA"; "malloc_callAT"; "nodeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_finalize_shape"; "P0_fs"; "@Stdlib.ZArith.BinInt.Z"; "le"; "mul"; "pow"; "add"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "jpost"; "LQP"; "agree_vals"; "import_sub"; "pos_add_nat"; "wsub_dom_below"; "J_ofP"; "call_checkP"; "call_linkP"; "import_okP"; "import_post"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@Stdlib.Lists.List"; "In"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_absorb"; "rho_sub"; "wsub_get"; "wsub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract"; "EC_P"; "MInvR"; "J_alloc_pre"; "Posts_malloc"; "Pre_malloc"; "L_malloc_null"; "L_malloc_ok"; "V_RES"; "ok_sideK"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_finalize__G1.Lib_finalize_shape_defs.VP"; "Pre_vp"; "Posts_vp"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_finalize__G1.Lib_finalize_shape_defs.VR"; "P0_vr"; "tv0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "tvz"; "FBx"; "T_ok"; "call_checkT"; "fbin"; "tv_below"; "tvd"; "tvin"; "T_after"; "T_afterN"; "import_tv"; "robjs_okF"; "tvL_ok"; "tv_sub_eqb"; "PostsC"; "malloc_contracts_ex"; "robjs_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_finalize__G1.Lib_finalize_shape_defs.AD"; "Pre_ad"; "P0_ad"; "PDA_ad"; "ahd"; "tv0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface"; "MA"; "ma_L"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_finalize_shape.Sum"; "Posts_fs"; "PDA_fs"; "@Corelib.Lists.ListDef";
"Forall"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "entails_fr"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "@LinuxProcessSemantics.Riscv.Instr"; "M_MUL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "jnode"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia Permutation.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import MallocModel MallocInv MallocLayout MallocIface MallocLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymSummary SymObj ExampleMemcpy Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Contract Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CfgGlue CursorGlue ObjUnbase ObjXform TobjJV TobjJVx TobjArena TobjJVA TobjJVAx.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_vec__G1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_arena_dup OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_finalize__G1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_vec__G1.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_vec__G1.Lib_vec_push OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_arena_dup OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_finalize__G1.Lib_finalize_shape_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_finalize__G1.Lib_finalize_shape_cert.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition P0_fs (FB : list (Z * Z)) (r : valuation) : Prop := True.

Lemma P0_vr_of_tvz2 : ltac2:(tb__ "0|2|
S1S13S13S12S15S6A1S90S84S15S14S3S3A2M0A1S24S3S83R2P11A2S5R6A1A3S24S3S83R3PfA2S5R8A1A3S93RaR3A2S7bG0S16S3S3S5RaA1M1SeSb5S8R8A1S5R9A1A3A4R4A3S7RcScG1S8S54A1A2A2S26S69Z1RaA2S69RaZ1000A2A2S91S82S81ReRaR9A3R8A2A1F_;F_;F_;F_;F_;F_;Ftv;Fs;Fms;FR;Fe;Fk;Fd;Frho;").
Proof.
  intros rho d k e R ms s tv H17 H15 HZ Hin Hf He. unfold VR.P0_vr. rewrite !rw_call', H17, H15. cbn [eval].
  intros Hk Hd. apply Hk. pose proof (proj1 (Forall_forall _ _) HZ _ Hin) as Ht. unfold tnz, tvv in Ht. cbn [fst snd] in Ht.
  specialize (Ht ltac:(intros Y; exact (Y Hd))).
  rewrite U_mul, U_lit in Ht. cbn [eval] in Ht. cbn [holds] in Hf. rewrite U_lit in Hf. cbn [eval] in Hf. unfold M64v, two47 in *.
  pose proof (bv_urange (rw rho k)) as Rk.
  rewrite (Z.mod_small e) in Ht by lia. rewrite (Z.mod_small (2 ^ 47)) in Hf by lia.
  rewrite Z.mod_small in Ht by nia. nia.
Qed.

Lemma P0_ad_of_kept : ltac2:(tb__ "0|1|
S15S14S12S12A2A1S1S13S3S15S6A1S90S84S15S14S3S3A2M0A1S24S3S83R2PdA2S5R6A1A3S24S3S83R3P10A2R6A3S7bG0S16S3S3S5R8A1R7A4R3A3S7RaScS8Z1000A1S5R9A1A2A2Sa5S94RcRbR5A3S82S81RbR8R7A3R6A2A2F_;F_;F_;F_;Fkept;Fs;Fms;FR;Fsz;Fd;Frho;FFB;").
Proof.
  intros FB rho d sz R ms s kept H13 H16 Hin Hd. unfold AD.P0_ad. rewrite !rw_call', H13, H16.
  cbn [holds] in Hd. rewrite U_lit in Hd. unfold M64v in Hd. rewrite Z.mod_small in Hd by lia.
  exists (bv_unsigned (eval rho (SVar d))), (bv_unsigned (eval rho sz)). split.
  - apply In_FBx. right. exists (SVar d, sz). split; [exact Hin|]. split; [|reflexivity].
    unfold tnz. cbn [fst]. cbn [eval] in Hd |- *. lia.
  - cbn [eval] in Hd |- *. lia.
Qed.

Section Sum.
Variable ok : world -> Prop.
Variable Kc : ltac2:(tb__ "0|0|
S15S7aA1S79OF_;F_;").
Variable FB : list (Z * Z).
Variable rho0 : valuation.
Hypothesis HS : ltac2:(tb__ "0|0|
S8dS0Vok;VKc;A3").
Hypothesis ML : malloc_laws segs C_P.
Hypothesis MC : malloc_contracts segs C_P EC_P.

Definition Posts_fs : list (sstate * jpost) := ltac2:(tb__ "0|3|
S1aS14S2S6eA2M0S16S2S6eS34S5dS0S22VKc;S68VFB;A1M1VFB;S2aS2dA7A4S1aG0S16S2S6eS35S5dS0S22VKc;G1VFB;S36S30A7A4S1aG0S16S2S6eS32S5dS0S22VKc;G1VFB;S2aS30A7M2A4S1aG0S16S2S6eS33G2A4S1fG0A1A3A3A3A3").
Definition PDA_fs : list (sstate * (list (sv * sv) * amode)) := ltac2:(tb__ "0|4|
S1aS14S2S14S15S14S3S3A2A1M0S56A2M1A2M2S16S2G1S34S16G0S56S2aS2dA4A4S1aG2S16S2G1S35S16G0S56S36S30A4A4S1aG2S16S2G1S32S16G0S56S2aS30A4M3A4S1aG2S16S2G1S33G3A4S1fG2A1A3A3A3A3").
Lemma Posts_fs_PDA : ltac2:(tb__ "0|0|
S24S15S14S2S6eA2A1SabS5cS0S22VKc;S68SacVFB;A6A3").
Proof using . reflexivity. Qed.

Lemma Posts_vp_PD : ltac2:(tb__ "0|1|
S15S14S12S12A2A1M0S24S15S14S2S6eA2A1S8fVKc;R1A2Sa1S0S22VKc;G0S91L_;S31R1A6A3FFBc;").
Proof using . reflexivity. Qed.

Let nA : ltac2:(tb__ "0|0|
S14S2S14S15S14S3S3A2A1S56A2A2Sb6Fn;") := ltac2:(tb__ "0|0|
S66S0S22S2bVKc;Vrho0;S68VFB;A1VFB;A7").
Let JGv (tv : list (sv * sv)) (am : amode) : jpred := ltac2:(tb__ "0|0|
S58S0S22S2bVKc;Vrho0;S68VFB;A1VFB;Vtv;Vam;A9").
Let Q : assn := ltac2:(tb__ "0|0|
S6fS0S2bVrho0;SabA4").

Lemma no_extra_vac : ltac2:(tb__ "0|0|
S15S6A1S6S12OF_;F_;S6S12S7bS6R2R4A3S24S17S50R3A1S18A3R5R4R3A2F_;F_;Fa;Fo;FG;FX;").
Proof using . intros X G o a _ H. discriminate H. Qed.

Section SumT.
Variable TR : assn -> assn -> Prop.
Variable FAM : Z -> assn.
Hypothesis TR_facts : ltac2:(tb__ "0|1|
S11S2S1S7dSadS9S7R2A1SaR3A1A3VTR;S10S0R5R4R3A4R2A2M0F_;G0F_;FQ';Frho;FS;FJ;").
Hypothesis TR_ex : forall (A : Type) (J : A -> jpred) S rho (Q' : assn),
  (forall x, TR (SPJ segs (J x) S rho) Q') -> TR (SPJ segs (fun r t m => exists x, J x r t m) S rho) Q'.
Hypothesis TR_pre : ltac2:(tb__ "0|0|
S7dS7dS7dS80R3R1A1R5R2A1F_;Fw;VTR;R4R2A2VTR;R4R3A2F_;F_;FQ';FP';FP;").
Hypothesis TR_exw : forall (A : Type) (P : A -> assn) (Q' : assn), (forall a, TR (P a) Q') -> TR (fun w => exists a, P a w) Q'.
Hypothesis TR_callP : ltac2:(tb__ "0|3|
S11S11S2S2S84S15S6A1M0S15S14S2S6eA2M1A1S7dS1S24S20G0A1SafR7R6R5A3S1dG0R4A2A3S24S17S75R8R7R6R5SaeG1S2S1bS2S6eA2R4A4A5S18A3S1VTR;S10S0RbR9R1A4S6fS0S4R9A1R1R6A4A2Frho1;S15S7aA1M2S90S79SbS0R7RdS16G2Sb0R3Sb1R2R1A2A4A4R10R8R4R2A3R10S82S81R9RcR4A3RdA2R5R3A3F_;F_;Fmd;Fms;Ftr;S2S6eG2S90S79S1G2S90S79S7bG1S16S2S6eR9R8A4R10A3SbS0RfR15S16G2Sb0R8Sb1R7R6A2A4A4R18R10R9R7A3S70S4R16A1S82S81R11R14R9A3R15A2R7A3SbS0R8RdS16G2Sb0R7Sb1R6R5A2A4A4RdS82S81R13R16RbA3R17A2R9R8R6A4S26S77R14RcR17R18R19RfRaA7S1S76R15RdR18R19R1aR1bR10R1RbA9VTR;S10S0S74R10S82S81R16R19ReA3R1aA2RcA3S78R1aS4R1bA1R11S4R1cA1R19A5R2A4R17A2F_;Frho';A2F_;F_;F_;F_;F_;F_;Fmd';Fms';Ftr';FrhoL;Fmd;Fms;Ftr;FJL;FL;VTR;S10S0ReRcR6A4R7A2F_;F_;F_;F_;F_;Frho;FQ';FPosts;FR;Fs;FPre;FC;FJp;FJ;").

Hypothesis CMALLOC : ltac2:(tb__ "0|0|
Sa9S1VTR;S10S0S87S0S22R2VKc;A4S89S85A1R1A4S6fS0S67R1S88S0S22S85R2VKc;A5A4A2Frho1;FAi;").
Hypothesis CAD : ltac2:(tb__ "0|0|
S15S14S12S12A2A1S1VTR;S10S0S59S0S22VKc;Sa5R2A1R2Sa8Sa7A7Sa4R1A4S6fS0S67R1S5cS0S22VKc;Sa5Sa6R2A6A4A2Frho1;FFBc;").
Hypothesis CVP : ltac2:(tb__ "0|2|
S15S14S12S12A2A1M0S1VTR;S10S0S59S0S22VKc;G0S91L_;M1R2A1R2S92S5aS5S2eA1A1A7S8eR1A4S6fS0S67R1S5cS0S22VKc;G1S5bS31S2eA2R2A6A4A2Frho1;FFBc;").
Hypothesis REENTER : ltac2:(tb__ "0|4|
S2S15S14S3S3A2A1M0S56S12S3S1S12S7bS14S14S2S14G0S56A2M1A2M2S14S12S3A2M3A2S16G2G3S16S2G1R7S16G0S56R6R5A4A4S16S12S3R4R3A4A4S4eA3S69Z0R5A2S69S6aS6cR6Z1A2S6bZ2Z40A2A2R3A2VTR;S10S0VJGv;R9R8A2RaR5A4VFAM;R4A1A2F_;F_;F_;Fb;Frho;FvT;FrT;Fam;Ftv;FT;").
Hypothesis POST : ltac2:(tb__ "0|0|
S2S15S14S3S3A2A1S56S1S12S7bS14S2S6eA2S16S2S6eR5S5dS0S22VKc;S68VFB;A1VFB;R4R3A7A4SabA3VTR;S10S0VJGv;R5R4A2R6R3A4VFAM;R2A1A2F_;Fb;Frho;Fam;Ftv;FP;").

Let MALLOC : ltac2:(tb__ "0|a|
S2S84S15S6A1M0S1S15S14S3S3A2M1A1S56S7dSa9S1VTR;S10S0S87S0S22R2VKc;A4S89S85A1M2R1A4S6fS0Sb3R1S88S0S22S85R2VKc;A5A4A2Frho1;FAi;S24S20G0A1SafR8G2R7A3S1dG0R6A2A3S24S17S96S22S2bR9G2R8R7S1aS2S8aS85A1M3S1aS2S8bS85A1M4S1fS2A1A3A3A7S18A3S24S17Sb2S2bS4RaA1A2S18A3S24S17S98S4RbA1R7A2S18A3S24S17S60S4RcA1R7A2S18A3S24S17SfS4RdA1S83RcPcM5A2A2S18A3S24S3S83S71RdSb3G4S4ReA1M6A4S8cA2S5S72G6UaM7A2A1A3Sa9SadS9S7RdA1SaR10A1A3S68VFB;Vrho0;A2S70S2bVrho0;RfA3S97VFB;R4A2S9aVFB;R5R11R10A4S99R12R11A2S93R13R12A2S5fVFB;R12R8R14R13A5S25S1S1S25S79S79S86S0S22RbR2R1A5Lmd;A2LrhoM;A2S95R16S23SaaRaA1A1A2S26Sa3S0S22RbS21S12A1R17R18A6S6dZ0Sb4Q40SdR17S83R19G5A2A2A2A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FAi;S1S70S4R11A1ReR1A3VTR;S10S0S58S0S22S2bVKc;Vrho0;S68VFB;A1M8VFB;ReRdA9M9S9bR12R11R10G3A4R2A4RcA2F_;Frho';S1S70S4R12A1RfR1A3VTR;S10S0S58S0S22S2bVKc;Vrho0;G8VFB;S1aG1S16S3S3S5S72S4R13A1G7A2A1S83R12G5A2A4RfA3ReA9S9bR13R12R11G4A4R2A4RdA2F_;Frho';VTR;S10S0G9R12RfA4RcA2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Fam;Ftv;Frho;FR;Fs;FCl;") := ltac2:(tb__ "0|0|
S65S0S22S85S2bVKc;Vrho0;S68VFB;A1VFB;VML;VTR;VTR_facts;VTR_ex;VTR_pre;VTR_callP;Ae").
Let CALLAD : ltac2:(tb__ "0|e|
S2S84S15S6A1M0S1S15S14S3S3A2M1A1M2G2S56S7dS24S20G0A1SafR8Sa4R7A3S1dG0R6A2A3S24S17S96S22S2bR9Sa4R8R7SaeS14S2S14G2S56A2M3A2M4S2S1bS2G3A2Sa6A4A7S18A3S24S17S73R9S67A2S18A3S24S17Sb2S2bS4RbA1A2S18A3S24S17S98S4RcA1S19G1R8R7A3A2S18A3S24S17S60S4RdA1R7A2S18A3S24S17Sa0RdR9Sa8A3S18A3S24S17S62S5eReSa7A2R9A2S18A3S24S17S7cG4G4S1eS1eS9fS67R10S4R11A1M5S1bS2G3R1A3M6S1bG2S56S1cS2G3R1A3M7A3M8A5S61S67R10G5G6S1cG2S56G7A3M9A5A2S64Sa4G6G8G9A4A2Ld;Sa6A3S18A3Sa9S90SadS9S7R10A1SaR13A1A3S68VFB;Vrho0;A2S70S2bVrho0;R12A3S97VFB;R5A2S9aVFB;R6R14S19G1R13R12A3A4S99R15S19G1R14R13A3A2S93R16S19G1R15R14A3A2S5fVFB;R14R9R17S19G1R16R15A3A5S25S1S1S25S79S79S86S0S22RcR2R1A5Lmd;A2LrhoM;A2S95R19S23SaaRbA1A1A2S26S9eS0S22Vrho0;VFB;R1aR19R1bA7Sa5S94VFB;R1aR19A3S82S81R1aR1bRbA3R1cA2A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fms;FAi;G4S1S7bG4R2Sa6A3S70S4R15A1R12R2A3VTR;S10S0S58S0S22S2bVKc;Vrho0;S68VFB;A1MaVFB;S19G1R12S9dS71R15S67S1bS2G3R4A3MbS4R16A1A4McS1bG2S56S1cS2G3R4A3MdA3A2A3S5eGcS1cG2S56GdA3A2A9S9cS67R16R15R14GbA5R3A4RfA2F_;F_;Frho';Fd;VTR;S10S0S58S0S22S2bVKc;Vrho0;GaVFB;S19G1RfReA3RdA9R13R10A4RcA2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Fam;Fpassed;Fkept;Frho;FR;Fs;FCl;") := ltac2:(tb__ "0|0|
S63S0S22S2bVKc;Vrho0;S68VFB;A1VFB;VML;Sa5Sa4Sa8Sa7Sa6S67S27S13S4Sa4A1A2VTR;VTR_facts;VTR_ex;VTR_pre;VTR_callP;VCAD;A15").
Let CALLVP : ltac2:(tb__ "0|f|
S2S84S15S6A1M0S1S15S14S3S3A2M1A1M2G2S56S7dS24S20G0A1SafR8S8eR7A3S1dG0R6A2A3S24S17S96S22S2bR9S8eR8R7SaeS14S2S14G2S56A2M3A2M4S2S1bS2G3A2S5bS31S2eA2M5A4A7S18A3S24S17S73R9S67A2S18A3S24S17Sb2S2bS4RbA1A2S18A3S24S17S98S4RcA1S19G1R8R7A3A2S18A3S24S17S60S4RdA1R7A2S18A3S24S17Sa0RdR9S92A3S18A3S24S17S62S5eReS5aS5S2eA1A1A2R9A2S18A3S24S17S7cG4G4S1eS1eS9fS67R10S4R11A1M6S1bS2G3R1A3M7S1bG2S56S1cS2G3R1A3M8A3M9A5S61S67R10G6G7S1cG2S56G8A3MaA5A2S64S8eG7G9GaA4A2Ld;G5A3S18A3Sa9S90SadS9S7R10A1SaR13A1A3S68VFB;Vrho0;A2S70S2bVrho0;R12A3S97VFB;R5A2S9aVFB;R6R14S19G1R13R12A3A4S99R15S19G1R14R13A3A2S93R16S19G1R15R14A3A2S5fVFB;R14R9R17S19G1R16R15A3A5S25S1S1S25S79S79S86S0S22RcR2R1A5Lmd;A2LrhoM;A2S95R19S23SaaRbA1A1A2S26S9eS0S22Vrho0;VFB;R1aR19R1bA7S15S14S12S12A2A1S91L_;S94VFB;R1aR19A3S82S81R1aR1bRbA3R1cA2A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fms;FAi;G4S1S7bG4R2G5A3S70S4R15A1R12R2A3VTR;S10S0S58S0S22S2bVKc;Vrho0;S68VFB;A1MbVFB;S19G1R12S9dS71R15S67S1bS2G3R4A3McS4R16A1A4MdS1bG2S56S1cS2G3R4A3MeA3A2A3S5eGdS1cG2S56GeA3A2A9S9cS67R16R15R14GcA5R3A4RfA2F_;F_;Frho';Fd;VTR;S10S0S58S0S22S2bVKc;Vrho0;GbVFB;S19G1RfReA3RdA9R13R10A4RcA2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Fam;Fpassed;Fkept;Frho;FR;Fs;FCl;") := ltac2:(tb__ "0|0|
S63S0S22S2bVKc;Vrho0;S68VFB;A1VFB;VML;S15S14S12S12A2A1S91L_;S8eS92S5aS5S2eA1A1S5bS31S2eA2S67S27S13S4S8eA1A2VTR;VTR_facts;VTR_ex;VTR_pre;VTR_callP;VCVP;A15").

Lemma bound_ge : ltac2:(tb__ "0|3|
S12S12S1S3S28S69S6aS6cR4Z1A2M0S6bZ2Z40A2M1A2S6cS6aR3G1A2Sb4Q40SdR2R1A2A2A2A2M2S29S69G0R3A2G2A2A2Fv;Frho;Fb;Fr;").
Proof using . intros. pose proof (urange (eval rho v)). nia. Qed.
Ltac reenter T tv am rT := apply (REENTER T tv am rT z0); [cbn; tauto | lia | first [lia | unfold ameas, ad_rank, ad_var, nd; cbn [fst snd]; apply bound_ge; left; lia]].

Ltac via_ex T tv am rT :=
  apply (TR_pre (fun w => exists r, SPJ segs (JGv tv am) T r w)); [ | apply TR_exw; intros r; reenter T tv am rT ].

Ltac land X2 T s tvi tvj ami amj Hw :=
  lazymatch type of Hw with SPJ _ _ _ ?r _ =>
    exists (rho_sub r s);
    eapply (SPJ_entails_JGA segs C_P NP Kc rho0 (P0_fs FB) FB ML X2 T s tvi tvj ami amj);
      [vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | vm_compute; reflexivity | exact Hw]
  end.

Lemma X_P_nop : ltac2:(tb__ "0|0|
S1S12VTR;S10S0VJGv;S2aS2dA2S34R2A4VFAM;R1A1A2Fb;Frho;").
Proof using POST nA. intros rho b. apply POST. cbn. tauto. Qed.
Lemma X_P_ok : ltac2:(tb__ "0|0|
S1S12VTR;S10S0VJGv;S36S30A2S35R2A4VFAM;R1A1A2Fb;Frho;").
Proof using POST nA. intros rho b. apply POST. cbn. tauto. Qed.
Lemma X_P_fail : ltac2:(tb__ "0|0|
S1S12VTR;S10S0VJGv;S2aS30A2S32R2A4VFAM;R1A1A2Fb;Frho;").
Proof using POST nA. intros rho b. apply POST. cbn. tauto. Qed.
Lemma X_P_failz : ltac2:(tb__ "0|0|
S1S12VTR;S10S0VJGv;S2aS30A2S33R2A4VFAM;R1A1A2Fb;Frho;").
Proof using POST nA. intros rho b. apply POST. cbn. tauto. Qed.

Lemma X_open_ok : ltac2:(tb__ "0|0|
S1S12S69S6aZ5cS6bZ2Z40A2A2R1A2VTR;S10S0VJGv;S2aS2dA2S49R3A4VFAM;R2A1A2F_;Fb;Frho;").
Proof using ML REENTER TR_exw TR_pre nA.
  intros rho b Hb. via_ex C_open tv0 am_open 91.
  intros w Hw.
  destruct (JGA_open segs C_P NP Kc rho0 (P0_fs FB) FB ML (TobjJVA.NP_ok_intro NP eq_refl) tv0 xHD X_open no_extra rho w) as (rho' & _ & Hw');
    [vm_compute; reflexivity | reflexivity | reflexivity | reflexivity | vm_compute; reflexivity | | vm_compute; reflexivity | exact Hw |].
  - intros o a Ho Hx. discriminate Hx.
  - exists rho'. exact Hw'.
Qed.

Lemma X_nofit_ok : ltac2:(tb__ "0|0|
S1S12S69S6aZ58S6bZ2Z40A2A2R1A2VTR;S10S0VJGv;S2aS42A2S48R3A4VFAM;R2A1A2F_;Fb;Frho;").
Proof using ML REENTER TR_exw TR_pre nA.
  intros rho b Hb. via_ex C_slow tv0 ahd 87.
  intros w Hw.
  destruct (JGA_close segs C_P NP Kc rho0 (P0_fs FB) FB ML tv0 xHD (SVar 400) (SVar 401) (SVar 402) X_nofit
              (firstn 30 (ss_objs X_nofit)) (nth 30 (ss_objs X_nofit) O_AF) rho w) as (rho' & _ & Hw');
    [vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | exact Hw |].
  change (drop_last_state X_nofit (firstn 30 (ss_objs X_nofit))) with X_nofitc in Hw'.
  land X_nofitc C_slow (infer_sub NP X_nofitc C_slow) tv0 tv0 ahd ahd Hw'.
Qed.

Lemma X_fit_ok : ltac2:(tb__ "0|0|
S1S12S69S6aZ50S6bZ2Z40A2A2R1A2VTR;S10S0VJGv;S2aS42A2S44R3A4VFAM;R2A1A2F_;Fb;Frho;").
Proof using ML REENTER TR_exw TR_pre nA.
  intros rho b Hb. via_ex C_nul tv0 am_nul 79.
  intros w Hw. exists (rho_sub rho s_fit).
  eapply (SPJ_entails_JGA segs C_P NP Kc rho0 (P0_fs FB) FB ML X_fit3 C_nul s_fit tv0 tv0 (AOpen xHD (SVar 400) (SVar 401) [(p_fit, SLit 1)]) am_nul);
    [vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | vm_compute; reflexivity |].
  apply (JGA_carve segs C_P NP Kc rho0 (P0_fs FB) FB ML (TobjJVA.NP_ok_intro NP eq_refl) tv0 xHD (SVar 400) (SVar 401) p_fit (SLit 1) X_fit no_extra rho w);
    [vm_compute; reflexivity | reflexivity | vm_compute; reflexivity | | | exact Hw].
  - intros o a _ Hx. discriminate Hx.
  - intros HP0 Hav HF. clear - HF. cbv beta. unfold p_fit, xHD, HDR.
    pick_facts HF [0%nat; 1%nat; 2%nat; 3%nat; 4%nat; 5%nat]. zfacts; zsimp; lia.
Qed.

Lemma X_E_m : ltac2:(tb__ "0|0|
S1VTR;S10S0VJGv;S2aS2dA2S3eR1A4VFAM;S57S2fS3eS2aS2dZ55A4R1A2A1A2Frho;").
Proof using CMALLOC MALLOC REENTER nA.
  intros rho. eapply TR_pre.
  2: { apply (MALLOC E_m s_m R_m rho tv0 ahd _ CMALLOC).
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - intros Ai HF HP0 Hav HP HN HD HZ HXA (rhoM & md & HM) HT. split.
    + eapply (robjs_check_sound segs C_P FB Ai rho (ss_facts E_m) tv0 None no_extra R_m None rhoM md HM HT HF HN HD HZ); [vm_compute; reflexivity | | exact I].
      intros o a _ Hx. discriminate Hx.
    + change (wsub_get s_m 12) with (SLit 65568). apply Z.ltb_lt. vm_compute. reflexivity.
  - intros rho' _.
    replace (T_after E_m s_m R_m (L_malloc_null EC_P)) with T_mnull by (vm_compute; reflexivity).
    reenter T_mnull tv0 ahd 83.
  - intros rho' _.
    replace (T_after E_m s_m R_m (L_malloc_ok EC_P)) with T_mok0 by (vm_compute; reflexivity).
    change (pos_add_nat (ss_next E_m) 10) with vN.
    change (wsub_get s_m 12) with (SLit 65568).
    eapply TR_pre; [ | reenter T_mok tv_m ahd 83 ].
    intros w Hw. unfold T_mok. apply SPJ_refacts_J; [exact Hw | reflexivity |].
    intros tr md HJ HF.
    eapply (JGA_tv_facts segs C_P NP Kc rho0 (P0_fs FB) FB); [exact HJ | left; reflexivity |].
    eapply (tnz_of_fact rho' (SVar vN)). eapply (proj1 (Forall_forall _ _) HF). vm_compute. tauto. }
  intros w Hw. exact (SPJ_xforms segs _ xs_mwin rho E_m0 E_m w ltac:(vm_compute; reflexivity) Hw).
Qed.

Lemma X_mfail_ok : ltac2:(tb__ "0|0|
S1S12S69S6aZbS6bZ2Z40A2A2R1A2VTR;S10S0VJGv;S2aS2dA2S45R3A4VFAM;R2A1A2F_;Fb;Frho;").
Proof using ML REENTER TR_exw TR_pre nA.
  intros rho b Hb. via_ex C_fail tv0 apH 10. intros w Hw.
  pose proof (SPJ_nsteps segs _ ns_mfail rho X_mfail X_mfail2 w ltac:(vm_compute; reflexivity) Hw) as Hw2.
  land X_mfail2 C_fail (infer_sub NP X_mfail2 C_fail) tv0 tv0 ahd apH Hw2.
Qed.

Lemma X_push_ok : ltac2:(tb__ "0|0|
S1S12S69S6aZ50S6bZ2Z40A2A2R1A2VTR;S10S0VJGv;S52S2dA2S4aR3A4VFAM;R2A1A2F_;Fb;Frho;").
Proof using ML REENTER TR_exw TR_pre nA.
  intros rho b Hb. via_ex C_nul tv0 am_nul 79. intros w Hw.
  pose proof (SPJ_nsteps segs _ ns_push rho X_push X_push3 w ltac:(vm_compute; reflexivity) Hw) as Hw1.
  destruct (JGA_push_open segs C_P NP Kc rho0 (P0_fs FB) FB ML tv_m 0%nat blkN xHD (SLit 65536) (SLit 1) X_push3
              (firstn 30 (ss_objs X_push3)) (nth 30 (ss_objs X_push3) O_AF) (nth 31 (ss_objs X_push3) O_AF) rho w)
    as (rho1 & _ & Hw2);
    [vm_compute; reflexivity | reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
    | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
    | vm_compute; reflexivity | exact Hw1 |].
  change (drop_last_state X_push3 (firstn 30 (ss_objs X_push3) ++ [nth 30 (ss_objs X_push3) O_AF])) with X_push4 in Hw2.
  change (remove_nth 0 tv_m) with tv0 in Hw2. change (fst blkN) with (SVar vN) in Hw2.
  exists (rho_sub rho1 s_push).
  eapply (SPJ_entails_JGA segs C_P NP Kc rho0 (P0_fs FB) FB ML X_push5 C_nul s_push tv0 tv0 (AOpen (SVar vN) xHD (SLit 65536) [(p_new, SLit 1)]) am_nul);
    [vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | vm_compute; reflexivity |].
  apply (JGA_carve segs C_P NP Kc rho0 (P0_fs FB) FB ML (TobjJVA.NP_ok_intro NP eq_refl) tv0 (SVar vN) xHD (SLit 65536) p_new (SLit 1) X_push4 no_extra rho1 w);
    [vm_compute; reflexivity | reflexivity | vm_compute; reflexivity | | | exact Hw2].
  - intros o a _ Hx. discriminate Hx.
  - intros HP0 Hav HF. clear - HF. cbv beta. unfold p_new, vN, HDR.
    pick_facts HF [0%nat; 2%nat; 3%nat]. zfacts; zsimp; lia.
Qed.

Ltac nul_glue X X1 X2 T :=
  intros rho b Hb; via_ex T tv0 apH 77; intros w Hw;
  destruct (JGA_unslot segs C_P NP Kc rho0 (P0_fs FB) FB ML tv0 pH pNX pCAP pNAME (SLit 1) X (firstn 31 (ss_objs X)) (nth 31 (ss_objs X) O_AF) rho w)
    as (rho1 & _ & Hw1); [vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | exact Hw |];
  change (drop_last_state X (firstn 31 (ss_objs X))) with X1 in Hw1;
  destruct (JGA_close segs C_P NP Kc rho0 (P0_fs FB) FB ML tv0 pH pNX pCAP pU X1 (firstn 30 (ss_objs X1)) (nth 30 (ss_objs X1) O_AF) rho1 w)
    as (rho2 & _ & Hw2); [vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | exact Hw1 |];
  change (drop_last_state X1 (firstn 30 (ss_objs X1))) with X2 in Hw2;
  land X2 T (infer_sub NP X2 T) tv0 tv0 apH apH Hw2.
Lemma X_nA_ok : ltac2:(tb__ "0|0|
S1S12S69S6aZ4eS6bZ2Z40A2A2R1A2VTR;S10S0VJGv;S2aS41A2S46R3A4VFAM;R2A1A2F_;Fb;Frho;").
Proof using ML REENTER TR_exw TR_pre nA. nul_glue X_nA X_nA1 X_nA2 C_A. Qed.
Lemma X_nB_ok : ltac2:(tb__ "0|0|
S1S12S69S6aZ4eS6bZ2Z40A2A2R1A2VTR;S10S0VJGv;S2aS41A2S47R3A4VFAM;R2A1A2F_;Fb;Frho;").
Proof using ML REENTER TR_exw TR_pre nA. nul_glue X_nB X_nB1 X_nB2 C_B. Qed.

Lemma tv0_split : ltac2:(tb__ "0|1|
S24S15S14S3S3A2M0A1S2aS19G0S51S1aG0S16S3S3S55S8Z40A1A4S1fG0A1A3A3A3").
Proof using . reflexivity. Qed.
Lemma tvz_app_l : ltac2:(tb__ "0|2|
S1S15S14S3S3A2M0A1M1G1S93R3S19G0R2R1A3A2S93R4R3A2F_;Fb;Fa;Frho;").
Proof using . intros rho a b H. unfold tvz in *. apply Forall_forall. intros t Ht. apply (proj1 (Forall_forall _ _) H). apply in_or_app. left. exact Ht. Qed.

Ltac ad_site E Ef Tf To dpos szk ipos rT :=
  intros rho; eapply TR_pre;
  [ | rewrite tv0_split;
      apply (CALLAD Ef (s_ad Ef) (R_ad Ef) rho tvK [(xAR, SLit 64)] apH);
      [ vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | reflexivity | reflexivity
      | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
      | intros Ai ms HF HP0 Hav HP HN HD HZ HXA HM HT; split;
        [ eapply (robjs_checkF_sound segs C_P rho0 FB rho (ss_facts Ef) tvK no_extra (R_ad Ef) HF (TobjJVx.T_ok_T0_agree _ _ _ _ Hav (@eq_refl comparison Lt) HT));
          [ exact (tvz_app_l rho _ _ HZ) | vm_compute; reflexivity | intros o a _ Hx; discriminate Hx ]
        | apply (P0_ad_of_kept FB rho dpos szk (R_ad Ef) ms (s_ad Ef) tvK);
          [ vm_compute; reflexivity | vm_compute; reflexivity | apply (nth_error_In _ ipos); reflexivity
          | pick_facts HF [3%nat]; assumption ] ]
      | intros d rho' Hd Hag; destruct Hd as [<-|[<-|[]]]; cbn [fst snd];
        match goal with |- TR (SPJ _ (JGA _ _ _ _ _ _ _ ?tv ?am) ?T _) _ =>
          replace tv with tv0 by (vm_compute; reflexivity);
          first [ replace am with am1_fail by (vm_compute; reflexivity); replace T with Tf by (vm_compute; reflexivity); reenter Tf tv0 am1_fail rT
                | replace am with am1_ok by (vm_compute; reflexivity); replace T with To by (vm_compute; reflexivity); reenter To tv0 am1_ok rT ]
        end ] ];
  intros w Hw; apply SPJ_refacts_J; [exact Hw | reflexivity |];
  intros tr md HJ HFX;
  eapply (nz_facts_sound segs C_P NP Kc rho0 (P0_fs FB) FB (ss_facts E) tv0); [vm_compute; reflexivity | exact HFX | exact (JGA_JG _ _ _ _ _ _ _ _ _ _ _ _ HJ)].

Lemma X_E_ad1 : ltac2:(tb__ "0|0|
S1VTR;S10S0VJGv;S2aS2cA2S37R1A4VFAM;S57S2fS37S2aS2cZ4bA4R1A2A1A2Frho;").
Proof using CALLAD REENTER nA. ad_site E_ad1 E_ad1f T1_fail T1_ok 113%positive (kb 12 (SVar 115)) 0%nat 73. Qed.
Lemma X_E_ad2 : ltac2:(tb__ "0|0|
S1VTR;S10S0VJGv;S2aS2cA2S38R1A4VFAM;S57S2fS38S2aS2cZ45A4R1A2A1A2Frho;").
Proof using CALLAD REENTER nA. ad_site E_ad2 E_ad2f T2_fail T2_ok 116%positive (kb 4 (SVar 118)) 1%nat 67. Qed.
Lemma X_E_ad3 : ltac2:(tb__ "0|0|
S1VTR;S10S0VJGv;S2aS2cA2S39R1A4VFAM;S57S2fS39S2aS2cZ3fA4R1A2A1A2Frho;").
Proof using CALLAD REENTER nA. ad_site E_ad3 E_ad3f T3_fail T3_ok 119%positive (kb 4 (SVar 121)) 2%nat 61. Qed.
Lemma X_E_ad4 : ltac2:(tb__ "0|0|
S1VTR;S10S0VJGv;S2aS2cA2S3aR1A4VFAM;S57S2fS3aS2aS2cZ39A4R1A2A1A2Frho;").
Proof using CALLAD REENTER nA. ad_site E_ad4 E_ad4f T4_fail T4_ok 122%positive (kb 4 (SVar 124)) 3%nat 55. Qed.
Lemma X_E_ad5 : ltac2:(tb__ "0|0|
S1VTR;S10S0VJGv;S2aS2cA2S3bR1A4VFAM;S57S2fS3bS2aS2cZ33A4R1A2A1A2Frho;").
Proof using CALLAD REENTER nA. ad_site E_ad5 E_ad5f T5_fail T5_ok 125%positive (kb 12 (SVar 127)) 4%nat 49. Qed.
Lemma X_E_ad6 : ltac2:(tb__ "0|0|
S1VTR;S10S0VJGv;S2aS2cA2S3cR1A4VFAM;S57S2fS3cS2aS2cZ2dA4R1A2A1A2Frho;").
Proof using CALLAD REENTER nA. ad_site E_ad6 E_ad6f T6_fail T6_ok 128%positive (kb 4 (SVar 130)) 5%nat 43. Qed.
Lemma X_E_ad7 : ltac2:(tb__ "0|0|
S1VTR;S10S0VJGv;S2aS2cA2S3dR1A4VFAM;S57S2fS3dS2aS2cZ27A4R1A2A1A2Frho;").
Proof using CALLAD REENTER nA. ad_site E_ad7 E_ad7f T7_fail T7_ok 131%positive (kb 12 (SVar 133)) 6%nat 37. Qed.

Lemma X_E_vp0 : ltac2:(tb__ "0|0|
S1VTR;S10S0VJGv;S2aS2cA2S3fR1A4VFAM;S57S2fS3fS2aS2cZ21A4R1A2A1A2Frho;").
Proof using CALLVP REENTER nA.
  intros rho. eapply TR_pre.
  2: { apply (CALLVP E_vp s_vp R_vp rho tvV [(t_d sh0, kb 128 (t_k sh0))] apH).
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - intros Ai ms HF HP0 Hav HP HN HD HZ HXA HM HT. split.
    + eapply (robjs_checkF_sound segs C_P rho0 FB rho (ss_facts E_vp) tvV no_extra R_vp HF (TobjJVx.T_ok_T0_agree _ _ _ _ Hav (@eq_refl comparison Lt) HT));
        [ exact (tvz_app_l rho _ _ HZ) | vm_compute; reflexivity | intros o a _ Hx; discriminate Hx ].
    + cbn beta. eapply (P0_vr_of_tvz2 rho 110 112 128); [vm_compute; reflexivity | vm_compute; reflexivity | exact HZ | apply in_or_app; right; left; reflexivity | | lia].
      eapply (proj1 (Forall_forall _ _) HF). vm_compute. tauto.
  - intros d rho' Hd Hag. destruct Hd as [<-|[<-|[<-|[]]]]; cbn [fst snd];
      match goal with |- TR (SPJ _ (JGA _ _ _ _ _ _ _ ?tv ?am) ?T _) _ =>
        replace am with apH by (vm_compute; reflexivity) end.
    + match goal with |- TR (SPJ _ (JGA _ _ _ _ _ _ _ ?tv _) ?T _) _ =>
        replace tv with tv_vpre by (vm_compute; reflexivity); replace T with T_vf by (vm_compute; reflexivity) end.
      reenter T_vf tv_vpre apH 31.
    + match goal with |- TR (SPJ _ (JGA _ _ _ _ _ _ _ ?tv _) ?T _) _ =>
        replace tv with tv_vpre by (vm_compute; reflexivity); replace T with T_vk0 by (vm_compute; reflexivity) end.
      eapply TR_pre; [ | reenter T_vk tv_vpre apH 31 ].
      intros w Hw. unfold T_vk, enrich. apply SPJ_refacts_J; [exact Hw | reflexivity |].
      intros tr md HJ HFX.
      eapply (nz_facts_sound segs C_P NP Kc rho0 (P0_fs FB) FB (ss_facts T_vk0) tv_vpre); [vm_compute; reflexivity | exact HFX | exact (JGA_JG _ _ _ _ _ _ _ _ _ _ _ _ HJ)].
    + match goal with |- TR (SPJ _ (JGA _ _ _ _ _ _ _ ?tv _) ?T _) _ =>
        replace tv with tv_vg by (vm_compute; reflexivity); replace T with T_vg by (vm_compute; reflexivity) end.
      reenter T_vg tv_vg apH 31. }
  intros w Hw. unfold tvV. apply (SPJ_JGA_move_last segs C_P NP Kc rho0 (P0_fs FB) FB tv7 [(xAR, SLit 64)] (t_d sh0, kb 128 (t_k sh0))).
  change (tv7 ++ (t_d sh0, kb 128 (t_k sh0)) :: [(xAR, SLit 64)]) with tv0.
  exact (SPJ_nsteps segs _ ns_vpwin rho E_vp0 E_vp w ltac:(vm_compute; reflexivity) Hw).
Qed.

Lemma X_vf_ok : ltac2:(tb__ "0|0|
S1S12S69S6aZbS6bZ2Z40A2A2R1A2VTR;S10S0VJGv;S43S2cA2S4bR3A4VFAM;R2A1A2F_;Fb;Frho;").
Proof using ML REENTER TR_exw TR_pre nA.
  intros rho b Hb. via_ex C_fail tv0 apH 10. intros w Hw.
  pose proof (SPJ_nsteps segs _ (ns_v 0 4 sel_f [XRebase 7]) rho X_vf X_vf2 w ltac:(vm_compute; reflexivity) Hw) as Hw1.
  unfold tv_vpre, tvV in Hw1.
  pose proof (SPJ_JGA_move_back segs C_P NP Kc rho0 (P0_fs FB) FB tv7 [(xAR, SLit 64)] (t_d sh0, kb 128 (t_k sh0)) apH X_vf2 rho w Hw1) as Hw2.
  change (tv7 ++ (t_d sh0, kb 128 (t_k sh0)) :: [(xAR, SLit 64)]) with tv0 in Hw2.
  land X_vf2 C_fail (infer_sub NP X_vf2 C_fail) tv0 tv0 apH apH Hw2.
Qed.
Lemma X_vk_ok : ltac2:(tb__ "0|0|
S1S12VTR;S10S0VJGv;S43S2cA2S4dR2A4VFAM;R1A1A2Fb;Frho;").
Proof using ML POST TR_exw TR_pre nA.
  intros rho b.
  apply (TR_pre (fun w => exists r, SPJ segs (JGv tvOK amq) P_ok r w)); [ | apply TR_exw; intros r; apply X_P_ok ].
  intros w Hw.
  pose proof (SPJ_nsteps segs _ (ns_v 0 4 sel_v [XRebase 7]) rho X_vk X_vk2 w ltac:(vm_compute; reflexivity) Hw) as Hw1.
  unfold tv_vpre, tvV in Hw1.
  pose proof (SPJ_JGA_move_back segs C_P NP Kc rho0 (P0_fs FB) FB tv7 [(xAR, SLit 64)] (t_d sh0, kb 128 (t_k sh0)) apH X_vk2 rho w Hw1) as Hw2.
  change (tv7 ++ (t_d sh0, kb 128 (t_k sh0)) :: [(xAR, SLit 64)]) with tv0 in Hw2.
  land X_vk2 P_ok (infer_sub NP X_vk2 P_ok) tv0 tvOK apH amq Hw2.
Qed.
Definition tv_vg' : list (sv * sv) := Eval vm_compute in tv7 ++ [nth 8 tv_vg (z0, z0); (xAR, SLit 64)].
Lemma X_vg_ok : ltac2:(tb__ "0|0|
S1S12VTR;S10S0VJGv;S53S2cA2S4cR2A4VFAM;R1A1A2Fb;Frho;").
Proof using ML POST TR_exw TR_pre nA.
  intros rho b.
  apply (TR_pre (fun w => exists r, SPJ segs (JGv tvOK amq) P_ok r w)); [ | apply TR_exw; intros r; apply X_P_ok ].
  intros w Hw.
  pose proof (SPJ_nsteps segs _ (ns_v 0 4 sel_v [XRebase 7]) rho X_vg X_vg2 w ltac:(vm_compute; reflexivity) Hw) as Hw1.
  change tv_vg with ((tv7 ++ [(xAR, SLit 64)]) ++ [nth 8 tv_vg (z0, z0)]) in Hw1.
  pose proof (SPJ_JGA_move_back segs C_P NP Kc rho0 (P0_fs FB) FB tv7 [(xAR, SLit 64)] (nth 8 tv_vg (z0, z0)) apH X_vg2 rho w Hw1) as Hw2.
  change (tv7 ++ nth 8 tv_vg (z0, z0) :: [(xAR, SLit 64)]) with tv_vg' in Hw2.
  land X_vg2 P_ok (infer_sub NP X_vg2 P_ok) tv_vg' tvOK apH amq Hw2.
Qed.

Lemma exits_okT : ltac2:(tb__ "0|4|
S2S15S14S3S3A2A1M0S56S14S12S3A2M1S1S7bS14S14S2S14G0S56A2M2A2M3G1A2S16G3G1S16S2G2R5S16G0S56R4R3A4A4R2A4S4fA3VTR;S10S0VJGv;R5R4A2R6R2A4VFAM;S57S16G3G1S16S2G2R6S16G0S56R5R4A4A4R3A4R2A2A1A2F_;Frho;FrvX;FamX;FtvX;FX;").
Proof using CALLAD CALLVP CMALLOC MALLOC POST REENTER TR_exw nA.
  intros X tvX amX rvX rho Hin. cbn [exitsE nd In] in Hin.
  destruct Hin as [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[]]]]]]]]]]]]]]]]]]]]]]]]; injection H as <- <- <- <-;
    unfold ameas, ad_rank, ad_var, nd; cbn [fst snd]; try (pose proof (urange (eval rho z0))).
  - apply X_open_ok. lia.
  - apply X_fit_ok. lia.
  - apply X_nofit_ok. lia.
  - apply X_E_m.
  - apply X_mfail_ok. lia.
  - apply X_push_ok. lia.
  - apply X_nA_ok. lia.
  - apply X_nB_ok. lia.
  - apply X_E_ad1.
  - apply X_E_ad2.
  - apply X_E_ad3.
  - apply X_E_ad4.
  - apply X_E_ad5.
  - apply X_E_ad6.
  - apply X_E_ad7.
  - apply X_E_vp0.
  - apply X_vf_ok. lia.
  - apply X_vk_ok.
  - apply X_vg_ok.
  - apply X_P_nop.
  - apply X_P_ok.
  - apply X_P_fail.
  - apply X_P_failz.
Qed.
End SumT.

Section Safety.
Lemma CVP_safe : ltac2:(tb__ "0|2|
S15S14S12S12A2A1M0S1S7fS0Vok;S10S0S59S0S22VKc;G0S91L_;M1R2A1R2S92S5aS5S2eA1A1A7S8eR1A4S6fS0S67R1S5cS0S22VKc;G1S5bS31S2eA2R2A6A4A4Frho1;FFBc;").
Proof using HS MC ML.
  apply (JGA_frame_sum segs C_P Kc (fun _ => VR.P0_vr) VP.Pre_vp VR.tv0 PD_vp NF hVP ML).
  - reflexivity.
  - intros F F' r _ H. exact H.
  - intros FBc rho1. rewrite <- (Posts_vp_PD FBc). apply (VP.vec_push_sum ok Kc FBc rho1 HS ML MC).
Qed.

Theorem finalize_shape_sum : ltac2:(tb__ "0|0|
S7fS0Vok;S10S0S59S0S22VKc;S68VFB;A1VFB;S2aS2dA7S40Vrho0;A4S6fS0S2bVrho0;SabA4A4").
Proof using HS MC ML.
  eapply triple_conseq; [ | intros w Hw; exact Hw | ].
  2: { apply (cfg_sound_JGAE segs C_P NP Kc rho0 (P0_fs FB) FB ML FUEL_fs cutpcs_fs NP cutsE exitsE ok Q (proj1 HS)
                (ejcertA_jcertA segs NP _ _ _ _ _ ejcert_ok)) with (rvT := (100, z0)); [|left; reflexivity].
       apply (exits_okT (triple segs ok) (fun _ w => SPfamGJ segs (map nA (map (@adrop) cutsE)) w \/ Q w)
                (triple_factsJ segs ok) (triple_SPJ_ex segs ok)
                (fun P P' Q' HP H => @triple_conseq segs ok P P' Q' Q' HP (fun w Hw => Hw) H)
                (fun A P Q' H => @triple_ex segs ok A P Q' H)
                (call_soundP segs ok)).
       - intros Ai rho1. apply (mc_malloc _ _ _ MC). exact HS.
       - intros FBc rho1. rewrite <- (AD.Posts_ad_PDA Kc FBc). apply (AD.arena_dup_sum ok Kc FBc rho1 HS ML MC).
       - exact CVP_safe.
       - intros T tv am rT vT rho b Hin _ _. exact (reenter_cutGAE segs C_P NP Kc rho0 (P0_fs FB) FB ok cutsE T tv am (rT, vT) Q rho Hin).
       - intros P tv am rho b Hin. apply (exit_postGA segs C_P NP Kc (P0_fs FB) FB ok rho0 tv am Posts_fs P). exact Hin. }
  intros w Hw. apply JGA_pre_intro. exact Hw.
Qed.
End Safety.

Section Existence.
Hypothesis Hvi : vm_insensitive Kc.
Hypothesis MCX : ltac2:(tb__ "0|0|
Sa2S0S22S85A3").

Lemma CVP_ex : ltac2:(tb__ "0|2|
S15S14S12S12A2A1M0S1S7eS0S10S0S59S0S22VKc;G0S91L_;M1R2A1R2S92S5aS5S2eA1A1A7S8eR1A4S6fS0S67R1S5cS0S22VKc;G1S5bS31S2eA2R2A6A4A3Frho1;FFBc;").
Proof using Hvi MCX ML.
  apply (JGA_frame_sum_ex segs C_P Kc (fun _ => VR.P0_vr) VP.Pre_vp VR.tv0 PD_vp NF hVP ML).
  - reflexivity.
  - intros F F' r _ H. exact H.
  - intros FBc rho1. rewrite <- (Posts_vp_PD FBc). apply (VP.vec_push_sum_ex Kc FBc rho1 ML Hvi MCX).
Qed.

Theorem finalize_shape_sum_ex : ltac2:(tb__ "0|0|
S7eS0S10S0S59S0S22VKc;S68VFB;A1VFB;S2aS2dA7S40Vrho0;A4S6fS0S2bVrho0;SabA4A3").
Proof using Hvi MCX ML.
  eapply etriple_conseq; [ | intros w Hw; exact Hw | ].
  2: { apply (cfg_complete_JGA segs C_P NP Kc rho0 (P0_fs FB) FB ML FUEL_fs cutpcs_fs NP cutsE exitsE Q ejcert_ok) with (rvT := (100, z0)); [|left; reflexivity].
       apply (exits_okT (etriple segs) (fun b w => SPfamEJ segs (map (enodeA segs C_P NP Kc rho0 (P0_fs FB) FB) cutsE) b w \/ Q w)
                (etriple_factsJ segs) (etriple_SPJ_ex segs)
                (fun P P' Q' HP H => @etriple_conseq segs P P' Q' Q' HP (fun w Hw => Hw) H)
                (fun A P Q' H => @etriple_ex segs A P Q' H)
                (call_completeP segs)).
       - intros Ai rho1. apply (mcx_malloc _ _ _ MCX). exact Hvi.
       - intros FBc rho1. rewrite <- (AD.Posts_ad_PDA Kc FBc). apply (AD.arena_dup_sum_ex Kc FBc rho1 ML Hvi MCX).
       - exact CVP_ex.
       - intros T tv am rT vT rho b Hin H0 Hb. apply (ereenter_cutAE segs C_P NP Kc rho0 (P0_fs FB) FB cutsE T tv am (rT, vT) Q b rho Hin).
         unfold ameas, ad_rank, ad_var. cbn [fst snd]. pose proof (urange (eval rho vT)). nia.
       - intros P tv am rho b Hin. apply (eexit_postGA segs C_P NP Kc (P0_fs FB) FB rho0 tv am Posts_fs P). exact Hin. }
  intros w Hw. apply JGA_pre_intro. exact Hw.
Qed.
End Existence.
End Sum.
