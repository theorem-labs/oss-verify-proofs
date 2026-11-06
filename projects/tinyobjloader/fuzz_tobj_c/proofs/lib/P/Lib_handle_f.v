(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sstate"; "valuation"; "ss_next"; "sobj"; "smatch"; "sprop"; "ss_facts"; "agree_below"; "holds"; "obj_range"; "sprop_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Code"; "segs"; "@Corelib.Init.Datatypes"; "prod"; "pair"; "list"; "bool"; "true"; "app"; "fst"; "Some"; "option"; "nil"; "snd"; "cons"; "andb"; "nat"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "SPJ"; "jpred"; "LQ"; "SP"; "LQJ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G1.Lib_handle_f_defs"; "tvH"; "NP"; "HF_P"; "P0_hf"; "PD_vr"; "HP_degen"; "HP_ret"; "Pre_hf"; "pC"; "tv_pre"; "E_co"; "E_fv"; "E_fv2"; "E_mi"; "E_mi2"; "E_mm"; "E_mm2"; "E_pc"; "E_rp"; "E_sg"; "E_sg2"; "E_tp"; "E_tr_bad"; "E_tr_ok"; "E_ts"; "is_txt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "C_P"; "topL"; "@Corelib.Init.Logic"; "eq"; "and"; "ex"; "eq_refl"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "emeas"; "JG"; "JG_pre"; "FBx"; "JLG"; "pdesc"; "tv_below"; "PostsC"; "T_afterN"; "T_ok"; "call_checkT"; "client_callT"; "ejcert"; "fbin"; "import_tv"; "malloc_contracts"; "malloc_contracts_ex"; "new_objs_tv"; "nodeI"; "pclF"; "pure_callT"; "robjs_okF"; "tvL_ok"; "tv_sub_eqb"; "tvd"; "tvin"; "tvz"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "etriple"; "world"; "triple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G1.Lib_handle_f_nodes"; "z0"; "VL"; "VT"; "hf_cuts"; "hf_exits"; "FUEL"; "cps"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "jpost"; "agree_vals"; "LQP"; "import_post"; "call_check"; "J_ofP"; "call_checkP"; "call_link"; "call_linkP"; "import_okP"; "import_sub"; "wsub_dom_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@Stdlib.Lists.List"; "In"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "leaf"; "lf_state"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_absorb"; "rho_sub"; "wsub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_vec__G1.Lib_vec_reserve"; "Pre_vr"; "P0_vr"; "tv0"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "entails_fr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVx"; "emeasZ"; "contE_TR"; "contE_check"; "entE_TR"; "entE_check"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle_f.Sum"; "Posts_hf"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract"; "EC_P"; "MInvR"; "ok_sideK"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_tess__G1.Lib_tess_polygon_defs"; "PG_P"; "Pre_pg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_tess__G2.Lib_tess_polygon_chk"; "Posts_pg"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@Stdlib.Sorting.Permutation"; "Permutation"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "add_facts"; "jnode";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform"; "xform"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface"; "MA"; "ma_L"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_parse_corner"; "Posts_pc"; "Pre_pc"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Contract.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CfgGlue CursorGlue ObjUnbase ObjXform TobjJV TobjJVx.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_vec__G1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_parse_corner OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_tess__G1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_tess__G2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_tess__G3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_tess_polygon_ex OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_vec__G1.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_parse_corner OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_tess__G1.Lib_tess_run2d OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_tess__G1.Lib_tess_polygon_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_tess__G2.Lib_tess_polygon_chk OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_tess__G3.Lib_tess_polygon OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_tess_polygon_ex OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G1.Lib_handle_f_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G1.Lib_handle_f_nodes OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G1.Lib_handle_f_arith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G2.Lib_handle_f_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G4.Lib_handle_f_s1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G5.Lib_handle_f_s2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G5.Lib_handle_f_s3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G6.Lib_handle_f_s4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G3.Lib_handle_f_s5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G6.Lib_handle_f_s6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G2.Lib_handle_f_c1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G3.Lib_handle_f_c2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G3.Lib_handle_f_c3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G2.Lib_handle_f_c4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G3.Lib_handle_f_c5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G4.Lib_handle_f_c6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Local Notation h := HF_P.

Definition tess_polygon_sum_ex_stmt : Prop := ltac2:(tb__ "0|0|
SfS5eA1S5dOF_;F_;S2S60ScS20ScR2S93S92S16S6A1A2R1A4S1fScR2S76R1S94A5A3Frho;FK;").
Lemma tess_polygon_sum_ex_ok : tess_polygon_sum_ex_stmt.
Proof. exact tess_polygon_sum_ex. Qed.

Section Sum.
Variable Kc : ltac2:(tb__ "0|0|
SfS5eA1S5dOF_;F_;").
Variable FB : list (Z * Z).
Variable rho0 : valuation.
Hypothesis ML : malloc_laws segs C_P.

Definition Posts_hf : list (sstate * jpost) := ltac2:(tb__ "0|2|
S18SdS1S6aA2M0SeS1S6aS28S24A1S46ScS3cVKc;S25VFB;A1VFB;S22A6M1A4S18G0SeS1S6aS27S24A1G1A4S16G0A1A3A3").
Let nI : ltac2:(tb__ "0|0|
SdS1SfSdS0S0A2A1A2S98Fn;") := ltac2:(tb__ "0|0|
S54ScS3cS23VKc;Vrho0;S25VFB;A1VFB;A7").
Let JGv (tv : list (sv * sv)) : jpred := ltac2:(tb__ "0|0|
S43ScS3cS23VKc;Vrho0;S25VFB;A1VFB;Vtv;A8").
Let Q : assn := ltac2:(tb__ "0|0|
S6cScS23Vrho0;S8aA4").

Lemma ejcert_ok : ltac2:(tb__ "0|0|
S3eS10S4eScS23S68S69S24A1S23S66S24A1S67S24A1A7S11A3").
Proof using .
  apply (ejcert_of_cuts segs NP FUEL (cps h) NP (hf_cuts h) (hf_exits h)). intros i n H.
  destruct i as [|i]; [cbn [hf_cuts nth_error] in H; injection H as <-; exact ec_Pre_hf |].
  destruct i as [|i]; [cbn [hf_cuts nth_error] in H; injection H as <-; exact ec_T50 |].
  destruct i as [|i]; [cbn [hf_cuts nth_error] in H; injection H as <-; exact ec_T60 |].
  destruct i as [|i]; [cbn [hf_cuts nth_error] in H; injection H as <-; exact ec_T94 |].
  destruct i as [|i]; [cbn [hf_cuts nth_error] in H; injection H as <-; exact ec_TA |].
  destruct i as [|i]; [cbn [hf_cuts nth_error] in H; injection H as <-; exact ec_FA |].
  destruct i as [|i]; [cbn [hf_cuts nth_error] in H; injection H as <-; exact ec_TP0 |].
  destruct i as [|i]; [cbn [hf_cuts nth_error] in H; injection H as <-; exact ec_TP |].
  destruct i as [|i]; [cbn [hf_cuts nth_error] in H; injection H as <-; exact ec_R1 |].
  destruct i as [|i]; [cbn [hf_cuts nth_error] in H; injection H as <-; exact ec_F1 |].
  destruct i as [|i]; [cbn [hf_cuts nth_error] in H; injection H as <-; exact ec_R2 |].
  destruct i as [|i]; [cbn [hf_cuts nth_error] in H; injection H as <-; exact ec_F2 |].
  destruct i as [|i]; [cbn [hf_cuts nth_error] in H; injection H as <-; exact ec_R3 |].
  destruct i as [|i]; [cbn [hf_cuts nth_error] in H; injection H as <-; exact ec_F3 |].
  destruct i as [|i]; [cbn [hf_cuts nth_error] in H; injection H as <-; exact ec_R4 |].
  destruct i as [|i]; [cbn [hf_cuts nth_error] in H; injection H as <-; exact ec_F4 |].
  destruct i as [|i]; [cbn [hf_cuts nth_error] in H; injection H as <-; exact ec_K1 |].
  destruct i as [|i]; [cbn [hf_cuts nth_error] in H; injection H as <-; exact ec_KT_ok |].
  destruct i as [|i]; [cbn [hf_cuts nth_error] in H; injection H as <-; exact ec_KT_bad |].
  destruct i as [|i]; [cbn [hf_cuts nth_error] in H; injection H as <-; exact ec_FT |].
  destruct i as [|i]; [cbn [hf_cuts nth_error] in H; injection H as <-; exact ec_K2 |].
  destruct i as [|i]; [cbn [hf_cuts nth_error] in H; injection H as <-; exact ec_J9c |].
  destruct i as [|i]; [cbn [hf_cuts nth_error] in H; injection H as <-; exact ec_KR |].
  destruct i as [|i]; [cbn [hf_cuts nth_error] in H; injection H as <-; exact ec_FR |].
  destruct i as [|i]; [cbn [hf_cuts nth_error] in H; injection H as <-; exact ec_K3 |].
  destruct i as [|i]; [cbn [hf_cuts nth_error] in H; injection H as <-; exact ec_KQ |].
  destruct i as [|i]; [cbn [hf_cuts nth_error] in H; injection H as <-; exact ec_FQ |].
  destruct i as [|i]; [cbn [hf_cuts nth_error] in H; injection H as <-; exact ec_KP_ok |].
  destruct i as [|i]; [cbn [hf_cuts nth_error] in H; injection H as <-; exact ec_KP_inv |].
  destruct i as [|i]; [cbn [hf_cuts nth_error] in H; injection H as <-; exact ec_L14 |].
  destruct i as [|i]; [cbn [hf_cuts nth_error] in H; injection H as <-; exact ec_A_mi2 |].
  destruct i as [|i]; [cbn [hf_cuts nth_error] in H; injection H as <-; exact ec_F_mi2 |].
  destruct i as [|i]; [cbn [hf_cuts nth_error] in H; injection H as <-; exact ec_A_fv2 |].
  destruct i as [|i]; [cbn [hf_cuts nth_error] in H; injection H as <-; exact ec_F_fv2 |].
  destruct i as [|i]; [cbn [hf_cuts nth_error] in H; injection H as <-; exact ec_A_mm2 |].
  destruct i as [|i]; [cbn [hf_cuts nth_error] in H; injection H as <-; exact ec_F_mm2 |].
  destruct i as [|i]; [cbn [hf_cuts nth_error] in H; injection H as <-; exact ec_A_sg2 |].
  destruct i as [|i]; [cbn [hf_cuts nth_error] in H; injection H as <-; exact ec_F_sg2 |].
  destruct i; cbn [hf_cuts nth_error] in H; discriminate.
Qed.

Lemma txt_extra_ok : ltac2:(tb__ "0|1|
S2SfSdS0S0A2A1SfS4A1S4S1bS25VFB;Vrho0;A2S6bS23Vrho0;R6A3S77S4R4R5A3S3eS10S3bR5A1S11A3S3fS8bS13S1bS1bSaR9R6A2M0A3R5A2S8cR5S17S1bS1bG0A3A2A2S55ScS3cVrho0;S45VFB;RaR9A3R6A5F_;F_;F_;F_;F_;Fa;Fo;FR;Fkept;Frho;").
Proof using JGv.
  intros rho kept R o a HP0 Hav Ho Ht Hr. unfold is_txt in Ht.
  apply andb_prop in Ht as [Ht H3]. apply andb_prop in Ht as [H1 H2].
  apply sv_eqb_sound in H1. apply sv_eqb_sound in H2. apply sv_eqb_sound in H3.
  unfold obj_range, obj_lo_of, obj_hi_of in Hr. rewrite H1, H2, H3 in Hr. cbn [fst snd] in Hr.
  unfold xB, xL in Hr. rewrite soff_lit_small in Hr by lia. unfold soff in Hr. rewrite !eval_var in Hr.
  destruct Hav as [Hw _]. rewrite <- (Hw 100%positive ltac:(reflexivity)), <- (Hw 101%positive ltac:(reflexivity)) in Hr.
  rewrite bv_signed_U in Hr.
  right; right.
  pose proof (bv_urange (rw rho0 101)) as R101.
  destruct HP0 as [Hz | (b & n & Hin & Hb & Hbn)].
  - exfalso. rewrite Hz in Hr. destruct (Zsigned_spec 0) as [[_ X]|[X1 X]]; rewrite X in Hr; lia.
  - exists b, n. split; [apply in_or_app; left; exact Hin|].
    destruct (Zsigned_spec (bv_unsigned (rw rho0 101))) as [[_ X]|[X1 X]]; rewrite X in Hr; unfold M64v in *; lia.
Qed.

Section SumT.
Variable TR : assn -> assn -> Prop.
Variable FAM : Z -> assn.
Hypothesis TR_facts : ltac2:(tb__ "0|1|
S1eS1S2S5fS8dS6S9R2A1S7R3A1A3VTR;S1dScR5R4R3A4R2A2M0F_;G0F_;FQ';Frho;FS;FJ;").
Hypothesis TR_ex : forall (A : Type) (J : A -> jpred) S rho (Q' : assn),
  (forall x, TR (SPJ segs (J x) S rho) Q') -> TR (SPJ segs (fun r t m => exists x, J x r t m) S rho) Q'.
Hypothesis TR_pre : ltac2:(tb__ "0|0|
S5fS5fS5fS61R3R1A1R5R2A1F_;Fw;VTR;R4R2A2VTR;R4R3A2F_;F_;FQ';FP';FP;").
Hypothesis TR_exw : forall (A : Type) (P : A -> assn) (Q' : assn), (forall a, TR (P a) Q') -> TR (fun w => exists a, P a w) Q'.
Hypothesis TR_pureh : ltac2:(tb__ "0|0|
OS5fS5fR3VTR;R3R2A2F_;VTR;S61S3fR5R4R1A1A2Lw;R2A2F_;FQ';FP;FX;").
Hypothesis TR_callP : ltac2:(tb__ "0|3|
S1eS1eS1S1S7eSfS4A1M0SfSdS1S6aA2M1A1S5fS2S3eS15G0A1S84R7R6R5A3S14G0R4A2A3S3eS10S70R8R7R6R5S8eG1S1S13S1S6aA2R4A4A5S11A3S2VTR;S1dScRbR9R1A4S6cScS3R9A1R1R6A4A2Frho1;SfS5eA1M2S7bS5dS5ScR7RdSeG2S82R3S83R2R1A2A4A4R10R8R4R2A3R10S7dS7cR9RcR4A3RdA2R5R3A3F_;F_;Fmd;Fms;Ftr;S1S6aG2S7bS5dS2G2S7bS5dS77G1SeS1S6aR9R8A4R10A3S5ScRfR15SeG2S82R8S83R7R6A2A4A4R18R10R9R7A3S6bS3R16A1S7dS7cR11R14R9A3R15A2R7A3S5ScR8RdSeG2S82R7S83R6R5A2A4A4RdS7dS7cR13R16RbA3R17A2R9R8R6A4S3fS73R14RcR17R18R19RfRaA7S2S72R15RdR18R19R1aR1bR10R1RbA9VTR;S1dScS6fR10S7dS7cR16R19ReA3R1aA2RcA3S6dR1aS3R1bA1R11S3R1cA1R19A5R2A4R17A2F_;Frho';A2F_;F_;F_;F_;F_;F_;Fmd';Fms';Ftr';FrhoL;Fmd;Fms;Ftr;FJL;FL;VTR;S1dScReRcR6A4R7A2F_;F_;F_;F_;F_;Frho;FQ';FPosts;FR;Fs;FPre;FC;FJp;FJ;").
Hypothesis TR_callJ : ltac2:(tb__ "0|3|
S1eS1eS1eS1eS1S1S7eSfS4A1M0SfS79A1S5fS2S3eS15G0A1S84R7R6R5A3S14G0R4A2A3S3eS10S6eR8R7R6R5R4A5S11A3S2VTR;S1dScRdR9R1A4S21ScRcS3R9A1R1R6A5A2Frho1;SfS5eA1M1S7bS5dS5ScR7RdSeG1S82R3S83R2R1A2A4A4R12R8R4R2A3R12S7dS7cR9RcR4A3RdA2R5R3A3F_;F_;Fmd;Fms;Ftr;S79S2S2G1S7bS5dG1S5dS77S79R8RfA3S5ScReR14SeG1S82R6S83R5R4A2A4A4R19RfR7R5A3S71R10R7R13R14R15R16S7aRbA1RaR9A9R19RaR6R5A3R19RcR7R6A3F_;F_;F_;F_;F_;Fmd';Ftr';Fmd;Fms;Ftr;FrhoL;Frho';FL;S79S2S77S79R2RaA3S8S3RfA1M2R9R2A3VTR;S1dScR11S6dReG2S7aR4A1S3R10A1RdA5R3A4RbA2F_;F_;Frho';FL;VTR;S1dScR11RdR7A4R8A2F_;F_;F_;F_;F_;F_;Frho;FQ';FPosts;FR;Fs;FPre;FC;FJc';FJp';FJp;FJ;").

Hypothesis CVR : ltac2:(tb__ "0|1|
SfSdS1bS1bA2A1M0S2VTR;S1dScS44ScS3cVKc;S80R2S81A6S7fR1A4S6cScS76R1S49ScS3cVKc;G0S80L_;S26R2A6A4A2Frho1;FFBc;").
Hypothesis CPC : ltac2:(tb__ "0|1|
SfSdS0S0A2A1S2S2VTR;S20ScSfS5eA1S5dVJGv;R5R4R2R1A4Lmd;Ltr;M0S9dR1A4S1fScG0S76R1S9cA5A2Frho1;Frho;Ftv;").
Hypothesis CTP : ltac2:(tb__ "0|1|
SfSdS0S0A2A1S2S2VTR;S20ScSfS5eA1S5dVJGv;R5R4R2R1A4Lmd;Ltr;M0S93S92S16S6A1A2R1A4S1fScG0S76R1S94A5A2Frho1;Frho;Ftv;").

Hypothesis REENTER : ltac2:(tb__ "0|4|
S1SfSdS0S0A2A1M0SdS1bS0A2M1S2S1bS77SdSdS1G0A2M2G1A2SeG2G1SeS1G0R5R4A4R3A4S66S24A1A3S3fS8bZ0S42SeG2G1SeS1G0R6R5A4R4A4R3A2M3A2S8cG3R2A2A2VTR;S1dScVJGv;R6A1R7R4A4VFAM;R3A1A2F_;F_;Fb;Frho;Frv;Ftv;FT;").
Hypothesis POST : ltac2:(tb__ "0|0|
S1SfSdS0S0A2A1S2S1bS77SdS1S6aA2SeS1S6aR4S46ScS3cVKc;S25VFB;A1VFB;R3A6A4S8aA3VTR;S1dScVJGv;R4A1R5R3A4VFAM;R2A1A2F_;Fb;Frho;Ftv;FP;").

Let PURE : ltac2:(tb__ "0|4|
S1S1S7eSfS4A1M0SfS79A1S2SfSdS0S0A2A1S5fS2VTR;S20ScSfS5eA1S5dS43ScS3cS23VKc;Vrho0;S25VFB;A1M1VFB;R5R6R2R1AbLmd;Ltr;M2R8R1A4S1fScG2S3R8A1R1R5A5A2Frho1;S3eS15G0A1S84R9R8R7A3S14G0R6A2A3S3eS10S6eRaR9R8R7R6A5S11A3S3eS10S95S23S3RbA1A2S11A3S3eS10S48S3RcA1R6A2S11A3S3eS10S78S6SbS3RdA1A1S7RdA1A3S11A3S79S2S77S79R2RcA3S8S3R11A1M3RcR2A3VTR;S1dScS43ScS3cS23VKc;Vrho0;G1VFB;RcA8S97S7R12A1S6dR10G3S7aR4A1S3R12A1RfA5A2R3A4RbA2F_;F_;Frho';FL;VTR;S1dScS43ScS3cS23VKc;Vrho0;G1VFB;R9A8RfRaA4R8A2F_;F_;F_;F_;F_;F_;F_;FQ;Ftv;Frho;FPosts;FR;Fs;FPre;FCl;") := ltac2:(tb__ "0|0|
S56ScS3cS23VKc;Vrho0;S25VFB;A1VFB;VML;VTR;VTR_facts;VTR_pre;VTR_callJ;Ac").
Let CLIENT : ltac2:(tb__ "0|8|
S1S7eSfS4A1M0S2SfSdS0S0A2M1A1M2G2S5fS3eS15G0A1S84R7S7fR6A3S14G0R5A2A3S3eS10S4cS3cS23R8S7fR7R6S8eSdS1G2A2M3S1S13S1G2A2S26A4A7S11A3S3eS10S75R8S76A2S11A3S3eS10S95S23S3RaA1A2S11A3S3eS10S48S3RbA1S12G1R7R6A3A2S11A3S3eS10S59RbR7S81A3S11A3S3eS10S78G3G3S19S58S76RdS3ReA1S13S1G2R1A3M4S17S1G2R1A3M5A5S53S7fG4G5A3A2Ld;S26A3S11A3S9aS7bS8dS6S9RdA1S7R10A1A3S25VFB;Vrho0;A2S6bS23Vrho0;RfA3S4fVFB;R5A2S5bVFB;R6R11S12G1R10RfA3A4S5aR12S12G1R11R10A3A2S5cR13S12G1R12R11A3A2S40S2S2S40S5dS5dS90ScS3cRbR2R1A5Lmd;A2LrhoM;A2S4bR15S3dS9bRaA1A1A2S3fS57ScS3cVrho0;VFB;R16R15R17A7SfSdS1bS1bA2A1S80L_;S45VFB;R16R15A3S7dS7cR16R17RaA3R18A2A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;Fms;FAi;S47S2S77S47R2S26A3S6bS3R12A1RfR2A3VTR;S1dScS43ScS3cS23VKc;Vrho0;S25VFB;A1M6VFB;S12G1RfS50S74R12S76S13S1G2R4A3M7S3R13A1A4S17S1G2R4A3A2A3A8S4aS76R13R12R11G7A5R3A4RdA2F_;F_;Frho';Fd;VTR;S1dScS43ScS3cS23VKc;Vrho0;G6VFB;S12G1RcRbA3A8R10RdA4RaA2F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Fpassed;Fkept;Frho;FR;Fs;FCl;") := ltac2:(tb__ "0|0|
S4dScS3cS23VKc;Vrho0;S25VFB;A1VFB;VML;SfSdS1bS1bA2A1S80L_;S7fS81S26S76S41S1cS3S7fA1A2VTR;VTR_facts;VTR_ex;VTR_pre;VTR_callP;VCVR;A14").
Let CONT : ltac2:(tb__ "0|4|
SfS99A1S1aS1bS1cS1S1SfSdS0S0A2M0A1M1G1G1S0S1bS1bS0S2S2S5fS3eS10S87S23R10RfReRdRcRbRaR9R7R6R5R4AdS11A3S96G0RaR9A3S6bRfR5R4A3S2S3fS8bZ0S85RaRbR1A3M2A2S8cG2S85R9R8R7A3A2A2VTR;S1dScS43ScS3cS23VKc;Vrho0;S25VFB;A1M3VFB;RdA8R10R2A4R6A2F_;Frho';VTR;S1dScS43ScS3cS23VKc;Vrho0;G3VFB;ReA8R10R6A4R5A2F_;F_;F_;F_;FFAMb;Frho;FrhoX;FvE;FrE;FrA;FvA;Ftvj';Ftvj;Ftvi;FA;FT;Fn;Fc;Fi;Fxs;") := ltac2:(tb__ "0|0|
S86ScS3cS23VKc;Vrho0;S25VFB;A1VFB;VML;VTR;VTR_pre;VTR_exw;VTR_pureh;Ac").
Let ENT : ltac2:(tb__ "0|4|
S1cS1S1SfSdS0S0A2M0A1M1G1G1S0S1bS1bS0S2S2S5fS3eS10S89S23RdRcRbRaR9R7R6R5R4AaS11A3S96G0RaR9A3S6bRfR5R4A3S2S3fS8bZ0S85RaRbR1A3M2A2S8cG2S85R9R8R7A3A2A2VTR;S1dScS43ScS3cS23VKc;Vrho0;S25VFB;A1M3VFB;RdA8R10R2A4R6A2F_;Frho';VTR;S1dScS43ScS3cS23VKc;Vrho0;G3VFB;ReA8R10R6A4R5A2F_;F_;F_;F_;FFAMb;Frho;FrhoX;FvE;FrE;FrA;FvA;Ftvj';Ftvj;Ftvi;FA;FX;Fn;") := ltac2:(tb__ "0|0|
S88ScS3cS23VKc;Vrho0;S25VFB;A1VFB;VML;VTR;VTR_pre;VTR_exw;VTR_pureh;Ac").

Lemma X_HP_ret : ltac2:(tb__ "0|2|
S2VTR;S1dScVJGv;S22A1S28S24A1M0R1A4VFAM;S42SeSdS1SfSdS0S0A2A1M1A2SdS1bS0A2SeS1G1G0S22A4SeS1bS0Z0S63A4A4R1A2A1A2Frho;").
Proof using POST nI. intros rho. apply POST. cbn. tauto. Qed.
Lemma X_HP_degen : ltac2:(tb__ "0|2|
S2VTR;S1dScVJGv;S22A1S27S24A1M0R1A4VFAM;S42SeSdS1SfSdS0S0A2A1M1A2SdS1bS0A2SeS1G1G0S22A4SeS1bS0Z0S63A4A4R1A2A1A2Frho;").
Proof using POST nI. intros rho. apply POST. cbn. tauto. Qed.

Lemma X_E_co : ltac2:(tb__ "0|2|
S2VTR;S1dScVJGv;S22A1S2cS24A1M0R1A4VFAM;S42SeSdS1SfSdS0S0A2A1M1A2SdS1bS0A2SeS1G1G0S22A4SeS1bS0Z5aS65S2aZ7A2A4A4R1A2A1A2Frho;").
Proof using CLIENT CONT REENTER nI.
  intros rho.
  destruct (vr_site_checkEP _ _ _ _ _ _ _ _ _ _ _ chk_co) as (R & HE & C1 & Cd & Cn & Cb & Cs & Cp & C2 & C3 & C4 & C5).
  eapply TR_pre.
  2: { apply (CLIENT E2_co s_co R rho (keptH 5) [tvH_x 5] _ HE C1 Cd Cn Cb Cs Cp).
  -
    intros Ai ms HF HP0 Hav _ _ _ HZ _ HT. split.
    + eapply robjs_checkF_sound; [exact HF | exact (TobjJVx.T_ok_T0_agree _ _ _ _ Hav (@eq_refl comparison Lt) HT) | | exact C2 |].
      * unfold tvz in *. apply Forall_forall. intros t Ht. apply (proj1 (Forall_forall _ _) HZ). apply in_or_app. left. exact Ht.
      * intros o a Ho Hx Hr. eapply txt_extra_ok; eauto.
    + cbn beta. eapply (P0_vr_of_tvz rho 312 314 12); [reflexivity | reflexivity | | | lia].
      * unfold tvz in *. constructor; [|constructor]. apply (proj1 (Forall_forall _ _) HZ). apply in_or_app. right. left. reflexivity.
      * eapply (proj1 (Forall_forall _ _) HF). vm_compute. tauto.
  -
    intros d rho' Hd Hag. destruct Hd as [<-|[<-|[<-|[]]]]; cbn [fst snd].
    + eapply (CONT _ _ _ _ _ _ _ _ tvH _ _ _ _ rho rho' _ C3); [apply Permutation_sym; apply (perm_move_last (tvH_l1 5) (tvH_l2 5) (tvH_x 5)) | exact Hag |].
      intros rho'' Hm. apply (REENTER (TA h) tvH (90, VT pC 6) rho''); [apply (nth_error_in _ 4); reflexivity | exact Hm].
    + eapply (CONT _ _ _ _ _ _ _ _ tvH _ _ _ _ rho rho' _ C4); [apply Permutation_sym; apply (perm_move_last (tvH_l1 5) (tvH_l2 5) (tvH_x 5)) | exact Hag |].
      intros rho'' Hm. apply (REENTER (FA h) tvH (85, z0) rho''); [apply (nth_error_in _ 5); reflexivity | exact Hm].
    + eapply (CONT _ _ _ _ _ _ _ _ tvH _ _ _ _ rho rho' _ C5); [apply Permutation_sym; apply (perm_move_last (tvH_l1 5) (tvH_l2 5) (tvH_x 5)) | exact Hag |].
      intros rho'' Hm. apply (REENTER (TA h) tvH (90, VT pC 6) rho''); [apply (nth_error_in _ 4); reflexivity | exact Hm].
  }
  intros w Hw. apply (SPJ_norm_xu segs _ _ _ _ _ _ rho w view_co).
  apply (SPJ_JG_move_last segs C_P NP Kc rho0 (P0_hf FB) FB (tvH_l1 5) (tvH_l2 5) (tvH_x 5)). exact Hw.
Qed.

Lemma X_E_mi : ltac2:(tb__ "0|2|
S2VTR;S1dScVJGv;S22A1S2fS24A1M0R1A4VFAM;S42SeSdS1SfSdS0S0A2A1M1A2SdS1bS0A2SeS1G1G0S22A4SeS1bS0Z50S63A4A4R1A2A1A2Frho;").
Proof using CLIENT CONT REENTER nI.
  intros rho.
  destruct (vr_site_checkEP _ _ _ _ _ _ _ _ _ _ _ chk_mi) as (R & HE & C1 & Cd & Cn & Cb & Cs & Cp & C2 & C3 & C4 & C5).
  eapply TR_pre.
  2: { apply (CLIENT E2_mi s_mi R rho (keptH 1) [tvH_x 1] _ HE C1 Cd Cn Cb Cs Cp).
  -
    intros Ai ms HF HP0 Hav _ _ _ HZ _ HT. split.
    + eapply robjs_checkF_sound; [exact HF | exact (TobjJVx.T_ok_T0_agree _ _ _ _ Hav (@eq_refl comparison Lt) HT) | | exact C2 |].
      * unfold tvz in *. apply Forall_forall. intros t Ht. apply (proj1 (Forall_forall _ _) HZ). apply in_or_app. left. exact Ht.
      * intros o a Ho Hx Hr. eapply txt_extra_ok; eauto.
    + cbn beta. eapply (P0_vr_of_tvz rho 300 302 12); [reflexivity | reflexivity | | | lia].
      * unfold tvz in *. constructor; [|constructor]. apply (proj1 (Forall_forall _ _) HZ). apply in_or_app. right. left. reflexivity.
      * eapply (proj1 (Forall_forall _ _) HF). vm_compute. tauto.
  -
    intros d rho' Hd Hag. destruct Hd as [<-|[<-|[<-|[]]]]; cbn [fst snd].
    + eapply (CONT _ _ _ _ _ _ _ _ tvH _ _ _ _ rho rho' _ C3); [apply Permutation_sym; apply (perm_move_last (tvH_l1 1) (tvH_l2 1) (tvH_x 1)) | exact Hag |].
      intros rho'' Hm. apply (REENTER (R1 h) tvH (79, z0) rho''); [apply (nth_error_in _ 8); reflexivity | exact Hm].
    + eapply (CONT _ _ _ _ _ _ _ _ tvH _ _ _ _ rho rho' _ C4); [apply Permutation_sym; apply (perm_move_last (tvH_l1 1) (tvH_l2 1) (tvH_x 1)) | exact Hag |].
      intros rho'' Hm. apply (REENTER (F1 h) tvH (79, z0) rho''); [apply (nth_error_in _ 9); reflexivity | exact Hm].
    + eapply (CONT _ _ _ _ _ _ _ _ tvH _ _ _ _ rho rho' _ C5); [apply Permutation_sym; apply (perm_move_last (tvH_l1 1) (tvH_l2 1) (tvH_x 1)) | exact Hag |].
      intros rho'' Hm. apply (REENTER (R1 h) tvH (79, z0) rho''); [apply (nth_error_in _ 8); reflexivity | exact Hm].
  }
  intros w Hw. apply (SPJ_norm_xu segs _ _ _ _ _ _ rho w view_mi).
  apply (SPJ_JG_move_last segs C_P NP Kc rho0 (P0_hf FB) FB (tvH_l1 1) (tvH_l2 1) (tvH_x 1)). exact Hw.
Qed.

Lemma X_E_fv : ltac2:(tb__ "0|2|
S2VTR;S1dScVJGv;S22A1S2dS24A1M0R1A4VFAM;S42SeSdS1SfSdS0S0A2A1M1A2SdS1bS0A2SeS1G1G0S22A4SeS1bS0Z4eS63A4A4R1A2A1A2Frho;").
Proof using CLIENT CONT REENTER nI.
  intros rho.
  destruct (vr_site_checkEP _ _ _ _ _ _ _ _ _ _ _ chk_fv) as (R & HE & C1 & Cd & Cn & Cb & Cs & Cp & C2 & C3 & C4 & C5).
  eapply TR_pre.
  2: { apply (CLIENT E2_fv s_fv R rho (keptH 2) [tvH_x 2] _ HE C1 Cd Cn Cb Cs Cp).
  -
    intros Ai ms HF HP0 Hav _ _ _ HZ _ HT. split.
    + eapply robjs_checkF_sound; [exact HF | exact (TobjJVx.T_ok_T0_agree _ _ _ _ Hav (@eq_refl comparison Lt) HT) | | exact C2 |].
      * unfold tvz in *. apply Forall_forall. intros t Ht. apply (proj1 (Forall_forall _ _) HZ). apply in_or_app. left. exact Ht.
      * intros o a Ho Hx Hr. eapply txt_extra_ok; eauto.
    + cbn beta. eapply (P0_vr_of_tvz rho 303 305 4); [reflexivity | reflexivity | | | lia].
      * unfold tvz in *. constructor; [|constructor]. apply (proj1 (Forall_forall _ _) HZ). apply in_or_app. right. left. reflexivity.
      * eapply (proj1 (Forall_forall _ _) HF). vm_compute. tauto.
  -
    intros d rho' Hd Hag. destruct Hd as [<-|[<-|[<-|[]]]]; cbn [fst snd].
    + eapply (CONT _ _ _ _ _ _ _ _ tvH _ _ _ _ rho rho' _ C3); [apply Permutation_sym; apply (perm_move_last (tvH_l1 2) (tvH_l2 2) (tvH_x 2)) | exact Hag |].
      intros rho'' Hm. apply (REENTER (R2 h) tvH (77, z0) rho''); [apply (nth_error_in _ 10); reflexivity | exact Hm].
    + eapply (CONT _ _ _ _ _ _ _ _ tvH _ _ _ _ rho rho' _ C4); [apply Permutation_sym; apply (perm_move_last (tvH_l1 2) (tvH_l2 2) (tvH_x 2)) | exact Hag |].
      intros rho'' Hm. apply (REENTER (F2 h) tvH (77, z0) rho''); [apply (nth_error_in _ 11); reflexivity | exact Hm].
    + eapply (CONT _ _ _ _ _ _ _ _ tvH _ _ _ _ rho rho' _ C5); [apply Permutation_sym; apply (perm_move_last (tvH_l1 2) (tvH_l2 2) (tvH_x 2)) | exact Hag |].
      intros rho'' Hm. apply (REENTER (R2 h) tvH (77, z0) rho''); [apply (nth_error_in _ 10); reflexivity | exact Hm].
  }
  intros w Hw. apply (SPJ_norm_xu segs _ _ _ _ _ _ rho w view_fv).
  apply (SPJ_JG_move_last segs C_P NP Kc rho0 (P0_hf FB) FB (tvH_l1 2) (tvH_l2 2) (tvH_x 2)). exact Hw.
Qed.

Lemma X_E_mm : ltac2:(tb__ "0|2|
S2VTR;S1dScVJGv;S22A1S31S24A1M0R1A4VFAM;S42SeSdS1SfSdS0S0A2A1M1A2SdS1bS0A2SeS1G1G0S22A4SeS1bS0Z4cS63A4A4R1A2A1A2Frho;").
Proof using CLIENT CONT REENTER nI.
  intros rho.
  destruct (vr_site_checkEP _ _ _ _ _ _ _ _ _ _ _ chk_mm) as (R & HE & C1 & Cd & Cn & Cb & Cs & Cp & C2 & C3 & C4 & C5).
  eapply TR_pre.
  2: { apply (CLIENT E2_mm s_mm R rho (keptH 3) [tvH_x 3] _ HE C1 Cd Cn Cb Cs Cp).
  -
    intros Ai ms HF HP0 Hav _ _ _ HZ _ HT. split.
    + eapply robjs_checkF_sound; [exact HF | exact (TobjJVx.T_ok_T0_agree _ _ _ _ Hav (@eq_refl comparison Lt) HT) | | exact C2 |].
      * unfold tvz in *. apply Forall_forall. intros t Ht. apply (proj1 (Forall_forall _ _) HZ). apply in_or_app. left. exact Ht.
      * intros o a Ho Hx Hr. eapply txt_extra_ok; eauto.
    + cbn beta. eapply (P0_vr_of_tvz rho 306 308 4); [reflexivity | reflexivity | | | lia].
      * unfold tvz in *. constructor; [|constructor]. apply (proj1 (Forall_forall _ _) HZ). apply in_or_app. right. left. reflexivity.
      * eapply (proj1 (Forall_forall _ _) HF). vm_compute. tauto.
  -
    intros d rho' Hd Hag. destruct Hd as [<-|[<-|[<-|[]]]]; cbn [fst snd].
    + eapply (CONT _ _ _ _ _ _ _ _ tvH _ _ _ _ rho rho' _ C3); [apply Permutation_sym; apply (perm_move_last (tvH_l1 3) (tvH_l2 3) (tvH_x 3)) | exact Hag |].
      intros rho'' Hm. apply (REENTER (R3 h) tvH (75, z0) rho''); [apply (nth_error_in _ 12); reflexivity | exact Hm].
    + eapply (CONT _ _ _ _ _ _ _ _ tvH _ _ _ _ rho rho' _ C4); [apply Permutation_sym; apply (perm_move_last (tvH_l1 3) (tvH_l2 3) (tvH_x 3)) | exact Hag |].
      intros rho'' Hm. apply (REENTER (F3 h) tvH (75, z0) rho''); [apply (nth_error_in _ 13); reflexivity | exact Hm].
    + eapply (CONT _ _ _ _ _ _ _ _ tvH _ _ _ _ rho rho' _ C5); [apply Permutation_sym; apply (perm_move_last (tvH_l1 3) (tvH_l2 3) (tvH_x 3)) | exact Hag |].
      intros rho'' Hm. apply (REENTER (R3 h) tvH (75, z0) rho''); [apply (nth_error_in _ 12); reflexivity | exact Hm].
  }
  intros w Hw. apply (SPJ_norm_xu segs _ _ _ _ _ _ rho w view_mm).
  apply (SPJ_JG_move_last segs C_P NP Kc rho0 (P0_hf FB) FB (tvH_l1 3) (tvH_l2 3) (tvH_x 3)). exact Hw.
Qed.

Lemma X_E_sg : ltac2:(tb__ "0|2|
S2VTR;S1dScVJGv;S22A1S35S24A1M0R1A4VFAM;S42SeSdS1SfSdS0S0A2A1M1A2SdS1bS0A2SeS1G1G0S22A4SeS1bS0Z4aS63A4A4R1A2A1A2Frho;").
Proof using CLIENT CONT REENTER nI.
  intros rho.
  destruct (vr_site_checkEP _ _ _ _ _ _ _ _ _ _ _ chk_sg) as (R & HE & C1 & Cd & Cn & Cb & Cs & Cp & C2 & C3 & C4 & C5).
  eapply TR_pre.
  2: { apply (CLIENT E2_sg s_sg R rho (keptH 4) [tvH_x 4] _ HE C1 Cd Cn Cb Cs Cp).
  -
    intros Ai ms HF HP0 Hav _ _ _ HZ _ HT. split.
    + eapply robjs_checkF_sound; [exact HF | exact (TobjJVx.T_ok_T0_agree _ _ _ _ Hav (@eq_refl comparison Lt) HT) | | exact C2 |].
      * unfold tvz in *. apply Forall_forall. intros t Ht. apply (proj1 (Forall_forall _ _) HZ). apply in_or_app. left. exact Ht.
      * intros o a Ho Hx Hr. eapply txt_extra_ok; eauto.
    + cbn beta. eapply (P0_vr_of_tvz rho 309 311 4); [reflexivity | reflexivity | | | lia].
      * unfold tvz in *. constructor; [|constructor]. apply (proj1 (Forall_forall _ _) HZ). apply in_or_app. right. left. reflexivity.
      * eapply (proj1 (Forall_forall _ _) HF). vm_compute. tauto.
  -
    intros d rho' Hd Hag. destruct Hd as [<-|[<-|[<-|[]]]]; cbn [fst snd].
    + eapply (CONT _ _ _ _ _ _ _ _ tvH _ _ _ _ rho rho' _ C3); [apply Permutation_sym; apply (perm_move_last (tvH_l1 4) (tvH_l2 4) (tvH_x 4)) | exact Hag |].
      intros rho'' Hm. apply (REENTER (R4 h) tvH (73, z0) rho''); [apply (nth_error_in _ 14); reflexivity | exact Hm].
    + eapply (CONT _ _ _ _ _ _ _ _ tvH _ _ _ _ rho rho' _ C4); [apply Permutation_sym; apply (perm_move_last (tvH_l1 4) (tvH_l2 4) (tvH_x 4)) | exact Hag |].
      intros rho'' Hm. apply (REENTER (F4 h) tvH (73, z0) rho''); [apply (nth_error_in _ 15); reflexivity | exact Hm].
    + eapply (CONT _ _ _ _ _ _ _ _ tvH _ _ _ _ rho rho' _ C5); [apply Permutation_sym; apply (perm_move_last (tvH_l1 4) (tvH_l2 4) (tvH_x 4)) | exact Hag |].
      intros rho'' Hm. apply (REENTER (R4 h) tvH (73, z0) rho''); [apply (nth_error_in _ 14); reflexivity | exact Hm].
  }
  intros w Hw. apply (SPJ_norm_xu segs _ _ _ _ _ _ rho w view_sg).
  apply (SPJ_JG_move_last segs C_P NP Kc rho0 (P0_hf FB) FB (tvH_l1 4) (tvH_l2 4) (tvH_x 4)). exact Hw.
Qed.

Lemma X_E_tr_ok : ltac2:(tb__ "0|2|
S2VTR;S1dScVJGv;S22A1S39S24A1M0R1A4VFAM;S42SeSdS1SfSdS0S0A2A1M1A2SdS1bS0A2SeS1G1G0S22A4SeS1bS0Z44S63A4A4R1A2A1A2Frho;").
Proof using CLIENT CONT REENTER nI.
  intros rho.
  destruct (vr_site_checkEP _ _ _ _ _ _ _ _ _ _ _ chk_trok) as (R & HE & C1 & Cd & Cn & Cb & Cs & Cp & C2 & C3 & C4 & C5).
  eapply TR_pre.
  2: { apply (CLIENT E2_trok s_trok R rho (keptH 7) [tvH_x 7] _ HE C1 Cd Cn Cb Cs Cp).
  -
    intros Ai ms HF HP0 Hav _ _ _ HZ _ HT. split.
    + eapply robjs_checkF_sound; [exact HF | exact (TobjJVx.T_ok_T0_agree _ _ _ _ Hav (@eq_refl comparison Lt) HT) | | exact C2 |].
      * unfold tvz in *. apply Forall_forall. intros t Ht. apply (proj1 (Forall_forall _ _) HZ). apply in_or_app. left. exact Ht.
      * intros o a Ho Hx Hr. eapply txt_extra_ok; eauto.
    + cbn beta. eapply (P0_vr_of_tvz rho 318 320 4); [reflexivity | reflexivity | | | lia].
      * unfold tvz in *. constructor; [|constructor]. apply (proj1 (Forall_forall _ _) HZ). apply in_or_app. right. left. reflexivity.
      * eapply (proj1 (Forall_forall _ _) HF). vm_compute. tauto.
  -
    intros d rho' Hd Hag. destruct Hd as [<-|[<-|[<-|[]]]]; cbn [fst snd].
    + eapply (CONT _ _ _ _ _ _ _ _ tvH _ _ _ _ rho rho' _ C3); [apply Permutation_sym; apply (perm_move_last (tvH_l1 7) (tvH_l2 7) (tvH_x 7)) | exact Hag |].
      intros rho'' Hm. apply (REENTER (KT_ok h) tvH (66, z0) rho''); [apply (nth_error_in _ 17); reflexivity | exact Hm].
    + eapply (CONT _ _ _ _ _ _ _ _ tvH _ _ _ _ rho rho' _ C4); [apply Permutation_sym; apply (perm_move_last (tvH_l1 7) (tvH_l2 7) (tvH_x 7)) | exact Hag |].
      intros rho'' Hm. apply (REENTER (FT h) tvH (66, z0) rho''); [apply (nth_error_in _ 19); reflexivity | exact Hm].
    + eapply (CONT _ _ _ _ _ _ _ _ tvH _ _ _ _ rho rho' _ C5); [apply Permutation_sym; apply (perm_move_last (tvH_l1 7) (tvH_l2 7) (tvH_x 7)) | exact Hag |].
      intros rho'' Hm. apply (REENTER (KT_ok h) tvH (66, z0) rho''); [apply (nth_error_in _ 17); reflexivity | exact Hm].
  }
  intros w Hw. apply (SPJ_norm_xu segs _ _ _ _ _ _ rho w view_trok).
  apply (SPJ_JG_move_last segs C_P NP Kc rho0 (P0_hf FB) FB (tvH_l1 7) (tvH_l2 7) (tvH_x 7)). exact Hw.
Qed.

Lemma X_E_tr_bad : ltac2:(tb__ "0|2|
S2VTR;S1dScVJGv;S22A1S38S24A1M0R1A4VFAM;S42SeSdS1SfSdS0S0A2A1M1A2SdS1bS0A2SeS1G1G0S22A4SeS1bS0Z44S63A4A4R1A2A1A2Frho;").
Proof using CLIENT CONT REENTER nI.
  intros rho.
  destruct (vr_site_checkEP _ _ _ _ _ _ _ _ _ _ _ chk_trbad) as (R & HE & C1 & Cd & Cn & Cb & Cs & Cp & C2 & C3 & C4 & C5).
  eapply TR_pre.
  2: { apply (CLIENT E2_trbad s_trbad R rho (keptH 7) [tvH_x 7] _ HE C1 Cd Cn Cb Cs Cp).
  -
    intros Ai ms HF HP0 Hav _ _ _ HZ _ HT. split.
    + eapply robjs_checkF_sound; [exact HF | exact (TobjJVx.T_ok_T0_agree _ _ _ _ Hav (@eq_refl comparison Lt) HT) | | exact C2 |].
      * unfold tvz in *. apply Forall_forall. intros t Ht. apply (proj1 (Forall_forall _ _) HZ). apply in_or_app. left. exact Ht.
      * intros o a Ho Hx Hr. eapply txt_extra_ok; eauto.
    + cbn beta. eapply (P0_vr_of_tvz rho 318 320 4); [reflexivity | reflexivity | | | lia].
      * unfold tvz in *. constructor; [|constructor]. apply (proj1 (Forall_forall _ _) HZ). apply in_or_app. right. left. reflexivity.
      * eapply (proj1 (Forall_forall _ _) HF). vm_compute. tauto.
  -
    intros d rho' Hd Hag. destruct Hd as [<-|[<-|[<-|[]]]]; cbn [fst snd].
    + eapply (CONT _ _ _ _ _ _ _ _ tvH _ _ _ _ rho rho' _ C3); [apply Permutation_sym; apply (perm_move_last (tvH_l1 7) (tvH_l2 7) (tvH_x 7)) | exact Hag |].
      intros rho'' Hm. apply (REENTER (KT_bad h) tvH (66, z0) rho''); [apply (nth_error_in _ 18); reflexivity | exact Hm].
    + eapply (CONT _ _ _ _ _ _ _ _ tvH _ _ _ _ rho rho' _ C4); [apply Permutation_sym; apply (perm_move_last (tvH_l1 7) (tvH_l2 7) (tvH_x 7)) | exact Hag |].
      intros rho'' Hm. apply (REENTER (FT h) tvH (66, z0) rho''); [apply (nth_error_in _ 19); reflexivity | exact Hm].
    + eapply (CONT _ _ _ _ _ _ _ _ tvH _ _ _ _ rho rho' _ C5); [apply Permutation_sym; apply (perm_move_last (tvH_l1 7) (tvH_l2 7) (tvH_x 7)) | exact Hag |].
      intros rho'' Hm. apply (REENTER (KT_bad h) tvH (66, z0) rho''); [apply (nth_error_in _ 18); reflexivity | exact Hm].
  }
  intros w Hw. apply (SPJ_norm_xu segs _ _ _ _ _ _ rho w view_trbad).
  apply (SPJ_JG_move_last segs C_P NP Kc rho0 (P0_hf FB) FB (tvH_l1 7) (tvH_l2 7) (tvH_x 7)). exact Hw.
Qed.

Lemma X_E_rp : ltac2:(tb__ "0|2|
S2VTR;S1dScVJGv;S22A1S34S24A1M0R1A4VFAM;S42SeSdS1SfSdS0S0A2A1M1A2SdS1bS0A2SeS1G1G0S22A4SeS1bS0Z3eS63A4A4R1A2A1A2Frho;").
Proof using CLIENT CONT REENTER nI.
  intros rho.
  destruct (vr_site_checkEP _ _ _ _ _ _ _ _ _ _ _ chk_rp) as (R & HE & C1 & Cd & Cn & Cb & Cs & Cp & C2 & C3 & C4 & C5).
  eapply TR_pre.
  2: { apply (CLIENT E2_rp s_rp R rho (keptH 6) [tvH_x 6] _ HE C1 Cd Cn Cb Cs Cp).
  -
    intros Ai ms HF HP0 Hav _ _ _ HZ _ HT. split.
    + eapply robjs_checkF_sound; [exact HF | exact (TobjJVx.T_ok_T0_agree _ _ _ _ Hav (@eq_refl comparison Lt) HT) | | exact C2 |].
      * unfold tvz in *. apply Forall_forall. intros t Ht. apply (proj1 (Forall_forall _ _) HZ). apply in_or_app. left. exact Ht.
      * intros o a Ho Hx Hr. eapply txt_extra_ok; eauto.
    + cbn beta. eapply (P0_vr_of_tvz rho 315 317 4); [reflexivity | reflexivity | | | lia].
      * unfold tvz in *. constructor; [|constructor]. apply (proj1 (Forall_forall _ _) HZ). apply in_or_app. right. left. reflexivity.
      * eapply (proj1 (Forall_forall _ _) HF). vm_compute. tauto.
  -
    intros d rho' Hd Hag. destruct Hd as [<-|[<-|[<-|[]]]]; cbn [fst snd].
    + eapply (CONT _ _ _ _ _ _ _ _ tvH _ _ _ _ rho rho' _ C3); [apply Permutation_sym; apply (perm_move_last (tvH_l1 6) (tvH_l2 6) (tvH_x 6)) | exact Hag |].
      intros rho'' Hm. apply (REENTER (KR h) tvH (60, z0) rho''); [apply (nth_error_in _ 22); reflexivity | exact Hm].
    + eapply (CONT _ _ _ _ _ _ _ _ tvH _ _ _ _ rho rho' _ C4); [apply Permutation_sym; apply (perm_move_last (tvH_l1 6) (tvH_l2 6) (tvH_x 6)) | exact Hag |].
      intros rho'' Hm. apply (REENTER (FR h) tvH (60, z0) rho''); [apply (nth_error_in _ 23); reflexivity | exact Hm].
    + eapply (CONT _ _ _ _ _ _ _ _ tvH _ _ _ _ rho rho' _ C5); [apply Permutation_sym; apply (perm_move_last (tvH_l1 6) (tvH_l2 6) (tvH_x 6)) | exact Hag |].
      intros rho'' Hm. apply (REENTER (KR h) tvH (60, z0) rho''); [apply (nth_error_in _ 22); reflexivity | exact Hm].
  }
  intros w Hw. apply (SPJ_norm_xu segs _ _ _ _ _ _ rho w view_rp).
  apply (SPJ_JG_move_last segs C_P NP Kc rho0 (P0_hf FB) FB (tvH_l1 6) (tvH_l2 6) (tvH_x 6)). exact Hw.
Qed.

Lemma X_E_ts : ltac2:(tb__ "0|2|
S2VTR;S1dScVJGv;S22A1S3aS24A1M0R1A4VFAM;S42SeSdS1SfSdS0S0A2A1M1A2SdS1bS0A2SeS1G1G0S22A4SeS1bS0Z38S63A4A4R1A2A1A2Frho;").
Proof using CLIENT CONT REENTER nI.
  intros rho.
  destruct (vr_site_checkEP _ _ _ _ _ _ _ _ _ _ _ chk_ts) as (R & HE & C1 & Cd & Cn & Cb & Cs & Cp & C2 & C3 & C4 & C5).
  eapply TR_pre.
  2: { apply (CLIENT E2_ts s_ts R rho (keptH 8) [tvH_x 8] _ HE C1 Cd Cn Cb Cs Cp).
  -
    intros Ai ms HF HP0 Hav _ _ _ HZ _ HT. split.
    + eapply robjs_checkF_sound; [exact HF | exact (TobjJVx.T_ok_T0_agree _ _ _ _ Hav (@eq_refl comparison Lt) HT) | | exact C2 |].
      * unfold tvz in *. apply Forall_forall. intros t Ht. apply (proj1 (Forall_forall _ _) HZ). apply in_or_app. left. exact Ht.
      * intros o a Ho Hx Hr. eapply txt_extra_ok; eauto.
    + cbn beta. eapply (P0_vr_of_tvz rho 321 323 1); [reflexivity | reflexivity | | | lia].
      * unfold tvz in *. constructor; [|constructor]. apply (proj1 (Forall_forall _ _) HZ). apply in_or_app. right. left. reflexivity.
      * eapply (proj1 (Forall_forall _ _) HF). vm_compute. tauto.
  -
    intros d rho' Hd Hag. destruct Hd as [<-|[<-|[<-|[]]]]; cbn [fst snd].
    + eapply (CONT _ _ _ _ _ _ _ _ tvH _ _ _ _ rho rho' _ C3); [apply Permutation_sym; apply (perm_move_last (tvH_l1 8) (tvH_l2 8) (tvH_x 8)) | exact Hag |].
      intros rho'' Hm. apply (REENTER (KQ h) tvH (54, z0) rho''); [apply (nth_error_in _ 25); reflexivity | exact Hm].
    + eapply (CONT _ _ _ _ _ _ _ _ tvH _ _ _ _ rho rho' _ C4); [apply Permutation_sym; apply (perm_move_last (tvH_l1 8) (tvH_l2 8) (tvH_x 8)) | exact Hag |].
      intros rho'' Hm. apply (REENTER (FQ h) tvH (54, z0) rho''); [apply (nth_error_in _ 26); reflexivity | exact Hm].
    + eapply (CONT _ _ _ _ _ _ _ _ tvH _ _ _ _ rho rho' _ C5); [apply Permutation_sym; apply (perm_move_last (tvH_l1 8) (tvH_l2 8) (tvH_x 8)) | exact Hag |].
      intros rho'' Hm. apply (REENTER (KQ h) tvH (54, z0) rho''); [apply (nth_error_in _ 25); reflexivity | exact Hm].
  }
  intros w Hw. apply (SPJ_norm_xu segs _ _ _ _ _ _ rho w view_ts).
  apply (SPJ_JG_move_last segs C_P NP Kc rho0 (P0_hf FB) FB (tvH_l1 8) (tvH_l2 8) (tvH_x 8)). exact Hw.
Qed.

Lemma X_E_mi2 : ltac2:(tb__ "0|2|
S2VTR;S1dScVJGv;S22A1S30S24A1M0R1A4VFAM;S42SeSdS1SfSdS0S0A2A1M1A2SdS1bS0A2SeS1G1G0S22A4SeS1bS0Z28S64Z8A1A4A4R1A2A1A2Frho;").
Proof using CLIENT CONT REENTER nI.
  intros rho.
  destruct (vr_site_checkEP _ _ _ _ _ _ _ _ _ _ _ chk_mi2) as (R & HE & C1 & Cd & Cn & Cb & Cs & Cp & C2 & C3 & C4 & C5).
  eapply TR_pre.
  2: { apply (CLIENT E2_mi2 s_mi2 R rho (keptH 1) [tvH_x 1] _ HE C1 Cd Cn Cb Cs Cp).
  -
    intros Ai ms HF HP0 Hav _ _ _ HZ _ HT. split.
    + eapply robjs_checkF_sound; [exact HF | exact (TobjJVx.T_ok_T0_agree _ _ _ _ Hav (@eq_refl comparison Lt) HT) | | exact C2 |].
      * unfold tvz in *. apply Forall_forall. intros t Ht. apply (proj1 (Forall_forall _ _) HZ). apply in_or_app. left. exact Ht.
      * intros o a Ho Hx Hr. eapply txt_extra_ok; eauto.
    + cbn beta. eapply (P0_vr_of_tvz rho 300 302 12); [reflexivity | reflexivity | | | lia].
      * unfold tvz in *. constructor; [|constructor]. apply (proj1 (Forall_forall _ _) HZ). apply in_or_app. right. left. reflexivity.
      * eapply (proj1 (Forall_forall _ _) HF). vm_compute. tauto.
  -
    intros d rho' Hd Hag. destruct Hd as [<-|[<-|[<-|[]]]]; cbn [fst snd].
    + eapply (CONT _ _ _ _ _ _ _ _ tvH _ _ _ _ rho rho' _ C3); [apply Permutation_sym; apply (perm_move_last (tvH_l1 1) (tvH_l2 1) (tvH_x 1)) | exact Hag |].
      intros rho'' Hm. apply (REENTER (A_mi2 h) tvH (40, VL 7) rho''); [apply (nth_error_in _ 30); reflexivity | exact Hm].
    + eapply (CONT _ _ _ _ _ _ _ _ tvH _ _ _ _ rho rho' _ C4); [apply Permutation_sym; apply (perm_move_last (tvH_l1 1) (tvH_l2 1) (tvH_x 1)) | exact Hag |].
      intros rho'' Hm. apply (REENTER (F_mi2 h) tvH (38, z0) rho''); [apply (nth_error_in _ 31); reflexivity | exact Hm].
    + eapply (CONT _ _ _ _ _ _ _ _ tvH _ _ _ _ rho rho' _ C5); [apply Permutation_sym; apply (perm_move_last (tvH_l1 1) (tvH_l2 1) (tvH_x 1)) | exact Hag |].
      intros rho'' Hm. apply (REENTER (A_mi2 h) tvH (40, VL 7) rho''); [apply (nth_error_in _ 30); reflexivity | exact Hm].
  }
  intros w Hw. apply (SPJ_norm_xu segs _ _ _ _ _ _ rho w view_mi2).
  apply (SPJ_JG_move_last segs C_P NP Kc rho0 (P0_hf FB) FB (tvH_l1 1) (tvH_l2 1) (tvH_x 1)). exact Hw.
Qed.

Lemma X_E_fv2 : ltac2:(tb__ "0|2|
S2VTR;S1dScVJGv;S22A1S2eS24A1M0R1A4VFAM;S42SeSdS1SfSdS0S0A2A1M1A2SdS1bS0A2SeS1G1G0S22A4SeS1bS0Z28S64Z6A1A4A4R1A2A1A2Frho;").
Proof using CLIENT CONT REENTER nI.
  intros rho.
  destruct (vr_site_checkEP _ _ _ _ _ _ _ _ _ _ _ chk_fv2) as (R & HE & C1 & Cd & Cn & Cb & Cs & Cp & C2 & C3 & C4 & C5).
  eapply TR_pre.
  2: { apply (CLIENT E2_fv2 s_fv2 R rho (keptH 2) [tvH_x 2] _ HE C1 Cd Cn Cb Cs Cp).
  -
    intros Ai ms HF HP0 Hav _ _ _ HZ _ HT. split.
    + eapply robjs_checkF_sound; [exact HF | exact (TobjJVx.T_ok_T0_agree _ _ _ _ Hav (@eq_refl comparison Lt) HT) | | exact C2 |].
      * unfold tvz in *. apply Forall_forall. intros t Ht. apply (proj1 (Forall_forall _ _) HZ). apply in_or_app. left. exact Ht.
      * intros o a Ho Hx Hr. eapply txt_extra_ok; eauto.
    + cbn beta. eapply (P0_vr_of_tvz rho 303 305 4); [reflexivity | reflexivity | | | lia].
      * unfold tvz in *. constructor; [|constructor]. apply (proj1 (Forall_forall _ _) HZ). apply in_or_app. right. left. reflexivity.
      * eapply (proj1 (Forall_forall _ _) HF). vm_compute. tauto.
  -
    intros d rho' Hd Hag. destruct Hd as [<-|[<-|[<-|[]]]]; cbn [fst snd].
    + eapply (CONT _ _ _ _ _ _ _ _ tvH _ _ _ _ rho rho' _ C3); [apply Permutation_sym; apply (perm_move_last (tvH_l1 2) (tvH_l2 2) (tvH_x 2)) | exact Hag |].
      intros rho'' Hm. apply (REENTER (A_fv2 h) tvH (40, VL 5) rho''); [apply (nth_error_in _ 32); reflexivity | exact Hm].
    + eapply (CONT _ _ _ _ _ _ _ _ tvH _ _ _ _ rho rho' _ C4); [apply Permutation_sym; apply (perm_move_last (tvH_l1 2) (tvH_l2 2) (tvH_x 2)) | exact Hag |].
      intros rho'' Hm. apply (REENTER (F_fv2 h) tvH (38, z0) rho''); [apply (nth_error_in _ 33); reflexivity | exact Hm].
    + eapply (CONT _ _ _ _ _ _ _ _ tvH _ _ _ _ rho rho' _ C5); [apply Permutation_sym; apply (perm_move_last (tvH_l1 2) (tvH_l2 2) (tvH_x 2)) | exact Hag |].
      intros rho'' Hm. apply (REENTER (A_fv2 h) tvH (40, VL 5) rho''); [apply (nth_error_in _ 32); reflexivity | exact Hm].
  }
  intros w Hw. apply (SPJ_norm_xu segs _ _ _ _ _ _ rho w view_fv2).
  apply (SPJ_JG_move_last segs C_P NP Kc rho0 (P0_hf FB) FB (tvH_l1 2) (tvH_l2 2) (tvH_x 2)). exact Hw.
Qed.

Lemma X_E_mm2 : ltac2:(tb__ "0|2|
S2VTR;S1dScVJGv;S22A1S32S24A1M0R1A4VFAM;S42SeSdS1SfSdS0S0A2A1M1A2SdS1bS0A2SeS1G1G0S22A4SeS1bS0Z28S64Z4A1A4A4R1A2A1A2Frho;").
Proof using CLIENT CONT REENTER nI.
  intros rho.
  destruct (vr_site_checkEP _ _ _ _ _ _ _ _ _ _ _ chk_mm2) as (R & HE & C1 & Cd & Cn & Cb & Cs & Cp & C2 & C3 & C4 & C5).
  eapply TR_pre.
  2: { apply (CLIENT E2_mm2 s_mm2 R rho (keptH 3) [tvH_x 3] _ HE C1 Cd Cn Cb Cs Cp).
  -
    intros Ai ms HF HP0 Hav _ _ _ HZ _ HT. split.
    + eapply robjs_checkF_sound; [exact HF | exact (TobjJVx.T_ok_T0_agree _ _ _ _ Hav (@eq_refl comparison Lt) HT) | | exact C2 |].
      * unfold tvz in *. apply Forall_forall. intros t Ht. apply (proj1 (Forall_forall _ _) HZ). apply in_or_app. left. exact Ht.
      * intros o a Ho Hx Hr. eapply txt_extra_ok; eauto.
    + cbn beta. eapply (P0_vr_of_tvz rho 306 308 4); [reflexivity | reflexivity | | | lia].
      * unfold tvz in *. constructor; [|constructor]. apply (proj1 (Forall_forall _ _) HZ). apply in_or_app. right. left. reflexivity.
      * eapply (proj1 (Forall_forall _ _) HF). vm_compute. tauto.
  -
    intros d rho' Hd Hag. destruct Hd as [<-|[<-|[<-|[]]]]; cbn [fst snd].
    + eapply (CONT _ _ _ _ _ _ _ _ tvH _ _ _ _ rho rho' _ C3); [apply Permutation_sym; apply (perm_move_last (tvH_l1 3) (tvH_l2 3) (tvH_x 3)) | exact Hag |].
      intros rho'' Hm. apply (REENTER (A_mm2 h) tvH (40, VL 3) rho''); [apply (nth_error_in _ 34); reflexivity | exact Hm].
    + eapply (CONT _ _ _ _ _ _ _ _ tvH _ _ _ _ rho rho' _ C4); [apply Permutation_sym; apply (perm_move_last (tvH_l1 3) (tvH_l2 3) (tvH_x 3)) | exact Hag |].
      intros rho'' Hm. apply (REENTER (F_mm2 h) tvH (38, z0) rho''); [apply (nth_error_in _ 35); reflexivity | exact Hm].
    + eapply (CONT _ _ _ _ _ _ _ _ tvH _ _ _ _ rho rho' _ C5); [apply Permutation_sym; apply (perm_move_last (tvH_l1 3) (tvH_l2 3) (tvH_x 3)) | exact Hag |].
      intros rho'' Hm. apply (REENTER (A_mm2 h) tvH (40, VL 3) rho''); [apply (nth_error_in _ 34); reflexivity | exact Hm].
  }
  intros w Hw. apply (SPJ_norm_xu segs _ _ _ _ _ _ rho w view_mm2).
  apply (SPJ_JG_move_last segs C_P NP Kc rho0 (P0_hf FB) FB (tvH_l1 3) (tvH_l2 3) (tvH_x 3)). exact Hw.
Qed.

Lemma X_E_sg2 : ltac2:(tb__ "0|2|
S2VTR;S1dScVJGv;S22A1S36S24A1M0R1A4VFAM;S42SeSdS1SfSdS0S0A2A1M1A2SdS1bS0A2SeS1G1G0S22A4SeS1bS0Z28S64Z2A1A4A4R1A2A1A2Frho;").
Proof using CLIENT CONT REENTER nI.
  intros rho.
  destruct (vr_site_checkEP _ _ _ _ _ _ _ _ _ _ _ chk_sg2) as (R & HE & C1 & Cd & Cn & Cb & Cs & Cp & C2 & C3 & C4 & C5).
  eapply TR_pre.
  2: { apply (CLIENT E2_sg2 s_sg2 R rho (keptH 4) [tvH_x 4] _ HE C1 Cd Cn Cb Cs Cp).
  -
    intros Ai ms HF HP0 Hav _ _ _ HZ _ HT. split.
    + eapply robjs_checkF_sound; [exact HF | exact (TobjJVx.T_ok_T0_agree _ _ _ _ Hav (@eq_refl comparison Lt) HT) | | exact C2 |].
      * unfold tvz in *. apply Forall_forall. intros t Ht. apply (proj1 (Forall_forall _ _) HZ). apply in_or_app. left. exact Ht.
      * intros o a Ho Hx Hr. eapply txt_extra_ok; eauto.
    + cbn beta. eapply (P0_vr_of_tvz rho 309 311 4); [reflexivity | reflexivity | | | lia].
      * unfold tvz in *. constructor; [|constructor]. apply (proj1 (Forall_forall _ _) HZ). apply in_or_app. right. left. reflexivity.
      * eapply (proj1 (Forall_forall _ _) HF). vm_compute. tauto.
  -
    intros d rho' Hd Hag. destruct Hd as [<-|[<-|[<-|[]]]]; cbn [fst snd].
    + eapply (CONT _ _ _ _ _ _ _ _ tvH _ _ _ _ rho rho' _ C3); [apply Permutation_sym; apply (perm_move_last (tvH_l1 4) (tvH_l2 4) (tvH_x 4)) | exact Hag |].
      intros rho'' Hm. apply (REENTER (A_sg2 h) tvH (40, VL 1) rho''); [apply (nth_error_in _ 36); reflexivity | exact Hm].
    + eapply (CONT _ _ _ _ _ _ _ _ tvH _ _ _ _ rho rho' _ C4); [apply Permutation_sym; apply (perm_move_last (tvH_l1 4) (tvH_l2 4) (tvH_x 4)) | exact Hag |].
      intros rho'' Hm. apply (REENTER (F_sg2 h) tvH (38, z0) rho''); [apply (nth_error_in _ 37); reflexivity | exact Hm].
    + eapply (CONT _ _ _ _ _ _ _ _ tvH _ _ _ _ rho rho' _ C5); [apply Permutation_sym; apply (perm_move_last (tvH_l1 4) (tvH_l2 4) (tvH_x 4)) | exact Hag |].
      intros rho'' Hm. apply (REENTER (A_sg2 h) tvH (40, VL 1) rho''); [apply (nth_error_in _ 36); reflexivity | exact Hm].
  }
  intros w Hw. apply (SPJ_norm_xu segs _ _ _ _ _ _ rho w view_sg2).
  apply (SPJ_JG_move_last segs C_P NP Kc rho0 (P0_hf FB) FB (tvH_l1 4) (tvH_l2 4) (tvH_x 4)). exact Hw.
Qed.

Lemma X_E_pc : ltac2:(tb__ "0|2|
S2VTR;S1dScVJGv;S22A1S33S24A1M0R1A4VFAM;S42SeSdS1SfSdS0S0A2A1M1A2SdS1bS0A2SeS1G1G0S22A4SeS1bS0Z5aS65S2aZ5A2A4A4R1A2A1A2Frho;").
Proof using CPC ENT PURE REENTER.
  intros rho. destruct (pc_site_checkP _ _ _ _ _ _ _ chk_pc) as (Hpre & R & HE & C1 & C2 & C3 & C4 & C5 & C6).
  eapply TR_pre.
  2: { apply (PURE (Epc2 (E_pc h)) Pre_pc (s_pc (E_pc h)) R Posts_pc rho tvH _ (CPC tvH rho) HE C1 C2 C3 C4).
  intros L rho' HinL Hag. destruct HinL as [<-|[<-|[]]]; cbn [lf_state].
  - destruct (pccont_soundP (JGv tvH) _ _ _ _ _ _ _ C5) as (X & HN & HC & HS).
    eapply TR_pre.
    2: { eapply (ENT _ X (TP0 h) tvH tvH tvH _ _ _ _ rho rho' _ HC (Permutation_refl _) (agree_below_vals _ _ _ Hag)).
         intros rho'' Hm. apply (REENTER (TP0 h) tvH (90, VT pC 4) rho''); [apply (nth_error_in _ 6); reflexivity | exact Hm]. }
    intros w Hw. exact (HS rho' w Hw).
  - destruct (pccont_soundP (JGv tvH) _ _ _ _ _ _ _ C6) as (X & HN & HC & HS).
    eapply TR_pre.
    2: { eapply (ENT _ X (TP h) tvH tvH tvH _ _ _ _ rho rho' _ HC (Permutation_refl _) (agree_below_vals _ _ _ Hag)).
         intros rho'' Hm. apply (REENTER (TP h) tvH (90, VT pC 4) rho''); [apply (nth_error_in _ 7); reflexivity | exact Hm]. }
    intros w Hw. exact (HS rho' w Hw).
  }
  intros w Hw. exact (pc_pre_sound (JGv tvH) (E_pc h) rho w Hpre Hw).
Qed.

Lemma X_E_tp : ltac2:(tb__ "0|2|
S2VTR;S1dScVJGv;S22A1S37S24A1M0R1A4VFAM;S42SeSdS1SfSdS0S0A2A1M1A2SdS1bS0A2SeS1G1G0S22A4SeS1bS0Z34S63A4A4R1A2A1A2Frho;").
Proof using CTP ENT PURE REENTER.
  intros rho. destruct (tp_site_checkP _ _ _ _ _ _ _ chk_tp) as (Hpre & R & HE & C1 & C2 & C3 & C4 & C5 & C6).
  eapply TR_pre.
  2: { apply (PURE (Etp6 (E_tp h)) (Pre_pg PG_P []) (s_tp (E_tp h)) R Posts_pg rho tvH _ (CTP tvH rho) HE C1 C2 C3 C4).
  intros L rho' HinL Hag. destruct HinL as [<-|[<-|[]]]; cbn [lf_state].
  - destruct (tpcont_soundP (JGv tvH) _ _ _ _ _ _ _ C5) as (X & HN & HC & HS).
    eapply TR_pre.
    2: { eapply (ENT _ X (KP_inv h) tvH tvH tvH _ _ _ _ rho rho' _ HC (Permutation_refl _) (agree_below_vals _ _ _ Hag)).
         intros rho'' Hm. apply (REENTER (KP_inv h) tvH (50, z0) rho''); [apply (nth_error_in _ 28); reflexivity | exact Hm]. }
    intros w Hw. exact (HS rho' w Hw).
  - destruct (tpcont_soundP (JGv tvH) _ _ _ _ _ _ _ C6) as (X & HN & HC & HS).
    eapply TR_pre.
    2: { eapply (ENT _ X (KP_ok h) tvH tvH tvH _ _ _ _ rho rho' _ HC (Permutation_refl _) (agree_below_vals _ _ _ Hag)).
         intros rho'' Hm. apply (REENTER (KP_ok h) tvH (50, z0) rho''); [apply (nth_error_in _ 27); reflexivity | exact Hm]. }
    intros w Hw. exact (HS rho' w Hw).
  }
  intros w Hw. exact (tp_pre_sound Kc rho0 FB (E_tp h) rho w Hpre Hw).
Qed.

Lemma exits_okT : ltac2:(tb__ "0|3|
S1SfSdS0S0A2A1M0SdS1bS0A2M1S2S77SdSdS1G0A2M2G1A2SeG2G1SeS1G0R4R3A4R2A4S67S24A1A3VTR;S1dScVJGv;R4A1R5R2A4VFAM;S42SeG2G1SeS1G0R5R4A4R3A4R2A2A1A2F_;Frho;FrvX;FtvX;FX;").
Proof using CLIENT CONT CPC CTP ENT POST PURE REENTER nI.
  intros X tvX rvX rho Hin. cbn [hf_exits In] in Hin.
  destruct Hin as [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[]]]]]]]]]]]]]]]]]]; injection H as <- <- <-.
  - apply X_E_co.
  - apply X_E_pc.
  - apply X_HP_ret.
  - apply X_HP_degen.
  - apply X_E_mi.
  - apply X_E_fv.
  - apply X_E_mm.
  - apply X_E_sg.
  - apply X_E_tr_ok.
  - apply X_E_tr_bad.
  - apply X_E_rp.
  - apply X_E_ts.
  - apply X_E_tp.
  - apply X_E_mi2.
  - apply X_E_fv2.
  - apply X_E_mm2.
  - apply X_E_sg2.
Qed.
End SumT.

Section Safety.
Variable ok : world -> Prop.
Hypothesis HS : ltac2:(tb__ "0|0|
S91ScVok;VKc;A3").
Hypothesis MC : ltac2:(tb__ "0|0|
S51ScS3cS8fA3").

Theorem handle_f_sum : ltac2:(tb__ "0|0|
S62ScVok;S1dScS44ScS3cVKc;S25VFB;A1VFB;S2bA6S29S24A1Vrho0;A4S6cScS23Vrho0;S8aA4A4").
Proof using HS MC ML.
  eapply triple_conseq; [ | intros w Hw; exact Hw | ].
  2: { apply (cfg_sound_JGE segs C_P NP Kc rho0 (P0_hf FB) FB ML FUEL (cps h) NP (hf_cuts h) (hf_exits h) ok Q (proj1 HS)
                (ejcert_jcert segs NP _ _ _ _ _ ejcert_ok)) with (rvT := (100, z0)); [|left; reflexivity].
       apply (exits_okT (triple segs ok) (fun _ w => SPfamGJ segs (map nI (map (@edrop) (hf_cuts h))) w \/ Q w)
                (triple_factsJ segs ok) (triple_SPJ_ex segs ok)
                (fun P P' Q' HP H => @triple_conseq segs ok P P' Q' Q' HP (fun w Hw => Hw) H)
                (fun A P Q' H => @triple_ex segs ok A P Q' H)
                (triple_pureh segs ok)
                (call_soundP segs ok) (call_soundJ segs ok)).
       - intros FBc rho1. apply (vec_reserve_sum ok Kc FBc rho1 HS ML MC).
       - intros tv rho rho1. apply parse_corner_sum.
         eapply ok_frame_imp; [|exact (proj1 HS)]. intros tr md (Ai & _ & HK & _). exact HK.
       - intros tv rho rho1. apply tess_polygon_sum.
         eapply ok_frame_imp; [|exact (proj1 HS)]. intros tr md (Ai & _ & HK & _). exact HK.
       - intros T tv rv rho b Hin _. exact (reenter_cutGE segs C_P NP Kc rho0 (P0_hf FB) FB ok (hf_cuts h) T tv rv Q rho Hin).
       - intros P tv rho b Hin. apply (exit_postG segs C_P NP Kc (P0_hf FB) FB ok rho0 tv Posts_hf P). exact Hin. }
  intros w Hw. apply JG_pre_intro. exact Hw.
Qed.
End Safety.

Section Existence.
Hypothesis Hvi : vm_insensitive Kc.
Hypothesis MCX : ltac2:(tb__ "0|0|
S52ScS3cS8fA3").

Theorem handle_f_sum_ex : ltac2:(tb__ "0|0|
S60ScS1dScS44ScS3cVKc;S25VFB;A1VFB;S2bA6S29S24A1Vrho0;A4S6cScS23Vrho0;S8aA4A3").
Proof using Hvi MCX ML.
  eapply etriple_conseq; [ | intros w Hw; exact Hw | ].
  2: { apply (cfg_complete_JG segs C_P NP Kc rho0 (P0_hf FB) FB ML FUEL (cps h) NP (hf_cuts h) (hf_exits h) Q ejcert_ok) with (rvT := (100, z0)); [|left; reflexivity].
       apply (exits_okT (etriple segs) (fun b w => SPfamEJ segs (map (enodeI segs C_P NP Kc rho0 (P0_hf FB) FB) (hf_cuts h)) b w \/ Q w)
                (etriple_factsJ segs) (etriple_SPJ_ex segs)
                (fun P P' Q' HP H => @etriple_conseq segs P P' Q' Q' HP (fun w Hw => Hw) H)
                (fun A P Q' H => @etriple_ex segs A P Q' H)
                (etriple_pureh segs)
                (call_completeP segs) (call_completeJ segs)).
       - intros FBc rho1. apply (vec_reserve_sum_ex Kc FBc rho1 ML Hvi MCX).
       - intros tv rho rho1. apply parse_corner_sum_ex.
       - intros tv rho rho1. apply tess_polygon_sum_ex.
       - intros T tv rv rho b Hin Hm. exact (ereenter_cutE segs C_P NP Kc rho0 (P0_hf FB) FB (hf_cuts h) T tv rv Q b rho Hin Hm).
       - intros P tv rho b Hin. apply (eexit_postG segs C_P NP Kc (P0_hf FB) FB rho0 tv Posts_hf P). exact Hin. }
  intros w Hw. apply JG_pre_intro. exact Hw.
Qed.
End Existence.
End Sum.
