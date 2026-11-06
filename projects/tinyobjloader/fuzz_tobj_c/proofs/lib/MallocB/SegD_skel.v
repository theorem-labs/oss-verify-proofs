(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "valuation"; "sv"; "rw"; "sprop"; "SLit"; "ss_objs"; "ss_facts"; "ss_next"; "SVar"; "ss_lenient"; "agree_below"; "ss_pc"; "rm"; "eval"; "ss_regs"; "sprop_below"; "obj_range"; "reg_sv"; "mkSS"; "obj_wf"; "ss_fcsr"; "ss_fregs"; "ss_resv"; "SAlu"; "ranges_disjoint"; "holds"; "rl"; "sv_eqb"; "sstate"; "obj_holds"; "smatch"; "swf"; "SPAlign"; "enc_bytes"; "ro_addr"; "sv_below"; "@Corelib.Init.Datatypes"; "cons"; "nil"; "list"; "bool"; "app"; "true"; "prod"; "pair"; "length"; "nat"; "option"; "false"; "Some"; "snd"; "fst"; "None"; "@Corelib.Init.Logic"; "eq"; "and"; "ex"; "not"; "or"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "lt"; "div"; "modulo"; "to_nat"; "mul"; "pow"; "sub"; "of_nat"; "land"; "shiftr"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "Z_to_bv"; "bv_signed"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "stableA"; "ok_frameA"; "jpredA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "leafA"; "mkLeafA"; "entailsA"; "axst"; "ax_base"; "ax_setS"; "la_state"; "ax_X"; "shadow_addr"; "sym_runA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "DG"; "dN"; "dFB"; "dF"; "dNB"; "dFP"; "list_upd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_skel.Skel"; "JJ"; "QD"; "gmid"; "HS"; "jK"; "winDFP"; "insK"; "JJ2"; "nbK"; "insK5"; "TOPr"; "W0ok"; "armsF"; "cK"; "earmsF"; "PDb"; "PDf"; "arm_e"; "pend"; "REL"; "VS_NZ"; "c3K"; "curOK"; "dK"; "fK"; "VS_F"; "VS_T"; "VS_Z"; "pend_stable"; "VS_C1"; "VS_D"; "VS_E2"; "VS_F2"; "VS_N"; "VS_NB"; "ids_ok"; "pend_view"; "E7"; "InvF"; "InvFe"; "O_mtM2"; "O_mu2"; "PD0"; "R8"; "ids3"; "ids4"; "ids5"; "ids6f"; "ids7"; "ids_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states"; "NXD"; "vW"; "O_tw"; "NPRE"; "O_slotN"; "runA"; "vNB"; "vF"; "O_nid"; "F_D"; "vN"; "vSt"; "O_tf"; "O_nn"; "O_trD"; "RT_D"; "F_tw"; "mkFindB"; "F_N"; "O_bd"; "O_stc"; "add"; "F_nb"; "O_alloc"; "O_nh"; "O_nl"; "O_slot"; "vAL"; "PreD"; "RETPC"; "vD"; "F_n"; "mkT1"; "O_bdM"; "O_stcM"; "vM"; "O_mtM"; "O_mu"; "XE"; "fr_addr"; "mkFindZ"; "O_stb"; "O_stb1"; "PCE2"; "bd_addr"; "mkC1R"; "mkFindNZ"; "F_f"; "O_fr"; "PCJ"; "PostD"; "PreD1"; "bd1_addr"; "d1_tail_ok"; "idN"; "mkC1"; "mkI3b"; "mkI4"; "mkI5d"; "mkI5e2"; "mkI5f"; "mkIn"; "stc_addr"; "vS"; "F_NZ"; "F_S"; "F_a"; "F_af"; "F_d"; "F_dj"; "F_e2"; "F_f2"; "NXP"; "O_frN"; "O_nnE"; "SZMAX"; "carved4b"; "dropo"; "mkC3j"; "mkCONT"; "mkDj"; "mkE2h"; "mkFAIL"; "mkFAILf"; "mkJh"; "mkNBh"; "mkNBj"; "mkOK"; "mkOKf"; "nn_addr"; "node_addr"; "single_at"; "slotN_addr"; "slot_addr"; "vHS"; "vP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf"; "dep_cost"; "droom"; "NBSZ"; "FBSZ"; "STORE"; "depot_vm"; "DNMAX"; "G_fblk"; "G_nblk"; "DFPw"; "DFP"; "G_page"; "JD"; "NODESMU"; "sumZ"; "DEPOT"; "MAP1"; "NFBLK"; "cellZ"; "dblocks"; "ranges_disjointZ"; "JLD"; "KD_laws"; "NIDS"; "TABSZ"; "depot_inv";
"depot_mem"; "fblk"; "fpage"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "nth"; "firstn"; "@Stdlib.Lists.List"; "forallb"; "In"; "existsb"; "@Corelib.Init.Peano"; "lt"; "le"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "etriple"; "triple"; "triple1"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "PG"; "IMG_HI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegD_glue"; "skel"; "ro_win"; "notin_vars"; "inclb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsCut"; "RsEcall"; "instr_at"; "set_objs"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "m_vmmaps"; "event"; "alloc_top"; "vm_maps"; "vm_noaccess"; "ENOMEM"; "errno_ret"; "with_vmmaps"; "VmMaps"; "vm_add_lazy"; "m_vm_lazy"; "vm_backing_used"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "A_globals"; "stack_win"; "V_DEPTH"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "wsub_get"; "wsub"; "rho_sub"; "rho_absorb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "sv_vars_all"; "state_vars_all"; "obj_vars_all"; "agree_vals"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "cfg_ms"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "ms_gpr"; "machine_state"; "find_segment"; "@Stdlib.PArith.BinPos.Pos"; "succ"; "le"; "eqb"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "rho_set_rw"; "S_after"; "mmap_obj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "view"; "bview"; "present"; "@Corelib.Init.Nat"; "sub"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_SRL"; "ALU_SLL"; "instr"; "ALU_AND"; "Ecall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "set_rm"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue"; "carved"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "A_after"; "ok_pframeA"; "smatch_pendingA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysStep"; "unmap_range"; "@LinuxProcessSemantics.LinuxProcessSem.MemImageType"; "Segment"; "@LinuxProcessSemantics.Riscv.Sem"; "low32"; "alu32"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec"; "mmap_n"; "mmap_nZ"; "mmap_place_ok"; "mmap_rw_vm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap"; "mmap_modeled_b"; "@LinuxProcessSemantics.Riscv.Prelude"; "sext"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.BackingAlgebra"; "covered"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "withGA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.LedgerA"; "tp_clear_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "mat_equiv"; "paid"; "vms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget"; "KMAX"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymSoundI SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt StepA SoundA EntailA CompleteA CFGA GlueA GlueA2 SummaryA LedgerA SysCallA MmapA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import StartLib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_ins.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegD_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_ins.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import SegD_mmap.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Lemma runA_some : ltac2:(tb__ "0|1|
S2eS27S3aA1S55S27S52A1M0S35G0S9aR4R3R2A3R1A3S38S35G0R2S26S52A1A3A1S35S2fG0A1S5bS3cR6R5R4S2aA5S31G0R3A2A3F_;F_;Fl;FA;Fcuts;Ffuel;").
Proof.
  intros fuel cuts A l H Hne. unfold runA in H. destruct (sym_runA segsA fuel cuts A true) as [l'|]; [congruence|]. subst. exfalso. apply Hne. reflexivity.
Qed.

Lemma single_at_inv : ltac2:(tb__ "0|1|
S27S52A1M0S3aS35S28Sf0R2R1A2S2aA3S37S52S52S36S35G0R4S25S52R1S26S52A1A3A3S35S3aScS51S58R1A1A1A1R3A3A2LL;A2F_;Fpc;Fl;").
Proof.
  intros l pc H. unfold single_at in H. destruct l as [|L [|]]; try discriminate. exists L. split; [reflexivity|]. apply Z.eqb_eq. exact H.
Qed.

Lemma shl44_shr42 : ltac2:(tb__ "0|2|
S3aS36S3eZ0R1A2S3fR1S44Z2M0Z40A2M1A2A2S35S3aS40S41S43R2S44G0Z2cA2A2G1A2S44G0Z2aA2A2S43Z4S41R2S44G0Z14A2A2A2A3F_;Fx;").
Proof.
  intros x Hx.
  pose proof (Z.div_mod x (2^20) ltac:(lia)) as E.
  pose proof (Z.mod_pos_bound x (2^20) ltac:(lia)) as B.
  set (q := x / 2^20) in E. set (r := x mod 2^20) in *.
  rewrite E. replace ((2 ^ 20 * q + r) * 2 ^ 44) with (r * 2^44 + q * 2^64) by lia.
  rewrite Z.mod_add by lia. rewrite Z.mod_small by lia.
  replace (r * 2^44) with ((4*r) * 2^42) by lia. rewrite Z.div_mul by lia. lia.
Qed.

Lemma ax_setS_setS : ltac2:(tb__ "0|0|
S55S1dS1dS35S55S57S57R3R2A2R1A2S57R3R1A2A3FS2;FS1;FA;").
Proof. reflexivity. Qed.

Lemma stableA_le : ltac2:(tb__ "0|0|
S50S3bS3bS14aR2R1A2S4eS3cR3R4A3S4eS3cR3R5A3F_;F_;Fm;Fn;FJ;").
Proof.
  intros J n m Hnm HJ rho rho' tp tr md md' Hag Hme Hk. eapply HJ; [|exact Hme|exact Hk].
  destruct Hag as (A & B & C). split; [|split; assumption]. intros i Hi. apply A. lia.
Qed.

Lemma srlw16_small : ltac2:(tb__ "0|1|
S4aQ40M0A1S3fS49G0R1A2S44Z2Z1fA2A2S35S3aS49G0S16aQ20G0S162S154S161R2A1S161S4bG0Z10A2A1A3A3A2S40S49G0R2A2Z10000A2A3F_;Fx;").
Proof.
  intros x Hx. pose proof (urange x) as R.
  assert (L : bv_unsigned (low32 x) = bv_unsigned x).
  { unfold low32. rewrite bv_extract_unsigned. change (Z.of_N 0) with 0. rewrite Z.shiftr_0_r. unfold bv_wrap. change (bv_modulus 32) with (2 ^ 32). apply Z.mod_small. lia. }
  assert (S : bv_unsigned (alu32 ALU_SRL (low32 x) (low32 (Z_to_bv 64 16))) = bv_unsigned x / 65536).
  { unfold alu32, alu. rewrite bv_shiftr_unsigned. rewrite L.
    replace (bv_unsigned (bv_and (low32 (Z_to_bv 64 16)) (Z_to_bv 32 31))) with 16 by reflexivity.
    rewrite Z.shiftr_div_pow2 by lia. reflexivity. }
  rewrite sext64_32_small; rewrite S; [reflexivity|]. apply Z.div_lt_upper_bound; lia.
Qed.

Lemma slot_addr_val : ltac2:(tb__ "0|2|
S1S3fS49Q40M0S3R1PafM1A2A2S44Z2Z1fA2A2S35S3aS49G0SeR2Sf2A2A2S3dS105S43Z8S40S49G0S3R2G1A2A2Z10000A2A2A2A3F_;Frho;").
Proof.
  intros rho Hs. unfold slot_addr, add, vS. cbn [eval]. rewrite add_val, sll_val, srlw16_small by exact Hs.
  change (3 mod 64) with 3. rewrite Z.shiftl_mul_pow2 by lia. pose proof (urange (rw rho 175%positive)).
  assert (0 <= bv_unsigned (rw rho 175%positive) / 65536 < 2 ^ 15).
  { split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
  unfold MAP1. rewrite u64_lit by lia. rewrite (Z.mod_small (_ * 2 ^ 3)) by lia. rewrite Z.mod_small by lia. lia.
Qed.

Lemma node_addr_val : ltac2:(tb__ "0|2|
S1S3eS3dS49Q40M0S3R1PacM1A2A2Sf7A2Z7fffff800000A2S35S3aS49G0SeR2SefA2A2S3dS49G0S3R2G1A2A2S43Z10S41S49G0S3R2PafA2A2Z10000A2A2A2A3F_;Frho;").
Proof.
  intros rho Hb. unfold node_addr, add, vB, vS. cbn [eval]. rewrite add_val, sll_val, and_val.
  change (4 mod 64) with 4. rewrite u64_lit by lia. change 65535 with (Z.ones 16). rewrite Z.land_ones by lia.
  rewrite Z.shiftl_mul_pow2 by lia. pose proof (Z.mod_pos_bound (bv_unsigned (rw rho 175%positive)) (2 ^ 16) ltac:(lia)).
  pose proof (urange (rw rho 172%positive)). unfold NBSZ in Hb.
  rewrite (Z.mod_small (_ * 2 ^ 4)) by lia. rewrite Z.mod_small by lia. change (2 ^ 16) with 65536 in *. lia.
Qed.

Lemma land_mask31 : ltac2:(tb__ "0|0|
S3aS36S3eZ0R1A2S3fR1S44Z2Z1fA2A2A2S35S3aS47R2Z7fffffffA2R2A3F_;Fw;").
Proof.
  intros w Hw. change 2147483647 with (Z.ones 31). rewrite Z.land_ones by lia. apply Z.mod_small. lia.
Qed.

Lemma present_cell4 : ltac2:(tb__ "0|0|
S151S3aS152R2R1S3dR1Z4A2A3S37S3aS3aS36S36S3eZ0R1A2S3fR1S44Z2Z20A2A2A2S107R4R3U4R1A4A2Lv;A2F_;Fa;Fm;").
Proof.
  intros m a Hp.
  destruct (Hp a ltac:(lia)) as [b0 H0]. destruct (Hp (a + 1) ltac:(lia)) as [b1 H1]. destruct (Hp (a + 2) ltac:(lia)) as [b2 H2]. destruct (Hp (a + 3) ltac:(lia)) as [b3 H3].
  exists (bv_unsigned (le_bytes_to_word [b0; b1; b2; b3])).
  pose proof (bytes_le_to_Z_bound [b0; b1; b2; b3]) as B. cbn [length] in B.
  assert (E : Z_to_bv 64 (bv_unsigned (le_bytes_to_word [b0; b1; b2; b3])) = le_bytes_to_word [b0; b1; b2; b3]) by apply Z_to_bv_bv_unsigned.
  split.
  - unfold le_bytes_to_word. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_small by lia. change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in B. lia.
  - unfold cellZ, cell_ok. cbn [c_addr c_w c_val]. intros k Hk. rewrite E. rewrite (enc_bytes_le_word 4) by (reflexivity || lia).
    destruct k as [|[|[|[|k]]]]; cbn [nth]; rewrite ?Z.add_0_r; try assumption. lia.
Qed.

Lemma shl44_shr41 : ltac2:(tb__ "0|2|
S3aS36S3eZ0R1A2S3fR1S44Z2M0Z40A2M1A2A2S35S3aS40S41S43R2S44G0Z2cA2A2G1A2S44G0Z29A2A2S43Z8S41R2S44G0Z14A2A2A2A3F_;Fx;").
Proof.
  intros x Hx.
  pose proof (Z.div_mod x (2^20) ltac:(lia)) as E.
  pose proof (Z.mod_pos_bound x (2^20) ltac:(lia)) as B.
  set (q := x / 2^20) in E. set (r := x mod 2^20) in *.
  rewrite E. replace ((2 ^ 20 * q + r) * 2 ^ 44) with (r * 2^44 + q * 2^64) by lia.
  rewrite Z.mod_add by lia. rewrite Z.mod_small by lia.
  replace (r * 2^44) with ((8*r) * 2^41) by lia. rewrite Z.div_mul by lia. lia.
Qed.

Lemma shr16_mask16 : ltac2:(tb__ "0|3|
S3aS36S3eZ0R1A2S3fR1S44Z2M0Z40A2A2A2S35S3aS45S48R2Z10M1A2M2S41G2S44G0Z4A2A2A2S43G1S40R2S44G0Z14A2A2A2A3F_;Fx;").
Proof.
  intros x Hx. rewrite Z.shiftr_div_pow2 by lia.
  pose proof (Z.div_mod (x / 2^16) (2^4) ltac:(lia)) as E.
  replace (x / 2 ^ 20) with (x / 2^16 / 2^4) by (rewrite Z.div_div by lia; reflexivity). lia.
Qed.

Lemma slotN_addr_val : ltac2:(tb__ "0|2|
S1S3aS35S3aS49Q40M0S3R2Pb1A2A2R1A3S36S3eZ0R2A2S3fR2S45S44Z2M1Z1fA2G1A2A2A2S35S3aS49G0SeR4Sf1A2A2S3dS105S43Z8S40S3dR3Z1A2Z10000A2A2A2A3F_;F_;FN;Frho;").
Proof.
  intros rho N HN HB. unfold slotN_addr, idN, add, vN, MAP1. cbn [eval]. rewrite add_val, sll_val, srl_val, add_val, HN.
  change (16 mod 64) with 16. change (3 mod 64) with 3. rewrite !u64_lit by lia. rewrite (Z.mod_small (N + 1)) by lia.
  rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia. change (2 ^ 16) with 65536.
  assert (0 <= (N + 1) / 65536 < 2 ^ 15) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  rewrite (Z.mod_small (_ * 2 ^ 3)) by lia. rewrite Z.mod_small by lia. lia.
Qed.

Lemma nn_addr_val : ltac2:(tb__ "0|3|
S1S3aS35S3aS49Q40M0S3R2Pb1A2A2R1A3S36S3eZ0R2A2S3fR2S45S44Z2M1Z1fA2G1A2A2A2S3eS3dS49G0S3R4Pb2M2A2A2Sf7A2Z7fffff800000A2S35S3aS49G0SeR5SeeA2A2S3dS49G0S3R5G2A2A2S43Z10S41S3dR4Z1A2Z10000A2A2A2A3F_;F_;F_;FN;Frho;").
Proof.
  intros rho N HN HB Hb. unfold nn_addr, idN, add, vNB, vN. cbn [eval]. rewrite add_val, sll_val, and_val, add_val, HN.
  change (4 mod 64) with 4. rewrite !u64_lit by lia. rewrite (Z.mod_small (N + 1)) by lia. change 65535 with (Z.ones 16). rewrite Z.land_ones by lia.
  rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 16) with 65536. pose proof (Z.mod_pos_bound (N + 1) 65536 ltac:(lia)).
  pose proof (urange (rw rho 178%positive)). unfold NBSZ in Hb.
  rewrite (Z.mod_small (_ * 2 ^ 4)) by lia. rewrite Z.mod_small by lia. lia.
Qed.

Lemma bd_addr_val : ltac2:(tb__ "0|1|
S1S3aS35S3aS49Q40M0S3R2Pb3A2A2R1A3S36S3eZ0R2A2S3fR2S44Z2Z20A2A2A2S35S3aS49G0SeR4Sc1A2A2S3dSf9S43Z10S40R3Z100000A2A2A2A3F_;F_;FF;Frho;").
Proof.
  intros rho F HF HB. unfold bd_addr, add, vF, STORE. cbn [eval]. rewrite add_val, sll_val, srl_val, HF.
  change (20 mod 64) with 20. change (4 mod 64) with 4. rewrite !u64_lit by lia. rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia.
  change (2 ^ 20) with 1048576. assert (0 <= F / 1048576 < 2 ^ 12) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  rewrite (Z.mod_small (_ * 2 ^ 4)) by lia. rewrite Z.mod_small by lia. lia.
Qed.

Lemma fr_addr_val : ltac2:(tb__ "0|2|
S1S3aS35S3aS49Q40M0S3R2Pb3A2A2R1A3S36S3eZ0R2A2S3fR2S44Z2Z20A2A2A2S3eS3dS49G0S3R4Pb4M1A2A2Sf8A2Z7fffff800000A2S35S3aS49G0SeR5SbcA2A2S3dS49G0S3R5G1A2A2S43Z8S41R4Z100000A2A2A2A3F_;F_;F_;FF;Frho;").
Proof.
  intros rho F HF HB Hb. unfold fr_addr, add, vF, vD. cbn [eval]. rewrite add_val, srl_val, sll_val, HF.
  change (44 mod 64) with 44. change (41 mod 64) with 41. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. rewrite (shl44_shr41 F) by lia.
  change (2 ^ 20) with 1048576. pose proof (Z.mod_pos_bound F 1048576 ltac:(lia)). pose proof (urange (rw rho 180%positive)).
  unfold FBSZ in Hb. rewrite Z.mod_small by lia. lia.
Qed.

Lemma stc_addr_val : ltac2:(tb__ "0|1|
S1S3aS35S3aS49Q40M0S3R2Pb3A2A2R1A3S36S3eZ0R2A2S3fR2S44Z2Z20A2A2A2S35S3aS49G0SeR4Sd3A2A2S3dSf9S43Z10S40R3Z100000A2A2A2A3F_;F_;FF;Frho;").
Proof.
  intros rho F HF HB. unfold stc_addr, add, vF, STORE. cbn [eval]. rewrite add_val, and_val, srl_val, HF.
  change (16 mod 64) with 16. rewrite !u64_lit by lia. change 18446744073709551600 with (2 ^ 64 - 2 ^ 4).
  assert (HS : 0 <= Z.shiftr F 16 < 2 ^ 16) by (rewrite Z.shiftr_div_pow2 by lia; split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  rewrite land_high_mask by lia. rewrite shr16_mask16 by lia. change (2 ^ 20) with 1048576.
  assert (0 <= F / 1048576 < 2 ^ 12) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  rewrite Z.mod_small by lia. lia.
Qed.

Section Skel.
Variable K : DG -> jpredA.
Hypothesis HKD : ltac2:(tb__ "0|0|
S10bS3cVK;S98A3").
Variable ok : assn.
Hypothesis HKok : ltac2:(tb__ "0|0|
S5cS4fS3cVok;VK;R1A1A3FG;").

Hypothesis HKokp : ltac2:(tb__ "0|0|
S5cS15dS3cVok;VK;R1A1A3FG;").
Variable sz : Z.
Hypothesis Hsz : 1 <= sz <= SZMAXT.

Variables (rho0 : valuation) (tp0 : list word) (G0 : DG).

Hypothesis Htol : ltac2:(tb__ "0|0|
S39S3eVsz;Se0A2S3eS5dVG0;A1S3dS171Z1A2A2A2").

Variable alloc_ceiling : Z.
Hypothesis alloc_ceiling_valD : 140735332483072 <= alloc_ceiling <= 140737479966720.
Hypothesis HT0 : ltac2:(tb__ "0|1|
S36S3eValloc_ceiling;S3dS49Q40M0S3Vrho0;PaA2A2S4cG0S3Vrho0;S139A2A2A2A2S3eValloc_ceiling;S49G0S3Vrho0;PcA2A2A2A2").
Hypothesis HKT : ltac2:(tb__ "0|0|
S5cS1S27S4aQ40A1A1S27S12cA1S12aVK;R5R4R3R2R1A5S35S3aS12dS12bR2A1A1Valloc_ceiling;A3F_;Fmd;Ftr;Ftp;Frho;FG;").
Definition TOPr (r : valuation) : Prop := ltac2:(tb__ "0|1|
S36S3eValloc_ceiling;S3dS49Q40M0S3Vr;PaA2A2S4cG0S3Vr;S139A2A2A2A2S3eValloc_ceiling;S49G0S3Vr;PcA2A2A2A2").

Definition REL (G : DG) (r : valuation) : Prop := ltac2:(tb__ "0|2|
S36S142S98Vrho0;Vr;A3S36S4aQ40M0A1S38SffVG;S49G0R1A2A2A1S35S2fS4aQ8A1A1M1SdVr;R2A2SdVrho0;R2A2A3F_;Fa;S3aS38SfeVG;R1A2A1S35G1S150S3cSdVr;A1R2A3S150S3cSdVrho0;A1R2A3A3F_;Fz;A2A2").

Definition pend : Type := ltac2:(tb__ "0|0|
S1S27S4aQ40A1A1S12aOF_;F_;F_;").
Definition PD0 : pend := fun _ _ _ => True.
Definition pend_stable (PD : pend) : Prop := ltac2:(tb__ "0|0|
S1S1S27S4aQ40A1A1S12aS12aSbS98R5R4A3S16eS3cR4R3R2A4VPD;R7R5R4A3VPD;R7R6R4A3F_;F_;F_;Fmd';Fmd;Ftp;Frho';Frho;").
Lemma PD0_stable : pend_stable PD0. Proof. unfold pend_stable, PD0. intros. exact I. Qed.

Definition JJ2 (Gk Gd : DG) (PD : pend) : jpredA := ltac2:(tb__ "0|0|
S16cS76VGk;A1S1S27S4aQ40A1A1S27S12cA1S12aS36VK;VGk;R4R3R2R1A5S36S10eS3cVGd;R4R1R3A5VPD;R4R3R1A3A2A2Lmd;Ltr;Ltp;Lrho;A2").
Definition JJ (G : DG) : jpredA := ltac2:(tb__ "0|0|
S6aVG;VG;S8dA3").
Definition QD : assn := ltac2:(tb__ "0|1|
S168S3cS98Vrho0;Vtp0;S25S2bS55S167A2M0S2cS55S167Sc7Vsz;A1S10aS3cVK;VG0;A3A4S26G0A1A3A5").

Lemma REL_agree : ltac2:(tb__ "0|0|
S5cS1S1S76R3R2A2SbS98R3R2A3S76R5R3A2F_;F_;Fr';Fr;FG;").
Proof.
  intros G r r' (A & B & C) (D & E & F). split; [|split].
  - destruct A as [A1 A2]. split; [intros i Hi; rewrite (A1 i Hi); apply D; exact Hi | intros l; rewrite (A2 l); apply E].
  - intros a Ha. rewrite <- F. apply B. exact Ha.
  - intros z Hz. rewrite <- (C z Hz). unfold view. destruct ((0 <=? z) && (z <? 2 ^ 64))%bool; [|reflexivity]. unfold rd_of. rewrite F. reflexivity.
Qed.

Lemma TOPr_of_REL : ltac2:(tb__ "0|0|
S5cS1S76R2R1A2S6dR2A1F_;Fr;FG;").
Proof.
  intros G r ([A1 _] & _ & _). unfold TOPr. unfold NPRE, V_DEPTH in *.
  rewrite <- (A1 10%positive), <- (A1 15%positive), <- (A1 12%positive) by (cbv; reflexivity). exact HT0.
Qed.
Lemma TOPr_of_JJ : ltac2:(tb__ "0|0|
S5cS5cS75S55S1S27S4aQ40A1A1S11bS4dS3cS6aR7R6R5A3R4R3R2R1A6S6dR4A1F_;Fw;Ftp;Fr;FX;FPD;FGd;FGk;").
Proof. intros Gk Gd PD X r tp w [_ [HR _]]. exact (TOPr_of_REL _ _ HR). Qed.

Lemma nb_top : ltac2:(tb__ "0|0|
S5cS5cS1S27S4aQ40A1A1S27S12cA1S12aS3aVK;R7R5R4R3R2A5SfaR7R3R5A3S117S3aR3S60R8A1A3S3eS3dR4Sf7A2Valloc_ceiling;A2F_;F_;F_;Fb;Fmd;Ftr;Ftp;Frho;FG;FGk;").
Proof.
  intros Gk G rho tp tr md b HK HV Hin. rewrite <- (HKT _ _ _ _ _ HK).
  exact (dv_top _ _ _ HV (b, NBSZ) ltac:(unfold dblocks; apply in_or_app; left; apply in_map_iff; exists b; split; [reflexivity|exact Hin])).
Qed.
Lemma fb_top : ltac2:(tb__ "0|0|
S5cS5cS1S27S4aQ40A1A1S27S12cA1S12aS3aVK;R7R5R4R3R2A5SfaR7R3R5A3S117S3aR3S5eR8A1A3S3eS3dR4Sf8A2Valloc_ceiling;A2F_;F_;F_;Fb;Fmd;Ftr;Ftp;Frho;FG;FGk;").
Proof.
  intros Gk G rho tp tr md b HK HV Hin. rewrite <- (HKT _ _ _ _ _ HK).
  exact (dv_top _ _ _ HV (b, FBSZ) ltac:(unfold dblocks; apply in_or_app; right; apply in_map_iff; exists b; split; [reflexivity|exact Hin])).
Qed.

Lemma JJ2_stable : ltac2:(tb__ "0|0|
S5cS5cS75S3bS7fR2A1S14aS98R2A2S4eS3cR3S6aR6R5R4A3A3F_;F_;Fn;FPD;FGd;FGk;").
Proof.
  intros Gk Gd PD n HPD Hn. apply (stableA_le _ NPRE n Hn). unfold JJ2. apply stableA_withG; [apply REL_agree|].
  intros rho rho' tp tr md md' Hag Hme [HK [HD HP]]. split; [|split].
  - eapply (kd_stable segsA K NPRE HKD); eauto.
  - destruct HD as [HM HV]. split.
    + destruct Hag as (_ & _ & Hrm). replace (rm rho') with (rm rho); [exact HM|]. apply functional_extensionality. exact Hrm.
    + destruct Hme as ((mat' & ->) & _). eapply depot_vm_mat; [| |exact HV]; reflexivity.
  - eapply HPD; eauto.
Qed.
Lemma JJ_stable : ltac2:(tb__ "0|0|
S5cS3bS14aS98R1A2S4eS3cR2S63R3A1A3F_;Fn;FG;").
Proof. intros G n Hn. apply JJ2_stable; [apply PD0_stable | exact Hn]. Qed.

Lemma JJ2_ok : ltac2:(tb__ "0|0|
S5cS5cS75S4fS3cVok;S6aR3R2R1A3A3FPD;FGd;FGk;").
Proof. intros Gk Gd PD rho tp tr ms md msv' [_ [HK _]]. exact (HKok Gk rho tp tr ms md msv' HK). Qed.
Lemma JJ_ok : ltac2:(tb__ "0|0|
S5cS4fS3cVok;S63R1A1A3FG;").
Proof. intros G. apply JJ2_ok. Qed.

Lemma stage_run : ltac2:(tb__ "0|1|
S50S2eS27S3aA1S55S27S52A1M0S1S27S4aQ40A1A1S11fS4fS3cVok;R8A3S4eS3cS98R9A3S35G0S9aR9R8R7A3R6A3S38S35G0R7S26S52A1A3A1S35S28SaS51R9A1A1S30A3S14aS98S8S51RaA1A1A2S52S1S117S52R2RcA3SbS8S51ReA1A1RcR2A3S11dS3cVok;S4dS3cR12S58R4A1R3RcA5RbA4F_;F_;Frho';FL;S11eS3cVok;S4dS3cRfRcRaR9A5R8A4F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho;Fl;FA;Fcuts;Ffuel;FJ;").
Proof.
  intros J fuel cuts A l rho tp Q Hok Hst Hr Hne Hlen Hnx Hk.
  eapply triple1_seq_l.
  - eapply (sym_run_soundA segsA fuel cuts A l ok J rho tp (runA_some _ _ _ _ Hr Hne) Hok Hlen (stableA_le J _ _ Hnx Hst)).
  - apply triple_LQA_of_leaves. exact Hk.
Qed.

Lemma estage_run : ltac2:(tb__ "0|1|
S50S2eS27S3aA1S55S27S52A1M0S1S27S4aQ40A1A1S11bOF_;S4eS3cS98R8A3S35G0S9aR8R7R6A3R5A3S38S35G0R6S26S52A1A3A1S35S28SaS51R8A1A1S30A3S14aS98S8S51R9A1A1A2S52S1S117S52R2RbA3SbS8S51RdA1A1RbR2A3S11cS3cS4dS3cR11S58R4A1R3RbA5RaA3F_;F_;Frho';FL;S11cS3cS4dS3cReRbR9R8A5R7A3F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho;Fl;FA;Fcuts;Ffuel;FJ;").
Proof.
  intros J fuel cuts A l rho tp Q Hst Hr Hne Hlen Hnx Hk.
  eapply etriple_seq.
  - eapply (sym_run_etripleA segsA fuel cuts A l J rho tp Hlen (stableA_le J _ _ Hnx Hst) (runA_some _ _ _ _ Hr Hne)).
  - apply etriple_LQA_of_leaves. exact Hk.
Qed.

Variable E1s : axst.

Hypothesis ENT_PRE1 : ltac2:(tb__ "0|0|
S35S28S54Sb1Vsz;A1Sc8Vsz;A1S26S2bS3bS2A2A1A3S2aA3").
Hypothesis RUN1 : ltac2:(tb__ "0|0|
S35S27S52A1S9aU320S25S3aZ7eb04S26S3aA1A3Sc8Vsz;A1A3S25S52S53VE1s;S126A2S26S52A1A3A3").

Lemma stage_pre : ltac2:(tb__ "0|1|
S11fS1S11dS3cVok;S4dS3cS63VG0;A1M0VE1s;R1Vtp0;A5R2A4Frho1;S11dS3cVok;S4dS3cG0Sb1Vsz;A1Vrho0;Vtp0;A5R2A4F_;FQ;").
Proof.
  intros Q HE1.
  eapply triple_conseq with (P := SPA segsA (JJ G0) (PreD1 sz) (rho_sub rho0 []) tp0) (Q := Q); [| intros w Hw; exact Hw |].
  { intros w Hw. exact (SPA_entails segsA (JJ G0) NPRE (PreD sz) (PreD1 sz) [] rho0 tp0 w ENT_PRE1 eq_refl (JJ_stable G0 NPRE ltac:(lia)) Hw). }
  apply triple1_triple. eapply (stage_run (JJ G0)); [apply JJ_ok | apply JJ_stable; lia | exact RUN1 | discriminate | reflexivity | apply Pos.leb_le; reflexivity |].
  intros L rho' [<-|[]] Hag. cbn [la_state]. apply HE1.
Qed.

Lemma estage_pre : ltac2:(tb__ "0|1|
S11bOF_;S1S11cS3cS4dS3cS63VG0;A1M0VE1s;R1Vtp0;A5R2A3Frho1;S11cS3cS4dS3cG0Sb1Vsz;A1Vrho0;Vtp0;A5R2A3F_;FQ;").
Proof.
  intros Q HE1.
  eapply etriple_conseq with (P := SPA segsA (JJ G0) (PreD1 sz) (rho_sub rho0 []) tp0) (Q := Q); [| intros w Hw; exact Hw |].
  { intros w Hw. exact (SPA_entails segsA (JJ G0) NPRE (PreD sz) (PreD1 sz) [] rho0 tp0 w ENT_PRE1 eq_refl (JJ_stable G0 NPRE ltac:(lia)) Hw). }
  eapply (estage_run (JJ G0)); [apply JJ_stable; lia | exact RUN1 | discriminate | reflexivity | apply Pos.leb_le; reflexivity |].
  intros L rho' [<-|[]] Hag. cbn [la_state]. apply HE1.
Qed.

Let rE1 (i : nat) : sv := ltac2:(tb__ "0|0|
S114S2Vi;SfS51VE1s;A1A1S5Z0A1A4").
Definition VS_T : list positive := ltac2:(tb__ "0|0|
S25S3bPb7S25S3bPabS25S3bPb6S25S3bPaaS26S3bA1A3A3A3A3").

Let S_T1b : sstate := ltac2:(tb__ "0|0|
S51VE1s;A1S1dS13ScR1A1SfR1A1S16R1A1S15R1A1S17R1A1S29S0S6R1A1S25S0S97S96A1S26S0A1A3A3S7R1A1S95SaR1A1A9TS;").
Hypothesis E1_X : ax_X E1s = [].
Hypothesis E1_vars : ltac2:(tb__ "0|0|
S35S28S140S124S7dA1S51VE1s;A1A2S2aA3").
Hypothesis E1_bvars : ltac2:(tb__ "0|0|
S35S28S13fS124S7dA1S56VE1s;A1A2S2aA3").
Hypothesis E1_skel : ltac2:(tb__ "0|1|
S35S27S2bS2bS2S2A2S2A2M0A1S113S0G0S122S6S51VE1s;A1A1A4S113S0G0S122S29S0S25S0S138S25S0Sa3S26S0A1A3A3S29S0S137Sa4A3A3A4A3").
Hypothesis E1_F : ltac2:(tb__ "0|0|
S35S28S125S9eS7S51VE1s;A1A1A2S2aA3").
Hypothesis E1_r18 : ltac2:(tb__ "0|0|
S35S2VrE1;U12A1SaaS18S154S18S155VrE1;U13A1S5Z2cA1A3S5Z2aA1A3S5S104A1A2A3").
Hypothesis E1_rvars : ltac2:(tb__ "0|0|
S35S28S116S2S13fS124S7dA1A1S25S2VrE1;UaA1S25S2VrE1;U12A1S25S2VrE1;U13A1S26S2A1A3A3A3A3S2aA3").
Hypothesis E1_nx : ltac2:(tb__ "0|0|
S35S28S14cS8S51VE1s;A1A1S95A2S2aA3").
Hypothesis T1b_swf : swf S_T1b = true.
Hypothesis T1_swf : ltac2:(tb__ "0|0|
S35S28S20S51Sb5VE1s;A1A1A1S2aA3").
Hypothesis T1_sd : ltac2:(tb__ "0|4|
S35S2fS2bS27S2bS2S2A2M0A1M1S27S4A1M2A2M3A1S15aVS_T1b;S51Sb5VE1s;A1A1A2S31G3S2cG1G2S25G0S2cS2S2VrE1;UaA1S9Pb7A1A4S25G0S2cS2S2VrE1;U12A1Sf4A4S25G0S2cS2S2VrE1;U13A1Sf3A4S26G0A1A3A3A3Sa5A4A2A3").

Lemma entry_objs_ranges_mm : ltac2:(tb__ "0|2|
S1S147S27S0A1M0G0S112S0S1eS3cR4R3A3R2A3S0S117S0R1R3A3S117S0R2R5A3F_;Fo;S35S27S2bS2bS2S2A2S2A2M1A1S113S0G1S122R3A4S113S0G1S122S29S0S25S0S138S25S0Sa3S26S0A1A3A3S29S0S137Sa4A3A3A4A3S112S4S1aR7A1S9eA3S6dR8A1S3aS3aS3eSf9R2A2S3eR2Valloc_ceiling;A2S3eR4R3A2S112S0S0S19S11RfR1A2S2cS3aS3aR6R5A4A2Lo';RbA3F_;F_;F_;Fhi;Flo;F_;F_;F_;F_;F_;Fobjs;Fall;Fms;Frho;").
Proof.
  intros rho ms all objs Hall Ho Hsk HF [HSW H12] lo hi Hr1 Hr2 Hle.
  assert (Hhigh : holds rho F_sp_high).
  { apply (proj1 (Forall_forall _ _) HF). unfold F_D, pre_facts. apply in_or_app. left. cbn. tauto. }
  pose proof alloc_ceiling_valD as ACV.
  destruct objs as [|osw rest]; [cbn in Hsk; discriminate|]. cbn [map app] in Hsk.
  assert (SKsw : skel osw = (SVar 10, SVar V_DEPTH, SLit 0)) by exact (f_equal (hd (skel osw)) Hsk).
  assert (SKrest : map skel rest = map skel (O_trD :: A_globals ++ RT_D)) by exact (f_equal (@tl _) Hsk).
  destruct (sw_range_mm segsA rho ms all osw Hall ltac:(apply Ho; left; reflexivity) SKsw Hhigh) as (SW1 & SW2 & SW3).
  pose proof (sw_lo_mm rho osw SKsw) as SW0.
  constructor.
  - unfold ranges_disjoint. cbn [fst snd]. unfold STORE in *. lia.
  - apply (Forall_ranges_skel rho (fun r => ranges_disjoint r (lo, hi)) rest _ SKrest).
    unfold O_trD, A_globals, O_got, O_rtc, RT_D, O_flag, O_pg, O_pgb, O_die, O_dpm, O_mlim, carved, GOT_LO, GOT_HI, RTC_LO, RTC_HI, CSDFLAG, DIEGATE, DPMCELL, MLIMCELL, v12.
    repeat apply Forall_cons; try apply Forall_nil; unfold ranges_disjoint; rewrite ?obj_range_mk by lia; cbn [fst snd eval];
      rewrite ?u64_lit by lia; unfold STORE in *; lia.
Qed.

Lemma smatch_objs_hold : ltac2:(tb__ "0|1|
S1S1dS2bS27S12cA1M0S143A2S1fS3cR3R2R1A4S112S0S1eS3cR4S145S32G0S143R2A3A1A3S6R3A1A3F_;Fw;FS;Frho;").
Proof. intros rho S w Hsm. destruct Hsm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hall & _ & _) & _). exact Hall. Qed.

Lemma entry_objs_ranges : ltac2:(tb__ "0|1|
S1S1dS2bS27S12cA1S143A2S27S0A1S1fS3cR4R3R2A4S0S117S0R1R3A3S117S0R2S6R6A1A3F_;Fo;S35S27S2bS2bS2S2A2S2A2M0A1S113S0G0S122R3A4S113S0G0S122S29S0S25S0S138S25S0Sa3S26S0A1A3A3S29S0S137Sa4A3A3A4A3S112S4S1aR7A1S9eA3S6dR8A1S3aS3aS3eSf9R2A2S3eR2Valloc_ceiling;A2S3eR4R3A2S112S0S0S19S11RfR1A2S2cS3aS3aR6R5A4A2Lo';RbA3F_;F_;F_;Fhi;Flo;F_;F_;F_;F_;F_;Fobjs;Fw;FS;Frho;").
Proof.
  intros rho S w objs Hsm. exact (entry_objs_ranges_mm rho _ _ objs (smatch_objs_hold rho S w Hsm)).
Qed.

Lemma glue_T : ltac2:(tb__ "0|2|
S1S11bS4dS3cS63VG0;A1M0VE1s;R2Vtp0;R1A6S37S1S1S36S4dS3cG0Sb5VE1s;A1R1Vtp0;R3A6S36S39S35S3aS49Q40S3R1PaaA2A2M1Z0A3S36S3eZ1G1A2S3eG1S5dVG0;A1A2A2A2S123S3cR1S97S96A1A3A2A2Lrho2;A2F_;Fw;Frho1;").
Proof.
  intros rho1 w H.
  destruct w as [tr [ms md]].
  pose proof H as [HsmA [HREL [HK [[HM HV] _]]]].
  pose proof (SPA_facts segsA _ _ _ _ _ H) as HFall.
  pose proof (holds_inclb rho1 _ _ E1_F HFall) as HFD.
  set (h := eval rho1 (rE1 19)).
  set (p := eval rho1 (rE1 18)).
  set (j := eval rho1 (rE1 10)).
  assert (Hp : bv_unsigned p = DEPOT + 4 * (bv_unsigned h mod 2 ^ 20)).
  { unfold p.
    rewrite E1_r18.
    unfold add.
    cbn [eval].
    fold h.
    rewrite add_val, srl_val, sll_val.
    change (44 mod 64) with 44.
    change (42 mod 64) with 42.
    rewrite Z.shiftl_mul_pow2 by lia.
    rewrite Z.shiftr_div_pow2 by lia.
    pose proof (urange h) as Rh.
    unfold DEPOT.
    rewrite u64_lit by lia.
    rewrite (shl44_shr42 _ Rh).
    pose proof (Z.mod_pos_bound (bv_unsigned h) (2 ^ 20) ltac:(lia)) as MB.
    rewrite Z.mod_small by lia.
    lia. }
  set (i := bv_unsigned h mod 2 ^ 20) in Hp.
  assert (Hi : 0 <= i < TABSZ).
  { unfold i, TABSZ. apply Z.mod_pos_bound. lia. }
  destruct (dm_tab _ _ HM i Hi) as (w0 & Hcell & Hw0r).
  pose proof (dm_N _ _ HM) as [HN _].
  set (bs := [(183%positive, j); (171%positive, p); (182%positive, h); (170%positive, Z_to_bv 64 w0)]).
  set (rho2 := rho_sets rho1 bs).
  assert (Hfst : map fst bs = VS_T) by reflexivity.
  assert (Hnd : List.NoDup (map fst bs)).
  { rewrite Hfst. unfold VS_T. repeat constructor; cbn; lia. }
  assert (E171 : rw rho2 171%positive = p).
  { apply rho_sets_get; [exact Hnd | right; left; reflexivity]. }
  assert (E170 : rw rho2 170%positive = Z_to_bv 64 w0).
  { apply rho_sets_get; [exact Hnd | right; right; right; left; reflexivity]. }
  assert (E182 : rw rho2 182%positive = h).
  { apply rho_sets_get; [exact Hnd | right; right; left; reflexivity]. }
  assert (E183 : rw rho2 183%positive = j).
  { apply rho_sets_get; [exact Hnd | left; reflexivity]. }
  destruct (rho_sets_rl_rm bs rho1) as [Hrl2 Hrm2].
  fold rho2 in Hrl2, Hrm2.
  pose proof E1_rvars as RV. cbn [forallb] in RV.
  apply andb_prop in RV as [RV10 RV]. apply andb_prop in RV as [RV18 RV]. apply andb_prop in RV as [RV19 _].
  assert (EVold : forall e, sv_vars_all (notin_vars VS_T) e = true -> eval rho2 e = eval rho1 e).
  { intros e He. symmetry. apply (eval_agree_vars (notin_vars VS_T)); [| |exact He].
    - intros v Hv. unfold rho2. symmetry. apply rho_sets_other. rewrite Hfst. apply notin_vars_true. exact Hv.
    - intros l. rewrite Hrl2. reflexivity. }
  exists rho2.
  assert (Hw0 : bv_unsigned (rw rho2 170%positive) = w0).
  { rewrite E170, u64_lit; lia. }
  assert (CIV : cells_in_view rho2 (rd_of segsA (rm rho2)) (DEPOT + 4 * i) [(0, 4%nat, vW)]).
  { unfold cells_in_view. constructor; [|constructor]. intros jj Hjj.
    refine (civ_cell rho2 (rm rho2) (DEPOT + 4 * i) 0 4 w0 vW _ _ _ _ jj Hjj).
    + rewrite Hrm2. rewrite Z.add_0_r. exact Hcell.
    + cbn [eval]. exact E170.
    + unfold DEPOT, TABSZ in *. lia.
    + unfold DEPOT, TABSZ in *. lia. }
  split; [|split; [rewrite Hw0; exact Hw0r|]].
  2:{ exists vP, 0, 4%nat, vW. unfold vP at 2 3 4. cbn [eval]. rewrite E171, Hp. unfold DEPOT, TABSZ in *.
      split; [reflexivity|]. repeat (split; [lia|]). exact CIV. }

  assert (H1 : SPA segsA (JJ G0) E1s rho2 tp0 (tr, mkCfg ms md)).
  { unfold rho2. eapply (SPA_bindV segsA (JJ G0) NPRE); [exact E1_X | apply JJ_stable; lia | | rewrite Hfst; exact E1_vars | rewrite Hfst; exact E1_bvars | exact H].
    rewrite Hfst. unfold VS_T, NPRE. intros v Hv. cbn in Hv. lia. }
  pose proof (SPA_facts segsA _ _ _ _ _ H1) as HFall2.
  pose proof (holds_inclb rho2 _ _ E1_F HFall2) as HFD2.

  assert (H2 : SPA segsA (JJ G0) (ax_setS E1s S_T1b) rho2 tp0 (tr, mkCfg ms md)).
  { unfold S_T1b, O_tw.
    apply (SPA_carve_obj segsA (JJ G0) rho2 E1s tp0 _ vP 0 4 [(0, 4%nat, vW)] NXD H1 T1b_swf).
    - apply Pos.leb_le. exact E1_nx.
    - lia.
    - lia.
    - lia.
    - lia.
    - unfold vP. cbn [eval]. rewrite E171, Hp. unfold DEPOT. lia.
    - unfold vP. cbn [eval]. rewrite E171, Hp. unfold DEPOT, TABSZ in *. lia.
    - unfold cells_inside. constructor; [|constructor]. cbn. lia.
    - pose proof (proj1 H1) as Hsm1. unfold smatchA, virt in Hsm1. cbn [fst snd cfg_ms cfg_model w_tr w_cfg] in Hsm1.
      unfold vP. cbn [eval]. rewrite E171, Hp.
      apply (entry_objs_ranges rho2 (ax_S E1s) _ _ (proj1 Hsm1) ltac:(intros o Ho; exact Ho) E1_skel HFD2 ltac:(first [assumption | eapply TOPr_of_REL; eassumption | eapply TOPr_of_JJ; eassumption])); unfold STORE, DEPOT, TABSZ in *; lia.
    - unfold vP. cbn [eval]. rewrite E171, Hp. intros off Hoff. split; [apply wok_of_imageA; unfold DEPOT, TABSZ in *; lia | apply rd_of_imageA; unfold DEPOT, TABSZ in *; lia].
    - unfold vP. cbn [eval]. rewrite E171, Hp. exact CIV.
    - unfold xwords_clear. cbn [ax_X]. rewrite E1_X. intros rr y jj [].
  }

  assert (H3 : SPA segsA (JJ G0) (ax_setS (ax_setS E1s S_T1b) (ax_S (mkT1 E1s))) rho2 tp0 (tr, mkCfg ms md)).
  { eapply (SPA_restate segsA (JJ G0) rho2 _ (ax_S (mkT1 E1s)) tp0 _ _ _ T1_swf).
    - cbn [ax_S ax_setS]. exact T1_sd.
    - reflexivity.
    - unfold diffs_ok, vP, vHS. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd eval].
      + rewrite E183. unfold j. apply EVold. exact RV10.
      + rewrite E171. unfold p. apply EVold. exact RV18.
      + rewrite E182. unfold h. apply EVold. exact RV19.
    - unfold F_tw, vW, vP. unfold DEPOT, TABSZ in *.
      apply Forall_cons; [cbn [holds eval]; rewrite E170, !u64_lit by lia; lia|].
      apply Forall_cons; [cbn [holds]; rewrite E171, Hp; split; [lia|];
                          replace (1900440 + 4 * i) with ((475110 + i) * 4) by lia; rewrite Z.pow_2_r; apply Z_mod_mult|].
      apply Forall_cons; [cbn [holds eval]; rewrite E171, Hp, u64_lit by lia; lia|].
      apply Forall_cons; [cbn [holds eval]; rewrite E171, Hp, u64_lit by lia; lia|].
      apply Forall_nil.
    - exact H2. }
  rewrite ax_setS_setS in H3. exact H3.
Qed.

Variable L2s : axst.
Hypothesis RUN2 : ltac2:(tb__ "0|0|
S35S27S52A1S9aU64S25S3aZ7eb24S26S3aA1A3Sb5VE1s;A1A3S25S52S53VL2s;S126A2S26S52A1A3A3").

Lemma stage_T1 : ltac2:(tb__ "0|1|
S1S11fS1S11dS3cVok;S4dS3cS63VG0;A1M0VL2s;R1Vtp0;A5R2A4Frho3;S11dS3cVok;S4dS3cG0Sb5VE1s;A1R3Vtp0;A5R2A4F_;FQ;Frho2;").
Proof.
  intros rho2 Q HL2. apply triple1_triple. eapply (stage_run (JJ G0)); [apply JJ_ok | apply JJ_stable; lia | exact RUN2 | discriminate | reflexivity | apply Pos.leb_le; reflexivity |].
  intros L rho' [<-|[]] Hag. cbn [la_state]. apply HL2.
Qed.
Lemma estage_T1 : ltac2:(tb__ "0|1|
S1S11bOF_;S1S11cS3cS4dS3cS63VG0;A1M0VL2s;R1Vtp0;A5R2A3Frho3;S11cS3cS4dS3cG0Sb5VE1s;A1R3Vtp0;A5R2A3F_;FQ;Frho2;").
Proof.
  intros rho2 Q HL2. eapply (estage_run (JJ G0)); [apply JJ_stable; lia | exact RUN2 | discriminate | reflexivity | apply Pos.leb_le; reflexivity |].
  intros L rho' [<-|[]] Hag. cbn [la_state]. apply HL2.
Qed.

Let rL2 (i : nat) : sv := ltac2:(tb__ "0|0|
S114S2Vi;SfS51VL2s;A1A1S5Z0A1A4").
Definition VS_F : list positive := ltac2:(tb__ "0|0|
S25S3bPb0S25S3bPafS25S3bPb8S26S3bA1A3A3A3").
Hypothesis L2_X : ax_X L2s = [].
Hypothesis L2_nx : ltac2:(tb__ "0|0|
S35S3bS8S51VL2s;A1A1S95A3").
Hypothesis L2_vars : ltac2:(tb__ "0|0|
S35S28S140S124S7cA1S51VL2s;A1A2S2aA3").
Hypothesis L2_bvars : ltac2:(tb__ "0|0|
S35S28S13fS124S7cA1S56VL2s;A1A2S2aA3").
Hypothesis L2_rvars : ltac2:(tb__ "0|0|
S35S28S116S2S13fS124S7cA1A1S25S2VrL2;UaA1S25S2VrL2;UcA1S26S2A1A3A3A3S2aA3").
Hypothesis L2_F : ltac2:(tb__ "0|0|
S35S28S125S29S4S9eSa5A3S7S51VL2s;A1A1A2S2aA3").
Hypothesis L2_skel : ltac2:(tb__ "0|2|
S35S27S2bS2bS2S2A2S2A2M0A1S113S0G0S122S6S51VL2s;A1A1A4S113S0G0S122S29S0S25S0S138S25S0Sa3S26S0A1M1A3A3S29S0S137S29S0Sa4S25S0S97S96A1G1A3A3A3A3A4A3").
Hypothesis FB_swf : ltac2:(tb__ "0|0|
S35S28S20S51Sa6VL2s;A1A1A1S2aA3").
Hypothesis FB_sd : ltac2:(tb__ "0|4|
S35S2fS2bS27S2bS2S2A2M0A1M1S27S4A1M2A2M3A1S15aS51VL2s;A1S51Sa6VL2s;A1A1A2S31G3S2cG1G2S25G0S2cS2S2VrL2;UaA1S9Pb0A1A4S25G0S2cS2S2VrL2;UbA1Sd4A4S25G0S2cS2S2VrL2;UcA1S9Pb8A1A4S25G0S2cS2S2VrL2;U19A1S96A4S26G0A1A3A3A3A3Sd6A4A2A3").
Hypothesis L2_r11 : ltac2:(tb__ "0|0|
S35S2VrL2;UbA1S18S157S96S5Z7fffffffA1A3A3").
Hypothesis L2_r25 : ltac2:(tb__ "0|0|
S35S2VrL2;U19A1S18S157S96S5Z7fffffffA1A3A3").

Definition winDFP (G : DG) (rho : valuation) (o : sobj) : Prop := ltac2:(tb__ "0|3|
S4aQ40M0A1S36S3eS33S3aS3aS11Vrho;Vo;A2M1A3S49G0R1A2M2A2S3fG2S32S3aS3aG1A3A2A2SffVG;S49G0R2A2A2F_;Fa;").

Lemma winDFP_agree : ltac2:(tb__ "0|0|
S5cS3bS1S1S0SbR4R3R2A3S35S28S14R5R2A2S2aA3S68R7R5R3A3S68R8R5R4A3F_;F_;F_;Fo;Frho';Frho;Fn;FG;").
Proof. intros G n rho rho' o Hag Hwf H a Ha. rewrite (obj_range_agree n rho rho' o Hag Hwf) in Ha. exact (H a Ha). Qed.

Definition curOK (rho : valuation) : Prop := ltac2:(tb__ "0|1|
S39S35S3aS49Q40S3Vrho;PafA2A2M0Z0A3S36S3eZ1G0A2S3eG0S5dVG0;A1A2A2A2").

Lemma glue_F : ltac2:(tb__ "0|7|
S1S11bS4dS3cS63VG0;A1M0VL2s;R2Vtp0;R1A6S39S35S3aS49Q40M1S3R3PaaM2A2A2M3Z0A3S36S3eZ1G3A2S3eG3S5dVG0;A1A2A2A2S123S3cR4S97S96A1M4A3S37S1S1S36S4dS3cG0Sa6VL2s;A1R1Vtp0;R5A6S36S79R1A1S36S35S4aG1A1M5S3R1G2A2S3R6G2A2A3S36S35G5S3R1PabM6A2S3R6G6A2A3S123S3cR1G4A3A2A2A2A2Lrho';A2F_;F_;F_;Fw;Frho;").
Proof.
  intros rho w H Hw HRO. destruct w as [tr [ms md]].
  pose proof (SPA_facts segsA _ _ _ _ _ H) as HFall. pose proof (holds_inclb rho _ _ L2_F HFall) as HF2.
  assert (W31 : bv_unsigned (rw rho 170%positive) <= 2 ^ 31 - 1).
  { pose proof (proj1 (Forall_forall _ _) HF2 (SPUle vW (SLit (2^31 - 1))) ltac:(apply in_or_app; right; unfold F_tw; cbn; tauto)) as X.
    cbn [holds eval vW] in X. rewrite u64_lit in X by lia. exact X. }
  set (bs := [(176%positive, eval rho (rL2 10)); (175%positive, rw rho 170%positive); (184%positive, eval rho (rL2 12))]).
  set (rho' := rho_sets rho bs).
  assert (Hfst : map fst bs = VS_F) by reflexivity.
  assert (Hnd : List.NoDup (map fst bs)) by (rewrite Hfst; unfold VS_F; repeat constructor; cbn; lia).
  assert (E176 : rw rho' 176%positive = eval rho (rL2 10)) by (apply rho_sets_get; [exact Hnd | left; reflexivity]).
  assert (E175 : rw rho' 175%positive = rw rho 170%positive) by (apply rho_sets_get; [exact Hnd | right; left; reflexivity]).
  assert (E184 : rw rho' 184%positive = eval rho (rL2 12)) by (apply rho_sets_get; [exact Hnd | right; right; left; reflexivity]).
  destruct (rho_sets_rl_rm bs rho) as [Hrl' Hrm']. fold rho' in Hrl', Hrm'.
  assert (EVold : forall e, sv_vars_all (notin_vars VS_F) e = true -> eval rho' e = eval rho e).
  { intros e He. symmetry. apply (eval_agree_vars (notin_vars VS_F)); [| |exact He].
    - intros v Hv. unfold rho'. symmetry. apply rho_sets_other. rewrite Hfst. apply notin_vars_true. exact Hv.
    - intros l. rewrite Hrl'. reflexivity. }
  assert (E170 : rw rho' 170%positive = rw rho 170%positive) by (apply (EVold (SVar 170)); reflexivity).
  assert (E171 : rw rho' 171%positive = rw rho 171%positive) by (apply (EVold (SVar 171)); reflexivity).
  pose proof L2_rvars as RV. cbn [forallb] in RV. apply andb_prop in RV as [RV10 RV]. apply andb_prop in RV as [RV12 _].
  exists rho'. split; [|split; [unfold curOK; rewrite E175; exact Hw | split; [exact E170 | split; [exact E171|]]]].
  2:{ eapply (ro_win_vars segsA (notin_vars VS_F)); [| | |reflexivity|exact HRO].
      - intros v Hv. unfold rho'. symmetry. apply rho_sets_other. rewrite Hfst. apply notin_vars_true. exact Hv.
      - intros l. rewrite Hrl'. reflexivity.
      - intros a. rewrite Hrm'. reflexivity. }
  assert (H1 : SPA segsA (JJ G0) L2s rho' tp0 (tr, mkCfg ms md)).
  { unfold rho'. eapply (SPA_bindV segsA (JJ G0) NPRE); [exact L2_X | apply JJ_stable; lia | | rewrite Hfst; exact L2_vars | rewrite Hfst; exact L2_bvars | exact H].
    rewrite Hfst. unfold VS_F, NPRE. intros v Hv. cbn in Hv. lia. }
  assert (AND31 : eval rho' (SAlu ALU_AND vW (SLit 2147483647)) = rw rho 170%positive).
  { apply bv_eq. cbn [eval vW]. rewrite and_val, E170, u64_lit by lia. apply land_mask31. pose proof (urange (rw rho 170%positive)). lia. }
  assert (H2 : SPA segsA (JJ G0) (ax_setS L2s (ax_S (mkFindB L2s))) rho' tp0 (tr, mkCfg ms md)).
  { eapply (SPA_restate segsA (JJ G0) rho' L2s (ax_S (mkFindB L2s)) tp0 _ _ _ FB_swf FB_sd).
    - cbn. symmetry. exact L2_nx.
    - unfold diffs_ok, vS, vW. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd eval].
      + rewrite E176. apply EVold. exact RV10.
      + rewrite L2_r11, E175. exact AND31.
      + rewrite E184. apply EVold. exact RV12.
      + rewrite L2_r25, E170. exact AND31.
    - unfold F_S, vS. apply Forall_cons; [|apply Forall_nil]. cbn [holds eval]. rewrite E175, u64_lit by lia. exact W31.
    - exact H1. }
  exact H2.
Qed.

Lemma fb_objs_ranges : ltac2:(tb__ "0|2|
S1S1dS2bS27S12cA1S143A2S27S0A1S1fS3cR4R3R2A4S0S117S0R1R3A3S117S0R2S6R6A1A3F_;Fo;S35S27S2bS2bS2S2A2S2A2M0A1S113S0G0S122R3A4S113S0G0S122S29S0S25S0S138S25S0Sa3S26S0A1M1A3A3S29S0S137S29S0Sa4S25S0S97S96A1G1A3A3A3A3A4A3S112S4S1aR7A1S29S4S9eSa5A3A3S6dR8A1S3aS3aS3eS10cR2A2S3eR2Valloc_ceiling;A2S3eR4R3A2S112S0S0S19S11RfR1A2S2cS3aS3aR6R5A4A2Lo';RbA3F_;F_;F_;Fhi;Flo;F_;F_;F_;F_;F_;Fobjs;Fw;FS;Frho;").
Proof.
  intros rho S w objs Hsm Ho Hsk HF HT lo hi Hr1 Hr2 Hle.
  apply Forall_app in HF as [HFD HFt].
  assert (HP : bv_unsigned (rw rho 171%positive) <= DEPOT + 4 * 2 ^ 20 - 4).
  { pose proof (proj1 (Forall_forall _ _) HFt (SPUle vP (SLit (DEPOT + 4 * 2^20 - 4))) ltac:(unfold F_tw; cbn; tauto)) as X.
    cbn [holds eval vP] in X. unfold DEPOT in *. rewrite u64_lit in X by lia. exact X. }
  destruct (exists_last (l:=objs)) as (pre & lst & ->).
  { intros E. subst. cbn in Hsk. discriminate. }
  rewrite !map_app in Hsk. cbn [map app] in Hsk.
  change (map skel pre ++ [skel lst] = ([skel stack_win; skel O_trD; skel O_got; skel O_rtc; skel O_flag; skel O_pg; skel O_die; skel O_dpm; skel O_mlim]) ++ [skel (O_tw vW)]) in Hsk.
  apply app_inj_tail in Hsk as [Hpre Hl].
  apply Forall_app. split.
  - eapply (entry_objs_ranges rho S w pre Hsm); [intros o Hoo; apply Ho; apply in_or_app; left; exact Hoo | exact Hpre | exact HFD | exact HT | unfold NIDS, STORE in *; lia | exact Hr2 | exact Hle].
  - constructor; [|constructor].
    rewrite (obj_range_skel rho lst (O_tw vW) Hl). unfold O_tw, carved, ranges_disjoint. rewrite obj_range_mk by lia. cbn [fst snd eval vP].
    unfold DEPOT, NIDS in *. lia.
Qed.

Lemma objs_ranges_ext_mm : ltac2:(tb__ "0|2|
S1S147S27S0A1M0G0G0S3aS3aS112S0S1eS3cR7R6A3R5A3S0S117S0R1R6A3S117S0R2R8A3F_;Fo;S35S27S2bS2bS2S2A2S2A2M1A1S113S0G1S122R6A4S113S0G1S122S29S0S29S0S25S0S138S25S0Sa3S26S0A1A3A3S29S0S137Sa4A3A3R5A3A4A3S112S4S1aRaA1S9eA3S6dRbA1S3eSf9R7A2S3eR7Valloc_ceiling;A2S3eR9R8A2S112S0S0S19S11R10R1A2S2cS3aS3aRbRaA4A2Le;RbA3S112S0S0S19S11R11R1A2S2cS3aS3aRcRbA4A2Lo';RdA3F_;F_;F_;F_;F_;F_;F_;F_;F_;Fhi;Flo;Fextra;Fobjs;Fall;Fms;Frho;").
Proof.
  intros rho ms all objs extra lo hi Hsm Ho Hsk HF HT Hr1 Hr2 Hle Hex.
  rewrite map_app in Hsk. cbn [map app] in Hsk.
  destruct objs as [|o1 [|o2 [|o3 [|o4 [|o5 [|o6 [|o7 [|o8 [|o9 rest]]]]]]]]]; cbn [map] in Hsk; try discriminate Hsk.
  pose proof (f_equal (firstn 9) Hsk : map skel [o1; o2; o3; o4; o5; o6; o7; o8; o9] = map skel ([stack_win; O_trD] ++ A_globals ++ RT_D)) as Hpre.
  pose proof (f_equal (skipn 9) Hsk : map skel rest = map skel extra) as Erest.
  assert (Hsev : Forall (fun o' => ranges_disjoint (obj_range rho o') (lo, hi)) [o1; o2; o3; o4; o5; o6; o7; o8; o9]).
  { eapply (entry_objs_ranges_mm rho ms all [o1; o2; o3; o4; o5; o6; o7; o8; o9] Hsm); [| exact Hpre | exact HF | exact HT | exact Hr1 | exact Hr2 | exact Hle].
    intros o Hoo. apply Ho. cbn [In] in Hoo. cbn [In app]. tauto. }
  pose proof (Forall_ranges_skel rho (fun r => ranges_disjoint r (lo, hi)) _ _ Erest Hex) as HR.
  change (o1 :: o2 :: o3 :: o4 :: o5 :: o6 :: o7 :: o8 :: o9 :: rest) with ([o1; o2; o3; o4; o5; o6; o7; o8; o9] ++ rest).
  apply Forall_app. split; [exact Hsev | exact HR].
Qed.

Lemma objs_ranges_ext : ltac2:(tb__ "0|2|
S1S1dS2bS27S12cA1S143A2S27S0A1M0G0S3aS3aS1fS3cR7R6R5A4S0S117S0R1R6A3S117S0R2S6R9A1A3F_;Fo;S35S27S2bS2bS2S2A2S2A2M1A1S113S0G1S122R6A4S113S0G1S122S29S0S29S0S25S0S138S25S0Sa3S26S0A1A3A3S29S0S137Sa4A3A3R5A3A4A3S112S4S1aRaA1S9eA3S6dRbA1S3eSf9R7A2S3eR7Valloc_ceiling;A2S3eR9R8A2S112S0S0S19S11R10R1A2S2cS3aS3aRbRaA4A2Le;RbA3S112S0S0S19S11R11R1A2S2cS3aS3aRcRbA4A2Lo';RdA3F_;F_;F_;F_;F_;F_;F_;F_;F_;Fhi;Flo;Fextra;Fobjs;Fw;FS;Frho;").
Proof.
  intros rho S w objs extra lo hi Hsm. exact (objs_ranges_ext_mm rho _ _ objs extra lo hi (smatch_objs_hold rho S w Hsm)).
Qed.

Definition VS_NZ : list positive := ltac2:(tb__ "0|0|
S25S3bPacS25S3bPadS25S3bPaeS26S3bA1A3A3A3").
Let SB : sstate := ax_S (mkFindB L2s).
Let S_NZb : sstate := ltac2:(tb__ "0|0|
S13ScVSB;A1SfVSB;A1S16VSB;A1S15VSB;A1S17VSB;A1S29S0S6VSB;A1S25S0SafS25S0SadS25S0SaeS26S0A1A3A3A3A3S7VSB;A1S95SaVSB;A1A9").
Hypothesis FB_vars : ltac2:(tb__ "0|0|
S35S28S140S124S77A1VSB;A2S2aA3").
Hypothesis FB_bvars : ltac2:(tb__ "0|0|
S35S28S13fS124S77A1S56VL2s;A1A2S2aA3").
Hypothesis NZb_swf : swf S_NZb = true.
Hypothesis NZ_fb : ltac2:(tb__ "0|0|
S35S28S116S4S10S95A1S29S4S7VSB;A1Sd5A3A3S2aA3").

Lemma glue_NZ : ltac2:(tb__ "0|7|
S1S11bS4dS3cS63VG0;A1M0Sa6VL2s;A1R2Vtp0;R1A6S123S3cR3S97S96A1M1A3S36S3eZ1S49Q40M2S3R4PafM3A2A2M4A2S3eG4S5dVG0;A1A2A2S37S1S1S36S4dS3cG0Sc3VL2s;A1R1Vtp0;R5A6S36S3bS35S28S124S77R1A2S2aA3S35S4aG2A1S3R3R2A2S3R8R2A2A3F_;Fi;S36S36S3eZ0S49G2S3R1PaeA2A2M5A2S3fG5S49G2S3R6G3A2A2A2A2S36S112S0S123S3cR1A2S25S0G1S25S0SafS25S0SadS25S0SaeS26S0A1A3A3A3A3M6A3S112S0S68VG0;R1A2G6A3A2A2A2A2Lrho';A2F_;F_;F_;Fw;Frho;").
Proof.
  intros rho w H HRO Hs. destruct w as [tr [ms md]].
  pose proof H as [HsmA [HREL [HK [[HM HV] _]]]].
  pose proof (SPA_facts segsA _ _ _ _ _ H) as HFall.
  assert (HF2 : Forall (holds rho) (F_D ++ F_tw)).
  { eapply holds_inclb; [exact L2_F|]. unfold mkFindB, upd in HFall. cbn [ax_S ax_setS ss_facts] in HFall. apply Forall_app in HFall as [X _]. exact X. }
  set (s0 := bv_unsigned (rw rho 175%positive)) in *.
  pose proof (dm_N _ _ HM) as [HN _].
  set (j := s0 / 65536).
  assert (Hj : 0 <= j < MAP1N) by (unfold j, MAP1N; split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  pose proof (dm_map1 _ _ HM j Hj) as Hslot.
  set (blk := nth (Z.to_nat j) (dNB G0) 0) in Hslot.
  assert (Hin : In blk (dNB G0)).
  { unfold blk. apply nth_In. pose proof (dm_map1_len _ _ HM) as ML. unfold nblk in ML.
    destruct (Z.eqb_spec (dN G0) 0); [lia|]. assert (s0 / 65536 <= dN G0 / 65536) by (apply Z.div_le_mono; lia). unfold j. lia. }
  destruct (dm_nb _ _ HM blk Hin) as (Bal & Blo & Bhi & Bpres).
  pose proof (nb_top _ _ _ _ _ _ _ HK HV Hin) as BhiT.
  destruct (dm_link _ _ HM s0 ltac:(lia)) as (h & l & Hh & Hl & Hls).
  assert (Hna : SegD_wf.node_addr G0 s0 = blk + 16 * (s0 mod 65536)) by reflexivity.
  rewrite Hna in Hh, Hl.
  pose proof (Z.mod_pos_bound s0 65536 ltac:(lia)) as MB.
  set (bs := [(172%positive, Z_to_bv 64 blk); (173%positive, Z_to_bv 64 h); (174%positive, Z_to_bv 64 l)]).
  set (rho' := rho_sets rho bs).
  assert (Hfst : map fst bs = VS_NZ) by reflexivity.
  assert (Hnd : List.NoDup (map fst bs)) by (rewrite Hfst; unfold VS_NZ; repeat constructor; cbn; lia).
  assert (E172 : rw rho' 172%positive = Z_to_bv 64 blk) by (apply rho_sets_get; [exact Hnd | left; reflexivity]).
  assert (E173 : rw rho' 173%positive = Z_to_bv 64 h) by (apply rho_sets_get; [exact Hnd | right; left; reflexivity]).
  assert (E174 : rw rho' 174%positive = Z_to_bv 64 l) by (apply rho_sets_get; [exact Hnd | right; right; left; reflexivity]).
  destruct (rho_sets_rl_rm bs rho) as [Hrl' Hrm']. fold rho' in Hrl', Hrm'.
  assert (Hother : forall i, notin_vars VS_NZ i = true -> rw rho' i = rw rho i).
  { intros i Hi. unfold rho'. apply rho_sets_other. rewrite Hfst. apply notin_vars_true. exact Hi. }
  assert (E175 : rw rho' 175%positive = rw rho 175%positive) by (apply Hother; reflexivity).
  assert (E171 : rw rho' 171%positive = rw rho 171%positive) by (apply Hother; reflexivity).
  pose proof (urange (rw rho 175%positive)) as R175.
  assert (Hcell_h : cell_ok (view segsA (rm rho')) (mkACell (blk + 16 * (s0 mod 65536) + 0) 8 h)) by (rewrite Hrm', Z.add_0_r; exact Hh).
  assert (Hcell_l : cell_ok (view segsA (rm rho')) (mkACell (blk + 16 * (s0 mod 65536) + 8) 4 l)) by (rewrite Hrm'; exact Hl).
  assert (Hcell_b : cell_ok (view segsA (rm rho')) (mkACell (MAP1 + 8 * j + 0) 8 blk)) by (rewrite Hrm', Z.add_0_r; exact Hslot).
  assert (SA : bv_unsigned (eval rho' slot_addr) = MAP1 + 8 * j).
  { rewrite slot_addr_val by (rewrite E175; lia). rewrite E175. reflexivity. }
  assert (NA : bv_unsigned (eval rho' node_addr) = blk + 16 * (s0 mod 65536)).
  { rewrite node_addr_val.
    - rewrite E172, E175, u64_lit by (unfold IMG_HI, NBSZ in Blo, Bhi; lia). reflexivity.
    - rewrite E172, u64_lit by (unfold IMG_HI, NBSZ in Blo, Bhi; lia). exact Bhi. }
  exists rho'.
  assert (CIVb : cells_in_view rho' (rd_of segsA (rm rho')) (MAP1 + 8 * j) [(0, 8%nat, vB)]).
  { unfold cells_in_view. constructor; [|constructor]. intros jj Hjj.
    refine (civ_cell rho' (rm rho') (MAP1 + 8 * j) 0 8 blk vB Hcell_b _ _ _ jj Hjj); [cbn [eval]; exact E172 | unfold MAP1; lia | unfold MAP1, MAP1N in *; lia]. }
  assert (CIVh : cells_in_view rho' (rd_of segsA (rm rho')) (blk + 16 * (s0 mod 65536)) [(0, 8%nat, vH)]).
  { unfold cells_in_view. constructor; [|constructor]. intros jj Hjj.
    refine (civ_cell rho' (rm rho') _ 0 8 h vH Hcell_h _ _ _ jj Hjj); [cbn [eval]; exact E173 | unfold IMG_HI in *; lia | unfold NBSZ in *; lia]. }
  assert (CIVl : cells_in_view rho' (rd_of segsA (rm rho')) (blk + 16 * (s0 mod 65536)) [(8, 4%nat, vL)]).
  { unfold cells_in_view. constructor; [|constructor]. intros jj Hjj.
    refine (civ_cell rho' (rm rho') _ 8 4 l vL Hcell_l _ _ _ jj Hjj); [cbn [eval]; exact E174 | unfold IMG_HI in *; lia | unfold NBSZ in *; lia]. }
  assert (HP : DEPOT <= bv_unsigned (rw rho' 171%positive) <= DEPOT + 4 * 2 ^ 20 - 4).
  { rewrite E171. apply Forall_app in HF2 as [_ HFt].
    pose proof (proj1 (Forall_forall _ _) HFt (SPUle vP (SLit (DEPOT + 4 * 2^20 - 4))) ltac:(unfold F_tw; cbn; tauto)) as X1.
    pose proof (proj1 (Forall_forall _ _) HFt (SPUle (SLit DEPOT) vP) ltac:(unfold F_tw; cbn; tauto)) as X2.
    cbn [holds eval vP] in X1, X2. unfold DEPOT in *. rewrite u64_lit in X1 by lia. rewrite u64_lit in X2 by lia. lia. }
  split; [|split; [exact Hother | split; [rewrite E174, u64_lit by lia; lia|split]]].
  2:{ constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]].
      - eapply (ro_win_vars segsA (notin_vars VS_NZ)); [intros v Hv; symmetry; apply Hother; exact Hv | intros l0; rewrite Hrl'; reflexivity | intros a; rewrite Hrm'; reflexivity | reflexivity | exact HRO].
      - exists slot_addr, 0, 8%nat, vB. rewrite SA. split; [reflexivity|]. unfold MAP1, MAP1N in *. repeat (split; [lia|]). exact CIVb.
      - exists node_addr, 0, 8%nat, vH. rewrite NA. split; [reflexivity|]. unfold IMG_HI, NBSZ in *. repeat (split; [lia|]). exact CIVh.
      - exists node_addr, 8, 4%nat, vL. rewrite NA. split; [reflexivity|]. unfold IMG_HI, NBSZ in *. repeat (split; [lia|]). exact CIVl. }
  2:{ unfold winDFP, O_tw, O_slot, O_nh, O_nl, carved.
      constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]]; intros a; rewrite obj_range_mk by lia; cbn [fst snd eval vP]; rewrite ?SA, ?NA; intros Ha.
      - left. left. unfold DEPOT, MAP1, MAP1N in *. lia.
      - left. left. unfold DEPOT, MAP1, MAP1N in *. lia.
      - right. left. exists blk. split; [exact Hin | unfold NBSZ in *; lia].
      - right. left. exists blk. split; [exact Hin | unfold NBSZ in *; lia]. }

  assert (H1 : SPA segsA (JJ G0) (mkFindB L2s) rho' tp0 (tr, mkCfg ms md)).
  { unfold rho'. eapply (SPA_bindV segsA (JJ G0) NPRE); [cbn; exact L2_X | apply JJ_stable; lia | | rewrite Hfst; exact FB_vars | rewrite Hfst; cbn [ax_base mkFindB upd ax_setS]; exact FB_bvars | exact H].
    rewrite Hfst. unfold VS_NZ, NPRE. intros v Hv. cbn in Hv. lia. }
  pose proof (SPA_facts segsA _ _ _ _ _ H1) as HFall'.
  assert (HF2' : Forall (holds rho') (F_D ++ F_tw)).
  { eapply holds_inclb; [exact L2_F|]. unfold mkFindB, upd in HFall'. cbn [ax_S ax_setS ss_facts] in HFall'. apply Forall_app in HFall' as [X _]. exact X. }

  assert (H2 : SPA segsA (JJ G0) (ax_setS (mkFindB L2s) S_NZb) rho' tp0 (tr, mkCfg ms md)).
  { unfold S_NZb.
    apply (SPA_carve_list segsA (JJ G0) rho' (mkFindB L2s) tp0 _
             [(slot_addr, 0, 8, [(0, 8%nat, vB)]); (node_addr, 0, 8, [(0, 8%nat, vH)]); (node_addr, 8, 12, [(8, 4%nat, vL)])] NXD H1 NZb_swf ltac:(apply Pos.le_refl)).
    - pose proof alloc_ceiling_valD as ACV. unfold MAP1, MAP1N, IMG_HI, NBSZ in *.
      repeat apply Forall_cons; try apply Forall_nil; rewrite ?SA, ?NA.
      + repeat (split; [lia|]). split; [unfold cells_inside; repeat constructor; cbn; lia|]. split; [|split; [exact CIVb | unfold xwords_clear; cbn; rewrite L2_X; intros rr y jj []]].
        intros off Hoff. split; [apply wok_of_imageA; lia | apply rd_of_imageA; lia].
      + repeat (split; [lia|]). split; [unfold cells_inside; repeat constructor; cbn; lia|]. split; [|split; [exact CIVh | unfold xwords_clear; cbn; rewrite L2_X; intros rr y jj []]].
        intros off Hoff. apply (cell_wok_rd (rm rho') (blk + 16 * (s0 mod 65536) + 0) 8 h); [exact Hcell_h | lia | lia | lia].
      + repeat (split; [lia|]). split; [unfold cells_inside; repeat constructor; cbn; lia|]. split; [|split; [exact CIVl | unfold xwords_clear; cbn; rewrite L2_X; intros rr y jj []]].
        intros off Hoff. apply (cell_wok_rd (rm rho') (blk + 16 * (s0 mod 65536) + 8) 4 l); [exact Hcell_l | lia | lia | lia].
    -
      pose proof (proj1 H1) as Hsm1. unfold smatchA, virt in Hsm1. cbn [fst snd cfg_ms cfg_model w_tr w_cfg] in Hsm1. apply proj1 in Hsm1.
      assert (SK : map skel (ss_objs SB) = map skel ([stack_win; O_trD] ++ A_globals ++ RT_D ++ [O_tw vW])).
      { unfold SB, mkFindB, upd. cbn [ax_S ax_setS ss_objs]. rewrite app_nil_r. exact L2_skel. }
      pose proof alloc_ceiling_valD as ACV. unfold MAP1, MAP1N, IMG_HI, NBSZ in *.
      repeat apply Forall_cons; try apply Forall_nil; cbn [carve_obj]; unfold carved; rewrite obj_range_mk by lia; rewrite ?SA, ?NA;
        (eapply (fb_objs_ranges rho' SB _ _ Hsm1 ltac:(intros o Ho; exact Ho) SK HF2' ltac:(first [assumption | eapply TOPr_of_REL; eassumption | eapply TOPr_of_JJ; eassumption])); unfold NIDS; lia).
    -
      cbn [map carve_obj pairwise_disjoint]. unfold carved.
      pose proof alloc_ceiling_valD as ACV. unfold MAP1, MAP1N, IMG_HI, NBSZ in *.
      split; [|split; [|split; [constructor|exact I]]].
      + apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold ranges_disjoint; rewrite !obj_range_mk by lia; cbn [fst snd]; rewrite SA, NA; lia.
      + apply Forall_cons; [|apply Forall_nil]. unfold ranges_disjoint; rewrite !obj_range_mk by lia; cbn [fst snd]; rewrite NA; lia. }

  assert (H3 : SPA segsA (JJ G0) (ax_with_facts (ax_setS (mkFindB L2s) S_NZb) (ss_facts SB ++ F_NZ)) rho' tp0 (tr, mkCfg ms md)).
  { apply SPA_refacts; [exact H2 | exact NZ_fb |]. cbn [ax_S ax_setS ss_facts]. intros HFB. apply Forall_app. split; [exact HFB|].
    unfold F_NZ, vS, vB, vL. pose proof alloc_ceiling_valD as ACV. unfold IMG_HI, NBSZ, PG in *.
    apply Forall_cons. { cbn [holds eval branch_taken]. unfold bv_eqb. rewrite E175, u64_lit by lia. intros X. apply Z.eqb_eq in X. lia. }
    apply Forall_cons. { cbn [holds eval branch_taken]. unfold bv_eqb. rewrite E172, !u64_lit by lia. intros X. apply Z.eqb_eq in X. lia. }
    apply Forall_cons. { cbn [holds]. split; [lia|]. rewrite E172, u64_lit by lia. change (2 ^ 4) with 16. apply Z.mod_divide; [lia|]. apply Z.mod_divide in Bal; [|lia]. destruct Bal as [q Hq]. exists (q * 256). lia. }
    apply Forall_cons. { cbn [holds eval]. rewrite E172, !u64_lit by lia. lia. }
    apply Forall_cons. { cbn [holds eval]. rewrite E172, !u64_lit by lia. lia. }
    apply Forall_cons. { cbn [holds eval]. rewrite E174, !u64_lit by lia. lia. }
    apply Forall_nil. }
  unfold ax_with_facts in H3. rewrite ax_setS_setS in H3. exact H3.
Qed.

Variables CONTs FOUNDs : axst.
Variables sC sF : wsub.
Hypothesis RUNNZ : ltac2:(tb__ "0|0|
S35S27S52A1S9aU64S25S3aZ7eb24S25S3aSb2S26S3aA1A3A3Sc3VL2s;A1A3S25S52S53VCONTs;S126A2S25S52S53VFOUNDs;S126A2S26S52A1A3A3A3").
Hypothesis CONT_objs : ltac2:(tb__ "0|1|
S35S27S0A1S6S51VCONTs;A1A1M0S29S0S115S0S153S2dS0G0A2U3A2G0A3S25S0SafS25S0SadS25S0SaeS26S0A1A3A3A3A3A3").
Hypothesis ENT_C : ltac2:(tb__ "0|0|
S35S28S54Se4VCONTs;A1Sa6VL2s;A1VsC;A3S2aA3").
Hypothesis SID_C : ltac2:(tb__ "0|0|
S35S28S13aVsC;S98A2S2aA3").
Hypothesis SC175 : wsub_get sC 175 = vL.
Hypothesis SC_tw : ltac2:(tb__ "0|0|
S35S28S141S3bS1cS13bVsC;R1A2S9R1A1A2Li;S97S96A1A2S2aA3").
Hypothesis FOUND_objs : ltac2:(tb__ "0|1|
S35S27S0A1S6S51VFOUNDs;A1A1M0S29S0S115S0S153S2dS0G0A2U4A2G0A3S25S0S97S96A1S25S0SafS25S0SadS25S0SaeS26S0A1A3A3A3A3A3A3").
Hypothesis ENT_F : ltac2:(tb__ "0|0|
S35S28S54Se2VFOUNDs;U4A2Sc7Vsz;A1VsF;A3S2aA3").
Hypothesis SID_F : ltac2:(tb__ "0|0|
S35S28S13aVsF;S98A2S2aA3").

Lemma NZ_owf : ltac2:(tb__ "0|0|
S35S28S116S0S14S95A1S25S0S97S96A1S25S0SafS25S0SadS25S0SaeS26S0A1A3A3A3A3A3S2aA3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition pend_view (PD : pend) : Prop := ltac2:(tb__ "0|2|
S1S1S27S4aQ40A1M0A1S12aS3bS35G0S3R4R1A2S3R5R1A2A3Fi;S3bS35S27S4aQ8A1M1A1S1bR5R1A2S1bR6R1A2A3Fl;S3aS35S2fG1A1S150S3cSdR6A1R1A3S150S3cSdR7A1R1A3A3Fz;VPD;R7R5R4A3VPD;R7R6R5A3F_;F_;F_;F_;Fmd;Ftp;Frho';Frho;").
Lemma PD0_view : pend_view PD0. Proof. unfold pend_view, PD0. intros. exact I. Qed.

Lemma JJ_dissolve : ltac2:(tb__ "0|6|
S5cS5cS75S55S1S27S4aQ40M0A1M1A1S27S12cA1M2S147S12aS27S0A1M3G3S87R9A1S4dS3cS6aRcRbRaA3R9R8R7S2cG2S143R6S144R5R4A2A4A6S35G3S6S51RaA1A1S29S0R4R3A3A3S112S0S123S3cRaA2R4A3S112S0S0G1S36S3eS33S3aS3aS11RdR2A2M4A3S49G0R1A2M5A2S3fG5S32S3aS3aG4A3A2A2SffR12S49G0R2A2A2F_;Fa;Lo;R5A3S13eRcR6S170R8RbR9A3A3S1S36S4dS3cS6aR11R10RfA3S57ReS129S51ReA1R8A2A2R1RcS2cG2S143RbS144RaR9A2A4A6S36S3aS35S2fS4aQ8A1A1S150S3cSdR2A1R1A3S150S3cSdReA1R1A3A3Fz;S3bS35G1S3R2R1A2S3ReR1A2A3Fi;A2A2Trho';F_;F_;F_;F_;F_;FR;Fobjs;Fmd;Fms;Ftr;Ftp;Frho;FA;FPD;FGd;FGk;").
Proof.
  intros Gk Gd PD A rho tp tr ms md objs R HPV H Ho HR HD rho'.
  pose proof (proj1 H) as HsmA. pose proof (proj1 HsmA) as Hsm. unfold virt in Hsm. cbn [fst snd cfg_ms cfg_model w_tr w_cfg] in Hsm.
  destruct (dissolve_ro_view segsA rho (ax_S A) tr (vms md tp ms) (vmd md) objs R Hsm Ho HR) as [HV Hrm].
  split; [|split; [exact HV | intros i; reflexivity]].
  apply (SPA_unobj segsA (JJ2 Gk Gd PD) rho A objs R tp tr ms md Ho H).
  intros [HRel [HK [HDI HP]]]. split; [|split; [|split]].
  - destruct HRel as (A1 & A2 & A3). split; [exact A1|split].
    + intros a Ha. fold rho'. rewrite Hrm; [apply A2; exact Ha|]. intros (o & HoR & Hrng). apply Ha. exact (proj1 (Forall_forall _ _) HD o HoR a Hrng).
    + intros z Hz. fold rho'. rewrite HV. apply A3. exact Hz.
  - eapply (kd_view segsA K NPRE HKD Gk rho rho'); [intros i; reflexivity | intros l; reflexivity | intros z _; apply HV | exact HK].
  - destruct HDI as [HM HVM]. split; [|exact HVM]. eapply depot_mem_frame; [|exact HM]. intros a _. apply HV.
  - apply (HPV rho rho' tp md); [intros i; reflexivity | intros l; reflexivity | exact HV | exact HP].
Qed.

Lemma cont_step : ltac2:(tb__ "0|8|
S1S1S11bS4dS3cS63VG0;A1M0VCONTs;R2Vtp0;R1A6SbS95R4R3A3S112S0S123S3cR5A2S25S0S97S96A1M1S25S0SafS25S0SadS25S0SaeS26S0A1A3A3A3A3M2A3S112S0S68VG0;R6A2G2A3S36S3eZ0S49Q40M3S3R7PaeM4A2A2M5A2S3fG5S49G3S3R7PafM6A2A2A2A2S3eS49G3S3R8G6A2A2S5dVG0;A1A2S37S1S1S36S4dS3cG0Sa6VL2s;A1R1Vtp0;R8A6S36S79R1A1S36S35S3aS49G3S3R1G6A2A2S49G3S3RaG4A2A2A3S36S123S3cR1G1A3S35S4aG3A1S3R1PaaM7A2S3RaG7A2A3A2A2A2A2Lrho';A2F_;F_;F_;F_;F_;F_;Fw;FrhoL;FrhoC;").
Proof.
  intros rhoC rhoL w H Hag HRO HD Hl Hs. destruct w as [tr [ms md]].
  pose proof NZ_owf as OW. cbn [forallb] in OW. apply andb_prop in OW as [OW1 OW]. apply andb_prop in OW as [OW2 OW]. apply andb_prop in OW as [OW3 OW]. apply andb_prop in OW as [OW4 _].
  assert (HRO' : Forall (ro_win segsA rhoL) [O_tw vW; O_slot; O_nh; O_nl]).
  { inversion HRO as [|? ? R1 X1]; subst. inversion X1 as [|? ? R2 X2]; subst. inversion X2 as [|? ? R3 X3]; subst. inversion X3 as [|? ? R4 _]; subst.
    repeat (apply Forall_cons; [eapply ro_win_agree; eassumption|]); apply Forall_nil. }
  assert (HD' : Forall (winDFP G0 rhoL) [O_tw vW; O_slot; O_nh; O_nl]).
  { inversion HD as [|? ? R1 X1]; subst. inversion X1 as [|? ? R2 X2]; subst. inversion X2 as [|? ? R3 X3]; subst. inversion X3 as [|? ? R4 _]; subst.
    repeat (apply Forall_cons; [eapply winDFP_agree; eassumption|]); apply Forall_nil. }
  destruct (JJ_dissolve G0 G0 PD0 CONTs rhoL tp0 tr ms md _ [O_slot; O_nh; O_nl] PD0_view H CONT_objs ltac:(inversion HRO'; assumption) ltac:(inversion HD'; assumption)) as (H1 & HV & Hrw).
  set (rho' := rho_absorb rhoL [O_slot; O_nh; O_nl] (vms md tp0 ms)) in *.
  assert (H2 : SPA segsA (JJ G0) (mkFindB L2s) (rho_sub rho' sC) tp0 (tr, mkCfg ms md)).
  { apply (SPA_entails segsA (JJ G0) NPRE (mkCONT CONTs) (mkFindB L2s) sC rho' tp0 _ ENT_C SID_C (JJ_stable G0 NPRE ltac:(lia))). exact H1. }
  exists (rho_sub rho' sC).
  destruct Hag as (Hagw & Hagl & Hagm).
  assert (E175 : rw (rho_sub rho' sC) 175%positive = rw rhoC 174%positive).
  { cbn [rho_sub rw]. rewrite SC175. cbn [eval vL]. rewrite Hrw. symmetry. apply Hagw. unfold NXD. lia. }
  pose proof SC_tw as SCv. unfold obj_vars_all, O_tw, carved, vP, vW in SCv. cbn -[sv_eqb wsub_get] in SCv.
  destruct (sv_eqb (wsub_get sC 171) (SVar 171)) eqn:SC171; [|discriminate]. destruct (sv_eqb (wsub_get sC 170) (SVar 170)) eqn:SC170; [|cbn in SCv; rewrite ?andb_false_r in SCv; discriminate].
  apply sv_eqb_sound in SC171. apply sv_eqb_sound in SC170.
  split; [exact H2|]. split; [|split; [|split]].
  - unfold curOK. rewrite E175. lia.
  - rewrite E175. reflexivity.
  - assert (RO1 : ro_win segsA rho' (O_tw vW)).
    { apply (ro_win_vars segsA (fun _ => true) rhoL rho'); [intros v _; symmetry; apply Hrw | intros l; reflexivity | apply view_eq_rd_of; exact HV | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | exact (Forall_inv HRO')]. }
    apply (ro_win_vars segsA (fun i => sv_eqb (wsub_get sC i) (SVar i)) rho' (rho_sub rho' sC)); [ | intros l; reflexivity | intros a; reflexivity | exact SC_tw | exact RO1].
    intros v Hv. apply sv_eqb_sound in Hv. cbn [rho_sub rw]. rewrite Hv. reflexivity.
  - cbn [rho_sub rw]. rewrite SC170. cbn [eval]. rewrite Hrw. symmetry. apply Hagw. unfold NXD. lia.
Qed.

Lemma found_exit : ltac2:(tb__ "0|1|
S1S1S11bS4dS3cS63VG0;A1VFOUNDs;R2Vtp0;R1A6SbS95R4R3A3S112S0S123S3cR5A2S25S0S97S96A1S25S0SafS25S0SadS25S0SaeS26S0A1A3A3A3A3M0A3S112S0S68VG0;R6A2G0A3S64R5A1F_;F_;F_;F_;Fw;FrhoL;FrhoC;").
Proof.
  intros rhoC rhoL w H Hag HRO HD. destruct w as [tr [ms md]].
  pose proof NZ_owf as OW. cbn [forallb] in OW. apply andb_prop in OW as [OW1 OW]. apply andb_prop in OW as [OW2 OW]. apply andb_prop in OW as [OW3 OW]. apply andb_prop in OW as [OW4 _].
  assert (HRO' : Forall (ro_win segsA rhoL) [O_tw vW; O_slot; O_nh; O_nl]).
  { inversion HRO as [|? ? R1 X1]; subst. inversion X1 as [|? ? R2 X2]; subst. inversion X2 as [|? ? R3 X3]; subst. inversion X3 as [|? ? R4 _]; subst.
    repeat (apply Forall_cons; [eapply ro_win_agree; eassumption|]); apply Forall_nil. }
  assert (HD' : Forall (winDFP G0 rhoL) [O_tw vW; O_slot; O_nh; O_nl]).
  { inversion HD as [|? ? R1 X1]; subst. inversion X1 as [|? ? R2 X2]; subst. inversion X2 as [|? ? R3 X3]; subst. inversion X3 as [|? ? R4 _]; subst.
    repeat (apply Forall_cons; [eapply winDFP_agree; eassumption|]); apply Forall_nil. }
  destruct (JJ_dissolve G0 G0 PD0 FOUNDs rhoL tp0 tr ms md _ [O_tw vW; O_slot; O_nh; O_nl] PD0_view H FOUND_objs HRO' HD') as (H1 & HV & Hrw).
  set (rho' := rho_absorb rhoL [O_tw vW; O_slot; O_nh; O_nl] (vms md tp0 ms)) in *.
  assert (H2 : SPA segsA (JJ G0) (PostD sz) (rho_sub rho' sF) tp0 (tr, mkCfg ms md)).
  { apply (SPA_entails segsA (JJ G0) NPRE (dropo FOUNDs 4) (PostD sz) sF rho' tp0 _ ENT_F SID_F (JJ_stable G0 NPRE ltac:(lia))). exact H1. }
  unfold QD. pose proof (proj2 H2) as HJ. cbn [w_tr w_cfg fst snd cfg_model] in HJ. destruct HJ as [[HA [Hrm Hvw]] [HK [HDI _]]].
  eapply (LQPA_intro segsA NPRE rho0 tp0 _ (PostD sz) (JLD segsA K G0) (rho_sub rho' sF) tp0 _ (JJ G0)); [left; reflexivity | exact H2 | exact HA |].
  intros _. exists G0. split; [exact HK|]. split; [exact HDI|]. split; [apply dpost_refl|]. split; [exact Hrm|]. split; [exact Hvw|].
  split; [intros l; symmetry; apply (proj2 HA) | exists []; reflexivity].
Qed.

Definition W0ok (rho : valuation) : Prop := ltac2:(tb__ "0|0|
S3eS49Q40S3Vrho;PaaA2A2S5dVG0;A1A2").
Definition InvF : assn := ltac2:(tb__ "0|0|
S11bS37S1S1S36S36S79R1A1S36S123S3cR1S97S96A1A3S6eR1A1A2A2S4dS3cS63VG0;A1Sa6VL2s;A1R1Vtp0;R2A6A2Lrho;A2Lw;").

Definition NZfam (rho : valuation) : assn := ltac2:(tb__ "0|3|
S11bS37S1S1S36S36S3bS35S28S124S77R1A2S2aA3S35S4aQ40M0A1S3R3R2A2S3Vrho;R2A2A3F_;Fi;S36S36S3eZ0S49G0S3R1PaeA2A2M1A2S3fG1S49G0S3Vrho;PafA2A2A2A2S36S112S0S123S3cR1A2S25S0S97S96A1S25S0SafS25S0SadS25S0SaeS26S0A1A3A3A3A3M2A3S112S0S68VG0;R1A2G2A3A2A2A2S4dS3cS63VG0;A1Sc3VL2s;A1R1Vtp0;R2A6A2Lrho';A2Lw;").

Lemma find_loop : ltac2:(tb__ "0|0|
S1S35S3aS49Q40S3R1PafA2A2Z0A3S123S3cR2S97S96A1A3S6eR3A1S11eS3cVok;S4dS3cS63VG0;A1Sa6VL2s;A1R4Vtp0;A5S64A4F_;F_;F_;Frho;S11dS3cVok;S89S64A4F_;").
Proof.
  intros HZ. apply triple_loop. unfold InvF at 1. apply triple1_ex. intros rho. apply triple1_pure. intros (Hc & Hro & Hw0).
  destruct Hc as [Hz | Hnz].
  - eapply triple1_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw | apply HZ; assumption].
  - eapply triple1_conseq with (P := NZfam rho).
    + intros w Hw. destruct (glue_NZ rho w Hw Hro Hnz) as (rho' & A & B & C & D & E). exists rho'. split; [|exact A]. split; [exact B|]. split; [exact C|]. split; assumption.
    + intros w Hw. exact Hw.
    + unfold NZfam. apply triple1_ex. intros rho'. apply triple1_pure. intros (Hoth & Hlt & HROs & HDs).
      assert (E175 : rw rho' 175%positive = rw rho 175%positive) by (apply Hoth; reflexivity).
      eapply (stage_run (JJ G0)); [apply JJ_ok | apply JJ_stable; lia | exact RUNNZ | discriminate | reflexivity | apply Pos.leb_le; reflexivity |].
      intros L rhoL [<-|[<-|[]]] Hag; cbn [la_state].
      *
        eapply triple_conseq; [| intros w Hw; exact Hw | apply triple_refl].
        intros w Hw. left. destruct (cont_step rho' rhoL w Hw Hag HROs HDs ltac:(rewrite E175; lia) ltac:(rewrite E175; lia)) as (rho2 & S2 & C2 & _ & R2 & W2).
        exists rho2. split; [split; [exact C2 | split; [exact R2 | unfold W0ok; rewrite W2, (Hoth 170%positive eq_refl); exact Hw0]] | exact S2].
      *
        eapply triple_conseq; [| intros w Hw; exact Hw | apply triple_refl].
        intros w Hw. right. exact (found_exit rho' rhoL w Hw Hag HROs HDs).
Qed.

Definition InvFe (a : nat) : world -> Prop := ltac2:(tb__ "0|0|
S11bS37S1S1S36S36S79R1A1S36S123S3cR1S97S96A1A3S36S6eR1A1S35S2eS42S49Q40S3R1PafA2A2A1Va;A3A2A2A2S4dS3cS63VG0;A1Sa6VL2s;A1R1Vtp0;R2A6A2Lrho;A2Lw;").

Lemma efind_loop : ltac2:(tb__ "0|0|
S1S35S3aS49Q40S3R1PafA2A2Z0A3S123S3cR2S97S96A1A3S6eR3A1S11cS3cS4dS3cS63VG0;A1Sa6VL2s;A1R4Vtp0;A5S64A3F_;F_;F_;Frho;S2eS11cS3cS8aR1A1S64A3Fa;F_;").
Proof.
  intros HZ. apply (etriple_loop (A := nat) (R := lt) Wf_nat.lt_wf InvFe QD). intros a.
  unfold InvFe at 1. apply etriple_ex. intros rho. apply etriple_pure. intros (Hc & Hro & Hw0 & Ha).
  destruct Hc as [Hz | Hnz].
  - eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw | apply HZ; assumption].
  - eapply etriple_conseq with (P := NZfam rho).
    + intros w Hw. destruct (glue_NZ rho w Hw Hro Hnz) as (rho' & A & B & C & D & E). exists rho'. split; [|exact A]. split; [exact B|]. split; [exact C|]. split; assumption.
    + intros w Hw. exact Hw.
    + unfold NZfam. apply etriple_ex. intros rho'. apply etriple_pure. intros (Hoth & Hlt & HROs & HDs).
      assert (E175 : rw rho' 175%positive = rw rho 175%positive) by (apply Hoth; reflexivity).
      eapply (estage_run (JJ G0)); [apply JJ_stable; lia | exact RUNNZ | discriminate | reflexivity | apply Pos.leb_le; reflexivity |].
      intros L rhoL [<-|[<-|[]]] Hag; cbn [la_state].
      * eapply etriple_conseq; [| intros w Hw; exact Hw | apply etriple_refl].
        intros w Hw. left. destruct (cont_step rho' rhoL w Hw Hag HROs HDs ltac:(rewrite E175; lia) ltac:(rewrite E175; lia)) as (rho2 & S2 & C2 & E2 & R2 & W2).
        exists (Z.to_nat (bv_unsigned (rw rho2 175%positive))). split; [rewrite <- Ha, E2; pose proof (urange (rw rho' 174%positive)); lia|].
        exists rho2. split; [split; [exact C2 | split; [exact R2 | split; [unfold W0ok; rewrite W2, (Hoth 170%positive eq_refl); exact Hw0 | reflexivity]]] | exact S2].
      * eapply etriple_conseq; [| intros w Hw; exact Hw | apply etriple_refl].
        intros w Hw. right. exact (found_exit rho' rhoL w Hw Hag HROs HDs).
Qed.

Definition VS_Z : list positive := [177]%positive.
Let S_Zb : sstate := ltac2:(tb__ "0|0|
S13ScVSB;A1SfVSB;A1S16VSB;A1S15VSB;A1S17VSB;A1S29S0S6VSB;A1S25S0S9dS9fA1S26S0A1A3A3S7VSB;A1S95SaVSB;A1A9").
Hypothesis FBz_vars : ltac2:(tb__ "0|0|
S35S28S140S124S7eA1VSB;A2S2aA3").
Hypothesis FBz_bvars : ltac2:(tb__ "0|0|
S35S28S13fS124S7eA1S56VL2s;A1A2S2aA3").
Hypothesis Zb_swf : swf S_Zb = true.
Hypothesis FZ_swf : ltac2:(tb__ "0|0|
S35S28S20S51SbdVL2s;A1A1A1S2aA3").
Hypothesis FZ_sd : ltac2:(tb__ "0|4|
S35S2fS2bS27S2bS2S2A2M0A1M1S27S4A1M2A2M3A1S15aVS_Zb;S51SbdVL2s;A1A1A2S31G3S2cG1G2S25G0S2cS2S2Sd4S5Z0A1A4S26G0A1A3Sa7A4A2A3").

Lemma glue_Z : ltac2:(tb__ "0|2|
S1S11bS4dS3cS63VG0;A1M0Sa6VL2s;A1R2Vtp0;R1A6S35S3aS49Q40M1S3R3PafA2A2Z0A3S6eR4A1S37S1S1S36S4dS3cG0SbdVL2s;A1R1Vtp0;R5A6S36S3bS35S28S124S7eR1A2S2aA3S35S4aG1A1S3R3R2A2S3R8R2A2A3F_;Fi;S36S35S3aS49G1S3R1Pb1A2A2S5dVG0;A1A3S36S68VG0;R1S97S96A1A3S68VG0;R1S9dS9fA1A3A2A2A2A2Lrho';A2F_;F_;F_;Fw;Frho;").
Proof.
  intros rho w H Hz Hw0. destruct w as [tr [ms md]].
  pose proof H as [HsmA [HREL [HK [[HM HV] _]]]].
  pose proof (SPA_facts segsA _ _ _ _ _ H) as HFall.
  assert (HF2 : Forall (holds rho) (F_D ++ F_tw)).
  { eapply holds_inclb; [exact L2_F|]. unfold mkFindB, upd in HFall. cbn [ax_S ax_setS ss_facts] in HFall. apply Forall_app in HFall as [X _]. exact X. }
  pose proof (dm_N _ _ HM) as [HN Hcell].
  destruct (kd_room segsA K NPRE HKD G0 rho tp0 _ _ HK (conj HM HV)) as [_ HDN].
  set (bs := [(177%positive, Z_to_bv 64 (dN G0))]).
  set (rho' := rho_sets rho bs).
  assert (Hfst : map fst bs = VS_Z) by reflexivity.
  assert (Hnd : List.NoDup (map fst bs)) by (rewrite Hfst; unfold VS_Z; repeat constructor; cbn; lia).
  assert (E177 : rw rho' 177%positive = Z_to_bv 64 (dN G0)) by (apply rho_sets_get; [exact Hnd | left; reflexivity]).
  destruct (rho_sets_rl_rm bs rho) as [Hrl' Hrm']. fold rho' in Hrl', Hrm'.
  assert (Hother : forall i, notin_vars VS_Z i = true -> rw rho' i = rw rho i).
  { intros i Hi. unfold rho'. apply rho_sets_other. rewrite Hfst. apply notin_vars_true. exact Hi. }
  assert (E175 : rw rho' 175%positive = rw rho 175%positive) by (apply Hother; reflexivity).
  assert (Hcell' : cell_ok (view segsA (rm rho')) (mkACell (NIDS + 0) 4 (dN G0))) by (rewrite Hrm', Z.add_0_r; exact Hcell).
  assert (CIVn : cells_in_view rho' (rd_of segsA (rm rho')) NIDS [(0, 4%nat, vN)]).
  { unfold cells_in_view. constructor; [|constructor]. intros jj Hjj.
    refine (civ_cell rho' (rm rho') NIDS 0 4 (dN G0) vN Hcell' _ _ _ jj Hjj); [cbn [eval]; exact E177 | unfold NIDS; lia | unfold NIDS; lia]. }
  assert (HP : DEPOT <= bv_unsigned (rw rho' 171%positive) <= DEPOT + 4 * 2 ^ 20 - 4).
  { rewrite (Hother 171%positive eq_refl). apply Forall_app in HF2 as [_ HFt].
    pose proof (proj1 (Forall_forall _ _) HFt (SPUle vP (SLit (DEPOT + 4 * 2^20 - 4))) ltac:(unfold F_tw; cbn; tauto)) as X1.
    pose proof (proj1 (Forall_forall _ _) HFt (SPUle (SLit DEPOT) vP) ltac:(unfold F_tw; cbn; tauto)) as X2.
    cbn [holds eval vP] in X1, X2. unfold DEPOT in *. rewrite u64_lit in X1 by lia. rewrite u64_lit in X2 by lia. lia. }
  exists rho'. split; [|split; [exact Hother | split; [rewrite E177, u64_lit by lia; reflexivity | split]]].
  2:{ unfold winDFP, O_tw, carved. intros a. rewrite obj_range_mk by lia. cbn [fst snd eval vP]. intros Ha. left. left. unfold DEPOT, MAP1, MAP1N in *. lia. }
  2:{ unfold winDFP, O_nid, carved, NIDS. intros a. rewrite obj_range_mk by lia. cbn [fst snd eval]. rewrite u64_lit by lia. intros Ha. left. left. unfold SegD_wf.NIDS, DEPOT, MAP1, MAP1N in *. lia. }

  assert (H1 : SPA segsA (JJ G0) (mkFindB L2s) rho' tp0 (tr, mkCfg ms md)).
  { unfold rho'. eapply (SPA_bindV segsA (JJ G0) NPRE); [cbn; exact L2_X | apply JJ_stable; lia | | rewrite Hfst; exact FBz_vars | rewrite Hfst; cbn [ax_base mkFindB upd ax_setS]; exact FBz_bvars | exact H].
    rewrite Hfst. unfold VS_Z, NPRE. intros v Hv. cbn in Hv. lia. }
  pose proof (SPA_facts segsA _ _ _ _ _ H1) as HFall'.
  assert (HF2' : Forall (holds rho') (F_D ++ F_tw)).
  { eapply holds_inclb; [exact L2_F|]. unfold mkFindB, upd in HFall'. cbn [ax_S ax_setS ss_facts] in HFall'. apply Forall_app in HFall' as [X _]. exact X. }

  assert (H2 : SPA segsA (JJ G0) (ax_setS (mkFindB L2s) S_Zb) rho' tp0 (tr, mkCfg ms md)).
  { unfold S_Zb, O_nid.
    apply (SPA_carve_obj segsA (JJ G0) rho' (mkFindB L2s) tp0 _ (SLit 0) NIDS (NIDS + 4) [(NIDS, 4%nat, vN)] NXD H1 Zb_swf).
    - apply Pos.le_refl.
    - unfold NIDS; lia.
    - unfold NIDS; lia.
    - unfold NIDS; lia.
    - unfold NIDS; lia.
    - cbn [eval]. rewrite u64_lit by lia. unfold NIDS; lia.
    - cbn [eval]. rewrite u64_lit by lia. unfold NIDS; lia.
    - unfold cells_inside. constructor; [cbn; unfold NIDS; lia|constructor].
    - pose proof (proj1 H1) as Hsm1. unfold smatchA, virt in Hsm1. cbn [fst snd cfg_ms cfg_model w_tr w_cfg] in Hsm1. apply proj1 in Hsm1.
      assert (SK : map skel (ss_objs SB) = map skel ([stack_win; O_trD] ++ A_globals ++ RT_D ++ [O_tw vW])).
      { unfold SB, mkFindB, upd. cbn [ax_S ax_setS ss_objs]. rewrite app_nil_r. exact L2_skel. }
      cbn [eval]. rewrite u64_lit by lia. rewrite Z.add_0_l.
      eapply (fb_objs_ranges rho' SB _ _ Hsm1 ltac:(intros o Ho; exact Ho) SK HF2' ltac:(first [assumption | eapply TOPr_of_REL; eassumption | eapply TOPr_of_JJ; eassumption])); unfold NIDS; lia.
    - intros off Hoff. cbn [eval]. rewrite u64_lit by lia. rewrite Z.add_0_l. unfold NIDS in Hoff. split; [apply wok_of_imageA; lia | apply rd_of_imageA; lia].
    - cbn [eval]. rewrite u64_lit by lia.
      unfold cells_in_view. constructor; [|constructor]. intros jj Hjj.
      refine (civ_cell rho' (rm rho') 0 NIDS 4 (dN G0) vN _ _ _ _ jj Hjj); [rewrite Z.add_0_l; rewrite Z.add_0_r in Hcell'; exact Hcell' | cbn [eval]; exact E177 | unfold NIDS; lia | unfold NIDS; lia].
    - unfold xwords_clear. cbn. rewrite L2_X. intros rr y jj [].
  }

  assert (H3 : SPA segsA (JJ G0) (ax_setS (ax_setS (mkFindB L2s) S_Zb) (ax_S (mkFindZ L2s))) rho' tp0 (tr, mkCfg ms md)).
  { eapply (SPA_restate segsA (JJ G0) rho' _ (ax_S (mkFindZ L2s)) tp0 _ _ _ FZ_swf).
    - cbn [ax_S ax_setS]. exact FZ_sd.
    - reflexivity.
    - unfold diffs_ok, vS. apply Forall_cons; [|apply Forall_nil]. cbn [fst snd eval]. rewrite E175. apply bv_eq. rewrite Hz, u64_lit by lia. reflexivity.
    - unfold F_N, vN. apply Forall_cons; [|apply Forall_nil]. cbn [holds eval]. rewrite E177, !u64_lit by lia. unfold DNMAX in HDN. lia.
    - exact H2. }
  rewrite ax_setS_setS in H3. unfold mkFindB, upd in H3. rewrite ax_setS_setS in H3. exact H3.
Qed.

Variable I3s : axst.
Hypothesis RUNZ : ltac2:(tb__ "0|0|
S35S27S52A1S9aU12cS25S3aZ7ebe4S26S3aA1A3SbdVL2s;A1A3S25S52S53VI3s;S126A2S26S52A1A3A3").
Lemma winDFP_wf2 : ltac2:(tb__ "0|0|
S35S28S116S0S14S95A1S25S0S97S96A1S25S0S9dS9fA1S26S0A1A3A3A3S2aA3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition insK (G : DG) (rho : valuation) : Prop := ltac2:(tb__ "0|2|
S36S35S3aS49Q40M0S3Vrho;Pb1A2A2S5dVG;A1M1A3S36S3eS49G0S3Vrho;PaaA2A2G1A2S36S68VG;Vrho;S97S96A1A3S68VG;Vrho;S9dS9fA1A3A2A2A2").

Lemma insK_agree : ltac2:(tb__ "0|0|
S5cS1S1SbS95R2R1A3S69R4R3A2S69R5R3A2F_;F_;Frho';Frho;FG;").
Proof.
  intros G rho rho' Hag (A & B & C & D). pose proof winDFP_wf2 as W. cbn [forallb] in W. apply andb_prop in W as [W1 W]. apply andb_prop in W as [W2 _].
  destruct Hag as (Hw & Hl & Hm).
  split; [rewrite <- (Hw 177%positive) by (unfold NXD; lia); exact A|]. split; [rewrite <- (Hw 170%positive) by (unfold NXD; lia); exact B|].
  split; eapply winDFP_agree; eauto; split; auto.
Qed.

Lemma zero_branch : ltac2:(tb__ "0|1|
S1S69VG0;R1A2S11dS3cVok;S4dS3cS63VG0;A1M0VI3s;R2Vtp0;A5S64A4F_;Frho;S1S35S3aS49Q40S3R1PafA2A2Z0A3S123S3cR2S97S96A1A3S6eR3A1S11eS3cVok;S4dS3cG0Sa6VL2s;A1R4Vtp0;A5S64A4F_;F_;F_;Frho;F_;").
Proof.
  intros HI3 rho Hz Hro Hw0.
  eapply triple1_conseq with (P := fun w => exists rho', (insK G0 rho') /\ SPA segsA (JJ G0) (mkFindZ L2s) rho' tp0 w).
  - intros w Hw. destruct (glue_Z rho w Hw Hz Hw0) as (rho' & A & B & C & D & E). exists rho'. split; [|exact A].
    split; [exact C|]. split; [unfold W0ok in Hw0; rewrite (B 170%positive eq_refl); exact Hw0|]. split; assumption.
  - intros w Hw. exact Hw.
  - apply triple1_ex. intros rho'. apply triple1_pure. intros HK1.
    eapply (stage_run (JJ G0)); [apply JJ_ok | apply JJ_stable; lia | exact RUNZ | discriminate | reflexivity | apply Pos.leb_le; reflexivity |].
    intros L rhoL [<-|[]] Hag. cbn [la_state]. apply HI3. eapply insK_agree; eauto.
Qed.

Lemma ezero_branch : ltac2:(tb__ "0|1|
S1S69VG0;R1A2S11cS3cS4dS3cS63VG0;A1M0VI3s;R2Vtp0;A5S64A3F_;Frho;S1S35S3aS49Q40S3R1PafA2A2Z0A3S123S3cR2S97S96A1A3S6eR3A1S11cS3cS4dS3cG0Sa6VL2s;A1R4Vtp0;A5S64A3F_;F_;F_;Frho;F_;").
Proof.
  intros HI3 rho Hz Hro Hw0.
  eapply etriple_conseq with (P := fun w => exists rho', (insK G0 rho') /\ SPA segsA (JJ G0) (mkFindZ L2s) rho' tp0 w).
  - intros w Hw. destruct (glue_Z rho w Hw Hz Hw0) as (rho' & A & B & C & D & E). exists rho'. split; [|exact A].
    split; [exact C|]. split; [unfold W0ok in Hw0; rewrite (B 170%positive eq_refl); exact Hw0|]. split; assumption.
  - intros w Hw. exact Hw.
  - apply etriple_ex. intros rho'. apply etriple_pure. intros HK1.
    eapply (estage_run (JJ G0)); [apply JJ_stable; lia | exact RUNZ | discriminate | reflexivity | apply Pos.leb_le; reflexivity |].
    intros L rhoL [<-|[]] Hag. cbn [la_state]. apply HI3. eapply insK_agree; eauto.
Qed.

Let SI3 : sstate := ax_S I3s.
Definition VS_NB : list positive := [178]%positive.
Let S_I4b : sstate := ltac2:(tb__ "0|0|
S13ScVSI3;A1SfVSI3;A1S16VSI3;A1S15VSI3;A1S17VSI3;A1S29S0S6VSI3;A1S25S0S99S9bA1S26S0A1A3A3S7VSI3;A1S95SaVSI3;A1A9").
Hypothesis I3_X : ax_X I3s = [].
Hypothesis I3_len : ltac2:(tb__ "0|0|
S35S28SaS51VI3s;A1A1S30A3").
Hypothesis I3_nx : ltac2:(tb__ "0|0|
S35S3bS8S51VI3s;A1A1S95A3").
Hypothesis I3_vars : ltac2:(tb__ "0|0|
S35S28S140S124S85A1VSI3;A2S2aA3").
Hypothesis I3_bvars : ltac2:(tb__ "0|0|
S35S28S13fS124S85A1S56VI3s;A1A2S2aA3").
Hypothesis I3_F : ltac2:(tb__ "0|0|
S35S28S125S29S4S9eS29S4Sa5Sa7A3A3S7VSI3;A1A2S2aA3").
Hypothesis I3_skel : ltac2:(tb__ "0|2|
S35S27S2bS2bS2S2A2S2A2M0A1S113S0G0S122S6VSI3;A1A4S113S0G0S122S29S0S29S0S25S0S138S25S0Sa3S26S0A1M1A3A3S29S0S137Sa4A3A3S25S0S97S96A1S25S0S9dS9fA1G1A3A3A3A4A3").
Hypothesis I4b_swf : swf S_I4b = true.
Hypothesis I4_fb : ltac2:(tb__ "0|0|
S35S28S116S4S10S95A1S29S4S7VSI3;A1SabA3A3S2aA3").

Lemma glue_nb : ltac2:(tb__ "0|4|
S1S11bS4dS3cS63VG0;A1M0VI3s;R2Vtp0;R1A6S69VG0;R3A2S119S42S40S3dS5dVG0;A1Z1A2Z10000A2A1M1S2dS3aS60VG0;A1M2A2A2S37S1S1S36S4dS3cG0SceVI3s;A1R1Vtp0;R5A6S36S69VG0;R1A2S36S35S3aS49Q40S3R1Pb2A2A2S114S3aG1G2Z0A4A3S36S123S3cR1S99S9bA1M3A3S68VG0;R1G3A3A2A2A2A2Lrho';A2F_;F_;F_;Fw;Frho;").
Proof.
  intros rho w H HIK Hj. destruct w as [tr [ms md]].
  pose proof H as [HsmA [HREL [HK [[HM HV] _]]]].
  pose proof HIK as (K177 & KW0 & KD1 & KD2).
  pose proof (dm_N _ _ HM) as [HN _].
  set (j := (dN G0 + 1) / 65536) in *.
  assert (Hjb : 0 <= j < MAP1N).
  { unfold j, MAP1N. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
  pose proof (dm_map1 _ _ HM j Hjb) as Hslot.
  set (blk := nth (Z.to_nat j) (dNB G0) 0) in *.
  assert (Hin : In blk (dNB G0)) by (unfold blk; apply nth_In; exact Hj).
  destruct (dm_nb _ _ HM blk Hin) as (Bal & Blo & Bhi & Bpres).
  pose proof (nb_top _ _ _ _ _ _ _ HK HV Hin) as BhiT.
  set (bs := [(178%positive, Z_to_bv 64 blk)]).
  set (rho' := rho_sets rho bs).
  assert (Hfst : map fst bs = VS_NB) by reflexivity.
  assert (Hnd : List.NoDup (map fst bs)) by (rewrite Hfst; unfold VS_NB; repeat constructor; cbn; lia).
  assert (E178 : rw rho' 178%positive = Z_to_bv 64 blk) by (apply rho_sets_get; [exact Hnd | left; reflexivity]).
  destruct (rho_sets_rl_rm bs rho) as [Hrl' Hrm']. fold rho' in Hrl', Hrm'.
  assert (Hother : forall i, notin_vars VS_NB i = true -> rw rho' i = rw rho i).
  { intros i Hi. unfold rho'. apply rho_sets_other. rewrite Hfst. apply notin_vars_true. exact Hi. }
  assert (AG : agree_below NXD rho rho' -> True) by (intros; exact I). clear AG.
  assert (HIK' : insK G0 rho').
  { pose proof winDFP_wf2 as W. cbn [forallb] in W. apply andb_prop in W as [W1 W]. apply andb_prop in W as [W2 _].
    split; [rewrite (Hother 177%positive eq_refl); exact K177|]. split; [rewrite (Hother 170%positive eq_refl); exact KW0|].
    split.
    - intros a Ha. apply (KD1 a). rewrite <- (obj_range_agree_vars (notin_vars VS_NB) rho rho' (O_tw vW)); [exact Ha | intros v Hv; symmetry; apply Hother; exact Hv | intros l; rewrite Hrl'; reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc].
    - intros a Ha. apply (KD2 a). rewrite <- (obj_range_agree_vars (notin_vars VS_NB) rho rho' (O_nid vN)); [exact Ha | intros v Hv; symmetry; apply Hother; exact Hv | intros l; rewrite Hrl'; reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc]. }
  pose proof alloc_ceiling_valD as ACV.
  assert (SA : bv_unsigned (eval rho' slotN_addr) = MAP1 + 8 * j).
  { unfold j. apply slotN_addr_val; [rewrite (Hother 177%positive eq_refl); exact K177 | ].
    destruct (kd_room segsA K NPRE HKD G0 rho tp0 _ _ HK (conj HM HV)) as [_ HDN]. unfold DNMAX in HDN. lia. }
  assert (Hcell' : cell_ok (view segsA (rm rho')) (mkACell (MAP1 + 8 * j + 0) 8 blk)) by (rewrite Hrm', Z.add_0_r; exact Hslot).
  assert (CIV : cells_in_view rho' (rd_of segsA (rm rho')) (MAP1 + 8 * j) [(0, 8%nat, vNB)]).
  { unfold cells_in_view. constructor; [|constructor]. intros jj Hjj.
    refine (civ_cell rho' (rm rho') (MAP1 + 8 * j) 0 8 blk vNB Hcell' _ _ _ jj Hjj); [cbn [eval]; exact E178 | unfold MAP1; lia | unfold MAP1, MAP1N in *; lia]. }
  exists rho'. split; [|split; [exact HIK' | split; [rewrite E178, u64_lit by (unfold IMG_HI, NBSZ in *; lia); reflexivity | split]]].
  2:{ exists slotN_addr, 0, 8%nat, vNB. rewrite SA. split; [reflexivity|]. unfold MAP1, MAP1N in *. repeat (split; [lia|]). exact CIV. }
  2:{ unfold winDFP, O_slotN, carved. intros a. rewrite obj_range_mk by lia. cbn [fst snd]. rewrite SA. intros Ha. left. left. unfold DEPOT, MAP1, MAP1N in *. lia. }

  assert (H1 : SPA segsA (JJ G0) I3s rho' tp0 (tr, mkCfg ms md)).
  { unfold rho'. eapply (SPA_bindV segsA (JJ G0) NPRE); [exact I3_X | apply JJ_stable; lia | | rewrite Hfst; exact I3_vars | rewrite Hfst; exact I3_bvars | exact H].
    rewrite Hfst. unfold VS_NB, NPRE. intros v Hv. cbn in Hv. lia. }
  pose proof (SPA_facts segsA _ _ _ _ _ H1) as HFall'.
  pose proof (holds_inclb rho' _ _ I3_F HFall') as HF3. apply Forall_app in HF3 as [HFD HF3]. apply Forall_app in HF3 as [HFt HFn].

  assert (H2 : SPA segsA (JJ G0) (ax_setS I3s S_I4b) rho' tp0 (tr, mkCfg ms md)).
  { unfold S_I4b, O_slotN.
    apply (SPA_carve_obj segsA (JJ G0) rho' I3s tp0 _ slotN_addr 0 8 [(0, 8%nat, vNB)] NXD H1 I4b_swf).
    - rewrite I3_nx. apply Pos.le_refl.
    - lia.
    - lia.
    - lia.
    - lia.
    - rewrite SA. unfold MAP1. lia.
    - rewrite SA. unfold MAP1, MAP1N in *. lia.
    - unfold cells_inside. constructor; [cbn; lia|constructor].
    - pose proof (proj1 H1) as Hsm1. unfold smatchA, virt in Hsm1. cbn [fst snd cfg_ms cfg_model w_tr w_cfg] in Hsm1. apply proj1 in Hsm1.
      rewrite SA.
      eapply (objs_ranges_ext rho' SI3 _ _ [O_tw vW; O_nid vN] _ _ Hsm1 ltac:(intros o Ho; exact Ho) I3_skel HFD ltac:(first [assumption | eapply TOPr_of_REL; eassumption | eapply TOPr_of_JJ; eassumption])); [unfold STORE, MAP1; lia | unfold MAP1, MAP1N in *; lia | lia |].
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      + pose proof (KD1) as X. unfold winDFP, O_tw, carved in X |- *. unfold ranges_disjoint. rewrite obj_range_mk by lia. cbn [fst snd eval vP].
        assert (HP : bv_unsigned (rw rho' 171%positive) <= DEPOT + 4 * 2 ^ 20 - 4).
        { pose proof (proj1 (Forall_forall _ _) HFt (SPUle vP (SLit (DEPOT + 4 * 2^20 - 4))) ltac:(unfold F_tw; cbn; tauto)) as X1.
          cbn [holds eval vP] in X1. unfold DEPOT in *. rewrite u64_lit in X1 by lia. exact X1. }
        unfold DEPOT, MAP1 in *. lia.
      + unfold O_nid, carved, ranges_disjoint. rewrite obj_range_mk by (unfold NIDS; lia). cbn [fst snd eval]. rewrite u64_lit by lia. unfold NIDS, MAP1. lia.
    - rewrite SA. intros off Hoff. unfold MAP1, MAP1N in *. split; [apply wok_of_imageA; lia | apply rd_of_imageA; lia].
    - rewrite SA. exact CIV.
    - unfold xwords_clear. cbn [ax_X]. rewrite I3_X. intros rr y jj [].
  }

  assert (H3 : SPA segsA (JJ G0) (ax_with_facts (ax_setS I3s S_I4b) (ss_facts SI3 ++ F_nb)) rho' tp0 (tr, mkCfg ms md)).
  { apply SPA_refacts; [exact H2 | exact I4_fb |]. cbn [ax_S ax_setS ss_facts]. intros HFB. apply Forall_app. split; [exact HFB|].
    unfold F_nb, vNB. unfold IMG_HI, NBSZ, PG in *.
    apply Forall_cons. { cbn [holds eval branch_taken]. unfold bv_eqb. rewrite E178, !u64_lit by lia. intros X. apply Z.eqb_eq in X. lia. }
    apply Forall_cons. { cbn [holds]. split; [lia|]. rewrite E178, u64_lit by lia. exact Bal. }
    apply Forall_cons. { cbn [holds eval]. rewrite E178, !u64_lit by lia. lia. }
    apply Forall_cons. { cbn [holds eval]. rewrite E178, !u64_lit by lia. lia. }
    apply Forall_nil. }
  unfold ax_with_facts in H3. rewrite ax_setS_setS in H3. exact H3.
Qed.

Variable NBr : axst.
Hypothesis RUNNB : ltac2:(tb__ "0|0|
S35S27S52A1S9aU14S25S3aZ7ebecS26S3aA1A3SceVI3s;A1A3S25S52S53VNBr;S126A2S26S52A1A3A3").

Definition nbK (G : DG) (rho : valuation) : Prop := ltac2:(tb__ "0|3|
S36S69VG;Vrho;A2S36S119S42S40S3dS5dVG;A1Z1A2Z10000A2A1M0S2dS3aS60VG;A1M1A2A2S36S35S3aS49Q40S3Vrho;Pb2A2A2S114S3aG0G1Z0A4A3S36S123S3cVrho;S99S9bA1M2A3S68VG;Vrho;G2A3A2A2A2A2").

Variable sH : wsub.
Hypothesis ENT_H : ltac2:(tb__ "0|0|
S35S28S54VNBr;SeaVNBr;A1VsH;A3S2aA3").
Hypothesis SID_H : ltac2:(tb__ "0|0|
S35S28S13aVsH;S98A2S2aA3").
Definition ids4 (s : wsub) : bool := ltac2:(tb__ "0|0|
S116S3bS3bS1cS13bVs;R1A2S9R1A1A2Li;S25S3bPaaS25S3bPabS25S3bPb1S25S3bPb2S26S3bA1A3A3A3A3A3").
Hypothesis IDS_H : ids4 sH = true.
Let NBs : axst := mkNBh NBr.

Lemma ids4_rw : ltac2:(tb__ "0|0|
S13cS1S3bS35S28S90R3A1S2aA3S117S3bR2S25S3bPaaS25S3bPabS25S3bPb1S25S3bPb2S26S3bA1A3A3A3A3A3S35S4aQ40A1S3S13dR4R5A2R3A2S3R4R3A2A3F_;F_;Fi;Frho;Fs;").
Proof.
  intros s rho i H Hi. unfold ids4 in H. pose proof (proj1 (forallb_forall _ _) H i Hi) as X. apply sv_eqb_sound in X.
  cbn [rw rho_sub]. rewrite X. reflexivity.
Qed.

Lemma OWV4 : ltac2:(tb__ "0|0|
S35S28S116S0S141S3bS118S3bS14bR1A1S25S3bPaaS25S3bPabS25S3bPb1S25S3bPb2S26S3bA1A3A3A3A3A3Li;A1S25S0S97S96A1S25S0S9dS9fA1S25S0S99S9bA1S26S0A1A3A3A3A3S2aA3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma nbK_vars : ltac2:(tb__ "0|2|
S5cS1S1S3bS117S3bR1S25S3bPaaS25S3bPabS25S3bPb1S25S3bPb2S26S3bA1A3A3A3A3A3S35S4aQ40A1M0S3R3R2A2S3R4R2A2A3F_;Fi;S3bS35S27S4aQ8A1M1A1S1bR3R1A2S1bR4R1A2A3Fl;G0S35S2fG1A1SdR4R1A2SdR5R1A2A3Fa;S6bR6R5A2S6bR7R5A2F_;F_;F_;F_;Frho';Frho;FG;").
Proof.
  intros G rho rho' Hv Hl Hm ((A1 & A2 & A3 & A4) & B & C & D & E).
  pose proof OWV4 as W. cbn [forallb] in W. apply andb_prop in W as [W1 W]. apply andb_prop in W as [W2 W]. apply andb_prop in W as [W3 _].
  assert (HV : forall v, existsb (Pos.eqb v) [170; 171; 177; 178]%positive = true -> rw rho v = rw rho' v).
  { intros v Hvv. symmetry. apply Hv. apply existsb_exists in Hvv as (x & Hx & Ex). apply Pos.eqb_eq in Ex. subst. exact Hx. }
  assert (RG : forall o, obj_vars_all (fun i => existsb (Pos.eqb i) [170; 171; 177; 178]%positive) o = true -> obj_range rho' o = obj_range rho o).
  { intros o Ho. apply (obj_range_agree_vars _ rho rho' o HV (fun l => eq_sym (Hl l)) Ho). }
  split; [|split; [exact B | split; [rewrite (Hv 178%positive ltac:(cbn; tauto)); exact C | split]]].
  - split; [rewrite (Hv 177%positive ltac:(cbn; tauto)); exact A1|]. split; [rewrite (Hv 170%positive ltac:(cbn; tauto)); exact A2|].
    split; [intros a Ha; apply A3; rewrite <- (RG _ W1); exact Ha | intros a Ha; apply A4; rewrite <- (RG _ W2); exact Ha].
  - eapply (ro_win_vars segsA (fun i => existsb (Pos.eqb i) [170; 171; 177; 178]%positive)); [exact HV | intros l; symmetry; apply Hl | | exact W3 | exact D].
    intros a. unfold rd_of. rewrite Hm. reflexivity.
  - intros a Ha. apply E. rewrite <- (RG _ W3). exact Ha.
Qed.

Lemma glue_h : ltac2:(tb__ "0|0|
S5cS27S4aQ40A1A1S1S11bS4dS3cS63R4A1VNBr;R2R3R1A6S6bR5R3A2S37S1S1S36S4dS3cS63R7A1VNBs;R1R6R4A6S6bR7R1A2A2Lrho';A2F_;F_;Fw;Frho;Ftp;FG;").
Proof.
  intros G tp rho w H HNK. exists (rho_sub rho sH). split.
  - apply (SPA_entails segsA (JJ G) NPRE NBr NBs sH rho tp _ ENT_H SID_H (JJ_stable G NPRE ltac:(lia))). exact H.
  - apply (nbK_vars G rho); [intros i Hi; apply ids4_rw; [exact IDS_H | exact Hi] | intros l; reflexivity | intros a; reflexivity | exact HNK].
Qed.

Let SNB : sstate := ax_S NBs.
Definition HS (G : DG) (S : Z) : Prop := ltac2:(tb__ "0|2|
S39S35S3aVS;S5fVG;A1M0A3S36S35S3aVS;S3dG0S3dVsz;Z1A2A2A3S3eZ100000M1S3dS41G0G1A2Vsz;A2A2A2A2").

Definition jK (G : DG) (S : Z) (rho : valuation) : Prop := ltac2:(tb__ "0|4|
S36S69VG;Vrho;A2S36S119S42S40S3dS5dVG;A1Z1A2Z10000A2A1M0S2dS3aS60VG;A1M1A2A2S36S35S3aS49Q40M2S3Vrho;Pb2A2A2S114S3aG0G1Z0A4A3S36S35S3aS49G2S3Vrho;Pb3A2A2VS;A3S36S123S3cVrho;S99S9bA1M3A3S112S0S68VG;Vrho;A2S25S0G3S25S0Sa2S25S0Sa1S9cA1S26S0A1A3A3A3A3A2A2A2A2A2").

Definition VS_N : list positive := [179]%positive.
Let S_Inb : sstate := ltac2:(tb__ "0|0|
S13ScVSNB;A1SfVSNB;A1S16VSNB;A1S15VSNB;A1S17VSNB;A1S29S0S6VSNB;A1S25S0Sa2S25S0Sa1S9cA1S26S0A1A3A3A3S7VSNB;A1S95SaVSNB;A1A9").
Hypothesis NB_X : ax_X NBs = [].
Hypothesis NB_len : ltac2:(tb__ "0|0|
S35S28SaS51VNBs;A1A1S30A3").
Hypothesis NB_nx : ltac2:(tb__ "0|0|
S35S3bS8S51VNBs;A1A1S95A3").
Hypothesis NB_vars : ltac2:(tb__ "0|0|
S35S28S140S124S84A1VSNB;A2S2aA3").
Hypothesis NB_bvars : ltac2:(tb__ "0|0|
S35S28S13fS124S84A1S56VNBs;A1A2S2aA3").
Hypothesis NB_F : ltac2:(tb__ "0|0|
S35S28S125S29S4S9eS29S4Sa5S29S4Sa7SabA3A3A3S7VSNB;A1A2S2aA3").
Hypothesis NB_skel : ltac2:(tb__ "0|2|
S35S27S2bS2bS2S2A2S2A2M0A1S113S0G0S122S6VSNB;A1A4S113S0G0S122S29S0S29S0S25S0S138S25S0Sa3S26S0A1M1A3A3S29S0S137Sa4A3A3S25S0S97S96A1S25S0S9dS9fA1S25S0S99S9bA1G1A3A3A3A3A4A3").
Hypothesis In_swf : swf S_Inb = true.
Hypothesis In_fb : ltac2:(tb__ "0|0|
S35S28S116S4S10S95A1S29S4S7VSNB;A1Sb4Vsz;A1A3A3S2aA3").

Lemma glue_n : ltac2:(tb__ "0|1|
S5cS27S4aQ40A1A1S1S11bS4dS3cS63R4A1VNBs;R2R3R1A6S6bR5R3A2S3fS3dS41S5fR6A1Z100000M0A2Vsz;A2G0A2S37S1S1S36S4dS3cS63R8A1Sd2Vsz;VNBs;A2R1R7R5A6S67R8S5fR8A1R1A3A2Lrho';A2F_;F_;F_;Fw;Frho;Ftp;FG;").
Proof.
  intros G tp rho w H (HIK & Hj & H178 & HROs & HDs) Hns. destruct w as [tr [ms md]].
  pose proof H as [HsmA [HREL [HK [[HM HV] _]]]].
  pose proof HIK as (K177 & KW0 & KD1 & KD2).
  pose proof (dm_N _ _ HM) as [HN _]. pose proof (dm_F _ _ HM) as (HF0 & HF11 & HF32 & HFcell).
  destruct (kd_room segsA K NPRE HKD G rho tp _ _ HK (conj HM HV)) as [_ HDN].
  set (jN := Z.to_nat ((dN G + 1) / 65536)) in *. set (blkN := nth jN (dNB G) 0) in *.
  assert (HinN : In blkN (dNB G)) by (unfold blkN; apply nth_In; exact Hj).
  destruct (dm_nb _ _ HM blkN HinN) as (NBal & NBlo & NBhi & NBpres).
  pose proof (nb_top _ _ _ _ _ _ _ HK HV HinN) as NBhiT.
  set (F := dF G) in *.
  pose proof (Z.mod_pos_bound F 1048576 ltac:(lia)) as MB. pose proof (Z.mod_pos_bound (dN G + 1) 65536 ltac:(lia)) as MBN.
  set (bs := [(179%positive, Z_to_bv 64 F)]).
  set (rho' := rho_sets rho bs).
  assert (Hfst : map fst bs = VS_N) by reflexivity.
  assert (Hnd : List.NoDup (map fst bs)) by (rewrite Hfst; unfold VS_N; repeat constructor; cbn; lia).
  assert (E179 : rw rho' 179%positive = Z_to_bv 64 F) by (apply rho_sets_get; [exact Hnd | left; reflexivity]).
  destruct (rho_sets_rl_rm bs rho) as [Hrl' Hrm']. fold rho' in Hrl', Hrm'.
  assert (Hother : forall i, notin_vars VS_N i = true -> rw rho' i = rw rho i).
  { intros i Hi. unfold rho'. apply rho_sets_other. rewrite Hfst. apply notin_vars_true. exact Hi. }
  pose proof alloc_ceiling_valD as ACV.
  assert (U179 : bv_unsigned (rw rho' 179%positive) = F) by (rewrite E179, u64_lit; lia).
  assert (U178 : bv_unsigned (rw rho' 178%positive) = blkN) by (rewrite (Hother 178%positive eq_refl); exact H178).
  assert (NNA : bv_unsigned (eval rho' nn_addr) = blkN + 16 * ((dN G + 1) mod 65536)).
  { rewrite (nn_addr_val rho' (dN G)); [rewrite U178; reflexivity | rewrite (Hother 177%positive eq_refl); exact K177 | unfold DNMAX in HDN; lia | rewrite U178; exact NBhi]. }
  assert (CIVt : cells_in_view rho' (rd_of segsA (rm rho')) 0 [(STORE, 8%nat, vF)]).
  { unfold cells_in_view. constructor; [|constructor]. intros jj Hjj.
    refine (civ_cell rho' (rm rho') 0 STORE 8 F vF _ _ _ _ jj Hjj); [rewrite Hrm', Z.add_0_l; exact HFcell | cbn [eval]; exact E179 | unfold STORE; lia | unfold STORE; lia]. }
  assert (HIK' : insK G rho').
  { split; [rewrite (Hother 177%positive eq_refl); exact K177|]. split; [rewrite (Hother 170%positive eq_refl); exact KW0|].
    split.
    - intros a Ha. apply (KD1 a). rewrite <- (obj_range_agree_vars (notin_vars VS_N) rho rho' (O_tw vW)); [exact Ha | intros v Hv; symmetry; apply Hother; exact Hv | intros l; rewrite Hrl'; reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc].
    - intros a Ha. apply (KD2 a). rewrite <- (obj_range_agree_vars (notin_vars VS_N) rho rho' (O_nid vN)); [exact Ha | intros v Hv; symmetry; apply Hother; exact Hv | intros l; rewrite Hrl'; reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc]. }
  exists rho'. split.
  2:{ split; [exact HIK'|]. split; [exact Hj|]. split; [exact U178|]. split; [exact U179|]. split.
      - eapply (ro_win_vars segsA (notin_vars VS_N)); [intros v Hv; symmetry; apply Hother; exact Hv | intros l; rewrite Hrl'; reflexivity | intros a; rewrite Hrm'; reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | exact HROs].
      - unfold winDFP, O_slotN, O_nn, O_tf, carved.
        apply Forall_cons. { intros a Ha. apply (HDs a). rewrite <- (obj_range_agree_vars (notin_vars VS_N) rho rho' (O_slotN vNB)); [exact Ha | intros v Hv; symmetry; apply Hother; exact Hv | intros l; rewrite Hrl'; reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc]. }
        apply Forall_cons. { intros a. rewrite obj_range_mk by lia. cbn [fst snd]. rewrite NNA. intros Ha. right. left. exists blkN. split; [exact HinN | unfold NBSZ in *; lia]. }
        apply Forall_cons. { intros a. unfold STORE. rewrite obj_range_mk by lia. cbn [fst snd eval]. rewrite u64_lit by lia. intros Ha. left. right. unfold SegD_wf.STORE, NFBLK. lia. }
        apply Forall_nil. }

  assert (H1 : SPA segsA (JJ G) NBs rho' tp (tr, mkCfg ms md)).
  { unfold rho'. eapply (SPA_bindV segsA (JJ G) NPRE); [exact NB_X | apply JJ_stable; lia | | rewrite Hfst; exact NB_vars | rewrite Hfst; exact NB_bvars | exact H].
    rewrite Hfst. unfold VS_N, NPRE. intros v Hv. cbn in Hv. lia. }
  pose proof (SPA_facts segsA _ _ _ _ _ H1) as HFall'.
  pose proof (holds_inclb rho' _ _ NB_F HFall') as HF4. apply Forall_app in HF4 as [HFD HF4]. apply Forall_app in HF4 as [HFt HF4]. apply Forall_app in HF4 as [HFn HFnb].
  assert (HP : bv_unsigned (rw rho' 171%positive) <= DEPOT + 4 * 2 ^ 20 - 4).
  { pose proof (proj1 (Forall_forall _ _) HFt (SPUle vP (SLit (DEPOT + 4 * 2^20 - 4))) ltac:(unfold F_tw; cbn; tauto)) as X1.
    cbn [holds eval vP] in X1. unfold DEPOT in *. rewrite u64_lit in X1 by lia. exact X1. }
  assert (SNA : DEPOT <= bv_unsigned (eval rho' slotN_addr) /\ bv_unsigned (eval rho' slotN_addr) + 8 <= IMG_HI).
  { rewrite (slotN_addr_val rho' (dN G)); [| rewrite (Hother 177%positive eq_refl); exact K177 | unfold DNMAX in HDN; lia].
    assert (0 <= (dN G + 1) / 65536 < 2 ^ 15) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; unfold DNMAX in HDN; lia]).
    unfold DEPOT, MAP1, IMG_HI. lia. }

  assert (H2 : SPA segsA (JJ G) (ax_setS NBs S_Inb) rho' tp (tr, mkCfg ms md)).
  { unfold S_Inb, O_nn, O_tf.
    apply (SPA_carve_list segsA (JJ G) rho' NBs tp _
             [(nn_addr, 0, 16, []); (SLit 0, STORE, STORE + 8, [(STORE, 8%nat, vF)])] NXD H1 In_swf ltac:(rewrite NB_nx; apply Pos.le_refl)).
    - unfold IMG_HI, NBSZ, FBSZ, FBPAGES, PG, SZMAXT in *.
      apply Forall_cons. { rewrite NNA. repeat (split; [lia|]). split; [unfold cells_inside; constructor|]. split; [|split; [constructor | unfold xwords_clear; cbn [ax_X]; rewrite NB_X; intros rr y jj []]].
        intros off Hoff. destruct (NBpres (blkN + 16 * ((dN G + 1) mod 65536) + off) ltac:(lia)) as [x Hx]. rewrite view_in in Hx by lia. rewrite Hrm'. eapply wok_rd_off_image; [lia | exact Hx]. }
      apply Forall_cons. { cbn [eval]. rewrite u64_lit by lia. unfold STORE. repeat (split; [lia|]). split; [unfold cells_inside; constructor; [cbn; lia | constructor]|]. split; [|split; [exact CIVt | unfold xwords_clear; cbn [ax_X]; rewrite NB_X; intros rr y jj []]].
        intros off Hoff. rewrite Z.add_0_l. split; [apply wok_of_imageA; lia | apply rd_of_imageA; lia]. }
      apply Forall_nil.
    -
      pose proof (proj1 H1) as Hsm1. unfold smatchA, virt in Hsm1. cbn [fst snd cfg_ms cfg_model w_tr w_cfg] in Hsm1. apply proj1 in Hsm1.
      assert (EXD : forall lo hi, (STORE <= lo /\ hi <= DEPOT) \/ (IMG_HI <= lo /\ hi <= alloc_ceiling) -> lo <= hi ->
                Forall (fun o' => ranges_disjoint (obj_range rho' o') (lo, hi)) (ss_objs SNB)).
      { intros lo hi Hlh Hle.
        eapply (objs_ranges_ext rho' SNB _ _ [O_tw vW; O_nid vN; O_slotN vNB] _ _ Hsm1 ltac:(intros o Ho; exact Ho) NB_skel HFD ltac:(first [assumption | eapply TOPr_of_REL; eassumption | eapply TOPr_of_JJ; eassumption])); [unfold STORE, DEPOT, IMG_HI in *; lia | unfold STORE, DEPOT, IMG_HI in *; lia | exact Hle |].
        unfold O_tw, O_nid, O_slotN, carved, ranges_disjoint.
        apply Forall_cons. { rewrite obj_range_mk by lia. cbn [fst snd eval vP].
          pose proof (proj1 (Forall_forall _ _) HFt (SPUle (SLit DEPOT) vP) ltac:(unfold F_tw; cbn; tauto)) as X2. cbn [holds eval vP] in X2. unfold DEPOT in X2. rewrite u64_lit in X2 by lia.
          unfold STORE, DEPOT, IMG_HI in *. lia. }
        apply Forall_cons. { rewrite obj_range_mk by (unfold NIDS; lia). cbn [fst snd eval]. rewrite u64_lit by lia. unfold NIDS, STORE, DEPOT, IMG_HI in *. lia. }
        apply Forall_cons. { rewrite obj_range_mk by lia. cbn [fst snd]. unfold STORE, DEPOT, IMG_HI in *. lia. }
        apply Forall_nil. }
      cbn [map carve_obj]. unfold carved. unfold IMG_HI, NBSZ, FBSZ, FBPAGES, PG, SZMAXT, NFBLK in *.
      apply Forall_cons. { rewrite obj_range_mk by lia. rewrite NNA. apply EXD; [right; unfold IMG_HI; lia | lia]. }
      apply Forall_cons. { rewrite obj_range_mk by (unfold STORE; lia). cbn [eval]. rewrite u64_lit by lia. apply EXD; [left; unfold STORE, DEPOT; lia | unfold STORE; lia]. }
      apply Forall_nil.
    -
      cbn [map carve_obj pairwise_disjoint]. unfold carved. unfold IMG_HI, NBSZ, FBSZ, FBPAGES, PG, SZMAXT, NFBLK, STORE in *.
      repeat split; try exact I;
        repeat (apply Forall_cons; [unfold ranges_disjoint; rewrite !obj_range_mk by lia; cbn [fst snd eval]; rewrite ?u64_lit by lia; rewrite ?NNA; lia|]); apply Forall_nil. }

  assert (H3 : SPA segsA (JJ G) (ax_with_facts (ax_setS NBs S_Inb) (ss_facts SNB ++ F_n sz)) rho' tp (tr, mkCfg ms md)).
  { apply SPA_refacts; [exact H2 | exact In_fb |]. cbn [ax_S ax_setS ss_facts]. intros HFB. apply Forall_app. split; [exact HFB|].
    unfold F_n, vF, add. pose proof Hsz as Hsz'. unfold SZMAXT in Hsz'.
    apply Forall_cons. { cbn [holds eval]. rewrite E179, !u64_lit by lia. lia. }
    apply Forall_cons. { cbn [holds eval branch_taken]. rewrite Bool.negb_true_iff. unfold bv_eqb. rewrite !srl_val, add_val, E179, !u64_lit by lia. change (20 mod 64) with 20.
      rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 20) with 1048576. rewrite (Z.mod_small (F + sz)) by lia.
      intros X. apply Z.eqb_neq in X. apply X. clear X.
      rewrite (Z.div_mod F 1048576) at 2 by lia. replace (1048576 * (F / 1048576) + F mod 1048576 + sz) with ((F mod 1048576 + sz) + (F / 1048576) * 1048576) by lia.
      rewrite Z.div_add by lia. rewrite (Z.div_small (F mod 1048576 + sz)) by lia. lia. }
    apply Forall_nil. }
  unfold ax_with_facts in H3. rewrite ax_setS_setS in H3. exact H3.
Qed.

Variable Jsr : axst. Variable sJ : wsub.
Hypothesis RUNN : ltac2:(tb__ "0|0|
S35S27S52A1S9aU12cS25S3aSc6S26S3aA1A3Sd2Vsz;VNBs;A2A3S25S52S53VJsr;S126A2S26S52A1A3A3").
Hypothesis ENT_J : ltac2:(tb__ "0|0|
S35S28S54VJsr;Se9VJsr;A1VsJ;A3S2aA3").
Hypothesis SID_J : ltac2:(tb__ "0|0|
S35S28S13aVsJ;S98A2S2aA3").
Definition ids5 (s : wsub) : bool := ltac2:(tb__ "0|0|
S116S3bS3bS1cS13bVs;R1A2S9R1A1A2Li;S25S3bPaaS25S3bPabS25S3bPb1S25S3bPb2S25S3bPb3S26S3bA1A3A3A3A3A3A3").
Hypothesis IDS_J : ids5 sJ = true.
Let Jhs : axst := mkJh Jsr.

Lemma ids5_rw : ltac2:(tb__ "0|0|
S13cS1S3bS35S28S91R3A1S2aA3S117S3bR2S25S3bPaaS25S3bPabS25S3bPb1S25S3bPb2S25S3bPb3S26S3bA1A3A3A3A3A3A3S35S4aQ40A1S3S13dR4R5A2R3A2S3R4R3A2A3F_;F_;Fi;Frho;Fs;").
Proof.
  intros s rho i H Hi. unfold ids5 in H. pose proof (proj1 (forallb_forall _ _) H i Hi) as X. apply sv_eqb_sound in X.
  cbn [rw rho_sub]. rewrite X. reflexivity.
Qed.

Lemma OWV5 : ltac2:(tb__ "0|0|
S35S28S116S0S141S3bS118S3bS14bR1A1S25S3bPaaS25S3bPabS25S3bPb1S25S3bPb2S25S3bPb3S26S3bA1A3A3A3A3A3A3Li;A1S25S0S97S96A1S25S0S9dS9fA1S25S0S99S9bA1S25S0Sa2S25S0Sa1S9cA1S26S0A1A3A3A3A3A3A3S2aA3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma jK_vars : ltac2:(tb__ "0|2|
S5cS3aS1S1S3bS117S3bR1S25S3bPaaS25S3bPabS25S3bPb1S25S3bPb2S25S3bPb3S26S3bA1A3A3A3A3A3A3S35S4aQ40A1M0S3R3R2A2S3R4R2A2A3F_;Fi;S3bS35S27S4aQ8A1M1A1S1bR3R1A2S1bR4R1A2A3Fl;G0S35S2fG1A1SdR4R1A2SdR5R1A2A3Fa;S67R7R6R5A3S67R8R7R5A3F_;F_;F_;F_;Frho';Frho;FS;FG;").
Proof.
  intros G S rho rho' Hv Hl Hm ((A1 & A2 & A3 & A4) & B & C & D & E & F).
  pose proof OWV5 as W. cbn [forallb] in W. apply andb_prop in W as [W1 W]. apply andb_prop in W as [W2 W]. apply andb_prop in W as [W3 W]. apply andb_prop in W as [W4 W]. apply andb_prop in W as [W5 _].
  assert (HV : forall v, existsb (Pos.eqb v) [170; 171; 177; 178; 179]%positive = true -> rw rho v = rw rho' v).
  { intros v Hvv. symmetry. apply Hv. apply existsb_exists in Hvv as (x & Hx & Ex). apply Pos.eqb_eq in Ex. subst. exact Hx. }
  assert (RG : forall o, obj_vars_all (fun i => existsb (Pos.eqb i) [170; 171; 177; 178; 179]%positive) o = true -> obj_range rho' o = obj_range rho o).
  { intros o Ho. apply (obj_range_agree_vars _ rho rho' o HV (fun l => eq_sym (Hl l)) Ho). }
  split; [|split; [exact B | split; [rewrite (Hv 178%positive ltac:(cbn; tauto)); exact C | split; [rewrite (Hv 179%positive ltac:(cbn; tauto)); exact D | split]]]].
  - split; [rewrite (Hv 177%positive ltac:(cbn; tauto)); exact A1|]. split; [rewrite (Hv 170%positive ltac:(cbn; tauto)); exact A2|].
    split; [intros a Ha; apply A3; rewrite <- (RG _ W1); exact Ha | intros a Ha; apply A4; rewrite <- (RG _ W2); exact Ha].
  - eapply (ro_win_vars segsA (fun i => existsb (Pos.eqb i) [170; 171; 177; 178; 179]%positive)); [exact HV | intros l; symmetry; apply Hl | | exact W3 | exact E].
    intros a. unfold rd_of. rewrite Hm. reflexivity.
  - pose proof (Forall_inv F) as F1. pose proof (Forall_inv (Forall_inv_tail F)) as F2. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail F))) as F3.
    repeat apply Forall_cons; [| | | apply Forall_nil]; intros a Ha; [apply F1; rewrite <- (RG _ W3) | apply F2; rewrite <- (RG _ W4) | apply F3; rewrite <- (RG _ W5)]; exact Ha.
Qed.

Lemma glue_j : ltac2:(tb__ "0|0|
S5cS3aS27S4aQ40A1A1S1S11bS4dS3cS63R5A1VJsr;R2R3R1A6S67R6R5R3A3S37S1S1S36S4dS3cS63R8A1VJhs;R1R6R4A6S67R8R7R1A3A2Lrho';A2F_;F_;Fw;Frho;Ftp;FS;FG;").
Proof.
  intros G S tp rho w H HJK. exists (rho_sub rho sJ). split.
  - apply (SPA_entails segsA (JJ G) NPRE Jsr Jhs sJ rho tp _ ENT_J SID_J (JJ_stable G NPRE ltac:(lia))). exact H.
  - apply (jK_vars G S rho); [intros i Hi; apply ids5_rw; [exact IDS_J | exact Hi] | intros l; reflexivity | intros a; reflexivity | exact HJK].
Qed.

Let SJ : sstate := ax_S Jhs.
Definition VS_E2 : list positive := [180; 181]%positive.
Let S_E2b : sstate := ltac2:(tb__ "0|0|
S13ScVSJ;A1SfVSJ;A1S16VSJ;A1S15VSJ;A1S17VSJ;A1S29S0S6VSJ;A1S25S0Sa8Sb3A1S25S0Sc5Vsz;A1S25S0Sa9Sa0A1S26S0A1A3A3A3A3S7VSJ;A1S95SaVSJ;A1A9").
Hypothesis J_X : ax_X Jhs = [].
Hypothesis J_len : ltac2:(tb__ "0|0|
S35S28SaS51VJhs;A1A1S30A3").
Hypothesis J_nx : ltac2:(tb__ "0|0|
S35S3bS8S51VJhs;A1A1S95A3").
Hypothesis J_vars : ltac2:(tb__ "0|0|
S35S28S140S124S82A1VSJ;A2S2aA3").
Hypothesis J_bvars : ltac2:(tb__ "0|0|
S35S28S13fS124S82A1S56VJhs;A1A2S2aA3").
Hypothesis J_F : ltac2:(tb__ "0|0|
S35S28S125S29S4S9eS29S4Sa5S29S4Sa7S29S4SabSb4Vsz;A1A3A3A3A3S7VSJ;A1A2S2aA3").
Hypothesis J_skel : ltac2:(tb__ "0|2|
S35S27S2bS2bS2S2A2S2A2M0A1S113S0G0S122S6VSJ;A1A4S113S0G0S122S29S0S29S0S25S0S138S25S0Sa3S26S0A1M1A3A3S29S0S137Sa4A3A3S25S0S97S96A1S25S0S9dS9fA1S25S0S99S9bA1S25S0Sa2S25S0Sa1S9cA1G1A3A3A3A3A3A3A4A3").
Hypothesis E2b_swf : swf S_E2b = true.
Hypothesis E2_fb : ltac2:(tb__ "0|0|
S35S28S116S4S10S95A1S29S4S7VSJ;A1SdbA3A3S2aA3").

Definition insK5 (G : DG) (b : nat) (S : Z) (rho : valuation) : Prop := ltac2:(tb__ "0|7|
S36S69VG;Vrho;A2S36S35S3aS49Q40M0S3Vrho;Pb2A2A2S114S3aS42S40S3dS5dVG;A1Z1M1A2Z10000A2A1S60VG;A1Z0M2A4A3S36S35S3aS49G0S3Vrho;Pb3A2A2VS;A3S36S35S3aS49G0S3Vrho;Pb4A2A2S114S3aVb;S5eVG;A1G2A4A3S36S123S3cVrho;S99S9bA1M3A3S36S123S3cVrho;Sa8Sb3A1M4A3S36S112S0S68VG;Vrho;A2S25S0G3S25S0Sa2S25S0Sa1S9cA1S25S0G4S25S0Sa9Sa0A1S26S0A1A3A3A3A3A3A3S4aG0A1S36S3eS49G0SeVrho;SbcA2A2M5S49G0R1A2M6A2S3fG6S3dG5S43Z8S3dVsz;G1A2A2A2A2A2SffVG;S49G0R2A2A2F_;Fa;A2A2A2A2A2A2A2").

Lemma HS_bounds : ltac2:(tb__ "0|3|
S5cS3aS66R2R1A2S3eZ1S5fR3A1A2S3eS5fR4A1S45S44Z2M0Z20A2M1S44G0Z15A2A2A2S36S36S3eS5fR5A1M2R4A2S3eR4S3dG2Z1fA2A2A2S36S3eZ0R4A2S3fR4S45G1S44G0Z14A2A2A2A2A2F_;F_;F_;FS;FG;").
Proof. intros G S H H0 H1. pose proof Hsz as Hs. unfold SZMAXT in Hs. unfold HS in H. lia. Qed.

Lemma glue_e2 : ltac2:(tb__ "0|1|
S5cS3aS27S4aQ40A1A1S1S11bS2eS4dS3cS63R6A1VJhs;R3R4R2A6S67R7R6R4A3S66R8R7A2S35S2eR4S42S40R8Z100000M0A2A1A3S119R5S2dS3aS5eRaA1A2A2S3fS3dS41RaG0A2Vsz;A2G0A2S3eS43Z8S3dS3dS41RbG0A2Vsz;A2Z1A2A2S43S120S114S3aR7S61RcA1Z0A4A2A2S37S1S1S36S4dS3cS63ReA1Sd0Vsz;VJhs;A2R1RcRaA6S6cReR9RdR1A4A2Lrho';A2F_;F_;F_;F_;F_;F_;F_;Fb;Fw;Frho;Ftp;FS;FG;").
Proof.
  intros G S tp rho w b H HJK HHS Hb Hbl Hns Hpaid. destruct w as [tr [ms md]].
  pose proof H as [HsmA [HREL [HK [[HM HV] _]]]].
  pose proof HJK as (HIK & Hj & H178 & H179 & HROs & HDs). pose proof HIK as (K177 & KW0 & KD1 & KD2).
  pose proof (dm_N _ _ HM) as [HN _]. pose proof (dm_F _ _ HM) as (HF0 & HF11 & HF32 & HFcell).
  destruct (kd_room segsA K NPRE HKD G rho tp _ _ HK (conj HM HV)) as [_ HDN].
  destruct (HS_bounds G S HHS HF0 HF32) as [HSF HS32].
  set (jN := Z.to_nat ((dN G + 1) / 65536)) in *. set (blkN := nth jN (dNB G) 0) in *.
  assert (HinN : In blkN (dNB G)) by (unfold blkN; apply nth_In; exact Hj).
  destruct (dm_nb _ _ HM blkN HinN) as (NBal & NBlo & NBhi & NBpres).
  pose proof (nb_top _ _ _ _ _ _ _ HK HV HinN) as NBhiT.
  set (fb := nth b (dFB G) 0) in *.
  assert (HbZ : Z.of_nat b = S / 1048576) by (subst b; rewrite Z2Nat.id by (apply Z.div_pos; lia); reflexivity).
  destruct (dm_fb _ _ HM b Hbl) as (FBcell & FBnz & FBst & FBmtx). fold fb in FBcell, FBnz.
  destruct (dm_fbases _ _ HM fb (nth_In _ _ Hbl)) as (FBal & FBlo & FBhi).
  pose proof (fb_top _ _ _ _ _ _ fb HK HV (nth_In _ _ Hbl)) as FBhiT.
  destruct (dm_fp _ _ HM b Hbl) as [FPrange FPpres]. fold fb in FPpres.
  destruct (present_cell4 (view segsA (rm rho)) (STORE + 24 + 16 * Z.of_nat b) ltac:(intros z Hz; apply FBst; lia)) as (stv & Hstv & STcell).
  pose proof (Z.mod_pos_bound S 1048576 ltac:(lia)) as MB. pose proof (Z.mod_pos_bound (dN G + 1) 65536 ltac:(lia)) as MBN.
  assert (DISJNF : blkN + NBSZ <= fb \/ fb + FBSZ <= blkN) by exact (dblocks_nf_disj G jN b Hj Hbl (dm_disj _ _ HM)).
  set (bs := [(180%positive, Z_to_bv 64 fb); (181%positive, Z_to_bv 64 stv)]).
  set (rho' := rho_sets rho bs).
  assert (Hfst : map fst bs = VS_E2) by reflexivity.
  assert (Hnd : List.NoDup (map fst bs)) by (rewrite Hfst; unfold VS_E2; repeat constructor; cbn; lia).
  assert (E180 : rw rho' 180%positive = Z_to_bv 64 fb) by (apply rho_sets_get; [exact Hnd | left; reflexivity]).
  assert (E181 : rw rho' 181%positive = Z_to_bv 64 stv) by (apply rho_sets_get; [exact Hnd | right; left; reflexivity]).
  destruct (rho_sets_rl_rm bs rho) as [Hrl' Hrm']. fold rho' in Hrl', Hrm'.
  assert (Hother : forall i, notin_vars VS_E2 i = true -> rw rho' i = rw rho i).
  { intros i Hi. unfold rho'. apply rho_sets_other. rewrite Hfst. apply notin_vars_true. exact Hi. }
  pose proof alloc_ceiling_valD as ACV.
  assert (U179 : bv_unsigned (rw rho' 179%positive) = S) by (rewrite (Hother 179%positive eq_refl); exact H179).
  assert (U180 : bv_unsigned (rw rho' 180%positive) = fb) by (rewrite E180, u64_lit; [reflexivity|]; unfold IMG_HI, FBSZ in *; lia).
  assert (U178 : bv_unsigned (rw rho' 178%positive) = blkN) by (rewrite (Hother 178%positive eq_refl); exact H178).
  assert (NNA : bv_unsigned (eval rho' nn_addr) = blkN + 16 * ((dN G + 1) mod 65536)).
  { rewrite (nn_addr_val rho' (dN G)); [rewrite U178; reflexivity | rewrite (Hother 177%positive eq_refl); exact K177 | unfold DNMAX in HDN; lia | rewrite U178; exact NBhi]. }
  assert (BDA : bv_unsigned (eval rho' bd_addr) = STORE + 16 * Z.of_nat b) by (rewrite HbZ; apply bd_addr_val; [exact U179 | lia]).
  assert (FRA : bv_unsigned (eval rho' fr_addr) = fb + 8 * (S mod 1048576)).
  { rewrite <- U180. apply fr_addr_val; [exact U179 | lia | rewrite U180; exact FBhi]. }
  assert (STA : bv_unsigned (eval rho' stc_addr) = STORE + 16 * Z.of_nat b) by (rewrite HbZ; apply stc_addr_val; [exact U179 | lia]).
  pose proof (fblk_lt (dF G) ltac:(lia) ltac:(lia)) as FBL. pose proof (dm_fb_len _ _ HM) as [FBlen _].
  assert (Hb4096 : Z.of_nat b < 4096) by lia.

  assert (CIVd : cells_in_view rho' (rd_of segsA (rm rho')) (STORE + 16 * Z.of_nat b) [(16, 8%nat, vD)]).
  { unfold cells_in_view. constructor; [|constructor]. intros jj Hjj.
    refine (civ_cell rho' (rm rho') (STORE + 16 * Z.of_nat b) 16 8 fb vD _ _ _ _ jj Hjj); [rewrite Hrm' | cbn [eval]; exact E180 | unfold STORE; lia | unfold STORE; lia].
    replace (STORE + 16 * Z.of_nat b + 16) with (STORE + 16 + 16 * Z.of_nat b) by lia. exact FBcell. }
  assert (CIVs : cells_in_view rho' (rd_of segsA (rm rho')) (STORE + 16 * Z.of_nat b) [(24, 4%nat, vSt)]).
  { unfold cells_in_view. constructor; [|constructor]. intros jj Hjj.
    refine (civ_cell rho' (rm rho') (STORE + 16 * Z.of_nat b) 24 4 stv vSt _ _ _ _ jj Hjj); [rewrite Hrm' | cbn [eval]; exact E181 | unfold STORE; lia | unfold STORE; lia].
    replace (STORE + 16 * Z.of_nat b + 24) with (STORE + 24 + 16 * Z.of_nat b) by lia. exact STcell. }
  assert (RGs : forall o, In o [O_tw vW; O_nid vN; O_slotN vNB; O_nn; O_tf vF] -> obj_range rho' o = obj_range rho o).
  { pose proof OWV5 as W. intros o Ho. apply (obj_range_agree_vars (fun i => existsb (Pos.eqb i) [170; 171; 177; 178; 179]%positive) rho rho' o).
    - intros v Hv. symmetry. apply Hother. apply existsb_exists in Hv as (x & Hx & Ex). apply Pos.eqb_eq in Ex. subst. cbn in Hx. unfold notin_vars, VS_E2. cbn. destruct Hx as [<-|[<-|[<-|[<-|[<-|[]]]]]]; reflexivity.
    - intros l. rewrite Hrl'. reflexivity.
    - exact (proj1 (forallb_forall _ _) W o Ho). }
  assert (HIK' : insK G rho').
  { split; [rewrite (Hother 177%positive eq_refl); exact K177|]. split; [rewrite (Hother 170%positive eq_refl); exact KW0|].
    split; [intros a Ha; apply (KD1 a); rewrite <- (RGs (O_tw vW) ltac:(cbn; tauto)); exact Ha | intros a Ha; apply (KD2 a); rewrite <- (RGs (O_nid vN) ltac:(cbn; tauto)); exact Ha]. }
  pose proof (Forall_inv HDs) as WD1. pose proof (Forall_inv (Forall_inv_tail HDs)) as WD2. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail HDs))) as WD3.
  exists rho'. split.
  2:{ split; [exact HIK'|]. split; [exact U178|]. split; [exact U179|]. split; [exact U180|]. split; [|split; [|split]].
      - eapply (ro_win_vars segsA (notin_vars VS_E2)); [intros v Hv; symmetry; apply Hother; exact Hv | intros l; rewrite Hrl'; reflexivity | intros a; rewrite Hrm'; reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | exact HROs].
      - exists bd_addr, 16, 8%nat, vD. rewrite BDA. split; [reflexivity|]. unfold STORE in *. repeat (split; [lia|]). exact CIVd.
      - apply Forall_cons; [intros a Ha; apply WD1; rewrite <- (RGs (O_slotN vNB) ltac:(cbn; tauto)); exact Ha|].
        apply Forall_cons; [intros a Ha; apply WD2; rewrite <- (RGs O_nn ltac:(cbn; tauto)); exact Ha|].
        apply Forall_cons; [intros a Ha; apply WD3; rewrite <- (RGs (O_tf vF) ltac:(cbn; tauto)); exact Ha|].
        unfold winDFP, O_bd, O_stc, carved.
        apply Forall_cons. { intros a. rewrite obj_range_mk by lia. cbn [fst snd]. rewrite BDA. intros Ha. left. right. unfold STORE, NFBLK in *. lia. }
        apply Forall_cons. { intros a. rewrite obj_range_mk by lia. cbn [fst snd]. rewrite STA. intros Ha. left. right. unfold STORE, NFBLK in *. lia. }
        apply Forall_nil.
      - intros a. rewrite FRA. intros Ha. right. right. exists fb. split; [apply nth_In; exact Hbl | unfold FBSZ, PG, FBPAGES in *; lia]. }

  assert (H1 : SPA segsA (JJ G) Jhs rho' tp (tr, mkCfg ms md)).
  { unfold rho'. eapply (SPA_bindV segsA (JJ G) NPRE); [exact J_X | apply JJ_stable; lia | | rewrite Hfst; exact J_vars | rewrite Hfst; exact J_bvars | exact H].
    rewrite Hfst. unfold VS_E2, NPRE. intros v Hv. cbn in Hv. lia. }
  pose proof (SPA_facts segsA _ _ _ _ _ H1) as HFall'.
  pose proof (holds_inclb rho' _ _ J_F HFall') as HF4. apply Forall_app in HF4 as [HFD HF4]. apply Forall_app in HF4 as [HFt HF4].
  assert (HP : bv_unsigned (rw rho' 171%positive) <= DEPOT + 4 * 2 ^ 20 - 4).
  { pose proof (proj1 (Forall_forall _ _) HFt (SPUle vP (SLit (DEPOT + 4 * 2^20 - 4))) ltac:(unfold F_tw; cbn; tauto)) as X1.
    cbn [holds eval vP] in X1. unfold DEPOT in *. rewrite u64_lit in X1 by lia. exact X1. }
  assert (SNA : DEPOT <= bv_unsigned (eval rho' slotN_addr) /\ bv_unsigned (eval rho' slotN_addr) + 8 <= IMG_HI).
  { rewrite (slotN_addr_val rho' (dN G)); [| rewrite (Hother 177%positive eq_refl); exact K177 | unfold DNMAX in HDN; lia].
    assert (0 <= (dN G + 1) / 65536 < 2 ^ 15) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; unfold DNMAX in HDN; lia]).
    unfold DEPOT, MAP1, IMG_HI. lia. }

  assert (H2 : SPA segsA (JJ G) (ax_setS Jhs S_E2b) rho' tp (tr, mkCfg ms md)).
  { unfold S_E2b, O_bd, O_fr, O_stc.
    apply (SPA_carve_list segsA (JJ G) rho' Jhs tp _
             [(bd_addr, 16, 24, [(16, 8%nat, vD)]); (fr_addr, 0, 8 * (sz + 1), []); (stc_addr, 24, 28, [(24, 4%nat, vSt)])] NXD H1 E2b_swf ltac:(rewrite J_nx; apply Pos.le_refl)).
    - unfold IMG_HI, NBSZ, FBSZ, FBPAGES, PG, SZMAXT in *.
      apply Forall_cons. { rewrite BDA. unfold STORE in *. repeat (split; [lia|]). split; [unfold cells_inside; constructor; [cbn; lia | constructor]|]. split; [|split; [exact CIVd | unfold xwords_clear; cbn [ax_X]; rewrite J_X; intros rr y jj []]].
        intros off Hoff. split; [apply wok_of_imageA; lia | apply rd_of_imageA; lia]. }
      apply Forall_cons. { rewrite FRA. repeat (split; [lia|]). split; [unfold cells_inside; constructor|]. split; [|split; [constructor | unfold xwords_clear; cbn [ax_X]; rewrite J_X; intros rr y jj []]].
        intros off Hoff. destruct (FPpres (fb + 8 * (S mod 1048576) + off) ltac:(lia)) as [x Hx]. rewrite view_in in Hx by lia. rewrite Hrm'. eapply wok_rd_off_image; [lia | exact Hx]. }
      apply Forall_cons. { rewrite STA. unfold STORE in *. repeat (split; [lia|]). split; [unfold cells_inside; constructor; [cbn; lia | constructor]|]. split; [|split; [exact CIVs | unfold xwords_clear; cbn [ax_X]; rewrite J_X; intros rr y jj []]].
        intros off Hoff. split; [apply wok_of_imageA; lia | apply rd_of_imageA; lia]. }
      apply Forall_nil.
    -
      pose proof (proj1 H1) as Hsm1. unfold smatchA, virt in Hsm1. cbn [fst snd cfg_ms cfg_model w_tr w_cfg] in Hsm1. apply proj1 in Hsm1.
      assert (EXD : forall lo hi, (STORE + 16 <= lo /\ hi <= DEPOT) \/ (fb <= lo /\ hi <= fb + FBSZ) -> lo <= hi ->
                Forall (fun o' => ranges_disjoint (obj_range rho' o') (lo, hi)) (ss_objs SJ)).
      { intros lo hi Hlh Hle.
        eapply (objs_ranges_ext rho' SJ _ _ [O_tw vW; O_nid vN; O_slotN vNB; O_nn; O_tf vF] _ _ Hsm1 ltac:(intros o Ho; exact Ho) J_skel HFD ltac:(first [assumption | eapply TOPr_of_REL; eassumption | eapply TOPr_of_JJ; eassumption])); [unfold STORE, DEPOT, IMG_HI, FBSZ in *; lia | unfold STORE, DEPOT, IMG_HI, FBSZ in *; lia | exact Hle |].
        unfold O_tw, O_nid, O_slotN, O_nn, O_tf, carved, ranges_disjoint.
        apply Forall_cons. { rewrite obj_range_mk by lia. cbn [fst snd eval vP].
          pose proof (proj1 (Forall_forall _ _) HFt (SPUle (SLit DEPOT) vP) ltac:(unfold F_tw; cbn; tauto)) as X2. cbn [holds eval vP] in X2. unfold DEPOT in X2. rewrite u64_lit in X2 by lia.
          unfold STORE, DEPOT, IMG_HI, FBSZ in *. lia. }
        apply Forall_cons. { rewrite obj_range_mk by (unfold NIDS; lia). cbn [fst snd eval]. rewrite u64_lit by lia. unfold NIDS, STORE, DEPOT, IMG_HI, FBSZ in *. lia. }
        apply Forall_cons. { rewrite obj_range_mk by lia. cbn [fst snd]. unfold STORE, DEPOT, IMG_HI, FBSZ in *. lia. }
        apply Forall_cons. { rewrite obj_range_mk by lia. cbn [fst snd]. rewrite NNA. unfold STORE, DEPOT, IMG_HI, FBSZ, NBSZ in *. lia. }
        apply Forall_cons. { rewrite obj_range_mk by (unfold STORE; lia). cbn [fst snd eval]. rewrite u64_lit by (unfold STORE; lia). unfold STORE, DEPOT, IMG_HI, FBSZ in *. lia. }
        apply Forall_nil. }
      cbn [map carve_obj]. unfold carved. unfold IMG_HI, NBSZ, FBSZ, FBPAGES, PG, SZMAXT, NFBLK in *.
      apply Forall_cons. { rewrite obj_range_mk by lia. rewrite BDA. apply EXD; [left; unfold STORE, DEPOT in *; lia | lia]. }
      apply Forall_cons. { rewrite obj_range_mk by lia. rewrite FRA. apply EXD; [right; lia | lia]. }
      apply Forall_cons. { rewrite obj_range_mk by lia. rewrite STA. apply EXD; [left; unfold STORE, DEPOT in *; lia | lia]. }
      apply Forall_nil.
    -
      cbn [map carve_obj pairwise_disjoint]. unfold carved. unfold IMG_HI, NBSZ, FBSZ, FBPAGES, PG, SZMAXT, NFBLK, STORE in *.
      repeat split; try exact I;
        repeat (apply Forall_cons; [unfold ranges_disjoint; rewrite !obj_range_mk by lia; cbn [fst snd eval]; rewrite ?u64_lit by lia; rewrite ?BDA, ?FRA, ?STA; lia|]); apply Forall_nil. }

  assert (H3 : SPA segsA (JJ G) (ax_with_facts (ax_setS Jhs S_E2b) (ss_facts SJ ++ F_e2)) rho' tp (tr, mkCfg ms md)).
  { apply SPA_refacts; [exact H2 | exact E2_fb |]. cbn [ax_S ax_setS ss_facts]. intros HFB. apply Forall_app. split; [exact HFB|].
    unfold F_e2, vD, vSt. unfold IMG_HI, FBSZ in *.
    apply Forall_cons. { cbn [holds eval branch_taken]. unfold bv_eqb. rewrite E180, !u64_lit by lia. intros X. apply Z.eqb_eq in X. lia. }
    apply Forall_cons. { cbn [holds]. split; [lia|]. rewrite E180, u64_lit by lia. exact FBal. }
    apply Forall_cons. { cbn [holds eval]. rewrite E180, !u64_lit by lia. lia. }
    apply Forall_cons. { cbn [holds eval]. rewrite E180, !u64_lit by lia. lia. }
    apply Forall_cons. { cbn [holds eval]. rewrite E181, !u64_lit by lia. lia. }
    apply Forall_nil. }
  unfold ax_with_facts in H3. rewrite ax_setS_setS in H3. exact H3.
Qed.

Variable E2r : axst. Variable sE : wsub.
Hypothesis RUNE1 : ltac2:(tb__ "0|0|
S35S27S52A1S9aU12dS25S3aSc0S26S3aA1A3Sd0Vsz;VJhs;A2A3S25S52S53VE2r;S126A2S26S52A1A3A3").
Hypothesis ENT_E : ltac2:(tb__ "0|0|
S35S28S54VE2r;Se6VE2r;A1VsE;A3S2aA3").
Hypothesis SID_E : ltac2:(tb__ "0|0|
S35S28S13aVsE;S98A2S2aA3").
Definition ids7 (s : wsub) : bool := ltac2:(tb__ "0|0|
S116S3bS3bS1cS13bVs;R1A2S9R1A1A2Li;S25S3bPaaS25S3bPabS25S3bPb1S25S3bPb2S25S3bPb3S25S3bPb4S25S3bPb5S26S3bA1A3A3A3A3A3A3A3A3").
Hypothesis IDS_E : ids7 sE = true.
Let E2hs : axst := mkE2h E2r.
Hypothesis E2_len : ltac2:(tb__ "0|0|
S35S28SaS51VE2hs;A1A1S30A3").
Hypothesis E2_nx : ltac2:(tb__ "0|0|
S35S3bS8S51VE2hs;A1A1S95A3").

Lemma ids7_rw : ltac2:(tb__ "0|0|
S13cS1S3bS35S28S93R3A1S2aA3S117S3bR2S25S3bPaaS25S3bPabS25S3bPb1S25S3bPb2S25S3bPb3S25S3bPb4S25S3bPb5S26S3bA1A3A3A3A3A3A3A3A3S35S4aQ40A1S3S13dR4R5A2R3A2S3R4R3A2A3F_;F_;Fi;Frho;Fs;").
Proof.
  intros s rho i H Hi. unfold ids7 in H. pose proof (proj1 (forallb_forall _ _) H i Hi) as X. apply sv_eqb_sound in X.
  cbn [rho_sub rw]. rewrite X. reflexivity.
Qed.

Lemma OWV6 : ltac2:(tb__ "0|0|
S35S28S116S0S141S3bS118S3bS14bR1A1S25S3bPaaS25S3bPabS25S3bPb1S25S3bPb2S25S3bPb3S25S3bPb4S25S3bPb5S26S3bA1A3A3A3A3A3A3A3A3Li;A1S25S0S97S96A1S25S0S9dS9fA1S25S0S99S9bA1S25S0Sa2S25S0Sa1S9cA1S25S0Sa8Sb3A1S25S0Sa9Sa0A1S26S0A1A3A3A3A3A3A3A3A3S2aA3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FRV6 : ltac2:(tb__ "0|0|
S35S28S13fS3bS118S3bS14bR1A1S25S3bPaaS25S3bPabS25S3bPb1S25S3bPb2S25S3bPb3S25S3bPb4S25S3bPb5S26S3bA1A3A3A3A3A3A3A3A3Li;SbcA2S2aA3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma insK5_vars : ltac2:(tb__ "0|2|
S5cS2eS3aS1S1S3bS117S3bR1S25S3bPaaS25S3bPabS25S3bPb1S25S3bPb2S25S3bPb3S25S3bPb4S25S3bPb5S26S3bA1A3A3A3A3A3A3A3A3S35S4aQ40A1M0S3R3R2A2S3R4R2A2A3F_;Fi;S3bS35S27S4aQ8A1M1A1S1bR3R1A2S1bR4R1A2A3Fl;G0S35S2fG1A1SdR4R1A2SdR5R1A2A3Fa;S6cR8R7R6R5A4S6cR9R8R7R5A4F_;F_;F_;F_;Frho';Frho;FS;Fb;FG;").
Proof.
  intros G b S rho rho' Hv Hl Hm ((A1 & A2 & A3 & A4) & B & C & D & E1 & E2 & F & FR).
  pose proof OWV6 as W. cbn [forallb] in W. apply andb_prop in W as [W1 W]. apply andb_prop in W as [W2 W]. apply andb_prop in W as [W3 W]. apply andb_prop in W as [W4 W].
  apply andb_prop in W as [W5 W]. apply andb_prop in W as [W6 W]. apply andb_prop in W as [W7 _].
  assert (HV : forall v, existsb (Pos.eqb v) [170; 171; 177; 178; 179; 180; 181]%positive = true -> rw rho v = rw rho' v).
  { intros v Hvv. symmetry. apply Hv. apply existsb_exists in Hvv as (x & Hx & Ex). apply Pos.eqb_eq in Ex. subst. exact Hx. }
  assert (RG : forall o, obj_vars_all (fun i => existsb (Pos.eqb i) [170; 171; 177; 178; 179; 180; 181]%positive) o = true -> obj_range rho' o = obj_range rho o).
  { intros o Ho. apply (obj_range_agree_vars _ rho rho' o HV (fun l => eq_sym (Hl l)) Ho). }
  assert (EFR : eval rho' fr_addr = eval rho fr_addr) by (symmetry; apply (eval_agree_vars (fun i => existsb (Pos.eqb i) [170; 171; 177; 178; 179; 180; 181]%positive) rho rho'); [exact HV | intros l; symmetry; apply Hl | exact FRV6]).
  split; [|split; [rewrite (Hv 178%positive ltac:(cbn; tauto)); exact B | split; [rewrite (Hv 179%positive ltac:(cbn; tauto)); exact C | split; [rewrite (Hv 180%positive ltac:(cbn; tauto)); exact D | split; [|split; [|split]]]]]].
  - split; [rewrite (Hv 177%positive ltac:(cbn; tauto)); exact A1|]. split; [rewrite (Hv 170%positive ltac:(cbn; tauto)); exact A2|].
    split; [intros a Ha; apply A3; rewrite <- (RG _ W1); exact Ha | intros a Ha; apply A4; rewrite <- (RG _ W2); exact Ha].
  - eapply (ro_win_vars segsA (fun i => existsb (Pos.eqb i) [170; 171; 177; 178; 179; 180; 181]%positive)); [exact HV | intros l; symmetry; apply Hl | | exact W3 | exact E1].
    intros a. unfold rd_of. rewrite Hm. reflexivity.
  - eapply (ro_win_vars segsA (fun i => existsb (Pos.eqb i) [170; 171; 177; 178; 179; 180; 181]%positive)); [exact HV | intros l; symmetry; apply Hl | | exact W6 | exact E2].
    intros a. unfold rd_of. rewrite Hm. reflexivity.
  - pose proof (Forall_inv F) as F1. pose proof (Forall_inv (Forall_inv_tail F)) as F2. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail F))) as F3.
    pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail F)))) as F4. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail F))))) as F5.
    repeat apply Forall_cons; [| | | | | apply Forall_nil]; intros a Ha;
      [apply F1; rewrite <- (RG _ W3) | apply F2; rewrite <- (RG _ W4) | apply F3; rewrite <- (RG _ W5) | apply F4; rewrite <- (RG _ W6) | apply F5; rewrite <- (RG _ W7)]; exact Ha.
  - intros a Ha. apply FR. rewrite <- EFR. exact Ha.
Qed.

Lemma glue_e2h : ltac2:(tb__ "0|0|
S5cS2eS3aS27S4aQ40A1A1S1S11bS4dS3cS63R6A1VE2r;R2R3R1A6S6cR7R6R5R3A4S37S1S1S36S4dS3cS63R9A1VE2hs;R1R6R4A6S6cR9R8R7R1A4A2Lrho';A2F_;F_;Fw;Frho;Ftp;FS;Fb;FG;").
Proof.
  intros G b S tp rho w H HK5. exists (rho_sub rho sE). split.
  - apply (SPA_entails segsA (JJ G) NPRE E2r E2hs sE rho tp _ ENT_E SID_E (JJ_stable G NPRE ltac:(lia))). exact H.
  - apply (insK5_vars G b S rho); [intros i Hi; apply ids7_rw; [exact IDS_E | exact Hi] | intros l; reflexivity | intros a; reflexivity | exact HK5].
Qed.

Definition R8 : list sobj := ltac2:(tb__ "0|0|
S25S0S97ScbA1S25S0S9dScbA1S25S0S99S9bA1S25S0SdfS25S0Sa1SaaS9cS5S3dVsz;Z1A2A1A2A1S25S0Sa8Sb3A1S25S0Sc5Vsz;A1S25S0Sa9S9Pc5A1A1S26S0A1A3A3A3A3A3A3A3A3").
Definition E7 : list sobj := ltac2:(tb__ "0|0|
S29S0S25S0S138S25S0Sa3S26S0A1A3A3S29S0S137Sa4A3A3").

Lemma XE_objs : ltac2:(tb__ "0|0|
S35S27S0A1S6S51SbbVsz;A1A1A1S29S0S88S8eA3A3").
Proof. reflexivity. Qed.

Lemma FD_below : ltac2:(tb__ "0|0|
S35S28S116S4S10SddA1S9eA3S2aA3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma OW8 : ltac2:(tb__ "0|0|
S35S28S116S0S14S95A1S25S0S97S96A1S25S0S9dS9fA1S25S0S99S9bA1S25S0Sa2S25S0Sa1S9cA1S25S0Sa8Sb3A1S25S0Sa9Sa0A1S26S0A1A3A3A3A3A3A3A3A3S2aA3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma bucket_index : ltac2:(tb__ "0|0|
S1S112S4S1aR1A1Sa5A3S37S3aS3aS36S36S3eZ0R1A2S3fR1S10dA2A2S35S3aS49Q40S3R3PabA2A2S3dS104S43Z4R1A2A2A3A2Li;A2F_;Frho;").
Proof.
  intros rho HF. unfold F_tw in HF.
  pose proof (proj1 (Forall_forall _ _) HF (SPAlign 171%positive 2) ltac:(cbn; tauto)) as A.
  pose proof (proj1 (Forall_forall _ _) HF (SPUle (SLit DEPOT) vP) ltac:(cbn; tauto)) as B.
  pose proof (proj1 (Forall_forall _ _) HF (SPUle vP (SLit (DEPOT + 4 * 2^20 - 4))) ltac:(cbn; tauto)) as C.
  cbn [holds eval vP] in A, B, C. unfold DEPOT, TABSZ in *. rewrite u64_lit in B by lia. rewrite u64_lit in C by lia.
  destruct A as [_ A]. change (2 ^ 2) with 4 in A.
  exists ((bv_unsigned (rw rho 171%positive) - 1900440) / 4).
  pose proof (Z.div_mod (bv_unsigned (rw rho 171%positive)) 4 ltac:(lia)) as DM.
  split; [split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia] |].
  pose proof (Z.div_mod (bv_unsigned (rw rho 171%positive) - 1900440) 4 ltac:(lia)) as DM2.
  assert ((bv_unsigned (rw rho 171%positive) - 1900440) mod 4 = 0).
  { rewrite Zminus_mod, A. reflexivity. }
  lia.
Qed.

Definition ids_ok (s : wsub) : bool := ltac2:(tb__ "0|0|
S116S3bS3bS1cS13bVs;R1A2S9R1A1A2Li;S25S3bPaaS25S3bPabS25S3bPb1S25S3bPb2S25S3bPb3S25S3bPb4S26S3bA1A3A3A3A3A3A3A3").

Lemma ids_ok_rw : ltac2:(tb__ "0|0|
S13cS1S3bS35S28S86R3A1S2aA3S117S3bR2S25S3bPaaS25S3bPabS25S3bPb1S25S3bPb2S25S3bPb3S25S3bPb4S26S3bA1A3A3A3A3A3A3A3S35S4aQ40A1S3S13dR4R5A2R3A2S3R4R3A2A3F_;F_;Fi;Frho;Fs;").
Proof.
  intros s rho i H Hi. unfold ids_ok in H. pose proof (proj1 (forallb_forall _ _) H i Hi) as X. apply sv_eqb_sound in X.
  cbn [rho_sub rw]. rewrite X. reflexivity.
Qed.

Definition ids_objs (s : wsub) : bool := ltac2:(tb__ "0|0|
S116S0S141S3bS1cS13bVs;R1A2S9R1A1A2Li;A1S25S0S97S96A1S25S0S9dS9fA1S25S0S99S9bA1S25S0Sa2S25S0Sa1S9cA1S25S0Sa8Sb3A1S25S0Sa9Sa0A1S26S0A1A3A3A3A3A3A3A3A3").

Lemma xe_exit_gen : ltac2:(tb__ "0|5|
S55S13cS35S28S54R2SbbVsz;A1R1A3S2aA3S35S28S13aR2S98A2S2aA3S35S28S86R3A1S2aA3S35S28S94R4A1S2aA3S5cS3aS27S4aQ40A1M0A1M1S2eS1S1S11bS4dS3cS63R7A1RdR2R5R1A6SbS95R4R3A3S6cR9R6R8R5A4S66RaR9A2S119S42S40S3dS5dRbA1Z1M2A2Z10000A2A1S2dS3aS60RbA1A2A2S35S2eR9S42S40RbZ100000M3A2A1A3S119RaS2dS3aS5eRdA1A2A2S3fS3dS41RdG3A2Vsz;A2G3A2S3eS43Z8S3dS3dS41ReG3A2Vsz;A2G2A2A2S43S120S114S3aRcS61RfA1Z0A4A2A2S35S3aS5dR10A1S5dVG0;A1A3S35S3aS5fR11A1S5fVG0;A1A3S37S27S3aA1M4G4S35G4S60R13A1S29S3aS60VG0;A1R1A3A3Ll;A2S37G4G4S35G4S5eR14A1S29S3aS5eVG0;A1R1A3A3Ll;A2S3eSf5R14A1S3dSf5VG0;A1Sf6VG0;A1A2A2S3aSfeVG0;R1A2SfeR17R2A2F_;Fa;S37G1G1S35G1R15S29G0R1Vtp0;A3A3Ll;A2S64R11A1F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fw;FrhoL;FrhoI;Fb;Ftp;FS;FG;F_;F_;F_;F_;Fs;FLs;").
Proof.
  intros Ls s ENT SID IDS IDSO G S tp b rhoI rhoL w H Hag HK5 HHS HjN Hb Hbl Hns Hpaid EdN EdF EdNB EdFB Hcost HFPw Htp.
  destruct w as [tr [ms md]]. pose proof Hsz as HszB. unfold SZMAXT in HszB.

  assert (H1 : SPA segsA (JJ G) (XE sz) (rho_sub rhoL s) tp (tr, mkCfg ms md)).
  { apply (SPA_entails segsA (JJ G) NPRE Ls (XE sz) s rhoL tp _ ENT SID (JJ_stable G NPRE ltac:(lia))). exact H. }
  set (rhoE := rho_sub rhoL s) in *.
  pose proof H1 as [HsmA [HREL [HKG [[HM HV] _]]]]. cbn [w_tr w_cfg fst snd cfg_model] in HKG, HV.
  pose proof (proj1 HsmA) as Hsm. unfold virt in Hsm. cbn [fst snd cfg_ms cfg_model w_tr w_cfg] in Hsm.
  pose proof (SPA_facts segsA _ _ _ _ _ H1) as HF. cbn [ax_S XE mkA ss_facts] in HF. unfold FXE in HF.
  apply Forall_app in HF as [HFD HF]. apply Forall_app in HF as [HFt HF]. apply Forall_app in HF as [HFn HF]. apply Forall_app in HF as [HFnb HFe].

  destruct Hag as (Hagw & Hagl & Hagm).
  assert (EV : forall i, In i [170; 171; 177; 178; 179; 180]%positive -> rw rhoE i = rw rhoI i).
  { intros i Hi. unfold rhoE. rewrite (ids_ok_rw s rhoL i IDS Hi). symmetry. apply Hagw. cbn in Hi. unfold NXD. lia. }
  destruct HK5 as ((K177 & K170 & KD1 & KD2) & K178 & K179 & K180 & ROs & ROd & WD5 & WDfr).
  rewrite <- (EV 177%positive ltac:(cbn; tauto)) in K177. rewrite <- (EV 170%positive ltac:(cbn; tauto)) in K170.
  rewrite <- (EV 178%positive ltac:(cbn; tauto)) in K178. rewrite <- (EV 179%positive ltac:(cbn; tauto)) in K179. rewrite <- (EV 180%positive ltac:(cbn; tauto)) in K180.
  pose proof (dm_N _ _ HM) as [HN _]. pose proof (dm_F _ _ HM) as (HF0 & HF11 & HF32 & _).
  destruct (kd_room segsA K NPRE HKD G rhoE tp _ _ HKG (conj HM HV)) as [_ HDN].
  set (jN := Z.to_nat ((dN G + 1) / 65536)) in *. set (blkN := nth jN (dNB G) 0) in *.
  assert (HinN : In blkN (dNB G)) by (unfold blkN; apply nth_In; exact HjN).
  destruct (dm_nb _ _ HM blkN HinN) as (NBal & NBlo & NBhi & NBpres).
  pose proof (nb_top _ _ _ _ _ _ _ HKG HV HinN) as NBhiT.
  set (F := dF G) in *. set (fb := nth b (dFB G) 0) in *.
  destruct (HS_bounds G S HHS HF0 HF32) as [HSF HS32]. fold F in HSF.
  assert (HbZ : Z.of_nat b = S / 1048576) by (subst b; rewrite Z2Nat.id by (apply Z.div_pos; lia); reflexivity).
  destruct (dm_fbases _ _ HM fb (nth_In _ _ Hbl)) as (FBal & FBlo & FBhi).
  pose proof (fb_top _ _ _ _ _ _ fb HKG HV (nth_In _ _ Hbl)) as FBhiT.
  pose proof (Z.mod_pos_bound S 1048576 ltac:(lia)) as MB. pose proof (Z.mod_pos_bound (dN G + 1) 65536 ltac:(lia)) as MBN.
  pose proof alloc_ceiling_valD as ACV.
  destruct (bucket_index rhoE HFt) as (i & Hi & U171).
  assert (NNA : bv_unsigned (eval rhoE nn_addr) = blkN + 16 * ((dN G + 1) mod 65536)).
  { rewrite (nn_addr_val rhoE (dN G)); [rewrite K178; reflexivity | exact K177 | unfold DNMAX in HDN; lia | rewrite K178; exact NBhi]. }
  assert (Ena : SegD_wf.node_addr G (dN G + 1) = blkN + 16 * ((dN G + 1) mod 65536)) by reflexivity.
  assert (BDA : bv_unsigned (eval rhoE bd_addr) = STORE + 16 * Z.of_nat b) by (rewrite HbZ; apply bd_addr_val; [exact K179 | lia]).
  assert (FRA : bv_unsigned (eval rhoE fr_addr) = fb + 8 * (S mod 1048576)).
  { rewrite <- K180. apply fr_addr_val; [exact K179 | lia | rewrite K180; exact FBhi]. }
  assert (STA : bv_unsigned (eval rhoE stc_addr) = STORE + 16 * Z.of_nat b) by (rewrite HbZ; apply stc_addr_val; [exact K179 | lia]).
  assert (SNA : bv_unsigned (eval rhoE slotN_addr) = MAP1 + 8 * ((dN G + 1) / 65536)) by (apply slotN_addr_val; [exact K177 | unfold DNMAX in HDN; lia]).
  assert (Hj15 : 0 <= (dN G + 1) / 65536 < 2 ^ 15) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; unfold DNMAX in HDN; lia]).
  pose proof (fblk_lt F ltac:(lia) ltac:(lia)) as FBL. pose proof (dm_fb_len _ _ HM) as [FBlen _].
  assert (Hb4096 : Z.of_nat b < 4096) by lia.
  assert (EidN : eval rhoE idN = Z_to_bv 64 (dN G + 1)).
  { apply bv_eq. unfold idN, add, vN. cbn [eval]. rewrite add_val, K177, !u64_lit by lia. rewrite Z.mod_small by lia. reflexivity. }
  assert (EtF : eval rhoE (add vF (SLit (sz + 1))) = Z_to_bv 64 (S + sz + 1)).
  { apply bv_eq. unfold add, vF. cbn [eval]. rewrite add_val, K179, !u64_lit by lia. rewrite Z.mod_small by lia. lia. }

  set (R := R8). set (rho' := rho_absorb rhoE R (vms md tp ms)).
  pose proof (SPA_unobj segsA (fun _ _ _ _ => True) rhoE (XE sz) E7 R tp tr ms md XE_objs (conj HsmA I) (fun _ => I)) as [HsmA' _].

  assert (RG : forall o, In o R -> exists lo hi, obj_range rhoE o = (lo, hi) /\
            ((o = O_slotN vNB /\ lo = MAP1 + 8 * ((dN G + 1) / 65536) /\ hi = lo + 8)
             \/ (o = O_bd vD /\ lo = STORE + 16 * Z.of_nat b + 16 /\ hi = lo + 8)
             \/ (ins_written G i b sz S lo /\ (forall z, lo <= z < hi -> ins_written G i b sz S z) /\ DFPw G lo /\ (forall z, lo <= z < hi -> DFPw G z /\ DFP G z)))).
  { intros o Ho. unfold R, R8 in Ho.
    unfold ins_written, DFPw, DFP, dfp_static, in_blk. rewrite Ena. fold F. fold fb.
    pose proof (Z.mod_pos_bound (dN G + 1) 65536 ltac:(lia)).
    unfold DEPOT, TABSZ, NIDS, MAP1, MAP1N, STORE, NFBLK, NBSZ, FBSZ, PG, IMG_HI in *.
    destruct Ho as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]].
    - exists (bv_unsigned (rw rhoE 171%positive)), (bv_unsigned (rw rhoE 171%positive) + 4). split; [unfold O_tw, carved; rewrite obj_range_mk by lia; cbn [eval vP]; f_equal; lia|].
      right; right. rewrite U171. split; [lia|]. split; [intros z Hz; lia|]. split; [lia|]. intros z Hz; lia.
    - exists 6094744, (6094744 + 4). split; [unfold O_nid, carved, NIDS; rewrite obj_range_mk by lia; cbn [eval]; rewrite u64_lit by lia; f_equal; lia|].
      right; right. split; [lia|]. split; [intros z Hz; lia|]. split; [lia|]. intros z Hz; lia.
    - exists (1900440 + 4194320 + 8 * ((dN G + 1) / 65536)), (1900440 + 4194320 + 8 * ((dN G + 1) / 65536) + 8). split; [unfold O_slotN, carved; rewrite obj_range_mk by lia; cbn [fst snd]; rewrite SNA; f_equal; lia|].
      left. split; [reflexivity|]. lia.
    - exists (blkN + 16 * ((dN G + 1) mod 65536)), (blkN + 16 * ((dN G + 1) mod 65536) + 16). split; [unfold O_nnE, carved; rewrite obj_range_mk by lia; cbn [fst snd]; rewrite NNA; f_equal; lia|].
      right; right. split; [lia|]. split; [intros z Hz; lia|]. split; [right; left; exists blkN; split; [exact HinN|lia]|]. intros z Hz. split; right; left; exists blkN; split; [exact HinN|lia|exact HinN|lia].
    - exists 1834888, (1834888 + 8). split; [unfold O_tf, carved, STORE; rewrite obj_range_mk by lia; cbn [eval]; rewrite u64_lit by lia; f_equal; lia|].
      right; right. split; [lia|]. split; [intros z Hz; lia|]. split; [lia|]. intros z Hz; lia.
    - exists (1834888 + 16 * Z.of_nat b + 16), (1834888 + 16 * Z.of_nat b + 16 + 8). split; [unfold O_bd, carved; rewrite obj_range_mk by lia; cbn [fst snd]; rewrite BDA; f_equal; lia|].
      right; left. split; [reflexivity|]. lia.
    - exists (fb + 8 * (S mod 1048576)), (fb + 8 * (S mod 1048576) + 8 * (sz + 1)). split; [unfold O_fr, carved; rewrite obj_range_mk by lia; cbn [fst snd]; rewrite FRA; f_equal; lia|].
      right; right. split; [lia|]. split; [intros z Hz; lia|].
      assert (BF : forall z, fb + 8 * (S mod 1048576) <= z < fb + 8 * (S mod 1048576) + 8 * (sz + 1) -> exists b1, In b1 (dFB G) /\ b1 <= z < b1 + 8388608).
      { intros z Hz. exists fb. split; [apply nth_In; exact Hbl | unfold FBPAGES in *; lia]. }
      split; [right; right; apply BF; lia|]. intros z Hz. split; right; right; apply BF; lia.
    - exists (1834888 + 16 * Z.of_nat b + 24), (1834888 + 16 * Z.of_nat b + 28). split; [unfold O_stc, carved; rewrite obj_range_mk by lia; cbn [fst snd]; rewrite STA; f_equal; lia|].
      right; right. split; [lia|]. split; [intros z Hz; lia|]. split; [lia|]. intros z Hz; lia. }

  pose proof OW8 as OW. cbn [forallb] in OW. repeat (apply andb_prop in OW as [?OWx OW]).
  pose proof IDSO as IO. unfold ids_objs in IO. cbn [forallb] in IO. repeat (apply andb_prop in IO as [?IOx IO]).
  assert (TRro : forall o, obj_wf NXD o = true -> obj_vars_all (fun i0 => sv_eqb (wsub_get s i0) (SVar i0)) o = true ->
            ro_win segsA rhoI o -> ro_win segsA rhoE o).
  { intros o Hwf Hvs Hro. apply (ro_win_vars segsA (fun i0 => sv_eqb (wsub_get s i0) (SVar i0)) rhoL rhoE).
    - intros v Hv. apply sv_eqb_sound in Hv. unfold rhoE. cbn [rho_sub rw]. rewrite Hv. reflexivity.
    - intros l. reflexivity.
    - intros a. reflexivity.
    - exact Hvs.
    - eapply ro_win_agree; [split; [exact Hagw | split; [exact Hagl | exact Hagm]] | exact Hwf | exact Hro]. }
  assert (TRrange : forall o, obj_wf NXD o = true -> obj_vars_all (fun i0 => sv_eqb (wsub_get s i0) (SVar i0)) o = true ->
            obj_range rhoE o = obj_range rhoI o).
  { intros o Hwf Hvs. rewrite <- (obj_range_agree NXD rhoI rhoL o ltac:(split; [exact Hagw | split; [exact Hagl | exact Hagm]]) Hwf).
    apply (obj_range_agree_vars (fun i0 => sv_eqb (wsub_get s i0) (SVar i0)) rhoL rhoE o); [| intros l; reflexivity | exact Hvs].
    intros v Hv. apply sv_eqb_sound in Hv. unfold rhoE. cbn [rho_sub rw]. rewrite Hv. reflexivity. }
  pose proof (TRro _ OWx1 IOx1 ROs) as ROsE. pose proof (TRro _ OWx4 IOx4 ROd) as ROdE.

  assert (InS : In (O_slotN vNB) R) by (unfold R, R8; cbn; tauto).
  assert (InD : In (O_bd vD) R) by (unfold R, R8; cbn; tauto).
  pose proof (absorb_view_ro segsA rhoE (ax_S (XE sz)) tr (vms md tp ms) (vmd md) E7 R _ Hsm XE_objs InS ROsE) as VS.
  pose proof (absorb_view_ro segsA rhoE (ax_S (XE sz)) tr (vms md tp ms) (vmd md) E7 R _ Hsm XE_objs InD ROdE) as VD. fold rho' in VS, VD.
  assert (VOUT : forall a, ~ in_ranges rhoE R a -> rm rho' a = rm rhoE a) by (intros a Ha; unfold rho'; apply rm_absorb_out; exact Ha).
  unfold SZMAXT in *.
  assert (CIVtw := absorb_view_cells segsA rhoE (ax_S (XE sz)) tr (vms md tp ms) (vmd md) E7 R vP 0 4 [(0, 4%nat, idN)] Hsm XE_objs
                    ltac:(unfold R, R8; cbn; tauto) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold cells_inside; constructor; [cbn; lia|constructor])
                    ltac:(cbn [eval vP]; rewrite U171; unfold DEPOT; lia) ltac:(cbn [eval vP]; rewrite U171; unfold DEPOT, TABSZ in *; lia)).
  assert (CIVni := absorb_view_cells segsA rhoE (ax_S (XE sz)) tr (vms md tp ms) (vmd md) E7 R (SLit 0) NIDS (NIDS + 4) [(NIDS, 4%nat, idN)] Hsm XE_objs
                    ltac:(unfold R, R8; cbn; tauto) ltac:(unfold NIDS; lia) ltac:(lia) ltac:(unfold NIDS; lia) ltac:(unfold cells_inside; constructor; [cbn; lia|constructor])
                    ltac:(cbn [eval]; rewrite u64_lit by lia; unfold NIDS; lia) ltac:(cbn [eval]; rewrite u64_lit by lia; unfold NIDS; lia)).
  assert (CIVnn := absorb_view_cells segsA rhoE (ax_S (XE sz)) tr (vms md tp ms) (vmd md) E7 R nn_addr 0 16 [(0, 8%nat, vHS); (8, 4%nat, vW); (12, 4%nat, SVar 195)] Hsm XE_objs
                    ltac:(unfold R, R8; cbn; tauto) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold cells_inside; repeat constructor; cbn; lia)
                    ltac:(rewrite NNA; unfold IMG_HI in *; lia) ltac:(rewrite NNA; unfold NBSZ in *; lia)).
  assert (CIVtf := absorb_view_cells segsA rhoE (ax_S (XE sz)) tr (vms md tp ms) (vmd md) E7 R (SLit 0) STORE (STORE + 8) [(STORE, 8%nat, add vF (SLit (sz + 1)))] Hsm XE_objs
                    ltac:(unfold R, R8; cbn; tauto) ltac:(unfold STORE; lia) ltac:(lia) ltac:(unfold STORE; lia) ltac:(unfold cells_inside; constructor; [cbn; lia|constructor])
                    ltac:(cbn [eval]; rewrite u64_lit by lia; unfold STORE; lia) ltac:(cbn [eval]; rewrite u64_lit by lia; unfold STORE; lia)).
  assert (CIVfr := absorb_view_cells segsA rhoE (ax_S (XE sz)) tr (vms md tp ms) (vmd md) E7 R fr_addr 0 (8 * (sz + 1)) [] Hsm XE_objs
                    ltac:(unfold R, R8; cbn; tauto) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold cells_inside; constructor)
                    ltac:(rewrite FRA; unfold IMG_HI in *; lia) ltac:(rewrite FRA; unfold FBSZ, PG, FBPAGES in *; lia)).
  assert (CIVst := absorb_view_cells segsA rhoE (ax_S (XE sz)) tr (vms md tp ms) (vmd md) E7 R stc_addr 24 28 [(24, 4%nat, SVar 197)] Hsm XE_objs
                    ltac:(unfold R, R8; cbn; tauto) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold cells_inside; constructor; [cbn; lia|constructor])
                    ltac:(rewrite STA; unfold STORE; lia) ltac:(rewrite STA; unfold STORE; lia)).
  fold rho' in CIVtw, CIVni, CIVnn, CIVtf, CIVfr, CIVst.
  cbn [eval vP] in CIVtw. rewrite U171 in CIVtw. cbn [eval] in CIVni, CIVtf. rewrite u64_lit in CIVni by lia. rewrite u64_lit in CIVtf by lia.
  rewrite NNA in CIVnn. rewrite FRA in CIVfr. rewrite STA in CIVst.
  destruct CIVtw as [Ctw _]. destruct CIVni as [Cni _]. destruct CIVnn as [Cnn Pnn]. destruct CIVtf as [Ctf _]. destruct CIVfr as [_ Pfr]. destruct CIVst as [Cst Pst].

  assert (Hsame : forall z, ~ ins_written G i b sz S z -> view segsA (rm rho') z = view segsA (rm rhoE) z).
  { intros z Hnw. destruct (Z_lt_le_dec z 0) as [Zn|Z0]; [unfold view; destruct (Z.leb_spec 0 z); [lia|reflexivity]|].
    destruct (Z_lt_le_dec z (2 ^ 64)) as [Z1|Z2]; [|unfold view; destruct (Z.ltb_spec z (2 ^ 64)); [lia|]; rewrite andb_false_r; reflexivity].
    destruct (in_ranges_dec rhoE R (Z_to_bv 64 z)) as [Hin|Hout].
    - destruct Hin as (o & HoR & Hrng). rewrite u64_lit in Hrng by lia. destruct (RG o HoR) as (lo & hi & Er & CS). rewrite Er in Hrng. cbn [fst snd] in Hrng.
      destruct CS as [(-> & Elo & Ehi)|[(-> & Elo & Ehi)|(W1 & W2 & _)]].
      + apply VS. rewrite Er. cbn [fst snd]. lia.
      + apply VD. rewrite Er. cbn [fst snd]. lia.
      + exfalso. exact (Hnw (W2 z Hrng)).
    - rewrite !view_in by lia. unfold rd_of. rewrite (VOUT _ Hout). reflexivity. }

  set (G' := G_ins G (S + sz + 1)).
  assert (PRsub : forall (m0 : bview) lo hi lo' hi', present m0 lo hi -> lo <= lo' -> hi' <= hi -> present m0 lo' hi') by (intros m0 lo hi lo' hi' Hp H1' H2' z Hz; apply Hp; lia).
  assert (HM' : depot_mem G' (view segsA (rm rho'))).
  { unfold G'. assert (Hsz' : 1 <= sz <= 30) by lia. assert (Htol' : sz <= 10 \/ dN G <= KMAX + 1) by (rewrite EdN; exact Htol).
    apply (depot_mem_insert G (view segsA (rm rhoE)) (view segsA (rm rho')) sz b i (bv_unsigned (eval rhoE vHS)) S HM Hsz' Htol' HDN HHS Hb Hbl Hns Hpaid HjN Hi Hsame).
    - intros j Hj. cbn [c_addr c_w RtCells.c_val]. rewrite <- EidN. replace (DEPOT + 4 * i + Z.of_nat j) with (DEPOT + 4 * i + 0 + Z.of_nat j) by lia. apply (Ctw 0 4%nat idN j); [left; reflexivity | exact Hj].
    - intros j Hj. cbn [c_addr c_w RtCells.c_val]. rewrite <- EidN. replace (NIDS + Z.of_nat j) with (0 + NIDS + Z.of_nat j) by lia. apply (Cni NIDS 4%nat idN j); [left; reflexivity | exact Hj].
    - intros j Hj. cbn [c_addr c_w RtCells.c_val]. rewrite Z_to_bv_bv_unsigned. rewrite Ena. replace (blkN + 16 * ((dN G + 1) mod 65536) + Z.of_nat j) with (blkN + 16 * ((dN G + 1) mod 65536) + 0 + Z.of_nat j) by lia.
      apply (Cnn 0 8%nat vHS j); [cbn; tauto | exact Hj].
    - exists (bv_unsigned (rw rhoE 170%positive)). split; [|pose proof (urange (rw rhoE 170%positive)); lia].
      intros j Hj. cbn [c_addr c_w RtCells.c_val]. rewrite Z_to_bv_bv_unsigned. rewrite Ena.
      change (rw rhoE 170%positive) with (eval rhoE vW). apply (Cnn 8 4%nat vW j); [cbn; tauto | exact Hj].
    - rewrite Ena. eapply PRsub; [exact Pnn | lia | lia].
    - intros j Hj. cbn [c_addr c_w RtCells.c_val]. rewrite <- EtF. replace (STORE + Z.of_nat j) with (0 + STORE + Z.of_nat j) by lia.
      apply (Ctf STORE 8%nat (add vF (SLit (sz + 1))) j); [left; reflexivity | exact Hj].
    - eapply PRsub; [exact Pst | lia | lia].
    - eapply PRsub; [exact Pfr | unfold fb; lia | unfold fb; lia]. }

  assert (Hvw : forall z, ~ DFPw G z -> view segsA (rm rho') z = view segsA (rm rhoE) z).
  { intros z Hnw. destruct (Z_lt_le_dec z 0) as [Zn|Z0]; [unfold view; destruct (Z.leb_spec 0 z); [lia|reflexivity]|].
    destruct (Z_lt_le_dec z (2 ^ 64)) as [Z1|Z2]; [|unfold view; destruct (Z.ltb_spec z (2 ^ 64)); [lia|]; rewrite andb_false_r; reflexivity].
    destruct (in_ranges_dec rhoE R (Z_to_bv 64 z)) as [Hin|Hout].
    - destruct Hin as (o & HoR & Hrng). rewrite u64_lit in Hrng by lia. destruct (RG o HoR) as (lo & hi & Er & CS). rewrite Er in Hrng. cbn [fst snd] in Hrng.
      destruct CS as [(-> & Elo & Ehi)|[(-> & Elo & Ehi)|(W1 & W2 & W3 & W4)]].
      + apply VS. rewrite Er. cbn [fst snd]. lia.
      + apply VD. rewrite Er. cbn [fst snd]. lia.
      + exfalso. exact (Hnw (proj1 (W4 z Hrng))).
    - rewrite !view_in by lia. unfold rd_of. rewrite (VOUT _ Hout). reflexivity. }

  assert (HRin : forall a, in_ranges rhoE R a -> DFP G (bv_unsigned a)).
  { intros a (o & HoR & Hrng). destruct (RG o HoR) as (lo & hi & Er & CS). rewrite Er in Hrng. cbn [fst snd] in Hrng.
    destruct CS as [(-> & Elo & Ehi)|[(-> & Elo & Ehi)|(W1 & W2 & W3 & W4)]].
    - left. left. unfold DEPOT, MAP1, MAP1N in *. lia.
    - left. right. unfold STORE, NFBLK in *. lia.
    - exact (proj2 (W4 _ Hrng)). }

  assert (HK' : K G' rho' tp tr md).
  { apply (kd_view segsA K NPRE HKD G' rhoE rho' tp tr md); [intros i0; reflexivity | intros l; reflexivity | |].
    - intros z Hz. apply Hvw. intros X. apply Hz. unfold G'. exact X.
    - apply (kd_trans segsA K NPRE HKD G tp md G' tp md rhoE tr); [|exact HKG].
      pose proof (dm_F_coarse _ _ HM') as FN'. unfold G' in FN' |- *. cbn [dN dF G_ins] in FN'. apply DT_ins; lia. }
  assert (HJ' : JJ G' rho' tp tr md).
  { unfold JJ, JJ2, withGA. destruct HREL as (R1 & R2 & R3). split; [|split; [exact HK' | split; [split; [exact HM' | apply depot_vm_G_ins; exact HV] | exact I]]].
    split; [exact R1|]. split.
    - intros a Ha. unfold rho'. rewrite rm_absorb_out; [apply R2; unfold G' in Ha; exact Ha|]. intros Hin. apply Ha. unfold G'. exact (HRin a Hin).
    - intros z Hz. rewrite Hvw by (unfold G' in Hz; exact Hz). apply R3. unfold G' in Hz. exact Hz. }
  assert (H2 : SPA segsA (JJ G') (ax_setS (XE sz) (set_objs (ax_S (XE sz)) E7)) rho' tp (tr, mkCfg ms md)) by (split; [exact HsmA' | exact HJ']).

  assert (H3 : SPA segsA (JJ G') (PostD sz) rho' tp (tr, mkCfg ms md)).
  { pose proof (SPA_refacts segsA (JJ G') rho' _ F_D tp _ H2 FD_below) as X.
    apply X. cbn [ax_S ax_setS set_objs ss_facts XE mkA]. intros HFX. unfold FXE in HFX. apply Forall_app in HFX as [Y _]. exact Y. }

  unfold QD. destruct HREL as (R1 & R2 & R3).
  eapply (LQPA_intro segsA NPRE rho0 tp0 _ (PostD sz) (JLD segsA K G0) rho' tp _ (JJ G')); [left; reflexivity | exact H3 | exact R1 |].
  intros _. exists G'. split; [exact HK'|]. split; [split; [exact HM' | apply depot_vm_G_ins; exact HV]|].
  split.
  { unfold dpost, G'. cbn [dN dF dNB dFB dFP G_ins]. rewrite EdN. fold F. fold F in EdF. destruct EdNB as [lN ElN]. destruct EdFB as [lF ElF]. pose proof Hsz.
    split; [right; reflexivity|]. split; [lia|]. split; [exists lN; exact ElN|]. split; [exists lF; exact ElF|].
    split; [|intros a Ha; apply HFPw; exact Ha].
    unfold dep_cost, dep_pages in Hcost |- *. cbn [dNB dFP G_ins]. lia. }
  split; [| split; [| split]].
  - intros a Ha. unfold rho'. rewrite rm_absorb_out; [apply R2; unfold G' in Ha; exact Ha|]. intros Hin. apply Ha. unfold G'. exact (HRin a Hin).
  - intros z Hz. rewrite Hvw by (unfold G' in Hz; exact Hz). apply R3. unfold G' in Hz. exact Hz.
  - intros l. symmetry. apply (proj2 R1).
  - exact Htp.
Qed.

Variables XAs XBs : axst.
Variables sXA sXB : wsub.
Hypothesis RUNE2 : ltac2:(tb__ "0|0|
S35S27S52A1S9aU5dcS25S3aSb2S26S3aA1A3VE2hs;A3S25S52S53VXAs;S126A2S25S52S53VXBs;S126A2S26S52A1A3A3A3").
Hypothesis ENT_XA : ltac2:(tb__ "0|0|
S35S28S54VXAs;SbbVsz;A1VsXA;A3S2aA3").
Hypothesis SID_XA : ltac2:(tb__ "0|0|
S35S28S13aVsXA;S98A2S2aA3").
Hypothesis IDS_XA : ids_ok sXA = true.
Hypothesis IDSO_XA : ids_objs sXA = true.
Hypothesis ENT_XB : ltac2:(tb__ "0|0|
S35S28S54VXBs;SbbVsz;A1VsXB;A3S2aA3").
Hypothesis SID_XB : ltac2:(tb__ "0|0|
S35S28S13aVsXB;S98A2S2aA3").
Hypothesis IDS_XB : ids_ok sXB = true.
Hypothesis IDSO_XB : ids_objs sXB = true.

Definition arm_e (G : DG) (S : Z) : Prop := ltac2:(tb__ "0|3|
S36S119S42S40VS;Z100000M0A2A1M1S2dS3aS5eVG;A1A2A2S36S3fS3dS41VS;G0A2Vsz;A2M2G0A2S3eS43Z8S3dG2Z1A2A2S43S120S114S3aG1S61VG;A1Z0A4A2A2A2A2").

Definition gmid (G : DG) (tp : list word) : Prop := ltac2:(tb__ "0|3|
S36S35S3aS5dVG;A1S5dVG0;A1A3S36S35S3aS5fVG;A1S5fVG0;A1A3S36S37S27S3aA1M0G0S35G0S60VG;A1S29S3aS60VG0;A1R1A3A3Ll;A2S36S37G0G0S35G0S5eVG;A1S29S3aS5eVG0;A1R1A3A3Ll;A2S36S3eSf5VG;A1S3dSf5VG0;A1Sf6VG0;A1A2A2S36S3aSfeVG0;R1A2SfeVG;R2A2F_;Fa;S37S27S4aQ40A1M1A1M2G2S35G2Vtp;S29G1R1Vtp0;A3A3Ll;A2A2A2A2A2A2A2").

Lemma gmid_refl : gmid G0 tp0.
Proof.
  unfold gmid. split; [reflexivity|]. split; [lia|]. split; [exists []; symmetry; apply app_nil_r|]. split; [exists []; symmetry; apply app_nil_r|].
  split; [unfold droom, PG, NBSZ; destruct ((dN G0 + 1) mod 65536 =? 0); lia|].
  split; [intros a H; exact H | exists []; reflexivity].
Qed.

Lemma agree_below_le : ltac2:(tb__ "0|0|
S3bS3bS1S1S14aR3R4A2SbR5R3R2A3SbR5R4R3A3F_;F_;Frho';Frho;Fm;Fn;").
Proof. intros n m rho rho' Hmn (A & B & C). split; [intros i Hi; apply A; lia | split; [exact B | exact C]]. Qed.

Lemma e2_cont : ltac2:(tb__ "0|0|
S5cS3aS27S4aQ40A1A1S1S65R4R2A2S6cR5S42S40R4Z100000A2A1R4R2A4S66R6R5A2S119S42S40S3dS5dR7A1Z1A2Z10000A2A1S2dS3aS60R7A1A2A2S74R8R7A2S11dS3cVok;S4dS3cS63R9A1VE2hs;R6R7A5S64A4F_;F_;F_;F_;F_;Frho;Ftp;FS;FG;").
Proof.
  intros G S tp rho (M1 & M2 & M3 & M4 & M5 & M6 & M7) HK5 HHS HjN (A1 & A2 & A3).
  apply triple1_triple.
  eapply (stage_run (JJ G)); [apply JJ_ok | apply JJ_stable; lia | exact RUNE2 | discriminate | exact E2_len | rewrite E2_nx; apply Pos.leb_le; reflexivity |].
  intros L rhoL [<-|[<-|[]]] Hag; cbn [la_state]; rewrite E2_nx in Hag.
  + eapply triple_conseq; [| intros w Hw; exact Hw | apply triple_refl]. intros w Hw.
    exact (xe_exit_gen XAs sXA ENT_XA SID_XA IDS_XA IDSO_XA G S tp _ rho rhoL w Hw Hag HK5 HHS HjN eq_refl A1 A2 A3 M1 M2 M3 M4 M5 M6 M7).
  + eapply triple_conseq; [| intros w Hw; exact Hw | apply triple_refl]. intros w Hw.
    exact (xe_exit_gen XBs sXB ENT_XB SID_XB IDS_XB IDSO_XB G S tp _ rho rhoL w Hw Hag HK5 HHS HjN eq_refl A1 A2 A3 M1 M2 M3 M4 M5 M6 M7).
Qed.

Lemma ee2_cont : ltac2:(tb__ "0|0|
S5cS3aS27S4aQ40A1A1S1S65R4R2A2S6cR5S42S40R4Z100000A2A1R4R2A4S66R6R5A2S119S42S40S3dS5dR7A1Z1A2Z10000A2A1S2dS3aS60R7A1A2A2S74R8R7A2S11cS3cS4dS3cS63R9A1VE2hs;R6R7A5S64A3F_;F_;F_;F_;F_;Frho;Ftp;FS;FG;").
Proof.
  intros G S tp rho (M1 & M2 & M3 & M4 & M5 & M6 & M7) HK5 HHS HjN (A1 & A2 & A3).
  eapply (estage_run (JJ G)); [apply JJ_stable; lia | exact RUNE2 | discriminate | exact E2_len | rewrite E2_nx; apply Pos.leb_le; reflexivity |].
  intros L rhoL [<-|[<-|[]]] Hag; cbn [la_state]; rewrite E2_nx in Hag.
  + eapply etriple_conseq; [| intros w Hw; exact Hw | apply etriple_refl]. intros w Hw.
    exact (xe_exit_gen XAs sXA ENT_XA SID_XA IDS_XA IDSO_XA G S tp _ rho rhoL w Hw Hag HK5 HHS HjN eq_refl A1 A2 A3 M1 M2 M3 M4 M5 M6 M7).
  + eapply etriple_conseq; [| intros w Hw; exact Hw | apply etriple_refl]. intros w Hw.
    exact (xe_exit_gen XBs sXB ENT_XB SID_XB IDS_XB IDSO_XB G S tp _ rho rhoL w Hw Hag HK5 HHS HjN eq_refl A1 A2 A3 M1 M2 M3 M4 M5 M6 M7).
Qed.

Lemma OW5b : ltac2:(tb__ "0|0|
S35S28S116S0S14S95A1S25S0S99S9bA1S25S0Sa2S25S0Sa1S9cA1S25S0Sa8Sb3A1S25S0Sa9Sa0A1S26S0A1A3A3A3A3A3A3S2aA3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FRwf : ltac2:(tb__ "0|0|
S35S28S24S95SbcA2S2aA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma insK5_agree : ltac2:(tb__ "0|0|
S5cS2eS3aS1S1SbS95R2R1A3S6cR6R5R4R3A4S6cR7R6R5R3A4F_;F_;Frho';Frho;FS;Fb;FG;").
Proof.
  intros G b S rho rho' Hag (A & B & C & D & E1 & E2 & F & FR).
  pose proof OW5b as W. cbn [forallb] in W. apply andb_prop in W as [W1 W]. apply andb_prop in W as [W2 W]. apply andb_prop in W as [W3 W]. apply andb_prop in W as [W4 W]. apply andb_prop in W as [W5 _].
  pose proof Hag as (Hw & Hl & Hm).
  split; [eapply insK_agree; eauto|]. split; [rewrite <- (Hw 178%positive) by (unfold NXD; lia); exact B|].
  split; [rewrite <- (Hw 179%positive) by (unfold NXD; lia); exact C|]. split; [rewrite <- (Hw 180%positive) by (unfold NXD; lia); exact D|].
  split; [eapply ro_win_agree; [exact Hag | exact W1 | exact E1]|]. split; [eapply ro_win_agree; [exact Hag | exact W4 | exact E2]|]. split.
  - pose proof (Forall_inv F) as F1. pose proof (Forall_inv (Forall_inv_tail F)) as F2. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail F))) as F3.
    pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail F)))) as F4. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail F))))) as F5.
    repeat apply Forall_cons; [| | | | | apply Forall_nil]; (eapply winDFP_agree; [exact Hag | | ]); [exact W1 | exact F1 | exact W2 | exact F2 | exact W3 | exact F3 | exact W4 | exact F4 | exact W5 | exact F5].
  - intros a Ha. apply FR. rewrite (eval_agree NXD rho rho' fr_addr Hag FRwf). exact Ha.
Qed.

Lemma je_cont : ltac2:(tb__ "0|0|
S5cS3aS27S4aQ40A1A1S1S65R4R2A2S67R5R4R2A3S66R6R5A2S74R7R6A2S11dS3cVok;S4dS3cS63R8A1VJhs;R5R6A5S64A4F_;F_;F_;F_;Frho;Ftp;FS;FG;").
Proof.
  intros G S tp rho HG HJK HHS HE. pose proof HE as (A1 & A2 & A3). pose proof HJK as (_ & HjN & _).
  eapply triple_conseq with (P := fun w => exists rho', insK5 G (Z.to_nat (S / 1048576)) S rho' /\ SPA segsA (JJ G) (mkI5e2 sz Jhs) rho' tp w).
  - intros w Hw. destruct (glue_e2 G S tp rho w (Z.to_nat (S / 1048576)) Hw HJK HHS eq_refl A1 A2 A3) as (rho' & S' & K'). exists rho'. split; [exact K' | exact S'].
  - intros w Hw. exact Hw.
  - apply triple_ex. intros rho'. apply triple_pure. intros HK5. apply triple1_triple.
    eapply (stage_run (JJ G)); [apply JJ_ok | apply JJ_stable; lia | exact RUNE1 | discriminate | exact J_len | apply Pos.leb_le; reflexivity |].
    intros L rhoL [<-|[]] Hag. cbn [la_state].
    eapply triple_conseq with (P := fun w => exists rho2, insK5 G (Z.to_nat (S / 1048576)) S rho2 /\ SPA segsA (JJ G) E2hs rho2 tp w); [| intros w Hw; exact Hw |].
    + intros w Hw. destruct (glue_e2h G _ S tp rhoL w Hw (insK5_agree G _ S rho' rhoL Hag HK5)) as (rho2 & S2 & K2). exists rho2. split; [exact K2 | exact S2].
    + apply triple_ex. intros rho2. apply triple_pure. intros HK2. exact (e2_cont G S tp rho2 HG HK2 HHS HjN HE).
Qed.

Lemma eje_cont : ltac2:(tb__ "0|0|
S5cS3aS27S4aQ40A1A1S1S65R4R2A2S67R5R4R2A3S66R6R5A2S74R7R6A2S11cS3cS4dS3cS63R8A1VJhs;R5R6A5S64A3F_;F_;F_;F_;Frho;Ftp;FS;FG;").
Proof.
  intros G S tp rho HG HJK HHS HE. pose proof HE as (A1 & A2 & A3). pose proof HJK as (_ & HjN & _).
  eapply etriple_conseq with (P := fun w => exists rho', insK5 G (Z.to_nat (S / 1048576)) S rho' /\ SPA segsA (JJ G) (mkI5e2 sz Jhs) rho' tp w).
  - intros w Hw. destruct (glue_e2 G S tp rho w (Z.to_nat (S / 1048576)) Hw HJK HHS eq_refl A1 A2 A3) as (rho' & S' & K'). exists rho'. split; [exact K' | exact S'].
  - intros w Hw. exact Hw.
  - apply etriple_ex. intros rho'. apply etriple_pure. intros HK5.
    eapply (estage_run (JJ G)); [apply JJ_stable; lia | exact RUNE1 | discriminate | exact J_len | apply Pos.leb_le; reflexivity |].
    intros L rhoL [<-|[]] Hag. cbn [la_state].
    eapply etriple_conseq with (P := fun w => exists rho2, insK5 G (Z.to_nat (S / 1048576)) S rho2 /\ SPA segsA (JJ G) E2hs rho2 tp w); [| intros w Hw; exact Hw |].
    + intros w Hw. destruct (glue_e2h G _ S tp rhoL w Hw (insK5_agree G _ S rho' rhoL Hag HK5)) as (rho2 & S2 & K2). exists rho2. split; [exact K2 | exact S2].
    + apply etriple_ex. intros rho2. apply etriple_pure. intros HK2. exact (ee2_cont G S tp rho2 HG HK2 HHS HjN HE).
Qed.

Lemma gmid_page : ltac2:(tb__ "0|1|
S5cS27S4aQ40A1M0A1S2eG0S65R4R3A2S119R3S2dS3aS61R5A1A2A2S3eS3dSf5R6A1S120A2S3dSf5VG0;A1Sf6VG0;A1A2A2S65S100R7R5A2S25G0R4R6A3A2F_;F_;F_;Fp;Fb;Ftp;FG;").
Proof.
  intros G tp b p (M1 & M2 & M3 & M4 & M5 & M6 & [l M7]) Hb Hc. unfold gmid. cbn [dN dF dNB dFB G_page].
  split; [exact M1|]. split; [exact M2|]. split; [exact M3|]. split; [exact M4|].
  split; [rewrite dep_cost_G_page by exact Hb; lia|]. split; [exact M6|]. exists (p :: l). rewrite M7. reflexivity.
Qed.

Lemma HS_cases : ltac2:(tb__ "0|7|
S5cS3aS66R2R1A2S3eZ1M0S5fR3A1A2S39S36S35S3aR3S5fR4A1M1A3S36S35S3aS40R3Z100000M2A2M3S40G1G2A2M4A3S35S3aS41R3G2A2M5S41G1G2A2M6A3A2A2S36S35S3aR3S3dS3dG1Vsz;A2G0A2A3S36S35S3aG3S3dG4G0A2A3S36S35S3aG5S45S3dS3dG6Vsz;A2G0A2G2A2A3S36S3eZ0G5A2S3eG5Vsz;A2A2A2A2A2A2F_;F_;FS;FG;").
Proof.
  intros G S H HF0. pose proof Hsz as Hs. unfold SZMAXT in Hs. pose proof (Z.mod_pos_bound (dF G) 1048576 ltac:(lia)) as MB.
  pose proof (Z.div_mod (dF G) 1048576 ltac:(lia)) as DM.
  destruct H as [E|[E SR]]; [left; subst S; repeat split; reflexivity|]. right.
  assert (Q : S / 1048576 = dF G / 1048576 + 1) by (symmetry; apply (Z.div_unique_pos S 1048576 (dF G / 1048576 + 1) (dF G mod 1048576 + sz + 1 - 1048576)); lia).
  assert (R : S mod 1048576 = dF G mod 1048576 + sz + 1 - 1048576) by (symmetry; apply (Z.mod_unique_pos S 1048576 (dF G / 1048576 + 1) (dF G mod 1048576 + sz + 1 - 1048576)); lia).
  lia.
Qed.

Lemma prepay_core : ltac2:(tb__ "0|6|
S5cS3aS27S4aQ40M0A1M1A1S1S27S12cA1M2S147S12aS42S40R6Z100000M3A2A1S2eS4bG0S111R8R1S114S3aR1S61R8A1Z0M4A4A3A2G1S100R9R2A2S5cS65RaR8A2S3eS3dSf5RbA1S120A2S3dSf5VG0;A1Sf6VG0;A1A2A2S67RcRbR9A3S66RdRcA2S119R7S2dS3aS5eReA1A2A2S3fS3dS41ReG3A2Vsz;A2G3A2S38S3eS43Z8S3dS3dS41RfG3A2Vsz;A2Z1A2A2S43S120S114S3aR9S61R10A1G4A4A2A2A1S4dS3cS63R11A1VJhs;ReRfS2cG2S143RdS144RcRbA2A4A6S37S1S1S36S36S67RaR12R1A3S36S74RaR12A2S65RaS25G1RbR11A3M5A2A2A2S4dS3cS63RaA1VJhs;R1G5S2cG2S143RfS144ReRdA2A4A6A2Lrho';A2F_;F_;F_;F_;F_;F_;F_;F_;TG';Tp;Tb;Fmd;Fms;Ftr;Frho;Ftp;FS;FG;").
Proof.
  intros G S tp rho tr ms md b p G' HG Hbud HJK HHS Hbl Hns Hnp Hw.
  set (fp := nth b (dFP G) 0) in *. set (fb := nth b (dFB G) 0).
  pose proof Hw as [HsmA [HREL [HK [[HM HV] _]]]].
  pose proof (proj1 HsmA) as Hsm. unfold virt in Hsm. cbn [fst snd cfg_ms cfg_model w_tr w_cfg] in Hsm.
  pose proof HJK as (HIK & Hj & H178 & H179 & HROs & HDs). pose proof HIK as (K177 & KW0 & KD1 & KD2).
  pose proof (dm_N _ _ HM) as [HN _]. pose proof (dm_F _ _ HM) as (HF0 & HF11 & HF32 & _).
  destruct (kd_room segsA K NPRE HKD G rho tp _ _ HK (conj HM HV)) as [Hroom HDN]. cbn [cfg_model w_cfg fst snd] in Hroom.
  assert (HroomPG : headroom md tp >= PG) by (unfold droom in Hroom; destruct ((dN G + 1) mod 65536 =? 0); unfold NBSZ, PG in *; lia).
  destruct (HS_bounds G S HHS HF0 HF32) as [HSF HS32].
  pose proof (Z.mod_pos_bound S 1048576 ltac:(lia)) as MB. pose proof (Z.mod_pos_bound (dF G) 1048576 ltac:(lia)) as MBF.
  pose proof (Z.div_mod S 1048576 ltac:(lia)) as DMS. pose proof (Z.div_mod (dF G) 1048576 ltac:(lia)) as DMF.
  assert (HbZ : Z.of_nat b = S / 1048576) by (subst b; rewrite Z2Nat.id by (apply Z.div_pos; lia); reflexivity).
  set (jN := Z.to_nat ((dN G + 1) / 65536)) in *. set (blkN := nth jN (dNB G) 0) in *.
  assert (HinN : In blkN (dNB G)) by (unfold blkN; apply nth_In; exact Hj).
  destruct (dm_nb _ _ HM blkN HinN) as (NBal & NBlo & NBhi & NBpres).
  pose proof (nb_top _ _ _ _ _ _ _ HK HV HinN) as NBhiT.
  assert (DISJNF : blkN + NBSZ <= fb \/ fb + FBSZ <= blkN) by exact (dblocks_nf_disj G jN b Hj Hbl (dm_disj _ _ HM)).
  assert (NNA : bv_unsigned (eval rho nn_addr) = blkN + 16 * ((dN G + 1) mod 65536)).
  { rewrite (nn_addr_val rho (dN G)); [rewrite H178; reflexivity | exact K177 | unfold DNMAX in HDN; lia | rewrite H178; exact NBhi]. }
  pose proof (Z.mod_pos_bound (dN G + 1) 65536 ltac:(lia)) as MBN.
  destruct (dm_fbases _ _ HM fb (nth_In _ _ Hbl)) as (FBal & FBlo & FBhi).
  pose proof (fb_top _ _ _ _ _ _ fb HK HV (nth_In _ _ Hbl)) as FBhiT.
  destruct (dm_fp _ _ HM b Hbl) as [FPrange FPpres]. fold fp fb in FPrange, FPpres.
  pose proof (proj2 (dm_fb_len _ _ HM)) as LEN.
  assert (Hszb : 1 <= sz <= 30) by (pose proof Hsz; unfold SZMAXT in *; lia).
  assert (Hfp : fp < FBPAGES) by (unfold FBPAGES, PG in *; lia).
  pose proof alloc_ceiling_valD as ACV.
  assert (Hpv : bv_unsigned p = fb + PG * fp) by (unfold p, fpage; fold fb; apply u64_lit; unfold PG, FBSZ, FBPAGES, IMG_HI in *; lia).

  assert (Hone : 8 * (S mod 1048576 + sz + 1) <= PG * (fp + 1) /\ PG * (fp + 1) <= 8 * (dF G - 1048576 * Z.of_nat b) + PG + 248).
  { pose proof (dm_fp_lo _ _ HM b Hbl) as LO. fold fp in LO. rewrite HbZ in LO |- *.
    destruct (HS_cases G S HHS HF0) as [(ES & EQ & ER)|(ES & EQ & ER & RR)].
    - rewrite EQ in LO |- *. rewrite Z.min_l in LO by lia. unfold PG in *. lia.
    - rewrite EQ in LO |- *. unfold PG in *. lia. }
  destruct Hone as [Hone Hhi].

  pose proof (SPA_facts segsA _ _ _ _ _ Hw) as HFall.
  pose proof (holds_inclb rho _ _ J_F HFall) as HF4.
  apply Forall_app in HF4 as [HFD HF4]. apply Forall_app in HF4 as [HFt HF4].
  assert (SNA : bv_unsigned (eval rho slotN_addr) = MAP1 + 8 * ((dN G + 1) / 65536)) by (apply slotN_addr_val; [exact K177 | unfold DNMAX in HDN; lia]).
  assert (HjNz : 0 <= (dN G + 1) / 65536 < 2 ^ 15) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; unfold DNMAX in HDN; lia]).
  assert (EXD : forall lo hi, fb <= lo /\ hi <= fb + FBSZ -> lo <= hi ->
            Forall (fun o' => ranges_disjoint (obj_range rho o') (lo, hi)) (ss_objs SJ)).
  { intros lo hi Hlh Hle.
    eapply (objs_ranges_ext rho SJ _ _ [O_tw vW; O_nid vN; O_slotN vNB; O_nn; O_tf vF] _ _ Hsm ltac:(intros o Ho; exact Ho) J_skel HFD ltac:(first [assumption | eapply TOPr_of_REL; eassumption | eapply TOPr_of_JJ; eassumption])); [unfold STORE, DEPOT, IMG_HI in *; lia | lia | exact Hle |].
    unfold O_tw, O_nid, O_slotN, O_nn, O_tf, carved, ranges_disjoint.
    apply Forall_cons. { rewrite obj_range_mk by lia. cbn [fst snd eval vP].
      pose proof (proj1 (Forall_forall _ _) HFt (SPUle vP (SLit (DEPOT + 4 * 2^20 - 4))) ltac:(unfold F_tw; cbn; tauto)) as X2. cbn [holds eval vP] in X2. unfold DEPOT in X2. rewrite u64_lit in X2 by lia.
      unfold STORE, DEPOT, IMG_HI in *. lia. }
    apply Forall_cons. { rewrite obj_range_mk by (unfold NIDS; lia). cbn [fst snd eval]. rewrite u64_lit by lia. unfold NIDS, STORE, DEPOT, IMG_HI in *. lia. }
    apply Forall_cons. { rewrite obj_range_mk by lia. cbn [fst snd]. rewrite SNA. unfold MAP1, IMG_HI in *. lia. }
    apply Forall_cons. { rewrite obj_range_mk by lia. cbn [fst snd]. rewrite NNA. unfold NBSZ, FBSZ, IMG_HI in *. lia. }
    apply Forall_cons. { rewrite obj_range_mk by (unfold STORE; lia). cbn [fst snd eval]. rewrite u64_lit by (unfold STORE; lia). unfold STORE, IMG_HI in *. lia. }
    apply Forall_nil. }
  assert (Hdisj : Forall (fun o => ranges_disjoint (obj_range rho o) (bv_unsigned p, bv_unsigned p + page_size)) (ss_objs (ax_S Jhs))).
  { rewrite Hpv. change page_size with PG. apply EXD; unfold PG, FBPAGES, FBSZ in *; lia. }

  assert (Hal : bv_unsigned p mod page_size = 0) by (rewrite Hpv; change page_size with 4096; unfold PG in *; rewrite Z.add_mod, FBal, Z.mul_comm, Z.mod_mul by lia; reflexivity).
  assert (Hlz : page_in_ranges p (m_vm_lazy md) = true).
  { apply (proj2 (page_in_ranges_spec p _)). exists (Z_to_bv 64 fb, Z_to_bv 64 FBSZ). split; [exact (dv_lazy _ _ _ HV fb (nth_In _ _ Hbl))|].
    apply (proj2 (page_in_range_spec p _)). cbn [fst snd]. rewrite Hpv, !u64_lit by (unfold FBSZ, IMG_HI in *; lia). change page_size with PG. unfold PG, FBSZ, FBPAGES in *. lia. }
  assert (Hnin : ~ In p tp).
  { intros Hin. pose proof (proj1 (dv_tp _ _ _ HV b fp Hbl ltac:(lia)) ) as X. unfold p in Hin. fold fp in X. specialize (X Hin). lia. }
  assert (Hacc : forall j, 0 <= j < page_size -> covered (vm_noaccess (m_vmmaps md)) (bv_unsigned p + j) = false).
  { intros j Hjj. change page_size with 4096 in Hjj. rewrite Hpv. replace (fb + PG * fp + j) with (fb + (PG * fp + j)) by lia.
    apply (dv_acc _ _ _ HV fb); [exact (nth_In _ _ Hbl) | unfold PG, FBSZ, FBPAGES in *; lia]. }
  assert (HroomPS : headroom md tp >= page_size) by (change page_size with PG; exact HroomPG).

  assert (Hw0 : SPA segsA (fun _ _ _ _ => True) Jhs rho tp (tr, mkCfg ms md)) by (split; [exact HsmA | exact I]).
  pose proof (SPA_prepay_zero segsA (fun _ _ _ _ => True) rho Jhs p tp tr ms md Hw0 Hal Hlz Hnin Hacc HroomPS Hdisj (fun _ => I)) as Hw1.

  set (A1 := ax_setS Jhs (set_objs (ax_S Jhs) (ss_objs (ax_S Jhs) ++ [zero_page_obj p]))) in Hw1.
  pose proof (SPA_unobj segsA (fun _ _ _ _ => True) rho A1 (ss_objs (ax_S Jhs)) [zero_page_obj p] (p :: tp) tr ms md eq_refl Hw1 (fun _ => I)) as Hw2.
  cbn zeta in Hw2. set (rho' := rho_absorb rho [zero_page_obj p] (vms md (p :: tp) ms)) in *.
  change (ax_setS A1 (set_objs (ax_S A1) (ss_objs (ax_S Jhs)))) with Jhs in Hw2.

  pose proof (proj1 (proj1 Hw1)) as Hsm1. unfold virt in Hsm1. cbn [fst snd cfg_ms cfg_model w_tr w_cfg] in Hsm1.
  assert (Ho1 : ss_objs (ax_S A1) = ss_objs (ax_S Jhs) ++ [zero_page_obj p]) by reflexivity.
  assert (Efp : fpage G b fp = fb + PG * fp) by (unfold fpage; fold fb; reflexivity).
  assert (ZP : forall z, fpage G b fp <= z < fpage G b fp + PG -> view segsA (rm rho') z = Some (Z_to_bv 8 0)).
  { intros z Hzp. rewrite Efp in Hzp. unfold rho', zero_page_obj.
    pose proof (urange p) as URp.
    apply (absorb_view_dzero segsA rho (ax_S A1) tr (vms md (p :: tp) ms) (vmd md) (ss_objs (ax_S Jhs)) _ (SLit (bv_unsigned p)) 0 page_size Hsm1 Ho1);
      cbn [eval]; rewrite ?u64_lit by (clear - URp; lia); change page_size with 4096; try (clear - URp; lia).
    1: left; reflexivity. all: rewrite Hpv; first [ clear - Hzp; unfold PG; lia | unfold PG, FBSZ, FBPAGES, IMG_HI in *; lia ]. }
  assert (OUT : forall a : word, ~ (fpage G b fp <= bv_unsigned a < fpage G b fp + PG) -> rm rho' a = rm rho a).
  { intros a Ha. unfold rho'. apply rm_absorb_out. intros (o & [<-|[]] & Hr). apply Ha. unfold zero_page_obj in Hr.
    rewrite obj_range_mk in Hr by (change page_size with 4096; lia). cbn [fst snd eval] in Hr. rewrite u64_lit in Hr by (pose proof (urange p); lia).
    change page_size with 4096 in Hr. rewrite Efp. unfold PG in *. lia. }
  assert (VOUT : forall z, ~ (fpage G b fp <= z < fpage G b fp + PG) -> view segsA (rm rho') z = view segsA (rm rho) z).
  { intros z Hz. unfold view. destruct ((0 <=? z) && (z <? 2 ^ 64))%bool eqn:E; [|reflexivity]. unfold rd_of. rewrite OUT; [reflexivity|].
    apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2. rewrite u64_lit by lia. exact Hz. }
  assert (PGin : forall z, fpage G b fp <= z < fpage G b fp + PG -> DFPw G z).
  { intros z Hz. right. right. exists fb. split; [apply nth_In; exact Hbl|]. rewrite Efp in Hz. unfold PG, FBSZ, FBPAGES in *. lia. }

  assert (HK1 : K G rho' tp tr md).
  { eapply (kd_view segsA K NPRE HKD G rho rho'); [intros i; reflexivity | intros l; reflexivity | | exact HK].
    intros z Hz. apply VOUT. intros Hin. exact (Hz (PGin z Hin)). }
  assert (HK' : K G' rho' (p :: tp) tr md).
  { eapply (kd_trans segsA K NPRE HKD G tp md G' (p :: tp) md rho' tr); [|exact HK1]. apply (DT_page G tp md b p Hbl Hfp eq_refl Hnin HroomPG). }
  pose proof (depot_mem_page G (view segsA (rm rho)) (view segsA (rm rho')) b HM Hbl Hfp Hhi ZP VOUT) as HM'.
  pose proof (depot_vm_page G (view segsA (rm rho)) md tp b p HM HV Hbl Hfp eq_refl) as HV'.
  destruct HREL as (R1 & R2 & R3).
  assert (HREL' : REL G' rho').
  { split; [exact R1 | split].
    - intros a Ha. rewrite OUT; [apply R2; exact Ha|]. intros Hin. apply Ha. apply DFPw_DFP. exact (PGin _ Hin).
    - intros z Hz. rewrite VOUT; [apply R3; exact Hz|]. intros Hin. exact (Hz (PGin z Hin)). }
  assert (Hw3 : SPA segsA (JJ G') Jhs rho' (p :: tp) (tr, mkCfg ms md)).
  { split; [exact (proj1 Hw2)|]. split; [exact HREL'|]. split; [exact HK'|]. split; [split; [exact HM' | exact HV']| exact I]. }
  exists rho'. split; [|exact Hw3].

  assert (SLOTout : forall a : word, fst (obj_range rho (O_slotN vNB)) <= bv_unsigned a < snd (obj_range rho (O_slotN vNB)) -> rm rho' a = rm rho a).
  { intros a Ha. apply OUT. unfold O_slotN, carved in Ha. rewrite obj_range_mk in Ha by lia. cbn [fst snd] in Ha. rewrite SNA in Ha. rewrite Efp. unfold MAP1, IMG_HI, PG in *. lia. }
  split; [|split].
  - split; [exact HIK|]. split; [exact Hj|]. split; [exact H178|]. split; [exact H179|]. split; [unfold rho'; apply ro_win_absorb; [exact HROs | exact SLOTout] |].
    pose proof (Forall_inv HDs) as WD1. pose proof (Forall_inv (Forall_inv_tail HDs)) as WD2. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail HDs))) as WD3.
    apply Forall_cons; [exact WD1|]. apply Forall_cons; [exact WD2|]. apply Forall_cons; [exact WD3|]. apply Forall_nil.
  - unfold arm_e, G'. cbn [dF dFB dFP G_page]. fold b. rewrite nth_list_upd_same by (rewrite LEN; exact Hbl). fold fp.
    split; [exact Hbl|]. split; [exact Hns|]. lia.
  - apply gmid_page; [exact HG | rewrite LEN; exact Hbl | exact Hbud].
Qed.

Lemma jp_cont : ltac2:(tb__ "0|1|
S5cS3aS27S4aQ40A1A1S1S65R4R2A2S3eS3dSf5R5A1S120A2S3dSf5VG0;A1Sf6VG0;A1A2A2S67R6R5R3A3S66R7R6A2S119S42S40R7Z100000M0A2A1S2dS3aS5eR8A1A2A2S3fS3dS41R8G0A2Vsz;A2G0A2S38S3eS43Z8S3dS3dS41R9G0A2Vsz;A2Z1A2A2S43S120S114S3aS42S40R9G0A2A1S61RaA1Z0A4A2A2A1S11dS3cVok;S4dS3cS63RbA1VJhs;R8R9A5S64A4F_;F_;F_;F_;F_;F_;F_;Frho;Ftp;FS;FG;").
Proof.
  intros G S tp rho HG Hbud HJK HHS Hbl Hns Hnp.
  set (b := Z.to_nat (S / 1048576)). set (p := Z_to_bv 64 (fpage G b (nth b (dFP G) 0))). set (G' := G_page G b).
  eapply triple_conseq with (P := fun w => exists rho', (jK G' S rho' /\ arm_e G' S /\ gmid G' (p :: tp)) /\ SPA segsA (JJ G') Jhs rho' (p :: tp) w);
    [| intros w Hw; exact Hw |].
  - intros [tr [ms md]] Hw. exact (prepay_core G S tp rho tr ms md HG Hbud HJK HHS Hbl Hns Hnp Hw).
  - apply triple_ex. intros rho'. apply triple_pure. intros (A1 & A2 & A3). apply (je_cont G' S (p :: tp) rho' A3 A1); [exact HHS | exact A2].
Qed.

Lemma ejp_cont : ltac2:(tb__ "0|1|
S5cS3aS27S4aQ40A1A1S1S65R4R2A2S3eS3dSf5R5A1S120A2S3dSf5VG0;A1Sf6VG0;A1A2A2S67R6R5R3A3S66R7R6A2S119S42S40R7Z100000M0A2A1S2dS3aS5eR8A1A2A2S3fS3dS41R8G0A2Vsz;A2G0A2S38S3eS43Z8S3dS3dS41R9G0A2Vsz;A2Z1A2A2S43S120S114S3aS42S40R9G0A2A1S61RaA1Z0A4A2A2A1S11cS3cS4dS3cS63RbA1VJhs;R8R9A5S64A3F_;F_;F_;F_;F_;F_;F_;Frho;Ftp;FS;FG;").
Proof.
  intros G S tp rho HG Hbud HJK HHS Hbl Hns Hnp.
  set (b := Z.to_nat (S / 1048576)). set (p := Z_to_bv 64 (fpage G b (nth b (dFP G) 0))). set (G' := G_page G b).
  eapply etriple_conseq with (P := fun w => exists rho', (jK G' S rho' /\ arm_e G' S /\ gmid G' (p :: tp)) /\ SPA segsA (JJ G') Jhs rho' (p :: tp) w);
    [| intros w Hw; exact Hw |].
  - intros [tr [ms md]] Hw. exact (prepay_core G S tp rho tr ms md HG Hbud HJK HHS Hbl Hns Hnp Hw).
  - apply etriple_ex. intros rho'. apply etriple_pure. intros (A1 & A2 & A3). apply (eje_cont G' S (p :: tp) rho' A3 A1); [exact HHS | exact A2].
Qed.

Lemma jx_cont : ltac2:(tb__ "0|1|
S5cS3aS27S4aQ40A1A1S1S65R4R2A2S3eS3dSf5R5A1S120A2S3dSf5VG0;A1Sf6VG0;A1A2A2S67R6R5R3A3S66R7R6A2S119S42S40R7Z100000M0A2A1S2dS3aS5eR8A1A2A2S3fS3dS41R8G0A2Vsz;A2G0A2S11dS3cVok;S4dS3cS63RaA1VJhs;R7R8A5S64A4F_;F_;F_;F_;F_;F_;Frho;Ftp;FS;FG;").
Proof.
  intros G S tp rho HG Hbud HJK HHS Hbl Hns.
  destruct (Z_lt_le_dec (PG * nth (Z.to_nat (S / 1048576)) (dFP G) 0) (8 * (S mod 1048576 + sz + 1))) as [Hnp|Hp].
  - apply (jp_cont G S tp rho HG Hbud HJK HHS Hbl Hns). lia.
  - apply (je_cont G S tp rho HG HJK HHS). split; [exact Hbl | split; [exact Hns | exact Hp]].
Qed.

Lemma ejx_cont : ltac2:(tb__ "0|1|
S5cS3aS27S4aQ40A1A1S1S65R4R2A2S3eS3dSf5R5A1S120A2S3dSf5VG0;A1Sf6VG0;A1A2A2S67R6R5R3A3S66R7R6A2S119S42S40R7Z100000M0A2A1S2dS3aS5eR8A1A2A2S3fS3dS41R8G0A2Vsz;A2G0A2S11cS3cS4dS3cS63RaA1VJhs;R7R8A5S64A3F_;F_;F_;F_;F_;F_;Frho;Ftp;FS;FG;").
Proof.
  intros G S tp rho HG Hbud HJK HHS Hbl Hns.
  destruct (Z_lt_le_dec (PG * nth (Z.to_nat (S / 1048576)) (dFP G) 0) (8 * (S mod 1048576 + sz + 1))) as [Hnp|Hp].
  - apply (ejp_cont G S tp rho HG Hbud HJK HHS Hbl Hns). lia.
  - apply (eje_cont G S tp rho HG HJK HHS). split; [exact Hbl | split; [exact Hns | exact Hp]].
Qed.

Lemma bd1_addr_val : ltac2:(tb__ "0|1|
S1S3aS35S3aS49Q40M0S3R2Pb3A2A2R1A3S3eZ0R2A2S3fS3dR3Vsz;A2S44Z2Z20A2A2S35S3aS49G0SeR5Sc9Vsz;A1A2A2S3dSf9S43Z10S40S3dR4Vsz;A2Z100000A2A2A2A3F_;F_;F_;FF;Frho;").
Proof.
  intros rho F HF HB1 HB2. pose proof Hsz as Hs. unfold SZMAXT in Hs. unfold bd1_addr, add, vF, STORE. cbn [eval]. rewrite add_val, sll_val, srl_val, add_val, HF.
  change (20 mod 64) with 20. change (4 mod 64) with 4. rewrite !u64_lit by lia. rewrite (Z.mod_small (F + sz)) by lia.
  rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia.
  change (2 ^ 20) with 1048576. assert (0 <= (F + sz) / 1048576 < 2 ^ 12) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  rewrite (Z.mod_small (_ * 2 ^ 4)) by lia. rewrite Z.mod_small by lia. lia.
Qed.

Lemma carved4b_sound : ltac2:(tb__ "0|3|
S0S2S35S28Se1R2R1A2S2aA3S37S2S2S35S0R4S15bR3Z18M0Z1cS25S2bS2bS3aS2eA2M1S2A2M2S2cG1S2S2cS3aS2eG0U4A4R1A4S26G2A1A3A4A3Le;A2F_;Fbase;Fo;").
Proof.
  intros [ob lo hi cs df] base H. unfold carved4b in H. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt] in H.
  apply andb_prop in H as [H Hd]. apply andb_prop in H as [H Hc]. apply andb_prop in H as [H Hhi]. apply andb_prop in H as [Hb Hlo].
  apply sv_eqb_sound in Hb. apply sv_eqb_sound in Hlo. apply sv_eqb_sound in Hhi. subst.
  destruct cs as [|[off k v] [|]]; [discriminate Hc | | discriminate Hc]. apply andb_prop in Hc as [Ho Hk]. apply sv_eqb_sound in Ho. apply Z.eqb_eq in Hk. cbn in Ho, Hk. subst.
  destruct df; try discriminate Hd. exists v. reflexivity.
Qed.

Definition dK (G : DG) (rho : valuation) : Prop := ltac2:(tb__ "0|4|
S36S69VG;Vrho;A2S36S119S42S40S3dS5dVG;A1Z1A2Z10000A2A1M0S2dS3aS60VG;A1M1A2A2S36S35S3aS49Q40M2S3Vrho;Pb2A2A2S114S3aG0G1Z0A4A3S36S35S3aS49G2S3Vrho;Pb3A2A2S5fVG;A1A3S36S123S3cVrho;S99S9bA1M3A3S112S0S68VG;Vrho;A2S25S0G3S25S0Sa2S25S0Sa1S9cA1S25S0SbeSa0A1S25S0SbfVsz;S9Pc6A1A2S26S0A1A3A3A3A3A3A3A2A2A2A2A2").

Definition VS_D : list positive := ltac2:(tb__ "0|0|
S25S3bPb3S25S3bPb5S25S3bPc6S26S3bA1A3A3A3").
Let S_Db : sstate := ltac2:(tb__ "0|0|
S13ScVSNB;A1SfVSNB;A1S16VSNB;A1S15VSNB;A1S17VSNB;A1S29S0S6VSNB;A1S25S0Sa2S25S0Sa1S9cA1S25S0SbeSa0A1S25S0SbfVsz;S9Pc6A1A2S26S0A1A3A3A3A3A3S7VSNB;A1S95SaVSNB;A1A9").
Hypothesis NB_vars3 : ltac2:(tb__ "0|0|
S35S28S140S124S81A1VSNB;A2S2aA3").
Hypothesis NB_bvars3 : ltac2:(tb__ "0|0|
S35S28S13fS124S81A1S56VNBs;A1A2S2aA3").
Hypothesis Db_swf : swf S_Db = true.
Hypothesis Db_fb : ltac2:(tb__ "0|0|
S35S28S116S4S10S95A1S29S4S7VSNB;A1Sd9Vsz;A1A3A3S2aA3").

Lemma glue_d : ltac2:(tb__ "0|1|
S5cS27S4aQ40A1A1S1S11bS4dS3cS63R4A1VNBs;R2R3R1A6S6bR5R3A2S3eZ100000M0S3dS41S5fR6A1G0A2Vsz;A2A2S37S1S1S36S4dS3cS63R8A1ScfVsz;VNBs;A2R1R7R5A6S7aR8R1A2A2Lrho';A2F_;F_;F_;Fw;Frho;Ftp;FG;").
Proof.
  intros G tp rho w H (HIK & Hj & H178 & HROs & HDs) Hstr. destruct w as [tr [ms md]].
  pose proof H as [HsmA [HREL [HK [[HM HV] _]]]].
  pose proof HIK as (K177 & KW0 & KD1 & KD2). pose proof Hsz as Hs. unfold SZMAXT in Hs.
  pose proof (dm_N _ _ HM) as [HN _]. pose proof (dm_F _ _ HM) as (HF0 & HF11 & HF32 & HFcell).
  destruct (kd_room segsA K NPRE HKD G rho tp _ _ HK (conj HM HV)) as [_ HDN].
  set (jN := Z.to_nat ((dN G + 1) / 65536)) in *. set (blkN := nth jN (dNB G) 0) in *.
  assert (HinN : In blkN (dNB G)) by (unfold blkN; apply nth_In; exact Hj).
  destruct (dm_nb _ _ HM blkN HinN) as (NBal & NBlo & NBhi & NBpres).
  pose proof (nb_top _ _ _ _ _ _ _ HK HV HinN) as NBhiT.
  set (F := dF G) in *. set (b := F / 1048576).
  pose proof (Z.mod_pos_bound F 1048576 ltac:(lia)) as MB. pose proof (Z.mod_pos_bound (dN G + 1) 65536 ltac:(lia)) as MBN.
  pose proof (Z.div_mod F 1048576 ltac:(lia)) as DMF.
  pose proof (fblk_lt F ltac:(lia) ltac:(lia)) as FBL. pose proof (dm_fb_len _ _ HM) as [FBlen _]. fold F in FBlen.
  assert (Hb0 : 0 <= b) by (apply Z.div_pos; lia).
  assert (HFB : fblk F = b + 1) by (unfold fblk; symmetry; apply (Z.div_unique_pos _ 1048576 (b + 1) (F mod 1048576 - 1)); lia).
  assert (Hb1 : (b + 1 < Z.of_nat (length (dFB G)) \/ Z.of_nat (length (dFB G)) <= b + 1) /\ b + 1 < NFBLK) by (unfold NFBLK; lia).

  assert (Hbl : (Z.to_nat b < length (dFB G))%nat) by (apply Nat2Z.inj_lt; rewrite Z2Nat.id by lia; lia).
  destruct (dm_fb _ _ HM (Z.to_nat b) Hbl) as (_ & _ & FBst & _). rewrite Z2Nat.id in FBst by lia.
  assert (FBst1 : present (view segsA (rm rho)) (STORE + 24 + 16 * (b + 1)) (STORE + 28 + 16 * (b + 1))).
  { destruct (lt_dec (Z.to_nat (b + 1)) (length (dFB G))) as [L|L].
    - destruct (dm_fb _ _ HM (Z.to_nat (b + 1)) L) as (_ & _ & X & _). rewrite Z2Nat.id in X by lia. exact X.
    - assert (L' : Z.of_nat (length (dFB G)) <= b + 1) by (apply Nat.nlt_ge in L; apply (proj1 (Nat2Z.inj_le _ _)) in L; rewrite Z2Nat.id in L by lia; exact L).
      destruct (dm_fb_zero _ _ HM (b + 1) ltac:(lia)) as (_ & X & _). exact X. }
  destruct (present_cell4 (view segsA (rm rho)) (STORE + 24 + 16 * b) ltac:(intros z Hz; apply FBst; lia)) as (stv & Hstv & STcell).
  destruct (present_cell4 (view segsA (rm rho)) (STORE + 24 + 16 * (b + 1)) ltac:(intros z Hz; apply FBst1; lia)) as (stv1 & Hstv1 & STcell1).
  set (bs := [(179%positive, Z_to_bv 64 F); (181%positive, Z_to_bv 64 stv); (198%positive, Z_to_bv 64 stv1)]).
  set (rho' := rho_sets rho bs).
  assert (Hfst : map fst bs = VS_D) by reflexivity.
  assert (Hnd : List.NoDup (map fst bs)) by (rewrite Hfst; unfold VS_D; repeat constructor; cbn; lia).
  assert (E179 : rw rho' 179%positive = Z_to_bv 64 F) by (apply rho_sets_get; [exact Hnd | left; reflexivity]).
  assert (E181 : rw rho' 181%positive = Z_to_bv 64 stv) by (apply rho_sets_get; [exact Hnd | right; left; reflexivity]).
  assert (E198 : rw rho' 198%positive = Z_to_bv 64 stv1) by (apply rho_sets_get; [exact Hnd | right; right; left; reflexivity]).
  destruct (rho_sets_rl_rm bs rho) as [Hrl' Hrm']. fold rho' in Hrl', Hrm'.
  assert (Hother : forall i, notin_vars VS_D i = true -> rw rho' i = rw rho i).
  { intros i Hi. unfold rho'. apply rho_sets_other. rewrite Hfst. apply notin_vars_true. exact Hi. }
  pose proof alloc_ceiling_valD as ACV.
  assert (U179 : bv_unsigned (rw rho' 179%positive) = F) by (rewrite E179, u64_lit; lia).
  assert (U178 : bv_unsigned (rw rho' 178%positive) = blkN) by (rewrite (Hother 178%positive eq_refl); exact H178).
  assert (NNA : bv_unsigned (eval rho' nn_addr) = blkN + 16 * ((dN G + 1) mod 65536)).
  { rewrite (nn_addr_val rho' (dN G)); [rewrite U178; reflexivity | rewrite (Hother 177%positive eq_refl); exact K177 | unfold DNMAX in HDN; lia | rewrite U178; exact NBhi]. }
  assert (BDA : bv_unsigned (eval rho' bd_addr) = STORE + 16 * b) by (apply bd_addr_val; [exact U179 | lia]).
  assert (BD1 : bv_unsigned (eval rho' (bd1_addr sz)) = STORE + 16 * (b + 1)).
  { rewrite (bd1_addr_val rho' F U179) by lia. f_equal. f_equal. symmetry. apply (Z.div_unique_pos _ 1048576 (b + 1) (F mod 1048576 + sz - 1048576)); lia. }
  assert (CIVt : cells_in_view rho' (rd_of segsA (rm rho')) 0 [(STORE, 8%nat, vF)]).
  { unfold cells_in_view. constructor; [|constructor]. intros jj Hjj.
    refine (civ_cell rho' (rm rho') 0 STORE 8 F vF _ _ _ _ jj Hjj); [rewrite Hrm', Z.add_0_l; exact HFcell | cbn [eval]; exact E179 | unfold STORE; lia | unfold STORE; lia]. }
  assert (CIVs : cells_in_view rho' (rd_of segsA (rm rho')) (STORE + 16 * b) [(24, 4%nat, vSt)]).
  { unfold cells_in_view. constructor; [|constructor]. intros jj Hjj.
    refine (civ_cell rho' (rm rho') (STORE + 16 * b) 24 4 stv vSt _ _ _ _ jj Hjj); [rewrite Hrm' | cbn [eval]; exact E181 | unfold STORE; lia | unfold STORE; lia].
    replace (STORE + 16 * b + 24) with (STORE + 24 + 16 * b) by lia. exact STcell. }
  assert (CIVs1 : cells_in_view rho' (rd_of segsA (rm rho')) (STORE + 16 * (b + 1)) [(24, 4%nat, SVar 198)]).
  { unfold cells_in_view. constructor; [|constructor]. intros jj Hjj.
    refine (civ_cell rho' (rm rho') (STORE + 16 * (b + 1)) 24 4 stv1 (SVar 198) _ _ _ _ jj Hjj); [rewrite Hrm' | cbn [eval]; exact E198 | unfold STORE; lia | unfold STORE; lia].
    replace (STORE + 16 * (b + 1) + 24) with (STORE + 24 + 16 * (b + 1)) by lia. exact STcell1. }
  assert (HIK' : insK G rho').
  { split; [rewrite (Hother 177%positive eq_refl); exact K177|]. split; [rewrite (Hother 170%positive eq_refl); exact KW0|].
    split.
    - intros a Ha. apply (KD1 a). rewrite <- (obj_range_agree_vars (notin_vars VS_D) rho rho' (O_tw vW)); [exact Ha | intros v Hv; symmetry; apply Hother; exact Hv | intros l; rewrite Hrl'; reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc].
    - intros a Ha. apply (KD2 a). rewrite <- (obj_range_agree_vars (notin_vars VS_D) rho rho' (O_nid vN)); [exact Ha | intros v Hv; symmetry; apply Hother; exact Hv | intros l; rewrite Hrl'; reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc]. }
  exists rho'. split.
  2:{ split; [exact HIK'|]. split; [exact Hj|]. split; [exact U178|]. split; [exact U179|]. split.
      - eapply (ro_win_vars segsA (notin_vars VS_D)); [intros v Hv; symmetry; apply Hother; exact Hv | intros l; rewrite Hrl'; reflexivity | intros a; rewrite Hrm'; reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | exact HROs].
      - unfold winDFP, O_slotN, O_nn, O_tf, O_stb, O_stb1, carved.
        apply Forall_cons. { intros a Ha. apply (HDs a). rewrite <- (obj_range_agree_vars (notin_vars VS_D) rho rho' (O_slotN vNB)); [exact Ha | intros v Hv; symmetry; apply Hother; exact Hv | intros l; rewrite Hrl'; reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc]. }
        apply Forall_cons. { intros a. rewrite obj_range_mk by lia. cbn [fst snd]. rewrite NNA. intros Ha. right. left. exists blkN. split; [exact HinN | unfold NBSZ in *; lia]. }
        apply Forall_cons. { intros a. unfold STORE. rewrite obj_range_mk by lia. cbn [fst snd eval]. rewrite u64_lit by lia. intros Ha. left. right. unfold SegD_wf.STORE, NFBLK. lia. }
        apply Forall_cons. { intros a. rewrite obj_range_mk by lia. cbn [fst snd]. rewrite BDA. intros Ha. left. right. unfold STORE, NFBLK in *. lia. }
        apply Forall_cons. { intros a. rewrite obj_range_mk by lia. cbn [fst snd]. rewrite BD1. intros Ha. left. right. unfold STORE, NFBLK in *. lia. }
        apply Forall_nil. }

  assert (H1 : SPA segsA (JJ G) NBs rho' tp (tr, mkCfg ms md)).
  { unfold rho'. eapply (SPA_bindV segsA (JJ G) NPRE); [exact NB_X | apply JJ_stable; lia | | rewrite Hfst; exact NB_vars3 | rewrite Hfst; exact NB_bvars3 | exact H].
    rewrite Hfst. unfold VS_D, NPRE. intros v Hv. cbn in Hv. lia. }
  pose proof (SPA_facts segsA _ _ _ _ _ H1) as HFall'.
  pose proof (holds_inclb rho' _ _ NB_F HFall') as HF4. apply Forall_app in HF4 as [HFD HF4]. apply Forall_app in HF4 as [HFt HF4].
  assert (HP : bv_unsigned (rw rho' 171%positive) <= DEPOT + 4 * 2 ^ 20 - 4).
  { pose proof (proj1 (Forall_forall _ _) HFt (SPUle vP (SLit (DEPOT + 4 * 2^20 - 4))) ltac:(unfold F_tw; cbn; tauto)) as X1.
    cbn [holds eval vP] in X1. unfold DEPOT in *. rewrite u64_lit in X1 by lia. exact X1. }
  assert (SNA : DEPOT <= bv_unsigned (eval rho' slotN_addr) /\ bv_unsigned (eval rho' slotN_addr) + 8 <= IMG_HI).
  { rewrite (slotN_addr_val rho' (dN G)); [| rewrite (Hother 177%positive eq_refl); exact K177 | unfold DNMAX in HDN; lia].
    assert (0 <= (dN G + 1) / 65536 < 2 ^ 15) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; unfold DNMAX in HDN; lia]).
    unfold DEPOT, MAP1, IMG_HI. lia. }

  assert (H2 : SPA segsA (JJ G) (ax_setS NBs S_Db) rho' tp (tr, mkCfg ms md)).
  { unfold S_Db, O_nn, O_tf, O_stb, O_stb1.
    apply (SPA_carve_list segsA (JJ G) rho' NBs tp _
             [(nn_addr, 0, 16, []); (SLit 0, STORE, STORE + 8, [(STORE, 8%nat, vF)]); (bd_addr, 24, 28, [(24, 4%nat, vSt)]); (bd1_addr sz, 24, 28, [(24, 4%nat, SVar 198)])]
             NXD H1 Db_swf ltac:(rewrite NB_nx; apply Pos.le_refl)).
    - unfold IMG_HI, NBSZ, FBSZ, FBPAGES, PG, NFBLK in *.
      apply Forall_cons. { rewrite NNA. repeat (split; [lia|]). split; [unfold cells_inside; constructor|]. split; [|split; [constructor | unfold xwords_clear; cbn [ax_X]; rewrite NB_X; intros rr y jj []]].
        intros off Hoff. destruct (NBpres (blkN + 16 * ((dN G + 1) mod 65536) + off) ltac:(lia)) as [x Hx]. rewrite view_in in Hx by lia. rewrite Hrm'. eapply wok_rd_off_image; [lia | exact Hx]. }
      apply Forall_cons. { cbn [eval]. rewrite u64_lit by lia. unfold STORE. repeat (split; [lia|]). split; [unfold cells_inside; constructor; [cbn; lia | constructor]|]. split; [|split; [exact CIVt | unfold xwords_clear; cbn [ax_X]; rewrite NB_X; intros rr y jj []]].
        intros off Hoff. rewrite Z.add_0_l. split; [apply wok_of_imageA; lia | apply rd_of_imageA; lia]. }
      apply Forall_cons. { rewrite BDA. unfold STORE in *. repeat (split; [lia|]). split; [unfold cells_inside; constructor; [cbn; lia | constructor]|]. split; [|split; [exact CIVs | unfold xwords_clear; cbn [ax_X]; rewrite NB_X; intros rr y jj []]].
        intros off Hoff. split; [apply wok_of_imageA; lia | apply rd_of_imageA; lia]. }
      apply Forall_cons. { rewrite BD1. unfold STORE in *. repeat (split; [lia|]). split; [unfold cells_inside; constructor; [cbn; lia | constructor]|]. split; [|split; [exact CIVs1 | unfold xwords_clear; cbn [ax_X]; rewrite NB_X; intros rr y jj []]].
        intros off Hoff. split; [apply wok_of_imageA; lia | apply rd_of_imageA; lia]. }
      apply Forall_nil.
    -
      pose proof (proj1 H1) as Hsm1. unfold smatchA, virt in Hsm1. cbn [fst snd cfg_ms cfg_model w_tr w_cfg] in Hsm1. apply proj1 in Hsm1.
      assert (EXD : forall lo hi, (STORE <= lo /\ hi <= DEPOT) \/ (IMG_HI <= lo /\ hi <= alloc_ceiling) -> lo <= hi ->
                Forall (fun o' => ranges_disjoint (obj_range rho' o') (lo, hi)) (ss_objs SNB)).
      { intros lo hi Hlh Hle.
        eapply (objs_ranges_ext rho' SNB _ _ [O_tw vW; O_nid vN; O_slotN vNB] _ _ Hsm1 ltac:(intros o Ho; exact Ho) NB_skel HFD ltac:(first [assumption | eapply TOPr_of_REL; eassumption | eapply TOPr_of_JJ; eassumption])); [unfold STORE, DEPOT, IMG_HI in *; lia | unfold STORE, DEPOT, IMG_HI in *; lia | exact Hle |].
        unfold O_tw, O_nid, O_slotN, carved, ranges_disjoint.
        apply Forall_cons. { rewrite obj_range_mk by lia. cbn [fst snd eval vP].
          pose proof (proj1 (Forall_forall _ _) HFt (SPUle (SLit DEPOT) vP) ltac:(unfold F_tw; cbn; tauto)) as X2. cbn [holds eval vP] in X2. unfold DEPOT in X2. rewrite u64_lit in X2 by lia.
          unfold STORE, DEPOT, IMG_HI in *. lia. }
        apply Forall_cons. { rewrite obj_range_mk by (unfold NIDS; lia). cbn [fst snd eval]. rewrite u64_lit by lia. unfold NIDS, STORE, DEPOT, IMG_HI in *. lia. }
        apply Forall_cons. { rewrite obj_range_mk by lia. cbn [fst snd]. unfold STORE, DEPOT, IMG_HI in *. lia. }
        apply Forall_nil. }
      cbn [map carve_obj]. unfold carved. unfold IMG_HI, NBSZ, FBSZ, FBPAGES, PG, NFBLK in *.
      apply Forall_cons. { rewrite obj_range_mk by lia. rewrite NNA. apply EXD; [right; unfold IMG_HI; lia | lia]. }
      apply Forall_cons. { rewrite obj_range_mk by (unfold STORE; lia). cbn [eval]. rewrite u64_lit by lia. apply EXD; [left; unfold STORE, DEPOT; lia | unfold STORE; lia]. }
      apply Forall_cons. { rewrite obj_range_mk by lia. rewrite BDA. apply EXD; [left; unfold STORE, DEPOT in *; lia | lia]. }
      apply Forall_cons. { rewrite obj_range_mk by lia. rewrite BD1. apply EXD; [left; unfold STORE, DEPOT in *; lia | lia]. }
      apply Forall_nil.
    -
      cbn [map carve_obj pairwise_disjoint]. unfold carved. unfold IMG_HI, NBSZ, FBSZ, FBPAGES, PG, NFBLK, STORE in *.
      repeat split; try exact I;
        repeat (apply Forall_cons; [unfold ranges_disjoint; rewrite !obj_range_mk by lia; cbn [fst snd eval]; rewrite ?u64_lit by lia; rewrite ?NNA, ?BDA, ?BD1; lia|]); apply Forall_nil. }

  assert (H3 : SPA segsA (JJ G) (ax_with_facts (ax_setS NBs S_Db) (ss_facts SNB ++ F_d sz)) rho' tp (tr, mkCfg ms md)).
  { apply SPA_refacts; [exact H2 | exact Db_fb |]. cbn [ax_S ax_setS ss_facts]. intros HFX. apply Forall_app. split; [exact HFX|].
    unfold F_d, vF, vSt, add.
    assert (Q1 : (F + sz) / 1048576 = b + 1) by (symmetry; apply (Z.div_unique_pos _ 1048576 (b + 1) (F mod 1048576 + sz - 1048576)); lia).
    assert (Q2 : (F + (sz + 1)) / 1048576 = b + 1) by (symmetry; apply (Z.div_unique_pos _ 1048576 (b + 1) (F mod 1048576 + sz + 1 - 1048576)); lia).
    assert (Q3 : (F + (sz + 1 + sz)) / 1048576 = b + 1) by (symmetry; apply (Z.div_unique_pos _ 1048576 (b + 1) (F mod 1048576 + sz + 1 + sz - 1048576)); lia).
    apply Forall_cons. { cbn [holds eval]. rewrite E179, !u64_lit by lia. lia. }
    apply Forall_cons. { cbn [holds eval branch_taken]. unfold bv_eqb. rewrite !srl_val, add_val, E179, !u64_lit by lia. change (20 mod 64) with 20.
      rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 20) with 1048576. rewrite (Z.mod_small (F + sz)) by lia. rewrite Q1.
      apply Bool.negb_true_iff. apply Z.eqb_neq. fold b. lia. }
    apply Forall_cons. { cbn [holds eval branch_taken]. unfold bv_eqb. rewrite !srl_val, !add_val, E179, !u64_lit by lia. change (20 mod 64) with 20.
      rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 20) with 1048576. rewrite !Z.mod_small by lia. rewrite Q2, Q3. apply Z.eqb_refl. }
    apply Forall_cons. { cbn [holds eval]. rewrite E181, !u64_lit by lia. lia. }
    apply Forall_cons. { cbn [holds eval]. rewrite E198, !u64_lit by lia. lia. }
    apply Forall_nil. }
  unfold ax_with_facts in H3. rewrite ax_setS_setS in H3. exact H3.
Qed.

Variable D1r : axst. Variable sD : wsub.
Hypothesis RUND : ltac2:(tb__ "0|0|
S35S27S52A1S9aUbc0S25S3aSc6S25S3aZ6bf18S25S3aSb2S26S3aA1A3A3A3ScfVsz;VNBs;A2A3S25S52S53VD1r;S126A2S26S52A1A3A3").
Hypothesis D1_X : ax_X D1r = [].
Hypothesis D1_tail : ltac2:(tb__ "0|0|
S35S28ScaVsz;VD1r;A2S2aA3").
Hypothesis D1_F : ltac2:(tb__ "0|0|
S35S28S125S29S4S9eS29S4Sa5S29S4Sa7SabA3A3A3S7S51VD1r;A1A1A2S2aA3").
Hypothesis Dj_fb : ltac2:(tb__ "0|1|
S35S28S116S4S10S8S51VD1r;A1M0A1A1S29S4S7G0A1SdaVsz;A1A3A3S2aA3").
Hypothesis ENT_D : ltac2:(tb__ "0|0|
S35S28S54Se5Vsz;VD1r;A2VJhs;VsD;A3S2aA3").
Hypothesis SID_D : ltac2:(tb__ "0|0|
S35S28S13aVsD;S98A2S2aA3").
Hypothesis IDS_D : ids4 sD = true.
Hypothesis SD179 : ltac2:(tb__ "0|0|
S35S2S13bVsD;Pb3A2SaaS9cS5S3dVsz;Z1A2A1A2A3").

Lemma OW_d : ltac2:(tb__ "0|0|
S35S28S116S0S14S95A1S25S0S99S9bA1S25S0Sa2S25S0Sa1S9cA1S25S0SbeSa0A1S25S0SbfVsz;S9Pc6A1A2S26S0A1A3A3A3A3A3A3S2aA3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma dK_agree : ltac2:(tb__ "0|0|
S5cS1S1SbS95R2R1A3S7aR4R3A2S7aR5R3A2F_;F_;Frho';Frho;FG;").
Proof.
  intros G rho rho' Hag (A & B & C & D & E & F).
  pose proof OW_d as W. cbn [forallb] in W. apply andb_prop in W as [W1 W]. apply andb_prop in W as [W2 W]. apply andb_prop in W as [W3 W]. apply andb_prop in W as [W4 W]. apply andb_prop in W as [W5 _].
  pose proof Hag as (Hw & Hl & Hm).
  split; [eapply insK_agree; eauto|]. split; [exact B|]. split; [rewrite <- (Hw 178%positive) by (unfold NXD; lia); exact C|].
  split; [rewrite <- (Hw 179%positive) by (unfold NXD; lia); exact D|]. split; [eapply ro_win_agree; [exact Hag | exact W1 | exact E]|].
  pose proof (Forall_inv F) as F1. pose proof (Forall_inv (Forall_inv_tail F)) as F2. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail F))) as F3.
  pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail F)))) as F4. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail F))))) as F5.
  repeat apply Forall_cons; [| | | | | apply Forall_nil]; (eapply winDFP_agree; [exact Hag | | ]); [exact W1 | exact F1 | exact W2 | exact F2 | exact W3 | exact F3 | exact W4 | exact F4 | exact W5 | exact F5].
Qed.

Lemma d1_tail_sound : ltac2:(tb__ "0|8|
S35S28ScaVsz;VD1r;A2S2aA3S37S27S0A1M0G0S37S2S2S37S2S2S36S35G0S6S51VD1r;A1A1M1S29S0R3S25S0S15bSc1Z18M2Z1cM3S25S2bS2bS3aS2eA2M4S2A2M5S2cG4S2S2cS3aS2eG2U4A4M6R2A4S26G5A1M7A3A4S25S0S15bSc9Vsz;A1G2G3S25G5S2cG4S2G6R1A4G7A3A4S26S0A1A3A3A3A3S35G0R3S115S0S153S2dS0G1A2U2A2G1A3A3A2Le2;A2Le1;A2LP;A2F_;").
Proof.
  intros H. unfold d1_tail_ok in H. set (objs := ss_objs (ax_S D1r)) in *.
  destruct (skipn (length objs - 2) objs) as [|o1 [|o2 [|]]] eqn:E; try discriminate H.
  apply andb_prop in H as [H1 H2]. destruct (carved4b_sound _ _ H1) as [e1 ->]. destruct (carved4b_sound _ _ H2) as [e2 ->].
  exists (firstn (length objs - 2) objs), e1, e2. split; [|reflexivity]. rewrite <- E. symmetry. apply firstn_skipn.
Qed.

Lemma glue_dj : ltac2:(tb__ "0|2|
S5cS1S1S27S4aQ40A1A1S11bS4dS3cS63R5A1VD1r;R3R2R1A6SbS95R5R4A3S7aR7R6A2S3eZ100000M0S3dS41S5fR8A1G0A2Vsz;A2A2S37S1S1S36S4dS3cS63RaA1VJhs;R1R7R6A6S36S67RaS3dS5fRaA1S3dVsz;Z1A2A2M1R1A3S3fS3dS41G1G0A2Vsz;A2G0A2A2A2Lrho';A2F_;F_;F_;F_;Fw;Ftp;FrhoL;FrhoI;FG;").
Proof.
  intros G rhoI rhoL tp w H Hag HDK0 Hstr. destruct w as [tr [ms md]].
  pose proof (dK_agree G rhoI rhoL Hag HDK0) as (HIK & Hj & H178 & H179 & HROs & HDs). pose proof HIK as (K177 & KW0 & KD1 & KD2).
  pose proof H as [HsmA [HREL [HK [[HM HV] _]]]]. cbn [w_tr w_cfg fst snd cfg_model] in HK, HV.
  pose proof (proj1 HsmA) as Hsm. unfold virt in Hsm. cbn [fst snd cfg_ms cfg_model w_tr w_cfg] in Hsm.
  pose proof Hsz as Hs. unfold SZMAXT in Hs.
  pose proof (dm_N _ _ HM) as [HN _]. pose proof (dm_F _ _ HM) as (HF0 & HF11 & HF32 & HFcell).
  destruct (kd_room segsA K NPRE HKD G rhoL tp _ _ HK (conj HM HV)) as [_ HDN].
  set (F := dF G) in *. set (b := F / 1048576).
  pose proof (Z.mod_pos_bound F 1048576 ltac:(lia)) as MB. pose proof (Z.div_mod F 1048576 ltac:(lia)) as DMF.
  pose proof (fblk_lt F ltac:(lia) ltac:(lia)) as FBL. assert (Hb0 : 0 <= b) by (apply Z.div_pos; lia).
  assert (HFB : fblk F = b + 1) by (unfold fblk; symmetry; apply (Z.div_unique_pos _ 1048576 (b + 1) (F mod 1048576 - 1)); lia).
  pose proof alloc_ceiling_valD as ACV.
  assert (BDA : bv_unsigned (eval rhoL bd_addr) = STORE + 16 * b) by (apply bd_addr_val; [exact H179 | lia]).
  assert (BD1 : bv_unsigned (eval rhoL (bd1_addr sz)) = STORE + 16 * (b + 1)).
  { rewrite (bd1_addr_val rhoL F H179) by lia. f_equal. f_equal. symmetry. apply (Z.div_unique_pos _ 1048576 (b + 1) (F mod 1048576 + sz - 1048576)); lia. }
  destruct (d1_tail_sound D1_tail) as (P & e1 & e2 & Hobjs & HP).
  set (R := [carved bd_addr 24 28 [(24, 4%nat, e1)]; carved (bd1_addr sz) 24 28 [(24, 4%nat, e2)]]) in *.

  pose proof (SPA_facts segsA _ _ _ _ _ H) as HFall.
  pose proof (holds_inclb rhoL _ _ D1_F HFall) as HF3. apply Forall_app in HF3 as [HFD _].

  assert (Hw0 : SPA segsA (fun _ _ _ _ => True) D1r rhoL tp (tr, mkCfg ms md)) by (split; [exact HsmA | exact I]).
  pose proof (SPA_unobj segsA (fun _ _ _ _ => True) rhoL D1r P R tp tr ms md Hobjs Hw0 (fun _ => I)) as Hw1.
  cbn zeta in Hw1. set (rho' := rho_absorb rhoL R (vms md tp ms)) in *.

  assert (CIV1 := absorb_view_cells segsA rhoL (ax_S D1r) tr (vms md tp ms) (vmd md) P R bd_addr 24 28 [(24, 4%nat, e1)] Hsm Hobjs
                    ltac:(unfold R; cbn; tauto) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold cells_inside; constructor; [cbn; lia|constructor])
                    ltac:(rewrite BDA; unfold STORE; lia) ltac:(rewrite BDA; unfold STORE; lia)).
  assert (CIV2 := absorb_view_cells segsA rhoL (ax_S D1r) tr (vms md tp ms) (vmd md) P R (bd1_addr sz) 24 28 [(24, 4%nat, e2)] Hsm Hobjs
                    ltac:(unfold R; cbn; tauto) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold cells_inside; constructor; [cbn; lia|constructor])
                    ltac:(rewrite BD1; unfold STORE; lia) ltac:(rewrite BD1; unfold STORE; lia)).
  fold rho' in CIV1, CIV2. rewrite BDA in CIV1. rewrite BD1 in CIV2. destruct CIV1 as [_ P1]. destruct CIV2 as [_ P2].
  assert (VOUT : forall x : word, ~ (STORE + 24 + 16 * b <= bv_unsigned x < STORE + 28 + 16 * b) -> ~ (STORE + 24 + 16 * (b + 1) <= bv_unsigned x < STORE + 28 + 16 * (b + 1)) ->
                 rm rho' x = rm rhoL x).
  { intros x H1 H2. unfold rho'. apply rm_absorb_out. intros (o & Ho & Hr). unfold R in Ho.
    destruct Ho as [<-|[<-|[]]]; unfold carved in Hr; rewrite obj_range_mk in Hr by lia; cbn [fst snd] in Hr; [rewrite BDA in Hr | rewrite BD1 in Hr]; lia. }
  assert (Hsame : forall z, ~ (STORE + 24 + 16 * b <= z < STORE + 28 + 16 * b) -> ~ (STORE + 24 + 16 * (b + 1) <= z < STORE + 28 + 16 * (b + 1)) ->
                  view segsA (rm rho') z = view segsA (rm rhoL) z).
  { intros z H1 H2. destruct (Z_lt_le_dec z 0) as [Zn|Z0]; [unfold view; destruct (Z.leb_spec 0 z); [lia|reflexivity]|].
    destruct (Z_lt_le_dec z (2 ^ 64)) as [Z1|Z2]; [|unfold view; destruct (Z.ltb_spec z (2 ^ 64)); [lia|]; rewrite andb_false_r; reflexivity].
    rewrite !view_in by lia. unfold rd_of. rewrite VOUT; [reflexivity | rewrite u64_lit by lia; exact H1 | rewrite u64_lit by lia; exact H2]. }

  assert (HM' : depot_mem G (view segsA (rm rho'))).
  { apply (depot_mem_stc G (view segsA (rm rhoL)) (view segsA (rm rho')) b HM Hb0 ltac:(unfold NFBLK; lia)).
    - intros z Hz. apply P1. lia.
    - intros z Hz. apply P2. lia.
    - exact Hsame. }
  assert (INW : forall z, (STORE + 24 + 16 * b <= z < STORE + 28 + 16 * b) \/ (STORE + 24 + 16 * (b + 1) <= z < STORE + 28 + 16 * (b + 1)) -> DFPw G z).
  { intros z Hz. left. unfold dfp_static, DEPOT, MAP1, MAP1N, STORE, NFBLK in *. lia. }
  assert (HK1 : K G rho' tp tr md).
  { eapply (kd_view segsA K NPRE HKD G rhoL rho'); [intros i; reflexivity | intros l; reflexivity | | exact HK].
    intros z Hz. apply Hsame; intros Hin; apply Hz; apply INW; tauto. }
  destruct HREL as (R1 & R2 & R3).
  assert (HREL1 : REL G rho').
  { split; [exact R1 | split].
    - intros x Hx. rewrite VOUT; [apply R2; exact Hx | |]; intros Hin; apply Hx; apply DFPw_DFP; apply INW; tauto.
    - intros z Hz. rewrite Hsame; [apply R3; exact Hz | |]; intros Hin; apply Hz; apply INW; tauto. }
  assert (Hw2 : SPA segsA (JJ G) (ax_setS D1r (set_objs (ax_S D1r) P)) rho' tp (tr, mkCfg ms md)).
  { split; [exact (proj1 Hw1)|]. split; [exact HREL1|]. split; [exact HK1|]. split; [split; [exact HM' | exact HV] | exact I]. }

  assert (E179 : rw rho' 179%positive = rw rhoL 179%positive) by reflexivity.
  assert (Q2 : (F + (sz + 1)) / 1048576 = b + 1) by (symmetry; apply (Z.div_unique_pos _ 1048576 (b + 1) (F mod 1048576 + sz + 1 - 1048576)); lia).
  assert (Q3 : (F + (sz + 1) + sz) / 1048576 = b + 1) by (symmetry; apply (Z.div_unique_pos _ 1048576 (b + 1) (F mod 1048576 + sz + 1 + sz - 1048576)); lia).
  assert (Hw3 : SPA segsA (JJ G) (mkDj sz D1r) rho' tp (tr, mkCfg ms md)).
  { unfold mkDj. rewrite <- HP. apply SPA_refacts; [exact Hw2 | exact Dj_fb |]. cbn [ax_S ax_setS set_objs ss_facts]. intros HFX. apply Forall_app. split; [exact HFX|].
    unfold F_dj, vF, add. pose proof (u64_lit F) as _.
    assert (V179 : bv_unsigned (rw rho' 179%positive) = F) by (rewrite E179; exact H179).
    apply Forall_cons. { cbn [holds eval]. rewrite add_val, V179, !u64_lit by lia. rewrite Z.mod_small by lia. lia. }
    apply Forall_cons. { cbn [holds eval branch_taken]. rewrite Bool.negb_true_iff. unfold bv_eqb. rewrite !srl_val, !add_val, V179, !u64_lit by lia. change (20 mod 64) with 20.
      rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 20) with 1048576. rewrite !Z.mod_small by lia. rewrite Q2, Q3. intros X. apply Z.eqb_neq in X. exact (X eq_refl). }
    apply Forall_nil. }

  exists (rho_sub rho' sD). split; [|split].
  - apply (SPA_entails segsA (JJ G) NPRE (mkDj sz D1r) Jhs sD rho' tp _ ENT_D SID_D (JJ_stable G NPRE ltac:(lia))). exact Hw3.
  - assert (HV4 : forall i, In i [170; 171; 177; 178]%positive -> rw (rho_sub rho' sD) i = rw rhoL i).
    { intros i Hi. rewrite (ids4_rw sD rho' i IDS_D Hi). reflexivity. }
    pose proof OWV4 as W. cbn [forallb] in W. apply andb_prop in W as [W1 W]. apply andb_prop in W as [W2 W]. apply andb_prop in W as [W3 _].
    assert (HVb : forall v, existsb (Pos.eqb v) [170; 171; 177; 178]%positive = true -> rw rhoL v = rw (rho_sub rho' sD) v).
    { intros v Hvv. symmetry. apply HV4. apply existsb_exists in Hvv as (x & Hx & Ex). apply Pos.eqb_eq in Ex. subst. exact Hx. }
    assert (RG : forall o, obj_vars_all (fun i => existsb (Pos.eqb i) [170; 171; 177; 178]%positive) o = true -> obj_range (rho_sub rho' sD) o = obj_range rhoL o).
    { intros o Ho. apply (obj_range_agree_vars _ rhoL (rho_sub rho' sD) o HVb (fun l => eq_refl) Ho). }
    pose proof (Forall_inv HDs) as WD1. pose proof (Forall_inv (Forall_inv_tail HDs)) as WD2. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail HDs))) as WD3.
    split; [|split; [exact Hj | split; [rewrite (HV4 178%positive ltac:(cbn; tauto)); exact H178 | split; [|split]]]].
    + split; [rewrite (HV4 177%positive ltac:(cbn; tauto)); exact K177|]. split; [rewrite (HV4 170%positive ltac:(cbn; tauto)); exact KW0|].
      split; [intros a Ha; apply KD1; rewrite <- (RG _ W1); exact Ha | intros a Ha; apply KD2; rewrite <- (RG _ W2); exact Ha].
    + cbn [rw rho_sub]. rewrite SD179. unfold add, vF. cbn [eval]. rewrite add_val, E179, H179, !u64_lit by lia. rewrite Z.mod_small by lia. reflexivity.
    + eapply (ro_win_vars segsA (fun i => existsb (Pos.eqb i) [170; 171; 177; 178]%positive) rho'); [intros v Hv; exact (HVb v Hv) | intros l; reflexivity | intros a; reflexivity | exact W3 |].
      unfold rho'. apply ro_win_absorb; [exact HROs|]. intros a Ha. apply VOUT; intros Hin; unfold O_slotN, carved in Ha; rewrite obj_range_mk in Ha by lia; cbn [fst snd] in Ha;
          rewrite (slotN_addr_val rhoL (dN G) K177 ltac:(unfold DNMAX in HDN; lia)) in Ha; unfold MAP1, STORE in *; lia.
    + apply Forall_cons; [intros a Ha; apply WD1; rewrite <- (RG _ W3); exact Ha|].
      apply Forall_cons; [intros a Ha; apply WD2; rewrite <- (RG O_nn ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc)); exact Ha|].
      apply Forall_cons; [|apply Forall_nil]. intros a. unfold O_tf, carved. rewrite obj_range_mk by (unfold STORE; lia). intros Ha. apply WD3. unfold O_tf, carved. rewrite obj_range_mk by (unfold STORE; lia). exact Ha.
  - assert (MR : (F + (sz + 1)) mod 1048576 = F mod 1048576 + sz + 1 - 1048576) by (symmetry; apply (Z.mod_unique_pos _ 1048576 (b + 1) _); lia). lia.
Qed.

Lemma OW_slotN : ltac2:(tb__ "0|0|
S35S28S14S95S99S9bA1A2S2aA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma nbK_agree : ltac2:(tb__ "0|0|
S5cS1S1SbS95R2R1A3S6bR4R3A2S6bR5R3A2F_;F_;Frho';Frho;FG;").
Proof.
  intros G rho rho' Hag (A & B & C & D & E). split; [eapply insK_agree; eauto|]. split; [exact B|].
  split; [rewrite <- C; f_equal; symmetry; apply (proj1 Hag); unfold NXD; lia|].
  split; [eapply ro_win_agree; [exact Hag | apply OW_slotN | exact D] | eapply winDFP_agree; [exact Hag | apply OW_slotN | exact E]].
Qed.

Lemma OW_j : ltac2:(tb__ "0|0|
S35S28S116S0S14S95A1S25S0S99S9bA1S25S0Sa2S25S0Sa1S9cA1S26S0A1A3A3A3A3S2aA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma jK_agree : ltac2:(tb__ "0|0|
S5cS3aS1S1SbS95R2R1A3S67R5R4R3A3S67R6R5R3A3F_;F_;Frho';Frho;FS;FG;").
Proof.
  intros G S rho rho' Hag (A & B & C & D & E & F).
  pose proof OW_j as W. cbn [forallb] in W. apply andb_prop in W as [W1 W]. apply andb_prop in W as [W2 W]. apply andb_prop in W as [W3 _].
  pose proof Hag as (Hw & Hl & Hm).
  split; [eapply insK_agree; eauto|]. split; [exact B|]. split; [rewrite <- (Hw 178%positive) by (unfold NXD; lia); exact C|].
  split; [rewrite <- (Hw 179%positive) by (unfold NXD; lia); exact D|]. split; [eapply ro_win_agree; [exact Hag | exact W1 | exact E]|].
  pose proof (Forall_inv F) as F1. pose proof (Forall_inv (Forall_inv_tail F)) as F2. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail F))) as F3.
  repeat apply Forall_cons; [| | | apply Forall_nil]; (eapply winDFP_agree; [exact Hag | | ]); [exact W1 | exact F1 | exact W2 | exact F2 | exact W3 | exact F3].
Qed.

Definition armsF : Prop := ltac2:(tb__ "0|1|
S5cS3aS27S4aQ40A1A1S1S65R4R2A2S3eS3dSf5R5A1S120A2S3dSf5VG0;A1Sf6VG0;A1A2A2S67R6R5R3A3S66R7R6A2S3fS3dS41R7Z100000M0A2Vsz;A2G0A2S38S119S42S40R8G0A2A1S2dS3aS5eR9A1A2A2A1S11dS3cVok;S4dS3cS63RaA1VJhs;R7R8A5S64A4F_;F_;F_;F_;F_;F_;Frho;Ftp;FS;FG;").
Definition earmsF : Prop := ltac2:(tb__ "0|1|
S5cS3aS27S4aQ40A1A1S1S65R4R2A2S3eS3dSf5R5A1S120A2S3dSf5VG0;A1Sf6VG0;A1A2A2S67R6R5R3A3S66R7R6A2S3fS3dS41R7Z100000M0A2Vsz;A2G0A2S38S119S42S40R8G0A2A1S2dS3aS5eR9A1A2A2A1S11cS3cS4dS3cS63RaA1VJhs;R7R8A5S64A3F_;F_;F_;F_;F_;F_;Frho;Ftp;FS;FG;").

Lemma jall_cont : ltac2:(tb__ "0|1|
S6fS5cS3aS27S4aQ40A1A1S1S65R4R2A2S3eS3dSf5R5A1S120A2S3dSf5VG0;A1Sf6VG0;A1A2A2S67R6R5R3A3S66R7R6A2S3fS3dS41R7Z100000M0A2Vsz;A2G0A2S11dS3cVok;S4dS3cS63R9A1VJhs;R6R7A5S64A4F_;F_;F_;F_;F_;Frho;Ftp;FS;FG;F_;").
Proof.
  intros HF G S tp rho HG Hbud HJK HHS Hns.
  destruct (lt_dec (Z.to_nat (S / 1048576)) (length (dFB G))) as [Hbl|Hnbl]; [exact (jx_cont G S tp rho HG Hbud HJK HHS Hbl Hns) | exact (HF G S tp rho HG Hbud HJK HHS Hns Hnbl)].
Qed.

Lemma ejall_cont : ltac2:(tb__ "0|1|
S71S5cS3aS27S4aQ40A1A1S1S65R4R2A2S3eS3dSf5R5A1S120A2S3dSf5VG0;A1Sf6VG0;A1A2A2S67R6R5R3A3S66R7R6A2S3fS3dS41R7Z100000M0A2Vsz;A2G0A2S11cS3cS4dS3cS63R9A1VJhs;R6R7A5S64A3F_;F_;F_;F_;F_;Frho;Ftp;FS;FG;F_;").
Proof.
  intros HF G S tp rho HG Hbud HJK HHS Hns.
  destruct (lt_dec (Z.to_nat (S / 1048576)) (length (dFB G))) as [Hbl|Hnbl]; [exact (ejx_cont G S tp rho HG Hbud HJK HHS Hbl Hns) | exact (HF G S tp rho HG Hbud HJK HHS Hns Hnbl)].
Qed.

Lemma n_main : ltac2:(tb__ "0|1|
S6fS5cS27S4aQ40A1A1S1S65R3R2A2S3eS3dSf5R4A1S120A2S3dSf5VG0;A1Sf6VG0;A1A2A2S6bR5R3A2S3fS3dS41S5fR6A1Z100000M0A2Vsz;A2G0A2S11dS3cVok;S4dS3cS63R7A1VNBs;R5R6A5S64A4F_;F_;F_;F_;Frho;Ftp;FG;F_;").
Proof.
  intros HF G tp rho HG Hbud HNK Hns.
  eapply triple_conseq with (P := fun w => exists rho', jK G (dF G) rho' /\ SPA segsA (JJ G) (mkIn sz NBs) rho' tp w); [| intros w Hw; exact Hw |].
  { intros w Hw. destruct (glue_n G tp rho w Hw HNK Hns) as (rho' & S' & K'). exists rho'. split; [exact K' | exact S']. }
  apply triple_ex. intros rho'. apply triple_pure. intros HJK. apply triple1_triple.
  eapply (stage_run (JJ G)); [apply JJ_ok | apply JJ_stable; lia | exact RUNN | discriminate | exact NB_len | apply Pos.leb_le; reflexivity |].
  intros L rhoL [<-|[]] Hag. cbn [la_state]. pose proof (jK_agree G (dF G) rho' rhoL Hag HJK) as HJK'.
  eapply triple_conseq with (P := fun w => exists rho'', jK G (dF G) rho'' /\ SPA segsA (JJ G) Jhs rho'' tp w); [| intros w Hw; exact Hw |].
  { intros w Hw. destruct (glue_j G (dF G) tp rhoL w Hw HJK') as (rho'' & S'' & K''). exists rho''. split; [exact K'' | exact S'']. }
  apply triple_ex. intros rho''. apply triple_pure. intros HJK''.
  apply (jall_cont HF G (dF G) tp rho'' HG Hbud HJK''); [left; reflexivity | exact Hns].
Qed.

Lemma en_main : ltac2:(tb__ "0|1|
S71S5cS27S4aQ40A1A1S1S65R3R2A2S3eS3dSf5R4A1S120A2S3dSf5VG0;A1Sf6VG0;A1A2A2S6bR5R3A2S3fS3dS41S5fR6A1Z100000M0A2Vsz;A2G0A2S11cS3cS4dS3cS63R7A1VNBs;R5R6A5S64A3F_;F_;F_;F_;Frho;Ftp;FG;F_;").
Proof.
  intros HF G tp rho HG Hbud HNK Hns.
  eapply etriple_conseq with (P := fun w => exists rho', jK G (dF G) rho' /\ SPA segsA (JJ G) (mkIn sz NBs) rho' tp w); [| intros w Hw; exact Hw |].
  { intros w Hw. destruct (glue_n G tp rho w Hw HNK Hns) as (rho' & S' & K'). exists rho'. split; [exact K' | exact S']. }
  apply etriple_ex. intros rho'. apply etriple_pure. intros HJK.
  eapply (estage_run (JJ G)); [apply JJ_stable; lia | exact RUNN | discriminate | exact NB_len | apply Pos.leb_le; reflexivity |].
  intros L rhoL [<-|[]] Hag. cbn [la_state]. pose proof (jK_agree G (dF G) rho' rhoL Hag HJK) as HJK'.
  eapply etriple_conseq with (P := fun w => exists rho'', jK G (dF G) rho'' /\ SPA segsA (JJ G) Jhs rho'' tp w); [| intros w Hw; exact Hw |].
  { intros w Hw. destruct (glue_j G (dF G) tp rhoL w Hw HJK') as (rho'' & S'' & K''). exists rho''. split; [exact K'' | exact S'']. }
  apply etriple_ex. intros rho''. apply etriple_pure. intros HJK''.
  apply (ejall_cont HF G (dF G) tp rho'' HG Hbud HJK''); [left; reflexivity | exact Hns].
Qed.

Lemma d_main : ltac2:(tb__ "0|1|
S6fS5cS27S4aQ40A1A1S1S65R3R2A2S3eS3dSf5R4A1S120A2S3dSf5VG0;A1Sf6VG0;A1A2A2S6bR5R3A2S3eZ100000M0S3dS41S5fR6A1G0A2Vsz;A2A2S11dS3cVok;S4dS3cS63R7A1VNBs;R5R6A5S64A4F_;F_;F_;F_;Frho;Ftp;FG;F_;").
Proof.
  intros HF G tp rho HG Hbud HNK Hstr.
  eapply triple_conseq with (P := fun w => exists rho', dK G rho' /\ SPA segsA (JJ G) (mkI5d sz NBs) rho' tp w); [| intros w Hw; exact Hw |].
  { intros w Hw. destruct (glue_d G tp rho w Hw HNK Hstr) as (rho' & S' & K'). exists rho'. split; [exact K' | exact S']. }
  apply triple_ex. intros rho'. apply triple_pure. intros HDK. apply triple1_triple.
  eapply (stage_run (JJ G)); [apply JJ_ok | apply JJ_stable; lia | exact RUND | discriminate | exact NB_len | apply Pos.leb_le; reflexivity |].
  intros L rhoL [<-|[]] Hag. cbn [la_state].
  eapply triple_conseq with (P := fun w => exists rho'', (jK G (dF G + (sz + 1)) rho'' /\ (dF G + (sz + 1)) mod 1048576 + sz < 1048576) /\ SPA segsA (JJ G) Jhs rho'' tp w); [| intros w Hw; exact Hw |].
  { intros w Hw. destruct (glue_dj G rho' rhoL tp w Hw Hag HDK Hstr) as (rho'' & S'' & K'' & M''). exists rho''. split; [exact (conj K'' M'') | exact S'']. }
  apply triple_ex. intros rho''. apply triple_pure. intros [HJK'' HM''].
  assert (HHS : HS G (dF G + (sz + 1))) by (right; split; [lia | exact Hstr]).
  exact (jall_cont HF G (dF G + (sz + 1)) tp rho'' HG Hbud HJK'' HHS HM'').
Qed.

Lemma ed_main : ltac2:(tb__ "0|1|
S71S5cS27S4aQ40A1A1S1S65R3R2A2S3eS3dSf5R4A1S120A2S3dSf5VG0;A1Sf6VG0;A1A2A2S6bR5R3A2S3eZ100000M0S3dS41S5fR6A1G0A2Vsz;A2A2S11cS3cS4dS3cS63R7A1VNBs;R5R6A5S64A3F_;F_;F_;F_;Frho;Ftp;FG;F_;").
Proof.
  intros HF G tp rho HG Hbud HNK Hstr.
  eapply etriple_conseq with (P := fun w => exists rho', dK G rho' /\ SPA segsA (JJ G) (mkI5d sz NBs) rho' tp w); [| intros w Hw; exact Hw |].
  { intros w Hw. destruct (glue_d G tp rho w Hw HNK Hstr) as (rho' & S' & K'). exists rho'. split; [exact K' | exact S']. }
  apply etriple_ex. intros rho'. apply etriple_pure. intros HDK.
  eapply (estage_run (JJ G)); [apply JJ_stable; lia | exact RUND | discriminate | exact NB_len | apply Pos.leb_le; reflexivity |].
  intros L rhoL [<-|[]] Hag. cbn [la_state].
  eapply etriple_conseq with (P := fun w => exists rho'', (jK G (dF G + (sz + 1)) rho'' /\ (dF G + (sz + 1)) mod 1048576 + sz < 1048576) /\ SPA segsA (JJ G) Jhs rho'' tp w); [| intros w Hw; exact Hw |].
  { intros w Hw. destruct (glue_dj G rho' rhoL tp w Hw Hag HDK Hstr) as (rho'' & S'' & K'' & M''). exists rho''. split; [exact (conj K'' M'') | exact S'']. }
  apply etriple_ex. intros rho''. apply etriple_pure. intros [HJK'' HM''].
  assert (HHS : HS G (dF G + (sz + 1))) by (right; split; [lia | exact Hstr]).
  exact (ejall_cont HF G (dF G + (sz + 1)) tp rho'' HG Hbud HJK'' HHS HM'').
Qed.

Lemma frames_cont : ltac2:(tb__ "0|0|
S6fS5cS27S4aQ40A1A1S1S65R3R2A2S3eS3dSf5R4A1S120A2S3dSf5VG0;A1Sf6VG0;A1A2A2S6bR5R3A2S11dS3cVok;S4dS3cS63R6A1VNBs;R4R5A5S64A4F_;F_;F_;Frho;Ftp;FG;F_;").
Proof.
  intros HF G tp rho HG Hbud HNK.
  destruct (Z_lt_le_dec (dF G mod 1048576 + sz) 1048576) as [Hns|Hs]; [exact (n_main HF G tp rho HG Hbud HNK Hns) | exact (d_main HF G tp rho HG Hbud HNK Hs)].
Qed.

Lemma eframes_cont : ltac2:(tb__ "0|0|
S71S5cS27S4aQ40A1A1S1S65R3R2A2S3eS3dSf5R4A1S120A2S3dSf5VG0;A1Sf6VG0;A1A2A2S6bR5R3A2S11cS3cS4dS3cS63R6A1VNBs;R4R5A5S64A3F_;F_;F_;Frho;Ftp;FG;F_;").
Proof.
  intros HF G tp rho HG Hbud HNK.
  destruct (Z_lt_le_dec (dF G mod 1048576 + sz) 1048576) as [Hns|Hs]; [exact (en_main HF G tp rho HG Hbud HNK Hns) | exact (ed_main HF G tp rho HG Hbud HNK Hs)].
Qed.

Variable EBs : axst.
Hypothesis RUNB1 : ltac2:(tb__ "0|0|
S35S27S52A1S9aUbb8S25S3aZ7ebecS25S3aZ6bf18S26S3aA1A3A3ScdVI3s;A1A3S25S52S53VEBs;S127A2S26S52A1A3A3").
Let S_b1 : sstate := ltac2:(tb__ "0|0|
S13ScVSI3;A1SfVSI3;A1S16VSI3;A1S15VSI3;A1S17VSI3;A1S29S0S6VSI3;A1S25S0S99S5Z0A1A1S26S0A1A3A3S7VSI3;A1S95SaVSI3;A1A9").
Let S_b2 : sstate := ltac2:(tb__ "0|1|
S13ScVSI3;A1SfVSI3;A1S16VSI3;A1S15VSI3;A1S17VSI3;A1S29S0S29S0S6VSI3;A1S25S0S99S5Z0A1A1S26S0A1M0A3A3S25S0SbaG0A3A3S7VSI3;A1S95SaVSI3;A1A9").
Hypothesis B1_swf : swf S_b1 = true.
Hypothesis B2_swf : swf S_b2 = true.
Hypothesis B2_fb : ltac2:(tb__ "0|0|
S35S28S116S4S10S95A1S29S4S7VSI3;A1S26S4A1A3A3S2aA3").

Lemma OW_mu : ltac2:(tb__ "0|0|
S35S28S14S95SbaA2S2aA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma glue_b : ltac2:(tb__ "0|6|
S1S11bS4dS3cS63VG0;A1M0VI3s;R2Vtp0;R1A6S69VG0;R3A2S38S119S42S40S3dS5dVG0;A1Z1A2M1Z10000M2A2M3A1S2dS3aS60VG0;A1A2M4A2A1S36S4dS3cG0ScdVI3s;A1R5Vtp0;R4A6S36S123S3cR5S99S5Z0M5A1A1A3S36S123S3cR5SbaA3S36S35S3aS46G4A1G3A3S35S3aS41G1G2A2G5A3A2A2A2A2F_;F_;F_;Fw;Frho;").
Proof.
  intros rho w H HIK Hj. destruct w as [tr [ms md]].
  pose proof H as [HsmA [HREL [HK [[HM HV] _]]]].
  pose proof HIK as (K177 & KW0 & KD1 & KD2).
  pose proof (dm_N _ _ HM) as [HN _].
  destruct (kd_room segsA K NPRE HKD G0 rho tp0 _ _ HK (conj HM HV)) as [_ HDN].
  set (j := (dN G0 + 1) / 65536) in *.
  assert (Hjb : 0 <= j < MAP1N).
  { unfold j, MAP1N. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; unfold DNMAX in HDN; lia]. }
  pose proof (dm_map1_len _ _ HM) as HL. unfold nblk in HL.
  destruct (Z.eqb_spec (dN G0) 0); [lia|]. destruct (Z.eqb_spec (dN G0 + 1) 0); [lia|].
  assert (HLj : Z.of_nat (length (dNB G0)) = j /\ (dN G0 + 1) mod 65536 = 0).
  { pose proof (Z.div_mod (dN G0) 65536 ltac:(lia)). pose proof (Z.div_mod (dN G0 + 1) 65536 ltac:(lia)).
    pose proof (Z.mod_pos_bound (dN G0) 65536 ltac:(lia)). pose proof (Z.mod_pos_bound (dN G0 + 1) 65536 ltac:(lia)).
    assert (Z.of_nat (Z.to_nat j) = j) by (apply Z2Nat.id; lia). unfold j in *. nia. }
  destruct HLj as [HLj Hmod].
  pose proof (dm_map1 _ _ HM j Hjb) as Hslot. rewrite (@nth_overflow _ (dNB G0) (Z.to_nat j) 0) in Hslot by lia.
  pose proof (dm_mu _ _ HM) as Hmu.
  pose proof alloc_ceiling_valD as ACV.
  assert (SA : bv_unsigned (eval rho slotN_addr) = MAP1 + 8 * j) by (unfold j; apply slotN_addr_val; [exact K177 | unfold DNMAX in HDN; lia]).
  assert (CIVs : cells_in_view rho (rd_of segsA (rm rho)) (MAP1 + 8 * j) [(0, 8%nat, SLit 0)]).
  { unfold cells_in_view. constructor; [|constructor]. intros jj Hjj.
    refine (civ_cell rho (rm rho) (MAP1 + 8 * j) 0 8 0 (SLit 0) ltac:(rewrite Z.add_0_r; exact Hslot) _ _ _ jj Hjj); [reflexivity | unfold MAP1; lia | unfold MAP1, MAP1N in *; lia]. }
  assert (CIVm : cells_in_view rho (rd_of segsA (rm rho)) 0 [(NODESMU, 4%nat, SLit 0)]).
  { unfold cells_in_view. constructor; [|constructor]. intros jj Hjj.
    refine (civ_cell rho (rm rho) 0 NODESMU 4 0 (SLit 0) ltac:(exact Hmu) _ _ _ jj Hjj); [reflexivity | unfold NODESMU; lia | unfold NODESMU; lia]. }
  pose proof (SPA_facts segsA _ _ _ _ _ H) as HFall.
  pose proof (holds_inclb rho _ _ I3_F HFall) as HF3. apply Forall_app in HF3 as [HFD HF3]. apply Forall_app in HF3 as [HFt HFn].
  assert (HP : bv_unsigned (rw rho 171%positive) <= DEPOT + 4 * 2 ^ 20 - 4).
  { pose proof (proj1 (Forall_forall _ _) HFt (SPUle vP (SLit (DEPOT + 4 * 2^20 - 4))) ltac:(unfold F_tw; cbn; tauto)) as X1.
    cbn [holds eval vP] in X1. unfold DEPOT in *. rewrite u64_lit in X1 by lia. exact X1. }
  pose proof (proj1 HsmA) as Hsm. unfold virt in Hsm. cbn [fst snd cfg_ms cfg_model w_tr w_cfg] in Hsm.
  split; [|split; [|split; [|split; [exact HLj | exact Hmod]]]].
  2:{ exists slotN_addr, 0, 8%nat, (SLit 0). rewrite SA. split; [reflexivity|]. unfold MAP1, MAP1N in *. repeat (split; [lia|]). exact CIVs. }
  2:{ exists (SLit 0), NODESMU, 4%nat, (SLit 0). cbn [eval]. rewrite u64_lit by lia. split; [reflexivity|]. unfold NODESMU. repeat (split; [lia|]). exact CIVm. }

  assert (H1 : SPA segsA (JJ G0) (ax_setS I3s S_b1) rho tp0 (tr, mkCfg ms md)).
  { unfold S_b1, O_slotN.
    apply (SPA_carve_obj segsA (JJ G0) rho I3s tp0 _ slotN_addr 0 8 [(0, 8%nat, SLit 0)] NXD H B1_swf).
    - rewrite I3_nx. apply Pos.le_refl.
    - lia. - lia. - lia. - lia.
    - rewrite SA. unfold MAP1. lia.
    - rewrite SA. unfold MAP1, MAP1N in *. lia.
    - unfold cells_inside. constructor; [cbn; lia|constructor].
    - rewrite SA.
      eapply (objs_ranges_ext rho SI3 _ _ [O_tw vW; O_nid vN] _ _ Hsm ltac:(intros o Ho; exact Ho) I3_skel HFD ltac:(first [assumption | eapply TOPr_of_REL; eassumption | eapply TOPr_of_JJ; eassumption])); [unfold STORE, MAP1; lia | unfold MAP1, MAP1N in *; lia | lia |].
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      + unfold O_tw, carved, ranges_disjoint. rewrite obj_range_mk by lia. cbn [fst snd eval vP]. unfold DEPOT, MAP1 in *. lia.
      + unfold O_nid, carved, ranges_disjoint. rewrite obj_range_mk by (unfold NIDS; lia). cbn [fst snd eval]. rewrite u64_lit by lia. unfold NIDS, MAP1. lia.
    - rewrite SA. intros off Hoff. unfold MAP1, MAP1N in *. split; [apply wok_of_imageA; lia | apply rd_of_imageA; lia].
    - rewrite SA. exact CIVs.
    - unfold xwords_clear. cbn [ax_X]. rewrite I3_X. intros rr y jj []. }

  assert (H2 : SPA segsA (JJ G0) (ax_setS (ax_setS I3s S_b1) S_b2) rho tp0 (tr, mkCfg ms md)).
  { unfold S_b2, O_mu, carved.
    apply (SPA_carve_obj segsA (JJ G0) rho (ax_setS I3s S_b1) tp0 _ (SLit 0) NODESMU (NODESMU + 4) [(NODESMU, 4%nat, SLit 0)] NXD H1 B2_swf);
      cbn [ax_S ax_setS ss_next ss_objs eval]; rewrite ?u64_lit by lia; unfold NODESMU;
      try (lazymatch goal with |- _ <= _ => lia | |- _ < _ => lia | |- _ <= _ < _ => lia | |- _ <= _ <= _ => lia | |- _ < _ <= _ => lia end).
    - apply Pos.le_refl.
    - unfold cells_inside. constructor; [cbn; lia|constructor].
    - pose proof (proj1 H1) as Hsm1. unfold smatchA, virt in Hsm1. cbn [fst snd cfg_ms cfg_model w_tr w_cfg ax_S ax_setS] in Hsm1. apply proj1 in Hsm1.
      apply Forall_app. split.
      + eapply (objs_ranges_ext rho SI3 _ _ [O_tw vW; O_nid vN] _ _ Hsm ltac:(intros o Ho; exact Ho) I3_skel HFD ltac:(first [assumption | eapply TOPr_of_REL; eassumption | eapply TOPr_of_JJ; eassumption])); [unfold STORE; lia | unfold MAP1, MAP1N in *; lia | lia |].
        apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
        * unfold O_tw, carved, ranges_disjoint. rewrite obj_range_mk by lia. cbn [fst snd eval vP]. unfold DEPOT in *. lia.
        * unfold O_nid, carved, ranges_disjoint. rewrite obj_range_mk by (unfold NIDS; lia). cbn [fst snd eval]. rewrite u64_lit by lia. unfold NIDS. lia.
      + apply Forall_cons; [|apply Forall_nil]. unfold O_slotN, carved, ranges_disjoint. rewrite obj_range_mk by lia. cbn [fst snd]. rewrite SA. unfold MAP1. lia.
    - intros off Hoff. split; [apply wok_of_imageA; lia | apply rd_of_imageA; lia].
    - exact CIVm.
    - unfold xwords_clear. cbn [ax_X ax_setS]. rewrite I3_X. intros rr y jj [].
  }

  assert (H3 : SPA segsA (JJ G0) (ax_with_facts (ax_setS (ax_setS I3s S_b1) S_b2) (ss_facts SI3 ++ [])) rho tp0 (tr, mkCfg ms md)).
  { apply SPA_refacts; [exact H2 | exact B2_fb |]. cbn [ax_S ax_setS ss_facts]. intros HFB. apply Forall_app. split; [exact HFB | apply Forall_nil]. }
  unfold ax_with_facts in H3. rewrite !ax_setS_setS in H3.
  unfold mkI3b, extN. fold SI3.
  replace (ss_objs SI3 ++ [O_slotN (SLit 0); O_mu]) with ((ss_objs SI3 ++ [O_slotN (SLit 0)]) ++ [O_mu]) by (rewrite <- app_assoc; reflexivity).
  exact H3.
Qed.

Lemma triple_spin_ent : ltac2:(tb__ "0|0|
S50S55S55S13cS1S27S4aQ40A1A1S11fS4fS3cVok;R7A3S4eS3cS98R8A3S35S27S52A1S9aU2S25S3aScS51R8A1A1S26S3aA1A3R8A3S25S52S53R7S126A2S26S52A1A3A3S35S28S54R8R9R7A3S2aA3S35S28S13aR8S98A2S2aA3S35S28SaS51RbA1A1S30A3S14aS98S8S51RcA1A1A2S11dS3cVok;S4dS3cReRdRaR9A5R8A4F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho;Fs;FA2;FA;FJ;").
Proof.
  intros J A A2 s rho tp Q Hok Hst Hrun ENT SID Hlen Hnx.
  apply (@triple_conseq segsA ok (fun w => exists rho', SPA segsA J A rho' tp w) _ Q Q); [intros w Hw; exists rho; exact Hw | intros w Hw; exact Hw |].
  apply triple_loop. apply triple1_ex. intros rho'.
  eapply (stage_run J); [exact Hok | exact Hst | exact Hrun | discriminate | exact Hlen | exact Hnx |].
  intros L rhoL [<-|[]] Hag. cbn [la_state].
  eapply triple_conseq; [| intros w Hw; exact Hw | apply triple_refl]. intros w Hw. left.
  exists (rho_sub rhoL s). apply (SPA_entails segsA J NPRE A2 A s rhoL tp _ ENT SID Hst). exact Hw.
Qed.

Hypothesis EB_X : ax_X EBs = [].
Hypothesis EB_len : ltac2:(tb__ "0|0|
S35S28SaS51VEBs;A1A1S30A3").
Hypothesis EB_nx : ltac2:(tb__ "0|0|
S35S3bS8S51VEBs;A1A1S95A3").
Hypothesis EB_instr : ltac2:(tb__ "0|0|
S35S2fS156A1S128S3cScS51VEBs;A1A1A2S31S156S158A2A3").
Hypothesis EB_r17 : ltac2:(tb__ "0|0|
S35S2S12S51VEBs;A1Z11A2S5ZdeA1A3").
Hypothesis EB_r10 : ltac2:(tb__ "0|0|
S35S2S12S51VEBs;A1ZaA2S5Z0A1A3").
Hypothesis EB_r11 : ltac2:(tb__ "0|0|
S35S2S12S51VEBs;A1ZbA2S5Sf7A1A3").
Hypothesis EB_r12 : ltac2:(tb__ "0|0|
S35S2S12S51VEBs;A1ZcA2S5Z3A1A3").
Hypothesis EB_r13 : ltac2:(tb__ "0|0|
S35S2S12S51VEBs;A1ZdA2S5Z22A1A3").
Hypothesis EB_r14 : ltac2:(tb__ "0|0|
S35S2S12S51VEBs;A1ZeA2S5ZffffffffffffffffA1A3").
Hypothesis EB_r15 : ltac2:(tb__ "0|0|
S35S2S12S51VEBs;A1ZfA2S5Z0A1A3").
Hypothesis EB_F : ltac2:(tb__ "0|0|
S35S28S125S29S4S9eS29S4Sa5Sa7A3A3S7S51VEBs;A1A1A2S2aA3").
Hypothesis EB_skel : ltac2:(tb__ "0|2|
S35S27S2bS2bS2S2A2S2A2M0A1S113S0G0S122S6S51VEBs;A1A1A4S113S0G0S122S29S0S29S0S25S0S138S25S0Sa3S26S0A1M1A3A3S29S0S137Sa4A3A3S25S0S97S96A1S25S0S9dS9fA1S25S0S99S5Z0A1A1S25S0SbaG1A3A3A3A3A3A4A3").
Hypothesis EB_fbO : ltac2:(tb__ "0|0|
S35S28S116S4S10S149S95A1A1S29S4S7S51VEBs;A1A1Sd7A3A3S2aA3").
Hypothesis EB_fbF : ltac2:(tb__ "0|0|
S35S28S116S4S10S95A1S29S4S7S51VEBs;A1A1Sc4A3A3S2aA3").

Variables SPNs SPN2s : axst. Variable sP : wsub.
Hypothesis RUNBF : ltac2:(tb__ "0|0|
S35S27S52A1S9aUbb9S25S3aZ7ebecS25S3aZ6bf18S26S3aA1A3A3Se7VEBs;A1A3S25S52S53VSPNs;S126A2S26S52A1A3A3").
Hypothesis SPN_len : ltac2:(tb__ "0|0|
S35S28SaS51VSPNs;A1A1S30A3").
Hypothesis SPN_nx : ltac2:(tb__ "0|0|
S35S28S14cS98S8S51VSPNs;A1A1A2S2aA3").
Hypothesis RUNSP : ltac2:(tb__ "0|0|
S35S27S52A1S9aU2S25S3aScS51VSPNs;A1A1S26S3aA1A3VSPNs;A3S25S52S53VSPN2s;S126A2S26S52A1A3A3").
Hypothesis ENT_P : ltac2:(tb__ "0|0|
S35S28S54VSPN2s;VSPNs;VsP;A3S2aA3").
Hypothesis SID_P : ltac2:(tb__ "0|0|
S35S28S13aVsP;S98A2S2aA3").

Lemma fail_spin : ltac2:(tb__ "0|0|
S1S11dS3cVok;S4dS3cS63VG0;A1S15cVEBs;S5S49Q40S131S130A1A2A1A2R1Vtp0;A5S64A4Frho;").
Proof.
  intros rho.
  eapply triple_conseq with (P := SPA segsA (JJ G0) (mkFAIL EBs) rho tp0); [| intros w Hw; exact Hw |].
  { intros w Hw. unfold mkFAIL. apply SPA_refacts; [exact Hw | cbn [ax_S A_after ax_setS S_after ss_next]; rewrite EB_nx; exact EB_fbF |].
    cbn [ax_S A_after ax_setS S_after ss_facts]. intros HF. apply Forall_app. split; [exact HF|].
    pose proof (holds_inclb rho _ _ EB_F HF) as HF3. apply Forall_app in HF3 as [HFD _].
    destruct w as [tr [ms md]]. pose proof (proj1 (proj1 Hw)) as Hsm. unfold virt in Hsm. cbn [fst snd cfg_ms cfg_model w_tr w_cfg ax_S A_after ax_setS] in Hsm.
    assert (Hhigh : holds rho F_sp_high).
    { apply (proj1 (Forall_forall _ _) HFD). unfold F_D, pre_facts. apply in_or_app. left. cbn. tauto. }
    pose proof EB_skel as SK. destruct (ss_objs (ax_S EBs)) as [|osw rest] eqn:EO; [cbn in SK; discriminate|].
    cbn [map app] in SK. assert (SKsw : skel osw = (SVar 10, SVar V_DEPTH, SLit 0)) by exact (f_equal (hd (skel osw)) SK).
    destruct (sw_range_gen segsA rho _ _ osw Hsm ltac:(left; reflexivity) SKsw Hhigh) as (SW1 & SW2 & SW3).
    pose proof alloc_ceiling_valD as ACV. pose proof (urange (rw rho 10%positive)) as R10.
    unfold F_f. apply Forall_cons; [|apply Forall_nil]. cbn [holds eval branch_taken]. unfold bv_eqb.
    rewrite add_val, !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
    change ((-192) mod 2 ^ 64) with (2 ^ 64 - 192). change (0 mod 2 ^ 64) with 0.
    assert (E : (bv_unsigned (rw rho 10%positive) + (2 ^ 64 - 192)) mod 2 ^ 64 = bv_unsigned (rw rho 10%positive) - 192).
    { symmetry. apply Z.mod_unique_pos with 1; lia. }
    rewrite E. intros X. apply Z.eqb_eq in X. lia. }
  apply triple1_triple.
  eapply (stage_run (JJ G0)); [apply JJ_ok | apply JJ_stable; lia | exact RUNBF | discriminate | | |].
  { cbn [mkFAIL ax_with_facts ax_S ax_setS with_facts A_after S_after ss_lenient]. exact EB_len. }
  { cbn [mkFAIL ax_with_facts ax_S ax_setS with_facts A_after S_after ss_next]. rewrite EB_nx. apply Pos.leb_le. reflexivity. }
  intros L rhoL [<-|[]] Hag. cbn [la_state].
  apply (triple_spin_ent (JJ G0) SPNs SPN2s sP rhoL tp0 QD (JJ_ok G0) (JJ_stable G0 NPRE ltac:(lia)) RUNSP ENT_P SID_P SPN_len).
  apply Pos.leb_le. exact SPN_nx.
Qed.

Definition PDb (a : word) : pend := ltac2:(tb__ "0|4|
S1S27S4aQ40M0A1M1A1S12aS36S117S2bG1G1A2S2cG1G1Va;S4bG0Sf7A2A4S12eS12bR1A1A1A3S36S35S3aS41S49G0Va;A2M2S120A2Z0A3S36S3eS121G2A2S36S3eS3dG2Sf7A2Valloc_ceiling;A2S2bS3aS3aA2M3S117G3R1S108VG0;A1A3S109R2S2cS3aS3aG2Sf7A4A2F_;Fbn;A2A2A2A2Lmd;L_;L_;").
Lemma PDb_stable : ltac2:(tb__ "0|0|
S4aQ40A1S7fS72R1A1A1Fa;").
Proof.
  intros a rho rho' tp md md' Hag ((mat' & ->) & _) H. exact H.
Qed.
Lemma PDb_view : ltac2:(tb__ "0|0|
S4aQ40A1S87S72R1A1A1Fa;").
Proof. intros a rho rho' tp md _ _ _ H. exact H. Qed.

Lemma depot_vm_grow : ltac2:(tb__ "0|3|
S5cS12aS133S27S4aQ40A1M0A1S2bG0G0A2M1SfaR5R4R2A3S35S27G1A1M2S12eR4A1S25G1R2S12eS12bR5A1A1A3A3S35G2S12fR5A1S12fS12bR6A1A1A3S35S3aS12dR6A1S12dS12bR7A1A1A3SfaR9S132R7R8A2R6A3F_;F_;F_;F_;Fe;Ftp;Fh';Fmd;FG;").
Proof.
  intros G md h' tp e [DM DL DA DT DTOP DTR] Hm Hn Ht. constructor; rewrite ?m_vmmaps_with_vmmaps, ?m_vm_lazy_with_vmmaps, ?Ht; try assumption.
  - intros bn Hbn. rewrite Hm. right. exact (DM bn Hbn).
  - intros b j Hb Hj. rewrite Hn. exact (DA b j Hb Hj).
Qed.

Variable NBbs : axst. Variable sB : wsub.
Hypothesis RUNB2 : ltac2:(tb__ "0|0|
S35S27S52A1S9aUbbaS25S3aZ7ebecS25S3aZ6bf18S26S3aA1A3A3SecVEBs;A1A3S25S52S53VNBbs;S126A2S26S52A1A3A3").
Definition O_mu2 : sobj := ltac2:(tb__ "0|3|
S15bS5Z0A1M0S102S3dS102Z4A2S25S2bS2bS3aS2eA2M1S2A2M2S2cG1S2S2cS3aS2eS102U1A4G0A4S25G2S2cG1S2S2cS3aS2eS3dS102Z1A2U3A4G0A4S26G2A1A3A3A4").
Let Pb : list sobj := ltac2:(tb__ "0|1|
S115S0S153S2dS0S6S51VNBbs;A1A1M0A2U3A2G0A3").
Let Rb : list sobj := ltac2:(tb__ "0|0|
S25S0S99S9S95A1A1S25S0S8cS25S0S14fS95Sf7A2S26S0A1A3A3A3").
Hypothesis NBb_objs : ltac2:(tb__ "0|0|
S35S27S0A1S6S51VNBbs;A1A1S29S0VPb;VRb;A3A3").
Hypothesis NBb_skel : ltac2:(tb__ "0|2|
S35S27S2bS2bS2S2A2S2A2M0A1S113S0G0S122VPb;A4S113S0G0S122S29S0S29S0S25S0S138S25S0Sa3S26S0A1M1A3A3S29S0S137Sa4A3A3S25S0S97S96A1S25S0S9dS9fA1G1A3A3A3A4A3").
Hypothesis NBb_F : ltac2:(tb__ "0|0|
S35S28S125S29S4S9eS29S4Sa5Sa7A3A3S7S51VNBbs;A1A1A2S2aA3").
Hypothesis NBb_X : ax_X NBbs = [].
Hypothesis NBb_nx : ltac2:(tb__ "0|0|
S35S3bS8S51VNBbs;A1A1S149S95A1A3").
Let S_bj : sstate := ltac2:(tb__ "0|1|
S13ScS51VNBbs;A1M0A1SfG0A1S16G0A1S15G0A1S17G0A1S29S0VPb;S25S0S99S9S95A1A1S26S0A1A3A3S7G0A1S8G0A1SaG0A1A9").
Hypothesis Bj_swf : swf S_bj = true.
Hypothesis Bj_fb : ltac2:(tb__ "0|1|
S35S28S116S4S10S8S51VNBbs;A1M0A1A1S29S4S7G0A1S26S4A1A3A3S2aA3").
Hypothesis ENT_B : ltac2:(tb__ "0|0|
S35S28S54SebVNBbs;A1VNBs;VsB;A3S2aA3").
Hypothesis SID_B : ltac2:(tb__ "0|0|
S35S28S13aVsB;S98A2S2aA3").
Definition ids3 (s : wsub) : bool := ltac2:(tb__ "0|0|
S116S3bS3bS1cS13bVs;R1A2S9R1A1A2Li;S25S3bPaaS25S3bPabS25S3bPb1S26S3bA1A3A3A3A3").
Hypothesis IDS_B : ids3 sB = true.
Hypothesis SB178 : ltac2:(tb__ "0|0|
S35S2S13bVsB;Pb2A2S9S95A1A3").

Lemma ids3_rw : ltac2:(tb__ "0|0|
S13cS1S3bS35S28S8fR3A1S2aA3S117S3bR2S25S3bPaaS25S3bPabS25S3bPb1S26S3bA1A3A3A3A3S35S4aQ40A1S3S13dR4R5A2R3A2S3R4R3A2A3F_;F_;Fi;Frho;Fs;").
Proof.
  intros s rho i H Hi. unfold ids3 in H. pose proof (proj1 (forallb_forall _ _) H i Hi) as X. apply sv_eqb_sound in X.
  cbn [rw rho_sub]. rewrite X. reflexivity.
Qed.

Lemma enc_zero_nth : ltac2:(tb__ "0|4|
S2eS2eS11aR2U8A2S119R2R3A2S35S4aQ8M0A1M1S114G1R3S22R4S4bQ40Z0M2A2A2S4bG0G2A2M3A4G3A3F_;F_;Fj;Fk;").
Proof.
  intros k j Hk Hj.
  destruct k as [|[|[|[|[|[|[|[|[|k]]]]]]]]]; try lia;
  destruct j as [|[|[|[|[|[|[|[|j]]]]]]]]; try lia; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
Qed.

Lemma depot_vm_nblk : ltac2:(tb__ "0|2|
S5cS12aS27S4aQ40M0A1M1A1G1SfaR4R3R2A3S117S2bG1G1A2S2cG1G1R2S4bG0Sf7A2A4S12eS12bR4A1A1A3S3eS3dS49G0R3A2Sf7A2S12dS12bR5A1A1A2SfaSfdR7S49G0R4A2A2R6R5A3F_;F_;F_;Fa;Ftp;Fmd;FG;").
Proof.
  intros G md tp a [DM DL DA DT DTOP DTR] Hin Htop. constructor; cbn [dNB dFB dFP G_nblk]; try assumption.
  - intros bn Hbn. rewrite dblocks_G_nblk in Hbn. apply in_app_or in Hbn as [Hbn|[<-|Hbn]].
    + apply DM. unfold dblocks. apply in_or_app. left. exact Hbn.
    + unfold wentry. cbn [fst snd]. rewrite Z_to_bv_bv_unsigned. exact Hin.
    + apply DM. unfold dblocks. apply in_or_app. right. exact Hbn.
  - intros bn Hbn. rewrite dblocks_G_nblk in Hbn. apply in_app_or in Hbn as [Hbn|[<-|Hbn]].
    + apply DTOP. unfold dblocks. apply in_or_app. left. exact Hbn.
    + cbn [fst snd]. exact Htop.
    + apply DTOP. unfold dblocks. apply in_or_app. right. exact Hbn.
Qed.

Lemma glue_bj : ltac2:(tb__ "0|5|
S4aQ40M0A1M1S1S11bSfdVG0;S49G0R3A2A2S5cS4dS3cS6aR1VG0;S72R4A1A3VNBbs;R3Vtp0;R2A6S3eS5dVG0;A1M2SfbA2S35S3aS49G0S3R5Pb1A2A2G2A3S3eS49G0S3R6PaaA2A2G2A2S35G1S3R7S95A2R8A3S68VG0;R8S97S96A1A3S68VG0;R9S9dS9fA1A3S35S3aS46S2dS3aS60VG0;A1A2A1S40S3dG2Z1A2M3Z10000M4A2A3S35S3aS41G3G4A2Z0A3S37S1S1S36S4dS3cS63RbA1VNBs;R1Vtp0;RcA6S6bRbR1A2A2Lrho';A2F_;F_;F_;F_;F_;F_;F_;F_;F_;TG1;Fw;FrhoL;Fa;").
Proof.
  intros a rhoL w G1 H HDN K177 K170 K210 KD1 KD2 HLj Hmod. destruct w as [tr [ms md]].
  pose proof H as [HsmA [HREL [HK [[HM HV] HPD]]]]. cbn [w_tr w_cfg fst snd cfg_model] in HK, HV, HPD.
  destruct HPD as (Pin & Pal & Plo & Phi & Pdisj).
  pose proof (proj1 HsmA) as Hsm. unfold virt in Hsm. cbn [fst snd cfg_ms cfg_model w_tr w_cfg] in Hsm.
  pose proof (dm_N _ _ HM) as [HN _]. pose proof alloc_ceiling_valD as ACV. pose proof (urange a) as Ra.
  set (j := length (dNB G0)) in *.
  assert (HjM : Z.of_nat j < MAP1N) by (unfold MAP1N, DNMAX in *; rewrite HLj; apply Z.div_lt_upper_bound; lia).
  assert (Hj1 : 1 <= Z.of_nat j).
  { pose proof (proj1 (dm_map1_len _ _ HM)) as X. unfold nblk in X. destruct (Z.eqb_spec (dN G0) 0); [lia|]. fold j in X. pose proof (Z.div_pos (dN G0) 65536). lia. }
  assert (SA : bv_unsigned (eval rhoL slotN_addr) = MAP1 + 8 * Z.of_nat j) by (rewrite HLj; apply slotN_addr_val; [exact K177 | unfold DNMAX in HDN; lia]).
  assert (E210 : eval rhoL (SVar NXD) = a) by (cbn [eval]; exact K210).

  pose proof (SPA_facts segsA _ _ _ _ _ H) as HFall.
  pose proof (holds_inclb rhoL _ _ NBb_F HFall) as HF3. apply Forall_app in HF3 as [HFD HF3]. apply Forall_app in HF3 as [HFt HFn].

  assert (Hw0 : SPA segsA (fun _ _ _ _ => True) NBbs rhoL tp0 (tr, mkCfg ms md)) by (split; [exact HsmA | exact I]).
  pose proof (SPA_unobj segsA (fun _ _ _ _ => True) rhoL NBbs Pb Rb tp0 tr ms md NBb_objs Hw0 (fun _ => I)) as Hw1.
  cbn zeta in Hw1. set (rho' := rho_absorb rhoL Rb (vms md tp0 ms)) in *.

  assert (CIVs := absorb_view_cells segsA rhoL (ax_S NBbs) tr (vms md tp0 ms) (vmd md) Pb Rb slotN_addr 0 8 [(0, 8%nat, SVar NXD)] Hsm NBb_objs
                    ltac:(unfold Rb; cbn; tauto) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold cells_inside; constructor; [cbn; lia|constructor])
                    ltac:(rewrite SA; unfold MAP1; lia) ltac:(rewrite SA; unfold MAP1, MAP1N in *; lia)).
  assert (CIVm := absorb_view_cells segsA rhoL (ax_S NBbs) tr (vms md tp0 ms) (vmd md) Pb Rb (SLit 0) NODESMU (NODESMU + 4) [(NODESMU, 1%nat, SLit 0); (NODESMU + 1, 3%nat, SLit 0)] Hsm NBb_objs
                    ltac:(unfold Rb; cbn; tauto) ltac:(unfold NODESMU; lia) ltac:(lia) ltac:(unfold NODESMU; lia) ltac:(unfold cells_inside; repeat constructor; cbn; lia)
                    ltac:(cbn [eval]; rewrite u64_lit by lia; unfold NODESMU; lia) ltac:(cbn [eval]; rewrite u64_lit by lia; unfold NODESMU; lia)).
  fold rho' in CIVs, CIVm. rewrite SA in CIVs. cbn [eval] in CIVm. rewrite u64_lit in CIVm by lia.
  destruct CIVs as [Cs _]. destruct CIVm as [Cm _].
  assert (ZB : forall z, bv_unsigned a <= z < bv_unsigned a + NBSZ -> view segsA (rm rho') z = Some (Z_to_bv 8 0)).
  { intros z Hz. unfold rho', Rb. unfold mmap_obj.
    apply (absorb_view_dzero segsA rhoL (ax_S NBbs) tr (vms md tp0 ms) (vmd md) Pb _ (SVar NXD) 0 NBSZ Hsm NBb_objs);
      rewrite ?E210; unfold NBSZ in *; try lia. cbn. tauto. }
  assert (VOUT : forall x : word, ~ (MAP1 + 8 * Z.of_nat j <= bv_unsigned x < MAP1 + 8 * Z.of_nat j + 8) -> ~ (NODESMU <= bv_unsigned x < NODESMU + 4) ->
                 ~ (bv_unsigned a <= bv_unsigned x < bv_unsigned a + NBSZ) -> rm rho' x = rm rhoL x).
  { intros x H1 H2 H3. unfold rho'. apply rm_absorb_out. intros (o & Ho & Hr). unfold Rb in Ho.
    destruct Ho as [<-|[<-|[<-|[]]]].
    - unfold O_slotN, carved in Hr. rewrite obj_range_mk in Hr by lia. rewrite SA in Hr. cbn [fst snd] in Hr. lia.
    - unfold O_mu2, carved in Hr. rewrite obj_range_mk in Hr by (unfold NODESMU; lia). cbn [fst snd eval] in Hr. rewrite u64_lit in Hr by lia. lia.
    - unfold mmap_obj in Hr. rewrite obj_range_mk in Hr by (unfold NBSZ; lia). rewrite E210 in Hr. cbn [fst snd] in Hr. lia. }
  assert (Hsame : forall z, ~ (MAP1 + 8 * Z.of_nat j <= z < MAP1 + 8 * Z.of_nat j + 8) -> ~ (bv_unsigned a <= z < bv_unsigned a + NBSZ) ->
                  view segsA (rm rho') z = view segsA (rm rhoL) z).
  { intros z H1 H3. destruct (Z_lt_le_dec z 0) as [Zn|Z0]; [unfold view; destruct (Z.leb_spec 0 z); [lia|reflexivity]|].
    destruct (Z_lt_le_dec z (2 ^ 64)) as [Z1|Z2]; [|unfold view; destruct (Z.ltb_spec z (2 ^ 64)); [lia|]; rewrite andb_false_r; reflexivity].
    destruct (zrange_dec NODESMU (NODESMU + 4) z) as [Hmu|Hmu].
    -
      pose proof (dm_mu _ _ HM) as MU. unfold cellZ, cell_ok in MU. cbn [c_addr c_w RtCells.c_val] in MU.
      specialize (MU (Z.to_nat (z - NODESMU)) ltac:(lia)). replace (NODESMU + Z.of_nat (Z.to_nat (z - NODESMU))) with z in MU by lia.
      rewrite MU, (enc_zero_nth 4) by lia.
      destruct (Z.eq_dec z NODESMU) as [->|Hne].
      + replace NODESMU with (0 + NODESMU + Z.of_nat 0) at 1 by lia. rewrite (Cm NODESMU 1%nat (SLit 0) 0%nat ltac:(cbn; tauto) ltac:(lia)). cbn [eval]. rewrite (enc_zero_nth 1) by lia. reflexivity.
      + replace z with (0 + (NODESMU + 1) + Z.of_nat (Z.to_nat (z - NODESMU - 1))) at 1 by lia.
        rewrite (Cm (NODESMU + 1) 3%nat (SLit 0) (Z.to_nat (z - NODESMU - 1)) ltac:(cbn; tauto) ltac:(lia)). cbn [eval]. rewrite (enc_zero_nth 3) by lia. reflexivity.
    - rewrite !view_in by lia. unfold rd_of. rewrite VOUT; [reflexivity | rewrite u64_lit by lia; exact H1 | rewrite u64_lit by lia; exact Hmu | rewrite u64_lit by lia; exact H3]. }

  assert (Cslot : cellZ (view segsA (rm rho')) (MAP1 + 8 * Z.of_nat j) 8 (bv_unsigned a)).
  { intros jj Hjj. cbn [c_addr c_w RtCells.c_val]. rewrite Z_to_bv_bv_unsigned.
    replace (MAP1 + 8 * Z.of_nat j + Z.of_nat jj) with (MAP1 + 8 * Z.of_nat j + 0 + Z.of_nat jj) by lia.
    rewrite (Cs 0 8%nat (SVar NXD) jj ltac:(left; reflexivity) Hjj). rewrite E210. reflexivity. }
  assert (Pblk : present (view segsA (rm rho')) (bv_unsigned a) (bv_unsigned a + NBSZ)) by (intros z Hz; rewrite (ZB z Hz); eexists; reflexivity).
  pose proof (depot_mem_nblk G0 (view segsA (rm rhoL)) (view segsA (rm rho')) (bv_unsigned a) HM HDN HLj Hmod Pal Plo ltac:(clear - Phi ACV; lia) Pdisj Cslot Pblk Hsame) as HM1.
  pose proof (depot_vm_nblk G0 md tp0 a HV Pin ltac:(rewrite (HKT _ _ _ _ _ HK); exact Phi)) as HV1.
  assert (INW : forall z, (MAP1 + 8 * Z.of_nat j <= z < MAP1 + 8 * Z.of_nat j + 8) \/ (bv_unsigned a <= z < bv_unsigned a + NBSZ) -> DFPw G1 z).
  { intros z [Hz|Hz].
    - left. unfold dfp_static, DEPOT, MAP1, MAP1N, STORE, NFBLK in *. lia.
    - right. left. exists (bv_unsigned a). split; [unfold G1, G_nblk; cbn [dNB]; apply in_or_app; right; left; reflexivity | exact Hz]. }
  assert (HK1 : K G1 rho' tp0 tr md).
  { eapply (kd_view segsA K NPRE HKD G1 rhoL rho'); [intros i; reflexivity | intros l; reflexivity | | exact HK].
    intros z Hz. apply Hsame; intros Hin; apply Hz; apply INW; tauto. }
  destruct HREL as (R1 & R2 & R3).
  assert (HREL1 : REL G1 rho').
  { split; [exact R1 | split].
    - intros x Hx. rewrite VOUT; [apply R2; exact Hx | | |]; intros Hin; apply Hx.
      + left. left. unfold dfp_static, DEPOT, MAP1, MAP1N, STORE, NFBLK in *. lia.
      + left. left. unfold dfp_static, DEPOT, MAP1, MAP1N, NODESMU in *. lia.
      + right. left. exists (bv_unsigned a). split; [unfold G1, G_nblk; cbn [dNB]; apply in_or_app; right; left; reflexivity | exact Hin].
    - intros z Hz. rewrite Hsame; [apply R3; exact Hz | |]; intros Hin; apply Hz; apply INW; tauto. }

  assert (CIV' : cells_in_view rho' (rd_of segsA (rm rho')) (MAP1 + 8 * Z.of_nat j) [(0, 8%nat, SVar NXD)]).
  { unfold cells_in_view. constructor; [|constructor]. intros jj Hjj. cbn beta iota.
    pose proof (Cs 0 8%nat (SVar NXD) jj ltac:(left; reflexivity) Hjj) as X. rewrite view_in in X by (unfold MAP1, MAP1N in *; lia).
    unfold rho'. rewrite eval_absorb. unfold rho' in X. exact X. }
  assert (H2 : SPA segsA (fun _ _ _ _ => True) (ax_setS (ax_setS NBbs (set_objs (ax_S NBbs) Pb)) S_bj) rho' tp0 (tr, mkCfg ms md)).
  { unfold S_bj, O_slotN.
    apply (SPA_carve_obj segsA (fun _ _ _ _ => True) rho' (ax_setS NBbs (set_objs (ax_S NBbs) Pb)) tp0 _ slotN_addr 0 8 [(0, 8%nat, SVar NXD)] (ss_next (ax_S NBbs)) Hw1 Bj_swf);
      cbn [ax_S ax_setS set_objs ss_next ss_objs]; unfold rho'; rewrite ?eval_absorb, ?SA; fold rho'.
    - apply Pos.le_refl.
    - lia. - lia. - lia. - lia.
    - unfold MAP1. lia.
    - unfold MAP1, MAP1N in *. lia.
    - unfold cells_inside. constructor; [cbn; lia|constructor].
    - pose proof (proj1 Hw1) as Hsm1. unfold smatchA, virt in Hsm1. cbn [fst snd cfg_ms cfg_model w_tr w_cfg ax_S ax_setS set_objs] in Hsm1. apply proj1 in Hsm1.
      assert (HFD' : Forall (holds rho') F_D).
      { pose proof (SPA_facts segsA _ _ _ _ _ Hw1) as HFall'. cbn [ax_S ax_setS set_objs ss_facts] in HFall'.
        pose proof (holds_inclb rho' _ _ NBb_F HFall') as X. apply Forall_app in X as [X _]. exact X. }
      eapply (objs_ranges_ext rho' (set_objs (ax_S NBbs) Pb) _ Pb [O_tw vW; O_nid vN] _ _ Hsm1 ltac:(intros o Ho; exact Ho) NBb_skel HFD' ltac:(first [assumption | eapply TOPr_of_REL; eassumption | eapply TOPr_of_JJ; eassumption])); [unfold STORE, MAP1; lia | unfold MAP1, MAP1N in *; lia | lia |].
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      + unfold O_tw, carved, ranges_disjoint. rewrite obj_range_mk by lia. cbn [fst snd eval vP]. unfold rho'. cbn [rw rho_absorb].
        assert (HP : bv_unsigned (rw rhoL 171%positive) <= DEPOT + 4 * 2 ^ 20 - 4).
        { pose proof (proj1 (Forall_forall _ _) HFt (SPUle vP (SLit (DEPOT + 4 * 2^20 - 4))) ltac:(unfold F_tw; cbn; tauto)) as X1.
          cbn [holds eval vP] in X1. unfold DEPOT in *. rewrite u64_lit in X1 by lia. exact X1. }
        unfold DEPOT, MAP1 in *. lia.
      + unfold O_nid, carved, ranges_disjoint. rewrite obj_range_mk by (unfold NIDS; lia). cbn [fst snd eval]. rewrite u64_lit by lia. unfold NIDS, MAP1. lia.
    - intros off Hoff. unfold MAP1, MAP1N in *. split; [apply wok_of_imageA; lia | apply rd_of_imageA; lia].
    - exact CIV'.
    - unfold xwords_clear. cbn [ax_X ax_setS]. rewrite NBb_X. intros rr y jj []. }
  assert (H3 : SPA segsA (fun _ _ _ _ => True) (ax_with_facts (ax_setS (ax_setS NBbs (set_objs (ax_S NBbs) Pb)) S_bj) (ss_facts (ax_S NBbs) ++ [])) rho' tp0 (tr, mkCfg ms md)).
  { apply SPA_refacts; [exact H2 | exact Bj_fb |]. cbn [ax_S ax_setS ss_facts]. intros HFB. apply Forall_app. split; [exact HFB | apply Forall_nil]. }
  unfold ax_with_facts in H3. rewrite !ax_setS_setS in H3.
  assert (H4 : SPA segsA (JJ G1) (mkNBj NBbs) rho' tp0 (tr, mkCfg ms md)).
  { split; [exact (proj1 H3)|]. split; [exact HREL1|]. split; [exact HK1|]. split; [split; [exact HM1 | exact HV1] | exact I]. }

  set (rho'' := rho_sub rho' sB).
  assert (H5 : SPA segsA (JJ G1) NBs rho'' tp0 (tr, mkCfg ms md)).
  { unfold rho''. apply (SPA_entails segsA (JJ G1) NPRE (mkNBj NBbs) NBs sB rho' tp0 _ ENT_B SID_B (JJ_stable G1 NPRE ltac:(lia))). exact H4. }
  exists rho''. split; [exact H5|].

  assert (U177 : rw rho'' 177%positive = rw rhoL 177%positive) by (unfold rho''; rewrite (ids3_rw sB rho' _ IDS_B) by (cbn; tauto); reflexivity).
  assert (U170 : rw rho'' 170%positive = rw rhoL 170%positive) by (unfold rho''; rewrite (ids3_rw sB rho' _ IDS_B) by (cbn; tauto); reflexivity).
  assert (U171 : rw rho'' 171%positive = rw rhoL 171%positive) by (unfold rho''; rewrite (ids3_rw sB rho' _ IDS_B) by (cbn; tauto); reflexivity).
  assert (U178 : rw rho'' 178%positive = a) by (unfold rho''; cbn [rw rho_sub]; rewrite SB178; unfold rho'; rewrite eval_absorb; exact E210).
  assert (RGt : obj_range rho'' (O_tw vW) = obj_range rhoL (O_tw vW)).
  { apply (obj_range_agree_vars (fun i => Pos.eqb i 171 || Pos.eqb i 170) rhoL rho'');
      [intros v Hv; apply orb_prop in Hv as [Hv|Hv]; apply Pos.eqb_eq in Hv; subst; symmetry; [exact U171 | exact U170] | intros l; reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc]. }
  assert (RGn : obj_range rho'' (O_nid vN) = obj_range rhoL (O_nid vN)).
  { apply (obj_range_agree_vars (fun i => Pos.eqb i 177) rhoL rho''); [intros v Hv; apply Pos.eqb_eq in Hv; subst; symmetry; exact U177 | intros l; reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc]. }
  assert (SA'' : bv_unsigned (eval rho'' slotN_addr) = MAP1 + 8 * Z.of_nat j) by (rewrite HLj; apply slotN_addr_val; [rewrite U177; exact K177 | unfold DNMAX in HDN; lia]).
  assert (DFPmono : forall z, DFP G0 z -> DFP G1 z).
  { intros z [Hz|[[b0 [Hb0 Hz]]|Hz]]; [left; exact Hz | right; left; exists b0; split; [unfold G1, G_nblk; cbn [dNB]; apply in_or_app; left; exact Hb0 | exact Hz] | right; right; exact Hz]. }
  split; [|split; [|split; [|split]]].
  - split; [rewrite U177; exact K177|]. split; [rewrite U170; exact K170|].
    split; [intros x Hx; apply DFPmono; apply KD1; rewrite <- RGt; exact Hx | intros x Hx; apply DFPmono; apply KD2; rewrite <- RGn; exact Hx].
  - unfold G1, G_nblk. cbn [dN dNB]. rewrite length_app. cbn [length]. rewrite <- HLj, Nat2Z.id. fold j. lia.
  - rewrite U178. unfold G1, G_nblk. cbn [dN dNB]. rewrite <- HLj, Nat2Z.id. fold j. rewrite app_nth2 by lia. rewrite Nat.sub_diag. reflexivity.
  - exists slotN_addr, 0, 8%nat, vNB. rewrite SA''. split; [reflexivity|]. unfold MAP1, MAP1N in *. repeat (split; [lia|]).
    unfold cells_in_view. constructor; [|constructor]. intros jj Hjj. cbn beta iota.
    pose proof (Cs 0 8%nat (SVar NXD) jj ltac:(left; reflexivity) Hjj) as X. rewrite view_in in X by lia. rewrite E210 in X.
    replace (eval rho'' vNB) with a by (symmetry; exact U178). change (rm rho'') with (rm rho'). exact X.
  - unfold winDFP, O_slotN, carved. intros x. rewrite obj_range_mk by lia. cbn [fst snd]. rewrite SA''. intros Hx. left. left. unfold DEPOT, MAP1, MAP1N in *. lia.
Qed.

Lemma JJ2_okp : ltac2:(tb__ "0|0|
S5cS5cS75S15dS3cVok;S6aR3R2R1A3A3FPD;FGd;FGk;").
Proof. intros Gk Gd PD rho tp tr ms md x8 [_ [HK _]] Hp Hok. exact (HKokp Gk rho tp tr ms md x8 HK Hp Hok). Qed.

Lemma NBSZ_lit : ltac2:(tb__ "0|1|
S35S3aS49Q40M0S4bG0Sf7A2A2Sf7A3"). Proof. apply u64_lit. unfold NBSZ. lia. Qed.
Lemma NBSZ_nZ : ltac2:(tb__ "0|0|
S35S3aS164S4bQ40Sf7A2A1Sf7A3").
Proof. unfold mmap_nZ, page_round_up_Z, page_size. rewrite NBSZ_lit. reflexivity. Qed.
Lemma NBSZ_n : ltac2:(tb__ "0|2|
S35S4aQ40M0A1S163S4bG0Sf7A2M1A1G1A3").
Proof. unfold mmap_n. rewrite NBSZ_nZ. reflexivity. Qed.

Lemma EB_objs_clear : ltac2:(tb__ "0|2|
S1S147S3aS3aS112S0S1eS3cR4R3A3S6S51VEBs;A1A1M0A3S112S4S1aR5A1S29S4S9eS29S4Sa5Sa7A3A3A3S6dR6A1S35S3aS49Q40S3R7Pb1A2A2S5dVG0;A1M1A3S36S3eZ1G1A2S3eG1SfbA2A2S3eS121R7A2S3eR7Valloc_ceiling;A2S3eR9R8A2S112S0S0S19S11RdR1A2S2cS3aS3aRbRaA4A2Lo;G0A3F_;F_;F_;F_;F_;F_;F_;F_;Fhi;Flo;Fms;Frho;").
Proof.
  intros rho ms lo hi Hsm HF HT K177 HDN H1 H2 H3. apply Forall_app in HF as [HFD HF]. apply Forall_app in HF as [HFt HFn].
  pose proof alloc_ceiling_valD as ACV.
  assert (SA : bv_unsigned (eval rho slotN_addr) = MAP1 + 8 * ((dN G0 + 1) / 65536)) by (apply slotN_addr_val; [exact K177 | unfold DNMAX in HDN; lia]).
  assert (HjNz : 0 <= (dN G0 + 1) / 65536 < 2 ^ 15) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; unfold DNMAX in HDN; lia]).
  eapply (objs_ranges_ext_mm rho ms _ _ [O_tw vW; O_nid vN; O_slotN (SLit 0); O_mu] _ _ Hsm ltac:(intros o Ho; exact Ho) EB_skel HFD ltac:(first [assumption | eapply TOPr_of_REL; eassumption | eapply TOPr_of_JJ; eassumption])); [unfold STORE, IMG_HI in *; lia | lia | exact H3 |].
  unfold O_tw, O_nid, O_slotN, O_mu, carved, ranges_disjoint.
  apply Forall_cons. { rewrite obj_range_mk by lia. cbn [fst snd eval vP].
    pose proof (proj1 (Forall_forall _ _) HFt (SPUle vP (SLit (DEPOT + 4 * 2^20 - 4))) ltac:(unfold F_tw; cbn; tauto)) as X2. cbn [holds eval vP] in X2. unfold DEPOT in X2. rewrite u64_lit in X2 by lia.
    unfold DEPOT, IMG_HI in *. lia. }
  apply Forall_cons. { rewrite obj_range_mk by (unfold NIDS; lia). cbn [fst snd eval]. rewrite u64_lit by lia. unfold NIDS, IMG_HI in *. lia. }
  apply Forall_cons. { rewrite obj_range_mk by lia. cbn [fst snd]. rewrite SA. unfold MAP1, IMG_HI in *. lia. }
  apply Forall_cons. { rewrite obj_range_mk by (unfold NODESMU; lia). cbn [fst snd eval]. rewrite u64_lit by lia. unfold NODESMU, IMG_HI in *. lia. }
  apply Forall_nil.
Qed.

Lemma mmap_user_b : ltac2:(tb__ "0|d|
S1S27S12cA1M0S147S12aS4aQ40M1A1M2S15eS3cR5Vtp0;VEBs;S2cG0S143R4S144R3R2A2A4A5S63VG0;R6Vtp0;R5R3A5S35S3aS49G1S3R7Pb1A2A2S5dVG0;A1M3A3S3eG3SfbA2S35S3aS41S3dG3Z1A2Z10000A2Z0A3S35G2S146R8U1M4A2S4bG1Sf7A2A3S165S146R9U0A2S146R9U3A2R8S146R9G4A2R7A5S36S0S117S0R1S6S51VEBs;A1M5A1A3S19S11ReR2A2S2cS3aS3aS49G1RaA2M6S3dG6Sf7A2A4A2F_;Fo;S36G2S36S3eS49G1R9A2M7S49G1R1A2M8A2S3fG8S3dG7Sf7A2A2A2S35S28S23S3cR2A2S30A3F_;Fx;S36S2bS2S2A2M9S3aS117G9R2S59VEBs;A1A3S36S3eS49G1SeRfS33S2S2R3A3A2A2MaR2A2S3fR2S3dGaS49G1SeRfS32S2S2R3A3A2A2A2A2A2S38S36S3eS49G1RcA2MbS49G1S5aS49G1SeR10S56VEBs;A1A2A2R3A2A2McA2S3fGcS3dGbSf7A2A2A2A1F_;F_;Fy;Fr;S6aSfdVG0;S49G1R8A2A2VG0;S72R8A1S14dRcS8G5A1R8A3Vtp0;RbS132S166S12bR9A1S146RaG4A2R8A3R9A2A7A2A2A2F_;F_;F_;F_;F_;F_;F_;Fa;Fmd;Fms;Ftr;Frho;").
Proof.
  intros rho tr ms md a Hsp HJ K177 HDN Hmod G1 Hpl.
  pose proof HJ as [HREL [HK [[HM HV] _]]].
  pose proof alloc_ceiling_valD as ACV. pose proof (urange a) as Ra.
  pose proof (smatch_pendingA_MI segsA _ _ _ _ _ _ Hsp) as HMI.
  rewrite G1 in Hpl. pose proof Hpl as (Pal & Ppos & Pceil & Pfree & _). rewrite NBSZ_nZ in Pceil. rewrite NBSZ_n in Pfree. pose proof Pceil as PceilM. rewrite (HKT _ _ _ _ _ HK) in Pceil.
  pose proof (kd_reserved segsA K NPRE HKD G0 rho tp0 tr md HK) as Hres.
  destruct (grant_facts_A _ _ md _ a Hpl Hres) as (_ & _ & _ & Himg & Hmaps). rewrite NBSZ_nZ in Himg, Hmaps.
  assert (Hlo : IMG_HI <= bv_unsigned a).
  { unfold IMG_HI, NBSZ in *. destruct (Z_lt_le_dec (bv_unsigned a) 0x10000) as [L|L].
    - exfalso. apply (Himg 0x10000); lia.
    - destruct (Z_lt_le_dec (bv_unsigned a) 0x643000) as [L2|L2]; [exfalso; apply (Himg (bv_unsigned a)); lia | exact L2]. }
  assert (Hdisj : forall bn, In bn (dblocks G0) -> ranges_disjointZ bn (bv_unsigned a, NBSZ)).
  { intros [b0 n0] Hbn. pose proof (dv_maps _ _ _ HV _ Hbn) as Hm. unfold wentry in Hm. cbn [fst snd] in Hm.
    pose proof (depot_inv_bounds segsA G0 rho md tp0 (conj HM HV)) as (_ & _ & BB & _). destruct (BB _ Hbn) as (B1 & B2 & _). cbn [fst snd] in B1, B2.
    assert (N0 : 0 < n0 < 2 ^ 40) by (unfold dblocks in Hbn; apply in_app_or in Hbn as [Hbn|Hbn]; apply in_map_iff in Hbn as (q & E & _); injection E; intros; subst; unfold NBSZ, FBSZ; lia).
    unfold ranges_disjointZ. cbn [fst snd]. unfold IMG_HI in *.
    destruct (Z_lt_le_dec (b0 + n0) (bv_unsigned a + 1)) as [L|L]; [lia|].
    destruct (Z_lt_le_dec (bv_unsigned a + NBSZ) (b0 + 1)) as [L2|L2]; [lia|]. exfalso.
    destruct (Z_lt_le_dec (bv_unsigned a) b0) as [L3|L3].
    - apply (Hmaps _ _ Hm b0); rewrite ?u64_lit by lia; unfold NBSZ in *; lia.
    - apply (Hmaps _ _ Hm (bv_unsigned a)); rewrite ?u64_lit by lia; unfold NBSZ in *; lia. }
  pose proof (smatch_pendingA_sp segsA _ _ _ _ _ _ Hsp) as Hsm0.
  split; [|split; [|split]].
  - intros o Ho. pose proof (smatch_pending_facts segsA _ _ _ _ _ Hsm0) as HFall.
    pose proof (holds_inclb rho _ _ EB_F HFall) as HF3.
    assert (Hall : Forall (obj_holds segsA rho (vms md tp0 ms)) (ss_objs (ax_S EBs))).
    { destruct Hsm0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hall & _ & _) & _). exact Hall. }
    pose proof (proj1 (dm_N _ _ HM)) as HN.
    exact (proj1 (Forall_forall _ _) (EB_objs_clear rho _ (bv_unsigned a) (bv_unsigned a + NBSZ) Hall HF3 ltac:(first [assumption | eapply TOPr_of_REL; eassumption | eapply TOPr_of_JJ; eassumption]) K177 ltac:(lia) Hlo Pceil ltac:(unfold NBSZ; lia)) o Ho).
  - intros x Hx. apply (grant_no_ro_A a NBSZ); [|exact Hx]. intros z Hz. apply Himg. exact Hz.
  - rewrite EB_X. intros r y [].
  - set (rho1 := rho_set_rw rho (ss_next (ax_S EBs)) a). set (h' := mmap_rw_vm (m_vmmaps md) (ms_gpr ms 1) a).
    assert (Hag : agree_below NPRE rho rho1) by (unfold rho1; apply agree_below_set_rw; rewrite EB_nx; unfold NPRE, NXD; lia).
    assert (Hvm : vm_maps h' = (a, Z_to_bv 64 NBSZ) :: vm_maps (m_vmmaps md)) by (unfold h', mmap_rw_vm; rewrite G1, NBSZ_n; reflexivity).
    assert (Hna : vm_noaccess h' = vm_noaccess (m_vmmaps md)) by reflexivity.
    assert (Hrs : vm_reserved h' = vm_reserved (m_vmmaps md)) by reflexivity.
    assert (Hlm : vm_limit h' = vm_limit (m_vmmaps md)) by reflexivity.
    destruct (kd_room segsA K NPRE HKD G0 rho tp0 _ _ HK (conj HM HV)) as [Hroom _].
    assert (HroomN : headroom md tp0 >= NBSZ) by (unfold droom in Hroom; rewrite (proj2 (Z.eqb_eq _ _) Hmod) in Hroom; unfold PG, NBSZ in *; lia).
    assert (Hpaid : paid (with_vmmaps h' md) tp0 <= paid md tp0 + NBSZ).
    { rewrite paid_with_vmmaps.
      pose proof (used_maps_cons_le md h' a (Z_to_bv 64 NBSZ) (MI_ivs_wf segsA _ _ HMI)
                   ltac:(unfold iv_wf, ivB, ivS; cbn [fst snd]; rewrite NBSZ_lit; unfold NBSZ in *; lia) Hvm Hna) as U.
      rewrite NBSZ_lit in U. lia. }
    split; [|split; [|split]].
    + destruct HREL as ((R1 & R1') & R2 & R3). split; [split|split].
      * intros i Hi. rewrite (R1 i Hi). unfold rho1. symmetry. apply rho_set_rw_other. rewrite EB_nx. unfold NPRE, NXD in *. lia.
      * intros l. rewrite (R1' l). reflexivity.
      * intros x Hx. cbn [rho1 rm rho_set_rw]. apply R2. intros HD. apply Hx.
        destruct HD as [HD|[[b0 [Hb0 HD]]|HD]]; [left; exact HD | right; left; exists b0; split; [cbn [dNB G_nblk]; apply in_or_app; left; exact Hb0 | exact HD] | right; right; exact HD].
      * intros z Hz. cbn [rho1 rm rho_set_rw]. apply R3. intros HD. apply Hz.
        destruct HD as [HD|[[b0 [Hb0 HD]]|HD]]; [left; exact HD | right; left; exists b0; split; [cbn [dNB G_nblk]; apply in_or_app; left; exact Hb0 | exact HD] | right; right; exact HD].
    + assert (HK0 : K G0 rho1 tp0 tr md) by (eapply (kd_stable segsA K NPRE HKD G0); [exact Hag | apply mat_equiv_refl | exact HK]).
      eapply (kd_trans segsA K NPRE HKD G0 tp0 md _ tp0 _ rho1 tr); [|exact HK0].
      apply (DT_nblk G0 tp0 md h' a (Z_to_bv 64 NBSZ) Hvm Hna Hrs Hlm ltac:(reflexivity) NBSZ_lit); try assumption; try (change PG with page_size; exact Pal); try exact Pfree.
    + split; [exact HM | apply (depot_vm_grow G0 md h' tp0 _ HV Hvm Hna); reflexivity].
    + cbn beta. split; [rewrite m_vmmaps_with_vmmaps, Hvm; left; reflexivity|].
      split; [change PG with page_size; exact Pal|]. split; [exact Hlo|]. split; [exact Pceil|]. exact Hdisj.
Qed.

Lemma mmap_step_b : ltac2:(tb__ "0|6|
S1S35S3aS49Q40M0S3R1Pb1A2A2S5dVG0;A1M1A3S3eG1SfbA2S35S3aS41S3dG1Z1A2Z10000A2Z0A3S11eS3cVok;S4dS3cS63VG0;A1M2VEBs;R4Vtp0;A5S11bS39S4dS3cG2S15cVEBs;S5S49G0S131S130A1A2A1A2R5Vtp0;R1A6S37S4aG0A1M3G3S4dS3cS6aSfdVG0;S49G0R1A2A2VG0;S72R1A1A3S57VEBs;S14eS51VEBs;A1M4S9S8G4A1M5A1S29S0S6G4A1S25S0S14fG5Sf7A2S26S0A1A3A3S149G5A1A4A2S14dR6G5R1A3Vtp0;R2A6La;A2A2Lw;A4F_;F_;F_;Frho;").
Proof.
  intros rho K177 HDN Hmod.
  apply (triple1_mmap_rw_objA segsA ok (JJ G0) (JJ G0) (fun a => JJ2 (G_nblk G0 (bv_unsigned a)) G0 (PDb a)) EBs rho tp0 NBSZ
           (JJ_ok G0) (JJ2_okp G0 G0 PD0) (JJ_stable G0 (ss_next (ax_S EBs)) ltac:(rewrite EB_nx; unfold NPRE, NXD; lia)) EB_instr EB_r17 EB_r11 ltac:(reflexivity) ltac:(unfold NBSZ; lia)).
  intros tr ms md Hsp HJ.
  destruct (pending_argsA segsA rho tp0 EBs tr ms md Hsp) as (Q0 & Q1 & Q2 & Q3 & Q4 & Q5).
  rewrite EB_r10 in Q0. rewrite EB_r11 in Q1. rewrite EB_r12 in Q2. rewrite EB_r13 in Q3. rewrite EB_r14 in Q4. rewrite EB_r15 in Q5.
  cbn [eval] in Q0, Q1, Q2, Q3, Q4, Q5.
  split; [rewrite Q2, Q3, Q5; apply mmap_modeled_b_intro; reflexivity|].
  split; [rewrite Q3; reflexivity|].
  pose proof HJ as [_ [HK [[HM HV] _]]].
  destruct (kd_room segsA K NPRE HKD G0 rho tp0 _ _ HK (conj HM HV)) as [Hroom _].
  split; [unfold droom in Hroom; rewrite (proj2 (Z.eqb_eq _ _) Hmod) in Hroom; unfold PG, NBSZ in *; cbn [cfg_model w_cfg snd] in Hroom; lia|].
  split; [exact HJ|].
  intros a Hpl. exact (mmap_user_b rho tr ms md a Hsp HJ K177 HDN Hmod Q1 Hpl).
Qed.

Lemma gmid_nblk : ltac2:(tb__ "0|1|
S3aS35S3aS41S3dS5dVG0;A1Z1A2Z10000A2Z0A3S36S65SfdVG0;R2A2M0Vtp0;A2S3eS3dSf5G0A1S120A2S3dSf5VG0;A1Sf6VG0;A1A2A2A2F_;Fa;").
Proof.
  intros a Hmod. unfold gmid, G_nblk, dep_cost, dep_pages, droom. cbn [dN dF dNB dFB dFP]. rewrite length_app. cbn [length].
  rewrite (proj2 (Z.eqb_eq _ _) Hmod).
  split; [|unfold NBSZ, PG; lia]. split; [reflexivity|]. split; [lia|]. split; [exists [a]; reflexivity|]. split; [exists []; symmetry; apply app_nil_r|].
  split; [unfold NBSZ, PG; lia|]. split; [|exists []; reflexivity].
  intros x [HD|[[b0 [Hb0 HD]]|HD]]; [left; exact HD | right; left; exists b0; split; [apply in_or_app; left; exact Hb0 | exact HD] | right; right; exact HD].
Qed.

Lemma armB_main : ltac2:(tb__ "0|0|
S6fS1S69VG0;R1A2S38S119S42S40S3dS5dVG0;A1Z1A2Z10000A2A1S2dS3aS60VG0;A1A2A2A1S11dS3cVok;S4dS3cS63VG0;A1VI3s;R3Vtp0;A5S64A4F_;F_;Frho;F_;").
Proof.
  intros HF rho HIK Hj.
  eapply triple_conseq with (P := fun w => (Z.of_nat (length (dNB G0)) = (dN G0 + 1) / 65536 /\ (dN G0 + 1) mod 65536 = 0 /\ dN G0 <= DNMAX)
                                         /\ SPA segsA (JJ G0) (mkI3b I3s) rho tp0 w); [| intros w Hw; exact Hw |].
  { intros w Hw. destruct (glue_b rho w Hw HIK Hj) as (S & _ & _ & L & M). split; [|exact S]. split; [exact L|]. split; [exact M|].
    destruct w as [tr [ms md]]. pose proof Hw as [_ [_ [HK [[HM HV] _]]]]. exact (proj2 (kd_room segsA K NPRE HKD G0 rho tp0 _ _ HK (conj HM HV))). }
  apply triple_pure. intros (HLj & Hmod & HDN). pose proof HIK as (K177 & K170 & KD1 & KD2).
  apply triple1_triple.
  eapply (stage_run (JJ G0)); [apply JJ_ok | apply JJ_stable; lia | exact RUNB1 | discriminate | exact I3_len | apply Pos.leb_le; reflexivity |].
  intros L rhoL [<-|[]] Hag. cbn [la_state]. cbn [ss_next ax_S ax_setS extN mkI3b] in Hag.
  pose proof (insK_agree G0 rho rhoL Hag HIK) as (L177 & L170 & LD1 & LD2).
  apply triple1_triple. eapply triple1_seq_l; [apply (mmap_step_b rhoL L177 HDN Hmod)|].
  apply triple_disj; [apply fail_spin|].
  apply triple_ex. intros a.

  set (rho1 := rho_set_rw rhoL (ss_next (ax_S EBs)) a).
  assert (E1 : rw rho1 NXD = a) by (unfold rho1; rewrite <- EB_nx; apply rho_set_rw_at).
  assert (AG1 : forall i, (i < NXD)%positive -> rw rho1 i = rw rhoL i) by (intros i Hi; unfold rho1; apply rho_set_rw_other; rewrite EB_nx; lia).
  eapply triple_conseq with (P := SPA segsA (JJ2 (G_nblk G0 (bv_unsigned a)) G0 (PDb a)) (mkOK EBs) rho1 tp0); [| intros w Hw; exact Hw |].
  { intros w Hw. unfold mkOK. apply SPA_refacts; [exact Hw | cbn [ax_S ax_setS S_after ss_next]; rewrite EB_nx; exact EB_fbO |].
    cbn [ax_S ax_setS S_after ss_facts]. intros HF0. apply Forall_app. split; [exact HF0|].
    destruct w as [tr [ms md]]. pose proof Hw as [_ [_ [_ [_ HPD]]]]. cbn [w_tr w_cfg fst snd cfg_model] in HPD. destruct HPD as (_ & Pal & Plo & Phi & _).
    pose proof alloc_ceiling_valD as ACV. pose proof (urange a) as Ra.
    unfold F_a. repeat apply Forall_cons; try apply Forall_nil; cbn [holds eval]; rewrite ?E1.
    - change (2 ^ 12) with PG. split; [unfold PG; lia | exact Pal].
    - rewrite u64_lit by (unfold IMG_HI; lia). exact Plo.
    - rewrite u64_lit by (unfold NBSZ in *; lia). unfold NBSZ in *. lia. }
  apply triple1_triple.
  eapply (stage_run (JJ2 (G_nblk G0 (bv_unsigned a)) G0 (PDb a)));
    [apply JJ2_ok | apply JJ2_stable; [apply PDb_stable | lia] | exact RUNB2 | discriminate | exact EB_len | |].
  { cbn [mkOK ax_with_facts with_facts ax_S ax_setS S_after ss_next]. rewrite EB_nx. apply Pos.leb_le. reflexivity. }
  intros L2 rhoL2 [<-|[]] Hag2. cbn [la_state]. cbn [mkOK ax_with_facts with_facts ax_S ax_setS S_after ss_next] in Hag2. rewrite EB_nx in Hag2.
  destruct Hag2 as (Hw2 & Hl2 & Hm2).
  assert (M177 : bv_unsigned (rw rhoL2 177%positive) = dN G0) by (rewrite <- (Hw2 177%positive) by (unfold NXD; lia); rewrite AG1 by (unfold NXD; lia); exact L177).
  assert (M170 : bv_unsigned (rw rhoL2 170%positive) <= dN G0) by (rewrite <- (Hw2 170%positive) by (unfold NXD; lia); rewrite AG1 by (unfold NXD; lia); exact L170).
  assert (M210 : rw rhoL2 NXD = a) by (rewrite <- (Hw2 NXD) by (unfold NXD; lia); exact E1).
  assert (AG2 : forall i, (i < NXD)%positive -> rw rhoL i = rw rhoL2 i) by (intros i Hi; rewrite <- (Hw2 i) by lia; symmetry; apply AG1; exact Hi).
  assert (AGB : agree_below NXD rhoL rhoL2).
  { split; [exact AG2 | split; [intros l; exact (Hl2 l) | intros x; exact (Hm2 x)]]. }
  pose proof winDFP_wf2 as W. cbn [forallb] in W. apply andb_prop in W as [W1 W]. apply andb_prop in W as [W2 _].
  pose proof (winDFP_agree G0 NXD rhoL rhoL2 (O_tw vW) AGB W1 LD1) as MD1.
  pose proof (winDFP_agree G0 NXD rhoL rhoL2 (O_nid vN) AGB W2 LD2) as MD2.
  eapply triple_conseq with (P := fun w => exists rho', nbK (G_nblk G0 (bv_unsigned a)) rho' /\ SPA segsA (JJ (G_nblk G0 (bv_unsigned a))) NBs rho' tp0 w); [| intros w Hw; exact Hw |].
  { intros w Hw. destruct (glue_bj a rhoL2 w Hw HDN M177 M170 M210 MD1 MD2 HLj Hmod) as (rho' & S' & K'). exists rho'. split; [exact K' | exact S']. }
  apply triple_ex. intros rho'. apply triple_pure. intros HNK.
  destruct (gmid_nblk (bv_unsigned a) Hmod) as [G1 G2].
  exact (frames_cont HF (G_nblk G0 (bv_unsigned a)) tp0 rho' G1 G2 HNK).
Qed.

Lemma paid_ge_usedD : ltac2:(tb__ "0|0|
S12aS27S4aQ40A1A1S3eS136R2A1S16fR2R1A2A2Ftp;Fmd;").
Proof. intros md tp. unfold paid. pose proof page_size_pos. nia. Qed.

Lemma emmap_step_b : ltac2:(tb__ "0|5|
S1S35S3aS49Q40M0S3R1Pb1A2A2S5dVG0;A1M1A3S3eG1SfbA2S35S3aS41S3dG1Z1A2Z10000A2Z0A3S11cS3cS4dS3cS63VG0;A1VEBs;R4Vtp0;A5S11bS37S4aG0A1M2G2S4dS3cS6aSfdVG0;S49G0R1A2A2VG0;S72R1A1A3S57VEBs;S14eS51VEBs;A1M3S9S8G3A1M4A1S29S0S6G3A1S25S0S14fG4Sf7A2S26S0A1A3A3S149G4A1A4A2S14dR6G4R1A3Vtp0;R2A6La;A2Lw;A3F_;F_;F_;Frho;").
Proof.
  intros rho K177 HDN Hmod.
  apply (etriple_mmap_rw_objA segsA (JJ G0) (fun a => JJ2 (G_nblk G0 (bv_unsigned a)) G0 (PDb a)) EBs rho tp0 NBSZ
           (JJ_stable G0 (ss_next (ax_S EBs)) ltac:(rewrite EB_nx; unfold NPRE, NXD; lia)) EB_instr EB_r17 EB_r11 ltac:(reflexivity) ltac:(unfold NBSZ; lia)).
  intros tr ms md Hsp HJ.
  destruct (pending_argsA segsA rho tp0 EBs tr ms md Hsp) as (Q0 & Q1 & Q2 & Q3 & Q4 & Q5).
  rewrite EB_r10 in Q0. rewrite EB_r11 in Q1. rewrite EB_r12 in Q2. rewrite EB_r13 in Q3. rewrite EB_r14 in Q4. rewrite EB_r15 in Q5.
  cbn [eval] in Q0, Q1, Q2, Q3, Q4, Q5.
  split; [rewrite Q2, Q3, Q5; apply mmap_modeled_b_intro; reflexivity|].
  split; [rewrite Q3; reflexivity|].
  pose proof HJ as [_ [HK [[HM HV] _]]].
  destruct (kd_room segsA K NPRE HKD G0 rho tp0 _ _ HK (conj HM HV)) as [Hroom _]. cbn [cfg_model w_cfg snd] in Hroom.
  assert (HroomN : headroom md tp0 >= NBSZ) by (unfold droom in Hroom; rewrite (proj2 (Z.eqb_eq _ _) Hmod) in Hroom; unfold PG, NBSZ in *; lia).
  split; [exact HroomN|].
  destruct (kd_place segsA K NPRE HKD G0 rho tp0 tr md NBSZ HK (conj HM HV) ltac:(left; reflexivity)) as [a Hplm].
  exists a.
  assert (Hpl : mmap_place_ok (ms_gpr ms 0) (ms_gpr ms 3) md (ms_gpr ms 1) a).
  { rewrite Q0, Q1, Q3. pose proof Hplm as (P1 & P2 & P3 & P4). unfold mmap_place_ok.
    split; [exact P1|]. split; [exact P2|]. split; [exact P3|]. split; [exact P4|].
    rewrite (mmap_noreserve_backed_ok_plain (Z_to_bv 64 34) md _ eq_refl). apply Z.leb_le.
    rewrite NBSZ_nZ. pose proof (paid_ge_usedD md tp0). unfold headroom in HroomN. lia. }
  split; [exact Hpl|].
  exact (mmap_user_b rho tr ms md a Hsp HJ K177 HDN Hmod Q1 Hpl).
Qed.

Lemma earmB_main : ltac2:(tb__ "0|0|
S71S1S69VG0;R1A2S38S119S42S40S3dS5dVG0;A1Z1A2Z10000A2A1S2dS3aS60VG0;A1A2A2A1S11cS3cS4dS3cS63VG0;A1VI3s;R3Vtp0;A5S64A3F_;F_;Frho;F_;").
Proof.
  intros HF rho HIK Hj.
  eapply etriple_conseq with (P := fun w => (Z.of_nat (length (dNB G0)) = (dN G0 + 1) / 65536 /\ (dN G0 + 1) mod 65536 = 0 /\ dN G0 <= DNMAX)
                                         /\ SPA segsA (JJ G0) (mkI3b I3s) rho tp0 w); [| intros w Hw; exact Hw |].
  { intros w Hw. destruct (glue_b rho w Hw HIK Hj) as (S & _ & _ & L & M). split; [|exact S]. split; [exact L|]. split; [exact M|].
    destruct w as [tr [ms md]]. pose proof Hw as [_ [_ [HK [[HM HV] _]]]]. exact (proj2 (kd_room segsA K NPRE HKD G0 rho tp0 _ _ HK (conj HM HV))). }
  apply etriple_pure. intros (HLj & Hmod & HDN). pose proof HIK as (K177 & K170 & KD1 & KD2).
  eapply (estage_run (JJ G0)); [apply JJ_stable; lia | exact RUNB1 | discriminate | exact I3_len | apply Pos.leb_le; reflexivity |].
  intros L rhoL [<-|[]] Hag. cbn [la_state]. cbn [ss_next ax_S ax_setS extN mkI3b] in Hag.
  pose proof (insK_agree G0 rho rhoL Hag HIK) as (L177 & L170 & LD1 & LD2).
  eapply etriple_seq; [apply (emmap_step_b rhoL L177 HDN Hmod)|].
  apply etriple_ex. intros a.
  set (rho1 := rho_set_rw rhoL (ss_next (ax_S EBs)) a).
  assert (E1 : rw rho1 NXD = a) by (unfold rho1; rewrite <- EB_nx; apply rho_set_rw_at).
  assert (AG1 : forall i, (i < NXD)%positive -> rw rho1 i = rw rhoL i) by (intros i Hi; unfold rho1; apply rho_set_rw_other; rewrite EB_nx; lia).
  eapply etriple_conseq with (P := SPA segsA (JJ2 (G_nblk G0 (bv_unsigned a)) G0 (PDb a)) (mkOK EBs) rho1 tp0); [| intros w Hw; exact Hw |].
  { intros w Hw. unfold mkOK. apply SPA_refacts; [exact Hw | cbn [ax_S ax_setS S_after ss_next]; rewrite EB_nx; exact EB_fbO |].
    cbn [ax_S ax_setS S_after ss_facts]. intros HF0. apply Forall_app. split; [exact HF0|].
    destruct w as [tr [ms md]]. pose proof Hw as [_ [_ [_ [_ HPD]]]]. cbn [w_tr w_cfg fst snd cfg_model] in HPD. destruct HPD as (_ & Pal & Plo & Phi & _).
    pose proof alloc_ceiling_valD as ACV. pose proof (urange a) as Ra.
    unfold F_a. repeat apply Forall_cons; try apply Forall_nil; cbn [holds eval]; rewrite ?E1.
    - change (2 ^ 12) with PG. split; [unfold PG; lia | exact Pal].
    - rewrite u64_lit by (unfold IMG_HI; lia). exact Plo.
    - rewrite u64_lit by (unfold NBSZ in *; lia). unfold NBSZ in *. lia. }
  eapply (estage_run (JJ2 (G_nblk G0 (bv_unsigned a)) G0 (PDb a)));
    [apply JJ2_stable; [apply PDb_stable | lia] | exact RUNB2 | discriminate | exact EB_len | |].
  { cbn [mkOK ax_with_facts with_facts ax_S ax_setS S_after ss_next]. rewrite EB_nx. apply Pos.leb_le. reflexivity. }
  intros L2 rhoL2 [<-|[]] Hag2. cbn [la_state]. cbn [mkOK ax_with_facts with_facts ax_S ax_setS S_after ss_next] in Hag2. rewrite EB_nx in Hag2.
  destruct Hag2 as (Hw2 & Hl2 & Hm2).
  assert (M177 : bv_unsigned (rw rhoL2 177%positive) = dN G0) by (rewrite <- (Hw2 177%positive) by (unfold NXD; lia); rewrite AG1 by (unfold NXD; lia); exact L177).
  assert (M170 : bv_unsigned (rw rhoL2 170%positive) <= dN G0) by (rewrite <- (Hw2 170%positive) by (unfold NXD; lia); rewrite AG1 by (unfold NXD; lia); exact L170).
  assert (M210 : rw rhoL2 NXD = a) by (rewrite <- (Hw2 NXD) by (unfold NXD; lia); exact E1).
  assert (AG2 : forall i, (i < NXD)%positive -> rw rhoL i = rw rhoL2 i) by (intros i Hi; rewrite <- (Hw2 i) by lia; symmetry; apply AG1; exact Hi).
  assert (AGB : agree_below NXD rhoL rhoL2).
  { split; [exact AG2 | split; [intros l; exact (Hl2 l) | intros x; exact (Hm2 x)]]. }
  pose proof winDFP_wf2 as W. cbn [forallb] in W. apply andb_prop in W as [W1 W]. apply andb_prop in W as [W2 _].
  pose proof (winDFP_agree G0 NXD rhoL rhoL2 (O_tw vW) AGB W1 LD1) as MD1.
  pose proof (winDFP_agree G0 NXD rhoL rhoL2 (O_nid vN) AGB W2 LD2) as MD2.
  eapply etriple_conseq with (P := fun w => exists rho', nbK (G_nblk G0 (bv_unsigned a)) rho' /\ SPA segsA (JJ (G_nblk G0 (bv_unsigned a))) NBs rho' tp0 w); [| intros w Hw; exact Hw |].
  { intros w Hw. destruct (glue_bj a rhoL2 w Hw HDN M177 M170 M210 MD1 MD2 HLj Hmod) as (rho' & S' & K'). exists rho'. split; [exact K' | exact S']. }
  apply etriple_ex. intros rho'. apply etriple_pure. intros HNK.
  destruct (gmid_nblk (bv_unsigned a) Hmod) as [G1 G2].
  exact (eframes_cont HF (G_nblk G0 (bv_unsigned a)) tp0 rho' G1 G2 HNK).
Qed.

Lemma present_cell8 : ltac2:(tb__ "0|0|
S151S3aS152R2R1S3dR1Z8A2A3S37S3aS3aS36S36S3eZ0R1A2S3fR1S44Z2Z40A2A2A2S107R4R3U8R1A4A2Lv;A2F_;Fa;Fm;").
Proof.
  intros m a Hp.
  destruct (Hp a ltac:(lia)) as [b0 H0]. destruct (Hp (a + 1) ltac:(lia)) as [b1 H1]. destruct (Hp (a + 2) ltac:(lia)) as [b2 H2]. destruct (Hp (a + 3) ltac:(lia)) as [b3 H3].
  destruct (Hp (a + 4) ltac:(lia)) as [b4 H4]. destruct (Hp (a + 5) ltac:(lia)) as [b5 H5]. destruct (Hp (a + 6) ltac:(lia)) as [b6 H6]. destruct (Hp (a + 7) ltac:(lia)) as [b7 H7].
  exists (bv_unsigned (le_bytes_to_word [b0; b1; b2; b3; b4; b5; b6; b7])).
  assert (E : Z_to_bv 64 (bv_unsigned (le_bytes_to_word [b0; b1; b2; b3; b4; b5; b6; b7])) = le_bytes_to_word [b0; b1; b2; b3; b4; b5; b6; b7]) by apply Z_to_bv_bv_unsigned.
  split; [pose proof (urange (le_bytes_to_word [b0; b1; b2; b3; b4; b5; b6; b7])); lia|].
  unfold cellZ, cell_ok. cbn [c_addr c_w RtCells.c_val]. intros k Hk. rewrite E. rewrite (enc_bytes_le_word 8) by (reflexivity || lia).
  destruct k as [|[|[|[|[|[|[|[|k]]]]]]]]; cbn [nth]; rewrite ?Z.add_0_r; try assumption. cbn in Hk. lia.
Qed.

Lemma missing_block : ltac2:(tb__ "0|4|
S5cS151S3aS10fR3R2A2S66R4R2A2S38S119S42S40R3Z100000M0A2A1S2dS3aS5eR5A1A2A2A1S36S35S3aS46S2dS3aS5eR6A1A2A1S40R4G0A2M1A3S36S36S3eZ1G1A2S3fG1S106A2A2S36S35S3aS110S5fR6A1M2A1G1A3S36S3eN1fS45G2S43G0G1A2A2M3A2S3eG3Z0A2A2A2A2A2F_;F_;F_;FS;Fm;FG;").
Proof.
  intros G m S HM HHS Hnbl. pose proof Hsz as Hs. unfold SZMAXT in Hs.
  pose proof (dm_F _ _ HM) as (HF0 & _ & HF32 & _). pose proof (proj1 (dm_fb_len _ _ HM)) as FBlen.
  pose proof (fblk_lt (dF G) ltac:(lia) HF32) as FBL.
  pose proof (Z.mod_pos_bound (dF G) 1048576 ltac:(lia)) as MBF. pose proof (Z.div_mod (dF G) 1048576 ltac:(lia)) as DMF.
  assert (Hb0 : 0 <= S / 1048576) by (apply Z.div_pos; [destruct HHS as [->|[-> _]]|]; lia).
  assert (L : Z.of_nat (length (dFB G)) <= S / 1048576) by lia.
  assert (F1 : 1 <= fblk (dF G)) by (unfold fblk; apply Z.div_le_lower_bound; lia).
  destruct (HS_cases G S HHS HF0) as [(ES & EQ & ER)|(ES & EQ & ER & RR)]; rewrite EQ in *.
  - assert (U : fblk (dF G) >= dF G / 1048576) by (unfold fblk; apply Z_div_ge; lia).
    destruct (Z.eq_dec (dF G mod 1048576) 0) as [Z0|NZ]; [unfold NFBLK; lia|].
    assert (U2 : fblk (dF G) = dF G / 1048576 + 1) by (unfold fblk; symmetry; apply (Z.div_unique_pos _ 1048576 (dF G / 1048576 + 1) (dF G mod 1048576 - 1)); lia). lia.
  - assert (U : fblk (dF G) = dF G / 1048576 + 1) by (unfold fblk; symmetry; apply (Z.div_unique_pos _ 1048576 (dF G / 1048576 + 1) (dF G mod 1048576 - 1)); lia). unfold NFBLK. lia.
Qed.

Definition VS_F2 : list positive := [181; 207]%positive.
Let S_F2b : sstate := ltac2:(tb__ "0|0|
S13ScVSJ;A1SfVSJ;A1S16VSJ;A1S15VSJ;A1S17VSJ;A1S29S0S6VSJ;A1S25S0Sa8S5Z0A1A1S25S0Sa9Sa0A1S25S0SacSb0A1S26S0A1A3A3A3A3S7VSJ;A1S95SaVSJ;A1A9").
Hypothesis J_vars2 : ltac2:(tb__ "0|0|
S35S28S140S124S83A1VSJ;A2S2aA3").
Hypothesis J_bvars2 : ltac2:(tb__ "0|0|
S35S28S13fS124S83A1S56VJhs;A1A2S2aA3").
Hypothesis F2b_swf : swf S_F2b = true.
Hypothesis F2_fb : ltac2:(tb__ "0|0|
S35S28S116S4S10S95A1S29S4S7VSJ;A1SdcA3A3S2aA3").

Definition fK (G : DG) (S : Z) (rho : valuation) : Prop := ltac2:(tb__ "0|0|
S36S67VG;VS;Vrho;A3S112S0S68VG;Vrho;A2S25S0Sa8S5Z0A1A1S25S0Sa9Sa0A1S25S0SacSb0A1S26S0A1A3A3A3A3A2").

Lemma OW_f : ltac2:(tb__ "0|0|
S35S28S116S0S14S95A1S25S0Sa8S5Z0A1A1S25S0Sa9Sa0A1S25S0SacSb0A1S26S0A1A3A3A3A3S2aA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma fK_agree : ltac2:(tb__ "0|0|
S5cS3aS1S1SbS95R2R1A3S7bR5R4R3A3S7bR6R5R3A3F_;F_;Frho';Frho;FS;FG;").
Proof.
  intros G S rho rho' Hag [A F]. split; [exact (jK_agree G S rho rho' Hag A)|].
  pose proof OW_f as W. cbn [forallb] in W. apply andb_prop in W as [W1 W]. apply andb_prop in W as [W2 W]. apply andb_prop in W as [W3 _].
  pose proof (Forall_inv F) as F1. pose proof (Forall_inv (Forall_inv_tail F)) as F2. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail F))) as F3.
  repeat apply Forall_cons; [| | | apply Forall_nil]; (eapply winDFP_agree; [exact Hag | | ]); [exact W1 | exact F1 | exact W2 | exact F2 | exact W3 | exact F3].
Qed.

Lemma glue_f2 : ltac2:(tb__ "0|0|
S5cS3aS27S4aQ40A1A1S1S11bS4dS3cS63R5A1VJhs;R2R3R1A6S67R6R5R3A3S66R7R6A2S38S119S42S40R7Z100000A2A1S2dS3aS5eR8A1A2A2A1S37S1S1S36S4dS3cS63RaA1Sd1Vsz;VJhs;A2R1R8R6A6S7bRaR9R1A3A2Lrho';A2F_;F_;F_;F_;Fw;Frho;Ftp;FS;FG;").
Proof.
  intros G S tp rho w H HJK HHS Hnbl. destruct w as [tr [ms md]].
  pose proof H as [HsmA [HREL [HK [[HM HV] _]]]].
  pose proof HJK as (HIK & Hj & H178 & H179 & HROs & HDs). pose proof HIK as (K177 & KW0 & KD1 & KD2).
  pose proof (dm_N _ _ HM) as [HN _]. pose proof (dm_F _ _ HM) as (HF0 & HF11 & HF32 & HFcell).
  destruct (kd_room segsA K NPRE HKD G rho tp _ _ HK (conj HM HV)) as [_ HDN].
  destruct (HS_bounds G S HHS HF0 HF32) as [HSF HS32].
  destruct (missing_block G _ S HM HHS Hnbl) as (HbL & HbR & HFB & HOFF).
  set (b := S / 1048576) in *.
  set (jN := Z.to_nat ((dN G + 1) / 65536)) in *. set (blkN := nth jN (dNB G) 0) in *.
  assert (HinN : In blkN (dNB G)) by (unfold blkN; apply nth_In; exact Hj).
  destruct (dm_nb _ _ HM blkN HinN) as (NBal & NBlo & NBhi & NBpres).
  pose proof (nb_top _ _ _ _ _ _ _ HK HV HinN) as NBhiT.
  destruct (dm_fb_zero _ _ HM b ltac:(lia)) as (FZd & FZs & FZm).
  destruct (present_cell4 (view segsA (rm rho)) (STORE + 24 + 16 * b) ltac:(intros z Hz; apply FZs; lia)) as (stv & Hstv & STcell).
  destruct (present_cell8 (view segsA (rm rho)) (STORE + 8) (dm_alloc _ _ HM)) as (alv & Halv & ALcell).
  pose proof (Z.mod_pos_bound (dN G + 1) 65536 ltac:(lia)) as MBN.
  set (bs := [(181%positive, Z_to_bv 64 stv); (207%positive, Z_to_bv 64 alv)]).
  set (rho' := rho_sets rho bs).
  assert (Hfst : map fst bs = VS_F2) by reflexivity.
  assert (Hnd : List.NoDup (map fst bs)) by (rewrite Hfst; unfold VS_F2; repeat constructor; cbn; lia).
  assert (E181 : rw rho' 181%positive = Z_to_bv 64 stv) by (apply rho_sets_get; [exact Hnd | left; reflexivity]).
  assert (E207 : rw rho' 207%positive = Z_to_bv 64 alv) by (apply rho_sets_get; [exact Hnd | right; left; reflexivity]).
  destruct (rho_sets_rl_rm bs rho) as [Hrl' Hrm']. fold rho' in Hrl', Hrm'.
  assert (Hother : forall i, notin_vars VS_F2 i = true -> rw rho' i = rw rho i).
  { intros i Hi. unfold rho'. apply rho_sets_other. rewrite Hfst. apply notin_vars_true. exact Hi. }
  pose proof alloc_ceiling_valD as ACV.
  assert (U179 : bv_unsigned (rw rho' 179%positive) = S) by (rewrite (Hother 179%positive eq_refl); exact H179).
  assert (U178 : bv_unsigned (rw rho' 178%positive) = blkN) by (rewrite (Hother 178%positive eq_refl); exact H178).
  assert (NNA : bv_unsigned (eval rho' nn_addr) = blkN + 16 * ((dN G + 1) mod 65536)).
  { rewrite (nn_addr_val rho' (dN G)); [rewrite U178; reflexivity | rewrite (Hother 177%positive eq_refl); exact K177 | unfold DNMAX in HDN; lia | rewrite U178; exact NBhi]. }
  assert (BDA : bv_unsigned (eval rho' bd_addr) = STORE + 16 * b) by (apply bd_addr_val; [exact U179 | lia]).
  assert (STA : bv_unsigned (eval rho' stc_addr) = STORE + 16 * b) by (apply stc_addr_val; [exact U179 | lia]).
  assert (Z8 : cellZ (view segsA (rm rho)) (STORE + 16 + 16 * b) 8 0).
  { intros k Hk. cbn [c_addr c_w RtCells.c_val] in Hk |- *. rewrite (FZd (STORE + 16 + 16 * b + Z.of_nat k)) by lia. rewrite (enc_zero_nth 8) by lia. reflexivity. }
  assert (CIVd : cells_in_view rho' (rd_of segsA (rm rho')) (STORE + 16 * b) [(16, 8%nat, SLit 0)]).
  { unfold cells_in_view. constructor; [|constructor]. intros jj Hjj.
    refine (civ_cell rho' (rm rho') (STORE + 16 * b) 16 8 0 (SLit 0) _ _ _ _ jj Hjj); [rewrite Hrm' | reflexivity | unfold STORE; lia | unfold STORE; lia].
    replace (STORE + 16 * b + 16) with (STORE + 16 + 16 * b) by lia. exact Z8. }
  assert (CIVs : cells_in_view rho' (rd_of segsA (rm rho')) (STORE + 16 * b) [(24, 4%nat, vSt)]).
  { unfold cells_in_view. constructor; [|constructor]. intros jj Hjj.
    refine (civ_cell rho' (rm rho') (STORE + 16 * b) 24 4 stv vSt _ _ _ _ jj Hjj); [rewrite Hrm' | cbn [eval]; exact E181 | unfold STORE; lia | unfold STORE; lia].
    replace (STORE + 16 * b + 24) with (STORE + 24 + 16 * b) by lia. exact STcell. }
  assert (CIVa : cells_in_view rho' (rd_of segsA (rm rho')) 0 [(STORE + 8, 8%nat, vAL)]).
  { unfold cells_in_view. constructor; [|constructor]. intros jj Hjj.
    refine (civ_cell rho' (rm rho') 0 (STORE + 8) 8 alv vAL _ _ _ _ jj Hjj); [rewrite Hrm', Z.add_0_l; exact ALcell | cbn [eval]; exact E207 | unfold STORE; lia | unfold STORE; lia]. }
  assert (RGs : forall o, In o [O_tw vW; O_nid vN; O_slotN vNB; O_nn; O_tf vF] -> obj_range rho' o = obj_range rho o).
  { pose proof OWV5 as W. intros o Ho. apply (obj_range_agree_vars (fun i => existsb (Pos.eqb i) [170; 171; 177; 178; 179]%positive) rho rho' o).
    - intros v Hv. symmetry. apply Hother. apply existsb_exists in Hv as (x & Hx & Ex). apply Pos.eqb_eq in Ex. subst. cbn in Hx. unfold notin_vars, VS_F2. cbn. destruct Hx as [<-|[<-|[<-|[<-|[<-|[]]]]]]; reflexivity.
    - intros l. rewrite Hrl'. reflexivity.
    - exact (proj1 (forallb_forall _ _) W o Ho). }
  assert (HIK' : insK G rho').
  { split; [rewrite (Hother 177%positive eq_refl); exact K177|]. split; [rewrite (Hother 170%positive eq_refl); exact KW0|].
    split; [intros a Ha; apply (KD1 a); rewrite <- (RGs (O_tw vW) ltac:(cbn; tauto)); exact Ha | intros a Ha; apply (KD2 a); rewrite <- (RGs (O_nid vN) ltac:(cbn; tauto)); exact Ha]. }
  pose proof (Forall_inv HDs) as WD1. pose proof (Forall_inv (Forall_inv_tail HDs)) as WD2. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail HDs))) as WD3.
  exists rho'. split.
  2:{ split.
      - split; [exact HIK'|]. split; [exact Hj|]. split; [exact U178|]. split; [exact U179|]. split.
        + eapply (ro_win_vars segsA (notin_vars VS_F2)); [intros v Hv; symmetry; apply Hother; exact Hv | intros l; rewrite Hrl'; reflexivity | intros a; rewrite Hrm'; reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | exact HROs].
        + apply Forall_cons; [intros a Ha; apply WD1; rewrite <- (RGs (O_slotN vNB) ltac:(cbn; tauto)); exact Ha|].
          apply Forall_cons; [intros a Ha; apply WD2; rewrite <- (RGs O_nn ltac:(cbn; tauto)); exact Ha|].
          apply Forall_cons; [intros a Ha; apply WD3; rewrite <- (RGs (O_tf vF) ltac:(cbn; tauto)); exact Ha | apply Forall_nil].
      - unfold winDFP, O_bd, O_stc, O_alloc, carved.
        apply Forall_cons. { intros a. rewrite obj_range_mk by lia. cbn [fst snd]. rewrite BDA. intros Ha. left. right. unfold STORE, NFBLK in *. lia. }
        apply Forall_cons. { intros a. rewrite obj_range_mk by lia. cbn [fst snd]. rewrite STA. intros Ha. left. right. unfold STORE, NFBLK in *. lia. }
        apply Forall_cons. { intros a. unfold STORE. rewrite obj_range_mk by lia. cbn [fst snd eval]. rewrite u64_lit by lia. intros Ha. left. right. unfold SegD_wf.STORE, NFBLK. lia. }
        apply Forall_nil. }

  assert (H1 : SPA segsA (JJ G) Jhs rho' tp (tr, mkCfg ms md)).
  { unfold rho'. eapply (SPA_bindV segsA (JJ G) NPRE); [exact J_X | apply JJ_stable; lia | | rewrite Hfst; exact J_vars2 | rewrite Hfst; exact J_bvars2 | exact H].
    rewrite Hfst. unfold VS_F2, NPRE. intros v Hv. cbn in Hv. lia. }
  pose proof (SPA_facts segsA _ _ _ _ _ H1) as HFall'.
  pose proof (holds_inclb rho' _ _ J_F HFall') as HF4. apply Forall_app in HF4 as [HFD HF4]. apply Forall_app in HF4 as [HFt HF4].
  assert (HP : bv_unsigned (rw rho' 171%positive) <= DEPOT + 4 * 2 ^ 20 - 4).
  { pose proof (proj1 (Forall_forall _ _) HFt (SPUle vP (SLit (DEPOT + 4 * 2^20 - 4))) ltac:(unfold F_tw; cbn; tauto)) as X1.
    cbn [holds eval vP] in X1. unfold DEPOT in *. rewrite u64_lit in X1 by lia. exact X1. }
  assert (SNA : DEPOT <= bv_unsigned (eval rho' slotN_addr) /\ bv_unsigned (eval rho' slotN_addr) + 8 <= IMG_HI).
  { rewrite (slotN_addr_val rho' (dN G)); [| rewrite (Hother 177%positive eq_refl); exact K177 | unfold DNMAX in HDN; lia].
    assert (0 <= (dN G + 1) / 65536 < 2 ^ 15) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; unfold DNMAX in HDN; lia]).
    unfold DEPOT, MAP1, IMG_HI. lia. }

  assert (H2 : SPA segsA (JJ G) (ax_setS Jhs S_F2b) rho' tp (tr, mkCfg ms md)).
  { unfold S_F2b, O_bd, O_stc, O_alloc.
    apply (SPA_carve_list segsA (JJ G) rho' Jhs tp _
             [(bd_addr, 16, 24, [(16, 8%nat, SLit 0)]); (stc_addr, 24, 28, [(24, 4%nat, vSt)]); (SLit 0, STORE + 8, STORE + 16, [(STORE + 8, 8%nat, vAL)])]
             NXD H1 F2b_swf ltac:(rewrite J_nx; apply Pos.le_refl)).
    - unfold IMG_HI, NBSZ, FBSZ, FBPAGES, PG, NFBLK in *.
      apply Forall_cons. { rewrite BDA. unfold STORE in *. repeat (split; [lia|]). split; [unfold cells_inside; constructor; [cbn; lia | constructor]|]. split; [|split; [exact CIVd | unfold xwords_clear; cbn [ax_X]; rewrite J_X; intros rr y jj []]].
        intros off Hoff. split; [apply wok_of_imageA; lia | apply rd_of_imageA; lia]. }
      apply Forall_cons. { rewrite STA. unfold STORE in *. repeat (split; [lia|]). split; [unfold cells_inside; constructor; [cbn; lia | constructor]|]. split; [|split; [exact CIVs | unfold xwords_clear; cbn [ax_X]; rewrite J_X; intros rr y jj []]].
        intros off Hoff. split; [apply wok_of_imageA; lia | apply rd_of_imageA; lia]. }
      apply Forall_cons. { cbn [eval]. rewrite u64_lit by lia. unfold STORE. repeat (split; [lia|]). split; [unfold cells_inside; constructor; [cbn; lia | constructor]|]. split; [|split; [exact CIVa | unfold xwords_clear; cbn [ax_X]; rewrite J_X; intros rr y jj []]].
        intros off Hoff. rewrite Z.add_0_l. split; [apply wok_of_imageA; lia | apply rd_of_imageA; lia]. }
      apply Forall_nil.
    - pose proof (proj1 H1) as Hsm1. unfold smatchA, virt in Hsm1. cbn [fst snd cfg_ms cfg_model w_tr w_cfg] in Hsm1. apply proj1 in Hsm1.
      assert (EXD : forall lo hi, STORE + 8 <= lo /\ hi <= DEPOT -> lo <= hi -> Forall (fun o' => ranges_disjoint (obj_range rho' o') (lo, hi)) (ss_objs SJ)).
      { intros lo hi Hlh Hle.
        eapply (objs_ranges_ext rho' SJ _ _ [O_tw vW; O_nid vN; O_slotN vNB; O_nn; O_tf vF] _ _ Hsm1 ltac:(intros o Ho; exact Ho) J_skel HFD ltac:(first [assumption | eapply TOPr_of_REL; eassumption | eapply TOPr_of_JJ; eassumption])); [unfold STORE, DEPOT, IMG_HI in *; lia | unfold STORE, DEPOT, IMG_HI in *; lia | exact Hle |].
        unfold O_tw, O_nid, O_slotN, O_nn, O_tf, carved, ranges_disjoint.
        apply Forall_cons. { rewrite obj_range_mk by lia. cbn [fst snd eval vP].
          pose proof (proj1 (Forall_forall _ _) HFt (SPUle (SLit DEPOT) vP) ltac:(unfold F_tw; cbn; tauto)) as X2. cbn [holds eval vP] in X2. unfold DEPOT in X2. rewrite u64_lit in X2 by lia.
          unfold STORE, DEPOT, IMG_HI in *. lia. }
        apply Forall_cons. { rewrite obj_range_mk by (unfold NIDS; lia). cbn [fst snd eval]. rewrite u64_lit by lia. unfold NIDS, STORE, DEPOT, IMG_HI in *. lia. }
        apply Forall_cons. { rewrite obj_range_mk by lia. cbn [fst snd]. unfold STORE, DEPOT, IMG_HI in *. lia. }
        apply Forall_cons. { rewrite obj_range_mk by lia. cbn [fst snd]. rewrite NNA. unfold STORE, DEPOT, IMG_HI, NBSZ in *. lia. }
        apply Forall_cons. { rewrite obj_range_mk by (unfold STORE; lia). cbn [fst snd eval]. rewrite u64_lit by (unfold STORE; lia). unfold STORE, DEPOT, IMG_HI in *. lia. }
        apply Forall_nil. }
      cbn [map carve_obj]. unfold carved. unfold IMG_HI, NBSZ, FBSZ, FBPAGES, PG, NFBLK in *.
      apply Forall_cons. { rewrite obj_range_mk by lia. rewrite BDA. apply EXD; unfold STORE, DEPOT in *; lia. }
      apply Forall_cons. { rewrite obj_range_mk by lia. rewrite STA. apply EXD; unfold STORE, DEPOT in *; lia. }
      apply Forall_cons. { rewrite obj_range_mk by (unfold STORE; lia). cbn [eval]. rewrite u64_lit by (unfold STORE; lia). apply EXD; unfold STORE, DEPOT; lia. }
      apply Forall_nil.
    - cbn [map carve_obj pairwise_disjoint]. unfold carved. unfold IMG_HI, NBSZ, FBSZ, FBPAGES, PG, NFBLK, STORE in *.
      repeat split; try exact I;
        repeat (apply Forall_cons; [unfold ranges_disjoint; rewrite !obj_range_mk by lia; cbn [fst snd eval]; rewrite ?u64_lit by lia; rewrite ?BDA, ?STA; lia|]); apply Forall_nil. }

  assert (H3 : SPA segsA (JJ G) (ax_with_facts (ax_setS Jhs S_F2b) (ss_facts SJ ++ F_f2)) rho' tp (tr, mkCfg ms md)).
  { apply SPA_refacts; [exact H2 | exact F2_fb |]. cbn [ax_S ax_setS ss_facts]. intros HFX. apply Forall_app. split; [exact HFX|].
    unfold F_f2, vSt. apply Forall_cons; [|apply Forall_nil]. cbn [holds eval]. rewrite E181, !u64_lit by lia. lia. }
  unfold ax_with_facts in H3. rewrite ax_setS_setS in H3. exact H3.
Qed.

Lemma bdoff_val : ltac2:(tb__ "0|3|
S1S3aS3aS35S3aS49Q40M0S3R3Pb3A2A2R2A3S36S3eZ0R3A2M1S3fR3S44Z2M2Z20A2A2A2S36G1S3fR3S44G2Z28A2A2A2S35S3aS49G0SeR6SaaS18S155S18S154S9cS5Z14A1A3S5Z4A1A3S5R4A1A2A2A2S3dS43Z10S40R5Z100000A2A2R4A2A3F_;F_;F_;Fc;FS;Frho;").
Proof.
  intros rho S c HF HB Hc. unfold add, vF. cbn [eval]. rewrite add_val, sll_val, srl_val, HF.
  change (20 mod 64) with 20. change (4 mod 64) with 4. rewrite !u64_lit by lia. rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia.
  change (2 ^ 20) with 1048576. assert (0 <= S / 1048576 < 2 ^ 12) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  rewrite (Z.mod_small (_ * 2 ^ 4)) by lia. rewrite Z.mod_small by lia. lia.
Qed.

Variable C1r : axst.
Hypothesis RUNF1 : ltac2:(tb__ "0|0|
S35S27S52A1S9aUbbbS25S3aZ7cf1cS25S3aZ6bf18S25S3aSb2S26S3aA1A3A3A3Sd1Vsz;VJhs;A2A3S25S52S53VC1r;S126A2S26S52A1A3A3").
Let SC1 : sstate := ax_S C1r.
Let rC : nat -> sv := ltac2:(tb__ "0|0|
S2eS114S2R1SfVSC1;A1S5Z0A1A4Li;").
Definition VS_C1 : list positive := [206]%positive.
Hypothesis C1_X : ax_X C1r = [].
Hypothesis C1_len : ss_lenient SC1 = false.
Hypothesis C1_nx : ltac2:(tb__ "0|0|
S35S3bS8VSC1;A1S95A3").
Hypothesis C1_vars : ltac2:(tb__ "0|0|
S35S28S140S124S80A1VSC1;A2S2aA3").
Hypothesis C1_bvars : ltac2:(tb__ "0|0|
S35S28S13fS124S80A1S56VC1r;A1A2S2aA3").
Hypothesis C1_F : ltac2:(tb__ "0|0|
S35S28S125S29S4S9eS29S4Sa5S29S4Sa7S29S4SabSb4Vsz;A1A3A3A3A3S7VSC1;A1A2S2aA3").
Hypothesis C1_r8 : ltac2:(tb__ "0|0|
S35S2VrC;U8A1SaaS18S155S18S154S9cS5Z14A1A3S5Z4A1A3S5S3dSf9Z1cA2A1A2A3").
Hypothesis C1_r9 : ltac2:(tb__ "0|0|
S35S2VrC;U9A1SaaS18S155S18S154S9cS5Z14A1A3S5Z4A1A3S5S3dSf9Z10A2A1A2A3").
Hypothesis C1_r12 : ltac2:(tb__ "0|0|
S35S2VrC;UcA1S18S157VrC;U8A1S5S45S44Z2Z40A2Z4A2A1A3A3").
Hypothesis C1R_swf : ltac2:(tb__ "0|0|
S35S28S20S51Sc2VC1r;A1A1A1S2aA3").
Hypothesis C1_sd : ltac2:(tb__ "0|5|
S35S2fS2bS27S2bS2S2A2M0A1M1S27S4A1M2A2M3A1S15aVSC1;S51Sc2VC1r;A1A1A2S31G3S2cG1G2S25G0S2cS2S2VrC;U8A1SaaSb8S5Z1cA1A2M4A4S25G0S2cS2S2VrC;U9A1SaaSb8S5Z10A1A2A4S25G0S2cS2S2VrC;UcA1G4A4S25G0S2cS2S2Sc1Sb8A4S25G0S2cS2S2Sd3Sb8A4S26G0A1A3A3A3A3A3S26S4A1A4A2A3").
Hypothesis C1_skel : ltac2:(tb__ "0|2|
S35S27S2bS2bS2S2A2S2A2M0A1S113S0G0S122S6S51Sc2VC1r;A1A1A1A4S113S0G0S122S29S0S29S0S25S0S138S25S0Sa3S26S0A1M1A3A3S29S0S137Sa4A3A3S25S0S97S96A1S25S0S9dS9fA1S25S0S99S9bA1S25S0Sa2S25S0Sa1S9cA1S25S0Sb6S5Z0A1A1S25S0Sb7Sa0A1S25S0SacSb0A1G1A3A3A3A3A3A3A3A3A3A4A3").
Let SC1R : sstate := ax_S (mkC1R C1r).
Let S_C1b : sstate := ltac2:(tb__ "0|0|
S13ScVSC1R;A1SfVSC1R;A1S16VSC1R;A1S15VSC1R;A1S17VSC1R;A1S29S0S6VSC1R;A1S25S0Sb9S26S0A1A3A3S7VSC1R;A1S95SaVSC1R;A1A9").
Hypothesis C1b_swf : swf S_C1b = true.
Hypothesis C1_fb : ltac2:(tb__ "0|0|
S35S28S116S4S10S95A1S29S4S7VSC1;A1S25S4S21PceZ3A2S26S4A1A3A3A3S2aA3").

Definition cK (G : DG) (S : Z) (rho : valuation) : Prop := ltac2:(tb__ "0|0|
S36S67VG;VS;Vrho;A3S36S35S3aS49Q40S3Vrho;PceA2A2S3dSf9S43Z10S40VS;Z100000A2A2A2A3S112S0S68VG;Vrho;A2S25S0Sb6S5Z0A1A1S25S0Sb7Sa0A1S25S0SacSb0A1S25S0Sb9S26S0A1A3A3A3A3A3A2A2").

Lemma STORE_mod8 : STORE mod 8 = 0. Proof. reflexivity. Qed.

Lemma glue_c1 : ltac2:(tb__ "0|0|
S5cS3aS27S4aQ40A1A1S1S1S11bS4dS3cS63R6A1VC1r;R2R4R1A6SbS95R4R3A3S7bR8R7R5A3S66R9R8A2S38S119S42S40R9Z100000A2A1S2dS3aS5eRaA1A2A2A1S37S1S1S36S4dS3cS63RcA1SccVC1r;A1R1RaR7A6S70RcRbR1A3A2Lrho';A2F_;F_;F_;F_;F_;Fw;FrhoL;FrhoI;Ftp;FS;FG;").
Proof.
  intros G S tp rhoI rhoL w H Hag HFK0 HHS Hnbl. destruct w as [tr [ms md]].
  destruct (fK_agree G S rhoI rhoL Hag HFK0) as [HJK HWF]. clear HFK0.
  pose proof H as [HsmA [HREL [HK [[HM HV] _]]]].
  pose proof HJK as (HIK & Hj & H178 & H179 & HROs & HDs). pose proof HIK as (K177 & KW0 & KD1 & KD2).
  pose proof (dm_N _ _ HM) as [HN _]. pose proof (dm_F _ _ HM) as (HF0 & HF11 & HF32 & HFcell).
  destruct (kd_room segsA K NPRE HKD G rhoL tp _ _ HK (conj HM HV)) as [_ HDN].
  destruct (HS_bounds G S HHS HF0 HF32) as [HSF HS32].
  destruct (missing_block G _ S HM HHS Hnbl) as (HbL & HbR & HFB & HOFF).
  set (b := S / 1048576) in *.
  destruct (dm_fb_zero _ _ HM b ltac:(lia)) as (FZd & FZs & FZm).
  pose proof alloc_ceiling_valD as ACV.
  set (bs := [(206%positive, Z_to_bv 64 (STORE + 16 * b))]).
  set (rho' := rho_sets rhoL bs).
  assert (Hfst : map fst bs = VS_C1) by reflexivity.
  assert (Hnd : List.NoDup (map fst bs)) by (rewrite Hfst; unfold VS_C1; repeat constructor; cbn; lia).
  assert (E206 : rw rho' 206%positive = Z_to_bv 64 (STORE + 16 * b)) by (apply rho_sets_get; [exact Hnd | left; reflexivity]).
  destruct (rho_sets_rl_rm bs rhoL) as [Hrl' Hrm']. fold rho' in Hrl', Hrm'.
  assert (Hother : forall i, notin_vars VS_C1 i = true -> rw rho' i = rw rhoL i).
  { intros i Hi. unfold rho'. apply rho_sets_other. rewrite Hfst. apply notin_vars_true. exact Hi. }
  assert (U206 : bv_unsigned (rw rho' 206%positive) = STORE + 16 * b) by (rewrite E206, u64_lit; unfold STORE, NFBLK in *; lia).
  assert (U179 : bv_unsigned (rw rho' 179%positive) = S) by (rewrite (Hother 179%positive eq_refl); exact H179).
  assert (EVM : forall c, 0 <= c < 2 ^ 40 -> bv_unsigned (eval rho' (add vM (SLit c))) = STORE + 16 * b + c).
  { intros c Hc. unfold add, vM. cbn [eval]. rewrite add_val, U206, u64_lit by lia. apply Z.mod_small. unfold STORE, NFBLK in *. lia. }
  assert (BDA : bv_unsigned (eval rho' bd_addr) = STORE + 16 * b) by (apply bd_addr_val; [exact U179 | lia]).
  assert (STA : bv_unsigned (eval rho' stc_addr) = STORE + 16 * b) by (apply stc_addr_val; [exact U179 | lia]).

  assert (H1 : SPA segsA (JJ G) C1r rho' tp (tr, mkCfg ms md)).
  { unfold rho'. eapply (SPA_bindV segsA (JJ G) NPRE); [exact C1_X | apply JJ_stable; lia | | rewrite Hfst; exact C1_vars | rewrite Hfst; exact C1_bvars | exact H].
    rewrite Hfst. unfold VS_C1, NPRE. intros v Hv. cbn in Hv. lia. }

  assert (H2 : SPA segsA (JJ G) (mkC1R C1r) rho' tp (tr, mkCfg ms md)).
  { unfold mkC1R. eapply (SPA_restate segsA (JJ G) rho' C1r _ tp _ _ _ C1R_swf C1_sd).
    - cbn [ax_S ax_setS ss_next]. symmetry. exact C1_nx.
    - unfold diffs_ok. unfold STORE, NFBLK in *.
      assert (E8 : bv_unsigned (eval rho' (rC 8%nat)) = 1834888 + 16 * b + 28) by (rewrite C1_r8; rewrite (bdoff_val rho' S) by lia; lia).
      assert (E9 : bv_unsigned (eval rho' (rC 9%nat)) = 1834888 + 16 * b + 16) by (rewrite C1_r9; rewrite (bdoff_val rho' S) by lia; lia).
      assert (E12 : bv_unsigned (eval rho' (rC 12%nat)) = 1834888 + 16 * b + 28).
      { rewrite C1_r12. cbn [eval]. rewrite and_val, E8, u64_lit by lia. change (2 ^ 64 - 4) with (2 ^ 64 - 2 ^ 2). rewrite land_high_mask by lia.
        replace ((1834888 + 16 * b + 28) mod 2 ^ 2) with 0; [lia|]. symmetry. change (2 ^ 2) with 4.
        replace (1834888 + 16 * b + 28) with ((458722 + 4 * b + 7) * 4) by lia. apply Z_mod_mult. }
      repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; apply bv_eq; rewrite ?EVM by lia.
      + rewrite E8. lia. + rewrite E9. lia. + rewrite E12. lia.
      + unfold vM. cbn [eval]. rewrite BDA, U206. reflexivity.
      + unfold vM. cbn [eval]. rewrite STA, U206. reflexivity.
    - constructor.
    - exact H1. }
  pose proof (SPA_facts segsA _ _ _ _ _ H2) as HFall'. cbn [ax_S ax_setS mkC1R ss_facts] in HFall'.
  pose proof (holds_inclb rho' _ _ C1_F HFall') as HF4. apply Forall_app in HF4 as [HFD HF4]. apply Forall_app in HF4 as [HFt HF4].
  assert (HP : bv_unsigned (rw rho' 171%positive) <= DEPOT + 4 * 2 ^ 20 - 4).
  { pose proof (proj1 (Forall_forall _ _) HFt (SPUle vP (SLit (DEPOT + 4 * 2^20 - 4))) ltac:(unfold F_tw; cbn; tauto)) as X1.
    cbn [holds eval vP] in X1. unfold DEPOT in *. rewrite u64_lit in X1 by lia. exact X1. }
  assert (SNA : DEPOT <= bv_unsigned (eval rho' slotN_addr) /\ bv_unsigned (eval rho' slotN_addr) + 8 <= IMG_HI).
  { rewrite (slotN_addr_val rho' (dN G)); [| rewrite (Hother 177%positive eq_refl); exact K177 | unfold DNMAX in HDN; lia].
    assert (0 <= (dN G + 1) / 65536 < 2 ^ 15) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; unfold DNMAX in HDN; lia]).
    unfold DEPOT, MAP1, IMG_HI. lia. }
  set (jN := Z.to_nat ((dN G + 1) / 65536)) in *. set (blkN := nth jN (dNB G) 0) in *.
  assert (HinN : In blkN (dNB G)) by (unfold blkN; apply nth_In; exact Hj).
  destruct (dm_nb _ _ HM blkN HinN) as (NBal & NBlo & NBhi & NBpres).
  pose proof (nb_top _ _ _ _ _ _ _ HK HV HinN) as NBhiT.
  pose proof (Z.mod_pos_bound (dN G + 1) 65536 ltac:(lia)) as MBN.
  assert (U178 : bv_unsigned (rw rho' 178%positive) = blkN) by (rewrite (Hother 178%positive eq_refl); exact H178).
  assert (NNA : bv_unsigned (eval rho' nn_addr) = blkN + 16 * ((dN G + 1) mod 65536)).
  { rewrite (nn_addr_val rho' (dN G)); [rewrite U178; reflexivity | rewrite (Hother 177%positive eq_refl); exact K177 | unfold DNMAX in HDN; lia | rewrite U178; exact NBhi]. }

  assert (Z4 : cellZ (view segsA (rm rhoL)) (STORE + 28 + 16 * b) 4 0).
  { intros k Hk. cbn [c_addr c_w RtCells.c_val] in Hk |- *. rewrite (FZm (STORE + 28 + 16 * b + Z.of_nat k)) by lia. rewrite (enc_zero_nth 4) by lia. reflexivity. }
  assert (CIVm : cells_in_view rho' (rd_of segsA (rm rho')) (STORE + 16 * b) [(28, 4%nat, SLit 0)]).
  { unfold cells_in_view. constructor; [|constructor]. intros jj Hjj.
    refine (civ_cell rho' (rm rho') (STORE + 16 * b) 28 4 0 (SLit 0) _ _ _ _ jj Hjj); [rewrite Hrm' | reflexivity | unfold STORE; lia | unfold STORE; lia].
    replace (STORE + 16 * b + 28) with (STORE + 28 + 16 * b) by lia. exact Z4. }
  assert (H3 : SPA segsA (JJ G) (ax_setS (mkC1R C1r) S_C1b) rho' tp (tr, mkCfg ms md)).
  { unfold S_C1b, O_mtM.
    apply (SPA_carve_obj segsA (JJ G) rho' (mkC1R C1r) tp _ vM 28 32 [(28, 4%nat, SLit 0)] NXD H2 C1b_swf);
      cbn [ax_S ax_setS mkC1R ss_next ss_objs]; unfold vM; cbn [eval]; rewrite ?U206.
    - apply Pos.le_refl.
    - lia. - lia. - lia. - lia.
    - unfold STORE. lia.
    - unfold STORE, NFBLK in *. lia.
    - unfold cells_inside. constructor; [cbn; lia|constructor].
    - pose proof (proj1 H2) as Hsm1. unfold smatchA, virt in Hsm1. cbn [fst snd cfg_ms cfg_model w_tr w_cfg ax_S ax_setS mkC1R] in Hsm1. apply proj1 in Hsm1.
      eapply (objs_ranges_ext rho' _ _ _ [O_tw vW; O_nid vN; O_slotN vNB; O_nn; O_tf vF; O_bdM (SLit 0); O_stcM vSt; O_alloc vAL] _ _ Hsm1 ltac:(intros o Ho; exact Ho) C1_skel HFD ltac:(first [assumption | eapply TOPr_of_REL; eassumption | eapply TOPr_of_JJ; eassumption]));
        [unfold STORE; lia | unfold STORE, NFBLK, DEPOT in *; lia | lia |].
      unfold O_tw, O_nid, O_slotN, O_nn, O_tf, O_bdM, O_stcM, O_alloc, carved, vM, ranges_disjoint. unfold IMG_HI, NBSZ, NFBLK in *.
      apply Forall_cons. { rewrite obj_range_mk by lia. cbn [fst snd eval vP].
        pose proof (proj1 (Forall_forall _ _) HFt (SPUle (SLit DEPOT) vP) ltac:(unfold F_tw; cbn; tauto)) as X2. cbn [holds eval vP] in X2. unfold DEPOT in X2. rewrite u64_lit in X2 by lia.
        unfold STORE, DEPOT in *. lia. }
      apply Forall_cons. { rewrite obj_range_mk by (unfold NIDS; lia). cbn [fst snd eval]. rewrite u64_lit by lia. unfold NIDS, STORE in *. lia. }
      apply Forall_cons. { rewrite obj_range_mk by lia. cbn [fst snd]. unfold STORE, DEPOT in *. lia. }
      apply Forall_cons. { rewrite obj_range_mk by lia. cbn [fst snd]. rewrite NNA. unfold STORE in *. lia. }
      apply Forall_cons. { rewrite obj_range_mk by (unfold STORE; lia). cbn [fst snd eval]. rewrite u64_lit by (unfold STORE; lia). unfold STORE in *. lia. }
      apply Forall_cons. { rewrite obj_range_mk by lia. cbn [fst snd eval]. rewrite U206. unfold STORE in *. lia. }
      apply Forall_cons. { rewrite obj_range_mk by lia. cbn [fst snd eval]. rewrite U206. unfold STORE in *. lia. }
      apply Forall_cons. { rewrite obj_range_mk by (unfold STORE; lia). cbn [fst snd eval]. rewrite u64_lit by (unfold STORE; lia). unfold STORE in *. lia. }
      apply Forall_nil.
    - intros off Hoff. unfold STORE, NFBLK in *. split; [apply wok_of_imageA; lia | apply rd_of_imageA; lia].
    - exact CIVm.
    - unfold xwords_clear. unfold mkC1R. cbn [ax_X ax_setS]. rewrite C1_X. intros rr y jj [].
  }

  assert (H4 : SPA segsA (JJ G) (ax_with_facts (ax_setS (mkC1R C1r) S_C1b) (ss_facts SC1 ++ [SPAlign 206%positive 3])) rho' tp (tr, mkCfg ms md)).
  { apply SPA_refacts; [exact H3 | exact C1_fb |]. cbn [ax_S ax_setS ss_facts]. intros HFX. apply Forall_app. split; [exact HFX|].
    apply Forall_cons; [|apply Forall_nil]. cbn [holds]. split; [lia|]. rewrite E206, u64_lit by (unfold STORE, NFBLK in *; lia). change (2 ^ 3) with 8.
    replace (STORE + 16 * b) with ((229361 + 2 * b) * 8) by (unfold STORE; lia).     apply Z_mod_mult. }
  exists rho'. split.
  - unfold mkC1, extN. unfold ax_with_facts in H4. rewrite ax_setS_setS in H4. exact H4.
  - assert (RGs : forall o, In o [O_tw vW; O_nid vN; O_slotN vNB; O_nn; O_tf vF] -> obj_range rho' o = obj_range rhoL o).
    { pose proof OWV5 as W. intros o Ho. apply (obj_range_agree_vars (fun i => existsb (Pos.eqb i) [170; 171; 177; 178; 179]%positive) rhoL rho' o).
      - intros v Hv. symmetry. apply Hother. apply existsb_exists in Hv as (x & Hx & Ex). apply Pos.eqb_eq in Ex. subst. cbn in Hx. unfold notin_vars, VS_C1. cbn. destruct Hx as [<-|[<-|[<-|[<-|[<-|[]]]]]]; reflexivity.
      - intros l. rewrite Hrl'. reflexivity.
      - exact (proj1 (forallb_forall _ _) W o Ho). }
    pose proof (Forall_inv HDs) as WD1. pose proof (Forall_inv (Forall_inv_tail HDs)) as WD2. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail HDs))) as WD3.
    pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail HWF))) as WA.
    split; [|split; [exact U206|]].
    + split; [|split; [exact Hj | split; [exact U178 | split; [exact U179 | split]]]].
      * split; [rewrite (Hother 177%positive eq_refl); exact K177|]. split; [rewrite (Hother 170%positive eq_refl); exact KW0|].
        split; [intros a Ha; apply (KD1 a); rewrite <- (RGs (O_tw vW) ltac:(cbn; tauto)); exact Ha | intros a Ha; apply (KD2 a); rewrite <- (RGs (O_nid vN) ltac:(cbn; tauto)); exact Ha].
      * eapply (ro_win_vars segsA (notin_vars VS_C1)); [intros v Hv; symmetry; apply Hother; exact Hv | intros l; rewrite Hrl'; reflexivity | intros a; rewrite Hrm'; reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | exact HROs].
      * apply Forall_cons; [intros a Ha; apply WD1; rewrite <- (RGs (O_slotN vNB) ltac:(cbn; tauto)); exact Ha|].
        apply Forall_cons; [intros a Ha; apply WD2; rewrite <- (RGs O_nn ltac:(cbn; tauto)); exact Ha|].
        apply Forall_cons; [intros a Ha; apply WD3; rewrite <- (RGs (O_tf vF) ltac:(cbn; tauto)); exact Ha | apply Forall_nil].
    + unfold winDFP, O_bdM, O_stcM, O_alloc, O_mtM, carved, vM.
      apply Forall_cons. { intros a. rewrite obj_range_mk by lia. cbn [fst snd eval]. rewrite U206. intros Ha. left. right. unfold STORE, NFBLK in *. lia. }
      apply Forall_cons. { intros a. rewrite obj_range_mk by lia. cbn [fst snd eval]. rewrite U206. intros Ha. left. right. unfold STORE, NFBLK in *. lia. }
      apply Forall_cons. { intros a. unfold STORE. rewrite obj_range_mk by lia. cbn [fst snd eval]. rewrite u64_lit by lia. intros Ha. left. right. unfold SegD_wf.STORE, NFBLK. lia. }
      apply Forall_cons. { intros a. rewrite obj_range_mk by lia. cbn [fst snd eval]. rewrite U206. intros Ha. left. right. unfold STORE, NFBLK in *. lia. }
      apply Forall_nil.
Qed.

Variable EFr : axst.
Hypothesis RUNF2 : ltac2:(tb__ "0|0|
S35S27S52A1S9aUbbcS25S3aZ6bf18S25S3aSb2S26S3aA1A3A3SccVC1r;A1A3S25S52S53VEFr;S127A2S26S52A1A3A3").
Hypothesis EF_X : ax_X EFr = [].
Hypothesis EF_len : ltac2:(tb__ "0|0|
S35S28SaS51VEFr;A1A1S30A3").
Hypothesis EF_nx : ltac2:(tb__ "0|0|
S35S3bS8S51VEFr;A1A1S95A3").
Hypothesis EF_instr : ltac2:(tb__ "0|0|
S35S2fS156A1S128S3cScS51VEFr;A1A1A2S31S156S158A2A3").
Hypothesis EF_r17 : ltac2:(tb__ "0|0|
S35S2S12S51VEFr;A1Z11A2S5ZdeA1A3").
Hypothesis EF_r10 : ltac2:(tb__ "0|0|
S35S2S12S51VEFr;A1ZaA2S5Z0A1A3").
Hypothesis EF_r11 : ltac2:(tb__ "0|0|
S35S2S12S51VEFr;A1ZbA2S5Sf8A1A3").
Hypothesis EF_r12 : ltac2:(tb__ "0|0|
S35S2S12S51VEFr;A1ZcA2S5Z3A1A3").
Hypothesis EF_r13 : ltac2:(tb__ "0|0|
S35S2S12S51VEFr;A1ZdA2S5Z4022A1A3").
Hypothesis EF_r14 : ltac2:(tb__ "0|0|
S35S2S12S51VEFr;A1ZeA2S5ZffffffffffffffffA1A3").
Hypothesis EF_r15 : ltac2:(tb__ "0|0|
S35S2S12S51VEFr;A1ZfA2S5Z0A1A3").
Hypothesis EF_F : ltac2:(tb__ "0|0|
S35S28S125S29S4S9eS29S4Sa5S29S4Sa7S29S4SabSb4Vsz;A1A3A3A3A3S7S51VEFr;A1A1A2S2aA3").
Hypothesis EF_skel : ltac2:(tb__ "0|2|
S35S27S2bS2bS2S2A2S2A2M0A1S113S0G0S122S6S51VEFr;A1A1A4S113S0G0S122S29S0S29S0S25S0S138S25S0Sa3S26S0A1M1A3A3S29S0S137Sa4A3A3S25S0S97S96A1S25S0S9dS9fA1S25S0S99S9bA1S25S0Sa2S25S0Sa1S9cA1S25S0Sb6S5Z0A1A1S25S0Sb7Sa0A1S25S0SacSb0A1S25S0Sb9G1A3A3A3A3A3A3A3A3A3A3A4A3").
Hypothesis EF_fbO : ltac2:(tb__ "0|0|
S35S28S116S4S10S149S95A1A1S29S4S7S51VEFr;A1A1Sd8A3A3S2aA3").
Hypothesis EF_fbF : ltac2:(tb__ "0|0|
S35S28S116S4S10S95A1S29S4S7S51VEFr;A1A1Sc4A3A3S2aA3").

Lemma FBSZ_lit : ltac2:(tb__ "0|1|
S35S3aS49Q40M0S4bG0Sf8A2A2Sf8A3"). Proof. apply u64_lit. unfold FBSZ. lia. Qed.
Lemma FBSZ_nZ : ltac2:(tb__ "0|0|
S35S3aS164S4bQ40Sf8A2A1Sf8A3").
Proof. unfold mmap_nZ. rewrite FBSZ_lit. reflexivity. Qed.
Lemma FBSZ_n : ltac2:(tb__ "0|2|
S35S4aQ40M0A1S163S4bG0Sf8A2M1A1G1A3").
Proof. unfold mmap_n. rewrite FBSZ_nZ. reflexivity. Qed.
Lemma mmap_modeled_nr : ltac2:(tb__ "0|1|
S35S28S169S4bQ40M0Z3A2S4bG0Z4022A2S4bG0Z0A2A3S2aA3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma mmap_noreserve_nr : mmap_noreserve_b (Z_to_bv 64 16418) = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Variables SF1s SF1b SF2s SF2b : axst. Variables sP1 sP2 : wsub.
Hypothesis RUNFF : ltac2:(tb__ "0|0|
S35S27S52A1S9aUbbfS25S3aSc0S25S3aZ6bf18S25S3aSb2S26S3aA1A3A3A3Se8VEFr;A1A3S25S52S53VSF1s;S126A2S25S52S53VSF2s;S126A2S26S52A1A3A3A3").
Hypothesis SF1_len : ltac2:(tb__ "0|0|
S35S28SaS51VSF1s;A1A1S30A3").
Hypothesis SF1_nx : ltac2:(tb__ "0|0|
S35S28S14cS98S8S51VSF1s;A1A1A2S2aA3").
Hypothesis RUNSP1 : ltac2:(tb__ "0|0|
S35S27S52A1S9aU2S25S3aScS51VSF1s;A1A1S26S3aA1A3VSF1s;A3S25S52S53VSF1b;S126A2S26S52A1A3A3").
Hypothesis ENT_P1 : ltac2:(tb__ "0|0|
S35S28S54VSF1b;VSF1s;VsP1;A3S2aA3").
Hypothesis SID_P1 : ltac2:(tb__ "0|0|
S35S28S13aVsP1;S98A2S2aA3").
Hypothesis SF2_len : ltac2:(tb__ "0|0|
S35S28SaS51VSF2s;A1A1S30A3").
Hypothesis SF2_nx : ltac2:(tb__ "0|0|
S35S28S14cS98S8S51VSF2s;A1A1A2S2aA3").
Hypothesis RUNSP2 : ltac2:(tb__ "0|0|
S35S27S52A1S9aU2S25S3aScS51VSF2s;A1A1S26S3aA1A3VSF2s;A3S25S52S53VSF2b;S126A2S26S52A1A3A3").
Hypothesis ENT_P2 : ltac2:(tb__ "0|0|
S35S28S54VSF2b;VSF2s;VsP2;A3S2aA3").
Hypothesis SID_P2 : ltac2:(tb__ "0|0|
S35S28S13aVsP2;S98A2S2aA3").

Lemma fail_spin_f : ltac2:(tb__ "0|1|
S5cS27S4aQ40M0A1A1S1S11dS3cVok;S4dS3cS63R3A1S15cVEFr;S5S49G0S131S130A1A2A1A2R1R2A5S64A4Frho;Ftp;FG;").
Proof.
  intros G tp rho.
  eapply triple_conseq with (P := SPA segsA (JJ G) (mkFAILf EFr) rho tp); [| intros w Hw; exact Hw |].
  { intros w Hw. unfold mkFAILf. apply SPA_refacts; [exact Hw | cbn [ax_S A_after ax_setS S_after ss_next]; rewrite EF_nx; exact EF_fbF |].
    cbn [ax_S A_after ax_setS S_after ss_facts]. intros HF. apply Forall_app. split; [exact HF|].
    pose proof (holds_inclb rho _ _ EF_F HF) as HF3. apply Forall_app in HF3 as [HFD _].
    destruct w as [tr [ms md]]. pose proof (proj1 (proj1 Hw)) as Hsm. unfold virt in Hsm. cbn [fst snd cfg_ms cfg_model w_tr w_cfg ax_S A_after ax_setS] in Hsm.
    assert (Hhigh : holds rho F_sp_high).
    { apply (proj1 (Forall_forall _ _) HFD). unfold F_D, pre_facts. apply in_or_app. left. cbn. tauto. }
    pose proof EF_skel as SK. destruct (ss_objs (ax_S EFr)) as [|osw rest] eqn:EO; [cbn in SK; discriminate SK|].
    cbn [map app] in SK. assert (SKsw : skel osw = (SVar 10, SVar V_DEPTH, SLit 0)) by exact (f_equal (hd (skel osw)) SK).
    destruct (sw_range_gen segsA rho _ _ osw Hsm ltac:(left; reflexivity) SKsw Hhigh) as (SW1 & SW2 & SW3).
    pose proof alloc_ceiling_valD as ACV. pose proof (urange (rw rho 10%positive)) as R10.
    unfold F_f. apply Forall_cons; [|apply Forall_nil]. cbn [holds eval branch_taken]. unfold bv_eqb.
    rewrite add_val, !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
    change ((-192) mod 2 ^ 64) with (2 ^ 64 - 192). change (0 mod 2 ^ 64) with 0.
    assert (E : (bv_unsigned (rw rho 10%positive) + (2 ^ 64 - 192)) mod 2 ^ 64 = bv_unsigned (rw rho 10%positive) - 192).
    { symmetry. apply Z.mod_unique_pos with 1; lia. }
    rewrite E. intros X. apply Z.eqb_eq in X. lia. }
  apply triple1_triple.
  eapply (stage_run (JJ G)); [apply JJ_ok | apply JJ_stable; lia | exact RUNFF | discriminate | | |].
  { cbn [mkFAILf ax_with_facts ax_S ax_setS with_facts A_after S_after ss_lenient]. exact EF_len. }
  { cbn [mkFAILf ax_with_facts ax_S ax_setS with_facts A_after S_after ss_next]. rewrite EF_nx. apply Pos.leb_le. reflexivity. }
  intros L rhoL [<-|[<-|[]]] Hag; cbn [la_state].
  - apply (triple_spin_ent (JJ G) SF1s SF1b sP1 rhoL tp QD (JJ_ok G) (JJ_stable G NPRE ltac:(lia)) RUNSP1 ENT_P1 SID_P1 SF1_len). apply Pos.leb_le. exact SF1_nx.
  - apply (triple_spin_ent (JJ G) SF2s SF2b sP2 rhoL tp QD (JJ_ok G) (JJ_stable G NPRE ltac:(lia)) RUNSP2 ENT_P2 SID_P2 SF2_len). apply Pos.leb_le. exact SF2_nx.
Qed.

Definition PDf (G : DG) (a : word) : pend := ltac2:(tb__ "0|7|
S1S27S4aQ40M0A1M1A1S12aS36S117S2bG1G1A2M2S2cG1G1Va;S4bG0Sf8A2A4M3S12eS12bR1A1A1A3S36S117G2G3S135R1A1A3S36S35S3aS41S49G0Va;A2M4S120A2Z0M5A3S36S3eS121G4A2S36S3eS3dG4Sf8A2Valloc_ceiling;A2S36S2bS3aS3aA2M6S117G6R1S108VG;A1A3S109R2S2cS3aS3aG4Sf8A4A2F_;Fbn;S36S3aS36S3eG5R1A2S3fR1Sf8A2A2S35S28S16bS12fS12bR3A1A1S3dG4R2A2A2S30A3F_;Fj;S16dR2S25G2G3S26G2A1A3A2A2A2A2A2A2A2A2Lmd;Ltp;L_;").
Lemma PDf_stable : ltac2:(tb__ "0|0|
S5cS4aQ40A1S7fS73R2R1A2A1Fa;FG;").
Proof. intros G a rho rho' tp md md' Hag ((mat' & ->) & _) H. exact H. Qed.

Lemma depot_vm_fblk : ltac2:(tb__ "0|2|
S5cS12aS27S4aQ40M0A1M1A1G1SfaR4R3R2A3S35S2eS2dS3aS61R5A1A2S2dS3aS5eR5A1A2A3S73R6R3Vrho0;R4R5A5S35S3aS12dS12bR6A1A1Valloc_ceiling;A3SfaSfcR8S49G0R5A2A2R7R6A3F_;F_;F_;F_;Fa;Ftp;Fmd;FG;").
Proof.
  intros G md tp a [DM DL DA DT DTOP DTR] HL (Pm & Pl & Pal & Plo & Phi & Pdj & Pna & Ptp) Htop. pose proof alloc_ceiling_valD as ACV. pose proof (urange a) as Ra.
  assert (Ea : Z_to_bv 64 (bv_unsigned a) = a) by apply Z_to_bv_bv_unsigned.
  constructor; cbn [dNB dFB dFP G_fblk].
  - intros bn Hbn. rewrite dblocks_fblk in Hbn. apply in_app_or in Hbn as [Hbn|[<-|[]]]; [exact (DM bn Hbn)|]. unfold wentry. cbn [fst snd]. rewrite Ea. exact Pm.
  - intros b Hb. apply in_app_or in Hb as [Hb|[<-|[]]]; [exact (DL b Hb)|]. rewrite Ea. exact Pl.
  - intros b j Hb Hj. apply in_app_or in Hb as [Hb|[<-|[]]]; [exact (DA b j Hb Hj)|]. exact (Pna j Hj).
  - intros b k Hb Hk. unfold G_fblk, fpage in Hb |- *. cbn [dFB dFP] in Hb |- *. rewrite length_app in Hb. cbn [length] in Hb.
    destruct (lt_dec b (length (dFB G))) as [L|L].
    + rewrite !app_nth1 by lia. exact (DT b k L Hk).
    + assert (b = length (dFB G)) as -> by lia.
      rewrite !app_nth2 by lia. rewrite HL, Nat.sub_diag. cbn [nth].
      split; [|lia]. intros Hin. exfalso. pose proof (Ptp _ Hin) as X.
      assert (Y : page_in_ranges (Z_to_bv 64 (bv_unsigned a + PG * k)) [(a, Z_to_bv 64 FBSZ)] = true).
      { apply (proj2 (page_in_ranges_spec _ _)). exists (a, Z_to_bv 64 FBSZ). split; [left; reflexivity|].
        apply (proj2 (page_in_range_spec _ _)). cbn [fst snd]. rewrite FBSZ_lit, u64_lit by (unfold PG, FBSZ, FBPAGES in *; lia). change page_size with PG. unfold PG, FBSZ, FBPAGES in *. lia. }
      rewrite Y in X. discriminate X.
  -   intros bn Hbn. rewrite dblocks_fblk in Hbn. apply in_app_or in Hbn as [Hbn|[<-|[]]]; [exact (DTOP bn Hbn)|]. cbn [fst snd]. rewrite Htop. exact Phi.
  - exact DTR.
Qed.

Lemma depot_vm_grow_lazy : ltac2:(tb__ "0|3|
S5cS12aS133S27S4aQ40A1M0A1G0G0SfaR6R5R3A3S35S27S2bG0G0A2M1A1M2S12eR5A1S25G1S2cG0G0R3R2A4S12eS12bR6A1A1A3A3S35G2S12fR6A1S12fS12bR7A1A1A3S35S3aS12dR7A1S12dS12bR8A1A1A3SfaRaS134R6R5S132R8R9A2A3R7A3F_;F_;F_;F_;Fn;Fa;Ftp;Fh';Fmd;FG;").
Proof.
  intros G md h' tp a n [DM DL DA DT DTOP DTR] Hm Hn Ht. constructor; rewrite ?m_vmmaps_vm_add_lazy, ?m_vm_lazy_vm_add_lazy, ?m_vmmaps_with_vmmaps, ?m_vm_lazy_with_vmmaps, ?Ht; try assumption.
  - intros bn Hbn. rewrite Hm. right. exact (DM bn Hbn).
  - intros b Hb. apply in_or_app. right. exact (DL b Hb).
  - intros b j Hb Hj. rewrite Hn. exact (DA b j Hb Hj).
Qed.

Lemma EF_objs_clear : ltac2:(tb__ "0|a|
S5cS3aS1S147S4aQ40M0A1S112S0S1eS3cR3R2A3S6S51VEFr;A1A1M1A3S112S4S1aR4A1S29S4S9eS29S4Sa5S29S4Sa7S29S4SabSb4Vsz;A1A3A3A3A3A3S6dR5A1S35S3aS49G0S3R6Pb1A2A2S5dR8A1A3S36S3eZ1M2S5dR9A1M3A2S3eG3SfbA2A2S3eS3dS49G0S3R8Pb2M4A2A2Sf7A2Z7fffff800000A2S35S3aS49G0S3R9PceA2A2S3dSf9S43Z10S40RaZ100000M5A2A2A2A3S36S3eG2S40RbG5A2M6A2S3fG6S106A2A2S3eS121S49G0R9A2A2S3eS3dS49G0RaA2Sf8A2Valloc_ceiling;A2S3aS36S3eS49G0RcA2M7R1A2S3fR1S3dG7Sf8A2A2A2S38S36S3eS49G0S3RfG4A2A2M8R2A2S3fR2S3dG8Sf7A2A2A2A1F_;Fx;S112S0S0S19S11RfR1A2S2cS3aS3aS49G0RdA2M9S3dG9Sf8A2A4A2Lo;G1A3F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fa;Fms;Frho;FS;FG;").
Proof.
  intros G S rho ms a Hsm HF HT K177 HDN NBhi U206 Hb Hlo Hhi Hnb. apply Forall_app in HF as [HFD HF]. apply Forall_app in HF as [HFt HFn].
  pose proof alloc_ceiling_valD as ACV.
  assert (SA : bv_unsigned (eval rho slotN_addr) = MAP1 + 8 * ((dN G + 1) / 65536)) by (apply slotN_addr_val; [exact K177 | unfold DNMAX in HDN; lia]).
  assert (HjNz : 0 <= (dN G + 1) / 65536 < 2 ^ 15) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; unfold DNMAX in HDN; lia]).
  pose proof (Z.mod_pos_bound (dN G + 1) 65536 ltac:(lia)) as MBN.
  assert (NNA : bv_unsigned (eval rho nn_addr) = bv_unsigned (rw rho 178%positive) + 16 * ((dN G + 1) mod 65536)).
  { rewrite (nn_addr_val rho (dN G)); [reflexivity | exact K177 | unfold DNMAX in HDN; lia | exact NBhi]. }
  eapply (objs_ranges_ext_mm rho ms _ _ [O_tw vW; O_nid vN; O_slotN vNB; O_nn; O_tf vF; O_bdM (SLit 0); O_stcM vSt; O_alloc vAL; O_mtM] _ _ Hsm ltac:(intros o Ho; exact Ho) EF_skel HFD ltac:(first [assumption | eapply TOPr_of_REL; eassumption | eapply TOPr_of_JJ; eassumption]));
    [unfold STORE, IMG_HI in *; lia | lia | unfold FBSZ; lia |].
  unfold O_tw, O_nid, O_slotN, O_nn, O_tf, O_bdM, O_stcM, O_alloc, O_mtM, carved, vM, ranges_disjoint. unfold IMG_HI, NFBLK, STORE, FBSZ in *.
  apply Forall_cons. { rewrite obj_range_mk by lia. cbn [fst snd eval vP].
    pose proof (proj1 (Forall_forall _ _) HFt (SPUle vP (SLit (DEPOT + 4 * 2^20 - 4))) ltac:(unfold F_tw; cbn; tauto)) as X2. cbn [holds eval vP] in X2. unfold DEPOT in X2. rewrite u64_lit in X2 by lia.
    unfold DEPOT in *. lia. }
  apply Forall_cons. { rewrite obj_range_mk by (unfold NIDS; lia). cbn [fst snd eval]. rewrite u64_lit by lia. unfold NIDS in *. lia. }
  apply Forall_cons. { rewrite obj_range_mk by lia. cbn [fst snd]. rewrite SA. unfold MAP1 in *. lia. }
  apply Forall_cons. { rewrite obj_range_mk by lia. cbn [fst snd]. rewrite NNA. unfold NBSZ in *.
    destruct (Z_lt_le_dec (bv_unsigned (rw rho 178%positive) + 16 * ((dN G + 1) mod 65536) + 16) (bv_unsigned a + 1)) as [L|L]; [lia|].
    destruct (Z_lt_le_dec (bv_unsigned a + 8388608) (bv_unsigned (rw rho 178%positive) + 16 * ((dN G + 1) mod 65536) + 1)) as [L2|L2]; [lia|]. exfalso.
    destruct (Z_lt_le_dec (bv_unsigned a) (bv_unsigned (rw rho 178%positive) + 16 * ((dN G + 1) mod 65536))) as [L3|L3].
    - apply (Hnb (bv_unsigned (rw rho 178%positive) + 16 * ((dN G + 1) mod 65536))); lia.
    - apply (Hnb (bv_unsigned a)); lia. }
  apply Forall_cons. { rewrite obj_range_mk by lia. cbn [fst snd eval]. rewrite u64_lit by lia. lia. }
  apply Forall_cons. { rewrite obj_range_mk by lia. cbn [fst snd eval]. rewrite U206. lia. }
  apply Forall_cons. { rewrite obj_range_mk by lia. cbn [fst snd eval]. rewrite U206. lia. }
  apply Forall_cons. { rewrite obj_range_mk by lia. cbn [fst snd eval]. rewrite u64_lit by lia. lia. }
  apply Forall_cons. { rewrite obj_range_mk by lia. cbn [fst snd eval]. rewrite U206. lia. }
  apply Forall_nil.
Qed.

Lemma mmap_user_f : ltac2:(tb__ "0|c|
S5cS3aS1S27S4aQ40M0A1M1A1S27S12cA1M2S147S12aG1S15eS3cR6R5VEFr;S2cG2S143R4S144R3R2A2A4A5S63R9R7R6R5R3A5S70RaR9R8A3S66RbRaA2S38S119S42S40RbZ100000A2A1S2dS3aS5eRcA1A2A2A1S35G1S146R8U1M3A2S4bG0Sf8A2M4A3S165S146R9U0A2S146R9U3A2R8S146R9G3A2R7A5S36S0S117S0R1S6S51VEFr;A1M5A1A3S19S11RfR2A2S2cS3aS3aS49G0RaA2M6S3dG6Sf8A2A4A2F_;Fo;S36S3aS36S3eS49G0R9A2M7R1A2S3fR1S3dG7Sf8A2A2A2S35S2fS160A1S148S3cR2Z1A3S34S160A1A3F_;Fz;S36S2bS2S2A2M8S3aS117G8R2S59VEFr;A1A3S36S3eS49G0SeR10S33S2S2R3A3A2A2M9R2A2S3fR2S3dG9S49G0SeR10S32S2S2R3A3A2A2A2A2A2S38S36S3eS49G0RcA2MaS49G0S5aS49G0SeR11S56VEFr;A1A2A2R3A2A2MbA2S3fGbS3dGaSf8A2A2A2A1F_;F_;Fy;Fr;S6aSfcRfS49G0R8A2A2RfS73RfR8A2S14dS159RdS15fSdRdA1R8G4A3A2S8G5A1R8A3RcRbS134R8G4S132S166S12bR9A1S146RaG3A2R8A3R9A2A3A7A2A2A2F_;F_;F_;F_;F_;F_;F_;Fa;Fmd;Fms;Ftr;Ftp;Frho;FS;FG;").
Proof.
  intros G S rho tp tr ms md a Hsp HJ HCK HHS Hnbl G1 Hpl.
  pose proof HJ as [HREL [HK [[HM HV] _]]]. pose proof HCK as ((HIK & Hj & H178 & H179 & HROs & HDs) & U206 & HWC). pose proof HIK as (K177 & KW0 & KD1 & KD2).
  pose proof alloc_ceiling_valD as ACV. pose proof (urange a) as Ra. pose proof Hsz as Hs. unfold SZMAXT in Hs.
  pose proof (smatch_pendingA_MI segsA _ _ _ _ _ _ Hsp) as HMI. pose proof HMI as (HW & HT & Hmat & Hsub & Hpaid & Hlc & Hivs & Hlim & Htm).
  pose proof (dm_N _ _ HM) as [HN _]. pose proof (dm_F _ _ HM) as (HF0 & HF11 & HF32 & _).
  destruct (kd_room segsA K NPRE HKD G rho tp _ _ HK (conj HM HV)) as [Hroom HDN].
  destruct (missing_block G _ S HM HHS Hnbl) as (HbL & HbR & HFB & HOFF).
  rewrite G1 in Hpl. pose proof Hpl as (Pal & Ppos & Pceil & Pfree & _). rewrite FBSZ_nZ in Pceil. rewrite FBSZ_n in Pfree. pose proof Pceil as PceilM. rewrite (HKT _ _ _ _ _ HK) in Pceil.
  pose proof (kd_reserved segsA K NPRE HKD G rho tp tr md HK) as Hres.
  destruct (grant_facts_A _ _ md _ a Hpl Hres) as (_ & _ & _ & Himg & Hmaps). rewrite FBSZ_nZ in Himg, Hmaps.
  assert (Hlo : IMG_HI <= bv_unsigned a).
  { unfold IMG_HI, FBSZ in *. destruct (Z_lt_le_dec (bv_unsigned a) 0x10000) as [L|L].
    - exfalso. apply (Himg 0x10000); lia.
    - destruct (Z_lt_le_dec (bv_unsigned a) 0x643000) as [L2|L2]; [exfalso; apply (Himg (bv_unsigned a)); lia | exact L2]. }
  assert (Hdisj : forall bn, In bn (dblocks G) -> ranges_disjointZ bn (bv_unsigned a, FBSZ)).
  { intros [b0 n0] Hbn. pose proof (dv_maps _ _ _ HV _ Hbn) as Hm. unfold wentry in Hm. cbn [fst snd] in Hm.
    pose proof (depot_inv_bounds segsA G rho md tp (conj HM HV)) as (_ & _ & BB & _). destruct (BB _ Hbn) as (B1 & B2 & _). cbn [fst snd] in B1, B2.
    assert (N0 : 0 < n0 < 2 ^ 40) by (unfold dblocks in Hbn; apply in_app_or in Hbn as [Hbn|Hbn]; apply in_map_iff in Hbn as (q & E & _); injection E; intros; subst; unfold NBSZ, FBSZ; lia).
    unfold ranges_disjointZ. cbn [fst snd]. unfold IMG_HI in *.
    destruct (Z_lt_le_dec (b0 + n0) (bv_unsigned a + 1)) as [L|L]; [lia|].
    destruct (Z_lt_le_dec (bv_unsigned a + FBSZ) (b0 + 1)) as [L2|L2]; [lia|]. exfalso.
    destruct (Z_lt_le_dec (bv_unsigned a) b0) as [L3|L3].
    - apply (Hmaps _ _ Hm b0); rewrite ?u64_lit by lia; unfold FBSZ in *; lia.
    - apply (Hmaps _ _ Hm (bv_unsigned a)); rewrite ?u64_lit by lia; unfold FBSZ in *; lia. }
  set (jN := Z.to_nat ((dN G + 1) / 65536)) in *. set (blkN := nth jN (dNB G) 0) in *.
  assert (HinN : In blkN (dNB G)) by (unfold blkN; apply nth_In; exact Hj).
  destruct (dm_nb _ _ HM blkN HinN) as (NBal & NBlo & NBhi & NBpres).
  pose proof (nb_top _ _ _ _ _ _ _ HK HV HinN) as NBhiT.
  assert (Hnb : forall x, bv_unsigned a <= x < bv_unsigned a + FBSZ -> ~ (bv_unsigned (rw rho 178%positive) <= x < bv_unsigned (rw rho 178%positive) + NBSZ)).
  { intros x Hx. rewrite H178. pose proof (Hdisj (blkN, NBSZ) ltac:(unfold dblocks; apply in_or_app; left; apply in_map_iff; exists blkN; split; [reflexivity | exact HinN])) as D.
    unfold ranges_disjointZ in D. cbn [fst snd] in D. lia. }
  pose proof (smatch_pendingA_sp segsA _ _ _ _ _ _ Hsp) as Hsm0.

  set (h' := mmap_rw_vm (m_vmmaps md) (ms_gpr ms 1) a).
  assert (Hvm : vm_maps h' = (a, Z_to_bv 64 FBSZ) :: vm_maps (m_vmmaps md)) by (unfold h', mmap_rw_vm; rewrite G1, FBSZ_n; reflexivity).
  assert (Hna : vm_noaccess h' = vm_noaccess (m_vmmaps md)) by reflexivity.
  assert (Hrs : vm_reserved h' = vm_reserved (m_vmmaps md)) by reflexivity.
  assert (Hvl : vm_limit h' = vm_limit (m_vmmaps md)) by reflexivity.
  assert (Hend : bv_unsigned a + bv_unsigned (Z_to_bv 64 FBSZ) <= 2 ^ 64) by (rewrite FBSZ_lit; unfold FBSZ in *; lia).
  assert (HfreeM : region_free (vm_maps (m_vmmaps md)) a (Z_to_bv 64 FBSZ) = true) by exact (region_free_app_r _ _ _ _ Pfree).
  assert (Hclr : tp_clear_of tp (lazy_interior a (Z_to_bv 64 FBSZ))) by exact (tp_clear_of_region_free md tp a _ Htm (proj1 Hivs) HfreeM Hend).
  assert (HLI : lazy_interior a (Z_to_bv 64 FBSZ) = [(a, Z_to_bv 64 FBSZ)]).
  { apply lazy_interior_aligned; rewrite ?FBSZ_lit; [exact Pal | reflexivity | unfold FBSZ; lia | unfold FBSZ in *; lia]. }
  assert (Hpaidle : paid (vm_add_lazy a (Z_to_bv 64 FBSZ) (with_vmmaps h' md)) tp <= paid md tp).
  { rewrite (paid_add_lazy _ a _ tp Hclr), paid_with_vmmaps.
    pose proof (used_rw_noreserve_le md h' a (Z_to_bv 64 FBSZ) Hivs Pal ltac:(rewrite FBSZ_lit; reflexivity) ltac:(rewrite FBSZ_lit; unfold FBSZ; lia) Hend Hvm Hna). lia. }
  split; [|split; [|split]].
  - intros o Ho. pose proof (smatch_pending_facts segsA _ _ _ _ _ Hsm0) as HFall.
    pose proof (holds_inclb rho _ _ EF_F HFall) as HF3.
    assert (Hall : Forall (obj_holds segsA rho (vms md tp ms)) (ss_objs (ax_S EFr))).
    { destruct Hsm0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hall & _ & _) & _). exact Hall. }
    rewrite <- H178 in NBhi.
    exact (proj1 (Forall_forall _ _) (EF_objs_clear G S rho _ a Hall HF3 ltac:(first [assumption | eapply TOPr_of_REL; eassumption | eapply TOPr_of_JJ; eassumption]) K177 ltac:(lia) NBhi U206 HbR Hlo Pceil Hnb) o Ho).
  - intros z Hz. apply find_segment_A_off. unfold IMG_HI in Hlo. lia.
  - rewrite EF_X. intros r y [].
  - set (rhoU := set_rm rho (unmap_range (rm rho) a (Z_to_bv 64 FBSZ))). set (rho1 := rho_set_rw rhoU (ss_next (ax_S EFr)) a).
    set (md1 := vm_add_lazy a (Z_to_bv 64 FBSZ) (with_vmmaps h' md)).
    assert (AgU : agree_below NPRE rhoU rho1) by (unfold rho1; apply agree_below_set_rw; rewrite EF_nx; unfold NPRE, NXD; lia).

    assert (RMU : forall x : word, ~ (bv_unsigned a <= bv_unsigned x < bv_unsigned a + FBSZ) -> rm rhoU x = rm rho x).
    { intros x Hx. unfold rhoU. cbn [rm set_rm]. rewrite unmap_range_at. destruct (in_range a (Z_to_bv 64 FBSZ) x) eqn:E; [|reflexivity].
      exfalso. apply Hx. apply in_range_spec in E. rewrite FBSZ_lit in E. exact E. }
    assert (VU : forall z, ~ (bv_unsigned a <= z < bv_unsigned a + FBSZ) -> view segsA (rm rhoU) z = view segsA (rm rho) z).
    { intros z Hz. unfold view. destruct ((0 <=? z) && (z <? 2 ^ 64))%bool eqn:E; [|reflexivity]. unfold rd_of. rewrite RMU; [reflexivity|].
      apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2. rewrite u64_lit by lia. exact Hz. }
    assert (GW : forall z, bv_unsigned a <= z < bv_unsigned a + FBSZ -> DFPw (G_fblk G (bv_unsigned a)) z).
    { intros z Hz. right. right. exists (bv_unsigned a). split; [unfold G_fblk; cbn [dFB]; apply in_or_app; right; left; reflexivity | exact Hz]. }
    assert (GOUT : forall z, DFP G z -> ~ (bv_unsigned a <= z < bv_unsigned a + FBSZ)).
    { intros z [Hst|[[b0 [Hb0 Hz]]|[b0 [Hb0 Hz]]]] Hin.
      - unfold dfp_static, DEPOT, MAP1, MAP1N, STORE, NFBLK, IMG_HI in *. lia.
      - pose proof (Hdisj (b0, NBSZ) ltac:(unfold dblocks; apply in_or_app; left; apply in_map_iff; exists b0; split; [reflexivity | exact Hb0])) as D. unfold ranges_disjointZ in D. cbn [fst snd] in D. lia.
      - pose proof (Hdisj (b0, FBSZ) ltac:(unfold dblocks; apply in_or_app; right; apply in_map_iff; exists b0; split; [reflexivity | exact Hb0])) as D. unfold ranges_disjointZ in D. cbn [fst snd] in D. lia. }
    assert (DFPmono : forall z, DFP G z -> DFP (G_fblk G (bv_unsigned a)) z).
    { intros z [X|[X|[b0 [Hb0 X]]]]; [left; exact X | right; left; exact X | right; right; exists b0; split; [unfold G_fblk; cbn [dFB]; apply in_or_app; left; exact Hb0 | exact X]]. }
    assert (DFPwmono : forall z, DFPw G z -> DFPw (G_fblk G (bv_unsigned a)) z).
    { intros z [X|[X|[b0 [Hb0 X]]]]; [left; exact X | right; left; exact X | right; right; exists b0; split; [unfold G_fblk; cbn [dFB]; apply in_or_app; left; exact Hb0 | exact X]]. }
    split; [|split; [|split]].
    + destruct HREL as ((R1 & R1') & R2 & R3). split; [split|split].
      * intros i Hi. rewrite (R1 i Hi). unfold rho1. symmetry. rewrite rho_set_rw_other by (rewrite EF_nx; unfold NPRE, NXD in *; lia). reflexivity.
      * intros l. rewrite (R1' l). reflexivity.
      * intros x Hx. unfold rho1. cbn [rm rho_set_rw]. rewrite RMU; [apply R2; intros HD; apply Hx; apply DFPmono; exact HD|].
        intros Hin. apply Hx. apply DFPw_DFP. apply GW. exact Hin.
      * intros z Hz. unfold rho1. cbn [rm rho_set_rw]. rewrite VU; [apply R3; intros HD; apply Hz; apply DFPwmono; exact HD|].
        intros Hin. apply Hz. apply GW. exact Hin.
    + assert (HK1 : K (G_fblk G (bv_unsigned a)) rho tp tr md1).
      { eapply (kd_trans segsA K NPRE HKD G tp md _ tp _ rho tr); [|exact HK].
        unfold md1. apply (DT_fblk G tp md h' a (Z_to_bv 64 FBSZ) Hvm Hna Hrs Hvl ltac:(reflexivity) FBSZ_lit); assumption. }
      assert (HK2 : K (G_fblk G (bv_unsigned a)) rhoU tp tr md1).
      { eapply (kd_view segsA K NPRE HKD _ rho rhoU); [intros i; reflexivity | intros l; reflexivity | | exact HK1].
        intros z Hz. apply VU. intros Hin. exact (Hz (GW z Hin)). }
      eapply (kd_stable segsA K NPRE HKD); [exact AgU | apply mat_equiv_refl | exact HK2].
    + split.
      * apply (depot_mem_frame G (view segsA (rm rho))); [|exact HM]. intros z Hz. unfold rho1. cbn [rm rho_set_rw]. apply VU. exact (GOUT z Hz).
      * unfold md1. apply (depot_vm_grow_lazy G md h' tp a _ HV Hvm Hna). reflexivity.
    + unfold PDf, md1. rewrite m_vmmaps_vm_add_lazy, m_vm_lazy_vm_add_lazy, m_vmmaps_with_vmmaps, m_vm_lazy_with_vmmaps, Hvm, Hna, HLI.
      split; [left; reflexivity|]. split; [left; reflexivity|]. split; [change PG with page_size; exact Pal|]. split; [exact Hlo|]. split; [exact Pceil|].
      split; [exact Hdisj|]. split.
      * intros j Hjj. destruct (covered (vm_noaccess (m_vmmaps md)) (bv_unsigned a + j)) eqn:E; [|reflexivity]. exfalso.
        unfold covered in E. apply existsb_exists in E as ([c m] & Hc & Hin). unfold in_iv, in_rng, ivB, ivS in Hin. cbn [fst snd] in Hin.
        apply andb_prop in Hin as [Hin1 Hin2]. apply Z.leb_le in Hin1. apply Z.ltb_lt in Hin2.
        destruct (kd_noacc segsA K NPRE HKD G rho tp tr md c m (bv_unsigned a + j) HK Hc ltac:(lia)) as (b0 & m0 & Hbm & Hx).
        apply (Hmaps _ _ Hbm (bv_unsigned a + j)); lia.
      * rewrite <- HLI. exact Hclr.
Qed.

Lemma mmap_step_f : ltac2:(tb__ "0|4|
S5cS3aS1S27S4aQ40M0A1M1A1S70R4R3R2A3S66R5R4A2S38S119S42S40R5Z100000A2A1S2dS3aS5eR6A1A2A2A1S11eS3cVok;S4dS3cS63R7A1VEFr;R5R4A5S11bS39S4dS3cS63R8A1S15cVEFr;S5S49G0S131S130A1A2A1A2R6R5R1A6S37G1G1S4dS3cS6aSfcR9S49G0R1A2A2R9S73R9R1A2A3S57VEFr;S14eS51VEFr;A1M2S9S8G2A1M3A1S6G2A1S149G3A1A4A2S14dS159R7S15fSdR7A1R1S4bG0Sf8A2A3A2G3R1A3R6R2A6La;A2A2Lw;A4F_;F_;F_;Ftp;Frho;FS;FG;").
Proof.
  intros G S rho tp HCK HHS Hnbl.
  apply (triple1_mmap_lazyA segsA ok (JJ G) (JJ G) (fun a => JJ2 (G_fblk G (bv_unsigned a)) G (PDf G a)) EFr rho tp FBSZ
           (JJ_ok G) (JJ2_okp G G PD0) (JJ_stable G (ss_next (ax_S EFr)) ltac:(rewrite EF_nx; unfold NPRE, NXD; lia)) EF_instr EF_r17 EF_r11 ltac:(reflexivity) ltac:(unfold FBSZ; lia)).
  intros tr ms md Hsp HJ.
  destruct (pending_argsA segsA rho tp EFr tr ms md Hsp) as (Q0 & Q1 & Q2 & Q3 & Q4 & Q5).
  rewrite EF_r10 in Q0. rewrite EF_r11 in Q1. rewrite EF_r12 in Q2. rewrite EF_r13 in Q3. rewrite EF_r14 in Q4. rewrite EF_r15 in Q5.
  cbn [eval] in Q0, Q1, Q2, Q3, Q4, Q5.
  split; [rewrite Q2, Q3, Q5; exact mmap_modeled_nr|].
  split; [rewrite Q3; exact mmap_noreserve_nr|].
  split; [exact HJ|].
  intros a Hpl. exact (mmap_user_f G S rho tp tr ms md a Hsp HJ HCK HHS Hnbl Q1 Hpl).
Qed.

Lemma emmap_step_f : ltac2:(tb__ "0|4|
S5cS3aS1S27S4aQ40M0A1M1A1S70R4R3R2A3S66R5R4A2S38S119S42S40R5Z100000A2A1S2dS3aS5eR6A1A2A2A1S11cS3cS4dS3cS63R7A1VEFr;R5R4A5S11bS37G1G1S4dS3cS6aSfcR9S49G0R1A2A2R9S73R9R1A2A3S57VEFr;S14eS51VEFr;A1M2S9S8G2A1M3A1S6G2A1S149G3A1A4A2S14dS159R7S15fSdR7A1R1S4bG0Sf8A2A3A2G3R1A3R6R2A6La;A2Lw;A3F_;F_;F_;Ftp;Frho;FS;FG;").
Proof.
  intros G S rho tp HCK HHS Hnbl.
  apply (etriple_mmap_lazyA segsA (JJ G) (fun a => JJ2 (G_fblk G (bv_unsigned a)) G (PDf G a)) EFr rho tp FBSZ
           (JJ_stable G (ss_next (ax_S EFr)) ltac:(rewrite EF_nx; unfold NPRE, NXD; lia)) EF_instr EF_r17 EF_r11 ltac:(reflexivity) ltac:(unfold FBSZ; lia)).
  intros tr ms md Hsp HJ.
  destruct (pending_argsA segsA rho tp EFr tr ms md Hsp) as (Q0 & Q1 & Q2 & Q3 & Q4 & Q5).
  rewrite EF_r10 in Q0. rewrite EF_r11 in Q1. rewrite EF_r12 in Q2. rewrite EF_r13 in Q3. rewrite EF_r14 in Q4. rewrite EF_r15 in Q5.
  cbn [eval] in Q0, Q1, Q2, Q3, Q4, Q5.
  split; [rewrite Q2, Q3, Q5; exact mmap_modeled_nr|].
  split; [rewrite Q3; exact mmap_noreserve_nr|].
  pose proof HJ as [_ [HK [[HM HV] _]]].
  destruct (kd_place segsA K NPRE HKD G rho tp tr md FBSZ HK (conj HM HV) ltac:(right; reflexivity)) as [a Hplm].
  exists a.
  assert (Hpl : mmap_place_ok (ms_gpr ms 0) (ms_gpr ms 3) md (ms_gpr ms 1) a).
  { rewrite Q0, Q1, Q3. pose proof Hplm as (P1 & P2 & P3 & P4). unfold mmap_place_ok.
    split; [exact P1|]. split; [exact P2|]. split; [exact P3|]. split; [exact P4|].
    unfold mmap_noreserve_backed_ok. rewrite mmap_noreserve_nr. reflexivity. }
  split; [exact Hpl|].
  exact (mmap_user_f G S rho tp tr ms md a Hsp HJ HCK HHS Hnbl Q1 Hpl).
Qed.

Lemma ro_win_setrm : ltac2:(tb__ "0|5|
S1S4aQ40M0A1M1S2fS4aQ8A1A1M2Fx;S0S123S3cR3R1A3G1S36S3eS33S3aS3aS11R5R3A2M3A3S49G0R1A2M4A2S3fG4S32S3aS3aG3A3A2A2S35G2R5R2A1SdR6R2A2A3F_;Fa;S123S3cS159R5R4A2R3A3F_;F_;Fo;Fm;Frho;").
Proof.
  intros rho m o (base & off & k & v & -> & H1 & H2 & H3 & H4 & H5 & H6) Hrm.
  unfold carved in Hrm. rewrite obj_range_mk in Hrm by lia. cbn [fst snd] in Hrm.
  exists base, off, k, v. rewrite !eval_set_rm. repeat (split; [first [reflexivity | assumption]|]).
  unfold cells_in_view in *. constructor; [|constructor].
  intros j Hj. rewrite eval_set_rm. pose proof (Forall_inv H6) as Y. cbn beta iota in Y. rewrite <- (Y j Hj).
  unfold rd_of. cbn [rm set_rm]. rewrite Hrm; [reflexivity|]. rewrite u64_lit by lia. lia.
Qed.

Definition c3K (G : DG) (S : Z) (a : word) (rho : valuation) : Prop := ltac2:(tb__ "0|3|
S36S69VG;Vrho;A2S36S119S42S40S3dS5dVG;A1Z1A2Z10000A2A1M0S2dS3aS60VG;A1M1A2A2S36S35S3aS49Q40M2S3Vrho;Pb2A2A2S114S3aG0G1Z0A4A3S36S35S3aS49G2S3Vrho;Pb3A2A2VS;A3S36S35S3aS49G2S3Vrho;PceA2A2S3dSf9S43Z10S40VS;Z100000A2A2A2A3S36S35S4aG2A1S3Vrho;S95A2Va;A3S123S3cVrho;S99S9bA1A3A2A2A2A2A2A2").

Lemma OW_cm : ltac2:(tb__ "0|0|
S35S28S116S0S14S149S95A1A1S25S0S97S96A1S25S0S9dS9fA1S25S0S99S9bA1S26S0A1A3A3A3A3S2aA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma c3K_agree : ltac2:(tb__ "0|0|
S5cS3aS4aQ40A1S1S1SbS149S95A1R2R1A3S78R6R5R4R3A4S78R7R6R5R3A4F_;F_;Frho';Frho;Fa;FS;FG;").
Proof.
  intros G S a rho rho' Hag ((A1 & A2 & A3 & A4) & B & C & D & E & F & R).
  pose proof OW_cm as W. cbn [forallb] in W. apply andb_prop in W as [W1 W]. apply andb_prop in W as [W2 W]. apply andb_prop in W as [W3 _].
  pose proof Hag as (Hw & Hl & Hm).
  split; [split; [rewrite <- (Hw 177%positive) by (unfold NXD; lia); exact A1 | split; [rewrite <- (Hw 170%positive) by (unfold NXD; lia); exact A2 | split; eapply winDFP_agree; eauto]]|].
  split; [exact B|]. split; [rewrite <- (Hw 178%positive) by (unfold NXD; lia); exact C|]. split; [rewrite <- (Hw 179%positive) by (unfold NXD; lia); exact D|].
  split; [rewrite <- (Hw 206%positive) by (unfold NXD; lia); exact E|]. split; [rewrite <- (Hw NXD) by (unfold NXD; lia); exact F|].
  eapply ro_win_agree; [exact Hag | exact W3 | exact R].
Qed.

Lemma cK_after_grant : ltac2:(tb__ "0|4|
S5cS3aS1S4aQ40M0A1M1G1S2fS4aQ8A1A1M2Fx;S70R5R4R3A3G1S3fS49G0R1A2S121A2S35G2R4R2A1SdR6R2A2A3F_;Fx;S36S3eZ1S5dR7A1M3A2S3eG3SfbA2A2S78R8R7R5S14dS159R6R4A2S8S51VEFr;A1A1R5A3A4F_;F_;F_;Fm;Fa;Frho;FS;FG;").
Proof.
  intros G S rho a m ((HIK & Hj & H178 & H179 & HROs & HDs) & U206 & _) Hm HDN. pose proof HIK as (K177 & KW0 & KD1 & KD2).
  rewrite EF_nx.
  assert (AG : agree_below NXD (set_rm rho m) (rho_set_rw (set_rm rho m) NXD a)) by (apply agree_below_set_rw; lia).
  pose proof winDFP_wf2 as W. cbn [forallb] in W. apply andb_prop in W as [W1 W]. apply andb_prop in W as [W2 _].
  assert (R : forall i, (i < NXD)%positive -> rw (rho_set_rw (set_rm rho m) NXD a) i = rw rho i) by (intros i Hi; rewrite rho_set_rw_other by lia; reflexivity).
  split; [split; [rewrite R by (unfold NXD; lia); exact K177 | split; [rewrite R by (unfold NXD; lia); exact KW0 | split]]|].
  - eapply winDFP_agree; [exact AG | exact W1 |]. intros x Hx. apply KD1. unfold obj_range in Hx |- *. rewrite !eval_set_rm in Hx. exact Hx.
  - eapply winDFP_agree; [exact AG | exact W2 |]. intros x Hx. apply KD2. unfold obj_range in Hx |- *. rewrite !eval_set_rm in Hx. exact Hx.
  - split; [exact Hj|]. split; [rewrite R by (unfold NXD; lia); exact H178|]. split; [rewrite R by (unfold NXD; lia); exact H179|].
    split; [rewrite R by (unfold NXD; lia); exact U206|]. split; [apply rho_set_rw_at|].
    eapply ro_win_agree; [exact AG | apply OW_slotN |]. apply ro_win_setrm; [exact HROs|].
    intros x Hx. apply Hm. unfold O_slotN, carved in Hx. rewrite obj_range_mk in Hx by lia. cbn [fst snd] in Hx.
    rewrite (slotN_addr_val rho (dN G) K177 ltac:(unfold DNMAX in HDN; lia)) in Hx.
    assert (0 <= (dN G + 1) / 65536 < 2 ^ 15) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; unfold DNMAX in HDN; lia]).
    unfold MAP1, IMG_HI in *. lia.
Qed.

Variable C3r : axst. Variable sC3 : wsub.
Hypothesis RUNF4 : ltac2:(tb__ "0|0|
S35S27S52A1S9aUbbdS25S3aSc0S25S3aZ6bf18S25S3aSb2S26S3aA1A3A3A3SedVEFr;A1A3S25S52S53VC3r;S126A2S26S52A1A3A3").
Hypothesis C3_X : ax_X C3r = [].
Hypothesis C3_nx : ltac2:(tb__ "0|0|
S35S3bS8S51VC3r;A1A1S149S95A1A3").
Definition O_mtM2 : sobj := ltac2:(tb__ "0|4|
S15bSb8Z1cM0Z20S25S2bS2bS3aS2eA2M1S2A2M2S2cG1S2S2cS3aS2eG0U1A4S5Z0A1M3A4S25G2S2cG1S2S2cS3aS2eZ1dU3A4G3A4S26G2A1A3A3A4").
Let P3 : list sobj := ltac2:(tb__ "0|1|
S115S0S153S2dS0S6S51VC3r;A1A1M0A2U4A2G0A3").
Let R4 : list sobj := ltac2:(tb__ "0|0|
S25S0Sb6S9S95A1A1S25S0Sb7Sa0A1S25S0SacSaaSb0S5Sf8A1A2A1S25S0S8bS26S0A1A3A3A3A3").
Hypothesis C3_objs : ltac2:(tb__ "0|0|
S35S27S0A1S6S51VC3r;A1A1S29S0VP3;VR4;A3A3").
Hypothesis C3_skel : ltac2:(tb__ "0|2|
S35S27S2bS2bS2S2A2S2A2M0A1S113S0G0S122VP3;A4S113S0G0S122S29S0S29S0S25S0S138S25S0Sa3S26S0A1M1A3A3S29S0S137Sa4A3A3S25S0S97S96A1S25S0S9dS9fA1S25S0S99S9bA1S25S0Sa2S25S0Sa1S9cA1G1A3A3A3A3A3A3A4A3").
Hypothesis C3_F : ltac2:(tb__ "0|0|
S35S28S125S29S4S9eS29S4Sa5S29S4Sa7S29S4SabSb4Vsz;A1A3A3A3A3S7S51VC3r;A1A1A2S2aA3").
Let S_C3b : sstate := ltac2:(tb__ "0|1|
S13ScS51VC3r;A1M0A1SfG0A1S16G0A1S15G0A1S17G0A1S29S0VP3;S25S0Sa8S9S95A1A1S25S0SdeVsz;A1S25S0Sa9Sa0A1S26S0A1A3A3A3A3S7G0A1S8G0A1SaG0A1A9").
Hypothesis C3b_swf : swf S_C3b = true.
Hypothesis ENT_C3 : ltac2:(tb__ "0|0|
S35S28S54Se3Vsz;VC3r;A2VE2hs;VsC3;A3S2aA3").
Hypothesis SID_C3 : ltac2:(tb__ "0|0|
S35S28S13aVsC3;S98A2S2aA3").
Definition ids6f (s : wsub) : bool := ltac2:(tb__ "0|0|
S116S3bS3bS1cS13bVs;R1A2S9R1A1A2Li;S25S3bPaaS25S3bPabS25S3bPb1S25S3bPb2S25S3bPb3S25S3bPb5S26S3bA1A3A3A3A3A3A3A3").
Hypothesis IDS_C3 : ids6f sC3 = true.
Hypothesis SC3_180 : ltac2:(tb__ "0|0|
S35S2S13bVsC3;Pb4A2S9S95A1A3").

Lemma ids6f_rw : ltac2:(tb__ "0|0|
S13cS1S3bS35S28S92R3A1S2aA3S117S3bR2S25S3bPaaS25S3bPabS25S3bPb1S25S3bPb2S25S3bPb3S25S3bPb5S26S3bA1A3A3A3A3A3A3A3S35S4aQ40A1S3S13dR4R5A2R3A2S3R4R3A2A3F_;F_;Fi;Frho;Fs;").
Proof.
  intros s rho i H Hi. unfold ids6f in H. pose proof (proj1 (forallb_forall _ _) H i Hi) as X. apply sv_eqb_sound in X.
  cbn [rw rho_sub]. rewrite X. reflexivity.
Qed.

Lemma list_upd_app_last {T} : ltac2:(tb__ "0|2|
S27VT;A1M0VT;VT;S35G0S62VT;S29VT;R3S25VT;R2S26VT;A1M1A3A3S2dVT;R3A2R1A4S29VT;R3S25VT;R1G1A3A3A3Fy;Fx;Fl;").
Proof. induction l; intros x y; cbn; [reflexivity | rewrite IHl; reflexivity]. Qed.
Lemma sumZ_app : ltac2:(tb__ "0|1|
S27S3aA1M0G0S35S3aS103S29S3aR2R1A3A1S3dS103R2A1S103R1A1A2A3Fl2;Fl1;").
Proof. induction l1; intros l2; cbn; [reflexivity | rewrite IHl1; unfold sumZ; cbn; lia]. Qed.

Lemma gmid_fblk_page : ltac2:(tb__ "0|3|
S5cS27S4aQ40M0A1M1A1S3aS65R3R2A2S3eS3dSf5R4A1S120A2S3dSf5VG0;A1Sf6VG0;A1A2A2S35S2eS2dS3aS61R5A1A2S2dS3aS5eR5A1A2A3S36S65S100SfcR6R4A2S2dS3aS5eR6A1A2A2M2S25G1S4bG0R4A2R5A3A2S35S3aSf5G2A1S3dSf5R6A1S120A2A3A2F_;F_;F_;Fa;Ftp;FG;").
Proof.
  intros G tp a (M1 & M2 & M3 & [lF M4] & M5 & M6 & [l M7]) Hbud HL.
  assert (DC : dep_cost (G_page (G_fblk G a) (length (dFB G))) = dep_cost G + PG).
  { unfold G_fblk. rewrite <- HL. unfold G_page, dep_cost, dep_pages. cbn [dN dF dNB dFB dFP]. rewrite list_upd_app_last.
    rewrite app_nth2 by lia. rewrite Nat.sub_diag. cbn [nth]. rewrite sumZ_app. cbn [sumZ fold_right]. unfold PG. lia. }
  split; [|exact DC]. unfold gmid. rewrite DC. unfold G_page, G_fblk. cbn [dN dF dNB dFB dFP].
  split; [exact M1|]. split; [exact M2|]. split; [exact M3|]. split; [exists (lF ++ [a]); rewrite M4, app_assoc; reflexivity|].
  split; [lia|]. split; [|exists (Z_to_bv 64 a :: l); rewrite M7; reflexivity].
  intros x Hx. destruct (M6 x Hx) as [X|[X|[b0 [Hb0 X]]]]; [left; exact X | right; left; exact X | right; right; exists b0; split; [apply in_or_app; left; exact Hb0 | exact X]].
Qed.

Lemma glue_c3 : ltac2:(tb__ "0|4|
S5cS3aS4aQ40M0A1M1S1S27G1A1S11bS2dS3aS5eR6A1A2S2eSfcR7S49G0R5A2A2S5cS100R1R2A2S5cS4dS3cS6aR2R9S73R9R7A2A3VC3r;R6R5R4A6S78RaR9R8R7A4S66RbRaA2S38S119S42S40RbZ100000M2A2A1S2dS3aS5eRcA1A2A2A1S3fS3dS41RcG2A2Vsz;A2G2A2S65ReRaA2S3eS3dSf5RfA1S120A2S3dSf5VG0;A1Sf6VG0;A1A2A2S37S1S1S36S4dS3cS63R9A1VE2hs;R1S25G1RfRdA3M3RcA6S36S6cR9RbR10R1A4S36S74R9R10A2S36S65R9G3A2S35S2eS42S40R10G2A2A1RbA3A2A2A2A2Lrho';A2F_;F_;F_;F_;F_;F_;F_;TG2;TG1;Tb;Fw;Ftp;FrhoL;Fa;FS;FG;").
Proof.
  intros G S a rhoL tp w b G1 G2 H HCK HHS Hnbl Hns HG Hbud. destruct w as [tr [ms md]].
  pose proof H as [HsmA [HREL [HK [[HM HV] HPD]]]]. cbn [w_tr w_cfg fst snd cfg_model] in HK, HV, HPD.
  pose proof HPD as (Pm & Pl & Pal & Plo & Phi & Pdj & Pna & Ptp).
  pose proof HCK as ((K177 & KW0 & KD1 & KD2) & Hj & H178 & H179 & U206 & E210 & HROs).
  pose proof (proj1 HsmA) as Hsm. unfold virt in Hsm. cbn [fst snd cfg_ms cfg_model w_tr w_cfg] in Hsm.
  pose proof alloc_ceiling_valD as ACV. pose proof (urange a) as Ra. pose proof Hsz as Hs. unfold SZMAXT in Hs.
  pose proof (dm_N _ _ HM) as [HN _]. pose proof (dm_F _ _ HM) as (HF0 & HF11 & HF32 & _). pose proof (proj2 (dm_fb_len _ _ HM)) as HL.
  destruct (HS_bounds G S HHS HF0 HF32) as [HSF HS32].
  destruct (missing_block G _ S HM HHS Hnbl) as (HbL & HbR & HFB & HOFF). fold b in HbL.
  assert (Hbn : b = Z.to_nat (S / 1048576)) by lia.
  assert (Ea : Z_to_bv 64 (bv_unsigned a) = a) by apply Z_to_bv_bv_unsigned.
  set (jN := Z.to_nat ((dN G + 1) / 65536)) in *. set (blkN := nth jN (dNB G) 0) in *.
  assert (HinN : In blkN (dNB G)) by (unfold blkN; apply nth_In; exact Hj).
  destruct (dm_nb _ _ HM blkN HinN) as (NBal & NBlo & NBhi & NBpres).
  pose proof (nb_top _ _ _ _ _ _ _ HK HV HinN) as NBhiT.
  pose proof (Z.mod_pos_bound (dN G + 1) 65536 ltac:(lia)) as MBN. pose proof (Z.mod_pos_bound S 1048576 ltac:(lia)) as MBS.
  assert (HSmod : S mod 1048576 <= 30).
  { pose proof (Z.div_mod S 1048576 ltac:(lia)) as DMS. destruct (HS_cases G S HHS HF0) as [(ES & EQ & ER)|(ES & EQ & ER & RR)]; [|lia].
    rewrite ER. rewrite EQ in HOFF. pose proof (Z.div_mod (dF G) 1048576 ltac:(lia)). pose proof (Z.mod_pos_bound (dF G) 1048576 ltac:(lia)). lia. }

  assert (EVM : bv_unsigned (eval rhoL vM) = STORE + 16 * Z.of_nat b) by (unfold vM; cbn [eval]; rewrite U206, HbL; reflexivity).
  assert (BDA : bv_unsigned (eval rhoL bd_addr) = STORE + 16 * Z.of_nat b) by (rewrite HbL; apply bd_addr_val; [exact H179 | lia]).
  assert (STA : bv_unsigned (eval rhoL stc_addr) = STORE + 16 * Z.of_nat b) by (rewrite HbL; apply stc_addr_val; [exact H179 | lia]).
  assert (Hb1 : 1 <= Z.of_nat b < NFBLK) by lia.

  assert (DNB : blkN + NBSZ <= bv_unsigned a \/ bv_unsigned a + FBSZ <= blkN).
  { pose proof (Pdj (blkN, NBSZ) ltac:(unfold dblocks; apply in_or_app; left; apply in_map_iff; exists blkN; split; [reflexivity | exact HinN])) as D. unfold ranges_disjointZ in D. cbn [fst snd] in D. lia. }

  pose proof (SPA_facts segsA _ _ _ _ _ H) as HFall.
  pose proof (holds_inclb rhoL _ _ C3_F HFall) as HF3. apply Forall_app in HF3 as [HFD HF3]. apply Forall_app in HF3 as [HFt _].

  assert (Hw0 : SPA segsA (fun _ _ _ _ => True) C3r rhoL tp (tr, mkCfg ms md)) by (split; [exact HsmA | exact I]).
  pose proof (SPA_unobj segsA (fun _ _ _ _ => True) rhoL C3r P3 R4 tp tr ms md C3_objs Hw0 (fun _ => I)) as HwA.
  cbn zeta in HwA. set (rhoA := rho_absorb rhoL R4 (vms md tp ms)) in *.
  assert (CIVd := absorb_view_cells segsA rhoL (ax_S C3r) tr (vms md tp ms) (vmd md) P3 R4 vM 16 24 [(16, 8%nat, SVar NXD)] Hsm C3_objs
                    ltac:(unfold R4; cbn; tauto) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold cells_inside; constructor; [cbn; lia|constructor])
                    ltac:(rewrite EVM; unfold STORE; lia) ltac:(rewrite EVM; unfold STORE, NFBLK in *; lia)).
  assert (CIVs := absorb_view_cells segsA rhoL (ax_S C3r) tr (vms md tp ms) (vmd md) P3 R4 vM 24 28 [(24, 4%nat, vSt)] Hsm C3_objs
                    ltac:(unfold R4; cbn; tauto) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold cells_inside; constructor; [cbn; lia|constructor])
                    ltac:(rewrite EVM; unfold STORE; lia) ltac:(rewrite EVM; unfold STORE, NFBLK in *; lia)).
  assert (CIVa := absorb_view_cells segsA rhoL (ax_S C3r) tr (vms md tp ms) (vmd md) P3 R4 (SLit 0) (STORE + 8) (STORE + 16) [(STORE + 8, 8%nat, add vAL (SLit FBSZ))] Hsm C3_objs
                    ltac:(unfold R4; cbn; tauto) ltac:(unfold STORE; lia) ltac:(lia) ltac:(unfold STORE; lia) ltac:(unfold cells_inside; constructor; [cbn; lia|constructor])
                    ltac:(cbn [eval]; rewrite u64_lit by lia; unfold STORE; lia) ltac:(cbn [eval]; rewrite u64_lit by lia; unfold STORE; lia)).
  assert (CIVm := absorb_view_cells segsA rhoL (ax_S C3r) tr (vms md tp ms) (vmd md) P3 R4 vM 28 32 [(28, 1%nat, SLit 0); (29, 3%nat, SLit 0)] Hsm C3_objs
                    ltac:(unfold R4; cbn; tauto) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold cells_inside; repeat constructor; cbn; lia)
                    ltac:(rewrite EVM; unfold STORE; lia) ltac:(rewrite EVM; unfold STORE, NFBLK in *; lia)).
  fold rhoA in CIVd, CIVs, CIVa, CIVm. rewrite EVM in CIVd, CIVs, CIVm. cbn [eval] in CIVa. rewrite u64_lit in CIVa by lia.
  destruct CIVd as [Cd _]. destruct CIVs as [Cs Ps]. destruct CIVa as [_ Pa]. destruct CIVm as [Cm _].
  assert (VOUTA : forall x : word, ~ (STORE + 8 <= bv_unsigned x < STORE + 16) -> ~ (STORE + 16 + 16 * Z.of_nat b <= bv_unsigned x < STORE + 32 + 16 * Z.of_nat b) ->
                  rm rhoA x = rm rhoL x).
  { intros x H1 H2. unfold rhoA. apply rm_absorb_out. intros (o & Ho & Hr). unfold R4 in Ho.
    destruct Ho as [<-|[<-|[<-|[<-|[]]]]]; unfold O_bdM, O_stcM, O_alloc, O_mtM2, carved in Hr; rewrite obj_range_mk in Hr by (unfold STORE; lia); cbn [fst snd] in Hr;
      rewrite ?EVM in Hr; [lia | lia | cbn [eval] in Hr; rewrite u64_lit in Hr by lia; lia | lia]. }
  assert (VA : forall z, ~ (STORE + 8 <= z < STORE + 16) -> ~ (STORE + 16 + 16 * Z.of_nat b <= z < STORE + 32 + 16 * Z.of_nat b) -> view segsA (rm rhoA) z = view segsA (rm rhoL) z).
  { intros z H1 H2. destruct (Z_lt_le_dec z 0) as [Zn|Z0]; [unfold view; destruct (Z.leb_spec 0 z); [lia|reflexivity]|].
    destruct (Z_lt_le_dec z (2 ^ 64)) as [Z1|Z2]; [|unfold view; destruct (Z.ltb_spec z (2 ^ 64)); [lia|]; rewrite andb_false_r; reflexivity].
    rewrite !view_in by lia. unfold rd_of. rewrite VOUTA; [reflexivity | rewrite u64_lit by lia; exact H1 | rewrite u64_lit by lia; exact H2]. }

  assert (Cdat : cellZ (view segsA (rm rhoA)) (STORE + 16 + 16 * Z.of_nat b) 8 (bv_unsigned a)).
  { intros jj Hjj. cbn [c_addr c_w RtCells.c_val] in Hjj |- *. rewrite Ea.
    replace (STORE + 16 + 16 * Z.of_nat b + Z.of_nat jj) with (STORE + 16 * Z.of_nat b + 16 + Z.of_nat jj) by lia.
    rewrite (Cd 16 8%nat (SVar NXD) jj ltac:(left; reflexivity) Hjj). cbn [eval]. unfold rhoA. cbn [rw rho_absorb]. rewrite E210. reflexivity. }
  assert (Cmtx : cellZ (view segsA (rm rhoA)) (STORE + 28 + 16 * Z.of_nat b) 4 0).
  { intros jj Hjj. cbn [c_addr c_w RtCells.c_val] in Hjj |- *. rewrite (enc_zero_nth 4) by lia.
    destruct jj as [|jj'].
    - replace (STORE + 28 + 16 * Z.of_nat b + Z.of_nat 0) with (STORE + 16 * Z.of_nat b + 28 + Z.of_nat 0) by lia.
      rewrite (Cm 28 1%nat (SLit 0) 0%nat ltac:(cbn; tauto) ltac:(lia)). cbn [eval]. rewrite (enc_zero_nth 1) by lia. reflexivity.
    - replace (STORE + 28 + 16 * Z.of_nat b + Z.of_nat (Datatypes.S jj')) with (STORE + 16 * Z.of_nat b + 29 + Z.of_nat jj') by lia.
      rewrite (Cm 29 3%nat (SLit 0) jj' ltac:(cbn; tauto) ltac:(lia)). cbn [eval]. rewrite (enc_zero_nth 3) by lia. reflexivity. }
  assert (HM1 : depot_mem G1 (view segsA (rm rhoA))).
  { unfold G1. apply (depot_mem_fblk G (view segsA (rm rhoL)) (view segsA (rm rhoA)) (bv_unsigned a) S sz HM ltac:(lia) HHS HbL).
    - exact Pal. - exact Plo. - clear - Phi ACV; lia. - exact Pdj.
    - exact Cdat.
    - intros z Hz. apply Ps. lia.
    - exact Cmtx.
    - intros z Hz. apply Pa. lia.
    - intros z Hz H1 H2. apply VA; [exact H1 | exact H2].
    - intros [b0 n0] z Hbn0 Hz. cbn [fst snd] in Hz. pose proof (depot_inv_bounds segsA G rhoL md tp (conj HM HV)) as (_ & _ & BB & _). destruct (BB _ Hbn0) as (B1 & _ & _). cbn [fst] in B1.
      apply VA; unfold STORE, IMG_HI, NFBLK in *; lia. }
  assert (HV1 : depot_vm G1 md tp) by (unfold G1; apply (depot_vm_fblk G md tp a HV HL); [exact HPD | exact (HKT _ _ _ _ _ HK)]).
  assert (INW : forall z, (STORE + 8 <= z < STORE + 16) \/ (STORE + 16 + 16 * Z.of_nat b <= z < STORE + 32 + 16 * Z.of_nat b) -> DFPw G1 z).
  { intros z Hz. left. unfold dfp_static, DEPOT, MAP1, MAP1N, STORE, NFBLK in *. lia. }
  assert (HK1 : K G1 rhoA tp tr md).
  { eapply (kd_view segsA K NPRE HKD G1 rhoL rhoA); [intros i; reflexivity | intros l; reflexivity | | exact HK].
    intros z Hz. apply VA; intros Hin; apply Hz; apply INW; tauto. }
  destruct HREL as (R1 & R2 & R3).
  assert (HREL1 : REL G1 rhoA).
  { split; [exact R1 | split].
    - intros x Hx. rewrite VOUTA; [apply R2; exact Hx | |]; intros Hin; apply Hx; apply DFPw_DFP; apply INW; tauto.
    - intros z Hz. rewrite VA; [apply R3; exact Hz | |]; intros Hin; apply Hz; apply INW; tauto. }
  destruct (kd_room segsA K NPRE HKD G1 rhoA tp _ _ HK1 (conj HM1 HV1)) as [Hroom HDN]. cbn [cfg_model w_cfg fst snd] in Hroom. unfold G1, G_fblk in HDN. cbn [dN] in HDN.
  assert (HroomPG : headroom md tp >= PG) by (unfold droom in Hroom; destruct ((dN G1 + 1) mod 65536 =? 0); unfold NBSZ, PG in *; lia).
  assert (NNA : bv_unsigned (eval rhoL nn_addr) = blkN + 16 * ((dN G + 1) mod 65536)).
  { rewrite (nn_addr_val rhoL (dN G)); [rewrite H178; reflexivity | exact K177 | unfold DNMAX in HDN; lia | rewrite H178; exact NBhi]. }
  assert (SNA : bv_unsigned (eval rhoL slotN_addr) = MAP1 + 8 * ((dN G + 1) / 65536)) by (apply slotN_addr_val; [exact K177 | unfold DNMAX in HDN; lia]).
  assert (HjNz : 0 <= (dN G + 1) / 65536 < 2 ^ 15) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; unfold DNMAX in HDN; lia]).

  set (A1 := ax_setS C3r (set_objs (ax_S C3r) P3)) in HwA.
  pose proof (proj1 (proj1 HwA)) as HsmA1. unfold virt in HsmA1. cbn [fst snd cfg_ms cfg_model w_tr w_cfg] in HsmA1.
  assert (Hal : bv_unsigned a mod page_size = 0) by (change page_size with PG; exact Pal).
  assert (Hlz : page_in_ranges a (m_vm_lazy md) = true).
  { apply (proj2 (page_in_ranges_spec a _)). exists (a, Z_to_bv 64 FBSZ). split; [exact Pl|].
    apply (proj2 (page_in_range_spec a _)). cbn [fst snd]. rewrite FBSZ_lit. change page_size with PG. unfold PG, FBSZ. lia. }
  assert (Hnin : ~ In a tp).
  { intros Hin. pose proof (Ptp a Hin) as X.
    assert (Y : page_in_ranges a [(a, Z_to_bv 64 FBSZ)] = true).
    { apply (proj2 (page_in_ranges_spec a _)). exists (a, Z_to_bv 64 FBSZ). split; [left; reflexivity|].
      apply (proj2 (page_in_range_spec a _)). cbn [fst snd]. rewrite FBSZ_lit. change page_size with PG. unfold PG, FBSZ. lia. }
    rewrite Y in X. discriminate X. }
  assert (Hacc : forall j, 0 <= j < page_size -> covered (vm_noaccess (m_vmmaps md)) (bv_unsigned a + j) = false).
  { intros j Hjj. apply Pna. change page_size with 4096 in Hjj. unfold FBSZ. lia. }
  assert (HroomPS : headroom md tp >= page_size) by (change page_size with PG; exact HroomPG).
  assert (HdisjP : Forall (fun o => ranges_disjoint (obj_range rhoA o) (bv_unsigned a, bv_unsigned a + page_size)) (ss_objs (ax_S A1))).
  { unfold A1. cbn [ax_S ax_setS set_objs ss_objs]. unfold A1 in HsmA1. cbn [ax_S ax_setS set_objs] in HsmA1.
    assert (HFDA : Forall (holds rhoA) F_D).
    { pose proof (SPA_facts segsA _ _ _ _ _ HwA) as HFallA. cbn [ax_S ax_setS set_objs ss_facts] in HFallA. pose proof (holds_inclb rhoA _ _ C3_F HFallA) as X. apply Forall_app in X as [X _]. exact X. }
    change page_size with 4096.
    eapply (objs_ranges_ext rhoA _ _ _ [O_tw vW; O_nid vN; O_slotN vNB; O_nn; O_tf vF] _ _ HsmA1 ltac:(intros o Ho; exact Ho) C3_skel HFDA ltac:(first [assumption | eapply TOPr_of_REL; eassumption | eapply TOPr_of_JJ; eassumption])); [unfold STORE, IMG_HI in *; lia | unfold FBSZ in *; lia | lia |].
    unfold O_tw, O_nid, O_slotN, O_nn, O_tf, carved, ranges_disjoint. unfold rhoA.
    apply Forall_cons. { rewrite obj_range_mk by lia. cbn [fst snd]. rewrite eval_absorb. cbn [eval vP].
      pose proof (proj1 (Forall_forall _ _) HFt (SPUle vP (SLit (DEPOT + 4 * 2^20 - 4))) ltac:(unfold F_tw; cbn; tauto)) as X2. cbn [holds eval vP] in X2. unfold DEPOT in X2. rewrite u64_lit in X2 by lia.
      unfold DEPOT, IMG_HI in *. lia. }
    apply Forall_cons. { rewrite obj_range_mk by (unfold NIDS; lia). cbn [fst snd]. rewrite eval_absorb. cbn [eval]. rewrite u64_lit by lia. unfold NIDS, IMG_HI in *. lia. }
    apply Forall_cons. { rewrite obj_range_mk by lia. cbn [fst snd]. rewrite eval_absorb, SNA. unfold MAP1, IMG_HI in *. lia. }
    apply Forall_cons. { rewrite obj_range_mk by lia. cbn [fst snd]. rewrite eval_absorb, NNA. unfold NBSZ, FBSZ in *. lia. }
    apply Forall_cons. { rewrite obj_range_mk by (unfold STORE; lia). cbn [fst snd]. rewrite eval_absorb. cbn [eval]. rewrite u64_lit by (unfold STORE; lia). unfold STORE, IMG_HI in *. lia. }
    apply Forall_nil. }
  pose proof (SPA_prepay_zero segsA (fun _ _ _ _ => True) rhoA A1 a tp tr ms md HwA Hal Hlz Hnin Hacc HroomPS HdisjP (fun _ => I)) as HwC.

  set (A2 := ax_setS A1 (set_objs (ax_S A1) (ss_objs (ax_S A1) ++ [zero_page_obj a]))) in HwC.
  pose proof (SPA_unobj segsA (fun _ _ _ _ => True) rhoA A2 (ss_objs (ax_S A1)) [zero_page_obj a] (a :: tp) tr ms md eq_refl HwC (fun _ => I)) as HwD.
  cbn zeta in HwD. set (rhoB := rho_absorb rhoA [zero_page_obj a] (vms md (a :: tp) ms)) in *.
  change (ax_setS A2 (set_objs (ax_S A2) (ss_objs (ax_S A1)))) with A1 in HwD.
  pose proof (proj1 (proj1 HwC)) as HsmC. unfold virt in HsmC. cbn [fst snd cfg_ms cfg_model w_tr w_cfg] in HsmC.
  assert (HoC : ss_objs (ax_S A2) = ss_objs (ax_S A1) ++ [zero_page_obj a]) by reflexivity.
  assert (ZP : forall z, bv_unsigned a <= z < bv_unsigned a + PG -> view segsA (rm rhoB) z = Some (Z_to_bv 8 0)).
  { intros z Hzp. unfold rhoB, zero_page_obj.
    pose proof (urange a) as URa.
    apply (absorb_view_dzero segsA rhoA (ax_S A2) tr (vms md (a :: tp) ms) (vmd md) (ss_objs (ax_S A1)) _ (SLit (bv_unsigned a)) 0 page_size HsmC HoC);
      cbn [eval]; rewrite ?u64_lit by (clear - URa; lia); change page_size with 4096; try (clear - URa; lia).
    1: left; reflexivity. all: first [ clear - Hzp; unfold PG; lia | unfold PG, FBSZ, IMG_HI in *; lia ]. }
  assert (VOUTB : forall x : word, ~ (bv_unsigned a <= bv_unsigned x < bv_unsigned a + PG) -> rm rhoB x = rm rhoA x).
  { intros x Hx. unfold rhoB. apply rm_absorb_out. intros (o & [<-|[]] & Hr). apply Hx. unfold zero_page_obj in Hr.
    rewrite obj_range_mk in Hr by (change page_size with 4096; lia). cbn [fst snd eval] in Hr. rewrite u64_lit in Hr by lia. change page_size with 4096 in Hr. unfold PG. lia. }
  assert (VB : forall z, ~ (bv_unsigned a <= z < bv_unsigned a + PG) -> view segsA (rm rhoB) z = view segsA (rm rhoA) z).
  { intros z Hz. unfold view. destruct ((0 <=? z) && (z <? 2 ^ 64))%bool eqn:E; [|reflexivity]. unfold rd_of. rewrite VOUTB; [reflexivity|].
    apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2. rewrite u64_lit by lia. exact Hz. }

  assert (Hbl1 : (b < length (dFB G1))%nat) by (unfold G1, G_fblk; cbn [dFB]; rewrite length_app; cbn [length]; lia).
  assert (Efb : nth b (dFB G1) 0 = bv_unsigned a) by (unfold G1, G_fblk; cbn [dFB]; rewrite app_nth2 by lia; unfold b; rewrite Nat.sub_diag; reflexivity).
  assert (Efp : nth b (dFP G1) 0 = 0) by (unfold G1, G_fblk; cbn [dFP]; rewrite app_nth2 by lia; unfold b; rewrite HL, Nat.sub_diag; reflexivity).
  assert (Epg : fpage G1 b (nth b (dFP G1) 0) = bv_unsigned a) by (unfold fpage; rewrite Efb, Efp; lia).
  assert (PGin : forall z, bv_unsigned a <= z < bv_unsigned a + PG -> DFPw G2 z).
  { intros z Hz. right. right. exists (bv_unsigned a). split; [unfold G2, G1, G_page, G_fblk; cbn [dFB]; apply in_or_app; right; left; reflexivity | unfold PG, FBSZ in *; lia]. }
  assert (HK2 : K G2 rhoB (a :: tp) tr md).
  { assert (HK1' : K G2 rhoA (a :: tp) tr md).
    { eapply (kd_trans segsA K NPRE HKD G1 tp md G2 (a :: tp) md rhoA tr); [|exact HK1].
      apply (DT_page G1 tp md b a Hbl1); [rewrite Efp; unfold FBPAGES; lia | rewrite Epg; symmetry; exact Ea | exact Hnin | exact HroomPG]. }
    eapply (kd_view segsA K NPRE HKD G2 rhoA rhoB); [intros i; reflexivity | intros l; reflexivity | | exact HK1'].
    intros z Hz. apply VB. intros Hin. exact (Hz (PGin z Hin)). }
  assert (HM2 : depot_mem G2 (view segsA (rm rhoB))).
  { unfold G2. apply (depot_mem_page G1 (view segsA (rm rhoA)) (view segsA (rm rhoB)) b HM1 Hbl1); rewrite ?Epg; rewrite ?Efp.
    - unfold FBPAGES. lia.
    - unfold G1, G_fblk. cbn [dF]. unfold PG. lia.
    - exact ZP.
    - exact VB. }
  assert (HV2 : depot_vm G2 md (a :: tp)).
  { unfold G2. apply (depot_vm_page G1 (view segsA (rm rhoA)) md tp b a HM1 HV1 Hbl1); [rewrite Efp; unfold FBPAGES; lia | rewrite Epg; symmetry; exact Ea]. }
  assert (HREL2 : REL G2 rhoB).
  { destruct HREL1 as (Q1 & Q2 & Q3). split; [exact Q1 | split].
    - intros x Hx. rewrite VOUTB; [apply Q2; intros HD; apply Hx; unfold G2; exact HD|]. intros Hin. apply Hx. apply DFPw_DFP. exact (PGin _ Hin).
    - intros z Hz. rewrite VB; [apply Q3; intros HD; apply Hz; unfold G2; exact HD|]. intros Hin. exact (Hz (PGin z Hin)). }
  assert (HwE : SPA segsA (JJ G2) A1 rhoB (a :: tp) (tr, mkCfg ms md)).
  { split; [exact (proj1 HwD)|]. split; [exact HREL2|]. split; [exact HK2|]. split; [split; [exact HM2 | exact HV2] | exact I]. }

  assert (EVB : forall e, eval rhoB e = eval rhoL e) by (intros e; unfold rhoB, rhoA; rewrite !eval_absorb; reflexivity).
  assert (FRN : bv_unsigned (eval rhoB (add (SVar NXD) (SAlu ALU_SRL (SAlu ALU_SLL vF (SLit 44)) (SLit 41)))) = bv_unsigned a + 8 * (S mod 1048576)).
  { rewrite EVB. unfold add, vF. cbn [eval]. rewrite add_val, srl_val, sll_val, E210, H179.
    change (44 mod 64) with 44. change (41 mod 64) with 41. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. rewrite (shl44_shr41 S) by lia.
    change (2 ^ 20) with 1048576. rewrite Z.mod_small by (unfold FBSZ in *; lia). reflexivity. }
  assert (CIVd2 : cells_in_view rhoB (rd_of segsA (rm rhoB)) (STORE + 16 * Z.of_nat b) [(16, 8%nat, SVar NXD)]).
  { unfold cells_in_view. constructor; [|constructor]. intros jj Hjj. cbn beta iota.
    pose proof (Cd 16 8%nat (SVar NXD) jj ltac:(left; reflexivity) Hjj) as X. rewrite view_in in X by (unfold STORE, NFBLK in *; lia).
    rewrite EVB. unfold rd_of in X |- *. rewrite VOUTB; [exact X|]. rewrite u64_lit by (unfold STORE, NFBLK in *; lia). unfold STORE, IMG_HI, NFBLK in *. lia. }
  assert (CIVs2 : cells_in_view rhoB (rd_of segsA (rm rhoB)) (STORE + 16 * Z.of_nat b) [(24, 4%nat, vSt)]).
  { unfold cells_in_view. constructor; [|constructor]. intros jj Hjj. cbn beta iota.
    pose proof (Cs 24 4%nat vSt jj ltac:(left; reflexivity) Hjj) as X. rewrite view_in in X by (unfold STORE, NFBLK in *; lia).
    rewrite EVB. unfold rd_of in X |- *. rewrite VOUTB; [exact X|]. rewrite u64_lit by (unfold STORE, NFBLK in *; lia). unfold STORE, IMG_HI, NFBLK in *. lia. }
  assert (HwF : SPA segsA (JJ G2) (ax_setS A1 S_C3b) rhoB (a :: tp) (tr, mkCfg ms md)).
  { unfold S_C3b, O_bd, O_frN, O_stc.
    pose proof (proj1 HwE) as HsmE. unfold smatchA, virt in HsmE. cbn [fst snd cfg_ms cfg_model w_tr w_cfg] in HsmE. apply proj1 in HsmE. unfold A1 in HsmE. cbn [ax_S ax_setS set_objs] in HsmE.
    assert (HFDB : Forall (holds rhoB) F_D).
    { pose proof (SPA_facts segsA _ _ _ _ _ HwE) as HFallB. unfold A1 in HFallB. cbn [ax_S ax_setS set_objs ss_facts] in HFallB. pose proof (holds_inclb rhoB _ _ C3_F HFallB) as X. apply Forall_app in X as [X _]. exact X. }
    assert (EXD : forall lo hi, (STORE + 8 <= lo /\ hi <= DEPOT) \/ (bv_unsigned a <= lo /\ hi <= bv_unsigned a + FBSZ) -> lo <= hi ->
              Forall (fun o' => ranges_disjoint (obj_range rhoB o') (lo, hi)) P3).
    { intros lo hi Hlh Hle.
      eapply (objs_ranges_ext rhoB _ _ _ [O_tw vW; O_nid vN; O_slotN vNB; O_nn; O_tf vF] _ _ HsmE ltac:(intros o Ho; exact Ho) C3_skel HFDB ltac:(first [assumption | eapply TOPr_of_REL; eassumption | eapply TOPr_of_JJ; eassumption]));
        [unfold STORE, DEPOT, IMG_HI in *; lia | unfold STORE, DEPOT, IMG_HI, FBSZ in *; lia | exact Hle |].
      unfold O_tw, O_nid, O_slotN, O_nn, O_tf, carved, ranges_disjoint.
      apply Forall_cons. { rewrite obj_range_mk by lia. cbn [fst snd]. rewrite EVB. cbn [eval vP].
        pose proof (proj1 (Forall_forall _ _) HFt (SPUle vP (SLit (DEPOT + 4 * 2^20 - 4))) ltac:(unfold F_tw; cbn; tauto)) as X2. cbn [holds eval vP] in X2. unfold DEPOT in X2. rewrite u64_lit in X2 by lia.
        pose proof (proj1 (Forall_forall _ _) HFt (SPUle (SLit DEPOT) vP) ltac:(unfold F_tw; cbn; tauto)) as X3. cbn [holds eval vP] in X3. unfold DEPOT in X3. rewrite u64_lit in X3 by lia.
        unfold STORE, DEPOT, IMG_HI, FBSZ in *. lia. }
      apply Forall_cons. { rewrite obj_range_mk by (unfold NIDS; lia). cbn [fst snd]. rewrite EVB. cbn [eval]. rewrite u64_lit by lia. unfold NIDS, STORE, DEPOT, IMG_HI, FBSZ in *. lia. }
      apply Forall_cons. { rewrite obj_range_mk by lia. cbn [fst snd]. rewrite EVB, SNA. unfold MAP1, STORE, DEPOT, IMG_HI, FBSZ in *. lia. }
      apply Forall_cons. { rewrite obj_range_mk by lia. cbn [fst snd]. rewrite EVB, NNA. unfold NBSZ, STORE, DEPOT, IMG_HI, FBSZ in *. lia. }
      apply Forall_cons. { rewrite obj_range_mk by (unfold STORE; lia). cbn [fst snd]. rewrite EVB. cbn [eval]. rewrite u64_lit by (unfold STORE; lia). unfold STORE, DEPOT, IMG_HI, FBSZ in *. lia. }
      apply Forall_nil. }
    apply (SPA_carve_list segsA (JJ G2) rhoB A1 (a :: tp) _
             [(bd_addr, 16, 24, [(16, 8%nat, SVar NXD)]); (add (SVar NXD) (SAlu ALU_SRL (SAlu ALU_SLL vF (SLit 44)) (SLit 41)), 0, 8 * (sz + 1), []); (stc_addr, 24, 28, [(24, 4%nat, vSt)])]
             (ss_next (ax_S C3r)) HwE C3b_swf ltac:(apply Pos.le_refl)).
    - unfold IMG_HI, NBSZ, FBSZ, FBPAGES, PG, NFBLK in *.
      apply Forall_cons. { rewrite EVB, BDA. unfold STORE in *. repeat (split; [lia|]). split; [unfold cells_inside; constructor; [cbn; lia | constructor]|]. split; [|split; [exact CIVd2 | unfold xwords_clear, A1; cbn [ax_X ax_setS]; rewrite C3_X; intros rr y jj []]].
        intros off Hoff. split; [apply wok_of_imageA; lia | apply rd_of_imageA; lia]. }
      apply Forall_cons. { rewrite FRN. repeat (split; [lia|]). split; [unfold cells_inside; constructor|]. split; [|split; [constructor | unfold xwords_clear, A1; cbn [ax_X ax_setS]; rewrite C3_X; intros rr y jj []]].
        intros off Hoff. pose proof (ZP (bv_unsigned a + 8 * (S mod 1048576) + off) ltac:(lia)) as Hx. rewrite view_in in Hx by lia. eapply wok_rd_off_image; [lia | exact Hx]. }
      apply Forall_cons. { rewrite EVB, STA. unfold STORE in *. repeat (split; [lia|]). split; [unfold cells_inside; constructor; [cbn; lia | constructor]|]. split; [|split; [exact CIVs2 | unfold xwords_clear, A1; cbn [ax_X ax_setS]; rewrite C3_X; intros rr y jj []]].
        intros off Hoff. split; [apply wok_of_imageA; lia | apply rd_of_imageA; lia]. }
      apply Forall_nil.
    - unfold A1. cbn [ax_S ax_setS set_objs ss_objs map carve_obj]. unfold carved. unfold IMG_HI, NBSZ, FBSZ, FBPAGES, PG, NFBLK in *.
      apply Forall_cons. { rewrite obj_range_mk by lia. rewrite EVB, BDA. apply EXD; unfold STORE, DEPOT in *; lia. }
      apply Forall_cons. { rewrite obj_range_mk by lia. rewrite FRN. apply EXD; lia. }
      apply Forall_cons. { rewrite obj_range_mk by lia. rewrite EVB, STA. apply EXD; unfold STORE, DEPOT in *; lia. }
      apply Forall_nil.
    - assert (FRNL : bv_unsigned (eval rhoL (add (SVar NXD) (SAlu ALU_SRL (SAlu ALU_SLL vF (SLit 44)) (SLit 41)))) = bv_unsigned a + 8 * (S mod 1048576)) by (rewrite <- EVB; exact FRN).
      cbn [map carve_obj pairwise_disjoint]. unfold carved. unfold IMG_HI, NBSZ, FBSZ, FBPAGES, PG, NFBLK, STORE in *.
      repeat split; try exact I;
        repeat (apply Forall_cons; [unfold ranges_disjoint; rewrite !obj_range_mk by lia; cbn [fst snd]; rewrite !EVB; rewrite ?BDA, ?FRNL, ?STA; lia|]); apply Forall_nil. }
  unfold A1 in HwF. rewrite ax_setS_setS in HwF. change (ax_setS C3r S_C3b) with (mkC3j sz C3r) in HwF.

  exists (rho_sub rhoB sC3). split; [|split; [|split; [|split; [|symmetry; exact Hbn]]]].
  - apply (SPA_entails segsA (JJ G2) NPRE (mkC3j sz C3r) E2hs sC3 rhoB (a :: tp) _ ENT_C3 SID_C3 (JJ_stable G2 NPRE ltac:(lia))). exact HwF.
  -
    set (rho5 := rho_sub rhoB sC3).
    assert (HV6 : forall i, In i [170; 171; 177; 178; 179; 181]%positive -> rw rho5 i = rw rhoL i).
    { intros i Hi. unfold rho5. rewrite (ids6f_rw sC3 rhoB i IDS_C3 Hi). reflexivity. }
    assert (E180 : rw rho5 180%positive = a) by (unfold rho5; cbn [rw rho_sub]; rewrite SC3_180; cbn [eval]; exact E210).
    assert (K177' : bv_unsigned (rw rho5 177%positive) = dN G) by (rewrite (HV6 177%positive ltac:(cbn; tauto)); exact K177).
    assert (K179' : bv_unsigned (rw rho5 179%positive) = S) by (rewrite (HV6 179%positive ltac:(cbn; tauto)); exact H179).
    assert (K178' : bv_unsigned (rw rho5 178%positive) = blkN) by (rewrite (HV6 178%positive ltac:(cbn; tauto)); exact H178).
    assert (SNA5 : bv_unsigned (eval rho5 slotN_addr) = MAP1 + 8 * ((dN G + 1) / 65536)) by (apply slotN_addr_val; [exact K177' | unfold DNMAX in HDN; lia]).
    assert (NNA5 : bv_unsigned (eval rho5 nn_addr) = blkN + 16 * ((dN G + 1) mod 65536)).
    { rewrite (nn_addr_val rho5 (dN G)); [rewrite K178'; reflexivity | exact K177' | unfold DNMAX in HDN; lia | rewrite K178'; exact NBhi]. }
    assert (BDA5 : bv_unsigned (eval rho5 bd_addr) = STORE + 16 * Z.of_nat b) by (rewrite HbL; apply bd_addr_val; [exact K179' | lia]).
    assert (STA5 : bv_unsigned (eval rho5 stc_addr) = STORE + 16 * Z.of_nat b) by (rewrite HbL; apply stc_addr_val; [exact K179' | lia]).
    assert (FRA5 : bv_unsigned (eval rho5 fr_addr) = bv_unsigned a + 8 * (S mod 1048576)).
    { rewrite (fr_addr_val rho5 S K179'); [rewrite E180; reflexivity | lia | rewrite E180; clear - Phi ACV; lia]. }
    assert (TWR : obj_range rho5 (O_tw vW) = obj_range rhoL (O_tw vW)).
    { apply (obj_range_agree_vars (fun i => existsb (Pos.eqb i) [170; 171; 177; 178; 179; 181]%positive) rhoL rho5); [| intros l; reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc].
      intros v Hv. symmetry. apply HV6. apply existsb_exists in Hv as (x & Hx & Ex). apply Pos.eqb_eq in Ex. subst. exact Hx. }
    assert (DFPm : forall z, DFP G z -> DFP G2 z).
    { intros z [X|[X|[b0 [Hb0 X]]]]; [left; exact X | right; left; exact X | right; right; exists b0; split; [unfold G2, G1, G_page, G_fblk; cbn [dFB]; apply in_or_app; left; exact Hb0 | exact X]]. }
    split; [|split; [|split; [exact K179' | split; [|split; [|split; [|split]]]]]].
    + split; [exact K177'|]. split; [rewrite (HV6 170%positive ltac:(cbn; tauto)); exact KW0|]. split.
      * intros x Hx. apply DFPm. apply KD1. rewrite <- TWR. exact Hx.
      * intros x. unfold O_nid, carved. rewrite obj_range_mk by (unfold NIDS; lia). cbn [fst snd eval]. rewrite u64_lit by (unfold NIDS; lia). intros Hx. left. left. unfold NIDS, DEPOT, MAP1, MAP1N in *. lia.
    + unfold G2, G1, G_page, G_fblk. cbn [dN dNB]. exact K178'.
    + rewrite E180. unfold G2, G1, G_page, G_fblk. cbn [dFB]. rewrite app_nth2 by lia. unfold b. rewrite Nat.sub_diag. reflexivity.
    + pose proof OWV4 as W. cbn [forallb] in W. apply andb_prop in W as [_ W]. apply andb_prop in W as [_ W]. apply andb_prop in W as [W3 _].
      eapply (ro_win_vars segsA (fun i => existsb (Pos.eqb i) [170; 171; 177; 178]%positive) rhoB rho5); [| intros l; reflexivity | intros x; reflexivity | exact W3 |].
      { intros v Hv. unfold rho5. symmetry. rewrite (ids6f_rw sC3 rhoB v IDS_C3); [reflexivity|]. apply existsb_exists in Hv as (x & Hx & Ex). apply Pos.eqb_eq in Ex. subst. cbn in Hx |- *. tauto. }
      unfold rhoB. apply ro_win_absorb.
      * unfold rhoA. apply ro_win_absorb; [exact HROs|]. intros x Hx. apply VOUTA; intros Hin; unfold O_slotN, carved in Hx; rewrite obj_range_mk in Hx by lia; cbn [fst snd] in Hx; rewrite SNA in Hx; unfold MAP1, STORE, NFBLK in *; lia.
      * intros x Hx. apply VOUTB. unfold O_slotN, carved in Hx. rewrite obj_range_mk in Hx by lia. cbn [fst snd] in Hx. unfold rhoA in Hx. rewrite eval_absorb, SNA in Hx. unfold MAP1, IMG_HI in *. lia.
    + exists bd_addr, 16, 8%nat, vD. rewrite BDA5. split; [reflexivity|]. unfold STORE in *. repeat (split; [lia|]).
      unfold cells_in_view. constructor; [|constructor]. intros jj Hjj. cbn beta iota.
      pose proof (proj1 (Forall_forall _ _) CIVd2 _ ltac:(left; reflexivity)) as X. cbn beta iota in X. specialize (X jj Hjj).
      replace (eval rho5 vD) with (eval rhoB (SVar NXD)); [exact X|]. unfold vD, rho5. cbn [eval rw rho_sub]. rewrite SC3_180. reflexivity.
    + unfold winDFP, O_slotN, O_nn, O_tf, O_bd, O_stc, carved.
      apply Forall_cons. { intros x. rewrite obj_range_mk by lia. cbn [fst snd]. rewrite SNA5. intros Hx. left. left. unfold MAP1, MAP1N, DEPOT in *. lia. }
      apply Forall_cons. { intros x. rewrite obj_range_mk by lia. cbn [fst snd]. rewrite NNA5. intros Hx. right. left. exists blkN. split; [exact HinN | unfold NBSZ in *; lia]. }
      apply Forall_cons. { intros x. unfold STORE. rewrite obj_range_mk by lia. cbn [fst snd eval]. rewrite u64_lit by lia. intros Hx. left. right. unfold SegD_wf.STORE, NFBLK. lia. }
      apply Forall_cons. { intros x. rewrite obj_range_mk by lia. cbn [fst snd]. rewrite BDA5. intros Hx. left. right. unfold STORE, NFBLK in *. lia. }
      apply Forall_cons. { intros x. rewrite obj_range_mk by lia. cbn [fst snd]. rewrite STA5. intros Hx. left. right. unfold STORE, NFBLK in *. lia. }
      apply Forall_nil.
    + intros x. rewrite FRA5. intros Hx. right. right. exists (bv_unsigned a).
      split; [unfold G2, G1, G_page, G_fblk; cbn [dFB]; apply in_or_app; right; left; reflexivity | unfold FBSZ in *; lia].
  - unfold arm_e, G2, G1, G_page, G_fblk. cbn [dFB dFP]. rewrite <- Hbn. unfold b. rewrite length_app. cbn [length].
    split; [lia|]. split; [exact Hns|]. rewrite <- HL. rewrite list_upd_app_last. rewrite !app_nth2 by lia. rewrite !Nat.sub_diag. cbn [nth Z.add]. unfold PG. lia.
  - destruct (gmid_fblk_page G tp (bv_unsigned a) HG Hbud HL) as [X _]. rewrite Ea in X. exact X.
Qed.

Lemma OW_c : ltac2:(tb__ "0|0|
S35S28S116S0S14S95A1S25S0Sb6S5Z0A1A1S25S0Sb7Sa0A1S25S0SacSb0A1S25S0Sb9S26S0A1A3A3A3A3A3S2aA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma cK_agree : ltac2:(tb__ "0|0|
S5cS3aS1S1SbS95R2R1A3S70R5R4R3A3S70R6R5R3A3F_;F_;Frho';Frho;FS;FG;").
Proof.
  intros G S rho rho' Hag (A & B & F). split; [exact (jK_agree G S rho rho' Hag A)|].
  pose proof Hag as (Hw & Hl & Hm). split; [rewrite <- (Hw 206%positive) by (unfold NXD; lia); exact B|].
  pose proof OW_c as W. cbn [forallb] in W. apply andb_prop in W as [W1 W]. apply andb_prop in W as [W2 W]. apply andb_prop in W as [W3 W]. apply andb_prop in W as [W4 _].
  pose proof (Forall_inv F) as F1. pose proof (Forall_inv (Forall_inv_tail F)) as F2. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail F))) as F3.
  pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail F)))) as F4.
  repeat apply Forall_cons; [| | | | apply Forall_nil]; (eapply winDFP_agree; [exact Hag | | ]); [exact W1 | exact F1 | exact W2 | exact F2 | exact W3 | exact F3 | exact W4 | exact F4].
Qed.

Lemma f_main : ltac2:(tb__ "0|1|
S5cS3aS27S4aQ40A1A1S1S65R4R2A2S3eS3dSf5R5A1S120A2S3dSf5VG0;A1Sf6VG0;A1A2A2S67R6R5R3A3S66R7R6A2S3fS3dS41R7Z100000M0A2Vsz;A2G0A2S38S119S42S40R8G0A2A1S2dS3aS5eR9A1A2A2A1S11dS3cVok;S4dS3cS63RaA1VJhs;R7R8A5S64A4F_;F_;F_;F_;F_;F_;Frho;Ftp;FS;FG;").
Proof.
  intros G S tp rho HG Hbud HJK HHS Hns Hnbl. pose proof HJK as (_ & Hj & _).
  eapply triple_conseq with (P := fun w => exists rho', fK G S rho' /\ SPA segsA (JJ G) (mkI5f sz Jhs) rho' tp w); [| intros w Hw; exact Hw |].
  { intros w Hw. destruct (glue_f2 G S tp rho w Hw HJK HHS Hnbl) as (rho' & S' & K'). exists rho'. split; [exact K' | exact S']. }
  apply triple_ex. intros rho1. apply triple_pure. intros HFK. apply triple1_triple.
  eapply (stage_run (JJ G)); [apply JJ_ok | apply JJ_stable; lia | exact RUNF1 | discriminate | exact J_len | apply Pos.leb_le; reflexivity |].
  intros L rhoL [<-|[]] Hag. cbn [la_state].
  eapply triple_conseq with (P := fun w => (1 <= dN G <= DNMAX) /\ exists rho2, cK G S rho2 /\ SPA segsA (JJ G) (mkC1 C1r) rho2 tp w); [| intros w Hw; exact Hw |].
  { intros w Hw. split.
    - destruct w as [tr [ms md]]. pose proof Hw as [_ [_ [HK [[HM HV] _]]]]. split; [exact (proj1 (proj1 (dm_N _ _ HM))) | exact (proj2 (kd_room segsA K NPRE HKD G rhoL tp _ _ HK (conj HM HV)))].
    - destruct (glue_c1 G S tp rho1 rhoL w Hw Hag HFK HHS Hnbl) as (rho2 & S2 & K2). exists rho2. split; [exact K2 | exact S2]. }
  apply triple_pure. intros HDN. apply triple_ex. intros rho2. apply triple_pure. intros HCK. apply triple1_triple.
  eapply (stage_run (JJ G)); [apply JJ_ok | apply JJ_stable; lia | exact RUNF2 | discriminate | exact C1_len | apply Pos.leb_le; reflexivity |].
  intros L2 rhoL2 [<-|[]] Hag2. cbn [la_state].
  pose proof (cK_agree G S rho2 rhoL2 Hag2 HCK) as HCK2.
  apply triple1_triple. eapply triple1_seq_l; [apply (mmap_step_f G S rhoL2 tp HCK2 HHS Hnbl)|].
  apply triple_disj; [apply fail_spin_f|].
  apply triple_ex. intros a.
  set (rho3 := rho_set_rw (set_rm rhoL2 (unmap_range (rm rhoL2) a (Z_to_bv 64 FBSZ))) (ss_next (ax_S EFr)) a).
  assert (E1 : rw rho3 NXD = a) by (unfold rho3; rewrite <- EF_nx; apply rho_set_rw_at).
  eapply triple_conseq with (P := fun w => (IMG_HI <= bv_unsigned a) /\ SPA segsA (JJ2 (G_fblk G (bv_unsigned a)) G (PDf G a)) (mkOKf EFr) rho3 tp w); [| intros w Hw; exact Hw |].
  { intros w Hw. destruct w as [tr [ms md]]. pose proof Hw as [_ [_ [_ [_ HPD]]]]. cbn [w_tr w_cfg fst snd cfg_model] in HPD. destruct HPD as (_ & _ & Pal & Plo & Phi & _).
    split; [exact Plo|].
    unfold mkOKf. apply SPA_refacts; [exact Hw | cbn [ax_S ax_setS S_after ss_next]; rewrite EF_nx; exact EF_fbO |].
    cbn [ax_S ax_setS S_after ss_facts]. intros HF0. apply Forall_app. split; [exact HF0|].
    pose proof alloc_ceiling_valD as ACV. pose proof (urange a) as Ra.
    unfold F_af. repeat apply Forall_cons; try apply Forall_nil; cbn [holds eval branch_taken]; rewrite ?E1.
    - change (2 ^ 12) with PG. split; [unfold PG; lia | exact Pal].
    - rewrite u64_lit by (unfold IMG_HI; lia). exact Plo.
    - rewrite u64_lit by (unfold FBSZ in *; lia). lia.
    - unfold bv_eqb. rewrite u64_lit by lia. intros X. apply Z.eqb_eq in X. unfold IMG_HI in Plo. lia.
    - rewrite u64_lit by lia. unfold FBSZ in Phi. lia. }
  apply triple_pure. intros Plo. apply triple1_triple.
  eapply (stage_run (JJ2 (G_fblk G (bv_unsigned a)) G (PDf G a)));
    [apply JJ2_ok | apply JJ2_stable; [apply PDf_stable | lia] | exact RUNF4 | discriminate | exact EF_len | |].
  { cbn [mkOKf ax_with_facts with_facts ax_S ax_setS S_after ss_next]. rewrite EF_nx. apply Pos.leb_le. reflexivity. }
  intros L4 rhoL4 [<-|[]] Hag4. cbn [la_state]. cbn [mkOKf ax_with_facts with_facts ax_S ax_setS S_after ss_next] in Hag4. rewrite EF_nx in Hag4.
  assert (HC3 : c3K G S a rhoL4).
  { apply (c3K_agree G S a rho3 rhoL4 Hag4). unfold rho3. apply (cK_after_grant G S rhoL2 a _ HCK2); [|exact HDN].
    intros x Hx. rewrite unmap_range_at. destruct (in_range a (Z_to_bv 64 FBSZ) x) eqn:E; [|reflexivity].
    exfalso. apply in_range_spec in E. rewrite FBSZ_lit in E. unfold IMG_HI in *. lia. }
  eapply triple_conseq with (P := fun w => exists rho5, (insK5 (G_page (G_fblk G (bv_unsigned a)) (length (dFB G))) (length (dFB G)) S rho5
      /\ arm_e (G_page (G_fblk G (bv_unsigned a)) (length (dFB G))) S /\ gmid (G_page (G_fblk G (bv_unsigned a)) (length (dFB G))) (a :: tp) /\ Z.to_nat (S / 1048576) = length (dFB G))
      /\ SPA segsA (JJ (G_page (G_fblk G (bv_unsigned a)) (length (dFB G)))) E2hs rho5 (a :: tp) w); [| intros w Hw; exact Hw |].
  { intros w Hw. destruct (glue_c3 G S a rhoL4 tp w Hw HC3 HHS Hnbl Hns HG Hbud) as (rho5 & S5 & K5 & A5 & M5 & B5). exists rho5. split; [|exact S5]. split; [exact K5 | split; [exact A5 | split; [exact M5 | exact B5]]]. }
  apply triple_ex. intros rho5. apply triple_pure. intros (K5 & A5 & M5 & B5).
  apply (e2_cont _ S (a :: tp) rho5 M5); [rewrite B5; exact K5 | exact HHS | exact Hj | exact A5].
Qed.

Lemma ef_main : ltac2:(tb__ "0|1|
S5cS3aS27S4aQ40A1A1S1S65R4R2A2S3eS3dSf5R5A1S120A2S3dSf5VG0;A1Sf6VG0;A1A2A2S67R6R5R3A3S66R7R6A2S3fS3dS41R7Z100000M0A2Vsz;A2G0A2S38S119S42S40R8G0A2A1S2dS3aS5eR9A1A2A2A1S11cS3cS4dS3cS63RaA1VJhs;R7R8A5S64A3F_;F_;F_;F_;F_;F_;Frho;Ftp;FS;FG;").
Proof.
  intros G S tp rho HG Hbud HJK HHS Hns Hnbl. pose proof HJK as (_ & Hj & _).
  eapply etriple_conseq with (P := fun w => exists rho', fK G S rho' /\ SPA segsA (JJ G) (mkI5f sz Jhs) rho' tp w); [| intros w Hw; exact Hw |].
  { intros w Hw. destruct (glue_f2 G S tp rho w Hw HJK HHS Hnbl) as (rho' & S' & K'). exists rho'. split; [exact K' | exact S']. }
  apply etriple_ex. intros rho1. apply etriple_pure. intros HFK.
  eapply (estage_run (JJ G)); [apply JJ_stable; lia | exact RUNF1 | discriminate | exact J_len | apply Pos.leb_le; reflexivity |].
  intros L rhoL [<-|[]] Hag. cbn [la_state].
  eapply etriple_conseq with (P := fun w => (1 <= dN G <= DNMAX) /\ exists rho2, cK G S rho2 /\ SPA segsA (JJ G) (mkC1 C1r) rho2 tp w); [| intros w Hw; exact Hw |].
  { intros w Hw. split.
    - destruct w as [tr [ms md]]. pose proof Hw as [_ [_ [HK [[HM HV] _]]]]. split; [exact (proj1 (proj1 (dm_N _ _ HM))) | exact (proj2 (kd_room segsA K NPRE HKD G rhoL tp _ _ HK (conj HM HV)))].
    - destruct (glue_c1 G S tp rho1 rhoL w Hw Hag HFK HHS Hnbl) as (rho2 & S2 & K2). exists rho2. split; [exact K2 | exact S2]. }
  apply etriple_pure. intros HDN. apply etriple_ex. intros rho2. apply etriple_pure. intros HCK.
  eapply (estage_run (JJ G)); [apply JJ_stable; lia | exact RUNF2 | discriminate | exact C1_len | apply Pos.leb_le; reflexivity |].
  intros L2 rhoL2 [<-|[]] Hag2. cbn [la_state].
  pose proof (cK_agree G S rho2 rhoL2 Hag2 HCK) as HCK2.
  eapply etriple_seq; [apply (emmap_step_f G S rhoL2 tp HCK2 HHS Hnbl)|].
  apply etriple_ex. intros a.
  set (rho3 := rho_set_rw (set_rm rhoL2 (unmap_range (rm rhoL2) a (Z_to_bv 64 FBSZ))) (ss_next (ax_S EFr)) a).
  assert (E1 : rw rho3 NXD = a) by (unfold rho3; rewrite <- EF_nx; apply rho_set_rw_at).
  eapply etriple_conseq with (P := fun w => (IMG_HI <= bv_unsigned a) /\ SPA segsA (JJ2 (G_fblk G (bv_unsigned a)) G (PDf G a)) (mkOKf EFr) rho3 tp w); [| intros w Hw; exact Hw |].
  { intros w Hw. destruct w as [tr [ms md]]. pose proof Hw as [_ [_ [_ [_ HPD]]]]. cbn [w_tr w_cfg fst snd cfg_model] in HPD. destruct HPD as (_ & _ & Pal & Plo & Phi & _).
    split; [exact Plo|].
    unfold mkOKf. apply SPA_refacts; [exact Hw | cbn [ax_S ax_setS S_after ss_next]; rewrite EF_nx; exact EF_fbO |].
    cbn [ax_S ax_setS S_after ss_facts]. intros HF0. apply Forall_app. split; [exact HF0|].
    pose proof alloc_ceiling_valD as ACV. pose proof (urange a) as Ra.
    unfold F_af. repeat apply Forall_cons; try apply Forall_nil; cbn [holds eval branch_taken]; rewrite ?E1.
    - change (2 ^ 12) with PG. split; [unfold PG; lia | exact Pal].
    - rewrite u64_lit by (unfold IMG_HI; lia). exact Plo.
    - rewrite u64_lit by (unfold FBSZ in *; lia). lia.
    - unfold bv_eqb. rewrite u64_lit by lia. intros X. apply Z.eqb_eq in X. unfold IMG_HI in Plo. lia.
    - rewrite u64_lit by lia. unfold FBSZ in Phi. lia. }
  apply etriple_pure. intros Plo.
  eapply (estage_run (JJ2 (G_fblk G (bv_unsigned a)) G (PDf G a)));
    [apply JJ2_stable; [apply PDf_stable | lia] | exact RUNF4 | discriminate | exact EF_len | |].
  { cbn [mkOKf ax_with_facts with_facts ax_S ax_setS S_after ss_next]. rewrite EF_nx. apply Pos.leb_le. reflexivity. }
  intros L4 rhoL4 [<-|[]] Hag4. cbn [la_state]. cbn [mkOKf ax_with_facts with_facts ax_S ax_setS S_after ss_next] in Hag4. rewrite EF_nx in Hag4.
  assert (HC3 : c3K G S a rhoL4).
  { apply (c3K_agree G S a rho3 rhoL4 Hag4). unfold rho3. apply (cK_after_grant G S rhoL2 a _ HCK2); [|exact HDN].
    intros x Hx. rewrite unmap_range_at. destruct (in_range a (Z_to_bv 64 FBSZ) x) eqn:E; [|reflexivity].
    exfalso. apply in_range_spec in E. rewrite FBSZ_lit in E. unfold IMG_HI in *. lia. }
  eapply etriple_conseq with (P := fun w => exists rho5, (insK5 (G_page (G_fblk G (bv_unsigned a)) (length (dFB G))) (length (dFB G)) S rho5
      /\ arm_e (G_page (G_fblk G (bv_unsigned a)) (length (dFB G))) S /\ gmid (G_page (G_fblk G (bv_unsigned a)) (length (dFB G))) (a :: tp) /\ Z.to_nat (S / 1048576) = length (dFB G))
      /\ SPA segsA (JJ (G_page (G_fblk G (bv_unsigned a)) (length (dFB G)))) E2hs rho5 (a :: tp) w); [| intros w Hw; exact Hw |].
  { intros w Hw. destruct (glue_c3 G S a rhoL4 tp w Hw HC3 HHS Hnbl Hns HG Hbud) as (rho5 & S5 & K5 & A5 & M5 & B5). exists rho5. split; [|exact S5]. split; [exact K5 | split; [exact A5 | split; [exact M5 | exact B5]]]. }
  apply etriple_ex. intros rho5. apply etriple_pure. intros (K5 & A5 & M5 & B5).
  apply (ee2_cont _ S (a :: tp) rho5 M5); [rewrite B5; exact K5 | exact HHS | exact Hj | exact A5].
Qed.

Lemma armsF_ok : armsF.
Proof. exact f_main. Qed.
Lemma earmsF_ok : earmsF.
Proof. exact ef_main. Qed.

Lemma droom_pg : ltac2:(tb__ "0|1|
S5cS3eS3dSf5R1A1M0S120A2S3dG0Sf6R1A1A2A2FG;").
Proof. intros G. unfold droom, PG, NBSZ. destruct ((dN G + 1) mod 65536 =? 0); lia. Qed.

Lemma i3_cont : ltac2:(tb__ "0|0|
S6fS1S69VG0;R1A2S11dS3cVok;S4dS3cS63VG0;A1VI3s;R2Vtp0;A5S64A4F_;Frho;F_;").
Proof.
  intros HNB rho HK. destruct (lt_dec (Z.to_nat ((dN G0 + 1) / 65536)) (length (dNB G0))) as [Hj|Hj]; [|exact (armB_main HNB rho HK Hj)].
  eapply triple_conseq with (P := fun w => exists rho', nbK G0 rho' /\ SPA segsA (JJ G0) (mkI4 I3s) rho' tp0 w).
  - intros w Hw. destruct (glue_nb rho w Hw HK Hj) as (rho' & S' & K' & E178 & RO & WD). exists rho'. split; [|exact S']. split; [exact K'|]. split; [exact Hj|]. split; [exact E178|]. split; assumption.
  - intros w Hw. exact Hw.
  - apply triple_ex. intros rho'. apply triple_pure. intros HNK. apply triple1_triple.
    eapply (stage_run (JJ G0)); [apply JJ_ok | apply JJ_stable; lia | exact RUNNB | discriminate | exact I3_len | apply Pos.leb_le; reflexivity |].
    intros L rhoL [<-|[]] Hag. cbn [la_state]. pose proof (nbK_agree G0 rho' rhoL Hag HNK) as HNK'.
    eapply triple_conseq with (P := fun w => exists rho'', nbK G0 rho'' /\ SPA segsA (JJ G0) NBs rho'' tp0 w); [| intros w Hw; exact Hw |].
    { intros w Hw. destruct (glue_h G0 tp0 rhoL w Hw HNK') as (rho'' & S'' & K''). exists rho''. split; [exact K'' | exact S'']. }
    apply triple_ex. intros rho''. apply triple_pure. intros HNK''.
    exact (frames_cont HNB G0 tp0 rho'' gmid_refl (droom_pg G0) HNK'').
Qed.

Lemma ei3_cont : ltac2:(tb__ "0|0|
S71S1S69VG0;R1A2S11cS3cS4dS3cS63VG0;A1VI3s;R2Vtp0;A5S64A3F_;Frho;F_;").
Proof.
  intros HNB rho HK. destruct (lt_dec (Z.to_nat ((dN G0 + 1) / 65536)) (length (dNB G0))) as [Hj|Hj]; [|exact (earmB_main HNB rho HK Hj)].
  eapply etriple_conseq with (P := fun w => exists rho', nbK G0 rho' /\ SPA segsA (JJ G0) (mkI4 I3s) rho' tp0 w).
  - intros w Hw. destruct (glue_nb rho w Hw HK Hj) as (rho' & S' & K' & E178 & RO & WD). exists rho'. split; [|exact S']. split; [exact K'|]. split; [exact Hj|]. split; [exact E178|]. split; assumption.
  - intros w Hw. exact Hw.
  - apply etriple_ex. intros rho'. apply etriple_pure. intros HNK.
    eapply (estage_run (JJ G0)); [apply JJ_stable; lia | exact RUNNB | discriminate | exact I3_len | apply Pos.leb_le; reflexivity |].
    intros L rhoL [<-|[]] Hag. cbn [la_state]. pose proof (nbK_agree G0 rho' rhoL Hag HNK) as HNK'.
    eapply etriple_conseq with (P := fun w => exists rho'', nbK G0 rho'' /\ SPA segsA (JJ G0) NBs rho'' tp0 w); [| intros w Hw; exact Hw |].
    { intros w Hw. destruct (glue_h G0 tp0 rhoL w Hw HNK') as (rho'' & S'' & K''). exists rho''. split; [exact K'' | exact S'']. }
    apply etriple_ex. intros rho''. apply etriple_pure. intros HNK''.
    exact (eframes_cont HNB G0 tp0 rho'' gmid_refl (droom_pg G0) HNK'').
Qed.

Lemma OW_tw : ltac2:(tb__ "0|0|
S35S28S14S95S97S96A1A2S2aA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma JJ_dN : ltac2:(tb__ "0|0|
S5cS55S1S27S4aQ40A1A1S11bS4dS3cS63R5A1R4R3R2R1A6S3eZ1S5dR6A1A2F_;Fw;Ftp;Frho;FA;FG;").
Proof. intros G A rho tp [tr [ms md]] H. pose proof H as [_ [_ [_ [[HM _] _]]]]. exact (proj1 (proj1 (dm_N _ _ HM))). Qed.

Theorem seg_D_core : ltac2:(tb__ "0|0|
S6fS11dS3cVok;S4dS3cS101S3cVK;VG0;A3Sb1Vsz;A1Vrho0;Vtp0;A5S64A4F_;").
Proof.
  intros HNB.
  eapply triple_conseq with (P := SPA segsA (JJ G0) (PreD sz) rho0 tp0); [| intros w Hw; exact Hw |].
  { intros w [Hsm [HK HD]]. split; [exact Hsm|]. split; [|split; [exact HK | split; [exact HD | exact I]]].
    split; [split; [intros; reflexivity | intros; reflexivity]|]. split; [intros; reflexivity | intros; reflexivity]. }
  apply stage_pre. intros rho1.
  eapply triple_conseq with (P := fun w => exists rho2, ((bv_unsigned (rw rho2 170%positive) = 0 \/ 1 <= bv_unsigned (rw rho2 170%positive) <= dN G0) /\ ro_win segsA rho2 (O_tw vW)) /\ SPA segsA (JJ G0) (mkT1 E1s) rho2 tp0 w).
  { intros w Hw. destruct (glue_T rho1 w Hw) as (rho2 & S & W & RO). exists rho2. split; [split; assumption | exact S]. }
  { intros w Hw; exact Hw. }
  apply triple_ex. intros rho2. apply triple_pure. intros [HW HRO]. apply triple1_triple.
  eapply (stage_run (JJ G0)); [apply JJ_ok | apply JJ_stable; lia | exact RUN2 | discriminate | reflexivity | apply Pos.leb_le; reflexivity |].
  intros L rho3 [<-|[]] Hag. cbn [la_state]. cbn [ss_next ax_S ax_setS upd mkT1] in Hag.
  assert (HW3 : bv_unsigned (rw rho3 170%positive) = 0 \/ 1 <= bv_unsigned (rw rho3 170%positive) <= dN G0) by (rewrite <- (proj1 Hag 170%positive) by (unfold NXD; lia); exact HW).
  assert (HRO3 : ro_win segsA rho3 (O_tw vW)) by (eapply ro_win_agree; [exact Hag | apply OW_tw | exact HRO]).
  eapply triple_conseq with (P := InvF); [| intros w Hw; exact Hw | apply find_loop].
  { intros w Hw. destruct (glue_F rho3 w Hw HW3 HRO3) as (rho4 & S & C & E170 & E171 & RO4). exists rho4. split; [|exact S].
    split; [exact C|]. split; [exact RO4|]. unfold W0ok. rewrite E170. pose proof (JJ_dN _ _ _ _ _ Hw). lia. }
  apply zero_branch. apply i3_cont. assumption.
Qed.

Theorem eseg_D_core : ltac2:(tb__ "0|0|
S71S11cS3cS4dS3cS101S3cVK;VG0;A3Sb1Vsz;A1Vrho0;Vtp0;A5S64A3F_;").
Proof.
  intros HNB.
  eapply etriple_conseq with (P := SPA segsA (JJ G0) (PreD sz) rho0 tp0); [| intros w Hw; exact Hw |].
  { intros w [Hsm [HK HD]]. split; [exact Hsm|]. split; [|split; [exact HK | split; [exact HD | exact I]]].
    split; [split; [intros; reflexivity | intros; reflexivity]|]. split; [intros; reflexivity | intros; reflexivity]. }
  apply estage_pre. intros rho1.
  eapply etriple_conseq with (P := fun w => exists rho2, ((bv_unsigned (rw rho2 170%positive) = 0 \/ 1 <= bv_unsigned (rw rho2 170%positive) <= dN G0) /\ ro_win segsA rho2 (O_tw vW)) /\ SPA segsA (JJ G0) (mkT1 E1s) rho2 tp0 w).
  { intros w Hw. destruct (glue_T rho1 w Hw) as (rho2 & S & W & RO). exists rho2. split; [split; assumption | exact S]. }
  { intros w Hw; exact Hw. }
  apply etriple_ex. intros rho2. apply etriple_pure. intros [HW HRO].
  eapply (estage_run (JJ G0)); [apply JJ_stable; lia | exact RUN2 | discriminate | reflexivity | apply Pos.leb_le; reflexivity |].
  intros L rho3 [<-|[]] Hag. cbn [la_state]. cbn [ss_next ax_S ax_setS upd mkT1] in Hag.
  assert (HW3 : bv_unsigned (rw rho3 170%positive) = 0 \/ 1 <= bv_unsigned (rw rho3 170%positive) <= dN G0) by (rewrite <- (proj1 Hag 170%positive) by (unfold NXD; lia); exact HW).
  assert (HRO3 : ro_win segsA rho3 (O_tw vW)) by (eapply ro_win_agree; [exact Hag | apply OW_tw | exact HRO]).
  eapply etriple_conseq with (P := fun w => exists a, InvFe a w); [| intros w Hw; exact Hw | apply etriple_ex; intros a; apply efind_loop].
  { intros w Hw. destruct (glue_F rho3 w Hw HW3 HRO3) as (rho4 & S & C & E170 & E171 & RO4).
    exists (Z.to_nat (bv_unsigned (rw rho4 175%positive))). exists rho4. split; [|exact S].
    split; [exact C|]. split; [exact RO4|]. split; [unfold W0ok; rewrite E170; pose proof (JJ_dN _ _ _ _ _ Hw); lia| reflexivity]. }
  apply ezero_branch. apply ei3_cont. assumption.
Qed.

Theorem seg_D_main : ltac2:(tb__ "0|0|
S11dS3cVok;S4dS3cS101S3cVK;VG0;A3Sb1Vsz;A1Vrho0;Vtp0;A5S64A4").
Proof. exact (seg_D_core armsF_ok). Qed.
Theorem eseg_D_main : ltac2:(tb__ "0|0|
S11cS3cS4dS3cS101S3cVK;VG0;A3Sb1Vsz;A1Vrho0;Vtp0;A5S64A3").
Proof. exact (eseg_D_core earmsF_ok). Qed.

End Skel.

