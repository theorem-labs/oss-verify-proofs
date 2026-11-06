(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "N"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "add"; "leb"; "mul"; "pow"; "opp"; "ltb"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sobj"; "valuation"; "sprop"; "rw"; "SLit"; "sstate"; "obj_range"; "sv_eqb"; "SVar"; "ss_next"; "ss_facts"; "SPUle"; "ob_base"; "ob_hi"; "ob_lo"; "holds"; "ss_objs"; "SAlu"; "soff"; "sprop_below"; "smatch"; "swf"; "SExt"; "@Corelib.Init.Logic"; "and"; "eq"; "or"; "ex"; "not"; "@Corelib.Init.Datatypes"; "bool"; "list"; "false"; "true"; "prod"; "cons"; "option"; "nat"; "nil"; "pair"; "andb"; "fst"; "snd"; "orb"; "Some"; "app"; "None"; "length"; "negb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "ax_X"; "ax_setS"; "entailsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CDepotCall.DC"; "X4"; "isSome"; "site_facts"; "KEEPD"; "X4r"; "osplit"; "F_call"; "T4b"; "T4d"; "X4a"; "X4b"; "X4c"; "X4f"; "zoneR"; "R4_families"; "T40"; "T4a"; "T4c"; "T4m1"; "T4m2"; "T4m3"; "in_famb"; "perm4"; "prim_fitb"; "rt_okD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_geom"; "aa_depot"; "ag_spacebeg"; "ag_ctx"; "ag_thread"; "topG"; "sec_chunk"; "DG"; "ageom"; "aa_live"; "aa_sec"; "sc_map_beg"; "sc_map_size"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"; "bv_signed"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states"; "PostD"; "PreD"; "nocells"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "smatchA"; "jpredA"; "liftKA"; "ok_frameA"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@Stdlib.Lists.List"; "In"; "forallb"; "incl"; "existsb"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "Build_machine_state"; "ms_fcsr"; "ms_fregs"; "ms_pc_val"; "ms_regs"; "ms_resv"; "ms_rom"; "ms_svc_pending"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "vms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP"; "E4d"; "C5"; "upd"; "F_gen"; "O_pcc"; "O_pck"; "O_pcs"; "O_st"; "PIECES"; "V_CNT"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "cfg_model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "assn"; "etriple"; "triple"; "w_cfg"; "w_tr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "KcA"; "Kc_ok"; "V_DEPTH"; "malloc_depth"; "J_alloc_preT"; "client_addrA"; "client_shadowA"; "pre_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_absorb"; "rho_sub"; "wsub_get"; "in_ranges"; "wsub"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SpineMallocS1"; "JG"; "@LinuxProcessSemantics.Riscv.Instr"; "aluop"; "mulop"; "ALU_ADD"; "@Corelib.Lists.ListDef"; "Forall"; "seq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj"; "merge_objs_at"; "split_obj_at"; "rebase_obj_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "import_postA"; "jpostA"; "J_ofPA"; "import_okPA"; "entails_frA"; "call_checkPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.DepotK"; "KD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "Size";
"rz"; "ClassID"; "IMG_HI"; "IMG_LO"; "Sh"; "is_primary"; "kSpaceSize"; "needed"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "call_linkP"; "new_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CDepotCall.GL"; "lit63"; "hi_leb"; "lo_geb"; "coveredb"; "coveredb_ref"; "hi_leb_p"; "lo_geb_p"; "coveredb_p"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf"; "DFP"; "JLD"; "MAP1"; "MAP1N"; "STORE"; "dfp_static"; "DFPw"; "JD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI"; "cls_of"; "chk_of"; "cnt_of"; "rhoM_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "geom_ok"; "inv3"; "primary_repr"; "secondary_repr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.InvD"; "AInvX"; "bumpK"; "with_depot"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.SpineCallocS5"; "JGb"; "depot_onlyK"; "hd_link"; "HD_stmt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "diffs_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "mk_pf"; "select"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObjFast"; "sitv_p"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "sitv"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM"; "rho_sets"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1"; "RT_m1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.SpineCallocS4"; "pvals_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "existsb_lazy"; "forallb_lazy"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.DigFastA"; "mk_pf_f"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CDepotCall"; "coveredb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "bview"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.SegD_refl"; "sobjb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ja.SpineCallocE"; "HDE_stmt"; "@Stdlib.PArith.BinPos.Pos"; "eqb"; "leb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import SysSpec Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymSoundW SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymDigFast SymObjFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt StepA SoundA CompleteA EntailA CFGA GlueA GlueA2 SummaryA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells Iface SegQ_defs Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RebuildSM SMGlue InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ContractFreeNull.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ContractFreeNullInit.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertCallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ip.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ja.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.GlueMU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineCallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.SpineCallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.SpineCallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.SpineCallocS6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ja.SpineCallocE.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_ins.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_laws2 SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ik.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i8.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.SegD_cost OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_ins OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.LedgerLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.InvD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_laws2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.SegD_refl OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ik.SegD2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.DepotK.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.CallocBase.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.DigFastA.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section GL.
Variable segs : list Segment.

Lemma SPA_rebase : ltac2:(tb__ "0|1|
S71SeS3dS30S12S2aS68Q40A1A1S91S25S2fS12A1SadS3cR5A1R4A2S37S12R3A2A3S25S2aS2dScScA2M0A1S3eR6A1S31G0A1A3S6fVsegs;R9R7R8R4R3A6S6fVsegs;RaS3fR8R6A2R9R5R4A6F_;F_;F_;Fw;Ftp;FS';Fi;FA;Frho;FJ;").
Proof using .
  intros J rho A i S' tp [tr [ms md]] Hrb HX [(Hsm & HMI & Hwf & Hsh & Hhz) Hk]. split; [|exact Hk].
  pose proof (smatch_rebase segs rho (ax_S A) i S' _ Hrb Hsm) as Hsm'.
  unfold rebase_obj_at in Hrb. destruct (nth_error (ss_objs (ax_S A)) i) as [o|] eqn:Hn; [|discriminate].
  destruct (rebase_obj (ss_facts (ax_S A)) o) as [o'|] eqn:Ho; [|discriminate]. injection Hrb as <-.
  split; [exact Hsm'|]. split; [exact HMI|]. split; [unfold axwf in Hwf |- *; cbn; exact Hwf|]. split; [|exact Hhz].
  unfold shadow_ok in *. destruct A as [S X b]. cbn [ax_X ax_S ax_base ax_setS] in *. subst X. constructor.
Qed.

Definition ms_with_mem (ms : machine_state) (f : word -> option byte) : machine_state := ltac2:(tb__ "0|0|
S7bS7fVms;A1S7dVms;A1S7eVms;A1S82Vms;A1S80Vms;A1S7cVms;A1Vf;S81Vms;A1A8").

Lemma smatch_absorb_any : ltac2:(tb__ "0|5|
SeS12S2aSdA1S7aS2dS2aS75A1S8eA2SdS68Q40M0A1S76SdR2R5A3S24S3S34S0S0S13R8R3A2M1A3S69G0R2A2M2A2S4G2S35S0S0G1A3A2A2S27SdSdS24S76SdR1S1dR9A1A3S24S3S34S0S0S13RaR1A2M3A3S69G0R4A2M4A2S4G4S35S0S0G3A3A2A2A2Lo';A2F_;F_;Fa;Fo;S21Vsegs;R6R5R2A4S21Vsegs;S9fR7R5R4A3R6R3A4F_;F_;Fw;Fmsf;FR;FS;Frho;").
Proof using .
  intros rho S R msf [tr [ms md]] HR Hsm.
  pose proof Hsm as (Hwf & Hpc & Hpend & Hhalt & Hrom & Hroc & Hregs & Hfregs & Hfcsr & Hresv & (Hall & Hpd & Hfr) & Hfacts).
  cbn [fst snd cfg_ms cfg_model] in *.
  split; [exact Hwf|]. split; [exact Hpc|]. split; [exact Hpend|]. split; [exact Hhalt|]. split; [exact Hrom|]. split; [exact Hroc|].
  split; [intros r; unfold regs_match in Hregs; rewrite eval_absorb; apply Hregs|].
  split; [intros r; unfold fregs_match in Hfregs; rewrite eval_absorb; apply Hfregs|].
  split; [unfold fcsr_match in *; destruct (ss_fcsr S); rewrite ?eval_absorb; exact Hfcsr|].
  split; [unfold resv_match in *; destruct (ss_resv S); rewrite ?eval_absorb; exact Hresv|].
  split; [|apply Forall_forall; intros p Hp; apply holds_absorb; exact (proj1 (Forall_forall _ _) Hfacts p Hp)].
  split; [apply Forall_forall; intros o Ho; apply obj_holds_absorb; exact (proj1 (Forall_forall _ _) Hall o Ho)|].
  split; [apply pairwise_disjoint_absorb; exact Hpd|].
  intros a Ha. rewrite outside_all_absorb in Ha. cbn [fst snd cfg_ms]. refine (eq_trans (Hfr a Ha) _). unfold rho_absorb. cbn [rm].
  destruct (in_ranges_dec rho R a) as [Hin|Hout]; [|reflexivity].
  exfalso. destruct Hin as (o & HoR & Hr). destruct (HR o a HoR Hr) as (o' & Ho' & Hr'). exact (proj1 (Forall_forall _ _) Ha o' Ho' Hr').
Qed.

Lemma SPA_absorb_any : ltac2:(tb__ "0|7|
S71S71SeS3dS2aSdA1S7aS2aS68Q40M0A1M1A1S91S25S2aS2dScScA2M2A1S3eR5A1S31G2A1A3SdG1S76SdR2R7A3S24S3S34S0S0S13RaR3A2M3A3S69G0R2A2M4A2S4G4S35S0S0G3A3A2A2S27SdSdS24S76SdR1S1dS3cRbA1A1A3S24S3S34S0S0S13RcR1A2M5A3S69G0R4A2M6A2S4G6S35S0S0G5A3A2A2A2Lo';A2F_;F_;Fa;Fo;S6fVsegs;RaR7R8R4R3A6RaS9fR9R7R6A3R5S96R4A1S90S95R4A1A1A4S6fVsegs;RbR9S9fRaR8R7A3R6R5A6F_;F_;F_;F_;Fw;Ftp;Fmsf;FR;FA;Frho;FJ';FJ;").
Proof using .
  intros J J' rho A R msf tp [tr [ms md]] HX HR [(Hsm & HMI & Hwf & Hsh & Hhz) _] HJ'. split; [|exact HJ'].
  split; [|split; [exact HMI | split; [exact Hwf | split; [|exact Hhz]]]].
  - unfold virt in Hsm |- *. cbn [fst snd cfg_ms cfg_model w_tr w_cfg] in Hsm |- *. apply smatch_absorb_any; [exact HR | exact Hsm].
  - unfold shadow_ok in *. destruct A as [S X b]. cbn [ax_X ax_S ax_base] in *. subst X. constructor.
Qed.

Definition lit63 (z : Z) : bool := ltac2:(tb__ "0|1|
S33S6S9S8Z2Z3fA2M0A1Vz;A2SaVz;G0A2A2").
Definition lo_geb (facts : list sprop) (l l' : sv) : bool := ltac2:(tb__ "0|4|
S36S14Vl;Vl';A2ScS29Ll;Vl;S0S33Sc2R1A1S2fS2dS0S0A2M0A1S29Lx;Se6Vfacts;Vl';A2G0G0S29Lp;R1S0S0S6R1R4A2Lh';Lz;X2dx1Lp;S2bX2fx2A2La;S1S2bLi;Sa6ScScS2bLb;La;M1Lop;M2G2Sa7G1Lop;M3G3S29S2ScS2bLa;Lw;Lsgn;S1ScS0S2bLk;Li;Ll0;Xcx8A2").
Definition hi_leb (facts : list sprop) (h h' : sv) : bool := ltac2:(tb__ "0|4|
S36S14Vh;Vh';A2ScS29Lh;Vh;S0S33Sc2R1A1S2fS2dS0S0A2M0A1S29Lx;Se6Vfacts;Vh';A2G0G0S29Lp;R1S0S0S6R4R2A2Lz;Ll';X2dx1Lp;S2bX2fx2A2La;S1S2bLi;Sa6ScScS2bLb;La;M1Lop;M2G2Sa7G1Lop;M3G3S29S2ScS2bLa;Lw;Lsgn;S1ScS0S2bLk;Li;Ll;Xcx8A2").
Definition coveredb_ref (facts : list sprop) (R objs : list sobj) : bool := ltac2:(tb__ "0|0|
S77SdSdS79SdSdS33S33S14S19R2A1S19R1A1A2Sc4Vfacts;S1bR2A1S1bR1A1A3A2Sc3Vfacts;S1aR2A1S1aR1A1A3A2Lo';Vobjs;A3Lo;VR;A3").
Lemma lo_geb_sound : ltac2:(tb__ "0|0|
SeS2aSfA1ScScSa9SfS1cR4A1R3A3S25S29Sc4R4R3R2A3S2cA3S3S1fR6R3A2S1fR6R4A2A2F_;F_;Fl';Fl;Ffacts;Frho;").
Proof.
  intros rho facts l l' HF H. unfold lo_geb in H. apply orb_prop in H as [H|H]; [apply sv_eqb_sound in H; subst; lia|].
  destruct l as [a| | | | | | |]; try discriminate H. apply andb_prop in H as [H1 H2]. unfold lit63 in H1. apply andb_prop in H1 as [H1a H1b].
  apply Z.leb_le in H1a. apply Z.ltb_lt in H1b. destruct (sitv facts l') as [[l0 h0]|] eqn:E; [|discriminate H2]. apply Z.leb_le in H2.
  pose proof (proj1 (sitv_sound rho facts l' l0 h0 HF E)). rewrite soff_lit_small by lia. lia.
Qed.
Lemma hi_leb_sound : ltac2:(tb__ "0|0|
SeS2aSfA1ScScSa9SfS1cR4A1R3A3S25S29Sc3R4R3R2A3S2cA3S3S1fR6R4A2S1fR6R3A2A2F_;F_;Fh';Fh;Ffacts;Frho;").
Proof.
  intros rho facts h h' HF H. unfold hi_leb in H. apply orb_prop in H as [H|H]; [apply sv_eqb_sound in H; subst; lia|].
  destruct h as [a| | | | | | |]; try discriminate H. apply andb_prop in H as [H1 H2]. unfold lit63 in H1. apply andb_prop in H1 as [H1a H1b].
  apply Z.leb_le in H1a. apply Z.ltb_lt in H1b. destruct (sitv facts h') as [[l0 h0]|] eqn:E; [|discriminate H2]. apply Z.leb_le in H2.
  pose proof (proj1 (sitv_sound rho facts h' l0 h0 HF E)). rewrite soff_lit_small by lia. lia.
Qed.
Lemma coveredb_ref_sound : ltac2:(tb__ "0|6|
S2aSfA1S2aSdA1M0G0SeSdS68Q40M1A1Sa9SfS1cR3A1R6A3S25S29Sc6R7R6R5A3S2cA3S76SdR4R7A3S24S3S34S0S0S13R6R5A2M2A3S69G1R4A2M3A2S4G3S35S0S0G2A3A2A2S27SdSdS24S76SdR1R9A3S24S3S34S0S0S13R8R1A2M4A3S69G1R6A2M5A2S4G5S35S0S0G4A3A2A2A2Lo';A2F_;F_;F_;F_;Fa;Fo;Frho;Fobjs;FR;Ffacts;").
Proof.
  intros facts R objs rho o a HF H Ho Ha. pose proof (proj1 (forallb_forall _ _) H o Ho) as X. cbn beta in X.
  apply existsb_exists in X as (o' & Ho' & E). apply andb_prop in E as [E Hh]. apply andb_prop in E as [Eb Hl].
  apply sv_eqb_sound in Eb. exists o'. split; [exact Ho'|].
  pose proof (lo_geb_sound rho facts _ _ HF Hl) as L. pose proof (hi_leb_sound rho facts _ _ HF Hh) as Hi.
  unfold obj_range, obj_lo_of, obj_hi_of in Ha |- *. cbn [fst snd] in Ha |- *. rewrite <- Eb. lia.
Qed.

Definition lo_geb_p (pf : pfacts) (l l' : sv) : bool := ltac2:(tb__ "0|5|
S29S29L_;M0S14Vl;Vl';A2S2cScS29Ll;Vl;S0G0Sc2R1A1S2fS2dS0S0A2M1A1S29Lx;Se5Vpf;Vl';A2G1G1S29Lp;R1S0S0S6R1R4A2Lh';Lz;X2dx1Lp;S2bX2fx2S2bX29x2La;S1S2bLi;Sa6ScScS2bLb;La;M2Lop;M3G3Sa7G2Lop;M4G4S29S2ScS2bLa;Lw;Lsgn;S1ScS0S2bLk;Li;Ll0;Xcx8X29x2").
Definition hi_leb_p (pf : pfacts) (h h' : sv) : bool := ltac2:(tb__ "0|5|
S29S29L_;M0S14Vh;Vh';A2S2cScS29Lh;Vh;S0G0Sc2R1A1S2fS2dS0S0A2M1A1S29Lx;Se5Vpf;Vh';A2G1G1S29Lp;R1S0S0S6R4R2A2Lz;Ll';X2dx1Lp;S2bX2fx2S2bX29x2La;S1S2bLi;Sa6ScScS2bLb;La;M2Lop;M3G3Sa7G2Lop;M4G4S29S2ScS2bLa;Lw;Lsgn;S1ScS0S2bLk;Li;Ll;Xcx8X29x2").
Definition coveredb_p (pf : pfacts) (R objs : list sobj) : bool := ltac2:(tb__ "0|1|
SedSdSdSecSdSdS29S29L_;M0S14S19R2A1S19R1A1A2G0Sc8Vpf;S1bR2A1S1bR1A1A3Sc7Vpf;S1aR2A1S1aR1A1A3S2bX29x2S2bX29x2Lo';Vobjs;A3Lo;VR;A3").
Definition coveredb (facts : list sprop) (R objs : list sobj) : bool := ltac2:(tb__ "0|0|
Sc9Sf0Vfacts;A1VR;Vobjs;A3").
Lemma lo_geb_p_eq : ltac2:(tb__ "0|0|
S2aSfA1ScScS25S29Sc8Se3R3A1R2R1A3Sc4R3R2R1A3A3Fl';Fl;Ffacts;").
Proof. intros facts l l'. unfold lo_geb_p, lo_geb. rewrite sitv_p_eq. destruct (sv_eqb l l'); [reflexivity|]. destruct l; reflexivity. Qed.
Lemma hi_leb_p_eq : ltac2:(tb__ "0|0|
S2aSfA1ScScS25S29Sc7Se3R3A1R2R1A3Sc3R3R2R1A3A3Fh';Fh;Ffacts;").
Proof. intros facts h h'. unfold hi_leb_p, hi_leb. rewrite sitv_p_eq. destruct (sv_eqb h h'); [reflexivity|]. destruct h; reflexivity. Qed.
Lemma coveredb_ref_eq : ltac2:(tb__ "0|1|
S2aSfA1S2aSdA1M0G0S25S29Sc5R3R2R1A3Sc6R3R2R1A3A3Fobjs;FR;Ffacts;").
Proof.
  intros facts R objs. unfold coveredb, coveredb_p, coveredb_ref. rewrite DigFastA.mk_pf_f_eq, forallb_lazy_eq.
  assert (FE : forall {T} (f g : T -> bool) l, (forall x, f x = g x) -> forallb f l = forallb g l).
  { intros T f g l H. induction l as [|x l IH]; [reflexivity|]. cbn. rewrite H, IH. reflexivity. }
  assert (EE : forall {T} (f g : T -> bool) l, (forall x, f x = g x) -> existsb f l = existsb g l).
  { intros T f g l H. induction l as [|x l IH]; [reflexivity|]. cbn. rewrite H, IH. reflexivity. }
  apply FE. intros o. rewrite existsb_lazy_eq. apply EE. intros o'.
  rewrite lo_geb_p_eq, hi_leb_p_eq. destruct (sv_eqb _ _); [|reflexivity]. destruct (lo_geb _ _ _); reflexivity.
Qed.
Lemma coveredb_sound : ltac2:(tb__ "0|6|
S2aSfA1S2aSdA1M0G0SeSdS68Q40M1A1Sa9SfS1cR3A1R6A3S25S29Sc5R7R6R5A3S2cA3S76SdR4R7A3S24S3S34S0S0S13R6R5A2M2A3S69G1R4A2M3A2S4G3S35S0S0G2A3A2A2S27SdSdS24S76SdR1R9A3S24S3S34S0S0S13R8R1A2M4A3S69G1R6A2M5A2S4G5S35S0S0G4A3A2A2A2Lo';A2F_;F_;F_;F_;Fa;Fo;Frho;Fobjs;FR;Ffacts;").
Proof.
  intros facts R objs rho o a HF H. rewrite coveredb_ref_eq in H. exact (coveredb_ref_sound facts R objs rho o a HF H).
Qed.
End GL.

Lemma rw_rho_sets_ext : ltac2:(tb__ "0|1|
SeSeS2aS2dS1S68Q40A1M0A2A1S1S1S25G0S10R4R1A2S10R5R1A2A3Fj;S25G0S10Se8R4R3A2R2A2S10Se8R5R3A2R2A2A3F_;Fi;Fl;Fr';Fr;").
Proof.
  intros r r' l. revert r r'. induction l as [|[j v] t IH]; intros r r' i H; cbn; [apply H|].
  apply IH. intros k. unfold rho_set_rw. cbn. rewrite H. reflexivity.
Qed.
Lemma rhoM_of_AK : ltac2:(tb__ "0|1|
S5aS62SeSeS1S25S68Q40A1M0S10R2R1A2S10R3R1A2A3Fj;S1S25G0S10Sd5SdbSdcR6R5A2A1R3A2R1A2S10Sd5R6R4A2R1A2A3Fi;F_;Fr';Fr;FG';FA;").
Proof.
  intros A G' r r' H i. unfold rhoM_of, cnt_of, chk_of, cst_of. cbn [aa_geom aa_sec aa_ptr_committed aa_cls bumpK with_depot].
  rewrite (H 12%positive). apply rw_rho_sets_ext. exact H.
Qed.

Section DC.
Variable st : ustop. Variable tmax : Z.
Let W : list ulink := Wcan 0.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.

Hypothesis HCSTD : ltac2:(tb__ "0|0|
S0Sf5VCST;R1A2S28ScfR2A1A1F_;Fa;").
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.
Let J (W : list ulink) (st : ustop) (A : AA) (Kc : KcA) : jpredA := ltac2:(tb__ "0|0|
S9bVAInv;VW;Vst;VA;VKc;S15PcA1A6").
Hypothesis Htmax : 1 <= tmax <= SZMAX.

Definition KEEPD (A : AA) (a : Z) : Prop := ltac2:(tb__ "0|0|
S26S9cVCST;VA;Va;A3S9dVCST;VXGL;VA;Va;A4A2").

Definition F_call : list sprop := ltac2:(tb__ "0|3|
S2eSfS18S11Z7fff7f800000A1M0S15PaA1M1A2S2eSfS18G0S1eSa8G1S11Nf10A1A3A2S2eSfS18G0S1eSa8G1S11N848A1A3M2A2S2eSfS18G2S11SbS8Z2Z40A2Z848A2A1A2S31SfA1A3A3A3A3").
Definition X4f : axst := ltac2:(tb__ "0|0|
SefS47S84VW;Vst;Vtmax;A3A2").
Definition X4r (sz : Z) : axst := ltac2:(tb__ "0|1|
S86VW;Vst;Vtmax;S4dZ7e9e4S2eS2dS30ScA2M0S32S30ScUbS11Vsz;A1A4S31G0A1A3S31SdA1S2bS31SfA1A9").
Definition osplit (A : axst) (i : nat) (mid : sv) : axst := ltac2:(tb__ "0|0|
S2fS12A1S3dLx;SacS3cVA;A1Vi;Vmid;A3S12S3fVA;R1A2LS';VA;X2fx2").
Definition isSome {T} (o : option T) : bool := match o with Some _ => true | None => false end.
Definition X4a (sz : Z) : axst := ltac2:(tb__ "0|0|
S46S45Vsz;A1U0S11Nf10A1A3").
Definition X4b (sz : Z) : axst := ltac2:(tb__ "0|0|
S46S4aVsz;A1U1S11N910A1A3").
Definition X4c (sz : Z) : axst := ltac2:(tb__ "0|0|
S46S4bVsz;A1U2S11N848A1A3").
Definition X4 (sz : Z) : axst := ltac2:(tb__ "0|0|
S46S4cVsz;A1U3S11N50A1A3").
Hypothesis NXE : ltac2:(tb__ "0|0|
S25S29Sf9SeaS16S3cS84VW;Vst;Vtmax;A3A1A1A2S2cA3").
Hypothesis FBE : ltac2:(tb__ "0|0|
S25S29S77SfS20S16S3cS84VW;Vst;Vtmax;A3A1A1A1S47A3S2cA3").
Hypothesis XE4 : ltac2:(tb__ "0|1|
S25S2aS2dScScA2M0A1S3eS84VW;Vst;Vtmax;A3A1S31G0A1A3").
Hypothesis F192 : ltac2:(tb__ "0|1|
S78SfS2eSfS18S11Z1A1S15Pc0A1M0A2S2eSfS18G0S11Vtmax;A1A2S31SfA1A3A3S17S3cS84VW;Vst;Vtmax;A3A1A1A3").
Hypothesis FDEP : ltac2:(tb__ "0|0|
S78SfS9eS9aA1S17S3cS84VW;Vst;Vtmax;A3A1A1A3").
Hypothesis FGEN4 : ltac2:(tb__ "0|0|
S78SfS87S17S3cS84VW;Vst;Vtmax;A3A1A1A3").
Hypothesis YP4 : ltac2:(tb__ "0|0|
S76SfS18S11Z1A1S15S8dA1A2S17S3cS84VW;Vst;Vtmax;A3A1A1A3").
Hypothesis WX4r : ltac2:(tb__ "0|0|
S0S24S3Z1R1A2S3R1Vtmax;A2A2S25S29S22S3cS45R2A1A1A1S2cA3F_;Fsz;").
Hypothesis DX4r : ltac2:(tb__ "0|4|
S0S24S3Z1R1A2S3R1Vtmax;A2A2S25S2fS2dS2aS2dScScA2M0A1M1S2aSfA1M2A2M3A1Se1S3cS4dA1S3cS45R2A1A1A2S37G3S32G1G2S2eG0S32ScScS23S2bQ20S15Pc0A1A3S11R2A1A4S31G0A1A3S31SfA1A4A2A3F_;Fsz;").
Hypothesis SPL1 : ltac2:(tb__ "0|0|
S0S24S3Z1R1A2S3R1Vtmax;A2A2S25S29S42S12SacS3cS45R2A1A1U0S11Nf10A1A3A2S2cA3F_;Fsz;").
Hypothesis SPL2 : ltac2:(tb__ "0|0|
S0S24S3Z1R1A2S3R1Vtmax;A2A2S25S29S42S12SacS3cS4aR2A1A1U1S11N910A1A3A2S2cA3F_;Fsz;").
Hypothesis SPL3 : ltac2:(tb__ "0|0|
S0S24S3Z1R1A2S3R1Vtmax;A2A2S25S29S42S12SacS3cS4bR2A1A1U2S11N848A1A3A2S2cA3F_;Fsz;").
Hypothesis SPL4 : ltac2:(tb__ "0|0|
S0S24S3Z1R1A2S3R1Vtmax;A2A2S25S29S42S12SacS3cS4cR2A1A1U3S11N50A1A3A2S2cA3F_;Fsz;").

Definition call_pack (X : axst) (sz : Z) : option (wsub * list sobj * axst) := ltac2:(tb__ "0|6|
S2eS2dS1ScA2M0S32S1ScPfS11N600A1A4SeeP1S3cVX;A1S3cS6dVsz;A1M1A1A3A3S2aG0A1M2S2fS2aSdA1M3A1S2fS2dS2dSa3G3A2S3dA2M4A1Lx;Sb2VX;G1R1A3G3S37S2dS2dG2G3A2M5S3dA2S32G5S3dS32G2G3R2R1A4SaeR2G1S6cVsz;A1VX;R1A5A4A2LR;S39G4A1X2fx2Ts;").

Variables (s4 : Z -> wsub) (R4 : Z -> list sobj) (T4 : Z -> axst).
Hypothesis HER : ltac2:(tb__ "0|1|
S0S24S3Z1R1A2S3R1Vtmax;A2A2S25S2fS2aSdA1M0A1Sb2S41R2A1S6dR2A1Vs4;R2A1A3S37G0VR4;R2A1A2A3F_;Fsz;").
Hypothesis HT4 : ltac2:(tb__ "0|0|
S0S24S3Z1R1A2S3R1Vtmax;A2A2S25S3dSaeVs4;R2A1S6dR2A1S6cR2A1S41R2A1VR4;R2A1A5VT4;R2A1A3F_;Fsz;").
Hypothesis XX4 : ltac2:(tb__ "0|1|
S0S24S3Z1R1A2S3R1Vtmax;A2A2S25S2aS2dScScA2M0A1S3eS41R2A1A1S31G0A1A3F_;Fsz;").
Hypothesis FBX4 : ltac2:(tb__ "0|1|
S0S24S3Z1R1A2S3R1Vtmax;A2A2S25S29S77SfS20S16S3cS41R2A1A1M0A1A1S17G0A1A3S2cA3F_;Fsz;").
Hypothesis Hchk4 : ltac2:(tb__ "0|0|
S0S24S3Z1R1A2S3R1Vtmax;A2A2S25S29Sb3S41R2A1S6dR2A1Vs4;R2A1VR4;R2A1S2eS3dS6cR2A1S31S3dA1A3A5S2cA3F_;Fsz;").
Hypothesis NX4 : ltac2:(tb__ "0|0|
S0S24S3Z1R1A2S3R1Vtmax;A2A2S25S1S16S3cS41R2A1A1A1S16S3cS84VW;Vst;Vtmax;A3A1A1A3F_;Fsz;").
Hypothesis WG10 : ltac2:(tb__ "0|1|
S0S24S3Z1R1A2S3R1Vtmax;A2A2S25ScSa1Vs4;R2A1PaM0A2S1eSa8S15G0A1S11N910A1A3A3F_;Fsz;").
Hypothesis WG15 : ltac2:(tb__ "0|0|
S0S24S3Z1R1A2S3R1Vtmax;A2A2S25ScSa1Vs4;R2A1PfA2S11N600A1A3F_;Fsz;").
Hypothesis WG12 : ltac2:(tb__ "0|0|
S0S24S3Z1R1A2S3R1Vtmax;A2A2S25ScSa1Vs4;R2A1PcA2S1eSa8S15PaA1S11N848A1A3A3F_;Fsz;").

Definition R4_families : list sobj := ltac2:(tb__ "0|0|
S38SdSe9S38SdS2eSdS88S2eSdS8aS2eSdS89S2eSdS8bS31SdA1A3A3A3A3S8cA3A3").
Definition in_famb (o : sobj) : bool := ltac2:(tb__ "0|3|
S36S79SdSdSf6S6eVo;A1S6eR1A1A2Lo';S4fA3S33S14S19Vo;A1S15PaA1A2ScS29Lx;S1bVo;A1S0S33S6N910R1A2S6R1Z0A2A2Llo;S1S33Sf8R1S99A2S14S1aVo;A1S11Nf10A1A2A2Li;Sa6ScScS2bLb;La;M0Lop;M1G1Sa7G0Lop;M2G2S29S2ScS2bLa;Lw;Lsgn;S1ScS0S2bLk;Li;Ll;Xcx8A2A2").
Hypothesis FAM4 : ltac2:(tb__ "0|0|
S0S24S3Z1R1A2S3R1Vtmax;A2A2S25S29S77SdS56VR4;R2A1A3S2cA3F_;Fsz;").
Hypothesis NEWO : ltac2:(tb__ "0|0|
S0S24S3Z1R1A2S3R1Vtmax;A2A2S25S2aSdA1Sc1S3cS6dR2A1A1S3cS6cR2A1A1A2S31SdA1A3F_;Fsz;").
Hypothesis XPost : ltac2:(tb__ "0|1|
S0S25S2aS2dScScA2M0A1S3eS6cR1A1A1S31G0A1A3Fsz;").

Hypothesis FBT4 : ltac2:(tb__ "0|0|
S0S24S3Z1R1A2S3R1Vtmax;A2A2S25S29S77SfS20S16S3cVT4;R2A1A1A1A1S17S3cS41R2A1A1A1A3S2cA3F_;Fsz;").
Hypothesis XT4 : ltac2:(tb__ "0|1|
S0S24S3Z1R1A2S3R1Vtmax;A2A2S25S2aS2dScScA2M0A1S3eVT4;R2A1A1S31G0A1A3F_;Fsz;").
Definition T40 (sz : Z) : axst := ltac2:(tb__ "0|0|
Sf1VT4;Vsz;A1S17S3cS41Vsz;A1A1A1A2").
Definition oreb (A : axst) (i : nat) : axst := ltac2:(tb__ "0|0|
S2fS12A1S3dLx;SadS3cVA;A1Vi;A2S12S3fVA;R1A2LS';VA;X2fx2").
Definition omrg (A : axst) (i : nat) : axst := ltac2:(tb__ "0|0|
S2fS12A1S3dLx;SabS3cVA;A1Vi;A2S12S3fVA;R1A2LS';VA;X2fx2").
Definition T4a (sz : Z) : axst := oreb (T40 sz) 0.
Definition T4b (sz : Z) : axst := oreb (T4a sz) 1.
Hypothesis RB1 : ltac2:(tb__ "0|0|
S0S24S3Z1R1A2S3R1Vtmax;A2A2S25S29S42S12SadS3cS50R2A1A1U0A2A2S2cA3F_;Fsz;").
Hypothesis RB2 : ltac2:(tb__ "0|0|
S0S24S3Z1R1A2S3R1Vtmax;A2A2S25S29S42S12SadS3cS51R2A1A1U1A2A2S2cA3F_;Fsz;").
Definition perm4 : list nat := ltac2:(tb__ "0|0|
S38S30S2eS30U9S2eS30U0S2eS30UaS2eS30U1S2eS30UbS2eS30U2S2eS30U3S2eS30U4S2eS30U5S2eS30U6S2eS30U7S2eS30U8S31S30A1A3A3A3A3A3A3A3A3A3A3A3A3SaaUcU24A2A3").
Hypothesis PERM_nd : nodupN perm4 = true.
Hypothesis PERM_len : ltac2:(tb__ "0|0|
S0S24S3Z1R1A2S3R1Vtmax;A2A2S25S30S3aSdS1dS3cS48R2A1A1A1A2U30A3F_;Fsz;").
Definition T4c (sz : Z) : axst := ltac2:(tb__ "0|2|
S3fS48Vsz;A1M0Se7S3cG0A1M1Se4S1dG1A1S57A2A2A2").
Definition T4m1 (sz : Z) : axst := omrg (T4c sz) 0.
Definition T4m2 (sz : Z) : axst := omrg (T4m1 sz) 0.
Definition T4m3 (sz : Z) : axst := omrg (T4m2 sz) 0.
Definition T4d (sz : Z) : axst := omrg (T4m3 sz) 0.
Hypothesis MRG1 : ltac2:(tb__ "0|0|
S0S24S3Z1R1A2S3R1Vtmax;A2A2S25S29S42S12SabS3cS52R2A1A1U0A2A2S2cA3F_;Fsz;").
Hypothesis MRG2 : ltac2:(tb__ "0|0|
S0S24S3Z1R1A2S3R1Vtmax;A2A2S25S29S42S12SabS3cS53R2A1A1U0A2A2S2cA3F_;Fsz;").
Hypothesis MRG3 : ltac2:(tb__ "0|0|
S0S24S3Z1R1A2S3R1Vtmax;A2A2S25S29S42S12SabS3cS54R2A1A1U0A2A2S2cA3F_;Fsz;").
Hypothesis MRG4 : ltac2:(tb__ "0|0|
S0S24S3Z1R1A2S3R1Vtmax;A2A2S25S29S42S12SabS3cS55R2A1A1U0A2A2S2cA3F_;Fsz;").
Variable sd : Z -> wsub.
Hypothesis ENT5 : ltac2:(tb__ "0|0|
S0S24S3Z1R1A2S3R1Vtmax;A2A2S25S29S40S49R2A1S85VW;Vst;Vtmax;A3Vsd;R2A1A3S2cA3F_;Fsz;").
Hypothesis SID5 : ltac2:(tb__ "0|0|
S0S24S3Z1R1A2S3R1Vtmax;A2A2S25S29Sa4Vsd;R2A1SeaA2S2cA3F_;Fsz;").

Hypothesis R4cov : ltac2:(tb__ "0|1|
S0S24S3Z1R1A2S3R1Vtmax;A2A2S25S29Sf3S17S3cS49R2A1A1M0A1VR4;R2A1S1dG0A1A3S2cA3F_;Fsz;").

Definition rt_okD (o : sobj) : bool := ltac2:(tb__ "0|b|
ScS29Lx;M0S1bVo;A1S0G0S1aVo;A1S0S36S36S33S14S19Vo;A1M1S11Z0M2A1A2S33S33S33S6Sb9R2A2S6R2R1A2M3A2S6R1Sb8A2A2S36S6R1SceA2S6S5SccS7Z8ScdA2A2R2A2A2A2A2S33S14G1S15P97A1A2S33S33S6G2R2A2G3A2S6R1Z1000A2A2M4A2A2S33S14G1S15P98A1A2G4A2A2Lhi;S1S2bLi;M5Sa6ScScS2bLb;La;M6Lop;M7G7Sa7G6Lop;M8G8S29S2ScS2bLa;Lw;Lsgn;M9S1ScS0S2bLk;Li;Ll;MaXcx8Llo;G5G7G7G8G8G9GaXcx8").
Lemma RT_m1_okD : ltac2:(tb__ "0|0|
S25S29S77SdS59Se9A3S2cA3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma obj_range_nocells : ltac2:(tb__ "0|0|
SeSdS25S2dS0S0A2S13R2S6eR1A1A2S13R2R1A2A3Fo;Frho;").
Proof. intros rho [b lo hi cs d]. reflexivity. Qed.

Definition zoneR (T C SB ab szc top a : Z) : Prop := ltac2:(tb__ "0|2|
S26S24S24S3Sb9Va;A2S4Va;Sb8A2A2S26S4Va;SceA2S3S5SccS7Z8ScdA2A2Va;A2A2A2S26S24S3VT;Va;A2S4Va;S5VT;Z1000M0A2A2A2S26S24S3VC;Va;A2S4Va;S5VC;G0A2A2A2S26S24S3Vab;Va;A2S4Va;S5Vab;Vszc;A2M1A2A2S26S24S3SbaVab;A1Va;A2S4Va;SbaG1A1A2A2S3Vtop;Va;A2A2A2A2A2A2").

Lemma R4_zone : ltac2:(tb__ "0|8|
S0SeS5aSdS0S24S3Z1M0R5A2S3R5Vtmax;A2A2S69Q40M1S10R5PcA2A2S0SebR6S5dS5bR5A1A1Sd2R1A1M2Sd3R5R1A2Sb6R1A1Sb5G2A1R1A7S24S3G0Sd4R6R2A2M3A2S3G3Z10M4A2A2S25S68G1A1M5S10R8P97A2S6aG1S5fS5bR7A1A1A2A3S25G5S10R9P98A2S6aG1S5eS5bR8A1A1A2A3S25G5S10RaP95A2S6aG1Sd4R9R5A2A2A3Sd6S5bRaA1A1S3S60S5bRbA1A1S5S69G1S10RcPaA2A2S6bG1S10RcS99A2A2A2A2S3S6bG1S10RdS99A2A2S9S9aA1A2S76SdRcVR4;RfA1A3S24S3S34S0S0S13RfRdA2M6A3RcA2S4RcS35S0S0G6A3A2A2S5S5S5dS5bRfA1A1S7Sd2RbA1S8Z2Z20A2A2A2S7G4Sd3RfRbA2A2A2S0S4eS5fS5bR10A1M7A1S5eG7A1S5dG7A1R1Sb5Sd2RcA1A1S60G7A1ReA7Tab;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Tnv;F_;Fa;Fo;FA;FrhoX;Fsz;").
Proof.
  intros sz rhoX A o a Hsz nv PV Hcnt E151 E152 E149 HG TOP DEP Ho Ha ab.
  pose proof (geom_nums _ HG) as (_ & _ & _ & T1 & T2 & _ & C1 & C2 & _ & _ & S1 & S2 & _ & TG). unfold HIGH_SHADOW_END in S1. rewrite kSpaceSize_val in S2.
  pose proof PV as (E12 & E148 & E150 & E155 & E158 & E159 & Bn & Bsz & Brz & Bfit & BSB & Bc & Bx & Btop).
  pose proof (pv_ab rhoX _ _ _ _ _ _ PV) as Eab. pose proof (pv_ub rhoX _ _ _ _ _ _ PV) as Eub. pose proof (pv_ue rhoX _ _ _ _ _ _ PV) as Eue.
  pose proof (pv_bsh rhoX _ _ _ _ _ _ PV) as Ebsh. pose proof (pv_bu rhoX _ _ _ _ _ _ PV) as Ebu. pose proof (pv_lu rhoX _ _ _ _ _ _ PV) as Elu.
  pose proof (pv_lp rhoX _ _ _ _ _ _ PV) as Elp. pose proof (pv_lt rhoX _ _ _ _ _ _ PV) as Elt. pose proof (pv_bp rhoX _ _ _ _ _ _ PV) as Ebp.
  pose proof (pv_br rhoX _ _ _ _ _ _ PV) as Ebr. pose proof (pv_lr rhoX _ _ _ _ _ _ PV) as [Elr Blr]. pose proof (r8_facts rhoX _ _ _ _ _ _ PV) as R8F.
  cbn zeta in Eab, Eub, Eue, Ebsh, Ebu, Elu, Elp, Elt, Ebp, Ebr, Elr, Blr, R8F. fold ab in Eab, Eub, Eue, Ebsh, Ebu, Ebp, Ebr.
  set (T := ag_thread (aa_geom A)) in *. set (CTX := ag_ctx (aa_geom A)) in *. set (SB := ag_spacebeg (aa_geom A)) in *.
  set (szc := Size (cls_of nv)) in *. set (rzv := rz nv) in *. set (x := chk_of A nv) in *. set (c := cls_of nv) in *.
  set (r8 := nv + 7 - (nv + 7) mod 8) in *. set (lp := if Z.eq_dec (nv mod 8) 0 then 0 else 1) in *.
  pose proof (Z.div_pos nv 8 ltac:(lia) ltac:(lia)) as Q0. pose proof (Z.div_le_mono nv (nv + 7) 8 ltac:(lia) ltac:(lia)) as Q1.
  assert (AB8 : ab mod 8 = 0).
  { apply Z.mod_divide; [lia|]. destruct (proj1 (Z.mod_divide SB (2 ^ 16) ltac:(lia)) ltac:(tauto)) as [q Hq].
    exists (q * 2 ^ 13 + c * 2 ^ 29 + 2 * x). unfold ab. fold SB c x. lia. }
  assert (SHR : forall k, 0 <= k <= szc -> Sh ab <= Sh (ab + k) <= Sh (ab + szc)).
  { intros k Hk. unfold Sh. split; apply Z.add_le_mono_r; apply Z.div_le_mono; lia. }
  assert (SHK : forall k, 0 <= k -> Sh (ab + k) = Sh ab + k / 8).
  { intros k Hk. unfold Sh. destruct (proj1 (Z.mod_divide ab 8 ltac:(lia)) AB8) as [q Hq]. rewrite Hq.
    replace (q * 8 + k) with (q * 8 + k) by lia. rewrite Z.div_add_l by lia. rewrite Z.div_mul by lia. lia. }

  pose proof (proj1 (forallb_forall _ _) (FAM4 sz Hsz) o Ho) as Fo. unfold in_famb in Fo. apply orb_prop in Fo as [Fo|Fo].
  - apply existsb_exists in Fo as (o' & Ho' & Eo). apply sobjb_sound in Eo.
    rewrite <- (obj_range_nocells rhoX o), Eo, (obj_range_nocells rhoX o') in Ha. clear Eo Ho o. rename o' into o.
    unfold R4_families in Ho'. apply in_app_or in Ho' as [HRT|Ho']; [|apply in_app_or in Ho' as [HPC|HPI]].
    +
      pose proof (proj1 (forallb_forall _ _) RT_m1_okD o HRT) as OK. unfold rt_okD in OK.
      destruct o as [b lo hi cs d]. cbn [ob_base ob_lo ob_hi] in OK.
      destruct lo as [lo|i1|o1 a1 b1|o1 a1 b1|o1 a1 b1|o1 a1 b1|sg wd a1|l1 i1 k1]; try discriminate OK.
      destruct hi as [hi|i2|o2 a2 b2|o2 a2 b2|o2 a2 b2|o2 a2 b2|sg2 wd2 a2|l2 i2 k2]; try discriminate OK.
      apply orb_prop in OK as [OK|OK]; [apply orb_prop in OK as [OK|OK]|];
        apply andb_prop in OK as [EB OK]; apply sv_eqb_sound in EB; subst b.
      *
        apply andb_prop in OK as [OK X]. apply andb_prop in OK as [OK X0]. apply andb_prop in OK as [OK X1].
        apply Z.leb_le in OK. apply Z.leb_le in X1. apply Z.leb_le in X0.
        rewrite obj_range_mk in Ha by (unfold IMG_LO, IMG_HI in OK, X0; lia). cbn [fst snd eval] in Ha. rewrite u64_lit in Ha by (unfold IMG_LO, IMG_HI in OK, X0; lia). left.
        unfold IMG_LO, IMG_HI, STORE, MAP1, MAP1N in *. apply orb_prop in X as [X|X]; apply Z.leb_le in X; lia.
      *
        apply andb_prop in OK as [OK X]. apply andb_prop in OK as [OK X0]. apply Z.leb_le in OK. apply Z.leb_le in X. apply Z.leb_le in X0.
        rewrite obj_range_mk in Ha by lia. cbn [fst snd eval] in Ha. rewrite E151, u64_lit in Ha by lia. right. left. lia.
      *
        apply andb_prop in OK as [OK X]. apply andb_prop in OK as [OK X0]. apply Z.leb_le in OK. apply Z.leb_le in X. apply Z.leb_le in X0.
        rewrite obj_range_mk in Ha by lia. cbn [fst snd eval] in Ha. rewrite E152, u64_lit in Ha by lia. right. right. left. lia.
    +
      assert (EB : bv_unsigned (eval rhoX pc_base) = T + 0xd0 + 80 * c).
      { unfold pc_base, vT, V_CLS. cbn [eval]. rewrite E151, E158. rewrite add_val, add_val, mul_val, !u64_lit by lia.
        rewrite (Z.mod_small (c * 80)) by lia. rewrite (Z.mod_small (T + 208)) by lia. rewrite Z.mod_small by lia. lia. }
      assert (ECH : soff rhoX choff = 16 + 4 * (cnt_of A nv - 1)).
      { unfold choff, V_CNT. rewrite soff_snorm. unfold U. cbn [eval]. rewrite E149. rewrite add_val, sll_val, add_val, !u64_lit by (clear - Hcnt; lia).
        replace (bv_unsigned (Z_to_bv 64 (-1))) with (2 ^ 64 - 1) by reflexivity.
        replace ((cnt_of A nv + (2 ^ 64 - 1)) mod 2 ^ 64) with (cnt_of A nv - 1) by (rewrite <- (Z.mod_add _ (-1)) by lia; rewrite Z.mod_small by lia; lia).
        change (2 mod 64) with 2. rewrite ?u64_lit by lia. rewrite Z.shiftl_mul_pow2 by lia. rewrite (Z.mod_small (_ * 2 ^ 2)) by lia. rewrite Z.mod_small by lia.
        unfold snorm. rewrite Z.mod_small by lia. destruct (Z.ltb_spec ((cnt_of A nv - 1) * 2 ^ 2 + 16) (2 ^ 63)); lia. }
      assert (ET : bv_unsigned (eval rhoX vT) = T). { unfold vT. cbn [eval]. rewrite E151. apply u64_lit. lia. }
      right. left. destruct HPC as [<-|[<-|[<-|[<-|[]]]]].
      * unfold obj_range, obj_lo_of, obj_hi_of in Ha. cbn [ob_base ob_lo ob_hi O_pcc] in Ha. rewrite !soff_lit_small in Ha by lia. rewrite EB in Ha. cbn [fst snd] in Ha. lia.
      * unfold obj_range, obj_lo_of, obj_hi_of in Ha. cbn [ob_base ob_lo ob_hi O_pcs] in Ha. rewrite !soff_lit_small in Ha by lia. rewrite EB in Ha. cbn [fst snd] in Ha. lia.
      * unfold obj_range, obj_lo_of, obj_hi_of in Ha. cbn [ob_base ob_lo ob_hi O_pck] in Ha. rewrite !soff_lit_small in Ha by lia. rewrite EB, ECH in Ha. cbn [fst snd] in Ha. lia.
      * unfold obj_range, obj_lo_of, obj_hi_of in Ha. cbn [ob_base ob_lo ob_hi O_st] in Ha. rewrite !soff_lit_small in Ha by lia. rewrite ET in Ha. cbn [fst snd] in Ha. lia.
    +
      assert (ELL : soff rhoX LLe = 2 * (rzv / 16 * 2) / 2).
      { destruct (proj1 (Z.mod_divide rzv 16 ltac:(lia)) ltac:(tauto)) as [qr Hqr].
        apply soff_of_val; [|first [clear - Brz Hqr; lia | lia]]. unfold LLe. cbn [eval]. unfold V_RZ. rewrite E150, srl_val, !u64_lit by lia. change (3 mod 64) with 3.
        rewrite Z.shiftr_div_pow2 by lia. rewrite Hqr. replace (qr * 16 / 2 ^ 3) with (2 * qr) by (apply Z.div_unique with 0; lia).
        replace (qr * 16 / 16) with qr by (apply Z.div_unique with 0; lia). first [clear - Hqr Brz; lia | lia]. }
      destruct (proj1 (Z.mod_divide rzv 16 ltac:(lia)) ltac:(tauto)) as [qr Hqr]. rewrite Hqr in ELL.
      replace (qr * 16 / 16) with qr in ELL by (apply Z.div_unique with 0; lia). replace (2 * (qr * 2) / 2) with (2 * qr) in ELL by (apply Z.div_unique with 0; lia).
      assert (SHab : Sh (ab + rzv) = Sh ab + 2 * qr). { rewrite (SHK rzv) by lia. rewrite Hqr. replace (qr * 16 / 8) with (2 * qr) by (apply Z.div_unique with 0; lia). lia. }
      destruct HPI as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]; unfold obj_range, obj_lo_of, obj_hi_of in Ha;
        cbn [ob_base ob_lo ob_hi O_H O_UB O_T O_L O_U O_P O_R] in Ha; rewrite ?soff_lit_small in Ha by lia.
      * rewrite Eab in Ha. rewrite (soff_of_val rhoX (SVar V_RZ) rzv) in Ha by (cbn [eval]; unfold V_RZ; rewrite ?E150; first [apply u64_lit; lia | lia]).
        cbn [fst snd] in Ha. do 3 right. left. lia.
      * rewrite Eub in Ha. rewrite (soff_of_val rhoX (SVar 12) nv) in Ha by (cbn [eval]; rewrite ?E12; first [apply u64_lit; lia | lia]).
        cbn [fst snd] in Ha. do 3 right. left. lia.
      * rewrite Eue in Ha. rewrite (soff_of_val rhoX LTe _ Elt) in Ha by lia. cbn [fst snd] in Ha. do 3 right. left. lia.
      * rewrite Ebsh, ELL in Ha. cbn [fst snd] in Ha. do 4 right. left. rewrite (SHK szc) by lia.
        pose proof (Z.div_le_mono rzv szc 8 ltac:(lia) ltac:(lia)). assert (rzv / 8 = 2 * qr) by (rewrite Hqr; symmetry; apply Z.div_unique with 0; lia). lia.
      * rewrite Ebu in Ha. rewrite (soff_of_val rhoX LUe (nv / 8) Elu) in Ha by (first [clear - Bn Q0; lia | lia]). cbn [fst snd] in Ha. do 4 right. left.
        rewrite SHab in Ha. rewrite (SHK szc) by lia.
        pose proof (Z.div_le_mono (rzv + nv) szc 8 ltac:(lia) ltac:(lia)) as M. rewrite Hqr in M at 1. replace ((qr * 16 + nv) / 8) with (2 * qr + nv / 8) in M by (rewrite <- (Z.div_add_l (2 * qr)) by lia; f_equal; lia).
        lia.
      * rewrite Ebp in Ha. rewrite (soff_of_val rhoX LPe lp Elp) in Ha by (unfold lp; destruct (Z.eq_dec _ _); lia). cbn [fst snd] in Ha. do 4 right. left.
        rewrite SHab in Ha. rewrite (SHK szc) by lia. destruct R8F as (Q81 & Q82 & Q83 & Q84).
        pose proof (Z.div_le_mono (rzv + r8) szc 8 ltac:(lia) ltac:(lia)) as M. rewrite Hqr, Q84 in M. fold lp in M.
        replace ((qr * 16 + (8 * (nv / 8) + (if Z.eq_dec (nv mod 8) 0 then 0 else 8))) / 8) with (2 * qr + nv / 8 + lp) in M.
        2:{ unfold lp. destruct (Z.eq_dec _ _); apply Z.div_unique with 0; lia. }
        unfold lp in *. destruct (Z.eq_dec _ _); lia.
      * rewrite Ebr in Ha. rewrite (soff_of_val rhoX LRe _ Elr) in Ha by (destruct R8F as (Q81 & Q82 & Q83 & Q84); pose proof (Z.div_le_upper_bound (szc - rzv - r8) 8) as DUB8; first [clear - Blr Bsz Brz Bn Q82 Q83 DUB8; lia | lia]).
        cbn [fst snd] in Ha. do 4 right. left. rewrite SHab in Ha. rewrite (SHK szc) by lia. destruct R8F as (Q81 & Q82 & Q83 & Q84).
        assert (Y1 : r8 / 8 + (szc - rzv - r8) / 8 <= (szc - rzv) / 8).
        { apply Z.div_le_lower_bound; [lia|]. pose proof (Z.mul_div_le r8 8 ltac:(lia)). pose proof (Z.mul_div_le (szc - rzv - r8) 8 ltac:(lia)). lia. }
        pose proof (Z.div_le_mono (szc - rzv) szc 8 ltac:(lia) ltac:(lia)) as Y2. pose proof (Z.div_pos r8 8 ltac:(lia) ltac:(lia)) as Y3.
        assert (Y4 : rzv / 8 = 2 * qr) by (rewrite Hqr; symmetry; apply Z.div_unique with 0; lia).
        assert (Y5 : (szc - rzv) / 8 + 2 * qr <= szc / 8).
        { rewrite <- Y4. apply Z.div_le_lower_bound; [lia|]. pose proof (Z.mul_div_le (szc - rzv) 8 ltac:(lia)). pose proof (Z.mul_div_le rzv 8 ltac:(lia)). lia. }
        lia.
  -
    apply andb_prop in Fo as [Fb Fl]. apply sv_eqb_sound in Fb.
    destruct o as [b lo hi cs d]. cbn [ob_base ob_lo ob_hi] in Fb, Fl. subst b.
    pose proof (urange (rw rhoX 10%positive)) as R10. pose proof (srange (rw rhoX V_DEPTH)) as R15.
    do 5 right. unfold obj_range, obj_lo_of, obj_hi_of in Ha. cbn [ob_base ob_lo ob_hi eval] in Ha.
    destruct lo as [lo|i|o1 a1 b1|o1 a1 b1|o1 a1 b1|o1 a1 b1|sg wd a1|l1 i1 k1]; try discriminate Fl.
    +
      apply andb_prop in Fl as [Fl Fl2]. apply Z.leb_le in Fl. apply Z.leb_le in Fl2. cbn [fst snd] in Ha.
      rewrite soff_lit_small in Ha by lia. unfold malloc_depth in DEP. lia.
    + apply andb_prop in Fl as [Fi Fl]. apply Pos.eqb_eq in Fi. subst i. apply sv_eqb_sound in Fl. subst hi. rewrite soff_lit_small in Ha by lia.
      unfold soff in Ha. cbn [eval] in Ha. change 15%positive with V_DEPTH in Ha. cbn [fst snd] in Ha. lia.
Qed.

Definition prim_fitb (n : Z) : bool := ltac2:(tb__ "0|0|
S36S3bSbbVn;A1A1S6S5Vn;Sb6Vn;A1A2Sb5Sb7SbdVn;A1A1A1A2A2").
Lemma prim_fitb_all : ltac2:(tb__ "0|1|
S0S24S3Z1M0R1A2S4R1S5G0Z10000A2A2A2S25S29S58R2A1S2cA3F_;Fn;").
Proof. intros n Hn. apply (forall_rangeZ_ok prim_fitb 1 65536); [|lia]. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma prim_fit : ltac2:(tb__ "0|0|
S0S3Z1R1A2S25S29SbbR2A1S2cA3S3S5R3Sb6R3A1A2Sb5Sb7SbdR3A1A1A1A2F_;F_;Fn;").
Proof.
  intros n Hn HP. destruct (Z_lt_le_dec n (1 + 65536)) as [L|L].
  - pose proof (prim_fitb_all n ltac:(lia)) as H. unfold prim_fitb in H. rewrite HP in H. cbn [negb orb] in H. apply Z.leb_le in H. exact H.
  - exfalso. unfold is_primary, needed, kMaxSize, kChunkHeader2Size in HP. apply Z.leb_le in HP.
    pose proof (round_up_ge8 (Z.max n 16)). unfold rz in HP. rewrite Z.shiftl_mul_pow2 in HP by (unfold rz_log; repeat destruct (_ <=? _); lia).
    assert (0 < 2 ^ rz_log n) by (apply Z.pow_pos_nonneg; [lia | unfold rz_log; repeat destruct (_ <=? _); lia]). lia.
Qed.

Lemma live_user_zone : ltac2:(tb__ "0|2|
Sf4S5aS0S0S0Sd6S5bR4A1A1Sd7R5A1Sd8R7R6A2Sd9R8R7A2S76S2dS0S0A2S32S0S0R7R6A4S64R8A1A3S3Z1R7A2S24S3R9R7A2S4R7S5R9R8A2A2A2S26S24S3S5dS5bRbA1A1M0R8A2S4R8S5S5G0SbcA2Z1000A2A2A2S27S61S61S24S76S61R1S65RcA1A3S24S3S66R1A1M1R9A2S4R9S5G1S67R1A1A2A2A2A2Lch;A2A2F_;F_;F_;F_;F_;F_;F_;Fz;Fn;Fb;FA;Fm;").
Proof.
  intros m A b n z HG HI3 HP HS Hin Hn Hz. destruct HI3 as (_ & LIV3 & _).
  destruct (LIV3 b n Hin) as [EP|(ch & Hch & Eb & Esz)].
  - left. pose proof (primary_cls n ltac:(lia) EP) as Hc. pose proof (prim_fit n ltac:(lia) EP) as FIT. pose proof (rz_bound n) as RZ.
    destruct HP as (_ & _ & _ & P4).
    destruct (P4 _ Hc) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & N1 & N2 & N3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & LV & _).
    destruct (LV b n Hin EP eq_refl) as (R1 & R2 & R3).
    pose proof (geom_nums _ HG) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & S1 & S2 & _).
    pose proof (Size_pos _ Hc) as SP.
    set (c := ClassID (needed n)) in *. clearbody c.
    unfold kUserSpaceSize, kRegionSize, kFreeArraySize, kUserMapSize in *. unfold region_beg, kRegionSize in R1, R3. rewrite kSpaceSize_val.
    nia.
  - right. exists ch. split; [exact Hch|]. destruct HS as (HS1 & _). destruct (In_nth_error _ _ Hch) as (i & Hi).
    destruct (HS1 i ch Hi) as (_ & _ & _ & _ & _ & _ & _ & D8 & _ & _ & D11 & D12 & _).
    assert (RU : forall x, x <= round_up x PG) by (intros x; unfold round_up, PG; pose proof (Z.div_mod (x + 4096 - 1) 4096 ltac:(lia)); pose proof (Z.mod_pos_bound (x + 4096 - 1) 4096 ltac:(lia)); lia).
    pose proof (RU (sc_size ch)). pose proof (round_up_ge8 n). unfold PG in *. lia.
Qed.

Lemma DFP_split : ltac2:(tb__ "0|0|
S62S0ScaR2R1A2S26ScfR2A1Sd0R3R2A2A2F_;Fa;FG;").
Proof. intros G a [H|[H|H]]; [left; exact H | right; right; left; exact H | right; right; right; exact H]. Qed.

Lemma keep_not_DFP : ltac2:(tb__ "0|0|
S5aSeS2aS68Q40A1A1S74S0SdaR5R4R3R2A4S44R6R2A2S28ScaS5cR7A1R3A2A1F_;F_;Fa;Fmd;Ftp;Frho;FA;").
Proof.
  intros A rho tp md a HX HK HD.
  pose proof HX as (HG & HR & HF & HRest & HM & HI3 & HB). destruct HRest as (Hsep & Hlive & HP & HS & _).
  assert (HSEC : forall i ch, nth_error (aa_sec A) i = Some ch -> dyn_in (topG (aa_geom A)) (sc_map_beg ch) (sc_map_size ch)).
  { intros i ch Hi. destruct HS as [X1 _]. destruct (X1 i ch Hi) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & D10 & _). exact D10. }
  assert (HPAB : dyn_ok (topG (aa_geom A)) (ag_pab (aa_geom A)) kPtrArrayReserve) by (destruct HS as (_ & _ & _ & _ & X4 & _); exact X4).
  pose proof (zones_not_DFPw A a HG HI3 HSEC HPAB) as ZN. cbn zeta in ZN.
  pose proof (geom_nums _ HG) as (F1 & F2 & _ & T1 & T2 & _ & C1 & C2 & D1 & D2 & S1 & S2 & _ & TG). unfold HIGH_SHADOW_END in S1.
  assert (GOAL : forall (P : Prop), (P -> ~ DFPw (aa_depot A) a) -> P -> ~ dfp_static a -> False).
  { intros P XP Xp Xns. destruct (DFP_split _ _ HD) as [Hs|Hw]; [exact (Xns Hs) | exact (XP Xp Hw)]. }
  assert (NS : forall lo hi, lo <= a < hi -> (hi <= STORE \/ MAP1 + 8 * MAP1N <= lo) -> ~ dfp_static a).
  { intros lo hi X1 X2 Hs. pose proof (dstat_range a Hs). lia. }
  destruct HK as [HC|HSH].
  - destruct (client_addr_cases CST A a _ HF HC) as [ST|[(b & n & Hbn & Hab)|[FR|[HCa|FL]]]].
    + apply (GOAL (topG (aa_geom A) <= a)); [intros H; apply ZN; do 9 right; exact H | lia | apply (NS (topG (aa_geom A)) (2 ^ 47)); [lia | unfold MAP1, MAP1N; lia]].
    + destruct (Hsep b n Hbn) as (N1 & _).
      destruct (live_user_zone _ A b n a HG HI3 HP HS Hbn N1 Hab) as [SP|(ch & Hch & Hz)].
      * apply (GOAL _ (fun H => ZN (or_intror (or_introl H))) SP). eapply NS; [exact SP | unfold MAP1, MAP1N; lia].
      * apply (GOAL (exists ch, In ch (aa_sec A) /\ sc_map_beg ch <= a < sc_map_beg ch + sc_map_size ch)).
        -- intros H. apply ZN. do 7 right. left. exact H.
        -- exists ch. exact (conj Hch Hz).
        -- destruct (In_nth_error _ _ Hch) as (i & Hi). destruct HS as [X1 _]. destruct (X1 i ch Hi) as (_ & _ & _ & _ & _ & _ & _ & D8 & D9 & D10 & _).
           pose proof (dyn_in_big _ _ _ D10 ltac:(unfold PG in D8; lia)) as CB. eapply NS; [exact Hz | unfold IMG_HI in CB; unfold MAP1, MAP1N; lia].
    + destruct FR as (c & p & Hc & Hp & _ & Hx). pose proof (fs_geom_nums (aa_geom A) c p HG Hc Hp) as M. cbn zeta in M. rewrite FS_frames_off_val, FS_kFlagsOffset_val in M.
      apply (GOAL (ag_fsb (aa_geom A) <= a < ag_fsb (aa_geom A) + FS_total)); [intros H; apply ZN; do 5 right; left; exact H | lia |].
      eapply NS; [exact Hx | unfold IMG_HI in M; unfold MAP1, MAP1N; lia].
    + destruct (HCST _ HCa) as [X _]. apply (GOAL (IMG_LO <= a < IMG_HI /\ ~ dstatw a)); [intros H; apply ZN; left; exact H | | exact (HCSTD a HCa)].
      split; [exact X|]. intros [Hs _]. exact (HCSTD a HCa Hs).
    + destruct FL as (c & p & Hc & Hp & _ & Ex). pose proof (fs_geom_nums (aa_geom A) c p HG Hc Hp) as M. cbn zeta in M. rewrite FS_frames_off_val, FS_kFlagsOffset_val in M. rewrite <- Ex in M.
      apply (GOAL (ag_fsb (aa_geom A) <= a < ag_fsb (aa_geom A) + FS_total)); [intros H; apply ZN; do 5 right; left; exact H | lia |].
      apply (NS a (a + 1)); [lia | unfold IMG_HI in M; unfold MAP1, MAP1N; lia].
  - pose proof (client_shadow_bounds CST XGL HCST HXGL A a _ HG HF Hsep HSH) as B. unfold SHADOW_OFF, HIGH_SHADOW_END in B.
    apply (GOAL (SHADOW_BAND_LO <= a < SHADOW_BAND_HI)); [intros H; apply ZN; do 8 right; left; exact H | |];
      unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END; [lia|].
    eapply NS; [split; [apply Z.le_refl | apply Z.lt_succ_diag_r] | unfold MAP1, MAP1N; lia].
Qed.

Lemma zoneR_not_DFP : ltac2:(tb__ "0|0|
S5aSeS2aS68Q40A1A1S74S0S0S0SdaR7R6R5R4A4S5bR8A1S63S3S5dR1A1R5A2S3S5R6R5A2S5S5dR2A1SbcA2A2S3Z0R6A2S4S5R8R7A2S8Z2Z2fA2A2S4eS5fR5A1S5eR5A1S5dR5A1R9R8S60R5A1R7A7S28ScaS5cReA1R8A2A1F_;F_;F_;F_;F_;TG;F_;Fa;Fszc;Fab;Fmd;Ftp;Frho;FA;").
Proof.
  intros A rho tp md ab szc a HX G Hab1 Hab2 Hsz Hab3 HZ HD. subst G.
  pose proof HX as (HG & HR & HF & HRest & HM & HI3 & HB). destruct HRest as (Hsep & Hlive & HP & HS & _).
  assert (HSEC : forall i ch, nth_error (aa_sec A) i = Some ch -> dyn_in (topG (aa_geom A)) (sc_map_beg ch) (sc_map_size ch)).
  { intros i ch Hi. destruct HS as [X1 _]. destruct (X1 i ch Hi) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & D10 & _). exact D10. }
  assert (HPAB : dyn_ok (topG (aa_geom A)) (ag_pab (aa_geom A)) kPtrArrayReserve) by (destruct HS as (_ & _ & _ & _ & X4 & _); exact X4).
  pose proof (zones_not_DFPw A a HG HI3 HSEC HPAB) as ZN. cbn zeta in ZN.
  pose proof (geom_nums _ HG) as (F1 & F2 & _ & T1 & T2 & _ & C1 & C2 & D1 & D2 & S1 & S2 & _ & TG). unfold HIGH_SHADOW_END in S1. rewrite kSpaceSize_val in S2, Hab2.
  pose proof (geom_bands _ HG) as (_ & _ & _ & _ & TI & CI & _). unfold IMG_LO, IMG_HI in TI, CI.
  assert (GOAL : forall (P : Prop), (P -> ~ DFPw (aa_depot A) a) -> P -> ~ dfp_static a -> False).
  { intros P XP Xp Xns. destruct (DFP_split _ _ HD) as [Hs|Hw]; [exact (Xns Hs) | exact (XP Xp Hw)]. }
  assert (NS : forall lo hi, lo <= a < hi -> (hi <= STORE \/ MAP1 + 8 * MAP1N <= lo) -> ~ dfp_static a).
  { intros lo hi X1 X2 Hs. pose proof (dstat_range a Hs). lia. }
  destruct HZ as [[Z1 Z2]|[ZT|[ZC|[ZA|[ZS|ZK]]]]].
  - apply (GOAL (IMG_LO <= a < IMG_HI /\ ~ dstatw a)); [intros H; apply ZN; left; exact H | |].
    + split; [exact Z1|]. intros [Hs _]. pose proof (dstat_range a Hs). lia.
    + intros Hs. pose proof (dstat_range a Hs). lia.
  - apply (GOAL _ (fun H => ZN (or_intror (or_intror (or_introl H)))) ZT). eapply NS; [exact ZT | unfold STORE, MAP1, MAP1N; lia].
  - apply (GOAL _ (fun H => ZN (or_intror (or_intror (or_intror (or_introl H))))) ZC). eapply NS; [exact ZC | unfold STORE, MAP1, MAP1N; lia].
  - apply (GOAL (ag_spacebeg (aa_geom A) <= a < ag_spacebeg (aa_geom A) + kSpaceSize + 4096)); [intros H; apply ZN; right; left; exact H | rewrite kSpaceSize_val; lia |].
    apply (NS (ag_spacebeg (aa_geom A)) (a + 1)); [lia | unfold MAP1, MAP1N; lia].
  - pose proof (Sh_in_band ab ltac:(lia)) as B1. pose proof (Sh_in_band (ab + szc) ltac:(lia)) as B2.
    apply (GOAL (SHADOW_BAND_LO <= a < SHADOW_BAND_HI)); [intros H; apply ZN; do 8 right; left; exact H | lia |].
    apply (NS SHADOW_BAND_LO (a + 1)); [lia | unfold SHADOW_BAND_LO, LOW_SHADOW_BEG, MAP1, MAP1N; lia].
  - apply (GOAL (topG (aa_geom A) <= a)); [intros H; apply ZN; do 9 right; exact H | exact ZK |].
    apply (NS (topG (aa_geom A)) (a + 1)); [lia | unfold MAP1, MAP1N; lia].
Qed.

Lemma SPA_updR : ltac2:(tb__ "0|5|
S71SeS3dS0S2aS2dS30ScA2A1S2aS68Q40A1A1S91S2aS2dScScA2A1M0S2aSfA1M1S25S29S22S3cS86VW;Vst;Vtmax;R7R6R5S31SdA1M2S2bS31SfA1M3A9A1A1S2cA3S25S2fS2dG0G1A2M4A1Se1S3cR8A1S3cS86VW;Vst;Vtmax;R8R7R6G2S2bG3A9A1A2S37G4S32G0G1R3R2A4A2A3Se2RaR4A2Sa9SfS1cRbA1R4A3S6fVsegs;RdRbRcR8R7A6S6fVsegs;ReS86VW;Vst;Vtmax;RcRbRaG2S2bG3A9RdR9R8A6F_;F_;F_;F_;F_;Fnf;Fd;Fw;FtpY;Fru;Fpc;FE;FrhoY;FJx;").
Proof. intros Jx rhoY E pc ru tpY w d nf Hw Hd Hok Hnf HE. unfold CertCallocSP.upd. eapply SPA_restate; [exact Hw | exact Hd | reflexivity | exact Hok | exact Hnf | exact HE]. Qed.

Definition site_facts (A : AA) (rho rhoE : valuation) (sz : Z) : Prop := ltac2:(tb__ "0|9|
S24S24S3Z1M0Vsz;A2S3Vsz;Vtmax;A2A2S24S3S6bQ40M1S10VrhoE;S99A2A2M2S9S9aA1A2S24Sd6S5bVA;A1M3A1S24S25S68G1A1M4S10VrhoE;PcM5A2M6S10Vrho;G5A2A3S24S69G1G6A2S0S24SebVrhoE;S5dG3A1Sd2R1A1M7Sd3VA;R1A2Sb6R1A1Sb5G7A1R1A7S24S24S3G0Sd4VA;R1A2M8A2S3G8Z10A2A2S25G4S10VrhoE;P95A2S6aG1G8A2A3A2A2Tnv;S24S25G4S10VrhoE;P97A2S6aG1S5fG3A1A2A3S24S25G4S10VrhoE;P98A2S6aG1S5eG3A1A2A3S3S60G3A1S5S69G1S10VrhoE;PaA2A2G2A2A2A2A2A2A2A2A2A2").

Lemma dc_facts : ltac2:(tb__ "0|1|
S5aS97SeSeS2aS68Q40M0A1A1S91S6fVsegs;Sa5VW;Vst;R6R5R4A5S84VW;Vst;Vtmax;A3R3R2R1A6S43R7R5R4S69G0S10R4Pc0A2A2A4F_;Fw;Ftp;FrhoE;Frho;FKc;FA;").
Proof.
  intros A Kc rho rhoE tp w Hw. destruct w as [tr [ms md]].
  pose proof (proj2 Hw) as [Hag HJ]. cbn [w_tr w_cfg cfg_model fst snd] in Hag, HJ.
  pose proof Hag as (Hagw & Hagl & Hagm).
  pose proof HJ as (HA & HK & Htp & HU & HB & HN & Htop). cbn [eval] in HN, HB. unfold top_high in Htop.
  pose proof (JG_rigid 0%nat st A Kc rho rhoE tp tr md (proj2 Hw)) as (E12 & E148 & E149 & E150 & E158 & E159).
  assert (FACT : forall p, In p (ss_facts (ax_S (E4d W st tmax))) -> holds rhoE p).
  { intros p Hp. exact (fact_of_state 0%nat st A Kc rho rhoE tp _ _ p Hw Hp). }
  pose proof (FACT _ (F192 _ (or_introl eq_refl))) as Fs1. pose proof (FACT _ (F192 _ (or_intror (or_introl eq_refl)))) as Fs2.
  cbn [holds eval] in Fs1, Fs2. rewrite u64_lit in Fs1 by lia. rewrite u64_lit in Fs2 by (unfold SZMAX in Htmax; lia).
  pose proof (FACT _ (FDEP _ ltac:(unfold pre_facts, F_depth; cbn [app]; do 2 right; left; reflexivity))) as Fd1.
  cbn [holds eval branch_taken] in Fd1. unfold bv_lts in Fd1. apply negb_true_iff in Fd1. apply Z.ltb_ge in Fd1.
  change (bv_signed (Z_to_bv 64 (- malloc_depth))) with (- malloc_depth) in Fd1.
  pose proof (proj1 HA) as HG.
  assert (E151 : rw rhoE 151%positive = Z_to_bv 64 (ag_thread (aa_geom A))). { rewrite <- (Hagw 151%positive) by (unfold GW; lia). reflexivity. }
  assert (E152 : rw rhoE 152%positive = Z_to_bv 64 (ag_ctx (aa_geom A))). { rewrite <- (Hagw 152%positive) by (unfold GW; lia). reflexivity. }
  pose proof (cnt_pos_of_fact 0%nat st A Kc rho rhoE tp _ _ Hw YP4) as Hcnt.
  pose proof (JGb_pvals 0%nat st A Kc rho rhoE tp _ _ (conj (proj1 Hw) (JG_JGb 0%nat st A Kc rho rhoE tp tr md (proj2 Hw))) FGEN4 Hcnt) as PV.
  cbn zeta in PV. rewrite <- E12 in PV, Hcnt, E149.
  pose proof PV as (_ & _ & _ & _ & _ & _ & Bn & _).
  assert (Hcnt16 : 1 <= cnt_of A (bv_unsigned (rw rhoE 12%positive)) <= 16).
  { split; [exact Hcnt|]. pose proof (pc_entry_facts segs A rhoE tp md _ HA Bn Hcnt) as PF. cbn zeta in PF. destruct PF as (_ & _ & _ & _ & X & _). exact X. }
  split; [lia|]. split; [exact Fd1|]. split; [exact HG|]. split; [exact E12|]. split; [exact (conj PV (conj Hcnt16 E149))|].
  split; [exact E151|]. split; [exact E152 | exact Htop].
Qed.

Lemma dc_site : ltac2:(tb__ "0|1|
S5aS97SeSeS2aS68Q40M0A1A1S91S6fVsegs;Sa5VW;Vst;R6R5R4A5S84VW;Vst;Vtmax;A3R3R2R1A6S6fVsegs;Sa5VW;Vst;R7R6R5A5S41S69G0S10R4Pc0A2A2A1R4R3R2A6F_;Fw;Ftp;FrhoE;Frho;FKc;FA;").
Proof.
  intros A Kc rho rhoE tp w Hw. pose proof (dc_facts A Kc rho rhoE tp w Hw) as (Hsz & Fd1 & HG & E12 & _ & _ & _ & Htop).
  set (sz := bv_unsigned (rw rhoE 192%positive)) in *. destruct w as [tr [ms md]].
  pose proof (urange (rw rhoE 10%positive)) as R10. pose proof (topG_range (aa_geom A)) as TG. unfold malloc_depth in Fd1.

  assert (Em3808 : bv_unsigned (eval rhoE (SAlu ALU_ADD (SVar 10) (SLit (-3856)))) = bv_unsigned (rw rhoE 10%positive) - 3856).
  { cbn [eval]. rewrite add_val. replace (bv_unsigned (Z_to_bv 64 (-3856))) with (2 ^ 64 - 3856) by reflexivity.
    rewrite <- (Z.mod_add _ (-1)) by lia. rewrite Z.mod_small by lia. lia. }
  assert (Em2112 : bv_unsigned (eval rhoE (SAlu ALU_ADD (SVar 10) (SLit (-2120)))) = bv_unsigned (rw rhoE 10%positive) - 2120).
  { cbn [eval]. rewrite add_val. replace (bv_unsigned (Z_to_bv 64 (-2120))) with (2 ^ 64 - 2120) by reflexivity.
    rewrite <- (Z.mod_add _ (-1)) by lia. rewrite Z.mod_small by lia. lia. }
  assert (HwF : SPA segs (JG W st A Kc rho) X4f rhoE tp (tr, mkCfg ms md)).
  { split; [|exact (proj2 Hw)]. unfold X4f. apply (smatchA_add_facts segs rhoE tp F_call _ _ (proj1 Hw)); [|exact FBE]. unfold F_call.
    repeat apply Forall_cons; try apply Forall_nil; cbn [holds]; rewrite ?Em3808, ?Em2112; cbn [eval]; rewrite ?u64_lit by lia; lia. }

  assert (HwR : SPA segs (JG W st A Kc rho) (X4r sz) rhoE tp (tr, mkCfg ms md)).
  { unfold X4r. eapply SPA_updR; [exact (WX4r sz Hsz) | exact (DX4r sz Hsz) | | constructor | exact HwF].
    unfold diffs_ok. apply Forall_cons; [|apply Forall_nil]. cbn [fst snd eval].
    apply bv_eq. change 32%N with (8 * N.of_nat 4)%N. rewrite ext_low_false_unsigned by lia. rewrite u64_lit by (unfold SZMAX in Htmax; lia).
    change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32). rewrite Z.mod_small by (unfold SZMAX in Htmax; lia). reflexivity. }

  assert (OS : forall (Jx : jpredA) X i mid, isSome (split_obj_at (ax_S X) i mid) = true ->
            SPA segs Jx X rhoE tp (tr, mkCfg ms md) -> SPA segs Jx (osplit X i mid) rhoE tp (tr, mkCfg ms md)).
  { intros Jx X i mid Hs HX. unfold osplit. destruct (split_obj_at (ax_S X) i mid) as [S'|] eqn:E; [|exact HX]. eapply (SPA_split segs); [exact E | exact HX]. }
  unfold X4. apply OS; [exact (SPL4 sz Hsz)|]. unfold X4c. apply OS; [exact (SPL3 sz Hsz)|]. unfold X4b. apply OS; [exact (SPL2 sz Hsz)|].
  unfold X4a. apply OS; [exact (SPL1 sz Hsz)| exact HwR].
Qed.

Lemma dc_R4 : ltac2:(tb__ "0|2|
S5aSeSeS0S43R4R3R2R1A4S5aSeS2aS68Q40M0A1M1A1S74G1SdaR5R4R3R2A4S25S63S5bR6A1S5bRbA1A3Sa2RaVR4;R9A1R3A3S28ScaS5cR8A1S69G0R4A2A2A1F_;F_;F_;Fa;Fmdx;Ftpx;Frx;FAx;F_;Fsz;FrhoE;Frho;FA;").
Proof.
  intros A rho rhoE sz (Hsz & Fd1 & HG & E12 & (PV & Hcnt16 & E149) & E151 & E152 & Htop) Ax rx tpx mdx a HX EG (o & Ho & Hoa) HD.
  cbn zeta in PV. pose proof PV as (_ & _ & _ & _ & _ & _ & Bn & Bsz & Brz & Bfit & BSB & Bc & Bx & Btop).
  pose proof (R4_zone sz rhoE A o (bv_unsigned a) Hsz PV Hcnt16 E151 E152 E149 HG Htop Fd1 Ho Hoa) as HZ. cbn zeta in HZ. rewrite <- EG in HZ.
  refine (zoneR_not_DFP Ax rx tpx mdx _ _ (bv_unsigned a) HX _ _ _ _ HZ HD); rewrite ?EG; rewrite ?kSpaceSize_val; lia.
Qed.

Lemma dc_entry : ltac2:(tb__ "0|1|
S5aS97SeSeS2aS68Q40A1A1S0S2aS75A1M0S7aS74S43R9R7R6R4A4S98R9A1S70Vsegs;R8R7S41R6A1S32G0S8eR5S8fR4R3A2A4A5Sa5VW;Vst;RcRbRaR9R8R6R4A9Sd1SbeSb4RdRcRaA3S5cRdA1Sa0S9fRaVR4;R8A1S83R5R9R6A3A3Vs4;R8A1A2R9R7R5A7F_;F_;F_;F_;Fmd0;Fms0;Ftr0;Fsz;Ftp;FrhoE;Frho;FKc;FA;").
Proof.
  intros A Kc rho rhoE tp sz tr0 ms0 md0 SF HKc Hsm0 [Hag0 HJ0].
  pose proof SF as (Hsz & Fd1 & HG & E12 & (PV & Hcnt16 & E149) & E151 & E152 & Htop). unfold malloc_depth in Fd1.
  pose proof HJ0 as (HA0 & HK0 & _ & _ & HB0 & HN0 & _). cbn [eval] in HB0, HN0.
  pose proof (AInvA_budget A rhoE tp md0 HA0) as (_ & _ & _ & HKm0 & _).
  pose proof (urange (rw rhoE 10%positive)) as R10. pose proof (topG_range (aa_geom A)) as TG.
  assert (Em2272 : bv_unsigned (eval rhoE (SAlu ALU_ADD (SVar 10) (SLit (-2320)))) = bv_unsigned (rw rhoE 10%positive) - 2320).
  { cbn [eval]. rewrite add_val. replace (bv_unsigned (Z_to_bv 64 (-2320))) with (2 ^ 64 - 2320) by reflexivity.
    rewrite <- (Z.mod_add _ (-1)) by lia. rewrite Z.mod_small by lia. lia. }
  assert (Em2112 : bv_unsigned (eval rhoE (SAlu ALU_ADD (SVar 10) (SLit (-2120)))) = bv_unsigned (rw rhoE 10%positive) - 2120).
  { cbn [eval]. rewrite add_val. replace (bv_unsigned (Z_to_bv 64 (-2120))) with (2 ^ 64 - 2120) by reflexivity.
    rewrite <- (Z.mod_add _ (-1)) by lia. rewrite Z.mod_small by lia. lia. }
  split.
  - apply (KD_intro A Kc rhoE _ HB0 HKm0 tp tr0 md0 HA0 HK0). unfold TOPr, V_DEPTH. cbn [rw rho_sub rho_absorb].
    rewrite (WG10 sz Hsz), (WG15 sz Hsz), (WG12 sz Hsz), !eval_absorb, Em2272, Em2112.
    change (bv_signed (eval rhoE (SLit (-1536)))) with (-1536). lia.
  - destruct (AInvA_X A rhoE tp md0 HA0) as (HX0 & HD0 & _).
    apply (depot_inv_frame segsA (aa_depot A) rhoE _ md0 tp); [|exact HD0]. intros a Ha. apply view_agree. intros Hr.
    apply rm_absorb_out. intros Hin. apply (dc_R4 A rho rhoE sz SF A rhoE tp md0 _ HX0 eq_refl Hin). rewrite u64_lit by exact Hr. exact Ha.
Qed.

Lemma dc_exit_ok : ltac2:(tb__ "0|2|
S5aS97SeSeS2aS68Q40A1A1M0S0S2aS75A1M1S7aS74SeG0G1S7aS74S43ReRcRbR9A4S98ReA1ScbSbeSb4R10RfRdA3S5cR10A1A3SafSa0S9fReVR4;RcA1S83R9RdRaA3A3Vs4;RcA1A2SeS70Vsegs;RfReS41RdA1S32G1S8eRcS8fRbRaA2A4A5Sa5VW;Vst;R13R12R11R10RfRdRbA9SbfS16S3cS6dRfA1A1A1R3RbA3S70Vsegs;RcRbS6cR10A1S32G1S8eRaS8fR9R8A2A4A5R6R5R12RdRcRbR9A6Sb1R14S83RfR13R10A3VR4;R12A1Vs4;R12A1S6dR12A1S6cR12A1S41R12A1ReA8F_;F_;F_;F_;F_;TrhoC;TJL;F_;F_;Fmd';Fms';Ftr';FtpL;FrhoL;Fmd0;Fms0;Ftr0;Fsz;Ftp;FrhoE;Frho;FKc;FA;").
Proof.
  intros A Kc rho rhoE tp sz tr0 ms0 md0 rhoL tpL tr' ms' md' SF HKc JL rhoC Hsm0 [Hag0 HJ0] HagL HsmL HJL.
  pose proof SF as (Hsz & _). subst JL.
  destruct HJL as (G' & HKD' & HDI' & Hdpost & HRM & HVW & HRL & (l0 & EtpL)).
  split; [split|split].
  - intros a Hin. apply HRM. pose proof HKD' as (HXK & _). exact (dc_R4 A rho rhoE sz SF _ rhoE tpL md' a HXK eq_refl Hin).
  - intros o' oR Ho' HoR. rewrite (NEWO sz Hsz) in Ho'. destruct Ho'.
  - intros r a j oR Hr. rewrite (XPost sz) in Hr. destruct Hr.
  - intros r a j Hr. rewrite (XX4 sz Hsz) in Hr. destruct Hr.
Qed.

Lemma dc_exit_core : ltac2:(tb__ "0|2|
S5aS97SeSeS2aS68Q40A1A1M0S0S2aS75A1M1S7aS74SeG0G1S7aS74S43ReRcRbR9A4S98ReA1ScbSbeSb4R10RfRdA3S5cR10A1A3SafSa0S9fReVR4;RcA1S83R9RdRaA3A3Vs4;RcA1A2SeS70Vsegs;RfReS41RdA1S32G1S8eRcS8fRbRaA2A4A5Sa5VW;Vst;R13R12R11R10RfRdRbA9SbfS16S3cS6dRfA1A1A1R3RbA3S70Vsegs;RcRbS6cR10A1S32G1S8eRaS8fR9R8A2A4A5R6R5R12RdRcRbR9A6SeS91Sc0R16S83R11R15R12A3VR4;R14A1Vs4;R14A1S3cS6dR14A1A1S3cS41R14A1A1S3cS6cR14A1A1R2R10A9S6fVsegs;Sb0RaR9R16R11R10A5SaeVs4;R15A1S6dR15A1S6cR15A1S41R15A1VR4;R15A1A5R3R10R2A6S27S5aS5aS27SeSeS27SeSeS24SdeR1eR3A2S24SdfS44R1eA1R1cR2A3S6fVsegs;SddVW;Vst;R3R1dR2A5S85VW;Vst;Vtmax;A3R1R14R6A6A2A2LrhoX;A2Lrho'';A2LA';A2F_;F_;Fw';Frho';F_;F_;F_;F_;F_;TrhoC;TJL;F_;F_;Fmd';Fms';Ftr';FtpL;FrhoL;Fmd0;Fms0;Ftr0;Fsz;Ftp;FrhoE;Frho;FKc;FA;").
Proof.
  intros A Kc rho rhoE tp sz tr0 ms0 md0 rhoL tpL tr' ms' md' SF HKc JL rhoC Hsm0 [Hag0 HJ0] HagL HsmL HJL rho' w' HLK [Hsm' HJ'].
  pose proof SF as (Hsz & Fd1 & HG & E12 & (PV & Hcnt16 & E149) & E151 & E152 & Htop).
  pose proof Hag0 as (Hagw & Hagl & Hagm).
  pose proof HJ0 as (HA0 & HK0 & Htp0 & HU0 & _ & HN0 & Htop0). cbn [eval] in HN0. unfold top_high in Htop0.
  pose proof (HER sz Hsz) as ER. pose proof (HT4 sz Hsz) as ET4.
  subst JL.
  destruct (entails_frA_sound segs (X4 sz) (PreD sz) (s4 sz) (R4 sz) rhoE tp tr0 ms0 md0 ER Hsm0) as (_ & _ & _ & HwfR & HinR).
  destruct w' as [tr2 [ms2 md2]]. cbn [w_tr w_cfg cfg_model fst snd] in HJ'.
  pose proof HJ' as HJc. unfold J_ofPA in HJ'.
  destruct HJ' as (G2 & HKD2 & HDI2 & Hdpost2 & HRM2 & HVW2 & HRL2 & (l2 & EtpL2)).
  pose proof HKD2 as (HX2 & HK2 & HL2 & HT2).
  pose proof HLK as (Hag' & Hrm' & HagL' & Hlink').
  rewrite ET4 in Hsm'.
  assert (NXlt : forall i, (i < GW)%positive -> (i < ss_next (ax_S (X4 sz)))%positive).
  { intros i Hi. eapply Pos.lt_le_trans; [exact Hi|]. rewrite (NX4 sz Hsz). apply Pos.leb_le. exact NXE. }

  assert (HF4 : Forall (holds rho') (ss_facts (ax_S (X4 sz)))).
  { pose proof (proj1 Hsm0) as HsmX. pose proof HsmX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hfacts4).
    apply Forall_forall. intros p Hp.
    exact (proj1 (holds_agree_vals _ rhoE rho' p Hag' (proj1 (forallb_forall _ _) (FBX4 sz Hsz) p Hp)) (proj1 (Forall_forall _ _) Hfacts4 p Hp)). }
  assert (HT40 : SPA segs (J_ofPA (JLD segsA (KD A Kc rhoE) (aa_depot A)) (rho_sub (rho_absorb rhoE (R4 sz) (vms md0 tp ms0)) (s4 sz)) tp rhoL tpL) (T40 sz) rho' tpL (tr2, mkCfg ms2 md2)).
  { unfold T40. apply (SPA_refacts segs); [exact (conj Hsm' HJc) | exact (FBT4 sz Hsz) | intros _; exact HF4]. }

  assert (AXr : forall X i, ax_X (oreb X i) = ax_X X) by (intros X i; unfold oreb; destruct (rebase_obj_at _ _); reflexivity).
  assert (AXm : forall X i, ax_X (omrg X i) = ax_X X) by (intros X i; unfold omrg; destruct (merge_objs_at _ _); reflexivity).
  assert (AX40 : ax_X (T40 sz) = []) by (unfold T40, ax_with_facts; cbn [ax_X ax_setS]; exact (XT4 sz Hsz)).
  assert (OR : forall (Jx : jpredA) X i, isSome (rebase_obj_at (ax_S X) i) = true -> ax_X X = [] ->
            SPA segs Jx X rho' tpL (tr2, mkCfg ms2 md2) -> SPA segs Jx (oreb X i) rho' tpL (tr2, mkCfg ms2 md2)).
  { intros Jx X i Hs HX0 HX. unfold oreb. destruct (rebase_obj_at (ax_S X) i) as [S'|] eqn:E; [|exact HX]. eapply (SPA_rebase segs); [exact E | exact HX0 | exact HX]. }
  assert (OM : forall (Jx : jpredA) X i, isSome (merge_objs_at (ax_S X) i) = true ->
            SPA segs Jx X rho' tpL (tr2, mkCfg ms2 md2) -> SPA segs Jx (omrg X i) rho' tpL (tr2, mkCfg ms2 md2)).
  { intros Jx X i Hs HX. unfold omrg. destruct (merge_objs_at (ax_S X) i) as [S'|] eqn:E; [|exact HX]. eapply (SPA_merge segs); [exact E | exact HX]. }
  match type of HT40 with SPA _ ?Jx _ _ _ _ => set (JP := Jx) in HT40 end.
  assert (HT4b : SPA segs JP (T4b sz) rho' tpL (tr2, mkCfg ms2 md2)).
  { unfold T4b. apply OR; [exact (RB2 sz Hsz) | unfold T4a; rewrite AXr; exact AX40 |]. unfold T4a. apply OR; [exact (RB1 sz Hsz) | exact AX40 | exact HT40]. }

  assert (PERM_lt : forallb (fun i => Nat.ltb i 48) perm4 = true) by reflexivity.
  assert (PERM_cov : forallb (fun i => existsb (Nat.eqb i) perm4) (seq 0 48) = true) by reflexivity.
  assert (HT4c : SPA segs JP (T4c sz) rho' tpL (tr2, mkCfg ms2 md2)).
  { unfold T4c. apply (SPA_select segs); [exact HT4b | exact PERM_nd | |].
    - intros i Hi. rewrite (PERM_len sz Hsz). apply Nat.ltb_lt. exact (proj1 (forallb_forall _ _) PERM_lt i Hi).
    - intros i Hi. rewrite (PERM_len sz Hsz) in Hi. pose proof (proj1 (forallb_forall _ _) PERM_cov i ltac:(apply in_seq; lia)) as X.
      apply existsb_exists in X as (j & Hj & E). apply Nat.eqb_eq in E. subst j. exact Hj. }

  assert (HT4d : SPA segs JP (T4d sz) rho' tpL (tr2, mkCfg ms2 md2)).
  { unfold T4d. apply OM; [exact (MRG4 sz Hsz)|]. unfold T4m3. apply OM; [exact (MRG3 sz Hsz)|]. unfold T4m2. apply OM; [exact (MRG2 sz Hsz)|].
    unfold T4m1. apply OM; [exact (MRG1 sz Hsz)| exact HT4c]. }
  assert (AX4d : ax_X (T4d sz) = []).
  { unfold T4d, T4m3, T4m2, T4m1. rewrite !AXm. unfold T4c. cbn [ax_X ax_setS]. unfold T4b, T4a. rewrite !AXr. exact AX40. }
  clear HT40 HT4b HT4c OR OM.

  assert (RNG : forall o, In o (R4 sz) -> obj_range rho' o = obj_range rhoE o).
  { intros o Ho. apply (obj_range_agree_vals (ss_next (ax_S (X4 sz)))); [exact Hag' | exact (proj1 (forallb_forall _ _) HwfR o Ho)]. }
  set (A' := bumpK (with_depot A G2)).
  set (rho5 := rho_absorb rho' (R4 sz) (ms_with_mem ms2 (rm rhoE))).
  set (rho'' := mkVal (rw rho) (rl rho) (rm rho5)).
  assert (RM5 : forall a, rm rho5 a = if in_ranges_dec rho' (R4 sz) a then rm rhoE a else rm rhoL a).
  { intros a. unfold rho5, rho_absorb, ms_with_mem. cbn [rm ms_mem]. rewrite Hrm'. reflexivity. }
  assert (IRE : forall a, in_ranges rho' (R4 sz) a <-> in_ranges rhoE (R4 sz) a).
  { intros a. split; intros (o & Ho & Hoa); exists o; [rewrite <- (RNG o Ho) | rewrite (RNG o Ho)]; exact (conj Ho Hoa). }
  assert (R4DFP : forall a, in_ranges rhoE (R4 sz) a -> ~ DFP G2 (bv_unsigned a)).
  { intros a Hin. exact (dc_R4 A rho rhoE sz SF A' rhoE tpL md2 a HX2 eq_refl Hin). }
  assert (KEY : forall a, ~ DFP G2 (bv_unsigned a) -> rm rho5 a = rm rhoE a).
  { intros a Ha. rewrite RM5. destruct (in_ranges_dec rho' (R4 sz) a) as [Hi|Hn]; [reflexivity|].
    rewrite (HRM2 a Ha). apply rm_absorb_out. intros Hi. exact (Hn (proj2 (IRE a) Hi)). }
  assert (KEYin : forall a, in_ranges rhoE (R4 sz) a -> rm rho5 a = rm rhoE a).
  { intros a Hi. rewrite RM5. destruct (in_ranges_dec rho' (R4 sz) a) as [|Hn]; [reflexivity|]. exfalso. exact (Hn (proj2 (IRE a) Hi)). }
  assert (BAND : forall Ax rx tpx mdx a, AInvX Ax rx tpx mdx -> SHADOW_BAND_LO <= a < SHADOW_BAND_HI -> ~ DFP (aa_depot Ax) a).
  { intros Ax rx tpx mdx a HX HB' HD. pose proof HX as (HGx & _ & _ & HRest & _ & HI3x & _). destruct HRest as (_ & _ & _ & HSx & _).
    assert (HSEC : forall i ch, nth_error (aa_sec Ax) i = Some ch -> dyn_in (topG (aa_geom Ax)) (sc_map_beg ch) (sc_map_size ch)).
    { intros i ch Hi. destruct HSx as [X1 _]. destruct (X1 i ch Hi) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & D10 & _). exact D10. }
    assert (HPAB : dyn_ok (topG (aa_geom Ax)) (ag_pab (aa_geom Ax)) kPtrArrayReserve) by (destruct HSx as (_ & _ & _ & _ & X4' & _); exact X4').
    pose proof (zones_not_DFPw Ax a HGx HI3x HSEC HPAB) as ZN. cbn zeta in ZN.
    destruct (DFP_split _ _ HD) as [Hs|Hws]; [pose proof (dstat_range a Hs) as DR; unfold SHADOW_BAND_LO, LOW_SHADOW_BEG in HB'; unfold MAP1, MAP1N, STORE in DR; clear -HB' DR; lia | ].
    apply ZN; [do 8 right; left; exact HB' | exact Hws]. }

  assert (HX5 : AInvX A' rho5 tpL md2).
  { apply (AInvX_frameV A' rhoE rho5 tpL md2 HX2). intros z Hz. change (aa_depot A') with G2 in Hz.
    destruct (in_ranges_dec rhoE (R4 sz) (Z_to_bv 64 z)) as [Hi|Hn].
    - apply view_agree. intros _. apply KEYin. exact Hi.
    - transitivity (view segs (rm rhoL) z).
      + apply view_agree. intros Hr. rewrite RM5. destruct (in_ranges_dec rho' (R4 sz) (Z_to_bv 64 z)) as [Hi'|]; [exfalso; exact (Hn (proj1 (IRE _) Hi')) | reflexivity].
      + exact (eq_trans (HVW2 z Hz) (view_agree _ _ z (fun _ => rm_absorb_out _ _ _ _ Hn))). }
  assert (HDI5 : depot_inv segsA G2 rho5 md2 tpL).
  { apply (depot_inv_frame segsA G2 rhoL rho5 md2 tpL); [|exact HDI2]. intros a Ha. apply view_agree. intros Hr. rewrite RM5.
    destruct (in_ranges_dec rho' (R4 sz) (Z_to_bv 64 a)) as [Hi|]; [|reflexivity]. exfalso.
    apply (R4DFP (Z_to_bv 64 a) (proj1 (IRE _) Hi)). rewrite u64_lit by exact Hr. exact Ha. }
  assert (HA5 : AInvA segs A' rho5 tpL md2).
  { apply (X_AInvA A' rho5 tpL md2 HX5 HDI5). destruct (AInvA_X A rhoE tp md0 HA0) as (_ & _ & L60).
    destruct Hdpost2 as (EdN & _). unfold A'. cbn [aa_depot aa_Km aa_Kf bumpK with_depot]. lia. }
  assert (RW5 : forall i, (i < GW)%positive -> rw rho5 i = rw rhoE i).
  { intros i Hi. unfold rho5. cbn [rw rho_absorb]. symmetry. exact (proj1 Hag' i (NXlt i Hi)). }
  assert (HJGb5 : JGb W st A' Kc rho'' rho5 tpL tr2 md2).
  { split.
    - split; [|split].
      + intros i Hi. unfold A'. refine (eq_trans (rhoM_of_AK A G2 rho rho'' (fun j => eq_refl _) i) _). rewrite (Hagw i Hi). symmetry. exact (RW5 i Hi).
      + intros l. unfold rhoM_of. rewrite rl_rho_sets. unfold rho'', rho5. cbn [rl rho_absorb]. rewrite <- (proj2 Hag' l), <- (Hagl l).
        unfold rhoM_of. rewrite rl_rho_sets. reflexivity.
      + intros a. unfold rhoM_of. rewrite rm_rho_sets. reflexivity.
    - split; [exact HA5|]. split; [exact HK2|].
      split; [unfold tp_ok in Htp0 |- *; rewrite (RW5 24%positive) by (unfold GW; lia); exact Htp0|].
      split; [exact I|]. split; [exact I|].
      split; [cbn [eval]; rewrite (RW5 12%positive) by (unfold GW; lia); exact HN0|].
      unfold top_high. rewrite (RW5 10%positive), (RW5 V_DEPTH) by (unfold GW, V_DEPTH; lia). exact Htop0. }

  assert (HT5 : SPA segs (JGb W st A' Kc rho'') (T4d sz) rho5 tpL (tr2, mkCfg ms2 md2)).
  { pose proof (proj1 (proj1 HT4d)) as HsmT. pose proof HsmT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HfT).
    unfold rho5. apply (SPA_absorb_any segs JP); [exact AX4d | | exact HT4d | exact HJGb5].
    intros o a Ho Ha. exact (coveredb_sound _ _ _ rho' o a HfT (R4cov sz Hsz) Ho Ha). }
  pose proof (SPA_entails segs (JGb W st A' Kc rho'') GW (T4d sz) (C5 W st tmax) _ rho5 tpL _ (ENT5 sz Hsz) (SID5 sz Hsz)
                (JGb_stable 0%nat st A' Kc rho'' (stopJ_stable_nil st) HKc) HT5) as HC5.
  exists A', rho'', (rho_sub rho5 (sd sz)). split; [|split; [|exact HC5]].
  - unfold depot_onlyK, A'. cbn [aa_geom aa_cls aa_cache_inited aa_sec aa_ptr_committed aa_live aa_q_thread aa_q_global aa_internal_inited aa_fs_busy aa_fs_hint aa_V aa_Km aa_Kf bumpK with_depot].
    repeat split; reflexivity.
  - split; [intros i; reflexivity|]. split; [intros l; reflexivity|]. split.
    + intros a Hk. unfold rho''. cbn [rm]. rewrite KEY; [rewrite <- (Hagm a); unfold rhoM_of; rewrite rm_rho_sets; reflexivity|].
      exact (keep_not_DFP A' rhoE tpL md2 (bv_unsigned a) HX2 Hk).
    + intros a HBa Hdef. unfold rho''. cbn [rm]. rewrite KEY; [rewrite <- (Hagm a); unfold rhoM_of; rewrite rm_rho_sets; exact Hdef|].
      exact (BAND A' rhoE tpL md2 (bv_unsigned a) HX2 HBa).
Qed.

Lemma dc_exit : ltac2:(tb__ "0|2|
S91OF_;S5aS97SeSeS2aS68Q40A1A1M0S92S0S2aS75A1M1S7aS74SeG0G1S7aS74S5aSeSeG0SdeR13R4A2SdfS44R14A1R12R4A3S94Vsegs;R16S6fVsegs;SddVW;Vst;R6R14R5A5S85VW;Vst;Vtmax;A3R4R3A5R10A4F_;F_;Ftp';FrhoX;Frho';FA';S43R10ReRdRaA4S98R10A1ScbSbeSb4R12R11RfA3S5cR12A1A3SafSa0S9fR10VR4;RdA1S83RaRfRbA3A3Vs4;RdA1A2SeS70Vsegs;R11R10S41ReA1S32G1S8eRdS8fRcRbA2A4A5Sa5VW;Vst;R15R14R13R12R11ReRcA9SbfS16S3cS6dR10A1A1A1R3RcA3S70Vsegs;RdRcS6cR11A1S32G1S8eRbS8fRaR9A2A4A5R6R5R14ReRdRcRaA6S24Sb1R16S83R10R15R11A3VR4;R13A1Vs4;R13A1S6dR13A1S6cR13A1S41R13A1RfA8SeSc0R17S83R11R16R12A3VR4;R14A1Vs4;R14A1S3cS6dR14A1A1S3cS41R14A1A1S3cS6cR14A1A1R1R10A9S94Vsegs;R1cS6fVsegs;Sb0R9R8R17R11R10A5SaeVs4;R15A1S6dR15A1S6cR15A1S41R15A1VR4;R15A1A5R2R10A5R16A4F_;Frho';A2F_;F_;F_;F_;F_;TrhoC;TJL;F_;F_;F_;Fmd';Fms';Ftr';FtpL;FrhoL;Fmd0;Fms0;Ftr0;Fsz;FQ;Ftp;FrhoE;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho rhoE tp Q sz tr0 ms0 md0 rhoL tpL tr' ms' md' Hcont SF HKc JL rhoC Hsm0 HJ0 HagL HsmL HJL.
  split; [exact (dc_exit_ok A Kc rho rhoE tp sz tr0 ms0 md0 rhoL tpL tr' ms' md' SF HKc Hsm0 HJ0 HagL HsmL HJL)|].
  intros rho' HLK n' Hg' w' Hw'.
  destruct (dc_exit_core A Kc rho rhoE tp sz tr0 ms0 md0 rhoL tpL tr' ms' md' SF HKc Hsm0 HJ0 HagL HsmL HJL rho' w' HLK Hw') as (A' & rho'' & rhoX & Hdo & Hl & HC5).
  exact (Hcont A' rho'' rhoX tpL Hdo Hl n' Hg' w' HC5).
Qed.

Lemma dc_exitE : ltac2:(tb__ "0|2|
S5aS97SeSeS2aS68Q40A1A1M0S91OF_;S0S2aS75A1M1S7aS74SeG0G1S7aS74S5aSeSeG0SdeR13R4A2SdfS44R14A1R12R4A3S93Vsegs;S6fVsegs;SddVW;Vst;R6R14R5A5S85VW;Vst;Vtmax;A3R4R3A5R10A3F_;F_;Ftp';FrhoX;Frho';FA';S43R10ReRdRaA4S98R10A1ScbSbeSb4R12R11RfA3S5cR12A1A3SafSa0S9fR10VR4;RdA1S83RaRfRbA3A3Vs4;RdA1A2SeS70Vsegs;R11R10S41ReA1S32G1S8eRdS8fRcRbA2A4A5Sa5VW;Vst;R15R14R13R12R11ReRcA9SbfS16S3cS6dR10A1A1A1R3RcA3S70Vsegs;RdRcS6cR11A1S32G1S8eRbS8fRaR9A2A4A5R6R5R14ReRdRcRaA6S24Sb1R16S83R10R15R11A3VR4;R13A1Vs4;R13A1S6dR13A1S6cR13A1S41R13A1RfA8SeSc0R17S83R11R16R12A3VR4;R14A1Vs4;R14A1S3cS6dR14A1A1S3cS41R14A1A1S3cS6cR14A1A1R1R10A9S93Vsegs;S6fVsegs;Sb0R9R8R17R11R10A5SaeVs4;R15A1S6dR15A1S6cR15A1S41R15A1VR4;R15A1A5R2R10A5R16A3F_;Frho';A2F_;F_;F_;F_;F_;TrhoC;TJL;F_;F_;F_;Fmd';Fms';Ftr';FtpL;FrhoL;Fmd0;Fms0;Ftr0;Fsz;FQ;Ftp;FrhoE;Frho;FKc;FA;").
Proof.
  intros A Kc rho rhoE tp Q sz tr0 ms0 md0 rhoL tpL tr' ms' md' Hcont SF HKc JL rhoC Hsm0 HJ0 HagL HsmL HJL.
  split; [exact (dc_exit_ok A Kc rho rhoE tp sz tr0 ms0 md0 rhoL tpL tr' ms' md' SF HKc Hsm0 HJ0 HagL HsmL HJL)|].
  intros rho' HLK w' Hw'.
  destruct (dc_exit_core A Kc rho rhoE tp sz tr0 ms0 md0 rhoL tpL tr' ms' md' SF HKc Hsm0 HJ0 HagL HsmL HJL rho' w' HLK Hw') as (A' & rho'' & rhoX & Hdo & Hl & HC5).
  exact (Hcont A' rho'' rhoX tpL Hdo Hl w' HC5).
Qed.

Theorem depot_call_HD : ltac2:(tb__ "0|0|
S91OF_;S5aS97SeS92S98R3A1S73Vsegs;R6S72R4A1A3Sf2Vsegs;R7S72R5A1A3Se0U0Vst;Vtmax;S44R7A1R8R7R6R5R4A9F_;F_;F_;FQ;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho Q HKc Hokl Hokpl rhoE tp Hcont n HgQ w Hw. destruct w as [tr [ms md]].
  pose proof (dc_facts A Kc rho rhoE tp _ Hw) as SF. pose proof (dc_site A Kc rho rhoE tp _ Hw) as Hw4.
  pose proof SF as (Hsz & Fd1 & HG & E12 & _ & _ & _ & Htop).
  set (sz := bv_unsigned (rw rhoE 192%positive)) in *.
  pose proof (proj2 Hw) as [Hag HJ]. cbn [w_tr w_cfg cfg_model fst snd] in Hag, HJ.
  pose proof HJ as (HA & HK & Htp & HU & HB & HN & _). cbn [eval] in HN, HB.
  pose proof (AInvA_budget A rhoE tp md HA) as (_ & _ & _ & HKm0 & _).
  assert (Hn0 : 0 <= bv_unsigned (rw rhoE 12%positive)) by apply urange.
  pose proof (topG_range (aa_geom A)) as TG.
  assert (HKT : forall G r t tr0 md0, KD A Kc rhoE G r t tr0 md0 -> alloc_top (m_vmmaps md0) = topG (aa_geom A)).
  { intros G r t tr0 md0 HKG. rewrite (geom_top _ HG). exact (KD_top A Kc rhoE G r t tr0 md0 HKG). }
  apply (call_soundPA segs ok (JG W st A Kc rho) (JD segsA (KD A Kc rhoE) (aa_depot A)) (X4 sz) (PreD sz) (s4 sz) (R4 sz)
           [(PostD sz, JLD segsA (KD A Kc rhoE) (aa_depot A))] Q rhoE tp (HER sz Hsz)).
  - change (map fst [(PostD sz, JLD segsA (KD A Kc rhoE) (aa_depot A))]) with [PostD sz]. exact (Hchk4 sz Hsz).
  -
    intros rho1 tp1 n1 Hg1 w1 Hw1. pose proof (proj1 (proj2 Hw1)) as (_ & _ & _ & HT1).
    refine (seg_D_sound2 (KD A Kc rhoE) (hcD A) (KD_laws A Kc rhoE _ HKc HB Hn0 HKm0 NPRE ltac:(cbv; discriminate)) ok _ _ (topG (aa_geom A)) TG HKT
              sz ltac:(lia) rho1 tp1 (aa_depot A) (dN_entry A rhoE _ HB Hn0 tp md HA) (hcD_entry A rhoE _ HB Hn0 tp md HA) HT1 n1 Hg1 w1 Hw1).
    + intros G r t tr0 ms0 md0 msv' HKG HMI Hh Hp Hs. exact (Hokl r t tr0 ms0 md0 msv' (KD_Kc A Kc rhoE G r t tr0 md0 HKG) HMI Hh Hp Hs).
    + intros G r t tr0 ms0 md0 x8 HKG Hp Hok. exact (Hokpl r t tr0 ms0 md0 x8 (KD_Kc A Kc rhoE G r t tr0 md0 HKG) Hp Hok).
  -
    intros tr0 ms0 md0 Hsm0 HJ0. exact (dc_entry A Kc rho rhoE tp sz tr0 ms0 md0 SF HKc Hsm0 HJ0).
  -
    intros L JL tr0 ms0 md0 rhoL tpL tr' ms' md' HinL Hsm0 HJ0 HagL HsmL HJL.
    destruct HinL as [EL|[]].
    pose proof (f_equal fst EL) as EL1. pose proof (f_equal snd EL) as EL2. cbn [fst snd] in EL1, EL2. subst L JL. clear EL.
    exact (dc_exit ok A Kc rho rhoE tp Q sz tr0 ms0 md0 rhoL tpL tr' ms' md' Hcont SF HKc Hsm0 HJ0 HagL HsmL HJL).
  - exact HgQ.
  - exact Hw4.
Qed.

Theorem depot_call_HDE : ltac2:(tb__ "0|0|
S5aS97SeS91OF_;S98R3A1Sf7U0Vst;Vtmax;S44R5A1R5R4R3R2A8F_;FQ;Frho;FKc;FA;").
Proof.
  intros A Kc rho Q HKc rhoE tp Hcont w Hw. destruct w as [tr [ms md]].
  pose proof (dc_facts A Kc rho rhoE tp _ Hw) as SF. pose proof (dc_site A Kc rho rhoE tp _ Hw) as Hw4.
  pose proof SF as (Hsz & Fd1 & HG & E12 & _ & _ & _ & Htop).
  set (sz := bv_unsigned (rw rhoE 192%positive)) in *.
  pose proof (proj2 Hw) as [Hag HJ]. cbn [w_tr w_cfg cfg_model fst snd] in Hag, HJ.
  pose proof HJ as (HA & HK & Htp & HU & HB & HN & _). cbn [eval] in HN, HB.
  pose proof (AInvA_budget A rhoE tp md HA) as (_ & _ & _ & HKm0 & _).
  assert (Hn0 : 0 <= bv_unsigned (rw rhoE 12%positive)) by apply urange.
  pose proof (topG_range (aa_geom A)) as TG.
  assert (HKT : forall G r t tr0 md0, KD A Kc rhoE G r t tr0 md0 -> alloc_top (m_vmmaps md0) = topG (aa_geom A)).
  { intros G r t tr0 md0 HKG. rewrite (geom_top _ HG). exact (KD_top A Kc rhoE G r t tr0 md0 HKG). }
  apply (call_completePA segs (JG W st A Kc rho) (JD segsA (KD A Kc rhoE) (aa_depot A)) (X4 sz) (PreD sz) (s4 sz) (R4 sz)
           [(PostD sz, JLD segsA (KD A Kc rhoE) (aa_depot A))] Q rhoE tp (HER sz Hsz)).
  - change (map fst [(PostD sz, JLD segsA (KD A Kc rhoE) (aa_depot A))]) with [PostD sz]. exact (Hchk4 sz Hsz).
  - intros rho1 tp1 w1 Hw1. pose proof (proj1 (proj2 Hw1)) as (_ & _ & _ & HT1).
    exact (seg_D_complete2 (KD A Kc rhoE) (hcD A) (KD_laws A Kc rhoE _ HKc HB Hn0 HKm0 NPRE ltac:(cbv; discriminate)) (topG (aa_geom A)) TG HKT
              sz ltac:(lia) rho1 tp1 (aa_depot A) (dN_entry A rhoE _ HB Hn0 tp md HA) (hcD_entry A rhoE _ HB Hn0 tp md HA) HT1 w1 Hw1).
  - intros tr0 ms0 md0 Hsm0 HJ0. exact (dc_entry A Kc rho rhoE tp sz tr0 ms0 md0 SF HKc Hsm0 HJ0).
  - intros L JL tr0 ms0 md0 rhoL tpL tr' ms' md' HinL Hsm0 HJ0 HagL HsmL HJL.
    destruct HinL as [EL|[]].
    pose proof (f_equal fst EL) as EL1. pose proof (f_equal snd EL) as EL2. cbn [fst snd] in EL1, EL2. subst L JL. clear EL.
    exact (dc_exitE A Kc rho rhoE tp Q sz tr0 ms0 md0 rhoL tpL tr' ms' md' Hcont SF HKc Hsm0 HJ0 HagL HsmL HJL).
  - exact Hw4.
Qed.
End DC.
