(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "valuation"; "sstate"; "ss_next"; "sobj"; "sprop"; "ss_facts"; "holds"; "eval"; "SVar"; "rm"; "SLit"; "smatch"; "sv_below"; "obj_range"; "sv_eqb"; "SMd"; "agree_below"; "ob_base"; "ob_lo"; "SAlu"; "ob_hi"; "SPUle"; "SPBranch"; "rw"; "sprop_below"; "SPNot"; "outside_all"; "sprop_eqb"; "ss_objs"; "covered"; "obj_holds"; "pairwise_disjoint"; "soff"; "ss_lenient"; "SAluW"; "SExt"; "SLBytes"; "SMdW"; "cell"; "mkVal"; "ranges_disjoint"; "rl"; "@Corelib.Init.Logic"; "eq"; "and"; "ex"; "or"; "not"; "iff"; "False"; "True"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "N"; "@Corelib.Init.Datatypes"; "list"; "bool"; "prod"; "true"; "option"; "pair"; "fst"; "Some"; "cons"; "snd"; "app"; "nat"; "andb"; "false"; "nil"; "None"; "negb"; "orb"; "length"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "SPJ"; "jpred"; "ok_frame"; "LQ"; "SP"; "LQJ"; "ok_frameJ"; "stableJ"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "VmMaps"; "m_vmmaps"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV.WithSegs.Sum"; "JG"; "edesc"; "tv_below"; "T_after"; "tnz"; "tvv"; "tvd"; "TPI"; "tvin"; "call_checkT"; "tvz"; "fbin"; "ed_state"; "edrop"; "inited"; "JGi"; "nodeI"; "remove_nth"; "tv_sub_eqb"; "enodeI"; "echeckJ"; "ed_rank"; "ed_tv"; "emeas"; "malloc_contracts_ex"; "patchf"; "T0"; "ed_var"; "eecheckJ"; "jcert"; "keptF"; "T_afterN"; "ejcert"; "pclF"; "@Stdlib.Lists.List"; "In"; "nth_error"; "forallb"; "existsb"; "Forall2"; "filter"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface"; "MA"; "ma_L"; "ma_blocks"; "ma_owned"; "MInv"; "ma_s"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "wsub"; "rho_sub"; "rho_absorb"; "wsub_id_below"; "in_ranges"; "sv_subst"; "in_ranges_dec"; "@Corelib.Lists.ListDef"; "map"; "Forall"; "@Stdlib.ZArith.BinInt.Z"; "lt"; "le"; "add"; "pow"; "leb"; "opp"; "ltb"; "eqb"; "min"; "mul"; "modulo"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "world"; "triple"; "etriple"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "pos_add_nat"; "jpost"; "import_sub"; "LQP"; "import_post"; "call_check"; "call_checkP"; "wsub_dom_below"; "J_ofP"; "call_linkP"; "import_okP"; "sv_vars_all"; "call_link"; "new_objs"; "wsub_bound"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract"; "MInvR"; "V_RES"; "L_calloc_null"; "L_calloc_ok"; "V_TOP"; "ok_sideK"; "vm_insensitive"; "L_free"; "Pre_free"; "top_kept"; "L_malloc_null"; "L_malloc_ok"; "Pre_calloc"; "Pre_malloc"; "ec_ret_calloc"; "ec_ret_calloc2"; "ec_ret_memset"; "errno_range"; "tp_ok"; "J_alloc_pre"; "mem_kept"; "JL_free"; "J_free_pre"; "Posts_calloc"; "Posts_malloc"; "alloc_static"; "client_addr"; "top_var"; "wseg_addr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "entails_fr"; "entails"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "topL"; "mc_img_hi"; "mc_img_lo"; "mc_chk_guard"; "mc_chk_guard_got";
"mc_ctx"; "mc_ctz_tab"; "mc_libc"; "mc_lock"; "mc_med_cnt_tab"; "mc_replaced"; "mc_size_classes"; "mc_small_cnt_tab"; "mc_tp"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "ltb"; "le"; "lt"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV.WithSegs"; "T_ok"; "robjs_ok"; "caddr"; "tvd"; "tvv"; "JG"; "static_range"; "tnz"; "T0"; "malloc_laws"; "tvz"; "call_checkT"; "fbin"; "malloc_contracts"; "pclF"; "robjs_check"; "tvin"; "JG_pre"; "T_afterN"; "tv_below"; "tv_sub_eqb"; "img_ok"; "robj_stack"; "robj_tracked"; "JLG"; "TPI"; "inited"; "keptF"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "leaf"; "uleq"; "sleq"; "lf_state"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "rho_patch"; "svT"; "aceil"; "@LinuxProcessSemantics.Riscv.Instr"; "M_MUL"; "ALU_ADD"; "BC_EQ"; "aluop"; "mulop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "edge"; "jnode"; "enodeJ"; "add_facts"; "SPfamGJ"; "SPfamEJ"; "cfg_edges"; "e_src"; "e_sub"; "e_tgt"; "edge_okJ"; "e_leaf"; "eedge_okJ"; "enj_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV.WithSegs.Client"; "FBx"; "pdesc"; "robjs_okF"; "PostsC"; "import_tv"; "new_objs_tv"; "tvL_ok"; "tnzb"; "ivar_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV.WithSegs.Sum.CallT"; "remove_nth"; "tv_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV.WithSegs.Posts"; "JLG"; "JG_pre"; "@Corelib.Init.Specif"; "sumbool"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform"; "xform"; "XSelect"; "apply_xforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv"; "layout"; "CTX_SIZE"; "pairwise"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "st_init_done"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import MallocModel MallocInv MallocLayout MallocIface MallocLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundL SymSoundI SymSoundM SymSoundR SymFrame SymEntail SymCFG SymSummary ExampleMemcpy Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Contract.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import CursorGlue ObjXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition aceil : Z := aceil_lo.
Definition svT : sv := SVar V_TOP.

Lemma bv_urange : ltac2:(tb__ "0|2|
S9dQ40M0A1S2cS8eZ0S9eG0R1A2M1A2S8dG1S90Z2Z40A2A2A2Fa;").
Proof. intros a. pose proof (bv_unsigned_in_range 64 a) as H. rewrite two64 in H. lia. Qed.

Lemma in_app_mid {A} : ltac2:(tb__ "0|1|
S36VA;A1M0G0VA;VA;S77VA;R1S40VA;R4R3A3A3S77VA;R2S40VA;R5S3eVA;R3R4A3A3A3F_;Fy;Fx;Fl2;Fl1;").
Proof. intros l1 l2 x y H. apply in_app_or in H as [H|H]; apply in_or_app; [left|right; right]; exact H. Qed.

Lemma in_mid_cases {A} : ltac2:(tb__ "0|1|
S36VA;A1M0G0VA;VA;S77VA;R1S40VA;R4S3eVA;R2R3A3A3A3S2eS2bVA;R2R3A3S77VA;R2S40VA;R5R4A3A3A2F_;Fy;Fx;Fl2;Fl1;").
Proof.
  intros l1 l2 x y H. apply in_app_or in H as [H|[H|H]]; [right | left; auto | right]; apply in_or_app; auto.
Qed.

Lemma pairwise_in2 {A} : ltac2:(tb__ "0|0|
VA;VA;OF_;F_;S36VA;A1VA;VA;S12fVA;R4R3A3S77VA;R3R4A3S77VA;R3R5A3S2eS2bVA;R5R4A3S2eR7R5R4A2R7R4R5A2A2A2F_;F_;F_;Fy;Fx;Fl;FR;").
Proof.
  intros R l x y. induction l as [|h t IH]; cbn; [tauto|].
  intros [Hh Ht] [<-|Hx] [<-|Hy]; [left; reflexivity | right; left; apply Hh; exact Hy | right; right; apply Hh; exact Hx |].
  exact (IH Ht Hx Hy).
Qed.

Lemma ranges_disjoint_by_points : ltac2:(tb__ "0|0|
S33S33S33S33S33S2cS8eR5R1A2S8dR1R4A2A2S2cS8eR4R2A2S8dR2R3A2A2S31F_;F_;Fa;S29S3bS33S33R5R4A4S3bS33S33R3R2A4A2F_;Fh2;Fl2;Fh1;Fl1;").
Proof.
  intros l1 h1 l2 h2 H. unfold ranges_disjoint. cbn [fst snd].
  destruct (Z_lt_dec (Z.max l1 l2) (Z.min h1 h2)) as [Hlt|Hge]; [|lia].
  exfalso. apply (H (Z.max l1 l2)); lia.
Qed.

Definition rho_patch (rho : valuation) (f : word -> option byte) : valuation := ltac2:(tb__ "0|0|
S28S18Vrho;A1S2aVrho;A1Vf;A3").

Lemma eval_patch : ltac2:(tb__ "0|1|
S1S9dQ40A1M0S3aS9dQ8A1A1F_;S0S2bG0S8S106R3R2A2R1A2S8R3R1A2A3Fe;Ff;Frho;").
Proof. intros rho f e. induction e; cbn; try rewrite ?IHe1, ?IHe2, ?IHe; reflexivity. Qed.
Lemma soff_patch : ltac2:(tb__ "0|0|
S1S9dQ40A1S3aS9dQ8A1A1F_;S0S2bS33S21S106R3R2A2R1A2S21R3R1A2A3Fe;Ff;Frho;").
Proof. intros. unfold soff. rewrite eval_patch. reflexivity. Qed.
Lemma holds_patch : ltac2:(tb__ "0|0|
S1S9dQ40A1S3aS9dQ8A1A1F_;S5S30S7S106R3R2A2R1A2S7R3R1A2A2Fp;Ff;Frho;").
Proof. intros rho f p. induction p; cbn; rewrite ?eval_patch; try tauto. Qed.
Lemma obj_range_patch : ltac2:(tb__ "0|0|
S1S9dQ40A1S3aS9dQ8A1A1F_;S4S2bS38S33S33A2SeS106R3R2A2R1A2SeR3R1A2A3Fo;Ff;Frho;").
Proof. intros. unfold obj_range, obj_lo_of, obj_hi_of. rewrite eval_patch, !soff_patch. reflexivity. Qed.
Lemma covered_patch : ltac2:(tb__ "0|0|
S1S9dQ40A1S3aS9dQ8A1A1F_;S36S27A1S33S30S1eS106R4R3A2R2R1A3S1eR4R2R1A3A2Foff;Fcells;Ff;Frho;").
Proof.
  intros. unfold covered. rewrite !Exists_exists. unfold in_cell.
  split; intros (c & Hin & Hc); exists c; split; auto; revert Hc; rewrite !soff_patch; tauto.
Qed.
Lemma agree_vals_patch : ltac2:(tb__ "0|0|
S34S1S9dQ40A1S3aS9dQ8A1A1F_;Sa0R3R2S106R2R1A2A3Ff;Frho;Fn;").
Proof. intros. split; intros; reflexivity. Qed.

Section WithSegs.
Variable segs : list Segment.

Lemma obj_holds_patch : ltac2:(tb__ "0|0|
S1S9dQ40A1S3aS9dQ8A1A1F_;Se1S4S1fVsegs;R4R2R1A4S1fVsegs;S106R5R4A2R3R2A4F_;Fo;Fms;Ff;Frho;").
Proof using .
  intros rho f ms o (Hb & Hw & Hc & Hd & Hdl). unfold obj_holds, obj_lo_of, obj_hi_of in *.
  rewrite eval_patch, !soff_patch.
  split; [exact Hb|]. split; [exact Hw|]. split; [|split].
  - apply Forall_forall. intros c Hin. pose proof (proj1 (Forall_forall _ _) Hc c Hin) as H.
    unfold cell_holds, oaddr in *. rewrite !eval_patch, !soff_patch. exact H.
  - intros off Hoff Hcov. rewrite covered_patch in Hcov. specialize (Hd off Hoff Hcov).
    destruct (ob_dflt o); cbn in *; exact Hd.
  - eapply dflt_inv_exprs; [| | exact Hdl]; [intros; reflexivity|].
    destruct (ob_dflt o); try exact I. split; [symmetry; apply eval_patch|].
    apply Forall_forall. intros t _. symmetry. apply eval_patch.
Qed.

Lemma pairwise_disjoint_patch : ltac2:(tb__ "0|0|
S1S9dQ40A1S3aS9dQ8A1A1F_;S36S4A1S20R3R1A2S20S106R4R3A2R2A2F_;Fobjs;Ff;Frho;").
Proof using .
  intros rho f objs. induction objs as [|o t IH]; cbn; [tauto|]. intros [Hf Hp]. split; [|apply IH; exact Hp].
  apply Forall_forall. intros o' Hin. rewrite !obj_range_patch. exact (proj1 (Forall_forall _ _) Hf o' Hin).
Qed.

Lemma outside_all_patch : ltac2:(tb__ "0|1|
S1S9dQ40A1M0S3aS9dQ8A1A1F_;S36S4A1G0S30S1bS106R4R3A2R2R1A3S1bR4R2R1A3A2Fa;Fobjs;Ff;Frho;").
Proof using .
  intros. unfold outside_all. split; intros H; apply Forall_forall; intros o Hin;
    pose proof (proj1 (Forall_forall _ _) H o Hin) as X; cbn beta in X |- *;
    [rewrite obj_range_patch in X | rewrite obj_range_patch]; exact X.
Qed.

Lemma smatch_patch : ltac2:(tb__ "0|2|
S1S9dQ40A1M0S3aS9dQ8A1A1M1Fx;S2S38S36S52A1SfeA2ScVsegs;R4R2R1A4G0S1bR6S1dR4A1R1A3S2bG1R6R2A1SaR7R2A2A3F_;Fa;ScVsegs;S106R6R5A2R4R3A4F_;F_;Fw;FS;Ff;Frho;").
Proof using .
  intros rho f S w Hsm Hf. destruct w as [tr [ms md]].
  destruct Hsm as (Hwf & Hpc & Hpend & Hhalt & Hrom & Hroc & Hregs & Hfregs & Hfcsr & Hresv & Hmem & Hfacts).
  cbn [fst snd cfg_ms cfg_model] in *.
  unfold smatch. cbn [fst snd cfg_ms cfg_model].
  split; [exact Hwf|]. split; [exact Hpc|]. split; [exact Hpend|]. split; [exact Hhalt|]. split; [exact Hrom|].
  split; [exact Hroc|].
  split; [intros r Hr; rewrite eval_patch; apply Hregs; exact Hr|].
  split; [intros r; rewrite eval_patch; apply Hfregs|].
  split; [destruct (ss_fcsr S); cbn in *; rewrite ?eval_patch; exact Hfcsr|].
  split; [unfold resv_match in *; destruct (ss_resv S); destruct (ms_resv ms); rewrite ?eval_patch; exact Hresv|].
  split.
  - destruct Hmem as (Hall & Hpd & Hfr).
    split; [apply Forall_forall; intros o Hin; apply obj_holds_patch; exact (proj1 (Forall_forall _ _) Hall o Hin)|].
    split; [apply pairwise_disjoint_patch; exact Hpd|].
    intros a Ha. apply outside_all_patch in Ha. cbn [rho_patch rm]. rewrite (Hf a Ha). apply Hfr. exact Ha.
  - apply Forall_forall. intros p Hp. apply holds_patch. exact (proj1 (Forall_forall _ _) Hfacts p Hp).
Qed.

Variable C : mconsts.
Variable E : entry_consts.

Definition static_range (a : Z) : Prop := ltac2:(tb__ "0|a|
S2eS2cS8eSd6VC;A1M0Va;A2S8dVa;S8fG0Z38A2A2A2S2eS2cS8eSd9VC;A1M1Va;A2S8dVa;S8fG1Z4M2A2A2A2S2eS2cS8eSdaVC;A1M3Va;A2S8dVa;S8fG3Z60A2A2A2S2eS2cS8eSdbVC;A1M4Va;A2S8dVa;S8fG4Z1bA2A2A2S2eS2cS8eSd8VC;A1M5Va;A2S8dVa;S8fG5G2A2A2A2S2eS2cS8eSd5VC;A1M6Va;A2S8dVa;S8fG6Z20A2A2A2S2eS2cS8eSd3VC;A1M7Va;A2S8dVa;S8fG7Z8M8A2A2A2S2cS8eSd2VC;A1M9Va;A2S8dVa;S8fG9G8A2A2A2A2A2A2A2A2A2A2").

Definition img_ok (a : Z) : Prop := ltac2:(tb__ "0|2|
S2cS2bS37SccVsegs;S9fQ40Va;A2A2S39A3S2cS2fS2cS8eSd4VC;A1M0Va;A2S8dVa;S8fG0S12eA2A2A2A1S2cS2fS2cS8eSd7VC;A1M1Va;A2S8dVa;S8fG1Z4A2A2A2A1S2cS2fSc1VC;Va;A2A1S2fSe8Va;A1A1A2A2A2A2").

Record malloc_laws : Prop := ML {

  ml_frame : minv_frame_stmt C;

  ml_client : client_addr_not_owned_stmt segs C;

  ml_statics : statics_in_image C;

  ml_wseg : forall a, wseg_addr segs a = true -> mc_img_lo C <= bv_unsigned a < mc_img_hi C
}.

Record malloc_contracts : Prop := MC {
  mc_malloc : malloc_contract segs C E;
  mc_calloc : calloc_contract segs C E;
  mc_free : free_contract segs C E
}.

Definition caddr (Ai : MA) (x : option Z) (a : Z) : Prop := ltac2:(tb__ "0|0|
S2eS8eScfS7eVAi;A1A1Va;A2S2eSf7Va;A1S2dS33S33S2dS33S33S2cS77S38S33S33A2S3bS33S33R2R1A4S7fVAi;A1A3S2cS2fS2bS3aS33A1Vx;S3dS33R2A2A3A1S2cS8eR2Va;A2S8dVa;S8fR2R1A2A2A2A2A2Ln;A2Lb;A2A2A2").

Lemma caddr_weaken : ltac2:(tb__ "0|0|
S7dS33S33Se4R3S3dS33R2A2R1A3Se4R4S45S33A1R2A3F_;Fa;Fx;FAi;").
Proof using .
  intros Ai x a [H|[H|(b & n & Hin & _ & Hr)]]; [left; exact H | right; left; exact H |].
  right; right. exists b, n. repeat split; [exact Hin | discriminate | lia | lia].
Qed.

Lemma static_or_errno_in_image : ltac2:(tb__ "0|0|
S33SebS2eSe8R2A1Sc1VC;R2A2A2S2cS8eSd1VC;A1R3A2S8dR3Sd0VC;A1A2A2F_;F_;Fa;").
Proof using .
  intros a ML H. pose proof (ml_statics ML) as S. unfold statics_in_image in S. cbn beta iota zeta in S.
  unfold static_range, errno_range in H. lia.
Qed.

Lemma img_below_aceil : ltac2:(tb__ "0|0|
SebS8eS8fSd0VC;A1Z10A2S108A2F_;").
Proof using . intros ML. pose proof (ml_statics ML) as S. unfold statics_in_image in S. unfold aceil. unfold UNIT in S. lia. Qed.
Lemma img_below_top : ltac2:(tb__ "0|0|
S12dSebS8eS8fSd0VC;A1Z10A2ScfR2A1A2F_;FL;").
Proof using . intros L ML. pose proof (img_below_aceil ML). pose proof (topL_range L). unfold aceil in *. lia. Qed.

Lemma block_addr_props : ltac2:(tb__ "0|1|
S7dS9dQ40A1M0S3aS9dQ8A1A1F_;G0S37F_;S53S33S33S33SebS81VC;R8R7R6R5A5S77S38S33S33A2S3bS33S33R5R4A4S7fR9A1A3S2cS8eR6R4A2S8dR4S8fR6R5A2A2A2S2cS8dR5ScfS7eRbA1A1A2S2fS2cS8eSd1VC;A1R5A2S8dR5Sd0VC;A1A2A2A1A2F_;F_;F_;F_;Fa;Fn;Fb;Fvm;Fwok;Frd;FAi;").
Proof using .
  intros Ai rd wok vm b n a ML HM Hin Ha.
  pose proof (minv_block_geom C Ai rd wok vm b n HM Hin) as (_ & _ & _ & G3 & G4).
  unfold UNIT, IB in *. lia.
Qed.

Lemma static_alloc_static : ltac2:(tb__ "0|0|
S33Sc9VC;R1A2Se8R2A1F_;Fa;").
Proof using . intros a H. unfold alloc_static, static_range in *. tauto. Qed.

Lemma caddr_client : ltac2:(tb__ "0|0|
S7dS3aS33A1S33Se4R3R2R1A3ScaVsegs;VC;R4R2A4F_;Fa;Fx;FAi;").
Proof using .
  intros Ai x a [H|[H|(b & n & Hin & _ & Hr)]].
  - left. exact H.
  - right; right. destruct H as (H1 & H2 & H3 & H4 & _). auto.
  - right; left. exists b, n. auto.
Qed.

Lemma caddr_props : ltac2:(tb__ "0|0|
S7dS3aS33A1S33S1S51SebSb0Vsegs;VC;R6R3R2A5S2cS8eZ0R5A2S8dR5S90Z2Z40A2A2A2Se4R8R7R6A3S2cS2fS80VC;R9R7A3A1S2cS2fSc1VC;R7A2A1S2fSe8R7A1A1A2A2F_;F_;F_;F_;Fmd;Frho;Fa;Fx;FAi;").
Proof using .
  intros Ai x a rho md ML HM Ha Hc.
  pose proof (caddr_client Ai x a Hc) as Hcl.
  split; [exact (ml_client ML Ai rho md a HM Hcl)|].
  pose proof (img_below_top (ma_L Ai) ML) as HB.
  destruct Hc as [H|[H|(b & n & Hin & _ & Hr)]].
  - split; intros X; pose proof (static_or_errno_in_image a ML ltac:(auto)) as L; lia.
  - destruct H as (_ & _ & _ & H4 & H5). auto.
  - destruct (block_addr_props Ai _ _ _ b n a ML HM Hin Hr) as [_ G].
    split; intros X; apply G; apply (static_or_errno_in_image a ML); auto.
Qed.

Lemma caddr_mono : ltac2:(tb__ "0|2|
S7dS7dS3aS33A1S33Sb9R4R3A2S38S33S33A2M0S77G0R1S7fR6A1M1A3S77G0R2G1A3F_;Fb;Se4R6R4R3A3Se4R6R5R4A3F_;F_;F_;Fa;Fx;FA';FAi;").
Proof using .
  intros Ai A' x a HT Hsub [H|[H|(b & n & Hb & Hx & Hr)]]; [left; unfold top_kept in HT; rewrite HT; exact H | right; left; exact H | right; right].
  exists b, n. split; [apply Hsub; exact Hb|]. split; [exact Hx | exact Hr].
Qed.

Definition robjs_ok (Ai : MA) (x : option Z) (rho : valuation) (R : list sobj) : Prop := ltac2:(tb__ "0|1|
S4S33S77S4R2VR;A3S2cS8eS3cS33S33SeVrho;R3A2M0A3R2A2S8dR2S3fS33S33G0A3A2A2Se4VAi;Vx;R3A3F_;F_;Fa;Fo;").

Lemma robjs_mono : ltac2:(tb__ "0|2|
S7dS7dS3aS33A1S1S36S4A1Sb9R5R4A2S38S33S33A2M0S77G0R1S7fR7A1M1A3S77G0R2G1A3F_;Fb;Se3R7R5R4R3A4Se3R7R6R5R4A4F_;F_;F_;FR;Frho;Fx;FA';FAi;").
Proof using . intros Ai A' x rho R HT Hsub H o a Ho Hr. eapply caddr_mono; [exact HT | exact Hsub|]. exact (H o a Ho Hr). Qed.

Lemma robjs_in_ranges : ltac2:(tb__ "0|1|
S7dS3aS33A1S1S36S4A1S9dQ40M0A1Se3R5R4R3R2A4S88R4R3R2A3Se4R7R6S9eG0R3A2A3F_;F_;Fa;FR;Frho;Fx;FAi;").
Proof using . intros Ai x rho R a H (o & Hin & Hr). exact (H o _ Hin Hr). Qed.

Lemma blocks_bases_differ : ltac2:(tb__ "0|3|
S7dS1S51S33S33S33S33Sb0Vsegs;VC;R7R6R5A5S77S38S33S33A2M0S3bS33S33R5R4A4M1S7fR8A1A3S77G0S3bS33S33R4R3A4S7fR9A1A3S2fS2bG0S3bS33S33R7R6A4G1A3A1S8dZ0M2R7A2S8dG2R6A2S2fS2bS33RaR8A3A1F_;F_;F_;F_;F_;F_;Fn2;Fb2;Fn1;Fb1;Fmd;Frho;FAi;").
Proof using .
  intros Ai rho md b1 n1 b2 n2 HM H1 H2 Hne Hn1 Hn2.
  unfold MInvR in HM.
  destruct (pairwise_in2 _ _ _ _ (minv_blocks_pairwise C Ai _ _ _ HM) H1 H2) as [X|[X|X]];
    [exact (fun _ => Hne X) | |]; unfold MallocInv.ranges_disjoint in X; cbn [fst snd] in X; lia.
Qed.

Definition robj_stack (facts : list sprop) (o : sobj) : bool := ltac2:(tb__ "0|e|
S0S37Lx;M0S13Vo;A1S33SbR1A1S0G0S15Vo;A1S33S37S37L_;M1S91S92S90Z2M2Z3eA2M3A1R3A2G1S91R3R1A2G1S93R1G3A2S102Vfacts;S107S92S95R3Z0M4A2A1S12Vo;A1M5A4S43X37x2S43X37x2S43X37x2Lhi;S34G1S102Vfacts;S107G4S14S10aG5R2A3A4G1S102Vfacts;S107G4G5A4M6G1S103Vfacts;SbS92S90G2Z2eA2A1A1M7G4R2A4S103Vfacts;R2G4SbG4A1M8A4S43X37x2S43X37x2S43X37x2Li;S10cS0S0G1S102Vfacts;S107G4S14S10aG5R4A3A4G1G6G1S103Vfacts;G7G4R4A4S103Vfacts;R4G4G8A4S43X37x2S43X37x2S43X37x2M9Lb;La;MaLop;MbGbS10dGaLop;McGcS37S35S0G9La;Lw;Lsgn;S34S0S33G9Lk;Li;Ll;X0x8Tlo;Llo;S34S9R1A1S0G1S102Vfacts;S107G4S14S10aG5R1A3A4G1G6G1S103Vfacts;G7G4R1A4S103Vfacts;R1G4G8A4S43X37x2S43X37x2S43X37x2MdTlo;Li;S10cS0S0S14R3R2R1A3S0GdTlo;Lb;La;Lop;S10cS0S0S23R3R2R1A3S0GdTlo;Lb;La;Lop;S10dS0S0S10R3R2R1A3S0GdTlo;Lb;La;Lop;S10dS0S0S26R3R2R1A3S0GdTlo;Lb;La;Lop;S37S35S0S24R3R2R1A3S0GdTlo;La;Lw;Lsgn;S34S0S33S25R3R2R1A3S0GdTlo;Lk;Li;Ll;X0x8").

Lemma mod_sub_once : ltac2:(tb__ "0|0|
S33S33S8dZ0R1A2S2cS8eR2R3A2S8dR3S96Z2R2A2A2A2S2bS33S97R4R3A2S98R4R3A2A3F_;F_;FM;Fx;").
Proof using .
  intros x M HM Hx. rewrite (Z.mod_eq x M) by lia.
  replace (x / M) with 1; [lia|]. apply Z.div_unique with (r := x - M); lia.
Qed.

Definition T_ok (rho : valuation) (T : Z) : Prop := ltac2:(tb__ "0|1|
S2cS2bS33S9eQ40S18Vrho;Sb4A2A2VT;A3S2cS8eS90Z2M0Z2eA2VT;A2S8dVT;S90G0Z3fA2A2A2A2").

Lemma T_ok_topL : ltac2:(tb__ "0|0|
S1S12dS2bS33S9eQ40S18R2Sb4A2A2ScfR1A1A3Se2R3ScfR2A1A2F_;FL;Frho;").
Proof using . intros rho L H. split; [exact H|]. pose proof (topL_range L). lia. Qed.

Lemma robj_stack_lit_sound : ltac2:(tb__ "0|4|
S36S5A1S1S33S4S33S33S33S8cS5S7R6A1R7A3Se2R7R6A2S2bS0S13R6A1SbR5A1M0A3S2bS0S15R7A1G0A3S2bS37S37S37L_;M1S91S92S90Z2Z3eA2M2A1R7A2G1S91R7R6A2G1S93R6G2A2S102RbS107S92S95R7Z0A2A1S12R8A1A4S43X37x2S43X37x2S43X37x2S39A3S2cS8eS3cS33S33SeRbR9A2M3A3R6A2S8dR6S3fS33S33G3A3A2A2S8eRbR7A2F_;F_;F_;F_;F_;F_;Fa;Fhi;Flo;Fo;FT;Frho;Ffacts;").
Proof using .
  intros facts rho T o lo hi a HF [HT TR] Elo Ehi H Hr.
  apply lazy_andb_prop in H as [H1 H]. apply lazy_andb_prop in H as [H2 H]. apply lazy_andb_prop in H as [H3 H4].
  apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.ltb_lt in H3.
  pose proof (uleq_sound rho facts _ _ _ HF H4) as U4. unfold U in U4. change (eval rho svT) with (rw rho V_TOP) in U4. rewrite HT in U4.
  unfold obj_range, obj_lo_of, obj_hi_of in Hr. rewrite Elo, Ehi in Hr. cbn [fst snd] in Hr.
  rewrite !soff_lit_small in Hr by lia. lia.
Qed.

Lemma robj_stack_sym_sound : ltac2:(tb__ "0|5|
S36S5A1S1S33S4S33S8cS5S7R4A1R5A3Se2R5R4A2S2bS37S37S37L_;M0S102R7S107Z0M1S14S10aS12R4A1M2S13R4A1M3A3A4G0S102R7S107G1G2A4G0S103R7SbS92S90Z2Z2eA2A1A1G1G3A4S103R7G3G1SbG1A1A4S43X37x2S43X37x2S43X37x2S39A3S2cS8eS3cS33S33SeR7R5A2M4A3R4A2S8dR4S3fS33S33G4A3A2A2S8eR7R5A2F_;F_;F_;F_;Fa;Fo;FT;Frho;Ffacts;").
Proof using .
  intros facts rho T o a HF [HT TR] H Hr.
  apply lazy_andb_prop in H as [H1 H]. apply lazy_andb_prop in H as [H2 H]. apply lazy_andb_prop in H as [H3 H4].
  pose proof (uleq_sound rho facts _ 0 _ HF H1) as U1. pose proof (uleq_sound rho facts _ 0 _ HF H2) as U2.
  pose proof (sleq_sound rho facts _ 0 _ HF H3) as S3. pose proof (sleq_sound rho facts _ 0 _ HF H4) as S4.
  clear H1 H2 H3 H4 HF.
  unfold U in U1, U2. change (eval rho svT) with (rw rho V_TOP) in U1, U2. rewrite HT in U1, U2. rewrite U_add in U1.
  rewrite (soff_lit_small rho (- 2 ^ 46)) in S3 by lia. rewrite (soff_lit_small rho 0) in S4 by lia.
  unfold obj_range, obj_lo_of, obj_hi_of in Hr. cbn [fst snd] in Hr.
  unfold soff in S3, S4, Hr. rewrite !bv_signed_U in S3, S4, Hr.
  pose proof (bv_urange (eval rho (ob_base o))) as Rb. pose proof (bv_urange (eval rho (ob_lo o))) as Rl.
  unfold M64v in U1, U2, Rb, Rl |- *.
  destruct (Zsigned_spec (bv_unsigned (eval rho (ob_lo o)))) as [[Cz Ez]|[Cz Ez]]; rewrite Ez in S3, S4, Hr.
  - assert (Z0' : bv_unsigned (eval rho (ob_lo o)) = 0) by lia. rewrite Z0' in U1. rewrite Z.add_0_r, Z.mod_small in U1 by lia. lia.
  - unfold H63v, M64v in Cz, Ez, U1, S3, S4, Hr |- *. rewrite mod_sub_once in U1 by lia. lia.
Qed.

Lemma robj_stack_sound : ltac2:(tb__ "0|1|
S36S5A1S1S33S4S33S8cS5S7R4A1R5A3Se2R5R4A2S2bS37Sf8R7R4A2S39A3S2cS8eS3cS33S33SeR7R5A2M0A3R4A2S8dR4S3fS33S33G0A3A2A2S8eR7R5A2F_;F_;F_;F_;Fa;Fo;FT;Frho;Ffacts;").
Proof using .
  intros facts rho T o a HF HT H Hr. unfold robj_stack in H.
  destruct (ob_lo o) as [lo| | | | | | |] eqn:Elo;
    first [ destruct (ob_hi o) as [hi| | | | | | |] eqn:Ehi;
            first [ exact (robj_stack_lit_sound facts rho T o lo hi a HF HT Elo Ehi H Hr)
                  | exact (robj_stack_sym_sound facts rho T o a HF HT ltac:(rewrite Elo; exact H) Hr) ]
          | exact (robj_stack_sym_sound facts rho T o a HF HT ltac:(rewrite Elo; exact H) Hr) ].
Qed.

Fixpoint robj_tracked (tv : list (sv * sv)) (skip : option nat) (o : sobj) : bool :=
  match tv with
  | [] => false
  | t :: rest =>
      (match skip with Some O => false | _ => true end
       &&& (sv_eqb (ob_base o) (fst t) &&& (sv_eqb (ob_lo o) (SLit 0) &&& sv_eqb (ob_hi o) (snd t))))
      ||| robj_tracked rest (match skip with Some (S k) => Some k | _ => None end) o
  end.

Lemma robj_tracked_sound : ltac2:(tb__ "0|2|
S36S38S0S0A2M0A1S3aS41A1M1S4S2bS37Sf9R3R2R1A3S39A3S2dS41S41S2dG0G0S2cS2bS3aG0A1S78G0R6R2A3S3dG0R1A2A3S2cS2fS2bG1R5S3dS41R2A2A3A1S2cS2bS0S12R4A1S3cS0S0R1A3A3S2cS2bS0S13R4A1SbZ0A1A3S2bS0S15R4A1S3fS0S0R1A3A3A2A2A2A2Lt;A2Lj;A2F_;Fo;Fskip;Ftv;").
Proof using .
  intros tv. induction tv as [|t rest IH]; intros skip o H; [discriminate|].
  cbn [robj_tracked] in H. apply lazy_orb_prop in H as [H|H].
  - apply lazy_andb_prop in H as [Hs H]. apply lazy_andb_prop in H as [H1 H]. apply lazy_andb_prop in H as [H2 H3].
    apply sv_eqb_sound in H1. apply sv_eqb_sound in H2. apply sv_eqb_sound in H3.
    exists 0%nat, t. split; [reflexivity|]. split; [|auto]. destruct skip as [[|k]|]; [discriminate|congruence|congruence].
  - destruct (IH _ o H) as (j & t' & Hj & Hsk & Hb & Hl & Hh).
    exists (S j), t'. split; [exact Hj|]. split; [|auto].
    destruct skip as [[|k]|]; [congruence| |congruence]. intros X. injection X as X. apply Hsk. congruence.
Qed.

Definition robjs_check (facts : list sprop) (tv : list (sv * sv)) (skip : option nat) (extra : sobj -> bool) (R : list sobj) : bool := ltac2:(tb__ "0|1|
S79S4S4S37S37L_;M0Sf8Vfacts;R1A2S39G0Sf9Vtv;Vskip;R1A3S39Vextra;R1A1X37x2X37x2Lo;VR;A3").

Section Sum.

Variable NP : positive.
Variable Kc : ltac2:(tb__ "0|0|
S36S52A1S51OF_;F_;").
Variable rho0 : valuation.

Variable P0f : valuation -> Prop.

Variable FB : list (Z * Z).

Ltac clear_sec0 := try clear FB; try clear P0f; try clear rho0; try clear Kc; try clear NP.

Definition tvv (rho : valuation) (t : sv * sv) : Z * Z := ltac2:(tb__ "0|1|
S3bS33S33S9eQ40M0S8Vrho;S3cS0S0Vt;A3A2A2S9eG0S8Vrho;S3fS0S0Vt;A3A2A2A4").
Definition tnz (rho : valuation) (t : sv * sv) : Prop := ltac2:(tb__ "0|0|
S2fS2bS33S9eQ40S8Vrho;S3cS0S0Vt;A3A2A2Z0A3A1").

Definition fbin (Ai : MA) : Prop := ltac2:(tb__ "0|1|
S38S33S33A2M0S77G0R1VFB;A3S77G0R2S7fVAi;A1A3F_;Fbn;").

Definition tvin (Ai : MA) (rho : valuation) (tv : list (sv * sv)) : Prop := ltac2:(tb__ "0|3|
S8cS38S0S0A2M0G0S59Vrho;R1A2S2cS8dZ0S3fS33S33S5aVrho;R2A2M1A3A2S2cS77S38S33S33A2M2G1S7fVAi;A1A3S2fS77G2G1VFB;A3A1A2A2F_;Lt;Vtv;A3").

Definition tvz (rho : valuation) (tv : list (sv * sv)) : Prop := ltac2:(tb__ "0|1|
S8cS38S0S0A2M0G0S2fS59Vrho;R1A2A1S2bS33S3fS33S33S5aVrho;R2A2A3Z0A3F_;Lt;Vtv;A3").

Fixpoint tvd (rho : valuation) (tv : list (sv * sv)) : Prop :=
  match tv with
  | [] => True
  | t :: r => (forall t', In t' r -> tnz rho t -> tnz rho t' -> tvv rho t <> tvv rho t') /\ tvd rho r
  end.

Definition T0 : Z := bv_unsigned (rw rho0 V_TOP).

Definition pclF (a : Z) : Prop := ltac2:(tb__ "0|0|
S2eS8eS6fVa;A2S2eSf7Va;A1S2dS33S33S2dS33S33S2cS77S38S33S33A2S3bS33S33R2R1A4VFB;A3S2cS8eR2Va;A2S8dVa;S8fR2R1A2A2A2A2Ln;A2Lb;A2A2A2").

Definition keptF (m0 m1 : word -> option byte) : Prop := ltac2:(tb__ "0|1|
S33S2cS8eZ0R1A2S8dR1S90Z2Z40A2A2A2S76R2A1S2bS3aS9dQ8A1A1Vm1;S9fQ40R3A2M0A1Vm0;G0A1A3F_;F_;Fa;").

Definition inited (Ai : MA) : Prop := ltac2:(tb__ "0|0|
S2bS37S130S82VAi;A1A1S39A3").

Definition TPI (Ai : MA) : Prop := ltac2:(tb__ "0|0|
S2cSc2VC;Vrho0;A2S2bS33ScfS7eVAi;A1A1S6fA3A2").

Lemma TPI_kept : ltac2:(tb__ "0|1|
S7dS7dSb9R2R1A2S5cR3A1M0G0F_;F_;FA';FAi;").
Proof using . intros Ai A' HK [H1 H2]. split; [exact H1|]. unfold top_kept in HK. rewrite HK. exact H2. Qed.
Lemma TPI_tp : ltac2:(tb__ "0|0|
S7dS5cR1A1Sc2VC;Vrho0;A2F_;FAi;").
Proof using . intros Ai [H _]. exact H. Qed.
Lemma TPI_top : ltac2:(tb__ "0|0|
S7dS5cR1A1S2bS33ScfS7eR2A1A1S6fA3F_;FAi;").
Proof using . intros Ai [_ H]. exact H. Qed.

Definition call_checkT (Cl Pre : sstate) (s : wsub) (R : list sobj) (posts : list sstate) : bool := ltac2:(tb__ "0|3|
S42S42Sa7VCl;VPre;Vs;VR;Vposts;A5S47S42SfS83Vs;P18M0A2M1S9G0A1A2SdeG0VNP;A2A2S42S42SfG1SbSdcVC;A1M2A1A2S91Z0G2A2A2S93G2S90Z2Z40A2A2A2A2A2S42SfS83Vs;Sb4A2S9Sb4A1A2SdeSb4VNP;A2A2A2").

Lemma call_checkT_P : ltac2:(tb__ "0|0|
S2S2S84S36S4A1S36S2A1S2bS37S5eR5R4R3R2R1A5S39A3S2bS37Sa7R6R5R4R3R2A5S39A3F_;Fposts;FR;Fs;FPre;FCl;").
Proof using . intros Cl Pre s R posts H. unfold call_checkT in H. apply andb_prop in H as [H _]. apply andb_prop in H as [H _]. exact H. Qed.

Lemma top_of_TPI : ltac2:(tb__ "0|1|
S2S2S84S36S4A1M0S36S2A1S1G0Se1S7dSa0VNP;Vrho0;R4A3S5cR2A1S2bS37S5eRbRaR9R8R7A5S39A3ScbR4S85S86R7R6R5A3RaA2A2F_;F_;F_;FAi;Fms;FRb;Frho;Fposts;FR;Fs;FPre;FCl;").
Proof using .
  clear FB P0f Kc. intros Cl Pre s R posts rho Rb ms Ai [Hw _] [_ Ht] H. unfold call_checkT in H. apply andb_prop in H as [_ H].
  apply andb_prop in H as [Ee Hn]. apply sv_eqb_sound in Ee. apply Pos.ltb_lt in Hn.
  unfold top_var. cbn [rw rho_sub]. rewrite Ee, eval_absorb. cbn [eval]. rewrite <- (Hw V_TOP Hn). symmetry. exact Ht.
Qed.

Lemma T_of_chk : ltac2:(tb__ "0|0|
S2S2S84S36S4A1S36S2A1S1S7dSa0VNP;Vrho0;R2A3S5cR2A1S2bS37S5eR9R8R7R6R5A5S39A3Se2R5ScfS7eR4A1A1A2F_;F_;F_;FAi;Frho;Fposts;FR;Fs;FPre;FCl;").
Proof using .
  clear FB P0f Kc. intros Cl Pre s R posts rho Ai [Hw _] [_ Ht] H. unfold call_checkT in H. apply andb_prop in H as [_ H].
  apply andb_prop in H as [_ Hn]. apply Pos.ltb_lt in Hn.
  apply T_ok_topL. rewrite <- (Hw V_TOP Hn). symmetry. exact Ht.
Qed.

Lemma T_of_TPI : ltac2:(tb__ "0|0|
S1S7dSa0VNP;Vrho0;R2A3Se0Sb4VNP;A2S5cR3A1Se2R5ScfS7eR4A1A1A2F_;F_;F_;FAi;Frho;").
Proof using .
  clear FB P0f Kc. intros rho Ai [Hw _] Hn [_ Ht]. apply T_ok_topL. rewrite <- (Hw V_TOP Hn). symmetry. exact Ht.
Qed.

Lemma tp_of_TPI : ltac2:(tb__ "0|1|
S2S2S84S36S4A1M0S36S2A1S1G0Se1S7dSa0VNP;Vrho0;R4A3S5cR2A1S2bS37S5eRbRaR9R8R7A5S39A3Sc2VC;S85S86R7R6R5A3RaA2A2F_;F_;F_;FAi;Fms;FRb;Frho;Fposts;FR;Fs;FPre;FCl;").
Proof using .
  clear FB P0f Kc. intros Cl Pre s R posts rho Rb ms Ai [Hw _] [Ht _] H. unfold call_checkT in H. apply andb_prop in H as [H _]. apply andb_prop in H as [_ H].
  unfold tp_ok in Ht. unfold tp_ok. cbn [rw rho_sub].
  destruct (sv_eqb (wsub_get s 24%positive) (SVar 24%positive) && (24 <? NP)%positive) eqn:E1.
  - apply andb_prop in E1 as [Ee Hn]. apply sv_eqb_sound in Ee. apply Pos.ltb_lt in Hn.
    rewrite Ee, eval_absorb. cbn [eval]. rewrite <- (Hw 24%positive Hn). exact Ht.
  - rewrite orb_false_l in H. apply andb_prop in H as [H Hhi]. apply andb_prop in H as [Ee Hlo]. apply sv_eqb_sound in Ee.
    apply Z.leb_le in Hlo. apply Z.ltb_lt in Hhi.
    rewrite Ee, eval_absorb. cbn [eval]. rewrite Z_to_bv_unsigned, bv_wrap_small; [reflexivity|]. rewrite two64. lia.
Qed.

Definition JGi (tv : list (sv * sv)) (Ai : MA) : jpred := ltac2:(tb__ "0|0|
S1S36S52A1S51S2cSa0VNP;Vrho0;R3A3S2cVKc;R2R1A2S2cS2cSb0Vsegs;VC;VAi;R3R1A5S2cS63VAi;A1S5cVAi;A1A2A2S2cS60VAi;A1S2cS2cS5dVAi;R3Vtv;A3S2cS5bR3Vtv;A2S5fR3Vtv;A2A2A2S2cS73SaVrho0;A1SaR3A1A2VP0f;Vrho0;A1A2A2A2A2A2A2Lmd;Ltr;Lrho;").

Definition JG (tv : list (sv * sv)) : jpred := ltac2:(tb__ "0|0|
S1S36S52A1S51S2dS7dS7dS64Vtv;R1R4R3R2A5LAi;A2Lmd;Ltr;Lrho;").

Lemma pclF_caddr : ltac2:(tb__ "0|0|
S7dS33S60R2A1S5cR3A1S76R3A1Se4R5S45S33A1R4A3F_;F_;F_;Fa;FAi;").
Proof using .
  intros Ai a HP HT [H|[H|(b & n & Hin & Hr)]]; [left; rewrite (TPI_top Ai HT); exact H | right; left; exact H |].
  right; right. exists b, n. split; [exact (HP _ Hin)|]. split; [discriminate | exact Hr].
Qed.

Definition tv_below (n : positive) (tv : list (sv * sv)) : bool := ltac2:(tb__ "0|1|
S79S38S0S0A2M0G0S42SdVn;S3cS0S0R1A3A2SdVn;S3fS0S0R1A3A2A2Lt;Vtv;A3").

Lemma tvv_agree : ltac2:(tb__ "0|0|
S34S1S1S38S0S0A2Sa0R4R3R2A3S2bS37S42SdR5S3cS0S0R2A3A2SdR5S3fS0S0R2A3A2A2S39A3S2bS38S33S33A2S5aR4R3A2S5aR5R3A2A3F_;F_;Ft;Frho';Frho;Fn;").
Proof using .
  clear_sec0. intros n rho rho' [d e] Hag Hb. apply andb_prop in Hb as [Hd He]. unfold tvv. cbn [fst snd].
  rewrite (eval_agree_vals n rho rho' d Hag Hd), (eval_agree_vals n rho rho' e Hag He). reflexivity.
Qed.

Lemma tnz_agree : ltac2:(tb__ "0|0|
S34S1S1S38S0S0A2Sa0R4R3R2A3S2bS37S42SdR5S3cS0S0R2A3A2SdR5S3fS0S0R2A3A2A2S39A3S30S59R4R3A2S59R5R3A2A2F_;F_;Ft;Frho';Frho;Fn;").
Proof using .
  clear_sec0. intros n rho rho' [d e] Hag Hb. apply andb_prop in Hb as [Hd He]. unfold tnz. cbn [fst snd].
  rewrite (eval_agree_vals n rho rho' d Hag Hd). tauto.
Qed.

Lemma tvin_agree : ltac2:(tb__ "0|0|
S7dS34S1S1S36S38S0S0A2A1Sa0R4R3R2A3S2bS37S57R5R2A2S39A3S5dR7R5R3A3S5dR8R5R4A3F_;F_;F_;Ftv;Frho';Frho;Fn;FAi;").
Proof using .
  intros Ai n rho rho' tv Hag Hb H. unfold tvin in *. apply Forall_forall. intros t Hin.
  pose proof (proj1 (forallb_forall _ _) Hb t Hin) as Hbt.
  pose proof (proj1 (Forall_forall _ _) H t Hin) as X. cbn beta in X.
  rewrite (tvv_agree n rho rho' t Hag Hbt). intros Hnz. apply X. apply (proj1 (tnz_agree n rho rho' t Hag Hbt)). exact Hnz.
Qed.

Lemma tvd_agree : ltac2:(tb__ "0|0|
S34S1S1S36S38S0S0A2A1Sa0R4R3R2A3S2bS37S57R5R2A2S39A3S5bR5R3A2S5bR5R4A2F_;F_;F_;Ftv;Frho';Frho;Fn;").
Proof using .
  clear_sec0. intros n rho rho' tv Hag. induction tv as [|t r IH]; intros Hb H; [exact I|].
  cbn in Hb. apply andb_prop in Hb as [Hbt Hbr]. destruct H as [H1 H2]. split; [|exact (IH Hbr H2)].
  intros t' Hin' Hnz Hnz'. pose proof (proj1 (forallb_forall _ _) Hbr t' Hin') as Hbt'.
  rewrite (tvv_agree n rho rho' t Hag Hbt), (tvv_agree n rho rho' t' Hag Hbt').
  apply H1; [exact Hin' | apply (proj1 (tnz_agree n rho rho' t Hag Hbt)); exact Hnz | apply (proj1 (tnz_agree n rho rho' t' Hag Hbt')); exact Hnz'].
Qed.

Lemma tvz_agree : ltac2:(tb__ "0|0|
S34S1S1S36S38S0S0A2A1Sa0R4R3R2A3S2bS37S57R5R2A2S39A3S5fR5R3A2S5fR5R4A2F_;F_;F_;Ftv;Frho';Frho;Fn;").
Proof using .
  clear_sec0. intros n rho rho' tv Hag Hb H. unfold tvz in *. apply Forall_forall. intros t Hin.
  pose proof (proj1 (forallb_forall _ _) Hb t Hin) as Hbt.
  pose proof (proj1 (Forall_forall _ _) H t Hin) as X. cbn beta in X.
  rewrite (tvv_agree n rho rho' t Hag Hbt). intros Hnz. apply X. intros Hz. apply Hnz. apply (proj2 (tnz_agree n rho rho' t Hag Hbt)). exact Hz.
Qed.

Hypothesis ML : malloc_laws.

Ltac clear_sec := try clear FB; try clear P0f; try clear rho0; try clear Kc; try clear NP.

Lemma MInvR_mem : ltac2:(tb__ "0|1|
S7dS1S1S51S51S2cSb0Vsegs;VC;R5R4R2A5S2cS63R5A1S5cR5A1A2A2S33S2cS8eZ0R1A2S8dR1S90Z2Z40A2A2A2S2eS80VC;R8R2A3Se8R2A1A2S2bS3aS9dQ8A1A1SaR7S9fQ40R3A2M0A2SaR8G0A2A3F_;F_;Fa;S2bS53S54R3A1S54R4A1A3S2cSb0Vsegs;VC;R8R6R4A5S2cS63R8A1S5cR8A1A2A2F_;F_;F_;Fmd';Fmd;Frho';Frho;FAi;").
Proof using ML.
  clear_sec. intros Ai rho rho' md md' [HM Hi] Hm Hvm. split; [|exact Hi]. unfold MInvR in *. rewrite Hvm.
  eapply (ml_frame ML); [exact HM| |reflexivity|reflexivity|reflexivity|reflexivity|reflexivity|reflexivity|exact (proj1 Hi)].
  intros a Ha Ho. unfold rd_of, wok_of. rewrite (Hm a Ha ltac:(unfold static_range; tauto)). split; reflexivity.
Qed.

Lemma MI1 : ltac2:(tb__ "0|0|
S7dS1S51S2cSb0Vsegs;VC;R3R2R1A5S2cS63R3A1S5cR3A1A2A2Sb0Vsegs;VC;R4R3R2A5F_;Fmd;Frho;FAi;").
Proof using . intros Ai rho md [H _]. exact H. Qed.

Lemma JGi_stable : ltac2:(tb__ "0|0|
S34S36S38S0S0A2A1S7dS1S1S36S52A1S51SdfVNP;R7A2S2bS37S57R8R7A2S39A3S11R9R6R5A3S64R9R8R7R5R4A5S64RaR9R7R6R5A5F_;F_;F_;F_;Fmd;Ftr;Frho';Frho;FAi;Ftv;Fn;").
Proof using ML.
  intros n tv Ai rho rho' tr md Hle Hb Hag (Hav & Hk & HM & HP & (HN & HD & HZ) & HK & HP0).
  pose proof (agree_below_vals _ _ _ Hag) as Hav'.
  split; [|split; [exact Hk|split; [|split; [exact HP|split; [split; [|split]|split; [|exact HP0]]]]]].
  - eapply agree_vals_trans; [exact Hav|]. eapply agree_vals_le; [exact Hle | exact Hav'].
  - eapply MInvR_mem; [exact HM| |reflexivity]. intros a _ _. destruct Hag as (_ & _ & Hm). symmetry. apply Hm.
  - eapply tvin_agree; [exact Hav' | exact Hb | exact HN].
  - eapply tvd_agree; [exact Hav' | exact Hb | exact HD].
  - eapply tvz_agree; [exact Hav' | exact Hb | exact HZ].
  - intros a Ha Hp. destruct Hag as (_ & _ & Hm). rewrite <- (Hm (Z_to_bv 64 a)). exact (HK a Ha Hp).
Qed.

Lemma stableJ_JG : ltac2:(tb__ "0|0|
S34S36S38S0S0A2A1SdfVNP;R2A2S2bS37S57R3R2A2S39A3S50R4S55R3A1A2F_;F_;Ftv;Fn;").
Proof using ML.
  intros n tv Hle Hb rho rho' tr md Hag [Ai HJ]. exists Ai. exact (JGi_stable n tv Ai rho rho' tr md Hle Hb Hag HJ).
Qed.

Lemma ok_frameJ_JG : ltac2:(tb__ "0|0|
S9aOF_;S36S38S0S0A2A1S4bVsegs;R2VKc;A3S4fVsegs;R3S55R2A1A3F_;Ftv;Fok;").
Proof using . intros ok tv H rho tr ms md ms' (Ai & _ & Hk & _). exact (H tr ms md ms' Hk). Qed.

Lemma JG_intro : ltac2:(tb__ "0|0|
S36S38S0S0A2A1S2S9aS4aS1S36S52A1S51R4R3R2R1A3S2cVKc;R3R2A2S2dS7dS7dS2cS2cSb0Vsegs;VC;R1R5R3A5S2cS63R1A1S5cR1A1A2A2S2cS60R1A1S2cS2cS5dR1R5R9A3S2cS5bR5R9A2S5fR5R9A2A2A2VP0f;R5A1A2A2A2LAi;A2A2F_;Fmd;Ftr;Frho;S49Vsegs;R2R4Vrho0;R3A5S49Vsegs;S55R6A1R5Vrho0;R4A5F_;F_;FJ0;Fw;FS;Ftv;").
Proof using .
  intros tv S w J0 HJ0 [Hsm HJ]. split; [exact Hsm|]. destruct (HJ0 _ _ _ HJ) as (Hk & Ai & HM & HP & HN & HP0).
  exists Ai. split; [apply agree_vals_refl|]. split; [exact Hk|]. split; [exact HM|]. split; [exact HP|].
  split; [exact HN|]. split; [|exact HP0]. intros a _ _. reflexivity.
Qed.

Definition T_afterN (n : positive) (Cl : sstate) (s : wsub) (R : list sobj) (L : sstate) : sstate := ltac2:(tb__ "0|0|
S111S6VCl;A1Sa5Vs;Vn;VL;S3VCl;A1VR;A5A2").
Definition T_after (Cl : sstate) (s : wsub) (R : list sobj) (L : sstate) : sstate := ltac2:(tb__ "0|0|
S74S100VCl;Vs;VR;VL;A5").

Lemma R_ranges_agree : ltac2:(tb__ "0|2|
S2S2S84S36S4A1M0S1S1S36S52A1M1Se1S51S2bS3aG0A1ScdR9R8R7A3S3dG0R6A2A3ScVsegs;R6RaS3bG1SfeR4SffR3R2A2A4A4Sa0S3RbA1R7R6A3S4S77S4R1RaA3S2bS38S33S33A2SeR9R2A2SeRaR2A2A3F_;Fo;F_;F_;F_;Fmd;Fms;Ftr;Frho';Frho;FR;Fs;FPre;FCl;").
Proof using .
  intros Cl Pre s R rho rho' tr ms md He Hsm Hag o Hin.
  destruct (entails_fr_sound segs Cl Pre s R rho tr ms md He Hsm) as (_ & _ & _ & Hwf & _).
  eapply obj_range_agree_vals; [exact Hag|]. exact (proj1 (forallb_forall _ _) Hwf o Hin).
Qed.

Lemma R_miss : ltac2:(tb__ "0|0|
S7dS3aS33A1S1S1S51S36S4A1S33Sb0Vsegs;VC;R7R4R3A5Se3R8R7R6R3A4S2cS8eZ0R3A2S8dR3S90Z2Z40A2A2A2S2eS80VC;RaR4A3Se8R4A1A2S2fS88R9R6S9fQ40R5A2A3A1F_;F_;F_;F_;Fa;FR;Fmd;FrhoM;Frho;Fx;FAi;").
Proof using ML.
  clear_sec. intros Ai x rho rhoM md R a HM HR Ha Ho Hin.
  apply (robjs_in_ranges Ai x rho R) in Hin; [|exact HR].
  rewrite Z_to_bv_unsigned, bv_wrap_small in Hin by (rewrite two64; lia).
  destruct (caddr_props Ai x a rhoM md ML HM Ha Hin) as (H1 & _ & H3). tauto.
Qed.

Lemma rw_call' : ltac2:(tb__ "0|0|
S1S36S4A1Se1S84S34S2bS9dQ40A1S18S85S86R5R4R3A3R2A2R1A2S8R5S83R2R1A2A2A3Fi;Fs;Fms;FR;Frho;").
Proof using . intros. cbn [rho_sub rw]. apply eval_absorb. Qed.

Definition patchf (rho rho' : valuation) (R : list sobj) : word -> option byte := ltac2:(tb__ "0|2|
S9dQ40A1S129S88Vrho;VR;R1A3M0S2fG0A1M1A2S3aS9dQ8A1A1L_;S8aVrho;VR;R1A3G0SaVrho;R2A2L_;G1SaVrho';R2A2L_;X129x2La;").

Lemma cont_smatchN : ltac2:(tb__ "0|3|
S34S2S2S2S84S36S4A1M0S1S1S36S52A1M1Se1S51S38G1SfeA2S2bS3aG0A1ScdRbRaR8A3S3dG0R7A2A3ScVsegs;R7RcS3bG1SfeR5SffR4R3A2A4A4S2bS34S3RcA1ReA3Sa0S3ReA1M2R9R8A3ScVsegs;R9Sa5RcG2RdS3RfA1RbA5R5A4ScVsegs;S106RaS6eRbRaRcA3A2S74R11R10RdRcReA5R6A4F_;F_;F_;F_;F_;Fw;Fmd;Fms;Ftr;Frho';Frho;FR;Fs;FL;FPre;FCl;Fn;").
Proof using .
  clear_sec. intros n Cl Pre L s R rho rho' tr ms md w He Hsm HnP Hag' Hsm'.
  unfold T_afterN. rewrite <- HnP. apply smatch_add_facts.
  - apply smatch_patch; [exact Hsm'|]. intros a Hout. unfold patchf.
    destruct (in_ranges_dec rho R a) as [Hi|Hn]; [|reflexivity]. exfalso.
    destruct Hi as (oR & HinR & Hr).
    unfold import_post in Hout. cbn [ss_objs set_objs] in Hout.
    apply outside_all_app_iff in Hout as [_ Hout].
    pose proof (proj1 (Forall_forall _ _) Hout oR HinR) as X. cbv beta zeta in X.
    rewrite (R_ranges_agree Cl Pre s R rho rho' tr ms md He Hsm Hag' oR HinR) in X. lia.
  - apply Forall_forall. intros p Hp. apply holds_patch.
    apply (holds_agree_vals (ss_next Cl) rho rho' p Hag').
    + exact (proj1 (forallb_forall _ _) (swf_facts _ (smatch_swf segs _ _ _ Hsm)) p Hp).
    + eapply (proj1 (Forall_forall _ _) (smatch_facts_hold segs _ _ _ Hsm)). exact Hp.
  - apply forallb_forall. intros p Hp.
    eapply sprop_below_mono; [| exact (proj1 (forallb_forall _ _) (swf_facts _ (smatch_swf segs _ _ _ Hsm)) p Hp)].
    unfold import_post. cbn [ss_next set_objs subst_state]. unfold import_next, pos_add_nat. lia.
Qed.

Lemma cont_smatch : ltac2:(tb__ "0|3|
S2S2S2S84S36S4A1M0S1S1S36S52A1M1Se1S51S38G1SfeA2S2bS3aG0A1ScdRbRaR8A3S3dG0R7A2A3ScVsegs;R7RcS3bG1SfeR5SffR4R3A2A4A4S2bS34S3RcA1S100A3Sa0S3ReA1M2R9R8A3ScVsegs;R9Sa5RcG2RdS3RfA1RbA5R5A4ScVsegs;S106RaS6eRbRaRcA3A2S58R10RdRcReA4R6A4F_;F_;F_;F_;F_;Fw;Fmd;Fms;Ftr;Frho';Frho;FR;Fs;FL;FPre;FCl;").
Proof using . intros. unfold T_after. eapply cont_smatchN; eauto. Qed.

Lemma keptF_step : ltac2:(tb__ "0|4|
S7dS7dS1S1Se1S84S36S4A1S51S51S1S60RaA1S38S33S33A2M0S77G0R1VFB;A3S77G0R2S7fRcA1A3F_;Fb;S2cSb0Vsegs;VC;RcRaR5A5M1S2cS63RcA1S5cRcA1A2A2G1Sb9ReRdA2Se3RfS45S33A1RdR9A4S73SaVrho0;A1M2SaReA1M3A2Sc4Vsegs;VC;R11R10SaS85S86RfRbRdA3RcA2A1G3A6S9dQ40A1S2bS3aS9dQ8A1A1SaRaR1A2SaR10R1A2A3Fa;S73G2SaS106RaS6eR11RaRdA3A2A1A2F_;F_;F_;F_;F_;F_;F_;F_;F_;Frho';FmdL;Fmd;FR;Fs;Fms;FrhoL;Frho;FA';FAi;").
Proof using ML.
  intros Ai A' rho rhoL ms s R md mdL rho' HP HP' (HM & _ & HT) HM' HTK HRok HK Hkept Hrm a Ha Hp.
  pose proof (TPI_kept _ _ HTK HT) as HT'.
  cbn [rho_patch rm]. unfold patchf.
  destruct (in_ranges_dec rho R (Z_to_bv 64 a)) as [Hi|Hn]; [apply HK; assumption|].
  rewrite Hrm.
  pose proof (pclF_caddr Ai a HP HT Hp) as Hc.
  destruct (caddr_props Ai None a rho md ML HM Ha Hc) as (O1 & O2 & O3).
  destruct (caddr_props A' None a rhoL mdL ML HM' Ha (pclF_caddr A' a HP' HT' Hp)) as (O1' & _).
  transitivity (rm (rho_sub (rho_absorb rho R ms) s) (Z_to_bv 64 a)).
  - apply Hkept; try assumption; [exact (caddr_client _ _ _ Hc) | exact (caddr_client _ _ _ (pclF_caddr A' a HP' HT' Hp)) |]. intros Hs. apply O3. apply static_alloc_static. exact Hs.
  - rewrite rm_absorb_out by exact Hn. apply HK; assumption.
Qed.

Lemma KEPT_step : ltac2:(tb__ "0|2|
S7dS7dS1S1Se1S84S36S4A1S51S51Sb0Vsegs;VC;R9R7R2A5M0G0Se3RbS45S33A1M1R9R5A4S33Se4RdG1R1A3Se4RdG1R2A3F_;Fa;Sc4Vsegs;VC;RdRcSaS85S86RbR7R9A3R8A2A1SaRaA1A6S9dQ40A1S88RdR9R1A3S2bS3aS9dQ8A1A1SaRdR2A2SaS85S86ReRaRcA3RbA2R2A2A3F_;Fa;F_;F_;F_;F_;F_;FmdL;Fmd;FR;Fs;Fms;FrhoL;Frho;FA';FAi;").
Proof using ML.
  clear_sec. intros Ai A' rho rhoL ms s R md mdL HM HM' HRok Hsub Hkept a Hin.
  apply (robjs_in_ranges Ai None rho R) in Hin; [|exact HRok].
  rewrite <- (Z_to_bv_bv_unsigned 64 a).
  pose proof (bv_urange a) as Ha.
  destruct (caddr_props Ai None _ rho md ML HM Ha Hin) as (O1 & O2 & O3).
  destruct (caddr_props A' None _ rhoL mdL ML HM' Ha (Hsub _ Hin)) as (O1' & _).
  apply Hkept; try assumption; [exact (caddr_client _ _ _ Hin) | exact (caddr_client _ _ _ (Hsub _ Hin)) |]. intros Hs. apply O3. apply static_alloc_static. exact Hs.
Qed.

Lemma MInvR_cont : ltac2:(tb__ "0|1|
S7dS7dS1S1S1S51S36S4A1S2cSb0Vsegs;VC;R6R4R2A5S2cS63R6A1S5cR6A1A2A2Se3R8S45S33A1M0R6R2A4S33Se4RaG0R1A3Se4RaG0R2A3F_;Fa;S9dQ40A1S2bS3aS9dQ8A1A1SaR7R1A2SaR8R1A2A3Fa;S2cSb0Vsegs;VC;RaS106R7S6eR9R7R5A3A2R6A5S2cS63RaA1S5cRaA1A2A2F_;F_;F_;F_;FR;Fmd2;Frho';FrhoL;Frho;FA2;FAi;").
Proof using ML.
  clear_sec. intros Ai A2 rho rhoL rho' md2 R HM2 HRok Hsub Hrm.
  eapply MInvR_mem; [exact HM2| |reflexivity]. intros a Ha Ho. cbn [rho_patch rm]. unfold patchf.
  destruct (in_ranges_dec rho R (Z_to_bv 64 a)) as [Hi|Hn'].
  - exfalso. eapply (R_miss A2 None rho rhoL _ R a); [exact (MI1 _ _ _ HM2) | | exact Ha | exact Ho | exact Hi].
    intros o b Ho' Hr'. apply Hsub. exact (HRok o b Ho' Hr').
  - apply Hrm.
Qed.

Lemma fresh_not_old : ltac2:(tb__ "0|3|
S7dS9dQ40A1M0S3aS9dQ8A1A1F_;G0S37F_;S53S36S38S33S33A2M1A1M2G2S33S33G1S81VC;R9R8R7R6A5S2bG2S7fRaA1S40G1R6S3eG1S3bS33S33R4R3A4R5A3A3A3S8dZ0R4A2S77G1R4S40G1R8R7A3A3S2fS2bG1R5S3bS33S33R7R6A4A3A1F_;F_;F_;F_;Fbn;Fn;Fp;Fl2;Fl1;Fvm;Fwok;Frd;FA';").
Proof using .
  clear_sec. intros A' rd wok vm l1 l2 p n bn HM HE Hn Hin ->.
  pose proof (new_block_disjoint C A' rd wok vm l1 l2 (p, n) HM HE (p, n) Hin) as D.
  unfold MallocInv.ranges_disjoint in D. cbn [fst snd] in D. lia.
Qed.

Section CallT.
Variable TR : assn -> assn -> Prop.
Hypothesis TR_facts : ltac2:(tb__ "0|1|
S4aS2S1S99S8cS5S7R2A1S6R3A1A3VTR;S49Vsegs;R5R4R3A4R2A2M0F_;G0F_;FQ;Frho;FS;FJ;").
Hypothesis TR_ex : forall (A : Type) (J : A -> jpred) S rho (Q : assn),
  (forall x, TR (SPJ segs (J x) S rho) Q) -> TR (SPJ segs (fun r t m => exists x, J x r t m) S rho) Q.
Hypothesis TR_pre : ltac2:(tb__ "0|0|
S99S99S99S9aR3R1A1R5R2A1F_;Fw;VTR;R4R2A2VTR;R4R3A2F_;F_;FQ;FP';FP;").
Hypothesis TR_callP : ltac2:(tb__ "0|3|
S4aS4aS2S2S84S36S4A1M0S36S38S2Sa2A2M1A1S99S1S2bS3aG0A1ScdR7R6R5A3S3dG0R4A2A3S2bS37Sa7R8R7R6R5S8bG1S2S3cS2Sa2A2R4A4A5S39A3S1VTR;S49Vsegs;RbR9R1A4Sa4Vsegs;S3R9A1R1R6A4A2Frho1;S36S52A1M2Se1S51ScVsegs;R7RdS3bG2SfeR3SffR2R1A2A4A4R10R8R4R2A3R10S85S86R9RcR4A3RdA2R5R3A3F_;F_;Fmd;Fms;Ftr;S2Sa2G2Se1S51S1G2Se1S51S77G1S3bS2Sa2R9R8A4R10A3ScVsegs;RfR15S3bG2SfeR8SffR7R6A2A4A4R18R10R9R7A3Sa0S3R16A1S85S86R11R14R9A3R15A2R7A3ScVsegs;R8RdS3bG2SfeR7SffR6R5A2A4A4RdS85S86R13R16RbA3R17A2R9R8R6A4S2cSabR14RcR17R18R19RfRaA7S1SaaR15RdR18R19R1aR1bR10R1RbA9VTR;S49Vsegs;Sa9R10S85S86R16R19ReA3R1aA2RcA3Sa5R1aS3R1bA1R11S3R1cA1R19A5R2A4R17A2F_;Frho';A2F_;F_;F_;F_;F_;F_;Fmd';Fms';Ftr';FrhoL;Fmd;Fms;Ftr;FJL;FL;VTR;S49Vsegs;ReRcR6A4R7A2F_;F_;F_;F_;F_;Frho;FQ;FPosts;FR;Fs;FPre;FC;FJp;FJ;").
Hypothesis TR_callJ : ltac2:(tb__ "0|3|
S4aS4aS4aS4aS2S2S84S36S4A1M0S36S101A1S99S1S2bS3aG0A1ScdR7R6R5A3S3dG0R4A2A3S2bS37Sa6R8R7R6R5R4A5S39A3S1VTR;S49Vsegs;RdR9R1A4S4eVsegs;RcS3R9A1R1R6A5A2Frho1;S36S52A1M1Se1S51ScVsegs;R7RdS3bG1SfeR3SffR2R1A2A4A4R12R8R4R2A3R12S85S86R9RcR4A3RdA2R5R3A3F_;F_;Fmd;Fms;Ftr;S101S1S1G1Se1S51G1S51S77S101R8RfA3ScVsegs;ReR14S3bG1SfeR6SffR5R4A2A4A4R19RfR7R5A3SadR10R7R13R14R15R16S104RbA1RaR9A9R19RaR6R5A3R19RcR7R6A3F_;F_;F_;F_;F_;Fmd';Ftr';Fmd;Fms;Ftr;FrhoL;Frho';FL;S101S1S77S101R2RaA3S11S3RfA1M2R9R2A3VTR;S49Vsegs;R11Sa5ReG2S104R4A1S3R10A1RdA5R3A4RbA2F_;F_;Frho';FL;VTR;S49Vsegs;R11RdR7A4R8A2F_;F_;F_;F_;F_;F_;Frho;FQ;FPosts;FR;Fs;FPre;FC;FJc';FJp';FJp;FJ;").

Ltac clear_TR := try clear TR_callJ; try clear TR_callP; try clear TR_pre; try clear TR_ex; try clear TR_facts.

Theorem malloc_callT : ltac2:(tb__ "0|8|
S2S84S36S4A1M0S1S36S38S0S0A2M1A1S99S7dS1VTR;S49Vsegs;Sc3Vsegs;VC;R2VKc;A4SbdVE;A1M2R1A4Sa4Vsegs;S100R1Sc8Vsegs;VC;VE;R2VKc;A5A4A2Frho1;FAi;S2bS3aG0A1ScdR7G2R6A3S3dG0R5A2A3S2bS37S5eR8G2R7R6S3eS2SbaVE;A1M3S3eS2SbbVE;A1M4S44S2A1A3A3A5S39A3S2bS37SddVNP;S3R9A1A2S39A3S2bS37S57S3RaA1R6A2S39A3S2bS37SdS3RbA1S83RaPcM5A2A2S39A3S2bS0S83Sa3RbS100G4S3RcA1M6A4Sb1A2S9Sa1G6UaM7A2A1A3S7dS8cS5S7RbA1S6ReA1A3VP0f;Vrho0;A1Sa0VNP;Vrho0;RdA3S60R4A1S5dR5RfReA3S5bR10RfA2S5fR11R10A2S2dS1S1S2dS51S51Sb0Vsegs;VC;RaR2R1A5Lmd;A2LrhoM;A2Se2R13ScfS7eR9A1A1A2S2cSe3RaS45S33A1R14R15A4S8dZ0S9eQ40S8R14S83R16G5A2A2A2A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;FAi;S1VTR;S49Vsegs;S55RbA1S58RfReRdG3A4R1A4RaA2Frho';S1VTR;S49Vsegs;S55S3eG1S3bS0S0S9Sa1S3R10A1G7A2A1S83RfG5A2A4RcA3A1S58R10RfReG4A4R1A4RbA2Frho';VTR;S49Vsegs;S55RcA1R10RdA4RbA2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftv;Frho;FR;Fs;FCl;").
Proof using ML TR_callP TR_ex TR_facts TR_pre.
  intros Cl s R rho tv Q CALLEE He Hchk Hnf Hnb Hs12 Hres HR Tnull Tok.
  apply Pos.leb_le in Hnf.
  apply TR_facts. intros HF.
  apply (TR_ex MA (JGi tv)). intros Ai.
  eapply (TR_callP (JGi tv Ai) (J_alloc_pre segs C Ai Kc) Cl (Pre_malloc E) s R
            (Posts_malloc segs C E Ai Kc) Q rho He).
  - exact (call_checkT_P _ _ _ _ _ Hchk).
  - intros rho1. apply CALLEE.
  -
    intros tr ms md Hsm (Hav & Hk & HM & HP & (HN & HD & HZ) & HK & HP0). split; [|split; [exact Hk | split; [exact (tp_of_TPI _ _ _ _ _ _ _ _ _ Hav (proj2 (proj2 HM)) Hchk) | split; [exact (proj1 (proj2 HM)) | exact (top_of_TPI _ _ _ _ _ _ _ _ _ Hav (proj2 (proj2 HM)) Hchk)]]]].
    destruct (HR Ai HF HP0 Hav HP HN HD HZ (ex_intro _ rho (ex_intro _ md (MI1 _ _ _ HM))) (T_of_chk _ _ _ _ _ _ _ Hav (proj2 (proj2 HM)) Hchk)) as [HRok _].
    eapply MI1. eapply MInvR_mem; [exact HM| |reflexivity].
    intros a Ha Ho. apply rm_absorb_out. eapply (R_miss Ai None rho rho md R a (MI1 _ _ _ HM)); [exact HRok|exact Ha|exact Ho].
  -
    intros L JL tr ms md rhoL tr' ms' md' HinL Hsm HJ Hag1 HsmL HJL.
    destruct HJ as (Hav & Hk & HM & HP & (HN & HD & HZ) & HK & HP0).
    destruct (HR Ai HF HP0 Hav HP HN HD HZ (ex_intro _ rho (ex_intro _ md (MI1 _ _ _ HM))) (T_of_chk _ _ _ _ _ _ _ Hav (proj2 (proj2 HM)) Hchk)) as [HRok Hpos].
    cbn [Posts_malloc In] in HinL.
    destruct HinL as [HinL | [HinL | []]]; injection HinL as HL HJLe; subst L JL.
    +
      destruct HJL as (A' & HM' & HbA' & Hkept & Hinit & _).
      assert (HsubA' : forall a, caddr Ai None a -> caddr A' None a) by (intros a; apply (caddr_mono _ _ _ _ (init_kept_top _ _ Hinit)); intros b Hb; rewrite HbA'; exact Hb).
      split.
      * split; [exact (KEPT_step Ai A' rho rhoL ms s R md md' (MI1 _ _ _ HM) HM' HRok HsubA' Hkept)|].
        intros o' oR Hin' _. cbn in Hin'. destruct Hin'.
      * intros rho' Hlink.
        eapply TR_pre; [ | apply (Tnull (rho_patch rho' (patchf rho rho' R)))].
        intros w [Hsm' HJ']. cbn [J_ofP] in HJ'.
        destruct HJ' as (A2 & HM2 & HbA2 & Hkept2 & Hinit2 & Hk2).
        assert (Hag' : agree_vals (ss_next Cl) rho rho') by (destruct Hlink as (A & _); exact A).
        assert (HsubA : forall b, In b (ma_blocks Ai) -> In b (ma_blocks A2)) by (intros b Hb; rewrite HbA2; exact Hb).
        split; [exact (cont_smatch Cl (Pre_malloc E) _ s R rho rho' tr ms md w He Hsm eq_refl Hag' Hsm')|].
        exists A2. split; [|split; [exact Hk2|split; [|split; [|split; [split; [|split]|split; [|exact HP0]]]]]].
        -- eapply agree_vals_trans; [exact Hav|].
           eapply agree_vals_trans; [eapply agree_vals_le; [exact Hnf| exact Hag']| apply agree_vals_patch].
        -- eapply (MInvR_cont Ai); [exact (conj HM2 (conj (init_kept_init _ _ Hinit2 (proj1 (proj2 HM))) (TPI_kept _ _ (init_kept_top _ _ Hinit2) (proj2 (proj2 HM))))) | exact HRok | intros a; apply (caddr_mono _ _ _ _ (init_kept_top _ _ Hinit2)); exact HsubA | intros a; eapply call_linkP_rm; exact Hlink].
        -- intros b Hb. apply HsubA. exact (HP b Hb).
        -- apply (tvin_agree A2 (ss_next Cl) rho); [eapply agree_vals_trans; [exact Hag' | apply agree_vals_patch] | exact Hnb |].
           unfold tvin in HN |- *. apply Forall_forall. intros t Ht Hnz.
           destruct (proj1 (Forall_forall _ _) HN t Ht Hnz) as (X0 & X1 & X2). split; [exact X0|]. split; [apply HsubA; exact X1 | exact X2].
        -- apply (tvd_agree (ss_next Cl) rho); [eapply agree_vals_trans; [exact Hag' | apply agree_vals_patch] | exact Hnb | exact HD].
        -- apply (tvz_agree (ss_next Cl) rho); [eapply agree_vals_trans; [exact Hag' | apply agree_vals_patch] | exact Hnb | exact HZ].
        -- eapply (keptF_step Ai A2 rho rhoL ms s R md _ rho' HP); [intros b Hb; apply HsubA; exact (HP b Hb) | exact HM | exact HM2 | exact (init_kept_top _ _ Hinit2) | exact HRok | exact HK | exact Hkept2 | intros a; eapply call_linkP_rm; exact Hlink].
    +
      destruct HJL as (A' & l1 & l2 & HM' & HbA' & HbAi & Hkept & Hinit & _).
      assert (HsubA' : forall b, In b (ma_blocks Ai) -> In b (ma_blocks A')).
      { intros b Hb. rewrite HbA'. apply in_app_mid. rewrite <- HbAi. exact Hb. }
      set (p := bv_unsigned (rw rhoL V_RES)) in *.
      set (n := bv_unsigned (rw (rho_sub (rho_absorb rho R ms) s) 12%positive)) in *.
      assert (Hn12 : bv_unsigned (rw rhoL 12%positive) = n).
      { subst n. f_equal. symmetry. apply (proj1 Hag1). reflexivity. }
      assert (Hnrho : bv_unsigned (eval rho (wsub_get s 12)) = n) by (subst n; rewrite rw_call'; reflexivity).
      assert (HinNew : In (p, n) (ma_blocks A')) by (rewrite HbA'; apply in_or_app; right; left; reflexivity).
      pose proof HM' as HMi'. unfold MInvR in HMi'.
      pose proof (minv_block_geom C A' _ _ _ p n HMi' HinNew) as (G0 & _ & G2 & G3 & G4).
      unfold PGSZ, UNIT, IB in G2, G3. pose proof (topL_range (ma_L A')) as TR3.
      pose proof (init_kept_top _ _ Hinit) as TK. unfold top_kept in TK.
      assert (NEWFREE : forall a, p <= a < p + n -> caddr Ai None a -> False).
      { intros a Ha [Hc|[Hc|(b & m & Hb & _ & Hr)]].
        - destruct (block_addr_props A' _ _ _ p n a ML HMi' HinNew Ha) as [X _]. lia.
        - destruct Hc as (Hw & _). apply (ml_wseg ML) in Hw.
          rewrite Z_to_bv_unsigned, bv_wrap_small in Hw by (rewrite two64; lia).
          destruct (block_addr_props A' _ _ _ p n a ML HMi' HinNew Ha) as [_ X]. exact (X Hw).
        - pose proof (new_block_disjoint C A' _ _ _ l1 l2 (p, n) HMi' HbA' (b, m) ltac:(rewrite <- HbAi; exact Hb)) as D.
          unfold MallocInv.ranges_disjoint in D. cbn [fst snd] in D. lia. }
      split.
      * split.
        -- exact (KEPT_step Ai A' rho rhoL ms s R md md' (MI1 _ _ _ HM) HM' HRok ltac:(intros a; apply (caddr_mono _ _ _ _ (init_kept_top _ _ Hinit)); exact HsubA') Hkept).
        -- intros o' oR Hin' HinR. cbn in Hin'. destruct Hin' as [<-|[]].
           destruct (obj_range rho oR) as [lo hi] eqn:HR2.
           unfold obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi block_obj].
           rewrite soff_lit_small by lia. unfold soff. cbn [eval]. fold p.
           rewrite bv_signed_U, Hn12.
           apply ranges_disjoint_by_points. intros a Ha1 Ha2.
           apply (NEWFREE a).
           ++ destruct (Zsigned_spec n) as [[_ X]|[_ X]]; rewrite X in Ha1; lia.
           ++ apply (HRok oR a HinR). rewrite HR2. cbn [fst snd]. exact Ha2.
      * intros rho' Hlink.
        eapply TR_pre; [ | apply (Tok (rho_patch rho' (patchf rho rho' R)))].
        intros w [Hsm' HJ']. cbn [J_ofP] in HJ'.
        destruct HJ' as (A2 & k1 & k2 & HM2 & HbA2 & HbAi2 & Hkept2 & Hinit2 & Hk2).
        assert (Hag' : agree_vals (ss_next Cl) rho rho') by (destruct Hlink as (A & _); exact A).
        assert (HsubA : forall b, In b (ma_blocks Ai) -> In b (ma_blocks A2)).
        { intros b Hb. rewrite HbA2. apply in_app_mid. rewrite <- HbAi2. exact Hb. }
        assert (E1 : rw rho' (pos_add_nat (ss_next Cl) 10) = rw rhoL V_RES).
        { destruct Hlink as (_ & _ & _ & L4).
          specialize (L4 V_RES). change (ss_next (Pre_malloc E)) with NF in L4.
          rewrite Hres in L4. cbn [eval] in L4. symmetry. apply L4; [reflexivity | cbv; lia]. }
        assert (E2 : bv_unsigned (eval rho' (wsub_get s 12)) = n).
        { rewrite <- Hnrho. f_equal. symmetry. eapply eval_agree_vals; [exact Hag' | exact Hs12]. }
        assert (Enew : tvv (rho_patch rho' (patchf rho rho' R)) (SVar (pos_add_nat (ss_next Cl) 10), wsub_get s 12) = (p, n)).
        { unfold tvv. cbn [fst snd eval]. rewrite !eval_patch. cbn [eval rho_patch rw]. rewrite E1, E2. reflexivity. }
        assert (HMi2 : MInv C A2 (rd_of segs (rm rhoL)) (wok_of segs (rm rhoL)) (m_vmmaps (cfg_model (w_cfg w)))) by exact HM2.
        split; [exact (cont_smatch Cl (Pre_malloc E) _ s R rho rho' tr ms md w He Hsm eq_refl Hag' Hsm')|].
        exists A2. split; [|split; [exact Hk2|split; [|split; [|split; [split; [|split]|split; [|exact HP0]]]]]].
        -- eapply agree_vals_trans; [exact Hav|].
           eapply agree_vals_trans; [eapply agree_vals_le; [exact Hnf| exact Hag']| apply agree_vals_patch].
        -- eapply (MInvR_cont Ai); [exact (conj HM2 (conj (init_kept_init _ _ Hinit2 (proj1 (proj2 HM))) (TPI_kept _ _ (init_kept_top _ _ Hinit2) (proj2 (proj2 HM))))) | exact HRok | intros a; apply (caddr_mono _ _ _ _ (init_kept_top _ _ Hinit2)); exact HsubA | intros a; eapply call_linkP_rm; exact Hlink].
        -- intros b Hb. apply HsubA. exact (HP b Hb).
        --
           constructor.
           ++ intros _. rewrite Enew. cbn [snd]. split; [lia|]. split; [rewrite HbA2; apply in_or_app; right; left; reflexivity|].
              intros HinFB. apply (fresh_not_old A2 _ _ _ k1 k2 p n (p, n) HMi2 HbA2 ltac:(lia)); [|reflexivity].
              rewrite <- HbAi2. exact (HP _ HinFB).
           ++ apply (tvin_agree A2 (ss_next Cl) rho); [eapply agree_vals_trans; [exact Hag' | apply agree_vals_patch] | exact Hnb |].
              unfold tvin in HN |- *. apply Forall_forall. intros t Ht Hnz.
              destruct (proj1 (Forall_forall _ _) HN t Ht Hnz) as (X0 & X1 & X2). split; [exact X0|]. split; [apply HsubA; exact X1 | exact X2].
        --
           cbn [tvd]. split.
           ++ intros t' Ht' _ Hnz'. rewrite Enew.
              assert (Hbt : (sv_below (ss_next Cl) (fst t') && sv_below (ss_next Cl) (snd t')) = true) by exact (proj1 (forallb_forall _ _) Hnb t' Ht').
              assert (Hag'' : agree_vals (ss_next Cl) rho (rho_patch rho' (patchf rho rho' R))) by (eapply agree_vals_trans; [exact Hag' | apply agree_vals_patch]).
              rewrite (tvv_agree (ss_next Cl) rho _ t' Hag'' Hbt).
              apply (proj1 (tnz_agree (ss_next Cl) rho _ t' Hag'' Hbt)) in Hnz'.
              destruct (proj1 (Forall_forall _ _) HN t' Ht' Hnz') as (_ & X1 & _).
              intros Heq. apply (fresh_not_old A2 _ _ _ k1 k2 p n (tvv rho t') HMi2 HbA2 ltac:(lia)); [|symmetry; exact Heq].
              rewrite <- HbAi2. exact X1.
           ++ apply (tvd_agree (ss_next Cl) rho); [eapply agree_vals_trans; [exact Hag' | apply agree_vals_patch] | exact Hnb | exact HD].
        --
           constructor.
           ++ intros Hz. exfalso. apply Hz. unfold tnz. change (bv_unsigned (eval ?r (fst ?t))) with (fst (tvv r t)). rewrite Enew. cbn [fst]. lia.
           ++ apply (tvz_agree (ss_next Cl) rho); [eapply agree_vals_trans; [exact Hag' | apply agree_vals_patch] | exact Hnb | exact HZ].
        -- eapply (keptF_step Ai A2 rho rhoL ms s R md _ rho' HP); [intros b Hb; apply HsubA; exact (HP b Hb) | exact HM | exact HM2 | exact (init_kept_top _ _ Hinit2) | exact HRok | exact HK | exact Hkept2 | intros a; eapply call_linkP_rm; exact Hlink].
Qed.

Theorem calloc_callT : ltac2:(tb__ "0|d|
S2S84S36S4A1M0S1S36S38S0S0A2M1A1S99S7dS1VTR;S49Vsegs;Sc3Vsegs;VC;R2VKc;A4SbcVE;A1M2R1A4Sa4Vsegs;S100R1Sc7Vsegs;VC;VE;R2VKc;A5A4A2Frho1;FAi;S2bS3aG0A1ScdR7G2R6A3S3dG0R5A2A3S2bS37S5eR8G2R7R6S3eS2Sb2SbeVE;A1M3A1M4S3eS2Sb2SbfVE;A1A1M5S3eS2Sb3G3A1M6S3eS2Sb3Sc0VE;A1A1M7S44S2A1A3A3A3A3A5S39A3S2bS37SddVNP;S3R9A1A2S39A3S2bS37S57S3RaA1R6A2S39A3S2bS37SdS3RbA1S83RaPcM8A2A2S39A3S2bS37SdS3RcA1S83RbPdM9A2A2S39A3S2bS0S83Sa3RcS100G6S3RdA1MaA4Sb1A2S9Sa1GaUaMbA2A1A3S2bS0S83Sa3RdS100G7S3ReA1McA4Sb1A2S9Sa1GcGbA2A1A3S7dS8cS5S7RdA1S6R10A1A3VP0f;Vrho0;A1Sa0VNP;Vrho0;RfA3S60R4A1S5dR5R11R10A3S5bR12R11A2S5fR13R12A2S2dS1S1S2dS51S51Sb0Vsegs;VC;RaR2R1A5Lmd;A2LrhoM;A2Se2R15ScfS7eR9A1A1A2S2cSe3RaS45S33A1R16R17A4S8dZ0S9eQ40S8R16S10S109S83R18G8A2S83R18G9A2A3A2A2A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;FAi;S1VTR;S49Vsegs;S55RdA1S58R11R10RfG4A4R1A4RcA2Frho';S1VTR;S49Vsegs;S55ReA1S58R12R11R10G5A4R1A4RdA2Frho';S1VTR;S49Vsegs;S55S3eG1S3bS0S0S9Sa1S3R13A1GbA2A1S10S109S83R12G8A2S83R12G9A2A3A4RfA3A1S58R13R12R11G6A4R1A4ReA2Frho';S1VTR;S49Vsegs;S55S3eG1S3bS0S0S9Sa1S3R14A1GbA2A1S10S109S83R13G8A2S83R13G9A2A3A4R10A3A1S58R14R13R12G7A4R1A4RfA2Frho';VTR;S49Vsegs;S55R10A1R14R11A4RfA2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftv;Frho;FR;Fs;FCl;").
Proof using ML TR_callP TR_ex TR_facts TR_pre.
  intros Cl s R rho tv Q CALLEE He Hchk Hnf Hnb Hs12 Hs13 Hres Hres2 HR Tnull Tnull2 Tok Tok2.
  apply Pos.leb_le in Hnf.
  apply TR_facts. intros HF.
  apply (TR_ex MA (JGi tv)). intros Ai.
  eapply (TR_callP (JGi tv Ai) (J_alloc_pre segs C Ai Kc) Cl (Pre_calloc E) s R
            (Posts_calloc segs C E Ai Kc) Q rho He).
  - exact (call_checkT_P _ _ _ _ _ Hchk).
  - intros rho1. apply CALLEE.
  -
    intros tr ms md Hsm (Hav & Hk & HM & HP & (HN & HD & HZ) & HK & HP0). split; [|split; [exact Hk | split; [exact (tp_of_TPI _ _ _ _ _ _ _ _ _ Hav (proj2 (proj2 HM)) Hchk) | split; [exact (proj1 (proj2 HM)) | exact (top_of_TPI _ _ _ _ _ _ _ _ _ Hav (proj2 (proj2 HM)) Hchk)]]]].
    destruct (HR Ai HF HP0 Hav HP HN HD HZ (ex_intro _ rho (ex_intro _ md (MI1 _ _ _ HM))) (T_of_chk _ _ _ _ _ _ _ Hav (proj2 (proj2 HM)) Hchk)) as [HRok _].
    eapply MI1. eapply MInvR_mem; [exact HM| |reflexivity].
    intros a Ha Ho. apply rm_absorb_out. eapply (R_miss Ai None rho rho md R a (MI1 _ _ _ HM)); [exact HRok|exact Ha|exact Ho].
  -
    intros L JL tr ms md rhoL tr' ms' md' HinL Hsm HJ Hag1 HsmL HJL.
    destruct HJ as (Hav & Hk & HM & HP & (HN & HD & HZ) & HK & HP0).
    destruct (HR Ai HF HP0 Hav HP HN HD HZ (ex_intro _ rho (ex_intro _ md (MI1 _ _ _ HM))) (T_of_chk _ _ _ _ _ _ _ Hav (proj2 (proj2 HM)) Hchk)) as [HRok Hpos].
    cbn [Posts_calloc In] in HinL.
    destruct HinL as [HinL | [HinL | [HinL | [HinL | []]]]]; injection HinL as HL HJLe; subst L JL.
    +
      destruct HJL as (A' & HM' & HbA' & Hkept & Hinit & _).
      assert (HsubA' : forall a, caddr Ai None a -> caddr A' None a) by (intros a; apply (caddr_mono _ _ _ _ (init_kept_top _ _ Hinit)); intros b Hb; rewrite HbA'; exact Hb).
      split.
      * split; [exact (KEPT_step Ai A' rho rhoL ms s R md md' (MI1 _ _ _ HM) HM' HRok HsubA' Hkept)|].
        intros o' oR Hin' _. cbn in Hin'. destruct Hin'.
      * intros rho' Hlink.
        eapply TR_pre; [ | apply (Tnull (rho_patch rho' (patchf rho rho' R)))].
        intros w [Hsm' HJ']. cbn [J_ofP] in HJ'.
        destruct HJ' as (A2 & HM2 & HbA2 & Hkept2 & Hinit2 & Hk2).
        assert (Hag' : agree_vals (ss_next Cl) rho rho') by (destruct Hlink as (A & _); exact A).
        assert (HsubA : forall b, In b (ma_blocks Ai) -> In b (ma_blocks A2)) by (intros b Hb; rewrite HbA2; exact Hb).
        split; [exact (cont_smatch Cl (Pre_calloc E) _ s R rho rho' tr ms md w He Hsm eq_refl Hag' Hsm')|].
        exists A2. split; [|split; [exact Hk2|split; [|split; [|split; [split; [|split]|split; [|exact HP0]]]]]].
        -- eapply agree_vals_trans; [exact Hav|].
           eapply agree_vals_trans; [eapply agree_vals_le; [exact Hnf| exact Hag']| apply agree_vals_patch].
        -- eapply (MInvR_cont Ai); [exact (conj HM2 (conj (init_kept_init _ _ Hinit2 (proj1 (proj2 HM))) (TPI_kept _ _ (init_kept_top _ _ Hinit2) (proj2 (proj2 HM))))) | exact HRok | intros a; apply (caddr_mono _ _ _ _ (init_kept_top _ _ Hinit2)); exact HsubA | intros a; eapply call_linkP_rm; exact Hlink].
        -- intros b Hb. apply HsubA. exact (HP b Hb).
        -- apply (tvin_agree A2 (ss_next Cl) rho); [eapply agree_vals_trans; [exact Hag' | apply agree_vals_patch] | exact Hnb |].
           unfold tvin in HN |- *. apply Forall_forall. intros t Ht Hnz.
           destruct (proj1 (Forall_forall _ _) HN t Ht Hnz) as (X0 & X1 & X2). split; [exact X0|]. split; [apply HsubA; exact X1 | exact X2].
        -- apply (tvd_agree (ss_next Cl) rho); [eapply agree_vals_trans; [exact Hag' | apply agree_vals_patch] | exact Hnb | exact HD].
        -- apply (tvz_agree (ss_next Cl) rho); [eapply agree_vals_trans; [exact Hag' | apply agree_vals_patch] | exact Hnb | exact HZ].
        -- eapply (keptF_step Ai A2 rho rhoL ms s R md _ rho' HP); [intros b Hb; apply HsubA; exact (HP b Hb) | exact HM | exact HM2 | exact (init_kept_top _ _ Hinit2) | exact HRok | exact HK | exact Hkept2 | intros a; eapply call_linkP_rm; exact Hlink].
    +
      destruct HJL as (A' & HM' & HbA' & Hkept & Hinit & _).
      assert (HsubA' : forall a, caddr Ai None a -> caddr A' None a) by (intros a; apply (caddr_mono _ _ _ _ (init_kept_top _ _ Hinit)); intros b Hb; rewrite HbA'; exact Hb).
      split.
      * split; [exact (KEPT_step Ai A' rho rhoL ms s R md md' (MI1 _ _ _ HM) HM' HRok HsubA' Hkept)|].
        intros o' oR Hin' _. cbn in Hin'. destruct Hin'.
      * intros rho' Hlink.
        eapply TR_pre; [ | apply (Tnull2 (rho_patch rho' (patchf rho rho' R)))].
        intros w [Hsm' HJ']. cbn [J_ofP] in HJ'.
        destruct HJ' as (A2 & HM2 & HbA2 & Hkept2 & Hinit2 & Hk2).
        assert (Hag' : agree_vals (ss_next Cl) rho rho') by (destruct Hlink as (A & _); exact A).
        assert (HsubA : forall b, In b (ma_blocks Ai) -> In b (ma_blocks A2)) by (intros b Hb; rewrite HbA2; exact Hb).
        split; [exact (cont_smatch Cl (Pre_calloc E) _ s R rho rho' tr ms md w He Hsm eq_refl Hag' Hsm')|].
        exists A2. split; [|split; [exact Hk2|split; [|split; [|split; [split; [|split]|split; [|exact HP0]]]]]].
        -- eapply agree_vals_trans; [exact Hav|].
           eapply agree_vals_trans; [eapply agree_vals_le; [exact Hnf| exact Hag']| apply agree_vals_patch].
        -- eapply (MInvR_cont Ai); [exact (conj HM2 (conj (init_kept_init _ _ Hinit2 (proj1 (proj2 HM))) (TPI_kept _ _ (init_kept_top _ _ Hinit2) (proj2 (proj2 HM))))) | exact HRok | intros a; apply (caddr_mono _ _ _ _ (init_kept_top _ _ Hinit2)); exact HsubA | intros a; eapply call_linkP_rm; exact Hlink].
        -- intros b Hb. apply HsubA. exact (HP b Hb).
        -- apply (tvin_agree A2 (ss_next Cl) rho); [eapply agree_vals_trans; [exact Hag' | apply agree_vals_patch] | exact Hnb |].
           unfold tvin in HN |- *. apply Forall_forall. intros t Ht Hnz.
           destruct (proj1 (Forall_forall _ _) HN t Ht Hnz) as (X0 & X1 & X2). split; [exact X0|]. split; [apply HsubA; exact X1 | exact X2].
        -- apply (tvd_agree (ss_next Cl) rho); [eapply agree_vals_trans; [exact Hag' | apply agree_vals_patch] | exact Hnb | exact HD].
        -- apply (tvz_agree (ss_next Cl) rho); [eapply agree_vals_trans; [exact Hag' | apply agree_vals_patch] | exact Hnb | exact HZ].
        -- eapply (keptF_step Ai A2 rho rhoL ms s R md _ rho' HP); [intros b Hb; apply HsubA; exact (HP b Hb) | exact HM | exact HM2 | exact (init_kept_top _ _ Hinit2) | exact HRok | exact HK | exact Hkept2 | intros a; eapply call_linkP_rm; exact Hlink].
    +
      destruct HJL as (A' & l1 & l2 & HM' & HbA' & HbAi & Hkept & Hinit & _).
      assert (HsubA' : forall b, In b (ma_blocks Ai) -> In b (ma_blocks A')).
      { intros b Hb. rewrite HbA'. apply in_app_mid. rewrite <- HbAi. exact Hb. }
      set (p := bv_unsigned (rw rhoL V_RES)) in *.
      set (n := bv_unsigned (rw (rho_sub (rho_absorb rho R ms) s) 12%positive)
                * bv_unsigned (rw (rho_sub (rho_absorb rho R ms) s) 13%positive)) in *.
      assert (Hn12' : bv_unsigned (rw rhoL 12%positive) * bv_unsigned (rw rhoL 13%positive) = n).
      { subst n. rewrite <- (proj1 Hag1 12%positive), <- (proj1 Hag1 13%positive) by reflexivity. reflexivity. }
      assert (Hpos' : 0 < n).
      { rewrite U_mul in Hpos. rewrite <- (rw_call' rho R ms s 12), <- (rw_call' rho R ms s 13) in Hpos. fold n in Hpos.
        pose proof (bv_urange (rw (rho_sub (rho_absorb rho R ms) s) 12%positive)) as R12.
        pose proof (bv_urange (rw (rho_sub (rho_absorb rho R ms) s) 13%positive)) as R13.
        assert (0 <= n) by (subst n; apply Z.mul_nonneg_nonneg; lia).
        pose proof (Z.mod_le n M64v ltac:(lia) ltac:(unfold M64v; lia)). lia. }
      assert (HinNew : In (p, n) (ma_blocks A')) by (rewrite HbA'; apply in_or_app; right; left; reflexivity).
      pose proof HM' as HMi'. unfold MInvR in HMi'.
      pose proof (minv_block_geom C A' _ _ _ p n HMi' HinNew) as (G0 & _ & G2 & G3 & G4).
      unfold PGSZ, UNIT, IB in G2, G3. pose proof (topL_range (ma_L A')) as TR3.
      pose proof (init_kept_top _ _ Hinit) as TK. unfold top_kept in TK.
      assert (NEWFREE : forall a, p <= a < p + n -> caddr Ai None a -> False).
      { intros a Ha [Hc|[Hc|(b & m & Hb & _ & Hr)]].
        - destruct (block_addr_props A' _ _ _ p n a ML HMi' HinNew Ha) as [X _]. lia.
        - destruct Hc as (Hw & _). apply (ml_wseg ML) in Hw.
          rewrite Z_to_bv_unsigned, bv_wrap_small in Hw by (rewrite two64; lia).
          destruct (block_addr_props A' _ _ _ p n a ML HMi' HinNew Ha) as [_ X]. exact (X Hw).
        - pose proof (new_block_disjoint C A' _ _ _ l1 l2 (p, n) HMi' HbA' (b, m) ltac:(rewrite <- HbAi; exact Hb)) as D.
          unfold MallocInv.ranges_disjoint in D. cbn [fst snd] in D. lia. }
      split.
      * split.
        -- exact (KEPT_step Ai A' rho rhoL ms s R md md' (MI1 _ _ _ HM) HM' HRok ltac:(intros a; apply (caddr_mono _ _ _ _ (init_kept_top _ _ Hinit)); exact HsubA') Hkept).
        -- intros o' oR Hin' HinR. cbn in Hin'. destruct Hin' as [<-|[]].
           destruct (obj_range rho oR) as [lo hi] eqn:HR2.
           unfold obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi block_obj].
           rewrite soff_lit_small by lia. unfold soff, calloc_size. fold p.
           rewrite bv_signed_U, U_mul. cbn [eval]. rewrite Hn12'.
           rewrite Z.mod_small by (unfold M64v; lia).
           apply ranges_disjoint_by_points. intros a Ha1 Ha2.
           apply (NEWFREE a).
           ++ destruct (Zsigned_spec n) as [[_ X]|[_ X]]; rewrite X in Ha1; lia.
           ++ apply (HRok oR a HinR). rewrite HR2. cbn [fst snd]. exact Ha2.
      * intros rho' Hlink.
        eapply TR_pre; [ | apply (Tok (rho_patch rho' (patchf rho rho' R)))].
        intros w [Hsm' HJ']. cbn [J_ofP] in HJ'.
        destruct HJ' as (A2 & k1 & k2 & HM2 & HbA2 & HbAi2 & Hkept2 & Hinit2 & Hk2).
        assert (Hag' : agree_vals (ss_next Cl) rho rho') by (destruct Hlink as (A & _); exact A).
        assert (HsubA : forall b, In b (ma_blocks Ai) -> In b (ma_blocks A2)).
        { intros b Hb. rewrite HbA2. apply in_app_mid. rewrite <- HbAi2. exact Hb. }
        assert (E1 : rw rho' (pos_add_nat (ss_next Cl) 10) = rw rhoL V_RES).
        { destruct Hlink as (_ & _ & _ & L4).
          specialize (L4 V_RES). change (ss_next (Pre_calloc E)) with NF in L4.
          rewrite Hres in L4. cbn [eval] in L4. symmetry. apply L4; [reflexivity | cbv; lia]. }
        assert (E2 : bv_unsigned (eval rho' (SMd M_MUL (wsub_get s 12) (wsub_get s 13))) = n).
        { rewrite U_mul.
          rewrite <- (eval_agree_vals _ _ _ _ Hag' Hs12), <- (eval_agree_vals _ _ _ _ Hag' Hs13).
          rewrite <- (rw_call' rho R ms s 12), <- (rw_call' rho R ms s 13). fold n.
          apply Z.mod_small. unfold M64v. lia. }
        assert (Enew : tvv (rho_patch rho' (patchf rho rho' R)) (SVar (pos_add_nat (ss_next Cl) 10), SMd M_MUL (wsub_get s 12) (wsub_get s 13)) = (p, n)).
        { unfold tvv. cbn [fst snd]. rewrite !eval_patch. rewrite E2. cbn [eval rho_patch rw]. rewrite E1. reflexivity. }
        assert (HMi2 : MInv C A2 (rd_of segs (rm rhoL)) (wok_of segs (rm rhoL)) (m_vmmaps (cfg_model (w_cfg w)))) by exact HM2.
        split; [exact (cont_smatch Cl (Pre_calloc E) _ s R rho rho' tr ms md w He Hsm eq_refl Hag' Hsm')|].
        exists A2. split; [|split; [exact Hk2|split; [|split; [|split; [split; [|split]|split; [|exact HP0]]]]]].
        -- eapply agree_vals_trans; [exact Hav|].
           eapply agree_vals_trans; [eapply agree_vals_le; [exact Hnf| exact Hag']| apply agree_vals_patch].
        -- eapply (MInvR_cont Ai); [exact (conj HM2 (conj (init_kept_init _ _ Hinit2 (proj1 (proj2 HM))) (TPI_kept _ _ (init_kept_top _ _ Hinit2) (proj2 (proj2 HM))))) | exact HRok | intros a; apply (caddr_mono _ _ _ _ (init_kept_top _ _ Hinit2)); exact HsubA | intros a; eapply call_linkP_rm; exact Hlink].
        -- intros b Hb. apply HsubA. exact (HP b Hb).
        --
           constructor.
           ++ intros _. rewrite Enew. cbn [snd]. split; [lia|]. split; [rewrite HbA2; apply in_or_app; right; left; reflexivity|].
              intros HinFB. apply (fresh_not_old A2 _ _ _ k1 k2 p n (p, n) HMi2 HbA2 ltac:(lia)); [|reflexivity].
              rewrite <- HbAi2. exact (HP _ HinFB).
           ++ apply (tvin_agree A2 (ss_next Cl) rho); [eapply agree_vals_trans; [exact Hag' | apply agree_vals_patch] | exact Hnb |].
              unfold tvin in HN |- *. apply Forall_forall. intros t Ht Hnz.
              destruct (proj1 (Forall_forall _ _) HN t Ht Hnz) as (X0 & X1 & X2). split; [exact X0|]. split; [apply HsubA; exact X1 | exact X2].
        --
           cbn [tvd]. split.
           ++ intros t' Ht' _ Hnz'. rewrite Enew.
              assert (Hbt : (sv_below (ss_next Cl) (fst t') && sv_below (ss_next Cl) (snd t')) = true) by exact (proj1 (forallb_forall _ _) Hnb t' Ht').
              assert (Hag'' : agree_vals (ss_next Cl) rho (rho_patch rho' (patchf rho rho' R))) by (eapply agree_vals_trans; [exact Hag' | apply agree_vals_patch]).
              rewrite (tvv_agree (ss_next Cl) rho _ t' Hag'' Hbt).
              apply (proj1 (tnz_agree (ss_next Cl) rho _ t' Hag'' Hbt)) in Hnz'.
              destruct (proj1 (Forall_forall _ _) HN t' Ht' Hnz') as (_ & X1 & _).
              intros Heq. apply (fresh_not_old A2 _ _ _ k1 k2 p n (tvv rho t') HMi2 HbA2 ltac:(lia)); [|symmetry; exact Heq].
              rewrite <- HbAi2. exact X1.
           ++ apply (tvd_agree (ss_next Cl) rho); [eapply agree_vals_trans; [exact Hag' | apply agree_vals_patch] | exact Hnb | exact HD].
        --
           constructor.
           ++ intros Hz. exfalso. apply Hz. unfold tnz. change (bv_unsigned (eval ?r (fst ?t))) with (fst (tvv r t)). rewrite Enew. cbn [fst]. lia.
           ++ apply (tvz_agree (ss_next Cl) rho); [eapply agree_vals_trans; [exact Hag' | apply agree_vals_patch] | exact Hnb | exact HZ].
        -- eapply (keptF_step Ai A2 rho rhoL ms s R md _ rho' HP); [intros b Hb; apply HsubA; exact (HP b Hb) | exact HM | exact HM2 | exact (init_kept_top _ _ Hinit2) | exact HRok | exact HK | exact Hkept2 | intros a; eapply call_linkP_rm; exact Hlink].
    +
      destruct HJL as (A' & l1 & l2 & HM' & HbA' & HbAi & Hkept & Hinit & _).
      assert (HsubA' : forall b, In b (ma_blocks Ai) -> In b (ma_blocks A')).
      { intros b Hb. rewrite HbA'. apply in_app_mid. rewrite <- HbAi. exact Hb. }
      set (p := bv_unsigned (rw rhoL V_RES)) in *.
      set (n := bv_unsigned (rw (rho_sub (rho_absorb rho R ms) s) 12%positive)
                * bv_unsigned (rw (rho_sub (rho_absorb rho R ms) s) 13%positive)) in *.
      assert (Hn12' : bv_unsigned (rw rhoL 12%positive) * bv_unsigned (rw rhoL 13%positive) = n).
      { subst n. rewrite <- (proj1 Hag1 12%positive), <- (proj1 Hag1 13%positive) by reflexivity. reflexivity. }
      assert (Hpos' : 0 < n).
      { rewrite U_mul in Hpos. rewrite <- (rw_call' rho R ms s 12), <- (rw_call' rho R ms s 13) in Hpos. fold n in Hpos.
        pose proof (bv_urange (rw (rho_sub (rho_absorb rho R ms) s) 12%positive)) as R12.
        pose proof (bv_urange (rw (rho_sub (rho_absorb rho R ms) s) 13%positive)) as R13.
        assert (0 <= n) by (subst n; apply Z.mul_nonneg_nonneg; lia).
        pose proof (Z.mod_le n M64v ltac:(lia) ltac:(unfold M64v; lia)). lia. }
      assert (HinNew : In (p, n) (ma_blocks A')) by (rewrite HbA'; apply in_or_app; right; left; reflexivity).
      pose proof HM' as HMi'. unfold MInvR in HMi'.
      pose proof (minv_block_geom C A' _ _ _ p n HMi' HinNew) as (G0 & _ & G2 & G3 & G4).
      unfold PGSZ, UNIT, IB in G2, G3. pose proof (topL_range (ma_L A')) as TR3.
      pose proof (init_kept_top _ _ Hinit) as TK. unfold top_kept in TK.
      assert (NEWFREE : forall a, p <= a < p + n -> caddr Ai None a -> False).
      { intros a Ha [Hc|[Hc|(b & m & Hb & _ & Hr)]].
        - destruct (block_addr_props A' _ _ _ p n a ML HMi' HinNew Ha) as [X _]. lia.
        - destruct Hc as (Hw & _). apply (ml_wseg ML) in Hw.
          rewrite Z_to_bv_unsigned, bv_wrap_small in Hw by (rewrite two64; lia).
          destruct (block_addr_props A' _ _ _ p n a ML HMi' HinNew Ha) as [_ X]. exact (X Hw).
        - pose proof (new_block_disjoint C A' _ _ _ l1 l2 (p, n) HMi' HbA' (b, m) ltac:(rewrite <- HbAi; exact Hb)) as D.
          unfold MallocInv.ranges_disjoint in D. cbn [fst snd] in D. lia. }
      split.
      * split.
        -- exact (KEPT_step Ai A' rho rhoL ms s R md md' (MI1 _ _ _ HM) HM' HRok ltac:(intros a; apply (caddr_mono _ _ _ _ (init_kept_top _ _ Hinit)); exact HsubA') Hkept).
        -- intros o' oR Hin' HinR. cbn in Hin'. destruct Hin' as [<-|[]].
           destruct (obj_range rho oR) as [lo hi] eqn:HR2.
           unfold obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi block_obj].
           rewrite soff_lit_small by lia. unfold soff, calloc_size. fold p.
           rewrite bv_signed_U, U_mul. cbn [eval]. rewrite Hn12'.
           rewrite Z.mod_small by (unfold M64v; lia).
           apply ranges_disjoint_by_points. intros a Ha1 Ha2.
           apply (NEWFREE a).
           ++ destruct (Zsigned_spec n) as [[_ X]|[_ X]]; rewrite X in Ha1; lia.
           ++ apply (HRok oR a HinR). rewrite HR2. cbn [fst snd]. exact Ha2.
      * intros rho' Hlink.
        eapply TR_pre; [ | apply (Tok2 (rho_patch rho' (patchf rho rho' R)))].
        intros w [Hsm' HJ']. cbn [J_ofP] in HJ'.
        destruct HJ' as (A2 & k1 & k2 & HM2 & HbA2 & HbAi2 & Hkept2 & Hinit2 & Hk2).
        assert (Hag' : agree_vals (ss_next Cl) rho rho') by (destruct Hlink as (A & _); exact A).
        assert (HsubA : forall b, In b (ma_blocks Ai) -> In b (ma_blocks A2)).
        { intros b Hb. rewrite HbA2. apply in_app_mid. rewrite <- HbAi2. exact Hb. }
        assert (E1 : rw rho' (pos_add_nat (ss_next Cl) 10) = rw rhoL V_RES).
        { destruct Hlink as (_ & _ & _ & L4).
          specialize (L4 V_RES). change (ss_next (Pre_calloc E)) with NF in L4.
          rewrite Hres2 in L4. cbn [eval] in L4. symmetry. apply L4; [reflexivity | cbv; lia]. }
        assert (E2 : bv_unsigned (eval rho' (SMd M_MUL (wsub_get s 12) (wsub_get s 13))) = n).
        { rewrite U_mul.
          rewrite <- (eval_agree_vals _ _ _ _ Hag' Hs12), <- (eval_agree_vals _ _ _ _ Hag' Hs13).
          rewrite <- (rw_call' rho R ms s 12), <- (rw_call' rho R ms s 13). fold n.
          apply Z.mod_small. unfold M64v. lia. }
        assert (Enew : tvv (rho_patch rho' (patchf rho rho' R)) (SVar (pos_add_nat (ss_next Cl) 10), SMd M_MUL (wsub_get s 12) (wsub_get s 13)) = (p, n)).
        { unfold tvv. cbn [fst snd]. rewrite !eval_patch. rewrite E2. cbn [eval rho_patch rw]. rewrite E1. reflexivity. }
        assert (HMi2 : MInv C A2 (rd_of segs (rm rhoL)) (wok_of segs (rm rhoL)) (m_vmmaps (cfg_model (w_cfg w)))) by exact HM2.
        split; [exact (cont_smatch Cl (Pre_calloc E) _ s R rho rho' tr ms md w He Hsm eq_refl Hag' Hsm')|].
        exists A2. split; [|split; [exact Hk2|split; [|split; [|split; [split; [|split]|split; [|exact HP0]]]]]].
        -- eapply agree_vals_trans; [exact Hav|].
           eapply agree_vals_trans; [eapply agree_vals_le; [exact Hnf| exact Hag']| apply agree_vals_patch].
        -- eapply (MInvR_cont Ai); [exact (conj HM2 (conj (init_kept_init _ _ Hinit2 (proj1 (proj2 HM))) (TPI_kept _ _ (init_kept_top _ _ Hinit2) (proj2 (proj2 HM))))) | exact HRok | intros a; apply (caddr_mono _ _ _ _ (init_kept_top _ _ Hinit2)); exact HsubA | intros a; eapply call_linkP_rm; exact Hlink].
        -- intros b Hb. apply HsubA. exact (HP b Hb).
        --
           constructor.
           ++ intros _. rewrite Enew. cbn [snd]. split; [lia|]. split; [rewrite HbA2; apply in_or_app; right; left; reflexivity|].
              intros HinFB. apply (fresh_not_old A2 _ _ _ k1 k2 p n (p, n) HMi2 HbA2 ltac:(lia)); [|reflexivity].
              rewrite <- HbAi2. exact (HP _ HinFB).
           ++ apply (tvin_agree A2 (ss_next Cl) rho); [eapply agree_vals_trans; [exact Hag' | apply agree_vals_patch] | exact Hnb |].
              unfold tvin in HN |- *. apply Forall_forall. intros t Ht Hnz.
              destruct (proj1 (Forall_forall _ _) HN t Ht Hnz) as (X0 & X1 & X2). split; [exact X0|]. split; [apply HsubA; exact X1 | exact X2].
        --
           cbn [tvd]. split.
           ++ intros t' Ht' _ Hnz'. rewrite Enew.
              assert (Hbt : (sv_below (ss_next Cl) (fst t') && sv_below (ss_next Cl) (snd t')) = true) by exact (proj1 (forallb_forall _ _) Hnb t' Ht').
              assert (Hag'' : agree_vals (ss_next Cl) rho (rho_patch rho' (patchf rho rho' R))) by (eapply agree_vals_trans; [exact Hag' | apply agree_vals_patch]).
              rewrite (tvv_agree (ss_next Cl) rho _ t' Hag'' Hbt).
              apply (proj1 (tnz_agree (ss_next Cl) rho _ t' Hag'' Hbt)) in Hnz'.
              destruct (proj1 (Forall_forall _ _) HN t' Ht' Hnz') as (_ & X1 & _).
              intros Heq. apply (fresh_not_old A2 _ _ _ k1 k2 p n (tvv rho t') HMi2 HbA2 ltac:(lia)); [|symmetry; exact Heq].
              rewrite <- HbAi2. exact X1.
           ++ apply (tvd_agree (ss_next Cl) rho); [eapply agree_vals_trans; [exact Hag' | apply agree_vals_patch] | exact Hnb | exact HD].
        --
           constructor.
           ++ intros Hz. exfalso. apply Hz. unfold tnz. change (bv_unsigned (eval ?r (fst ?t))) with (fst (tvv r t)). rewrite Enew. cbn [fst]. lia.
           ++ apply (tvz_agree (ss_next Cl) rho); [eapply agree_vals_trans; [exact Hag' | apply agree_vals_patch] | exact Hnb | exact HZ].
        -- eapply (keptF_step Ai A2 rho rhoL ms s R md _ rho' HP); [intros b Hb; apply HsubA; exact (HP b Hb) | exact HM | exact HM2 | exact (init_kept_top _ _ Hinit2) | exact HRok | exact HK | exact Hkept2 | intros a; eapply call_linkP_rm; exact Hlink].
Qed.

Fixpoint remove_nth {A} (i : nat) (l : list A) : list A :=
  match l, i with
  | [], _ => []
  | _ :: r, O => r
  | x :: r, S i' => x :: remove_nth i' r
  end.

Lemma remove_nth_In {A} : ltac2:(tb__ "0|0|
S36VA;A1S41VA;S77VA;R1S125VA;R2R3A3A3S77VA;R2R4A3F_;Fx;Fi;Fl;").
Proof using .
  clear_sec.
  induction l as [|h r IH]; intros [|i] x H; cbn in H; try destruct H; try (destruct H as [<-|H]); cbn; auto.
  right. eapply IH. exact H.
Qed.

Lemma tvd_remove : ltac2:(tb__ "0|1|
S1S36S38S0S0A2M0A1S41S5bR3R2A2S5bR4S125G0R2R3A3A2F_;Fi;Ftv;Frho;").
Proof using .
  clear_sec.
  intros rho tv. induction tv as [|t r IH]; intros [|i] H; cbn in *; try exact I; destruct H as [H1 H2]; [exact H2|].
  split; [|apply IH; exact H2]. intros t' Hin'. apply H1. eapply remove_nth_In. exact Hin'.
Qed.

Lemma tvd_nth_distinct : ltac2:(tb__ "0|1|
S1S36S38S0S0A2M0A1S41G0G0S5bR5R4A2S2bS3aG0A1S78G0R5R4A3S3dG0R3A2A3S77G0R3S125G0R5R6A3A3S59R8R5A2S59R9R5A2S2fS2bS38S33S33A2S5aRaR6A2S5aRaR7A2A3A1F_;F_;F_;F_;F_;Ft';Ft;Fi;Ftv;Frho;").
Proof using .
  clear_sec.
  intros rho tv. induction tv as [|h r IH]; intros [|i] t t' HD Hn Hin Hz Hz'; cbn in Hn; try discriminate.
  - injection Hn as <-. cbn in Hin. destruct HD as [H1 _]. intros Heq. exact (H1 t' Hin Hz Hz' (eq_sym Heq)).
  - cbn in Hin. destruct HD as [H1 H2]. destruct Hin as [<-|Hin].
    + apply H1; [eapply nth_error_In; exact Hn | exact Hz' | exact Hz].
    + eapply IH; eauto.
Qed.

Theorem free_callT : ltac2:(tb__ "0|7|
S2S84S36S4A1M0S1S36S38S0S0A2M1A1S41G1S99S7dS1VTR;S49Vsegs;Sc6Vsegs;VC;R2VKc;A4Sb8VE;A1M2R1A4Sa4Vsegs;S100R1S3eS38S2Sa2A2M3S3bS2Sa2Sb7VE;A1M4Sc5Vsegs;VC;R2VKc;A4A4S44G3A1A3A4A2Frho1;FAi;S2bS3aG0A1ScdR9G2R8A3S3dG0R7A2A3S2bS37S5eRaG2R9R8S3eS2G4S44S2A1A3A5S39A3S2bS37SddVNP;S3RbA1A2S39A3S2bS37S57S3RcA1R8A2S39A3S2bS3aG1A1S78G1R9R8A3S3dG1R7A2A3S7dS8cS5S7RcA1S6RfA1A3VP0f;Vrho0;A1Sa0VNP;Vrho0;ReA3S60R4A1S5dR5R10RfA3S5bR11R10A2S5fR12R11A2S2dS1S1S2dS51S51Sb0Vsegs;VC;RaR2R1A5Lmd;A2LrhoM;A2Se2R14ScfS7eR9A1A1A2S2cS59R15R12A2S2cS2bS38S33S33A2S5aR15R12A2S3bS33S33S9eQ40M5S8R15S83R17PcA2A2A2M6S9eG5S8R15S83R17PdA2A2A2A4A3Se3RaS3dS33G6A2R15R16A4A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;FAi;S1VTR;S49Vsegs;S55S125G1RbRcA3A1S58R10RfReG4A4R1A4R9A2Frho';VTR;S49Vsegs;S55RcA1R10RdA4R9A2F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ft;Fi;Ftv;Frho;FR;Fs;FCl;").
Proof using ML TR_callP TR_ex TR_facts TR_pre.
  intros Cl s R rho tv i t Q CALLEE He Hchk Hnf Hnb Hnth HR Tfree.
  apply Pos.leb_le in Hnf.
  apply TR_facts. intros HF.
  apply (TR_ex MA (JGi tv)). intros Ai.
  eapply (TR_callP (JGi tv Ai) (J_free_pre segs C Ai Kc) Cl (Pre_free E) s R
            [(L_free E, JL_free segs C Ai Kc)] Q rho He).
  - exact (call_checkT_P _ _ _ _ _ Hchk).
  - intros rho1. apply CALLEE.
  -
    intros tr ms md Hsm (Hav & Hk & HM & HP & (HN & HD & HZ) & HK & HP0).
    destruct (HR Ai HF HP0 Hav HP HN HD HZ (ex_intro _ rho (ex_intro _ md (MI1 _ _ _ HM))) (T_of_chk _ _ _ _ _ _ _ Hav (proj2 (proj2 HM)) Hchk)) as (Hnz & Ht & HRok).
    destruct (proj1 (Forall_forall _ _) HN t (nth_error_In _ _ Hnth) Hnz) as (Tpos & Tin & Tfb).
    split; [|split; [|split; [exact Hk | split; [exact (tp_of_TPI _ _ _ _ _ _ _ _ _ Hav (proj2 (proj2 HM)) Hchk) | split; [exact (proj1 (proj2 HM)) | exact (top_of_TPI _ _ _ _ _ _ _ _ _ Hav (proj2 (proj2 HM)) Hchk)]]]]].
    + eapply MI1. eapply MInvR_mem; [exact HM| |reflexivity]. intros a Ha Ho. apply rm_absorb_out.
      exact (R_miss Ai (Some _) rho rho md R a (MI1 _ _ _ HM) HRok Ha Ho).
    + rewrite !rw_call'. rewrite <- Ht. exact Tin.
  -
    intros L JL tr ms md rhoL tr' ms' md' HinL Hsm HJ Hag1 HsmL HJL.
    destruct HJ as (Hav & Hk & HM & HP & (HN & HD & HZ) & HK & HP0).
    destruct (HR Ai HF HP0 Hav HP HN HD HZ (ex_intro _ rho (ex_intro _ md (MI1 _ _ _ HM))) (T_of_chk _ _ _ _ _ _ _ Hav (proj2 (proj2 HM)) Hchk)) as (Hnz & Ht & HRok).
    destruct (proj1 (Forall_forall _ _) HN t (nth_error_In _ _ Hnth) Hnz) as (Tpos & Tin & Tfb).
    cbn [In] in HinL. destruct HinL as [HinL|[]]. injection HinL as HL HJLe. subst L JL.
    destruct HJL as (A' & l1 & l2 & HM' & HbAi & HbA' & Hkept & Hinit & _).
    rewrite !rw_call' in HbAi.
    set (x := bv_unsigned (eval rho (wsub_get s 12))) in *.
    set (m := bv_unsigned (eval rho (wsub_get s 13))) in *.
    assert (SUB : forall A2 k1 k2, ma_blocks Ai = k1 ++ (x, m) :: k2 -> ma_blocks A2 = k1 ++ k2 ->
                 forall bn, In bn (ma_blocks Ai) -> bn <> (x, m) -> In bn (ma_blocks A2)).
    { intros A2 k1 k2 E1 E2 bn Hb Hbx. rewrite E2. rewrite E1 in Hb.
      apply in_mid_cases in Hb as [Hb|Hb]; [|exact Hb]. exfalso. exact (Hbx Hb). }
    assert (CADDR : forall A2, top_kept Ai A2 -> (forall bn, In bn (ma_blocks Ai) -> bn <> (x, m) -> In bn (ma_blocks A2)) ->
                   forall a, caddr Ai (Some x) a -> caddr A2 None a).
    { intros A2 HTK HS a [H|[H|(b & n & Hb & Hbx & Hr)]]; [left; unfold top_kept in HTK; rewrite HTK; exact H | right; left; exact H | right; right].
      exists b, n. split; [apply HS; [exact Hb | intros Heq; apply Hbx; injection Heq as -> ->; reflexivity]|].
      split; [discriminate | exact Hr]. }
    assert (FB2 : forall A2, (forall bn, In bn (ma_blocks Ai) -> bn <> (x, m) -> In bn (ma_blocks A2)) ->
                 forall bn, In bn FB -> In bn (ma_blocks A2)).
    { intros A2 HS bn Hbn. apply HS; [exact (HP _ Hbn)|]. intros ->. rewrite <- Ht in Hbn. exact (Tfb Hbn). }
    pose proof (SUB A' l1 l2 HbAi HbA') as HsubA'.
    split.
    + split.
      * intros a Hina.
        apply (robjs_in_ranges Ai (Some x) rho R) in Hina; [|exact HRok].
        rewrite <- (Z_to_bv_bv_unsigned 64 a).
        pose proof (bv_urange a) as Ha.
        destruct (caddr_props Ai (Some x) _ rho md ML (MI1 _ _ _ HM) Ha Hina) as (O1 & O2 & O3).
        destruct (caddr_props A' None _ rhoL md' ML HM' Ha (CADDR A' (init_kept_top _ _ Hinit) HsubA' _ Hina)) as (O1' & _).
        apply Hkept; try assumption; [exact (caddr_client _ _ _ Hina) | exact (caddr_client _ _ _ (CADDR A' (init_kept_top _ _ Hinit) HsubA' _ Hina)) |]. intros Hs. apply O3. apply static_alloc_static. exact Hs.
      * intros o' oR Hin' _. cbn in Hin'. destruct Hin'.
    + intros rho' Hlink.
      eapply TR_pre; [ | apply (Tfree (rho_patch rho' (patchf rho rho' R)))].
      intros w [Hsm' HJ']. cbn [J_ofP] in HJ'.
      destruct HJ' as (A2 & k1 & k2 & HM2 & HbAi2 & HbA2 & Hkept2 & Hinit2 & Hk2).
      rewrite !rw_call' in HbAi2. fold x in HbAi2. fold m in HbAi2.
      pose proof (SUB A2 k1 k2 HbAi2 HbA2) as HsubA2.
      assert (Hag' : agree_vals (ss_next Cl) rho rho') by (destruct Hlink as (A & _); exact A).
      assert (Hag'' : agree_vals (ss_next Cl) rho (rho_patch rho' (patchf rho rho' R))) by (eapply agree_vals_trans; [exact Hag' | apply agree_vals_patch]).
      split; [exact (cont_smatch Cl (Pre_free E) _ s R rho rho' tr ms md w He Hsm eq_refl Hag' Hsm')|].
      exists A2. split; [|split; [exact Hk2|split; [|split; [|split; [split; [|split]|split; [|exact HP0]]]]]].
      * eapply agree_vals_trans; [exact Hav|].
        eapply agree_vals_trans; [eapply agree_vals_le; [exact Hnf| exact Hag']| apply agree_vals_patch].
      * eapply MInvR_mem; [exact (conj HM2 (conj (init_kept_init _ _ Hinit2 (proj1 (proj2 HM))) (TPI_kept _ _ (init_kept_top _ _ Hinit2) (proj2 (proj2 HM)))))| |reflexivity]. intros a Ha Ho. cbn [rho_patch rm]. unfold patchf.
        destruct (in_ranges_dec rho R (Z_to_bv 64 a)) as [Hi|Hn'].
        -- exfalso. eapply (R_miss A2 None rho rhoL _ R a); [exact HM2 | | exact Ha | exact Ho | exact Hi].
           intros o b Ho' Hr'. apply (CADDR A2 (init_kept_top _ _ Hinit2) HsubA2). exact (HRok o b Ho' Hr').
        -- eapply call_linkP_rm. exact Hlink.
      * exact (FB2 A2 HsubA2).
      * apply (tvin_agree A2 (ss_next Cl) rho); [exact Hag'' | |].
        { unfold tv_below in *. apply forallb_forall. intros t' Ht'. apply (proj1 (forallb_forall _ _) Hnb). eapply remove_nth_In. exact Ht'. }
        unfold tvin in HN |- *. apply Forall_forall. intros t' Ht' Hnz'.
        destruct (proj1 (Forall_forall _ _) HN t' (remove_nth_In _ _ _ Ht') Hnz') as (X0 & X1 & X2).
        split; [exact X0|]. split; [|exact X2]. apply HsubA2; [exact X1|].
        rewrite <- Ht. exact (tvd_nth_distinct rho tv i t t' HD Hnth Ht' Hnz Hnz').
      * apply (tvd_agree (ss_next Cl) rho); [exact Hag'' | | apply tvd_remove; exact HD].
        unfold tv_below in *. apply forallb_forall. intros t' Ht'. apply (proj1 (forallb_forall _ _) Hnb). eapply remove_nth_In. exact Ht'.
      * apply (tvz_agree (ss_next Cl) rho); [exact Hag'' | |].
        { unfold tv_below in *. apply forallb_forall. intros t' Ht'. apply (proj1 (forallb_forall _ _) Hnb). eapply remove_nth_In. exact Ht'. }
        unfold tvz in HZ |- *. apply Forall_forall. intros t' Ht'. apply (proj1 (Forall_forall _ _) HZ). eapply remove_nth_In. exact Ht'.
      * intros a Ha Hp. cbn [rho_patch rm]. unfold patchf.
        destruct (in_ranges_dec rho R (Z_to_bv 64 a)) as [Hi|Hn']; [apply HK; assumption|].
        rewrite (call_linkP_rm _ _ _ _ _ _ _ _ _ _ Hlink).
        pose proof (pclF_caddr Ai a HP (proj2 (proj2 HM)) Hp) as Hc.
        destruct (caddr_props Ai None a rho md ML (MI1 _ _ _ HM) Ha Hc) as (O1 & O2 & O3).
        destruct (caddr_props A2 None a rhoL _ ML HM2 Ha (pclF_caddr A2 a (FB2 A2 HsubA2) (TPI_kept _ _ (init_kept_top _ _ Hinit2) (proj2 (proj2 HM))) Hp)) as (O1' & _).
        transitivity (rm (rho_sub (rho_absorb rho R ms) s) (Z_to_bv 64 a)).
        -- apply Hkept2; try assumption; [exact (caddr_client _ _ _ Hc) | exact (caddr_client _ _ _ (pclF_caddr A2 a (FB2 A2 HsubA2) (TPI_kept _ _ (init_kept_top _ _ Hinit2) (proj2 (proj2 HM))) Hp)) |]. intros Hs. apply O3. apply static_alloc_static. exact Hs.
        -- rewrite rm_absorb_out by exact Hn'. apply HK; assumption.
Qed.

Lemma SPJ_refacts_J : ltac2:(tb__ "0|0|
S4aS1S2S36S5A1S9aS49Vsegs;R5R3R4R1A5S2bS37S79S5S19S3R4A1A1R3A3S39A3S36S52A1S51R9R8R2R1A3S8cS5S7R9A1S6R8A1A3S8cS5S7RaA1R8A3F_;F_;Fmd;Ftr;S49Vsegs;R8S111R5R6A2R7R4A5F_;F_;F_;Fw;Ff;FS;Frho;FJ;").
Proof using .
  intros J rho S f w [Hsm Hk] Hb Hf. split; [|exact Hk].
  apply smatch_add_facts; [exact Hsm | | exact Hb]. destruct w as [tr [ms md]].
  apply (Hf tr md Hk). eapply smatch_facts_hold. exact Hsm.
Qed.

Definition tv_facts (t : sv * sv) : list sprop := ltac2:(tb__ "0|3|
S3eS5S16S3cS0S0Vt;A3M0SbZ7fffff800000A1M1A2S3eS5S16S3fS0S0Vt;A3M2G1A2S3eS5S16S14S10aG0G2A3G1A2S3eS5S16SbZ1000A1G0A2S3eS5S16SbZ1A1G2A2S44S5A1A3A3A3A3A3").

Lemma tv_facts_hold : ltac2:(tb__ "0|1|
S36S38S0S0A2M0A1S7dS1S36S52A1S51G0S64R6R5R4R3R2A5S77G0R2R7A3S59R6R3A2S8cS5S7R7A1S126R4A1A3F_;F_;F_;Ft;Fmd;Ftr;Frho;FAi;Ftv;").
Proof using .
  intros tv Ai rho tr md [d sz] (Hav & Hk & [HM _] & HP & (HN & HD & HZ) & HK & HP0) Hin Hnz.
  destruct (proj1 (Forall_forall _ _) HN _ Hin Hnz) as (Hpos & Hb & _). unfold tvv in Hb, Hpos. cbn [fst snd] in Hb, Hpos.
  unfold MInvR in HM.
  pose proof (minv_block_geom C Ai _ _ _ _ _ HM Hb) as (G0 & _ & G2 & G3 & _).
  pose proof (topL_range (ma_L Ai)) as TRg. unfold PGSZ, UNIT, IB in *.
  pose proof (bv_urange (eval rho d)) as R1. pose proof (bv_urange (eval rho sz)) as R2.
  unfold tv_facts. cbn [fst snd].
  repeat constructor; cbn [holds]; rewrite ?U_add, ?U_lit; unfold M64v;
    rewrite ?(Z.mod_small 140737479966720) by lia; rewrite ?(Z.mod_small 4096) by lia; rewrite ?(Z.mod_small 1) by lia; try lia;
    rewrite Z.mod_small by lia; lia.
Qed.

Lemma JG_tv_facts : ltac2:(tb__ "0|1|
S36S38S0S0A2M0A1S1S36S52A1S51G0S55R5R4R3R2A4S77G0R2R6A3S59R6R3A2S8cS5S7R7A1S126R4A1A3F_;F_;F_;Ft;Fmd;Ftr;Frho;Ftv;").
Proof using . intros tv rho tr md t [Ai H] Hin Hnz. eapply tv_facts_hold; eauto. Qed.

Lemma tnz_of_fact : ltac2:(tb__ "0|0|
S1S0S0S7R3S1aS17S10bR2SbZ0A1A3A1A2S59R4S3bS0S0R3R2A4A2F_;Fsz;Fd;Frho;").
Proof using .
  clear_sec.
  intros rho d sz H Hz. apply H. apply holds_beq. rewrite U_lit. unfold tnz in Hz. cbn [fst] in Hz. unfold M64v. rewrite Z.mod_0_l by lia. exact Hz.
Qed.

Lemma JG_drop_last_empty : ltac2:(tb__ "0|2|
S36S38S0S0A2A1S2S36S4A1M0S4S1S9aS2bG0S1dR5A1S40S4R4S3eS4R3S44S4A1A3A3A3S2bS37SddVNP;S3R6A1A2S39A3S2bS37S57S3R7A1R8A2S39A3S8cS5S7R5A1S6R8A1A3S8eS3fS33S33SeR6R7A2M1A3S3cS33S33G1A3A2F_;S49Vsegs;S55RaA1R9R6R5A5S2dS1S1S49Vsegs;S55RcA1S105RbRaA2R1R7A5Lrho';A2F_;F_;F_;F_;F_;Fw;Frho;Fo;Fobjs;FS;Ftv;").
Proof using ML.
  intros tv S objs o rho [tr [ms md]] Ho Hnf Hnb Hemp [Hsm HJ]. apply Pos.leb_le in Hnf.
  exists (rho_absorb rho [o] ms). split.
  - apply (smatch_frame_in segs rho S objs [o] tr ms md Ho Hsm).
  - assert (Hag : agree_below (ss_next S) rho (rho_absorb rho [o] ms)).
    { split; [intros; reflexivity|]. split; [intros; reflexivity|].
      intros a. unfold rho_absorb. cbn [rm]. destruct (in_ranges_dec rho [o] a) as [Hi|]; [|reflexivity].
      exfalso. destruct Hi as (o' & [<-|[]] & Hr). specialize (Hemp (smatch_facts_hold segs _ _ _ Hsm)). lia. }
    eapply (stableJ_JG (ss_next S) tv); [exact Hnf | exact Hnb | exact Hag | exact HJ].
Qed.

Lemma ok_frame_imp : ltac2:(tb__ "0|2|
S9aOF_;S36S52A1M0S51OF_;F_;M1G1G0S51R3R2R1A2R5R3R2A2F_;Fmd;Ftr;S4bVsegs;R4R3A3S4bVsegs;R5R3A3F_;F_;FK';FK;Fok;").
Proof using . intros ok K K' HK H tr ms md ms' Hk. apply (H tr ms md ms'). apply HK. exact Hk. Qed.

Theorem pure_callT : ltac2:(tb__ "0|3|
S2S2S84S36S4A1M0S36S101A1S1S36S38S0S0A2A1S99S1VTR;S4dVsegs;S36S52A1S51S55R5R6R2R1A4Lmd;Ltr;M1R8R1A4S4cVsegs;G1S3R8A1R1R5A5A2Frho1;S2bS3aG0A1ScdR9R8R7A3S3dG0R6A2A3S2bS37Sa6RaR9R8R7R6A5S39A3S2bS37SddVNP;S3RbA1A2S39A3S2bS37S57S3RcA1R6A2S39A3S2bS37S79S5S19S3RdA1A1S6RdA1A3S39A3S101S1S77S101R2RcA3S11S3R11A1M2RcR2A3VTR;S49Vsegs;S55RcA1S111S6R12A1Sa5R10G2S104R4A1S3R12A1RfA5A2R3A4RbA2F_;F_;Frho';FL;VTR;S49Vsegs;S55R9A1RfRaA4R8A2F_;F_;F_;F_;F_;F_;F_;FQ;Ftv;Frho;FPosts;FR;Fs;FPre;FCl;").
Proof using ML TR_callJ TR_facts TR_pre.
  intros Cl Pre s R Posts rho tv Q Hsum He Hchk Hnf Hnb Hfb Hcont. apply Pos.leb_le in Hnf.
  apply TR_facts. intros HF.
  apply (TR_callJ (JG tv) (liftK (fun tr md => JG tv rho tr md)) (liftK (fun tr md => JG tv rho tr md))
           (JG tv) Cl Pre s R Posts Q rho He Hchk).
  - intros rho1. apply Hsum.
  - intros tr ms md Hsm HJ. exact HJ.
  - intros L rho' rhoL tr ms md tr' md' HinL Hsm HJ HLK HJ'. cbn [liftK] in HJ'.
    eapply (stableJ_JG (ss_next Cl) tv Hnf Hnb); [exact (proj1 HLK) | exact HJ'].
  - intros L rho' HinL Hag. eapply TR_pre; [ | apply (Hcont L rho' HinL Hag)].
    intros w [Hsm' HJ']. split; [|exact HJ'].
    apply smatch_add_facts; [exact Hsm' | |].
    + apply Forall_forall. intros q Hq.
      apply (holds_agree_vals (ss_next Cl) rho rho' q (agree_below_vals _ _ _ Hag)).
      * exact (proj1 (forallb_forall _ _) Hfb q Hq).
      * exact (proj1 (Forall_forall _ _) HF q Hq).
    + apply forallb_forall. intros q Hq.
      eapply sprop_below_mono; [| exact (proj1 (forallb_forall _ _) Hfb q Hq)].
      unfold import_post. cbn [ss_next set_objs subst_state]. unfold import_next, pos_add_nat. lia.
Qed.
End CallT.

Record malloc_contracts_ex : Prop := MCX {
  mcx_malloc : malloc_contract_ex segs C E;
  mcx_calloc : calloc_contract_ex segs C E;
  mcx_free : free_contract_ex segs C E
}.

Let TRs (ok : world -> Prop) : assn -> assn -> Prop := triple segs ok.
Let TRe : assn -> assn -> Prop := etriple segs.
Lemma TRs_facts : ltac2:(tb__ "0|1|
S9aOF_;S4aS2S1S99S8cS5S7R2A1S6R3A1A3VTRs;R6S49Vsegs;R5R4R3A4R2A3M0F_;G0F_;FQ;Frho;FS;FJ;Fok;").
Proof using . intros ok. exact (triple_factsJ segs ok). Qed.
Lemma TRs_ex : forall ok (A : Type) (J : A -> jpred) S rho (Q : assn),
  (forall x, TRs ok (SPJ segs (J x) S rho) Q) -> TRs ok (SPJ segs (fun r t m => exists x, J x r t m) S rho) Q.
Proof using . intros ok. exact (triple_SPJ_ex segs ok). Qed.
Lemma TRs_pre : ltac2:(tb__ "0|0|
S9aOF_;S99S99S99S9aR3R1A1R5R2A1F_;Fw;VTRs;R5R4R2A3VTRs;R6R4R3A3F_;F_;FQ;FP';FP;Fok;").
Proof using segs. intros ok P P' Q HP H. eapply triple_conseq; [exact HP | intros w Hw; exact Hw | exact H]. Qed.
Lemma TRe_facts : ltac2:(tb__ "0|1|
S4aS2S1S99S8cS5S7R2A1S6R3A1A3VTRe;S49Vsegs;R5R4R3A4R2A2M0F_;G0F_;FQ;Frho;FS;FJ;").
Proof using . exact (etriple_factsJ segs). Qed.
Lemma TRe_ex : forall (A : Type) (J : A -> jpred) S rho (Q : assn),
  (forall x, TRe (SPJ segs (J x) S rho) Q) -> TRe (SPJ segs (fun r t m => exists x, J x r t m) S rho) Q.
Proof using . exact (etriple_SPJ_ex segs). Qed.
Lemma TRe_pre : ltac2:(tb__ "0|0|
S99S99S99S9aR3R1A1R5R2A1F_;Fw;VTRe;R4R2A2VTRe;R4R3A2F_;F_;FQ;FP';FP;").
Proof using segs. intros P P' Q HP H. eapply etriple_conseq; [exact HP | intros w Hw; exact Hw | exact H]. Qed.

Ltac by_callT_safety ok lem :=
  apply (lem (triple segs ok) (TRs_facts ok) (TRs_ex ok) (TRs_pre ok) (call_soundP segs ok)).
Ltac by_callT_ex lem :=
  apply (lem (etriple segs) TRe_facts TRe_ex TRe_pre (call_completeP segs)).
Ltac by_pureT_safety ok :=
  apply (pure_callT (triple segs ok) (TRs_facts ok) (TRs_pre ok) (call_soundJ segs ok)).
Ltac by_pureT_ex :=
  apply (pure_callT (etriple segs) TRe_facts TRe_pre (call_completeJ segs)).

Theorem malloc_callJ : ltac2:(tb__ "0|8|
S9aOF_;S2S84S36S4A1M0S1S36S38S0S0A2M1A1S99Sb5Vsegs;R7VKc;A3SefS2bS3aG0A1ScdR8SbdVE;A1M2R7A3S3dG0R6A2A3S2bS37S5eR9G2R8R7S3eS2SbaVE;A1M3S3eS2SbbVE;A1M4S44S2A1A3A3A5S39A3S2bS37SddVNP;S3RaA1A2S39A3S2bS37S57S3RbA1R7A2S39A3S2bS37SdS3RcA1S83RbPcM5A2A2S39A3S2bS0S83Sa3RcS100G4S3RdA1M6A4Sb1A2S9Sa1G6UaM7A2A1A3S7dS8cS5S7RcA1S6RfA1A3VP0f;Vrho0;A1Sa0VNP;Vrho0;ReA3S60R4A1S5dR5R10RfA3S5bR11R10A2S5fR12R11A2S2dS1S1S2dS51S51Sb0Vsegs;VC;RaR2R1A5Lmd;A2LrhoM;A2Se2R14ScfS7eR9A1A1A2S2cSe3RaS45S33A1R15R16A4S8dZ0S9eQ40S8R15S83R17G5A2A2A2A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;FAi;S1S9bVsegs;R11S49Vsegs;S55RcA1S58R10RfReG3A4R1A4RbA4Frho';S1S9bVsegs;R12S49Vsegs;S55S3eG1S3bS0S0S9Sa1S3R11A1G7A2A1S83R10G5A2A4RdA3A1S58R11R10RfG4A4R1A4RcA4Frho';S9bVsegs;R12S49Vsegs;S55RdA1R11ReA4RcA4F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftv;Frho;FR;Fs;FCl;Fok;").
Proof using ML.
  intros ok Cl s R rho tv Q Hok MC. by_callT_safety ok malloc_callT.
  intros Ai rho1. apply (mc_malloc MC). exact Hok.
Qed.

Theorem malloc_callJ_ex : ltac2:(tb__ "0|8|
S2S84S36S4A1M0S1S36S38S0S0A2M1A1S99Sb6VKc;A1S6dS2bS3aG0A1ScdR8SbdVE;A1M2R7A3S3dG0R6A2A3S2bS37S5eR9G2R8R7S3eS2SbaVE;A1M3S3eS2SbbVE;A1M4S44S2A1A3A3A5S39A3S2bS37SddVNP;S3RaA1A2S39A3S2bS37S57S3RbA1R7A2S39A3S2bS37SdS3RcA1S83RbPcM5A2A2S39A3S2bS0S83Sa3RcS100G4S3RdA1M6A4Sb1A2S9Sa1G6UaM7A2A1A3S7dS8cS5S7RcA1S6RfA1A3VP0f;Vrho0;A1Sa0VNP;Vrho0;ReA3S60R4A1S5dR5R10RfA3S5bR11R10A2S5fR12R11A2S2dS1S1S2dS51S51Sb0Vsegs;VC;RaR2R1A5Lmd;A2LrhoM;A2Se2R14ScfS7eR9A1A1A2S2cSe3RaS45S33A1R15R16A4S8dZ0S9eQ40S8R15S83R17G5A2A2A2A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;FAi;S1S9cVsegs;S49Vsegs;S55RcA1S58R10RfReG3A4R1A4RbA3Frho';S1S9cVsegs;S49Vsegs;S55S3eG1S3bS0S0S9Sa1S3R11A1G7A2A1S83R10G5A2A4RdA3A1S58R11R10RfG4A4R1A4RcA3Frho';S9cVsegs;S49Vsegs;S55RdA1R11ReA4RcA3F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftv;Frho;FR;Fs;FCl;").
Proof using ML.
  intros Cl s R rho tv Q Hvi MCXh. by_callT_ex malloc_callT.
  intros Ai rho1. apply (mcx_malloc MCXh). exact Hvi.
Qed.

Theorem calloc_callJ : ltac2:(tb__ "0|d|
S9aOF_;S2S84S36S4A1M0S1S36S38S0S0A2M1A1S99Sb5Vsegs;R7VKc;A3SefS2bS3aG0A1ScdR8SbcVE;A1M2R7A3S3dG0R6A2A3S2bS37S5eR9G2R8R7S3eS2Sb2SbeVE;A1M3A1M4S3eS2Sb2SbfVE;A1A1M5S3eS2Sb3G3A1M6S3eS2Sb3Sc0VE;A1A1M7S44S2A1A3A3A3A3A5S39A3S2bS37SddVNP;S3RaA1A2S39A3S2bS37S57S3RbA1R7A2S39A3S2bS37SdS3RcA1S83RbPcM8A2A2S39A3S2bS37SdS3RdA1S83RcPdM9A2A2S39A3S2bS0S83Sa3RdS100G6S3ReA1MaA4Sb1A2S9Sa1GaUaMbA2A1A3S2bS0S83Sa3ReS100G7S3RfA1McA4Sb1A2S9Sa1GcGbA2A1A3S7dS8cS5S7ReA1S6R11A1A3VP0f;Vrho0;A1Sa0VNP;Vrho0;R10A3S60R4A1S5dR5R12R11A3S5bR13R12A2S5fR14R13A2S2dS1S1S2dS51S51Sb0Vsegs;VC;RaR2R1A5Lmd;A2LrhoM;A2Se2R16ScfS7eR9A1A1A2S2cSe3RaS45S33A1R17R18A4S8dZ0S9eQ40S8R17S10S109S83R19G8A2S83R19G9A2A3A2A2A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;FAi;S1S9bVsegs;R13S49Vsegs;S55ReA1S58R12R11R10G4A4R1A4RdA4Frho';S1S9bVsegs;R14S49Vsegs;S55RfA1S58R13R12R11G5A4R1A4ReA4Frho';S1S9bVsegs;R15S49Vsegs;S55S3eG1S3bS0S0S9Sa1S3R14A1GbA2A1S10S109S83R13G8A2S83R13G9A2A3A4R10A3A1S58R14R13R12G6A4R1A4RfA4Frho';S1S9bVsegs;R16S49Vsegs;S55S3eG1S3bS0S0S9Sa1S3R15A1GbA2A1S10S109S83R14G8A2S83R14G9A2A3A4R11A3A1S58R15R14R13G7A4R1A4R10A4Frho';S9bVsegs;R16S49Vsegs;S55R11A1R15R12A4R10A4F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftv;Frho;FR;Fs;FCl;Fok;").
Proof using ML.
  intros ok Cl s R rho tv Q Hok MC. by_callT_safety ok calloc_callT.
  intros Ai rho1. apply (mc_calloc MC). exact Hok.
Qed.

Theorem calloc_callJ_ex : ltac2:(tb__ "0|d|
S2S84S36S4A1M0S1S36S38S0S0A2M1A1S99Sb6VKc;A1S6dS2bS3aG0A1ScdR8SbcVE;A1M2R7A3S3dG0R6A2A3S2bS37S5eR9G2R8R7S3eS2Sb2SbeVE;A1M3A1M4S3eS2Sb2SbfVE;A1A1M5S3eS2Sb3G3A1M6S3eS2Sb3Sc0VE;A1A1M7S44S2A1A3A3A3A3A5S39A3S2bS37SddVNP;S3RaA1A2S39A3S2bS37S57S3RbA1R7A2S39A3S2bS37SdS3RcA1S83RbPcM8A2A2S39A3S2bS37SdS3RdA1S83RcPdM9A2A2S39A3S2bS0S83Sa3RdS100G6S3ReA1MaA4Sb1A2S9Sa1GaUaMbA2A1A3S2bS0S83Sa3ReS100G7S3RfA1McA4Sb1A2S9Sa1GcGbA2A1A3S7dS8cS5S7ReA1S6R11A1A3VP0f;Vrho0;A1Sa0VNP;Vrho0;R10A3S60R4A1S5dR5R12R11A3S5bR13R12A2S5fR14R13A2S2dS1S1S2dS51S51Sb0Vsegs;VC;RaR2R1A5Lmd;A2LrhoM;A2Se2R16ScfS7eR9A1A1A2S2cSe3RaS45S33A1R17R18A4S8dZ0S9eQ40S8R17S10S109S83R19G8A2S83R19G9A2A3A2A2A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;FAi;S1S9cVsegs;S49Vsegs;S55ReA1S58R12R11R10G4A4R1A4RdA3Frho';S1S9cVsegs;S49Vsegs;S55RfA1S58R13R12R11G5A4R1A4ReA3Frho';S1S9cVsegs;S49Vsegs;S55S3eG1S3bS0S0S9Sa1S3R14A1GbA2A1S10S109S83R13G8A2S83R13G9A2A3A4R10A3A1S58R14R13R12G6A4R1A4RfA3Frho';S1S9cVsegs;S49Vsegs;S55S3eG1S3bS0S0S9Sa1S3R15A1GbA2A1S10S109S83R14G8A2S83R14G9A2A3A4R11A3A1S58R15R14R13G7A4R1A4R10A3Frho';S9cVsegs;S49Vsegs;S55R11A1R15R12A4R10A3F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftv;Frho;FR;Fs;FCl;").
Proof using ML.
  intros Cl s R rho tv Q Hvi MCXh. by_callT_ex calloc_callT.
  intros Ai rho1. apply (mcx_calloc MCXh). exact Hvi.
Qed.

Theorem free_callJ : ltac2:(tb__ "0|6|
S9aOF_;S2S84S36S4A1M0S1S36S38S0S0A2M1A1S41G1S99Sb5Vsegs;R9VKc;A3SefS2bS3aG0A1ScdRaSb8VE;A1M2R9A3S3dG0R8A2A3S2bS37S5eRbG2RaR9S3eS2Sb7VE;A1M3S44S2A1A3A5S39A3S2bS37SddVNP;S3RcA1A2S39A3S2bS37S57S3RdA1R9A2S39A3S2bS3aG1A1S78G1RaR9A3S3dG1R8A2A3S7dS8cS5S7RdA1S6R10A1A3VP0f;Vrho0;A1Sa0VNP;Vrho0;RfA3S60R4A1S5dR5R11R10A3S5bR12R11A2S5fR13R12A2S2dS1S1S2dS51S51Sb0Vsegs;VC;RaR2R1A5Lmd;A2LrhoM;A2Se2R15ScfS7eR9A1A1A2S2cS59R16R13A2S2cS2bS38S33S33A2S5aR16R13A2S3bS33S33S9eQ40M4S8R16S83R18PcA2A2A2M5S9eG4S8R16S83R18PdA2A2A2A4A3Se3RaS3dS33G5A2R16R17A4A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;FAi;S1S9bVsegs;R12S49Vsegs;S55S66G1RcRdA3A1S58R11R10RfG3A4R1A4RaA4Frho';S9bVsegs;R12S49Vsegs;S55RdA1R11ReA4RaA4F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ft;Fi;Ftv;Frho;FR;Fs;FCl;Fok;").
Proof using ML.
  intros ok Cl s R rho tv i t Q Hok MC. by_callT_safety ok free_callT.
  intros Ai rho1. apply (mc_free MC). exact Hok.
Qed.

Theorem free_callJ_ex : ltac2:(tb__ "0|6|
S2S84S36S4A1M0S1S36S38S0S0A2M1A1S41G1S99Sb6VKc;A1S6dS2bS3aG0A1ScdRaSb8VE;A1M2R9A3S3dG0R8A2A3S2bS37S5eRbG2RaR9S3eS2Sb7VE;A1M3S44S2A1A3A5S39A3S2bS37SddVNP;S3RcA1A2S39A3S2bS37S57S3RdA1R9A2S39A3S2bS3aG1A1S78G1RaR9A3S3dG1R8A2A3S7dS8cS5S7RdA1S6R10A1A3VP0f;Vrho0;A1Sa0VNP;Vrho0;RfA3S60R4A1S5dR5R11R10A3S5bR12R11A2S5fR13R12A2S2dS1S1S2dS51S51Sb0Vsegs;VC;RaR2R1A5Lmd;A2LrhoM;A2Se2R15ScfS7eR9A1A1A2S2cS59R16R13A2S2cS2bS38S33S33A2S5aR16R13A2S3bS33S33S9eQ40M4S8R16S83R18PcA2A2A2M5S9eG4S8R16S83R18PdA2A2A2A4A3Se3RaS3dS33G5A2R16R17A4A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;FAi;S1S9cVsegs;S49Vsegs;S55S66G1RcRdA3A1S58R11R10RfG3A4R1A4RaA3Frho';S9cVsegs;S49Vsegs;S55RdA1R11ReA4RaA3F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ft;Fi;Ftv;Frho;FR;Fs;FCl;").
Proof using ML.
  intros Cl s R rho tv i t Q Hvi MCXh. by_callT_ex free_callT.
  intros Ai rho1. apply (mcx_free MCXh). exact Hvi.
Qed.

Theorem pure_callJ : ltac2:(tb__ "0|2|
S9aOF_;S2S2S84S36S4A1M0S36S101A1S1S36S38S0S0A2A1S99S36S52A1S51OF_;F_;S1S4bVsegs;RbR2A3S9bVsegs;RcS4dVsegs;R3RaR2A4S4cVsegs;R3S3RaA1R2R7A5A4F_;Frho1;FK;S4bVsegs;RaVKc;A3S2bS3aG0A1ScdRaR9R8A3S3dG0R7A2A3S2bS37Sa6RbRaR9R8R7A5S39A3S2bS37SddVNP;S3RcA1A2S39A3S2bS37S57S3RdA1R7A2S39A3S2bS37S79S5S19S3ReA1A1S6ReA1A3S39A3S101S1S77S101R2RdA3S11S3R12A1M1RdR2A3S9bVsegs;R14S49Vsegs;S55RdA1S111S6R13A1Sa5R11G1S104R4A1S3R13A1R10A5A2R3A4RcA4F_;F_;Frho';FL;S9bVsegs;R11S49Vsegs;S55RaA1R10RbA4R9A4F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftv;Frho;FPosts;FR;Fs;FPre;FCl;Fok;").
Proof using ML.
  intros ok Cl Pre s R Posts rho tv Q Hsum Hok. by_pureT_safety ok.
  intros rho1. apply (Hsum (fun tr md => JG tv rho tr md) rho1).
  eapply ok_frame_imp; [|exact Hok]. intros tr md (Ai & _ & Hk & _). exact Hk.
Qed.

Theorem pure_callJ_ex : ltac2:(tb__ "0|2|
S2S2S84S36S4A1M0S36S101A1S1S36S38S0S0A2A1S99S36S52A1S51OF_;F_;S1S9cVsegs;S4dVsegs;R2R9R1A4S4cVsegs;R2S3R9A1R1R6A5A3Frho1;FK;S2bS3aG0A1ScdR9R8R7A3S3dG0R6A2A3S2bS37Sa6RaR9R8R7R6A5S39A3S2bS37SddVNP;S3RbA1A2S39A3S2bS37S57S3RcA1R6A2S39A3S2bS37S79S5S19S3RdA1A1S6RdA1A3S39A3S101S1S77S101R2RcA3S11S3R11A1M1RcR2A3S9cVsegs;S49Vsegs;S55RcA1S111S6R12A1Sa5R10G1S104R4A1S3R12A1RfA5A2R3A4RbA3F_;F_;Frho';FL;S9cVsegs;S49Vsegs;S55R9A1RfRaA4R8A3F_;F_;F_;F_;F_;F_;F_;FQ;Ftv;Frho;FPosts;FR;Fs;FPre;FCl;").
Proof using ML.
  intros Cl Pre s R Posts rho tv Q Hsum. by_pureT_ex.
  intros rho1. apply Hsum.
Qed.

Definition nodeI (n : sstate * list (sv * sv)) : jnode := ltac2:(tb__ "0|1|
S3bS2S4aS3cS2S36S38S0S0A2A1M0Vn;A3S55S3fS2G0Vn;A3A1A4").

Fixpoint tv_sub_eqb (s : wsub) (tv tv' : list (sv * sv)) : bool :=
  match tv, tv' with
  | [], [] => true
  | t :: r, t' :: r' => sv_eqb (sv_subst s (fst t')) (fst t) && sv_eqb (sv_subst s (snd t')) (snd t) && tv_sub_eqb s r r'
  | _, _ => false
  end.

Lemma tv_sub_eqb_sound : ltac2:(tb__ "0|5|
S84S36S38S0S0A2M0A1M1G1S1S2bS37S67R4R3R2A3S39A3S2cS2bS36S38S33S33A2M2A1S8bG0G2S5aS85R2R5A2A1R3A4S8bG0G2S5aR2A1R4A4A3S41G0G0S2bS3aG0A1M3S78G0R7R3A3S3dG0R2A2M4A3S2bG3S78G0R7R4A3G4A3S30S59S85R7RaA2R3A2S59R7R4A2A2F_;F_;Ft';Ft;Fk;A2F_;Frho;Ftv';Ftv;Fs;").
Proof using .
  clear_sec. intros s tv. induction tv as [|t r IH]; intros [|t' r'] rho H; cbn in H; try discriminate.
  - split; [reflexivity|]. intros [|k] ? ? H1; discriminate.
  - apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
    apply sv_eqb_sound in H1. apply sv_eqb_sound in H2.
    destruct (IH r' rho H3) as [IH1 IH2].
    assert (E1 : eval (rho_sub rho s) (fst t') = eval rho (fst t)) by (rewrite <- eval_subst, H1; reflexivity).
    assert (E2 : eval (rho_sub rho s) (snd t') = eval rho (snd t)) by (rewrite <- eval_subst, H2; reflexivity).
    split.
    + cbn [map]. f_equal; [|exact IH1]. unfold tvv. rewrite E1, E2. reflexivity.
    + intros [|k] t0 t0' Ha Hb; cbn in Ha, Hb.
      * injection Ha as <-. injection Hb as <-. unfold tnz. rewrite E1. tauto.
      * exact (IH2 k t0 t0' Ha Hb).
Qed.

Lemma tvin_map : ltac2:(tb__ "0|5|
S7dS1S1S36S38S0S0A2M0A1M1G1S2bS36S38S33S33A2M2A1S8bG0G2S5aR3A1R1A4S8bG0G2S5aR4A1R2A4A3S41G0G0S2bS3aG0A1M3S78G0R6R3A3S3dG0R2A2M4A3S2bG3S78G0R6R4A3G4A3S30S59R9R3A2S59RaR4A2A2F_;F_;Ft';Ft;Fk;S5dR7R6R4A3S5dR8R6R4A3F_;F_;F_;Ftv';Ftv;Frho';Frho;FAi;").
Proof using .
  intros Ai rho rho' tv. induction tv as [|t r IH]; intros [|t' r'] H Hz HN; cbn [map] in H; try discriminate.
  - constructor.
  - assert (H1 : tvv rho' t' = tvv rho t) by congruence. assert (H2 : map (tvv rho') r' = map (tvv rho) r) by congruence.
    inversion HN; subst. constructor.
    + intros Hnz'. rewrite H1. match goal with Ht : tnz rho t -> _ |- _ => apply Ht end.
      apply (proj1 (Hz 0%nat t t' eq_refl eq_refl)). exact Hnz'.
    + apply IH; [exact H2 | | assumption]. intros k. exact (Hz (S k)).
Qed.

Lemma tvd_map : ltac2:(tb__ "0|6|
S1S1S36S38S0S0A2M0A1M1G1S2bS36S38S33S33A2M2A1S8bG0G2S5aR3A1R1A4S8bG0G2S5aR4A1R2A4A3S41G0G0S2bS3aG0A1M3S78G0R6R3A3S3dG0R2A2M4A3S2bG3S78G0R6R4A3G4A3S30S59R9R3A2S59RaR4A2A2F_;F_;Ft';Ft;Fk;S5bR6R4A2M5G5F_;F_;F_;Ftv';Ftv;Frho';Frho;").
Proof using .
  clear_sec.
  intros rho rho' tv. induction tv as [|t r IH]; intros [|t' r'] H Hz HD; cbn [map] in H; try discriminate; [exact I|].
  assert (H1 : tvv rho' t' = tvv rho t) by congruence. assert (H2 : map (tvv rho') r' = map (tvv rho) r) by congruence.
  destruct HD as [HD1 HD2]. cbn. split.
  - intros u' Hin' Hz1 Hz2. rewrite H1.
    destruct (In_nth_error _ _ Hin') as [k Hk].
    assert (exists u, nth_error r k = Some u) as [u Hu].
    { clear - H2 Hk. revert r H2 k Hk. induction r' as [|a r' IH]; intros [|b r] H2 [|k] Hk; cbn in *; try discriminate.
      - eexists; reflexivity.
      - assert (H2' : map (tvv rho') r' = map (tvv rho) r) by congruence. exact (IH r H2' k Hk). }
    assert (Eu : tvv rho' u' = tvv rho u).
    { clear - H2 Hk Hu. revert r H2 k Hk Hu. induction r' as [|a r' IH]; intros [|b r] H2 [|k] Hk Hu; cbn in *; try discriminate.
      - congruence.
      - assert (H2' : map (tvv rho') r' = map (tvv rho) r) by congruence. exact (IH r H2' k Hk Hu). }
    rewrite Eu. apply HD1; [eapply nth_error_In; exact Hu | apply (proj1 (Hz 0%nat t t' eq_refl eq_refl)); exact Hz1 |].
    apply (proj1 (Hz (S k) u u' Hu Hk)). exact Hz2.
  - apply IH; [exact H2 | | exact HD2]. intros k. exact (Hz (S k)).
Qed.

Lemma tvz_map : ltac2:(tb__ "0|6|
S1S1S36S38S0S0A2M0A1M1G1S2bS36S38S33S33A2M2A1S8bG0G2S5aR3A1R1A4S8bG0G2S5aR4A1R2A4A3S41G0G0S2bS3aG0A1M3S78G0R6R3A3S3dG0R2A2M4A3S2bG3S78G0R6R4A3G4A3S30S59R9R3A2S59RaR4A2A2F_;F_;Ft';Ft;Fk;S5fR6R4A2M5G5F_;F_;F_;Ftv';Ftv;Frho';Frho;").
Proof using .
  clear_sec.
  intros rho rho' tv. induction tv as [|t r IH]; intros [|t' r'] H Hz HN; cbn [map] in H; try discriminate.
  - constructor.
  - assert (H1 : tvv rho' t' = tvv rho t) by congruence. assert (H2 : map (tvv rho') r' = map (tvv rho) r) by congruence.
    inversion HN; subst. constructor.
    + intros Hnz'. rewrite H1. match goal with Ht : ~ tnz rho t -> _ |- _ => apply Ht end.
      intros Hz'. apply Hnz'. apply (proj2 (Hz 0%nat t t' eq_refl eq_refl)). exact Hz'.
    + apply IH; [exact H2 | | assumption]. intros k. exact (Hz (S k)).
Qed.

Definition echeckJ (nodes : list (sstate * list (sv * sv))) (e : edge) : bool := ltac2:(tb__ "0|5|
S3aS38S2S36S38S0S0A2A1M0A2M1A1S37Lx;M2S78G1Vnodes;S115Ve;A1A3G1G1S37Lp;R1S2G0G2S78G1Vnodes;S117Ve;A1A3G1G1S37Lp0;R1S2G0S42S42S42S87S116Ve;A1M3VNP;A2SddVNP;S3R5A1M4A2A2S57G4R4A2A2S67G3R4R1A3A2Ltvj;LTj;X38x1Lp0;S43X3ax2Ltvi;LTi;X38x1Lp;S43X3ax2").

Lemma JGi_transfer : ltac2:(tb__ "0|1|
S84S34S36S38S0S0A2A1M0G0S7dS1S1S36S52A1S51S2bS37S87R9VNP;A2S39A3SdfVNP;R9A2S2bS37S57RaR9A2S39A3S2bS37S67RcRaR9A3S39A3S11RcR8R7A3S64RcRaR9R7R6A5S64RcRbS85R9RfA2R8R7A5F_;F_;F_;F_;F_;F_;Fmd;Ftr;Frho';Frho;FAi;Ftvj;Ftvi;Fn;Fs;").
Proof using ML.
  intros s n tvi tvj Ai rho rho' tr md H1 H2 H3 H5 Hag HJ.
  destruct HJ as (Hav & Hk & HM & HP & (HN & HD & HZ) & HK & HP0).
  pose proof (agree_below_vals _ _ _ Hag) as Hav'.
  pose proof (rho_sub_agree s NP rho' H1) as Hids.
  destruct (tv_sub_eqb_sound s tvi tvj rho' H5) as [M1 M2].
  split; [|split; [exact Hk|split; [|split; [exact HP|split; [split; [|split]|split; [|exact HP0]]]]]].
  - eapply agree_vals_trans; [exact Hav|]. eapply agree_vals_trans; [eapply agree_vals_le; [exact H2|exact Hav']|].
    apply agree_below_vals. exact Hids.
  - eapply MInvR_mem; [exact HM| |reflexivity]. intros a _ _. cbn [rho_sub rm]. destruct Hag as (_ & _ & Hm). symmetry. apply Hm.
  - eapply tvin_map; [exact M1 | exact M2 |]. eapply tvin_agree; [exact Hav' | exact H3 | exact HN].
  - eapply tvd_map; [exact M1 | exact M2 |]. eapply tvd_agree; [exact Hav' | exact H3 | exact HD].
  - eapply tvz_map; [exact M1 | exact M2 |]. eapply tvz_agree; [exact Hav' | exact H3 | exact HZ].
  - intros a Ha Hp. cbn [rho_sub rm]. destruct Hag as (_ & _ & Hm). rewrite <- (Hm (Z_to_bv 64 a)). exact (HK a Ha Hp).
Qed.

Lemma JG_transfer : ltac2:(tb__ "0|1|
S84S34S36S38S0S0A2A1M0G0S1S1S36S52A1S51S2bS37S87R8VNP;A2S39A3SdfVNP;R8A2S2bS37S57R9R8A2S39A3S2bS37S67RbR9R8A3S39A3S11RbR8R7A3S55RbR9R7R6A4S55RbS85R9ReA2R8R7A4F_;F_;F_;F_;F_;F_;Fmd;Ftr;Frho';Frho;Ftvj;Ftvi;Fn;Fs;").
Proof using ML.
  intros s n tvi tvj rho rho' tr md H1 H2 H3 H5 Hag [Ai HJ]. exists Ai. eapply JGi_transfer; eauto.
Qed.

Lemma echeckJ_sound : ltac2:(tb__ "0|1|
S36S38S2S36S38S0S0A2A1A2M0A1S10eS2bS37S69R2R1A2S39A3S118S8bG0S10fS65R3A4R2A2F_;Fe;Fnodes;").
Proof using ML.
  intros nodes e H Ti Tj Hi Hj rho rho' tr md Hag HJ HF.
  unfold echeckJ in H. rewrite nth_error_map in Hi, Hj.
  destruct (nth_error nodes (e_src e)) as [[Si tvi]|]; [|discriminate].
  destruct (nth_error nodes (e_tgt e)) as [[Sj tvj]|]; [|discriminate].
  cbn in Hi, Hj. injection Hi as <-. injection Hj as <-. cbn [nodeI fst snd] in *.
  apply andb_prop in H as [H H5]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2]. apply Pos.leb_le in H2.
  eapply JG_transfer; eauto.
Qed.

Lemma echeckJ_all : ltac2:(tb__ "0|1|
S36S38S2S36S38S0S0A2A1A2M0A1S36S10eA1S2bS37S79S10eS69R2A1R1A3S39A3S8cS10eS118S8bG0S10fS65R3A4A1R2A3F_;Fes;Fnodes;").
Proof using ML.
  intros nodes es H. apply Forall_forall. intros e He. apply echeckJ_sound.
  exact (proj1 (forallb_forall _ _) H e He).
Qed.

Definition jcert (fuel : nat) (cutpcs : list Z) (g : positive) (cutsD exitsD : list (sstate * list (sv * sv))) : bool := ltac2:(tb__ "0|4|
S42S79S38S2S36S38S0S0A2A1M0A2M1G1S46S22S3cS2G0R1A3A1A1Ln;VcutsD;A3S3aS36S10eA1M2A1S37Lx;S114Vsegs;Vfuel;Vcutpcs;Vg;S8bG1S2S3cS2G0A2M3VcutsD;A4S8bG1S2G3VexitsD;A4A6G2S79S10eS69S40G1VcutsD;VexitsD;A3A1R1A3Les;S43X3ax2A2").

Lemma map_fst_nodeI : ltac2:(tb__ "0|2|
S36S38S2S36S38S0S0A2A1M0A2M1A1S2bS36S2A1S8bS38S2S4aA2S2S3cS2S4aA2S8bG1S10fS65R1A4A4S8bG1S2S3cS2G0A2R1A4A3Fl;").
Proof using . clear_sec. intros l. rewrite map_map. apply map_ext. intros [a b]. reflexivity. Qed.

Theorem cfg_sound_JG : ltac2:(tb__ "0|5|
S41S36S33A1S34S36S38S2S36S38S0S0A2A1M0A2M1A1M2G2S9aOF_;S99S4bVsegs;R2VKc;A3S2bS37S72R8R7R6R5R4A5S39A3S2G0S1S77G1S3bS2G0R3R2A4M3R8A3S9bVsegs;R8S49Vsegs;S55R3A1R4R2A4M4S9aS2eS112Vsegs;S8bG1S10fS65RbA4R1A3R8R1A1A2Lw;A4F_;Frho;FtvX;FX;S2G0S1S77G1G3RaA3S9bVsegs;R9G4R8A4F_;Frho;FtvT;FT;F_;F_;F_;FQ;Fok;FexitsD;FcutsD;Fg;Fcutpcs;Ffuel;").
Proof using ML.
  intros fuel cutpcs g cutsD exitsD ok Q Hok Hc Hexits T tvT rho HinT.
  unfold jcert in Hc. apply andb_prop in Hc as [Hstrict Hc].
  destruct (cfg_edges segs fuel cutpcs g (map fst cutsD) (map fst exitsD)) as [es|] eqn:Hes; [|discriminate].
  apply (cfg_sound_genJ segs fuel cutpcs g (map nodeI cutsD) (map nodeI exitsD) es ok Q).
  - intros T' J' Hin. apply in_map_iff in Hin as ([S k] & Heq & _). cbn in Heq. injection Heq as <- <-.
    apply ok_frameJ_JG. exact Hok.
  - intros T' J' Hin Hlen. exfalso. apply in_map_iff in Hin as ([S k] & Heq & Hin). cbn in Heq. injection Heq as <- <-.
    pose proof (proj1 (forallb_forall _ _) Hstrict _ Hin) as X. cbn [fst] in X. rewrite Hlen in X. discriminate.
  - rewrite !map_fst_nodeI. exact Hes.
  - rewrite <- map_app. apply echeckJ_all. exact Hc.
  - intros X JX rho' Hin. apply in_map_iff in Hin as ([S k] & Heq & Hin). cbn in Heq. injection Heq as <- <-.
    exact (Hexits S k rho' Hin).
  - exact (in_map nodeI cutsD (T, tvT) HinT).
Qed.

Definition edesc : Type := ltac2:(tb__ "0|0|
S38S38S2S36S38S0S0A2A1A2S38S33S0A2A2").
Definition ed_state (n : edesc) : sstate := fst (fst n).
Definition ed_tv (n : edesc) : list (sv * sv) := snd (fst n).
Definition ed_rank (n : edesc) : Z := fst (snd n).
Definition ed_var (n : edesc) : sv := snd (snd n).
Definition emeas (n : edesc) (rho : valuation) : Z := ltac2:(tb__ "0|0|
S8fS96S6aVn;A1S90Z2Z40A2A2S9eQ40S8Vrho;S70Vn;A1A2A2A2").
Definition enodeI (n : edesc) : enodeJ := ltac2:(tb__ "0|0|
S3bS38S2S4aA2S1S33Frho;S3bS2S4aS61Vn;A1S55S6bVn;A1A1A4S6cVn;A1A4").

Definition eecheckJ (nodes : list edesc) (e : edge) : bool := ltac2:(tb__ "0|7|
S3aS56A1S37Lx;M0S78S56Vnodes;S115Ve;A1A3S56G0S78S56Vnodes;S117Ve;A1A3S56S42S42S42S42S42S42S87S116Ve;A1M1VNP;A2SddVNP;S3S61R2A1A1M2A2A2S57G2S6bR2A1M3A2A2S67G1G3S6bR1A1A3A2SdG2S70R2A1M4A2A2S91Z0S6aR1A1M5A2A2S47S93G5S6aR2A1M6A2S42S94G5G6A2S102S6S119Ve;A1A1S89G1S70R1A1A2Z1G4A4A2A2A2Lnj;S43X3ax2Lni;S43X3ax2").

Lemma eecheckJ_sound : ltac2:(tb__ "0|0|
S36S56A1S10eS2bS37S71R2R1A2S39A3S11aS8bS56S110S68R3A4R2A2F_;Fe;Fnodes;").
Proof using ML.
  intros nodes e H Ti Tj Hi Hj rho rho' tr md Hag HJ HF.
  unfold eecheckJ in H. rewrite nth_error_map in Hi, Hj.
  destruct (nth_error nodes (e_src e)) as [ni|]; [|discriminate].
  destruct (nth_error nodes (e_tgt e)) as [nj|]; [|discriminate].
  cbn in Hi, Hj. injection Hi as <-. injection Hj as <-.
  cbn [enodeI enj_state enj_pred enj_meas fst snd] in *.
  apply andb_prop in H as [H Hdec]. apply andb_prop in H as [H Hrk]. apply andb_prop in H as [H Hvb].
  apply andb_prop in H as [H H5]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply Pos.leb_le in H2. apply Z.leb_le in Hrk.
  split; [eapply JG_transfer; eauto|].
  unfold emeas. rewrite <- eval_subst.
  rewrite (eval_agree _ rho rho' (ed_var ni) Hag Hvb).
  pose proof (urange (eval rho' (sv_subst (e_sub e) (ed_var nj)))) as R1.
  pose proof (urange (eval rho' (ed_var ni))) as R2.
  apply orb_prop in Hdec. destruct Hdec as [Hlt | Heq].
  - apply Z.ltb_lt in Hlt. nia.
  - apply andb_prop in Heq as [Heq Hu]. apply Z.eqb_eq in Heq.
    pose proof (uleq_sound rho' _ _ 1 _ HF Hu) as U1. unfold U in U1. rewrite Heq. lia.
Qed.

Definition ejcert (fuel : nat) (cutpcs : list Z) (g : positive) (cutsE exitsE : list edesc) : bool := ltac2:(tb__ "0|1|
S42S79S56S56S46S22S61R1A1A1A1Ln;VcutsE;A3S3aS36S10eA1M0A1S37Lx;S114Vsegs;Vfuel;Vcutpcs;Vg;S8bS56S2S61VcutsE;A4S8bS56S2S61VexitsE;A4A6G0S79S10eS71S40S56VcutsE;VexitsE;A3A1R1A3Les;S43X3ax2A2").

Lemma map_ed_state : ltac2:(tb__ "0|0|
S36S56A1S2bS36S2A1S8bS110S2S11bS8bS56S110S68R1A4A4S8bS56S2S61R1A4A3Fl;").
Proof using . clear_sec. intros l. rewrite map_map. apply map_ext. intros [[a b] c]. reflexivity. Qed.

Theorem cfg_complete_JG : ltac2:(tb__ "0|7|
S41S36S33A1S34S36S56A1M0G0S99S2bS37S75R6R5R4R3R2A5S39A3S2S36S38S0S0A2A1M1S38S33S0A2M2S1S77S38S38S2G1A2M3G2A2M4S3bG3G2S3bS2G1R4R3A4R2A4M5R7A3S9cVsegs;S49Vsegs;S55R4A1R5R2A4M6S9aS2eS113Vsegs;S8bS56S110S68RaA4S6cS3bG3G2S3bS2G1R6R5A4R4A4R3A2R1A4R8R1A1A2Lw;A3F_;Frho;FrvX;FtvX;FX;S2G1G2S1S77G4G5R9A3S9cVsegs;G6R8A3F_;Frho;FrvT;FtvT;FT;F_;F_;FQ;FexitsE;FcutsE;Fg;Fcutpcs;Ffuel;").
Proof using ML.
  intros fuel cutpcs g cutsE exitsE Q Hc Hexits T tvT rvT rho HinT.
  unfold ejcert in Hc. apply andb_prop in Hc as [Hstrict Hc].
  destruct (cfg_edges segs fuel cutpcs g (map ed_state cutsE) (map ed_state exitsE)) as [es|] eqn:Hes; [|discriminate].
  change (etriple segs (SPJ segs (enj_pred (enodeI (T, tvT, rvT))) (enj_state (enodeI (T, tvT, rvT))) rho) Q).
  apply (cfg_complete_genJ segs fuel cutpcs g (map enodeI cutsE) (map enodeI exitsE) es Q).
  - apply forallb_forall. intros m Hm. apply in_map_iff in Hm as (m0 & <- & Hm0).
    exact (proj1 (forallb_forall _ _) Hstrict m0 Hm0).
  - rewrite !map_ed_state. exact Hes.
  - rewrite <- map_app. apply Forall_forall. intros e He. apply eecheckJ_sound.
    exact (proj1 (forallb_forall _ _) Hc e He).
  - intros En rhoE HinE. apply in_map_iff in HinE as ([[X tvX] rvX] & <- & HinE0).
    exact (Hexits X tvX rvX rhoE HinE0).
  - exact (in_map enodeI cutsE (T, tvT, rvT) HinT).
Qed.

Definition edrop (n : edesc) : sstate * list (sv * sv) := ltac2:(tb__ "0|0|
S3bS2S36S38S0S0A2A1S61Vn;A1S6bVn;A1A4").

Lemma map_fst_edrop : ltac2:(tb__ "0|2|
S36S56A1S2bS36S2A1S8bS38S2S36S38S0S0A2A1M0A2M1S2S3cS2G0A2S8bS56G1S62R1A4A4S8bS56S2S61R1A4A3Fl;").
Proof using . clear_sec. intros l. rewrite map_map. apply map_ext. intros [[a b] c]. reflexivity. Qed.

Lemma eecheckJ_echeckJ : ltac2:(tb__ "0|0|
S36S56A1S10eS2bS37S71R2R1A2S39A3S2bS37S69S8bS56S38S2S36S38S0S0A2A1A2S62R3A4R2A2S39A3F_;Fe;Fnodes;").
Proof using .
  clear_sec. intros nodes e H. unfold eecheckJ in H. unfold echeckJ. rewrite !nth_error_map.
  destruct (nth_error nodes (e_src e)) as [ni|]; [|discriminate].
  destruct (nth_error nodes (e_tgt e)) as [nj|]; [|discriminate]. cbn [option_map edrop fst snd].
  apply andb_prop in H as [H _]. apply andb_prop in H as [H _]. apply andb_prop in H as [H _]. exact H.
Qed.

Lemma ejcert_jcert : ltac2:(tb__ "0|2|
S41S36S33A1S34S36S56A1M0G0S2bS37S75R5R4R3R2R1A5S39A3S2bS37S72R6R5R4S8bS56S38S2S36S38S0S0A2A1A2M1S62R3A4S8bS56G1S62R2A4A5S39A3F_;FexitsE;FcutsE;Fg;Fcutpcs;Ffuel;").
Proof using .
  clear_sec. intros fuel cutpcs g cutsE exitsE H. unfold ejcert in H. unfold jcert.
  rewrite !map_fst_edrop. apply andb_prop in H as [Hs H]. apply andb_true_intro. split.
  - apply forallb_forall. intros n Hn. apply in_map_iff in Hn as (m & <- & Hm). cbn [edrop fst].
    exact (proj1 (forallb_forall _ _) Hs m Hm).
  - destruct (cfg_edges segs fuel cutpcs g (map ed_state cutsE) (map ed_state exitsE)) as [es|]; [|discriminate].
    rewrite <- map_app. apply forallb_forall. intros e He. apply eecheckJ_echeckJ.
    exact (proj1 (forallb_forall _ _) H e He).
Qed.

Theorem cfg_sound_JGE : ltac2:(tb__ "0|7|
S41S36S33A1S34S36S56A1M0G0S9aOF_;S99S4bVsegs;R2VKc;A3S2bS37S72R8R7R6S8bS56S38S2S36S38S0S0A2A1M1A2M2S62R5A4S8bS56G2S62R4A4A5S39A3S2G1S38S33S0A2M3S1S77S38G2G3A2M4S3bG2G3S3bS2G1R4R3A4R2A4M5R9A3S9bVsegs;R9S49Vsegs;S55R4A1R5R2A4M6S9aS2eS112Vsegs;S8bG2S10fS65S8bS56G2S62RcA4A4R1A3R9R1A1A2Lw;A4F_;Frho;FrvX;FtvX;FX;S2G1G3S1S77G4G5RbA3S9bVsegs;RaG6R9A4F_;Frho;FrvT;FtvT;FT;F_;F_;F_;FQ;Fok;FexitsE;FcutsE;Fg;Fcutpcs;Ffuel;").
Proof using ML.
  intros fuel cutpcs g cutsE exitsE ok Q Hok Hc Hexits T tvT rvT rho HinT.
  apply (cfg_sound_JG fuel cutpcs g (map edrop cutsE) (map edrop exitsE) ok Q Hok Hc).
  - intros X tvX r Hin. apply in_map_iff in Hin as ([[X' tv'] rv'] & Heq & Hin). cbn in Heq. injection Heq as <- <-.
    exact (Hexits X' tv' rv' r Hin).
  - exact (in_map edrop cutsE (T, tvT, rvT) HinT).
Qed.

Lemma reenter_cutGE : ltac2:(tb__ "0|3|
S9aOF_;S36S56A1S2S36S38S0S0A2A1M0S38S33S0A2M1S99S1S77S38S38S2G0A2M2G1A2S3bG2G1S3bS2G0R5R4A4R3A4R6A3S9bVsegs;R8S49Vsegs;S55R5A1R6R2A4S9aS2eS112Vsegs;S8bG2S10fS65S8bS56G2S62R8A4A4R1A3R4R1A1A2Lw;A4F_;Frho;FQ;Frv;Ftv;FT;FcutsE;Fok;").
Proof using .
  intros ok cutsE T tv rv Q rho Hin.
  eapply triple_conseq; [| intros w Hw; exact Hw | apply triple_refl].
  intros w Hw. left. exists T, (JG tv), rho. split; [|exact Hw].
  exact (in_map nodeI (map edrop cutsE) (T, tv) (in_map edrop cutsE (T, tv, rv) Hin)).
Qed.

Lemma ereenter_cutE : ltac2:(tb__ "0|4|
S36S56A1S2S36S38S0S0A2A1M0S38S33S0A2M1S99S33S1S77S38S38S2G0A2M2G1A2S3bG2G1S3bS2G0R6R5A4R4A4R7A3S2cS8eZ0S6cS3bG2G1S3bS2G0R7R6A4R5A4R2A2M3A2S8dG3R3A2A2S9cVsegs;S49Vsegs;S55R7A1R8R3A4S9aS2eS113Vsegs;S8bS56S110S68RaA4R5R1A4R6R1A1A2Lw;A3F_;F_;Frho;Fbound;FQ;Frv;Ftv;FT;FcutsE;").
Proof using .
  intros cutsE T tv rv Q bound rho Hin Hm w Hw. exists w. split; [apply wsteps_refl|]. left.
  exists (enodeI (T, tv, rv)), rho. split; [exact (in_map enodeI cutsE _ Hin)|]. split; [exact Hw | exact Hm].
Qed.

Lemma ereenter_rank : ltac2:(tb__ "0|3|
S36S56A1S2S36S38S0S0A2A1M0S33S0S99S56S1S1S77S38S38S2G0A2M1S38S33S0A2M2A2S3bG1G2S3bS2G0R8R7A4S3bS33S0R6R5A4A4R9A3S8eZ0R7A2S8eS8fR8Z1A2S6aR5A1A2S9cVsegs;S49Vsegs;S55RaA1RbR4A4S9aS2eS113Vsegs;S8bS56S110S68RdA4S6cR7R6A2R1A4R8R1A1A2Lw;A3F_;F_;F_;Frho;FrhoX;FX;FQ;FvT;FrT;Ftv;FT;FcutsE;").
Proof using .
  intros cutsE T tv rT vT Q X rhoX rho Hin H0 Hr. apply (ereenter_cutE cutsE T tv (rT, vT) Q); [exact Hin|].
  unfold emeas, ed_rank, ed_var in *. cbn [fst snd] in *.
  pose proof (urange (eval rho vT)). pose proof (urange (eval rhoX (snd (snd X)))). nia.
Qed.

Lemma SPJ_entails_JG : ltac2:(tb__ "0|2|
S2S2S84S36S38S0S0A2A1M0G0S1S9aS2bS37SceR7R6R5A3S39A3S2bS37S87R6VNP;A2S39A3S2bS37SddVNP;S3R9A1A2S39A3S2bS37S57S3RaA1R7A2S39A3S2bS37S67R9R8R7A3S39A3S49Vsegs;S55R9A1M1RcR7R6A5S49Vsegs;G1RcS85R8RbA2R7A5F_;F_;F_;F_;F_;F_;Fw;Frho;Ftvj;Ftvi;Fs;FT;FL;").
Proof using ML.
  intros L T s tvi tvj rho w He H1 H2 H3 H5 [Hsm HJ]. apply Pos.leb_le in H2.
  split; [eapply entails_sound; eauto|].
  destruct w as [tr [ms md]]. eapply JG_transfer; eauto. apply agree_below_refl.
Qed.

Lemma JG_tv_requiv : ltac2:(tb__ "0|3|
S36S38S0S0A2M0A1M1G1S1S36S52A1S51S7bG0G0G0G0S2cS1S2bS9dQ40A1M2S8R1S3cS0S0R2A3A2S8R1S3cS0S0R3A3A2A3Fr;S1S2bG2S8R1S3fS0S0R2A3A2S8R1S3fS0S0R3A3A2A3Fr;A2Lt';Lt;R5R4A5S55R6R4R3R2A4S55R6R5R4R3A4F_;F_;Fmd;Ftr;Frho;Ftv';Ftv;").
Proof using .
  intros tv tv' rho tr md HF (Ai & Hav & Hk & HM & HP & (HN & HD & HZ) & HK & HP0).
  assert (M1 : map (tvv rho) tv' = map (tvv rho) tv).
  { clear - HF. induction HF as [|t t' r r' [E1 E2] _ IH]; [reflexivity|]. cbn [map]. f_equal; [|exact IH]. unfold tvv. rewrite E1, E2. reflexivity. }
  assert (M2 : forall k t t', nth_error tv k = Some t -> nth_error tv' k = Some t' -> (tnz rho t' <-> tnz rho t)).
  { clear - HF. induction HF as [|t t' r r' [E1 E2] _ IH]; intros [|k] a b Ha Hb; cbn in Ha, Hb; try discriminate.
    - injection Ha as <-. injection Hb as <-. unfold tnz. rewrite E1. tauto.
    - exact (IH k a b Ha Hb). }
  exists Ai. split; [exact Hav|]. split; [exact Hk|]. split; [exact HM|]. split; [exact HP|]. split; [|split; [exact HK|exact HP0]].
  split; [eapply tvin_map; eauto | split; [eapply tvd_map; eauto | eapply tvz_map; eauto]].
Qed.

Lemma JG_drop_tv : ltac2:(tb__ "0|1|
S36S38S0S0A2M0A1S41S1S36S52A1S51S55R5R3R2R1A4S55S66G0R5R6A3R4R3R2A4F_;Fmd;Ftr;Frho;Fi;Ftv;").
Proof using .
  intros tv i rho tr md (Ai & Hav & Hk & HM & HP & (HN & HD & HZ) & HK & HP0).
  exists Ai. split; [exact Hav|]. split; [exact Hk|]. split; [exact HM|]. split; [exact HP|]. split; [|split; [exact HK|exact HP0]].
  split; [|split].
  - unfold tvin in *. apply Forall_forall. intros t Ht. apply (proj1 (Forall_forall _ _) HN). eapply remove_nth_In. exact Ht.
  - apply tvd_remove. exact HD.
  - unfold tvz in *. apply Forall_forall. intros t Ht. apply (proj1 (Forall_forall _ _) HZ). eapply remove_nth_In. exact Ht.
Qed.

Lemma JG_drop_null_vec : ltac2:(tb__ "0|3|
S36S38S0S0A2M0A1S41G0S2S2S36S41A1S36S4A1M1S4S1S9aS2bS3aS2A1S12cR7S3eS12aS12bR5A1S44S12aA1A3A2S3dS2R6A2A3S2bG1S1dR7A1S40S4R5S3eS4R4S44S4A1A3A3A3S2bS3aG0A1S78G0RcRbA3S3dG0RaA2A3S2bS37SfS12R6A1S3cS0S0RbA3A2S39A3S2bS37SfS13R7A1SbZ0A1M2A2S39A3S2bS37SfS15R8A1S3fS0S0RdA3A2S39A3S2bS37S7aS5S1cS17S10bS3cS0S0ReA3G2A3A1S6RdA1A3S39A3S2bS37SddVNP;S3RdA1A2S39A3S2bS37S57S3ReA1R12A2S39A3S49Vsegs;S55R13A1R10RbRaA5S2dS1S1S49Vsegs;S55S66G0R14R15A3A1S105R11RfA2R1RcA5Lrho';A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fw;Frho;Fo;Fobjs;Fperm;FX1;FX;Ft;Fi;Ftv;").
Proof using ML.
  intros tv i t X X1 perm objs o rho [tr [ms md]] Hx Ho Hnth Hb Hl Hh Hz Hnf Hnb HJX.
  apply sv_eqb_sound in Hb. apply sv_eqb_sound in Hl. apply sv_eqb_sound in Hh. apply Pos.leb_le in Hnf.
  pose proof (SPJ_xforms segs (JG tv) [XSelect perm] rho X X1 _ Hx HJX) as [Hsm HJ].
  destruct HJX as [HsmX _].
  apply existsb_exists in Hz as (f & Hf & Hfe). apply sprop_eqb_sound in Hfe. subst f.
  pose proof (proj1 (Forall_forall _ _) (smatch_facts_hold segs _ _ _ HsmX) _ Hf) as Hz. apply holds_beq in Hz.
  rewrite U_lit in Hz. unfold M64v in Hz. rewrite Z.mod_0_l in Hz by lia.
  pose proof HJ as (Ai & Hav & Hk & HM & HP & (HN & HD & HZ) & HK & HP0).
  assert (Hsz : bv_unsigned (eval rho (snd t)) = 0).
  { pose proof (proj1 (Forall_forall _ _) HZ t (nth_error_In _ _ Hnth)) as Z0. unfold tnz, tvv in Z0. cbn [fst snd] in Z0. apply Z0. lia. }
  exists (rho_absorb rho [o] ms). split.
  - apply (smatch_frame_in segs rho X1 objs [o] tr ms md Ho Hsm).
  - assert (Hag : agree_below (ss_next X1) rho (rho_absorb rho [o] ms)).
    { split; [intros; reflexivity|]. split; [intros; reflexivity|].
      intros a. unfold rho_absorb. cbn [rm]. destruct (in_ranges_dec rho [o] a) as [Hi|]; [|reflexivity].
      exfalso. destruct Hi as (o' & [<-|[]] & Hr).
      unfold obj_range, obj_lo_of, obj_hi_of in Hr. rewrite Hb, Hl, Hh in Hr. cbn [fst snd] in Hr.
      rewrite soff_lit_small in Hr by lia. unfold soff in Hr. rewrite bv_signed_U, Hsz in Hr. cbn in Hr. lia. }
    apply JG_drop_tv. eapply (stableJ_JG (ss_next X1) tv); [exact Hnf | exact Hnb | exact Hag | exact HJ].
Qed.

Lemma mul_comm_eval : ltac2:(tb__ "0|0|
S1S0S0S2bS9dQ40A1S8R3S10S109R2R1A3A2S8R3S10S109R1R2A3A2A3Fb;Fa;Fr;").
Proof using . intros r a b. apply bv_eq. rewrite !U_mul. rewrite Z.mul_comm. reflexivity. Qed.

Lemma tracked_range : ltac2:(tb__ "0|5|
S1S4S38S0S0A2S33S2bS0S12R3A1S3cS0S0R2A3A3S2bS0S13R4A1SbZ0M0A1A3S2bS0S15R5A1S3fS0S0R4A3A3S2cS8eS3cS33S33SeR7R6A2M1A3R4A2S8dR4S3fS33S33G1A3A2A2S2cS2cS8eS3cS33S33S5aR8R6A2M2A3M3R5A2S8dR5S8fG3S3fS33S33G2A3M4A2A2A2S8dG0G4A2A2F_;F_;F_;F_;Fa;Ft;Fo;Frho;").
Proof using .
  clear_sec. intros rho o t a Hb Hl Hh Hr.
  unfold obj_range, obj_lo_of, obj_hi_of in Hr. rewrite Hb, Hl, Hh in Hr. cbn [fst snd] in Hr.
  rewrite soff_lit_small in Hr by lia. unfold soff in Hr. rewrite bv_signed_U in Hr.
  unfold tvv. cbn [fst snd]. pose proof (bv_urange (eval rho (snd t))) as R.
  destruct (Zsigned_spec (bv_unsigned (eval rho (snd t)))) as [[_ Ez]|[_ Ez]]; rewrite Ez in Hr; unfold M64v in R, Ez, Hr |- *; lia.
Qed.

Lemma tvd_nth : ltac2:(tb__ "0|3|
S1S36S38S0S0A2M0A1S41S41G0G0S5bR6R5A2S2bS3aG0A1M1S78G0R6R5A3S3dG0R3A2M2A3S2bG1S78G0R7R5A3G2A3S2fS2bS41R7R6A3A1S59RaR6A2S59RbR6A2S2fS2bS38S33S33A2S5aRcR8A2S5aRcR7A2A3A1F_;F_;F_;F_;F_;F_;Ftj;Fti;Fj;Fi;Ftv;Frho;").
Proof using .
  clear_sec. intros rho tv. induction tv as [|t r IH]; intros i j ti tj HD Hi Hj Hij Hzi Hzj; [destruct i; discriminate|].
  destruct HD as [H1 H2]. destruct i as [|i], j as [|j]; cbn in Hi, Hj.
  - congruence.
  - injection Hi as <-. exact (H1 tj (nth_error_In _ _ Hj) Hzi Hzj).
  - injection Hj as <-. intros Ex. apply (H1 ti (nth_error_In _ _ Hi) Hzj Hzi). symmetry. exact Ex.
  - eapply IH; eauto.
Qed.

Lemma robjs_check_sound : ltac2:(tb__ "0|5|
S7dS1S36S5A1S36S38S0S0A2M0A1S3aS41A1M1S4S37F_;S36S4A1S3aS33A1M2S1S51Sb0Vsegs;VC;RaR2R1A5Se2RaScfS7eRbA1A1A2S8cS5S7RbA1RaA3S5dRdRcRaA3S5bRdRbA2S5fReRcA2S2bS37Sf1ReRdRcRbRaA5S39A3S4S33S77S4R2RdA3S2bS37RfR3A1S39A3S2cS8eS3cS33S33SeR14R4A2M3A3R3A2S8dR3S3fS33S33G3A3A2A2Se4R16RfR4A3F_;F_;F_;Fa;Fo;G1OLskip;ReS41G2OLx;M4RcS33S2dG0G0S2cS2bS3aG0A1S78G0R12R3A3S3dG0R1A2A3S2cS59R14R1A2S2bS33S3cS33S33S5aR14R1A2A3R2A3A2A2Lt;A2Lxb;S31X3ax2Li;G4RbS33S31Lz;S32X3ax2X3ax2Se3R13RcR12RdA4F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd;FrhoM;Fx;FR;Fextra;Fskip;Ftv;Ffacts;Frho;FAi;").
Proof using .
  clear_sec. intros Ai rho facts tv skip extra R x rhoM md HM HT HF HN HD HZ Hchk Hextra Hx o a Ho Hr.
  unfold robjs_check in Hchk. pose proof (proj1 (forallb_forall _ _) Hchk o Ho) as Hc. cbn beta in Hc.
  apply lazy_orb_prop in Hc as [Hc|Hc]; [left; exact (robj_stack_sound facts rho _ o a HF HT Hc Hr)|].
  apply lazy_orb_prop in Hc as [Hc|Hc]; [|exact (Hextra o a Ho Hc Hr)].
  destruct (robj_tracked_sound tv skip o Hc) as (j & t & Hj & Hsk & Hb & Hl & Hh).
  destruct (tracked_range rho o t a Hb Hl Hh Hr) as [Ha Hpos].
  pose proof (nth_error_In _ _ Hj) as Hin.
  assert (Hnz : tnz rho t).
  { intros Hz. pose proof (proj1 (Forall_forall _ _) HZ t Hin (fun H => H Hz)). lia. }
  destruct (proj1 (Forall_forall _ _) HN t Hin Hnz) as (Tpos & Tin & Tfb).
  right; right. exists (fst (tvv rho t)), (snd (tvv rho t)). rewrite <- surjective_pairing.
  split; [exact Tin|]. split; [|exact Ha].
  destruct skip as [i|], x as [xb|]; try contradiction; [|discriminate].
  destruct Hx as (ti & Hi & Hzi & Hxb). intros Ex. injection Ex as Ex. subst xb.
  assert (Hij : i <> j) by (intros ->; apply Hsk; reflexivity).
  destruct (proj1 (Forall_forall _ _) HN ti (nth_error_In _ _ Hi) Hzi) as (Tpos' & Tin' & _).
  pose proof (tvd_nth rho tv i j ti t HD Hi Hj Hij Hzi Hnz) as Hne.
  rewrite (surjective_pairing (tvv rho ti)) in Tin', Hne. rewrite (surjective_pairing (tvv rho t)) in Tin, Hne.
  eapply (blocks_bases_differ Ai rhoM md _ _ _ _ HM Tin' Tin Hne Tpos' Tpos). exact Ex.
Qed.

Theorem free_site_auto : ltac2:(tb__ "0|4|
S9aOF_;S2S84S36S4A1M0S1S36S38S0S0A2M1A1S41G1S99Sb5Vsegs;R9VKc;A3SefS2bS3aG0A1ScdRaSb8VE;A1M2R9A3S3dG0R8A2A3S2bS37S5eRbG2RaR9S3eS2Sb7VE;A1M3S44S2A1A3A5S39A3S2bS37SddVNP;S3RcA1A2S39A3S2bS37S57S3RdA1R9A2S39A3S2bS3aG1A1S78G1RaR9A3S3dG1R8A2A3S2bS37SfS3cS0S0R9A3S83RePcA2A2S39A3S2bS37SfS3fS0S0RaA3S83RfPdA2A2S39A3S2bS37S7aS5S1cS1aS17S10bS3cS0S0RbA3SbZ0A1A3A1A1S6R11A1A3S39A3S2bS37Sf1S6R12A1ReS3dS41RdA2S4S43L_;R10A5S39A3S1S9bVsegs;R15S49Vsegs;S55S66G1RfR10A3A1S58R14R13R12G3A4R1A4RdA4Frho';S9bVsegs;R15S49Vsegs;S55R10A1R14R11A4RdA4F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ft;Fi;Ftv;Frho;FR;Fs;FCl;Fok;").
Proof using ML.
  intros ok Cl s R rho tv i t Q Hok MC He Hchk Hnf Hnb Hnth H12 H13 Hnz Hrc Tfree.
  apply sv_eqb_sound in H12. apply sv_eqb_sound in H13.
  apply (free_callJ ok Cl s R rho tv i t Q Hok MC He Hchk Hnf Hnb Hnth); [|exact Tfree].
  intros Ai HF HP0 Hav HP HN HD HZ (rhoM & md & HM) HT.
  apply existsb_exists in Hnz as (f & Hf & Hfe). apply sprop_eqb_sound in Hfe. subst f.
  pose proof (proj1 (Forall_forall _ _) HF _ Hf) as Hnz.
  assert (Tnz : tnz rho t) by (rewrite (surjective_pairing t); apply (tnz_of_fact rho (fst t) (snd t)); exact Hnz).
  rewrite <- H12, <- H13. split; [exact Tnz|]. split; [reflexivity|].
  eapply (robjs_check_sound Ai rho (ss_facts Cl) tv (Some i) (fun _ => false) R _ rhoM md HM HT HF HN HD HZ Hrc).
  - intros o a _ Hx _. discriminate.
  - exists t. split; [exact Hnth|]. split; [exact Tnz|reflexivity].
Qed.

Theorem free_site_auto_ex : ltac2:(tb__ "0|4|
S2S84S36S4A1M0S1S36S38S0S0A2M1A1S41G1S99Sb6VKc;A1S6dS2bS3aG0A1ScdRaSb8VE;A1M2R9A3S3dG0R8A2A3S2bS37S5eRbG2RaR9S3eS2Sb7VE;A1M3S44S2A1A3A5S39A3S2bS37SddVNP;S3RcA1A2S39A3S2bS37S57S3RdA1R9A2S39A3S2bS3aG1A1S78G1RaR9A3S3dG1R8A2A3S2bS37SfS3cS0S0R9A3S83RePcA2A2S39A3S2bS37SfS3fS0S0RaA3S83RfPdA2A2S39A3S2bS37S7aS5S1cS1aS17S10bS3cS0S0RbA3SbZ0A1A3A1A1S6R11A1A3S39A3S2bS37Sf1S6R12A1ReS3dS41RdA2S4S43L_;R10A5S39A3S1S9cVsegs;S49Vsegs;S55S66G1RfR10A3A1S58R14R13R12G3A4R1A4RdA3Frho';S9cVsegs;S49Vsegs;S55R10A1R14R11A4RdA3F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ft;Fi;Ftv;Frho;FR;Fs;FCl;").
Proof using ML.
  intros Cl s R rho tv i t Q Hok MC He Hchk Hnf Hnb Hnth H12 H13 Hnz Hrc Tfree.
  apply sv_eqb_sound in H12. apply sv_eqb_sound in H13.
  apply (free_callJ_ex Cl s R rho tv i t Q Hok MC He Hchk Hnf Hnb Hnth); [|exact Tfree].
  intros Ai HF HP0 Hav HP HN HD HZ (rhoM & md & HM) HT.
  apply existsb_exists in Hnz as (f & Hf & Hfe). apply sprop_eqb_sound in Hfe. subst f.
  pose proof (proj1 (Forall_forall _ _) HF _ Hf) as Hnz.
  assert (Tnz : tnz rho t) by (rewrite (surjective_pairing t); apply (tnz_of_fact rho (fst t) (snd t)); exact Hnz).
  rewrite <- H12, <- H13. split; [exact Tnz|]. split; [reflexivity|].
  eapply (robjs_check_sound Ai rho (ss_facts Cl) tv (Some i) (fun _ => false) R _ rhoM md HM HT HF HN HD HZ Hrc).
  - intros o a _ Hx _. discriminate.
  - exists t. split; [exact Hnth|]. split; [exact Tnz|reflexivity].
Qed.

End Sum.

Section Posts.
Variable NP : positive.
Variable Kc : ltac2:(tb__ "0|0|
S36S52A1S51OF_;F_;").
Variable P0f : valuation -> Prop.
Variable FB : list (Z * Z).

Definition JLG (tv : list (sv * sv)) : jpost := ltac2:(tb__ "0|0|
S1S1S36S52A1S51S2cVKc;R2R1A2S2dS7dS7dS2cS2cSb0Vsegs;VC;R1R4R2A5S2cSfcR1A1SfbR5R1A2A2A2S2cSeeVFB;R1A2S2cS2cSf2VFB;R1R4Vtv;A4S2cSe5R4Vtv;A2SecR4Vtv;A2A2A2S2cSfdR5VFB;SaR5A1SaR4A1A4VP0f;R5A1A2A2A2A2LAi;A2A2Lmd;Ltr;Lrho;Lr0;").

Lemma exit_postG : ltac2:(tb__ "0|1|
S9aOF_;S1S36S38S0S0A2A1S36S38S2Sa2A2M0A1S2S99S77G0S3bS2Sa2R2S127R4A1A4R3A3S1S9bVsegs;R8S49Vsegs;Se7VNP;VKc;R7VP0f;VFB;R6A6R4R1A4S9aS2eR4R1A1Sa4Vsegs;VNP;R8R6R1A5A2Lw;A4Frho;F_;FX;FP;FPosts;Ftv;Frho0;Fok;").
Proof using .
  intros ok rho0 tv Posts P X Hin. apply (exit_postP segs ok _ NP rho0 Posts P (JLG tv) X Hin).
  intros rho tr md (Ai & Hav & Hk & HM & HP & HN & HK & HP0). split; [exact Hav|].
  split; [exact Hk|]. exists Ai. auto.
Qed.

Lemma eexit_postG : ltac2:(tb__ "0|1|
S1S36S38S0S0A2A1S36S38S2Sa2A2M0A1S2S99S77G0S3bS2Sa2R2S127R4A1A4R3A3S1S9cVsegs;S49Vsegs;Se7VNP;VKc;R7VP0f;VFB;R6A6R4R1A4S9aS2eR4R1A1Sa4Vsegs;VNP;R8R6R1A5A2Lw;A3Frho;F_;FX;FP;FPosts;Ftv;Frho0;").
Proof using .
  intros rho0 tv Posts P X Hin. apply (eexit_postP segs _ NP rho0 Posts P (JLG tv) X Hin).
  intros rho tr md (Ai & Hav & Hk & HM & HP & HN & HK & HP0). split; [exact Hav|].
  split; [exact Hk|]. exists Ai. auto.
Qed.

Lemma reenter_cutG : ltac2:(tb__ "0|0|
S9aOF_;S36S10fA1S2S4aS99S1S77S38S2S4aA2S3bS2S4aR4R3A4R5A3S9bVsegs;R7S49Vsegs;R4R5R2A4S9aS2eS112Vsegs;R7R1A3R4R1A1A2Lw;A4F_;Frho;FQ;FJ;FT;Fcuts;Fok;").
Proof using .
  intros ok cuts T J Q rho Hin.
  eapply triple_conseq; [| intros w Hw; exact Hw | apply triple_refl].
  intros w Hw. left. exists T, J, rho. split; [exact Hin | exact Hw].
Qed.

Definition JG_pre (tv : list (sv * sv)) : jpred := ltac2:(tb__ "0|0|
S1S36S52A1S51S127Vtv;R3R3R2R1A5Lmd;Ltr;Lrho;").

Lemma JG_pre_intro : ltac2:(tb__ "0|0|
S1S36S38S0S0A2A1S2S9aS49Vsegs;S128R3A1R2R4R1A5S49Vsegs;Se7VNP;VKc;R5VP0f;VFB;R4A6R3R5R2A5F_;Fw;FS;Ftv;Frho0;").
Proof using .
  intros rho0 tv S w [Hsm (Hk & Ai & HM & HP & HN & HK & HP0)]. split; [exact Hsm|].
  exists Ai. split; [apply agree_vals_refl|]. repeat (split; [assumption|]). exact HP0.
Qed.
End Posts.

Section Client.
Variable NP : positive.
Variable Kc : ltac2:(tb__ "0|0|
S36S52A1S51OF_;F_;").
Variable rho0 : valuation.
Variable P0f : valuation -> Prop.
Variable FB : list (Z * Z).
Hypothesis ML : malloc_laws.

Variable P0c : ltac2:(tb__ "0|0|
S36S38S33S33A2A1S1OF_;F_;").
Variable PreC : sstate.
Variable tvC : list (sv * sv).
Definition pdesc : Type := ltac2:(tb__ "0|0|
S38S2S36S38S0S0A2A1A2").
Variable PD : list pdesc.
Definition PostsC (FBc : list (Z * Z)) : list (sstate * jpost) := ltac2:(tb__ "0|2|
S8bS38S2S36S38S0S0A2A1M0A2M1S38S2Sa2A2G1S3bS2Sa2S3cS2G0R1A3SfaVKc;VP0c;VFBc;A1VFBc;S3fS2G0R1A3A4A4Ld;VPD;A4").

Variable NPc : positive.
Hypothesis HnextPre : ltac2:(tb__ "0|0|
S2bS34S3VPreC;A1VNPc;A3").

Ltac clear_secC := try clear HnextPre; try clear NPc; try clear PD; try clear tvC; try clear PreC; try clear P0c; try clear FB; try clear P0f; try clear rho0; try clear Kc; try clear NP.

Definition tnzb (rho : valuation) (t : sv * sv) : bool := ltac2:(tb__ "0|0|
S46S94S9eQ40S8Vrho;S3cS0S0Vt;A3A2A2Z0A2A1").
Definition FBx (rho : valuation) (kept : list (sv * sv)) : list (Z * Z) := ltac2:(tb__ "0|2|
S40S38S33S33A2M0VFB;S8bS38S0S0A2M1G0Se6Vrho;A1S7cG1S123Vrho;A1Vkept;A3A4A3").

Lemma tnzb_true : ltac2:(tb__ "0|0|
S1S38S0S0A2S30S2bS37S123R2R1A2S39A3Se9R2R1A2A2Ft;Frho;").
Proof using . clear_secC. intros rho t. unfold tnzb, tnz. rewrite Bool.negb_true_iff, Z.eqb_neq. tauto. Qed.

Lemma In_FBx : ltac2:(tb__ "0|2|
S1S36S38S0S0A2M0A1S38S33S33A2M1S30S77G1R1S11cR3R2A2A3S2eS77G1R1VFB;A3S2dG0G0S2cS77G0R1R3A3S2cSe9R4R1A2S2bG1Se6R4R1A2R2A3A2A2Lt;A2A2A2Fbn;Fkept;Frho;").
Proof using .
  intros rho kept bn. unfold FBx. rewrite in_app_iff, in_map_iff. split.
  - intros [H|(t & Ht & Hin)]; [left; exact H|right]. apply filter_In in Hin as [Hin Hb]. exists t. rewrite <- tnzb_true. auto.
  - intros [H|(t & Hin & Hnz & Ht)]; [left; exact H|right]. exists t. split; [exact Ht|]. apply filter_In. rewrite tnzb_true. auto.
Qed.

Definition robjs_okF (rho : valuation) (kept : list (sv * sv)) (R : list sobj) : Prop := ltac2:(tb__ "0|1|
S4S33S77S4R2VR;A3S2cS8eS3cS33S33SeVrho;R3A2M0A3R2A2S8dR2S3fS33S33G0A3A2A2Sf0Vrho0;S11cVrho;Vkept;A2R3A3F_;F_;Fa;Fo;").

Lemma T0_callee : ltac2:(tb__ "0|1|
S2S84S36S4A1M0S36S2A1S1G0Se1Sa0VNP;Vrho0;R3A3S2bS37SedVNP;R8VPreC;R7R6R5A6S39A3S2bS33SeaS85S86R5R4R3A3R8A2A1SeaVrho0;A1A3F_;F_;Fms;FRb;Frho;Fposts;FR;Fs;FCl;").
Proof using .
  clear_secC. intros Cl s R posts rho Rb ms [Hw _] H. unfold call_checkT in H. apply andb_prop in H as [_ H].
  apply andb_prop in H as [Ee Hn]. apply sv_eqb_sound in Ee. apply Pos.ltb_lt in Hn.
  unfold T0. cbn [rw rho_sub]. rewrite Ee, eval_absorb. cbn [eval]. rewrite <- (Hw V_TOP Hn). reflexivity.
Qed.

Lemma pclF_reT : ltac2:(tb__ "0|0|
S1S1S36S38S33S33A2A1S33S2bS33SeaR3A1SeaR4A1A3Sf0R5R3R2A3Sf0R5R4R3A3F_;F_;Fa;FF;Fr2;Fr1;").
Proof using . clear_secC. intros r1 r2 F a ET [H|H]; [left; rewrite ET; exact H | right; exact H]. Qed.

Lemma robjs_checkF_sound : ltac2:(tb__ "0|1|
S1S36S5A1S36S38S0S0A2A1S4S37F_;S36S4A1S8cS5S7R5A1R4A3Se2R6SeaVrho0;A1A2SecR7R5A2S2bS37Sf1R7R6S45S41A1R5R4A5S39A3S4S33S77S4R2R7A3S2bS37R9R3A1S39A3S2cS8eS3cS33S33SeRdR4A2M0A3R3A2S8dR3S3fS33S33G0A3A2A2Sf0Vrho0;S11cReRcA2R4A3F_;F_;F_;Fa;Fo;S11eRaR8R6A3F_;F_;F_;F_;F_;FR;Fextra;Fkept;Ffacts;Frho;").
Proof using .
  clear_secC. intros rho facts kept extra R HF HT HZ Hchk Hextra o a Ho Hr.
  unfold robjs_check in Hchk. pose proof (proj1 (forallb_forall _ _) Hchk o Ho) as Hc. cbn beta in Hc.
  apply lazy_orb_prop in Hc as [Hc|Hc]; [left; exact (robj_stack_sound facts rho _ o a HF HT Hc Hr)|].
  apply lazy_orb_prop in Hc as [Hc|Hc]; [|exact (Hextra o a Ho Hc Hr)].
  destruct (robj_tracked_sound kept None o Hc) as (j & t & Hj & _ & Hb & Hl & Hh).
  destruct (tracked_range rho o t a Hb Hl Hh Hr) as [Ha Hpos].
  pose proof (nth_error_In _ _ Hj) as Hin.
  assert (Hnz : tnz rho t).
  { intros Hz. pose proof (proj1 (Forall_forall _ _) HZ t Hin (fun H => H Hz)). lia. }
  right; right. exists (fst (tvv rho t)), (snd (tvv rho t)). split; [|exact Ha].
  apply (proj2 (In_FBx rho kept _)). right. exists t. rewrite <- surjective_pairing. auto.
Qed.

Definition import_tv (isub : wsub) (tvL : list (sv * sv)) : list (sv * sv) := ltac2:(tb__ "0|1|
S8bS38S0S0A2M0G0G0S3bS0S0S89Visub;S3cS0S0R1A3A2S89Visub;S3fS0S0R1A3A2A4Lt;VtvL;A4").
Definition ivar_ok (s : wsub) (nc : positive) (L : sstate) (v : positive) : bool := ltac2:(tb__ "0|0|
S42S47S47S46SdeVv;VNPc;A2A1SafVs;Vv;A2A2SdeVv;Vnc;A2A2SdeVv;S3VL;A1A2A2").
Definition tvL_ok (s : wsub) (nc : positive) (L : sstate) (tvL : list (sv * sv)) : bool := ltac2:(tb__ "0|2|
S79S38S0S0A2M0G0S42SacS124Vs;Vnc;VL;A3M1S3cS0S0R1A3A2SacG1S3fS0S0R1A3A2A2Lt;VtvL;A3").

Definition new_objs_tv (L : sstate) (tvL : list (sv * sv)) : bool := ltac2:(tb__ "0|1|
S79S4S4S7aS38S0S0A2M0G0S42S42SfS12R2A1S3cS0S0R1A3A2SfS13R2A1SbZ0A1A2A2SfS15R2A1S3fS0S0R1A3A2A2Lt;VtvL;A3Lo';SaeVPreC;VL;A2A3").

Lemma tvd_app_l : ltac2:(tb__ "0|2|
S1S36S38S0S0A2M0A1M1G1Se5R3S40G0R2R1A3A2Se5R4R3A2F_;Fl2;Fl1;Frho;").
Proof using .
  clear_secC.
  intros rho l1 l2. induction l1 as [|t r IH]; cbn; intros H; [exact I|]. destruct H as [H1 H2].
  split; [|exact (IH H2)]. intros t' Hin'. apply H1. apply in_or_app. left. exact Hin'.
Qed.
Lemma tvd_app_r : ltac2:(tb__ "0|2|
S1S36S38S0S0A2M0A1M1G1Se5R3S40G0R2R1A3A2Se5R4R2A2F_;Fl2;Fl1;Frho;").
Proof using . clear_secC. intros rho l1 l2. induction l1 as [|t r IH]; cbn; intros H; [exact H|]. apply IH. exact (proj2 H). Qed.
Lemma tvd_app_cross : ltac2:(tb__ "0|3|
S1S36S38S0S0A2M0A1M1G1G0G0Se5R5S40G0R4R3A3A2S77G0R3R5A3M2G2Se9R8R5A2Se9R9R5A2S2fS2bS38S33S33A2Se6RaR7A2Se6RaR6A2A3A1F_;F_;F_;F_;F_;Ft';Ft;Fl2;Fl1;Frho;").
Proof using .
  clear_secC.
  intros rho l1 l2 t t'. induction l1 as [|h r IH]; cbn; intros H Hin Hin' Hz Hz'; [destruct Hin|].
  destruct H as [H1 H2]. destruct Hin as [<-|Hin].
  - apply H1; [apply in_or_app; right; exact Hin' | exact Hz | exact Hz'].
  - exact (IH H2 Hin Hin' Hz Hz').
Qed.
Lemma tvd_app : ltac2:(tb__ "0|3|
S1S36S38S0S0A2M0A1M1G1Se5R3R2A2Se5R4R2A2G0G0S77G0R2R6A3M2G2Se9R9R4A2Se9RaR4A2S2fS2bS38S33S33A2Se6RbR6A2Se6RbR5A2A3A1F_;F_;F_;F_;Ft';Ft;Se5R6S40G0R5R4A3A2F_;F_;F_;Fl2;Fl1;Frho;").
Proof using .
  clear_secC.
  intros rho l1 l2. induction l1 as [|h r IH]; cbn; intros H1 H2 Hx; [exact H2|]. destruct H1 as [Ha Hb]. split.
  - intros t' Hin'. apply in_app_or in Hin' as [Hin'|Hin']; [apply Ha; exact Hin'|]. intros Hz Hz'. apply Hx; auto.
  - apply IH; [exact Hb | exact H2 |]. intros t t' Ht Ht'. apply Hx; auto.
Qed.

Lemma Forall2_map_eq : ltac2:(tb__ "0|3|
S1S1S36S38S0S0A2M0A1M1G1S2bS36S38S33S33A2M2A1S8bG0G2Se6R3A1R1A4S8bG0G2Se6R4A1R2A4A3S2bS41S48G0R2A2S48G0R3A2A3F_;Fl';Fl;Frho';Frho;").
Proof using . clear_secC. intros rho rho' l l' H. apply (f_equal (@length _)) in H. rewrite !length_map in H. exact H. Qed.

Lemma map_nth2 : ltac2:(tb__ "0|5|
S1S1S36S38S0S0A2M0A1M1G1S41G0G0S2bS36S38S33S33A2M2A1S8bG0G2Se6R6A1R4A4S8bG0G2Se6R7A1R5A4A3S2bS3aG0A1M3S78G0R6R4A3S3dG0R3A2M4A3S2bG3S78G0R6R5A3G4A3S2bG2Se6R9R4A2Se6RaR5A2A3F_;F_;F_;Ft';Ft;Fk;Fl';Fl;Frho';Frho;").
Proof using .
  clear_secC. intros rho rho' l. induction l as [|a r IH]; intros [|b r'] [|k] t t' H Ha Hb; cbn in *; try discriminate.
  - congruence.
  - eapply IH; eauto. congruence.
Qed.

Section CallTC.
Variable TR : assn -> assn -> Prop.
Hypothesis TR_facts : ltac2:(tb__ "0|1|
S4aS2S1S99S8cS5S7R2A1S6R3A1A3VTR;S49Vsegs;R5R4R3A4R2A2M0F_;G0F_;FQ;Frho;FS;FJ;").
Hypothesis TR_ex : forall (A : Type) (J : A -> jpred) S rho (Q : assn),
  (forall x, TR (SPJ segs (J x) S rho) Q) -> TR (SPJ segs (fun r t m => exists x, J x r t m) S rho) Q.
Hypothesis TR_pre : ltac2:(tb__ "0|0|
S99S99S99S9aR3R1A1R5R2A1F_;Fw;VTR;R4R2A2VTR;R4R3A2F_;F_;FQ;FP';FP;").
Hypothesis TR_callP : ltac2:(tb__ "0|3|
S4aS4aS2S2S84S36S4A1M0S36S38S2Sa2A2M1A1S99S1S2bS3aG0A1ScdR7R6R5A3S3dG0R4A2A3S2bS37Sa7R8R7R6R5S8bG1S2S3cS2Sa2A2R4A4A5S39A3S1VTR;S49Vsegs;RbR9R1A4Sa4Vsegs;S3R9A1R1R6A4A2Frho1;S36S52A1M2Se1S51ScVsegs;R7RdS3bG2SfeR3SffR2R1A2A4A4R10R8R4R2A3R10S85S86R9RcR4A3RdA2R5R3A3F_;F_;Fmd;Fms;Ftr;S2Sa2G2Se1S51S1G2Se1S51S77G1S3bS2Sa2R9R8A4R10A3ScVsegs;RfR15S3bG2SfeR8SffR7R6A2A4A4R18R10R9R7A3Sa0S3R16A1S85S86R11R14R9A3R15A2R7A3ScVsegs;R8RdS3bG2SfeR7SffR6R5A2A4A4RdS85S86R13R16RbA3R17A2R9R8R6A4S2cSabR14RcR17R18R19RfRaA7S1SaaR15RdR18R19R1aR1bR10R1RbA9VTR;S49Vsegs;Sa9R10S85S86R16R19ReA3R1aA2RcA3Sa5R1aS3R1bA1R11S3R1cA1R19A5R2A4R17A2F_;Frho';A2F_;F_;F_;F_;F_;F_;Fmd';Fms';Ftr';FrhoL;Fmd;Fms;Ftr;FJL;FL;VTR;S49Vsegs;ReRcR6A4R7A2F_;F_;F_;F_;F_;Frho;FQ;FPosts;FR;Fs;FPre;FC;FJp;FJ;").

Hypothesis SUMT : ltac2:(tb__ "0|0|
S36S38S33S33A2A1S1VTR;S49Vsegs;Sf3VKc;VP0c;R2A1R2VtvC;A4VPreC;R1A4Sa4Vsegs;VNPc;R1S11fR2A1A4A2Frho1;FFBc;").

Theorem client_callT : ltac2:(tb__ "0|7|
S2S84S36S4A1M0S1S36S38S0S0A2M1A1M2G2S99S2bS3aG0A1ScdR7VPreC;R6A3S3dG0R5A2A3S2bS37SedVNP;R8VPreC;R7R6S8bS38S2G2A2M3S2S3cS2G2A2VPD;A4A6S39A3S2bS37Sa8R8VNPc;A2S39A3S2bS37SddVNP;S3RaA1A2S39A3S2bS37Sf5S3RbA1S40G1R7R6A3A2S39A3S2bS37Sf6RbR7VtvC;A3S39A3S2bS37S79G3G3S42S122RdS3ReA1S3cS2G2R1A3M4S3fS2G2R1A3M5A4S121G4G5A2A2Ld;VPD;A3S39A3S7dSe1S8cS5S7RdA1S6R10A1A3VP0f;Vrho0;A1Sa0VNP;Vrho0;RfA3SeeVFB;R5A2Sf2VFB;R6R11S40G1R10RfA3A4Se5R12S40G1R11R10A3A2SecR13S40G1R12R11A3A2S2dS1S1S2dS51S51Sb0Vsegs;VC;RbR2R1A5Lmd;A2LrhoM;A2Se2R15ScfS7eRaA1A1A2S2cS11eR16R15R17A3VP0c;S11cR16R15A2S85S86R16R17RaA3R18A2A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;Fms;FAi;S11dS1S77S11dR2VPD;A3Sa0S3R12A1RfR2A3VTR;S49Vsegs;Se7VNP;VKc;Vrho0;VP0f;VFB;S40G1RfS120Sa3R12VNPc;S3cS2G2R4A3M6S3R13A1A4S3fS2G2R4A3A2A3A6Sf4VNPc;R13R12R11G6A5R3A4RdA2F_;F_;Frho';Fd;VTR;S49Vsegs;Se7VNP;VKc;Vrho0;VP0f;VFB;S40G1RcRbA3A6R10RdA4RaA2F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Fpassed;Fkept;Frho;FR;Fs;FCl;").
Proof using HnextPre ML SUMT TR_callP TR_ex TR_facts TR_pre.
  intros Cl s R rho kept passed Q He Hchk Hdom Hnf Hnb Hpass Hpd HIN Tcont.
  apply Pos.leb_le in Hnf.
  apply TR_facts. intros HF.
  apply (TR_ex MA (JGi NP Kc rho0 P0f FB (kept ++ passed))). intros Ai.

  assert (PASS : forall ms, map (tvv (rho_sub (rho_absorb rho R ms) s)) tvC = map (tvv rho) passed
                 /\ forall k t t', nth_error passed k = Some t -> nth_error tvC k = Some t' -> (tnz (rho_sub (rho_absorb rho R ms) s) t' <-> tnz rho t)).
  { intros ms. destruct (tv_sub_eqb_sound s passed tvC (rho_absorb rho R ms) Hpass) as [M1 M2].
    assert (EA : forall l, map (tvv (rho_absorb rho R ms)) l = map (tvv rho) l).
    { intros l. apply map_ext. intros t. unfold tvv. rewrite !eval_absorb. reflexivity. }
    split; [rewrite M1; apply EA|]. intros k t t' Ht Ht'. rewrite (M2 k t t' Ht Ht'). unfold tnz. rewrite eval_absorb. tauto. }
  eapply (TR_callP (JGi NP Kc rho0 P0f FB (kept ++ passed) Ai) (JG_pre Kc (P0c (FBx rho kept)) (FBx rho kept) tvC) Cl PreC s R
            (PostsC (FBx rho kept)) Q rho He).
  - unfold PostsC. rewrite map_map. exact (call_checkT_P _ _ _ _ _ _ Hchk).
  - intros rho1. rewrite HnextPre. apply SUMT.
  -
    intros tr ms md Hsm (Hav & Hk & HM & HP & (HN & HD & HZ) & HK & HP0).
    destruct (HIN Ai ms HF HP0 Hav HP HN HD HZ (ex_intro _ rho (ex_intro _ md (MI1 _ _ _ _ HM))) (T_of_chk _ _ _ _ _ _ _ _ _ Hav (proj2 (proj2 HM)) Hchk)) as [HRok HPc]. destruct (PASS ms) as [PM PZ].
    assert (FBX : fbin (FBx rho kept) Ai).
    { intros bn Hbn. apply In_FBx in Hbn as [Hbn|(t & Ht & Hnz & <-)]; [exact (HP _ Hbn)|].
      destruct (proj1 (Forall_forall _ _) HN t ltac:(apply in_or_app; left; exact Ht) Hnz) as (_ & X & _). exact X. }
    split; [exact Hk|]. exists Ai. split; [|split; [exact FBX | split; [split; [|split]|split; [intros a _ _; reflexivity| exact HPc]]]].
    + split; [| split; [exact (proj1 (proj2 HM)) | split; [exact (tp_of_TPI _ _ _ _ _ _ _ _ _ _ _ Hav (proj2 (proj2 HM)) Hchk)
                                                          | rewrite (T0_callee _ _ _ _ _ _ _ Hav Hchk); exact (TPI_top _ _ (proj2 (proj2 HM)))]]].
      eapply MI1. eapply (MInvR_mem _ ML); [exact HM| |reflexivity].
      intros a Ha Ho. apply rm_absorb_out. eapply (R_miss ML Ai None rho rho md R a (MI1 _ _ _ _ HM)); [|exact Ha|exact Ho].
      intros o b Ho' Hr'. apply (pclF_caddr _ (FBx rho kept) Ai b FBX (proj2 (proj2 HM))). exact (HRok o b Ho' Hr').
    +
      unfold tvin. apply Forall_forall. intros tc Htc Hnz.
      destruct (In_nth_error _ _ Htc) as [k Hk'].
      assert (exists tp, nth_error passed k = Some tp) as [tp Htp].
      { pose proof (Forall2_map_eq _ _ _ _ PM) as L. destruct (nth_error passed k) eqn:En; [eexists; reflexivity|].
        exfalso. apply nth_error_None in En. assert (k < length tvC)%nat by (apply nth_error_Some; congruence). lia. }
      rewrite (map_nth2 _ _ _ _ k tp tc PM Htp Hk'). apply (proj1 (PZ k tp tc Htp Hk')) in Hnz.
      pose proof (nth_error_In _ _ Htp) as HinP.
      destruct (proj1 (Forall_forall _ _) HN tp ltac:(apply in_or_app; right; exact HinP) Hnz) as (X0 & X1 & X2).
      split; [exact X0|]. split; [exact X1|]. intros Hin. apply In_FBx in Hin as [Hin|(t & Ht & Hnzt & Heq)]; [exact (X2 Hin)|].
      exact (tvd_app_cross rho kept passed t tp HD Ht HinP Hnzt Hnz Heq).
    + eapply tvd_map; [exact PM | exact PZ | exact (tvd_app_r rho kept passed HD)].
    + eapply tvz_map; [exact PM | exact PZ |]. unfold tvz in HZ |- *. apply Forall_forall. intros t Ht. apply (proj1 (Forall_forall _ _) HZ). apply in_or_app. right. exact Ht.
  -
    intros L JL tr ms md rhoL tr' ms' md' HinL Hsm HJ Hag1 HsmL HJL.
    destruct HJ as (Hav & Hk & HM & HP & (HN & HD & HZ) & HK & HP0).
    unfold PostsC in HinL. apply in_map_iff in HinL as ([Ld tvL] & Heq & Hd). cbn [fst snd] in Heq. injection Heq as HL HJLe. subst L JL.
    destruct (HIN Ai ms HF HP0 Hav HP HN HD HZ (ex_intro _ rho (ex_intro _ md (MI1 _ _ _ _ HM))) (T_of_chk _ _ _ _ _ _ _ _ _ Hav (proj2 (proj2 HM)) Hchk)) as [HRok HPc].
    pose proof (proj1 (forallb_forall _ _) Hpd _ Hd) as Hpdd. cbn [fst snd] in Hpdd. apply andb_prop in Hpdd as [HtvL Hnew].
    destruct HJL as (HkL & A' & HM' & HP' & (HNc & HDc & HZc) & HKc & HP0c).
    assert (HsubA' : forall bn, In bn (FBx rho kept) -> In bn (ma_blocks A')) by exact HP'.
    split.
    + split.
      *   intros a Hina. rewrite <- (Z_to_bv_bv_unsigned 64 a).
        apply HKc; [apply bv_urange |]. destruct Hina as (o & Ho & Hr). exact (pclF_reT _ _ _ _ (T0_callee _ _ _ _ _ _ _ Hav Hchk) (HRok o _ Ho Hr)).
      *
        intros o' oR Hin' HinR.
        unfold new_objs_tv in Hnew. pose proof (proj1 (forallb_forall _ _) Hnew o' Hin') as Ho'.
        apply existsb_exists in Ho' as ([vd vsz] & Hvn & Heqs). cbn [fst snd] in Heqs.
        apply andb_prop in Heqs as [Heqs E3]. apply andb_prop in Heqs as [E1 E2].
        apply sv_eqb_sound in E1. apply sv_eqb_sound in E2. apply sv_eqb_sound in E3.
        destruct (obj_range rho oR) as [lo hi] eqn:HR2.
        destruct o' as [ob olo ohi oc od]. cbn [ob_base ob_lo ob_hi] in E1, E2, E3. subst ob olo ohi.
        unfold obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi].
        rewrite soff_lit_small by lia. unfold soff. rewrite bv_signed_U.
        set (p := bv_unsigned (eval rhoL vd)). set (n' := bv_unsigned (eval rhoL vsz)).
        apply ranges_disjoint_by_points. intros a Ha1 Ha2.
        assert (Ha : p <= a < p + n') by (destruct (Zsigned_spec n') as [[_ X]|[_ X]]; rewrite X in Ha1; lia).
        assert (Hnz : tnz rhoL (vd, vsz)).
        { intros Hz. pose proof (proj1 (Forall_forall _ _) HZc _ Hvn (fun H => H Hz)) as Z0. unfold tvv in Z0. cbn [fst snd] in Z0. fold n' in Z0. lia. }
        destruct (proj1 (Forall_forall _ _) HNc _ Hvn Hnz) as (Npos & HinN & HninF). unfold tvv in HinN, HninF. cbn [fst snd] in HinN, HninF. fold p n' in HinN. fold p n' in HninF.
        pose proof (MI1 _ _ _ _ HM') as HMr. unfold MInvR in HMr.
        pose proof (minv_block_geom C A' _ _ _ p n' HMr HinN) as (G0 & _ & G2 & G3 & G4).
        unfold PGSZ, UNIT, IB in G2, G3. pose proof (topL_range (ma_L A')) as TR3.
        pose proof (TPI_top _ _ (proj2 (proj2 HM'))) as TK. rewrite (T0_callee _ _ _ _ _ _ _ Hav Hchk) in TK.
        assert (Hc : pclF rho0 (FBx rho kept) a) by (apply (HRok oR a HinR); rewrite HR2; exact Ha2).
        destruct Hc as [Hc|[Hc|(b & m & Hb & Hr)]].
        -- destruct (block_addr_props A' _ _ _ p n' a ML HMr HinN Ha) as [X _]. lia.
        -- destruct Hc as (Hw & _). apply (ml_wseg ML) in Hw.
           rewrite Z_to_bv_unsigned, bv_wrap_small in Hw by (rewrite two64; lia).
           destruct (block_addr_props A' _ _ _ p n' a ML HMr HinN Ha) as [_ X]. exact (X Hw).
        -- pose proof (HsubA' _ Hb) as HbA'.
           assert (Hne : (b, m) <> (p, n')) by (intros Heq; apply HninF; rewrite <- Heq; exact Hb).
           destruct (pairwise_in2 _ _ _ _ (minv_blocks_pairwise C A' _ _ _ HMr) HbA' HinN) as [X|[X|X]];
             [exact (Hne X) | |]; unfold MallocInv.ranges_disjoint in X; cbn [fst snd] in X; lia.
    + intros rho' Hlink.
      assert (Hag' : agree_vals (ss_next Cl) rho rho') by (destruct Hlink as (A & _); exact A).
      assert (Hag''0 : agree_vals (ss_next Cl) rho (rho_patch rho' (patchf rho rho' R))) by (eapply agree_vals_trans; [exact Hag' | apply agree_vals_patch]).
      eapply TR_pre; [ | apply (Tcont (Ld, tvL) (rho_patch rho' (patchf rho rho' R)) Hd Hag''0)].
      intros w [Hsm' HJ']. cbn [J_ofP fst snd] in HJ' |- *.
      destruct HJ' as (Hk2 & A2 & HM2 & HP2 & (HN2 & HD2 & HZ2) & HK2 & _).
      set (rho'' := rho_patch rho' (patchf rho rho' R)).
      assert (Hag'' : agree_vals (ss_next Cl) rho rho'') by (exact Hag''0).
      assert (Hnbk : tv_below (ss_next Cl) kept = true).
      { unfold tv_below in *. rewrite forallb_app in Hnb. apply andb_prop in Hnb as [A _]. exact A. }

      set (isub := import_sub s NPc Ld (ss_next Cl)).
      destruct Hlink as (L1 & L2 & L3 & L4). rewrite HnextPre in L4.
      assert (EI : forall e, sv_vars_all (ivar_ok s (ss_next Cl) Ld) e = true -> eval rho'' (sv_subst isub e) = eval rhoL e).
      { intros e Hev. subst rho''. rewrite eval_patch, eval_subst. symmetry.
        apply (eval_agree_vars (ivar_ok s (ss_next Cl) Ld) rhoL (rho_sub rho' isub) e); [| |exact Hev].
        - intros u Hu. unfold ivar_ok in Hu. apply andb_prop in Hu as [Hu1 Hu2]. apply Pos.ltb_lt in Hu2.
          cbn [rho_sub rw]. apply L4; [exact Hu1 | lia].
        - intros l. cbn [rho_sub rl]. rewrite <- (proj2 L3 l). cbn [rho_sub rho_absorb rl]. exact (proj2 L1 l). }
      assert (IM : map (tvv rho'') (import_tv isub tvL) = map (tvv rhoL) tvL
                   /\ forall k t t', nth_error tvL k = Some t -> nth_error (import_tv isub tvL) k = Some t' -> (tnz rho'' t' <-> tnz rhoL t)).
      { unfold tvL_ok in HtvL. clear - HtvL EI. induction tvL as [|t r IH]; [split; [reflexivity | intros [|k] ? ? H; discriminate]|].
        cbn in HtvL. apply andb_prop in HtvL as [Ht Hr]. apply andb_prop in Ht as [Ht1 Ht2]. destruct (IH Hr) as [IH1 IH2].
        split.
        - cbn [map import_tv]. f_equal; [|exact IH1]. unfold tvv. cbn [fst snd]. rewrite (EI _ Ht1), (EI _ Ht2). reflexivity.
        - intros [|k] a b Ha Hb; cbn in Ha, Hb; [|exact (IH2 k a b Ha Hb)].
          injection Ha as <-. injection Hb as <-. unfold tnz. cbn [fst]. rewrite (EI _ Ht1). tauto. }
      destruct IM as [IM1 IM2].
      split; [exact (cont_smatchN NPc Cl PreC _ s R rho rho' tr ms md w He Hsm HnextPre Hag' Hsm')|].
      exists A2. split; [|split; [exact Hk2|split; [|split; [|split; [split; [|split]|split; [|exact HP0]]]]]].
      * eapply agree_vals_trans; [exact Hav|]. eapply agree_vals_trans; [eapply agree_vals_le; [exact Hnf| exact Hag']| apply agree_vals_patch].
      * assert (HT2 : TPI rho0 A2).
        { split; [exact (TPI_tp _ _ (proj2 (proj2 HM))) | rewrite <- (T0_callee _ _ R _ _ R ms Hav Hchk); exact (TPI_top _ _ (proj2 (proj2 HM2)))]. }
        eapply (MInvR_mem _ ML); [exact (conj (proj1 HM2) (conj (proj1 (proj2 HM2)) HT2))| |reflexivity]. intros a Ha Ho. subst rho''. cbn [rho_patch rm]. unfold patchf.
        destruct (in_ranges_dec rho R (Z_to_bv 64 a)) as [Hi|Hn'].
        -- exfalso. eapply (R_miss ML A2 None rho rhoL _ R a); [exact (proj1 HM2) | | exact Ha | exact Ho | exact Hi].
           intros o b Ho' Hr'. apply (pclF_caddr _ (FBx rho kept) A2 b HP2 HT2). exact (HRok o b Ho' Hr').
        -- apply L2.
      * intros bn Hbn. apply HP2. apply In_FBx. left. exact Hbn.
      *
        unfold tvin. apply Forall_app. split.
        -- apply Forall_forall. intros t Ht Hnz.
           pose proof (proj1 (forallb_forall _ _) Hnbk t Ht) as Hbt.
           rewrite (tvv_agree (ss_next Cl) rho rho'' t Hag'' Hbt) in *. apply (proj1 (tnz_agree (ss_next Cl) rho rho'' t Hag'' Hbt)) in Hnz.
           destruct (proj1 (Forall_forall _ _) HN t ltac:(apply in_or_app; left; exact Ht) Hnz) as (X0 & X1 & X2).
           split; [exact X0|]. split; [|exact X2]. apply HP2. apply In_FBx. right. exists t. auto.
        -- eapply tvin_map; [exact IM1 | exact IM2 |].
           unfold tvin in HN2 |- *. apply Forall_forall. intros t Ht Hnz. destruct (proj1 (Forall_forall _ _) HN2 t Ht Hnz) as (X0 & X1 & X2).
           split; [exact X0|]. split; [exact X1|]. intros Hin. apply X2. apply In_FBx. left. exact Hin.
      *
        apply tvd_app.
        -- apply (tvd_agree (ss_next Cl) rho rho'' kept Hag'' Hnbk). exact (tvd_app_l rho kept passed HD).
        -- eapply tvd_map; [exact IM1 | exact IM2 | exact HD2].
        -- intros t t' Ht Ht' Hnz Hnz' Heq.
           pose proof (proj1 (forallb_forall _ _) Hnbk t Ht) as Hbt.
           rewrite (tvv_agree (ss_next Cl) rho rho'' t Hag'' Hbt) in Heq. apply (proj1 (tnz_agree (ss_next Cl) rho rho'' t Hag'' Hbt)) in Hnz.
           destruct (In_nth_error _ _ Ht') as [k Hk'].
           assert (exists t0, nth_error tvL k = Some t0) as [t0 Ht0].
           { pose proof (Forall2_map_eq _ _ _ _ IM1) as L. destruct (nth_error tvL k) eqn:En; [eexists; reflexivity|].
             exfalso. apply nth_error_None in En. assert (k < length (import_tv isub tvL))%nat by (apply nth_error_Some; congruence). lia. }
           rewrite (map_nth2 _ _ _ _ k t0 t' IM1 Ht0 Hk') in Heq. apply (proj1 (IM2 k t0 t' Ht0 Hk')) in Hnz'.
           destruct (proj1 (Forall_forall _ _) HN2 t0 (nth_error_In _ _ Ht0) Hnz') as (_ & _ & X2).
           apply X2. apply In_FBx. right. exists t. auto.
      *
        unfold tvz. apply Forall_app. split.
        -- apply (tvz_agree (ss_next Cl) rho rho'' kept Hag'' Hnbk). unfold tvz in HZ |- *. apply Forall_forall. intros t Ht. apply (proj1 (Forall_forall _ _) HZ). apply in_or_app. left. exact Ht.
        -- eapply tvz_map; [exact IM1 | exact IM2 | exact HZ2].
      *
        intros a Ha Hp. subst rho''. cbn [rho_patch rm]. unfold patchf.
        destruct (in_ranges_dec rho R (Z_to_bv 64 a)) as [Hi|Hn']; [apply HK; assumption|].
        rewrite L2. transitivity (rm (rho_sub (rho_absorb rho R ms) s) (Z_to_bv 64 a)).
        -- apply HK2; [exact Ha|]. destruct Hp as [H|[H|(b & m & Hb & Hr)]]; [left; rewrite (T0_callee _ _ R _ _ R ms Hav Hchk); exact H | right; left; exact H | right; right].
           exists b, m. split; [apply In_FBx; left; exact Hb | exact Hr].
        -- rewrite rm_absorb_out by exact Hn'. apply HK; assumption.
Qed.
End CallTC.

Hypothesis SUM : ltac2:(tb__ "0|0|
S9aOF_;S36S38S33S33A2A1S1Sb5Vsegs;R3VKc;A3S9bVsegs;R4S49Vsegs;Sf3VKc;VP0c;R3A1R3VtvC;A4VPreC;R2A4Sa4Vsegs;VNPc;R2S11fR3A1A4A4F_;Frho1;FFBc;Fok;").

Hypothesis SUMX : ltac2:(tb__ "0|0|
S36S38S33S33A2A1S1Sb6VKc;A1S9cVsegs;S49Vsegs;Sf3VKc;VP0c;R3A1R3VtvC;A4VPreC;R2A4Sa4Vsegs;VNPc;R2S11fR3A1A4A3F_;Frho1;FFBc;").

Theorem client_callJ : ltac2:(tb__ "0|7|
S9aOF_;S2S84S36S4A1M0S1S36S38S0S0A2M1A1M2G2S99Sb5Vsegs;R8VKc;A3S2bS3aG0A1ScdR8VPreC;R7A3S3dG0R6A2A3S2bS37SedVNP;R9VPreC;R8R7S8bS38S2G2A2M3S2S3cS2G2A2VPD;A4A6S39A3S2bS37Sa8R9VNPc;A2S39A3S2bS37SddVNP;S3RbA1A2S39A3S2bS37Sf5S3RcA1S40G1R8R7A3A2S39A3S2bS37Sf6RcR8VtvC;A3S39A3S2bS37S79G3G3S42S122ReS3RfA1S3cS2G2R1A3M4S3fS2G2R1A3M5A4S121G4G5A2A2Ld;VPD;A3S39A3S7dSe1S8cS5S7ReA1S6R11A1A3VP0f;Vrho0;A1Sa0VNP;Vrho0;R10A3SeeVFB;R5A2Sf2VFB;R6R12S40G1R11R10A3A4Se5R13S40G1R12R11A3A2SecR14S40G1R13R12A3A2S2dS1S1S2dS51S51Sb0Vsegs;VC;RbR2R1A5Lmd;A2LrhoM;A2Se2R16ScfS7eRaA1A1A2S2cS11eR17R16R18A3VP0c;S11cR17R16A2S85S86R17R18RaA3R19A2A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;Fms;FAi;S11dS1S77S11dR2VPD;A3Sa0S3R13A1R10R2A3S9bVsegs;R15S49Vsegs;Se7VNP;VKc;Vrho0;VP0f;VFB;S40G1R10S120Sa3R13VNPc;S3cS2G2R4A3M6S3R14A1A4S3fS2G2R4A3A2A3A6Sf4VNPc;R14R13R12G6A5R3A4ReA4F_;F_;Frho';Fd;S9bVsegs;R12S49Vsegs;Se7VNP;VKc;Vrho0;VP0f;VFB;S40G1RdRcA3A6R11ReA4RbA4F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Fpassed;Fkept;Frho;FR;Fs;FCl;Fok;").
Proof using HnextPre ML SUM.
  intros ok Cl s R rho kept passed Q Hok.
  apply (client_callT (triple segs ok) (triple_factsJ segs ok) (triple_SPJ_ex segs ok)
           (fun P P' Q' HP H => @triple_conseq segs ok P P' Q' Q' HP (fun w Hw => Hw) H) (call_soundP segs ok)).
  intros FBc rho1. apply SUM. exact Hok.
Qed.

Theorem client_callJ_ex : ltac2:(tb__ "0|7|
S2S84S36S4A1M0S1S36S38S0S0A2M1A1M2G2S99Sb6VKc;A1S2bS3aG0A1ScdR8VPreC;R7A3S3dG0R6A2A3S2bS37SedVNP;R9VPreC;R8R7S8bS38S2G2A2M3S2S3cS2G2A2VPD;A4A6S39A3S2bS37Sa8R9VNPc;A2S39A3S2bS37SddVNP;S3RbA1A2S39A3S2bS37Sf5S3RcA1S40G1R8R7A3A2S39A3S2bS37Sf6RcR8VtvC;A3S39A3S2bS37S79G3G3S42S122ReS3RfA1S3cS2G2R1A3M4S3fS2G2R1A3M5A4S121G4G5A2A2Ld;VPD;A3S39A3S7dSe1S8cS5S7ReA1S6R11A1A3VP0f;Vrho0;A1Sa0VNP;Vrho0;R10A3SeeVFB;R5A2Sf2VFB;R6R12S40G1R11R10A3A4Se5R13S40G1R12R11A3A2SecR14S40G1R13R12A3A2S2dS1S1S2dS51S51Sb0Vsegs;VC;RbR2R1A5Lmd;A2LrhoM;A2Se2R16ScfS7eRaA1A1A2S2cS11eR17R16R18A3VP0c;S11cR17R16A2S85S86R17R18RaA3R19A2A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;Fms;FAi;S11dS1S77S11dR2VPD;A3Sa0S3R13A1R10R2A3S9cVsegs;S49Vsegs;Se7VNP;VKc;Vrho0;VP0f;VFB;S40G1R10S120Sa3R13VNPc;S3cS2G2R4A3M6S3R14A1A4S3fS2G2R4A3A2A3A6Sf4VNPc;R14R13R12G6A5R3A4ReA3F_;F_;Frho';Fd;S9cVsegs;S49Vsegs;Se7VNP;VKc;Vrho0;VP0f;VFB;S40G1RdRcA3A6R11ReA4RbA3F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Fpassed;Fkept;Frho;FR;Fs;FCl;").
Proof using HnextPre ML SUMX.
  intros Cl s R rho kept passed Q Hvi.
  apply (client_callT (etriple segs) (etriple_factsJ segs) (etriple_SPJ_ex segs)
           (fun P P' Q' HP H => @etriple_conseq segs P P' Q' Q' HP (fun w Hw => Hw) H) (call_completeP segs)).
  intros FBc rho1. apply SUMX. exact Hvi.
Qed.
End Client.
End WithSegs.
