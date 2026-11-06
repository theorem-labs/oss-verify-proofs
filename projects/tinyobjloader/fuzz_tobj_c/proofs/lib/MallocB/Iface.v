(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "list"; "nil"; "prod"; "app"; "pair"; "None"; "false"; "nat"; "bool"; "Some"; "option"; "fst"; "length"; "snd"; "@Corelib.Init.Logic"; "and"; "eq"; "ex"; "or"; "not"; "True"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sobj"; "sprop"; "SVar"; "SLit"; "valuation"; "SPUle"; "rw"; "FcsrFrm0"; "mkSS"; "cell"; "mkObj"; "rm"; "DUnknown"; "SAlu"; "SPBranch"; "eval"; "mkCell"; "SPNot"; "DImage"; "DZero"; "SPAlign"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"; "bv_signed"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "pre_fregs"; "pre_regs"; "cut_regs"; "setregs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_geom"; "aa_frames"; "aa_live"; "aa_Kf"; "aa_Km"; "aa_V"; "ageom"; "cls_keptA"; "topG"; "budget_ok_alloc"; "budget_ok_free"; "aa_fs_busy"; "ag_fsb"; "ag_tp"; "cls_kept_freeA"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "with_vm_backing"; "VmState"; "m_fd"; "m_fsys"; "m_io"; "m_lim"; "m_proc"; "m_time"; "m_vmmaps"; "mkModelOf"; "mkVmState"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "word_byte"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface.WithSegs"; "ustop"; "A_globals"; "mkA"; "stack_win"; "ulink"; "pre_facts"; "unwind_factsS"; "unwind_objs"; "UStopLe"; "NPOSTM"; "V_RES"; "Wcan"; "malloc_depth"; "pub_facts"; "free_depth"; "memx_depth"; "stack_malloc_depth"; "unwind_stopJ"; "V_DEPTH"; "ae_free"; "calloc_shape"; "free_shape"; "malloc_shape"; "wcanon"; "F_res_facts"; "RTC_LO"; "V_TOP"; "ae_calloc"; "ae_malloc"; "ae_ret_calloc"; "ae_ret_free"; "ae_ret_malloc"; "ae_stack_free"; "ae_stack_malloc"; "block_obj"; "chain_facts"; "last_link"; "AE"; "F_depth"; "F_sp_aligned"; "F_sp_high"; "GOT_HI"; "GOT_LO"; "NMAXW"; "O_got"; "O_rtc"; "RTC_HI"; "UStopLeOrPc"; "ae_ret_stack_free"; "ae_ret_stack_malloc"; "calloc_shapes"; "chain_pre"; "free_shapes"; "malloc_shapes"; "unwind_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface.WithSegs.Contracts"; "KcA"; "Kc_ok"; "tp_ok"; "mem_keptA"; "band_free"; "top_high"; "top_var"; "calloc_size"; "JL_pure"; "J_alloc_pre"; "J_pure_pre"; "L_memcpy"; "V_FL"; "V_FREE_A1"; "frame_flag"; "J_stack_free_pre"; "J_stack_malloc_pre"; "client_addrA"; "flag_obj"; "flagbyte_obj"; "frame_obj"; "JL_free"; "JL_free_null"; "JL_stack_free"; "JL_stack_malloc"; "J_free_null_pre"; "J_free_pre"; "J_memcpy_pre"; "J_memset_pre"; "J_pure_preT"; "L_free"; "L_free_null"; "L_memset"; "L_stack_free"; "L_stack_malloc"; "Posts_calloc"; "Posts_malloc"; "Pre_calloc"; "Pre_free"; "Pre_free_null"; "Pre_malloc"; "Pre_memcpy"; "Pre_memset"; "Pre_stack_free"; "Pre_stack_malloc"; "V_FLAG"; "client_shadowA"; "memcpy_facts"; "memset_facts"; "n_frames"; "with_vm"; "JL_calloc_null"; "JL_calloc_ok"; "JL_malloc_null"; "JL_malloc_ok"; "L_calloc_null"; "L_calloc_ok"; "L_malloc_null"; "L_malloc_ok";
"client_mut_addrA"; "errno_addrA"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "pow"; "lt"; "sub"; "eqb"; "mul"; "opp"; "to_nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "ok_frameA"; "liftKA"; "jpredA"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_EQ"; "BC_GE"; "BC_GEU"; "@Stdlib.Lists.List"; "In"; "nth_error"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "etriple"; "triple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "fs_frame_size"; "Sh"; "IMG_HI"; "SHADOW_BAND_HI"; "SHADOW_BAND_LO"; "SHADOW_OFF"; "fs_class_of_size"; "fs_flag_addr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "ERRNO_A"; "@Corelib.Init.Peano"; "le"; "lt"; "@Corelib.Lists.ListDef"; "nth"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundR SymSummary ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA SummaryA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section WithSegs.
Variable segs : list Segment.

Record aentry := AE {
  ae_malloc : Z; ae_calloc : Z; ae_free : Z;
  ae_ret_malloc : Z; ae_ret_calloc : Z; ae_ret_free : Z;
  ae_stack_malloc : Z -> Z; ae_ret_stack_malloc : Z -> Z;
  ae_stack_free : Z -> Z; ae_ret_stack_free : Z -> Z;
  ae_asan_memset : Z; ae_ret_asan_memset : Z;
  ae_asan_memcpy : Z; ae_ret_asan_memcpy : Z;
  ae_memset_icpt : Z; ae_memcpy_icpt : Z;
  ae_ret_musl_memset : Z; ae_ret_musl_memcpy : Z; ae_ret_musl_memcpy2 : Z;
  ae_set_shadow : Z -> Z
}.

Definition AE_A : aentry := ltac2:(tb__ "0|a|
S7cZ5e1f4Z5e1f8Z5e1f0Z5e52cZ5e768Z5e3d0S2bS2bS2bLc;M0R1Z47a9cS2cS2cS2bLp;M1R1S2cS2cS2bLp0;M2R1S2cN1M3Lp1;M4S2cS2cS2bLp1;M5R1S2cG3Lp2;M6G6Z480e8X2cx3Lp1;Z47f3cX2cx3Lp0;S2cG2R1S2cG5R1G6G6Z483a8X2cx3Lp1;G4Z47da0X2cx3Lp0;Z47c10X2cx3Lp;S2cG3Lp;M7X2bx3Lc;S2bG0R1Z47bf0S2cG1R1S2cG2R1G4S2cG5R1G6G6Z482d4X2cx3Lp1;Z480c8X2cx3Lp0;S2cG2R1S2cG5R1G6G6Z48524X2cx3Lp1;G4Z47f1cX2cx3Lp0;Z47d80X2cx3Lp;G7X2bx3Lc;S2bG0R1G3S2cG1R1S2cG2R1G4S2cG5R1G6G6Z482f4X2cx3Lp1;G3X2cx3Lp0;S2cG2R1S2cG5R1G6G6Z48544X2cx3Lp1;G4G3X2cx3Lp0;G3X2cx3Lp;G7X2bx3Lc;S2bG0R1G3S2cG1R1S2cG2R1G4S2cG5R1G6G6Z483a4X2cx3Lp1;G3X2cx3Lp0;S2cG2R1S2cG5R1G6G6Z48588X2cx3Lp1;G4G3X2cx3Lp0;G3X2cx3Lp;G7X2bx3Lc;Z5ce7cZ5cf3cZ5c9e0Z5cb08Z5c9d4Z5c9dcZ5d184Z5d99cM8G8S2bS9S2bL_;M9Sd0R1Z0A2Z6041cG9Sd0R1Zf5A2Z60524G9Sd0R1Zf8A2Z6053cG3X9x2X9x2X9x2Lv;A14").

Definition V_RES : positive := 110%positive.
Definition NPOSTM : positive := 140%positive.
Definition V_DEPTH : positive := 15%positive.
Definition stack_win : sobj := ltac2:(tb__ "0|0|
S20S18PaA1S18S69A1S19Z0A1S2S1fA1S22A5").
Definition F_depth (depth : Z) : list sprop := ltac2:(tb__ "0|1|
S0S17S24SdaS19Sd2Vdepth;A1A1S18S69A1M0A3S0S17S24SdaG0S19Sd2ScdZ2Z28A2A1A1A3S2S17A1A3A3").
Definition F_sp_aligned : sprop := SPAlign 10%positive 4.

Definition F_sp_high : sprop := ltac2:(tb__ "0|0|
S1bS19Z7fff7f800000A1S23Sd8S18PaA1S18S69A1A3A2").
Definition V_TOP : positive := 30%positive.
Definition F_top : list sprop := ltac2:(tb__ "0|1|
S0S17S1bS18S71A1M0S23Sd8S18PaA1S18S69A1A3A2S0S17S1bS19Z7fff7f800000A1G0A2S0S17S1bG0S19Z7fffff800000A1A2S2S17A1A3A3A3").

Definition ulink : Type := (sv * sv)%type.

Inductive ustop := UStopLe | UStopLeOrPc.

Fixpoint link_objs (bp : sv) (W : list ulink) : list sobj :=
  match W with
  | [] => []
  | (nbp, pc) :: W' => mkObj bp (SLit (-16)) (SLit 0) [mkCell (SLit (-16)) 8 nbp; mkCell (SLit (-8)) 8 pc] DUnknown :: link_objs nbp W'
  end.

Fixpoint last_link (bp : sv) (W : list ulink) : sv * sv * sv   :=
  match W with
  | [] => (bp, bp, SLit 0)
  | [(nbp, pc)] => (bp, nbp, pc)
  | (nbp, pc) :: W' => last_link nbp W'
  end.

Definition link_var (i : nat) : positive := ltac2:(tb__ "0|1|
SeeS2cVi;S0S2cP34S0S2cP35S0S2cP36S0S2cP37S0S2cP38S0S2cP39S0S2cP3aS0S2cP3bS0S2cP5cS0S2cP5dS0S2cP5eS0S2cP5fS0S2cP60S0S2cP61S0S2cP62S0S2cP63M0S2S2cA1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G0A4").
Fixpoint Wcan_from (k i : nat) : list ulink :=
  match k with O => [] | S k' => (SVar (link_var i), SVar (link_var (S i))) :: Wcan_from k' (S (S i)) end.
Definition Wcan (n : nat) : list ulink := Wcan_from n 0.
Definition NMAXW : nat := 2%nat.

Definition wcanon (W : list ulink) : Prop := ltac2:(tb__ "0|0|
S11S8S8SfSecR1S82A2S10S1S5bA1VW;S62R1A1A3A2Ln;A2").
Definition unwind_objs (W : list ulink) : list sobj := link_objs (SVar 28) W.

Definition malloc_shapes : list (list ulink * ustop) := ltac2:(tb__ "0|2|
S0S3S1S5bA1M0S57A2M1S5G0S57S62U0A1S5fA4S0G1S5G0S57S62U2A1S5fA4S2G1A1A3A3").
Definition calloc_shapes : list (list ulink * ustop) := ltac2:(tb__ "0|2|
S0S3S1S5bA1M0S57A2M1S5G0S57S62U0A1S5fA4S0G1S5G0S57S62U1A1S86A4S2G1A1A3A3").
Definition free_shapes : list (list ulink * ustop) := ltac2:(tb__ "0|2|
S0S3S1S5bA1M0S57A2M1S5G0S57S62U0A1S5fA4S0G1S5G0S57S62U1A1S5fA4S0G1S5G0S57S62U2A1S5fA4S2G1A1A3A3A3").
Definition malloc_shape (W : list ulink) (st : ustop) : Prop := ltac2:(tb__ "0|1|
SdcS3S1S5bA1M0S57A2S5G0S57VW;Vst;A4S8cA3").
Definition calloc_shape (W : list ulink) (st : ustop) : Prop := ltac2:(tb__ "0|1|
SdcS3S1S5bA1M0S57A2S5G0S57VW;Vst;A4S89A3").
Definition free_shape (W : list ulink) (st : ustop) : Prop := ltac2:(tb__ "0|1|
SdcS3S1S5bA1M0S57A2S5G0S57VW;Vst;A4S8bA3").
Lemma malloc_shape_wcanon : ltac2:(tb__ "0|0|
S1S5bA1S57S6dR2R1A2S6eR3A1F_;Fst;FW;").
Proof. intros W st [H|[H|[]]]; injection H as <- _; [exists 0%nat | exists 2%nat]; split; [unfold NMAXW; lia | reflexivity | unfold NMAXW; lia | reflexivity]. Qed.
Lemma calloc_shape_wcanon : ltac2:(tb__ "0|0|
S1S5bA1S57S6bR2R1A2S6eR3A1F_;Fst;FW;").
Proof. intros W st [H|[H|[]]]; injection H as <- _; [exists 0%nat | exists 1%nat]; split; [unfold NMAXW; lia | reflexivity | unfold NMAXW; lia | reflexivity]. Qed.
Lemma free_shape_wcanon : ltac2:(tb__ "0|0|
S1S5bA1S57S6cR2R1A2S6eR3A1F_;Fst;FW;").
Proof. intros W st [H|[H|[H|[]]]]; injection H as <- _; [exists 0%nat | exists 1%nat | exists 2%nat]; (split; [unfold NMAXW; lia | reflexivity]). Qed.
Lemma malloc_shape_nil : malloc_shape [] UStopLe. Proof. left. reflexivity. Qed.
Lemma calloc_shape_nil : calloc_shape [] UStopLe. Proof. left. reflexivity. Qed.
Lemma free_shape_nil : free_shape [] UStopLe. Proof. left. reflexivity. Qed.

Fixpoint chain_facts (bp : sv) (W : list ulink) : list sprop :=
  match W with
  | [] => []
  | [_] => []
  | (nbp, pc) :: W' => SPUle (SAlu ALU_ADD bp (SLit 16)) nbp :: SPUle nbp (SLit (2 ^ 47)) :: chain_facts nbp W'
  end.
Definition unwind_facts (W : list ulink) (st : ustop) : list sprop := ltac2:(tb__ "0|7|
S1S5bA1M0S1S17A1M1LW;VW;S0S17S1bS18P1cA1M2S18PaA1M3A2S2S17A1M4A3S5bG0S4S17S4S17S0S17S1bG3S19ScdZ2Z2fA2A1M5A2S0S17S1bS23Sd8G3S19Z10A1A3G2A2S0S17S1bG2G5A2G4A3A3A3S7aG2VW;A2A3S3S3S15S15A2M6S15A2G1Lx;S7bG2VW;A2G6S15G6G1Lp;R2S15S15S57G1Lst;Vst;S0S17S1bR1R2A2G4A3S0S17S27S24SdbR3S19Z1000A1A3A1G4A3X57x2Lnbp;Lbp;X3x1Lpc;Lp;X3x1A3Ll;Lu;X1x2").

Definition unwind_stopJ (W : list ulink) (st : ustop) (rho : valuation) : Prop := ltac2:(tb__ "0|3|
S1S5bA1M0OLW;VW;S14S5bG0S57OLst;Vst;S14S3S3S15S15A2M1S15A2OLx;S7bS18P1cA1VW;A2G1S15G1OLp;R2S15S15S12SceS2eQ40M2S25Vrho;R3A2A2Z1000A2SccS2eG2S25Vrho;R1A2A2S2eG2S25Vrho;R2A2A2A2A2Lnbp;Lbp;X3x1Lpc;Lp;X3x1X57x2Ll;Lu;X1x2").
Definition chain_pre (W : list ulink) : list sprop := ltac2:(tb__ "0|5|
S1S5bA1M0S1S17A1LW;VW;S2S17A1M1S5bG0S4S17S0S17S1bS18PaA1M2S19ScdZ2Z2fA2A1M3A2S0S17S1bS23Sd8G2S19Z10A1A3S18P1cA1M4A2S0S17S1bG4G3A2G1A3A3A3S7aG4VW;A2A3Ll;Lu;X1x2").
Definition unwind_factsS (W : list ulink) (st : ustop) : list sprop := ltac2:(tb__ "0|3|
S57S1S17A1M0Lst;Vst;S8dVW;S5fA2M1S1S5bA1M2G0LW;VW;G1S5bG2S8aVW;A1Ll;Lu;X1x2X57x2").

Definition GOT_LO : Z := 0xe4868.
Definition GOT_HI : Z := 0xe5608.
Definition O_got : sobj := ltac2:(tb__ "0|0|
S20S19Z0A1S19S81A1S19S80A1S2S1fA1S28A5").
Definition RTC_LO : Z := 0xee0b8.
Definition RTC_HI : Z := 0xee0c4.
Definition O_rtc : sobj := ltac2:(tb__ "0|2|
S20S19Z0A1S19S70A1M0S19S85A1S0S1fS26G0Z8M1S19Se6A1A3S0S1fS26S19ScbS70G1A2A1Z4S19Z1A1A3S2S1fA1A3A3S28A5").
Definition A_globals : list sobj := ltac2:(tb__ "0|0|
S0S16S83S0S16S84S2S16A1A3A3").

Definition malloc_depth : Z := 4096.
Definition free_depth : Z := 4096.
Definition stack_malloc_depth : Z := 256.
Definition memx_depth : Z := 2304.

Definition pre_facts (depth : Z) : list sprop := ltac2:(tb__ "0|0|
S4S17S0S17S7eS0S17S7fS2S17A1A3A3S7dVdepth;A1A3").

Definition pub_facts (depth : Z) : list sprop := pre_facts depth ++ F_top.

Definition block_obj (size : sv) (d : odefault) : sobj := ltac2:(tb__ "0|0|
S20S18S61A1S19Z0A1Vsize;S2S1fA1Vd;A5").
Definition F_res_facts (size : sv) : list sprop := ltac2:(tb__ "0|1|
S0S17S2aS61Z4A2S0S17S27S24Sd9S18S61A1M0S19Z0A1A3A1S0S17S1bS19Z1000A1G0A2S0S17S1bS23Sd8G0Vsize;A3S19Z7fffff800000A1A2S2S17A1A3A3A3A3").

Definition base_sv : sv := SLit SHADOW_OFF.
Definition mkA (S : sstate) (X : list (sv * sv)) : axst := mkAX S X base_sv.

Section Contracts.
Variable E : aentry.

Variable AInvA : ltac2:(tb__ "0|0|
S36S1aS1S2dQ40A1A1S46OF_;F_;F_;F_;").

Variables CST XGL : list (Z * Z).

Definition tp_ok (A : AA) (rho : valuation) : Prop := ltac2:(tb__ "0|0|
S10S2bS2eQ40S1cVrho;P18A2A2S44S37VA;A1A1A3").

Definition top_var (A : AA) (rho : valuation) : Prop := ltac2:(tb__ "0|0|
S10S2bS2eQ40S1cVrho;S71A2A2S3fS37VA;A1A1A3").
Definition top_high (A : AA) (rho : valuation) : Prop := ltac2:(tb__ "0|1|
SccS3fS37VA;A1A1ScbS2eQ40M0S1cVrho;PaA2A2S30G0S1cVrho;S69A2A2A2A2").

Definition KcA : Type := ltac2:(tb__ "0|0|
S1S47A1S46OF_;F_;").
Definition with_vm (v : VmState) (m : Model) : Model := ltac2:(tb__ "0|0|
S51S4aVm;A1Vv;S4cVm;A1S4bVm;A1S4eVm;A1S4dVm;A1S4fVm;A1A7").
Definition Kc_ok (Kc : KcA) : Prop := ltac2:(tb__ "0|0|
S1S47A1S46S49VKc;R3R2A2VKc;R4Sc0R2R3A2A2F_;Fv;Fmd;Ftr;").
Lemma with_vm_backing_with_vm : ltac2:(tb__ "0|1|
S1S3S2dQ40A1M0G0A2A1S1G0A1S46S10S46S48R3R2R1A3Sc0S52S50R1A1R3R2A3R1A2A3Fm;Fp;Fl;").
Proof. reflexivity. Qed.
Lemma Kc_ok_mat : ltac2:(tb__ "0|3|
S8eS1S47A1S46S1S3S2dQ40A1M0G0A2A1M1S1G0A1M2G1G2S8fR7A1R8R7S48R5R4R6A3A2R9R8S48R4R3R7A3A2F_;F_;Fp';Fl';Fp;Fl;Fmd;Ftr;FKc;").
Proof.
  intros Kc tr md l p l' p' HK H.
  replace (with_vm_backing l' p' md) with (with_vm (mkVmState (m_vmmaps md) l' p') (with_vm_backing l p md)) by (destruct md; reflexivity).
  apply HK. exact H.
Qed.

Lemma ok_frameA_liftKA : ltac2:(tb__ "0|0|
SdeOF_;S8eSd7Sd5Vsegs;R3Sd6R2A1A3S1aS1S2dQ40A1A1S1S47A1S46R6R4R3R2R1A4R8R3R2A2F_;Fmd;Ftr;Ftp;Frho;Sd5Vsegs;R5R3A3F_;F_;FJ;FKc;Fok;").
Proof. intros ok Kc J H HJ rho tp tr ms md msv' Hj. apply (H rho tp tr ms md msv'). exact (HJ _ _ _ _ Hj). Qed.

Definition Pre_malloc (W : list ulink) (st : ustop) : axst := ltac2:(tb__ "0|0|
S59S1eS73VE;A1S33S32S1dS6S15A1S0S16S5aS4S16S5eVW;A1S58A3A3S4S17S5dVW;Vst;A2S64S63A1A3S31S7A9S2S3S15S15A2A1A2").

Definition Pre_mallocI (W : list ulink) (st : ustop) : axst := ltac2:(tb__ "0|0|
S59S1eS73VE;A1S33S32S1dS6S15A1S0S16S5aS4S16S5eVW;A1S58A3A3S4S17S5dVW;Vst;A2S5cS63A1A3S31S7A9S2S3S15S15A2A1A2").

Definition L_malloc_null (W : list ulink) (st : ustop) : axst := ltac2:(tb__ "0|1|
S59S1eS76VE;A1S35S34S31A1S0S3S8S15A2M0S5S8S15UaS19Z0A1A4S2G0A1A3A2S32S1dS6S15A1S0S16S5aS4S16S5eVW;A1S58A3A3S4S17S5dVW;Vst;A2S5cS63A1A3S60S7A9S2S3S15S15A2A1A2").

Definition L_malloc_ok (W : list ulink) (st : ustop) : axst := ltac2:(tb__ "0|2|
S59S1eS76VE;A1S34S31A1S32S1dS6S15A1S0S16S5aS4S16S5eVW;A1S4S16S0S16S79S18PcA1M0S22A2S2S16A1A3S58A3A3A3S4S17S6fG0A1S4S17S5dVW;Vst;A2S5cS63A1A3A3S60S7A9S0S3S15S15A2M1S5S15S15S18S61A1G0A4S2G1A1A3A2").

Definition J_alloc_pre (W : list ulink) (st : ustop) (A : AA) (Kc : KcA) (n : sv) : jpredA := ltac2:(tb__ "0|2|
S1aS1S2dQ40M0A1A1S1S47A1S46SfVAInvA;VA;R4R3R1A4SfVKc;R2R1A2SfS90VA;R4A2SfS68VW;Vst;R4A3SfS40VA;S2eG0S25R4Vn;A2A2M1A2SfSfSccZ1G1A2SceG1ScdZ2Z27A2A2A2S94VA;R4A2A2A2A2A2A2A2Lmd;Ltr;Ltp;Lrho;").

Definition J_alloc_preT (W : list ulink) (st : ustop) (A : AA) (Kc : KcA) (n : sv) : jpredA := ltac2:(tb__ "0|2|
S1aS1S2dQ40M0A1A1S1S47A1S46SfVAInvA;VA;R4R3R1A4SfVKc;R2R1A2SfS90VA;R4A2SfS68VW;Vst;R4A3SfS40VA;S2eG0S25R4Vn;A2A2M1A2SfSfSccZ1G1A2SceG1ScdZ2Z27A2A2A2S93VA;R4A2A2A2A2A2A2A2Lmd;Ltr;Ltp;Lrho;").

Definition frame_flag (G : ageom) (fs : Z * Z) : Z := ltac2:(tb__ "0|0|
Se8S43VG;A1Se7SeS2bS2bVfs;A3A1ScS2bS2bVfs;A3A3").

Definition client_mut_addrA (A : AA) (a : Z) : Prop := ltac2:(tb__ "0|0|
S12SfSccS3fS37VA;A1A1Va;A2SceVa;ScdZ2Z2fA2A2A2S12SeaS39VA;A1Va;A2S12S11S2bS2bS11S2bS2bSfSdcS3S2bS2bA2S5S2bS2bR2R1A4S38VA;A1A3SfSccR2Va;A2SceVa;ScbR2R1A2A2A2A2Ls;A2Lf;A2SeaVCST;Va;A2A2A2A2").

Definition client_addrA (A : AA) (a : Z) : Prop := ltac2:(tb__ "0|1|
S12Sc9VA;Va;A2S11S3S2bS2bA2M0G0SfSdcG0R1S38VA;A1A3S10S2bVa;S9cS37VA;A1R1A2A3A2Lfs;A2A2").

Definition client_shadowA (A : AA) (a : Z) : Prop := ltac2:(tb__ "0|1|
S12S11S2bS2bSfS9fVA;R1A2S10S2bVa;Se2R1A1A3M0A2Lx;A2S11S2bS2bSfSeaVXGL;R1A2G0A2Lx;A2A2").

Definition errno_addrA (a : Z) : Prop := ltac2:(tb__ "0|0|
SfSccSebVa;A2SceVa;ScbSebZ4A2A2A2").
Definition mem_keptA (A A' : AA) (m0 m1 : word -> option byte) : Prop := ltac2:(tb__ "0|8|
SfS2bSfSccZ0M0R1A2SceR1ScdZ2Z40A2A2A2S12SfS9fVA;R2A2M1SfS9fVA';R2A2M2S13ScaR2A1A1A2A2SfSbcVA;R2A2SfSbcVA';R2A2S13S10SbS2dQ8A1M3A1M4Vm0;S2fQ40M5R2A2A1S6G3A1M6A3A1A2A2A2S10G4Vm1;S2fG5R3A2M7A1Vm0;G7A1A3F_;F_;Fa;S2bS2bS12SfG1G2A2SeaVXGL;R2A2A2SfSccG0R2A2SceR2Z8A2A2S13S10G4Vm0;S54Se2R4A1R3A2A1G6A3A1S13S10G4Vm1;S54Se2R5A1R4A2A1G6A3A1F_;F_;F_;Fj;Fx;A2").

Definition JL_malloc_null (A : AA) (Kc : KcA) : jpostA := ltac2:(tb__ "0|4|
S1aS1S2dQ40M0A1A1M1S1aG1S1S47A1S46S11S36S36SfVAInvA;R1R5R4R2A4SfS10S1S3S2bS2bA2A1M2S39R1A1S39VA;A1A3SfS10G2S38R1A1S38VA;A1A3SfS10S2bS3cR1A1ScbS3cVA;A1S2eG0S1cR7PcA2A2M3A2A3SfS10S2bS3bR1A1ScbS3bVA;A1Z1A2A3SfS10S2bS3aR1A1S3aVA;A1A3SfS10S3dS37R1A1S37VA;A1A3SfS91VA;R1S21R7A1S21R5A1A4SfVKc;R3R2A2S3eVA;R1G3A3A2A2A2A2A2A2A2A2A2LA';A2Lmd;Ltr;Ltp';Lrho';Ltp0;Lrho0;").

Definition JL_malloc_ok (A : AA) (Kc : KcA) : jpostA := ltac2:(tb__ "0|5|
S1aS1S2dQ40M0A1A1M1S1aG1S1S47A1S46S11S36S36S11S1S3S2bS2bA2M2A1M3G3S11G3G3SfVAInvA;R3R7R6R4A4SfS10G3S39R3A1S4G2R2S0G2S5S2bS2bS2eG0S1cR7S61A2A2S2eG0S1cR9PcA2A2M4A4R1A3A3A3SfS10G3S39VA;A1S4G2R2R1A3A3SfS10G3S38R3A1S38VA;A1A3SfS10S2bS3cR3A1ScbS3cVA;A1G4A2A3SfS10S2bS3bR3A1ScbS3bVA;A1Z1A2A3SfS10S2bS3aR3A1S3aVA;A1A3SfS10S3dS37R3A1S37VA;A1A3SfS91VA;R3S21R9A1S21R7A1A4SfVKc;R5R4A2S3eVA;R3G4A3A2A2A2A2A2A2A2A2A2A2Ll2;A2Ll1;A2LA';A2Lmd;Ltr;Ltp';Lrho';Ltp0;Lrho0;").

Definition Posts_malloc (W : list ulink) (st : ustop) (A : AA) Kc : list (axst * jpostA) := ltac2:(tb__ "0|1|
S0S3S53S55A2M0S5S53S55Sc7VW;Vst;A2Sc3VA;VKc;A2A4S0G0S5S53S55Sc8VW;Vst;A2Sc4VA;VKc;A2A4S2G0A1A3A3").

Definition malloc_contractA : Prop := ltac2:(tb__ "0|0|
S1S5bA1S57SdeOF_;S36S8eS1aS1S2dQ40A1A1S6dR7R6A2S8fR4A1Sd5Vsegs;R7Sd6R5A1A3Se9Vsegs;R8Sd6R6A1A3Se0Vsegs;R9Sd4Vsegs;S97RbRaR8R7S18PcA1A5Sb6RbRaA2R6R5A5S56Vsegs;S31R6R5Sb2RbRaR8R7A4A5A4F_;F_;F_;F_;Ftp;Frho;FKc;FA;Fok;Fst;FW;").

Definition malloc_contractA_ex : Prop := ltac2:(tb__ "0|0|
S1S5bA1S57S36S8eS1aS1S2dQ40A1A1S6dR6R5A2S8fR4A1SdfVsegs;Sd4Vsegs;S97R8R7R6R5S18PcA1A5Sb6R8R7A2R4R3A5S56Vsegs;S31R4R3Sb2R8R7R6R5A4A5A3F_;F_;Ftp;Frho;FKc;FA;Fst;FW;").

Definition calloc_size : sv := SMd M_MUL (SVar 12) (SVar 13).
Definition Pre_calloc (W : list ulink) (st : ustop) : axst := ltac2:(tb__ "0|0|
S59S1eS72VE;A1S33S32S1dS6S15A1S0S16S5aS4S16S5eVW;A1S58A3A3S4S17S5dVW;Vst;A2S64S63A1A3S31S7A9S2S3S15S15A2A1A2").
Definition Pre_callocI (W : list ulink) (st : ustop) : axst := ltac2:(tb__ "0|0|
S59S1eS72VE;A1S33S32S1dS6S15A1S0S16S5aS4S16S5eVW;A1S58A3A3S4S17S5dVW;Vst;A2S5cS63A1A3S31S7A9S2S3S15S15A2A1A2").
Definition L_calloc_null (W : list ulink) (st : ustop) : axst := ltac2:(tb__ "0|1|
S59S1eS74VE;A1S35S34S31A1S0S3S8S15A2M0S5S8S15UaS19Z0A1A4S2G0A1A3A2S32S1dS6S15A1S0S16S5aS4S16S5eVW;A1S58A3A3S4S17S5dVW;Vst;A2S5cS63A1A3S60S7A9S2S3S15S15A2A1A2").
Definition L_calloc_ok (W : list ulink) (st : ustop) : axst := ltac2:(tb__ "0|1|
S59S1eS74VE;A1S34S31A1S32S1dS6S15A1S0S16S5aS4S16S5eVW;A1S4S16S0S16S79S95S29A2S2S16A1A3S58A3A3A3S4S17S6fS95A1S4S17S5dVW;Vst;A2S5cS63A1A3A3S60S7A9S0S3S15S15A2M0S5S15S15S18S61A1S95A4S2G0A1A3A2").
Definition JL_calloc_ok (A : AA) (Kc : KcA) : jpostA := ltac2:(tb__ "0|5|
S1aS1S2dQ40M0A1A1M1S1aG1S1S47A1S46S11S36S36S11S1S3S2bS2bA2M2A1M3G3S11G3G3SfVAInvA;R3R7R6R4A4SfS10G3S39R3A1S4G2R2S0G2S5S2bS2bS2eG0S1cR7S61A2A2Sd1S2eG0S1cR9PcA2A2S2eG0S1cR9PdA2A2A2M4A4R1A3A3A3SfS10G3S39VA;A1S4G2R2R1A3A3SfS10G3S38R3A1S38VA;A1A3SfS10S2bS3cR3A1ScbS3cVA;A1G4A2A3SfS10S2bS3bR3A1ScbS3bVA;A1Z1A2A3SfS10S2bS3aR3A1S3aVA;A1A3SfS10S3dS37R3A1S37VA;A1A3SfS91VA;R3S21R9A1S21R7A1A4SfVKc;R5R4A2S3eVA;R3G4A3A2A2A2A2A2A2A2A2A2A2Ll2;A2Ll1;A2LA';A2Lmd;Ltr;Ltp';Lrho';Ltp0;Lrho0;").
Definition JL_calloc_null (A : AA) (Kc : KcA) : jpostA := ltac2:(tb__ "0|4|
S1aS1S2dQ40M0A1A1M1S1aG1S1S47A1S46S11S36S36SfVAInvA;R1R5R4R2A4SfS10S1S3S2bS2bA2A1M2S39R1A1S39VA;A1A3SfS10G2S38R1A1S38VA;A1A3SfS10S2bS3cR1A1ScbS3cVA;A1Sd1S2eG0S1cR7PcA2A2S2eG0S1cR7PdA2A2A2M3A2A3SfS10S2bS3bR1A1ScbS3bVA;A1Z1A2A3SfS10S2bS3aR1A1S3aVA;A1A3SfS10S3dS37R1A1S37VA;A1A3SfS91VA;R1S21R7A1S21R5A1A4SfVKc;R3R2A2S3eVA;R1G3A3A2A2A2A2A2A2A2A2A2LA';A2Lmd;Ltr;Ltp';Lrho';Ltp0;Lrho0;").
Definition Posts_calloc (W : list ulink) (st : ustop) (A : AA) Kc : list (axst * jpostA) := ltac2:(tb__ "0|1|
S0S3S53S55A2M0S5S53S55Sc5VW;Vst;A2Sc1VA;VKc;A2A4S0G0S5S53S55Sc6VW;Vst;A2Sc2VA;VKc;A2A4S2G0A1A3A3").
Definition calloc_contractA : Prop := ltac2:(tb__ "0|0|
S1S5bA1S57SdeOF_;S36S8eS1aS1S2dQ40A1A1S6bR7R6A2S8fR4A1Sd5Vsegs;R7Sd6R5A1A3Se9Vsegs;R8Sd6R6A1A3Se0Vsegs;R9Sd4Vsegs;S97RbRaR8R7S95A5Sb3RbRaA2R6R5A5S56Vsegs;S31R6R5Sb1RbRaR8R7A4A5A4F_;F_;F_;F_;Ftp;Frho;FKc;FA;Fok;Fst;FW;").
Definition calloc_contractA_ex : Prop := ltac2:(tb__ "0|0|
S1S5bA1S57S36S8eS1aS1S2dQ40A1A1S6bR6R5A2S8fR4A1SdfVsegs;Sd4Vsegs;S97R8R7R6R5S95A5Sb3R8R7A2R4R3A5S56Vsegs;S31R4R3Sb1R8R7R6R5A4A5A3F_;F_;Ftp;Frho;FKc;FA;Fst;FW;").

Definition V_FREE_A1 : positive := 17%positive.
Definition Pre_free (W : list ulink) (st : ustop) : axst := ltac2:(tb__ "0|1|
S59S1eS6aVE;A1S35S33S0S3S8S15A2M0S5S8S15UbS18S9bA1A4S2G0A1A3A2S32S1dS6S15A1S0S16S5aS4S16S5eVW;A1S4S16S0S16S20S18PcA1S19Z0A1S18PdA1S2S1fA1S22A5S2S16A1A3S58A3A3A3S4S17S5dVW;Vst;A2S64S65A1A3S31S7A9S2S3S15S15A2A1A2").
Definition Pre_freeI (W : list ulink) (st : ustop) : axst := ltac2:(tb__ "0|1|
S59S1eS6aVE;A1S35S33S0S3S8S15A2M0S5S8S15UbS18S9bA1A4S2G0A1A3A2S32S1dS6S15A1S0S16S5aS4S16S5eVW;A1S4S16S0S16S20S18PcA1S19Z0A1S18PdA1S2S1fA1S22A5S2S16A1A3S58A3A3A3S4S17S5dVW;Vst;A2S5cS65A1A3S31S7A9S2S3S15S15A2A1A2").
Definition L_free (W : list ulink) (st : ustop) : axst := ltac2:(tb__ "0|0|
S59S1eS75VE;A1S34S31A1S32S1dS6S15A1S0S16S5aS4S16S5eVW;A1S58A3A3S4S17S5dVW;Vst;A2S5cS65A1A3S60S7A9S2S3S15S15A2A1A2").
Definition J_free_pre (W : list ulink) (st : ustop) (A : AA) (Kc : KcA) : jpredA := ltac2:(tb__ "0|1|
S1aS1S2dQ40M0A1A1S1S47A1S46SfVAInvA;VA;R4R3R1A4SfS68VW;Vst;R4A3SfSdcS3S2bS2bA2S5S2bS2bS2eG0S1cR4PcA2A2S2eG0S1cR4PdA2A2A4S39VA;A1A3SfVKc;R2R1A2SfS90VA;R4A2SfS41VA;A1S94VA;R4A2A2A2A2A2A2A2Lmd;Ltr;Ltp;Lrho;").
Definition J_free_preT (W : list ulink) (st : ustop) (A : AA) (Kc : KcA) : jpredA := ltac2:(tb__ "0|1|
S1aS1S2dQ40M0A1A1S1S47A1S46SfVAInvA;VA;R4R3R1A4SfS68VW;Vst;R4A3SfSdcS3S2bS2bA2S5S2bS2bS2eG0S1cR4PcA2A2S2eG0S1cR4PdA2A2A4S39VA;A1A3SfVKc;R2R1A2SfS90VA;R4A2SfS41VA;A1S93VA;R4A2A2A2A2A2A2A2Lmd;Ltr;Ltp;Lrho;").
Definition JL_free (A : AA) (Kc : KcA) : jpostA := ltac2:(tb__ "0|4|
S1aS1S2dQ40M0A1A1M1S1aG1S1S47A1S46S11S36S36S11S1S3S2bS2bA2M2A1M3G3S11G3G3SfVAInvA;R3R7R6R4A4SfS10G3S39VA;A1S4G2R2S0G2S5S2bS2bS2eG0S1cR9PcA2A2S2eG0S1cR9PdA2A2A4R1A3A3A3SfS10G3S39R3A1S4G2R2R1A3A3SfS10G3S38R3A1S38VA;A1A3SfS10S2bS3cR3A1S3cVA;A1A3SfS10S2bS3bR3A1S3bVA;A1A3SfS10S2bS3aR3A1ScbS3aVA;A1Z1A2A3SfS10S3dS37R3A1S37VA;A1A3SfS91VA;R3S21R9A1S21R7A1A4SfVKc;R5R4A2S45VA;R3A2A2A2A2A2A2A2A2A2A2A2Ll2;A2Ll1;A2LA';A2Lmd;Ltr;Ltp';Lrho';Ltp0;Lrho0;").
Definition free_contractA : Prop := ltac2:(tb__ "0|1|
S1S5bA1S57SdeOF_;S36S8eS1aS1S2dQ40A1A1S6cR7R6A2S8fR4A1Sd5Vsegs;R7Sd6R5A1A3Se9Vsegs;R8Sd6R6A1A3Se0Vsegs;R9Sd4Vsegs;Sa8RbRaR8R7A4Sb4RbRaA2R6R5A5S56Vsegs;S31R6R5S0S3S53S55A2M0S5S53S55SacRbRaA2Sa3R8R7A2A4S2G0A1A3A5A4F_;F_;F_;F_;Ftp;Frho;FKc;FA;Fok;Fst;FW;").
Definition free_contractA_ex : Prop := ltac2:(tb__ "0|1|
S1S5bA1S57S36S8eS1aS1S2dQ40A1A1S6cR6R5A2S8fR4A1SdfVsegs;Sd4Vsegs;Sa8R8R7R6R5A4Sb4R8R7A2R4R3A5S56Vsegs;S31R4R3S0S3S53S55A2M0S5S53S55SacR8R7A2Sa3R6R5A2A4S2G0A1A3A5A3F_;F_;Ftp;Frho;FKc;FA;Fst;FW;").

Definition Pre_free_null (W : list ulink) (st : ustop) : axst := ltac2:(tb__ "0|1|
S59S1eS6aVE;A1S35S33S0S3S8S15A2M0S5S8S15UaS19Z0A1A4S0G0S5S8S15UbS18S9bA1A4S2G0A1A3A3A2S32S1dS6S15A1S0S16S5aS4S16S5eVW;A1S58A3A3S4S17S5dVW;Vst;A2S64S65A1A3S31S7A9S2S3S15S15A2A1A2").
Definition Pre_free_nullI (W : list ulink) (st : ustop) : axst := ltac2:(tb__ "0|1|
S59S1eS6aVE;A1S35S33S0S3S8S15A2M0S5S8S15UaS19Z0A1A4S0G0S5S8S15UbS18S9bA1A4S2G0A1A3A3A2S32S1dS6S15A1S0S16S5aS4S16S5eVW;A1S58A3A3S4S17S5dVW;Vst;A2S5cS65A1A3S31S7A9S2S3S15S15A2A1A2").
Definition L_free_null (W : list ulink) (st : ustop) : axst := ltac2:(tb__ "0|0|
S59S1eS75VE;A1S34S31A1S32S1dS6S15A1S0S16S5aS4S16S5eVW;A1S58A3A3S4S17S5dVW;Vst;A2S5cS65A1A3S60S7A9S2S3S15S15A2A1A2").
Definition J_free_null_pre (W : list ulink) (st : ustop) (A : AA) (Kc : KcA) : jpredA := ltac2:(tb__ "0|0|
S1aS1S2dQ40A1A1S1S47A1S46SfVAInvA;VA;R4R3R1A4SfS68VW;Vst;R4A3SfVKc;R2R1A2SfS90VA;R4A2S94VA;R4A2A2A2A2A2Lmd;Ltr;Ltp;Lrho;").
Definition J_free_null_preT (W : list ulink) (st : ustop) (A : AA) (Kc : KcA) : jpredA := ltac2:(tb__ "0|0|
S1aS1S2dQ40A1A1S1S47A1S46SfVAInvA;VA;R4R3R1A4SfS68VW;Vst;R4A3SfVKc;R2R1A2SfS90VA;R4A2S93VA;R4A2A2A2A2A2Lmd;Ltr;Ltp;Lrho;").
Definition JL_free_null (A : AA) (Kc : KcA) : jpostA := ltac2:(tb__ "0|2|
S1aS1S2dQ40A1A1M0S1aG0S1S47A1S46S11S36S36SfVAInvA;R1R5R4R2A4SfS10S1S3S2bS2bA2A1M1S39R1A1S39VA;A1A3SfS10G1S38R1A1S38VA;A1A3SfS10S2bS3cR1A1S3cVA;A1A3SfS10S2bS3bR1A1S3bVA;A1A3SfS10S2bS3aR1A1S3aVA;A1A3SfS10S3dS37R1A1S37VA;A1A3SfS91VA;R1S21R7A1S21R5A1A4VKc;R3R2A2A2A2A2A2A2A2A2A2LA';A2Lmd;Ltr;Ltp';Lrho';Ltp0;Lrho0;").

Definition free_null_contractA : Prop := ltac2:(tb__ "0|2|
SdeOF_;S36S8eS1aS1S2dQ40A1A1S8fR3A1Sd5Vsegs;R6Sd6R4A1A3Se9Vsegs;R7Sd6R5A1A3Se0Vsegs;R8Sd4Vsegs;Sa7S2S5bA1M0S5fR7R6A4Sb5G0S5fA2R5R4A5S56Vsegs;S31R5R4S0S3S53S55A2M1S5S53S55SadG0S5fA2Sa4R7R6A2A4S2G1A1A3A5A4F_;F_;F_;Ftp;Frho;FKc;FA;Fok;").
Definition free_null_contractA_ex : Prop := ltac2:(tb__ "0|2|
S36S8eS1aS1S2dQ40A1A1S8fR3A1SdfVsegs;Sd4Vsegs;Sa7S2S5bA1M0S5fR5R4A4Sb5G0S5fA2R3R2A5S56Vsegs;S31R3R2S0S3S53S55A2M1S5S53S55SadG0S5fA2Sa4R5R4A2A4S2G1A1A3A5A3F_;Ftp;Frho;FKc;FA;").

Definition Pre_stack_malloc (c : Z) : axst := ltac2:(tb__ "0|0|
S59S1eS78VE;Vc;A2S33S32S1dS6S15A1S4S16S0S16S5aS2S16A1A3S58A3S64S67A1S31S7A9S2S3S15S15A2A1A2").
Definition Pre_stack_mallocI (c : Z) : axst := ltac2:(tb__ "0|0|
S59S1eS78VE;Vc;A2S33S32S1dS6S15A1S4S16S0S16S5aS2S16A1A3S58A3S5cS67A1S31S7A9S2S3S15S15A2A1A2").
Definition V_FLAG : positive := 120%positive.
Definition frame_obj (f : sv) (c : Z) : sobj := ltac2:(tb__ "0|0|
S20Vf;S19Z0A1S19ScfSe1Vc;A1Z8A2A1S2S1fA1S22A5").
Definition flag_obj (f : sv) (c : Z) (fl : sv) : sobj := ltac2:(tb__ "0|3|
S20Vf;S19ScfSe1Vc;A1M0Z8M1A2A1M2S19G0A1S0S1fS26G2G1Vfl;A3S2S1fA1A3S22A5").
Definition flagbyte_obj (fl : sv) (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S20Vfl;S19Z0A1S19Z1A1Vcells;S22A5").
Definition L_stack_malloc (c : Z) : axst := ltac2:(tb__ "0|9|
S59S1eS88VE;Vc;A2S34S31A1S32S1dS6S15A1S4S16S0S16S5aS0S16Sa2S18S61A1M0Vc;A2S0S16Sa0G0Vc;S18SbbA1M1A3S0S16Sa1G1S0S1fS26S19Z0A1M2Z1M3S19G3A1M4A3S2S1fA1A3A2S2S16A1A3A3A3A3S58A3S4S17S0S17S2aS61Z5A2S0S17S27S24Sd9G0G2A3A1S0S17S1bS19Se3A1M5G0A2S0S17S1bS23Sd8G0S19Se1Vc;A1A1M6A3S19Z7fffff800000A1M7A2S0S17S1bG5G1A2S0S17S1bS23Sd8G1G4A3G7A2S2S17A1A3A3A3A3A3A3S5cS67A1A3S60S7A9S0S3S15S15A2M8S5S15S15G0G6A4S2G8A1A3A2").
Definition n_frames (A : AA) (c : Z) : nat := ltac2:(tb__ "0|1|
SdS3S2bS2bA2M0SeeS1G0A1Sd3Vc;A1S42VA;A1S2G0A1A4A2").
Definition J_stack_malloc_pre (c : Z) (A : AA) (Kc : KcA) : jpredA := ltac2:(tb__ "0|1|
S1aS1S2dQ40M0A1A1S1S47A1S46SfVAInvA;VA;R4R3R1A4SfVKc;R2R1A2SfS90VA;R4A2SfSecSbfVA;Vc;A2U8A2SfSccS2eG0S1cR4PcA2A2Se1Vc;A1A2S94VA;R4A2A2A2A2A2A2Lmd;Ltr;Ltp;Lrho;").
Definition J_stack_malloc_preT (c : Z) (A : AA) (Kc : KcA) : jpredA := ltac2:(tb__ "0|1|
S1aS1S2dQ40M0A1A1S1S47A1S46SfVAInvA;VA;R4R3R1A4SfVKc;R2R1A2SfS90VA;R4A2SfSecSbfVA;Vc;A2U8A2SfSccS2eG0S1cR4PcA2A2Se1Vc;A1A2S93VA;R4A2A2A2A2A2A2Lmd;Ltr;Ltp;Lrho;").
Definition JL_stack_malloc (c : Z) (A : AA) (Kc : KcA) : jpostA := ltac2:(tb__ "0|6|
S1aS1S2dQ40M0A1A1M1S1aG1S1S47A1S46S11S36S36S11S1S3S2bS2bA2M2A1M3G3S11G3G3SfVAInvA;R3R7R6R4A4SfS10G3S39R3A1S39VA;A1A3SfS10G3S38VA;A1S4G2R2R1A3A3SfS10G3S38R3A1S4G2R2S0G2S5S2bS2bS2eG0S1cR7S61A2A2Se1Vc;A1A4M4R1A3A3A3SfS10S2bS2eG0S1cR7SbbA2A2S9cS37VA;A1M5G4A2A3SfS10S2bS3cR3A1S3cVA;A1A3SfS10S2bS3bR3A1S3bVA;A1A3SfS10S2bS3aR3A1S3aVA;A1A3SfS10S3dS37R3A1G5A3SfS91VA;R3S21R9A1S21R7A1A4SfVKc;R5R4A2S10G1R6R8A3A2A2A2A2A2A2A2A2A2A2A2Ll2;A2Ll1;A2LA';A2Lmd;Ltr;Ltp';Lrho';Ltp0;Lrho0;").
Definition stack_malloc_contractA (c : Z) : Prop := ltac2:(tb__ "0|1|
SdeOF_;S36S8eS1aS1S2dQ40A1A1S8fR3A1Sd5Vsegs;R6S9eVc;R5R4A3A3Se0Vsegs;R7Sd4Vsegs;S9eVc;R6R5A3SbaVc;A1R4R3A5S56Vsegs;S31R4R3S0S3S53S55A2M0S5S53S55Sb0Vc;A1Sa6Vc;R6R5A3A4S2G0A1A3A5A4F_;F_;Ftp;Frho;FKc;FA;Fok;").
Definition stack_malloc_contractA_ex (c : Z) : Prop := ltac2:(tb__ "0|1|
S36S8eS1aS1S2dQ40A1A1S8fR3A1SdfVsegs;Sd4Vsegs;S9eVc;R5R4A3SbaVc;A1R3R2A5S56Vsegs;S31R3R2S0S3S53S55A2M0S5S53S55Sb0Vc;A1Sa6Vc;R5R4A3A4S2G0A1A3A5A3F_;Ftp;Frho;FKc;FA;").

Definition V_FL : positive := 16%positive.
Definition Pre_stack_free (c : Z) : axst := ltac2:(tb__ "0|2|
S59S1eS77VE;Vc;A2S33S32S1dS6S15A1S4S16S0S16S5aS0S16Sa2S18PcA1M0Vc;A2S0S16Sa0G0Vc;S18S9aA1M1A3S0S16Sa1G1S2S1fA1A2S2S16A1A3A3A3A3S58A3S64S67A1S31S7A9S2S3S15S15A2A1A2").
Definition Pre_stack_freeI (c : Z) : axst := ltac2:(tb__ "0|2|
S59S1eS77VE;Vc;A2S33S32S1dS6S15A1S4S16S0S16S5aS0S16Sa2S18PcA1M0Vc;A2S0S16Sa0G0Vc;S18S9aA1M1A3S0S16Sa1G1S2S1fA1A2S2S16A1A3A3A3A3S58A3S5cS67A1S31S7A9S2S3S15S15A2A1A2").
Definition L_stack_free (c : Z) : axst := ltac2:(tb__ "0|0|
S59S1eS87VE;Vc;A2S34S31A1S32S1dS6S15A1S4S16S0S16S5aS2S16A1A3S58A3S5cS67A1S60S7A9S2S3S15S15A2A1A2").
Definition J_stack_free_pre (c : Z) (A : AA) (Kc : KcA) : jpredA := ltac2:(tb__ "0|2|
S1aS1S2dQ40M0A1A1S1S47A1S46SfVAInvA;VA;R4R3R1A4SfVKc;R2R1A2SfS90VA;R4A2SfSdcS3S2bS2bA2S5S2bS2bS2eG0S1cR4PcA2A2Se1Vc;A1A4M1S38VA;A1A3SfS10S2bS2eG0S1cR4S9aA2A2S9cS37VA;A1G1A2A3S94VA;R4A2A2A2A2A2A2Lmd;Ltr;Ltp;Lrho;").
Definition J_stack_free_preT (c : Z) (A : AA) (Kc : KcA) : jpredA := ltac2:(tb__ "0|2|
S1aS1S2dQ40M0A1A1S1S47A1S46SfVAInvA;VA;R4R3R1A4SfVKc;R2R1A2SfS90VA;R4A2SfSdcS3S2bS2bA2S5S2bS2bS2eG0S1cR4PcA2A2Se1Vc;A1A4M1S38VA;A1A3SfS10S2bS2eG0S1cR4S9aA2A2S9cS37VA;A1G1A2A3S93VA;R4A2A2A2A2A2A2Lmd;Ltr;Ltp;Lrho;").
Definition JL_stack_free (c : Z) (A : AA) (Kc : KcA) : jpostA := ltac2:(tb__ "0|4|
S1aS1S2dQ40M0A1A1M1S1aG1S1S47A1S46S11S36S36S11S1S3S2bS2bA2M2A1M3G3S11G3G3SfVAInvA;R3R7R6R4A4SfS10G3S39R3A1S39VA;A1A3SfS10G3S38VA;A1S4G2R2S0G2S5S2bS2bS2eG0S1cR9PcA2A2Se1Vc;A1A4R1A3A3A3SfS10G3S38R3A1S4G2R2R1A3A3SfS10S2bS3cR3A1S3cVA;A1A3SfS10S2bS3bR3A1S3bVA;A1A3SfS10S2bS3aR3A1S3aVA;A1A3SfS10S3dS37R3A1S37VA;A1A3SfS91VA;R3S21R9A1S21R7A1A4SfVKc;R5R4A2S10G1R6R8A3A2A2A2A2A2A2A2A2A2A2Ll2;A2Ll1;A2LA';A2Lmd;Ltr;Ltp';Lrho';Ltp0;Lrho0;").
Definition stack_free_contractA (c : Z) : Prop := ltac2:(tb__ "0|1|
SdeOF_;S36S8eS1aS1S2dQ40A1A1S8fR3A1Sd5Vsegs;R6S9dVc;R5R4A3A3Se0Vsegs;R7Sd4Vsegs;S9dVc;R6R5A3Sb9Vc;A1R4R3A5S56Vsegs;S31R4R3S0S3S53S55A2M0S5S53S55SafVc;A1Sa5Vc;R6R5A3A4S2G0A1A3A5A4F_;F_;Ftp;Frho;FKc;FA;Fok;").
Definition stack_free_contractA_ex (c : Z) : Prop := ltac2:(tb__ "0|1|
S36S8eS1aS1S2dQ40A1A1S8fR3A1SdfVsegs;Sd4Vsegs;S9dVc;R5R4A3Sb9Vc;A1R3R2A5S56Vsegs;S31R3R2S0S3S53S55A2M0S5S53S55SafVc;A1Sa5Vc;R5R4A3A4S2G0A1A3A5A3F_;Ftp;Frho;FKc;FA;").

Definition memset_facts : list sprop := ltac2:(tb__ "0|9|
S0S17S1bS18P35A1M0S18PcA1M1A2S0S17S1bS23Sd8G1S18PeA1M2A3S23Sd8G0S18P36A1M3A3M4A2S0S17S1bG2S19ScdZ2M5Z20A2A1A2S0S17S1bS19Se3A1G0A2S0S17S1bG4S19ScfScdG5Z2fA2M6Z8A2A1M7A2S0S17S1bG3S19ScdG5Z28A2A1A2S0S17S1bS19Z1A1G2A2S0S17S1bG0G7A2S0S17S1bG1S19G6A1M8A2S0S17S1bS18PaA1G8A2S2S17A1A3A3A3A3A3A3A3A3A3A3").
Definition Pre_memset (entry : Z) : axst := ltac2:(tb__ "0|3|
S59S1eVentry;S35S33S0S3S8S15A2M0S5S8S15UbS19Z0A1M1A4S2G0A1A3A2S32S1dS6S15A1S4S16S0S16S5aS0S16S20S18PcA1G1S18PeA1S2S1fA1S22A5S2S16A1A3A3S58A3S4S17SbeS64S66A1A3S31S7A9S0S3S15S15A2M2S5S15S15S18P35A1S18P36A1A4S2G2A1A3A2").
Definition Pre_memsetI (entry : Z) : axst := ltac2:(tb__ "0|3|
S59S1eVentry;S35S33S0S3S8S15A2M0S5S8S15UbS19Z0A1M1A4S2G0A1A3A2S32S1dS6S15A1S4S16S0S16S5aS0S16S20S18PcA1G1S18PeA1S2S1fA1S22A5S2S16A1A3A3S58A3S4S17SbeS5cS66A1A3S31S7A9S0S3S15S15A2M2S5S15S15S18P35A1S18P36A1A4S2G2A1A3A2").
Definition L_memset (retpc : Z) : axst := ltac2:(tb__ "0|3|
S59S1eVretpc;S35S34S31A1S0S3S8S15A2M0S5S8S15UaS18PcA1M1A4S2G0A1A3A2S32S1dS6S15A1S4S16S0S16S5aS0S16S20G1S19Z0A1S18PeA1S2S1fA1S29A5S2S16A1A3A3S58A3S5cS66A1S60S7A9S0S3S15S15A2M2S5S15S15S18P35A1S18P36A1A4S2G2A1A3A2").
Definition J_pure_pre (A : AA) (Kc : KcA) : jpredA := ltac2:(tb__ "0|0|
S1aS1S2dQ40A1A1S1S47A1S46SfVAInvA;VA;R4R3R1A4SfVKc;R2R1A2SfS90VA;R4A2S94VA;R4A2A2A2A2Lmd;Ltr;Ltp;Lrho;").
Definition J_pure_preT (A : AA) (Kc : KcA) : jpredA := ltac2:(tb__ "0|0|
S1aS1S2dQ40A1A1S1S47A1S46SfVAInvA;VA;R4R3R1A4SfVKc;R2R1A2SfS90VA;R4A2S93VA;R4A2A2A2A2Lmd;Ltr;Ltp;Lrho;").
Definition JL_pure (A : AA) (Kc : KcA) : jpostA := ltac2:(tb__ "0|1|
S1aS1S2dQ40A1A1M0S1aG0S1S47A1S46SfVAInvA;VA;R4R3R1A4SfS10G0R3R5A3SfS91VA;VA;S21R6A1S21R4A1A4VKc;R2R1A2A2A2A2Lmd;Ltr;Ltp';Lrho';Ltp0;Lrho0;").

Definition band_free (lo len : Z) : Prop := ltac2:(tb__ "0|0|
S12SccScbVlo;Vlen;A2Se5A2SccSe4Vlo;A2A2").
Definition J_memset_pre (A : AA) (Kc : KcA) : jpredA := ltac2:(tb__ "0|1|
S1aS1S2dQ40M0A1A1S1S47A1S46SfS98VA;VKc;R4R3R2R1A6S92S2eG0S1cR4P35A2A2S2eG0S1cR4P36A2A2A2A2Lmd;Ltr;Ltp;Lrho;").
Definition J_memset_preT (A : AA) (Kc : KcA) : jpredA := ltac2:(tb__ "0|1|
S1aS1S2dQ40M0A1A1S1S47A1S46SfSabVA;VKc;R4R3R2R1A6S92S2eG0S1cR4P35A2A2S2eG0S1cR4P36A2A2A2A2Lmd;Ltr;Ltp;Lrho;").
Definition J_memcpy_pre (A : AA) (Kc : KcA) : jpredA := ltac2:(tb__ "0|1|
S1aS1S2dQ40M0A1A1S1S47A1S46SfS98VA;VKc;R4R3R2R1A6SfS92S2eG0S1cR4P35A2A2S2eG0S1cR4P36A2A2A2S92S2eG0S1cR4P37A2A2S2eG0S1cR4P38A2A2A2A2A2Lmd;Ltr;Ltp;Lrho;").
Definition J_memcpy_preT (A : AA) (Kc : KcA) : jpredA := ltac2:(tb__ "0|1|
S1aS1S2dQ40M0A1A1S1S47A1S46SfSabVA;VKc;R4R3R2R1A6SfS92S2eG0S1cR4P35A2A2S2eG0S1cR4P36A2A2A2S92S2eG0S1cR4P37A2A2S2eG0S1cR4P38A2A2A2A2A2Lmd;Ltr;Ltp;Lrho;").
Definition memset_contractA (entry retpc : Z) : Prop := ltac2:(tb__ "0|1|
SdeOF_;S36S8eS1aS1S2dQ40A1A1S8fR3A1Sd5Vsegs;R6S98R5R4A2A3Se0Vsegs;R7Sd4Vsegs;SaaR6R5A2Sb8Ventry;A1R4R3A5S56Vsegs;S31R4R3S0S3S53S55A2M0S5S53S55SaeVretpc;A1S96R6R5A2A4S2G0A1A3A5A4F_;F_;Ftp;Frho;FKc;FA;Fok;").

Definition memset_contractA_ex (entry retpc : Z) : Prop := ltac2:(tb__ "0|1|
S36S8eS1aS1S2dQ40A1A1S8fR3A1SdfVsegs;Sd4Vsegs;SaaR5R4A2Sb8Ventry;A1R3R2A5S56Vsegs;S31R3R2S0S3S53S55A2M0S5S53S55SaeVretpc;A1S96R5R4A2A4S2G0A1A3A5A3F_;Ftp;Frho;FKc;FA;").

Definition memcpy_facts : list sprop := ltac2:(tb__ "0|f|
S0S17S1bS18P35A1M0S18PcA1M1A2S0S17S1bS23Sd8G1S18PeA1M2A3S23Sd8G0S18P36A1M3A3M4A2S0S17S1bS18P37A1M5S18PdA1M6A2S0S17S1bS23Sd8G6G2A3S23Sd8G5S18P38A1M7A3M8A2S0S17S1bG2S19ScdZ2M9Z20A2A1A2S0S17S1bS19Se3A1MaG0A2S0S17S1bG4S19ScfScdG9Z2fA2MbZ8A2A1McA2S0S17S1bG3S19ScdG9Z28A2A1MdA2S0S17S1bS19Z1A1G2A2S0S17S1bG0GcA2S0S17S1bG1S19GbA1MeA2S0S17S1bS18PaA1GeA2S0S17S1bGaG5A2S0S17S1bG8GcA2S0S17S1bG7GdA2S0S17S1bG5GcA2S0S17S1bG6GeA2S2S17A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition Pre_memcpy (entry : Z) : axst := ltac2:(tb__ "0|4|
S59S1eVentry;S33S32S1dS6S15A1S4S16S0S16S5aS0S16S20S18PcA1S19Z0A1M0S18PeA1M1S2S1fA1M2S22A5S0S16S20S18PdA1G0G1G2S22A5S2S16A1A3A3A3S58A3S4S17SbdS64S66A1A3S31S7A9S0S3S15S15A2M3S5S15S15S18P35A1S18P36A1A4S0G3S5S15S15S18P37A1S18P38A1A4S2G3A1A3A3A2").
Definition Pre_memcpyI (entry : Z) : axst := ltac2:(tb__ "0|4|
S59S1eVentry;S33S32S1dS6S15A1S4S16S0S16S5aS0S16S20S18PcA1S19Z0A1M0S18PeA1M1S2S1fA1M2S22A5S0S16S20S18PdA1G0G1G2S22A5S2S16A1A3A3A3S58A3S4S17SbdS5cS66A1A3S31S7A9S0S3S15S15A2M3S5S15S15S18P35A1S18P36A1A4S0G3S5S15S15S18P37A1S18P38A1A4S2G3A1A3A3A2").

Definition L_memcpy (retpc : Z) : axst := ltac2:(tb__ "0|6|
S59S1eVretpc;S35S34S31A1S0S3S8S15A2M0S5S8S15UaS18PcA1M1A4S2G0A1A3A2S32S1dS6S15A1S4S16S0S16S5aS0S16S20G1S19Z0A1M2S18PeA1M3S2S1fA1M4S22A5S0S16S20S18PdA1G2G3G4S22A5S2S16A1A3A3A3S58A3S5cS66A1S60S7A9S0S3S15S15A2M5S5S15S15S18P35A1S18P36A1A4S0G5S5S15S15S18P37A1S18P38A1A4S2G5A1A3A3A2").
Definition memcpy_contractA (entry retpc retpc2 : Z) : Prop := ltac2:(tb__ "0|2|
SdeOF_;S36S8eS1aS1S2dQ40A1A1S8fR3A1Sd5Vsegs;R6S98R5R4A2A3Se0Vsegs;R7Sd4Vsegs;Sa9R6R5A2Sb7Ventry;A1R4R3A5S56Vsegs;S31R4R3S0S3S53S55A2M0S5S53S55S99Vretpc;A1S96R6R5A2M1A4S0G0S5S53S55S99Vretpc2;A1G1A4S2G0A1A3A3A5A4F_;F_;Ftp;Frho;FKc;FA;Fok;").
Definition memcpy_contractA_ex (entry retpc retpc2 : Z) : Prop := ltac2:(tb__ "0|2|
S36S8eS1aS1S2dQ40A1A1S8fR3A1SdfVsegs;Sd4Vsegs;Sa9R5R4A2Sb7Ventry;A1R3R2A5S56Vsegs;S31R3R2S0S3S53S55A2M0S5S53S55S99Vretpc;A1S96R5R4A2M1A4S0G0S5S53S55S99Vretpc2;A1G1A4S2G0A1A3A3A5A3F_;Ftp;Frho;FKc;FA;").

Definition client_owned_shadowA (A : AA) (a : Z) : Prop := ltac2:(tb__ "0|0|
S11S2bS2bS11S2bS2bSfSdcS3S2bS2bA2S5S2bS2bR2R1A4S38VA;A1A3SfSccSe2R2A1Va;A2SccVa;Se2ScfScbR2R1A2Z1A2A1A2A2A2Ls;A2Lf;A2").
Definition pairwise_disjoint (l : list (Z * Z)) : Prop := ltac2:(tb__ "0|3|
S8S8S2bS2bS2bS2bSedR6R5A2S10SbS3S2bS2bA2M0A1M1SddG0Vl;R7A3M2SaG0S5S2bS2bR5R4A4A2A3S10G1G2SaG0S5S2bS2bR4R3A4A2A3S12SccScbR7R6A2R5A2SccScbR5R4A2R7A2A2F_;F_;F_;Fn';Fb';Fn;Fb;Fj;Fi;").
Record alloc_lawsA : Prop := ALA {

  law_frame : forall A rho rho' tp md,
      AInvA A rho tp md ->
      (forall a, ~ client_mut_addrA A (bv_unsigned a) -> ~ client_owned_shadowA A (bv_unsigned a) -> rm rho' a = rm rho a) ->
      (forall a, client_owned_shadowA A (bv_unsigned a) -> rm rho a <> None -> rm rho' a <> None) ->
      AInvA A rho' tp md;

  law_vars : forall A rho rho' tp md, AInvA A rho tp md -> rm rho' = rm rho -> AInvA A rho' tp md;

  law_mat : forall A rho tp md md', AInvA A rho tp md -> mat_equiv segs tp md md' -> AInvA A rho tp md';

  law_blocks : forall A rho tp md, AInvA A rho tp md ->
      pairwise_disjoint (aa_live A ++ aa_frames A)
      /\ (forall b n, In (b, n) (aa_live A) ->

            1 <= n /\ b mod 16 = 0 /\ 4096 <= b /\ b + n + 2048 <= topG (aa_geom A) /\ IMG_HI <= b - 4096)
      /\ (forall f s, In (f, s) (aa_frames A) ->
            f mod 64 = 0 /\ s mod 64 = 0 /\ 64 <= s /\ IMG_HI <= f /\ f + s <= topG (aa_geom A)
            /\ IMG_HI <= frame_flag (aa_geom A) (f, s) /\ frame_flag (aa_geom A) (f, s) + 1 <= topG (aa_geom A)
            /\ (forall b n, In (b, n) (aa_live A) -> b + n <= frame_flag (aa_geom A) (f, s) \/ frame_flag (aa_geom A) (f, s) + 1 <= b - 16)
            /\ (forall f' s', In (f', s') (aa_frames A) -> f' + s' <= frame_flag (aa_geom A) (f, s) \/ frame_flag (aa_geom A) (f, s) + 1 <= f'));

  law_client_app : forall A rho tp md a, AInvA A rho tp md -> client_addrA A a ->
      (topG (aa_geom A) <= a < 2 ^ 47)
      \/ (IMG_HI <= a < topG (aa_geom A) /\ (a < SHADOW_BAND_LO \/ SHADOW_BAND_HI <= a))
      \/ (0 <= a < IMG_HI);

  law_rtc : forall A rho tp md, AInvA A rho tp md -> cells_ok (view segs (rm rho)) (rtc_cells_img RTC_A (aa_geom A));

  law_budget : forall A rho tp md, AInvA A rho tp md ->
      paid md tp <= budget_bound A /\ vm_limit (m_vmmaps md) = LIMIT /\ 0 <= aa_V A /\ 0 <= aa_Km A /\ 0 <= aa_Kf A;

  law_fake_frame_release : forall A rho rho' tp md f s,
      AInvA A rho tp md -> In (f, s) (aa_frames A) ->
      (forall z, 0 <= z < 2 ^ 64 -> ~ (f <= z < f + s) -> z <> frame_flag (aa_geom A) (f, s) -> ~ (Sh f <= z < Sh (f + s)) ->
         rm rho' (Z_to_bv 64 z) = rm rho (Z_to_bv 64 z)) ->
      rm rho' (Z_to_bv 64 (frame_flag (aa_geom A) (f, s))) = Some (Z_to_bv 8 0) ->
      (forall z, f <= z < f + s -> rm rho' (Z_to_bv 64 z) <> None) ->
      (forall z, Sh f <= z < Sh (f + s) -> rm rho' (Z_to_bv 64 z) <> None) ->
      exists A' l1 l2, AInvA A' rho' tp md /\ aa_frames A = l1 ++ (f, s) :: l2 /\ aa_frames A' = l1 ++ l2 /\ aa_live A' = aa_live A
                 /\ aa_V A' = aa_V A /\ aa_Km A' = aa_Km A /\ aa_Kf A' = aa_Kf A /\ aa_geom A' = aa_geom A
}.

Record alloc_contractsA : Prop := ACA {
  aca_malloc : malloc_contractA;
  aca_calloc : calloc_contractA;
  aca_free : free_contractA;
  aca_free_null : free_null_contractA;
  aca_stack_malloc : forall c, In c [0;1;2;3;5;6] -> stack_malloc_contractA c;
  aca_stack_free : forall c, In c [5;6] -> stack_free_contractA c;
  aca_asan_memset : memset_contractA (ae_asan_memset E) (ae_ret_asan_memset E);
  aca_asan_memcpy : memcpy_contractA (ae_asan_memcpy E) (ae_ret_asan_memcpy E) (ae_ret_asan_memcpy E)

}.
Record alloc_contractsA_ex : Prop := ACAX {
  acx_malloc : malloc_contractA_ex;
  acx_calloc : calloc_contractA_ex;
  acx_free : free_contractA_ex;
  acx_free_null : free_null_contractA_ex;
  acx_stack_malloc : forall c, In c [0;1;2;3;5;6] -> stack_malloc_contractA_ex c;
  acx_stack_free : forall c, In c [5;6] -> stack_free_contractA_ex c;
  acx_asan_memset : memset_contractA_ex (ae_asan_memset E) (ae_ret_asan_memset E);
  acx_asan_memcpy : memcpy_contractA_ex (ae_asan_memcpy E) (ae_ret_asan_memcpy E) (ae_ret_asan_memcpy E)
}.
End Contracts.
End WithSegs.
