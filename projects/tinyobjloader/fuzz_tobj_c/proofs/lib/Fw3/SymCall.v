(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "not"; "ex"; "iff"; "@Corelib.Init.Datatypes"; "list"; "pair"; "bool"; "option"; "Some"; "false"; "true"; "length"; "nat"; "orb"; "nil"; "app"; "prod"; "None"; "cons"; "snd"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "cfg_model"; "sys_input"; "cfg_ms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "sobj"; "sstate"; "sv"; "eval"; "smatch"; "ss_objs"; "cell"; "rl"; "ss_pc"; "soff"; "ss_next"; "mkObj"; "reg_sv"; "mem_match"; "obj_holds"; "SVar"; "DList"; "ob_base"; "obj_range"; "rw"; "dflt_writable"; "rm"; "SLit"; "holds"; "ob_dflt"; "obj_hi_of"; "obj_lo_of"; "odefault"; "regs_match"; "sprop"; "ss_facts"; "swf"; "obj_wf"; "ro_addr"; "ss_fcsr"; "ss_resv"; "DZero"; "c_off"; "outside_all"; "ro_clear"; "sv_below"; "tfact"; "agree_below"; "c_val"; "covered"; "fcsr_match"; "freg_sv"; "fregs_match"; "mkVal"; "ob_cells"; "ob_hi"; "ob_lo"; "pairwise_disjoint"; "ranges_disjoint"; "rd"; "rd_bytes"; "resv_match"; "rom_ok"; "sfcsr"; "ss_fregs"; "ss_regs"; "mkSS"; "ss_lenient"; "tf_expr"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "ms_mem"; "ms_rom"; "write_to_mem"; "ms_gpr"; "ms_read_byte"; "ms_svc_pending"; "ms_pc"; "ms_regs"; "MachineOk"; "find_segment"; "machine_result"; "ms_writable_byte"; "step"; "wview"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "FdEntry"; "read_bytes_aux"; "read_bytes_map"; "ENOTTY"; "FdChannel"; "errno_ret"; "fd_lookup"; "m_fds"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall.C"; "smatch_pending"; "sv_has_rl"; "S_after"; "obj_has_rl"; "SPp"; "SPpJ"; "ok_pframe"; "state_has_rl"; "dflt_has_rl"; "sprop_has_rl"; "vpart"; "mmap_obj"; "ok_pframeJ"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "of_nat"; "lt"; "sub"; "to_nat"; "pow"; "eqb"; "@LinuxProcessSemantics.Riscv.Instr"; "instr"; "Ecall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "model_idle"; "wstep"; "triple1"; "etriple"; "assn"; "tcons"; "w_cfg"; "w_tr"; "ok_src"; "ok_tgt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "rho_set_rl"; "rho_set_rw"; "pending_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "instr_at"; "list_set"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysStep"; "after_sys_mem"; "after_sys"; "only_ok"; "zero_range"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "jpred"; "SP"; "SPJ"; "ok_frame"; "ok_frameJ"; "@Stdlib.Lists.List"; "existsb"; "nth_error"; "In"; "forallb"; "@Corelib.Lists.ListDef"; "nth"; "Forall"; "repeat"; "firstn"; "skipn"; "@Stdlib.PArith.BinPos.Pos"; "succ"; "eqb"; "le"; "@Corelib.Init.Peano"; "lt"; "@Corelib.Init.Nat"; "add"; "sub"; "@LinuxProcessSemantics.LinuxProcessSem.MemImageType"; "Segment"; "@LinuxProcessSemantics.LinuxProcessSem.BvBase"; "word_to_nat"; "@LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall"; "cmd32"; "fd32"; "@LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi";
"TIOCGWINSZ"; "@LinuxProcessSemantics.Riscv.Prelude"; "bvmap"; "@LinuxProcessSemantics.Riscv.Sem"; "reg_get"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import PArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType Fs State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundW SymSoundR.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition rho_set_rw (rho : valuation) (n : positive) (v : word) : valuation := ltac2:(tb__ "0|0|
S4eS6eS7S15Q40A1L_;Sb3R1Vn;A2Vv;S31Vrho;R1A2X7x2Li;S25Vrho;A1S33Vrho;A1A3").

Definition rho_set_rl (rho : valuation) (l : positive) (bs : list byte) : valuation := ltac2:(tb__ "0|0|
S4eS31Vrho;A1S6eS7S5S15Q8A1A1L_;Sb3R1Vl;A2Vbs;S25Vrho;R1A2X7x2Li;S33Vrho;A1A3").

Lemma rho_set_rw_at : ltac2:(tb__ "0|1|
S1dS6eS15Q40A1M0S0G0S31S9cR3R2R1A3R2A2R1A3Fv;Fn;Frho;").
Proof. intros. cbn. rewrite Pos.eqb_refl. reflexivity. Qed.

Lemma rho_set_rw_other : ltac2:(tb__ "0|1|
S1dS6eS15Q40A1M0S6eS2S0S6eR1R3A3A1S0G0S31S9cR5R4R3A3R2A2S31R5R2A2A3F_;Fi;Fv;Fn;Frho;").
Proof. intros rho n v i Hne. cbn. destruct (Pos.eqb_spec i n); [contradiction|reflexivity]. Qed.

Lemma rho_set_rw_rl : ltac2:(tb__ "0|0|
S1dS6eS15Q40A1S0S6eS5S15Q8A1A1F_;S25S9cR3R2R1A3A1S25R3A1A3Fv;Fn;Frho;").
Proof. reflexivity. Qed.

Lemma rho_set_rw_rm : ltac2:(tb__ "0|1|
S1dS6eS15Q40A1M0S0G0S8S15Q8A1A1F_;S33S9cR3R2R1A3A1S33R3A1A3Fv;Fn;Frho;").
Proof. reflexivity. Qed.

Lemma agree_below_set_rw : ltac2:(tb__ "0|0|
S1dS6eS15Q40A1S6eSb4R1R3A2S48R2R5S9cR5R4R3A3A3F_;Fm;Fv;Fn;Frho;").
Proof.
  intros rho n v m Hle. split; [|split; [reflexivity|reflexivity]].
  intros i Hi. cbn. destruct (Pos.eqb_spec i n); [lia|reflexivity].
Qed.

Lemma rho_set_rl_at : ltac2:(tb__ "0|1|
S1dS6eS5S15Q8A1A1M0S0G0S25S9bR3R2R1A3R2A2R1A3Fbs;Fl;Frho;").
Proof. intros. cbn. rewrite Pos.eqb_refl. reflexivity. Qed.

Lemma rho_set_rl_other : ltac2:(tb__ "0|1|
S1dS6eS5S15Q8A1A1M0S6eS2S0S6eR1R3A3A1S0G0S25S9bR5R4R3A3R2A2S25R5R2A2A3F_;Fi;Fbs;Fl;Frho;").
Proof. intros rho l bs i Hne. cbn. destruct (Pos.eqb_spec i l); [contradiction|reflexivity]. Qed.

Lemma rho_set_rl_rw : ltac2:(tb__ "0|0|
S1dS6eS5S15Q8A1A1S0S6eS15Q40A1F_;S31S9bR3R2R1A3A1S31R3A1A3Fbs;Fl;Frho;").
Proof. reflexivity. Qed.

Lemma rho_set_rl_rm : ltac2:(tb__ "0|1|
S1dS6eS5S15Q8A1M0A1S0S15Q40A1S8G0A1F_;S33S9bR3R2R1A3A1S33R3A1A3Fbs;Fl;Frho;").
Proof. reflexivity. Qed.

Definition pending_of (ms : machine_state) : machine_state :=
  {| ms_regs := ms_regs ms; ms_fregs := ms_fregs ms; ms_pc_val := ms_pc_val ms;
     ms_svc_pending := Some (ms_reg ms 17); ms_resv := ms_resv ms; ms_fcsr := ms_fcsr ms;
     ms_mem := ms_mem ms; ms_rom := ms_rom ms |}.

Lemma pending_of_regs : ltac2:(tb__ "0|0|
S5eS0SbdQ5S15Q40A1A2S66S9dR1A1A1S66R1A1A3Fms;").
Proof. reflexivity. Qed.
Lemma pending_of_mem : ltac2:(tb__ "0|0|
S5eS0S15Q40A1S8S15Q8A1A1F_;S5fS9dR1A1A1S5fR1A1A3Fms;").
Proof. reflexivity. Qed.
Lemma pending_of_rom : ltac2:(tb__ "0|0|
S5eS0S15Q40A1S8S15Q8A1A1F_;S60S9dR1A1A1S60R1A1A3Fms;").
Proof. reflexivity. Qed.
Lemma pending_of_pc : ltac2:(tb__ "0|0|
S5eS0S15Q40A1S65S9dR1A1A1S65R1A1A3Fms;").
Proof. reflexivity. Qed.
Lemma pending_of_pending : forall ms, ms_svc_pending (pending_of ms) = Some (ms_reg ms 17).
Proof. reflexivity. Qed.
Lemma pending_of_gpr : ltac2:(tb__ "0|0|
S5eSdS0S15Q40A1S62S9dR2A1R1A2S62R2R1A2A3Fi;Fms;").
Proof. reflexivity. Qed.
Lemma pending_of_read_byte : ltac2:(tb__ "0|0|
S5eS0S15Q40A1S8S15Q8A1A1Faddr;S63S9dR1A1A1S63R1A1A3Fms;").
Proof. reflexivity. Qed.

Section C.
Variable segs : list Segment.

Notation wstep := (wstep segs).

Definition smatch_pending (rho : valuation) (S : sstate) (w : list event * config) : Prop := ltac2:(tb__ "0|3|
S1cS14S5S70A1S18Vw;A3M0A1S5eS1aG0A1S6fS1S0S7S3dVS;A1SbA3S1S0S15Q40M1A1M2S65R2A1S17G1S26VS;A1A2A3S1S0S8G2A1S64R2A1S9G2S21Vrho;S2aVS;Z11A2A2A2A3S1S91R1A1S1S57Vsegs;R2A2S1S45Vsegs;R2A2S1S3aVrho;VS;R2A3S1S4dVrho;VS;R2A3S1S4bVrho;S40VS;A1R2A3S1S56Vrho;S41VS;A1R2A3S1S2bVsegs;Vrho;S23VS;A1R2A4SaeS3bS35Vrho;A1S3cVS;A1A3A2A2A2A2A2A2A2A2A2A2A2Tmd;Tms;").

Lemma regs_match_reg_get : ltac2:(tb__ "0|0|
S1dS1fS5eS6dS3aR4R3R2A3S1S89Z0R2A2S89R2Z20A2A2S0S15Q40A1SbeS66R4A1S17Q5R3A2A2S21R6S2aR5R3A2A2A3F_;F_;Fr;Fms;FS;Frho;").
Proof using .
  intros rho S ms r Hrm Hr.
  assert (Hu : bv_unsigned (Z_to_bv 5 r) = r).
  { rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 5) with 32. lia. }
  rewrite (Hrm (Z_to_bv 5 r)) by (rewrite Hu; lia). rewrite Hu. reflexivity.
Qed.

Lemma regs_match_ms_reg17 : forall rho S ms,
  regs_match rho S ms -> ms_reg ms 17 = eval rho (reg_sv S 17).
Proof using .
  intros rho S ms Hrm. unfold ms_reg.
  change (bv_eqb (17 : reg) 0) with false. cbv iota.
  exact (regs_match_reg_get rho S ms 17 Hrm ltac:(lia)).
Qed.

Lemma regs_match_gpr : ltac2:(tb__ "0|0|
S1dS1fS5eSdS3aR4R3R2A3Sb5R2U6A2S0S15Q40A1S62R4R3A2S21R6S2aR5S86ZaS88R3A1A2A2A2A3F_;F_;Fi;Fms;FS;Frho;").
Proof using .
  intros rho S ms i Hrm Hi. unfold ms_gpr. apply regs_match_reg_get; [exact Hrm | lia].
Qed.

Lemma smatch_x17 : forall rho S tr ms md,
  smatch segs rho S (tr, mkCfg ms md) -> ms_reg ms 17 = eval rho (reg_sv S 17).
Proof using .
  intros rho S tr ms md Hsm. pose proof Hsm as (_ & _ & _ & _ & _ & _ & Hregs & _).
  exact (regs_match_ms_reg17 rho S ms Hregs).
Qed.

Lemma smatch_gpr : ltac2:(tb__ "0|1|
S1dS1fS5S70A1M0S5eS6fSdS22Vsegs;R6R5S6G0S18R4S19R3R2A2A4A4Sb5R2U6A2S0S15Q40A1S62R5R3A2S21R8S2aR7S86ZaS88R3A1A2A2A2A3F_;F_;Fi;Fmd;Fms;Ftr;FS;Frho;").
Proof using .
  intros rho S tr ms md i Hsm Hi. pose proof Hsm as (_ & _ & _ & _ & _ & _ & Hregs & _).
  exact (regs_match_gpr rho S ms i Hregs Hi).
Qed.

Lemma smatch_pending_of : ltac2:(tb__ "0|1|
S1dS1fS5S70A1M0S5eS6fS22Vsegs;R5R4S6G0S18R3S19R2R1A2A4A4S79R6R5S6G0S18R4S19S9dR3A1R2A2A4A3F_;Fmd;Fms;Ftr;FS;Frho;").
Proof using .
  intros rho S tr ms md Hsm.
  pose proof Hsm as (Hwf & Hpc & Hpend & Hhalt & Hrom & Hroc & Hregs & Hfregs & Hfcsr & Hresv & Hmem & Hfacts).
  cbn [fst snd cfg_ms cfg_model] in *.
  unfold smatch_pending. cbn [fst snd cfg_ms cfg_model].
  split; [exact Hwf|]. split; [exact Hpc|].
  split; [cbn [pending_of ms_svc_pending]; f_equal; exact (regs_match_ms_reg17 rho S ms Hregs)|].
  split; [exact Hhalt|]. split; [exact Hrom|]. split; [exact Hroc|].
  split; [exact Hregs|]. split; [exact Hfregs|]. split; [exact Hfcsr|]. split; [exact Hresv|].
  split; [|exact Hfacts].
  apply (mem_match_same_mem segs rho (ss_objs S) ms); [reflexivity|reflexivity|exact Hmem].
Qed.

Lemma smatch_pending_pending : ltac2:(tb__ "0|2|
S1dS1fS5S70A1M0S5eS6fS79R5R4S6G0S18R3S19R2R1A2A4A3S0S8S15Q40A1M1A1S64R3A1S9G1S21R6S2aR5Z11A2A2A2A3F_;Fmd;Fms;Ftr;FS;Frho;").
Proof using . intros rho S tr ms md H. pose proof H as (_ & _ & Hp & _). exact Hp. Qed.

Lemma smatch_pending_halted : ltac2:(tb__ "0|1|
S1dS1fS5S70A1M0S5eS6fS79R5R4S6G0S18R3S19R2R1A2A4A3S91R2A1F_;Fmd;Fms;Ftr;FS;Frho;").
Proof using . intros rho S tr ms md H. pose proof H as (_ & _ & _ & Hh & _). exact Hh. Qed.

Lemma smatch_pending_gpr : ltac2:(tb__ "0|1|
S1dS1fS5S70A1M0S5eS6fSdS79R6R5S6G0S18R4S19R3R2A2A4A3Sb5R2U6A2S0S15Q40A1S62R5R3A2S21R8S2aR7S86ZaS88R3A1A2A2A2A3F_;F_;Fi;Fmd;Fms;Ftr;FS;Frho;").
Proof using .
  intros rho S tr ms md i H Hi. pose proof H as (_ & _ & _ & _ & _ & _ & Hregs & _).
  exact (regs_match_gpr rho S ms i Hregs Hi).
Qed.

Lemma smatch_pending_regs : ltac2:(tb__ "0|1|
S1dS1fS5S70A1M0S5eS6fS79R5R4S6G0S18R3S19R2R1A2A4A3S3aR6R5R3A3F_;Fmd;Fms;Ftr;FS;Frho;").
Proof using . intros rho S tr ms md H. pose proof H as (_ & _ & _ & _ & _ & _ & Hregs & _). exact Hregs. Qed.

Lemma smatch_pending_mem : ltac2:(tb__ "0|1|
S1dS1fS5S70A1M0S5eS6fS79R5R4S6G0S18R3S19R2R1A2A4A3S2bVsegs;R6S23R5A1R3A4F_;Fmd;Fms;Ftr;FS;Frho;").
Proof using . intros rho S tr ms md H. pose proof H as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hmem & _). exact Hmem. Qed.

Lemma smatch_pending_rom : ltac2:(tb__ "0|1|
S1dS1fS5S70A1M0S5eS6fS79R5R4S6G0S18R3S19R2R1A2A4A3S57Vsegs;R3A2F_;Fmd;Fms;Ftr;FS;Frho;").
Proof using . intros rho S tr ms md H. pose proof H as (_ & _ & _ & _ & Hrom & _). exact Hrom. Qed.

Lemma smatch_pending_ro_clear : ltac2:(tb__ "0|1|
S1dS1fS5S70A1M0S5eS6fS79R5R4S6G0S18R3S19R2R1A2A4A3S45Vsegs;R3A2F_;Fmd;Fms;Ftr;FS;Frho;").
Proof using . intros rho S tr ms md H. pose proof H as (_ & _ & _ & _ & _ & Hroc & _). exact Hroc. Qed.

Lemma smatch_pending_facts : ltac2:(tb__ "0|1|
S1dS1fS5S70A1M0S5eS6fS79R5R4S6G0S18R3S19R2R1A2A4A3SaeS3bS35R6A1S3cR5A1A3F_;Fmd;Fms;Ftr;FS;Frho;").
Proof using . intros rho S tr ms md H. pose proof H as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hf). exact Hf. Qed.

Lemma smatch_pending_swf : ltac2:(tb__ "0|1|
S1dS1fS5S70A1M0S5eS6fS79R5R4S6G0S18R3S19R2R1A2A4A3S0S7S3dR5A1SbA3F_;Fmd;Fms;Ftr;FS;Frho;").
Proof using . intros rho S tr ms md H. pose proof H as (Hwf & _). exact Hwf. Qed.

Lemma smatch_pending_frame : ltac2:(tb__ "0|1|
S1dS1fS5S70A1M0S5eS6fG0S6fS79R7R6S6G0S18R5S19R4R3A2A4A3S91R2A1S79R9R8S6G0S18R4S19R6R3A2A4A3F_;F_;Fmd';Ftr';Fmd;Fms;Ftr;FS;Frho;").
Proof using .
  intros rho S tr ms md tr' md' H Hh.
  pose proof H as (Hwf & Hpc & Hpend & Hhalt & Hrest).
  unfold smatch_pending. cbn [fst snd cfg_ms cfg_model] in *.
  split; [exact Hwf|]. split; [exact Hpc|]. split; [exact Hpend|]. split; [exact Hh|]. exact Hrest.
Qed.

Lemma smatch_pending_agree : ltac2:(tb__ "0|1|
S1dS1dS1fS5S70A1M0S5eS6fS48S28R4A1R6R5A3S79R7R5S6G0S18R4S19R3R2A2A4A3S79R7R6S6G0S18R5S19R4R3A2A4A3F_;F_;Fmd;Fms;Ftr;FS;Frho';Frho;").
Proof using .
  intros rho rho' S tr ms md Hag H.

  set (ms0 := {| ms_regs := ms_regs ms; ms_fregs := ms_fregs ms; ms_pc_val := ms_pc_val ms;
                 ms_svc_pending := None; ms_resv := ms_resv ms; ms_fcsr := ms_fcsr ms;
                 ms_mem := ms_mem ms; ms_rom := ms_rom ms |}).
  pose proof H as (Hwf & Hpc & Hpend & Hhalt & Hrom & Hroc & Hregs & Hfregs & Hfcsr & Hresv & Hmem & Hfacts).
  cbn [fst snd cfg_ms cfg_model] in *.
  assert (Hsm0 : smatch segs rho S (tr, mkCfg ms0 md)).
  { unfold smatch. cbn [fst snd cfg_ms cfg_model].
    split; [exact Hwf|]. split; [exact Hpc|]. split; [reflexivity|]. split; [exact Hhalt|].
    split; [exact Hrom|]. split; [exact Hroc|]. split; [exact Hregs|]. split; [exact Hfregs|].
    split; [exact Hfcsr|]. split; [exact Hresv|]. split; [|exact Hfacts].
    apply (mem_match_same_mem segs rho (ss_objs S) ms); [reflexivity|reflexivity|exact Hmem]. }
  pose proof (smatch_agree segs rho rho' S _ Hag Hsm0) as Hsm1.
  pose proof Hsm1 as (_ & _ & _ & _ & _ & _ & Hregs' & Hfregs' & Hfcsr' & Hresv' & Hmem' & Hfacts').
  cbn [fst snd cfg_ms cfg_model] in *.
  unfold smatch_pending. cbn [fst snd cfg_ms cfg_model].
  split; [exact Hwf|]. split; [exact Hpc|].
  split.
  { rewrite Hpend. f_equal. apply (eval_agree (ss_next S)); [exact Hag|].
    unfold reg_sv. cbn [Z.eqb]. apply forallb_nth; [apply swf_regs_below; exact Hwf | reflexivity]. }
  split; [exact Hhalt|]. split; [exact Hrom|]. split; [exact Hroc|].
  split; [exact Hregs'|]. split; [exact Hfregs'|]. split; [exact Hfcsr'|]. split; [exact Hresv'|].
  split; [|exact Hfacts'].
  apply (mem_match_same_mem segs rho' (ss_objs S) ms0); [reflexivity|reflexivity|exact Hmem'].
Qed.

Lemma ecall_step : ltac2:(tb__ "0|1|
S1dS1fS5S70A1M0S5eS6fS22Vsegs;R5R4S6G0S18R3S19R2R1A2A4A4S0S8S8eA1S9eVsegs;S26R5A1A2S9S8eS8fA2A3S0S69S5eA1S6bVsegs;R4A2S67S5eS9dR4A1A2A3F_;F_;Fmd;Fms;Ftr;FS;Frho;").
Proof using .
  intros rho S tr ms md Hsm Hi.
  pose proof Hsm as (_ & Hpc & _). cbn [fst snd cfg_ms cfg_model] in Hpc.
  exact (step_ecall_at segs ms (ss_pc S) Hpc Hi).
Qed.

Lemma ecall_wstep : ltac2:(tb__ "0|1|
S1dS1fS5S70A1M0S5eS6fS22Vsegs;R5R4S6G0S18R3S19R2R1A2A4A4S0S8S8eA1S9eVsegs;S26R5A1A2S9S8eS8fA2A3S92Vsegs;S6G0S18R5S19R4R3A2A4S6G0S18R5S19S9dR4A1R3A2A4A3F_;F_;Fmd;Fms;Ftr;FS;Frho;").
Proof using .
  intros rho S tr ms md Hsm Hi.
  pose proof Hsm as (_ & _ & Hpend & Hhalt & _). cbn [fst snd cfg_ms cfg_model] in Hpend, Hhalt.
  apply wstep_of_step; [exact Hhalt | exact Hpend | exact (ecall_step rho S tr ms md Hsm Hi)].
Qed.

Lemma ecall_wstep_inv : ltac2:(tb__ "0|1|
S1dS1fS5S70A1M0S5eS6fS90S22Vsegs;R6R5S6G0S18R4S19R3R2A2A4A4S0S8S8eA1S9eVsegs;S26R6A1A2S9S8eS8fA2A3S92Vsegs;S6G0S18R6S19R5R4A2A4R3A3S0S90R4S6G0S18R7S19S9dR6A1R5A2A4A3F_;F_;F_;Fw';Fmd;Fms;Ftr;FS;Frho;").
Proof using .
  intros rho S tr ms md w' Hsm Hi Hw.
  pose proof Hsm as (_ & _ & Hpend & Hhalt & _). cbn [fst snd cfg_ms cfg_model] in Hpend, Hhalt.
  exact (wstep_step_inv segs tr ms md (pending_of ms) w' Hhalt Hpend (ecall_step rho S tr ms md Hsm Hi) Hw).
Qed.

Lemma pending_gpr : ltac2:(tb__ "0|1|
S1dS1fS5S70A1M0S5eS6fSdS22Vsegs;R6R5S6G0S18R4S19R3R2A2A4A4Sb5R2U6A2S0S15Q40A1S62S9dR5A1R3A2S21R8S2aR7S86ZaS88R3A1A2A2A2A3F_;F_;Fi;Fmd;Fms;Ftr;FS;Frho;").
Proof using . intros rho S tr ms md i Hsm Hi. rewrite pending_of_gpr. eapply smatch_gpr; eauto. Qed.

Lemma ecall_ok : ltac2:(tb__ "0|1|
S90OF_;S5S70A1M0S6fOF_;F_;S1dS1fG0S5eS6fSa7Vsegs;R7R6A3R7R4R2A2S22Vsegs;R7R6S6G0S18R5S19R4R3A2A4A4S0S8S8eA1S9eVsegs;S26R7A1A2S9S8eS8fA2A3RbS6G0S18R7S19R6R5A2A4A1F_;F_;F_;F_;Fmd;Fms;Ftr;FS;Frho;FK;Fok;").
Proof using .
  intros ok K rho S tr ms md Hok Hk Hsm Hi.
  pose proof Hsm as (_ & _ & Hpend & Hhalt & _). cbn [fst snd cfg_ms cfg_model] in Hpend, Hhalt.
  exact (Hok tr ms md (pending_of ms) Hk Hhalt Hpend (ecall_step rho S tr ms md Hsm Hi)).
Qed.

Definition SPp (K : list event -> Model -> Prop) (S : sstate) (rho : valuation) : assn := ltac2:(tb__ "0|0|
S90S1S79Vrho;VS;R1A3VK;S98R1A1S1aS97R1A1A1A2A2Lw;").

Lemma triple1_ecall : ltac2:(tb__ "0|0|
S90OF_;S5S70A1S6fOF_;F_;S1fS1dSa7Vsegs;R4R3A3S0S8S8eA1S9eVsegs;S26R3A1A2S9S8eS8fA2A3S93Vsegs;R6Sa5Vsegs;R5R4R3A4S7dR5R4R3A3A4F_;F_;Frho;FS;FK;Fok;").
Proof using .
  intros ok K S rho Hok Hi. apply triple1_step.
  intros [tr [ms md]] [Hsm Hk]. cbn [w_tr w_cfg fst snd cfg_model] in Hk.
  split; [eapply ecall_ok; eauto|].
  intros w' Hw. rewrite (ecall_wstep_inv rho S tr ms md w' Hsm Hi Hw).
  split; [apply smatch_pending_of; exact Hsm | exact Hk].
Qed.

Lemma etriple_ecall : ltac2:(tb__ "0|0|
S5S70A1S6fOF_;F_;S1fS1dS0S8S8eA1S9eVsegs;S26R2A1A2S9S8eS8fA2A3S94Vsegs;Sa5Vsegs;R4R3R2A4S7dR4R3R2A3A3F_;Frho;FS;FK;").
Proof using .
  intros K S rho Hi. apply etriple_step.
  intros [tr [ms md]] [Hsm Hk]. cbn [w_tr w_cfg fst snd cfg_model] in Hk.
  exists (tr, mkCfg (pending_of ms) md). split; [eapply ecall_wstep; eauto|].
  split; [apply smatch_pending_of; exact Hsm | exact Hk].
Qed.

Definition S_after (S : sstate) (e : sv) (objs : list sobj) (nx : positive) : sstate := ltac2:(tb__ "0|0|
S5bS86S26VS;A1Z4A2S9fS20S5aVS;A1UaVe;A4S59VS;A1S40VS;A1S41VS;A1Vobjs;S3cVS;A1Vnx;S5cVS;A1A9").

Lemma swf_S_after : ltac2:(tb__ "0|0|
S1fS20S5S1eA1S6eS0S7S3dR4A1SbA3Sb4S28R5A1R2A2S0S7S46R3R5A2SbA3S0S7SacS1eS3eR4A1R5A3SbA3S0S7S3dS7bR8R7R6R5A4A1SbA3F_;F_;F_;F_;Fnx;Fobjs;Fe;FS;").
Proof using .
  intros S e objs nx Hwf Hle He Hobjs.
  pose proof (swf_mono_next S nx Hle Hwf) as H1.
  unfold swf in H1 |- *. unfold S_after.
  cbn [ss_pc ss_regs ss_fregs ss_fcsr ss_resv ss_objs ss_facts ss_next] in *.
  repeat (apply andb_prop in H1; destruct H1 as [H1 ?]).
  repeat (apply andb_true_intro; split);
    first [ assumption
          | rewrite list_set_length; assumption
          | apply forallb_list_set; assumption ].
Qed.

Lemma reg_sv_S_after : ltac2:(tb__ "0|0|
S1fS20S5S1eA1S6eS6dS0S7S3dR5A1SbA3S1S87Z0R2A2S89R2Z20A2A2S0S20S2aS7bR7R6R5R4A4R3A2S7S20L_;S8dR3ZaA2R6S2aR7R3A2X7x2A3F_;F_;Fr;Fnx;Fobjs;Fe;FS;").
Proof using .
  intros S e objs nx r Hwf Hr. pose proof (swf_regs_len S Hwf) as Hlen.
  unfold reg_sv, S_after. cbn [ss_regs].
  destruct (Z.eqb_spec r 0) as [E0|E0].
  - subst. reflexivity.
  - rewrite nth_list_set by (rewrite Hlen; lia).
    destruct (Nat.eqb_spec (Z.to_nat r) 10) as [En|En]; destruct (Z.eqb_spec r 10) as [Ez|Ez];
      try reflexivity; exfalso; lia.
Qed.

Lemma freg_sv_S_after : ltac2:(tb__ "0|0|
S1fS20S5S1eA1S6eS6dS0S20S4cS7bR5R4R3R2A4R1A2S4cR5R1A2A3Fr;Fnx;Fobjs;Fe;FS;").
Proof using . reflexivity. Qed.

Lemma smatch_after_sys : ltac2:(tb__ "0|4|
S1dS1fS5S70A1M0S5eS6fG0S6fS15Q40A1M1S20G1S8S15Q8A1M2A1M3F_;S5S1eA1S6eS79RcRbS6G0S18RaS19R9R8A2A4A3S91R7A1Sb4S28RdA1R3A2S0S7S46R4R7A2SbA3S0G1S21R10R8A2R9A3S0S7SacS1eS3eR6A1R7A3SbA3S2bVsegs;R12R8Sa0RfRbR9A3A4G1S0S7S3fVsegs;R1A2SbA3S0G3RcR2A1S12G2A1A3F_;Fa;S22Vsegs;R14S7bR13RcRaR9A4S6G0S18RfS19Sa0R11RdRbA3ReA2A4A4F_;F_;F_;F_;F_;F_;F_;F_;Fnx;Fobjs;Fmem;Fe;Fr;Fmd';Ftr';Fmd;Fms;Ftr;FS;Frho;").
Proof using .
  intros rho S tr ms md tr' md' r e mem objs nx Hsp Hh' Hle He Hev Hobjs Hmm Hroc'.
  pose proof Hsp as (Hwf & Hpc & Hpend & Hhalt & Hrom & Hroc & Hregs & Hfregs & Hfcsr & Hresv & Hmem & Hfacts).
  cbn [fst snd cfg_ms cfg_model] in *.
  unfold smatch. cbn [fst snd cfg_ms cfg_model].
  split; [apply swf_S_after; assumption|].
  split.
  { rewrite after_sys_pc, Hpc. unfold S_after; cbn [ss_pc]. apply bv_add_ZZ. }
  split; [reflexivity|].
  split; [exact Hh'|].
  split; [intros a; rewrite after_sys_rom; apply Hrom|].
  split; [intros a Ha; rewrite after_sys_memq; apply Hroc'; exact Ha|].
  split.
  { intros rr Hrr.
    pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
    rewrite reg_sv_S_after by (auto; lia).
    unfold after_sys_mem; cbn [ms_regs]. rewrite reg_get_set. unfold bv_eqb.
    change (bv_unsigned (Z_to_bv 5 10)) with 10.
    destruct (Z.eqb_spec (bv_unsigned rr) 10) as [E|E]; [symmetry; exact Hev | apply Hregs; exact Hrr]. }
  split; [intros rr; rewrite after_sys_fregs, freg_sv_S_after; apply Hfregs|].
  split; [unfold fcsr_match in *; unfold S_after; cbn [ss_fcsr]; rewrite after_sys_fcsr; exact Hfcsr|].
  split; [unfold resv_match in *; unfold S_after; cbn [ss_resv]; rewrite after_sys_resv; exact Hresv|].
  split; [exact Hmm|].
  exact Hfacts.
Qed.

Lemma mem_match_after_sys_same : ltac2:(tb__ "0|0|
S1dS5S1eA1S5eS15Q40A1S2bVsegs;R4R3R2A4S2bVsegs;R5R4Sa1R3R2A2A4F_;Fr;Fms;Fobjs;Frho;").
Proof using .
  intros rho objs ms r Hmm. unfold after_sys.
  apply (mem_match_same_mem segs rho objs ms); [reflexivity|reflexivity|exact Hmm].
Qed.

Lemma smatch_after_ret : ltac2:(tb__ "0|2|
S1dS1fS5S70A1M0S5eS6fG0S6fS15Q40A1S79R8R7S6G0S18R6S19R5R4A2A4A3S91R3A1S22Vsegs;S9cRaS28R9A1M1R3A3S7bR9S2dG1A1S23R9A1Sb2G1A1A4S6G0S18R5S19Sa1R7R3A2R4A2A4A4F_;F_;Fr;Fmd';Ftr';Fmd;Fms;Ftr;FS;Frho;").
Proof using .
  intros rho S tr ms md tr' md' r Hsp Hh'.
  set (rho' := rho_set_rw rho (ss_next S) r).
  assert (Hag : agree_below (ss_next S) rho rho') by (apply agree_below_set_rw; lia).
  pose proof (smatch_pending_agree rho rho' S tr ms md Hag Hsp) as Hsp'.
  unfold after_sys. eapply smatch_after_sys; [exact Hsp' | exact Hh' | lia | | | | |].
  - cbn. apply Pos.ltb_lt. lia.
  - cbn. rewrite Pos.eqb_refl. reflexivity.
  - apply forallb_forall. intros o Hin. eapply obj_wf_mono; [|exact (proj1 (forallb_forall _ _) (swf_objs S (smatch_pending_swf _ _ _ _ _ Hsp)) o Hin)]. lia.
  - apply (mem_match_after_sys_same). exact (smatch_pending_mem _ _ _ _ _ Hsp').
  - exact (smatch_pending_ro_clear _ _ _ _ _ Hsp).
Qed.

Lemma smatch_after_ret_lit : ltac2:(tb__ "0|2|
S1dS1fS5S70A1M0S5eS6fG0S6fS15Q40M1A1S79R8R7S6G0S18R6S19R5R4A2A4A3S91R3A1S22Vsegs;RaS7bR9S34S16G1R3A2A1S23R9A1S28R9A1A4S6G0S18R5S19Sa1R7R3A2R4A2A4A4F_;F_;Fr;Fmd';Ftr';Fmd;Fms;Ftr;FS;Frho;").
Proof using .
  intros rho S tr ms md tr' md' r Hsp Hh'.
  unfold after_sys. eapply smatch_after_sys; [exact Hsp | exact Hh' | lia | reflexivity | | | |].
  - cbn. apply Z_to_bv_bv_unsigned.
  - exact (swf_objs S (smatch_pending_swf _ _ _ _ _ Hsp)).
  - apply (mem_match_after_sys_same). exact (smatch_pending_mem _ _ _ _ _ Hsp).
  - exact (smatch_pending_ro_clear _ _ _ _ _ Hsp).
Qed.

Lemma smatch_after_ret_expr : ltac2:(tb__ "0|2|
S1dS1fS5S70A1M0S5eS6fG0S6fS15Q40A1M1S20S79R9R8S6G0S18R7S19R6R5A2A4A3S91R4A1S0S7S46S28RaA1R3A2SbA3S0G1S21RcR4A2R5A3S22Vsegs;RdS7bRcR5S23RcA1S28RcA1A4S6G0S18R8S19Sa1RaR6A2R7A2A4A4F_;F_;F_;F_;Fe;Fr;Fmd';Ftr';Fmd;Fms;Ftr;FS;Frho;").
Proof using .
  intros rho S tr ms md tr' md' r e Hsp Hh' He Hev.
  unfold after_sys. eapply smatch_after_sys; [exact Hsp | exact Hh' | lia | exact He | exact Hev | | |].
  - exact (swf_objs S (smatch_pending_swf _ _ _ _ _ Hsp)).
  - apply (mem_match_after_sys_same). exact (smatch_pending_mem _ _ _ _ _ Hsp).
  - exact (smatch_pending_ro_clear _ _ _ _ _ Hsp).
Qed.

Lemma obj_holds_ext : ltac2:(tb__ "0|3|
S1dS6eS5eS5eS1eS0S15Q40M0A1S8S15Q8A1A1M1F_;S60R2A1S60R3A1A3S6dS1S87S38R7R3A2R1A2S89R1S37R7R3A2A2A2S0G1S5fR5S17G0S86S16G0S21R8S2fR4A1A2A2R2A2A2M2A2S5fR6G2A2A3F_;Foff;S0S7S3eR6R3A2SbA3S2cVsegs;R8R6R4A4S2cVsegs;R9R6R5A4F_;F_;F_;F_;Fo;Fms';Fms;Fn;Frho;").
Proof using .
  intros rho n ms ms' o Hr Hsame Hwf (Hb & Hw & Hc & Hd & Hdl).
  unfold obj_lo_of, obj_hi_of in *. unfold obj_holds, obj_lo_of, obj_hi_of.
  split; [exact Hb|]. split.
  { intros off' Hoff'. unfold wview. rewrite Hsame by exact Hoff'. apply Hw. exact Hoff'. }
  split.
  { apply Forall_forall. intros c Hin. pose proof (proj1 (Forall_forall _ _) Hc c Hin) as (B1 & B2 & Hch).
    destruct (obj_wf_cell _ _ _ Hwf Hin) as (C1 & C2 & C3 & C4).
    unfold cell_holds. split; [exact B1|]. split; [exact B2|]. rewrite <- Hch. apply rd_bytes_unchanged; [exact Hr | |].
    - rewrite oaddr_unsigned by lia. rewrite Z2Nat.id by lia. lia.
    - intros j Hj. rewrite oaddr_unsigned by lia. rewrite <- Z.add_assoc. apply Hsame. lia. }
  split; [| eapply dflt_inv_unchanged; [exact Hr | exact Hsame | lia | lia | exact Hdl]].
  intros off' Hoff' Hcov. specialize (Hd off' Hoff' Hcov).
  destruct (ob_dflt o); cbn in Hd |- *.
  - destruct Hd as [b Hbb]. exists b. rewrite (rd_unchanged ms ms'); [exact Hbb | apply Hsame; lia | exact Hr].
  - rewrite (rd_unchanged ms ms'); [exact Hd | apply Hsame; lia | exact Hr].
  - destruct Hd as [Hnone Hib]. split; [|exact Hib]. rewrite Hsame by lia. exact Hnone.
  - rewrite (rd_unchanged ms ms'); [exact Hd | apply Hsame; lia | exact Hr].
  - rewrite (rd_unchanged ms ms'); [exact Hd | apply Hsame; lia | exact Hr].
  - destruct Hd as [b Hbb]. exists b. rewrite (rd_unchanged ms ms'); [exact Hbb | apply Hsame; lia | exact Hr].
Qed.

Lemma pairwise_disjoint_app1 : ltac2:(tb__ "0|0|
S1dS5S1eA1S1eS52R3R2A2SaeS1eS1eS53S30R5R1A2S30R5R3A2A2Lo';R3A3S52R5S10S1eR4S13S1eR3SfS1eA1A3A3A2F_;F_;Fo;Fobjs;Frho;").
Proof using .
  intros rho objs o. induction objs as [|h t IH]; intros Hpd Hf.
  - cbn. split; [constructor | exact I].
  - cbn. destruct Hpd as [Hh Ht]. inversion Hf; subst. split.
    + apply Forall_app. split; [exact Hh|]. constructor; [assumption | constructor].
    + apply IH; assumption.
Qed.

Lemma outside_all_app : ltac2:(tb__ "0|1|
S1dS5S1eA1M0G0S15Q40A1S4S44R4S10S1eR3R2A3R1A3S1S44R4R3R1A3S44R4R2R1A3A2A2Fa;Fl2;Fl1;Frho;").
Proof using . intros. unfold outside_all. apply Forall_app. Qed.

Lemma u64_of_sum : ltac2:(tb__ "0|1|
S6dS1S87Z0R1A2S89R1S8cZ2Z40A2A2A2S0S6dS16Q40M0S17G0R2A2A2R2A3F_;Fx;").
Proof using . intros x Hx. rewrite Z_to_bv_unsigned. apply bv_wrap_small. rewrite two64. exact Hx. Qed.

Lemma ro_addr_false_of_no_segment : ltac2:(tb__ "0|1|
S15Q40M0A1S0S8Sb8A1S68Vsegs;S16G0R1A2Z1A3S12Sb8A1A3S0S7S3fVsegs;R2A2SaA3F_;Fx;").
Proof using . intros x H. unfold ro_addr. rewrite H. reflexivity. Qed.

Definition mmap_obj (nxt : positive) (nlit : Z) : sobj := ltac2:(tb__ "0|0|
S29S2dVnxt;A1S34Z0A1S34Vnlit;A1SfS24A1S42A5").

Lemma smatch_after_mmap : ltac2:(tb__ "0|8|
S1dS1fS5S70A1M0S5eS6fG0S6fS15Q40M1A1M2G2S6dS79RaR9S6G0S18R8S19R7R6A2A4A3S91R5A1S0S6dS16G1R4A2R3A3S89R4S8cZ2M3Z3fA2A2S87S86S16G1R7A2R5A2S8cG3Z40A2A2S1eSabS1eR1S23RfA1A3S53S30R11R2A2S6S6dS6dS16G1RaA2M4S86G4R8A2M5A4A2F_;Fo;G2S1S87G4S16G1R1A2M6A2S89G6G5A2A2S0S7S3fVsegs;R2A2SaA3F_;Fx;S22Vsegs;S9cR11S28R10A1M7RaA3S7bR10S2dG7A1S10S1eS23R10A1S13S1eS84G7R8A2SfS1eA1A3A3Sb2G7A1A4S6G0S18RcS19Sa0ReRaSa3S5fReA1RaR9A3A3RbA2A4A4F_;F_;F_;F_;F_;F_;F_;Fnlit;Fn;Fa;Fmd';Ftr';Fmd;Fms;Ftr;FS;Frho;").
Proof using .
  intros rho S tr ms md tr' md' a n nlit Hsp Hh' Hn Hn63 Hnw Hdisj Hnro.
  pose proof (urange a) as Ha. pose proof (urange n) as Hn0.
  set (nx := ss_next S). set (rho' := rho_set_rw rho nx a).
  assert (Hag : agree_below nx rho rho') by (apply agree_below_set_rw; lia).
  pose proof (smatch_pending_agree rho rho' S tr ms md Hag Hsp) as Hsp'.
  pose proof (smatch_pending_swf _ _ _ _ _ Hsp) as Hwf.
  pose proof (swf_objs S Hwf) as Hobjwf.
  assert (Hbase : eval rho' (SVar nx) = a) by (cbn; rewrite Pos.eqb_refl; reflexivity).
  assert (Hlo0 : soff rho' (SLit 0) = 0) by (rewrite soff_lit; reflexivity).
  assert (Hhi0 : soff rho' (SLit nlit) = nlit).
  { rewrite soff_lit. unfold snorm. rewrite Z.mod_small by lia. destruct (Z.ltb_spec nlit (2 ^ 63)); lia. }
  assert (Hrng : forall o, In o (ss_objs S) -> obj_range rho' o = obj_range rho o).
  { intros o Hin. eapply obj_range_agree; [exact Hag | exact (proj1 (forallb_forall _ _) Hobjwf o Hin)]. }
  assert (Hzr : forall x : word,
            zero_range (ms_mem ms) a n x = if in_range a n x then Some (Z_to_bv 8 0) else ms_mem ms x)
    by (intros x; apply zero_range_at).
  eapply smatch_after_sys; [exact Hsp' | exact Hh' | lia | | exact Hbase | | |].
  - cbn. apply Pos.ltb_lt. lia.
  - rewrite forallb_app. apply andb_true_intro. split.
    + apply forallb_forall. intros o Hin. eapply obj_wf_mono; [|exact (proj1 (forallb_forall _ _) Hobjwf o Hin)]. lia.
    + unfold mmap_obj, obj_wf. cbn [ob_base ob_lo ob_hi ob_cells forallb sv_below andb].
      rewrite (proj2 (Pos.ltb_lt nx (Pos.succ nx))) by lia. reflexivity.
  - pose proof (smatch_pending_mem _ _ _ _ _ Hsp') as (Hall & Hpd & Hfr).
    pose proof (smatch_pending_rom _ _ _ _ _ Hsp') as Hrom.
    split; [|split].
    + apply Forall_app. split.
      * apply Forall_forall. intros o Hin.
        pose proof (proj1 (Forall_forall _ _) Hall o Hin) as Ho.
        pose proof (proj1 (forallb_forall _ _) Hobjwf o Hin) as Howf.
        eapply (obj_holds_ext rho' nx ms); [reflexivity | | exact Howf | exact Ho].
        intros off Hoff. rewrite after_sys_memq, Hzr.
        pose proof (Hdisj o Hin) as D. rewrite <- (Hrng o Hin) in D.
        pose proof (proj1 Ho) as HB. unfold obj_range, ranges_disjoint in D. cbn [fst snd] in D.
        unfold obj_lo_of, obj_hi_of in *.
        destruct (in_range a n _) eqn:Hir; [|reflexivity].
        apply in_range_spec in Hir. rewrite u64_of_sum in Hir by lia. lia.
      * constructor; [|constructor].
        unfold obj_holds, obj_lo_of, obj_hi_of, mmap_obj. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt]. rewrite Hbase, Hlo0, Hhi0.
        split; [lia|]. split.
        { intros off Hoff. rewrite after_sys_memq. unfold wview. rewrite Hzr.
          replace (in_range a n (Z_to_bv 64 (bv_unsigned a + off))) with true; [discriminate|].
          symmetry. apply in_range_spec. rewrite u64_of_sum by lia. lia. }
        split; [constructor|]. split; [|exact I].
        intros off Hoff _. cbn [dflt_holds]. unfold rd, ms_read_byte. rewrite after_sys_memq, Hzr.
        replace (in_range a n (Z_to_bv 64 (bv_unsigned a + off))) with true; [reflexivity|].
        symmetry. apply in_range_spec. rewrite u64_of_sum by lia. lia.
    + apply pairwise_disjoint_app1; [exact Hpd|].
      apply Forall_forall. intros o Hin. rewrite (Hrng o Hin).
      unfold obj_range at 2. unfold obj_lo_of, obj_hi_of, mmap_obj. cbn [ob_base ob_lo ob_hi]. rewrite Hbase, Hlo0, Hhi0, Z.add_0_r.
      exact (Hdisj o Hin).
    + intros x Hout. apply outside_all_app in Hout as [Hout1 Hout2].
      rewrite after_sys_memq, Hzr.
      destruct (in_range a n x) eqn:Hir.
      * exfalso. apply in_range_spec in Hir. pose proof (Forall_inv Hout2) as Hx. cbn zeta in Hx.
        apply Hx. unfold obj_range, obj_lo_of, obj_hi_of, mmap_obj. cbn [ob_base ob_lo ob_hi fst snd]. rewrite Hbase, Hlo0, Hhi0. lia.
      * apply Hfr. exact Hout1.
  - intros x Hro. rewrite Hzr. destruct (in_range a n x) eqn:Hir.
    + apply in_range_spec in Hir. rewrite (Hnro x) in Hro by lia. discriminate.
    + apply (smatch_pending_ro_clear _ _ _ _ _ Hsp). exact Hro.
Qed.

Lemma obj_holds_kwrite : ltac2:(tb__ "0|7|
S1dS5eS5eS20S20S20S6dS6dS5S24A1S39S6eS15Q40M0A1M1S5S15Q8M2A1M3A1S6dS2cVsegs;ReRdS29RbRaR9R6R5A5A4S0S7S32R6A1SbA3S0S6dS27R10RcA2RaA3S0S6dS27R11RcA2RaA3S0G1S8G3A1M4F_;M5S60R10A1S60R11A1A3S0G5S5fR11A1S61S5fR12A1R8R7A3A3S0S6dS16G0R9A2S86S16G0S21R14R11A2A2R7A2A3S87RfR8A2S87S86R9S88ScG3RaA2A1A2RfA2S0S6dS88ScG3S25R17RdA2A2A1S8aR10R11A2A3SdSb5R1ScG3RdA2A2S0G3SadG3Sb6S8bS8aRdR14A2A1R2A2S25R1aR10A2S17G2Z0A2M6A4SadG3R2ReG6A4A3F_;Fj;S6dS1S87R14R1A2S89R1R13A2A2S2S1S87ReR2A2S89R2S86ReS88ScG3RfA2A1A2A2A2A1S0G4S54R1bS17G0S86S16G0S21R1cR19A2A2R3A2A2A2S9G3SadG3S8bS8aR3R16A2A1S25R1cR12A2G6A4A2A3F_;F_;Foff;S2cVsegs;R1aR18S29R17R16R15SfS24A1S2eR10A1A5A4F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fwoff;Fbs;Fbuf;Fl;Fd;Fcells;Fhi;Flo;Fehi;Felo;Fbase;Fms';Fms;Frho;").
Proof using .
  intros rho ms ms' base elo ehi lo hi cells d l buf bs woff Ho Hdw Helo Hehi Hr Hm Hbuf Hlo Hhi Hlen Hin Hout.
  unfold obj_holds, obj_lo_of, obj_hi_of in Ho. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt] in Ho.
  rewrite Helo, Hehi in Ho. destruct Ho as (Hb & Hw & _ & _ & _).
  set (B := bv_unsigned (eval rho base)) in *.
  assert (Hnw : bv_unsigned buf + Z.of_nat (length bs) <= 2 ^ 64) by lia.
  assert (Hsame : forall off, lo <= off < hi -> ~ (woff <= off < woff + Z.of_nat (length bs)) ->
            ms_mem ms' (Z_to_bv 64 (B + off)) = ms_mem ms (Z_to_bv 64 (B + off))).
  { intros off Hoff Hno. rewrite Hm. apply write_to_mem_out; [exact Hnw|].
    rewrite u64_of_sum by lia. lia. }
  unfold obj_holds, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt]. rewrite Helo, Hehi. fold B.
  split; [exact Hb|]. split.
  { intros off Hoff _. eapply wview_mono; [|apply Hw; [exact Hoff | exact Hdw]].
    intros y Hy. rewrite Hm. apply write_to_mem_grows. exact Hy. }
  split; [constructor|]. split; [|cbn; exact Hlen].
  intros off Hoff _. cbn [dflt_holds].
  destruct (Z_lt_le_dec off woff) as [Hlt|Hge].
  { rewrite (rd_unchanged ms ms'); [apply Hout; lia | apply Hsame; lia | exact Hr]. }
  destruct (Z_lt_le_dec off (woff + Z.of_nat (length bs))) as [Hlt2|Hge2].
  2:{ rewrite (rd_unchanged ms ms'); [apply Hout; lia | apply Hsame; lia | exact Hr]. }

  unfold rd, ms_read_byte. rewrite Hm.
  replace (B + off) with (bv_unsigned buf + Z.of_nat (Z.to_nat (off - woff))) by lia.
  rewrite write_to_mem_in; [|exact Hnw|lia].
  f_equal. rewrite <- Hin by lia. f_equal. lia.
Qed.

Lemma mem_match_kwrite : ltac2:(tb__ "0|4|
S1dS5S1eA1S5eS5eS6eSdS1eS1eS15Q40M0A1M1S5S15Q8A1M2A1S6dS0G1S8G2A1F_;M3S60R8A1S60R9A1A3S0G3S5fR9A1S61S5fRaA1R4R3A3A3S2bVsegs;RdRcRbA4S0S7SacS1eS3eRaA1RdA3SbA3S0S8S1eA1SaaS1eReRaA3S9S1eR9A2A3S0S6dS16G0R8A2S86S16G0S21R10S2fRaA1A2A2R6A2A3S87S38R11RbA2R7A2S87S86R8S88ScG2R9A2A1A2S37R12RcA2A2S0S11S6dS6dA2S30R13RcA2S30R13RdA2A3S2cVsegs;R14R11RdA4S2bVsegs;R15S9fS1eR14R10ReA4R12A4F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fwoff;Fbs;Fbuf;Fo';Fo;Fk;Fn;Fms';Fms;Fobjs;Frho;").
Proof using .
  intros rho objs ms ms' n k o o' buf bs woff Hr Hm Hmm Hwf Hnth Hbuf Hlo Hhi Hrng Ho'.
  pose proof (mem_match_nth segs _ _ _ _ _ Hmm Hnth) as Hoh. pose proof (proj1 Hoh) as HB.
  unfold obj_lo_of, obj_hi_of in HB, Hlo, Hhi.
  destruct Hmm as (Hall & Hpd & Hfr).
  assert (Hnw : bv_unsigned buf + Z.of_nat (length bs) <= 2 ^ 64) by lia.
  split; [|split].
  - apply Forall_forall. intros o2 Hin2.
    destruct (In_list_set _ _ _ _ Hin2) as [-> | (m & Hne & Hm2)]; [exact Ho'|].
    pose proof (proj1 (Forall_forall _ _) Hall o2 (nth_error_In _ _ Hm2)) as Ho2.
    pose proof (proj1 (forallb_forall _ _) Hwf o2 (nth_error_In _ _ Hm2)) as Hwf2.
    pose proof (pairwise_disjoint_nth rho _ _ _ _ _ Hpd Hnth Hm2 ltac:(lia)) as D.
    pose proof (proj1 Ho2) as HB2.
    eapply (obj_holds_ext rho n ms ms' o2 Hr); [|exact Hwf2|exact Ho2].
    intros off Hoff. rewrite Hm. apply write_to_mem_out; [exact Hnw|].
    unfold obj_range, obj_lo_of, obj_hi_of, ranges_disjoint in D. cbn [fst snd] in D.
    unfold obj_lo_of, obj_hi_of in Hoff, HB2.
    rewrite u64_of_sum by lia. lia.
  - eapply pairwise_disjoint_set; [exact Hnth | exact Hrng | exact Hpd].
  - intros a Ha'. apply (proj1 (outside_all_set rho objs k o o' a Hnth Hrng)) in Ha'.
    rewrite Hm. rewrite write_to_mem_out; [apply Hfr; exact Ha' | exact Hnw |].
    pose proof (proj1 (Forall_forall _ _) Ha' o (nth_error_In _ _ Hnth)) as Ho. cbn zeta in Ho.
    unfold obj_range, obj_lo_of, obj_hi_of in Ho. cbn [fst snd] in Ho. lia.
Qed.

Lemma ro_clear_kwrite : ltac2:(tb__ "0|5|
S1dS5eS1eS15Q40M0A1M1S5S15Q8A1M2A1S6dG1S8G2A1M3F_;M4S45Vsegs;R6A2S2cVsegs;R8R7R6A4S0S7S32S36R7A1A1SbA3S0S6dS16G0R7A2S86S16G0S21RaS2fR8A1A2A2R5A2A3S87S38RbR9A2R6A2S87S86R7S88ScG2R8A2A1A2S37RcRaA2A2S0G4R7S61S5fRcA1RaR9A3A3G1S0S7S3fVsegs;R1A2SbA3S0G3RaR2A1S12G2A1A3F_;Fa;F_;F_;F_;F_;F_;F_;F_;Fmem;Fwoff;Fbs;Fbuf;Fo;Fms;Frho;").
Proof using .
  intros rho ms o buf bs woff mem Hroc Ho Hdw Hbuf Hlo Hhi Hmem a Hro. subst mem.
  destruct bs as [|b bs'].
  { cbn. apply Hroc. exact Hro. }
  assert (HB := proj1 Ho). unfold obj_lo_of, obj_hi_of in HB, Hlo, Hhi.
  assert (Hbuf' : buf = oaddr rho (ob_base o) woff).
  { unfold oaddr. rewrite <- Hbuf. symmetry. apply Z_to_bv_bv_unsigned. }
  set (ms' := {| ms_regs := ms_regs ms; ms_fregs := ms_fregs ms; ms_pc_val := ms_pc_val ms;
                 ms_svc_pending := None; ms_resv := ms_resv ms; ms_fcsr := ms_fcsr ms;
                 ms_mem := write_to_mem (ms_mem ms) buf (b :: bs'); ms_rom := ms_rom ms |}).
  change (ms_mem ms' a = None). revert a Hro.
  eapply (ro_clear_store segs rho ms ms' o woff (Z.of_nat (length (b :: bs'))));
    [exact Hroc | exact Ho | exact Hdw | exact Hlo | exact Hhi | cbn [length]; lia
    | rewrite Nat2Z.id; reflexivity | cbn [ms' ms_mem]; rewrite <- Hbuf'; reflexivity].
Qed.

Lemma smatch_after_kwrite : ltac2:(tb__ "0|7|
S1dS1fS5S70A1M0S5eS6fG0S6fS15Q40M1A1M2SdS20S20S20S6dS6dS5S24A1S39S6eG2S5S15Q8M3A1M4A1S6dS79R14R13S6G0S18R12S19R11R10A2A4A3S91RfA1S0S8S1eA1SaaS1eS23R15A1ReA3S9S1eS29RdRcRbR8R7A5A2A3S0S7S32R8A1SbA3S0S6dS27R18ReA2RcA3S0S6dS27R19ReA2RcA3S0S6dS16G1R9A2S86S16G1S21R1aR11A2A2R7A2A3S87RfR8A2S87S86R9S88ScG4RaA2A1A2RfA2S0S6dS88ScG4S25R1dRdA2A2A1S8aR10R11A2A3SdSb5R1ScG4RdA2A2S0G4SadG4Sb6S8bS8aRdR14A2A1R2A2S25R20R10A2S17G3Z0A2M5A4SadG4R2ReG5A4A3F_;Fj;S6dS1S87R14R1A2S89R1R13A2A2S2S1S87ReR2A2S89R2S86ReS88ScG4RfA2A1A2A2A2A1S0S8G4A1S54R1fS17G1S86S16G1S21R22R19A2A2R3A2A2A2S9G4SadG4S8bS8aR3R16A2A1S25R22R12A2G5A4A2A3F_;F_;Foff;S22Vsegs;S9cR20S28R1fA1M6R19A3S7bR1fS2dG6A1S9fS1eS23R1fA1R18S29R17R16R15SfS24A1S2eR10A1A5A4Sb2G6A1A4S6G0S18R1bS19Sa0R1dR19S61S5fR1dA1RfReA3A3R1aA2A4A4F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fwoff;Fbs;Fbuf;Fl;Fd;Fcells;Fhi;Flo;Fehi;Felo;Fbase;Fk;Fr;Fmd';Ftr';Fmd;Fms;Ftr;FS;Frho;").
Proof using .
  intros rho S tr ms md tr' md' r k base elo ehi lo hi cells d l buf bs woff
         Hsp Hh' Hnth Hdw Helo Hehi Hbuf Hlo Hhi Hlen Hin Hout.
  set (nx := ss_next S). set (rho' := rho_set_rw rho nx r).
  assert (Hag : agree_below nx rho rho') by (apply agree_below_set_rw; lia).
  pose proof (smatch_pending_agree rho rho' S tr ms md Hag Hsp) as Hsp'.
  pose proof (smatch_pending_swf _ _ _ _ _ Hsp) as Hwf.
  pose proof (swf_objs S Hwf) as Hobjwf.
  pose proof (swf_obj_nth _ _ _ Hwf Hnth) as Howf.
  pose proof Howf as Howf0. unfold obj_wf in Howf0. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt] in Howf0.
  apply andb_prop in Howf0 as [Howf0 _]. apply andb_prop in Howf0 as [Howf0 _]. apply andb_prop in Howf0 as [Howf0 Hbhi].
  apply andb_prop in Howf0 as [Hbb Hblo].
  assert (Hbase : eval rho' base = eval rho base).
  { symmetry. eapply eval_agree; [exact Hag| exact Hbb]. }
  assert (Helo' : soff rho' elo = lo).
  { unfold soff. rewrite <- (eval_agree nx rho rho' elo Hag Hblo). exact Helo. }
  assert (Hehi' : soff rho' ehi = hi).
  { unfold soff. rewrite <- (eval_agree nx rho rho' ehi Hag Hbhi). exact Hehi. }
  pose proof (smatch_pending_mem _ _ _ _ _ Hsp') as Hmm'.
  pose proof (mem_match_nth segs _ _ _ _ _ Hmm' Hnth) as Hoh'.
  eapply smatch_after_sys; [exact Hsp' | exact Hh' | lia | | | | |].
  - cbn. apply Pos.ltb_lt. lia.
  - cbn. rewrite Pos.eqb_refl. reflexivity.
  - apply forallb_list_set.
    + apply forallb_forall. intros o Hino. eapply obj_wf_mono; [|exact (proj1 (forallb_forall _ _) Hobjwf o Hino)]. lia.
    + pose proof (obj_wf_mono nx (Pos.succ nx) _ ltac:(lia) Howf) as W.
      unfold obj_wf in W |- *. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt dflt_wf forallb] in *.
      apply andb_prop in W as [W _]. apply andb_prop in W as [W _]. rewrite W. reflexivity.
  - eapply (mem_match_kwrite rho' (ss_objs S) ms _ nx k (mkObj base elo ehi cells d) _ buf bs woff);
      [reflexivity | reflexivity | exact Hmm' | exact Hobjwf | exact Hnth
      | cbn [ob_base]; rewrite Hbase; exact Hbuf
      | unfold obj_lo_of; cbn [ob_lo]; rewrite Helo'; exact Hlo
      | unfold obj_hi_of; cbn [ob_hi]; rewrite Hehi'; exact Hhi | reflexivity | ].
    eapply (obj_holds_kwrite rho' ms _ base elo ehi lo hi cells d l buf bs woff);
      [exact Hoh' | exact Hdw | exact Helo' | exact Hehi' | reflexivity | reflexivity | rewrite Hbase; exact Hbuf | exact Hlo | exact Hhi
      | cbn; exact Hlen | cbn; exact Hin | rewrite Hbase; cbn [rl rho' rho_set_rw]; exact Hout].
  - pose proof (smatch_pending_mem _ _ _ _ _ Hsp) as Hmm.
    eapply (ro_clear_kwrite rho ms (mkObj base elo ehi cells d) buf bs woff);
      [exact (smatch_pending_ro_clear _ _ _ _ _ Hsp) | exact (mem_match_nth segs _ _ _ _ _ Hmm Hnth)
      | exact Hdw
      | cbn [ob_base]; exact Hbuf
      | unfold obj_lo_of; cbn [ob_lo]; rewrite Helo; exact Hlo
      | unfold obj_hi_of; cbn [ob_hi]; rewrite Hehi; exact Hhi | reflexivity].
Qed.

Lemma smatch_after_kwrite_zero : ltac2:(tb__ "0|8|
S1dS1fS5S70A1M0S5eS6fG0S6fS15Q40M1A1M2SdS20S20S20S6dS6dS6eG2S5S15Q8M3A1M4A1M5S79R11R10S6G0S18RfS19ReRdA2A4A3S91RcA1S0S8S1eA1SaaS1eS23R12A1RbA3S9S1eS29RaR9R8SfS24A1M6S42A5A2A3S0S6dS27R14RaA2R8A3S0S6dS27R15RaA2R8A3S0S6dS16G1R7A2S86S16G1S21R16RdA2A2RaA2A3S87S88ScG4R7A2A1S8aRaRbA2A2S0G5S25R18RaA2S10G4R8SafG4S17G3Z0A2Sb7S8bS8aRbRcA2A1ScG4R8A2A2A3A3A3S22Vsegs;S9cR19S28R18A1M7R12A3S7bR18S2dG7A1S9fS1eS23R18A1R11S29R10RfReG6S2eRbA1A5A4Sb2G7A1A4S6G0S18R14S19Sa0R16R12S61S5fR16A1RaR9A3A3R13A2A4A4F_;F_;F_;F_;F_;F_;F_;F_;Fbs;Fbuf;Fl;Fhi;Flo;Fehi;Felo;Fbase;Fk;Fr;Fmd';Ftr';Fmd;Fms;Ftr;FS;Frho;").
Proof using .
  intros rho S tr ms md tr' md' r k base elo ehi lo hi l buf bs Hsp Hh' Hnth Helo Hehi Hbuf Hlenle Hl.
  pose proof (mem_match_nth segs _ _ _ _ _ (smatch_pending_mem _ _ _ _ _ Hsp) Hnth) as Hoh.
  unfold obj_holds, obj_lo_of, obj_hi_of in Hoh. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt] in Hoh.
  rewrite Helo, Hehi in Hoh. destruct Hoh as (HB & _ & _ & Hd & _).
  eapply smatch_after_kwrite; [exact Hsp | exact Hh' | exact Hnth | reflexivity | exact Helo | exact Hehi | exact Hbuf | lia | lia | | |].
  - rewrite Hl, length_app, repeat_length. lia.
  - intros j Hj. rewrite Hl, Z.sub_diag. cbn [Z.to_nat Nat.add]. apply app_nth1. exact Hj.
  - intros off Hoff Hno. rewrite (Hd off Hoff ltac:(intro HC; inversion HC)). f_equal. rewrite Hl.
    rewrite app_nth2 by lia. symmetry. apply nth_repeat_lt. lia.
Qed.

Lemma smatch_after_kwrite_full : ltac2:(tb__ "0|6|
S1dS1fS5S70A1M0S5eS6fG0S6fS15Q40M1A1M2SdS20S20S20S6dS6dS5S24A1S39S6eG2S5S15Q8A1M3A1M4S79R13R12S6G0S18R11S19R10RfA2A4A3S91ReA1S0S8S1eA1SaaS1eS23R14A1RdA3S9S1eS29RcRbRaR7R6A5A2A3S0S7S32R7A1SbA3S0S6dS27R17RdA2RbA3S0S6dS27R18RdA2RbA3S0S6dS16G1R8A2S86S16G1S21R19R10A2A2RdA2A3S0S6dS88ScG3R8A2A1S8aRdReA2A3S0G4S25R1bRbA2R9A3S22Vsegs;S9cR1cS28R1bA1M5R15A3S7bR1bS2dG5A1S9fS1eS23R1bA1R14S29R13R12R11SfS24A1S2eRcA1A5A4Sb2G5A1A4S6G0S18R17S19Sa0R19R15S61S5fR19A1RbRaA3A3R16A2A4A4F_;F_;F_;F_;F_;F_;F_;F_;F_;Fbs;Fbuf;Fl;Fd;Fcells;Fhi;Flo;Fehi;Felo;Fbase;Fk;Fr;Fmd';Ftr';Fmd;Fms;Ftr;FS;Frho;").
Proof using .
  intros rho S tr ms md tr' md' r k base elo ehi lo hi cells d l buf bs Hsp Hh' Hnth Hdw Helo Hehi Hbuf Hlen Hl.
  eapply smatch_after_kwrite; [exact Hsp | exact Hh' | exact Hnth | exact Hdw | exact Helo | exact Hehi | exact Hbuf | lia | lia | | |].
  - rewrite Hl. exact Hlen.
  - intros j Hj. rewrite Hl, Z.sub_diag. reflexivity.
  - intros off Hoff Hno. exfalso. lia.
Qed.

Lemma smatch_after_kwrite_list : ltac2:(tb__ "0|9|
S1dS1fS5S70A1M0S5eS6fG0S6fS15Q40M1A1M2SdS20S20S20S6dS6dS6eS6eG2S5S15Q8A1M3A1M4S6dS79R13R12S6G0S18R11S19R10RfA2A4A3S91ReA1S0S8S1eA1SaaS1eS23R14A1RdA3S9S1eS29RcRbRaSfS24A1M5S2eR7A1A5A2A3S0S6dS27R16RcA2RaA3S0S6dS27R17RcA2RaA3S0S6dS16G1R8A2S86S16G1S21R18RfA2A2R6A2A3S87RdR7A2S87S86R8S88ScG3R9A2A1A2RdA2S0G4S25R1bRcA2S10G3Sb0G3S8bS8aR9RfA2A1M6S25R1bRdA2M7A3S10G3RaSb1G3Sb6G6ScG3RaA2A2G7A3A3A3A3S22Vsegs;S9cR1cS28R1bA1M8R15A3S7bR1bS2dG8A1S9fS1eS23R1bA1R14S29R13R12R11G5S2eRdA1A5A4Sb2G8A1A4S6G0S18R17S19Sa0R19R15S61S5fR19A1RcRbA3A3R16A2A4A4F_;F_;F_;F_;F_;F_;F_;F_;F_;Fwoff;Fbs;Fbuf;Fl;Fl0;Fhi;Flo;Fehi;Felo;Fbase;Fk;Fr;Fmd';Ftr';Fmd;Fms;Ftr;FS;Frho;").
Proof using .
  intros rho S tr ms md tr' md' r k base elo ehi lo hi l0 l buf bs woff Hsp Hh' Hnth Helo Hehi Hbuf Hlo Hhi Hl.
  pose proof (mem_match_nth segs _ _ _ _ _ (smatch_pending_mem _ _ _ _ _ Hsp) Hnth) as Hoh.
  unfold obj_holds, obj_lo_of, obj_hi_of in Hoh. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt] in Hoh.
  rewrite Helo, Hehi in Hoh. destruct Hoh as (HB & _ & _ & Hd & Hdl). cbn [dflt_inv] in Hdl.
  assert (Hlen1 : length (firstn (Z.to_nat (woff - lo)) (rl rho l0)) = Z.to_nat (woff - lo)).
  { apply firstn_length_le. lia. }
  eapply smatch_after_kwrite; [exact Hsp | exact Hh' | exact Hnth | reflexivity | exact Helo | exact Hehi | exact Hbuf | exact Hlo | exact Hhi | | |].
  - rewrite Hl, !length_app, Hlen1, length_skipn. lia.
  - intros j Hj. rewrite Hl. rewrite <- Hlen1 at 1. rewrite app_nth2_plus. apply app_nth1. exact Hj.
  - intros off Hoff Hno. rewrite (Hd off Hoff ltac:(intro HC; inversion HC)). cbn [dflt_holds]. f_equal. rewrite Hl.
    destruct (Z_lt_le_dec off woff) as [Hlt|Hge].
    + rewrite app_nth1 by (rewrite Hlen1; lia). rewrite nth_firstn.
      destruct (Nat.ltb_spec (Z.to_nat (off - lo)) (Z.to_nat (woff - lo))); [reflexivity | exfalso; lia].
    + rewrite app_nth2 by (rewrite Hlen1; lia). rewrite Hlen1.
      rewrite app_nth2 by lia. rewrite nth_skipn. f_equal. lia.
Qed.

Fixpoint sv_has_rl (l : positive) (e : sv) : bool :=
  match e with
  | SLBytes l' i _ => Pos.eqb l l' || sv_has_rl l i
  | SAlu _ a b | SAluW _ a b | SMd _ a b | SMdW _ a b => sv_has_rl l a || sv_has_rl l b
  | SExt _ _ a => sv_has_rl l a
  | _ => false
  end.

Fixpoint sprop_has_rl (l : positive) (p : sprop) : bool :=
  match p with
  | SPBranch _ a b | SPUlt a b | SPUle a b | SPEq a b => sv_has_rl l a || sv_has_rl l b
  | SPNot p => sprop_has_rl l p
  | _ => false
  end.

Definition dflt_has_rl (l : positive) (d : odefault) : bool := ltac2:(tb__ "0|1|
S39S7Ld;Vd;SaSaSaS6eSb3Vl;R1A2Ll';M0G0S6dS20S5S11S6dS6dA2A1S5S47A1SeS7aVl;R3A2Sa9S47S47S7aVl;S5dR1A1A2Lt;R1A3A2Ltmpl;Lflds;Lcnt;Lesz;X39x6").

Definition obj_has_rl (l : positive) (o : sobj) : bool := ltac2:(tb__ "0|0|
SeSeSeSeS7aVl;S2fVo;A1A2S7aVl;S51Vo;A1A2A2S7aVl;S50Vo;A1A2A2Sa9S24S24SeS7aVl;S43R1A1A2S7aVl;S49R1A1A2A2Lc;S4fVo;A1A3A2S81Vl;S36Vo;A1A2A2").

Definition state_has_rl (l : positive) (S : sstate) : bool := ltac2:(tb__ "0|2|
SeSeSeSeSeSa9S20S7aVl;A1M0S5aVS;A1A3Sa9S20G0S59VS;A1A3A2S58S7Lx;S40VS;A1SaS20S7aVl;R1A2Lv;M1X58x2A2S8S20A1S7Lx;S41VS;A1G1SaX8x2A2Sa9S1eS7cVl;A1S23VS;A1A3A2Sa9S3bS82Vl;A1S3cVS;A1A3A2").

Lemma eval_set_rl : ltac2:(tb__ "0|0|
S1dS6eS5S15Q8A1A1S20S0S7S7aR3R1A2SaA3S0S15Q40A1S21S9bR5R4R3A3R2A2S21R5R2A2A3F_;Fe;FL;Fl;Frho;").
Proof using .
  intros rho l L e. induction e; cbn; intros H;
    try (apply Bool.orb_false_iff in H as [H1 H2]; rewrite (IHe1 H1), (IHe2 H2)); try reflexivity.
  - rewrite (IHe H). reflexivity.
  - apply Bool.orb_false_iff in H as [H1 H2]. rewrite (IHe H2). cbn.
    destruct (Pos.eqb_spec l0 l) as [E|E]; [subst; rewrite Pos.eqb_refl in H1; discriminate|]. reflexivity.
Qed.

Lemma holds_set_rl : ltac2:(tb__ "0|0|
S1dS6eS5S15Q8A1A1S3bS0S7S82R3R1A2SaA3S4S35S9bR5R4R3A3R2A2S35R5R2A2A2F_;Fp;FL;Fl;Frho;").
Proof using .
  intros rho l L p. induction p; cbn; intros H;
    try (apply Bool.orb_false_iff in H as [H1 H2]; rewrite !eval_set_rl by assumption); try tauto.
  all: specialize (IHp H); tauto.
Qed.

Lemma existsb_false_forall : forall {A} (f : A -> bool) l x,
  existsb f l = false -> In x l -> f x = false.
Proof using .
  intros A f l x H Hin. destruct (f x) eqn:E; [|reflexivity].
  assert (existsb f l = true) by (apply existsb_exists; eauto). congruence.
Qed.

Lemma nth_has_rl_false : ltac2:(tb__ "0|0|
S6eS5S20A1SdS0S7Sa9S20S7aR3A1R2A3SaA3S0S7S7aR4SadS20R2R3S34Z0A1A4A2SaA3F_;Fn;Fregs;Fl;").
Proof using .
  intros l regs n H. destruct (nth_in_or_default n regs (SLit 0)) as [Hin | ->]; [|reflexivity].
  eapply existsb_false_forall; eauto.
Qed.

Lemma obj_has_rl_split : ltac2:(tb__ "0|0|
S6eS1eS0S7S7cR2R1A2SaA3S1S0S7S7aR3S2fR2A1A2SaA3S1S0S7S7aR3S51R2A1A2SaA3S1S0S7S7aR3S50R2A1A2SaA3S1S24SabS24R1S4fR3A1A3S1S0S7S7aR5S43R2A1A2SaA3S0S7S7aR5S49R2A1A2SaA3A2F_;Fc;S0S7S81R3S36R2A1A2SaA3A2A2A2A2F_;Fo;Fl;").
Proof using .
  intros l o Hno. unfold obj_has_rl in Hno.
  apply Bool.orb_false_iff in Hno as [Hno Hdf]. apply Bool.orb_false_iff in Hno as [Hno Hcells].
  apply Bool.orb_false_iff in Hno as [Hno Hhi]. apply Bool.orb_false_iff in Hno as [Hbase Hlo].
  repeat split; try assumption.
  - apply (existsb_false_forall _ _ c Hcells) in H. apply Bool.orb_false_iff in H as [H _]. exact H.
  - apply (existsb_false_forall _ _ c Hcells) in H. apply Bool.orb_false_iff in H as [_ H]. exact H.
Qed.

Lemma soff_set_rl : ltac2:(tb__ "0|0|
S1dS6eS5S15Q8A1A1S20S0S7S7aR3R1A2SaA3S0S6dS27S9bR5R4R3A3R2A2S27R5R2A2A3F_;Fe;FL;Fl;Frho;").
Proof using . intros. unfold soff. rewrite eval_set_rl by assumption. reflexivity. Qed.

Lemma covered_set_rl : ltac2:(tb__ "0|0|
S1dS6eS5S15Q8A1A1S5S24A1S6dS24SabS24R1R3A3S0S7S7aR6S43R2A1A2SaA3F_;Fc;S4S4aS9bR6R5R4A3R3R2A3S4aR6R3R2A3A2F_;Foff;Fcells;FL;Fl;Frho;").
Proof using .
  intros rho l L cells off Hc. unfold covered. rewrite !Exists_exists.
  split; intros (c & Hin & Hic); exists c; split; [exact Hin| |exact Hin|];
    unfold in_cell in *; rewrite soff_set_rl in * by (apply Hc; exact Hin); exact Hic.
Qed.

Lemma obj_holds_set_rl : ltac2:(tb__ "0|0|
S1dS6eS5S15Q8A1A1S5eS1eS0S7S7cR4R1A2SaA3S2cVsegs;R6R3R2A4S2cVsegs;S9bR7R6R5A3R4R3A4F_;F_;Fo;Fms;FL;Fl;Frho;").
Proof using .
  intros rho l L ms o Hno (Hb & Hw & Hc & Hd & Hdl).
  destruct (obj_has_rl_split l o Hno) as (Hbase & Hlo & Hhi & Hcells & Hdf).
  unfold obj_holds, obj_lo_of, obj_hi_of in *. rewrite (eval_set_rl rho l L _ Hbase).
  rewrite (soff_set_rl rho l L _ Hlo), (soff_set_rl rho l L _ Hhi).
  split; [exact Hb|]. split; [exact Hw|]. split; [|split].
  - apply Forall_forall. intros c Hin. pose proof (proj1 (Forall_forall _ _) Hc c Hin) as Hch.
    destruct (Hcells c Hin) as [Hco Hcv].
    unfold cell_holds, oaddr in *. rewrite (eval_set_rl rho l L _ Hbase).
    rewrite (soff_set_rl rho l L _ Hco). rewrite (eval_set_rl rho l L (c_val c) Hcv).
    exact Hch.
  - intros off Hoff Hcov.
    specialize (Hd off Hoff ltac:(intro HC; apply Hcov; apply (covered_set_rl rho l L _ off (fun c Hin => proj1 (Hcells c Hin))); exact HC)).
    destruct (ob_dflt o) as [| | |l'|l'|esz cnt flds tmpl]; cbn in *; try exact Hd;
    (destruct (Pos.eqb_spec l' l) as [E|E]; [subst; rewrite Pos.eqb_refl in Hdf; discriminate|]; exact Hd).
  - destruct (ob_dflt o) as [| | |l'|l'|esz cnt flds tmpl]; cbn in Hdl, Hdf |- *; try exact Hdl;
    try (destruct (Pos.eqb_spec l' l) as [E|E]; [subst; rewrite Pos.eqb_refl in Hdf; discriminate|]; exact Hdl).
    apply Bool.orb_false_iff in Hdf as [Hcnt Htm].
    rewrite (eval_set_rl rho l L cnt Hcnt).
    destruct Hdl as (Q1 & Q2 & Q3 & Q4). split; [exact Q1|]. split; [exact Q2|]. split; [exact Q3|].
    intros k Hk. apply (elem_holds_exprs rho); [|apply Q4; exact Hk].
    apply Forall_forall. intros t Hin. symmetry. apply eval_set_rl.
    apply (existsb_false_forall _ _ t Htm). exact Hin.
Qed.

Lemma obj_range_set_rl : ltac2:(tb__ "0|0|
S1dS6eS5S15Q8A1A1S1eS0S7S7cR3R1A2SaA3S0S11S6dS6dA2S30S9bR5R4R3A3R2A2S30R5R2A2A3F_;Fo;FL;Fl;Frho;").
Proof using .
  intros rho l L o Hno. destruct (obj_has_rl_split l o Hno) as (Hbase & Hlo & Hhi & _ & _).
  unfold obj_range, obj_lo_of, obj_hi_of. rewrite (eval_set_rl rho l L _ Hbase).
  rewrite (soff_set_rl rho l L _ Hlo), (soff_set_rl rho l L _ Hhi). reflexivity.
Qed.

Lemma mem_match_set_rl : ltac2:(tb__ "0|0|
S1dS6eS5S15Q8A1A1S5S1eA1S5eS0S7Sa9S1eS7cR4A1R2A3SaA3S2bVsegs;R6R3R2A4S2bVsegs;S9bR7R6R5A3R4R3A4F_;F_;Fms;Fobjs;FL;Fl;Frho;").
Proof using .
  intros rho l L objs ms Hno (Hall & Hpd & Hfr). split; [|split].
  - apply Forall_forall. intros o Hin. apply obj_holds_set_rl; [eapply existsb_false_forall; eauto|].
    exact (proj1 (Forall_forall _ _) Hall o Hin).
  - apply pairwise_disjoint_pdr. apply pairwise_disjoint_pdr in Hpd.
    rewrite (map_ext_in _ (obj_range rho)); [exact Hpd|].
    intros o Hin. apply obj_range_set_rl. eapply existsb_false_forall; eauto.
  - intros a Ha. cbn [rm rho_set_rl]. apply Hfr.
    apply outside_all_ranges. apply outside_all_ranges in Ha.
    rewrite (map_ext_in (obj_range (rho_set_rl rho l L)) (obj_range rho)) in Ha; [exact Ha|].
    intros o Hin. apply obj_range_set_rl. eapply existsb_false_forall; eauto.
Qed.

Definition vpart (rho : valuation) (S : sstate) (ms : machine_state) : Prop := ltac2:(tb__ "0|0|
S1S3aVrho;VS;Vms;A3S1S4dVrho;VS;Vms;A3S1S4bVrho;S40VS;A1Vms;A3S1S56Vrho;S41VS;A1Vms;A3S1S2bVsegs;Vrho;S23VS;A1Vms;A4SaeS3bS35Vrho;A1S3cVS;A1A3A2A2A2A2A2").

Lemma vpart_set_rl : ltac2:(tb__ "0|0|
S1dS6eS5S15Q8A1A1S1fS5eS0S7S80R4R2A2SaA3S83R6R3R2A3S83S9bR7R6R5A3R4R3A3F_;F_;Fms;FS;FL;Fl;Frho;").
Proof using .
  intros rho l L S ms Hno (Hregs & Hfregs & Hfcsr & Hresv & Hmem & Hfacts).
  unfold state_has_rl in Hno.
  apply Bool.orb_false_iff in Hno as [Hno Hfa]. apply Bool.orb_false_iff in Hno as [Hno Hob].
  apply Bool.orb_false_iff in Hno as [Hno Hrs]. apply Bool.orb_false_iff in Hno as [Hno Hfc].
  apply Bool.orb_false_iff in Hno as [Hrg Hfr].
  split.
  { intros r Hr. rewrite (Hregs r Hr). symmetry. apply eval_set_rl.
    unfold reg_sv. destruct (bv_unsigned r =? 0); [reflexivity|]. apply nth_has_rl_false. exact Hrg. }
  split.
  { intros r. rewrite (Hfregs r). symmetry. apply eval_set_rl. unfold freg_sv. apply nth_has_rl_false. exact Hfr. }
  split.
  { unfold fcsr_match in *. destruct (ss_fcsr S); [exact Hfcsr|]. rewrite eval_set_rl by exact Hfc. exact Hfcsr. }
  split.
  { unfold resv_match in *. destruct (ss_resv S); [|exact Hresv]. destruct (ms_resv ms); [|exact Hresv].
    rewrite eval_set_rl by exact Hrs. exact Hresv. }
  split; [apply mem_match_set_rl; assumption|].
  apply Forall_forall. intros p Hin. apply holds_set_rl; [eapply existsb_false_forall; eauto|].
  exact (proj1 (Forall_forall _ _) Hfacts p Hin).
Qed.

Lemma smatch_set_rl : ltac2:(tb__ "0|0|
S1dS6eS5S15Q8A1A1S1fS11S5S70A1S18A2S0S7S80R4R2A2SaA3S22Vsegs;R6R3R2A4S22Vsegs;S9bR7R6R5A3R4R3A4F_;F_;Fw;FS;FL;Fl;Frho;").
Proof using .
  intros rho l L S [tr [ms md]] Hno Hsm.
  pose proof Hsm as (Hwf & Hpc & Hpend & Hhalt & Hrom & Hroc & Hv).
  change (vpart rho S ms) in Hv.
  unfold smatch. cbn [fst snd cfg_ms cfg_model].
  split; [exact Hwf|]. split; [exact Hpc|]. split; [exact Hpend|]. split; [exact Hhalt|].
  split; [exact Hrom|]. split; [exact Hroc|].
  change (vpart (rho_set_rl rho l L) S ms). apply vpart_set_rl; assumption.
Qed.

Lemma smatch_pending_set_rl : ltac2:(tb__ "0|1|
S1dS6eS5S15Q8A1A1S1fS5S70A1M0S5eS6fS0S7S80R6R4A2SaA3S79R8R5S6G0S18R4S19R3R2A2A4A3S79S9bR9R8R7A3R6S6G0S18R5S19R4R3A2A4A3F_;F_;Fmd;Fms;Ftr;FS;FL;Fl;Frho;").
Proof using .
  intros rho l L S tr ms md Hno Hsp.
  pose proof Hsp as (Hwf & Hpc & Hpend & Hhalt & Hrom & Hroc & Hv).
  change (vpart rho S ms) in Hv. cbn [fst snd cfg_ms cfg_model] in Hpc, Hpend, Hhalt, Hrom, Hroc.
  unfold state_has_rl in Hno. pose proof Hno as Hno0.
  apply Bool.orb_false_iff in Hno as [Hno _]. apply Bool.orb_false_iff in Hno as [Hno _].
  apply Bool.orb_false_iff in Hno as [Hno _]. apply Bool.orb_false_iff in Hno as [Hno _].
  apply Bool.orb_false_iff in Hno as [Hrg _].
  unfold smatch_pending. cbn [fst snd cfg_ms cfg_model].
  split; [exact Hwf|]. split; [exact Hpc|].
  split.
  { rewrite Hpend. f_equal. symmetry. apply eval_set_rl. unfold reg_sv. cbn [Z.eqb].
    apply nth_has_rl_false. exact Hrg. }
  split; [exact Hhalt|]. split; [exact Hrom|]. split; [exact Hroc|].
  change (vpart (rho_set_rl rho l L) S ms). apply vpart_set_rl; assumption.
Qed.

Lemma smatch_after_kwrite_zero_fresh : ltac2:(tb__ "0|8|
S1dS1fS5S70A1M0S5eS6fG0S6fS15Q40M1A1M2SdS20S20S20S6dS6dS6eG2S5S15Q8M3A1M4A1M5S79R11R10S6G0S18RfS19ReRdA2A4A3S91RcA1S0S8S1eA1SaaS1eS23R12A1RbA3S9S1eS29RaR9R8SfS24A1M6S42A5A2A3S0S6dS27R14RaA2R8A3S0S6dS27R15RaA2R8A3S0S6dS16G1R7A2S86S16G1S21R16RdA2A2RaA2A3S87S88ScG4R7A2A1S8aRaRbA2A2S0S7S80RaR17A2SaA3S10G4R9SafG4S17G3Z0A2Sb7S8bS8aRcRdA2A1ScG4R9A2A2A3A3G5S22Vsegs;S9cS9bR1aRcR1A3S28R19A1M7R13A3S7bR19S2dG7A1S9fS1eS23R19A1R12S29R11R10RfG6S2eRcA1A5A4Sb2G7A1A4S6G0S18R15S19Sa0R17R13S61S5fR17A1RbRaA3A3R14A2A4A4TL;F_;F_;F_;F_;F_;F_;F_;F_;Fbs;Fbuf;Fl;Fhi;Flo;Fehi;Felo;Fbase;Fk;Fr;Fmd';Ftr';Fmd;Fms;Ftr;FS;Frho;").
Proof using .
  intros rho S tr ms md tr' md' r k base elo ehi lo hi l buf bs Hsp Hh' Hnth Helo Hehi Hbuf Hlenle Hno L.
  pose proof (smatch_pending_set_rl rho l L S tr ms md Hno Hsp) as Hsp'.
  pose proof Hno as Hno0. unfold state_has_rl in Hno.
  apply Bool.orb_false_iff in Hno as [Hno _]. apply Bool.orb_false_iff in Hno as [_ Hob].
  pose proof (existsb_false_forall _ _ _ Hob (nth_error_In _ _ Hnth)) as Ho.
  destruct (obj_has_rl_split l _ Ho) as (Hb0 & Hlo0 & Hhi0 & _ & _). cbn [ob_base ob_lo ob_hi] in Hb0, Hlo0, Hhi0.
  eapply smatch_after_kwrite_zero; [exact Hsp' | exact Hh' | exact Hnth
    | rewrite soff_set_rl by exact Hlo0; exact Helo
    | rewrite soff_set_rl by exact Hhi0; exact Hehi
    | | exact Hlenle | apply rho_set_rl_at].
  rewrite eval_set_rl; [exact Hbuf| exact Hb0].
Qed.

Lemma read_bytes_aux_rd_bytes : ltac2:(tb__ "0|0|
S5eS15Q40A1SdS0S8S5S15Q8A1A1A1S72S63R3A1R2R1A3S55R3R2R1A3A3Fk;Fa;Fms;").
Proof using .
  intros ms a k. revert a. induction k as [|k IH]; intros a; [reflexivity|].
  cbn [read_bytes_aux rd_bytes]. unfold rd. rewrite IH.
  destruct (ms_read_byte ms a); [|reflexivity]. destruct (rd_bytes ms (a + 1)%bv k); reflexivity.
Qed.

Lemma read_bytes_map_rd_bytes : ltac2:(tb__ "0|2|
S5eS15Q40M0A1M1G1S0S8S5S15Q8A1A1A1S73S63R3A1R2R1A3S55R3R2S8bS16G0R1A2A1A3A3Flen;Fa;Fms;").
Proof using . intros. rewrite read_bytes_map_eq; unfold word_to_nat. apply read_bytes_aux_rd_bytes. Qed.

Lemma word_to_nat_of_Z : ltac2:(tb__ "0|0|
S6dS1S87Z0R1A2S89R1S8cZ2Z40A2A2A2S0SdSb9S17Q40R2A2A1S8bR2A1A3F_;Fk;").
Proof using . intros k Hk. unfold word_to_nat. rewrite u64_of_sum by exact Hk. reflexivity. Qed.

Lemma Z_to_bv64_add1 : forall x, (Z_to_bv 64 x + 1)%bv = Z_to_bv 64 (x + 1).
Proof using .
  intros x. apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned.
  unfold bv_wrap. rewrite two64. change (bv_unsigned (1%bv : bv 64)) with 1.
  rewrite Zplus_mod_idemp_l. reflexivity.
Qed.

Lemma read_bytes_aux_wview_obj : ltac2:(tb__ "0|2|
S1dS5eS1eS6dSdS2cVsegs;R5R4R3A4S0S7S32S36R4A1A1SbA3S87S38R7R5A2R4A2S87S86R5S88R4A1A2S37R8R6A2A2S2S0S8S5S15Q8A1A1M0A1S72S6cVsegs;S5fR8A1A2S17Q40M1S86S16G1S21R9S2fR7A1A2A2R6A2A2R5A3S12G0A1A3A1F_;F_;F_;F_;Fk;Foff;Fo;Fms;Frho;").
Proof using .
  intros rho ms o off k (Hb & Hw & _) Hdw Hlo. revert off Hlo.
  induction k as [|k IH]; intros off Hlo Hhi; [discriminate|].
  cbn [read_bytes_aux]. rewrite Nat2Z.inj_succ in Hhi.
  pose proof (Hw off ltac:(lia) Hdw) as H1.
  destruct (wview segs (ms_mem ms) (Z_to_bv 64 (bv_unsigned (eval rho (ob_base o)) + off))) as [b|]; [|exfalso; exact (H1 eq_refl)].
  rewrite Z_to_bv64_add1. rewrite <- Z.add_assoc.
  specialize (IH (off + 1) ltac:(lia) ltac:(lia)).
  destruct (read_bytes_aux _ _ k); [discriminate | exact IH].
Qed.

Lemma writable_range_obj : ltac2:(tb__ "0|3|
S1dS5eS1eS15Q40M0A1M1G1S6dS2cVsegs;R6R5R4A4S0S7S32S36R5A1A1SbA3S0S6dS16G0R5A2S86S16G0S21R8S2fR6A1A2A2R3A2A3S87S38R9R7A2R4A2S87S86R5S16G0R6A2A2S37RaR8A2A2S2S0S8S5S15Q8A1A1M2A1S73S6aVsegs;RaA2R8R7A3S12G2A1A3A1F_;F_;F_;F_;F_;Foff;Flen;Fbuf;Fo;Fms;Frho;").
Proof using .
  intros rho ms o buf len off Ho Hdw Hbuf Hlo Hhi. pose proof (urange len) as Hl.
  rewrite read_bytes_map_eq; unfold ms_writable_byte, word_to_nat.
  replace buf with (Z_to_bv 64 (bv_unsigned (eval rho (ob_base o)) + off))
    by (rewrite <- Hbuf; apply Z_to_bv_bv_unsigned).
  change (fun addr => wview segs (ms_mem ms) addr) with (wview segs (ms_mem ms)).
  apply (read_bytes_aux_wview_obj rho ms o off); [exact Ho | exact Hdw | exact Hlo | rewrite Z2Nat.id by lia; exact Hhi].
Qed.

Lemma triple1_pending : ltac2:(tb__ "0|1|
S11S5S70A1M0S18A2OFx;G0S6fOFx0;Fx;S1fS1dS95G0S5eS6fS79R5R6S6G0S18R3S19R2R1A2A4A3R8R4R2A2S1RaS6G0S18R5S19R4R3A2A4A1S90S92Vsegs;S6G0S18R6S19R5R4A2A4R1A3R8R2A1F_;Fw';A2F_;F_;Fmd;Fms;Ftr;S93Vsegs;R6S7dR5R4R3A3R2A4F_;FQ;Frho;FS;FK;Fok;").
Proof using .
  intros ok K S rho Q H. apply triple1_step.
  intros [tr [ms md]] [Hsp Hk]. cbn [w_tr w_cfg fst snd cfg_model] in Hk. exact (H tr ms md Hsp Hk).
Qed.

Lemma etriple_pending : ltac2:(tb__ "0|1|
S5S70A1M0S6fOFx0;Fx;S1fS1dS90OF_;G0S5eS6fS79R5R6S6G0S18R3S19R2R1A2A4A3R8R4R2A2S3S90S90S1S92Vsegs;S6G0S18R6S19R5R4A2A4R1A3R7R1A1A2Lw';A2F_;F_;Fmd;Fms;Ftr;S94Vsegs;S7dR5R4R3A3R2A3F_;FQ;Frho;FS;FK;").
Proof using .
  intros K S rho Q H. apply etriple_step.
  intros [tr [ms md]] [Hsp Hk]. cbn [w_tr w_cfg fst snd cfg_model] in Hk. exact (H tr ms md Hsp Hk).
Qed.

Lemma triple1_ecall_det : ltac2:(tb__ "0|1|
S90OF_;S5S70A1M0S6fOF_;F_;S1fS1dS95Sa7Vsegs;R5R4A3S0S8S8eA1S9eVsegs;S26R4A1A2S9S8eS8fA2A3G0S5eS6fS79R7R8S6G0S18R3S19R2R1A2A4A3RaR4R2A2S1RcS6G0S18R5S19R4R3A2A4A1S90S92Vsegs;S6G0S18R6S19R5R4A2A4R1A3RaR2A1F_;Fw';A2F_;F_;Fmd;Fms;Ftr;S93Vsegs;R8Sa5Vsegs;R7R6R5A4R4A4F_;F_;F_;FQ;Frho;FS;FK;Fok;").
Proof using .
  intros ok K S rho Q Hok Hi H.
  eapply triple1_seq_l; [apply triple1_ecall; [exact Hok | exact Hi]|].
  apply triple1_triple. apply triple1_pending. exact H.
Qed.

Lemma etriple_ecall_det : ltac2:(tb__ "0|1|
S5S70A1M0S6fOFx0;Fx;S1fS1dS90OF_;S0S8S8eA1S9eVsegs;S26R3A1A2S9S8eS8fA2A3G0S5eS6fS79R6R7S6G0S18R3S19R2R1A2A4A3R9R4R2A2S3S90S90S1S92Vsegs;S6G0S18R6S19R5R4A2A4R1A3R8R1A1A2Lw';A2F_;F_;Fmd;Fms;Ftr;S94Vsegs;Sa5Vsegs;R6R5R4A4R3A3F_;F_;FQ;Frho;FS;FK;").
Proof using .
  intros K S rho Q Hi H.
  eapply etriple_seq; [apply etriple_ecall; exact Hi|]. apply etriple_pending. exact H.
Qed.

Definition SPpJ (J : jpred) (S : sstate) (rho : valuation) : assn := ltac2:(tb__ "0|0|
S90S1S79Vrho;VS;R1A3VJ;Vrho;S98R1A1S1aS97R1A1A1A3A2Lw;").

Lemma ecall_okJ : ltac2:(tb__ "0|1|
S90OF_;Sa4S1dS1fS5S70A1M0S5eS6fSa8Vsegs;R7R6A3R7R6R4R2A3S22Vsegs;R7R6S6G0S18R5S19R4R3A2A4A4S0S8S8eA1S9eVsegs;S26R7A1A2S9S8eS8fA2A3RbS6G0S18R7S19R6R5A2A4A1F_;F_;F_;F_;Fmd;Fms;Ftr;FS;Frho;FJ;Fok;").
Proof using .
  intros ok J rho S tr ms md Hok Hk Hsm Hi.
  pose proof Hsm as (_ & _ & Hpend & Hhalt & _). cbn [fst snd cfg_ms cfg_model] in Hpend, Hhalt.
  exact (Hok rho tr ms md (pending_of ms) Hk Hhalt Hpend (ecall_step rho S tr ms md Hsm Hi)).
Qed.

Lemma triple1_ecallJ : ltac2:(tb__ "0|0|
S90OF_;Sa4S1fS1dSa8Vsegs;R4R3A3S0S8S8eA1S9eVsegs;S26R3A1A2S9S8eS8fA2A3S93Vsegs;R6Sa6Vsegs;R5R4R3A4S7eR5R4R3A3A4F_;F_;Frho;FS;FJ;Fok;").
Proof using .
  intros ok J S rho Hok Hi. apply triple1_step.
  intros [tr [ms md]] [Hsm Hk]. cbn [w_tr w_cfg fst snd cfg_model] in Hk.
  split; [eapply ecall_okJ; eauto|].
  intros w' Hw. rewrite (ecall_wstep_inv rho S tr ms md w' Hsm Hi Hw).
  split; [apply smatch_pending_of; exact Hsm | exact Hk].
Qed.

Lemma etriple_ecallJ : ltac2:(tb__ "0|0|
Sa4S1fS1dS0S8S8eA1S9eVsegs;S26R2A1A2S9S8eS8fA2A3S94Vsegs;Sa6Vsegs;R4R3R2A4S7eR4R3R2A3A3F_;Frho;FS;FJ;").
Proof using .
  intros J S rho Hi. apply etriple_step.
  intros [tr [ms md]] [Hsm Hk]. cbn [w_tr w_cfg fst snd cfg_model] in Hk.
  exists (tr, mkCfg (pending_of ms) md). split; [eapply ecall_wstep; eauto|].
  split; [apply smatch_pending_of; exact Hsm | exact Hk].
Qed.

Lemma triple1_pendingJ : ltac2:(tb__ "0|1|
S11S5S70A1M0S18A2OFx;Sa4S1fS1dS95G0S5eS6fS79R5R6S6G0S18R3S19R2R1A2A4A3R8R6R4R2A3S1RaS6G0S18R5S19R4R3A2A4A1S90S92Vsegs;S6G0S18R6S19R5R4A2A4R1A3R8R2A1F_;Fw';A2F_;F_;Fmd;Fms;Ftr;S93Vsegs;R6S7eR5R4R3A3R2A4F_;FQ;Frho;FS;FJ;Fok;").
Proof using .
  intros ok J S rho Q H. apply triple1_step.
  intros [tr [ms md]] [Hsp Hk]. cbn [w_tr w_cfg fst snd cfg_model] in Hk. exact (H tr ms md Hsp Hk).
Qed.

Lemma etriple_pendingJ : ltac2:(tb__ "0|1|
Sa4S1fS1dS90OF_;S5S70A1M0S5eS6fS79R5R6S6G0S18R3S19R2R1A2A4A3R8R6R4R2A3S3S90S90S1S92Vsegs;S6G0S18R6S19R5R4A2A4R1A3R7R1A1A2Lw';A2F_;F_;Fmd;Fms;Ftr;S94Vsegs;S7eR5R4R3A3R2A3F_;FQ;Frho;FS;FJ;").
Proof using .
  intros J S rho Q H. apply etriple_step.
  intros [tr [ms md]] [Hsp Hk]. cbn [w_tr w_cfg fst snd cfg_model] in Hk. exact (H tr ms md Hsp Hk).
Qed.

Lemma triple1_ecall_detJ : ltac2:(tb__ "0|1|
S90OF_;Sa4S1fS1dS95Sa8Vsegs;R5R4A3S0S8S8eA1S9eVsegs;S26R4A1A2S9S8eS8fA2A3S5S70A1M0S5eS6fS79R7R8S6G0S18R3S19R2R1A2A4A3RaR8R4R2A3S1RcS6G0S18R5S19R4R3A2A4A1S90S92Vsegs;S6G0S18R6S19R5R4A2A4R1A3RaR2A1F_;Fw';A2F_;F_;Fmd;Fms;Ftr;S93Vsegs;R8Sa6Vsegs;R7R6R5A4R4A4F_;F_;F_;FQ;Frho;FS;FJ;Fok;").
Proof using .
  intros ok J S rho Q Hok Hi H.
  eapply triple1_seq_l; [apply triple1_ecallJ; [exact Hok | exact Hi]|].
  apply triple1_triple. apply triple1_pendingJ. exact H.
Qed.

Lemma etriple_ecall_detJ : ltac2:(tb__ "0|1|
Sa4S1fS1dS90OF_;S0S8S8eA1S9eVsegs;S26R3A1A2S9S8eS8fA2A3S5S70A1M0S5eS6fS79R6R7S6G0S18R3S19R2R1A2A4A3R9R7R4R2A3S3S90S90S1S92Vsegs;S6G0S18R6S19R5R4A2A4R1A3R8R1A1A2Lw';A2F_;F_;Fmd;Fms;Ftr;S94Vsegs;Sa6Vsegs;R6R5R4A4R3A3F_;F_;FQ;Frho;FS;FJ;").
Proof using .
  intros J S rho Q Hi H.
  eapply etriple_seq; [apply etriple_ecallJ; exact Hi|]. apply etriple_pendingJ. exact H.
Qed.

Definition ok_pframe (ok : world -> Prop) (K : list event -> Model -> Prop) : Prop := ltac2:(tb__ "0|2|
S5S70A1M0S5eS6fS15Q40A1M1VK;R4R2A2S0S8G1A1S64R4A1S9G1R2A2A3Sa2S1bVsegs;R5R3A3R4A2Vok;S6G0S18R7S19R6R5A2A4A1F_;F_;F_;Fx8;Fmd;Fms;Ftr;").

Definition ok_pframeJ (ok : world -> Prop) (J : jpred) : Prop := ltac2:(tb__ "0|2|
S1dS5S70A1M0S5eS6fS15Q40A1M1VJ;R5R4R2A3S0S8G1A1S64R4A1S9G1R2A2A3Sa2S1bVsegs;R5R3A3R4A2Vok;S6G0S18R7S19R6R5A2A4A1F_;F_;F_;Fx8;Fmd;Fms;Ftr;Frho;").

Lemma ok_pframeJ_of_tcons : ltac2:(tb__ "0|1|
S90OF_;S5S70A1M0OF_;Sa4S7fR3G0S6fS96R4R2A2L_;Ltr;A2S1dG0S6fR5R3R2R1A3S96R7R3A2F_;Fmd;Ftr;Frho;S85R5R3A2F_;F_;FJ;FSpec;Fok;").
Proof using . intros ok Spec J Hok HJ rho tr ms md x8 Hj. apply Hok. eapply HJ; eauto. Qed.

Lemma ok_pframe_src : ltac2:(tb__ "0|1|
S5S70A1M0OF_;S7fS99Vsegs;R1A2G0S6fS96R3R2A2L_;Ltr;A2FSpec;").
Proof using . intros Spec tr ms md x8 Hk Hp Hok. eapply ok_src_pending; eauto. Qed.

Lemma ok_pframe_tgt : ltac2:(tb__ "0|1|
S5S70A1M0OF_;S7fS9aVsegs;R1A2G0S6fS96R3R2A2L_;Ltr;A2FSpec;").
Proof using . intros Spec tr ms md x8 Hk Hp Hok. eapply ok_tgt_pending; eauto. Qed.

Lemma triple1_ioctl_example : ltac2:(tb__ "0|3|
S90OF_;S5S70A1M0S6fOF_;F_;S1fS1dSa7Vsegs;R4R3A3S7fR5R4A2S0S8S8eA1S9eVsegs;S26R4A1A2S9S8eS8fA2A3S0S15Q40M1A1M2S21R4S2aR5Z11A2A2S17G1Z1dA2A3G0S6fR9R2R1A2S3G2G2S0S8S71A1S77S78R3A1SbbS21R9S2aRaZaA2A2A1A2S9S71S75R1A1A2A3Le;A2F_;Fmd;Ftr;S0G2SbaS21R6S2aR7ZbA2A2A1SbcA3S93Vsegs;RaSa5Vsegs;R9R8R7A4Sa5Vsegs;R9S7bR8S34S16G1S76S74A1A2A1S23R8A1S28R8A1A4R7A4A4F_;F_;F_;F_;F_;F_;Frho;FS;FK;Fok;").
Proof using .
  intros ok K S rho Hokf Hokp Hi H17 Hfd Hcmd.
  apply triple1_ecall_det; [exact Hokf | exact Hi |].
  intros tr ms md Hsp Hk.
  pose proof (smatch_pending_pending _ _ _ _ _ Hsp) as Hp. rewrite H17 in Hp.
  pose proof (smatch_pending_halted _ _ _ _ _ Hsp) as Hh.
  destruct (Hfd tr md Hk) as [e He].
  pose proof (smatch_pending_gpr _ _ _ _ _ 0 Hsp ltac:(lia)) as G0. change (10 + Z.of_nat 0) with 10 in G0.
  pose proof (smatch_pending_gpr _ _ _ _ _ 1 Hsp ltac:(lia)) as G1. change (10 + Z.of_nat 1) with 11 in G1.
  rewrite <- G0 in He. pose proof Hcmd as Hc. rewrite <- G1 in Hc.
  assert (H29 : bv_unsigned (Z_to_bv 64 29) = 29) by reflexivity.
  split.
  - eapply Hokp; [exact Hk | exact Hp |]. eapply ioctl_only_ok; eauto.
  - intros w' Hw. rewrite (wstep_ioctl_inv Hp Hh H29 He Hc Hw).
    split; [|exact Hk]. eapply smatch_after_ret_lit; [exact Hsp | exact Hh].
Qed.

End C.
