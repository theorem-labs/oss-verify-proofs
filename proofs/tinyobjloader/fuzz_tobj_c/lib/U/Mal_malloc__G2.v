(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "or"; "ex"; "iff"; "not"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "N"; "@Corelib.Init.Datatypes"; "bool"; "true"; "prod"; "list"; "option"; "pair"; "cons"; "Some"; "orb"; "nil"; "fst"; "false"; "negb"; "None"; "nat"; "andb"; "app"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "pow"; "mul"; "modulo"; "sub"; "eqb"; "to_nat"; "land"; "opp"; "of_nat"; "shiftr"; "div"; "even"; "lor"; "lxor"; "of_N"; "testbit"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sprop"; "SLit"; "valuation"; "SAlu"; "rw"; "sobj"; "obj_range"; "sstate"; "obj_holds"; "ss_lenient"; "swf"; "SVar"; "ss_next"; "ss_facts"; "eval"; "holds"; "rl"; "SExt"; "cell"; "rm"; "sprop_eqb"; "SAluW"; "SLBytes"; "mkObj"; "DUnknown"; "SMd"; "SPBranch"; "SPUle"; "image_byte"; "mkSS"; "smatch"; "soff"; "FcsrFrm0"; "SPNot"; "enc_bytes"; "mkCell"; "mkVal"; "odefault"; "pairwise_disjoint"; "ranges_disjoint"; "ss_fcsr"; "ss_fregs"; "ss_objs"; "ss_pc"; "ss_regs"; "ss_resv"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval"; "zeval"; "zsupported"; "zholds"; "psupported"; "toS"; "sx32"; "zalu"; "zl_of"; "zle"; "zr_of"; "zsublist"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "segsU"; "pre_fregs"; "pre_regs"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G2.Mal_malloc_fastI.Inst"; "zr1"; "zl1"; "rho1"; "sc"; "idx"; "stv"; "j164"; "sc0"; "kd"; "off"; "S2"; "kq"; "zG"; "zSt"; "avail"; "isRC"; "sz"; "bits"; "N_all"; "ctr"; "ga1"; "ga2"; "zMem"; "Q_stk"; "freed"; "ga3"; "zE"; "Q_act"; "Q_act0"; "Q_ctr"; "Q_ctz"; "Q_lock"; "Q_meta"; "Q_nl"; "Q_sct"; "Q_slot"; "Q_usg0"; "Q_usg1"; "a166"; "ga4"; "rw1"; "sp0"; "u165"; "u167"; "D0"; "off0"; "slack"; "rl1"; "rw1_changed"; "zz"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.Mal_malloc_fast_runs"; "vkind"; "NX"; "MR_P"; "C0"; "F_all"; "F5"; "E_lowbit"; "E_stride"; "voff"; "vrsv"; "CUTS"; "E_S"; "E_p0"; "E_strideM"; "E_strideT"; "F_base"; "F_kind"; "OBJS"; "VL"; "VM0"; "VM1"; "@Stdlib.PArith.BinPos.Pos"; "eqb"; "@stdpp.bitvector.definitions"; "Z_to_bv"; "bv"; "bv_unsigned"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G2.Mal_malloc_fastI"; "zr1"; "kd"; "zl1"; "kq"; "sc0"; "isRC"; "sc"; "off"; "sz"; "zSt"; "avail"; "bits"; "ctr"; "freed"; "idx"; "j164"; "rw1"; "u165"; "zG"; "zMem"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta"; "v"; "@Stdlib.Lists.List"; "forallb"; "In"; "existsb"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink"; "agrees"; "in_vars"; "below200"; "set_vars"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "leaf"; "RsCut"; "mkLeaf"; "lf_state"; "sym_run"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "SP"; "ok_frame"; "@Corelib.Lists.ListDef"; "map"; "Forall"; "nth"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "sptr"; "am_maplen"; "am_last"; "st_active"; "class_of_units"; "region"; "usage_of"; "IB"; "MMAP_THRESHOLD"; "am_mem"; "ameta"; "class_size"; "lowbit"; "mslot"; "nth_slot"; "slot_start"; "ss_hdr"; "st_mmap_counter"; "MUsed"; "PGSZ";
"RkMap"; "UNIT"; "bit"; "padd"; "poff"; "prid"; "rg_kind"; "rg_len"; "rg_live"; "rkind"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "triple"; "assn"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G2.Mal_malloc_fastC.InstC"; "POST"; "setp"; "set_par"; "keys_distinct"; "D05c"; "D05qc"; "D11c"; "D22c"; "D33c"; "D44c"; "D5ac"; "D5aqc"; "D5bc"; "D5bqc"; "D5oc"; "D66c"; "D6oc"; "SETS5"; "SETS5a"; "SETS5aq"; "SETS5b"; "SETS5bq"; "SETS5q"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "state_vars_all"; "sprop_vars_all"; "sv_vars_all"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "with_mem"; "diffs_ok"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue"; "rd_of"; "wok_of"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_SLL"; "ALU_SRL"; "ALU_AND"; "BC_LTU"; "M_MUL"; "aluop"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv"; "mcell"; "image"; "MCell"; "LCtx"; "le_byte"; "mc_w"; "implb"; "loc_addr"; "mc_loc"; "CTX_active"; "VZ"; "optr"; "CTX_mmap_counter"; "CTX_usage"; "LMem"; "MT"; "VP"; "class_ok"; "fold_off"; "group_extent"; "group_ok"; "ly_reg"; "region_of"; "slot_ok"; "usedX"; "used_metas"; "zseq"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G2.Mal_malloc_fast_enum"; "zl_tab"; "zr_list"; "Qst"; "sv_uses"; "G3"; "G4"; "ENV"; "G1"; "G2"; "Pst"; "chk_env"; "zholdsb"; "chk"; "sp_uses"; "stages"; "P1"; "P2"; "P3"; "P4"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.Mal_malloc_fast_runs.RP"; "C5"; "C5q"; "L0s"; "L5a"; "L5b"; "P5a"; "P5b"; "C6"; "F3"; "F4"; "T5a"; "T5b"; "T1"; "T2"; "T3"; "T4"; "C1"; "C2"; "C3"; "C4"; "C5o"; "Ck"; "L0k"; "L1s"; "L2s"; "L3s"; "L4s"; "L5qs"; "L6os"; "L6s"; "T6"; "C7"; "C8"; "L0"; "L1"; "L2"; "L3"; "L4"; "L5"; "L5q"; "L6"; "L6o"; "Tidx"; "Tlhu1"; "Tlhu2"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "ctz_tab_bytes"; "topL"; "C_U"; "addr_of"; "size_classes_bytes"; "byteview_of"; "malloc_stack"; "statics_ok"; "vm_ok"; "@Corelib.Init.Peano"; "lt"; "le"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue"; "cellZ"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface"; "MInv"; "mkMA"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFastPost"; "loop_case"; "malloc_class"; "mf_idx"; "mf_first"; "mf_off"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter"; "reprO"; "slot_end"].
#[local] Ltac2 tb__ s := OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
Require Stdlib.ZArith.ZArith.
Require Stdlib.NArith.NArith.
Require Stdlib.Lists.List.
Require Stdlib.Bool.Bool.
Require Stdlib.PArith.PArith.
Require Stdlib.micromega.Lia.
Require stdpp.bitvector.bitvector.
Require LinuxProcessSemantics.LinuxProcessSem.BvBase.
Require LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Require LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Require LinuxProcessSemantics.LinuxProcessSem.State.
Require LinuxProcessSemantics.LinuxProcessSem.Run.
Require LinuxProcessSemantics.Riscv.Prelude.
Require LinuxProcessSemantics.Riscv.Instr.
Require LinuxProcessSemantics.Riscv.Decode.
Require LinuxProcessSemantics.Riscv.DecodeC.
Require LinuxProcessSemantics.Riscv.Sem.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.LiaFast.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfInv.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSurgery.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGeom.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRepr.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfMain.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSlot.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooterLemmas.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeQuickModel.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ImageUpd.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FpLaws.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFastPost.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_free__G1.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mal_malloc_fast_enum.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.Mal_malloc_fast_runs.

Import ListNotations. Close Scope bv_scope. Open Scope Z_scope.
Import RP.

Fixpoint zholdsb (zr : positive -> Z) (zl : positive -> list Z) (p : sprop) : bool :=
  match p with
  | SPBranch c a b => zcond c (zeval zr zl a) (zeval zr zl b)
  | SPNot q => negb (zholdsb zr zl q)
  | SPUlt a b => zeval zr zl a <? zeval zr zl b
  | SPUle a b => zeval zr zl a <=? zeval zr zl b
  | SPEq a b => zeval zr zl a =? zeval zr zl b
  | SPTrue => true
  | SPAlign i a => (0 <=? a) && ((zr i mod 2 ^ 64) mod 2 ^ a =? 0)
  end.

Lemma zholdsb_sound zr zl p : ltac2:(tb__ "0|0|
S4S0S9S148Vzr;Vzl;Vp;A3SaA3S5eVzr;Vzl;Vp;A3A2").
Proof.
  induction p; cbn.
  - tauto.
  - rewrite Bool.negb_true_iff. rewrite <- IHp. destruct (zholdsb zr zl p); intuition congruence.
  - rewrite Z.ltb_lt. tauto.
  - rewrite Z.leb_le. tauto.
  - rewrite Z.eqb_eq. tauto.
  - tauto.
  - rewrite Bool.andb_true_iff, Z.leb_le, Z.eqb_eq. tauto.
Qed.

Fixpoint sv_uses (P Q : positive -> bool) (e : sv) : bool :=
  match e with
  | SLit _ => true
  | SVar i => P i
  | SAlu _ a b | SAluW _ a b | SMd _ a b | SMdW _ a b => sv_uses P Q a && sv_uses P Q b
  | SExt _ _ a => sv_uses P Q a
  | SLBytes l i _ => Q l && sv_uses P Q i
  end.
Fixpoint sp_uses (P Q : positive -> bool) (p : sprop) : bool :=
  match p with
  | SPBranch _ a b | SPUlt a b | SPUle a b | SPEq a b => sv_uses P Q a && sv_uses P Q b
  | SPNot q => sp_uses P Q q
  | SPTrue => true
  | SPAlign i _ => P i
  end.

Lemma zeval_agree P Q zr zr' zl zl' e : ltac2:(tb__ "0|0|
S0S9S140VP;VQ;Ve;A3SaA3S7S0S9VP;R1A1SaA3S0S6Vzr;R2A1Vzr';R2A1A3F_;Fi;S7S0S9VQ;R1A1SaA3S0ScS6A1Vzl;R2A1Vzl';R2A1A3F_;Fl;S0S6S5cVzr;Vzl;Ve;A3S5cVzr';Vzl';Ve;A3A3F_;F_;F_;").
Proof.
  intros He Hr Hl. induction e; cbn in He |- *;
    repeat match goal with H : (_ && _)%bool = true |- _ => apply andb_prop in H; destruct H end;
    rewrite ?IHe1, ?IHe2, ?IHe by assumption; try reflexivity.
  - rewrite Hr by assumption. reflexivity.
  - rewrite Hl by assumption. reflexivity.
Qed.

Lemma zholds_agree P Q zr zr' zl zl' p : ltac2:(tb__ "0|0|
S0S9S14aVP;VQ;Vp;A3SaA3S7S0S9VP;R1A1SaA3S0S6Vzr;R2A1Vzr';R2A1A3F_;Fi;S7S0S9VQ;R1A1SaA3S0ScS6A1Vzl;R2A1Vzl';R2A1A3F_;Fl;S4S5eVzr;Vzl;Vp;A3S5eVzr';Vzl';Vp;A3A2F_;F_;F_;").
Proof.
  intros Hp Hr Hl. induction p; cbn in Hp |- *;
    repeat match goal with H : (_ && _)%bool = true |- _ => apply andb_prop in H; destruct H end;
    rewrite ?(zeval_agree P Q zr zr' zl zl') by assumption; try tauto.
  rewrite Hr by assumption. tauto.
Qed.

Definition zl_tab : positive -> list Z := ltac2:(tb__ "0|1|
S7S9ScS6A1L_;M0Sb1R1P1A2S181G0Sb1R1P4A2S17dS12S6A1X9x2X9x2Ll;").

Fixpoint zr_list (l : list (positive * Z)) (i : positive) : Z :=
  match l with [] => 0 | (j, x) :: t => if Pos.eqb i j then x else zr_list t i end.
Lemma zr_list_hit j x t : ltac2:(tb__ "0|0|
S0S6S13eSfSbS7S6A2SeS7S6Vj;Vx;A4Vt;A3Vj;A2Vx;A3").
Proof. cbn [zr_list]. rewrite Pos.eqb_refl. reflexivity. Qed.
Lemma zr_list_skip i j x t : ltac2:(tb__ "0|0|
S0S9Sb1Vi;Vj;A2S14A3S0S6S13eSfSbS7S6A2SeS7S6Vj;Vx;A4Vt;A3Vi;A2S13eVt;Vi;A2A3F_;").
Proof. intros H. cbn [zr_list]. rewrite H. reflexivity. Qed.

Definition G1 (k : Z) : Z := ltac2:(tb__ "0|1|
S5cS13eSfSbS7S6A2M0SeS7S6P95Vk;A4S12G0A1A3A1S13dS15cA3").
Definition G2 (k a : Z) : Z := ltac2:(tb__ "0|1|
S5cS13eSfSbS7S6A2M0SeS7S6Pa0Va;A4SfG0SeS7S6P95Vk;A4S12G0A1A3A3A1S13dS15dA3").
Definition G3 (k a b : Z) : Z := ltac2:(tb__ "0|1|
S5cS13eSfSbS7S6A2M0SeS7S6Pa1Vb;A4SfG0SeS7S6Pa0Va;A4SfG0SeS7S6P95Vk;A4S12G0A1A3A3A3A1S13dS15eA3").
Definition G4 (k a b c : Z) : Z := ltac2:(tb__ "0|1|
S5cS13eSfSbS7S6A2M0SeS7S6Pa2Vc;A4SfG0SeS7S6Pa1Vb;A4SfG0SeS7S6Pa0Va;A4SfG0SeS7S6P95Vk;A4S12G0A1A3A3A3A3A1S13dS15fA3").
Definition ENV (k a b c d : Z) : positive -> Z := ltac2:(tb__ "0|1|
S13eSfSbS7S6A2M0SeS7S6Pa3Vd;A4SfG0SeS7S6Pa2Vc;A4SfG0SeS7S6Pa1Vb;A4SfG0SeS7S6Pa0Va;A4SfG0SeS7S6P95Vk;A4S12G0A1A3A3A3A3A3A1").

Definition chk_env (k : Z) (zr : positive -> Z) : bool := ltac2:(tb__ "0|4|
S18S18S18S18ScaS2eS148Vzr;S13dA2M0S158A3ScaS2eG0S159A3A2S11ScaS2eG0S155A3M1ScaS2eG0S156A3M2A2A2S128G1S21S5cVzr;S13dS15aA3SdfVk;A1M3A2A2A2S128G2S21S5cVzr;S13dS15bA3G3A2A2A2").

Definition stages (k : Z) : Z * Z * Z * Z := ltac2:(tb__ "0|1|
S144Vk;A1S6S145Vk;R1A2S6S141Vk;R2R1A3S6SeSbSbS6S6A2M0S6A2S6SeG0S6SeS6S6R3R2A4R1A4S142Vk;R3R2R1A4A4Tc;Tb;Ta;").
Definition chk (k : Z) : bool := ltac2:(tb__ "0|2|
SbSbSbS6S6A2M0S6A2M1S6A2S9Lx;S14bVk;A1G1S6G1S9Lp;R2G0S6G0S9Lp0;R2S6S6S147Vk;S143Vk;R2R1R3R5A5A2Lb;La;Xbx1Lc;Lp0;Xbx1Ld;Lp;Xbx1").
Lemma stages_eq k : ltac2:(tb__ "0|5|
S0SbSbSbS6S6A2M0S6A2M1S6A2S14bVk;A1SeG1S6SeG0S6SeS6S6S144Vk;A1M2S145Vk;G2A2M3A4S141Vk;G2G3A3M4A4S142Vk;G2G3G4A4A4A3").
Proof. reflexivity. Qed.
Lemma chk_envP k a b c d : ltac2:(tb__ "0|5|
S0S9S147Vk;S143Vk;Va;Vb;Vc;Vd;A5M0A2SaA3G0S7S6F_;S1S0S9ScaS2eS148R1S13dA2M1S158A3SaA3S1S0S9ScaS2eG1S159A3SaA3S1S0S9S11ScaS2eG1S155A3M2ScaS2eG1S156A3M3A2SaA3S1S0S9S128G2S21S5cR1S13dS15aA3SdfVk;A1M4A2A2SaA3S0S9S128G3S21S5cR1S13dS15bA3G4A2A2SaA3A2A2A2A2Tzr;F_;").
Proof.
  unfold chk_env. intros H. cbv zeta.
  apply andb_prop in H as [H H5]. apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  exact (conj H1 (conj H2 (conj H3 (conj H4 H5)))).
Qed.
Lemma chk_sound k : ltac2:(tb__ "0|3|
S0S9S149Vk;A1SaA3S0S9S147Vk;S143Vk;S144Vk;A1M0S145Vk;G0A2M1S141Vk;G0G1A3M2S142Vk;G0G1G2A4A5A2SaA3F_;").
Proof. unfold chk. rewrite stages_eq. exact (fun H => H). Qed.

Lemma chk_all : ltac2:(tb__ "0|0|
S0S9ScaS6S149S13cZaZ1ff5A2A3SaA3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Definition Pst (i : positive) : bool := ltac2:(tb__ "0|0|
S11S11S11S11Sb1Vi;P95A2Sb1Vi;Pa0A2A2Sb1Vi;Pa1A2A2Sb1Vi;Pa2A2A2Sb1Vi;Pa3A2A2").
Definition Qst (l : positive) : bool := ltac2:(tb__ "0|0|
S11Sb1Vl;P1A2Sb1Vl;P4A2A2").
Definition P1 (i : positive) : bool := Pos.eqb i 149.
Definition P2 (i : positive) : bool := ltac2:(tb__ "0|0|
S11Sb1Vi;P95A2Sb1Vi;Pa0A2A2").
Definition P3 (i : positive) : bool := ltac2:(tb__ "0|0|
S11S11Sb1Vi;P95A2Sb1Vi;Pa0A2A2Sb1Vi;Pa1A2A2").
Definition P4 (i : positive) : bool := ltac2:(tb__ "0|0|
S11S11S11Sb1Vi;P95A2Sb1Vi;Pa0A2A2Sb1Vi;Pa1A2A2Sb1Vi;Pa2A2A2").

Lemma uses_ok : ltac2:(tb__ "0|0|
S1S0S9ScaS2eS14aS146S13fA2S19S2eS158S19S2eS159S19S2eS155S156A3A3A3A3SaA3S1S0S9S18S140S146S13fS15aA3S140S146S13fS15bA3A2SaA3S1S0S9S140S14cS13fS15cA3SaA3S1S0S9S140S14dS13fS15dA3SaA3S1S0S9S140S14eS13fS15eA3SaA3S0S9S140S14fS13fS15fA3SaA3A2A2A2A2A2").
Proof. repeat split; vm_cast_no_check (@eq_refl bool true). Qed.

Local Ltac pos_cases H :=
  repeat (apply Bool.orb_prop in H; destruct H as [H|H]); apply Pos.eqb_eq in H; subst.
Local Ltac lookup := rewrite ?zr_list_skip by reflexivity; rewrite zr_list_hit.

Theorem sc_stage_ok : ltac2:(tb__ "0|5|
S6S7S6F_;S7ScS6A1M0F_;S1S1aZaR3A2S1aR3Z1ffeA2A2S0S6R3P95A1R4A3S0S6R4Pa0A1S5cR4R3S15cA3A3S0S6R5Pa1A1S5cR5R4S15dA3A3S0S6R6Pa2A1S5cR6R5S15eA3A3S0S6R7Pa3A1S5cR7R6S15fA3A3S0G0R7P1A1S181A3S0G0R8P4A1S17dA3S1Sd9S2eS5eRaR9A2M1S158A3S1Sd9S2eG1S159A3S1S2Sd9S2eG1S155A3M2Sd9S2eG1S156A3M3A2S1G2S0S6S5cRbRaS15aA3SdfRcA1M4A3F_;G3S0S6S5cRbRaS15bA3G4A3F_;A2A2A2A2F_;F_;F_;F_;F_;F_;F_;F_;Fzl;Fzr;Fk;").
Proof.
  intros k zr zl Hk H149 H160 H161 H162 H163 Hl1 Hl4.
  pose proof uses_ok as (U & UT & U1 & U2 & U3 & U4).
  assert (HQ : forall l, Qst l = true -> zl l = zl_tab l).
  { intros l Hq. unfold Qst in Hq. apply Bool.orb_prop in Hq as [Hq|Hq]; apply Pos.eqb_eq in Hq; subst l; [exact Hl1 | exact Hl4]. }
  assert (HQ' : forall l, Qst l = true -> zl_tab l = zl l) by (intros l Hl; symmetry; exact (HQ l Hl)).
  set (a := zr 160%positive). set (b := zr 161%positive). set (c := zr 162%positive). set (d := zr 163%positive).
  assert (A1 : a = G1 k).
  { subst a. rewrite H160. unfold G1. apply (zeval_agree P1 Qst _ _ _ _ _ U1); [|exact HQ].
    intros i Hi. unfold P1 in Hi. pos_cases Hi. lookup. reflexivity. }
  assert (A2 : b = G2 k a).
  { subst b. rewrite H161. unfold G2. apply (zeval_agree P2 Qst _ _ _ _ _ U2); [|exact HQ].
    intros i Hi. unfold P2 in Hi. pos_cases Hi; lookup; reflexivity. }
  assert (A3 : c = G3 k a b).
  { subst c. rewrite H162. unfold G3. apply (zeval_agree P3 Qst _ _ _ _ _ U3); [|exact HQ].
    intros i Hi. unfold P3 in Hi. pos_cases Hi; lookup; reflexivity. }
  assert (A4 : d = G4 k a b c).
  { subst d. rewrite H163. unfold G4. apply (zeval_agree P4 Qst _ _ _ _ _ U4); [|exact HQ].
    intros i Hi. unfold P4 in Hi. pos_cases Hi; lookup; reflexivity. }
  assert (HP : forall i, Pst i = true -> zr i = ENV k a b c d i).
  { intros i Hi. unfold Pst in Hi. unfold ENV. pos_cases Hi; lookup; first [exact H149 | reflexivity]. }

  pose proof chk_all as CK. rewrite forallb_forall in CK. specialize (CK k ltac:(apply In_zseq; lia)).
  apply chk_sound in CK.
  rewrite <- !A1, <- !A2, <- !A3, <- !A4 in CK.
  apply chk_envP in CK. cbv zeta in CK. destruct CK as (C3 & C4 & Por & E5a & E5b).
  assert (TR : forall ps, forallb (sp_uses Pst Qst) ps = true -> forallb (zholdsb (ENV k a b c d) zl_tab) ps = true -> Forall (zholds zr zl) ps).
  { intros ps Hu Hb. apply Forall_forall. intros p Hp.
    apply (proj2 (zholds_agree Pst Qst zr (ENV k a b c d) zl zl_tab p (proj1 (forallb_forall _ _) Hu p Hp) HP HQ)).
    apply zholdsb_sound. exact (proj1 (forallb_forall _ _) Hb p Hp). }
  assert (TRb : forall ps, forallb (sp_uses Pst Qst) ps = true -> Forall (zholds zr zl) ps -> forallb (zholdsb (ENV k a b c d) zl_tab) ps = true).
  { intros ps Hu Hf. apply forallb_forall. intros p Hp. apply zholdsb_sound.
    apply (proj1 (zholds_agree Pst Qst zr (ENV k a b c d) zl zl_tab p (proj1 (forallb_forall _ _) Hu p Hp) HP HQ)).
    exact (proj1 (Forall_forall _ _) Hf p Hp). }
  rewrite !forallb_app in U. apply andb_prop in U as [UF3 U]. apply andb_prop in U as [UF4 U]. apply andb_prop in U as [UPa UPb].
  apply andb_prop in UT as [UTa UTb].
  split; [exact (TR _ UF3 C3)|]. split; [exact (TR _ UF4 C4)|].
  split.
  { apply Bool.orb_prop in Por as [Por|Por]; [left; exact (TR _ UPa Por) | right; exact (TR _ UPb Por)]. }
  split.
  - intros Ha. rewrite (TRb _ UPa Ha) in E5a. cbn [implb] in E5a. apply Z.eqb_eq in E5a.
    rewrite <- E5a. apply (zeval_agree Pst Qst _ _ _ _ _ UTa HP HQ).
  - intros Hb. rewrite (TRb _ UPb Hb) in E5b. cbn [implb] in E5b. apply Z.eqb_eq in E5b.
    rewrite <- E5b. apply (zeval_agree Pst Qst _ _ _ _ _ UTb HP HQ).
Qed.
End Mal_malloc_fast_enum.

Module Mal_malloc_fastI.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSurgery OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGeom OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRepr OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfMain OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSlot OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooterLemmas OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeQuickModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ImageUpd OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FpLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFastPost.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.Mal_malloc_fast_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G2.Mal_malloc_fast_enum OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_free__G1.Mal_free_quick.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Local Ltac top_range_of L := lazymatch goal with | _ : 0x7fff7f800000 <= OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL L <= 0x7fffff800000 |- _ => fail | _ => let h := fresh "TOPR" in pose proof (OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL_val L) as h end.
Local Ltac top_ranges := repeat match goal with | |- context [OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL ?L] => top_range_of L | _ : context [OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL ?L] |- _ => top_range_of L end.
Local Ltac lia := first [Stdlib.micromega.Lia.lia | top_ranges; Stdlib.micromega.Lia.lia].
Local Ltac nia := first [Stdlib.micromega.Lia.nia | top_ranges; Stdlib.micromega.Lia.nia].
Import RP.

Lemma ctz_tab_bytes_range : ltac2:(tb__ "0|0|
Sd9S6S6S1S1aZ0R1A2S1cR1Z100A2A2Lb;S17dA3").
Proof.
  apply Forall_forall. intros b Hb.
  assert (H : forallb (fun b => (0 <=? b) && (b <? 256))%bool ctz_tab_bytes = true) by (vm_compute; reflexivity).
  pose proof (proj1 (forallb_forall _ _) H b Hb) as Hb'. apply andb_prop in Hb' as [H1 H2].
  apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia.
Qed.

Lemma zl_ctz : ltac2:(tb__ "0|2|
S0ScS6A1Sd8Sb3Q8M0A1M1S6G1Sb4G0R1A2Lb;Sd8S6G1Sb2G0A1S17dA4A4S17dA3").
Proof.
  rewrite map_map. rewrite <- (map_id ctz_tab_bytes) at 2. apply map_ext_in.
  intros b Hb. pose proof (proj1 (Forall_forall _ _) ctz_tab_bytes_range b Hb) as R.
  cbn beta in R. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (0 <= b < 256). lia.
Qed.

Lemma ctz_lookup : ltac2:(tb__ "0|2|
S6S1S1aZ0R1A2S1cR1Z20M0A2A2S0S6SdaS6S22S26S1fS1eS1dZ2M1R2A2Z77cb531A2S1dG1G0A2A2Z1bA2A1S17dZ63A4R2A3F_;Fk;").
Proof.
  intros k Hk.
  pose proof (forall_range_dec (fun k => nth (Z.to_nat (Z.shiftr ((2 ^ k * 0x077cb531) mod 2 ^ 32) 27)) ctz_tab_bytes 99 =? k) 0 32
                ctz_tab_ok k Hk) as H.
  apply Z.eqb_eq in H. exact H.
Qed.

Lemma bitop_range : ltac2:(tb__ "0|6|
S6S6S1S1aZ0M0R2A2S1cR2S1dZ2Z40A2M1A2A2M2G2S1S1S1aG0S23R4R3A2M3A2S1cG3G1A2A2S1S1S1aG0S29R4R3A2M4A2S1cG4G1A2A2S1S1aG0S2aR4R3A2M5A2S1cG5G1A2A2A2A2F_;F_;Fb;Fa;").
Proof.
  intros a b Ha Hb.
  assert (La : Z.log2 a < 64). { destruct (Z.eq_dec a 0) as [->|]; [cbn; lia|]. apply Z.log2_lt_pow2; lia. }
  assert (Lb : Z.log2 b < 64). { destruct (Z.eq_dec b 0) as [->|]; [cbn; lia|]. apply Z.log2_lt_pow2; lia. }
  pose proof (Z.land_nonneg a b). pose proof (Z.lor_nonneg a b). pose proof (Z.lxor_nonneg a b).
  pose proof (Z.log2_land a b). pose proof (Z.log2_lor a b). pose proof (Z.log2_lxor a b).
  assert (UP : forall x, 0 <= x -> Z.log2 x < 64 -> x < 2 ^ 64).
  { intros x Hx Hl. destruct (Z.eq_dec x 0) as [->|]; [lia|]. apply Z.log2_lt_pow2; lia. }
  repeat split; try lia; apply UP; lia.
Qed.

Lemma zeval_range : ltac2:(tb__ "0|1|
S7S6F_;S7ScS6A1F_;S2dS0S9S5dR1A1SaA3S1S1aZ0S5cR4R3R2A3M0A2S1cG0S1dZ2Z40A2A2A2F_;Fe;Fzl;Fzr;").
Proof.
  intros zr zl e. induction e; cbn [zsupported zeval]; intros Hs.
  - apply Z.mod_pos_bound. lia.
  - apply Z.mod_pos_bound. lia.
  - apply andb_prop in Hs as [H1 H2]. specialize (IHe1 H1). specialize (IHe2 H2).
    set (a := zeval zr zl e1) in *. set (b := zeval zr zl e2) in *.
    destruct op; cbn [zalu]; try (apply Z.mod_pos_bound; lia).
    + destruct (toS 64 a <? toS 64 b); lia.
    + destruct (a mod 2 ^ 64 <? b mod 2 ^ 64); lia.
    + rewrite !Z.mod_small by lia. apply bitop_range; lia.
    + rewrite Z.mod_small by lia. split; [apply Z.shiftr_nonneg; lia|].
      rewrite Z.shiftr_div_pow2 by (apply Z.mod_pos_bound; lia).
      apply Z.div_lt_upper_bound; [apply Z.pow_pos_nonneg; [lia | apply Z.mod_pos_bound; lia]|].
      pose proof (Z.pow_le_mono_r 2 0 (b mod 64) ltac:(lia) ltac:(apply Z.mod_pos_bound; lia)). nia.
    + rewrite !Z.mod_small by lia. apply bitop_range; lia.
    + rewrite !Z.mod_small by lia. apply bitop_range; lia.
  - unfold sx32. apply Z.mod_pos_bound. lia.
  - destruct op; try discriminate. apply Z.mod_pos_bound. lia.
  - destruct op; try discriminate. unfold sx32. apply Z.mod_pos_bound. lia.
  - apply andb_prop in Hs as [Hs H3]. apply andb_prop in Hs as [H1 H2]. apply Z.ltb_lt in H1. apply Z.leb_le in H2.
    destruct sgn; [apply Z.mod_pos_bound; lia|].
    pose proof (Z.mod_pos_bound (zeval zr zl e) (2 ^ Z.of_N w) ltac:(apply Z.pow_pos_nonneg; lia)).
    pose proof (Z.pow_le_mono_r 2 (Z.of_N w) 64 ltac:(lia) H2). lia.
  - apply Z.mod_pos_bound. lia.
Qed.

Definition kind_of (am : ameta) : vkind := ltac2:(tb__ "0|2|
S9S9cL_;M0S21SddVam;A1Z0M1A2G0S21SdcVam;A1G1A2SafSb0X9x2SaeX9x2").

Section Inst.
Variables (s : astate) (L : layout) (n : Z) (g : sptr) (am : ameta).
Variable rho : valuation.
Variables (b3 b16 : Z).

Hypothesis HW : WF s.
Hypothesis HC : ltac2:(tb__ "0|0|
S18fVs;Vn;Vg;Vam;A4").
Hypothesis HLok : layout_ok L s.
Hypothesis HP12 : ltac2:(tb__ "0|0|
S0S6Sb4Q40S32Vrho;PcA2A2Vn;A3").
Hypothesis Hb3 : 0 <= b3 < 256.
Hypothesis Hb16 : 0 <= b16 < 65536.

Hypothesis Hhdr : ltac2:(tb__ "0|1|
S6S6S0SdSbS6S6A2M0A1SebSe9Vam;S191Vam;A1A2A1S10G0SeS6S6R2R1A4A2A3S1S0S6Vb3;R3A3S0S6Vb16;R2A3A2F_;Fh16;Fh3;").

Definition sc : Z := am_sc am.
Definition sc0 : Z := size_to_class n.
Definition kq : Z := Z.shiftr (n + 3) 4.
Definition idx : Z := mf_idx am.
Definition stv : Z := mf_stride am.
Definition sz : Z := znth sc size_classes.
Definition zG : Z := addr_of L g.
Definition zMem : Z := ltac2:(tb__ "0|0|
S180VL;Se4Vam;A1A2").
Definition zSt : Z := ltac2:(tb__ "0|0|
S180VL;SeaVam;S6eA2A2").
Definition zE : Z := ltac2:(tb__ "0|0|
S180VL;S195Vam;S6eA2A2").
Definition avail : Z := am_avail am.
Definition freed : Z := am_freed am.
Definition bits : Z := meta_bits am.
Definition ctr : Z := ltac2:(tb__ "0|0|
S1fSecVs;A1S1dZ2Z20A2A2").

Definition off0 : Z := ltac2:(tb__ "0|0|
S23S9S6L_;S21Vb3;Z0A2S7dS1bVb16;Z1A2X9x2ZffA2").
Definition slack : Z := mf_slack n am.
Definition off : Z := fold_off slack off0.

Definition zz : Z := off0.

Definition ga1 : Z := G1 kq.
Definition ga2 : Z := G2 kq ga1.
Definition ga3 : Z := ltac2:(tb__ "0|0|
S141S75S7eS7fA3").
Definition ga4 : Z := ltac2:(tb__ "0|0|
S142S75S7eS7fS83A4").
Definition kd : vkind := kind_of am.

Lemma Hn : ltac2:(tb__ "0|0|
S1S1aZ0Vn;A2S1cVn;Se3A2A2"). Proof using HC. exact (proj1 HC). Qed.
Lemma Hu : ltac2:(tb__ "0|0|
S13aS12SdbA1Vs;Vg;Vam;A4"). Proof using HC. exact (mfy_u s n g am HC). Qed.
Lemma Hum : ltac2:(tb__ "0|0|
ScbSbSdbSe5A2SeSdbSe5Vg;Vam;A4S13bVs;A1A3"). Proof using HC HW. apply (used_metas_usedX s g am HW). apply Hu. Qed.
Lemma HMT : ltac2:(tb__ "0|0|
S0SdSe8A1S131Vs;Vg;A2S10Se8SedVam;A1A2A3"). Proof using HC. exact (proj1 (proj2 (proj2 HC))). Qed.
Lemma Hact : ltac2:(tb__ "0|1|
S0SdSdbA1M0SdaG0S22S190Vs;Vn;A2A1SdeVs;A1S16SdbA1A4S10SdbVg;A2A3"). Proof using HC. exact (proj1 (proj2 HC)). Qed.
Lemma Havail_nz : avail <> 0. Proof using HC. exact (proj2 (proj2 (proj2 HC))). Qed.
Lemma G0 : ltac2:(tb__ "0|0|
S136S12SdbA1S16SbSdbS6A2A1Vs;Vg;Vam;A5"). Proof using HC HW. exact (inv_groups HW g am Hu). Qed.

Lemma Hsc : ltac2:(tb__ "0|1|
S1S0S6S6dS190Vs;Vn;A2A3S1S1S1aZ0S6dA2S1cS6dZ30A2A2S1S1aS1bVn;Se2A2Se6S6dA1M0A2S1aG0S6fA2A2A2A2").
Proof using HC HW. exact (mfy_sc s n g am HW HC). Qed.

Lemma Hkq : ltac2:(tb__ "0|0|
S1S1S1aZ0S75A2S1cS75Z1fffA2A2S0S6S71SdfS75A1A3A2").
Proof using HC Hb16 Hb3.
  pose proof Hn as N. unfold kq, sc0, size_to_class, IB.
  replace (n + 4 - 1) with (n + 3) by lia. split; [|reflexivity].
  rewrite Z.shiftr_div_pow2 by lia. unfold MMAP_THRESHOLD in N. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
Qed.

Lemma Hsc0 : ltac2:(tb__ "0|0|
S1S1S1aZ0S71A2S1cS71Z30A2A2S1aS1bVn;Se2A2Se6S71A1A2A2").
Proof using HC. exact (size_to_class_range n Hn). Qed.

Definition isRC : bool := ltac2:(tb__ "0|1|
SdSdbA1M0S9Lx;SdaG0S22S71A1SdeVs;A1S16SdbA1A4SdbS14Ls0;SaXdx2").

Lemma route_cases : ltac2:(tb__ "0|3|
S2S1S0S9S79S14A3S0S6S6dS71A3A2S1S0S9S79SaA3S1S0S6S6dS1bS71Z1A2M0A3S1S1S1aZ4S71A2S1cS71Z20A2A2S1S5S0S6S71Z6A3A1S1S0S9S28S71A1SaA3S1S0S6Se1Vs;S71A2Z0A3S1S1aSe1Vs;G0A2ZcA2S0SdSdbA1M1SdaG1S22S71A1SdeVs;A1S16SdbA1M2A4G2A3A2A2A2A2A2A2A2A2").
Proof using HC HW Hb16 Hb3.
  pose proof Hsc as (E & _). pose proof Hact as A. unfold isRC, sc0.
  destruct (malloc_class_cases s n) as [[M _]|(M & G0 & R & N6 & EV & U0 & U1)]; rewrite M in E, A.
  - left. rewrite A. auto.
  - right. rewrite G0. split; [reflexivity|]. split; [exact E|]. split; [exact R|]. split; [exact N6|]. split; [exact EV|]. split; [exact U0|].
    split; [|reflexivity].
    rewrite A in U1. pose proof HMT as T. unfold MT in T. rewrite T in U1.
    replace (am_avail am =? 0) with false in U1 by (symmetry; apply Z.eqb_neq; exact Havail_nz). cbn [andb] in U1. lia.
Qed.

Definition j164 : Z := ltac2:(tb__ "0|1|
S9S6L_;M0S79S71G0S21S6dZ2fA2Z0S1bS6dZ1A2X9x2X9x2").
Definition a166 : Z := ltac2:(tb__ "0|1|
SdSdbA1M0S6Lx;SdaG0S22S70A1SdeVs;A1S16SdbA1A4SdbS180VL;R1A2Lq;Z0Xdx2").
Definition u165 : Z := usage_of s sc.
Definition u167 : Z := usage_of s j164.

Lemma Hj164 : ltac2:(tb__ "0|0|
S1S1S1aZ0S70A2S1cS70Z30A2A2S5S0S6S70S6dA3A1A2").
Proof using HC HW Hb16 Hb3.
  pose proof Hsc as (_ & R & _). pose proof Hsc0 as [R0 _]. unfold j164.
  destruct route_cases as [[-> ->]|(-> & -> & X & _)]; [|lia].
  destruct (sc0 =? 47) eqn:E; [apply Z.eqb_eq in E|apply Z.eqb_neq in E]; lia.
Qed.

Lemma Hidx : ltac2:(tb__ "0|0|
S1S1S1aZ0S6eA2S1aS6eSddVam;A1A2A2S1S0S9S2cS78S6eA2SaA3S0S6S192Vam;A1Sf1S6eA1A3A2A2").
Proof using HC HW.
  destruct (mfy_first s n g am HW HC) as (k & Hk & E1 & E2 & Hb). unfold idx, avail. rewrite E2. auto.
Qed.

Lemma Gmasks : masks_ok am. Proof using HC HW. exact (proj1 G0). Qed.
Lemma Gclass : ltac2:(tb__ "0|0|
S133S16SbSdbS6A2A1Vg;Vam;A3"). Proof using HC HW. exact (proj1 (proj2 (proj2 (proj2 G0)))). Qed.
Lemma Gslot : ltac2:(tb__ "0|0|
S6S1S1aZ0R1A2S1aR1SddVam;A1A2A2S139S16SbSdbS6A2A1Vg;Vam;R2A4F_;Fi;"). Proof using HC HW. exact (proj1 (proj2 (proj2 G0))). Qed.
Lemma Gmapped : mapped_ok s am. Proof using HC HW. exact (proj1 (proj2 (proj2 (proj2 (proj2 G0))))). Qed.

Lemma Hlast : ltac2:(tb__ "0|1|
S1S1aZ0SddVam;A1M0A2S1aG0Z1fA2A2").
Proof using HC HW. exact (proj1 Gmasks). Qed.

Lemma Hsz : 1 <= sz <= 8191.
Proof using HC HW Hb16 Hb3. unfold sz. apply znth_size_classes_range. pose proof Hsc. lia. Qed.

Lemma Havail_range : 0 < avail < 2 ^ 32.
Proof using HC HW Hb16 Hb3.
  pose proof Gmasks as (Gl & _ & _ & Gav & _ & _ & Gabove & _). pose proof Havail_nz as NZ. unfold avail in *.
  split; [lia|].
  destruct (Z_lt_dec (am_avail am) (2 ^ 32)) as [H|H]; [exact H|]. exfalso.

  assert (E : Z.testbit (am_avail am) (Z.log2 (am_avail am)) = true) by (apply Z.bit_log2; lia).
  assert (32 <= Z.log2 (am_avail am)).
  { replace 32 with (Z.log2 (2 ^ 32)) by reflexivity. apply Z.log2_le_mono. lia. }
  destruct (Gabove (Z.log2 (am_avail am)) ltac:(lia)) as [X _]. rewrite X in E. discriminate.
Qed.

Lemma Hfreed_range : 0 <= freed < 2 ^ 32.
Proof using HC HW Hb16 Hb3.
  pose proof Gmasks as (Gl & _ & _ & _ & Gfr & _ & Gabove & _). unfold freed.
  split; [lia|].
  destruct (Z_lt_dec (am_freed am) (2 ^ 32)) as [H|H]; [exact H|]. exfalso.
  assert (E : Z.testbit (am_freed am) (Z.log2 (am_freed am)) = true) by (apply Z.bit_log2; lia).
  assert (32 <= Z.log2 (am_freed am)).
  { replace 32 with (Z.log2 (2 ^ 32)) by reflexivity. apply Z.log2_le_mono. lia. }
  destruct (Gabove (Z.log2 (am_freed am)) ltac:(lia)) as [_ X]. rewrite X in E. discriminate.
Qed.

Lemma Hmaplen : 0 <= am_maplen am.
Proof using HC HW. exact (proj1 (proj2 G0)). Qed.

Lemma Hstv : ltac2:(tb__ "0|2|
S0S6S6fS9S6L_;S18S21SddVam;A1Z0M0A2S15S21SdcVam;A1M1G0A2A1A2S20S1eG1Z1000A2Sf0A2S1eZ10S7aA2X9x2A3").
Proof using . unfold stv, mf_stride, stride_of, sz, sc, class_size, UNIT. reflexivity. Qed.

Lemma Hstv_range : ltac2:(tb__ "0|1|
S1S1aZ10M0S6fA2S1S1aS1bVn;Z4A2S6fA2S1S1aS1eG0S7aA2S6fA2S1cS1eS6fS1bSddVam;A1Z1A2A2S1dZ2Z14A2A2A2A2A2").
Proof using HC HW Hb16 Hb3.
  pose proof (stride_pos _ _ _ _ _ G0) as Sp. pose proof Hsc as (_ & R & F1 & F2).
  unfold stv, IB in *. split; [exact Sp|]. split; [lia|]. split; [unfold class_size, UNIT, sz, sc in *; lia|].
  destruct Gclass as [(E63 & _) | (_ & _ & _ & X)]; [unfold sc in R; lia|]. exact X.
Qed.

Lemma Hstv20 : stv < 2 ^ 20.
Proof using HC HW Hb16 Hb3. pose proof Hstv_range. pose proof Hlast. nia. Qed.

Variables (rd0 : word -> option byte) (wok0 : word -> bool) (vm : VmMaps).
Hypothesis HMI : ltac2:(tb__ "0|0|
S189S17fS18aVs;VL;A2Vrd0;Vwok0;Vvm;A5").

Lemma Hoff0 : 0 <= off0 < 256.
Proof using Hb16 Hb3. unfold off0. pose proof (land255_range (if b3 =? 0 then ctr else b16 + 1)). lia. Qed.
Lemma Hslack : 0 <= slack.
Proof using HC HW Hb16 Hb3. unfold slack, mf_slack. pose proof Hstv_range. unfold stv in *. apply Z.div_pos; [unfold IB; lia | unfold UNIT; lia]. Qed.
Lemma Hoff : ltac2:(tb__ "0|0|
S1S1S1aZ0S73A2S1aS73S98A2A2S1aS73ZffA2A2").
Proof using HC HW Hb16 Hb3.
  pose proof (fold_off_ok slack off0 Hslack Hoff0) as A. pose proof (fold_off_le slack off0 ltac:(pose proof Hoff0; lia) Hslack) as B.
  pose proof Hoff0 as C. unfold off. lia.
Qed.
Lemma Hzz : 0 <= zz < 256. Proof using Hb16 Hb3. exact Hoff0. Qed.

Lemma land255_mod32 : ltac2:(tb__ "0|1|
S6S0S6S23S1fR1S1dZ2Z20A2A2ZffM0A2S23R1G0A2A3Fx;").
Proof using Hb16 Hb3.
  intros x. change 255 with (Z.ones 8). rewrite !land_ones_low by lia.
  symmetry. apply Znumtheory.Zmod_div_mod; try lia. exists (2 ^ 24). reflexivity.
Qed.

Lemma fold_off_0 : ltac2:(tb__ "0|1|
S6S1aZ0M0R1A2S0S6S134G0R2A2G0A3F_;Fx;").
Proof using Hb16 Hb3.
  intros x Hx. unfold fold_off. cbn [Z.shiftr Z.lor Z.shiftl].
  destruct (0 <? x) eqn:E; [|apply Z.ltb_ge in E; lia].
  rewrite Z.land_0_r. reflexivity.
Qed.

Lemma off_model : ltac2:(tb__ "0|0|
S0S6S73S193Vs;Vn;Vam;S9bA4A3").
Proof using Hb16 Hb3 Hhdr.
  unfold off, mf_off. fold slack. unfold mf_off0. fold slack idx.
  destruct (slack =? 0) eqn:E0.
  - apply Z.eqb_eq in E0. rewrite E0. rewrite !fold_off_0; [reflexivity | lia | pose proof Hoff0; lia].
  - f_equal. destruct (ss_hdr (nth_slot am idx)) as [[h3 h16]|] eqn:Eh.
    + destruct (Hhdr h3 h16 Eh) as [E3 E16]. rewrite <- E3, <- E16. unfold off0, ctr, mf_ctr.
      destruct (b3 =? 0); [apply land255_mod32 | reflexivity].
    + unfold zz. rewrite Z.mod_small by (pose proof Hoff0; lia). reflexivity.
Qed.

Definition rw1 (j : positive) : word := ltac2:(tb__ "0|2|
S9Sb3Q40M0A1L_;M1Sb1Vj;P8eA2Sb2G0Vb3;A2G1Sb1Vj;P8fA2Sb2G0Vb16;A2G1Sb1Vj;P95A2Sb2G0S75A2G1Sb1Vj;P96A2Sb2G0S6dA2G1Sb1Vj;P97A2Sb2G0S76A2G1Sb1Vj;P98A2Sb2G0S78A2G1Sb1Vj;P99A2Sb2G0S7dA2G1Sb1Vj;P9aA2Sb2G0S82A2G1Sb1Vj;P9bA2Sb2G0S7bA2G1Sb1Vj;P9cA2Sb2G0S80A2G1Sb1Vj;P9dA2Sb2G0S6eA2G1Sb1Vj;P9eA2Sb2G0S73A2G1Sb1Vj;Pa0A2Sb2G0S7eA2G1Sb1Vj;Pa1A2Sb2G0S7fA2G1Sb1Vj;Pa2A2Sb2G0S83A2G1Sb1Vj;Pa3A2Sb2G0S91A2G1Sb1Vj;Pa4A2Sb2G0S70A2G1Sb1Vj;Pa5A2Sb2G0S94A2G1Sb1Vj;Pa6A2Sb2G0S90A2G1Sb1Vj;Pa7A2Sb2G0S95A2S32Vrho;Vj;A2X9x2X9x2X9x2X9x2X9x2X9x2X9x2X9x2X9x2X9x2X9x2X9x2X9x2X9x2X9x2X9x2X9x2X9x2X9x2X9x2").

Definition rw1_changed (j : positive) : bool := ltac2:(tb__ "0|0|
S11S11S11S11S11S11S11S11S11S11S11S11S11S11S11S11S11S11S11Sb1Vj;P8eA2Sb1Vj;P8fA2A2Sb1Vj;P95A2A2Sb1Vj;P96A2A2Sb1Vj;P97A2A2Sb1Vj;P98A2A2Sb1Vj;P99A2A2Sb1Vj;P9aA2A2Sb1Vj;P9bA2A2Sb1Vj;P9cA2A2Sb1Vj;P9dA2A2Sb1Vj;P9eA2A2Sb1Vj;Pa0A2A2Sb1Vj;Pa1A2A2Sb1Vj;Pa2A2A2Sb1Vj;Pa3A2A2Sb1Vj;Pa4A2A2Sb1Vj;Pa5A2A2Sb1Vj;Pa6A2A2Sb1Vj;Pa7A2A2").

Lemma rw1_other : ltac2:(tb__ "0|0|
S7S0S9S9aR1A1S14A3S0Sb3Q40A1S92R2A1S32Vrho;R2A2A3F_;Fj;").
Proof using .
  intros j H. unfold rw1_changed in H. unfold rw1.
  repeat (apply Bool.orb_false_iff in H; destruct H as [H ?]).
  repeat match goal with
         | |- (if Pos.eqb j ?c then _ else _) = _ => replace (Pos.eqb j c) with false by (symmetry; assumption)
         end.
  reflexivity.
Qed.

Definition rl1 (l : positive) : list byte := ltac2:(tb__ "0|4|
S9ScSb3Q8M0A1M1A1L_;M2Sb1Vl;P1A2Sd8S6G1Sb2G0A1M3S181A4G2Sb1Vl;P4A2Sd8S6G1G3S17dA4S3eVrho;Vl;A2X9x2X9x2").

Definition rho1 (m : word -> option byte) : valuation := ltac2:(tb__ "0|0|
S52S92S99Vm;A3").

Definition zr1 : positive -> Z := zr_of (rho1 (fun _ => None)).
Definition zl1 : positive -> list Z := zl_of (rho1 (fun _ => None)).

Lemma zr1_zl1_any : ltac2:(tb__ "0|1|
Sb3Q40A1SdSb3Q8A1A1F_;S2dS0S6S5cS65S6cR2A1M0A1S63G0A1R1A3S5cS6aS6bR1A3A3Fe;Fm;").
Proof using . intros. apply zeval_ext; intros; reflexivity. Qed.

Lemma zl1_1 : zl1 1%positive = size_classes_bytes.
Proof using . unfold zl1, zl_of, rho1, rl1. cbn [rl Pos.eqb]. apply zl_table. Qed.
Lemma zl1_4 : zl1 4%positive = ctz_tab_bytes.
Proof using . unfold zl1, zl_of, rho1, rl1. cbn [rl Pos.eqb]. apply zl_ctz. Qed.

Lemma T_supported : ltac2:(tb__ "0|0|
S1S0S9S5dS15cA1SaA3S1S0S9S5dS15dA1SaA3S1S0S9S5dS15eA1SaA3S1S0S9S5dS15fA1SaA3S1S0S9S5dS15aA1SaA3S1S0S9S5dS15bA1SaA3S1S0S9S5dS16eA1SaA3S1S0S9S5dS17aA1SaA3S1S0S9S5dS17bA1SaA3S0S9ScaS2dS5dS17cA3SaA3A2A2A2A2A2A2A2A2A2").
Proof using . repeat split; vm_cast_no_check (@eq_refl bool true). Qed.

Lemma Gk_range : ltac2:(tb__ "0|2|
S1S1S1aZ0M0S7eA2S1cS7eS1dZ2Z40A2M1A2A2S1S1S1aG0S7fA2S1cS7fG1A2A2S1S1S1aG0S83A2S1cS83G1A2A2S1S1aG0S91A2S1cS91G1A2A2A2A2A2").
Proof using .
  unfold ga1, ga2, ga3, ga4, G1, G2, G3, G4.
  pose proof T_supported as (S1 & S2 & S3 & S4 & _).
  repeat split; apply zeval_range; assumption.
Qed.

Lemma HI_vm : ltac2:(tb__ "0|0|
S185VL;Vs;Vvm;A3"). Proof using HMI. exact (proj1 (proj2 (proj2 (proj2 (proj2 HMI))))). Qed.
Lemma HI_ledger : ledger_ok C_U vm. Proof using HMI. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HMI)))))))). Qed.
Lemma Husage : ltac2:(tb__ "0|1|
S6S1S1aZ0Se1Vs;R1A2M0A2S1cG0S1dZ2Z30A2A2A2Fc;").
Proof using HMI. intros c. pose proof (proj1 (proj2 HMI)) as B. cbn [ma_s] in B. exact (proj1 B c). Qed.
Lemma Hu165 : 0 <= u165 < 2 ^ 48. Proof using HMI. exact (Husage sc). Qed.
Lemma Hu167 : 0 <= u167 < 2 ^ 48. Proof using HMI. exact (Husage j164). Qed.

Lemma RC_vals : ltac2:(tb__ "0|1|
S0S9S79SaA3S1S0S6S70S71A3S1S0S6S90Z0M0A3S1S0S6S95G0A3S1S1aS94ZcA2S0S6S6dS1bS71Z1A2A3A2A2A2A2F_;").
Proof using HC HW Hb16 Hb3.
  intros H. destruct route_cases as [[X _]|(_ & E & _ & _ & _ & U0 & U1 & G0)]; [rewrite H in X; discriminate|].
  assert (J : j164 = sc0) by (unfold j164; rewrite H; reflexivity).
  unfold a166, u167, u165. rewrite J, G0, E. auto.
Qed.

Lemma Hregion : ltac2:(tb__ "0|7|
S3Se0Se0S1S0SdSe0A1S138Vs;Sf4Se4Vam;A1M0A1M1A2S10Se0R1A2A3S1S0Sf8Sf5R1A1SefA3S1S0S9Sf7R1A1SaA3S1S1aZ0M2Sf3G0A1M3A2S1S1aS1bS1bG3S135Vam;A1A2Se2A2Sf6R1A1M4A2S1S1cG2SdcVam;A1A2S0S6G3G2A3F_;S1S1aSeeS137VL;G1A2M5A2S1S1aS1bG5G4A2M6S17eVL;A1A2S2S1aG6Z10000A2S1aZ5b000G5A2A2A2A2A2A2A2A2A2A2Lrg;A2").
Proof using HC HMI HW Hb16 Hb3.
  destruct (used_group_region [] None U0 s g am HW Hu) as (rg & Hr & Hk & Hl & Ho & Hext & Hm0).
  exists rg. repeat (split; [assumption|]).
  pose proof (footprint_region_In s _ _ Hr Hk Hl) as InR.
  pose proof (extent_pos _ _ _ _ _ G0) as EP.
  assert (LEN : 0 <= rg_len rg) by (unfold IB in Hext; lia).
  pose proof (fp_mem_range C_U L s vm _ _ HI_vm HI_ledger InR LEN) as (M1 & M2 & M3).
  unfold addr_of, loc_addr in M1, M2, M3. cbn [prid poff mc_img_lo mc_img_hi C_U] in M1, M2, M3.
  rewrite Z.add_0_r in M1, M2, M3. lia.
Qed.

Lemma Hmaplen_small : ltac2:(tb__ "0|0|
S1cS1eSdcVam;A1Z1000A2S1dZ2Z2fA2A2").
Proof using HC HMI HW Hb16 Hb3.
  destruct (Z_lt_dec 0 (am_maplen am)) as [Hp|Hz]; [|pose proof Hmaplen; lia].
  destruct (Gmapped Hp) as (r & rg & Em & Hr & _ & _ & Len & _).
  destruct Hregion as (rg' & Hr' & _ & _ & _ & _ & _ & P1 & P2 & _).
  rewrite Em in Hr'. cbn [prid] in Hr'. rewrite Hr in Hr'. injection Hr' as <-.
  top_ranges. unfold PGSZ in *. lia.
Qed.

Lemma bits_eq : ltac2:(tb__ "0|0|
S0S6S7bS1bS1bS1bSddVam;A1Z20A2S1eZ40S6dA2A2S1eZ1000SdcVam;A1A2A2A3").
Proof using . reflexivity. Qed.

Lemma ctr_range : 0 <= ctr < 2 ^ 32.
Proof using Hb16 Hb3. unfold ctr. apply Z.mod_pos_bound. lia. Qed.

Lemma R_all : ltac2:(tb__ "0|10|
S1S1S1aZ0M0Vn;A2S1cVn;Se3A2A2S1S1S1aG0S75A2S1cS75Z1fffM1A2A2S1S1S1aG0S6dA2S1cS6dZ30A2A2S1S1S1aZ1M2S7aA2S1aS7aG1A2A2S1S1S1aG0S6eA2S1aS6eSddVam;A1M3A2A2S1S1S1aG0G3A2S1aG3Z1fA2A2S1S1aZ10M4S6fA2S1S1aS1bVn;Z4M5A2S6fA2S1S1aS1eG4S7aA2S6fA2S1S1cS6fS1dZ2M6Z14A2M7A2S1S1aG0S1eS6fS6eA2M8A2S1S1aS1bG8S6fA2S1eS6fS1bG3G2A2A2M9A2S1S1cG9G7A2S1S1S1cG0S78A2S1cS78S1dG6Z20A2MaA2A2S1S1S1aG0S82A2S1cS82GaA2A2S1S1S1aG0S7dA2S1cS7dGaA2A2S1S1aG0SdcVam;A1MbA2S1S1cS1eGbZ1000McA2S1dG6Z2fA2MdA2S1S1S1aG0Vb3;A2S1cVb3;Z100MeA2A2S1S1S1aG0Vb16;A2S1cVb16;Z10000A2A2S1S1S1aG0S97A2S1cS97GeA2A2S1S1S1aG0S73A2S1aS73S98A2A2S1S1aS73ZffA2S1S1aS1bS1bS1eG4S73A2Vn;A2G5A2S6fA2S1S1aGcS80A2S1S0S6S77S1bS1bS80G4A2G8A2A3S1S0S6S84S20S1bS77S6fA2G5A2A3S1S1aS1bS84G5A2S17eVL;A1MfA2S1S1cGfGdA2S1S1aGcS76A2S1aS1bS76Z28A2GfA2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof using HC HMI HW Hb16 Hb3 Hhdr.
  pose proof Hn. pose proof Hkq. pose proof Hsc. pose proof Hsz. pose proof Hidx. pose proof Hlast.
  pose proof Hstv_range. pose proof Hstv20. pose proof Havail_range. pose proof Hfreed_range. pose proof ctr_range.
  pose proof Hmaplen. pose proof Hmaplen_small. pose proof Hb3. pose proof Hb16. pose proof Hoff0. pose proof Hoff.
  pose proof (F_off C_U s L n g am zz rd0 wok0 vm HMI HC Hzz) as (O1 & O2 & O3). unfold f_off in O1, O2. rewrite <- off_model in O1, O2.
  pose proof (F_geom C_U s L n g am zz rd0 wok0 vm HMI HC Hzz) as (Sp & E1 & E2 & E3 & EZ & Pm & Pe & Hsi & (rg & Hrg & [RI1 RI2] & Erg)).
  destruct Hregion as (rg' & Hr' & _ & _ & Ho & Hext & _ & P1 & P2 & _).
  pose proof (F_area C_U s L n g am zz rd0 wok0 vm HMI HC Hzz) as (a & k & Ha & Hk & Eg & InA & Pa & Pa2 & EzG & _).
  pose proof (fp_mem_range C_U L s vm _ _ HI_vm HI_ledger InA ltac:(unfold PGSZ; lia)) as (A1 & A2 & A3).
  pose proof ceiling_small.
  assert (EzMem : zMem = ly_reg L (prid (am_mem am)) + poff (am_mem am)).
  { unfold zMem, addr_of, loc_addr. destruct (am_mem am); reflexivity. }
  unfold f_st, f_zm, f_p, f_e, f_idx, f_zg in *. fold idx stv zSt zMem zE zG in E1, E2, E3, Pm, Pe.
  change (mf_stride am) with stv in *. change (mf_idx am) with idx in *.
  unfold group_extent in *. change (stride_of am) with stv in *.
  unfold UNIT, IB, PGSZ, AREA_HDR, META_SIZE, METAS_PER_AREA in *. unfold zG in *.
  repeat match goal with |- _ /\ _ => split end; lia.
Qed.

Lemma zr1_v : ltac2:(tb__ "0|1|
S7S6S0Sb3Q40M0A1S92R2A1Sb2G0R1A2A3S1S1aZ0R2A2S1cR2S1dZ2Z40A2A2A2S0S6S6aR4A1R3A3F_;F_;Fz;Fj;").
Proof using . intros j z E Hz. unfold zr1, zr_of, rho1. cbn [rw]. rewrite E. apply u64. exact Hz. Qed.

Local Ltac zv j := unfold zr1, zr_of, rho1; cbn [rw rw1 Pos.eqb]; apply u64; pose proof R_all; pose proof Gk_range; try lia.

Lemma zr1_12 : zr1 12%positive = n. Proof using HP12. unfold zr1, zr_of, rho1. cbn [rw rw1 Pos.eqb]. exact HP12. Qed.
Lemma zr1_142 : zr1 142%positive = b3. Proof using HC HMI HW Hb16 Hb3 Hhdr. zv 142. Qed.
Lemma zr1_143 : zr1 143%positive = b16. Proof using HC HMI HW Hb16 Hb3 Hhdr. zv 143. Qed.
Lemma zr1_149 : zr1 149%positive = kq. Proof using HC HMI HW Hb16 Hb3 Hhdr. zv 149. Qed.
Lemma zr1_150 : zr1 150%positive = sc. Proof using HC HMI HW Hb16 Hb3 Hhdr. zv 150. Qed.
Lemma zr1_151 : zr1 151%positive = zG. Proof using HC HMI HW Hb16 Hb3 Hhdr. zv 151. Qed.
Lemma zr1_152 : zr1 152%positive = avail. Proof using HC HMI HW Hb16 Hb3 Hhdr. zv 152. Qed.
Lemma zr1_153 : zr1 153%positive = ctr. Proof using HC HMI HW Hb16 Hb3 Hhdr. zv 153. Qed.
Lemma zr1_154 : zr1 154%positive = freed. Proof using HC HMI HW Hb16 Hb3 Hhdr. zv 154. Qed.
Lemma bits_range : 0 <= bits < 2 ^ 48.
Proof using HC HMI HW Hb16 Hb3 Hhdr. rewrite bits_eq. pose proof R_all. lia. Qed.
Lemma zr1_155 : zr1 155%positive = bits. Proof using HC HMI HW Hb16 Hb3 Hhdr. pose proof bits_range. zv 155. Qed.
Lemma zr1_156 : zr1 156%positive = zMem. Proof using HC HMI HW Hb16 Hb3 Hhdr. zv 156. Qed.
Lemma zr1_157 : zr1 157%positive = idx. Proof using HC HMI HW Hb16 Hb3 Hhdr. zv 157. Qed.
Lemma zr1_158 : zr1 158%positive = off. Proof using HC HW Hb16 Hb3. unfold zr1, zr_of, rho1; cbn [rw rw1 Pos.eqb]; apply u64. pose proof Hoff. lia. Qed.
Lemma zr1_160 : zr1 160%positive = ga1. Proof using HC HMI HW Hb16 Hb3 Hhdr. zv 160. Qed.
Lemma zr1_161 : zr1 161%positive = ga2. Proof using HC HMI HW Hb16 Hb3 Hhdr. zv 161. Qed.
Lemma zr1_162 : zr1 162%positive = ga3. Proof using HC HMI HW Hb16 Hb3 Hhdr. zv 162. Qed.
Lemma zr1_163 : zr1 163%positive = ga4. Proof using HC HMI HW Hb16 Hb3 Hhdr. zv 163. Qed.
Lemma zr1_164 : zr1 164%positive = j164. Proof using HC HMI HW Hb16 Hb3 Hhdr. pose proof Hj164. zv 164. Qed.
Lemma zr1_165 : zr1 165%positive = u165. Proof using HC HMI HW Hb16 Hb3 Hhdr. pose proof Hu165. zv 165. Qed.
Lemma zr1_166 : ltac2:(tb__ "0|0|
S0S9S79SaA3S0S6S6aPa6A1Z0A3F_;"). Proof using HC HW Hb16 Hb3. intros H. pose proof (RC_vals H) as (_ & E & _). unfold zr1, zr_of, rho1; cbn [rw rw1 Pos.eqb]. rewrite E. apply u64. lia. Qed.
Lemma zr1_167 : zr1 167%positive = u167. Proof using HC HMI HW Hb16 Hb3 Hhdr. pose proof Hu167. zv 167. Qed.

Lemma ze_var : ltac2:(tb__ "0|0|
S7S0S6S5cS6aS6bS39R1A1A3S1fS6aR1A1S1dZ2Z40A2A2A3Fj;"). Proof using . reflexivity. Qed.
Lemma ze_v : ltac2:(tb__ "0|0|
S7S0S6S5cS6aS6bSc9R1A1A3S1fS6aR1A1S1dZ2Z40A2A2A3Fj;"). Proof using . reflexivity. Qed.
Lemma ze_lit : ltac2:(tb__ "0|0|
S6S0S6S5cS6aS6bS2fR1A1A3S1fR1S1dZ2Z40A2A2A3Fz;"). Proof using . reflexivity. Qed.
Lemma ze_alu : ltac2:(tb__ "0|0|
S121S2dS2dS0S6S5cS6aS6bS31R3R2R1A3A3S62Z40R3S5cS6aS6bR2A3S5cS6aS6bR1A3A4A3Fy;Fx;Fop;"). Proof using . reflexivity. Qed.
Lemma ze_aluw : ltac2:(tb__ "0|2|
S121S2dS2dS0S6S5cS6aS6bS43R3R2R1A3A3S61S62Z20M0R3S1fS5cS6aS6bR2A3S1dZ2G0A2M1A2S1fS5cS6aS6bR1A3G1A2A4A1A3Fy;Fx;Fop;"). Proof using . reflexivity. Qed.
Lemma ze_mul : ltac2:(tb__ "0|0|
S2dS2dS0S6S5cS6aS6bS47S120R2R1A3A3S1fS1eS5cS6aS6bR2A3S5cS6aS6bR1A3A2S1dZ2Z40A2A2A3Fy;Fx;"). Proof using . reflexivity. Qed.
Lemma ze_ext : ltac2:(tb__ "0|3|
S9S8S2dS0S6S5cS6aS6bS3fR3R2R1A3A3S9S6Lsg;R3S1fS60S2bR2A1M0S5cS6aS6bR1A3M1A2S1dZ2M2Z40A2A2S1fG1S1dG2G0A2A2X9x2A3Fx;Fw;Fsg;"). Proof using . reflexivity. Qed.
Lemma ze_lbytes : ltac2:(tb__ "0|0|
S7S2dS6S0S6S5cS6aS6bS44R3R2R1A3A3S1fS64S66S5cS6aS6bR2A3R1S6bR3A1A3A1S1dZ2Z40A2A2A3Fkk;Fix;Fl;"). Proof using . reflexivity. Qed.

Local Ltac zvv L := rewrite ze_v, L; apply m64; pose proof R_all; pose proof bits_range; pose proof Gk_range; lia.
Lemma ze12 : ltac2:(tb__ "0|0|
S0S6S5cS6aS6bSc9PcA1A3Vn;A3"). Proof using HC HMI HP12 HW Hb16 Hb3 Hhdr. zvv zr1_12. Qed.
Lemma ze142 : ltac2:(tb__ "0|0|
S0S6S5cS6aS6bSc9P8eA1A3Vb3;A3"). Proof using HC HMI HW Hb16 Hb3 Hhdr. zvv zr1_142. Qed.
Lemma ze143 : ltac2:(tb__ "0|0|
S0S6S5cS6aS6bSc9P8fA1A3Vb16;A3"). Proof using HC HMI HW Hb16 Hb3 Hhdr. zvv zr1_143. Qed.
Lemma ze149 : ltac2:(tb__ "0|0|
S0S6S5cS6aS6bSc9P95A1A3S75A3"). Proof using HC HMI HW Hb16 Hb3 Hhdr. zvv zr1_149. Qed.
Lemma ze150 : ltac2:(tb__ "0|0|
S0S6S5cS6aS6bSc9P96A1A3S6dA3"). Proof using HC HMI HW Hb16 Hb3 Hhdr. zvv zr1_150. Qed.
Lemma ze151 : ltac2:(tb__ "0|0|
S0S6S5cS6aS6bSc9P97A1A3S76A3"). Proof using HC HMI HW Hb16 Hb3 Hhdr. zvv zr1_151. Qed.
Lemma ze152 : ltac2:(tb__ "0|0|
S0S6S5cS6aS6bSc9P98A1A3S78A3"). Proof using HC HMI HW Hb16 Hb3 Hhdr. zvv zr1_152. Qed.
Lemma ze153 : ltac2:(tb__ "0|0|
S0S6S5cS6aS6bSc9P99A1A3S7dA3"). Proof using HC HMI HW Hb16 Hb3 Hhdr. zvv zr1_153. Qed.
Lemma ze154 : ltac2:(tb__ "0|0|
S0S6S5cS6aS6bSc9P9aA1A3S82A3"). Proof using HC HMI HW Hb16 Hb3 Hhdr. zvv zr1_154. Qed.
Lemma ze155 : ltac2:(tb__ "0|0|
S0S6S5cS6aS6bSc9P9bA1A3S7bA3"). Proof using HC HMI HW Hb16 Hb3 Hhdr. zvv zr1_155. Qed.
Lemma ze156 : ltac2:(tb__ "0|0|
S0S6S5cS6aS6bSc9P9cA1A3S80A3"). Proof using HC HMI HW Hb16 Hb3 Hhdr. zvv zr1_156. Qed.
Lemma ze157 : ltac2:(tb__ "0|0|
S0S6S5cS6aS6bSc9P9dA1A3S6eA3"). Proof using HC HMI HW Hb16 Hb3 Hhdr. zvv zr1_157. Qed.
Lemma ze158 : ltac2:(tb__ "0|0|
S0S6S5cS6aS6bSc9P9eA1A3S73A3"). Proof using HC HMI HW Hb16 Hb3 Hhdr. rewrite ze_v, zr1_158. apply m64. pose proof R_all. pose proof Hslack. lia. Qed.
Lemma ze164 : ltac2:(tb__ "0|0|
S0S6S5cS6aS6bSc9Pa4A1A3S70A3"). Proof using HC HMI HW Hb16 Hb3 Hhdr. rewrite ze_v, zr1_164. apply m64. pose proof Hj164. lia. Qed.
Lemma ze165 : ltac2:(tb__ "0|0|
S0S6S5cS6aS6bSc9Pa5A1A3S94A3"). Proof using HC HMI HW Hb16 Hb3 Hhdr. rewrite ze_v, zr1_165. apply m64. pose proof Hu165. lia. Qed.
Lemma ze166 : ltac2:(tb__ "0|0|
S0S9S79SaA3S0S6S5cS6aS6bSc9Pa6A1A3Z0A3F_;"). Proof using HC HW Hb16 Hb3. intros H. rewrite ze_v, (zr1_166 H). reflexivity. Qed.
Lemma ze167 : ltac2:(tb__ "0|0|
S0S6S5cS6aS6bSc9Pa7A1A3S95A3"). Proof using HC HMI HW Hb16 Hb3 Hhdr. rewrite ze_v, zr1_167. apply m64. pose proof Hu167. lia. Qed.

Lemma bits_shift5 : ltac2:(tb__ "0|0|
S0S6S26S7bZ5A2S1bS1bZ1S1eZ2S6dA2A2S1eZ80SdcVam;A1A2A2A3").
Proof using HC HMI HW Hb16 Hb3 Hhdr.
  rewrite bits_eq, Z.shiftr_div_pow2 by lia. change (2 ^ 5) with 32. pose proof R_all. pose proof Hlast.
  replace (am_last am + 32 + 64 * sc + 4096 * am_maplen am) with (am_last am + (1 + 2 * sc + 128 * am_maplen am) * 32) by lia.
  rewrite Z.div_add by lia. rewrite Z.div_small by lia. lia.
Qed.

Lemma ze_tabidx : ltac2:(tb__ "0|0|
S0S6S5cS6aS6bS31S11eS31S11dSc9P9bA1S2fZ5A1A3S2fZ7eA1A3A3S1eZ2S6dA2A3").
Proof using HC HMI HW Hb16 Hb3 Hhdr.
  rewrite !ze_alu, ze155, ze_lit. cbn [zalu]. pose proof bits_range as B. pose proof R_all as R.
  rewrite (Z.mod_small bits) by lia. change (5 mod 2 ^ 64) with 5. change (5 mod 64) with 5.
  rewrite bits_shift5. rewrite (Z.mod_small (1 + 2 * sc + 128 * am_maplen am)) by lia.
  change (126 mod 2 ^ 64) with 126. apply land_126_odd; lia.
Qed.

Lemma ze_S : ltac2:(tb__ "0|0|
S0S6S5cS6aS6bSa7A3S7aA3").
Proof using HC HMI HW Hb16 Hb3 Hhdr.
  unfold E_S. rewrite ze_ext. cbn [Z.of_N]. rewrite ze_lbytes, ze_tabidx, zl1_1.
  pose proof R_all as R. rewrite table_u16 by lia. fold sz. rewrite !Z.mod_small; lia.
Qed.

Lemma ze_strideT : ltac2:(tb__ "0|0|
S0S6S5cS6aS6bSaaA3S1eZ10S7aA2A3").
Proof using HC HMI HW Hb16 Hb3 Hhdr.
  unfold E_strideT. rewrite ze_alu, ze_S, ze_lit. cbn [zalu]. change ((4 mod 2 ^ 64) mod 64) with 4.
  rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 4) with 16. pose proof R_all. rewrite Z.mod_small; lia.
Qed.

Lemma land_not4095 : ltac2:(tb__ "0|0|
S6S1S1aZ0R1A2S1cR1S1dZ2Z40A2A2A2S0S6S23R2Zfffffffffffff000A2S20R2S1fR2Z1000A2A2A3F_;Fx;").
Proof using Hb16 Hb3.
  intros x Hx.
  assert (E : Z.land x 18446744073709547520 = Z.ldiff (Z.land x (Z.ones 64)) (Z.ones 12)).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.ldiff_spec, !Z.land_spec.
    assert (E2 : 18446744073709547520 = Z.ldiff (Z.ones 64) (Z.ones 12)) by reflexivity. rewrite E2, Z.ldiff_spec.
    destruct (Z.testbit x i), (Z.testbit (Z.ones 64) i), (Z.testbit (Z.ones 12) i); reflexivity. }
  rewrite E, Z.land_ones, (Z.mod_small x (2 ^ 64)) by lia.
  rewrite Z.ldiff_ones_r by lia. rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia.
  change (2 ^ 12) with 4096. pose proof (Z.div_mod x 4096 ltac:(lia)). lia.
Qed.

Lemma ze_strideM : ltac2:(tb__ "0|1|
S1cZ0SdcVam;A1M0A2S0S6S5cS6aS6bSa9A3S20S1eG0Z1000A2Z10A2A3F_;").
Proof using HC HMI HW Hb16 Hb3 Hhdr.
  intros Hm. unfold E_strideM. rewrite !ze_alu, ze155, !ze_lit. cbn [zalu]. pose proof bits_range as B. pose proof R_all as R.
  pose proof Hlast as HL.
  rewrite (Z.mod_small bits) by lia. change (18446744073709547520 mod 2 ^ 64) with 18446744073709547520.
  rewrite land_not4095 by lia. rewrite bits_eq.
  rewrite <- (Z.mod_unique_pos (am_last am + 32 + 64 * sc + 4096 * am_maplen am) 4096 (am_maplen am) (am_last am + 32 + 64 * sc)) by lia.
  change ((-16) mod 2 ^ 64) with (2 ^ 64 - 16).
  replace (am_last am + 32 + 64 * sc + 4096 * am_maplen am - (am_last am + 32 + 64 * sc) + (2 ^ 64 - 16))
    with ((am_maplen am * 4096 - 16) + 1 * 2 ^ 64) by lia.
  rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

Lemma ze_stride : ltac2:(tb__ "0|0|
S0S6S5cS6aS6bSa3S72A1A3S6fA3").
Proof using HC HMI HW Hb16 Hb3 Hhdr.
  rewrite Hstv. unfold kd, kind_of.
  destruct (am_last am =? 0) eqn:El; [destruct (am_maplen am =? 0) eqn:Em|]; cbn [E_stride andb negb].
  - rewrite ze_strideT. reflexivity.
  - apply Z.eqb_neq in Em. pose proof Hmaplen. rewrite ze_strideM by lia. reflexivity.
  - rewrite ze_strideT. reflexivity.
Qed.

Lemma ze_p0 : ltac2:(tb__ "0|0|
S0S6S5cS6aS6bSa8S72A1A3S77A3").
Proof using HC HMI HW Hb16 Hb3 Hhdr.
  unfold E_p0. rewrite !ze_alu, ze_mul, ze_stride, ze156, ze157, !ze_lit. cbn [zalu]. pose proof R_all as R.
  rewrite !Z.mod_small; lia.
Qed.

Lemma ze_hi : ltac2:(tb__ "0|0|
S0S6S5cS6aS6bS31S11bSa3S72A1S2fN4A1A3A3S20S6fZ4A2A3").
Proof using HC HMI HW Hb16 Hb3 Hhdr.
  rewrite ze_alu, ze_stride, ze_lit. cbn [zalu]. pose proof R_all as R.
  change ((-4) mod 2 ^ 64) with (2 ^ 64 - 4). replace (stv + (2 ^ 64 - 4)) with ((stv - 4) + 1 * 2 ^ 64) by lia.
  rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

Lemma ze_actoff : ltac2:(tb__ "0|1|
S0S6S5cS6aS6bS31S11bS31S11cSc9P96A1S2fZ3A1A3S2fZ58M0A1A3A3S1bS1eZ8S6dA2G0A2A3").
Proof using HC HMI HW Hb16 Hb3 Hhdr.
  rewrite !ze_alu, ze150, !ze_lit. cbn [zalu]. change ((3 mod 2 ^ 64) mod 64) with 3. rewrite Z.shiftl_mul_pow2 by lia.
  change (2 ^ 3) with 8. pose proof R_all. rewrite !Z.mod_small; lia.
Qed.
Lemma ze_acthi : ltac2:(tb__ "0|1|
S0S6S5cS6aS6bS31S11bS31S11cSc9P96A1S2fZ3A1A3S2fZ60M0A1A3A3S1bS1eZ8S6dA2G0A2A3").
Proof using HC HMI HW Hb16 Hb3 Hhdr.
  rewrite !ze_alu, ze150, !ze_lit. cbn [zalu]. change ((3 mod 2 ^ 64) mod 64) with 3. rewrite Z.shiftl_mul_pow2 by lia.
  change (2 ^ 3) with 8. pose proof R_all. rewrite !Z.mod_small; lia.
Qed.

Lemma ze_idx8 : ltac2:(tb__ "0|1|
S2dS6S6S0S6S5cS6aS6bR3A3R2A3S1S1aZ0R3A2M0S1cR3Z30A2A2S1G0S1cR3Z3e8A2A2S0S6S5cS6aS6bS31S11bS31S11cR6S2fZ3A1A3S2fR4A1A3A3S1bS1eZ8R5A2R4A2A3F_;F_;F_;Fk;Fx;Fe;").
Proof using Hb16 Hb3.
  intros e x k He Hx Hk. rewrite !ze_alu, He, !ze_lit. cbn [zalu]. change ((3 mod 2 ^ 64) mod 64) with 3. rewrite Z.shiftl_mul_pow2 by lia.
  change (2 ^ 3) with 8. rewrite !Z.mod_small; lia.
Qed.
Lemma ze_act0off : ltac2:(tb__ "0|1|
S0S6S5cS6aS6bS31S11bS31S11cSc9Pa4A1S2fZ3A1A3S2fZ58M0A1A3A3S1bS1eZ8S70A2G0A2A3").
Proof using HC HMI HW Hb16 Hb3 Hhdr. apply (ze_idx8 (v 164) j164 88 ze164); [pose proof Hj164; lia | lia]. Qed.
Lemma ze_act0hi : ltac2:(tb__ "0|1|
S0S6S5cS6aS6bS31S11bS31S11cSc9Pa4A1S2fZ3A1A3S2fZ60M0A1A3A3S1bS1eZ8S70A2G0A2A3").
Proof using HC HMI HW Hb16 Hb3 Hhdr. apply (ze_idx8 (v 164) j164 96 ze164); [pose proof Hj164; lia | lia]. Qed.
Lemma ze_usg0off : ltac2:(tb__ "0|1|
S0S6S5cS6aS6bS31S11bS31S11cSc9Pa4A1S2fZ3A1A3S2fZ1d8M0A1A3A3S1bS1eZ8S70A2G0A2A3").
Proof using HC HMI HW Hb16 Hb3 Hhdr. apply (ze_idx8 (v 164) j164 472 ze164); [pose proof Hj164; lia | lia]. Qed.
Lemma ze_usg0hi : ltac2:(tb__ "0|1|
S0S6S5cS6aS6bS31S11bS31S11cSc9Pa4A1S2fZ3A1A3S2fZ1e0M0A1A3A3S1bS1eZ8S70A2G0A2A3").
Proof using HC HMI HW Hb16 Hb3 Hhdr. apply (ze_idx8 (v 164) j164 480 ze164); [pose proof Hj164; lia | lia]. Qed.
Lemma ze_usg1off : ltac2:(tb__ "0|1|
S0S6S5cS6aS6bS31S11bS31S11cSc9P96A1S2fZ3A1A3S2fZ1d8M0A1A3A3S1bS1eZ8S6dA2G0A2A3").
Proof using HC HMI HW Hb16 Hb3 Hhdr. apply (ze_idx8 (v 150) sc 472 ze150); [pose proof R_all; lia | lia]. Qed.
Lemma ze_usg1hi : ltac2:(tb__ "0|1|
S0S6S5cS6aS6bS31S11bS31S11cSc9P96A1S2fZ3A1A3S2fZ1e0M0A1A3A3S1bS1eZ8S6dA2G0A2A3").
Proof using HC HMI HW Hb16 Hb3 Hhdr. apply (ze_idx8 (v 150) sc 480 ze150); [pose proof R_all; lia | lia]. Qed.

Lemma land_neg_mod32 : ltac2:(tb__ "0|1|
S6S1S1cZ0R1A2S1cR1S1dZ2Z20A2M0A2A2S0S6S23R2S1fS24R2A1G0A2A2Se7R2A1A3F_;Fm;").
Proof using Hb16 Hb3.
  intros m Hm. unfold lowbit. apply Z.bits_inj'. intros i Hi. rewrite !Z.land_spec.
  destruct (Z_lt_dec i 32).
  - rewrite Z.mod_pow2_bits_low by lia. reflexivity.
  - rewrite (testbit_false_of_lt m 32 i) by lia. reflexivity.
Qed.

Lemma first_eq : ltac2:(tb__ "0|0|
S0S6Se7S78A1S1dZ2S6eA2A3").
Proof using HC HW. pose proof Hidx as (_ & _ & E). unfold mf_first, avail in *. rewrite E. apply bit_eq. Qed.

Lemma pow_idx_range : ltac2:(tb__ "0|2|
S1S1aZ1S1dZ2M0S6eA2M1A2S1cG1S1dG0Z20A2A2A2").
Proof using HC HMI HW Hb16 Hb3 Hhdr.
  pose proof R_all as R. split.
  - change 1 with (2 ^ 0). apply Z.pow_le_mono_r; lia.
  - apply Z.pow_lt_mono_r; lia.
Qed.

Lemma ze_sxavail : ltac2:(tb__ "0|0|
S0S6S5cS6aS6bS3fSaQ20Sc9P98A1A3A3S61S78A1A3").
Proof using HC HMI HW Hb16 Hb3 Hhdr. rewrite ze_ext, ze152. reflexivity. Qed.

Lemma ze_lowbit : ltac2:(tb__ "0|0|
S0S6S5cS6aS6bSa2A3S61S1dZ2S6eA2A1A3").
Proof using HC HMI HW Hb16 Hb3 Hhdr.
  unfold E_lowbit. rewrite ze_alu, ze_aluw, !ze_sxavail, ze_lit. cbn [zalu]. pose proof R_all as R.
  rewrite sx32_mod32 by lia. change ((0 mod 2 ^ 64) mod 2 ^ 32) with 0.
  pose proof (sx32_range avail ltac:(lia)). pose proof (Z.mod_pos_bound (0 - avail) (2 ^ 32) ltac:(lia)) as M.
  pose proof (sx32_range ((0 - avail) mod 2 ^ 32) ltac:(lia)).
  rewrite !Z.mod_small by lia. rewrite sx32_land by lia. rewrite land_neg_mod32 by lia. rewrite first_eq. reflexivity.
Qed.

Lemma mulC_mod32 : ltac2:(tb__ "0|4|
S0S6S1fS1fS1eS61S1dZ2M0S6eA2M1A1Z77cb531M2A2S1dG0Z40A2A2S1dG0Z20A2M3A2S1fS1eG1G2A2G3A2A3").
Proof using HC HMI HW Hb16 Hb3 Hhdr.
  pose proof pow_idx_range as P.
  rewrite <- Znumtheory.Zmod_div_mod; [|lia|lia|exists (2 ^ 32); reflexivity].
  rewrite <- Z.mul_mod_idemp_l by lia. rewrite sx32_mod32 by lia. reflexivity.
Qed.

Lemma dbidx_range : ltac2:(tb__ "0|3|
S1S1aZ0S26S1fS1eS1dZ2M0S6eA2Z77cb531A2S1dG0Z20M1A2A2Z1bA2M2A2S1cG2G1A2A2").
Proof using Hb16 Hb3.
  pose proof (Z.mod_pos_bound (2 ^ idx * 125613361) (2 ^ 32) ltac:(lia)) as M.
  rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|].
  change (2 ^ 27 * 32) with (2 ^ 32). lia.
Qed.

Lemma ze_dbidx : ltac2:(tb__ "0|3|
S0S6S5cS6aS6bS43S11dS47S120Sa2S2fZ77cb531M0A1A3S2fZ1bM1A1A3A3S26S1fS1eS1dZ2M2S6eA2G0A2S1dG2Z20A2A2G1A2A3").
Proof using HC HMI HW Hb16 Hb3 Hhdr.
  rewrite ze_aluw, ze_mul, ze_lowbit, !ze_lit. cbn [zalu].
  change (((27 mod 2 ^ 64) mod 2 ^ 32) mod 32) with 27. change (125613361 mod 2 ^ 64) with 125613361.
  rewrite Z.mod_mod by lia. rewrite mulC_mod32. apply sx32_small. pose proof dbidx_range. lia.
Qed.

Lemma ze_T6 : ltac2:(tb__ "0|0|
S0S6S5cS6aS6bS16eA3S6eA3").
Proof using HC HMI HW Hb16 Hb3 Hhdr.
  change T6 with (SExt false 8 (SLBytes 4 (SAluW ALU_SRL (SMd M_MUL E_lowbit (SLit 125613361)) (SLit 27)) 1)).
  rewrite ze_ext. cbn [Z.of_N]. rewrite ze_lbytes, ze_dbidx, zl1_4.
  pose proof dbidx_range as D. pose proof R_all as R.
  set (j := Z.shiftr ((2 ^ idx * 125613361) mod 2 ^ 32) 27) in *.
  pose proof (ctz_lookup idx ltac:(lia)) as E. fold j in E.
  unfold zsublist. change (Z.to_nat 1) with 1%nat.
  assert (LEN : (Z.to_nat j < length ctz_tab_bytes)%nat) by (change (length ctz_tab_bytes) with 32%nat; lia).
  destruct (skipn (Z.to_nat j) ctz_tab_bytes) as [|b t] eqn:Es.
  - exfalso. pose proof (length_skipn (Z.to_nat j) ctz_tab_bytes) as SL. rewrite Es in SL. cbn in SL. lia.
  - cbn [firstn zle].
    assert (Eb : b = idx).
    { rewrite <- E. rewrite <- (Nat.add_0_r (Z.to_nat j)). rewrite <- nth_skipn. rewrite Es. reflexivity. }
    subst b. cbn [firstn zle]. rewrite (Z.mod_small idx 256) by lia. rewrite Z.mul_0_r, Z.add_0_r. rewrite !Z.mod_small; lia.
Qed.

Hypothesis Hsp : ltac2:(tb__ "0|1|
S1S1aZ1000Sb4Q40S32Vrho;PaA2A2M0A2S0S6S1fG0Z10A2Z0A3A2").
Hypothesis Hdepth : ltac2:(tb__ "0|1|
S1S1aS60Z40Sb4Q40S32Vrho;PfA2A2A2M0S24S183A1A2S1aS24S1dZ2Z28A2A1G0A2A2").
Hypothesis Hsp_high : ltac2:(tb__ "0|1|
S1aS17eVL;A1S1bSb4Q40M0S32Vrho;PaA2A2S60Z40Sb4G0S32Vrho;PfA2A2A2A2A2").

Ltac zfact := cbn [zholds zcond].

Lemma zr1_10 : ltac2:(tb__ "0|1|
S0S6S6aPaM0A1Sb4Q40S32Vrho;G0A2A2A3"). Proof using . reflexivity. Qed.
Lemma zr1_15 : ltac2:(tb__ "0|1|
S0S6S6aPfM0A1Sb4Q40S32Vrho;G0A2A2A3"). Proof using . reflexivity. Qed.

Lemma bits_mod32 : ltac2:(tb__ "0|0|
S1S0S6S1fS7bZ20A2SddVam;A1A3S0S6S27S7bZ1000A2SdcVam;A1A3A2").
Proof using HC HMI HW Hb16 Hb3 Hhdr Hsp.
  pose proof Hlast. pose proof R_all as R. rewrite bits_eq.
  set (l := am_last am) in *. set (c := sc) in *. set (m := am_maplen am) in *.
  split.
  - replace (l + 32 + 64 * c + 4096 * m) with (l + (1 + 2 * c + 128 * m) * 32) by lia.
    rewrite Z.mod_add by lia. apply Z.mod_small. lia.
  - replace (l + 32 + 64 * c + 4096 * m) with ((l + 32 + 64 * c) + m * 4096) by lia.
    rewrite Z.div_add by lia. rewrite Z.div_small by lia. lia.
Qed.

Lemma ze_last : ltac2:(tb__ "0|0|
S0S6S5cS6aS6bS31S11eSc9P9bA1S2fZ1fA1A3A3SddVam;A1A3").
Proof using HC HMI HW Hb16 Hb3 Hhdr Hsp.
  rewrite ze_alu, ze155, ze_lit. cbn [zalu]. pose proof bits_range. rewrite (Z.mod_small bits) by lia.
  change (31 mod 2 ^ 64) with 31. rewrite land_31. apply bits_mod32.
Qed.
Lemma ze_maplen : ltac2:(tb__ "0|0|
S0S6S5cS6aS6bS31S11dSc9P9bA1S2fZcA1A3A3SdcVam;A1A3").
Proof using HC HMI HW Hb16 Hb3 Hhdr Hsp.
  rewrite ze_alu, ze155, ze_lit. cbn [zalu]. pose proof bits_range. rewrite (Z.mod_small bits) by lia.
  change ((12 mod 2 ^ 64) mod 64) with 12. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 12) with 4096. apply bits_mod32.
Qed.

Lemma sp_sum : ltac2:(tb__ "0|4|
S0S6S1fS1bSb4Q40M0S32Vrho;PaA2A2M1Sb4G0S32Vrho;PfA2A2M2A2S1dZ2Z40M3A2A2S1bG1S60G3G2A2A2A3").
Proof using Hb16 Hb3 Hdepth Hsp Hsp_high.
  pose proof Hdepth as [D1 D2]. pose proof Hsp_high as SH. pose proof (urange (rw rho 10%positive)) as U10. pose proof (urange (rw rho 15%positive)) as U15.
  unfold malloc_stack in D1.
  unfold toS in *. rewrite (Z.mod_small (bv_unsigned (rw rho 15%positive)) (2 ^ 64)) in * by lia.
  change (2 ^ (64 - 1)) with (2 ^ 63) in *.
  destruct (bv_unsigned (rw rho 15%positive) <? 2 ^ 63) eqn:E; [apply Z.ltb_lt in E; lia|apply Z.ltb_ge in E].
  top_ranges.
  replace (bv_unsigned (rw rho 10%positive) + bv_unsigned (rw rho 15%positive))
    with ((bv_unsigned (rw rho 10%positive) + (bv_unsigned (rw rho 15%positive) - 2 ^ 64)) + 1 * 2 ^ 64) by lia.
  rewrite Z.mod_add by lia. rewrite Z.mod_small; lia.
Qed.

Theorem ZF_base : ltac2:(tb__ "0|0|
Sd9S2eS5eS6aS6bA2SabS72A1A3").
Proof using HC HMI HP12 HW Hb16 Hb3 Hdepth Hhdr Hsp Hsp_high.
  pose proof R_all as R. pose proof Hsp as [S1 S2]. pose proof Hdepth as [D1 D2]. pose proof Hsp_high as SH. unfold malloc_stack in D1.
  pose proof pow_idx_range as P. pose proof bits_range as B.
  unfold F_base.
  constructor. { zfact. rewrite zr1_10. split; [lia|]. rewrite (Z.mod_small _ (2 ^ 64)) by (pose proof (urange (rw rho 10%positive)); lia).
                 change (2 ^ 4) with 16. exact S2. }
  constructor. { zfact. rewrite ze_lit, ze_alu, !ze_var, zr1_10, zr1_15. cbn [zalu].
                 pose proof (urange (rw rho 10%positive)) as U10. pose proof (urange (rw rho 15%positive)) as U15.
                 rewrite !(Z.mod_small (bv_unsigned _) (2 ^ 64)) by lia. rewrite sp_sum. top_ranges.
                 change (140735332483072 mod 2 ^ 64) with 140735332483072. lia. }
  constructor. { zfact. rewrite ze_lit, ze_var, zr1_15. rewrite (toS_mod 64 (bv_unsigned (rw rho 15%positive))) by lia.
                 replace (toS 64 ((-752) mod 2 ^ 64)) with (-752) by reflexivity. apply Bool.negb_true_iff. apply Z.ltb_ge. lia. }
  constructor. { zfact. rewrite ze_lit, ze_var, zr1_15. rewrite (toS_mod 64 (bv_unsigned (rw rho 15%positive))) by lia.
                 replace (toS 64 ((- 2 ^ 40) mod 2 ^ 64)) with (- 2 ^ 40) by reflexivity. apply Bool.negb_true_iff. apply Z.ltb_ge. lia. }
  constructor. { zfact. rewrite ze12, ze_lit. change (131051 mod 2 ^ 64) with 131051. unfold MMAP_THRESHOLD in R. lia. }
  constructor. { zfact. rewrite ze150, ze_lit. change (47 mod 2 ^ 64) with 47. lia. }
  constructor. { zfact. rewrite ze151, ze_lit. change (0 mod 2 ^ 64) with 0. rewrite Z.eqb_eq. lia. }
  constructor. { zfact. rewrite ze153, ze_lit. change (4294967295 mod 2 ^ 64) with 4294967295. lia. }
  constructor. { zfact. rewrite ze152, ze_lit. change (4294967295 mod 2 ^ 64) with 4294967295. lia. }
  constructor. { zfact. rewrite ze151, ze_lit. change ((2 ^ 47) mod 2 ^ 64) with (2 ^ 47). lia. }
  constructor. { zfact. rewrite ze151, ze_lit. change (4096 mod 2 ^ 64) with 4096. lia. }
  constructor. { zfact. rewrite ze156, ze_lit. change ((2 ^ 47) mod 2 ^ 64) with (2 ^ 47). lia. }
  constructor. { zfact. rewrite ze156, ze_lit. change (4096 mod 2 ^ 64) with 4096. lia. }
  constructor. { zfact. rewrite ze157, ze_lit. change (31 mod 2 ^ 64) with 31. lia. }
  constructor. { zfact. rewrite ze142, ze_lit. change (255 mod 2 ^ 64) with 255. lia. }
  constructor. { zfact. rewrite ze143, ze_lit. change (65535 mod 2 ^ 64) with 65535. lia. }
  constructor. { zfact. rewrite ze_tabidx, ze_lit. change (94 mod 2 ^ 64) with 94. lia. }
  constructor. { zfact. rewrite ze_stride, ze_lit. change ((2 ^ 20) mod 2 ^ 64) with (2 ^ 20). lia. }
  constructor. { zfact. rewrite ze_stride, ze_lit. change (16 mod 2 ^ 64) with 16. lia. }
  constructor. { zfact. rewrite ze_alu, ze12, ze_lit, ze_stride. cbn [zalu]. change (4 mod 2 ^ 64) with 4. rewrite Z.mod_small; lia. }
  constructor. { zfact. rewrite ze_lowbit, ze_lit. change (0 mod 2 ^ 64) with 0. rewrite Z.eqb_eq.
                 intros E. apply (proj1 (sx32_zero_iff (2 ^ idx) ltac:(lia))) in E. lia. }
  constructor. { zfact. rewrite ze_dbidx, ze_lit. change (31 mod 2 ^ 64) with 31. pose proof dbidx_range. lia. }
  constructor.
Qed.

Theorem ZF_kind : ltac2:(tb__ "0|0|
Sd9S2eS5eS6aS6bA2SacS72A1A3").
Proof using HC HMI HW Hb16 Hb3 Hhdr Hsp.
  pose proof R_all as R. pose proof Hmaplen as M. unfold kd, kind_of.
  destruct (am_last am =? 0) eqn:El; [apply Z.eqb_eq in El; destruct (am_maplen am =? 0) eqn:Em; [apply Z.eqb_eq in Em|apply Z.eqb_neq in Em]|apply Z.eqb_neq in El]; cbn [F_kind].
  - constructor. { zfact. rewrite ze_last, ze_lit. change (0 mod 2 ^ 64) with 0. apply Z.eqb_eq. exact El. }
    constructor. { zfact. rewrite ze_maplen, ze_lit. change (0 mod 2 ^ 64) with 0. apply Z.eqb_eq. exact Em. }
    constructor.
  - constructor. { zfact. rewrite ze_last, ze_lit. change (0 mod 2 ^ 64) with 0. apply Z.eqb_eq. exact El. }
    constructor. { zfact. rewrite ze_maplen, ze_lit. change (0 mod 2 ^ 64) with 0. rewrite Z.eqb_eq. exact Em. }
    constructor.
  - constructor. { zfact. rewrite ze_last, ze_lit. change (0 mod 2 ^ 64) with 0. rewrite Z.eqb_eq. exact El. }
    constructor.
Qed.

Theorem ZF_all : ltac2:(tb__ "0|0|
Sd9S2eS5eS6aS6bA2Sa0S72A1A3").
Proof using HC HMI HP12 HW Hb16 Hb3 Hdepth Hhdr Hsp Hsp_high. unfold F_all. apply Forall_app. split; [apply ZF_base | apply ZF_kind]. Qed.

Theorem ZF5 : ltac2:(tb__ "0|0|
S0S9S79SaA3Sd9S2eS5eS6aS6bA2Sa1A3F_;").
Proof using HC HMI HW Hb16 Hb3 Hhdr Hsp.
  intros H. pose proof (RC_vals H) as (J & A0 & U0 & U1 & E). pose proof route_cases as [[X _]|(_ & _ & R & N6 & EV & _ & _ & _)]; [rewrite H in X; discriminate|].
  pose proof R_all as RA. pose proof Hu165 as R5. pose proof Hj164 as RJ.
  unfold F5. repeat apply Forall_cons; try apply Forall_nil; zfact.
  - split; [lia|]. rewrite zr1_164, J. rewrite (Z.mod_small sc0 (2 ^ 64)) by lia. change (2 ^ 1) with 2. rewrite Zeven_mod in EV. apply Z.eqb_eq in EV. exact EV.
  - rewrite ze_lit, ze164, J. change (4 mod 2 ^ 64) with 4. lia.
  - rewrite ze_lit, ze164, J. change (30 mod 2 ^ 64) with 30. rewrite Zeven_mod in EV. apply Z.eqb_eq in EV. lia.
  - rewrite ze_lit, ze164, J. change (6 mod 2 ^ 64) with 6. intros X. apply Z.eqb_eq in X. lia.
  - rewrite ze_lit, (ze166 H). change (0 mod 2 ^ 64) with 0. lia.
  - rewrite ze_lit, ze167, U0. change (0 mod 2 ^ 64) with 0. lia.
  - rewrite ze_lit, ze165. change (12 mod 2 ^ 64) with 12. lia.
  - rewrite ze_lit, ze_sxavail. change (0 mod 2 ^ 64) with 0. unfold sx32, toS.
    destruct (avail mod 2 ^ 32 <? 2 ^ (32 - 1)) eqn:X; [apply Z.ltb_lt in X|apply Z.ltb_ge in X]; rewrite Z.mod_small in X by lia;
      apply Bool.negb_true_iff; apply Z.eqb_neq; Z.to_euclidean_division_equations; lia.
Qed.

Lemma F5_supported : ltac2:(tb__ "0|0|
S0S9ScaS2eS5fSa1A3SaA3").
Proof using . vm_cast_no_check (@eq_refl bool true). Qed.

Lemma F_all_supported : ltac2:(tb__ "0|0|
S9cS0S9ScaS2eS5fSa0R1A1A3SaA3Fkd';").
Proof using . intros [| |]; vm_cast_no_check (@eq_refl bool true). Qed.

Theorem facts_hold : ltac2:(tb__ "0|0|
Sb3Q40A1SdSb3Q8A1A1F_;Sd9S2eS3dS6cR1A1A1Sa0S72A1A3Fm;").
Proof using HC HMI HP12 HW Hb16 Hb3 Hdepth Hhdr Hsp Hsp_high.
  intros m. apply Forall_holds_of_zholds; [apply F_all_supported|].
  apply Forall_forall. intros f Hf. apply (proj1 (zholds_ext zr1 (zr_of (rho1 m)) zl1 (zl_of (rho1 m)) f ltac:(intros; reflexivity) ltac:(intros; reflexivity))).
  exact (proj1 (Forall_forall _ _) ZF_all f Hf).
Qed.

Variable m0 : word -> option byte.
Hypothesis Erd : ltac2:(tb__ "0|0|
S0Sb3Q40A1SdSb3Q8A1A1F_;Vrd0;S119S67Vm0;A2A3").
Hypothesis Ewok : ltac2:(tb__ "0|0|
S0Sb3Q40A1S9F_;Vwok0;S11aS67Vm0;A2A3").
Variable ms : machine_state.
Hypothesis Hrom : rom_ok segsU ms.

Hypothesis Hm0_sct : ltac2:(tb__ "0|1|
S6S1S1aZ0R1A2S1cR1Z60A2A2S0SdSb3Q8A1M0A1Vm0;Sb2Q40S1bZ108ecR2A2A2A1S16G0A1A3F_;Fkk;").
Hypothesis Hm0_ctz : ltac2:(tb__ "0|1|
S6S1S1aZ0R1A2S1cR1Z20A2A2S0SdSb3Q8A1M0A1Vm0;Sb2Q40S1bZ108ccR2A2A2A1S16G0A1A3F_;Fkk;").

Hypothesis Hm3 : ltac2:(tb__ "0|2|
S0SdSb3Q8M0A1M1A1S119S67Vm0;Sb2Q40S20S77Z3A2A2A3S10G1Sb2G0Vb3;A2A2A3").
Hypothesis Hm16 : ltac2:(tb__ "0|3|
S17S186R1U2M0A2S0SdSb3Q8M1A1M2A1S119S67Vm0;Sb2Q40S1bS20S77Z2A2S25R2A1A2A2A3S10G2Sb2G1S126Vb16;G0R2A3A2A2A3F_;Fj;").

Let bv0 : byteview := ltac2:(tb__ "0|0|
S182S119S67Vm0;A2S11aS67Vm0;A2A2").

Lemma HMI0 : ltac2:(tb__ "0|0|
S189S17fS18aVs;VL;A2S119S67Vm0;A2S11aS67Vm0;A2Vvm;A5").
Proof using Erd Ewok HMI. rewrite <- Erd, <- Ewok. exact HMI. Qed.
Lemma HreprO : ltac2:(tb__ "0|0|
S194VL;Vs;Vbv0;A3"). Proof using Erd Ewok HMI. exact (proj1 (proj2 (proj2 (proj2 HMI0)))). Qed.
Lemma Hstat : ltac2:(tb__ "0|0|
S184S17fS182S119S67Vm0;A2Sb3Q40A1SaL_;A2Vbv0;A3").
Proof using Erd Ewok HMI. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 HMI0)))))). Qed.
Lemma Hctx : ly_ctx L = 0x5a3d0.
Proof using Erd Ewok HMI. exact (proj1 (proj2 (proj2 HMI0))). Qed.

Lemma cell_bytes0 : ltac2:(tb__ "0|4|
S122S6ScbS122R2S123Vs;A1A3S0SdS6A1S188VL;R3A2S10S6R2A2A3S17S186R1S127R5A1A2S1S1S1aZ0S1bS129VL;S12aR6A1A2S25R2A1A2M0A2S1cG0S1dZ2Z40A2A2A2S1S0S9S11aS67Vm0;Sb2Q40G0A2M1A3SaA3S0SdSb3Q8M2A1M3A1S119S67Vm0;G1A3S10G3Sb2G2S126R5S127R6A1R2A3A2A2A3A2A2F_;Fj;F_;F_;Fz;Fc;").
Proof using Erd Ewok HMI.
  intros c z Hc Hz j Hj.
  assert (CH : MallocInv.cell_holds L bv0 c) by exact (proj1 (Forall_forall _ _) (proj1 (proj2 (proj1 HreprO))) c Hc).
  exact (cell_bytes L _ _ c z CH Hz j Hj).
Qed.

Lemma cell_rw0 : ltac2:(tb__ "0|3|
S122S6S6S6S17ScbS122R5S123Vs;A1A3S0SdS6A1S188VL;R6A2S10S6R5A2A3S0S17S127R7A1R3A3S0S6S129VL;S12aR8A1A2S1bR6R5A2A3S6S1S1aS1bR8R7A2M0R1A2S1cR1S1bG0S25R6A1A2A2A2S1S0S9S11aS67Vm0;Sb2Q40M1R2A2A3SaA3S3Sb3Q8A1M2G2S0SdG2A1S119S67Vm0;Sb2G1R3A2A3S10G2R1A2A3Lbb;A2A2F_;Fx;F_;F_;F_;F_;Fkk;Foffs;Fb;Fz;Fc;").
Proof using Erd Ewok HMI Hb16 Hb3 Hsp.
  intros c z b offs kk Hc Hz Hw Ha x Hx.
  destruct (cell_bytes0 c z Hc Hz (Z.to_nat (x - (b + offs))) ltac:(rewrite Hw; lia)) as (_ & W & R).
  rewrite Ha in W, R. rewrite Z2Nat.id in W, R by lia. replace (b + offs + (x - (b + offs))) with x in W, R by lia.
  split; [exact W | eexists; exact R].
Qed.

Lemma ev1 : ltac2:(tb__ "0|2|
Sb3Q40M0A1M1SdSb3Q8A1A1F_;S2dS0S9S5dR1A1SaA3S0G1S3cS6cR3A1R2A2Sb2G0S5cS6aS6bR2A3A2A3F_;Fe;Fm;").
Proof using .
  intros m e He. rewrite <- (zr1_zl1_any m). rewrite <- (eval_zeval (rho1 m) e He). symmetry. apply Z_to_bv_bv_unsigned.
Qed.
Lemma ev1u : ltac2:(tb__ "0|1|
Sb3Q40M0A1SdSb3Q8A1A1F_;S2dS0S9S5dR1A1SaA3S0S6Sb4G0S3cS6cR3A1R2A2A2S5cS6aS6bR2A3A3F_;Fe;Fm;").
Proof using . intros m e He. rewrite <- (zr1_zl1_any m). apply eval_zeval. exact He. Qed.

Lemma cell_view0 : ltac2:(tb__ "0|4|
S122S6S6S6S17S2dScbS122R6S123Vs;A1A3S0SdS6A1S188VL;R7A2S10S6R6A2A3S0S17S127R8A1R4A3S187R5U8A2S0S6S129VL;S12aRaA1A2S1bR8R7A2A3S0Sb3Q40M0A1S3cS6cVm0;A1M1R6A2Sb2G0RaA2A3S17S186R1R9A2S0SdSb3Q8M2A1M3A1S119S67Vm0;Sb2G0S1bS1bRcRbA2S25R2A1A2A2A3S10G3SdaG3R2S50RaS3cG1R9A2A2Sb2G2Z0A2A4A2A3F_;Fj;F_;F_;F_;F_;F_;F_;Fe;Fkk;Foffs;Fb;Fz;Fc;").
Proof using Erd Ewok HMI.
  intros c z b offs kk e Hc Hz Hw Hk Ha He j Hj.
  destruct (cell_bytes0 c z Hc Hz j ltac:(rewrite Hw; exact Hj)) as (_ & _ & R).
  rewrite Ha in R. rewrite R, He, Hw. rewrite nth_enc_bytes by assumption. reflexivity.
Qed.

Definition Q_nl : sobj := U.Mal_malloc__G1.Mal_malloc_fast_runs.O_nl MR_P.
Definition Q_lock : sobj := U.Mal_malloc__G1.Mal_malloc_fast_runs.O_lock MR_P.
Definition Q_ctr : sobj := U.Mal_malloc__G1.Mal_malloc_fast_runs.O_ctr MR_P.
Definition Q_act : sobj := U.Mal_malloc__G1.Mal_malloc_fast_runs.O_act MR_P.
Definition Q_sct : sobj := U.Mal_malloc__G1.Mal_malloc_fast_runs.O_sct MR_P.
Definition Q_ctz : sobj := U.Mal_malloc__G1.Mal_malloc_fast_runs.O_ctz MR_P.
Definition Q_meta : sobj := U.Mal_malloc__G1.Mal_malloc_fast_runs.O_meta.
Definition Q_slot : sobj := U.Mal_malloc__G1.Mal_malloc_fast_runs.O_slot kd.
Definition Q_act0 : sobj := U.Mal_malloc__G1.Mal_malloc_fast_runs.O_act0 MR_P.
Definition Q_usg0 : sobj := U.Mal_malloc__G1.Mal_malloc_fast_runs.O_usg0 MR_P.
Definition Q_usg1 : sobj := U.Mal_malloc__G1.Mal_malloc_fast_runs.O_usg1 MR_P.
Definition Q_stk : sobj := U.Mal_malloc__G1.Mal_malloc_fast_runs.O_stk.

Ltac cells_inside_tac := unfold cells_inside; repeat constructor; cbn; lia.

Lemma libc_byte0 : ltac2:(tb__ "0|2|
S0SdSb3Q8M0A1M1A1S119S67Vm0;Sb2Q40Z5a35bA2A3S10G1Sb2G0Z0A2A2A3").
Proof using Erd Ewok HMI Hb16 Hb3 rho.
  destruct Hstat as (NL & _). unfold holds, mc_need_locks in NL. cbn [mc_libc C_U] in NL.
  specialize (NL 0%nat ltac:(lia)). cbn [Z.of_nat] in NL. rewrite Z.add_0_r in NL.
  destruct (byteview_of_Some _ _ _ _ NL) as (_ & _ & b & Hb & E).
  change (369496 + 3) with 369499 in Hb. rewrite Hb. f_equal.
  rewrite <- (Z_to_bv_bv_unsigned 8 b). rewrite <- E. reflexivity.
Qed.

Lemma lock_bytes0 : ltac2:(tb__ "0|3|
S17S186R1U4A2S1S0S9S11aS67Vm0;Sb2Q40S1bZ5a3c8S25R2A1A2A2M0A3SaA3S0SdSb3Q8M1A1M2A1S119S67Vm0;G0A3S10G2Sb2G1Z0A2A2A3A2F_;Fkk;").
Proof using Erd Ewok HMI Hb16 Hb3 rho.
  intros kk Hk. destruct Hstat as (_ & _ & _ & LK & _). unfold holds in LK. cbn [mc_lock C_U] in LK.
  specialize (LK kk Hk).
  destruct (byteview_of_Some _ _ _ _ LK) as (_ & W & b & Hb & E). split; [exact W|]. rewrite Hb. f_equal.
  rewrite <- (Z_to_bv_bv_unsigned 8 b). rewrite <- E. unfold le_byte. rewrite Z.mod_0_l, Z.shiftr_0_l by (apply Z.pow_nonzero; lia). reflexivity.
Qed.

Lemma hold_nl : ltac2:(tb__ "0|0|
S36S67S6cVm0;A1S117Vms;Vm0;A2S8bA4").
Proof using Erd Ewok HC HMI HW Hb16 Hb3 Hhdr Hrom.
  pose proof R_all as R.
  change Q_nl with (carved (SLit 0x5a35b) 0 1 [(0, 1%nat, SLit 0)]).
  assert (B : bv_unsigned (eval (rho1 m0) (SLit 0x5a35b)) = 0x5a35b) by (cbn [eval]; apply u64; lia).
  apply obj_holds_frame_lit; rewrite ?B; try exact Hrom; try lia.
  - cells_inside_tac.
  - intros o Ho. replace o with 0 by lia. rewrite Z.add_0_r. split; [|exists (Z_to_bv 8 0); exact libc_byte0].
    unfold Glue.wok_of. destruct (m0 (Z_to_bv 64 0x5a35b)); [reflexivity|]. vm_compute. reflexivity.
  - unfold cells_in_view. constructor; [|constructor]. intros j Hj. replace j with 0%nat by lia.
    cbn [Z.of_nat]. rewrite !Z.add_0_r. exact libc_byte0.
Qed.

Lemma hold_lock : ltac2:(tb__ "0|0|
S36S67S6cVm0;A1S117Vms;Vm0;A2S89A4").
Proof using Erd Ewok HC HMI HW Hb16 Hb3 Hhdr Hrom Hsp.
  pose proof R_all as R.
  change Q_lock with (carved (SLit 0x5a3c8) 0 4 [(0, 4%nat, SLit 0)]).
  assert (B : bv_unsigned (eval (rho1 m0) (SLit 0x5a3c8)) = 0x5a3c8) by (cbn [eval]; apply u64; lia).
  apply obj_holds_frame_lit; rewrite ?B; try exact Hrom; try lia.
  - cells_inside_tac.
  - intros o Ho. destruct (lock_bytes0 (Z.to_nat o) ltac:(lia)) as [W RD]. rewrite Z2Nat.id in W, RD by lia.
    split; [exact W | exists (Z_to_bv 8 0); exact RD].
  - unfold cells_in_view. constructor; [|constructor]. intros j Hj. rewrite Z.add_0_r.
    destruct (lock_bytes0 j Hj) as [_ RD]. rewrite RD.
    do 4 (destruct j as [|j]; [reflexivity|]). lia.
Qed.

Lemma Cctr : ltac2:(tb__ "0|0|
ScbS122S124S125S12eA1U4S12cSecVs;A1A1A3S123Vs;A1A3").
Proof using Hb16 Hb3 Hdepth Hsp. unfold image. apply in_app_iff. left. unfold ctx_cells. cbn. tauto. Qed.

Lemma Cact : ltac2:(tb__ "0|0|
ScbS122S124S125S1bS12bS1eZ8S6dA2A2A1U8S132Vg;A1A3S123Vs;A1A3").
Proof using HC HMI HW Hb16 Hb3 Hhdr Hsp.
  pose proof R_all as R. unfold image. apply in_app_iff. left. unfold ctx_cells.
  apply in_app_iff. right. apply in_app_iff. left. apply in_map_iff. exists (Z.to_nat sc).
  rewrite Z2Nat.id by lia. split.
  - pose proof Hact as A. pose proof Hsc as (E & _). unfold sc in *. rewrite <- E in A. rewrite A. reflexivity.
  - apply in_seq. lia.
Qed.

Lemma le_byte_mod32 : ltac2:(tb__ "0|1|
S6S17S186R1U4M0A2S0S6S126S1fR3S1dZ2Z20A2A2G0R2A3S126R3G0R2A3A3F_;Fj;Fx;").
Proof using Hb16 Hb3 rho. intros x j Hj. unfold le_byte. change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32). rewrite Z.mod_mod by lia. reflexivity. Qed.

Lemma hold_ctr : ltac2:(tb__ "0|0|
S36S67S6cVm0;A1S117Vms;Vm0;A2S87A4").
Proof using Erd Ewok HC HMI HW Hb16 Hb3 Hdepth Hhdr Hrom Hsp.
  pose proof R_all as R. pose proof Hctx as HCX.
  change Q_ctr with (carved (SLit 0x5a3c8) 20 24 [(20, 4%nat, v 153)]).
  assert (B : bv_unsigned (eval (rho1 m0) (SLit 0x5a3c8)) = 0x5a3c8) by (cbn [eval]; apply u64; lia).
  assert (AD : loc_addr L (mc_loc (MCell (LCtx CTX_mmap_counter) 4 (VZ (st_mmap_counter s)))) = 0x5a3c8 + 20).
  { cbn [mc_loc loc_addr]. rewrite HCX. reflexivity. }
  apply obj_holds_frame_lit; rewrite ?B; try exact Hrom; try lia.
  - cells_inside_tac.
  - intros o Ho. apply (cell_rw0 _ (st_mmap_counter s) 0x5a3c8 20 4 Cctr eq_refl eq_refl AD). lia.
  - unfold cells_in_view. constructor; [|constructor]. intros j Hj.
    destruct (cell_bytes0 _ (st_mmap_counter s) Cctr eq_refl j Hj) as (_ & _ & RD). rewrite AD in RD. cbn [mc_w] in RD.
    rewrite RD. rewrite (ev1 m0 (v 153) eq_refl), ze153. rewrite nth_enc_bytes by lia. unfold ctr. rewrite le_byte_mod32 by exact Hj. reflexivity.
Qed.

Lemma soff_of_ev : ltac2:(tb__ "0|0|
S2dS6S0S9S5dR2A1SaA3S0S6S5cS6aS6bR3A3R2A3S1S1aZ0R3A2S1cR3S1dZ2Z3fA2A2A2S0S6S4dS6cVm0;A1R5A2R4A3F_;F_;F_;Fz;Fe;").
Proof using Hb16 Hb3.
  intros e z Hs Hz Hr. unfold soff. rewrite (ev1 m0 e Hs), Hz. rewrite bv_signed_toS by (cbn; lia). change (Z.of_N 64) with 64.
  rewrite u64 by lia. unfold toS. rewrite Z.mod_small by lia. change (2 ^ (64 - 1)) with (2 ^ 63).
  replace (z <? 2 ^ 63) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.

Lemma hold_act : ltac2:(tb__ "0|0|
S36S67S6cVm0;A1S117Vms;Vm0;A2S85A4").
Proof using Erd Ewok HC HMI HW Hb16 Hb3 Hhdr Hrom Hsp.
  pose proof R_all as R. pose proof Hctx as HCX.
  assert (B : bv_unsigned (eval (rho1 m0) (SLit 0x5a3c8)) = 0x5a3c8) by (cbn [eval]; apply u64; lia).
  assert (AD : loc_addr L (mc_loc (MCell (LCtx (CTX_active + 8 * sc)) 8 (VP g))) = 0x5a3c8 + (8 * sc + 88)).
  { cbn [mc_loc loc_addr]. rewrite HCX. unfold CTX_active. lia. }
  apply (obj_holds_sem segsU (rho1 m0) (with_mem ms m0) (carved (SLit 0x5a3c8) (8 * sc + 88) (8 * sc + 96) [(8 * sc + 88, 8%nat, v 151)])).
  - reflexivity.
  - cbn [ob_lo carved Q_act U.Mal_malloc__G1.Mal_malloc_fast_runs.O_act]. rewrite soff_lit_small by lia. apply soff_of_ev; [reflexivity | apply ze_actoff | lia].
  - cbn [ob_hi carved Q_act U.Mal_malloc__G1.Mal_malloc_fast_runs.O_act]. rewrite soff_lit_small by lia. apply soff_of_ev; [reflexivity | apply ze_acthi | lia].
  - reflexivity.
  - cbn [ob_cells carved Q_act U.Mal_malloc__G1.Mal_malloc_fast_runs.O_act map]. constructor; [|constructor].
    split; [|split; reflexivity]. cbn [c_off]. rewrite soff_lit_small by lia. apply soff_of_ev; [reflexivity | apply ze_actoff | lia].
  - apply obj_holds_frame_lit; rewrite ?B; try exact Hrom; try lia.
    + cells_inside_tac.
    + intros o Ho. apply (cell_rw0 _ zG 0x5a3c8 (8 * sc + 88) 8 Cact eq_refl eq_refl AD). lia.
    + unfold cells_in_view. constructor; [|constructor]. intros j Hj.
      apply (cell_view0 _ zG 0x5a3c8 (8 * sc + 88) 8 (v 151) Cact eq_refl eq_refl ltac:(lia) AD); [|exact Hj].
      rewrite (ev1 m0) by reflexivity. rewrite ze151. reflexivity.
Qed.

Lemma Cact0 : ltac2:(tb__ "0|0|
ScbS122S124S125S1bS12bS1eZ8S70A2A2A1U8S12dSdaSdSdbA1S22S70A1SdeVs;A1S16SdbA1A4A1A3S123Vs;A1A3").
Proof using HC HW Hb16 Hb3 Hsp.
  pose proof Hj164 as R. unfold image. apply in_app_iff. left. unfold ctx_cells.
  apply in_app_iff. right. apply in_app_iff. left. apply in_map_iff. exists (Z.to_nat j164).
  rewrite Z2Nat.id by lia. split; [reflexivity | apply in_seq; lia].
Qed.
Lemma Cusg : ltac2:(tb__ "0|0|
S6S1S1aZ0R1A2S1cR1Z30A2A2ScbS122S124S125S1bS12fS1eZ8R2A2A2A1U8S12cSe1Vs;R2A2A1A3S123Vs;A1A3F_;Fj;").
Proof using Hb16 Hb3 Hsp.
  intros j Hj. unfold image. apply in_app_iff. left. unfold ctx_cells.
  apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. left. apply in_map_iff. exists (Z.to_nat j).
  rewrite Z2Nat.id by lia. split; [unfold usage_of, znth; reflexivity | apply in_seq; lia].
Qed.
Lemma cellZ_act0 : ltac2:(tb__ "0|0|
S0SdS6A1S188VL;S124S125S1bS12bS1eZ8S70A2A2A1U8S12dSdaSdSdbA1S22S70A1SdeVs;A1S16SdbA1A4A1A3A2S10S6S90A2A3").
Proof using . unfold a166, cellZ. cbn [mc_val]. destruct (nth (Z.to_nat j164) (st_active s) None) as [q|]; reflexivity. Qed.

Lemma hold_ctx8 : ltac2:(tb__ "0|6|
S33S2dS2dS7S6S6S122S0S33R7S45S2fZ5a3c8M0A1R6R5SfS40S51R6Z8M1Sc9R4A1A3S12S40A1A3S46A5A3S0S9S5dR7A1SaA3M2G2S0S6S5cS6aS6bR9A3M3R6A3S0S6G3S1bR7G1A2A3S1S1aZ58R8A2S1cR8Z3e8A2A2ScbS122R7S123Vs;A1A3S0SdS6A1S188VL;R8A2S10S6R9A2A3S0S17S127R9A1U8A3S0S6S129VL;S12aRaA1A2S1bG0RcA2A3S0Sb3Q40M4A1S3cS6cVm0;A1M5Sc9ReA1A2Sb2G4RcA2A3S36S67G5S117Vms;Vm0;A2R12A4F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fc;Fz;Foff;Fvv;Fehi;Felo;FQ;").
Proof using Erd Ewok HMI Hb16 Hb3 Hrom Hsp.
  intros Q elo ehi vv off z c -> Slo Shi Elo Ehi Hoff Hc Hz Hw AD Ev.
  assert (B : bv_unsigned (eval (rho1 m0) (SLit 0x5a3c8)) = 0x5a3c8) by (cbn [eval]; apply u64; lia).
  apply (obj_holds_sem segsU (rho1 m0) (with_mem ms m0) (carved (SLit 0x5a3c8) off (off + 8) [(off, 8%nat, v vv)])).
  - reflexivity.
  - cbn [ob_lo carved]. rewrite soff_lit_small by lia. apply soff_of_ev; [exact Slo | exact Elo | lia].
  - cbn [ob_hi carved]. rewrite soff_lit_small by lia. apply soff_of_ev; [exact Shi | exact Ehi | lia].
  - reflexivity.
  - cbn [ob_cells carved map]. constructor; [|constructor].
    split; [|split; reflexivity]. cbn [c_off]. rewrite soff_lit_small by lia. apply soff_of_ev; [exact Slo | exact Elo | lia].
  - apply obj_holds_frame_lit; rewrite ?B; try exact Hrom; try lia.
    + cells_inside_tac.
    + intros o Ho. apply (cell_rw0 _ z 0x5a3c8 off 8 Hc Hz Hw AD). lia.
    + unfold cells_in_view. constructor; [|constructor]. intros j Hj.
      apply (cell_view0 _ z 0x5a3c8 off 8 (v vv) Hc Hz Hw ltac:(lia) AD); [exact Ev | exact Hj].
Qed.

Lemma hold_act0 : ltac2:(tb__ "0|0|
S36S67S6cVm0;A1S117Vms;Vm0;A2S86A4").
Proof using Erd Ewok HC HMI HW Hb16 Hb3 Hhdr Hrom Hsp.
  pose proof Hj164 as R. pose proof Hctx as HCX.
  eapply (hold_ctx8 Q_act0 _ _ 166%positive (8 * j164 + 88) a166); [reflexivity | reflexivity | reflexivity | apply ze_act0off | rewrite ze_act0hi; lia | lia
    | apply Cact0 | apply cellZ_act0 | reflexivity | cbn [mc_loc loc_addr]; rewrite HCX; unfold CTX_active; lia |].
  unfold rho1. cbn [eval rw rw1 Pos.eqb]. reflexivity.
Qed.
Lemma hold_usg0 : ltac2:(tb__ "0|0|
S36S67S6cVm0;A1S117Vms;Vm0;A2S8eA4").
Proof using Erd Ewok HC HMI HW Hb16 Hb3 Hhdr Hrom Hsp.
  pose proof Hj164 as R. pose proof Hctx as HCX.
  eapply (hold_ctx8 Q_usg0 _ _ 167%positive (8 * j164 + 472) u167); [reflexivity | reflexivity | reflexivity | apply ze_usg0off | rewrite ze_usg0hi; lia | lia
    | apply (Cusg j164); lia | reflexivity | reflexivity | cbn [mc_loc loc_addr]; rewrite HCX; unfold CTX_usage; lia |].
  unfold rho1. cbn [eval rw rw1 Pos.eqb]. reflexivity.
Qed.
Lemma hold_usg1 : ltac2:(tb__ "0|0|
S36S67S6cVm0;A1S117Vms;Vm0;A2S8fA4").
Proof using Erd Ewok HC HMI HW Hb16 Hb3 Hhdr Hrom Hsp.
  pose proof R_all as R. pose proof Hctx as HCX.
  eapply (hold_ctx8 Q_usg1 _ _ 165%positive (8 * sc + 472) u165); [reflexivity | reflexivity | reflexivity | apply ze_usg1off | rewrite ze_usg1hi; lia | lia
    | apply (Cusg sc); lia | reflexivity | reflexivity | cbn [mc_loc loc_addr]; rewrite HCX; unfold CTX_usage; lia |].
  unfold rho1. cbn [eval rw rw1 Pos.eqb]. reflexivity.
Qed.

Lemma sctab_image : ltac2:(tb__ "0|3|
S6S1S1aZ0M0R1A2S1cR1Z60A2A2S0SdSb3Q8M1A1M2A1S4aS67Sb2Q40S1bZ108ecR2A2A2A2S10G2SdaG2S22R2A1S3eS6cVm0;A1P1A2Sb2G1G0A2A4A2A3F_;Fkk;").
Proof using Hb16 Hb3.
  intros kk Hk.
  pose proof (forall_range_dec (fun kk => match image_byte segsU (Z_to_bv 64 (0x108ec + kk)) with
                                         | Some b => bv_eqb b (nth (Z.to_nat kk) (map (Z_to_bv 8) size_classes_bytes) (Z_to_bv 8 0))
                                         | None => false end) 0 96 ltac:(vm_compute; reflexivity) kk ltac:(lia)) as H.
  cbn beta in H. cbn [rl rho1 rl1 Pos.eqb].
  destruct (image_byte segsU (Z_to_bv 64 (67820 + kk))) as [b|]; [|discriminate].
  f_equal. unfold bv_eqb in H. apply Z.eqb_eq in H. apply bv_eq. exact H.
Qed.

Lemma ctztab_image : ltac2:(tb__ "0|3|
S6S1S1aZ0M0R1A2S1cR1Z20A2A2S0SdSb3Q8M1A1M2A1S4aS67Sb2Q40S1bZ108ccR2A2A2A2S10G2SdaG2S22R2A1S3eS6cVm0;A1P4A2Sb2G1G0A2A4A2A3F_;Fkk;").
Proof using Hb16 Hb3.
  intros kk Hk.
  pose proof (forall_range_dec (fun kk => match image_byte segsU (Z_to_bv 64 (0x108cc + kk)) with
                                         | Some b => bv_eqb b (nth (Z.to_nat kk) (map (Z_to_bv 8) ctz_tab_bytes) (Z_to_bv 8 0))
                                         | None => false end) 0 32 ltac:(vm_compute; reflexivity) kk ltac:(lia)) as H.
  cbn beta in H. cbn [rl rho1 rl1 Pos.eqb].
  destruct (image_byte segsU (Z_to_bv 64 (67788 + kk))) as [b|]; [|discriminate].
  f_equal. unfold bv_eqb in H. apply Z.eqb_eq in H. apply bv_eq. exact H.
Qed.

Lemma hold_sct : ltac2:(tb__ "0|0|
S36S67S6cVm0;A1S117Vms;Vm0;A2S8cA4").
Proof using Hb16 Hb3 Hm0_sct Hrom.
  unfold Q_sct, U.Mal_malloc__G1.Mal_malloc_fast_runs.O_sct. cbn [mr_sct MR_P].
  apply obj_holds_frame_rom; try exact Hrom; try lia.
  - reflexivity.
  - intros kk Hk. split; [apply Hm0_sct; exact Hk | apply sctab_image; exact Hk].
Qed.

Lemma hold_ctz : ltac2:(tb__ "0|0|
S36S67S6cVm0;A1S117Vms;Vm0;A2S88A4").
Proof using Hb16 Hb3 Hm0_ctz Hrom.
  unfold Q_ctz, U.Mal_malloc__G1.Mal_malloc_fast_runs.O_ctz. cbn [mr_ctz MR_P].
  apply obj_holds_frame_rom; try exact Hrom; try lia.
  - reflexivity.
  - intros kk Hk. split; [apply Hm0_ctz; exact Hk | apply ctztab_image; exact Hk].
Qed.

Lemma hold_meta : ltac2:(tb__ "0|0|
S36S67S6cVm0;A1S117Vms;Vm0;A2S8aA4").
Proof using Erd Ewok HC HMI HW Hb16 Hb3 Hhdr Hrom Hsp.
  pose proof R_all as R.
  pose proof (meta_cells_old C_U s L n g am zz rd0 wok0 vm HMI HC Hzz) as (C5 & C6 & C7 & C8 & _).
  change Q_meta with (carved (v 151) 16 40 [(16, 8%nat, v 156); (24, 4%nat, v 152); (28, 4%nat, v 154); (32, 8%nat, v 155)]).
  assert (B : bv_unsigned (eval (rho1 m0) (v 151)) = zG) by (rewrite ev1u by reflexivity; apply ze151).
  assert (AG : forall d, loc_addr L (LMem (padd g d)) = zG + d) by (intros d; unfold zG, addr_of, loc_addr; destruct g; cbn [padd]; lia).
  apply obj_holds_frame_lit; rewrite ?B; try exact Hrom; try lia.
  - cells_inside_tac.
  - intros o Ho.
    destruct (Z_lt_dec o 24) as [O1|O1]; [|destruct (Z_lt_dec o 28) as [O2|O2]; [|destruct (Z_lt_dec o 32) as [O3|O3]]].
    + apply (cell_rw0 _ zMem zG 16 8 C5 eq_refl eq_refl); [apply AG|lia].
    + apply (cell_rw0 _ avail zG 24 4 C6 eq_refl eq_refl); [apply AG|lia].
    + apply (cell_rw0 _ freed zG 28 4 C7 eq_refl eq_refl); [apply AG|lia].
    + apply (cell_rw0 _ bits zG 32 8 C8 eq_refl eq_refl); [apply AG|lia].
  - unfold cells_in_view. constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]].
    + apply (cell_view0 _ zMem zG 16 8 _ C5 eq_refl eq_refl ltac:(lia)); [apply AG|]. rewrite ev1 by reflexivity. rewrite ze156. reflexivity.
    + apply (cell_view0 _ avail zG 24 4 _ C6 eq_refl eq_refl ltac:(lia)); [apply AG|]. rewrite ev1 by reflexivity. rewrite ze152. reflexivity.
    + apply (cell_view0 _ freed zG 28 4 _ C7 eq_refl eq_refl ltac:(lia)); [apply AG|]. rewrite ev1 by reflexivity. rewrite ze154. reflexivity.
    + apply (cell_view0 _ bits zG 32 8 _ C8 eq_refl eq_refl ltac:(lia)); [apply AG|]. rewrite ev1 by reflexivity. rewrite ze155. reflexivity.
Qed.

Lemma slot_rw : ltac2:(tb__ "0|2|
S6S1S1aS20S77Z4A2R1A2S1cR1S84A2A2S1S0S9S11aS67Vm0;Sb2Q40M0R2A2A3SaA3S3Sb3Q8A1M1G1S0SdG1A1S119S67Vm0;Sb2G0R3A2A3S10G1R1A2A3Lbb;A2A2F_;Fx;").
Proof using Erd Ewok HC HMI Hb16 Hb3.
  intros x Hx.
  pose proof (slot_owned C_U s L n g am zz rd0 wok0 vm HMI HC Hzz x) as OW.
  unfold f_st, f_e, f_idx in OW. fold idx in OW. fold zSt zE in OW. specialize (OW Hx).
  pose proof (proj2 (proj2 (proj1 HreprO)) x OW) as M. unfold bv0 in M.
  destruct (byteview_of (Glue.rd_of segsU m0) (Glue.wok_of segsU m0) x) as [vv|] eqn:E; [|exfalso; exact (M eq_refl)].
  destruct (byteview_of_Some _ _ _ _ E) as (_ & W & bb & Hb & _). split; [exact W | exists bb; exact Hb].
Qed.

Lemma Ccheck : ltac2:(tb__ "0|0|
ScbS122S124S130Sf2SeaVam;S6eA2N4A2A1U1S12cZ0A1A3S123Vs;A1A3").
Proof using HC HMI HW Hb16 Hb3 Hhdr rho. pose proof R_all. exact (proj1 (slot_start_cells s g am idx HW Hum ltac:(lia))). Qed.

Lemma hold_slot : ltac2:(tb__ "0|0|
S36S67S6cVm0;A1S117Vms;Vm0;A2S8dA4").
Proof using Erd Ewok HC HMI HW Hb16 Hb3 Hhdr Hm16 Hm3 Hrom Hsp.
  pose proof R_all as R.
  assert (B : bv_unsigned (eval (rho1 m0) (E_p0 kd)) = zSt) by (rewrite ev1u by (destruct kd; reflexivity); apply ze_p0).
  assert (AS : forall d, loc_addr L (LMem (padd (slot_start am idx) d)) = zSt + d)
    by (intros d; unfold zSt, addr_of, loc_addr; destruct (slot_start am idx); cbn [padd]; lia).
  apply (obj_holds_sem segsU (rho1 m0) (with_mem ms m0) (carved (E_p0 kd) (-4) (stv - 4) [((-4), 1%nat, SLit 0); ((-3), 1%nat, v 142); ((-2), 2%nat, v 143)])).
  - reflexivity.
  - cbn [ob_lo carved Q_slot U.Mal_malloc__G1.Mal_malloc_fast_runs.O_slot]. reflexivity.
  - cbn [ob_hi carved Q_slot U.Mal_malloc__G1.Mal_malloc_fast_runs.O_slot]. rewrite soff_lit_small by lia. apply soff_of_ev; [destruct kd; reflexivity | apply ze_hi | lia].
  - reflexivity.
  - cbn [ob_cells carved Q_slot U.Mal_malloc__G1.Mal_malloc_fast_runs.O_slot map]. repeat constructor.
  - apply obj_holds_frame_lit; rewrite ?B; try exact Hrom; try lia.
    + cells_inside_tac.
    + intros o Ho. apply slot_rw. lia.
    + unfold cells_in_view. constructor; [|constructor; [|constructor; [|constructor]]].
      * apply (cell_view0 _ 0 zSt (-4) 1 (SLit 0) Ccheck eq_refl eq_refl ltac:(lia)); [apply AS | reflexivity].
      * intros j Hj. replace j with 0%nat by lia. cbn [Z.of_nat]. rewrite Z.add_0_r.
        replace (zSt + -3) with (zSt - 3) by lia. rewrite Hm3. rewrite (ev1 m0 (v 142) eq_refl), ze142, nth_enc_bytes by lia.
        do 2 f_equal. unfold le_byte. change (2 ^ (8 * Z.of_nat 1)) with 256. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r, Z.mod_mod by lia. symmetry. apply Z.mod_small. lia.
      * intros j Hj. replace (zSt + -2 + Z.of_nat j) with (zSt - 2 + Z.of_nat j) by lia. rewrite Hm16 by exact Hj.
        rewrite (ev1 m0 (v 143) eq_refl), ze143, nth_enc_bytes by lia. reflexivity.
Qed.

Definition sp0 : Z := bv_unsigned (rw rho 10%positive).
Definition D0 : Z := ltac2:(tb__ "0|0|
S60Z40Sb4Q40S32Vrho;PfA2A2A2").

Lemma soff1_lit : ltac2:(tb__ "0|1|
Sb3Q40A1SdSb3Q8A1A1F_;S6S1S1aS24S1dZ2Z3eA2M0A1R1A2S1aR1G0A2A2S0S6S4dS6cR3A1S2fR2A1A2R2A3F_;Fz;Fm;").
Proof using Hb16 Hb3. intros. apply soff_lit_small. lia. Qed.

Lemma rng_lit : ltac2:(tb__ "0|3|
Sb3Q40M0A1SdSb3Q8A1A1F_;S2dS6S6ScS40A1S53S6S1S1aS24S1dZ2Z3eA2M1A1R5A2S1aR5G1A2A2M2G2S0S6Sb4G0S3cS6cR9A1R8A2A2R3A3S0SbS6S6A2S34S6cRaA1S45R9S2fR8A1S2fR7A1R6R5A5A2SeS6S6S1bR4R8A2S1bR4R7A2A4A3F_;F_;F_;Fb;Fd;Fcs;Fhi;Flo;Fbase;Fm;").
Proof using Hb16 Hb3.
  intros m base lo hi cs d b Hlo Hhi Hb. unfold obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi].
  rewrite Hb, !soff1_lit by lia. reflexivity.
Qed.

Lemma rng_stk : ltac2:(tb__ "0|0|
S0SbS6S6A2S34S6cVm0;A1S81A2SeS6S6S1bS93S96A2S93A4A3").
Proof using Hb16 Hb3.
  unfold obj_range, obj_lo_of, obj_hi_of, Q_stk, U.Mal_malloc__G1.Mal_malloc_fast_runs.O_stk. cbn [ob_base ob_lo ob_hi]. cbn [eval rho1 rw rw1 Pos.eqb].
  rewrite soff1_lit by lia. unfold soff. cbn [eval rho1 rw rw1 v Pos.eqb]. rewrite bv_signed_toS by (cbn; lia). unfold sp0, D0. f_equal. lia.
Qed.
Lemma rng_nl : ltac2:(tb__ "0|1|
S0SbS6S6A2S34S6cVm0;A1S8bA2SeS6S6S1bZ5a35bM0Z0A2S1bG0Z1A2A4A3").
Proof using Hb16 Hb3. apply rng_lit; try lia. cbn [eval]. apply u64. lia. Qed.
Lemma rng_lock : ltac2:(tb__ "0|1|
S0SbS6S6A2S34S6cVm0;A1S89A2SeS6S6S1bZ5a3c8M0Z0A2S1bG0Z4A2A4A3").
Proof using Hb16 Hb3. apply rng_lit; try lia. cbn [eval]. apply u64. lia. Qed.
Lemma rng_ctr : ltac2:(tb__ "0|1|
S0SbS6S6A2S34S6cVm0;A1S87A2SeS6S6S1bZ5a3c8M0Z14A2S1bG0Z18A2A4A3").
Proof using Hb16 Hb3. apply rng_lit; try lia. cbn [eval]. apply u64. lia. Qed.
Lemma rng_act : ltac2:(tb__ "0|2|
S0SbS6S6A2S34S6cVm0;A1S85A2SeS6S6S1bZ5a3c8M0S1bS1eZ8S6dA2M1Z58A2A2S1bG0S1bG1Z60A2A2A4A3").
Proof using HC HMI HW Hb16 Hb3 Hhdr Hsp.
  pose proof R_all. unfold obj_range, obj_lo_of, obj_hi_of, Q_act, U.Mal_malloc__G1.Mal_malloc_fast_runs.O_act. cbn [ob_base ob_lo ob_hi mr_LK MR_P].
  rewrite (soff_of_ev (SAlu ALU_ADD (SAlu ALU_SLL (v 150) (SLit 3)) (SLit 88)) (8 * sc + 88) eq_refl ze_actoff) by lia.
  rewrite (soff_of_ev (SAlu ALU_ADD (SAlu ALU_SLL (v 150) (SLit 3)) (SLit 96)) (8 * sc + 96) eq_refl ze_acthi) by lia.
  cbn [eval]. rewrite u64 by lia. reflexivity.
Qed.
Lemma rng_ctx8 : ltac2:(tb__ "0|4|
S2dS2dScS40A1S6S0S9S5dR4A1SaA3M0G0S0S6S5cS6aS6bR6A3M1R3A3S0S6G1S1bR4Z8M2A2A3S1S1aZ0R5A2S1cR5Z3e8A2A2S0SbS6S6A2S34S6cVm0;A1S45S2fZ5a3c8M3A1R9R8R7S46A5A2SeS6S6S1bG3R6A2S1bG3S1bR6G2A2A2A4A3F_;F_;F_;F_;F_;Foff;Fcs;Fehi;Felo;").
Proof using Hb16 Hb3.
  intros elo ehi cs off Slo Shi Elo Ehi Hoff. unfold obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi].
  rewrite (soff_of_ev elo off Slo Elo) by lia. rewrite (soff_of_ev ehi (off + 8) Shi Ehi) by lia.
  cbn [eval]. rewrite u64 by lia. reflexivity.
Qed.
Lemma rng_act0 : ltac2:(tb__ "0|3|
S0SbS6S6A2S34S6cVm0;A1S86A2SeS6S6S1bZ5a3c8M0S1bS1eZ8M1S70A2Z58A2M2A2S1bG0S1bG2G1A2A2A4A3").
Proof using HC HMI HW Hb16 Hb3 Hhdr Hsp. pose proof Hj164. apply rng_ctx8; [reflexivity | reflexivity | apply ze_act0off | rewrite ze_act0hi; lia | lia]. Qed.
Lemma rng_usg0 : ltac2:(tb__ "0|3|
S0SbS6S6A2S34S6cVm0;A1S8eA2SeS6S6S1bZ5a3c8M0S1bS1eZ8M1S70A2Z1d8A2M2A2S1bG0S1bG2G1A2A2A4A3").
Proof using HC HMI HW Hb16 Hb3 Hhdr Hsp. pose proof Hj164. apply rng_ctx8; [reflexivity | reflexivity | apply ze_usg0off | rewrite ze_usg0hi; lia | lia]. Qed.
Lemma rng_usg1 : ltac2:(tb__ "0|3|
S0SbS6S6A2S34S6cVm0;A1S8fA2SeS6S6S1bZ5a3c8M0S1bS1eZ8M1S6dA2Z1d8A2M2A2S1bG0S1bG2G1A2A2A4A3").
Proof using HC HMI HW Hb16 Hb3 Hhdr Hsp. pose proof R_all. apply rng_ctx8; [reflexivity | reflexivity | apply ze_usg1off | rewrite ze_usg1hi; lia | lia]. Qed.
Lemma rng_sct : ltac2:(tb__ "0|1|
S0SbS6S6A2S34S6cVm0;A1S8cA2SeS6S6S1bZ108ecM0Z0A2S1bG0Z60A2A4A3").
Proof using Hb16 Hb3. apply rng_lit; try lia. cbn [eval]. apply u64. lia. Qed.
Lemma rng_ctz : ltac2:(tb__ "0|1|
S0SbS6S6A2S34S6cVm0;A1S88A2SeS6S6S1bZ108ccM0Z0A2S1bG0Z20A2A4A3").
Proof using Hb16 Hb3. apply rng_lit; try lia. cbn [eval]. apply u64. lia. Qed.
Lemma rng_meta : ltac2:(tb__ "0|0|
S0SbS6S6A2S34S6cVm0;A1S8aA2SeS6S6S1bS76Z10A2S1bS76Z28A2A4A3").
Proof using HC HMI HW Hb16 Hb3 Hhdr. apply rng_lit; try lia. rewrite ev1u by reflexivity. apply ze151. Qed.
Lemma rng_slot : ltac2:(tb__ "0|0|
S0SbS6S6A2S34S6cVm0;A1S8dA2SeS6S6S1bS77N4A2S1bS77S20S6fZ4A2A2A4A3").
Proof using HC HMI HW Hb16 Hb3 Hhdr.
  pose proof R_all. unfold obj_range, obj_lo_of, obj_hi_of, Q_slot, U.Mal_malloc__G1.Mal_malloc_fast_runs.O_slot. cbn [ob_base ob_lo ob_hi].
  rewrite soff1_lit by lia. rewrite (soff_of_ev (SAlu ALU_ADD (E_stride kd) (SLit (-4))) (stv - 4) ltac:(destruct kd; reflexivity) ze_hi) by lia.
  rewrite ev1u by (destruct kd; reflexivity). rewrite ze_p0. reflexivity.
Qed.

Lemma Zones : ltac2:(tb__ "0|5|
S1S3S6S6S3S6S6S3S6S6S1S1aR3S80A2S1S1aS1bS84Z4A2R2A2S1S1aR2S17eVL;A1M0A2S1S1aZ1000M1R3A2S1S2S1aS1bR1G1A2M2R3A2S1aR2R1A2A2S1S2S1aR2Z10000M3A2S1aZ5b000M4R3A2A2S1S2S1aG2G3A2S1aG4R1A2A2S1S1aR1S76A2S1S1aS1bS76Z28A2G2A2S1S1aG1R1A2S1aG2G0A2A2A2A2A2A2A2A2A2A2A2LaLo;A2LgHi;A2LgLo;A2S1S1aG0S1bS93S96A2A2S1aS1bG4Z10A2G0A2A2A2").
Proof using HC HLok HMI HW Hb16 Hb3 Hhdr Hsp Hsp_high.
  pose proof R_all as R. pose proof Hsp_high as SH.
  destruct Hregion as (rg & Hr & Hk & Hl & Ho & Hext & _ & P1 & P2 & P3).
  pose proof (F_area C_U s L n g am zz rd0 wok0 vm HMI HC Hzz) as (a & k & Ha & Hk' & Eg & InA & Pa & Pa2 & EzG & (rga & Hra & Hkind)).
  pose proof (fp_mem_range C_U L s vm _ _ HI_vm HI_ledger InA ltac:(unfold PGSZ; lia)) as (A1 & A2 & A3). cbn [mc_img_lo mc_img_hi C_U] in A3.
  pose proof (footprint_region_In s _ _ Hr Hk Hl) as InR.
  assert (NE : (LMem a, PGSZ) <> (LMem (SP (prid (am_mem am)) 0), rg_len rg)).
  { intros E. injection E as E1 E2. rewrite E1 in Hra. cbn [prid] in Hra. rewrite Hr in Hra. injection Hra as <-. exact (Hkind Hk). }
  destruct HLok as (_ & _ & PW & _).
  assert (EzMem : zMem = ly_reg L (prid (am_mem am)) + poff (am_mem am)) by (unfold zMem, addr_of, loc_addr; destruct (am_mem am); reflexivity).
  unfold f_zg in EzG. fold zG in EzG.
  destruct a as [ar ao]. unfold addr_of in *. cbn [loc_addr prid poff] in *.
  destruct (pairwise_map_In _ (crange L) (footprint s) _ _ PW InA InR NE) as [DD|DD];
    unfold MallocInv.ranges_disjoint, crange in DD; cbn [fst snd loc_addr] in DD;
    unfold group_extent, UNIT, IB, PGSZ, AREA_HDR, META_SIZE, METAS_PER_AREA in *;
    change (stride_of am) with stv in *; top_ranges;
    (split; [exists (ly_reg L (prid (am_mem am))), (ly_reg L (prid (am_mem am)) + rg_len rg), (ly_reg L ar + ao);
             repeat match goal with |- _ /\ _ => split end; lia
           | unfold sp0, D0; lia]).
Qed.

Definition N_all : list sobj := ltac2:(tb__ "0|0|
SfS33S8bSfS33S89SfS33S87SfS33S85SfS33S8cSfS33S88SfS33S8aSfS33S8dSfS33S86SfS33S8eSfS33S8fS12S33A1A3A3A3A3A3A3A3A3A3A3A3").

Lemma OBJS_eq : ltac2:(tb__ "0|0|
S0ScS33A1SadS9eS72A2SfS33S81S7cA3A3").
Proof using . reflexivity. Qed.

Ltac zone := rewrite ?rng_nl, ?rng_lock, ?rng_ctr, ?rng_act, ?rng_sct, ?rng_ctz, ?rng_meta, ?rng_slot, ?rng_act0, ?rng_usg0, ?rng_usg1, ?rng_stk; unfold SymState.ranges_disjoint in *; cbn [fst snd] in *; lia.

Lemma N_hold : ltac2:(tb__ "0|0|
Sd9S33S36S67S6cVm0;A1S117Vms;Vm0;A2A3S7cA3").
Proof using Erd Ewok HC HMI HW Hb16 Hb3 Hdepth Hhdr Hm0_ctz Hm0_sct Hm16 Hm3 Hrom Hsp.
  unfold N_all. repeat (apply Forall_cons; [first [apply hold_nl|apply hold_lock|apply hold_ctr|apply hold_act|apply hold_sct|apply hold_ctz|apply hold_meta|apply hold_slot|apply hold_act0|apply hold_usg0|apply hold_usg1]|]).
  apply Forall_nil.
Qed.

Lemma N_vs_stack : ltac2:(tb__ "0|1|
Sd9S33S33S55S34S6cVm0;A1M0S81A2S34G0R1A2A2Lo;S7cA3").
Proof using HC HLok HMI HW Hb16 Hb3 Hhdr Hsp Hsp_high.
  pose proof R_all as R. pose proof Hj164 as RJ. destruct Zones as ((gLo & gHi & aLo & ZZ) & SH & AC). rewrite rng_stk.
  unfold N_all. repeat (apply Forall_cons; [zone|]). apply Forall_nil.
Qed.

Lemma N_pairwise : ltac2:(tb__ "0|0|
S54S6cVm0;A1S7cA2").
Proof using HC HLok HMI HW Hb16 Hb3 Hhdr Hsp Hsp_high.
  pose proof R_all as (_ & _ & Rsc & _ & Ridx & _ & R16 & _ & _ & _ & Rsi & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & RzM & RzSt & RzE & Rce & R47 & RzG & RzG2).
  pose proof Hj164 as RJ. destruct Zones as ((gLo & gHi & aLo & ZZ) & SH & AC).
  unfold N_all. cbn [pairwise_disjoint].
  repeat split; repeat (apply Forall_cons;
    [rewrite ?rng_nl, ?rng_lock, ?rng_ctr, ?rng_act, ?rng_sct, ?rng_ctz, ?rng_meta, ?rng_slot, ?rng_act0, ?rng_usg0, ?rng_usg1;
     unfold SymState.ranges_disjoint; cbn [fst snd]; lia|]); apply Forall_nil.
Qed.

Definition S2 : sstate := ltac2:(tb__ "0|0|
S4bZ2056cS69S68S4eS16S2dA1SfS33S81S12S33A1A3Sa0S72A1S9dS14A9").

Lemma C0_eq : ltac2:(tb__ "0|0|
S0S35S9fS9eS72A2S4bS59S74A1S5aS74A1S57S74A1S56S74A1S5bS74A1S19S33S58S74A1S7cA3S3bS74A1S9dS37S74A1A9A3").
Proof using . reflexivity. Qed.

Lemma swf_C0 : ltac2:(tb__ "0|0|
S9cS0S9S38S9fS9eR1A2A1SaA3Fkd';").
Proof using . intros [| |]; vm_cast_no_check (@eq_refl bool true). Qed.

Theorem carve : ltac2:(tb__ "0|2|
ScS18eA1M0S18dS4cS67S6cVm0;A1M1S74SeG0S18bR2S18cVms;R1A2A4A4S4cS67G1S9fS9eS72A2SeG0S18bR3S18cVms;R2A2A4A4F_;Fmd;Ftr;").
Proof using Erd Ewok HC HLok HMI HW Hb16 Hb3 Hdepth Hhdr Hm0_ctz Hm0_sct Hm16 Hm3 Hrom Hsp Hsp_high.
  intros tr md Hsm. rewrite C0_eq. apply smatch_extend_objs.
  - exact Hsm.
  - rewrite <- C0_eq. apply swf_C0.
  - cbn [ss_objs S2]. change (rm (rho1 m0)) with m0. apply N_hold.
  - cbn [ss_objs S2]. apply Forall_forall. intros o Ho. constructor; [|constructor].
    exact (proj1 (Forall_forall _ _) N_vs_stack o Ho).
  - apply N_pairwise.
Qed.

End Inst.
End Mal_malloc_fastI.

Module Mal_malloc_fastC.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSurgery OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGeom OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRepr OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfMain OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSlot OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooterLemmas OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeQuickModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ImageUpd OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FpLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFastPost OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.Mal_malloc_fast_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G2.Mal_malloc_fast_enum OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_free__G1.Mal_free_quick OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G2.Mal_malloc_fastI.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Local Ltac top_range_of L := lazymatch goal with | _ : 0x7fff7f800000 <= OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL L <= 0x7fffff800000 |- _ => fail | _ => let h := fresh "TOPR" in pose proof (OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL_val L) as h end.
Local Ltac top_ranges := repeat match goal with | |- context [OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL ?L] => top_range_of L | _ : context [OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL ?L] |- _ => top_range_of L end.
Local Ltac lia := first [Stdlib.micromega.Lia.lia | top_ranges; Stdlib.micromega.Lia.lia].
Local Ltac nia := first [Stdlib.micromega.Lia.nia | top_ranges; Stdlib.micromega.Lia.nia].
Import RP.

Section InstC.

Variables (s : astate) (L : layout) (n : Z) (g : sptr) (am : ameta).
Variable rho : valuation.
Variables (b3 b16 : Z).
Hypothesis HW : WF s.
Hypothesis HC : ltac2:(tb__ "0|0|
S18fVs;Vn;Vg;Vam;A4").
Hypothesis HLok : layout_ok L s.
Hypothesis HP12 : ltac2:(tb__ "0|0|
S0S6Sb4Q40S32Vrho;PcA2A2Vn;A3").
Hypothesis Hb3 : 0 <= b3 < 256.
Hypothesis Hb16 : 0 <= b16 < 65536.
Hypothesis Hhdr : ltac2:(tb__ "0|1|
S6S6S0SdSbS6S6A2M0A1SebSe9Vam;S191Vam;A1A2A1S10G0SeS6S6R2R1A4A2A3S1S0S6Vb3;R3A3S0S6Vb16;R2A3A2F_;Fh16;Fh3;").
Local Notation "§1§ h__" := (h__ am) (at level 10, h__ global).
Local Abbreviation sc := (§1§ U.Mal_malloc__G2.Mal_malloc_fastI.sc).
Local Abbreviation sc0 := (@U.Mal_malloc__G2.Mal_malloc_fastI.sc0 n).
Local Abbreviation kq := (@U.Mal_malloc__G2.Mal_malloc_fastI.kq n).
Local Abbreviation idx := (§1§ U.Mal_malloc__G2.Mal_malloc_fastI.idx).
Local Abbreviation sz := (§1§ U.Mal_malloc__G2.Mal_malloc_fastI.sz).
Local Abbreviation zG := (@U.Mal_malloc__G2.Mal_malloc_fastI.zG L g).
Local Abbreviation zMem := (@U.Mal_malloc__G2.Mal_malloc_fastI.zMem L am).
Local Abbreviation zSt := (@U.Mal_malloc__G2.Mal_malloc_fastI.zSt L am).
Local Abbreviation avail := (§1§ U.Mal_malloc__G2.Mal_malloc_fastI.avail).
Local Abbreviation freed := (§1§ U.Mal_malloc__G2.Mal_malloc_fastI.freed).
Local Abbreviation bits := (§1§ U.Mal_malloc__G2.Mal_malloc_fastI.bits).
Local Abbreviation ctr := (@U.Mal_malloc__G2.Mal_malloc_fastI.ctr s).
Local Abbreviation off := (@U.Mal_malloc__G2.Mal_malloc_fastI.off s n am b3 b16).
Local Abbreviation ga1 := (@U.Mal_malloc__G2.Mal_malloc_fastI.ga1 n).
Local Abbreviation ga2 := (@U.Mal_malloc__G2.Mal_malloc_fastI.ga2 n).
Local Abbreviation ga3 := (@U.Mal_malloc__G2.Mal_malloc_fastI.ga3 n).
Local Abbreviation ga4 := (@U.Mal_malloc__G2.Mal_malloc_fastI.ga4 n).
Local Abbreviation kd := (§1§ U.Mal_malloc__G2.Mal_malloc_fastI.kd).
Local Notation "§2§ h__" := (h__ s n g am HC) (at level 10, h__ global).
Local Abbreviation Hn := (§2§ U.Mal_malloc__G2.Mal_malloc_fastI.Hn).
Local Abbreviation Hu := (§2§ U.Mal_malloc__G2.Mal_malloc_fastI.Hu).
Local Abbreviation Hkq := (@U.Mal_malloc__G2.Mal_malloc_fastI.Hkq s n g am b3 b16 HC Hb3 Hb16).
Local Abbreviation isRC := (@U.Mal_malloc__G2.Mal_malloc_fastI.isRC s n).
Local Notation "§3§ h__" := (h__ s n g am b3 b16 HW HC Hb3 Hb16) (at level 10, h__ global).
Local Abbreviation route_cases := (§3§ U.Mal_malloc__G2.Mal_malloc_fastI.route_cases).
Local Abbreviation j164 := (@U.Mal_malloc__G2.Mal_malloc_fastI.j164 s n am).
Local Abbreviation u165 := (@U.Mal_malloc__G2.Mal_malloc_fastI.u165 s am).
Local Abbreviation Hj164 := (§3§ U.Mal_malloc__G2.Mal_malloc_fastI.Hj164).
Local Abbreviation Hlast := (@U.Mal_malloc__G2.Mal_malloc_fastI.Hlast s n g am HW HC).
Variables (rd0 : word -> option byte) (wok0 : word -> bool) (vm : VmMaps).
Hypothesis HMI : ltac2:(tb__ "0|0|
S189S17fS18aVs;VL;A2Vrd0;Vwok0;Vvm;A5").
Local Abbreviation Hoff := (§3§ U.Mal_malloc__G2.Mal_malloc_fastI.Hoff).
Local Notation "§4§ h__" := (h__ s L n g am rho b3 b16) (at level 10, h__ global).
Local Abbreviation rw1 := (§4§ U.Mal_malloc__G2.Mal_malloc_fastI.rw1).
Local Abbreviation rho1 := (§4§ U.Mal_malloc__G2.Mal_malloc_fastI.rho1).
Local Abbreviation zr1 := (§4§ U.Mal_malloc__G2.Mal_malloc_fastI.zr1).
Local Abbreviation zl1 := (§4§ U.Mal_malloc__G2.Mal_malloc_fastI.zl1).
Local Abbreviation zl1_1 := (§4§ U.Mal_malloc__G2.Mal_malloc_fastI.zl1_1).
Local Abbreviation zl1_4 := (§4§ U.Mal_malloc__G2.Mal_malloc_fastI.zl1_4).
Local Abbreviation Gk_range := (@U.Mal_malloc__G2.Mal_malloc_fastI.Gk_range n).
Local Abbreviation RC_vals := (@U.Mal_malloc__G2.Mal_malloc_fastI.RC_vals s L n g am b3 b16 HW HC Hb3 Hb16).
Local Abbreviation bits_eq := (§1§ U.Mal_malloc__G2.Mal_malloc_fastI.bits_eq).
Local Notation "§5§ h__" := (h__ s L n g am b3 b16 HW HC Hb3 Hb16 Hhdr rd0 wok0 vm HMI) (at level 10, h__ global).
Local Abbreviation R_all := (§5§ U.Mal_malloc__G2.Mal_malloc_fastI.R_all).
Local Abbreviation zr1_12 := (@U.Mal_malloc__G2.Mal_malloc_fastI.zr1_12 s L n g am rho b3 b16 HP12).
Local Notation "§6§ h__" := (h__ s L n g am rho b3 b16 HW HC Hb3 Hb16 Hhdr rd0 wok0 vm HMI) (at level 10, h__ global).
Local Abbreviation zr1_149 := (§6§ U.Mal_malloc__G2.Mal_malloc_fastI.zr1_149).
Local Abbreviation bits_range := (§5§ U.Mal_malloc__G2.Mal_malloc_fastI.bits_range).
Local Abbreviation zr1_155 := (§6§ U.Mal_malloc__G2.Mal_malloc_fastI.zr1_155).
Local Abbreviation zr1_158 := (@U.Mal_malloc__G2.Mal_malloc_fastI.zr1_158 s L n g am rho b3 b16 HW HC Hb3 Hb16).
Local Abbreviation zr1_160 := (§6§ U.Mal_malloc__G2.Mal_malloc_fastI.zr1_160).
Local Abbreviation zr1_161 := (§6§ U.Mal_malloc__G2.Mal_malloc_fastI.zr1_161).
Local Abbreviation zr1_162 := (§6§ U.Mal_malloc__G2.Mal_malloc_fastI.zr1_162).
Local Abbreviation zr1_163 := (§6§ U.Mal_malloc__G2.Mal_malloc_fastI.zr1_163).
Local Abbreviation ze_var := (§4§ U.Mal_malloc__G2.Mal_malloc_fastI.ze_var).
Local Abbreviation ze_lit := (§4§ U.Mal_malloc__G2.Mal_malloc_fastI.ze_lit).
Local Abbreviation ze_alu := (§4§ U.Mal_malloc__G2.Mal_malloc_fastI.ze_alu).
Local Abbreviation ze_aluw := (§4§ U.Mal_malloc__G2.Mal_malloc_fastI.ze_aluw).
Local Notation "§7§ h__" := (h__ s L n g am rho b3 b16 HW HC HP12 Hb3 Hb16 Hhdr rd0 wok0 vm HMI) (at level 10, h__ global).
Local Abbreviation ze12 := (§7§ U.Mal_malloc__G2.Mal_malloc_fastI.ze12).
Local Abbreviation ze142 := (§6§ U.Mal_malloc__G2.Mal_malloc_fastI.ze142).
Local Abbreviation ze143 := (§6§ U.Mal_malloc__G2.Mal_malloc_fastI.ze143).
Local Abbreviation ze149 := (§6§ U.Mal_malloc__G2.Mal_malloc_fastI.ze149).
Local Abbreviation ze150 := (§6§ U.Mal_malloc__G2.Mal_malloc_fastI.ze150).
Local Abbreviation ze151 := (§6§ U.Mal_malloc__G2.Mal_malloc_fastI.ze151).
Local Abbreviation ze152 := (§6§ U.Mal_malloc__G2.Mal_malloc_fastI.ze152).
Local Abbreviation ze153 := (§6§ U.Mal_malloc__G2.Mal_malloc_fastI.ze153).
Local Abbreviation ze154 := (§6§ U.Mal_malloc__G2.Mal_malloc_fastI.ze154).
Local Abbreviation ze155 := (§6§ U.Mal_malloc__G2.Mal_malloc_fastI.ze155).
Local Abbreviation ze156 := (§6§ U.Mal_malloc__G2.Mal_malloc_fastI.ze156).
Local Abbreviation ze157 := (§6§ U.Mal_malloc__G2.Mal_malloc_fastI.ze157).
Local Abbreviation ze158 := (§6§ U.Mal_malloc__G2.Mal_malloc_fastI.ze158).
Local Abbreviation ze164 := (§6§ U.Mal_malloc__G2.Mal_malloc_fastI.ze164).
Local Abbreviation ze165 := (§6§ U.Mal_malloc__G2.Mal_malloc_fastI.ze165).
Local Abbreviation ze_S := (§6§ U.Mal_malloc__G2.Mal_malloc_fastI.ze_S).
Local Abbreviation ze_strideT := (§6§ U.Mal_malloc__G2.Mal_malloc_fastI.ze_strideT).
Local Abbreviation land_not4095 := (@U.Mal_malloc__G2.Mal_malloc_fastI.land_not4095 b3 b16 Hb3 Hb16).
Local Abbreviation ze_strideM := (§6§ U.Mal_malloc__G2.Mal_malloc_fastI.ze_strideM).
Local Abbreviation ze_T6 := (§6§ U.Mal_malloc__G2.Mal_malloc_fastI.ze_T6).
Hypothesis Hsp : ltac2:(tb__ "0|1|
S1S1aZ1000Sb4Q40S32Vrho;PaA2A2M0A2S0S6S1fG0Z10A2Z0A3A2").
Hypothesis Hdepth : ltac2:(tb__ "0|1|
S1S1aS60Z40Sb4Q40S32Vrho;PfA2A2A2M0S24S183A1A2S1aS24S1dZ2Z28A2A1G0A2A2").
Hypothesis Hsp_high : ltac2:(tb__ "0|1|
S1aS17eVL;A1S1bSb4Q40M0S32Vrho;PaA2A2S60Z40Sb4G0S32Vrho;PfA2A2A2A2A2").
Local Notation "§8§ h__" := (h__ s L n g am rho b3 b16 HW HC Hb3 Hb16 Hhdr rd0 wok0 vm HMI Hsp) (at level 10, h__ global).
Local Abbreviation ZF5 := (§8§ U.Mal_malloc__G2.Mal_malloc_fastI.ZF5).
Local Notation "§9§ h__" := (h__ s L n g am rho b3 b16 HW HC HP12 Hb3 Hb16 Hhdr rd0 wok0 vm HMI Hsp Hdepth Hsp_high) (at level 10, h__ global).
Local Abbreviation facts_hold := (§9§ U.Mal_malloc__G2.Mal_malloc_fastI.facts_hold).
Variable m0 : word -> option byte.
Hypothesis Erd : ltac2:(tb__ "0|0|
S0Sb3Q40A1SdSb3Q8A1A1F_;Vrd0;S119S67Vm0;A2A3").
Hypothesis Ewok : ltac2:(tb__ "0|0|
S0Sb3Q40A1S9F_;Vwok0;S11aS67Vm0;A2A3").
Variable ms : machine_state.
Hypothesis Hrom : rom_ok segsU ms.
Hypothesis Hm0_sct : ltac2:(tb__ "0|1|
S6S1S1aZ0R1A2S1cR1Z60A2A2S0SdSb3Q8A1M0A1Vm0;Sb2Q40S1bZ108ecR2A2A2A1S16G0A1A3F_;Fkk;").
Hypothesis Hm0_ctz : ltac2:(tb__ "0|1|
S6S1S1aZ0R1A2S1cR1Z20A2A2S0SdSb3Q8A1M0A1Vm0;Sb2Q40S1bZ108ccR2A2A2A1S16G0A1A3F_;Fkk;").
Hypothesis Hm3 : ltac2:(tb__ "0|2|
S0SdSb3Q8M0A1M1A1S119S67Vm0;Sb2Q40S20SbeVL;Vam;A2Z3A2A2A3S10G1Sb2G0Vb3;A2A2A3").
Hypothesis Hm16 : ltac2:(tb__ "0|3|
S17S186R1U2M0A2S0SdSb3Q8M1A1M2A1S119S67Vm0;Sb2Q40S1bS20SbeVL;Vam;A2Z2A2S25R2A1A2A2A3S10G2Sb2G1S126Vb16;G0R2A3A2A2A3F_;Fj;").
Let bv0 : byteview := ltac2:(tb__ "0|0|
S182S119S67Vm0;A2S11aS67Vm0;A2A2").
Local Abbreviation ev1 := (§4§ U.Mal_malloc__G2.Mal_malloc_fastI.ev1).
Local Notation "§10§ h__" := (h__ s L n g am rho b3 b16 HW HC HLok Hb3 Hb16 Hhdr rd0 wok0 vm HMI Hsp Hsp_high) (at level 10, h__ global).
Local Abbreviation Zones := (§10§ U.Mal_malloc__G2.Mal_malloc_fastI.Zones).

Variable ok : world -> Prop.
Variable K : ltac2:(tb__ "0|0|
ScS18eA1S18dOF_;F_;").
Hypothesis HK : ltac2:(tb__ "0|0|
Sd7S67Vok;VK;A3").

Variable mW : word -> option byte.
Let rhoW : valuation := rho1 mW.

Lemma EV : ltac2:(tb__ "0|1|
S30S2dScdVrhoW;R2A2S0S9S115ScfR2A2SaA3S0S9S5dR3A1SaA3S0Sb3Q40M0A1S3cR5R4A2Sb2G0S5cSb5Vs;VL;Vn;Vg;Vam;Vrho;Vb3;Vb16;A8Sb7Vs;VL;Vn;Vg;Vam;Vrho;Vb3;Vb16;A8R4A3A2A3F_;F_;F_;Fe;Frho';").
Proof using mW. intros rho' e Hag Hv Hs. rewrite (eval_agrees rhoW rho' e Hag Hv). apply ev1. exact Hs. Qed.

Lemma EVu : ltac2:(tb__ "0|0|
S30S2dScdVrhoW;R2A2S0S9S115ScfR2A2SaA3S0S9S5dR3A1SaA3S0S6Sb4Q40S3cR5R4A2A2S5cSb5Vs;VL;Vn;Vg;Vam;Vrho;Vb3;Vb16;A8Sb7Vs;VL;Vn;Vg;Vam;Vrho;Vb3;Vb16;A8R4A3A3F_;F_;F_;Fe;Frho';").
Proof using mW. intros rho' e Hag Hv Hs. rewrite (EV rho' e Hag Hv Hs). apply u64. apply zeval_range. exact Hs. Qed.

Lemma HOLDS : ltac2:(tb__ "0|0|
S30S2eScdVrhoW;R2A2S0S9S114ScfR2A2SaA3S0S9S5fR3A1SaA3S4S3dR5R4A2S5eSb5Vs;VL;Vn;Vg;Vam;Vrho;Vb3;Vb16;A8Sb7Vs;VL;Vn;Vg;Vam;Vrho;Vb3;Vb16;A8R4A3A2F_;F_;F_;Fp;Frho';").
Proof using mW.
  intros rho' p (Hw & Hl & _) Hv Hs.
  rewrite (holds_agree_vars below200 rho' rhoW p Hw Hl Hv).
  rewrite (holds_zholds rhoW p Hs). apply zholds_ext; intros; reflexivity.
Qed.

Lemma rw_agrees : ltac2:(tb__ "0|0|
S30S7ScdVrhoW;R2A2S0S9ScfR2A1SaA3S0Sb3Q40A1S32R4R3A2Sc5Vs;VL;Vn;Vg;Vam;Vrho;Vb3;Vb16;R3A9A3F_;F_;Fj;Frho';").
Proof using mW. intros rho' j (Hw & _) Hj. rewrite (Hw j Hj). reflexivity. Qed.

Lemma seg_run : ltac2:(tb__ "0|1|
S17S35ScSd1A1M0SfbS30S0S9S37R4A1S14A3S0S7S3aR5A1S9dA3S0SdG0A1Sd5S67R7Sa6S9eA1R6SaA5S10G0R5A2A3ScdVrhoW;R4A2Sd1S30Sf9ScbSd1R3RaA3ScdVrhoW;R3A2Sd6S67VK;Sd4R5A1R4R3A5RcR4A1F_;F_;F_;Fw;Frho'';FLf;SfaS67Vok;Sd6S67VK;R9R6A4R7A4F_;F_;F_;F_;F_;Frho';FQ;Fleaves;FS;Ffuel;").
Proof using HK Hb16 Hb3 L am g mW n rho s.
  intros fuel S leaves Q rho' Hl Hn Hrun Hag HQ.
  eapply triple_conseq; [intros w Hw; exact Hw | | apply triple1_triple; exact (sym_run_sound_strict segsU fuel (CUTS MR_P) S leaves ok K rho' Hl Hrun HK)].
  intros w (Lf & rho'' & Hin & Hab & Hsm & HKw). apply (HQ Lf rho'' w Hin).
  - eapply agrees_below; [exact Hag | exact Hab | rewrite Hn; unfold NX; lia].
  - split; [exact Hsm | exact HKw].
Qed.

Lemma ze_kq : ltac2:(tb__ "0|0|
S0S6S5cSb5Vs;VL;Vn;Vg;Vam;Vrho;Vb3;Vb16;A8Sb7Vs;VL;Vn;Vg;Vam;Vrho;Vb3;Vb16;A8S31S11dS31S11bS39PcA1S2fZ3A1A3S2fZ4A1A3A3Sb8Vn;A1A3").
Proof using HC HMI HP12 HW Hb16 Hb3 Hhdr Hsp.
  change (SVar 12) with (v 12). rewrite !ze_alu, ze12, !ze_lit. cbn [zalu]. pose proof R_all as R. unfold MMAP_THRESHOLD in R.
  change ((4 mod 2 ^ 64) mod 64) with 4. change (3 mod 2 ^ 64) with 3. rewrite !Z.mod_small by lia. reflexivity.
Qed.

Lemma zr1_stages : ltac2:(tb__ "0|3|
S1S0S6Sb5Vs;VL;Vn;Vg;Vam;Vrho;Vb3;Vb16;P95A9Sb8Vn;A1A3S1S0S6Sb5Vs;VL;Vn;Vg;Vam;Vrho;Vb3;Vb16;Pa0A9S5cSb5Vs;VL;Vn;Vg;Vam;Vrho;Vb3;Vb16;A8M0Sb7Vs;VL;Vn;Vg;Vam;Vrho;Vb3;Vb16;A8M1S15cA3A3S1S0S6Sb5Vs;VL;Vn;Vg;Vam;Vrho;Vb3;Vb16;Pa1A9S5cG0G1S15dA3A3S1S0S6Sb5Vs;VL;Vn;Vg;Vam;Vrho;Vb3;Vb16;Pa2A9S5cG0G1S15eA3A3S1S0S6Sb5Vs;VL;Vn;Vg;Vam;Vrho;Vb3;Vb16;Pa3A9S5cG0G1S15fA3A3S1S0ScS6A1M2Sb7Vs;VL;Vn;Vg;Vam;Vrho;Vb3;Vb16;P1A9S181A3S0G2Sb7Vs;VL;Vn;Vg;Vam;Vrho;Vb3;Vb16;P4A9S17dA3A2A2A2A2A2A2").
Proof using HC HMI HW Hb16 Hb3 Hhdr.
  pose proof uses_ok as (_ & _ & U1 & U2 & U3 & U4).
  assert (HQ : forall l, Qst l = true -> zl_tab l = zl1 l).
  { intros l Hq. unfold Qst in Hq. apply Bool.orb_prop in Hq as [Hq|Hq]; apply Pos.eqb_eq in Hq; subst l; [rewrite zl1_1 | rewrite zl1_4]; reflexivity. }
  assert (A1 : zeval zr1 zl1 T1 = ga1).
  { unfold ga1, G1. symmetry. apply (zeval_agree P1 Qst); [exact U1 | | exact HQ].
    intros i Hi. unfold P1 in Hi. apply Pos.eqb_eq in Hi. subst i. rewrite zr_list_hit. symmetry. apply zr1_149. }
  assert (A2 : zeval zr1 zl1 T2 = ga2).
  { unfold ga2, G2. symmetry. apply (zeval_agree P2 Qst); [exact U2 | | exact HQ].
    intros i Hi. unfold P2 in Hi. apply Bool.orb_prop in Hi as [Hi|Hi]; apply Pos.eqb_eq in Hi; subst i;
      rewrite ?zr_list_skip by reflexivity; rewrite zr_list_hit; symmetry; [apply zr1_149 | rewrite zr1_160; fold ga1; rewrite <- A1; reflexivity]. }
  assert (A3 : zeval zr1 zl1 T3 = ga3).
  { unfold ga3, G3. symmetry. apply (zeval_agree P3 Qst); [exact U3 | | exact HQ].
    intros i Hi. unfold P3 in Hi. repeat (apply Bool.orb_prop in Hi; destruct Hi as [Hi|Hi]); apply Pos.eqb_eq in Hi; subst i;
      rewrite ?zr_list_skip by reflexivity; rewrite zr_list_hit; symmetry;
      first [apply zr1_149 | rewrite zr1_160; rewrite <- A1; reflexivity | rewrite zr1_161; rewrite <- A2; reflexivity]. }
  assert (A4 : zeval zr1 zl1 T4 = ga4).
  { unfold ga4, G4. symmetry. apply (zeval_agree P4 Qst); [exact U4 | | exact HQ].
    intros i Hi. unfold P4 in Hi. repeat (apply Bool.orb_prop in Hi; destruct Hi as [Hi|Hi]); apply Pos.eqb_eq in Hi; subst i;
      rewrite ?zr_list_skip by reflexivity; rewrite zr_list_hit; symmetry;
      first [apply zr1_149 | rewrite zr1_160; rewrite <- A1; reflexivity | rewrite zr1_161; rewrite <- A2; reflexivity | rewrite zr1_162; rewrite <- A3; reflexivity]. }
  rewrite A1, A2, A3, A4. repeat split; first [apply zr1_149 | apply zr1_160 | apply zr1_161 | apply zr1_162 | apply zr1_163 | apply zl1_1 | apply zl1_4].
Qed.

Lemma stage_cert : ltac2:(tb__ "0|6|
S1aZaSb8Vn;A1A2S1Sd9S2eS5eSb5Vs;VL;Vn;Vg;Vam;Vrho;Vb3;Vb16;A8M0Sb7Vs;VL;Vn;Vg;Vam;Vrho;Vb3;Vb16;A8M1A2M2S158A3S1Sd9S2eG2S159A3S1S2Sd9S2eG2S155A3M3Sd9S2eG2S156A3M4A2S1G3S0S6S5cG0G1S15aA3Sb9Vn;A1M5A3F_;G4S0S6S5cG0G1S15bA3G5A3F_;A2A2A2A2F_;").
Proof using HC HMI HW Hb16 Hb3 Hhdr.
  intros Hk. pose proof R_all as R. pose proof Hkq as [_ Esc]. rewrite Esc.
  destruct zr1_stages as (E149 & E160 & E161 & E162 & E163 & El1 & El4).
  exact (sc_stage_ok kq zr1 zl1 ltac:(lia) E149 E160 E161 E162 E163 El1 El4).
Qed.

Definition POST (C : sstate) : assn := ltac2:(tb__ "0|0|
Sf9S3S30S30S1ScdVrhoW;R1A2Sd6S67VK;VC;R1R2A5A2Lrho'';A2Lw;").

Lemma link_gen : ltac2:(tb__ "0|6|
S35S35ScSbS7S2dA2M0A1ScSbS2dS2dA2A1M1ScS2eA1M2S30Sf9S0S9S113S7S15SceSd8G0S7S13S7S2dA2R6A4M3R1A2A1Lv;R7A2SaA3S0S9ScaS7S7S15ScfR1A1A1Lv;G3A3SaA3S0S9S38R8A1SaA3S0SdSbG1G2A2M4A1S116RaR9A2S10G4SeG1G2R7R6A4A2A3ScdVrhoW;R6A2ScdVrhoW;Sd0R7RaA2A2Sd9S2eS3dR8A1S3bRdA1A3S1S118Sd0R9RcA2M5RbA2Sd9S2eS3dG5A1RaA3A2F_;F_;Sd6S67VK;RdR8R7A5SfcRdR8A2F_;F_;F_;F_;F_;F_;F_;Fw;Frho';Fnf;Fd;Fsets;FC;FLf;").
Proof using .
  intros Lf C sets d nf rho' w Hvars Hb Hwf Hsd Hag Hsem HSP.
  pose proof (agrees_set_vars rhoW rho' sets Hag Hb) as Hag'.
  destruct (Hsem Hag' (SP_facts_hold segsU K rho' Lf w HSP)) as [Hd Hnf].
  exists (set_vars rho' sets). split; [exact Hag'|].
  exact (relink segsU K rho' Lf C w sets d nf Hvars Hwf Hsd Hd Hnf HSP).
Qed.

Lemma leaf_fact : ltac2:(tb__ "0|0|
S30S35Sf9S2eScdVrhoW;R4A2Sd6S67VK;R4R5R3A5ScbS2eR3S3bR5A1A3S0S9S114ScfR4A2SaA3S0S9S5fR5A1SaA3S5eSb5Vs;VL;Vn;Vg;Vam;Vrho;Vb3;Vb16;A8Sb7Vs;VL;Vn;Vg;Vam;Vrho;Vb3;Vb16;A8R6A3F_;F_;F_;F_;F_;Fp;Fw;FLf;Frho';").
Proof using mW.
  intros rho' Lf w p Hag HSP Hin Hv Hs. apply (proj1 (HOLDS rho' p Hag Hv Hs)).
  exact (proj1 (Forall_forall _ _) (SP_facts_hold segsU K rho' Lf w HSP) p Hin).
Qed.

Local Ltac hfact Hag :=
  match goal with |- SymState.holds ?r ?p => apply (proj2 (HOLDS r p Hag eq_refl eq_refl)); cbn [zholds zcond] end.

Local Ltac by_kind kd0 := destruct kd0; vm_compute; reflexivity.

Lemma L0_cases : ltac2:(tb__ "0|1|
S9cSd1ScbSd1R1S171R2A1A3S2S0S35Sd4R2A1M0S152R3A1A3S0S35G0S166R3A1A3A2F_;FLf;Fkd0;").
Proof using .
  intros kd0 Lf Hin.
  assert (E : L0 kd0 = [mkLeaf (L0s kd0) RsCut; mkLeaf (L0k kd0) RsCut]).
  { destruct kd0; match goal with |- ?l = _ => vm_cast_no_check (@eq_refl (list leaf) l) end. }
  rewrite E in Hin. destruct Hin as [<-|[<-|[]]]; cbn; auto.
Qed.

Lemma L0s_fact : ltac2:(tb__ "0|0|
S9cScbS2eS48S11fS39PcA1S2fZ9dA1A3S3bS152R1A1A1A3Fkd0;").
Proof using Hb16 Hb3 Hdepth Hsp. intros [| |]; vm_compute; tauto. Qed.
Lemma L0k_fact : ltac2:(tb__ "0|0|
S9cScbS2eS4fS48S11fS39PcA1S2fZ9dA1A3A1S3bS166R1A1A1A3Fkd0;").
Proof using Hb16 Hb3 Hdepth Hsp. intros [| |]; vm_compute; tauto. Qed.

Lemma n157_kq : ltac2:(tb__ "0|0|
S4S1cVn;Z9dA2S1cSb8Vn;A1ZaA2A2").
Proof using HC HMI HW Hb16 Hb3 Hhdr Hsp. unfold kq. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 4) with 16. pose proof R_all. split; intros; [apply Z.div_lt_upper_bound|]; lia. Qed.

Lemma sd_0k : ltac2:(tb__ "0|6|
S9cS0SdSbScSbS2dS2dA2M0A1M1ScS2eA1M2A2M3A1S116S166R1A1S165R1A1A2S10G3SeG1G2SfG0SeS2dS2dS31S11dS31S11bS39PcA1S2fZ3A1A3S2fZ4A1A3S39P95M4A1A4S12G0A1A3SfS2eS49S2fZaA1Sc9G4A1M5A2SfS2eS49G5S2fZ1ffeA1A2S12S2eA1A3A3A4A2A3Fkd0;").
Proof using . intros [| |]; vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop))
  (Some ([(SAlu ALU_SRL (SAlu ALU_ADD (SVar 12) (SLit 3)) (SLit 4), SVar 149)], [SPUle (SLit 10) (v 149); SPUle (v 149) (SLit 8190)]))). Qed.

Lemma link_0k : ltac2:(tb__ "0|1|
S30Sf9ScdVrhoW;R2A2Sd6S67VK;S166Sb6Vam;A1M0A1R3R2A5S1S1aZaSb8Vn;A1A2SfcS165G0A1R3A2A2F_;F_;Fw;Frho';").
Proof using HC HMI HP12 HW Hb16 Hb3 Hdepth Hhdr Hsp.
  intros rho' w Hag HSP. pose proof R_all as R.
  assert (Hk : 10 <= kq).
  { pose proof (leaf_fact rho' _ w _ Hag HSP (L0k_fact kd) eq_refl eq_refl) as F. cbn [zholds zcond] in F.
    rewrite ze_lit, (ze_var), zr1_12 in F. change (157 mod 2 ^ 64) with 157 in F. rewrite Z.mod_small in F by (unfold MMAP_THRESHOLD in R; lia).
    destruct (n <? 157) eqn:E; [exfalso; apply F; reflexivity|]. apply Z.ltb_ge in E. pose proof n157_kq. lia. }
  split; [exact Hk|].
  eapply (link_gen (L0k kd) (Ck kd) [] _ _ rho' w); [unfold U.Mal_malloc__G2.Mal_malloc_fastI.kd, kind_of; destruct (am_last am =? 0); [destruct (am_maplen am =? 0)|]; vm_compute; reflexivity | reflexivity | unfold U.Mal_malloc__G2.Mal_malloc_fastI.kd, kind_of; destruct (am_last am =? 0); [destruct (am_maplen am =? 0)|]; vm_compute; reflexivity | apply sd_0k | exact Hag | | exact HSP].
  intros Hag' _. cbn [set_vars]. split.
  - constructor; [|constructor]. cbn [fst snd]. rewrite (EV rho') by (auto; reflexivity). rewrite ze_kq.
    cbn [eval]. rewrite (rw_agrees rho' 149%positive Hag eq_refl). reflexivity.
  - constructor; [|constructor; [|constructor]]; hfact Hag; rewrite ze149, ze_lit.
    + change (10 mod 2 ^ 64) with 10. lia.
    + change (8190 mod 2 ^ 64) with 8190. lia.
Qed.

Fixpoint set_par (rhoA rhoB : valuation) (l : list (positive * sv)) : valuation :=
  match l with
  | [] => rhoB
  | (j, e) :: t => set_par rhoA (rho_set_rw rhoB j (eval rhoA e)) t
  end.
Definition setp (rhoB : valuation) (l : list (positive * sv)) : valuation := ltac2:(tb__ "0|0|
SfeVrhoB;VrhoB;Vl;A3").

Fixpoint keys_distinct (l : list positive) : bool :=
  match l with [] => true | j :: t => negb (in_vars t j) && keys_distinct t end.

Lemma set_par_rl : ltac2:(tb__ "0|0|
S30ScSbS7S2dA2A1S30S0S7ScSb3Q8A1A1F_;S3eSfeR3R1R2A3A1S3eR1A1A3FrhoB;Fl;FrhoA;").
Proof using . intros rhoA l. induction l as [|[j e] t IH]; intros rhoB; [reflexivity|]. cbn. rewrite IH. reflexivity. Qed.
Lemma set_par_rm : ltac2:(tb__ "0|0|
S30ScSbS7S2dA2A1S30S0Sb3Q40A1SdSb3Q8A1A1F_;S41SfeR3R1R2A3A1S41R1A1A3FrhoB;Fl;FrhoA;").
Proof using . intros rhoA l. induction l as [|[j e] t IH]; intros rhoB; [reflexivity|]. cbn. rewrite IH. reflexivity. Qed.
Lemma set_par_other : ltac2:(tb__ "0|1|
S30ScSbS7S2dA2M0A1S30S7S0S9SceSd8G0S7S13S7S2dA2R3A4R1A2S14A3S0Sb3Q40A1S32SfeR5R3R4A3R2A2S32R3R2A2A3F_;Fu;FrhoB;Fl;FrhoA;").
Proof using .
  intros rhoA l. induction l as [|[j e] t IH]; intros rhoB u Hu; [reflexivity|].
  cbn in Hu. apply Bool.orb_false_iff in Hu as [H1 H2]. cbn. rewrite IH by exact H2. cbn [rw rho_set_rw]. rewrite H1. reflexivity.
Qed.
Lemma set_par_get : ltac2:(tb__ "0|1|
S30ScSbS7S2dA2M0A1S30S7S2dS0S9SffSd8G0S7S13S7S2dA2R4A4A1SaA3ScbG0SeS7S2dR3R2A4R5A3S0Sb3Q40A1S32SfeR7R5R6A3R4A2S3cR7R3A2A3F_;F_;Fe;Fj;FrhoB;Fl;FrhoA;").
Proof using .
  intros rhoA l. induction l as [|[j' e'] t IH]; intros rhoB j e Hd Hin; [destruct Hin|].
  cbn in Hd. apply andb_prop in Hd as [Hn Hd]. cbn. destruct Hin as [E|Hin].
  - injection E as E1 E2. subst j' e'.
    rewrite set_par_other. { cbn [rw rho_set_rw]. rewrite Pos.eqb_refl. reflexivity. }
    destruct (in_vars (map fst t) j); [discriminate|reflexivity].
  - apply IH; assumption.
Qed.
Lemma setp_get : ltac2:(tb__ "0|1|
S30ScSbS7S2dA2M0A1S7S2dS0S9SffSd8G0S7S13S7S2dA2R3A4A1SaA3ScbG0SeS7S2dR3R2A4R4A3S0Sb3Q40A1S32SfdR6R5A2R4A2S3cR6R3A2A3F_;F_;Fe;Fj;Fl;FrhoB;").
Proof using . intros. unfold setp. apply set_par_get; assumption. Qed.
Lemma setp_other : ltac2:(tb__ "0|1|
S30ScSbS7S2dA2M0A1S7S0S9SceSd8G0S7S13S7S2dA2R2A4R1A2S14A3S0Sb3Q40A1S32SfdR4R3A2R2A2S32R4R2A2A3F_;Fu;Fl;FrhoB;").
Proof using . intros. unfold setp. apply set_par_other; assumption. Qed.
Lemma setp_rl : ltac2:(tb__ "0|0|
S30ScSbS7S2dA2A1S0S7ScSb3Q8A1A1F_;S3eSfdR2R1A2A1S3eR2A1A3Fl;FrhoB;"). Proof using . intros. apply set_par_rl. Qed.
Lemma setp_rm : ltac2:(tb__ "0|0|
S30ScSbS7S2dA2A1S0Sb3Q40A1SdSb3Q8A1A1F_;S41SfdR2R1A2A1S41R2A1A3Fl;FrhoB;"). Proof using . intros. apply set_par_rm. Qed.

Lemma agrees_setp : ltac2:(tb__ "0|1|
S30ScSbS7S2dA2M0A1ScdVrhoW;R2A2S0S9ScaS7S7S15ScfR1A1A1Lj;Sd8G0S7S13S7S2dA2R2A4A3SaA3ScdVrhoW;SfdR4R3A2A2F_;F_;Fl;FrhoB;").
Proof using L am b16 b3 g mW n rho s.
  intros rhoB l (Hw & Hl & Hm) Hb. split; [|split; [intros l0; rewrite setp_rl; apply Hl | rewrite setp_rm; exact Hm]].
  intros u Hu. rewrite setp_other; [apply Hw; exact Hu|].
  rewrite forallb_forall in Hb. destruct (in_vars (map fst l) u) eqn:E; [|reflexivity].
  unfold in_vars in E. apply existsb_exists in E as (u' & Hu' & E). apply Pos.eqb_eq in E. subst u'.
  specialize (Hb u Hu'). rewrite Hu in Hb. discriminate.
Qed.

Lemma relinkp : ltac2:(tb__ "0|4|
S30S35S35Sf9ScSbS7S2dA2M0A1ScSbS2dS2dA2A1M1ScS2eA1M2S0S9S113S7S15SceSd8G0S7S13S7S2dA2R4A4R1A2A1Lu;R6A2SaA3S0S9S38R6A1SaA3S0SdSbG1G2A2M3A1S116R8R7A2S10G3SeG1G2R4R3A4A2A3S118SfdRaR6A2R5A2Sd9S2eS3dSfdRbR7A2A1R5A3Sd6S67VK;RbRcR9A5Sd6S67VK;RbSfdRdR9A2RaA5F_;F_;F_;F_;F_;F_;Fnf;Fd;Fl;Fw;FS';FS;FrhoB;").
Proof using .
  intros rhoB S S' w l d nf Hvars Hwf Hsd Hd Hnf HSP.
  eapply SP_restate; [exact Hwf | exact Hsd | exact Hd | exact Hnf |].
  destruct HSP as [Hsm HK']. split; [|exact HK'].
  apply (smatch_agree_vars segsU (fun u => negb (in_vars (map fst l) u)) rhoB); try assumption.
  - intros u Hu. symmetry. apply setp_other. destruct (in_vars (map fst l) u); [discriminate|reflexivity].
  - intros l0. rewrite setp_rl. reflexivity.
  - rewrite setp_rm. reflexivity.
Qed.

Lemma linkp : ltac2:(tb__ "0|6|
S35S35ScSbS7S2dA2M0A1ScSbS2dS2dA2A1M1ScS2eA1M2S30Sf9S0S9S113S7S15SceSd8G0S7S13S7S2dA2R6A4M3R1A2A1Lu;R7A2SaA3S0S9ScaS7S7S15ScfR1A1A1Lj;G3A3SaA3S0S9S38R8A1SaA3S0SdSbG1G2A2M4A1S116RaR9A2S10G4SeG1G2R7R6A4A2A3ScdVrhoW;R6A2ScdVrhoW;SfdR7RaA2A2Sd9S2eS3dR8A1S3bRdA1A3S1S118SfdR9RcA2M5RbA2Sd9S2eS3dG5A1RaA3A2F_;F_;Sd6S67VK;RdR8R7A5SfcRdR8A2F_;F_;F_;F_;F_;F_;F_;Fw;FrhoB';Fnf;Fd;Fsets;FC;FLf;").
Proof using .
  intros Lf C sets d nf rhoB' w Hvars Hb Hwf Hsd Hag Hsem HSP.
  pose proof (agrees_setp rhoB' sets Hag Hb) as Hag'.
  destruct (Hsem Hag' (SP_facts_hold segsU K rhoB' Lf w HSP)) as [Hd Hnf].
  exists (setp rhoB' sets). split; [exact Hag'|].
  exact (relinkp rhoB' Lf C w sets d nf Hvars Hwf Hsd Hd Hnf HSP).
Qed.

Fixpoint scratch_of (d : list (sv * sv)) : list (positive * sv) :=
  match d with
  | [] => []
  | (e, SVar j) :: t => if (200 <=? j)%positive then (j, e) :: scratch_of t else scratch_of t
  | _ :: t => scratch_of t
  end.

Lemma Zv12 : ltac2:(tb__ "0|0|
S0S6S1fSb5Vs;VL;Vn;Vg;Vam;Vrho;Vb3;Vb16;PcA9S1dZ2Z40A2A2Vn;A3"). Proof using HC HMI HP12 HW Hb16 Hb3 Hhdr. exact ze12. Qed.
Lemma Zv142 : ltac2:(tb__ "0|0|
S0S6S1fSb5Vs;VL;Vn;Vg;Vam;Vrho;Vb3;Vb16;P8eA9S1dZ2Z40A2A2Vb3;A3"). Proof using HC HMI HW Hb16 Hb3 Hhdr. exact ze142. Qed.
Lemma Zv143 : ltac2:(tb__ "0|0|
S0S6S1fSb5Vs;VL;Vn;Vg;Vam;Vrho;Vb3;Vb16;P8fA9S1dZ2Z40A2A2Vb16;A3"). Proof using HC HMI HW Hb16 Hb3 Hhdr. exact ze143. Qed.
Lemma Zv149 : ltac2:(tb__ "0|0|
S0S6S1fSb5Vs;VL;Vn;Vg;Vam;Vrho;Vb3;Vb16;P95A9S1dZ2Z40A2A2Sb8Vn;A1A3"). Proof using HC HMI HW Hb16 Hb3 Hhdr. exact ze149. Qed.
Lemma Zv150 : ltac2:(tb__ "0|0|
S0S6S1fSb5Vs;VL;Vn;Vg;Vam;Vrho;Vb3;Vb16;P96A9S1dZ2Z40A2A2SbbVam;A1A3"). Proof using HC HMI HW Hb16 Hb3 Hhdr. exact ze150. Qed.
Lemma Zv151 : ltac2:(tb__ "0|0|
S0S6S1fSb5Vs;VL;Vn;Vg;Vam;Vrho;Vb3;Vb16;P97A9S1dZ2Z40A2A2Sc7VL;Vg;A2A3"). Proof using HC HMI HW Hb16 Hb3 Hhdr. exact ze151. Qed.
Lemma Zv152 : ltac2:(tb__ "0|0|
S0S6S1fSb5Vs;VL;Vn;Vg;Vam;Vrho;Vb3;Vb16;P98A9S1dZ2Z40A2A2SbfVam;A1A3"). Proof using HC HMI HW Hb16 Hb3 Hhdr. exact ze152. Qed.
Lemma Zv153 : ltac2:(tb__ "0|0|
S0S6S1fSb5Vs;VL;Vn;Vg;Vam;Vrho;Vb3;Vb16;P99A9S1dZ2Z40A2A2Sc1Vs;A1A3"). Proof using HC HMI HW Hb16 Hb3 Hhdr. exact ze153. Qed.
Lemma Zv154 : ltac2:(tb__ "0|0|
S0S6S1fSb5Vs;VL;Vn;Vg;Vam;Vrho;Vb3;Vb16;P9aA9S1dZ2Z40A2A2Sc2Vam;A1A3"). Proof using HC HMI HW Hb16 Hb3 Hhdr. exact ze154. Qed.
Lemma Zv155 : ltac2:(tb__ "0|0|
S0S6S1fSb5Vs;VL;Vn;Vg;Vam;Vrho;Vb3;Vb16;P9bA9S1dZ2Z40A2A2Sc0Vam;A1A3"). Proof using HC HMI HW Hb16 Hb3 Hhdr. exact ze155. Qed.
Lemma Zv156 : ltac2:(tb__ "0|0|
S0S6S1fSb5Vs;VL;Vn;Vg;Vam;Vrho;Vb3;Vb16;P9cA9S1dZ2Z40A2A2Sc8VL;Vam;A2A3"). Proof using HC HMI HW Hb16 Hb3 Hhdr. exact ze156. Qed.
Lemma Zv157 : ltac2:(tb__ "0|0|
S0S6S1fSb5Vs;VL;Vn;Vg;Vam;Vrho;Vb3;Vb16;P9dA9S1dZ2Z40A2A2Sc3Vam;A1A3"). Proof using HC HMI HW Hb16 Hb3 Hhdr. exact ze157. Qed.
Lemma Zv158 : ltac2:(tb__ "0|0|
S0S6S1fSb5Vs;VL;Vn;Vg;Vam;Vrho;Vb3;Vb16;P9eA9S1dZ2Z40A2A2SbcVs;Vn;Vam;Vb3;Vb16;A5A3"). Proof using HC HMI HW Hb16 Hb3 Hhdr. exact ze158. Qed.
Lemma Zv164 : ltac2:(tb__ "0|0|
S0S6S1fSb5Vs;VL;Vn;Vg;Vam;Vrho;Vb3;Vb16;Pa4A9S1dZ2Z40A2A2Sc4Vs;Vn;Vam;A3A3"). Proof using HC HMI HW Hb16 Hb3 Hhdr. exact ze164. Qed.
Lemma Zv165 : ltac2:(tb__ "0|0|
S0S6S1fSb5Vs;VL;Vn;Vg;Vam;Vrho;Vb3;Vb16;Pa5A9S1dZ2Z40A2A2Sc6Vs;Vam;A2A3"). Proof using HC HMI HW Hb16 Hb3 Hhdr. exact ze165. Qed.

Lemma ZE_S : ltac2:(tb__ "0|0|
S0S6S5cSb5Vs;VL;Vn;Vg;Vam;Vrho;Vb3;Vb16;A8Sb7Vs;VL;Vn;Vg;Vam;Vrho;Vb3;Vb16;A8S3fS14Q10S44P1S31S11eS31S11dS39P9bA1S2fZ5A1A3S2fZ7eA1A3Z2A3A3A3SbdVam;A1A3").
Proof using HC HMI HW Hb16 Hb3 Hhdr. exact ze_S. Qed.
Lemma ZE_strideT : ltac2:(tb__ "0|0|
S0S6S5cSb5Vs;VL;Vn;Vg;Vam;Vrho;Vb3;Vb16;A8Sb7Vs;VL;Vn;Vg;Vam;Vrho;Vb3;Vb16;A8S31S11cS3fS14Q10S44P1S31S11eS31S11dS39P9bA1S2fZ5A1A3S2fZ7eA1A3Z2A3A3S2fZ4A1A3A3S1eZ10SbdVam;A1A2A3").
Proof using HC HMI HW Hb16 Hb3 Hhdr. exact ze_strideT. Qed.
Lemma ZE_and155 : ltac2:(tb__ "0|1|
S1cZ0SdcVam;A1M0A2S0S6S5cSb5Vs;VL;Vn;Vg;Vam;Vrho;Vb3;Vb16;A8Sb7Vs;VL;Vn;Vg;Vam;Vrho;Vb3;Vb16;A8S31S11eS39P9bA1S2fZfffffffffffff000A1A3A3S1eG0Z1000A2A3F_;").
Proof using HC HMI HW Hb16 Hb3 Hhdr Hsp.
  intros Hm. rewrite !ze_alu, ze_var, zr1_155, !ze_lit. cbn [zalu]. pose proof bits_range as B. pose proof R_all as R. pose proof Hlast as HL.
  rewrite (Z.mod_small bits) by lia. change (18446744073709547520 mod 2 ^ 64) with 18446744073709547520.
  rewrite (Z.mod_small bits) by lia. rewrite land_not4095 by lia. rewrite bits_eq.
  rewrite <- (Z.mod_unique_pos (am_last am + 32 + 64 * sc + 4096 * am_maplen am) 4096 (am_maplen am) (am_last am + 32 + 64 * sc)) by lia.
  lia.
Qed.
Lemma ZE_strideM : ltac2:(tb__ "0|1|
S1cZ0SdcVam;A1M0A2S0S6S5cSb5Vs;VL;Vn;Vg;Vam;Vrho;Vb3;Vb16;A8Sb7Vs;VL;Vn;Vg;Vam;Vrho;Vb3;Vb16;A8S31S11bS31S11eS39P9bA1S2fZfffffffffffff000A1A3S2fN10A1A3A3S20S1eG0Z1000A2Z10A2A3F_;").
Proof using HC HMI HW Hb16 Hb3 Hhdr. exact ze_strideM. Qed.
Lemma ZE_sll : ltac2:(tb__ "0|0|
S0S6S5cSb5Vs;VL;Vn;Vg;Vam;Vrho;Vb3;Vb16;A8Sb7Vs;VL;Vn;Vg;Vam;Vrho;Vb3;Vb16;A8S43S11cS39P9eA1S2fZ4A1A3A3S1eZ10SbcVs;Vn;Vam;Vb3;Vb16;A5A2A3").
Proof using HC HMI HW Hb16 Hb3 Hhdr Hsp.
  rewrite ze_aluw, ze_var, zr1_158, ze_lit. cbn [zalu]. pose proof R_all as R. pose proof Hoff as HO.
  change ((4 mod 2 ^ 64) mod 2 ^ 32 mod 32) with 4. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 4) with 16.
  rewrite (Z.mod_small off) by lia. rewrite (Z.mod_small off) by lia. rewrite (Z.mod_small (off * 16)) by lia.
  rewrite sx32_small by lia. lia.
Qed.

Lemma land_255 : ltac2:(tb__ "0|0|
S6S0S6S23R1ZffA2S1fR1Z100A2A3Fa;").
Proof using Hb16 Hb3 rho. intros a. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma land_31' : ltac2:(tb__ "0|0|
S6S0S6S23R1Z1fA2S1fR1Z20A2A3Fa;").
Proof using Hb16 Hb3 rho. intros a. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. reflexivity. Qed.

Ltac zlits :=
  repeat match goal with
  | |- context [ (?x mod ?y) ] =>
      lazymatch x with Z0 => idtac | Zpos _ => idtac | Zneg _ => idtac end;
      lazymatch y with Zpos _ => idtac | Z.pow (Zpos _) (Zpos _) => idtac end;
      let vv := eval vm_compute in (x mod y) in change (x mod y) with vv
  end.

Ltac mlia := Z.to_euclidean_division_equations; lia.

Ltac zev :=
  rewrite ?ZE_strideT, ?ZE_sll;
  try rewrite ZE_strideM by lia; try rewrite ZE_and155 by lia;
  cbn [zeval zholds zcond zalu Z.of_N];
  zlits;
  rewrite ?Zv12, ?Zv142, ?Zv143, ?Zv149, ?Zv150, ?Zv151, ?Zv152, ?Zv153, ?Zv154, ?Zv155, ?Zv156, ?Zv157, ?Zv158, ?Zv164, ?Zv165;
  rewrite ?Z.shiftr_div_pow2, ?Z.shiftl_mul_pow2 by lia;
  rewrite ?land_255, ?land_31'.

Lemma F_all_hold : ltac2:(tb__ "0|0|
S30ScdVrhoW;R1A2Sd9S2eS3dR2A1Sa0Sb6Vam;A1A1A3F_;Frho';").
Proof using HC HMI HP12 HW Hb16 Hb3 Hdepth Hhdr Hsp Hsp_high mW.
  intros rho' (Hw & Hl & _). apply Forall_forall. intros p Hp.
  assert (Hv : sprop_vars_all below200 p = true).
  { assert (A : forall kd', forallb (sprop_vars_all below200) (F_all kd') = true) by (intros [| |]; vm_cast_no_check (@eq_refl bool true)).
    exact (proj1 (forallb_forall _ _) (A kd) p Hp). }
  rewrite (holds_agree_vars below200 rho' rhoW p Hw Hl Hv).
  exact (proj1 (Forall_forall _ _) (facts_hold mW) p Hp).
Qed.

Ltac scratch_pair Hag HagS :=
  lazymatch goal with |- eval (setp ?r0 ?l) ?e = eval (setp ?r0 ?l) (SVar ?j) =>
    change (eval (setp r0 l) (SVar j)) with (rw (setp r0 l) j);
    rewrite (setp_get r0 l j e eq_refl) by (cbn; tauto);
    rewrite (eval_agrees rhoW (setp r0 l) e HagS) by reflexivity;
    rewrite (eval_agrees rhoW r0 e Hag) by reflexivity; reflexivity
  end.

Ltac sem_pair HagS :=
  rewrite !(EV _ _ HagS) by reflexivity; f_equal.

Definition D05c : list (sv * sv) * list sprop := Eval vm_compute in D05 VL.
Definition D5ac : list (sv * sv) * list sprop := Eval vm_compute in D5a VL.
Definition D5bc : list (sv * sv) * list sprop := Eval vm_compute in D5b VL.
Definition D11c : list (sv * sv) * list sprop := Eval vm_compute in D11 VL.
Definition D22c : list (sv * sv) * list sprop := Eval vm_compute in D22 VL.
Definition D33c : list (sv * sv) * list sprop := Eval vm_compute in D33 VL.
Definition D44c : list (sv * sv) * list sprop := Eval vm_compute in D44 VL.
Definition D66c : list (sv * sv) * list sprop := Eval vm_compute in D66 VL.

Local Ltac sd_tac v := intros [| |]; vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some v)).
Lemma sd_05 : ltac2:(tb__ "0|1|
S9cS0SdSbScSbS2dS2dA2A1ScS2eA1A2M0A1S116S152R1A1S150R1A1A2S10G0S100A2A3Fkd0;"). Proof using . sd_tac D05c. Qed.
Lemma sd_5a : ltac2:(tb__ "0|1|
S9cS0SdSbScSbS2dS2dA2A1ScS2eA1A2M0A1S116S153R1A1S150R1A1A2S10G0S106A2A3Fkd0;"). Proof using . sd_tac D5ac. Qed.
Lemma sd_5b : ltac2:(tb__ "0|1|
S9cS0SdSbScSbS2dS2dA2A1ScS2eA1A2M0A1S116S154R1A1S150R1A1A2S10G0S108A2A3Fkd0;"). Proof using . sd_tac D5bc. Qed.
Lemma sd_11 : ltac2:(tb__ "0|1|
S9cS0SdSbScSbS2dS2dA2A1ScS2eA1A2M0A1S116S167R1A1S160R1A1A2S10G0S102A2A3Fkd0;"). Proof using . sd_tac D11c. Qed.
Lemma sd_22 : ltac2:(tb__ "0|1|
S9cS0SdSbScSbS2dS2dA2A1ScS2eA1A2M0A1S116S168R1A1S161R1A1A2S10G0S103A2A3Fkd0;"). Proof using . sd_tac D22c. Qed.
Lemma sd_33 : ltac2:(tb__ "0|1|
S9cS0SdSbScSbS2dS2dA2A1ScS2eA1A2M0A1S116S169R1A1S162R1A1A2S10G0S104A2A3Fkd0;"). Proof using . sd_tac D33c. Qed.
Lemma sd_44 : ltac2:(tb__ "0|1|
S9cS0SdSbScSbS2dS2dA2A1ScS2eA1A2M0A1S116S16aR1A1S163R1A1A2S10G0S105A2A3Fkd0;"). Proof using . sd_tac D44c. Qed.
Lemma sd_66 : ltac2:(tb__ "0|1|
S9cS0SdSbScSbS2dS2dA2A1ScS2eA1A2M0A1S116S16dR1A1S157R1A1A2S10G0S10bA2A3Fkd0;"). Proof using . sd_tac D66c. Qed.

Lemma L1_eq : ltac2:(tb__ "0|0|
S9cS0ScSd1A1S172R1A1SfSd1Sd3S167R1A1Sd2A2S12Sd1A1A3A3Fkd0;"). Proof using . intros [| |]; match goal with |- ?l = _ => vm_cast_no_check (@eq_refl (list leaf) l) end. Qed.
Lemma L2_eq : ltac2:(tb__ "0|0|
S9cS0ScSd1A1S173R1A1SfSd1Sd3S168R1A1Sd2A2S12Sd1A1A3A3Fkd0;"). Proof using . intros [| |]; match goal with |- ?l = _ => vm_cast_no_check (@eq_refl (list leaf) l) end. Qed.
Lemma L3_eq : ltac2:(tb__ "0|0|
S9cS0ScSd1A1S174R1A1SfSd1Sd3S169R1A1Sd2A2S12Sd1A1A3A3Fkd0;"). Proof using . intros [| |]; match goal with |- ?l = _ => vm_cast_no_check (@eq_refl (list leaf) l) end. Qed.
Lemma L4_eq : ltac2:(tb__ "0|0|
S9cS0ScSd1A1S175R1A1SfSd1Sd3S16aR1A1Sd2A2S12Sd1A1A3A3Fkd0;"). Proof using . intros [| |]; match goal with |- ?l = _ => vm_cast_no_check (@eq_refl (list leaf) l) end. Qed.
Lemma L5_eq : ltac2:(tb__ "0|0|
S9cS0ScSd1A1S176R1A1SfSd1Sd3S153R1A1Sd2A2SfSd1Sd3S154R1A1Sd2A2S12Sd1A1A3A3A3Fkd0;"). Proof using . intros [| |]; match goal with |- ?l = _ => vm_cast_no_check (@eq_refl (list leaf) l) end. Qed.
Lemma L6_eq : ltac2:(tb__ "0|0|
S9cS0ScSd1A1S178R1A1SfSd1Sd3S16dR1A1Sd2A2S12Sd1A1A3A3Fkd0;"). Proof using . intros [| |]; match goal with |- ?l = _ => vm_cast_no_check (@eq_refl (list leaf) l) end. Qed.

Local Ltac by_kinds := intros [| |]; vm_cast_no_check (@eq_refl bool true).
Lemma swf_C5 : ltac2:(tb__ "0|0|
S9cS0S9S38S150R1A1A1SaA3Fkd0;"). Proof using . by_kinds. Qed.
Lemma swf_Ck : ltac2:(tb__ "0|0|
S9cS0S9S38S165R1A1A1SaA3Fkd0;"). Proof using . by_kinds. Qed.
Lemma swf_C1 : ltac2:(tb__ "0|0|
S9cS0S9S38S160R1A1A1SaA3Fkd0;"). Proof using . by_kinds. Qed.
Lemma swf_C2 : ltac2:(tb__ "0|0|
S9cS0S9S38S161R1A1A1SaA3Fkd0;"). Proof using . by_kinds. Qed.
Lemma swf_C3 : ltac2:(tb__ "0|0|
S9cS0S9S38S162R1A1A1SaA3Fkd0;"). Proof using . by_kinds. Qed.
Lemma swf_C4 : ltac2:(tb__ "0|0|
S9cS0S9S38S163R1A1A1SaA3Fkd0;"). Proof using . by_kinds. Qed.
Lemma swf_C6 : ltac2:(tb__ "0|0|
S9cS0S9S38S157R1A1A1SaA3Fkd0;"). Proof using . by_kinds. Qed.

Definition SETS5 : list (positive * sv) := scratch_of (fst D05c).
Definition SETS5a : list (positive * sv) := scratch_of (fst D5ac).
Definition SETS5b : list (positive * sv) := scratch_of (fst D5bc).
Lemma vars_05 : ltac2:(tb__ "0|0|
S9cS0S9S113S7S15SceSd8SbS7S2dA2S7S13S7S2dA2S10dA4R1A2A1Lu;S152R1A1A2SaA3Fkd0;"). Proof using . by_kinds. Qed.
Lemma vars_5a : ltac2:(tb__ "0|0|
S9cS0S9S113S7S15SceSd8SbS7S2dA2S7S13S7S2dA2S10eA4R1A2A1Lu;S153R1A1A2SaA3Fkd0;"). Proof using . by_kinds. Qed.
Lemma vars_5b : ltac2:(tb__ "0|0|
S9cS0S9S113S7S15SceSd8SbS7S2dA2S7S13S7S2dA2S110A4R1A2A1Lu;S154R1A1A2SaA3Fkd0;"). Proof using . by_kinds. Qed.

Lemma kq_small : ltac2:(tb__ "0|0|
S1cVn;Z9dA2S0S6Sb8Vn;A1Sb9Vn;A1A3F_;").
Proof using HC HMI HW Hb16 Hb3 Hhdr Hsp. intros Hn157. pose proof Hkq as [Hk E]. rewrite E. unfold class_of_units. pose proof n157_kq as NK.
  destruct (kq <? 10) eqn:C; [reflexivity|]. apply Z.ltb_ge in C. lia. Qed.

Lemma ze_kexpr : ltac2:(tb__ "0|0|
S0S6S5cSb5Vs;VL;Vn;Vg;Vam;Vrho;Vb3;Vb16;A8Sb7Vs;VL;Vn;Vg;Vam;Vrho;Vb3;Vb16;A8S31S11dS31S11bS39PcA1S2fZ3A1A3S2fZ4A1A3A3Sb8Vn;A1A3").
Proof using HC HMI HP12 HW Hb16 Hb3 Hhdr Hsp. exact ze_kq. Qed.

Lemma link_05 : ltac2:(tb__ "0|1|
S0S6SbbVam;A1Sb9Vn;A1A3S30Sf9ScdVrhoW;R2A2Sd6S67VK;S152Sb6Vam;A1M0A1R3R2A5SfcS150G0A1R3A2F_;F_;Fw;Frho';F_;").
Proof using HC HMI HP12 HW Hb16 Hb3 Hdepth Hhdr Hsp.
  intros Hrt rho' w Hag HSP. pose proof R_all as R.
  assert (Hn157 : n < 157).
  { pose proof (leaf_fact rho' _ w _ Hag HSP (L0s_fact kd) eq_refl eq_refl) as F. cbn [zholds zcond] in F.
    rewrite ze_lit, ze_var, zr1_12 in F. change (157 mod 2 ^ 64) with 157 in F. rewrite Z.mod_small in F by (unfold MMAP_THRESHOLD in R; lia).
    destruct (n <? 157) eqn:E; [apply Z.ltb_lt in E; exact E | discriminate]. }
  eapply (linkp (L0s kd) (C5 kd) SETS5 _ _ rho' w); [apply vars_05 | reflexivity | apply swf_C5 | apply sd_05 | exact Hag | | exact HSP].
  intros HagS _. cbn [D05c fst snd]. split; [|constructor].
  unfold diffs_ok.
  repeat (apply Forall_cons; [cbn [fst snd]|]); [ .. | apply Forall_nil].
  all: first [scratch_pair Hag HagS | sem_pair HagS].

  rewrite ze_kexpr. zev. rewrite Hrt. apply kq_small. exact Hn157.
Qed.

Lemma ZF_holds : ltac2:(tb__ "0|0|
S30ScS2eA1ScdVrhoW;R2A2S0S9ScaS2eS114ScfA1R2A3SaA3S0S9ScaS2eS5fR3A3SaA3Sd9S2eS5eSb5Vs;VL;Vn;Vg;Vam;Vrho;Vb3;Vb16;A8Sb7Vs;VL;Vn;Vg;Vam;Vrho;Vb3;Vb16;A8A2R4A3Sd9S2eS3dR6A1R5A3F_;F_;F_;F_;Fl;Frho';").
Proof using mW.
  intros rho' l Hag Hv Hs HZ. apply Forall_forall. intros p Hp.
  apply (proj2 (HOLDS rho' p Hag (proj1 (forallb_forall _ _) Hv p Hp) (proj1 (forallb_forall _ _) Hs p Hp))).
  exact (proj1 (Forall_forall _ _) HZ p Hp).
Qed.

Lemma in_facts_b : ltac2:(tb__ "0|0|
S2eS35S0S9SccS2eS42R2A1S3bR1A1A3SaA3ScbS2eR3S3bR2A1A3F_;FS;Fp;").
Proof using .
  intros p S H. apply existsb_exists in H as (q & Hq & E). apply sprop_eqb_sound in E. subst q. exact Hq.
Qed.

Lemma from_POST : ltac2:(tb__ "0|0|
S35SfbS30ScdVrhoW;R1A2SfaS67Vok;Sd6S67VK;R4R2A4R3A4F_;Frho';SfaS67Vok;SfcR3A1R2A4F_;FQ;FC;").
Proof using . intros C Q H. unfold POST. apply triple_ex. intros rho'. apply triple_pure. apply H. Qed.

Lemma P5a_in : ltac2:(tb__ "0|0|
S9cS0S9ScaS2eS2eSccS2eS42R1A1S3bS153R2A1A1A3Lp;S155A3SaA3Fkd0;"). Proof using . by_kinds. Qed.
Lemma P5b_in : ltac2:(tb__ "0|0|
S9cS0S9ScaS2eS2eSccS2eS42R1A1S3bS154R2A1A1A3Lp;S156A3SaA3Fkd0;"). Proof using . by_kinds. Qed.
Lemma P5_supported : ltac2:(tb__ "0|1|
S1S0S9ScaS2eS114ScfA1M0S155A3SaA3S1S0S9ScaS2eS5fS155A3SaA3S1S0S9ScaS2eG0S156A3SaA3S0S9ScaS2eS5fS156A3SaA3A2A2A2").
Proof using . repeat split; vm_cast_no_check (@eq_refl bool true). Qed.
Lemma F34_supported : ltac2:(tb__ "0|1|
S1S0S9ScaS2eS114ScfA1M0S158A3SaA3S1S0S9ScaS2eS5fS158A3SaA3S1S0S9ScaS2eG0S159A3SaA3S0S9ScaS2eS5fS159A3SaA3A2A2A2").
Proof using . repeat split; vm_cast_no_check (@eq_refl bool true). Qed.

Lemma leaf_facts_Z : ltac2:(tb__ "0|0|
S30S35Sf9ScS2eA1ScdVrhoW;R4A2Sd6S67VK;R4R5R3A5S0S9ScaS2eS2eSccS2eS42R1A1S3bR6A1A3Lp;R3A3SaA3S0S9ScaS2eS114ScfA1R4A3SaA3S0S9ScaS2eS5fR5A3SaA3Sd9S2eS5eSb5Vs;VL;Vn;Vg;Vam;Vrho;Vb3;Vb16;A8Sb7Vs;VL;Vn;Vg;Vam;Vrho;Vb3;Vb16;A8A2R6A3F_;F_;F_;F_;F_;Fl;Fw;FS;Frho';").
Proof using mW.
  intros rho' S w l Hag HSP Hin Hv Hs. apply Forall_forall. intros p Hp.
  apply (leaf_fact rho' S w p Hag HSP).
  - apply in_facts_b. exact (proj1 (forallb_forall _ _) Hin p Hp).
  - exact (proj1 (forallb_forall _ _) Hv p Hp).
  - exact (proj1 (forallb_forall _ _) Hs p Hp).
Qed.

Lemma link_5a : ltac2:(tb__ "0|1|
S0S6SbbVam;A1Sb9Vn;A1A3S30Sf9S1aZaSb8Vn;A1A2ScdVrhoW;R3A2Sd6S67VK;S153Sb6Vam;A1M0A1R4R3A5SfcS150G0A1R4A2F_;F_;F_;Fw;Frho';F_;").
Proof using HC HMI HW Hb16 Hb3 Hdepth Hhdr Hsp.
  intros Hrt rho' w Hk Hag HSP. pose proof R_all as R.
  pose proof (stage_cert Hk) as (_ & _ & _ & S5a & _).
  pose proof P5_supported as (Pv & Ps & _ & _).
  pose proof (S5a (leaf_facts_Z rho' _ w P5a Hag HSP (P5a_in kd) Pv Ps)) as E5.
  eapply (linkp (L5a kd) (C5 kd) SETS5a _ _ rho' w); [apply vars_5a | reflexivity | apply swf_C5 | apply sd_5a | exact Hag | | exact HSP].
  intros HagS _. cbn [D5ac fst snd]. split; [|constructor].
  unfold diffs_ok.
  repeat (apply Forall_cons; [cbn [fst snd]|]); [ .. | apply Forall_nil].
  all: first [scratch_pair Hag HagS | sem_pair HagS].
  transitivity (sc : Z); [rewrite Hrt; exact E5 | symmetry; exact Zv150].
Qed.

Lemma link_5b : ltac2:(tb__ "0|1|
S0S6SbbVam;A1Sb9Vn;A1A3S30Sf9S1aZaSb8Vn;A1A2ScdVrhoW;R3A2Sd6S67VK;S154Sb6Vam;A1M0A1R4R3A5SfcS150G0A1R4A2F_;F_;F_;Fw;Frho';F_;").
Proof using HC HMI HW Hb16 Hb3 Hdepth Hhdr Hsp.
  intros Hrt rho' w Hk Hag HSP. pose proof R_all as R.
  pose proof (stage_cert Hk) as (_ & _ & _ & _ & S5b).
  pose proof P5_supported as (_ & _ & Pv & Ps).
  pose proof (S5b (leaf_facts_Z rho' _ w P5b Hag HSP (P5b_in kd) Pv Ps)) as E5.
  eapply (linkp (L5b kd) (C5 kd) SETS5b _ _ rho' w); [apply vars_5b | reflexivity | apply swf_C5 | apply sd_5b | exact Hag | | exact HSP].
  intros HagS _. cbn [D5bc fst snd]. split; [|constructor].
  unfold diffs_ok.
  repeat (apply Forall_cons; [cbn [fst snd]|]); [ .. | apply Forall_nil].
  all: first [scratch_pair Hag HagS | sem_pair HagS].
  transitivity (sc : Z); [rewrite Hrt; exact E5 | symmetry; exact Zv150].
Qed.

Lemma vars_none : ltac2:(tb__ "0|1|
S35S4S0S9S113S7S15SceSd8SbS7S2dA2M0S7S13S7S2dA2S12G0A1A4R1A2A1Lu;R1A2SaA3S0S9S113S7SaL_;R1A2SaA3A2FS;").
Proof using Hb16 Hb3 Hdepth Hsp. intros S. cbn [map in_vars existsb negb]. tauto. Qed.
Lemma vars_L1s : ltac2:(tb__ "0|1|
S9cS0S9S113S7S15SceSd8SbS7S2dA2M0S7S13S7S2dA2S12G0A1A4R1A2A1Lu;S167R1A1A2SaA3Fkd0;"). Proof using . by_kinds. Qed.
Lemma vars_L2s : ltac2:(tb__ "0|1|
S9cS0S9S113S7S15SceSd8SbS7S2dA2M0S7S13S7S2dA2S12G0A1A4R1A2A1Lu;S168R1A1A2SaA3Fkd0;"). Proof using . by_kinds. Qed.
Lemma vars_L3s : ltac2:(tb__ "0|1|
S9cS0S9S113S7S15SceSd8SbS7S2dA2M0S7S13S7S2dA2S12G0A1A4R1A2A1Lu;S169R1A1A2SaA3Fkd0;"). Proof using . by_kinds. Qed.
Lemma vars_L4s : ltac2:(tb__ "0|1|
S9cS0S9S113S7S15SceSd8SbS7S2dA2M0S7S13S7S2dA2S12G0A1A4R1A2A1Lu;S16aR1A1A2SaA3Fkd0;"). Proof using . by_kinds. Qed.
Lemma vars_L6s : ltac2:(tb__ "0|1|
S9cS0S9S113S7S15SceSd8SbS7S2dA2M0S7S13S7S2dA2S12G0A1A4R1A2A1Lu;S16dR1A1A2SaA3Fkd0;"). Proof using . by_kinds. Qed.

Lemma link_11 : ltac2:(tb__ "0|1|
S30Sf9S1aZaSb8Vn;A1A2ScdVrhoW;R3A2Sd6S67VK;S167Sb6Vam;A1M0A1R4R3A5SfcS160G0A1R4A2F_;F_;F_;Fw;Frho';").
Proof using HC HMI HW Hb16 Hb3 Hhdr.
  intros rho' w Hk Hag HSP. destruct zr1_stages as (E149 & E160 & E161 & E162 & E163 & El1 & El4). pose proof Gk_range as GR.
  eapply (linkp (L1s kd) (C1 kd) [] _ _ rho' w); [apply vars_L1s | reflexivity | apply swf_C1 | apply sd_11 | exact Hag | | exact HSP].
  intros HagS _. cbn [D11c fst snd]. split; [|constructor].
  unfold diffs_ok. apply Forall_cons; [cbn [fst snd]|apply Forall_nil]. sem_pair HagS.
  transitivity (zr1 160%positive); [exact (eq_sym E160) | rewrite zr1_160; symmetry; exact (eq_trans (ze_var 160%positive) (eq_trans (f_equal (fun x => x mod 2 ^ 64) zr1_160) (Z.mod_small _ _ (proj1 GR))))].
Qed.

Lemma link_22 : ltac2:(tb__ "0|1|
S30Sf9S1aZaSb8Vn;A1A2ScdVrhoW;R3A2Sd6S67VK;S168Sb6Vam;A1M0A1R4R3A5SfcS161G0A1R4A2F_;F_;F_;Fw;Frho';").
Proof using HC HMI HW Hb16 Hb3 Hhdr.
  intros rho' w Hk Hag HSP. destruct zr1_stages as (E149 & E160 & E161 & E162 & E163 & El1 & El4). pose proof Gk_range as GR.
  eapply (linkp (L2s kd) (C2 kd) [] _ _ rho' w); [apply vars_L2s | reflexivity | apply swf_C2 | apply sd_22 | exact Hag | | exact HSP].
  intros HagS _. cbn [D22c fst snd]. split; [|constructor].
  unfold diffs_ok. apply Forall_cons; [cbn [fst snd]|apply Forall_nil]. sem_pair HagS.
  transitivity (zr1 161%positive); [exact (eq_sym E161) | change (zeval zr1 zl1 (SVar 161)) with (zr1 161%positive mod 2 ^ 64); rewrite zr1_161; symmetry; apply Z.mod_small; lia].
Qed.

Lemma link_33 : ltac2:(tb__ "0|1|
S30Sf9S1aZaSb8Vn;A1A2ScdVrhoW;R3A2Sd6S67VK;S169Sb6Vam;A1M0A1R4R3A5SfcS162G0A1R4A2F_;F_;F_;Fw;Frho';").
Proof using HC HMI HW Hb16 Hb3 Hhdr.
  intros rho' w Hk Hag HSP. destruct zr1_stages as (E149 & E160 & E161 & E162 & E163 & El1 & El4). pose proof Gk_range as GR.
  pose proof (stage_cert Hk) as (S3 & _).
  pose proof F34_supported as (F3v & F3s & _ & _).
  eapply (linkp (L3s kd) (C3 kd) [] _ _ rho' w); [apply vars_L3s | reflexivity | apply swf_C3 | apply sd_33 | exact Hag | | exact HSP].
  intros HagS _. cbn [D33c fst snd]. split.
  - unfold diffs_ok. apply Forall_cons; [cbn [fst snd]|apply Forall_nil]. sem_pair HagS.
    transitivity (zr1 162%positive); [exact (eq_sym E162) | change (zeval zr1 zl1 (SVar 162)) with (zr1 162%positive mod 2 ^ 64); rewrite zr1_162; symmetry; apply Z.mod_small; lia].
  - exact (ZF_holds _ F3 HagS F3v F3s S3).
Qed.

Lemma link_44 : ltac2:(tb__ "0|1|
S30Sf9S1aZaSb8Vn;A1A2ScdVrhoW;R3A2Sd6S67VK;S16aSb6Vam;A1M0A1R4R3A5SfcS163G0A1R4A2F_;F_;F_;Fw;Frho';").
Proof using HC HMI HW Hb16 Hb3 Hhdr.
  intros rho' w Hk Hag HSP. destruct zr1_stages as (E149 & E160 & E161 & E162 & E163 & El1 & El4). pose proof Gk_range as GR.
  pose proof (stage_cert Hk) as (_ & S4 & _).
  pose proof F34_supported as (_ & _ & F4v & F4s).
  eapply (linkp (L4s kd) (C4 kd) [] _ _ rho' w); [apply vars_L4s | reflexivity | apply swf_C4 | apply sd_44 | exact Hag | | exact HSP].
  intros HagS _. cbn [D44c fst snd]. split.
  - unfold diffs_ok. apply Forall_cons; [cbn [fst snd]|apply Forall_nil]. sem_pair HagS.
    transitivity (zr1 163%positive); [exact (eq_sym E163) | change (zeval zr1 zl1 (SVar 163)) with (zr1 163%positive mod 2 ^ 64); rewrite zr1_163; symmetry; apply Z.mod_small; lia].
  - exact (ZF_holds _ F4 HagS F4v F4s S4).
Qed.

Lemma link_66 : ltac2:(tb__ "0|1|
S30Sf9ScdVrhoW;R2A2Sd6S67VK;S16dSb6Vam;A1M0A1R3R2A5SfcS157G0A1R3A2F_;F_;Fw;Frho';").
Proof using HC HMI HW Hb16 Hb3 Hhdr.
  intros rho' w Hag HSP. pose proof R_all as R.
  eapply (linkp (L6s kd) (C6 kd) [] _ _ rho' w); [apply vars_L6s | reflexivity | apply swf_C6 | apply sd_66 | exact Hag | | exact HSP].
  intros HagS _. cbn [D66c fst snd]. split; [|constructor].
  unfold diffs_ok. apply Forall_cons; [cbn [fst snd]|apply Forall_nil]. sem_pair HagS.
  transitivity (idx : Z); [exact ze_T6 | symmetry; exact Zv157].
Qed.

Definition D05qc : list (sv * sv) * list sprop := Eval vm_compute in D05q VL.
Definition D5aqc : list (sv * sv) * list sprop := Eval vm_compute in D5aq VL.
Definition D5bqc : list (sv * sv) * list sprop := Eval vm_compute in D5bq VL.
Definition D5oc : list (sv * sv) * list sprop := Eval vm_compute in D5o VL.
Definition D6oc : list (sv * sv) * list sprop := Eval vm_compute in D6o VL.
Lemma sd_05q : ltac2:(tb__ "0|1|
S9cS0SdSbScSbS2dS2dA2A1ScS2eA1A2M0A1S116S152R1A1S151R1A1A2S10G0S101A2A3Fkd0;"). Proof using . sd_tac D05qc. Qed.
Lemma sd_5aq : ltac2:(tb__ "0|1|
S9cS0SdSbScSbS2dS2dA2A1ScS2eA1A2M0A1S116S153R1A1S151R1A1A2S10G0S107A2A3Fkd0;"). Proof using . sd_tac D5aqc. Qed.
Lemma sd_5bq : ltac2:(tb__ "0|1|
S9cS0SdSbScSbS2dS2dA2A1ScS2eA1A2M0A1S116S154R1A1S151R1A1A2S10G0S109A2A3Fkd0;"). Proof using . sd_tac D5bqc. Qed.
Lemma sd_5o : ltac2:(tb__ "0|1|
S9cS0SdSbScSbS2dS2dA2A1ScS2eA1A2M0A1S116S16bR1A1S164R1A1A2S10G0S10aA2A3Fkd0;"). Proof using . sd_tac D5oc. Qed.
Lemma sd_6o : ltac2:(tb__ "0|1|
S9cS0SdSbScSbS2dS2dA2A1ScS2eA1A2M0A1S116S16cR1A1S157R1A1A2S10G0S10cA2A3Fkd0;"). Proof using . sd_tac D6oc. Qed.
Lemma L5q_eq : ltac2:(tb__ "0|0|
S9cS0ScSd1A1S177R1A1SfSd1Sd3S16bR1A1Sd2A2S12Sd1A1A3A3Fkd0;"). Proof using . intros [| |]; match goal with |- ?l = _ => vm_cast_no_check (@eq_refl (list leaf) l) end. Qed.
Lemma L6o_eq : ltac2:(tb__ "0|0|
S9cS0ScSd1A1S179R1A1SfSd1Sd3S16cR1A1Sd2A2S12Sd1A1A3A3Fkd0;"). Proof using . intros [| |]; match goal with |- ?l = _ => vm_cast_no_check (@eq_refl (list leaf) l) end. Qed.
Lemma swf_C5q : ltac2:(tb__ "0|0|
S9cS0S9S38S151R1A1A1SaA3Fkd0;"). Proof using . by_kinds. Qed.
Lemma swf_C5o : ltac2:(tb__ "0|0|
S9cS0S9S38S164R1A1A1SaA3Fkd0;"). Proof using . by_kinds. Qed.
Definition SETS5q : list (positive * sv) := scratch_of (fst D05qc).
Definition SETS5aq : list (positive * sv) := scratch_of (fst D5aqc).
Definition SETS5bq : list (positive * sv) := scratch_of (fst D5bqc).
Lemma vars_05q : ltac2:(tb__ "0|0|
S9cS0S9S113S7S15SceSd8SbS7S2dA2S7S13S7S2dA2S112A4R1A2A1Lu;S152R1A1A2SaA3Fkd0;"). Proof using . by_kinds. Qed.
Lemma vars_5aq : ltac2:(tb__ "0|0|
S9cS0S9S113S7S15SceSd8SbS7S2dA2S7S13S7S2dA2S10fA4R1A2A1Lu;S153R1A1A2SaA3Fkd0;"). Proof using . by_kinds. Qed.
Lemma vars_5bq : ltac2:(tb__ "0|0|
S9cS0S9S113S7S15SceSd8SbS7S2dA2S7S13S7S2dA2S111A4R1A2A1Lu;S154R1A1A2SaA3Fkd0;"). Proof using . by_kinds. Qed.
Lemma vars_L5qs : ltac2:(tb__ "0|1|
S9cS0S9S113S7S15SceSd8SbS7S2dA2M0S7S13S7S2dA2S12G0A1A4R1A2A1Lu;S16bR1A1A2SaA3Fkd0;"). Proof using . by_kinds. Qed.
Lemma vars_L6os : ltac2:(tb__ "0|1|
S9cS0S9S113S7S15SceSd8SbS7S2dA2M0S7S13S7S2dA2S12G0A1A4R1A2A1Lu;S16cR1A1A2SaA3Fkd0;"). Proof using . by_kinds. Qed.
Lemma F5_vs : ltac2:(tb__ "0|0|
S1S0S9ScaS2eS114ScfA1Sa1A3SaA3S0S9ScaS2eS5fSa1A3SaA3A2").
Proof using . split; vm_cast_no_check (@eq_refl bool true). Qed.

Lemma link_05q : ltac2:(tb__ "0|1|
S0S9SbaVs;Vn;A2SaA3S30Sf9ScdVrhoW;R2A2Sd6S67VK;S152Sb6Vam;A1M0A1R3R2A5SfcS151G0A1R3A2F_;F_;Fw;Frho';F_;").
Proof using HC HMI HP12 HW Hb16 Hb3 Hdepth Hhdr Hsp.
  intros Hrc rho' w Hag HSP. pose proof R_all as R. pose proof (RC_vals Hrc) as (J & _). pose proof F5_vs as [F5v F5s].
  assert (Hn157 : n < 157).
  { pose proof (leaf_fact rho' _ w _ Hag HSP (L0s_fact kd) eq_refl eq_refl) as F. cbn [zholds zcond] in F.
    rewrite ze_lit, ze_var, zr1_12 in F. change (157 mod 2 ^ 64) with 157 in F. rewrite Z.mod_small in F by (unfold MMAP_THRESHOLD in R; lia).
    destruct (n <? 157) eqn:E; [apply Z.ltb_lt in E; exact E | discriminate]. }
  eapply (linkp (L0s kd) (C5q kd) SETS5q _ _ rho' w); [apply vars_05q | reflexivity | apply swf_C5q | apply sd_05q | exact Hag | | exact HSP].
  intros HagS _. cbn [D05qc fst snd]. split; [| exact (ZF_holds _ F5 HagS F5v F5s (ZF5 Hrc))].
  unfold diffs_ok.
  repeat (apply Forall_cons; [cbn [fst snd]|]); [ .. | apply Forall_nil].
  all: first [scratch_pair Hag HagS | sem_pair HagS].
  rewrite ze_kexpr. zev. rewrite J. apply kq_small. exact Hn157.
Qed.

Lemma link_5aq : ltac2:(tb__ "0|1|
S0S9SbaVs;Vn;A2SaA3S30Sf9S1aZaSb8Vn;A1A2ScdVrhoW;R3A2Sd6S67VK;S153Sb6Vam;A1M0A1R4R3A5SfcS151G0A1R4A2F_;F_;F_;Fw;Frho';F_;").
Proof using HC HMI HW Hb16 Hb3 Hdepth Hhdr Hsp.
  intros Hrc rho' w Hk Hag HSP. pose proof R_all as R. pose proof (RC_vals Hrc) as (J & _). pose proof F5_vs as [F5v F5s].
  pose proof (stage_cert Hk) as (_ & _ & _ & S5a & _).
  pose proof P5_supported as (Pv & Ps & _ & _).
  pose proof (S5a (leaf_facts_Z rho' _ w P5a Hag HSP (P5a_in kd) Pv Ps)) as E5.
  eapply (linkp (L5a kd) (C5q kd) SETS5aq _ _ rho' w); [apply vars_5aq | reflexivity | apply swf_C5q | apply sd_5aq | exact Hag | | exact HSP].
  intros HagS _. cbn [D5aqc fst snd]. split; [| exact (ZF_holds _ F5 HagS F5v F5s (ZF5 Hrc))].
  unfold diffs_ok.
  repeat (apply Forall_cons; [cbn [fst snd]|]); [ .. | apply Forall_nil].
  all: first [scratch_pair Hag HagS | sem_pair HagS].
  transitivity (sc0 : Z); [exact E5 | symmetry; rewrite <- J; exact Zv164].
Qed.

Lemma link_5bq : ltac2:(tb__ "0|1|
S0S9SbaVs;Vn;A2SaA3S30Sf9S1aZaSb8Vn;A1A2ScdVrhoW;R3A2Sd6S67VK;S154Sb6Vam;A1M0A1R4R3A5SfcS151G0A1R4A2F_;F_;F_;Fw;Frho';F_;").
Proof using HC HMI HW Hb16 Hb3 Hdepth Hhdr Hsp.
  intros Hrc rho' w Hk Hag HSP. pose proof R_all as R. pose proof (RC_vals Hrc) as (J & _). pose proof F5_vs as [F5v F5s].
  pose proof (stage_cert Hk) as (_ & _ & _ & _ & S5b).
  pose proof P5_supported as (_ & _ & Pv & Ps).
  pose proof (S5b (leaf_facts_Z rho' _ w P5b Hag HSP (P5b_in kd) Pv Ps)) as E5.
  eapply (linkp (L5b kd) (C5q kd) SETS5bq _ _ rho' w); [apply vars_5bq | reflexivity | apply swf_C5q | apply sd_5bq | exact Hag | | exact HSP].
  intros HagS _. cbn [D5bqc fst snd]. split; [| exact (ZF_holds _ F5 HagS F5v F5s (ZF5 Hrc))].
  unfold diffs_ok.
  repeat (apply Forall_cons; [cbn [fst snd]|]); [ .. | apply Forall_nil].
  all: first [scratch_pair Hag HagS | sem_pair HagS].
  transitivity (sc0 : Z); [exact E5 | symmetry; rewrite <- J; exact Zv164].
Qed.

Lemma link_5o : ltac2:(tb__ "0|1|
S0S9SbaVs;Vn;A2SaA3S30Sf9ScdVrhoW;R2A2Sd6S67VK;S16bSb6Vam;A1M0A1R3R2A5SfcS164G0A1R3A2F_;F_;Fw;Frho';F_;").
Proof using HC HMI HW Hb16 Hb3 Hhdr Hsp.
  intros Hrc rho' w Hag HSP. pose proof R_all as R. pose proof (RC_vals Hrc) as (J & _ & _ & _ & E). pose proof Hj164 as RJ.
  eapply (linkp (L5qs kd) (C5o kd) [] _ _ rho' w); [apply vars_L5qs | reflexivity | apply swf_C5o | apply sd_5o | exact Hag | | exact HSP].
  intros HagS _. cbn [D5oc fst snd]. split; [|constructor].
  unfold diffs_ok. apply Forall_cons; [cbn [fst snd]|apply Forall_nil]. sem_pair HagS.
  zev. rewrite Z.mod_small by lia. lia.
Qed.

Lemma link_6o : ltac2:(tb__ "0|1|
S30Sf9ScdVrhoW;R2A2Sd6S67VK;S16cSb6Vam;A1M0A1R3R2A5SfcS157G0A1R3A2F_;F_;Fw;Frho';").
Proof using HC HMI HW Hb16 Hb3 Hhdr.
  intros rho' w Hag HSP. pose proof R_all as R.
  eapply (linkp (L6os kd) (C6 kd) [] _ _ rho' w); [apply vars_L6os | reflexivity | apply swf_C6 | apply sd_6o | exact Hag | | exact HSP].
  intros HagS _. cbn [D6oc fst snd]. split; [|constructor].
  unfold diffs_ok. apply Forall_cons; [cbn [fst snd]|apply Forall_nil]. sem_pair HagS.
  transitivity (idx : Z); [exact ze_T6 | symmetry; exact Zv157].
Qed.

Local Ltac lnx_tac := split; reflexivity.

Lemma lnx_Ck : ltac2:(tb__ "0|1|
S9cS1S0S9S37S165R1A1M0A1S14A3S0S7S3aG0A1S9dA3A2Fkd0;"). Proof using . intros [| |]; lnx_tac. Qed.
Lemma lnx_C1 : ltac2:(tb__ "0|1|
S9cS1S0S9S37S160R1A1M0A1S14A3S0S7S3aG0A1S9dA3A2Fkd0;"). Proof using . intros [| |]; lnx_tac. Qed.
Lemma lnx_C2 : ltac2:(tb__ "0|1|
S9cS1S0S9S37S161R1A1M0A1S14A3S0S7S3aG0A1S9dA3A2Fkd0;"). Proof using . intros [| |]; lnx_tac. Qed.
Lemma lnx_C3 : ltac2:(tb__ "0|1|
S9cS1S0S9S37S162R1A1M0A1S14A3S0S7S3aG0A1S9dA3A2Fkd0;"). Proof using . intros [| |]; lnx_tac. Qed.
Lemma lnx_C4 : ltac2:(tb__ "0|1|
S9cS1S0S9S37S163R1A1M0A1S14A3S0S7S3aG0A1S9dA3A2Fkd0;"). Proof using . intros [| |]; lnx_tac. Qed.
Lemma lnx_C5 : ltac2:(tb__ "0|1|
S9cS1S0S9S37S150R1A1M0A1S14A3S0S7S3aG0A1S9dA3A2Fkd0;"). Proof using . intros [| |]; lnx_tac. Qed.
Lemma lnx_C6 : ltac2:(tb__ "0|1|
S9cS1S0S9S37S157R1A1M0A1S14A3S0S7S3aG0A1S9dA3A2Fkd0;"). Proof using . intros [| |]; lnx_tac. Qed.
Lemma lnx_C5q : ltac2:(tb__ "0|1|
S9cS1S0S9S37S151R1A1M0A1S14A3S0S7S3aG0A1S9dA3A2Fkd0;"). Proof using . intros [| |]; lnx_tac. Qed.
Lemma lnx_C5o : ltac2:(tb__ "0|1|
S9cS1S0S9S37S164R1A1M0A1S14A3S0S7S3aG0A1S9dA3A2Fkd0;"). Proof using . intros [| |]; lnx_tac. Qed.
Lemma lnx_C7 : ltac2:(tb__ "0|1|
S9cSa4Sa5S1S0S9S37S16fR3R2R1A3M0A1S14A3S0S7S3aG0A1S9dA3A2Fr;Fo;Fkd0;"). Proof using . intros [| |] o r; lnx_tac. Qed.
Lemma lnx_C8 : ltac2:(tb__ "0|1|
S9cSa4Sa5S1S0S9S37S170R3R2R1A3M0A1S14A3S0S7S3aG0A1S9dA3A2Fr;Fo;Fkd0;"). Proof using . intros [| |] [|] [| | |]; lnx_tac. Qed.

Theorem pro_C5 : ltac2:(tb__ "0|1|
S0S6SbbVam;A1Sb9Vn;A1A3SfaS67Vok;Sd6S67VK;S9fS9eSb6Vam;A1M0A2VrhoW;A4SfcS150G0A1A1A4F_;").
Proof using HC HK HMI HP12 HW Hb16 Hb3 Hdepth Hhdr Hsp.
  intros Hrt. eapply triple_seq.
  - apply (seg_run 400 (C0 MR_P kd) (L0 kd) (fun w => POST (C5 kd) w \/ (10 <= kq /\ POST (Ck kd) w)) rhoW);
      [reflexivity | reflexivity | apply run0 | apply agrees_refl |].
    intros Lf rho'' w Hin Hag HSP. destruct (L0_cases kd Lf Hin) as [E|E]; rewrite E in HSP.
    + left. exact (link_05 Hrt rho'' w Hag HSP).
    + right. exact (link_0k rho'' w Hag HSP).
  - apply triple_disj; [apply triple_refl|]. apply triple_pure. intros Hk.

    apply from_POST. intros r0 Hag0.
    eapply triple_seq; [apply (seg_run 100 (Ck kd) (L1 kd) (POST (C1 kd)) r0); [apply (proj1 (lnx_Ck kd)) | apply (proj2 (lnx_Ck kd)) | apply run1 | exact Hag0 |];
      intros Lf rho'' w Hin Hag HSP; rewrite L1_eq in Hin; destruct Hin as [<-|[]]; exact (link_11 rho'' w Hk Hag HSP) |].
    apply from_POST. intros r1 Hag1.
    eapply triple_seq; [apply (seg_run 100 (C1 kd) (L2 kd) (POST (C2 kd)) r1); [apply (proj1 (lnx_C1 kd)) | apply (proj2 (lnx_C1 kd)) | apply run2 | exact Hag1 |];
      intros Lf rho'' w Hin Hag HSP; rewrite L2_eq in Hin; destruct Hin as [<-|[]]; exact (link_22 rho'' w Hk Hag HSP) |].
    apply from_POST. intros r2 Hag2.
    eapply triple_seq; [apply (seg_run 100 (C2 kd) (L3 kd) (POST (C3 kd)) r2); [apply (proj1 (lnx_C2 kd)) | apply (proj2 (lnx_C2 kd)) | apply run3 | exact Hag2 |];
      intros Lf rho'' w Hin Hag HSP; rewrite L3_eq in Hin; destruct Hin as [<-|[]]; exact (link_33 rho'' w Hk Hag HSP) |].
    apply from_POST. intros r3 Hag3.
    eapply triple_seq; [apply (seg_run 100 (C3 kd) (L4 kd) (POST (C4 kd)) r3); [apply (proj1 (lnx_C3 kd)) | apply (proj2 (lnx_C3 kd)) | apply run4 | exact Hag3 |];
      intros Lf rho'' w Hin Hag HSP; rewrite L4_eq in Hin; destruct Hin as [<-|[]]; exact (link_44 rho'' w Hk Hag HSP) |].
    apply from_POST. intros r4 Hag4.
    apply (seg_run 100 (C4 kd) (L5 kd) (POST (C5 kd)) r4); [apply (proj1 (lnx_C4 kd)) | apply (proj2 (lnx_C4 kd)) | apply run5 | exact Hag4 |].
    intros Lf rho'' w Hin Hag HSP. rewrite L5_eq in Hin. destruct Hin as [<-|[<-|[]]].
    + exact (link_5a Hrt rho'' w Hk Hag HSP).
    + exact (link_5b Hrt rho'' w Hk Hag HSP).
Qed.

Theorem pro_C5q : ltac2:(tb__ "0|1|
S0S9SbaVs;Vn;A2SaA3SfaS67Vok;Sd6S67VK;S9fS9eSb6Vam;A1M0A2VrhoW;A4SfcS151G0A1A1A4F_;").
Proof using HC HK HMI HP12 HW Hb16 Hb3 Hdepth Hhdr Hsp.
  intros Hrc. eapply triple_seq.
  - apply (seg_run 400 (C0 MR_P kd) (L0 kd) (fun w => POST (C5q kd) w \/ (10 <= kq /\ POST (Ck kd) w)) rhoW);
      [reflexivity | reflexivity | apply run0 | apply agrees_refl |].
    intros Lf rho'' w Hin Hag HSP. destruct (L0_cases kd Lf Hin) as [E|E]; rewrite E in HSP.
    + left. exact (link_05q Hrc rho'' w Hag HSP).
    + right. exact (link_0k rho'' w Hag HSP).
  - apply triple_disj; [apply triple_refl|]. apply triple_pure. intros Hk.

    apply from_POST. intros r0 Hag0.
    eapply triple_seq; [apply (seg_run 100 (Ck kd) (L1 kd) (POST (C1 kd)) r0); [apply (proj1 (lnx_Ck kd)) | apply (proj2 (lnx_Ck kd)) | apply run1 | exact Hag0 |];
      intros Lf rho'' w Hin Hag HSP; rewrite L1_eq in Hin; destruct Hin as [<-|[]]; exact (link_11 rho'' w Hk Hag HSP) |].
    apply from_POST. intros r1 Hag1.
    eapply triple_seq; [apply (seg_run 100 (C1 kd) (L2 kd) (POST (C2 kd)) r1); [apply (proj1 (lnx_C1 kd)) | apply (proj2 (lnx_C1 kd)) | apply run2 | exact Hag1 |];
      intros Lf rho'' w Hin Hag HSP; rewrite L2_eq in Hin; destruct Hin as [<-|[]]; exact (link_22 rho'' w Hk Hag HSP) |].
    apply from_POST. intros r2 Hag2.
    eapply triple_seq; [apply (seg_run 100 (C2 kd) (L3 kd) (POST (C3 kd)) r2); [apply (proj1 (lnx_C2 kd)) | apply (proj2 (lnx_C2 kd)) | apply run3 | exact Hag2 |];
      intros Lf rho'' w Hin Hag HSP; rewrite L3_eq in Hin; destruct Hin as [<-|[]]; exact (link_33 rho'' w Hk Hag HSP) |].
    apply from_POST. intros r3 Hag3.
    eapply triple_seq; [apply (seg_run 100 (C3 kd) (L4 kd) (POST (C4 kd)) r3); [apply (proj1 (lnx_C3 kd)) | apply (proj2 (lnx_C3 kd)) | apply run4 | exact Hag3 |];
      intros Lf rho'' w Hin Hag HSP; rewrite L4_eq in Hin; destruct Hin as [<-|[]]; exact (link_44 rho'' w Hk Hag HSP) |].
    apply from_POST. intros r4 Hag4.
    apply (seg_run 100 (C4 kd) (L5 kd) (POST (C5q kd)) r4); [apply (proj1 (lnx_C4 kd)) | apply (proj2 (lnx_C4 kd)) | apply run5 | exact Hag4 |].
    intros Lf rho'' w Hin Hag HSP. rewrite L5_eq in Hin. destruct Hin as [<-|[<-|[]]].
    + exact (link_5aq Hrc rho'' w Hk Hag HSP).
    + exact (link_5bq Hrc rho'' w Hk Hag HSP).
Qed.

Theorem pro_C6 : ltac2:(tb__ "0|1|
SfaS67Vok;Sd6S67VK;S9fS9eSb6Vam;A1M0A2VrhoW;A4SfcS157G0A1A1A4").
Proof using HC HK HMI HP12 HW Hb16 Hb3 Hdepth Hhdr Hsp.
  destruct route_cases as [[_ Hrt]|[Hrc _]].
  -
    eapply triple_seq; [apply (pro_C5 Hrt)|].
    apply from_POST. intros r5 Hag5.
    apply (seg_run 400 (C5 kd) (L6 kd) (POST (C6 kd)) r5); [apply (proj1 (lnx_C5 kd)) | apply (proj2 (lnx_C5 kd)) | apply run6 | exact Hag5 |].
    intros Lf rho'' w Hin Hag HSP. rewrite L6_eq in Hin. destruct Hin as [<-|[]]. exact (link_66 rho'' w Hag HSP).
  -
    eapply triple_seq; [apply (pro_C5q Hrc)|].
    apply from_POST. intros r5 Hag5.
    eapply triple_seq.
    { apply (seg_run 100 (C5q kd) (L5q kd) (POST (C5o kd)) r5); [apply (proj1 (lnx_C5q kd)) | apply (proj2 (lnx_C5q kd)) | apply run5q | exact Hag5 |].
      intros Lf rho'' w Hin Hag HSP. rewrite L5q_eq in Hin. destruct Hin as [<-|[]]. exact (link_5o Hrc rho'' w Hag HSP). }
    apply from_POST. intros r6 Hag6.
    apply (seg_run 400 (C5o kd) (L6o kd) (POST (C6 kd)) r6); [apply (proj1 (lnx_C5o kd)) | apply (proj2 (lnx_C5o kd)) | apply run6o | exact Hag6 |].
    intros Lf rho'' w Hin Hag HSP. rewrite L6o_eq in Hin. destruct Hin as [<-|[]]. exact (link_6o rho'' w Hag HSP).
Qed.

End InstC.
End Mal_malloc_fastC.
