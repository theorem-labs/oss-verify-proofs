(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "not"; "or"; "ex"; "True"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "sub"; "modulo"; "mul"; "pow"; "land"; "max"; "of_nat"; "div"; "shiftr"; "divide"; "eqb"; "opp"; "to_nat"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rw"; "valuation"; "sv"; "sobj"; "rm"; "sprop"; "SLit"; "ss_facts"; "holds"; "eval"; "SVar"; "rl"; "ss_next"; "obj_range"; "ranges_disjoint"; "SAlu"; "ss_objs"; "cell"; "sprop_eqb"; "SPUle"; "mkObj"; "DList"; "DImage"; "SPEq"; "outside_all"; "sstate"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Start7.Seg7"; "mE"; "r6of"; "rho0C"; "out18"; "Q18"; "vals"; "B18pre"; "TP18"; "XBz"; "band"; "PostC18"; "out18_ok"; "XEz"; "lowb"; "G18"; "Wz"; "out18_W"; "Q18post"; "TOPz"; "BE"; "SXB"; "SZ18"; "bandw"; "Wok"; "ZX18"; "nE"; "B18"; "Post18"; "SXE"; "grp_out"; "objs_belowS_except_b"; "out18_model"; "M18"; "obj_belowS_b"; "out18_tp"; "rho18g"; "@Corelib.Init.Datatypes"; "list"; "prod"; "pair"; "bool"; "true"; "nat"; "nil"; "snd"; "option"; "cons"; "fst"; "app"; "Some"; "length"; "orb"; "false"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts"; "segsA"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "m_vmmaps"; "vm_maps"; "event"; "vm_brk"; "m_vm_lazy"; "vm_reserved"; "vm_start_brk"; "alloc_top"; "page_in_ranges"; "vm_noaccess"; "lazy_interior"; "vm_init_sp"; "maps_subtract"; "region_free"; "vm_limit"; "iv_subtract"; "VmMaps"; "page_mem"; "vm_add_lazy"; "vm_forget_range"; "with_vmmaps"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "mkAX"; "ax_X"; "ax_base"; "axst"; "entailsA"; "word_byte"; "xr_below"; "@Stdlib.Lists.List"; "In"; "existsb"; "nth_error"; "combine"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Start7States"; "R18"; "s18"; "C18"; "C18e"; "K18"; "I18a"; "I18b"; "I18c"; "E18g"; "SP18"; "es18"; "C18c"; "E18b"; "EV18"; "I18af"; "I18bf"; "I18cf"; "J18"; "L18b"; "L18c"; "T18c1"; "XB18"; "XL18"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.KxA"; "KxA"; "@Corelib.Lists.ListDef"; "Forall"; "seq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.MuslMallocIface"; "Pre_M"; "X_M"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Start6"; "x1"; "q12x"; "TP17"; "n17"; "m16"; "enspage"; "m17"; "G17"; "HPz"; "LIMz"; "PBz"; "PEz"; "RM6"; "TP16"; "e12x"; "tcls"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.MuslMalloc40Post"; "out1"; "out1_model"; "P_null0"; "P_null1"; "P_ok"; "out1_ok"; "out0"; "JL_null0"; "JL_null1"; "JL_ok"; "NA"; "NG"; "O_area"; "rm_kept_outside"; "O_grp"; "out1_W"; "out1_tp"; "m40_hyps"; "out0_W"; "out0_model"; "out0_ok"; "out1_base"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec"; "mmap_place_ok_none"; "munmap_model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "vms"; "lazy_in_maps";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "etriple"; "triple"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fs.Start6bStates"; "E18"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Start7"; "brk_same"; "kHighMemBeg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.StartALib"; "SHB"; "ARGF"; "objs_clear_e"; "RMH"; "eblk_clear_b"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.BackingAlgebra"; "ivs_wf"; "iv_wf"; "covered"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "in_ranges"; "wsub_get"; "rho_sub"; "rho_absorb"; "wsub"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Placement"; "SHADOW_BAND_LO"; "SHADOW_BAND_HI"; "band_covered"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "call_linkP"; "new_objs"; "import_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "J_ofPA"; "post_vars"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3"; "import_okPA3"; "import_postA3"; "@Stdlib.PArith.BinPos.Pos"; "lt"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_SLL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.MuslMalloc40Nodes"; "pgw"; "brk0"; "brk0w"; "mgrant"; "n8w"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e3.StartArgF"; "arg_layout"; "ARG_LIM"; "obj_below_b"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fl.Start5"; "m15"; "m12"; "m13"; "stackshadow_zero"; "vals12"; "@Stdlib.Arith.PeanoNat.Nat"; "eqb"; "@Corelib.Init.Peano"; "lt"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "segments_reserved"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.Start4"; "m8"; "m10"; "m11"; "m7"; "m9"; "n7"; "n9"; "priZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fl.Start6States"; "LOWPG"; "LEN16"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartDefsA"; "pages_rev"; "pageZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "rho_set_rw"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@Corelib.Init.Nat"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e8.StartGlueA"; "bump_next"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e5.StartGlueB"; "byte_cells"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e7.StartNodes"; "eager_model"; "null_none_model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MmapFixedA"; "tp_forget"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import Logic.FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uapi.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymCall SymSummary Glue3 SymHeap SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt LedgerA StepA SoundA EntailA CompleteA GlueA GlueA2 SysCallA
  MmapA MmapFixedA MmapFixedA2 MmapBrkA MmapNodesA SummaryA SummaryA2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import SummaryA3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv InitState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e3.StartArgF.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts Init Code StartLib KxA Placement PlacementA SysSpecStart.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require SysStartA SysStartA2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require StartDefsA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Start4States.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fl.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Start6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Start7States.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Init OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartLib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.KxA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Placement OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.PlacementA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.SysSpecStart OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.StartALib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.SysStartA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.SysStartA2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e7.StartNodes OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.StartNodes2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartDefsA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e8.StartGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e5.StartGlueB OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e6.StartGlueC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Start4States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.Start4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Start5States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fn.Start5CallStates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ec.Start5bStates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fl.Start5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fl.Start6States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fq.Start6JStates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fs.Start6Aux OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Start6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.MuslMallocIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e3.MuslMalloc40States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.MuslMalloc40Nodes OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.MuslMalloc40Post OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e6.MuslMalloc40 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fs.Start6bStates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Start7States.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition brk_same (a b : Model) : Prop := ltac2:(tb__ "0|3|
S1S0S18Q40A1M0S6eS6bVa;A1M1A1S6eS6bVb;A1M2A1A3S0G0S71G1A1S71G2A1A3A2").
Lemma brk_same_trans : ltac2:(tb__ "0|1|
S6aS6aS6aSddR3R2A2M0G0SddR5R3A2F_;F_;Fc;Fb;Fa;").
Proof. intros a b c [A1 A2] [B1 B2]. split; congruence. Qed.
Lemma brk_same_with : ltac2:(tb__ "0|1|
S7bS6aS0S18Q40A1M0S6eR2A1S6eS6bR1A1A1A3S0G0S71R3A1S71S6bR2A1A1A3SddS7fR4R3A2R3A2F_;F_;Fmd;Fh;").
Proof. intros h md E1 E2. unfold brk_same. rewrite m_vmmaps_with_vmmaps. auto. Qed.
Lemma brk_same_forget : ltac2:(tb__ "0|0|
S6S6S6aSddS7eR3R2R1A3R1A2Fmd;Fhi;Flo;").
Proof. intros. unfold brk_same. rewrite m_vmmaps_vm_forget_range. auto. Qed.
Lemma brk_same_add_lazy : ltac2:(tb__ "0|1|
S18Q40A1M0G0S6aSddS7dR3R2R1A3R1A2Fmd;Fn;Fa;").
Proof. intros. unfold brk_same. rewrite m_vmmaps_vm_add_lazy. auto. Qed.
Lemma brk_same_eager : ltac2:(tb__ "0|0|
S6S6aS18Q40A1SddS11eR3R2R1A3R2A2Fa;Fmd;FL;").
Proof. intros. unfold eager_model, eager_h. apply brk_same_with; reflexivity. Qed.
Lemma brk_same_null_none : ltac2:(tb__ "0|0|
S6S6aS18Q40A1SddS11fR3R2R1A3R2A2Fa;Fmd;FL;").
Proof. intros. unfold null_none_model. eapply brk_same_trans; [apply brk_same_add_lazy|]. unfold null_none_h. apply brk_same_with; reflexivity. Qed.
Lemma brk_same_munmap : ltac2:(tb__ "0|1|
S6aS18Q40A1M0G0SddSd4R3R2R1A3R3A2Fn;Fa;Fmd;").
Proof. intros. unfold munmap_model, with_mmap_destroyed. eapply brk_same_trans; [apply brk_same_forget|]. unfold munmap_vm. apply brk_same_with; reflexivity. Qed.
Lemma brk_same_m16 : ltac2:(tb__ "0|1|
S6aS18Q40A1M0G0G0G0G0G0G0S6SddSb0R9R8R7R6R5R4R3R2R1A9S103R9R8R7R6R5R4R3R2A8A2Fx;Fb9;Fb8;Fb7;Fb6;Fb5;Fb4;FP;Fm;").
Proof. intros. unfold m16, Start6.mF, brk_same. auto. Qed.
Lemma brk17 : ltac2:(tb__ "0|1|
S6aS18Q40A1M0G0G0G0G0G0G0S6G0SddSb2RaR9R8R7R6R5R4R3R2R1AaRaA2Fb10;Fx;Fb9;Fb8;Fb7;Fb6;Fb5;Fb4;FP;Fm;").
Proof.
  intros. unfold m17. eapply brk_same_trans; [apply brk_same_eager|].
  eapply brk_same_trans; [apply brk_same_m16|].
  unfold m15. eapply brk_same_trans; [apply brk_same_munmap|].
  unfold m14. eapply brk_same_trans; [apply brk_same_eager|].
  unfold m13. eapply brk_same_trans; [apply brk_same_eager|].
  unfold m12. eapply brk_same_trans; [apply brk_same_eager|].
  unfold m11. eapply brk_same_trans; [apply brk_same_eager|].
  unfold m10. eapply brk_same_trans; [apply brk_same_eager|].
  unfold m9. eapply brk_same_trans; [apply brk_same_null_none|].
  unfold m8. eapply brk_same_trans; [apply brk_same_forget|].
  eapply brk_same_trans; [apply brk_same_with; unfold h8, mmap_fixed_rw_next; reflexivity|].
  unfold brk_same. rewrite (mP_vmmaps m P). split; reflexivity.
Qed.

Lemma triple_pre_fact : ltac2:(tb__ "0|1|
Sd8OF_;SdbSdbOSd8R4R1A1R3F_;Fw;R2SdaS69R6R5R4A4M0F_;G0F_;F_;FF;FQ;FP;Fok;").
Proof. intros ok P Q F HF HT n Hg w Hw. exact (HT (HF w Hw) n Hg w Hw). Qed.

Lemma iv_subtract_pos : ltac2:(tb__ "0|4|
S18Q40M0A1M1G1S6S6S5aG1G1A2M2Se5S5bG1G1R5R4A4A1SaZ0M3S19G0R5A2A2S88G2R3S7aR7R6R5R4A4A3SaG3S19G0S60G1G1R4A3A2A2F_;F_;F_;Fr;Fhi;Flo;Fsz;Fa;").
Proof.
  intros a sz lo hi r Hwf Hsz Hin. unfold iv_wf, ivB, ivS in Hwf. cbn [fst snd] in Hwf. pose proof (urange a). pose proof (urange sz).
  unfold iv_subtract in Hin. apply in_app_iff in Hin as [Hin|Hin].
  - destruct (bv_unsigned a <? lo) eqn:E; [|destruct Hin]. apply Z.ltb_lt in E. destruct Hin as [<-|[]]. cbn [snd]. rewrite u64_of_lit by lia. lia.
  - destruct (hi <? bv_unsigned a + bv_unsigned sz) eqn:E; [|destruct Hin]. apply Z.ltb_lt in E. destruct Hin as [<-|[]]. cbn [snd]. rewrite u64_of_lit by lia. lia.
Qed.
Lemma maps_subtract_pos : ltac2:(tb__ "0|4|
S59S5aS18Q40M0A1M1G1A2M2A1S6S6Se4R3A1G2S88G2R1R5A3SaZ0S19G0S60G1G1R2A3A2A2M3F_;Fr;G2S88G2R1S77R6R5R4A3A3G3F_;Fr;F_;F_;Fhi;Flo;Fl;").
Proof.
  intros l lo hi. induction l as [|[a sz] l IH]; intros Hwf Hpos r Hin; [destruct Hin|].
  cbn [maps_subtract] in Hin. apply ivs_wf_cons_inv in Hwf as [H1 H2]. apply in_app_iff in Hin as [Hin|Hin].
  - eapply iv_subtract_pos; [exact H1 | exact (Hpos _ (or_introl eq_refl)) | exact Hin].
  - apply IH; [exact H2 | intros r' Hr'; apply Hpos; right; exact Hr' | exact Hin].
Qed.
Lemma lazy_interior_pos : ltac2:(tb__ "0|3|
S18Q40M0A1M1G1S5aG1G1A2M2Se5S5bG1G1R3R2A4A1S88G2R2S75R4R3A2A3S1SaZ0S19G0S60G1G1R3A3A2A2Se5R3A1A2F_;F_;Fr;Fn;Fa;").
Proof.
  intros a n r Hwf Hin. unfold iv_wf, ivB, ivS in Hwf. cbn [fst snd] in Hwf.
  unfold lazy_interior in Hin. pose proof (urange a). pose proof (urange n). unfold page_size in Hin.
  match type of Hin with context [if ?c then _ else _] => destruct c eqn:E end; [|destruct Hin]. apply Z.ltb_lt in E.
  destruct Hin as [<-|[]]. cbn [snd]. unfold iv_wf, ivB, ivS. cbn [fst snd].
  assert (B1 : 0 <= (bv_unsigned a + 4096 - 1) / 4096 * 4096) by (apply Z.mul_nonneg_nonneg; [apply Z.div_pos; lia | lia]).
  assert (B2 : 4096 * ((bv_unsigned a + bv_unsigned n) / 4096) <= bv_unsigned a + bv_unsigned n) by (apply Z.mul_div_le; lia).
  rewrite (u64_of_lit ((bv_unsigned a + bv_unsigned n) / 4096 * 4096 - (bv_unsigned a + 4096 - 1) / 4096 * 4096)) by lia.
  rewrite (u64_of_lit ((bv_unsigned a + 4096 - 1) / 4096 * 4096)) by lia. lia.
Qed.

Lemma tp_forget_id : ltac2:(tb__ "0|4|
S6S6S59S18Q40M0A1M1A1M2G1S88G1R1R2A3S2S1S8R5S19G0R2A2M3A2SaG3R4A2A2A1F_;Fp;S0G2S121R4R3R2A3R2A3F_;Ftp;Fhi;Flo;").
Proof.
  intros lo hi tp. induction tp as [|p tp IH]; intros H; [reflexivity|]. unfold tp_forget in IH |- *. cbn [List.filter].
  pose proof (H p (or_introl eq_refl)) as Hp. unfold page_outside_range at 1.
  replace ((lo <=? bv_unsigned p) && (bv_unsigned p <? hi)) with false.
  2:{ symmetry. apply andb_false_iff. destruct (Z.le_gt_cases lo (bv_unsigned p)); [right; apply Z.ltb_ge; lia | left; apply Z.leb_gt; lia]. }
  cbn [negb]. f_equal. apply IH. intros q Hq. apply H. right. exact Hq.
Qed.

Lemma pagedown_props : ltac2:(tb__ "0|2|
S6SbR1ScR1Z1000M0A2M1A2S6S1S0S6G1Z0A3S1S8R1R2A2SaR2S9R1G0A2A2A2A2Tp;Fs;").
Proof. intros s p. subst p. pose proof (Z.mod_pos_bound s 4096 ltac:(lia)). split; [|lia]. rewrite Zminus_mod, Z.mod_mod by lia. rewrite Z.sub_diag. reflexivity. Qed.
Lemma rd64_props : ltac2:(tb__ "0|2|
S6SbR1ScR1Z40M0A2M1A2S6S1S0S6G1Z0A3S1S8R1R2A2SaR2S9R1G0A2A2A2A2Tp;Fs;").
Proof. intros s p. subst p. pose proof (Z.mod_pos_bound s 64 ltac:(lia)). split; [|lia]. rewrite Zminus_mod, Z.mod_mod by lia. rewrite Z.sub_diag. reflexivity. Qed.

Lemma page_in_ranges_In : ltac2:(tb__ "0|5|
S18Q40M0A1M1S59S5aG1G1A2M2A1S0S5cS73R2R1A2S5dA3S4G1G1S4G1G1S1S88G2S5bG1G1R2R1A4R4A3S1S8S19G0R2A2M3S19G0R5A2M4A2S8S9G4Z1000A2S9G3S19G0R1A2A2A2A2A2Ls;A2Lb;A2F_;Fl;Fp;").
Proof.
  intros p l H. rewrite page_in_ranges_eq in H. apply existsb_exists in H as ([b s] & Hin & Hr). unfold page_in_range in Hr. cbn [fst snd] in Hr.
  apply andb_prop in Hr as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. unfold page_size in H2. exists b, s. auto.
Qed.
Lemma page_in_ranges_of_In' : ltac2:(tb__ "0|5|
S18Q40M0A1M1G1G1S59S5aG1G1A2M2A1S88G2S5bG1G1R3R2A4R1A3S8S19G0R4A2M3S19G0R5A2M4A2S8S9S19G0R6A2Z1000A2S9G4G3A2A2S0S5cS73R7R4A2S5dA3F_;F_;F_;Fl;Fs;Fb;Fp;").
Proof.
  intros p b s l Hin H1 H2. rewrite page_in_ranges_eq. apply existsb_exists. exists (b, s). split; [exact Hin|].
  unfold page_in_range. cbn [fst snd]. unfold page_size. apply andb_true_intro. split; apply Z.leb_le; lia.
Qed.
Lemma in_maps_subtract_of' : ltac2:(tb__ "0|2|
S59S5aS18Q40A1M0G0A2M1A1G0G0S6S6G1S88G1S5bG0G0R5R4A4R6A3S88G1R2S7aR6R5R4R3A4A3S88G1R3S77R8R5R4A3A3F_;F_;Fq;Fhi;Flo;Fsz;Fa;Fl;").
Proof.
  intros l. induction l as [|[a' sz'] l IH]; intros a sz lo hi q Hin Hq; [destruct Hin|].
  cbn [maps_subtract]. apply in_app_iff. destruct Hin as [[= <- <-]|Hin]; [left; exact Hq | right; exact (IH _ _ _ _ _ Hin Hq)].
Qed.

Lemma page_in_ranges_subtract_keep : ltac2:(tb__ "0|3|
S59S5aS18Q40M0A1M1G1A2A1S6S6G1Se4R4A1S8R4R3A2S0S5cS73R3R6A2S5dA3S3S8S9S19G0R4A2M2Z1000A2R6A2S8R5G2A2A2S0S5cS73R5S77R8R7R6A3A2S5dA3F_;F_;F_;F_;Fp;Fhi;Flo;Fl;").
Proof.
  intros l lo hi p Hwf Hlh Hp Hout. apply page_in_ranges_In in Hp as (b & s & Hin & H1 & H2).
  destruct (iv_subtract_keeps b s lo hi (bv_unsigned p) (bv_unsigned p + 4096) (Hwf _ Hin) Hlh H1 H2 ltac:(lia) Hout) as ([rb rs] & Hr & Q1 & Q2).
  cbn [fst snd] in Q1, Q2. apply (page_in_ranges_of_In' p rb rs); [|exact Q1|exact Q2]. eapply in_maps_subtract_of'; [exact Hin | exact Hr].
Qed.

Lemma U_add_slit' : ltac2:(tb__ "0|4|
S1cS1dS6S1S8S16SeZ2M0Z3fA2M1A1R1A2SaR1G1A2A2S1S8Z0S9S19Q40M2S24R4R3A2A2R2A2M3A2SaG3SeG0Z40A2A2A2S0S6S19G2S24R5S2aSf9R4S21R3A1A3A2A2S9S19G2S24R5R4A2A2R3A2A3F_;F_;Fc;Fe;Frho;").
Proof.
  intros rho e c Hc Hr. cbn [eval]. unfold alu64, alu. rewrite bv_add_unsigned, Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  pose proof (urange (eval rho e)) as U.
  destruct (Z.lt_ge_cases c 0).
  - replace (c mod 2 ^ 64) with (c + 2 ^ 64) by (rewrite <- (Z_mod_plus_full c 1 (2 ^ 64)); symmetry; apply Z.mod_small; lia).
    replace (bv_unsigned (eval rho e) + (c + 2 ^ 64)) with ((bv_unsigned (eval rho e) + c) + 1 * 2 ^ 64) by lia.
    rewrite Z_mod_plus_full. apply Z.mod_small. lia.
  - rewrite (Z.mod_small c) by lia. apply Z.mod_small. lia.
Qed.

Definition kHighMemBeg : Z := 0x10007fff8000.
Ltac klia := unfold kHighMemBeg in *; repeat match goal with H : context [Z.modulo _ _] |- _ => clear H end; lia.

Section Seg7.

Variables (m : Model) (a1 a2 : word) (B : Z).
Hypothesis Hres : ltac2:(tb__ "0|1|
S0S59S5aS18Q40A1M0G0A2A1S70S6bVm;A1A1S10cS69A1A3").
Hypothesis Hmaps : ltac2:(tb__ "0|3|
S0S59S5aS18Q40M0A1M1G1A2M2A1S6cS6bVm;A1A1S62G2S5bG1G1Va2;S1aG0Z38e000A2A4S62G2S5bG1G1Va1;S1aG0Z10000A2A4S62G2S5bG1G1S1aG0Z2008fff7000A2S1aG0Zdfff0001000A2A4S62G2S5bG1G1S1aG0Z8fff7000A2S1aG0Z20000000000A2A4S62G2S5bG1G1S1aG0Z7fff7000A2S1aG0Z10000000A2A4S5fG2A1A3A3A3A3A3A3").
Hypothesis Hna : ltac2:(tb__ "0|3|
S0S59S5aS18Q40M0A1M1G1A2M2A1S74S6bVm;A1A1S62G2S5bG1G1S1aG0Z8fff7000A2S1aG0Z20000000000A2A4S5fG2A1A3A3").
Hypothesis Hlz : ltac2:(tb__ "0|3|
S0S59S5aS18Q40M0A1M1G1A2M2A1S6fVm;A1S64G2S75S1aG0Z2008fff7000A2S1aG0Zdfff0001000A2A2S64G2S75S1aG0Z8fff7000A2S1aG0Z20000000000A2A2S75S1aG0Z7fff7000A2S1aG0Z10000000A2A2A3A3A3").
Hypothesis Htop : init_sp_ok (m_vmmaps m).
Hypothesis Ha1 : ltac2:(tb__ "0|2|
S1S8Z646000S19Q40Va1;A2M0A2S1S3S8S9G0Z10000A2M1SedA2S8SeeG0A2A2S8G1S72S6bVm;A1A1A2A2A2").
Hypothesis Ha2 : ltac2:(tb__ "0|2|
S1S8Z646000S19Q40Va2;A2M0A2S1S3S8S9G0Z38e000A2M1SedA2S8SeeG0A2A2S8G1S72S6bVm;A1A1A2A2A2").
Hypothesis HBlim : ltac2:(tb__ "0|0|
S8S9VB;Z1000000A2S79S6bVm;A1A1A2").
Hypothesis Hsb : ltac2:(tb__ "0|1|
S0S18Q40A1S71S6bVm;A1M0A1S6eG0A1A3").
Hypothesis Hbrk : ltac2:(tb__ "0|1|
S1S8Z646000S19Q40S6eS6bVm;A1A1A2M0A2S8G0Z80646000A2A2").
Hypothesis Hbal : ltac2:(tb__ "0|0|
S14Z1000S19Q40S6eS6bVm;A1A1A2A2").
Variable ok : assn.
Hypothesis OKF : ltac2:(tb__ "0|1|
Sa5S1cS59S18Q40A1A1S59S6dA1M0S6aR5R4R3R2R1A4S0G0R3S5fS6dA1A3F_;Fmd;Ftr;Ftp;Frho;Sa6S69Vok;R2A3F_;FJ;").
Hypothesis OKP : ltac2:(tb__ "0|1|
Sa5S1cS59S18Q40A1A1S59S6dA1M0S6aR5R4R3R2R1A4S0G0R3S5fS6dA1A3F_;Fmd;Ftr;Ftp;Frho;S11aS69Vok;R2A3F_;FJ;").
Variables (P b4 b5 b6 : word).
Hypothesis HPL : ltac2:(tb__ "0|0|
Sd3S1aQ40Z0A2Vm;S112VP;A4").
Hypothesis HPL4 : ltac2:(tb__ "0|0|
Sd3S1aQ40Z0A2S10dVm;VP;A2S113Vb4;A4").
Hypothesis HPL5 : ltac2:(tb__ "0|1|
Sd3S1aQ40M0Z0A2S111Vm;VP;Vb4;A3S1aG0Z1000A2Vb5;A4").
Hypothesis HPL6 : ltac2:(tb__ "0|1|
Sd3S1aQ40M0Z0A2S10eVm;VP;Vb4;Vb5;A4S1aG0Z10000A2Vb6;A4").
Variables (b7 b8 b9 : word).
Hypothesis HPL7 : ltac2:(tb__ "0|1|
Sd3S1aQ40M0Z0A2S10fVm;VP;Vb4;Vb5;Vb6;A5S1aG0Z1000A2Vb7;A4").
Hypothesis HPL8 : ltac2:(tb__ "0|1|
Sd3S1aQ40M0Z0A2S104Vm;VP;Vb4;Vb5;Vb6;Vb7;A6S1aG0Z1000A2Vb8;A4").
Hypothesis HPL9 : ltac2:(tb__ "0|1|
Sd3S1aQ40M0Z0A2S105Vm;VP;Vb4;Vb5;Vb6;Vb7;Vb8;A7S1aG0Z1000A2Vb9;A4").
Variables (x : Z) (b10 : word).
Hypothesis Hx : 0x7fff80000000 <= x <= 2 ^ 47.
Hypothesis H16 : x mod 16 = 0.
Hypothesis Hxtop : ltac2:(tb__ "0|0|
S0S6S72S6bVm;A1A1SbVx;Z800000A2A3").
Hypothesis HPL10 : ltac2:(tb__ "0|1|
Sd3S1aQ40M0Z0A2Sb0Vm;VP;Vb4;Vb5;Vb6;Vb7;Vb8;Vb9;Vx;A9S1aG0SafA2Vb10;A4").

Definition mE : Model := ltac2:(tb__ "0|0|
Sb2Vm;VP;Vb4;Vb5;Vb6;Vb7;Vb8;Vb9;Vx;Vb10;Aa").
Definition BE : Z := B17 B.
Definition vals : valuation -> Prop := ltac2:(tb__ "0|0|
S107Vm;Va1;Va2;VP;Vb4;Vb5;Vb6;A7").
Definition brk0 : Z := bv_unsigned (vm_brk (m_vmmaps m)).
Definition TOPz : Z := x - 8388608.
Local Notation P_facts := (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.Start4.P_facts m a1 a2 Hres Hmaps Htop P HPL) (only parsing).
Local Notation RI_range := (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.Start4.RI_range m a1 a2 Hres Hmaps Htop P HPL) (only parsing).
Local Notation RI_val := (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.Start4.RI_val m a1 a2 Hres Hmaps Htop P HPL) (only parsing).
Local Notation SB_val := (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.Start4.SB_val m a1 a2 Hres Hmaps Htop P HPL) (only parsing).
Local Notation b4_facts := (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.Start4.b4_facts m a1 a2 Hres Hmaps Htop P HPL b4 HPL4) (only parsing).
Local Notation b5_facts := (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.Start4.b5_facts m a1 a2 Hres Hmaps Htop P HPL b4 HPL4 b5 HPL5) (only parsing).
Local Notation b6_facts := (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.Start4.b6_facts m a1 a2 Hres Hmaps Htop P HPL b4 HPL4 b5 HPL5 b6 HPL6) (only parsing).
Local Notation b7_facts := (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fl.Start5.b7_facts m a1 a2 Hres Hmaps Htop P b4 b5 b6 HPL HPL4 HPL5 HPL6 b7 HPL7) (only parsing).
Local Notation b8_facts := (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fl.Start5.b8_facts m a1 a2 Hres Hmaps Htop P b4 b5 b6 HPL HPL4 HPL5 HPL6 b7 HPL7 b8 HPL8) (only parsing).
Local Notation b9_facts := (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fl.Start5.b9_facts m a1 a2 Hres Hmaps Htop P b4 b5 b6 HPL HPL4 HPL5 HPL6 b7 HPL7 b8 HPL8 b9 HPL9) (only parsing).
Local Notation plfacts := (Start6.plfacts m a1 a2 Hres Hmaps Htop P b4 b5 b6 HPL HPL4 HPL5 HPL6 b7 b8 b9 HPL7 HPL8 HPL9) (only parsing).
Local Notation priZ_facts := (Start6.priZ_facts m a1 a2 Hres Hmaps Htop P b4 b5 b6 HPL) (only parsing).
Local Notation sbZ_facts' := (Start6.sbZ_facts' m a1 a2 Hres Hmaps Htop P b4 b5 b6 HPL HPL4 HPL5 HPL6) (only parsing).
Local Notation Upri := (Start6.Upri m a1 a2 P b4 b5 b6) (only parsing).
Local Notation mF_vmmaps := (Start6.mF_vmmaps m P b4 b5 b6 b7 b8 b9) (only parsing).
Local Notation m16_fields := (Start6.m16_fields m P b4 b5 b6 b7 b8 b9) (only parsing).
Local Notation maps16_keep := (Start6.maps16_keep m a1 a2 Hres Hmaps Htop P b4 b5 b6 HPL HPL4 HPL5 HPL6 b7 b8 b9 HPL7 HPL8 HPL9) (only parsing).
Local Notation band_m16 := (Start6.band_m16 m a1 a2 Hres Hmaps Htop P b4 b5 b6 HPL HPL4 HPL5 HPL6 b7 b8 b9 HPL7 HPL8 HPL9) (only parsing).
Local Notation init_sp_ok_m16 := (Start6.init_sp_ok_m16 m Htop P b4 b5 b6 b7 b8 b9) (only parsing).
Local Notation high_shadow_lazy_mF := (Start6.high_shadow_lazy_mF m a1 a2 Hres Hmaps Hlz Htop P b4 b5 b6 HPL HPL4 HPL5 HPL6 b7 b8 b9 HPL7 HPL8 HPL9) (only parsing).
Local Notation high_shadow_acc_mF := (Start6.high_shadow_acc_mF m a1 a2 Hres Hmaps Hna Hlz Htop P b4 b5 b6 HPL HPL4 HPL5 HPL6 b7 b8 b9 HPL7 HPL8 HPL9) (only parsing).
Local Notation blocks16 := (Start6.blocks16 m a1 a2 Hres Hmaps Htop Ha1 Ha2 P b4 b5 b6 HPL HPL4 HPL5 HPL6 b7 b8 b9 HPL7 HPL8 HPL9) (only parsing).
Local Notation W9 := (Start6.W9 m a1 a2 Hres Hmaps Hna Htop P b4 HPL HPL4) (only parsing).
Local Notation RIw := (RI P) (only parsing).

Lemma OKFx : ltac2:(tb__ "0|0|
S6aS6Sa6S69Vok;Sa7R2R1A2A3FBB;Fmm;").
Proof using OKF. clear -OKF. intros. apply OKF. intros; eapply KxA_nil; eassumption. Qed.
Lemma OKPx : ltac2:(tb__ "0|0|
S6aS6S11aS69Vok;Sa7R2R1A2A3FBB;Fmm;").
Proof using OKP. clear -OKP. intros. apply OKP. intros; eapply KxA_nil; eassumption. Qed.

Lemma CAx : ltac2:(tb__ "0|9|
SbbVx;A1S6S1S1S8Z0M0R1A2S8R1Z7A2A2S1S8Z10006fef8000M1Sb4Vx;A1M2A2S1S8Sb7Vx;A1M3Z10007fff8000A2S1S0S6G3S9G2Z100000A2A3S1S8S9G2Z1000M4A2M5SadVx;A1A2S1S1S8SbaVx;A1M6G3A2S8G3S9G6G4A2A2A2S1S0S6ScG3G4A2G0A3S1S8Sb5Vx;A1M7S9G2SdZ200R1A2A2A2S1S8G1G7A2S1S0S6Sb6Vx;A1M8S5cS6L_;S15R1G0A2G2G5X5cx2A3S1S0S6S9G8S116R1A1A2G3A3S0S6ScG6G4A2G0A3A2A2A2A2A2A2A2A2A2A2A2Tt;").
Proof using Hx H16.
  clear -Hx H16. pose proof (class_arith x Hx H16) as CA. cbv zeta in CA.
  destruct CA as (Ct & C79al & C80x8 & C80al & C80nn & C79lo & C79hi & Ctop1 & Ctop2 & Ctopal & Ctoplo & Cand & CHPal & CPEal & CPBal & CPB & CLEN & CPEHP & CHPlo & CPEhi & CPEe & CHPq & Ce12al & CLIM & CLIM0).
  cbv zeta. repeat split; assumption || lia.
Qed.

Lemma mE_fields : ltac2:(tb__ "0|8|
S1S0S59S5aS18Q40M0A1M1G1A2M2A1M3S70S6bS35A1M4A1S70S6bVm;A1M5A1A3S1S0G3S6cG4A1S62G2S5bG1G1Vb10;S1aG0SafA2A4S6cS6bSb0Vm;VP;Vb4;Vb5;Vb6;Vb7;Vb8;Vb9;Vx;A9M6A1M7A1A3A3S1S0S6S79G4A1S79G5A1A3S1S0G1S76G4A1S76G5A1A3S1S0G3S6fS35A1S6fG6A1A3S1S0G3S74G4A1S74G7A1A3S1S0G1S6eG4A1S6eG5A1A3S0G1S71G4A1S71G5A1A3A2A2A2A2A2A2A2").
Proof.
  clear. pose proof (m16_fields x) as (MR & MM & ML & MB & LZ & NA).
  pose proof (brk17 m P b4 b5 b6 b7 b8 b9 x b10) as [K1 K2].
  unfold mE, m17, eager_model, eager_h. rewrite m_vmmaps_with_vmmaps, m_vm_lazy_with_vmmaps.
  cbn [vm_reserved vm_maps vm_limit vm_init_sp vm_noaccess vm_brk vm_start_brk]. rewrite MR, ML, MB.
  unfold mE, m17, eager_model, eager_h in K1, K2. rewrite m_vmmaps_with_vmmaps in K1, K2. cbn [vm_brk vm_start_brk] in K1, K2.
  repeat split; try reflexivity; assumption.
Qed.
Lemma top_mE : ltac2:(tb__ "0|0|
S0S6S72S6bS35A1A1S47A3").
Proof using Hxtop. clear -Hxtop. pose proof mE_fields as (_ & _ & _ & L4 & _). unfold alloc_top in *. rewrite L4. unfold TOPz. exact Hxtop. Qed.
Lemma init_sp_ok_mE : init_sp_ok (m_vmmaps mE).
Proof using Htop. clear -Htop. pose proof mE_fields as (_ & _ & _ & L4 & _). unfold init_sp_ok in *. rewrite L4. exact Htop. Qed.

Lemma b10_facts : ltac2:(tb__ "0|5|
S1S8Z646000S19Q40M0Vb10;A2M1A2S1S3S8S9G1SafA2M2SedA2S8SeeG1A2A2S1S8G2S47A2S1S0S6ScG1Z1000A2Z0A3S0S5cS78S64S5aS18G0A1M3G3A2S70S6bSb0Vm;VP;Vb4;Vb5;Vb6;Vb7;Vb8;Vb9;Vx;A9A1M4A1S6cG4A1A3Vb10;S1aG0SafA2A3S5dA3A2A2A2A2").
Proof using HPL HPL10 HPL4 HPL5 HPL6 HPL7 HPL8 HPL9 Hmaps Hres Htop Hxtop.
  clear Ha1 Ha2 HBlim Hsb Hbrk Hbal. pose proof (m16_fields x) as (MR & MM & ML & MB & _).
  pose proof (place_LB_A (m16 m P b4 b5 b6 b7 b8 b9 x) n17 b10 (init_sp_ok_m16 x) ltac:(rewrite MR; exact Hres) (band_m16 x) ltac:(unfold n17; lia) ltac:(reflexivity) HPL10)
    as (PLB & Pimg & Pband & Ptop & _).
  pose proof HPL10 as (Hal & _ & _ & Hfree).
  assert (Ptop' : bv_unsigned b10 + n17 <= TOPz).
  { unfold TOPz. rewrite <- Hxtop. unfold alloc_top in Ptop |- *. rewrite <- MB. exact Ptop. }
  assert (Hn : mmap_n (Z_to_bv 64 n17) = Z_to_bv 64 n17) by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). rewrite Hn in Hfree.
  change (LB_of n17) with 0x646000 in PLB. repeat split; try assumption.
Qed.

Lemma band_mE : ltac2:(tb__ "0|2|
SefS64S5aS18Q40A1M0G0A2S70S6bS35A1M1A1S6cG1A1A3SedSeeA3").
Proof using HPL HPL4 HPL5 HPL6 HPL7 HPL8 HPL9 Hmaps Hres Htop.
  clear Ha1 Ha2 HBlim Hsb Hbrk Hbal HPL10 Hxtop. pose proof mE_fields as (MR & MM & _). pose proof (m16_fields x) as (MR6 & _).
  rewrite MR, MM, <- MR6. apply band_covered_app_cons. exact (band_m16 x).
Qed.

Definition XBz : Z := ltac2:(tb__ "0|1|
SbSbVx;Z2f0A2M0ScG0Z40A2A2").
Definition XEz (r6 : Z) : Z := ltac2:(tb__ "0|1|
SbS9Vr6;Z4fA2M0ScG0Z40A2A2").
Definition SXB : Z := SHB + XBz / 8.
Definition SXE (r6 : Z) : Z := ltac2:(tb__ "0|0|
S9SdfS12S41Vr6;A1Z8A2A2").
Definition Q18 : Z := PEz x.
Definition Wz (r6 : Z) : Z := ltac2:(tb__ "0|0|
S9S51Vr6;A1ZfffA2S6SbR1ScR1Z1000A2A2Ts;").
Definition nE (r6 : Z) : nat := ltac2:(tb__ "0|0|
S17S12SbS44Vr6;A1S39A2Z1000A2A1").
Definition r6of (rho : valuation) : Z := bv_unsigned (rw rho 6%positive).

Definition TP18 (rho : valuation) : list word := ltac2:(tb__ "0|3|
S4eS36Vrho;A1A1S5eS5cS59S18Q40M0A1M1A1L_;S108R1U0A2SaeVrho;A1M2S64G1S117S9S39Z1000A2S11bR1U1A2A2Sb1S1aG0S39A2G2A2A3X5cx2Tn;").
Definition B18pre : Z := BE + 4096 * 72.
Definition B18 : Z := B18pre + 12288.

Definition SZ18 (rho : valuation) : Prop := ltac2:(tb__ "0|4|
S1S6S1S8SadVx;A1R1A2SaR1S39A2A2S0S61S18Q8M0A1M1A1S1fVrho;S1aQ40M2R2A2A2S65G1S1aG0Z0A2A2A3M3F_;Fz;S0S5cS7cS1aG2S39A2Sb9Vrho;A1A2S5dA3S6S1S8S39R1A2SaR1S9S39Z1000A2A2A2G3F_;Fz;F_;A2").
Definition ZX18 (r6 : Z) (rho : valuation) : Prop := ltac2:(tb__ "0|2|
S6S1S8SadVx;A1R1A2SaR1S10S39S44Vr6;A1A2A2A2S0S61S18Q8M0A1M1A1S1fVrho;S1aQ40R2A2A2S65G1S1aG0Z0A2A2A3F_;Fz;").

Lemma arith18 : ltac2:(tb__ "0|f|
S6S8S9Vx;Z50A2R1A2S8S9R2Z10M0A2SeZ2Z2fA2M1A2S8S9R3G0A2S9Vx;Z2228cfA2A2S1S0S6ScS3dZ40M2A2Z0M3A3S1S1S8SbVx;Z32fA2S3dA2S8S3dSbVx;Z2f0A2A2A2S1S0S6ScS41R4A1M4G2A2G3A3S1S1S8S9R4G0A2G4A2S8G4S9R4Z4fA2A2A2S1S8G4G1A2S1S0S6ScS49Z8M5A2G3A3S1S0S6ScS51R4A1M6G5A2G3A3S1S0S6SdG5SbS49SdfA2A2S3dA3S1S0S6SdG5SbG6SdfA2A2G4A3S1S8S9SadVx;A1M7Z1000M8A2S49A2S1SaS49G6A2S1S8G6S44R4A1M9A2S1S0S6ScG9G8A2G3A3S1S8G9SdeA2S1S8G6SdeA2S1S0S6ScS39G8A2G3A3S1S8S9Z10006fef8000G8A2MaS39A2S1S8S39SdeA2S1S8G7S39A2S1S8SbG9S39A2SdG8Z48MbA2A2S1S8S11S4eR4A1McA1GbA2S1S0S5eGcU0A3MdS8S44R5A1MeS39A2F_;S1S2GdA1S0S6GeS9S39SdG8S11S4eR5A1A1A2A2A3F_;S8GaG7A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2F_;F_;F_;Fr6;").
Proof.
  clear -x Hx H16. intros r6 H1 H2 H3. pose proof (class_arith x Hx H16) as CA. cbv zeta in CA.
  destruct CA as (Ct & C79al & C80x8 & C80al & C80nn & C79lo & C79hi & Ctop1 & Ctop2 & Ctopal & Ctoplo & Cand & CHPal & CPEal & CPBal & CPB & CLEN & CPEHP & CHPlo & CPEhi & Ce12 & CHPq & Ce12al & _).
  pose proof (rd64_props (x - 752)) as [AB RB]. pose proof (rd64_props (r6 + 79)) as [AE RE].
  change (x - 752 - (x - 752) mod 64) with XBz in AB, RB. change (r6 + 79 - (r6 + 79) mod 64) with (XEz r6) in AE, RE.
  pose proof (pagedown_props (SXE r6 + 4095)) as [AW RW]. change (SXE r6 + 4095 - (SXE r6 + 4095) mod 4096) with (Wz r6) in AW, RW.
  unfold q12x, e12x, shx in *. pose proof (pagedown_props (x / 8 + 2147450880 - 131072)) as [AQ RQ]. pose proof (pagedown_props (x / 8 + 2147450880 - 9)) as [AE12 RE12].
  set (q12 := x / 8 + 2147450880 - 131072 - (x / 8 + 2147450880 - 131072) mod 4096) in *.
  set (e12 := x / 8 + 2147450880 - 9 - (x / 8 + 2147450880 - 9) mod 4096) in *.
  apply Z.mod_divide in H16 as [k16 Hk16]; [|lia].
  apply Z.mod_divide in AB as [kb Hkb]; [|lia]. apply Z.mod_divide in AE as [ke Hke]; [|lia].
  assert (E47 : XEz r6 <= 2 ^ 47) by (assert (ke <= 2 ^ 41) by (apply (Z.mul_le_mono_pos_r _ _ 64); lia); lia).
  assert (DB : XBz / 8 = 8 * kb) by (rewrite Hkb; replace (kb * 64) with (8 * kb * 8) by lia; apply Z_div_mult; lia).
  assert (DE : XEz r6 / 8 = 8 * ke) by (rewrite Hke; replace (ke * 64) with (8 * ke * 8) by lia; apply Z_div_mult; lia).
  assert (Dx : x / 8 = 2 * k16) by (rewrite Hk16; replace (k16 * 16) with (2 * k16 * 8) by lia; apply Z_div_mult; lia).
  assert (ESB : SXB = 2147450880 + 8 * kb) by (unfold SXB, SHB; rewrite DB; reflexivity).
  assert (ESE : SXE r6 = 2147450880 + 8 * ke) by (unfold SXE, SHB; rewrite DE; reflexivity).
  rewrite ESB, ESE in *. rewrite Dx in *. unfold Q18, kHighMemBeg, SHB in *.
  apply Z.mod_divide in AW as [kw Hkw]; [|lia]. apply Z.mod_divide in CPEal as [kq Hkq]; [|lia].
  assert (En : forall d, 0 <= d -> Z.of_nat (Z.to_nat ((d * 4096) / 4096)) = d) by (intros d Hd; rewrite Z_div_mult by lia; apply Z2Nat.id; exact Hd).
  assert (EWQ : Wz r6 - PEz x = (kw - kq) * 4096) by lia.
  assert (NE : nE r6 = Z.to_nat (kw - kq)) by (unfold nE, Q18; rewrite EWQ, Z_div_mult by lia; reflexivity).
  rewrite NE.
  repeat split; lia.
Qed.

Lemma lazy_mP_facts : ltac2:(tb__ "0|4|
S1Se4S6fS110Vm;VP;A2A1M0A1S5aS18Q40M1A1M2G2A2M3S88G3R1G0A3SaZ0S19G1S60G2G2R2A3A2A2F_;Fr;A2").
Proof using HPL Hlz Hmaps Hres Htop.
  clear -HPL Hlz Hmaps Hres Htop. rewrite (lazy_mP m a1 a2 Hres Hmaps Hlz Htop P HPL). pose proof P_facts as (Pal & Pceil & _).
  pose proof (alloc_top_lt (m_vmmaps m)) as TL. unfold two_pow_64 in TL.
  assert (U7 : bv_unsigned n7 = 0x2000011000) by (unfold n7; apply u64_of_lit; lia).
  split.
  - repeat (apply ivs_wf_cons; [unfold iv_wf, ivB, ivS; cbn [fst snd]; rewrite ?U7, ?u64_of_lit by lia; lia|]). apply ivs_wf_nil.
  - intros r Hr. repeat (destruct Hr as [<-|Hr]; [cbn [snd]; rewrite ?U7, ?u64_of_lit by lia; lia|]). destruct Hr.
Qed.
Lemma lazy_m8_facts : ltac2:(tb__ "0|4|
S1Se4S6fS10dVm;VP;A2A1M0A1S5aS18Q40M1A1M2G2A2M3S88G3R1G0A3SaZ0S19G1S60G2G2R2A3A2A2F_;Fr;A2").
Proof using HPL Hlz Hmaps Hres Htop.
  clear -HPL Hlz Hmaps Hres Htop. pose proof lazy_mP_facts as [W7 P7]. rewrite (lazy_m8 m P).
  destruct (maps_subtract_sem (m_vm_lazy (m7 m P)) (bv_unsigned (RI P)) (bv_unsigned (RI P) + bv_unsigned pg) W7 ltac:(pose proof (urange pg); lia)) as (W8' & _).
  split; [exact W8'|]. apply maps_subtract_pos; [exact W7 | exact P7].
Qed.
Lemma lazy_mF_facts : ltac2:(tb__ "0|4|
S1Se4S6fS103Vm;VP;Vb4;Vb5;Vb6;Vb7;Vb8;Vb9;A8A1M0A1S5aS18Q40M1A1M2G2A2M3S88G3R1G0A3SaZ0S19G1S60G2G2R2A3A2A2F_;Fr;A2").
Proof using HPL HPL4 Hlz Hmaps Hres Htop.
  clear -HPL HPL4 Hlz Hmaps Hres Htop. pose proof lazy_m8_facts as [W8' P8]. pose proof mF_vmmaps as (_ & _ & _ & _ & _ & LZ).
  unfold Start6.mF in LZ. rewrite LZ.
  pose proof b4_facts as (F4lo & F4band & F4top & F4al & _). pose proof (alloc_top_lt (m_vmmaps m)) as TL. unfold two_pow_64 in TL.
  assert (W4 : iv_wf (b4, n9)) by (unfold iv_wf, ivB, ivS, n9; cbn [fst snd]; rewrite u64_of_lit by lia; lia).
  assert (WL : ivs_wf (lazy_interior b4 n9 ++ m_vm_lazy (m8 m P))).
  { apply ivs_wf_app; [|exact W8']. intros q Hq. exact (proj2 (lazy_interior_pos b4 n9 q W4 Hq)). }
  destruct (maps_subtract_sem _ (bv_unsigned b9) (bv_unsigned b9 + 4096) WL ltac:(lia)) as (WF & _).
  unfold Start6.b9lo. split; [exact WF|]. apply maps_subtract_pos; [exact WL|].
  intros r Hr. apply in_app_iff in Hr as [Hr|Hr]; [exact (proj1 (lazy_interior_pos b4 n9 r W4 Hr)) | exact (P8 r Hr)].
Qed.
Lemma lazy_mE_facts : ltac2:(tb__ "0|4|
S1Se4S6fS35A1M0A1S5aS18Q40M1A1M2G2A2M3S88G3R1G0A3SaZ0S19G1S60G2G2R2A3A2A2F_;Fr;A2").
Proof using HPL HPL4 Hlz Hmaps Hres Htop Hx H16.
  clear -HPL HPL4 Hlz Hmaps Hres Htop Hx H16. pose proof lazy_mF_facts as [WF PF]. pose proof mE_fields as (_ & _ & _ & _ & LZ & _). rewrite LZ.
  pose proof (m16_fields x) as (_ & _ & _ & _ & LZ6 & _). rewrite LZ6. unfold Start6.mF. split; [exact WF | exact PF].
Qed.

Lemma high_shadow_lazy_mE : ltac2:(tb__ "0|1|
S18Q40M0A1S8S39S19G0R1A2A2S8S9S19G0R2A2Z1000A2SdeA2S0S5cS73R3S6fS35A1A2S5dA3F_;F_;Fp;").
Proof using HPL HPL4 HPL5 HPL6 HPL7 HPL8 HPL9 Hlz Hmaps Hres Htop Hx H16.
  clear Ha1 Ha2 HBlim Hsb Hbrk Hbal HPL10 Hxtop.
  intros p Hlo Hhi. pose proof mE_fields as (_ & _ & _ & _ & LZ & _). rewrite LZ.
  pose proof (m16_fields x) as (_ & _ & _ & _ & LZ6 & _). rewrite LZ6.
  pose proof CAx as CA. cbv zeta in CA. destruct CA as (Ct & CHPlo & CPEhi & CPEHP & CHPq & CPEe & CPEal & CLIM & CLIM0 & CPB & CLEN & Ce12al).
  clear LZ LZ6. unfold Q18 in Hlo. unfold kHighMemBeg in *.
  apply high_shadow_lazy_mF; unfold SHADOW_BAND_HI; lia.
Qed.

Lemma noacc_mF_wf : ltac2:(tb__ "0|0|
Se4S74S6bS103Vm;VP;Vb4;Vb5;Vb6;Vb7;Vb8;Vb9;A8A1A1A1").
Proof using HPL HPL4 Hna Hmaps Hres Htop.
  clear -HPL HPL4 Hna Hmaps Hres Htop. pose proof mF_vmmaps as (_ & _ & NA & _). unfold Start6.mF in NA. rewrite NA. unfold Start6.b9lo.
  exact (proj1 (maps_subtract_sem _ (bv_unsigned b9) (bv_unsigned b9 + 4096) W9 ltac:(lia))).
Qed.

Lemma high_shadow_acc_mE : ltac2:(tb__ "0|0|
S6S1S8Z2008fff7000R1A2SaR1SdeA2A2S0S5cSe6S74S6bS35A1A1R2A2S68A3F_;Fz;").
Proof using HPL HPL4 HPL5 HPL6 HPL7 HPL8 HPL9 Hlz Hna Hmaps Hres Htop Hx H16.
  clear Ha1 Ha2 HBlim Hsb Hbrk Hbal HPL10 Hxtop.
  intros z Hz. pose proof mE_fields as (_ & _ & _ & _ & _ & NA & _). rewrite NA.
  pose proof (m16_fields x) as (_ & _ & _ & _ & _ & NA6). rewrite NA6.
  apply high_shadow_acc_mF. unfold SHADOW_BAND_HI. unfold kHighMemBeg in Hz. exact Hz.
Qed.

Lemma hs_map_mE : ltac2:(tb__ "0|2|
S88S5aS18Q40M0A1M1G1A2S5bG1G1S1aG0Z2008fff7000A2S1aG0Zdfff0001000A2A4S6cS6bS35A1A1A3").
Proof using HPL HPL4 HPL5 HPL6 HPL7 HPL8 HPL9 Hmaps Hres Htop Hx.
  clear Ha1 Ha2 HBlim Hsb Hbrk Hbal HPL10 Hxtop.
  pose proof mE_fields as (_ & MM & _). rewrite MM. right.
  apply (maps16_keep x); [|rewrite u64_of_lit by lia; lia].
  pose proof (m13_ledger m P b4 b5 b6 b7 b8) as (_ & M13 & _). rewrite M13. right.
  pose proof (m12_ledger m P b4 b5 b6 b7) as (_ & M12 & _). rewrite M12. right.
  pose proof (mE_ledger m P b4 b5 b6) as (_ & M11 & _). rewrite M11. do 4 right.
  rewrite Hmaps. cbn [In]. tauto.
Qed.
Lemma s4_map_mE : ltac2:(tb__ "0|2|
S88S5aS18Q40M0A1M1G1A2S5bG1G1S1aG0Z7fff7000A2S1aG0Z10000000A2A4S6cS6bS35A1A1A3").
Proof using HPL HPL4 HPL5 HPL6 HPL7 HPL8 HPL9 Hmaps Hres Htop Hx.
  clear Ha1 Ha2 HBlim Hsb Hbrk Hbal HPL10 Hxtop.
  pose proof mE_fields as (_ & MM & _). rewrite MM. right.
  apply (maps16_keep x); [|rewrite u64_of_lit by lia; lia].
  pose proof (m13_ledger m P b4 b5 b6 b7 b8) as (_ & M13 & _). rewrite M13. right.
  pose proof (m12_ledger m P b4 b5 b6 b7) as (_ & M12 & _). rewrite M12. right.
  pose proof (mE_ledger m P b4 b5 b6) as (_ & M11 & _). rewrite M11. do 4 right.
  rewrite Hmaps. cbn [In]. tauto.
Qed.

Lemma m40_mE : ltac2:(tb__ "0|0|
Sd6S35A1ScdS35S3bA2F_;").
Proof using HBlim HPL HPL4 HPL5 HPL6 HPL7 HPL8 HPL9 Hbal Hbrk Hlz Hmaps Hres Hsb Htop Hx H16.
  clear Ha1 Ha2 HPL10 Hxtop.
  intros Hlim. pose proof mE_fields as (MR & MM & ML & MB & LZ & NA & K1 & K2). pose proof lazy_mE_facts as [_ PZ]. destruct Hbal as [kb Hkb].
  constructor.
  - rewrite MR. exact Hres.
  - rewrite K1, K2. exact Hsb.
  - unfold brk0w. rewrite K1, Hkb. apply Z_mod_mult.
  - unfold brk0w. rewrite K1. lia.
  - unfold brk0w. rewrite K1. lia.
  - rewrite ML. unfold B18pre, BE, B17, B16L, B16, BF, B12x, B12, B11, n17. lia.
  - exact init_sp_ok_mE.
  - exact band_mE.
  - exact PZ.
  - exact Hlim.
Qed.

Definition rho18g (rho : valuation) : valuation := ltac2:(tb__ "0|1|
S119S119Vrho;P54S1aQ40M0S3dA2A3P55S1aG0SbS41S36Vrho;A1A1S3dA2A2A3").

Lemma E18_facts23 : ltac2:(tb__ "0|1|
S1S0S5cS89S20S2dS2eS25P2A1S21Z400A1A2A1S22S80SdcA1A1M0A3S5dA3S0S5cS89S20S2dS2eS25P3A1S21Z100A1A2A1G0A3S5dA3A2").
Proof. clear. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma E18b_eq : ltac2:(tb__ "0|0|
S0S34S11cS80SdcA1P56A2S99A3"). Proof. clear. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma E18_at2 : ltac2:(tb__ "0|1|
S1S0S7S27S80SdcA1A1P54A3S1S0S59S5aS1dS1dA2M0A1S82SdcA1S5fG0A1A3S0S1dS83SdcA1S21SdfA1A3A2A2"). Proof. clear. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Lemma ghost18 : ltac2:(tb__ "0|2|
S1cSd8S0S6SacR2A1Vx;A3S8S9Vx;Z50A2S36R3A1A2S8S9S36R4A1Z10M0A2SeZ2Z2fA2A2S8S9S36R5A1G0A2S9Vx;Z2228cfA2A2Sa4S69Sa7S35S48A2M1SdcR6SaeR6A1R5A6Sa4S69G1S81S95S5fS5aS1dS1dA2A1S21SdfA1A3S58R7A1SaeR7A1R6A6F_;F_;F_;F_;F_;Fw;Frho;").
Proof using Hx H16 Hxtop.
  clear Hres Hmaps Hna Hlz Htop Ha1 Ha2 HBlim Hsb Hbrk Hbal OKF OKP HPL HPL4 HPL5 HPL6 HPL7 HPL8 HPL9 HPL10.
  intros rho w Hx1 H1 H2 H3 Hsp. pose proof (arith18 _ H1 H2 H3) as AR.
  destruct AR as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & _). clear A6 A7 A8 A9 A13.
  pose proof (SPA_facts_hold segsA _ _ _ _ _ Hsp) as HF. cbn [ax_S] in HF.
  destruct E18_facts23 as [X2 X3]. pose proof (fact_of_state _ _ rho X2 HF) as F2. pose proof (fact_of_state _ _ rho X3 HF) as F3.
  cbn [holds eval] in F2, F3. rewrite u64_of_lit in F2 by lia. rewrite u64_of_lit in F3 by lia.
  pose proof (urange (rw rho 2%positive)) as UR2. pose proof (urange (rw rho 3%positive)) as UR3.
  destruct E18_at2 as (N84 & X0 & B0). destruct sd18 as (SD & WF & NX).
  set (rho' := rho18g rho).
  assert (R1 : rw rho' 1%positive = rw rho 1%positive) by (unfold rho', rho18g; rewrite !rho_set_rw_other by lia; reflexivity).
  assert (R2 : rw rho' 2%positive = rw rho 2%positive) by (unfold rho', rho18g; rewrite !rho_set_rw_other by lia; reflexivity).
  assert (R3 : rw rho' 3%positive = rw rho 3%positive) by (unfold rho', rho18g; rewrite !rho_set_rw_other by lia; reflexivity).
  assert (R6 : rw rho' 6%positive = rw rho 6%positive) by (unfold rho', rho18g; rewrite !rho_set_rw_other by lia; reflexivity).
  assert (U1 : bv_unsigned (rw rho' 1%positive) = x) by (rewrite R1; exact Hx1).
  assert (U6 : bv_unsigned (rw rho' 6%positive) = r6of rho) by (rewrite R6; reflexivity).
  unfold kHighMemBeg in *.
  assert (U84 : bv_unsigned (rw rho' 84%positive) = XBz) by (unfold rho', rho18g; rewrite rho_set_rw_other by lia; rewrite rho_set_rw_at; apply u64_of_lit; lia).
  assert (U85 : bv_unsigned (rw rho' 85%positive) = XEz (r6of rho) - XBz) by (unfold rho', rho18g; rewrite rho_set_rw_at; apply u64_of_lit; lia).
  assert (USP : bv_unsigned (eval rho' SP18) = x - 240) by (unfold SP18; rewrite U_add_slit' by (cbn [eval]; rewrite ?U1; lia); cbn [eval]; lia).
  assert (UXE : bv_unsigned (eval rho' XE18) = XEz (r6of rho)).
  { unfold XE18, XB18, XL18. cbn [eval]. rewrite add_val, U84, U85. rewrite Z.mod_small by lia. lia. }
  assert (UAX : bv_unsigned (eval rho' AUXV18) = x + 8 * bv_unsigned (rw rho 2%positive) + 8 * bv_unsigned (rw rho 3%positive) + 24).
  { unfold AUXV18. cbn [eval]. rewrite !add_val, !sll_val. change (3 mod 64) with 3. rewrite !Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8.
    rewrite R1, R2, R3. unfold x1 in Hx1. rewrite Hx1. rewrite (u64_of_lit 24) by lia.
    pose proof (urange (rw rho 2%positive)). pose proof (urange (rw rho 3%positive)).
    set (u2 := bv_unsigned (rw rho 2%positive)) in *. set (u3 := bv_unsigned (rw rho 3%positive)) in *.
    rewrite (Z.mod_small (u2 * 8)) by lia. rewrite (Z.mod_small (u3 * 8)) by lia. rewrite (Z.mod_small (x + u2 * 8)) by lia.
    rewrite (Z.mod_small (x + u2 * 8 + u3 * 8)) by lia. rewrite Z.mod_small by lia. lia. }
  replace (mkAX E18g [] (SLit SHB)) with (ax_setS E18 E18g) by (rewrite <- X0, <- B0; reflexivity).
  apply (SPA_ghosts (KxA mE BE) rho rho' E18 E18g 86%positive (TP17 rho) w [] F18).
  - intros r r' t tr md X; exact X.
  - rewrite N84. unfold rho', rho18g. split; [intros i Hi; rewrite !rho_set_rw_other by lia; reflexivity | split; [intros l; reflexivity | intros a; reflexivity]].
  - rewrite N84. lia.
  - exact WF.
  - rewrite E18b_eq. exact SD.
  - exact NX.
  - constructor.
  - unfold F18. repeat apply Forall_cons; try apply Forall_nil; cbn [holds]; unfold XB18, XL18 in *.
    + split; [lia|]. rewrite U84. change (2 ^ 6) with 64. exact A1.
    + split; [lia|]. rewrite U85. change (2 ^ 6) with 64. lia.
    + rewrite (U_add_lit rho' (SVar 84%positive) 512) by (cbn [eval]; rewrite ?U84; lia). cbn [eval]. rewrite U84, USP. lia.
    + rewrite USP, UXE. lia.
    + cbn [eval]. rewrite U84, U6. lia.
    + rewrite (U_add_slit' rho' (SVar 6%positive) 16) by (cbn [eval]; rewrite ?U6; lia). cbn [eval]. rewrite U6, UXE. lia.
    + cbn [eval]. rewrite U85, u64_of_lit by lia. lia.
    + cbn [eval]. rewrite U84, u64_of_lit by lia. lia.
    + cbn [eval]. rewrite U84, u64_of_lit by lia. lia.
    + rewrite UXE. cbn [eval]. rewrite u64_of_lit by lia. lia.
    + rewrite (U_add_lit rho' SP18 320) by (rewrite ?USP; lia). rewrite USP. cbn [eval]. rewrite U6. lia.
    + rewrite (U_add_lit rho' SP18 64) by (rewrite ?USP; lia). rewrite USP, UAX. lia.
    + rewrite UAX. cbn [eval]. rewrite u64_of_lit by lia. lia.
    + rewrite UAX. cbn [eval]. rewrite u64_of_lit by lia. lia.
  - exact Hsp.
Qed.

Lemma land_land_distr : ltac2:(tb__ "0|0|
S6S6S6S0S6SfSfR3R2A2R1A2SfSfR3R1A2SfR2R1A2A2A3Fc;Fb;Fa;").
Proof.
  clear. intros a b c. apply Z.bits_inj'. intros n Hn. rewrite !Z.land_spec.
  destruct (Z.testbit a n), (Z.testbit b n), (Z.testbit c n); reflexivity.
Qed.
Lemma mod256_land : ltac2:(tb__ "0|0|
S6S8Z0R1A2S0S6ScR2Z100A2SfR2ZffA2A3F_;Fa;").
Proof. clear. intros a Ha. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. reflexivity. Qed.
Definition M18 : Z := 18446744073709486335.
Lemma landM_byte : ltac2:(tb__ "0|3|
S6S5eS8Z0M0R2A2S109R2U8A2S0S6ScS13SfR4S55A2SdZ8S11R3A1A2M1A2Z100M2A2S5cS6L_;S108R3U1A2G0ScS13R4G1A2G2A2X5cx2A3F_;F_;Fk;Fv;").
Proof.
  clear. intros v k Hv Hk.
  assert (Hs : 0 <= Z.shiftr v (8 * Z.of_nat k)) by (apply Z.shiftr_nonneg; lia).
  rewrite Z.shiftr_land. rewrite mod256_land by (apply Z.land_nonneg; left; exact Hs). rewrite land_land_distr.
  assert (E : Z.land (Z.shiftr M18 (8 * Z.of_nat k)) 255 = if Nat.eqb k 1 then 0 else 255).
  { do 8 (destruct k as [|k]; [reflexivity|]). lia. }
  rewrite E. destruct (Nat.eqb k 1); [apply Z.land_0_r|]. rewrite <- Z.land_assoc, Z.land_diag. rewrite <- mod256_land by exact Hs. reflexivity.
Qed.
Lemma EV18_bytes : ltac2:(tb__ "0|2|
S1cS5eS1dS0S61S1dA1S8aS1dS97R2A3S65S1dR1A2A3S0S6ScS19Q40M0S24R4R2A2A2Z100M1A2ScS13S19G0S24R4S9aA2A2SdZ8S11R3A1A2A2G1A2A3F_;Fe;Fk;Frho;").
Proof.
  clear. intros rho k e Hk.
  pose proof (urange (rw rho 9%positive)) as U9. set (v := bv_unsigned (rw rho 9%positive)) in *.
  assert (EV : bv_unsigned (eval rho EV18) = Z.land v M18).
  { unfold EV18. cbn [eval]. rewrite and_val, u64_of_lit by lia. reflexivity. }
  rewrite EV.
  do 8 (destruct k as [|k]; [cbn in Hk; injection Hk as <-; rewrite landM_byte by lia; cbn [Nat.eqb]; cbn [eval];
    rewrite ?U_zext8, ?srl_val, ?u64_of_lit by lia; fold v;
    match goal with |- context [Z.shiftr v (8 * Z.of_nat ?k)] => let n := eval cbv in (8 * Z.of_nat k) in change (8 * Z.of_nat k) with n | _ => idtac end;
    rewrite ?Z.shiftr_0_r, ?Z.mod_mod by lia;
    try reflexivity;
    match goal with |- context [Z.shiftr v (?a mod 64)] => let n := eval cbv in (a mod 64) in change (a mod 64) with n end; reflexivity |]).
  destruct k; discriminate.
Qed.

Lemma C18_ssp_nth : ltac2:(tb__ "0|1|
S0S61S1eA1S8aS1eS2bS98A1U15A3S65S1eS2fS21Z0A1S21Z6445f8M0A1S21Z644600A1S64S2cS11dG0S97A2S5fS2cA1A3S31A5A2A3").
Proof. clear. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma shape18 : ltac2:(tb__ "0|2|
Sa5S1cS59S18Q40A1A1Sd8Sa4S69R4S81S95S5fS5aS1dS1dA2A1M0S21SdfA1M1A3R3R2R1A6Sa4S69R5S81S90G0G1A3R4R3R2A6F_;Fw;Ftp;Frho;FJ;").
Proof.
  clear. intros J rho tp w H0.

  pose proof (SPA_split_chain segsA J rho splits18 (mkAX E18g [] (SLit SHB)) C18a tp w split18_ok H0) as H1. cbn [ax_setS] in H1.

  destruct C18b_facts as (N19 & D19 & S19 & E19).
  pose proof (SPA_img_to_unknown J rho (mkAX C18a [] (SLit SHB)) 19 o18errno tp w N19 D19 S19 H1) as H2. cbn [ax_S ax_setS] in H2. rewrite E19 in H2.

  destruct C18c_facts as (N21 & B21 & L21 & U21 & D21 & I1 & I2 & S21 & E21).
  pose proof (SPA_cells_equiv J rho (mkAX C18b [] (SLit SHB)) 21 (SLit 0) (SLit 0x6445f8) (SLit 0x644600) (ob_cells o18ssp) bytes18 DImage tp w) as H3.
  cbn [ax_S ax_setS] in H3.
  assert (EO : mkObj (SLit 0) (SLit 0x6445f8) (SLit 0x644600) (ob_cells o18ssp) DImage = o18ssp).
  { destruct o18ssp as [b l h cs d]. cbn [ob_base ob_lo ob_hi ob_dflt ob_cells] in B21, L21, U21, D21 |- *. subst. reflexivity. }
  rewrite EO in H3. change (mkObj (SLit 0) (SLit 0x6445f8) (SLit 0x644600) bytes18 DImage) with o18ssp_s in H3.
  specialize (H3 N21 (cells_incl_sound _ _ I2) (cells_incl_sound _ _ I1) S21 H2). rewrite E21 in H3.
  destruct C18d_facts as (_ & S21m & E21m & N21m & S21u & E21u).
  pose proof (SPA_merge8 J rho (mkAX C18c [] (SLit SHB)) 21 (SLit 0) (SLit 0x6445f8) (SLit 0x644600) DImage 0x6445f8 es18 EV18 [] tp w C18_ssp_nth eq_refl ltac:(lia) ltac:(lia)) as H4.
  cbn [ax_S ax_setS] in H4. change (mkObj (SLit 0) (SLit 0x6445f8) (SLit 0x644600) (mkCell (SLit 0x6445f8) 8 EV18 :: []) DImage) with o18ssp_m in H4.
  specialize (H4 ltac:(intros _ k e Hk; exact (EV18_bytes rho k e Hk)) S21m H3).
  rewrite E21m in H4.
  pose proof (SPA_img_to_unknown J rho (mkAX C18d [] (SLit SHB)) 21 o18ssp_m tp w N21m eq_refl S21u H4) as H5. cbn [ax_S ax_setS] in H5. rewrite E21u in H5.

  destruct C18e_facts as (N43 & D43 & F43 & S43 & E43).
  pose proof (SPA_drop_cells_unknown J rho (mkAX C18d' [] (SLit SHB)) 43 o18win (fun _ => false) tp w N43 D43) as H6.
  unfold drop_cells in H6. rewrite F43 in H6. cbn [ax_S ax_setS] in H6. specialize (H6 S43 H5). rewrite E43 in H6. exact H6.
Qed.

Definition G18 : list (sv * Z) := ltac2:(tb__ "0|1|
S64S5aS1dS6A2M0Sb3S62G0S5bS1dS6S25P53A1SafA4S5fG0A1A3A3").
Lemma clear18 : ltac2:(tb__ "0|0|
S0S5cSe1S43S90A2S5dA3"). Proof. clear. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition bandw (z : Z) : Prop := ltac2:(tb__ "0|0|
S1S8SedVz;A2SaVz;SeeA2A2").
Definition lowb (rho : valuation) (z : Z) : Prop :=
  (SHADOW_BAND_LO <= z < q12x x) /\ ~ (priZ rho <= z < priZ rho + 512) /\ ~ (LOWPG <= z < LOWPG + 0x4c00).
Lemma q12x_hi : q12x x <= kHighMemBeg.
Proof using Hx. clear - Hx. unfold q12x, shx, kHighMemBeg. pose proof (Z.mod_pos_bound (x / 8 + 2147450880 - 131072) 4096 ltac:(lia)).
  assert (x / 8 <= 17592186044416) by (apply Z.div_le_upper_bound; lia). lia. Qed.

Lemma blocks18 : ltac2:(tb__ "0|3|
S1cS3aR1A1S0S18Q40M0A1M1S1bR2P24A2Vb7;A3S0G1S1bR3P4dA2Vb8;A3S0G1S1bR4P4eA2Vb9;A3S0G1S1bR5P53A2Vb10;A3S0S6SacR6A1Vx;A3S1dS6S88S5aS1dS6A2S5bS1dS6R2R1A4S43A3S3S8S9S19G0S24RaR3A2A2M2R2A2SadVx;A1A2S8SdeG2A2A2F_;Fsz;Fe;F_;F_;F_;F_;F_;F_;Frho;").
Proof using HPL HPL10 HPL4 HPL5 HPL6 HPL7 HPL8 HPL9 Ha1 Ha2 Hmaps Hres Htop Hx H16 Hxtop.
  clear Hlz Hsb Hbrk Hbal HBlim OKF OKP.
  intros rho HV H36 H77 H78 H83 Hx1 e sz Hin. pose proof b10_facts as (L1 & L2 & _).
  pose proof CAx as CA. cbv zeta in CA. destruct CA as (Ct & CHPlo & CPEhi & CPEHP & CHPq & CPEe & CPEal & CLIM & CLIM0 & CPB & CLEN & Ce12al).
  unfold G18, G17 in Hin. rewrite !in_app_iff in Hin. destruct Hin as [[Hin|[[= <- <-]|[]]]|[[= <- <-]|[]]].
  - assert (Hin' : In (e, sz) G14b) by (unfold G14b; apply in_app_iff; left; exact Hin).
    destruct (blocks16 rho HV H36 H77 H78 e sz Hin') as [Hb|(_ & _ & Hl & _)].
    + unfold SHADOW_BAND_LO, SHADOW_BAND_HI, kHighMemBeg in *. lia.
    + left. rewrite Hx1 in Hl. lia.
  - left. cbn [eval]. unfold LOWPG. rewrite u64_of_lit by lia. lia.
  - cbn [eval]. rewrite H83. unfold SHADOW_BAND_LO, SHADOW_BAND_HI, kHighMemBeg in *. lia.
Qed.

Lemma blocks18_low : ltac2:(tb__ "0|3|
S1cS3aR1A1S0S18Q40M0A1M1S1bR2P24A2Vb7;A3S0G1S1bR3P4dA2Vb8;A3S0G1S1bR4P4eA2Vb9;A3S0G1S1bR5P53A2Vb10;A3S0S6SacR6A1Vx;A3S1dS6S88S5aS1dS6A2S5bS1dS6R2R1A4S43A3S6S42RbR1A2S2S1S8S19G0S24RcR5A2A2M2R2A2SaR2S9G2R4A2A2A2A1F_;Fy;F_;Fsz;Fe;F_;F_;F_;F_;F_;F_;Frho;").
Proof using HPL HPL10 HPL4 HPL5 HPL6 HPL7 HPL8 HPL9 Ha1 Ha2 Hmaps Hres Htop Hx H16 Hxtop.
  clear Hlz Hsb Hbrk Hbal HBlim OKF OKP.
  intros rho HV H36 H77 H78 H83 Hx1 e sz Hin y (Hy & N1 & N2). pose proof b10_facts as (L1 & L2 & _).
  pose proof CAx as CA. cbv zeta in CA. destruct CA as (Ct & CHPlo & CPEhi & CPEHP & CHPq & CPEe & CPEal & CLIM & CLIM0 & CPB & CLEN & Ce12al).
  pose proof q12x_hi as QHI.
  unfold G18, G17 in Hin. rewrite !in_app_iff in Hin. destruct Hin as [[Hin|[[= <- <-]|[]]]|[[= <- <-]|[]]].
  - assert (Hin' : In (e, sz) G14b) by (unfold G14b; apply in_app_iff; left; exact Hin).
    destruct (blocks16 rho HV H36 H77 H78 e sz Hin') as [Hb|(-> & -> & Hl & Hh)].
    + unfold SHADOW_BAND_LO, SHADOW_BAND_HI, kHighMemBeg in *. lia.
    + change (eval rho shRI_base) with (pRI rho). rewrite (Upri rho HV). lia.
  - cbn [eval]. unfold LOWPG in *. rewrite u64_of_lit by lia. lia.
  - cbn [eval]. rewrite H83. unfold SHADOW_BAND_LO, SHADOW_BAND_HI, kHighMemBeg in *. lia.
Qed.

Lemma TP17_le : ltac2:(tb__ "0|3|
S1cS3aR1A1S0S6SacR2A1Vx;A3S0S6SdZ8S19Q40M0S1bR3P23A2A2A2S19G0Vb6;A2A3S18G0A1M1S88G1R1SaeR5A1A3S1S8S19G0R2A2M2S39A2S8Z7fff7000G2A2A2F_;Fp;F_;F_;F_;Frho;").
Proof using HPL HPL4 HPL5 HPL6 Hmaps Hres Htop Hx H16 Hxtop.
  clear Hlz Hsb Hbrk Hbal HBlim OKF OKP HPL10.
  intros rho HV Hx1 V35 p Hp. pose proof HV as (_ & _ & _ & _ & H31 & _ & _ & H34 & Hv1).
  pose proof CAx as CA. cbv zeta in CA. destruct CA as (Ct & CHPlo & CPEhi & CPEHP & CHPq & CPEe & CPEal & CLIM & CLIM0 & CPB & CLEN & Ce12al).
  pose proof (priZ_facts rho HV) as (PR1 & PR2 & PR3 & PR4). pose proof (sbZ_facts' rho HV V35) as SB1. rewrite Hx1 in PR1, SB1.
  unfold Q18, kHighMemBeg in *. unfold x1 in Hx1.
  assert (T12 : In p (TP12 rho) -> bv_unsigned p <= PEz x /\ 0x7fff7000 <= bv_unsigned p).
  { clear Hp. intros Hp. unfold TP12 in Hp. apply in_app_iff in Hp as [Hp|Hp].
    - apply In_pages_rev in Hp as (k & Hk & ->). apply Nat2Z.inj_lt in Hk. unfold pageZ.
      unfold n12, q12, e12, shZ in *. rewrite Hx1 in *. unfold e12x, q12x, shx in *.
      pose proof (pagedown_props (x / 8 + 2147450880 - 131072)) as [_ RQ]. pose proof (pagedown_props (x / 8 + 2147450880 - 9)) as [_ RE].
      set (q := x / 8 + 2147450880 - 131072 - (x / 8 + 2147450880 - 131072) mod 4096) in *.
      set (e := x / 8 + 2147450880 - 9 - (x / 8 + 2147450880 - 9) mod 4096) in *.
      assert (Hxd : 0x7fff80000000 / 8 <= x / 8 <= 2 ^ 47 / 8) by (split; apply Z.div_le_mono; lia).
      change (0x7fff80000000 / 8) with 17591917608960 in Hxd. change (2 ^ 47 / 8) with 17592186044416 in Hxd.
      assert (Hk' : Z.of_nat k <= (e - q) / 4096).
      { rewrite Z2Nat.id in Hk; [lia|]. apply Z.add_nonneg_nonneg; [apply Z.div_pos; lia | lia]. }
      assert (4096 * ((e - q) / 4096) <= e - q) by (apply Z.mul_div_le; lia).
      rewrite u64_of_lit by lia. lia.
    - unfold TP11 in Hp.
      pose proof (Upri rho HV) as UP.
      pose proof (Z.mod_pos_bound (sbZ rho) 4096 ltac:(lia)) as MB. pose proof (urange (rw rho 35%positive)) as U35.
      assert (Hpri : 0x2008fff7000 <= priZ rho /\ priZ rho + 12288 + 4096 <= PEz x) by lia.
      assert (Hsb : 0x7fff8000 - 4096 <= q1Z rho /\ q1Z rho + 12288 + 4096 <= PEz x) by (unfold q1Z in *; unfold sbZ in *; lia).
      destruct (q1Z rho =? priZ rho); repeat (destruct Hp as [<-|Hp]; [first [rewrite u64_of_lit by lia | rewrite UP]; lia|]); destruct Hp. }
  assert (T16 : In p (TP16 rho) -> bv_unsigned p <= PEz x /\ 0x7fff7000 <= bv_unsigned p).
  { clear Hp. intros Hp. unfold TP16 in Hp. unfold x1 in Hp. rewrite Hx1 in Hp.
    destruct (n16_val x Hx H16) as [N16 N16b]. destruct (site_arith x Hx H16) as (_ & SQlo & _ & _ & SQPE & _).
    apply in_app_iff in Hp as [Hp|Hp].
    - apply In_pages_rev in Hp as (k & Hk & ->). apply Nat2Z.inj_lt in Hk. unfold pageZ. rewrite u64_of_lit by lia. lia.
    - apply In_enspage_inv in Hp as [->|Hp]; [rewrite u64_of_lit by lia; lia | exact (T12 Hp)]. }
  apply In_TP17 in Hp as [(k & Hk & _ & Uk)|Hp]; [rewrite Uk; unfold LOWPG; lia | exact (T16 Hp)].
Qed.

Lemma objs18_clear : ltac2:(tb__ "0|1|
S1cS1cS6S6S3aR4A1S0S18Q40A1M0S1bR5P24A2Vb7;A3S0G0S1bR6P4dA2Vb8;A3S0G0S1bR7P4eA2Vb9;A3S0G0S1bR8P53A2Vb10;A3S0S6SacR9A1Vx;A3S7S0G0S1bRaR1A2S1bRbR1A2A3Fi;S7S0S59S18Q8A1A1S26RbR1A2S26RcR1A2A3Fl;Sa8S20S23RbA1S22S90A1A3S8SadVx;A1RbA2S8Z0RbA2S8S9RdRcA2SdeA2Sa8S1eS1eS29S28R10R1A2S5bS6S6RfS9RfReA2A4A2Lo;S2bS90A1A3F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Flen;Flo;Fr;Frho;").
Proof using HPL HPL10 HPL4 HPL5 HPL6 HPL7 HPL8 HPL9 Ha1 Ha2 Hmaps Hres Htop Hx H16 Hxtop.
  clear Hsb Hbrk Hbal OKF OKP Hlz HBlim.
  intros rho r lo len HV H36 H77 H78 H83 Hx1 Hrw Hrl HFr Hlo Hlen Hhi.
  pose proof CAx as CA. cbv zeta in CA. destruct CA as (Ct & CHPlo & CPEhi & CPEHP & CHPq & _).
  apply Forall_forall. intros o Ho.
  pose proof (objs_clear_e_sound r G18 C18e (Z_to_bv 64 lo) len HFr clear18 Hlen) as X. rewrite u64_of_lit in X by (unfold kHighMemBeg in *; lia).
  apply X; [unfold kHighMemBeg in *; left; lia | intros y Hy; unfold kHighMemBeg in *; lia | | exact Ho].
  intros e sz Hin y Hy.
  assert (Ee : eval r e = eval rho e) by (apply eval_ext_rwrl; assumption).
  rewrite Ee. destruct (blocks18 rho HV H36 H77 H78 H83 Hx1 e sz Hin); unfold kHighMemBeg in *; lia.
Qed.

Lemma outside_all_of_disjoint : ltac2:(tb__ "0|3|
S1cS59S1eA1S6S6S18Q40M0A1Sa8S1eS1eS29S28R6R1A2S5bS6S6R4S9R4R3A2M1A4A2Lo;R4A3S1S8R4S19G0R2A2M2A2SaG2G1A2A2S33R7R6R3A3F_;F_;Fa;Flen;Flo;Fobjs;Frho;").
Proof.
  clear. intros rho objs lo len a HF Ha. unfold outside_all. apply Forall_forall. intros o Ho.
  pose proof (proj1 (Forall_forall _ _) HF o Ho) as D. unfold ranges_disjoint in D. cbn [fst snd] in D. cbv zeta. lia.
Qed.

Lemma In_enspage_inv : ltac2:(tb__ "0|1|
S18Q40A1M0G0S59G0A1S88G0R3Sb1R2R1A2A3S3S0G0R4R3A3S88G0R4R2A3A2F_;Ftp;Fp;Fq;").
Proof.
  clear. intros q p tp H. unfold enspage in H.
  destruct (page_mem p tp); [right; exact H | destruct H as [E|H]; [left; symmetry; exact E | right; exact H]].
Qed.

Lemma pay18 : ltac2:(tb__ "0|7|
S1cS59S6dA1M0Sd2S6aS3aR4A1S0S6SacR5A1Vx;A3S0S18Q40M1A1M2S1bR6P24A2Vb7;A3S0G2S1bR7P4dA2Vb8;A3S0G2S1bR8P4eA2Vb9;A3S0G2S1bR9P53A2Vb10;A3S0S6SdZ8S19G1S1bRaP23A2A2A2S19G1Vb6;A2A3S8S9Vx;Z50A2S36RbA1A2S8S9S36RcA1Z10M3A2SeZ2Z2fA2A2S8S9S36RdA1G3A2S9Vx;Z2228cfA2A2S4aReA1Sa4S69Sa7S35S48A2S81S90S5fS5aS1dS1dA2A1S21SdfA1A3M4RfSaeRfA1S5bG0S10aReS10bRdRcA2A4A6S4S1cS1cS1Sa4S69Sa7S35S3bA2G4R1S3cR11A1S5bG0S10aR10S10bRfReA2A4A6S1S7S0G2S1bR2R1A2S1bR12R1A2A3Fi;S1S7S0S59S18Q8A1M5A1S26R2R1A2S26R12R1A2A3Fl;S1S4dS36R11A1R1A2G2S3SaS19G1R1A2M6S39A2S8S10S39S44S36R12A1A1A2G6A2A2S0S61G5A1S1fR3R2A2S1fR13R2A2A3F_;Fa;A2A2A2A2Lrho';A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd;Fms;Ftr;Frho;").
Proof using HBlim HPL HPL10 HPL4 HPL5 HPL6 HPL7 HPL8 HPL9 Ha1 Ha2 Hlz Hmaps Hna Hres Htop Hx H16 Hxtop.
  clear Hsb Hbrk Hbal OKF OKP.
  intros rho tr ms md HV Hx1 H36 H77 H78 H83 V35 H1 H2 H3 HSZ Hsp.
  pose proof (arith18 _ H1 H2 H3) as AR.
  destruct AR as (_ & A2 & _ & A4 & A5 & _ & _ & _ & _ & A10 & A11 & A12 & _ & A14 & A15 & A16 & A17 & A18 & A19 & A20 & A21 & A22 & A23 & A24).
  unfold kHighMemBeg in A14, A15, A18, A24.
  pose proof Hsp as [Hsm (Htr & Hem & Hpaid)]. cbn [w_tr w_cfg cfg_model fst snd] in Htr, Hem, Hpaid. unfold BE in Hpaid.
  pose proof (erase_mat_eq_fields md mE Hem) as (Evm & Elz & _). pose proof mE_fields as (_ & _ & ML & _).
  pose proof (SPA_facts_hold segsA _ _ _ _ _ Hsp) as HF. cbn [ax_S] in HF.
  set (J' := fun (r : valuation) (_ : list word) (tr0 : list event) (md0 : Model) => KxA mE B18pre r (TP18 rho) tr0 md0).
  assert (HJ' : forall r r' t t', J' r t tr md -> J' r' t' tr md) by (intros r r' t t' X; exact X).

  assert (PB : paid md (TP18 rho) <= B18pre).
  { unfold TP18. unfold B18pre, BE. destruct (nE (r6of rho) =? 0)%nat eqn:En; [klia|].
    pose proof (paid_app_le md (pages_rev (Q18 + 4096) (nE (r6of rho) - 1)) (enspage (Z_to_bv 64 Q18) (TP17 rho))) as P1. rewrite length_pages_rev in P1.
    pose proof (paid_enspage_le md (Z_to_bv 64 Q18) (TP17 rho)) as P2. unfold page_size in *. apply Nat.eqb_neq in En. klia. }
  assert (Hsp0 : SPA segsA J' (mkAX C18e [] (SLit SHB)) rho (TP17 rho) (tr, mkCfg ms md)).
  { split; [exact Hsm|]. subst J'. cbv beta. split; [exact Htr|]. split; [exact Hem|]. exact PB. }
  destruct (nE (r6of rho)) as [|k] eqn:EN.
  -
    exists rho. assert (ET : TP18 rho = TP17 rho) by (unfold TP18; rewrite EN; reflexivity).
    split; [rewrite ET; destruct Hsp0 as [S0 K0]; split; [exact S0 | subst J'; cbv beta in K0; rewrite ET in K0; exact K0]|].
    split; [intros; reflexivity|]. split; [intros; reflexivity|]. split; [|intros; reflexivity].
    intros z Hz. apply (proj1 HSZ). specialize (A22 eq_refl). klia.
  - specialize (A23 ltac:(discriminate)). assert (Hk : Z.of_nat (S k) = Z.of_nat k + 1) by klia. rewrite Hk in A23, A21.

    destruct (ensure_page J' (mkAX C18e [] (SLit SHB)) Q18 Q18 (Q18 + 4096) rho (TP17 rho) tr ms md Hsp0 HJ' A16 ltac:(klia) ltac:(klia) ltac:(lia) ltac:(lia))
      as (rho1 & tp1 & Hsp1 & Hrw1 & Hrl1 & Hz1 & Ho1 & Hfz1 & Hsm1 & Htp1).
    + rewrite Elz. apply high_shadow_lazy_mE; rewrite u64_of_lit by klia; klia.
    + intros z Hz. rewrite Evm. apply high_shadow_acc_mE. klia.
    + unfold headroom. rewrite Evm, ML. unfold BE, B17, B16L, B16, BF, B12x, B12, B11, n17, page_size in *. klia.
    + intros _. cbn [ax_S]. apply (objs18_clear rho rho Q18 4096 HV H36 H77 H78 H83 Hx1); [intros; reflexivity | intros; reflexivity | exact HF | klia | klia | klia].
    + intros Hin a Ha. apply In_TP17 in Hin as [(k' & Hk' & _ & Uk)|Hin].
      * exfalso. rewrite u64_of_lit in Uk by klia. unfold LOWPG in Uk. klia.
      * apply (proj2 HSZ); [|exact Ha]. apply page_mem_In. exact Hin.
    +
      pose proof (SPA_facts_hold segsA _ _ _ _ _ Hsp1) as HF1. cbn [ax_S] in HF1.
      destruct (SPA_prepay_pages_rm J' (mkAX C18e [] (SLit SHB)) (Q18 + 4096) k rho1 tp1 tr ms md Hsp1 HJ'
                  ltac:(rewrite <- Zplus_mod_idemp_l, A16; reflexivity) ltac:(klia) ltac:(klia))
        as (rho2 & Hsp2 & Hrw2 & Hrl2 & Hz2 & Ho2).
      * intros k' Hk'. rewrite Elz. apply high_shadow_lazy_mE; unfold pageZ; rewrite u64_of_lit by klia; klia.
      * intros k' Hk' Hin. rewrite Htp1 in Hin.
        assert (Hin' : In (pageZ (Q18 + 4096) k') (TP17 rho) \/ pageZ (Q18 + 4096) k' = Z_to_bv 64 Q18).
        { destruct (page_mem (Z_to_bv 64 Q18) (TP17 rho)); [left; exact Hin | destruct Hin as [E|Hin]; [right; symmetry; exact E | left; exact Hin]]. }
        destruct Hin' as [Hin'|E].
        -- pose proof (proj1 (TP17_le rho HV Hx1 V35 _ Hin')) as LE. unfold pageZ in LE. rewrite u64_of_lit in LE by klia. klia.
        -- apply (f_equal bv_unsigned) in E. unfold pageZ in E. rewrite !u64_of_lit in E by klia. klia.
      * intros z Hz. rewrite Evm. apply high_shadow_acc_mE. klia.
      * unfold headroom. rewrite Evm, ML. rewrite Htp1.
        pose proof (paid_enspage_le md (Z_to_bv 64 Q18) (TP17 rho)) as P2. unfold enspage in P2.
        unfold BE, B17, B16L, B16, BF, B12x, B12, B11, n17, page_size in *. klia.
      * cbn [ax_S]. apply (objs18_clear rho rho1 (Q18 + 4096) (4096 * Z.of_nat k) HV H36 H77 H78 H83 Hx1 Hrw1 Hrl1 HF1); klia.
      * exists rho2.
        assert (ET : TP18 rho = pages_rev (Q18 + 4096) k ++ tp1).
        { unfold TP18. rewrite EN. cbn [Nat.eqb]. replace (S k - 1)%nat with k by klia. rewrite Htp1. unfold enspage. reflexivity. }
        split; [rewrite ET; destruct Hsp2 as [S2 K2]; split; [exact S2 | subst J'; cbv beta in K2; rewrite ET in K2; exact K2]|].
        split; [intros i; rewrite Hrw2; apply Hrw1|]. split; [intros l; rewrite Hrl2; apply Hrl1|]. split.
        -- intros z Hz. destruct (Z.lt_ge_cases z Q18).
           ++ rewrite Ho2 by (rewrite u64_of_lit by klia; klia). rewrite Ho1 by (rewrite u64_of_lit by klia; klia).
              apply (proj1 HSZ). klia.
           ++ destruct (Z.lt_ge_cases z (Q18 + 4096)).
              ** rewrite Ho2 by (rewrite u64_of_lit by klia; klia). apply Hz1. klia.
              ** apply Hz2. klia.
        -- intros a Ha. rewrite Ho2 by klia. apply Ho1. klia.
Qed.

Lemma C18e_xr : ltac2:(tb__ "0|0|
S0S5cS87S27S90A1S5bS1dS1dSa2Sa3A4A2S5dA3"). Proof. clear. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma publish18 : ltac2:(tb__ "0|3|
Sa5S1cS59S18Q40M0A1M1A1Sd8S3aR3A1S0G1S1bR4P24A2Vb7;A3S0G1S1bR5P4dA2Vb8;A3S0G1S1bR6P4eA2Vb9;A3S0G1S1bR7P53A2Vb10;A3S0S6SacR8A1Vx;A3S8S9Vx;Z50A2S36R9A1A2S8S9S36RaA1Z10M2A2SeZ2Z2fA2A2S8S9S36RbA1G2A2S9Vx;Z2228cfA2A2S0G1S1bRcP54A2S1aG0S3dA2A3S0G1S1bRdP55A2S1aG0SbS41S36RdA1A1S3dA2A2A3S4dS36ReA1ReA2Sa4S69R10S81S90S5fS5aS1dS1dA2A1S21SdfA1A3RfReRdA6Sa4S69R11S8fR10RfReA6F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fw;Ftp;Frho;FJ;").
Proof using HPL HPL10 HPL4 HPL5 HPL6 HPL7 HPL8 HPL9 Ha1 Ha2 Hmaps Hres Htop Hx H16 Hxtop.
  clear Hsb Hbrk Hbal OKF OKP Hlz HBlim.
  intros J rho tp w HV H36 H77 H78 H83 Hx1 H1 H2 H3 R84 R85 HZ Hsp.
  pose proof (arith18 _ H1 H2 H3) as AR.
  destruct AR as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17 & A18 & A19 & A20 & A21 & A22 & A23 & A24).
  pose proof (SPA_facts_hold segsA _ _ _ _ _ Hsp) as HF. cbn [ax_S] in HF.
  unfold C18, X18. change (mkAX C18e [(XB18, XL18)] (SLit SHB)) with (ax_setX (mkAX C18e [] (SLit SHB)) ((XB18, XL18) :: ax_X (mkAX C18e [] (SLit SHB)))).
  apply SPA_x_publish; [exact C18e_xr | | exact Hsp]. cbn [ax_S ax_base].
  assert (U84 : bv_unsigned (rw rho 84%positive) = XBz) by (rewrite R84; apply u64_of_lit; unfold kHighMemBeg; klia).
  assert (U85 : bv_unsigned (rw rho 85%positive) = XEz (r6of rho) - XBz) by (rewrite R85; apply u64_of_lit; unfold kHighMemBeg; klia).
  assert (ESH : bv_unsigned (eval rho (SLit SHB)) = SHB) by (cbn [eval]; apply u64_of_lit; unfold SHB; klia). rewrite ESH.
  apply (xr_ok_of_zero rho (ss_objs C18e) SHB (XB18, XL18) SXB (SXE (r6of rho))); cbn [fst snd]; unfold XB18, XL18; cbn [eval]; rewrite ?U84, ?U85.
  - apply Z.mod_divide in A1 as [kb ->]; [|klia]. replace (kb * 64) with (kb * 8 * 8) by klia. apply Z_mod_mult.
  - klia.
  - klia.
  - klia.
  - exact A6.
  - exact A7.
  - intros a Ha.
    assert (D1 : XBz / 8 <= a / 8) by (apply Z.div_le_mono; klia).
    apply Z.mod_divide in A3 as [ke Hke]; [|klia].
    assert (D2 : a / 8 < XEz (r6of rho) / 8).
    { rewrite Hke. replace (ke * 64) with (ke * 8 * 8) by klia. rewrite Z_div_mult by klia. apply Z.div_lt_upper_bound; klia. }
    unfold SXB, SXE in *. klia.
  - intros z Hz. apply HZ. klia.
  - intros z Hz. apply (outside_all_of_disjoint rho (ss_objs C18e) SXB (SXE (r6of rho) - SXB)); [|rewrite u64_of_lit by klia; klia].
    apply (objs18_clear rho rho SXB (SXE (r6of rho) - SXB) HV H36 H77 H78 H83 Hx1); [intros; reflexivity | intros; reflexivity | exact HF | klia | klia | klia].
Qed.

Inductive out18 : Type := O18a (o : out0) | O18b (o : out1) | O18c (o : out1) (g : word).
Definition out18_ok (o : out18) : Prop := ltac2:(tb__ "0|1|
S38OLo;Vo;Sc2Sd0S35R1A2Lo;SbcSc1S35R1A2Lo;SbcS18Q40M0A1S1Sc1S35R2A2Sd3S1aG0Z0A2SbdS35R2A2SfbR1A4A2Lg;Lo;X38x3").
Definition out18_model (o : out18) : Model := ltac2:(tb__ "0|0|
S38S6aLo;Vo;Sc2ScfS35R1A2Lo;SbcSbdS35R1A2Lo;SbcS18Q40A1SfeSbdS35R2A2R1A2Lg;Lo;X38x3").
Definition out18_W (o : out18) : Z * Z := ltac2:(tb__ "0|0|
S38S5aS6S6A2Lo;Vo;Sc2SceR1A1Lo;SbcScbS35R1A2Lo;SbcS18Q40A1ScbS35R2A2Lg;Lo;X38x3").
Definition out18_tp (o : out18) (tp : list word) : list word := ltac2:(tb__ "0|1|
S38S59S18Q40A1M0A1Lo;Vo;Sc2Vtp;Lo0;SbcSccS35R1Vtp;A3Lo;SbcG0SccS35R2Vtp;A3Lg;Lo;X38x3").

Definition Wok (lo hi : Z) : Prop := ltac2:(tb__ "0|4|
S3S8Vhi;Vlo;A2S1S8Z1000Vlo;A2S1S0S6Vhi;S9Vlo;Z2000M0A2A3S1S8Vhi;S47A2S1S0S5cS78S64S5aS18Q40M1A1M2G2A2S70S6bS35A1M3A1S6cG3A1A3S1aG1Vlo;A2S1aG1G0A2A3S5dA3S1S3S8Vhi;Z10000A2S8Z646000Vlo;A2A2S3S8Vhi;SedA2S8SeeVlo;A2A2A2A2A2A2A2A2").

Lemma place8k_Wok : ltac2:(tb__ "0|2|
S18Q40M0A1Sd3S1aG0Z0A2S35SffR1A4S4cS19G0R2A2M1S9G1Z2000A2A2F_;Fa;").
Proof using HPL HPL10 HPL4 HPL5 HPL6 HPL7 HPL8 HPL9 Hmaps Hres Htop Hxtop Hx H16.
  clear Hsb Hbrk Hbal OKF OKP Hlz HBlim Ha1 Ha2.
  intros a Hpl. pose proof mE_fields as (MR & _).
  pose proof (place_LB_A mE 8192 a init_sp_ok_mE ltac:(rewrite MR; exact Hres) band_mE ltac:(lia) ltac:(reflexivity) Hpl) as (PLB & Pimg & Pband & Ptop & _).
  change (LB_of 8192) with 0x1000 in PLB. rewrite top_mE in Ptop.
  pose proof Hpl as (_ & _ & _ & Pfree). assert (Hn : mmap_n n8w = Z_to_bv 64 8192) by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). rewrite Hn in Pfree.
  right. rewrite Z_to_bv_bv_unsigned. repeat split; try lia. exact Pfree.
Qed.

Lemma out18_Wok : ltac2:(tb__ "0|1|
S38S40R1A1S4cS63S6S6S45R2A1M0A3S60S6S6G0A3A2F_;Fo;").
Proof using HPL HPL10 HPL4 HPL5 HPL6 HPL7 HPL8 HPL9 Hmaps Hres Htop Hxtop Hbrk Hx H16.
  clear OKF OKP Hlz HBlim Hsb Hbal Ha1 Ha2.
  intros o Ho. pose proof mE_fields as (_ & _ & _ & _ & _ & _ & K1 & _).
  assert (GROW : OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.MuslMalloc40Nodes.brk0 mE + 8192 <= alloc_top (m_vmmaps mE) /\ region_free (vm_reserved (m_vmmaps mE) ++ vm_maps (m_vmmaps mE)) (brk0w mE) n3w = true ->
                 Wok (bv_unsigned (brk0w mE)) (bv_unsigned (brk0w mE) + 8192)).
  { intros [A1 A2]. right. unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.MuslMalloc40Nodes.brk0, brk0w in *. rewrite K1 in *. rewrite Z_to_bv_bv_unsigned. rewrite top_mE in A1.
    pose proof (region_free_shrink _ _ _ (vm_brk (m_vmmaps m)) (Z_to_bv 64 8192) A2 ltac:(lia) ltac:(rewrite n3w_val, u64_of_lit by lia; lia)) as A3.

    pose proof (grant_avoids_band _ SHADOW_BAND_LO SHADOW_BAND_HI (vm_brk (m_vmmaps m)) n3w band_mE ltac:(unfold SHADOW_BAND_LO, SHADOW_BAND_HI; lia) A2 ltac:(rewrite n3w_val; lia)) as A4.
    rewrite n3w_val in A4.
    unfold SHADOW_BAND_LO, SHADOW_BAND_HI in *. split; [lia|]. split; [lia|]. split; [exact A1|]. split; [exact A3|]. split; lia. }
  destruct o as [o|o|o g]; cbn [out18_ok out18_W] in Ho |- *.
  - destruct o as [|a]; cbn [out0_ok out0_W fst snd] in Ho |- *; [left; lia|]. exact (place8k_Wok a Ho).
  - destruct o as [| | |a]; cbn [out1_ok out1_W out1_base fst snd] in Ho |- *; try (apply GROW; exact Ho). exact (place8k_Wok a Ho).
  - destruct Ho as [Ho _]. destruct o as [| | |a]; cbn [out1_ok out1_W out1_base fst snd] in Ho |- *; try (apply GROW; exact Ho). exact (place8k_Wok a Ho).
Qed.

Lemma blocks18_maps : ltac2:(tb__ "0|5|
S1cS3aR1A1S0S18Q40M0A1M1S1bR2P24A2Vb7;A3S0G1S1bR3P4dA2Vb8;A3S0G1S1bR4P53A2Vb10;A3S1dS6S88S5aS1dS6A2S5bS1dS6R2R1A4S43A3S4G1G1S4G1G1S1S88S5aG1G1A2S5bG1G1R2R1A4S6cS6bS35A1A1A3S1S8S19G0R2A2M2S19G0S24RaR5A2A2M3A2S1S8S9G3R4A2S9G2S19G0R1A2M4A2A2SaZ0G4A2A2A2A2Ls;A2Lb;A2F_;Fsz;Fe;F_;F_;F_;F_;Frho;").
Proof using HPL HPL4 HPL5 HPL6 HPL7 HPL8 HPL9 Hres Htop Hmaps Ha1 Ha2 Hx H16 Hxtop.
  clear HBlim Hsb Hbrk Hbal OKF OKP Hlz HPL10. intros rho HV H36 H77 H83 e sz Hin. pose proof HV as (H27 & H28 & H29 & H30 & H31 & H32 & H33 & H34 & Hv1).
  pose proof P_facts as (Pal & Pceil & Pfree & PLB & Phi). pose proof RI_range as (R1 & R2 & R3). pose proof RI_val as RV. pose proof SB_val as SB.
  pose proof (urange P) as UP. pose proof (Z.mod_pos_bound (bv_unsigned P) 65536 ltac:(lia)) as MB. unfold alloc_ceiling_hi in Phi. unfold SHADOW_BAND_HI in PLB.
  pose proof (priZ_facts rho HV) as (PR1 & PR2 & PR3 & PR4).
  pose proof (m13_ledger m P b4 b5 b6 b7 b8) as (_ & L2 & _). pose proof (m12_ledger m P b4 b5 b6 b7) as (_ & O2 & _). pose proof (mE_ledger m P b4 b5 b6) as (_ & Q2 & _).
  pose proof mE_fields as (_ & MM & _).
  assert (IN13 : forall e0 s0, In (e0, s0) ((b8, Z_to_bv 64 4096) :: (b7, Z_to_bv 64 4096) :: (b6, Z_to_bv 64 65536) :: (b5, Z_to_bv 64 4096) :: (b4, n9) :: (P, n7)
                                  :: vm_maps (m_vmmaps m)) -> 0 < bv_unsigned s0 -> In (e0, s0) (vm_maps (m_vmmaps mE))).
  { intros e0 s0 Hi Hs. rewrite MM. right. apply maps16_keep; [|exact Hs]. rewrite L2, O2, Q2. exact Hi. }
  rewrite Hmaps in IN13.
  unfold G18, G17, G13b, G12b, G11c in Hin. rewrite !in_app_iff in Hin. cbn [In] in Hin.
  destruct Hin as [[[[[[= <- <-]|[[= <- <-]|[[= <- <-]|[[= <- <-]|[[= <- <-]|[[= <- <-]|[]]]]]]]|[[= <- <-]|[]]]|[[= <- <-]|[]]]|[[= <- <-]|[]]]|[[= <- <-]|[]]]; cbn [eval].
  - exists a1, (Z_to_bv 64 0x10000). rewrite H27. split; [apply IN13; [cbn [In]; tauto | rewrite u64_of_lit by lia; lia]|]. rewrite u64_of_lit by lia. lia.
  - exists a2, (Z_to_bv 64 0x38e000). rewrite H28. split; [apply IN13; [cbn [In]; tauto | rewrite u64_of_lit by lia; lia]|]. rewrite u64_of_lit by lia. lia.
  - exists P, n7. split; [apply IN13; [cbn [In]; tauto | unfold n7; rewrite u64_of_lit by lia; lia]|].
    unfold ri30. cbn [eval]. rewrite H30. unfold alu64, alu. rewrite bv_add_unsigned, Z_to_bv_unsigned. change (bv_wrap 64 137438953472) with (2 ^ 37).
    rewrite bv_wrap_small by (change (bv_modulus 64) with (2 ^ 64); lia). unfold n7. rewrite u64_of_lit by lia. lia.
  - exists (Z_to_bv 64 0x2008fff7000), (Z_to_bv 64 0xdfff0001000). split; [apply IN13; [cbn [In]; tauto | rewrite u64_of_lit by lia; lia]|].
    change (eval rho shRI_base) with (pRI rho). rewrite (Upri rho HV). rewrite !u64_of_lit by lia.
    assert (HX : LIMz (x1 rho) <= 0x10007fff8000 - 1048576 + 0).
    { unfold LIMz. pose proof (Z.mod_pos_bound (x1 rho) 4096 ltac:(lia)).
      assert (x1 rho <= 0x800000000000) by (unfold x1 in *; rewrite Hv1; unfold init_sp_ok, sp_window_lo, sp_window_hi in Htop; lia).
      pose proof (Z.div_le_mono (x1 rho - x1 rho mod 4096) 0x800000000000 8 ltac:(lia) ltac:(lia)). change (0x800000000000 / 8) with 17592186044416 in *. lia. }
    lia.
  - exists b5, (Z_to_bv 64 4096). rewrite H33. split; [apply IN13; [cbn [In]; tauto | rewrite u64_of_lit by lia; lia]|]. rewrite u64_of_lit by lia. lia.
  - exists b6, (Z_to_bv 64 65536). rewrite H34. split; [apply IN13; [cbn [In]; tauto | rewrite u64_of_lit by lia; lia]|]. rewrite u64_of_lit by lia. lia.
  - exists b7, (Z_to_bv 64 4096). rewrite H36. split; [apply IN13; [cbn [In]; tauto | rewrite u64_of_lit by lia; lia]|]. rewrite u64_of_lit by lia. lia.
  - exists b8, (Z_to_bv 64 4096). rewrite H77. split; [apply IN13; [cbn [In]; tauto | rewrite u64_of_lit by lia; lia]|]. rewrite u64_of_lit by lia. lia.
  - exists (Z_to_bv 64 0x7fff7000), (Z_to_bv 64 0x10000000). split; [apply IN13; [cbn [In]; tauto | rewrite u64_of_lit by lia; lia]|].
    unfold LOWPG. rewrite !u64_of_lit by lia. lia.
  - exists b10, (Z_to_bv 64 n17). rewrite H83. split; [rewrite MM; left; reflexivity|]. unfold n17. rewrite u64_of_lit by lia. lia.
Qed.

Lemma clearR18 : ltac2:(tb__ "0|0|
S0S5cSe1S43S120S90S8dA2A2S5dA3"). Proof. clear. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma R18_clear_W : ltac2:(tb__ "0|1|
S1cS6S6S3aR3A1S0S18Q40A1M0S1bR4P24A2Vb7;A3S0G0S1bR5P4dA2Vb8;A3S0G0S1bR6P53A2Vb10;A3S0S6SacR7A1Vx;A3Sa8S20S23R8A1S22S90A1A3S4cR8R7A2S1eS88S1eR1S8dA3S29S28RcR2A2S5bS6S6RbRaA4A2F_;Fo;F_;F_;F_;F_;F_;F_;F_;Fhi;Flo;Frho;").
Proof using HPL HPL4 HPL5 HPL6 HPL7 HPL8 HPL9 Hres Htop Hmaps Ha1 Ha2 Hx H16 Hxtop.
  clear Hsb Hbrk Hbal OKF OKP Hlz HBlim HPL10.
  intros rho lo hi HV H36 H77 H83 Hx1 HF HW o Ho.
  destruct HW as [Hemp|(W1 & W2 & W3 & W4 & W5 & W6)]; [unfold ranges_disjoint; cbn [fst snd]; lia|]. subst hi. unfold TOPz in W3.
  pose proof (objs_clear_e_sound rho G18 (set_objs C18e R18) (Z_to_bv 64 lo) 8192 HF clearR18 ltac:(lia)) as X. rewrite u64_of_lit in X by lia.
  apply X; [right; unfold x1 in Hx1; rewrite Hx1; lia | intros y Hy; lia | | exact Ho].
  intros e sz Hin y Hy. destruct (blocks18_maps rho HV H36 H77 H83 e sz Hin) as (b & s0 & Hm & B1 & B2 & _).
  pose proof (State.region_free_In _ _ _ _ _ (region_free_app_r _ _ _ _ W4) Hm) as OV.
  unfold iv_overlap in OV. rewrite u64_of_lit in OV by lia. rewrite u64_of_lit in OV by lia. apply andb_false_iff in OV.
  destruct OV as [OV|OV]; apply Z.ltb_ge in OV; lia.
Qed.

Lemma TP18_range : ltac2:(tb__ "0|5|
S1cS3aR1A1S0S6SacR2A1Vx;A3S0S6SdZ8S19Q40M0S1bR3P23A2A2A2S19G0Vb6;A2A3S8S9Vx;Z50A2S36R4A1A2S8S9S36R5A1Z10M1A2SeZ2Z2fA2A2S8S9S36R6A1G1A2S9Vx;Z2228cfA2A2S18G0A1M2S88G2R1S3cR8A1A3S1S8Z7fff7000S19G0R2A2M3A2S8S9G3Z1000M4A2S10S9S39G4A2S44S36R9A1A1A2A2A2F_;Fp;F_;F_;F_;F_;F_;F_;Frho;").
Proof using HPL HPL4 HPL5 HPL6 Hmaps Hres Htop Hx H16 Hxtop.
  clear OKF OKP Hlz HBlim Hsb Hbrk Hbal HPL10.
  intros rho HV Hx1 V35 H1 H2 H3 p Hp. pose proof (arith18 _ H1 H2 H3) as AR.
  destruct AR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & A14 & _ & _ & A17 & A18 & _ & _ & _ & A22 & A23 & _).
  unfold TP18 in Hp. destruct (nE (r6of rho)) as [|k] eqn:EN.
  - cbn [Nat.eqb] in Hp. pose proof (TP17_le rho HV Hx1 V35 p Hp). klia.
  - cbn [Nat.eqb] in Hp. specialize (A23 ltac:(discriminate)). apply in_app_iff in Hp as [Hp|Hp].
    + apply In_pages_rev in Hp as (k' & Hk' & ->). unfold pageZ. apply Nat2Z.inj_lt in Hk'. rewrite Nat2Z.inj_sub in Hk' by lia. change (Z.of_nat 1) with 1 in Hk'.
      rewrite u64_of_lit by klia. klia.
    + apply In_enspage_inv in Hp as [->|Hp']; [rewrite u64_of_lit by klia; klia|]. pose proof (TP17_le rho HV Hx1 V35 p Hp'). klia.
Qed.

Lemma TP18_out18 : ltac2:(tb__ "0|3|
S1cS38S3aR2A1S0S6SacR3A1Vx;A3S0S6SdZ8S19Q40M0S1bR4P23A2A2A2S19G0Vb6;A2A3S8S9Vx;Z50A2S36R5A1A2S8S9S36R6A1Z10M1A2SeZ2Z2fA2A2S8S9S36R7A1G1A2S9Vx;Z2228cfA2A2S40R7A1S0S59S18G0A1A1S57R8S3cR9A1M2A2G2A3F_;F_;F_;F_;F_;F_;F_;Fo;Frho;").
Proof using HPL HPL4 HPL5 HPL6 HPL7 HPL8 HPL9 Hmaps Hres Htop Hx H16 Hbrk Hxtop.
  clear OKF OKP Hlz HBlim HPL10 Hsb Hbal.
  intros rho o HV Hx1 V35 H1 H2 H3 Ho.
  assert (GEN : forall o1, out1_ok mE o1 -> out1_tp mE o1 (TP18 rho) = TP18 rho).
  { intros o1 Ho1. destruct o1; cbn [out1_tp out1_ok] in Ho1 |- *; try reflexivity. unfold tp20. destruct Ho1 as [A1 A2].

    pose proof (grant_avoids_band _ SHADOW_BAND_LO SHADOW_BAND_HI (brk0w mE) n3w band_mE ltac:(unfold SHADOW_BAND_LO, SHADOW_BAND_HI; lia) A2 ltac:(rewrite n3w_val; lia)) as A4.
    rewrite n3w_val in A4.
    pose proof mE_fields as (_ & _ & _ & _ & _ & _ & K1 & _). unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.MuslMalloc40Nodes.brk0, brk0w in *. rewrite K1 in *. unfold SHADOW_BAND_LO, SHADOW_BAND_HI in A4.
    apply tp_forget_id. intros p Hp. pose proof (TP18_range rho HV Hx1 V35 H1 H2 H3 p Hp) as [R1 R2]. klia. }
  destruct o as [o0|o1|o1 g]; cbn [out18_tp out18_ok out18_W] in Ho |- *; [reflexivity | exact (GEN o1 Ho) | exact (GEN o1 (proj1 Ho))].
Qed.

Lemma R18_clear_band : ltac2:(tb__ "0|1|
S1cS6S6S3aR3A1S0S18Q40A1M0S1bR4P24A2Vb7;A3S0G0S1bR5P4dA2Vb8;A3S0G0S1bR6P4eA2Vb9;A3S0G0S1bR7P53A2Vb10;A3S0S6SacR8A1Vx;A3Sa8S20S23R9A1S22S90A1A3S8SadVx;A1R9A2S8Z0R9A2S8S9RbRaA2SdeA2S1eS88S1eR1S8dA3S29S28RfR2A2S5bS6S6ReS9ReRdA2A4A2F_;Fo;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Flen;Flo;Frho;").
Proof using HPL HPL10 HPL4 HPL5 HPL6 HPL7 HPL8 HPL9 Ha1 Ha2 Hmaps Hres Htop Hx H16 Hxtop.
  clear Hsb Hbrk Hbal OKF OKP Hlz HBlim.
  intros rho lo len HV H36 H77 H78 H83 Hx1 HF Hlo Hlen Hhi o Ho.
  pose proof CAx as CA. cbv zeta in CA. destruct CA as (Ct & CHPlo & CPEhi & CPEHP & CHPq & _).
  pose proof (objs_clear_e_sound rho G18 (set_objs C18e R18) (Z_to_bv 64 lo) len HF clearR18 Hlen) as X. rewrite u64_of_lit in X by (unfold kHighMemBeg in *; lia).
  apply X; [unfold kHighMemBeg in *; left; lia | intros y Hy; unfold kHighMemBeg in *; lia | | exact Ho].
  intros e sz Hin y Hy. destruct (blocks18 rho HV H36 H77 H78 H83 Hx1 e sz Hin); unfold kHighMemBeg in *; lia.
Qed.

Lemma R18_clear_lowb : ltac2:(tb__ "0|3|
S1cS18Q40M0A1M1S3aR2A1S0G1S1bR3P24A2Vb7;A3S0G1S1bR4P4dA2Vb8;A3S0G1S1bR5P4eA2Vb9;A3S0G1S1bR6P53A2Vb10;A3S0S6SacR7A1Vx;A3Sa8S20S23R8A1S22S90A1A3S42R9S19G0R8A2A2S1eS88S1eR1S8dA3S29S28RcR2A2S5bS6S6S19G0RbA2M2S9G2Z1A2A4A2F_;Fo;F_;F_;F_;F_;F_;F_;F_;F_;Fa;Frho;").
Proof using HPL HPL10 HPL4 HPL5 HPL6 HPL7 HPL8 HPL9 Ha1 Ha2 Hmaps Hres Htop Hx H16 Hxtop.
  clear Hsb Hbrk Hbal OKF OKP Hlz HBlim.
  intros rho a HV H36 H77 H78 H83 Hx1 HF Hlb o Ho. pose proof Hlb as (Ha & N1 & N2).
  pose proof CAx as CA. cbv zeta in CA. destruct CA as (Ct & CHPlo & CPEhi & CPEHP & CHPq & _).
  pose proof q12x_hi as QHI.
  pose proof (objs_clear_e_sound rho G18 (set_objs C18e R18) a 1 HF clearR18 ltac:(lia)) as X.
  apply X; [unfold SHADOW_BAND_LO, kHighMemBeg in *; left; lia | intros y Hy; unfold SHADOW_BAND_LO in *; lia | | exact Ho].
  intros e sz Hin y Hy. replace y with (bv_unsigned a) by lia. exact (blocks18_low rho HV H36 H77 H78 H83 Hx1 e sz Hin (bv_unsigned a) Hlb).
Qed.

Lemma brk0_mE : ltac2:(tb__ "0|1|
S1S8Z646000SfcS35A1M0A2S1S8G0Z80646000A2S0S18Q40A1SfdS35A1S6eS6bVm;A1A1A3A2A2").
Proof using Hbrk Hx H16 Hxtop.
  clear -Hbrk Hx H16 Hxtop. pose proof mE_fields as (_ & _ & _ & _ & _ & _ & K1 & _). unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.MuslMalloc40Nodes.brk0, brk0w. rewrite K1. repeat split; lia.
Qed.

Lemma s5_in_out1 : ltac2:(tb__ "0|2|
SbcS88S5aS18Q40M0A1M1G1A2S5bG1G1S1aG0Z2008fff7000A2S1aG0Zdfff0001000A2A4S6cS6bSbdS35R1A2A1A1A3Fo;").
Proof using HPL HPL4 HPL5 HPL6 HPL7 HPL8 HPL9 Hmaps Hres Htop Hbrk Hx H16 Hxtop.
  clear OKF OKP Hlz HBlim Ha1 Ha2 HPL10 Hsb Hbal.
  intros o. pose proof hs_map_mE as H5. pose proof brk0_mE as (Hlo' & Hhi' & K1).
  assert (MG : In (Z_to_bv 64 0x2008fff7000, Z_to_bv 64 0xdfff0001000) (vm_maps (m_vmmaps (mg mE)))).
  { rewrite (mg_vmmaps mE Hlo' Hhi'). cbn [vm_maps]. right. exact H5. }
  destruct o as [| | |a]; cbn [out1_model].
  - exact MG.
  - unfold mg_ok. rewrite m_vmmaps_vm_forget_range, m_vmmaps_with_vmmaps. unfold mmap_fixed_ok_vm. cbn [vm_maps]. exact MG.
  - unfold mg_dead. rewrite m_vmmaps_vm_forget_range, m_vmmaps_with_vmmaps. unfold mmap_fixed_dead_vm. cbn [vm_maps].
    apply (in_maps_subtract_of' _ _ _ _ _ _ MG). unfold iv_subtract. rewrite !u64_of_lit by lia.
    unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.MuslMalloc40Nodes.brk0, pgw in *. rewrite K1 in *. rewrite (u64_of_lit 4096) by lia.
    replace (2201439137792 <? bv_unsigned (vm_brk (m_vmmaps m))) with false by (symmetry; apply Z.ltb_ge; lia).
    replace (bv_unsigned (vm_brk (m_vmmaps m)) + 4096 <? 2201439137792 + 15392894357504) with true by (symmetry; apply Z.ltb_lt; lia).
    cbn [app]. left. rewrite Z.max_l by lia. reflexivity.
  - unfold mf_exp, mprotect_model_next. rewrite m_vmmaps_with_vmmaps. cbn [vm_maps]. rewrite mf_res_vmmaps. unfold mmap_none_vm. cbn [vm_maps]. right. exact H5.
Qed.

Lemma res_out1 : ltac2:(tb__ "0|2|
SbcS1S0S59S5aS18Q40A1M0G0A2A1S70S6bSbdS35R1A2A1M1A1S10cS69A1A3S0G0S76G1A1S76S6bS35A1A1A3A2Fo;").
Proof using Hres Hbrk Hx H16 Hxtop.
  clear -Hres Hbrk Hx H16 Hxtop. intros o. pose proof mE_fields as (MR & _). pose proof brk0_mE as (Hlo' & Hhi' & K1). rewrite <- Hres, <- MR.
  destruct o; cbn [out1_model]; unfold mg_ok, mg_dead, mf_exp, mprotect_model_next;
    rewrite ?m_vmmaps_vm_forget_range, ?m_vmmaps_with_vmmaps, ?mf_res_vmmaps, ?(mg_vmmaps mE Hlo' Hhi'); cbn; split; reflexivity.
Qed.
Lemma top_out1 : ltac2:(tb__ "0|0|
SbcS0S6S72S6bSbdS35R1A2A1A1S47A3Fo;").
Proof using Hres Hbrk Hxtop Hx H16. clear -Hres Hbrk Hxtop Hx H16. intros o. pose proof (res_out1 o) as [_ E]. rewrite <- top_mE. unfold alloc_top. rewrite E. reflexivity. Qed.

Lemma grp_facts : ltac2:(tb__ "0|6|
SbcS18Q40M0A1M1Sd3S1aG0Z0M2A2SbdS35R2A2SfbR1A4S1S3S8S9S19G0R2A2M3Z1000A2M4Z2008fff7000A2S8SdeG3A2A2S1S3S8G4Z10000A2S8Z646000G3A2A2S1S8G4S47A2S1SaG2G3A2S0S5cS78S64S5aG1G1A2S70S6bSbdS35R3A2A1M5A1S6cG5A1A3R2SfbA3S5dA3A2A2A2A2F_;Fg;Fo;").
Proof using HPL HPL4 HPL5 HPL6 HPL7 HPL8 HPL9 Hmaps Hres Htop Hbrk Hxtop Hx H16.
  clear OKF OKP Hlz HBlim Ha1 Ha2 HPL10 Hsb Hbal.
  intros o g (Pal & Ppos & Pceil & Pfree).
  assert (HnZ : mmap_nZ pgw = 4096) by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). assert (Hn : mmap_n pgw = pgw) by (unfold mmap_n; rewrite HnZ; reflexivity). rewrite Hn in Pfree.
  rewrite HnZ, top_out1 in Pceil. assert (Upg : bv_unsigned pgw = 4096) by (unfold pgw; apply u64_of_lit; lia).
  pose proof (State.region_free_In _ _ _ _ _ (region_free_app_r _ _ _ _ Pfree) (s5_in_out1 o)) as OV.
  unfold iv_overlap in OV. rewrite Upg in OV. rewrite !u64_of_lit in OV by lia. apply andb_false_iff in OV. unfold kHighMemBeg.
  pose proof (res_out1 o) as [RES _].
  assert (IB : band_covered (vm_reserved (m_vmmaps (out1_model mE o)) ++ vm_maps (m_vmmaps (out1_model mE o))) IMG_BAND_LO IMG_BAND_HI).
  { apply img_band_covered. rewrite RES. apply incl_appl. apply incl_refl. }
  pose proof (grant_avoids_band _ IMG_BAND_LO IMG_BAND_HI g pgw IB ltac:(unfold IMG_BAND_LO, IMG_BAND_HI; lia) Pfree ltac:(rewrite Upg; lia)) as IMG.
  rewrite Upg in IMG. unfold IMG_BAND_LO, IMG_BAND_HI in IMG.
  split; [destruct OV as [OV|OV]; apply Z.ltb_ge in OV; lia|]. split; [exact IMG|]. split; [exact Pceil|]. split; [exact Ppos | exact Pfree].
Qed.

Lemma join18 : ltac2:(tb__ "0|0|
S6aS6S84SebS1cS59S18Q40A1A1Sd8S0S5cS85R5S9eR4A3S5dA3S0S5cSecR5P9cA2S5dA3Sa4S69Sa7R9R8A2R7R5R4R3A6Sa4S69Sa7RaR9A2S91Se9R6R7A2R5R4A6F_;F_;F_;Fw;Ftp;Frho;Fsx;FU;FBx;Fmo;").
Proof.
  clear. intros mo Bx U sx rho tp w He Hid Hsp. destruct K18_eq as [M1 M2].
  pose proof (SPA_entails segsA (KxA mo Bx) 156%positive U J18 sx rho tp w He Hid (stableA_KxA segsA _ mo Bx) Hsp) as H1.
  pose proof (SPA_merge segsA (KxA mo Bx) _ J18 42 K18a tp w M1 H1) as H2.
  pose proof (SPA_merge segsA (KxA mo Bx) _ (ax_setS J18 K18a) 42 K18S tp w M2 H2) as H3. exact H3.
Qed.

Lemma maps_mE_sub_out1 : ltac2:(tb__ "0|5|
SbcS18Q40M0A1M1G1Sc1S35R3A2S88S5aG1G1A2M2S5bG1G1R3R2A4S6cS6bS35A1A1A3SaZ0S19G0R3A2A2Se5S5bG1G1R5R4A4A1S4G1G1S4G1G1S1S88G2S5bG1G1R2R1A4S6cS6bSbdS35R9A2A1A1A3S1S8S19G0R2A2M3S19G0R8A2M4A2S8S9G4S19G0R7A2A2S9G3S19G0R1A2A2A2A2A2Ls';A2Lb';A2F_;F_;F_;F_;Fsz;Fb;Fo;").
Proof using Hbrk Hx H16 Hxtop.
  clear -Hbrk x b10 Hx H16 Hxtop.
  intros o b sz Ho Hin Hsz Hwf. pose proof brk0_mE as (Hlo' & Hhi' & K1).
  assert (SELF : forall l, In (b, sz) l -> exists b' s', In (b', s') l /\ bv_unsigned b' <= bv_unsigned b /\ bv_unsigned b + bv_unsigned sz <= bv_unsigned b' + bv_unsigned s')
    by (intros l Hl; exists b, sz; split; [exact Hl | lia]).
  assert (MG : In (b, sz) (vm_maps (m_vmmaps (mg mE)))) by (rewrite (mg_vmmaps mE Hlo' Hhi'); cbn [vm_maps]; right; exact Hin).
  destruct o as [| | |a]; cbn [out1_model out1_ok] in Ho |- *.
  - apply SELF. exact MG.
  - apply SELF. unfold mg_ok. rewrite m_vmmaps_vm_forget_range, m_vmmaps_with_vmmaps. unfold mmap_fixed_ok_vm. cbn [vm_maps]. exact MG.
  - unfold mg_dead. rewrite m_vmmaps_vm_forget_range, m_vmmaps_with_vmmaps. unfold mmap_fixed_dead_vm. cbn [vm_maps].
    destruct Ho as [A1 A2]. pose proof (State.region_free_In _ _ _ _ _ (region_free_app_r _ _ _ _ A2) Hin) as OV.
    unfold iv_overlap in OV. rewrite n3w_val in OV. apply andb_false_iff in OV.
    unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.MuslMalloc40Nodes.brk0, pgw in *. rewrite K1 in *.
    destruct (iv_subtract_keeps b sz (bv_unsigned (vm_brk (m_vmmaps m))) (bv_unsigned (vm_brk (m_vmmaps m)) + bv_unsigned (Z_to_bv 64 4096))
                (bv_unsigned b) (bv_unsigned b + bv_unsigned sz) Hwf ltac:(rewrite u64_of_lit by lia; lia) ltac:(lia) ltac:(lia) ltac:(lia)) as ([rb rs] & Hr & Q1 & Q2).
    + rewrite u64_of_lit by lia. destruct OV as [OV|OV]; apply Z.ltb_ge in OV; lia.
    + exists rb, rs. split; [eapply in_maps_subtract_of'; [exact MG | exact Hr]|]. cbn [fst snd] in Q1, Q2. lia.
  - apply SELF. unfold mf_exp, mprotect_model_next. rewrite m_vmmaps_with_vmmaps. cbn [vm_maps]. rewrite mf_res_vmmaps. unfold mmap_none_vm. cbn [vm_maps]. right. exact Hin.
Qed.

Lemma grp_clear_R18 : ltac2:(tb__ "0|3|
S1cSbcS18Q40M0A1M1S3aR3A1S0G1S1bR4P24A2Vb7;A3S0G1S1bR5P4dA2Vb8;A3S0G1S1bR6P53A2Vb10;A3S0S6SacR7A1Vx;A3Se4S6cS6bS35A1A1A1Sa8S20S23R9A1S22S90A1A3Sc1S35R9A2Sd3S1aG0Z0A2SbdS35RaA2SfbR9A4S1eS88S1eR1S8dA3S29S28ReR2A2S5bS6S6S19G0RcA2M2S9G2Z1000A2A4A2F_;FoR;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fg;Fo;Frho;").
Proof using HPL HPL4 HPL5 HPL6 HPL7 HPL8 HPL9 Hmaps Hres Htop Hbrk Hxtop Ha1 Ha2 Hx H16.
  clear OKF OKP Hlz HBlim HPL10 Hsb Hbal.
  intros rho o g HV H36 H77 H83 Hx1 MWF HF Ho Hpl oR HoR. pose proof (grp_facts o g Hpl) as (G1 & G2 & G3 & G4 & G5). pose proof Hpl as (Pal & Ppos & Pceil & Pfree).
  assert (Upg : bv_unsigned pgw = 4096) by (unfold pgw; apply u64_of_lit; lia). unfold TOPz in G3.
  apply (objs_clear_e_sound rho G18 (set_objs C18e R18) g 4096 HF clearR18 ltac:(lia)); [right; unfold x1 in Hx1; rewrite Hx1; lia | intros y Hy; lia | | exact HoR].
  intros e sz Hin y Hy. destruct (blocks18_maps rho HV H36 H77 H83 e sz Hin) as (b & s0 & Hm & B1 & B2 & B3).
  destruct (maps_mE_sub_out1 o b s0 Ho Hm B3 (MWF _ Hm)) as (b' & s' & Hm' & C1 & C2).
  pose proof (State.region_free_In _ _ _ _ _ (region_free_app_r _ _ _ _ G5) Hm') as OV.
  unfold iv_overlap in OV. rewrite Upg in OV. apply andb_false_iff in OV. destruct OV as [OV|OV]; apply Z.ltb_ge in OV; lia.
Qed.

Definition band (z : Z) : Prop := ltac2:(tb__ "0|0|
S1S8SadVx;A1Vz;A2SaVz;SdeA2A2").

Definition grp_out (o : out18) (z : Z) : Prop := ltac2:(tb__ "0|2|
S38OLo;Vo;Sc2S5Lo0;SbcS5Lo0;SbcS18Q40M0A1S2S1S8S19G0R1A2M1Vz;A2SaVz;S9G1Z1000A2A2A2A1Lg;Lo0;X38x3").
Lemma band_bandw : ltac2:(tb__ "0|0|
S6S3eR1A1S4bR2A1F_;Fz;").
Proof using Hx H16 Hxtop. clear -x Hx H16 Hxtop. intros z Hz. unfold band, bandw in *. pose proof CAx as CA. cbv zeta in CA. destruct CA as (_ & CHPlo & _ & _ & CHPq & _).
  pose proof q12x_hi. unfold SHADOW_BAND_LO, SHADOW_BAND_HI, kHighMemBeg in *. lia. Qed.
Lemma lowb_bandw : ltac2:(tb__ "0|0|
S1cS6S42R2R1A2S4bR2A1F_;Fz;Frho;").
Proof using Hx H16 Hxtop. clear -x Hx H16 Hxtop. intros rho z (Hz & _ & _). unfold bandw in *. pose proof q12x_hi.
  unfold SHADOW_BAND_LO, SHADOW_BAND_HI, kHighMemBeg in *. lia. Qed.

Definition Q18post (mo : Model) (Bx : Z) (rho' : valuation) (tp : list word) (ex : Z -> Prop) : assn := ltac2:(tb__ "0|4|
Sd8S4S1cS1cS1S7Sf8R1P56A2S0S18Q40M0A1M1S1bR3R2A2S1bVrho';R2A2A3F_;Fi;S1S7S0S59S18Q8A1M2A1S26R2R1A2S26Vrho';R1A2A3Fl;S1G1S3S3eS19G0R1A2M3A1S3S8Vx;G3A2S1S4bG3A1Vex;G3A1A2A2A2S0S61G2A1S1fR3R2A2S1fVrho';R2A2A3F_;Fa;Sa4S69Sa7Vmo;VBx;A2S91R1Vtp;R2A6A2A2A2Lrho4;A2Lw;").

Lemma I18_nexts : ltac2:(tb__ "0|2|
S1S0S7S27S80S9bA1A1P9cM0A3S1S0S7S27S80S9cA1A1G0A3S1S0S7S27S80S9dA1A1G0A3S1S0S7S27S80S92A1A1G0A3S1S0S7S27S80S93A1A1G0A3S1S0S7S27S80S94A1A1G0A3S1S0S5eS66S1eS2bS80S9fA1A1A2U31A3S1S0S5eS66S1eS2bS80Sa0A1A1A2U32M1A3S0S5eS66S1eS2bSa1A1A2G1A3A2A2A2A2A2A2A2A2").
Proof. clear. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Lemma after18a : ltac2:(tb__ "0|0|
S6aS6S1cS59S18Q40A1A1Sa8S20S23R2A1S22S90A1A3SdaS69Vok;Sa4S69Sa7R5R4A2S92R3R2A5S46R5R4R3R2S6S5L_;A5A4F_;Ftp;Frho';FBx;Fmo;").
Proof using OKF Hx H16 Hxtop.
  clear -ok OKF x Hx H16 Hxtop. intros mo Bx rho' tp HF. destruct I18_nexts as (Na & _ & _ & Ma & _).
  eapply (@triple_conseq segsA ok (SPA segsA (KxA mo Bx) I18af rho' tp)); [intros w Hw | intros w Hw; exact Hw |].
  { rewrite <- (proj1 I18f_eq). unfold refact18. apply SPA_refacts; [exact Hw | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc |].
    intros HF'. apply Forall_app. split; [exact HF' | exact HF]. }
  eapply triple_conseq; [intros w Hw; exact Hw | |].
  2:{ apply triple1_triple. eapply sym_run_soundA; [exact run18a | apply OKFx; exact OKF | reflexivity | apply stableA_KxA]. }
  intros w Hw. rewrite Na in Hw. apply (proj1 (LQA1 _ _ _ _ _ w)) in Hw as (rho2 & Hag & Hsp). pose proof Hag as (V2 & L2 & R2).
  exists (rho_sub rho2 (sJ18 L18a)). destruct sJ18_id as (IDa & _). pose proof (rho_sub_agree (sJ18 L18a) 156%positive rho2 IDa) as (V3 & L3 & R3).
  split; [|split; [|split]].
  - intros i Hi. rewrite <- (V3 i) by lia. symmetry. apply V2. lia.
  - intros l. rewrite <- (L3 l). symmetry. apply L2.
  - intros a Ha. rewrite <- (R3 a). symmetry. apply R2.
  - apply (join18 mo Bx L18a); [exact entJ18a | exact IDa | exact Hsp].
Qed.

Lemma after18b : ltac2:(tb__ "0|4|
S6aS6S1cS59S18Q40M0A1A1S6Sa8S20S23R3A1S22S90A1A3S0S6S19G0S1bR4P94A2A2R2A3S8S9R3Z2000M1A2Vx;A2S6S3eR1A1S2S1S8S9R6Z1000A2M2R2A2SaR2S9R6G1A2M3A2A2A1F_;Fz;SdaS69Vok;Sa4S69Sa7R9R8A2S93R7R6A5S46R9R8R7R6S6S2S1S8G2R1A2SaR1G3A2A2A1Lz;A5A4F_;F_;F_;F_;Fnb;Ftp;Frho';FBx;Fmo;").
Proof using OKF Hx H16 Hxtop.
  clear -ok OKF x Hx H16 Hxtop. intros mo Bx rho' tp nb HF U148 Hnb Hband. destruct I18_nexts as (_ & Nb & _ & _ & Mb & _ & LENb & _).
  eapply (@triple_conseq segsA ok (SPA segsA (KxA mo Bx) I18bf rho' tp)); [intros w Hw | intros w Hw; exact Hw |].
  { rewrite <- (proj1 (proj2 I18f_eq)). unfold refact18. apply SPA_refacts; [exact Hw | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc |].
    intros HF'. apply Forall_app. split; [exact HF' | exact HF]. }
  eapply triple_conseq; [intros w Hw; exact Hw | |].
  2:{ apply triple1_triple. eapply sym_run_soundA; [exact run18b | apply OKFx; exact OKF | reflexivity | apply stableA_KxA]. }
  intros [tr [ms md]] Hw. rewrite Nb in Hw. apply (proj1 (LQA1 _ _ _ _ _ _)) in Hw as (rho2 & Hag & Hsp). pose proof Hag as (V2 & L2 & R2).

  destruct T18b_facts as (MV & SMV & _ & SPL & EU & EO).
  pose proof (SPA_move_lastX (KxA mo Bx) rho2 L18b 14 tp _ ltac:(rewrite LENb; lia) ltac:(rewrite MV; exact SMV) Hsp) as H1. rewrite MV in H1.
  pose proof (SPA_unobj segsA (KxA mo Bx) rho2 (ax_setS L18b T18b) (ss_objs (ax_S U18b)) [oarea18b] tp tr ms md SPL H1 ltac:(intros X; exact X)) as H2.
  cbv zeta in H2. rewrite ax_S_ax_setS, ax_setS_ax_setS, EU in H2.
  set (rho3 := rho_absorb rho2 [oarea18b] (vms md tp ms)) in *.
  exists (rho_sub rho3 (sJ18 U18b)). destruct sJ18_id as (_ & IDb & _). pose proof (rho_sub_agree (sJ18 U18b) 156%positive rho3 IDb) as (V3 & L3 & R3).
  split; [|split; [|split]].
  - intros i Hi. rewrite <- (V3 i) by lia. unfold rho3. rewrite rw_absorb. symmetry. apply V2. lia.
  - intros l. rewrite <- (L3 l). unfold rho3. rewrite rl_absorb. symmetry. apply L2.
  - intros a Ha. rewrite <- (R3 a). unfold rho3. rewrite rm_absorb_outside; [symmetry; apply R2|].
    intros (o & [<-|[]] & Hr). rewrite EO in Hr. unfold obj_range, obj_lo_of, obj_hi_of, soff in Hr. cbn [ob_base ob_lo ob_hi fst snd] in Hr.
    assert (R148 : rw rho2 148%positive = rw rho' 148%positive) by (symmetry; apply V2; lia).
    rewrite (U_add_lit rho2 (SVar 148%positive) 4096) in Hr by (cbn [eval]; rewrite ?R148, ?U148; lia). cbn [eval] in Hr. rewrite R148, U148 in Hr.
    replace (bv_signed (Z_to_bv 64 0)) with 0 in Hr by reflexivity. replace (bv_signed (Z_to_bv 64 4096)) with 4096 in Hr by reflexivity.
    destruct Ha as [Ha|[Ha|[_ Hex]]]; [exact (Hband _ Ha ltac:(lia)) | lia | exact (Hex ltac:(lia))].
  - apply (join18 mo Bx U18b); [exact entJ18b | exact IDb | exact H2].
Qed.

Lemma after18c : ltac2:(tb__ "0|5|
S6aS6S1cS59S18Q40M0A1A1S6S6Sa8S20S23R4A1S22S90A1A3S0S6S19G0S1bR5P94A2A2R3A3S8S9R4Z2000M1A2Vx;A2S0S6S19G0S1bR7P95A2A2R4A3S8S9R5Z1000M2A2Vx;A2S6S3eR1A1M3S2S1S8S9R9G2A2M4R2A2SaR2S9R9G1A2A2A2A1F_;Fz;S6G3S2S1S8R9R2A2SaR2G4A2A2A1F_;Fz;SdaS69Vok;Sa4S69Sa7RdRcA2S94RbRaA5S46RdRcRbRaS6S1S2S1S8S9RaG2A2R1A2SaR1S9RaG1A2A2A2A1S2S1S8R9R1A2SaR1G4A2A2A1A2Lz;A5A4F_;F_;F_;F_;F_;F_;F_;Fng;Fnb;Ftp;Frho';FBx;Fmo;").
Proof using OKF Hx H16 Hxtop.
  clear -ok OKF x Hx H16 Hxtop. intros mo Bx rho' tp nb ng HF U148 Hnb U149 Hng Hb1 Hb2. destruct I18_nexts as (_ & _ & Nc & _ & _ & Mc & _ & LENc & LENc1).
  eapply (@triple_conseq segsA ok (SPA segsA (KxA mo Bx) I18cf rho' tp)); [intros w Hw | intros w Hw; exact Hw |].
  { rewrite <- (proj2 (proj2 I18f_eq)). unfold refact18. apply SPA_refacts; [exact Hw | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc |].
    intros HF'. apply Forall_app. split; [exact HF' | exact HF]. }
  eapply triple_conseq; [intros w Hw; exact Hw | |].
  2:{ apply triple1_triple. eapply sym_run_soundA; [exact run18c | apply OKFx; exact OKF | reflexivity | apply stableA_KxA]. }
  intros [tr [ms md]] Hw. rewrite Nc in Hw. apply (proj1 (LQA1 _ _ _ _ _ _)) in Hw as (rho2 & Hag & Hsp). pose proof Hag as (V2 & L2 & R2).
  destruct T18c_facts as (MV1 & SMV1 & _ & MV2 & SMV2 & _ & SPL & EU & EOa & EOb & EOl & EOh).
  pose proof (SPA_move_lastX (KxA mo Bx) rho2 L18c 14 tp _ ltac:(rewrite LENc; lia) ltac:(rewrite MV1; exact SMV1) Hsp) as H1. rewrite MV1 in H1.
  pose proof (SPA_move_lastX (KxA mo Bx) rho2 (ax_setS L18c T18c1) 14 tp _ ltac:(cbn [ax_S ax_setS]; rewrite LENc1; lia) ltac:(cbn [ax_S ax_setS]; rewrite MV2; exact SMV2) H1) as H1'.
  cbn [ax_S ax_setS] in H1'. rewrite MV2, ax_setS_ax_setS in H1'.
  pose proof (SPA_unobj segsA (KxA mo Bx) rho2 (ax_setS L18c T18c) (ss_objs (ax_S U18c)) [oarea18c; ogrp18c] tp tr ms md SPL H1' ltac:(intros X; exact X)) as H2.
  cbv zeta in H2. rewrite ax_S_ax_setS, ax_setS_ax_setS, EU in H2.
  set (rho3 := rho_absorb rho2 [oarea18c; ogrp18c] (vms md tp ms)) in *.
  exists (rho_sub rho3 (sJ18 U18c)). destruct sJ18_id as (_ & _ & IDc). pose proof (rho_sub_agree (sJ18 U18c) 156%positive rho3 IDc) as (V3 & L3 & R3).
  split; [|split; [|split]].
  - intros i Hi. rewrite <- (V3 i) by lia. unfold rho3. rewrite rw_absorb. symmetry. apply V2. lia.
  - intros l. rewrite <- (L3 l). unfold rho3. rewrite rl_absorb. symmetry. apply L2.
  - intros a Ha. rewrite <- (R3 a). unfold rho3. rewrite rm_absorb_outside; [symmetry; apply R2|].
    intros (o & [<-|[<-|[]]] & Hr).
    + rewrite EOa in Hr. unfold obj_range, obj_lo_of, obj_hi_of, soff in Hr. cbn [ob_base ob_lo ob_hi fst snd] in Hr.
      assert (R148 : rw rho2 148%positive = rw rho' 148%positive) by (symmetry; apply V2; lia).
      rewrite (U_add_lit rho2 (SVar 148%positive) 4096) in Hr by (cbn [eval]; rewrite ?R148, ?U148; lia). cbn [eval] in Hr. rewrite R148, U148 in Hr.
      replace (bv_signed (Z_to_bv 64 0)) with 0 in Hr by reflexivity. replace (bv_signed (Z_to_bv 64 4096)) with 4096 in Hr by reflexivity.
      destruct Ha as [Ha|[Ha|[_ [Hex _]]]]; [exact (Hb1 _ Ha ltac:(lia)) | lia | exact (Hex ltac:(lia))].
    + unfold obj_range, obj_lo_of, obj_hi_of, soff in Hr. rewrite EOl, EOh, EOb in Hr. cbn [eval fst snd] in Hr.
      rewrite <- (V2 149%positive) in Hr by lia. rewrite U149 in Hr.
      replace (bv_signed (Z_to_bv 64 0)) with 0 in Hr by reflexivity. replace (bv_signed (Z_to_bv 64 4096)) with 4096 in Hr by reflexivity.
      destruct Ha as [Ha|[Ha|[_ [_ Hex]]]]; [exact (Hb2 _ Ha ltac:(lia)) | lia | exact (Hex ltac:(lia))].
  - apply (join18 mo Bx U18c); [exact entJ18c | exact IDc | exact H2].
Qed.

Lemma etriple_pre_fact : ltac2:(tb__ "0|1|
SdbSd8OF_;OSd8R4R1A1R3F_;Fw;R2Sd9S69R5R4A3M0F_;G0F_;F_;FF;FQ;FP;").
Proof. clear. intros P Q F H1 H2 w Hw. exact (H2 (H1 w Hw) w Hw). Qed.

Lemma eafter18a : ltac2:(tb__ "0|0|
S6aS6S1cS59S18Q40A1A1Sa8S20S23R2A1S22S90A1A3Sd9S69Sa4S69Sa7R5R4A2S92R3R2A5S46R5R4R3R2S6S5L_;A5A3F_;Ftp;Frho';FBx;Fmo;").
Proof.
  clear -x Hx H16 Hxtop. intros mo Bx rho' tp HF. destruct I18_nexts as (Na & _ & _ & Ma & _).
  eapply (@etriple_conseq segsA (SPA segsA (KxA mo Bx) I18af rho' tp)); [intros w Hw | intros w Hw; exact Hw |].
  { rewrite <- (proj1 I18f_eq). unfold refact18. apply SPA_refacts; [exact Hw | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc |].
    intros HF'. apply Forall_app. split; [exact HF' | exact HF]. }
  eapply etriple_conseq; [intros w Hw; exact Hw | |].
  2:{ eapply sym_run_etripleA; [reflexivity | apply stableA_KxA | exact run18a]. }
  intros w Hw. rewrite Na in Hw. apply (proj1 (LQA1 _ _ _ _ _ w)) in Hw as (rho2 & Hag & Hsp). pose proof Hag as (V2 & L2 & R2).
  exists (rho_sub rho2 (sJ18 L18a)). destruct sJ18_id as (IDa & _). pose proof (rho_sub_agree (sJ18 L18a) 156%positive rho2 IDa) as (V3 & L3 & R3).
  split; [|split; [|split]].
  - intros i Hi. rewrite <- (V3 i) by lia. symmetry. apply V2. lia.
  - intros l. rewrite <- (L3 l). symmetry. apply L2.
  - intros a Ha. rewrite <- (R3 a). symmetry. apply R2.
  - apply (join18 mo Bx L18a); [exact entJ18a | exact IDa | exact Hsp].
Qed.

Lemma eafter18b : ltac2:(tb__ "0|4|
S6aS6S1cS59S18Q40M0A1A1S6Sa8S20S23R3A1S22S90A1A3S0S6S19G0S1bR4P94A2A2R2A3S8S9R3Z2000M1A2Vx;A2S6S3eR1A1S2S1S8S9R6Z1000A2M2R2A2SaR2S9R6G1A2M3A2A2A1F_;Fz;Sd9S69Sa4S69Sa7R9R8A2S93R7R6A5S46R9R8R7R6S6S2S1S8G2R1A2SaR1G3A2A2A1Lz;A5A3F_;F_;F_;F_;Fnb;Ftp;Frho';FBx;Fmo;").
Proof using Hx H16 Hxtop.
  clear -x Hx H16 Hxtop. intros mo Bx rho' tp nb HF U148 Hnb Hband. destruct I18_nexts as (_ & Nb & _ & _ & Mb & _ & LENb & _).
  eapply (@etriple_conseq segsA (SPA segsA (KxA mo Bx) I18bf rho' tp)); [intros w Hw | intros w Hw; exact Hw |].
  { rewrite <- (proj1 (proj2 I18f_eq)). unfold refact18. apply SPA_refacts; [exact Hw | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc |].
    intros HF'. apply Forall_app. split; [exact HF' | exact HF]. }
  eapply etriple_conseq; [intros w Hw; exact Hw | |].
  2:{ eapply sym_run_etripleA; [reflexivity | apply stableA_KxA | exact run18b]. }
  intros [tr [ms md]] Hw. rewrite Nb in Hw. apply (proj1 (LQA1 _ _ _ _ _ _)) in Hw as (rho2 & Hag & Hsp). pose proof Hag as (V2 & L2 & R2).

  destruct T18b_facts as (MV & SMV & _ & SPL & EU & EO).
  pose proof (SPA_move_lastX (KxA mo Bx) rho2 L18b 14 tp _ ltac:(rewrite LENb; lia) ltac:(rewrite MV; exact SMV) Hsp) as H1. rewrite MV in H1.
  pose proof (SPA_unobj segsA (KxA mo Bx) rho2 (ax_setS L18b T18b) (ss_objs (ax_S U18b)) [oarea18b] tp tr ms md SPL H1 ltac:(intros X; exact X)) as H2.
  cbv zeta in H2. rewrite ax_S_ax_setS, ax_setS_ax_setS, EU in H2.
  set (rho3 := rho_absorb rho2 [oarea18b] (vms md tp ms)) in *.
  exists (rho_sub rho3 (sJ18 U18b)). destruct sJ18_id as (_ & IDb & _). pose proof (rho_sub_agree (sJ18 U18b) 156%positive rho3 IDb) as (V3 & L3 & R3).
  split; [|split; [|split]].
  - intros i Hi. rewrite <- (V3 i) by lia. unfold rho3. rewrite rw_absorb. symmetry. apply V2. lia.
  - intros l. rewrite <- (L3 l). unfold rho3. rewrite rl_absorb. symmetry. apply L2.
  - intros a Ha. rewrite <- (R3 a). unfold rho3. rewrite rm_absorb_outside; [symmetry; apply R2|].
    intros (o & [<-|[]] & Hr). rewrite EO in Hr. unfold obj_range, obj_lo_of, obj_hi_of, soff in Hr. cbn [ob_base ob_lo ob_hi fst snd] in Hr.
    assert (R148 : rw rho2 148%positive = rw rho' 148%positive) by (symmetry; apply V2; lia).
    rewrite (U_add_lit rho2 (SVar 148%positive) 4096) in Hr by (cbn [eval]; rewrite ?R148, ?U148; lia). cbn [eval] in Hr. rewrite R148, U148 in Hr.
    replace (bv_signed (Z_to_bv 64 0)) with 0 in Hr by reflexivity. replace (bv_signed (Z_to_bv 64 4096)) with 4096 in Hr by reflexivity.
    destruct Ha as [Ha|[Ha|[_ Hex]]]; [exact (Hband _ Ha ltac:(lia)) | lia | exact (Hex ltac:(lia))].
  - apply (join18 mo Bx U18b); [exact entJ18b | exact IDb | exact H2].
Qed.

Lemma eafter18c : ltac2:(tb__ "0|5|
S6aS6S1cS59S18Q40M0A1A1S6S6Sa8S20S23R4A1S22S90A1A3S0S6S19G0S1bR5P94A2A2R3A3S8S9R4Z2000M1A2Vx;A2S0S6S19G0S1bR7P95A2A2R4A3S8S9R5Z1000M2A2Vx;A2S6S3eR1A1M3S2S1S8S9R9G2A2M4R2A2SaR2S9R9G1A2A2A2A1F_;Fz;S6G3S2S1S8R9R2A2SaR2G4A2A2A1F_;Fz;Sd9S69Sa4S69Sa7RdRcA2S94RbRaA5S46RdRcRbRaS6S1S2S1S8S9RaG2A2R1A2SaR1S9RaG1A2A2A2A1S2S1S8R9R1A2SaR1G4A2A2A1A2Lz;A5A3F_;F_;F_;F_;F_;F_;F_;Fng;Fnb;Ftp;Frho';FBx;Fmo;").
Proof using Hx H16 Hxtop.
  clear -x Hx H16 Hxtop. intros mo Bx rho' tp nb ng HF U148 Hnb U149 Hng Hb1 Hb2. destruct I18_nexts as (_ & _ & Nc & _ & _ & Mc & _ & LENc & LENc1).
  eapply (@etriple_conseq segsA (SPA segsA (KxA mo Bx) I18cf rho' tp)); [intros w Hw | intros w Hw; exact Hw |].
  { rewrite <- (proj2 (proj2 I18f_eq)). unfold refact18. apply SPA_refacts; [exact Hw | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc |].
    intros HF'. apply Forall_app. split; [exact HF' | exact HF]. }
  eapply etriple_conseq; [intros w Hw; exact Hw | |].
  2:{ eapply sym_run_etripleA; [reflexivity | apply stableA_KxA | exact run18c]. }
  intros [tr [ms md]] Hw. rewrite Nc in Hw. apply (proj1 (LQA1 _ _ _ _ _ _)) in Hw as (rho2 & Hag & Hsp). pose proof Hag as (V2 & L2 & R2).
  destruct T18c_facts as (MV1 & SMV1 & _ & MV2 & SMV2 & _ & SPL & EU & EOa & EOb & EOl & EOh).
  pose proof (SPA_move_lastX (KxA mo Bx) rho2 L18c 14 tp _ ltac:(rewrite LENc; lia) ltac:(rewrite MV1; exact SMV1) Hsp) as H1. rewrite MV1 in H1.
  pose proof (SPA_move_lastX (KxA mo Bx) rho2 (ax_setS L18c T18c1) 14 tp _ ltac:(cbn [ax_S ax_setS]; rewrite LENc1; lia) ltac:(cbn [ax_S ax_setS]; rewrite MV2; exact SMV2) H1) as H1'.
  cbn [ax_S ax_setS] in H1'. rewrite MV2, ax_setS_ax_setS in H1'.
  pose proof (SPA_unobj segsA (KxA mo Bx) rho2 (ax_setS L18c T18c) (ss_objs (ax_S U18c)) [oarea18c; ogrp18c] tp tr ms md SPL H1' ltac:(intros X; exact X)) as H2.
  cbv zeta in H2. rewrite ax_S_ax_setS, ax_setS_ax_setS, EU in H2.
  set (rho3 := rho_absorb rho2 [oarea18c; ogrp18c] (vms md tp ms)) in *.
  exists (rho_sub rho3 (sJ18 U18c)). destruct sJ18_id as (_ & _ & IDc). pose proof (rho_sub_agree (sJ18 U18c) 156%positive rho3 IDc) as (V3 & L3 & R3).
  split; [|split; [|split]].
  - intros i Hi. rewrite <- (V3 i) by lia. unfold rho3. rewrite rw_absorb. symmetry. apply V2. lia.
  - intros l. rewrite <- (L3 l). unfold rho3. rewrite rl_absorb. symmetry. apply L2.
  - intros a Ha. rewrite <- (R3 a). unfold rho3. rewrite rm_absorb_outside; [symmetry; apply R2|].
    intros (o & [<-|[<-|[]]] & Hr).
    + rewrite EOa in Hr. unfold obj_range, obj_lo_of, obj_hi_of, soff in Hr. cbn [ob_base ob_lo ob_hi fst snd] in Hr.
      assert (R148 : rw rho2 148%positive = rw rho' 148%positive) by (symmetry; apply V2; lia).
      rewrite (U_add_lit rho2 (SVar 148%positive) 4096) in Hr by (cbn [eval]; rewrite ?R148, ?U148; lia). cbn [eval] in Hr. rewrite R148, U148 in Hr.
      replace (bv_signed (Z_to_bv 64 0)) with 0 in Hr by reflexivity. replace (bv_signed (Z_to_bv 64 4096)) with 4096 in Hr by reflexivity.
      destruct Ha as [Ha|[Ha|[_ [Hex _]]]]; [exact (Hb1 _ Ha ltac:(lia)) | lia | exact (Hex ltac:(lia))].
    + unfold obj_range, obj_lo_of, obj_hi_of, soff in Hr. rewrite EOl, EOh, EOb in Hr. cbn [eval fst snd] in Hr.
      rewrite <- (V2 149%positive) in Hr by lia. rewrite U149 in Hr.
      replace (bv_signed (Z_to_bv 64 0)) with 0 in Hr by reflexivity. replace (bv_signed (Z_to_bv 64 4096)) with 4096 in Hr by reflexivity.
      destruct Ha as [Ha|[Ha|[_ [_ Hex]]]]; [exact (Hb2 _ Ha ltac:(lia)) | lia | exact (Hex ltac:(lia))].
  - apply (join18 mo Bx U18c); [exact entJ18c | exact IDc | exact H2].
Qed.

Definition PostC18 (rhoC : valuation) : assn := ltac2:(tb__ "0|5|
Sd8S4S38S38S4S1cS1cS1S40R2A1S1S7Sf8R1P56A2S0S18Q40M0A1M1S1bR3R2A2S1bVrhoC;R2A2A3F_;Fi;S1S7S0S59S18Q8A1M2A1S26R2R1A2S26VrhoC;R1A2A3Fl;S1G1S3S3eS19G0R1A2M3A1Se0VrhoC;R1A2A2S0S61G2A1M4S1fR3R2A2S1fVrhoC;R2A2A3F_;Fa;S1G1S42VrhoC;G3A2S52R4S19G0R2A2A2S0G4S1fR4R3A2S1fVrhoC;R3A2A3F_;F_;Fa;Sa4S69Sa7S54R2A1S4fA2S91R1S3cVrhoC;A1R3A6A2A2A2A2A2Lrho4;A2Lo;A2Lw;").

Lemma imports18 : ltac2:(tb__ "0|6|
S1S0S1dSe8Sf3S8eSd7S80SbfA1M0P56M1A4Sc6A2S25P94A1M2A3S1S0S1dSe8Sf3S8eSd7S80Sc0A1M3G1A4M4Sc6A2G2A3S1S0S1dSe8G4Sc7A2S25P95A1A3S1S0S5cSf5S8eSd7G1Sc6A4S5dA3S1S0S5cSf5S8eSd7G1Sc7A4S5dA3S1S0S7S27G0A1PaaM5A3S1S0S7S27G3A1G5A3S1S0S7S27S80SbeA1A1G5A3S1S0S1dSe8S8eP34A2S25P54A1A3S1S0S1dSe8S8eP35A2S25P55A1A3S0S1dSe8S8ePaA2S96A3A2A2A2A2A2A2A2A2A2A2").
Proof. clear. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma new_objs18 : ltac2:(tb__ "0|5|
S1S0S59S1eA1M0Sf2S80SaaA1M1S80SbeA1A2S5fS1eA1M2A3S1S0G0Sf2G1S80SbfA1A2S62S1eSc8G2A3A3S1S0G0Sf2G1S80Sc0A1A2S62S1eSc8S62S1eScaG2A3A3A3S1S0S59S5aS1dS1dA2A1M3S82SbeA1SabA3S1S0G3S82SbfA1SabA3S1S0G3S82Sc0A1SabA3S1S0S1dS83SbeA1S21SdfA1M4A3S1S0S1dS83SbfA1G4A3S1S0S1dS83Sc0A1G4A3S1S0S7S27G1A1Sd7A3S0S7S27S80S8fA1A1P56A3A2A2A2A2A2A2A2A2A2A2").
Proof. clear. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Lemma ranges_disjoint_sub : ltac2:(tb__ "0|0|
S5aS6S6A2S6S6S6S6S29R5S5bS6S6R4R3A4A2S8R5R3A2S8R3R5A2S29R8S5bS6S6R5R4A4A2F_;F_;F_;Fhi';Flo';Fhi;Flo;Fr;").
Proof. clear. intros [a b] lo hi lo' hi' H H1 H2. unfold ranges_disjoint in *. cbn [fst snd] in *. lia. Qed.

Definition rho0C (rhoC : valuation) (md : Model) (ms : machine_state) : valuation := ltac2:(tb__ "0|0|
Se9SeaVrhoC;S8dSd5Vmd;S3cVrhoC;A1Vms;A3A3S8eA2").

Lemma rm_sub_absorb : ltac2:(tb__ "0|0|
S1cS59S1eA1Sd2SebS18Q40A1S2Se7R5R4R1A3A1S0S61S18Q8A1A1S1fSe9SeaR6R5R4A3R3A2R2A2S1fR6R2A2A3F_;Fa;Fs;Fms;FR;Frho;").
Proof. clear. intros rho R ms s a Ha. unfold rho_sub. cbn [rm]. apply rm_absorb_outside. exact Ha. Qed.
Lemma rw_sub_absorb : ltac2:(tb__ "0|0|
S1cS59S1eA1Sd2SebS7S0S18Q40A1S1bSe9SeaR5R4R3A3R2A2R1A2S24R5Se8R2R1A2A2A3Fv;Fs;Fms;FR;Frho;").
Proof. clear. intros rho R ms s v. unfold rho_sub. cbn [rw]. apply eval_absorb. Qed.

Lemma rho0C_facts : ltac2:(tb__ "0|2|
S1cS6aSd2S1S18Q40A1M0S2Se7R4S8dR1A3A1S0S61S18Q8A1A1S1fS37R5R4R3A3R2A2S1fR5R2A2A3F_;Fa;S1S0G0S1bS37R3R2R1A3M1P34A2S1bR3P54A2A3S1S0G0S1bG1P35A2S1bR3P55A2A3S0G0S1bG1PaA2S24R3S96A2A3A2A2A2Fms;Fmd;FrhoC;").
Proof.
  clear. intros rhoC md ms. destruct imports18 as (_ & _ & _ & _ & _ & _ & _ & _ & S52 & S53 & S10). unfold rho0C.
  split; [intros a Ha; apply rm_sub_absorb; exact Ha|]. rewrite !rw_sub_absorb, S52, S53, S10. repeat split; reflexivity.
Qed.

Lemma q12x_lo : 0x10006fef8000 + 4096 <= q12x x.
Proof using Hx H16 Hxtop. clear -x Hx H16 Hxtop. pose proof CAx as CA. cbv zeta in CA. destruct CA as (_ & CHPlo & _ & _ & CHPq & _). lia. Qed.

Definition obj_belowS_b (facts : list sprop) (Ge : list (sv * Z)) (o : sobj) : bool := ltac2:(tb__ "0|0|
S67S102Vfacts;Vo;A2Se3VGe;Vo;A2A2").
Definition objs_belowS_except_b (facts : list sprop) (Ge : list (sv * Z)) (skip : list nat) (objs : list sobj) : bool := ltac2:(tb__ "0|1|
S8cS5aS5eS1eA2M0G0S67S89S5eS108S63S5eS1eR1A3A1Vskip;A3S56Vfacts;VGe;S60S5eS1eR1A3A3A2Lio;S8bS5eS1eSa9U0S66S1eVobjs;A2A2Vobjs;A4A3").

Lemma objs_belowS_except_sound : ltac2:(tb__ "0|5|
S1cS59S20A1S59S5aS1dS6A2M0A1S59S5eA1S59S1eA1S18Q40M1A1Sa8S20S23R6A1R5A3S8S101S19G1S1bR7P1M2A2A2A2S1dS6S88G0S5bS1dS6R2R1A4R8A3S8S9S19G1S24RbR3A2A2R2A2S9S19G1S1bRbG2A2A2Z10A2A2F_;Fsz;Fe;S0S5cS53R8R7R6R5A4S5dA3Se0RaR5A2S5eS1eS88S5eR2RaA3S0S61S1eA1S8aS1eRaR3A3S65S1eR2A2A3S2S1S8S63S6S6S28RfR3A2M3A3S19G1RaA2M4A2SaG4S60S6S6G3A3A2A2A1F_;F_;Fo;Fi;S2Se7RcR8R7A3A1F_;F_;F_;F_;F_;F_;Fa;Fobjs;Fskip;FGe;Ffacts;Frho;").
Proof.
  clear. intros rho facts Ge skip objs a HF H1 HG Hb Ha Hskip (o & Ho & Hr).
  destruct (combine_seq_In objs 0 o Ho) as [i Hi].
  pose proof (proj1 (forallb_forall _ _) Hb _ Hi) as X. cbn [fst snd] in X.
  apply Bool.orb_prop in X as [X|X].
  - apply existsb_exists in X as (j & Hj & Hij). apply Nat.eqb_eq in Hij. subst j.
    destruct (combine_seq_nth objs 0 i o Hi) as [Hn _]. rewrite Nat.sub_0_r in Hn. exact (Hskip i o Hj Hn Hr).
  - unfold obj_belowS_b in X. apply Bool.orb_prop in X as [X|X].
    + exact (obj_below_sound rho facts o a HF H1 X Ha Hr).
    + pose proof (eblk_clear_sound rho Ge a 1 o) as D.
      assert (D' : ranges_disjoint (obj_range rho o) (bv_unsigned a, bv_unsigned a + 1)).
      { apply D; [|exact X]. intros e sz Hin y Hy. pose proof (HG e sz Hin). destruct Ha as [Ha _]. lia. }
      unfold ranges_disjoint in D'. cbn [fst snd] in D'. lia.
Qed.

Lemma R18_belowS : ltac2:(tb__ "0|0|
S0S5cS53S22S90A1S43S62S5eU2S62S5eU3S5fS5eA1A3A3S8dA4S5dA3").
Proof. clear. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma R18_nth23 : ltac2:(tb__ "0|6|
S1S0S61S1eA1M0S8aS1eS8dU2A3S65S1eS2fS2aSf9S2aSf9S25P1M1A1S2aSfaS25P2M2A1S21Z3A1M3A3A3S21Z10A1A3S21Z0A1M4S2aSf9S2aSfaS25P3A1G3A3S21Z8A1A3S5fS2cA1S30G1A1A5A2A3S4S59S2cA1M5G5S0G0S8aS1eS8dU3A3S65S1eS2fS25P4A1G4S2aSf9S25P5A1S21Z1A1A3R1S30G2A1A5A2A3Lcs;A2A2").
Proof. clear. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | eexists; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc]. Qed.

Lemma blocks18_top : ltac2:(tb__ "0|2|
S1cS3aR1A1S0S18Q40M0A1M1S1bR2P24A2Vb7;A3S0G1S1bR3P4dA2Vb8;A3S0G1S1bR4P4eA2Vb9;A3S0G1S1bR5P53A2Vb10;A3S0S6SacR6A1Vx;A3S1dS6S88S5aS1dS6A2S5bS1dS6R2R1A4S43A3S8S9S19G0S24RaR3A2A2R2A2Vx;A2F_;Fsz;Fe;F_;F_;F_;F_;F_;F_;Frho;").
Proof using HPL HPL10 HPL4 HPL5 HPL6 HPL7 HPL8 HPL9 Ha1 Ha2 Hmaps Hres Htop Hx H16 Hxtop.
  clear Hlz Hsb Hbrk Hbal HBlim OKF OKP.
  intros rho HV H36 H77 H78 H83 Hx1 e sz Hin. pose proof Ha1 as (_ & _ & A1t). pose proof Ha2 as (_ & _ & A2t). pose proof HV as (H27 & H28 & H29 & H30 & H31 & H32 & H33 & H34 & Hv1).
  pose proof P_facts as (Pal & Pceil & Pfree & PLB & Phi). pose proof RI_range as (R1 & R2 & R3). pose proof RI_val as RV. pose proof SB_val as SB.
  pose proof (urange P) as UP. pose proof (Z.mod_pos_bound (bv_unsigned P) 65536 ltac:(lia)) as MB.
  pose proof b5_facts as (_ & _ & _ & F5t & _). pose proof b6_facts as (_ & _ & F6t & _). pose proof b7_facts as (_ & _ & F7t & _).
  pose proof b8_facts as (_ & _ & F8t & _). pose proof b10_facts as (_ & _ & F10t & _).
  pose proof (priZ_facts rho HV) as (PR1 & _). pose proof CAx as CA. cbv zeta in CA. destruct CA as (Ct & CHPlo & CPEhi & CPEHP & CHPq & CPEe & CPEal & CLIM & _).
  rewrite Hxtop in *. unfold TOPz in F10t. rewrite Hx1 in PR1.
  unfold G18, G17, G13b, G12b, G11c in Hin. rewrite !in_app_iff in Hin. cbn [In] in Hin.
  destruct Hin as [[[[[[= <- <-]|[[= <- <-]|[[= <- <-]|[[= <- <-]|[[= <- <-]|[[= <- <-]|[]]]]]]]|[[= <- <-]|[]]]|[[= <- <-]|[]]]|[[= <- <-]|[]]]|[[= <- <-]|[]]]; cbn [eval].
  - rewrite H27. lia.
  - rewrite H28. lia.
  - unfold ri30. cbn [eval]. rewrite H30. unfold alu64, alu. rewrite bv_add_unsigned, Z_to_bv_unsigned. change (bv_wrap 64 137438953472) with (2 ^ 37).
    rewrite bv_wrap_small by (change (bv_modulus 64) with (2 ^ 64); lia). lia.
  - change (eval rho shRI_base) with (pRI rho). rewrite (Upri rho HV). lia.
  - rewrite H33. lia.
  - rewrite H34. lia.
  - rewrite H36. lia.
  - rewrite H77. lia.
  - unfold LOWPG. rewrite u64_of_lit by lia. lia.
  - rewrite H83. lia.
Qed.

Section CallSite18.
Variables (rhoC : valuation).
Hypothesis HV : vals rhoC.
Hypothesis Hx1 : x1 rhoC = x.
Hypothesis H36 : rw rhoC 36%positive = b7.
Hypothesis H77 : rw rhoC 77%positive = b8.
Hypothesis H78 : rw rhoC 78%positive = b9.
Hypothesis H83 : rw rhoC 83%positive = b10.
Hypothesis V35 : ltac2:(tb__ "0|1|
S0S6SdZ8S19Q40M0S1bVrhoC;P23A2A2A2S19G0Vb6;A2A3").
Hypothesis H1 : ltac2:(tb__ "0|0|
S8S9Vx;Z50A2S36VrhoC;A1A2").
Hypothesis H2 : ltac2:(tb__ "0|0|
S8S9S36VrhoC;A1Z10A2SeZ2Z2fA2A2").
Hypothesis H3 : ltac2:(tb__ "0|0|
S8S9S36VrhoC;A1Z10A2S9Vx;Z2228cfA2A2").
Hypothesis R84 : ltac2:(tb__ "0|1|
S0S18Q40M0A1S1bVrhoC;P54A2S1aG0S3dA2A3").
Hypothesis R85 : ltac2:(tb__ "0|1|
S0S18Q40M0A1S1bVrhoC;P55A2S1aG0SbS41S36VrhoC;A1A1S3dA2A2A3").
Hypothesis HF : ltac2:(tb__ "0|0|
Sa8S20S23VrhoC;A1S22S90A1A3").
Hypothesis HAL : arg_layout rhoC.

Hypothesis MWF : ltac2:(tb__ "0|0|
Se4S6cS6bS35A1A1A1").

Lemma KEPT18 : ltac2:(tb__ "0|1|
S6aSd2S1cS38S40R1A1Sc9S63S6S6S45R2A1M0A3S60S6S6G0A3S37VrhoC;R5R4A3R3A4S18Q40A1Se7VrhoC;S8dR1A3S0S61S18Q8A1A1S1fR6R2A2S1fS37VrhoC;R8R7A3R2A2A3F_;Fa;F_;F_;Fo;FrhoL;Fms;Fmd;").
Proof.
  intros md ms rhoL o Ho Hk a (oR & HoR & Hr). apply Hk. intros Hin.
  pose proof (R18_clear_W rhoC _ _ HV H36 H77 H83 Hx1 HF (out18_Wok o Ho) oR HoR) as D. unfold ranges_disjoint in D. cbn [fst snd] in D. klia.
Qed.

Lemma PSC18 : ltac2:(tb__ "0|7|
S1cS1cS5aS1dS1dA2M0S6S6S1eS88G0R4SabA3S0S18Q40M1A1M2S1bR7P34A2S1bVrhoC;P54A2A3S0G2S1bR8P35A2S1bVrhoC;P55A2A3S7Sf8R1Sd7A2S0G2S1bRbR2A2S1bRaR2A2A3F_;Fi;S1S8S19G1S24R9S63S1dS1dR8A3A2A2M3R7A2SaR7S9G3S19G1S24R9S60S1dS1dR8A3A2A2A2A2A2S1S8Z0R7A2SaR7Z8M4A2A2S88S1eR7S8dA3S2S1S8S63S6S6S28VrhoC;R8A2M5A3S19G1S86S9S19G1S24RcS21SdfA1A2A2S12RaG4A2A2R9A2A2M6A2SaG6S60S6S6G5A3A2A2A1F_;F_;F_;F_;F_;F_;F_;FoR;Fj;Fa;Fr;FrhoL;Frho0';").
Proof.
  pose proof (arith18 _ H1 H2 H3) as AR.
  destruct AR as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17 & A18 & A19 & A20 & A21 & A22 & A23 & A24).
  intros rho0' rhoL r a j oR [<-|[]] E52 E53 AG Ha Hj HoR. unfold vXB, vXL in Ha. cbn [fst snd eval] in Ha. rewrite <- (AG 52%positive), <- (AG 53%positive) in Ha by (unfold NF; klia).
  rewrite E52, E53, R84, R85 in Ha. rewrite !u64_of_lit in Ha by klia.
  cbn [eval]. rewrite (u64_of_lit SHB) by (unfold SHB; klia).
  pose proof (word_byte_range (SHB + a / 8) j ltac:(unfold SHB; split; [|]; [apply Z.add_nonneg_nonneg; [klia|apply Z.div_pos; klia] | ]; assert (a / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; klia); change (2 ^ 47 / 8) with 17592186044416 in *; klia) Hj) as (_ & WB & _).
  rewrite WB.
  assert (D1 : XBz / 8 <= a / 8) by (apply Z.div_le_mono; klia).
  apply Z.mod_divide in A3 as [ke Hke]; [|klia].
  assert (D2 : a / 8 < XEz (r6of rhoC) / 8).
  { rewrite Hke. replace (ke * 64) with (ke * 8 * 8) by klia. rewrite Z_div_mult by klia. apply Z.div_lt_upper_bound; klia. }
  apply Z.mod_divide in A6 as [kb Hkb]; [|klia]. apply Z.mod_divide in A7 as [kc Hkc]; [|klia].
  assert (LO : SXB <= (SHB + a / 8) / 8 * 8).
  { pose proof (Z.div_le_mono SXB (SHB + a / 8) 8 ltac:(klia) ltac:(unfold SXB; klia)) as M. rewrite Hkb in M at 1. rewrite Z_div_mult in M by klia. klia. }
  assert (HI : (SHB + a / 8) / 8 * 8 + 8 <= SXE (r6of rhoC)).
  { assert (M : (SHB + a / 8) / 8 < kc) by (apply Z.div_lt_upper_bound; [klia|]; unfold SXE in Hkc; klia). klia. }
  pose proof (R18_clear_band rhoC SXB (SXE (r6of rhoC) - SXB) HV H36 H77 H78 H83 Hx1 HF ltac:(klia) ltac:(klia) ltac:(klia) oR HoR) as D.
  unfold ranges_disjoint in D. cbn [fst snd] in D. klia.
Qed.

Lemma HFof18 : ltac2:(tb__ "0|0|
S1cSf0P56VrhoC;R1A3Sa8S20S23R2A1S22S90A1A3F_;Frho';").
Proof.
  intros rho' Hag. apply Forall_forall. intros f Hf.
  apply (proj1 (holds_agree_vals 86%positive rhoC rho' f Hag (proj1 (forallb_forall _ _) C18e_facts_below f Hf))).
  exact (proj1 (Forall_forall _ _) HF f Hf).
Qed.

Lemma BANDR18 : ltac2:(tb__ "0|1|
S18Q40M0A1S3eS19G0R1A2A1S2Se7VrhoC;S8dR2A3A1F_;Fa;").
Proof.
  intros a Ha (oR & HoR & Hr). unfold band in Ha. pose proof q12x_lo as QLO.
  pose proof (R18_clear_band rhoC (bv_unsigned a) 1 HV H36 H77 H78 H83 Hx1 HF ltac:(klia) ltac:(lia) ltac:(klia) oR HoR) as D.
  unfold ranges_disjoint in D. cbn [fst snd] in D. lia.
Qed.
Lemma BANDW18 : ltac2:(tb__ "0|3|
S38S18Q40M0A1S40R2A1S3eS19G0R2A2A1S2S1S8S63S6S6S45R4A1M1A3S19G0R3A2M2A2SaG2S60S6S6G1A3A2A2A1F_;F_;Fa;Fo;").
Proof.
  intros o a Ho Ha. pose proof (out18_Wok o Ho) as HW. unfold band in Ha. pose proof q12x_lo as QLO.
  destruct HW as [HW|(W1 & W2 & W3 & W4 & W5 & W6)]; [lia|]. unfold SHADOW_BAND_LO, SHADOW_BAND_HI, kHighMemBeg in *. klia.
Qed.

Lemma area_clear18 : ltac2:(tb__ "0|0|
SbcS1cS1eSc1S35R3A2S0S18Q40A1S1bR3Sc6A2Sd1S35R4A2A3S88S1eR3S8dA3S29S28R5Sc8A2S28VrhoC;R4A2A2F_;F_;F_;FoR;FrhoL;Fo;").
Proof.
  intros o rhoL oR Ho HNA HoR.
  pose proof (out18_Wok (O18b o) Ho) as HW. cbn [out18_W out1_W fst snd] in HW.
  pose proof (R18_clear_W rhoC _ _ HV H36 H77 H83 Hx1 HF HW oR HoR) as D.
  assert (UB : bv_unsigned (out1_base mE o) + 8192 <= 2 ^ 64) by (destruct HW as [HW'|(W1 & W2 & W3 & W4 & W5 & W6)]; unfold TOPz in *; klia).
  unfold obj_range at 1. unfold obj_lo_of, obj_hi_of, soff, O_area. cbn [ob_base ob_lo ob_hi].
  rewrite (U_add_lit rhoL (SVar NA) 4096) by (cbn [eval]; rewrite ?HNA; lia). cbn [eval]. rewrite HNA.
  replace (bv_signed (Z_to_bv 64 0)) with 0 by reflexivity. replace (bv_signed (Z_to_bv 64 4096)) with 4096 by reflexivity.
  unfold ranges_disjoint in D |- *. cbn [fst snd] in D |- *. lia.
Qed.
Lemma grp_clear18 : ltac2:(tb__ "0|2|
SbcS18Q40M0A1M1S1cS1eSc1S35R4A2Sd3S1aG0Z0A2SbdS35R5A2SfbR4A4S0G1S1bR4Sc7A2R5A3S88S1eR4S8dA3S29S28R6ScaA2S28VrhoC;R5A2A2F_;F_;F_;F_;FoR;FrhoL;Fg;Fo;").
Proof.
  intros o g rhoL oR Ho Hpl HNG HoR. pose proof (grp_clear_R18 rhoC o g HV H36 H77 H83 Hx1 MWF HF Ho Hpl oR HoR) as D.
  pose proof (grp_facts o g Hpl) as (_ & _ & G3 & _). unfold TOPz in G3.
  unfold obj_range at 1. unfold obj_lo_of, obj_hi_of, soff, O_grp. cbn [ob_base ob_lo ob_hi eval]. rewrite HNG.
  replace (bv_signed (Z_to_bv 64 0)) with 0 by reflexivity. replace (bv_signed (Z_to_bv 64 4096)) with 4096 by reflexivity.
  unfold ranges_disjoint in D |- *. cbn [fst snd] in D |- *. lia.
Qed.

Lemma ARGR18 : ltac2:(tb__ "0|0|
S18Q40A1Se0VrhoC;R1A2S2Se7VrhoC;S8dR2A3A1F_;Fa;").
Proof.
  intros a Ha.
  assert (HX1 : ARG_LIM <= bv_unsigned (rw rhoC 1%positive)) by (unfold ARG_LIM; unfold x1 in Hx1; rewrite Hx1; lia).
  apply (objs_belowS_except_sound rhoC (ss_facts C18e) G18 [2; 3]%nat R18 a HF HX1); [| exact R18_belowS | exact Ha |].
  - intros e sz Hin. pose proof (blocks18_top rhoC HV H36 H77 H78 H83 Hx1 e sz Hin). unfold x1 in Hx1. rewrite Hx1. lia.
  - destruct R18_nth23 as [N2 [cs3 N3]]. intros i o Hi Hn. destruct Hi as [<-|[<-|[]]].
    + rewrite N2 in Hn. injection Hn as <-. exact (argf_not_env rhoC _ _ a HAL Ha).
    + rewrite N3 in Hn. injection Hn as <-. exact (argf_not_str0 rhoC _ _ a HAL Ha).
Qed.
Lemma BANDR18g : ltac2:(tb__ "0|1|
S18Q40M0A1S3S3eS19G0R1A2A1Se0VrhoC;R1A2A2S2Se7VrhoC;S8dR2A3A1F_;Fa;").
Proof.
  intros a [Ha|Ha]; [exact (BANDR18 a Ha) | exact (ARGR18 a Ha)].
Qed.
Lemma BANDW18g : ltac2:(tb__ "0|3|
S38S18Q40M0A1S40R2A1S3S3eS19G0R2A2A1Se0VrhoC;R2A2A2S2S1S8S63S6S6S45R4A1M1A3S19G0R3A2M2A2SaG2S60S6S6G1A3A2A2A1F_;F_;Fa;Fo;").
Proof.
  intros o a Ho [Ha|[Ha _]]; [exact (BANDW18 o a Ho Ha)|].
  pose proof (out18_Wok o Ho) as HW. unfold x1 in Hx1. rewrite Hx1 in Ha.
  destruct HW as [HW|(W1 & W2 & W3 & W4 & W5 & W6)]; unfold TOPz in *; lia.
Qed.
Lemma boh18 : ltac2:(tb__ "0|2|
S6OF_;S18Q40M0A1S3S3eS19G0R1A2A1Se0VrhoC;R1A2A2S3S3eS19G0R2A2M1A1S3S8Vx;G1A2S1S4bG1A1R3G1A1A2A2A2F_;Fa;Fex;").
Proof.
  intros ex a [Ha|[Ha _]]; [left; exact Ha | right; left]. unfold x1 in Hx1. rewrite Hx1 in Ha. lia.
Qed.

Lemma BANDR18L : ltac2:(tb__ "0|1|
S18Q40M0A1S42VrhoC;S19G0R1A2A2S2Se7VrhoC;S8dR2A3A1F_;Fa;").
Proof.
  intros a Ha (oR & HoR & Hr). pose proof (R18_clear_lowb rhoC a HV H36 H77 H78 H83 Hx1 HF Ha oR HoR) as D. unfold ranges_disjoint in D. cbn [fst snd] in D. lia.
Qed.
Lemma BANDW18L : ltac2:(tb__ "0|3|
S38S18Q40M0A1S40R2A1S42VrhoC;S19G0R2A2A2S2S1S8S63S6S6S45R4A1M1A3S19G0R3A2M2A2SaG2S60S6S6G1A3A2A2A1F_;F_;Fa;Fo;").
Proof.
  intros o a Ho Ha. pose proof (lowb_bandw rhoC (bv_unsigned a) Ha) as Hb. unfold bandw in Hb. pose proof (out18_Wok o Ho) as HW.
  destruct HW as [HW|(W1 & W2 & W3 & W4 & W5 & W6)]; [lia|]. unfold SHADOW_BAND_LO, SHADOW_BAND_HI in *. klia.
Qed.
Lemma rm_back18 : ltac2:(tb__ "0|3|
S6aSd2S1cS1cS1cS38S18Q40M0A1S40R2A1S3S3eS19G0R2A2A1Se0VrhoC;R2A2A2S0S61S18Q8A1A1M1S1fR5R3A2S1fR6R3A2A3S0G1S1fR7R4A2S1fR8R4A2A3Sc9S63S6S6S45R6A1M2A3S60S6S6G2A3S37VrhoC;RbRaA3R9A4S0G1S1fR8R6A2S1fVrhoC;R6A2A3F_;F_;F_;F_;F_;Fa;Fo;Frho4;Frho';FrhoL;Fms;Fmd;").
Proof.
  intros md ms rhoL rho' rho4 o a Ho Ha E4 EL Hk. rewrite E4, EL, (Hk a) by (exact (BANDW18g o a Ho Ha)).
  apply (proj1 (rho0C_facts rhoC md ms)). exact (BANDR18g a Ha).
Qed.
Lemma rm_back18L : ltac2:(tb__ "0|3|
S6aSd2S1cS1cS1cS38S18Q40M0A1S40R2A1S42VrhoC;S19G0R2A2A2S0S61S18Q8A1A1M1S1fR5R3A2S1fR6R3A2A3S0G1S1fR7R4A2S1fR8R4A2A3Sc9S63S6S6S45R6A1M2A3S60S6S6G2A3S37VrhoC;RbRaA3R9A4S0G1S1fR8R6A2S1fVrhoC;R6A2A3F_;F_;F_;F_;F_;Fa;Fo;Frho4;Frho';FrhoL;Fms;Fmd;").
Proof.
  intros md ms rhoL rho' rho4 o a Ho Ha E4 EL Hk. rewrite E4, EL, (Hk a) by (exact (BANDW18L o a Ho Ha)).
  apply (proj1 (rho0C_facts rhoC md ms)). exact (BANDR18L a Ha).
Qed.

Lemma cont18a : ltac2:(tb__ "0|2|
S6aSd2S1cS59S18Q40A1A1S59S6dA1S6aSf0Sd7S37VrhoC;R6R5A3R4A3Sc3S35S3bS37VrhoC;R7R6A3S3cVrhoC;A1M0R5R4R3R2A8S1Sf6VrhoC;Sd5R8G0R7A3S8dS8eSaaSbeS8fS5fS5aS1dS1dA2A1M1R6A9S1cSf1VrhoC;Sd5R9G0R8A3S8dS8eS80SaaA1S80S8fA1S80SbeA1R1R7A9SdaS69Vok;Sa4S69Sf4Sc3S35S3bA2S37VrhoC;RaR9A3G0R8R7A5Sf7S8eSaaSbeS8fS8dG1A6R2R7A5S3fVrhoC;A1A4F_;Frho';A2F_;F_;Fmd';Ftr';FtpL;FrhoL;Fms;Fmd;").
Proof using All.
  intros md ms rhoL tpL tr' md' HagL HJL.
  destruct new_objs18 as (NO0 & NO1 & NO2 & XL0 & XL1 & XL2 & BL0 & BL1 & BL2 & NPRE & NC). pose proof (rho0C_facts rhoC md ms) as (RM0 & E52 & E53 & _).
  unfold JL_null0 in HJL. destruct HJL as (EtpL & HagL' & o & Ho & Hkept & HKo).
  split; [split; [split|]|].
  - intros a Ha. exact (KEPT18 md ms rhoL (O18a o) Ho Hkept a Ha).
  - intros o' oR Ho' HoR. rewrite NO0 in Ho'. destruct Ho'.
  - split; [|intros r a Hr; destruct Hr].
    intros r a j oR Hr Ha Hj HoR. rewrite XL0 in Hr. rewrite BL0. exact (PSC18 _ rhoL r a j oR Hr E52 E53 (proj1 HagL') Ha Hj HoR).
  - intros rho' (HagC & HrmL & _ & Himp). rewrite (proj1 I18_eq).
    eapply (@triple_conseq segsA ok (fun w => exists o', out0_ok mE o' /\ rm_kept_outside (fst (out0_W o')) (snd (out0_W o')) (rho0C rhoC md ms) rhoL
                                              /\ SPA segsA (KxA (out0_model mE o') B18) I18a rho' tpL w)); [intros w Hw | intros w Hw; exact Hw |].
    { destruct Hw as [HsmW HJW]. unfold J_ofPA, JL_null0 in HJW. destruct HJW as (_ & _ & o' & Ho' & Hkept' & HK').
      exists o'. split; [exact Ho'|]. split; [exact Hkept'|]. split; [exact HsmW | unfold B18; exact HK']. }
    apply triple_ex; intros o'. apply triple_pure; intros Ho'. apply triple_pure; intros Hkept'.
    eapply triple_conseq; [intros w Hw; exact Hw | | exact (after18a (out0_model mE o') B18 rho' tpL (HFof18 rho' HagC))].
    intros w (rho4 & Q1 & Q2 & Q3 & Q4). exists (O18a o'), rho4. split; [exact Ho'|].
    split; [intros i0 Hi0; rewrite (Q1 i0 Hi0); symmetry; apply (proj1 HagC); exact Hi0|].
    split; [intros l; rewrite (Q2 l); symmetry; apply (proj2 HagC)|].
    split; [intros a Ha; exact (rm_back18 md ms rhoL rho' rho4 (O18a o') a Ho' Ha (Q3 a (boh18 (fun _ => True) a Ha)) (HrmL a) Hkept')|].
    split; [intros a Ha _; exact (rm_back18L md ms rhoL rho' rho4 (O18a o') a Ho' Ha (Q3 a ltac:(right; right; split; [exact (lowb_bandw rhoC _ Ha) | exact I])) (HrmL a) Hkept')|].
    rewrite EtpL in Q4. exact Q4.
Qed.

Lemma cont18b : ltac2:(tb__ "0|2|
S6aSd2S1cS59S18Q40A1A1S59S6dA1S6aSf0Sd7S37VrhoC;R6R5A3R4A3Sc4S35S3bS37VrhoC;R7R6A3S3cVrhoC;A1M0R5R4R3R2A8S1Sf6VrhoC;Sd5R8G0R7A3S8dS8eSaaSbfS8fS5fS5aS1dS1dA2A1M1R6A9S1cSf1VrhoC;Sd5R9G0R8A3S8dS8eS80SaaA1S80S8fA1S80SbfA1R1R7A9SdaS69Vok;Sa4S69Sf4Sc4S35S3bA2S37VrhoC;RaR9A3G0R8R7A5Sf7S8eSaaSbfS8fS8dG1A6R2R7A5S3fVrhoC;A1A4F_;Frho';A2F_;F_;Fmd';Ftr';FtpL;FrhoL;Fms;Fmd;").
Proof using All.
  intros md ms rhoL tpL tr' md' HagL HJL.
  destruct new_objs18 as (NO0 & NO1 & NO2 & XL0 & XL1 & XL2 & BL0 & BL1 & BL2 & NPRE & NC). destruct imports18 as (IM1 & IM2 & IM3 & PV1 & PV2 & NX1 & NX2 & NX0 & _).
  pose proof (rho0C_facts rhoC md ms) as (RM0 & E52 & E53 & _).
  unfold JL_null1 in HJL. destruct HJL as (HagL' & o & Ho & EtpL & HNA & Hkept & HKo).
  split; [split; [split|]|].
  - intros a Ha. exact (KEPT18 md ms rhoL (O18b o) Ho Hkept a Ha).
  - intros o' oR Ho' HoR. rewrite NO1 in Ho'. destruct Ho' as [<-|[]]. exact (area_clear18 o rhoL oR Ho HNA HoR).
  - split; [|intros r a Hr; destruct Hr].
    intros r a j oR Hr Ha Hj HoR. rewrite XL1 in Hr. rewrite BL1. exact (PSC18 _ rhoL r a j oR Hr E52 E53 (proj1 HagL') Ha Hj HoR).
  - intros rho' (HagC & HrmL & _ & Himp). rewrite (proj1 (proj2 I18_eq)).
    eapply (@triple_conseq segsA ok (fun w => exists o', out1_ok mE o' /\ tpL = out1_tp mE o' (TP18 rhoC) /\ rw rhoL NA = out1_base mE o'
                                              /\ rm_kept_outside (fst (out1_W mE o')) (snd (out1_W mE o')) (rho0C rhoC md ms) rhoL
                                              /\ SPA segsA (KxA (out1_model mE o') B18) I18b rho' tpL w)); [intros w Hw | intros w Hw; exact Hw |].
    { destruct Hw as [HsmW HJW]. unfold J_ofPA, JL_null1 in HJW. destruct HJW as (_ & o' & Ho' & Etp' & HNA' & Hkept' & HK').
      exists o'. split; [exact Ho'|]. split; [exact Etp'|]. split; [exact HNA'|]. split; [exact Hkept'|]. split; [exact HsmW | unfold B18; exact HK']. }
    apply triple_ex; intros o'. apply triple_pure; intros Ho'. apply triple_pure; intros Etp'. apply triple_pure; intros HNA'. apply triple_pure; intros Hkept'.
    pose proof (out18_Wok (O18b o') Ho') as HW'. cbn [out18_W out1_W fst snd] in HW'. pose proof q12x_lo as QLO.
    assert (E148 : rw rho' 148%positive = out1_base mE o').
    { specialize (Himp NA). rewrite NPRE, NC, NX1, IM1 in Himp. cbn [eval] in Himp. rewrite <- HNA'. symmetry. apply Himp; [exact PV1 | cbv; lia]. }
    eapply triple_conseq; [intros w Hw; exact Hw | |].
    2:{ apply (after18b (out1_model mE o') B18 rho' tpL (bv_unsigned (out1_base mE o')) (HFof18 rho' HagC)).
        - rewrite E148. reflexivity.
        - destruct HW' as [HW'|(W1 & W2 & W3 & W4 & W5 & W6)]; unfold TOPz in *; klia.
        - intros z Hz. unfold band in Hz. destruct HW' as [HW'|(W1 & W2 & W3 & W4 & W5 & W6)]; [klia|]. unfold SHADOW_BAND_LO, SHADOW_BAND_HI in W6. klia. }
    intros w (rho4 & Q1 & Q2 & Q3 & Q4). exists (O18b o'), rho4. split; [exact Ho'|].
    split; [intros i0 Hi0; rewrite (Q1 i0 Hi0); symmetry; apply (proj1 HagC); exact Hi0|].
    split; [intros l; rewrite (Q2 l); symmetry; apply (proj2 HagC)|].
    split; [intros a Ha; exact (rm_back18 md ms rhoL rho' rho4 (O18b o') a Ho' Ha (Q3 a (boh18 (fun z => ~ (bv_unsigned (out1_base mE o') + 4096 <= z < bv_unsigned (out1_base mE o') + 8192)) a Ha)) (HrmL a) Hkept')|].
    split; [intros a Ha Hg; exact (rm_back18L md ms rhoL rho' rho4 (O18b o') a Ho' Ha (Q3 a ltac:(right; right; split; [exact (lowb_bandw rhoC _ Ha) | cbv beta; pose proof (BANDW18L (O18b o') a Ho' Ha) as WW; cbn [out18_W out1_W fst snd] in WW; lia])) (HrmL a) Hkept')|].
    pose proof (TP18_out18 rhoC (O18b o') HV Hx1 V35 H1 H2 H3 Ho') as TT. cbn [out18_tp] in TT. rewrite Etp', TT in Q4. exact Q4.
Qed.

Lemma cont18c : ltac2:(tb__ "0|2|
S6aSd2S1cS59S18Q40A1A1S59S6dA1S6aSf0Sd7S37VrhoC;R6R5A3R4A3Sc5S35S3bS37VrhoC;R7R6A3S3cVrhoC;A1M0R5R4R3R2A8S1Sf6VrhoC;Sd5R8G0R7A3S8dS8eSaaSc0S8fS5fS5aS1dS1dA2A1M1R6A9S1cSf1VrhoC;Sd5R9G0R8A3S8dS8eS80SaaA1S80S8fA1S80Sc0A1R1R7A9SdaS69Vok;Sa4S69Sf4Sc5S35S3bA2S37VrhoC;RaR9A3G0R8R7A5Sf7S8eSaaSc0S8fS8dG1A6R2R7A5S3fVrhoC;A1A4F_;Frho';A2F_;F_;Fmd';Ftr';FtpL;FrhoL;Fms;Fmd;").
Proof using All.
  intros md ms rhoL tpL tr' md' HagL HJL.
  destruct new_objs18 as (NO0 & NO1 & NO2 & XL0 & XL1 & XL2 & BL0 & BL1 & BL2 & NPRE & NC). destruct imports18 as (IM1 & IM2 & IM3 & PV1 & PV2 & NX1 & NX2 & NX0 & _).
  pose proof (rho0C_facts rhoC md ms) as (RM0 & E52 & E53 & _).
  unfold JL_ok in HJL. destruct HJL as (HagL' & o & g & Ho & Hpl & EtpL & HNA & HNG & Hkept & HKo).
  split; [split; [split|]|].
  - intros a Ha. exact (KEPT18 md ms rhoL (O18c o g) (conj Ho Hpl) Hkept a Ha).
  - intros o' oR Ho' HoR. rewrite NO2 in Ho'. destruct Ho' as [<-|[<-|[]]]; [exact (area_clear18 o rhoL oR Ho HNA HoR) | exact (grp_clear18 o g rhoL oR Ho Hpl HNG HoR)].
  - split; [|intros r a Hr; destruct Hr].
    intros r a j oR Hr Ha Hj HoR. rewrite XL2 in Hr. rewrite BL2. exact (PSC18 _ rhoL r a j oR Hr E52 E53 (proj1 HagL') Ha Hj HoR).
  - intros rho' (HagC & HrmL & _ & Himp). rewrite (proj2 (proj2 I18_eq)).
    eapply (@triple_conseq segsA ok (fun w => exists o' g', out1_ok mE o' /\ mmap_place_ok_none (Z_to_bv 64 0) (out1_model mE o') pgw g'
                                              /\ tpL = out1_tp mE o' (TP18 rhoC) /\ rw rhoL NA = out1_base mE o' /\ rw rhoL NG = g'
                                              /\ rm_kept_outside (fst (out1_W mE o')) (snd (out1_W mE o')) (rho0C rhoC md ms) rhoL
                                              /\ SPA segsA (KxA (mgrant (out1_model mE o') g') B18) I18c rho' tpL w)); [intros w Hw | intros w Hw; exact Hw |].
    { destruct Hw as [HsmW HJW]. unfold J_ofPA, JL_ok in HJW. destruct HJW as (_ & o' & g' & Ho' & Hpl' & Etp' & HNA' & HNG' & Hkept' & HK').
      exists o', g'. split; [exact Ho'|]. split; [exact Hpl'|]. split; [exact Etp'|]. split; [exact HNA'|]. split; [exact HNG'|]. split; [exact Hkept'|]. split; [exact HsmW | unfold B18; exact HK']. }
    apply triple_ex; intros o'. apply triple_ex; intros g'. apply triple_pure; intros Ho'. apply triple_pure; intros Hpl'. apply triple_pure; intros Etp'.
    apply triple_pure; intros HNA'. apply triple_pure; intros HNG'. apply triple_pure; intros Hkept'.
    pose proof (out18_Wok (O18b o') Ho') as HW'. cbn [out18_W out1_W fst snd] in HW'. pose proof q12x_lo as QLO.
    pose proof (grp_facts o' g' Hpl') as (G1 & G2 & G3 & G4 & G5).
    assert (E148 : rw rho' 148%positive = out1_base mE o').
    { specialize (Himp NA). rewrite NPRE, NC, NX2, IM2 in Himp. cbn [eval] in Himp. rewrite <- HNA'. symmetry. apply Himp; [exact PV1 | cbv; lia]. }
    assert (E149 : rw rho' 149%positive = g').
    { pose proof (Himp NG) as Hg. rewrite NPRE, NC, NX2, IM3 in Hg. cbn [eval] in Hg. rewrite <- HNG'. symmetry. apply Hg; [exact PV2 | cbv; lia]. }
    eapply triple_conseq; [intros w Hw; exact Hw | |].
    2:{ apply (after18c (mgrant (out1_model mE o') g') B18 rho' tpL (bv_unsigned (out1_base mE o')) (bv_unsigned g') (HFof18 rho' HagC)).
        - rewrite E148. reflexivity.
        - destruct HW' as [HW'|(W1 & W2 & W3 & W4 & W5 & W6)]; unfold TOPz in *; klia.
        - rewrite E149. reflexivity.
        - unfold TOPz in G3. klia.
        - intros z Hz. unfold band in Hz. destruct HW' as [HW'|(W1 & W2 & W3 & W4 & W5 & W6)]; [klia|]. unfold SHADOW_BAND_LO, SHADOW_BAND_HI in W6. klia.
        - intros z Hz. unfold band in Hz. klia. }
    intros w (rho4 & Q1 & Q2 & Q3 & Q4). exists (O18c o' g'), rho4. split; [split; [exact Ho' | exact Hpl']|].
    split; [intros i0 Hi0; rewrite (Q1 i0 Hi0); symmetry; apply (proj1 HagC); exact Hi0|].
    split; [intros l; rewrite (Q2 l); symmetry; apply (proj2 HagC)|].
    split; [intros a Ha; exact (rm_back18 md ms rhoL rho' rho4 (O18b o') a Ho' Ha (Q3 a (boh18 (fun z => ~ (bv_unsigned (out1_base mE o') + 4096 <= z < bv_unsigned (out1_base mE o') + 8192) /\ ~ (bv_unsigned g' <= z < bv_unsigned g' + 4096)) a Ha)) (HrmL a) Hkept')|].
    split; [intros a Ha Hg; exact (rm_back18L md ms rhoL rho' rho4 (O18b o') a Ho' Ha (Q3 a ltac:(right; right; split; [exact (lowb_bandw rhoC _ Ha) | cbv beta; split; [pose proof (BANDW18L (O18b o') a Ho' Ha) as WW; cbn [out18_W out1_W fst snd] in WW; lia | exact Hg]])) (HrmL a) Hkept')|].
    pose proof (TP18_out18 rhoC (O18b o') HV Hx1 V35 H1 H2 H3 Ho') as TT. cbn [out18_tp] in TT. rewrite Etp', TT in Q4. exact Q4.
Qed.

Lemma call18_core : ltac2:(tb__ "0|0|
Sd6S35A1SdaS69Vok;Sa4S69Sa7S35S3bA2S8fVrhoC;S3cVrhoC;A1A5S3fVrhoC;A1A4F_;").
Proof using All.
  intros HLIM.
  apply (call_soundPA3 segsA ok (KxA mE B18pre) (KxM mE B18pre) C18 Pre_M s18 R18 (Posts_M mE B18pre) [] (PostC18 rhoC) rhoC (TP18 rhoC)).
  - intros r [].
  - exact ent18.
  - exact chk18.
  -
    intros rho1 tp1. exact (musl_malloc40_sum_A ok mE B18pre OKF OKP (m40_mE HLIM) rho1 tp1).
  -
    intros tr ms md Hsm HK. split; [exact HK|].
    pose proof (rho0C_facts rhoC md ms) as (_ & _ & _ & E10). unfold rho0C in E10. rewrite E10, top_mE.
    unfold SP18. unfold x1 in Hx1. rewrite (U_add_slit' rhoC (SVar 1%positive) (-240)) by (cbn [eval]; rewrite ?Hx1; lia). cbn [eval]. rewrite Hx1.
    unfold TOPz, D_M. lia.
  -
    intros L JL tr ms md rhoL tpL tr' ms' md' HinL HsmC HK HagL HsmL HJL.
    change (rho_sub (rho_absorb rhoC R18 (vms md (TP18 rhoC) ms)) s18) with (rho0C rhoC md ms) in HagL, HJL |- *.
    destruct HinL as [E|[E|[E|[]]]]; injection E as EL EJ; subst L JL.
    + exact (cont18a md ms rhoL tpL tr' md' HagL HJL).
    + exact (cont18b md ms rhoL tpL tr' md' HagL HJL).
    + exact (cont18c md ms rhoL tpL tr' md' HagL HJL).
Qed.

Lemma econt18a : ltac2:(tb__ "0|2|
S6aSd2S1cS59S18Q40A1A1S59S6dA1S6aSf0Sd7S37VrhoC;R6R5A3R4A3Sc3S35S3bS37VrhoC;R7R6A3S3cVrhoC;A1M0R5R4R3R2A8S1Sf6VrhoC;Sd5R8G0R7A3S8dS8eSaaSbeS8fS5fS5aS1dS1dA2A1M1R6A9S1cSf1VrhoC;Sd5R9G0R8A3S8dS8eS80SaaA1S80S8fA1S80SbeA1R1R7A9Sd9S69Sa4S69Sf4Sc3S35S3bA2S37VrhoC;RaR9A3G0R8R7A5Sf7S8eSaaSbeS8fS8dG1A6R2R7A5S3fVrhoC;A1A3F_;Frho';A2F_;F_;Fmd';Ftr';FtpL;FrhoL;Fms;Fmd;").
Proof using All.
  intros md ms rhoL tpL tr' md' HagL HJL.
  destruct new_objs18 as (NO0 & NO1 & NO2 & XL0 & XL1 & XL2 & BL0 & BL1 & BL2 & NPRE & NC). pose proof (rho0C_facts rhoC md ms) as (RM0 & E52 & E53 & _).
  unfold JL_null0 in HJL. destruct HJL as (EtpL & HagL' & o & Ho & Hkept & HKo).
  split; [split; [split|]|].
  - intros a Ha. exact (KEPT18 md ms rhoL (O18a o) Ho Hkept a Ha).
  - intros o' oR Ho' HoR. rewrite NO0 in Ho'. destruct Ho'.
  - split; [|intros r a Hr; destruct Hr].
    intros r a j oR Hr Ha Hj HoR. rewrite XL0 in Hr. rewrite BL0. exact (PSC18 _ rhoL r a j oR Hr E52 E53 (proj1 HagL') Ha Hj HoR).
  - intros rho' (HagC & HrmL & _ & Himp). rewrite (proj1 I18_eq).
    eapply (@etriple_conseq segsA (fun w => exists o', out0_ok mE o' /\ rm_kept_outside (fst (out0_W o')) (snd (out0_W o')) (rho0C rhoC md ms) rhoL
                                              /\ SPA segsA (KxA (out0_model mE o') B18) I18a rho' tpL w)); [intros w Hw | intros w Hw; exact Hw |].
    { destruct Hw as [HsmW HJW]. unfold J_ofPA, JL_null0 in HJW. destruct HJW as (_ & _ & o' & Ho' & Hkept' & HK').
      exists o'. split; [exact Ho'|]. split; [exact Hkept'|]. split; [exact HsmW | unfold B18; exact HK']. }
    apply etriple_ex; intros o'. apply etriple_pure; intros Ho'. apply etriple_pure; intros Hkept'.
    eapply etriple_conseq; [intros w Hw; exact Hw | | exact (eafter18a (out0_model mE o') B18 rho' tpL (HFof18 rho' HagC))].
    intros w (rho4 & Q1 & Q2 & Q3 & Q4). exists (O18a o'), rho4. split; [exact Ho'|].
    split; [intros i0 Hi0; rewrite (Q1 i0 Hi0); symmetry; apply (proj1 HagC); exact Hi0|].
    split; [intros l; rewrite (Q2 l); symmetry; apply (proj2 HagC)|].
    split; [intros a Ha; exact (rm_back18 md ms rhoL rho' rho4 (O18a o') a Ho' Ha (Q3 a (boh18 (fun _ => True) a Ha)) (HrmL a) Hkept')|].
    split; [intros a Ha _; exact (rm_back18L md ms rhoL rho' rho4 (O18a o') a Ho' Ha (Q3 a ltac:(right; right; split; [exact (lowb_bandw rhoC _ Ha) | exact I])) (HrmL a) Hkept')|].
    rewrite EtpL in Q4. exact Q4.
Qed.

Lemma econt18b : ltac2:(tb__ "0|2|
S6aSd2S1cS59S18Q40A1A1S59S6dA1S6aSf0Sd7S37VrhoC;R6R5A3R4A3Sc4S35S3bS37VrhoC;R7R6A3S3cVrhoC;A1M0R5R4R3R2A8S1Sf6VrhoC;Sd5R8G0R7A3S8dS8eSaaSbfS8fS5fS5aS1dS1dA2A1M1R6A9S1cSf1VrhoC;Sd5R9G0R8A3S8dS8eS80SaaA1S80S8fA1S80SbfA1R1R7A9Sd9S69Sa4S69Sf4Sc4S35S3bA2S37VrhoC;RaR9A3G0R8R7A5Sf7S8eSaaSbfS8fS8dG1A6R2R7A5S3fVrhoC;A1A3F_;Frho';A2F_;F_;Fmd';Ftr';FtpL;FrhoL;Fms;Fmd;").
Proof using All.
  intros md ms rhoL tpL tr' md' HagL HJL.
  destruct new_objs18 as (NO0 & NO1 & NO2 & XL0 & XL1 & XL2 & BL0 & BL1 & BL2 & NPRE & NC). destruct imports18 as (IM1 & IM2 & IM3 & PV1 & PV2 & NX1 & NX2 & NX0 & _).
  pose proof (rho0C_facts rhoC md ms) as (RM0 & E52 & E53 & _).
  unfold JL_null1 in HJL. destruct HJL as (HagL' & o & Ho & EtpL & HNA & Hkept & HKo).
  split; [split; [split|]|].
  - intros a Ha. exact (KEPT18 md ms rhoL (O18b o) Ho Hkept a Ha).
  - intros o' oR Ho' HoR. rewrite NO1 in Ho'. destruct Ho' as [<-|[]]. exact (area_clear18 o rhoL oR Ho HNA HoR).
  - split; [|intros r a Hr; destruct Hr].
    intros r a j oR Hr Ha Hj HoR. rewrite XL1 in Hr. rewrite BL1. exact (PSC18 _ rhoL r a j oR Hr E52 E53 (proj1 HagL') Ha Hj HoR).
  - intros rho' (HagC & HrmL & _ & Himp). rewrite (proj1 (proj2 I18_eq)).
    eapply (@etriple_conseq segsA (fun w => exists o', out1_ok mE o' /\ tpL = out1_tp mE o' (TP18 rhoC) /\ rw rhoL NA = out1_base mE o'
                                              /\ rm_kept_outside (fst (out1_W mE o')) (snd (out1_W mE o')) (rho0C rhoC md ms) rhoL
                                              /\ SPA segsA (KxA (out1_model mE o') B18) I18b rho' tpL w)); [intros w Hw | intros w Hw; exact Hw |].
    { destruct Hw as [HsmW HJW]. unfold J_ofPA, JL_null1 in HJW. destruct HJW as (_ & o' & Ho' & Etp' & HNA' & Hkept' & HK').
      exists o'. split; [exact Ho'|]. split; [exact Etp'|]. split; [exact HNA'|]. split; [exact Hkept'|]. split; [exact HsmW | unfold B18; exact HK']. }
    apply etriple_ex; intros o'. apply etriple_pure; intros Ho'. apply etriple_pure; intros Etp'. apply etriple_pure; intros HNA'. apply etriple_pure; intros Hkept'.
    pose proof (out18_Wok (O18b o') Ho') as HW'. cbn [out18_W out1_W fst snd] in HW'. pose proof q12x_lo as QLO.
    assert (E148 : rw rho' 148%positive = out1_base mE o').
    { specialize (Himp NA). rewrite NPRE, NC, NX1, IM1 in Himp. cbn [eval] in Himp. rewrite <- HNA'. symmetry. apply Himp; [exact PV1 | cbv; lia]. }
    eapply etriple_conseq; [intros w Hw; exact Hw | |].
    2:{ apply (eafter18b (out1_model mE o') B18 rho' tpL (bv_unsigned (out1_base mE o')) (HFof18 rho' HagC)).
        - rewrite E148. reflexivity.
        - destruct HW' as [HW'|(W1 & W2 & W3 & W4 & W5 & W6)]; unfold TOPz in *; klia.
        - intros z Hz. unfold band in Hz. destruct HW' as [HW'|(W1 & W2 & W3 & W4 & W5 & W6)]; [klia|]. unfold SHADOW_BAND_LO, SHADOW_BAND_HI in W6. klia. }
    intros w (rho4 & Q1 & Q2 & Q3 & Q4). exists (O18b o'), rho4. split; [exact Ho'|].
    split; [intros i0 Hi0; rewrite (Q1 i0 Hi0); symmetry; apply (proj1 HagC); exact Hi0|].
    split; [intros l; rewrite (Q2 l); symmetry; apply (proj2 HagC)|].
    split; [intros a Ha; exact (rm_back18 md ms rhoL rho' rho4 (O18b o') a Ho' Ha (Q3 a (boh18 (fun z => ~ (bv_unsigned (out1_base mE o') + 4096 <= z < bv_unsigned (out1_base mE o') + 8192)) a Ha)) (HrmL a) Hkept')|].
    split; [intros a Ha Hg; exact (rm_back18L md ms rhoL rho' rho4 (O18b o') a Ho' Ha (Q3 a ltac:(right; right; split; [exact (lowb_bandw rhoC _ Ha) | cbv beta; pose proof (BANDW18L (O18b o') a Ho' Ha) as WW; cbn [out18_W out1_W fst snd] in WW; lia])) (HrmL a) Hkept')|].
    pose proof (TP18_out18 rhoC (O18b o') HV Hx1 V35 H1 H2 H3 Ho') as TT. cbn [out18_tp] in TT. rewrite Etp', TT in Q4. exact Q4.
Qed.

Lemma econt18c : ltac2:(tb__ "0|2|
S6aSd2S1cS59S18Q40A1A1S59S6dA1S6aSf0Sd7S37VrhoC;R6R5A3R4A3Sc5S35S3bS37VrhoC;R7R6A3S3cVrhoC;A1M0R5R4R3R2A8S1Sf6VrhoC;Sd5R8G0R7A3S8dS8eSaaSc0S8fS5fS5aS1dS1dA2A1M1R6A9S1cSf1VrhoC;Sd5R9G0R8A3S8dS8eS80SaaA1S80S8fA1S80Sc0A1R1R7A9Sd9S69Sa4S69Sf4Sc5S35S3bA2S37VrhoC;RaR9A3G0R8R7A5Sf7S8eSaaSc0S8fS8dG1A6R2R7A5S3fVrhoC;A1A3F_;Frho';A2F_;F_;Fmd';Ftr';FtpL;FrhoL;Fms;Fmd;").
Proof using All.
  intros md ms rhoL tpL tr' md' HagL HJL.
  destruct new_objs18 as (NO0 & NO1 & NO2 & XL0 & XL1 & XL2 & BL0 & BL1 & BL2 & NPRE & NC). destruct imports18 as (IM1 & IM2 & IM3 & PV1 & PV2 & NX1 & NX2 & NX0 & _).
  pose proof (rho0C_facts rhoC md ms) as (RM0 & E52 & E53 & _).
  unfold JL_ok in HJL. destruct HJL as (HagL' & o & g & Ho & Hpl & EtpL & HNA & HNG & Hkept & HKo).
  split; [split; [split|]|].
  - intros a Ha. exact (KEPT18 md ms rhoL (O18c o g) (conj Ho Hpl) Hkept a Ha).
  - intros o' oR Ho' HoR. rewrite NO2 in Ho'. destruct Ho' as [<-|[<-|[]]]; [exact (area_clear18 o rhoL oR Ho HNA HoR) | exact (grp_clear18 o g rhoL oR Ho Hpl HNG HoR)].
  - split; [|intros r a Hr; destruct Hr].
    intros r a j oR Hr Ha Hj HoR. rewrite XL2 in Hr. rewrite BL2. exact (PSC18 _ rhoL r a j oR Hr E52 E53 (proj1 HagL') Ha Hj HoR).
  - intros rho' (HagC & HrmL & _ & Himp). rewrite (proj2 (proj2 I18_eq)).
    eapply (@etriple_conseq segsA (fun w => exists o' g', out1_ok mE o' /\ mmap_place_ok_none (Z_to_bv 64 0) (out1_model mE o') pgw g'
                                              /\ tpL = out1_tp mE o' (TP18 rhoC) /\ rw rhoL NA = out1_base mE o' /\ rw rhoL NG = g'
                                              /\ rm_kept_outside (fst (out1_W mE o')) (snd (out1_W mE o')) (rho0C rhoC md ms) rhoL
                                              /\ SPA segsA (KxA (mgrant (out1_model mE o') g') B18) I18c rho' tpL w)); [intros w Hw | intros w Hw; exact Hw |].
    { destruct Hw as [HsmW HJW]. unfold J_ofPA, JL_ok in HJW. destruct HJW as (_ & o' & g' & Ho' & Hpl' & Etp' & HNA' & HNG' & Hkept' & HK').
      exists o', g'. split; [exact Ho'|]. split; [exact Hpl'|]. split; [exact Etp'|]. split; [exact HNA'|]. split; [exact HNG'|]. split; [exact Hkept'|]. split; [exact HsmW | unfold B18; exact HK']. }
    apply etriple_ex; intros o'. apply etriple_ex; intros g'. apply etriple_pure; intros Ho'. apply etriple_pure; intros Hpl'. apply etriple_pure; intros Etp'.
    apply etriple_pure; intros HNA'. apply etriple_pure; intros HNG'. apply etriple_pure; intros Hkept'.
    pose proof (out18_Wok (O18b o') Ho') as HW'. cbn [out18_W out1_W fst snd] in HW'. pose proof q12x_lo as QLO.
    pose proof (grp_facts o' g' Hpl') as (G1 & G2 & G3 & G4 & G5).
    assert (E148 : rw rho' 148%positive = out1_base mE o').
    { specialize (Himp NA). rewrite NPRE, NC, NX2, IM2 in Himp. cbn [eval] in Himp. rewrite <- HNA'. symmetry. apply Himp; [exact PV1 | cbv; lia]. }
    assert (E149 : rw rho' 149%positive = g').
    { pose proof (Himp NG) as Hg. rewrite NPRE, NC, NX2, IM3 in Hg. cbn [eval] in Hg. rewrite <- HNG'. symmetry. apply Hg; [exact PV2 | cbv; lia]. }
    eapply etriple_conseq; [intros w Hw; exact Hw | |].
    2:{ apply (eafter18c (mgrant (out1_model mE o') g') B18 rho' tpL (bv_unsigned (out1_base mE o')) (bv_unsigned g') (HFof18 rho' HagC)).
        - rewrite E148. reflexivity.
        - destruct HW' as [HW'|(W1 & W2 & W3 & W4 & W5 & W6)]; unfold TOPz in *; klia.
        - rewrite E149. reflexivity.
        - unfold TOPz in G3. klia.
        - intros z Hz. unfold band in Hz. destruct HW' as [HW'|(W1 & W2 & W3 & W4 & W5 & W6)]; [klia|]. unfold SHADOW_BAND_LO, SHADOW_BAND_HI in W6. klia.
        - intros z Hz. unfold band in Hz. klia. }
    intros w (rho4 & Q1 & Q2 & Q3 & Q4). exists (O18c o' g'), rho4. split; [split; [exact Ho' | exact Hpl']|].
    split; [intros i0 Hi0; rewrite (Q1 i0 Hi0); symmetry; apply (proj1 HagC); exact Hi0|].
    split; [intros l; rewrite (Q2 l); symmetry; apply (proj2 HagC)|].
    split; [intros a Ha; exact (rm_back18 md ms rhoL rho' rho4 (O18b o') a Ho' Ha (Q3 a (boh18 (fun z => ~ (bv_unsigned (out1_base mE o') + 4096 <= z < bv_unsigned (out1_base mE o') + 8192) /\ ~ (bv_unsigned g' <= z < bv_unsigned g' + 4096)) a Ha)) (HrmL a) Hkept')|].
    split; [intros a Ha Hg; exact (rm_back18L md ms rhoL rho' rho4 (O18b o') a Ho' Ha (Q3 a ltac:(right; right; split; [exact (lowb_bandw rhoC _ Ha) | cbv beta; split; [pose proof (BANDW18L (O18b o') a Ho' Ha) as WW; cbn [out18_W out1_W fst snd] in WW; lia | exact Hg]])) (HrmL a) Hkept')|].
    pose proof (TP18_out18 rhoC (O18b o') HV Hx1 V35 H1 H2 H3 Ho') as TT. cbn [out18_tp] in TT. rewrite Etp', TT in Q4. exact Q4.
Qed.

Lemma ecall18_core : ltac2:(tb__ "0|0|
Sd6S35A1Sd9S69Sa4S69Sa7S35S3bA2S8fVrhoC;S3cVrhoC;A1A5S3fVrhoC;A1A3F_;").
Proof using All.
  intros HLIM.
  apply (call_completePA3 segsA (KxA mE B18pre) (KxM mE B18pre) C18 Pre_M s18 R18 (Posts_M mE B18pre) [] (PostC18 rhoC) rhoC (TP18 rhoC)).
  - intros r [].
  - exact ent18.
  - exact chk18.
  -
    intros rho1 tp1. exact (musl_malloc40_sum_ex_A mE B18pre (m40_mE HLIM) rho1 tp1).
  -
    intros tr ms md Hsm HK. split; [exact HK|].
    pose proof (rho0C_facts rhoC md ms) as (_ & _ & _ & E10). unfold rho0C in E10. rewrite E10, top_mE.
    unfold SP18. unfold x1 in Hx1. rewrite (U_add_slit' rhoC (SVar 1%positive) (-240)) by (cbn [eval]; rewrite ?Hx1; lia). cbn [eval]. rewrite Hx1.
    unfold TOPz, D_M. lia.
  -
    intros L JL tr ms md rhoL tpL tr' ms' md' HinL HsmC HK HagL HsmL HJL.
    change (rho_sub (rho_absorb rhoC R18 (vms md (TP18 rhoC) ms)) s18) with (rho0C rhoC md ms) in HagL, HJL |- *.
    destruct HinL as [E|[E|[E|[]]]]; injection E as EL EJ; subst L JL.
    + exact (econt18a md ms rhoL tpL tr' md' HagL HJL).
    + exact (econt18b md ms rhoL tpL tr' md' HagL HJL).
    + exact (econt18c md ms rhoL tpL tr' md' HagL HJL).
Qed.
End CallSite18.

Lemma call18 : ltac2:(tb__ "0|3|
S1cS3aR1A1S0S6SacR2A1Vx;A3S0S18Q40M0A1M1S1bR3P24A2Vb7;A3S0G1S1bR4P4dA2Vb8;A3S0G1S1bR5P4eA2Vb9;A3S0G1S1bR6P53A2Vb10;A3S0S6SdZ8S19G0S1bR7P23A2A2A2S19G0Vb6;A2A3S8S9Vx;Z50A2S36R8A1A2S8S9S36R9A1Z10M2A2SeZ2Z2fA2A2S8S9S36RaA1G2A2S9Vx;Z2228cfA2A2S0G1S1bRbP54A2S1aG0S3dA2A3S0G1S1bRcP55A2S1aG0SbS41S36RcA1A1S3dA2A2A3Sa8S20S23RdA1S22S90A1A3S100ReA1SdaS69Vok;Sa4S69Sa7S35S3bA2S8fRfS3cRfA1A5S3fRfA1A4F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FrhoC;").
Proof using All.
  intros rhoC HV Hx1 H36 H77 H78 H83 V35 H1 H2 H3 R84 R85 HF HAL.
  apply (triple_pre_fact ok _ _ (ivs_wf (vm_maps (m_vmmaps mE)) /\ lazy_in_maps mE)).
  - intros [tr [ms md]] [(Hsm & HMI & _) (_ & Hem & _)]. cbn [w_tr w_cfg cfg_model fst snd] in Hem, HMI.
    pose proof (erase_mat_eq_fields md mE Hem) as (Evm & Elz & _). destruct HMI as (_ & _ & _ & _ & _ & _ & (HW & _) & HL & _).
    unfold lazy_in_maps in HL |- *. rewrite <- Elz, <- Evm. split; [exact HW | exact HL].
  - intros [MWF HLIM]. exact (call18_core rhoC HV Hx1 H36 H77 H78 H83 V35 H1 H2 H3 R84 R85 HF HAL MWF HLIM).
Qed.

Definition Post18 (rho : valuation) : assn := ltac2:(tb__ "0|8|
Sd8S4S38S38S4S1cS1cS1S40R2A1S1S7Sf8R1P54M0A2S0S18Q40M1A1M2S1bR3R2A2S1bVrho;R2A2A3F_;Fi;S1S7S0S59S18Q8A1M3A1S26R2R1A2S26Vrho;R1A2A3Fl;S1S0G2S1bR1G0A2S1aG1S3dA2A3S1S0G2S1bR1P55A2S1aG1SbS41S36Vrho;A1M4A1S3dA2A2A3S1S4dG4R1A2S1Se2Vrho;R1A2S1G2S42Vrho;S19G1R1A2M5A2S52R4S19G1R2A2M6A2S0S61G3A1S1fR4R3A2S1fVrho;R3A2A3M7F_;F_;Fa;S1G2S3eG5A1S8S10S39S44G4A1A2G6A2G7F_;F_;Fa;Sa4S69Sa7S54R2A1S4fA2S91R1S3cVrho;A1R3A6A2A2A2A2A2A2A2A2A2Lrho';A2Lo;A2Lw;").

Lemma E18_facts35 : ltac2:(tb__ "0|2|
S1S0S5cS89S20S2dS32S2aSfaS25P23A1M0S21Z3A1A3S25P22A1A2A1S22S80SdcA1A1M1A3S5dA3S0S5cS89S20S2dS2eG0S21SbSeZ2Z3dA2Z1A2A1A2A1G1A3S5dA3A2").
Proof. clear. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Lemma V35_of_facts : ltac2:(tb__ "0|1|
S1cS3aR1A1Sa8S20S23R2A1S22S80SdcA1A1A3S0S6SdZ8S19Q40M0S1bR3P23A2A2A2S19G0Vb6;A2A3F_;F_;Frho;").
Proof.
  clear. intros rho HV HF0.
  destruct E18_facts35 as [X1 X2]. pose proof (fact_of_state _ _ rho X1 HF0) as E1. pose proof (fact_of_state _ _ rho X2 HF0) as E2.
  cbn [holds eval] in E2. rewrite Z_to_bv_unsigned in E2. change (bv_wrap 64 (2 ^ 61 - 1)) with (2 ^ 61 - 1) in E2. cbn [holds] in E1.
  apply (f_equal bv_unsigned) in E1. cbn [eval] in E1. rewrite sll_val in E1. change (3 mod 64) with 3 in E1. rewrite Z.shiftl_mul_pow2 in E1 by lia.
  change (2 ^ 3) with 8 in E1. pose proof (urange (rw rho 35%positive)). rewrite Z.mod_small in E1 by lia.
  destruct HV as (_ & _ & _ & _ & _ & _ & _ & H34 & _). rewrite H34 in E1. lia.
Qed.

Lemma TP18_ext : ltac2:(tb__ "0|1|
S1cS1cS7Sf8R1P54A2S0S18Q40A1M0S1bR3R2A2S1bR4R2A2A3F_;Fi;S7S0S59S18Q8A1A1S26R3R1A2S26R4R1A2A3Fl;S0S59G0A1S3cR3A1S3cR4A1A3F_;F_;Frho';Frho;").
Proof.
  clear. intros rho rho' Hrw Hrl. unfold TP18, r6of, TP17. rewrite (Hrw 6%positive) by lia.
  rewrite (TP16_ext rho rho') by (split; [intros i Hi; apply Hrw; lia | exact Hrl]). reflexivity.
Qed.

Theorem seg18 : ltac2:(tb__ "0|2|
S1cS3aR1A1S0S18Q40A1M0S1bR2P24A2Vb7;A3S0G0S1bR3P4dA2Vb8;A3S0G0S1bR4P4eA2Vb9;A3S0G0S1bR5P53A2Vb10;A3S0S6SacR6A1Vx;A3S8S9Vx;Z50A2S36R7A1A2S8S9S36R8A1Z10M1A2SeZ2Z2fA2A2S8S9S36R9A1G1A2S9Vx;Z2228cfA2A2S4aRaA1S100RbA1SdaS69Vok;Sa4S69Sa7S35S48A2SdcRcSaeRcA1A5S50RcA1A4F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Frho;").
Proof using All.
  intros rho HV H36 H77 H78 H83 Hx1 H1 H2 H3 HSZ HAL0.
  pose proof (arith18 _ H1 H2 H3) as AR.
  destruct AR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & A14 & _ & _ & _ & A18 & _).
  apply triple_factsA. intros HF0.
  pose proof (V35_of_facts rho HV HF0) as V35.

  eapply triple_conseq; [intros w Hw; exact (ghost18 rho w Hx1 H1 H2 H3 Hw) | intros w Hw; exact Hw |].
  set (rho1 := rho18g rho).
  assert (R1 : forall i, i <> 84%positive -> i <> 85%positive -> rw rho1 i = rw rho i) by (intros i Ha Hb; unfold rho1, rho18g; rewrite !rho_set_rw_other by lia; reflexivity).
  assert (L1 : forall l, rl rho1 l = rl rho l) by (intros l; reflexivity).
  assert (M1 : forall a, rm rho1 a = rm rho a) by (intros a; reflexivity).
  assert (HV1 : vals rho1) by (unfold vals; eapply (vals12_agree _ _ _ _ _ _ _ 84%positive rho rho1); [lia | exact HV | intros i Hi; apply R1; lia]).
  assert (H36a : rw rho1 36%positive = b7) by (rewrite R1 by lia; exact H36).
  assert (H77a : rw rho1 77%positive = b8) by (rewrite R1 by lia; exact H77).
  assert (H78a : rw rho1 78%positive = b9) by (rewrite R1 by lia; exact H78).
  assert (H83a : rw rho1 83%positive = b10) by (rewrite R1 by lia; exact H83).
  assert (Hx1a : x1 rho1 = x) by (unfold x1; rewrite R1 by lia; exact Hx1).
  assert (R6a : r6of rho1 = r6of rho) by (unfold r6of; rewrite R1 by lia; reflexivity).
  assert (V35a : 8 * bv_unsigned (rw rho1 35%positive) = bv_unsigned b6) by (rewrite R1 by lia; exact V35).
  assert (T17 : TP17 rho1 = TP17 rho) by (unfold TP17; rewrite (TP16_ext rho rho1) by (split; [intros i Hi; apply R1; lia | exact L1]); reflexivity).
  assert (T18 : TP18 rho1 = TP18 rho) by (apply TP18_ext; [intros i Hi; apply R1; lia | exact L1]).
  assert (HSZ1 : SZ18 rho1).
  { destruct HSZ as [Z1 Z2]. split; [intros z Hz; rewrite M1; apply Z1; exact Hz|]. intros Hpm z Hz. rewrite M1. apply Z2; [|exact Hz].
    rewrite <- (TP16_ext rho rho1) by (split; [intros i Hi; apply R1; lia | exact L1]). exact Hpm. }
  assert (G84 : rw rho1 84%positive = Z_to_bv 64 XBz) by (unfold rho1, rho18g; rewrite rho_set_rw_other by lia; apply rho_set_rw_at).
  assert (G85 : rw rho1 85%positive = Z_to_bv 64 (XEz (r6of rho) - XBz)) by (unfold rho1, rho18g; apply rho_set_rw_at).
  rewrite <- T17.

  eapply (@triple_conseq segsA ok (fun w => exists rho2, (forall i, rw rho2 i = rw rho1 i) /\ (forall l, rl rho2 l = rl rho1 l) /\ ZX18 (r6of rho1) rho2
                                                 /\ (forall a : word, bv_unsigned a < Q18 \/ Z.max Q18 (Wz (r6of rho)) <= bv_unsigned a -> rm rho2 a = rm rho1 a)
                                                 /\ SPA segsA (KxA mE B18pre) C18 rho2 (TP18 rho1) w)); [intros [tr [ms md]] Hw | intros w Hw; exact Hw |].
  { apply shape18 in Hw.
    destruct (pay18 rho1 tr ms md HV1 Hx1a H36a H77a H78a H83a V35a ltac:(rewrite R6a; exact H1) ltac:(rewrite R6a; exact H2) ltac:(rewrite R6a; exact H3) HSZ1 Hw)
      as (rho2 & Hsp2 & Hrw2 & Hrl2 & HZ2 & Hrm2).
    exists rho2. split; [exact Hrw2|]. split; [exact Hrl2|]. split; [exact HZ2|].
    split.
    { intros a Ha. apply Hrm2. rewrite R6a. exact Ha. }
    apply (publish18 (KxA mE B18pre) rho2 (TP18 rho1) _); try (rewrite ?Hrw2; assumption).
    - unfold vals; eapply (vals12_agree _ _ _ _ _ _ _ 84%positive rho1 rho2); [lia | exact HV1 | intros i Hi; apply Hrw2].
    - unfold x1. rewrite Hrw2. exact Hx1a.
    - unfold r6of. rewrite Hrw2. fold (r6of rho1). rewrite R6a. exact H1.
    - unfold r6of. rewrite Hrw2. fold (r6of rho1). rewrite R6a. exact H2.
    - unfold r6of. rewrite Hrw2. fold (r6of rho1). rewrite R6a. exact H3.
    - unfold r6of. rewrite !Hrw2. fold (r6of rho1). rewrite R6a. exact G85.
    - unfold r6of. rewrite Hrw2. fold (r6of rho1). exact HZ2. }
  apply triple_ex; intros rho2. apply triple_pure; intros Hrw2. apply triple_pure; intros Hrl2. apply triple_pure; intros HZ2. apply triple_pure; intros HM2.
  assert (R6b : r6of rho2 = r6of rho) by (unfold r6of; rewrite Hrw2; fold (r6of rho1); exact R6a).
  assert (T18b : TP18 rho2 = TP18 rho1) by (apply TP18_ext; [intros i Hi; apply Hrw2 | exact Hrl2]).
  rewrite <- T18b.
  eapply triple_conseq; [intros w Hw; exact Hw | |].
  2:{ apply triple_factsA. intros HFC. cbn [ax_S] in HFC.
      apply (call18 rho2); try (rewrite ?Hrw2; assumption).
      - unfold vals; eapply (vals12_agree _ _ _ _ _ _ _ 84%positive rho1 rho2); [lia | exact HV1 | intros i Hi; apply Hrw2].
      - unfold x1. rewrite Hrw2. exact Hx1a.
      - rewrite R6b. exact H1.
      - rewrite R6b. exact H2.
      - rewrite R6b. exact H3.
      - rewrite R6b, Hrw2. exact G85.
      - apply (arg_layout_ext rho rho2); [intros i Hi; rewrite Hrw2; apply R1; lia | exact HAL0]. }

  intros w (o & rho4 & Ho & Q1 & Q2 & Q3 & Q3L & Q4). exists o, rho4. split; [exact Ho|].
  split; [intros i Hi; rewrite (Q1 i) by lia; rewrite Hrw2; apply R1; lia|].
  split; [intros l; rewrite (Q2 l), Hrl2; apply L1|].
  split; [rewrite (Q1 84%positive) by lia; rewrite Hrw2; exact G84|].
  split; [rewrite (Q1 85%positive) by lia; rewrite Hrw2; exact G85|].
  split.
  - pose proof q12x_lo as QLO. intros z Hz. rewrite Q3; [apply HZ2; rewrite R6a; exact Hz|]. left. unfold band. rewrite u64_of_lit by klia. klia.
  - split.
    +
      assert (E2lo : forall i, (i < 7)%positive -> rw rho2 i = rw rho i) by (intros i Hi; rewrite Hrw2; apply R1; lia).
      intros a Ha. rewrite (Q3 a) by (right; apply (proj2 (ARGF_ext rho rho2 a E2lo)); exact Ha).
      rewrite (HM2 a) by (right; destruct Ha as [Ha _]; unfold x1 in Hx1; unfold kHighMemBeg in *; lia). apply M1.
    + split.
      *
        pose proof (arith18 _ H1 H2 H3) as AR3.
        destruct AR3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Q19 & _).
        intros a Ha Hg.
        assert (HaL : lowb rho2 (bv_unsigned a)) by (unfold lowb, priZ in *; rewrite Hrw2, (R1 31%positive) by lia; exact Ha).
        rewrite (Q3L a HaL Hg). rewrite (HM2 a) by (left; destruct Ha as (HaQ & _ & _); lia). apply M1.
      * split.
        --
           intros a Ha Hhi. rewrite (Q3 a) by (left; exact Ha). rewrite (HM2 a) by (right; exact Hhi). apply M1.
        -- rewrite T18b, T18 in Q4. exact Q4.
Qed.

Lemma pages_rev_In : ltac2:(tb__ "0|0|
S6S5eS5eS109R1R2A2S88S18Q40A1S118R4R2A2S117R4R3A2A3F_;Fk;Fn;Fq;").
Proof.
  clear. intros q n. induction n as [|n IH]; intros k Hk; [lia|]. cbn [pages_rev].
  destruct (Nat.eq_dec k n) as [->|Hne]; [left; reflexivity | right; apply IH; lia].
Qed.

Lemma SZ18_of_RM6 : ltac2:(tb__ "0|1|
S1cS1cS3aR2A1S0S6SacR3A1Vx;A3S0S6SdZ8S19Q40M0S1bR4P23A2A2A2S19G0Vb6;A2A3S106R5A1Sb8R6R5A2S7Sf8R1P4fA2S0S18G0A1S1bR8R2A2S1bR9R2A2A3F_;Fi;S7S0S59S18Q8A1A1S26R8R1A2S26R9R1A2A3Fl;S4aR8A1F_;F_;F_;F_;F_;F_;F_;Frho;Frho0;").
Proof using HPL HPL4 HPL5 HPL6 Hmaps Hres Htop Hx H16 Hxtop.
  clear OKF OKP Hlz HBlim Hsb Hbrk Hbal HPL10 Ha1 Ha2.
  intros rho0 rho HV Hx1 V35 Hz (R1 & R2 & _) Hrw Hrl.
  pose proof CAx as CA. cbv zeta in CA. destruct CA as (Ct & CHPlo & CPEhi & CPEHP & CHPq & CPEe & CPEal & CLIM & CLIM0 & CPB & CLEN & Ce12al).
  unfold x1 in Hx1. cbv zeta in R1, R2. unfold x1 in R1, R2. rewrite Hx1 in R1, R2.
  assert (T16 : TP16 rho = TP16 rho0) by (apply TP16_ext; split; [intros i Hi; apply Hrw; lia | exact Hrl]).
  destruct (n16_val x Hx H16) as [N16 N16b]. destruct (site_arith x Hx H16) as (_ & SQlo & _ & _ & SQPE & SEND & _).
  unfold stackshadow_zero in Hz.
  assert (Eq12 : q12 rho0 = q12x x) by (unfold q12, q12x, shZ, shx; rewrite Hx1; reflexivity).
  assert (Ee12 : e12 rho0 = e12x x) by (unfold e12, e12x, shZ, shx; rewrite Hx1; reflexivity).
  pose proof (pagedown_props (x / 8 + 2147450880 - 131072)) as [AQ RQ]. pose proof (pagedown_props (x / 8 + 2147450880 - 9)) as [AE RE].
  change (x / 8 + 2147450880 - 131072 - (x / 8 + 2147450880 - 131072) mod 4096) with (q12x x) in AQ, RQ.
  change (x / 8 + 2147450880 - 9 - (x / 8 + 2147450880 - 9) mod 4096) with (e12x x) in AE, RE.
  apply Z.mod_divide in AQ as [tq Htq]; [|lia]. apply Z.mod_divide in AE as [te Hte]; [|lia].
  assert (Hxd : 17591917608960 <= x / 8 <= 17592186044416) by (split; [apply (Z.div_le_lower_bound x 8); lia | apply (Z.div_le_upper_bound x 8); lia]).
  assert (Hn : Z.of_nat (n12 rho0) = te - tq + 1).
  { unfold n12. rewrite Eq12, Ee12, Htq, Hte. replace (te * 4096 - tq * 4096) with ((te - tq) * 4096) by lia. rewrite Z_div_mult by lia. rewrite Z2Nat.id; lia. }
  split.
  -
    intros z Hzr. unfold Q18 in Hzr. apply R2. clear -Hzr SQlo Ct. lia.
  - intros Hpm z Hzr. unfold Q18 in *. unfold kHighMemBeg in *.
    destruct (Z_lt_dec z (PEz x + 512 * tcls x)) as [LT|GE]; [apply R2; clear -Hzr LT SQlo SQPE Ct; lia|].

    rewrite T16 in Hpm. apply page_mem_In in Hpm. unfold TP16 in Hpm. unfold x1 in Hpm. rewrite Hx1 in Hpm.
    assert (H12 : In (Z_to_bv 64 (PEz x)) (TP12 rho0)).
    { apply in_app_iff in Hpm as [Hpm|Hpm].
      - exfalso. apply In_pages_rev in Hpm as (k & Hk & Ek). apply (f_equal bv_unsigned) in Ek. apply Nat2Z.inj_lt in Hk. unfold pageZ in Ek.
        rewrite !u64_of_lit in Ek by lia. lia.
      - apply In_enspage_inv in Hpm as [E|Hpm]; [|exact Hpm]. exfalso. apply (f_equal bv_unsigned) in E. rewrite !u64_of_lit in E by lia. lia. }
    unfold TP12 in H12. apply in_app_iff in H12 as [Hpk|Hpk].
    + rewrite Eq12 in Hpk. apply In_pages_rev in Hpk as (k & Hk & Ek). apply (f_equal bv_unsigned) in Ek. unfold pageZ in Ek.
      rewrite !u64_of_lit in Ek by lia. apply Nat2Z.inj_lt in Hk. rewrite Hn in Hk.
      rewrite R1; [apply Hz; rewrite Eq12, Hn; lia | rewrite u64_of_lit by lia; lia | rewrite u64_of_lit by lia; unfold LOWPG; lia].
    + exfalso. unfold TP11 in Hpk.
      pose proof (priZ_facts rho0 HV) as (PR1 & PR2 & PR3 & PR4). pose proof (sbZ_facts' rho0 HV V35) as SB1. unfold x1 in PR1, SB1. rewrite Hx1 in PR1, SB1.
      pose proof (Upri rho0 HV) as UP.
      pose proof (Z.mod_pos_bound (sbZ rho0) 4096 ltac:(lia)) as MB. pose proof (urange (rw rho0 35%positive)) as U35.
      assert (Hpri : 0 <= priZ rho0 /\ priZ rho0 + 12288 + 4096 <= PEz x) by lia.
      assert (Hsb : 0 <= q1Z rho0 /\ q1Z rho0 + 12288 + 4096 <= PEz x) by (unfold q1Z in *; unfold sbZ in *; lia).
      destruct (q1Z rho0 =? priZ rho0);
        repeat (destruct Hpk as [Ep|Hpk]; [apply (f_equal bv_unsigned) in Ep; first [rewrite !u64_of_lit in Ep by lia | rewrite UP, u64_of_lit in Ep by lia]; lia|]); destruct Hpk.
Qed.

Lemma ecall18 : ltac2:(tb__ "0|3|
S1cS3aR1A1S0S6SacR2A1Vx;A3S0S18Q40M0A1M1S1bR3P24A2Vb7;A3S0G1S1bR4P4dA2Vb8;A3S0G1S1bR5P4eA2Vb9;A3S0G1S1bR6P53A2Vb10;A3S0S6SdZ8S19G0S1bR7P23A2A2A2S19G0Vb6;A2A3S8S9Vx;Z50A2S36R8A1A2S8S9S36R9A1Z10M2A2SeZ2Z2fA2A2S8S9S36RaA1G2A2S9Vx;Z2228cfA2A2S0G1S1bRbP54A2S1aG0S3dA2A3S0G1S1bRcP55A2S1aG0SbS41S36RcA1A1S3dA2A2A3Sa8S20S23RdA1S22S90A1A3S100ReA1Sd9S69Sa4S69Sa7S35S3bA2S8fRfS3cRfA1A5S3fRfA1A3F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FrhoC;").
Proof using All.
  intros rhoC HV Hx1 H36 H77 H78 H83 V35 H1 H2 H3 R84 R85 HF HAL.
  apply (etriple_pre_fact _ _ (ivs_wf (vm_maps (m_vmmaps mE)) /\ lazy_in_maps mE)).
  - intros [tr [ms md]] [(Hsm & HMI & _) (_ & Hem & _)]. cbn [w_tr w_cfg cfg_model fst snd] in Hem, HMI.
    pose proof (erase_mat_eq_fields md mE Hem) as (Evm & Elz & _). destruct HMI as (_ & _ & _ & _ & _ & _ & (HW & _) & HL & _).
    unfold lazy_in_maps in HL |- *. rewrite <- Elz, <- Evm. split; [exact HW | exact HL].
  - intros [MWF HLIM]. exact (ecall18_core rhoC HV Hx1 H36 H77 H78 H83 V35 H1 H2 H3 R84 R85 HF HAL MWF HLIM).
Qed.

Theorem eseg18 : ltac2:(tb__ "0|2|
S1cS3aR1A1S0S18Q40A1M0S1bR2P24A2Vb7;A3S0G0S1bR3P4dA2Vb8;A3S0G0S1bR4P4eA2Vb9;A3S0G0S1bR5P53A2Vb10;A3S0S6SacR6A1Vx;A3S8S9Vx;Z50A2S36R7A1A2S8S9S36R8A1Z10M1A2SeZ2Z2fA2A2S8S9S36R9A1G1A2S9Vx;Z2228cfA2A2S4aRaA1S100RbA1Sd9S69Sa4S69Sa7S35S48A2SdcRcSaeRcA1A5S50RcA1A3F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Frho;").
Proof using All.
  intros rho HV H36 H77 H78 H83 Hx1 H1 H2 H3 HSZ HAL0.
  pose proof (arith18 _ H1 H2 H3) as AR.
  destruct AR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & A14 & _ & _ & _ & A18 & _).
  apply etriple_factsA. intros HF0.
  pose proof (V35_of_facts rho HV HF0) as V35.

  eapply etriple_conseq; [intros w Hw; exact (ghost18 rho w Hx1 H1 H2 H3 Hw) | intros w Hw; exact Hw |].
  set (rho1 := rho18g rho).
  assert (R1 : forall i, i <> 84%positive -> i <> 85%positive -> rw rho1 i = rw rho i) by (intros i Ha Hb; unfold rho1, rho18g; rewrite !rho_set_rw_other by lia; reflexivity).
  assert (L1 : forall l, rl rho1 l = rl rho l) by (intros l; reflexivity).
  assert (M1 : forall a, rm rho1 a = rm rho a) by (intros a; reflexivity).
  assert (HV1 : vals rho1) by (unfold vals; eapply (vals12_agree _ _ _ _ _ _ _ 84%positive rho rho1); [lia | exact HV | intros i Hi; apply R1; lia]).
  assert (H36a : rw rho1 36%positive = b7) by (rewrite R1 by lia; exact H36).
  assert (H77a : rw rho1 77%positive = b8) by (rewrite R1 by lia; exact H77).
  assert (H78a : rw rho1 78%positive = b9) by (rewrite R1 by lia; exact H78).
  assert (H83a : rw rho1 83%positive = b10) by (rewrite R1 by lia; exact H83).
  assert (Hx1a : x1 rho1 = x) by (unfold x1; rewrite R1 by lia; exact Hx1).
  assert (R6a : r6of rho1 = r6of rho) by (unfold r6of; rewrite R1 by lia; reflexivity).
  assert (V35a : 8 * bv_unsigned (rw rho1 35%positive) = bv_unsigned b6) by (rewrite R1 by lia; exact V35).
  assert (T17 : TP17 rho1 = TP17 rho) by (unfold TP17; rewrite (TP16_ext rho rho1) by (split; [intros i Hi; apply R1; lia | exact L1]); reflexivity).
  assert (T18 : TP18 rho1 = TP18 rho) by (apply TP18_ext; [intros i Hi; apply R1; lia | exact L1]).
  assert (HSZ1 : SZ18 rho1).
  { destruct HSZ as [Z1 Z2]. split; [intros z Hz; rewrite M1; apply Z1; exact Hz|]. intros Hpm z Hz. rewrite M1. apply Z2; [|exact Hz].
    rewrite <- (TP16_ext rho rho1) by (split; [intros i Hi; apply R1; lia | exact L1]). exact Hpm. }
  assert (G84 : rw rho1 84%positive = Z_to_bv 64 XBz) by (unfold rho1, rho18g; rewrite rho_set_rw_other by lia; apply rho_set_rw_at).
  assert (G85 : rw rho1 85%positive = Z_to_bv 64 (XEz (r6of rho) - XBz)) by (unfold rho1, rho18g; apply rho_set_rw_at).
  rewrite <- T17.

  eapply (@etriple_conseq segsA (fun w => exists rho2, (forall i, rw rho2 i = rw rho1 i) /\ (forall l, rl rho2 l = rl rho1 l) /\ ZX18 (r6of rho1) rho2
                                                 /\ (forall a : word, bv_unsigned a < Q18 \/ Z.max Q18 (Wz (r6of rho)) <= bv_unsigned a -> rm rho2 a = rm rho1 a)
                                                 /\ SPA segsA (KxA mE B18pre) C18 rho2 (TP18 rho1) w)); [intros [tr [ms md]] Hw | intros w Hw; exact Hw |].
  { apply shape18 in Hw.
    destruct (pay18 rho1 tr ms md HV1 Hx1a H36a H77a H78a H83a V35a ltac:(rewrite R6a; exact H1) ltac:(rewrite R6a; exact H2) ltac:(rewrite R6a; exact H3) HSZ1 Hw)
      as (rho2 & Hsp2 & Hrw2 & Hrl2 & HZ2 & Hrm2).
    exists rho2. split; [exact Hrw2|]. split; [exact Hrl2|]. split; [exact HZ2|].
    split.
    { intros a Ha. apply Hrm2. rewrite R6a. exact Ha. }
    apply (publish18 (KxA mE B18pre) rho2 (TP18 rho1) _); try (rewrite ?Hrw2; assumption).
    - unfold vals; eapply (vals12_agree _ _ _ _ _ _ _ 84%positive rho1 rho2); [lia | exact HV1 | intros i Hi; apply Hrw2].
    - unfold x1. rewrite Hrw2. exact Hx1a.
    - unfold r6of. rewrite Hrw2. fold (r6of rho1). rewrite R6a. exact H1.
    - unfold r6of. rewrite Hrw2. fold (r6of rho1). rewrite R6a. exact H2.
    - unfold r6of. rewrite Hrw2. fold (r6of rho1). rewrite R6a. exact H3.
    - unfold r6of. rewrite !Hrw2. fold (r6of rho1). rewrite R6a. exact G85.
    - unfold r6of. rewrite Hrw2. fold (r6of rho1). exact HZ2. }
  apply etriple_ex; intros rho2. apply etriple_pure; intros Hrw2. apply etriple_pure; intros Hrl2. apply etriple_pure; intros HZ2. apply etriple_pure; intros HM2.
  assert (R6b : r6of rho2 = r6of rho) by (unfold r6of; rewrite Hrw2; fold (r6of rho1); exact R6a).
  assert (T18b : TP18 rho2 = TP18 rho1) by (apply TP18_ext; [intros i Hi; apply Hrw2 | exact Hrl2]).
  rewrite <- T18b.
  eapply etriple_conseq; [intros w Hw; exact Hw | |].
  2:{ apply etriple_factsA. intros HFC. cbn [ax_S] in HFC.
      apply (ecall18 rho2); try (rewrite ?Hrw2; assumption).
      - unfold vals; eapply (vals12_agree _ _ _ _ _ _ _ 84%positive rho1 rho2); [lia | exact HV1 | intros i Hi; apply Hrw2].
      - unfold x1. rewrite Hrw2. exact Hx1a.
      - rewrite R6b. exact H1.
      - rewrite R6b. exact H2.
      - rewrite R6b. exact H3.
      - rewrite R6b, Hrw2. exact G85.
      - apply (arg_layout_ext rho rho2); [intros i Hi; rewrite Hrw2; apply R1; lia | exact HAL0]. }

  intros w (o & rho4 & Ho & Q1 & Q2 & Q3 & Q3L & Q4). exists o, rho4. split; [exact Ho|].
  split; [intros i Hi; rewrite (Q1 i) by lia; rewrite Hrw2; apply R1; lia|].
  split; [intros l; rewrite (Q2 l), Hrl2; apply L1|].
  split; [rewrite (Q1 84%positive) by lia; rewrite Hrw2; exact G84|].
  split; [rewrite (Q1 85%positive) by lia; rewrite Hrw2; exact G85|].
  split.
  - pose proof q12x_lo as QLO. intros z Hz. rewrite Q3; [apply HZ2; rewrite R6a; exact Hz|]. left. unfold band. rewrite u64_of_lit by klia. klia.
  - split.
    +
      assert (E2lo : forall i, (i < 7)%positive -> rw rho2 i = rw rho i) by (intros i Hi; rewrite Hrw2; apply R1; lia).
      intros a Ha. rewrite (Q3 a) by (right; apply (proj2 (ARGF_ext rho rho2 a E2lo)); exact Ha).
      rewrite (HM2 a) by (right; destruct Ha as [Ha _]; unfold x1 in Hx1; unfold kHighMemBeg in *; lia). apply M1.
    + split.
      *
        pose proof (arith18 _ H1 H2 H3) as AR3.
        destruct AR3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Q19 & _).
        intros a Ha Hg.
        assert (HaL : lowb rho2 (bv_unsigned a)) by (unfold lowb, priZ in *; rewrite Hrw2, (R1 31%positive) by lia; exact Ha).
        rewrite (Q3L a HaL Hg). rewrite (HM2 a) by (left; destruct Ha as (HaQ & _ & _); lia). apply M1.
      * split.
        --
           intros a Ha Hhi. rewrite (Q3 a) by (left; exact Ha). rewrite (HM2 a) by (right; exact Hhi). apply M1.
        -- rewrite T18b, T18 in Q4. exact Q4.
Qed.
End Seg7.
