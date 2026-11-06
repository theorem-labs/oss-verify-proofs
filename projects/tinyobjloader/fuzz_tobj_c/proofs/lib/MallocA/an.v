(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia FunctionalExtensionality.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aj SpineCallocIo RefillJ bc.

(* [comment removed for export] *)
Module SpineMallocS3.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "entailsA"; "axst"; "ax_setS"; "@Corelib.Init.Datatypes"; "bool"; "true"; "list"; "prod"; "app"; "cons"; "nil"; "pair"; "andb"; "Some"; "option"; "fst"; "length"; "snd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sobj"; "sprop"; "swf"; "valuation"; "SVar"; "ss_next"; "ss_facts"; "SLit"; "obj_range"; "rw"; "ss_objs"; "sprop_below"; "SPBranch"; "holds"; "ob_base"; "ob_hi"; "ob_lo"; "rm"; "sstate"; "SPNot"; "eval"; "mkSS"; "smatch"; "sprop_eqb"; "ss_fcsr"; "ss_fregs"; "ss_lenient"; "ss_pc"; "ss_regs"; "ss_resv"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "leb"; "mul"; "modulo"; "pow"; "eqb"; "lt"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3"; "skel"; "X2"; "X2r"; "X1"; "X1b"; "X1c"; "X1r"; "cls_ok8"; "inclb"; "@Corelib.Lists.ListDef"; "map"; "Forall"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "ulink"; "unwind_objs"; "A_globals"; "KcA"; "Kc_ok"; "UStopLeOrPc"; "V_DEPTH"; "malloc_depth"; "pre_facts"; "unwind_factsS"; "ustop"; "F_sp_high"; "J_alloc_preT"; "chain_pre"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1"; "JG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "rho_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP"; "E2a"; "E2b"; "C2p0"; "C2r0"; "F_gen"; "F_cls"; "creg_a"; "creg_b"; "C1g"; "C2p"; "C2r"; "F_pop"; "V_CLS"; "V_ND"; "@Stdlib.Lists.List"; "incl"; "forallb"; "In"; "existsb"; "nth_error"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "bv_signed"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "ag_thread"; "aa_geom"; "ageom"; "aa_cache_inited"; "class_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI"; "cnt_of"; "cls_of"; "stopJ_stable"; "needed8"; "chk_of"; "cst_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "cell_ok"; "mkACell"; "present"; "bview"; "view"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aj.SpineMallocS2"; "E2a'"; "E2b'"; "only_var"; "tab_ok"; "@LinuxProcessSemantics.LinuxProcessSem.MemImageType"; "Segment"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "triple"; "world"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1"; "F_s1"; "RT_m1"; "sw_s1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "ClassID"; "Size"; "max_count"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "AInvA"; "@Corelib.Init.Decimal"; "D8"; "D1"; "D2"; "Nil"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@LinuxProcessSemantics.Riscv.Instr"; "BC_LTU"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3.B1B"; "X2"; "X2r"; "X1"; "X1b"; "X1c"; "X1r"; "@Corelib.Init.Nat"; "of_num_uint"; "sub"; "@Corelib.Init.Number"; "UIntDecimal";
"@Corelib.Init.Peano"; "lt"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "check_cfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws"; "segsA"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA GlueA2 SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SMGlue InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ContractFreeNull.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ContractFreeNullInit.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aj.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aj.SpineMallocS2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Local Ltac liaL := first [ solve [ repeat match goal with K : _ |- _ => clear K end; lia ] | lia ].
Local Ltac liaZ := lazymatch goal with |- gcells_inside _ _ _ _ => fail | |- cells_inside _ _ _ => fail | |- Forall _ _ => fail | |- cells_in_view _ _ _ _ => fail | |- xwords_clear _ _ _ _ => fail | |- forall _, _ => fail | |- (_ <= _)%positive => fail | |- _ => liaL end.

Definition cls_ok8 (n : Z) : bool := ltac2:(tb__ "0|5|
S90S7dVn;A1M0A1S33SeSeSeSeSeSeSeS37Z1M1R1A2S37R1Z1eA2A2S37Z18G0A2A2S37G0S91R1A1M2A2A2S37G2Z10000A2A2S3bS39G2Z10M3A2Z0A2A2S37S92R1A1M4G3A2A2S37G1G4A2A2Tc;").
Lemma cls_ok8_all : ltac2:(tb__ "0|0|
S33S1S35Z1R1A2S35R1Zfc00A2A2S0S6S45R2A1S7A3F_;Fn;").
Proof. intros n Hn. apply (forall_rangeZ_ok cls_ok8 1 64512); [|lia]. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma cls_facts : ltac2:(tb__ "0|6|
S33S1S35Z1M0R1A2S35R1Zfc00A2A2S1S1S35G0S7bR2A1M1A2S35G1Z1eA2A2S1S1S1S35Z18S7dR2A1M2A2S35G2S91G1A1M3A2A2S35G3Z10000A2A2S1S0S33S39G3Z10M4A2Z0A3S1S35G0S92G1A1M5A2S35G5G4A2A2A2A2A2F_;Fn;").
Proof.
  intros n Hn. pose proof (cls_ok8_all n Hn) as H. unfold cls_ok8, cls_of in *.
  repeat (apply andb_prop in H as [H ?X]).
  repeat match goal with K : (_ <=? _) = true |- _ => apply Z.leb_le in K | K : (_ =? _) = true |- _ => apply Z.eqb_eq in K end. lia.
Qed.

Definition skel (o : sobj) : sv * sv * sv := ltac2:(tb__ "0|0|
SdS9S14S14A2S14SdS14S14S23Vo;A1S25Vo;A1A4S24Vo;A1A4").
Lemma obj_range_skel : ltac2:(tb__ "0|0|
S18S15S15S0S9S9S14S14A2S14A2S3eR2A1S3eR1A1A3S0S9S33S33A2S1dR4R3A2S1dR4R2A2A3F_;Fo';Fo;Frho;").
Proof. intros rho [b l h c d] [b' l' h' c' d'] E. cbn in E. injection E as -> -> ->. reflexivity. Qed.
Lemma Forall_ranges_skel : ltac2:(tb__ "0|2|
S18S9S33S33A2OF_;S8S15A1M0G0S0S8S9S9S14S14A2S14A2M1A1S47S15G1S3eR2A4S47S15G1S3eR1A4A3S48S15S15R5S1dR6R1A2A1Lo;R2A3S48S15S15R6S1dR7R1A2A1Lo;R4A3F_;F_;Fl';Fl;FP;Frho;").
Proof.
  intros rho P l. induction l as [|o l IH]; intros [|o' l'] E H; cbn in E; try discriminate; [constructor|].
  assert (Es : skel o = skel o') by congruence. assert (El : map skel l = map skel l') by congruence.
  apply Forall_cons_iff in H as [Ha Hb]. constructor; [rewrite (obj_range_skel rho o o' Es); exact Ha | exact (IH l' El Hb)].
Qed.

Lemma nth_error_last : ltac2:(tb__ "0|1|
S8S33A1Sa5U0S12S33R1A2A2S0S10S33A1S70S33R2Sa3S12S33R2A2U1A2M0A3SfS33S49S33G0R2Z0A4A2A3F_;Fl;").
Proof.
  intros l Hl. destruct (nth_error l (length l - 1)) as [x|] eqn:E.
  - f_equal. symmetry. apply nth_error_nth. exact E.
  - apply nth_error_None in E. lia.
Qed.

Definition inclb (l1 l2 : list sprop) : bool := ltac2:(tb__ "0|0|
S6dS16S16S6fS16S2cR1A1Vl2;A3Lp;Vl1;A3").
Lemma inclb_incl : ltac2:(tb__ "0|1|
S8S16A1M0G0S0S6S46R2R1A2S7A3S6cS16R3R2A3F_;Fl2;Fl1;").
Proof.
  intros l1 l2 H p Hp. pose proof (proj1 (forallb_forall _ _) H p Hp) as E. apply existsb_sprop_eqb in E. exact E.
Qed.

Lemma sw_range_gen : ltac2:(tb__ "0|5|
S8S89A1S18S27S9S8S99A1Sa6A2S15S2bR5R4R3R2A4S6eS15R2S1fR4A1A3S0S9S9S14S14A2M0S14A2S3eR3A1SdG0S14SdS14S14S19PaM1A1S19S53A1A4S1cZ0A1A4A3S22R7S58A2S1S35Z7fff7f800000S11S33S33S1dR8R5A2M2A3M3A2S1S0S33S13S33S33G2A3M4S71Q40S1eR8G1A2A2A3S35G3G4A2A2A2F_;F_;F_;F_;Fo;Fw;FS;Frho;Fsegs;").
Proof.
  intros segs rho S w o Hsm Hin Hsk Hf.
  destruct o as [ob olo ohi ocs od]. cbn in Hsk. injection Hsk as -> -> ->.
  destruct Hsm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hall & _ & _) & _).
  pose proof (proj1 (Forall_forall _ _) Hall _ Hin) as Ho.
  pose proof (stack_win_range segs rho (mkSS 0 [] [] FcsrFrm0 None [stack_win] [] NW2 false) w) as SW.
  unfold obj_holds, obj_lo_of, obj_hi_of in Ho. cbn [ob_base ob_lo ob_hi] in Ho.
  destruct Ho as ((B1 & B2 & B3 & B4) & _).
  unfold obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi fst snd].
  rewrite soff_lit in *. replace (snorm 0) with 0 in * by reflexivity.
  cbn [eval] in *. unfold holds, F_sp_high in Hf. cbn [eval] in Hf. rewrite add_val in Hf.
  rewrite u64_lit in Hf by lia.
  rewrite soff_snorm in *. unfold U in *. cbn [eval] in *.
  pose proof (urange (rw rho 10%positive)) as R10. pose proof (urange (rw rho V_DEPTH)) as R15.
  unfold snorm in *.
  rewrite (Z.mod_small (bv_unsigned (rw rho V_DEPTH)) (2 ^ 64)) in * by lia.
  destruct (Z.ltb_spec (bv_unsigned (rw rho V_DEPTH)) (2 ^ 63)).
  - assert (bv_unsigned (rw rho V_DEPTH) = 0) by lia. rewrite H0 in *. rewrite Z.add_0_r, Z.mod_small in Hf by lia. lia.
  - replace ((bv_unsigned (rw rho 10%positive) + bv_unsigned (rw rho V_DEPTH)) mod 2 ^ 64)
      with (bv_unsigned (rw rho 10%positive) + bv_unsigned (rw rho V_DEPTH) - 2 ^ 64) in Hf.
    2:{ symmetry. replace (bv_unsigned (rw rho 10%positive) + bv_unsigned (rw rho V_DEPTH)) with
          ((bv_unsigned (rw rho 10%positive) + bv_unsigned (rw rho V_DEPTH) - 2 ^ 64) + 1 * 2 ^ 64) at 1 by lia.
        rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
    lia.
Qed.

Lemma pc_entry_facts : ltac2:(tb__ "0|7|
S8S89A1S74S18S8S72Q40A1A1S98S33S93R6R5R4R3R2A5S1S35Z1M0R2A2S35R2Zfc00A2A2S35G0S7aR7R3A2A2S76R8A1S77S7bR5A1S33S7fRaR6A2S79S36S36S75R3A1Zd0A2S38Z50M1R2A2A2S33S84RdS26RbA1A2S83S1S0S6S78RdA1S7A3S1S80R1S81R2U4M2S7aRdR9A2M3A3A2S1S80R1S81S36R2Z8A2U8S91R4A1A3A2S1S80R1S81S36S36R2Z10M4A2S38Z4S3dG3G0A2A2A2G2S7eRdR9A2M5A3A2S1S35G3G4A2S1S1S35Z0G5A2S3cG5S3aZ2Z1cA2A2A2S1S82R1R2S36R2G1A2A3S82R1S36S75R5A1M6Zad0A2S36G6Zc60A2A3A2A2A2A2A2A2A2Tm;Te;Tcs;Tc;TG;F_;F_;F_;Fnv;Fmd;Ftp;Frho;FA;Fsegs;").
Proof.
  intros segs A rho tp md nv HA Hnv Hcnt G c cs e m. unfold e, m, cs, c, G. clear G c cs e m.
  pose proof (cls_facts nv Hnv) as (C1 & C2 & C3 & C4).
  unfold chk_of, cnt_of, cst_of in *.
  set (G := aa_geom A) in *. set (c := cls_of nv) in *. set (m := view segs (rm rho)) in *.
  pose proof HA as (HG & HR & HF & HRest & HM).
  destruct HRest as (Hsep & Hlive & Hprim & _ & _ & _ & _ & HTH & _).
  destruct Hprim as (_ & _ & _ & P4). specialize (P4 c C1).
  assert (MT : forall z, ag_thread G <= z < ag_thread G + 0x1000 -> maskv (fs_footb G) (view segs (rm rho)) z = m z).
  { intros z Hz. apply maskv_out. apply fs_footb_thread; [exact HG | exact Hz]. }
  unfold class_repr in P4.
  destruct P4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & N1 & N2 & N3 & N4 & N5 & N6 & _ & _ & N7 & _ & _ & PE & ND & LV & CI & CN & _ & _ & _ & _).
  set (cs := nthZ (aa_cls A) c cs_empty) in *.
  assert (Hci : aa_cache_inited A = true).
  { destruct (aa_cache_inited A) eqn:E; [reflexivity|]. exfalso. destruct (CN eq_refl) as [Hc0 _].
    rewrite Hc0 in Hcnt. cbn in Hcnt. lia. }
  destruct (CI Hci) as (D1 & D2 & D3 & D4 & D5).
  assert (ER : forall k a v, ag_thread G + 0xd0 <= a -> a + Z.of_nat k <= ag_thread G + 0x1000 ->
             cell_ok (maskv (fs_footb G) (view segs (rm rho))) (mkACell a k v) -> cell_ok m (mkACell a k v)).
  { intros k a v Ha1 Ha2 Hc j Hj. specialize (Hc j Hj). cbn [c_addr c_w c_val] in Hc, Hj |- *. rewrite MT in Hc by lia. exact Hc. }
  split; [exact Hci|].
  split; [apply (ER 4%nat); [lia| cbn; lia | exact D1]|].
  split; [apply (ER 8%nat); [lia | cbn; lia | exact D3]|].
  split.
  { pose proof (nth_error_last (cs_cache cs) ltac:(lia)) as NE.
    specialize (D4 (length (cs_cache cs) - 1)%nat _ NE).
    replace (Z.of_nat (length (cs_cache cs) - 1)) with (Z.of_nat (length (cs_cache cs)) - 1) in D4 by lia.
    apply (ER 4%nat); [lia | cbn; lia | exact D4]. }
  split; [lia|].
  split.
  { assert (Hin : In (nth (length (cs_cache cs) - 1)%nat (cs_cache cs) 0) (cs_free_array cs ++ cs_cache cs)).
    { apply in_or_app. right. apply nth_In. lia. }
    destruct (N7 _ Hin) as (X1 & X2 & X3). unfold kCompactPtrScale in X3. rewrite Z.shiftl_mul_pow2 in X3 by lia.
    unfold kUserSpaceSize, kUserMapSize, kRegionSize, kFreeArraySize in N2, N3. clear -X1 X3 N2 N3 C2. lia. }
  split.
  { intros z Hz. destruct (PE z Hz) as [b Hb]. exists b. rewrite <- (MT z) by lia. exact Hb. }
  unfold thread_inv in HTH. destruct HTH as [_ HTS]. intros z Hz. assert (Hz' : ag_thread (aa_geom A) + 2688 <= z < ag_thread (aa_geom A) + 3168) by (unfold G in Hz; clear -Hz; lia). destruct (HTS z Hz') as [b Hb]. exists b. rewrite <- (MT z) by lia. exact Hb.
Qed.

Lemma pc_entry_facts0 : ltac2:(tb__ "0|3|
S8S89A1S74S18S8S72Q40A1A1S98S33S93R6R5R4R3R2A5S1S35Z1R2A2S35R2Zfc00A2A2S0S33S7aR7R3A2Z0M0A3S76R8A1S77S7bR5A1S33S36S36S75R2A1Zd0A2S38Z50M1R1A2A2S33S84RcS26RaA1A2S83S1S80R1S81R2U4G0A3A2S1S82R1R2S36R2G1A2A3S82R1S36S75R4A1M2Zad0A2S36G2Zc60A2A3A2A2Tm;Te;Tc;TG;F_;F_;F_;Fnv;Fmd;Ftp;Frho;FA;Fsegs;").
Proof.
  intros segs A rho tp md nv HA Hnv Hcnt G c e m. unfold e, m, c, G. clear G c e m.
  pose proof (cls_facts nv Hnv) as (C1 & C2 & C3 & C4).
  unfold cnt_of, cst_of in *.
  set (G := aa_geom A) in *. set (c := cls_of nv) in *. set (m := view segs (rm rho)) in *.
  pose proof HA as (HG & HR & HF & HRest & HM).
  destruct HRest as (Hsep & Hlive & Hprim & _ & _ & _ & _ & HTH & _).
  destruct Hprim as (_ & _ & _ & P4). specialize (P4 c C1).
  assert (MT : forall z, ag_thread G <= z < ag_thread G + 0x1000 -> maskv (fs_footb G) (view segs (rm rho)) z = m z).
  { intros z Hz. apply maskv_out. apply fs_footb_thread; [exact HG | exact Hz]. }
  unfold class_repr in P4.
  destruct P4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & N1 & N2 & N3 & N4 & N5 & N6 & _ & _ & N7 & _ & _ & PE & ND & LV & CI & CN & _ & _ & _ & _).
  set (cs := nthZ (aa_cls A) c cs_empty) in *.
  split.
  { assert (D : cell_ok (maskv (fs_footb G) (view segs (rm rho))) (mkACell (ag_thread G + 208 + 80 * c) 4 0)).
    { destruct (aa_cache_inited A) eqn:E.
      - destruct (CI eq_refl) as (D1 & _). rewrite Hcnt in D1. exact D1.
      - destruct (CN eq_refl) as [_ FL]. intros j Hj. cbn [c_addr c_w RtCells.c_val] in Hj |- *.
        etransitivity; [apply FL; subst G c; lia|].
        rewrite nth_enc_bytes by lia. unfold MallocInv.le_byte. rewrite Z.mod_0_l, Z.shiftr_0_l, Z.mod_0_l by lia. reflexivity. }
    intros j Hj. specialize (D j Hj). cbn [c_addr c_w RtCells.c_val] in D, Hj |- *. rewrite MT in D by lia. exact D. }
  split.
  { intros z Hz. destruct (PE z Hz) as [b Hb]. exists b. rewrite <- (MT z) by lia. exact Hb. }
  unfold thread_inv in HTH. destruct HTH as [_ HTS]. intros z Hz. assert (Hz' : ag_thread (aa_geom A) + 2688 <= z < ag_thread (aa_geom A) + 3168) by (unfold G in Hz; clear -Hz; lia). destruct (HTS z Hz') as [b Hb]. exists b. rewrite <- (MT z) by lia. exact Hb.
Qed.

Lemma sw_lo_gen : ltac2:(tb__ "0|3|
S18S15S0S9S9S14S14A2M0S14A2S3eR1A1SdG0S14SdS14S14S19PaM1A1S19S53A1A4S1cZ0A1A4A3S0S33S11S33S33S1dR3R2A2A3S36S71Q40M2S1eR3G1A2A2S73G2S1eR3S53A2A2A2A3F_;Fo;Frho;").
Proof. intros rho [ob olo ohi ocs od] Hsk. cbn in Hsk. injection Hsk as -> -> ->. reflexivity. Qed.

Lemma unwind_objs_above : ltac2:(tb__ "0|3|
S8S4dA1S18S33S48S16S22R2A1S5aR3A1A3S35R2S71Q40M0S1eR3PaA2A2A2S35Z0M1R3A2S48S15S15S1S1S35S36R5Z10A2S71G0S29R6S23R1A1A2A2M2A2S35G2S3aZ2Z2fA2A2A2S1S0S14S25R1A1S1cN10A1A3S0S14S24R1A1S1cG1A1A3A2A2Lo;S4eR6A1A3F_;F_;F_;FT;Frho;FW;").
Proof.
  intros W rho T HC Hsp HT0. unfold unwind_objs. destruct W as [|l W']; [constructor|].
  unfold chain_pre in HC. cbn [app] in HC.
  pose proof (Forall_inv HC) as X0. pose proof (Forall_inv (Forall_inv_tail HC)) as X1c.
  pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail HC))) as X2. do 3 apply Forall_inv_tail in HC.
  cbn [holds eval] in X0, X1c, X2. rewrite u64_lit in X0 by lia. rewrite add_val, !u64_lit in X1c by lia. rewrite u64_lit in X2 by lia.
  pose proof (urange (rw rho 10%positive)). rewrite Z.mod_small in X1c by lia.
  eapply Forall_impl; [|apply (chain_facts_bases rho (SVar 28) (l :: W') HC); cbn [eval]; lia].
  intros o (B & L & Hh). cbn [eval] in B. repeat split; try assumption; lia.
Qed.

Section B1B.
Let segs : list Segment := segsA.
Variable nW : nat. Variable st : ustop. Variable tmax : Z.
Let W : list ulink := Wcan nW.

Variable X : axst.
Hypothesis HXskel : ltac2:(tb__ "0|1|
S0S8S9S9S14S14A2S14A2M0A1S47S15G0S3eS1fS2VX;A1A1A4S47S15G0S3eSaS15SbS15S8fSaS15S4eVW;A1S4fA3A3S8eA3A4A3").
Hypothesis HXX : ax_X X = [].
Hypothesis HXF : ltac2:(tb__ "0|0|
S6cS16SaS16SaS16SaS16S56VW;Vst;A2S55S54A1A3S8dA3S62A3S1bS2VX;A1A1A3").

Definition addobj (A : axst) (o : sobj) : axst := ltac2:(tb__ "0|0|
S2VA;A1S27S5VA;S2aS30R1A1S31R1A1S2eR1A1S2dR1A1S32R1A1SaS15S1fR1A1SbS15Vo;ScS15A1A3A3S1bR1A1S1aR1A1S2fR1A1A9A2TS;").

Definition X1 : axst := addobj X O_pcc.
Definition X1b : axst := addobj X1 O_pcs.
Definition X1c : axst := addobj X1b O_pck.
Definition X2 : axst := addobj X1c O_st.
Definition X1r : axst := addobj X O_pcc0.
Definition X2r : axst := addobj X1r O_st.
Hypothesis W1 : ltac2:(tb__ "0|0|
S0S6S17S2S9eA1A1S7A3").
Hypothesis W1b : ltac2:(tb__ "0|0|
S0S6S17S2S9fA1A1S7A3").
Hypothesis W1c : ltac2:(tb__ "0|0|
S0S6S17S2Sa0A1A1S7A3").
Hypothesis W2 : ltac2:(tb__ "0|0|
S0S6S17S2S9cA1A1S7A3").
Hypothesis W1r : ltac2:(tb__ "0|0|
S0S6S17S2Sa1A1A1S7A3").
Hypothesis W2r : ltac2:(tb__ "0|0|
S0S6S17S2S9dA1A1S7A3").

Variable s sr : wsub.
Hypothesis ENT : ltac2:(tb__ "0|0|
S0S6S3S9cS60VW;Vst;Vtmax;A3Vs;A3S7A3").
Hypothesis SID : ltac2:(tb__ "0|0|
S0S6S5cVs;S4cA2S7A3").
Hypothesis FB : ltac2:(tb__ "0|0|
S0S6S6dS16S20S1aS2S60VW;Vst;Vtmax;A3A1A1A1SaS16S63S69A3A3S7A3").
Hypothesis ENTr : ltac2:(tb__ "0|0|
S0S6S3S9dS61VW;Vst;Vtmax;A3Vsr;A3S7A3").
Hypothesis SIDr : ltac2:(tb__ "0|0|
S0S6S5cVsr;S4cA2S7A3").
Hypothesis FBr : ltac2:(tb__ "0|0|
S0S6S6dS16S20S1aS2S61VW;Vst;Vtmax;A3A1A1A1S63A3S7A3").

Lemma b1_pop : ltac2:(tb__ "0|1|
S74S50S18S8S72Q40M0A1A1S8bS18S0S57Vst;S52A3S0S8S4dA1VW;ScS4dA1A3F_;S7cVW;Vst;A2S51R7A1S35Z1S7aR9S71G0S1eR7PcA2A2A2A2S4aVsegs;S5bVW;Vst;RaR9R8A5VX;R5R7R6A6S4aVsegs;S5bVW;Vst;RbRaR9A5S67VW;Vst;Vtmax;A3S5dR6Vs;A2R8R7A6F_;F_;F_;F_;F_;FrhoE;Fw;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp w rhoE HW HUS HKc Hcnt H.
  pose proof H as [HsmA [Hag HJ]]. destruct Hag as (Hagw & Hagl & Hagm).
  destruct HJ as (HA & HK & Htp & HU & HB & HN & Htop). cbn [eval] in HN.
  assert (E12 : rw rhoE 12%positive = rw rho 12%positive). { rewrite <- (Hagw 12%positive) by (unfold GW; lia). reflexivity. }

  rewrite E12 in HN. set (nv := bv_unsigned (rw rho 12%positive)) in HN, Hcnt |- *.
  assert (E148 : rw rhoE 148%positive = Z_to_bv 64 (Size (cls_of nv))). { rewrite <- (Hagw 148%positive) by (unfold GW; lia). reflexivity. }
  assert (E149 : rw rhoE 149%positive = Z_to_bv 64 (cnt_of A nv)). { rewrite <- (Hagw 149%positive) by (unfold GW; lia). reflexivity. }
  assert (E151 : rw rhoE 151%positive = Z_to_bv 64 (ag_thread (aa_geom A))). { rewrite <- (Hagw 151%positive) by (unfold GW; lia). reflexivity. }
  assert (E152 : rw rhoE 152%positive = Z_to_bv 64 (ag_ctx (aa_geom A))). { rewrite <- (Hagw 152%positive) by (unfold GW; lia). reflexivity. }
  assert (E157 : rw rhoE 157%positive = Z_to_bv 64 (needed8 nv)). { rewrite <- (Hagw 157%positive) by (unfold GW; lia). reflexivity. }
  assert (E158 : rw rhoE 158%positive = Z_to_bv 64 (cls_of nv)). { rewrite <- (Hagw 158%positive) by (unfold GW; lia). reflexivity. }
  assert (E159 : rw rhoE 159%positive = Z_to_bv 64 (chk_of A nv)). { rewrite <- (Hagw 159%positive) by (unfold GW; lia). reflexivity. }

  pose proof (proj1 HsmA) as Hsm. unfold virt in Hsm. cbn [fst snd w_tr w_cfg cfg_ms cfg_model ax_S] in Hsm.
  pose proof (smatch_facts_hold _ _ _ _ Hsm) as HFa.
  assert (HFX : forall p, In p (((unwind_factsS W st ++ pre_facts malloc_depth) ++ F_s1) ++ F_gen) -> holds rhoE p).
  { intros p Hp. exact (proj1 (Forall_forall _ _) HFa p (HXF p Hp)). }
  assert (Hnv : nv <= 64512).
  { pose proof (HFX (SPUle (SVar 12) (SLit 64512)) ltac:(apply in_or_app; right; unfold F_gen; cbn; tauto)) as F. cbn [holds eval] in F.
    rewrite E12, u64_lit in F by lia. exact F. }
  pose proof (cls_facts nv ltac:(lia)) as (C1 & C2 & C3 & C4).
  pose proof (pc_entry_facts segs A rhoE tp _ nv HA ltac:(lia) Hcnt) as PF. cbn zeta in PF.
  destruct PF as (Hci & Kcnt & Ksz & Kch & Hc16 & Hch & PE & PS).
  pose proof HA as (HG & HR & HF & HRest & HM). pose proof HG as HG0.
  pose proof (geom_old _ HG0) as HG'. rewrite FS_total_val, kSpaceSize_val in HG'. unfold HIGH_SHADOW_END, IMG_HI, PG in HG'.
  destruct HG' as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 & G18 & G19 & G20 & G21 & G22 & G23 & G24).
  clear G15 G16 G17 G18 G20 G21.
  pose proof (geom_bands _ HG0) as (_ & _ & _ & _ & TI & _ & _). unfold IMG_LO, IMG_HI in TI.

  assert (EB : bv_unsigned (eval rhoE pc_base) = ag_thread (aa_geom A) + 208 + 80 * cls_of nv).
  { unfold pc_base, vT, V_CLS. cbn [eval]. rewrite E151, E158. rewrite add_val, add_val, mul_val, !u64_lit by lia.
    rewrite (Z.mod_small (cls_of nv * 80)) by lia. rewrite (Z.mod_small (ag_thread (aa_geom A) + 208)) by lia. rewrite Z.mod_small by lia. lia. }

  assert (Hhigh : holds rhoE F_sp_high) by (apply HFX; apply in_or_app; left; apply in_or_app; left; apply in_or_app; right; cbn; tauto).
  cbn [map app] in HXskel.
  destruct (ss_objs (ax_S X)) as [|osw orest] eqn:EO; [cbn [map] in HXskel; exfalso; clear -HXskel; discriminate HXskel|].
  cbn [map] in HXskel.
  assert (SKsw : skel osw = (SVar 10, SVar V_DEPTH, SLit 0)) by exact (f_equal (hd (skel osw)) HXskel).
  assert (SKrest : map skel orest = map skel ((unwind_objs W ++ A_globals) ++ RT_m1)) by exact (f_equal (@tl _) HXskel).
  destruct (sw_range_gen _ rhoE _ _ osw Hsm ltac:(rewrite EO; left; reflexivity) SKsw Hhigh) as (SW1 & SW2 & SW3).
  assert (SW0 : topG (aa_geom A) <= fst (obj_range rhoE osw)) by (rewrite (sw_lo_gen rhoE osw SKsw); exact Htop).

  assert (LNK : Forall (fun o => topG (aa_geom A) + 16 <= bv_unsigned (eval rhoE (ob_base o)) <= 2 ^ 47 /\ ob_lo o = SLit (-16) /\ ob_hi o = SLit 0)
                  (unwind_objs W)).
  { apply (unwind_objs_above _ _ (topG (aa_geom A))); [|clear TI G19; lia|clear TI G19; lia]. apply Forall_forall. intros p Hp.
    assert (Hp' : In p (unwind_factsS W st)).
    { destruct st; [apply chain_pre_in; exact Hp|]. rewrite (HW eq_refl) in Hp. destruct Hp. }
    apply HFX. apply in_or_app; left. apply in_or_app; left. apply in_or_app; left. exact Hp'. }

  assert (DISJ : forall lo' hi', 288 <= lo' -> lo' <= hi' <= 3168 ->
            Forall (fun o' => ranges_disjoint (obj_range rhoE o') (ag_thread (aa_geom A) + lo', ag_thread (aa_geom A) + hi')) (ss_objs (ax_S X))).
  { intros lo' hi' Hlo' Hhi'. rewrite EO. constructor.
    - clear -SW0 G6 Hlo' Hhi'. unfold ranges_disjoint. cbn [fst snd]. lia.
    - apply (Forall_ranges_skel rhoE (fun r => ranges_disjoint r (ag_thread (aa_geom A) + lo', ag_thread (aa_geom A) + hi')) orest _ SKrest).
      apply Forall_app. split.
      + apply Forall_app. split.
        * eapply Forall_impl; [|exact LNK]. intros [ob olo ohi ocs od] (B & L & Hh). cbn [ob_base ob_lo ob_hi] in B, L, Hh. subst olo ohi.
          unfold ranges_disjoint. rewrite !obj_range_mk by (first [ clear - G5 G6 G8 G9 G24 Hlo' Hhi' B; lia | clear - G5 G6 G8 G9 G24 Hlo' Hhi' B TI; lia | clear - G5 G6 G8 G9 G24 Hlo' Hhi' B G19; lia | clear TI G19; lia | clear G19; lia | clear TI; lia | lia ]). cbn [fst snd]. (first [ clear - G5 G6 G8 G9 G24 Hlo' Hhi' B; lia | clear - G5 G6 G8 G9 G24 Hlo' Hhi' B TI; lia | clear - G5 G6 G8 G9 G24 Hlo' Hhi' B G19; lia | clear TI G19; lia | clear G19; lia | clear TI; lia | lia ]).
        * unfold A_globals, O_got, O_rtc, GOT_LO, GOT_HI, RTC_LO, RTC_HI.
          repeat apply Forall_cons; try apply Forall_nil; unfold ranges_disjoint; rewrite ?obj_range_mk by (first [ clear - G5 G6 G8 G9 G24 Hlo' Hhi'; lia | clear - G5 G6 G8 G9 G24 Hlo' Hhi' TI; lia | clear - G5 G6 G8 G9 G24 Hlo' Hhi' G19; lia | clear TI G19; lia | clear G19; lia | clear TI; lia | lia ]); cbn [fst snd eval]; rewrite ?u64_lit by (first [ clear - G5 G6 G8 G9 G24 Hlo' Hhi'; lia | clear - G5 G6 G8 G9 G24 Hlo' Hhi' TI; lia | clear - G5 G6 G8 G9 G24 Hlo' Hhi' G19; lia | clear TI G19; lia | clear G19; lia | clear TI; lia | lia ]); (first [ clear - G5 G6 G8 G9 G24 Hlo' Hhi'; lia | clear - G5 G6 G8 G9 G24 Hlo' Hhi' TI; lia | clear - G5 G6 G8 G9 G24 Hlo' Hhi' G19; lia | clear TI G19; lia | clear G19; lia | clear TI; lia | lia ]).
      + unfold RT_m1, RT_m0, O_rt1a, O_rt1b, O_tsda, O_tsdb, O_tsdc, O_self_tsd, O_tsd0, O_ctx8, O_ctx98, O_T0, O_T40, O_T3168, O_cfa, O_pga, O_pgb, O_mcs,
               O_insta, O_insta2, O_instb, O_rss, O_cfb, O_cfc, O_rms, O_ppf, O_hooks, O_lsan, O_cft, O_afl, O_csd, O_die.
        unfold carved, vT, vCTX, vTOP, vBOT, vSB, vRIS.
        repeat apply Forall_cons; try apply Forall_nil; unfold ranges_disjoint; rewrite ?obj_range_mk by (first [ clear - G5 G6 G8 G9 G24 Hlo' Hhi'; lia | clear - G5 G6 G8 G9 G24 Hlo' Hhi' TI; lia | clear - G5 G6 G8 G9 G24 Hlo' Hhi' G19; lia | clear TI G19; lia | clear G19; lia | clear TI; lia | lia ]); cbn [fst snd eval];
          rewrite ?E151, ?E152, ?u64_lit by (first [ clear - G5 G6 G8 G9 G24 Hlo' Hhi'; lia | clear - G5 G6 G8 G9 G24 Hlo' Hhi' TI; lia | clear - G5 G6 G8 G9 G24 Hlo' Hhi' G19; lia | clear TI G19; lia | clear G19; lia | clear TI; lia | lia ]); (first [ clear - G5 G6 G8 G9 G24 Hlo' Hhi'; lia | clear - G5 G6 G8 G9 G24 Hlo' Hhi' TI; lia | clear - G5 G6 G8 G9 G24 Hlo' Hhi' G19; lia | clear TI G19; lia | clear G19; lia | clear TI; lia | lia ]). }

  assert (PRES : forall lo' hi', 0 <= lo' -> hi' <= 4096 -> present (view segs (rm rhoE)) (ag_thread (aa_geom A) + lo') (ag_thread (aa_geom A) + hi') ->
            forall off, lo' <= off < hi' -> wok_of segs (rm rhoE) (Z_to_bv 64 (ag_thread (aa_geom A) + off)) = true
                                       /\ exists x, rd_of segs (rm rhoE) (Z_to_bv 64 (ag_thread (aa_geom A) + off)) = Some x).
  { intros lo' hi' Hlo0 Hhi0 HP off Hoff. destruct (HP (ag_thread (aa_geom A) + off) ltac:(lia)) as [b Hb].
    clear -Hb G5 G6 G24 TI Hlo0 Hhi0 Hoff. rewrite view_in in Hb by (clear TI; lia).

    eapply wok_rd_off_image2; [| |exact Hb]; [clear TI; lia | lia]. }

  assert (ECH : soff rhoE choff = 16 + 4 * (cnt_of A nv - 1)).
  { unfold choff, V_CNT. rewrite soff_snorm. unfold U. cbn [eval]. rewrite E149. rewrite add_val, sll_val, add_val, !u64_lit by lia.
    replace (bv_unsigned (Z_to_bv 64 (-1))) with (2 ^ 64 - 1) by reflexivity.
    replace ((cnt_of A nv + (2 ^ 64 - 1)) mod 2 ^ 64) with (cnt_of A nv - 1) by (rewrite <- (Z.mod_add _ (-1)) by lia; rewrite Z.mod_small by lia; lia).
    change (2 mod 64) with 2. rewrite ?u64_lit by lia. rewrite Z.shiftl_mul_pow2 by lia. rewrite (Z.mod_small (_ * 2 ^ 2)) by lia. rewrite Z.mod_small by lia.
    unfold snorm. rewrite Z.mod_small by lia. destruct (Z.ltb_spec ((cnt_of A nv - 1) * 2 ^ 2 + 16) (2 ^ 63)); lia. }
  assert (E80 : soff rhoE (SLit 80) = 80) by (apply soff_lit_small; lia).

  assert (H1 : SPA segs (JG W st A Kc rho) X1 rhoE tp w).
  { unfold X1, addobj.
    apply (SPA_carve_gen segs (JG W st A Kc rho) rhoE X tp w pc_base 0 4 _ (ss_next (ax_S X)) H W1 ltac:(lia)); rewrite ?EB; try liaZ.
    - unfold gcells_inside. repeat apply Forall_cons; try apply Forall_nil; cbn [c_off c_width c_val]; rewrite ?soff_lit_small by lia; lia.
    - replace (ag_thread (aa_geom A) + 208 + 80 * cls_of nv + 0) with (ag_thread (aa_geom A) + (208 + 80 * cls_of nv)) by lia.
      replace (ag_thread (aa_geom A) + 208 + 80 * cls_of nv + 4) with (ag_thread (aa_geom A) + (208 + 80 * cls_of nv + 4)) by lia.
      apply DISJ; lia.
    - intros off Hoff. replace (ag_thread (aa_geom A) + 208 + 80 * cls_of nv + off) with (ag_thread (aa_geom A) + (208 + 80 * cls_of nv + off)) by lia.
      apply (PRES (208 + 80 * cls_of nv) (208 + 80 * cls_of nv + 80) ltac:(lia) ltac:(lia)); [|lia].
      intros z Hz. apply PE. lia.
    - unfold gcells_in_view. repeat apply Forall_cons; try apply Forall_nil; cbn [c_off c_width SymState.c_val Z.to_nat Pos.to_nat]; rewrite ?soff_lit_small by lia.
      intros j Hj. unfold V_CNT. cbn [eval]. rewrite E149. specialize (Kcnt j Hj). cbn [c_addr c_w c_val] in Kcnt.
      rewrite view_in in Kcnt by lia. rewrite Z.add_0_r. exact Kcnt.
    - unfold xwords_clear. rewrite HXX. intros rr y j [].
  }
  assert (NX1 : ss_next (ax_S X1) = ss_next (ax_S X)) by reflexivity.
  assert (OB1 : ss_objs (ax_S X1) = ss_objs (ax_S X) ++ [O_pcc]) by reflexivity.

  assert (H1b : SPA segs (JG W st A Kc rho) X1b rhoE tp w).
  { unfold X1b, addobj.
    apply (SPA_carve_gen segs (JG W st A Kc rho) rhoE X1 tp w pc_base 8 16 _ (ss_next (ax_S X)) H1 W1b ltac:(rewrite NX1; lia)); rewrite ?EB; try liaZ.
    - unfold gcells_inside. repeat apply Forall_cons; try apply Forall_nil; cbn [c_off c_width c_val]; rewrite ?soff_lit_small by lia; lia.
    - rewrite OB1. apply Forall_app. split.
      + replace (ag_thread (aa_geom A) + 208 + 80 * cls_of nv + 8) with (ag_thread (aa_geom A) + (208 + 80 * cls_of nv + 8)) by lia.
        replace (ag_thread (aa_geom A) + 208 + 80 * cls_of nv + 16) with (ag_thread (aa_geom A) + (208 + 80 * cls_of nv + 16)) by lia.
        apply DISJ; lia.
      + constructor; [|constructor]. unfold O_pcc, ranges_disjoint. rewrite obj_range_mk by lia. cbn [fst snd]. rewrite EB. clear. lia.
    - intros off Hoff. replace (ag_thread (aa_geom A) + 208 + 80 * cls_of nv + off) with (ag_thread (aa_geom A) + (208 + 80 * cls_of nv + off)) by lia.
      apply (PRES (208 + 80 * cls_of nv) (208 + 80 * cls_of nv + 80) ltac:(lia) ltac:(lia)); [|lia].
      intros z Hz. apply PE. lia.
    - unfold gcells_in_view. repeat apply Forall_cons; try apply Forall_nil; cbn [c_off c_width SymState.c_val Z.to_nat Pos.to_nat]; rewrite ?soff_lit_small by lia.
      intros j Hj. unfold V_SIZE. cbn [eval]. rewrite E148. specialize (Ksz j Hj). cbn [c_addr c_w c_val] in Ksz.
      rewrite view_in in Ksz by lia. exact Ksz.
    - unfold xwords_clear, X1, addobj. cbn [ax_X ax_setS]. rewrite HXX. intros rr y j [].
  }
  assert (NX1b : ss_next (ax_S X1b) = ss_next (ax_S X)) by reflexivity.
  assert (OB1b : ss_objs (ax_S X1b) = (ss_objs (ax_S X) ++ [O_pcc]) ++ [O_pcs]) by reflexivity.

  assert (H1c : SPA segs (JG W st A Kc rho) X1c rhoE tp w).
  { unfold X1c, addobj.
    apply (SPA_carve_gsym segs (JG W st A Kc rho) rhoE X1b tp w pc_base choff (SLit 80) _ (ss_next (ax_S X)) H1b W1c ltac:(rewrite NX1b; lia));
      rewrite ?EB, ?ECH, ?E80; try liaZ.
    - unfold gcells_inside. repeat apply Forall_cons; try apply Forall_nil; cbn [c_off c_width c_val]; rewrite ?ECH; lia.
    - rewrite OB1b. apply Forall_app. split; [apply Forall_app; split|].
      + replace (ag_thread (aa_geom A) + 208 + 80 * cls_of nv + (16 + 4 * (cnt_of A nv - 1))) with (ag_thread (aa_geom A) + (208 + 80 * cls_of nv + (16 + 4 * (cnt_of A nv - 1)))) by lia.
        replace (ag_thread (aa_geom A) + 208 + 80 * cls_of nv + 80) with (ag_thread (aa_geom A) + (208 + 80 * cls_of nv + 80)) by lia.
        apply DISJ; lia.
      + constructor; [|constructor]. unfold O_pcc, ranges_disjoint. rewrite obj_range_mk by lia. cbn [fst snd]. rewrite EB. clear -Hcnt. lia.
      + constructor; [|constructor]. unfold O_pcs, ranges_disjoint. rewrite obj_range_mk by lia. cbn [fst snd]. rewrite EB. clear -Hcnt. lia.
    - intros off Hoff. replace (ag_thread (aa_geom A) + 208 + 80 * cls_of nv + off) with (ag_thread (aa_geom A) + (208 + 80 * cls_of nv + off)) by lia.
      apply (PRES (208 + 80 * cls_of nv) (208 + 80 * cls_of nv + 80) ltac:(lia) ltac:(lia)); [|lia].
      intros z Hz. apply PE. lia.
    - unfold gcells_in_view. repeat apply Forall_cons; try apply Forall_nil; cbn [c_off c_width SymState.c_val Z.to_nat Pos.to_nat]; rewrite ?ECH.
      intros j Hj. unfold V_CH. cbn [eval]. rewrite E159. specialize (Kch j Hj). cbn [c_addr c_w c_val] in Kch.
      rewrite view_in in Kch by lia.
      replace (ag_thread (aa_geom A) + 208 + 80 * cls_of nv + (16 + 4 * (cnt_of A nv - 1)) + Z.of_nat j)
        with (ag_thread (aa_geom A) + 208 + 80 * cls_of nv + 16 + 4 * (cnt_of A nv - 1) + Z.of_nat j) by lia. exact Kch.
    - unfold xwords_clear, X1b, X1, addobj. cbn [ax_X ax_setS]. rewrite HXX. intros rr y j [].
  }
  assert (NX1c : ss_next (ax_S X1c) = ss_next (ax_S X)) by reflexivity.
  assert (OB1c : ss_objs (ax_S X1c) = ((ss_objs (ax_S X) ++ [O_pcc]) ++ [O_pcs]) ++ [O_pck]) by reflexivity.

  assert (H2 : SPA segs (JG W st A Kc rho) X2 rhoE tp w).
  { unfold X2, addobj.
    apply (SPA_carve_gen segs (JG W st A Kc rho) rhoE X1c tp w vT 2768 3168 [] (ss_next (ax_S X)) H1c W2 ltac:(rewrite NX1c; lia));
      unfold vT; cbn [eval]; rewrite ?E151, ?u64_lit by lia; try liaZ.
    - unfold gcells_inside. constructor.
    - rewrite OB1c. apply Forall_app. split; [apply Forall_app; split; [apply Forall_app; split; [apply DISJ; lia|]|]|];
        (constructor; [|constructor]); unfold O_pcc, O_pcs, O_pck, ranges_disjoint.
      + rewrite obj_range_mk by lia. cbn [fst snd]. rewrite EB. clear -C1. lia.
      + rewrite obj_range_mk by lia. cbn [fst snd]. rewrite EB. clear -C1. lia.
      + unfold obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi fst snd]. rewrite ECH, E80, EB. clear -C1 Hcnt. lia.
    - intros off Hoff. apply (PRES 2768 3168 ltac:(lia) ltac:(lia) PS). exact Hoff.
    - unfold gcells_in_view. constructor.
    - unfold xwords_clear, X1c, X1b, X1, addobj. cbn [ax_X ax_setS]. rewrite HXX. intros rr y j [].
  }

  unfold C2p.
  apply (SPA_entails_sem segs (JG W st A Kc rho) GW X2 (C2p0 W st tmax) (F_cls ++ F_pop) s rhoE tp w ENT SID).
  - apply stableA_withG; [intros r1 r2 Hg Hag; eapply agree_below_trans; eauto | apply JM_stableA; [exact HUS | exact HKc]].
  - exact FB.
  - intros rho' tp' tr' md' [Hag' _] _.
    assert (AG : agree_below GW (rhoM_of A rho) (rho_sub rho' s)).
    { eapply agree_below_trans; [exact Hag' | apply rho_sub_agree; exact SID]. }
    destruct AG as (AGw & _ & _).
    assert (R148 : rw (rho_sub rho' s) 148%positive = Z_to_bv 64 (Size (cls_of nv))) by (rewrite <- (AGw 148%positive) by (unfold GW; lia); reflexivity).
    assert (R149 : rw (rho_sub rho' s) 149%positive = Z_to_bv 64 (cnt_of A nv)) by (rewrite <- (AGw 149%positive) by (unfold GW; lia); reflexivity).
    assert (R157 : rw (rho_sub rho' s) 157%positive = Z_to_bv 64 (needed8 nv)) by (rewrite <- (AGw 157%positive) by (unfold GW; lia); reflexivity).
    assert (R158 : rw (rho_sub rho' s) 158%positive = Z_to_bv 64 (cls_of nv)) by (rewrite <- (AGw 158%positive) by (unfold GW; lia); reflexivity).
    assert (R159 : rw (rho_sub rho' s) 159%positive = Z_to_bv 64 (chk_of A nv)) by (rewrite <- (AGw 159%positive) by (unfold GW; lia); reflexivity).
    clear -R148 R149 R157 R158 R159 C1 C2 C3 C4 Hcnt Hc16 Hch.
    unfold F_cls, F_pop, V_CLS, V_ND, V_SIZE, V_CNT, V_CH. cbn [app].
    repeat apply Forall_cons; try apply Forall_nil; cbn [holds eval]; rewrite ?R148, ?R149, ?R157, ?R158, ?R159; rewrite ?u64_lit by lia; lia.
  - exact H2.
Qed.

Lemma b1_refill : ltac2:(tb__ "0|1|
S74S50S18S8S72Q40M0A1A1S8bS18S0S57Vst;S52A3S0S8S4dA1VW;ScS4dA1A3F_;S7cVW;Vst;A2S51R7A1S0S33S7aR9S71G0S1eR7PcA2A2A2Z0A3S4aVsegs;S5bVW;Vst;RaR9R8A5VX;R5R7R6A6S4aVsegs;S5bVW;Vst;RbRaR9A5S68VW;Vst;Vtmax;A3S5dR6Vsr;A2R8R7A6F_;F_;F_;F_;F_;FrhoE;Fw;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp w rhoE HW HUS HKc Hcnt H.
  pose proof H as [HsmA [Hag HJ]]. destruct Hag as (Hagw & Hagl & Hagm).
  destruct HJ as (HA & HK & Htp & HU & HB & HN & Htop). cbn [eval] in HN.
  assert (E12 : rw rhoE 12%positive = rw rho 12%positive). { rewrite <- (Hagw 12%positive) by (unfold GW; lia). reflexivity. }

  rewrite E12 in HN. set (nv := bv_unsigned (rw rho 12%positive)) in HN, Hcnt |- *.
  assert (E148 : rw rhoE 148%positive = Z_to_bv 64 (Size (cls_of nv))). { rewrite <- (Hagw 148%positive) by (unfold GW; lia). reflexivity. }
  assert (E149 : rw rhoE 149%positive = Z_to_bv 64 (cnt_of A nv)). { rewrite <- (Hagw 149%positive) by (unfold GW; lia). reflexivity. }
  assert (E151 : rw rhoE 151%positive = Z_to_bv 64 (ag_thread (aa_geom A))). { rewrite <- (Hagw 151%positive) by (unfold GW; lia). reflexivity. }
  assert (E152 : rw rhoE 152%positive = Z_to_bv 64 (ag_ctx (aa_geom A))). { rewrite <- (Hagw 152%positive) by (unfold GW; lia). reflexivity. }
  assert (E157 : rw rhoE 157%positive = Z_to_bv 64 (needed8 nv)). { rewrite <- (Hagw 157%positive) by (unfold GW; lia). reflexivity. }
  assert (E158 : rw rhoE 158%positive = Z_to_bv 64 (cls_of nv)). { rewrite <- (Hagw 158%positive) by (unfold GW; lia). reflexivity. }
  assert (E159 : rw rhoE 159%positive = Z_to_bv 64 (chk_of A nv)). { rewrite <- (Hagw 159%positive) by (unfold GW; lia). reflexivity. }

  pose proof (proj1 HsmA) as Hsm. unfold virt in Hsm. cbn [fst snd w_tr w_cfg cfg_ms cfg_model ax_S] in Hsm.
  pose proof (smatch_facts_hold _ _ _ _ Hsm) as HFa.
  assert (HFX : forall p, In p (((unwind_factsS W st ++ pre_facts malloc_depth) ++ F_s1) ++ F_gen) -> holds rhoE p).
  { intros p Hp. exact (proj1 (Forall_forall _ _) HFa p (HXF p Hp)). }
  assert (Hnv : nv <= 64512).
  { pose proof (HFX (SPUle (SVar 12) (SLit 64512)) ltac:(apply in_or_app; right; unfold F_gen; cbn; tauto)) as F. cbn [holds eval] in F.
    rewrite E12, u64_lit in F by lia. exact F. }
  pose proof (cls_facts nv ltac:(lia)) as (C1 & C2 & C3 & C4).
  pose proof (pc_entry_facts0 segs A rhoE tp _ nv HA ltac:(lia) Hcnt) as PF. cbn zeta in PF.
  destruct PF as (K0 & PE & PS).
  pose proof HA as (HG & HR & HF & HRest & HM). pose proof HG as HG0.
  pose proof (geom_old _ HG0) as HG'. rewrite FS_total_val, kSpaceSize_val in HG'. unfold HIGH_SHADOW_END, IMG_HI, PG in HG'.
  destruct HG' as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 & G18 & G19 & G20 & G21 & G22 & G23 & G24).
  clear G15 G16 G17 G18 G20 G21.
  pose proof (geom_bands _ HG0) as (_ & _ & _ & _ & TI & _ & _). unfold IMG_LO, IMG_HI in TI.

  assert (EB : bv_unsigned (eval rhoE pc_base) = ag_thread (aa_geom A) + 208 + 80 * cls_of nv).
  { unfold pc_base, vT, V_CLS. cbn [eval]. rewrite E151, E158. rewrite add_val, add_val, mul_val, !u64_lit by lia.
    rewrite (Z.mod_small (cls_of nv * 80)) by lia. rewrite (Z.mod_small (ag_thread (aa_geom A) + 208)) by lia. rewrite Z.mod_small by lia. lia. }

  assert (Hhigh : holds rhoE F_sp_high) by (apply HFX; apply in_or_app; left; apply in_or_app; left; apply in_or_app; right; cbn; tauto).
  cbn [map app] in HXskel.
  destruct (ss_objs (ax_S X)) as [|osw orest] eqn:EO; [cbn [map] in HXskel; exfalso; clear -HXskel; discriminate HXskel|].
  cbn [map] in HXskel.
  assert (SKsw : skel osw = (SVar 10, SVar V_DEPTH, SLit 0)) by exact (f_equal (hd (skel osw)) HXskel).
  assert (SKrest : map skel orest = map skel ((unwind_objs W ++ A_globals) ++ RT_m1)) by exact (f_equal (@tl _) HXskel).
  destruct (sw_range_gen _ rhoE _ _ osw Hsm ltac:(rewrite EO; left; reflexivity) SKsw Hhigh) as (SW1 & SW2 & SW3).
  assert (SW0 : topG (aa_geom A) <= fst (obj_range rhoE osw)) by (rewrite (sw_lo_gen rhoE osw SKsw); exact Htop).

  assert (LNK : Forall (fun o => topG (aa_geom A) + 16 <= bv_unsigned (eval rhoE (ob_base o)) <= 2 ^ 47 /\ ob_lo o = SLit (-16) /\ ob_hi o = SLit 0)
                  (unwind_objs W)).
  { apply (unwind_objs_above _ _ (topG (aa_geom A))); [|clear TI G19; lia|clear TI G19; lia]. apply Forall_forall. intros p Hp.
    assert (Hp' : In p (unwind_factsS W st)).
    { destruct st; [apply chain_pre_in; exact Hp|]. rewrite (HW eq_refl) in Hp. destruct Hp. }
    apply HFX. apply in_or_app; left. apply in_or_app; left. apply in_or_app; left. exact Hp'. }

  assert (DISJ : forall lo' hi', 288 <= lo' -> lo' <= hi' <= 3168 ->
            Forall (fun o' => ranges_disjoint (obj_range rhoE o') (ag_thread (aa_geom A) + lo', ag_thread (aa_geom A) + hi')) (ss_objs (ax_S X))).
  { intros lo' hi' Hlo' Hhi'. rewrite EO. constructor.
    - clear -SW0 G6 Hlo' Hhi'. unfold ranges_disjoint. cbn [fst snd]. lia.
    - apply (Forall_ranges_skel rhoE (fun r => ranges_disjoint r (ag_thread (aa_geom A) + lo', ag_thread (aa_geom A) + hi')) orest _ SKrest).
      apply Forall_app. split.
      + apply Forall_app. split.
        * eapply Forall_impl; [|exact LNK]. intros [ob olo ohi ocs od] (B & L & Hh). cbn [ob_base ob_lo ob_hi] in B, L, Hh. subst olo ohi.
          unfold ranges_disjoint. rewrite !obj_range_mk by (first [ clear - G5 G6 G8 G9 G24 Hlo' Hhi' B; lia | clear - G5 G6 G8 G9 G24 Hlo' Hhi' B TI; lia | clear - G5 G6 G8 G9 G24 Hlo' Hhi' B G19; lia | clear TI G19; lia | clear G19; lia | clear TI; lia | lia ]). cbn [fst snd]. (first [ clear - G5 G6 G8 G9 G24 Hlo' Hhi' B; lia | clear - G5 G6 G8 G9 G24 Hlo' Hhi' B TI; lia | clear - G5 G6 G8 G9 G24 Hlo' Hhi' B G19; lia | clear TI G19; lia | clear G19; lia | clear TI; lia | lia ]).
        * unfold A_globals, O_got, O_rtc, GOT_LO, GOT_HI, RTC_LO, RTC_HI.
          repeat apply Forall_cons; try apply Forall_nil; unfold ranges_disjoint; rewrite ?obj_range_mk by (first [ clear - G5 G6 G8 G9 G24 Hlo' Hhi'; lia | clear - G5 G6 G8 G9 G24 Hlo' Hhi' TI; lia | clear - G5 G6 G8 G9 G24 Hlo' Hhi' G19; lia | clear TI G19; lia | clear G19; lia | clear TI; lia | lia ]); cbn [fst snd eval]; rewrite ?u64_lit by (first [ clear - G5 G6 G8 G9 G24 Hlo' Hhi'; lia | clear - G5 G6 G8 G9 G24 Hlo' Hhi' TI; lia | clear - G5 G6 G8 G9 G24 Hlo' Hhi' G19; lia | clear TI G19; lia | clear G19; lia | clear TI; lia | lia ]); (first [ clear - G5 G6 G8 G9 G24 Hlo' Hhi'; lia | clear - G5 G6 G8 G9 G24 Hlo' Hhi' TI; lia | clear - G5 G6 G8 G9 G24 Hlo' Hhi' G19; lia | clear TI G19; lia | clear G19; lia | clear TI; lia | lia ]).
      + unfold RT_m1, RT_m0, O_rt1a, O_rt1b, O_tsda, O_tsdb, O_tsdc, O_self_tsd, O_tsd0, O_ctx8, O_ctx98, O_T0, O_T40, O_T3168, O_cfa, O_pga, O_pgb, O_mcs,
               O_insta, O_insta2, O_instb, O_rss, O_cfb, O_cfc, O_rms, O_ppf, O_hooks, O_lsan, O_cft, O_afl, O_csd, O_die.
        unfold carved, vT, vCTX, vTOP, vBOT, vSB, vRIS.
        repeat apply Forall_cons; try apply Forall_nil; unfold ranges_disjoint; rewrite ?obj_range_mk by (first [ clear - G5 G6 G8 G9 G24 Hlo' Hhi'; lia | clear - G5 G6 G8 G9 G24 Hlo' Hhi' TI; lia | clear - G5 G6 G8 G9 G24 Hlo' Hhi' G19; lia | clear TI G19; lia | clear G19; lia | clear TI; lia | lia ]); cbn [fst snd eval];
          rewrite ?E151, ?E152, ?u64_lit by (first [ clear - G5 G6 G8 G9 G24 Hlo' Hhi'; lia | clear - G5 G6 G8 G9 G24 Hlo' Hhi' TI; lia | clear - G5 G6 G8 G9 G24 Hlo' Hhi' G19; lia | clear TI G19; lia | clear G19; lia | clear TI; lia | lia ]); (first [ clear - G5 G6 G8 G9 G24 Hlo' Hhi'; lia | clear - G5 G6 G8 G9 G24 Hlo' Hhi' TI; lia | clear - G5 G6 G8 G9 G24 Hlo' Hhi' G19; lia | clear TI G19; lia | clear G19; lia | clear TI; lia | lia ]). }

  assert (PRES : forall lo' hi', 0 <= lo' -> hi' <= 4096 -> present (view segs (rm rhoE)) (ag_thread (aa_geom A) + lo') (ag_thread (aa_geom A) + hi') ->
            forall off, lo' <= off < hi' -> wok_of segs (rm rhoE) (Z_to_bv 64 (ag_thread (aa_geom A) + off)) = true
                                       /\ exists x, rd_of segs (rm rhoE) (Z_to_bv 64 (ag_thread (aa_geom A) + off)) = Some x).
  { intros lo' hi' Hlo0 Hhi0 HP off Hoff. destruct (HP (ag_thread (aa_geom A) + off) ltac:(lia)) as [b Hb].
    clear -Hb G5 G6 G24 TI Hlo0 Hhi0 Hoff. rewrite view_in in Hb by (clear TI; lia).

    eapply wok_rd_off_image2; [| |exact Hb]; [clear TI; lia | lia]. }

  assert (H1 : SPA segs (JG W st A Kc rho) X1r rhoE tp w).
  { unfold X1r, addobj.
    apply (SPA_carve_gen segs (JG W st A Kc rho) rhoE X tp w pc_base 0 4 _ (ss_next (ax_S X)) H W1r ltac:(lia)); rewrite ?EB; try liaZ.
    - unfold gcells_inside. repeat apply Forall_cons; try apply Forall_nil; cbn [c_off c_width c_val]; rewrite ?soff_lit_small by lia; lia.
    - replace (ag_thread (aa_geom A) + 208 + 80 * cls_of nv + 0) with (ag_thread (aa_geom A) + (208 + 80 * cls_of nv)) by lia.
      replace (ag_thread (aa_geom A) + 208 + 80 * cls_of nv + 4) with (ag_thread (aa_geom A) + (208 + 80 * cls_of nv + 4)) by lia.
      apply DISJ; lia.
    - intros off Hoff. replace (ag_thread (aa_geom A) + 208 + 80 * cls_of nv + off) with (ag_thread (aa_geom A) + (208 + 80 * cls_of nv + off)) by lia.
      apply (PRES (208 + 80 * cls_of nv) (208 + 80 * cls_of nv + 80) ltac:(lia) ltac:(lia)); [|lia].
      intros z Hz. apply PE. lia.
    - unfold gcells_in_view. repeat apply Forall_cons; try apply Forall_nil; cbn [c_off c_width SymState.c_val Z.to_nat Pos.to_nat]; rewrite ?soff_lit_small by lia.
      intros j Hj. cbn [eval]. specialize (K0 j Hj). cbn [c_addr c_w c_val] in K0.
      rewrite view_in in K0 by lia. rewrite Z.add_0_r. exact K0.
    - unfold xwords_clear. rewrite HXX. intros rr y j [].
  }

  assert (NX1r : ss_next (ax_S X1r) = ss_next (ax_S X)) by reflexivity.
  assert (OB1 : ss_objs (ax_S X1r) = ss_objs (ax_S X) ++ [O_pcc0]) by reflexivity.
  assert (H2 : SPA segs (JG W st A Kc rho) X2r rhoE tp w).
  { unfold X2r, addobj.
    apply (SPA_carve_gen segs (JG W st A Kc rho) rhoE X1r tp w vT 2768 3168 [] (ss_next (ax_S X)) H1 W2r ltac:(rewrite NX1r; lia));
      unfold vT; cbn [eval]; rewrite ?E151, ?u64_lit by lia; try liaZ.
    - unfold gcells_inside. constructor.
    - rewrite OB1. apply Forall_app. split; [apply DISJ; lia|]. constructor; [|constructor].
      unfold O_pcc0, ranges_disjoint. rewrite obj_range_mk by lia. cbn [fst snd]. rewrite EB. clear -C1. lia.
    - intros off Hoff. apply (PRES 2768 3168 ltac:(lia) ltac:(lia) PS). exact Hoff.
    - unfold gcells_in_view. constructor.
    - unfold xwords_clear, X1r, addobj. cbn [ax_X ax_setS]. rewrite HXX. intros rr y j [].
  }

  unfold C2r.
  apply (SPA_entails_sem segs (JG W st A Kc rho) GW X2r (C2r0 W st tmax) F_cls sr rhoE tp w ENTr SIDr).
  - apply stableA_withG; [intros r1 r2 Hg Hag; eapply agree_below_trans; eauto | apply JM_stableA; [exact HUS | exact HKc]].
  - exact FBr.
  - intros rho' tp' tr' md' [Hag' _] _.
    assert (AG : agree_below GW (rhoM_of A rho) (rho_sub rho' sr)).
    { eapply agree_below_trans; [exact Hag' | apply rho_sub_agree; exact SIDr]. }
    destruct AG as (AGw & _ & _).
    assert (R148 : rw (rho_sub rho' sr) 148%positive = Z_to_bv 64 (Size (cls_of nv))) by (rewrite <- (AGw 148%positive) by (unfold GW; lia); reflexivity).
    assert (R149 : rw (rho_sub rho' sr) 149%positive = Z_to_bv 64 (cnt_of A nv)) by (rewrite <- (AGw 149%positive) by (unfold GW; lia); reflexivity).
    assert (R157 : rw (rho_sub rho' sr) 157%positive = Z_to_bv 64 (needed8 nv)) by (rewrite <- (AGw 157%positive) by (unfold GW; lia); reflexivity).
    assert (R158 : rw (rho_sub rho' sr) 158%positive = Z_to_bv 64 (cls_of nv)) by (rewrite <- (AGw 158%positive) by (unfold GW; lia); reflexivity).
    assert (R159 : rw (rho_sub rho' sr) 159%positive = Z_to_bv 64 (chk_of A nv)) by (rewrite <- (AGw 159%positive) by (unfold GW; lia); reflexivity).
    clear -R148 R149 R157 R158 R159 C1 C2 C3 C4 Hcnt.
    unfold F_cls, V_CLS, V_ND, V_SIZE, V_CNT, V_CH. cbn [app].
    repeat apply Forall_cons; try apply Forall_nil; cbn [holds eval]; rewrite ?R148, ?R149, ?R157, ?R158, ?R159; rewrite ?u64_lit by lia; lia.
  - exact H2.
Qed.
End B1B.

Section SPINE2.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Let J (W : list ulink) (st : ustop) (A : AA) (Kc : KcA) : jpredA := ltac2:(tb__ "0|0|
S59S93Vsegs;A1VW;Vst;VA;VKc;S19PcA1A6").
Variable nW : nat. Variable st : ustop. Variable tmax : Z.
Let W : list ulink := Wcan nW.
Let Xa : axst := ltac2:(tb__ "0|0|
S5S5eVW;Vst;Vtmax;A3S2S85VnW;Vst;Vtmax;A3A1A2").
Let Xb : axst := ltac2:(tb__ "0|0|
S5S5fVW;Vst;Vtmax;A3S2S86VnW;Vst;Vtmax;A3A1A2").

Hypothesis Cert2 : ltac2:(tb__ "0|1|
S0S6Sa7Sa8Ufa0SbS33Z40bacScS33A1A3S4cSbS4S66VW;Vst;Vtmax;A3ScS4A1M0A3SbS4S5eVW;Vst;Vtmax;A3SbS4S5fVW;Vst;Vtmax;A3G0A3A3A6S7A3").

Hypothesis OVa : ltac2:(tb__ "0|0|
S0S6S87P9dS64VW;Vst;Vtmax;A3A2S7A3").
Hypothesis OVb : ltac2:(tb__ "0|0|
S0S6S87P9dS65VW;Vst;Vtmax;A3A2S7A3").
Hypothesis TABa : ltac2:(tb__ "0|0|
S0S6S88P9dS64VW;Vst;Vtmax;A3S90Z208Sa2Sa4S94S95S96S94S97A1A1A1A1A1A1A5S7A3").
Hypothesis TABb : ltac2:(tb__ "0|0|
S0S6S88P9dS65VW;Vst;Vtmax;A3S90Z18U3eA5S7A3").
Hypothesis Wa' : ltac2:(tb__ "0|0|
S0S6S17S2S85VnW;Vst;Vtmax;A3A1A1S7A3").
Hypothesis Wb' : ltac2:(tb__ "0|0|
S0S6S17S2S86VnW;Vst;Vtmax;A3A1A1S7A3").
Hypothesis Da' : ltac2:(tb__ "0|4|
S0S10S9S8S9S14S14A2M0A1M1S8S16A1M2A2M3A1S9bS2S5eVW;Vst;Vtmax;A3A1S2S85VnW;Vst;Vtmax;A3A1A2SfG3SdG1G2SbG0SdS14S14S64VW;Vst;Vtmax;A3S19S6aA1A4ScG0A1A3ScS16A1A4A2A3").
Hypothesis Db' : ltac2:(tb__ "0|4|
S0S10S9S8S9S14S14A2M0A1M1S8S16A1M2A2M3A1S9bS2S5fVW;Vst;Vtmax;A3A1S2S86VnW;Vst;Vtmax;A3A1A2SfG3SdG1G2SbG0SdS14S14S65VW;Vst;Vtmax;A3S19S6aA1A4ScG0A1A3ScS16A1A4A2A3").
Hypothesis NXa : ltac2:(tb__ "0|0|
S0S34S1aS2S85VnW;Vst;Vtmax;A3A1A1S1aS2S5eVW;Vst;Vtmax;A3A1A1A3").
Hypothesis NXb : ltac2:(tb__ "0|0|
S0S34S1aS2S86VnW;Vst;Vtmax;A3A1A1S1aS2S5fVW;Vst;Vtmax;A3A1A1A3").
Hypothesis Fa : ltac2:(tb__ "0|0|
S6eS16S21S9aS1cZ200A1S19S6bA1A3S1bS2S5eVW;Vst;Vtmax;A3A1A1A3").
Hypothesis Fb : ltac2:(tb__ "0|0|
S6eS16S28S21S9aS1cZ200A1S19S6bA1A3A1S1bS2S5fVW;Vst;Vtmax;A3A1A1A3").
Hypothesis Ga : ltac2:(tb__ "0|0|
S6cS16S62S1bS2S5eVW;Vst;Vtmax;A3A1A1A3").
Hypothesis Gb : ltac2:(tb__ "0|0|
S6cS16S62S1bS2S5fVW;Vst;Vtmax;A3A1A1A3").

Hypothesis SKa : ltac2:(tb__ "0|1|
S0S8S9S9S14S14A2S14A2M0A1S47S15G0S3eS1fS2VXa;A1A1A4S47S15G0S3eSaS15SbS15S8fSaS15S4eVW;A1S4fA3A3S8eA3A4A3").
Hypothesis SKb : ltac2:(tb__ "0|1|
S0S8S9S9S14S14A2S14A2M0A1S47S15G0S3eS1fS2VXb;A1A1A4S47S15G0S3eSaS15SbS15S8fSaS15S4eVW;A1S4fA3A3S8eA3A4A3").
Hypothesis XXa : ax_X Xa = [].
Hypothesis XXb : ax_X Xb = [].
Hypothesis XFa : ltac2:(tb__ "0|0|
S6cS16SaS16SaS16SaS16S56VW;Vst;A2S55S54A1A3S8dA3S62A3S1bS2VXa;A1A1A3").
Hypothesis XFb : ltac2:(tb__ "0|0|
S6cS16SaS16SaS16SaS16S56VW;Vst;A2S55S54A1A3S8dA3S62A3S1bS2VXb;A1A1A3").
Hypothesis W1a : ltac2:(tb__ "0|0|
S0S6S17S2S41VXa;A1A1A1S7A3").   Hypothesis W1ba : ltac2:(tb__ "0|0|
S0S6S17S2S42VXa;A1A1A1S7A3").  Hypothesis W1ca : ltac2:(tb__ "0|0|
S0S6S17S2S43VXa;A1A1A1S7A3").  Hypothesis W2a : ltac2:(tb__ "0|0|
S0S6S17S2S3fVXa;A1A1A1S7A3").
Hypothesis W1ra : ltac2:(tb__ "0|0|
S0S6S17S2S44VXa;A1A1A1S7A3"). Hypothesis W2ra : ltac2:(tb__ "0|0|
S0S6S17S2S40VXa;A1A1A1S7A3").
Hypothesis W1b : ltac2:(tb__ "0|0|
S0S6S17S2S41VXb;A1A1A1S7A3").   Hypothesis W1bb : ltac2:(tb__ "0|0|
S0S6S17S2S42VXb;A1A1A1S7A3").  Hypothesis W1cb : ltac2:(tb__ "0|0|
S0S6S17S2S43VXb;A1A1A1S7A3").  Hypothesis W2b : ltac2:(tb__ "0|0|
S0S6S17S2S3fVXb;A1A1A1S7A3").
Hypothesis W1rb : ltac2:(tb__ "0|0|
S0S6S17S2S44VXb;A1A1A1S7A3"). Hypothesis W2rb : ltac2:(tb__ "0|0|
S0S6S17S2S40VXb;A1A1A1S7A3").
Variables sa sra sb srb : wsub.
Hypothesis ENTa : ltac2:(tb__ "0|0|
S0S6S3S3fVXa;A1S60VW;Vst;Vtmax;A3Vsa;A3S7A3").
Hypothesis ENTra : ltac2:(tb__ "0|0|
S0S6S3S40VXa;A1S61VW;Vst;Vtmax;A3Vsra;A3S7A3").
Hypothesis ENTb : ltac2:(tb__ "0|0|
S0S6S3S3fVXb;A1S60VW;Vst;Vtmax;A3Vsb;A3S7A3").
Hypothesis ENTrb : ltac2:(tb__ "0|0|
S0S6S3S40VXb;A1S61VW;Vst;Vtmax;A3Vsrb;A3S7A3").
Hypothesis SIDa : ltac2:(tb__ "0|0|
S0S6S5cVsa;S4cA2S7A3").   Hypothesis SIDra : ltac2:(tb__ "0|0|
S0S6S5cVsra;S4cA2S7A3").
Hypothesis SIDb : ltac2:(tb__ "0|0|
S0S6S5cVsb;S4cA2S7A3").   Hypothesis SIDrb : ltac2:(tb__ "0|0|
S0S6S5cVsrb;S4cA2S7A3").
Hypothesis FB : ltac2:(tb__ "0|0|
S0S6S6dS16S20S1aS2S60VW;Vst;Vtmax;A3A1A1A1SaS16S63S69A3A3S7A3").
Hypothesis FBr : ltac2:(tb__ "0|0|
S0S6S6dS16S20S1aS2S61VW;Vst;Vtmax;A3A1A1A1S63A3S7A3").

Theorem spine_s2 : ltac2:(tb__ "0|0|
S8bOF_;S74S50S18S8S72Q40A1A1S8cS0S57Vst;S52A3S0S8S4dA1VW;ScS4dA1A3F_;S7cVW;Vst;A2S51R6A1S4bVsegs;R9VJ;VW;Vst;R8R7A4A3S18S8aVsegs;RbS4aVsegs;S5bVW;Vst;RaR9R8A5S67VW;Vst;Vtmax;A3R1R7A5R6A4FrhoE;S18S8aVsegs;RcS4aVsegs;S5bVW;Vst;RbRaR9A5S68VW;Vst;Vtmax;A3R1R8A5R7A4FrhoE;S18S8aVsegs;RdS4aVsegs;S5bVW;Vst;RcRbRaA5S66VW;Vst;Vtmax;A3R1R9A5R8A4FrhoE;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp Q HW HUS HKc Hokf HP HR rhoE.
  pose proof (Zle_0_nat (length (cs_cache (cst_of A (bv_unsigned (rw rho 12%positive)))))) as Hc0.
  change (0 <= cnt_of A (bv_unsigned (rw rho 12%positive))) in Hc0.
  apply (cfg_soundA segs 4000%nat [0x40bac] GW [C1g W st tmax] [E2a W st tmax; E2b W st tmax] (JG W st A Kc rho) ok Q tp).
  - intros r t tr ms md msv' [_ HJ]. eapply Hokf; eauto.
  - apply stableA_withG; [intros r1 r2 H1 H2; eapply agree_below_trans; eauto | apply JM_stableA; [exact HUS | exact HKc]].
  - exact Cert2.
  - intros E rhoX HinE. destruct HinE as [<-|[<-|[]]].
    +
      destruct (Z_lt_dec 0 (cnt_of A (bv_unsigned (rw rho 12%positive)))) as [Hp|Hz].
      * eapply triple_conseq; [intros w Hw | intros w Hw; right; exact Hw | apply (HP (rho_sub rhoX sa))].
        apply (b1_pop nW st tmax Xa SKa XXa XFa W1a W1ba W1ca W2a sa sra ENTa SIDa FB ENTra FBr A Kc rho tp w rhoX HW HUS HKc ltac:(lia)).
        exact (class_restate_a nW st tmax OVa TABa Wa' Da' NXa NXb Fa Ga A Kc rho tp w rhoX Hw).
      * eapply triple_conseq; [intros w Hw | intros w Hw; right; exact Hw | apply (HR (rho_sub rhoX sra))].
        apply (b1_refill nW st tmax Xa SKa XXa XFa W1ra W2ra sa sra ENTa FB ENTra SIDra FBr A Kc rho tp w rhoX HW HUS HKc ltac:(lia)).
        exact (class_restate_a nW st tmax OVa TABa Wa' Da' NXa NXb Fa Ga A Kc rho tp w rhoX Hw).
    +
      destruct (Z_lt_dec 0 (cnt_of A (bv_unsigned (rw rho 12%positive)))) as [Hp|Hz].
      * eapply triple_conseq; [intros w Hw | intros w Hw; right; exact Hw | apply (HP (rho_sub rhoX sb))].
        apply (b1_pop nW st tmax Xb SKb XXb XFb W1b W1bb W1cb W2b sb srb ENTb SIDb FB ENTrb FBr A Kc rho tp w rhoX HW HUS HKc ltac:(lia)).
        exact (class_restate_b nW st tmax OVb TABb Wb' NXa NXb Db' Fb Gb A Kc rho tp w rhoX Hw).
      * eapply triple_conseq; [intros w Hw | intros w Hw; right; exact Hw | apply (HR (rho_sub rhoX srb))].
        apply (b1_refill nW st tmax Xb SKb XXb XFb W1rb W2rb sb srb ENTb FB ENTrb SIDrb FBr A Kc rho tp w rhoX HW HUS HKc ltac:(lia)).
        exact (class_restate_b nW st tmax OVb TABb Wb' NXa NXb Db' Fb Gb A Kc rho tp w rhoX Hw).
  - left. reflexivity.
Qed.
End SPINE2.
End SpineMallocS3.

(* [comment removed for export] *)
Module CertCallocOv.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sobj"; "SLit"; "ss_objs"; "mkSS"; "FcsrFrm0"; "SVar"; "ss_facts"; "ss_fcsr"; "ss_fregs"; "ss_lenient"; "ss_next"; "ss_pc"; "ss_regs"; "ss_resv"; "@Corelib.Init.Datatypes"; "pair"; "cons"; "nat"; "prod"; "nil"; "app"; "None"; "false"; "length"; "list"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "ax_setS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.CertCallocOv.W"; "EXo"; "NOBJo"; "stKo"; "stRo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "ERRNO_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "setregs"; "NF"; "cut_regs"; "pre_fregs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.CertCallocOv"; "P0os"; "N_ovn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "AE_A"; "A_globals"; "Wcan"; "stack_win"; "unwind_objs"; "L_calloc_null"; "ae_ret_calloc"; "mkA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineCallocIo"; "P0o"; "FACTSo"; "@Corelib.Lists.ListDef"; "firstn"; "map"; "skipn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.CertCallocS1"; "stop_le"; "stop_pc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull"; "NW2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1"; "RT_m1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc"; "TP_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM"; "carve_obj"; "carve_spec"; "@Stdlib.ZArith.BinInt.Z"; "add"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymFrame SymEntail SymCFG ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA CFGA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ak.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineCallocIo.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ak.SpineCallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineCallocIo.
Import ListNotations.
Open Scope Z_scope.

Definition N_ovn : list carve_spec := ltac2:(tb__ "0|8|
S10S12S12S12S0S19A2M0S19A2M1S18S12S12S19S11A2M2S0A2M3A1M4A2M5SfG1G4SfG0S19SfS0S19S2Z0A1M6Z173660A4Z173662A4S10G3SfG2S0SfS19S11Z173661U1A4S2Z1A1A4S13G3A1M7A3A4S10G5SfG1G4SfG0S19SfS0S19G6S21A4S40S21Z4A2A4S10G3SfG2S0SfS19S11S21U4A4S2ZcA1A4G7A3A4S13G5A1A3A3").

Section W.
Variable W : list ulink.
Variable st : ustop.

Definition EXo : axst := ltac2:(tb__ "0|1|
S2fS4S2eS28A1S22S24S3cA1S10S12S11S0A2M0SfS11S0U4S2S3dA1A4S10G0SfS11S0UaS2Z0A1A4S13G0A1A3A3A2S25S5S15S0A1S14S1S10S1S2bS14S1S2cVW;A1S29A3A3S14S1S3bS33S3fS1S3eS27A4A3A3S31VW;Vst;A2S3aS16A9S13S12S0S0A2A1A2").
Definition NOBJo : nat := ltac2:(tb__ "0|0|
S17S1S10S1S2bS14S1S2cVW;A1S29A3A3A2").
Definition stKo : axst := ltac2:(tb__ "0|1|
S1cS1dS36S1aS1dA1M0S32S1S1eS3G0A1A3A2A2").
Definition stRo_S : sstate := ltac2:(tb__ "0|2|
S4ScS1aS1fA1M0A1S22SdG0A1S10S12S11S0A2M1SfS11S0U4S6P18A1A4S13G1A1A3A2S9G0A1S8G0A1SeG0A1S3G0A1S7G0A1SbG0A1SaG0A1A9").
Definition stRo : axst := ax_setS stKo stRo_S.
Definition s_o : wsub := ltac2:(tb__ "0|0|
S35S23S1aS20A1S1aS2dS28VW;Vst;A3A1A3").
Definition R_o : list sobj := ltac2:(tb__ "0|0|
S34S1S1eS3S1aS1dA1A1A3").
End W.

Definition ov_cuts (n : nat) (st : ustop) : list axst := ltac2:(tb__ "0|0|
S10S1bS30S2aVn;A1Vst;A2S13S1bA1A3").

Definition P0os (W : list ulink) (st : ustop) (sx : list sprop) : axst := ltac2:(tb__ "0|0|
S37Vsx;S30VW;Vst;A2A2").
Definition ov_cuts_pcs (n : nat) (st : ustop) : list axst := ltac2:(tb__ "0|1|
S10S1bS26S2aVn;A1M0Vst;S39G0A1A3S10S1bS26G0Vst;S38G0A1A3S13S1bA1A3A3").
End CertCallocOv.

(* [comment removed for export] *)
Module RefillJP.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "not"; "iff"; "or"; "True"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.RefillJP"; "piece"; "ph_set"; "ph_get"; "ph_quiet"; "pord"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillJ"; "phase"; "zoneR"; "mlink"; "rlink"; "ph_f"; "mkPh"; "ph_cnt"; "ph_fill"; "ph_pop"; "ph_ri"; "ph_u"; "F0"; "U0"; "shpage"; "@Corelib.Init.Datatypes"; "nat"; "list"; "None"; "app"; "bool"; "false"; "option"; "length"; "prod"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "m_vmmaps"; "Model"; "alloc_top"; "m_vm_lazy"; "maps_subtract"; "vm_limit"; "vm_maps"; "vm_noaccess"; "vm_reserved"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "bview"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "lt"; "of_nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.RefillJP.JP"; "pbase"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "paid"; "@Stdlib.Lists.List"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "Sh"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymFrame Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt StepA SoundA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv RefillModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RefillJ.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillJ.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Inductive piece : Set := PU | PF.

Definition ph_get (p : piece) (ph : phase) : nat := ltac2:(tb__ "0|0|
S6S1aLp;Vp;S16Vph;A1S10Vph;A1X6x2").
Definition ph_set (p : piece) (n : nat) (ph : phase) : phase := ltac2:(tb__ "0|4|
S6ScLp;Vp;S11Vn;S10Vph;A1S13Vph;A1M0S14Vph;A1M1S12Vph;A1M2S15Vph;A1M3A6S11S16Vph;A1Vn;G0G1G2G3A6X6x2").

Definition pord (p : piece) (ph : phase) : Prop := ltac2:(tb__ "0|0|
S6OLp;Vp;S0S1aS10Vph;A1U0A3S5X6x2").
Definition ph_quiet (ph : phase) : Prop := ltac2:(tb__ "0|1|
S1S0SbS13Vph;A1Z0M0A3S1S0SbS14Vph;A1G0A3S1S0S1eS12Vph;A1S1fA3S0S1eS15Vph;A1S1fA3A2A2A2").

Lemma ph_get_set : ltac2:(tb__ "0|0|
S6S1aScS0S1aS8R3S7R3R2R1A3A2R2A3Fph;Fn;Fp;").
Proof. intros [|] n ph; reflexivity. Qed.
Lemma ph_set_set : ltac2:(tb__ "0|0|
S6S1aS1aScS0ScS7R4R2S7R4R3R1A3A3S7R4R2R1A3A3Fph;Fn';Fn;Fp;").
Proof. intros [|] n n' ph; reflexivity. Qed.
Lemma ph_quiet_set : ltac2:(tb__ "0|0|
S6S1aScS9R1A1S9S7R4R3R2A3A1F_;Fph;Fn;Fp;").
Proof. intros [|] n ph H; exact H. Qed.
Lemma pord_set : ltac2:(tb__ "0|0|
S6S1aScSaR3R1A2SaR4S7R4R3R2A3A2F_;Fph;Fn;Fp;").
Proof. intros [|] n ph H; exact H. Qed.

Section JP.
Variables (A : AA) (rb : valuation) (tp0 : list word) (md0 : Model).
Definition pbase (p : piece) : Z := ltac2:(tb__ "0|0|
S6SbLp;Vp;S18VA;Vrb;A2S17VA;Vrb;A2X6x2").

Lemma mlink_commit : ltac2:(tb__ "0|9|
S6ScS1bS32Q40A1M0A1S24S24SeVA;Vrb;Vtp0;Vmd0;R4R3R2A7S0S1aS8R6R5A2U0A3SaR7R6A2S0S1bS22G0G0A2A1M1S29S23R4A1A1S29S23R5A1M2A1A3S0G1S2bG2A1S2bS23R6A1M3A1A3S0SbS28G3A1S28S23R7A1M4A1A3S0SbS25G4A1S25S23R8A1M5A1A3S0G1S2aG5A1S27S2aS23R9A1A1S31RcA1M6S2dG6Z40000M7A2A3A3S0G1S26R9A1S27S26RaA1S31RdA1M8S2dG8G7A2A3A3S2eS33RaRcA2S2dS33RbRcA2G7A2A2SeVA;Vrb;Vtp0;Vmd0;S7RfU1ReA3RdRbA7F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd';Fmd;Ftp;Fph;Fp;").
Proof.
  intros p ph tp md md' HM Hg Ho EM ER EL ET EN ELz HP.
  unfold mlink in HM |- *. cbn zeta in HM |- *. destruct HM as (M1 & M2 & M3 & M4 & M5 & M6 & tp1 & M7 & M8 & M9 & M10).
  rewrite EM, ER, EL, ET, EN, ELz, M5, M6.
  split; [exact M1|]. split; [exact M2|]. split; [exact M3|]. split; [exact M4|].
  destruct p; cbn [ph_get pord pbase ph_set ph_u ph_f] in *.
  - rewrite Hg, Ho in *. unfold subU, subF, committed, revealedp, kUserMapSize in *. cbn [Nat.leb] in *.
    split; [reflexivity|]. split; [reflexivity|]. exists tp1. split; [exact M7|]. split; [exact M8|]. split; [exact M9|]. lia.
  - rewrite Hg in *. unfold subF, committed, revealedp, kFreeArrayMapSize in *. cbn [Nat.leb] in *.
    split; [reflexivity|]. split; [reflexivity|]. exists tp1. split; [exact M7|]. split; [exact M8|]. split; [exact M9|]. lia.
Qed.

Lemma mlink_reveal : ltac2:(tb__ "0|2|
S6ScS1bS32Q40A1M0A1M1S24G1SeVA;Vrb;Vtp0;Vmd0;R4R3R2A7S0S1aS8R6R5A2U1A3G0S34G0R1R4A3S1S2S34G0R2R7A3A1S19S31R9A1R2A2A2F_;Fq;S2eS30S21G0R4A2A1Z8A2S2eS33R6S1dG0R5R7A3A2S2dS33R6R7A2Z8000A2A2SeVA;Vrb;Vtp0;Vmd0;S7RaU2R9A3S1dG0R6R8A3R7A7F_;F_;F_;F_;F_;Ftpn;Fmd;Ftp;Fph;Fp;").
Proof.
  intros p ph tp md tpn HM Hg Hq Hn HP.
  unfold mlink in HM |- *. cbn zeta in HM |- *. destruct HM as (M1 & M2 & M3 & M4 & M5 & M6 & tp1 & M7 & M8 & M9 & M10).
  split; [exact M1|]. split; [exact M2|]. split; [exact M3|]. split; [exact M4|].
  destruct p; cbn [ph_get pbase ph_set ph_u ph_f] in *; rewrite Hg in *; unfold committed, revealedp in *; cbn [Nat.leb] in *.
  - split; [exact M5|]. split; [exact M6|]. exists (tpn ++ tp1). split; [rewrite M7, app_assoc; reflexivity|].
    split.
    { intros q Hin. apply in_app_or in Hin as [Hin|Hin].
      - destruct (Hq q Hin) as [N S]. split; [intros X; apply N; rewrite M7; apply in_or_app; right; exact X | left; split; [reflexivity | exact S]].
      - destruct (M8 q Hin) as [N [[X _]|X]]; [discriminate X|]. split; [exact N | right; exact X]. }
    split; [rewrite length_app, Nat2Z.inj_add; lia|].
    lia.
  - split; [exact M5|]. split; [exact M6|]. exists (tpn ++ tp1). split; [rewrite M7, app_assoc; reflexivity|].
    split.
    { intros q Hin. apply in_app_or in Hin as [Hin|Hin].
      - destruct (Hq q Hin) as [N S]. split; [intros X; apply N; rewrite M7; apply in_or_app; right; exact X | right; split; [reflexivity | exact S]].
      - destruct (M8 q Hin) as [N [X|[X _]]]; [|discriminate X]. split; [exact N | left; exact X]. }
    split; [rewrite length_app, Nat2Z.inj_add; lia|].
    lia.
Qed.

Lemma mlink_release : ltac2:(tb__ "0|0|
S6ScS1bS32Q40A1A1S24SeVA;Vrb;Vtp0;Vmd0;R3R2R1A7S0S1aS8R5R4A2U2A3SeVA;Vrb;Vtp0;Vmd0;S7R6U3R5A3R4R3A7F_;F_;Fmd;Ftp;Fph;Fp;").
Proof.
  intros p ph tp md HM Hg. unfold mlink in HM |- *. cbn zeta in HM |- *.
  destruct p; cbn [ph_get ph_set ph_u ph_f] in *; rewrite Hg in HM; exact HM.
Qed.

Lemma zone_commit : ltac2:(tb__ "0|0|
S6ScSbS0S1aS8R3R2A2U0A3S3SdVA;Vrb;S7R4U1R3A3R2A4SdVA;Vrb;R3R2A4A2F_;Fz;Fph;Fp;").
Proof.
  intros p ph z Hg. unfold zoneR. destruct p; cbn [ph_get ph_set ph_u ph_f ph_fill ph_pop ph_cnt ph_ri] in *; rewrite Hg;
    unfold revealedp, releasedp; cbn [Nat.leb]; tauto.
Qed.
Lemma zone_reveal : ltac2:(tb__ "0|1|
S6ScSbS0S1aS8R3R2A2U1A3S3SdVA;Vrb;S7R4U2R3A3R2A4S4SdVA;Vrb;R3R2A4S1S2eS35S31R4A1A1M0R2A2S2fR2S2dG0Z8000A2A2A2A2A2F_;Fz;Fph;Fp;").
Proof.
  intros p ph z Hg. unfold zoneR. destruct p; cbn [ph_get pbase ph_set ph_u ph_f ph_fill ph_pop ph_cnt ph_ri] in *; rewrite Hg;
    unfold revealedp, releasedp; cbn [Nat.leb]; split; intros H; repeat (destruct H as [H|H]); try (destruct H as [X H]; try discriminate X); tauto.
Qed.
Lemma zone_release : ltac2:(tb__ "0|1|
S6ScSbS0S1aS8R3R2A2U2A3S3SdVA;Vrb;S7R4U3R3A3R2A4S4SdVA;Vrb;R3R2A4S1S2eS31R4A1M0R2A2S2fR2S2dG0Z40000A2A2A2A2A2F_;Fz;Fph;Fp;").
Proof.
  intros p ph z Hg. unfold zoneR. destruct p; cbn [ph_get pbase ph_set ph_u ph_f ph_fill ph_pop ph_cnt ph_ri] in *; rewrite Hg;
    unfold revealedp, releasedp, kUserMapSize, kFreeArrayMapSize; cbn [Nat.leb]; split; intros H; repeat (destruct H as [H|H]); try (destruct H as [X H]; try discriminate X); tauto.
Qed.

Lemma rlink_grow_quiet : ltac2:(tb__ "0|5|
ScScSbOF_;S2cS2cS2cS9R6A1M0G0SbS3SdVA;Vrb;R8R1A4S4SdVA;Vrb;R9R1A4R7R1A1A2A2Fz;SbS4R8R1A1M1S2G1A1A2Fz;SfVA;Vrb;RaR7R6A5SbS2RaR1A1A1S0S20S32Q8A1M2A1M3R8R2A1R9R2A1M4A3F_;Fz;SbRbR1A1S2S0G3G4S1cG2A1A3A1F_;Fz;SfVA;Vrb;RcRaR8A5F_;F_;F_;F_;F_;F_;F_;Fm';Fm;Fm0;FN;Fph';Fph;").
Proof.
  intros ph ph' N m0 m m' (Q1 & Q2 & Q3 & Q4) (Q1' & Q2' & Q3' & Q4') HZ ND (L1 & L2 & _) HO HI.
  unfold rlink. rewrite Q1', Q2', Q3', Q4'.
  split; [intros z Hz; rewrite HO by (intros X; apply Hz; apply HZ; right; exact X); apply L1; intros X; apply Hz; apply HZ; left; exact X|].
  split.
  { intros z Hz. apply HZ in Hz. destruct (ND z) as [Y|Y]; [exact (HI z Y)|]. rewrite (HO z Y). destruct Hz as [Hz|Hz]; [exact (L2 z Hz) | contradiction]. }
  split; [intros j Hj; exfalso; lia|]. split; [intros i Hi; exfalso; lia|]. split; intros X; discriminate X.
Qed.

Lemma rlink_quiet_intro : ltac2:(tb__ "0|3|
ScScS2cS2cS2cS9R4A1SbSdVA;Vrb;R7R1A4SdVA;Vrb;R7R2A4F_;Fz;SfVA;Vrb;R7R5R4A5SbS2SdVA;Vrb;R8R1A4A1S0S20S32Q8A1M0A1M1R6R2A1R7R2A1M2A3F_;Fz;SbSdVA;Vrb;R9R1A4S2S0G1G2S1cG0A1A3A1F_;Fz;SfVA;Vrb;R9R8R6A5F_;F_;F_;F_;F_;Fm';Fm;Fm0;Fph';Fph;").
Proof.
  intros ph ph' m0 m m' (Q1' & Q2' & Q3' & Q4') HZ (L1 & _) HO HI.
  unfold rlink. rewrite Q1', Q2', Q3', Q4'.
  split; [intros z Hz; rewrite (HO z Hz); apply L1; intros X; exact (Hz (HZ z X))|].
  split; [exact HI|].
  split; [intros j Hj; exfalso; lia|]. split; [intros i Hi; exfalso; lia|]. split; intros X; discriminate X.
Qed.
End JP.
End RefillJP.

(* [comment removed for export] *)
Module CertMallocSV.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SLit"; "SAlu"; "SVar"; "sobj"; "sprop"; "mkObj"; "mkCell"; "cell"; "DUnknown"; "sv"; "SPBranch"; "SPNot"; "DZero"; "SPUle"; "sstate"; "ss_objs"; "mkSS"; "sprop_eqb"; "ss_facts"; "ss_fcsr"; "ss_fregs"; "ss_lenient"; "ss_next"; "ss_pc"; "ss_regs"; "ss_resv"; "@Corelib.Init.Datatypes"; "cons"; "nil"; "nat"; "prod"; "app"; "pair"; "true"; "bool"; "list"; "option"; "length"; "negb"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_SRL"; "ALU_AND"; "ALU_SUB"; "BC_LTU"; "BC_EQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "SEC_INST"; "kAllocBegMagic"; "@Stdlib.ZArith.BinInt.Z"; "add"; "pow"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.CertMallocSV.NX2"; "RUE"; "L3b"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP"; "M48"; "MSENT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocST"; "rstS"; "BR"; "Bw"; "O_1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "ax_setS"; "sym_runA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.CertMallocSV.NX3"; "a2e8"; "END8"; "B4"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@Corelib.Init.Nat"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.CertMallocSS"; "V_MS"; "V_NCH"; "V_PAB"; "O_errno"; "O_oom"; "O_san"; "V_NS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.CertMallocSV.NX"; "L3"; "B3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.CertMallocSV.NX4"; "UE9"; "BP9"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.CertMallocSV.NX5"; "UBs"; "@Corelib.Lists.ListDef"; "seq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "select"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj"; "split_obj_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.CertMallocSV"; "B4"; "BP9"; "F_g7"; "F_g8"; "F_g9"; "L3b"; "O_3"; "O_3b"; "O_4z"; "O_Mhi"; "O_Mlo"; "O_Pf9"; "O_fill"; "O_pxF"; "O_secgF"; "O_seciF"; "O_secmF"; "O_secsF"; "O_stF"; "PGST"; "a2e8"; "fx8"; "perm7"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc"; "vT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "PG"; "kPtrArrayReserve"; "@Stdlib.Bool.Bool"; "Is_true"; "@Stdlib.Lists.List"; "existsb"; "@stdpp.base"; "filter"; "@stdpp.decidable"; "Is_true_dec"; "@stdpp.list_basics.list"; "list_filter"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymObj SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SoundA EntailA CFGA SysCallA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fi.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fi.Str_memsetZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI SecLog2 CertMallocST.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bc.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.CertMallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SecLog2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocST OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bc.CertMallocSU.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section NX.
Variable nx : positive.

Definition F_A : list sprop := ltac2:(tb__ "0|0|
S1aS4SdS1S26S2Vnx;A1S2S42A1A3S2P9bA1A2S1bS4A1A3").
Definition F_B : list sprop := ltac2:(tb__ "0|0|
S1aS4SdS1S26S2P9bA1S0S2eS2fZ2Z25A2Z1000A2A1A3S2Vnx;A1A2S1bS4A1A3").

Definition B3 : sv := ltac2:(tb__ "0|0|
S1S26S1S27S1S26S2Vnx;A1S0Z1000A1A3S0Z3A1A3S0Z7fff8000A1A3").
Definition a2e6 : sv := ltac2:(tb__ "0|2|
S1S29S1S26S1S27S1S26S2Vnx;A1M0S0Z17f8A1A3S0Z3A1M1A3S0Z1A1A3S1S27S1S26G0S0Z1000A1A3G1A3A3").
Definition L3 : sv := SLit 256.
Definition O_3 : sobj := ltac2:(tb__ "0|0|
S5S4aS0Z0A1S49S1bS7A1S8A5").
Definition ru6 : list (nat * sv) := ltac2:(tb__ "0|1|
S1aS1dS1cS9A2M0S1fS1cS9UcS49A4S1bG0A1A3").
End NX.

Definition rmF (f : list sprop) (E : axst) : axst := ltac2:(tb__ "0|1|
S39VE;A1SeS3aVE;S10S17R1A1S18R1A1S14R1A1S13R1A1S19R1A1SfR1A1S6eS4S22S4A1S70S4A1S4S6cS25S6dS4S11R1A1Vf;A3A1M0A1Lp;S4S6fG0A1Lx;S12R1A1A6S16R1A1S15R1A1A9A2TS;").
Definition runT6 (T : axst) : option (list leafA) := ltac2:(tb__ "0|0|
S3bS40Ufa0S1aS30S34S1bS30A1A3VT;S20A5").

Section NX2.
Variable nx : positive.
Definition RUE : sv := ltac2:(tb__ "0|0|
S1S28S1S26S1S26S1S26S2Vnx;A1S0Z1800A1A3S2PcA1A3S0Z7A1A3S0Zfffffffffffffff8A1A3").
Definition F_g7 : list sprop := ltac2:(tb__ "0|0|
S1aS4SbSaS2aS0Z7fffffffffffA1S31A3A1S1bS4A1A3").
Definition a0e7 : sv := ltac2:(tb__ "0|0|
S1S26S1S27S31S0Z3A1A3S0Z7fff8000A1A3").
Definition a2e7 : sv := ltac2:(tb__ "0|1|
S1S29S1S26S1S27S1S26S1S26S31S1S26S1S29S1S26S2Vnx;A1S0Z1000A1A3S31A3S1S28S1S26S2S48A1S0ZfffA1A3S0Zfffffffffffff000A1A3A3A3S0N8A1A3S0Z3A1M0A3S0Z1A1A3S1S27S31G0A3A3").
Definition L3b : sv := SAlu ALU_ADD L2 (SLit 256).
Definition O_3n : sobj := ltac2:(tb__ "0|0|
S5S36Vnx;A1S0Z0A1S0Z100A1S1bS7A1S8A5").
Definition ru7 : list (nat * sv) := ltac2:(tb__ "0|1|
S1aS1dS1cS9A2M0S1fS1cS9UaS36Vnx;A1A4S1aG0S1fS1cS9UcS32A4S1bG0A1A3A3").
End NX2.
Definition U7p (nx : positive) (E : axst) : axst := ltac2:(tb__ "0|0|
S35VE;S1bS1dS1cS9A2A1S54Vnx;A1A3").

Definition perm7 (n : nat) : list nat := ltac2:(tb__ "0|1|
S1eS1cS1aS1cU0S1aS1cS41Vn;U1M0A2S1aS1cG0S1bS1cA1A3A3A3S4eU2S41Vn;U3A2A2A3").
Definition sel7 (E : axst) : axst := ltac2:(tb__ "0|2|
S3aVE;S51S39VE;A1M0S4fSfG0A1M1S68S24S3G1A2A1A2A2A2").

Section NX3.
Variable nx : positive.
Definition END8 : sv := ltac2:(tb__ "0|0|
S1S26S1S26S1S26S2Vnx;A1S0Z1800A1A3S1S28S2PcA1S0S33A1A3A3S0N8A1A3").
Definition a2e8 : sv := ltac2:(tb__ "0|1|
S1S29S1S26S1S27S3eS0Z3A1M0A3S0Z1A1A3S1S27S1S26S2Vnx;A1S0Z1800A1A3G0A3A3").
Definition B4 : sv := ltac2:(tb__ "0|0|
S1S26S1S27S1S26S2Vnx;A1S0Z1800A1A3S0Z3A1A3S0Z7fff8000A1A3").

Definition F_g8 : list sprop := ltac2:(tb__ "0|0|
S1aS4SaS2aS3dS0ZffffffffffffffffA1A3S1aS4SbSaS2aS0Z7fffffffffffA1S3eA3A1S1aS4SbSaS2bS1S28S2PcA1S0S33A1A3S0Z0A1A3A1S1bS4A1A3A3A3").

Definition fx8 : list sprop := ltac2:(tb__ "0|0|
S1aS4SdS3dS0Z4000000000000000A1A2S1bS4A1A3").
Definition O_3b : sobj := ltac2:(tb__ "0|0|
S5S36Vnx;A1S0Z0A1S57S1bS7A1S8A5").
Definition O_4 : sobj := ltac2:(tb__ "0|0|
S5S3fS0Z0A1S3dS1bS7A1S8A5").
End NX3.
Definition U8p (nx : positive) (E : axst) : axst := ltac2:(tb__ "0|0|
S35VE;S1bS1dS1cS9A2A1S55Vnx;A1A3").
Definition CT8p (nx : positive) (E : axst) : axst := ltac2:(tb__ "0|0|
S35VE;S1bS1dS1cS9A2A1S67Vnx;A1A3").

Section NX4.
Variable nx : positive.
Definition UE9 : sv := ltac2:(tb__ "0|0|
S1S26S1S26S2Vnx;A1S0Z1800A1A3S1S28S2PcA1S0S33A1A3A3").
Definition F_g9 : list sprop := ltac2:(tb__ "0|0|
S1aS4SbSaS2aS0Z7fffffffffffA1S4bA3A1S1bS4A1A3").
Definition BP9 : sv := ltac2:(tb__ "0|0|
S1S26S1S27S4bS0Z3A1A3S0Z7fff8000A1A3").
Definition O_4z : sobj := ltac2:(tb__ "0|0|
S5S52Vnx;A1S0Z0A1S66Vnx;A1S1bS7A1ScA5").
Definition O_P9 : sobj := ltac2:(tb__ "0|0|
S5S4cS0Z0A1S0Z1A1S1bS7A1S8A5").
Definition F_par : sprop := ltac2:(tb__ "0|1|
SaS2bS2PcA1M0S1S28G0S0S33A1A3A3").
End NX4.
Definition U9p (nx : positive) (E : axst) : axst := ltac2:(tb__ "0|0|
S35VE;S1bS1dS1cS9A2A1S56Vnx;A1A3").
Definition PGST : Z := 0x3c728.
Definition runT9 (T : axst) : option (list leafA) := ltac2:(tb__ "0|0|
S3bS40Ufa0S1aS30S34S1aS30S65S1bS30A1A3A3VT;S20A5").
Definition osplit (A : axst) (i : nat) (mid : sv) : axst := ltac2:(tb__ "0|0|
S23SeA1S3cLx;S50S39VA;A1Vi;Vmid;A3SeS3aVA;R1A2LS';VA;X23x2").
Fixpoint find_map (nx : positive) (l : list sobj) (i : nat) : nat :=
  match l with [] => i | o :: t => if sv_eqb (ob_base o) (SVar nx) then i else find_map nx t (S i) end.
Definition runTF (T : axst) : option (list leafA) := ltac2:(tb__ "0|0|
S3bS40Ufa0S1bS30A1VT;S20A5").

Section NX5.
Variable nx : positive.
Definition UBs : sv := ltac2:(tb__ "0|0|
S1S26S2Vnx;A1S0Z1800A1A3").
Definition O_fill : sobj := ltac2:(tb__ "0|0|
S5S4dS0Z0A1S0Z1000A1S1bS7A1S8A5").
Definition O_Mlo (mc : list cell) : sobj := ltac2:(tb__ "0|0|
S5S2Vnx;A1S0Z0A1S0Z1800A1Vmc;ScA5").
Definition O_Mhi : sobj := ltac2:(tb__ "0|0|
S5S2Vnx;A1S0Z2800A1S2S42A1S1bS7A1ScA5").
Definition O_UBs : sobj := ltac2:(tb__ "0|0|
S5S4dS0Z0A1S2PcA1S1bS7A1S8A5").
Definition mc_map : cell := ltac2:(tb__ "0|0|
S6S0Z0A1Z8S2Vnx;A1A3").
Definition mc_ms : cell := mkCell (SLit 8) 8 msx.
Definition mc_ns : cell := mkCell (SLit 16) 8 (SVar V_NS).
Definition mc_idx : cell := ltac2:(tb__ "0|0|
S6S0Z18A1Z8S2S43A1A3").
Definition mc_magic : cell := ltac2:(tb__ "0|0|
S6S0Z1000A1Z8S0S2dA1A3").
Definition mc_cptr : cell := ltac2:(tb__ "0|0|
S6S0Z1008A1Z8S1S26S2Vnx;A1S0Z17f0A1A3A3").
Definition mc_state : cell := mkCell (SLit 6128) 1 (SLit 2).
Definition mc_type (t : Z) : cell := mkCell (SLit 6129) 1 (SLit t).
Definition mc_sizehi : cell := ltac2:(tb__ "0|0|
S6S0Z17f2A1Z2S1S27S2PcA1S0Z20A1A3A3").
Definition mc_size : cell := mkCell (SLit 6132) 4 (SVar 12).
Definition O_Pf9 : sobj := ltac2:(tb__ "0|2|
S5S53Vnx;A1S0Z0A1M0S0Z1M1A1S1aS7S6G0G1S1S28S2PcA1S0Z7A1A3A3S1bS7A1A3S8A5").
Definition xc_map : cell := ltac2:(tb__ "0|0|
S6S0Z0A1Z8S2Vnx;A1A3").
End NX5.
Definition O_seciF (c : list cell) : sobj := ltac2:(tb__ "0|0|
S5S0Z0A1S0S2cA1S0S2eS2cZ40A2A1Vc;S8A5").
Definition O_secsF (c : list cell) : sobj := ltac2:(tb__ "0|0|
S5S0Z0A1S0S2eS2cZ40A2A1S0Zee040A1Vc;S8A5").
Definition O_secmF : sobj := ltac2:(tb__ "0|2|
S5S0Z0A1M0S0Zee040A1M1S0Zee044A1S1aS7S6G1Z1G0A3S1aS7S6S0Zee041A1Z3G0A3S1bS7A1A3A3S8A5").
Definition O_secgF (c : list cell) : sobj := ltac2:(tb__ "0|0|
S5S0Z0A1S0Zee048A1S0Zee070A1Vc;S8A5").
Definition O_stF (c : list cell) : sobj := ltac2:(tb__ "0|0|
S5S69S0Zad0A1S0Zc60A1Vc;S8A5").
Definition O_pxF (blk : Z) (d : odefault) (c : list cell) : sobj := ltac2:(tb__ "0|0|
S5S37S0Z0A1S0Vblk;A1Vc;Vd;A5").
Definition ic_pg : cell := ltac2:(tb__ "0|0|
S6S0S2cA1Z8S0S6aA1A3").
Definition ic_c1 : cell := ltac2:(tb__ "0|1|
S6S0S2eS2cZ8M0A2A1G0S2S44A1A3").
Definition ic_c2 : cell := ltac2:(tb__ "0|0|
S6S0S2eS2cZ10A2A1Z8S2S44A1A3").
Definition ic_rs : cell := ltac2:(tb__ "0|0|
S6S0S2eS2cZ18A2A1Z8S0S6bA1A3").
Definition ic_nres (e : sv) : cell := ltac2:(tb__ "0|0|
S6S0S2eS2cZ30A2A1Z8Ve;A3").
Definition ic_nch : cell := ltac2:(tb__ "0|0|
S6S0S2eS2cZ38A2A1Z8S1S26S2S43A1S0Z1A1A3A3").
Definition RSF (nx : positive) (c1 c2 c4 c5 mc xc : list cell) (blk : Z) (dpx : odefault) (partial : bool) : list sobj := ltac2:(tb__ "0|1|
S1eS3S1aS3S5eVnx;A1S1aS3S5aVnx;A1S1aS3S59Vnx;A1S1aS3S58Vnx;A1S1aS3S38Vnx;A1S1bS3A1M0A3A3A3A3A3S1eS3S1aS3S61Vc1;A1S1aS3S63Vc2;A1S1aS3S62S1aS3S60Vc4;A1S1aS3S47S1aS3S46S1aS3S45S1aS3S64Vc5;A1G0A3A3A3A3A3A3A3A3S1eS3S1aS3S5cVnx;Vmc;A2S1aS3S5bVnx;A1S1aS3S5fVblk;Vdpx;Vxc;A3G0A3A3A3S21S22S3A1Lpartial;Vpartial;S1aS3S5dVnx;A1G0A3G0X21x2A3A3A3").
End CertMallocSV.

