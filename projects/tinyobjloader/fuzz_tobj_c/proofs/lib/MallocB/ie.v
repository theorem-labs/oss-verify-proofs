(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith List Bool Lia Permutation FunctionalExtensionality.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic SegQ_wf2.

(* [comment removed for export] *)
Module SegQ3_skel.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "pair"; "cons"; "nat"; "nil"; "list"; "prod"; "bool"; "true"; "app"; "length"; "option"; "None"; "false"; "Some"; "fst"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "qbatch"; "aa_q_global"; "AA"; "aa_q_thread"; "aa_cache_inited"; "qb_addr"; "@Corelib.Init.Logic"; "eq"; "not"; "and"; "ex"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sobj"; "valuation"; "rw"; "eval"; "SLit"; "mkSS"; "ss_objs"; "FcsrFrm0"; "SVar"; "rm"; "sprop"; "sprop_below"; "ss_facts"; "ss_fcsr"; "ss_fregs"; "ss_lenient"; "ss_pc"; "ss_regs"; "ss_resv"; "sstate"; "agree_below"; "enc_bytes"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@Stdlib.ZArith.BinInt.Z"; "add"; "of_nat"; "le"; "lt"; "pow"; "mul"; "@stdpp.bitvector.definitions"; "Z_to_bv"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.SegQ3_states"; "QG"; "ZQ"; "KEEP3"; "NX3"; "PostQ3e"; "PostQ3n"; "vTB"; "vTF"; "vTN"; "vGB"; "vGF"; "F_T"; "F_T0"; "F_Tn"; "O_gmax"; "O_gq"; "O_mtx0'"; "O_tq"; "PreQ3e"; "PreQ3n"; "ReQ3e"; "ReQ3n"; "gsz"; "regs3"; "vGN"; "vGS"; "vMIN"; "vTS"; "DRAIN"; "O_glb"; "RETD"; "vGBN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf2"; "JQ3"; "qbounded"; "JLQ3"; "batch_mem"; "batch_pure"; "set_q"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "ax_setS"; "entailsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states"; "NPRE"; "add"; "NXQ"; "post_ru"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ie.SegQ3_skel"; "rhoT"; "PostQ3"; "PreQ3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "qsize"; "qb_dflt"; "qlinks"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "cell_ok"; "bview"; "mkACell"; "acell"; "c_addr"; "c_w"; "present"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "etriple"; "triple"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegQsep"; "last_addr"; "hd_addr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegQpiece"; "keeps"; "@Stdlib.Lists.List"; "In"; "last"; "forallb"; "removelast"; "NoDup"; "hd"; "@Corelib.Lists.ListDef"; "map"; "Forall"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ie.SegQ3_skel.Drain"; "KEPT3"; "PostQ3e_k"; "PostQ3n_k"; "sde"; "sdn"; "HRECE_e"; "HRECE_n"; "HREC_e"; "HREC_n"; "N3e"; "N3n"; "REST3e"; "REST3n"; "S1e"; "S1n"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "pre_fregs"; "setregs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM"; "carve_obj"; "carve_spec"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "kQuarantineMax"; "kQuarantineMin"; "kQuarantineBatchSize";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "A_globals"; "mkA"; "stack_win"; "@Corelib.Init.Peano"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegD_glue"; "rho_sets"; "@stdpp.base"; "NoDup"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia Permutation FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundM SymEntail SymFrame SymCFG SymCall SymSummary ExampleMemcpy Glue3 SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA CFGA SummaryA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Inv Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQ_defs SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegD_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegQsep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.SegQ3_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegQpiece OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.SegQ3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Lemma present_cell8q : ltac2:(tb__ "0|0|
S74SfS79R2R1S33R1Z8A2A3S1aSfSfS19S19S35Z0R1A2S36R1S37Z2Z40A2A2A2S73R4S75R3U8R1A3A2A2Lv;A2F_;Fa;Fm;").
Proof.
  intros m a Hp.
  destruct (Hp a ltac:(lia)) as [b0 H0]. destruct (Hp (a + 1) ltac:(lia)) as [b1 H1]. destruct (Hp (a + 2) ltac:(lia)) as [b2 H2]. destruct (Hp (a + 3) ltac:(lia)) as [b3 H3].
  destruct (Hp (a + 4) ltac:(lia)) as [b4 H4]. destruct (Hp (a + 5) ltac:(lia)) as [b5 H5]. destruct (Hp (a + 6) ltac:(lia)) as [b6 H6]. destruct (Hp (a + 7) ltac:(lia)) as [b7 H7].
  exists (bv_unsigned (le_bytes_to_word [b0; b1; b2; b3; b4; b5; b6; b7])).
  assert (E : Z_to_bv 64 (bv_unsigned (le_bytes_to_word [b0; b1; b2; b3; b4; b5; b6; b7])) = le_bytes_to_word [b0; b1; b2; b3; b4; b5; b6; b7]) by apply Z_to_bv_bv_unsigned.
  split; [pose proof (urange (le_bytes_to_word [b0; b1; b2; b3; b4; b5; b6; b7])); lia|].
  unfold cell_ok. cbn [c_addr c_w RtCells.c_val]. intros k Hk. rewrite E. rewrite (enc_bytes_le_word 8) by (reflexivity || lia).
  destruct k as [|[|[|[|[|[|[|[|k]]]]]]]]; cbn [nth]; rewrite ?Z.add_0_r; try assumption. cbn in Hk. lia.
Qed.

Lemma qsize_app : ltac2:(tb__ "0|1|
S4S11A1M0G0S17SfS70S8S11R2R1A3A1S33S70R2A1S70R1A1A2A3Fl2;Fl1;").
Proof. intros l1 l2. unfold qsize. induction l1 as [|b l1 IH]; cbn; [reflexivity | rewrite IH; lia]. Qed.

Lemma qsize_ge : ltac2:(tb__ "0|0|
S13S74S4S11A1S88S11S61R3A1R1A3S88S11S60R3A1R2A3S35S38Sa3S34S9S11R3A2A1A2S70R3A1A2F_;F_;Fl;Fm;FA;").
Proof.
  intros A m l HP HM. induction l as [|b l IH]; [cbn; lia|].
  pose proof (Forall_inv HP) as (_ & _ & _ & Hits). pose proof (Forall_inv HM) as (_ & _ & Hs & _).
  specialize (IH (Forall_inv_tail HP) (Forall_inv_tail HM)). unfold qsize in *. cbn [fold_right length]. rewrite Nat2Z.inj_succ.
  assert (0 <= fold_right (fun it acc => snd it + acc) 0 (qb_items b)).
  { clear -Hits. induction Hits as [|it r Hit _ IHr]; cbn; [lia|]. destruct Hit as (_ & Hn & _). lia. }
  unfold kQuarantineBatchSize in *. lia.
Qed.

Definition PreQ3 : axst := ltac2:(tb__ "0|0|
Sa5S21S57S52S99S23SbS1bA1S1S1cSa6Sa4A3S47S67ScA9S3S5S1bS1bA2A1A2").
Definition PostQ3 : axst := ltac2:(tb__ "0|0|
Sa5S21S59S9aS52S6aA2S99S23SbS1bA1S1S1cSa6Sa4A3S47S69ScA9S3S5S1bS1bA2A1A2").

Definition rhoT (A : AA) (gf gb : Z) (rho : valuation) : valuation := ltac2:(tb__ "0|4|
S14VA;A1S4S11A1M0S12VA;A1G0Sa8Vrho;S1S5S10S3aQ40M1A1M2A2M3S0S10G2Pc8S39G1S34S9S11R2A2A1A2A4S1G3S0S10G2Pc9S39G1S7fR2A1A2A4S1G3S0S10G2PcaS39G1S7eR2A1A2A4S1G3S0S10G2PcbS39G1S70R2A1A2A4S1G3S0S10G2PccS39G1S34S9S11R1A2A1A2A4S1G3S0S10G2PcdS39G1Vgf;A2A4S1G3S0S10G2PceS39G1Vgb;A2A4S1G3S0S10G2PcfS39G1S70R1A1A2A4S1G3S0S10G2Pd0S39G1Sa2A2A4S1G3S0S10G2Pd1S39G1Z0A2A4S3G3A1A3A3A3A3A3A3A3A3A3A3A2Tgl;Ttl;").

Section Drain.
Let segs : list Segment := segsA.
Variable K : AA -> jpredA.
Variable ok : assn.
Hypothesis HL : KQ_laws segsA K.
Hypothesis HOK : ltac2:(tb__ "0|0|
S13S5cS32Vok;VK;R1A1A3FA;").

Definition N3n : list carve_spec := ltac2:(tb__ "0|f|
S1S5S5S5S1bSfA2M0SfA2M1S4S5S5SfS2A2M2S1bA2M3A1M4A2M5S0G1G4S0G0SfS0S1bSfS24PdA1Z0M6A4Z20A4S1G3S0G2S1bS0SfS2G6U8M7A4M8S43A4S1G3S0G2S1bS0SfS2Z8M9G7A4S42A4S1G3S0G2S1bS0SfS2Z10G7A4S41A4S1G3S0G2S1bS0SfS2Z18G7A4S56A4S3G3A1MaA3A3A3A3A4S1G5S0G1G4S0G0SfS0S1bSfS20G6A1MbS33S3bZ98A2McA4S33S3bZ9cA2A4S1G3S0G2S1bS0SfS2GcU4A4GbA4GaA3A4S1G5S0G1G4S0G0SfS0S1bSfGbS33S3bZa0A2MdA4S33S3bZc0A2A4S1G3S0G2S1bS0SfS2GdG7A4S53A4S1G3S0G2S1bS0SfS2S33S3bZa8A2G7A4S45A4S1G3S0G2S1bS0SfS2S33S3bZb0A2G7A4S44A4S1G3S0G2S1bS0SfS2S33S3bZb8A2G7A4S54A4GaA3A3A3A3A4S1G5S0G1G4S0G0SfS0S1bSfGbS33S3bZ40A2MeA4S33S3bZ50A2A4S1G3S0G2S1bS0SfS2GeG7A4S20Sa1A1A4S1G3S0G2S1bS0SfS2S33S3bZ48A2G7A4S55A4GaA3A3A4S1G5S0G1G4S0G0SfS0S1bSfS44G6A4G9A4S1G3S0G2S1bG8S5aA4GaA3A4S3G5A1A3A3A3A3A3").
Definition N3e : list carve_spec := ltac2:(tb__ "0|d|
S1S5S5S5S1bSfA2M0SfA2M1S4S5S5SfS2A2M2S1bA2M3A1M4A2M5S0G1G4S0G0SfS0S1bSfS24PdA1Z0M6A4Z20A4S1G3S0G2S1bS0SfS2G6U8M7A4S43A4S1G3S0G2S1bS0SfS2Z8G7A4S42A4S1G3S0G2S1bS0SfS2Z10G7A4S41A4S1G3S0G2S1bS0SfS2Z18G7A4S56A4S3G3A1M8A3A3A3A3A4S1G5S0G1G4S0G0SfS0S1bSfS20G6A1M9S33S3bZ98A2MaA4S33S3bZ9cA2A4S1G3S0G2S1bS0SfS2GaU4A4G9A4G8A3A4S1G5S0G1G4S0G0SfS0S1bSfG9S33S3bZa0A2MbA4S33S3bZc0A2A4S1G3S0G2S1bS0SfS2GbG7A4G9A4S1G3S0G2S1bS0SfS2S33S3bZa8A2G7A4S45A4S1G3S0G2S1bS0SfS2S33S3bZb0A2G7A4S44A4S1G3S0G2S1bS0SfS2S33S3bZb8A2G7A4S54A4G8A3A3A3A3A4S1G5S0G1G4S0G0SfS0S1bSfG9S33S3bZ40A2McA4S33S3bZ50A2A4S1G3S0G2S1bS0SfS2GcG7A4S20Sa1A1A4S1G3S0G2S1bS0SfS2S33S3bZ48A2G7A4S55A4G8A3A3A4S3G5A1A3A3A3A3").
Definition S1n : sstate := ltac2:(tb__ "0|0|
S63S6dA1S2fS21S2cR1A1S2dR1A1S2aR1A1S29R1A1S2eR1A1S8S1cS22R1A1S87Sa0S1cS9fS94A4A3S28R1A1S3eS2bR1A1A9TS;").
Definition S1e : sstate := ltac2:(tb__ "0|0|
S63S6dA1S2fS21S2cR1A1S2dR1A1S2aR1A1S29R1A1S2eR1A1S8S1cS22R1A1S87Sa0S1cS9fS93A4A3S28R1A1S3eS2bR1A1A9TS;").
Lemma S1n_swf : swf S1n = true. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma S1e_swf : swf S1e = true. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma S1n_pre : ltac2:(tb__ "0|0|
S17S64S9eS65S6dS98A2S48A2S4eA3"). Proof. reflexivity. Qed.
Lemma S1e_pre : ltac2:(tb__ "0|0|
S17S64S9eS65S6dS97A2S46A2S4dA3"). Proof. reflexivity. Qed.
Lemma F_Tn_below : ltac2:(tb__ "0|0|
S17S6S83S26S27S3eA1S48A3S7A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma F_T_below : ltac2:(tb__ "0|0|
S17S6S83S26S27S3eA1S46A3S7A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma qlinks_last : ltac2:(tb__ "0|1|
S74S4S11A1M0S72R2R1A2S18S17G0R2S3S11A1A3A1S73R4S75S7eR3A1U8Z0A3A2F_;F_;Fl;Fm;").
Proof.
  intros m l. induction l as [|b l IH]; intros H Hne; [congruence|]. cbn [qlinks] in H. destruct H as [Hc Hr].
  unfold last_addr. destruct l as [|b' l']; [cbn; exact Hc|]. cbn [last]. apply IH; [exact Hr | discriminate].
Qed.
Lemma In_last : ltac2:(tb__ "0|1|
S4S11A1M0S11S18S17G0R2S3S11A1A3A1S81S11S82S11R3R2A3R3A3F_;Fd;Fl;").
Proof. intros l d H. rewrite (app_removelast_last d H) at 2. apply in_or_app. right. left. reflexivity. Qed.
Lemma In_hd : ltac2:(tb__ "0|1|
S4S11A1M0S11S18S17G0R2S3S11A1A3A1S81S11S86S11R2R3A3R3A3F_;Fd;Fl;").
Proof. intros [|b l] d H; [congruence | left; reflexivity]. Qed.

Lemma NoDup10 : ltac2:(tb__ "0|4|
S85S10S87S5S10S3aQ40M0A1M1A2M2S10SeS10G1A2S1G2S0S10G1Pc8S39G0Z0A2M3A4S1G2S0S10G1Pc9G3A4S1G2S0S10G1PcaG3A4S1G2S0S10G1PcbG3A4S1G2S0S10G1PccG3A4S1G2S0S10G1PcdG3A4S1G2S0S10G1PceG3A4S1G2S0S10G1PcfG3A4S1G2S0S10G1Pd0G3A4S1G2S0S10G1Pd1G3A4S3G2A1A3A3A3A3A3A3A3A3A3A3A4A2").
Proof. cbn. repeat (constructor; [cbn; intros HH; repeat (destruct HH as [HH|HH]; [discriminate HH|]); exact HH|]). constructor. Qed.

Lemma entry_n : ltac2:(tb__ "0|3|
S13S1dS4S3aQ40A1A1S7aS18S17S4S11A1M0S14R4A1S3S11A1M1A3A1S18S17G0S12R5A1G1A3A1S17S6S15R6A1S7A3S5eR7A1S5bS32S5dS32VK;R8A3S6dR7R6R5A6S5bS32S5dS32VK;R9A3S4eS6bR9S7fS12R9A1M2A1S7eG2A1R8A4R7R6A6F_;F_;F_;F_;F_;Fw;Ftp;Frho;FA;").
Proof.
  intros A rho tp w HTL HGL HCI HBND H.
  pose proof (proj2 H) as [HK HQ]. cbn [w_tr w_cfg cfg_model fst snd] in HK, HQ.
  destruct (kq_facts segsA K HL A rho tp _ _ HK) as [HG HRIG HRTC HMIN HST HLEN HCLS HQP HIDS HSEP HSEP3 HKTOP HKSECQ].
  pose proof (topG_range (aa_geom A)) as ACV. pose proof kSpaceSize_val as KSV.
  pose proof HG as HG0. apply geom_old in HG. rewrite FS_total_val, KSV in HG. unfold HIGH_SHADOW_END, IMG_HI, PG in HG.
  destruct HG as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & Grest).
  pose proof (geom_bands _ HG0) as (_ & _ & _ & _ & TI & _). unfold IMG_LO, IMG_HI in TI.
  clear Grest.
  destruct HRIG as (E151 & E152 & E155 & E156).

  destruct HQ as (HBM & HLT & HLG & HHT & HHG & HMTX). destruct HQP as [HBP HND]. unfold qall in HBP, HND.
  destruct HHT as (HT0 & HT12 & HTP & HT3). destruct (HT12 HTL) as [HT1 HT2]. clear HT12.
  destruct HHG as (HG0' & HG12 & HGP & HG3). destruct (HG12 HGL) as [HGa HGb]. clear HG12.
  pose proof (proj1 (Forall_forall _ _) HBP _ (in_or_app _ _ _ (or_intror (In_last (aa_q_global A) qb_dflt HGL)))) as (LB1 & LB2 & (y & LBy & Ly0 & Lal & Ly1) & _).
  pose proof (qlinks_last _ (aa_q_global A) HLG HGL) as HLNK.
  change (qb_addr (last (aa_q_global A) qb_dflt)) with (last_addr (aa_q_global A)) in HGb, LBy, LB1, HLNK.
  change (qb_addr (hd qb_dflt (aa_q_global A))) with (hd_addr (aa_q_global A)) in HGa.
  change (qb_addr (last (aa_q_thread A) qb_dflt)) with (last_addr (aa_q_thread A)) in HT2. change (qb_addr (hd qb_dflt (aa_q_thread A))) with (hd_addr (aa_q_thread A)) in HT1.
  destruct (cv_bounds _ _ _ _ _ (HCLS HCI 24 ltac:(lia))) as (C1 & C2 & C3 & C4).
  unfold kUserMapSize, kUserSpaceSize, kRegionSize, kFreeArraySize in C3. unfold region_beg, kRegionSize in LBy. unfold kQuarantineBatchSize in Ly1.

  pose proof (SPA_facts_hold segsA _ rho PreQ3 tp w H) as HF0. cbn [ax_S PreQ3 ss_facts] in HF0.
  assert (U13 : bv_unsigned (rw rho 13%positive) = ag_thread (aa_geom A) + 80).
  { unfold F_T0 in HF0. apply Forall_app in HF0 as [_ HF1].
    pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail HF1))) as X. cbn [holds branch_taken] in X. unfold add, vT in X. cbn [eval] in X. unfold bv_eqb in X.
    apply Z.eqb_eq in X. rewrite add_val, E151, !u64_lit in X by lia. rewrite Z.mod_small in X by lia. exact X. }

  set (rho1 := rhoT A (hd_addr (aa_q_global A)) (last_addr (aa_q_global A)) rho).
  assert (Hag1 : agree_below NPRE rho rho1).
  { unfold rho1, rhoT. apply agree_below_rho_sets. intros j v Hin. cbn in Hin. unfold NPRE.
    repeat (destruct Hin as [E|Hin]; [injection E; intros; subst; cbv; discriminate|]). destruct Hin. }
  assert (H1 : SPA segsA (JQ3 segsA K A) PreQ3 rho1 tp w).
  { eapply SPA_agree; [exact Hag1 | | exact H]. intros HJ. eapply (JQ3_stable segsA K A NPRE HL ltac:(apply Pos.le_refl)); [exact Hag1 | apply mat_equiv_refl | exact HJ]. }
  assert (Erm : rm rho1 = rm rho) by (unfold rho1, rhoT; apply rm_rho_sets).
  assert (EE : forall i v, In (i, v) [(200%positive, Z_to_bv 64 (Z.of_nat (length (aa_q_thread A)))); (201%positive, Z_to_bv 64 (hd_addr (aa_q_thread A)));
                (202%positive, Z_to_bv 64 (last_addr (aa_q_thread A))); (203%positive, Z_to_bv 64 (qsize (aa_q_thread A)));
                (204%positive, Z_to_bv 64 (Z.of_nat (length (aa_q_global A)))); (205%positive, Z_to_bv 64 (hd_addr (aa_q_global A)));
                (206%positive, Z_to_bv 64 (last_addr (aa_q_global A))); (207%positive, Z_to_bv 64 (qsize (aa_q_global A)));
                (208%positive, Z_to_bv 64 kQuarantineMin); (209%positive, Z_to_bv 64 0)] -> rw rho1 i = v).
  { intros i v Hin. unfold rho1, rhoT. apply rw_rho_sets_in; [exact NoDup10 | exact Hin]. }
  assert (E200 : rw rho1 200%positive = Z_to_bv 64 (Z.of_nat (length (aa_q_thread A)))) by (apply EE; cbn [In]; do 0 right; left; reflexivity).
  assert (E201 : rw rho1 201%positive = Z_to_bv 64 (hd_addr (aa_q_thread A))) by (apply EE; cbn [In]; do 1 right; left; reflexivity).
  assert (E202 : rw rho1 202%positive = Z_to_bv 64 (last_addr (aa_q_thread A))) by (apply EE; cbn [In]; do 2 right; left; reflexivity).
  assert (E203 : rw rho1 203%positive = Z_to_bv 64 (qsize (aa_q_thread A))) by (apply EE; cbn [In]; do 3 right; left; reflexivity).
  assert (E204 : rw rho1 204%positive = Z_to_bv 64 (Z.of_nat (length (aa_q_global A)))) by (apply EE; cbn [In]; do 4 right; left; reflexivity).
  assert (E205 : rw rho1 205%positive = Z_to_bv 64 (hd_addr (aa_q_global A))) by (apply EE; cbn [In]; do 5 right; left; reflexivity).
  assert (E206 : rw rho1 206%positive = Z_to_bv 64 (last_addr (aa_q_global A))) by (apply EE; cbn [In]; do 6 right; left; reflexivity).
  assert (E207 : rw rho1 207%positive = Z_to_bv 64 (qsize (aa_q_global A))) by (apply EE; cbn [In]; do 7 right; left; reflexivity).
  assert (E208 : rw rho1 208%positive = Z_to_bv 64 kQuarantineMin) by (apply EE; cbn [In]; do 8 right; left; reflexivity).
  assert (E209 : rw rho1 209%positive = Z_to_bv 64 0) by (apply EE; cbn [In]; do 9 right; left; reflexivity).
  clear EE.
  assert (E13 : rw rho1 13%positive = rw rho 13%positive) by (symmetry; apply (proj1 Hag1); cbv; reflexivity).
  assert (E151' : rw rho1 151%positive = Z_to_bv 64 (ag_thread (aa_geom A))) by (rewrite <- E151; symmetry; apply (proj1 Hag1); cbv; reflexivity).

  assert (HMAX : cell_ok (view segsA (rm rho)) (mkACell (QG + 64) 8 kQuarantineMax)).
  { unfold rtc_inv, rtc_cells in HRTC. exact (cells_ok_nth _ _ 7 _ HRTC eq_refl). }
  pose proof (proj1 (proj1 H1)) as Hsm1. unfold virt in Hsm1. cbn [fst snd w_tr w_cfg cfg_ms cfg_model ax_S] in Hsm1.
  pose proof (SPA_facts_hold segsA _ rho1 PreQ3 tp w H1) as HFa1.
  assert (Hhigh : holds rho1 F_sp_high) by (apply (proj1 (Forall_forall _ _) HFa1); cbn [In ss_facts ax_S PreQ3 mkA F_T0 pre_facts app]; tauto).
  destruct (stack_win_range _ rho1 _ _ Hsm1 ltac:(cbn; tauto) Hhigh) as (SW1 & SW2 & SW3).
  assert (TOPlo : topG (aa_geom A) <= fst (obj_range rho1 stack_win)).
  { pose proof HKTOP as HT. unfold top_high in HT. change (fst (obj_range rho1 stack_win)) with (bv_unsigned (rw rho1 10%positive) + bv_signed (rw rho1 V_DEPTH)).
    rewrite <- (proj1 Hag1 10%positive), <- (proj1 Hag1 V_DEPTH) by (cbv; reflexivity). exact HT. }
  assert (GBND : 0x10007fff8000 <= last_addr (aa_q_global A) /\ last_addr (aa_q_global A) + 8192 <= 140737479966720).
  { unfold HIGH_SHADOW_END in LB1. split; [exact LB1|]. rewrite LBy. lia. }
  unfold QG, Inv.QG in *.
  assert (TLlen : 0 < Z.of_nat (length (aa_q_thread A))) by (destruct (aa_q_thread A); [congruence | cbn; lia]).

  assert (H2 : SPA segsA (JQ3 segsA K A) (ax_setS PreQ3 S1n) rho1 tp w).
  { unfold S1n. eapply SPA_carve_list; [exact H1 | exact S1n_swf | cbv; discriminate | | |].
    - unfold N3n. unfold vTN, vTF, vTB, vTS, vGN, vGF, vGB, vGS, vMIN, vGBN.
      repeat apply Forall_cons; try apply Forall_nil; unfold QG, Inv.QG; cbn [eval]; rewrite ?E13, ?E206, ?U13; rewrite ?u64_lit by lia.
      all: split; [lia|]. all: split; [lia|]. all: split; [lia|]. all: split; [lia|]. all: split; [lia|].
      all: split; [unfold cells_inside; repeat apply Forall_cons; try apply Forall_nil; cbn; lia|].
      all: split; [|split; [|apply xwords_clear_nil]].
      all: rewrite ?Erm.
      + intros off Hoff.
        destruct (Z_lt_dec off 8); [|destruct (Z_lt_dec off 16); [|destruct (Z_lt_dec off 24)]].
        * eapply (cell_wok_rd2 _ _ _ _ _ HT0); cbn [Z.of_nat]; lia.
        * eapply (cell_wok_rd2 _ _ _ _ _ HT1); cbn [Z.of_nat]; lia.
        * eapply (cell_wok_rd2 _ _ _ _ _ HT2); cbn [Z.of_nat]; lia.
        * eapply (cell_wok_rd2 _ _ _ _ _ HT3); cbn [Z.of_nat]; lia.
      + unfold cells_in_view. repeat apply Forall_cons; try apply Forall_nil.
        * eapply (civ_cell rho1 (rm rho) (ag_thread (aa_geom A) + 80) 0); [rewrite Z.add_0_r; exact HT0 | cbn [eval]; exact E200 | lia | lia].
        * eapply (civ_cell rho1 (rm rho) (ag_thread (aa_geom A) + 80) 8); [exact HT1 | cbn [eval]; exact E201 | lia | lia].
        * eapply (civ_cell rho1 (rm rho) (ag_thread (aa_geom A) + 80) 16); [exact HT2 | cbn [eval]; exact E202 | lia | lia].
        * eapply (civ_cell rho1 (rm rho) (ag_thread (aa_geom A) + 80) 24); [exact HT3 | cbn [eval]; exact E203 | lia | lia].
      + intros off Hoff; split; [apply wok_of_imageA; lia | apply rd_of_imageA; lia].
      + unfold cells_in_view. repeat apply Forall_cons; try apply Forall_nil.
        eapply (civ_cell rho1 (rm rho) 0 (961840 + 152)); [exact HMTX | reflexivity | lia | lia].
      + intros off Hoff; split; [apply wok_of_imageA; lia | apply rd_of_imageA; lia].
      + unfold cells_in_view. repeat apply Forall_cons; try apply Forall_nil.
        * eapply (civ_cell rho1 (rm rho) 0 (961840 + 160)); [first [exact HG0' | rewrite (Z.add_0_r (961840 + 160)) in HG0'; exact HG0'] | cbn [eval]; exact E204 | lia | lia].
        * eapply (civ_cell rho1 (rm rho) 0 (961840 + 168)); [exact HGa | cbn [eval]; exact E205 | lia | lia].
        * eapply (civ_cell rho1 (rm rho) 0 (961840 + 176)); [exact HGb | cbn [eval]; exact E206 | lia | lia].
        * eapply (civ_cell rho1 (rm rho) 0 (961840 + 184)); [exact HG3 | cbn [eval]; exact E207 | lia | lia].
      + intros off Hoff; split; [apply wok_of_imageA; lia | apply rd_of_imageA; lia].
      + unfold cells_in_view. repeat apply Forall_cons; try apply Forall_nil.
        * eapply (civ_cell rho1 (rm rho) 0 (961840 + 64)); [exact HMAX | reflexivity | lia | lia].
        * eapply (civ_cell rho1 (rm rho) 0 (961840 + 72)); [exact HMIN | cbn [eval]; exact E208 | lia | lia].
      + intros off Hoff. eapply (cell_wok_rd _ _ _ _ _ HLNK); cbn [Z.of_nat]; lia.
      + unfold cells_in_view. repeat apply Forall_cons; try apply Forall_nil.
        eapply (civ_cell rho1 (rm rho) (last_addr (aa_q_global A)) 0); [rewrite Z.add_0_r; exact HLNK | cbn [eval]; exact E209 | lia | lia].
    -
      assert (QF : forall z, last_addr (aa_q_global A) <= z < last_addr (aa_q_global A) + 8192 -> ~ (ag_thread (aa_geom A) <= z < ag_thread (aa_geom A) + 4096)).
      { intros z Hz. apply HSEP. unfold q_foot. apply Exists_exists. exists (last (aa_q_global A) qb_dflt). split; [apply in_or_app; right; apply In_last; exact HGL|].
        left. unfold kQuarantineBatchSize. exact Hz. }
      pose proof (QF (last_addr (aa_q_global A)) ltac:(lia)) as QF0.
      unfold N3n. cbn [map carve_obj ss_objs ax_S PreQ3 mkA app]. unfold carved, vTN, vTF, vTB, vTS, vGN, vGF, vGB, vGS, vMIN, vGBN.
      unfold A_globals, O_got, O_rtc, GOT_LO, GOT_HI, RTC_LO, RTC_HI, QG.
      destruct (obj_range rho1 stack_win) as [slo shi] eqn:ESW. cbn [fst snd] in SW1, SW2, SW3, TOPlo.
      apply Forall_cons; [(apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]; unfold ranges_disjoint; rewrite ?ESW;
                      rewrite ?obj_range_mk by lia; cbn [fst snd eval]; rewrite ?E13, ?E206, ?U13; rewrite ?u64_lit by lia; lia)|]. apply Forall_cons; [(apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]; unfold ranges_disjoint; rewrite ?ESW;
                      rewrite ?obj_range_mk by lia; cbn [fst snd eval]; rewrite ?E13, ?E206, ?U13; rewrite ?u64_lit by lia; lia)|]. apply Forall_cons; [(apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]; unfold ranges_disjoint; rewrite ?ESW;
                      rewrite ?obj_range_mk by lia; cbn [fst snd eval]; rewrite ?E13, ?E206, ?U13; rewrite ?u64_lit by lia; lia)|]. apply Forall_cons; [(apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]; unfold ranges_disjoint; rewrite ?ESW;
                      rewrite ?obj_range_mk by lia; cbn [fst snd eval]; rewrite ?E13, ?E206, ?U13; rewrite ?u64_lit by lia; lia)|]. apply Forall_cons; [(apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]; unfold ranges_disjoint; rewrite ?ESW;
                      rewrite ?obj_range_mk by lia; cbn [fst snd eval]; rewrite ?E13, ?E206, ?U13; rewrite ?u64_lit by lia; lia)|]. apply Forall_nil.
    -
      assert (QF : forall z, last_addr (aa_q_global A) <= z < last_addr (aa_q_global A) + 8192 -> ~ (ag_thread (aa_geom A) <= z < ag_thread (aa_geom A) + 4096)).
      { intros z Hz. apply HSEP. unfold q_foot. apply Exists_exists. exists (last (aa_q_global A) qb_dflt). split; [apply in_or_app; right; apply In_last; exact HGL|].
        left. unfold kQuarantineBatchSize. exact Hz. }
      pose proof (QF (last_addr (aa_q_global A)) ltac:(lia)) as QF0. pose proof (QF (last_addr (aa_q_global A) + 7) ltac:(lia)) as QF7.
      unfold N3n. cbn [map carve_obj pairwise_disjoint]. unfold carved, vTN, vTF, vTB, vTS, vGN, vGF, vGB, vGS, vMIN, vGBN, QG.
      repeat split; repeat apply Forall_cons; try apply Forall_nil; try exact I; unfold ranges_disjoint;
        rewrite ?obj_range_mk by lia; cbn [fst snd eval]; rewrite ?E13, ?E206, ?U13; rewrite ?u64_lit by lia; lia. }
  clear H1.

  rewrite <- S1n_pre. eapply SPA_refacts; [exact H2 | exact F_Tn_below |].
  cbn [ax_S ax_setS ss_facts PreQ3 mkA]. intros HF. unfold F_Tn. apply Forall_app. split; [exact HF|].
  assert (LEN2 : Z.of_nat (length (aa_q_thread A)) < 2 ^ 35 /\ Z.of_nat (length (aa_q_global A)) < 2 ^ 35).
  { destruct HBND as [B1 B2]. apply Forall_app in HBP as [HBPt HBPg]. apply Forall_app in HBM as [HBMt HBMg].
    pose proof (qsize_ge A _ _ HBPt HBMt). pose proof (qsize_ge A _ _ HBPg HBMg). unfold kQuarantineBatchSize, kQuarantineMax in *. lia. }
  unfold vTN, vGN, vGB. repeat apply Forall_cons; try apply Forall_nil; cbn [holds branch_taken eval]; rewrite ?E200, ?E204, ?E206.
  + unfold bv_eqb. rewrite !u64_lit by lia. intros E. apply Z.eqb_eq in E. lia.
  + split; [lia|]. rewrite u64_lit by lia. rewrite LBy. replace (ag_spacebeg (aa_geom A) + 24 * 2 ^ 32 + 16 * y) with ((2 ^ 13 * (ag_spacebeg (aa_geom A) / 2 ^ 16) + 3 * 2 ^ 32 + 2 * y) * 2 ^ 3) by (pose proof (Z.div_mod (ag_spacebeg (aa_geom A)) (2 ^ 16) ltac:(lia)); lia).
    apply Z.mod_mul. lia.
  + unfold bv_eqb. rewrite !u64_lit by lia. intros E. apply Z.eqb_eq in E. assert (aa_q_global A = []) by (destruct (aa_q_global A); [reflexivity | cbn in E; lia]). exact (HGL H0).
  + unfold HIGH_SHADOW_END in *. rewrite !u64_lit by lia. lia.
Qed.

Definition KEPT3 : list sobj := stack_win :: A_globals.
Definition REST3n : list sobj := ltac2:(tb__ "0|0|
S1S1cS4cS3cS3cS3cS3cA4S1S1cS4bS1S1cS4aS68S53S43A2S45S41S51A4S1S1cS49S1S1cS58S42A1S3S1cA1A3A3A3A3A3").
Definition PostQ3n_k : axst := ltac2:(tb__ "0|0|
S65S40S9dS63S40A1S8aA2A2").
Definition sdn : wsub := ltac2:(tb__ "0|0|
S9bS67S63S8cA1S63S6cA1A3").
Lemma ENT3n : ltac2:(tb__ "0|0|
S17S6S66S8cS6cS8eA3S7A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma SID3n : ltac2:(tb__ "0|0|
S17S6S9cS8eS67A2S7A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma OBJS3n : ltac2:(tb__ "0|0|
S17S4S1cA1S22S63S40A1A1S8S1cS8aS96A3A3"). Proof. reflexivity. Qed.

Definition A1T (A : AA) : AA := ltac2:(tb__ "0|0|
S62VA;S3S11A1S8S11S12VA;A1S14VA;A1A3A3").

Lemma rhoT_vals : ltac2:(tb__ "0|4|
S13SfSfS1dS6bR4R3R2R1A4S1dS19S17S3aQ40M0A1M1S1eR1Pc8A2S39G0S34S9S11S14R5A1M2A2A1A2A3S19S17G1S1eR1Pc9A2S39G0S7fG2A1A2A3S19S17G1S1eR1PcaA2S39G0S7eG2A1A2A3S19S17G1S1eR1PcbA2S39G0S70G2A1A2A3S19S17G1S1eR1PccA2S39G0S34S9S11S12R5A1M3A2A1A2A3S19S17G1S1eR1PcdA2S39G0R4A2A3S19S17G1S1eR1PceA2S39G0R3A2A3S19S17G1S1eR1PcfA2S39G0S70G3A1A2A3S19S17G1S1eR1Pd0A2S39G0Sa2A2A3S19S17G1S1eR1Pd1A2S39G0Z0A2A3S19S17G1SaS3aQ8A1A1F_;S25R1A1S25R2A1A3S30S67R2R1A3A2A2A2A2A2A2A2A2A2A2A2Tr;Frho;Fgb;Fgf;FA;").
Proof.
  intros A gf gb rho r.
  assert (EE : forall i v, In (i, v) [(200%positive, Z_to_bv 64 (Z.of_nat (length (aa_q_thread A)))); (201%positive, Z_to_bv 64 (hd_addr (aa_q_thread A)));
                (202%positive, Z_to_bv 64 (last_addr (aa_q_thread A))); (203%positive, Z_to_bv 64 (qsize (aa_q_thread A)));
                (204%positive, Z_to_bv 64 (Z.of_nat (length (aa_q_global A)))); (205%positive, Z_to_bv 64 gf);
                (206%positive, Z_to_bv 64 gb); (207%positive, Z_to_bv 64 (qsize (aa_q_global A)));
                (208%positive, Z_to_bv 64 kQuarantineMin); (209%positive, Z_to_bv 64 0)] -> rw r i = v).
  { intros i v Hin. unfold r, rhoT. apply rw_rho_sets_in; [exact NoDup10 | exact Hin]. }
  split; [apply EE; cbn [In]; do 0 right; left; reflexivity|]. split; [apply EE; cbn [In]; do 1 right; left; reflexivity|].
  split; [apply EE; cbn [In]; do 2 right; left; reflexivity|]. split; [apply EE; cbn [In]; do 3 right; left; reflexivity|].
  split; [apply EE; cbn [In]; do 4 right; left; reflexivity|]. split; [apply EE; cbn [In]; do 5 right; left; reflexivity|].
  split; [apply EE; cbn [In]; do 6 right; left; reflexivity|]. split; [apply EE; cbn [In]; do 7 right; left; reflexivity|].
  split; [apply EE; cbn [In]; do 8 right; left; reflexivity|]. split; [apply EE; cbn [In]; do 9 right; left; reflexivity|].
  split; [unfold r, rhoT; apply rm_rho_sets|].
  unfold r, rhoT. apply agree_below_rho_sets. intros j v Hin. cbn in Hin. unfold NPRE.
  repeat (destruct Hin as [E|Hin]; [injection E; intros; subst; cbv; discriminate|]). destruct Hin.
Qed.

Lemma av_cell : ltac2:(tb__ "0|4|
S74SfSfS2S1bSfS1dS2Sa7R1R5A2S17SaS3aQ8M0A1M1A1R9S33S33R8R7A2M2S34R2A1A2A1SdG1S89G1R2S31R6S1fR3R5A2A2S39G0Z0A2A4A2A3F_;Fj;S17S3aQ40M3A1S1fR2R4A2S39G3R3A2A3S73R9S75G2R6R4A3A2F_;F_;Frho;Fval;Fv;Fk;Foff;Fb;Fm;").
Proof. intros m b off k v val rho H E j Hj. cbn [c_addr c_w RtCells.c_val] in *. rewrite <- E. exact (H j Hj). Qed.

Lemma eval_add_z : ltac2:(tb__ "0|4|
S1dS1bS1bSfSfS17S3aQ40M0A1M1S1fR5R4A2S39G0R2A2M2A3S17G1S1fR6R4A2G2A3S35Z0R4A2M3G3S36S33R6R5A2S37Z2Z40A2A2S17G1S1fRaS68R9R8A2A2S39G0S33R7R6A2A2A3F_;F_;F_;F_;F_;Fy;Fx;Fb;Fa;Frho;").
Proof.
  intros rho a b x y Ea Eb Hx Hy Hs. apply bv_eq. unfold add. cbn [eval]. rewrite add_val, Ea, Eb, !u64_lit by lia. rewrite Z.mod_small by lia. reflexivity.
Qed.

Lemma cell4_of_1_3 : ltac2:(tb__ "0|1|
S74SfS73R2S75R1U1Z0M0A3A2S73R3S75S33R2Z1A2U3G0A3A2S73R4S75R3U4G0A3A2F_;F_;Fa;Fm;").
Proof.
  intros m a H1 H3 k Hk. unfold cell_ok in *. cbn [c_addr c_w RtCells.c_val] in *. destruct k as [|k].
  - rewrite H1 by lia. reflexivity.
  - replace (a + Z.of_nat (S k)) with (a + 1 + Z.of_nat k) by lia. rewrite H3 by lia.
    destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | lia].
Qed.
Lemma cell_ok_same : ltac2:(tb__ "0|1|
S74S74S76S73R3R1A2S73R3R2A2SfS19S35S77R4A1M0R1A2S36R1S33G0S34S78R4A1A1A2A2A2S17SaS3aQ8A1A1R6R2A1R7R2A1A3F_;Fz;F_;F_;Fc;Fm';Fm;").
Proof.
  intros m m' c H H' z Hz. unfold cell_ok in *. replace z with (c_addr c + Z.of_nat (Z.to_nat (z - c_addr c))) by lia.
  rewrite H, H' by lia. reflexivity.
Qed.

Lemma in_removelast_q : ltac2:(tb__ "0|0|
S4S11A1S11S81S11R1S84S11R2A2A3S81S11R2R3A3F_;Fx;Fl;").
Proof.
  induction l as [|a l IH]; intros x H; [destruct H|]. destruct l as [|b l']; [destruct H|]. cbn [removelast] in H.
  destruct H as [<-|H]; [left; reflexivity | right; exact (IH x H)].
Qed.
Lemma last_app_ne : ltac2:(tb__ "0|1|
S4S11A1M0G0S11S18S17G0R2S3S11A1A3A1S17S11S82S11S8S11R4R3A3R2A3S82S11R3R2A3A3F_;Fd;Fl2;Fl1;").
Proof.
  induction l1 as [|a l1 IH]; intros l2 d H; [reflexivity|]. cbn [app]. destruct (l1 ++ l2) eqn:E.
  - destruct l1; [cbn in E; congruence | discriminate E].
  - rewrite <- E. cbn [last]. rewrite E. rewrite <- E. exact (IH l2 d H).
Qed.
Lemma removelast_not_last : ltac2:(tb__ "0|1|
S4S11A1M0S18S17G0R1S3S11A1A3A1Sa9SfS87S11SfS16R2A4A2S18S81S11S82S11R3S71A3S84S11R3A2A3A1F_;F_;Fl;").
Proof.
  intros l Hne HND Hin. rewrite (app_removelast_last qb_dflt Hne) in HND at 1. rewrite map_app in HND. cbn [map] in HND.
  apply (NoDup_app_disj (map qb_addr (removelast l)) [qb_addr (last l qb_dflt)] (qb_addr (last l qb_dflt)) HND); [apply in_map; exact Hin | left; reflexivity].
Qed.

Lemma exit_n : ltac2:(tb__ "0|4|
S13S1dS1dS4S3aQ40A1A1S7aS18S17S4S11A1M0S14R5A1S3S11A1M1A3A1S18S17G0S12R6A1G1A3A1S17S6S15R7A1S7A3S5eR8A1S80S3dS6bR9S7fS12R9A1M2A1S7eG2A1R8A4R7A3S5bS32S5dS32VK;RaA3S40R8R7R6A6S6fS32S67RaR8S1S5S64S6eA2M3S0S64S6eS6cS5fS32VK;RbA3A4S3G3A1A3R7A6F_;F_;F_;F_;F_;F_;Fw;Ftp;Frho';Frho;FA;").
Proof.
  intros A rho rho' tp w HTL HGL HCI HBND [Hag Hkeep] H. destruct w as [tr [ms md]].
  pose proof (proj2 H) as [HK HQ]. cbn [w_tr w_cfg cfg_model fst snd] in HK, HQ.
  pose proof (proj1 (proj1 H)) as Hsm. unfold virt in Hsm. cbn [fst snd w_tr w_cfg cfg_ms cfg_model] in Hsm.
  set (tl := aa_q_thread A) in *. set (gl := aa_q_global A) in *. set (T := ag_thread (aa_geom A)).
  destruct (kq_facts segsA K HL A rho' tp _ _ HK) as [HG HRIG HRTC HMIN HST HLEN HCLS HQP HIDS HSEP HSEP3 HKTOP HKSECQ].
  pose proof (topG_range (aa_geom A)) as ACV. pose proof kSpaceSize_val as KSV.
  pose proof HG as HG0. apply geom_old in HG. rewrite FS_total_val, KSV in HG. unfold HIGH_SHADOW_END, IMG_HI, PG in HG.
  destruct HG as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & _). fold T in G5, G6, G7.
  pose proof (geom_bands _ HG0) as (_ & _ & _ & _ & TI & _). unfold IMG_LO, IMG_HI in TI. fold T in TI.
  destruct HRIG as (E151 & E152 & E155 & E156). fold T in E151.

  destruct (rhoT_vals A (hd_addr gl) (last_addr gl) rho) as (R200 & R201 & R202 & R203 & R204 & R205 & R206 & R207 & R208 & R209 & RRM & RAG).
  assert (KV : forall v, In v KEEP3 -> rw rho' v = rw (rhoT A (hd_addr gl) (last_addr gl) rho) v) by exact Hkeep.
  assert (E200 : rw rho' 200%positive = Z_to_bv 64 (Z.of_nat (length tl))) by (rewrite KV by (cbn; tauto); exact R200).
  assert (E201 : rw rho' 201%positive = Z_to_bv 64 (hd_addr tl)) by (rewrite KV by (cbn; tauto); exact R201).
  assert (E202 : rw rho' 202%positive = Z_to_bv 64 (last_addr tl)) by (rewrite KV by (cbn; tauto); exact R202).
  assert (E203 : rw rho' 203%positive = Z_to_bv 64 (qsize tl)) by (rewrite KV by (cbn; tauto); exact R203).
  assert (E204 : rw rho' 204%positive = Z_to_bv 64 (Z.of_nat (length gl))) by (rewrite KV by (cbn; tauto); exact R204).
  assert (E205 : rw rho' 205%positive = Z_to_bv 64 (hd_addr gl)) by (rewrite KV by (cbn; tauto); exact R205).
  assert (E206 : rw rho' 206%positive = Z_to_bv 64 (last_addr gl)) by (rewrite KV by (cbn; tauto); exact R206).
  assert (E207 : rw rho' 207%positive = Z_to_bv 64 (qsize gl)) by (rewrite KV by (cbn; tauto); exact R207).
  assert (E208 : rw rho' 208%positive = Z_to_bv 64 kQuarantineMin) by (rewrite KV by (cbn; tauto); exact R208).
  clear KV R200 R201 R202 R203 R204 R205 R206 R207 R208 R209.

  pose proof (SPA_facts_hold segsA _ rho' PostQ3n tp _ H) as HFa.
  assert (U13 : bv_unsigned (rw rho' 13%positive) = T + 80).
  { assert (X : holds rho' (SPBranch BC_EQ (SVar 13) (add vT (SLit 80)))) by (apply (proj1 (Forall_forall _ _) HFa); cbn; tauto).
    cbn [holds branch_taken] in X. unfold add, vT in X. cbn [eval] in X. unfold bv_eqb in X.
    apply Z.eqb_eq in X. rewrite add_val, E151, !u64_lit in X by lia. rewrite Z.mod_small in X by lia. exact X. }
  assert (FLE : holds rho' F_le) by (apply (proj1 (Forall_forall _ _) HFa); cbn; tauto).

  destruct HQ as (HBM & HLT & HLG & HHT & HHG & HMTX). destruct HQP as [HBP HND]. unfold qall in HBP, HND, HBM. fold tl gl in HBP, HND, HBM, HLT, HLG, HHT, HHG.
  pose proof (proj1 (Forall_forall _ _) HBP _ (in_or_app _ _ _ (or_intror (In_last gl qb_dflt HGL)))) as (LB1 & LB2 & (y & LBy & Ly0 & Lal & Ly1) & _).
  change (qb_addr (last gl qb_dflt)) with (last_addr gl) in LBy, LB1.
  assert (LEN2 : Z.of_nat (length tl) < 2 ^ 35 /\ Z.of_nat (length gl) < 2 ^ 35 /\ 0 <= qsize tl /\ 0 <= qsize gl).
  { destruct HBND as [B1 B2]. fold tl gl in B1, B2. apply Forall_app in HBP as [HBPt HBPg]. apply Forall_app in HBM as [HBMt HBMg].
    pose proof (qsize_ge A _ _ HBPt HBMt). pose proof (qsize_ge A _ _ HBPg HBMg). unfold kQuarantineBatchSize, kQuarantineMax in *. lia. }
  destruct LEN2 as (LT & LG & ST0 & SG0). destruct HBND as [BT BG]. fold tl gl in BT, BG. unfold kQuarantineMax in BG.
  assert (HAU : forall c, 1 <= c <= 30 -> 0 <= cs_allocated_user (cls_of A c) <= kUserSpaceSize).
  { intros c Hc. pose proof (cv_bounds _ _ _ _ _ (HCLS HCI c Hc)) as (B1 & B2 & B3 & _). unfold kUserMapSize in *. lia. }
  pose proof (conj HBP HND : q_pure A) as HQP.
  destruct (batch_slot A HQP HAU HG0 _ (in_or_app _ _ _ (or_intror (In_last gl qb_dflt HGL)))) as (yb & GB1 & GB2 & GB3 & GB4 & GB5 & GB6 & GB7).
  change (qb_addr (last gl qb_dflt)) with (last_addr gl) in GB1, GB5, GB6, GB7. set (gb := last_addr gl) in *. unfold HIGH_SHADOW_END in GB5.
  assert (GBhi : gb + 8192 <= 140737479966720) by (clear -GB6 G14 ACV; lia).

  set (rho3 := rho_absorb rho' REST3n (vms md tp ms)). set (v3 := view segsA (rm rho3)). set (v' := view segsA (rm rho')).
  assert (CI : forall lo hi cs, cells_inside lo hi cs <-> cells_inside lo hi cs) by (intros; tauto).
  destruct (absorb_view_cells segsA rho' _ tr (vms md tp ms) (vmd md) KEPT3 REST3n (SVar 13) 0 32 _ Hsm OBJS3n ltac:(cbn; tauto) ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(unfold cells_inside; repeat apply Forall_cons; try apply Forall_nil; cbn; lia) ltac:(cbn [eval]; rewrite U13; lia) ltac:(cbn [eval]; rewrite U13; lia)) as [AV1 PR1].
  destruct (absorb_view_cells segsA rho' _ tr (vms md tp ms) (vmd md) KEPT3 REST3n (SLit 0) (QG + 152) (QG + 156) _ Hsm OBJS3n ltac:(cbn; tauto) ltac:(unfold QG; lia) ltac:(lia) ltac:(unfold QG; lia)
                ltac:(unfold cells_inside, QG; repeat apply Forall_cons; try apply Forall_nil; cbn; lia) ltac:(cbn [eval]; rewrite u64_lit by lia; unfold QG; lia) ltac:(cbn [eval]; rewrite u64_lit by lia; unfold QG; lia)) as [AV2 PR2].
  destruct (absorb_view_cells segsA rho' _ tr (vms md tp ms) (vmd md) KEPT3 REST3n (SLit 0) (QG + 160) (QG + 192) _ Hsm OBJS3n ltac:(cbn; tauto) ltac:(unfold QG; lia) ltac:(lia) ltac:(unfold QG; lia)
                ltac:(unfold cells_inside, QG; repeat apply Forall_cons; try apply Forall_nil; cbn; lia) ltac:(cbn [eval]; rewrite u64_lit by lia; unfold QG; lia) ltac:(cbn [eval]; rewrite u64_lit by lia; unfold QG; lia)) as [AV3 PR3].
  destruct (absorb_view_cells segsA rho' _ tr (vms md tp ms) (vmd md) KEPT3 REST3n (SLit 0) (QG + 64) (QG + 80) _ Hsm OBJS3n ltac:(cbn; tauto) ltac:(unfold QG; lia) ltac:(lia) ltac:(unfold QG; lia)
                ltac:(unfold cells_inside, QG; repeat apply Forall_cons; try apply Forall_nil; cbn; lia) ltac:(cbn [eval]; rewrite u64_lit by lia; unfold QG; lia) ltac:(cbn [eval]; rewrite u64_lit by lia; unfold QG; lia)) as [AV4 PR4].
  destruct (absorb_view_cells segsA rho' _ tr (vms md tp ms) (vmd md) KEPT3 REST3n vGB 0 8 _ Hsm OBJS3n ltac:(cbn; tauto) ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(unfold cells_inside; repeat apply Forall_cons; try apply Forall_nil; cbn; lia) ltac:(unfold vGB; cbn [eval]; rewrite E206, u64_lit by (fold gb; lia); fold gb; lia)
                ltac:(unfold vGB; cbn [eval]; rewrite E206, u64_lit by (fold gb; lia); fold gb; lia)) as [AV5 PR5].
  clear CI. fold rho3 v3 in AV1, PR1, AV2, PR2, AV3, PR3, AV4, PR4, AV5, PR5.
  cbn [eval] in AV1, PR1, AV2, PR2, AV3, PR3, AV4, PR4. rewrite U13 in AV1, PR1. rewrite u64_lit in AV2, PR2, AV3, PR3, AV4, PR4 by lia.
  unfold vGB in AV5, PR5. cbn [eval] in AV5, PR5. rewrite E206, u64_lit in AV5, PR5 by (fold gb; lia). fold gb in AV5, PR5.
  assert (C_t0 : cell_ok v3 (mkACell (T + 80) 8 0)) by (replace (T + 80) with (T + 80 + 0) by lia; exact (av_cell v3 (T + 80) 0 8 ZQ 0 rho' (fun j => AV1 0 8%nat ZQ j (or_introl eq_refl)) eq_refl)).
  assert (C_t1 : cell_ok v3 (mkACell (T + 80 + 8) 8 0)) by exact (av_cell v3 (T + 80) 8 8 ZQ 0 rho' (fun j => AV1 8 8%nat ZQ j (or_intror (or_introl eq_refl))) eq_refl).
  assert (C_t2 : cell_ok v3 (mkACell (T + 80 + 16) 8 0)) by exact (av_cell v3 (T + 80) 16 8 ZQ 0 rho' (fun j => AV1 16 8%nat ZQ j (or_intror (or_intror (or_introl eq_refl)))) eq_refl).
  assert (C_t3 : cell_ok v3 (mkACell (T + 80 + 24) 8 0)) by exact (av_cell v3 (T + 80) 24 8 ZQ 0 rho' (fun j => AV1 24 8%nat ZQ j (or_intror (or_intror (or_intror (or_introl eq_refl))))) eq_refl).
  assert (C_mtx : cell_ok v3 (mkACell (QG + 152) 4 0)).
  { apply cell4_of_1_3.
    - replace (QG + 152) with (0 + (QG + 152)) by lia. exact (av_cell v3 0 (QG + 152) 1 (SLit 0) 0 rho' (fun j => AV2 (QG + 152) 1%nat (SLit 0) j (or_introl eq_refl)) eq_refl).
    - replace (QG + 152 + 1) with (0 + (QG + 153)) by lia. exact (av_cell v3 0 (QG + 153) 3 (SLit 0) 0 rho' (fun j => AV2 (QG + 153) 3%nat (SLit 0) j (or_intror (or_introl eq_refl))) eq_refl). }
  assert (EGN : eval rho' (add vGN vTN) = Z_to_bv 64 (Z.of_nat (length gl) + Z.of_nat (length tl))) by (apply eval_add_z; [exact E204 | exact E200 | lia | lia | lia]).
  assert (EGS : eval rho' gsz = Z_to_bv 64 (qsize gl + qsize tl)) by (apply eval_add_z; [exact E207 | exact E203 | lia | lia | lia]).
  assert (C_g0 : cell_ok v3 (mkACell (QG + 160) 8 (Z.of_nat (length gl) + Z.of_nat (length tl)))) by (replace (QG + 160) with (0 + (QG + 160)) by lia; exact (av_cell v3 0 (QG + 160) 8 _ _ rho' (fun j => AV3 _ _ _ j (or_introl eq_refl)) EGN)).
  assert (C_g1 : cell_ok v3 (mkACell (QG + 160 + 8) 8 (hd_addr gl))) by (replace (QG + 160 + 8) with (0 + (QG + 168)) by lia; exact (av_cell v3 0 (QG + 168) 8 _ _ rho' (fun j => AV3 _ _ _ j (or_intror (or_introl eq_refl))) E205)).
  assert (C_g2 : cell_ok v3 (mkACell (QG + 160 + 16) 8 (last_addr tl))) by (replace (QG + 160 + 16) with (0 + (QG + 176)) by lia; exact (av_cell v3 0 (QG + 176) 8 _ _ rho' (fun j => AV3 _ _ _ j (or_intror (or_intror (or_introl eq_refl)))) E202)).
  assert (C_g3 : cell_ok v3 (mkACell (QG + 160 + 24) 8 (qsize gl + qsize tl))) by (replace (QG + 160 + 24) with (0 + (QG + 184)) by lia; exact (av_cell v3 0 (QG + 184) 8 _ _ rho' (fun j => AV3 _ _ _ j (or_intror (or_intror (or_intror (or_introl eq_refl))))) EGS)).
  assert (C_max : cell_ok v3 (mkACell (QG + 64) 8 kQuarantineMax)) by (replace (QG + 64) with (0 + (QG + 64)) by lia; exact (av_cell v3 0 (QG + 64) 8 _ _ rho' (fun j => AV4 _ _ _ j (or_introl eq_refl)) eq_refl)).
  assert (C_min : cell_ok v3 (mkACell (QG + 72) 8 kQuarantineMin)) by (replace (QG + 72) with (0 + (QG + 72)) by lia; exact (av_cell v3 0 (QG + 72) 8 _ _ rho' (fun j => AV4 _ _ _ j (or_intror (or_introl eq_refl))) E208)).
  assert (C_lnk : cell_ok v3 (mkACell gb 8 (hd_addr tl))) by (replace gb with (gb + 0) at 1 by lia; exact (av_cell v3 gb 0 8 _ _ rho' (fun j => AV5 _ _ _ j (or_introl eq_refl)) E201)).
  clear AV1 AV2 AV3 AV4 AV5.

  assert (INR : forall a, in_ranges rho' REST3n a ->
            let z := bv_unsigned a in T + 80 <= z < T + 112 \/ QG + 152 <= z < QG + 156 \/ QG + 160 <= z < QG + 192 \/ QG + 64 <= z < QG + 80 \/ gb <= z < gb + 8).
  { intros a (o & Ho & Hz). cbn zeta. cbn [REST3n In] in Ho.
    destruct Ho as [<-|[<-|[<-|[<-|[<-|[]]]]]]; unfold O_tq, O_mtx0', O_gq, O_gmax, O_glb, carved, vGB in Hz; rewrite obj_range_mk in Hz by (unfold QG; lia);
      cbn [fst snd eval] in Hz; rewrite ?U13, ?E206, ?u64_lit in Hz by (fold gb; lia); fold gb in Hz; lia. }
  assert (FR : forall z, ~ (T + 80 <= z < T + 112 \/ QG + 152 <= z < QG + 156 \/ QG + 160 <= z < QG + 192 \/ QG + 64 <= z < QG + 80 \/ gb <= z < gb + 8) -> v3 z = v' z).
  { intros z Hz. unfold v3, v'. apply view_agree. intros Hr. unfold rho3, rho_absorb. cbn [rm].
    destruct (in_ranges_dec rho' REST3n (Z_to_bv 64 z)) as [Hin|]; [|reflexivity]. exfalso. apply Hz. pose proof (INR _ Hin) as X. cbn zeta in X. rewrite u64_lit in X by exact Hr. exact X. }
  assert (FRrm : forall a, ~ (let z := bv_unsigned a in T + 80 <= z < T + 112 \/ QG + 152 <= z < QG + 156 \/ QG + 160 <= z < QG + 192 \/ QG + 64 <= z < QG + 80 \/ gb <= z < gb + 8) -> rm rho3 a = rm rho' a).
  { intros a Hz. unfold rho3, rho_absorb. cbn [rm]. destruct (in_ranges_dec rho' REST3n a) as [Hin|]; [|reflexivity]. exfalso. exact (Hz (INR _ Hin)). }
  set (P := fun z : Z => T + 80 <= z < T + 112 \/ QG + 152 <= z < QG + 156 \/ QG + 160 <= z < QG + 192 \/ QG + 64 <= z < QG + 80 \/ gb <= z < gb + 8).
  change (forall z, ~ P z -> v3 z = v' z) in FR. change (forall a, ~ P (bv_unsigned a) -> rm rho3 a = rm rho' a) in FRrm.
  assert (PD : forall z, P z \/ ~ P z) by (intros z; unfold P; lia).

  assert (LASTIN : In (last gl qb_dflt) (qall A)) by (unfold qall; fold tl gl; apply in_or_app; right; apply In_last; exact HGL).
  assert (ADDR_INJ : forall b, In b (qall A) -> qb_addr b = gb -> b = last gl qb_dflt).
  { intros b Hb E. apply (NoDup_map_In_inj qb_addr (qall A)); [unfold qall; fold tl gl; exact HND | exact Hb | exact LASTIN | exact E]. }
  assert (IT_OUT : forall it, In it (qitems (qall A)) -> forall z, ifoot it z -> ~ P z).
  { intros it Hit z Hz HP.
    assert (QF : q_foot A z).
    { destruct (qitems_In A it Hit) as (b & Hb & Hib). unfold q_foot. apply Exists_exists. exists b. split; [exact Hb|]. right. apply Exists_exists. exists it. split; [exact Hib|].
      unfold ifoot, it_ab in Hz. exact Hz. }
    pose proof (HSEP z QF) as NT. fold T in NT.
    destruct (qitems_In A it Hit) as (b & Hb & Hib).
    pose proof (proj1 (Forall_forall _ _) (proj1 HQP) b Hb) as (_ & _ & _ & HIP). pose proof (proj1 (Forall_forall _ _) HIP it Hib) as (IP1 & IP2 & IP3 & IP4).
    pose proof (rz_facts (snd it)) as [RZ1 RZ2]. unfold IMG_HI in IP1.
    assert (SHlo : 0x7fff8000 <= Sh (fst it)) by (unfold Sh, SHADOW_OFF; pose proof (Z.div_pos (fst it) 8 ltac:(lia) ltac:(lia)); lia).
    unfold P in HP. unfold ifoot, it_ab in Hz. unfold QG in HP.
    destruct HP as [HP|[HP|[HP|[HP|HP]]]]; [lia | destruct Hz; lia | destruct Hz; lia | destruct Hz; lia |].

    destruct (is_primary (snd it)) eqn:EP.
    - pose proof (item_batch_apart A HQP HIDS HAU HG0 it _ Hit EP LASTIN) as AP. change (qb_addr (last gl qb_dflt)) with gb in AP.
      pose proof (item_zones A HQP HAU HG0 it Hit EP) as IZ. cbv zeta in IZ. destruct IZ as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & _). unfold it_ab, HIGH_SHADOW_END in *.
      destruct Hz as [Hz|Hz]; lia.
    - pose proof (HKSECQ it Hit EP) as [SQ SQ2]. rewrite KSV in SQ.
      assert (SHhi : Sh (fst it) + (snd it + 7) / 8 <= 0x10007fff8000).
      { unfold Sh, SHADOW_OFF. pose proof (Z.div_mod (fst it) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (fst it) 8 ltac:(lia)).
        pose proof (Z.div_mod (snd it + 7) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (snd it + 7) 8 ltac:(lia)). lia. }
      destruct Hz as [Hz|Hz]; lia. }
  assert (BX_OUT : forall b, In b (qall A) -> forall z, qb_addr b + (if Z.eq_dec (qb_addr b) gb then 8 else 0) <= z < qb_addr b + 8192 -> ~ P z).
  { intros b Hb z Hz HP.
    assert (QF : q_foot A z).
    { unfold q_foot. apply Exists_exists. exists b. split; [exact Hb|]. left. unfold kQuarantineBatchSize. destruct (Z.eq_dec (qb_addr b) gb); lia. }
    pose proof (HSEP z QF) as NT. fold T in NT.
    destruct (batch_slot A HQP HAU HG0 b Hb) as (yy & _ & _ & _ & _ & BB5 & _). unfold HIGH_SHADOW_END in BB5.
    unfold P, QG in HP. destruct HP as [HP|[HP|[HP|[HP|HP]]]]; [lia | destruct (Z.eq_dec (qb_addr b) gb); lia | destruct (Z.eq_dec (qb_addr b) gb); lia | destruct (Z.eq_dec (qb_addr b) gb); lia |].
    destruct (Z.eq_dec (qb_addr b) gb) as [E|NE]; [lia|].
    pose proof (batches_apart A HQP HAU HG0 b _ Hb LASTIN NE) as AP. change (qb_addr (last gl qb_dflt)) with gb in AP. lia. }
  assert (BF_OUT : forall b, In b (qall A) -> forall z, bfoot b z -> ~ P z).
  { intros b Hb z [Hz|Hz].
    - apply (BX_OUT b Hb). unfold kQuarantineBatchSize in Hz. destruct (Z.eq_dec (qb_addr b) gb); lia.
    - apply Exists_exists in Hz as (it & Hit & Hz). apply (IT_OUT it); [|exact Hz]. unfold qitems. apply in_flat_map. exists b. exact (conj Hb Hit). }
  assert (LK_OUT : forall b, In b (qall A) -> b <> last gl qb_dflt -> forall z, qb_addr b <= z < qb_addr b + 8 -> ~ P z).
  { intros b Hb NE z Hz. apply (BX_OUT b Hb). destruct (Z.eq_dec (qb_addr b) gb) as [E|_]; [exfalso; exact (NE (ADDR_INJ b Hb E)) | lia]. }

  assert (HMAX : cell_ok v' (mkACell (QG + 64) 8 kQuarantineMax)).
  { unfold rtc_inv, rtc_cells in HRTC. exact (cells_ok_nth _ _ 7 _ HRTC eq_refl). }
  assert (GMX : forall z, QG + 64 <= z < QG + 80 -> v3 z = v' z).
  { intros z Hz. destruct (Z_lt_dec z (QG + 72)).
    - apply (cell_ok_same v' v3 _ HMAX C_max). cbn [c_addr c_w]. lia.
    - apply (cell_ok_same v' v3 _ HMIN C_min). cbn [c_addr c_w]. unfold Inv.QG, QG in *. lia. }
  assert (PQW : forall z, P z -> ~ (QG + 64 <= z < QG + 80) -> QW A z).
  { intros z HP NG. unfold P in HP. destruct HP as [HP|[HP|[HP|[HP|HP]]]].
    - right. left. left. fold T. lia.
    - right. left. right. left. exact HP.
    - right. left. right. right. exact HP.
    - exfalso. exact (NG HP).
    - left. unfold qzone. apply Exists_exists. exists (last gl qb_dflt). split; [exact LASTIN|]. left. change (qb_addr (last gl qb_dflt)) with gb. unfold kQuarantineBatchSize. lia. }
  assert (PPR : forall z, P z -> exists b, v3 z = Some b).
  { intros z HP. unfold P in HP. destruct HP as [HP|[HP|[HP|[HP|HP]]]]; [apply PR1 | apply PR2 | apply PR3 | apply PR4 | apply PR5]; lia. }
  assert (HK3 : K A rho3 tp tr md).
  { apply (kq_view segsA K HL A rho' rho3 tp tr md); [intros i; reflexivity | intros l; reflexivity | | | exact HK].
    - intros z NQ. destruct (PD z) as [HP|NP]; [|exact (FR z NP)].
      destruct (Z_lt_dec z (QG + 64)) as [|]; [exfalso; apply NQ; apply PQW; [exact HP | lia]|].
      destruct (Z_lt_dec z (QG + 80)) as [|]; [apply GMX; lia | exfalso; apply NQ; apply PQW; [exact HP | lia]].
    - intros z _ Hd. destruct (PD z) as [HP|NP]; [destruct (PPR z HP) as [b Hb]; fold v3; rewrite Hb; discriminate | fold v3 v' in Hd |- *; rewrite (FR z NP); exact Hd]. }
  assert (HK1 : K (A1T A) rho3 tp tr md).
  { unfold A1T. apply (kq_perm segsA K HL A [] (gl ++ tl) rho3 tp tr md); [|exact HK3]. unfold qall. fold tl gl. cbn [app]. apply Permutation_app_comm. }

  assert (INT : forall b, In b tl -> In b (qall A)) by (intros b Hb; unfold qall; fold tl gl; apply in_or_app; left; exact Hb).
  assert (ING : forall b, In b gl -> In b (qall A)) by (intros b Hb; unfold qall; fold tl gl; apply in_or_app; right; exact Hb).
  assert (TL_NOT_LAST : forall b, In b tl -> b <> last gl qb_dflt).
  { intros b Hb E. subst b.
    pose proof (NoDup_app_disj (map qb_addr tl) (map qb_addr gl) gb) as X. rewrite map_app in HND.
    apply (X HND); [apply in_map_iff; exists (last gl qb_dflt); split; [reflexivity | exact Hb] | apply in_map_iff; exists (last gl qb_dflt); split; [reflexivity | apply In_last; exact HGL]]. }
  assert (HQ1 : q_mem v3 (A1T A)).
  { unfold q_mem, A1T, qall. cbn [aa_q_thread aa_q_global aa_geom set_q app]. fold tl gl T.
    split; [|split; [exact I|split; [|split; [|split; [|exact C_mtx]]]]].
    -
      apply Forall_forall. intros b Hb.
      assert (Hb' : In b (qall A)) by (apply in_app_or in Hb as [Hb|Hb]; [exact (ING b Hb) | exact (INT b Hb)]).
      apply (batch_mem_frame A v' v3 b (proj1 (Forall_forall _ _) (proj1 HQP) b Hb')); [intros z Hz; exact (FR z (BF_OUT b Hb' z Hz))|].
      exact (proj1 (Forall_forall _ _) HBM b ltac:(unfold qall in Hb'; fold tl gl in Hb'; exact Hb')).
    -
      apply qlinks_to_0. apply qlinks_to_app; [exact HTL | |].
      + apply (qlinks_to_relast v' v3 gl 0 (hd_addr tl) HGL); [| exact C_lnk | apply qlinks_to_0; exact HLG].
        intros b z Hb Hz. apply FR. apply (LK_OUT b (ING b (in_removelast_q _ _ Hb))); [|exact Hz].
        intros E. subst b. rewrite map_app in HND. exact (removelast_not_last gl HGL (NoDup_app_r _ _ HND) Hb).
      + apply (qlinks_to_frame v' v3 tl 0); [|apply qlinks_to_0; exact HLT].
        intros b z Hb Hz. apply FR. exact (LK_OUT b (INT b Hb) (TL_NOT_LAST b Hb) z Hz).
    -
      unfold qhdr_repr. cbn [length]. change (T + 0x50) with (T + 80).
      split; [exact C_t0|]. split; [intros X; exfalso; exact (X eq_refl)|]. split; [intros z Hz; apply PR1; lia|]. exact C_t3.
    -
      unfold qhdr_repr. rewrite length_app, Nat2Z.inj_add, qsize_app.
      split; [exact C_g0|]. split; [|split; [intros z Hz; apply PR3; unfold Inv.QG, QG in *; lia | exact C_g3]].
      intros _. split.
      + replace (hd qb_dflt (gl ++ tl)) with (hd qb_dflt gl) by (destruct gl; [congruence | reflexivity]). exact C_g1.
      + rewrite (last_app_ne gl tl qb_dflt HTL). exact C_g2. }
  assert (QSZ : qsize (gl ++ tl) <= kQuarantineMax).
  { rewrite qsize_app. unfold F_le in FLE. cbn [holds branch_taken] in FLE. rewrite EGS in FLE. cbn [eval] in FLE.
    apply negb_true_iff in FLE. unfold bv_ltu in FLE. apply Z.ltb_ge in FLE. rewrite !u64_lit in FLE by (unfold kQuarantineMax; lia). exact FLE. }

  set (TJ := (fun (_ : valuation) (_ : list word) (_ : list event) (_ : Model) => True) : jpredA).
  assert (HT : SPA segsA TJ PostQ3n rho' tp (tr, mkCfg ms md)) by (split; [exact (proj1 H) | exact I]).
  pose proof (SPA_unobj segsA TJ rho' PostQ3n KEPT3 REST3n tp tr ms md OBJS3n HT (fun x => x)) as HU. cbn zeta in HU. fold rho3 in HU.
  assert (STJ : stableA segsA NPRE TJ) by (unfold stableA, TJ; intros; exact I).
  pose proof (SPA_entails segsA TJ NPRE PostQ3n_k PostQ3 sdn rho3 tp _ ENT3n SID3n STJ HU) as HE.
  pose proof (rho_sub_agree sdn NPRE rho3 SID3n) as AG4.
  assert (ERM : forall a, rm rho' a = rm rho a) by (intros a; rewrite <- (proj2 (proj2 Hag) a), RRM; reflexivity).
  assert (EV' : forall z, v' z = view segsA (rm rho) z) by (intros z; unfold v'; apply view_agree; intros _; apply ERM).
  apply (LQPA_intro segsA NPRE rho tp [(PostQ3, JLQ3 segsA K A)] PostQ3 (JLQ3 segsA K A) (rho_sub rho3 sdn) tp _ TJ (or_introl eq_refl) HE).
  - apply (agree_vals_trans NPRE rho (rhoT A (hd_addr gl) (last_addr gl) rho)); [exact (agree_below_vals _ _ _ RAG)|].
    apply (agree_vals_trans NPRE _ rho'); [exact (agree_below_vals _ _ _ Hag)|].
    apply (agree_vals_trans NPRE _ rho3); [split; intros; reflexivity | exact (agree_below_vals _ _ _ AG4)].
  - intros _. cbn [w_tr w_cfg cfg_model fst snd]. exists (A1T A).
    assert (HJ4 : JQ3 segsA K (A1T A) (rho_sub rho3 sdn) tp tr md).
    { eapply (JQ3_stable segsA K (A1T A) NPRE HL ltac:(apply Pos.le_refl)); [exact AG4 | apply mat_equiv_refl | exact (conj HK1 HQ1)]. }
    split; [exact (proj1 HJ4)|]. split; [exact (proj2 HJ4)|].
    split.
    { unfold qpost, A1T. split; [unfold same_but_qcs, set_q; reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [intros c Hc; exact Hc|]. cbn [aa_q_global set_q]. fold tl gl. exact QSZ. }
    split.
    { intros a NQ. change (rm (rho_sub rho3 sdn) a) with (rm rho3 a). rewrite <- ERM. apply FRrm. intros HP. apply NQ.
      destruct (Z_lt_dec (bv_unsigned a) (QG + 64)) as [|]; [left; left; apply PQW; [exact HP | lia]|].
      destruct (Z_lt_dec (bv_unsigned a) (QG + 80)) as [|]; [right; left; left; unfold Inv.QG, QG in *; lia | left; left; apply PQW; [exact HP | lia]]. }
    split.
    { intros z NQ. change (view segsA (rm (rho_sub rho3 sdn)) z) with (v3 z). rewrite <- EV'. destruct (PD z) as [HP|NP]; [|exact (FR z NP)].
      destruct (Z_lt_dec z (QG + 64)) as [|]; [exfalso; apply NQ; left; apply PQW; [exact HP | lia]|].
      destruct (Z_lt_dec z (QG + 80)) as [|]; [apply GMX; lia | exfalso; apply NQ; left; apply PQW; [exact HP | lia]]. }
    split; [|split; [reflexivity|]].
    { intros l. change (rl (rho_sub rho3 sdn) l) with (rl rho' l). rewrite <- (proj1 (proj2 Hag) l). symmetry. exact (proj1 (proj2 RAG) l). }

    intros a HB Hdef. change (rm (rho_sub rho3 sdn) a) with (rm rho3 a). rewrite FRrm; [rewrite ERM; exact Hdef|].
    intros HP. unfold P in HP. pose proof (geom_bands _ HG0) as (_ & TBD & _). fold T in TBD.
    unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END, Inv.QG, QG in *. clear -HP HB TBD GB5. lia.
Qed.

Lemma entry_e : ltac2:(tb__ "0|2|
S13S1dS4S3aQ40A1A1S7aS18S17S4S11A1M0S14R4A1S3S11A1M1A3A1S17G0S12R5A1G1A3S5eR6A1S5bS32S5dS32VK;R7A3S6dR6R5R4A6S1aSfSfS1aSfSfS5bS32S5dS32VK;RaA3S4dS6bRaR2R1R9A4R8R7A6Lgb;A2Lgf;A2F_;F_;F_;F_;Fw;Ftp;Frho;FA;").
Proof.
  intros A rho tp w HTL HGL HBND H.
  pose proof (proj2 H) as [HK HQ]. cbn [w_tr w_cfg cfg_model fst snd] in HK, HQ.
  destruct (kq_facts segsA K HL A rho tp _ _ HK) as [HG HRIG HRTC HMIN HST HLEN HCLS HQP HIDS HSEP HSEP3 HKTOP HKSECQ].
  pose proof (topG_range (aa_geom A)) as ACV. pose proof kSpaceSize_val as KSV.
  pose proof HG as HG0. apply geom_old in HG. rewrite FS_total_val, KSV in HG. unfold HIGH_SHADOW_END, IMG_HI, PG in HG.
  destruct HG as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & _).
  pose proof (geom_bands _ HG0) as (_ & _ & _ & _ & TI & _). unfold IMG_LO, IMG_HI in TI.
  destruct HRIG as (E151 & E152 & E155 & E156).
  destruct HQ as (HBM & HLT & HLG & HHT & HHG & HMTX). destruct HQP as [HBP HND]. unfold qall in HBP, HND.
  destruct HHT as (HT0 & HT12 & HTP & HT3). destruct (HT12 HTL) as [HT1 HT2]. clear HT12.
  destruct HHG as (HG0' & _ & HGP & HG3). rewrite HGL in HG0', HG3. cbn [length] in HG0'. change (qsize []) with 0 in HG3.
  change (qb_addr (last (aa_q_thread A) qb_dflt)) with (last_addr (aa_q_thread A)) in HT2. change (qb_addr (hd qb_dflt (aa_q_thread A))) with (hd_addr (aa_q_thread A)) in HT1.
  unfold QG, Inv.QG in *.
  assert (PGa : present (view segsA (rm rho)) (961840 + 160 + 8) (961840 + 160 + 8 + 8)) by (intros z Hz; apply HGP; lia).
  assert (PGb : present (view segsA (rm rho)) (961840 + 160 + 16) (961840 + 160 + 16 + 8)) by (intros z Hz; apply HGP; lia).
  destruct (present_cell8q _ _ PGa) as (gf & Rgf & HGa).
  destruct (present_cell8q _ _ PGb) as (gb & Rgb & HGb).
  exists gf, gb.
  pose proof (SPA_facts_hold segsA _ rho PreQ3 tp w H) as HF0. cbn [ax_S PreQ3 ss_facts] in HF0.
  assert (U13 : bv_unsigned (rw rho 13%positive) = ag_thread (aa_geom A) + 80).
  { unfold F_T0 in HF0. apply Forall_app in HF0 as [_ HF1].
    pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail HF1))) as X. cbn [holds branch_taken] in X. unfold add, vT in X. cbn [eval] in X. unfold bv_eqb in X.
    apply Z.eqb_eq in X. rewrite add_val, E151, !u64_lit in X by lia. rewrite Z.mod_small in X by lia. exact X. }
  set (rho1 := rhoT A gf gb rho).
  destruct (rhoT_vals A gf gb rho) as (E200 & E201 & E202 & E203 & E204 & E205 & E206 & E207 & E208 & E209 & Erm & Hag1). fold rho1 in E200, E201, E202, E203, E204, E205, E206, E207, E208, E209, Erm, Hag1.
  rewrite HGL in E204, E207. cbn [length] in E204. change (qsize []) with 0 in E207.
  assert (H1 : SPA segsA (JQ3 segsA K A) PreQ3 rho1 tp w).
  { eapply SPA_agree; [exact Hag1 | | exact H]. intros HJ. eapply (JQ3_stable segsA K A NPRE HL ltac:(apply Pos.le_refl)); [exact Hag1 | apply mat_equiv_refl | exact HJ]. }
  assert (E13 : rw rho1 13%positive = rw rho 13%positive) by (symmetry; apply (proj1 Hag1); cbv; reflexivity).
  assert (E151' : rw rho1 151%positive = Z_to_bv 64 (ag_thread (aa_geom A))) by (rewrite <- E151; symmetry; apply (proj1 Hag1); cbv; reflexivity).
  assert (HMAX : cell_ok (view segsA (rm rho)) (mkACell (QG + 64) 8 kQuarantineMax)).
  { unfold rtc_inv, rtc_cells in HRTC. exact (cells_ok_nth _ _ 7 _ HRTC eq_refl). }
  pose proof (proj1 (proj1 H1)) as Hsm1. unfold virt in Hsm1. cbn [fst snd w_tr w_cfg cfg_ms cfg_model ax_S] in Hsm1.
  pose proof (SPA_facts_hold segsA _ rho1 PreQ3 tp w H1) as HFa1.
  assert (Hhigh : holds rho1 F_sp_high) by (apply (proj1 (Forall_forall _ _) HFa1); cbn [In ss_facts ax_S PreQ3 mkA F_T0 pre_facts app]; tauto).
  destruct (stack_win_range _ rho1 _ _ Hsm1 ltac:(cbn; tauto) Hhigh) as (SW1 & SW2 & SW3).
  assert (TOPlo : topG (aa_geom A) <= fst (obj_range rho1 stack_win)).
  { pose proof HKTOP as HT. unfold top_high in HT. change (fst (obj_range rho1 stack_win)) with (bv_unsigned (rw rho1 10%positive) + bv_signed (rw rho1 V_DEPTH)).
    rewrite <- (proj1 Hag1 10%positive), <- (proj1 Hag1 V_DEPTH) by (cbv; reflexivity). exact HT. }
  unfold QG, Inv.QG in *.
  assert (TLlen : 0 < Z.of_nat (length (aa_q_thread A))) by (destruct (aa_q_thread A); [congruence | cbn; lia]).

  assert (H2 : SPA segsA (JQ3 segsA K A) (ax_setS PreQ3 S1e) rho1 tp w).
  { unfold S1e. eapply SPA_carve_list; [exact H1 | exact S1e_swf | cbv; discriminate | | |].
    - unfold N3e. unfold vTN, vTF, vTB, vTS, vGN, vGF, vGB, vGS, vMIN, vGBN.
      repeat apply Forall_cons; try apply Forall_nil; unfold QG, Inv.QG; cbn [eval]; rewrite ?E13, ?E206, ?U13; rewrite ?u64_lit by lia.
      all: split; [lia|]. all: split; [lia|]. all: split; [lia|]. all: split; [lia|]. all: split; [lia|].
      all: split; [unfold cells_inside; repeat apply Forall_cons; try apply Forall_nil; cbn; lia|].
      all: split; [|split; [|apply xwords_clear_nil]].
      all: rewrite ?Erm.
      + intros off Hoff.
        destruct (Z_lt_dec off 8); [|destruct (Z_lt_dec off 16); [|destruct (Z_lt_dec off 24)]].
        * eapply (cell_wok_rd2 _ _ _ _ _ HT0); cbn [Z.of_nat]; lia.
        * eapply (cell_wok_rd2 _ _ _ _ _ HT1); cbn [Z.of_nat]; lia.
        * eapply (cell_wok_rd2 _ _ _ _ _ HT2); cbn [Z.of_nat]; lia.
        * eapply (cell_wok_rd2 _ _ _ _ _ HT3); cbn [Z.of_nat]; lia.
      + unfold cells_in_view. repeat apply Forall_cons; try apply Forall_nil.
        * eapply (civ_cell rho1 (rm rho) (ag_thread (aa_geom A) + 80) 0); [rewrite Z.add_0_r; exact HT0 | cbn [eval]; exact E200 | lia | lia].
        * eapply (civ_cell rho1 (rm rho) (ag_thread (aa_geom A) + 80) 8); [exact HT1 | cbn [eval]; exact E201 | lia | lia].
        * eapply (civ_cell rho1 (rm rho) (ag_thread (aa_geom A) + 80) 16); [exact HT2 | cbn [eval]; exact E202 | lia | lia].
        * eapply (civ_cell rho1 (rm rho) (ag_thread (aa_geom A) + 80) 24); [exact HT3 | cbn [eval]; exact E203 | lia | lia].
      + intros off Hoff; split; [apply wok_of_imageA; lia | apply rd_of_imageA; lia].
      + unfold cells_in_view. repeat apply Forall_cons; try apply Forall_nil.
        eapply (civ_cell rho1 (rm rho) 0 (961840 + 152)); [exact HMTX | reflexivity | lia | lia].
      + intros off Hoff; split; [apply wok_of_imageA; lia | apply rd_of_imageA; lia].
      + unfold cells_in_view. repeat apply Forall_cons; try apply Forall_nil.
        * eapply (civ_cell rho1 (rm rho) 0 (961840 + 160)); [exact HG0' | reflexivity | lia | lia].
        * eapply (civ_cell rho1 (rm rho) 0 (961840 + 168)); [exact HGa | cbn [eval]; exact E205 | lia | lia].
        * eapply (civ_cell rho1 (rm rho) 0 (961840 + 176)); [exact HGb | cbn [eval]; exact E206 | lia | lia].
        * eapply (civ_cell rho1 (rm rho) 0 (961840 + 184)); [exact HG3 | cbn [eval]; exact E207 | lia | lia].
      + intros off Hoff; split; [apply wok_of_imageA; lia | apply rd_of_imageA; lia].
      + unfold cells_in_view. repeat apply Forall_cons; try apply Forall_nil.
        * eapply (civ_cell rho1 (rm rho) 0 (961840 + 64)); [exact HMAX | reflexivity | lia | lia].
        * eapply (civ_cell rho1 (rm rho) 0 (961840 + 72)); [exact HMIN | cbn [eval]; exact E208 | lia | lia].
    -
      unfold N3e. cbn [map carve_obj ss_objs ax_S PreQ3 mkA app]. unfold carved, vTN, vTF, vTB, vTS, vGN, vGF, vGB, vGS, vMIN, vGBN.
      unfold A_globals, O_got, O_rtc, GOT_LO, GOT_HI, RTC_LO, RTC_HI, QG.
      destruct (obj_range rho1 stack_win) as [slo shi] eqn:ESW. cbn [fst snd] in SW1, SW2, SW3, TOPlo.
      apply Forall_cons; [(apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]; unfold ranges_disjoint; rewrite ?ESW;
                      rewrite ?obj_range_mk by lia; cbn [fst snd eval]; rewrite ?E13, ?E206, ?U13; rewrite ?u64_lit by lia; lia)|]. apply Forall_cons; [(apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]; unfold ranges_disjoint; rewrite ?ESW;
                      rewrite ?obj_range_mk by lia; cbn [fst snd eval]; rewrite ?E13, ?E206, ?U13; rewrite ?u64_lit by lia; lia)|]. apply Forall_cons; [(apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]; unfold ranges_disjoint; rewrite ?ESW;
                      rewrite ?obj_range_mk by lia; cbn [fst snd eval]; rewrite ?E13, ?E206, ?U13; rewrite ?u64_lit by lia; lia)|]. apply Forall_cons; [(apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]; unfold ranges_disjoint; rewrite ?ESW;
                      rewrite ?obj_range_mk by lia; cbn [fst snd eval]; rewrite ?E13, ?E206, ?U13; rewrite ?u64_lit by lia; lia)|]. apply Forall_nil.
    -
      unfold N3e. cbn [map carve_obj pairwise_disjoint]. unfold carved, vTN, vTF, vTB, vTS, vGN, vGF, vGB, vGS, vMIN, vGBN, QG.
      repeat split; repeat apply Forall_cons; try apply Forall_nil; try exact I; unfold ranges_disjoint;
        rewrite ?obj_range_mk by lia; cbn [fst snd eval]; rewrite ?E13, ?E206, ?U13; rewrite ?u64_lit by lia; lia. }
  clear H1.

  rewrite <- S1e_pre. eapply SPA_refacts; [exact H2 | exact F_T_below |].
  cbn [ax_S ax_setS ss_facts PreQ3 mkA]. intros HF. unfold F_T. apply Forall_app. split; [exact HF|].
  assert (LEN2 : Z.of_nat (length (aa_q_thread A)) < 2 ^ 35).
  { destruct HBND as [B1 B2]. apply Forall_app in HBP as [HBPt HBPg]. apply Forall_app in HBM as [HBMt HBMg].
    pose proof (qsize_ge A _ _ HBPt HBMt). unfold kQuarantineBatchSize in *. lia. }
  unfold vTN. repeat apply Forall_cons; try apply Forall_nil; cbn [holds branch_taken eval]; rewrite ?E200.
  unfold bv_eqb. rewrite !u64_lit by lia. intros E. apply Z.eqb_eq in E. lia.
Qed.

Definition REST3e : list sobj := ltac2:(tb__ "0|0|
S1S1cS4cS3cS3cS3cS3cA4S1S1cS4bS1S1cS4aS43S42S41S51A4S1S1cS49S3S1cA1A3A3A3A3").
Definition PostQ3e_k : axst := ltac2:(tb__ "0|0|
S65S3fS9dS63S3fA1S8aA2A2").
Definition sde : wsub := ltac2:(tb__ "0|0|
S9bS67S63S8bA1S63S6cA1A3").
Lemma ENT3e : ltac2:(tb__ "0|0|
S17S6S66S8bS6cS8dA3S7A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma SID3e : ltac2:(tb__ "0|0|
S17S6S9cS8dS67A2S7A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma OBJS3e : ltac2:(tb__ "0|0|
S17S4S1cA1S22S63S3fA1A1S8S1cS8aS95A3A3"). Proof. reflexivity. Qed.

Lemma exit_e : ltac2:(tb__ "0|3|
S13SfSfS1dS1dS4S3aQ40A1A1S7aS18S17S4S11A1M0S14R7A1S3S11A1M1A3A1S17G0S12R8A1G1A3S5eR9A1S80S3dS6bRaR9R8R7A4R6A3S5bS32S5dS32VK;RbA3S3fR7R6R5A6S6fS32S67R9R7S1S5S64S6eA2M2S0S64S6eS6cS5fS32VK;RcA3A4S3G2A1A3R6A6F_;F_;F_;F_;F_;Fw;Ftp;Frho';Frho;Fgb;Fgf;FA;").
Proof.
  intros A gf gb rho rho' tp w HTL HGL HBND [Hag Hkeep] H. destruct w as [tr [ms md]].
  pose proof (proj2 H) as [HK HQ]. cbn [w_tr w_cfg cfg_model fst snd] in HK, HQ.
  pose proof (proj1 (proj1 H)) as Hsm. unfold virt in Hsm. cbn [fst snd w_tr w_cfg cfg_ms cfg_model] in Hsm.
  set (tl := aa_q_thread A) in *. set (T := ag_thread (aa_geom A)).
  destruct (kq_facts segsA K HL A rho' tp _ _ HK) as [HG HRIG HRTC HMIN HST HLEN HCLS HQP HIDS HSEP HSEP3 HKTOP HKSECQ].
  pose proof (topG_range (aa_geom A)) as ACV. pose proof kSpaceSize_val as KSV.
  pose proof HG as HG0. apply geom_old in HG. rewrite FS_total_val, KSV in HG. unfold HIGH_SHADOW_END, IMG_HI, PG in HG.
  destruct HG as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & _). fold T in G5, G6, G7.
  pose proof (geom_bands _ HG0) as (_ & _ & _ & _ & TI & _). unfold IMG_LO, IMG_HI in TI. fold T in TI.
  destruct HRIG as (E151 & E152 & E155 & E156). fold T in E151.
  destruct (rhoT_vals A gf gb rho) as (R200 & R201 & R202 & R203 & R204 & R205 & R206 & R207 & R208 & R209 & RRM & RAG).
  assert (KV : forall v, In v KEEP3 -> rw rho' v = rw (rhoT A gf gb rho) v) by exact Hkeep.
  assert (E200 : rw rho' 200%positive = Z_to_bv 64 (Z.of_nat (length tl))) by (rewrite KV by (cbn; tauto); exact R200).
  assert (E201 : rw rho' 201%positive = Z_to_bv 64 (hd_addr tl)) by (rewrite KV by (cbn; tauto); exact R201).
  assert (E202 : rw rho' 202%positive = Z_to_bv 64 (last_addr tl)) by (rewrite KV by (cbn; tauto); exact R202).
  assert (E203 : rw rho' 203%positive = Z_to_bv 64 (qsize tl)) by (rewrite KV by (cbn; tauto); exact R203).
  assert (E207 : rw rho' 207%positive = Z_to_bv 64 0) by (rewrite KV by (cbn; tauto); rewrite R207, HGL; reflexivity).
  assert (E208 : rw rho' 208%positive = Z_to_bv 64 kQuarantineMin) by (rewrite KV by (cbn; tauto); exact R208).
  clear KV R200 R201 R202 R203 R204 R205 R206 R207 R208 R209.
  pose proof (SPA_facts_hold segsA _ rho' PostQ3e tp _ H) as HFa.
  assert (U13 : bv_unsigned (rw rho' 13%positive) = T + 80).
  { assert (X : holds rho' (SPBranch BC_EQ (SVar 13) (add vT (SLit 80)))) by (apply (proj1 (Forall_forall _ _) HFa); cbn; tauto).
    cbn [holds branch_taken] in X. unfold add, vT in X. cbn [eval] in X. unfold bv_eqb in X.
    apply Z.eqb_eq in X. rewrite add_val, E151, !u64_lit in X by lia. rewrite Z.mod_small in X by lia. exact X. }
  assert (FLE : holds rho' F_le) by (apply (proj1 (Forall_forall _ _) HFa); cbn; tauto).
  destruct HQ as (HBM & HLT & HLG & HHT & HHG & HMTX). destruct HQP as [HBP HND]. unfold qall in HBP, HND, HBM. rewrite HGL in HBP, HND, HBM. rewrite app_nil_r in HBP, HND, HBM. fold tl in HBP, HND, HBM, HLT, HHT.
  assert (LEN2 : Z.of_nat (length tl) < 2 ^ 35 /\ 0 <= qsize tl).
  { destruct HBND as [B1 B2]. fold tl in B1. pose proof (qsize_ge A _ _ HBP HBM). unfold kQuarantineBatchSize in *. lia. }
  destruct LEN2 as (LT & ST0). destruct HBND as [BT _]. fold tl in BT.
  assert (QALL : qall A = tl) by (unfold qall; rewrite HGL, app_nil_r; reflexivity).
  pose proof (conj HBP HND : Forall (batch_pure A) tl /\ NoDup (map qb_addr tl)) as HQP'.

  set (rho3 := rho_absorb rho' REST3e (vms md tp ms)). set (v3 := view segsA (rm rho3)). set (v' := view segsA (rm rho')).
  destruct (absorb_view_cells segsA rho' _ tr (vms md tp ms) (vmd md) KEPT3 REST3e (SVar 13) 0 32 _ Hsm OBJS3e ltac:(cbn; tauto) ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(unfold cells_inside; repeat apply Forall_cons; try apply Forall_nil; cbn; lia) ltac:(cbn [eval]; rewrite U13; lia) ltac:(cbn [eval]; rewrite U13; lia)) as [AV1 PR1].
  destruct (absorb_view_cells segsA rho' _ tr (vms md tp ms) (vmd md) KEPT3 REST3e (SLit 0) (QG + 152) (QG + 156) _ Hsm OBJS3e ltac:(cbn; tauto) ltac:(unfold QG; lia) ltac:(lia) ltac:(unfold QG; lia)
                ltac:(unfold cells_inside, QG; repeat apply Forall_cons; try apply Forall_nil; cbn; lia) ltac:(cbn [eval]; rewrite u64_lit by lia; unfold QG; lia) ltac:(cbn [eval]; rewrite u64_lit by lia; unfold QG; lia)) as [AV2 PR2].
  destruct (absorb_view_cells segsA rho' _ tr (vms md tp ms) (vmd md) KEPT3 REST3e (SLit 0) (QG + 160) (QG + 192) _ Hsm OBJS3e ltac:(cbn; tauto) ltac:(unfold QG; lia) ltac:(lia) ltac:(unfold QG; lia)
                ltac:(unfold cells_inside, QG; repeat apply Forall_cons; try apply Forall_nil; cbn; lia) ltac:(cbn [eval]; rewrite u64_lit by lia; unfold QG; lia) ltac:(cbn [eval]; rewrite u64_lit by lia; unfold QG; lia)) as [AV3 PR3].
  destruct (absorb_view_cells segsA rho' _ tr (vms md tp ms) (vmd md) KEPT3 REST3e (SLit 0) (QG + 64) (QG + 80) _ Hsm OBJS3e ltac:(cbn; tauto) ltac:(unfold QG; lia) ltac:(lia) ltac:(unfold QG; lia)
                ltac:(unfold cells_inside, QG; repeat apply Forall_cons; try apply Forall_nil; cbn; lia) ltac:(cbn [eval]; rewrite u64_lit by lia; unfold QG; lia) ltac:(cbn [eval]; rewrite u64_lit by lia; unfold QG; lia)) as [AV4 PR4].
  fold rho3 v3 in AV1, PR1, AV2, PR2, AV3, PR3, AV4, PR4.
  cbn [eval] in AV1, PR1, AV2, PR2, AV3, PR3, AV4, PR4. rewrite U13 in AV1, PR1. rewrite u64_lit in AV2, PR2, AV3, PR3, AV4, PR4 by lia.
  assert (C_t0 : cell_ok v3 (mkACell (T + 80) 8 0)) by (replace (T + 80) with (T + 80 + 0) by lia; exact (av_cell v3 (T + 80) 0 8 ZQ 0 rho' (fun j => AV1 0 8%nat ZQ j (or_introl eq_refl)) eq_refl)).
  assert (C_t3 : cell_ok v3 (mkACell (T + 80 + 24) 8 0)) by exact (av_cell v3 (T + 80) 24 8 ZQ 0 rho' (fun j => AV1 24 8%nat ZQ j (or_intror (or_intror (or_intror (or_introl eq_refl))))) eq_refl).
  assert (C_mtx : cell_ok v3 (mkACell (QG + 152) 4 0)).
  { apply cell4_of_1_3.
    - replace (QG + 152) with (0 + (QG + 152)) by lia. exact (av_cell v3 0 (QG + 152) 1 (SLit 0) 0 rho' (fun j => AV2 (QG + 152) 1%nat (SLit 0) j (or_introl eq_refl)) eq_refl).
    - replace (QG + 152 + 1) with (0 + (QG + 153)) by lia. exact (av_cell v3 0 (QG + 153) 3 (SLit 0) 0 rho' (fun j => AV2 (QG + 153) 3%nat (SLit 0) j (or_intror (or_introl eq_refl))) eq_refl). }
  assert (EGS : eval rho' gsz = Z_to_bv 64 (qsize tl)) by (replace (qsize tl) with (0 + qsize tl) by lia; apply eval_add_z; [exact E207 | exact E203 | lia | lia | lia]).
  assert (C_g0 : cell_ok v3 (mkACell (QG + 160) 8 (Z.of_nat (length tl)))) by (replace (QG + 160) with (0 + (QG + 160)) by lia; exact (av_cell v3 0 (QG + 160) 8 _ _ rho' (fun j => AV3 _ _ _ j (or_introl eq_refl)) E200)).
  assert (C_g1 : cell_ok v3 (mkACell (QG + 160 + 8) 8 (hd_addr tl))) by (replace (QG + 160 + 8) with (0 + (QG + 168)) by lia; exact (av_cell v3 0 (QG + 168) 8 _ _ rho' (fun j => AV3 _ _ _ j (or_intror (or_introl eq_refl))) E201)).
  assert (C_g2 : cell_ok v3 (mkACell (QG + 160 + 16) 8 (last_addr tl))) by (replace (QG + 160 + 16) with (0 + (QG + 176)) by lia; exact (av_cell v3 0 (QG + 176) 8 _ _ rho' (fun j => AV3 _ _ _ j (or_intror (or_intror (or_introl eq_refl)))) E202)).
  assert (C_g3 : cell_ok v3 (mkACell (QG + 160 + 24) 8 (qsize tl))) by (replace (QG + 160 + 24) with (0 + (QG + 184)) by lia; exact (av_cell v3 0 (QG + 184) 8 _ _ rho' (fun j => AV3 _ _ _ j (or_intror (or_intror (or_intror (or_introl eq_refl))))) EGS)).
  assert (C_max : cell_ok v3 (mkACell (QG + 64) 8 kQuarantineMax)) by (replace (QG + 64) with (0 + (QG + 64)) by lia; exact (av_cell v3 0 (QG + 64) 8 _ _ rho' (fun j => AV4 _ _ _ j (or_introl eq_refl)) eq_refl)).
  assert (C_min : cell_ok v3 (mkACell (QG + 72) 8 kQuarantineMin)) by (replace (QG + 72) with (0 + (QG + 72)) by lia; exact (av_cell v3 0 (QG + 72) 8 _ _ rho' (fun j => AV4 _ _ _ j (or_intror (or_introl eq_refl))) E208)).
  clear AV1 AV2 AV3 AV4.
  set (P := fun z : Z => T + 80 <= z < T + 112 \/ QG + 152 <= z < QG + 156 \/ QG + 160 <= z < QG + 192 \/ QG + 64 <= z < QG + 80).
  assert (INR : forall a, in_ranges rho' REST3e a -> P (bv_unsigned a)).
  { intros a (o & Ho & Hz). unfold P. cbn [REST3e In] in Ho.
    destruct Ho as [<-|[<-|[<-|[<-|[]]]]]; unfold O_tq, O_mtx0', O_gq, O_gmax, carved in Hz; rewrite obj_range_mk in Hz by (unfold QG; lia);
      cbn [fst snd eval] in Hz; rewrite ?U13, ?u64_lit in Hz by lia; lia. }
  assert (FR : forall z, ~ P z -> v3 z = v' z).
  { intros z Hz. unfold v3, v'. apply view_agree. intros Hr. unfold rho3, rho_absorb. cbn [rm].
    destruct (in_ranges_dec rho' REST3e (Z_to_bv 64 z)) as [Hin|]; [|reflexivity]. exfalso. apply Hz. pose proof (INR _ Hin) as X. rewrite u64_lit in X by exact Hr. exact X. }
  assert (FRrm : forall a, ~ P (bv_unsigned a) -> rm rho3 a = rm rho' a).
  { intros a Hz. unfold rho3, rho_absorb. cbn [rm]. destruct (in_ranges_dec rho' REST3e a) as [Hin|]; [|reflexivity]. exfalso. exact (Hz (INR _ Hin)). }
  assert (PD : forall z, P z \/ ~ P z) by (intros z; unfold P; lia).
  assert (QF_OUT : forall z, q_foot A z -> IMG_HI <= z -> ~ P z).
  { intros z QF Hhi HP. pose proof (HSEP z QF) as NT. fold T in NT. unfold P, QG, IMG_HI in *. lia. }
  assert (BF_OUT : forall b, In b tl -> forall z, bfoot b z \/ qb_addr b <= z < qb_addr b + 8 -> ~ P z).
  { intros b Hb z Hz.
    pose proof (proj1 (Forall_forall _ _) HBP b Hb) as (BP1 & _ & _ & HIP). unfold HIGH_SHADOW_END in BP1.
    assert (Hbq : In b (aa_q_thread A ++ aa_q_global A)) by (apply in_or_app; left; exact Hb).
    destruct Hz as [[Hz|Hz]|Hz].
    - apply QF_OUT; [| unfold IMG_HI; lia]. unfold q_foot. apply Exists_exists. exists b. split; [exact Hbq|]. left. unfold kQuarantineBatchSize in *. lia.
    - apply Exists_exists in Hz as (it & Hit & Hz). pose proof (proj1 (Forall_forall _ _) HIP it Hit) as (IP1 & _). pose proof (rz_facts (snd it)) as [RZ1 _].
      assert (SHlo : 0x7fff8000 <= Sh (fst it)) by (unfold Sh, SHADOW_OFF; unfold IMG_HI in IP1; pose proof (Z.div_pos (fst it) 8 ltac:(lia) ltac:(lia)); lia).
      apply QF_OUT; [| unfold ifoot, it_ab, IMG_HI in *; destruct Hz; lia].
      unfold q_foot. apply Exists_exists. exists b. split; [exact Hbq|]. right. apply Exists_exists. exists it. split; [exact Hit|]. unfold ifoot, it_ab in Hz. exact Hz.
    - apply QF_OUT; [| unfold IMG_HI; lia]. unfold q_foot. apply Exists_exists. exists b. split; [exact Hbq|]. left. unfold kQuarantineBatchSize. lia. }
  assert (HMAX : cell_ok v' (mkACell (QG + 64) 8 kQuarantineMax)).
  { unfold rtc_inv, rtc_cells in HRTC. exact (cells_ok_nth _ _ 7 _ HRTC eq_refl). }
  assert (GMX : forall z, QG + 64 <= z < QG + 80 -> v3 z = v' z).
  { intros z Hz. destruct (Z_lt_dec z (QG + 72)).
    - apply (cell_ok_same v' v3 _ HMAX C_max). cbn [c_addr c_w]. lia.
    - apply (cell_ok_same v' v3 _ HMIN C_min). cbn [c_addr c_w]. unfold Inv.QG, QG in *. lia. }
  assert (PQW : forall z, P z -> ~ (QG + 64 <= z < QG + 80) -> QW A z).
  { intros z HP NG. unfold P in HP. destruct HP as [HP|[HP|[HP|HP]]].
    - right. left. left. fold T. lia.
    - right. left. right. left. exact HP.
    - right. left. right. right. exact HP.
    - exfalso. exact (NG HP). }
  assert (PPR : forall z, P z -> exists b, v3 z = Some b).
  { intros z HP. unfold P in HP. destruct HP as [HP|[HP|[HP|HP]]]; [apply PR1 | apply PR2 | apply PR3 | apply PR4]; lia. }
  assert (HK3 : K A rho3 tp tr md).
  { apply (kq_view segsA K HL A rho' rho3 tp tr md); [intros i; reflexivity | intros l; reflexivity | | | exact HK].
    - intros z NQ. destruct (PD z) as [HP|NP]; [|exact (FR z NP)].
      destruct (Z_lt_dec z (QG + 64)) as [|]; [exfalso; apply NQ; apply PQW; [exact HP | lia]|].
      destruct (Z_lt_dec z (QG + 80)) as [|]; [apply GMX; lia | exfalso; apply NQ; apply PQW; [exact HP | lia]].
    - intros z _ Hd. destruct (PD z) as [HP|NP]; [destruct (PPR z HP) as [b Hb]; fold v3; rewrite Hb; discriminate | fold v3 v' in Hd |- *; rewrite (FR z NP); exact Hd]. }
  assert (HK1 : K (set_q A [] tl) rho3 tp tr md).
  { apply (kq_perm segsA K HL A [] tl rho3 tp tr md); [|exact HK3]. rewrite QALL. cbn [app]. apply Permutation_refl. }
  assert (HQ1 : q_mem v3 (set_q A [] tl)).
  { unfold q_mem, qall. cbn [aa_q_thread aa_q_global aa_geom set_q app]. fold T.
    split; [|split; [exact I|split; [|split; [|split; [|exact C_mtx]]]]].
    - apply Forall_forall. intros b Hb.
      apply (batch_mem_frame A v' v3 b (proj1 (Forall_forall _ _) HBP b Hb)); [intros z Hz; exact (FR z (BF_OUT b Hb z (or_introl Hz)))|].
      exact (proj1 (Forall_forall _ _) HBM b Hb).
    - apply qlinks_to_0. apply (qlinks_to_frame v' v3 tl 0); [|apply qlinks_to_0; exact HLT].
      intros b z Hb Hz. apply FR. exact (BF_OUT b Hb z (or_intror Hz)).
    - unfold qhdr_repr. cbn [length]. change (T + 0x50) with (T + 80).
      split; [exact C_t0|]. split; [intros X; exfalso; exact (X eq_refl)|]. split; [intros z Hz; apply PR1; lia|]. exact C_t3.
    - unfold qhdr_repr.
      split; [exact C_g0|]. split; [|split; [intros z Hz; apply PR3; unfold Inv.QG, QG in *; lia | exact C_g3]].
      intros _. split; [exact C_g1 | exact C_g2]. }
  assert (QSZ : qsize tl <= kQuarantineMax).
  { unfold F_le in FLE. cbn [holds branch_taken] in FLE. rewrite EGS in FLE. cbn [eval] in FLE.
    apply negb_true_iff in FLE. unfold bv_ltu in FLE. apply Z.ltb_ge in FLE. rewrite !u64_lit in FLE by (unfold kQuarantineMax; lia). exact FLE. }
  set (TJ := (fun (_ : valuation) (_ : list word) (_ : list event) (_ : Model) => True) : jpredA).
  assert (HT : SPA segsA TJ PostQ3e rho' tp (tr, mkCfg ms md)) by (split; [exact (proj1 H) | exact I]).
  pose proof (SPA_unobj segsA TJ rho' PostQ3e KEPT3 REST3e tp tr ms md OBJS3e HT (fun x => x)) as HU. cbn zeta in HU. fold rho3 in HU.
  assert (STJ : stableA segsA NPRE TJ) by (unfold stableA, TJ; intros; exact I).
  pose proof (SPA_entails segsA TJ NPRE PostQ3e_k PostQ3 sde rho3 tp _ ENT3e SID3e STJ HU) as HE.
  pose proof (rho_sub_agree sde NPRE rho3 SID3e) as AG4.
  assert (ERM : forall a, rm rho' a = rm rho a) by (intros a; rewrite <- (proj2 (proj2 Hag) a), RRM; reflexivity).
  assert (EV' : forall z, v' z = view segsA (rm rho) z) by (intros z; unfold v'; apply view_agree; intros _; apply ERM).
  apply (LQPA_intro segsA NPRE rho tp [(PostQ3, JLQ3 segsA K A)] PostQ3 (JLQ3 segsA K A) (rho_sub rho3 sde) tp _ TJ (or_introl eq_refl) HE).
  - apply (agree_vals_trans NPRE rho (rhoT A gf gb rho)); [exact (agree_below_vals _ _ _ RAG)|].
    apply (agree_vals_trans NPRE _ rho'); [exact (agree_below_vals _ _ _ Hag)|].
    apply (agree_vals_trans NPRE _ rho3); [split; intros; reflexivity | exact (agree_below_vals _ _ _ AG4)].
  - intros _. cbn [w_tr w_cfg cfg_model fst snd]. exists (set_q A [] tl).
    assert (HJ4 : JQ3 segsA K (set_q A [] tl) (rho_sub rho3 sde) tp tr md).
    { eapply (JQ3_stable segsA K (set_q A [] tl) NPRE HL ltac:(apply Pos.le_refl)); [exact AG4 | apply mat_equiv_refl | exact (conj HK1 HQ1)]. }
    split; [exact (proj1 HJ4)|]. split; [exact (proj2 HJ4)|].
    split.
    { unfold qpost. split; [unfold same_but_qcs, set_q; reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [intros c Hc; exact Hc|]. cbn [aa_q_global set_q]. exact QSZ. }
    split.
    { intros a NQ. change (rm (rho_sub rho3 sde) a) with (rm rho3 a). rewrite <- ERM. apply FRrm. intros HP. apply NQ.
      destruct (Z_lt_dec (bv_unsigned a) (QG + 64)) as [|]; [left; left; apply PQW; [exact HP | lia]|].
      destruct (Z_lt_dec (bv_unsigned a) (QG + 80)) as [|]; [right; left; left; unfold Inv.QG, QG in *; lia | left; left; apply PQW; [exact HP | lia]]. }
    split.
    { intros z NQ. change (view segsA (rm (rho_sub rho3 sde)) z) with (v3 z). rewrite <- EV'. destruct (PD z) as [HP|NP]; [|exact (FR z NP)].
      destruct (Z_lt_dec z (QG + 64)) as [|]; [exfalso; apply NQ; left; apply PQW; [exact HP | lia]|].
      destruct (Z_lt_dec z (QG + 80)) as [|]; [apply GMX; lia | exfalso; apply NQ; left; apply PQW; [exact HP | lia]]. }
    split; [|split; [reflexivity|]].
    { intros l. change (rl (rho_sub rho3 sde) l) with (rl rho' l). rewrite <- (proj1 (proj2 Hag) l). symmetry. exact (proj1 (proj2 RAG) l). }
    intros a HB Hdef. change (rm (rho_sub rho3 sde) a) with (rm rho3 a). rewrite FRrm; [rewrite ERM; exact Hdef|].
    intros HP. unfold P in HP. pose proof (geom_bands _ HG0) as (_ & TBD & _). fold T in TBD.
    unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END, Inv.QG, QG in *. clear -HP HB TBD. lia.
Qed.

Definition HREC_n (A : AA) (rho : valuation) (tp : list word) (Q : assn) : Prop := ltac2:(tb__ "0|1|
S1dS80S3dS6bVA;S7fS12VA;A1M0A1S7eG0A1Vrho;A4R1A3S7cS32Vok;S5bS32S5dS32VK;VA;A3S50R2Vtp;A5VQ;A4F_;Frho';").
Definition HREC_e (A : AA) (rho : valuation) (tp : list word) (Q : assn) : Prop := ltac2:(tb__ "0|0|
SfSfS1dS80S3dS6bVA;R3R2Vrho;A4R1A3S7cS32Vok;S5bS32S5dS32VK;VA;A3S4fR2Vtp;A5VQ;A4F_;Frho';Fgb;Fgf;").
Definition HRECE_n (A : AA) (rho : valuation) (tp : list word) (Q : world -> Prop) : Prop := ltac2:(tb__ "0|1|
S1dS80S3dS6bVA;S7fS12VA;A1M0A1S7eG0A1Vrho;A4R1A3S7bS32S5bS32S5dS32VK;VA;A3S50R2Vtp;A5VQ;A3F_;Frho';").
Definition HRECE_e (A : AA) (rho : valuation) (tp : list word) (Q : world -> Prop) : Prop := ltac2:(tb__ "0|0|
SfSfS1dS80S3dS6bVA;R3R2Vrho;A4R1A3S7bS32S5bS32S5dS32VK;VA;A3S4fR2Vtp;A5VQ;A3F_;Frho';Fgb;Fgf;").

Theorem transfer_sound : ltac2:(tb__ "0|3|
S13S1dS4S3aQ40A1A1S7dS18S17S4S11A1M0S14R4A1S3S11A1M1A3A1S17S6S15R5A1S7A3S5eR6A1S7aS6fS32S67R7R6S1S5S64S6eA2M2S0S64S6eS6cS5fS32VK;R8A3A4S3G2A1A3R1A6R6R2A1F_;Fw;S18S17G0S12R8A1G1A3A1S92R9R8R7R6A4F_;S17G0S12R9A1G1A3S91RaR9R8R7A4F_;S7cS32Vok;S5bS32S5dS32VK;RaA3S6dR9R8A5R7A4F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho;FA;").
Proof.
  intros A rho tp Q HTL HCI HBND HQ HRn HRe k Hg w Hw.
  assert (HST : stableA segsA NPRE (JQ3 segsA K A)) by (apply (JQ3_stable segsA K A NPRE HL); apply Pos.le_refl).
  destruct (aa_q_global A) as [|g0 gl'] eqn:EG.
  - destruct (entry_e A rho tp w HTL EG HBND Hw) as (gf & gb & Hw1).
    refine (seg_Q3Te_sound (JQ3 segsA K A) ok _ tp Q (JQ3_ok_frame segsA K A ok (HOK A)) HST _ k Hg w Hw1).
    intros T rho' HT HKp. destruct HT as [<-|[<-|[]]].
    + eapply triple_conseq; [intros w' Hw'; exact Hw' | exact HQ |]. intros k' Hg' w' Hw'. apply Hg'. exact (exit_e A gf gb rho rho' tp w' HTL EG HBND HKp Hw').
    + exact (HRe eq_refl gf gb rho' HKp).
  - assert (HGL : aa_q_global A <> []) by (rewrite EG; discriminate). rewrite <- EG in *.
    pose proof (entry_n A rho tp w HTL HGL HCI HBND Hw) as Hw1.
    refine (seg_Q3Tn_sound (JQ3 segsA K A) ok _ tp Q (JQ3_ok_frame segsA K A ok (HOK A)) HST _ k Hg w Hw1).
    intros T rho' HT HKp. destruct HT as [<-|[<-|[]]].
    + eapply triple_conseq; [intros w' Hw'; exact Hw' | exact HQ |]. intros k' Hg' w' Hw'. apply Hg'. exact (exit_n A rho rho' tp w' HTL HGL HCI HBND HKp Hw').
    + exact (HRn HGL rho' HKp).
Qed.

Theorem transfer_complete : ltac2:(tb__ "0|3|
S13S1dS4S3aQ40A1A1S7aOF_;S18S17S4S11A1M0S14R4A1S3S11A1M1A3A1S17S6S15R5A1S7A3S5eR6A1S7aS6fS32S67R7R6S1S5S64S6eA2M2S0S64S6eS6cS5fS32VK;R8A3A4S3G2A1A3R1A6R6R2A1F_;Fw;S18S17G0S12R8A1G1A3A1S90R9R8R7R6A4F_;S17G0S12R9A1G1A3S8fRaR9R8R7A4F_;S7bS32S5bS32S5dS32VK;RaA3S6dR9R8A5R7A3F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho;FA;").
Proof.
  intros A rho tp Q HTL HCI HBND HQ HRn HRe w Hw.
  assert (HST : stableA segsA NPRE (JQ3 segsA K A)) by (apply (JQ3_stable segsA K A NPRE HL); apply Pos.le_refl).
  destruct (aa_q_global A) as [|g0 gl'] eqn:EG.
  - destruct (entry_e A rho tp w HTL EG HBND Hw) as (gf & gb & Hw1).
    refine (seg_Q3Te_complete (JQ3 segsA K A) _ tp Q HST _ w Hw1).
    intros T rho' HT HKp. destruct HT as [<-|[<-|[]]].
    + eapply etriple_conseq; [intros w' Hw'; exact Hw' | exact HQ |]. intros w' Hw'. exists w'. split; [apply wsteps_refl|]. exact (exit_e A gf gb rho rho' tp w' HTL EG HBND HKp Hw').
    + exact (HRe eq_refl gf gb rho' HKp).
  - assert (HGL : aa_q_global A <> []) by (rewrite EG; discriminate). rewrite <- EG in *.
    pose proof (entry_n A rho tp w HTL HGL HCI HBND Hw) as Hw1.
    refine (seg_Q3Tn_complete (JQ3 segsA K A) _ tp Q HST _ w Hw1).
    intros T rho' HT HKp. destruct HT as [<-|[<-|[]]].
    + eapply etriple_conseq; [intros w' Hw'; exact Hw' | exact HQ |]. intros w' Hw'. exists w'. split; [apply wsteps_refl|]. exact (exit_n A rho rho' tp w' HTL HGL HCI HBND HKp Hw').
    + exact (HRn HGL rho' HKp).
Qed.

End Drain.
End SegQ3_skel.

(* [comment removed for export] *)
Module F0A_cL0A.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "leafA"; "ax_setS"; "la_state"; "@Corelib.Init.Datatypes"; "bool"; "cons"; "nil"; "true"; "list"; "Some"; "option"; "false"; "prod"; "pair"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "ss_next"; "sv"; "sprop"; "ss_lenient"; "ss_facts"; "sobj"; "sprop_below"; "swf"; "SLit"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states"; "FUELF"; "DEPE"; "leaves_at"; "sD_of"; "BIGX"; "CASX"; "DRNE"; "ENQE"; "MSE"; "PSE"; "PreQ1"; "RETF"; "sM_of"; "sQ_of"; "F_typ"; "PostQ1"; "S1c_of"; "XD"; "XDr"; "casx"; "vH3"; "PostMS"; "XQ"; "d3F"; "d4F"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states"; "runA"; "leaf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ie.F0A_cL0A"; "C4_L0A"; "EQ_L0A"; "q_L0A"; "C2_L0A_1"; "C2_L0A_2"; "C3_L0A"; "CD_L0A"; "ED_L0A_1"; "ED_L0A_2"; "P0_L0A"; "Ems_L0A"; "Eps_L0A"; "S1c_L0A_1"; "S1c_L0A_2"; "TM_L0A"; "TQ_L0A"; "run3_L0A"; "run6_L0A"; "RM_L0A"; "RQ_L0A"; "TM0_L0A"; "TQ0_L0A"; "run2_L0A_1"; "run2_L0A_2"; "run4_L0A"; "run5_L0A"; "EfD_L0A_1"; "EfD_L0A_2"; "Eq_L0A"; "RD_L0A_1"; "RD_L0A_2"; "TDr_L0A_1"; "TDr_L0A_2"; "exits1_L0A"; "run1_L0A"; "Ebg_L0A"; "Edr_L0A"; "TD_L0A_1"; "TD_L0A_2"; "W_L0A"; "Xf_L0A"; "st_L0A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "segsA"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "entails_frA"; "call_checkA"; "call_checkPA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states"; "PreD"; "PostD"; "@Stdlib.Lists.List"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset"; "Pre_memsetA"; "Posts_memsetA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_cfgA"; "check_ecfgA"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib"; "entsI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls"; "P0_fc"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame SymCFG SymCall SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA EntailA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import ObjXform ObjUnbase MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.
Import ListNotations.
Open Scope Z_scope.

Definition W_L0A : list ulink := Wcan 0.
Definition st_L0A : ustop := UStopLe.
Definition q_L0A : qvar := QA.
Definition P0_L0A : axst := ltac2:(tb__ "0|0|
S76S10S5eS60S39A4").

Definition run1_L0A : list leafA := ltac2:(tb__ "0|0|
S35S1cSaS2S21SbS2A1A3S40A3").

Definition S1c_L0A_1 : axst := ltac2:(tb__ "0|0|
S2cS36U0S59A2S17S5S40A1A1Z1A3").
Definition C2_L0A_1 : axst := C2_of S1c_L0A_1.
Definition run2_L0A_1 : list leafA := ltac2:(tb__ "0|0|
S35S1cSaS2S1dSbS2A1A3S3aA3").
Definition EfD_L0A_1 : axst := leaf 0 run2_L0A_1.
Definition ED_L0A_1 : axst := ED_of EfD_L0A_1.
Definition RD_L0A_1 : list sobj := RD_of ED_L0A_1 1.
Definition TD_L0A_1 : axst := TD_of ED_L0A_1 1.
Definition TDr_L0A_1 : axst := TDr_of TD_L0A_1.
Definition S1c_L0A_2 : axst := ltac2:(tb__ "0|0|
S2cS36U0S59A2S17S5S40A1A1Z2A3").
Definition C2_L0A_2 : axst := C2_of S1c_L0A_2.
Definition run2_L0A_2 : list leafA := ltac2:(tb__ "0|0|
S35S1cSaS2S1dSbS2A1A3S3bA3").
Definition EfD_L0A_2 : axst := leaf 0 run2_L0A_2.
Definition ED_L0A_2 : axst := ED_of EfD_L0A_2.
Definition RD_L0A_2 : list sobj := RD_of ED_L0A_2 2.
Definition TD_L0A_2 : axst := TD_of ED_L0A_2 2.
Definition TDr_L0A_2 : axst := TDr_of TD_L0A_2.
Definition exits1_L0A : list axst := ltac2:(tb__ "0|0|
SaS4S43SaS4S44SbS4A1A3A3").

Definition CD_L0A : axst := CD_of TDr_L0A_1.
Definition run3_L0A : list leafA := ltac2:(tb__ "0|0|
S35S1cSaS2S25SaS2S20SbS2A1A3A3S3dA3").
Definition Eps_L0A : axst := leaf 0 run3_L0A.
Definition Ebg_L0A : axst := leaf 1 run3_L0A.
Definition C3_L0A : axst := C3_of Eps_L0A.
Definition run4_L0A : list leafA := ltac2:(tb__ "0|0|
S35S1cSaS2S24SbS2A1A3S3cA3").
Definition Ems_L0A : axst := leaf 0 run4_L0A.
Definition C4_L0A : axst := C4_of Ems_L0A.
Definition RM_L0A : list sobj := RM_of C4_L0A.
Definition TM0_L0A : axst := TM0_of C4_L0A.
Definition TM_L0A : axst := TM_of C4_L0A.
Definition run5_L0A : list leafA := ltac2:(tb__ "0|0|
S35S1cSaS2S23SbS2A1A3S45A3").
Definition Eq_L0A : axst := leaf 0 run5_L0A.
Definition EQ_L0A : axst := EQ_of Eq_L0A.
Definition RQ_L0A : list sobj := RQ_of EQ_L0A q_L0A.
Definition TQ0_L0A : axst := TQ0_of EQ_L0A q_L0A.
Definition TQ_L0A : axst := TQ_of EQ_L0A q_L0A.
Definition run6_L0A : list leafA := ltac2:(tb__ "0|0|
S35S1cSaS2S22SaS2S27SbS2A1A3A3S46A3").
Definition Edr_L0A : axst := leaf 0 run6_L0A.
Definition Xf_L0A : axst := leaf 1 run6_L0A.

Ltac vmr := match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end.
Lemma Cert1_L0A : ltac2:(tb__ "0|0|
S0S9S71S62S1cSaS2S21SbS2A1A3S61SaS4S40SbS4A1A3S58A6ScA3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runl segsA FUELF [CASX] GW P0_L0A exits1_L0A run1_L0A); [unfold run1_L0A, runA, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.runlA; reflexivity | vmr]. Qed.
Lemma ECert1_L0A : ltac2:(tb__ "0|2|
S0S9S72S62S1cSaS2S21SbS2A1A3S61SaS6fS70S40Z1S1bZ0M0A1M1A3SbS6fA1A3S73S4S6fS4S70R1G0G1A3LE;S58A4A6ScA3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runl segsA FUELF [CASX] GW (mkVNA P0_L0A 1 (SLit 0)) (map (fun E => mkVNA E 0 (SLit 0)) exits1_L0A) run1_L0A); [unfold run1_L0A, runA, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.runlA; reflexivity | vmr]. Qed.

Lemma D2_L0A_1 : ltac2:(tb__ "0|4|
S0SfS11SdS11S14S14A2M0A1M1SdS15A1M2A2M3A1S65S5S43A1S5S3aA1A2SeG3S12G1G2SaG0S12S14S14S2fS30A4SbG0A1A3S2aA4A2A3"). Proof. Time vmr. Qed.
Lemma W2_L0A_1 : ltac2:(tb__ "0|1|
S1S0S9S1aS5S3aA1M0A1ScA3S1S0S3S13G0A1S13S5S43A1A1A3S0S9S16G0A1S10A3A2A2"). Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma NX2_L0A_1 : ltac2:(tb__ "0|0|
S0S9S63S61S13S5S3aA1A1A2ScA3"). Proof. vmr. Qed.
Lemma EQ2_L0A_1 : ltac2:(tb__ "0|0|
S0S4S7S43S5S3aA1A2S3aA3"). Proof. vmr. Qed.
Lemma RUN2_L0A_1 : ltac2:(tb__ "0|0|
S0SdS6A1S35S1cSaS2S1dSbS2A1A3S3aA3S4dA3"). Proof. unfold run2_L0A_1; reflexivity. Qed.
Lemma L2_L0A_1 : ltac2:(tb__ "0|0|
S1S0S9S1eS4dSaS2S1dSbS2A1A3A2ScA3S0S4S36U0S4dA2S51A3A2"). Proof. Time (split; [vmr | unfold EfD_L0A_1; reflexivity]). Qed.
Lemma AXD_L0A_1 : ltac2:(tb__ "0|0|
S0SfS4A1S64S51S2dA2SeS4S3eA2A3"). Proof. Time vmr. Qed.
Lemma HeD_L0A_1 : ltac2:(tb__ "0|2|
S0SfSdS18A1M0A1S66S3eS6aZ1M1A1S1fS3eG1A2A3SeG0S54A2A3"). Proof. Time vmr. Qed.
Lemma HchkD_L0A_1 : ltac2:(tb__ "0|1|
S0S9S68S3eS6aZ1M0A1S1fS3eG0A2S54SaS4S6bG0A1SbS4A1A3A5ScA3"). Proof. Time vmr. Qed.
Lemma AXDr_L0A_1 : ltac2:(tb__ "0|0|
S0SfS4A1S64S5cS2eA2SeS4S56A2A3"). Proof. Time vmr. Qed.
Lemma ENTD_L0A_1 : ltac2:(tb__ "0|0|
S0S9S75S56S3dA2ScA3"). Proof. Time vmr. Qed.
Lemma D2_L0A_2 : ltac2:(tb__ "0|4|
S0SfS11SdS11S14S14A2M0A1M1SdS15A1M2A2M3A1S65S5S44A1S5S3bA1A2SeG3S12G1G2SaG0S12S14S14S2fS30A4SbG0A1A3S2aA4A2A3"). Proof. Time vmr. Qed.
Lemma W2_L0A_2 : ltac2:(tb__ "0|1|
S1S0S9S1aS5S3bA1M0A1ScA3S1S0S3S13G0A1S13S5S44A1A1A3S0S9S16G0A1S10A3A2A2"). Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma NX2_L0A_2 : ltac2:(tb__ "0|0|
S0S9S63S61S13S5S3bA1A1A2ScA3"). Proof. vmr. Qed.
Lemma EQ2_L0A_2 : ltac2:(tb__ "0|0|
S0S4S7S44S5S3bA1A2S3bA3"). Proof. vmr. Qed.
Lemma RUN2_L0A_2 : ltac2:(tb__ "0|0|
S0SdS6A1S35S1cSaS2S1dSbS2A1A3S3bA3S4eA3"). Proof. unfold run2_L0A_2; reflexivity. Qed.
Lemma L2_L0A_2 : ltac2:(tb__ "0|0|
S1S0S9S1eS4eSaS2S1dSbS2A1A3A2ScA3S0S4S36U0S4eA2S52A3A2"). Proof. Time (split; [vmr | unfold EfD_L0A_2; reflexivity]). Qed.
Lemma AXD_L0A_2 : ltac2:(tb__ "0|0|
S0SfS4A1S64S52S2dA2SeS4S3fA2A3"). Proof. Time vmr. Qed.
Lemma HeD_L0A_2 : ltac2:(tb__ "0|2|
S0SfSdS18A1M0A1S66S3fS6aZ2M1A1S1fS3fG1A2A3SeG0S55A2A3"). Proof. Time vmr. Qed.
Lemma HchkD_L0A_2 : ltac2:(tb__ "0|1|
S0S9S68S3fS6aZ2M0A1S1fS3fG0A2S55SaS4S6bG0A1SbS4A1A3A5ScA3"). Proof. Time vmr. Qed.
Lemma AXDr_L0A_2 : ltac2:(tb__ "0|0|
S0SfS4A1S64S5dS2eA2SeS4S57A2A3"). Proof. Time vmr. Qed.
Lemma ENTD_L0A_2 : ltac2:(tb__ "0|0|
S0S9S75S57S3dA2ScA3"). Proof. Time vmr. Qed.
Lemma RUN3_L0A : ltac2:(tb__ "0|0|
S0SdS6A1S35S1cSaS2S25SaS2S20SbS2A1A3A3S3dA3S47A3"). Proof. unfold run3_L0A; reflexivity. Qed.
Lemma L3_L0A : ltac2:(tb__ "0|0|
S1S0S9S1eS47SaS2S25SaS2S20SbS2A1A3A3A2ScA3S1S0S4S36U0S47A2S42A3S0S4S36U1S47A2S5aA3A2A2"). Proof. Time (split; [vmr | split; [unfold Eps_L0A | unfold Ebg_L0A]; reflexivity]). Qed.
Lemma NX3_L0A : ltac2:(tb__ "0|1|
S1S0S9S63S61S13S5S3dA1M0A1A2ScA3S0S9S16G0A1S10A3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma D3_L0A : ltac2:(tb__ "0|3|
S0SfS11SdS11S14S14A2A1M0SdS15A1M1A2M2A1S65S5S42A1S5S3cA1A2SeG2S12G0G1S33SbS15A1A4A2A3"). Proof. Time vmr. Qed.
Lemma EQ3_L0A : ltac2:(tb__ "0|0|
S0S4S7S42S5S3cA1A2S3cA3"). Proof. vmr. Qed.
Lemma NX3b_L0A : ltac2:(tb__ "0|0|
S0S9S63S61S13S5S3cA1A1A2ScA3"). Proof. vmr. Qed.
Lemma W3_L0A : ltac2:(tb__ "0|1|
S1S0S9S1aS5S3cA1M0A1ScA3S1S0S3S13G0A1S13S5S42A1A1A3S0S9S16G0A1S10A3A2A2"). Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma RUN4_L0A : ltac2:(tb__ "0|0|
S0SdS6A1S35S1cSaS2S24SbS2A1A3S3cA3S4fA3"). Proof. unfold run4_L0A; reflexivity. Qed.
Lemma L4_L0A : ltac2:(tb__ "0|0|
S1S0S9S1eS4fSaS2S24SbS2A1A3A2ScA3S0S4S36U0S4fA2S41A3A2"). Proof. Time (split; [vmr | unfold Ems_L0A; reflexivity]). Qed.
Lemma D4_L0A : ltac2:(tb__ "0|3|
S0SfS11SdS11S14S14A2A1M0SdS15A1M1A2M2A1S65S5S41A1S5S37A1A2SeG2S12G0G1S34SbS15A1A4A2A3"). Proof. Time vmr. Qed.
Lemma EQ4_L0A : ltac2:(tb__ "0|0|
S0S4S7S41S5S37A1A2S37A3"). Proof. vmr. Qed.
Lemma W4_L0A : ltac2:(tb__ "0|1|
S1S0S9S1aS5S37A1M0A1ScA3S1S0S3S13G0A1S13S5S41A1A1A3S0S9S16G0A1S10A3A2A2"). Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma HeM_L0A : ltac2:(tb__ "0|1|
S0SfSdS18A1M0A1S66S37S6dS28S37A1A3SeG0S49A2A3"). Proof. Time vmr. Qed.
Lemma HchkM_L0A : ltac2:(tb__ "0|0|
S0S9S67S37S6dS28S37A1S49S73S6S4S8S6eA4A5ScA3"). Proof. Time vmr. Qed.
Lemma HTM_L0A : ltac2:(tb__ "0|0|
S0S4S69S28S37A1S6dS31S37S49A5S4bA3"). Proof. unfold TM0_L0A, TM0_of, RM_L0A; reflexivity. Qed.
Lemma FBM_L0A : ltac2:(tb__ "0|3|
S1S0S9S6cS15S19S13S5S37A1M0A1M1A1S17G0A1M2A3ScA3S1S0S9S6cS15S19S13S5S4bA1A1A1G2A3ScA3S0S9S63S61G1A2ScA3A2A2").
Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma ETM_L0A : ltac2:(tb__ "0|0|
S0S4S74S4bS17S5S37A1A1A2S45A3"). Proof. vmr. Qed.
Lemma NX5_L0A : ltac2:(tb__ "0|1|
S1S0S9S63S61S13S5S45A1M0A1A2ScA3S0S9S16G0A1S10A3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma RUN5_L0A : ltac2:(tb__ "0|0|
S0SdS6A1S35S1cSaS2S23SbS2A1A3S45A3S50A3"). Proof. unfold run5_L0A; reflexivity. Qed.
Lemma L5_L0A : ltac2:(tb__ "0|0|
S1S0S9S1eS50SaS2S23SbS2A1A3A2ScA3S0S4S36U0S50A2S53A3A2"). Proof. Time (split; [vmr | unfold Eq_L0A; reflexivity]). Qed.
Lemma AXQ_L0A : ltac2:(tb__ "0|0|
S0SfS4A1S64S53S32A2SeS4S38A2A3"). Proof. Time vmr. Qed.
Lemma HeQ_L0A : ltac2:(tb__ "0|1|
S0SfSdS18A1M0A1S66S38S26S39A1S29S38S39A2A3SeG0S4aA2A3"). Proof. Time vmr. Qed.
Lemma HchkQ_L0A : ltac2:(tb__ "0|0|
S0S9S67S38S26S39A1S29S38S39A2S4aSaS4S2bS39A1SbS4A1A3A5ScA3"). Proof. Time vmr. Qed.
Lemma HTQ_L0A : ltac2:(tb__ "0|0|
S0S4S69S29S38S39A2S26S39A1S2bS39A1S38S4aA5S4cA3"). Proof. unfold TQ0_L0A, TQ0_of, RQ_L0A; reflexivity. Qed.
Lemma FBQ_L0A : ltac2:(tb__ "0|3|
S1S0S9S6cS15S19S13S5S38A1M0A1M1A1S17G0A1M2A3ScA3S1S0S9S6cS15S19S13S5S4cA1A1A1G2A3ScA3S0S9S63S61G1A2ScA3A2A2").
Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma ETQ_L0A : ltac2:(tb__ "0|0|
S0S4S74S4cS17S5S38A1A1A2S46A3"). Proof. vmr. Qed.
Lemma NX6_L0A : ltac2:(tb__ "0|1|
S1S0S9S63S61S13S5S46A1M0A1A2ScA3S0S9S16G0A1S10A3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma RUN6_L0A : ltac2:(tb__ "0|0|
S0SdS6A1S35S1cSaS2S22SaS2S27SbS2A1A3A3S46A3S48A3"). Proof. unfold run6_L0A; reflexivity. Qed.
Lemma L6_L0A : ltac2:(tb__ "0|0|
S1S0S9S1eS48SaS2S22SaS2S27SbS2A1A3A3A2ScA3S1S0S4S36U0S48A2S5bA3S0S4S36U1S48A2S5fA3A2A2"). Proof. Time (split; [vmr | split; [unfold Edr_L0A | unfold Xf_L0A]; reflexivity]). Qed.

End F0A_cL0A.

(* [comment removed for export] *)
Module F0A_cL0Bf.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "leafA"; "ax_setS"; "la_state"; "@Corelib.Init.Datatypes"; "bool"; "cons"; "nil"; "true"; "list"; "Some"; "option"; "false"; "prod"; "pair"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "ss_next"; "sv"; "sprop"; "ss_lenient"; "ss_facts"; "sobj"; "sprop_below"; "swf"; "SLit"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states"; "FUELF"; "DEPE"; "leaves_at"; "sD_of"; "BIGX"; "CASX"; "DRNE"; "ENQE"; "MSE"; "PSE"; "PreQ1"; "RETF"; "sM_of"; "sQ_of"; "F_typ"; "PostQ1"; "S1c_of"; "XD"; "XDr"; "casx"; "vH3"; "PostMS"; "XQ"; "d3F"; "d4F"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states"; "runA"; "leaf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ie.F0A_cL0Bf"; "C4_L0Bf"; "EQ_L0Bf"; "q_L0Bf"; "C2_L0Bf_1"; "C2_L0Bf_2"; "C3_L0Bf"; "CD_L0Bf"; "ED_L0Bf_1"; "ED_L0Bf_2"; "P0_L0Bf"; "Ems_L0Bf"; "Eps_L0Bf"; "S1c_L0Bf_1"; "S1c_L0Bf_2"; "TM_L0Bf"; "TQ_L0Bf"; "run3_L0Bf"; "run6_L0Bf"; "RM_L0Bf"; "RQ_L0Bf"; "TM0_L0Bf"; "TQ0_L0Bf"; "run2_L0Bf_1"; "run2_L0Bf_2"; "run4_L0Bf"; "run5_L0Bf"; "EfD_L0Bf_1"; "EfD_L0Bf_2"; "Eq_L0Bf"; "RD_L0Bf_1"; "RD_L0Bf_2"; "TDr_L0Bf_1"; "TDr_L0Bf_2"; "exits1_L0Bf"; "run1_L0Bf"; "Ebg_L0Bf"; "Edr_L0Bf"; "TD_L0Bf_1"; "TD_L0Bf_2"; "W_L0Bf"; "Xf_L0Bf"; "st_L0Bf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "segsA"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "entails_frA"; "call_checkA"; "call_checkPA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states"; "PreD"; "PostD"; "@Stdlib.Lists.List"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset"; "Pre_memsetA"; "Posts_memsetA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_cfgA"; "check_ecfgA"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib"; "entsI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls"; "P0_fc"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame SymCFG SymCall SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA EntailA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import ObjXform ObjUnbase MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.
Import ListNotations.
Open Scope Z_scope.

Definition W_L0Bf : list ulink := Wcan 0.
Definition st_L0Bf : ustop := UStopLe.
Definition q_L0Bf : qvar := QBf.
Definition P0_L0Bf : axst := ltac2:(tb__ "0|0|
S76S10S5eS60S39A4").

Definition run1_L0Bf : list leafA := ltac2:(tb__ "0|0|
S35S1cSaS2S21SbS2A1A3S40A3").

Definition S1c_L0Bf_1 : axst := ltac2:(tb__ "0|0|
S2cS36U0S59A2S17S5S40A1A1Z1A3").
Definition C2_L0Bf_1 : axst := C2_of S1c_L0Bf_1.
Definition run2_L0Bf_1 : list leafA := ltac2:(tb__ "0|0|
S35S1cSaS2S1dSbS2A1A3S3aA3").
Definition EfD_L0Bf_1 : axst := leaf 0 run2_L0Bf_1.
Definition ED_L0Bf_1 : axst := ED_of EfD_L0Bf_1.
Definition RD_L0Bf_1 : list sobj := RD_of ED_L0Bf_1 1.
Definition TD_L0Bf_1 : axst := TD_of ED_L0Bf_1 1.
Definition TDr_L0Bf_1 : axst := TDr_of TD_L0Bf_1.
Definition S1c_L0Bf_2 : axst := ltac2:(tb__ "0|0|
S2cS36U0S59A2S17S5S40A1A1Z2A3").
Definition C2_L0Bf_2 : axst := C2_of S1c_L0Bf_2.
Definition run2_L0Bf_2 : list leafA := ltac2:(tb__ "0|0|
S35S1cSaS2S1dSbS2A1A3S3bA3").
Definition EfD_L0Bf_2 : axst := leaf 0 run2_L0Bf_2.
Definition ED_L0Bf_2 : axst := ED_of EfD_L0Bf_2.
Definition RD_L0Bf_2 : list sobj := RD_of ED_L0Bf_2 2.
Definition TD_L0Bf_2 : axst := TD_of ED_L0Bf_2 2.
Definition TDr_L0Bf_2 : axst := TDr_of TD_L0Bf_2.
Definition exits1_L0Bf : list axst := ltac2:(tb__ "0|0|
SaS4S43SaS4S44SbS4A1A3A3").

Definition CD_L0Bf : axst := CD_of TDr_L0Bf_1.
Definition run3_L0Bf : list leafA := ltac2:(tb__ "0|0|
S35S1cSaS2S25SaS2S20SbS2A1A3A3S3dA3").
Definition Eps_L0Bf : axst := leaf 0 run3_L0Bf.
Definition Ebg_L0Bf : axst := leaf 1 run3_L0Bf.
Definition C3_L0Bf : axst := C3_of Eps_L0Bf.
Definition run4_L0Bf : list leafA := ltac2:(tb__ "0|0|
S35S1cSaS2S24SbS2A1A3S3cA3").
Definition Ems_L0Bf : axst := leaf 0 run4_L0Bf.
Definition C4_L0Bf : axst := C4_of Ems_L0Bf.
Definition RM_L0Bf : list sobj := RM_of C4_L0Bf.
Definition TM0_L0Bf : axst := TM0_of C4_L0Bf.
Definition TM_L0Bf : axst := TM_of C4_L0Bf.
Definition run5_L0Bf : list leafA := ltac2:(tb__ "0|0|
S35S1cSaS2S23SbS2A1A3S45A3").
Definition Eq_L0Bf : axst := leaf 0 run5_L0Bf.
Definition EQ_L0Bf : axst := EQ_of Eq_L0Bf.
Definition RQ_L0Bf : list sobj := RQ_of EQ_L0Bf q_L0Bf.
Definition TQ0_L0Bf : axst := TQ0_of EQ_L0Bf q_L0Bf.
Definition TQ_L0Bf : axst := TQ_of EQ_L0Bf q_L0Bf.
Definition run6_L0Bf : list leafA := ltac2:(tb__ "0|0|
S35S1cSaS2S22SaS2S27SbS2A1A3A3S46A3").
Definition Edr_L0Bf : axst := leaf 0 run6_L0Bf.
Definition Xf_L0Bf : axst := leaf 1 run6_L0Bf.

Ltac vmr := match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end.
Lemma Cert1_L0Bf : ltac2:(tb__ "0|0|
S0S9S71S62S1cSaS2S21SbS2A1A3S61SaS4S40SbS4A1A3S58A6ScA3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runl segsA FUELF [CASX] GW P0_L0Bf exits1_L0Bf run1_L0Bf); [unfold run1_L0Bf, runA, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.runlA; reflexivity | vmr]. Qed.
Lemma ECert1_L0Bf : ltac2:(tb__ "0|2|
S0S9S72S62S1cSaS2S21SbS2A1A3S61SaS6fS70S40Z1S1bZ0M0A1M1A3SbS6fA1A3S73S4S6fS4S70R1G0G1A3LE;S58A4A6ScA3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runl segsA FUELF [CASX] GW (mkVNA P0_L0Bf 1 (SLit 0)) (map (fun E => mkVNA E 0 (SLit 0)) exits1_L0Bf) run1_L0Bf); [unfold run1_L0Bf, runA, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.runlA; reflexivity | vmr]. Qed.

Lemma D2_L0Bf_1 : ltac2:(tb__ "0|4|
S0SfS11SdS11S14S14A2M0A1M1SdS15A1M2A2M3A1S65S5S43A1S5S3aA1A2SeG3S12G1G2SaG0S12S14S14S2fS30A4SbG0A1A3S2aA4A2A3"). Proof. Time vmr. Qed.
Lemma W2_L0Bf_1 : ltac2:(tb__ "0|1|
S1S0S9S1aS5S3aA1M0A1ScA3S1S0S3S13G0A1S13S5S43A1A1A3S0S9S16G0A1S10A3A2A2"). Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma NX2_L0Bf_1 : ltac2:(tb__ "0|0|
S0S9S63S61S13S5S3aA1A1A2ScA3"). Proof. vmr. Qed.
Lemma EQ2_L0Bf_1 : ltac2:(tb__ "0|0|
S0S4S7S43S5S3aA1A2S3aA3"). Proof. vmr. Qed.
Lemma RUN2_L0Bf_1 : ltac2:(tb__ "0|0|
S0SdS6A1S35S1cSaS2S1dSbS2A1A3S3aA3S4dA3"). Proof. unfold run2_L0Bf_1; reflexivity. Qed.
Lemma L2_L0Bf_1 : ltac2:(tb__ "0|0|
S1S0S9S1eS4dSaS2S1dSbS2A1A3A2ScA3S0S4S36U0S4dA2S51A3A2"). Proof. Time (split; [vmr | unfold EfD_L0Bf_1; reflexivity]). Qed.
Lemma AXD_L0Bf_1 : ltac2:(tb__ "0|0|
S0SfS4A1S64S51S2dA2SeS4S3eA2A3"). Proof. Time vmr. Qed.
Lemma HeD_L0Bf_1 : ltac2:(tb__ "0|2|
S0SfSdS18A1M0A1S66S3eS6aZ1M1A1S1fS3eG1A2A3SeG0S54A2A3"). Proof. Time vmr. Qed.
Lemma HchkD_L0Bf_1 : ltac2:(tb__ "0|1|
S0S9S68S3eS6aZ1M0A1S1fS3eG0A2S54SaS4S6bG0A1SbS4A1A3A5ScA3"). Proof. Time vmr. Qed.
Lemma AXDr_L0Bf_1 : ltac2:(tb__ "0|0|
S0SfS4A1S64S5cS2eA2SeS4S56A2A3"). Proof. Time vmr. Qed.
Lemma ENTD_L0Bf_1 : ltac2:(tb__ "0|0|
S0S9S75S56S3dA2ScA3"). Proof. Time vmr. Qed.
Lemma D2_L0Bf_2 : ltac2:(tb__ "0|4|
S0SfS11SdS11S14S14A2M0A1M1SdS15A1M2A2M3A1S65S5S44A1S5S3bA1A2SeG3S12G1G2SaG0S12S14S14S2fS30A4SbG0A1A3S2aA4A2A3"). Proof. Time vmr. Qed.
Lemma W2_L0Bf_2 : ltac2:(tb__ "0|1|
S1S0S9S1aS5S3bA1M0A1ScA3S1S0S3S13G0A1S13S5S44A1A1A3S0S9S16G0A1S10A3A2A2"). Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma NX2_L0Bf_2 : ltac2:(tb__ "0|0|
S0S9S63S61S13S5S3bA1A1A2ScA3"). Proof. vmr. Qed.
Lemma EQ2_L0Bf_2 : ltac2:(tb__ "0|0|
S0S4S7S44S5S3bA1A2S3bA3"). Proof. vmr. Qed.
Lemma RUN2_L0Bf_2 : ltac2:(tb__ "0|0|
S0SdS6A1S35S1cSaS2S1dSbS2A1A3S3bA3S4eA3"). Proof. unfold run2_L0Bf_2; reflexivity. Qed.
Lemma L2_L0Bf_2 : ltac2:(tb__ "0|0|
S1S0S9S1eS4eSaS2S1dSbS2A1A3A2ScA3S0S4S36U0S4eA2S52A3A2"). Proof. Time (split; [vmr | unfold EfD_L0Bf_2; reflexivity]). Qed.
Lemma AXD_L0Bf_2 : ltac2:(tb__ "0|0|
S0SfS4A1S64S52S2dA2SeS4S3fA2A3"). Proof. Time vmr. Qed.
Lemma HeD_L0Bf_2 : ltac2:(tb__ "0|2|
S0SfSdS18A1M0A1S66S3fS6aZ2M1A1S1fS3fG1A2A3SeG0S55A2A3"). Proof. Time vmr. Qed.
Lemma HchkD_L0Bf_2 : ltac2:(tb__ "0|1|
S0S9S68S3fS6aZ2M0A1S1fS3fG0A2S55SaS4S6bG0A1SbS4A1A3A5ScA3"). Proof. Time vmr. Qed.
Lemma AXDr_L0Bf_2 : ltac2:(tb__ "0|0|
S0SfS4A1S64S5dS2eA2SeS4S57A2A3"). Proof. Time vmr. Qed.
Lemma ENTD_L0Bf_2 : ltac2:(tb__ "0|0|
S0S9S75S57S3dA2ScA3"). Proof. Time vmr. Qed.
Lemma RUN3_L0Bf : ltac2:(tb__ "0|0|
S0SdS6A1S35S1cSaS2S25SaS2S20SbS2A1A3A3S3dA3S47A3"). Proof. unfold run3_L0Bf; reflexivity. Qed.
Lemma L3_L0Bf : ltac2:(tb__ "0|0|
S1S0S9S1eS47SaS2S25SaS2S20SbS2A1A3A3A2ScA3S1S0S4S36U0S47A2S42A3S0S4S36U1S47A2S5aA3A2A2"). Proof. Time (split; [vmr | split; [unfold Eps_L0Bf | unfold Ebg_L0Bf]; reflexivity]). Qed.
Lemma NX3_L0Bf : ltac2:(tb__ "0|1|
S1S0S9S63S61S13S5S3dA1M0A1A2ScA3S0S9S16G0A1S10A3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma D3_L0Bf : ltac2:(tb__ "0|3|
S0SfS11SdS11S14S14A2A1M0SdS15A1M1A2M2A1S65S5S42A1S5S3cA1A2SeG2S12G0G1S33SbS15A1A4A2A3"). Proof. Time vmr. Qed.
Lemma EQ3_L0Bf : ltac2:(tb__ "0|0|
S0S4S7S42S5S3cA1A2S3cA3"). Proof. vmr. Qed.
Lemma NX3b_L0Bf : ltac2:(tb__ "0|0|
S0S9S63S61S13S5S3cA1A1A2ScA3"). Proof. vmr. Qed.
Lemma W3_L0Bf : ltac2:(tb__ "0|1|
S1S0S9S1aS5S3cA1M0A1ScA3S1S0S3S13G0A1S13S5S42A1A1A3S0S9S16G0A1S10A3A2A2"). Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma RUN4_L0Bf : ltac2:(tb__ "0|0|
S0SdS6A1S35S1cSaS2S24SbS2A1A3S3cA3S4fA3"). Proof. unfold run4_L0Bf; reflexivity. Qed.
Lemma L4_L0Bf : ltac2:(tb__ "0|0|
S1S0S9S1eS4fSaS2S24SbS2A1A3A2ScA3S0S4S36U0S4fA2S41A3A2"). Proof. Time (split; [vmr | unfold Ems_L0Bf; reflexivity]). Qed.
Lemma D4_L0Bf : ltac2:(tb__ "0|3|
S0SfS11SdS11S14S14A2A1M0SdS15A1M1A2M2A1S65S5S41A1S5S37A1A2SeG2S12G0G1S34SbS15A1A4A2A3"). Proof. Time vmr. Qed.
Lemma EQ4_L0Bf : ltac2:(tb__ "0|0|
S0S4S7S41S5S37A1A2S37A3"). Proof. vmr. Qed.
Lemma W4_L0Bf : ltac2:(tb__ "0|1|
S1S0S9S1aS5S37A1M0A1ScA3S1S0S3S13G0A1S13S5S41A1A1A3S0S9S16G0A1S10A3A2A2"). Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma HeM_L0Bf : ltac2:(tb__ "0|1|
S0SfSdS18A1M0A1S66S37S6dS28S37A1A3SeG0S49A2A3"). Proof. Time vmr. Qed.
Lemma HchkM_L0Bf : ltac2:(tb__ "0|0|
S0S9S67S37S6dS28S37A1S49S73S6S4S8S6eA4A5ScA3"). Proof. Time vmr. Qed.
Lemma HTM_L0Bf : ltac2:(tb__ "0|0|
S0S4S69S28S37A1S6dS31S37S49A5S4bA3"). Proof. unfold TM0_L0Bf, TM0_of, RM_L0Bf; reflexivity. Qed.
Lemma FBM_L0Bf : ltac2:(tb__ "0|3|
S1S0S9S6cS15S19S13S5S37A1M0A1M1A1S17G0A1M2A3ScA3S1S0S9S6cS15S19S13S5S4bA1A1A1G2A3ScA3S0S9S63S61G1A2ScA3A2A2").
Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma ETM_L0Bf : ltac2:(tb__ "0|0|
S0S4S74S4bS17S5S37A1A1A2S45A3"). Proof. vmr. Qed.
Lemma NX5_L0Bf : ltac2:(tb__ "0|1|
S1S0S9S63S61S13S5S45A1M0A1A2ScA3S0S9S16G0A1S10A3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma RUN5_L0Bf : ltac2:(tb__ "0|0|
S0SdS6A1S35S1cSaS2S23SbS2A1A3S45A3S50A3"). Proof. unfold run5_L0Bf; reflexivity. Qed.
Lemma L5_L0Bf : ltac2:(tb__ "0|0|
S1S0S9S1eS50SaS2S23SbS2A1A3A2ScA3S0S4S36U0S50A2S53A3A2"). Proof. Time (split; [vmr | unfold Eq_L0Bf; reflexivity]). Qed.
Lemma AXQ_L0Bf : ltac2:(tb__ "0|0|
S0SfS4A1S64S53S32A2SeS4S38A2A3"). Proof. Time vmr. Qed.
Lemma HeQ_L0Bf : ltac2:(tb__ "0|1|
S0SfSdS18A1M0A1S66S38S26S39A1S29S38S39A2A3SeG0S4aA2A3"). Proof. Time vmr. Qed.
Lemma HchkQ_L0Bf : ltac2:(tb__ "0|0|
S0S9S67S38S26S39A1S29S38S39A2S4aSaS4S2bS39A1SbS4A1A3A5ScA3"). Proof. Time vmr. Qed.
Lemma HTQ_L0Bf : ltac2:(tb__ "0|0|
S0S4S69S29S38S39A2S26S39A1S2bS39A1S38S4aA5S4cA3"). Proof. unfold TQ0_L0Bf, TQ0_of, RQ_L0Bf; reflexivity. Qed.
Lemma FBQ_L0Bf : ltac2:(tb__ "0|3|
S1S0S9S6cS15S19S13S5S38A1M0A1M1A1S17G0A1M2A3ScA3S1S0S9S6cS15S19S13S5S4cA1A1A1G2A3ScA3S0S9S63S61G1A2ScA3A2A2").
Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma ETQ_L0Bf : ltac2:(tb__ "0|0|
S0S4S74S4cS17S5S38A1A1A2S46A3"). Proof. vmr. Qed.
Lemma NX6_L0Bf : ltac2:(tb__ "0|1|
S1S0S9S63S61S13S5S46A1M0A1A2ScA3S0S9S16G0A1S10A3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma RUN6_L0Bf : ltac2:(tb__ "0|0|
S0SdS6A1S35S1cSaS2S22SaS2S27SbS2A1A3A3S46A3S48A3"). Proof. unfold run6_L0Bf; reflexivity. Qed.
Lemma L6_L0Bf : ltac2:(tb__ "0|0|
S1S0S9S1eS48SaS2S22SaS2S27SbS2A1A3A3A2ScA3S1S0S4S36U0S48A2S5bA3S0S4S36U1S48A2S5fA3A2A2"). Proof. Time (split; [vmr | split; [unfold Edr_L0Bf | unfold Xf_L0Bf]; reflexivity]). Qed.

End F0A_cL0Bf.

(* [comment removed for export] *)
Module F0A_cL0Be.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "leafA"; "ax_setS"; "la_state"; "@Corelib.Init.Datatypes"; "bool"; "cons"; "nil"; "true"; "list"; "Some"; "option"; "false"; "prod"; "pair"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "ss_next"; "sv"; "sprop"; "ss_lenient"; "ss_facts"; "sobj"; "sprop_below"; "swf"; "SLit"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states"; "FUELF"; "DEPE"; "leaves_at"; "sD_of"; "BIGX"; "CASX"; "DRNE"; "ENQE"; "MSE"; "PSE"; "PreQ1"; "RETF"; "sM_of"; "sQ_of"; "F_typ"; "PostQ1"; "S1c_of"; "XD"; "XDr"; "casx"; "vH3"; "PostMS"; "XQ"; "d3F"; "d4F"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states"; "runA"; "leaf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ie.F0A_cL0Be"; "C4_L0Be"; "EQ_L0Be"; "q_L0Be"; "C2_L0Be_1"; "C2_L0Be_2"; "C3_L0Be"; "CD_L0Be"; "ED_L0Be_1"; "ED_L0Be_2"; "P0_L0Be"; "Ems_L0Be"; "Eps_L0Be"; "S1c_L0Be_1"; "S1c_L0Be_2"; "TM_L0Be"; "TQ_L0Be"; "run3_L0Be"; "run6_L0Be"; "RM_L0Be"; "RQ_L0Be"; "TM0_L0Be"; "TQ0_L0Be"; "run2_L0Be_1"; "run2_L0Be_2"; "run4_L0Be"; "run5_L0Be"; "EfD_L0Be_1"; "EfD_L0Be_2"; "Eq_L0Be"; "RD_L0Be_1"; "RD_L0Be_2"; "TDr_L0Be_1"; "TDr_L0Be_2"; "exits1_L0Be"; "run1_L0Be"; "Ebg_L0Be"; "Edr_L0Be"; "TD_L0Be_1"; "TD_L0Be_2"; "W_L0Be"; "Xf_L0Be"; "st_L0Be"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "segsA"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "entails_frA"; "call_checkA"; "call_checkPA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states"; "PreD"; "PostD"; "@Stdlib.Lists.List"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset"; "Pre_memsetA"; "Posts_memsetA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_cfgA"; "check_ecfgA"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib"; "entsI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls"; "P0_fc"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame SymCFG SymCall SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA EntailA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import ObjXform ObjUnbase MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.
Import ListNotations.
Open Scope Z_scope.

Definition W_L0Be : list ulink := Wcan 0.
Definition st_L0Be : ustop := UStopLe.
Definition q_L0Be : qvar := QBe.
Definition P0_L0Be : axst := ltac2:(tb__ "0|0|
S76S10S5eS60S39A4").

Definition run1_L0Be : list leafA := ltac2:(tb__ "0|0|
S35S1cSaS2S21SbS2A1A3S40A3").

Definition S1c_L0Be_1 : axst := ltac2:(tb__ "0|0|
S2cS36U0S59A2S17S5S40A1A1Z1A3").
Definition C2_L0Be_1 : axst := C2_of S1c_L0Be_1.
Definition run2_L0Be_1 : list leafA := ltac2:(tb__ "0|0|
S35S1cSaS2S1dSbS2A1A3S3aA3").
Definition EfD_L0Be_1 : axst := leaf 0 run2_L0Be_1.
Definition ED_L0Be_1 : axst := ED_of EfD_L0Be_1.
Definition RD_L0Be_1 : list sobj := RD_of ED_L0Be_1 1.
Definition TD_L0Be_1 : axst := TD_of ED_L0Be_1 1.
Definition TDr_L0Be_1 : axst := TDr_of TD_L0Be_1.
Definition S1c_L0Be_2 : axst := ltac2:(tb__ "0|0|
S2cS36U0S59A2S17S5S40A1A1Z2A3").
Definition C2_L0Be_2 : axst := C2_of S1c_L0Be_2.
Definition run2_L0Be_2 : list leafA := ltac2:(tb__ "0|0|
S35S1cSaS2S1dSbS2A1A3S3bA3").
Definition EfD_L0Be_2 : axst := leaf 0 run2_L0Be_2.
Definition ED_L0Be_2 : axst := ED_of EfD_L0Be_2.
Definition RD_L0Be_2 : list sobj := RD_of ED_L0Be_2 2.
Definition TD_L0Be_2 : axst := TD_of ED_L0Be_2 2.
Definition TDr_L0Be_2 : axst := TDr_of TD_L0Be_2.
Definition exits1_L0Be : list axst := ltac2:(tb__ "0|0|
SaS4S43SaS4S44SbS4A1A3A3").

Definition CD_L0Be : axst := CD_of TDr_L0Be_1.
Definition run3_L0Be : list leafA := ltac2:(tb__ "0|0|
S35S1cSaS2S25SaS2S20SbS2A1A3A3S3dA3").
Definition Eps_L0Be : axst := leaf 0 run3_L0Be.
Definition Ebg_L0Be : axst := leaf 1 run3_L0Be.
Definition C3_L0Be : axst := C3_of Eps_L0Be.
Definition run4_L0Be : list leafA := ltac2:(tb__ "0|0|
S35S1cSaS2S24SbS2A1A3S3cA3").
Definition Ems_L0Be : axst := leaf 0 run4_L0Be.
Definition C4_L0Be : axst := C4_of Ems_L0Be.
Definition RM_L0Be : list sobj := RM_of C4_L0Be.
Definition TM0_L0Be : axst := TM0_of C4_L0Be.
Definition TM_L0Be : axst := TM_of C4_L0Be.
Definition run5_L0Be : list leafA := ltac2:(tb__ "0|0|
S35S1cSaS2S23SbS2A1A3S45A3").
Definition Eq_L0Be : axst := leaf 0 run5_L0Be.
Definition EQ_L0Be : axst := EQ_of Eq_L0Be.
Definition RQ_L0Be : list sobj := RQ_of EQ_L0Be q_L0Be.
Definition TQ0_L0Be : axst := TQ0_of EQ_L0Be q_L0Be.
Definition TQ_L0Be : axst := TQ_of EQ_L0Be q_L0Be.
Definition run6_L0Be : list leafA := ltac2:(tb__ "0|0|
S35S1cSaS2S22SaS2S27SbS2A1A3A3S46A3").
Definition Edr_L0Be : axst := leaf 0 run6_L0Be.
Definition Xf_L0Be : axst := leaf 1 run6_L0Be.

Ltac vmr := match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end.
Lemma Cert1_L0Be : ltac2:(tb__ "0|0|
S0S9S71S62S1cSaS2S21SbS2A1A3S61SaS4S40SbS4A1A3S58A6ScA3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runl segsA FUELF [CASX] GW P0_L0Be exits1_L0Be run1_L0Be); [unfold run1_L0Be, runA, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.runlA; reflexivity | vmr]. Qed.
Lemma ECert1_L0Be : ltac2:(tb__ "0|2|
S0S9S72S62S1cSaS2S21SbS2A1A3S61SaS6fS70S40Z1S1bZ0M0A1M1A3SbS6fA1A3S73S4S6fS4S70R1G0G1A3LE;S58A4A6ScA3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runl segsA FUELF [CASX] GW (mkVNA P0_L0Be 1 (SLit 0)) (map (fun E => mkVNA E 0 (SLit 0)) exits1_L0Be) run1_L0Be); [unfold run1_L0Be, runA, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.runlA; reflexivity | vmr]. Qed.

Lemma D2_L0Be_1 : ltac2:(tb__ "0|4|
S0SfS11SdS11S14S14A2M0A1M1SdS15A1M2A2M3A1S65S5S43A1S5S3aA1A2SeG3S12G1G2SaG0S12S14S14S2fS30A4SbG0A1A3S2aA4A2A3"). Proof. Time vmr. Qed.
Lemma W2_L0Be_1 : ltac2:(tb__ "0|1|
S1S0S9S1aS5S3aA1M0A1ScA3S1S0S3S13G0A1S13S5S43A1A1A3S0S9S16G0A1S10A3A2A2"). Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma NX2_L0Be_1 : ltac2:(tb__ "0|0|
S0S9S63S61S13S5S3aA1A1A2ScA3"). Proof. vmr. Qed.
Lemma EQ2_L0Be_1 : ltac2:(tb__ "0|0|
S0S4S7S43S5S3aA1A2S3aA3"). Proof. vmr. Qed.
Lemma RUN2_L0Be_1 : ltac2:(tb__ "0|0|
S0SdS6A1S35S1cSaS2S1dSbS2A1A3S3aA3S4dA3"). Proof. unfold run2_L0Be_1; reflexivity. Qed.
Lemma L2_L0Be_1 : ltac2:(tb__ "0|0|
S1S0S9S1eS4dSaS2S1dSbS2A1A3A2ScA3S0S4S36U0S4dA2S51A3A2"). Proof. Time (split; [vmr | unfold EfD_L0Be_1; reflexivity]). Qed.
Lemma AXD_L0Be_1 : ltac2:(tb__ "0|0|
S0SfS4A1S64S51S2dA2SeS4S3eA2A3"). Proof. Time vmr. Qed.
Lemma HeD_L0Be_1 : ltac2:(tb__ "0|2|
S0SfSdS18A1M0A1S66S3eS6aZ1M1A1S1fS3eG1A2A3SeG0S54A2A3"). Proof. Time vmr. Qed.
Lemma HchkD_L0Be_1 : ltac2:(tb__ "0|1|
S0S9S68S3eS6aZ1M0A1S1fS3eG0A2S54SaS4S6bG0A1SbS4A1A3A5ScA3"). Proof. Time vmr. Qed.
Lemma AXDr_L0Be_1 : ltac2:(tb__ "0|0|
S0SfS4A1S64S5cS2eA2SeS4S56A2A3"). Proof. Time vmr. Qed.
Lemma ENTD_L0Be_1 : ltac2:(tb__ "0|0|
S0S9S75S56S3dA2ScA3"). Proof. Time vmr. Qed.
Lemma D2_L0Be_2 : ltac2:(tb__ "0|4|
S0SfS11SdS11S14S14A2M0A1M1SdS15A1M2A2M3A1S65S5S44A1S5S3bA1A2SeG3S12G1G2SaG0S12S14S14S2fS30A4SbG0A1A3S2aA4A2A3"). Proof. Time vmr. Qed.
Lemma W2_L0Be_2 : ltac2:(tb__ "0|1|
S1S0S9S1aS5S3bA1M0A1ScA3S1S0S3S13G0A1S13S5S44A1A1A3S0S9S16G0A1S10A3A2A2"). Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma NX2_L0Be_2 : ltac2:(tb__ "0|0|
S0S9S63S61S13S5S3bA1A1A2ScA3"). Proof. vmr. Qed.
Lemma EQ2_L0Be_2 : ltac2:(tb__ "0|0|
S0S4S7S44S5S3bA1A2S3bA3"). Proof. vmr. Qed.
Lemma RUN2_L0Be_2 : ltac2:(tb__ "0|0|
S0SdS6A1S35S1cSaS2S1dSbS2A1A3S3bA3S4eA3"). Proof. unfold run2_L0Be_2; reflexivity. Qed.
Lemma L2_L0Be_2 : ltac2:(tb__ "0|0|
S1S0S9S1eS4eSaS2S1dSbS2A1A3A2ScA3S0S4S36U0S4eA2S52A3A2"). Proof. Time (split; [vmr | unfold EfD_L0Be_2; reflexivity]). Qed.
Lemma AXD_L0Be_2 : ltac2:(tb__ "0|0|
S0SfS4A1S64S52S2dA2SeS4S3fA2A3"). Proof. Time vmr. Qed.
Lemma HeD_L0Be_2 : ltac2:(tb__ "0|2|
S0SfSdS18A1M0A1S66S3fS6aZ2M1A1S1fS3fG1A2A3SeG0S55A2A3"). Proof. Time vmr. Qed.
Lemma HchkD_L0Be_2 : ltac2:(tb__ "0|1|
S0S9S68S3fS6aZ2M0A1S1fS3fG0A2S55SaS4S6bG0A1SbS4A1A3A5ScA3"). Proof. Time vmr. Qed.
Lemma AXDr_L0Be_2 : ltac2:(tb__ "0|0|
S0SfS4A1S64S5dS2eA2SeS4S57A2A3"). Proof. Time vmr. Qed.
Lemma ENTD_L0Be_2 : ltac2:(tb__ "0|0|
S0S9S75S57S3dA2ScA3"). Proof. Time vmr. Qed.
Lemma RUN3_L0Be : ltac2:(tb__ "0|0|
S0SdS6A1S35S1cSaS2S25SaS2S20SbS2A1A3A3S3dA3S47A3"). Proof. unfold run3_L0Be; reflexivity. Qed.
Lemma L3_L0Be : ltac2:(tb__ "0|0|
S1S0S9S1eS47SaS2S25SaS2S20SbS2A1A3A3A2ScA3S1S0S4S36U0S47A2S42A3S0S4S36U1S47A2S5aA3A2A2"). Proof. Time (split; [vmr | split; [unfold Eps_L0Be | unfold Ebg_L0Be]; reflexivity]). Qed.
Lemma NX3_L0Be : ltac2:(tb__ "0|1|
S1S0S9S63S61S13S5S3dA1M0A1A2ScA3S0S9S16G0A1S10A3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma D3_L0Be : ltac2:(tb__ "0|3|
S0SfS11SdS11S14S14A2A1M0SdS15A1M1A2M2A1S65S5S42A1S5S3cA1A2SeG2S12G0G1S33SbS15A1A4A2A3"). Proof. Time vmr. Qed.
Lemma EQ3_L0Be : ltac2:(tb__ "0|0|
S0S4S7S42S5S3cA1A2S3cA3"). Proof. vmr. Qed.
Lemma NX3b_L0Be : ltac2:(tb__ "0|0|
S0S9S63S61S13S5S3cA1A1A2ScA3"). Proof. vmr. Qed.
Lemma W3_L0Be : ltac2:(tb__ "0|1|
S1S0S9S1aS5S3cA1M0A1ScA3S1S0S3S13G0A1S13S5S42A1A1A3S0S9S16G0A1S10A3A2A2"). Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma RUN4_L0Be : ltac2:(tb__ "0|0|
S0SdS6A1S35S1cSaS2S24SbS2A1A3S3cA3S4fA3"). Proof. unfold run4_L0Be; reflexivity. Qed.
Lemma L4_L0Be : ltac2:(tb__ "0|0|
S1S0S9S1eS4fSaS2S24SbS2A1A3A2ScA3S0S4S36U0S4fA2S41A3A2"). Proof. Time (split; [vmr | unfold Ems_L0Be; reflexivity]). Qed.
Lemma D4_L0Be : ltac2:(tb__ "0|3|
S0SfS11SdS11S14S14A2A1M0SdS15A1M1A2M2A1S65S5S41A1S5S37A1A2SeG2S12G0G1S34SbS15A1A4A2A3"). Proof. Time vmr. Qed.
Lemma EQ4_L0Be : ltac2:(tb__ "0|0|
S0S4S7S41S5S37A1A2S37A3"). Proof. vmr. Qed.
Lemma W4_L0Be : ltac2:(tb__ "0|1|
S1S0S9S1aS5S37A1M0A1ScA3S1S0S3S13G0A1S13S5S41A1A1A3S0S9S16G0A1S10A3A2A2"). Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma HeM_L0Be : ltac2:(tb__ "0|1|
S0SfSdS18A1M0A1S66S37S6dS28S37A1A3SeG0S49A2A3"). Proof. Time vmr. Qed.
Lemma HchkM_L0Be : ltac2:(tb__ "0|0|
S0S9S67S37S6dS28S37A1S49S73S6S4S8S6eA4A5ScA3"). Proof. Time vmr. Qed.
Lemma HTM_L0Be : ltac2:(tb__ "0|0|
S0S4S69S28S37A1S6dS31S37S49A5S4bA3"). Proof. unfold TM0_L0Be, TM0_of, RM_L0Be; reflexivity. Qed.
Lemma FBM_L0Be : ltac2:(tb__ "0|3|
S1S0S9S6cS15S19S13S5S37A1M0A1M1A1S17G0A1M2A3ScA3S1S0S9S6cS15S19S13S5S4bA1A1A1G2A3ScA3S0S9S63S61G1A2ScA3A2A2").
Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma ETM_L0Be : ltac2:(tb__ "0|0|
S0S4S74S4bS17S5S37A1A1A2S45A3"). Proof. vmr. Qed.
Lemma NX5_L0Be : ltac2:(tb__ "0|1|
S1S0S9S63S61S13S5S45A1M0A1A2ScA3S0S9S16G0A1S10A3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma RUN5_L0Be : ltac2:(tb__ "0|0|
S0SdS6A1S35S1cSaS2S23SbS2A1A3S45A3S50A3"). Proof. unfold run5_L0Be; reflexivity. Qed.
Lemma L5_L0Be : ltac2:(tb__ "0|0|
S1S0S9S1eS50SaS2S23SbS2A1A3A2ScA3S0S4S36U0S50A2S53A3A2"). Proof. Time (split; [vmr | unfold Eq_L0Be; reflexivity]). Qed.
Lemma AXQ_L0Be : ltac2:(tb__ "0|0|
S0SfS4A1S64S53S32A2SeS4S38A2A3"). Proof. Time vmr. Qed.
Lemma HeQ_L0Be : ltac2:(tb__ "0|1|
S0SfSdS18A1M0A1S66S38S26S39A1S29S38S39A2A3SeG0S4aA2A3"). Proof. Time vmr. Qed.
Lemma HchkQ_L0Be : ltac2:(tb__ "0|0|
S0S9S67S38S26S39A1S29S38S39A2S4aSaS4S2bS39A1SbS4A1A3A5ScA3"). Proof. Time vmr. Qed.
Lemma HTQ_L0Be : ltac2:(tb__ "0|0|
S0S4S69S29S38S39A2S26S39A1S2bS39A1S38S4aA5S4cA3"). Proof. unfold TQ0_L0Be, TQ0_of, RQ_L0Be; reflexivity. Qed.
Lemma FBQ_L0Be : ltac2:(tb__ "0|3|
S1S0S9S6cS15S19S13S5S38A1M0A1M1A1S17G0A1M2A3ScA3S1S0S9S6cS15S19S13S5S4cA1A1A1G2A3ScA3S0S9S63S61G1A2ScA3A2A2").
Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma ETQ_L0Be : ltac2:(tb__ "0|0|
S0S4S74S4cS17S5S38A1A1A2S46A3"). Proof. vmr. Qed.
Lemma NX6_L0Be : ltac2:(tb__ "0|1|
S1S0S9S63S61S13S5S46A1M0A1A2ScA3S0S9S16G0A1S10A3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma RUN6_L0Be : ltac2:(tb__ "0|0|
S0SdS6A1S35S1cSaS2S22SaS2S27SbS2A1A3A3S46A3S48A3"). Proof. unfold run6_L0Be; reflexivity. Qed.
Lemma L6_L0Be : ltac2:(tb__ "0|0|
S1S0S9S1eS48SaS2S22SaS2S27SbS2A1A3A3A2ScA3S1S0S4S36U0S48A2S5bA3S0S4S36U1S48A2S5fA3A2A2"). Proof. Time (split; [vmr | split; [unfold Edr_L0Be | unfold Xf_L0Be]; reflexivity]). Qed.

End F0A_cL0Be.

(* [comment removed for export] *)
Module F0A_cL1A.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "leafA"; "ax_setS"; "la_state"; "@Corelib.Init.Datatypes"; "bool"; "cons"; "nil"; "true"; "list"; "Some"; "option"; "prod"; "false"; "pair"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "ss_next"; "sv"; "sprop"; "ss_lenient"; "ss_facts"; "sobj"; "swf"; "sprop_below"; "SLit"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states"; "FUELF"; "DEPE"; "leaves_at"; "sD_of"; "BIGX"; "CASX"; "DRNE"; "ENQE"; "F_typ"; "MSE"; "PSE"; "PreQ1"; "RETF"; "S1c_of"; "XD"; "XDr"; "casx"; "sM_of"; "sQ_of"; "vH3"; "PostQ1"; "PostMS"; "XQ"; "d3F"; "d4F"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states"; "runA"; "leaf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ie.F0A_cL1A"; "C4_L1A"; "EQ_L1A"; "q_L1A"; "C2_L1A_1"; "C2_L1A_2"; "C2_L1A_3"; "C3_L1A"; "CD_L1A"; "P0_L1A"; "ED_L1A_1"; "ED_L1A_2"; "ED_L1A_3"; "Ems_L1A"; "Eps_L1A"; "S1c_L1A_1"; "S1c_L1A_2"; "S1c_L1A_3"; "TM_L1A"; "TQ_L1A"; "run3_L1A"; "run6_L1A"; "RM_L1A"; "RQ_L1A"; "TM0_L1A"; "TQ0_L1A"; "run1_L1A"; "run2_L1A_1"; "run2_L1A_2"; "run2_L1A_3"; "run4_L1A"; "run5_L1A"; "EfD_L1A_1"; "EfD_L1A_2"; "EfD_L1A_3"; "Eq_L1A"; "RD_L1A_1"; "RD_L1A_2"; "RD_L1A_3"; "TDr_L1A_1"; "TDr_L1A_2"; "TDr_L1A_3"; "exits1_L1A"; "Ebg_L1A"; "Edr_L1A"; "TD_L1A_1"; "TD_L1A_2"; "TD_L1A_3"; "W_L1A"; "Xf_L1A"; "st_L1A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "segsA"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states"; "PreD"; "PostD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "entails_frA"; "call_checkPA"; "call_checkA"; "import_postA"; "@Stdlib.Lists.List"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset"; "Pre_memsetA"; "Posts_memsetA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_cfgA"; "check_ecfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib"; "entsI"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls"; "P0_fc"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame SymCFG SymCall SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA EntailA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import ObjXform ObjUnbase MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.
Import ListNotations.
Open Scope Z_scope.

Definition W_L1A : list ulink := Wcan 1.
Definition st_L1A : ustop := UStopLe.
Definition q_L1A : qvar := QA.
Definition P0_L1A : axst := ltac2:(tb__ "0|0|
S7eS11S66S68S39A4").

Definition run1_L1A : list leafA := ltac2:(tb__ "0|0|
S35S1cSaS2S21SbS2A1A3S3fA3").

Definition S1c_L1A_1 : axst := ltac2:(tb__ "0|0|
S29S36U0S50A2S17S5S3fA1A1Z1A3").
Definition C2_L1A_1 : axst := C2_of S1c_L1A_1.
Definition run2_L1A_1 : list leafA := ltac2:(tb__ "0|0|
S35S1cSaS2S1dSbS2A1A3S3aA3").
Definition EfD_L1A_1 : axst := leaf 0 run2_L1A_1.
Definition ED_L1A_1 : axst := ED_of EfD_L1A_1.
Definition RD_L1A_1 : list sobj := RD_of ED_L1A_1 1.
Definition TD_L1A_1 : axst := TD_of ED_L1A_1 1.
Definition TDr_L1A_1 : axst := TDr_of TD_L1A_1.
Definition S1c_L1A_2 : axst := ltac2:(tb__ "0|0|
S29S36U0S50A2S17S5S3fA1A1Z2A3").
Definition C2_L1A_2 : axst := C2_of S1c_L1A_2.
Definition run2_L1A_2 : list leafA := ltac2:(tb__ "0|0|
S35S1cSaS2S1dSbS2A1A3S3bA3").
Definition EfD_L1A_2 : axst := leaf 0 run2_L1A_2.
Definition ED_L1A_2 : axst := ED_of EfD_L1A_2.
Definition RD_L1A_2 : list sobj := RD_of ED_L1A_2 2.
Definition TD_L1A_2 : axst := TD_of ED_L1A_2 2.
Definition TDr_L1A_2 : axst := TDr_of TD_L1A_2.
Definition S1c_L1A_3 : axst := ltac2:(tb__ "0|0|
S29S36U0S50A2S17S5S3fA1A1Z3A3").
Definition C2_L1A_3 : axst := C2_of S1c_L1A_3.
Definition run2_L1A_3 : list leafA := ltac2:(tb__ "0|0|
S35S1cSaS2S1dSbS2A1A3S3cA3").
Definition EfD_L1A_3 : axst := leaf 0 run2_L1A_3.
Definition ED_L1A_3 : axst := ED_of EfD_L1A_3.
Definition RD_L1A_3 : list sobj := RD_of ED_L1A_3 3.
Definition TD_L1A_3 : axst := TD_of ED_L1A_3 3.
Definition TDr_L1A_3 : axst := TDr_of TD_L1A_3.
Definition exits1_L1A : list axst := ltac2:(tb__ "0|0|
SaS4S45SaS4S46SaS4S47SbS4A1A3A3A3").

Definition CD_L1A : axst := CD_of TDr_L1A_1.
Definition run3_L1A : list leafA := ltac2:(tb__ "0|0|
S35S1cSaS2S26SaS2S20SbS2A1A3A3S3eA3").
Definition Eps_L1A : axst := leaf 0 run3_L1A.
Definition Ebg_L1A : axst := leaf 1 run3_L1A.
Definition C3_L1A : axst := C3_of Eps_L1A.
Definition run4_L1A : list leafA := ltac2:(tb__ "0|0|
S35S1cSaS2S25SbS2A1A3S3dA3").
Definition Ems_L1A : axst := leaf 0 run4_L1A.
Definition C4_L1A : axst := C4_of Ems_L1A.
Definition RM_L1A : list sobj := RM_of C4_L1A.
Definition TM0_L1A : axst := TM0_of C4_L1A.
Definition TM_L1A : axst := TM_of C4_L1A.
Definition run5_L1A : list leafA := ltac2:(tb__ "0|0|
S35S1cSaS2S23SbS2A1A3S48A3").
Definition Eq_L1A : axst := leaf 0 run5_L1A.
Definition EQ_L1A : axst := EQ_of Eq_L1A.
Definition RQ_L1A : list sobj := RQ_of EQ_L1A q_L1A.
Definition TQ0_L1A : axst := TQ0_of EQ_L1A q_L1A.
Definition TQ_L1A : axst := TQ_of EQ_L1A q_L1A.
Definition run6_L1A : list leafA := ltac2:(tb__ "0|0|
S35S1cSaS2S22SaS2S28SbS2A1A3A3S49A3").
Definition Edr_L1A : axst := leaf 0 run6_L1A.
Definition Xf_L1A : axst := leaf 1 run6_L1A.

Ltac vmr := match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end.
Lemma Cert1_L1A : ltac2:(tb__ "0|0|
S0S9S79S6aS1cSaS2S21SbS2A1A3S69SaS4S3fSbS4A1A3S60A6ScA3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runl segsA FUELF [CASX] GW P0_L1A exits1_L1A run1_L1A); [unfold run1_L1A, runA, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.runlA; reflexivity | vmr]. Qed.
Lemma ECert1_L1A : ltac2:(tb__ "0|2|
S0S9S7aS6aS1cSaS2S21SbS2A1A3S69SaS77S78S3fZ1S1bZ0M0A1M1A3SbS77A1A3S7cS4S77S4S78R1G0G1A3LE;S60A4A6ScA3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runl segsA FUELF [CASX] GW (mkVNA P0_L1A 1 (SLit 0)) (map (fun E => mkVNA E 0 (SLit 0)) exits1_L1A) run1_L1A); [unfold run1_L1A, runA, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.runlA; reflexivity | vmr]. Qed.

Lemma D2_L1A_1 : ltac2:(tb__ "0|4|
S0SfS10SdS10S14S14A2M0A1M1SdS15A1M2A2M3A1S6fS5S45A1S5S3aA1A2SeG3S12G1G2SaG0S12S14S14S2cS2fA4SbG0A1A3S24A4A2A3"). Proof. Time vmr. Qed.
Lemma W2_L1A_1 : ltac2:(tb__ "0|1|
S1S0S9S19S5S3aA1M0A1ScA3S1S0S3S13G0A1S13S5S45A1A1A3S0S9S16G0A1S11A3A2A2"). Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma NX2_L1A_1 : ltac2:(tb__ "0|0|
S0S9S6bS69S13S5S3aA1A1A2ScA3"). Proof. vmr. Qed.
Lemma EQ2_L1A_1 : ltac2:(tb__ "0|0|
S0S4S7S45S5S3aA1A2S3aA3"). Proof. vmr. Qed.
Lemma RUN2_L1A_1 : ltac2:(tb__ "0|0|
S0SdS6A1S35S1cSaS2S1dSbS2A1A3S3aA3S51A3"). Proof. unfold run2_L1A_1; reflexivity. Qed.
Lemma L2_L1A_1 : ltac2:(tb__ "0|0|
S1S0S9S1eS51SaS2S1dSbS2A1A3A2ScA3S0S4S36U0S51A2S56A3A2"). Proof. Time (split; [vmr | unfold EfD_L1A_1; reflexivity]). Qed.
Lemma AXD_L1A_1 : ltac2:(tb__ "0|0|
S0SfS4A1S6cS56S2aA2SeS4S40A2A3"). Proof. Time vmr. Qed.
Lemma HeD_L1A_1 : ltac2:(tb__ "0|2|
S0SfSdS18A1M0A1S70S40S6dZ1M1A1S1fS40G1A2A3SeG0S5aA2A3"). Proof. Time vmr. Qed.
Lemma HchkD_L1A_1 : ltac2:(tb__ "0|1|
S0S9S71S40S6dZ1M0A1S1fS40G0A2S5aSaS4S6eG0A1SbS4A1A3A5ScA3"). Proof. Time vmr. Qed.
Lemma AXDr_L1A_1 : ltac2:(tb__ "0|0|
S0SfS4A1S6cS63S2bA2SeS4S5dA2A3"). Proof. Time vmr. Qed.
Lemma ENTD_L1A_1 : ltac2:(tb__ "0|0|
S0S9S7bS5dS3eA2ScA3"). Proof. Time vmr. Qed.
Lemma D2_L1A_2 : ltac2:(tb__ "0|4|
S0SfS10SdS10S14S14A2M0A1M1SdS15A1M2A2M3A1S6fS5S46A1S5S3bA1A2SeG3S12G1G2SaG0S12S14S14S2cS2fA4SbG0A1A3S24A4A2A3"). Proof. Time vmr. Qed.
Lemma W2_L1A_2 : ltac2:(tb__ "0|1|
S1S0S9S19S5S3bA1M0A1ScA3S1S0S3S13G0A1S13S5S46A1A1A3S0S9S16G0A1S11A3A2A2"). Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma NX2_L1A_2 : ltac2:(tb__ "0|0|
S0S9S6bS69S13S5S3bA1A1A2ScA3"). Proof. vmr. Qed.
Lemma EQ2_L1A_2 : ltac2:(tb__ "0|0|
S0S4S7S46S5S3bA1A2S3bA3"). Proof. vmr. Qed.
Lemma RUN2_L1A_2 : ltac2:(tb__ "0|0|
S0SdS6A1S35S1cSaS2S1dSbS2A1A3S3bA3S52A3"). Proof. unfold run2_L1A_2; reflexivity. Qed.
Lemma L2_L1A_2 : ltac2:(tb__ "0|0|
S1S0S9S1eS52SaS2S1dSbS2A1A3A2ScA3S0S4S36U0S52A2S57A3A2"). Proof. Time (split; [vmr | unfold EfD_L1A_2; reflexivity]). Qed.
Lemma AXD_L1A_2 : ltac2:(tb__ "0|0|
S0SfS4A1S6cS57S2aA2SeS4S41A2A3"). Proof. Time vmr. Qed.
Lemma HeD_L1A_2 : ltac2:(tb__ "0|2|
S0SfSdS18A1M0A1S70S41S6dZ2M1A1S1fS41G1A2A3SeG0S5bA2A3"). Proof. Time vmr. Qed.
Lemma HchkD_L1A_2 : ltac2:(tb__ "0|1|
S0S9S71S41S6dZ2M0A1S1fS41G0A2S5bSaS4S6eG0A1SbS4A1A3A5ScA3"). Proof. Time vmr. Qed.
Lemma AXDr_L1A_2 : ltac2:(tb__ "0|0|
S0SfS4A1S6cS64S2bA2SeS4S5eA2A3"). Proof. Time vmr. Qed.
Lemma ENTD_L1A_2 : ltac2:(tb__ "0|0|
S0S9S7bS5eS3eA2ScA3"). Proof. Time vmr. Qed.
Lemma D2_L1A_3 : ltac2:(tb__ "0|4|
S0SfS10SdS10S14S14A2M0A1M1SdS15A1M2A2M3A1S6fS5S47A1S5S3cA1A2SeG3S12G1G2SaG0S12S14S14S2cS2fA4SbG0A1A3S24A4A2A3"). Proof. Time vmr. Qed.
Lemma W2_L1A_3 : ltac2:(tb__ "0|1|
S1S0S9S19S5S3cA1M0A1ScA3S1S0S3S13G0A1S13S5S47A1A1A3S0S9S16G0A1S11A3A2A2"). Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma NX2_L1A_3 : ltac2:(tb__ "0|0|
S0S9S6bS69S13S5S3cA1A1A2ScA3"). Proof. vmr. Qed.
Lemma EQ2_L1A_3 : ltac2:(tb__ "0|0|
S0S4S7S47S5S3cA1A2S3cA3"). Proof. vmr. Qed.
Lemma RUN2_L1A_3 : ltac2:(tb__ "0|0|
S0SdS6A1S35S1cSaS2S1dSbS2A1A3S3cA3S53A3"). Proof. unfold run2_L1A_3; reflexivity. Qed.
Lemma L2_L1A_3 : ltac2:(tb__ "0|0|
S1S0S9S1eS53SaS2S1dSbS2A1A3A2ScA3S0S4S36U0S53A2S58A3A2"). Proof. Time (split; [vmr | unfold EfD_L1A_3; reflexivity]). Qed.
Lemma AXD_L1A_3 : ltac2:(tb__ "0|0|
S0SfS4A1S6cS58S2aA2SeS4S42A2A3"). Proof. Time vmr. Qed.
Lemma HeD_L1A_3 : ltac2:(tb__ "0|2|
S0SfSdS18A1M0A1S70S42S6dZ3M1A1S1fS42G1A2A3SeG0S5cA2A3"). Proof. Time vmr. Qed.
Lemma HchkD_L1A_3 : ltac2:(tb__ "0|1|
S0S9S71S42S6dZ3M0A1S1fS42G0A2S5cSaS4S6eG0A1SbS4A1A3A5ScA3"). Proof. Time vmr. Qed.
Lemma AXDr_L1A_3 : ltac2:(tb__ "0|0|
S0SfS4A1S6cS65S2bA2SeS4S5fA2A3"). Proof. Time vmr. Qed.
Lemma ENTD_L1A_3 : ltac2:(tb__ "0|0|
S0S9S7bS5fS3eA2ScA3"). Proof. Time vmr. Qed.
Lemma RUN3_L1A : ltac2:(tb__ "0|0|
S0SdS6A1S35S1cSaS2S26SaS2S20SbS2A1A3A3S3eA3S4aA3"). Proof. unfold run3_L1A; reflexivity. Qed.
Lemma L3_L1A : ltac2:(tb__ "0|0|
S1S0S9S1eS4aSaS2S26SaS2S20SbS2A1A3A3A2ScA3S1S0S4S36U0S4aA2S44A3S0S4S36U1S4aA2S61A3A2A2"). Proof. Time (split; [vmr | split; [unfold Eps_L1A | unfold Ebg_L1A]; reflexivity]). Qed.
Lemma NX3_L1A : ltac2:(tb__ "0|1|
S1S0S9S6bS69S13S5S3eA1M0A1A2ScA3S0S9S16G0A1S11A3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma D3_L1A : ltac2:(tb__ "0|3|
S0SfS10SdS10S14S14A2A1M0SdS15A1M1A2M2A1S6fS5S44A1S5S3dA1A2SeG2S12G0G1S33SbS15A1A4A2A3"). Proof. Time vmr. Qed.
Lemma EQ3_L1A : ltac2:(tb__ "0|0|
S0S4S7S44S5S3dA1A2S3dA3"). Proof. vmr. Qed.
Lemma NX3b_L1A : ltac2:(tb__ "0|0|
S0S9S6bS69S13S5S3dA1A1A2ScA3"). Proof. vmr. Qed.
Lemma W3_L1A : ltac2:(tb__ "0|1|
S1S0S9S19S5S3dA1M0A1ScA3S1S0S3S13G0A1S13S5S44A1A1A3S0S9S16G0A1S11A3A2A2"). Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma RUN4_L1A : ltac2:(tb__ "0|0|
S0SdS6A1S35S1cSaS2S25SbS2A1A3S3dA3S54A3"). Proof. unfold run4_L1A; reflexivity. Qed.
Lemma L4_L1A : ltac2:(tb__ "0|0|
S1S0S9S1eS54SaS2S25SbS2A1A3A2ScA3S0S4S36U0S54A2S43A3A2"). Proof. Time (split; [vmr | unfold Ems_L1A; reflexivity]). Qed.
Lemma D4_L1A : ltac2:(tb__ "0|3|
S0SfS10SdS10S14S14A2A1M0SdS15A1M1A2M2A1S6fS5S43A1S5S37A1A2SeG2S12G0G1S34SbS15A1A4A2A3"). Proof. Time vmr. Qed.
Lemma EQ4_L1A : ltac2:(tb__ "0|0|
S0S4S7S43S5S37A1A2S37A3"). Proof. vmr. Qed.
Lemma W4_L1A : ltac2:(tb__ "0|1|
S1S0S9S19S5S37A1M0A1ScA3S1S0S3S13G0A1S13S5S43A1A1A3S0S9S16G0A1S11A3A2A2"). Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma HeM_L1A : ltac2:(tb__ "0|1|
S0SfSdS18A1M0A1S70S37S75S2dS37A1A3SeG0S4cA2A3"). Proof. Time vmr. Qed.
Lemma HchkM_L1A : ltac2:(tb__ "0|0|
S0S9S72S37S75S2dS37A1S4cS7cS6S4S8S76A4A5ScA3"). Proof. Time vmr. Qed.
Lemma HTM_L1A : ltac2:(tb__ "0|0|
S0S4S73S2dS37A1S75S31S37S4cA5S4eA3"). Proof. unfold TM0_L1A, TM0_of, RM_L1A; reflexivity. Qed.
Lemma FBM_L1A : ltac2:(tb__ "0|3|
S1S0S9S74S15S1aS13S5S37A1M0A1M1A1S17G0A1M2A3ScA3S1S0S9S74S15S1aS13S5S4eA1A1A1G2A3ScA3S0S9S6bS69G1A2ScA3A2A2").
Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma ETM_L1A : ltac2:(tb__ "0|0|
S0S4S7dS4eS17S5S37A1A1A2S48A3"). Proof. vmr. Qed.
Lemma NX5_L1A : ltac2:(tb__ "0|1|
S1S0S9S6bS69S13S5S48A1M0A1A2ScA3S0S9S16G0A1S11A3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma RUN5_L1A : ltac2:(tb__ "0|0|
S0SdS6A1S35S1cSaS2S23SbS2A1A3S48A3S55A3"). Proof. unfold run5_L1A; reflexivity. Qed.
Lemma L5_L1A : ltac2:(tb__ "0|0|
S1S0S9S1eS55SaS2S23SbS2A1A3A2ScA3S0S4S36U0S55A2S59A3A2"). Proof. Time (split; [vmr | unfold Eq_L1A; reflexivity]). Qed.
Lemma AXQ_L1A : ltac2:(tb__ "0|0|
S0SfS4A1S6cS59S32A2SeS4S38A2A3"). Proof. Time vmr. Qed.
Lemma HeQ_L1A : ltac2:(tb__ "0|1|
S0SfSdS18A1M0A1S70S38S27S39A1S2eS38S39A2A3SeG0S4dA2A3"). Proof. Time vmr. Qed.
Lemma HchkQ_L1A : ltac2:(tb__ "0|0|
S0S9S72S38S27S39A1S2eS38S39A2S4dSaS4S30S39A1SbS4A1A3A5ScA3"). Proof. Time vmr. Qed.
Lemma HTQ_L1A : ltac2:(tb__ "0|0|
S0S4S73S2eS38S39A2S27S39A1S30S39A1S38S4dA5S4fA3"). Proof. unfold TQ0_L1A, TQ0_of, RQ_L1A; reflexivity. Qed.
Lemma FBQ_L1A : ltac2:(tb__ "0|3|
S1S0S9S74S15S1aS13S5S38A1M0A1M1A1S17G0A1M2A3ScA3S1S0S9S74S15S1aS13S5S4fA1A1A1G2A3ScA3S0S9S6bS69G1A2ScA3A2A2").
Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma ETQ_L1A : ltac2:(tb__ "0|0|
S0S4S7dS4fS17S5S38A1A1A2S49A3"). Proof. vmr. Qed.
Lemma NX6_L1A : ltac2:(tb__ "0|1|
S1S0S9S6bS69S13S5S49A1M0A1A2ScA3S0S9S16G0A1S11A3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma RUN6_L1A : ltac2:(tb__ "0|0|
S0SdS6A1S35S1cSaS2S22SaS2S28SbS2A1A3A3S49A3S4bA3"). Proof. unfold run6_L1A; reflexivity. Qed.
Lemma L6_L1A : ltac2:(tb__ "0|0|
S1S0S9S1eS4bSaS2S22SaS2S28SbS2A1A3A3A2ScA3S1S0S4S36U0S4bA2S62A3S0S4S36U1S4bA2S67A3A2A2"). Proof. Time (split; [vmr | split; [unfold Edr_L1A | unfold Xf_L1A]; reflexivity]). Qed.

End F0A_cL1A.

(* [comment removed for export] *)
Module F0A_cL1Be.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "leafA"; "ax_setS"; "la_state"; "@Corelib.Init.Datatypes"; "bool"; "cons"; "nil"; "true"; "list"; "Some"; "option"; "prod"; "false"; "pair"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "ss_next"; "sv"; "sprop"; "ss_lenient"; "ss_facts"; "sobj"; "swf"; "sprop_below"; "SLit"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states"; "FUELF"; "DEPE"; "leaves_at"; "sD_of"; "BIGX"; "CASX"; "DRNE"; "ENQE"; "F_typ"; "MSE"; "PSE"; "PreQ1"; "RETF"; "S1c_of"; "XD"; "XDr"; "casx"; "sM_of"; "sQ_of"; "vH3"; "PostQ1"; "PostMS"; "XQ"; "d3F"; "d4F"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states"; "runA"; "leaf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ie.F0A_cL1Be"; "C4_L1Be"; "EQ_L1Be"; "q_L1Be"; "C2_L1Be_1"; "C2_L1Be_2"; "C2_L1Be_3"; "C3_L1Be"; "CD_L1Be"; "P0_L1Be"; "ED_L1Be_1"; "ED_L1Be_2"; "ED_L1Be_3"; "Ems_L1Be"; "Eps_L1Be"; "S1c_L1Be_1"; "S1c_L1Be_2"; "S1c_L1Be_3"; "TM_L1Be"; "TQ_L1Be"; "run3_L1Be"; "run6_L1Be"; "RM_L1Be"; "RQ_L1Be"; "TM0_L1Be"; "TQ0_L1Be"; "run1_L1Be"; "run2_L1Be_1"; "run2_L1Be_2"; "run2_L1Be_3"; "run4_L1Be"; "run5_L1Be"; "EfD_L1Be_1"; "EfD_L1Be_2"; "EfD_L1Be_3"; "Eq_L1Be"; "RD_L1Be_1"; "RD_L1Be_2"; "RD_L1Be_3"; "TDr_L1Be_1"; "TDr_L1Be_2"; "TDr_L1Be_3"; "exits1_L1Be"; "Ebg_L1Be"; "Edr_L1Be"; "TD_L1Be_1"; "TD_L1Be_2"; "TD_L1Be_3"; "W_L1Be"; "Xf_L1Be"; "st_L1Be"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "segsA"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states"; "PreD"; "PostD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "entails_frA"; "call_checkPA"; "call_checkA"; "import_postA"; "@Stdlib.Lists.List"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset"; "Pre_memsetA"; "Posts_memsetA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_cfgA"; "check_ecfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib"; "entsI"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls"; "P0_fc"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame SymCFG SymCall SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA EntailA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import ObjXform ObjUnbase MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.
Import ListNotations.
Open Scope Z_scope.

Definition W_L1Be : list ulink := Wcan 1.
Definition st_L1Be : ustop := UStopLe.
Definition q_L1Be : qvar := QBe.
Definition P0_L1Be : axst := ltac2:(tb__ "0|0|
S7eS11S66S68S39A4").

Definition run1_L1Be : list leafA := ltac2:(tb__ "0|0|
S35S1cSaS2S21SbS2A1A3S3fA3").

Definition S1c_L1Be_1 : axst := ltac2:(tb__ "0|0|
S29S36U0S50A2S17S5S3fA1A1Z1A3").
Definition C2_L1Be_1 : axst := C2_of S1c_L1Be_1.
Definition run2_L1Be_1 : list leafA := ltac2:(tb__ "0|0|
S35S1cSaS2S1dSbS2A1A3S3aA3").
Definition EfD_L1Be_1 : axst := leaf 0 run2_L1Be_1.
Definition ED_L1Be_1 : axst := ED_of EfD_L1Be_1.
Definition RD_L1Be_1 : list sobj := RD_of ED_L1Be_1 1.
Definition TD_L1Be_1 : axst := TD_of ED_L1Be_1 1.
Definition TDr_L1Be_1 : axst := TDr_of TD_L1Be_1.
Definition S1c_L1Be_2 : axst := ltac2:(tb__ "0|0|
S29S36U0S50A2S17S5S3fA1A1Z2A3").
Definition C2_L1Be_2 : axst := C2_of S1c_L1Be_2.
Definition run2_L1Be_2 : list leafA := ltac2:(tb__ "0|0|
S35S1cSaS2S1dSbS2A1A3S3bA3").
Definition EfD_L1Be_2 : axst := leaf 0 run2_L1Be_2.
Definition ED_L1Be_2 : axst := ED_of EfD_L1Be_2.
Definition RD_L1Be_2 : list sobj := RD_of ED_L1Be_2 2.
Definition TD_L1Be_2 : axst := TD_of ED_L1Be_2 2.
Definition TDr_L1Be_2 : axst := TDr_of TD_L1Be_2.
Definition S1c_L1Be_3 : axst := ltac2:(tb__ "0|0|
S29S36U0S50A2S17S5S3fA1A1Z3A3").
Definition C2_L1Be_3 : axst := C2_of S1c_L1Be_3.
Definition run2_L1Be_3 : list leafA := ltac2:(tb__ "0|0|
S35S1cSaS2S1dSbS2A1A3S3cA3").
Definition EfD_L1Be_3 : axst := leaf 0 run2_L1Be_3.
Definition ED_L1Be_3 : axst := ED_of EfD_L1Be_3.
Definition RD_L1Be_3 : list sobj := RD_of ED_L1Be_3 3.
Definition TD_L1Be_3 : axst := TD_of ED_L1Be_3 3.
Definition TDr_L1Be_3 : axst := TDr_of TD_L1Be_3.
Definition exits1_L1Be : list axst := ltac2:(tb__ "0|0|
SaS4S45SaS4S46SaS4S47SbS4A1A3A3A3").

Definition CD_L1Be : axst := CD_of TDr_L1Be_1.
Definition run3_L1Be : list leafA := ltac2:(tb__ "0|0|
S35S1cSaS2S26SaS2S20SbS2A1A3A3S3eA3").
Definition Eps_L1Be : axst := leaf 0 run3_L1Be.
Definition Ebg_L1Be : axst := leaf 1 run3_L1Be.
Definition C3_L1Be : axst := C3_of Eps_L1Be.
Definition run4_L1Be : list leafA := ltac2:(tb__ "0|0|
S35S1cSaS2S25SbS2A1A3S3dA3").
Definition Ems_L1Be : axst := leaf 0 run4_L1Be.
Definition C4_L1Be : axst := C4_of Ems_L1Be.
Definition RM_L1Be : list sobj := RM_of C4_L1Be.
Definition TM0_L1Be : axst := TM0_of C4_L1Be.
Definition TM_L1Be : axst := TM_of C4_L1Be.
Definition run5_L1Be : list leafA := ltac2:(tb__ "0|0|
S35S1cSaS2S23SbS2A1A3S48A3").
Definition Eq_L1Be : axst := leaf 0 run5_L1Be.
Definition EQ_L1Be : axst := EQ_of Eq_L1Be.
Definition RQ_L1Be : list sobj := RQ_of EQ_L1Be q_L1Be.
Definition TQ0_L1Be : axst := TQ0_of EQ_L1Be q_L1Be.
Definition TQ_L1Be : axst := TQ_of EQ_L1Be q_L1Be.
Definition run6_L1Be : list leafA := ltac2:(tb__ "0|0|
S35S1cSaS2S22SaS2S28SbS2A1A3A3S49A3").
Definition Edr_L1Be : axst := leaf 0 run6_L1Be.
Definition Xf_L1Be : axst := leaf 1 run6_L1Be.

Ltac vmr := match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end.
Lemma Cert1_L1Be : ltac2:(tb__ "0|0|
S0S9S79S6aS1cSaS2S21SbS2A1A3S69SaS4S3fSbS4A1A3S60A6ScA3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runl segsA FUELF [CASX] GW P0_L1Be exits1_L1Be run1_L1Be); [unfold run1_L1Be, runA, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.runlA; reflexivity | vmr]. Qed.
Lemma ECert1_L1Be : ltac2:(tb__ "0|2|
S0S9S7aS6aS1cSaS2S21SbS2A1A3S69SaS77S78S3fZ1S1bZ0M0A1M1A3SbS77A1A3S7cS4S77S4S78R1G0G1A3LE;S60A4A6ScA3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runl segsA FUELF [CASX] GW (mkVNA P0_L1Be 1 (SLit 0)) (map (fun E => mkVNA E 0 (SLit 0)) exits1_L1Be) run1_L1Be); [unfold run1_L1Be, runA, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.runlA; reflexivity | vmr]. Qed.

Lemma D2_L1Be_1 : ltac2:(tb__ "0|4|
S0SfS10SdS10S14S14A2M0A1M1SdS15A1M2A2M3A1S6fS5S45A1S5S3aA1A2SeG3S12G1G2SaG0S12S14S14S2cS2fA4SbG0A1A3S24A4A2A3"). Proof. Time vmr. Qed.
Lemma W2_L1Be_1 : ltac2:(tb__ "0|1|
S1S0S9S19S5S3aA1M0A1ScA3S1S0S3S13G0A1S13S5S45A1A1A3S0S9S16G0A1S11A3A2A2"). Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma NX2_L1Be_1 : ltac2:(tb__ "0|0|
S0S9S6bS69S13S5S3aA1A1A2ScA3"). Proof. vmr. Qed.
Lemma EQ2_L1Be_1 : ltac2:(tb__ "0|0|
S0S4S7S45S5S3aA1A2S3aA3"). Proof. vmr. Qed.
Lemma RUN2_L1Be_1 : ltac2:(tb__ "0|0|
S0SdS6A1S35S1cSaS2S1dSbS2A1A3S3aA3S51A3"). Proof. unfold run2_L1Be_1; reflexivity. Qed.
Lemma L2_L1Be_1 : ltac2:(tb__ "0|0|
S1S0S9S1eS51SaS2S1dSbS2A1A3A2ScA3S0S4S36U0S51A2S56A3A2"). Proof. Time (split; [vmr | unfold EfD_L1Be_1; reflexivity]). Qed.
Lemma AXD_L1Be_1 : ltac2:(tb__ "0|0|
S0SfS4A1S6cS56S2aA2SeS4S40A2A3"). Proof. Time vmr. Qed.
Lemma HeD_L1Be_1 : ltac2:(tb__ "0|2|
S0SfSdS18A1M0A1S70S40S6dZ1M1A1S1fS40G1A2A3SeG0S5aA2A3"). Proof. Time vmr. Qed.
Lemma HchkD_L1Be_1 : ltac2:(tb__ "0|1|
S0S9S71S40S6dZ1M0A1S1fS40G0A2S5aSaS4S6eG0A1SbS4A1A3A5ScA3"). Proof. Time vmr. Qed.
Lemma AXDr_L1Be_1 : ltac2:(tb__ "0|0|
S0SfS4A1S6cS63S2bA2SeS4S5dA2A3"). Proof. Time vmr. Qed.
Lemma ENTD_L1Be_1 : ltac2:(tb__ "0|0|
S0S9S7bS5dS3eA2ScA3"). Proof. Time vmr. Qed.
Lemma D2_L1Be_2 : ltac2:(tb__ "0|4|
S0SfS10SdS10S14S14A2M0A1M1SdS15A1M2A2M3A1S6fS5S46A1S5S3bA1A2SeG3S12G1G2SaG0S12S14S14S2cS2fA4SbG0A1A3S24A4A2A3"). Proof. Time vmr. Qed.
Lemma W2_L1Be_2 : ltac2:(tb__ "0|1|
S1S0S9S19S5S3bA1M0A1ScA3S1S0S3S13G0A1S13S5S46A1A1A3S0S9S16G0A1S11A3A2A2"). Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma NX2_L1Be_2 : ltac2:(tb__ "0|0|
S0S9S6bS69S13S5S3bA1A1A2ScA3"). Proof. vmr. Qed.
Lemma EQ2_L1Be_2 : ltac2:(tb__ "0|0|
S0S4S7S46S5S3bA1A2S3bA3"). Proof. vmr. Qed.
Lemma RUN2_L1Be_2 : ltac2:(tb__ "0|0|
S0SdS6A1S35S1cSaS2S1dSbS2A1A3S3bA3S52A3"). Proof. unfold run2_L1Be_2; reflexivity. Qed.
Lemma L2_L1Be_2 : ltac2:(tb__ "0|0|
S1S0S9S1eS52SaS2S1dSbS2A1A3A2ScA3S0S4S36U0S52A2S57A3A2"). Proof. Time (split; [vmr | unfold EfD_L1Be_2; reflexivity]). Qed.
Lemma AXD_L1Be_2 : ltac2:(tb__ "0|0|
S0SfS4A1S6cS57S2aA2SeS4S41A2A3"). Proof. Time vmr. Qed.
Lemma HeD_L1Be_2 : ltac2:(tb__ "0|2|
S0SfSdS18A1M0A1S70S41S6dZ2M1A1S1fS41G1A2A3SeG0S5bA2A3"). Proof. Time vmr. Qed.
Lemma HchkD_L1Be_2 : ltac2:(tb__ "0|1|
S0S9S71S41S6dZ2M0A1S1fS41G0A2S5bSaS4S6eG0A1SbS4A1A3A5ScA3"). Proof. Time vmr. Qed.
Lemma AXDr_L1Be_2 : ltac2:(tb__ "0|0|
S0SfS4A1S6cS64S2bA2SeS4S5eA2A3"). Proof. Time vmr. Qed.
Lemma ENTD_L1Be_2 : ltac2:(tb__ "0|0|
S0S9S7bS5eS3eA2ScA3"). Proof. Time vmr. Qed.
Lemma D2_L1Be_3 : ltac2:(tb__ "0|4|
S0SfS10SdS10S14S14A2M0A1M1SdS15A1M2A2M3A1S6fS5S47A1S5S3cA1A2SeG3S12G1G2SaG0S12S14S14S2cS2fA4SbG0A1A3S24A4A2A3"). Proof. Time vmr. Qed.
Lemma W2_L1Be_3 : ltac2:(tb__ "0|1|
S1S0S9S19S5S3cA1M0A1ScA3S1S0S3S13G0A1S13S5S47A1A1A3S0S9S16G0A1S11A3A2A2"). Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma NX2_L1Be_3 : ltac2:(tb__ "0|0|
S0S9S6bS69S13S5S3cA1A1A2ScA3"). Proof. vmr. Qed.
Lemma EQ2_L1Be_3 : ltac2:(tb__ "0|0|
S0S4S7S47S5S3cA1A2S3cA3"). Proof. vmr. Qed.
Lemma RUN2_L1Be_3 : ltac2:(tb__ "0|0|
S0SdS6A1S35S1cSaS2S1dSbS2A1A3S3cA3S53A3"). Proof. unfold run2_L1Be_3; reflexivity. Qed.
Lemma L2_L1Be_3 : ltac2:(tb__ "0|0|
S1S0S9S1eS53SaS2S1dSbS2A1A3A2ScA3S0S4S36U0S53A2S58A3A2"). Proof. Time (split; [vmr | unfold EfD_L1Be_3; reflexivity]). Qed.
Lemma AXD_L1Be_3 : ltac2:(tb__ "0|0|
S0SfS4A1S6cS58S2aA2SeS4S42A2A3"). Proof. Time vmr. Qed.
Lemma HeD_L1Be_3 : ltac2:(tb__ "0|2|
S0SfSdS18A1M0A1S70S42S6dZ3M1A1S1fS42G1A2A3SeG0S5cA2A3"). Proof. Time vmr. Qed.
Lemma HchkD_L1Be_3 : ltac2:(tb__ "0|1|
S0S9S71S42S6dZ3M0A1S1fS42G0A2S5cSaS4S6eG0A1SbS4A1A3A5ScA3"). Proof. Time vmr. Qed.
Lemma AXDr_L1Be_3 : ltac2:(tb__ "0|0|
S0SfS4A1S6cS65S2bA2SeS4S5fA2A3"). Proof. Time vmr. Qed.
Lemma ENTD_L1Be_3 : ltac2:(tb__ "0|0|
S0S9S7bS5fS3eA2ScA3"). Proof. Time vmr. Qed.
Lemma RUN3_L1Be : ltac2:(tb__ "0|0|
S0SdS6A1S35S1cSaS2S26SaS2S20SbS2A1A3A3S3eA3S4aA3"). Proof. unfold run3_L1Be; reflexivity. Qed.
Lemma L3_L1Be : ltac2:(tb__ "0|0|
S1S0S9S1eS4aSaS2S26SaS2S20SbS2A1A3A3A2ScA3S1S0S4S36U0S4aA2S44A3S0S4S36U1S4aA2S61A3A2A2"). Proof. Time (split; [vmr | split; [unfold Eps_L1Be | unfold Ebg_L1Be]; reflexivity]). Qed.
Lemma NX3_L1Be : ltac2:(tb__ "0|1|
S1S0S9S6bS69S13S5S3eA1M0A1A2ScA3S0S9S16G0A1S11A3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma D3_L1Be : ltac2:(tb__ "0|3|
S0SfS10SdS10S14S14A2A1M0SdS15A1M1A2M2A1S6fS5S44A1S5S3dA1A2SeG2S12G0G1S33SbS15A1A4A2A3"). Proof. Time vmr. Qed.
Lemma EQ3_L1Be : ltac2:(tb__ "0|0|
S0S4S7S44S5S3dA1A2S3dA3"). Proof. vmr. Qed.
Lemma NX3b_L1Be : ltac2:(tb__ "0|0|
S0S9S6bS69S13S5S3dA1A1A2ScA3"). Proof. vmr. Qed.
Lemma W3_L1Be : ltac2:(tb__ "0|1|
S1S0S9S19S5S3dA1M0A1ScA3S1S0S3S13G0A1S13S5S44A1A1A3S0S9S16G0A1S11A3A2A2"). Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma RUN4_L1Be : ltac2:(tb__ "0|0|
S0SdS6A1S35S1cSaS2S25SbS2A1A3S3dA3S54A3"). Proof. unfold run4_L1Be; reflexivity. Qed.
Lemma L4_L1Be : ltac2:(tb__ "0|0|
S1S0S9S1eS54SaS2S25SbS2A1A3A2ScA3S0S4S36U0S54A2S43A3A2"). Proof. Time (split; [vmr | unfold Ems_L1Be; reflexivity]). Qed.
Lemma D4_L1Be : ltac2:(tb__ "0|3|
S0SfS10SdS10S14S14A2A1M0SdS15A1M1A2M2A1S6fS5S43A1S5S37A1A2SeG2S12G0G1S34SbS15A1A4A2A3"). Proof. Time vmr. Qed.
Lemma EQ4_L1Be : ltac2:(tb__ "0|0|
S0S4S7S43S5S37A1A2S37A3"). Proof. vmr. Qed.
Lemma W4_L1Be : ltac2:(tb__ "0|1|
S1S0S9S19S5S37A1M0A1ScA3S1S0S3S13G0A1S13S5S43A1A1A3S0S9S16G0A1S11A3A2A2"). Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma HeM_L1Be : ltac2:(tb__ "0|1|
S0SfSdS18A1M0A1S70S37S75S2dS37A1A3SeG0S4cA2A3"). Proof. Time vmr. Qed.
Lemma HchkM_L1Be : ltac2:(tb__ "0|0|
S0S9S72S37S75S2dS37A1S4cS7cS6S4S8S76A4A5ScA3"). Proof. Time vmr. Qed.
Lemma HTM_L1Be : ltac2:(tb__ "0|0|
S0S4S73S2dS37A1S75S31S37S4cA5S4eA3"). Proof. unfold TM0_L1Be, TM0_of, RM_L1Be; reflexivity. Qed.
Lemma FBM_L1Be : ltac2:(tb__ "0|3|
S1S0S9S74S15S1aS13S5S37A1M0A1M1A1S17G0A1M2A3ScA3S1S0S9S74S15S1aS13S5S4eA1A1A1G2A3ScA3S0S9S6bS69G1A2ScA3A2A2").
Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma ETM_L1Be : ltac2:(tb__ "0|0|
S0S4S7dS4eS17S5S37A1A1A2S48A3"). Proof. vmr. Qed.
Lemma NX5_L1Be : ltac2:(tb__ "0|1|
S1S0S9S6bS69S13S5S48A1M0A1A2ScA3S0S9S16G0A1S11A3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma RUN5_L1Be : ltac2:(tb__ "0|0|
S0SdS6A1S35S1cSaS2S23SbS2A1A3S48A3S55A3"). Proof. unfold run5_L1Be; reflexivity. Qed.
Lemma L5_L1Be : ltac2:(tb__ "0|0|
S1S0S9S1eS55SaS2S23SbS2A1A3A2ScA3S0S4S36U0S55A2S59A3A2"). Proof. Time (split; [vmr | unfold Eq_L1Be; reflexivity]). Qed.
Lemma AXQ_L1Be : ltac2:(tb__ "0|0|
S0SfS4A1S6cS59S32A2SeS4S38A2A3"). Proof. Time vmr. Qed.
Lemma HeQ_L1Be : ltac2:(tb__ "0|1|
S0SfSdS18A1M0A1S70S38S27S39A1S2eS38S39A2A3SeG0S4dA2A3"). Proof. Time vmr. Qed.
Lemma HchkQ_L1Be : ltac2:(tb__ "0|0|
S0S9S72S38S27S39A1S2eS38S39A2S4dSaS4S30S39A1SbS4A1A3A5ScA3"). Proof. Time vmr. Qed.
Lemma HTQ_L1Be : ltac2:(tb__ "0|0|
S0S4S73S2eS38S39A2S27S39A1S30S39A1S38S4dA5S4fA3"). Proof. unfold TQ0_L1Be, TQ0_of, RQ_L1Be; reflexivity. Qed.
Lemma FBQ_L1Be : ltac2:(tb__ "0|3|
S1S0S9S74S15S1aS13S5S38A1M0A1M1A1S17G0A1M2A3ScA3S1S0S9S74S15S1aS13S5S4fA1A1A1G2A3ScA3S0S9S6bS69G1A2ScA3A2A2").
Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma ETQ_L1Be : ltac2:(tb__ "0|0|
S0S4S7dS4fS17S5S38A1A1A2S49A3"). Proof. vmr. Qed.
Lemma NX6_L1Be : ltac2:(tb__ "0|1|
S1S0S9S6bS69S13S5S49A1M0A1A2ScA3S0S9S16G0A1S11A3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma RUN6_L1Be : ltac2:(tb__ "0|0|
S0SdS6A1S35S1cSaS2S22SaS2S28SbS2A1A3A3S49A3S4bA3"). Proof. unfold run6_L1Be; reflexivity. Qed.
Lemma L6_L1Be : ltac2:(tb__ "0|0|
S1S0S9S1eS4bSaS2S22SaS2S28SbS2A1A3A3A2ScA3S1S0S4S36U0S4bA2S62A3S0S4S36U1S4bA2S67A3A2A2"). Proof. Time (split; [vmr | split; [unfold Edr_L1Be | unfold Xf_L1Be]; reflexivity]). Qed.

End F0A_cL1Be.

