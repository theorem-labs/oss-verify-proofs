(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import F_syscalls MallocRep F_malloc_free F_malloc_fast F_malloc_entry F_malloc_enframe MallocTree MallocFacts_A MallocHINV MallocKit_A.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import MallocKit_AB.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import Malloc_fp MallocKit_A2 AllocSlot_iface Malloc_iface.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import MallocNat MallocFacts_AS MallocKit_A3 ASlot_W0 ASlot_W9 ASlot_W18 ASlot_I.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import RunP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Agent_ASlot_M0 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.ASlot_I."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.ASlot_M0."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.ASlot_M0.CEIL_WRAP_1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.ASlot_M0.CEIL_WRAP_2."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.ASlot_W0."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.ASlot_W18."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.F_malloc_enframe."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.F_malloc_entry."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocNat."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocRep."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocTree."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.Malloc_fp."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Mem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.Malloc."; "Stdlib.Lists.List."; "Stdlib.NArith.BinNat.N."; "Stdlib.ZArith.BinInt.Z."; "stdpp.base."; "stdpp.bitvector.definitions."; "stdpp.countable."; "stdpp.decidable."; "stdpp.gmap."; "stdpp.numbers.N."; "stdpp.numbers.Z."], [["1Some"; "1bool"; "1list"; "1option"; "1pair"; "1prod"; "1true"; "2and"; "2eq"; "2iff"; "2not"; "3N"; "3Z"; "0RUNp"; "4ALLC"; "4ENTRY_REL"]; ["6LO"; "6links_only"; "7nest_fn"; "7sc_mono_fn"; "5LO"; "5links_only"; "8ta_rel"; "9as_fm_st"; ":zseq"; ";stc_q"; "<bS"; "<kS"; "=ticks_ok"; ">am_rel"; ">leaf_of"; ">mem"]; ["?grp_hdr_cov"; "?unk_agree"; "@wa"; "ARKGroup"; "AUnknown"; "Aactive"; "Aalloc_meta"; "Aaptr"; "Aarea"; "Abounces"; "Abrkstate"; "Ac_brk"; "Ac_mmap_counter"; "Ac_seq"; "Acell_read"; "Acellval"]; ["Actx"; "Adequeue"; "Aget_meta_rec"; "Aget_shadow"; "Aghdr"; "Alhead"; "Am_set_next"; "Am_set_prev"; "Ameta"; "Amstate"; "Aoptr"; "Ar_base"; "Ar_cells"; "Ar_kind"; "Ar_len"; "Aregion"]; ["Arkind"; "Around_up_pg"; "As_areas"; "As_groups"; "As_next_rid"; "As_regions"; "As_reserved"; "As_shadow"; "As_slots"; "As_tick"; "Aset_head"; "Aset_tick"; "Ashadow"; "Asize_class"; "Aunmap_seq"; "Aupd_meta"]; ["Ausage"; "Bforallb"; "Cle"; "Clt"; "Dadd"; "Dle"; "Dlt"; "0a"; "0b"; "0c"; "0f"; "0g"; "0h"; "0i"; "0m"; "0mA"]; ["0mB"; "0mo"; "0o"; "0off"; "0q"; "0r"; "0rid"; "0sc"; "0sh"; "0st"; "0st'"; "0st0"; "0st1"; "0st2"; "0st3"; "0stA"]; ["0stB"; "Eis_Some"; "Elookup"; "Fbv"; "GN_countable"; "GZ_countable"; "Gprod_countable"; "Hprod_eq_dec"; "Igmap"; "Igmap_lookup"; "Jeq_dec"; "Keq_dec"; "0t"; "0tk"; "0v"; "0w"]; ["0x"]]).
Section CEIL_WRAP_1.
Context {RUNp : RunP}.
Definition links_only (r r' : meta) : Prop :=
m_mem r' = m_mem r /\ m_avail r' = m_avail r /\ m_freed r' = m_freed r
/\ m_last_idx r' = m_last_idx r /\ m_freeable r' = m_freeable r /\ m_sizeclass r' = m_sizeclass r /\ m_maplen r' = m_maplen r.
Lemma leaf_of_ret_inv {R} o (r r' : R) : leaf_of o (SRet r) r' -> r' = r.
Proof. intros (ans & o' & H). rewrite mrun_ret in H. cbn in H. destruct ans; inversion H; reflexivity. Qed.
Lemma leaf_of_vis_inv {R} o e (k : Z -> Malloc.M R) r :
leaf_of o (SVis e k) r ->
match e with
| EUndef _ => False
| EPeek p c h => leaf_of o (k (pans_mem o p c h)) r
| _ => exists z, leaf_of o (k z) r
end.
Proof.
intros (ans & o' & H).
destruct e; try (rewrite mrun_vis in H by exact I; cbn [follow] in H; destruct ans as [|a ans]; [discriminate|]; exists a; exists ans, o'; exact H).
- rewrite mrun_peek in H. exists ans, o'. exact H.
- rewrite mrun_vis in H by exact I. cbn [follow] in H. destruct ans; discriminate.
Qed.
Lemma leaf_of_bad {R} o (bail : Malloc.M R) r : leaf_of o (bad_answer bail) r -> False.
Proof. intros H. exact (leaf_of_vis_inv o _ _ r H). Qed.
Definition LO (st st' : mstate) : Prop := forall q, links_only (get_meta_rec st q) (get_meta_rec st' q).
Lemma LO_refl : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_M0 "5'QI&@r1%2211pVD41").
Proof. intros st. intros q. repeat split; reflexivity. Qed.
Lemma LO_trans : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_M0 "<'QI&@r3r2%3221r5%5214p031p041pVN91pVL:1pVJ;1").
Proof. intros st1 st2 st3.
intros A B q. destruct (A q) as (A1&A2&A3&A4&A5&A6&A7). destruct (B q) as (B1&B2&B3&B4&B5&B6&B7).
repeat split; congruence.
Qed.
Lemma LO_same : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_M0 "A'QI&Q7'8'QH&QBr2r1%3221r3%5213%83731pV::1&@%1258p031pVF?1pVD@1").
Proof. intros st st'. intros H q. rewrite H. apply LO_refl. Qed.
Lemma LO_upd_links : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_M0 "D'QI&Q7'QHpX211&Ar1r2%112%4231pV<71&@r4&R?r3%23183%5241p071pUF>1pUNA1pVDC1").
Proof. intros st m f.
intros Hf q. unfold upd_meta. destruct (decide (q = m)) as [->|NE].
- rewrite get_meta_rec_put_same. apply Hf.
- rewrite get_meta_rec_put_other by exact NE. apply LO_refl.
Qed.
Lemma lo_set_prev : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_M0 ":&QJ'QH&Ar1&QGr2%2213%5241pV<71pWN91"). Proof. intros v r. repeat split; reflexivity. Qed.
Lemma lo_set_next : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_M0 ":&QJ'QH&Ar1&QFr2%2213%5241pV<71pWN91"). Proof. intros v r. repeat split; reflexivity. Qed.
Lemma lo_set_pn : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_M0 ">&QJ'QH&Ar1&QGr3&QFr2%2215%5241%8271pV<:1pX0<1pWN=1"). Proof. intros v w r. repeat split; reflexivity. Qed.
Lemma rec_set_head : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_M0 "D'QE&QJ'QI&Q7'8'QH&QB&R:r4r3r2%43321r1%7221%8242%;3:21pV:=1pVD?1pWNA1pUJC1").
Proof. intros h v st q. destruct h; reflexivity. Qed.
End CEIL_WRAP_1.
Ltac lo_peel :=
first [ apply LO_refl
| apply LO_same; intros ?; reflexivity
| eapply LO_trans; [| apply LO_upd_links; intros ?; repeat split; reflexivity]; lo_peel
| eapply LO_trans; [| apply LO_same; intros ?; apply rec_set_head]; lo_peel ].
Section CEIL_WRAP_2.
Context {RUNp : RunP}.
Lemma LO_dequeue : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_M0 "='QE&Q7'QI&Dr1&QAr3r2%33214%6251pVD81pUN:1pUJ<1").
Proof. intros h m st.
unfold dequeue. cbv zeta.
destruct (negb (optr_eqb (m_next (get_meta_rec st m)) (Some m)));
destruct (m_prev (get_meta_rec st m)) as [pv|]; destruct (m_next (get_meta_rec st m)) as [nx|];
try destruct (optr_eqb _ (Some m)); lo_peel.
Qed.
Section AML.
Context {R : Type}.
Variable o : mem.
Variable Φ : R -> Prop.
Definition KOK (st : mstate) (k : mstate -> optr -> Malloc.M R) : Prop :=
forall st2 mo r, LO st st2 -> leaf_of o (k st2 mo) r -> Φ r.
Definition BOK (bail : Malloc.M R) : Prop := forall r, leaf_of o bail r -> Φ r.
Lemma KOK_LO st st1 k : LO st st1 -> KOK st k -> KOK st1 k.
Proof. intros L K st2 mo r L2 H. apply (K st2 mo r); [eapply LO_trans; [exact L| exact L2]| exact H]. Qed.
Lemma am_take_leaves st k bail r : KOK st k -> BOK bail -> leaf_of o (am_take st k bail) r -> Φ r.
Proof.
intros K B H. unfold am_take in H.
destruct (c_avail_meta (ctx st)) as [m|].
- eapply K; [| exact H]. lo_peel.
- destruct (leaf_of_vis_inv o _ _ r H).
Qed.
Lemma am_carve_leaves st p k bail r : KOK st k -> BOK bail -> leaf_of o (am_carve st p k bail) r -> Φ r.
Proof.
intros K B H. unfold am_carve in H. cbv zeta in H.
eapply am_take_leaves; [| exact B| exact H].
eapply KOK_LO; [| exact K]. apply LO_same. intros q.
destruct (c_meta_area_tail _); reflexivity.
Qed.
Lemma am_finish_leaves st nu k bail r : KOK st k -> BOK bail -> leaf_of o (am_finish st nu k bail) r -> Φ r.
Proof.
intros K B H. unfold am_finish in H.
destruct (c_avail_meta_areas (ctx st)) as [p|]; [| destruct (leaf_of_vis_inv o _ _ r H)].
cbv zeta in H.
destruct (if negb (snd p mod PGSZ =? 0) then false else nu).
- destruct (leaf_of_vis_inv o _ _ r H) as [z Hz]. cbv beta in Hz.
destruct (negb (mprotect_answer_ok z)); [destruct (leaf_of_bad o _ _ Hz)|].
destruct ((z =? 0) || (z =? TWO64 - ENOSYS)).
+ eapply am_carve_leaves; [exact K| exact B| exact Hz].
+ exact (K _ _ _ (LO_refl st) Hz).
- eapply am_carve_leaves; [exact K| exact B| exact H].
Qed.
Lemma am_after_brk_leaves st nu k bail r : KOK st k -> BOK bail -> leaf_of o (am_after_brk st nu k bail) r -> Φ r.
Proof.
intros K B H. unfold am_after_brk in H.
destruct (c_avail_meta_area_count (ctx st) =? 0).
- destruct (leaf_of_vis_inv o _ _ r H) as [z Hz]. cbv beta in Hz.
destruct (negb (mmap_answer_ok _ _ z)); [destruct (leaf_of_bad o _ _ Hz)|].
destruct (is_err z); [exact (K _ _ _ (LO_refl st) Hz)|].
destruct (new_region RKMeta z _ st) as [st1 rid] eqn:E.
eapply am_finish_leaves; [| exact B| exact Hz].
eapply KOK_LO; [| exact K]. apply LO_same. intros q.
replace st1 with (fst (new_region RKMeta z (Z.shiftl 2 (c_meta_alloc_shift (ctx st)) * PGSZ) st)) by (rewrite E; reflexivity). reflexivity.
- eapply am_finish_leaves; [exact K| exact B| exact H].
Qed.
Section SE.
Local Abbreviation SEC_T_alloc_meta_leaves := (forall st k bail r, KOK st k -> BOK bail -> leaf_of o (alloc_meta st k bail) r -> Φ r) (only parsing).
Variable st : ltac:(sec_ty2 constr:(SEC_T_alloc_meta_leaves) 0%nat 0%nat).
Variable k : ltac:(sec_ty2 constr:(SEC_T_alloc_meta_leaves) 1%nat 0%nat).
Variable bail : ltac:(sec_ty2 constr:(SEC_T_alloc_meta_leaves) 2%nat 0%nat).
Variable r : ltac:(sec_ty2 constr:(SEC_T_alloc_meta_leaves) 3%nat 0%nat).
Lemma alloc_meta_leaves : ltac:(sec_stmt2 constr:(SEC_T_alloc_meta_leaves) 4%nat 0%nat).
Proof.
intros K B H. unfold alloc_meta in H.
set (stI := if c_init_done (ctx st) =? 0 then upd_ctx (fun c => set_init_done 1 (set_secret (s_secret st) c)) st else st) in H.
assert (LI : LO st stI) by (apply LO_same; intros q; subst stI; destruct (c_init_done (ctx st) =? 0); reflexivity).
pose proof (KOK_LO st stI k LI K) as KI.
destruct (c_free_meta_head (ctx stI)) as [m|].
{ exact (KI _ _ _ (LO_dequeue LFree m stI) H). }
destruct (negb (c_avail_meta_count (ctx stI) =? 0)); [eapply am_take_leaves; [exact KI| exact B| exact H]|].
destruct ((c_avail_meta_area_count (ctx stI) =? 0) && _); [| eapply am_after_brk_leaves; [exact KI| exact B| exact H]].
destruct (c_brk (ctx stI)) as [| |rid off].
-
destruct (leaf_of_vis_inv o _ _ r H) as [cur Hc]. cbv beta in Hc.
destruct (negb (brk0_answer_ok cur)); [destruct (leaf_of_bad o _ _ Hc)|].
destruct (leaf_of_vis_inv o _ _ r Hc) as [z Hz]. cbv beta in Hz.
destruct (negb (brk_answer_ok _ _ z)); [destruct (leaf_of_bad o _ _ Hz)|].
destruct (negb (z =? _)).
+ eapply am_after_brk_leaves; [| exact B| exact Hz]. eapply KOK_LO; [| exact KI]. apply LO_same; intros q; reflexivity.
+ destruct (negb (brk_pages_ok _ _ _)); [destruct (leaf_of_bad o _ _ Hz)|].
destruct (leaf_of_vis_inv o _ _ r Hz) as [w Hw]. cbv beta in Hw.
destruct (negb (mmap_fixed_answer_ok _ w)); [destruct (leaf_of_bad o _ _ Hw)|].
destruct (new_region RKBrk _ _ stI) as [st1 rid1] eqn:E.
eapply am_after_brk_leaves; [| exact B| exact Hw]. eapply KOK_LO; [| exact KI]. apply LO_same; intros q.
replace st1 with (fst (new_region RKBrk (round_up_pg cur) (2 * PGSZ) stI)) by (rewrite E; reflexivity). reflexivity.
- eapply am_after_brk_leaves; [exact KI| exact B| exact H].
-
destruct (leaf_of_vis_inv o _ _ r H) as [z Hz]. cbv beta in Hz.
destruct (negb (brk_answer_ok _ _ z)); [destruct (leaf_of_bad o _ _ Hz)|].
destruct (negb (z =? _)).
+ eapply am_after_brk_leaves; [| exact B| exact Hz]. eapply KOK_LO; [| exact KI]. apply LO_same; intros q; reflexivity.
+ destruct (negb (brk_pages_ok _ _ _)); [destruct (leaf_of_bad o _ _ Hz)|].
eapply am_after_brk_leaves; [| exact B| exact Hz]. eapply KOK_LO; [| exact KI]. apply LO_same; intros q.
unfold upd_region. destruct (get_region stI rid); reflexivity.
Qed.
End SE.
End AML.
Lemma am_leaf_links_only : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_M0 "Q5&O'QI&QJ&N'3'5%1254%311r4&Q6v=r3&K%12<;&J%119%7569531(0(4r2r1%34DC21%52@1%D4@?71&Q7&E&QBr5%2218%32E9%5221pV:71p091pV4O1pVFQ11pVDQ21pV6Q41").
Proof.
intros o st st' mo H.
refine (alloc_meta_leaves o (fun r => match r with Some (stX, _) => LO st stX | None => True end) st kS bS (Some (st', mo)) _ _ H).
- intros st2 mo2 r L HL. apply leaf_of_ret_inv in HL. subst r. exact L.
- intros r HL. apply leaf_of_ret_inv in HL. subst r. exact I.
Qed.
Lemma links_only_refl : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_M0 "5'QH&Er1%2211pV<41").
Proof. intros r. repeat split; reflexivity. Qed.
Lemma links_only_trans : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_M0 "<'QH&Er3r2%3221r5%5214p031p041pUD91pUB:1pU@;1").
Proof. intros a b c. intros (?&?&?&?&?&?&?) (?&?&?&?&?&?&?). repeat split; congruence. Qed.
Lemma ER_refl_tick : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_M0 ":'QI';'?r2&R;r1%2213%5241pWJ71pVH91").
Proof. intros st0 t.
constructor; try reflexivity; try (intros; tauto).
- split; [intros rid r H; exists r; cbn; repeat split; auto; lia| cbn; lia| reflexivity].
Qed.
Lemma ER_ta : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_M0 "A'QI'<'?r4r3%3221'Fr2%23451r6%8216p031p071pVJ=1pV@=1pVD?1pVH@1").
Proof. intros st0 st sc st1.
intros E T. destruct E as [ES EG EGR EM EME EGE EB EA].
constructor.
- rewrite (tr_shadow _ _ _ T). exact ES.
- intros b. rewrite <- (EG b). destruct (tr_groups _ _ _ T b) as [A B].
split; intros [x Hx]; [destruct (A (ex_intro _ x Hx)) as [y Hy]| destruct (B (ex_intro _ x Hx)) as [y Hy]]; rewrite Hy; eexists; reflexivity.
- intros rid r Hk. rewrite (tr_regions _ _ _ T). apply EGR. exact Hk.
- destruct EM as [R1 N1 S1]. split; [| rewrite (tr_next _ _ _ T); exact N1| rewrite (tr_reserved _ _ _ T); exact S1].
intros rid r Hr. rewrite (tr_regions _ _ _ T). exact (R1 rid r Hr).
- intros q. destruct (tr_geom _ _ _ T q) as (M & _). rewrite M. apply EME.
- intros q Hq. destruct (EGE q Hq) as (A1 & A2 & A3). destruct (tr_geom _ _ _ T q) as (M & L & F & S & P). rewrite L, S. repeat split; try assumption.
unfold get_stride. rewrite L, S, P. exact A1.
- intros q i Hi Hb. apply (EB q i Hi). apply (tr_bits _ _ _ T q i Hi). exact Hb.
- intros a Ha. rewrite (tr_areas _ _ _ T). apply EA. exact Ha.
Qed.
Section SE.
Local Abbreviation SEC_T_ER_am := (ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_M0 "Q;'QI&Q7&O'?r5r4%3221'M(0r3%2291%43761&N'3'5&QJ%22@1%411&Q6v=r6&K%12F7&J%118%7568531%=1I%=2K1(4%E2LH%24N4J1%G241%D4?G71r8%O21>p031p0I1p0O1pV6Q41pUNQ61pVJQ81pVDQ91pVHQ:1")) (only parsing).
Variable st0 : ltac:(sec_ty2 constr:(SEC_T_ER_am) 0%nat 0%nat).
Variable st : ltac:(sec_ty2 constr:(SEC_T_ER_am) 1%nat 0%nat).
Variable st1 : ltac:(sec_ty2 constr:(SEC_T_ER_am) 2%nat 0%nat).
Variable m : ltac:(sec_ty2 constr:(SEC_T_ER_am) 3%nat 0%nat).
Variable o : ltac:(sec_ty2 constr:(SEC_T_ER_am) 4%nat 0%nat).
Lemma ER_am : ltac:(sec_stmt2 constr:(SEC_T_ER_am) 5%nat 0%nat).
Proof.
intros E A L. destruct E as [ES EG EGR EM EME EGE EB EA].
pose proof (am_leaf_links_only o st st1 (Some m) L) as LO.
constructor.
- rewrite (amr_shadow _ _ _ A). exact ES.
- intros b. rewrite <- (EG b). rewrite (amr_groups _ _ _ A). tauto.
- intros rid r Hk. rewrite <- (EGR rid r Hk). split; intros Hr.
+ destruct ((s_regions st) !! rid) as [r0|] eqn:E0.
* destruct (amr_regions _ _ _ A rid r0 E0) as (r' & Hr' & K' & _ & _ & G'). rewrite Hr in Hr'. inversion Hr'; subst r'.
rewrite (G' ltac:(rewrite <- K'; exact Hk)). reflexivity.
* exfalso. exact (amr_new _ _ _ A rid r Hr E0 Hk).
+ destruct (amr_regions _ _ _ A rid r Hr) as (r' & Hr' & K' & _ & _ & G'). rewrite Hr'. f_equal. apply G'. exact Hk.
- destruct EM as [R1 N1 S1]. split.
+ intros rid r Hr. destruct (R1 rid r Hr) as (r1 & H1 & K1 & B1 & L1).
destruct (amr_regions _ _ _ A rid r1 H1) as (r2 & H2 & K2 & B2 & L2 & _). exists r2. repeat split; try congruence. lia.
+ pose proof (amr_next_rid _ _ _ A). lia.
+ rewrite (amr_reserved _ _ _ A). exact S1.
- intros q. destruct (LO q) as (M & _). rewrite M. apply EME.
- intros q Hq. destruct (EGE q Hq) as (A1 & A2 & A3). destruct (LO q) as (M & AV & FR & L2 & F & S & P). rewrite L2, S. repeat split; try assumption.
unfold get_stride. rewrite L2, S, P. exact A1.
- intros q i Hi Hb. apply (EB q i Hi). destruct (LO q) as (_ & AV & FR & _). rewrite <- AV, <- FR. exact Hb.
- intros a Ha. apply (amr_areas _ _ _ A). apply EA. exact Ha.
Qed.
End SE.
Lemma ticks_ok_same : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_M0 "K'QI'8'SH';&SJ&SD'R<%544321&R7r1%211r2%411%<3631&R9%114r3%311%A3?31&Lr4%211p011p051p0;1pVJI1pVDJ1").
Proof. intros st st1. intros ES ET [T1 T2]. split; rewrite ES, ET; assumption. Qed.
Lemma ALLC_tick : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_M0 "QN'QI';'R<'<'8'3%114&SB'SH&SJ&SD%34:219&SI%14<43;r5&R7r7%211%;6A@7541(0r4%22C1%B3@41'5%12EG%D11&SK&SE%D4I214%A4J325&QL%11A%I6M843<1(4r3r2%34Q1Q321%B2=1%Q23=61&RB&R9r9%211%4291p061p0G1pWLQ=1pWNQ<1pV6Q=1pVBQ?1pV>QA1&RC%<1B%221B&>&R;%12FQ4%311p051p091pWJQK1pVHQM1").
Proof. intros st0 t. intros H Ht rid sh o v tk Hs Hc. cbn. pose proof (H rid sh o v tk Hs Hc). lia. Qed.
Lemma ALLC_same : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_M0 "K'QI'8'SH';&SJ&SD'R<%544321&R7r1%211r2%411%<3631&R9%114r3%311%A3?31&>r4%211p011p051p0;1pVJI1pVDJ1").
Proof. intros st st1. intros ES ET H rid sh o v tk Hs Hc. rewrite ET. rewrite ES in Hs. exact (H rid sh o v tk Hs Hc). Qed.
Lemma ALLC_ta : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_M0 "@'QI'<'Fr2r3r1%43321&>r4%211%316p021p061pVJ=1pV@=1pVD?1").
Proof. intros st sc st1. intros T. apply ALLC_same; [apply (tr_shadow _ _ _ T)| apply (tr_tick _ _ _ T)]. Qed.
Lemma ALLC_am : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_M0 "?'QI&QJ'Mr3r2r1%43321&>r4%211p011p051pV4;1pVJ=1pVD>1").
Proof. intros st st1 mo. intros A. apply ALLC_same; [apply (amr_shadow _ _ _ A)| apply (amr_tick _ _ _ A)]. Qed.
Definition sc_mono_fn (a : Z) : bool := forallb (fun b => (size_class a <? size_class b)) (zseq (a + 1) (47 - a)).
Lemma sc_mono_check : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_M0 "<'8'1&RA'<&C&Hz+Q@%3221%73651(6%;3:21").
Proof. vm_compute. reflexivity. Qed.
Lemma size_class_mono : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_M0 "E'<&REzr2%3221'7&RFr3%2215+Q@%4271%6231&R=r4%211%318%:221p061p0>1pUBC1pU@D1").
Proof. intros a b.
intros Ha Hb. pose proof (forallb_zseq sc_mono_fn 0 48 a sc_mono_check ltac:(lia) ltac:(lia)) as X. unfold sc_mono_fn in X.
pose proof (forallb_zseq _ (a + 1) (47 - a) b X ltac:(lia) ltac:(lia)) as Y. apply Z.ltb_lt in Y. exact Y.
Qed.
Lemma size_class_lt_inv : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_M0 "G'<'7&REzr2%3221&RF+Q@%2241%8241&R=r4%211r3%411%9231r5%;216p031p0:1p0;1pUBE1pU@F1").
Proof. intros a b.
intros Ha Hb H. destruct (Z.lt_ge_cases a b) as [L|G]; [exact L|]. exfalso.
destruct (Z.eq_dec a b) as [->|NE]; [lia|]. pose proof (size_class_mono b a ltac:(lia) ltac:(lia)). lia.
Qed.
Definition nest_fn (q : Z) : bool := let j := stc_q q in (0 <=? j) && (j <=? 26) && (q + 1 <=? size_class j).
Lemma nest_check : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_M0 "<'8'1&RA'<&B&H+1+SO%3221%73651(6%;3:21").
Proof. vm_compute. reflexivity. Qed.
Lemma nest_class_props : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_M0 "I'<'7&RE+1r1%3221+SO%5231%7231z&Ir2%211%;241+J%=231%?231&RD%127?&R=%118%C231%E261p0?1pV:H1").
Proof. intros q.
intros Hq. pose proof (forallb_zseq nest_fn 1 127 q nest_check ltac:(lia) ltac:(lia)) as X. unfold nest_fn in X. cbv zeta in X.
rewrite !Bool.andb_true_iff in X. destruct X as [[A B] C]. apply Z.leb_le in A. apply Z.leb_le in B. apply Z.leb_le in C. lia.
Qed.
Lemma unk_agree_xfer : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_M0 "T<&O'QI'SCyR0%211'3y8%511%311pX251&Q1r4r5r3%43321'8'SH';&SJ&SD'R<%544321&R7%11:%21<%:3421'QO'R0&QMr1%211(Q3%A3521%L17&SB%C4BA@9&SI%14DCB;&R5r7%211%76H?64L1(0r2%22B1%N3<41r:%911%>6OF=;Q51%72GQ4%Q33A21p061p0D1pV<K1pV>Q51&Q7&9&SA'QD&SG'<&SK%34Q=Q<21&SF&SE%26Q@Q?Q>541%QB4;418%O4<529&R3r6%211%Q56@=54Q:1%?2>1r8%611%Q96DA98Q>1%C2B1%E251pUBG1r<%Q:11%Q?6R0QGQ>Q<R61%R33QA1Q1%QG1R8%R53QI1QE'7&REz%221R=&RF&R1&QN%11R@%311%52RC1%:271'Q?&Q>&QCr?%221QM%421RI(Q4%11RL%RI3831&:&Q0r@%231Q3Q7%411r>&Q2&RD&QK%11Q9%321R<%511%711%;12%S83S?21p0;1p0A1p0K1p0Q71p0Q:1pUJR11pV8R21pV<S51pV>S?1%SG3RJRCQLp021p0QE1p0R>1p0S<1p0SH1pV2SN1pW2T71pV0T91pW0T91pV6T;1").
Proof. intros o stA mA stB mB.
intros UA ES ERG EG AG rid r off h Hr Hk Ho Hc NG.
pose proof (ERG rid r Hk Hr) as Hr0.
assert (Hc0 : cell_read (get_shadow stA rid) off = Unknown h) by (revert Hc; unfold get_shadow; rewrite ES; intros X; exact X).
assert (NG0 : ~ grp_hdr_cov stA rid off).
{ intros (bq & gh & Hbq & Hf & Hoff). apply NG. destruct (proj2 (EG bq) (ex_intro _ gh Hbq)) as [gh1 Hbq1]. exists bq, gh1. auto. }
rewrite (AG rid r off h Hr0 Hk Ho Hc0 NG0). exact (UA rid r off h Hr0 Hk Ho Hc0 NG0).
Qed.
Lemma fm_proj : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_M0 "SI'QI&Q7&Gr2r1%3221'7'8'SH';&SJ&SD'QO%544321&R5%11;r3%311%;3531'R<%<4;:91&R7%11B%217%A3421&SG'<&SK%34CB21&SF&SE%26FED541'QD%I4Q0521&R3%11O%21D%N3421'Q8%O4Q6;81&R2%11Q5%21J%Q43421'5%12Q<C%Q64Q=B?1&R8%11Q<%21Q1%Q;3421&R9%11Q@%21Q5%Q?3Q=21&R4%11QD%21Q9%QC3QA21'2%@2Q2Q2%211&R6%11QK%21Q@%QJ3421&QJ&Q5%12R1R0r4%321R2%R03531pUDQ>1&R@%12R7R6%226R7%R53QB21pULQC1'Q:&Q;&Q@%11R=%311%31R3%511%R>3731&Q<%116%215%RB3QO21&Q9%12RHRG%22GRH%RF3R321pULR41&R>%12RMRL%22LRM%RK3R821pULR91&Q=%11D%21C%S03R=21%S2251%S32;1%S42A1%S52F1%S62O1%S72Q51%S82Q=1%S92QE1%S:2QJ1%S;2QO1%S<2R71%S=2R>1%S>2RL1%S?2S31tVFSFSA1pUHSF1pVDSH1").
Proof. intros st g.
unfold as_fm_st, as_queue_st, as_fm_link, as_fm_single. cbn [get_head].
destruct (c_free_meta_head (ctx (put_meta g meta0 st))) as [h|].
- cbv zeta. destruct (m_prev (get_meta_rec (put_meta g meta0 st) h)) as [p|]; repeat split; reflexivity.
- repeat split; reflexivity.
Qed.
End CEIL_WRAP_2.
