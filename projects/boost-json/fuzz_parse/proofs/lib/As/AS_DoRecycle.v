(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require AW_0Gc. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From Stdlib Require Import FMapPositive.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.boost_json.fuzz_parse.images Require Import Asan.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import SReach AllocSim MmapSim LazyRestrict LazyLedger LazySR LazyNodes AsanAllocModel AsanAllocCons AsanAllocConsC.   (* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require Import ASegs AsShadow AllocWf AllocKit AllocBudget AllocRep AllocRepFacts AllocRepFacts2 AllocRepX
     AsDepotInv AW_DepotFrame AllocWalkKit SecLazy AG_Malloc AG_Malloc2 AG_MallocModel
     AG_RepQ AG_RepQFacts AW_MergeBatches AW_Recycle AW_DoRecycle AG_WriteSet SecLazy2 AG_RecycleDefs.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As8AsShadow~~~~~~03mem37Corelib7Numbers7BinNumsk31Zk34Npos35stdpp9bitvectorbdefinitionsm72bv37Corelib4Init9Datatypeso94Noneo96option37Corelib4Init5Logicr12eqr13not3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticst05wview79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As5ASegs~~~~~~hgf5asegsm7bbv_unsigned79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As8AllocRep~~~~~~hm18agree_on79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~hqb8bytes_ato96lengtho94listr13and46Stdlib6ZArith6BinInt1Zig73addig72leig72ltig76of_nat79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Frame~~~~~~ijc3stkhm14junkhqb5wr_at79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Step~~~~~~ip08rw_cells79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Cells~~~~~~it74cellit7acells_size79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Arr~~~~~~ji96u64arrig73mul04SHAD02sh08poisonedo93nat69OSSVerify6Proofsaboost_jsonafuzz_parse3libeAsanAllocModel~~~~~~joe7qb_addrjoeakBatchSizejoe8qb_counthm19batch_repr12orjoe9qb_chunksjoe6qbatchjoe4zlenig73div79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2AsfAW_MergeBatches~~~~~~kic4bseg37Corelib5Lists7ListDefkn96Forallkic3bok36Stdlib5Lists4Listkq12In79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As7AG_RepQ~~~~~~kra3WFQ79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2AsbAllocBudget~~~~~~kve6B_PRIMkve6pusage69OSSVerify6Proofsaboost_jsonafuzz_parse3libeAsanAllocConsC~~~~~~ll34NUMcjoe6astatejoeaget_regionjoeh1rg_allocated_userjoecas_space_begjoedclass_of_addrjoeain_primaryo94booljoebkBatchClassig73powo94truer12exjoe5chunkjoebCQuarantinejoecch_chunk_begjoe8ch_statejoeachunk_listjoe6cstateo94Someo94conso93nilhm15wlistit72C879OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4TacX~~~~~~mp12wzkq19nth_errorkra5AREPQhm15AINSThm1bOI_SPACEBEGhm14a_sbhm13astjoe7qb_sizekic4bsum79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2AsbAG_WriteSet~~~~~~ni26acompl79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2AsaAsDepotInv~~~~~~nmd5depot3h5LinuxProcessSemanticsfLinuxProcessSem5Statenr65Modelhm14a_stjoe6schunkhm14a_ALhm14a_Zrhm15a_bothm15a_ctxhm15a_fsbhm14a_pahm15a_thrhm15a_topjoe6as_seco94prod79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2AseAG_RecycleDefs~~~~~~ol55aliveol5aalive_keptol54avisni24avmx79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As7SecLazy~~~~~~os0anonvm_same79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2AsaAG_Malloc2~~~~~~pgbcdepot_placed79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As9AllocRepX~~~~~~plb7AMODELXplb8awin_visplb9depot_covplbaflagsx_repnmd5DEPOTjoefas_cache_initedhqb7mem_invjoe6effecto94negbjoedcache_deallocjoefcb_recycle_listjoeado_recyclekq1arev_append99OSSVerify6Proofsaboost_jsonafuzz_parse3lib2AscAS_DoRecycle3HCW4Loop~~~~~~qk46dr_mid79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2AseAG_MallocModel~~~~~~qp9fsame_but_shadowt0dmachine_statehm13a_Lhm13a_Sm77Z_to_bvo94pair3h5LinuxProcessSemanticsfLinuxProcessSem3Runrhf5mkCfgqk43CURqk43REL69OSSVerify6Proofsaboost_jsonafuzz_parse3libcLazyRestrict~~~~~~rm28restrict69OSSVerify6Proofsaboost_jsonafuzz_parse3lib6LazySR~~~~~~rqd4lzokijc3mkR79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib6MState~~~~~~rv52MS79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib8PropExec~~~~~~sj87seg_romkn93mapkq15NoDupkq12hd79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2AscAW_DoRecycle~~~~~~sp88dr_framejoeh9kAsanHeapLeftRedzoneMagickq14lastig76to_nat36Stdlib7SortingbPermutationth6bPermutationqk43MSFqk43TOKsp8bdr_head_memsp8adr_head_mskq18flat_mapni25awrithm19placed_ok05aceilol55pendzijc3ivlo93fsto93sndqk46wlocalijc7outsideijc5munchijc5wmonorm2h5same_but_materialized69OSSVerify6Proofsaboost_jsonafuzz_parse3lib6SReach~~~~~~tv26sreach69OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Scfg~~~~~~uj5dhunspell_scfgqk47HEADINVqk47dr_postqk44memBjoeakSpaceSizeo93appkn95skipnhm14OI_Qhm1bbatches_rephm17a_cacheig76modulohm13ATPnmd4d_nbnmd4d_sbol5arstep_postjoeacb_recyclejoeaclass_size" s.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Ltac lia ::=
  first [ zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
        | zify_prune; Zify.zify; xlia zchecker
        | Zify.zify; xlia zchecker ].
(* [comment removed for export] *)
Local Ltac olia := Zify.zify; xlia zchecker.

Section HCW.
  Context {HCEIL : HeapCeil}.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition wkeep : ltac2:(zQ "20!je!lc>1P>0$1P>1m$0>2m'$0P") := ltac2:(zQ "b0!m0!o4!q1!q8!s5!sa!hg7!hka!je!lc!hl3\1P>0$9P\1m$8\2m'$8>1x@1$1@1$0#k0>0@1^4@2$a@1$0#k0^1>0@1$5@3$4@1$3@1$1@1$0#8@3$6$7^4^2@1$2@1$1@1$0#8@1$5@3$4@1$3@1$1@1$0#8@3$6$7^4^3@1$2@1$1@1$0#8").

Lemma agree_on_weaken : ltac2:(zQ "30!lc!hpf!je>1P>0$0P>2P'>0$0P>1m$2>2m'$2>0>1a$0>0@1^4^1@1^6^2>0@3$1^5^3^2@3$1^5^4^3").
Proof. intros P P' m m' H A x Hp Hr. exact (A x (H _ Hp) Hr). Qed.
Lemma agree_on_refl : ltac2:(zQ "30!lc!hpf!je>1P>0$0P>1m$2@3$1^2^1^1").
Proof. intros P m x _ _. reflexivity. Qed.
Lemma agree_on_trans : ltac2:(zQ "30!hpf!je!lc>1P>0$2P>2m1$1>2m2$1>2m3$1>0@3$0^4^3^2>0@3$0^5^3^2@3$0^6^5^3").
Proof. intros P m1 m2 m3 A B x Hp Hr. rewrite (B x Hp Hr). exact (A x Hp Hr). Qed.

Section TransportPt2.
  Variable P : ltac2:(zQ "10!lc>0$0P").
  Variables m m' : mem.
  Hypothesis AG : ltac2:(zQ "10!hpf@3$0?1P?1m?2m'").
  Let WK : wkeep P m m'.
  Proof.
    intros x Hp Hx. pose proof (bv_unsigned_in_range _ x) as R; change (bv_modulus 64) with (2^64) in R.
    pose proof (AG (bv_unsigned x) Hp R) as E. unfold wa in E. rewrite Z_to_bv_bv_unsigned in E.
    rewrite (wview_pointwise m m' x E). exact Hx.
  Qed.

  Lemma bytes_at_transport_pt2 : ltac2:(zQ "c0!m0!lc!hka!hu5!o4!hv1!hva!ig1!ihf!ii6!iic!ij2>1A$1>2bs@1$6@1$4@1$0#8>0@4$3$2?1m^2^1>0>1a$1>0@2$7@2$9^4^1@2$a^1@2$8^4@1$b@2$5@1$4@1$0#8^3@1?1P^2@4$3$2?2m'^4^3").
  Proof.
    (intros A bs nd_i1 HR; ndestruct nd_i1 as (Ha & Hl & H)). split; [olia|]. split; [olia|].
    intros i Hi. unfold mrd. rewrite AG; [apply H; exact Hi| apply HR; olia| olia].
  Qed.
  Lemma stk_transport_pt2 : ltac2:(zQ "60!lc!hka!in8!ig1!ii6!iic>2lo$0>2hi$0>0@4$2$1?1m^2^1>0>1a$0>0@2$3@2$4^4^1@2$5^1^3@1?1P^2@4$2$1?2m'^4^3").
  Proof.
    (intros lo hi nd_i2 HR; ndestruct nd_i2 as (H1 & H2 & H)). split; [olia|]. split; [olia|]. intros a Ha.
    destruct (H a Ha) as [Hw (b & Hb)]. split.
    - apply WK; [| exact Hw]. unfold wa. rewrite unsigned_lit by olia. apply HR. exact Ha.
    - exists b. unfold mrd in *. rewrite AG; [exact Hb| apply HR; olia| olia].
  Qed.
  Lemma junk_transport_pt2 : ltac2:(zQ "60!lc!inf!ig1!ihf!ii6!iic>2lo$0>1n$0>0@3$1?1m^2^1>0>1a$0>0@2$2@2$4^4^1@2$5^1@2$3^4^3@1?1P^2@3$1?2m'^4^3").
  Proof. intros lo n J HR Hn. eapply stk_transport_pt2; [apply J; exact Hn| exact HR]. Qed.
  Lemma wr_at_transport_pt2 : ltac2:(zQ "70!lc!hka!io7!ig1!ihf!ii6!iic>1A$0>1n$0>0@4$2$1?1m^2^1>0>1a$0>0@2$3@2$5^4^1@2$6^1@2$4^4^3@1?1P^2@4$2$1?2m'^4^3").
  Proof.
    (intros A n nd_i3 HR; ndestruct nd_i3 as (H1 & H2 & H)). split; [exact H1|]. split; [exact H2|]. intros i Hi.
    apply WK; [| apply H; exact Hi]. unfold wa. rewrite unsigned_lit by olia. apply HR. olia.
  Qed.
  Lemma rw_cells_transport_pt2 : ltac2:(zQ "b0!lc!hka!isb!hva!ig1!jh3!jhb!ihf!ii6!iic!ij2>1A$0>2cs@1$3$5>0@4$2$1?1m^2^1>0>1a$0>0@2$4@2$8^4^1@2$9^1@2$7^4@1$a@1$6^3@1?1P^2@4$2$1?2m'^4^3").
  Proof.
    intros A cs [[Hwf Hb] Hw] HR. split; [split; [exact Hwf|]| eapply wr_at_transport_pt2; [exact Hw| exact HR]].
    eapply bytes_at_transport_pt2; [exact Hb|]. rewrite cells_bytes_length by assumption. exact HR.
  Qed.
  Lemma u64arr_transport_pt2 : ltac2:(zQ "d0!m0!lc!hka!jm3!o4!hv1!hva!ig1!ihf!ii6!iic!jmd!ij2>1A$1>2ws@1$6@1$4@1$0#k0>0@4$3$2?1m^2^1>0>1a$1>0@2$7@2$9^4^1@2$a^1@2$8^4@2$b+8@1$c@2$5@1$4@1$0#k0^3@1?1P^2@4$3$2?2m'^4^3").
  Proof.
    intros A ws [Hb Hw] HR. split.
    - eapply bytes_at_transport_pt2; [exact Hb|]. rewrite u64s_length, Nat2Z.inj_mul. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. intros a Ha. apply HR. olia.
    - eapply wr_at_transport_pt2; [exact Hw|]. exact HR.
  Qed.
  Lemma SHAD_transport_pt2 : ltac2:(zQ "c0!m0!lc!jn4!jna!o4!hv1!hva!ig1!ihf!ii6!iic!ij2>1A$1>3sbs@1$6@1$4@1$0#8>0@3$2?1m^2^1>0>1a$1>0@2$7@2$9@1$3^4^1@2$a^1@2$8@1$3^4@1$b@2$5@1$4@1$0#8^3@1?1P^2@3$2?2m'^4^3").
  Proof.
    (intros A sbs nd_i4 HR; ndestruct nd_i4 as (A0 & HA & [Hb Hw])). split; [exact A0|]. split; [exact HA|].
    split; [eapply bytes_at_transport_pt2; eauto| eapply wr_at_transport_pt2; [exact Hw| exact HR]].
  Qed.
  Lemma poisoned_transport_pt2 : ltac2:(zQ "90!lc!jne!jna!jo8!ig1!ihf!ii6!iic!ij2>1A$0>1k$3>1v$0>0@4$1?1m^3^2^1>0>1a$0>0@2$4@2$6@1$2^5^1@2$7^1@2$5@1$2^5@1$8^4@1?1P^2@4$1?2m'^5^4^3").
  Proof.
    intros A k v H HR. eapply SHAD_transport_pt2; [exact H|]. unfold poison_bytes. rewrite repeat_length. exact HR.
  Qed.
  Lemma batch_rep_transport_pt2 : ltac2:(zQ "h10!lc!jsf!ii6!jta!ju8!ihf!ig1!jv4!jna!iic!s5!kg1!kg6!kh3!khd!ki5!jmd>1b$d>2nx$0>0>1a$0>0@2$b@2$6@2$2@1$1^3^1@2$9^1@2$5@1$1^3$3@2$6@2$2@1$8@1$1^3^1@2$9^1@2$5@1$8@1$1^3@2$f$3+8@1?1P^2>0@2$2Z@1$4^3>0@2$2@2$5+h8@2$h0+8@1$4^4$3>0@3$a$0@1$4^5@2$e$0@1$c^5>0@3$7?1m^6^5@3$7?2m'^7^6").
  Proof.
    (intros b nx HP K1 K2 K3 nd_i5; ndestruct nd_i5 as (B1 & B2 & B3 & B4)). unfold batch_rep. unfold kBatchSize in *.
    assert (LW : Z.of_nat (length (wlist (qb_chunks b))) = qb_count b) by (unfold wlist; rewrite length_map; unfold zlen in K3; olia).
    split; [| split; [| split]].
    - eapply rw_cells_transport_pt2; [exact B1|]. cbn [cells_size csize Nat.add]. intros a Ha. apply HP. left. olia.
    - eapply u64arr_transport_pt2; [exact B2|]. rewrite LW. intros a Ha. apply HP. left. olia.
    - eapply junk_transport_pt2; [exact B3|]. intros a Ha. apply HP. left. olia.
    - eapply poisoned_transport_pt2; [exact B4|]. intros a Ha. apply HP. right.
      change (Z.of_nat (Z.to_nat (8192 / 8))) with 1024 in Ha. change (8192 / 8) with 1024. olia.
  Qed.
  Lemma bseg_transport_pt2 : ltac2:(zQ "h00!jsf!kh3!ig1!lc!kn1!jna!jta!ihf!ii6!iic!hva!kg1!kp0!kpa!kr4!ki5>1l@1$a$1>2nx$3>0>1b$1>1a$3>0@3$e$1^2^4>0@2$b@2$2@2$8@1$0^3^2@2$9^2@2$7@1$0^3$6@2$2@2$8@1$5@1$0^3^2@2$9^2@2$7@1$5@1$0^3@2$f$6+8@1?1P^3>0@3$c$1@1$d?5HCEIL^3>0@3$4?1m^4^3@3$4?2m'^5^4").
  Proof.
    intros l nx HP OKl. induction l as [|b r IH]; [exact (fun x => x)|].
    cbn [bseg]. intros [HB HR]. apply Forall_cons_iff in OKl. destruct OKl as [OKb OKr].
    split; [| apply IH; [intros b0 a Hb0 Ha; apply (HP b0 a); [right; exact Hb0| exact Ha]| exact OKr| exact HR]].
    ndestruct OKb as (_ & _ & _ & K1 & K2 & _). unfold kBatchCount, kBatchSize in *.
    apply (batch_rep_transport_pt2 b _); [intros a Ha; apply (HP b a); [left; reflexivity| exact Ha]| clear - K1; olia| clear - K1; unfold kBatchSize; olia| exact K2| exact HB].
  Qed.
End TransportPt2.


(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma PROOM_of_NUM : ltac2:(zQ "90!hva!lc!kv7!ljf!lk9!lp4!lpc!ihf!ii6>2st$6>2XC@1$0$1>2XB@1$0$1>0@3$2^3^2^1>0@1$5^4@2$8@2$7@1$4^5+kqgg0$3").
Proof.
  intros st XC XB W NM. pose proof B0c_val as BV.
  assert (PB : pusage st <= B0c); [| clear - PB BV; olia].
  apply pusage_boundc; [exact NM|]. intros c Hc. unfold kNumClasses in Hc.
  pose proof (WFQ_region st XC XB c W ltac:(unfold kNumClasses; olia)) as RO. npose (class_size_table_facts c ltac:(olia)) as (CS1 & _ & CS3 & _).
  cbv zeta. split; [olia|]. split; [split; [apply (ro_alloc_nonneg _ _ RO)| apply (ro_alloc_le _ _ RO)]|].
  split.
  - pose proof (ro_tail_small _ _ RO ltac:(olia)) as T. destruct (rg_allocated_user (get_region st c) =? 0); unfold kUserMapSize in *; olia.
  - pose proof (ro_fa_le _ _ RO). pose proof (ro_fa_bound _ _ RO). pose proof (ro_numfreed _ _ RO). pose proof (zlen_nonneg (rg_free_array (get_region st c))). olia.
Qed.

Lemma NUM_au : ltac2:(zQ "70!lc!lp4!lpc!lq6!lr4!s5!ii6>2st$2>3st'$2>0>2c0$0>0@2$6Z^1@3$5$0@1$4@2$3^3^2@1$4@2$3^4^2>0@1$1^3@1$1^3").
Proof. intros st st' AU NM c Hc. unfold ncarved. rewrite (AU c ltac:(clear - Hc; olia)). exact (NM c Hc). Qed.

Lemma class_of_addr_sb : ltac2:(zQ "50!lc!s5!lsa!lpc!lta>2st$3>3st'$3>1a$0>0@3$1$0@1$2^2@1$2^3@3$1$0@2$4^3^2@2$4^4^2").
Proof. intros st st' a E. unfold class_of_addr. rewrite E. reflexivity. Qed.
Lemma in_primary_sb : ltac2:(zQ "60!s5!lc!lsa!lpc!lub!lv9>2st$3>3st'$3>1a$1>0@3$0$1@1$2^2@1$2^3@3$0$5@2$4^3^2@2$4^4^2").
Proof. intros st st' a E. unfold in_primary. rewrite E. reflexivity. Qed.

(* [comment removed for export] *)
Lemma xb24_facts : ltac2:(zQ "h30!lc!ig1!s5!hva!mg0!ihf!mgf!lv9!mh6!mhd!kv7!lsa!lpc!lta!lub!kr4!ii6!iic!jmd>2st$c>2XC@1$3$0>2XB@1$3$0>1B$0>0@3$a^4^3^2>0@3$f$0^2^3>0@3$2$0@2$d^6^3$4@2$9$0\3off$0@2$1@2$1@2$h0Z^1@2$h1^1@2$6+2+i0@2$1@3$2$0^5@2$5@2$5@1$b^8@2$h2$4@2$6+2+i0^1@3$2$7@2$e^8^5$8").
Proof.
  intros st XC XB B W HB CL. pose proof (WFQ_xb st XC XB B W HB) as CV. unfold xb_ok in CV. rewrite CL in CV.
  ndestruct CV as (C1 & C2 & C3 & C4 & C5).
  pose proof (WFQ_region st XC XB kBatchClass W ltac:(unfold kBatchClass, kNumClasses; olia)) as RO.
  pose proof (ro_alloc_le _ _ RO) as A1. pose proof (ro_mapped_bound _ _ RO) as A2.
  unfold region_beg, kRegionSizeLog in *. rewrite Z.shiftl_mul_pow2 in * by (clear; olia).
  change (class_size kBatchClass) with 8192 in *. unfold kFreeArrayOffset, kUserMapSize, kBatchClass in *.
  exists (B - as_space_beg st - 24 * 2^32). split; [clear - C3 C5 A1 A2; olia|]. split; [clear; olia|].
  unfold in_primary, kSpaceSize. apply andb_true_intro; split; [apply Z.leb_le| apply Z.ltb_lt]; clear - C3 C5 A1 A2; olia.
Qed.

(* [comment removed for export] *)
Lemma xc_chunk : ltac2:(zQ "e0!lc!mi2!hva!ig1!s5!kr4!mhd!kv7!mib!lpc!mja!mka!ml6!mm4>2st$9>2XC@1$2$0>2XB@1$2$0>3mch$0>0@3$7^4^3^2>0@3$5$0^2^4@2$6$1\2ch$1@2$3@3$5$1^1@1$c^7@2$3@3$4$d@1$b^1$8@3$4$0@1$a^1^4").
Proof.
  intros st XC XB mch W Hin. ndestruct (WFQ_xc st XC XB mch W Hin) as (ch & Fd & Qu). exists ch.
  split; [exact (find_chunk_In st _ ch Fd)|]. split; [exact Qu|].
  unfold ch_chunk_beg. rewrite (find_chunk_key st _ ch (WFQ_keys st XC XB W) Fd). unfold kChunkHeaderSize. clear; olia.
Qed.

(* [comment removed for export] *)
Lemma u64arr_cell : ltac2:(zQ "h50!lc!q8!m0!hka!jh3!o4!mme!mn5!hva!jo8!mnc!s5!mo2!jm3!mob!isb!msc!mt2!ihf!jmd!ij2>1m>0@1$5@1$2#k0@1$1@1$5@1$2#8>1A$0>2ls@1$8$0>1i$9>1x$0>0@4$d$3^5^4@1$c^3>0@3$b@1$1$0@3$h1$0^4^3@2$6$0^2@4$f$3^7@2$h2^6@2$h3+8@1$h4^4@3$7$4@1$e@1$h0^3@1$a$4").
Proof.
  intros m A ls i x U NE. apply nth_error_split in NE. ndestruct NE as (l1 & l2 & -> & LEN).
  unfold wlist in U. rewrite map_app in U. cbn [map] in U. apply (proj1 (mb_u64arr_app _ _ _ _)) in U. destruct U as [_ U].
  apply (proj1 (mb_u64arr_cons _ _ _ _)) in U. destruct U as [U _]. rewrite length_map, LEN in U. exact U.
Qed.

(* [comment removed for export] *)
Lemma arepq_sb_cell : ltac2:(zQ "h00!hva!lc!jh3!mn5!mnc!mtf!hka!mu8!mv1!ng0!ng8!je!mob!isb!msc!ihf>1s$a>2XC@1$0$1>2XB@1$0$1>1m$b>0@5$5?5HCEIL^4^3^2^1@4$d$6^2@2$f$7$8@3$3$2@1$c@1$e@1$9^5@1$4$2").
Proof.
  intros s XC XB m R. pose proof (AREPQ_mem _ _ _ _ R) as (I & _). destruct I as (I1 & _).
  apply (proj1 (rw_cells_app asegs _ _ [_] _)) in I1. exact (proj1 I1).
Qed.

(* [comment removed for export] *)
Lemma batch_junk : ltac2:(zQ "h80!jsf!jh3!ihf!mn5!hka!mob!msc!m0!jta!ju8!o4!mnc!q8!lc!kpa!inf!mo2!kg6!ngf!kh3!jm3!in8!isb!jmd>1m>0@1$a@1$7#k0@1$c@1$a@1$7#8>1b$h3>2nx$d>0@2$e?5HCEIL^2>0@4$h6$4^4@1$0^3@3$3$1@1$5@1$6^2@3$3$1@1$5@1$6@1$h2^3@3$3$1@1$5@1$6@1$9^3@1$b$1>0@4$h4$4^5@2$2@1$0^4+h8@1$h0@1$h1^4>0@4$h5$4^6@2$2@2$2@1$0^5+h8@2$h7+8@1$9^5@2$2@1$0^5$8@3$f^7@1$0^6$8").
Proof.
  intros m b nx OK H1 H2 H3 _. ndestruct OK as (K0 & K0' & _ & K1 & K2 & _).
  pose proof (stk_of_rw_cells asegs _ _ _ H1) as S1. cbn [cells_size csize Nat.add] in S1. change (Z.of_nat 24) with 24 in S1.
  pose proof (stk_of_u64arr _ _ _ H2) as S2. unfold wlist in S2. rewrite length_map in S2.
  replace (8 * Z.of_nat (length (qb_chunks b))) with (8 * qb_count b) in S2 by (unfold zlen in K2; clear - K2; olia).
  unfold kBatchSize, kBatchCount in *.
  eapply stk_merge; [exact S1| eapply stk_merge; [exact S2| exact H3| clear - K1; olia]| clear - K1; olia].
Qed.

Lemma bsum_cons_le : ltac2:(zQ "60!kh3!nha!mn5!hva!kpa!ii6>1b$0>1T@1$3$0>0@2$4?5HCEIL^2@2$5@1$1^2@1$1@3$2$0^3^2").
Proof. (intros b T nd_i6; ndestruct nd_i6 as (_ & _ & _ & _ & _ & K & _)). rewrite bsum_cons. unfold kBatchSize in K. clear - K; olia. Qed.

(* [comment removed for export] *)
Lemma acompl_SP_mono : ltac2:(zQ "60!lc!nm3!ng8!je!nqd!ii6>1s$2>2s'$2>1d$4>2lo$0>2SP$0>3SP'$0>1m$3>2m'$3>0@2$5^4^3>0@7$1^9^8^7^6^5^3^2@7$1^a^9^8^7^5^4^3").
Proof.
  intros s s' d lo SP SP' m m' LE A a Ha NW. apply (A a Ha). intros W. apply NW. unfold awrit in W |- *.
  destruct W as [H|H]; [left; clear - H LE; olia| right; exact H].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Loop.
  Variables (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32).
  (* [comment removed for export] *)
  Variables (rs0 rs1 rs2 rs3 rs4 rs5 rs6 rs7 rs8 rs9 s10 s11 cs : word).
  Variables (lo : Z) (d : depot) (l : list qbatch) (Q : config -> Prop).
  (* [comment removed for export] *)
  Variables (s0 : ast) (m0 : mem) (mo0 : Model) (T0L : list qbatch).

  Let spv : ltac2:(zQ "10!lc$0") := ltac2:(zQ "20!m0!hl3@2$1@1$0#k0?2sp").          (* [comment removed for export] *)
  Let T0 : ltac2:(zQ "10!lc$0") := ltac2:(zQ "10!ihf@2$0?3spv+n0").                (* [comment removed for export] *)
  Let SP : ltac2:(zQ "10!lc$0") := ltac2:(zQ "10!ihf@2$0?3spv+p0").                (* [comment removed for export] *)
  Let st0 : ltac2:(zQ "10!lpc$0") := ltac2:(zQ "10!nud@1$0?2s0").
  Let ca : ltac2:(zQ "20!m0!o4@1$1@1$0#k0") := ltac2:(zQ "20!usf!msc@1$1@1$0?2s0").          (* [comment removed for export] *)

  Hypothesis LO : ltac2:(zQ "20!toe!ii6@2$1@1$0?5HCEIL?2lo").
  Hypothesis HI : ltac2:(zQ "20!ihf!ii6@2$1@2$0?2lo+ji0?3spv").
  Hypothesis SPT : ltac2:(zQ "30!ihf!ii6!mgf@2$1@2$0@2$0?3spv+n0+m0@2$2+2+if").
  Hypothesis SPA : ltac2:(zQ "30!s5!lc!uta@3$0$1@2$2?3spv+h0Z").
  Hypothesis TPv : ltac2:(zQ "50!s5!m0!lc!uu4!hl3@3$0$2@2$4@1$1#k0?2tp$3").
  Hypothesis OKL : ltac2:(zQ "30!kp0!kpa!kh3@3$0$2@1$1?5HCEIL?1l").
  Hypothesis PW : ltac2:(zQ "b0!lc!so2!jta!jsf!kh3!kr4!ihf!ii6!s5!sa!kg1>1a$0>1b$0>0@3$5$0^2@4$1$4$0$3?1l>0@3$5$0^2@4$1$4$0$3?1l>0@1$9@3$8$0^4^3@2$a@2$7@2$6^5$2^4@2$7@2$6^4$2^5").
  Hypothesis DLO : ltac2:(zQ "60!ihf!ii6!jmd!ig1!uub!uv3@2$3@2$1@2$0@1$4?1d@2$2+h0+hggg0?2lo@2$1@2$0@1$5?1d@2$2+8+ogg0?2lo").
  (* [comment removed for export] *)
  Hypothesis ALB : ltac2:(zQ "40!lc!op9!toe!iic>1a$0>0@2$1?3st0^1@2$3^2@1$2?5HCEIL").

  (* [comment removed for export] *)
  Definition REL : ltac2:(zQ "30!nu4!ng8!je>1s$1>1m$2>2mo$0P") := ltac2:(zQ "i10!ig1!lc!s5!nud!nv5!m0!nvf!og7!ogf!oh8!oi1!oia!ng0!oj2!ojb!hpf!ok4!lq6!lr4!kr4!ii6!o4!hva!oke!nu4!op9!oq2!or0!nm3!or8!ng8!je!ovd\1s$he\1m$hf\2mo$h8@2$0@3$2$1@1$d^3@1$d?2s0@2$0@3$2$1@1$9^3@1$9?2s0@2$0@3$2$1@1$a^3@1$a?2s0@2$0@3$2@1$h6@2$h7@1$h5@1$5#k0@1$h5@1$5#k0@1$7^3@1$7?2s0@2$0@3$2$1@1$e^3@1$e?2s0@2$0@3$2$1@1$8^3@1$8?2s0@2$0@3$2$1@1$6^3@1$6?2s0@2$0@3$2$1@1$c^3@1$c?2s0@2$0@3$2$1@1$b^3@1$b?2s0@2$0>2sc$4>0@3$h3$4^1@1$h0@1$3^4@3$h3$4^2@1$h0?3st0@2$0>2c0$1>0@2$h4Z^1@3$2$1@1$h2@2$h1@1$3^5^2@1$h2@2$h1?3st0^2@2$0@2$i0?3mo0^1@2$0@4$hd?2s0^3?3mo0^1@2$0@7$hc?2s0^3?1d?2lo?2SP?2m0^2@2$0@4$hb?2s0^3?2m0^2@2$0@3$f\1a$1@2$h4?2SP^1?2m0^2@2$0@2$ha?3st0@1$3^3@3$f@1$h9?3st0?2m0^2").

  (* [comment removed for export] *)
  Definition CUR : ltac2:(zQ "50!hva!lc!nu4!ng8!je>1s$3>1m$4>2mo$2>2XC@1$0$1>2XB@1$0$1P") := ltac2:(zQ "h50!ig1!hva!lc!hka!nud!lv9!mh6!s5!nu4!pkb!mtf!ng8!ppa!pq5!pr1!pre!psc!je!lp4!pt5!pu8\1s$b\1m$h1\2mo$8\2XC@1$1$2\2XB@1$1$2@2$0@5$a?5HCEIL^5^2^1^4@2$0@3$7$5@1$h3@1$4^5$6@2$0@1$h2@1$4^5@2$0@2$d^5^4@2$0@1$f^4@2$0@3$c?5HCEIL^5^3@2$0@3$h0$3?1d^4@2$0@3$9?5HCEIL^5?1d@2$0@2$e?1d^3@2$h4$3^4").

  (* [comment removed for export] *)
  Definition dr_mid : ltac2:(zQ "70!hva!lc!lpc!pv3!q8!oke!kh3>1B$1>2T'@1$0$6>2st$2>2ms@1$0$1>4racc@1$0$3@1$4@2$5$2@1$0$3") := ltac2:(zQ "h02!hva!pv3!lpc!oke!q8!q1!lv9!lc!pvd!qg4!qh5!lta!qi8!lub!kh3!qj6&\1x@1$4@2$3$2@1$0$1@1$4@2$3$2@1$0$1&\1p@2$3$2@1$0$1@1$4@2$3$2@1$0$1\1B$7\2T'@1$0$e\2st$2\2ms@1$0$7\4racc@1$0$1M4~0@3$a^3^2^1\1p@2$3$2@1$0$1M3~1^1\3st1$2\5racc1@1$0$1M6\0$6@1$4@2$3$2@1$0$1@1$8@2$d^2^8@1$5@2$3$2@1$0$1M4~0@3$9^2@2$b^2^8^8\1p@2$3$2@1$0$1M3~1^1\3st2$2\3ev2@1$0$1@3$c^2^a@3$f$1^1^4@1$5@2$3$2@1$0$1@1$5@2$3$2@1$0$1").
  Lemma do_recycle_cons : ltac2:(zQ "c0!hva!kh3!lpc!pv3!mn5!q8!oke!s5!qof!qi8!jsf!kg6>2st$2>1b$1>2T'@1$0$1>4racc@1$0$3@3$7@1$5@2$6$2@1$0$3@3$9^4@3$4$1^3^2^1@5$8@1$a^3^2^4@1$b^3^1").
  Proof. reflexivity. Qed.

  (* [comment removed for export] *)
  Definition MSF : ltac2:(zQ "50!lpc!hva!pv3!q8!oke>1R>0$0>0@1$1$2@1$3@2$4$0@1$1$2>2st$0P") := ltac2:(zQ "a0!lpc!hva!pv3!q8!oke!mhd!qtd!ig1!s5!qi8\1R>0$0>0@1$1$2@1$3@2$4$0@1$1$2\2st$0>3stA$0>4racc@1$1$2>0@2$6^2?3st0@2$5$0\3stB$0@2$5@1$1$2\5raccB@1$1$2@2$7@3$8@1$3@2$4$0@1$1$2@3$9^5?3T0L^4@2^7^2^1@2$6^2^6").

  (* [comment removed for export] *)
  Definition dr_post : ltac2:(zQ "20!qv0!nu4>4msF'$0>3mo'$1P") := ltac2:(zQ "i90!m0!o4!mhd!ig1!hva!lpc!pv3!jh3!msc!mn5!hka!mob!mnc!oke!s5!lc!qv0!qtd!rg0!rg7!ng8!je!rge!q1!mme!q8!rh8!rkb!nu4!rl4!rlb!og7!nud!qi8!rq1!ru6!rue!in8!sj2!sn7!isb\4msF'$h0\3mo'$hc@2$2$h4\2s'$h4@2$2@1$1@1$0#k0\2t0@1$1@1$0#k0@2$2@1$1@1$0#k0\2t1@1$1@1$0#k0@2$2@1$1@1$0#k0\2t2@1$1@1$0#k0@2$2@1$1@1$0#k0\2a0@1$1@1$0#k0@2$2@1$1@1$0#k0\2a1@1$1@1$0#k0@2$2@1$1@1$0#k0\2a2@1$1@1$0#k0@2$2@1$1@1$0#k0\2a3@1$1@1$0#k0@2$2@1$1@1$0#k0\2a4@1$1@1$0#k0@2$2@1$1@1$0#k0\2a5@1$1@1$0#k0@2$2@1$1@1$0#k0\2a6@1$1@1$0#k0@2$2@1$1@1$0#k0\2a7@1$1@1$0#k0@2$2@1$1@1$0#k0\2t3@1$1@1$0#k0@2$2@1$1@1$0#k0\2t4@1$1@1$0#k0@2$2@1$1@1$0#k0\2t5@1$1@1$0#k0@2$2@1$1@1$0#k0\2t6@1$1@1$0#k0@2$2$h5\2m'$h5@2$3@3$he^h1^1^h2@2$3@5$hd^h1^1^h2@1$c$f@1$c$f@2$3@5$i3$a@1$h2^h1@1$h3^h1@1$hf^h1@2$hb^h3^h2@2$3@3$e$h0@3$i2@1$h2^h1@1$h3^h1^h3@7$i6@hf$i4@1$8+mrgmc@2$h6@1$0#k0?2T0?2gp?2tp^h0^f^e?3rs0?3rs1^d^c^b^a^9^8^7^6?3rs2?3rs3?3rs4?3rs5?3rs6?3rs7?3rs8?3rs9?3s10?3s11^5^4^3^2?1F@2$h6@1$0#k0+mrgmc?2fc@1$h7@1$1@1$0#k0^1@1$i7$a@2$3@4$i5$a^1?2lo?2T0@2$3@4$i8$a^1?2T0@3$9$7@1$b@1$8Z@3$9$7@1$b@1$8Z@3$9$7@1$b@1$8Z@3$9$7@1$b@1$8Z@1$c$7>3stA$5>4racc@1$4$6>0@2$h1^2?3st0@2$2$5\4stA'$5@2$2@1$4$6\5racc'@1$4$6@2$3@3$e@1$h9@2$d$5@1$4$6@3$i1^5?3T0L^4@2$h8@2$d$5@1$4$6@4$ha$5@1$4$6^2^1@2$h1^2@1$i0^h6").

  (* [comment removed for export] *)
  Hypothesis STEP_CHUNK : ltac2:(zQ "k70!m0!o4!hka!ihf!hva!lpc!s5!ii6!lc!pv3!msc!nud!ig1!qv0!rkb!mja!rge!mn5!oke!mhd!nu4!qtd!mu8!rg0!rg7!mi2!jh3!uib!umc!mgf!q1!mme!lv9!mnc!q8!rh8!mh6!pkb!uvb!mtf!ljf!lk9!uu4!og7!usf!ng8!ppa!pq5!pr1!pre!psc!toe!je!mib!pt5!vg9!mka!ml6!mm4!rq1!ru6!mob!rue!in8!sj2!pu8!sn7!isb!kr4!uta!hl3>2ra@1$1@1$0#k0>2t0@1$1@1$0#k0>2t1@1$1@1$0#k0>2t2@1$1@1$0#k0>2a2@1$1@1$0#k0>2a3@1$1@1$0#k0>2a4@1$1@1$0#k0>2a5@1$1@1$0#k0>2a6@1$1@1$0#k0>2a7@1$1@1$0#k0>2x2@1$1@1$0#k0>2x3@1$1@1$0#k0>2x4@1$1@1$0#k0>2x5@1$1@1$0#k0>2x6@1$1@1$0#k0>2x7@1$1@1$0#k0>2x8@1$1@1$0#k0>2x9@1$1@1$0#k0>2t3@1$1@1$0#k0>2t4@1$1@1$0#k0>2t5@1$1@1$0#k0>2t6@1$1@1$0#k0>1m$j4>3msF$d>2mo$h4>1s$id>2XC@1$4$8>2XB@1$4$8>2ch$h9>0@5$i7?5HCEIL^4@3$h1$8@1$f^1^3^2^7>0@3$k4$h9^2@1$j9@1$b^5>0@3$6$ja@1$j8^3$j5>0@3$6$i0@1$j6@1$b^7$i4>0@2$c@2$if^8^b@1$j1^b>0@3$ie?5HCEIL^9^a>0@3$j2$2?1d^d>0@3$i5?5HCEIL^b?1d>0@2$j0?1d^d>0@2$k1$2^h0>0@2$7@1$j3?5HCEIL?2lo>0@2$7@2$3?2lo+ji0?3spv>0@2$7@2$3?3spv+h0@2$hd+2+if>0@3$6$8@2$k5?3spv+h0Z>0@4$jf$2^h5?2lo?3spv>0@3$6$8@2$k6@1$0#k0?2tp$ia>0@2$7@2$3@1$i9@1$b^h4+kqgg0$i8>0@2$c@2$7?3spv@2$3?3spv+8@2$7@2$3@2$3?3spv+8+8@2$hd+2+jf>0@4$k3$2^h9@2$3?3spv+8@3$h1$ha@1$jd@1$a@1$ic^h6@1$i1$ha>0@5$jc$2@1$h7^h7@1$h8^h7@1$ib^h7@2$e^h9^h8>0@3$6$d@3$jb@1$h7^h8@1$h8^h8^ha@7$k0@hf$je^j1?2sp?2gp?2tp^j0^if^ie@2$h0@1$0#k0?2T0@1$a$h6@1$a@2$3?3spv+8@1$a@1$f^h5^id^ic^ib^ia^i9^i8^i7^i6^i5^i4^i3^i2^i1^i0?3s10?3s11^hf^he^hd^hc?1F@2$h0@1$0#k0+mrjpc?2fc@1$he@1$1@1$0#k0^hb@1$k2$2>0>4msF'$d>3mo'$h4>0@he$i6?5HCEIL^j4?2sp?2gp?2tp@2$h0@1$0#k0?2T0@1$a$h6^ia^i9^i8^i7^i6^i5^i4^i3?3s10?3s11?1F?2fc^hb?1d?2lo^he^hc^ha^h9^h9\3st'$5>3stA$5>0@2$h5^1@1$b^hd@2$h3$5\4stA'$5@2$h3@1$4$9\2ev@1$4$9@2$c@3$6@1$i2@2$h2$5@1$4$9@2$j7^4@1$f^hd@2$hf@2$h2$5@1$4$9@4$i3$5@1$4$9^2^1@2$h5^2^5^2^1@4$hb$2$hc?1Q@2$e^3^2@4$hb$2$hc?1Q@2$e^hc^hb").

  Hypothesis STEP_BATCH : ltac2:(zQ "k40!m0!o4!hva!lc!hka!lpc!s5!msc!pv3!mg0!nud!ii6!qv0!rkb!mu8!ihf!rge!oke!ig1!mhd!nu4!qtd!rg0!rg7!vh7!uib!umc!q1!mme!lv9!mn5!q8!rh8!mh6!pkb!uvb!mtf!ljf!lk9!uu4!og7!usf!ng8!inf!ppa!pq5!pr1!pre!psc!toe!je!jne!pt5!qg4!lta!su6!rq1!ru6!rue!in8!sj2!pu8!sn7!ki5!uta!mgf!tgc!hl3>2ra@1$1@1$0#k0>2t0@1$1@1$0#k0>2t1@1$1@1$0#k0>2t2@1$1@1$0#k0>2a4@1$1@1$0#k0>2a5@1$1@1$0#k0>2a6@1$1@1$0#k0>2a7@1$1@1$0#k0>2x2@1$1@1$0#k0>2x3@1$1@1$0#k0>2x4@1$1@1$0#k0>2x5@1$1@1$0#k0>2x6@1$1@1$0#k0>2x7@1$1@1$0#k0>2x8@1$1@1$0#k0>2x9@1$1@1$0#k0>2t3@1$1@1$0#k0>2t4@1$1@1$0#k0>2t5@1$1@1$0#k0>2t6@1$1@1$0#k0>1m$j2>3msF$c>2mo$h4>1s$ia>2XC@1$2$3>2XB@1$2$3>1p$3>0@5$i4?5HCEIL^4^3@3$he$3^1^2^7>0@3$6$3@2$j6@1$a^5^2$9>0@3$6$hd@1$j4@1$a^6$i1>0@2$h2@2$id^7^a@1$if^a>0@3$ic?5HCEIL^8^9>0@3$j0$4?1d^c>0@3$i2?5HCEIL^a?1d>0@2$ie?1d^c>0@2$jd$4^f>0@2$b@1$j1?5HCEIL?2lo>0@2$b@2$f?2lo+ir0?3spv>0@2$b@2$f?3spv+h0@2$k1+2+if>0@3$6$3@2$k0?3spv+h0Z>0@4$jb$4^h4?2lo?3spv>0@3$6$3@2$k3@1$0#k0?2tp$i7>0@3$ib^h6^h0@1$h8$9>0@4$j3^h7^h1@1$k2@2$jf@1$h8$9+8$j7>0@2$b@2$f@1$i6@1$a^h5+kqgg0$i5>0@5$j9$4@1$h6^h6@1$h7^h6@1$i8^h6@2$d^h8^h7>0@3$6$c@3$j8@1$h6^h7@1$h7^h7^h9@7$jc@hf$ja^ie?2sp?2gp?2tp^id^ic^ib@2$h0@1$0#k0?2T0@1$7$e@1$7@1$i9^h7@1$7$e@1$7$9@1$7^h4^ia^i9^i8^i7^i6^i5^i4^i3^i2^i1^i0^hf?3s10?3s11^he^hd^hc^hb?1F@2$h0@1$0#k0+mrnq0?2fc@1$hb@1$1@1$0#k0^ha@1$je$4>0>4msF'$c>3mo'$h4>0@he$i3?5HCEIL^j1?2sp?2gp?2tp@2$h0@1$0#k0?2T0@1$7$e^i9^i8^i7^i6^i5^i4^i3^i2?3s10?3s11?1F?2fc^ha?1d?2lo^hd^hb^h9^h8^h8\3st'$5>3stA$5>0@2$h5^1@1$a^hc@2$h3$5\4stA'$5@2$h3@1$2$8\2ev@1$2$8@2$h2@3$6@1$hf@2$h1$5@1$2$8@3$j5^4$9^hc@2$hc@2$h1$5@1$2$8@4$i0$5@1$2$8^2^1@2$h5^2^5^2^1@4$h9$4$ha?1Q@2$d^3^2@4$h9$4$ha?1Q@2$d^hb^ha").


  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition TOK : ltac2:(zQ "20!hva!kh3>1T@1$0$1P") := ltac2:(zQ "h00!kh3!lc!ig1!jsf!kp0!so2!kr4!hva!s5!kpa!nha!lta!mg0!so9!iic!mgf\1T@1$7$0@2$2@3$4$0@1$9?5HCEIL^1@2$2@2$d$1@4$5$0$1$3^1@2$2>1x$0>0@3$6$0^1^2@3$6$1@1$3^2@4$5$0$1$3?1l@2$2@2$e@1$a^1@2$f+2+je@3$4$0\1b$0@3$8$1@2$b?3st0@1$3^1$c^1").

  (* [comment removed for export] *)
  Definition memB : ltac2:(zQ "50!hva!kh3!m0!je!o4>1m$3>1b$1>2T'@1$0$1>2j0@1$0@1$4@1$2#8P") := ltac2:(zQ "i32!jh3!jsf!msc!mn5!mob!ig1!lc!kh3!hka!ihf!so2!hva!mnc!jta!ju8!isb!sp2!m0!sta!kn1!nha!mo2!je!jne!su6!kg6!ngf!khd!jm3!in8!tg4!ki5!jmd!tgc!o4&@1$2@3$h0$6Z@4$a$7$6$1^2&@1$4~0\1m$h6\1b$7\2T'@1$b$7\2j0@1$b@1$i2@1$h1#8@2$5@4$f$8^4?2T0@3$3$0@1$4@1$2@2$hb$7^2@3$3$0~1@3$3$0@1$4@1$2@3$he$6@4$a$7$6$1^2Z@3$3$0@1$4@1$2@1$h4^2@1$c$0@2$5@3$h3^4^2Z@2$5@h0$h2^4?3spv^1?2ca?2cs?3rs9?3rs8?3rs7?3rs6?3rs5?3rs4?3rs3?3rs2?3rs1?3rs0@1$2+mrgmc@2$5@4$f$8^4@1$1^3@3$3$0~1@3$3$0@1$4@1$2@1$ha^3@3$3$0@1$4@1$2@1$e^3@1$c$0@2$5@4$hc$8^4@2$9@1$1^3+h8@1$h5@1$h9^3@2$5@4$hd$8^4@2$9@2$9@1$1^3+h8@2$i0+8@1$e^3@2$9@1$1^3$d@4$h7^4@1$1^3@1$i1@2$hf$d+8$h8").

  (* [comment removed for export] *)
  Definition HEADINV : ltac2:(zQ "90!m0!o4!hva!lc!qv0!nu4!ng8!je!kh3>1T@1$2$8>1s$6>1m$7>2mo$5>3msF$4>2XC@1$2$3>2XB@1$2$3>2j0@1$2@1$1@1$0#8>3rax@1$1@1$0#k0>2t0@1$1@1$0#k0>2t1@1$1@1$0#k0>2t2@1$1@1$0#k0>2a1@1$1@1$0#k0>2a2@1$1@1$0#k0>2a3@1$1@1$0#k0>2a4@1$1@1$0#k0>2a5@1$1@1$0#k0>2a6@1$1@1$0#k0>2a7@1$1@1$0#k0>2x4@1$1@1$0#k0>2x6@1$1@1$0#k0>2x7@1$1@1$0#k0>2x8@1$1@1$0#k0>2x9@1$1@1$0#k0>2t3@1$1@1$0#k0>2t4@1$1@1$0#k0>2t5@1$1@1$0#k0>2t6@1$1@1$0#k0P") := ltac2:(zQ "i20!m0!o4!ig1!lc!hva!kh3!qv0!hka!rg0!rg7!tj2!s5!so2!rkb!nu4!rl4!tk1!rlb!tk8!tkf!tle!og7!nud!ng8!je!lpc!qi8!pv3!jsf!kg6!rq1!ru6!in8!tmc\1T@1$4$5\1s$h7\1m$h8\2mo$e\3msF$6\2XC@1$4$3\2XB@1$4$3\2j0@1$4@1$1@1$0#8\3rax@1$1@1$0#k0\2t0@1$1@1$0#k0\2t1@1$1@1$0#k0\2t2@1$1@1$0#k0\2a1@1$1@1$0#k0\2a2@1$1@1$0#k0\2a3@1$1@1$0#k0\2a4@1$1@1$0#k0\2a5@1$1@1$0#k0\2a6@1$1@1$0#k0\2a7@1$1@1$0#k0\2x4@1$1@1$0#k0\2x6@1$1@1$0#k0\2x7@1$1@1$0#k0\2x8@1$1@1$0#k0\2x9@1$1@1$0#k0\2t3@1$1@1$0#k0\2t4@1$1@1$0#k0\2t5@1$1@1$0#k0\2t6@1$1@1$0#k0@2$2@3$h1^hb^ha^h9@2$2@5$f^hb^ha^h9^h7^h6@2$2@4$i0$7^ha?2lo?3spv@2$2@3$a$3^h7@4$i1$5$3$hd^hc@2$2@3$a$3^h6@4$c$5$3$hc^hc@2$2@1$h2^hc@2$2@h0$h3?2sp?3rs0?3rs1?3rs2?3rs3?3rs4?3rs5?3rs6?3rs7?3rs8?3rs9?2ca?2cs^ha^hc^h5@2$2@2$h0\3stB$h9\5raccB@1$4$hb@3$ha^2^he^1@1$h6^hb@2$2@5$hf$7@1$8^hb@1$9^hb@1$h5^hb@2$d^h8^h9@3$b$6@3$he@1$8^hb@1$9^hb^h8@he$h4?2sp?2gp?2tp?1F?2fc?3s10?3s11^h4^h3^h2^h1^h0^f^e^d^c^b^a^9^8^7^6^5^4^3^2^1^hc+mritc^ha").

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma REL_refl : ltac2:(zQ "20!or8!rlb>0@4$0?2s0?2s0?3mo0?3mo0@3$1?2s0?2m0?3mo0").
  Proof.
    intros AV. unfold REL. repeat (split; [reflexivity|]). split; [intros sc Hsc; exact Hsc|]. split; [intros c0 _; reflexivity|].
    split; [apply nonvm_same_refl|]. split; [exact AV|]. split; [apply acompl_refl|]. split; [apply avis_of_wmono; apply wmono_refl|]. split; [apply agree_on_refl|].
    split; [apply alive_kept_refl| apply agree_on_refl].
  Qed.

  (* [comment removed for export] *)
  Lemma agree_of_acompl : ltac2:(zQ "70!lc!ng8!je!sa!nm3!tn8!hpf>1P>0$0P>1s$1>2s'$1>3SPx$0>1m$2>2m'$2>0@7$4^5^4?1d?2lo^3^2^1>0>1a$0>0@1^8^1@1$3@6$5^8^7?1d?2lo^6^2@3$6^8^4^3").
  Proof. intros P s s' SPx m m' A NW x Hx Hr. exact (A x Hr (NW x Hx)). Qed.

  (* [comment removed for export] *)
  Lemma above_not_awrit : ltac2:(zQ "b0!nv5!ii6!lc!nud!ng8!ok4!kr4!sa!tn8!to1!toe>1s$4>2s'$4>3SPx$2>1a$2>0@2$9?5HCEIL^4>0>2sc$0>0@3$6$0^1@1$5@1$3^5@3$6$0^2@1$5@1$3^7>0@2$1@1$a?5HCEIL^4>0@2$1?2lo^5>0@2$1^6^5@1$7@6$8^9^8?1d?2lo^7^6").
  Proof.
    intros s s' SPx a PL SUB AC LS Ha W. pose proof aceil_range as ACR. pose proof DLO as [D1 D2].
    npose PL as (S1 & S2 & S3 & P1 & P2 & P3 & T1 & T2 & T3 & X1 & X2 & X3 & _ & _ & _ & _ & _ & F1 & F2 & _ & _ & _ & _ & SEC & SEC2 & TCX).
    unfold awrit, astatw in W. unfold a_sb, kSpaceSize, kPageSize, kPtrArrayReserve, AINST, AIAINIT, AIAINST, sh, ASHADOW_BASE in *.
    destruct W as [H|[H|[H|[H|[H|[H|[H|H]]]]]]].
    - clear - H Ha. olia.
    - clear - H Ha T3 AC. olia.
    - clear - H Ha S3 AC. olia.
    - clear - H Ha S3 AC ACR. olia.
    - clear - H Ha P3 AC. olia.
    - ndestruct H as (sc & I & R). assert (I' : In sc (as_sec (a_st s))) by (destruct I as [I|I]; [exact I| exact (SUB sc I)]).
      npose (SEC sc I') as (_ & _ & G & _). clear - R Ha G AC ACR. olia.
    - clear - H Ha AC ACR. olia.
    - clear - H Ha D1 D2 LS. olia.
  Qed.

  (* [comment removed for export] *)
  Lemma batch_in_pendz : ltac2:(zQ "h00!lc!ig1!jna!jta!ihf!ii6!iic!hva!s5!kg1!tp5!lpc!lta!mg0!kr4!ki5>2st$b>2PZ@1$7$0>1x$0>1a$0>0@3$e$0^2^3>0@3$8$0@2$c^5^3$d>0@2$9@2$1@2$5^4^3@2$6^3@2$4^4$3@2$1@2$5@1$2^4^3@2$6^3@2$4@1$2^4@2$f$3+8@3$a^7^6^4").
  Proof.
    intros st PZ x a Hx CL R. exists x. split; [exact Hx|]. rewrite CL. change (class_size kBatchClass) with kBatchSize. exact R.
  Qed.

  Lemma TOK_tail : ltac2:(zQ "40!kh3!tk8!mn5!hva>1b$0>1T@1$3$0>0@1$1@3$2$0^2^1@1$1^2").
  Proof.
    (intros b T nd_i7; ndestruct nd_i7 as (K1 & K2 & K3 & K4 & K5)). apply Forall_cons_iff in K1. apply Forall_cons_iff in K5. cbn [map] in K2. apply List.NoDup_cons_iff in K2.
    split; [exact (proj2 K1)|]. split; [exact (proj2 K2)|]. split; [intros x Hx; apply K3; right; exact Hx|].
    split; [pose proof (bsum_cons_le b T (proj1 K1)); clear - H K4; olia| exact (proj2 K5)].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition wlocal : ltac2:(zQ "20!hva!tpe>1W@1$0$1P") := ltac2:(zQ "80!lc!tpe!ii6!tq5!hva!tqb!ig1!kp0\1W@1$4$1@3$7$1\2iv$1@2$6@2$2?3spv@3$3$0$0^1@2$2@3$5$0$0^1?2SP^1").

  Lemma outside_below : ltac2:(zQ "60!hva!lc!tr1!tpe!trb!iic>1W@1$0$3>1a$1>0@1$2^2>0@2$5^2?3spv@2$4^4^3").
  Proof.
    intros W a FW Ha. induction W as [|[x y] W IH]; [exact I|]. apply Forall_cons_iff in FW. destruct FW as [F1 F2]. cbn [fst snd] in F1.
    split; [clear - F1 Ha; olia| exact (IH F2)].
  Qed.
  Lemma outside_above : ltac2:(zQ "60!hva!lc!tr1!tpe!trb!ii6>1W@1$0$3>1a$1>0@1$2^2>0@2$5?2SP^2@2$4^4^3").
  Proof.
    intros W a FW Ha. induction W as [|[x y] W IH]; [exact I|]. apply Forall_cons_iff in FW. destruct FW as [F1 F2]. cbn [fst snd] in F1.
    split; [clear - F1 Ha; olia| exact (IH F2)].
  Qed.

  Lemma flagsx_local : ltac2:(zQ "b0!m0!pre!o4!hva!q8!tr1!hka!je!tpe!ts6!tsf>1W@1$3$8>1m$7>2m'>0@1$2@1$0#k0@1$4@1$2@1$0#8>0@1$1^2>0@1$5^4>0@3$9^5^4^3>0@3$a$6^5^4@1$1^5").
  Proof.
    intros W m m' FX FW MU WM. pose proof (munch_agree _ _ _ MU) as AG. pose proof aceil_range as ACR.
    assert (ZT : forall a, a < AIMG_TOP -> outside W a) by (intros a Ha; apply (outside_below W a FW); clear - Ha ACR LO HI; unfold AIMG_TOP, spv in *; olia).
    ndestruct FX as (FXa & FXb & [g FXc] & FXd & [bb FXe]). unfold flagsx_rep. unfold ALIBCPGSZ, AGOT_SSP, ASSPGUARD, ACFLAGS, AIMG_TOP in *.
    split; [| split; [| split; [exists g| split; [| exists bb]]]];
      (eapply (rw_cells_transport_pt _ m m' AG WM); [eassumption|]; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; intros a Ha; apply ZT; clear - Ha; olia).
  Qed.

  Lemma stk_local : ltac2:(zQ "c1!m0!o4!hka!q8!in8!hva!lc!tr1!tpe!ts6!tsf!ii6&>0@1$1@1$0#k0@1$3@1$1@1$0#8>1W@1$5$8>1m~0>2m'~0>1x$6>0@4$4$2^3?2lo^1>0@1$7^5>0@2$b^3?3spv>0@3$9^7^6^5>0@3$a$2^7^6@4$4$2^7?2lo^6").
  Proof.
    intros W m m' x ST FW LE MU WM. eapply (stk_transport_pt _ m m' (munch_agree _ _ _ MU) WM); [exact ST|]. intros a Ha. apply (outside_below W a FW). clear - Ha LE; olia.
  Qed.

  Lemma CUR_local : ltac2:(zQ "h00!hva!m0!lc!nu4!rl4!hka!o4!q8!tr1!ng8!je!tt8!tpe!ts6!tsf!pu8>1s$9>1m$a>2mo$3>2XC@1$0$2>2XB@1$0$2>1W@1$0$c>2m'>0@1$6@1$1#k0@1$7@1$6@1$1#8>3mo'$3>0@5$4^8^7^6^5^4>0@1$8^4>0@3$d^5^9^4>0@3$e$5^a^5>0@2$f$5^6>0@2$b^b^6@5$4^e^8^7^b^a").
  Proof.
    (intros s m mo XC XB W m' mo' nd_i8 FW MU WM MI' SBM; ndestruct nd_i8 as (RQ & INIT & NM & AWV & FXR & AMX & DEP & DPL & DCOV & MI)). pose proof aceil_range as ACR.
    split; [| split; [exact INIT| split; [exact NM| split; [exact (awin_vis_wmono s m m' AWV WM)| split; [exact (flagsx_local W m m' FXR FW MU WM)| split; [exact (AMODELX_mat s mo mo' AMX SBM)| split; [| split; [exact DPL| split; [exact (depot_cov_mat d mo mo' DCOV SBM)| exact MI']]]]]]]]].
    - eapply AREPQ_frame; [exact RQ| exact MU| exact WM|]. unfold awin_ok. apply Forall_forall. intros [x y] Hin a Ha.
      apply (stack_not_afootQ s XC XB (conj (AREPQ_placed _ _ _ _ RQ) (AREPQ_WFQ _ _ _ _ RQ))).
      pose proof (proj1 (Forall_forall _ _) FW (x, y) Hin) as [F1 F2]. cbn [fst snd] in F1, F2, Ha. clear - F1 Ha LO HI; unfold spv in *; olia.
    - eapply DEPOT_transport; [exact DEP| exact MU| exact WM|]. pose proof DLO as [D1 D2]. unfold depot_avoid, avoids.
      repeat split; apply Forall_forall; intros [x y] Hin; pose proof (proj1 (Forall_forall _ _) FW (x, y) Hin) as [F1 F2]; cbn [fst snd] in F1, F2 |- *;
        clear - F1 D1 D2 ACR LO HI; unfold spv in *; olia.
  Qed.

  Lemma REL_local : ltac2:(zQ "e0!m0!nu4!rlb!o4!hva!q8!tr1!hka!ng8!je!tt8!tpe!ts6!tsf>1s$8>1m$9>2mo$1>1W@1$4$b>2m'>0@1$3@1$0#k0@1$5@1$3@1$0#8>3mo'$1>0@3$2^6^5^4>0@1$6^4>0@3$c^5^7^4>0@3$d$7^8^5>0@2$a^8^5@3$2^b^7^6").
  Proof.
    intros s m mo W m' mo' RL FW MU WM SBM.
    npose RL as (Et & Ec & Ef & Ez & Etp & Ebt & Eal & Esb & Epa & SUBS & AU & NVS & AVM & ACM & AVS & AGS & ALK & AGA).
    unfold REL. split; [exact Et|]. split; [exact Ec|]. split; [exact Ef|]. split; [exact Ez|]. split; [exact Etp|]. split; [exact Ebt|].
    split; [exact Eal|]. split; [exact Esb|]. split; [exact Epa|]. split; [exact SUBS|]. split; [exact AU|].
    split; [eapply nonvm_same_trans; [exact NVS| apply nonvm_same_mat; exact SBM]|].
    split; [eapply avmx_mat_r; [exact AVM| exact SBM]|].
    split.
    { apply (acompl_trans s0 s s d lo SP m0 m m' (conj Et (conj Esb Epa)) SUBS ACM).
      apply (acompl_of_munchF s s d lo SP W m m' MU). apply Forall_forall. intros [x y] Hin a Ha.
      pose proof (proj1 (Forall_forall _ _) FW (x, y) Hin) as [F1 F2]. cbn [fst snd] in F1, F2, Ha. unfold awrit. left. clear - F1 F2 Ha LO HI; unfold spv, SP in *; olia. }
    split; [apply (avis_trans s0 s s m0 m m' SUBS (fun sc H => H) AVS); apply avis_of_wmono; exact WM|].
    split; [eapply agree_on_trans; [exact AGS|]; intros a Ha Hr; apply (munch_agree _ _ _ MU a); [| exact Hr]; apply (outside_above W a FW); exact Ha|].
    split; [exact ALK|].
    eapply agree_on_trans; [exact AGA|]. intros a Ha Hr. apply (munch_agree _ _ _ MU a); [| exact Hr]. apply (outside_below W a FW).
    pose proof (ALB a Ha) as B. clear - B LO HI. unfold spv. olia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma batch_phase : ltac2:(zQ "j00!m0!o4!lc!hva!kh3!hka!msc!qv0!rkb!jsf!nu4!mu8!uib!umc!mn5!mnc!s5!rg0!rg7!ng8!je!tj2!ihf!rge!q1!sa!so2!rl4!und!tk1!rlb!tk8!qof!uo8!up3!og7!nud!lpc!pv3!upb!kg6!rq1!ru6!rue!in8!sj2!sn7!tmc>1b$4>2T'@1$3$4>2XC@1$3$2>2XB@1$3$2>1s$h3>1m$h4>2mo$a>3msF$7>2j0@1$3@1$1@1$0#8>3rax@1$1@1$0#k0>2t0@1$1@1$0#k0>2t1@1$1@1$0#k0>2t2@1$1@1$0#k0>2a0@1$1@1$0#k0>2a1@1$1@1$0#k0>2a2@1$1@1$0#k0>2a3@1$1@1$0#k0>2a4@1$1@1$0#k0>2a5@1$1@1$0#k0>2a6@1$1@1$0#k0>2a7@1$1@1$0#k0>2x6@1$1@1$0#k0>2x7@1$1@1$0#k0>2x8@1$1@1$0#k0>2x9@1$1@1$0#k0>2t3@1$1@1$0#k0>2t4@1$1@1$0#k0>2t5@1$1@1$0#k0>2t6@1$1@1$0#k0>0@3$he^h9^h8^h7>0@5$hb^ha^h9^h8^hc^hb>0@4$ic$5^ha?2lo?3spv>0@3$h5$2^he@4$if$4$2$i8^hf>0@3$h5$2^he@3$e$2@1$9^i1@4$ha$4$2$9^i0>0@1$hf@3$e$4^i2^i1>0@4$i2^he^i3^i2^hb>0@2$hd\3stB$i5\5raccB@1$3$i6@5$i0@1$9^i6^i5^2@1$f$2^1@1$i4^i0>0@5$ia$5@1$h1^i1@1$h2^i1@1$i3^i1@2$8^he^hf>0@3$h0$7@3$i9@1$h1^i2@1$h2^i2^hf@7$id@hf$ib^hd?2sp?2gp?2tp^hc^hb^ha@2$h7@1$0#k0?2T0@1$6$b^h9^h8^h7^h6^h5^h4^h3^h2@1$6@2$h6$b+k0@1$6@2$h6$b+ir0@1$6@1$9^i6@1$6$i7^h1^h0^f^e?3s10?3s11^d^c^b^a?1F@2$h7@1$0#k0+mrjj4?2fc@1$h8@1$1@1$0#k0^i1@1$ie$5>0>0@1$h9@3$h0@1$3$4^i6@1$f$4>2s'$h3>2m'$h4>3mo'$a>4msF'$7>3XC'@1$3$2>3XB'@1$3$2>3j0'@1$3@1$1@1$0#8>4rax'@1$1@1$0#k0>3t0'@1$1@1$0#k0>3t1'@1$1@1$0#k0>3t2'@1$1@1$0#k0>3a1'@1$1@1$0#k0>3a2'@1$1@1$0#k0>3a3'@1$1@1$0#k0>3a4'@1$1@1$0#k0>3a5'@1$1@1$0#k0>3a6'@1$1@1$0#k0>3a7'@1$1@1$0#k0>3x4'@1$1@1$0#k0>3x6'@1$1@1$0#k0>3x7'@1$1@1$0#k0>3x8'@1$1@1$0#k0>3x9'@1$1@1$0#k0>3t3'@1$1@1$0#k0>3t4'@1$1@1$0#k0>3t5'@1$1@1$0#k0>3t6'@1$1@1$0#k0>0@hc$hc^k2^hb^ha^h9^h8^h7^h6^h5^h4^h3^h2^h1^h0^f^e^d^c^b^a^9^8^7^6^5^4^3^2^1@4$c$5$d?1Q@2$8^h9^ha>0>4msF'$7>3mo'$a>0@2$i1^2^1@4$c$5$d?1Q@2$8^3^2@4$c$5$d?1Q@2$8^i2^i3").
  Proof.
    intros b T' XC XB s m mo msF j0 rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x6 x7 x8 x9 t3 t4 t5 t6.
    intros RL CU ST PXC PXB TK MB MF OK VIS HK K.
    ndestruct CU as (RQ & INIT & NM & AWV & FXR & AMX & DEP & DPL & DCOV & MI).
    npose RL as (Et & Ec & Ef & Ez & Etp & Ebt & Eal & Esb & Epa & SUBS & AU & NVS & AVM & ACM & AVS & AGS & ALK & AGA).
    ndestruct TK as (OKT & NDT & SUBT & BST & CLT).
    ndestruct MB as (HT & BSG & FR & HB & ARR & STB & POI).
    pose proof (AREPQ_placed _ _ _ _ RQ) as PL. pose proof (AREPQ_WFQ _ _ _ _ RQ) as WQ.
    pose proof (bv_unsigned_in_range _ sp) as SPR; change (bv_modulus 64) with (2^64) in SPR.
    pose proof aceil_range as ACR.
    assert (CLb : class_of_addr (a_st s) (qb_addr b) = kBatchClass).
    { rewrite (class_of_addr_sb st0 (a_st s)) by exact Esb. exact (Forall_inv CLT). }
    assert (INb : In (qb_addr b) XB) by (eapply Permutation_in; [apply Permutation_sym; exact PXB| left; reflexivity]).
    destruct (xb24_facts _ _ _ _ WQ INb CLb) as (off & OFF & EB & PRIM).
    pose proof (Forall_inv OKT) as OKb. npose OKb as (Kb1 & Kb2 & Kb3 & Kb4 & Kb5 & Kb6 & Kb7).
    npose PL as (S1 & S2 & S3 & PLrest).
    assert (ECA : a_cache s = a_cache s0) by (unfold a_cache; rewrite Et; reflexivity).
    (* [comment removed for export] *)
    eapply (evt_sreach_lazy_at asegs (a_L s) (a_S s) (a_Zr s) _ msF _ mo Q OK VIS).
    { eapply (dr_call_batch sp gp tp F fc rs0 rs1 rs2 rs3 rs4 rs5 rs6 rs7 rs8 rs9 s10 s11 ca cs (qb_addr b) (a_sb s) kBatchClass off).
      - exact MI.
      - exact S2.
      - exact S3.
      - unfold kBatchClass; clear; olia.
      - exact OFF.
      - exact EB.
      - exact (arepq_sb_cell _ _ _ _ RQ).
      - exact FR. }
    cbv beta. intros msF1 mo1 OK1 SBM1 _ VIS1.
    (* [comment removed for export] *)
    pose proof (AMODELX_mat s mo mo1 AMX SBM1) as AMX1. pose proof (depot_cov_mat d mo mo1 DCOV SBM1) as DCOV1.
    apply (STEP_BATCH (wz 0x6b360) t0 t1 t2 a4 a5 a6 a7 (wz (AINST + 64)) (wz (AINST + 688)) (wz (qb_addr b)) (wz kSpaceSize) x6 x7 x8 x9 t3 t4 t5 t6
             m msF1 mo1 s XC (map qb_addr T') (qb_addr b)).
    - eapply AREPQ_perm; [apply Permutation_refl| exact PXB| exact RQ].
    - exact CLb.
    - exact INIT.
    - exact (conj AWV FXR).
    - exact AMX1.
    - exact DEP.
    - exact DPL.
    - exact DCOV1.
    - exact MI.
    - exact LO.
    - clear - HI; unfold spv in *; olia.
    - clear - SPT; unfold spv in *; olia.
    - exact SPA.
    - exact ST.
    - exact TPv.
    - change (class_size kBatchClass) with kBatchSize. exact (batch_junk m b _ OKb HB ARR STB).
    - change (class_size kBatchClass / 8) with (kBatchSize / 8). exact POI.
    - exact (PROOM_of_NUM _ _ _ WQ NM).
    - exact OK1.
    - rewrite VIS1. unfold ca. rewrite ECA. reflexivity.
    - cbv beta. intros msF2 mo2 POST.
    ndestruct POST as (s2 & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2
                      & Et2 & Ec2 & Ef2 & Ez2 & Etp2 & Ebt2 & Eal2 & Esb2 & Epa2 & SUB2 & INIT2 & AU2 & OK2 & VIS2
                      & RQ2 & AWV2 & FXR2 & AMX2 & NVS2 & AVM2 & DCOV2 & DEP2 & DPL2 & MI2 & ST2 & ACM2 & AVS2 & AGP2 & ALK2 & AGA2 & MOD2).
    change (ret_pc (wz 0x6b360)) with (ret_pc (Z_to_bv 64 0x6b360)) in VIS2. rewrite (ret_pc_even 0x6b360) in VIS2 by (clear; olia).
    (* [comment removed for export] *)
    assert (AGS2 : agree_on (fun a => spv <= a) m m2).
    { apply (agree_of_acompl _ s s2 spv m m2 ACM2). intros a Ha. apply (above_not_awrit s s2 spv a PL SUB2); [clear - LO HI ACR; unfold spv in *; olia| clear - HI; unfold spv in *; olia| exact Ha]. }
    npose (TOK_tail b T' (conj OKT (conj NDT (conj SUBT (conj BST CLT))))) as (OKT' & NDT' & SUBT' & BST' & CLT').
    assert (HM2 : dr_head_mem sp rs0 rs1 rs2 rs3 rs4 rs5 rs6 rs7 rs8 rs9 ca cs m2 T' j0).
    { split; [| split].
      - eapply (rw_cells_transport_pt2 _ m m2 AGS2); [exact HT|]. cbn [cells_size csize Nat.add]. intros a Ha. unfold T0, spv in *. clear - Ha; olia.
      - eapply (bseg_transport_pt2 _ m m2 AGP2); [| exact OKT'| exact BSG].
        intros b0 a Hb0 Ha. apply (batch_in_pendz (a_st s) (map qb_addr T') (qb_addr b0) a); [apply in_map; exact Hb0| | exact Ha].
        rewrite (class_of_addr_sb st0 (a_st s)) by exact Esb. exact (proj1 (Forall_forall _ _) CLT' b0 Hb0).
      - unfold dr_frame in FR |- *. eapply (rw_cells_transport_pt2 _ m m2 AGS2); [exact FR|]. intros a Ha. unfold spv in *. clear - Ha; olia. }
    (* [comment removed for export] *)
    eapply (evt_sreach_lazy_at asegs (a_L s2) (a_S s2) (a_Zr s2) _ msF2 _ mo2 Q OK2 VIS2).
    { eapply (dr_loop_test sp gp tp F fc rs0 rs1 rs2 rs3 rs4 rs5 rs6 rs7 rs8 rs9 s10 s11 ca cs lo); [| exact MI2| exact OKT'| exact BST'| exact HM2| exact ST2].
      clear - HI; unfold spv in *; olia. }
    cbv beta. intros msF3 mo3 OK3 SBM3 _ VIS3.
    (* [comment removed for export] *)
    assert (RL2 : REL s2 m2 mo3).
    { unfold REL. rewrite Et2, Ec2, Ef2, Ez2, Etp2, Ebt2, Eal2, Esb2, Epa2.
      split; [exact Et|]. split; [exact Ec|]. split; [exact Ef|]. split; [exact Ez|]. split; [exact Etp|]. split; [exact Ebt|].
      split; [exact Eal|]. split; [exact Esb|]. split; [exact Epa|].
      split; [intros sc Hsc; exact (SUBS sc (SUB2 sc Hsc))|].
      split; [intros c0 Hc0; rewrite (AU2 c0 Hc0); exact (AU c0 Hc0)|].
      split; [eapply nonvm_same_trans; [exact NVS| eapply nonvm_same_trans; [apply nonvm_same_mat; exact SBM1| eapply nonvm_same_trans; [exact NVS2| apply nonvm_same_mat; exact SBM3]]]|].
      split; [apply (avmx_trans s0 s s2 mo0 mo mo3 SUBS SUB2 AVM);
              eapply avmx_mat_r; [eapply avmx_mat_l; [exact SBM1| exact AVM2]| exact SBM3]|].
      split; [apply (acompl_trans s0 s s2 d lo SP m0 m m2 (conj Et (conj Esb Epa)) SUBS ACM); apply (acompl_SP_mono s s2 d lo spv SP m m2); [unfold SP, spv; clear; olia| exact ACM2]|].
      split; [exact (avis_trans s0 s s2 m0 m m2 SUBS SUB2 AVS AVS2)|].
      split; [eapply agree_on_trans; [exact AGS|]; eapply agree_on_weaken; [| exact AGS2]; intros a Ha; unfold SP, spv in *; clear - Ha; olia|].
      split; [exact (alive_kept_trans _ _ _ ALK ALK2)| exact (agree_alive_trans st0 (a_st s) m0 m m2 ALK AGA AGA2)]. }
    pose proof (NUM_au _ _ AU2 NM) as NM2.
    pose proof (AMODELX_mat s2 mo2 mo3 AMX2 SBM3) as AMX3. pose proof (depot_cov_mat d mo2 mo3 DCOV2 SBM3) as DCOV3.
    assert (MF2 : MSF (fun stB raccB => do_recycle stB T' raccB) (a_st s2)).
    { intros stA racc SA. ndestruct (MF stA racc SA) as (stB & raccB & EQ & SB).
      pose proof SB as SB'. destruct SB' as (Esbeg & _).
      ndestruct (MOD2 stB SB) as (stC & ev & CD & SC).
      exists stC, (rev_append ev raccB). split; [| exact SC].
      rewrite EQ. unfold dr_mid. cbn [cb_recycle_list]. rewrite (in_primary_sb (a_st s) stB) by exact Esbeg. rewrite PRIM. cbn [negb].
      rewrite (class_of_addr_sb (a_st s) stB) by exact Esbeg. rewrite CLb. rewrite CD. reflexivity. }
    assert (XCP : Permutation XC (flat_map qb_chunks T')) by exact PXC.
    destruct T' as [|b' T''].
    + (* [comment removed for export] *)
      destruct VIS3 as [VIS3 ST3].
      apply K. unfold dr_post. nexists s2, t0', t1', t2', (wz 0), a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m2.
      split; [exact RL2|].
      split. { split; [| split; [exact INIT2| split; [exact NM2| split; [exact AWV2| split; [exact FXR2| split; [exact AMX3| split; [exact DEP2| split; [exact DPL2| split; [exact DCOV3| exact MI2]]]]]]]]].
               cbn [flat_map] in XCP. apply Permutation_sym, Permutation_nil in XCP. subst XC. exact RQ2. }
      split; [exact OK3|]. split; [exact VIS3|]. split; [exact ST3|]. split; [exact (proj1 HM2)|].
      intros stA racc SA. ndestruct (MF2 stA racc SA) as (stB & raccB & EQ & SB). exists stB, raccB. split; [exact EQ| exact SB].
    + (* [comment removed for export] *)
      eapply (HK ltac:(discriminate)). unfold HEADINV.
      split; [exact RL2|].
      split; [split; [exact RQ2| split; [exact INIT2| split; [exact NM2| split; [exact AWV2| split; [exact FXR2| split; [exact AMX3| split; [exact DEP2| split; [exact DPL2| split; [exact DCOV3| exact MI2]]]]]]]]]|].
      split; [exact ST2|]. split; [exact XCP|]. split; [apply Permutation_refl|].
      split; [exact (conj OKT' (conj NDT' (conj SUBT' (conj BST' CLT'))))|].
      split; [exact HM2|]. split; [exact MF2|]. split; [exact OK3| exact VIS3].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma chunk_phase : ltac2:(zQ "j60!m0!o4!lc!hva!msc!kh3!hka!ihf!jsf!s5!qv0!rkb!nu4!mu8!uib!umc!mn5!mnc!sa!rg0!rg7!ng8!je!kg6!tj2!rge!q1!uq9!so2!uqf!rl4!und!tk1!rlb!tk8!qof!uo8!up3!og7!nud!lpc!pv3!upb!ju8!rq1!ru6!rue!in8!sj2!sn7!tmc!ii6!jmd!tgc>4rest@1$3$2>1b$5>2T'@1$3$5>2XC@1$3$2>2XB@1$3$2>1s$h5>1m$h6>2mo$c>3msF$a>2j0@1$3@1$1@1$0#8>1i$2>3rax@1$1@1$0#k0>2t0@1$1@1$0#k0>2t1@1$1@1$0#k0>2t2@1$1@1$0#k0>2a0@1$1@1$0#k0>2a1@1$1@1$0#k0>2a2@1$1@1$0#k0>2a3@1$1@1$0#k0>2a4@1$1@1$0#k0>2a5@1$1@1$0#k0>2a6@1$1@1$0#k0>2a7@1$1@1$0#k0>2x6@1$1@1$0#k0>2t3@1$1@1$0#k0>2t4@1$1@1$0#k0>2t5@1$1@1$0#k0>2t6@1$1@1$0#k0>0@1$h2@3$9@1$3$2^hc@1$h1$2>0@2$j3Z^h3>0@3$9@1$3$2^he@3$hd$2@1$j5^h4@1$h7^hd>0@3$i1^ha^h9^h8>0@5$he^hb^ha^h9^hd^hc>0@4$if$6^hb?2lo?3spv>0@3$h8$2^hf@3$hb$2^i2@4$j2$5$2$h7^i0>0@3$h8$2^hf@3$h0$2@1$8^i2@4$hc$5$2$8^i1>0@1$i2@3$h0$5^i3^i2>0@4$i5^hf^i4^i3^hc>0@2$i0\3stB$i8\5raccB@1$3$i9@5$i3@1$8^i7^i6^2^i8^1@1$i7^i1>0@5$id$6@1$h3^i2@1$h4^i2@1$i6^i2@2$b^hf^i0>0@3$9$a@3$ic@1$h3^i3@1$h4^i3^i0@7$j0@hf$ie^hd?2sp?2gp?2tp^hc^hb^ha@2$h9@1$0#k0?2T0@1$4$d^h9^h8^h7^h6^h5^h4^h3^h2@1$4@2$7$d+k0@1$4@2$7$d+ir0@1$4@1$8^i7@1$4$ia^h1@1$4@2$7@2$7@1$8^i7+p8@2$j4+8^he@1$4@2$7@1$ib^i7+h0@1$4@2$7+h0^he?3s10?3s11^h0^f^e^d?1F@2$h9@1$0#k0+mrjhc?2fc@1$ha@1$1@1$0#k0^i2@1$j1$6>0>0@1$h2@3$9@1$3$5^i7@1$h1$5>2s'$h5>2m'$h6>3mo'$c>4msF'$a>3XC'@1$3$2>3XB'@1$3$2>3j0'@1$3@1$1@1$0#8>4rax'@1$1@1$0#k0>3t0'@1$1@1$0#k0>3t1'@1$1@1$0#k0>3t2'@1$1@1$0#k0>3a1'@1$1@1$0#k0>3a2'@1$1@1$0#k0>3a3'@1$1@1$0#k0>3a4'@1$1@1$0#k0>3a5'@1$1@1$0#k0>3a6'@1$1@1$0#k0>3a7'@1$1@1$0#k0>3x4'@1$1@1$0#k0>3x6'@1$1@1$0#k0>3x7'@1$1@1$0#k0>3x8'@1$1@1$0#k0>3x9'@1$1@1$0#k0>3t3'@1$1@1$0#k0>3t4'@1$1@1$0#k0>3t5'@1$1@1$0#k0>3t6'@1$1@1$0#k0>0@hc$hf^k3^hb^ha^h9^h8^h7^h6^h5^h4^h3^h2^h1^h0^f^e^d^c^b^a^9^8^7^6^5^4^3^2^1@4$e$6$f?1Q@2$b^h9^ha>0>4msF'$a>3mo'$c>0@2$i4^2^1@4$e$6$f?1Q@2$b^3^2@4$e$6$f?1Q@2$b^i3^i4").
  Proof.
    induction rest as [|mi rest' IH]; intros b T' XC XB s m mo msF j0 i rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x6 t3 t4 t5 t6;
      intros NE I0 EQR RL CU ST PXC PXB TK MB MF OK VIS HK K; [exfalso; exact (NE eq_refl)|]. clear NE.
    ndestruct CU as (RQ & INIT & NM & AWV & FXR & AMX & DEP & DPL & DCOV & MI).
    npose RL as (Et & Ec & Ef & Ez & Etp & Ebt & Eal & Esb & Epa & SUBS & AU & NVS & AVM & ACM & AVS & AGS & ALK & AGA).
    npose TK as (OKT & NDT & SUBT & BST & CLT).
    npose MB as (HT & BSG & FR & HB & ARR & STB & POI).
    pose proof (AREPQ_placed _ _ _ _ RQ) as PL. pose proof (AREPQ_WFQ _ _ _ _ RQ) as WQ.
    pose proof (bv_unsigned_in_range _ sp) as SPR; change (bv_modulus 64) with (2^64) in SPR.
    pose proof aceil_range as ACR.
    pose proof (Forall_inv OKT) as OKb. npose OKb as (Kb1 & Kb2 & Kb3 & Kb4 & Kb5 & Kb6 & Kb7).
    pose proof (Forall_inv CLT) as CLb0.
    assert (ECA : a_cache s = a_cache s0) by (unfold a_cache; rewrite Et; reflexivity).
    (* [comment removed for export] *)
    assert (NTH : nth_error (qb_chunks b) (Z.to_nat i) = Some mi) by (rewrite <- hd_error_skipn, <- EQR; reflexivity).
    assert (IR : 0 <= i < qb_count b).
    { split; [exact I0|]. pose proof (length_skipn (Z.to_nat i) (qb_chunks b)) as LS. rewrite <- EQR in LS. cbn [length] in LS. unfold zlen in Kb5. clear - LS Kb5 I0. olia. }
    assert (MIR : 0 <= mi < 2^64) by exact (proj1 (Forall_forall _ _) Kb7 mi (nth_error_In _ _ NTH)).
    assert (CELL : rw_cells asegs m (qb_addr b + 24 + 8 * i) [C8 (wz mi)]).
    { pose proof (u64arr_cell m _ _ _ _ ARR NTH) as C. rewrite Z2Nat.id in C by exact I0. exact C. }
    (* [comment removed for export] *)
    eapply (evt_sreach_lazy_at asegs (a_L s) (a_S s) (a_Zr s) _ msF _ mo Q OK VIS).
    { eapply (dr_call_chunk sp gp tp F fc s10 s11 (qb_addr b) i (qb_count b) mi); [exact MI| exact Kb1| exact Kb2| exact IR| clear - Kb4; olia| exact MIR| exact CELL]. }
    cbv beta. intros msF1 mo1 OK1 SBM1 _ VIS1.
    pose proof (AMODELX_mat s mo mo1 AMX SBM1) as AMX1. pose proof (depot_cov_mat d mo mo1 DCOV SBM1) as DCOV1.
    (* [comment removed for export] *)
    assert (INmi : In mi XC) by (eapply Permutation_in; [apply Permutation_sym; exact PXC| left; reflexivity]).
    destruct (xc_chunk _ _ _ _ WQ INmi) as (ch & CHIN & QUAR & Ebeg).
    (* [comment removed for export] *)
    assert (CBC : rw_cells asegs m (spv + 8) [C8 (wz (a_cache s))]).
    { unfold dr_frame in FR. apply (proj1 (rw_cells_app asegs _ _ [_] _)) in FR. destruct FR as [_ FR2].
      apply (proj1 (rw_cells_app asegs _ _ [_] _)) in FR2. destruct FR2 as [FR2 _]. cbn [cells_size csize Nat.add] in FR2.
      rewrite ECA. unfold ca in FR2. replace (spv + 8) with (spv + Z.of_nat 8) by (clear; olia). exact FR2. }
    (* [comment removed for export] *)
    apply (STEP_CHUNK (wz 0x6b328) t0 t1 t2 a2 a3 a4 a5 a6 a7 (wz (AINST + 64)) (wz (AINST + 688)) (wz (qb_addr b)) (wz kSpaceSize) x6
             (wz (qb_addr b + 152 + 8 * i)) (wz (qb_count b + 16)) (wz (16 + i)) t3 t4 t5 t6
             m msF1 mo1 s (rest' ++ flat_map qb_chunks T') XB ch).
    - rewrite Ebeg. eapply AREPQ_perm; [exact PXC| apply Permutation_refl| exact RQ].
    - exact CHIN.
    - exact QUAR.
    - exact INIT.
    - exact (conj AWV FXR).
    - exact AMX1.
    - exact DEP.
    - exact DPL.
    - exact DCOV1.
    - exact MI.
    - exact LO.
    - exact HI.
    - clear - SPT; unfold spv in *; olia.
    - exact SPA.
    - exact ST.
    - exact TPv.
    - exact (PROOM_of_NUM _ _ _ WQ NM).
    - clear - SPT SPR; unfold spv in *; olia.
    - exact CBC.
    - exact OK1.
    - rewrite VIS1, Ebeg. unfold wz, T0, spv. reflexivity.
    - cbv beta. intros msF2 mo2 POST.
    ndestruct POST as (s2 & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2
                      & Et2 & Ec2 & Ef2 & Ez2 & Etp2 & Ebt2 & Eal2 & Esb2 & Epa2 & SUB2 & INIT2 & AU2 & OK2 & VIS2
                      & RQ2 & AWV2 & FXR2 & AMX2 & NVS2 & AVM2 & DCOV2 & DEP2 & DPL2 & MI2 & ST2 & ACM2 & AVS2 & AGP2 & ALK2 & AGA2 & MOD2).
    change (ret_pc (wz 0x6b328)) with (ret_pc (Z_to_bv 64 0x6b328)) in VIS2. rewrite (ret_pc_even 0x6b328) in VIS2 by (clear; olia).
    (* [comment removed for export] *)
    assert (AGS2 : agree_on (fun a => spv <= a) m m2).
    { apply (agree_of_acompl _ s s2 spv m m2 ACM2). intros a Ha. apply (above_not_awrit s s2 spv a PL SUB2); [clear - LO HI ACR; unfold spv in *; olia| clear - HI; unfold spv in *; olia| exact Ha]. }
    assert (INB : In (qb_addr b) XB) by (eapply Permutation_in; [apply Permutation_sym; exact PXB| left; reflexivity]).
    assert (PZb : forall a, (qb_addr b <= a < qb_addr b + kBatchSize \/ sh (qb_addr b) <= a < sh (qb_addr b) + kBatchSize / 8) -> pendz (a_st s) XB a).
    { intros a Ha. apply (batch_in_pendz (a_st s) XB (qb_addr b) a INB); [| exact Ha]. rewrite (class_of_addr_sb st0 (a_st s)) by exact Esb. exact CLb0. }
    assert (MB2 : memB m2 b T' j0).
    { npose (TOK_tail b T' TK) as (OKT' & _ & _ & _ & CLT').
      assert (LW : Z.of_nat (length (wlist (qb_chunks b))) = qb_count b) by (unfold wlist; rewrite length_map; unfold zlen in Kb5; clear - Kb5; olia).
      unfold memB. unfold kBatchSize, kBatchCount in *.
      split; [| split; [| split; [| split; [| split; [| split]]]]].
      - eapply (rw_cells_transport_pt2 _ m m2 AGS2); [exact HT|]. cbn [cells_size csize Nat.add]. intros a Ha. unfold T0, spv in *. clear - Ha; olia.
      - eapply (bseg_transport_pt2 _ m m2 AGP2); [| exact OKT'| exact BSG].
        intros b0 a Hb0 Ha. apply (batch_in_pendz (a_st s) XB (qb_addr b0) a); [| | exact Ha].
        + eapply Permutation_in; [apply Permutation_sym; exact PXB| right; apply in_map; exact Hb0].
        + rewrite (class_of_addr_sb st0 (a_st s)) by exact Esb. exact (proj1 (Forall_forall _ _) CLT' b0 Hb0).
      - unfold dr_frame in FR |- *. eapply (rw_cells_transport_pt2 _ m m2 AGS2); [exact FR|]. intros a Ha. unfold spv in *. clear - Ha; olia.
      - eapply (rw_cells_transport_pt2 _ m m2 AGP2); [exact HB|]. cbn [cells_size csize Nat.add]. intros a Ha. apply PZb. left. clear - Ha; olia.
      - eapply (u64arr_transport_pt2 _ m m2 AGP2); [exact ARR|]. rewrite LW. intros a Ha. apply PZb. left. clear - Ha Kb4; olia.
      - eapply (stk_transport_pt2 _ m m2 AGP2); [exact STB|]. intros a Ha. apply PZb. left. clear - Ha Kb4; olia.
      - eapply (poisoned_transport_pt2 _ m m2 AGP2); [exact POI|]. intros a Ha. apply PZb. right.
        change (Z.of_nat (Z.to_nat (8192 / 8))) with 1024 in Ha. change (8192 / 8) with 1024. clear - Ha; olia. }
    (* [comment removed for export] *)
    eapply (evt_sreach_lazy_at asegs (a_L s2) (a_S s2) (a_Zr s2) _ msF2 _ mo2 Q OK2 VIS2).
    { eapply (dr_next_chunk sp gp tp F fc s10 s11 (qb_addr b) i (qb_count b)); [exact IR| clear - Kb4; olia| clear - Kb1; unfold AHI_LO in Kb1; olia| clear - Kb2 ACR; olia]. }
    cbv beta. intros msF3 mo3 OK3 SBM3 _ VIS3.
    (* [comment removed for export] *)
    assert (RL2 : REL s2 m2 mo3).
    { unfold REL. rewrite Et2, Ec2, Ef2, Ez2, Etp2, Ebt2, Eal2, Esb2, Epa2.
      split; [exact Et|]. split; [exact Ec|]. split; [exact Ef|]. split; [exact Ez|]. split; [exact Etp|]. split; [exact Ebt|].
      split; [exact Eal|]. split; [exact Esb|]. split; [exact Epa|].
      split; [intros sc Hsc; exact (SUBS sc (SUB2 sc Hsc))|].
      split; [intros c0 Hc0; rewrite (AU2 c0 Hc0); exact (AU c0 Hc0)|].
      split; [eapply nonvm_same_trans; [exact NVS| eapply nonvm_same_trans; [apply nonvm_same_mat; exact SBM1| eapply nonvm_same_trans; [exact NVS2| apply nonvm_same_mat; exact SBM3]]]|].
      split; [apply (avmx_trans s0 s s2 mo0 mo mo3 SUBS SUB2 AVM);
              eapply avmx_mat_r; [eapply avmx_mat_l; [exact SBM1| exact AVM2]| exact SBM3]|].
      split; [apply (acompl_trans s0 s s2 d lo SP m0 m m2 (conj Et (conj Esb Epa)) SUBS ACM); apply (acompl_SP_mono s s2 d lo spv SP m m2); [unfold SP, spv; clear; olia| exact ACM2]|].
      split; [exact (avis_trans s0 s s2 m0 m m2 SUBS SUB2 AVS AVS2)|].
      split; [eapply agree_on_trans; [exact AGS|]; eapply agree_on_weaken; [| exact AGS2]; intros a Ha; unfold SP, spv in *; clear - Ha; olia|].
      split; [exact (alive_kept_trans _ _ _ ALK ALK2)| exact (agree_alive_trans st0 (a_st s) m0 m m2 ALK AGA AGA2)]. }
    pose proof (NUM_au _ _ AU2 NM) as NM2.
    pose proof (AMODELX_mat s2 mo2 mo3 AMX2 SBM3) as AMX3. pose proof (depot_cov_mat d mo2 mo3 DCOV2 SBM3) as DCOV3.
    assert (CU2 : CUR s2 m2 mo3 (rest' ++ flat_map qb_chunks T') XB).
    { split; [exact RQ2| split; [exact INIT2| split; [exact NM2| split; [exact AWV2| split; [exact FXR2| split; [exact AMX3| split; [exact DEP2| split; [exact DPL2| split; [exact DCOV3| exact MI2]]]]]]]]]. }
    assert (MF2 : MSF (fun stB raccB => dr_mid (qb_addr b) T' stB rest' raccB) (a_st s2)).
    { intros stA racc SA. ndestruct (MF stA racc SA) as (stB & raccB & EQ & SB).
      ndestruct (MOD2 stB SB) as (stC & ev & CR & SC). rewrite Ebeg in CR.
      exists stC, (rev_append ev raccB). split; [| exact SC].
      rewrite EQ. unfold dr_mid. cbn [cb_recycle_list]. rewrite CR. reflexivity. }
    destruct rest' as [|mi' rest''].
    + (* [comment removed for export] *)
      replace (i + 1 =? qb_count b) with true in VIS3.
      2: { symmetry. apply Z.eqb_eq. pose proof (length_skipn (Z.to_nat i) (qb_chunks b)) as LS. rewrite <- EQR in LS. cbn [length] in LS. unfold zlen in Kb5. clear - LS Kb5 I0. olia. }
      eapply (batch_phase b T' _ XB s2 m2 mo3 msF3 j0); [exact RL2| exact CU2| exact ST2| apply Permutation_refl| exact PXB| exact TK| exact MB2| exact MF2| exact OK3| exact VIS3| exact HK| exact K].
    + (* [comment removed for export] *)
      assert (NEQ : i + 1 <> qb_count b).
      { pose proof (length_skipn (Z.to_nat i) (qb_chunks b)) as LS. rewrite <- EQR in LS. cbn [length] in LS. unfold zlen in Kb5. clear - LS Kb5 I0. olia. }
      replace (i + 1 =? qb_count b) with false in VIS3 by (symmetry; apply Z.eqb_neq; exact NEQ).
      eapply (IH b T' _ XB s2 m2 mo3 msF3 j0 (i + 1)); [discriminate| clear - I0; olia| | exact RL2| exact CU2| exact ST2| apply Permutation_refl| exact PXB| exact TK| exact MB2| exact MF2| exact OK3| exact VIS3| exact HK| exact K].
      rewrite Z2Nat.inj_add, Nat.add_comm, <- skipn_skipn, <- EQR by (clear - I0; olia). reflexivity.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma head_body : ltac2:(zQ "h30!m0!o4!hva!kh3!lc!qv0!rkb!nu4!hka!uib!umc!und!ng8!je!mn5!mnc!s5!sa!uo8>2T'@1$2$3>1b$3>1s$c>1m$d>2mo$7>3msF$5>2XC@1$2$4>2XB@1$2$4>2j0@1$2@1$1@1$0#8>3rax@1$1@1$0#k0>2t0@1$1@1$0#k0>2t1@1$1@1$0#k0>2t2@1$1@1$0#k0>2a1@1$1@1$0#k0>2a2@1$1@1$0#k0>2a3@1$1@1$0#k0>2a4@1$1@1$0#k0>2a5@1$1@1$0#k0>2a6@1$1@1$0#k0>2a7@1$1@1$0#k0>2x4@1$1@1$0#k0>2x6@1$1@1$0#k0>2x7@1$1@1$0#k0>2x8@1$1@1$0#k0>2x9@1$1@1$0#k0>2t3@1$1@1$0#k0>2t4@1$1@1$0#k0>2t5@1$1@1$0#k0>2t6@1$1@1$0#k0>0@hc$b@3$e$3^hc^hd^hb^ha^h9^h8^h7^h6^h5^h4^h3^h2^h1^h0^f^e^d^c^b^a^9^8^7^6^5^4^3^2^1>0>0@1$h1@3$h0@1$2$3^he@1$f$3>2s'$c>2m'$d>3mo'$7>4msF'$5>3XC'@1$2$4>3XB'@1$2$4>3j0'@1$2@1$1@1$0#8>4rax'@1$1@1$0#k0>3t0'@1$1@1$0#k0>3t1'@1$1@1$0#k0>3t2'@1$1@1$0#k0>3a1'@1$1@1$0#k0>3a2'@1$1@1$0#k0>3a3'@1$1@1$0#k0>3a4'@1$1@1$0#k0>3a5'@1$1@1$0#k0>3a6'@1$1@1$0#k0>3a7'@1$1@1$0#k0>3x4'@1$1@1$0#k0>3x6'@1$1@1$0#k0>3x7'@1$1@1$0#k0>3x8'@1$1@1$0#k0>3x9'@1$1@1$0#k0>3t3'@1$1@1$0#k0>3t4'@1$1@1$0#k0>3t5'@1$1@1$0#k0>3t6'@1$1@1$0#k0>0@hc$b^ja^hb^ha^h9^h8^h7^h6^h5^h4^h3^h2^h1^h0^f^e^d^c^b^a^9^8^7^6^5^4^3^2^1@4$9$8$a?1Q@2$6^h9^ha>0>4msF'$5>3mo'$7>0@2$h2^2^1@4$9$8$a?1Q@2$6^3^2@4$9$8$a?1Q@2$6^hb^hc").
  Proof.
    intros T' b s m mo msF XC XB j0 rax t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x4 x6 x7 x8 x9 t3 t4 t5 t6 HINV HK K.
    ndestruct HINV as (RL & CU & ST & PXC & PXB & TK & HM & MF & OK & VIS).
    npose CU as (RQ & INIT & NM & AWV & FXR & AMX & DEP & DPL & DCOV & MI).
    npose TK as (OKT & NDT & SUBT & BST & CLT).
    pose proof (bv_unsigned_in_range _ sp) as SPR; change (bv_modulus 64) with (2^64) in SPR.
    pose proof aceil_range as ACR.
    pose proof (Forall_inv OKT) as OKb. npose OKb as (Kb1 & Kb2 & Kb3 & Kb4 & Kb5 & Kb6 & Kb7).
    (* [comment removed for export] *)
    eapply (evt_sreach_lazy_at asegs (a_L s) (a_S s) (a_Zr s) _ msF _ mo Q OK VIS).
    { eapply (dr_deq sp gp tp F fc rs0 rs1 rs2 rs3 rs4 rs5 rs6 rs7 rs8 rs9 s10 s11 ca cs lo l LO HI SPT OKL PW); [exact MI| exact OKT| exact SUBT| exact NDT| exact BST| exact HM]. }
    cbv beta. intros msF1 mo1 OK1 SBM1 _ VIS1.
    ndestruct VIS1 as (m1 & VIS1 & MU1 & WM1 & MI1 & HT1 & BSG1 & FR1 & HB1 & ARR1 & STB1 & POI1).
    assert (WL : wlocal [(T0, T0 + 32)]%Z) by (constructor; [cbn [fst snd]; unfold T0, SP, spv; clear; olia| constructor]).
    pose proof (CUR_local s m mo XC XB _ m1 mo1 CU WL MU1 WM1 MI1 SBM1) as CU1.
    pose proof (REL_local s m mo _ m1 mo1 RL WL MU1 WM1 SBM1) as RL1.
    pose proof (stk_local _ m m1 spv ST WL ltac:(clear; olia) MU1 WM1) as ST1.
    assert (MB1 : memB m1 b T' j0) by (exact (conj HT1 (conj BSG1 (conj FR1 (conj HB1 (conj ARR1 (conj STB1 POI1))))))).
    assert (MF1 : MSF (fun stB raccB => dr_mid (qb_addr b) T' stB (qb_chunks b) raccB) (a_st s)).
    { intros stA racc SA. ndestruct (MF stA racc SA) as (stB & raccB & EQ & SB). exists stB, raccB. split; [| exact SB]. rewrite EQ. apply do_recycle_cons. }
    destruct (Z.eqb_spec (qb_count b) 0) as [C0|C0].
    - (* [comment removed for export] *)
      assert (CH0 : qb_chunks b = []) by (clear - Kb5 C0; unfold zlen in Kb5; destruct (qb_chunks b); [reflexivity| cbn [length] in Kb5; exfalso; olia]).
      rewrite CH0 in MF1.
      eapply (batch_phase b T' XC XB s m1 mo1 msF1 j0); [exact RL1| exact CU1| exact ST1| | exact PXB| exact TK| exact MB1| exact MF1| exact OK1| exact VIS1| exact HK| exact K].
      cbn [flat_map] in PXC. rewrite CH0 in PXC. exact PXC.
    - (* [comment removed for export] *)
      eapply (chunk_phase (qb_chunks b) b T' XC XB s m1 mo1 msF1 j0 0); [ | clear; olia| reflexivity| exact RL1| exact CU1| exact ST1| exact PXC| exact PXB| exact TK| exact MB1| exact MF1| exact OK1| | exact HK| exact K].
      + intros E. apply C0. rewrite Kb5, E. reflexivity.
      + rewrite VIS1. replace (qb_addr b + 152 + 8 * 0) with (qb_addr b + 152) by (clear; olia). replace (16 + 0) with 16 by (clear; olia). reflexivity.
  Qed.

  Lemma head_phase : ltac2:(zQ "h00!m0!o4!hva!kh3!lc!qv0!rkb!nu4!hka!uib!umc!mn5!und!uo8!ng8!je>2T'@1$2$3>1b$3>1s$e>1m$f>2mo$7>3msF$5>2XC@1$2$4>2XB@1$2$4>2j0@1$2@1$1@1$0#8>3rax@1$1@1$0#k0>2t0@1$1@1$0#k0>2t1@1$1@1$0#k0>2t2@1$1@1$0#k0>2a1@1$1@1$0#k0>2a2@1$1@1$0#k0>2a3@1$1@1$0#k0>2a4@1$1@1$0#k0>2a5@1$1@1$0#k0>2a6@1$1@1$0#k0>2a7@1$1@1$0#k0>2x4@1$1@1$0#k0>2x6@1$1@1$0#k0>2x7@1$1@1$0#k0>2x8@1$1@1$0#k0>2x9@1$1@1$0#k0>2t3@1$1@1$0#k0>2t4@1$1@1$0#k0>2t5@1$1@1$0#k0>2t6@1$1@1$0#k0>0@hc$c@3$b$3^hc^hd^hb^ha^h9^h8^h7^h6^h5^h4^h3^h2^h1^h0^f^e^d^c^b^a^9^8^7^6^5^4^3^2^1>0>4msF'$5>3mo'$7>0@2$d^2^1@4$9$8$a?1Q@2$6^3^2@4$9$8$a?1Q@2$6^ha^hb").
  Proof.
    induction T' as [|b' T'' IH]; intros b s m mo msF XC XB j0 rax t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x4 x6 x7 x8 x9 t3 t4 t5 t6 HINV K;
      (eapply head_body; [exact HINV| | exact K]).
    - intros NE. exfalso. exact (NE eq_refl).
    - intros _ s' m' mo' msF' XC' XB' j0' rax' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' x4' x6' x7' x8' x9' t3' t4' t5' t6' HINV'.
      eapply IH; [exact HINV'| exact K].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Theorem do_recycle_arepq : ltac2:(zQ "id0!m0!o4!lc!hka!msc!kh3!jh3!mn5!mob!so2!qv0!rkb!jsf!rge!hva!rg0!rg7!uib!umc!tj2!q1!mnc!s5!nu4!rl4!tk8!uo8!nha!mu8!ur8!og7!us0!kg6!khd!rq1!ru6!rue!in8!sj2!sn7!isb!tmc!sp2!tg4!ihf>3msF$a>2XC@1$e$2>2XB@1$e$2>2t0@1$1@1$0#k0>2t1@1$1@1$0#k0>2t2@1$1@1$0#k0>2a4@1$1@1$0#k0>2a5@1$1@1$0#k0>2a6@1$1@1$0#k0>2a7@1$1@1$0#k0>2t3@1$1@1$0#k0>2t4@1$1@1$0#k0>2t5@1$1@1$0#k0>2t6@1$1@1$0#k0>0@5$h8?2s0?2m0?3mo0^d^c>0@4$i5$3?2m0?2lo?2T0>0@3$h3$2^f@4$i9$5$2$i0?3T0L>0@3$h3$2^f@4$9$5$2$c?3T0L>0@1$h9?3T0L>0@4$i8$3?2m0?2T0@3$7$6@1$8@1$4@2$i1$5?3T0L@3$7$6@1$8@1$4@3$ia$2Z@4$9$5$2$c?3T0L@3$7$6@1$8@1$4@3$ib$2@4$9$5$2$c?3T0LZ@3$7$6@1$8@1$4@1$hb?3T0L@1$h5$6>0@2$hf?2m0?3T0L>0@5$i3$3@1$f?2s0@1$h0?2s0@1$he?2s0@2$b^h5?3mo0>0@3$h6$a@3$i2@1$f?2s0@1$h0?2s0^h6@7$i6@hf$i4@1$4+mrgmc@2$d@1$0#k0?2T0?2gp?2tp^h3^h2^h1?3rs0?3rs1@1$4@2$ic$hc$hd@2$d@1$0#k0?2T0?2ca?2cs^h0^f^e^d?3rs2?3rs3?3rs4?3rs5?3rs6?3rs7?3rs8?3rs9?3s10?3s11^c^b^a^9?1F@2$d@1$0#k0+mrim4?2fc@1$h4@1$1@1$0#k0?2m0@1$i7$3>0>4msF'$a>3mo'$h7>0@2$ha^2^1@4$h1$3$h2?1Q@2$b^3^2@4$h1$3$h2?1Q@2$b^h8?3mo0").
  Proof.
    intros msF XC XB t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 CU ST PXC PXB TK HT BR OK VIS K.
    npose CU as (RQ & INIT & NM & AWV & FXR & AMX & DEP & DPL & DCOV & MI).
    npose TK as (OKT & NDT & SUBT & BST & CLT).
    pose proof (bv_unsigned_in_range _ sp) as SPR; change (bv_modulus 64) with (2^64) in SPR.
    assert (RL0 : REL s0 m0 mo0) by (apply REL_refl; apply avmx_same; reflexivity).
    apply (proj2 (bseg_batches m0 T0L)) in BR.
    (* [comment removed for export] *)
    eapply (evt_sreach_lazy_at asegs (a_L s0) (a_S s0) (a_Zr s0) _ msF _ mo0 Q OK VIS).
    { eapply (dr_entry sp gp tp F fc rs0 rs1 rs2 rs3 rs4 rs5 rs6 rs7 rs8 rs9 s10 s11 ca cs lo l LO HI SPT OKL PW T0L); [exact MI| exact ST| exact OKT| exact SUBT| exact BST| exact HT| exact BR]. }
    cbv beta. intros msF1 mo1 OK1 SBM1 _ VIS1.
    ndestruct VIS1 as (a1' & j0 & m1 & VIS1 & MU1 & WM1 & MI1 & HT1 & BSG1 & REST1).
    assert (WL : wlocal [(spv, T0)]%Z) by (constructor; [cbn [fst snd]; unfold T0, SP, spv; clear; olia| constructor]).
    pose proof (CUR_local s0 m0 mo0 XC XB _ m1 mo1 CU WL MU1 WM1 MI1 SBM1) as CU1.
    pose proof (REL_local s0 m0 mo0 _ m1 mo1 RL0 WL MU1 WM1 SBM1) as RL1.
    destruct T0L as [|b T'] eqn:ET.
    - (* [comment removed for export] *)
      apply K. unfold dr_post. nexists s0, t0, t1, t2, (wz 0), a1', ca, cs, a4, a5, a6, a7, t3, t4, t5, t6, m1.
      split; [exact RL1|].
      split. { cbn [flat_map map] in PXC, PXB. apply Permutation_sym, Permutation_nil in PXC. apply Permutation_sym, Permutation_nil in PXB. subst XC XB. exact CU1. }
      split; [exact OK1|]. split; [exact VIS1|]. split; [exact REST1|]. split; [exact HT1|].
      intros stA racc SA. exists stA, racc. rewrite ET. split; [reflexivity| exact SA].
    - destruct REST1 as [ST1 FR1].
      eapply (head_phase T' b s0 m1 mo1 msF1 XC XB j0); [| exact K]. unfold HEADINV.
      split; [exact RL1|]. split; [exact CU1|]. split; [exact ST1|]. split; [exact PXC|]. split; [exact PXB|]. split; [exact TK|].
      split; [exact (conj HT1 (conj BSG1 FR1))|].
      split; [intros stA racc SA; exists stA, racc; rewrite ET; split; [reflexivity| exact SA]|].
      split; [exact OK1| exact VIS1].
  Qed.

End Loop.
End HCW.
(* [comment removed for export] *)
