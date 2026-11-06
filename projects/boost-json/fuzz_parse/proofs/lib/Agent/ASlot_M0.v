(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Ref Require Import RSegs. (* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import F_syscalls MallocRep F_malloc_free F_malloc_fast F_malloc_entry F_malloc_enframe MallocTree MallocFacts_A MallocHINV MallocKit_A.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import MallocKit_AB.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import Malloc_fp MallocKit_A2 AllocSlot_iface Malloc_iface.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import MallocNat MallocFacts_AS MallocKit_A3 ASlot_W0 ASlot_W9 ASlot_W18 ASlot_I.
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import StoreDj.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6Malloc~~~~~~04meta37Corelib4Init5Logick42eqk43and37Corelib7Numbers7BinNumsm31Z07m_avail0am_freeable07m_freed0am_last_idx08m_maplen05m_mem0bm_sizeclass04optr06mstate0cget_meta_rec79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Agent8ASlot_M0~~~~~~u4alinks_only04aptru42LO08upd_meta05lhead08set_head07dequeue01M79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5AgentaMallocTree~~~~~~hm47leaf_of89OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Agent8ASlot_M03AML~~~~~~hr23KOKhr23BOK07am_take08am_carve37Corelib4Init9Datatypesih84bool09am_finish0cam_after_brk0aalloc_metaih84prodih86optionih84Someih84pair79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Agent9MallocNat~~~~~~inf2bSinf2kShm43memm31N79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Agent7ASlot_I~~~~~~it89ENTRY_REL08set_tick79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Agent8ASlot_W0~~~~~~jif6ta_relhm46am_rel79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Agent9MallocRep~~~~~~jo48ticks_ok08s_shadow06s_tick06shadow25stdpp9countablejucbN_countable25stdpp4gmapkgc4gmap35stdpp7numbers1Nki06eq_dec25stdpp4basekjb6lookupjucbZ_countablekgcbgmap_lookup35stdpp7numbers1Zkmf6eq_decit84ALLC07r_cells46Stdlib6NArith6BinNat1Nkpb2lekpb2lt0asize_class79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Agenth0F_malloc_enframe~~~~~~ksb4zseq36Stdlib5Lists4Listlhd7forallb46Stdlib6ZArith6BinInt1Zljb3addljb3ltbljb3subih84trueu4asc_mono_fnljb2ltljb2leljb3lebih84andb79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5AgenteF_malloc_entry~~~~~~lp85stc_qu47nest_fn06region04ghdrjuceprod_countable25stdpp9decidablemh2bprod_eq_decm34Npos09s_regions35stdpp9bitvectorbdefinitionsmk42bv79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Agent9Malloc_fp~~~~~~mm79unk_agree79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~mr62wa07RKGroup06r_base06r_kind05rkind08s_groupskjb7is_Somek43iffk43notmm7bgrp_hdr_cov07Unknown09cell_read07cellval0aget_shadow05r_len0bround_up_pg03ctx06active07bounces05c_brk0ec_mmap_counter05c_seq07s_areas0as_next_rid0as_reserved07s_slots09unmap_seq05usageih84list79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Agent9ASlot_W18~~~~~~nvb8as_fm_st04area08brkstate" s.   (* [comment removed for export] *)
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition links_only : ltac2:(zQ "10!je>1r$0>2r'$0P") := ltac2:(zQ "c0!l8!ld!nc!o0!o9!p5!pe!qa!r4!rb!je!s8\1r$a\2r'$a@2$1@3$0$b@1$8^1@1$8^2@2$1@3$0$2@1$3^1@1$3^2@2$1@3$0$2@1$5^1@1$5^2@2$1@3$0$2@1$6^1@1$6^2@2$1@3$0$2@1$4^1@1$4^2@2$1@3$0$2@1$9^1@1$9^2@3$0$2@1$7^1@1$7^2").

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma leaf_of_ret_inv {R} o (r r' : R) : leaf_of o (SRet r) r' -> r' = r.
Proof. (intros nd_i1; ndestruct nd_i1 as (ans & o' & H)). rewrite mrun_ret in H. cbn in H. destruct ans; inversion H; reflexivity. Qed.

Lemma leaf_of_vis_inv {R} o e (k : Z -> Malloc.M R) r :
  leaf_of o (SVis e k) r ->
  match e with
  | EUndef _ => False
  | EPeek p c h => leaf_of o (k (pans_mem o p c h)) r
  | _ => exists z, leaf_of o (k z) r
  end.
Proof.
  (intros nd_i2; ndestruct nd_i2 as (ans & o' & H)).
  destruct e; try (rewrite mrun_vis in H by exact I; cbn [follow] in H; destruct ans as [|a ans]; [discriminate|]; exists a; exists ans, o'; exact H).
  - rewrite mrun_peek in H. exists ans, o'. exact H.
  - rewrite mrun_vis in H by exact I. cbn [follow] in H. destruct ans; discriminate.
Qed.

Lemma leaf_of_bad {R} o (bail : Malloc.M R) r : leaf_of o (bad_answer bail) r -> False.
Proof. intros H. exact (leaf_of_vis_inv o _ _ r H). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition LO : ltac2:(zQ "10!se>2st$0>3st'$0P") := ltac2:(zQ "40!t6!se!hi5!hj2\2st$1\3st'$1>1q$3@2$2@2$0^3^1@2$0^2^1").

Lemma LO_refl st : LO st st.
Proof. intros q. repeat split; reflexivity. Qed.
Lemma LO_trans : ltac2:(zQ "20!hj8!se>3st1$1>3st2$1>3st3$1>0@2$0^3^2>0@2$0^3^2@2$0^5^3").
Proof. intros st1 st2 st3.
  intros A B q. ndestruct (A q) as (A1&A2&A3&A4&A5&A6&A7). ndestruct (B q) as (B1&B2&B3&B4&B5&B6&B7).
  repeat split; congruence.
Qed.
Lemma LO_same : ltac2:(zQ "60!t6!se!l8!hj8!hj2!je>2st$1>3st'$1>0>1q$4@3$2$5@2$0^2^1@2$0^3^1@2$3^3^2").
Proof. intros st st'. intros H q. rewrite H. apply LO_refl. Qed.

Lemma LO_upd_links : ltac2:(zQ "60!je!hj8!hi5!hj2!se!hjd>2st$4>1m$3>1f>1x$0$0>0>1r$0@2$2^1@1^2^1@2$1^4@3$5^3^2^4").
Proof. intros st m f.
  intros Hf q. unfold upd_meta. destruct (decide (q = m)) as [->|NE].
  - rewrite get_meta_rec_put_same. apply Hf.
  - rewrite get_meta_rec_put_other by exact NE. apply LO_refl.
Qed.

Lemma rec_set_head : ltac2:(zQ "80!t6!l8!hj2!hk7!je!se!s8!hke>1h$3>1v$6>2st$5>1q$2@3$1$4@2$0@3$7^4^3^2^1@2$0^2^1").
Proof. intros h v st q. destruct h; reflexivity. Qed.

Ltac lo_peel :=
  first [ apply LO_refl
        | apply LO_same; intros ?; reflexivity
        | eapply LO_trans; [| apply LO_upd_links; intros ?; repeat split; reflexivity]; lo_peel
        | eapply LO_trans; [| apply LO_same; intros ?; apply rec_set_head]; lo_peel ].

Lemma LO_dequeue : ltac2:(zQ "50!hj8!hj2!hl8!hk7!se>1h$3>1m$1>2st$4@2$0^1@3$2^3^2^1").
Proof. intros h m st.
  unfold dequeue. cbv zeta.
  destruct (negb (optr_eqb (m_next (get_meta_rec st m)) (Some m)));
  destruct (m_prev (get_meta_rec st m)) as [pv|]; destruct (m_next (get_meta_rec st m)) as [nx|];
  try destruct (optr_eqb _ (Some m)); lo_peel.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section AML.
Context {R : Type}.
Variable o : ltac2:(zQ "10!isd$0").
Variable Φ : ltac2:(zQ "00>0?1RP").

Definition KOK : ltac2:(zQ "30!se!hm1!s8>2st$0>1k>0$0>0$2@1$1?1RP") := ltac2:(zQ "50!se!s8!hj8!hq7!hm1\2st$0\1k>0$0>0$1@1$4?1R>3st2$0>2mo$1>1r?1R>0@2$2^5^3>0@4$3?1R?1o@2^5^4^3^2@1?2Φ^3").
Definition BOK : ltac2:(zQ "10!hm1>4bail@1$0?1RP") := ltac2:(zQ "20!hq7!hm1\4bail@1$1?1R>1r?1R>0@4$0?1R?1o^2^1@1?2Φ^2").

Lemma KOK_LO : ltac2:(zQ "50!se!hv7!hj8!hm1!s8>2st$0>3st1$0>1k>0$0>0$4@1$3?1R>0@2$2^3^2>0@2$1^4^2@2$1^4^3").
Proof. intros st st1 k. intros L K st2 mo r L2 H. apply (K st2 mo r); [eapply LO_trans; [exact L| exact L2]| exact H]. Qed.

Lemma am_take_leaves : ltac2:(zQ "70!hm1!se!hve!hv7!hq7!ig5!s8>2st$1>1k>0$1>0$6@1$0?1R>4bail@1$0?1R>1r?1R>0@2$3^4^3>0@1$2^3>0@4$4?1R?1o@4$5?1R^6^5^4^3@1?2Φ^4").
Proof. intros st k bail r.
  intros K B H. unfold am_take in H.
  destruct (c_avail_meta (ctx st)) as [m|].
  - eapply K; [| exact H]. lo_peel.
  - destruct (leaf_of_vis_inv o _ _ r H).
Qed.

Lemma am_carve_leaves : ltac2:(zQ "80!hm1!se!hve!hv7!hq7!ige!hj2!s8>2st$1>1p$6>1k>0$1>0$7@1$0?1R>4bail@1$0?1R>1r?1R>0@2$3^5^3>0@1$2^3>0@4$4?1R?1o@5$5?1R^7^6^5^4^3@1?2Φ^4").
Proof. intros st p k bail r.
  intros K B H. unfold am_carve in H. cbv zeta in H.
  eapply am_take_leaves; [| exact B| exact H].
  eapply KOK_LO; [| exact K]. apply LO_same. intros q.
  destruct (c_meta_area_tail _); reflexivity.
Qed.

Lemma am_finish_leaves : ltac2:(zQ "80!hm1!se!ij0!hve!hv7!hq7!ij8!s8>2st$1>2nu$2>1k>0$1>0$7@1$0?1R>4bail@1$0?1R>1r?1R>0@2$4^5^3>0@1$3^3>0@4$5?1R?1o@5$6?1R^7^6^5^4^3@1?2Φ^4").
Proof. intros st nu k bail r.
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

Lemma am_after_brk_leaves : ltac2:(zQ "80!hm1!se!ij0!hve!hv7!hq7!ik3!s8>2st$1>2nu$2>1k>0$1>0$7@1$0?1R>4bail@1$0?1R>1r?1R>0@2$4^5^3>0@1$3^3>0@4$5?1R?1o@5$6?1R^7^6^5^4^3@1?2Φ^4").
Proof. intros st nu k bail r.
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

Lemma alloc_meta_leaves : ltac2:(zQ "70!hm1!se!hve!hv7!hq7!il1!s8>2st$1>1k>0$1>0$6@1$0?1R>4bail@1$0?1R>1r?1R>0@2$3^4^3>0@1$2^3>0@4$4?1R?1o@4$5?1R^6^5^4^3@1?2Φ^4").
Proof. intros st k bail r.
  intros K B H. unfold alloc_meta in H.
  set (stI := if c_init_done (ctx st) =? 0 then upd_ctx (fun c => set_init_done 1 (set_secret (s_secret st) c)) st else st) in H.
  assert (LI : LO st stI) by (apply LO_same; intros q; subst stI; destruct (c_init_done (ctx st) =? 0); reflexivity).
  pose proof (KOK_LO st stI k LI K) as KI.
  destruct (c_free_meta_head (ctx stI)) as [m|].
  { exact (KI _ _ _ (LO_dequeue LFree m stI) H). }
  destruct (negb (c_avail_meta_count (ctx stI) =? 0)); [eapply am_take_leaves; [exact KI| exact B| exact H]|].
  destruct ((c_avail_meta_area_count (ctx stI) =? 0) && _); [| eapply am_after_brk_leaves; [exact KI| exact B| exact H]].
  destruct (c_brk (ctx stI)) as [| |rid off].
  - (* [comment removed for export] *)
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
  - (* [comment removed for export] *) eapply am_after_brk_leaves; [exact KI| exact B| exact H].
  - (* [comment removed for export] *)
    destruct (leaf_of_vis_inv o _ _ r H) as [z Hz]. cbv beta in Hz.
    destruct (negb (brk_answer_ok _ _ z)); [destruct (leaf_of_bad o _ _ Hz)|].
    destruct (negb (z =? _)).
    + eapply am_after_brk_leaves; [| exact B| exact Hz]. eapply KOK_LO; [| exact KI]. apply LO_same; intros q; reflexivity.
    + destruct (negb (brk_pages_ok _ _ _)); [destruct (leaf_of_bad o _ _ Hz)|].
      eapply am_after_brk_leaves; [| exact B| exact Hz]. eapply KOK_LO; [| exact KI]. apply LO_same; intros q.
      unfold upd_region. destruct (get_region stI rid); reflexivity.
Qed.
End AML.

Lemma am_leaf_links_only : ltac2:(zQ "e0!se!s8!ild!im5!t6!imf!in7!hi5!is1!is7!hq7!isd!il1!hj2>1o$b>2st$0>3st'$0>2mo$1>0@4$a@1$3@2$2$0$1^4@4$c@1$3@2$2$0$1^3@2$9$0$1@1$8@2$2$0$1@2$5@2$2$0$1@4$6$0$1^2^1>1q$d@2$7@2$4^5^1@2$4^4^1").
Proof.
  intros o st st' mo H.
  refine (alloc_meta_leaves o (fun r => match r with Some (stX, _) => LO st stX | None => True end) st kS bS (Some (st', mo)) _ _ H).
  - intros st2 mo2 r L HL. apply leaf_of_ret_inv in HL. subst r. exact L.
  - intros r HL. apply leaf_of_ret_inv in HL. subst r. exact I.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ER_refl_tick : ltac2:(zQ "40!it4!jh8!se!ji5>3st0$2>1t$0@2$1^2@2$3^1^2").
Proof. intros st0 t.
  constructor; try reflexivity; try (intros; tauto).
  - split; [intros rid r H; exists r; cbn; repeat split; auto; lia| cbn; lia| reflexivity].
Qed.

Lemma ER_ta : ltac2:(zQ "40!se!jh8!nc!jn0>3st0$0>2st$0>2sc$2>3st1$0>0@2$1^4^3>0@3$3^3^4^2@2$1^6^3").
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
  - intros q Hq. ndestruct (EGE q Hq) as (A1 & A2 & A3). destruct (tr_geom _ _ _ T q) as (M & L & F & S & P). rewrite L, S. repeat split; try assumption.
    unfold get_stride. rewrite L, S, P. exact A1.
  - intros q i Hi Hb. apply (EB q i Hi). apply (tr_bits _ _ _ T q i Hi). exact Hb.
  - intros a Ha. rewrite (tr_areas _ _ _ T). apply EA. exact Ha.
Qed.

Lemma ER_am : ltac2:(zQ "e0!se!hj2!im5!ild!s8!imf!jh8!in7!is1!is7!jna!hq7!isd!il1>3st0$0>2st$0>3st1$0>1m$1>1o$c>0@2$6^5^4>0@3$a^5^4@2$5$1^3>0@4$b@1$2@2$3$0$4^3@4$d@1$2@2$3$0$4^6@2$9$0$4@1$8@2$3$0$4@2$5@2$3$0@1$2$1@4$7$0@1$2$1^5@2$5$1^4@2$6^8^6").
Proof. intros st0 st st1 m o.
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
    + intros rid r Hr. ndestruct (R1 rid r Hr) as (r1 & H1 & K1 & B1 & L1).
      destruct (amr_regions _ _ _ A rid r1 H1) as (r2 & H2 & K2 & B2 & L2 & _). exists r2. repeat split; try congruence. lia.
    + pose proof (amr_next_rid _ _ _ A). lia.
    + rewrite (amr_reserved _ _ _ A). exact S1.
  - intros q. destruct (LO q) as (M & _). rewrite M. apply EME.
  - intros q Hq. ndestruct (EGE q Hq) as (A1 & A2 & A3). ndestruct (LO q) as (M & AV & FR & L2 & F & S & P). rewrite L2, S. repeat split; try assumption.
    unfold get_stride. rewrite L2, S, P. exact A1.
  - intros q i Hi Hb. apply (EB q i Hi). ndestruct (LO q) as (_ & AV & FR & _). rewrite <- AV, <- FR. exact Hb.
  - intros a Ha. apply (amr_areas _ _ _ A). apply EA. exact Ha.
Qed.

Lemma ticks_ok_same : ltac2:(zQ "a0!l8!it4!js6!se!jt2!jtc!ju4!jvd!kh8!kj1>2st$3>3st1$3>0@3$0@4$8$1$9$7$6@1$4^1@1$4^2>0@3$0$1@1$5^2@1$5^3>0@1$2^4@1$2^4").
Proof. intros st st1. intros ES ET [T1 T2]. split; rewrite ES, ET; assumption. Qed.

(* [comment removed for export] *)
Lemma ALLC_tick : ltac2:(zQ "h70!it4!nc!ju4!ild!imf!im5!l8!jtc!kk7!jvd!kl1!kh8!km0!kj1!ko0!in7!koa!se!kp2!jt2!ji5!kr3!kr9>3st0$h1>1t$0>0>3rid$0>2sh$2>1o$1>1v$1>2tk$0>0@3$6@1$5$2@6$8$0$2@4$b$0$d$9$2@4$c$0$d$9$2^5@1$h3^7@2$4$2^4>0@3$6@1$5@2$3$1$0@6$8$1@2$3$1$0@4$b$1$e$a@2$3$1$0@4$c$1$e$a@2$3$1$0^4@1$h2^5@2$4@2$3$1$0@4$f$1$0^3^2@2$h5^3@1$7^9>0@2$h6@1$7^3^2@1$h0@2$h4^3^4").
Proof. intros st0 t. intros H Ht rid sh o v tk Hs Hc. cbn. pose proof (H rid sh o v tk Hs Hc). lia. Qed.

Lemma ALLC_same : ltac2:(zQ "a0!l8!it4!koa!se!jt2!jtc!ju4!jvd!kh8!kj1>2st$3>3st1$3>0@3$0@4$8$1$9$7$6@1$4^1@1$4^2>0@3$0$1@1$5^2@1$5^3>0@1$2^4@1$2^4").
Proof. intros st st1. intros ES ET H rid sh o v tk Hs Hc. rewrite ET. rewrite ES in Hs. exact (H rid sh o v tk Hs Hc). Qed.

Lemma ALLC_ta : ltac2:(zQ "40!koa!se!nc!jn0>2st$1>2sc$2>3st1$1>0@3$3^2^3^1>0@1$0^4@1$0^3").
Proof. intros st sc st1. intros T. apply ALLC_same; [apply (tr_shadow _ _ _ T)| apply (tr_tick _ _ _ T)]. Qed.

Lemma ALLC_am : ltac2:(zQ "40!koa!se!jna!s8>2st$1>3st1$1>2mo$3>0@3$2^3^2^1>0@1$0^4@1$0^4").
Proof. intros st st1 mo. intros A. apply ALLC_same; [apply (amr_shadow _ _ _ A)| apply (amr_tick _ _ _ A)]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition sc_mono_fn : ltac2:(zQ "20!ij0!nc>1a$1$0") := ltac2:(zQ "70!nc!krf!lh5!lj0!ll3!lla!lm1\1a$0@3$3$0\1b$0@2$5@1$1^2@1$1^1@2$2@2$4^1+1@2$6+if^1").
Lemma sc_mono_check : ltac2:(zQ "70!ij0!lm8!l8!nc!ln0!lh5!lj0@3$2$0@3$6$3$4@2$5Z+j0$1").
Proof. vm_compute. reflexivity. Qed.
Lemma size_class_mono : ltac2:(zQ "50!lnd!nc!krf!ld!lo3>1a$1>1b$1>0@2$4Z^2>0@2$3@2$0^3^2@2$0^2+j0@2$0@1$2^4@1$2^3").
Proof. intros a b.
  intros Ha Hb. pose proof (forallb_zseq sc_mono_fn 0 48 a sc_mono_check ltac:(lia) ltac:(lia)) as X. unfold sc_mono_fn in X.
  pose proof (forallb_zseq _ (a + 1) (47 - a) b X ltac:(lia) ltac:(lia)) as Y. apply Z.ltb_lt in Y. exact Y.
Qed.

(* [comment removed for export] *)
Definition nest_fn : ltac2:(zQ "20!ij0!nc>1q$1$0") := ltac2:(zQ "60!lo9!lp0!nc!ltf!krf!ll3\1q$2=1j$2@1$3^1@2$1@2$1@2$0Z^1@2$0^1+ha@2$0@2$5^2+1@1$4^1").
Lemma nest_check : ltac2:(zQ "70!ij0!lm8!l8!nc!lu8!lh5!lj0@3$2$0@3$6$3$4@2$5+1+nf$1").
Proof. vm_compute. reflexivity. Qed.
Lemma nest_class_props : ltac2:(zQ "60!lo3!ld!ltf!nc!krf!ll3>1q$3>0@2$1@2$0+1^1@2$0^1+nf@2$1@2$1@2$0Z@1$2^2@2$0@1$2^2+ha@2$0@2$5^2+1@1$4@1$2^2").
Proof. intros q.
  intros Hq. pose proof (forallb_zseq nest_fn 1 127 q nest_check ltac:(lia) ltac:(lia)) as X. unfold nest_fn in X. cbv zeta in X.
  rewrite !Bool.andb_true_iff in X. destruct X as [[A B] C]. apply Z.leb_le in A. apply Z.leb_le in B. apply Z.leb_le in C. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section FPER.
Variables (st0 st : mstate) (m : mem).
Hypothesis MR : mrep st m.
Hypothesis ER : ENTRY_REL st0 st.
End FPER.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma unk_agree_xfer : ltac2:(zQ "id2!it4!lv2!kj1!jvd!nc!l8!lva!ko0!hj2!kh8!im5!kk7!km0!kl1!mg0!mi3!imf!mj2!mj9!mm1!isd!mq9!mv0!mv6!se!mvf!ng7!ngf!nh6!jt2!ll3!ni0!ld!nib!nj1!nj7!nk6!nkf!nla!nm3!nmf!nn6!ju4!lo3!lnd&@4$9$8@4$f$0$2$4$7@6$e$0$2$3$4$7$d$6&@4$c$8@4$f$0$2$4$7@6$e$0$2$3$4$7$d$6>1o$h4>3stA$h8>2mA$h4>3stB$h8>2mB>1x@1$h3@1$h1#k0@1$a@1$h3@1$h1#8>0@3$h5^4^5^3>0@3$5@4$9$0$2$3$ia@1$hd^3@1$hd^5>0>3rid$0>1r$1>0@3$5$hb@1$ha^1$h7>0@3$5@1$a$1@6$b$0$1@4$9$0$2$3$1@4$c$0$2$3$1^3@1$h2^7@2$h0$1^2@3$5@1$a$1@6$b$0$1@4$9$0$2$3$1@4$c$0$2$3$1^4@1$h2^a@2$h0$1^3>0>1b$8@2$i1@2$hf$6@6$b$8$6~0~1^1@1$hc^6@2$hf$6@6$b$8$6~0~1^1@1$hc^8>0>3rid$0>1r$1>3off$4>1h$4>0@3$5@1$a$1@6$b$0$1@4$9$0$2$3$1@4$c$0$2$3$1^4@1$h2^c@2$h0$1^3>0@3$5$hb@1$ha^4$h7>0@2$i0@2$ibZ^4@2$ic^4@1$i9@1$i8^5>0@3$5$i6@2$i5@2$i7^f^7^5@1$i4^4>0@1$i2@3$i3^h0^8^6@3$5@1$a@1$h3@1$h1#8@1^e@1$h6@2$he@1$h9^8^7@1^h0@1$h6@2$he@1$h9^8^7@3$h5^7^a^6").
Proof. intros o stA mA stB mB.
  intros UA ES ERG EG AG rid r off h Hr Hk Ho Hc NG.
  pose proof (ERG rid r Hk Hr) as Hr0.
  assert (Hc0 : cell_read (get_shadow stA rid) off = Unknown h) by (revert Hc; unfold get_shadow; rewrite ES; intros X; exact X).
  assert (NG0 : ~ grp_hdr_cov stA rid off).
  { (intros nd_i3; ndestruct nd_i3 as (bq & gh & Hbq & Hf & Hoff)). apply NG. destruct (proj2 (EG bq) (ex_intro _ gh Hbq)) as [gh1 Hbq1]. exists bq, gh1. auto. }
  rewrite (AG rid r off h Hr0 Hk Ho Hc0 NG0). exact (UA rid r off h Hr0 Hk Ho Hc0 NG0).
Qed.

(* [comment removed for export] *)
Lemma fm_proj : ltac2:(zQ "i60!nc!l8!ld!it4!kj1!no3!ko0!hj2!jvd!kh8!kl1!mg0!mi3!ild!no8!np0!np9!nq0!nr0!se!nr7!nh6!ns0!mj9!nsc!jt2!nt8!jtc!nu1!nuc!nv3!ojd!ok9!okf!lva!s8!lv2!ju4>2st$h3>1g$7=3st'$h3@2$hf^2^1@2$2@3$1@4$9$3$4$8$i4@1$h7^1@1$h7^3@2$2@3$1@4$9$3$4$8$i5@1$h9^1@1$h9^3@2$2@3$1@4$9$7@4$c$3$4$0$6@6$b$3$4$8$0$6$a$i2@1$h5^1@1$h5^3@2$2@3$1@4$9$7@4$c$3$4$0$6@6$b$3$4$8$0$6$a$i0@1$h4^1@1$h4^3@2$2@3$1@4$9$7@4$c$3$4$0$6@6$b$3$4$8$0$6$a@2$d$7$0@1$ha^1@1$ha^3@2$2@3$1$3@1$hb^1@1$hb^3@2$2@3$1$3@1$h6^1@1$h6^3@2$2@3$1@1$he@2$d$0$0@1$h8^1@1$h8^3@2$2>1c$0@3$1$i3@2$e^2^1@2$e^4^1@2$2>1i$0@3$1$0@2$hd^2^1@2$hd^4^1@2$2@3$1$i1@1$h0@1$5^1@1$h0@1$5^3@2$2@3$1$0@1$h1@1$5^1@1$h1@1$5^3@2$2>1i$0@3$1$0@2$f^2^1@2$f^4^1@2$2>1i$0@3$1$0@2$hc^2^1@2$hc^4^1@3$1$0@1$h2@1$5^1@1$h2@1$5^3").
Proof. intros st g.
  unfold as_fm_st, as_queue_st, as_fm_link, as_fm_single. cbn [get_head].
  destruct (c_free_meta_head (ctx (put_meta g meta0 st))) as [h|].
  - cbv zeta. destruct (m_prev (get_meta_rec (put_meta g meta0 st) h)) as [p|]; repeat split; reflexivity.
  - repeat split; reflexivity.
Qed.
