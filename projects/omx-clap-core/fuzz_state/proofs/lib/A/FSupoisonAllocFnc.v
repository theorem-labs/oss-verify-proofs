(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AFfy.v, with its module paths changed; its ADDRESS literals moved to omx-clap-core/fuzz_preset's ASan build where h-mani-a2's maps/reloc-cgif-preset.A.tsv (hex) and reloc-cgif-preset.A.dec.tsv (decimal) classify and map them; every other literal is still cgif_file_fuzzer.asan's (listed in the commits that moved them). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/AFfy.v, with its module paths and module names changed; 297 of its 352 lines of code are new or changed and 504 lines of the source are left out. *)
(* The any-U twins of free(NULL) (donor lib/A/AFg3.v:399 afree_null_arm, :416 afree_null) and of free with room in the last batch and no drain (donor lib/A/AFfy.v:442 afree_common_arm, lib/A/AFfu.v:710 afree_common): afree_nullU, afree_commonU. *)
(* Shared any-U allocator, within-budget units (cgif's EV_MAX 11,776, < 2 GiB per class); the cf form (fuzz_preset / fuzz_reply, YG0dcf.v) bridges to this. *)
(* The donor walk text is kept: the facts (AFg3.FH_ok, AFfu.FH_ok and the lemmas they rest on) are applied UNCHANGED
   at mu = FSupoison.unpoison UP mem, the runs (AFh1.segN; AFga.segA, AFgc.segB, the depot call, AFge.segC) are
   applied UNCHANGED on the REAL memory with the hyps record moved there by FSupoisonAllocFncR.fhn_real / fhc_real,
   and the leaves (AFg3.FINH, AFfy.FINH) are applied UNCHANGED at mu on the post moved back by
   FSupoisonAllocFncR.retn_unpoison / at_RET_unpoison. What U adds, at the end of each walk:
   - upoison_ok B ly' S' UP for every layout above ly: free removes only the freed block, and afree_realizesU's own
     premise (every UP range outside [sptr_addr p, + req_size n)) puts UP's ranges in the blocks that remain
     (FSupoisonAllocFK.upoison_ok_free, FSupoisonAllocFncR.ablocks_keep_le / ablocks_free_keep);
   - upoisoned W' mem' UP: the runs write only inside the fixed bytes, and no shadow byte of UP is one of them
     (FSupoisonAllocFncR.free_null_regions_off_ush / free_common_regions_off_ush).
   The depot call (AFfy.v:498 D1) runs on the REAL memory: its const cells and its depot_mem_ok are moved from mu to
   it with the same region condition.
   The trace premise is afree_realizesU's (In ... (as_universe B) \/ st_nev S < EV_MAX), turned into tr_admit by
   tr_admit_call; the depot call takes its length (tr_admit_len), as the donor AFfu.v / AFfy.v do. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q YG0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0l YG0m.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AB1v AB1q AB1t AF0l AF0m AF0x AFl0.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AB1w AE3d AFeq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AFgi AFfv AFga AFgc AFge AFex AFfy AFfu.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AB13 AFgn AFfx AFh1 AFf0 AFfg AFg3.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require
FSupoison FSupoisonU FSupoisonAllocR FSupoisonAllocFK FSupoisonAllocFncR.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.
Local Open Scope am_scope.
(* Picks the disjunct of a "fixed" goal that lia proves (FSupoisonAllocFncR's pick_disj, here under a local name). *)
Ltac pdisj := first [ left; lia | right; pdisj | lia ].
(* membership in a literal list (AFfy's inl, which its section keeps local). *)
Ltac inl := cbn [In]; repeat (first [ left; reflexivity | right ]); fail.
Module FSP := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.FSupoison.
Module FSU := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.FSupoisonU.
Module FAR := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.FSupoisonAllocR.
Module FK := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.FSupoisonAllocFK.
Module FR := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.FSupoisonAllocFncR.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The depot's own memory and the globals' const cells lie in the common walk's fixed bytes.                        *)
(* ---------------------------------------------------------------------------------------------------------------- *)
Lemma depot_fixed : forall B, TfibSyms B -> forall ly regs pa nn a, depot_footprint B ly a ->
  FR.free_common_fixed ly regs pa nn a.
Proof.
intros B TB ly regs pa nn a H. unfold depot_footprint in H. rewrite (ts_depot _ TB), (ts_store _ TB) in H.
unfold FR.free_common_fixed, TFIB_DEPOT, TFIB_STORE, d_map1, TFIB_IMG_LO, TFIB_IMG_END in *.
destruct H as [X|[X|[X|X]]]; pdisj.
Qed.
Lemma const_fixed : forall B, TfibSyms B -> forall ly regs pa nn, ly_tsd ly = TFIB_TSD ->
  forall c i, In c (as_const B ly) -> 0 <= i < Z.max 1 (Z.of_nat (c_w c)) ->
  FR.free_common_fixed ly regs pa nn (aeval B ly (c_at c) + i).
Proof.
intros B TB ly regs pa nn HTSD c i Hc Hi. rewrite (ts_const _ TB) in Hc.
pose proof (proj1 (forallb_forall _ _) (AFfy.Tfib_const_loc ly) c Hc) as K. unfold AFfy.const_loc_ok in K.
assert (LOW : forall a, AFfy.low_ok a (Z.max 1 (Z.of_nat (c_w c))) = true -> FR.free_common_fixed ly regs pa nn (a + i)).
{ intros a L. unfold AFfy.low_ok in L. set (w := Z.max 1 (Z.of_nat (c_w c))) in *.
  assert (R : (TFIB_IMG_LO <= a /\ a + w <= TFIB_IAL_LO) \/ (TFIB_IAL_HI <= a /\ a + w <= TFIB_IAL_FLAG) \/
    (TFIB_IAL_FLAG + 4 <= a /\ a + w <= TFIB_IMG_END) \/
    (SHADOW_OFF + TFIB_IMG_LO / 8 <= a /\ a + w <= SHADOW_OFF + TFIB_IMG_END / 8)) by lia.
  clear L K. unfold FR.free_common_fixed, TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG, TFIB_IMG_LO, TFIB_IMG_END, SHADOW_OFF in *.
  change (65536 / 8) with 8192 in *. change (6279168 / 8) with 784896 in *.
  destruct R as [R|[R|[R|R]]]; pdisj. }
destruct (c_at c); try discriminate K; cbn [aeval].
- apply LOW, K.
- unfold FR.free_common_fixed, kThreadObjSize. pdisj.
- unfold FR.free_common_fixed. pdisj.
- rewrite HTSD. apply LOW, K.
- rewrite (ts_inst _ TB). apply LOW, K.
- rewrite (ts_tp _ TB). apply LOW, K.
- unfold FR.free_common_fixed. pdisj.
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* free of NULL, any UP (donor lib/A/AFg3.v:399 / :416).                                                            *)
(* ---------------------------------------------------------------------------------------------------------------- *)
Theorem afree_nullU : forall B, AR_laws tfibsegs B -> TfibSyms B -> forall ly S UP W regs mem md n ch,
  FSU.acall_preU tfibsegs B ly S UP W regs mem md ch -> getr regs 10 = w64 0 ->
  tfib_unwind_spec -> ly_tsd ly = TFIB_TSD ->
  amreal tfibsegs (free PNull (call_trace ly 0x531b4 regs ch) S) W (cfg_at tfibsegs 0x53070 regs mem md)
    (FSU.free_leafU tfibsegs B ly S UP W regs mem md PNull n).
Proof.
intros B LAWS TB ly S UP W regs mem md n ch PREU HA0 U1 HTSD.
pose proof PREU as (PRE_u & OKu & POu).
pose proof (FAR.ARU_of_acall_preU B ly S UP W regs mem md ch PREU) as HARU.
pose proof (am_wf B ly S (aview tfibsegs (w_H W) (FSP.unpoison UP mem)) (proj1 (proj1 PRE_u))) as WFS.
assert (FHu : AFgn.free_hyps W ly regs (FSP.unpoison UP mem) ch (st_internal_inited S))
  by exact (AFg3.FH_ok B TB ly S W regs (FSP.unpoison UP mem) md ch PRE_u HA0 tfib_ialloc_ok U1 HTSD).
pose proof (FR.fhn_real B ly S UP W mem md regs ch (st_internal_inited S) HARU FHu) as FHr.
assert (SPLIT : amreal tfibsegs (ret tt (set_internal_inited true (set_nev (st_nev S + 1) S))) W
    (cfg_at tfibsegs 0x53070 regs mem md) (FSU.free_leafU tfibsegs B ly S UP W regs mem md PNull n) ->
  amreal tfibsegs (free PNull (call_trace ly 0x531b4 regs ch) S) W (cfg_at tfibsegs 0x53070 regs mem md)
    (FSU.free_leafU tfibsegs B ly S UP W regs mem md PNull n)).
{ intros MAIN. unfold free. cbn [bind ret tick modify mcheck ibind get put set_nev set_internal_inited st_internal_inited].
  destruct (st_internal_inited S) eqn:E; cbn [ibind ret modify].
  - replace (set_nev (st_nev S + 1) S) with (set_internal_inited true (set_nev (st_nev S + 1) S)); [exact MAIN|].
    generalize E. generalize S. clear. intros S0 E0. destruct S0; cbn in E0 |- *. subst. reflexivity.
  - exact MAIN. }
apply SPLIT. clear SPLIT. cbn [ret amreal].
unfold cfg_at. rewrite <- (AFg3.wvb_self md) at 1.
eapply SRr_mono.
- exact (AFh1.segN W ly regs mem md ch (st_internal_inited S) (m_vm_materialized md) FHr).
- intros W' c' _ HR.
  destruct (FR.retn_unpoison B ly S UP W mem md regs ch (st_internal_inited S) W' c' HARU FHu HR)
    as (regs' & mem' & mat & -> & -> & HRu & POST).
  rewrite (FR.cfg_ra regs regs' mem' (with_vm_backing (m_vm_lazy md) mat md)).
  eapply (FK.free_leafU_intro B).
  + rewrite <- (FR.cfg_ra regs regs' (FSP.unpoison UP mem') (with_vm_backing (m_vm_lazy md) mat md)).
    exact (AFg3.FINH B TB ly S W regs (FSP.unpoison UP mem) md n ch PRE_u HA0 tfib_ialloc_ok U1 HTSD W _ HRu).
  + intros ly' LE. cbn [snd].
    apply (FAR.upoison_ok_keep B ly S ly' (set_internal_inited true (set_nev (st_nev S + 1) S)) UP OKu).
    intros r q m Hr Hb _ _.
    apply (FR.ablocks_keep_le B ly ly' S (set_internal_inited true (set_nev (st_nev S + 1) S)) WFS LE); [|exact Hb].
    intros x Hx. cbn [st_chunks set_internal_inited set_nev]. exact Hx.
  + exact POST.
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* free of a block with room in the last batch and no drain, any UP (donor lib/A/AFfy.v:442, lib/A/AFfu.v:710).     *)
(* ---------------------------------------------------------------------------------------------------------------- *)
Theorem afree_commonU : forall B, AR_laws tfibsegs B -> TfibSyms B ->
  forall ly S UP W regs mem md p n ch lastb initr,
  FSU.acall_preU tfibsegs B ly S UP W regs mem md ch -> In (p, n) (blocks S) ->
  (forall r, In r UP -> fst r + snd r <= sptr_addr B ly p \/ sptr_addr B ly p + req_size n <= fst r) ->
  getr regs 10 = w64 (sptr_addr B ly p) -> In (call_trace ly 0x531b4 regs ch) (as_universe B) \/ st_nev S < EV_MAX ->
  rev (qc_list (st_qthread S)) = lastb :: initr /\ Z.of_nat (length (b_items lastb)) < kBatchSlots /\
    qc_bytes (st_qthread S) + req_size n <= kQuarantineCacheMax ->
  tfib_ialloc_spec -> tfib_unwind_spec -> tfib_depot_spec B -> ly_tsd ly = TFIB_TSD ->
  amreal tfibsegs (free p (call_trace ly 0x531b4 regs ch) S) W (cfg_at tfibsegs 0x53070 regs mem md)
    (FSU.free_leafU tfibsegs B ly S UP W regs mem md p n).
Proof.
intros B LAWS TB ly S UP W regs mem md p n ch lastb initr PREU HBLK OUT HA0 HU ARM IA1 U1 D1 HTSD.
apply tr_admit_call in HU.
pose proof PREU as (PRE_u & OKu & POu).
pose proof (FAR.ARU_of_acall_preU B ly S UP W regs mem md ch PREU) as HARU.
pose proof PRE_u as PRE'.
destruct PRE' as (HAR & Hev & Hra & Hal & Hlo & Hbot & Hhi & HPRES & Hgp & Htp & Hch & HQT).
destruct HAR as (M & LED & BUD & MW & HSH).
pose proof (am_wf B ly S _ M) as WFS.
pose proof (find_user_block _ 0 0 0 S p n WFS HBLK) as (k & Hf & Hk & Hst & Hu & Hr).
pose proof ARM as ARM'. destruct ARM' as (Hrev & Hroom & Hcache).
set (pa := sptr_addr B ly p) in *. set (nn := req_size n) in *.
set (tr := call_trace ly 0x531b4 regs ch) in *. set (sp0 := bv_unsigned (getr regs 2)) in *.
(* the hyps record at mu, with the donor's own hb1 / j1 / j2 / j3 *)
assert (EX : exists hb1 j1 j2 j3, AFgi.free_hyps W ly regs (FSP.unpoison UP mem) ch pa nn hb1 (st_qthread S) lastb
    j1 j2 j3 (st_internal_inited S)).
{ do 4 eexists.
  exact (AFfu.FH_ok B TB ly S W regs (FSP.unpoison UP mem) md p n ch PRE_u HBLK HA0 lastb initr ARM IA1 U1 HTSD). }
destruct EX as (hb1 & j1 & j2 & j3 & FH).
pose proof (FR.fhc_real B LAWS ly S UP W mem md regs ch pa nn hb1 (st_qthread S) lastb j1 j2 j3
  (st_internal_inited S) HARU OUT FH) as FHr.
pose proof (FR.free_common_regions_off_ush B LAWS ly S UP W mem md regs ch pa nn hb1 (st_qthread S) lastb j1 j2 j3
  (st_internal_inited S) HARU OUT FH) as OFF.
(* UP's shadow bytes are none of the walk's fixed bytes *)
assert (NFIX : forall s, FSP.in_ush UP s = true -> ~ FR.free_common_fixed ly regs pa nn s).
{ intros s Hs X. exact (FR.ush_not_offU UP s Hs (FSP.ush_range tfibsegs B ly S UP W mem md s HARU Hs) (OFF s X)). }
set (BODY := fun s' : astate =>
(match p with
 | PNull => ret ()
 | _ => s <- get;;
   match find_user (st_chunks s) p with
   | Some k0 =>
     mcheck match ck_state k0 with CAllocated => true | CQuarantined => false end 1;;
     depot_put tr;;
     modify (fun s0 : astate => set_chunks (upd_chunk (st_chunks s0) {| ck_beg := ck_beg k0; ck_req := ck_req k0; ck_state := CQuarantined |}) s0);;
     enqueue {| ck_beg := ck_beg k0; ck_req := ck_req k0; ck_state := CQuarantined |};; maybe_drain
   | None => fail (FCheck 2)
   end
 end) s').
assert (SPLIT : amreal tfibsegs (BODY (set_internal_inited true (set_nev (st_nev S + 1) S))) W
    (cfg_at tfibsegs 0x53070 regs mem md) (FSU.free_leafU tfibsegs B ly S UP W regs mem md p n) ->
  amreal tfibsegs (free p tr S) W (cfg_at tfibsegs 0x53070 regs mem md)
    (FSU.free_leafU tfibsegs B ly S UP W regs mem md p n)).
{ intros MAIN. unfold free. cbn [bind ret tick modify mcheck ibind get put set_nev set_internal_inited st_internal_inited].
  destruct (st_internal_inited S) eqn:E; cbn [ibind ret modify].
  - replace (set_nev (st_nev S + 1) S) with (set_internal_inited true (set_nev (st_nev S + 1) S)); [exact MAIN|].
    generalize E. generalize S. clear. intros S0 E0. destruct S0; cbn in E0 |- *. subst. reflexivity.
  - exact MAIN. }
apply SPLIT. clear SPLIT. subst BODY. cbn beta.
set (k' := {| ck_beg := ck_beg k; ck_req := ck_req k; ck_state := CQuarantined |}).
assert (MAIN : amreal tfibsegs ((s <- get;;
  match find_user (st_chunks s) p with
  | Some k0 =>
    mcheck match ck_state k0 with CAllocated => true | CQuarantined => false end 1;;
    depot_put tr;;
    modify (fun s0 : astate => set_chunks (upd_chunk (st_chunks s0) {| ck_beg := ck_beg k0; ck_req := ck_req k0; ck_state := CQuarantined |}) s0);;
    enqueue {| ck_beg := ck_beg k0; ck_req := ck_req k0; ck_state := CQuarantined |};; maybe_drain
  | None => fail (FCheck 2)
  end) (set_internal_inited true (set_nev (st_nev S + 1) S))) W (cfg_at tfibsegs 0x53070 regs mem md)
  (FSU.free_leafU tfibsegs B ly S UP W regs mem md p n)).
2:{ rewrite AFfy.match_nonnull; [exact MAIN|]. intros Hp0.
  pose proof (proj1 (Forall_forall _ _) (wf_chunks _ _ _ _ _ WFS) k Hk) as CK.
  revert Hu. rewrite Hp0. unfold ck_user. destruct CK as [_ CK]. destruct (ck_beg k); cbn; try discriminate; destruct CK. }
cbn [bind get ret ibind]. change (st_chunks (set_internal_inited true (set_nev (st_nev S + 1) S))) with (st_chunks S).
rewrite Hf, Hst. cbn [mcheck ret ibind].
unfold depot_put. cbn [bind askz ibind].
apply AFfy.amreal_ask_depot.
unfold cfg_at. rewrite <- (AFg3.wvb_self md) at 1.
eapply SRr_bind;
  [exact (AFga.segA W ly regs mem md ch pa nn hb1 (st_qthread S) lastb j1 j2 j3 (st_internal_inited S)
     (m_vm_materialized md) FHr)|].
intros W1 c1 _ HU1.
eapply SRr_bind;
  [exact (AFgc.segB W ly regs mem md ch pa nn hb1 (st_qthread S) lastb j1 j2 j3 (st_internal_inited S) FHr W1 c1 HU1)|].
clear HU1. intros W2 c2 _ (-> & msD & matD & E3 & -> & HshD & HEn3 & HS & MEQD & TRQ & PRESD).
(* the two readings agree outside the run's write window and the internal allocator's zone *)
assert (AGD : forall a, ~ AFgi.WIN ly regs pa lastb a -> ~ AFgi.IZONE a -> 0 <= a < 2 ^ 64 ->
  aview tfibsegs (w_H W) (ms_mem msD) a = aview tfibsegs (w_H W) mem a).
{ intros a Hw Hz Ha. apply aview_same. apply (proj1 MEQD); rewrite unsigned_lit_small by exact Ha; assumption. }
assert (AGU : forall a, ~ AFgi.WIN ly regs pa lastb a -> ~ AFgi.IZONE a -> 0 <= a < 2 ^ 64 -> FAR.offU UP a ->
  aview tfibsegs (w_H W) (ms_mem msD) a = aview tfibsegs (w_H W) (FSP.unpoison UP mem) a).
{ intros a Hw Hz Ha Ho. rewrite (AGD a Hw Hz Ha). symmetry. exact (FAR.aview_unpoison (w_H W) UP mem a Ho). }
assert (COUT : Forall (fun c => forall i, 0 <= i < Z.max 1 (Z.of_nat (c_w c)) ->
    ~ AFgi.WIN ly regs pa lastb (aeval B ly (c_at c) + i) /\ ~ AFgi.IZONE (aeval B ly (c_at c) + i) /\
    0 <= aeval B ly (c_at c) + i < 2 ^ 64) (as_const B ly))
  by exact (AFfy.CONST_OUT B TB ly S W regs (FSP.unpoison UP mem) p n ch lastb hb1 j1 j2 j3 FH HTSD).
assert (DFPR : forall a, depot_footprint B ly a -> 0 <= a < 2 ^ 64)
  by exact (AFfy.DFP_RANGE B TB ly S W regs (FSP.unpoison UP mem) md p n ch PRE_u lastb hb1 j1 j2 j3 FH).
assert (DFPO : forall a, depot_footprint B ly a ->
    ~ AFgi.WIN ly regs pa lastb a /\ ~ AFgi.IZONE a /\ AFgi.DZONE ly a)
  by exact (AFfy.DFP_OUT B TB ly S W regs (FSP.unpoison UP mem) p n ch lastb hb1 j1 j2 j3 FH).
rewrite HshD. eapply SRr_bind.
{ pose proof (st_ok_restrict_mkst tfibsegs (w_H W) E3 _ _ HS eq_refl) as Hsh.
  rreg HS (2%bv : bv 5) R2. rewrite (HEn3 2%nat ltac:(cbv; lia)), (AFgi.E2 ly regs ch pa nn hb1 (st_qthread S) lastb j1 j2 j3) in R2.
  pose proof (lo_top ly (am_layout B ly S _ M)) as (T1 & T2 & T3 & T4 & T5 & T6 & T7).
  assert (Usp : 0 <= sp0 < 2 ^ 64) by (unfold sp0; apply u64_range).
  apply (D1 W ly (set_internal_inited true (set_nev (st_nev S + 1) S)) (ms_regs msD) (ms_mem msD) _ (sp0 - 2112) tr
    (am_layout B ly S _ M) (img_cover_of_ledger ly S md LED)
    (AFfy.s1_wf B ly S W regs (FSP.unpoison UP mem) md p n ch PRE_u lastb) (tr_admit_len _ _ _ (am_universe B ly S _ M) HU)).
  -   apply Forall_forall. intros c Hc. eapply (cell_holds_agree B ly (aview tfibsegs (w_H W) (FSP.unpoison UP mem))).
    + exact (proj1 (Forall_forall _ _) (am_const B ly S _ M) c Hc).
    + intros i Hi. destruct (proj1 (Forall_forall _ _) COUT c Hc i Hi) as (X1 & X2 & X3).
      apply AGU; [exact X1 | exact X2 | exact X3 | exact (OFF _ (const_fixed B TB ly regs pa nn HTSD c i Hc Hi))].
  -   assert (DM : depot_mem_ok B ly S (aview tfibsegs (w_H W) (FSP.unpoison UP mem))).
    { split; [|split].
      - apply Forall_forall. intros c Hc. apply (proj1 (Forall_forall _ _) (am_cells B ly S _ M)).
        unfold acells. rewrite !in_app_iff. tauto.
      - exact (am_depot B ly S _ M).
      - pose proof (am_junk B ly S _ M) as J. pose proof (am_areas B ly S _ M) as A. rewrite Forall_forall in J, A.
        repeat apply Forall_cons; try apply Forall_nil;
        first [ apply J; unfold ajunk; do 2 right; repeat (apply in_or_app; first [ left; inl | right ]); inl
              | apply A; unfold aareas; repeat (apply in_or_app; first [ left; inl | right ]); inl ]. }
    eapply (AFfy.depot_mem_ok_agree B ly S (set_internal_inited true (set_nev (st_nev S + 1) S)));
      [exact WFS | exact (am_universe B ly S _ M) | reflexivity | | exact DM].
    intros a Ha. destruct (DFPO a Ha) as (X1 & X2 & X3).
    apply AGU; [exact X1 | exact X2 | exact (DFPR a Ha) | exact (OFF _ (depot_fixed B TB ly regs pa nn a Ha))].
  - rreg HS (10%bv : bv 5) R; rewrite R, (HEn3 2%nat ltac:(cbv; lia)), (AFgi.E2 ly regs ch pa nn hb1 (st_qthread S) lastb j1 j2 j3).
    unfold sp0; f_equal; lia.
  - rreg HS (11%bv : bv 5) R; rewrite R, (HEn3 36%nat ltac:(cbv; lia)), (AFgi.EaLEN ly regs ch pa nn hb1 (st_qthread S) lastb j1 j2 j3). reflexivity.
  - rreg HS (3%bv : bv 5) R; rewrite R, (HEn3 3%nat ltac:(cbv; lia)), (AFgi.Er ly regs ch pa nn hb1 (st_qthread S) lastb j1 j2 j3 3 3%bv eq_refl). exact Hgp.
  - rreg HS (4%bv : bv 5) R; rewrite R. rewrite (ts_tp _ TB) in Htp. reflexivity.
  - rreg HS (1%bv : bv 5) R; rewrite R. apply YK0s.ret_ok_even. reflexivity.
  - intros i Hi. apply (TRQ i Hi).
  - unfold sp0. replace (bv_unsigned (getr regs 2) - 2112) with (bv_unsigned (getr regs 2) + (-264) * 8) by lia.
    rewrite Z_mod_plus_full. apply (mod0_factor _ 8 2); [lia|]. exact Hal.
  - unfold spZ, ASTACK in *; unfold sp0; lia.
  -   unfold spZ, ASTACK in *; unfold sp0; lia.
  - right. rewrite R2. unfold w64. rewrite unsigned_lit_small by (unfold spZ, ASTACK, kHighMemBeg, kHighMemEnd in *; lia). unfold sp0; lia.
  - rewrite R2. unfold w64. rewrite unsigned_lit_small by (unfold spZ, ASTACK, kHighMemBeg, kHighMemEnd in *; lia).
    replace (bv_unsigned (getr regs 2) + -2176) with (bv_unsigned (getr regs 2) + (-136) * 16) by lia.
    rewrite Z_mod_plus_full. exact Hal.
  - rewrite R2. unfold w64. rewrite unsigned_lit_small by (unfold spZ, ASTACK, kHighMemBeg, kHighMemEnd in *; lia).
    unfold spZ, ASTACK, DEP_STK in *; lia.
  - rewrite R2. unfold w64. rewrite unsigned_lit_small by (unfold spZ, ASTACK, kHighMemBeg, kHighMemEnd in *; lia).
    unfold spZ in *; lia.
  - intros a Ha. rewrite R2 in Ha. unfold w64 in Ha.
    rewrite unsigned_lit_small in Ha by (unfold spZ, ASTACK, kHighMemBeg, kHighMemEnd in *; lia).
    apply PRESD. unfold DEP_STK, ASTACK, sp0 in *. lia. }
intros W3 c3 _ (-> & z & regs4 & mem4 & mat4 & -> & AOK & HP4 & Hfr4 & Hpr4 & DEPOK & HC4). srr_norm_model.
apply SRr_ret. exists z. split; [exact AOK|].
rreg HS (1%bv : bv 5) Q1. rreg HS (2%bv : bv 5) Q2.
rewrite Q2, (HEn3 2%nat ltac:(cbv; lia)), (AFgi.E2 ly regs ch pa nn hb1 (st_qthread S) lastb j1 j2 j3) in Hfr4.
pose proof (lo_top ly (am_layout B ly S _ M)) as (T1 & T2 & T3 & T4 & T5 & T6 & T7).
rewrite unsigned_lit_small in Hfr4 by (unfold spZ, ASTACK, kHighMemBeg, kHighMemEnd in *; lia). fold sp0 in Hfr4.
assert (DZ : forall x : word, ~ (sp0 - 2176 - DEP_STK <= bv_unsigned x < sp0 - 2176) -> ~ AFgi.DZONE ly (bv_unsigned x) ->
  mem4 x = ms_mem msD x).
{ intros x Hx Hd. apply Hfr4; [lia|]. intros Hf'. apply Hd. exact (proj2 (proj2 (DFPO _ Hf'))). }
assert (TAIL : let sd := depot_after z tr (set_internal_inited true (set_nev (st_nev S + 1) S)) in
  amreal tfibsegs ((modify (fun s0 : astate => set_chunks (upd_chunk (st_chunks s0) k') s0);; enqueue k';; maybe_drain) sd)
  W (mkCfg (YK11.mkst regs4 (getr (ms_regs msD) 1) mem4 (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md) mat4 md))
  (FSU.free_leafU tfibsegs B ly S UP W regs mem md p n)).
{ cbn zeta.
  assert (Qsd : st_qthread (depot_after z tr (set_internal_inited true (set_nev (st_nev S + 1) S))) = st_qthread S)
    by (unfold depot_after; destruct (z =? 0); reflexivity).
  assert (Csd : st_chunks (depot_after z tr (set_internal_inited true (set_nev (st_nev S + 1) S))) = st_chunks S)
    by (unfold depot_after; destruct (z =? 0); reflexivity).
  unfold enqueue, maybe_drain. cbn [bind modify ibind get st_qthread set_chunks]. rewrite Qsd.
  unfold need_new_batch. rewrite Hrev.
  replace (Z.of_nat (length (b_items lastb)) =? kBatchSlots) with false by (symmetry; apply Z.eqb_neq; lia).
  cbn [bind ret ibind modify st_qthread set_qthread get set_chunks]. rewrite Qsd.
  replace (qc_bytes (qc_push (st_qthread S) k' None) <=? kQuarantineCacheMax) with true.
  2:{ symmetry. apply Z.leb_le. cbn [qc_push qc_bytes]. subst k'. unfold nn, ck_n in *. cbn [ck_req]. rewrite Hr. exact Hcache. }
  cbn [ret amreal]. rewrite Q1.
  eapply SRr_mono.
  - apply (AFge.segC W ly regs mem md ch pa nn hb1 (st_qthread S) lastb j1 j2 j3 (st_internal_inited S) FHr
      msD E3 regs4 mem4 mat4).
    split; [exact HshD|]. split; [exact HEn3|]. split; [exact HS|]. split; [exact HP4|]. split; [exact DZ|].
    split; [exact Hpr4|]. split; [exact MEQD | exact PRESD].
  - intros W' c' _ HR.
    destruct (FR.at_RET_unpoison B LAWS ly S UP W mem md regs ch pa nn hb1 (st_qthread S) lastb j1 j2 j3
      (st_internal_inited S) mem4 W' c' HARU OUT FH HR) as (regs' & mem'' & mat' & -> & -> & HRu & FRM).
    assert (MEQDu : AFgi.MEQI W ly regs (FSP.unpoison UP mem) pa lastb (ms_mem (YK11.mkst (ms_regs msD) (w64 0x72f3c) (FSP.unpoison UP (ms_mem msD)) (seg_rom tfibsegs))))
      by (unfold YK11.mkst; cbn [ms_mem];
          exact (FR.meqi_unpoison B LAWS ly S UP W mem md regs ch pa nn hb1 (st_qthread S) lastb j1 j2 j3
                  (st_internal_inited S) (ms_mem msD) HARU OUT FH MEQD)).
    assert (PRESDu : forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W) (ms_mem (YK11.mkst (ms_regs msD) (w64 0x72f3c) (FSP.unpoison UP (ms_mem msD)) (seg_rom tfibsegs))) a)
      by (intros a Ha; unfold YK11.mkst; cbn [ms_mem]; apply FAR.apresent_to_unpoison; exact (PRESD a Ha)).
    assert (FRu : forall x : word, ~ (sp0 - 2176 - DEP_STK <= bv_unsigned x < sp0 - 2176) ->
        ~ depot_footprint B ly (bv_unsigned x) -> FSP.unpoison UP mem4 x = ms_mem (YK11.mkst (ms_regs msD) (w64 0x72f3c) (FSP.unpoison UP (ms_mem msD)) (seg_rom tfibsegs)) x)
      by (intros x Hx Hd; unfold FSP.unpoison, YK11.mkst; cbn [ms_mem];
          destruct (FSP.in_ush UP (bv_unsigned x)); [reflexivity | exact (Hfr4 x Hx Hd)]).
    assert (PRu : forall a, apresent (w_H W) (ms_mem (YK11.mkst (ms_regs msD) (w64 0x72f3c) (FSP.unpoison UP (ms_mem msD)) (seg_rom tfibsegs))) a -> apresent (w_H W) (FSP.unpoison UP mem4) a)
      by (unfold YK11.mkst; cbn [ms_mem]; apply FR.apresent_unpoison_mono; exact Hpr4).
    assert (DEPu : depot_mem_ok B ly (depot_after z tr (set_internal_inited true (set_nev (st_nev S + 1) S)))
        (aview tfibsegs (w_H W) (FSP.unpoison UP mem4))).
    { apply (AFfy.depot_mem_ok_agree B ly (depot_after z tr (set_internal_inited true (set_nev (st_nev S + 1) S)))
        (depot_after z tr (set_internal_inited true (set_nev (st_nev S + 1) S)))
        (aview tfibsegs (w_H W) mem4) (aview tfibsegs (w_H W) (FSP.unpoison UP mem4)));
      [ apply (WfP_weaken _ 1 1 1); try lia;
        exact (AFex.sd_wf B ly S (aview tfibsegs (w_H W) (FSP.unpoison UP mem)) M lastb z tr Hev AOK HU)
      | exact (am_universe B ly S _ M) | reflexivity
      | intros a Ha; apply FAR.aview_unpoison; exact (OFF _ (depot_fixed B TB ly regs pa nn a Ha))
      | exact DEPOK ]. }
    assert (HCu : Forall (cell_holds B ly (aview tfibsegs (w_H W) (FSP.unpoison UP mem4))) (as_const B ly)).
    { apply Forall_forall. intros c Hc.
      apply (cell_holds_agree B ly (aview tfibsegs (w_H W) mem4));
      [ exact (proj1 (Forall_forall _ _) HC4 c Hc)
      | intros i Hi; apply FAR.aview_unpoison; exact (OFF _ (const_fixed B TB ly regs pa nn HTSD c i Hc Hi)) ]. }
    rewrite (FR.cfg_ra regs regs' mem'' (with_vm_backing (m_vm_lazy md) mat' md)).
    eapply (FK.free_leafU_intro B).
    +   rewrite <- (FR.cfg_ra regs regs' (FSP.unpoison UP mem'') (with_vm_backing (m_vm_lazy md) mat' md)).
      exact (AFfy.FINH B TB ly S W regs (FSP.unpoison UP mem) md p n ch PRE_u HBLK HU lastb initr ARM
        hb1 j1 j2 j3 FH HTSD z k (YK11.mkst (ms_regs msD) (w64 0x72f3c) (FSP.unpoison UP (ms_mem msD)) (seg_rom tfibsegs)) (FSP.unpoison UP mem4) W _ Hf AOK MEQDu PRESDu FRu PRu DEPu HCu HRu).
    + intros ly' LE. cbn [snd].
      apply (FK.upoison_ok_free B ly S ly'
        (set_qthread (qc_push (st_qthread S) k' None)
           (set_chunks (upd_chunk (st_chunks (depot_after z tr (set_internal_inited true (set_nev (st_nev S + 1) S)))) k')
              (depot_after z tr (set_internal_inited true (set_nev (st_nev S + 1) S))))) UP pa n OKu OUT).
      intros q m Hb NE.
      apply (FR.ablocks_free_keep B ly ly' S _ k WFS LE Hk); [|exact Hb|].
      * intros x Hx Hne. cbn [st_chunks set_qthread set_chunks]. rewrite Csd.
        apply FR.in_upd_chunk_other; [exact Hx | exact Hne].
      * rewrite Hu, Hr. exact NE.
    + apply (FAR.upoisoned_keep UP W W mem mem'' POu). intros s Hs.
      pose proof (FSP.ush_range tfibsegs B ly S UP W mem md s HARU Hs) as Rs.
      pose proof (NFIX s Hs) as NF.
      apply FSP.aview_at.
      rewrite (FRM (Z_to_bv 64 s)); rewrite ?(FSP.wz s Rs).
      2:{ intros X. apply NF. apply (FR.win_fixed W ly regs (FSP.unpoison UP mem) ch pa nn hb1 (st_qthread S) lastb j1 j2 j3
            (st_internal_inited S) FH). exact (AFgi.WIN2_WIN ly regs pa lastb s X). }
      2:{ intros X. apply NF. exact (FR.freed_fixed ly regs pa nn s X). }
      rewrite (Hfr4 (Z_to_bv 64 s)); rewrite ?(FSP.wz s Rs).
      2:{ intros X. apply NF. exact (FR.dstack_fixed ly regs pa nn s X). }
      2:{ intros X. apply NF. exact (depot_fixed B TB ly regs pa nn s X). }
      apply (proj1 MEQD); rewrite ?(FSP.wz s Rs).
      * intros X. apply NF. apply (FR.win_fixed W ly regs (FSP.unpoison UP mem) ch pa nn hb1 (st_qthread S) lastb j1 j2 j3
          (st_internal_inited S) FH). exact X.
      * intros X. apply NF. exact (FR.izone_fixed ly regs pa nn s X). }
destruct AOK as [-> | [-> _]].
- cbn [Z.eqb ret ibind]. exact TAIL.
- cbn [Z.eqb bind get ret ibind].
  destruct (depot_ids (set_internal_inited true (set_nev (st_nev S + 1) S)) + 1 <? kDepotIdsPerBlock);
    cbn [mcheck ret ibind]; [|exact I].
  destruct (kStartFramesMax + depot_frames (set_internal_inited true (set_nev (st_nev S + 1) S)) + Z.of_nat (length tr) + 1
    <? kStoreFramesPerBlock); cbn [mcheck ret put ibind]; [|exact I].
  exact TAIL.
Qed.
End a.
