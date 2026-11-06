(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YCbq.v, with its module paths changed and off_img's image range set to libreac/fuzz_boxreg's own (Reusable/YImgTop.v IMG_LO, IMG_TOP). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/Reusable/YCbq.v, with its module paths and module names changed; 442 of its 552 lines of code are new or changed and 2852 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSW_malloc_free.v, with its module paths changed; 570 of its 627 lines of code are new or changed and 495 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: lib/B (fs.asan-ubsan) twin of lib/A/FSW_realloc.v (this lane), same lemma
   names and statement shapes, image B's names: the B kit (lib/B/FSW_K / K3 / ret / rres / statics / poison_conv / head),
   lib/B/FSH_Fn_alloc.v's specs, the image-free realloc model lib/A/FSH_ReallocModelG.v and contract
   lib/A/FSupoisonReallocG.v through lib/B/FSH_ReallocModel.v / lib/B/FSupoisonRealloc.v (a Theorem Labs lane b7139cbe20d:
   FS_AREALLOC_BU at FS_AREALLOC_PC_B 0x530e8 / FS_AREALLOC_IPC_B 0x53620). No lib/A image file is Required.
   proves function fuzz_realloc (B 0x82bc4) (reuse search: proof-index on main@f4cc67298b7 / ossv/recipes@5121fb8693b
   / ossv/candidates@ee89628c997 / release/pau-projects-recipes@b6a0088adcb, by address on those four refs, and on named
   lane branches / `proof-index fuzz_realloc`, `git grep -i -e <addr>`, `git grep -E '^(Theorem|Lemma)
   .*fuzz_realloc_spec'`; B 0x82bc4: 0 hits, CONFIRM). *)
(*
   port-from: lib/A/FSW_realloc.v (image A, this lane; its port-from list applies unchanged: the released plain control
   flow, the realloc model and its any-U contract, cgif_rgb's realloc call site, the donor's granted-allocation rule).
   The image-free model lemmas (free_null_eq, atok_flag_free, realloc_tree_tok, arealloc_granted, realloc_ticks3,
   split_snoc, pairwise_head_once) are copied verbatim: A's file is image A and may not be Required here.
   B-specific: fsr_p0 walks B's p = 0 path (frame 32; 0x82bdc `beqz a0` taken; 0x82c14 a0 = s0 = n, restore ra / s0 /
   s1 / s2, `j fuzz_malloc` 0x82c2c -> 0x82a58; MEASURED, capstone on the unstripped twin of the pinned fs.asan-ubsan).
   No rename. Relocated files: none.

   NAMED PREMISES (arguments of the lemmas, listed with owners in the lane report):
   - FS_AREALLOC_BU: lib/B/FSupoisonRealloc.FS_AREALLOC_BU (as_universe B), the any-U realloc contract at B's
     0x530e8 / trace ipc 0x53620 (C5 trace premise `In .. \/ st_nev S + 2 < EV_MAX`, closed here from the call site's
     room premise; stack margin `ly_bot ly + 0x8a0 < spZ regs`, from the STK_RT_REALLOC budget). Owner: a Theorem Labs lane,
     through another Theorem Labs lane. An ARGUMENT of fsw_aj_reallocU.
   - fuzz_malloc_spec (lib/B/FSH_Fn_alloc): an ARGUMENT of fsr_p0; a Theorem Labs lane's lib/B fuzz_malloc_holds
     discharges it.
   - api_env (FS_ENV): a fact of fs's TfibB, owner RELOC.

   THE NULL ARM OF THE REALLOC MODEL IS DEAD, PROVED HERE (realloc_tree_tok, arealloc_granted), as in lib/A: fuzz_realloc
   asks realloc for HEAD + n >= 16 bytes and never passes NULL (B: p = 0 branches to fuzz_malloc at 0x82bdc), so the
   model's inner malloc answers NULL only on a refused kernel request (ml_malloc_ns: flag false), and the run follows a
   granted path (amreal_SRr04: gflag = true). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YM05 YG00 YG0a YG01 YG0l YG0d YG0f YG0n YG05 YG08 YG0q YCbq YI16.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSupoison FSupoisonU FSpoisonS FSH_YC20 FSH_Gen.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import
YB1v YB1w FSH_Base FSH_Rt FSPstat FSH_Fn_alloc FSH_ReallocModel FSupoisonRealloc
FSW_K FSW_K3 FSW_ret FSW_rres FSW_rd FSW_statics FSW_statics_awr FSW_head FSW_poison_conv FSW_fuzz_realloc_tbl.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The realloc model: free PNull ticks only; the granted path never answers NULL.                                   *)
(* ---------------------------------------------------------------------------------------------------------------- *)

(* FSH_ReallocModel's free_null_eq_stmt (cgif_rgb YG0f.v:35-40): the model's free of PNull makes no request. *)
Lemma free_null_eq : free_null_eq_stmt.
Proof.
intros tr s. unfold free, realloc_s1, tick, get, modify, ret, YG00.bind. cbn.
destruct (st_internal_inited s) eqn:E; [|reflexivity].
destruct s; cbn in *. subst. reflexivity.
Qed.

(* an atok whose post ignores the flag holds from any flag, once it holds from the true one *)
Lemma atok_flag_free : forall {A} (t : itree astate A) ns (Q : bool -> A -> Prop) (P : A -> Prop),
  atok true t Q -> (forall b a, Q b a -> P a) -> atok ns t (fun _ a => P a).
Proof.
intros A t ns Q P H HP. destruct t as [a | q snap k | pc | f]; cbn in *.
- exact (HP true a H).
- destruct H as [Hr Hk]. split; [exact Hr|]. intros z Hz. eapply atok_mono; [|exact (Hk z Hz)].
  intros b a HQ. exact (HP b a HQ).
- discriminate H.
- exact H.
Qed.

(* realloc_tree from the true flag: an answer of PNull carries the false flag (a refused kernel request). Premises:
   the model's own (Wf, the old block live, the trace's length within kUnwindMax: C5's model laws) and room for its
   three ticks. *)
Lemma realloc_tree_tok : forall (TU : list (list Z)) S p n_old n tr,
  model_laws TU -> Wf TU S -> st_nev S + 2 < EV_MAX -> 0 <= n < MALLOC_MAX -> blocks_bytes S + n <= LIVE_MAX ->
  In (p, n_old) (blocks S) -> (length tr <= kUnwindMax)%nat ->
  atok true (realloc_tree p n tr S) (fun ns r => fst r = PNull -> ns = false).
Proof.
intros TU S p n_old n tr ML HWF Hev Hn Hlive Hin Htr.
pose proof (ml_free _ ML S PNull 0 tr HWF ltac:(lia) (or_introl eq_refl) Htr) as HF0.
rewrite free_null_eq in HF0. cbn in HF0. destruct HF0 as (HWF1 & _).
set (s1 := realloc_s1 S) in *.
assert (Hnev1 : st_nev s1 = st_nev S + 1) by reflexivity.
assert (Hbl1 : blocks s1 = blocks S) by reflexivity.
assert (Hbb1 : blocks_bytes s1 = blocks_bytes S) by reflexivity.
unfold realloc_tree. apply atok_bind. rewrite free_null_eq. cbn [atok fst snd]. fold s1.
apply atok_bind.
assert (Hadm : tr_admit TU s1 tr) by (right; split; [exact Htr | lia]).
eapply atok_mono;
  [|exact (ml_malloc_ns _ ML s1 n tr HWF1 (regime_ok_small s1 ltac:(lia)) Hn ltac:(lia) Hadm)].
intros ns [q s2] [HMP HNS]. cbn [fst snd] in HMP, HNS |- *.
destruct HMP as (HWF2 & Hnev2 & _ & _ & HBL & _).
destruct q as [|o|r o|c o]; cbn beta iota.
{ cbn. intros _. exact (HNS eq_refl). }
all: destruct HBL as [Hbl2 _]; assert (Hin2 : In (p, n_old) (blocks s2))
       by (rewrite Hbl2, Hbl1; apply in_or_app; left; exact Hin);
     apply atok_bind;
     eapply atok_mono;
       [|exact (atok_flag_free (free p tr s2) ns _ (fun _ => True)
                 (ml_free _ ML s2 p n_old tr HWF2 ltac:(lia) (or_intror Hin2) Htr) (fun _ _ _ => I))];
     intros b [[] s3] _; cbn; intros E; discriminate E.
Qed.

(* THE NULL ARM IS DEAD: a machine run that realizes realloc_tree (amreal, as the realloc contract's leaf states it)
   lands, at every reachable end, in a post whose model answer is not PNull. The run follows a granted path
   (amreal_SRr04: gflag = true), so the flag the answer carries is true (last_flag_true), and realloc_tree_tok
   says a PNull answer carries the false flag. *)
Lemma arealloc_granted : forall segs (TU : list (list Z)) S p n_old n tr W c
  (Q : sptr * astate -> world segs -> config -> Prop),
  model_laws TU -> Wf TU S -> st_nev S + 2 < EV_MAX -> 0 <= n < MALLOC_MAX -> blocks_bytes S + n <= LIVE_MAX ->
  In (p, n_old) (blocks S) -> (length tr <= kUnwindMax)%nat ->
  amreal segs (realloc_tree p n tr S) W c Q ->
  SRr segs W c (fun W' c' => exists r, fst r <> PNull /\ Q r W' c').
Proof.
intros segs TU S p n_old n tr W c Q ML HWF Hev Hn Hlive Hin Htr HREAL.
pose proof (realloc_tree_tok TU S p n_old n tr ML HWF Hev Hn Hlive Hin Htr) as HTOK.
eapply SRr_mono.
{ exact (amreal_SRr04 segs _ W c Q HREAL (atok_asafe _ _ _ HTOK) (atok_agprog _ _ _ HTOK) (atok_nospin _ _ HTOK)). }
intros W' c' _ (r & tr' & Hpath & Hgf & HQ). exists r. split; [|exact HQ].
pose proof (atok_apath_flag _ _ _ tr' r HTOK Hpath) as HN. cbv beta in HN. rewrite (last_flag_true tr' Hgf) in HN.
intros E. discriminate (HN E).
Qed.

(* the three ticks of a realloc that answers a block (a Theorem Labs lane's realloc_ticks, cgif_rgb ReallocAll.v:30-34) *)
Lemma realloc_ticks3 : forall (TU : list (list Z)) S n ns q S2 p n_old ns' S3,
  realloc_mpost TU S n ns (q, S2) -> realloc_fpost TU S2 p n_old ns' (tt, S3) -> st_nev S3 = st_nev S + 3.
Proof.
intros TU S n ns q S2 p n_old ns' S3 ((_ & NE & _) & _) ((_ & NF & _) & _). cbn [snd] in NF.
unfold realloc_s1 in NE. cbn [st_nev set_nev set_internal_inited] in NE. lia.
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* Lists                                                                                                            *)
(* ---------------------------------------------------------------------------------------------------------------- *)

(* an element found in m ++ [y] that is not y sits inside m. Port-from: cgif_rgb_fuzzer lib/YC07.v split_snoc
   (origin/ossv/recipes), statement and proof verbatim. *)
Lemma split_snoc : forall {X} (l1 l2 m : list X) x y, l1 ++ x :: l2 = m ++ [y] -> x <> y ->
  exists l2', l2 = l2' ++ [y] /\ m = l1 ++ x :: l2'.
Proof.
intros X l1 l2 m x y E Hxy. destruct (exists_last (l := x :: l2) ltac:(discriminate)) as (l' & z & El).
rewrite El in E. rewrite app_assoc in E. apply app_inj_tail in E as [Em Ez]. subst z.
destruct l2 as [|w l2] using rev_ind.
- destruct l' as [|u l']; [cbn in El; injection El as El; exact (False_ind _ (Hxy El))|]. cbn in El. injection El as _ El. destruct l'; discriminate El.
- clear IHl2. exists l2. rewrite app_comm_cons in El. apply app_inj_tail in El as [El Ew]. subst w. split; [reflexivity|]. rewrite <- Em, <- El. reflexivity.
Qed.

(* a 16-byte head that occurs once in a pairwise-disjoint list does not occur in the rest *)
Lemma pairwise_head_once : forall (U1 U2 : list (Z * Z)) h,
  pairwise zdisjoint (U1 ++ (h, 16) :: U2) -> ~ In (h, 16) (U1 ++ U2).
Proof.
intros U1 U2 h P Hin.
assert (P' : pairwise zdisjoint ((h, 16) :: U1 ++ U2)).
{ apply (FSupoisonU.pairwise_zdisjoint_perm (U1 ++ (h, 16) :: U2)); [|exact P]. symmetry. apply Permutation_middle. }
destruct P' as [F _]. pose proof (proj1 (Forall_forall _ _) F _ Hin) as D. unfold zdisjoint in D. cbn [fst snd] in D. lia.
Qed.

Section k. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.

(* a frame on the machine memories outside U's shadow bytes is a frame on the unpoisoned memories
   (FSW_poison_conv.fsw_unpoison_view0 at both ends) *)
Lemma fsr_unpoison_view : forall ly S ly' S' U (W W' : world tfibsegs) mem mem' md md' a,
  ARU tfibsegs B ly S U W mem md -> ARU tfibsegs B ly' S' U W' mem' md' -> 0 <= a < 2 ^ 64 ->
  (in_ush U a = false -> aview tfibsegs (w_H W') mem' a = aview tfibsegs (w_H W) mem a) ->
  aview tfibsegs (w_H W') (unpoison U mem') a = aview tfibsegs (w_H W) (unpoison U mem) a.
Proof.
intros ly S ly' S' U W W' mem mem' md md' a H H' Ha F.
destruct (in_ush U a) eqn:E.
- rewrite (fsw_unpoison_view0 B ly' S' U W' mem' md' a H' E), (fsw_unpoison_view0 B ly S U W mem md a H E). reflexivity.
- rewrite !(aview_unpoison_out tfibsegs) by (rewrite (wz a Ha); exact E). exact (F eq_refl).
Qed.

(* astk_ok is a fact of the layout's stack fields, which layout_le keeps *)
Lemma fsr_astk_ok_le : forall n stk ly ly' sp, layout_le n ly ly' -> astk_ok stk ly sp -> astk_ok stk ly' sp.
Proof.
intros n stk ly ly' sp Hly Hs.
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
unfold astk_ok, ly_bot in *. rewrite Etop, Eslo, Eshi. exact Hs.
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* One astageU of the realloc leaf as a journal over the unpoisoned memories (YCbq.v call_effect_journal).          *)
(* ---------------------------------------------------------------------------------------------------------------- *)

Lemma fsr_astageU_journal : forall stk lyc Sc Uc (Wc : world tfibsegs) regs memc mdc (E : Z -> Prop) ly2 S2 W2 mem2
  md2 FP1 k1,
  api_env tfibsegs B ->
  astageU tfibsegs B stk lyc Sc Uc Wc regs memc mdc E ly2 S2 W2 mem2 md2 ->
  ARU tfibsegs B lyc Sc Uc Wc memc mdc ->
  astk_ok stk lyc (spZ regs) ->
  frames S2 = frames Sc -> st_nev S2 <= st_nev Sc + k1 -> 0 <= k1 ->
  (length (st_secs Sc) <= length (st_secs S2))%nat ->
  (forall a, E a -> exists b m, (In (b, m) (ablocks B lyc Sc) \/ In (b, m) (ablocks B ly2 S2)) /\
     b <= a < b + req_size m /\ (inFP FP1 a \/ ~ In (b, m) (ablocks B lyc Sc))) ->
  (forall p n i, In (p, n) (ablocks B lyc Sc) -> ~ In (p, n) (ablocks B ly2 S2) -> 0 <= i < req_size n ->
     inFP FP1 (p + i)) ->
  qtight S2 ->
  ajournal tfibsegs B stk (spZ regs) FP1 lyc Sc Wc (unpoison Uc memc) mdc [] ly2 S2 W2 (unpoison Uc mem2) md2 k1.
Proof.
intros stk lyc Sc Uc Wc regs memc mdc E ly2 S2 W2 mem2 md2 FP1 k1 ENV (HARU2 & Hly & Hwle & Hio & Hfr & Hpres) HARU
  Hstk Hfrs Hnev Hk Hsecs HE Hgone HQT.
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & _ & C3 & _).
apply (call_effect_journal tfibsegs B LAWS fs_segs_low ENV stk lyc Sc Wc regs (unpoison Uc memc) mdc ly2 S2 W2
  (unpoison Uc mem2) md2 E FP1 [] k1).
all: first
  [ solve [exact (proj1 HARU2)] | solve [exact Hly] | solve [exact Hwle] | solve [exact Hio]
  | solve [exact (proj1 HARU)] | solve [exact Hstk] | solve [exact Hfrs] | solve [exact Hnev] | solve [exact Hk]
  | solve [exact Hsecs] | solve [exact HE] | solve [exact Hgone] | solve [exact HQT]
  | solve [intros a Ha Ho1 Ho2 Hs He;
           apply (fsr_unpoison_view lyc Sc ly2 S2 Uc Wc W2 memc mem2 mdc md2 a HARU HARU2 Ha);
           intros _; exact (Hfr a Ha Ho1 Ho2 Hs He)]
  | solve [intros a Ha; apply (fsw_apresent_poison B ly2 S2 Uc W2 mem2 md2 a HARU2);
           first [solve [lia] | solve [exact (Hpres a Ha)]]] ].
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The realloc leaf (FSupoisonRealloc.arealloc_leafU) at a non-PNull answer: the return state, the call's journal  *)
(* over the unpoisoned memories (window ASTACK below the call's sp, footprint the old block), ARU at the same U, the   *)
(* block list with the old block swapped for the new one at the end, the kept bytes, three ticks.                    *)
(* ---------------------------------------------------------------------------------------------------------------- *)

Lemma fsr_realloc_leaf : forall TU Uc lyc Sc (Wc : world tfibsegs) regsC memc mdc p' n_old n' r W' c',
  api_env tfibsegs B ->
  ARU tfibsegs B lyc Sc Uc Wc memc mdc ->
  astk_ok ASTACK lyc (spZ regsC) ->
  In (p', n_old) (blocks Sc) -> sptr_addr B lyc p' <> 0 -> 0 <= n' ->
  fst r <> PNull ->
  arealloc_leafU tfibsegs B TU Uc lyc Sc Wc regsC memc mdc p' n_old n' r W' c' ->
  exists ly' regs' mem' md',
    c' = cfg_at tfibsegs (raZ regsC) regs' mem' md' /\ aregs_preserved regsC regs' /\
    getr regs' 10 = w64 (sptr_addr B ly' (fst r)) /\
    ajournal tfibsegs B ASTACK (spZ regsC) (ablocks_fp [(sptr_addr B lyc p', n_old)])
      lyc Sc Wc (unpoison Uc memc) mdc [] ly' (snd r) W' (unpoison Uc mem') md' 3 /\
    ARU tfibsegs B ly' (snd r) Uc W' mem' md' /\
    (exists b1 b2, ablocks B lyc Sc = b1 ++ (sptr_addr B lyc p', n_old) :: b2 /\
       ablocks B ly' (snd r) = (b1 ++ b2) ++ [(sptr_addr B ly' (fst r), n')]) /\
    (forall i, 0 <= i < Z.min n_old n' ->
       aview tfibsegs (w_H W') mem' (sptr_addr B ly' (fst r) + i) = aview tfibsegs (w_H Wc) memc (sptr_addr B lyc p' + i)) /\
    st_nev (snd r) = st_nev Sc + 3 /\ frames (snd r) = frames Sc.
Proof.
intros TU Uc lyc Sc Wc regsC memc mdc p' n_old n' r W' c' ENV HARU Hstk Hin Hp0 Hn' Hnn Hleaf.
destruct Hleaf as (ly' & regs' & mem' & md' & Ec & HP & R10 & QT & REST).
destruct r as [q S']. cbn [fst snd] in *.
assert (REST' : exists ly2 S2 W2 mem2 md2,
  astageU tfibsegs B ASTACK lyc Sc Uc Wc regsC memc mdc
    (fun a => sptr_addr B ly2 q <= a < sptr_addr B ly2 q + req_size n') ly2 S2 W2 mem2 md2 /\
  (exists ns, realloc_mpost TU Sc n' ns (q, S2)) /\ qtight S2 /\
  (forall i, 0 <= i < Z.min n_old n' ->
     aview tfibsegs (w_H W2) mem2 (sptr_addr B ly2 q + i) = aview tfibsegs (w_H Wc) memc (sptr_addr B lyc p' + i)) /\
  astageU tfibsegs B ASTACK ly2 S2 Uc W2 regsC mem2 md2
    (fun a => sptr_addr B lyc p' <= a < sptr_addr B lyc p' + req_size n_old) ly' S' W' mem' md' /\
  (exists ns, realloc_fpost TU S2 p' n_old ns (tt, S')))
  by (destruct q; [exfalso; exact (Hnn eq_refl) | exact REST | exact REST | exact REST]).
clear REST.
destruct REST' as (ly2 & S2 & W2 & mem2 & md2 & A1 & (ns & M1) & QT2 & CPY & A2 & (ns' & F2)).
pose proof asan_consts as (C1 & _ & C3 & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (proj1 HARU) as HARc.
pose proof A1 as (HARU2 & Hly1 & _ & _ & _ & _). pose proof (proj1 HARU2) as HAR2.
pose proof A2 as (HARU' & Hly2 & _ & _ & Hfr2 & _). pose proof (proj1 HARU') as HAR'.
(* the model posts *)
destruct M1 as (MP & _ & _). destruct F2 as (FP2 & _).
assert (MP' : Wf TU S2 /\ st_nev S2 = st_nev Sc + 2 /\ secs_ext (realloc_s1 Sc) S2 /\ frames S2 = frames Sc /\
  (blocks S2 = blocks Sc ++ [(q, n')] /\ ~ In q (map fst (blocks Sc))))
  by (destruct q; [exfalso; exact (Hnn eq_refl) | | |];
      destruct MP as (W1 & N1 & X1 & F1 & B1 & _); cbn [st_nev realloc_s1 set_nev set_internal_inited] in N1;
      (split; [exact W1 | split; [lia | split; [exact X1 | split; [exact F1 | exact B1]]]])).
clear MP. destruct MP' as (_ & Hnev2 & Hsecs2 & Hfrs2 & Hbl2 & Hfresh).
assert (Hpn : p' <> PNull) by (intros ->; exact (Hp0 eq_refl)).
destruct FP2 as (_ & Hnev' & Hsecs' & Hfrs' & (l1 & l2 & Hsp & Hbl') & _). cbn [snd] in *.
destruct Hsp as [[E _] | Hbl2'] ; [exfalso; exact (Hpn E)|].
(* the old block sits in blocks Sc *)
assert (NE : (p', n_old) <> (q, n')).
{ intros E. injection E as E _. subst q. apply Hfresh. apply (in_map fst _ (p', n_old)). exact Hin. }
rewrite Hbl2 in Hbl2'. destruct (split_snoc _ _ _ _ _ (eq_sym Hbl2') NE) as (l2' & El2 & Ebl). subst l2.
(* layouts: old blocks keep their addresses *)
destruct (al_layout _ _ LAWS lyc Sc Wc (unpoison Uc memc) mdc ly2 HARc Hly1) as (Eab1 & _ & _).
destruct (al_layout _ _ LAWS ly2 S2 W2 (unpoison Uc mem2) md2 ly' HAR2 Hly2) as (Eab2 & _ & _).
unfold ablocks in Eab1, Eab2.
set (fc := fun b : sptr * Z => (sptr_addr B lyc (fst b), snd b)) in *.
set (f2 := fun b : sptr * Z => (sptr_addr B ly2 (fst b), snd b)) in *.
set (f' := fun b : sptr * Z => (sptr_addr B ly' (fst b), snd b)) in *.
assert (E2c : forall b, In b (blocks Sc) -> f2 b = fc b) by (intros b Hb; exact (map_eq_In f2 fc _ b Eab1 Hb)).
assert (E'2 : forall b, In b (blocks S2) -> f' b = f2 b) by (intros b Hb; exact (map_eq_In f' f2 _ b Eab2 Hb)).
assert (Hq2 : In (q, n') (blocks S2)) by (rewrite Hbl2; apply in_or_app; right; left; reflexivity).
assert (Eq' : sptr_addr B ly' q = sptr_addr B ly2 q) by (exact (f_equal fst (E'2 _ Hq2))).
assert (Hinc : forall b, In b (blocks Sc) -> In b (blocks S2)) by (intros b Hb; rewrite Hbl2; apply in_or_app; left; exact Hb).
assert (Ep' : sptr_addr B ly2 p' = sptr_addr B lyc p') by (exact (f_equal fst (E2c _ Hin))).
set (res2 := sptr_addr B ly2 q) in *.
set (old := sptr_addr B lyc p') in *.
(* the three block lists *)
assert (Ab_c : ablocks B lyc Sc = map fc l1 ++ (old, n_old) :: map fc l2') by (unfold ablocks; rewrite Ebl, map_app; reflexivity).
assert (Ab_2 : ablocks B ly2 S2 = ablocks B lyc Sc ++ [(res2, n')]).
{ unfold ablocks. fold f2. fold fc. rewrite Hbl2, map_app. cbn [map]. f_equal. exact Eab1. }
assert (Ab' : ablocks B ly' S' = (map fc l1 ++ map fc l2') ++ [(res2, n')]).
{ unfold ablocks. fold f'. rewrite Hbl'. rewrite !map_app. cbn [map]. rewrite <- app_assoc.
  assert (K : forall l, (forall b, In b l -> In b (blocks Sc)) -> map f' l = map fc l).
  { intros l Hl. apply map_ext_in. intros b Hb. rewrite (E'2 b (Hinc b (Hl b Hb))). exact (E2c b (Hl b Hb)). }
  rewrite (K l1), (K l2');
    try (intros b Hb; rewrite Ebl; apply in_or_app; first [left; exact Hb | right; right; exact Hb]).
  unfold f' at 1. cbn [fst snd]. rewrite Eq'. reflexivity. }
(* the new block is not an old one, and is disjoint from the old block *)
assert (Hold2 : In (old, n_old) (ablocks B lyc Sc)) by (rewrite Ab_c; apply in_or_app; right; left; reflexivity).
assert (Hreq : forall m, 0 <= m -> 0 < req_size m) by (intros m Hm; unfold req_size; destruct (Z.eqb_spec m 0); lia).
assert (Hnold : 0 <= n_old) by (destruct (al_blocks _ _ LAWS lyc Sc Wc _ mdc old n_old HARc Hold2) as (_ & _ & _ & _ & _ & _ & HN); lia).
assert (Hnew_not : ~ In (res2, n') (ablocks B lyc Sc)).
{ intros Hc. apply in_split in Hc as (x1 & x2 & Ex).
  pose proof (sep_blocks_pos tfibsegs B LAWS ly2 S2 W2 _ md2 (res2, n') (res2, n') x1 x2 [] HAR2
    ltac:(rewrite Ab_2, Ex, <- app_assoc; reflexivity)) as D.
  unfold zdisjoint, block_rng in D. cbn [fst snd] in D. pose proof (Hreq n' Hn'). lia. }
assert (Dsep : zdisjoint (block_rng (old, n_old)) (block_rng (res2, n'))).
{ apply (sep_blocks_pos tfibsegs B LAWS ly2 S2 W2 _ md2 (old, n_old) (res2, n') (map fc l1) (map fc l2') [] HAR2).
  rewrite Ab_2, Ab_c, <- app_assoc. reflexivity. }
unfold zdisjoint, block_rng in Dsep. cbn [fst snd] in Dsep.
assert (Hnew2 : In (res2, n') (ablocks B ly2 S2)) by (rewrite Ab_2; apply in_or_app; right; left; reflexivity).
assert (Hnew' : In (res2, n') (ablocks B ly' S')) by (rewrite Ab'; apply in_or_app; right; left; reflexivity).
assert (Hold2' : In (old, n_old) (ablocks B ly2 S2)) by (rewrite Ab_2; apply in_or_app; left; exact Hold2).
(* the two stage journals *)
set (FP1 := ablocks_fp [(old, n_old)]).
assert (InFP1 : forall a, old <= a < old + req_size n_old -> inFP FP1 a).
{ intros a Ha. exists (old, old + req_size n_old). split; [left; reflexivity | cbn [fst snd]; lia]. }
assert (InFP1' : forall a, inFP FP1 a -> old <= a < old + req_size n_old).
{ intros a (rg & [<-|[]] & Ha). cbn [fst snd] in Ha. exact Ha. }
assert (J1 : ajournal tfibsegs B ASTACK (spZ regsC) FP1 lyc Sc Wc (unpoison Uc memc) mdc [] ly2 S2 W2 (unpoison Uc mem2) md2 2).
{ apply (fsr_astageU_journal ASTACK lyc Sc Uc Wc regsC memc mdc _ ly2 S2 W2 mem2 md2 FP1 2 ENV A1 HARU Hstk).
  - exact Hfrs2.
  - lia.
  - lia.
  - exact (secs_ext_length _ _ Hsecs2).
  - intros a Ha. exists res2, n'. split; [right; exact Hnew2|]. split; [exact Ha | right; exact Hnew_not].
  - intros pp nn i H1 H2 _. exfalso. apply H2. rewrite Ab_2. apply in_or_app. left. exact H1.
  - exact QT2. }
assert (J2 : ajournal tfibsegs B ASTACK (spZ regsC) FP1 ly2 S2 W2 (unpoison Uc mem2) md2 [] ly' S' W' (unpoison Uc mem') md' 1).
{ apply (fsr_astageU_journal ASTACK ly2 S2 Uc W2 regsC mem2 md2 _ ly' S' W' mem' md' FP1 1 ENV A2 HARU2
    (fsr_astk_ok_le _ _ _ _ _ Hly1 Hstk)).
  - exact Hfrs'.
  - lia.
  - lia.
  - exact (secs_ext_length _ _ Hsecs').
  - intros a Ha. exists old, n_old. split; [left; exact Hold2'|]. split; [exact Ha | left; exact (InFP1 a Ha)].
  - intros pp nn i H1 H2 Hi.
    assert (Epn : (pp, nn) = (old, n_old)).
    { rewrite Ab_2, Ab_c in H1. rewrite Ab' in H2.
      apply in_app_or in H1 as [H1|H1]; [apply in_app_or in H1 as [H1|[H1|H1]]|].
      - exfalso. apply H2. apply in_or_app. left. apply in_or_app. left. exact H1.
      - exact (eq_sym H1).
      - exfalso. apply H2. apply in_or_app. left. apply in_or_app. right. exact H1.
      - exfalso. apply H2. apply in_or_app. right. exact H1. }
    injection Epn as -> ->. apply InFP1. lia.
  - exact QT. }
pose proof (ajournal_sub tfibsegs B LAWS fs_segs_low ASTACK (spZ regsC) FP1 lyc Sc Wc (unpoison Uc memc) mdc []
  ly2 S2 W2 (unpoison Uc mem2) md2 2 ASTACK (spZ regsC) FP1 [] ly' S' W' (unpoison Uc mem') md' 1 J1 J2
  ltac:(lia) ltac:(lia)
  ltac:(intros a Ha; left; split; [exact Ha | exists old, n_old; split; [exact Hold2' | exact (InFP1' a Ha)]]))
  as J.
exists ly', regs', mem', md'.
split; [exact Ec|]. split; [exact HP|]. split; [exact R10|].
split; [exact J|]. split; [exact HARU'|].
split; [exists (map fc l1), (map fc l2'); rewrite Eq'; split; [exact Ab_c | exact Ab']|].
split.
{ intros i Hi. rewrite Eq'. rewrite <- (CPY i Hi).
  assert (Hi' : 0 <= i < req_size n') by (unfold req_size; destruct (Z.eqb_spec n' 0); lia).
  destruct (al_blocks _ _ LAWS ly2 S2 W2 _ md2 res2 n' HAR2 Hnew2) as (_ & H4096 & Hc2 & _ & Hb2 & _).
  destruct (al_blocks _ _ LAWS ly' S' W' _ md' res2 n' HAR' Hnew') as (_ & _ & _ & _ & Hb' & _).
  apply Hfr2.
  - lia.
  - exact (proj2 (Hb2 (res2 + i) ltac:(lia))).
  - exact (proj2 (Hb' (res2 + i) ltac:(lia))).
  - intros [Hs|He].
    + pose proof (fsr_astk_ok_le _ _ _ _ _ Hly1 Hstk) as (_ & _ & Hc' & Hs' & _). lia.
    + exact (blk_img tfibsegs B LAWS ly2 S2 W2 _ md2 res2 n' (res2 + i) HAR2 Hnew2 ltac:(lia)
        (proj1 (proj2 ENV) _ He)).
  - cbv beta. pose proof (Hreq n_old Hnold). lia. }
split; [lia | rewrite Hfrs'; exact Hfrs2].
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The heads after the swap: the old head (removed by the unpoison) leaves U1 ++ U2 in the kept blocks; the new head *)
(* (h, 16) of the new block is disjoint from all of them and fs_heads holds of U1 ++ U2 ++ [(h, 16)].               *)
(* ---------------------------------------------------------------------------------------------------------------- *)

Lemma fsr_new_heads : forall ly S ly' S' (W' : world tfibsegs) mem' md' U1 U2 hold k h n b1 b2,
  AR tfibsegs B ly' S' W' mem' md' ->
  fs_heads B ly S (U1 ++ (hold, 16) :: U2) -> pairwise zdisjoint (U1 ++ (hold, 16) :: U2) ->
  ablocks B ly S = b1 ++ (hold, k + 16) :: b2 ->
  ablocks B ly' S' = (b1 ++ b2) ++ [(h, n + 16)] -> 0 <= n ->
  fs_heads B ly' S' (U1 ++ U2) /\ fs_heads B ly' S' (U1 ++ U2 ++ [(h, 16)]) /\ Forall (zdisjoint (h, 16)) (U1 ++ U2).
Proof.
intros ly S ly' S' W' mem' md' U1 U2 hold k h n b1 b2 HAR' FH PW Eb Eb' Hn.
pose proof (pairwise_head_once U1 U2 hold PW) as Honce.
assert (OLD : forall r, In r (U1 ++ U2) -> snd r = 16 /\ exists m, In (fst r, m) (b1 ++ b2) /\ 16 <= req_size m).
{ intros r Hr.
  assert (Hr' : In r (U1 ++ (hold, 16) :: U2)) by (apply in_app_or in Hr as [H|H]; apply in_or_app; [left | right; right]; exact H).
  destruct (FH r Hr') as (E16 & m & Hm & M16). split; [exact E16|]. exists m. split; [|exact M16].
  rewrite Eb in Hm. apply in_app_or in Hm as [Hm|[Hm|Hm]]; [apply in_or_app; left; exact Hm | | apply in_or_app; right; exact Hm].
  exfalso. injection Hm as E1 _. destruct r as [x s]. cbn [fst snd] in *. subst x s. exact (Honce Hr). }
assert (H1 : fs_heads B ly' S' (U1 ++ U2)).
{ intros r Hr. destruct (OLD r Hr) as (E16 & m & Hm & M16). split; [exact E16|]. exists m. split; [|exact M16].
  rewrite Eb'. apply in_or_app. left. exact Hm. }
split; [exact H1|]. split.
- intros r Hr. apply in_app_or in Hr as [Hr|Hr]; [apply H1; apply in_or_app; left; exact Hr|].
  apply in_app_or in Hr as [Hr|[<-|[]]]; [apply H1; apply in_or_app; right; exact Hr|].
  cbn [fst snd]. split; [reflexivity|]. exists (n + 16). split; [rewrite Eb'; apply in_or_app; right; left; reflexivity|].
  unfold req_size. destruct (Z.eqb_spec (n + 16) 0); lia.
- apply Forall_forall. intros r Hr. destruct (OLD r Hr) as (E16 & m & Hm & M16).
  apply in_split in Hm as (x1 & x2 & Ex).
  pose proof (sep_blocks_pos tfibsegs B LAWS ly' S' W' mem' md' (fst r, m) (h, n + 16) x1 x2 [] HAR'
    ltac:(rewrite Eb', Ex, <- app_assoc; reflexivity)) as D.
  unfold zdisjoint, block_rng in *. cbn [fst snd] in *. rewrite E16.
  assert (req_size (n + 16) = n + 16) by (unfold req_size; destruct (Z.eqb_spec (n + 16) 0); lia). lia.
Qed.

(* the new head joins a user-poisoned set it is disjoint from *)
Lemma fsr_upoison_ok_cons : forall ly S U h m,
  upoison_ok B ly S U -> Forall (zdisjoint (h, 16)) U -> In (h, m) (ablocks B ly S) -> h mod 8 = 0 ->
  16 <= 8 * (req_size m / 8) -> upoison_ok B ly S ((h, 16) :: U).
Proof.
intros ly S U h m [F PW] DJ Hin H8 Hm. split; [|split; [exact DJ | exact PW]].
constructor; [|exact F]. cbn [fst snd]. split; [exact H8|]. split; [lia|]. split; [reflexivity|].
exists h, m. split; [exact Hin | lia].
Qed.

(* ARU with the new head moved from the front (the poison contract's form) to the end (the spec's form) *)
Lemma fsr_ARU_append : forall ly S U h (W : world tfibsegs) mem md,
  ARU tfibsegs B ly S ((h, 16) :: U) W mem md -> ARU tfibsegs B ly S (U ++ [(h, 16)]) W mem md.
Proof.
intros ly S U h W mem md H. apply (FSupoisonU.ARU_perm tfibsegs B LAWS ly S ((h, 16) :: U)); [|exact H].
apply Permutation_cons_append.
Qed.

(* YCbq.mbyte_of_aview at two addresses *)
Lemma fsr_mbyte_of_aview2 : forall (H H' : word -> bool) (m m' : word -> option byte) a a',
  aview tfibsegs H' m' a' = aview tfibsegs H m a -> mbyte tfibsegs (mrestrict H' m') a' = mbyte tfibsegs (mrestrict H m) a.
Proof.
intros H H' m m' a a' E. unfold aview in E.
destruct (mbyte tfibsegs (mrestrict H' m') a') as [b'|], (mbyte tfibsegs (mrestrict H m) a) as [b|];
  cbn in E; try discriminate; [|reflexivity].
injection E as E. f_equal. apply bv_eq. exact E.
Qed.

(* bytes kept by a copy: the first m bytes of l at src, read at dst *)
Lemma fsr_zbytes_copy : forall (W W' : world tfibsegs) mem mem' src dst l m,
  zbytes_at tfibsegs W mem src l -> 0 <= m -> (Z.to_nat m <= length l)%nat ->
  (forall i, 0 <= i < m -> aview tfibsegs (w_H W') mem' (dst + i) = aview tfibsegs (w_H W) mem (src + i)) ->
  zbytes_at tfibsegs W' mem' dst (firstn (Z.to_nat m) l).
Proof.
intros W W' mem mem' src dst l m Hz Hm Hl Hc j Hj.
rewrite length_firstn in Hj. rewrite nth_firstn.
destruct (Nat.ltb_spec j (Z.to_nat m)) as [Hjm|Hjm]; [|lia].
destruct (Hz j ltac:(lia)) as [Hv Hb]. split; [|exact Hb].
intros kk Hk. assert (kk = 0%nat) by lia. subst kk.
pose proof (fsr_mbyte_of_aview2 _ _ _ _ _ _ (Hc (Z.of_nat j) ltac:(lia))) as E.
specialize (Hv 0%nat ltac:(lia)). cbn [Z.of_nat] in *. rewrite Z.add_0_r in *. rewrite E. exact Hv.
Qed.

End k.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* fsw_aj_reallocU: the realloc call site, the any-U twin of cgif_rgb lib/YC07.v aj_realloc_atD (non-NULL branch    *)
(* only: the NULL answer is dead, arealloc_granted). From a within-walk journal over `unpoison U mem` and ARU of the  *)
(* machine memory, consume `jal __wrap_realloc`: the composed journal (k + 3), ARU at the result with the same U, the *)
(* block swap, the kept bytes, and the caller's kept frame. Shape of a Theorem Labs lane's fsw_aj_mallocU                 *)
(* (lib/A/FSW_malloc_free.v, a working branch 89a91617162).                                                  *)
(* ---------------------------------------------------------------------------------------------------------------- *)

Section r. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Hypothesis FS_ENV : api_env tfibsegs B.
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.
Let segs_low : forall a, in_img tfibsegs a -> 0 <= a < kLowMemEnd := fs_segs_low.

Lemma fsw_aj_reallocU : FS_AREALLOC_BU tfibsegs B (as_universe B) ->
  forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc U mdc k pa n_old n (o : Z) raw ch,
  ajournal tfibsegs B STK sp0 FP ly S W0 (unpoison U mem) md own lyc Sc W (unpoison U memT) mdc k ->
  ARU tfibsegs B lyc Sc U W memT mdc ->
  In (pa, n_old) (ablocks B lyc Sc) ->
  (forall rg, In rg U -> fst rg + snd rg <= pa \/ pa + req_size n_old <= fst rg) ->
  getr regsT 10 = w64 pa -> getr regsT 11 = w64 n -> 1 <= n < MALLOC_MAX -> blocks_bytes Sc + n <= LIVE_MAX ->
  spZ regsT = sp0 + o -> o mod 16 = 0 -> o + 16 < 0 -> STK_RT_REALLOC - o <= STK ->
  getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
  getr regsT 1 = raw -> YK0s.ret_ok raw ->
  st_nev Sc + 2 < EV_MAX ->
  chain_pre lyc (aview tfibsegs (w_H W) (unpoison U memT)) regsT ch ->
  (forall i, 0 <= i < req_size n_old -> inFP FP (pa + i)) ->
  SRr tfibsegs W (mkCfg (mkst regsT (Z_to_bv 64 FS_AREALLOC_PC_B) memT (seg_rom tfibsegs)) mdc)
  (fun W2 c2 => exists ly2 S2 regs2 mem2 md2 (res : Z),
    c2 = mkCfg (mkst regs2 raw mem2 (seg_rom tfibsegs)) md2 /\
    ARU tfibsegs B ly2 S2 U W2 mem2 md2 /\
    ajournal tfibsegs B STK sp0 FP ly S W0 (unpoison U mem) md own ly2 S2 W2 (unpoison U mem2) md2 (k + 3) /\
    aregs_preserved regsT regs2 /\ getr regs2 10 = w64 res /\ frames S2 = frames Sc /\
    st_nev S2 = st_nev Sc + 3 /\ 4096 <= res /\
    (exists b1 b2, ablocks B lyc Sc = b1 ++ (pa, n_old) :: b2 /\ ablocks B ly2 S2 = (b1 ++ b2) ++ [(res, n)]) /\
    (forall i, 0 <= i < Z.min n_old n -> aview tfibsegs (w_H W2) mem2 (res + i) = aview tfibsegs (w_H W) memT (pa + i)) /\
    acall_kept tfibsegs B lyc Sc W (unpoison U memT) W2 (unpoison U mem2) (sp0 + o - ASTACK) (sp0 + o)
      (fun a => res <= a < res + req_size n \/ pa <= a < pa + req_size n_old)).
Proof.
intros AREALLOC W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc U mdc k pa n_old n o raw ch
  HJ HARU Hin HUout Ha0 Ha1 Hn Hlive Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw Hev Hch HFP.
pose proof HARU as (HARU_AR & HARU_OK & HARU_PO).
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & F1 & F2 & F3 & F4 & Hgone & Hpres & Hstatic & F5 & HQT).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (ASTACK = 16384) as Has by reflexivity.
(* the budget carries realloc's runtime prefix (STK_RT_REALLOC = ASTACK + 0x8a0): it gives the old ASTACK facts and,
   with the journal's `ly_bot ly + STK < sp0 + ASTACK`, arealloc_realizesU's margin `ly_bot lyc + 0x8a0 < spZ regsT` *)
unfold STK_RT_REALLOC in Hbud.
assert (Hmar : ly_bot lyc + 0x8a0 < spZ regsT).
{ pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop0 & _).
  unfold ly_bot in *. rewrite Hsp'. lia. }
destruct (proj1 (in_ablocks B lyc Sc pa n_old) Hin) as (q & Hq & Hqin).
destruct (al_blocks _ _ LAWS lyc Sc W (unpoison U memT) mdc pa n_old HAR Hin) as (Hpa16 & Hpa4096 & _).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
assert (HstkC : astk_ok ASTACK lyc (spZ regsT)).
{ unfold astk_ok, ly_bot in *. rewrite Hsp', Eslo, Eshi, Etop. repeat split; try zlia.
  all: rewrite Z.add_mod, Hal16, Hal by zlia; reflexivity. }
assert (HPRE0 : acall_pre tfibsegs B lyc Sc W regsT (unpoison U memT) mdc ch).
{ destruct HstkC as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9).
  split; [exact HAR|]. split; [exact (aregime_small Sc ltac:(lia))|]. split; [rewrite Hra; exact Hraw|].
  split; [exact Q1|]. split; [zlia|]. split; [zlia|]. split; [zlia|].
  split; [intros a Ha; apply Hpres; rewrite Hsp' in Ha; zlia|].
  split; [exact Hgp|]. split; [exact Htp|]. split; [exact Hch|].
  exact (conj HQT (mroom_of_regime (as_universe B) Sc (am_wf _ _ _ _ (proj1 HAR))
    (aregime_to_mid Sc (aregime_small Sc ltac:(lia))) (qtight_qloose Sc HQT))). }
assert (HPRE : FSupoisonU.acall_preU tfibsegs B lyc Sc U W regsT memT mdc ch)
  by (split; [exact HPRE0 | split; [exact HARU_OK | exact HARU_PO]]).
pose proof (am_wf _ _ _ _ (proj1 HAR)) as HWF.
pose proof (model_laws_ok (as_universe B) (am_universe _ _ _ _ (proj1 HAR))) as ML.
(* the trace premise in C5 form (FSupoisonRealloc @ fda61055856): two events remain, the room premise itself *)
assert (Htr' : In (call_trace lyc FS_AREALLOC_IPC_B regsT ch) (as_universe B) \/ st_nev Sc + 2 < EV_MAX)
  by (right; exact Hev).
pose proof (AREALLOC lyc Sc U W regsT memT mdc q n_old n ch HPRE (or_introl Hev) Hqin
  ltac:(rewrite Hq; exact Ha0) Ha1 Hn Hlive ltac:(rewrite Hq; exact HUout) Htr' Hmar) as HREAL.
eapply SRr_mono.
{ exact (arealloc_granted tfibsegs (as_universe B) Sc q n_old n _ W _ _ ML HWF ltac:(lia) ltac:(lia) Hlive Hqin
    (call_trace_len lyc FS_AREALLOC_IPC_B regsT ch) HREAL). }
intros W2 c2 HwleW (r & Hnn & Hleaf).
destruct (fsr_realloc_leaf B (as_universe B) U lyc Sc W regsT memT mdc q n_old n r W2 c2 FS_ENV HARU HstkC Hqin
  ltac:(rewrite Hq; lia) ltac:(lia) Hnn Hleaf)
  as (ly2 & regs2 & mem2 & md2 & Ec & HP & R10 & HJ1 & HARU2 & (b1 & b2 & Eb1 & Eb2) & CPY & Hnev2 & Hfrs2).
rewrite Hq in *.
set (res := sptr_addr B ly2 (fst r)) in *.
assert (Hnew : In (res, n) (ablocks B ly2 (snd r))) by (rewrite Eb2; apply in_or_app; right; left; reflexivity).
destruct (al_blocks _ _ LAWS ly2 (snd r) W2 (unpoison U mem2) md2 res n (proj1 HARU2) Hnew) as (_ & Hr4096 & _).
assert (HoldS : forall a, inFP (ablocks_fp [(pa, n_old)]) a -> pa <= a < pa + req_size n_old).
{ intros a (rg & [<-|[]] & Ha). cbn [fst snd] in Ha. exact Ha. }
exists ly2, (snd r), regs2, mem2, md2, res.
split; [rewrite Ec; unfold cfg_at, raZ, YG0d.w64; rewrite Hra, Z_to_bv_bv_unsigned; reflexivity|].
split; [exact HARU2|].
split.
{ rewrite Hsp' in HJ1. change own with ([] ++ own).
  eapply (ajournal_sub tfibsegs B LAWS segs_low).
  all: first
    [ solve [exact HJ] | solve [exact HJ1] | solve [zlia]
    | solve [intros a Ha; left; pose proof (HoldS a Ha) as Hr; split;
             [ replace a with (pa + (a - pa)) by lia; apply HFP; lia
             | exists pa, n_old; split; [exact Hin | exact Hr] ]] ]. }
split; [exact HP|]. split; [exact R10|]. split; [exact Hfrs2|]. split; [exact Hnev2|]. split; [exact Hr4096|].
split; [exists b1, b2; split; [exact Eb1 | exact Eb2]|].
split; [exact CPY|].
rewrite Hsp' in HJ1.
(* the core's acall_kept_of_journal premises, in either core version (the FP-keyed core adds `in_img -> ~ inFP FP1`) *)
eapply (acall_kept_of_journal tfibsegs B segs_low).
all: first
  [ solve [exact HJ1] | solve [exact (proj1 HARU)]
  | (intros a Ha; right; exact (HoldS a Ha))
  | (intros b m i Hb Hi HnE; rewrite Eb2; apply in_or_app; left; rewrite Eb1 in Hb;
     apply in_app_or in Hb as [Hb|[Hb|Hb]]; [apply in_or_app; left; exact Hb | | apply in_or_app; right; exact Hb];
     exfalso; injection Hb as <- <-; apply HnE; right; lia)
  | (apply sink_closed_ablocks_fp; constructor; [cbn [fst]; lia | constructor])
  | (intros a Hi Hf; exact (blk_img tfibsegs B LAWS lyc Sc W _ mdc pa n_old a HAR Hin (HoldS a Hf) Hi)) ].
Qed.
End r.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The walk: fuzz_realloc_spec's post, the p = 0 arm (B: the tail call to fuzz_malloc at 0x82c2c).                     *)
(* ---------------------------------------------------------------------------------------------------------------- *)

Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.

(* fuzz_realloc_spec's post (lib/A/FSH_Fn_alloc.v:208-234), text verbatim at segs := tfibsegs *)
Definition fsr_post (regs : bvmap 5 word) ly S U (W : world tfibsegs) mem md (p k n : Z) (old : list Z)
  (live peak cnt fail : Z) : world tfibsegs -> config -> Prop :=
    (fun W' c' =>
       (cnt = fail /\ apost_baseU tfibsegs B STK_fuzz_realloc FS_PSTAT_FP regs ly S W mem md 0 U U
          (fun ly' S' W' regs' mem' md' =>
             getr regs' 10 = w64 0 /\ ablocks B ly' S' = ablocks B ly S /\
             fs_heads B ly' S' U /\
             fs_glob tfibsegs W' mem' live peak (cnt + 1) SIZE_MAXZ) W' c')
       \/
       (cnt <> fail /\ p = 0 /\ exists res,
          apost_baseU tfibsegs B STK_fuzz_realloc FS_PSTAT_FP regs ly S W mem md 1 U (U ++ [(res - HEAD, HEAD)])
          (fun ly' S' W' regs' mem' md' =>
             getr regs' 10 = w64 res /\ 4096 + HEAD <= res /\
             ablocks B ly' S' = ablocks B ly S ++ [(res - HEAD, n + HEAD)] /\
             fs_heads B ly' S' (U ++ [(res - HEAD, HEAD)]) /\
             (0 < n -> fs_rblock tfibsegs B ly' S' W' mem' res n) /\
             fs_glob tfibsegs W' mem' (live + n) (Z.max peak (live + n)) (cnt + 1) fail) W' c')
       \/
       (cnt <> fail /\ p <> 0 /\ exists U1 U2 res, U = U1 ++ (p - HEAD, HEAD) :: U2 /\
          apost_baseU tfibsegs B STK_fuzz_realloc (FS_PSTAT_FP ++ ablocks_fp [(p - HEAD, k + HEAD)]) regs ly S W mem md 3
            U (U1 ++ U2 ++ [(res - HEAD, HEAD)])
          (fun ly' S' W' regs' mem' md' =>
             getr regs' 10 = w64 res /\ 4096 + HEAD <= res /\
             (exists b1 b2 c1 c2, ablocks B ly S = b1 ++ (p - HEAD, k + HEAD) :: b2 /\
                ablocks B ly' S' = c1 ++ (res - HEAD, n + HEAD) :: c2 /\ c1 ++ c2 = b1 ++ b2) /\
             fs_heads B ly' S' (U1 ++ U2 ++ [(res - HEAD, HEAD)]) /\
             (0 < n -> fs_rblock tfibsegs B ly' S' W' mem' res n) /\
             zbytes_at tfibsegs W' mem' res (firstn (Z.to_nat (Z.min k n)) old) /\
             fs_glob tfibsegs W' mem' (live - k + n) (Z.max peak (live - k + n)) (cnt + 1) fail) W' c')).

(* a TAIL call to a program function at the caller's own sp: the caller's journal up to the jump (FP = FS_PSTAT_FP)
   and the callee's fpostU (its journal at the same sp, window STKc <= STK, FP = FS_PSTAT_FP) give the caller's
   fpostU. The callee's footprint is the statics, image bytes in the caller's FP: the third arm of RELOC's
   ajournal_sub (FSW_K3.fsw_ajournal_sub3). *)
Lemma fsr_tail_post : forall STK STKc ly S U (W : world tfibsegs) regs mem md regs1 mem1 md1 k U'
  (Q Q' : alayout -> astate -> world tfibsegs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop) W' c',
  ajournal tfibsegs B STK (spZ regs) FS_PSTAT_FP ly S W (unpoison U mem) md [] ly S W (unpoison U mem1) md1 0 ->
  0 <= STKc <= STK -> spZ regs1 = spZ regs -> YK11.getr regs1 1 = YK11.getr regs 1 -> aregs_preserved regs regs1 ->
  (forall ly' S' W2 regs' mem' md', Q ly' S' W2 regs' mem' md' -> Q' ly' S' W2 regs' mem' md') ->
  fpostU tfibsegs B STKc (spZ regs1) FS_PSTAT_FP regs1 ly S U W mem1 md1 k U' Q W' c' ->
  fpostU tfibsegs B STK (spZ regs) FS_PSTAT_FP regs ly S U W mem md k U' Q' W' c'.
Proof.
intros STK STKc ly S U W regs mem md regs1 mem1 md1 k U' Q Q' W' c' HJ HSTK Hsp Hra HP HQQ
  (ly' & S' & regs' & mem' & md' & Ec & HJc & OK & PO & HP' & HQ).
exists ly', S', regs', mem', md'.
split; [rewrite Ec, Hra; reflexivity|].
split.
{ exact (fsw_ajournal_sub3 B STK (spZ regs) FS_PSTAT_FP ly S W (unpoison U mem) md [] ly S W (unpoison U mem1) md1 0
    STKc (spZ regs1) FS_PSTAT_FP [] ly' S' W' (unpoison U' mem') md' k HJ HJc ltac:(lia) ltac:(lia)
    (fun a Ha => or_intror (or_intror (conj Ha (fs_pstat_img a Ha))))). }
split; [exact OK|]. split; [exact PO|]. split; [|exact (HQQ _ _ _ _ _ _ HQ)].
intros r Hr. rewrite (HP' r Hr). exact (HP r Hr).
Qed.

(* p = 0 (alloc.c:77): the prologue, `beqz a0` taken, the epilogue and `j fuzz_malloc` with a0 = n; fuzz_malloc's two
   arms are arms (a) and (b) of the post. The path reads no static and no shadow base, so the entry is the plain
   FSW_K.fsw_entry (the frame only); the journal is opened at FS_PSTAT_FP, the footprint the post names. *)
Lemma fsr_p0 : @fuzz_malloc_spec fx rc SK tfibsegs B ->
  forall ly S U (W : world tfibsegs) regs mem md ch n live peak cnt fail,
  fpreU tfibsegs B STK_fuzz_realloc ly S U W regs mem md ch -> fs_heads B ly S U ->
  YK11.getr regs 10 = w64 0 -> YK11.getr regs 11 = w64 n -> 1 <= n -> n + HEAD < MALLOC_MAX ->
  fs_glob tfibsegs W mem live peak cnt fail -> (cnt <> fail -> live + n < 2 ^ 64) -> cnt + 1 < 2 ^ 64 ->
  st_nev S + EV_fuzz_malloc <= EV_MAX -> (cnt <> fail -> blocks_bytes S + (n + HEAD) <= LIVE_MAX) ->
  SRr tfibsegs W (cfg_at tfibsegs A_fuzz_realloc regs mem md) (fsr_post regs ly S U W mem md 0 0 n [] live peak cnt fail).
Proof.
intros MALLOC ly S U W regs mem md ch n live peak cnt fail HPRE FH H10 H11 Hn1 Hn2 HGL Hlv Hcn Hev Hbb.
pose proof HPRE as (HAP & HRO).
pose proof (fsw_ARU B STK_fuzz_realloc ly S U W regs mem md ch HAP) as HARU.
pose proof HAP as (HAN & _ & _).
pose proof HAN as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof (fsw_sp B STK_fuzz_realloc ly S U W regs mem md ch HAP) as (Hal16 & Hceil & H47 & HS0).
pose proof asan_consts as (C1 & _ & C3 & _).
assert (FR : STK_fuzz_realloc = ltac:(let v := eval vm_compute in STK_fuzz_realloc in exact v)) by reflexivity.
assert (FM : STK_fuzz_malloc = ltac:(let v := eval vm_compute in STK_fuzz_malloc in exact v)) by reflexivity.
pose proof (fsw_entry B STK_fuzz_realloc 32 ly S U W regs mem md ch A_fuzz_realloc HAP
  ltac:(rewrite FR; lia) ltac:(vm_compute; reflexivity)) as HS.
pose proof (ajournal_init tfibsegs B STK_fuzz_realloc FS_PSTAT_FP ly S W regs (unpoison U mem) md ch HAN) as HJ.
set (E := Ereg regs []) in HS.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (subst E; rewrite (ew_Ereg_nat regs [] 2 2%bv eq_refl); reflexivity).
assert (E10 : ew E 10 = Z_to_bv 64 0) by (subst E; rewrite (ew_Ereg_nat regs [] 10 10%bv eq_refl); exact H10).
unfold cfg_at. change (w64 A_fuzz_realloc) with (Z_to_bv 64 A_fuzz_realloc).
(* 0x82bc4..0x82bd8: frame, save ra / s0 / s1 / s2, s0 = n; stops at beqz a0 0x82bdc *)
fsw_aj_runU fsr_tbl_ok HS HJ HARU.
{ awr_ok_tac. exact Usp. }
assert (SB1 : same_below mem (ms_mem ms) alloc_ceiling).
{ change (frame_of E [fstk 32] mem (ms_mem ms)) in HF.
  apply (same_below_frame1 E (fstk 32) mem (ms_mem ms) alloc_ceiling HF).
  all: first [solve [lia] | solve [cbn [fstk YP09.r_base YP09.r_wlo base_val]; rewrite Usp; lia]]. }
clear HF HFr HG.
(* 0x82bdc beqz a0: taken, since a0 = p = 0 *)
eapply SRr_sym_branch with (c := BC_EQ) (a := SOff 10 0) (b := SLit 0); [exact HS | intros Hb HS2 | intros Hb _].
2:{ exfalso. rewrite branch_eq_U, (U_atom E 10 0 E10 ltac:(lia)), U_lit in Hb by lia. discriminate Hb. }
clear HS.
(* 0x82c14..0x82c2c: a0 = n, restore ra / s0 / s1 / s2, sp; `j fuzz_malloc` stops at the fetch of 0x82a58 *)
fsw_aj_runU fsr_tbl_ok HS2 HJ HARU.
{ awr_ok_tac. exact Usp. }
assert (SB2 : same_below (ms_mem ms) (ms_mem ms0) alloc_ceiling).
{ cbn [add_cond ss_mem] in HF.
  eapply (same_below_frame1 E _ (ms_mem ms) (ms_mem ms0) alloc_ceiling HF).
  all: first [solve [lia] | solve [cbn [YP09.r_base YP09.r_wlo base_val]; rewrite Usp; lia]]. }
clear HF HFr HG.
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) E _ ms0 HS2 eq_refl) as Hshape.
pose proof (fsw_reg_atom (w_H W) regs [] _ ms0 1%bv 1%bv 1 HS2 ltac:(vm_compute; reflexivity) eq_refl) as R1.
pose proof (fsw_reg_atom (w_H W) regs [] _ ms0 2%bv 2%bv 2 HS2 ltac:(vm_compute; reflexivity) eq_refl) as R2.
pose proof (fsw_reg_atom (w_H W) regs [] _ ms0 3%bv 3%bv 3 HS2 ltac:(vm_compute; reflexivity) eq_refl) as R3.
pose proof (fsw_reg_atom (w_H W) regs [] _ ms0 4%bv 4%bv 4 HS2 ltac:(vm_compute; reflexivity) eq_refl) as R4.
pose proof (fsw_reg_atom (w_H W) regs [] _ ms0 8%bv 8%bv 8 HS2 ltac:(vm_compute; reflexivity) eq_refl) as R8.
pose proof (fsw_reg_atom (w_H W) regs [] _ ms0 10%bv 11%bv 11 HS2 ltac:(vm_compute; reflexivity) eq_refl) as R10.
assert (HP : aregs_preserved regs (ms_regs ms0)).
{ eapply (aregs_preserved_of_st_ok tfibsegs _ E _ _ regs [] HS2).
  all: first [ solve [apply env_agree_refl]
             | solve [lazymatch goal with |- forallb _ _ = true => vm_compute; reflexivity end] ]. }
set (regs1 := ms_regs ms0) in *. set (mem1 := ms_mem ms0) in *.
set (md1 := with_vm_backing (m_vm_lazy (with_vm_backing (m_vm_lazy md) mat md)) mat0
  (with_vm_backing (m_vm_lazy md) mat md)) in *.
assert (Rsp : spZ regs1 = spZ regs) by (unfold spZ; rewrite R2; reflexivity).
assert (Rs0 : s0Z regs1 = s0Z regs) by (unfold s0Z; rewrite R8; reflexivity).
assert (SB : same_below mem mem1 alloc_ceiling) by exact (same_below_trans _ _ _ _ SB1 SB2).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _).
pose proof Hstk as (_ & _ & _ & _ & Hshi & H47' & _ & Htop & Htop2).
(* fuzz_malloc's fpreU at the jump: the same layout, chain and window top *)
assert (HPRE1 : fpreU tfibsegs B STK_fuzz_malloc ly S U W regs1 mem1 md1 ch).
{ pose proof HARU as (_ & OK & PO).
  split; [|exact (arodata_below B W mem mem1 SB HRO)].
  split; [|split; [exact OK | exact PO]].
  apply (afn_pre_at tfibsegs B STK_fuzz_realloc (spZ regs) FS_PSTAT_FP ly S W (unpoison U mem) md [] ly S W
    (unpoison U mem1) md1 0 regs1 STK_fuzz_malloc 0 ch HJ).
  all: first
    [ solve [lia]
    | solve [reflexivity]
    | solve [lazymatch goal with |- YK0s.ret_ok _ => rewrite R1; exact Hra end]
    | solve [lazymatch goal with |- 4096 <= raZ _ => unfold raZ; rewrite R1; exact Hra4 end]
    | solve [lazymatch goal with |- getr _ 3 = _ => rewrite R3; exact Hgp end]
    | solve [lazymatch goal with |- getr _ 4 = _ => rewrite R4; exact Htp end]
    | solve [rewrite Rsp, Rs0;
             apply (achain_kept ly (aview tfibsegs (w_H W) (unpoison U mem)) _ (spZ regs) (s0Z regs) ch (spZ regs) Hch);
             first [solve [lia] | solve [intros a Ha; apply F1; lia]]] ]. }
assert (HGL1 : fs_glob tfibsegs W mem1 live peak cnt fail) by exact (fs_glob_below W mem mem1 live peak cnt fail SB HGL).
rewrite Hshape. change (Z_to_bv 64 (ss_pc _)) with (w64 A_fuzz_malloc). fold (cfg_at tfibsegs A_fuzz_malloc regs1 mem1 md1).
eapply SRr_mono.
{ apply (MALLOC ly S U W regs1 mem1 md1 ch n live peak cnt fail HPRE1 FH).
  all: first
    [ solve [rewrite R10; exact H11]
    | solve [exact Hn1] | solve [exact Hn2] | solve [exact HGL1] | solve [exact Hlv] | solve [exact Hcn]
    | solve [exact Hbb]
    | solve [unfold EV_fuzz_malloc in *; lia] ]. }
intros W2 c2 _ Hpost. unfold fsr_post.
destruct Hpost as [(Hcf & HA) | (Hcf & res & HA)].
- left. split; [exact Hcf|].
  exact (fsr_tail_post STK_fuzz_realloc STK_fuzz_malloc ly S U W regs mem md regs1 mem1 md1 0 U _ _ W2 c2 HJ
    ltac:(lia) Rsp R1 HP (fun _ _ _ _ _ _ H => H) HA).
- right. left. split; [exact Hcf|]. split; [reflexivity|]. exists res.
  exact (fsr_tail_post STK_fuzz_realloc STK_fuzz_malloc ly S U W regs mem md regs1 mem1 md1 1 _ _ _ W2 c2 HJ
    ltac:(lia) Rsp R1 HP
    (fun _ _ _ _ _ _ H => match H with conj Q1 (conj Q2 (conj Q3 (conj Q4 (conj Q5 (conj _ Q7))))) =>
       conj Q1 (conj Q2 (conj Q3 (conj Q4 (conj Q5 Q7)))) end) HA).
Qed.
End w.
