(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* omx-clap-core/fuzz_preset (both images; generic over the listing and the PAImg, as lib/A/Ent102CutsA.v is): THE
   CONSUMER'S _of_post BRIDGE for check_no_overread (the kit owner's ruling 01:50Z, measure-then-decide; harness fix #102). It
   derives the walk's ENTRY-KEYED callee text from the batch kit's POST-FORM text PRH_FnCheck.tcheck_no_overread_specX
   (lib/A/PRH_FnCheck.v:738 at the batch kit's cdde0ed15730), so the interface's pcc_* callee contract is discharged at
   the seam. Both texts are cited by qualified name; no body of the batch kit's is restated.
   WHAT DOES NOT CLOSE, AND WHY (measured): Ent102CutsA.l1_tcno_exactX (Ent102CutsA.v:145-190 at eee068f42333) is
   STRONGER than the kit's text in two places, both from the kit's WILD BUDGET (465fa40e163, after PRH_OfPost.v's Qed at
   8ba304fe2f93):
   (W1) the batch kit's text takes `YCbqGwild.wild_room (as_universe B) [] (prh_wk F_check_no_overread) (st_depot S)` at entry
        (PRH_FnCheck.v:770); l1_tcno_exactX has no such premise, and none of its premises gives it.
   (W2) the batch kit's post is `fpostFbm B ARx SK (YCbqGwild.wbudget [] (prh_wk F_check_no_overread)) ..` (:786): the journal
        may store up to prh_wk F_check_no_overread = 6 new wild traces (parse_noting's subtree stores some, e.g. B'
        parse_items' free). l1_tcno_exactX states `fpostFm`, the EMPTY budget (no new wild trace), which the budgeted
        post does not give (YCbqGwild.apost_base_xbF_of_x is the other direction only).
   Both facts are OURS to adopt (the consumer's text), not the kit's: l1_tcno_exactX_wb below is l1_tcno_exactX with
   exactly (W1) inserted after `ck_frm0 ->` and (W2) in place of `fpostFm B ARx SK`. It is a WEAKENING of the cut
   file's text (l1_tcno_exactX_wb_of_cuts), and the batch kit's text implies it with NO added premise
   (l1_tcno_exactX_wb_of_post). The walk of LLVMFuzzerTestOneInput then discharges (W1) at the call and threads the
   budget (YCbqGwild's call rules).
   R1 (`rp_i = length (PresetRun.hruns rp_sm rp_x rp_os)`, GrantA's tcheck_no_overread_grantedX) is NOT needed for
   l1_tcno_exactX_wb: under `rp_x = x` the run premise at any triple puts the entry index inside hruns rp_os by length
   (ofc_run_inside), which is all the position lift needs.
   R1 SUPPLIES WHAT THE GRANTED FORM NEEDS (GrantA's tcheck_no_overread_grantedX, blob 478c607a4fe1, with W1 / W2:
   tcheck_no_overread_grantedXb_R1 below), whose post states own' = 0. The batch kit's post gives own' = 0 only by its copies
   clause (PRH_FnCheck.v:801-804), whose premise `PRH_Base.prh_cons_from sm x0 os i (length (ck_cno_copies x))`
   asks the hcons flags at rp_i .. rp_i + 2 to be true. At the call boundary, R1, they are call_cons's copy flags,
   true in every arm (PresetRun.v:392-409; ofc_cons_copies). Without R1 the run premise gives only
   rp_i <= length (hruns ..), and below it the flags are the earlier calls' (false on their P1 reading segments): no
   premise of the text gives the window there (no counterexample was built). With R1 kept, Qed with no other
   premise (tcheck_no_overread_grantedXb_R1_of_post).
   THE ROUTE (PRH_OfPost.v's header at 8ba304fe2f93 :14-26): the run hypothesis at os := rp_os ++ [(o1, o2, o0)]
   from the consumer's `forall o1 o2 o0` run premise (PRH_FnCheck.ck_cno_evs_call, PRH_Base.prh_run_at_app_iff), the
   entry position lifted to that os (ofc_room_pos_snoc), the two room counts from the lifted position along the
   all-granted list (PresetRoomCounts.peak_sec_of_room_pos / peak_c24_of_room_pos: PresetLiveSec.live_sec /
   live_c24 at every prefix), and the cut file's l1_cno_evs equal to the batch kit's ck_cno_evs under |x| <= MAXB.
   THE RE-HIDING MOVE AND THE HULL (the primed callee texts of PRH_FnCheck.v): tcheck_no_overread_specX,
   tparse_noting_specX and tcheck_as_written_specX conclude SRr' segs RZ_cf and take the hull budget of their
   all-granted events (tcheck_as_written_specX also the run position at entry, HPOS). Every text bridged here states
   the same SRr' and takes that hull premise word for word as its LAST premise, (W3) / (P5) below; its post keeps its
   shape (parse_noting's new `hull_used` conjunct is not restated: the walk pays every hull from its position, the
   cut file's ech_hull_pay). HPOS is supplied from tcheck_as_written_grantX's position, its run's first event and
   its `(length rp_os <= 4)%nat`.
   rule 24: proves no function (kind: statement corollaries between two callee texts; no program code is walked). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0s YK0o YK15 YK18 YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YI00 YI04 YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YCbqG YG0dcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0b YPsym YC4aP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YCbqGwild YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_FnPj PRH_FnReader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoomPos PresetReqAt PresetRun PresetRoomCounts.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_FnCheck.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Ent102CutsA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetHullBudget.
(* stdpp, through the LPS modules, shadows several list names; the lemmas here are Stdlib's. *)
From Stdlib Require Import List.
Import ListNotations.
Local Open Scope Z_scope.

(* ---- the model side: no section variable ---- *)
(* the cut file's l1_cno_evs is the batch kit's ck_cno_evs below MAXB (the same three arms; l1_cno_evs adds the MAXB guard) *)
Lemma ofc_cno_evs_eq : forall sm x o1 o2 o0, (PresetReqAt.MAXB <? Z.of_nat (length x)) = false ->
  Ent102CutsA.l1_cno_evs sm x o1 o2 o0 = ck_cno_evs sm x o1 o2 o0.
Proof. intros sm x o1 o2 o0 H. unfold Ent102CutsA.l1_cno_evs, ck_cno_evs. cbv zeta. rewrite H. reflexivity. Qed.

(* a call's events below MAXB are not empty: they start with the three copies *)
Lemma ofc_call_evs_len : forall sm x o1 o2 o0, (PresetReqAt.MAXB <? Z.of_nat (length x)) = false ->
  (3 <= length (PresetRun.call_evs sm x o1 o2 o0))%nat.
Proof.
  intros sm x o1 o2 o0 H. rewrite (ck_cno_evs_call sm x o1 o2 o0 H).
  destruct (ck_cno_evs_copies sm x o1 o2 o0) as [rest ->]. unfold ck_cno_copies.
  rewrite !length_app. cbn [length]. lia.
Qed.

(* THE COPIES ARE CONSUMER EVENTS AT THE CALL BOUNDARY: at index length (hruns os) of os ++ [t], the next three
   flags are call_cons's first three, true in every arm *)
Lemma ofc_cons_copies : forall sm x os o1 o2 o0, (PresetReqAt.MAXB <? Z.of_nat (length x)) = false ->
  PRH_Base.prh_cons_from sm x (os ++ [(o1, o2, o0)]) (length (PresetRun.hruns sm x os)) 3.
Proof.
  intros sm x os o1 o2 o0 Hg. unfold PRH_Base.prh_cons_from. intros j e Hj _.
  assert (Hf : nth (length (PresetRun.hruns sm x os) + j) (PresetRun.hcons sm x (os ++ [(o1, o2, o0)])) false = true).
  { assert (E : PresetRun.hcons sm x (os ++ [(o1, o2, o0)]) =
                PresetRun.hcons sm x os ++ PresetRun.call_cons sm x o1 o2 o0).
    { unfold PresetRun.hcons. rewrite map_app, concat_app. cbn [map concat]. rewrite app_nil_r. reflexivity. }
    rewrite E. rewrite app_nth2 by (rewrite PresetRun.hcons_len; lia). rewrite PresetRun.hcons_len.
    replace (length (PresetRun.hruns sm x os) + j - length (PresetRun.hruns sm x os))%nat with j by lia.
    unfold PresetRun.call_cons. cbv zeta. rewrite Hg.
    destruct (PresetRun.ranout sm x o1); [|destruct (PresetRun.ranout sm x o2)];
      unfold PresetRun.flags; cbn [map app];
      (destruct j as [|[|[|j]]]; [reflexivity | reflexivity | reflexivity | lia]). }
  destruct e; first [exact Hf | exact I].
Qed.

(* THE ENTRY INDEX IS INSIDE hruns rp_os (what R1 would give, by length only): a run over the call's own events at
   os ++ [t], with the run's bytes the call's, starts no later than the end of hruns os *)
Lemma ofc_run_inside : forall sm x os o1 o2 o0 i, (0 < length (PresetRun.call_evs sm x o1 o2 o0))%nat ->
  PRH_Base.prh_run_at sm x (os ++ [(o1, o2, o0)]) i (PresetRun.call_evs sm x o1 o2 o0) ->
  (i <= length (PresetRun.hruns sm x os))%nat.
Proof.
  intros sm x os o1 o2 o0 i Hn H. unfold PRH_Base.prh_run_at in H.
  rewrite PresetRoomCounts.hruns_snoc_rc in H.
  apply (f_equal (@length PresetReqAt.hev)) in H.
  rewrite length_firstn, length_skipn, length_app in H.
  set (a := length (PresetRun.hruns sm x os)) in *. set (c := length (PresetRun.call_evs sm x o1 o2 o0)) in *.
  clearbody a c. lia.
Qed.

(* the position at os is the position at os ++ os' while the index is inside hruns os: iface_room_pos reads the run
   only through firstn i *)
Lemma ofc_room_pos_snoc : forall sm x os os' i H0 hist S, (i <= length (PresetRun.hruns sm x os))%nat ->
  PresetRoomPos.iface_room_pos sm x os i H0 hist S -> PresetRoomPos.iface_room_pos sm x (os ++ os') i H0 hist S.
Proof.
  intros sm x os os' i H0 hist S Hi Hp.
  assert (E : firstn i (PresetRun.hruns sm x (os ++ os')) = firstn i (PresetRun.hruns sm x os)).
  { unfold PresetRun.hruns. rewrite map_app, concat_app, firstn_app. fold (PresetRun.hruns sm x os).
    replace (i - length (PresetRun.hruns sm x os))%nat with 0%nat by lia. rewrite firstn_O, app_nil_r.
    reflexivity. }
  unfold PresetRoomPos.iface_room_pos in *. rewrite E. exact Hp.
Qed.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0b YPsym YC4aP YImgTop YC1fP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm YCbqGwild.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YG01cf YG00cf YGcfRoom.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjRoundTrip.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoomPos PresetReqAt PresetRun.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoomCounts.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require ReaderRes Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_FnAlloc PRH_FnPj PRH_FnCheck.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_FnReader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_PjOrder.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Ent102GrantA.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {PI : PrhImg}
  {RL : PrhRoomLive}.
Context {L : ptable asym} {PA : PAImg L}.
Local Notation segs := pa_segs.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
#[local] Notation ck_frm0 := (@PRH_FnCheck.ck_frm0 fx).

(* l1_tcno_exactX_wb: Ent102CutsA.l1_tcno_exactX (Ent102CutsA.v:145-190, eee068f42333) WORD FOR WORD with three
   changes, all the batch kit's (PRH_FnCheck.v:770, :786; the hull :803): (W1) the wild room after `ck_frm0 ->`; (W2) the
   budgeted post `fpostFbm B ARx SK (YCbqGwild.wbudget [] (prh_wk F_check_no_overread))` in place of
   `fpostFm B ARx SK`; (W3) the hull budget after (W1), with the text's SRr' segs RZ_cf in place of SRr. *)
Definition l1_tcno_exactX_wb (CTX0 : list (list Z)) : Prop :=
  forall (rp_sm : list Z -> Z * Z) (rp_x : list Z) (rp_os : list (option nat * option nat * option nat))
    (rp_i : nat) (rp_H0 : list Z) (rp_hist : list YG00.chunk),
  forall ly S Hp W regs mem md ch data (x : list Z) Lam peak cnt ran most,
  rp_sm = ReaderRes.jr_strtod ->
  let size := Z.of_nat (length x) in
  fpre B ARx STK_check_no_overread ly S Hp W regs mem md ch ->
  YAkMemnorm.memnorm segs mem ->
  prh_univ_closure B CTX0 -> prh_ctx CTX0 F_check_no_overread (raZ regs :: spine ch) ->
  getr regs 10 = w64 data -> getr regs 11 = w64 size ->
  size <= 3 * 2 ^ 20 ->
  src_rd W mem data x -> (0 < size -> PRH_FnReader.prhReader_home B ly S Hp Lam data size) ->
  prh_ledger B ly S Hp W mem Lam peak cnt SIZE_MAXZ ran most 0 -> cnt < 2 ^ 62 - 2 ^ 30 ->
  ran = 0 ->
  PRH_FnPj.RQ_pj_parse x <= most ->
  blocks_bytes S + LIVE_check_no_overread x <= LIVE_MAX ->
  size + 16 < cf_malloc_max -> PRH_FnPj.RQ_pj_parse x + cf_head < cf_malloc_max ->
  Z.of_nat (length (frames S)) <= ck_FRAMES_CAP - FR_check_no_overread ->
  room_live_cf S -> PresetRoomPos.iface_room_pos rp_sm rp_x rp_os rp_i rp_H0 rp_hist S ->
  (forall o1 o2 o0, prh_run_at rp_sm rp_x (rp_os ++ [(o1, o2, o0)]) rp_i (PresetRun.call_evs rp_sm x o1 o2 o0)) ->
  rp_x = x ->
  ck_frm0 ->
  (* (W1) K1's wild room (PRH_FnCheck.v:770) *)
  YCbqGwild.wild_room (as_universe B) [] (prh_wk F_check_no_overread) (st_depot S) ->
  (* (W3) the hull budget (PRH_FnCheck.v tcheck_no_overread_specX), and its SRr' *)
  PresetHullBudget.hull_budget S (ck_cno_evs ReaderRes.jr_strtod x None None None) ->
  SRr' segs YGcfRehidePost.RZ_cf W (cfg_at segs (pa_sigma AS_check_no_overread) regs mem md)
    (* (W2) K1's budgeted post (PRH_FnCheck.v:786) *)
    (fpostFbm B ARx SK (YCbqGwild.wbudget [] (prh_wk F_check_no_overread))
      STK_check_no_overread [] regs ly S Hp W mem md (fun ly' S' Hp' W' regs' mem' md' =>
       room_live_cf S' /\
       exists Lam' peak' cnt' ran' own',
       Permutation Lam' Lam /\ Permutation (ablocks B ly' S') (ablocks B ly S) /\
       peak <= peak' /\ cnt <= cnt' <= cnt + 3 * ck_ncalls x /\
       prh_ledger B ly' S' Hp' W' mem' Lam' peak' cnt' SIZE_MAXZ ran' most own' /\
       bytes_at W' mem' data x /\
       exists r, getr regs' 10 = w64 r /\
         ((r = 1 /\ (own' = 1 \/ ran' = 1)) \/ (r = 0 /\ own' = 0 /\ ran' = 0)) /\
         (own' = 0 -> exists o1 o2 o0,
            (exists rp_hist', PresetRoomPos.iface_room_pos rp_sm rp_x (rp_os ++ [(o1, o2, o0)])
               (rp_i + length (Ent102CutsA.l1_cno_evs rp_sm x o1 o2 o0))%nat rp_H0 rp_hist' S') /\
            (r = 1 <-> (PresetRun.ranout rp_sm x o1 || PresetRun.ranout rp_sm x o2 || PresetRun.ranout rp_sm x o0) = true)))).

(* the budgeted m-form post is monotone in its Q *)
Lemma ofc_fpostFbm_mono : forall P STK FP regs ly S Hp W mem md
  (Q Q' : alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
  (forall ly' S' Hp' W' regs' mem' md', Q ly' S' Hp' W' regs' mem' md' -> Q' ly' S' Hp' W' regs' mem' md') ->
  forall W' c', fpostFbm B ARx SK P STK FP regs ly S Hp W mem md Q W' c' ->
  fpostFbm B ARx SK P STK FP regs ly S Hp W mem md Q' W' c'.
Proof.
  intros P STK FP regs ly S Hp W mem md Q Q' HQ W' c'. unfold fpostFbm, fpostFb, YCbqGwild.apost_base_xbF, fQmn.
  intros (fx' & ly' & S' & Hp' & regs' & mem' & md' & k & WS & Hc & Hz & Hkf & HP & HJ & Hpr & H1 & H2).
  exists fx', ly', S', Hp', regs', mem', md', k, WS.
  split; [exact Hc|]. split; [exact Hz|]. split; [exact Hkf|]. split; [exact HP|]. split; [exact HJ|].
  split; [exact Hpr|]. exact (conj (HQ _ _ _ _ _ _ _ H1) H2).
Qed.

(* THE BRIDGE: the batch kit's post-form text gives the consumer's entry-keyed text (budgeted), with no added premise; R1 is not
   used *)
Lemma l1_tcno_exactX_wb_of_post : forall CTX0,
  PRH_FnCheck.tcheck_no_overread_specX B ARx SK CTX0 -> l1_tcno_exactX_wb CTX0.
Proof.
  intros CTX0 HK rp_sm rp_x rp_os rp_i rp_H0 rp_hist ly S Hp W regs mem md ch data x Lam peak cnt ran most Hsm size
    Hpre Hmn Hcl Hctx Hr10 Hr11 Hsz Hsrc Hhome Hled Hcnt Hran Hmost Hlive Hcm1 Hcm2 Hfr Hrl Hpos Hrun Hx Hfrm Hwild
    Hhull.
  subst rp_sm rp_x.
  (* |x| <= MAXB: the call's events are ck_cno_evs ++ the rest *)
  assert (Hg : (PresetReqAt.MAXB <? Z.of_nat (length x)) = false).
  { assert (Hs : Z.of_nat (length x) <= 3 * 2 ^ 20) by exact Hsz.
    assert (Hm : PresetReqAt.MAXB = 3 * 2 ^ 20) by reflexivity.
    apply Z.ltb_ge. rewrite Hm. exact Hs. }
  (* the entry index is inside hruns rp_os, so the entry position is a position of every rp_os ++ [t] *)
  assert (Hin : (rp_i <= length (PresetRun.hruns ReaderRes.jr_strtod x rp_os))%nat).
  { pose proof (ofc_call_evs_len ReaderRes.jr_strtod x None None None Hg) as Hn.
    exact (ofc_run_inside ReaderRes.jr_strtod x rp_os None None None rp_i ltac:(lia) (Hrun None None None)). }
  assert (Hpos' : forall t, PresetRoomPos.iface_room_pos ReaderRes.jr_strtod x (rp_os ++ [t]) rp_i rp_H0 rp_hist S).
  { intros t. exact (ofc_room_pos_snoc ReaderRes.jr_strtod x rp_os [t] rp_i rp_H0 rp_hist S Hin Hpos). }
  (* the run hypothesis of the batch kit's position clause at any triple *)
  assert (Hrt : forall o1 o2 o0, PRH_Base.prh_run_at ReaderRes.jr_strtod x (rp_os ++ [(o1, o2, o0)]) rp_i
                  (ck_cno_evs ReaderRes.jr_strtod x o1 o2 o0)).
  { intros o1 o2 o0. pose proof (Hrun o1 o2 o0) as H.
    rewrite (ck_cno_evs_call ReaderRes.jr_strtod x o1 o2 o0 Hg) in H. exact (proj1 (proj1 (prh_run_at_app_iff _ _ _ _ _ _) H)). }
  (* The batch kit's two room counts along the all-granted list, from the lifted entry position *)
  pose proof (PresetRoomCounts.peak_sec_of_room_pos ReaderRes.jr_strtod x (rp_os ++ [(None, None, None)]) rp_i rp_H0
    rp_hist S (ck_cno_evs ReaderRes.jr_strtod x None None None) (Hpos' (None, None, None)) (Hrt None None None))
    as Hpk1.
  pose proof (PresetRoomCounts.peak_c24_of_room_pos ReaderRes.jr_strtod x (rp_os ++ [(None, None, None)]) rp_i rp_H0
    rp_hist S (ck_cno_evs ReaderRes.jr_strtod x None None None) (Hpos' (None, None, None)) (Hrt None None None))
    as Hpk2.
  unfold SRr'. eapply SRrG_mono;
    [exact (HK ly S Hp W regs mem md ch data x Lam peak cnt ran most Hpre Hmn Hcl Hctx Hr10 Hr11 Hsz Hsrc Hhome
              Hled Hcnt Hran Hmost Hlive Hcm1 Hcm2 Hfr Hrl Hfrm Hwild Hpk1 Hpk2 Hhull)|].
  intros W' c' _ HP. eapply ofc_fpostFbm_mono; [|exact HP].
  intros ly' S' Hp' W'' regs' mem' md'
    (Hrl' & Lam' & peak' & cnt' & ran' & own' & HL & HA & Hpk & Hcn & Hled' & Hby & r & Hr & Htie & _ & Htrip).
  split; [exact Hrl'|]. exists Lam', peak', cnt', ran', own'.
  split; [exact HL|]. split; [exact HA|]. split; [exact Hpk|]. split; [exact Hcn|]. split; [exact Hled'|].
  split; [exact Hby|]. exists r. split; [exact Hr|]. split; [exact Htie|].
  intros Ho. destruct (Htrip Ho) as (o1 & o2 & o0 & Hrv & _ & Hpost). exists o1, o2, o0. split.
  - destruct (Hpost ReaderRes.jr_strtod x (rp_os ++ [(o1, o2, o0)]) rp_i rp_H0 rp_hist (Hpos' (o1, o2, o0))
      (Hrt o1 o2 o0)) as [h Hh].
    exists h. rewrite (ofc_cno_evs_eq ReaderRes.jr_strtod x o1 o2 o0 Hg). exact Hh.
  - rewrite Hrv. unfold ck_cno_ranout.
    destruct (PresetRun.ranout ReaderRes.jr_strtod x o1 || PresetRun.ranout ReaderRes.jr_strtod x o2 ||
              PresetRun.ranout ReaderRes.jr_strtod x o0); split; intros H; first [reflexivity | discriminate].
Qed.


(* tcheck_no_overread_grantedXb_R1: Ent102GrantA.tcheck_no_overread_grantedX (Ent102GrantA.v:186-233, blob
   478c607a4fe1) WORD FOR WORD with the same changes (W1) / (W2) / (W3), R1 KEPT (the measurement: R1 suffices; the
   header says why it is needed) *)
Definition tcheck_no_overread_grantedXb_R1 (CTX0 : list (list Z)) : Prop :=
  forall (rp_sm : list Z -> Z * Z) (rp_x : list Z) (rp_os : list (option nat * option nat * option nat))
    (rp_i : nat) (rp_H0 : list Z) (rp_hist : list YG00.chunk),
  forall ly S Hp W regs mem md ch data (x : list Z) Lam peak cnt ran most,
  rp_sm = ReaderRes.jr_strtod ->
  let size := Z.of_nat (length x) in
  fpre B ARx STK_check_no_overread ly S Hp W regs mem md ch ->
  YAkMemnorm.memnorm segs mem ->
  prh_univ_closure B CTX0 -> prh_ctx CTX0 F_check_no_overread (raZ regs :: spine ch) ->
  getr regs 10 = w64 data -> getr regs 11 = w64 size ->
  size <= 3 * 2 ^ 20 ->
  src_rd W mem data x -> (0 < size -> PRH_FnReader.prhReader_home B ly S Hp Lam data size) ->
  prh_ledger B ly S Hp W mem Lam peak cnt SIZE_MAXZ ran most 0 -> cnt < 2 ^ 62 - 2 ^ 30 ->
  ran = 0 ->
  PRH_FnPj.RQ_pj_parse x <= most ->
  blocks_bytes S + LIVE_check_no_overread x <= LIVE_MAX ->
  size + 16 < cf_malloc_max -> PRH_FnPj.RQ_pj_parse x + cf_head < cf_malloc_max ->
  Z.of_nat (length (frames S)) <= ck_FRAMES_CAP - FR_check_no_overread ->
  room_live_cf S -> PresetRoomPos.iface_room_pos rp_sm rp_x rp_os rp_i rp_H0 rp_hist S ->
  (forall o1 o2 o0, prh_run_at rp_sm rp_x (rp_os ++ [(o1, o2, o0)]) rp_i (PresetRun.call_evs rp_sm x o1 o2 o0)) ->
  rp_x = x ->
  rp_i = length (PresetRun.hruns rp_sm rp_x rp_os) ->
  ck_frm0 ->
  (* (W1) K1's wild room (PRH_FnCheck.v:770) *)
  YCbqGwild.wild_room (as_universe B) [] (prh_wk F_check_no_overread) (st_depot S) ->
  (* THE HULL BUDGET of the call's all-granted events (tcheck_no_overread_specX's, word for word) *)
  PresetHullBudget.hull_budget S (ck_cno_evs ReaderRes.jr_strtod x None None None) ->
  SRr' segs YGcfRehidePost.RZ_cf W (cfg_at segs (pa_sigma AS_check_no_overread) regs mem md)
    (* (W2) K1's budgeted post (PRH_FnCheck.v:786) *)
    (fpostFbm B ARx SK (YCbqGwild.wbudget [] (prh_wk F_check_no_overread))
      STK_check_no_overread [] regs ly S Hp W mem md (fun ly' S' Hp' W' regs' mem' md' =>
       room_live_cf S' /\
       exists Lam' peak' cnt' ran' own',
       Permutation Lam' Lam /\ Permutation (ablocks B ly' S') (ablocks B ly S) /\
       peak <= peak' /\ cnt <= cnt' <= cnt + 3 * ck_ncalls x /\
       prh_ledger B ly' S' Hp' W' mem' Lam' peak' cnt' SIZE_MAXZ ran' most own' /\
       bytes_at W' mem' data x /\
       exists r, getr regs' 10 = w64 r /\
         own' = 0 /\ ((r = 1 /\ ran' = 1) \/ (r = 0 /\ ran' = 0)) /\
         (own' = 0 -> exists o1 o2 o0,
            (exists rp_hist', PresetRoomPos.iface_room_pos rp_sm rp_x (rp_os ++ [(o1, o2, o0)])
               (rp_i + length (Ent102CutsA.l1_cno_evs rp_sm x o1 o2 o0))%nat rp_H0 rp_hist' S') /\
            (r = 1 <-> (PresetRun.ranout rp_sm x o1 || PresetRun.ranout rp_sm x o2 || PresetRun.ranout rp_sm x o0) = true)))).

Lemma tcheck_no_overread_grantedXb_R1_of_post : forall CTX0,
  PRH_FnCheck.tcheck_no_overread_specX B ARx SK CTX0 -> tcheck_no_overread_grantedXb_R1 CTX0.
Proof.
  intros CTX0 HK rp_sm rp_x rp_os rp_i rp_H0 rp_hist ly S Hp W regs mem md ch data x Lam peak cnt ran most Hsm size
    Hpre Hmn Hcl Hctx Hr10 Hr11 Hsz Hsrc Hhome Hled Hcnt Hran Hmost Hlive Hcm1 Hcm2 Hfr Hrl Hpos Hrun Hx HR1 Hfrm
    Hwild Hhull.
  subst rp_sm rp_x.
  assert (Hg : (PresetReqAt.MAXB <? Z.of_nat (length x)) = false).
  { assert (Hs : Z.of_nat (length x) <= 3 * 2 ^ 20) by exact Hsz.
    assert (Hm : PresetReqAt.MAXB = 3 * 2 ^ 20) by reflexivity.
    apply Z.ltb_ge. rewrite Hm. exact Hs. }
  assert (Hin : (rp_i <= length (PresetRun.hruns ReaderRes.jr_strtod x rp_os))%nat) by (rewrite HR1; lia).
  assert (Hpos' : forall t, PresetRoomPos.iface_room_pos ReaderRes.jr_strtod x (rp_os ++ [t]) rp_i rp_H0 rp_hist S).
  { intros t. exact (ofc_room_pos_snoc ReaderRes.jr_strtod x rp_os [t] rp_i rp_H0 rp_hist S Hin Hpos). }
  assert (Hrt : forall o1 o2 o0, PRH_Base.prh_run_at ReaderRes.jr_strtod x (rp_os ++ [(o1, o2, o0)]) rp_i
                  (ck_cno_evs ReaderRes.jr_strtod x o1 o2 o0)).
  { intros o1 o2 o0. pose proof (Hrun o1 o2 o0) as H.
    rewrite (ck_cno_evs_call ReaderRes.jr_strtod x o1 o2 o0 Hg) in H. exact (proj1 (proj1 (prh_run_at_app_iff _ _ _ _ _ _) H)). }
  pose proof (PresetRoomCounts.peak_sec_of_room_pos ReaderRes.jr_strtod x (rp_os ++ [(None, None, None)]) rp_i rp_H0
    rp_hist S (ck_cno_evs ReaderRes.jr_strtod x None None None) (Hpos' (None, None, None)) (Hrt None None None))
    as Hpk1.
  pose proof (PresetRoomCounts.peak_c24_of_room_pos ReaderRes.jr_strtod x (rp_os ++ [(None, None, None)]) rp_i rp_H0
    rp_hist S (ck_cno_evs ReaderRes.jr_strtod x None None None) (Hpos' (None, None, None)) (Hrt None None None))
    as Hpk2.
  (* the copies clause's run and consumer window, at the call boundary R1 *)
  assert (Hcp : PRH_Base.prh_run_at ReaderRes.jr_strtod x (rp_os ++ [(None, None, None)]) rp_i (ck_cno_copies x)).
  { destruct (ck_cno_evs_copies ReaderRes.jr_strtod x None None None) as [rest Er].
    pose proof (Hrt None None None) as H. rewrite Er in H. exact (proj1 (proj1 (prh_run_at_app_iff _ _ _ _ _ _) H)). }
  assert (Hcf : PRH_Base.prh_cons_from ReaderRes.jr_strtod x (rp_os ++ [(None, None, None)]) rp_i
                  (length (ck_cno_copies x))).
  { rewrite HR1. exact (ofc_cons_copies ReaderRes.jr_strtod x rp_os None None None Hg). }
  unfold SRr'. eapply SRrG_mono;
    [exact (HK ly S Hp W regs mem md ch data x Lam peak cnt ran most Hpre Hmn Hcl Hctx Hr10 Hr11 Hsz Hsrc Hhome
              Hled Hcnt Hran Hmost Hlive Hcm1 Hcm2 Hfr Hrl Hfrm Hwild Hpk1 Hpk2 Hhull)|].
  intros W' c' _ HP. eapply ofc_fpostFbm_mono; [|exact HP].
  intros ly' S' Hp' W'' regs' mem' md'
    (Hrl' & Lam' & peak' & cnt' & ran' & own' & HL & HA & Hpk & Hcn & Hled' & Hby & r & Hr & Htie & Hcopy & Htrip).
  pose proof (Hcopy ReaderRes.jr_strtod x (rp_os ++ [(None, None, None)]) rp_i rp_H0 rp_hist (Hpos' (None, None, None))
    Hcp Hcf) as Ho.
  split; [exact Hrl'|]. exists Lam', peak', cnt', ran', own'.
  split; [exact HL|]. split; [exact HA|]. split; [exact Hpk|]. split; [exact Hcn|]. split; [exact Hled'|].
  split; [exact Hby|]. exists r. split; [exact Hr|]. split; [exact Ho|].
  split.
  { destruct Htie as [(Hr1 & [Ho1 | Hra]) | (Hr0 & _ & Hra)];
      [lia | left; split; assumption | right; split; assumption]. }
  intros _. destruct (Htrip Ho) as (o1 & o2 & o0 & Hrv & _ & Hpost). exists o1, o2, o0. split.
  - destruct (Hpost ReaderRes.jr_strtod x (rp_os ++ [(o1, o2, o0)]) rp_i rp_H0 rp_hist (Hpos' (o1, o2, o0))
      (Hrt o1 o2 o0)) as [h Hh].
    exists h. rewrite (ofc_cno_evs_eq ReaderRes.jr_strtod x o1 o2 o0 Hg). exact Hh.
  - rewrite Hrv. unfold ck_cno_ranout.
    destruct (PresetRun.ranout ReaderRes.jr_strtod x o1 || PresetRun.ranout ReaderRes.jr_strtod x o2 ||
              PresetRun.ranout ReaderRes.jr_strtod x o0); split; intros H; first [reflexivity | discriminate].
Qed.

#[local] Notation rdW W mem := (mrestrict (w_H W) mem).

(* Ent102CutsA.tparse_noting_exactX (CutsA:192-261) with EXACTLY three edits, each marked EDIT: (P3) the wild room,
   (C0) the post at K's budget, (P5) K's hull budget as the last premise with K's SRr'. Every other line is CutsA's,
   byte for byte. *)
Definition tparse_noting_exactXb (CTX0 : list (list Z)) : Prop :=
  forall (rp_sm : list Z -> Z * Z) (rp_x : list Z) (rp_os : list (option nat * option nat * option nat))
    (rp_i : nat) (rp_H0 : list Z) (rp_hist : list YG00.chunk) most own,
  forall ly S Hp W regs mem md ch text (tb : list Z) doc Lam peak cnt fail ran,
  let len := Z.of_nat (length tb) in
  rp_sm = ReaderRes.jr_strtod ->
  fpre B ARx STK_parse_noting ly S Hp W regs mem md ch ->
  YAkMemnorm.memnorm segs mem ->
  prh_univ_closure B CTX0 ->
  getr regs 10 = w64 text -> getr regs 11 = w64 len -> getr regs 12 = w64 doc ->
  len < 2 ^ 40 -> 0 < text -> text + len < 2 ^ 62 ->
  src_rd W mem text tb -> PRH_FnReader.prhReader_home B ly S Hp Lam text len ->
  Z.of_nat (PjRoundTrip.maxrun tb) < 2 ^ 30 ->
  doc mod 8 = 0 -> ck_out_ok B STK_parse_noting ly S W regs mem doc 56 ->
  ran = 0 ->
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own -> cnt + 2 * len + 2 < 2 ^ 64 - 1 ->
  blocks_bytes S + PRH_FnPj.LIVE_pj_parse tb <= LIVE_MAX -> PRH_FnPj.RQ_pj_parse tb + cf_head < cf_malloc_max ->
  PRH_FnPj.RQ_pj_parse tb <= most ->
  Z.of_nat (length (frames S)) <= ck_FRAMES_CAP - FR_parse_noting -> ck_frm0 ->
  room_live_cf S -> PresetRoomPos.iface_room_pos rp_sm rp_x rp_os rp_i rp_H0 rp_hist S ->
  PRH_Base.prh_run_at rp_sm rp_x rp_os rp_i (PresetReqAt.parse_evs rp_sm tb []) ->
  PRH_Base.prh_cons_from rp_sm rp_x rp_os rp_i (length (PresetReqAt.parse_evs rp_sm tb [])) ->
  (fail < cnt \/ cnt + ck_ncalls tb <= fail) ->
  (* EDIT (P3): K's wild room (PRH_FnCheck.v:637), word for word *)
  YCbqGwild.wild_room (as_universe B) [] (prh_wk F_parse_noting) (st_depot S) ->
  (* EDIT (P5): K's hull budget (PRH_FnCheck.v tparse_noting_specX), word for word, and K's SRr' *)
  PresetHullBudget.hull_budget S (PresetReqAt.parse_evs ReaderRes.jr_strtod tb []) ->
  SRr' segs YGcfRehidePost.RZ_cf W (cfg_at segs (pa_sigma AS_parse_noting) regs mem md)
    (* EDIT (C0): K's budgeted post (PRH_FnCheck.v:648) in place of fpostFm *)
    (fpostFbm B ARx SK (YCbqGwild.wbudget [] (prh_wk F_parse_noting))
      STK_parse_noting [(doc, doc + 56)] regs ly S Hp W mem md
      (fun ly' S' Hp' W' regs' mem' md' =>
       room_live_cf S' /\
       exists Lam' peak' cnt' fail' ran' ok res tr,
       (PRH_FnReader.prhReader_agree ok [] (PjGrammar.calls tr) ->
          exists rp_hist', PresetRoomPos.iface_room_pos rp_sm rp_x rp_os
            (rp_i + length (PresetReqAt.parse_evs rp_sm tb [])) rp_H0 rp_hist' S') /\
       PjGrammar.jr_run ReaderRes.jr_strtod tb ok = (res, tr) /\
       prh_oks ok cnt fail (PjGrammar.calls tr) (prh_ev_reqs tr) most 0 ran' /\
       cnt' = cnt + Z.of_nat (PjGrammar.calls tr) /\ ReaderRes.fail_after cnt fail (PjGrammar.calls tr) fail' /\
       peak' = Z.max (Z.max peak (Ledger.lsum Lam + ReaderRes.hpeak tr))
         (prh_refused_peak ok cnt fail (PjGrammar.calls tr)
            (map (Z.add (Ledger.lsum Lam)) (prh_ev_helds (PRH_FnPj.prhPj_ptrace tb)))) /\
       ReaderRes.hpeak tr <= 224 * len + 16384 /\
       (cnt <= fail < cnt + ck_ncalls tb -> res = None) /\
       (ran' <> 0 -> res = None) /\
       (ran' = 0 -> fail < cnt \/ cnt + ck_ncalls tb <= fail ->
          res = ck_read tb /\ Z.of_nat (PjGrammar.calls tr) = ck_ncalls tb) /\
       bytes_at W' mem' text tb /\
       prh_ledger B ly' S' Hp' W' mem' Lam' peak' cnt' fail' ran' most own /\
       match res with
       | Some t =>
           getr regs' 10 = w64 0 /\
           exists D, Permutation Lam' (D ++ Lam) /\
             Permutation (map snd D) (map Z.of_nat (ReaderRes.lsz tr)) /\ Z.of_nat (length D) = ReaderRes.nlive tr /\
             (cf_head = PresetReqAt.HEAD -> Permutation (map (fun b => snd b + cf_head) D)
                (PresetReqAt.rd_blocks (PresetReqAt.rtr ReaderRes.jr_strtod ok tb))) /\
             (cf_head = PresetReqAt.HEAD -> forall n, (PjTree.depth t <= n)%nat ->
                exists F, PRH_PjOrder.pj_foR segs (rdW W' mem') (prh_lin Lam') n doc D F /\
                  map (fun b => snd b + cf_head) F = PresetReqAt.pj_frees ReaderRes.jr_strtod ok tb) /\
             (forall a k, In (a, k) D -> ~ In (a - cf_head, k + cf_head) (ablocks B ly S)) /\
             Permutation (ablocks B ly' S') (ablocks B ly S ++ ck_hblks D) /\
             pj_nodeR segs (rdW W' mem') (prh_lin Lam') doc t D
       | None =>
           getr regs' 10 = w64 (-1) /\ Permutation Lam' Lam /\ Permutation (ablocks B ly' S') (ablocks B ly S) /\
           pj_zeroR segs (rdW W' mem') doc
       end)).

(* the budgeted float post is monotone in its Q (ofp_fpostm_mono's twin, PRH_OfPost.v :99-109 at 8ba304fe2f93) *)
Lemma ofpp_fpostFbm_mono : forall P STK FP regs ly S Hp W mem md
  (Q Q' : alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
  (forall ly' S' Hp' W' regs' mem' md', Q ly' S' Hp' W' regs' mem' md' -> Q' ly' S' Hp' W' regs' mem' md') ->
  forall W' c', fpostFbm B ARx SK P STK FP regs ly S Hp W mem md Q W' c' ->
  fpostFbm B ARx SK P STK FP regs ly S Hp W mem md Q' W' c'.
Proof.
  intros P STK FP regs ly S Hp W mem md Q Q' HQ W' c'.
  unfold fpostFbm, fpostFb, YCbqGwild.apost_base_xbF, fQmn.
  intros (fx' & ly' & S' & Hp' & regs' & mem' & md' & k & WS & Hc & Hz & Hkf & HPw & HJ & Hpr & H1 & H2).
  exists fx', ly', S', Hp', regs', mem', md', k, WS.
  split; [exact Hc|]. split; [exact Hz|]. split; [exact Hkf|]. split; [exact HPw|]. split; [exact HJ|].
  split; [exact Hpr|]. exact (conj (HQ _ _ _ _ _ _ _ H1) H2).
Qed.

(* THE GRANTED TWIN (LlvmWalk's 02:0xZ measurement order): lib/A/Prog/Ent102GrantA.v tparse_noting_grantedX
   (GrantA:59-128 at eddc5db39b43, blob 478c607a4fe1) is E with `ran' = 0` in place of `(ran' <> 0 -> res = None)`
   (GrantA:104), every other line E's. The fact that gives ran' = 0 from K under E's premises is K's OWN outcome
   clause (FnCheck:672-681), whose FIRST conjunct is `ran' = 0` (:678) under exactly the four hypotheses E already
   takes: the entry position (CutsA:211), the run at the all-granted events (:213), the consumer window prh_cons_from
   over them (:216) and the pick condition (:217). prh_oks (:682) alone does allow ran' = 1 (a refused request
   <= most sets the flag), but K does not leave ran' to prh_oks: under the window the outcome clause fixes it. So no
   further premise, no ec_noref fact and no kit fact is needed: DERIVED, owner none. The twin carries the same two
   edits (P3) / (C0) as exactXb; tparse_noting_grantedXb_of_post is Qed with no hypothesis, and exactXb follows from
   grantedXb (ran' = 0 makes the refusal implication vacuous). *)
Definition tparse_noting_grantedXb (CTX0 : list (list Z)) : Prop :=
  forall (rp_sm : list Z -> Z * Z) (rp_x : list Z) (rp_os : list (option nat * option nat * option nat))
    (rp_i : nat) (rp_H0 : list Z) (rp_hist : list YG00.chunk) most own,
  forall ly S Hp W regs mem md ch text (tb : list Z) doc Lam peak cnt fail ran,
  let len := Z.of_nat (length tb) in
  rp_sm = ReaderRes.jr_strtod ->
  fpre B ARx STK_parse_noting ly S Hp W regs mem md ch ->
  YAkMemnorm.memnorm segs mem ->
  prh_univ_closure B CTX0 ->
  getr regs 10 = w64 text -> getr regs 11 = w64 len -> getr regs 12 = w64 doc ->
  len < 2 ^ 40 -> 0 < text -> text + len < 2 ^ 62 ->
  src_rd W mem text tb -> PRH_FnReader.prhReader_home B ly S Hp Lam text len ->
  Z.of_nat (PjRoundTrip.maxrun tb) < 2 ^ 30 ->
  doc mod 8 = 0 -> ck_out_ok B STK_parse_noting ly S W regs mem doc 56 ->
  ran = 0 ->
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own -> cnt + 2 * len + 2 < 2 ^ 64 - 1 ->
  blocks_bytes S + PRH_FnPj.LIVE_pj_parse tb <= LIVE_MAX -> PRH_FnPj.RQ_pj_parse tb + cf_head < cf_malloc_max ->
  PRH_FnPj.RQ_pj_parse tb <= most ->
  Z.of_nat (length (frames S)) <= ck_FRAMES_CAP - FR_parse_noting -> ck_frm0 ->
  room_live_cf S -> PresetRoomPos.iface_room_pos rp_sm rp_x rp_os rp_i rp_H0 rp_hist S ->
  PRH_Base.prh_run_at rp_sm rp_x rp_os rp_i (PresetReqAt.parse_evs rp_sm tb []) ->
  PRH_Base.prh_cons_from rp_sm rp_x rp_os rp_i (length (PresetReqAt.parse_evs rp_sm tb [])) ->
  (fail < cnt \/ cnt + ck_ncalls tb <= fail) ->
  (* EDIT (P3) *)
  YCbqGwild.wild_room (as_universe B) [] (prh_wk F_parse_noting) (st_depot S) ->
  (* EDIT (P5): THE HULL BUDGET of the reading's all-granted events (tparse_noting_specX's, word for word) *)
  PresetHullBudget.hull_budget S (PresetReqAt.parse_evs ReaderRes.jr_strtod tb []) ->
  SRr' segs YGcfRehidePost.RZ_cf W (cfg_at segs (pa_sigma AS_parse_noting) regs mem md)
    (* EDIT (C0) *)
    (fpostFbm B ARx SK (YCbqGwild.wbudget [] (prh_wk F_parse_noting))
      STK_parse_noting [(doc, doc + 56)] regs ly S Hp W mem md
      (fun ly' S' Hp' W' regs' mem' md' =>
       room_live_cf S' /\
       exists Lam' peak' cnt' fail' ran' ok res tr,
       (PRH_FnReader.prhReader_agree ok [] (PjGrammar.calls tr) ->
          exists rp_hist', PresetRoomPos.iface_room_pos rp_sm rp_x rp_os
            (rp_i + length (PresetReqAt.parse_evs rp_sm tb [])) rp_H0 rp_hist' S') /\
       PjGrammar.jr_run ReaderRes.jr_strtod tb ok = (res, tr) /\
       prh_oks ok cnt fail (PjGrammar.calls tr) (prh_ev_reqs tr) most 0 ran' /\
       cnt' = cnt + Z.of_nat (PjGrammar.calls tr) /\ ReaderRes.fail_after cnt fail (PjGrammar.calls tr) fail' /\
       peak' = Z.max (Z.max peak (Ledger.lsum Lam + ReaderRes.hpeak tr))
         (prh_refused_peak ok cnt fail (PjGrammar.calls tr)
            (map (Z.add (Ledger.lsum Lam)) (prh_ev_helds (PRH_FnPj.prhPj_ptrace tb)))) /\
       ReaderRes.hpeak tr <= 224 * len + 16384 /\
       (cnt <= fail < cnt + ck_ncalls tb -> res = None) /\
       ran' = 0 /\
       (ran' = 0 -> fail < cnt \/ cnt + ck_ncalls tb <= fail ->
          res = ck_read tb /\ Z.of_nat (PjGrammar.calls tr) = ck_ncalls tb) /\
       bytes_at W' mem' text tb /\
       prh_ledger B ly' S' Hp' W' mem' Lam' peak' cnt' fail' ran' most own /\
       match res with
       | Some t =>
           getr regs' 10 = w64 0 /\
           exists D, Permutation Lam' (D ++ Lam) /\
             Permutation (map snd D) (map Z.of_nat (ReaderRes.lsz tr)) /\ Z.of_nat (length D) = ReaderRes.nlive tr /\
             (cf_head = PresetReqAt.HEAD -> Permutation (map (fun b => snd b + cf_head) D)
                (PresetReqAt.rd_blocks (PresetReqAt.rtr ReaderRes.jr_strtod ok tb))) /\
             (cf_head = PresetReqAt.HEAD -> forall n, (PjTree.depth t <= n)%nat ->
                exists F, PRH_PjOrder.pj_foR segs (rdW W' mem') (prh_lin Lam') n doc D F /\
                  map (fun b => snd b + cf_head) F = PresetReqAt.pj_frees ReaderRes.jr_strtod ok tb) /\
             (forall a k, In (a, k) D -> ~ In (a - cf_head, k + cf_head) (ablocks B ly S)) /\
             Permutation (ablocks B ly' S') (ablocks B ly S ++ ck_hblks D) /\
             pj_nodeR segs (rdW W' mem') (prh_lin Lam') doc t D
       | None =>
           getr regs' 10 = w64 (-1) /\ Permutation Lam' Lam /\ Permutation (ablocks B ly' S') (ablocks B ly S) /\
           pj_zeroR segs (rdW W' mem') doc
       end)).

(* THE BRIDGE to the granted twin: K -> grantedXb. No hypothesis. *)
Lemma tparse_noting_grantedXb_of_post : forall CTX0,
  tparse_noting_specX B ARx SK CTX0 -> tparse_noting_grantedXb CTX0.
Proof.
  intros CTX0 HK rp_sm rp_x rp_os rp_i rp_H0 rp_hist most own ly S Hp W regs mem md ch text tb doc Lam peak cnt
    fail ran len Hsm Hpre Hmn Hcl Hr10 Hr11 Hr12 Hlen Htx Htl Hsrc Hhome Hmax Hdoc Hout Hran Hled Hcnt Hlive Hrq
    Hrqm Hfr Hfrm Hrl Hpos Hrun Hcons Hpick Hwild Hhull.
  subst rp_sm.
  (* (P4): the two room counts from the entry position along the run *)
  pose proof (PresetRoomCounts.peak_sec_of_room_pos ReaderRes.jr_strtod rp_x rp_os rp_i rp_H0 rp_hist S
    (PresetReqAt.parse_evs ReaderRes.jr_strtod tb []) Hpos Hrun) as Hsec.
  pose proof (PresetRoomCounts.peak_c24_of_room_pos ReaderRes.jr_strtod rp_x rp_os rp_i rp_H0 rp_hist S
    (PresetReqAt.parse_evs ReaderRes.jr_strtod tb []) Hpos Hrun) as Hc24.
  unfold SRr'. eapply SRrG_mono;
    [exact (HK most own ly S Hp W regs mem md ch text tb doc Lam peak cnt fail ran Hpre Hmn Hcl Hr10 Hr11 Hr12
       Hlen Htx Htl Hsrc Hhome Hmax Hdoc Hout Hran Hled Hcnt Hlive Hrq Hrqm Hfr Hfrm Hrl Hwild Hsec Hc24 Hhull)|].
  intros W' c' _. apply ofpp_fpostFbm_mono.
  intros ly' S' Hp' W'' regs' mem' md' HQ. cbv beta in HQ |- *.
  (* K's post: its first conjunct is the hull use (not restated) *)
  destruct HQ as (_ & Hrl' & Lam' & peak' & cnt' & fail' & ran' & ok & res & tr & Hjr & _ & _ & Hocl & Hoks & Hc' & Hfa
    & Hpk & Hhp & Hp1 & _ & Hp3 & Hby & Hled' & Hm).
  (* (C1) and the granted flag: THE OUTCOME clause at the entry position, the run, the window and the pick *)
  destruct (Hocl ReaderRes.jr_strtod rp_x rp_os rp_i rp_H0 rp_hist Hpos Hrun Hcons Hpick) as (Hr0 & _ & _ & Hh).
  split; [exact Hrl'|].
  exists Lam', peak', cnt', fail', ran', ok, res, tr.
  split; [intros _; exact Hh|].
  split; [exact Hjr|]. split; [exact Hoks|]. split; [exact Hc'|]. split; [exact Hfa|]. split; [exact Hpk|].
  split; [exact Hhp|]. split; [exact Hp1|]. split; [exact Hr0|]. split; [exact Hp3|]. split; [exact Hby|].
  split; [exact Hled'|].
  (* (C3): the Some arm drops K's pj_ncapR *)
  destruct res as [t|].
  - destruct Hm as (H0 & D & HD1 & HD2 & HD3 & HD4 & HD5 & HD6 & HD7 & HD8 & _).
    split; [exact H0|]. exists D.
    exact (conj HD1 (conj HD2 (conj HD3 (conj HD4 (conj HD5 (conj HD6 (conj HD7 HD8))))))).
  - exact Hm.
Qed.

(* THE BRIDGE: K -> E with (P3) and (C0) as K has them, through the granted twin. No hypothesis. *)
Lemma tparse_noting_exactXb_of_post : forall CTX0,
  tparse_noting_specX B ARx SK CTX0 -> tparse_noting_exactXb CTX0.
Proof.
  intros CTX0 HK rp_sm rp_x rp_os rp_i rp_H0 rp_hist most own ly S Hp W regs mem md ch text tb doc Lam peak cnt
    fail ran len Hsm Hpre Hmn Hcl Hr10 Hr11 Hr12 Hlen Htx Htl Hsrc Hhome Hmax Hdoc Hout Hran Hled Hcnt Hlive Hrq
    Hrqm Hfr Hfrm Hrl Hpos Hrun Hcons Hpick Hwild Hhull.
  unfold SRr'. eapply SRrG_mono;
    [exact (tparse_noting_grantedXb_of_post CTX0 HK rp_sm rp_x rp_os rp_i rp_H0 rp_hist most own ly S Hp W regs
       mem md ch text tb doc Lam peak cnt fail ran Hsm Hpre Hmn Hcl Hr10 Hr11 Hr12 Hlen Htx Htl Hsrc Hhome Hmax Hdoc
       Hout Hran Hled Hcnt Hlive Hrq Hrqm Hfr Hfrm Hrl Hpos Hrun Hcons Hpick Hwild Hhull)|].
  intros W' c' _. apply ofpp_fpostFbm_mono.
  intros ly' S' Hp' W'' regs' mem' md' HQ. cbv beta in HQ |- *.
  destruct HQ as (Hrl' & Lam' & peak' & cnt' & fail' & ran' & ok & res & tr & Hh & Hjr & Hoks & Hc' & Hfa & Hpk
    & Hhp & Hp1 & Hr0 & Hrest).
  split; [exact Hrl'|].
  exists Lam', peak', cnt', fail', ran', ok, res, tr.
  split; [exact Hh|]. split; [exact Hjr|]. split; [exact Hoks|]. split; [exact Hc'|]. split; [exact Hfa|].
  split; [exact Hpk|]. split; [exact Hhp|]. split; [exact Hp1|].
  split; [intros Hne; contradiction (Hne Hr0)|].
  exact Hrest.
Qed.


(* ---- THE TWO BRIDGES AT THE WALK'S OWN NAMES (one home: lib/A/Prog/Ent102GrantA.v's granted texts) ---- *)
Lemma tcheck_no_overread_grantedX_of_post : forall CTX0,
  tcheck_no_overread_specX B ARx SK CTX0 -> Ent102GrantA.tcheck_no_overread_grantedX B ARx SK CTX0.
Proof.
  intros CTX0 HK. unfold Ent102GrantA.tcheck_no_overread_grantedX.
  exact (tcheck_no_overread_grantedXb_R1_of_post CTX0 HK).
Qed.
Lemma tparse_noting_grantedX_of_post : forall CTX0,
  tparse_noting_specX B ARx SK CTX0 -> Ent102GrantA.tparse_noting_grantedX B ARx SK CTX0.
Proof.
  intros CTX0 HK. unfold Ent102GrantA.tparse_noting_grantedX.
  exact (tparse_noting_grantedXb_of_post CTX0 HK).
Qed.

(* ---- THE THIRD BRIDGE (row LL3): the batch kit's PRH_FnCheck.tcheck_as_written_specX (FnCheck:832-902 at b1ed4e6c944d) gives
   the walk's lib/A/Prog/Ent102GrantA.v tcheck_as_written_grantX (GrantA:136-186 at b1ed4e6c944d). The two texts,
   line by line - every other line is the same bytes (the binders ly .. most, fpre .. prh_ledger, ran = 0 .. frames,
   room_live_cf S, the hull budget of the scratch pair, and the post's head: SRr', fpostFm STK_check_as_written [],
   room_live_cf S' /\ Hp' = Hp /\ ablocks, own', the ledger, bytes_at, r and its register):
   (D1) GrantA binds rp_sm rp_x rp_os rp_i rp_H0 rp_hist; the batch kit binds none (its position is post-implication).
   (D2) GrantA takes, after the ledger, the run `prh_run_at rp_sm rp_x rp_os rp_i [HMal (size + 1); HFr (size + 1)]`
        and the window `PRH_Base.prh_cons_from rp_sm rp_x rp_os rp_i 2`; the batch kit takes neither.
   (D3) GrantA takes the entry position `PresetRoomPos.iface_room_pos rp_sm rp_x rp_os rp_i rp_H0 rp_hist S` and
        `(length rp_os <= 4)%nat`; the batch kit takes instead the two room counts `YGcfRoomLive.sec_cnt S <= LSEC + DRV` and
        `YGcfRoomLive.ccnt24 S <= L24 + DRV`, which PresetRoomCounts.counts_of_room_pos_rl gives from that position,
        and HPOS, the run position at entry (exists a position of at most 4 calls whose next event is the scratch's
        malloc), which that position, its length bound and the run's first event (D2) give.
   (D4) the batch kit's post after the register is its OUTCOME clause (for every position, run of the scratch pair and window
        over it: r = 0 and the position after the pair) and the two arms (r = 1 /\ own' = 1 /\ the position kept) \/
        (r = 0 /\ own' = 0 /\ the position after the pair /\ the tree kept); GrantA's is the r = 0 arm alone at its
        own position, `r = 0 /\ own' = 0 /\ (exists hist', iface_room_pos .. (rp_i + 2) ..) /\ (rc = 0 -> pj_nodeR ..)`.
   NOT A DIFFERENCE: neither text is budgeted (both fpostFm; no wild_room premise), so no measured local form is
   needed and GrantA needs no budget edit. THE ROUTE: the outcome clause at GrantA's position, run and window (D2, D3)
   gives r = 0 and the position at rp_i + length [_; _] = rp_i + 2; r = 0 refutes the batch kit's r = 1 arm, and its r = 0 arm
   gives own' = 0 and the tree. Qed, no hypothesis. *)
(* the m-form float post is monotone in its Q *)
Lemma ofcaw_fpostFm_mono : forall STK FP regs ly S Hp W mem md
  (Q Q' : alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
  (forall ly' S' Hp' W' regs' mem' md', Q ly' S' Hp' W' regs' mem' md' -> Q' ly' S' Hp' W' regs' mem' md') ->
  forall W' c', fpostFm B ARx SK STK FP regs ly S Hp W mem md Q W' c' ->
  fpostFm B ARx SK STK FP regs ly S Hp W mem md Q' W' c'.
Proof.
  intros STK FP regs ly S Hp W mem md Q Q' HQ W' c'. unfold fpostFm, fpostF, apost_base_xF, fQmn.
  intros (fx' & ly' & S' & Hp' & regs' & mem' & md' & k & Hc & Hz & Hkf & HJ & Hpr & H1 & H2).
  exists fx', ly', S', Hp', regs', mem', md', k.
  split; [exact Hc|]. split; [exact Hz|]. split; [exact Hkf|]. split; [exact HJ|]. split; [exact Hpr|].
  exact (conj (HQ _ _ _ _ _ _ _ H1) H2).
Qed.

Lemma tcheck_as_written_grantX_of_post : forall CTX0,
  tcheck_as_written_specX B ARx SK CTX0 -> Ent102GrantA.tcheck_as_written_grantX B ARx SK CTX0.
Proof.
  intros CTX0 HK. unfold Ent102GrantA.tcheck_as_written_grantX.
  intros rp_sm rp_x rp_os rp_i rp_H0 rp_hist ly S Hp W regs mem md ch data x rc0 doc t D Lam peak cnt fail ran most
    Hpre Hmn Hcl Hr10 Hr11 Hr12 Hr13 Hrc Hdoc Hsz Hd0 Hds Hsrc Hblk Hrd Htree Hled Hrun Hcons Hran Hlive Hmx
    Hfr Hrl Hpos Hos4 Hhull Hfrm.
  (* (D3): the batch kit's two room counts from GrantA's entry position *)
  destruct (PresetRoomCounts.counts_of_room_pos_rl rp_sm rp_x rp_os rp_i rp_H0 rp_hist S Hpos) as [Hsec Hc24].
  (* (D3): HPOS from the position, its length bound and the run's first event (the scratch's malloc) *)
  assert (HPOS : exists (sm0 : list Z -> Z * Z) (x0 : list Z) (os0 : list (option nat * option nat * option nat))
      (i0 : nat) (H00 : list Z) (hist0 : list YG00.chunk),
      (length os0 <= 4)%nat /\ PresetRoomPos.iface_room_pos sm0 x0 os0 i0 H00 hist0 S /\
      PRH_Base.prh_run_at sm0 x0 os0 i0 [PresetReqAt.HMal (Z.of_nat (length x) + 1)]).
  { exists rp_sm, rp_x, rp_os, rp_i, rp_H0, rp_hist. split; [exact Hos4|]. split; [exact Hpos|].
    exact (proj1 (proj1 (prh_run_at_app_iff _ _ _ _ [_] [_]) Hrun)). }
  unfold SRr'. eapply SRrG_mono;
    [exact (HK ly S Hp W regs mem md ch data x rc0 doc t D Lam peak cnt fail ran most Hpre Hmn Hcl Hr10 Hr11 Hr12 Hr13
              Hrc Hdoc Hsz Hd0 Hds Hsrc Hblk Hrd Htree Hled Hran Hlive Hmx Hfr Hrl Hsec Hc24 Hhull HPOS Hfrm)|].
  intros W' c' _. apply ofcaw_fpostFm_mono.
  intros ly' S' Hp' W'' regs' mem' md' HQ. cbv beta in HQ |- *.
  destruct HQ as (Hrl' & HHp & HA & own' & Hled' & Hby & r & Hr & Hocl & Harms).
  (* (D4): the outcome clause at the position, the run and the window (D2) *)
  destruct (Hocl rp_sm rp_x rp_os rp_i rp_H0 rp_hist Hpos Hrun Hcons) as (Hr0 & Hh).
  split; [exact Hrl'|]. split; [exact HHp|]. split; [exact HA|].
  exists own'. split; [exact Hled'|]. split; [exact Hby|].
  exists r. split; [exact Hr|].
  destruct Harms as [(Hr1 & _ & _) | (_ & Ho & _ & Hnode)]; [lia|].
  split; [exact Hr0|]. split; [exact Ho|]. split; [exact Hh | exact Hnode].
Qed.

End c.
Print Assumptions tcheck_no_overread_grantedX_of_post.
Print Assumptions tparse_noting_grantedX_of_post.
Print Assumptions tcheck_as_written_grantX_of_post.
