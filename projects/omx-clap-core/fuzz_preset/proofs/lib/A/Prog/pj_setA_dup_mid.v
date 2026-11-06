(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: the FIRST HALF of segment DUP of pj_set's image-A' walk (fuzz_preset asan,
   A 0x8685c; the cuts of lib/A/Prog/pj_setA_defs.v): from the cut pjsA_DUP at `mv a0, s2` (+0xa8) through
   fuzz_strdup's STATED text (tfuzz_strdup_specX, pjsA_texts' fourth conjunct) to the state `pjsdA_C` at the
   first instrumented check (+0xb0), which lib/A/Prog/pj_setA_seg_dup.v walks to pjsA_FAILc or pjsA_TAIL.
     +0xa8  mv a0, s2      a0 := key
     +0xac  jal fuzz_strdup
   The cut is past grow (the re-hiding relation WR := YA0nH.wle' at YGcfRehidePost.RZ_cf): the two steps run plainly
   (YGcfRhLift.ra_rh_of_SRr) and the call is bound at WR (YSRrG.SRr'_bind) by YCbqGcallW.v aj_call_xWR at the callee
   window e1 = 0; fuzz_strdup's text is a plain SRr with an apost_base_x post, read as fpostW_x by YCbqGcallW.v
   fpostW_x_of_apost and lifted to WR (YA0nH.SRr_SRrG, YCbqGcallW.v fpostW_x_R_lift).
   Its hull budget (hull_budget S [HMal (|kname| + 1 + cf_head)]) is pjsA_g_hull's at the cut's position
   (pj_setA_glue.v pjsA_hull_mal; a run of at most 4 calls, pjsA_pre's length premise); what it leaves after its use
   (PresetHullBudget.hull_budget_used) is the NULL arm's hull_budget S' [], pj_free's at pjsA_FAILc.
   fuzz_strdup's premises come from the cut (the key's cstr_ok / kept_at in pjsA_data_c, the room), the entry's fpre
   (its last conjunct frm_zero (fp_csr fx): pj_set never changes fx) and the two live counts, which
   lib/Spec/PresetRoomCounts.v counts_of_room_pos_rl reads off the cut's model-run position at jsA_i + c;
   prh_malloc_univ follows from prh_univ_closure by PRH_Base.v prh_univ_closure_malloc. The text is
   POST-IMPLICATION (no position at entry): the walk applies each arm's position implication itself, at jsA_i + c.
   fuzz_strdup's post is read BY NAME (its top-level conjunctions split, each picked by its type). Its three arms
   (chosen failure, allocator refusal, success) collapse into the two arms of `pjsdA_C`:
   - THE DEAD REFUSAL ARM (pj_setA_defs.v's header): at jsA_i + c the run's event is the strdup's HMal (pjsA_pre's run
     premise prhPj_set_evs, whose absent arm ends in rd_hev (EAlloc (S |kname|)) = HMal (|kname| + 1 + HEAD), after
     grow's c events, at cf_head = HEAD), pjsA_pre's prh_cons_from covers that event (PRH_Base.prh_cons_from_sub), so
     THE OUTCOME conjunct gives res <> 0 whenever cnt + c <> fail: the refusal arm is exfalso, and a NULL is the
     CHOSEN failure, cnt + c = fail, with the granted peak (the NULL's implication with E = [] keeps the position, so
     the class-24 bound pjsA_PB holds);
   - dup <> 0: the grant's E is the run's event, so its implication advances the position to jsA_i + c + 1 =
     jsA_i + |prhPj_set_evs|.
   The object's ordered free list and val's agreement with the entry memory (pjsA_DUP's last two conjuncts) cross the
   call by the block and placement clauses of fuzz_strdup's journal (pjsdA_foot_agree). The memnorm keep (pjsA_invR's
   last conjunct) rides through fuzz_strdup's m-form post (PRH_Base.v fQmn).
   proves no function (kind: segment lemma, first half).
   Numerals: 48 / 56 (LENGTH: frame, struct); 8 (DERIVED: the pc offset of the return); register numbers 1, 9, 10,
   18 (WORD). No ADDRESS literal. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07 YI16.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YG0p YCbqG YCbqGcall YCbqGcallW FCiface YGcallMx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YGcfRoomKeep YG0dcf YGcfRoomPre.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK0o YK06 YGcfFsVis.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRoomLive.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YA0nH YSRrG YGcfRehidePost YGcfRhLift.
(* the live-set bounds of a model-run position (counts_of_room_pos_rl, lib/Spec/PresetRoomCounts.v), used qualified *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoomCounts PresetHullBudget.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar PresetLiveBounds.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoomPos PresetRun PresetReqAt PresetReqAtNoMiss.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_Charge PRH_FnReader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_FnPj PRH_FnAlloc PRH_PjOrder.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PjFoMember.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S1Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Img0 Listing_prog PAImg_prog PRH_Img.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S1ImgA pj_setA_defs pj_setA_glue pj_setA_steps pj_setA_vis pj_setA_dup_step pj_setA_dup_sep pj_setA_dup_tree.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import pj_set_trans.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Open Scope Z_scope.
#[local] Existing Instance prh_img_A.

(* the outcome list of the walk's c + 1 allocations: the c the arm already made (all granted) and the strdup *)
Definition pjsdA_ok (ok : list bool) (c : nat) (b : bool) : list bool :=
  map (fun j => nth j ok true) (seq 0 c) ++ [b].

Lemma pjsdA_ok_len : forall (ok : list bool) c, length (map (fun j => nth j ok true) (seq 0 c)) = c.
Proof. intros ok c. rewrite length_map, length_seq. reflexivity. Qed.

Lemma pjsdA_map_seq_nth : forall (f : nat -> bool) c s i d,
  (i < c)%nat -> nth i (map f (seq s c)) d = f (s + i)%nat.
Proof.
intros f c. induction c as [|c IH]; intros s i d Hi; [lia|].
cbn [seq map]. destruct i as [|i]; cbn [nth].
- f_equal. lia.
- rewrite (IH (Datatypes.S s) i d ltac:(lia)). f_equal. lia.
Qed.

Lemma pjsdA_ok_lt : forall ok c b i, (i < c)%nat -> nth i (pjsdA_ok ok c b) true = nth i ok true.
Proof.
intros ok c b i Hi. unfold pjsdA_ok.
pose proof (pjsdA_ok_len ok c) as Hl.
rewrite app_nth1 by lia.
rewrite (pjsdA_map_seq_nth (fun j => nth j ok true) c 0 i true ltac:(lia)).
reflexivity.
Qed.

Lemma pjsdA_ok_at : forall ok c b, nth c (pjsdA_ok ok c b) true = b.
Proof.
intros ok c b. unfold pjsdA_ok.
pose proof (pjsdA_ok_len ok c) as Hl.
rewrite app_nth2 by lia. rewrite Hl, Nat.sub_diag. reflexivity.
Qed.

(* ---- the model's events of an absent key: grow's c reallocs, then the key's strdup (PRH_FnPj.v prhPj_set_evs) ---- *)
Lemma pjsdA_zl_eqb_eq : forall a b, PresetReqAt.zl_eqb a b = true -> a = b.
Proof.
induction a as [|x a IH]; intros [|y b] H; cbn [PresetReqAt.zl_eqb] in H; try discriminate H; [reflexivity|].
apply andb_true_iff in H as [H1 H2]. apply Z.eqb_eq in H1. subst y. f_equal. exact (IH b H2).
Qed.

Lemma pjsdA_mfind_none : forall kname ms, ~ In kname (map fst ms) -> prhPj_mfind kname ms = None.
Proof.
intros kname ms. induction ms as [|[k u] r IH]; intros Hn; [reflexivity|].
cbn [prhPj_mfind]. destruct (PresetReqAt.zl_eqb k kname) eqn:E.
- exfalso. apply Hn. left. exact (pjsdA_zl_eqb_eq k kname E).
- apply IH. intros Hi. apply Hn. right. exact Hi.
Qed.

Lemma pjsdA_rd_hev_grow : forall m n, length (PresetReqAt.rd_hev (PjGrammar.EGrow m n)) = 1%nat.
Proof. intros [|m] n; reflexivity. Qed.

Lemma pjsdA_evs_absent : forall ms kname n cap (c : nat),
  ~ In kname (map fst ms) -> 0 <= n ->
  (n < cap /\ c = 0%nat \/ n = cap /\ c = 2%nat) ->
  exists g, length g = c /\
    prhPj_set_evs ms kname n cap = g ++ [PresetReqAt.HMal (Z.of_nat (length kname) + 1 + PresetReqAt.HEAD)].
Proof.
intros ms kname n cap c Hn Hn0 Hc. unfold prhPj_set_evs. rewrite (pjsdA_mfind_none kname ms Hn).
unfold PresetReqAt.rd_hevs. rewrite flat_map_app.
exists (flat_map PresetReqAt.rd_hev (PjRoundTrip.grow_ev true (Z.to_nat n) (Z.to_nat cap))). split.
- unfold PjRoundTrip.grow_ev. destruct Hc as [(Hlt & ->) | (-> & ->)].
  + replace (Nat.ltb (Z.to_nat n) (Z.to_nat cap)) with true by (symmetry; apply Nat.ltb_lt; lia). reflexivity.
  + rewrite Nat.ltb_irrefl. cbn [flat_map]. rewrite !length_app, !pjsdA_rd_hev_grow. reflexivity.
- cbn [flat_map PresetReqAt.rd_hev]. rewrite app_nil_r. rewrite Nat2Z.inj_succ.
  replace (Z.succ (Z.of_nat (length kname))) with (Z.of_nat (length kname) + 1) by lia. reflexivity.
Qed.

(* the run's event at jsA_i + c is the strdup's, and the call's events end at jsA_i + c + 1 *)
Lemma pjsdA_run_dup : forall (sm : list Z -> Z * Z) x os i ms kname n cap (c : nat),
  ~ In kname (map fst ms) -> 0 <= n ->
  (n < cap /\ c = 0%nat \/ n = cap /\ c = 2%nat) ->
  prh_run_at sm x os i (prhPj_set_evs ms kname n cap) ->
  nth_error (PresetRun.hruns sm x os) (i + c)%nat =
    Some (PresetReqAt.HMal (Z.of_nat (length kname) + 1 + PresetReqAt.HEAD)) /\
  length (prhPj_set_evs ms kname n cap) = Datatypes.S c.
Proof.
intros sm x os i ms kname n cap c Hn Hn0 Hc HR.
destruct (pjsdA_evs_absent ms kname n cap c Hn Hn0 Hc) as (g & Hg & E). rewrite E in HR |- *.
apply prh_run_at_app_iff in HR as (_ & HR). rewrite Hg in HR. apply prh_run_at_one in HR.
split; [exact HR|]. rewrite length_app, Hg. cbn [length]. lia.
Qed.

Section m. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Context {SK : YI16.sink_head}.
#[local] Notation PA := PI_prog_A.
#[local] Notation SEGS := (@pa_segs _ A_prog_listing PA).
#[local] Notation BASE := (@pa_val _ A_prog_listing PA A_TEXT).
#[local] Notation PST := (prh_pst (PI := prh_img_A)).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.
Hypothesis VIS : pjsA_g_vis B ARx.
(* the hull budget's instance fact (pj_setA_defs.v pjsA_g_hull) *)
Hypothesis HULL : @pjsA_g_hull cp.
#[local] Notation WR := (YA0nH.wle' SEGS YGcfRehidePost.RZ_cf).

(* a present byte is a readable byte *)
Lemma pjsdA_aview_some : forall (W : world SEGS) mem a,
  apresent (w_H W) mem a -> aview SEGS (w_H W) mem a <> None.
Proof.
intros W mem a (Hh & b & Hb). unfold aview, mbyte, mrestrict. rewrite Hh, Hb. cbn. discriminate.
Qed.

(* ---- the state at +0xb0, after fuzz_strdup returned: the cut is past grow, so its invariant is at WR ---- *)
Definition pjsdA_Cp (dd : nat) (en : PjsEntA) (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS)
  (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z)
  (dup : Z) (Lam2 Lam3 : list (Z * Z)) (peak3 fail3 ran3 : Z) (c : nat) (ok3 : list bool)
  (Do Lr Dold Dnew Dr : list (Z * Z)) (num3 str3 kids2 keys2 cap2v : Z) : Prop :=
  pjsA_invR B ARx WR dd en ly S Hp W regs mem md k /\ room_live_cf S /\
  getr regs 9 = w64 (jsA_o en) /\
    getr regs 10 = w64 dup /\
    prh_ledger (PA := PA) B ly S Hp W mem Lam3 peak3 (jsA_cnt en + Z.of_nat (Datatypes.S c)) fail3 ran3 (jsA_most en) (jsA_own en) /\
    (* the contract's outcome cell of the walk's c + 1 allocations (prh_oks over the trace's requests) *)
    prh_oks ok3 (jsA_cnt en) (jsA_fail en) (Datatypes.S c)
      (prh_ev_reqs (prhPj_set_trace (jsA_n en) (jsA_cap en) (jsA_kname en))) (jsA_most en) (jsA_ran en) ran3 /\
    ReaderRes.fail_after (jsA_cnt en) (jsA_fail en) (Datatypes.S c) fail3 /\
    (forall i, (i < c)%nat -> nth i ok3 true = true) /\
    ~ In (jsA_kname en) (map fst (jsA_ms en)) /\
    Permutation (jsA_Lam en) (jsA_D en ++ jsA_Dw en ++ Lr) /\
    Permutation Lam2 (Do ++ jsA_Dw en ++ Lr) /\
    prhPj_blocks B (jsA_ly en) (jsA_S en) (jsA_Lam en) ly S Lam3 /\
    Permutation (jsA_D en) (Dold ++ Dr) /\ Permutation Do (Dnew ++ Dr) /\
    jsA_D en = Dold ++ Dr /\ Do = Dnew ++ Dr /\
    prhPj_new B (jsA_ly en) (jsA_S en) Dnew /\
    (jsA_n en < jsA_cap en /\ c = 0%nat /\ kids2 = jsA_kids en /\ keys2 = jsA_keys en /\ cap2v = jsA_cap en /\
       Dold = [] /\ Dnew = []
     \/ jsA_n en = jsA_cap en /\ c = 2%nat /\ cap2v = cap2R (jsA_cap en) /\
       Dold = kids_blkR (jsA_kids en) (jsA_cap en) ++ keys_blkR 6 (jsA_keys en) (jsA_cap en) /\
       Dnew = [(kids2, 56 * cap2R (jsA_cap en)); (keys2, 8 * cap2R (jsA_cap en))]) /\
    jsA_n en < cap2v /\
    pj_nodeR SEGS (mrestrict (w_H W) mem) (prh_lin Lam3) (jsA_o en) (PjTree.JObj (jsA_ms en)) Do /\
    pj_hdrR SEGS (mrestrict (w_H W) mem) (jsA_o en) 6 num3 str3 kids2 keys2 (jsA_n en) cap2v /\
    pj_slots_atR (prh_lin Lam3) 6 kids2 keys2 (jsA_n en) cap2v /\
    pj_nodeR SEGS (mrestrict (w_H W) mem) (prh_lin Lam3) (jsA_w en) (jsA_tv en) (jsA_Dw en) /\
    pjsA_data_c B dd en ly S Lam3 W mem /\
    (forall x, jsA_w en <= x < jsA_w en + 56 -> ~ pj_footR (jsA_o en) Do x) /\
    jsA_w en + 56 <= YM05.alloc_ceiling /\
    (forall a, jsA_w en <= a < jsA_w en + 56 -> apresent (w_H W) mem a /\ ~ in_img SEGS a) /\
    (* pjsA_DUP's capacities, the object's ordered free list and val's agreement with the entry memory, carried
       across the call (pjsdA_foot_agree) *)
    jsA_cap en = Z.of_nat (PresetReqAt.ncap (length (jsA_ms en))) /\
    cap2v = Z.of_nat (PresetReqAt.ncap (Datatypes.S (length (jsA_ms en)))) /\
    (forall nn, (PjTree.depth (PjTree.JObj (jsA_ms en)) <= nn)%nat ->
       exists F, pj_foR SEGS (mrestrict (w_H W) mem) (prh_lin Lam3) nn (jsA_o en) Do F /\
         map (fun b => snd b + PresetReqAt.HEAD) F =
           PjFoMember.pfm_slots PresetReqAtNoMiss.kblk (jsA_ms en) ++
           PresetReqAt.arrz true (PresetReqAt.ncap (Datatypes.S (length (jsA_ms en))))) /\
    pj_agreeR SEGS (mrestrict (w_H (jsA_W en)) (jsA_mem en)) (mrestrict (w_H W) mem) (pj_footR (jsA_w en) (jsA_Dw en)) /\
    (* the arms; the last conjunct of each is the model-run fact its exit needs: the class-24 bound pjsA_PB at the
       kept position and pj_free's hull budget (pjsA_FAILc), the position past the call's own events (the contract's
       res = 0 position, pjsA_TAIL). A NULL is the CHOSEN failure (THE DEAD REFUSAL ARM), so its peak is the granted
       one. *)
    ((dup = 0 /\ Lam3 = Lam2 /\ jsA_cnt en + Z.of_nat c = jsA_fail en /\
      peak3 = Z.max (jsA_peak en) (Ledger.lsum Lam2) /\
      nth c ok3 true = false /\ pjsA_PB S /\ PresetHullBudget.hull_budget S [])
     \/
     (dup <> 0 /\ Lam3 = (dup, jsA_klen en + 1) :: Lam2 /\
      peak3 = Z.max (jsA_peak en) (Ledger.lsum Lam3) /\
      (forall i, (i < Datatypes.S c)%nat -> nth i ok3 true = true) /\
      bytes_at (PA := PA) W mem dup (jsA_kname en ++ [0]) /\
      4096 + cf_head <= dup /\ dup mod 16 = 0 /\
      (forall x, jsA_o en <= x < jsA_o en + 56 -> ~ (dup <= x < dup + jsA_klen en + 1)) /\
      (forall x, jsA_w en <= x < jsA_w en + 56 -> ~ (dup <= x < dup + jsA_klen en + 1)) /\
      exists hist, PresetRoomPos.iface_room_pos ReaderRes.jr_strtod (jsA_x en) (jsA_os en)
        (jsA_i en + length (pjsA_evs en))%nat (jsA_H0 en) hist S)).

Definition pjsdA_C (dd : nat) (en : PjsEntA) (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS)
  (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z) : Prop :=
  exists (dup : Z) (Lam2 Lam3 : list (Z * Z)) (peak3 fail3 ran3 : Z) (c : nat) (ok3 : list bool)
         (Do Lr Dold Dnew Dr : list (Z * Z)) (num3 str3 kids2 keys2 cap2v : Z),
  pjsdA_Cp dd en ly S Hp W regs mem md k dup Lam2 Lam3 peak3 fail3 ran3 c ok3 Do Lr Dold Dnew Dr
    num3 str3 kids2 keys2 cap2v.

(* a block the allocator appends was not live before (its own pairwise disjointness) *)
Lemma pjsdA_app_fresh : forall ly S ly' S' Hp' W' mem' md' q kq,
  ARx ly' S' Hp' W' mem' md' ->
  ablocks B ly' S' = ablocks B ly S ++ [(q, kq)] -> 0 <= kq ->
  ~ In (q, kq) (ablocks B ly S).
Proof.
intros ly S ly' S' Hp' W' mem' md' q kq HAR Eab Hkq Hin.
destruct (alx_blocks SEGS B ARx LAWS ly' S' Hp' W' mem' md' q kq HAR
  ltac:(rewrite Eab; apply in_or_app; right; left; reflexivity)) as (_ & _ & _ & _ & _ & Hpw).
rewrite Eab, map_app in Hpw. cbn [map] in Hpw.
pose proof (prh_pw_last zdisjoint _ _ Hpw (q, req_size kq)
  ltac:(apply in_map_iff; exists (q, kq); split; [reflexivity | exact Hin])) as Hdis.
unfold zdisjoint in Hdis. cbn [fst snd] in Hdis.
pose proof (prh_req_size_pos kq Hkq). lia.
Qed.

(* a struct's footprint across a call (pj_setA_vis.v pjsA_tree_kept's agreement, for any block list): its 56 bytes by
   the placement clause, its blocks by the block clause, when the blocks are harness blocks of both ledgers and the
   footprint lies outside the callee's *)
Lemma pjsdA_foot_agree {RJ : world SEGS -> world SEGS -> Prop} : forall ly S Hp W mem md Lam peak cnt fail ran
    most own STK1 sp FP1 ly2 S2 Hp2 W2 mem2 md2 k1
    Lam2 peak2 cnt2 fail2 ran2 most2 own2 (regs : bvmap 5 word) e p D,
  ajournal_xR (SK := SK) SEGS B PST ARx RJ STK1 sp FP1 ly S Hp W mem md [] ly2 S2 Hp2 W2 mem2 md2 k1 ->
  prh_ledger (PA := PA) B ly S Hp W mem Lam peak cnt fail ran most own ->
  prh_ledger (PA := PA) B ly2 S2 Hp2 W2 mem2 Lam2 peak2 cnt2 fail2 ran2 most2 own2 ->
  sp <= spZ regs -> spZ regs + e < 2 ^ 64 ->
  (forall b m, In (b, m) (ablocks B ly S) -> b <= p -> p + 56 <= b + m -> In (b, m) (ablocks B ly2 S2)) ->
  prhReader_at B ly S Lam regs e p 56 ->
  pj_rwR SEGS (mrestrict (w_H W2) mem2) p ->
  (forall a k, In (a, k) D -> In (a, k) Lam) ->
  (forall a k, In (a, k) D -> In (a, k) Lam2) ->
  (forall x, pj_footR p D x -> ~ inFP FP1 x) ->
  pj_agreeR SEGS (mrestrict (w_H W) mem) (mrestrict (w_H W2) mem2) (pj_footR p D).
Proof.
intros ly S Hp W mem md Lam peak cnt fail ran most own STK1 sp FP1 ly2 S2 Hp2 W2 mem2 md2 k1 Lam2 peak2 cnt2 fail2
  ran2 most2 own2 regs e p D HJ HL HL2 Hsp He HSB Hat Hrw2 HDL HDL2 HFP.
pose proof (@cf_head_nonneg cp) as Hh0.
pose proof (ajxR_ar HJ) as HAR2.
pose proof HL2 as (_ & _ & HLF2 & _).
apply pjsA_agree.
- intros x [Hx | ((a, k) & Hb & Hx)].
  + exact (pjsA_at_bytes B ARx ly S Hp W mem md STK1 sp FP1 ly2 S2 Hp2 W2 mem2 md2 k1 Lam peak cnt fail ran most own
      regs e p HJ HL Hsp He HSB Hat x Hx (HFP x (or_introl Hx))).
  + unfold pj_holdsR in Hx. cbn [fst snd] in Hx.
    exact (pjsA_lam_bytes B ARx ly S Hp W mem md STK1 sp FP1 ly2 S2 Hp2 W2 mem2 md2 k1 Lam peak cnt fail ran most own
      Lam2 peak2 cnt2 fail2 ran2 most2 own2 a k x HJ HL HL2 (HDL a k Hb) (HDL2 a k Hb) Hx
      (HFP x (or_intror (ex_intro _ (a, k) (conj Hb Hx))))).
- intros x [Hx | ((a, k) & Hb & Hx)] _.
  + exact (proj2 Hrw2 x Hx).
  + unfold pj_holdsR in Hx. cbn [fst snd] in Hx.
    pose proof (proj1 (Forall_forall _ _) HLF2 (a, k) (HDL2 a k Hb)) as (Hk0 & Hab2 & _). cbn [fst snd] in Hk0, Hab2.
    pose proof (pjsA_req (k + @cf_head cp) ltac:(lia)) as (Rq & _).
    exact (pjsA_blk_writable B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 _ _ x HAR2 Hab2 ltac:(lia)).
Qed.

(* an ORDERED free list across a call (PRH_PjOrder.pj_foR_frame over pjsdA_foot_agree, the block predicate moving
   to the new ledger) *)
Lemma pjsdA_fo_kept {RJ : world SEGS -> world SEGS -> Prop} : forall ly S Hp W mem md Lam peak cnt fail ran most own
    STK1 sp FP1 ly2 S2 Hp2 W2 mem2 md2 k1
    Lam2 peak2 cnt2 fail2 ran2 most2 own2 (regs : bvmap 5 word) e p d D F,
  ajournal_xR (SK := SK) SEGS B PST ARx RJ STK1 sp FP1 ly S Hp W mem md [] ly2 S2 Hp2 W2 mem2 md2 k1 ->
  prh_ledger (PA := PA) B ly S Hp W mem Lam peak cnt fail ran most own ->
  prh_ledger (PA := PA) B ly2 S2 Hp2 W2 mem2 Lam2 peak2 cnt2 fail2 ran2 most2 own2 ->
  sp <= spZ regs -> spZ regs + e < 2 ^ 64 ->
  (forall b m, In (b, m) (ablocks B ly S) -> b <= p -> p + 56 <= b + m -> In (b, m) (ablocks B ly2 S2)) ->
  prhReader_at B ly S Lam regs e p 56 ->
  pj_rwR SEGS (mrestrict (w_H W2) mem2) p ->
  (forall a k, In (a, k) D -> In (a, k) Lam2) ->
  (forall x, pj_footR p D x -> ~ inFP FP1 x) ->
  pj_foR SEGS (mrestrict (w_H W) mem) (prh_lin Lam) d p D F ->
  pj_foR SEGS (mrestrict (w_H W2) mem2) (prh_lin Lam2) d p D F.
Proof.
intros ly S Hp W mem md Lam peak cnt fail ran most own STK1 sp FP1 ly2 S2 Hp2 W2 mem2 md2 k1 Lam2 peak2 cnt2 fail2
  ran2 most2 own2 regs e p d D F HJ HL HL2 Hsp He HSB Hat Hrw2 HDL2 HFP HF.
apply (pj_foR_frame SEGS d _ _ (prh_lin Lam) (prh_lin Lam2) p D F HF); [exact HDL2|].
apply (pjsdA_foot_agree ly S Hp W mem md Lam peak cnt fail ran most own STK1 sp FP1 ly2 S2 Hp2 W2 mem2 md2 k1
  Lam2 peak2 cnt2 fail2 ran2 most2 own2 regs e p D HJ HL HL2 Hsp He HSB Hat Hrw2); [|exact HDL2 | exact HFP].
intros a k Hb. exact (pj_foR_lblk SEGS _ _ d p D F HF a k Hb).
Qed.

(* fuzz_strdup's post read BY NAME (Ent102CallB.v's ec_conj_split, local copy): its top-level conjunctions split *)
Local Ltac pjsdA_conj_split H :=
  lazymatch type of H with
  | _ /\ _ =>
    let H1 := fresh "Hc" in let H2 := fresh "Hc" in destruct H as [H1 H2]; pjsdA_conj_split H1; pjsdA_conj_split H2
  | _ => idtac
  end.

(* ---- the call (the cut is past grow: bound at WR) ---- *)
Theorem pjsdA_call : forall CTX0 dd en ly S Hp W regs mem md k,
  pjsA_texts B ARx CTX0 dd -> pjsA_frame_kept_stmtR B ARx WR dd ->
  pjsA_pre B ARx CTX0 dd en -> pjsA_DUP B ARx dd en ly S Hp W regs mem md k ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W (pjsA_cfg PJSA_DUP regs mem md)
    (fun W2 c2 => exists ly2 S2 Hp2 regs2 mem2 md2 k2,
       c2 = pjsA_cfg (PJSA_DUP + 8) regs2 mem2 md2 /\
       pjsdA_C dd en ly2 S2 Hp2 W2 regs2 mem2 md2 k2).
Proof.
intros CTX0 dd en ly S Hp W regs mem md k TXT KEEP HPRE HCUT.
destruct TXT as (_ & _ & _ & SD & _ & _).
pose proof (@pa_segs_low _ A_prog_listing PA) as Hsegs.
pose proof asan_consts as (CA1 & CA2 & CA3 & CA4 & CA5).
pose proof (@cf_head_nonneg cp) as Hh0.
pose proof HPRE as HPRE0.
unfold pjsA_pre in HPRE. cbv zeta in HPRE.
destruct HPRE as (HFPRE & HUNIV & HROOM0 & _ & HLOS & HCONS & _ & _ & _ & HFWIN & HNODE0 & HHDR0 & HCAP & HSLOTO0 & HNODEW0 &
  HSLOTW0 & HWLOW & HDW & HWF & HAPW & HDEPO & HDEPV & HCSTR0 & HKEPT0 & HKF & HLED0 & HCNT & HKLEN & HGROW & HLIVE &
  _ & _ & HHEAD & HRUN).
pose proof HFPRE as ((HAR0 & Hra0 & Hra40 & Hgp0 & Htp0 & Hstk0 & Hpres0 & Hch0 & Hqt0) & HROD0 & HSTKHI0 & HRAC0).
(* the kit-FRM0-ENTRY: the entry's rounding mode, which fuzz_strdup's fpre asks of the same fx *)
assert (HFRM : YK0o.frm_zero (@YK11.fp_csr fx)) by (destruct HFPRE as (_ & _ & _ & _ & H); exact H).
pose proof Hstk0 as (Hal0 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop0 & Htop20).
pose proof HFWIN as (Hd0 & Hd16 & Hdtop & Hdpres).
destruct HCUT as (HINV & HROOM & Lam2 & peak2 & c & ok & Do & Lr & kids2 & keys2 & cap2v & Dold & Dnew & Dr &
  HLED & Hoks & Hokall & Hfnot & HpLam & HpLam2 & HBLK & HNI & HpD & HpDo & HNEW & HCASE & Hpeak2 & Hncap2 &
  (hist & HPOS) & HLIVE2 & HNODEo & HHDRo & HSLOTS & H9 & HNODEW & HDATAC & HoD & HoDo & Hcapm & Hcap2m & HFO &
  HAGRW).
(* fuzz_strdup's live-set premises, from the position at jsA_i + c *)
destruct (PresetRoomCounts.counts_of_room_pos_rl _ _ _ _ _ _ _ HPOS) as (HSEC & HC24).
pose proof HINV as (HJ & HWIN & Hsp & Hra & Hs0 & Hs1 & Hs2 & Hs3 & Hs4 & H8 & H18 & H20 & HKEPT & HPRES & HROD &
  HMN).
pose proof (ajxR_ar HJ) as HARc. pose proof (ajxR_ly HJ) as Hly. pose proof (ajxR_frs HJ) as HFRS. pose proof (ajxR_hi HJ) as F1. pose proof (ajxR_blk HJ) as F2. pose proof (ajxR_frm HJ) as F4. pose proof (ajxR_pres HJ) as HPRESJ. pose proof (ajxR_stk HJ) as Hast.
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
rewrite app_nil_l in HFRS.
pose proof HDATAC as (_ & HPLo & HSLOTW & HCSTR & HKEPTk).
(* c is 0 or 2 *)
assert (Hc2 : (c <= 2)%nat) by (destruct HCASE as [(_ & -> & _) | (_ & -> & _)]; lia).
assert (HSTKS : 0 <= STK_fuzz_strdup) by (apply Z.leb_le; vm_compute; reflexivity).
assert (HSTKB : STK_fuzz_strdup + 48 <= STK_pj_set dd).
{ unfold STK_pj_set, zmaxl. cbn [fold_right].
  replace (pi_frame F_pj_set) with 48 by (vm_compute; reflexivity). lia. }
assert (HW4096 : 4096 <= jsA_w en) by (destruct HSLOTW as (H & _); exact H).
(* the value struct lies below the ceiling (it is no stack struct: the kit bounds it) *)
assert (HWCEIL : jsA_w en + 56 <= YM05.alloc_ceiling).
{ destruct HSLOTW as (_ & Hat & _).
  destruct Hat as [(a & kk & Hin & Ha & Hk) | [(b & m & Hin & _ & Hb & Hm) |
    [(cid & pos & Hin & Hf & Hfm) | (Hw1 & Hw2)]]].
  - destruct (prh_ledger_hblock B ly S Hp W mem Lam2 peak2 (jsA_cnt en + Z.of_nat c) (jsA_fail en) (jsA_ran en) a kk (jsA_most en) (jsA_own en) HLED Hin) as (Hk0 & Hab & _).
    destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md _ _ HARc Hab) as (_ & _ & Hcl & _).
    pose proof (pjsA_req (kk + @cf_head cp) ltac:(lia)) as (Rq & _). lia.
  - destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md b m HARc Hin) as (_ & _ & Hcl & _).
    pose proof (pjsA_req m ltac:(lia)) as (Rm & _). lia.
  - destruct (frames_bounds_x SEGS B ARx LAWS ly S Hp W mem md cid pos HARc Hin) as (_ & Hc' & _). lia.
  - exfalso. pose proof Hast as (_ & _ & Hc1 & Hc2' & _). lia. }
assert (HWPRES : forall a, jsA_w en <= a < jsA_w en + 56 -> apresent (w_H W) mem a /\ ~ in_img SEGS a).
{ intros a Ha. destruct HSLOTW as (_ & Hat & _).
  destruct Hat as [(a0 & kk & Hin & Ha1 & Hk1) | [(b & m & Hin & _ & Hb & Hm) |
    [(cid & pos & Hin & Hf & Hfm) | (Hw1 & Hw2)]]].
  - destruct (prh_ledger_hblock B ly S Hp W mem Lam2 peak2 (jsA_cnt en + Z.of_nat c) (jsA_fail en) (jsA_ran en) a0 kk (jsA_most en) (jsA_own en) HLED Hin) as (Hk0 & Hab & _).
    pose proof (pjsA_req (kk + @cf_head cp) ltac:(lia)) as (Rq & _).
    destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md _ _ HARc Hab) as (_ & _ & _ & _ & Hbpo & _).
    split; [exact (proj1 (Hbpo a ltac:(lia)))|].
    exact (blk_img_x SEGS B ARx LAWS ly S Hp W mem md _ _ a HARc Hab ltac:(lia)).
  - pose proof (pjsA_req m ltac:(lia)) as (Rm & _).
    destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md b m HARc Hin) as (_ & _ & _ & _ & Hbpo & _).
    split; [exact (proj1 (Hbpo a ltac:(lia)))|].
    exact (blk_img_x SEGS B ARx LAWS ly S Hp W mem md b m a HARc Hin ltac:(lia)).
  - destruct (alx_frames SEGS B ARx LAWS ly S Hp W mem md cid pos HARc Hin) as (_ & _ & Hfpo & _).
    split; [exact (proj1 (Hfpo a ltac:(lia)))|].
    exact (frm_img_x SEGS B ARx LAWS ly S Hp W mem md cid pos a HARc Hin ltac:(lia)).
  - exfalso. pose proof Hast as (_ & _ & Hc1 & Hc2' & _). lia. }
(* fuzz_strdup's hull budget at the call: one malloc of |kname| + 1 + cf_head at the cut's position *)
assert (HHBS : PresetHullBudget.hull_budget S
  [PresetReqAt.HMal (Z.of_nat (length (jsA_kname en)) + 1 + cf_head)]).
{ apply (pjsA_hull_mal HULL _ _ _ _ _ _ S _ HLOS HPOS). unfold jsA_klen in HKLEN. lia. }
unfold pjsA_cfg.
apply YGcfRhLift.ra_rh_of_SRr.
(* ======== +0xa8  mv a0, s2 ======== *)
pjsA_fd PJSA_DUP Hl1 Hd1.
eapply (pjsA_step_addi W regs mem md _ PJSA_DUP _ _ _ _ (10%bv : bv 5) (getr regs (18%bv : bv 5)) Hl1 Hd1).
{ vm_compute. reflexivity. }
{ apply bv_eq. vm_compute. reflexivity. }
{ lazymatch goal with |- v_addi (getr _ ?rs) (bv_signed ?im) = _ =>
    replace rs with (18%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity);
    replace (bv_signed im) with 0 by (vm_compute; reflexivity) end.
  unfold v_addi. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned. }
intros X1.
pose proof (ajournal_x_materializeR (SK := SK) SEGS B PST ARx LAWS Hsegs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X1 HJ) as HJ1.
replace (v_addi (Z_to_bv 64 (BASE + PJSA_DUP)) 4) with (Z_to_bv 64 (BASE + (PJSA_DUP + 4)))
  by (apply bv_eq; vm_compute; reflexivity).
(* ======== +0xac  jal fuzz_strdup ======== *)
pjsA_fd (PJSA_DUP + 4) Hl2 Hd2.
eapply (pjsA_step_jal W _ mem _ _ (PJSA_DUP + 4) _ _ _ (1%bv : bv 5) (Z_to_bv 64 (BASE + (PJSA_DUP + 8)))
  (Z_to_bv 64 (@pa_sigma _ A_prog_listing PA AS_fuzz_strdup)) Hl2 Hd2).
{ vm_compute. reflexivity. }
{ apply bv_eq. vm_compute. reflexivity. }
{ apply bv_eq. vm_compute. reflexivity. }
{ apply bv_eq. vm_compute. reflexivity. }
intros X2.
pose proof (ajournal_x_materializeR (SK := SK) SEGS B PST ARx LAWS Hsegs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X2 HJ1) as HJ2.
lazymatch goal with |- SRr _ _ (mkCfg (@YK11.mkst _ ?r _ _ _) ?m) _ =>
  remember r as regsc eqn:Eregsc; set (mdc := m) in * end.
assert (HSPC : spZ regsc = jsA_sp1 en).
{ unfold YG0d.spZ at 1. rewrite Eregsc, !getr_other by pjsA_regne. exact Hsp. }
assert (HS0LOW : s0Z regsc < YM05.alloc_ceiling).
{ unfold YG0d.s0Z. rewrite Eregsc, !getr_other by pjsA_regne. rewrite H8. unfold w64.
  rewrite unsigned_lit_small by lia. lia. }
assert (HGP : getr regsc 3 = w64 (as_gp B)).
{ rewrite Eregsc, !getr_other by pjsA_regne. rewrite (HKEPT 3%bv) by (unfold PJSA_KEPT; left; reflexivity).
  exact Hgp0. }
assert (HTP : getr regsc 4 = w64 (as_tp B)).
{ rewrite Eregsc, !getr_other by pjsA_regne. rewrite (HKEPT 4%bv) by (unfold PJSA_KEPT; right; left; reflexivity).
  exact Htp0. }
assert (HRA1 : getr regsc 1 = Z_to_bv 64 (BASE + (PJSA_DUP + 8)))
  by (rewrite Eregsc; apply getr_same; pjsA_regne).
assert (HRAW : YK0s.ret_ok (Z_to_bv 64 (BASE + (PJSA_DUP + 8)))).
{ apply (YC1fP.ret_ok_codeptr_v (PI := PA));
  [split; [apply Z.leb_le | apply Z.ltb_lt]; vm_compute; reflexivity | vm_compute; reflexivity]. }
assert (HRA4 : 4096 <= bv_unsigned (Z_to_bv 64 (BASE + (PJSA_DUP + 8))))
  by (apply Z.leb_le; vm_compute; reflexivity).
assert (HSPO : spZ regsc = jsA_sp0 en + jsA_d en + (- 48 - jsA_d en))
  by (rewrite HSPC; unfold jsA_sp1, jsA_sp0, PJSA_FR; lia).
assert (Ea0 : getr regsc 10 = w64 (jsA_k en))
  by (rewrite Eregsc; rewrite getr_other by pjsA_regne; rewrite getr_same by pjsA_regne; exact H18).
assert (HMU : prh_malloc_univ B).
{ exact (prh_univ_closure_malloc B CTX0 HUNIV ltac:(vm_compute; discriminate)). }
(* ======== the call: fuzz_strdup's text at the callee window e1 = 0, bound at WR ======== *)
apply SRr_ret. cbv beta.
eapply (YSRrG.SRr'_bind SEGS YGcfRehidePost.RZ_cf).
{ eapply (aj_call_xWR (fx := fx) (SK := SK) SEGS B PST ARx LAWS Hsegs WR
    (YA0nH.wle'_refl SEGS YGcfRehidePost.RZ_cf) (YA0nH.wle'_trans SEGS YGcfRehidePost.RZ_cf) W regsc mem
    (@pa_sigma _ A_prog_listing PA AS_fuzz_strdup)
    (STK_pj_set dd + jsA_d en) (jsA_sp0 en + jsA_d en) (pjsA_FP en)
    (jsA_ly en) (jsA_S en) (jsA_Hp en) (jsA_W en) (jsA_mem en) (jsA_md en) [] ly S Hp mdc k
    STK_fuzz_strdup 0 [] (- 48 - jsA_d en) (Z_to_bv 64 (BASE + (PJSA_DUP + 8))) []
    _ HJ2 HSPO ltac:(lia) ltac:(lia) HSTKS ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
    HGP HTP HRA1 HRAW HRA4 (achain_low _ _ _ _ HS0LOW)).
  - intros HPRE1 _.
    apply (YA0nH.SRr_SRrG SEGS _ (YA0nH.wle_wle' SEGS YGcfRehidePost.RZ_cf)).
    eapply SRr_mono.
    + apply (SD ly S Hp W regsc mem mdc [] (jsA_k en) (jsA_kname en) Lam2 peak2
        (jsA_cnt en + Z.of_nat c) (jsA_fail en) (jsA_ran en) (jsA_most en) (jsA_own en)).
      * split; [exact HPRE1|]. split; [exact HROD|].
        split; [rewrite HSPC, Eshi; unfold jsA_sp1, jsA_sp0, PJSA_FR; lia|].
        split; [|exact HFRM].
        (* fpre's return-address bound: the jal's return pc +0xb0, a text literal below the ceiling *)
        unfold raZ. rewrite HRA1. eapply Z.lt_le_trans; [|apply (proj1 CA1)].
        apply Z.ltb_lt. vm_compute. reflexivity.
      * exact HROOM.
      * exact HMU.
      * exact HSEC.
      * exact HC24.
      * exact HHBS.
      * exact Ea0.
      * exact HCSTR.
      * exact HKEPTk.
      * unfold jsA_klen in HKLEN. exact HKLEN.
      * exact HLED.
      * (* the live room, guarded by the call's success flag (cnt <> fail) in the text *)
        intros _. unfold jsA_klen in HLIVE2. exact HLIVE2.
    + intros W' c' _ Hap.
      apply (fpostW_x_R_lift (SK := SK) SEGS B PST ARx WR (YA0nH.wle_wle' SEGS YGcfRehidePost.RZ_cf)).
      exact (fpostW_x_of_apost (SK := SK) SEGS B PST ARx STK_fuzz_strdup [] regsc ly S Hp
        W mem mdc _ W' c' Hap).
  - intros a Ha. exfalso. exact (inFP_nil a Ha). }
cbv beta. intros W2 c2 _ (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & -> & HJ2' & HJc & _ & HP2 & HK).
unfold fQmn in HK. cbv beta in HK.
(* fuzz_strdup's post BY NAME: its conjunctions split, each picked by its type *)
destruct HK as ((res & HKp) & HMN2).
pjsdA_conj_split HKp.
lazymatch goal with H : getr regs2 _ = w64 res |- _ => rename H into Hres end.
lazymatch goal with H : room_live_cf S2 |- _ => rename H into HROOM2 end.
lazymatch goal with H : res = 0 -> forall _ _ _ _ _ _, _ |- _ => rename H into HPZ end.
lazymatch goal with H : res <> 0 -> forall _ _ _ _ _ _, _ |- _ => rename H into HPNZ end.
lazymatch goal with H : forall _ _ _ _ _ _, _ -> _ -> PRH_Base.prh_cons_from _ _ _ _ _ -> _ |- _ =>
  rename H into HOUT end.
lazymatch goal with H : context [prh_alloc_post] |- _ => rename H into HAPOST end.
lazymatch goal with H : PresetHullBudget.hull_used S S2 _ |- _ => rename H into HUSEDS end.
lazymatch goal with H : res <> 0 -> bytes_at _ _ _ _ |- _ => rename H into HBYT end.
replace (STK_fuzz_strdup + 0) with STK_fuzz_strdup in HJc by lia.
replace (jsA_sp0 en + jsA_d en + (- 48 - jsA_d en) + 0) with (jsA_sp1 en) in HJc
  by (unfold jsA_sp1, jsA_sp0, PJSA_FR; lia).
(* ---- what the state looks like after the call ---- *)
pose proof (ajxR_ar HJ2) as HARmc.
pose proof (ajxR_ar HJ2') as HAR2. pose proof (ajxR_ly HJ2') as Hly2. pose proof (ajxR_frs HJ2') as HFRS2. pose proof (ajxR_pres HJ2') as HPRES2.
pose proof (ajxR_ly HJc) as Hlyc. pose proof (ajxR_frs HJc) as HFRSc. pose proof (ajxR_stk HJc) as Hastc.
rewrite app_nil_l in HFRS2, HFRSc.
assert (HASTK0 : astk_ok (STK_pj_set dd) ly (jsA_sp0 en)).
{ pose proof Hstk0 as HS. unfold astk_ok, ly_bot, jsA_sp0 in HS |- *.
  rewrite Eslo, Eshi, Etop. exact HS. }
pose proof HASTK0 as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9).
assert (Hdhi : jsA_sp0 en + jsA_d en <= ly_stk_hi ly).
{ rewrite Eshi. pose proof Hstk0 as (_ & _ & _ & _ & _ & _ & _ & _ & A9).
  unfold jsA_sp0 in *. lia. }
assert (Hdtop' : jsA_sp0 en + jsA_d en <= ly_top ly) by (rewrite Etop; unfold jsA_sp0 in *; lia).
assert (HCEILSP : YM05.alloc_ceiling <= jsA_sp0 en) by lia.
assert (HPRW : forall a, jsA_sp1 en <= a < jsA_sp0 en + jsA_d en -> apresent (w_H W2) mem2 a).
{ intros a Ha. apply HPRES2. unfold jsA_sp1, jsA_sp0, PJSA_FR in *. lia. }
assert (HWSP : jsA_w en < jsA_sp0 en) by lia.
(* the callee's journal at pj_set's widened window *)
destruct (pjsA_aj_widen B ARx STK_fuzz_strdup (jsA_sp1 en) [] ly S Hp W mem mdc []
  ly2 S2 Hp2 W2 mem2 md2 k1 (48 + jsA_d en) HJc ltac:(lia)
  ltac:(unfold astk_ok, ly_bot, jsA_sp1, jsA_sp0, PJSA_FR in *; repeat split; lia)
  ltac:(intros a Ha; apply HPRW; unfold jsA_sp1, jsA_sp0, PJSA_FR in *; lia)) as (HJcW & HXW).
replace (jsA_sp1 en + (48 + jsA_d en)) with (jsA_sp0 en + jsA_d en) in HJcW, HXW
  by (unfold jsA_sp1, jsA_sp0, PJSA_FR; lia).
destruct (KEEP en ly S Hp W regsc mem mdc k STK_fuzz_strdup [] ly2 S2 Hp2 W2 mem2 md2 k1
  ltac:(split; [exact HJ2|]; split; [exact HWIN|];
        split; [exact HSPC|]; split; [exact Hra|]; split; [exact Hs0|]; split; [exact Hs1|];
        split; [exact Hs2|]; split; [exact Hs3|]; split; [exact Hs4|];
        split; [rewrite Eregsc, !getr_other by pjsA_regne; exact H8|];
        split; [rewrite Eregsc, !getr_other by pjsA_regne; exact H18|];
        split; [rewrite Eregsc, !getr_other by pjsA_regne; exact H20|];
        split; [intros r Hr; rewrite Eregsc, !getr_other by pjsA_kept_ne; exact (HKEPT r Hr)|];
        split; [exact HPRES|]; split; [exact HROD | exact HMN])
  HJcW
  ltac:(intros a Ha Hf; apply HXW; [unfold jsA_sp1, jsA_sp0, PJSA_FR in *; lia | exact Hf])
  ltac:(intros a _ Hf; exact (inFP_nil a Hf))
  ltac:(intros a _ _ Hf; exact (inFP_nil a Hf))
  HSTKS Hd0 sink_closed_nil) as (KW & KRA & KS0 & KS1 & KS2 & KS3 & KS4 & KPR & KROD).
(* ---- the three arms of fuzz_strdup, bundled ---- *)
pose proof HLED0 as HB0. apply prh_ledger_bounds in HB0. destruct HB0 as (_ & _ & Hcntr & Hfailr & _).
set (ok3 := pjsdA_ok ok c (negb (res =? 0))).
assert (Hok3lt : forall i, (i < c)%nat -> nth i ok3 true = true)
  by (intros i Hi; unfold ok3; rewrite pjsdA_ok_lt by lia; exact (Hokall i Hi)).
assert (Hok3at : nth c ok3 true = negb (res =? 0)) by (unfold ok3; apply pjsdA_ok_at).
assert (Hcntmod : (jsA_cnt en + Z.of_nat c + 1) mod 2 ^ 64 = jsA_cnt en + Z.of_nat (Datatypes.S c)).
{ rewrite Nat2Z.inj_succ.
  replace (jsA_cnt en + Z.succ (Z.of_nat c)) with (jsA_cnt en + Z.of_nat c + 1) by lia.
  apply Z.mod_small. lia. }
assert (Hn0 : 0 <= jsA_n en) by (pose proof HHDRo as (_ & _ & _ & _ & _ & _ & (Hnr0 & _) & _); lia).
assert (HCc : jsA_n en < jsA_cap en /\ c = 0%nat \/ jsA_n en = jsA_cap en /\ c = 2%nat)
  by (destruct HCASE as [(HCa & HCb & _) | (HCa & HCb & _)]; [left | right]; split; assumption).
(* the run's event at jsA_i + c is the strdup's own HMal (at cf_head = HEAD), and pjsA_pre's consumer window covers it *)
destruct (pjsdA_run_dup ReaderRes.jr_strtod (jsA_x en) (jsA_os en) (jsA_i en) (jsA_ms en) (jsA_kname en) (jsA_n en)
  (jsA_cap en) c HNI Hn0 HCc HRUN) as (Hev & Hlen).
assert (HRD : PRH_Base.prh_run_at ReaderRes.jr_strtod (jsA_x en) (jsA_os en) (jsA_i en + c)%nat
  [PresetReqAt.HMal (Z.of_nat (length (jsA_kname en)) + 1 + cf_head)]).
{ apply (proj2 (prh_run_at_one _ _ _ _ _)). rewrite HHEAD. exact Hev. }
assert (HCD : PRH_Base.prh_cons_from ReaderRes.jr_strtod (jsA_x en) (jsA_os en) (jsA_i en + c)%nat
  (length [PresetReqAt.HMal (Z.of_nat (length (jsA_kname en)) + 1 + cf_head)])).
{ apply (PRH_Base.prh_cons_from_sub _ _ _ _ (length (prhPj_set_evs (jsA_ms en) (jsA_kname en) (jsA_n en) (jsA_cap en)))
    c _); [rewrite Hlen; cbn [length]; lia | exact HCONS]. }
(* THE DEAD REFUSAL ARM: with no injected failure at this call, THE OUTCOME conjunct says the strdup granted *)
assert (HGRANT : jsA_cnt en + Z.of_nat c <> jsA_fail en -> res <> 0)
  by (intros Hne; exact (proj1 (HOUT _ _ _ _ _ _ HPOS HRD HCD Hne))).
assert (HARM : exists (Lam3 : list (Z * Z)) (peak3 fail3 ran3 : Z),
  prh_ledger (PA := PA) B ly2 S2 Hp2 W2 mem2 Lam3 peak3 (jsA_cnt en + Z.of_nat (Datatypes.S c)) fail3 ran3 (jsA_most en) (jsA_own en) /\
  prh_oks ok3 (jsA_cnt en) (jsA_fail en) (Datatypes.S c)
    (prh_ev_reqs (prhPj_set_trace (jsA_n en) (jsA_cap en) (jsA_kname en))) (jsA_most en) (jsA_ran en) ran3 /\
  ReaderRes.fail_after (jsA_cnt en) (jsA_fail en) (Datatypes.S c) fail3 /\
  (forall b m, In (b, m) (ablocks B ly S) -> In (b, m) (ablocks B ly2 S2)) /\
  (forall a kk, In (a, kk) Lam2 -> In (a, kk) Lam3) /\
  (forall b m, In (b, m) (ablocks B ly S) -> ~ In (b + cf_head, m - cf_head) Lam2 ->
     ~ In (b + cf_head, m - cf_head) Lam3) /\
  prhPj_blocks B (jsA_ly en) (jsA_S en) (jsA_Lam en) ly2 S2 Lam3 /\
  ((res = 0 /\ Lam3 = Lam2 /\ jsA_cnt en + Z.of_nat c = jsA_fail en /\
    peak3 = Z.max (jsA_peak en) (Ledger.lsum Lam2) /\ nth c ok3 true = false)
   \/ (res <> 0 /\ Lam3 = (res, jsA_klen en + 1) :: Lam2 /\
       peak3 = Z.max (jsA_peak en) (Ledger.lsum Lam3) /\
       (forall i, (i < Datatypes.S c)%nat -> nth i ok3 true = true) /\
       bytes_at (PA := PA) W2 mem2 res (jsA_kname en ++ [0]) /\
       4096 + cf_head <= res /\ res mod 16 = 0 /\
       ablocks B ly2 S2 = ablocks B ly S ++ [(res - cf_head, jsA_klen en + 1 + cf_head)]))).
{ assert (Hok0 : jsA_cnt en + Z.of_nat c <> jsA_fail en ->
    forall i, (i < Datatypes.S c)%nat -> jsA_cnt en + Z.of_nat i <> jsA_fail en).
  { intros Hne i Hi Heq. destruct (Nat.lt_ge_cases i c) as [Hlt | Hge]; [apply Hfnot; lia|].
    assert (i = c) by lia. subst i. exact (Hne Heq). }
  destruct HAPOST as [(Hcf & Hres0 & EHp3 & Eab3 & HL3)
                     | [(Hcf & Hres0 & _)
                     | (Hcf & Hdlo & Hdmod & Hnin & EHp3 & Eab3 & HRA3 & HSH3 & Hbl3 & HL3)]].
  - (* the chosen failure: the ledger is the arm's, g_fail_at saturates; no allocation was refused *)
    exists Lam2, peak2, SIZE_MAXZ, (jsA_ran en).
    rewrite Hcntmod in HL3.
    assert (Hres' : (res =? 0) = true) by (apply Z.eqb_eq; exact Hres0).
    rewrite Hres' in Hok3at. cbn [negb] in Hok3at.
    split; [exact HL3|].
    split.
    { split.
      { intros i Hi Heq. destruct (Nat.lt_ge_cases i c) as [Hlt | Hge].
        - exfalso. apply Hfnot. lia.
        - assert (i = c) by lia. subst i. exact Hok3at. }
      split; [left; reflexivity|].
      intros i Hi Hr _. exfalso. unfold prh_refused in Hr. apply andb_true_iff in Hr as [Hr1 Hr2].
      destruct (Nat.lt_ge_cases i c) as [Hlt | Hge].
      - rewrite (Hok3lt i Hlt) in Hr1. cbn [negb] in Hr1. discriminate Hr1.
      - assert (i = c) by lia. subst i. rewrite (proj2 (Z.eqb_eq _ _) Hcf) in Hr2. cbn [negb] in Hr2.
        discriminate Hr2. }
    split.
    { split; [intros _; reflexivity | intros Hno; exfalso; apply Hno; lia]. }
    split; [intros b m Hb; rewrite Eab3; exact Hb|].
    split; [intros a kk Ha; exact Ha|].
    split; [intros b m _ Hn; exact Hn|].
    split; [destruct HBLK as (other & Hb1 & Hb2); exists other; split; [exact Hb1 | rewrite Eab3; exact Hb2]|].
    left. split; [exact Hres0|]. split; [reflexivity|]. split; [exact Hcf|].
    split; [exact Hpeak2 | exact Hok3at].
  - (* a refusal: excluded by THE OUTCOME conjunct (no injected failure here, so the strdup granted) *)
    exfalso. exact (HGRANT Hcf Hres0).
  - (* granted: one new harness block *)
    assert (Hres' : (res =? 0) = false) by (apply Z.eqb_neq; lia).
    rewrite Hres' in Hok3at. cbn [negb] in Hok3at.
    assert (Hall : forall i, (i < Datatypes.S c)%nat -> nth i ok3 true = true).
    { intros i Hi. destruct (Nat.lt_ge_cases i c) as [Hlt | Hge]; [exact (Hok3lt i Hlt)|].
      assert (i = c) by lia. subst i. exact Hok3at. }
    exists ((res, jsA_klen en + 1) :: Lam2), (Z.max peak2 (Ledger.lsum Lam2 + (jsA_klen en + 1))),
      (jsA_fail en), (jsA_ran en).
    rewrite Hcntmod in HL3. unfold jsA_klen in HL3, Eab3, Hbl3 |- *.
    split; [exact HL3|].
    split.
    { split; [intros i Hi Heq; exfalso; exact (Hok0 Hcf i Hi Heq)|].
      split; [left; reflexivity|].
      intros i Hi Hr _. exfalso. unfold prh_refused in Hr. apply andb_true_iff in Hr as [Hr1 _].
      rewrite (Hall i Hi) in Hr1. cbn [negb] in Hr1. discriminate Hr1. }
    split.
    { split; [|intros _; reflexivity].
      intros Hin. exfalso. apply (Hok0 Hcf (Z.to_nat (jsA_fail en - jsA_cnt en)) ltac:(lia)). lia. }
    split; [intros b m Hb; rewrite Eab3; apply in_or_app; left; exact Hb|].
    split; [intros a kk Ha; right; exact Ha|].
    split.
    { intros b m Hb Hn Hc'. destruct Hc' as [Heq | Hc']; [|exact (Hn Hc')].
      injection Heq as E1 E2.
      apply (pjsdA_app_fresh ly S ly2 S2 Hp2 W2 mem2 md2 (res - cf_head)
        (Z.of_nat (length (jsA_kname en)) + 1 + cf_head) HAR2 Eab3 ltac:(lia)).
      replace (res - cf_head) with b by lia.
      replace (Z.of_nat (length (jsA_kname en)) + 1 + cf_head) with m by lia. exact Hb. }
    split.
    { destruct HBLK as (other & Hb1 & Hb2). exists other. split; [exact Hb1|].
      rewrite Eab3. unfold prhPj_hbl. cbn [map fst snd]. fold (prhPj_hbl Lam2).
      eapply Permutation_trans; [apply Permutation_sym, Permutation_cons_append|].
      apply perm_skip. exact Hb2. }
    right. split; [lia|]. split; [reflexivity|].
    split; [cbn [Ledger.lsum]; lia|].
    split; [exact Hall|].
    split; [exact (HBYT ltac:(lia))|].
    split; [lia|]. split; [exact Hdmod | exact Eab3]. }
destruct HARM as (Lam3 & peak3 & fail3 & ran3 & HLED3 & HOKS3 & HFA3 & EAB & ELAM & ENL & HBLK3 & HARMD).
(* ---- the data at the post-call state ---- *)
assert (HDATA3 : pjsA_data_c B dd en ly2 S2 Lam3 W2 mem2).
{ apply (pjsA_datac_kept B ARx LAWS VIS dd en ly S Hp W mem mdc
    Lam2 peak2 (jsA_cnt en + Z.of_nat c) (jsA_fail en) (jsA_ran en) (jsA_most en) (jsA_own en) STK_fuzz_strdup (jsA_sp1 en) []
    ly2 S2 Hp2 W2 mem2 md2 k1 Lam3 peak3 (jsA_cnt en + Z.of_nat (Datatypes.S c)) fail3 ran3 (jsA_most en) (jsA_own en)
    HARmc HJc HLED HLED3).
  - intros x Hx. exfalso. exact (inFP_nil x Hx).
  - exact sink_closed_nil.
  - intros x _ Hx. exact (inFP_nil x Hx).
  - lia.
  - exact Hdhi.
  - intros a Ha. apply HPRW. unfold jsA_sp1, jsA_sp0, PJSA_FR in *. lia.
  - exact HWSP.
  - intros a kk p _ Hin _ _. exact (ELAM a kk Hin).
  - intros b m p _ Hbm HnL _ _. split; [exact (EAB b m Hbm) | exact (ENL b m Hbm HnL)].
  - intros a kk Hin _ _. exact (ELAM a kk Hin).
  - exact HROOM2.
  - exact HDATAC. }
pose proof HDATA3 as (_ & HPL3 & HSLOTW3 & HCSTR3 & HKEPT3).
assert (HSUB3 : forall a kk, In (a, kk) Do -> In (a, kk) Lam3).
{ intros a kk Hin. apply ELAM. eapply Permutation_in; [exact (Permutation_sym HpLam2)|].
  apply in_or_app. left. exact Hin. }
assert (HSUBW3 : forall a kk, In (a, kk) (jsA_Dw en) -> In (a, kk) Lam3).
{ intros a kk Hin. apply ELAM. eapply Permutation_in; [exact (Permutation_sym HpLam2)|].
  apply in_or_app. right. apply in_or_app. left. exact Hin. }
assert (HAGRo : forall x, jsA_o en <= x < jsA_o en + 56 ->
  aview SEGS (w_H W2) mem2 x = aview SEGS (w_H W) mem x).
{ intros x Hx. destruct HPLo as (_ & Hat & _).
  exact (pjsA_at_bytes B ARx ly S Hp W mem mdc STK_fuzz_strdup (jsA_sp1 en) [] ly2 S2 Hp2 W2 mem2 md2 k1
    Lam2 peak2 (jsA_cnt en + Z.of_nat c) (jsA_fail en) (jsA_ran en) (jsA_most en) (jsA_own en) (jsA_regs en) (jsA_d en) (jsA_o en)
    HJc HLED ltac:(unfold jsA_sp1, jsA_sp0, PJSA_FR; lia) ltac:(unfold jsA_sp0 in *; lia)
    (fun b m Hbm _ _ => EAB b m Hbm) Hat x Hx (inFP_nil x)). }
assert (HHDR3 : pj_hdrR SEGS (mrestrict (w_H W2) mem2) (jsA_o en) 6 (jsA_num en) (jsA_str en) kids2 keys2
  (jsA_n en) cap2v).
{ destruct HPL3 as (_ & _ & Hrw3 & _).
  apply (pj_hdrR_frame SEGS (mrestrict (w_H W) mem)); [exact HHDRo|].
  apply (pjsA_agree W W2 mem mem2); [|intros x Hx _; exact (proj2 Hrw3 x Hx)].
  intros x Hx. exact (HAGRo x Hx). }
assert (HNODE3 : pj_nodeR SEGS (mrestrict (w_H W2) mem2) (prh_lin Lam3) (jsA_o en)
  (PjTree.JObj (jsA_ms en)) Do).
{ destruct HPL3 as (_ & _ & Hrw3 & _). destruct HPLo as (_ & Hat & _).
  apply (pjsA_tree_kept B ARx LAWS ly S Hp W mem mdc Lam2 peak2 (jsA_cnt en + Z.of_nat c) (jsA_fail en)
    (jsA_ran en) (jsA_most en) (jsA_own en) STK_fuzz_strdup (jsA_sp1 en) [] ly2 S2 Hp2 W2 mem2 md2 k1
    Lam3 peak3 (jsA_cnt en + Z.of_nat (Datatypes.S c)) fail3 ran3 (jsA_most en) (jsA_own en)
    (jsA_regs en) (jsA_d en) (jsA_o en) (PjTree.JObj (jsA_ms en)) Do
    HJc HLED HLED3 ltac:(unfold jsA_sp1, jsA_sp0, PJSA_FR; lia) ltac:(unfold jsA_sp0 in *; lia)
    (fun b m Hbm _ _ => EAB b m Hbm) Hat Hrw3).
  - exact HSUB3.
  - intros x _ Hx. exact (inFP_nil x Hx).
  - exact HNODEo. }
assert (HNODEW3 : pj_nodeR SEGS (mrestrict (w_H W2) mem2) (prh_lin Lam3) (jsA_w en) (jsA_tv en) (jsA_Dw en)).
{ destruct HSLOTW3 as (_ & _ & Hrw3 & _). destruct HSLOTW as (_ & Hat & _).
  apply (pjsA_tree_kept B ARx LAWS ly S Hp W mem mdc Lam2 peak2 (jsA_cnt en + Z.of_nat c) (jsA_fail en)
    (jsA_ran en) (jsA_most en) (jsA_own en) STK_fuzz_strdup (jsA_sp1 en) [] ly2 S2 Hp2 W2 mem2 md2 k1
    Lam3 peak3 (jsA_cnt en + Z.of_nat (Datatypes.S c)) fail3 ran3 (jsA_most en) (jsA_own en)
    (jsA_regs en) (jsA_d en) (jsA_w en) (jsA_tv en) (jsA_Dw en)
    HJc HLED HLED3 ltac:(unfold jsA_sp1, jsA_sp0, PJSA_FR; lia) ltac:(unfold jsA_sp0 in *; lia)
    (fun b m Hbm _ _ => EAB b m Hbm) Hat Hrw3).
  - exact HSUBW3.
  - intros x _ Hx. exact (inFP_nil x Hx).
  - exact HNODEW. }
assert (HWPRES2 : forall a, jsA_w en <= a < jsA_w en + 56 ->
  apresent (w_H W2) mem2 a /\ ~ in_img SEGS a).
{ intros a Ha. destruct HSLOTW3 as (_ & Hat & _).
  destruct Hat as [(a0 & kk & Hin & Ha1 & Hk1) | [(b & m & Hin & _ & Hb & Hm) |
    [(cid & pos & Hin & Hf & Hfm) | (Hw1 & Hw2)]]].
  - destruct (prh_ledger_hblock B ly2 S2 Hp2 W2 mem2 Lam3 peak3
      (jsA_cnt en + Z.of_nat (Datatypes.S c)) fail3 ran3 a0 kk (jsA_most en) (jsA_own en) HLED3 Hin) as (Hk0 & Hab & _).
    pose proof (pjsA_req (kk + @cf_head cp) ltac:(lia)) as (Rq & _).
    destruct (alx_blocks SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 _ _ HAR2 Hab) as (_ & _ & _ & _ & Hbpo & _).
    split; [exact (proj1 (Hbpo a ltac:(lia)))|].
    exact (blk_img_x SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 _ _ a HAR2 Hab ltac:(lia)).
  - pose proof (pjsA_req m ltac:(lia)) as (Rm & _).
    destruct (alx_blocks SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 b m HAR2 Hin) as (_ & _ & _ & _ & Hbpo & _).
    split; [exact (proj1 (Hbpo a ltac:(lia)))|].
    exact (blk_img_x SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 b m a HAR2 Hin ltac:(lia)).
  - destruct (alx_frames SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 cid pos HAR2 Hin) as (_ & _ & Hfpo & _).
    split; [exact (proj1 (Hfpo a ltac:(lia)))|].
    exact (frm_img_x SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 cid pos a HAR2 Hin ltac:(lia)).
  - exfalso. unfold jsA_sp0 in *. lia. }
(* ---- the object's ordered free list and val's entry agreement, across the call ---- *)
assert (HFO3 : forall nn, (PjTree.depth (PjTree.JObj (jsA_ms en)) <= nn)%nat ->
  exists F, pj_foR SEGS (mrestrict (w_H W2) mem2) (prh_lin Lam3) nn (jsA_o en) Do F /\
    map (fun b => snd b + PresetReqAt.HEAD) F =
      PjFoMember.pfm_slots PresetReqAtNoMiss.kblk (jsA_ms en) ++
      PresetReqAt.arrz true (PresetReqAt.ncap (Datatypes.S (length (jsA_ms en))))).
{ intros nn Hnn. destruct (HFO nn Hnn) as (F & HF & HmF). exists F. split; [|exact HmF].
  destruct HPL3 as (_ & _ & Hrw3 & _). destruct HPLo as (_ & Hat & _).
  apply (pjsdA_fo_kept ly S Hp W mem mdc Lam2 peak2 (jsA_cnt en + Z.of_nat c) (jsA_fail en)
    (jsA_ran en) (jsA_most en) (jsA_own en) STK_fuzz_strdup (jsA_sp1 en) [] ly2 S2 Hp2 W2 mem2 md2 k1
    Lam3 peak3 (jsA_cnt en + Z.of_nat (Datatypes.S c)) fail3 ran3 (jsA_most en) (jsA_own en)
    (jsA_regs en) (jsA_d en) (jsA_o en) nn Do F
    HJc HLED HLED3 ltac:(unfold jsA_sp1, jsA_sp0, PJSA_FR; lia) ltac:(unfold jsA_sp0 in *; lia)
    (fun b m Hbm _ _ => EAB b m Hbm) Hat Hrw3 HSUB3 (fun x _ Hx => inFP_nil x Hx) HF). }
assert (HAGRW3 : pj_agreeR SEGS (mrestrict (w_H (jsA_W en)) (jsA_mem en)) (mrestrict (w_H W2) mem2)
  (pj_footR (jsA_w en) (jsA_Dw en))).
{ apply (pjsA_agree_trans _ _ _ _ HAGRW).
  destruct HSLOTW3 as (_ & _ & Hrw3 & _). destruct HSLOTW as (_ & Hat & _).
  apply (pjsdA_foot_agree ly S Hp W mem mdc Lam2 peak2 (jsA_cnt en + Z.of_nat c) (jsA_fail en)
    (jsA_ran en) (jsA_most en) (jsA_own en) STK_fuzz_strdup (jsA_sp1 en) [] ly2 S2 Hp2 W2 mem2 md2 k1
    Lam3 peak3 (jsA_cnt en + Z.of_nat (Datatypes.S c)) fail3 ran3 (jsA_most en) (jsA_own en)
    (jsA_regs en) (jsA_d en) (jsA_w en) (jsA_Dw en)
    HJc HLED HLED3 ltac:(unfold jsA_sp1, jsA_sp0, PJSA_FR; lia) ltac:(unfold jsA_sp0 in *; lia)
    (fun b m Hbm _ _ => EAB b m Hbm) Hat Hrw3); [| exact HSUBW3 | exact (fun x _ Hx => inFP_nil x Hx)].
  intros a kk Hin. eapply Permutation_in; [exact (Permutation_sym HpLam2)|].
  apply in_or_app. right. apply in_or_app. left. exact Hin. }
(* ---- the cut ---- *)
apply (YSRrG.SRr'_ret SEGS YGcfRehidePost.RZ_cf).
exists ly2, S2, Hp2, regs2, mem2, md2, (k + k1).
split; [reflexivity|].
exists res, Lam2, Lam3, peak3, fail3, ran3, c, ok3, Do, Lr, Dold, Dnew, Dr,
  (jsA_num en), (jsA_str en), kids2, keys2, cap2v.
unfold pjsdA_Cp.
split.
{ (* the invariant *)
  split; [exact HJ2'|].
  split; [exact KW|].
  split; [rewrite (pjsA_pres_sp regsc regs2 HP2); exact HSPC|].
  split; [exact KRA|]. split; [exact KS0|]. split; [exact KS1|]. split; [exact KS2|]. split; [exact KS3|].
  split; [exact KS4|].
  split; [rewrite (pjsA_pres regsc regs2 (8%bv : bv 5) HP2 ltac:(pjsA_cs));
          rewrite Eregsc, !getr_other by pjsA_regne; exact H8|].
  split; [rewrite (pjsA_pres regsc regs2 (18%bv : bv 5) HP2 ltac:(pjsA_cs));
          rewrite Eregsc, !getr_other by pjsA_regne; exact H18|].
  split; [rewrite (pjsA_pres regsc regs2 (20%bv : bv 5) HP2 ltac:(pjsA_cs));
          rewrite Eregsc, !getr_other by pjsA_regne; exact H20|].
  split.
  { intros r Hr.
    assert (Hcs : acallee_saved (bv_unsigned r)).
    { unfold PJSA_KEPT in Hr. cbn [In] in Hr. repeat (destruct Hr as [<- | Hr]; [pjsA_cs |]). destruct Hr. }
    rewrite (pjsA_pres regsc regs2 r HP2 Hcs). rewrite Eregsc, !getr_other by pjsA_kept_ne.
    exact (HKEPT r Hr). }
  split; [exact KPR|]. split; [exact KROD|].
  (* the memnorm keep: the cut's, then fuzz_strdup's m-form post *)
  intros HMN0. exact (HMN2 (HMN HMN0)). }
split; [exact HROOM2|].
split.
{ rewrite (pjsA_pres regsc regs2 (9%bv : bv 5) HP2 ltac:(pjsA_cs));
  rewrite Eregsc, !getr_other by pjsA_regne; exact H9. }
split; [exact Hres|].
split; [exact HLED3|].
split; [exact HOKS3|].
split; [exact HFA3|].
split; [exact Hok3lt|].
split; [exact HNI|].
split; [exact HpLam|].
split; [exact HpLam2|].
split; [exact HBLK3|].
split; [exact HpD|].
split; [exact HpDo|].
split; [exact HoD|]. split; [exact HoDo|].
split; [exact HNEW|].
split; [exact HCASE|].
split; [exact Hncap2|].
split; [exact HNODE3|].
split; [exact HHDR3|].
split.
{ destruct HSLOTS as (Hty & Hnc & Hz & Hpos). split; [exact Hty|]. split; [exact Hnc|].
  split; [exact Hz|]. intros Hc'. destruct (Hpos Hc') as (Hk' & Hy').
  split; [exact (ELAM kids2 (56 * cap2v) Hk')|].
  intros Hty6. exact (ELAM keys2 (8 * cap2v) (Hy' Hty6)). }
split; [exact HNODEW3|].
split; [exact HDATA3|].
split.
{ intros x Hx. apply (pjsdA_w_apart B ARx LAWS CTX0 dd en ly S Hp W regs mem md k Lam2 peak2
    (jsA_cnt en + Z.of_nat c) (jsA_fail en) (jsA_ran en) (jsA_most en) (jsA_own en) Do Lr Dold Dnew Dr
    HPRE0 HINV HLED HpLam HpLam2 HBLK HpD HpDo HNEW HSLOTW HNODEW x Hx). }
split; [exact HWCEIL|].
split; [exact HWPRES2|].
split; [exact Hcapm|]. split; [exact Hcap2m|]. split; [exact HFO3|]. split; [exact HAGRW3|].
destruct HARMD as [(Hr0 & EL3 & Ecf & EP3 & Hokf) | (Hrn & EL3 & EP3 & Hokall3 & HBYT3 & Hdlo & Hdmod & Eab3)].
- (* a NULL keeps the position: the class-24 bound holds there (counts_of_room_pos_rl) *)
  left. split; [exact Hr0|]. split; [exact EL3|]. split; [exact Ecf|]. split; [exact EP3|]. split; [exact Hokf|].
  unfold pjsA_PB.
  destruct (HPZ Hr0 ReaderRes.jr_strtod (jsA_x en) (jsA_os en) (jsA_i en + c)%nat (jsA_H0 en) hist HPOS eq_refl)
    as (hist' & HPOS').
  split; [exact (proj2 (PresetRoomCounts.counts_of_room_pos_rl _ _ _ _ _ _ _ HPOS'))|].
  (* pj_free's hull budget: what fuzz_strdup's leaves after its use *)
  exact (PresetHullBudget.hull_budget_used S S2 _ HHBS HUSEDS).
- right. split; [exact Hrn|]. split; [exact EL3|]. split; [exact EP3|].
  split; [exact Hokall3|]. split; [exact HBYT3|].
  split; [exact Hdlo|]. split; [exact Hdmod|].
  assert (HFRESH : ~ In (res - cf_head, jsA_klen en + 1 + cf_head) (ablocks B ly S)).
  { apply (pjsdA_app_fresh ly S ly2 S2 Hp2 W2 mem2 md2 _ _ HAR2 Eab3). unfold jsA_klen. lia. }
  assert (HNEWIN : In (res - cf_head, jsA_klen en + 1 + cf_head) (ablocks B ly2 S2))
    by (rewrite Eab3; unfold jsA_klen; apply in_or_app; right; left; reflexivity).
  assert (Hkl0 : 0 <= jsA_klen en) by (unfold jsA_klen; apply Nat2Z.is_nonneg).
  assert (HRQ : req_size (jsA_klen en + 1 + cf_head) = jsA_klen en + 1 + cf_head).
  { assert (Hq0 : 0 <= jsA_klen en + 1 + cf_head) by lia.
    destruct (pjsA_req _ Hq0) as (_ & _ & Hq). apply Hq. lia. }
  split.
  + intros x Hx Hd'. destruct HPLo as (_ & Hat & _).
    apply (pjsdA_at_fresh_core B ARx LAWS ly S Hp W mem mdc ly2 S2 Hp2 W2 mem2 md2
      Lam2 peak2 (jsA_cnt en + Z.of_nat c) (jsA_fail en) (jsA_ran en) (jsA_most en) (jsA_own en) (jsA_regs en) (jsA_d en)
      (jsA_o en) 56 (res - cf_head) (jsA_klen en + 1 + cf_head)
      HARmc HAR2 HLED Hat ltac:(lia) ltac:(unfold jsA_sp0 in *; lia) HFRSc Hlyc EAB HNEWIN HFRESH x Hx).
    rewrite HRQ. lia.
  + split.
    * intros x Hx Hd'. destruct HSLOTW as (_ & Hat & _).
      apply (pjsdA_at_fresh_core B ARx LAWS ly S Hp W mem mdc ly2 S2 Hp2 W2 mem2 md2
        Lam2 peak2 (jsA_cnt en + Z.of_nat c) (jsA_fail en) (jsA_ran en) (jsA_most en) (jsA_own en) (jsA_regs en) (jsA_d en)
        (jsA_w en) 56 (res - cf_head) (jsA_klen en + 1 + cf_head)
        HARmc HAR2 HLED Hat ltac:(lia) ltac:(unfold jsA_sp0 in *; lia) HFRSc Hlyc EAB HNEWIN HFRESH x Hx).
      rewrite HRQ. lia.
    * (* the run's event at jsA_i + c is the strdup's own HMal (at cf_head = HEAD, HRD above), so the position
         advances past the call's last event *)
      destruct (HPNZ Hrn _ _ _ _ _ _ HPOS HRD) as (hist' & HPOS'). cbn [length] in HPOS'.
      exists hist'. unfold pjsA_evs. rewrite Hlen.
      replace (jsA_i en + Datatypes.S c)%nat with (jsA_i en + c + 1)%nat by lia.
      exact HPOS'.
Qed.

End m.
