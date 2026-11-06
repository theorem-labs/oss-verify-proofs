(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: the GLUE facts of pj_parse's image-A' walk (fuzz_preset asan, A' 0x85e20): the pure
   Props pjp_g_* / pjp_glue of lib/A/Prog/PjParseA_defs.v, and the allocator-trace universe fact the parse_value call
   needs, from pj_parse's closure. RELOCATED from a Theorem Labs lane's image-B' walk 5134b312d551 lib/B/Prog/pj_parse_glue.v:
   the module names and the PrhImg instance (prh_img_B -> prh_img_A) only; every proof step is the B' one.
   proves no function (kind: glue lemma). Pure facts over the grammar (Spec/PjGrammar.v), the reader's tree predicates
   (lib/A/PRH_Reader.v) and one universe membership at image A''s generated values (lib/A/PRH_Img.v).
   - pjp_g_fd_mono / pjp_g_node_fd: transcribed from preset's plain lib/Prog/PjStruct.v:412-572 (pf_items_mono,
     pj_fshape_mono, pj_fd_succ, pj_fd_mono, pj_items_pf, pj_mems_pf, pj_node_fd) over PRH_Reader's restated
     predicates; no plain lemma is cited.
   - pjp_g_rest: the rest of an accepted value is a suffix of the text, transcribed from plain lib/Prog/ReaderKB.v:27-145
     (its rk_suf lemmas) at ANY strtod model (the plain one is stated at jr_strtod only).
   - pjp_g_depth / run / fail_in / norefuse / calls: PjGrammar's jr_value_depth, jr_run_eq, G7_1, G7_1_calls, G7_2,
     vspec_jr_value, ok_upto_dec.
  - pjp_g_univ: the kit's prh_univ_closure_malloc / prh_univ_closure_realloc (walkkit a3bdeca3920: rd_pre's trace
    premises are the pc0-filtered prh_trace pc0 r [], parse text blob dcff6bfa302a). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07 YI16.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YG0p YCbqG FCiface YGcallMx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YGcfRoomKeep YG0dcf YGcfRoomPre.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK0o YK06.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar PjRoundTrip.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_Charge PRH_FnReader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_FnPj PRH_FnParse.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Img0 Listing_prog PAImg_prog PRH_Img.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import PjParseA_defs.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require PjpTree.
Import ListNotations.
Local Open Scope Z_scope.
#[local] Existing Instance prh_img_A.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* ---- the tree: a represented tree is freeable to its depth, and freeable is monotone in the depth: module
   PjpTree, in the image-free lib/Reusable/PjpTree.v (Required above, not imported; its names are PjpTree.pjg_...) *)

(* ---- the grammar: the rest of an accepted value is a suffix of the text (any strtod model) ---- *)
Module PjpSuf.
Import PjGrammar.
Section suf.
Variable sm : list Z -> Z * Z.

Definition suf (r x : list Z) : Prop := exists u, x = u ++ r.

Lemma suf_refl : forall x, suf x x.
Proof. intros x. exists []. reflexivity. Qed.

Lemma suf_trans : forall r y x, suf r y -> suf y x -> suf r x.
Proof. intros r y x (u & Hu) (v & Hv). exists (v ++ u). rewrite Hv, Hu. apply app_assoc. Qed.

Lemma suf_skipn : forall n x, suf (skipn n x) x.
Proof. intros n x. exists (firstn n x). symmetry. apply firstn_skipn. Qed.

Lemma suf_skip : forall x, suf (skip x) x.
Proof.
  induction x as [|b r IH]; [apply suf_refl|]. cbn [skip]. destruct (ws b).
  - destruct IH as (u & Hu). exists (b :: u). cbn [app]. f_equal. exact Hu.
  - apply suf_refl.
Qed.

Lemma suf_tl : forall x, suf (List.tl x) x.
Proof. intros [|b r]; [apply suf_refl|]. exists [b]. reflexivity. Qed.

Lemma suf_cons : forall b r y, suf (b :: r) y -> suf r y.
Proof. intros b r y (u & Hu). exists (u ++ [b]). rewrite Hu, <- app_assoc. reflexivity. Qed.

Lemma suf_string : forall z ok s r t ok', jr_string z ok = (Some (s, r), t, ok') -> suf r z.
Proof.
  intros z ok s r t ok' H. pose proof (jr_string_spec z ok) as S. rewrite H in S.
  destruct S as (q & Hq & Hd & _). destruct (G1_4 z s r Hd) as (q' & _ & Hr & _). rewrite Hr. apply suf_skipn.
Qed.

Lemma suf_lit : forall w v x ok u r t ok', lit w v x ok = (Some (u, r), t, ok') -> suf r x.
Proof.
  intros w v x ok u r t ok' H. unfold lit in H.
  destruct (prefixb w x); [|unfold jrefuse in H; discriminate].
  unfold jret in H. injection H as E1 E2 E3 E4. rewrite <- E2. apply suf_skipn.
Qed.

Lemma suf_number : forall x ok u r t ok', jr_number sm x ok = (Some (u, r), t, ok') -> suf r x.
Proof.
  intros x ok u r t ok' H. unfold jr_number in H. cbv zeta in H.
  destruct (skipn _ x) as [|c z] eqn:E; cbv beta iota in H; [unfold jrefuse in H; discriminate|].
  destruct (negb (digit c)); cbv beta iota in H; [unfold jrefuse in H; discriminate|].
  destruct ((c =? 48) && _); cbv beta iota in H; [unfold jrefuse in H; discriminate|].
  destruct (span numch z) as [a r'] eqn:SP. cbv beta iota in H.
  apply jbind_some in H as (a0 & t1 & ok1 & t2 & _ & H & _).
  destruct (whole _ _); [|unfold jrefuse in H; discriminate].
  unfold jret in H. injection H as E1 E2 E3 E4. subst r.
  apply (suf_trans r' (c :: z) x).
  - apply span_app in SP. exists (c :: a). rewrite SP. reflexivity.
  - rewrite <- E. apply suf_skipn.
Qed.

Lemma suf_name : forall o y ok nm y1 tn ok2, jr_name o y ok = (Some (nm, y1), tn, ok2) -> suf y1 y.
Proof.
  intros o y ok nm y1 tn ok2 H. unfold jr_name in H. destruct o.
  - destruct (skip y) as [|b z] eqn:E; [unfold jrefuse in H; discriminate|].
    destruct (b =? 34); cbv beta iota in H; [|unfold jrefuse in H; discriminate].
    apply jbind_some in H as ([name r] & t1 & ok1 & t2 & Hs & H & _). cbv beta iota in H.
    destruct (skip r) as [|c r1] eqn:E2; [unfold jbind, jfree, jrefuse in H; cbn in H; discriminate H|].
    destruct (c =? 58); [|unfold jbind, jfree, jrefuse in H; cbn in H; discriminate H].
    unfold jret in H. injection H as F1 F2 F3 F4. subst y1.
    apply (suf_trans r1 r y); [apply (suf_cons c); rewrite <- E2; apply suf_skip|].
    apply (suf_trans r z y); [exact (suf_string z ok name r t1 ok1 Hs)|].
    apply (suf_cons b). rewrite <- E. apply suf_skip.
  - unfold jret in H. injection H as F1 F2 F3 F4. subst y1. apply suf_refl.
Qed.

Lemma suf_cont : forall loop d o x ok t r tr ok',
  (forall o' n cap acc y ok1 t1 r1 tr1 ok2, loop (S d) o' n cap acc y ok1 = (Some (t1, r1), tr1, ok2) -> suf r1 y) ->
  jr_cont loop d o x ok = (Some (t, r), tr, ok') -> suf r x.
Proof.
  intros loop d o x ok t r tr ok' HL H. unfold jr_cont in H.
  destruct (Nat.ltb MAXD (S d)); cbv beta iota in H; [unfold jrefuse in H; discriminate|].
  cbv zeta in H.
  destruct (skip (List.tl x)) as [|c r0] eqn:E; cbv beta iota in H.
  - pose proof (suf_trans _ _ _ (suf_skip (List.tl x)) (suf_tl x)) as SY. rewrite E in SY.
    exact (suf_trans _ _ _ (HL _ _ _ _ _ _ _ _ _ _ H) SY).
  - pose proof (suf_trans _ _ _ (suf_skip (List.tl x)) (suf_tl x)) as SY. rewrite E in SY.
    destruct (c =? closer o); cbv beta iota in H.
    + unfold jret in H. injection H as F1 F2 F3 F4. subst r. exact (suf_cons c _ _ SY).
    + exact (suf_trans _ _ _ (HL _ _ _ _ _ _ _ _ _ _ H) SY).
Qed.

Lemma suf_fuel : forall f,
  (forall d x ok t r tr ok', jrv sm f d x ok = (Some (t, r), tr, ok') -> suf r x) /\
  (forall d o n cap acc y ok t r tr ok', jrl sm f d o n cap acc y ok = (Some (t, r), tr, ok') -> suf r y).
Proof.
  induction f as [|f [IHv IHl]].
  - split; intros; cbn [jrv jrl] in *; unfold jrefuse in *; discriminate.
  - split.
    + intros d x ok t r tr ok' H. cbn [jrv] in H.
      destruct (skip x) as [|b y] eqn:SX; cbv beta iota in H; [unfold jrefuse in H; discriminate|].
      assert (SY : suf (b :: y) x) by (rewrite <- SX; apply suf_skip).
      apply (suf_trans r (b :: y) x); [|exact SY].
      destruct (b =? 123); cbv beta iota in H.
      { exact (suf_cont _ _ _ _ _ _ _ _ _ (fun o' n cap acc y0 ok1 t1 r1 tr1 ok2 => IHl (S d) o' n cap acc y0 ok1 t1 r1 tr1 ok2) H). }
      destruct (b =? 91); cbv beta iota in H.
      { exact (suf_cont _ _ _ _ _ _ _ _ _ (fun o' n cap acc y0 ok1 t1 r1 tr1 ok2 => IHl (S d) o' n cap acc y0 ok1 t1 r1 tr1 ok2) H). }
      destruct (b =? 34); cbv beta iota in H.
      { apply jbind_some in H as ([s r1] & t1 & ok1 & t2 & Hs & H & _). cbv beta iota in H.
        unfold jret in H. injection H as F1 F2 F3 F4. subst r.
        apply (suf_trans r1 y); [exact (suf_string y ok s r1 t1 ok1 Hs)|]. exists [b]. reflexivity. }
      destruct (b =? 116); cbv beta iota in H; [exact (suf_lit _ _ _ _ _ _ _ _ H)|].
      destruct (b =? 102); cbv beta iota in H; [exact (suf_lit _ _ _ _ _ _ _ _ H)|].
      destruct (b =? 110); cbv beta iota in H; [exact (suf_lit _ _ _ _ _ _ _ _ H)|].
      exact (suf_number _ _ _ _ _ _ H).
    + intros d o n cap acc y ok t r tr ok' H. cbn [jrl] in H.
      apply jbind_some in H as (cap1 & tg & ok1 & t2 & _ & H & _). cbv beta in H.
      apply jbind_some in H as ([nm y1] & tn & ok2 & t3 & Hn & H & _). cbv beta iota in H.
      apply jbind_some in H as ([v r0] & tv & ok3 & t4 & Ev & H & _). cbv beta iota in H.
      pose proof (suf_trans _ _ _ (IHv d y1 ok2 v r0 tv ok3 Ev) (suf_name o y ok1 nm y1 tn ok2 Hn)) as S0.
      destruct (skip r0) as [|c r1] eqn:E; cbv beta iota in H; [unfold jrefuse in H; discriminate|].
      assert (S1 : suf r1 y).
      { apply (suf_trans r1 r0 y); [apply (suf_cons c); rewrite <- E; apply suf_skip | exact S0]. }
      destruct (c =? 44); cbv beta iota in H.
      { exact (suf_trans _ _ _ (IHl d o (S n) cap1 ((nm, v) :: acc) r1 ok3 t r t4 ok' H) S1). }
      destruct (c =? closer o); cbv beta iota in H; [|unfold jrefuse in H; discriminate].
      unfold jret in H. injection H as F1 F2 F3 F4. subst r. exact S1.
Qed.

Lemma suf_jr_value : forall d x ok t r tr ok', jr_value sm d x ok = (Some (t, r), tr, ok') -> suf r x.
Proof. intros d x ok t r tr ok' H. unfold jr_value in H. exact (proj1 (suf_fuel _) d x ok t r tr ok' H). Qed.
End suf.
End PjpSuf.

(* ---- the ten pure Props ---- *)
Lemma pjg_fd_mono : pjp_g_fd_mono.
Proof. intros segs m lblk n n' p D Hle H. exact (PjpTree.pjg_fd_mono segs m lblk n n' p D Hle H). Qed.

Lemma pjg_node_fd : pjp_g_node_fd.
Proof.
  intros segs m lblk t p D n H Hd.
  exact (PjpTree.pjg_fd_mono segs m lblk (PjTree.depth t) n p D Hd (PjpTree.pjg_node_fd segs t m lblk p D H)).
Qed.

Lemma pjg_depth : pjp_g_depth.
Proof.
  intros tl ok t r tr okr H. pose proof (PjGrammar.jr_value_depth ReaderRes.jr_strtod 0 tl ok t r tr okr H) as Hd. lia.
Qed.

Lemma pjg_run_of : forall tl ok res tr okr, PjGrammar.jr_value ReaderRes.jr_strtod 0 tl ok = (res, tr, okr) ->
  PjGrammar.jr_run ReaderRes.jr_strtod tl ok = (PjGrammar.post res, tr).
Proof. intros tl ok res tr okr H. rewrite PjGrammar.jr_run_eq, H. reflexivity. Qed.

(* parse_value's all-granted trace at d = 0 over pj_parse's text IS pj_parse's (PRH_Charge.prhPv_gtrace,
   PRH_FnPj.prhPj_ptrace; PjGrammar.jr_run_eq): the refusal peaks of the two texts read the same list *)
Lemma pjg_gtrace : forall tl, prhPv_gtrace 0 tl = prhPj_ptrace tl.
Proof.
  intros tl. unfold prhPv_gtrace, prhPj_ptrace, PjGrammar.jr_run.
  destruct (PjGrammar.jr_value prh_jr_strtod 0%nat tl []) as [[[[t r]|] tr] okr]; reflexivity.
Qed.

Lemma pjg_run : pjp_g_run.
Proof. exact pjg_run_of. Qed.

Lemma pjg_fail_in : pjp_g_fail_in.
Proof.
  intros tl ok res tr okr cnt fail ns most ran ran' H (HO & _ & _) HF.
  pose proof (pjg_run_of tl ok res tr okr H) as E.
  destruct (PjGrammar.ok_upto_dec ok (PjGrammar.ncalls ReaderRes.jr_strtod tl)) as [Hu | (j & Hj & Hf & Hu)].
  - exfalso. pose proof (PjGrammar.G7_1_calls ReaderRes.jr_strtod tl ok Hu) as HC. rewrite E in HC. cbn [snd] in HC.
    specialize (HO (Z.to_nat (fail - cnt)) ltac:(lia) ltac:(lia)).
    rewrite (Hu (Z.to_nat (fail - cnt)) ltac:(lia)) in HO. discriminate HO.
  - destruct (PjGrammar.G7_2 ReaderRes.jr_strtod tl ok j Hj Hf Hu) as (G & _). rewrite E in G. exact G.
Qed.

Lemma pjg_norefuse : pjp_g_norefuse.
Proof.
  intros tl ok res tr okr cnt fail H HF HN.
  pose proof (pjg_run_of tl ok res tr okr H) as E.
  destruct (PjGrammar.ok_upto_dec ok (PjGrammar.ncalls ReaderRes.jr_strtod tl)) as [Hu | (j & Hj & Hf & Hu)].
  - pose proof (PjGrammar.G7_1 ReaderRes.jr_strtod tl ok Hu) as G. rewrite E in G. injection G as G1 G2.
    split; [exact G1|]. rewrite G2. reflexivity.
  - exfalso. destruct (PjGrammar.G7_2 ReaderRes.jr_strtod tl ok j Hj Hf Hu) as (_ & G). rewrite E in G. cbn [snd] in G.
    specialize (HN j ltac:(lia) Hf). lia.
Qed.

Lemma pjg_calls : pjp_g_calls.
Proof.
  intros tl ok res tr okr H. pose proof (PjGrammar.vspec_jr_value ReaderRes.jr_strtod 0 tl ok) as V. rewrite H in V.
  destruct V as (V & _). cbn [fst snd] in V. lia.
Qed.

Lemma pjg_fail_after : pjp_g_fail_after.
Proof. intros cnt fail k f'. unfold fail_afterR, ReaderRes.fail_after, SIZE_MAXZ. split; intros X; exact X. Qed.

Lemma pjg_rest : pjp_g_rest.
Proof.
  intros tl ok t r tr okr t0 H.
  destruct (PjpSuf.suf_jr_value ReaderRes.jr_strtod 0 tl ok t r tr okr H) as (u & Hu).
  assert (L : length tl = (length u + length r)%nat) by (rewrite Hu, length_app; reflexivity).
  split; [lia|].
  unfold rest_atR.
  replace (Z.to_nat (t0 + Z.of_nat (length tl) - Z.of_nat (length r) - t0)) with (length u) by lia.
  rewrite Hu, skipn_app, skipn_all, Nat.sub_diag. reflexivity.
Qed.

Lemma pjg_ab_hbl {cp : CfParams} : @pjp_g_ab_hbl cp.
Proof. intros D. reflexivity. Qed.

Theorem pjp_glue_holds {cp : CfParams} : @pjp_glue cp.
Proof.
  split; [exact pjg_fd_mono|]. split; [exact pjg_node_fd|]. split; [exact pjg_depth|]. split; [exact pjg_run|].
  split; [exact pjg_fail_in|]. split; [exact pjg_norefuse|]. split; [exact pjg_calls|].
  split; [exact pjg_fail_after|]. split; [exact pjg_rest|]. exact (@pjg_ab_hbl cp).
Qed.

(* ---- the universe fact (Section variables as PjParseA_defs.v Section d) ---- *)
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Context {SK : YI16.sink_head}.
Variable B : asyms.

(* The kit's prh_univ_closure_malloc / prh_univ_closure_realloc (walkkit a3bdeca3920, the pc0-filtered traces); the two
   site lists are non-empty at prh_img_A (vm_compute over the generated PRH_Img.v values) *)
Theorem pjp_g_univ_holds : pjp_g_univ B.
Proof.
  intros CTX0 HC.
  destruct (prh_univ_closure_realloc B CTX0 HC ltac:(vm_compute; discriminate)) as [R1 R2].
  split; [|split; [exact R1 | exact R2]].
  apply (prh_univ_closure_malloc B CTX0 HC). vm_compute. discriminate.
Qed.
End d.

(* Print Assumptions, run once (zfb v5, log, the internal file zfb-20261029T081625Z.log): pjp_glue_holds shows only Corelib's
   PrimInt63 / PrimString primitives; pjp_g_univ_holds is closed under the global context.
Print Assumptions pjp_glue_holds.
Print Assumptions pjp_g_univ_holds. *)
