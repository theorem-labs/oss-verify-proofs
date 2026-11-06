(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Import ExecF ITreeA SysStepF.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AImg AProto ABase AKit AKit2 ABytes ARep ARepKit ARepFrame ALayout AHeapP. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_ammap. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_ammap.F_ammap. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AMalloc_iface AEmbRep AFrameD AEmbFrame. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_arefill. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_arefill.F_arefill_x. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import ARefill_iface_x AExh.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AC6U.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC. Context {rc : runConstT} {ov : annOV}.

Definition c6_img (x : Z) : Prop :=
     (0xd14f8 <= x < 0xd1538) \/ (0xd3470 <= x < 0xd3478) \/ (AEMB <= x < AEMB + 56) \/ (0x169560 <= x < 0x169568)
  \/ (0x16b628 <= x < 0x16b629) \/ (0x16b678 <= x < 0x16b680) \/ (0x16b6ec <= x < 0x16b6ed) \/ (0x16b7d0 <= x < 0x16b7d8).

Lemma exh_cells_frameC : forall m m' (W : list ivl), exh_cells m -> munch W m m' -> (forall x, c6_img x -> outside W x) -> exh_cells m'.
Proof.
  intros m m' W (RC & TN & CF & CB) MU IC.
  assert (T : forall A cs, rw_cells asegs m A cs -> (forall x, A <= x < A + Z.of_nat (cells_size cs) -> c6_img x) -> rw_cells asegs m' A cs).
  { intros A cs Hc HA. eapply cells_frameO; [exact Hc| exact MU|]. intros x Hx. apply IC. exact (HA x Hx). }
  destruct RC as (R1 & R2 & R3 & R4 & R5).
  split; [unfold rmap_cells; split; [| split; [| split; [| split]]]| split; [| split]];
    (eapply T; [eassumption|]; cbn [cells_size csize Nat.add]; intros x Hx; unfold c6_img, AEMB; lia).
Qed.
Lemma emb_cells_frameC : forall st m m' (W : list ivl), emb_cells st m -> munch W m m' -> (forall x, c6_img x -> outside W x) ->
  (let '(d, cap, _) := a_emb st in forall x, d <= x < d + cap -> outside W x) -> emb_cells st m'.
Proof.
  intros st m m' W EC MU IC DB. unfold emb_cells in *. destruct (a_emb st) as [[d cap] sz].
  assert (T : forall A cs, rw_cells asegs m A cs -> AEMB <= A -> A + Z.of_nat (cells_size cs) <= AEMB + 56 -> rw_cells asegs m' A cs).
  { intros A cs Hc H1 H2. eapply cells_frameO; [exact Hc| exact MU|]. intros x Hx. apply IC. unfold c6_img. right; right; left. lia. }
  destruct EC as [MTX EC]. split; [apply T; [exact MTX| unfold AEMB; lia| unfold AEMB; cbn; lia]|].
  destruct (cap =? 0) eqn:C0.
  - destruct EC as (PTR & SZ & VEC). split; [apply T; [exact PTR| lia| unfold AEMB; cbn; lia]|]. split; [exact SZ|]. apply T; [exact VEC| lia| unfold AEMB; cbn; lia].
  - destruct EC as (PTR & VEC & P1 & P2 & P3 & P4 & P5 & P6 & (junk & OLD)).
    split; [apply T; [exact PTR| lia| unfold AEMB; cbn; lia]|]. split; [apply T; [exact VEC| lia| unfold AEMB; cbn; lia]|].
    repeat (split; [assumption|]). exists junk. eapply cells_frameO; [exact OLD| exact MU|].
    cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r, Z2Nat.id by (unfold EMB_INIT in P2; lia). exact DB.
Qed.

Definition c6_piece (L : alayout) (iv : Z * Z) : Prop :=
  fst iv < snd iv ->
     ATOP <= fst iv
  \/ (al_t L <= fst iv /\ snd iv <= al_t L + 4096)
  \/ (al_res L <= fst iv /\ snd iv <= al_space_beg L + 137438953472)
  \/ (0x7fff7000 <= fst iv /\ snd iv <= 0x10007fff8000)
  \/ (AINSTANCE <= fst iv /\ snd iv <= AINSTANCE + 728)
  \/ (0x1ab988 <= fst iv /\ snd iv <= 0x5fb9d0)
  \/ (al_nodes L <= fst iv /\ snd iv <= al_nodes L + 1048576)
  \/ (al_store L <= fst iv /\ snd iv <= al_store L + 8388608)
  \/ (0x15bd20 <= fst iv /\ snd iv <= 0x15bd21)
  \/ (AERRNO <= fst iv /\ snd iv <= AERRNO + 4).

Lemma outside_Forall : forall (W : list ivl) x, Forall (fun iv => ~ (fst iv <= x < snd iv)) W -> outside W x.
Proof. induction W as [|[lo hi] W IH]; intros x HF; cbn; [exact I|]. inversion HF as [|? ? H1 H2]; subst. cbn [fst snd] in H1. split; [exact H1| apply IH; exact H2]. Qed.

Theorem c6_frame : forall L RESV RNG st m m' (W : list ivl),
  alayout_ok L -> aresv_ok L RESV -> axg RESV RNG st m -> axflags L st m -> munch W m m' -> Forall (c6_piece L) W ->
  axg RESV RNG st m' /\ axflags L st m'.
Proof.
  intros L RESV RNG st m m' W ALO ARV (XC & EC & ER & ECL) AXF MU PCS.
  pose proof atop_range as ATR.
  pose proof (ao_t L ALO) as (_ & OT1 & OT2 & _ & OTi). unfold iclr, AIMG_LO, AIMG_HI in OTi.
  pose proof (ao_res L ALO) as (_ & _ & ORS & _). pose proof (ao_res_hi L ALO) as ORH. pose proof (ao_space L ALO) as RSP.
  pose proof (aobj_img _ _ (ao_nodes L ALO) ltac:(lia)) as ONi. pose proof (aobj_img _ _ (ao_store L ALO) ltac:(lia)) as OSi. unfold AIMG_HI in ONi, OSi.
  pose proof (ad_t_res L ALO) as DTR. pose proof (ad_nodes_res L ALO) as DNR. pose proof (ad_store_res L ALO) as DSR. unfold adisj in DTR, DNR, DSR.

  assert (IC : forall x, c6_img x -> outside W x).
  { intros x Hx. apply outside_Forall. eapply Forall_impl; [| exact PCS]. intros [lo hi] K. cbn [fst snd] in *. unfold c6_piece in K. cbn [fst snd] in K.
    intros IN. specialize (K ltac:(lia)). unfold c6_img, AEMB, AINSTANCE, AERRNO, ATP in *.
    clear -K IN Hx ATR OT1 OT2 OTi ORH ONi OSi. lia. }

  assert (DB : let '(d, cap, _) := a_emb st in forall x, d <= x < d + cap -> outside W x).
  { pose proof EC as EC1. unfold emb_cells in EC1. unfold emb_clr in ECL. destruct (a_emb st) as [[d cap] sz]. intros x Hx.
    destruct (Z.eqb_spec cap 0) as [E0|NZ]; [exfalso; lia|].
    destruct EC1 as (_ & _ & _ & _ & P2 & _ & _ & P5 & P6 & _). unfold EMB_INIT in P2.
    destruct ECL as [QQ|AV]; [exfalso; exact (NZ QQ)|]. unfold avoids_all in AV. rewrite forallb_app in AV. apply andb_prop in AV as [AV _].
    destruct ARV as (PCI & PCS' & PCR & _ & PCT & _ & PCN & PCST & _). fold (al_res L) in PCR.
    pose proof (pcov_clear _ _ _ _ _ PCI AV ltac:(unfold AIMG_HI; lia) ltac:(lia)) as Q1.
    pose proof (pcov_clear _ _ _ _ _ PCS' AV ltac:(lia) ltac:(lia)) as Q2.
    pose proof (pcov_clear _ _ _ _ _ PCR AV ltac:(lia) ltac:(lia)) as Q3.
    pose proof (pcov_clear _ _ _ _ _ PCT AV ltac:(lia) ltac:(lia)) as Q4.
    pose proof (pcov_clear _ _ _ _ _ PCN AV ltac:(lia) ltac:(lia)) as Q5.
    pose proof (pcov_clear _ _ _ _ _ PCST AV ltac:(lia) ltac:(lia)) as Q6.
    apply outside_Forall. eapply Forall_impl; [| exact PCS]. intros [lo hi] K. cbn [fst snd] in *. unfold c6_piece in K. cbn [fst snd] in K.
    intros IN. specialize (K ltac:(lia)). unfold AIMG_HI, AINSTANCE, AERRNO, ATP in *.
    clear -K IN Hx P6 Q1 Q2 Q3 Q4 Q5 Q6 RSP ATR. lia. }
  split.
  - split; [exact (exh_cells_frameC m m' W XC MU IC)|]. split; [exact (emb_cells_frameC st m m' W EC MU IC DB)|]. split; [exact ER| exact ECL].
  - intros c Hc NC. specialize (AXF c Hc NC). unfold axflag in *. eapply cells_frameO; [exact AXF| exact MU|]. cbn [cells_size csize Nat.add].
    intros x Hx. apply outside_Forall. eapply Forall_impl; [| exact PCS]. intros [lo hi] K. cbn [fst snd] in *. unfold c6_piece in K. cbn [fst snd] in K.
    intros IN. specialize (K ltac:(lia)).
    assert (RIE : aregion_info L c = al_space_beg L + 137438953472 + c * 128) by (unfold aregion_info, K_SPACE_SIZE, ARI_STRIDE; change (2^37) with 137438953472; reflexivity).
    unfold K_NUM_CLASSES, AINSTANCE, AERRNO, ATP in *. rewrite RIE in Hx.
    clear -K IN Hx Hc ATR OT1 OT2 OTi ORS ORH RSP ONi OSi DTR DNR DSR. lia.
Qed.

Lemma exh_mem_clear_other : forall c c' s, c' <> c -> exh_mem c' (exh_clear c s) = exh_mem c' s.
Proof.
  intros c c' s NE. unfold exh_mem, exh_clear. destruct s. cbn. induction a_exh as [|x l IH]; [reflexivity|]. cbn.
  destruct (x =? c) eqn:Q; cbn.
  - apply Z.eqb_eq in Q. subst x. replace (c' =? c) with false by (symmetry; apply Z.eqb_neq; exact NE). cbn. exact IH.
  - rewrite IH. reflexivity.
Qed.
Lemma exh_mem_set_other : forall c c' s, c' <> c -> exh_mem c' (exh_set c s) = exh_mem c' s.
Proof. intros c c' s NE. unfold exh_mem, exh_set. destruct s. cbn. replace (c' =? c) with false by (symmetry; apply Z.eqb_neq; exact NE). reflexivity. Qed.
Lemma exh_mem_eq_list : forall c s s', a_exh s' = a_exh s -> exh_mem c s' = exh_mem c s.
Proof. intros c s s' E. unfold exh_mem. rewrite E. reflexivity. Qed.

Lemma emb_clr_sub : forall RESV st st', a_emb st' = a_emb st ->
  (forall iv, In iv (flat_map sec_iv (achunks st')) -> In iv (flat_map sec_iv (achunks st))) -> emb_clr RESV st -> emb_clr RESV st'.
Proof.
  intros RESV st st' EE SUB EC. unfold emb_clr in *. rewrite EE. destruct (a_emb st) as [[d cap] sz]. destruct EC as [Z0|AV]; [left; exact Z0| right].
  unfold avoids_all in *. rewrite forallb_app in *. apply andb_prop in AV as [A1 A2]. apply andb_true_intro. split; [exact A1|].
  apply forallb_forall. intros iv Hiv. exact (proj1 (forallb_forall _ _) A2 iv (SUB iv Hiv)).
Qed.
Lemma achunks_new_prim : forall st st' id c n,
  a_live st' = <[id := CPrim c n]> (a_live st) -> a_qloc st' = a_qloc st -> a_qglob st' = a_qglob st ->
  forall iv, In iv (flat_map sec_iv (achunks st')) -> In iv (flat_map sec_iv (achunks st)).
Proof.
  intros st st' id c n EL EQ1 EQ2 iv Hiv. apply in_flat_map in Hiv as (ch & Hch & Hin). apply in_flat_map.
  unfold achunks in *. rewrite EL, EQ1, EQ2 in Hch. apply in_app_or in Hch as [Hch|Hch].
  - apply in_map_iff in Hch as ([p ch'] & E & Hp). cbn [snd] in E. subst ch'.
    apply list_elem_of_In in Hp. apply elem_of_map_to_list in Hp. apply lookup_insert_Some in Hp as [[_ E]|[_ Hp]].
    + subst ch. cbn [sec_iv] in Hin. destruct Hin.
    + exists ch. split; [| exact Hin]. apply in_or_app. left. apply in_map_iff. exists (p, ch). split; [reflexivity|].
      apply list_elem_of_In. apply elem_of_map_to_list. exact Hp.
  - exists ch. split; [| exact Hin]. apply in_or_app. right. exact Hch.
Qed.

Lemma c6_img_cell : forall L x, c6_img x -> c6_cell L x.
Proof.
  intros L x Hx. unfold c6_cell. unfold c6_img, AEMB in Hx.
  destruct Hx as [H|[H|[H|[H|[H|[H|[H|H]]]]]]];
    [left| do 1 right; left| do 2 right; left| do 3 right; left| do 4 right; left| do 5 right; left| do 6 right; left| do 7 right; left]; lia.
Qed.
Theorem aexh_frame : forall cs L st st' m m' (W : list ivl),
  AEXHc cs L st m -> munch W m m' -> sec_untouched L W -> c6_untouched L W ->
  a_emb st' = a_emb st -> a_exh st' = a_exh st -> AEXHc cs L st' m'.
Proof.
  intros cs L st st' m m' W (XC & EC & AXF & CK & CS) MU SU C6 EE EX.
  assert (IC : forall x, c6_img x -> outside W x).
  { intros x Hx. apply outside_Forall. eapply Forall_impl; [| exact C6]. intros [lo hi] K IN. cbn [fst snd] in *. exact (K x IN (c6_img_cell L x Hx)). }
  assert (DB : let '(d, cap, _) := a_emb st in forall x, d <= x < d + cap -> outside W x).
  { unfold emb_clrK in CK. destruct (a_emb st) as [[d cap] sz]. intros x Hx. apply outside_Forall. unfold sec_untouched in SU.
    eapply Forall_impl; [| exact SU]. intros [lo hi] K IN. cbn [fst snd] in *. exact (proj1 (proj2 (CK x Hx)) (K x IN)). }
  split; [exact (exh_cells_frameC m m' W XC MU IC)|].
  split. { pose proof (emb_cells_frameC st m m' W EC MU IC DB) as E. unfold emb_cells in *. rewrite EE. exact E. }
  split. { intros c Hc NC. specialize (AXF c Hc NC). unfold axflag in *. rewrite (exh_mem_eq_list c st st' EX).
           eapply cells_frameO; [exact AXF| exact MU|]. cbn [cells_size csize Nat.add]. intros x Hx. apply outside_Forall.
           eapply Forall_impl; [| exact C6]. intros [lo hi] K IN. cbn [fst snd] in *. apply (K x IN). unfold c6_cell. do 8 right.
           exists c. split; [exact Hc| split; [exact NC| lia]]. }
  split; [unfold emb_clrK in *; rewrite EE; exact CK| exact (emb_clrC_sub cs cs st st' EE (fun ch H => H) CS)].
Qed.

Definition c6_kind (cs : list achunk) (L : alayout) (st : astate) (iv : Z * Z) : Prop :=
  fst iv < snd iv ->
     AC6U.c6_std L (fst iv) (snd iv)
  \/ (exists c, 1 <= c < K_NUM_CLASSES /\ aregion_info L c <= fst iv /\ snd iv <= aregion_info L c + 128
               /\ (snd iv <= aregion_info L c + 68 \/ aregion_info L c + 69 <= fst iv \/ c = K_BATCH_CLASS))
  \/ (exists ch, In ch cs /\ sec_wf1 L ch /\ sec_mb ch <= fst iv /\ snd iv <= sec_mb ch + sec_ms ch)
  \/ ((forall x, fst iv <= x < snd iv -> ~ c6_cell L x)
      /\ (let '(d, cap, _) := a_emb st in forall x, d <= x < d + cap -> ~ (fst iv <= x < snd iv)))
  \/ AC6U.c6_imgp (fst iv) (snd iv).

Lemma c6_kind_cell : forall cs L st iv, alayout_ok L -> c6_kind cs L st iv -> forall x, fst iv <= x < snd iv -> ~ c6_cell L x.
Proof.
  intros cs L st [lo hi] ALO K x Hx. unfold c6_kind in K. cbn [fst snd] in *. specialize (K ltac:(lia)).
  destruct K as [K|[(c & Hc & K1 & K2 & K3)|[(ch & Hin & WF1 & K1 & K2)|[[K _]|KI]]]].
  5: exact (AC6U.c6p_imgp L lo hi ALO KI x Hx).
  - exact (AC6U.c6p_std L lo hi ALO (fun _ => K) x Hx).
  - exact (AC6U.c6p_ri L c lo hi ALO Hc K1 K2 K3 x Hx).
  - destruct ch as [c n|mb ms n]; [destruct WF1|]. cbn [sec_wf1 sec_mb sec_ms] in *. destruct WF1 as (_ & G2 & _ & _ & _ & _ & (_ & _ & Qr & _)).
    apply (AC6U.c6c_off_page L x ALO). right. pose proof (ao_space L ALO) as RSP. unfold ablk, AC6U.RIP, AIMG_HI, KLS in *. lia.
  - exact (K x Hx).
Qed.
Lemma c6_kind_buf : forall cs L st iv, alayout_ok L -> emb_clrK L st -> emb_clrC cs st -> c6_kind cs L st iv ->
  let '(d, cap, _) := a_emb st in forall x, d <= x < d + cap -> ~ (fst iv <= x < snd iv).
Proof.
  intros cs L st [lo hi] ALO CK CC K. unfold c6_kind, emb_clrK, emb_clrC in *. destruct (a_emb st) as [[d cap] sz] eqn:EA. intros x Hx IN. cbn [fst snd] in *.
  specialize (K ltac:(lia)). destruct (CK x Hx) as (BI & NK & NB & NP).
  destruct K as [K|[(c & Hc & K1 & K2 & K3)|[(ch & Hin & WF1 & K1 & K2)|[[_ K]|[KI _]]]]].
  5: { unfold AIMG_HI in *. lia. }
  - apply NK. pose proof (ao_space L ALO) as RSP. unfold AC6U.c6_std, AC6U.RIP, AINSTANCE in K. unfold aknown. unfold AIMG_HI, KLS, K_HIGH_MEM in *.
    destruct K as [K|[K|[K|[K|[K|[K|[K|[K|[K|[K|[K|[K|K]]]]]]]]]]]]; try (exfalso; lia).
    + do 4 right; left; lia.
    + do 5 right; left; lia.
    + do 6 right; left; lia.
    + do 7 right; left; lia.
    + do 8 right; left; lia.
    + do 9 right; left; lia.
    + do 10 right; left; lia.
    + do 11 right; lia.
  - apply NK. destruct (AC6U.ri_in_page L c Hc) as [P1 P2]. pose proof (ao_space L ALO) as RSP. unfold aknown, AC6U.RIP in *. do 7 right; left. lia.
  - destruct CC as [Z0|AV]; [lia|]. unfold avoids_all in AV. rewrite forallb_forall in AV.
    destruct ch as [c n|mb ms n]; [destruct WF1|]. cbn [sec_mb sec_ms] in *.
    assert (Hiv : In (mb, mb + ms) (flat_map sec_iv cs)) by (apply in_flat_map; exists (CSec mb ms n); split; [exact Hin| left; reflexivity]).
    specialize (AV _ Hiv). unfold iv_clear in AV. cbn [fst snd] in AV. apply orb_prop in AV as [Q|Q]; apply Z.leb_le in Q; lia.
  - exact (K x Hx IN).
Qed.

Theorem aexhc_frameK : forall cs L st st' m m' (W : list ivl),
  alayout_ok L -> AEXHc cs L st m -> munch W m m' -> Forall (c6_kind cs L st) W ->
  a_emb st' = a_emb st -> a_exh st' = a_exh st -> AEXHc cs L st' m'.
Proof.
  intros cs L st st' m m' W ALO (XC & EC & AXF & CK & CS) MU KS EE EX.
  assert (CELL : forall x, c6_cell L x -> outside W x).
  { intros x Hx. apply outside_Forall. eapply Forall_impl; [| exact KS]. intros iv K IN. exact (c6_kind_cell cs L st iv ALO K x IN Hx). }
  assert (IC : forall x, c6_img x -> outside W x) by (intros x Hx; exact (CELL x (c6_img_cell L x Hx))).
  assert (DB : let '(d, cap, _) := a_emb st in forall x, d <= x < d + cap -> outside W x).
  { assert (Q : Forall (fun iv => let '(d, cap, _) := a_emb st in forall x, d <= x < d + cap -> ~ (fst iv <= x < snd iv)) W).
    { eapply Forall_impl; [| exact KS]. intros iv K. exact (c6_kind_buf cs L st iv ALO CK CS K). }
    destruct (a_emb st) as [[d cap] sz]. intros x Hx. apply outside_Forall. eapply Forall_impl; [| exact Q]. intros iv K. exact (K x Hx). }
  split; [exact (exh_cells_frameC m m' W XC MU IC)|].
  split. { pose proof (emb_cells_frameC st m m' W EC MU IC DB) as E. unfold emb_cells in *. rewrite EE. exact E. }
  split. { intros c Hc NC. specialize (AXF c Hc NC). unfold axflag in *. rewrite (exh_mem_eq_list c st st' EX).
           eapply cells_frameO; [exact AXF| exact MU|]. cbn [cells_size csize Nat.add]. intros x Hx. apply CELL. unfold c6_cell. do 8 right.
           exists c. split; [exact Hc| split; [exact NC| lia]]. }
  split; [unfold emb_clrK in *; rewrite EE; exact CK| exact (emb_clrC_sub cs cs st st' EE (fun ch H => H) CS)].
Qed.

End CANSEC.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW Require Import BImg.
Module TwinB.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Exec OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Tac OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ExecF OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ITreeA OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.SysStepF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import AProto.TwinB ABase.TwinB AKit.TwinB AKit2.TwinB ABytes.TwinB ARep.TwinB ARepKit.TwinB ARepFrame.TwinB ALayout.TwinB AHeapP.TwinB.

  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_ammap.TwinB.F_ammap. Import AMalloc_iface.TwinB AEmbRep.TwinB AFrameD.TwinB AEmbFrame.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_arefill.TwinB.F_arefill_x. Import ARefill_iface_x.TwinB AExh.TwinB.
Import AC6U.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC. Context {rc : runConstT} {ov : annOV}.

Definition c6_img (x : Z) : Prop :=
     (0xd3610 <= x < 0xd3650) \/ (0xd5588 <= x < 0xd5590) \/ (AEMB <= x < AEMB + 56) \/ (0x16b720 <= x < 0x16b728)
  \/ (0x16d7e8 <= x < 0x16d7e9) \/ (0x16d838 <= x < 0x16d840) \/ (0x16d8ac <= x < 0x16d8ad) \/ (0x16d990 <= x < 0x16d998).

Lemma exh_cells_frameC : forall m m' (W : list ivl), exh_cells m -> munch W m m' -> (forall x, c6_img x -> outside W x) -> exh_cells m'.
Proof.
  intros m m' W (RC & TN & CF & CB) MU IC.
  assert (T : forall A cs, rw_cells bsegs m A cs -> (forall x, A <= x < A + Z.of_nat (cells_size cs) -> c6_img x) -> rw_cells bsegs m' A cs).
  { intros A cs Hc HA. eapply cells_frameO; [exact Hc| exact MU|]. intros x Hx. apply IC. exact (HA x Hx). }
  destruct RC as (R1 & R2 & R3 & R4 & R5).
  split; [unfold rmap_cells; split; [| split; [| split; [| split]]]| split; [| split]];
    (eapply T; [eassumption|]; cbn [cells_size csize Nat.add]; intros x Hx; unfold c6_img, AEMB; lia).
Qed.
Lemma emb_cells_frameC : forall st m m' (W : list ivl), emb_cells st m -> munch W m m' -> (forall x, c6_img x -> outside W x) ->
  (let '(d, cap, _) := a_emb st in forall x, d <= x < d + cap -> outside W x) -> emb_cells st m'.
Proof.
  intros st m m' W EC MU IC DB. unfold emb_cells in *. destruct (a_emb st) as [[d cap] sz].
  assert (T : forall A cs, rw_cells bsegs m A cs -> AEMB <= A -> A + Z.of_nat (cells_size cs) <= AEMB + 56 -> rw_cells bsegs m' A cs).
  { intros A cs Hc H1 H2. eapply cells_frameO; [exact Hc| exact MU|]. intros x Hx. apply IC. unfold c6_img. right; right; left. lia. }
  destruct EC as [MTX EC]. split; [apply T; [exact MTX| unfold AEMB; lia| unfold AEMB; cbn; lia]|].
  destruct (cap =? 0) eqn:C0.
  - destruct EC as (PTR & SZ & VEC). split; [apply T; [exact PTR| lia| unfold AEMB; cbn; lia]|]. split; [exact SZ|]. apply T; [exact VEC| lia| unfold AEMB; cbn; lia].
  - destruct EC as (PTR & VEC & P1 & P2 & P3 & P4 & P5 & P6 & (junk & OLD)).
    split; [apply T; [exact PTR| lia| unfold AEMB; cbn; lia]|]. split; [apply T; [exact VEC| lia| unfold AEMB; cbn; lia]|].
    repeat (split; [assumption|]). exists junk. eapply cells_frameO; [exact OLD| exact MU|].
    cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r, Z2Nat.id by (unfold EMB_INIT in P2; lia). exact DB.
Qed.

Definition c6_piece (L : alayout) (iv : Z * Z) : Prop :=
  fst iv < snd iv ->
     ATOP <= fst iv
  \/ (al_t L <= fst iv /\ snd iv <= al_t L + 4096)
  \/ (al_res L <= fst iv /\ snd iv <= al_space_beg L + 137438953472)
  \/ (0x7fff7000 <= fst iv /\ snd iv <= 0x10007fff8000)
  \/ (AINSTANCE <= fst iv /\ snd iv <= AINSTANCE + 728)
  \/ (0x1adb48 <= fst iv /\ snd iv <= 0x5fdb90)
  \/ (al_nodes L <= fst iv /\ snd iv <= al_nodes L + 1048576)
  \/ (al_store L <= fst iv /\ snd iv <= al_store L + 8388608)
  \/ (0x15dee0 <= fst iv /\ snd iv <= 0x15dee1)
  \/ (AERRNO <= fst iv /\ snd iv <= AERRNO + 4).

Lemma outside_Forall : forall (W : list ivl) x, Forall (fun iv => ~ (fst iv <= x < snd iv)) W -> outside W x.
Proof. induction W as [|[lo hi] W IH]; intros x HF; cbn; [exact I|]. inversion HF as [|? ? H1 H2]; subst. cbn [fst snd] in H1. split; [exact H1| apply IH; exact H2]. Qed.

Theorem c6_frame : forall L RESV RNG st m m' (W : list ivl),
  alayout_ok L -> aresv_ok L RESV -> axg RESV RNG st m -> axflags L st m -> munch W m m' -> Forall (c6_piece L) W ->
  axg RESV RNG st m' /\ axflags L st m'.
Proof.
  intros L RESV RNG st m m' W ALO ARV (XC & EC & ER & ECL) AXF MU PCS.
  pose proof atop_range as ATR.
  pose proof (ao_t L ALO) as (_ & OT1 & OT2 & _ & OTi). unfold iclr, AIMG_LO, AIMG_HI in OTi.
  pose proof (ao_res L ALO) as (_ & _ & ORS & _). pose proof (ao_res_hi L ALO) as ORH. pose proof (ao_space L ALO) as RSP.
  pose proof (aobj_img _ _ (ao_nodes L ALO) ltac:(lia)) as ONi. pose proof (aobj_img _ _ (ao_store L ALO) ltac:(lia)) as OSi. unfold AIMG_HI in ONi, OSi.
  pose proof (ad_t_res L ALO) as DTR. pose proof (ad_nodes_res L ALO) as DNR. pose proof (ad_store_res L ALO) as DSR. unfold adisj in DTR, DNR, DSR.

  assert (IC : forall x, c6_img x -> outside W x).
  { intros x Hx. apply outside_Forall. eapply Forall_impl; [| exact PCS]. intros [lo hi] K. cbn [fst snd] in *. unfold c6_piece in K. cbn [fst snd] in K.
    intros IN. specialize (K ltac:(lia)). unfold c6_img, AEMB, AINSTANCE, AERRNO, ATP in *.
    clear -K IN Hx ATR OT1 OT2 OTi ORH ONi OSi. lia. }

  assert (DB : let '(d, cap, _) := a_emb st in forall x, d <= x < d + cap -> outside W x).
  { pose proof EC as EC1. unfold emb_cells in EC1. unfold emb_clr in ECL. destruct (a_emb st) as [[d cap] sz]. intros x Hx.
    destruct (Z.eqb_spec cap 0) as [E0|NZ]; [exfalso; lia|].
    destruct EC1 as (_ & _ & _ & _ & P2 & _ & _ & P5 & P6 & _). unfold EMB_INIT in P2.
    destruct ECL as [QQ|AV]; [exfalso; exact (NZ QQ)|]. unfold avoids_all in AV. rewrite forallb_app in AV. apply andb_prop in AV as [AV _].
    destruct ARV as (PCI & PCS' & PCR & _ & PCT & _ & PCN & PCST & _). fold (al_res L) in PCR.
    pose proof (pcov_clear _ _ _ _ _ PCI AV ltac:(unfold AIMG_HI; lia) ltac:(lia)) as Q1.
    pose proof (pcov_clear _ _ _ _ _ PCS' AV ltac:(lia) ltac:(lia)) as Q2.
    pose proof (pcov_clear _ _ _ _ _ PCR AV ltac:(lia) ltac:(lia)) as Q3.
    pose proof (pcov_clear _ _ _ _ _ PCT AV ltac:(lia) ltac:(lia)) as Q4.
    pose proof (pcov_clear _ _ _ _ _ PCN AV ltac:(lia) ltac:(lia)) as Q5.
    pose proof (pcov_clear _ _ _ _ _ PCST AV ltac:(lia) ltac:(lia)) as Q6.
    apply outside_Forall. eapply Forall_impl; [| exact PCS]. intros [lo hi] K. cbn [fst snd] in *. unfold c6_piece in K. cbn [fst snd] in K.
    intros IN. specialize (K ltac:(lia)). unfold AIMG_HI, AINSTANCE, AERRNO, ATP in *.
    clear -K IN Hx P6 Q1 Q2 Q3 Q4 Q5 Q6 RSP ATR. lia. }
  split.
  - split; [exact (exh_cells_frameC m m' W XC MU IC)|]. split; [exact (emb_cells_frameC st m m' W EC MU IC DB)|]. split; [exact ER| exact ECL].
  - intros c Hc NC. specialize (AXF c Hc NC). unfold axflag in *. eapply cells_frameO; [exact AXF| exact MU|]. cbn [cells_size csize Nat.add].
    intros x Hx. apply outside_Forall. eapply Forall_impl; [| exact PCS]. intros [lo hi] K. cbn [fst snd] in *. unfold c6_piece in K. cbn [fst snd] in K.
    intros IN. specialize (K ltac:(lia)).
    assert (RIE : aregion_info L c = al_space_beg L + 137438953472 + c * 128) by (unfold aregion_info, K_SPACE_SIZE, ARI_STRIDE; change (2^37) with 137438953472; reflexivity).
    unfold K_NUM_CLASSES, AINSTANCE, AERRNO, ATP in *. rewrite RIE in Hx.
    clear -K IN Hx Hc ATR OT1 OT2 OTi ORS ORH RSP ONi OSi DTR DNR DSR. lia.
Qed.

Lemma exh_mem_clear_other : forall c c' s, c' <> c -> exh_mem c' (exh_clear c s) = exh_mem c' s.
Proof.
  intros c c' s NE. unfold exh_mem, exh_clear. destruct s. cbn. induction a_exh as [|x l IH]; [reflexivity|]. cbn.
  destruct (x =? c) eqn:Q; cbn.
  - apply Z.eqb_eq in Q. subst x. replace (c' =? c) with false by (symmetry; apply Z.eqb_neq; exact NE). cbn. exact IH.
  - rewrite IH. reflexivity.
Qed.
Lemma exh_mem_set_other : forall c c' s, c' <> c -> exh_mem c' (exh_set c s) = exh_mem c' s.
Proof. intros c c' s NE. unfold exh_mem, exh_set. destruct s. cbn. replace (c' =? c) with false by (symmetry; apply Z.eqb_neq; exact NE). reflexivity. Qed.
Lemma exh_mem_eq_list : forall c s s', a_exh s' = a_exh s -> exh_mem c s' = exh_mem c s.
Proof. intros c s s' E. unfold exh_mem. rewrite E. reflexivity. Qed.

Lemma emb_clr_sub : forall RESV st st', a_emb st' = a_emb st ->
  (forall iv, In iv (flat_map sec_iv (achunks st')) -> In iv (flat_map sec_iv (achunks st))) -> emb_clr RESV st -> emb_clr RESV st'.
Proof.
  intros RESV st st' EE SUB EC. unfold emb_clr in *. rewrite EE. destruct (a_emb st) as [[d cap] sz]. destruct EC as [Z0|AV]; [left; exact Z0| right].
  unfold avoids_all in *. rewrite forallb_app in *. apply andb_prop in AV as [A1 A2]. apply andb_true_intro. split; [exact A1|].
  apply forallb_forall. intros iv Hiv. exact (proj1 (forallb_forall _ _) A2 iv (SUB iv Hiv)).
Qed.
Lemma achunks_new_prim : forall st st' id c n,
  a_live st' = <[id := CPrim c n]> (a_live st) -> a_qloc st' = a_qloc st -> a_qglob st' = a_qglob st ->
  forall iv, In iv (flat_map sec_iv (achunks st')) -> In iv (flat_map sec_iv (achunks st)).
Proof.
  intros st st' id c n EL EQ1 EQ2 iv Hiv. apply in_flat_map in Hiv as (ch & Hch & Hin). apply in_flat_map.
  unfold achunks in *. rewrite EL, EQ1, EQ2 in Hch. apply in_app_or in Hch as [Hch|Hch].
  - apply in_map_iff in Hch as ([p ch'] & E & Hp). cbn [snd] in E. subst ch'.
    apply list_elem_of_In in Hp. apply elem_of_map_to_list in Hp. apply lookup_insert_Some in Hp as [[_ E]|[_ Hp]].
    + subst ch. cbn [sec_iv] in Hin. destruct Hin.
    + exists ch. split; [| exact Hin]. apply in_or_app. left. apply in_map_iff. exists (p, ch). split; [reflexivity|].
      apply list_elem_of_In. apply elem_of_map_to_list. exact Hp.
  - exists ch. split; [| exact Hin]. apply in_or_app. right. exact Hch.
Qed.

Lemma c6_img_cell : forall L x, c6_img x -> c6_cell L x.
Proof.
  intros L x Hx. unfold c6_cell. unfold c6_img, AEMB in Hx.
  destruct Hx as [H|[H|[H|[H|[H|[H|[H|H]]]]]]];
    [left| do 1 right; left| do 2 right; left| do 3 right; left| do 4 right; left| do 5 right; left| do 6 right; left| do 7 right; left]; lia.
Qed.
Theorem aexh_frame : forall cs L st st' m m' (W : list ivl),
  AEXHc cs L st m -> munch W m m' -> sec_untouched L W -> c6_untouched L W ->
  a_emb st' = a_emb st -> a_exh st' = a_exh st -> AEXHc cs L st' m'.
Proof.
  intros cs L st st' m m' W (XC & EC & AXF & CK & CS) MU SU C6 EE EX.
  assert (IC : forall x, c6_img x -> outside W x).
  { intros x Hx. apply outside_Forall. eapply Forall_impl; [| exact C6]. intros [lo hi] K IN. cbn [fst snd] in *. exact (K x IN (c6_img_cell L x Hx)). }
  assert (DB : let '(d, cap, _) := a_emb st in forall x, d <= x < d + cap -> outside W x).
  { unfold emb_clrK in CK. destruct (a_emb st) as [[d cap] sz]. intros x Hx. apply outside_Forall. unfold sec_untouched in SU.
    eapply Forall_impl; [| exact SU]. intros [lo hi] K IN. cbn [fst snd] in *. exact (proj1 (proj2 (CK x Hx)) (K x IN)). }
  split; [exact (exh_cells_frameC m m' W XC MU IC)|].
  split. { pose proof (emb_cells_frameC st m m' W EC MU IC DB) as E. unfold emb_cells in *. rewrite EE. exact E. }
  split. { intros c Hc NC. specialize (AXF c Hc NC). unfold axflag in *. rewrite (exh_mem_eq_list c st st' EX).
           eapply cells_frameO; [exact AXF| exact MU|]. cbn [cells_size csize Nat.add]. intros x Hx. apply outside_Forall.
           eapply Forall_impl; [| exact C6]. intros [lo hi] K IN. cbn [fst snd] in *. apply (K x IN). unfold c6_cell. do 8 right.
           exists c. split; [exact Hc| split; [exact NC| lia]]. }
  split; [unfold emb_clrK in *; rewrite EE; exact CK| exact (emb_clrC_sub cs cs st st' EE (fun ch H => H) CS)].
Qed.

Definition c6_kind (cs : list achunk) (L : alayout) (st : astate) (iv : Z * Z) : Prop :=
  fst iv < snd iv ->
     AC6U.TwinB.c6_std L (fst iv) (snd iv)
  \/ (exists c, 1 <= c < K_NUM_CLASSES /\ aregion_info L c <= fst iv /\ snd iv <= aregion_info L c + 128
               /\ (snd iv <= aregion_info L c + 68 \/ aregion_info L c + 69 <= fst iv \/ c = K_BATCH_CLASS))
  \/ (exists ch, In ch cs /\ sec_wf1 L ch /\ sec_mb ch <= fst iv /\ snd iv <= sec_mb ch + sec_ms ch)
  \/ ((forall x, fst iv <= x < snd iv -> ~ c6_cell L x)
      /\ (let '(d, cap, _) := a_emb st in forall x, d <= x < d + cap -> ~ (fst iv <= x < snd iv)))
  \/ AC6U.TwinB.c6_imgp (fst iv) (snd iv).

Lemma c6_kind_cell : forall cs L st iv, alayout_ok L -> c6_kind cs L st iv -> forall x, fst iv <= x < snd iv -> ~ c6_cell L x.
Proof.
  intros cs L st [lo hi] ALO K x Hx. unfold c6_kind in K. cbn [fst snd] in *. specialize (K ltac:(lia)).
  destruct K as [K|[(c & Hc & K1 & K2 & K3)|[(ch & Hin & WF1 & K1 & K2)|[[K _]|KI]]]].
  5: exact (AC6U.TwinB.c6p_imgp L lo hi ALO KI x Hx).
  - exact (AC6U.TwinB.c6p_std L lo hi ALO (fun _ => K) x Hx).
  - exact (AC6U.TwinB.c6p_ri L c lo hi ALO Hc K1 K2 K3 x Hx).
  - destruct ch as [c n|mb ms n]; [destruct WF1|]. cbn [sec_wf1 sec_mb sec_ms] in *. destruct WF1 as (_ & G2 & _ & _ & _ & _ & (_ & _ & Qr & _)).
    apply (AC6U.TwinB.c6c_off_page L x ALO). right. pose proof (ao_space L ALO) as RSP. unfold ablk, AC6U.TwinB.RIP, AIMG_HI, KLS in *. lia.
  - exact (K x Hx).
Qed.
Lemma c6_kind_buf : forall cs L st iv, alayout_ok L -> emb_clrK L st -> emb_clrC cs st -> c6_kind cs L st iv ->
  let '(d, cap, _) := a_emb st in forall x, d <= x < d + cap -> ~ (fst iv <= x < snd iv).
Proof.
  intros cs L st [lo hi] ALO CK CC K. unfold c6_kind, emb_clrK, emb_clrC in *. destruct (a_emb st) as [[d cap] sz] eqn:EA. intros x Hx IN. cbn [fst snd] in *.
  specialize (K ltac:(lia)). destruct (CK x Hx) as (BI & NK & NB & NP).
  destruct K as [K|[(c & Hc & K1 & K2 & K3)|[(ch & Hin & WF1 & K1 & K2)|[[_ K]|[KI _]]]]].
  5: { unfold AIMG_HI in *. lia. }
  - apply NK. pose proof (ao_space L ALO) as RSP. unfold AC6U.TwinB.c6_std, AC6U.TwinB.RIP, AINSTANCE in K. unfold aknown. unfold AIMG_HI, KLS, K_HIGH_MEM in *.
    destruct K as [K|[K|[K|[K|[K|[K|[K|[K|[K|[K|[K|[K|K]]]]]]]]]]]]; try (exfalso; lia).
    + do 4 right; left; lia.
    + do 5 right; left; lia.
    + do 6 right; left; lia.
    + do 7 right; left; lia.
    + do 8 right; left; lia.
    + do 9 right; left; lia.
    + do 10 right; left; lia.
    + do 11 right; lia.
  - apply NK. destruct (AC6U.TwinB.ri_in_page L c Hc) as [P1 P2]. pose proof (ao_space L ALO) as RSP. unfold aknown, AC6U.TwinB.RIP in *. do 7 right; left. lia.
  - destruct CC as [Z0|AV]; [lia|]. unfold avoids_all in AV. rewrite forallb_forall in AV.
    destruct ch as [c n|mb ms n]; [destruct WF1|]. cbn [sec_mb sec_ms] in *.
    assert (Hiv : In (mb, mb + ms) (flat_map sec_iv cs)) by (apply in_flat_map; exists (CSec mb ms n); split; [exact Hin| left; reflexivity]).
    specialize (AV _ Hiv). unfold iv_clear in AV. cbn [fst snd] in AV. apply orb_prop in AV as [Q|Q]; apply Z.leb_le in Q; lia.
  - exact (K x Hx IN).
Qed.

Theorem aexhc_frameK : forall cs L st st' m m' (W : list ivl),
  alayout_ok L -> AEXHc cs L st m -> munch W m m' -> Forall (c6_kind cs L st) W ->
  a_emb st' = a_emb st -> a_exh st' = a_exh st -> AEXHc cs L st' m'.
Proof.
  intros cs L st st' m m' W ALO (XC & EC & AXF & CK & CS) MU KS EE EX.
  assert (CELL : forall x, c6_cell L x -> outside W x).
  { intros x Hx. apply outside_Forall. eapply Forall_impl; [| exact KS]. intros iv K IN. exact (c6_kind_cell cs L st iv ALO K x IN Hx). }
  assert (IC : forall x, c6_img x -> outside W x) by (intros x Hx; exact (CELL x (c6_img_cell L x Hx))).
  assert (DB : let '(d, cap, _) := a_emb st in forall x, d <= x < d + cap -> outside W x).
  { assert (Q : Forall (fun iv => let '(d, cap, _) := a_emb st in forall x, d <= x < d + cap -> ~ (fst iv <= x < snd iv)) W).
    { eapply Forall_impl; [| exact KS]. intros iv K. exact (c6_kind_buf cs L st iv ALO CK CS K). }
    destruct (a_emb st) as [[d cap] sz]. intros x Hx. apply outside_Forall. eapply Forall_impl; [| exact Q]. intros iv K. exact (K x Hx). }
  split; [exact (exh_cells_frameC m m' W XC MU IC)|].
  split. { pose proof (emb_cells_frameC st m m' W EC MU IC DB) as E. unfold emb_cells in *. rewrite EE. exact E. }
  split. { intros c Hc NC. specialize (AXF c Hc NC). unfold axflag in *. rewrite (exh_mem_eq_list c st st' EX).
           eapply cells_frameO; [exact AXF| exact MU|]. cbn [cells_size csize Nat.add]. intros x Hx. apply CELL. unfold c6_cell. do 8 right.
           exists c. split; [exact Hc| split; [exact NC| lia]]. }
  split; [unfold emb_clrK in *; rewrite EE; exact CK| exact (emb_clrC_sub cs cs st st' EE (fun ch H => H) CS)].
Qed.

End CANSEC.
End TwinB.
