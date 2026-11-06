(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/Prog/check_no_overread.v, with its module paths, module names, addresses and numbers changed; 599 of its 725 lines of code are new or changed and 726 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_egress/lib/Prog/check_restamp.v; 247 of its 303 lines of code are new or changed and 669 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: ported from libreac/fuzz_decode proofs/libreac/fuzz_decode/lib/Prog/KindB.v at bf7779f81ed764787b77895d2f5c0db2627f33f3 for libdiginet/fuzz_decode; no image value changed; module path OSSVerify.Proofs.libdiginet.fuzz_decode.lib. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_decode/lib/Prog/KindB.v; 1381 of its 1439 lines of code are new or changed and 245 lines of the source are left out. *)
(* mark_quietly (fuzz_link.c:153-164), PLAIN build: the walk of its contract (lib/Prog/mark_quietly_c.v).

   The code (0x15d88, 31 instructions): push a 32-byte frame (ra, s0, s1, s2); s0 = ifname, s1 = m,
   s2 = the auipc base of g_sink; load g_sink. When it is 0 (the first call): fmemopen(g_said, 4096, "w")
   at 0x15dc4 (an SR contract, it reaches malloc), store the FILE in g_sink, abort on NULL (ruled out:
   fmemopen's Post gives a non-NULL block), reac_served_say_to(f) at 0x15dd0 (a `leaf` contract). Then
   rewind(g_sink) at 0x15ddc (`leaf`), pop the frame, and tail-call reac_served_mark at 0x15dfc (`leaf_fp`)
   on mark_quietly's own sp and ra.

   The walk runs in three pieces of instructions (`mq_pro`, `mq_mid`, `mq_tail`, over `mkR` registers on a
   memory that holds no byte above TASK_SIZE outside the image, MemNorm's `normalize_cj`), joined at the
   SR level (`mark_quietly_holds`): Contract.v's `evt_SR_canon` turns each instruction run into an SR
   step, and fmemopen's SR contract runs between the first two pieces. The frame facts the pieces carry
   are lib/Prog/mark_quietly_aux.v's `kb` / `kw`. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem mk_leaf mk_leaf_fp mk_call mk_str
  memfile_c reac_served_mark_c rewind_c reac_served_say_to_c printf_facts_c mark_quietly_aux.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require MemFile.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require Import KindBGlue.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require memfile_place.
Local Open Scope Z_scope.

(* ==========================================================================
   1. Readings of the marking predicates
   ========================================================================== *)

Definition MQ_K : Z := 17280.     (* MARK_QUIETLY_K *)
Definition RSM_K : Z := 17248.    (* reac_served_mark's K *)
Definition A_ERRNO : Z := 0x75564. (* tp - 164 with the frame's tp 0x75608 *)

Lemma apart_frame_K : forall R R' K K' a n, spZ R' = spZ R -> K' <= K ->
  apart_frame R K a n -> apart_frame R' K' a n.
Proof. intros R R' K K' a n E HK H. unfold apart_frame in *. rewrite E. lia. Qed.

Lemma mark_errno_ok_conv : forall m R R' K K' s, spZ R' = spZ R -> errno_at R' = errno_at R -> K' <= K ->
  mark_errno_ok m R K s -> mark_errno_ok m R' K' s.
Proof.
  intros m R R' K K' s E1 E2 HK (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9).
  unfold mark_errno_ok. rewrite E2.
  refine (conj H1 (conj _ (conj H3 (conj H4 (conj H5 (conj H6 (conj H7 (conj H8 H9)))))))).
  eapply apart_frame_K; [exact E1 | exact HK | exact H2].
Qed.

Lemma mark_table_ok_conv : forall m R R' K K' s tab, spZ R' = spZ R -> errno_at R' = errno_at R ->
  arg R' 0 = arg R 0 -> K' <= K -> mark_table_ok m R K s tab -> mark_table_ok m R' K' s tab.
Proof.
  intros m R R' K K' s tab E1 E2 E3 HK H i n2 ix p Hi Hp. cbv zeta.
  destruct (H i n2 ix p Hi Hp) as (H1 & H2 & H3 & H4 & H5). cbv zeta in *.
  rewrite E2, E3. refine (conj _ (conj H2 (conj H3 (conj H4 H5)))).
  eapply apart_frame_K; [exact E1 | exact HK | exact H1].
Qed.

Lemma mark_name_ok_conv : forall m R R' K K' s nm, spZ R' = spZ R -> errno_at R' = errno_at R ->
  arg R' 0 = arg R 0 -> arg R' 1 = arg R 1 -> K' <= K -> mark_name_ok m R K s nm -> mark_name_ok m R' K' s nm.
Proof.
  intros m R R' K K' s nm E1 E2 E3 E4 HK H str Hs.
  destruct (H str Hs) as (H1 & H2 & H3 & H4 & H5 & H6 & H7).
  rewrite E2, E3, E4. refine (conj H1 (conj _ (conj H3 (conj H4 (conj H5 (conj H6 H7)))))).
  eapply apart_frame_K; [exact E1 | exact HK | exact H2].
Qed.

Lemma mark_block_ok_conv : forall m R R' K K' s, spZ R' = spZ R -> errno_at R' = errno_at R ->
  arg R' 0 = arg R 0 -> K' <= K -> mark_block_ok m R K s -> mark_block_ok m R' K' s.
Proof.
  intros m R R' K K' s E1 E2 E3 HK H N. rewrite E3 in N.
  destruct (H N) as (H1 & H2 & H3 & H4 & H5 & H6).
  rewrite E2, E3. refine (conj _ (conj H2 (conj H3 (conj H4 (conj H5 H6))))).
  eapply apart_frame_K; [exact E1 | exact HK | exact H1].
Qed.

Lemma frame_apart_gnl_K : forall R R' K K', spZ R' = spZ R -> 0 <= K' <= K ->
  frame_apart_gnl R K -> frame_apart_gnl R' K'.
Proof. intros R R' K K' E HK H. unfold frame_apart_gnl, apart_gnl in *. rewrite E. lia. Qed.

(* the FILE moves from 0 (none yet) to the block fmemopen made *)
Lemma mark_errno_ok_sink : forall m R K s s', apart (errno_at R) 4 s' FILE_BLOCK ->
  mark_errno_ok m R K s -> mark_errno_ok m R K s'.
Proof.
  intros m R K s s' A (H1 & H2 & H3 & H4 & H5).
  exact (conj H1 (conj H2 (conj H3 (conj A H5)))).
Qed.

Lemma mark_table_ok_sink : forall m R K s s' tab,
  (forall i n2 ix p, nth_error tab i = Some (n2, ix) -> u64_at m (A_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p ->
     apart s' FILE_BLOCK p (Z.of_nat (length n2) + 1)) ->
  mark_table_ok m R K s tab -> mark_table_ok m R K s' tab.
Proof.
  intros m R K s s' tab A H i n2 ix p Hi Hp. cbv zeta.
  destruct (H i n2 ix p Hi Hp) as (H1 & H2 & H3 & H4 & H5).
  exact (conj H1 (conj H2 (conj H3 (conj (A i n2 ix p Hi Hp) H5)))).
Qed.

Lemma mark_name_ok_sink : forall m R K s s' nm,
  (forall str, nm = Some str -> apart s' FILE_BLOCK (arg R 1) (Z.of_nat (length str) + 8)) ->
  mark_name_ok m R K s nm -> mark_name_ok m R K s' nm.
Proof.
  intros m R K s s' nm A H str Hs. destruct (H str Hs) as (H1 & H2 & H3 & H4 & H5 & H6 & H7).
  exact (conj H1 (conj H2 (conj H3 (conj (A str Hs) (conj H5 (conj H6 H7)))))).
Qed.

Lemma mark_block_ok_sink : forall m R K s s', (arg R 0 <> 0 -> apart s' FILE_BLOCK (arg R 0) MK_SIZE) ->
  mark_block_ok m R K s -> mark_block_ok m R K s'.
Proof.
  intros m R K s s' A H N. destruct (H N) as (H1 & H2 & H3 & H4 & H5 & H6).
  exact (conj H1 (conj H2 (conj H3 (conj (A N) (conj H5 H6))))).
Qed.

(* ==========================================================================
   2. The facts reac_served_mark asks, as the walk carries them
   ========================================================================== *)

Definition mq_core (R : bvmap 5 word) (m : word -> option byte) (kbs : list byte)
    (tab : list (list byte * Z)) (nm : option (list byte)) (s : Z) : Prop :=
  nlk_at m kbs /\ iftab_at m kbs tab /\ mark_errno_ok m R MQ_K s /\ mark_table_ok m R MQ_K s tab
  /\ str_arg m (arg R 1) nm /\ mark_name_ok m R MQ_K s nm /\ mark_block_ok m R MQ_K s
  /\ (forall str, nm = Some str -> kept_str (arg R 1) (name_span (arg R 1) str))
  /\ (forall i n2 ix p, nth_error tab i = Some (n2, ix) ->
        u64_at m (A_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p -> 0 <= p < 2 ^ 64 -> kept_str p (Z.of_nat (length n2) + 1)).

(* the bytes they read (g_nl, the kept strings, the marks block) and the bytes they need writable *)
Definition mq_fpb (a0 x : Z) : Prop :=
  rng A_G_NL NK_SIZE x \/ rng A_G_NAMES G_NAMES_SIZE x \/ (0x10000 <= x < 0x20000)
  \/ (a0 <> 0 /\ rng a0 MK_SIZE x).
Definition mq_fpw (a0 e x : Z) : Prop :=
  rng A_G_NL NK_SIZE x \/ (a0 <> 0 /\ rng a0 MK_SIZE x) \/ rng e 4 x.

Lemma arg_range : forall R i, 0 <= arg R i < 2 ^ 64.
Proof. intros R i. unfold arg. apply (bv_unsigned_in_range 64). Qed.

Lemma kept_rng : forall a n x, kept_str a n -> 0 <= a < 2 ^ 64 -> rng a n x -> mq_fpb 0 x.
Proof.
  intros a n x K Ha Hx. unfold rng in Hx.
  destruct (kept_str_range a n K Ha ltac:(lia)) as [[H1 H2]|[H1 H2]]; unfold mq_fpb, rng.
  - right; left. lia.
  - right; right; left. lia.
Qed.

Lemma mq_fpb_0 : forall a0 x, mq_fpb 0 x -> ~ (a0 <> 0 /\ rng a0 MK_SIZE x) -> mq_fpb a0 x.
Proof. intros a0 x H _. unfold mq_fpb in *. tauto. Qed.

Lemma mq_fpb_widen : forall a0 x, mq_fpb 0 x -> mq_fpb a0 x.
Proof. intros a0 x H. unfold mq_fpb in *. destruct H as [H|[H|[H|[H _]]]]; [tauto | tauto | tauto | lia]. Qed.

Lemma mq_core_keep : forall R m m' kbs tab nm s, mq_core R m kbs tab nm s ->
  kb (mq_fpb (arg R 0)) m m' -> kw (mq_fpw (arg R 0) (errno_at R)) m m' -> mq_core R m' kbs tab nm s.
Proof.
  intros R m m' kbs tab nm s (NL & IT & EO & TO & SA & NO & BO & KN & KT) KB KW.
  assert (KG : kb (rng A_G_NL NK_SIZE) m m') by (eapply kb_mono; [|exact KB]; intros x Hx; left; exact Hx).
  assert (KS : forall a n, kept_str a n -> 0 <= a < 2 ^ 64 -> kb (rng a n) m m').
  { intros a n K Ha. eapply kb_mono; [|exact KB]. intros x Hx. apply mq_fpb_widen. exact (kept_rng a n x K Ha Hx). }
  pose proof IT as (_ & LT & _).
  split; [apply (nlk_at_kbw m); [exact NL | exact KG | eapply kw_mono; [|exact KW]; intros x Hx; left; exact Hx]|].
  split.
  { apply (iftab_at_kb m m' kbs tab IT KG). intros i n2 ix p Hi Hp H0 H1.
    apply KS; [exact (KT i n2 ix p Hi Hp ltac:(lia)) | lia]. }
  split; [apply (mark_errno_ok_kw m); [exact EO | eapply kw_mono; [|exact KW]; intros x Hx; right; right; exact Hx]|].
  split; [apply (mark_table_ok_kb m); [exact TO | exact LT | exact KG]|].
  split.
  { apply (str_arg_kb m m' _ nm SA). intros str Hs. eapply kb_mono; [|exact (KS _ _ (KN str Hs) (arg_range R 1))].
    intros x Hx. unfold rng, name_span in *.
    pose proof (Z.mod_pos_bound (- (arg R 1 + Z.of_nat (length str) + 1)) 8 ltac:(lia)). lia. }
  split.
  { apply (mark_name_ok_kb m m' R MQ_K s nm NO). intros str Hs. exact (KS _ _ (KN str Hs) (arg_range R 1)). }
  split.
  { apply (mark_block_ok_kbw m m' R MQ_K s BO). intros N. split.
    - eapply kb_mono; [|exact KB]. intros x Hx. right; right; right. split; [exact N | exact Hx].
    - eapply kw_mono; [|exact KW]. intros x Hx. right; left. split; [exact N | exact Hx]. }
  split; [exact KN|].
  intros i n2 ix p Hi Hp Hr. apply (KT i n2 ix p Hi); [|exact Hr].
  apply (u64_at_kb m' m); [exact Hp|]. apply kb_sym. eapply kb_mono; [|exact KG].
  assert (Hl : (i < length tab)%nat) by (apply nth_error_Some; rewrite Hi; discriminate).
  intros x Hx. unfold rng in *. unfold NK_IF_NAME, NK_SIZE in *. lia.
Qed.

(* the marks block lies outside the image (snprintf's pf_img_free), apart from errno and the FILE *)
Lemma pf_img_free_range : forall D n, pf_img_free D n -> 0 < n -> 0 <= D -> D + n <= 0x10000 \/ 0x97000 <= D.
Proof.
  intros D n H Hn HD.
  destruct (Z_le_gt_dec (D + n) 0x10000) as [E|E]; [left; exact E|].
  destruct (Z_le_gt_dec 0x97000 D) as [E'|E']; [right; exact E'|]. exfalso.
  set (i := Z.max 0 (0x10000 - D)).
  destruct (memfile_place.rsv_sweep_sound 8 memfile_c.IMG_LO memfile_c.IMG_TOP (D + i) memfile_place.rsv_cover)
    as (sg & Hs & Hsa); [unfold memfile_c.IMG_LO, memfile_c.IMG_TOP, i; lia|].
  exact (H i ltac:(unfold i; lia) sg Hs Hsa).
Qed.

Lemma marks_place : forall m R K s, mark_block_ok m R K s -> arg R 0 <> 0 ->
  (arg R 0 + MK_SIZE <= 0x10000 \/ 0x97000 <= arg R 0)
  /\ apart_frame R K (arg R 0) MK_SIZE /\ apart_gnl (arg R 0) MK_SIZE
  /\ apart (errno_at R) 4 (arg R 0) MK_SIZE /\ apart s FILE_BLOCK (arg R 0) MK_SIZE.
Proof.
  intros m R K s H N. destruct (H N) as (H1 & H2 & H3 & H4 & H5 & _).
  pose proof (arg_range R 0) as Ra.
  split; [exact (pf_img_free_range _ _ H5 ltac:(unfold MK_SIZE; lia) ltac:(lia))|]. tauto.
Qed.

Ltac mq_unf :=
  unfold mq_fpb, mq_fpw, rng, apart, apart_gnl, apart_frame, frame_apart_gnl, mf_place_ok, rapart,
    A_G_NL, NK_SIZE, NK_N_SENT, A_G_SAID, SAID_SIZE, A_G_SAY, A_G_SINK, MK_SIZE, FILE_BLOCK,
    MemFile.MF_BLOCK, MemFile.MF_ZEROED, MemFile.MF_BUF, MemFile.MF_BUFSIZ, MQ_K, RSM_K, A_IMG_TOP,
    IMG_TOP, IMG_LO, A_ERRNO, A_G_NAMES, G_NAMES_SIZE, GOT_GUARD, GUARD, A_GOT_GUARD, A_GUARD,
    REWIND_K, MARK_LINE_MAX in *.

Ltac out_tac := cbn [outside mf_hdr mf_said mf_block fst snd]; repeat split; mq_unf; lia.

(* the bytes mq_core reads survive any write list that misses g_nl, the kept strings and the marks block *)
Lemma mq_fpb_out : forall a0 (W : list ivl),
  (a0 <> 0 -> 0 <= a0 /\ a0 + MK_SIZE <= 2 ^ 64) ->
  (forall lo hi, In (lo, hi) W ->
     (hi <= A_G_NL \/ A_G_NL + NK_SIZE <= lo) /\ (hi <= A_G_NAMES \/ A_G_NAMES + G_NAMES_SIZE <= lo) /\
     (hi <= 0x10000 \/ 0x20000 <= lo) /\ (a0 <> 0 -> hi <= a0 \/ a0 + MK_SIZE <= lo)) ->
  forall x, mq_fpb a0 x -> 0 <= x < 2 ^ 64 /\ outside W x.
Proof.
  intros a0 W HA HW x Hx. split.
  - unfold mq_fpb, rng in Hx. destruct Hx as [Hx|[Hx|[Hx|[N Hx]]]];
      [mq_unf; lia | mq_unf; lia | lia | destruct (HA N); lia].
  - induction W as [|[lo hi] W IH]; cbn [outside]; [exact I|]. split.
    + destruct (HW lo hi (or_introl eq_refl)) as (H1 & H2 & H3 & H4).
      unfold mq_fpb, rng in Hx. destruct Hx as [Hx|[Hx|[Hx|[N Hx]]]];
        [mq_unf; lia | mq_unf; lia | lia | specialize (H4 N); lia].
    + apply IH. intros lo' hi' Hin. exact (HW lo' hi' (or_intror Hin)).
Qed.

(* ==========================================================================
   3. The last piece: rewind, the pop and the tail call (0x15dd8 .. 0x15dfc)
   ========================================================================== *)

(* what the whole run may write, from mark_quietly's own sp: its frame and every callee's below it, the
   FILE, g_said, errno, the fake kernel up to its request ring and the marks block *)
Definition mq_tw (sp a0 e s : Z) : list ivl :=
  [(sp - MQ_K, sp); mf_block s; mf_said; (e, e + 4); (A_G_NL, A_G_NL + NK_N_SENT + 4);
   (a0, a0 + (if a0 =? 0 then 0 else MK_SIZE))].

(* reac_served_mark's answer, over the memory the last piece starts on *)
Definition mq_tp (a0 s : Z) (m : word -> option byte) (kbs : list byte) (tab : list (list byte * Z))
    (nm : option (list byte)) (regs' : bvmap 5 word) (m' : word -> option byte) : Prop :=
  (exists k', 0 <= k' <= MARK_LINE_MAX /\ memfile_k m' s k') /\
  (a0 = 0 -> getr regs' 10 = wz (- E_INVAL) /\ nlk_at m' kbs) /\
  (a0 <> 0 -> forall gbs, marks_at m a0 gbs ->
     let M := mark_lib tab nm (mk_names gbs) (nk_sent kbs) (nk_kstate kbs) in
     getr regs' 10 = wz (m_rc M)
     /\ (exists gbs', marks_at m' a0 gbs' /\ marks_wf gbs' /\ mk_names gbs' = m_marks M
           /\ mk_n gbs' = Z.of_nat (length (m_marks M)))
     /\ (exists kbs', nlk_at m' kbs' /\ nlk_wf kbs'
           /\ nk_chunks kbs' = nk_chunks kbs /\ nk_end_errno kbs' = nk_end_errno kbs
           /\ nk_n_if kbs' = nk_n_if kbs /\ iftab_at m' kbs' tab
           /\ nk_next kbs' = Z.of_nat (k_next (m_state M))
           /\ nk_sent kbs' = m_reqs M /\ nk_n_sent kbs' = Z.of_nat (length (m_reqs M))
           /\ nk_open kbs' = 0 /\ nk_misuse kbs' = nk_misuse kbs
           /\ nk_opened kbs' - nk_closed kbs' = nk_opened kbs - nk_closed kbs
           /\ nk_opened kbs <= nk_opened kbs' <= nk_opened kbs + 2)).

Definition mq_tq (R0 : bvmap 5 word) (m : word -> option byte) (W : list ivl)
    (P : bvmap 5 word -> (word -> option byte) -> Prop) (ms : machine_state) : Prop :=
  exists (regs' Ft : bvmap 5 word) (fc' : bv 32) (m' : word -> option byte),
    ms = MS regs' Ft (ret_pc (getr R0 1)) fc' None m' (seg_rom rsegs) /\ frm0 fc' /\
    regs_preserved R0 regs' /\ munch W m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
    task_mem rsegs m' /\ P regs' m'.

Lemma mq_tq_ext : forall R0 m W P, (forall q1 q2 m', getr_same q1 q2 -> P q1 m' -> P q2 m') ->
  q_ext (mq_tq R0 m W P).
Proof.
  intros R0 m W P HP c a (regs' & Ft & fc' & m' & -> & FR & RP & MU & WM & MI & TM & PO) HE.
  destruct a as [Ra Fa pca svca rva fca ma roa].
  destruct HE as (ER & EF & EP & ES & EV & EC & EM & EO). cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending
    ms_resv ms_fcsr ms_mem ms_rom MS] in *. subst Fa pca svca rva fca ma roa.
  assert (E : getr_same regs' Ra) by (intros r; apply getr_eqv, ER).
  exists Ra, Ft, fc', m'. split; [reflexivity|]. split; [exact FR|].
  split; [exact (regs_preserved_same R0 R0 regs' Ra (fun r => eq_refl) E RP)|].
  repeat (split; [eassumption|]). exact (HP _ _ _ E PO).
Qed.

Lemma mq_tp_ext : forall a0 s m kbs tab nm q1 q2 m', getr_same q1 q2 ->
  mq_tp a0 s m kbs tab nm q1 m' -> mq_tp a0 s m kbs tab nm q2 m'.
Proof.
  intros a0 s m kbs tab nm q1 q2 m' E (H1 & H2 & H3). unfold mq_tp. rewrite <- (E 10%bv).
  exact (conj H1 (conj H2 H3)).
Qed.

Lemma rewind_post_ext : forall f k pos len pb om,
  post_ext (fun (regs : bvmap 5 word) (m : word -> option byte) (regs' : bvmap 5 word) m' =>
    let n1 := mf_n1 k pos in
    memfile_k m' f 0 /\ mf_pend_bytes m' f pb /\
    bytes_at rsegs m' (A_G_SAID + pos) (firstn (Z.to_nat n1) pb) /\
    mf_dyn m' f MemFile.F_NORD om 0 0 0 (if n1 <? k then pos + n1 else 0) (Z.max len (pos + n1))).
Proof. intros f k pos len pb om r1 r2 m q1 q2 m' _ _ H. exact H. Qed.

Lemma mq_tail : rewind_contract -> reac_served_mark_contract ->
  forall (ra0 sp0 gp tp t0 t1 t2 s0o s1o a0o a1o a2 a3 a4 a5 a6 a7 s2o s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
          ra' u0 u1 u2 v0 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 sw : word) F fc m kbs tab nm k,
  let R0 := mkR ra0 sp0 gp tp t0 t1 t2 s0o s1o a0o a1o a2 a3 a4 a5 a6 a7 s2o s3 s4 s5 s6 s7 s8 s9 s10 s11
                t3 t4 t5 t6 in
  mem_inv rsegs m -> task_mem rsegs m -> frm0 fc ->
  A_IMG_TOP <= bv_unsigned sp0 - MQ_K -> bv_unsigned sp0 <= TASK_SIZE -> bv_unsigned tp = 0x75608 ->
  stk rsegs m (bv_unsigned sp0 - MQ_K) (bv_unsigned sp0 + -32) ->
  rw_cells rsegs m (bv_unsigned sp0 + -32) [C8 s2o; C8 s1o; C8 s0o; C8 ra0] ->
  mq_core R0 m kbs tab nm (bv_unsigned sw) -> frame_apart_gnl R0 MQ_K ->
  nlk_wf kbs -> nk_open kbs = 0 -> nk_opened kbs + 2 < 2 ^ 31 -> nk_closed kbs + 2 < 2 ^ 31 ->
  memfile_k m (bv_unsigned sw) k -> u64_at m A_G_SAY (bv_unsigned sw) -> bv_unsigned sw <> 0 ->
  bv_unsigned sw + FILE_BLOCK <= bv_unsigned sp0 - MQ_K -> guard_words m ->
  evt rsegs (mq_tq R0 m (mq_tw (bv_unsigned sp0) (bv_unsigned a0o) A_ERRNO (bv_unsigned sw))
                   (mq_tp (bv_unsigned a0o) (bv_unsigned sw) m kbs tab nm))
    (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp0 + -32)) gp tp u0 u1 u2 a1o a0o v0 sw v2 v3 v4 v5 v6 v7
             (Z_to_bv 64 474528) s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
        F (Z_to_bv 64 0x15dd8) fc None m (seg_rom rsegs)).
Proof.
  intros RW RSM ra0 sp0 gp tp t0 t1 t2 s0o s1o a0o a1o a2 a3 a4 a5 a6 a7 s2o s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    ra' u0 u1 u2 v0 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 sw F fc m kbs tab nm k R0
    MI TM FRM ITOP STOP TP ST FR CORE FAG NW NOPN NOP NCL MF SAY SNZ SFB GW.
  assert (TS : TASK_SIZE = 140737488355328) by (vm_compute; reflexivity). rewrite TS in STOP.
  pose proof (bv_unsigned_in_range 64 sp0) as RSP. change (bv_modulus 64) with (2 ^ 64) in RSP.
  pose proof (bv_unsigned_in_range 64 sw) as RSW. change (bv_modulus 64) with (2 ^ 64) in RSW.
  assert (ERR : errno_at R0 = A_ERRNO)
    by (unfold errno_at; change (getr R0 4) with tp; rewrite TP; reflexivity).
  assert (A0 : arg R0 0 = bv_unsigned a0o) by reflexivity.
  assert (A1 : arg R0 1 = bv_unsigned a1o) by reflexivity.
  assert (SP0 : spZ R0 = bv_unsigned sp0) by reflexivity.
  pose proof (memfile_k_place m _ k MF) as PL.
  destruct (mf_dyn_of_memfile_k m _ k MF) as (fl & om & wend & wpos & wbase & pos & len & MD).
  destruct (mf_pend_of_memfile_k m _ k MF) as (pb & MP & LP).
  pose proof CORE as (NL & IT & EO & TO & SA & NO & BO & KN & KT).
  pose proof EO as (EW & _ & EG & ES & _).
  rewrite ERR in EW, EG, ES.
  assert (MPL : bv_unsigned a0o <> 0 ->
            (bv_unsigned a0o + MK_SIZE <= 0x10000 \/ 0x97000 <= bv_unsigned a0o)
            /\ apart_frame R0 MQ_K (bv_unsigned a0o) MK_SIZE /\ apart_gnl (bv_unsigned a0o) MK_SIZE
            /\ apart A_ERRNO 4 (bv_unsigned a0o) MK_SIZE /\ apart (bv_unsigned sw) FILE_BLOCK (bv_unsigned a0o) MK_SIZE).
  { intros N. rewrite <- A0 in N |- *. rewrite <- ERR. exact (marks_place m R0 MQ_K _ BO N). }
  assert (MA : bv_unsigned a0o <> 0 -> 0 <= bv_unsigned a0o /\ bv_unsigned a0o + MK_SIZE <= 2 ^ 64).
  { intros N. rewrite <- A0 in N. destruct (BO N) as (_ & _ & _ & _ & _ & gbs & (((H1 & H2 & _) & _) & L) & _).
    rewrite A0 in *. split; [exact H1|]. rewrite L in H2. exact H2. }
  unfold apart_frame in MPL. rewrite SP0 in MPL.
  pose proof FAG as FAG0. unfold frame_apart_gnl, apart_gnl in FAG. rewrite SP0 in FAG.
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp0 + -32)) = bv_unsigned sp0 + -32)
    by (apply unsigned_lit; mq_unf; lia).
  zstep. zstep.
  eapply (leaf_call _ _ _ _ _ (RW (bv_unsigned sw) k fl om wend wpos wbase pos len pb)
            (rewind_post_ext (bv_unsigned sw) k pos len pb om)).
  { apply mq_tq_ext. apply mq_tp_ext. }
  { cbv beta. rewrite mkR_a0. split; [reflexivity|].
    split; [exact MF|]. split; [exact MD|]. split; [exact MP|]. split; [exact LP|].
    unfold apart_frame, errno_ok, apart_frame. rewrite mkR_sp, ESP, mkR_errno.
    change (bv_unsigned tp + ERRNO_TP_OFF) with (errno_at R0). rewrite ERR.
    split; [mq_unf; lia|]. split; [mq_unf; lia|].
    split; [split; [exact EW|]; split; [mq_unf; lia|]; split; [exact ES|]; split; mq_unf; lia|].
    split; [mq_unf; lia | exact GW]. }
  { exact MI. }
  { rewrite ESP. exact ST. }
  { rewrite ESP. mq_unf. lia. }
  { rewrite ESP. lia. }
  intros ra1 w0 w1 w2 b0 b1 b2 b3 b4 b5 b6 b7 w3 w4 w5 w6 m1 MU1 WM1 MI1 ST1 PO1.
  cbv beta zeta in MU1, PO1. destruct PO1 as (MK1 & _).
  rewrite ESP, mkR_errno in MU1. rewrite ESP in ST1.
  change (bv_unsigned tp + ERRNO_TP_OFF) with (errno_at R0) in MU1. rewrite ERR in MU1.
  unfold mf_hdr, mf_said in MU1.
  assert (KB1 : kb (mq_fpb (arg R0 0)) m m1).
  { eapply kb_munch; [exact MU1|]. rewrite A0. apply mq_fpb_out; [exact MA|].
    intros lo hi Hin. cbn [In] in Hin.
    destruct Hin as [E|[E|[E|[E|[]]]]]; injection E as <- <-; repeat split; mq_unf; try lia;
      intros N; destruct (MPL N) as (P1 & P2 & P3 & P4 & P5); mq_unf; lia. }
  assert (KW1 : forall S, kw S m m1) by (intros S; apply kw_wmono; exact WM1).
  pose proof (mq_core_keep R0 m m1 kbs tab nm _ CORE KB1 (KW1 _)) as CORE1.
  assert (FR1 : rw_cells rsegs m1 (bv_unsigned sp0 + -32) [C8 s2o; C8 s1o; C8 s0o; C8 ra0]).
  { apply (rw_cells_kbw m); [exact FR | | apply KW1]. eapply kb_munch; [exact MU1|].
    intros x Hx. cbn in Hx. unfold rng in Hx. split; [mq_unf; lia | out_tac]. }
  assert (SAY1 : u64_at m1 A_G_SAY (bv_unsigned sw)).
  { apply (u64_at_kb m); [exact SAY|]. eapply kb_munch; [exact MU1|].
    intros x Hx. unfold rng in Hx. split; [mq_unf; lia | out_tac]. }
  assert (GW1 : guard_words m1).
  { apply (guard_words_kb m); [exact GW|]. eapply kb_munch; [exact MU1|].
    intros x Hx. unfold rng in Hx. split; [mq_unf; lia | out_tac]. }
  assert (TM1 : task_mem rsegs m1).
  { apply (task_mem_munch _ m m1 TM MU1). intros lo hi Hin. cbn [In] in Hin.
    destruct Hin as [E|[E|[E|[E|[]]]]]; injection E as <- <-; mq_unf; lia. }
  pose proof (marks_place m R0 MQ_K _ BO) as MPL0.
  rewrite ret_pc_even by (lia || reflexivity).
  zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
  lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ _ _) => set (Rt := R) end.
  assert (Et0 : arg Rt 0 = bv_unsigned a0o) by reflexivity.
  assert (Et1 : arg Rt 1 = arg R0 1) by reflexivity.
  assert (EtS : spZ Rt = spZ R0) by reflexivity.
  assert (EtE : errno_at Rt = errno_at R0) by reflexivity.
  assert (EtA : arg Rt 0 = arg R0 0) by reflexivity.
  assert (RPt : regs_preserved R0 Rt) by kb_saved.
  pose proof (stk_release rsegs m1 _ _ _ ST1 FR1 ltac:(unfold MQ_K; lia)) as ST3.
  cbn [cells_size csize Nat.add] in ST3.
  replace (bv_unsigned sp0 + -32 + Z.of_nat 32) with (bv_unsigned sp0) in ST3 by lia.
  clear ST1. rename ST3 into ST1.
  pose proof CORE1 as (NL1 & IT1 & EO1 & TO1 & SA1 & NO1 & BO1 & _ & _).
  pose proof (RSM (bv_unsigned sw)) as RS. unfold leaf_fp in RS.
  eapply evt_mono.
  { eapply (RS Rt F fc m1 (bv_unsigned sp0 - MQ_K)).
    - exists kbs, tab, nm, 0.
      refine (conj NL1 (conj _ (conj NW (conj NOPN (conj NOP (conj NCL (conj IT1 (conj _ (conj _
        (conj (policy_ro_of_mem_inv m1 MI1) (conj SAY1 (conj SNZ (conj MK1 (conj _ (conj _ (conj _
        (conj _ _))))))))))))))))).
      + exact (frame_apart_gnl_K R0 Rt MQ_K 17248 EtS ltac:(unfold MQ_K; lia) FAG0).
      + exact (mark_errno_ok_conv m1 R0 Rt MQ_K 17248 _ EtS EtE ltac:(unfold MQ_K; lia) EO1).
      + exact (mark_table_ok_conv m1 R0 Rt MQ_K 17248 _ tab EtS EtE EtA ltac:(unfold MQ_K; lia) TO1).
      + unfold MemFile.MF_BUFSIZ, MARK_LINE_MAX. lia.
      + rewrite EtS, SP0. mq_unf. lia.
      + rewrite Et1. exact SA1.
      + exact (mark_name_ok_conv m1 R0 Rt MQ_K 17248 _ nm EtS EtE EtA Et1 ltac:(unfold MQ_K; lia) NO1).
      + exact (mark_block_ok_conv m1 R0 Rt MQ_K 17248 _ EtS EtE EtA ltac:(unfold MQ_K; lia) BO1).
    - exact MI1.
    - exact TM1.
    - rewrite EtS, SP0. exact ST1.
    - rewrite EtS, SP0. unfold MQ_K. lia.
    - rewrite EtS, SP0. lia.
    - exact FRM.
    - exact ITOP.
    - exact (proj1 GW1).
    - destruct GW1 as [_ (g & Hg)]. exists g. exact Hg. }
  intros ms' (regs' & Ft & fc' & m' & -> & FRM' & FK & RP & MU2 & WM2 & MI2 & TM2 & ST2 & PO2).
  cbv beta in MU2, PO2. rewrite EtS, SP0, Et0, EtE, ERR in MU2.
  exists regs', Ft, fc', m'.
  split; [reflexivity|]. split; [exact FRM'|].
  split; [intros r Hr; rewrite (RP r Hr); exact (RPt r Hr)|].
  split.
  { apply (munch_trans _ m m1 m').
    - eapply munch_weaken; [|exact MU1]. intros x Hx. unfold mq_tw in Hx.
      cbn [outside mf_block mf_said] in Hx |- *.
      destruct Hx as (H1 & H2 & H3 & H4 & H5 & H6 & _). repeat split; mq_unf; lia.
    - eapply munch_weaken; [|exact MU2]. intros x Hx. unfold mq_tw in Hx.
      cbn [outside mf_block mf_said] in Hx |- *.
      destruct Hx as (H1 & H2 & H3 & H4 & H5 & H6 & _). repeat split; mq_unf; lia. }
  split; [exact (wmono_trans rsegs m m1 m' WM1 WM2)|].
  split; [exact MI2|]. split; [exact TM2|].
  destruct PO2 as (P1 & P2 & P3).
  split.
  { destruct (P1 0 MK1) as (k' & Hk & Mk). exists k'. split; [unfold MARK_LINE_MAX in *; lia | exact Mk]. }
  split.
  { intros Z0. rewrite Et0 in P2. destruct (P2 Z0) as (R10 & NLK). split; [exact R10 | exact (NLK kbs NL1)]. }
  intros N gbs MG. rewrite Et0 in P3.
  assert (MG1 : marks_at m1 (bv_unsigned a0o) gbs).
  { apply (marks_at_kbw m); [exact MG | | apply KW1]. eapply kb_mono; [|exact KB1].
    intros x Hx. rewrite A0. right; right; right. split; [exact N | exact Hx]. }
  exact (P3 N kbs tab nm gbs NL1 IT1 SA1 MG1).
Qed.

(* ==========================================================================
   4. The first piece: the push, the load of g_sink and the branch (0x15d88 .. 0x15dc4)
   ========================================================================== *)

Lemma mq_pro : forall (Q : machine_state -> Prop)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc m lo (sinkw : word),
  mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp) -> lo + 32 <= bv_unsigned sp -> 0x97000 <= lo ->
  bv_unsigned sp < 2 ^ 63 ->
  bytes_at rsegs m A_G_SINK (le8 sinkw) ->
  (forall m1, munch [(bv_unsigned sp + -32, bv_unsigned sp)] m m1 -> wmono rsegs m m1 -> mem_inv rsegs m1 ->
     stk rsegs m1 lo (bv_unsigned sp + -32) ->
     rw_cells rsegs m1 (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra] ->
     (bv_eqb sinkw (Z_to_bv 64 0) = false ->
        evt rsegs Q (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 a1 a0 a0 sinkw a2 a3 a4 a5 a6 a7
                             (Z_to_bv 64 474528) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 0x15dd8) fc None m1 (seg_rom rsegs))) /\
     (bv_eqb sinkw (Z_to_bv 64 0) = true ->
        evt rsegs Q (MS (mkR (Z_to_bv 64 89544) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 a1 a0
                             (Z_to_bv 64 476464) (Z_to_bv 64 4096) (Z_to_bv 64 66916) a3 a4 a5 a6 a7
                             (Z_to_bv 64 474528) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 0x192a0) fc None m1 (seg_rom rsegs)))) ->
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x15d88) fc None m (seg_rom rsegs)).
Proof.
  intros Q ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo sinkw
    MI ST LO IT SP HS K.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  assert (L0 : 0 <= lo) by (destruct ST as [? _]; lia).
  unfold A_G_SINK in HS.
  carve_frame 32%nat ST.
  zstep. zstep. zstep. zstep. zstep. zstep. zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m1 end.
  assert (HR : ov_read_bytes rsegs m1 (Z_to_bv 64 476456) 8 = Some (le8 sinkw)).
  { pose proof (bytes_at_ov_read rsegs m1 476456 (le8 sinkw) 0 8 HS ltac:(rewrite length_le8; lia)) as R.
    rewrite Z.add_0_r in R. exact R. }
  zstep. zstep. zstep.
  destruct (K m1 MU WM MI ST FR) as [KN KZ].
  case_eq (bv_eqb sinkw (Z_to_bv 64 0)); intros Es.
  - cbn [negb]. cbv iota. zstep. zstep. zstep. zstep. zstep. zstep. exact (KZ Es).
  - cbn [negb]. cbv iota. exact (KN Es).
Qed.

(* ==========================================================================
   5. The middle piece: g_sink = f, the NULL check, reac_served_say_to (0x15dc8 .. 0x15dd4)
   ========================================================================== *)

Lemma say_to_post_ext : post_ext (fun (regs : bvmap 5 word) (m : word -> option byte) (regs' : bvmap 5 word) m' =>
  u64_at m' A_G_SAY (arg regs 0)).
Proof. intros r1 r2 m q1 q2 m' E _ H. unfold arg in *. rewrite <- E. exact H. Qed.

Lemma mq_mid : reac_served_say_to_contract -> forall (Q : machine_state -> Prop), q_ext Q ->
  forall (ra' sp' gp tp t0 t1 t2 s0 s1 h a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc m lo,
  mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp') -> 0x97000 <= lo -> lo <= bv_unsigned sp' ->
  bv_unsigned sp' < 2 ^ 63 ->
  bv_unsigned h <> 0 ->
  (forall (ra'' t0' t1' t2' a0' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m2,
     munch [(A_G_SINK, A_G_SINK + 8); (A_G_SAY, A_G_SAY + 8)] m m2 -> wmono rsegs m m2 -> mem_inv rsegs m2 ->
     stk rsegs m2 lo (bv_unsigned sp') ->
     u64_at m2 A_G_SINK (bv_unsigned h) -> u64_at m2 A_G_SAY (bv_unsigned h) ->
     evt rsegs Q (MS (mkR ra'' sp' gp tp t0' t1' t2' s0 s1 a0' h a2' a3' a4' a5' a6' a7'
                          (Z_to_bv 64 474528) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                     F (Z_to_bv 64 0x15dd8) fc None m2 (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR ra' sp' gp tp t0 t1 t2 s0 s1 h a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 474528)
                       s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x15dc8) fc None m (seg_rom rsegs)).
Proof.
  intros SAYTO Q HQ ra' sp' gp tp t0 t1 t2 s0 s1 h a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo MI ST IT LS SP HNZ K.
  assert (L0 : 0 <= lo) by (destruct ST as [? _]; lia).
  pose proof (wr_at_store_ok rsegs m 476456 8 0 8 (wr_at_g_sink m) ltac:(lia) ltac:(lia)) as HS.
  replace (476456 + 0) with 476456 in HS by reflexivity.
  zstep.
  change (Z_to_bv 64 476456) with (wa 476456).
  set (m1 := write_to_mem m (wa 476456) (le8 h)).
  assert (MU1 : munch [(A_G_SINK, A_G_SINK + 8)] m m1).
  { apply munch_write; [apply munch_refl | lia | rewrite length_le8; unfold A_G_SINK; lia
                       | cbn [inside]; rewrite length_le8; left; unfold A_G_SINK; lia]. }
  assert (WM1 : wmono rsegs m m1) by (apply wmono_write, wmono_refl).
  assert (MI1 : mem_inv rsegs m1) by (apply mem_inv_store; [exact MI | rewrite length_le8; exact HS]).
  assert (ST1 : stk rsegs m1 lo (bv_unsigned sp')) by (apply stk_write; [exact ST | lia | rewrite length_le8; lia]).
  assert (BS1 : bytes_at rsegs m1 476456 (le8 h)) by (apply bytes_at_write_same; [lia | rewrite length_le8; lia]).
  clearbody m1.
  zstep.
  assert (Eh : bv_eqb h (Z_to_bv 64 0) = false).
  { unfold bv_eqb. apply Z.eqb_neq. rewrite unsigned_lit by lia. exact HNZ. }
  rewrite Eh. cbv iota.
  zstep.
  eapply (leaf_call _ _ _ _ _ SAYTO say_to_post_ext Q HQ).
  { cbv beta. exact (wr_at_g_say m1). }
  { exact MI1. }
  { exact ST1. }
  { unfold REAC_SERVED_SAY_TO. lia. }
  { exact SP. }
  intros ra1 w0 w1 w2 b0 b1 b2 b3 b4 b5 b6 b7 w3 w4 w5 w6 m2 MU2 WM2 MI2 ST2 PO2.
  cbv beta in MU2, PO2. rewrite mkR_a0 in PO2.
  assert (BS2 : bytes_at rsegs m2 476456 (le8 h)).
  { apply (bytes_at_transport rsegs _ m1 m2 _ _ BS1 MU2). rewrite length_le8. cbn [disjoint_from].
    unfold A_G_SAY. lia. }
  assert (HR : ov_read_bytes rsegs m2 (Z_to_bv 64 476456) 8 = Some (le8 h)).
  { pose proof (bytes_at_ov_read rsegs m2 476456 (le8 h) 0 8 BS2 ltac:(rewrite length_le8; lia)) as R.
    rewrite Z.add_0_r in R. exact R. }
  rewrite ret_pc_even by (lia || reflexivity).
  zstep.
  apply (K ra1 w0 w1 w2 b0 b2 b3 b4 b5 b6 b7 w3 w4 w5 w6 m2).
  - apply (munch_trans _ m m1 m2).
    + eapply munch_weaken; [|exact MU1]. intros x Hx. cbn [outside] in *. tauto.
    + eapply munch_weaken; [|exact MU2]. intros x Hx. cbn [outside] in *. unfold A_G_SINK, A_G_SAY in *.
      repeat split; lia.
  - exact (wmono_trans rsegs m m1 m2 WM1 WM2).
  - exact MI2.
  - exact ST2.
  - unfold u64_at, wz. rewrite Z_to_bv_bv_unsigned. exact BS2.
  - exact PO2.
Qed.

(* ==========================================================================
   6. The SR level: the frame's allocator interface and fmemopen between the pieces
   ========================================================================== *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09
  YO0i YO0f YO0d YM05 YL01 YO09.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YI14 YI16 YK14.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require Import Contract.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import StdioModel fmemopen_c mark_quietly_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require reac_served_say_to.
(* link's own names first again (YI14 has pcap's FILE_BLOCK) *)
Import link_mem memfile_c reac_served_mark_c mark_quietly_aux.

Lemma mq_canon_mkst : forall (fx : FPState) regs pc mem rom,
  RegisterBridge.canonical_register_state (@YK11.mkst fx regs pc mem rom)
  = MS (Regs6ss.mkR_of regs) fp_regs pc fp_csr None mem rom.
Proof. reflexivity. Qed.

(* an SR configuration runs a piece of instructions on the normalised memory *)
Lemma sr_cj : forall (fx : FPState) regs pc mem md (Q : machine_state -> Prop) (P : config -> Prop),
  ro_agree rsegs mem -> m_halted md = None -> m_vm_lazy md = [] ->
  evt rsegs Q (MS (Regs6ss.mkR_of regs) fp_regs pc fp_csr None (normalize_cj rsegs mem) (seg_rom rsegs)) ->
  (forall s0 can ms', Q s0 -> ms_rel_cj rsegs can s0 -> cj_same rsegs mem (ms_mem can) ->
     Regs6ss.ms_eqv can ms' -> SR rsegs (mkCfg ms' md) P) ->
  SR rsegs (mkCfg (@YK11.mkst fx regs pc mem (seg_rom rsegs)) md) P.
Proof.
  intros fx regs pc mem md Q P RO Hh Hl H K.
  eapply (evt_SR_canon rsegs); [| exact Hh | exact Hl |].
  { rewrite mq_canon_mkst. apply (evt_normalize_cj rsegs); [exact FrameAPI.wx_apart_rsegs | exact RO | exact H]. }
  intros ms' (can & (s0 & Q0 & REL & CJ) & EQ). exact (K s0 can ms' Q0 REL CJ EQ).
Qed.

(* the state a piece ends in, read back as the real configuration *)
Lemma ms_back : forall s0 can ms' (regs' Ft : bvmap 5 word) (fc' : bv 32) pc mf ro,
  s0 = MS regs' Ft pc fc' None mf ro -> ms_rel_cj rsegs can s0 -> Regs6ss.ms_eqv can ms' ->
  ms' = @YK11.mkst (mkFP Ft fc') (ms_regs ms') pc (ms_mem ms') ro /\ mem_rel_cj rsegs (ms_mem ms') mf /\
  (forall r, getr (ms_regs ms') r = getr regs' r) /\ ms_mem ms' = ms_mem can.
Proof.
  intros s0 [r1 f1 p1 sv1 rv1 fc1 m1 ro1] [r2 f2 p2 sv2 rv2 fc2 m2 ro2] regs' Ft fc' pc mf ro -> REL EQ.
  destruct REL as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8).
  destruct EQ as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8).
  cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom MS] in *. subst.
  split; [reflexivity|]. split; [assumption|].
  split; [intros r; symmetry; apply getr_eqv; assumption | reflexivity].
Qed.

Lemma mq_tw_cases : forall sp a0 e s x, ~ outside (mq_tw sp a0 e s) x ->
  (sp - MQ_K <= x < sp) \/ (s <= x < s + FILE_BLOCK) \/ (A_G_SAID <= x < A_G_SAID + SAID_SIZE)
  \/ (e <= x < e + 4) \/ (A_G_NL <= x < A_G_NL + NK_N_SENT + 4) \/ (a0 <> 0 /\ a0 <= x < a0 + MK_SIZE).
Proof.
  intros sp a0 e s x H. unfold mq_tw in H. cbn [outside mf_block mf_said fst snd] in H.
  destruct (a0 =? 0) eqn:E; [apply Z.eqb_eq in E | apply Z.eqb_neq in E];
    unfold FILE_BLOCK, MemFile.MF_BLOCK in *; lia.
Qed.

(* the frame's stack window, as `stk` sees it: writable and above the image, so present *)
Lemma mq_stk : forall m lo hi, 0x97000 <= lo -> hi <= 2 ^ 64 ->
  (forall a, lo <= a < hi -> writable_at rsegs m a) -> stk rsegs m lo hi.
Proof.
  intros m lo hi Hlo Hhi H. split; [lia|]. split; [lia|]. intros a Ha.
  pose proof (H a Ha) as W. split; [exact W|].
  destruct (present_of_writable_out m a ltac:(lia) ltac:(lia) W) as (bb & Hb).
  exists bb. unfold mrd, wa. rewrite Hb. reflexivity.
Qed.

Lemma mkR_of_getr : forall regs r, getr (Regs6ss.mkR_of regs) r = getr regs r.
Proof. intros regs r. symmetry. apply getr_eqv. apply Regs6ss.mkR_of_eqv. Qed.

Lemma ro_false_hi : forall x, 0x20000 <= x < 2 ^ 64 -> ro_addr rsegs (wa x) = false.
Proof.
  intros x Hx. destruct (ro_addr rsegs (wa x)) eqn:E; [|reflexivity].
  apply ro_addr_range in E; lia.
Qed.

Lemma ro_false_lo : forall x, 0 <= x < 0x10000 -> ro_addr rsegs (wa x) = false.
Proof.
  intros x Hx. destruct (ro_addr rsegs (wa x)) eqn:E; [|reflexivity].
  apply ro_addr_range in E; lia.
Qed.

Section SR.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : YI16.sink_head} {SK : YI14.sink_syms}.

(* the frame's pins of the allocator's symbols on the plain image (lib/FrameAPI.v `frame_facts_plain`) *)
Definition mq_pins : Prop :=
  ms_tp B = 0x75608 /\ ms_errno_off B = -164 /\ ms_ctx B = 0x95910 /\ ms_lock B = 0x95908 /\
  ms_libc B = 0x95898 /\ ms_got_guard B = 0x208d8 /\ ms_guard B = 0x95878 /\ ms_debruijn B = 0x10778 /\
  ms_size_classes B = 0x10798 /\ ms_small_cnt B = 0x107f8 /\ ms_med_cnt B = 0x10813 /\
  ms_vmlock B = None /\ ms_debruijn_len B = 32.

Hypothesis PINS : mq_pins.
Hypothesis AX : AllocExtra B (aa_MR API).

Lemma glob_unowned : forall L A mem md a, ms_segs B = rsegs -> aa_MR API L A mem md ->
  0x31b80 <= a < 0x75568 -> ~ owned B L A a.
Proof.
  intros L A mem md a SEGS HM Ha [Ho|Ho].
  - assert (Hi : in_img B a) by (apply (proj2 (in_img_rsegs B a SEGS)); lia).
    pose proof (ax_img AX L A mem md a HM Hi Ho) as C.
    destruct PINS as (_ & _ & PC & _). rewrite PC in C. unfold CTX_SIZE in C. lia.
  - destruct PINS as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13).
    unfold static_owned, vml_lo, vml_len in Ho. rewrite P4, P5, P6, P7, P8, P9, P10, P11, P12, P13 in Ho.
    change (Z.max 32 32) with 32 in Ho. lia.
Qed.

Lemma blk_facts : forall L A mem md q n a, ms_segs B = rsegs -> aa_MR API L A mem md ->
  In (q, n) (blocks L A) -> q <= a < q + n ->
  ~ owned B L A a /\ (a < 0x10000 \/ 0x97000 <= a) /\ 4096 <= q /\ q + n <= YM05.alloc_ceiling /\ present mem a.
Proof.
  intros L A mem md q n a SEGS HM Hin Ha. unfold blocks in Hin. apply in_map_iff in Hin as ([p k] & E & Hp).
  cbn [fst snd] in E. injection E as <- <-.
  destruct (mr_blocks B _ (aa_laws API) L A mem md p k (a - ptr_addr L p) HM Hp ltac:(lia)) as (Hpr & H1 & H2 & H3).
  pose proof (ax_blocks_img AX L A mem md p k (a - ptr_addr L p) HM Hp ltac:(lia)) as NI.
  replace (ptr_addr L p + (a - ptr_addr L p)) with a in * by lia.
  rewrite (in_img_rsegs B a SEGS) in NI.
  split; [exact H3|]. split; [lia|]. split; [lia|]. split; [lia | exact Hpr].
Qed.

Lemma mq_MR_keep : forall L A mem md mem' W, ms_segs B = rsegs -> aa_MR API L A mem md ->
  munch W mem mem' -> wmono rsegs mem mem' ->
  (forall x, 0 <= x < YM05.alloc_ceiling -> owned B L A x -> outside W x) -> aa_MR API L A mem' md.
Proof.
  intros L A mem md mem' W SEGS HM MU WM HO.
  pose proof YM05.alloc_ceiling_val as Hc.
  destruct (mr_model _ _ (aa_laws API) _ _ _ _ HM) as (Hh & Hl & Hmat).
  apply (mr_frame _ _ (aa_laws API) L A mem mem' md md HM).
  - intros a Ho. pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ HM Ho).
    rewrite SEGS. apply (KindBGlue.mbyte_munch rsegs W); [exact MU | lia | apply HO; [lia | exact Ho]].
  - intros a Ho Hpr. pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ HM Ho).
    apply (KindBGlue.present_munch W mem); [exact MU | lia | apply HO; [lia | exact Ho] | exact Hpr].
  - intros p n i Hin Hi.
    assert (Hb : In (ptr_addr L p, n) (blocks L A))
      by (unfold blocks; exact (in_map (fun b => (ptr_addr L (fst b), snd b)) _ _ Hin)).
    destruct (blk_facts L A mem md _ n (ptr_addr L p + i) SEGS HM Hb ltac:(lia)) as (_ & Hr & H1 & H2 & (bb & Hbb)).
    apply (present_of_writable_out mem'); [lia | exact Hr |].
    unfold writable_at. apply WM. unfold wview. rewrite Hbb. discriminate.
  - reflexivity.
  - exact Hh.
  - exact Hl.
  - exact Hmat.
Qed.

(* a callee-saved register a call keeps, read through the map it was set in *)
Lemma rg_pres : forall R1 R2 R3, regs_preserved R1 R2 -> (forall r, YK11.getr R1 r = YK11.getr R3 r) ->
  forall r, callee_saved r -> reg_get R2 (Z_to_bv 5 r) = reg_get R3 (Z_to_bv 5 r).
Proof.
  intros R1 R2 R3 RP G r Hr. pose proof (RP r Hr) as E. rewrite G in E.
  assert (NZ : bv_eqb (Z_to_bv 5 r) 0 = false).
  { unfold bv_eqb. apply Z.eqb_neq. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32.
    unfold callee_saved in Hr. rewrite Z.mod_small by lia. change (bv_unsigned 0) with 0. lia. }
  unfold YK11.getr in E. rewrite NZ in E. exact E.
Qed.

(* q_ext through an existential over the memory a piece starts on *)
Lemma q_ext_ex : forall (P : (word -> option byte) -> machine_state -> Prop),
  (forall m, q_ext (P m)) -> q_ext (fun s => exists m, P m s).
Proof. intros P H c a (m & Hm) E. exists m. exact (H m c a Hm E). Qed.

Lemma q_ext_and : forall (X : Prop) (Q : machine_state -> Prop), q_ext Q -> q_ext (fun s => X /\ Q s).
Proof. intros X Q H c a [Hx Hq] E. exact (conj Hx (H c a Hq E)). Qed.

(* the block fmemopen's malloc returns lies outside the image (memfile_place.v's argument) *)
Lemma place_of_fresh : forall h, ms_segs B = rsegs -> 4096 <= h -> (forall i, 0 <= i < MemFile.MF_BLOCK -> ~ in_img B (h + i)) ->
  mf_place_ok h.
Proof.
  intros h SEGS H0 H. unfold mf_place_ok, IMG_LO, IMG_TOP, MemFile.MF_BLOCK in *.
  destruct (Z_le_gt_dec (h + 1304) 0x10000) as [E|E]; [left; exact E|].
  destruct (Z_le_gt_dec 0x97000 h) as [E'|E']; [right; exact E'|]. exfalso.
  apply (H (Z.max h 0x10000 - h)); [lia|]. apply (in_img_rsegs B _ SEGS). lia.
Qed.

(* ... and so is the string followed by up to 8 more bytes *)
Lemma kept_apart_h8 : forall h p n k, kept_str p n -> 0 < n -> 0 <= k <= 8 -> mf_place_ok h -> 4096 <= h ->
  h + FILE_BLOCK <= 2 ^ 64 -> apart h FILE_BLOCK p (n + k).
Proof.
  intros h p n k K Hn Hk PL H0 H1. unfold apart, mf_place_ok, IMG_LO, IMG_TOP, MemFile.MF_BLOCK, FILE_BLOCK in *.
  destruct (Z_le_gt_dec (2 ^ 64) p) as [E|E]; [left; lia|].
  destruct (Z_le_gt_dec 0 p) as [E'|E'].
  - destruct (kept_str_range p n K ltac:(lia) Hn) as [[Q1 Q2]|[Q1 Q2]]; unfold A_G_NAMES, G_NAMES_SIZE in *; lia.
  - destruct (Z_le_gt_dec (p + n) 0) as [F|F]; [right; lia|]. exfalso.
    destruct K as [[K1 K2]|K]; [unfold A_G_NAMES in K1; lia|].
    specialize (K (- p) ltac:(lia)). replace (p + - p) with 0 in K by ring.
    rewrite (ro_false_lo 0 ltac:(lia)) in K. discriminate.
Qed.

(* u64_at fixes the stored value modulo 2^64 *)
Lemma u64_at_cong : forall m a v w, u64_at m a v -> u64_at m a w -> v mod 2 ^ 64 = w mod 2 ^ 64.
Proof.
  intros m a v w (_ & _ & Hv) (_ & _ & Hw).
  assert (E : le8 (wz v) = le8 (wz w)).
  { apply nth_error_ext. intros i. destruct (Nat.lt_ge_cases i 8) as [Hi|Hi].
    - rewrite <- (Hv i ltac:(rewrite length_le8; lia)), <- (Hw i ltac:(rewrite length_le8; lia)). reflexivity.
    - rewrite (proj2 (nth_error_None (le8 (wz v)) i)), (proj2 (nth_error_None (le8 (wz w)) i))
        by (rewrite length_le8; lia). reflexivity. }
  apply (f_equal le_bytes_to_word) in E. rewrite !le_bytes_to_word_le8 in E.
  apply (f_equal bv_unsigned) in E. unfold wz in E. rewrite !Z_to_bv_unsigned in E.
  unfold bv_wrap, bv_modulus in E. exact E.
Qed.

(* a kept string is apart from a FILE block outside the image *)
Lemma kept_apart_h : forall h p n, kept_str p n -> 0 < n -> mf_place_ok h -> 4096 <= h -> h + FILE_BLOCK <= 2 ^ 64 ->
  apart h FILE_BLOCK p n.
Proof.
  intros h p n K Hn PL H0 H1. unfold apart, mf_place_ok, IMG_LO, IMG_TOP, MemFile.MF_BLOCK, FILE_BLOCK in *.
  destruct (Z_le_gt_dec (2 ^ 64) p) as [E|E]; [left; lia|].
  destruct (Z_le_gt_dec 0 p) as [E'|E'].
  - destruct (kept_str_range p n K ltac:(lia) Hn) as [[Q1 Q2]|[Q1 Q2]]; unfold A_G_NAMES, G_NAMES_SIZE in *; lia.
  - destruct (Z_le_gt_dec (p + n) 0) as [F|F]; [right; lia|]. exfalso.
    destruct K as [[K1 K2]|K]; [unfold A_G_NAMES in K1; lia|].
    specialize (K (- p) ltac:(lia)). replace (p + - p) with 0 in K by ring.
    rewrite (ro_false_lo 0 ltac:(lia)) in K. discriminate.
Qed.

Lemma mq_pairwise_mid : forall {X} (R : X -> X -> Prop) b1 x b2 y,
  pairwise R (b1 ++ x :: b2) -> In y (b1 ++ b2) -> R x y \/ R y x.
Proof.
  intros X R b1. induction b1 as [|z b1 IH]; intros x b2 y HP Hin; cbn in *.
  - left. apply (proj1 HP). exact Hin.
  - destruct HP as [H1 H2]. destruct Hin as [<-|Hin].
    + right. apply H1. apply in_or_app. right. left. reflexivity.
    + exact (IH x b2 y H2 Hin).
Qed.

Lemma blocks_mid_disjoint : forall L A mem md b1 b2 d n q k, aa_MR API L A mem md ->
  blocks L A = b1 ++ (d, n) :: b2 -> In (q, k) (b1 ++ b2) -> q + k <= d \/ d + n <= q.
Proof.
  intros L A mem md b1 b2 d n q k HM E Hin.
  pose proof (mr_blocks_disjoint B _ (aa_laws API) L A mem md HM) as P. rewrite E in P.
  destruct (mq_pairwise_mid _ _ _ _ _ P Hin) as [D|D]; unfold ranges_disjoint in D; cbn in D; lia.
Qed.

Lemma mq_core_conv : forall R R' m kbs tab nm s,
  spZ R' = spZ R -> errno_at R' = errno_at R -> arg R' 0 = arg R 0 -> arg R' 1 = arg R 1 ->
  mq_core R m kbs tab nm s -> mq_core R' m kbs tab nm s.
Proof.
  intros R R' m kbs tab nm s E1 E2 E3 E4 (NL & IT & EO & TO & SA & NO & BO & KN & KT).
  refine (conj NL (conj IT (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ KT)))))))).
  - exact (mark_errno_ok_conv m R R' MQ_K MQ_K s E1 E2 ltac:(lia) EO).
  - exact (mark_table_ok_conv m R R' MQ_K MQ_K s tab E1 E2 E3 ltac:(lia) TO).
  - rewrite E4. exact SA.
  - exact (mark_name_ok_conv m R R' MQ_K MQ_K s nm E1 E2 E3 E4 ltac:(lia) NO).
  - exact (mark_block_ok_conv m R R' MQ_K MQ_K s E1 E2 E3 ltac:(lia) BO).
  - rewrite E4. exact KN.
Qed.

Theorem mark_quietly_holds : fmemopen_w_contract B API -> reac_served_say_to_contract -> rewind_contract ->
  reac_served_mark_contract -> mark_quietly_contract B API.
Proof.
  intros FMO SAYTO RW RSM. unfold mark_quietly_contract.
  intros L A regs mem md b tab kbs nm sink SEGS PRE RO NL NW NOPN IT FAG NOP NCL POL STR GSK EO TO TSZ MBLK FBLK
    KN KT NO BO ITOP GWm SN SZ FRM RES ROOM.
  pose proof YM05.alloc_ceiling_val as AC.
  pose proof PRE as (HM & HWF & HBD & HRA & HAL & HCEIL & H63 & HWS & HTP & HERR & HAUX).
  destruct (mr_model _ _ (aa_laws API) _ _ _ _ HM) as (Hh & Hl & Hmat).
  pose proof PINS as (P_TP & P_ERR & P_CTX & P_LOCK & P_LIBC & P_GOT & P_GUARD & P_DB & P_SC & P_SM & P_MD & P_VM & P_DL).
  rewrite SEGS in *.
  assert (TS : TASK_SIZE = 140737488355328) by (vm_compute; reflexivity).
  rewrite TS in TSZ.
  assert (TPv : bv_unsigned (getr regs 4) = 0x75608)
    by (change (getr regs 4) with (YK11.getr regs 4); rewrite HTP, P_TP; reflexivity).
  assert (ERRv : errno_at regs = A_ERRNO) by (unfold errno_at; rewrite TPv; reflexivity).
  assert (ERRA : errno_addr B = A_ERRNO) by (unfold errno_addr; rewrite P_TP, P_ERR; reflexivity).
  set (R0 := Regs6ss.mkR_of regs).
  assert (R0s : spZ R0 = spZ regs) by reflexivity.
  assert (R0e : errno_at R0 = errno_at regs) by reflexivity.
  assert (R0a0 : arg R0 0 = arg regs 0) by reflexivity.
  assert (R0a1 : arg R0 1 = arg regs 1) by reflexivity.
  assert (Ea0 : arg regs 0 = bv_unsigned (getr regs 10)) by reflexivity.
  assert (Ea1 : arg regs 1 = bv_unsigned (getr regs 11)) by reflexivity.
  assert (CORE : mq_core regs mem kbs tab nm sink).
  { refine (conj NL (conj IT (conj EO (conj TO (conj _ (conj NO (conj BO (conj _ _)))))))).
    - rewrite Ea1. exact STR.
    - rewrite Ea1. exact KN.
    - exact KT. }
  assert (CORER : mq_core R0 mem kbs tab nm sink) by exact (mq_core_conv regs R0 _ _ _ _ _ R0s R0e R0a0 R0a1 CORE).
  pose proof (bv_unsigned_in_range 64 (getr regs 2)) as RSP. change (bv_modulus 64) with (2 ^ 64) in RSP.
  change (bv_unsigned (getr regs 2)) with (spZ regs) in RSP.
  (* the marks block *)
  assert (MK0 : bv_unsigned (getr regs 10) <> 0 ->
      (bv_unsigned (getr regs 10) + MK_SIZE <= 0x10000 \/ 0x97000 <= bv_unsigned (getr regs 10))
      /\ 4096 <= bv_unsigned (getr regs 10) /\ bv_unsigned (getr regs 10) + MK_SIZE <= YM05.alloc_ceiling
      /\ forall x, bv_unsigned (getr regs 10) <= x < bv_unsigned (getr regs 10) + MK_SIZE ->
           ~ owned B L A x /\ (x < 0x10000 \/ 0x97000 <= x)).
  { intros N. destruct (MBLK N) as (q & n & Hq & H1 & H2).
    destruct (marks_place mem regs MARK_QUIETLY_K sink BO ltac:(rewrite Ea0; exact N)) as (P1 & _).
    rewrite Ea0 in P1.
    destruct (blk_facts L A mem md q n q SEGS HM Hq ltac:(unfold MK_SIZE in *; lia)) as (_ & _ & B1 & B2 & _).
    split; [exact P1|]. split; [lia|]. split; [lia|].
    intros x Hx. destruct (blk_facts L A mem md q n x SEGS HM Hq ltac:(lia)) as (O1 & O2 & _). tauto. }
  assert (MKF : bv_unsigned (getr regs 10) <> 0 ->
      bv_unsigned (getr regs 10) + MK_SIZE <= spZ regs - MARK_QUIETLY_K \/ spZ regs <= bv_unsigned (getr regs 10)).
  { intros N. destruct (marks_place mem regs MARK_QUIETLY_K sink BO ltac:(rewrite Ea0; exact N)) as (_ & P2 & _).
    unfold apart_frame in P2. rewrite Ea0 in P2. exact P2. }
  assert (MA : bv_unsigned (getr regs 10) <> 0 ->
      0 <= bv_unsigned (getr regs 10) /\ bv_unsigned (getr regs 10) + MK_SIZE <= 2 ^ 64)
    by (intros N; destruct (MK0 N) as (_ & H1 & H2 & _); lia).
  pose proof FAG as FAG1. unfold frame_apart_gnl, apart_gnl in FAG1.
  (* the normalised memory every piece runs on *)
  set (m0 := normalize_cj rsegs mem).
  assert (MI0 : mem_inv rsegs m0) by (apply mem_inv_cj_inv, mem_inv_cj_normalize).
  assert (TM0 : task_mem rsegs m0) by (apply mem_inv_cj_task, mem_inv_cj_normalize).
  assert (KB0 : forall S : Z -> Prop, (forall x, S x -> 0 <= x < TASK_SIZE) -> kb S mem m0)
    by (intros S HS; eapply kb_mono; [exact HS | apply kb_ncj; exact RO]).
  assert (KW0 : forall S : Z -> Prop, (forall x, S x -> 0 <= x < TASK_SIZE /\ ro_addr rsegs (wa x) = false) ->
      kw S mem m0) by (intros S HS; eapply kw_mono; [exact HS | apply kw_ncj]).
  assert (FPB : forall x, mq_fpb (arg R0 0) x -> 0 <= x < TASK_SIZE).
  { intros x Hx. rewrite TS. rewrite R0a0, Ea0 in Hx. unfold mq_fpb, rng in Hx.
    destruct Hx as [Hx|[Hx|[Hx|[N Hx]]]]; [mq_unf; lia | mq_unf; lia | lia | destruct (MK0 N) as (_ & _ & H2 & _); lia]. }
  assert (FPW : forall x, mq_fpw (arg R0 0) (errno_at R0) x -> 0 <= x < TASK_SIZE /\ ro_addr rsegs (wa x) = false).
  { intros x Hx. rewrite TS. rewrite R0a0, Ea0, R0e, ERRv in Hx. unfold mq_fpw, rng in Hx.
    destruct Hx as [Hx|[[N Hx]|Hx]].
    - mq_unf. split; [lia | apply ro_false_hi; lia].
    - destruct (MK0 N) as (P1 & H1 & H2 & _). split; [lia|].
      destruct P1 as [P1|P1]; [apply ro_false_lo | apply ro_false_hi]; mq_unf; lia.
    - mq_unf. split; [lia | apply ro_false_hi; lia]. }
  assert (CORE0 : mq_core R0 m0 kbs tab nm sink) by exact (mq_core_keep R0 mem m0 _ _ _ _ CORER (KB0 _ FPB) (KW0 _ FPW)).
  assert (STKm : stk rsegs mem (spZ regs - MQ_K) (spZ regs)).
  { apply mq_stk; [unfold A_IMG_TOP, MARK_QUIETLY_K, MQ_K in *; lia | lia |]. exact HWS. }
  assert (STK0 : stk rsegs m0 (spZ regs - MQ_K) (spZ regs)).
  { apply (stk_kbw mem); [exact STKm | apply KB0 | apply KW0]; intros x Hx; rewrite TS;
      unfold MQ_K, A_IMG_TOP, MARK_QUIETLY_K in *.
    - lia.
    - split; [lia | apply ro_false_hi; lia]. }
  assert (GW0 : guard_words m0).
  { apply (guard_words_kb mem); [exact GWm|]. apply KB0. intros x Hx. rewrite TS. unfold rng, GOT_GUARD, GUARD in Hx. lia. }
  assert (GS0 : u64_at m0 A_G_SINK sink).
  { apply (u64_at_kb mem); [exact GSK|]. apply KB0. intros x Hx. rewrite TS. unfold rng, A_G_SINK in Hx. lia. }
  assert (USK : 0 <= sink < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 sink) = sink) by (intros; apply unsigned_lit; lia).
  (* the PRO piece's stores miss what mq_core reads *)
  assert (KBP : forall m1, munch [(bv_unsigned (reg_get regs 2) + -32, bv_unsigned (reg_get regs 2))] m0 m1 ->
                  kb (mq_fpb (arg R0 0)) m0 m1).
  { intros m1 MU. eapply kb_munch; [exact MU|]. rewrite R0a0, Ea0. apply mq_fpb_out; [exact MA|].
    intros lo hi Hin. cbn [In] in Hin. destruct Hin as [E|[]]. injection E as <- <-.
    change (bv_unsigned (reg_get regs 2)) with (spZ regs).
    repeat split; mq_unf; unfold MARK_QUIETLY_K in *; try lia;
      intros N; specialize (MKF N); lia. }
  destruct (Z.eq_dec sink 0) as [S0|S0].
  - subst sink.
    destruct (SZ eq_refl) as (SOK & OE & GOK & WSAID).
    assert (REL0 : mem_rel_cj rsegs mem m0) by (apply mem_rel_cj_normalize; exact RO).
    set (Rf := mkR (Z_to_bv 64 89544) (Z_to_bv 64 (bv_unsigned (reg_get regs 2) + -32)) (reg_get regs 3)
                (reg_get regs 4) (reg_get regs 5) (reg_get regs 6) (reg_get regs 7) (reg_get regs 11)
                (reg_get regs 10) (Z_to_bv 64 476464) (Z_to_bv 64 4096) (Z_to_bv 64 66916) (reg_get regs 13)
                (reg_get regs 14) (reg_get regs 15) (reg_get regs 16) (reg_get regs 17) (Z_to_bv 64 474528)
                (reg_get regs 19) (reg_get regs 20) (reg_get regs 21) (reg_get regs 22) (reg_get regs 23)
                (reg_get regs 24) (reg_get regs 25) (reg_get regs 26) (reg_get regs 27) (reg_get regs 28)
                (reg_get regs 29) (reg_get regs 30) (reg_get regs 31)).
    eapply (sr_cj fx regs _ mem md
      (fun s1 => exists m1, munch [(bv_unsigned (reg_get regs 2) + -32, bv_unsigned (reg_get regs 2))] m0 m1
          /\ wmono rsegs m0 m1 /\ mem_inv rsegs m1
          /\ rw_cells rsegs m1 (bv_unsigned (reg_get regs 2) + -32)
               [C8 (reg_get regs 18); C8 (reg_get regs 9); C8 (reg_get regs 8); C8 (reg_get regs 1)]
          /\ s1 = MS Rf fp_regs (Z_to_bv 64 0x192a0) fp_csr None m1 (seg_rom rsegs))
      _ RO Hh Hl).
    { unfold R0, Regs6ss.mkR_of, MARK_QUIETLY.
      apply (mq_pro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m0 (spZ regs - MQ_K)
               (Z_to_bv 64 0)); [exact MI0 | exact STK0 | change (bv_unsigned (reg_get regs 2)) with (spZ regs); unfold MQ_K; lia
                                 | unfold A_IMG_TOP, MARK_QUIETLY_K, MQ_K in *; lia | exact H63 | exact GS0 |].
      intros m1 MU1 WM1 MI1 ST1 FR1. split.
      - intros Hne. exfalso. vm_compute in Hne. discriminate Hne.
      - intros _. apply evt_done. exists m1. split; [exact MU1|]. split; [exact WM1|]. split; [exact MI1|].
        split; [exact FR1 | reflexivity]. }
    intros s1 can1 ms1 (m1 & MU1 & WM1 & MI1 & FR1 & ->) REL1 CJ1 EQ1.
    destruct (ms_back _ _ _ _ _ _ _ _ _ eq_refl REL1 EQ1) as (EMS1 & RELF1 & GR1 & EMM1).
    assert (CJ1' : cj_same rsegs mem (ms_mem ms1)) by (rewrite EMM1; exact CJ1).
    rewrite EMS1.
    replace (@YK11.mkst (mkFP fp_regs fp_csr) (ms_regs ms1) (Z_to_bv 64 0x192a0) (ms_mem ms1) (seg_rom rsegs))
      with (@YK11.mkst fx (ms_regs ms1) (Z_to_bv 64 0x192a0) (ms_mem ms1) (seg_rom rsegs)) by reflexivity.
    set (R1 := ms_regs ms1) in *. set (mem1 := ms_mem ms1) in *.
    assert (GR1' : forall r, YK11.getr R1 r = YK11.getr Rf r) by exact GR1.
    assert (SPf : bv_unsigned (Z_to_bv 64 (bv_unsigned (reg_get regs 2) + -32)) = spZ regs - 32).
    { change (bv_unsigned (reg_get regs 2)) with (spZ regs). apply unsigned_lit.
      unfold A_IMG_TOP, MARK_QUIETLY_K in *. lia. }
    assert (SP1 : spZ R1 = spZ regs - 32) by (unfold spZ; rewrite GR1'; exact SPf).
    assert (MUm1 : munch [(bv_unsigned (reg_get regs 2) + -32, bv_unsigned (reg_get regs 2))] mem mem1)
      by exact (munch_rel_cj rsegs _ mem m0 mem1 m1 REL0 RELF1 CJ1' MU1).
    assert (WMm1 : wmono rsegs mem mem1) by exact (wmono_rel_cj rsegs mem m0 mem1 m1 REL0 RELF1 CJ1' WM1).
    assert (RO1 : ro_agree rsegs mem1) by exact (ro_agree_same_cj rsegs mem mem1 RO CJ1').
    assert (OUT1 : forall x, ~ (spZ regs - 32 <= x < spZ regs) ->
                   outside [(bv_unsigned (reg_get regs 2) + -32, bv_unsigned (reg_get regs 2))] x).
    { intros x Hx. cbn [outside]. change (bv_unsigned (reg_get regs 2)) with (spZ regs). split; [lia | exact I]. }
    assert (KB1 : forall S : Z -> Prop, (forall x, S x -> 0 <= x < 2 ^ 64 /\ ~ (spZ regs - 32 <= x < spZ regs)) ->
                  kb S mem mem1).
    { intros S HS. eapply kb_munch; [exact MUm1|]. intros x Hx. destruct (HS x Hx) as [H1 H2].
      split; [exact H1 | exact (OUT1 x H2)]. }
    pose proof (FMO L A R1 mem1 md b SEGS) as F1. rewrite SEGS in F1.
    eapply SR_bind.
    { apply F1.
      - unfold call_pre_k. rewrite SEGS.
        split.
        { apply (mq_MR_keep L A mem md mem1 _ SEGS HM MUm1 WMm1). intros x Hx Ho. apply OUT1.
          unfold MARK_QUIETLY_K in *. lia. }
        split; [exact HWF|]. split; [exact HBD|].
        split; [rewrite GR1'; vm_compute; reflexivity|].
        split; [rewrite SP1; replace (spZ regs - 32) with (spZ regs + (-2) * 16) by ring; rewrite Z.mod_add by lia;
                exact HAL|].
        split; [rewrite SP1; unfold FMEMOPEN_K, MARK_QUIETLY_K in *; lia|].
        split; [rewrite SP1; lia|].
        split; [intros a Ha; rewrite SP1 in Ha; unfold writable_at; apply WMm1; apply HWS;
                unfold FMEMOPEN_K, MARK_QUIETLY_K in *; lia|].
        split; [rewrite GR1'; exact HTP|].
        split; [intros a Ha; unfold writable_at; apply WMm1; apply HERR; exact Ha|].
        intros Hst. rewrite SP1. apply (auxv_pre_mono B _ (spZ regs)); [lia|].
        apply (kb_auxv B API _ _ mem mem1 _ L A md HM (HAUX Hst) MUm1).
        + intros x Hx Hy. apply OUT1. lia.
        + intros x Hx Ho. apply OUT1. unfold MARK_QUIETLY_K in *. lia.
      - rewrite GR1'. reflexivity.
      - rewrite GR1'. reflexivity.
      - rewrite GR1'. reflexivity.
      - exact (wr_at_kw mem mem1 _ _ WSAID (kw_wmono _ _ _ WMm1)).
      - apply (stdio_ok_kb mem); [exact SOK|]. apply KB1. intros x Hx. unfold rng, A_LIBC, A_OFL_LOCK in Hx.
        unfold A_IMG_TOP, MARK_QUIETLY_K in *. lia.
      - apply (ofl_empty_kbw mem); [exact OE | apply KB1 | apply kw_wmono; exact WMm1].
        intros x Hx. unfold rng, A_OFL_HEAD in Hx. unfold A_IMG_TOP, MARK_QUIETLY_K in *. lia.
      - apply (guard_ok_kb mem); [exact GOK|]. apply KB1. intros x Hx. unfold rng, A_GOT_GUARD, A_GUARD in Hx.
        unfold A_IMG_TOP, MARK_QUIETLY_K in *. lia.
      - exact RO1.
      - exact RES.
      - exact ROOM. }
    intros c2 (L' & A' & R2 & mem2 & md2 & h & -> & CPOST & H10 & HNZ & HAL16 & FRESH & (b1 & b2 & BLK1 & BLK2)
      & KEPT & UBK & INIT & RLEN & RES' & MFK & MFD & OFL & SOK2 & GOK2 & RO2).
    pose proof CPOST as (HM2 & HWF2 & HBD2 & HLE & HSTAB & HPRES & HVM & HFRAME & HBLKS & HSCR).
    rewrite SEGS in HFRAME, HBLKS, HSCR.
    destruct (mr_model _ _ (aa_laws API) _ _ _ _ HM2) as (Hh2 & Hl2 & Hmat2).
    pose proof FRESH as (FR_lo & FR_hi & FR_img).
    assert (PLh : mf_place_ok h) by exact (place_of_fresh h SEGS FR_lo FR_img).
    assert (Hh64 : 0 <= h < 2 ^ 64) by (unfold MemFile.MF_BLOCK in FR_hi; lia).
    assert (INH : In (h, MemFile.MF_BLOCK) (blocks L' A')) by (rewrite BLK1; apply in_or_app; right; left; reflexivity).
    assert (SP1' : spZ R1 = spZ regs - 32) by exact SP1.
    assert (ERR1 : errno_addr B = A_ERRNO) by exact ERRA.
    (* fmemopen keeps the bytes it does not own, write or use as scratch *)
    assert (FKB : forall x, (YM05.alloc_ceiling <= x < 2 ^ 64 \/ in_img B x) -> ~ owned B L A x -> ~ owned B L' A' x ->
                  ~ scratch_k B FMEMOPEN_K R1 x -> ~ fmemopen_w_writes h x ->
                  mbyte rsegs mem2 x = mbyte rsegs mem1 x /\ (writable_at rsegs mem1 x <-> writable_at rsegs mem2 x))
      by exact HFRAME.
    assert (GLOB : forall x, 0x31b80 <= x < 0x75538 ->
                   mbyte rsegs mem2 x = mbyte rsegs mem1 x /\ (writable_at rsegs mem1 x <-> writable_at rsegs mem2 x)).
    { intros x Hx. apply FKB.
      - right. apply (in_img_rsegs B x SEGS). lia.
      - exact (glob_unowned L A mem md x SEGS HM ltac:(lia)).
      - exact (glob_unowned L' A' mem2 md2 x SEGS HM2 ltac:(lia)).
      - unfold scratch_k. rewrite SP1', ERR1. unfold A_IMG_TOP, MARK_QUIETLY_K, A_ERRNO, FMEMOPEN_K in *. lia.
      - unfold fmemopen_w_writes, A_OFL_HEAD, mf_place_ok, IMG_LO, IMG_TOP, MemFile.MF_BLOCK in *. lia. }
    assert (HIGH : forall x, YM05.alloc_ceiling <= x < 2 ^ 64 -> ~ (spZ regs - 32 - FMEMOPEN_K <= x < spZ regs - 32) ->
                   mbyte rsegs mem2 x = mbyte rsegs mem1 x /\ (writable_at rsegs mem1 x <-> writable_at rsegs mem2 x)).
    { intros x Hx Hs. apply FKB.
      - left. exact Hx.
      - intros Ho. pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ HM Ho). lia.
      - intros Ho. pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ HM2 Ho). lia.
      - unfold scratch_k. rewrite SP1', ERR1. unfold A_ERRNO, FMEMOPEN_K in *. lia.
      - unfold fmemopen_w_writes, A_OFL_HEAD, MemFile.MF_BLOCK in *. lia. }
    (* the marks block, a block of A that fmemopen keeps *)
    assert (MKB : bv_unsigned (getr regs 10) <> 0 -> exists p n, In (p, n) (user_blocks A) /\
                   ptr_addr L p <= bv_unsigned (getr regs 10) /\ bv_unsigned (getr regs 10) + MK_SIZE <= ptr_addr L p + n).
    { intros N. destruct (MBLK N) as (q & n & Hq & H1 & H2). unfold blocks in Hq.
      apply in_map_iff in Hq as ([p n'] & E & Hp). cbn [fst snd] in E. injection E as <- <-.
      exists p, n'. split; [exact Hp | lia]. }
    assert (KB01 : kb (mq_fpb (arg R0 0)) mem mem1).
    { apply KB1. intros x Hx. rewrite R0a0, Ea0 in Hx. unfold mq_fpb, rng in Hx.
      destruct Hx as [Hx|[Hx|[Hx|[N Hx]]]].
      - mq_unf. unfold MARK_QUIETLY_K in *. lia.
      - mq_unf. unfold A_IMG_TOP, MARK_QUIETLY_K in *. lia.
      - unfold A_IMG_TOP, MARK_QUIETLY_K in *. lia.
      - specialize (MKF N). destruct (MK0 N) as (_ & _ & H2 & _). unfold MARK_QUIETLY_K in *. lia. }
    assert (KB12 : kb (mq_fpb (arg R0 0)) mem1 mem2).
    { intros x Hx. rewrite R0a0, Ea0 in Hx. unfold mq_fpb, rng in Hx.
      destruct Hx as [Hx|[Hx|[Hx|[N Hx]]]].
      - apply GLOB. mq_unf. lia.
      - apply GLOB. mq_unf. lia.
      - apply (kb_ro mem1 mem2 RO1 RO2). split; [lia | apply ro_addr_of_range; lia].
      - destruct (MKB N) as (p & n & Hp & H1 & H2).
        replace x with (ptr_addr L p + (x - ptr_addr L p)) by ring.
        apply (HBLKS p n); [exact Hp | exact (UBK p n Hp) | lia]. }
    assert (KW12 : kw (mq_fpw (arg R0 0) (errno_at R0)) mem1 mem2).
    { intros x Hx Wx. rewrite R0a0, Ea0, R0e, ERRv in Hx. unfold mq_fpw, rng in Hx.
      destruct Hx as [Hx|[[N Hx]|Hx]].
      - apply (GLOB x); [mq_unf; lia | exact Wx].
      - destruct (MKB N) as (p & n & Hp & H1 & H2).
        destruct (mr_blocks B _ (aa_laws API) L' A' mem2 md2 p n (x - ptr_addr L p) HM2 (UBK p n Hp) ltac:(lia))
          as ((bb & Hbb) & _).
        rewrite (HSTAB p n Hp (UBK p n Hp)) in Hbb. replace (ptr_addr L p + (x - ptr_addr L p)) with x in Hbb by ring.
        unfold writable_at, wview. rewrite Hbb. discriminate.
      - apply HSCR. right. rewrite ERR1. exact Hx. }
    assert (CORE1 : mq_core R0 mem1 kbs tab nm 0)
      by exact (mq_core_keep R0 mem mem1 _ _ _ _ CORER KB01 (kw_wmono _ _ _ WMm1)).
    assert (CORE2 : mq_core R0 mem2 kbs tab nm 0) by exact (mq_core_keep R0 mem1 mem2 _ _ _ _ CORE1 KB12 KW12).
    set (m2n := normalize_cj rsegs mem2).
    assert (REL2 : mem_rel_cj rsegs mem2 m2n) by (apply mem_rel_cj_normalize; exact RO2).
    assert (MI2n : mem_inv rsegs m2n) by (apply mem_inv_cj_inv, mem_inv_cj_normalize).
    assert (TM2n : task_mem rsegs m2n) by (apply mem_inv_cj_task, mem_inv_cj_normalize).
    assert (KB2n : forall S : Z -> Prop, (forall x, S x -> 0 <= x < TASK_SIZE) -> kb S mem2 m2n)
      by (intros S HS; eapply kb_mono; [exact HS | apply kb_ncj; exact RO2]).
    assert (KW2n : forall S : Z -> Prop, (forall x, S x -> 0 <= x < TASK_SIZE /\ ro_addr rsegs (wa x) = false) ->
        kw S mem2 m2n) by (intros S HS; eapply kw_mono; [exact HS | apply kw_ncj]).
    assert (CORE2n : mq_core R0 m2n kbs tab nm 0) by exact (mq_core_keep R0 mem2 m2n _ _ _ _ CORE2 (KB2n _ FPB) (KW2n _ FPW)).
    (* the stack window and the frame cells in mem2 *)
    assert (WS2 : forall a, spZ regs - MQ_K <= a < spZ regs -> writable_at rsegs mem2 a).
    { intros a Ha. destruct (Z_lt_le_dec a (spZ regs - 32 - FMEMOPEN_K)) as [L1|L1];
        [|destruct (Z_lt_le_dec a (spZ regs - 32)) as [L2|L2]].
      - apply (proj1 (proj2 (HIGH a ltac:(unfold MQ_K, MARK_QUIETLY_K in *; lia) ltac:(lia)))). unfold writable_at.
        apply WMm1. apply HWS. unfold MQ_K, MARK_QUIETLY_K in *. lia.
      - apply HSCR. left. rewrite SP1'. lia.
      - apply (proj1 (proj2 (HIGH a ltac:(unfold MQ_K, MARK_QUIETLY_K in *; lia) ltac:(lia)))). unfold writable_at.
        apply WMm1. apply HWS. unfold MQ_K, MARK_QUIETLY_K in *. lia. }
    assert (STK2n : stk rsegs m2n (spZ regs - MQ_K) (spZ regs - 32)).
    { apply (stk_kbw mem2); [apply mq_stk; [unfold A_IMG_TOP, MARK_QUIETLY_K, MQ_K in *; lia | lia |];
                             intros a Ha; apply WS2; lia | apply KB2n | apply KW2n];
        intros x Hx; rewrite TS; unfold MQ_K, A_IMG_TOP, MARK_QUIETLY_K in *.
      - lia.
      - split; [lia | apply ro_false_hi; lia]. }
    assert (FR2n : rw_cells rsegs m2n (bv_unsigned (reg_get regs 2) + -32)
               [C8 (reg_get regs 18); C8 (reg_get regs 9); C8 (reg_get regs 8); C8 (reg_get regs 1)]).
    { change (bv_unsigned (reg_get regs 2)) with (spZ regs) in *. cbn [cells_size csize Nat.add] in *.
      apply (rw_cells_kbw mem2); [apply (rw_cells_kbw mem1); [apply (rw_cells_kbw m1); [exact FR1 | |] | |] | |];
        cbn [cells_size csize Nat.add].
      - eapply kb_mono; [|exact (kb_rcj mem1 m1 RELF1 RO1)]. intros x Hx. unfold rng in Hx.
        change (Z.of_nat 32) with 32 in Hx. rewrite TS. unfold A_IMG_TOP, MARK_QUIETLY_K in *. lia.
      - apply kw_rcj. exact RELF1.
      - intros x Hx. unfold rng in Hx. change (Z.of_nat 32) with 32 in Hx. unfold A_IMG_TOP, MARK_QUIETLY_K in *.
        exact (proj1 (HIGH x ltac:(lia) ltac:(lia))).
      - intros x Hx Wx. unfold rng in Hx. change (Z.of_nat 32) with 32 in Hx. unfold A_IMG_TOP, MARK_QUIETLY_K in *.
        exact (proj1 (proj2 (HIGH x ltac:(lia) ltac:(lia))) Wx).
      - apply KB2n. intros x Hx. unfold rng in Hx. change (Z.of_nat 32) with 32 in Hx. rewrite TS.
        unfold A_IMG_TOP, MARK_QUIETLY_K in *. lia.
      - apply KW2n. intros x Hx. unfold rng in Hx. change (Z.of_nat 32) with 32 in Hx. rewrite TS.
        unfold A_IMG_TOP, MARK_QUIETLY_K in *. split; [lia | apply ro_false_hi; lia]. }
    assert (MF2n : memfile_k m2n h 0).
    { apply (memfile_k_kbw mem2); [exact MFK | apply KB2n | apply KW2n]; intros x Hx; rewrite TS;
        unfold rng, mf_place_ok in *; mq_unf.
      - lia.
      - destruct Hx as [Hx|Hx]; (split; [lia|]); [destruct PLh as [P|P]; [apply ro_false_lo | apply ro_false_hi]; lia
                                                  | apply ro_false_hi; lia]. }
    assert (GW2n : guard_words m2n).
    { apply (guard_words_kb mem2); [exact GOK2|]. apply KB2n. intros x Hx. rewrite TS. unfold rng, GOT_GUARD, GUARD in Hx. lia. }
    assert (OFL2n : u64_at m2n A_OFL_HEAD h).
    { apply (u64_at_kb mem2).
      - destruct OFL as [[_ BOF] _]. cbn [cells_bytes cbytes] in BOF. rewrite app_nil_r in BOF. exact BOF.
      - apply KB2n. intros x Hx. rewrite TS. unfold rng, A_OFL_HEAD in Hx. lia. }
    assert (H10' : reg_get R2 10 = Z_to_bv 64 h) by exact H10.
    assert (UH : bv_unsigned (reg_get R2 10) = h) by (rewrite H10'; apply unsigned_lit; exact Hh64).
    set (W' := mq_tw (spZ regs) (bv_unsigned (getr regs 10)) A_ERRNO h).
    replace (YK11.getr R1 1) with (Z_to_bv 64 0x15dc8) by (rewrite GR1'; reflexivity).
    assert (QEXT : q_ext (fun s => exists m3, (munch [(A_G_SINK, A_G_SINK + 8); (A_G_SAY, A_G_SAY + 8)] m2n m3
                                                /\ wmono rsegs m2n m3 /\ u64_at m3 A_G_SINK h /\ u64_at m3 A_G_SAY h)
                                    /\ mq_tq R0 m3 W' (mq_tp (bv_unsigned (getr regs 10)) h m3 kbs tab nm) s)).
    { apply (q_ext_ex (fun m3 s => (munch [(A_G_SINK, A_G_SINK + 8); (A_G_SAY, A_G_SAY + 8)] m2n m3
                                     /\ wmono rsegs m2n m3 /\ u64_at m3 A_G_SINK h /\ u64_at m3 A_G_SAY h)
                                   /\ mq_tq R0 m3 W' (mq_tp (bv_unsigned (getr regs 10)) h m3 kbs tab nm) s)).
      intros m3. apply q_ext_and. apply mq_tq_ext. apply mq_tp_ext. }
    eapply (sr_cj fx R2 _ mem2 md2
      (fun s => exists m3, (munch [(A_G_SINK, A_G_SINK + 8); (A_G_SAY, A_G_SAY + 8)] m2n m3 /\ wmono rsegs m2n m3
                            /\ u64_at m3 A_G_SINK h /\ u64_at m3 A_G_SAY h)
                 /\ mq_tq R0 m3 W' (mq_tp (bv_unsigned (getr regs 10)) h m3 kbs tab nm) s)
      _ RO2 Hh2 Hl2).
    { replace (Regs6ss.mkR_of R2) with
        (mkR (reg_get R2 1) (Z_to_bv 64 (bv_unsigned (reg_get regs 2) + -32)) (reg_get regs 3) (reg_get regs 4)
             (reg_get R2 5) (reg_get R2 6) (reg_get R2 7) (reg_get regs 11) (reg_get regs 10) (reg_get R2 10)
             (reg_get R2 11) (reg_get R2 12) (reg_get R2 13) (reg_get R2 14) (reg_get R2 15) (reg_get R2 16)
             (reg_get R2 17) (Z_to_bv 64 474528) (reg_get regs 19) (reg_get regs 20) (reg_get regs 21)
             (reg_get regs 22) (reg_get regs 23) (reg_get regs 24) (reg_get regs 25) (reg_get regs 26)
             (reg_get regs 27) (reg_get R2 28) (reg_get R2 29) (reg_get R2 30) (reg_get R2 31)).
      2: { unfold Regs6ss.mkR_of. f_equal;
           match goal with
           | |- reg_get R2 ?k = _ => let z := eval vm_compute in (bv_unsigned k) in
                exact (rg_pres R1 R2 Rf HPRES GR1' z ltac:(unfold callee_saved; lia))
           | |- _ = reg_get R2 ?k => let z := eval vm_compute in (bv_unsigned k) in
                symmetry; exact (rg_pres R1 R2 Rf HPRES GR1' z ltac:(unfold callee_saved; lia))
           end. }
      apply (mq_mid SAYTO _ QEXT (reg_get R2 1) (Z_to_bv 64 (bv_unsigned (reg_get regs 2) + -32)) (reg_get regs 3)
               (reg_get regs 4) (reg_get R2 5) (reg_get R2 6) (reg_get R2 7) (reg_get regs 11) (reg_get regs 10)
               (reg_get R2 10) (reg_get R2 11) (reg_get R2 12) (reg_get R2 13) (reg_get R2 14) (reg_get R2 15)
               (reg_get R2 16) (reg_get R2 17) (reg_get regs 19) (reg_get regs 20) (reg_get regs 21)
               (reg_get regs 22) (reg_get regs 23) (reg_get regs 24) (reg_get regs 25) (reg_get regs 26)
               (reg_get regs 27) (reg_get R2 28) (reg_get R2 29) (reg_get R2 30) (reg_get R2 31)
               fp_regs fp_csr m2n (spZ regs - MQ_K)).
      - exact MI2n.
      - rewrite SPf. exact STK2n.
      - unfold A_IMG_TOP, MARK_QUIETLY_K, MQ_K in *. lia.
      - rewrite SPf. unfold MQ_K. lia.
      - rewrite SPf. lia.
      - rewrite UH. exact HNZ.
      - intros ra2 w0 w1 w2 c0 c2' c3 c4 c5 c6 c7 w3 w4 w5 w6 m3 MU3 WM3 MI3 ST3 SINK3 SAY3.
        assert (KB3 : forall S : Z -> Prop, (forall x, S x -> 0 <= x < 2 ^ 64 /\ ~ (A_G_SINK <= x < A_G_SINK + 8)
                                               /\ ~ (A_G_SAY <= x < A_G_SAY + 8)) -> kb S m2n m3).
        { intros S HS. eapply kb_munch; [exact MU3|]. intros x Hx. destruct (HS x Hx) as (H1 & H2 & H3).
          split; [exact H1|]. cbn [outside]. tauto. }
        assert (CORE3 : mq_core R0 m3 kbs tab nm 0).
        { apply (mq_core_keep R0 m2n m3 _ _ _ _ CORE2n); [|apply kw_wmono; exact WM3].
          apply KB3. intros x Hx. rewrite R0a0, Ea0 in Hx. unfold mq_fpb, rng in Hx.
          destruct Hx as [Hx|[Hx|[Hx|[N Hx]]]]; [mq_unf; lia | mq_unf; lia | mq_unf; lia|].
          destruct (MK0 N) as (P1 & _ & H2 & _). mq_unf. lia. }
        assert (CORE3h : mq_core R0 m3 kbs tab nm h).
        { destruct CORE3 as (NL3 & IT3 & EO3 & TO3 & SA3 & NO3 & BO3 & KN3 & KT3).
          refine (conj NL3 (conj IT3 (conj _ (conj _ (conj SA3 (conj _ (conj _ (conj KN3 KT3)))))))).
          - apply (mark_errno_ok_sink m3 R0 MQ_K 0 h); [|exact EO3]. rewrite R0e, ERRv.
            unfold apart, A_ERRNO, FILE_BLOCK. unfold mf_place_ok, IMG_LO, IMG_TOP, MemFile.MF_BLOCK in PLh. lia.
          - apply (mark_table_ok_sink m3 R0 MQ_K 0 h tab); [|exact TO3]. intros i n2 ix p Hi Hp.
            destruct (Z_le_gt_dec 0 p) as [P0|P0]; [destruct (Z_lt_ge_dec p (2 ^ 64)) as [P1|P1]|].
            + apply (kept_apart_h h p _ (KT3 i n2 ix p Hi Hp ltac:(lia)) ltac:(lia) PLh FR_lo).
              unfold FILE_BLOCK. unfold MemFile.MF_BLOCK in FR_hi. lia.
            + left. unfold FILE_BLOCK. unfold MemFile.MF_BLOCK in FR_hi. lia.
            + (* a negative p is congruent to the table's in-range pointer, so it lies below 0 *)
              pose proof IT3 as (_ & _ & ITf). destruct (ITf i n2 ix Hi) as (_ & p0 & Hp0 & _ & [Hc _] & _).
              pose proof (u64_at_cong m3 _ p p0 Hp Hp0) as C.
              pose proof (bytes_at_bound rsegs m3 p0 _ Hc) as Bd. rewrite length_app in Bd. cbn [length] in Bd.
              assert (Hm : p mod 2 ^ 64 = p0) by (rewrite C; apply Z.mod_small; lia).
              right. clear - Hm Bd P0 FR_lo. Z.div_mod_to_equations. lia.
          - apply (mark_name_ok_sink m3 R0 MQ_K 0 h nm); [|exact NO3]. intros str Hs.
            pose proof (Z.mod_pos_bound (- (arg R0 1 + Z.of_nat (length str) + 1)) 8 ltac:(lia)) as MB.
            assert (AP : apart h FILE_BLOCK (arg R0 1) (name_span (arg R0 1) str + 7)).
            { apply (kept_apart_h8 h _ _ 7 (KN3 str Hs)); [unfold name_span; lia | lia | exact PLh | exact FR_lo |].
              unfold FILE_BLOCK. unfold MemFile.MF_BLOCK in FR_hi. lia. }
            unfold apart, name_span in *. lia.
          - apply (mark_block_ok_sink m3 R0 MQ_K 0 h); [|exact BO3]. intros N. rewrite R0a0, Ea0 in N |- *.
            destruct (MBLK N) as (q & n & Hq & H1 & H2). rewrite BLK2 in Hq.
            pose proof (blocks_mid_disjoint L' A' mem2 md2 b1 b2 h MemFile.MF_BLOCK q n HM2 BLK1 Hq) as D.
            unfold apart, FILE_BLOCK, MemFile.MF_BLOCK, MK_SIZE in *. lia. }
        eapply evt_mono.
        + apply (mq_tail RW RSM (reg_get regs 1) (reg_get regs 2) (reg_get regs 3) (reg_get regs 4) (reg_get regs 5)
                   (reg_get regs 6) (reg_get regs 7) (reg_get regs 8) (reg_get regs 9) (reg_get regs 10)
                   (reg_get regs 11) (reg_get regs 12) (reg_get regs 13) (reg_get regs 14) (reg_get regs 15)
                   (reg_get regs 16) (reg_get regs 17) (reg_get regs 18) (reg_get regs 19) (reg_get regs 20)
                   (reg_get regs 21) (reg_get regs 22) (reg_get regs 23) (reg_get regs 24) (reg_get regs 25)
                   (reg_get regs 26) (reg_get regs 27) (reg_get regs 28) (reg_get regs 29) (reg_get regs 30)
                   (reg_get regs 31) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m3 kbs tab nm 0).
          * exact MI3.
          * apply (task_mem_munch _ m2n m3 TM2n MU3). intros lo hi Hin. cbn [In] in Hin.
            destruct Hin as [E|[E|[]]]; injection E as <- <-; rewrite TS; mq_unf; lia.
          * exact FRM.
          * change (bv_unsigned (reg_get regs 2)) with (spZ regs). unfold MQ_K, MARK_QUIETLY_K in *. lia.
          * change (bv_unsigned (reg_get regs 2)) with (spZ regs). rewrite TS. lia.
          * exact TPv.
          * rewrite SPf in ST3. change (bv_unsigned (reg_get regs 2)) with (spZ regs).
            replace (spZ regs + -32) with (spZ regs - 32) by lia. exact ST3.
          * apply (rw_cells_kbw m2n); [exact FR2n | | apply kw_wmono; exact WM3].
            apply KB3. intros x Hx. unfold rng in Hx. cbn [cells_size csize Nat.add] in Hx.
            change (Z.of_nat 32) with 32 in Hx. change (bv_unsigned (reg_get regs 2)) with (spZ regs) in Hx.
            mq_unf. unfold MARK_QUIETLY_K in *. lia.
          * rewrite UH. exact CORE3h.
          * exact (frame_apart_gnl_K regs R0 MARK_QUIETLY_K MQ_K R0s ltac:(unfold MQ_K, MARK_QUIETLY_K; lia) FAG).
          * exact NW.
          * exact NOPN.
          * exact NOP.
          * exact NCL.
          * rewrite UH. apply (memfile_k_kbw m2n); [exact MF2n | | apply kw_wmono; exact WM3].
            apply KB3. intros x Hx. unfold rng in Hx. unfold mf_place_ok, IMG_LO, IMG_TOP in PLh.
            mq_unf. lia.
          * exact SAY3.
          * rewrite UH. exact HNZ.
          * rewrite UH. change (bv_unsigned (reg_get regs 2)) with (spZ regs).
            unfold MemFile.MF_BLOCK in FR_hi. unfold FILE_BLOCK, MQ_K, MARK_QUIETLY_K in *. lia.
          * apply (guard_words_kb m2n); [exact GW2n|]. apply KB3. intros x Hx. unfold rng in Hx. mq_unf. lia.
        + intros s Hs. exists m3. rewrite UH in Hs, SINK3, SAY3.
          split; [split; [exact MU3 | split; [exact WM3 | split; [exact SINK3 | exact SAY3]]]|]. exact Hs. }
    intros s0 can ms' (m3 & (MU23 & WM23 & SINK3 & SAY3) & (regs' & Ft & fc' & mf & -> & FRM' & RP & MUT & WMT
      & MIF & TMF & TP))
      REL CJ EQ.
    destruct (ms_back _ _ _ _ _ _ _ _ _ eq_refl REL EQ) as (EMS & RELF & GR & EMM).
    assert (CJF : cj_same rsegs mem2 (ms_mem ms')) by (rewrite EMM; exact CJ).
    set (memf := ms_mem ms') in *.
    set (W2 := (A_G_SINK, A_G_SINK + 8) :: (A_G_SAY, A_G_SAY + 8) :: W').
    assert (MUF : munch W2 mem2 memf).
    { apply (munch_rel_cj rsegs _ mem2 m2n memf mf REL2 RELF CJF).
      apply (munch_trans _ m2n m3 mf).
      - eapply munch_weaken; [|exact MU23]. intros x Hx. unfold W2 in Hx. cbn [outside] in Hx |- *. tauto.
      - eapply munch_weaken; [|exact MUT]. intros x Hx. unfold W2 in Hx. cbn [outside] in Hx. tauto. }
    assert (WMF : wmono rsegs mem2 memf).
    { apply (wmono_rel_cj rsegs mem2 m2n memf mf REL2 RELF CJF). exact (wmono_trans _ _ _ _ WM23 WMT). }
    assert (MLE : mle mf memf) by (apply mle_rcj; exact RELF).
    assert (ROF : ro_agree rsegs memf) by exact (ro_agree_same_cj rsegs mem2 memf RO2 CJF).
    assert (GRk : forall r, YK11.getr (ms_regs ms') r = YK11.getr regs' r) by exact GR.
    assert (G0 : forall r, YK11.getr R0 r = YK11.getr regs r) by (intros r; exact (mkR_of_getr regs r)).
    assert (WCASE2 : forall x, ~ outside W2 x ->
      (A_G_SINK <= x < A_G_SINK + 8) \/ (A_G_SAY <= x < A_G_SAY + 8) \/ ~ outside W' x).
    { intros x Hx. unfold W2 in Hx. cbn [outside] in Hx.
      assert (D1 : (A_G_SINK <= x < A_G_SINK + 8) \/ ~ (A_G_SINK <= x < A_G_SINK + 8)) by lia.
      assert (D2 : (A_G_SAY <= x < A_G_SAY + 8) \/ ~ (A_G_SAY <= x < A_G_SAY + 8)) by lia.
      destruct D1 as [D1|D1]; [left; exact D1|]. destruct D2 as [D2|D2]; [right; left; exact D2|].
      right; right. intros O. apply Hx. exact (conj D1 (conj D2 O)). }
    apply SR_ret.
    exists (mkFP Ft fc'), L', A', (ms_regs ms'), memf, md2, h.
    split.
    { rewrite EMS at 1. change (getr R0 1) with (YK11.getr regs 1). rewrite (kb_ret_pc _ HRA). reflexivity. }
    split; [exact FRM'|].
    split.
    { unfold mq_post_k. rewrite SEGS.
      split.
      { apply (mq_MR_keep L' A' mem2 md2 memf W2 SEGS HM2 MUF WMF). intros x Hx Ho.
        destruct (kb_outside_dec W2 x) as [O|O]; [exact O|]. exfalso.
        destruct (WCASE2 x O) as [H|[H|O']].
        - apply (glob_unowned L' A' mem2 md2 x SEGS HM2); [mq_unf; lia | exact Ho].
        - apply (glob_unowned L' A' mem2 md2 x SEGS HM2); [mq_unf; lia | exact Ho].
        - destruct (mq_tw_cases _ _ _ _ x O') as [H|[H|[H|[H|[H|[N H]]]]]].
          + unfold MQ_K, MARK_QUIETLY_K in *. lia.
          + destruct (blk_facts L' A' mem2 md2 h MemFile.MF_BLOCK x SEGS HM2 INH
                        ltac:(unfold FILE_BLOCK, MemFile.MF_BLOCK in *; lia)) as (O1 & _). exact (O1 Ho).
          + apply (glob_unowned L' A' mem2 md2 x SEGS HM2); [mq_unf; lia | exact Ho].
          + apply (glob_unowned L' A' mem2 md2 x SEGS HM2); [mq_unf; lia | exact Ho].
          + apply (glob_unowned L' A' mem2 md2 x SEGS HM2); [mq_unf; lia | exact Ho].
          + destruct (MKB N) as (p & n & Hp & H1 & H2).
            assert (Hb : In (ptr_addr L' p, n) (blocks L' A'))
              by (unfold blocks; exact (in_map (fun b => (ptr_addr L' (fst b), snd b)) _ _ (UBK p n Hp))).
            rewrite (HSTAB p n Hp (UBK p n Hp)) in Hb.
            destruct (blk_facts L' A' mem2 md2 _ n x SEGS HM2 Hb ltac:(lia)) as (O1 & _). exact (O1 Ho). }
      split; [exact HWF2|]. split; [exact HBD2|]. split; [exact HLE|]. split; [exact HSTAB|].
      split; [intros r Hr; rewrite GRk, (RP r Hr), G0; reflexivity|].
      split; [exact HVM|].
      split.
      { intros a Ha No No' Ns Ne.
        assert (Hr : 0 <= a < 2 ^ 64) by (destruct Ha as [Ha|Ha]; [lia | apply (in_img_rsegs B a SEGS) in Ha; lia]).
        assert (E1 : mbyte rsegs mem1 a = mbyte rsegs mem a /\ (writable_at rsegs mem a <-> writable_at rsegs mem1 a)).
        { assert (O : outside [(bv_unsigned (reg_get regs 2) + -32, bv_unsigned (reg_get regs 2))] a).
          { apply OUT1. intros H. apply Ns. unfold scratch_k. left. unfold MARK_QUIETLY_K in *. lia. }
          split; [exact (KindBGlue.mbyte_munch rsegs _ _ _ _ MUm1 Hr O) | exact (KindBGlue.writable_munch rsegs _ _ _ _ MUm1 Hr O)]. }
        assert (E2 : mbyte rsegs mem2 a = mbyte rsegs mem1 a /\ (writable_at rsegs mem1 a <-> writable_at rsegs mem2 a)).
        { apply FKB; [exact Ha | exact No | exact No' | |].
          - unfold scratch_k. rewrite SP1', ERR1. intros [H|H]; apply Ns; unfold scratch_k.
            + left. unfold FMEMOPEN_K, MARK_QUIETLY_K in *. lia.
            + right. rewrite ERRA. exact H.
          - unfold fmemopen_w_writes. intros [H|H]; apply Ne; unfold mq_writes.
            + right; right; right; right; left. exact H.
            + right; right; right; right; right; right. unfold FILE_BLOCK, MemFile.MF_BLOCK in *. lia. }
        assert (E3 : mbyte rsegs memf a = mbyte rsegs mem2 a /\ (writable_at rsegs mem2 a <-> writable_at rsegs memf a)).
        { destruct (kb_outside_dec W2 a) as [O|O].
          - split; [exact (KindBGlue.mbyte_munch rsegs _ _ _ _ MUF Hr O) | exact (KindBGlue.writable_munch rsegs _ _ _ _ MUF Hr O)].
          - exfalso. destruct (WCASE2 a O) as [H|[H|O']].
            + apply Ne. unfold mq_writes. right; left. exact H.
            + apply Ne. unfold mq_writes. right; right; left. exact H.
            + destruct (mq_tw_cases _ _ _ _ a O') as [H|[H|[H|[H|[H|H]]]]].
              * apply Ns. unfold scratch_k. left. unfold MQ_K, MARK_QUIETLY_K in *. lia.
              * apply Ne. unfold mq_writes. right; right; right; right; right; right. exact H.
              * apply Ne. unfold mq_writes. right; right; right; left. exact H.
              * apply Ns. unfold scratch_k. right. rewrite ERRA. exact H.
              * apply Ne. unfold mq_writes. left. exact H.
              * apply Ne. unfold mq_writes. right; right; right; right; right; left. exact H. }
        destruct E1 as [E1a E1b]. destruct E2 as [E2a E2b]. destruct E3 as [E3a E3b].
        split; [rewrite E3a, E2a, E1a; reflexivity | tauto]. }
      split.
      { intros p n i Hin Hin' Hi Nx.
        assert (Hb : In (ptr_addr L p, n) (blocks L A))
          by (unfold blocks; exact (in_map (fun b => (ptr_addr L (fst b), snd b)) _ _ Hin)).
        destruct (blk_facts L A mem md _ n (ptr_addr L p + i) SEGS HM Hb ltac:(lia)) as (_ & Hrx & H1 & H2 & _).
        assert (Hr : 0 <= ptr_addr L p + i < 2 ^ 64) by lia.
        assert (E1 : mbyte rsegs mem1 (ptr_addr L p + i) = mbyte rsegs mem (ptr_addr L p + i)).
        { apply (KindBGlue.mbyte_munch rsegs _ _ _ _ MUm1 Hr). apply OUT1. unfold A_IMG_TOP, MARK_QUIETLY_K in *. lia. }
        assert (E2 : mbyte rsegs mem2 (ptr_addr L p + i) = mbyte rsegs mem1 (ptr_addr L p + i))
          by exact (HBLKS p n i Hin Hin' Hi).
        assert (E3 : mbyte rsegs memf (ptr_addr L p + i) = mbyte rsegs mem2 (ptr_addr L p + i)).
        { destruct (kb_outside_dec W2 (ptr_addr L p + i)) as [O|O].
          - exact (KindBGlue.mbyte_munch rsegs _ _ _ _ MUF Hr O).
          - exfalso. destruct (WCASE2 _ O) as [H|[H|O']]; [mq_unf; lia | mq_unf; lia |].
            destruct (mq_tw_cases _ _ _ _ _ O') as [H|[H|[H|[H|[H|H]]]]].
            + unfold MQ_K, MARK_QUIETLY_K in *. lia.
            + apply Nx. right. exact H.
            + mq_unf. lia.
            + mq_unf. lia.
            + mq_unf. lia.
            + apply Nx. left. exact H. }
        rewrite E3, E2, E1. reflexivity. }
      intros a [Ha|Ha]; unfold writable_at; apply WMF.
      - apply WS2. unfold MQ_K, MARK_QUIETLY_K in *. lia.
      - apply HSCR. right. rewrite ERR1. rewrite ERRA in Ha. exact Ha. }
    split; [exact ROF|].
    assert (OUTW' : forall x, (A_G_SINK <= x < A_G_SINK + 8) \/ (A_G_SAY <= x < A_G_SAY + 8) -> outside W' x).
    { intros x Hx. destruct (kb_outside_dec W' x) as [O|O]; [exact O|]. exfalso.
      destruct (mq_tw_cases _ _ _ _ x O) as [H|[H|[H|[H|[H|[N H]]]]]]; mq_unf; unfold MARK_QUIETLY_K in *; try lia;
        destruct (MK0 N) as (P1 & _); mq_unf; lia. }
    split.
    { apply (u64_at_mle mf memf); [|exact MLE]. apply (u64_at_kb m3); [exact SINK3|].
      eapply kb_munch; [exact MUT|]. intros x Hx. unfold rng in Hx. split; [mq_unf; lia | apply OUTW'; left; exact Hx]. }
    split.
    { apply (u64_at_mle mf memf); [|exact MLE]. apply (u64_at_kb m3); [exact SAY3|].
      eapply kb_munch; [exact MUT|]. intros x Hx. unfold rng in Hx. split; [mq_unf; lia | apply OUTW'; right; exact Hx]. }
    split.
    { assert (OUTO : forall x, A_OFL_HEAD <= x < A_OFL_HEAD + 8 -> outside W' x).
      { intros x Hx. destruct (kb_outside_dec W' x) as [O|O]; [exact O|]. exfalso.
        destruct (mq_tw_cases _ _ _ _ x O) as [H|[H|[H|[H|[H|[N H]]]]]]; mq_unf; unfold MARK_QUIETLY_K, A_OFL_HEAD in *;
          try lia; destruct (MK0 N) as (P1 & _); mq_unf; lia. }
      apply (u64_at_mle mf memf); [|exact MLE]. apply (u64_at_kb m3).
      - apply (u64_at_kb m2n); [exact OFL2n|]. eapply kb_munch; [exact MU23|]. intros x Hx. unfold rng in Hx.
        split; [unfold A_OFL_HEAD in Hx; lia | cbn [outside]; mq_unf; unfold A_OFL_HEAD in Hx; lia].
      - eapply kb_munch; [exact MUT|]. intros x Hx. unfold rng in Hx.
        split; [unfold A_OFL_HEAD in Hx; lia | apply OUTO; exact Hx]. }
    split; [exact HNZ|].
    destruct TP as ((k' & Hk & MK') & TP2 & TP3).
    split; [exists k'; split; [unfold MARK_LINE_MAX in *; lia | exact (memfile_k_mle mf memf h k' MK' MLE)]|].
    split; [intros C; exfalso; exact (C eq_refl)|].
    split; [intros _; split; [exact FRESH|]; split; [exists b1, b2; split; [exact BLK1 | exact BLK2]|];
            split; [exact RES'|]; split; [exact UBK | exact INIT]|].
    split.
    { intros Z0. destruct (TP2 Z0) as (R10 & NLK). split; [rewrite GR; exact R10 | exact (nlk_at_mle mf memf kbs NLK MLE)]. }
    intros N gbs MG.
    assert (MG3 : marks_at m3 (bv_unsigned (getr regs 10)) gbs).
    { assert (SUB : forall x, rng (bv_unsigned (getr regs 10)) MK_SIZE x -> mq_fpb (arg R0 0) x)
        by (intros x Hx; rewrite R0a0, Ea0; right; right; right; split; [exact N | exact Hx]).
      assert (SUBW : forall x, rng (bv_unsigned (getr regs 10)) MK_SIZE x -> mq_fpw (arg R0 0) (errno_at R0) x)
        by (intros x Hx; rewrite R0a0, Ea0; right; left; split; [exact N | exact Hx]).
      apply (marks_at_kbw m2n); [| | apply kw_wmono; exact WM23].
      2: { eapply kb_munch; [exact MU23|]. intros x Hx. unfold rng in Hx. destruct (MK0 N) as (P1 & _ & H2 & _).
           split; [lia|]. cbn [outside]. mq_unf. lia. }
      apply (marks_at_kbw mem2); [| eapply kb_mono; [exact SUB | exact (KB2n _ FPB)]
                                   | eapply kw_mono; [exact SUBW | exact (KW2n _ FPW)]].
      apply (marks_at_kbw mem1); [| eapply kb_mono; [exact SUB | exact KB12] | eapply kw_mono; [exact SUBW | exact KW12]].
      apply (marks_at_kbw mem); [exact MG | eapply kb_mono; [exact SUB | exact KB01] | apply kw_wmono; exact WMm1]. }
    destruct (TP3 N gbs MG3) as (R10 & (gbs' & G1 & G2 & G3 & G4) & (kbs' & K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8
      & K9 & K10 & K11 & K12 & K13)).
    split; [rewrite GR; exact R10|].
    split; [exists gbs'; exact (conj (marks_at_mle mf memf _ gbs' G1 MLE) (conj G2 (conj G3 G4)))|].
    exists kbs'. refine (conj (nlk_at_mle mf memf kbs' K1 MLE) (conj K2 (conj K3 (conj K4 (conj K5
      (conj (iftab_at_mle mf memf kbs' tab K6 MLE) (conj K7 (conj K8 (conj K9 (conj K10 (conj K11 (conj K12 K13)))))))))))).
  - destruct (SN S0) as ((k & MF) & SAY & OFLs & SFB).
    pose proof (memfile_k_place mem _ k MF) as PL.
    pose proof MF as ((Hf0 & Hf1 & _) & _).
    pose proof (FBLK S0) as INF.
    assert (SRng : 0 <= sink < 2 ^ 64) by (unfold MemFile.MF_BLOCK in Hf1; lia).
    pose proof (USK SRng) as US.
    assert (MFm0 : memfile_k m0 sink k).
    { apply (memfile_k_kbw mem); [exact MF | apply KB0 | apply KW0]; intros x Hx; rewrite TS;
        unfold rng, mf_place_ok in *; mq_unf; unfold MARK_QUIETLY_K in *.
      - lia.
      - destruct Hx as [Hx|Hx]; (split; [lia|]); [destruct PL as [PL|PL]; [apply ro_false_lo | apply ro_false_hi]; lia
                                                  | apply ro_false_hi; lia]. }
    assert (SAY0 : u64_at m0 A_G_SAY sink).
    { apply (u64_at_kb mem); [exact SAY|]. apply KB0. intros x Hx. rewrite TS. unfold rng, A_G_SAY in Hx. lia. }
    set (W := mq_tw (spZ regs) (bv_unsigned (getr regs 10)) A_ERRNO sink).
    eapply (sr_cj fx regs _ mem md
      (fun s0 => exists m1, munch [(bv_unsigned (reg_get regs 2) + -32, bv_unsigned (reg_get regs 2))] m0 m1
                   /\ wmono rsegs m0 m1 /\ mq_tq R0 m1 W (mq_tp (bv_unsigned (getr regs 10)) sink m1 kbs tab nm) s0)
      _ RO Hh Hl).
    { unfold R0, Regs6ss.mkR_of, MARK_QUIETLY.
      apply (mq_pro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m0 (spZ regs - MQ_K)
               (Z_to_bv 64 sink)); [exact MI0 | exact STK0 | change (bv_unsigned (reg_get regs 2)) with (spZ regs); unfold MQ_K; lia
                                    | unfold A_IMG_TOP, MARK_QUIETLY_K, MQ_K in *; lia | exact H63 | exact GS0 |].
      intros m1 MU1 WM1 MI1 ST1 FR1. split.
      - intros Hne. eapply evt_mono.
        + apply (mq_tail RW RSM (reg_get regs 1) (reg_get regs 2) (reg_get regs 3) (reg_get regs 4) (reg_get regs 5)
                   (reg_get regs 6) (reg_get regs 7) (reg_get regs 8) (reg_get regs 9) (reg_get regs 10)
                   (reg_get regs 11) (reg_get regs 12) (reg_get regs 13) (reg_get regs 14) (reg_get regs 15)
                   (reg_get regs 16) (reg_get regs 17) (reg_get regs 18) (reg_get regs 19) (reg_get regs 20)
                   (reg_get regs 21) (reg_get regs 22) (reg_get regs 23) (reg_get regs 24) (reg_get regs 25)
                   (reg_get regs 26) (reg_get regs 27) (reg_get regs 28) (reg_get regs 29) (reg_get regs 30)
                   (reg_get regs 31) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 kbs tab nm k).
          * exact MI1.
          * apply (task_mem_munch _ m0 m1 TM0 MU1). intros lo hi Hin. cbn [In] in Hin.
            destruct Hin as [E|[]]. injection E as <- <-. change (bv_unsigned (reg_get regs 2)) with (spZ regs). lia.
          * exact FRM.
          * change (bv_unsigned (reg_get regs 2)) with (spZ regs). unfold MQ_K, MARK_QUIETLY_K in *. lia.
          * change (bv_unsigned (reg_get regs 2)) with (spZ regs). rewrite TS. lia.
          * exact TPv.
          * exact ST1.
          * exact FR1.
          * rewrite US. exact (mq_core_keep R0 m0 m1 _ _ _ _ CORE0 (KBP m1 MU1) (kw_wmono _ _ _ WM1)).
          * exact (frame_apart_gnl_K regs R0 MARK_QUIETLY_K MQ_K R0s ltac:(unfold MQ_K, MARK_QUIETLY_K; lia) FAG).
          * exact NW.
          * exact NOPN.
          * exact NOP.
          * exact NCL.
          * rewrite US. apply (memfile_k_kbw m0); [exact MFm0 | | apply kw_wmono; exact WM1].
            eapply kb_munch; [exact MU1|]. intros x Hx. change (bv_unsigned (reg_get regs 2)) with (spZ regs).
            unfold rng in Hx. split; [mq_unf; lia | cbn [outside]; mq_unf; unfold MARK_QUIETLY_K in *; split; [lia | exact I]].
          * rewrite US. apply (u64_at_kb m0); [exact SAY0|].
            eapply kb_munch; [exact MU1|]. intros x Hx. change (bv_unsigned (reg_get regs 2)) with (spZ regs).
            unfold rng in Hx. split; [mq_unf; lia | cbn [outside]; mq_unf; unfold MARK_QUIETLY_K in *; split; [lia | exact I]].
          * rewrite US. exact S0.
          * rewrite US. change (bv_unsigned (reg_get regs 2)) with (spZ regs). unfold MQ_K, MARK_QUIETLY_K in *. lia.
          * apply (guard_words_kb m0); [exact GW0|]. eapply kb_munch; [exact MU1|]. intros x Hx.
            change (bv_unsigned (reg_get regs 2)) with (spZ regs).
            unfold rng in Hx. split; [mq_unf; lia | cbn [outside]; mq_unf; unfold MARK_QUIETLY_K in *; split; [lia | exact I]].
        + intros s Hs. exists m1. split; [exact MU1|]. split; [exact WM1|].
          rewrite US in Hs. exact Hs.
      - intros Heq. exfalso. apply S0. apply bv_eqb_true in Heq. apply (f_equal bv_unsigned) in Heq.
        rewrite US in Heq. exact Heq. }
    intros s0 can ms' (m1 & MU01 & WM01 & (regs' & Ft & fc' & mf & -> & FRM' & RP & MUT & WMT & MIF & TMF & TP))
      REL CJ EQ.
    destruct (ms_back _ _ _ _ _ _ _ _ _ eq_refl REL EQ) as (EMS & RELF & GR & EMM).
    assert (CJF : cj_same rsegs mem (ms_mem ms')) by (rewrite EMM; exact CJ).
    set (memf := ms_mem ms') in *.
    assert (REL0 : mem_rel_cj rsegs mem m0) by (apply mem_rel_cj_normalize; exact RO).
    assert (MUF : munch W mem memf).
    { apply (munch_rel_cj rsegs _ mem m0 memf mf REL0 RELF CJF).
      apply (munch_trans _ m0 m1 mf); [| exact MUT].
      eapply munch_weaken; [|exact MU01]. intros x Hx. unfold W, mq_tw in Hx. cbn [outside] in Hx |- *.
      destruct Hx as (H1 & _). change (bv_unsigned (reg_get regs 2)) with (spZ regs).
      split; [unfold MQ_K in *; lia | exact I]. }
    assert (WMF : wmono rsegs mem memf).
    { apply (wmono_rel_cj rsegs mem m0 memf mf REL0 RELF CJF). exact (wmono_trans _ _ _ _ WM01 WMT). }
    assert (MLE : mle mf memf) by (apply mle_rcj; exact RELF).
    assert (ROF : ro_agree rsegs memf) by exact (ro_agree_same_cj rsegs mem memf RO CJF).
    assert (GRk : forall r, YK11.getr (ms_regs ms') r = YK11.getr regs' r) by exact GR.
    assert (G0 : forall r, YK11.getr R0 r = YK11.getr regs r) by (intros r; exact (mkR_of_getr regs r)).
    (* every byte the run writes is the frame's scratch or the footprint mq_writes names *)
    assert (WCASE : forall x, ~ outside W x ->
       (spZ regs - MQ_K <= x < spZ regs) \/ (sink <= x < sink + FILE_BLOCK)
       \/ (A_G_SAID <= x < A_G_SAID + SAID_SIZE) \/ (A_ERRNO <= x < A_ERRNO + 4)
       \/ (A_G_NL <= x < A_G_NL + NK_N_SENT + 4)
       \/ (bv_unsigned (getr regs 10) <> 0 /\ bv_unsigned (getr regs 10) <= x < bv_unsigned (getr regs 10) + MK_SIZE))
      by (intros x Hx; exact (mq_tw_cases _ _ _ _ x Hx)).
    assert (OWN : forall x, 0 <= x < YM05.alloc_ceiling -> owned B L A x -> outside W x).
    { intros x Hx Ho. destruct (kb_outside_dec W x) as [O|O]; [exact O|]. exfalso.
      destruct (WCASE x O) as [H|[H|[H|[H|[H|[N H]]]]]].
      - unfold MQ_K, MARK_QUIETLY_K in *. lia.
      - destruct (blk_facts L A mem md sink FILE_SIZE x SEGS HM INF ltac:(unfold FILE_SIZE, FILE_BLOCK in *; lia))
          as (O1 & _). exact (O1 Ho).
      - apply (glob_unowned L A mem md x SEGS HM); [mq_unf; lia | exact Ho].
      - apply (glob_unowned L A mem md x SEGS HM); [mq_unf; lia | exact Ho].
      - apply (glob_unowned L A mem md x SEGS HM); [mq_unf; lia | exact Ho].
      - destruct (MK0 N) as (_ & _ & _ & HX). exact (proj1 (HX x H) Ho). }
    apply SR_ret.
    exists (mkFP Ft fc'), L, A, (ms_regs ms'), memf, md, sink.
    split.
    { rewrite EMS at 1. change (getr R0 1) with (YK11.getr regs 1). rewrite (kb_ret_pc _ HRA). reflexivity. }
    split; [exact FRM'|].
    split.
    { unfold mq_post_k. rewrite SEGS.
      split; [exact (mq_MR_keep L A mem md memf W SEGS HM MUF WMF OWN)|].
      split; [exact HWF|]. split; [exact HBD|]. split; [apply layout_le_refl|].
      split; [intros; reflexivity|].
      split; [intros r Hr; rewrite GRk, (RP r Hr), G0; reflexivity|].
      split; [exists (m_vmmaps md); symmetry; apply kb_vm_id|].
      split.
      { intros a Ha No No' Ns Ne.
        assert (Hr : 0 <= a < 2 ^ 64) by (destruct Ha as [Ha|Ha]; [lia | apply (in_img_rsegs B a SEGS) in Ha; lia]).
        destruct (kb_outside_dec W a) as [O|O].
        - split; [exact (KindBGlue.mbyte_munch rsegs _ _ _ _ MUF Hr O) | exact (KindBGlue.writable_munch rsegs _ _ _ _ MUF Hr O)].
        - exfalso. destruct (WCASE a O) as [H|[H|[H|[H|[H|H]]]]].
          + apply Ns. unfold scratch_k. left. unfold MQ_K, MARK_QUIETLY_K in *. lia.
          + apply Ne. unfold mq_writes. right; right; right; right; right; right. exact H.
          + apply Ne. unfold mq_writes. right; right; right; left. exact H.
          + apply Ns. unfold scratch_k. right. rewrite ERRA. exact H.
          + apply Ne. unfold mq_writes. left. exact H.
          + apply Ne. unfold mq_writes. right; right; right; right; right; left. exact H. }
      split.
      { intros p n i Hin Hin' Hi Nx.
        assert (Hb : In (ptr_addr L p, n) (blocks L A))
          by (unfold blocks; exact (in_map (fun b => (ptr_addr L (fst b), snd b)) _ _ Hin)).
        destruct (blk_facts L A mem md _ n (ptr_addr L p + i) SEGS HM Hb ltac:(lia)) as (_ & Hrx & H1 & H2 & _).
        destruct (kb_outside_dec W (ptr_addr L p + i)) as [O|O].
        - apply (KindBGlue.mbyte_munch rsegs _ _ _ _ MUF); [lia | exact O].
        - exfalso. destruct (WCASE _ O) as [H|[H|[H|[H|[H|H]]]]].
          + unfold MQ_K, MARK_QUIETLY_K in *. lia.
          + apply Nx. right. exact H.
          + mq_unf. lia.
          + mq_unf. lia.
          + mq_unf. lia.
          + apply Nx. left. exact H. }
      intros a [Ha|Ha]; unfold writable_at; apply WMF; [apply HWS | apply HERR]; exact Ha. }
    split; [exact ROF|].
    assert (OUTG : forall x, (A_G_SINK <= x < A_G_SINK + 8) \/ (A_G_SAY <= x < A_G_SAY + 8) -> outside W x).
    { intros x Hx. destruct (kb_outside_dec W x) as [O|O]; [exact O|]. exfalso.
      destruct (WCASE x O) as [H|[H|[H|[H|[H|[N H]]]]]]; mq_unf; unfold MARK_QUIETLY_K in *; try lia;
        destruct (MK0 N) as (P1 & _); mq_unf; lia. }
    split.
    { apply (u64_at_kb mem); [exact GSK|]. eapply kb_munch; [exact MUF|]. intros x Hx. unfold rng in Hx.
      split; [mq_unf; lia | apply OUTG; left; exact Hx]. }
    split.
    { apply (u64_at_kb mem); [exact SAY|]. eapply kb_munch; [exact MUF|]. intros x Hx. unfold rng in Hx.
      split; [mq_unf; lia | apply OUTG; right; exact Hx]. }
    split.
    { assert (OUTO : forall x, A_OFL_HEAD <= x < A_OFL_HEAD + 8 -> outside W x).
      { intros x Hx. destruct (kb_outside_dec W x) as [O|O]; [exact O|]. exfalso.
        destruct (WCASE x O) as [H|[H|[H|[H|[H|[N H]]]]]]; mq_unf; unfold MARK_QUIETLY_K, A_OFL_HEAD in *; try lia;
          destruct (MK0 N) as (P1 & _); mq_unf; lia. }
      apply (u64_at_kb mem); [exact OFLs|]. eapply kb_munch; [exact MUF|]. intros x Hx. unfold rng in Hx.
      split; [unfold A_OFL_HEAD in Hx; lia | apply OUTO; exact Hx]. }
    split; [exact S0|].
    destruct TP as ((k' & Hk & MK') & TP2 & TP3).
    split; [exists k'; split; [unfold MARK_LINE_MAX in *; lia | exact (memfile_k_mle mf memf sink k' MK' MLE)]|].
    split; [intros _; split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity | exact RES]|].
    split; [intros E; exfalso; exact (S0 E)|].
    split.
    { intros Z0. destruct (TP2 Z0) as (R10 & NLK). split.
      - change (getr (ms_regs ms') 10) with (getr (ms_regs ms') 10). rewrite GR. exact R10.
      - exact (nlk_at_mle mf memf kbs NLK MLE). }
    intros N gbs MG.
    assert (MG1 : marks_at m1 (bv_unsigned (getr regs 10)) gbs).
    { destruct (MK0 N) as (P1 & H1 & H2 & _).
      apply (marks_at_kbw m0).
      - apply (marks_at_kbw mem); [exact MG | apply KB0 | apply KW0]; intros x Hx; unfold rng in Hx; rewrite TS.
        + mq_unf. lia.
        + split; [mq_unf; lia|]. destruct P1 as [P1|P1]; [apply ro_false_lo | apply ro_false_hi]; mq_unf; lia.
      - eapply kb_munch; [exact MU01|]. intros x Hx. unfold rng in Hx. specialize (MKF N).
        change (bv_unsigned (reg_get regs 2)) with (spZ regs).
        split; [mq_unf; lia | cbn [outside]; mq_unf; unfold MARK_QUIETLY_K in *; split; [lia | exact I]].
      - apply kw_wmono. exact WM01. }
    destruct (TP3 N gbs MG1) as (R10 & (gbs' & G1 & G2 & G3 & G4) & (kbs' & K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8
      & K9 & K10 & K11 & K12 & K13)).
    split; [rewrite GR; exact R10|].
    split; [exists gbs'; exact (conj (marks_at_mle mf memf _ gbs' G1 MLE) (conj G2 (conj G3 G4)))|].
    exists kbs'. refine (conj (nlk_at_mle mf memf kbs' K1 MLE) (conj K2 (conj K3 (conj K4 (conj K5
      (conj (iftab_at_mle mf memf kbs' tab K6 MLE) (conj K7 (conj K8 (conj K9 (conj K10 (conj K11 (conj K12 K13)))))))))))).
Qed.

End SR.

(* closed over the released walk of reac_served_say_to (lib/Prog/reac_served_say_to.v); fmemopen, rewind and
   reac_served_mark stay hypotheses, with the frame's pins and AllocExtra *)
Theorem mark_quietly_closed {fx : YK11.FPState} {rc : YM05.RunCeil} (B : malloc_syms) (API : AllocAPI B) :
  mq_pins B -> AllocExtra B (aa_MR API) ->
  fmemopen_w_contract B API -> rewind_contract -> reac_served_mark_contract -> mark_quietly_contract B API.
Proof.
  intros PINS AX FMO RW RSM.
  exact (mark_quietly_holds B API PINS AX FMO reac_served_say_to.reac_served_say_to_holds RW RSM).
Qed.
