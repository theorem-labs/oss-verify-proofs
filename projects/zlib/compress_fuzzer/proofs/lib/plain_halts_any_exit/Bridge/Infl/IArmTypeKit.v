(** * Bridge.Infl.IArmTypeKit — the shared kit of pairs I7 (TYPE, TYPEDO) and I8 (STORED,
    COPY_, COPY).

    [icore] carried across each move these arms make:
    - a bit-reader move: S5's [wbr w b'] against RT's [qset_br q b'] ([icore_wbr]), and the
      [IBits] macro equations restated against an [icore] hypothesis ([icore_needbits],
      [icore_dropbits], [icore_bytebits], [icore_initbits], [icore_bits], [icore_hold]);
    - a state write: S5's [iset_mode]/[iset_last]/[iset_length]/[fixedtables] against RT's
      [qmode]/[set_last]/[set_length]/[fixedtables] ([icore_mode], [icore_last],
      [icore_length], [icore_fixed]), all through [icore_st];
    - the per-trip outcomes ([step_leave_ok], [step_bad_ok], [step_cont_ok]) and the [imode]
      cases these arms end in. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require InflateState InflateArms.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Base ZBitsIn Inflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge Require Import IRelArr IRelInfl.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge Require S5IFields.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.Infl Require Import IInv IBits.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

(** Split conjunctions (never [<->]), closing each piece by an assumption when one fits. *)
Ltac csplit := repeat (first [assumption | match goal with |- _ /\ _ => split end]).

(** Reduce S5's monad up to the next macro (a stuck [abind] is left folded), and step over
    a macro with its equation [E : macro w = ARun v w']. *)
Ltac s5red := cbn [IS.abind IS.gs IS.gr IS.us IS.uc IS.ur IS.aret IS.aleave IA.set_mode].
Ltac s5step E := rewrite (abind_ARun _ _ _ _ _ E); s5red.

(** The flush tests both models make, at [FL = Z_NO_FLUSH]. *)
Lemma fl_trees_s5 : (IS.iv_flush_exits IS.ivar_ref && (FL =? Z_TREES)) = false.
Proof. reflexivity. Qed.
Lemma fl_trees_rt : (FL =? RI.Z_TREES) = false.
Proof. reflexivity. Qed.
Lemma fl_type_s5 : (IS.iv_flush_exits IS.ivar_ref && ((FL =? Z_BLOCK) || (FL =? Z_TREES))) = false.
Proof. reflexivity. Qed.
Lemma fl_type_rt : ((FL =? RBa.Z_BLOCK) || (FL =? RI.Z_TREES)) = false.
Proof. reflexivity. Qed.

(** S5's [wrap32] and RT's [u32] agree on all of [Z]. *)
Lemma wrap32_u32 : forall x, wrap32 x = RBa.u32 x.
Proof. intros x. rewrite wrap32_mod. reflexivity. Qed.

Ltac icore_destr H :=
  unfold icore, iw_rel in H; cbv zeta in H;
  destruct H as ((?Hcore & ?Hh & ?Hbt & ?Hn & ?Hv & ?Hn0 & ?Hv0 & ?Hlen & ?Hinr & ?Hput & ?Hleft
                  & ?Hp0 & ?Hl0 & ?Hol & ?Hor & ?Hz & ?Hi & ?Ho & ?Hr)
                 & ?Hret & ?Hbr & ?Hhr & ?H8 & ?Hin & ?Hot & ?Hpl & ?Hnv & ?Hout & ?Htot & ?Hstot
                 & ?Hwrap & ?Hwb & ?Hhd & ?Hsane & ?Hws & ?Hwh & ?Hwn & ?Hwin & ?Hfl & ?Hcodes & ?Hwbyte & ?Hobyte).

(* ------------------------------------------------------------------------- *)
(* Reading icore                                                             *)
(* ------------------------------------------------------------------------- *)

Lemma icore_core : forall w q, icore w q -> ist_core_rel (IS.w_s w) (RI.q_st q).
Proof. intros w q H. icore_destr H. exact Hcore. Qed.

Lemma icore_ret : forall w q, icore w q -> RI.q_ret q = RBa.Z_OK.
Proof. intros w q H. icore_destr H. exact Hret. Qed.

Lemma icore_b8 : forall w q, icore w q -> RB.br_bits (RI.q_br q) <= 8 * RB.br_next (RI.q_br q).
Proof. intros w q H. icore_destr H. rewrite <- Hbt, <- Hn. exact H8. Qed.

Lemma icore_next0 : forall w q, icore w q -> 0 <= RB.br_next (RI.q_br q).
Proof. intros w q H. icore_destr H. rewrite <- Hn. exact Hn0. Qed.

Lemma icore_flags : forall w q, icore w q ->
  IS.is_mode (IS.w_s w) <> IS.HEAD -> IS.is_flags (IS.w_s w) = 0 /\ IS.is_check (IS.w_s w) = 1.
Proof. intros w q H. icore_destr H. exact Hfl. Qed.

Lemma icore_codes : forall w q, icore w q -> forall i, code_rng (RI.t_codes (RI.s_tab (RI.q_st q)) i).
Proof. intros w q H. icore_destr H. exact Hcodes. Qed.

Lemma icore_mode_eq : forall w q, icore w q -> IS.is_mode (IS.w_s w) = RI.m_val (RI.q_mode q).
Proof. intros w q H. exact (proj1 (proj1 (icore_core w q H))). Qed.

Lemma icore_last_eq : forall w q, icore w q ->
  IS.is_last (IS.w_s w) = RI.h_last (RI.s_hdr (RI.q_st q)).
Proof. intros w q H. exact (proj1 (proj2 (proj1 (icore_core w q H)))). Qed.

Lemma icore_length_eq : forall w q, icore w q ->
  IS.is_length (IS.w_s w) = RI.u_length (RI.s_cur (RI.q_st q)).
Proof. intros w q H. exact (proj1 (proj1 (proj2 (proj2 (icore_core w q H))))). Qed.

Lemma icore_mode_nh : forall w q, icore w q -> RI.q_mode q <> RI.M_HEAD ->
  IS.is_mode (IS.w_s w) <> IS.HEAD.
Proof.
  intros w q H Hq E. apply Hq. apply RI.m_val_inj.
  rewrite <- (icore_mode_eq w q H). exact E.
Qed.

(* ------------------------------------------------------------------------- *)
(* Outcomes and modes                                                        *)
(* ------------------------------------------------------------------------- *)

Lemma ok_ne_end : RBa.Z_OK <> RBa.Z_STREAM_END.
Proof. unfold RBa.Z_OK, RBa.Z_STREAM_END. discriminate. Qed.

Lemma step_leave_ok : forall sr q, RI.q_ret q = RBa.Z_OK -> step_ok sr (RI.InfLeave q).
Proof. intros sr q H. unfold step_ok. intros E. rewrite H in E. exfalso. exact (ok_ne_end E). Qed.

Lemma step_bad_ok : forall sr q, RI.q_mode q = RI.M_BAD -> step_ok sr (RI.InfCont q).
Proof. intros sr q H. unfold step_ok. intros E. contradiction. Qed.

Lemma step_cont_ok : forall w' q', inv w' q' -> step_ok (IS.ARun tt w') (RI.InfCont q').
Proof. intros w' q' H. unfold step_ok. intros _. exists w'. split; [reflexivity | exact H]. Qed.

Lemma imode_check : forall w q, RI.q_mode q = RI.M_CHECK -> imode w q.
Proof. intros w q E. unfold imode. rewrite E. exact I. Qed.
Lemma imode_stored : forall w q, RI.q_mode q = RI.M_STORED -> imode w q.
Proof. intros w q E. unfold imode. rewrite E. exact I. Qed.
Lemma imode_table : forall w q, RI.q_mode q = RI.M_TABLE -> imode w q.
Proof. intros w q E. unfold imode. rewrite E. exact I. Qed.
Lemma imode_type : forall w q, RI.q_mode q = RI.M_TYPE -> imode w q.
Proof. intros w q E. unfold imode. rewrite E. exact I. Qed.
Lemma imode_len_ : forall w q, RI.q_mode q = RI.M_LEN_ -> tviews_blk w q -> imode w q.
Proof. intros w q E H. unfold imode. rewrite E. exact H. Qed.
Lemma imode_copy : forall w q, RI.q_mode q = RI.M_COPY ->
  0 <= IS.is_length (IS.w_s w) < 65536 -> imode w q.
Proof. intros w q E H. unfold imode. rewrite E. exact H. Qed.
Lemma imode_copy_ : forall w q, RI.q_mode q = RI.M_COPY_ ->
  0 <= IS.is_length (IS.w_s w) < 65536 -> imode w q.
Proof. intros w q E H. unfold imode. rewrite E. exact H. Qed.

(* ------------------------------------------------------------------------- *)
(* Bit-reader moves                                                          *)
(* ------------------------------------------------------------------------- *)

Lemma brel_wset_s : forall w s b, brel w b -> brel (IS.wset_s w s) b.
Proof. intros w s b H. unfold brel in *. cbv zeta in *. autorewrite with s5w. exact H. Qed.

Lemma icore_wbr : forall w q b',
  icore w q -> brel (wbr w b') b' ->
  RB.br_in b' = RB.br_in (RI.q_br q) ->
  RB.br_next b' + RB.br_have b' = RB.br_next (RI.q_br q) + RB.br_have (RI.q_br q) ->
  RB.br_bits b' <= 8 * RB.br_next b' ->
  icore (wbr w b') (RI.qset_br q b').
Proof.
  intros w q b' H Hb Hin' Hsum H8'.
  destruct Hb as (_ & _ & _ & _ & Hn0' & Hv0' & Hnv' & Hbt' & Hhr' & _).
  rewrite wbr_r in Hn0', Hv0', Hnv', Hbt', Hhr'.
  cbn [setbr IS.ir_next IS.ir_have IS.ir_bits IS.ir_hold] in Hn0', Hv0', Hnv', Hbt', Hhr'.
  icore_destr H.
  unfold icore, iw_rel. cbv zeta.
  rewrite wbr_s, wbr_c, wbr_r. setbr_cbn.
  cbn [RI.qset_br RI.q_st RI.q_z RI.q_br RI.q_ob RI.q_in RI.q_out RI.q_ret].
  rewrite Hin'.
  csplit; try reflexivity; lia.
Qed.

Lemma nb_go_inv : forall f n b b', RI.inf_nb_go f n b = RI.NBOk b' ->
  RB.br_bits b' - 8 * RB.br_next b' = RB.br_bits b - 8 * RB.br_next b.
Proof.
  induction f as [|f IH]; intros n b b' Hf; cbn [RI.inf_nb_go] in Hf.
  - destruct (RB.br_bits b <? n); [discriminate|]. injection Hf as <-. reflexivity.
  - destruct (RB.br_bits b <? n).
    + destruct (RB.br_pullbyte b) as [b1|] eqn:Hp; [|discriminate].
      pose proof (RB.br_pullbyte_step b b1 Hp) as (_ & Hn1 & Hb1 & _).
      rewrite (IH n b1 b' Hf). lia.
    + injection Hf as <-. reflexivity.
Qed.

Lemma icore_needbits : forall w q b b' n,
  icore w q -> RI.q_br q = b -> 0 <= n <= 32 -> RI.inf_nb n b = RI.NBOk b' ->
  IA.NEEDBITS n w = IS.ARun tt (wbr w b') /\ icore (wbr w b') (RI.qset_br q b') /\ n <= RB.br_bits b'.
Proof.
  intros w q b b' n H Eb Hn Hf. subst b.
  destruct (needbits_sim w (RI.q_br q) b' n (icore_brel w q H) Hn Hf) as (E & Hb' & Hle & Hin & Hsum).
  split; [exact E|]. split; [|exact Hle].
  apply icore_wbr; [exact H | exact Hb' | exact Hin | exact Hsum |].
  pose proof (nb_go_inv _ _ _ _ Hf). pose proof (icore_b8 w q H). lia.
Qed.

Lemma icore_dropbits : forall w q b n,
  icore w q -> RI.q_br q = b -> 0 <= n <= RB.br_bits b ->
  IA.DROPBITS n w = IS.ARun tt (wbr w (RB.br_dropbits n b))
  /\ icore (wbr w (RB.br_dropbits n b)) (RI.qset_br q (RB.br_dropbits n b)).
Proof.
  intros w q b n H Eb Hn. subst b.
  destruct (dropbits_sim w (RI.q_br q) n (icore_brel w q H) Hn) as (E & Hb').
  split; [exact E|].
  apply icore_wbr; [exact H | exact Hb' | reflexivity | reflexivity |].
  pose proof (icore_b8 w q H). cbn [RB.br_bits RB.br_next RB.br_dropbits]. lia.
Qed.

Lemma icore_bytebits : forall w q b,
  icore w q -> RI.q_br q = b ->
  IA.BYTEBITS w = IS.ARun tt (wbr w (RB.br_bytebits b))
  /\ icore (wbr w (RB.br_bytebits b)) (RI.qset_br q (RB.br_bytebits b)).
Proof.
  intros w q b H Eb. subst b.
  destruct (bytebits_sim w (RI.q_br q) (icore_brel w q H)) as (E & Hb').
  split; [exact E|].
  apply icore_wbr; [exact H | exact Hb' | reflexivity | reflexivity |].
  pose proof (icore_b8 w q H).
  pose proof (icore_brel w q H) as (_ & Hbt & _ & _ & _ & _ & _ & Hbr & _). rewrite Hbt in Hbr.
  assert (0 <= Z.land (RB.br_bits (RI.q_br q)) 7) by (apply Z.land_nonneg; right; lia).
  unfold RB.br_bytebits. cbn [RB.br_bits RB.br_next RB.br_dropbits]. lia.
Qed.

Lemma icore_initbits : forall w q b,
  icore w q -> RI.q_br q = b ->
  IA.INITBITS w = IS.ARun tt (wbr w (RB.br_initbits b))
  /\ icore (wbr w (RB.br_initbits b)) (RI.qset_br q (RB.br_initbits b)).
Proof.
  intros w q b H Eb. subst b.
  destruct (initbits_sim w (RI.q_br q) (icore_brel w q H)) as (E & Hb').
  split; [exact E|].
  apply icore_wbr; [exact H | exact Hb' | reflexivity | reflexivity |].
  pose proof (icore_next0 w q H). cbn [RB.br_bits RB.br_next RB.br_initbits]. lia.
Qed.

Lemma icore_bits : forall w q b n, icore w q -> RI.q_br q = b -> 0 <= n <= 32 ->
  IA.BITS n w = IS.ARun (RB.br_bits_of n b) w.
Proof. intros w q b n H Eb Hn. subst b. exact (bits_sim w _ n (icore_brel w q H) Hn). Qed.

Lemma icore_hold : forall w q b, icore w q -> RI.q_br q = b -> IA.HOLD w = IS.ARun (RB.br_hold b) w.
Proof. intros w q b H Eb. subst b. exact (hold_sim w _ (icore_brel w q H)). Qed.

(* ------------------------------------------------------------------------- *)
(* State writes                                                              *)
(* ------------------------------------------------------------------------- *)

Lemma icore_st : forall w q s' st',
  icore w q -> ist_core_rel s' st' ->
  IS.is_total s' = IS.is_total (IS.w_s w) -> IS.is_wrap s' = IS.is_wrap (IS.w_s w) ->
  IS.is_wbits s' = IS.is_wbits (IS.w_s w) -> IS.is_havedict s' = IS.is_havedict (IS.w_s w) ->
  IS.is_sane s' = IS.is_sane (IS.w_s w) -> IS.is_wsize s' = IS.is_wsize (IS.w_s w) ->
  IS.is_whave s' = IS.is_whave (IS.w_s w) -> IS.is_wnext s' = IS.is_wnext (IS.w_s w) ->
  IS.is_window_blk s' = IS.is_window_blk (IS.w_s w) ->
  RI.w_win (RI.s_win st') = RI.w_win (RI.s_win (RI.q_st q)) ->
  (IS.is_mode s' <> IS.HEAD -> IS.is_flags s' = 0 /\ IS.is_check s' = 1) ->
  (forall i, code_rng (RI.t_codes (RI.s_tab st') i)) ->
  icore (IS.wset_s w s') (RI.qset_st q st').
Proof.
  intros w q s' st' H Hc E1 E2 E3 E4 E5 E6 E7 E8 E9 Ew Hf Hcd.
  icore_destr H.
  unfold icore, iw_rel. cbv zeta. autorewrite with s5w.
  cbn [RI.qset_st RI.q_st RI.q_z RI.q_br RI.q_ob RI.q_in RI.q_out RI.q_ret].
  rewrite E1, E2, E3, E4, E5, E6, E7, E8, E9, Ew.
  csplit.
Qed.

Lemma icr_mode : forall s st m,
  ist_core_rel s st -> ist_core_rel (IS.iset_mode s (RI.m_val m)) (RI.set_mode st m).
Proof.
  intros s st m (Hh & Hw & Hc & Ht & Hb).
  unfold ist_core_rel. unfold hdr_rel, win_rel, cur_rel, tab_rel, bld_rel in *.
  autorewrite with s5i_mode.
  cbn [RI.set_mode RI.s_hdr RI.s_win RI.s_cur RI.s_tab RI.s_bld RI.h_mode RI.h_last RI.h_wrap
       RI.h_havedict RI.h_flags RI.h_dmax RI.h_check RI.h_total RI.h_head].
  destruct Hh as (_ & Hh).
  exact (conj (conj eq_refl Hh) (conj Hw (conj Hc (conj Ht Hb)))).
Qed.

Lemma icr_last : forall s st v,
  ist_core_rel s st -> ist_core_rel (IS.iset_last s v) (RI.set_last st v).
Proof.
  intros s st v (Hh & Hw & Hc & Ht & Hb).
  unfold ist_core_rel. unfold hdr_rel, win_rel, cur_rel, tab_rel, bld_rel in *.
  autorewrite with s5i_last.
  cbn [RI.set_last RI.s_hdr RI.s_win RI.s_cur RI.s_tab RI.s_bld RI.h_mode RI.h_last RI.h_wrap
       RI.h_havedict RI.h_flags RI.h_dmax RI.h_check RI.h_total RI.h_head].
  destruct Hh as (Hm & _ & Hh).
  exact (conj (conj Hm (conj eq_refl Hh)) (conj Hw (conj Hc (conj Ht Hb)))).
Qed.

Lemma icr_length : forall s st v,
  ist_core_rel s st -> ist_core_rel (IS.iset_length s v) (RI.set_length st v).
Proof.
  intros s st v (Hh & Hw & Hc & Ht & Hb).
  unfold ist_core_rel. unfold hdr_rel, win_rel, cur_rel, tab_rel, bld_rel in *.
  autorewrite with s5i_length.
  cbn [RI.set_length RI.s_hdr RI.s_win RI.s_cur RI.s_tab RI.s_bld RI.u_length RI.u_offset
       RI.u_extra RI.u_back RI.u_was].
  destruct Hc as (_ & Hc).
  exact (conj Hh (conj Hw (conj (conj eq_refl Hc) (conj Ht Hb)))).
Qed.

Lemma icr_fixed : forall s st,
  ist_core_rel s st -> ist_core_rel (IA.fixedtables s) (RI.fixedtables st).
Proof.
  intros s st (Hh & Hw & Hc & Ht & Hb).
  unfold IA.fixedtables, RI.fixedtables, ist_core_rel.
  unfold hdr_rel, win_rel, cur_rel, tab_rel, bld_rel in *.
  autorewrite with s5i_distbits s5i_distcode s5i_lenbits s5i_lencode.
  cbn [RI.set_distbits RI.set_distcode RI.set_lenbits RI.set_lencode RI.s_hdr RI.s_win RI.s_cur
       RI.s_tab RI.s_bld RI.t_lencode RI.t_distcode RI.t_lenbits RI.t_distbits RI.t_next
       RI.t_codes RI.t_sane].
  destruct Ht as (_ & _ & _ & _ & Ht).
  refine (conj Hh (conj Hw (conj Hc (conj _ Hb)))).
  split; [exact I|]. split; [exact I|]. split; [reflexivity|]. split; [reflexivity|]. exact Ht.
Qed.

Lemma icore_mode : forall w q m,
  icore w q -> RI.q_mode q <> RI.M_HEAD ->
  icore (IS.wset_s w (IS.iset_mode (IS.w_s w) (RI.m_val m))) (RI.qmode q m).
Proof.
  intros w q m H Hq.
  pose proof (icore_flags w q H) as Hfl. pose proof (icore_codes w q H) as Hcd.
  pose proof (icore_mode_nh w q H Hq) as Hnh.
  unfold RI.qmode.
  apply icore_st; [exact H | exact (icr_mode _ _ m (icore_core w q H)) | ..];
    autorewrite with s5i_mode; try reflexivity.
  - intros _. exact (Hfl Hnh).
  - cbn [RI.set_mode RI.s_tab]. exact Hcd.
Qed.

(** The same, with S5's mode constant ([IS.CHECK], ...) as the arm spells it. *)
Lemma icore_modez : forall w q m z,
  icore w q -> z = RI.m_val m -> RI.q_mode q <> RI.M_HEAD ->
  icore (IS.wset_s w (IS.iset_mode (IS.w_s w) z)) (RI.qmode q m).
Proof. intros w q m z H Ez Hq. subst z. exact (icore_mode w q m H Hq). Qed.

Lemma icore_last : forall w q v,
  icore w q -> icore (IS.wset_s w (IS.iset_last (IS.w_s w) v)) (RI.qset_st q (RI.set_last (RI.q_st q) v)).
Proof.
  intros w q v H.
  pose proof (icore_flags w q H) as Hfl. pose proof (icore_codes w q H) as Hcd.
  apply icore_st; [exact H | exact (icr_last _ _ v (icore_core w q H)) | ..];
    autorewrite with s5i_last; try reflexivity.
  - exact Hfl.
  - cbn [RI.set_last RI.s_tab]. exact Hcd.
Qed.

Lemma icore_length : forall w q v,
  icore w q ->
  icore (IS.wset_s w (IS.iset_length (IS.w_s w) v)) (RI.qset_st q (RI.set_length (RI.q_st q) v)).
Proof.
  intros w q v H.
  pose proof (icore_flags w q H) as Hfl. pose proof (icore_codes w q H) as Hcd.
  apply icore_st; [exact H | exact (icr_length _ _ v (icore_core w q H)) | ..];
    autorewrite with s5i_length; try reflexivity.
  - exact Hfl.
  - cbn [RI.set_length RI.s_tab]. exact Hcd.
Qed.

Lemma icore_fixed : forall w q,
  icore w q ->
  icore (IS.wset_s w (IA.fixedtables (IS.w_s w))) (RI.qset_st q (RI.fixedtables (RI.q_st q))).
Proof.
  intros w q H.
  pose proof (icore_flags w q H) as Hfl. pose proof (icore_codes w q H) as Hcd.
  apply icore_st; [exact H | exact (icr_fixed _ _ (icore_core w q H)) | ..];
    unfold IA.fixedtables; autorewrite with s5i_distbits s5i_distcode s5i_lenbits s5i_lencode;
    try reflexivity.
  - exact Hfl.
  - cbn [RI.fixedtables RI.set_distbits RI.set_distcode RI.set_lenbits RI.set_lencode RI.s_tab
         RI.t_codes].
    exact Hcd.
Qed.
