(** * Bridge.Infl.IArmTableKit — pair I9 (TABLE / LENLENS / CODELENS), the shared kit.

    - [rt_cbn]: reduces RT's setters and projections (RT records are small);
    - the [icore] update lemmas, one per S5 write the three arms make, each in the shape the
      S5 monad produces ([wset_s w (iset_X (w_s w) v)], [wbr w b], [wset_r w (irset_ret ..)]),
      paired with RT's write of the same value;
    - the S5 monad stepping equations ([abind_gs], [abind_us], ...);
    - [inflate_table_bnd]: on success the new table's root and sub-tables lie below [next]. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require InflateState InflateArms Inftrees InftreesCoverage.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require ItDefs ItGen ItSimPre ItSim2 ItTable.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Base ZBitsIn Inflate Inftrees.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge Require Import IRelArr IRelInfl IFuelInfl.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge Require S5IFields.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.Infl Require Import IInv IBits ITree.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Ltac rt_cbn :=
  cbn [RI.q_st RI.q_z RI.q_br RI.q_ob RI.q_in RI.q_out RI.q_ret
       RI.qset_st RI.qset_br RI.qset_ret RI.qset_z RI.qmode RI.qbad
       RI.set_mode RI.set_lens RI.set_have RI.set_nlen RI.set_ndist RI.set_ncode
       RI.set_codes RI.set_next RI.set_lenbits RI.set_lencode RI.set_distcode RI.set_distbits
       RI.s_hdr RI.s_win RI.s_cur RI.s_tab RI.s_bld RI.s_hold RI.s_bits
       RI.h_mode RI.h_last RI.h_wrap RI.h_havedict RI.h_flags RI.h_dmax RI.h_check RI.h_total RI.h_head
       RI.w_wbits RI.w_wsize RI.w_whave RI.w_wnext RI.w_alloc RI.w_win
       RI.u_length RI.u_offset RI.u_extra RI.u_back RI.u_was
       RI.t_lencode RI.t_distcode RI.t_lenbits RI.t_distbits RI.t_next RI.t_codes RI.t_sane
       RI.b_ncode RI.b_nlen RI.b_ndist RI.b_have RI.b_lens RI.b_work
       RI.z_tin RI.z_tout RI.z_adler RI.z_dtype RI.z_msg RI.zset_msg
       RI.o_buf RI.o_put RI.o_left RI.cl_have RI.cl_lens RI.cl_br].

Ltac rt_cbn_in H :=
  cbn [RI.q_st RI.q_z RI.q_br RI.q_ob RI.q_in RI.q_out RI.q_ret
       RI.qset_st RI.qset_br RI.qset_ret RI.qset_z RI.qmode RI.qbad
       RI.set_mode RI.set_lens RI.set_have RI.set_nlen RI.set_ndist RI.set_ncode
       RI.set_codes RI.set_next RI.set_lenbits RI.set_lencode RI.set_distcode RI.set_distbits
       RI.s_hdr RI.s_win RI.s_cur RI.s_tab RI.s_bld RI.s_hold RI.s_bits
       RI.h_mode RI.h_last RI.h_wrap RI.h_havedict RI.h_flags RI.h_dmax RI.h_check RI.h_total RI.h_head
       RI.w_wbits RI.w_wsize RI.w_whave RI.w_wnext RI.w_alloc RI.w_win
       RI.u_length RI.u_offset RI.u_extra RI.u_back RI.u_was
       RI.t_lencode RI.t_distcode RI.t_lenbits RI.t_distbits RI.t_next RI.t_codes RI.t_sane
       RI.b_ncode RI.b_nlen RI.b_ndist RI.b_have RI.b_lens RI.b_work
       RI.z_tin RI.z_tout RI.z_adler RI.z_dtype RI.z_msg RI.zset_msg
       RI.o_buf RI.o_put RI.o_left RI.cl_have RI.cl_lens RI.cl_br] in H.

Ltac icore_unf_in H :=
  unfold icore, iw_rel, ist_core_rel, hdr_rel, win_rel, cur_rel, tab_rel, bld_rel, zstrm_rel in H;
  cbv zeta in H.
Ltac icore_unf :=
  unfold icore, iw_rel, ist_core_rel, hdr_rel, win_rel, cur_rel, tab_rel, bld_rel, zstrm_rel;
  cbv zeta.
Ltac split_hyps := repeat match goal with H : _ /\ _ |- _ => destruct H end.
Ltac split_goal := repeat match goal with |- _ /\ _ => split end.

(* ------------------------------------------------------------------------- *)
(* Accessors                                                                 *)
(* ------------------------------------------------------------------------- *)

Lemma icore_iw : forall w q, icore w q -> iw_rel w q.
Proof. intros w q H. exact (proj1 H). Qed.

Lemma icore_hdr : forall w q, icore w q -> hdr_rel (IS.w_s w) (RI.s_hdr (RI.q_st q)).
Proof. intros w q H. exact (proj1 (proj1 (proj1 H))). Qed.

Lemma icore_tab : forall w q, icore w q -> tab_rel (IS.w_s w) (RI.s_tab (RI.q_st q)).
Proof. intros w q H. exact (proj1 (proj2 (proj2 (proj2 (proj1 (proj1 H)))))). Qed.

Lemma icore_bld : forall w q, icore w q -> bld_rel (IS.w_s w) (RI.s_bld (RI.q_st q)).
Proof. intros w q H. exact (proj2 (proj2 (proj2 (proj2 (proj1 (proj1 H)))))). Qed.

Lemma icore_retok : forall w q, icore w q -> RI.q_ret q = RBa.Z_OK.
Proof. intros w q H. exact (proj1 (proj2 H)). Qed.

Lemma icore_rng : forall w q, icore w q -> forall i, code_rng (RI.t_codes (RI.s_tab (RI.q_st q)) i).
Proof.
  intros w q H. unfold icore in H. cbv zeta in H.
  repeat match type of H with _ /\ (_ /\ (_ /\ _)) => apply proj2 in H end. exact (proj1 H).
Qed.

Lemma icore_b8 : forall w q, icore w q -> RB.br_bits (RI.q_br q) <= 8 * RB.br_next (RI.q_br q).
Proof.
  intros w q H. unfold icore, iw_rel in H. cbv zeta in H.
  destruct H as ((_ & _ & Hb & Hn & _) & _ & _ & _ & H8 & _). congruence.
Qed.

Lemma icore_mode : forall w q, icore w q -> IS.is_mode (IS.w_s w) = RI.m_val (RI.q_mode q).
Proof. intros w q H. exact (proj1 (icore_hdr w q H)). Qed.

Lemma icore_req : forall w q q', icore w q -> q = q' -> icore w q'.
Proof. intros w q q' H <-. exact H. Qed.

(* ------------------------------------------------------------------------- *)
(* The update lemmas                                                         *)
(* ------------------------------------------------------------------------- *)

(** What [icore] needs of a moved bit reader [b] (the old one is [b0]). *)
Definition brf (b0 b : RB.BR) : Prop :=
  RB.br_in b = RB.br_in b0 /\ RB.br_next b + RB.br_have b = RB.br_next b0 + RB.br_have b0
  /\ 0 <= RB.br_next b /\ 0 <= RB.br_have b /\ 0 <= RB.br_bits b <= 39
  /\ 0 <= RB.br_hold b < 2 ^ RB.br_bits b /\ RB.br_bits b <= 8 * RB.br_next b.

Lemma icore_br : forall w q b, icore w q -> brf (RI.q_br q) b -> icore (wbr w b) (RI.qset_br q b).
Proof.
  intros w q b H Hf. destruct Hf as (Hin & Hsum & Hn & Hv & Hbt & Hh & H8).
  icore_unf_in H. icore_unf.
  rewrite ?wbr_s, ?wbr_c, ?wbr_r. setbr_cbn. rt_cbn. split_hyps.
  rewrite Hin.
  split_goal; first [assumption | reflexivity | lia].
Qed.

(** In every update lemma the state S5 writes into is given separately ([s], [r]) with an
    equation to the current one, so the lemmas match a goal whatever form that state has. *)

Lemma icore_have : forall w q s vs vr, icore w q -> s = IS.w_s w -> vs = vr ->
  icore (IS.wset_s w (IS.iset_have s vs)) (RI.qset_st q (RI.set_have (RI.q_st q) vr)).
Proof.
  intros w q s vs vr H -> <-. icore_unf_in H. icore_unf.
  autorewrite with s5w s5i_have. rt_cbn. split_hyps.
  split_goal; first [assumption | reflexivity].
Qed.

Lemma icore_lens : forall w q s L Lr, icore w q -> s = IS.w_s w ->
  arr_len L = NLENS -> arr_rel L Lr 0 NLENS ->
  icore (IS.wset_s w (IS.iset_lens s L)) (RI.qset_st q (RI.set_lens (RI.q_st q) Lr)).
Proof.
  intros w q s L Lr H -> HL HR. icore_unf_in H. icore_unf.
  autorewrite with s5w s5i_lens. rt_cbn. split_hyps.
  split_goal; first [assumption | reflexivity].
Qed.

(** One [us] writing both [lens] and [have] (S5's [lens_repeat]). *)
Lemma icore_lens_have : forall w q s L Lr vs vr, icore w q -> s = IS.w_s w ->
  arr_len L = NLENS -> arr_rel L Lr 0 NLENS -> vs = vr ->
  icore (IS.wset_s w (IS.iset_have (IS.iset_lens s L) vs))
        (RI.qset_st q (RI.set_lens (RI.set_have (RI.q_st q) vr) Lr)).
Proof.
  intros w q s L Lr vs vr H -> HL HR <-. icore_unf_in H. icore_unf.
  autorewrite with s5w s5i_have s5i_lens. rt_cbn. split_hyps.
  split_goal; first [assumption | reflexivity].
Qed.

Lemma icore_nlen : forall w q s vs vr, icore w q -> s = IS.w_s w -> vs = vr ->
  icore (IS.wset_s w (IS.iset_nlen s vs)) (RI.qset_st q (RI.set_nlen (RI.q_st q) vr)).
Proof.
  intros w q s vs vr H -> <-. icore_unf_in H. icore_unf.
  autorewrite with s5w s5i_nlen. rt_cbn. split_hyps.
  split_goal; first [assumption | reflexivity].
Qed.

Lemma icore_ndist : forall w q s vs vr, icore w q -> s = IS.w_s w -> vs = vr ->
  icore (IS.wset_s w (IS.iset_ndist s vs)) (RI.qset_st q (RI.set_ndist (RI.q_st q) vr)).
Proof.
  intros w q s vs vr H -> <-. icore_unf_in H. icore_unf.
  autorewrite with s5w s5i_ndist. rt_cbn. split_hyps.
  split_goal; first [assumption | reflexivity].
Qed.

Lemma icore_ncode : forall w q s vs vr, icore w q -> s = IS.w_s w -> vs = vr ->
  icore (IS.wset_s w (IS.iset_ncode s vs)) (RI.qset_st q (RI.set_ncode (RI.q_st q) vr)).
Proof.
  intros w q s vs vr H -> <-. icore_unf_in H. icore_unf.
  autorewrite with s5w s5i_ncode. rt_cbn. split_hyps.
  split_goal; first [assumption | reflexivity].
Qed.

Lemma icore_setmode : forall w q s v m, icore w q -> s = IS.w_s w -> v = RI.m_val m ->
  IS.is_mode (IS.w_s w) <> IS.HEAD ->
  icore (IS.wset_s w (IS.iset_mode s v)) (RI.qmode q m).
Proof.
  intros w q s v m H -> -> Hm. icore_unf_in H. icore_unf.
  autorewrite with s5w s5i_mode. rt_cbn. split_hyps.
  split_goal; first [assumption | reflexivity | intros _; auto].
Qed.

Lemma icore_ret : forall w q r v, icore w q -> r = IS.w_r w -> v = 0 ->
  icore (IS.wset_r w (IS.irset_ret r v)) (RI.qset_ret q 0).
Proof.
  intros w q r v H -> ->. icore_unf_in H. icore_unf.
  autorewrite with s5w s5ir_ret. rt_cbn. split_hyps.
  split_goal; first [assumption | reflexivity].
Qed.

(** A literal/length or code-length table write ([lencode], [lenbits]). *)
Lemma icore_ltbl : forall w q s tbl tc k nx lb wk, icore w q -> s = IS.w_s w ->
  arr_len tbl = ENOUGH -> tbl_rel tbl tc 0 ENOUGH -> (forall i, code_rng (tc i)) ->
  arr_len wk = NWORK ->
  icore (IS.wset_s w (IS.iset_work (IS.iset_lenbits (IS.iset_next
           (IS.iset_lencode (IS.iset_codes s tbl) (IS.CDyn k)) nx) lb) wk))
        (RI.qset_st q (RI.set_codes (RI.set_next (RI.set_lenbits
           (RI.set_lencode (RI.q_st q) (RI.TRcodes k)) lb) nx) tc)).
Proof.
  intros w q s tbl tc k nx lb wk H -> Hl Hr Hg Hwl. icore_unf_in H. icore_unf.
  autorewrite with s5w s5i_work s5i_lenbits s5i_next s5i_lencode s5i_codes. rt_cbn. split_hyps.
  split_goal; first [assumption | reflexivity | exact eq_refl].
Qed.

(** A distance table write ([distcode], [distbits]). *)
Lemma icore_dtbl : forall w q s tbl tc k nx db wk, icore w q -> s = IS.w_s w ->
  arr_len tbl = ENOUGH -> tbl_rel tbl tc 0 ENOUGH -> (forall i, code_rng (tc i)) ->
  arr_len wk = NWORK ->
  icore (IS.wset_s w (IS.iset_work (IS.iset_distbits (IS.iset_next
           (IS.iset_distcode (IS.iset_codes s tbl) (IS.CDyn k)) nx) db) wk))
        (RI.qset_st q (RI.set_codes (RI.set_next (RI.set_distbits
           (RI.set_distcode (RI.q_st q) (RI.TRcodes k)) db) nx) tc)).
Proof.
  intros w q s tbl tc k nx db wk H -> Hl Hr Hg Hwl. icore_unf_in H. icore_unf.
  autorewrite with s5w s5i_work s5i_distbits s5i_next s5i_distcode s5i_codes. rt_cbn. split_hyps.
  split_goal; first [assumption | reflexivity | exact eq_refl].
Qed.


(* ------------------------------------------------------------------------- *)
(* S5 monad stepping                                                         *)
(* ------------------------------------------------------------------------- *)

Lemma abind_gs : forall {A B} (g : IS.inflate_state -> A) (f : A -> IS.AM B) w,
  IS.abind (IS.gs g) f w = f (g (IS.w_s w)) w.
Proof. reflexivity. Qed.

Lemma abind_us : forall {B} g (f : unit -> IS.AM B) w,
  IS.abind (IS.us g) f w = f tt (IS.wset_s w (g (IS.w_s w))).
Proof. reflexivity. Qed.

Lemma abind_ur : forall {B} g (f : unit -> IS.AM B) w,
  IS.abind (IS.ur g) f w = f tt (IS.wset_r w (g (IS.w_r w))).
Proof. reflexivity. Qed.

Lemma abind_setmode : forall {B} m (f : unit -> IS.AM B) w,
  IS.abind (IA.set_mode m) f w = f tt (IS.wset_s w (IS.iset_mode (IS.w_s w) m)).
Proof. reflexivity. Qed.

Lemma abind_setlens : forall {B} i v (f : unit -> IS.AM B) w,
  IS.abind (IA.set_lens i v) f w
  = f tt (IS.wset_s w (IS.iset_lens (IS.w_s w) (arr_set (IS.is_lens (IS.w_s w)) i (wrap16 v)))).
Proof. reflexivity. Qed.

Lemma aret_eq : forall {A} (a : A) w, IS.aret a w = IS.ARun a w.
Proof. reflexivity. Qed.

Lemma setmode_eq : forall m w, IA.set_mode m w = IS.ARun tt (IS.wset_s w (IS.iset_mode (IS.w_s w) m)).
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------------- *)
(* step_ok on the excluded outcomes                                          *)
(* ------------------------------------------------------------------------- *)

Lemma step_ok_bad : forall sr q', RI.q_mode q' = RI.M_BAD -> step_ok sr (RI.InfCont q').
Proof. intros sr q' H. unfold step_ok. intros C. contradiction. Qed.

Lemma step_ok_leave : forall sr q', RI.q_ret q' = RBa.Z_OK -> step_ok sr (RI.InfLeave q').
Proof.
  intros sr q' H. unfold step_ok. rewrite H. unfold RBa.Z_OK, RBa.Z_STREAM_END. intros C. discriminate.
Qed.

Lemma qbad_mode : forall q m, RI.q_mode (RI.qbad q m) = RI.M_BAD.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------------- *)
(* The bit reader                                                            *)
(* ------------------------------------------------------------------------- *)

(** [bits <= 8 * next] (every accumulated bit was read from consumed input). *)
Lemma nb_go_b8 : forall f n b b', RI.inf_nb_go f n b = RI.NBOk b' ->
  RB.br_bits b <= 8 * RB.br_next b -> RB.br_bits b' <= 8 * RB.br_next b'.
Proof.
  induction f as [|f IH]; intros n b b' Hf H8; cbn [RI.inf_nb_go] in Hf.
  - destruct (Z.ltb (RB.br_bits b) n); [discriminate|]. injection Hf as <-. exact H8.
  - destruct (Z.ltb (RB.br_bits b) n).
    + destruct (RB.br_pullbyte b) as [b1|] eqn:Hp; [|discriminate].
      pose proof (RB.br_pullbyte_step b b1 Hp) as (_ & Hn1 & Hb1 & _).
      apply (IH n b1 b' Hf). lia.
    + injection Hf as <-. exact H8.
Qed.

Lemma nb_b8 : forall n b b', RI.inf_nb n b = RI.NBOk b' ->
  RB.br_bits b <= 8 * RB.br_next b -> RB.br_bits b' <= 8 * RB.br_next b'.
Proof. intros n b b'. unfold RI.inf_nb. apply nb_go_b8. Qed.

Lemma gfetch_b8 : forall f ix t cb b h b', gfetch f ix t cb b = RI.FetchOk h b' ->
  RB.br_bits b <= 8 * RB.br_next b -> RB.br_bits b' <= 8 * RB.br_next b'.
Proof.
  induction f as [|f IH]; intros ix t cb b h b' Hf H8; cbn [gfetch] in Hf; [discriminate|].
  destruct (Z.leb _ _).
  - injection Hf as _ <-. exact H8.
  - destruct (RB.br_pullbyte b) as [b1|] eqn:Hp; [|discriminate].
    pose proof (RB.br_pullbyte_step b b1 Hp) as (_ & Hn1 & Hb1 & _).
    apply (IH ix t cb b1 h b' Hf). lia.
Qed.

Lemma fetch_b8 : forall t nb b h b', RI.inf_fetch t nb b = RI.FetchOk h b' ->
  RB.br_bits b <= 8 * RB.br_next b -> RB.br_bits b' <= 8 * RB.br_next b'.
Proof. intros t nb b h b'. unfold RI.inf_fetch. rewrite fetch_gfetch. apply gfetch_b8. Qed.

(** [brf] from a macro's conclusion. *)
Lemma brf_intro : forall w b0 b, brel (wbr w b) b ->
  RB.br_in b = RB.br_in b0 -> RB.br_next b + RB.br_have b = RB.br_next b0 + RB.br_have b0 ->
  RB.br_bits b <= 8 * RB.br_next b -> brf b0 b.
Proof.
  intros w b0 b Hb Hin Hsum H8.
  destruct Hb as (_ & _ & _ & _ & Hn0 & Hv0 & _ & Hbt & Hh & _).
  rewrite wbr_r in Hn0, Hv0, Hbt, Hh. setbr_cbn.
  cbn [setbr IS.ir_next IS.ir_have IS.ir_bits IS.ir_hold] in Hn0, Hv0, Hbt, Hh.
  unfold brf. repeat split; assumption || lia.
Qed.

Lemma brf_drop : forall w b n, brel (wbr w (RB.br_dropbits n b)) (RB.br_dropbits n b) ->
  0 <= n -> RB.br_bits b <= 8 * RB.br_next b -> brf b (RB.br_dropbits n b).
Proof.
  intros w b n Hb Hn H8. apply (brf_intro w); cbn [RB.br_dropbits RB.br_in RB.br_next RB.br_have RB.br_bits];
    [exact Hb | reflexivity | reflexivity | lia].
Qed.

(* ------------------------------------------------------------------------- *)
(* CODELENS's state                                                          *)
(* ------------------------------------------------------------------------- *)

(** RT's [put_cl] inside [inf_CODELENS] (also LENLENS's partial state). *)
Definition put_cl (q : RI.InfSt) (s : RI.ClSt) : RI.InfSt :=
  RI.qset_br (RI.qset_st q (RI.set_lens (RI.set_have (RI.q_st q) (RI.cl_have s)) (RI.cl_lens s)))
             (RI.cl_br s).

Lemma put_cl_id : forall q,
  put_cl q (RI.mkClSt (RI.b_have (RI.s_bld (RI.q_st q))) (RI.b_lens (RI.s_bld (RI.q_st q))) (RI.q_br q)) = q.
Proof. intros [[h w c t [nc nl nd hv ls wk] ho bi] z b o i ou r]. reflexivity. Qed.

Lemma code_at_eq : forall s1 s2 p, IS.is_codes s1 = IS.is_codes s2 -> IS.code_at s1 p = IS.code_at s2 p.
Proof. intros s1 s2 p E. unfold IS.code_at. rewrite E. reflexivity. Qed.

(* ------------------------------------------------------------------------- *)
(* [order]                                                                   *)
(* ------------------------------------------------------------------------- *)

Lemma order_get : forall h, 0 <= h < 19 ->
  arr_get IS.order_a h = RI.inf_order h /\ 0 <= RI.inf_order h < 19.
Proof.
  intros h Hh.
  assert (B : forallb (fun k => (arr_get IS.order_a (Z.of_nat k) =? RI.inf_order (Z.of_nat k))
                                && (0 <=? RI.inf_order (Z.of_nat k)) && (RI.inf_order (Z.of_nat k) <? 19))
                      (seq 0 19) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in B. specialize (B (Z.to_nat h) ltac:(apply in_seq; lia)).
  rewrite Z2Nat.id in B by lia.
  apply andb_prop in B as [B B3]. apply andb_prop in B as [B1 B2].
  apply Z.eqb_eq in B1. apply Z.leb_le in B2. apply Z.ltb_lt in B3. auto.
Qed.

Lemma order_cover : forall i, 0 <= i < 19 -> exists j, 0 <= j < 19 /\ RI.inf_order j = i.
Proof.
  intros i Hi.
  assert (B : forallb (fun i => existsb (fun j => RI.inf_order (Z.of_nat j) =? Z.of_nat i) (seq 0 19))
                      (seq 0 19) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in B. specialize (B (Z.to_nat i) ltac:(apply in_seq; lia)).
  apply existsb_exists in B as [j [Hj Hq]]. apply in_seq in Hj. apply Z.eqb_eq in Hq.
  exists (Z.of_nat j). split; [lia|]. rewrite Hq. lia.
Qed.

(* ------------------------------------------------------------------------- *)
(* Where a new table lives                                                   *)
(* ------------------------------------------------------------------------- *)

(** Every index a decode reads from a table lies below [U]. *)
Definition tbnd (f : Z -> Z) (root : Z) (k : tkind) (U : Z) : Prop :=
  2 ^ root <= U /\
  forall x, 0 <= x < 2 ^ root -> tsub k (IS.code_op (f x)) = true ->
    IS.code_val (f x) + 2 ^ IS.code_op (f x) <= U.

Lemma inflate_table_bnd : forall ty lens ofs codes tbl table bits work,
  0 <= codes <= ty_max ty ->
  (forall i, ofs <= i < ofs + codes -> 0 <= arr_get lens i <= 15) ->
  (ty = IS.CODES -> forall i, ofs <= i < ofs + codes -> arr_get lens i <= 7) ->
  arr_len tbl = ENOUGH -> 0 <= table -> table + ICov.it_room ty <= ENOUGH ->
  arr_len work = NWORK -> 1 <= bits <= 15 -> (ty = IS.CODES -> 7 <= bits) ->
  let '(ret, tbl', next, bits', work') := IT.inflate_table ty lens ofs codes tbl table bits work in
  ret = 0 -> table + 2 ^ bits' <= next
             /\ tbnd (fun x => arr_get tbl' (table + x)) bits' (ty_kind ty) (next - table).
Proof.
  intros ty lens ofs codes tbl table bits work Hc HL H7 Hlen Ht0 Htr Hw Hbits Hb7.
  assert (HC19 : ty = IS.CODES -> codes <= 19) by (intros ->; cbn [ty_max] in Hc; lia).
  assert (Hcodes : 0 <= codes <= 288) by (destruct ty; cbn [ty_max] in Hc; lia).
  assert (Hwk : codes <= arr_len work) by (rewrite Hw; unfold NWORK; lia).
  pose proof (ItSim2.inflate_table_abs ty lens ofs codes (ItDefs.lens_list lens ofs codes)
                (ItDefs.wl_of (ItDefs.lens_list lens ofs codes)) table bits Hcodes HL eq_refl eq_refl HC19 Hbits
                tbl work Hwk) as R1.
  assert (Hok : ItTable.ty_ok ty (ItDefs.lens_list lens ofs codes) bits).
  { assert (ENC : ItDefs.NC (ItDefs.lens_list lens ofs codes) = codes) by (apply ItSimPre.NC_lens; lia).
    destruct ty; cbn [ItTable.ty_ok]; rewrite ENC; cbn [ty_max] in Hc; try lia.
    split; [lia|]. split; [apply Hb7; reflexivity|].
    unfold ItDefs.lens_list. apply Forall_forall. intros l Hl. apply in_map_iff in Hl as [n [<- Hn]].
    apply in_seq in Hn. apply (H7 eq_refl). lia. }
  pose proof (ItTable.it_abs_props (ItDefs.wl_of (ItDefs.lens_list lens ofs codes)) (ItDefs.lens_list lens ofs codes)
                table bits (ItSimPre.Hll lens ofs codes _ _ Hcodes HL eq_refl eq_refl) eq_refl Hbits ty Hok) as PR.
  rewrite R1. clear R1.
  destruct (ItDefs.it_abs (ItDefs.wl_of (ItDefs.lens_list lens ofs codes)) (ItDefs.lens_list lens ofs codes) ty table bits)
    as [[[[ret ws] toff] bits'] ww].
  cbn beta iota in PR |- *.
  intros H0. destruct (PR H0) as [P1 [P2 [P3 [P4 P5]]]].
  split; [lia|]. split; [lia|].
  intros x Hx T.
  assert (Hin : In (table + x) (map fst ws)) by (apply P4; lia).
  assert (Hr : 0 <= table + x < arr_len tbl) by lia.
  pose proof (ItGen.applyw_all (fun i v => ICov.entry_shape ty bits' (toff - table) (i - table) v)
                ws tbl (table + x) P5 Hin Hr) as P.
  cbv beta in P. replace (table + x - table) with x in P by lia.
  destruct (shape_root ty bits' (toff - table) x _ P1 Hx P) as [_ [_ R3]].
  destruct (R3 T) as [_ [_ [_ [_ L5]]]]. exact L5.
Qed.

(** A table view survives any change outside the indices it reads. *)
Lemma tview_transport : forall f g f' g' root k U,
  tview f g root k -> tbnd f root k U ->
  (forall x, 0 <= x < U -> f' x = f x /\ g' x = g x) ->
  tview f' g' root k.
Proof.
  intros f g f' g' root k U [Hr Htv] [HU Hb] Heq. split; [exact Hr|].
  intros x Hx.
  assert (Hp : 0 < 2 ^ root) by (apply Z.pow_pos_nonneg; lia).
  destruct (Heq x ltac:(lia)) as [Ef Eg]. rewrite Ef, Eg.
  destruct (Htv x Hx) as (A1 & A2 & A3 & A4 & A5).
  split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [exact A4|].
  intros T. destruct (A5 T) as (B1 & B2 & B3 & B4). split; [exact B1|]. split; [exact B2|].
  split; [exact B3|].
  intros y Hy. cbv zeta.
  pose proof (Hb x Hx T) as Hlt.
  assert (Hv0 : 0 <= IS.code_val (f x)) by (unfold IS.code_val; apply Z.land_nonneg; right; lia).
  destruct (Heq (IS.code_val (f x) + y) ltac:(lia)) as [Ef2 Eg2]. rewrite Ef2, Eg2. exact (B4 y Hy).
Qed.

(* ------------------------------------------------------------------------- *)
(* More monad stepping                                                       *)
(* ------------------------------------------------------------------------- *)

Global Hint Rewrite wbr_s wbr_c wbr_r : s5wbr.

Lemma abind_assoc : forall {A B C} (m : IS.AM A) (f : A -> IS.AM B) (k : B -> IS.AM C) w,
  IS.abind (IS.abind m f) k w = IS.abind m (fun a => IS.abind (f a) k) w.
Proof. intros. unfold IS.abind. destruct (m w); reflexivity. Qed.

Lemma abind_aret : forall {A B} (a : A) (k : A -> IS.AM B) w, IS.abind (IS.aret a) k w = k a w.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------------- *)
(* S5's [lens_repeat]                                                        *)
(* ------------------------------------------------------------------------- *)

Definition rep_step (len : Z) : arr * Z * Z -> bool * (arr * Z * Z) :=
  fun st : arr * Z * Z => let '(lens, have, copy) := st in
    if negb (copy =? 0) then (true, (arr_set lens have (wrap16 len), wrap32 (have + 1), wrap32 (copy - 1)))
    else (false, (lens, have, copy)).

Lemma lens_repeat_eq : forall copy len w,
  IA.lens_repeat copy len w =
  IS.ARun tt (IS.wset_s w (let '(lens, have, _) :=
                             loopZ copy (rep_step len) (IS.is_lens (IS.w_s w), IS.is_have (IS.w_s w), copy) in
                           IS.iset_have (IS.iset_lens (IS.w_s w) lens) have)).
Proof. reflexivity. Qed.

(** The tuple is a separate argument [st] with an equation: S5's first tuple has an [arr]
    component and the ones [rep_step] builds a [parr Z] one (convertible, not equal). *)
Lemma rep_loop_nat : forall n (L : arr) Lr h len st, st = (L, h, Z.of_nat n) ->
  0 <= h -> h + Z.of_nat n <= NLENS -> arr_len L = NLENS ->
  arr_rel L Lr 0 NLENS -> 0 <= len < 65536 ->
  exists L' : arr, loopZ (Z.of_nat n) (rep_step len) st = (L', h + Z.of_nat n, 0)
             /\ arr_len L' = NLENS /\ arr_rel L' (RI.zfill n Lr h len) 0 NLENS.
Proof.
  induction n as [|n IH]; intros L Lr h len st -> Hh Hn HL HR Hlen.
  - exists L. rewrite loopZ_le0 by lia. cbn [RI.zfill]. rewrite Z.add_0_r. auto.
  - rewrite loopZ_step by lia. unfold rep_step at 1.
    assert (E1 : negb (Z.of_nat (S n) =? 0) = true) by (apply negb_true_iff, Z.eqb_neq; lia).
    rewrite E1. cbv iota.
    rewrite (wrap16_id len) by (change (2 ^ 16) with 65536; lia).
    rewrite (wrap32_id (h + 1)) by (unfold NLENS in Hn; lia).
    rewrite (wrap32_id (Z.of_nat (S n) - 1)) by (unfold NLENS in Hn; lia).
    replace (Z.of_nat (S n) - 1) with (Z.of_nat n) by lia.
    match goal with |- exists _, loopZ (Z.of_nat n) (rep_step len) ?st' = _ /\ _ =>
      destruct (IH (arr_set L h len) (RBa.zset Lr h len) (h + 1) len st' eq_refl ltac:(lia) ltac:(lia)
                   ltac:(rewrite arr_len_set; exact HL)
                   ltac:(apply arr_rel_set; [exact HR | rewrite HL; intros; lia]) Hlen) as (L' & E & HL' & HR')
    end.
    exists L'. rewrite E. split; [f_equal; f_equal; lia|]. split; [exact HL'|].
    cbn [RI.zfill]. exact HR'.
Qed.

Lemma rep_loop : forall cp (L : arr) Lr h len st, st = (L, h, cp) ->
  0 <= cp -> 0 <= h -> h + cp <= NLENS -> arr_len L = NLENS ->
  arr_rel L Lr 0 NLENS -> 0 <= len < 65536 ->
  exists L' : arr, loopZ cp (rep_step len) st = (L', h + cp, 0)
             /\ arr_len L' = NLENS /\ arr_rel L' (RI.zfill (Z.to_nat cp) Lr h len) 0 NLENS.
Proof.
  intros cp L Lr h len st Hst Hc Hh Hn HL HR Hlen.
  destruct (rep_loop_nat (Z.to_nat cp) L Lr h len st ltac:(rewrite Z2Nat.id by lia; exact Hst)
              Hh ltac:(lia) HL HR Hlen) as (L' & E & H1 & H2).
  rewrite Z2Nat.id in E by lia. exists L'. auto.
Qed.
