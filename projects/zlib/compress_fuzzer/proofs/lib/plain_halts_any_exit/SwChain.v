(** * SwChain — the slow-path walk, part W2: the hash-chain invariant and
      [ins_h] synchronisation through [fill_window].

    OWNER: q5-emitter (zlib z-repro campaign, 2026-08-19).  G4/W2 of the Q5
    plan; design in WALK-DESIGN.md.

    TRUST BOUNDARY: pure Gallina, image-INDEPENDENT.

    WHAT THIS FILE GLUES.  CresChain.v owns ALL the chain algebra
    ([insert_inv], [slide_inv]/[slide_hash_inv], [window_ext_inv],
    [flr_advance]); this file instantiates it along [fill_window]'s actual
    control flow, using SwFill.v's named pieces ([fwp_slide]/[fwp_pre]/
    [fwp_blit]/[fw_step_shape]).

    THE ONE-CALL SIMPLIFICATION, measured on the model: in the z-repro call
    shape ([zr_deflate]: a single [deflate(Z_FINISH)]), [ls_insert] starts 0
    ([deflate_reset]) and NOTHING ever raises it — [fw_insert] decrements,
    the slide clamps DOWN, and [ds_tail]'s [setL_insert] runs only at the
    very end of the stream.  So the walk carries [ls_insert = 0]
    ([cc_ins0]): the [fw_insert] drain never runs, and [fw_seed] reduces to
    the [ins_h] re-seed — which establishes [SyncOK] BY CONSTRUCTION
    (definitionally: [update_hash (update_hash (w ss) (w (ss+1))) (w (ss+2))]
    IS [h3 ss]). *)

From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Chunk Deflate Trees CresChain CbFold.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import SwWin SwFill SwTally.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Local Open Scope Z_scope.

Local Ltac lsimp :=
  cbn [ls_window ls_prev ls_head ls_insh ls_blockstart ls_matchlen
       ls_prevmatch ls_matchavail ls_strstart ls_matchstart ls_lookahead
       ls_prevlen ls_insert ls_highwater ls_windowsize
       setL_window setL_prev setL_head setL_insh setL_blockstart
       setL_matchlen setL_prevmatch setL_matchavail setL_strstart
       setL_matchstart setL_lookahead setL_prevlen setL_insert
       setL_highwater setL_windowsize
       fst snd].

(** ** 1. The chain clause the walk carries *)

Record ChainCl (g : DeflGeom) (Ins : Z -> Prop) (l : LSt) : Prop
  := mkChainCl {
  cc_inv  : ChainInv g (ls_window l) (ls_prev l) (ls_head l)
                     (ls_strstart l) (ls_lookahead l) Ins;
  cc_hi   : forall p, Ins p -> p < ls_strstart l;
  cc_ins0 : ls_insert l = 0;
  cc_sync : SyncOK g l
}.

(** The empty chain at the reset state: [lm_init] clears [head], and the
    empty [Ins] satisfies every clause vacuously. *)
Lemma chaincl_reset : forall g wbits hbits wrap,
  GeomOk2 g wbits hbits ->
  ChainCl g (fun _ => False) (d_ls (deflate_reset g wrap)).
Proof.
  intros g wbits hbits wrap Hg.
  unfold deflate_reset. cbn [d_ls].
  unfold lm_init, clear_hash. lsimp.
  constructor.
  - constructor; try (intros p Hp; exact (False_ind _ Hp)).
    + (* head entries: cleared range reads NIL, outside is zzero = NIL *)
      intros h Hh. lsimp. left.
      destruct ((0 <=? h) && (h <? dg_hash_size g)); reflexivity.
    + (* head_h3: heads are NIL, and NIL is never above the floor *)
      intros h Hh Hgt. exfalso.
      revert Hgt. lsimp.
      destruct ((0 <=? h) && (h <? dg_hash_size g));
        unfold NIL, flr, zzero, zconst;
        (* this lia does not see through [Z.max]; hand it the bound *)
        (intros Hx; pose proof (Z.le_max_l 0 (0 - dg_w_size g)); lia).
  - intros p Hp. destruct Hp.
  - lsimp. reflexivity.
  - unfold SyncOK. lsimp. intros _ Hla.
    unfold MIN_MATCH in Hla. lia.
Qed.

(** ** 2. Through the slide *)

Lemma chaincl_slide : forall g wbits hbits l st slid Ins,
  GeomOk2 g wbits hbits ->
  WinInv g slid l st ->
  ChainCl g Ins l ->
  dg_w_size g + dg_max_dist g <= ls_strstart l ->
  ChainCl g (fun p => 0 <= p /\ Ins (p + dg_w_size g)) (fwp_slide g l).
Proof.
  intros g wbits hbits l st slid Ins Hg Hw Hc Hsl.
  pose proof (go_ws_lo _ (g2_geom _ _ _ Hg)) as Hws262.
  pose proof (go_ws_hi _ (g2_geom _ _ _ Hg)) as Hws32.
  pose proof (go_maxd _ (g2_geom _ _ _ Hg)) as Hmd.
  pose proof (g2_u16 _ _ _ Hg) as Hu16.
  pose proof (wi_ss _ _ _ _ Hw) as Hss.
  pose proof (wi_la _ _ _ _ Hw) as Hla.
  pose proof (wi_room _ _ _ _ Hw) as Hroom.
  pose proof (wi_wsize _ _ _ _ Hw) as Hwsz.
  destruct Hc as [Hinv Hhi Hins0 Hsync].
  assert (Hm0 : u32 (ls_windowsize l - ls_lookahead l - ls_strstart l)
                = ls_windowsize l - ls_lookahead l - ls_strstart l).
  { unfold u32. apply Z.mod_small. lia. }
  unfold fwp_slide. cbv zeta. rewrite Hm0.
  set (wsz := dg_w_size g) in *.
  assert (Hcnt : wsz - (ls_windowsize l - ls_lookahead l - ls_strstart l)
                 = ls_strstart l + ls_lookahead l - wsz) by lia.
  rewrite Hcnt.
  (* the insert clamp is decidable at insert = 0 *)
  lsimp.
  rewrite Hins0.
  replace (Z.ltb (ls_strstart l - wsz) 0) with false
    by (symmetry; apply Z.ltb_ge; lia).
  constructor.
  - (* ChainInv, via slide_hash_inv; the discharge chain is order-agnostic
       because eapply's premise order follows the section's usage order *)
    eapply (slide_hash_inv g wbits hbits); lsimp;
      first [ exact Hinv
            | exact (g2_wb0 _ _ _ Hg) | exact (g2_hb0 _ _ _ Hg)
            | exact (g2_ws _ _ _ Hg) | exact (g2_wm _ _ _ Hg)
            | exact (g2_hs _ _ _ Hg) | exact (g2_hm _ _ _ Hg)
            | exact Hmd | reflexivity | lia ].
  - (* Ins bound shifts with strstart *)
    intros p [Hp0 Hp].
    specialize (Hhi _ Hp).
    unfold slide_hash. lsimp. lia.
  - unfold slide_hash. lsimp. exact Hins0.
  - (* sync survives: the three reads move together with strstart *)
    unfold SyncOK, slide_hash in *. lsimp.
    intros _ Hla3. unfold MIN_MATCH in Hla3.
    assert (Hsync2 := Hsync Hins0 ltac:(unfold MIN_MATCH; lia)).
    unfold win_move.
    set (ss2 := ls_strstart l - wsz).
    set (cnt := ls_strstart l + ls_lookahead l - wsz).
    assert (R : forall q, ss2 <= q <= ss2 + 2 ->
              (if (0 <=? q) && (q <? 0 + cnt)
               then ls_window l (q - 0 + wsz) else ls_window l q)
              = ls_window l (q + wsz)).
    { intros q Hq.
      destruct (Z.leb_spec 0 q) as [H1|H1]; [|unfold ss2 in *; lia].
      destruct (Z.ltb_spec q (0 + cnt)) as [H2|H2];
        [|unfold ss2, cnt in *; lia].
      cbn [andb]. f_equal. lia. }
    unfold h3.
    rewrite (R ss2 ltac:(lia)), (R (ss2 + 1) ltac:(lia)),
            (R (ss2 + 2) ltac:(lia)).
    replace (ss2 + wsz) with (ls_strstart l) by (unfold ss2; lia).
    replace (ss2 + 1 + wsz) with (ls_strstart l + 1) by (unfold ss2; lia).
    replace (ss2 + 2 + wsz) with (ls_strstart l + 2) by (unfold ss2; lia).
    unfold h3 in Hsync2.
    exact Hsync2.
Qed.

(** ** 3. Through the read + blit + re-seed

    The blit can cover the very bytes the sync reads (when the OLD lookahead
    was short), so sync is NOT preserved through the blit — it is
    RE-ESTABLISHED by [fw_seed], which always follows it inside [fw_step].
    The two are therefore proved as one composite step. *)

(** [fw_seed] at [insert = 0] is an [ins_h] re-seed, nothing else. *)
Lemma fw_seed_insert0 : forall g l,
  ls_insert l = 0 ->
  fw_seed g l
  = if Z.leb MIN_MATCH (ls_lookahead l)
    then setL_insh
           (update_hash g (ls_window l (ls_strstart l))
              (ls_window l (ls_strstart l + 1))) l
    else l.
Proof.
  intros g l Hi0. unfold fw_seed. cbv zeta.
  rewrite Hi0. rewrite Z.add_0_r, Z.sub_0_r.
  destruct (Z.leb MIN_MATCH (ls_lookahead l)); [|reflexivity].
  replace (Z.to_nat 0 + 1)%nat with 1%nat by reflexivity.
  cbn [fw_insert].
  lsimp. rewrite Hi0. cbn [Z.eqb]. reflexivity.
Qed.

Lemma chaincl_blit_seed : forall g wbits hbits Ins l dat,
  GeomOk2 g wbits hbits ->
  ChainCl g Ins l ->
  0 <= zlen dat ->
  ChainCl g Ins (fw_seed g (fwp_blit dat l)).
Proof.
  intros g wbits hbits Ins l dat Hg Hc Hd.
  destruct Hc as [Hinv Hhi Hins0 Hsync].
  assert (Hext : arr_eq_on (ls_window l)
            (win_blit dat (ls_strstart l + ls_lookahead l) (ls_window l))
            0 (ls_strstart l + ls_lookahead l)).
  { intros i Hi. unfold win_blit. cbv zeta.
    replace ((ls_strstart l + ls_lookahead l <=? i) && _) with false
      by (symmetry; apply andb_false_iff; left; apply Z.leb_gt; lia).
    reflexivity. }
  assert (Hinv1 : ChainInv g
            (win_blit dat (ls_strstart l + ls_lookahead l) (ls_window l))
            (ls_prev l) (ls_head l)
            (ls_strstart l) (ls_lookahead l) Ins).
  { eapply (window_ext_inv g wbits hbits);
      first [ exact Hinv | exact Hext
            | exact (g2_wb0 _ _ _ Hg) | exact (g2_hb0 _ _ _ Hg)
            | exact (g2_ws _ _ _ Hg) | exact (g2_wm _ _ _ Hg)
            | exact (g2_hs _ _ _ Hg) | exact (g2_hm _ _ _ Hg)
            | exact (go_maxd _ (g2_geom _ _ _ Hg)) | lia ]. }
  assert (Hinv2 : ChainInv g
            (win_blit dat (ls_strstart l + ls_lookahead l) (ls_window l))
            (ls_prev l) (ls_head l)
            (ls_strstart l) (ls_lookahead l + zlen dat) Ins).
  { eapply (flr_advance g wbits hbits);
      first [ exact Hinv1
            | exact (g2_wb0 _ _ _ Hg) | exact (g2_hb0 _ _ _ Hg)
            | exact (g2_ws _ _ _ Hg) | exact (g2_wm _ _ _ Hg)
            | exact (g2_hs _ _ _ Hg) | exact (g2_hm _ _ _ Hg)
            | exact (go_maxd _ (g2_geom _ _ _ Hg)) | lia ]. }
  assert (Hins6 : ls_insert (fwp_blit dat l) = 0)
    by (unfold fwp_blit; cbv zeta; lsimp; exact Hins0).
  rewrite (fw_seed_insert0 g (fwp_blit dat l) Hins6).
  destruct (Z.leb_spec MIN_MATCH (ls_lookahead (fwp_blit dat l)))
    as [Hla|Hla].
  - (* re-seed: sync holds definitionally *)
    constructor.
    + unfold fwp_blit. cbv zeta. lsimp. exact Hinv2.
    + unfold fwp_blit. cbv zeta. lsimp. exact Hhi.
    + unfold fwp_blit. cbv zeta. lsimp. exact Hins0.
    + unfold SyncOK. lsimp.
      intros _ _. unfold h3. reflexivity.
  - (* no seed: the guard is dead, sync vacuous *)
    constructor.
    + unfold fwp_blit. cbv zeta. lsimp. exact Hinv2.
    + unfold fwp_blit. cbv zeta. lsimp. exact Hhi.
    + unfold fwp_blit. cbv zeta. lsimp. exact Hins0.
    + unfold SyncOK. intros _ Hla3. exfalso. lia.
Qed.

(** ** 5. One [fw_step], the loop, the high-water bump, [fill_window] *)

Lemma chaincl_highwater : forall g wbits hbits Ins l,
  GeomOk2 g wbits hbits ->
  ChainCl g Ins l ->
  ChainCl g Ins (fw_highwater l).
Proof.
  intros g wbits hbits Ins l Hg Hc.
  destruct Hc as [Hinv Hhi Hins0 Hsync].
  unfold fw_highwater. cbv zeta.
  destruct (Z.ltb (ls_highwater l) (ls_windowsize l)) eqn:H1;
    [|now constructor].
  destruct (Z.ltb (ls_highwater l) (ls_strstart l + ls_lookahead l)) eqn:H2.
  - apply Z.ltb_lt in H2.
    assert (Hext : arr_eq_on (ls_window l)
              (win_zero (ls_strstart l + ls_lookahead l)
                 (if Z.ltb WIN_INIT
                       (ls_windowsize l - (ls_strstart l + ls_lookahead l))
                  then WIN_INIT
                  else ls_windowsize l - (ls_strstart l + ls_lookahead l))
                 (ls_window l))
              0 (ls_strstart l + ls_lookahead l)).
    { intros i Hi. unfold win_zero.
      replace ((ls_strstart l + ls_lookahead l <=? i) && _) with false
        by (symmetry; apply andb_false_iff; left; apply Z.leb_gt; lia).
      reflexivity. }
    constructor; lsimp; try assumption.
    + eapply (window_ext_inv g wbits hbits);
        first [ exact Hinv | exact Hext
              | exact (g2_wb0 _ _ _ Hg) | exact (g2_hb0 _ _ _ Hg)
              | exact (g2_ws _ _ _ Hg) | exact (g2_wm _ _ _ Hg)
              | exact (g2_hs _ _ _ Hg) | exact (g2_hm _ _ _ Hg)
              | exact (go_maxd _ (g2_geom _ _ _ Hg)) | lia ].
    + unfold SyncOK in *. lsimp. intros Hi0 Hla3.
      unfold MIN_MATCH in Hla3.
      unfold win_zero, h3.
      repeat (replace ((ls_strstart l + ls_lookahead l <=? _) && _)
                with false
                by (symmetry; apply andb_false_iff; left;
                    apply Z.leb_gt; lia)).
      unfold h3 in Hsync. apply Hsync; [exact Hi0 | unfold MIN_MATCH; lia].
  - destruct (Z.ltb (ls_highwater l)
                (ls_strstart l + ls_lookahead l + WIN_INIT)) eqn:H3;
      [|now constructor].
    apply Z.ltb_ge in H2.
    assert (Hext : arr_eq_on (ls_window l)
              (win_zero (ls_highwater l)
                 (if Z.ltb (ls_windowsize l - ls_highwater l)
                       (ls_strstart l + ls_lookahead l + WIN_INIT
                        - ls_highwater l)
                  then ls_windowsize l - ls_highwater l
                  else ls_strstart l + ls_lookahead l + WIN_INIT
                       - ls_highwater l)
                 (ls_window l))
              0 (ls_strstart l + ls_lookahead l)).
    { intros i Hi. unfold win_zero.
      replace ((ls_highwater l <=? i) && _) with false
        by (symmetry; apply andb_false_iff; left; apply Z.leb_gt; lia).
      reflexivity. }
    constructor; lsimp; try assumption.
    + eapply (window_ext_inv g wbits hbits);
        first [ exact Hinv | exact Hext
              | exact (g2_wb0 _ _ _ Hg) | exact (g2_hb0 _ _ _ Hg)
              | exact (g2_ws _ _ _ Hg) | exact (g2_wm _ _ _ Hg)
              | exact (g2_hs _ _ _ Hg) | exact (g2_hm _ _ _ Hg)
              | exact (go_maxd _ (g2_geom _ _ _ Hg)) | lia ].
    + unfold SyncOK in *. lsimp. intros Hi0 Hla3.
      unfold MIN_MATCH in Hla3.
      unfold win_zero, h3.
      repeat (replace ((ls_highwater l <=? _) && _)
                with false
                by (symmetry; apply andb_false_iff; left;
                    apply Z.leb_gt; lia)).
      unfold h3 in Hsync. apply Hsync; [exact Hi0 | unfold MIN_MATCH; lia].
Qed.

Lemma fw_step_chain : forall g wbits hbits wrap l st slid Ins,
  GeomOk2 g wbits hbits ->
  WinInv g slid l st ->
  ChainCl g Ins l ->
  exists Ins',
    ChainCl g Ins' (snd (fst (fw_step g wrap l st))).
Proof.
  intros g wbits hbits wrap l st slid Ins Hg Hw Hc.
  rewrite fw_step_shape.
  (* the pre part, shared by both arms *)
  assert (Hpre : exists Ins',
    ChainCl g Ins' (fst (fwp_pre g l))
    /\ (forall p, Ins' p -> p < ls_strstart (fst (fwp_pre g l)))).
  { unfold fwp_pre. cbv zeta.
    destruct (Z.leb_spec (dg_w_size g + dg_max_dist g) (ls_strstart l))
      as [Hsl|Hsl]; cbn [fst].
    - exists (fun p => 0 <= p /\ Ins (p + dg_w_size g)).
      pose proof (chaincl_slide g wbits hbits l st slid Ins Hg Hw Hc Hsl)
        as Hc'.
      split; [exact Hc' | exact (cc_hi _ _ _ Hc')].
    - exists Ins. split; [exact Hc | exact (cc_hi _ _ _ Hc)]. }
  destruct Hpre as (Ins1 & Hc1 & _).
  destruct (Z.eqb (zlen (zs_in st)) 0); cbn [fst snd].
  - exists Ins1. exact Hc1.
  - exists Ins1.
    apply (chaincl_blit_seed g wbits hbits); [exact Hg | exact Hc1|].
    unfold zlen. lia.
Qed.

Lemma fw_loop_chain : forall f g wbits hbits wrap l st slid Ins,
  GeomOk2 g wbits hbits ->
  WinInv g slid l st -> CkInv wrap st ->
  ChainCl g Ins l ->
  exists Ins',
    ChainCl g Ins' (fst (fw_loop f g wrap l st)).
Proof.
  induction f as [|f IH]; intros g wbits hbits wrap l st slid Ins Hg Hw Hck Hc.
  - cbn [fw_loop fst]. exists Ins. exact Hc.
  - cbn [fw_loop].
    destruct (fw_step_chain g wbits hbits wrap l st slid Ins Hg Hw Hc)
      as (Ins1 & Hc1).
    destruct (fw_step_pres g wrap l st slid (g2_geom _ _ _ Hg) Hw Hck)
      as (slid1 & HP1 & Hck1).
    destruct (fw_step g wrap l st) as [[brk l1] st1] eqn:Estep.
    cbn [fst snd] in Hc1, HP1, Hck1.
    destruct brk.
    + exists Ins1. exact Hc1.
    + destruct ((Z.ltb (ls_lookahead l1) MIN_LOOKAHEAD)
                  && negb (Z.eqb (zlen (zs_in st1)) 0)).
      * exact (IH g wbits hbits wrap l1 st1 slid1 Ins1 Hg
                 (sp_inv _ _ _ _ _ _ _ HP1) Hck1 Hc1).
      * exists Ins1. exact Hc1.
Qed.

Theorem fill_window_chain : forall g wbits hbits wrap l st slid Ins,
  GeomOk2 g wbits hbits ->
  WinInv g slid l st -> CkInv wrap st ->
  ChainCl g Ins l ->
  exists Ins',
    ChainCl g Ins' (fst (fill_window g wrap l st)).
Proof.
  intros g wbits hbits wrap l st slid Ins Hg Hw Hck Hc.
  unfold fill_window. cbv zeta. cbn [fst].
  destruct (fw_loop_chain (Z.to_nat (zlen (zs_in st)) + 2) g wbits hbits wrap
              l st slid Ins Hg Hw Hck Hc) as (Ins1 & Hc1).
  exists Ins1.
  apply (chaincl_highwater g wbits hbits); [exact Hg | exact Hc1].
Qed.

Print Assumptions fill_window_chain.
Print Assumptions chaincl_reset.
