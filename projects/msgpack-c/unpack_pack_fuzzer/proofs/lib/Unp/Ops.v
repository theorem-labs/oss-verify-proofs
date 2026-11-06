(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 W64Proofs Val IMap Mem State MemProofs.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import Model Layout Inv Steps OpsBridge.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Cost Acct.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Pot.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Export Seal SealX.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap Require Import Op.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val Mem St MemP UB HeapOp.
Open Scope Z_scope.
Unset Lia Cache.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.

Module UO.

Definition CM_NONE : Z := 0.
Definition CM_UNP : Z := 1.
Definition CM_CONS : Z := 2.

Fixpoint obj_bodies (o : obj) : list (Z * Z) :=
  match o with
  | OStr p n | OBin p n => if p =? 0 then [] else [(p, n)]
  | OExt p n => [(p, n + 1)]
  | OArr _ kids | OMap _ kids =>
      (fix bs (l : list obj) : list (Z * Z) := match l with [] => [] | o' :: l' => obj_bodies o' ++ bs l' end) kids
  | _ => []
  end.
Definition objs_bodies (l : list obj) : list (Z * Z) := flat_map obj_bodies l.

Definition obj_cnt (o : obj) : Z :=
  match o with
  | OArr _ kids => Z.of_nat (length kids)
  | OMap _ kids => Z.of_nat (length kids) / 2
  | OStr _ n | OBin _ n | OExt _ n => n
  | _ => 0
  end.
Lemma obj_cnt_of_type : forall o, (obj_type o = T_ARRAY \/ obj_type o = T_MAP) -> obj_cnt o = obj_count o.
Proof. intros [] [H|H]; cbn in H |- *; try reflexivity; discriminate H. Qed.
Lemma obj_bodies_kids : forall kids,
  (fix bs (l : list obj) : list (Z * Z) := match l with [] => [] | o' :: l' => obj_bodies o' ++ bs l' end) kids = objs_bodies kids.
Proof. induction kids as [|o l IH]; [reflexivity|]. cbn [objs_bodies flat_map]. rewrite IH. reflexivity. Qed.
Lemma obj_bodies_arr : forall p kids, obj_bodies (OArr p kids) = objs_bodies kids.
Proof. intros. cbn [obj_bodies]. apply obj_bodies_kids. Qed.
Lemma obj_bodies_map : forall p kids, obj_bodies (OMap p kids) = objs_bodies kids.
Proof. intros. cbn [obj_bodies]. apply obj_bodies_kids. Qed.

Definition range_ok (z : zoneg) (ls : list level) (r : Z * Z) : Prop :=
  0 <= snd r /\ in_alloc z (fst r) (snd r) /\ forall l, In l ls -> rdisj (fst r) (snd r) (lv_slot l) (lv_unfilled l).
Definition bodies_ok (z : zoneg) (ls : list level) (o : obj) : Prop := Forall (range_ok z ls) (obj_bodies o).

Definition completed_ok (bm : bmem) (z : zoneg) (ls : list level) : Prop :=
  forall l, In l ls -> forall i, 0 <= i < lv_k l ->
    exists o, tree_at bm z (lv_P l + OBJ_SIZE * i) o /\
              (forall c, In c (obj_cells (lv_P l + OBJ_SIZE * i) o) -> Inv.cell_ok z ls c) /\ bodies_ok z ls o.

Lemma completed_ok_wf : forall bm z ls, completed_ok bm z ls -> completed_wf bm z ls.
Proof. intros bm z ls H l Hl i Hi. destruct (H l Hl i Hi) as (o & A & B & _). eauto. Qed.

Definition hdr_at (bm : bmem) (a : Z) (o : obj) : Prop :=
  u32_at bm a (obj_type o) /\
  match o with
  | ONil => True
  | OBool b => u8_at bm (a + 8) (if b then 1 else 0)
  | OPos u => u64_at bm (a + 8) u
  | ONeg i => u64_at bm (a + 8) (enc64 i)
  | OF32 bits => u64_at bm (a + 8) bits
  | OF64 bits => u64_at bm (a + 8) bits
  | OStr p n | OBin p n | OExt p n => u32_at bm (a + 8) n /\ u64_at bm (a + 16) p
  | OArr p kids => u32_at bm (a + 8) (Z.of_nat (length kids)) /\ u64_at bm (a + 16) p
  | OMap p kids => u32_at bm (a + 8) (Z.of_nat (length kids) / 2) /\ u64_at bm (a + 16) p
  end.
Definition kids_at (bm : bmem) (o : obj) : Prop :=
  match o with OArr p kids | OMap p kids => objs_at bm p kids | _ => True end.

Lemma obj_at_split : forall bm a o, obj_at bm a o <-> hdr_at bm a o /\ kids_at bm o.
Proof.
  intros bm a o. destruct o; first [rewrite obj_at_arr | rewrite obj_at_map | idtac]; unfold hdr_at, kids_at; cbn [obj_at obj_type]; tauto.
Qed.

Lemma kids_at_frame : forall m m' a o,
  (forall c, In c (tl (obj_cells a o)) -> agree_on m m' c OBJ_SIZE) -> kids_at m o -> kids_at m' o.
Proof.
  intros m m' a o AG K. destruct o; unfold kids_at in *; try exact I.
  all: first [rewrite obj_cells_arr in AG| rewrite obj_cells_map in AG]; cbn [tl] in AG;
    apply objs_at_nth; intros i o Hi; apply (obj_at_frame m m'); [| exact (proj1 (objs_at_nth _ _ _) K i o Hi)];
    intros c Hc; apply AG; apply in_kids_cells; eauto.
Qed.

Record ucargs := UC {
  c_root : Z;
  c_cb : Z; c_ce : Z; c_ccap : Z;
  c_vb : Z; c_ve : Z; c_vcap : Z;
  c_zptr : Z; c_zfree : Z; c_c0 : Z;
  c_slot : Z;
  c_tD : Z; c_restD : Z;
  c_rootT : Z; c_n1 : Z; c_P1 : Z
}.

Definition decode_uc (ca : list word) : option ucargs :=
  match ca with
  | [a0; a1; a2; a3; a4; a5; a6; a7; a8; a9; a10; a11; a12; a13; a14; a15; _zh] =>
      Some (UC (bv_unsigned a0) (bv_unsigned a1) (bv_unsigned a2) (bv_unsigned a3) (bv_unsigned a4) (bv_unsigned a5)
               (bv_unsigned a6) (bv_unsigned a7) (bv_unsigned a8) (bv_unsigned a9) (bv_unsigned a10) (bv_unsigned a11)
               (bv_unsigned a12) (bv_unsigned a13) (bv_unsigned a14) (bv_unsigned a15))
  | _ => None
  end.

Section WithSegs.
Variable segs : list Segment.

Variable XW : client_world.

Definition cstk_block (g : unpg) : Z * Z := (v_begin (u_cstk g), v_bytes (u_cstk g)).
Definition vstk_block (g : unpg) : Z * Z := (v_begin (u_vstk g), v_bytes (u_vstk g)).
Definition owned (g : unpg) : list (Z * Z) := cstk_block g :: vstk_block g :: map chunk_block (z_chunks (u_zone g)).

Definition link (u : ucargs) (g : unpg) : Prop :=
  u_root g = c_root u /\
  v_begin (u_cstk g) = c_cb u /\ v_end (u_cstk g) = c_ce u /\ v_capend (u_cstk g) = c_ccap u /\
  v_begin (u_vstk g) = c_vb u /\ v_end (u_vstk g) = c_ve u /\ v_capend (u_vstk g) = c_vcap u /\
  z_ptr (u_zone g) = c_zptr u /\ z_free (u_zone g) = c_zfree u /\ z_head (u_zone g) = c_c0 u /\
  (u_levels g <> [] ->
     u_cur_slot g = c_slot u /\
     (exists lD, last_opt (u_levels g) = Some lD /\ ctype_code (lv_t lD) = c_tD u /\ lv_rest lD = c_restD u) /\
     (exists l1 ls1, u_levels g = l1 :: ls1 /\ container_type (lv_t l1) = c_rootT u /\ lv_n l1 = c_n1 u /\ lv_P l1 = c_P1 u)).

Definition pure_ok (g : unpg) : Prop :=
  vec_valid (u_cstk g) /\ v_elt (u_cstk g) = 8 /\ v_size (u_cstk g) = u_D g /\ cap32_b (v_cap (u_cstk g)) = true /\
  vec_valid (u_vstk g) /\ v_elt (u_vstk g) = 8 /\ v_size (u_vstk g) = u_D g + 1 /\ cap32_b (v_cap (u_vstk g)) = true /\
  Forall level_valid (u_levels g) /\ u_D g <= LIMIT /\ levels_alloc (u_zone g) (u_levels g) /\ zone_valid (u_zone g).

Definition blocks_tied (l : list (Z * Z)) : Prop :=
  match l with c :: v :: _ => snd v = snd c \/ snd v = 2 * snd c | _ => True end.
Definition own_ok (g : unpg) (LB : blocks) : Prop :=
  (forall b, In b (owned g) -> In b LB) /\
  ForallOrdPairs (fun b b' => rdisj (fst b) (snd b) (fst b') (snd b')) (owned g) /\
  blocks_tied (owned g).

Definition K_CTOP : Z := 2.  Definition K_VTOP : Z := 3.  Definition K_SLOT : Z := 4.  Definition K_ZONE : Z := 5.
Definition sub_ok (md : Z) (g : unpg) (w : window) : Prop :=
  let lo := w_lo w in let hi := w_lo w + w_len w in
  (w_kind w = K_CTOP /\ v_begin (u_cstk g) <= lo /\ v_end (u_cstk g) - 8 <= lo /\ hi <= v_capend (u_cstk g))
  \/ (w_kind w = K_VTOP /\ v_begin (u_vstk g) <= lo /\ v_end (u_vstk g) - 8 <= lo /\ hi <= v_capend (u_vstk g))
  \/ (w_kind w = K_SLOT /\ exists lD, last_opt (u_levels g) = Some lD /\
        (if md =? CM_CONS then lv_slot lD + OBJ_SIZE else lv_slot lD) <= lo /\ hi <= lv_slot lD + lv_unfilled lD)
  \/ (w_kind w = K_ZONE /\ z_ptr (u_zone g) <= lo /\ hi <= chunk_hi (hd (0,0) (z_chunks (u_zone g)))).

Definition wins_ok (md : Z) (g : unpg) (ws : list window) : Prop :=
  Forall (fun w => w_kind w <> K_STACK ->
            ((w_kind w = K_BLOCK \/ K_GHOST <= w_kind w) /\ forall b, In b (owned g) -> forall a, in_iv (w_iv w) a -> ~ in_iv b a)
            \/ (w_kind w <> K_BLOCK /\ sub_ok md g w)) ws.

Definition mem_ok (md : Z) (bm : bmem) (g : unpg) : Prop :=
  let ls := u_levels g in let z := u_zone g in
  cstk_at bm (v_begin (u_cstk g)) (removelast ls) /\
  (ls <> [] -> u64_at bm (v_begin (u_vstk g)) (u_root g)) /\ vstk_at bm (v_begin (u_vstk g) + 8) (removelast ls) /\
  chunks_at bm (z_chunks z) /\
  conts_at bm (tl (containers (u_root g) ls)) (tl ls) /\
  completed_ok bm z ls.

Definition POT_BASE : Z := 3 * 2 ^ 61.
Definition POT_SPAN : Z := 2 ^ 42.
Definition pot_win (w : window) : Prop := w_kind w = K_STACK /\ w_len w = 0 /\ POT_BASE <= w_lo w <= POT_BASE + POT_SPAN.
Definition pot_at (ws : list window) (v : Z) : Prop := forall w, In w ws -> pot_win w -> w_lo w = POT_BASE + v.

Lemma pot_at_ws : forall ws ws' v, pot_at ws v -> (forall w, In w ws' -> pot_win w -> In w ws) -> pot_at ws' v.
Proof. intros ws ws' v H HW w Hw PW. exact (H w (HW w Hw PW) PW). Qed.
Lemma pot_at_eq : forall ws v v', pot_at ws v -> v' = v -> pot_at ws v'.
Proof. intros ws v v' H ->. exact H. Qed.

Lemma pot_at_app_heap : forall ws l v, pot_at ws v -> (forall w, In w l -> w_kind w <> K_STACK) -> pot_at (ws ++ l) v.
Proof.
  intros ws l v H N. apply (pot_at_ws ws (ws ++ l) v H). intros w Hw (K & _). apply in_app_or in Hw as [Hw|Hw]; [exact Hw| exfalso; exact (N w Hw K)].
Qed.
Lemma pot_at_none : forall ws v, (forall w, In w ws -> ~ pot_win w) -> pot_at ws v.
Proof. intros ws v N w Hw PW. exfalso. exact (N w Hw PW). Qed.

Definition cons_ok (md : Z) (ws : list window) (u : ucargs) (bm : bmem) (g : unpg) : Prop :=
  md = CM_CONS ->
  let ls := u_levels g in let z := u_zone g in
  exists o, tree_wf bm z o /\ kids_at bm o /\
    (ls <> [] -> hdr_at bm (u_cur_slot g) o) /\
    (ls = [] -> obj_type o = c_rootT u /\ obj_cnt o = c_n1 u /\ obj_ptr o = c_P1 u) /\
    (forall c, In c (tl (obj_cells (u_cur_slot g) o)) -> Inv.cell_ok z ls c) /\ bodies_ok z ls o /\
    (Cost.obj_depth o + length ls <= 1001)%nat /\
    (exists S, Pot.Pot.kids_pk bm z ls S /\ pot_at ws (Pot.Pot.pot_val ls S (Pot.Pot.pk10_tree o))).

Definition acct_ex (bm : bmem) (g : unpg) : Prop := exists X, Acct.acct_ok bm (u_zone g) (u_levels g) X.

Definition pot_unp (md : Z) (ws : list window) (bm : bmem) (g : unpg) : Prop :=
  md = CM_UNP -> exists S, Pot.Pot.kids_pk bm (u_zone g) (u_levels g) S /\ pot_at ws (Pot.Pot.pot_val (u_levels g) S 0).
Definition acct_pot (md : Z) (ws : list window) (bm : bmem) (g : unpg) : Prop := acct_ex bm g /\ pot_unp md ws bm g.

Lemma cons_ok_ws : forall md ws ws' u bm g, cons_ok md ws u bm g -> (forall w, In w ws' -> pot_win w -> In w ws) -> cons_ok md ws' u bm g.
Proof.
  intros md ws ws' u bm g H HW MD. destruct (H MD) as (o & TW & KA & HD & RT & CL & BD & DP & S & KP & PA).
  exists o. split; [exact TW|]. split; [exact KA|]. split; [exact HD|]. split; [exact RT|]. split; [exact CL|]. split; [exact BD|]. split; [exact DP|].
  exists S. split; [exact KP| exact (pot_at_ws ws ws' _ PA HW)].
Qed.
Lemma pot_unp_ws : forall md ws ws' bm g, pot_unp md ws bm g -> (forall w, In w ws' -> pot_win w -> In w ws) -> pot_unp md ws' bm g.
Proof. intros md ws ws' bm g H HW MD. destruct (H MD) as (S & KP & PA). exists S. split; [exact KP| exact (pot_at_ws ws ws' _ PA HW)]. Qed.
Lemma acct_pot_ws : forall md ws ws' bm g, acct_pot md ws bm g -> (forall w, In w ws' -> pot_win w -> In w ws) -> acct_pot md ws' bm g.
Proof. intros md ws ws' bm g [AX PT] HW. split; [exact AX| exact (pot_unp_ws md ws ws' bm g PT HW)]. Qed.

Lemma pot_handover : forall ws bm g o, u_levels g = [] ->
  (exists S, Pot.Pot.kids_pk bm (u_zone g) (u_levels g) S /\ pot_at ws (Pot.Pot.pot_val (u_levels g) S (Pot.Pot.pk10_tree o))) ->
  pot_at ws (Pot.Pot.Q0 + 4 * Pot.Pot.pk10_tree o).
Proof.
  intros ws bm g o E (S & KP & PA). rewrite E in KP, PA. rewrite (Pot.Pot.kids_pk_nil_inv _ _ _ KP), Pot.Pot.pot_val_nil in PA. exact PA.
Qed.

Lemma pot_app_heap : forall (ws l : list window), (forall w, In w l -> w_kind w <> K_STACK) -> forall w, In w (ws ++ l) -> pot_win w -> In w ws.
Proof. intros ws l N w Hw (K & _). apply in_app_or in Hw as [Hw|Hw]; [exact Hw| exfalso; exact (N w Hw K)]. Qed.

Definition unp_client (md : Z) (u : ucargs) (LB : blocks) (ws : list window) (m : word -> option byte) : Prop :=
  exists g, link u g /\ pure_ok g /\ own_ok g LB /\ wins_ok md g ws /\ mem_ok md (bmem_of segs m) g /\ cons_ok md ws u (bmem_of segs m) g /\
            acct_pot md ws (bmem_of segs m) g /\
            Seal.seal_ok ws (z_chunks (u_zone g)).

Definition no_sub (w : window) : Prop := ~ (K_SUB <= w_kind w < K_GHOST).
Definition cw_unp_holds (md : Z) (ca : list word) (LB : blocks) (ws : list window) (m : word -> option byte) : Prop :=
  if md =? CM_NONE then Forall no_sub ws
  else if (md =? CM_UNP) || (md =? CM_CONS) then
    match decode_uc ca with Some u => unp_client md u LB ws m | None => False end
  else cw_holds XW md ca LB ws m.

Lemma own_ok_grow : forall g LB b n, own_ok g LB -> own_ok g ((b, n) :: LB).
Proof. intros g LB b n [O1 O2]. split; [| exact O2]. intros x Hx. right. exact (O1 x Hx). Qed.
Lemma own_tied : forall g LB, own_ok g LB ->
  v_bytes (u_vstk g) = v_bytes (u_cstk g) \/ v_bytes (u_vstk g) = 2 * v_bytes (u_cstk g).
Proof. intros g LB (_ & _ & T). exact T. Qed.

Lemma wins_ok_grow : forall md g LB ws b n, own_ok g LB -> wins_ok md g ws ->
  (forall a, in_iv (b, n) a -> ~ in_user LB a) -> wins_ok md g (ws ++ [Win b n K_BLOCK]).
Proof.
  intros md g LB ws b n [O1 _] Wk FR. unfold wins_ok in *. apply Forall_app. split; [exact Wk|]. constructor; [|constructor].
  intros _. left. split; [left; reflexivity|]. intros ob Hob a Ha Hb. apply (FR a Ha). unfold in_user. apply in_ivs_In. exists ob. split; [exact (O1 ob Hob)| exact Hb].
Qed.

Lemma cw_unp_grow : forall md ca LB ws m b n, cw_unp_holds md ca LB ws m ->
  (forall a, in_iv (b, n) a -> ~ in_user LB a) ->
  cw_unp_holds md ca ((b, n) :: LB) (ws ++ [Win b n K_BLOCK]) m.
Proof.
  intros md ca LB ws m b n H FR. unfold cw_unp_holds in *.
  destruct (md =? CM_NONE); [apply Forall_app; split; [exact H| constructor; [unfold no_sub; cbn [w_kind]; unfold K_SUB, K_BLOCK, K_GHOST; lia| constructor]]|].
  destruct ((md =? CM_UNP) || (md =? CM_CONS)); [| exact (cw_grow XW md ca LB ws m b n H FR)].
  destruct (decode_uc ca) as [u|]; [|exact H].
  assert (NP : forall w, In w (ws ++ [Win b n K_BLOCK]) -> pot_win w -> In w ws).
  { apply pot_app_heap. intros w [<-|[]]. cbn. unfold K_BLOCK, K_STACK. lia. }
  destruct H as (g & L & P & O & Wk & M & CS & AX & SE). exists g. split; [exact L|]. split; [exact P|]. split; [| split; [|split; [exact M| split; [exact (cons_ok_ws _ _ _ _ _ _ CS NP)| split; [exact (acct_pot_ws _ _ _ _ _ AX NP)|]]]]].
  - apply own_ok_grow. exact O.
  - eapply wins_ok_grow; eassumption.
  - apply SealX.seal_ok_app_other; [exact SE|]. intros w [<-|[]]. cbn. unfold Seal.K_TWIN, K_BLOCK. lia.
Qed.

Lemma owned_pos : forall g, pure_ok g -> forall ob, In ob (owned g) -> 0 < snd ob.
Proof.
  intros g (VC & EC & SC & CC & VV & EV & SV & CV & LV & DL & LA & ZV) ob Hob.
  unfold owned in Hob. cbn [In] in Hob.
  assert (CAP : forall c, cap32_b c = true -> 32 <= c).
  { intros c Hc. unfold cap32_b in Hc. apply andb_prop in Hc as [Hc _]. apply andb_prop in Hc as [Hc _].
    apply Z.leb_le in Hc. unfold EMBED_STACK in Hc. exact Hc. }
  destruct Hob as [<-|[<-|Hob]].
  - cbn [snd cstk_block]. unfold v_bytes. rewrite EC. pose proof (CAP _ CC). lia.
  - cbn [snd vstk_block]. unfold v_bytes. rewrite EV. pose proof (CAP _ CV). lia.
  - apply in_map_iff in Hob as (c & <- & Hc). cbn [snd chunk_block].
    destruct ZV as (_ & _ & V3 & _). destruct (V3 c Hc) as (_ & _ & S). unfold CHUNK_HDR, CHUNK_SIZE0 in *. lia.
Qed.

Lemma own_ok_free : forall md g LB ws b n, pure_ok g -> own_ok g LB -> wins_ok md g ws -> In (Win b n K_BLOCK) ws ->
  own_ok g (remove iv_eq_dec (b, n) LB).
Proof.
  intros md g LB ws b n P [O1 O2] Wk Hin. split; [| exact O2].
  intros x Hx. apply in_in_remove; [| exact (O1 x Hx)]. intros E. subst x.
  pose proof (owned_pos g P _ Hx) as POS. cbn [snd] in POS.
  destruct (proj1 (Forall_forall _ _) Wk _ Hin ltac:(cbn [w_kind]; discriminate)) as [[_ D]|[NB _]].
  - apply (D (b, n) Hx b); unfold in_iv, w_iv; cbn [fst snd w_lo w_len]; lia.
  - apply NB. reflexivity.
Qed.

Lemma cw_unp_free : forall md ca LB ws m b n ws', cw_unp_holds md ca LB ws m -> In (Win b n K_BLOCK) ws ->
  (forall w, In w ws' <-> In w ws /\ w <> Win b n K_BLOCK) ->
  cw_unp_holds md ca (remove iv_eq_dec (b, n) LB) ws' m.
Proof.
  intros md ca LB ws m b n ws' H Hin Hws'. unfold cw_unp_holds in *.
  destruct (md =? CM_NONE); [apply Forall_forall; intros w Hw; apply Hws' in Hw as [Hw _]; exact (proj1 (Forall_forall _ _) H w Hw)|].
  destruct ((md =? CM_UNP) || (md =? CM_CONS)); [| exact (cw_free XW md ca LB ws m b n ws' H Hin Hws')].
  destruct (decode_uc ca) as [u|]; [|exact H].
  assert (NP : forall w, In w ws' -> pot_win w -> In w ws) by (intros w Hw _; apply Hws' in Hw as [Hw _]; exact Hw).
  destruct H as (g & L & P & O & Wk & M & CS & AX & SE). exists g. split; [exact L|]. split; [exact P|]. split; [| split; [|split; [exact M| split; [exact (cons_ok_ws _ _ _ _ _ _ CS NP)| split; [exact (acct_pot_ws _ _ _ _ _ AX NP)|]]]]].
  - eapply own_ok_free; eassumption.
  - unfold wins_ok in *. apply Forall_forall. intros w Hw. apply Hws' in Hw as [Hw _]. exact (proj1 (Forall_forall _ _) Wk w Hw).
  - apply (Seal.seal_ok_ws ws _ ws' SE). intros w Hw _. apply Hws' in Hw as [Hw _]. exact Hw.
Qed.

Lemma readable_agree : forall (m m' : bmem) a n, agree_on m m' a (Z.of_nat n) -> readable m a n -> readable m' a n.
Proof. intros m m' a n A [v Hv]. exists v. rewrite (rdZ_agree m m' a n A). exact Hv. Qed.

Lemma removelast_snoc : forall {A} (l : list A) x, removelast (l ++ [x]) = l.
Proof. intros A l x. unfold removelast. rewrite rev_app_distr. cbn. apply rev_involutive. Qed.
Lemma removelast_nil : forall {A}, removelast (@nil A) = [].
Proof. reflexivity. Qed.

Lemma tree_wf_agree : forall (m m' : bmem) z o,
  (forall b, In b (obj_bodies o) -> agree_on m m' (fst b) (snd b)) -> tree_wf m z o -> tree_wf m' z o.
Proof.
  intros m m' z. apply (obj_ind_size (fun o => (forall b, In b (obj_bodies o) -> agree_on m m' (fst b) (snd b)) -> tree_wf m z o -> tree_wf m' z o)).
  intros o IH AG H. destruct o; try exact H.
  -   cbn [tree_wf] in H |- *. destruct H as (A & B & C). split; [exact A|]. split; [exact B|].
    intros Hp. destruct (C Hp) as [C1 C2]. split; [exact C1|].
    eapply readable_agree; [|exact C2]. rewrite Z2Nat.id by lia. apply (AG (p, n)). cbn [obj_bodies].
    destruct (Z.eqb_spec p 0); [contradiction| left; reflexivity].
  -   cbn [tree_wf] in H |- *. destruct H as (A & B & C). split; [exact A|]. split; [exact B|].
    intros Hp. destruct (C Hp) as [C1 C2]. split; [exact C1|].
    eapply readable_agree; [|exact C2]. rewrite Z2Nat.id by lia. apply (AG (p, n)). cbn [obj_bodies].
    destruct (Z.eqb_spec p 0); [contradiction| left; reflexivity].
  -   cbn [tree_wf] in H |- *. destruct H as (A & B & C & D & E). repeat split; try assumption.
    eapply readable_agree; [|exact E]. rewrite Z2Nat.id by lia. apply (AG (p, n + 1)). cbn [obj_bodies]. left; reflexivity.
  -   apply tree_wf_arr in H. apply tree_wf_arr. destruct H as (H1 & H2 & H3 & H4). split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
    apply trees_wf_forall. intros k Hk. apply IH.
    + rewrite obj_size_arr. pose proof (in_kids_size k kids Hk). lia.
    + intros b Hb. apply AG. rewrite obj_bodies_arr. unfold objs_bodies. apply in_flat_map. eauto.
    + exact (proj1 (trees_wf_forall _ _ _) H4 k Hk).
  -   apply tree_wf_map in H. apply tree_wf_map. destruct H as (H0 & H1 & H2 & H3 & H4). split; [exact H0|]. split; [exact H1|].
    split; [exact H2|]. split; [exact H3|].
    apply trees_wf_forall. intros k Hk. apply IH.
    + rewrite obj_size_map. pose proof (in_kids_size k kids Hk). lia.
    + intros b Hb. apply AG. rewrite obj_bodies_map. unfold objs_bodies. apply in_flat_map. eauto.
    + exact (proj1 (trees_wf_forall _ _ _) H4 k Hk).
Qed.

Lemma tree_at_agree : forall (m m' : bmem) z a o,
  (forall c, In c (obj_cells a o) -> agree_on m m' c OBJ_SIZE) ->
  (forall b, In b (obj_bodies o) -> agree_on m m' (fst b) (snd b)) ->
  tree_at m z a o -> tree_at m' z a o.
Proof.
  intros m m' z a o AC AB [H1 H2]. split; [eapply obj_at_frame; eauto| eapply tree_wf_agree; eauto].
Qed.

Section Frame.
  Variables (md : Z) (g : unpg) (LB : blocks) (ws : list window) (m m' : word -> option byte).
  Hypothesis P : pure_ok g.
  Hypothesis O : own_ok g LB.
  Hypothesis W : wins_ok md g ws.
  Hypothesis FR : forall a, 0 <= a < two64 -> in_user LB a -> ~ in_ws (heap_ws ws) a -> m (Z_to_bv 64 a) = m' (Z_to_bv 64 a).
  #[local] Notation bm := (bmem_of segs m).
  #[local] Notation bm' := (bmem_of segs m').
  #[local] Notation ls := (u_levels g).
  #[local] Notation z := (u_zone g).

  Definition safe (a : Z) : Prop := forall w, In w ws -> sub_ok md g w -> ~ in_iv (w_iv w) a.

  Lemma agree_byte : forall a ob, In ob (owned g) -> in_iv ob a -> safe a -> bm' a = bm a.
  Proof.
    intros a ob Hob Ha SF. unfold bmem_of.
    destruct (Z.leb_spec 0 a); destruct (Z.ltb_spec a two64); cbn [andb]; try reflexivity.
    rewrite (rb_ext segs m m' a); [reflexivity|]. symmetry. apply FR; [lia| |].
    - unfold in_user. apply in_ivs_In. exists ob. split; [exact (proj1 O ob Hob)| exact Ha].
    - intros X. unfold in_ws, heap_ws in X. apply in_ivs_In in X as (v & Hv & Hin). apply in_map_iff in Hv as (w & <- & Hw).
      apply filter_In in Hw as [Hw Hk].
      destruct (Z.eqb_spec (w_kind w) K_STACK) as [|NK]; [discriminate|].
      destruct (proj1 (Forall_forall _ _) W w Hw NK) as [[_ D]|[NB SO]].
      + exact (D ob Hob a Hin Ha).
      + exact (SF w Hw SO Hin).
  Qed.

  Lemma pf : vec_valid (u_cstk g) /\ v_elt (u_cstk g) = 8 /\ v_size (u_cstk g) = u_D g /\
             vec_valid (u_vstk g) /\ v_elt (u_vstk g) = 8 /\ v_size (u_vstk g) = u_D g + 1 /\
             Forall level_valid ls /\ levels_alloc z ls /\ zone_valid z.
  Proof. destruct P as (VC & EC & SC & CC & VV & EV & SV & CV & LV & DL & LA & ZV). exact (conj VC (conj EC (conj SC (conj VV (conj EV (conj SV (conj LV (conj LA ZV)))))))). Qed.

  Lemma owned_cstk : In (cstk_block g) (owned g). Proof. left; reflexivity. Qed.
  Lemma owned_vstk : In (vstk_block g) (owned g). Proof. right; left; reflexivity. Qed.
  Lemma owned_chunk : forall c, In c (z_chunks z) -> In (chunk_block c) (owned g).
  Proof. intros c Hc. right; right. apply in_map. exact Hc. Qed.

  Lemma disj_cv : rdisj (v_begin (u_cstk g)) (v_bytes (u_cstk g)) (v_begin (u_vstk g)) (v_bytes (u_vstk g)).
  Proof. destruct O as [_ [O2 _]]. unfold owned in O2. inversion O2 as [|x l F _]; subst. inversion F; subst. exact H1. Qed.
  Lemma disj_cc : forall c, In c (z_chunks z) -> rdisj (v_begin (u_cstk g)) (v_bytes (u_cstk g)) (fst c) (CHUNK_HDR + snd c).
  Proof.
    intros c Hc. destruct O as [_ [O2 _]]. unfold owned in O2. inversion O2 as [|x l F _]; subst.
    pose proof (proj1 (Forall_forall _ _) F (chunk_block c) ltac:(right; apply in_map; exact Hc)) as R. exact R.
  Qed.
  Lemma disj_vc : forall c, In c (z_chunks z) -> rdisj (v_begin (u_vstk g)) (v_bytes (u_vstk g)) (fst c) (CHUNK_HDR + snd c).
  Proof.
    intros c Hc. destruct O as [_ [O2 _]]. unfold owned in O2. inversion O2 as [|x l F P2]; subst. inversion P2 as [|x' l' F' _]; subst.
    exact (proj1 (Forall_forall _ _) F' (chunk_block c) ltac:(apply in_map; exact Hc)).
  Qed.
  Lemma disj_chunks : forall c c', In c (z_chunks z) -> In c' (z_chunks z) -> c = c' \/ chunk_disj c c'.
  Proof.
    intros c c' Hc Hc'. destruct pf as (_ & _ & _ & _ & _ & _ & _ & _ & ZV). destruct ZV as (_ & _ & _ & _ & _ & _ & PW).
    destruct (ForallOrdPairs_In PW c c' Hc Hc') as [E|[R|R]]; [left; exact E| right; exact R| right].
    unfold chunk_disj, rdisj in *. lia.
  Qed.

  Lemma top_level : forall lD, last_opt ls = Some lD -> exists ls0, ls = ls0 ++ [lD] /\ removelast ls = ls0 /\ In lD ls.
  Proof.
    intros lD H. pose proof (last_opt_spec ls) as S. rewrite H in S. destruct S as [ls0 E]. exists ls0.
    split; [exact E|]. split; [rewrite E; apply removelast_snoc|]. rewrite E. apply in_app_iff. right; left; reflexivity.
  Qed.
  Lemma level_array : forall l, In l ls -> level_valid l /\ in_alloc z (lv_P l) (lv_bytes l) /\
    lv_P l <= lv_slot l /\ lv_slot l + OBJ_SIZE <= lv_P l + lv_bytes l /\ lv_slot l + lv_unfilled l = lv_P l + lv_bytes l /\
    exists c, In c (z_chunks z) /\ in_chunk c (lv_P l) (lv_bytes l).
  Proof.
    intros l Hl. destruct pf as (_ & _ & _ & _ & _ & _ & LV & [LA1 _] & ZV).
    pose proof (proj1 (Forall_forall _ _) LV l Hl) as V. pose proof (LA1 l Hl) as A.
    pose proof (level_geom l V) as (G1 & G2 & G3 & G4 & _). split; [exact V|]. split; [exact A|]. split; [exact G1|]. split; [exact G2|].
    split; [exact G4|]. exact (in_alloc_chunk z _ _ ZV A).
  Qed.
  Lemma head_chunk : exists h r, z_chunks z = h :: r /\ chunk_lo h <= z_ptr z /\ z_ptr z + z_free z = chunk_hi h /\ 0 <= z_free z.
  Proof.
    destruct pf as (_ & _ & _ & _ & _ & _ & _ & _ & ZV). destruct ZV as (NE & _ & _ & V4 & V5 & V6 & _).
    destruct (z_chunks z) as [|h r]; [contradiction|]. exists h, r. cbn in *. repeat split; auto.
  Qed.

  Ltac win_cases SO := destruct SO as [(KD & I1 & I2 & I3)|[(KD & I1 & I2 & I3)|[(KD & lD & HlD & I2 & I3)|(KD & I2 & I3)]]].

  Lemma safe_cstk : forall a, v_begin (u_cstk g) <= a < v_end (u_cstk g) - 8 -> safe a.
  Proof.
    intros a Ha w Hw SO Hin. unfold in_iv, w_iv in Hin. cbn [fst snd] in Hin.
    destruct pf as (VC & EC & SC & VV & EV & SV & _ & _ & _).
    destruct VC as (VC1 & VC2 & _). destruct VV as (VV1 & VV2 & _).
    unfold v_end, v_capend, v_bytes in *.
    unfold sub_ok in SO. cbv zeta in SO. win_cases SO.
    - unfold v_end, v_capend in *. lia.
    - unfold v_end, v_capend in *. pose proof disj_cv as D. unfold rdisj, v_bytes in D. nia.
    - destruct (top_level lD HlD) as (ls0 & E & _ & HinD). destruct (level_array lD HinD) as (V & A & G1 & G2 & G4 & c & Hc & IC).
      pose proof (disj_cc c Hc) as D. unfold in_chunk, chunk_lo, chunk_hi, CHUNK_HDR, rdisj, v_bytes in *.
      assert (lv_slot lD <= w_lo w) by (destruct (md =? CM_CONS); unfold OBJ_SIZE in *; lia). nia.
    - destruct head_chunk as (h & r & E & H1 & H2 & H3). rewrite E in I3. cbn [hd] in I3.
      pose proof (disj_cc h ltac:(rewrite E; left; reflexivity)) as D. unfold chunk_lo, chunk_hi, CHUNK_HDR, rdisj, v_bytes in *. nia.
  Qed.

  Lemma safe_vstk : forall a, v_begin (u_vstk g) <= a < v_end (u_vstk g) - 8 -> safe a.
  Proof.
    intros a Ha w Hw SO Hin. unfold in_iv, w_iv in Hin. cbn [fst snd] in Hin.
    destruct pf as (VC & EC & SC & VV & EV & SV & _ & _ & _).
    destruct VC as (VC1 & VC2 & _). destruct VV as (VV1 & VV2 & _).
    unfold v_end, v_capend, v_bytes in *.
    unfold sub_ok in SO. cbv zeta in SO. win_cases SO.
    - unfold v_end, v_capend in *. pose proof disj_cv as D. unfold rdisj, v_bytes in D. nia.
    - unfold v_end, v_capend in *. lia.
    - destruct (top_level lD HlD) as (ls0 & E & _ & HinD). destruct (level_array lD HinD) as (V & A & G1 & G2 & G4 & c & Hc & IC).
      pose proof (disj_vc c Hc) as D. unfold in_chunk, chunk_lo, chunk_hi, CHUNK_HDR, rdisj, v_bytes in *.
      assert (lv_slot lD <= w_lo w) by (destruct (md =? CM_CONS); unfold OBJ_SIZE in *; lia). nia.
    - destruct head_chunk as (h & r & E & H1 & H2 & H3). rewrite E in I3. cbn [hd] in I3.
      pose proof (disj_vc h ltac:(rewrite E; left; reflexivity)) as D. unfold chunk_lo, chunk_hi, CHUNK_HDR, rdisj, v_bytes in *. nia.
  Qed.

  Lemma safe_hdr : forall c a, In c (z_chunks z) -> fst c <= a < fst c + CHUNK_HDR -> safe a.
  Proof.
    intros c a Hc Ha w Hw SO Hin. unfold in_iv, w_iv in Hin. cbn [fst snd] in Hin.
    destruct pf as (VC & EC & SC & VV & EV & SV & _ & _ & ZV).
    pose proof ZV as ZV'. destruct ZV' as (_ & _ & V3 & _). destruct (V3 c Hc) as (_ & _ & SZ).
    unfold sub_ok in SO. cbv zeta in SO. win_cases SO.
    - pose proof (disj_cc c Hc) as D. unfold v_end, v_capend, v_bytes, rdisj, CHUNK_HDR, CHUNK_SIZE0 in *. nia.
    - pose proof (disj_vc c Hc) as D. unfold v_end, v_capend, v_bytes, rdisj, CHUNK_HDR, CHUNK_SIZE0 in *. nia.
    - destruct (top_level lD HlD) as (ls0 & E & _ & HinD). destruct (level_array lD HinD) as (V & A & G1 & G2 & G4 & c' & Hc' & IC).
      assert (lv_slot lD <= w_lo w) by (destruct (md =? CM_CONS); unfold OBJ_SIZE in *; lia).
      destruct (disj_chunks c c' Hc Hc') as [<-|D]; unfold in_chunk, chunk_lo, chunk_hi, chunk_disj, rdisj, CHUNK_HDR, CHUNK_SIZE0 in *; lia.
    - destruct head_chunk as (h & r & E & H1 & H2 & H3). rewrite E in I3. cbn [hd] in I3.
      assert (Hh : In h (z_chunks z)) by (rewrite E; left; reflexivity).
      destruct (V3 h Hh) as (_ & _ & SZh).
      destruct (disj_chunks c h Hc Hh) as [<-|D]; unfold chunk_lo, chunk_hi, chunk_disj, rdisj, CHUNK_HDR, CHUNK_SIZE0 in *; lia.
  Qed.

  Lemma safe_alloc : forall lo n a, 0 <= n -> in_alloc z lo n -> (forall l, In l ls -> rdisj lo n (lv_slot l) (lv_unfilled l)) ->
    lo <= a < lo + n -> safe a.
  Proof.
    intros lo n a Hn A U Ha w Hw SO Hin. unfold in_iv, w_iv in Hin. cbn [fst snd] in Hin.
    destruct pf as (VC & EC & SC & VV & EV & SV & _ & _ & ZV).
    destruct (in_alloc_chunk z lo n ZV A) as (c & Hc & IC).
    unfold sub_ok in SO. cbv zeta in SO. win_cases SO.
    - pose proof (disj_cc c Hc) as D. unfold in_chunk, chunk_lo, chunk_hi, v_end, v_capend, v_bytes, rdisj, CHUNK_HDR in *. nia.
    - pose proof (disj_vc c Hc) as D. unfold in_chunk, chunk_lo, chunk_hi, v_end, v_capend, v_bytes, rdisj, CHUNK_HDR in *. nia.
    - destruct (top_level lD HlD) as (ls0 & E & _ & HinD). pose proof (U lD HinD) as D.
      assert (lv_slot lD <= w_lo w) by (destruct (md =? CM_CONS); unfold OBJ_SIZE in *; lia). unfold rdisj in D. lia.
    - pose proof (in_alloc_fresh_disj z lo n (w_lo w) (w_len w) ZV Hn A I2 I3) as D. unfold rdisj in D. lia.
  Qed.

  Lemma safe_cont : forall l a, In l (removelast ls) -> lv_slot l <= a < lv_slot l + OBJ_SIZE -> safe a.
  Proof.
    intros l a Hl Ha w Hw SO Hin. unfold in_iv, w_iv in Hin. cbn [fst snd] in Hin.
    destruct pf as (VC & EC & SC & VV & EV & SV & LV & [LA1 LA2] & ZV).
    assert (Hl' : In l ls).
    { destruct (last_opt ls) as [lD|] eqn:HL.
      - destruct (top_level lD HL) as (ls0 & E & R & _). rewrite R in Hl. rewrite E. apply in_app_iff. left; exact Hl.
      - pose proof (last_opt_spec ls) as S. rewrite HL in S. rewrite S in Hl. cbn in Hl. destruct Hl. }
    destruct (level_array l Hl') as (V & A & G1 & G2 & G4 & c & Hc & IC).
    unfold sub_ok in SO. cbv zeta in SO. win_cases SO.
    - pose proof (disj_cc c Hc) as D. unfold in_chunk, chunk_lo, chunk_hi, v_end, v_capend, v_bytes, rdisj, CHUNK_HDR in *. nia.
    - pose proof (disj_vc c Hc) as D. unfold in_chunk, chunk_lo, chunk_hi, v_end, v_capend, v_bytes, rdisj, CHUNK_HDR in *. nia.
    - destruct (top_level lD HlD) as (ls0 & E & R & HinD). rewrite R in Hl.
      destruct (level_array lD HinD) as (VD & AD & D1 & D2 & D4 & _).
      rewrite E in LA2. destruct (ForallOrdPairs_app_inv _ _ _ _ LA2) as [_ F].
      pose proof (proj1 (Forall_forall _ _) F l Hl) as DJ. unfold level_disj, rdisj in DJ.
      assert (lv_slot lD <= w_lo w) by (destruct (md =? CM_CONS); unfold OBJ_SIZE in *; lia). lia.
    - pose proof (in_alloc_fresh_disj z (lv_P l) (lv_bytes l) (w_lo w) (w_len w) ZV ltac:(lia) A I2 I3) as D. unfold rdisj in D. lia.
  Qed.

  Lemma safe_slot : forall lT a, md = CM_CONS -> last_opt ls = Some lT -> lv_slot lT <= a < lv_slot lT + OBJ_SIZE -> safe a.
  Proof.
    intros lT a MD HL Ha w Hw SO Hin. unfold in_iv, w_iv in Hin. cbn [fst snd] in Hin.
    destruct pf as (VC & EC & SC & VV & EV & SV & LV & LA & ZV).
    destruct (top_level lT HL) as (ls0 & E & R & HinD). destruct (level_array lT HinD) as (V & A & G1 & G2 & G4 & c & Hc & IC).
    unfold sub_ok in SO. cbv zeta in SO. win_cases SO.
    - pose proof (disj_cc c Hc) as D. unfold in_chunk, chunk_lo, chunk_hi, v_end, v_capend, v_bytes, rdisj, CHUNK_HDR in *. nia.
    - pose proof (disj_vc c Hc) as D. unfold in_chunk, chunk_lo, chunk_hi, v_end, v_capend, v_bytes, rdisj, CHUNK_HDR in *. nia.
    - rewrite HL in HlD. injection HlD as <-. rewrite MD in I2. cbn in I2. lia.
    - pose proof (in_alloc_fresh_disj z (lv_P lT) (lv_bytes lT) (w_lo w) (w_len w) ZV ltac:(lia) A I2 I3) as D. unfold rdisj in D. lia.
  Qed.

  Lemma agree_range : forall ob lo n, In ob (owned g) -> fst ob <= lo -> lo + n <= fst ob + snd ob ->
    (forall a, lo <= a < lo + n -> safe a) -> agree_on bm bm' lo n.
  Proof.
    intros ob lo n Hob H1 H2 SF x Hx. apply (agree_byte x ob Hob); [unfold in_iv; lia| apply SF; lia].
  Qed.

  Lemma agree_alloc : forall lo n, 0 <= n -> in_alloc z lo n ->
    (forall l, In l ls -> rdisj lo n (lv_slot l) (lv_unfilled l)) -> agree_on bm bm' lo n.
  Proof.
    intros lo n Hn A U. destruct pf as (_ & _ & _ & _ & _ & _ & _ & _ & ZV).
    destruct (in_alloc_chunk z lo n ZV A) as (c & Hc & IC).
    apply (agree_range (chunk_block c)); [apply owned_chunk; exact Hc| | |].
    - unfold chunk_block, in_chunk, chunk_lo, CHUNK_HDR in *. cbn [fst]. lia.
    - unfold chunk_block, in_chunk, chunk_lo, chunk_hi, CHUNK_HDR in *. cbn [fst snd]. lia.
    - intros a Ha. eapply safe_alloc; eauto.
  Qed.

  Lemma snoc_decomp : forall {A} (y : A) l, exists l0 w, y :: l = l0 ++ [w].
  Proof.
    intros A y l. destruct (exists_last (l:=y :: l) ltac:(discriminate)) as [l0 [w E]]. exists l0, w. exact E.
  Qed.
  Lemma removelast_cons2 : forall {A} (x y : A) l, removelast (x :: y :: l) = x :: removelast (y :: l).
  Proof.
    intros A x y l. destruct (snoc_decomp y l) as (l0 & w & E). rewrite E.
    change (x :: l0 ++ [w]) with ((x :: l0) ++ [w]). rewrite !removelast_snoc. reflexivity.
  Qed.
  Lemma removelast_one : forall {A} (x : A), removelast [x] = [].
  Proof. reflexivity. Qed.
  Lemma removelast_length : forall {A} (l : list A), l <> [] -> length (removelast l) = (length l - 1)%nat.
  Proof.
    intros A l H. destruct (exists_last H) as [l0 [w E]]. rewrite E, removelast_snoc, length_app. cbn. lia.
  Qed.
  Lemma tl_containers : forall l ls' , containers (lv_slot l) ls' = map lv_slot (removelast (l :: ls')).
  Proof.
    intros l ls'. revert l. induction ls' as [|l2 ls'' IH]; intros l.
    - rewrite removelast_one. reflexivity.
    - rewrite removelast_cons2. cbn [containers map]. rewrite IH. reflexivity.
  Qed.

  Lemma mem_frame : mem_ok md bm g -> mem_ok md bm' g.
  Proof.
    intros (M1 & M2 & M3 & M4 & M5 & M6).
    destruct pf as (VC & EC & SC & VV & EV & SV & LV & LA & ZV).
    pose proof VC as (VC1 & VC2 & VC3 & VC4). pose proof VV as (VV1 & VV2 & VV3 & VV4).
    assert (DLEN : u_D g = Z.of_nat (length ls)) by reflexivity.

    assert (AGC : agree_on bm bm' (v_begin (u_cstk g)) (8 * Z.of_nat (length (removelast ls)))).
    { destruct ls as [|l1 ls1] eqn:EL.
      - intros x Hx. cbn in Hx. lia.
      - rewrite (removelast_length (l1 :: ls1)) by discriminate.
        apply (agree_range (cstk_block g) _ _ owned_cstk).
        + cbn [fst cstk_block]. lia.
        + cbn [fst snd cstk_block]. unfold v_bytes. rewrite EC. rewrite ?EL in DLEN. cbn [length] in DLEN |- *. nia.
        + intros a Ha. apply safe_cstk. unfold v_end. rewrite EC, SC, DLEN, ?EL. cbn [length] in Ha |- *. lia. }
    assert (AGV : ls <> [] -> agree_on bm bm' (v_begin (u_vstk g)) (8 + 8 * Z.of_nat (length (removelast ls)))).
    { intros NE. rewrite (removelast_length _ NE).
      assert (1 <= Z.of_nat (length ls)) by (destruct ls; [contradiction| cbn [length]; lia]).
      apply (agree_range (vstk_block g) _ _ owned_vstk).
      + cbn [fst vstk_block]. lia.
      + cbn [fst snd vstk_block]. unfold v_bytes. rewrite EV. clear - VV2 SV DLEN H. nia.
      + intros a Ha. apply safe_vstk. unfold v_end. rewrite EV, SV, DLEN. clear - Ha H. lia. }
    split; [| split; [| split; [| split; [| split]]]].
    - eapply cstk_at_frame; [exact AGC| exact M1].
    - intros NE. eapply u64_at_frame; [| exact (M2 NE)]. eapply agree_on_sub; [exact (AGV NE)| lia| lia].
    - destruct ls as [|l1 ls1] eqn:EL; [exact I|].
      eapply vstk_at_frame; [| exact M3]. eapply agree_on_sub; [apply AGV; discriminate| lia| lia].
    - eapply chunks_at_frame; [| exact M4]. intros c Hc.
      destruct ZV as (_ & _ & V3 & _). destruct (V3 c Hc) as (_ & _ & SZ).
      apply (agree_range (chunk_block c) _ _ (owned_chunk c Hc)); [cbn [fst chunk_block]; lia| cbn [fst snd chunk_block]; unfold CHUNK_HDR, CHUNK_SIZE0 in *; lia|].
      intros a Ha. eapply safe_hdr; [exact Hc| unfold CHUNK_HDR; lia].
    - eapply conts_at_frame; [| exact M5]. intros c Hc.
      destruct ls as [|l1 ls1] eqn:EL; [cbn in Hc; destruct Hc|].
      cbn [containers tl] in Hc. rewrite tl_containers in Hc. apply in_map_iff in Hc as (l & <- & Hl).
      rewrite <- EL in Hl.
      assert (Hl' : In l ls).
      { destruct (last_opt ls) as [lD|] eqn:HL.
        - destruct (top_level lD HL) as (ls0 & E & R & _). rewrite R in Hl. rewrite E. apply in_app_iff. left; exact Hl.
        - pose proof (last_opt_spec ls) as S0. rewrite HL in S0. rewrite S0 in EL. discriminate. }
      destruct (level_array l Hl') as (V & A & G1 & G2 & G4 & c & Hc & IC).
      apply (agree_range (chunk_block c) _ _ (owned_chunk c Hc)).
      + unfold chunk_block, in_chunk, chunk_lo, CHUNK_HDR in *. cbn [fst]. lia.
      + unfold chunk_block, in_chunk, chunk_lo, chunk_hi, CHUNK_HDR in *. cbn [fst snd]. lia.
      + intros a Ha. eapply safe_cont; [exact Hl| exact Ha].
    - intros l Hl i Hi. destruct (M6 l Hl i Hi) as (o & T & CS & BS). exists o. split; [| split; [exact CS| exact BS]].
      eapply tree_at_agree; [| | exact T].
      + intros c Hc. destruct (CS c Hc) as [A U]. apply agree_alloc; [unfold OBJ_SIZE; lia| exact A| exact U].
      + intros b Hb. pose proof (proj1 (Forall_forall _ _) BS b Hb) as (N & A & U). apply agree_alloc; assumption.
  Qed.

  Lemma kids_frame_ops : mem_ok md bm g ->
    forall l i o, In l ls -> Z.of_nat i < lv_k l -> tree_at bm z (Acct.kid_addr l i) o -> tree_at bm' z (Acct.kid_addr l i) o.
  Proof.
    intros (_ & _ & _ & _ & _ & M6) l i o Hl Hi T. unfold Acct.kid_addr in *.
    destruct (M6 l Hl (Z.of_nat i) ltac:(lia)) as (o' & T' & CS & BS).
    pose proof (Acct.tree_at_unique _ _ _ _ _ T T') as ->.
    eapply tree_at_agree; [| | exact T'].
    + intros c Hc. destruct (CS c Hc) as [A0 U]. apply agree_alloc; [unfold OBJ_SIZE; lia| exact A0| exact U].
    + intros b Hb. pose proof (proj1 (Forall_forall _ _) BS b Hb) as (N & A0 & U). apply agree_alloc; assumption.
  Qed.

  Lemma kids_pk_frame_ops : mem_ok md bm g -> forall S, Pot.Pot.kids_pk bm z ls S -> Pot.Pot.kids_pk bm' z ls S.
  Proof. intros M S K. exact (Pot.Pot.kids_pk_frame bm bm' z z ls S (kids_frame_ops M) K). Qed.

  Lemma cons_frame : forall u, mem_ok md bm g -> cons_ok md ws u bm g -> cons_ok md ws u bm' g.
  Proof.
    intros u MO C MD. destruct (C MD) as (o & TW & K & HD & RT & CS & BS & DP & PT). cbv zeta.
    assert (AB : forall b, In b (obj_bodies o) -> agree_on bm bm' (fst b) (snd b)).
    { intros b Hb. pose proof (proj1 (Forall_forall _ _) BS b Hb) as (N & A & U). apply agree_alloc; assumption. }
    assert (AC : forall c, In c (tl (obj_cells (u_cur_slot g) o)) -> agree_on bm bm' c OBJ_SIZE).
    { intros c Hc. destruct (CS c Hc) as [A U]. apply agree_alloc; [unfold OBJ_SIZE; lia| exact A| exact U]. }
    exists o. split; [exact (tree_wf_agree _ _ _ _ AB TW)|]. split; [exact (kids_at_frame _ _ _ _ AC K)|].
    split; [| split; [exact RT| split; [exact CS| split; [exact BS| split; [exact DP|
      destruct PT as (S & KP & PA); exists S; split; [exact (kids_pk_frame_ops MO S KP)| exact PA]]]]]].
    intros NE. pose proof (HD NE) as H.
    destruct (last_opt ls) as [lD|] eqn:HL.
    2:{ pose proof (last_opt_spec ls) as S0. rewrite HL in S0. contradiction. }
    destruct (top_level lD HL) as (ls0 & E & R & HinD).
    assert (SL : u_cur_slot g = lv_slot lD) by (unfold u_cur_slot; rewrite E; apply cur_slot_snoc).
    assert (AH : agree_on bm bm' (u_cur_slot g) OBJ_SIZE).
    { destruct (level_array lD HinD) as (V & A & G1 & G2 & G4 & c' & Hc' & IC).
      apply (agree_range (chunk_block c') _ _ (owned_chunk c' Hc')).
      - rewrite SL. unfold chunk_block, in_chunk, chunk_lo, CHUNK_HDR in *. cbn [fst]. lia.
      - rewrite SL. unfold chunk_block, in_chunk, chunk_lo, chunk_hi, CHUNK_HDR in *. cbn [fst snd]. lia.
      - intros a Ha. eapply safe_slot; [exact MD| exact HL| rewrite <- SL; exact Ha]. }
    assert (OA : obj_at bm' (u_cur_slot g) o).
    { apply (obj_at_frame bm bm'); [| exact (proj2 (obj_at_split _ _ _) (conj H K))].
      intros c Hc. rewrite obj_cells_hd in Hc. destruct Hc as [<-|Hc]; [exact AH| exact (AC c Hc)]. }
    exact (proj1 (proj1 (obj_at_split _ _ _) OA)).
  Qed.

  Lemma acct_frame_ops : mem_ok md bm g -> acct_ex bm g -> acct_ex bm' g.
  Proof. intros M (X & A). exists X. eapply Acct.acct_frame; [| exact A]. exact (kids_frame_ops M). Qed.
  Lemma acct_pot_frame : mem_ok md bm g -> acct_pot md ws bm g -> acct_pot md ws bm' g.
  Proof.
    intros M [AX PT]. split; [exact (acct_frame_ops M AX)|]. intros MD. destruct (PT MD) as (S & KP & PA).
    exists S. split; [exact (kids_pk_frame_ops M S KP)| exact PA].
  Qed.
End Frame.

Lemma cw_unp_frame : forall md ca LB ws m m', cw_unp_holds md ca LB ws m ->
  (forall a, 0 <= a < two64 -> in_user LB a -> ~ in_ws (heap_ws ws) a -> m (Z_to_bv 64 a) = m' (Z_to_bv 64 a)) ->
  cw_unp_holds md ca LB ws m'.
Proof.
  intros md ca LB ws m m' H FR. unfold cw_unp_holds in *.
  destruct (md =? CM_NONE); [exact H|]. destruct ((md =? CM_UNP) || (md =? CM_CONS)); [| exact (cw_frame XW md ca LB ws m m' H FR)].
  destruct (decode_uc ca) as [u|]; [|exact H].
  destruct H as (g & L & P & O & Wk & M & CS & AX & SE). exists g. split; [exact L|]. split; [exact P|]. split; [exact O|]. split; [exact Wk|].
  split; [exact (mem_frame md g LB ws m m' P O Wk FR M)|]. split; [exact (cons_frame md g LB ws m m' P O Wk FR u M CS)|].
  split; [exact (acct_pot_frame md g LB ws m m' P O Wk FR M AX)| exact SE].
Qed.

Definition unp_cw : client_world := CW (cw_unp_holds) (cw_unp_frame) (cw_unp_grow) (cw_unp_free).

End WithSegs.
End UO.
