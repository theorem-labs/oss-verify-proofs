(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.U Require Import Z_ikit Z_infl_defs Z_ukit Z_infl_pure Z_infl_pure2 Z_infl_c_pure Z_infl_c_tab Zg_infl_iface Zg_inffast_defs Zg_inffast_exit Zg_inffast_copy.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.P Require Import Zg_inffast_model.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZProg ZIface InflateState InflateArms Inflate InflateFast InffastModel InffastCtx InffastSafe InffastMem.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.


Definition ff_place (x : ffx) (f : ffs) : ffs :=
  if x_wnext x =? 0 then
    let f := fset_from f (FWin (x_wsize x - f_op f)) in
    if f_op f <? f_len f then
      let f := fset_len f (wrap32 (f_len f - f_op f)) in
      let f := copy_op x f in
      fset_from f (FOut (f_out f - f_dist f))
    else f
  else if x_wnext x <? f_op f then
    let f := fset_from f (FWin (x_wsize x + x_wnext x - f_op f)) in
    let f := fset_op f (wrap32 (f_op f - x_wnext x)) in
    if f_op f <? f_len f then
      let f := fset_len f (wrap32 (f_len f - f_op f)) in
      let f := copy_op x f in
      let f := fset_from f (FWin 0) in
      if x_wnext x <? f_len f then
        let f := fset_op f (x_wnext x) in
        let f := fset_len f (wrap32 (f_len f - f_op f)) in
        let f := copy_op x f in
        fset_from f (FOut (f_out f - f_dist f))
      else f
    else f
  else
    let f := fset_from f (FWin (x_wnext x - f_op f)) in
    if f_op f <? f_len f then
      let f := fset_len f (wrap32 (f_len f - f_op f)) in
      let f := copy_op x f in
      fset_from f (FOut (f_out f - f_dist f))
    else f.

Definition ff_winres (x : ffx) (f : ffs) : fstep :=
  let op := wrap32 (f_dist f - wrap32 (f_out f - x_beg x)) in
  if (x_whave x <? op) && negb (x_sane x =? 0) then
    FBreak (fset_op f op) BAD (Some MSG_ff_invalid_distance_too_far_back)
  else
    let f := fset_op f op in
    let f := ff_place x f in
    let f := copy_while3 x f in
    FCont (copy_tail x f).

Definition pl_out (g : ffs) : ffs := fset_from g (FOut (f_out g - f_dist g)).
Definition pl_leg1 (x : ffx) (f1 : ffs) (k : Z) : ffs := copy_op x (fset_len (fset_from f1 (FWin k)) (f_len f1 - f_op f1)).
Definition pl_leg2a (x : ffx) (f1 : ffs) : ffs :=
  copy_op x (fset_len (fset_op (fset_from f1 (FWin (x_wsize x + x_wnext x - f_op f1))) (f_op f1 - x_wnext x)) (f_len f1 - (f_op f1 - x_wnext x))).
Definition pl_leg2b (x : ffx) (g : ffs) : ffs := copy_op x (fset_len (fset_op (fset_from g (FWin 0)) (x_wnext x)) (f_len g - x_wnext x)).

Lemma ff_place_eq : forall x f1, 0 <= x_wnext x -> 1 <= f_op f1 < 2^31 -> 0 <= f_len f1 < 2^31 ->
  (x_wnext x < f_op f1 -> f_op f1 <= x_wsize x + x_wnext x) ->
  ff_place x f1 =
    if x_wnext x =? 0 then
      if f_op f1 <? f_len f1 then pl_out (pl_leg1 x f1 (x_wsize x - f_op f1)) else fset_from f1 (FWin (x_wsize x - f_op f1))
    else if x_wnext x <? f_op f1 then
      if f_op f1 - x_wnext x <? f_len f1 then
        if x_wnext x <? f_len f1 - (f_op f1 - x_wnext x) then pl_out (pl_leg2b x (pl_leg2a x f1)) else fset_from (pl_leg2a x f1) (FWin 0)
      else fset_op (fset_from f1 (FWin (x_wsize x + x_wnext x - f_op f1))) (f_op f1 - x_wnext x)
    else if f_op f1 <? f_len f1 then pl_out (pl_leg1 x f1 (x_wnext x - f_op f1)) else fset_from f1 (FWin (x_wnext x - f_op f1)).
Proof.
  intros x f1 Hw Hop Hlen Hcase. unfold ff_place, pl_out, pl_leg1, pl_leg2a, pl_leg2b.
  cbn [f_op f_len f_out f_dist fset_from fset_len fset_op].
  destruct (Z.eqb_spec (x_wnext x) 0) as [E0|E0].
  - destruct (Z.ltb_spec (f_op f1) (f_len f1)); [|reflexivity]. rewrite wrap32_id by lia. reflexivity.
  - destruct (Z.ltb_spec (x_wnext x) (f_op f1)) as [C2|C3].
    + rewrite (wrap32_id (f_op f1 - x_wnext x)) by lia.
      destruct (Z.ltb_spec (f_op f1 - x_wnext x) (f_len f1)) as [C|C]; [|reflexivity].
      rewrite (wrap32_id (f_len f1 - (f_op f1 - x_wnext x))) by lia.
      rewrite copy_op_len by (cbn; lia). cbn [f_len fset_len fset_op fset_from].
      destruct (Z.ltb_spec (x_wnext x) (f_len f1 - (f_op f1 - x_wnext x))); [|reflexivity].
      rewrite wrap32_id by lia. reflexivity.
    + destruct (Z.ltb_spec (f_op f1) (f_len f1)); [|reflexivity]. rewrite wrap32_id by lia. reflexivity.
Qed.

Lemma pl_leg1_shape : forall x f1 k, 1 <= f_op f1 < 2^32 ->
  let g := pl_leg1 x f1 k in
  f_in g = f_in f1 /\ f_hold g = f_hold f1 /\ f_bits g = f_bits f1 /\ f_len g = f_len f1 - f_op f1 /\ f_dist g = f_dist f1
  /\ f_out g = f_out f1 + f_op f1 /\ f_ob g = cblit (x_window x) (FWin k) (f_ob f1) (f_out f1) (Z.to_nat (f_op f1)).
Proof.
  intros x f1 k H. unfold pl_leg1.
  destruct (copy_op_shape x (fset_len (fset_from f1 (FWin k)) (f_len f1 - f_op f1)) ltac:(cbn; lia)) as (A & B & C & D & E & F & G & _ & I).
  cbn [f_in f_hold f_bits f_len f_dist f_op f_out f_from f_ob fset_len fset_from] in *. repeat split; assumption.
Qed.
Lemma pl_leg2a_shape : forall x f1, 0 <= x_wnext x -> x_wnext x < f_op f1 -> f_op f1 < 2^32 ->
  let g := pl_leg2a x f1 in
  f_in g = f_in f1 /\ f_hold g = f_hold f1 /\ f_bits g = f_bits f1 /\ f_len g = f_len f1 - (f_op f1 - x_wnext x) /\ f_dist g = f_dist f1
  /\ f_out g = f_out f1 + (f_op f1 - x_wnext x)
  /\ f_ob g = cblit (x_window x) (FWin (x_wsize x + x_wnext x - f_op f1)) (f_ob f1) (f_out f1) (Z.to_nat (f_op f1 - x_wnext x)).
Proof.
  intros x f1 H0 H H32. unfold pl_leg2a.
  destruct (copy_op_shape x (fset_len (fset_op (fset_from f1 (FWin (x_wsize x + x_wnext x - f_op f1))) (f_op f1 - x_wnext x)) (f_len f1 - (f_op f1 - x_wnext x))) ltac:(cbn; lia))
    as (A & B & C & D & E & F & G & _ & I).
  cbn [f_in f_hold f_bits f_len f_dist f_op f_out f_from f_ob fset_len fset_from fset_op] in *. repeat split; assumption.
Qed.
Lemma pl_leg2b_shape : forall x g, 1 <= x_wnext x < 2^32 ->
  let h := pl_leg2b x g in
  f_in h = f_in g /\ f_hold h = f_hold g /\ f_bits h = f_bits g /\ f_len h = f_len g - x_wnext x /\ f_dist h = f_dist g
  /\ f_out h = f_out g + x_wnext x /\ f_ob h = cblit (x_window x) (FWin 0) (f_ob g) (f_out g) (Z.to_nat (x_wnext x)).
Proof.
  intros x g H. unfold pl_leg2b.
  destruct (copy_op_shape x (fset_len (fset_op (fset_from g (FWin 0)) (x_wnext x)) (f_len g - x_wnext x)) ltac:(cbn; lia)) as (A & B & C & D & E & F & G & _ & I).
  cbn [f_in f_hold f_bits f_len f_dist f_op f_out f_from f_ob fset_len fset_from fset_op] in *. repeat split; assumption.
Qed.

Section TP.
Variables (X : ictx) (s : inflate_state) (c : icall) (r : iregs) (sv : ffsave).

Definition FFMs (me : mem) : Prop :=
  rw_cells usegs me (ff_sp X) (ff_frame_cells X s c r sv)
  /\ isA me (ix_L X) s /\ isT me (ix_L X) s /\ izs me (ix_L X) c
  /\ icodes me (ix_L X) s /\ iwin me (ix_L X) s /\ iin me X /\ iarrs s /\ ilay_ok (ix_L X) s.

Lemma FFM_split : forall f m, FFM X s c r sv f m -> FFMs m /\ CPM X c (f_ob f) (f_out f) m.
Proof.
  intros f m (A & B & C & D & E & F & G & H & I & J & K). split; [| split; assumption].
  split; [exact A|]. split; [exact B|]. split; [exact C|]. split; [exact D|]. split; [exact E|]. split; [exact F|].
  split; [exact G|]. split; [exact J| exact K].
Qed.

Lemma FFMs_transport : forall me m', ix_ok X -> (is_window_blk s <> None -> ix_hasw X = true) ->
  FFMs me -> munch (ffW X) me m' -> wmono usegs me m' -> FFMs m'.
Proof.
  intros me m' XO Whas (FR & GA & GT & ZS & Gc & Gwin & IN & ARRS & LAY) MUf WMf. ix_open XO. unfold ffW in MUf.
  unfold ff_frame_cells in FR. unfold iin in IN. unfold ff_sp in *.
  pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
  itr_groups MUf WMf.
  eapply rw_cells_transport in FR; [| exact MUf| exact WMf| cbn [disjoint_from]; cells_cbv; slia].
  eapply u8ro_transport in IN; [| exact MUf| cbn [disjoint_from]; rewrite av8_length; slia].
  split; [exact FR|]. split; [exact GA|]. split; [exact GT|]. split; [exact ZS|]. split; [exact Gc|]. split; [exact Gwin|].
  split; [exact IN|]. split; [exact ARRS| exact LAY].
Qed.

Lemma tpost_of_w3 : forall g fin hold bits obF outF me mc ms',
  ix_ok X -> (is_window_blk s <> None -> ix_hasw X = true) ->
  w3_post X s c r hold bits fin obF outF mc ms' ->
  FFMs me -> munch (ffW X) me mc -> wmono usegs me mc ->
  f_in g = fin -> f_hold g = hold -> f_bits g = bits -> f_out g = outF -> f_ob g = obF ->
  0 <= bits <= 63 -> 0 <= hold < 2 ^ bits -> ic_next_in c <= fin <= arr_len (ic_input c) ->
  ic_next_out c <= outF <= arr_len (ic_outbuf c) -> arr_len obF = arr_len (ic_outbuf c) ->
  TPOST X s c r sv me (FCont g) ms'.
Proof.
  intros g fin hold bits obF outF me mc ms' XO Whas (x1 & x5 & x6 & x7 & x9 & x13 & x23 & x27 & x29 & m' & -> & MU & WM & MI & CP & OBT) HS MU0 WM0
         E1 E2 E3 E4 E5 Rb Rh Rin Rout Rlen.
  cbn [TPOST]. exists x1, x5, x6, x7, x9, x13, x23, x27, x29, m'.
  split; [unfold FFL; rewrite E1, E2, E3, E4; reflexivity|].
  pose proof (munch_trans _ _ _ _ MU0 MU) as MU1. pose proof (wmono_trans _ _ _ _ WM0 WM) as WM1.
  split; [eapply munch_weaken; [|exact MU1]; unfold sub_fp, ffW, ffWb; cbn [outside]; intros; lia|].
  split; [exact WM1|]. split; [exact MI|].
  destruct (FFMs_transport me m' XO Whas HS MU1 WM1) as (FR & GA & GT & ZS & Gc & Gwin & IN & ARRS & LAY).
  destruct CP as [OUT MI'].
  split.
  - unfold FFM, FFMg. rewrite E4, E5.
    split; [exact FR|]. split; [exact GA|]. split; [exact GT|]. split; [exact ZS|]. split; [exact Gc|]. split; [exact Gwin|].
    split; [exact IN|]. split; [exact OUT|]. split; [exact MI'|]. split; [exact ARRS| exact LAY].
  - unfold FINV. rewrite E1, E2, E3, E4, E5. repeat (split; [lia|]). intros i Hi. apply OBT. exact Hi.
Qed.

Lemma ffm_after_copy : forall g me m', ix_ok X -> (is_window_blk s <> None -> ix_hasw X = true) ->
  FFMs me -> munch (ffW X) me m' -> wmono usegs me m' -> CPM X c (f_ob g) (f_out g) m' -> FFM X s c r sv g m'.
Proof.
  intros g me m' XO Whas HS MU WM [OUT MI].
  destruct (FFMs_transport me m' XO Whas HS MU WM) as (FR & GA & GT & ZS & Gc & Gwin & IN & ARRS & LAY).
  unfold FFM, FFMg.
  split; [exact FR|]. split; [exact GA|]. split; [exact GT|]. split; [exact ZS|]. split; [exact Gc|]. split; [exact Gwin|].
  split; [exact IN|]. split; [exact OUT|]. split; [exact MI|]. split; [exact ARRS| exact LAY].
Qed.
Lemma finv_after_copy : forall f g, FINV X s c f -> f_in g = f_in f -> f_hold g = f_hold f -> f_bits g = f_bits f ->
  f_out f <= f_out g <= arr_len (ic_outbuf c) -> arr_len (f_ob g) = arr_len (f_ob f) -> OBT (f_ob g) (f_out g) -> FINV X s c g.
Proof.
  intros f g (Fb & Fh & Fin & Fout & Fob & Fbytes) E1 E2 E3 Ro Rl OBT. unfold FINV. rewrite E1, E2, E3, Rl.
  repeat (split; [lia|]). exact OBT.
Qed.

Lemma CPS_of : ix_ok X -> ff_typed X s c r -> iarrs s -> CPS X s.
Proof.
  intros XO HT ARRS.
  destruct HT as (Pin & Pout & Rn & Rh & Rnh & Rin31 & Rp & Rl & Rpl & Rout31 & Rout & Rbeg & Bin & Bout & Bwin & Rb & Rhold
               & Rlb & Rdb & CPL & CPD & Rws & Rwh & Rwn & Rsane & Wnone & Wz & Whas).
  destruct ARRS as (_ & _ & _ & AW).
  split; [exact XO|]. split; [exact Whas|]. split; [exact AW|]. split; [exact Bwin|]. lia.
Qed.
End TP.

Ltac fnorm := cbn [f_in f_out f_hold f_bits f_len f_dist f_op f_from f_ob fset_in fset_out fset_hold fset_bits fset_len fset_dist fset_op fset_from fset_ob fdrop].
Tactic Notation "fnorm" "in" hyp(H) := cbn [f_in f_out f_hold f_bits f_len f_dist f_op f_from f_ob fset_in fset_out fset_hold fset_bits fset_len fset_dist fset_op fset_from fset_ob fdrop] in H.
Local Ltac ffreg3 :=
  first [ ffreg
        | f_equal; rewrite ?ffrom_add, ?ffrom_succ; unfold ffrom; cbn [faddr Z.of_nat Pos.to_nat Pos.iter_op Nat.add]; lia
        | try match goal with H : win_addr _ _ = il_Aw _ |- _ => rewrite H end; unfold ffrom; cbn [faddr];
          first [ ffreg | f_equal; rewrite ?zext32_swrap, ?zext32_land, ?wrap32_id by lia; lia ] ].

Ltac tp_open XO HRS HT FI HS :=
  pose proof HRS as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6);
  lazymatch type of HS with FFMs ?X ?s ?c ?r ?sv ?me =>
    pose proof HS as (FR & GA & GT & ZS & Gc & Gwin & IN & ARRS & LAY);
    pose proof (CPS_of X s c r XO HT ARRS) as CP
  end;
  lazymatch type of FI with FINV _ _ _ ?fP =>
    pose proof FI as (Fb & Fh & Fin & Fout & Fob & Fbytes);
    pose proof HT as (Pin & Pout & Rn & Rh & Rnh & Rin31 & Rp & Rl & Rpl & Rout31 & Rout & Rbeg & Bin & Bout & Bwin & Rb & Rhold
                 & Rlb & Rdb & CPL & CPD & Rws & Rwh & Rwn & Rsane & Wnone & Wz & Whas);
    assert (RH64 : 0 <= f_hold fP < 2^64) by (split; [lia|]; eapply Z.lt_le_trans; [exact (proj2 Fh)|]; apply Z.pow_le_mono_r; lia)
  end.


Section WIN.
Variables (X : ictx) (s : inflate_state) (c : icall) (r : iregs) (sv : ffsave).
Local Notation L := (ix_L X).
Local Notation xx := (ffx_of s c r).

Lemma tpost_of_brk : forall f md g me m ms',
  ff_brk_post X s c r sv f (Some (md, g)) m ms' -> FINV X s c f -> munch (ffW X) me m -> wmono usegs me m ->
  TPOST X s c r sv me (FBreak f md g) ms'.
Proof.
  intros f md g me m ms' (y1 & y5 & y6 & y7 & y8 & y9 & y13 & y17 & y18 & y19 & y20 & y23 & y24 & y25 & y26 & y27 & y28 & y29 & y30 & y31 & m' & -> & MU & WM & MI' & HMg) FI MU0 WM0.
  cbn [TPOST]. do 21 eexists. split; [reflexivity|].
  split.
  { eapply munch_trans; [eapply munch_weaken; [|exact MU0] | eapply munch_weaken; [|exact MU]];
      unfold sub_fp, ffW, ffWb; cbn [outside]; intros; lia. }
  split; [eapply wmono_trans; [exact WM0| exact WM]|]. split; [exact MI'|]. split; [exact HMg| exact FI].
Qed.

Lemma ff_w3_tp : forall fP (x1 x5 x6 x7 x9 x13 x23 : word) me m,
  ix_ok X -> ff_restored s c r -> ff_typed X s c r -> FINV X s c fP ->
  FFMs X s c r sv me -> munch (ffW X) me m -> wmono usegs me m -> CPM X c (f_ob fP) (f_out fP) m ->
  srcn s (f_out fP) (f_from fP) (f_len fP) -> 0 <= f_len fP < 2^31 -> f_out fP + f_len fP <= arr_len (ic_outbuf c) ->
  evt usegs (TPOST X s c r sv me (FCont (copy_tail xx (copy_while3 xx fP))))
    (FFL X s c r fP PC_FF_W3E x1 x5 x6 x7 x9 x13 x23 (wz (f_len fP)) (wz (ffrom X (f_from fP))) m).
Proof.
  intros fP x1 x5 x6 x7 x9 x13 x23 me m XO HRS HT FI HS MU0 WM0 HC SR Rlen Rol. tp_open XO HRS HT FI HS.
  destruct (w3_shape xx fP ltac:(lia)) as (E1 & E2 & E3 & E4 & E5). cbn [x_window ffx_of] in E5.
  eapply evt_mono.
  - eapply evt_eq; [| eapply (ff_w3 X s c r (f_from fP) (f_ob fP) (f_out fP) (f_len fP) (f_hold fP) (f_bits fP) (f_in fP) _ _ x1 x5 x6 x7 x9 x13 x23 me m);
      first [ exact CP | exact HC | exact Gwin | exact MU0 | exact WM0 | reflexivity | intros _; exact SR
            | intros i Hi; apply Fbytes; exact Hi | rewrite <- Pin; lia | lia ] ].
    eapply FFL_intro2; fnorm; ffreg3.
  - intros ms' PO. eapply (tpost_of_w3 X s c r sv _ (f_in fP) (f_hold fP) (f_bits fP));
      first [ exact XO | exact Whas | exact PO | exact HS | apply munch_refl | apply wmono_refl | exact E1 | exact E2 | exact E3 | exact E4 | exact E5
            | rewrite cblit_len2; lia | lia ].
Qed.

Lemma ff_w3b_tp : forall fP out0 (x5 x6 x7 x9 x13 x29 : word) me m,
  ix_ok X -> ff_restored s c r -> ff_typed X s c r -> FINV X s c fP ->
  FFMs X s c r sv me -> munch (ffW X) me m -> wmono usegs me m -> CPM X c (f_ob fP) (f_out fP) m ->
  f_from fP = FOut (f_out fP - f_dist fP) -> 1 <= f_dist fP <= f_out fP -> f_dist fP < 2^32 ->
  0 <= f_len fP < 2^31 -> f_out fP + f_len fP <= arr_len (ic_outbuf c) -> 0 <= out0 <= f_out fP ->
  evt usegs (TPOST X s c r sv me (FCont (copy_tail xx (copy_while3 xx fP))))
    (FFL X s c r (fset_out fP out0) 0x22ca4 (wz (il_NO L + f_out fP)) x5 x6 x7 x9 x13 (wz (f_dist fP)) (wz (f_len fP)) x29 m).
Proof.
  intros fP out0 x5 x6 x7 x9 x13 x29 me m XO HRS HT FI HS MU0 WM0 HC Efr Rd Rd32 Rlen Rol Ro0. tp_open XO HRS HT FI HS. ffx_pose HRS HT. ix_open XO.
  assert (SR : srcn s (f_out fP) (f_from fP) (f_len fP)) by (rewrite Efr; cbn; lia).
  destruct (w3_shape xx fP ltac:(lia)) as (E1 & E2 & E3 & E4 & E5). cbn [x_window ffx_of] in E5.
  unfold FFL, ff_sp. fnorm. do 2 zs. zstep. br_cases K.
  -
    do 2 zs.
    eapply evt_mono.
    + eapply evt_eq; [| eapply (ff_w3l X s c r (Z.to_nat (f_len fP)) (f_from fP) (f_ob fP) out0 (f_out fP) (f_len fP) (f_hold fP) (f_bits fP) (f_in fP) _ _ _ _ _ _ me m);
        first [ exact CP | exact HC | exact Gwin | exact MU0 | exact WM0 | reflexivity | exact SR
              | intros i Hi; apply Fbytes; exact Hi | rewrite <- Pin; lia | lia ] ].
      unfold PC_FF_W3L. eapply FFL_intro2; fnorm; rewrite ?Efr; ffreg3.
    + intros ms' PO. eapply (tpost_of_w3 X s c r sv _ (f_in fP) (f_hold fP) (f_bits fP));
        first [ exact XO | exact Whas | exact PO | exact HS | apply munch_refl | apply wmono_refl | exact E1 | exact E2 | exact E3 | exact E4 | exact E5
              | rewrite cblit_len2; lia | lia ].
  -
    zs.
    eapply evt_mono.
    + eapply evt_eq; [| eapply (ff_w3t X s c r (f_from fP) (f_ob fP) out0 (f_out fP) (f_len fP) (f_hold fP) (f_bits fP) (f_in fP) _ _ _ _ _ _ _ _ me m);
        first [ exact CP | exact HC | exact Gwin | exact MU0 | exact WM0 | reflexivity | intros _; exact SR
              | intros i Hi; apply Fbytes; exact Hi | rewrite <- Pin; lia | lia ] ].
      unfold PC_FF_TAIL. eapply FFL_intro2; fnorm; rewrite ?Efr; ffreg3.
    + intros ms' PO. eapply (tpost_of_w3 X s c r sv _ (f_in fP) (f_hold fP) (f_bits fP));
        first [ exact XO | exact Whas | exact PO | exact HS | apply munch_refl | apply wmono_refl | exact E1 | exact E2 | exact E3 | exact E4 | exact E5
              | rewrite cblit_len2; lia | lia ].
Qed.

Lemma ff_w3c_tp : forall fP (x5 x6 x7 x9 x29 : word) me m,
  ix_ok X -> ff_restored s c r -> ff_typed X s c r -> FINV X s c fP ->
  FFMs X s c r sv me -> munch (ffW X) me m -> wmono usegs me m -> CPM X c (f_ob fP) (f_out fP) m ->
  f_from fP = FOut (f_out fP - f_dist fP) -> 1 <= f_dist fP <= f_out fP -> f_dist fP < 2^32 ->
  0 <= f_len fP < 2^31 -> f_out fP + f_len fP <= arr_len (ic_outbuf c) ->
  evt usegs (TPOST X s c r sv me (FCont (copy_tail xx (copy_while3 xx fP))))
    (FFL X s c r fP 0x22ca0 (wz (il_NO L + f_out fP)) x5 x6 x7 x9 (wz (il_NO L + f_out fP)) (wz (f_dist fP)) (wz (f_len fP)) x29 m).
Proof.
  intros fP x5 x6 x7 x9 x29 me m XO HRS HT FI HS MU0 WM0 HC Efr Rd Rd32 Rlen Rol. tp_open XO HRS HT FI HS. ffx_pose HRS HT. ix_open XO.
  unfold FFL, ff_sp. gF.
  eapply evt_eq; [| eapply (ff_w3b_tp fP (f_out fP) _ _ _ _ _ _ me m); first [assumption | lia] ].
  eapply FFL_intro2; fnorm; ffreg3.
Qed.

Lemma ff_w3x_tp : forall fP (x1 x5 x6 x7 x9 x23 x29 : word) me m,
  ix_ok X -> ff_restored s c r -> ff_typed X s c r -> FINV X s c fP ->
  FFMs X s c r sv me -> munch (ffW X) me m -> wmono usegs me m -> CPM X c (f_ob fP) (f_out fP) m ->
  f_from fP = FWin 0 -> is_window_blk s <> None -> 0 <= f_len fP <= 32768 -> f_out fP + f_len fP <= arr_len (ic_outbuf c) ->
  evt usegs (TPOST X s c r sv me (FCont (copy_tail xx (copy_while3 xx fP))))
    (FFL X s c r fP 0x22d78 x1 x5 x6 x7 x9 (wz (il_NO L + f_out fP)) x23 (wz (f_len fP)) x29 m).
Proof.
  intros fP x1 x5 x6 x7 x9 x23 x29 me m XO HRS HT FI HS MU0 WM0 HC Efr NWB Rlen Rol. tp_open XO HRS HT FI HS. ffx_pose HRS HT. ix_open XO.
  assert (EWA : win_addr L (is_window_blk s) = il_Aw L) by (destruct (is_window_blk s); [reflexivity| exfalso; apply NWB; reflexivity]).
  pose proof (xo_win _ XO (Whas NWB)) as XW.
  assert (SR : srcn s (f_out fP) (f_from fP) (f_len fP)) by (rewrite Efr; cbn; split; [exact NWB| lia]).
  destruct (w3_shape xx fP ltac:(lia)) as (E1 & E2 & E3 & E4 & E5). cbn [x_window ffx_of] in E5.
  unfold ff_frame_cells, ff_sp in FR. unfold ffW in MU0.
  eapply rw_cells_transport in FR; [| exact MU0| exact WM0| cbn [disjoint_from]; cells_cbv; slia].
  unfold FFL, ff_sp. rewrite EWA in FR. do 3 zs. zstep. br_cases K.
  -
    eapply evt_mono.
    + eapply evt_eq; [| eapply (ff_w3t X s c r (f_from fP) (f_ob fP) (f_out fP) (f_out fP) (f_len fP) (f_hold fP) (f_bits fP) (f_in fP) _ _ _ _ _ _ _ _ me m);
        first [ exact CP | exact HC | exact Gwin | exact MU0 | exact WM0 | reflexivity | intros _; exact SR
              | intros i Hi; apply Fbytes; exact Hi | rewrite <- Pin; lia | lia ] ].
      unfold PC_FF_TAIL. eapply FFL_intro2; fnorm; rewrite ?Efr; ffreg3.
    + intros ms' PO. eapply (tpost_of_w3 X s c r sv _ (f_in fP) (f_hold fP) (f_bits fP));
        first [ exact XO | exact Whas | exact PO | exact HS | apply munch_refl | apply wmono_refl | exact E1 | exact E2 | exact E3 | exact E4 | exact E5
              | rewrite cblit_len2; lia | lia ].
  -
    do 3 zs.
    eapply evt_mono.
    + eapply evt_eq; [| eapply (ff_w3l X s c r (Z.to_nat (f_len fP)) (f_from fP) (f_ob fP) (f_out fP) (f_out fP) (f_len fP) (f_hold fP) (f_bits fP) (f_in fP) _ _ _ _ _ _ me m);
        first [ exact CP | exact HC | exact Gwin | exact MU0 | exact WM0 | reflexivity | exact SR
              | intros i Hi; apply Fbytes; exact Hi | rewrite <- Pin; lia | lia ] ].
      unfold PC_FF_W3L. eapply FFL_intro2; fnorm; rewrite ?Efr; ffreg3.
    + intros ms' PO. eapply (tpost_of_w3 X s c r sv _ (f_in fP) (f_hold fP) (f_bits fP));
        first [ exact XO | exact Whas | exact PO | exact HS | apply munch_refl | apply wmono_refl | exact E1 | exact E2 | exact E3 | exact E4 | exact E5
              | rewrite cblit_len2; lia | lia ].
Qed.

Lemma ff_do3_tp : forall fP (x1 x5 x6 x7 x9 x13 x29 : word) me m,
  ix_ok X -> ff_restored s c r -> ff_typed X s c r -> FINV X s c fP ->
  FFMs X s c r sv me -> munch (ffW X) me m -> wmono usegs me m -> CPM X c (f_ob fP) (f_out fP) m ->
  f_from fP = FOut (f_out fP - f_dist fP) -> 1 <= f_dist fP <= f_out fP -> f_dist fP < 2^32 ->
  3 <= f_len fP < 2^31 -> f_out fP + f_len fP <= arr_len (ic_outbuf c) ->
  evt usegs (TPOST X s c r sv me (FCont (copy_tail xx (copy_do3 xx fP))))
    (FFL X s c r fP PC_FF_OUT x1 x5 x6 x7 x9 x13 (wz (f_dist fP)) (wz (f_len fP)) x29 m).
Proof.
  intros fP x1 x5 x6 x7 x9 x13 x29 me m XO HRS HT FI HS MU0 WM0 HC Efr Rd Rd32 Rlen Rol. tp_open XO HRS HT FI HS.
  destruct (do3_shape xx fP ltac:(lia)) as (E1 & E2 & E3 & E4 & E5). cbn [x_window ffx_of] in E5. rewrite Efr in E5.
  eapply evt_mono.
  - eapply evt_eq; [| eapply (ff_do3 X s c r (f_ob fP) (f_out fP) (f_len fP) (f_dist fP) (f_hold fP) (f_bits fP) (f_in fP) _ _ x1 x5 x6 x7 x9 x13 x29 me m);
      first [ exact CP | exact HC | exact Gwin | exact MU0 | exact WM0 | reflexivity
            | intros i Hi; apply Fbytes; exact Hi | rewrite <- Pin; lia | lia ] ].
    eapply FFL_intro2; fnorm; ffreg3.
  - intros ms' PO. eapply (tpost_of_w3 X s c r sv _ (f_in fP) (f_hold fP) (f_bits fP));
      first [ exact XO | exact Whas | exact PO | exact HS | apply munch_refl | apply wmono_refl | exact E1 | exact E2 | exact E3 | exact E4 | exact E5
            | rewrite cblit_len2; lia | lia ].
Qed.

Local Ltac bfact H := first [apply Z.leb_le in H | apply Z.ltb_lt in H | apply Z.ltb_ge in H | apply Z.leb_gt in H].

Lemma ff_place_spec : forall f1 (x1 x6 x7 x9 x13 x29 : word) me m,
  ix_ok X -> ff_restored s c r -> ff_typed X s c r -> FINV X s c f1 ->
  FFMs X s c r sv me -> munch (ffW X) me m -> wmono usegs me m -> CPM X c (f_ob f1) (f_out f1) m ->
  window_ok xx (arr_len (ic_outbuf c)) (arr_len (is_window s)) f1 = true ->
  1 <= f_op f1 <= f_dist f1 -> f_dist f1 <= f_out f1 + f_op f1 -> f_dist f1 < 2^31 -> 3 <= f_len f1 ->
  evt usegs (TPOST X s c r sv me (FCont (copy_tail xx (copy_while3 xx (ff_place xx f1)))))
    (FFL X s c r f1 0x22a44 x1 (wz (f_op f1)) x6 x7 x9 x13 (wz (f_dist f1)) (wz (f_len f1)) x29 m).
Proof.
  intros f1 x1 x6 x7 x9 x13 x29 me m XO HRS HT FI HS MU0 WM0 HC WOK Rop Rdo Rd31 Rlen. tp_open XO HRS HT FI HS. ffx_pose HRS HT. ix_open XO.
  unfold window_ok in WOK. cbn [x_wnext x_wsize x_whave ffx_of f_op f_len f_out fset_op] in WOK.
  apply andb_prop in WOK. destruct WOK as [WL WOK]. apply Z.leb_le in WL.
  destruct ARRS as (AW1 & AW2 & AW3 & AW).
  assert (Wsum : is_wnext s < f_op f1 -> f_op f1 <= is_wsize s + is_wnext s).
  { intros Hlt. destruct (Z.eq_dec (is_wnext s) 0) as [E0|E0].
    - replace (is_wnext s =? 0) with true in WOK by (symmetry; apply Z.eqb_eq; lia).
      apply andb_prop in WOK. destruct WOK as [W1 _]. apply Z.leb_le in W1. lia.
    - replace (is_wnext s =? 0) with false in WOK by (symmetry; apply Z.eqb_neq; lia).
      replace (is_wnext s <? f_op f1) with true in WOK by (symmetry; apply Z.ltb_lt; lia).
      apply andb_prop in WOK. destruct WOK as [W1 _]. apply Z.leb_le in W1. lia. }
  rewrite ff_place_eq by (cbn [x_wnext x_wsize ffx_of]; first [ lia | exact Wsum ]).
  cbn [x_wnext x_wsize ffx_of].
  pose proof FR as FRm. unfold ff_frame_cells, ff_sp in FRm. unfold ffW in MU0.
  eapply rw_cells_transport in FRm; [| exact MU0| exact WM0| cbn [disjoint_from]; cells_cbv; slia].
  unfold FFL, ff_sp.
  zstep. br_cases Kw.
  -
    replace (is_wnext s =? 0) with true in WOK |- * by (symmetry; apply Z.eqb_eq; lia).
    apply andb_prop in WOK. destruct WOK as [W1 WOK]. apply Z.leb_le in W1.
    assert (NWB : is_window_blk s <> None) by (intros E; pose proof (Wnone E); lia).
    assert (EWA : win_addr (ix_L X) (is_window_blk s) = il_Aw (ix_L X)) by (destruct (is_window_blk s); [reflexivity| exfalso; apply NWB; reflexivity]).
    pose proof (xo_win _ XO (Whas NWB)) as XW. pose proof (AW NWB) as WN. rewrite WN in WOK. rewrite EWA in FRm.
    do 4 zs. rewrite (land_u32_small (is_wsize s - f_op f1)) by lia.
    do 2 zs. gF. do 4 zs. gX.
    zstep. br_cases K1.
    +
      replace (f_op f1 <? f_len f1) with false in WOK |- * by (symmetry; apply Z.ltb_ge; lia). bfact WOK.
      eapply evt_eq; [| eapply (ff_w3_tp (fset_from f1 (FWin (is_wsize s - f_op f1))) _ _ _ _ _ _ _ me m); fnorm;
        first [assumption | cbn [srcn]; split; [exact NWB| lia] | lia] ].
      unfold PC_FF_W3E. eapply FFL_intro2; fnorm; ffreg3.
    +
      replace (f_op f1 <? f_len f1) with true in WOK |- * by (symmetry; apply Z.ltb_lt; lia). bfact WOK.
      destruct (pl_leg1_shape xx f1 (is_wsize s - f_op f1) ltac:(lia)) as (G1 & G2 & G3 & G4 & G5 & G7 & G9). cbn [x_window ffx_of] in G9.
      set (g := pl_leg1 xx f1 (is_wsize s - f_op f1)) in *.
      do 3 zs.
      eapply evt_cut.
      { eapply evt_eq; [| eapply (ff_opcd X s c r PC_FF_LPC 0x22c34 (Z.to_nat (f_op f1)) (FWin (is_wsize s - f_op f1)) (f_ob f1) (f_out f1) (f_op f1) (f_hold f1) (f_bits f1) (f_in f1) _ _ _ _ _ _ (wz (f_dist f1)) _ me m);
          first [ left; split; reflexivity | exact CP | exact HC | exact Gwin | exact MU0 | exact WM0 | reflexivity
                | cbn [srcn]; split; [exact NWB| lia] | intros i Hi; apply Fbytes; exact Hi | rewrite <- Pin; lia | lia ] ].
        unfold PC_FF_LPC. eapply FFL_intro2; fnorm; ffreg3. }
      intros ms' (y7 & m' & -> & MU & WM & MI' & CP' & OBT').
      unfold FFL. zs.
      eapply evt_eq; [| eapply (ff_w3c_tp (pl_out g) _ _ _ _ _ me m'); unfold pl_out; fnorm; rewrite ?G1, ?G2, ?G3, ?G4, ?G5, ?G7, ?G9;
        first [ assumption | reflexivity | lia
              | eapply finv_after_copy; [exact FI| fnorm; rewrite ?G1, ?G2, ?G3, ?G7, ?G9, ?cblit_len2; first [reflexivity | assumption | lia] ..] ] ].
      eapply FFL_intro2; unfold pl_out; fnorm; rewrite ?G2, ?G3, ?G1, ?G5, ?G7; ffreg3.
  -
    replace (is_wnext s =? 0) with false in WOK |- * by (symmetry; apply Z.eqb_neq; lia).
    assert (NWB : is_window_blk s <> None) by (intros E; pose proof (Wnone E) as E0; destruct (Wz E0); lia).
    assert (EWA : win_addr (ix_L X) (is_window_blk s) = il_Aw (ix_L X)) by (destruct (is_window_blk s); [reflexivity| exfalso; apply NWB; reflexivity]).
    pose proof (xo_win _ XO (Whas NWB)) as XW. pose proof (AW NWB) as WN. rewrite WN in WOK. rewrite EWA in FRm.
    zstep. br_cases K3.
    +
      replace (is_wnext s <? f_op f1) with false in WOK |- * by (symmetry; apply Z.ltb_ge; lia).
      do 3 zs. rewrite (land_u32_small (is_wnext s - f_op f1)) by lia.
      do 2 zs. gF. do 4 zs. gX.
      zstep. br_cases K1.
      * replace (f_op f1 <? f_len f1) with false in WOK |- * by (symmetry; apply Z.ltb_ge; lia). bfact WOK.
        eapply evt_eq; [| eapply (ff_w3_tp (fset_from f1 (FWin (is_wnext s - f_op f1))) _ _ _ _ _ _ _ me m); fnorm;
          first [assumption | cbn [srcn]; split; [exact NWB| lia] | lia] ].
        unfold PC_FF_W3E. eapply FFL_intro2; fnorm; ffreg3.
      * replace (f_op f1 <? f_len f1) with true in WOK |- * by (symmetry; apply Z.ltb_lt; lia). bfact WOK.
        destruct (pl_leg1_shape xx f1 (is_wnext s - f_op f1) ltac:(lia)) as (G1 & G2 & G3 & G4 & G5 & G7 & G9). cbn [x_window ffx_of] in G9.
        set (g := pl_leg1 xx f1 (is_wnext s - f_op f1)) in *.
        do 3 zs.
        eapply evt_cut.
        { eapply evt_eq; [| eapply (ff_opcd X s c r PC_FF_LPD 0x22ca0 (Z.to_nat (f_op f1)) (FWin (is_wnext s - f_op f1)) (f_ob f1) (f_out f1) (f_op f1) (f_hold f1) (f_bits f1) (f_in f1) _ _ _ _ _ _ (wz (f_dist f1)) _ me m);
            first [ right; split; reflexivity | exact CP | exact HC | exact Gwin | exact MU0 | exact WM0 | reflexivity
                  | cbn [srcn]; split; [exact NWB| lia] | intros i Hi; apply Fbytes; exact Hi | rewrite <- Pin; lia | lia ] ].
          unfold PC_FF_LPD. eapply FFL_intro2; fnorm; ffreg3. }
        intros ms' (y7 & m' & -> & MU & WM & MI' & CP' & OBT').
        eapply evt_eq; [| eapply (ff_w3c_tp (pl_out g) _ _ _ _ _ me m'); unfold pl_out; fnorm; rewrite ?G1, ?G2, ?G3, ?G4, ?G5, ?G7, ?G9;
          first [ assumption | reflexivity | lia
                | eapply finv_after_copy; [exact FI| fnorm; rewrite ?G1, ?G2, ?G3, ?G7, ?G9, ?cblit_len2; first [reflexivity | assumption | lia] ..] ] ].
        unfold FFL. eapply FFL_intro2; unfold pl_out; fnorm; rewrite ?G2, ?G3, ?G1, ?G5, ?G7; ffreg3.
    +
      replace (is_wnext s <? f_op f1) with true in WOK |- * by (symmetry; apply Z.ltb_lt; lia).
      apply andb_prop in WOK. destruct WOK as [W1 WOK]. apply Z.leb_le in W1.
      do 4 zs. rewrite (land_u32_small (is_wnext s + is_wsize s - f_op f1)) by lia.
      replace (is_wnext s + is_wsize s - f_op f1) with (is_wsize s + is_wnext s - f_op f1) by lia.
      do 2 zs. gF. do 4 zs. gX.
      zs. zstep. br_cases K1.
      *
        replace (f_op f1 - is_wnext s <? f_len f1) with false in WOK |- * by (symmetry; apply Z.ltb_ge; lia). bfact WOK.
        eapply evt_eq; [| eapply (ff_w3_tp (fset_op (fset_from f1 (FWin (is_wsize s + is_wnext s - f_op f1))) (f_op f1 - is_wnext s)) _ _ _ _ _ _ _ me m); fnorm;
          first [assumption | cbn [srcn]; split; [exact NWB| lia] | lia] ].
        unfold PC_FF_W3E. eapply FFL_intro2; fnorm; ffreg3.
      *
        replace (f_op f1 - is_wnext s <? f_len f1) with true in WOK |- * by (symmetry; apply Z.ltb_lt; lia).
        apply andb_prop in WOK. destruct WOK as [W2 WOK]. apply Z.leb_le in W2.
        destruct (pl_leg2a_shape xx f1 ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia)) as (G1 & G2 & G3 & G4 & G5 & G7 & G9). cbn [x_window x_wsize x_wnext ffx_of] in G4, G7, G9.
        set (g := pl_leg2a xx f1) in *.
        do 4 zs.
        eapply evt_cut.
        { eapply evt_eq; [| eapply (ff_opa X s c r (Z.to_nat (f_op f1 - is_wnext s)) (FWin (is_wsize s + is_wnext s - f_op f1)) (f_ob f1) (f_out f1) (f_op f1 - is_wnext s) (f_hold f1) (f_bits f1) (f_in f1) _ _ _ _ _ (wz (f_dist f1)) _ me m);
            first [ exact CP | exact HC | exact Gwin | exact MU0 | exact WM0 | reflexivity
                  | cbn [srcn]; split; [exact NWB| lia] | intros i Hi; apply Fbytes; exact Hi | rewrite <- Pin; lia | lia ] ].
          eapply FFL_intro2; fnorm; ffreg3. }
        intros ms' (m' & -> & MU & WM & MI' & CP' & OBT').
        assert (FI1 : FINV X s c g).
        { eapply finv_after_copy; [exact FI| ..]; rewrite ?G1, ?G2, ?G3, ?G7, ?G9, ?cblit_len2; first [reflexivity | exact OBT' | lia]. }
        unfold FFL, ff_sp. zstep. br_cases K2.
        --
          replace (is_wnext s <? f_len f1 - (f_op f1 - is_wnext s)) with false in WOK |- * by (symmetry; apply Z.ltb_ge; lia). bfact WOK.
          eapply evt_eq; [| eapply (ff_w3x_tp (fset_from g (FWin 0)) _ _ _ _ _ _ _ me m'); fnorm; rewrite ?G1, ?G2, ?G3, ?G4, ?G5, ?G7, ?G9;
            first [ assumption | reflexivity | lia ] ].
          eapply FFL_intro2; fnorm; rewrite ?G2, ?G3, ?G1, ?G4, ?G7; ffreg3.
        --
          replace (is_wnext s <? f_len f1 - (f_op f1 - is_wnext s)) with true in WOK |- * by (symmetry; apply Z.ltb_lt; lia). bfact WOK.
          destruct (pl_leg2b_shape xx g ltac:(cbn; lia)) as (H1 & H2 & H3 & H4 & H5 & H7 & H9). cbn [x_window x_wnext ffx_of] in H4, H7, H9.
          rewrite G1 in H1. rewrite G2 in H2. rewrite G3 in H3. rewrite G4 in H4. rewrite G5 in H5. rewrite G7 in H7. rewrite G9, G7 in H9.
          set (h := pl_leg2b xx g) in *.
          clear FRm. pose proof FR as FRm. unfold ff_frame_cells, ff_sp in FRm. unfold ffW in MU.
          eapply rw_cells_transport in FRm; [| exact MU| exact WM| cbn [disjoint_from]; cells_cbv; slia]. rewrite EWA in FRm.
          do 4 zs.
          eapply evt_cut.
          { eapply evt_eq; [| eapply (ff_opb X s c r (Z.to_nat (is_wnext s)) (FWin 0) (f_ob g) (f_out g) (f_out g) (is_wnext s) (f_hold f1) (f_bits f1) (f_in f1) _ _ _ _ _ (wz (f_dist f1)) _ me m');
              rewrite ?G7, ?G9; first [ exact CP | exact CP' | exact Gwin | exact MU | exact WM | reflexivity
                    | cbn [srcn]; split; [exact NWB| lia] | exact OBT' | rewrite ?cblit_len2; lia | rewrite <- Pin; lia | lia ] ].
            eapply FFL_intro2; fnorm; rewrite ?G7; ffreg3. }
          intros ms2 (z6 & m2 & -> & MU2 & WM2 & MI2 & CP2 & OBT2).
          unfold FFL, ff_sp. gT.
          eapply evt_eq; [| eapply (ff_w3b_tp (pl_out h) (f_out g) _ _ _ _ _ _ me m2); unfold pl_out; fnorm; rewrite ?H1, ?H2, ?H3, ?H4, ?H5, ?H7, ?H9;
            first [ assumption | reflexivity | lia
                  | eapply finv_after_copy; [exact FI1| fnorm; rewrite ?H1, ?H2, ?H3, ?H7, ?H9, ?G1, ?G2, ?G3, ?G7, ?G9, ?cblit_len2; first [reflexivity | assumption | lia] ..] ] ].
          eapply FFL_intro2; unfold pl_out; fnorm; rewrite ?H2, ?H3, ?H1, ?H4, ?H5, ?H7; ffreg3.
Qed.

Lemma ff_win : forall f (x1 x5 x7 x9 x13 x29 : word) me m,
  ix_ok X -> ff_restored s c r -> ff_typed X s c r -> FINV X s c f ->
  FFMs X s c r sv me -> munch (ffW X) me m -> wmono usegs me m -> CPM X c (f_ob f) (f_out f) m ->
  wrap32 (f_out f - x_beg xx) < f_dist f -> 1 <= f_dist f < 2^31 -> 3 <= f_len f ->
  (let opw := wrap32 (f_dist f - wrap32 (f_out f - x_beg xx)) in
   if (is_whave s <? opw) && negb (is_sane s =? 0) then true
   else window_ok xx (arr_len (ic_outbuf c)) (arr_len (is_window s)) (fset_op f opw)) = true ->
  evt usegs (TPOST X s c r sv me (ff_winres xx f))
    (FFL X s c r f PC_FF_WIN x1 x5 (wz (il_NO L + x_beg xx)) x7 x9 x13 (wz (f_dist f)) (wz (f_len f)) x29 m).
Proof.
  intros f x1 x5 x7 x9 x13 x29 me m XO HRS HT FI HS MU0 WM0 HC Hbr Rd Rlen WOK. tp_open XO HRS HT FI HS. ffx_pose HRS HT. ix_open XO.
  cbv zeta in WOK. unfold ff_winres.
  rewrite (wrap32_id (f_out f - x_beg xx)) in Hbr, WOK |- * by lia.
  rewrite (wrap32_id (f_dist f - (f_out f - x_beg xx))) in WOK |- * by lia.
  set (opw := f_dist f - (f_out f - x_beg xx)) in *.
  pose proof FR as FRm. unfold ff_frame_cells, ff_sp in FRm. unfold ffW in MU0.
  eapply rw_cells_transport in FRm; [| exact MU0| exact WM0| cbn [disjoint_from]; cells_cbv; slia].
  unfold FFL, ff_sp, PC_FF_WIN. do 2 zs.
  replace (wz (f_dist f - (il_NO L + f_out f + - (il_NO L + x_beg xx)))) with (wz opw) by (f_equal; lia).
  zs. zstep. br_cases K.
  -
    replace (is_whave s <? opw) with false in WOK |- * by (symmetry; apply Z.ltb_ge; lia). cbn [andb] in WOK |- *.
    eapply evt_eq; [| eapply (ff_place_spec (fset_op f opw) _ _ _ _ _ _ me m); fnorm; first [assumption | lia] ].
    eapply FFL_intro2; fnorm; ffreg3.
  -
    replace (is_whave s <? opw) with true in WOK |- * by (symmetry; apply Z.ltb_lt; lia). cbn [andb] in WOK |- *.
    apply (isT_munch me m L s (ffW X)) in GT; [| exact MU0 | exact WM0 | unfold ffW; cbn [disjoint_from]; slia ].
    open_isT GT. zs. zs. zstep. br_cases Ks.
    +
      replace (is_sane s =? 0) with false in WOK |- * by (symmetry; apply Z.eqb_neq; lia). cbn [negb] in WOK |- *.
      pose proof (ffm_after_copy X s c r sv f me m XO Whas HS MU0 WM0 HC) as HM.
      eapply evt_mono.
      * eapply evt_eq; [| eapply (ff_brk3 X s c r sv f _ _ _ _ _ _ _ _ _ m); first [exact XO | exact HRS | exact HT | exact FI | exact HM] ].
        unfold FFL, PC_FF_BRK3. eapply FFL_intro2; fnorm; ffreg3.
      * intros ms' PO. eapply tpost_of_brk; [exact PO| exact FI| exact MU0| exact WM0].
    +
      replace (is_sane s =? 0) with true in WOK |- * by (symmetry; apply Z.eqb_eq; lia). cbn [negb] in WOK |- *.
      eapply evt_eq; [| eapply (ff_place_spec (fset_op f opw) _ _ _ _ _ _ me m); fnorm; first [assumption | lia] ].
      eapply FFL_intro2; fnorm; ffreg3.
Qed.
End WIN.
