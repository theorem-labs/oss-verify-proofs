(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim STree Malloc Monad Stdio StrFun SjModel AtpModel Target Prog AtpImpl.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjTape SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import Layout Exit Printf_wfile Sj_iface Sj_kit Sj_new Sj_new_t2 Sj_h_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Sj_num_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import F_memchr F_memcmp F_strlen F_memcpy F_memmove_t2 Atp_defs Atp_kitu Atp_arrl Atp_str Atp_strr Atp_objk Atp_obju Atp_objt.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Notation ae_T E := (Tf (ae_tws E)).
Notation ae_S E := (Tf (ae_sbs E)).
Notation ae_n E := (Z.of_nat (length (ae_tws E))).
Notation ae_sn E := (Z.of_nat (length (ae_sbs E))).

Definition objs_W (q A' cap : Z) : list (Z * Z) := [(q - 336, q - 112); (A', A' + cap)].

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Lemma shdr_frame : forall W m m' S (lg : bool) A cap sz,
  shdr m S lg A cap sz -> munch W m m' -> wmono usegs m m' -> disjoint_from W S (if lg then 24 else 1) -> shdr m' S lg A cap sz.
Proof.
  intros W m m' S lg A cap sz H MU WM D. unfold shdr in *. destruct lg.
  - destruct H as [H1 H2]. split; [| exact H2]. eapply rw_cells_transport; [exact H1| exact MU| exact WM| exact D].
  - destruct H as (H1 & H2 & H3). split; [| split; assumption]. eapply rw_cells_transport; [exact H1| exact MU| exact WM| exact D].
Qed.

Lemma lxor_ones64 : forall a, 0 <= a < 2^64 -> Z.lxor a 18446744073709551615 = 18446744073709551615 - a.
Proof.
  intros a Ha. change (Z.lxor a 18446744073709551615) with (Z.lxor a (Z.ones 64)).
  assert (E1 : Z.lxor a (Z.ones 64) = Z.land (Z.lnot a) (Z.ones 64)).
  { apply Z.bits_inj'. intros k Hk. rewrite Z.lxor_spec, Z.land_spec, Z.lnot_spec by lia.
    destruct (Z_lt_dec k 64).
    - rewrite Z.ones_spec_low by lia. rewrite Bool.xorb_true_r, Bool.andb_true_r. reflexivity.
    - rewrite Z.ones_spec_high by lia. rewrite Bool.xorb_false_r, Bool.andb_false_r.
      destruct (Z.eq_dec a 0) as [->|]; [rewrite Z.bits_0; reflexivity|].
      rewrite Z.bits_above_log2; [reflexivity| lia|]. apply (Z.lt_le_trans _ 64); [apply Z.log2_lt_pow2; lia| lia]. }
  rewrite E1, Z.land_ones by lia. unfold Z.lnot.
  replace (Z.pred (- a)) with ((18446744073709551615 - a) + (-1) * 2^64) by lia. rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

Section Obj.
  Variable E : aenv.
  Hypothesis OK : aenv_ok E.
  Variable d : nat.

  Lemma obj_str_phase : forall (K : machine_state -> Prop) (m : mem) (F : bvmap 5 word) (fc : bv 32)
      (q : Z) (lg : bool) (A' cap L e0 P L0 sl : Z) (rest0 : list Z) (i e c node out : Z)
      (junk j0 j8 j16 j24 j28 jk j4 : list byte)
      (x1 x3 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),

    shdr m (q + -176) lg A' cap L -> rw_cells usegs m A' [CB (Z.to_nat cap) junk] -> 1 <= L -> L < cap -> cap < 2^40 -> 0 < A' -> A' + cap < 2^63 ->
    (lg = true -> A' + cap <= ae_lo E /\ (A' + cap <= 0x10000 \/ 0x111000 <= A')) -> (lg = false -> A' = q + -175) ->
    (A' + cap <= ae_lo E \/ (A' = q + -175 /\ cap = 23)) ->
    (forall a, A' <= a < A' + cap -> ~ in_block (ae_LB E) a) -> (forall a, in_block (ae_LB E) a -> a < alloc_ceiling) ->
    (ae_PTR E <= P + 1 /\ P + 1 + L0 <= ae_PTR E + zlength (ae_p1 E)) ->

    bytes_at usegs m (P + 1) (map (Z_to_bv 8) rest0) -> Forall (fun c => 0 <= c < 256) rest0 -> zlength rest0 = L0 -> L <= L0 -> L0 < 2^40 ->
    0 <= P -> P + 1 + L0 < 2^63 -> (P + 1 + L0 <= alloc_ceiling) -> 0 <= e0 < L ->

    rw_cells usegs m (q + -208) [CB 8 j0; CB 8 j8; CB 8 j16; CB 4 j24; CB 4 j28] ->
    rw_cells usegs m (q + -152) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 12); CB 4 j4] ->
    rw_cells usegs m (q + -128) [CB 16 jk] ->

    AINV E m -> rw_cells usegs m node [C8 (Z_to_bv 64 (ae_DOC E)); C8 (Z_to_bv 64 i)] -> q <= node -> node + 16 <= ae_B E -> q <= ae_DOC E ->
    ty (ae_T E) i = t_obj -> tnext (ae_T E i) = e + 1 ->
    tiles (field (ae_T E) (ae_S E) (ae_sn E) (elem (ae_T E) (ae_S E) (ae_sn E) ck_any d)) (i + 1) e c -> 0 <= i -> e + 1 <= ae_n E - 1 ->
    (0 < ae_TAPE E /\ ae_TAPE E + 8 * ae_n E <= alloc_ceiling) -> (0 < ae_SBUF E /\ ae_SBUF E + ae_sn E <= alloc_ceiling) ->

    stk usegs m (ae_lo E) (q + -208) -> ae_lo E <= q - 336 -> alloc_ceiling <= ae_lo E -> GLOBALS_TOP <= ae_lo E -> q <= out -> out + 24 <= ae_B E -> ae_B E < 2^63 ->
    mem_inv usegs m ->

    (forall (m' : mem) (sz : Z) (ja' : list byte) (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y19 y21 y28 y29 y30 y31 : word),
       lstr m' (q + -176) lg A' cap sz -> (lg = true -> y10 = Z_to_bv 64 A') ->
       rw_cells usegs m' (q + -208) [CB 32 ja'] ->
       rw_cells usegs m' (q + -152) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 12); CB 4 j4] -> rw_cells usegs m' (q + -128) [CB 16 jk] ->
       mem_inv usegs m' -> stk usegs m' (ae_lo E) (q + -208) -> munch (objs_W q A' cap) m m' -> wmono usegs m m' ->
       evt usegs K (MS (mkR y1 (Z_to_bv 64 (q + -208)) x3 (Z_to_bv 64 RATP) y5 y6 y7 (Z_to_bv 64 out) (Z_to_bv 64 sl) y10 y11 y12 y13 y14 y15 y16 y17
                          (Z_to_bv 64 node) y19 (Z_to_bv 64 (q + -175)) y21 (Z_to_bv 64 49) (Z_to_bv 64 18446744073709551615) (Z_to_bv 64 LIT_T) (Z_to_bv 64 LIT_S) (Z_to_bv 64 48)
                          x27 y28 y29 y30 y31)
                     F (Z_to_bv 64 0x3f2b0) fc None m' (seg_rom usegs))) ->

    (forall (m' : mem) (sz err : Z) (ja' : list byte) (w0 w1 y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y19 y20 y21 y22 y23 y24 y25 y26 y28 y29 y30 y31 : word),
       lstr m' (q + -176) lg A' cap sz ->
       rw_cells usegs m' (q + -208) [CB 32 ja'] ->
       rw_cells usegs m' (q + -152) [C8 w0; C8 w1; C4 (Z_to_bv 64 err); CB 4 j4] -> rw_cells usegs m' (q + -128) [CB 16 jk] ->
       (err = 20 \/ (err = 0 /\ exists vj j', w0 = Z_to_bv 64 (ae_DOC E) /\ w1 = Z_to_bv 64 vj /\
                      elem (ae_T E) (ae_S E) (ae_sn E) ck_any d vj j' /\ 0 <= vj /\ j' <= e)) ->
       mem_inv usegs m' -> stk usegs m' (ae_lo E) (q + -208) -> munch (objs_W q A' cap) m m' -> wmono usegs m m' ->
       (lg = false ->
        evt usegs K (MS (mkR y1 (Z_to_bv 64 (q + -208)) x3 (Z_to_bv 64 RATP) y5 y6 y7 (Z_to_bv 64 out) (Z_to_bv 64 sl) y10 y11 y12 y13 y14 y15 y16 y17
                           (Z_to_bv 64 err) y19 y20 y21 y22 y23 y24 y25 y26 x27 y28 y29 y30 y31)
                      F (Z_to_bv 64 0x3f330) fc None m' (seg_rom usegs))) /\
       (lg = true ->
        evt usegs K (MS (mkR (Z_to_bv 64 0x3f330) (Z_to_bv 64 (q + -208)) x3 (Z_to_bv 64 RATP) y5 y6 y7 (Z_to_bv 64 out) (Z_to_bv 64 sl) (Z_to_bv 64 A') (Z_to_bv 64 cap) y12 y13 y14 y15 y16 y17
                           (Z_to_bv 64 err) y19 y20 y21 y22 y23 y24 y25 y26 x27 y28 y29 y30 y31)
                      F (Z_to_bv 64 0x7b870) fc None m' (seg_rom usegs)))) ->
    evt usegs K (MS (mkR x1 (Z_to_bv 64 (q + -208)) x3 (Z_to_bv 64 RATP) x5 x6 x7 (Z_to_bv 64 out) (Z_to_bv 64 sl) x10 x11 x12 x13 x14 x15 x16 x17
                       (Z_to_bv 64 node) (Z_to_bv 64 e0) (Z_to_bv 64 (P + 1)) (Z_to_bv 64 L) (Z_to_bv 64 A') x23 x24 x25 x26 x27 x28 x29 x30 x31)
                  F (Z_to_bv 64 0x3f1ec) fc None m (seg_rom usegs)).
  Proof.
    intros until x31.
    intros HDR DATA L1 LC CAP A0 AC HLG HSH SEPLO NBLK BLB PIN KEYB KEYF ZL0 LL0 L040 P0 PL PCEIL E0 SCR REC FRK AI NODE QN NB QD TY NXT TILES I0 EN TR SR ST LO CEIL GLO QO OB B63 MI XBAD XREC.
    pose proof OK as OK'. destruct OK' as [WF SBS P1 P1L BT BS BP PP0 _ _ [DL DB] [AL8D AL8T]].
    assert (LO0 : 0 <= ae_lo E) by (destruct ST as [? _]; assumption).
    pose proof CEIL as CEIL'. unfold OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in CEIL; try (pose proof alloc_ceiling_range as CEIL_RANGE__).
    unfold GLOBALS_TOP in GLO.
    pose proof (tape_wf_root _ _ _ _ _ WF) as [_ NR].
    assert (HSN : ae_sn E < 2^56) by (destruct WF as (_ & ? & _); lia).
    pose proof (munch_refl (objs_W q A' cap) m) as MU. pose proof (wmono_refl usegs m) as WM.

    assert (SEPP : P + 1 + L0 <= A' \/ A' + cap <= P + 1).
    { destruct SEPLO as [H|[H1 H2]]; [| lia].
      destruct (Z_le_dec (P + 1 + L0) A') as [|G1]; [lia|]. destruct (Z_le_dec (A' + cap) (P + 1)) as [|G2]; [lia|]. exfalso.
      destruct BP as [Ep0|(bp & Bp1 & Bp2 & Bp3)]; [rewrite Ep0 in PIN; unfold zlength in PIN; cbn in PIN; lia|].
      destruct (Z_le_dec A' (P + 1)) as [Y|N].
      - apply (NBLK (P + 1)); [lia|]. exists bp. split; [exact Bp1| lia].
      - apply (NBLK A'); [lia|]. exists bp. split; [exact Bp1| lia]. }

    hide AI. hide KEYB.
    assert (REGET : forall mX, munch (objs_W q A' cap) m mX -> wmono usegs m mX -> AINV E mX /\ bytes_at usegs mX (P + 1) (map (Z_to_bv 8) rest0)).
    { intros mX MUX WMX. unhide AI. unhide KEYB. pose proof (agree_on_of_munch _ _ _ MUX WMX) as AG. split.
      - eapply AINV_agree; [exact AI| exact AG| | | exact OK].
        + intros a Ha. pose proof (BLB a Ha). unfold objs_W. cbn [outside]. split; [lia|]. split; [| exact I]. intros R. exact (NBLK a R Ha).
        + intros a Ha. unfold objs_W. cbn [outside]. lia.
      - eapply bytes_at_agree; [exact AG| exact KEYB|]. intros a Ha. rewrite length_map in Ha. unfold zlength in ZL0. unfold objs_W. cbn [outside]. lia. }
    destruct (REGET m MU WM) as [(TAPEB & SBUFB & PTRB & DOCC) KEYB0]. unfold objs_W in MU.

    apply (rw_cells_split_CB usegs _ _ [] (Z.to_nat cap) junk [] [Z.to_nat L; Z.to_nat (cap - L)]) in DATA; [| cbn; lia]. cbn [mk_CB_cells app] in DATA.
    apply (proj1 (rw_cells_app _ _ [_] _)) in DATA. destruct DATA as [D1 D2]. cbn [cells_size csize Nat.add] in D2.
    lazymatch type of D2 with rw_cells _ _ ?a _ => replace a with (A' + L) in D2 by lia end.
    pose proof (bytes_at_firstn _ _ _ (Z.to_nat L) KEYB0) as KEYL. rewrite firstn_map in KEYL. clear TAPEB SBUFB PTRB KEYB0.
    pose proof (munch_refl [(A', A' + cap)]%Z m) as MUH.
    step. step. step. step.
    call memmove_far_callZ.
    1:{ exact KEYL. }
    1:{ rewrite length_map, firstn_length_le; [reflexivity| unfold zlength in ZL0; lia]. }
    1:{ exact D1. }
    all: try lia. 1:{ assumption. }
    name_mem m2. rename PC into D1'. clear POST.

    astep. rewrite lxor_ones64 by lia. step. if_lia.
    apply (rw_cells_split_CB usegs _ _ [] (Z.to_nat (cap - L)) _ [] [1; Z.to_nat (cap - L - 1)]%nat) in D2; [| cbn; lia].
    cbn [mk_CB_cells app] in D2.
    astep. astep. astep. astep. astep. astep.

    remember (A' + L) as AL eqn:EAL. rewrite EAL in *. rewrite <- EAL in D2.
    lazymatch goal with |- context [Z_to_bv 64 (A' + L)] => replace (Z_to_bv 64 (A' + L)) with (Z_to_bv 64 AL) by (f_equal; lia) end.
    hstep. subst AL. astep. astep. astep. name_mem m3.
    lazymatch goal with H : mem_inv usegs m3 |- _ => rename H into MI3 end.

    assert (HDR3 : shdr m3 (q + -176) lg A' cap L).
    { eapply shdr_frame; [exact HDR| exact MUH| exact WM|]. cbn. split; [| exact I].
      destruct lg; [destruct (HLG eq_refl) as [X _]; lia| pose proof (HSH eq_refl); lia]. }
    clear MUH.
    pose proof (rw_cells_join _ _ _ _ _ D1' D2 ltac:(cbn [cells_size csize Nat.add]; lia)) as D3. cbn [app] in D3.
    set (jr := take (Z.to_nat (cap - L - 1)) (drop 1 (take (Z.to_nat (cap - L)) (drop (Z.to_nat L) junk)))) in D3.
    assert (LJR : length jr = Z.to_nat (cap - L - 1)).
    { pose proof D3 as [[W _] _]. cbn [cells_wf cell_wf] in W. tauto. }
    assert (DA : u8arr usegs m3 A' (map (Z_to_bv 8) (take (Z.to_nat L) rest0) ++ Z_to_bv 8 0 :: jr)).
    { apply (u8arr_of_rw_cells _ _ _ (Z.to_nat cap)). eapply rw_cells_recast; [exact D3| | cbn [cells_bytes cbytes]; rewrite !app_nil_r; reflexivity|].
      - cbn [cells_wf cell_wf]. rewrite length_app, length_map, firstn_length_le by (unfold zlength in ZL0; lia). cbn [length]. split; [lia| exact I].
      - cbn [cells_size csize]. lia. }
    assert (LS3 : lstr m3 (q + -176) lg A' cap L).
    { unfold lstr. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [| unfold shdr in HDR3; exact HDR3].
      exists (map (Z_to_bv 8) (take (Z.to_nat L) rest0) ++ Z_to_bv 8 0 :: jr). split; [exact DA|]. split.
      - rewrite length_app, length_map, firstn_length_le by (unfold zlength in ZL0; lia). cbn [length]. lia.
      - rewrite app_nth2 by (rewrite length_map, firstn_length_le by (unfold zlength in ZL0; lia); lia).
        rewrite length_map, firstn_length_le by (unfold zlength in ZL0; lia). rewrite Nat.sub_diag. reflexivity. }
    clear D1' D2 D3 DA.

    eapply evt_eq; [| eapply (obj_unesc_loop K m3 F fc (q + -208) (ae_lo E) lg A' cap x3 (Z_to_bv 64 out) (Z_to_bv 64 sl) (Z_to_bv 64 node) x27
              CEIL' ltac:(unfold GLOBALS_TOP; lia) ltac:(lia) ltac:(lia) A0 AC
              ltac:(intros Hl; destruct (HLG Hl) as [X Y]; split; [exact X| exact Y]) ltac:(intros Hs; pose proof (HSH Hs); lia))
              with (n := S (Z.to_nat (L - e0))) (m := m3) (sz := L) (esc := e0)];
      [atp_st_eq| | | replace (q + -208 + 32) with (q + -176) by lia; exact LS3| lia| lia| exact MI3| exact ST| apply munch_refl| apply wmono_refl].
    {
      intros m' sz y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y19 y21 y28 y29 y30 y31 LS' HA0 MI' ST' MU' WM'.
      replace (q + -208 + 32) with (q + -176) in LS' by lia.
      pose proof (rw_cells_transport _ _ _ _ _ _ SCR MU' WM' ltac:(unfold unesc_W; cbn; lia)) as SCR'.
      apply (rw_cells_merge usegs _ _ [] [_; _; _; _; _] []) in SCR'. cbn [cells_size csize cells_bytes cbytes Nat.add app] in SCR'.
      eapply evt_eq; [| eapply XBAD; [exact LS'| exact HA0| exact SCR'| | | exact MI'| exact ST'| |] ]; [atp_st_eq| | | |].
      - eapply rw_cells_transport; [exact REC| exact MU'| exact WM'| unfold unesc_W; cbn; lia].
      - eapply rw_cells_transport; [exact FRK| exact MU'| exact WM'| unfold unesc_W; cbn; lia].
      - eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MU']. unfold sub_fp, unesc_W, objs_W. cbn [outside]. intros x' Hx. lia.
      - eapply wmono_trans; [exact WM| exact WM']. }

    intros m4 sz y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y21 y28 y29 y30 y31 LS4 MI4 ST4 MU4 WM4.
    replace (q + -208 + 32) with (q + -176) in LS4 by lia.
    assert (MU04 : munch (objs_W q A' cap) m m4).
    { eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MU4]. unfold sub_fp, unesc_W, objs_W. cbn [outside]. intros x' Hx. lia. }
    assert (WM04 : wmono usegs m m4) by (eapply wmono_trans; [exact WM| exact WM4]).
    pose proof (rw_cells_transport _ _ _ _ _ _ SCR MU4 WM4 ltac:(unfold unesc_W; cbn; lia)) as SCR4. clear SCR.
    pose proof (rw_cells_transport _ _ _ _ _ _ REC MU4 WM4 ltac:(unfold unesc_W; cbn; lia)) as REC4. clear REC.
    pose proof (rw_cells_transport _ _ _ _ _ _ FRK MU4 WM4 ltac:(unfold unesc_W; cbn; lia)) as FRK4. clear FRK.
    pose proof (rw_cells_transport _ _ _ _ _ _ NODE MU4 WM4 ltac:(unfold unesc_W; cbn; lia)) as NODE4. clear NODE.
    clear DOCC MI3. destruct (REGET m4 MU04 WM04) as [(TAPEB & SBUFB & PTRB & DOCC) _].
    clear MU4 WM4 LS3 HDR3.
    pose proof LS4 as (SZ0 & SZC & _ & _ & _ & (bs4 & BS4 & LBS4 & NUL4) & REP4).

    assert (DEC : forall (K' : machine_state -> Prop),
      (forall (ya0 : word),
         evt usegs K' (MS (mkR y1 (Z_to_bv 64 (q + -208)) x3 (Z_to_bv 64 RATP) y5 y6 y7 (Z_to_bv 64 out) (Z_to_bv 64 sl) ya0 y11 y12 (Z_to_bv 64 sz) y14 y15 y16 y17
                             (Z_to_bv 64 node) (Z_to_bv 64 18446744073709551615) (Z_to_bv 64 A') y21 (Z_to_bv 64 49) (Z_to_bv 64 18446744073709551615) (Z_to_bv 64 LIT_T) (Z_to_bv 64 LIT_S) (Z_to_bv 64 48)
                             x27 y28 y29 y30 y31)
                        F (Z_to_bv 64 0x3f2e4) fc None m4 (seg_rom usegs))) ->
      evt usegs K' (MS (mkR y1 (Z_to_bv 64 (q + -208)) x3 (Z_to_bv 64 RATP) y5 y6 y7 (Z_to_bv 64 out) (Z_to_bv 64 sl) y10 y11 y12 y13 y14 y15 y16 y17
                          (Z_to_bv 64 node) (Z_to_bv 64 18446744073709551615) (Z_to_bv 64 (q + -208 + 33)) y21 (Z_to_bv 64 49) (Z_to_bv 64 18446744073709551615) (Z_to_bv 64 LIT_T) (Z_to_bv 64 LIT_S) (Z_to_bv 64 48)
                          x27 y28 y29 y30 y31)
                     F (Z_to_bv 64 0x3f298) fc None m4 (seg_rom usegs))).
    { intros K' HK'. destruct lg.
      - destruct REP4 as [HDR4 EV4].
        pose proof (rw_cells_C8_read1 _ _ _ _ HDR4) as RD0.

        astep. rewrite zx8_lit by lia. astep. rewrite long_byte0 by lia. step. if_false. step. step. step.
        eapply evt_eq; [| eapply HK']. atp_st_eq.
      - destruct REP4 as (HDR4 & EA4 & ECAP4).

        astep. astep. rewrite short_byte0. step. if_true. astep. rewrite short_size by lia.
        eapply evt_eq; [| eapply HK']. atp_st_eq. }
    apply DEC. clear DEC. intros ya0.

    pose proof (bytes_at_firstn _ _ _ (Z.to_nat sz) (proj1 BS4)) as KB4.
    apply (proj1 (rw_cells_app _ _ [_] _)) in SCR4. destruct SCR4 as [SCR0 AKO]. cbn [cells_size csize Nat.add] in AKO.
    replace (q + -208 + Z.of_nat 8) with (q + -200) in AKO by lia.
    unfold objs_W in MU04.
    astep. step. step. step.
    eapply evt_cut.
    { eapply (atkey_spec E OK d) with (lo := ae_lo E) (kb := firstn (Z.to_nat sz) bs4);
      [exact NODE4| lia| lia| exact TAPEB| exact SBUFB| exact DOCC| exact TY| exact NXT| exact TILES| exact I0| exact EN
      | exact KB4| rewrite firstn_length_le by lia; lia| lia| lia| destruct SEPLO as [H|[H1 H2]]; lia| destruct SEPLO as [H|[H1 H2]]; lia
      | exact AKO| lia| lia| exact TR| exact SR| exact ST4| lia| lia| exact MI4| lia| lia]. }
    cbv beta. intros ms' PO. unfold atkey_post in PO.
    destruct PO as (z0 & z1 & z2 & za0 & za1 & za2 & za3 & za4 & za5 & za6 & za7 & z3 & z4 & z5 & z6 & m5 & r0 & it & code & -> & MU5 & WM5 & MI5 & ST5 & AKO5 & RES5).
    replace (ret_pc (Z_to_bv 64 0x3f2f4)) with (Z_to_bv 64 0x3f2f4) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    replace (q + -208 - 128) with (q - 336) in MU5 by lia.
    assert (MU05 : munch (objs_W q A' cap) m m5).
    { eapply munch_trans; [exact MU04|]. eapply munch_weaken; [| exact MU5]. unfold sub_fp, objs_W. cbn [outside]. intros x' Hx. lia. }
    assert (WM05 : wmono usegs m m5) by (eapply wmono_trans; [exact WM04| exact WM5]).
    assert (LS5 : lstr m5 (q + -176) lg A' cap sz).
    { eapply lstr_frame; [exact LS4| exact MU5| exact WM5| cbn; lia| cbn]. split; [| split; [| exact I]]; destruct SEPLO as [H|[H1 H2]]; lia. }
    pose proof (rw_cells_transport _ _ _ _ _ _ SCR0 MU5 WM5 ltac:(cbn; lia)) as SCR5. clear SCR0.
    pose proof (rw_cells_transport _ _ _ _ _ _ REC4 MU5 WM5 ltac:(cbn; lia)) as REC5. clear REC4.
    pose proof (rw_cells_transport _ _ _ _ _ _ FRK4 MU5 WM5 ltac:(cbn; lia)) as FRK5. clear FRK4.
    clear MU5 WM5 AKO KB4 LS4 BS4 NUL4 REP4 TAPEB SBUFB PTRB DOCC NODE4 MI4 ST4.

    assert (HERR : (code = 20 /\ r0 = Z_to_bv 64 0 /\ it = 0) \/ (code = 0 /\ exists vj j', r0 = Z_to_bv 64 (ae_DOC E) /\ Z_to_bv 64 it = Z_to_bv 64 vj /\
                      elem (ae_T E) (ae_S E) (ae_sn E) ck_any d vj j' /\ 0 <= vj /\ j' <= e)).
    { destruct RES5 as [(C0 & R0 & IT0 & (j' & EL & JE))|(C20 & R0 & IT0)]; [right| left; tauto].
      split; [exact C0|]. exists it, j'. split; [exact R0|]. split; [reflexivity|]. split; [exact EL|]. split; [exact IT0| exact JE]. }
    assert (CR : 0 <= code < 64) by (destruct RES5 as [(C0 & _)|(C20 & _)]; lia).
    pose proof (munch_refl [(q - 152, q - 128)]%Z m5) as MUR. pose proof (wmono_refl usegs m5) as WMR. unfold objs_W in MU05.

    step. step. astep. astep. hstep. hstep. step. if_lia. name_mem m6.
    assert (LS6 : lstr m6 (q + -176) lg A' cap sz).
    { eapply lstr_frame; [exact LS5| exact MUR| exact WMR| cbn; lia| cbn]. split; [| exact I]. destruct SEPLO as [H|[H1 H2]]; lia. }
    clear MUR WMR. pose proof (munch_refl [(q - 152, q - 128)]%Z m6) as MUS. pose proof (wmono_refl usegs m6) as WMS.

    assert (FINISH : forall (m7 : mem) (ya0' : word),
      rw_cells usegs m7 (q + -152) [C8 r0; C8 (Z_to_bv 64 it); C4 (Z_to_bv 64 code); CB 4 j4] ->
      rw_cells usegs m7 (q + -208) [CB 8 j0] -> rw_cells usegs m7 (q + -200) [C8 r0; C8 (Z_to_bv 64 it); C4 (Z_to_bv 64 code); CB 4 j28] ->
      rw_cells usegs m7 (q + -128) [CB 16 jk] -> lstr m7 (q + -176) lg A' cap sz ->
      mem_inv usegs m7 -> stk usegs m7 (ae_lo E) (q + -208) -> munch [(q - 152, q - 128)] m6 m7 -> wmono usegs m6 m7 ->
      evt usegs K (MS (mkR (Z_to_bv 64 0x3f2f4) (Z_to_bv 64 (q + -208)) x3 (Z_to_bv 64 RATP) z0 z1 z2 (Z_to_bv 64 out) (Z_to_bv 64 sl)
                         ya0' (Z_to_bv 64 it) (Z_to_bv 64 64) za3 za4 za5 za6 za7
                         (Z_to_bv 64 code) (Z_to_bv 64 18446744073709551615) (Z_to_bv 64 A') y21 (Z_to_bv 64 49) (Z_to_bv 64 18446744073709551615) (Z_to_bv 64 LIT_T) (Z_to_bv 64 LIT_S) (Z_to_bv 64 48)
                         x27 z3 z4 z5 z6)
                    F (Z_to_bv 64 (if lg then 0x3f320 else 0x3f330)) fc None m7 (seg_rom usegs))).
    { intros m7 ya0' REC7 SCR7 AKO7 FRK7 LS7 MI7 ST7 MU7 WM7.
      assert (MU07 : munch (objs_W q A' cap) m m7).
      { unfold objs_W. eapply munch_trans; [exact MU05|]. eapply munch_weaken; [| exact MU7]. unfold sub_fp. cbn [outside]. intros x' Hx. lia. }
      assert (WM07 : wmono usegs m m7) by (eapply wmono_trans; [exact WM05| exact WM7]).
      destruct (rw_cells_forget _ _ _ _ AKO7) as [ja AKO7']. cbn [cells_size csize Nat.add] in AKO7'.
      pose proof (rw_cells_join _ _ _ _ _ SCR7 AKO7' ltac:(cbn [cells_size csize Nat.add]; lia)) as J1. cbn [app] in J1.
      apply (rw_cells_merge usegs _ _ [] [_; _] []) in J1. cbn [cells_size csize cells_bytes cbytes Nat.add app] in J1.
      assert (HERR' : code = 20 \/ (code = 0 /\ exists vj j', r0 = Z_to_bv 64 (ae_DOC E) /\ Z_to_bv 64 it = Z_to_bv 64 vj /\
                      elem (ae_T E) (ae_S E) (ae_sn E) ck_any d vj j' /\ 0 <= vj /\ j' <= e)) by (destruct HERR as [(C & _)|X]; [left; exact C| right; exact X]).
      pose proof (XREC m7 sz code (j0 ++ ja ++ []) r0 (Z_to_bv 64 it) (Z_to_bv 64 0x3f2f4) z0 z1 z2 ya0' (Z_to_bv 64 it) (Z_to_bv 64 64) za3 za4 za5 za6 za7
                    (Z_to_bv 64 18446744073709551615) (Z_to_bv 64 A') y21 (Z_to_bv 64 49) (Z_to_bv 64 18446744073709551615) (Z_to_bv 64 LIT_T) (Z_to_bv 64 LIT_S) (Z_to_bv 64 48)
                    z3 z4 z5 z6 LS7 J1 REC7 FRK7 HERR' MI7 ST7 MU07 WM07) as [XF XD].
      destruct lg.
      -
        pose proof LS7 as (_ & _ & CAP7 & _ & _ & _ & [HDR7 EV7]).
        pose proof (munch_refl ([] : list (Z * Z)) m7) as MU0. pose proof (wmono_refl usegs m7) as WM0.
        step. step. astep. rewrite long_capmask by lia. step.
        eapply evt_eq; [| eapply (XD eq_refl)]. atp_st_eq.
      - exact (XF eq_refl). }
    destruct lg.
    - pose proof LS6 as (_ & _ & CAP6 & _ & _ & _ & [HDR6 EV6]).
      pose proof (rw_cells_C8_read1 _ _ _ _ HDR6) as RD0.
      astep. rewrite zx8_lit by lia. astep. rewrite long_byte0 by lia. hstep. step. if_false. name_mem m7.
      lazymatch goal with H : rw_cells usegs m7 (q + -152) _ |- _ => rename H into REC7 end.
      lazymatch goal with H : rw_cells usegs m7 (q + -208) _ |- _ => rename H into SCR7 end.
      lazymatch goal with H : rw_cells usegs m7 (q + -128) _ |- _ => rename H into FRK7 end.
      lazymatch goal with H : mem_inv usegs m7 |- _ => rename H into MI7 end.
      lazymatch goal with H : stk usegs m7 _ _ |- _ => rename H into ST7 end.
      assert (LS7 : lstr m7 (q + -176) true A' cap sz).
      { eapply lstr_frame; [exact LS6| exact MUS| exact WMS| cbn; lia| cbn]. split; [| exact I]. destruct SEPLO as [H|[H1 H2]]; lia. }
      eapply evt_eq; [| eapply (FINISH m7); [exact REC7| exact SCR7| exact AKO5| exact FRK7| exact LS7| exact MI7| exact ST7| exact MUS| exact WMS] ]. atp_st_eq.
    - pose proof LS6 as (SZ6 & SZC6 & CAP6 & _ & _ & _ & (HDR6 & EA6 & ECAP6)).
      astep. astep. rewrite short_byte0. hstep. step. if_true. name_mem m7.
      lazymatch goal with H : rw_cells usegs m7 (q + -152) _ |- _ => rename H into REC7 end.
      lazymatch goal with H : rw_cells usegs m7 (q + -208) _ |- _ => rename H into SCR7 end.
      lazymatch goal with H : rw_cells usegs m7 (q + -128) _ |- _ => rename H into FRK7 end.
      lazymatch goal with H : mem_inv usegs m7 |- _ => rename H into MI7 end.
      lazymatch goal with H : stk usegs m7 _ _ |- _ => rename H into ST7 end.
      assert (LS7 : lstr m7 (q + -176) false A' cap sz).
      { eapply lstr_frame; [exact LS6| exact MUS| exact WMS| cbn; lia| cbn]. split; [| exact I]. destruct SEPLO as [H|[H1 H2]]; lia. }
      eapply evt_eq; [| eapply (FINISH m7); [exact REC7| exact SCR7| exact AKO5| exact FRK7| exact LS7| exact MI7| exact ST7| exact MUS| exact WMS] ]. atp_st_eq.
  Qed.
End Obj.
End WithCeiling0.
