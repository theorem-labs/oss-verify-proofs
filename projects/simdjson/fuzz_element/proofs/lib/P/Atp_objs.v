(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX StoreFast.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.MallocP Require Import RMallocRep RMallocTree RMalloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim STree Malloc Monad Stdio StrFun SjModel AtpModel Target Prog AtpImpl.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjTape SjTapeList.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.P Require Import Layout Exit Printf_wfile Sj_iface Sj_kit Sj_new Sj_new_t2 Sj_h_kit.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.P Require Import F_memchr F_memcmp F_strlen F_memcpy Sj_num_kit F_memmove_t2 Atp_defs Atp_str Atp_strr Atp_objl Atp_obju Atp_objt.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.P Require Import Rnd.
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

Definition objs_W (q A' cap : Z) : list (Z * Z) := [(q - 304, q - 104); (A', A' + cap)].

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Lemma shdr_frame : forall W m m' S (lg : bool) A cap sz,
  shdr m S lg A cap sz -> munch W m m' -> wmono psegs m m' -> disjoint_from W S (if lg then 24 else 1) -> shdr m' S lg A cap sz.
Proof.
  intros W m m' S lg A cap sz H MU WM D. unfold shdr in *. destruct lg.
  - destruct H as [H1 H2]. split; [| exact H2]. eapply rw_cells_transport; [exact H1| exact MU| exact WM| exact D].
  - destruct H as (H1 & H2 & H3). split; [| split; assumption]. eapply rw_cells_transport; [exact H1| exact MU| exact WM| exact D].
Qed.

Section Obj.
  Variable E : aenv.
  Hypothesis OK : aenv_ok E.
  Variable d : nat.

  Lemma obj_str_phase : forall (K : machine_state -> Prop) (m : mem) (F : bvmap 5 word) (fc : bv 32)
      (q : Z) (lg : bool) (A' cap L e0 P L0 sl : Z) (rest0 : list Z) (i e c node out : Z)
      (junk j0 j8 j16 j24 j32 j40 j48 j64 j4 : list byte)
      (x1 x3 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x19 x24 x25 x28 x29 x30 x31 : word),

    shdr m (q + -152) lg A' cap L -> rw_cells psegs m A' [CB (Z.to_nat cap) junk] -> 1 <= L -> L < cap -> cap < 2^40 -> 0 < A' -> A' + cap < 2^63 ->
    (lg = true -> A' + cap <= ae_lo E /\ (A' + cap <= 0x10000 \/ 0x105000 <= A')) -> (lg = false -> A' = q + -151) ->

    (A' + cap <= ae_lo E \/ (A' = q + -151 /\ cap = 23)) ->
    (forall a, A' <= a < A' + cap -> ~ in_block (ae_LB E) a) -> (forall a, in_block (ae_LB E) a -> a < alloc_ceiling) ->
    (ae_PTR E <= P + 1 /\ P + 1 + L0 <= ae_PTR E + zlength (ae_p1 E)) ->

    bytes_at psegs m (P + 1) (map (Z_to_bv 8) rest0) -> Forall (fun c => 0 <= c < 256) rest0 -> zlength rest0 = L0 -> L <= L0 -> L0 < 2^40 ->
    0 <= P -> P + 1 + L0 < 2^63 -> (P + 1 + L0 <= alloc_ceiling) -> 0 <= e0 < L ->

    rw_cells psegs m (q + -224) [CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24; CB 8 j32; CB 8 j40; CB 8 j48; C8 (Z_to_bv 64 sl); CB 8 j64] ->
    rw_cells psegs m (q + -128) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 12); CB 4 j4] ->

    AINV E m -> rw_cells psegs m node [C8 (Z_to_bv 64 (ae_DOC E)); C8 (Z_to_bv 64 i)] -> q <= node -> node + 16 <= ae_B E -> q <= ae_DOC E ->
    ty (ae_T E) i = t_obj -> tnext (ae_T E i) = e + 1 ->
    tiles (field (ae_T E) (ae_S E) (ae_sn E) (elem (ae_T E) (ae_S E) (ae_sn E) ck_any d)) (i + 1) e c -> 0 <= i -> e + 1 <= ae_n E - 1 ->
    (0 < ae_TAPE E /\ ae_TAPE E + 8 * ae_n E <= alloc_ceiling) -> (0 < ae_SBUF E /\ ae_SBUF E + ae_sn E <= alloc_ceiling) ->

    stk psegs m (ae_lo E) (q + -224) -> ae_lo E <= q - 304 -> alloc_ceiling <= ae_lo E -> GLOBALS_TOP <= ae_lo E -> q <= out -> out + 24 <= ae_B E -> ae_B E < 2^63 ->
    mem_inv psegs m ->

    (forall (m' : mem) (sz : Z) (ja' jb' : list byte) (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y21 y22 y28 y29 y30 y31 : word),
       lstr m' (q + -152) lg A' cap sz -> (lg = true -> y10 = Z_to_bv 64 A') ->
       rw_cells psegs m' (q + -224) [CB 56 ja'; C8 (Z_to_bv 64 sl); CB 8 jb'] ->
       rw_cells psegs m' (q + -128) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 12); CB 4 j4] ->
       mem_inv psegs m' -> stk psegs m' (ae_lo E) (q + -224) -> munch (objs_W q A' cap) m m' -> wmono psegs m m' ->
       evt psegs K (MS (mkR y1 (Z_to_bv 64 (q + -224)) x3 (Z_to_bv 64 RATP) y5 y6 y7 (Z_to_bv 64 (P + 1)) (Z_to_bv 64 49) y10 y11 y12 y13 y14 y15 y16 y17
                          (Z_to_bv 64 18446744073709551615) (Z_to_bv 64 (q + -151)) (Z_to_bv 64 node) y21 y22 (Z_to_bv 64 LIT_T) (Z_to_bv 64 LIT_S) (Z_to_bv 64 48)
                          (Z_to_bv 64 out) (Z_to_bv 64 L0) y28 y29 y30 y31)
                     F (Z_to_bv 64 0x3dce0) fc None m' (seg_rom psegs))) ->

    (forall (m' : mem) (sz err : Z) (ja' jb' : list byte) (w0 w1 y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y25 y28 y29 y30 y31 : word),
       lstr m' (q + -152) lg A' cap sz ->
       rw_cells psegs m' (q + -224) [CB 56 ja'; C8 (Z_to_bv 64 sl); CB 8 jb'] ->
       rw_cells psegs m' (q + -128) [C8 w0; C8 w1; C4 (Z_to_bv 64 err); CB 4 j4] ->
       (err = 20 \/ (err = 0 /\ exists vj j', w0 = Z_to_bv 64 (ae_DOC E) /\ w1 = Z_to_bv 64 vj /\
                      elem (ae_T E) (ae_S E) (ae_sn E) ck_any d vj j' /\ 0 <= vj /\ j' <= e)) ->
       mem_inv psegs m' -> stk psegs m' (ae_lo E) (q + -224) -> munch (objs_W q A' cap) m m' -> wmono psegs m m' ->
       (lg = false ->
        evt psegs K (MS (mkR y1 (Z_to_bv 64 (q + -224)) x3 (Z_to_bv 64 RATP) y5 y6 y7 (Z_to_bv 64 (P + 1)) y9 y10 y11 y12 y13 y14 y15 y16 y17
                           y18 y19 y20 y21 y22 y23 (Z_to_bv 64 err) y25 (Z_to_bv 64 out) (Z_to_bv 64 L0) y28 y29 y30 y31)
                      F (Z_to_bv 64 0x3dee0) fc None m' (seg_rom psegs))) /\
       (lg = true ->
        evt psegs K (MS (mkR (Z_to_bv 64 0x3dee0) (Z_to_bv 64 (q + -224)) x3 (Z_to_bv 64 RATP) y5 y6 y7 (Z_to_bv 64 (P + 1)) y9 (Z_to_bv 64 A') (Z_to_bv 64 cap) y12 y13 y14 y15 y16 y17
                           y18 y19 y20 y21 y22 y23 (Z_to_bv 64 err) y25 (Z_to_bv 64 out) (Z_to_bv 64 L0) y28 y29 y30 y31)
                      F (Z_to_bv 64 0x6fc70) fc None m' (seg_rom psegs)))) ->
    evt psegs K (MS (mkR x1 (Z_to_bv 64 (q + -224)) x3 (Z_to_bv 64 RATP) x5 x6 x7 x8 (Z_to_bv 64 (P + 1)) x10 x11 x12 x13 x14 x15 x16 x17
                       (Z_to_bv 64 sl) x19 (Z_to_bv 64 node) (Z_to_bv 64 L) (Z_to_bv 64 e0) (Z_to_bv 64 A') x24 x25 (Z_to_bv 64 out) (Z_to_bv 64 L0) x28 x29 x30 x31)
                  F (Z_to_bv 64 0x3dc24) fc None m (seg_rom psegs)).
  Proof.
    intros until x31.
    intros HDR DATA L1 LC CAP A0 AC HLG HSH SEPLO NBLK BLB PIN KEYB KEYF ZL0 LL0 L040 P0 PL PCEIL E0 SCR REC AI NODE QN NB QD TY NXT TILES I0 EN TR SR ST LO CEIL GLO QO OB B63 MI XBAD XREC.
    pose proof OK as OK'. destruct OK' as [WF SBS P1 P1L BT BS BP PP0 _ _ [DL DB]].
    assert (LO0 : 0 <= ae_lo E) by (destruct ST as [? _]; assumption).
    pose proof CEIL as CEIL'. unfold OSSVerify.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in CEIL; try (pose proof alloc_ceiling_range as CEIL_RANGE__).
    unfold GLOBALS_TOP in GLO.
    pose proof (tape_wf_root _ _ _ _ _ WF) as [_ NR].
    assert (HSN : ae_sn E < 2^56) by (destruct WF as (_ & ? & _); lia).
    pose proof (munch_refl (objs_W q A' cap) m) as MU. pose proof (wmono_refl psegs m) as WM.

    assert (SEPP : P + 1 + L0 <= A' \/ A' + cap <= P + 1).
    { destruct SEPLO as [H|[H1 H2]]; [| lia].
      destruct (Z_le_dec (P + 1 + L0) A') as [|G1]; [lia|]. destruct (Z_le_dec (A' + cap) (P + 1)) as [|G2]; [lia|]. exfalso.
      destruct BP as [Ep0|(bp & Bp1 & Bp2 & Bp3)]; [rewrite Ep0 in PIN; unfold zlength in PIN; cbn in PIN; lia|].
      destruct (Z_le_dec A' (P + 1)) as [Y|N].
      - apply (NBLK (P + 1)); [lia|]. exists bp. split; [exact Bp1| lia].
      - apply (NBLK A'); [lia|]. exists bp. split; [exact Bp1| lia]. }

    hide AI. hide KEYB.
    assert (REGET : forall mX, munch (objs_W q A' cap) m mX -> wmono psegs m mX -> AINV E mX /\ bytes_at psegs mX (P + 1) (map (Z_to_bv 8) rest0)).
    { intros mX MUX WMX. unhide AI. unhide KEYB. pose proof (agree_on_of_munch _ _ _ MUX WMX) as AG. split.
      - eapply AINV_agree; [exact AI| exact AG| | | exact OK].
        + intros a Ha. pose proof (BLB a Ha). unfold objs_W. cbn [outside]. split; [lia|]. split; [| exact I]. intros R. exact (NBLK a R Ha).
        + intros a Ha. unfold objs_W. cbn [outside]. lia.
      - eapply bytes_at_agree; [exact AG| exact KEYB|]. intros a Ha. rewrite length_map in Ha. unfold zlength in ZL0. unfold objs_W. cbn [outside]. lia. }
    destruct (REGET m MU WM) as [(TAPEB & SBUFB & PTRB & DOCC) KEYB0]. unfold objs_W in MU.

    apply (rw_cells_split_CB psegs _ _ [] (Z.to_nat cap) junk [] [Z.to_nat L; Z.to_nat (cap - L)]) in DATA; [| cbn; lia]. cbn [mk_CB_cells app] in DATA.
    apply (proj1 (rw_cells_app _ _ [_] _)) in DATA. destruct DATA as [D1 D2]. cbn [cells_size csize Nat.add] in D2.
    lazymatch type of D2 with rw_cells _ _ ?a _ => replace a with (A' + L) in D2 by lia end.
    pose proof (bytes_at_firstn _ _ _ (Z.to_nat L) KEYB0) as KEYL. rewrite firstn_map in KEYL. clear TAPEB SBUFB PTRB KEYB0.
    pose proof (munch_refl [(A', A' + cap)]%Z m) as MUH.
    astep. step. step. step. step. step.
    call memmove_far_callZ.
    1:{ exact KEYL. }
    1:{ rewrite length_map, firstn_length_le; [reflexivity| unfold zlength in ZL0; lia]. }
    1:{ exact D1. }
    all: try lia. 1:{ assumption. }
    name_mem m2. rename PC into D1'. clear POST.

    apply (rw_cells_split_CB psegs _ _ [] (Z.to_nat (cap - L)) _ [] [1; Z.to_nat (cap - L - 1)]%nat) in D2; [| cbn; lia].
    cbn [mk_CB_cells app] in D2.
    astep. astep. astep. astep. astep.

    remember (A' + L) as AL eqn:EAL. rewrite EAL in *. rewrite <- EAL in D2.
    lazymatch goal with |- context [Z_to_bv 64 (A' + L)] => replace (Z_to_bv 64 (A' + L)) with (Z_to_bv 64 AL) by (f_equal; lia) end.
    hstep. subst AL. astep. astep. astep. name_mem m3.

    assert (HDR3 : shdr m3 (q + -152) lg A' cap L).
    { eapply shdr_frame; [exact HDR| exact MUH| exact WM|]. cbn. split; [| exact I].
      destruct lg; [destruct (HLG eq_refl) as [X _]; lia| pose proof (HSH eq_refl); lia]. }
    clear MUH.
    pose proof (rw_cells_join _ _ _ _ _ D1' D2 ltac:(cbn [cells_size csize Nat.add]; lia)) as D3. cbn [app] in D3.
    set (jr := take (Z.to_nat (cap - L - 1)) (drop 1 (take (Z.to_nat (cap - L)) (drop (Z.to_nat L) junk)))) in D3.
    assert (LJR : length jr = Z.to_nat (cap - L - 1)).
    { pose proof D3 as [[W _] _]. cbn [cells_wf cell_wf] in W. tauto. }
    assert (DA : u8arr psegs m3 A' (map (Z_to_bv 8) (take (Z.to_nat L) rest0) ++ Z_to_bv 8 0 :: jr)).
    { apply (u8arr_of_rw_cells _ _ _ (Z.to_nat cap)). eapply rw_cells_recast; [exact D3| | cbn [cells_bytes cbytes]; rewrite !app_nil_r; reflexivity|].
      - cbn [cells_wf cell_wf]. rewrite length_app, length_map, firstn_length_le by (unfold zlength in ZL0; lia). cbn [length]. split; [lia| exact I].
      - cbn [cells_size csize]. lia. }
    assert (LS3 : lstr m3 (q + -152) lg A' cap L).
    { unfold lstr. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [| unfold shdr in HDR3; exact HDR3].
      exists (map (Z_to_bv 8) (take (Z.to_nat L) rest0) ++ Z_to_bv 8 0 :: jr). split; [exact DA|]. split.
      - rewrite length_app, length_map, firstn_length_le by (unfold zlength in ZL0; lia). cbn [length]. lia.
      - rewrite app_nth2 by (rewrite length_map, firstn_length_le by (unfold zlength in ZL0; lia); lia).
        rewrite length_map, firstn_length_le by (unfold zlength in ZL0; lia). rewrite Nat.sub_diag. reflexivity. }
    clear D1' D2 D3 DA.

    eapply evt_eq; [| eapply (obj_unesc_loop K m3 F fc (q + -224) (ae_lo E) lg A' cap x3 (Z_to_bv 64 (P + 1)) (Z_to_bv 64 node) (Z_to_bv 64 out) (Z_to_bv 64 L0)
              CEIL' ltac:(unfold GLOBALS_TOP; lia) ltac:(lia) ltac:(lia) A0 AC
              ltac:(intros Hl; destruct (HLG Hl) as [X Y]; split; [exact X| exact Y]) ltac:(intros Hs; pose proof (HSH Hs); lia))
              with (n := S (Z.to_nat (L - e0))) (m := m3) (sz := L) (esc := e0)];
      [atp_st_eq| | | replace (q + -224 + 72) with (q + -152) by lia; exact LS3| lia| lia| exact MI0| exact ST| apply munch_refl| apply wmono_refl].
    {
      intros m' sz y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y21 y22 y28 y29 y30 y31 LS' HA0 MI' ST' MU' WM'.
      replace (q + -224 + 72) with (q + -152) in LS' by lia.
      pose proof (rw_cells_transport _ _ _ _ _ _ SCR MU' WM' ltac:(unfold unesc_W; cbn; lia)) as SCR'.
      apply (rw_cells_merge psegs _ _ [] [_; _; _; _; _; _; _] [_; _]) in SCR'. cbn [cells_size csize cells_bytes cbytes Nat.add app] in SCR'.
      eapply evt_eq; [| eapply XBAD; [exact LS'| exact HA0| exact SCR'| | exact MI'| exact ST'| |] ]; [atp_st_eq| | |].
      - eapply rw_cells_transport; [exact REC| exact MU'| exact WM'| unfold unesc_W; cbn; lia].
      - eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MU']. unfold sub_fp, unesc_W, objs_W. cbn [outside]. intros x' Hx. lia.
      - eapply wmono_trans; [exact WM| exact WM']. }

    intros m4 sz y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y21 y28 y29 y30 y31 LS4 MI4 ST4 MU4 WM4.
    replace (q + -224 + 72) with (q + -152) in LS4 by lia.
    assert (MU04 : munch (objs_W q A' cap) m m4).
    { eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MU4]. unfold sub_fp, unesc_W, objs_W. cbn [outside]. intros x' Hx. lia. }
    assert (WM04 : wmono psegs m m4) by (eapply wmono_trans; [exact WM| exact WM4]).
    pose proof (rw_cells_transport _ _ _ _ _ _ SCR MU4 WM4 ltac:(unfold unesc_W; cbn; lia)) as SCR4. clear SCR.
    pose proof (rw_cells_transport _ _ _ _ _ _ REC MU4 WM4 ltac:(unfold unesc_W; cbn; lia)) as REC4. clear REC.
    pose proof (rw_cells_transport _ _ _ _ _ _ NODE MU4 WM4 ltac:(unfold unesc_W; cbn; lia)) as NODE4. clear NODE.
    clear DOCC MI0. destruct (REGET m4 MU04 WM04) as [(TAPEB & SBUFB & PTRB & DOCC) _].
    clear MU4 WM4 LS3 HDR3.
    pose proof LS4 as (SZ0 & SZC & _ & _ & _ & (bs4 & BS4 & LBS4 & NUL4) & REP4).
    pose proof (munch_refl ([] : list (Z * Z)) m4) as MU0. pose proof (wmono_refl psegs m4) as WM0.

    assert (DEC : forall (K' : machine_state -> Prop),
      (forall (ya0 ya1 : word), (lg = true -> ya0 = Z_to_bv 64 A') ->
         evt psegs K' (MS (mkR y1 (Z_to_bv 64 (q + -224)) x3 (Z_to_bv 64 RATP) y5 y6 y7 (Z_to_bv 64 (P + 1)) (Z_to_bv 64 49) ya0 ya1 y12 y13 y14
                             (Z_to_bv 64 (if lg then 1 else 0)) y16 y17
                             (Z_to_bv 64 18446744073709551615) (Z_to_bv 64 A') (Z_to_bv 64 node) y21 (Z_to_bv 64 sz) (Z_to_bv 64 LIT_T) (Z_to_bv 64 LIT_S) (Z_to_bv 64 48)
                             (Z_to_bv 64 out) (Z_to_bv 64 L0) y28 y29 y30 y31)
                        F (Z_to_bv 64 0x3dd10) fc None m4 (seg_rom psegs))) ->
      evt psegs K' (MS (mkR y1 (Z_to_bv 64 (q + -224)) x3 (Z_to_bv 64 RATP) y5 y6 y7 (Z_to_bv 64 (P + 1)) (Z_to_bv 64 49) y10 y11 y12 y13 y14 y15 y16 y17
                          (Z_to_bv 64 18446744073709551615) (Z_to_bv 64 (q + -224 + 73)) (Z_to_bv 64 node) y21 (Z_to_bv 64 18446744073709551615) (Z_to_bv 64 LIT_T) (Z_to_bv 64 LIT_S) (Z_to_bv 64 48)
                          (Z_to_bv 64 out) (Z_to_bv 64 L0) y28 y29 y30 y31)
                     F (Z_to_bv 64 0x3dcc0) fc None m4 (seg_rom psegs))).
    { intros K' HK'. destruct lg.
      - destruct REP4 as [HDR4 EV4].
        pose proof (rw_cells_C8_read1 _ _ _ _ HDR4) as RD0.

        astep. rewrite zx8_lit by lia. step. astep. rewrite long_byte0 by lia. step. if_false. step. step. if_false. step. step.
        eapply evt_eq; [| eapply HK'; reflexivity]. atp_st_eq.
      - destruct REP4 as (HDR4 & EA4 & ECAP4).
        pose proof (bytes_at_read psegs m4 A' bs4 15 8 (proj1 BS4) ltac:(lia) ltac:(lia)) as RD8.
        remember (firstn 8 (skipn (Z.to_nat 15) bs4)) as l8 eqn:El8 in RD8. replace (A' + 15) with (q + -224 + 88) in RD8 by lia.

        astep. step. astep. rewrite short_byte0. step. if_true. step. if_true. astep. rewrite short_size by lia.
        eapply evt_eq; [| eapply HK'; intros X; discriminate X]. atp_st_eq. }
    apply DEC. clear DEC. intros ya0 ya1 HYA0.

    pose proof (tiles_le _ (field_lt _ _ _ _ (elem_lt _ _ _ _ d)) _ _ _ TILES) as [IE CC].
    pose proof (tape_read _ (ae_TAPE E) (ae_tws E) i TAPEB ltac:(lia)) as RDT.
    unfold ty in TY. pose proof (ttype_range _ _ TY ltac:(unfold t_obj; lia) ltac:(unfold t_obj; lia)) as TIR.

    step. step. step. astep. astep. step. astep. rewrite TY. unfold t_obj. astep. astep. astep. step. if_false.

    astep. astep. astep. astep. step. if_true. astep. astep. astep. astep. astep. step. if_false. astep. astep.
    rewrite land32_tnext by lia. rewrite NXT. step.

    astep. astep.

    assert (STORE : forall (m5 : mem) (err : Z) (ja5 jb5 : list byte) (w0 w1 z1 z5 z6 z7 z9 z12 z13 z14 z16 z17 z19 z20 z21 z22 z23 z25 z28 z29 z30 z31 : word),
      rw_cells psegs m5 (q + -224) [CB 56 ja5; C8 (Z_to_bv 64 sl); CB 8 jb5] ->
      rw_cells psegs m5 (q + -128) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 12); CB 4 j4] ->
      (err = 20 \/ (err = 0 /\ exists vj j', w0 = Z_to_bv 64 (ae_DOC E) /\ w1 = Z_to_bv 64 vj /\
                     elem (ae_T E) (ae_S E) (ae_sn E) ck_any d vj j' /\ 0 <= vj /\ j' <= e)) -> 0 <= err < 64 ->
      mem_inv psegs m5 -> stk psegs m5 (ae_lo E) (q + -224) -> munch (objs_W q A' cap) m m5 -> wmono psegs m m5 ->
      lstr m5 (q + -152) lg A' cap sz ->
      evt psegs K (MS (mkR z1 (Z_to_bv 64 (q + -224)) x3 (Z_to_bv 64 RATP) z5 z6 z7 (Z_to_bv 64 (P + 1)) z9 ya0 w0 z12 z13 z14
                         (Z_to_bv 64 (if lg then 1 else 0)) z16 z17 w1 z19 z20 z21 z22 z23 (Z_to_bv 64 err) z25 (Z_to_bv 64 out) (Z_to_bv 64 L0) z28 z29 z30 z31)
                    F (Z_to_bv 64 0x3dec4) fc None m5 (seg_rom psegs))).
    { intros m5 err ja5 jb5 w0 w1 z1 z5 z6 z7 z9 z12 z13 z14 z16 z17 z19 z20 z21 z22 z23 z25 z28 z29 z30 z31 SCR5 REC5 HERR ERR64 MI5 ST5 MU5 WM5 LS5.
      clear MU0 WM0. unfold objs_W in MU5.
      pose proof (munch_refl [(q - 128, q - 104)]%Z m5) as MUR. pose proof (wmono_refl psegs m5) as WMR.

      hstep. hstep. hstep. name_mem m6.
      assert (LS6 : lstr m6 (q + -152) lg A' cap sz).
      { eapply lstr_frame; [exact LS5| exact MUR| exact WMR| cbn; lia| cbn]. split; [| exact I].
        destruct SEPLO as [H|[H1 H2]]; lia. }
      clear MUR WMR LS5.

      destruct lg.
      - pose proof LS6 as (_ & _ & _ & _ & _ & _ & [HDR6 EV6]). rewrite (HYA0 eq_refl).
        pose proof (rw_cells_C8_read1 _ _ _ _ HDR6) as RD0.
        step. if_false. astep. astep. rewrite long_capmask by lia. step.
        eapply (proj2 (XREC m6 sz err ja5 jb5 w0 w1 (Z_to_bv 64 0) _ _ _ _ (Z_to_bv 64 0) (Z_to_bv 64 0) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ LS6 SCR5 REC5 HERR MI5 ST5 MU5 WM5) eq_refl).
      - step. if_true.
        eapply (proj1 (XREC m6 sz err ja5 jb5 w0 w1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ LS6 SCR5 REC5 HERR MI5 ST5 MU5 WM5) eq_refl). }
    step. if_cases KEM; zify_cond KEM.
    2:{
      astep. astep. step.
      apply (rw_cells_merge psegs _ _ [] [_; _; _; _; _; _; _] [_; _]) in SCR4.
      apply (rw_cells_merge psegs _ _ [_; _] [_] []) in SCR4. cbn [cells_size csize cells_bytes cbytes Nat.add app] in SCR4.
      eapply evt_eq; [| eapply (STORE m4 20); [exact SCR4| exact REC4| left; reflexivity| lia| exact MI4| exact ST4| exact MU04| exact WM04| exact LS4] ]; [atp_st_eq]. }

    clear MU0 WM0. pose proof (munch_refl [(q - 224, q - 152)]%Z m4) as MUS. pose proof (wmono_refl psegs m4) as WMS. unfold objs_W in MU04.
    hstep. hstep. hstep. hstep. astep. astep. hstep. step. astep. astep. astep. astep. hstep. astep. astep. astep. astep. hstep. name_mem m5.
    assert (LS5 : lstr m5 (q + -152) lg A' cap sz).
    { eapply lstr_frame; [exact LS4| exact MUS| exact WMS| cbn; lia| cbn]. split; [| exact I]. destruct SEPLO as [H|[H1 H2]]; lia. }
    clear MUS WMS BS4. try clear TAPEB. try clear SBUFB. try clear PTRB. try clear DOCC.
    assert (MU05 : munch (objs_W q A' cap) m m5) by exact MU04.
    destruct (REGET m5 MU05 WM04) as [(TAPEB & SBUFB & PTRB & DOCC5) _].
    pose proof LS5 as (_ & _ & _ & _ & _ & (bs5 & BS5 & LBS5 & NUL5) & _).
    pose proof (bytes_at_firstn _ _ _ (Z.to_nat sz) (proj1 BS5)) as KB5.
    lazymatch goal with H : rw_cells psegs m5 (q + -224) _ |- _ => rename H into SCR5 end.

    pose proof SCR5 as SCRX.
    apply (proj1 (rw_cells_app _ _ [_; _; _; _] _)) in SCRX. destruct SCRX as [_ SCRX]. cbn [cells_size csize Nat.add] in SCRX.
    apply (proj1 (rw_cells_app _ _ [_] _)) in SCRX. destruct SCRX as [M32 SCRX]. cbn [cells_size csize Nat.add] in SCRX.
    apply (proj1 (rw_cells_app _ _ [_; _; _] _)) in SCRX. destruct SCRX as [_ M64]. cbn [cells_size csize Nat.add] in M64.
    replace (q + -224 + Z.of_nat 32) with (q + -224 + 32) in M32 by lia.
    lazymatch type of M64 with rw_cells _ _ ?a _ => replace a with (q + -224 + 64) in M64 by lia end.
    eapply evt_eq; [| eapply (obj_key_loop2 E OK d K m5 F fc e (q + -224) A' sz (firstn (Z.to_nat sz) bs5) x3 _ _ _ _ _ _ _ _ _ _ _
                               TAPEB SBUFB KB5 ltac:(rewrite firstn_length_le by lia; lia) ltac:(lia) ltac:(lia) M64 M32 EN MI4 SR)
                        with (n := S (Z.to_nat (e - (i + 1)))) (it := i + 1) (c' := c)];
      [atp_st_eq| | | exact TILES| exact KEM| lia| lia].
    -
      intros it j' w1 wa0 wa1 wa2 wa3 wa4 w27 STR EL IT0 ITE.
      pose proof (munch_refl ([] : list (Z * Z)) m5) as MU0'. pose proof (wmono_refl psegs m5) as WM0'.
      astep. astep. step. step. step. step. step.
      pose proof SCR5 as SCRY.
      apply (rw_cells_merge psegs _ _ [] [_; _; _; _; _; _; _] [_; _]) in SCRY.
      apply (rw_cells_merge psegs _ _ [_; _] [_] []) in SCRY. cbn [cells_size csize cells_bytes cbytes Nat.add app] in SCRY.
      pose proof (elem_lt _ _ _ _ _ _ _ EL) as IJ2.
      eapply evt_eq; [| eapply (STORE m5 0); [exact SCRY| exact REC4| | lia| exact MI4| exact ST4| exact MU05| exact WM04| exact LS5] ]; [atp_st_eq|].
      right. split; [reflexivity|]. exists (it + 1), j'. split; [reflexivity|]. split; [reflexivity|]. split; [exact EL| lia].
    -
      intros w1 wa0 wa1 wa2 wa3 wa4 w18 w27.
      pose proof (munch_refl ([] : list (Z * Z)) m5) as MU0'. pose proof (wmono_refl psegs m5) as WM0'.
      astep. astep. step. step. astep. step. step. step.
      pose proof SCR5 as SCRY.
      apply (rw_cells_merge psegs _ _ [] [_; _; _; _; _; _; _] [_; _]) in SCRY.
      apply (rw_cells_merge psegs _ _ [_; _] [_] []) in SCRY. cbn [cells_size csize cells_bytes cbytes Nat.add app] in SCRY.
      eapply evt_eq; [| eapply (STORE m5 20); [exact SCRY| exact REC4| left; reflexivity| lia| exact MI4| exact ST4| exact MU05| exact WM04| exact LS5] ]; [atp_st_eq].
  Qed.
End Obj.
End WithCeiling0.
