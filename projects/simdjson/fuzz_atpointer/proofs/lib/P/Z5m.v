(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Lib Require Import Tac Image Z11w Z119 ITree Nodes Decode Arr FP MonadX Z10q.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Malloc Require Import Zei Zf6.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.MallocP Require Import Zhy Zhz Zi1.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Spec Require Import Prelim STree Malloc Monad Stdio StrFun Zpb Z3o Target Prog AtpImpl.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Sj Require Import SjTape Zpk.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.P Require Import Layout Exit Zfr Zq5 Sj_kit Sj_new Zq6 Zpu.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.P Require Import Z9l Z9m Zb0 Z9n Zso Z9o Z44 Z74 Z75 Z66 Z6g Z6f Z6d Z69 Z5r.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.P Require Import Rnd.
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

Lemma find_byte_zlist_Some : forall c (l : list Z) n ix, Forall (fun x => 0 <= x < 256) l -> 0 <= c < 256 ->
  find_byte c (firstn n (map (Z_to_bv 8) l)) = Some ix ->
  (ix < length l)%nat /\ (ix < n)%nat /\ nth ix l 0 = c /\ (forall j, (j < ix)%nat -> nth j l 0 <> c).
Proof.
  intros c l n ix HF Hc H. destruct (find_byte_Some _ _ _ H) as (Hl & (b & Hb & Hbc) & Hmin).
  rewrite length_firstn, length_map in Hl.
  assert (L1 : (ix < length l)%nat) by lia. assert (L2 : (ix < n)%nat) by lia.
  split; [exact L1|]. split; [exact L2|]. split.
  - rewrite nth_error_firstn in Hb. replace (ix <? n)%nat with true in Hb by (symmetry; apply Nat.ltb_lt; lia).
    rewrite nth_error_map, (nth_error_nth' l 0 L1) in Hb. cbn in Hb. injection Hb as EB. rewrite <- EB in Hbc.
    pose proof (Forall_nth_Z _ l ix HF L1) as R. rewrite a_u8_small in Hbc by exact R. exact Hbc.
  - intros j Hj E. apply (Hmin j (Z_to_bv 8 (nth j l 0)) Hj).
    + rewrite nth_error_firstn. replace (j <? n)%nat with true by (symmetry; apply Nat.ltb_lt; lia).
      rewrite nth_error_map. rewrite (nth_error_nth' l 0) by lia. reflexivity.
    + rewrite a_u8_small; [exact E|]. apply Forall_nth_Z; [exact HF| lia].
Qed.

Lemma find_byte_zlist_None : forall c (l : list Z) n, Forall (fun x => 0 <= x < 256) l -> 0 <= c < 256 ->
  find_byte c (firstn n (map (Z_to_bv 8) l)) = None -> forall j, (j < n)%nat -> (j < length l)%nat -> nth j l 0 <> c.
Proof.
  intros c l n HF Hc H j Hj Hl E. apply (find_byte_None _ _ H j (Z_to_bv 8 (nth j l 0))).
  - rewrite nth_error_firstn. replace (j <? n)%nat with true by (symmetry; apply Nat.ltb_lt; lia).
    rewrite nth_error_map. rewrite (nth_error_nth' l 0) by lia. reflexivity.
  - rewrite a_u8_small; [exact E|]. apply Forall_nth_Z; [exact HF| lia].
Qed.

Lemma has_tilde_nth : forall (k : list Z) j, (j < length k)%nat -> nth j k 0 = 126 -> has_tilde k = true.
Proof.
  intros k j Hj E. unfold has_tilde. apply existsb_exists. exists (nth j k 0). split; [apply nth_In; exact Hj| rewrite E; reflexivity].
Qed.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Section Obj.
  Variable E : aenv.
  Hypothesis OK : aenv_ok E.
  Variable d : nat.
  Hypothesis HELEM : atp_elem_stmt E d.
  Hypothesis HM : rmalloc_stmt.
  Hypothesis HF : rfree_stmt.

  Theorem atp_obj : atp_obj_stmt E d.
  Proof.
    unfold atp_obj_stmt. intros until jo.
    intros AI PAT TY NXT CLOSE TILES I0 EN NODE QN NB NO OUT QO OD OB HEAP AUX QD ST LO Q16 ERR MI.
    pose proof OK as OK'. destruct OK' as [WF SBS P1 P1L BT BS BP PP0 [CEIL GLO] B63 [DL DB]].
    pose proof LO as LOF. unfold obj_need, elem_need, ATP_LEAFX, RMALLOC_STACK, GLOBALS_TOP, ATP_OBJ in *.
    assert (LO0 : 0 <= ae_lo E) by (destruct ST as [? _]; assumption).
    pose proof CEIL as CEIL'. unfold OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Spec.Malloc.MCEIL in CEIL; try (pose proof alloc_ceiling_range as CEIL_RANGE__).
    pose proof (tape_wf_root _ _ _ _ _ WF) as [_ NR].
    pose proof (aenv_ranges E s m OK HEAP) as (TR & SR & PR).
    assert (HSN : ae_sn E < 2^56) by (destruct WF as (_ & ? & _); lia).
    assert (ELX : LX_ERRNO = 563116) by reflexivity. rewrite ELX in ERR.
    pose proof (tiles_le _ (field_lt _ _ _ _ (elem_lt _ _ _ _ d)) _ _ _ TILES) as [IE CC].
    pose proof (munch_refl [(q - 224, q); (out, out + 24)]%Z m) as MU. pose proof (wmono_refl psegs m) as WM.
    assert (BLB : forall a, in_block (ae_LB E) a -> a < alloc_ceiling) by (intros a Ha; exact (proj2 (blocks_below _ _ _ _ HEAP Ha))).
    assert (CLI : forall a, 0 <= a < 2^64 -> lx_client (ae_LB E) q [(out, out + 24)] a -> outside [(q - 224, q); (out, out + 24)] a).
    { intros a Ha [HX HC]. cbn [rin_ivs fst snd] in HX. cbn [outside]. split; [| split; [clear - HX; lia| exact I]].
      destruct HC as [HC|[HC|HC]]; [lia| specialize (BLB a HC); lia| lia]. }
    assert (PTRF : Forall (fun c => 0 <= c < 256) ptr).
    { destruct PAT as (pre & Ep & _). rewrite Ep in P1. apply Forall_app in P1. tauto. }
    assert (PL : zlength ptr <= zlength (ae_p1 E)).
    { destruct PAT as (pre & Ep & _). rewrite Ep. unfold zlength. rewrite length_app. lia. }
    assert (PP : 0 <= P /\ P + zlength ptr = ae_PTR E + zlength (ae_p1 E)).
    { destruct PAT as (pre & Ep & EP). rewrite EP, Ep. unfold zlength. rewrite length_app. lia. }
    assert (ZLR : 0 <= zlength ptr < 2^26) by (unfold zlength in *; lia).
    hide AI.
    unfold implM. iprefix.

    step. carve_frame 224%nat ST.
    apply (rw_cells_split_CB psegs _ _ [] 224 junk [] [72;24;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8]%nat) in FR; [|reflexivity]. cbn [mk_CB_cells app] in FR.
    do 13 step. step. step. name_mem m1.
    apply (proj1 (rw_cells_app _ _ [_] _)) in FR. destruct FR as [SCR FR]. cbn [cells_size csize Nat.add] in FR.
    apply (proj1 (rw_cells_app _ _ [_] _)) in FR. destruct FR as [STRS FR]. cbn [cells_size csize Nat.add] in FR.
    apply (proj1 (rw_cells_app _ _ [_; _; _] _)) in FR. destruct FR as [REC FRB]. cbn [cells_size csize Nat.add] in FRB.
    replace (q + -224 + Z.of_nat 72) with (q + -152) in STRS by lia.
    replace (q + -224 + Z.of_nat 72 + Z.of_nat 24) with (q + -128) in REC by lia.
    lazymatch type of FRB with rw_cells _ _ ?a _ => replace a with (q + -104) in FRB by lia end.
    unhide AI.
    assert (AI1 : AINV E m1).
    { eapply AINV_agree; [exact AI| eapply agree_on_of_munch; [exact MU| exact WM]| | | exact OK].
      - intros a Ha. pose proof (BLB a Ha). cbn [outside]. lia.
      - intros a Ha. cbn [outside]. lia. }
    hide AI. pose proof AI1 as (TAPEB & SBUFB & PTRB & DOCC). hide AI1.
    assert (PTRB1 : bytes_at psegs m1 P (map (Z_to_bv 8) ptr)).
    { destruct PAT as (pre & Ep & EP). pose proof PTRB as X. rewrite Ep, map_app in X.
      apply (bytes_at_skipn _ _ _ (length (map (Z_to_bv 8) pre))) in X; [| rewrite length_app; lia].
      rewrite skipn_app, skipn_all, Nat.sub_diag, length_map in X. cbn [skipn] in X. rewrite EP. unfold zlength. exact X. }
    assert (HEAP1 : RHEAP s (ae_LB E) m1).
    { eapply LH_frame; [exact HEAP| exact MU| exact WM|]. constructor; [apply W_ok_stack; cbn; lia|]. constructor; [apply W_ok_stack; cbn; lia| constructor]. }
    assert (AUX1 : rauxv_ok m1 (ae_B E)).
    { eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]. constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
    assert (PRES1 : lx_pres (ae_LB E) q [(out, out + 24)] m m1) by (eapply lx_pres_of_munch; [exact MU| exact WM| exact CLI]).

    apply (rw_cells_split_CB psegs _ _ [] 24 jo [] [8;8;8]%nat) in OUT; [|reflexivity]. cbn [mk_CB_cells app] in OUT.
    assert (EXIT : forall (m2 : mem) (cs : list cell) (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
      rw_cells psegs m2 out cs -> cells_size cs = 24%nat ->
      rw_cells psegs m2 (q + -224) [CB 72 (firstn 72 junk)] -> rw_cells psegs m2 (q + -152) [CB 24 (firstn 24 (skipn 72 junk))] ->
      rw_cells psegs m2 (q + -128) [CB 8 (firstn 8 (skipn 24 (skipn 72 junk))); CB 8 (firstn 8 (skipn 8 (skipn 24 (skipn 72 junk)))); CB 8 (firstn 8 (skipn 8 (skipn 8 (skipn 24 (skipn 72 junk)))))] ->
      rw_cells psegs m2 (q + -104) (obj_saved ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
      mem_inv psegs m2 -> stk psegs m2 (ae_lo E) (q + -224) -> rw_cells psegs m2 LX_ERRNO [C4 errv] ->
      munch [(q - 224, q); (out, out + 24)] m m2 -> wmono psegs m m2 ->
      evt psegs (fun ms' => impl psegs (at_node psegs) (atp_walk lops (ptr_segs ptr) s)
                  (epost (fun p => hpost ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s (ae_lo E) (ae_B E) (lvl_R E q out m) (snd p))) ms')
        (MS (mkR x1 (Z_to_bv 64 (q + -224)) gp (Z_to_bv 64 RATP) x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x28694) fc None m2 (seg_rom psegs))).
    { intros m2 cs x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
             OUT2 CS SCR2 STRS2 REC2 FRB2 MI2 ST2 ERR2 MU2 WM2. unfold obj_saved in FRB2.
      stop_now.
      pose proof (rw_cells_join _ _ _ _ _ SCR2 STRS2 ltac:(cbn [cells_size csize Nat.add]; lia)) as J1. cbn [app] in J1.
      pose proof (rw_cells_join _ _ _ _ _ J1 REC2 ltac:(cbn [cells_size csize Nat.add]; lia)) as J2. cbn [app] in J2.
      destruct (rw_cells_forget _ _ _ _ J2) as [ja3 FRA]. cbn [cells_size csize Nat.add] in FRA.
      eapply (obj_epi E); [exact FRA| unfold obj_saved; exact FRB2| exact MI2| exact ST2| lia| exists errv; exact ERR2| | reflexivity| reflexivity| | |].
      - eapply rauxv_ok_frame; [exact AUX| exact MU2| exact WM2|]. constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor].
      - eapply LH_frame; [exact HEAP| exact MU2| exact WM2|]. constructor; [apply W_ok_stack; cbn; lia|]. constructor; [apply W_ok_stack; cbn; lia| constructor].
      - eapply lx_pres_of_munch; [exact MU2| exact WM2| exact CLI].
      - destruct (rw_cells_forget _ _ _ _ OUT2) as [j' O']. rewrite CS in O'. exists j'. exact O'. }

    step. if_cases K0; zify_cond K0.
    {
      step. step. hstep. hstep. hstep. step. name_mem m2.
      eapply EXIT; [exact OUT| reflexivity| exact SCR| exact STRS| exact REC| exact FRB| exact MI| exact ST| exact ERR| exact MU| exact WM]. }
    destruct ptr as [|c0 rest0]; [exfalso; apply K0; reflexivity|].
    assert (C0R : 0 <= c0 < 256) by (inversion PTRF; assumption).
    assert (KEYF : Forall (fun c => 0 <= c < 256) rest0) by (inversion PTRF; assumption).
    rewrite zlength_cons in *. pose proof (zlength_nonneg rest0) as ZL0N.
    pose proof (zbytes_read1 m1 P (c0 :: rest0) 0 PTRB1 ltac:(rewrite zlength_cons; lia)) as RD0. change (nth (Z.to_nat 0) (c0 :: rest0) 0) with c0 in RD0. rewrite Z.add_0_r in RD0.

    astep. astep. step. if_cases K1; zify_cond K1.
    {
      astep. hstep. hstep. hstep. step. name_mem m2.
      eapply EXIT; [exact OUT| reflexivity| exact SCR| exact STRS| exact REC| exact FRB| exact MI| exact ST| exact ERR| exact MU| exact WM]. }
    subst c0.
    assert (RB1 : bytes_at psegs m1 (P + 1) (map (Z_to_bv 8) rest0)) by (exact (bytes_at_skipn _ _ _ 1 PTRB1 ltac:(cbn; lia))).
    set (L0 := zlength rest0) in *.
    assert (P1R : P + 1 + L0 <= alloc_ceiling /\ ae_PTR E <= P + 1).
    { destruct BP as [E0p|BPx]; [exfalso; rewrite E0p in PL; unfold zlength in PL; cbn in PL; lia|].
      pose proof (in_blocks_range _ _ _ _ _ HEAP BPx ltac:(unfold zlength; lia)). destruct PAT as (pre & Ep & EP). rewrite EP. unfold zlength in *. lia. }

    assert (AT2C : forall (mX : mem) (sl L : Z) (k : list Z) (REST : list (list Z)) (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
      rw_cells psegs mX (q + -224) [CB 72 (firstn 72 junk)] -> rw_cells psegs mX (q + -152) [CB 24 (firstn 24 (skipn 72 junk))] ->
      rw_cells psegs mX (q + -128) [CB 8 (firstn 8 (skipn 24 (skipn 72 junk))); CB 8 (firstn 8 (skipn 8 (skipn 24 (skipn 72 junk)))); CB 8 (firstn 8 (skipn 8 (skipn 8 (skipn 24 (skipn 72 junk)))))] ->
      rw_cells psegs mX (q + -104) (obj_saved ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
      rw_cells psegs mX out [CB 8 (firstn 8 jo); CB 8 (firstn 8 (skipn 8 jo)); CB 8 (firstn 8 (skipn 8 (skipn 8 jo)))] ->
      rw_cells psegs mX node [C8 (Z_to_bv 64 (ae_DOC E)); C8 (Z_to_bv 64 i)] -> bytes_at psegs mX (P + 1) (map (Z_to_bv 8) rest0) ->
      rw_cells psegs mX LX_ERRNO [C4 errv] -> mem_inv psegs mX -> stk psegs mX (ae_lo E) (q + -224) ->
      munch [(q - 224, q); (out, out + 24)] m mX -> wmono psegs m mX ->
      ptr_segs (47 :: rest0) = k :: REST -> k = firstn (Z.to_nat L) rest0 -> 0 <= L <= L0 ->
      ((sl = 18446744073709551615 /\ L = L0) \/ (0 <= sl < L0 /\ L = sl)) ->
      ((sl = 18446744073709551615 /\ REST = []) \/
       (0 <= sl < L0 /\ exists r, REST = ptr_segs (47 :: r) /\ ptr_at E (P + 1 + sl) (47 :: r) /\ zlength (47 :: r) = L0 - sl)) ->
      evt psegs (fun ms' => impl psegs (at_node psegs) (atp_walk lops (ptr_segs (47 :: rest0)) s)
                  (epost (fun p => hpost ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s (ae_lo E) (ae_B E) (lvl_R E q out m) (snd p))) ms')
        (MS (mkR y1 (Z_to_bv 64 (q + -224)) gp (Z_to_bv 64 RATP) y5 y6 y7 s0 (Z_to_bv 64 (P + 1)) y10 y11 y12 y13 y14 y15 y16 y17
                 (Z_to_bv 64 sl) s3 (Z_to_bv 64 node) s5 s6 s7 s8 s9 (Z_to_bv 64 out) (Z_to_bv 64 L0) y28 y29 y30 y31)
            F (Z_to_bv 64 0x28128) fc None mX (seg_rom psegs))).
    { clear SCR STRS REC FRB OUT NODE RB1 ERR MI ST.
      intros mX sl L k REST y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 SCR STRS REC FRB OUT NODE RB1 ERR MI ST MU1 WM1 SEGS EK LL SLC RC.
      unfold obj_saved in FRB. rewrite ELX in ERR. rewrite SEGS.

      assert (AT38 : forall y21 : word, y21 = Z_to_bv 64 L ->
        evt psegs (fun ms' => impl psegs (at_node psegs) (atp_walk lops (k :: REST) s)
                    (epost (fun p => hpost ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s (ae_lo E) (ae_B E) (lvl_R E q out m) (snd p))) ms')
          (MS (mkR y1 (Z_to_bv 64 (q + -224)) gp (Z_to_bv 64 RATP) y5 y6 y7 s0 (Z_to_bv 64 (P + 1)) y10 y11 y12 y13 y14 y15 y16 y17
                   (Z_to_bv 64 sl) s3 (Z_to_bv 64 node) y21 s6 s7 s8 s9 (Z_to_bv 64 out) (Z_to_bv 64 L0) y28 y29 y30 y31)
              F (Z_to_bv 64 0x28134) fc None mX (seg_rom psegs))).
      2:{ step. step. if_cases KB; zify_cond KB; rewrite ?land64_mod in KB.
          - apply AT38. f_equal. destruct SLC as [[A1 A2]|[A1 A2]]; lia.
          - step. apply AT38. f_equal. destruct SLC as [[A1 A2]|[A1 A2]]; lia. }
      intros y21 ->.

      hide RB1. pose proof (munch_refl [(q - 224, q); (out, out + 24)]%Z mX) as MUX. pose proof (wmono_refl psegs mX) as WMX.
      astep. hstep. hstep. hstep. name_mem m2.
      assert (RB2 : bytes_at psegs m2 (P + 1) (map (Z_to_bv 8) rest0)).
      { unhide RB1. eapply bytes_at_agree; [eapply agree_on_of_munch; [exact MUX| exact WMX]| exact RB1|]. intros a Ha. rewrite length_map in Ha.
        unfold L0, zlength in *. cbn [outside]. lia. }
      lazymatch goal with H : rw_cells psegs m2 (q + -128) _ |- _ => rename H into REC2 end.
      lazymatch goal with H : rw_cells psegs m2 out _ |- _ => rename H into OUT2 end.
      destruct (rw_cells_forget _ _ _ _ OUT2) as [jo2 OUT2']. cbn [cells_size csize Nat.add] in OUT2'. clear OUT2.

      assert (NOESC : forall (mY : mem) (xja xjs xj4 : list byte) (z1 z5 z6 z7 z8 z10 z11 z12 z13 z14 z15 z16 z17 z19 z22 z23 z24 z25 z28 z29 z30 z31 : word),
        rw_cells psegs mY (q + -224) [CB 72 xja] -> rw_cells psegs mY (q + -152) [CB 24 xjs] ->
        rw_cells psegs mY (q + -128) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 12); CB 4 xj4] ->
        rw_cells psegs mY (q + -104) (obj_saved ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) -> rw_cells psegs mY out [CB 24 jo2] ->
        rw_cells psegs mY node [C8 (Z_to_bv 64 (ae_DOC E)); C8 (Z_to_bv 64 i)] -> bytes_at psegs mY (P + 1) (map (Z_to_bv 8) rest0) ->
        munch [(q - 224, q); (out, out + 24)] m mY -> wmono psegs m mY -> stk psegs mY (ae_lo E) (q + -224) ->
        rw_cells psegs mY LX_ERRNO [C4 errv] -> mem_inv psegs mY ->
        evt psegs (fun ms' => impl psegs (at_node psegs) (atp_walk lops (k :: REST) s)
                    (epost (fun p => hpost ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s (ae_lo E) (ae_B E) (lvl_R E q out m) (snd p))) ms')
          (MS (mkR z1 (Z_to_bv 64 (q + -224)) gp (Z_to_bv 64 RATP) z5 z6 z7 z8 (Z_to_bv 64 (P + 1)) z10 z11 z12 z13 z14 z15 z16 z17
                   (Z_to_bv 64 sl) z19 (Z_to_bv 64 node) (Z_to_bv 64 L) z22 z23 z24 z25 (Z_to_bv 64 out) (Z_to_bv 64 L0) z28 z29 z30 z31)
              F (Z_to_bv 64 0x2818c) fc None mY (seg_rom psegs))).
      { intros mY xja xjs xj4 z1 z5 z6 z7 z8 z10 z11 z12 z13 z14 z15 z16 z17 z19 z22 z23 z24 z25 z28 z29 z30 z31 XSCR XSTRS XREC XFRB XOUT XNODE XRB XMU XWM XST XERR XMI.
        assert (XAI : AINV E mY).
        { unhide AI. eapply AINV_agree; [exact AI| eapply agree_on_of_munch; [exact XMU| exact XWM]| | | exact OK].
          - intros a Ha. pose proof (BLB a Ha). cbn [outside]. lia.
          - intros a Ha. cbn [outside]. lia. }
        assert (XHEAP : RHEAP s (ae_LB E) mY).
        { eapply LH_frame; [exact HEAP| exact XMU| exact XWM|]. constructor; [apply W_ok_stack; cbn; lia|]. constructor; [apply W_ok_stack; cbn; lia| constructor]. }
        assert (XAUX : rauxv_ok mY (ae_B E)).
        { eapply rauxv_ok_frame; [exact AUX| exact XMU| exact XWM|]. constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
        assert (XPRES : lx_pres (ae_LB E) q [(out, out + 24)] m mY).
        { eapply lx_pres_of_munch; [exact XMU| exact XWM| exact CLI]. }
        apply evt_done.
        eapply (obj_noesc E OK d HELEM ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s out node i e c P L0 L sl rest0 k REST m mY);
          [exact XSCR| exact XSTRS| exact XREC| exact XFRB| exact XOUT| exact QO| exact OB| exact QD| exact OD| exact XAI| exact XNODE| exact QN| exact NB
          | exact TY| exact NXT| exact TILES| exact I0| exact EN| exact XRB| reflexivity| exact EK| exact LL| unfold L0; lia| lia| lia| exact RC
          | exact XHEAP| exact XAUX| exact XST| exact LOF| exact Q16| exists errv; exact XERR| exact XMI| exact XPRES]. }

      step. if_cases KL0; zify_cond KL0.
      { eapply NOESC; [exact SCR| exact STRS| exact REC2| exact FRB| exact OUT2'| exact NODE| exact RB2| exact MU1| exact WM1| exact ST| rewrite ELX; exact ERR| exact MI]. }

      astep. step. step. step.
      call memchr_spec.
      1:{ rewrite unsigned_lit by lia. exact RB2. }
      1:{ rewrite !unsigned_lit by lia. unfold memchr_ok. change (126 mod 256) with 126.
          destruct (find_byte 126 (firstn (Z.to_nat L) (map (Z_to_bv 8) rest0))); rewrite length_map; [left|]; unfold L0, zlength in *; lia. }
      1:{ assumption. }
      rewrite !unsigned_lit by lia. change (126 mod 256) with 126. unfold memchr_res. name_mem m3.
      lazymatch goal with H : mem_inv psegs m3 |- _ => rename H into MI3 end.
      destruct (find_byte 126 (firstn (Z.to_nat L) (map (Z_to_bv 8) rest0))) as [ix|] eqn:FB.
      2:{
        step. if_cases K2; zify_cond K2; [| exfalso; apply K2; reflexivity].
        eapply NOESC; [exact SCR| exact STRS| exact REC2| exact FRB| exact OUT2'| exact NODE| exact RB2| exact MU1| exact WM1| exact ST| rewrite ELX; exact ERR| exact MI3]. }
      pose proof (find_byte_zlist_Some 126 rest0 (Z.to_nat L) ix KEYF ltac:(lia) FB) as (IX1 & IX2 & IXC & _).
      assert (HT : has_tilde k = true).
      { rewrite EK. apply (has_tilde_nth _ ix); [rewrite firstn_length_le by (unfold L0, zlength in *; lia); exact IX2|].
        rewrite <- (firstn_skipn (Z.to_nat L) rest0) in IXC. rewrite app_nth1 in IXC by (rewrite firstn_length_le by (unfold L0, zlength in *; lia); exact IX2). exact IXC. }

      step. if_cases K2; zify_cond K2; [exfalso; lia|]. astep. astep. step. if_cases K3; zify_cond K3.
      { eapply NOESC; [exact SCR| exact STRS| exact REC2| exact FRB| exact OUT2'| exact NODE| exact RB2| exact MU1| exact WM1| exact ST| rewrite ELX; exact ERR| exact MI3]. }

      astep. step. if_cases KD; zify_cond KD; rewrite ?land64_mod in KD; [exfalso; lia|]. astep.
      hide RB2. apply (rw_cells_split_CB psegs _ _ [] 72 _ [] [8;8;8;8;8;8;8;8;8]%nat) in SCR; [|reflexivity]. cbn [mk_CB_cells app] in SCR.
      hstep. name_mem m4.
      lazymatch goal with H : rw_cells psegs m4 (q + -224) _ |- _ => rename H into SCR4 end.
      lazymatch goal with H : rw_cells psegs m4 out _ |- _ => rename H into OUT4 end.
      assert (AI4 : AINV E m4).
      { unhide AI. eapply AINV_agree; [exact AI| eapply agree_on_of_munch; [exact MU1| exact WM1]| | | exact OK].
        - intros a Ha. pose proof (BLB a Ha). cbn [outside]. lia.
        - intros a Ha. cbn [outside]. lia. }
      assert (RB4 : bytes_at psegs m4 (P + 1) (map (Z_to_bv 8) rest0)).
      { unhide RB1. eapply bytes_at_agree; [eapply agree_on_of_munch; [exact MUX| exact WMX]| exact RB1|]. intros a Ha. rewrite length_map in Ha.
        unfold L0, zlength in *. cbn [outside]. lia. }
      assert (HEAP4 : RHEAP s (ae_LB E) m4).
      { eapply LH_frame; [exact HEAP| exact MU1| exact WM1|]. constructor; [apply W_ok_stack; cbn; lia|]. constructor; [apply W_ok_stack; cbn; lia| constructor]. }
      assert (AUX4 : rauxv_ok m4 (ae_B E)).
      { eapply rauxv_ok_frame; [exact AUX| exact MU1| exact WM1|]. constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
      assert (PRES4 : lx_pres (ae_LB E) q [(out, out + 24)] m m4).
      { eapply lx_pres_of_munch; [exact MU1| exact WM1| exact CLI]. }
      step. if_cases KH; zify_cond KH.
      all: replace (P + 1 + Z.of_nat ix + - (P + 1)) with (Z.of_nat ix) by lia.
      - apply evt_done. eapply (obj_esc_heap E OK d HELEM HM HF) with (e0 := Z.of_nat ix); [| lia].
        unfold esc_pre.
        split; [exact SCR4|]. split; [exact STRS|]. split; [exact REC2|]. split; [unfold obj_saved; exact FRB|]. split; [exact OUT4|].
        split; [exact QO|]. split; [exact OB|]. split; [exact QD|]. split; [exact OD|]. split; [exact AI4|]. split; [exact NODE|]. split; [exact QN|]. split; [exact NB|].
        split; [exact TY|]. split; [exact NXT|]. split; [exact TILES|]. split; [exact I0|]. split; [exact EN|]. split; [exact RB4|]. split; [exact KEYF|].
        split; [reflexivity|]. split; [exact EK|]. split; [lia|]. split; [unfold L0; lia|]. split; [lia|]. split; [lia|]. split; [exact PAT|]. split; [exact HT|].
        split; [exact RC|]. split; [exact HEAP4|]. split; [exact AUX4|]. split; [exact ST|]. split; [exact LOF|]. split; [exact Q16|].
        split; [rewrite ELX; exact ERR|]. split; [exact MI3| exact PRES4].
      - apply evt_done. eapply (obj_esc_sso E OK d HELEM) with (e0 := Z.of_nat ix); [| lia].
        unfold esc_pre.
        split; [exact SCR4|]. split; [exact STRS|]. split; [exact REC2|]. split; [unfold obj_saved; exact FRB|]. split; [exact OUT4|].
        split; [exact QO|]. split; [exact OB|]. split; [exact QD|]. split; [exact OD|]. split; [exact AI4|]. split; [exact NODE|]. split; [exact QN|]. split; [exact NB|].
        split; [exact TY|]. split; [exact NXT|]. split; [exact TILES|]. split; [exact I0|]. split; [exact EN|]. split; [exact RB4|]. split; [exact KEYF|].
        split; [reflexivity|]. split; [exact EK|]. split; [lia|]. split; [unfold L0; lia|]. split; [lia|]. split; [lia|]. split; [exact PAT|]. split; [exact HT|].
        split; [exact RC|]. split; [exact HEAP4|]. split; [exact AUX4|]. split; [exact ST|]. split; [exact LOF|]. split; [exact Q16|].
        split; [rewrite ELX; exact ERR|]. split; [exact MI3| exact PRES4]. }

    astep. astep. step. if_cases KZ; zify_cond KZ; rewrite ?land64_mod in KZ.
    {
      assert (R0 : rest0 = []).
      { destruct rest0 as [|r1 rr]; [reflexivity| exfalso]. unfold L0 in KZ. rewrite zlength_cons in KZ. pose proof (zlength_nonneg rr). lia. }
      astep.
      eapply evt_eq; [| eapply (AT2C m1 18446744073709551615 0 [] []);
        [exact SCR| exact STRS| exact REC| exact FRB| exact OUT| exact NODE| exact RB1| rewrite <- ELX in ERR; exact ERR| exact MI| exact ST| exact MU| exact WM
        | rewrite R0; reflexivity| reflexivity| unfold L0; lia| left; split; [reflexivity| unfold L0; rewrite R0; reflexivity]| left; split; reflexivity] ]; [atp_st_eq]. }

    astep. step. step. step.
    call memchr_spec.
    1:{ rewrite unsigned_lit by lia. exact RB1. }
    1:{ rewrite !unsigned_lit by lia. unfold memchr_ok. change (47 mod 256) with 47.
        destruct (find_byte 47 (firstn (Z.to_nat L0) (map (Z_to_bv 8) rest0))); rewrite length_map; [left|]; unfold L0, zlength in *; lia. }
    1:{ assumption. }
    rewrite !unsigned_lit by lia. change (47 mod 256) with 47. unfold memchr_res. name_mem m2.
    lazymatch goal with H : mem_inv psegs m2 |- _ => rename H into MI2 end.
    lazymatch goal with H : bytes_at psegs m2 (P + 1) _ |- _ => rename H into RB2 end.

    destruct (find_byte 47 (firstn (Z.to_nat L0) (map (Z_to_bv 8) rest0))) as [ix|] eqn:FB.
    - pose proof (find_byte_zlist_Some 47 rest0 (Z.to_nat L0) ix KEYF ltac:(lia) FB) as (IX1 & IX2 & IXC & IXN).
      astep. astep. astep. astep. rewrite find_or_found by lia. step.
      destruct (seg_split rest0 ix ltac:(lia) IXN) as [E1 E2]. rewrite (skipn_cons_nth _ _ IX1), IXC in E1, E2.
      set (r := skipn (S ix) rest0) in *.
      change (take_seg (47 :: r)) with (@nil Z) in E1. change (drop_seg (47 :: r)) with (47 :: r) in E2. rewrite app_nil_r in E1.
      assert (PAT2 : ptr_at E (P + 1 + Z.of_nat ix) (47 :: r)).
      { pose proof (ptr_at_skip E P (47 :: rest0) (S ix) PAT ltac:(cbn [length]; lia)) as X.
        change (skipn (S ix) (47 :: rest0)) with (skipn ix rest0) in X. rewrite (skipn_cons_nth _ _ IX1), IXC in X. fold r in X.
        replace (P + Z.of_nat (S ix)) with (P + 1 + Z.of_nat ix) in X by lia. exact X. }
      assert (ZR : zlength (47 :: r) = L0 - Z.of_nat ix).
      { subst r. rewrite zlength_cons, zlength_skipn by lia. unfold L0. lia. }
      eapply evt_eq; [| eapply (AT2C m2 (Z.of_nat ix) (Z.of_nat ix) (firstn ix rest0) (ptr_segs (47 :: r)));
        [exact SCR| exact STRS| exact REC| exact FRB| exact OUT| exact NODE| exact RB2| rewrite <- ELX in ERR; exact ERR| exact MI2| exact ST| exact MU| exact WM
        | rewrite ptr_segs_unfold, E1, E2; reflexivity| rewrite Nat2Z.id; reflexivity| unfold L0, zlength in *; lia| right; unfold L0, zlength in *; lia
        | right; split; [unfold L0, zlength in *; lia| exists r; split; [reflexivity| split; [exact PAT2| exact ZR]]]] ]; [atp_st_eq].
    - pose proof (find_byte_zlist_None 47 rest0 (Z.to_nat L0) KEYF ltac:(lia) FB) as IXN.
      astep. astep. astep. astep. rewrite find_or_npos by (rewrite land64_mod; lia). step.
      destruct (seg_split rest0 (length rest0) ltac:(lia) ltac:(intros j Hj; apply IXN; unfold L0, zlength; lia)) as [E1 E2].
      rewrite skipn_all in E1, E2. cbn [take_seg drop_seg] in E1, E2. rewrite app_nil_r, firstn_all in E1.
      eapply evt_eq; [| eapply (AT2C m2 18446744073709551615 L0 rest0 []);
        [exact SCR| exact STRS| exact REC| exact FRB| exact OUT| exact NODE| exact RB2| rewrite <- ELX in ERR; exact ERR| exact MI2| exact ST| exact MU| exact WM
        | rewrite ptr_segs_unfold, E1, E2; reflexivity| unfold L0, zlength; rewrite Nat2Z.id, firstn_all; reflexivity| unfold L0; lia| left; split; reflexivity| left; split; reflexivity] ];
        [atp_st_eq].
  Qed.
End Obj.
End WithCeiling0.
