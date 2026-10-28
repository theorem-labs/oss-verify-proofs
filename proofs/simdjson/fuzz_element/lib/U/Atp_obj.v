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
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import F_memchr F_memcmp F_strlen F_memcpy F_memmove_t2 Atp_defs Atp_kitu Atp_arrl Atp_str Atp_strr Atp_objk Atp_obju Atp_objt Atp_objs Atp_obje Atp_objh.
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
    intros AI PAT TY NXT CLOSE TILES I0 EN ELN NODE QN NB NO OUT QO OD OB HEAP AUX QD ST LO Q16 ERR MI.
    pose proof OK as OK'. destruct OK' as [WF SBS P1 P1L BT BS BP PP0 [CEIL GLO] B63 [DL DB] [AL8D AL8T]].
    pose proof LO as LOF. unfold obj_need, elem_need, ATP_LEAFX, RMALLOC_STACK, GLOBALS_TOP, ATP_OBJ in *.
    assert (LO0 : 0 <= ae_lo E) by (destruct ST as [? _]; assumption).
    pose proof CEIL as CEIL'. unfold OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in CEIL; try (pose proof alloc_ceiling_range as CEIL_RANGE__).
    pose proof (tape_wf_root _ _ _ _ _ WF) as [_ NR].
    pose proof (aenv_ranges E s m OK HEAP) as (TR & SR & PR).
    assert (HSN : ae_sn E < 2^56) by (destruct WF as (_ & ? & _); lia).
    assert (ELX : LX_ERRNO = 980196) by reflexivity. rewrite ELX in ERR.
    pose proof (tiles_le _ (field_lt _ _ _ _ (elem_lt _ _ _ _ d)) _ _ _ TILES) as [IE CC].
    pose proof (munch_refl [(q - 336, q); (out, out + 24)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
    assert (BLB : forall a, in_block (ae_LB E) a -> a < alloc_ceiling) by (intros a Ha; exact (proj2 (blocks_below _ _ _ _ HEAP Ha))).
    assert (CLI : forall a, 0 <= a < 2^64 -> lx_client (ae_LB E) q [(out, out + 24)] a -> outside [(q - 336, q); (out, out + 24)] a).
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

    step. carve_frame 208%nat ST.
    apply (rw_cells_split_CB usegs _ _ [] 208 junk [] [32;24;8;8;4;4;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8]%nat) in FR; [|reflexivity]. cbn [mk_CB_cells app] in FR.
    do 12 step. step. step. hstep. hstep. name_mem m1.
    apply (proj1 (rw_cells_app _ _ [_] _)) in FR. destruct FR as [SCR FR]. cbn [cells_size csize Nat.add] in FR.
    apply (proj1 (rw_cells_app _ _ [_] _)) in FR. destruct FR as [STRS FR]. cbn [cells_size csize Nat.add] in FR.
    apply (proj1 (rw_cells_app _ _ [_; _; _; _] _)) in FR. destruct FR as [REC FR]. cbn [cells_size csize Nat.add] in FR.
    apply (proj1 (rw_cells_app _ _ [_; _] _)) in FR. destruct FR as [FRK FR]. cbn [cells_size csize Nat.add] in FR.
    apply (proj1 (rw_cells_app _ _ [_; _] _)) in FR. destruct FR as [FRSV FRB]. cbn [cells_size csize Nat.add] in FRB.
    replace (q + -208 + Z.of_nat 32) with (q + -176) in STRS by lia.
    lazymatch type of REC with rw_cells _ _ ?a _ => replace a with (q + -152) in REC by lia end.
    lazymatch type of FRK with rw_cells _ _ ?a _ => replace a with (q + -128) in FRK by lia end.
    lazymatch type of FRSV with rw_cells _ _ ?a _ => replace a with (q + -112) in FRSV by lia end.
    lazymatch type of FRB with rw_cells _ _ ?a _ => replace a with (q + -96) in FRB by lia end.
    unhide AI. pose proof AI as (_ & _ & PTRB & _). hide AI. hide PTRB.
    assert (HEAP1 : RHEAP s (ae_LB E) m1).
    { eapply LH_frame; [exact HEAP| exact MU| exact WM|]. constructor; [apply W_ok_stack; cbn; lia|]. constructor; [apply W_ok_stack; cbn; lia| constructor]. }
    assert (AUX1 : rauxv_ok m1 (ae_B E)).
    { eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]. constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }

    apply (rw_cells_split_CB usegs _ _ [] 24 jo [] [8;8;4;4]%nat) in OUT; [|reflexivity]. cbn [mk_CB_cells app] in OUT.
    assert (EXIT : forall (m2 : mem) (r0 : word) (j code : Z) (ja js c1 c2 c3 c4 k1 k2 jn : list byte) (pv lv : word)
                          (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 : word),
      rw_cells usegs m2 out [C8 r0; C8 (Z_to_bv 64 j); C4 (Z_to_bv 64 code); CB 4 jn] -> 0 <= code < 64 ->
      (code = 0 -> r0 = Z_to_bv 64 (ae_DOC E) /\ 0 <= j /\ exists dd jj, elem (ae_T E) (ae_S E) (ae_sn E) ck_any dd j jj) ->
      rw_cells usegs m2 (q + -208) [CB 32 ja] -> rw_cells usegs m2 (q + -176) [CB 24 js] ->
      rw_cells usegs m2 (q + -152) [CB 8 c1; CB 8 c2; CB 4 c3; CB 4 c4] -> rw_cells usegs m2 (q + -128) [CB 8 k1; CB 8 k2] ->
      rw_cells usegs m2 (q + -112) [C8 pv; C8 lv] ->
      rw_cells usegs m2 (q + -96) (obj_savedU ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10) ->
      mem_inv usegs m2 -> stk usegs m2 (ae_lo E) (q + -208) -> rw_cells usegs m2 LX_ERRNO [C4 errv] ->
      munch [(q - 336, q); (out, out + 24)] m m2 -> wmono usegs m m2 ->
      evt usegs (hpost ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s (ae_lo E) (ae_B E) (lvl_R E q out m) s)
        (MS (mkR x1 (Z_to_bv 64 (q + -208)) gp (Z_to_bv 64 RATP) x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0x3f398) fc None m2 (seg_rom usegs))).
    { intros m2 r0 j code ja js c1 c2 c3 c4 k1 k2 jn pv lv x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31
             OUT2 CR CIMP SCR2 STRS2 REC2 FRK2 FRSV2 FRB2 MI2 ST2 ERR2 MU2 WM2.
      destruct (frame112 m2 q _ _ _ _ _ _ SCR2 STRS2 REC2 eq_refl FRK2 eq_refl FRSV2) as [ja3 FRA].
      eapply (obj_epi E); [exact FRA| exact FRB2| exact MI2| exact ST2| lia| exists errv; exact ERR2| | reflexivity| reflexivity| | |].
      - eapply rauxv_ok_frame; [exact AUX| exact MU2| exact WM2|]. constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor].
      - eapply LH_frame; [exact HEAP| exact MU2| exact WM2|]. constructor; [apply W_ok_stack; cbn; lia|]. constructor; [apply W_ok_stack; cbn; lia| constructor].
      - eapply lx_pres_of_munch; [exact MU2| exact WM2| exact CLI].
      - exists r0, j, code, jn. split; [exact OUT2|]. split; [exact CR| exact CIMP]. }

    step. if_cases K0; zify_cond K0.
    {
      step. if_lia. step. step. hstep. hstep. hstep. step. name_mem m2.
      lazymatch goal with H : rw_cells usegs m2 out _ |- _ => rename H into OUT2 end.
      lazymatch goal with H : mem_inv usegs m2 |- _ => rename H into MI2 end.
      lazymatch goal with H : stk usegs m2 _ _ |- _ => rename H into ST2 end.
      stop_now.
      eapply EXIT; [exact OUT2| lia| intros _; split; [reflexivity| split; [exact I0| exact ELN]]| exact SCR| exact STRS| exact REC| exact FRK| exact FRSV| exact FRB
                   | exact MI2| exact ST2| exact ERR| exact MU| exact WM]. }
    destruct ptr as [|c0 rest0]; [exfalso; apply K0; reflexivity|].
    assert (C0R : 0 <= c0 < 256) by (inversion PTRF; assumption).
    assert (KEYF : Forall (fun c => 0 <= c < 256) rest0) by (inversion PTRF; assumption).
    rewrite zlength_cons in *. pose proof (zlength_nonneg rest0) as ZL0N.
    destruct BP as [E0p|BPx]; [exfalso; rewrite E0p in PL; unfold zlength in PL; cbn in PL; lia|].
    pose proof (in_blocks_range _ _ _ _ _ HEAP BPx ltac:(unfold zlength; lia)) as PRANGE.
    assert (PTRB0 : bytes_at usegs m P (map (Z_to_bv 8) (c0 :: rest0))).
    { unhide PTRB. destruct PAT as (pre & Ep & EP). pose proof PTRB as X. rewrite Ep, map_app in X.
      apply (bytes_at_skipn _ _ _ (length (map (Z_to_bv 8) pre))) in X; [| rewrite length_app; lia].
      rewrite skipn_app, skipn_all, Nat.sub_diag, length_map in X. cbn [skipn] in X. rewrite EP. unfold zlength. exact X. }
    clear PTRB.
    assert (PTRB1 : bytes_at usegs m1 P (map (Z_to_bv 8) (c0 :: rest0))).
    { eapply bytes_at_agree; [eapply agree_on_of_munch; [exact MU| exact WM]| exact PTRB0|]. intros a Ha. rewrite length_map in Ha. cbn [length] in Ha.
      unfold zlength in *. cbn [length] in PP. cbn [outside]. lia. }
    pose proof (zbytes_read1 m1 P (c0 :: rest0) 0 PTRB1 ltac:(rewrite zlength_cons; lia)) as RD0. change (nth (Z.to_nat 0) (c0 :: rest0) 0) with c0 in RD0. rewrite Z.add_0_r in RD0.
    clear PTRB1.

    step. if_lia. astep. astep. step. if_cases K1; zify_cond K1.
    {
      step. if_lia. astep. hstep. hstep. hstep. step. name_mem m2.
      lazymatch goal with H : rw_cells usegs m2 out _ |- _ => rename H into OUT2 end.
      lazymatch goal with H : mem_inv usegs m2 |- _ => rename H into MI2 end.
      lazymatch goal with H : stk usegs m2 _ _ |- _ => rename H into ST2 end.
      stop_now.
      eapply (EXIT m2 (Z_to_bv 64 0) 0 22); [exact OUT2| lia| intros C0; exfalso; lia| exact SCR| exact STRS| exact REC| exact FRK| exact FRSV| exact FRB
                   | exact MI2| exact ST2| exact ERR| exact MU| exact WM]. }
    subst c0. clear RD0.
    pose proof (bytes_at_skipn _ _ _ 1 PTRB0 ltac:(cbn; lia)) as RB0. cbn [skipn map Z.of_nat Pos.of_succ_nat] in RB0. clear PTRB0.
    set (L0 := zlength rest0) in *.
    assert (P1R : P + 1 + L0 <= alloc_ceiling /\ ae_PTR E <= P + 1).
    { destruct PAT as (pre & Ep & EP). rewrite EP. unfold zlength in *. lia. }

    assert (RBX : forall mX, munch [(q - 336, q); (out, out + 24)] m mX -> wmono usegs m mX -> bytes_at usegs mX (P + 1) (map (Z_to_bv 8) rest0)).
    { intros mX MUx WMx. eapply bytes_at_agree; [eapply agree_on_of_munch; [exact MUx| exact WMx]| exact RB0|]. intros a Ha. rewrite length_map in Ha.
      unfold L0, zlength in *. cbn [outside]. lia. }

    assert (AT44 : forall (mX : mem) (sl L : Z) (k : list Z) (REST : list (list Z)) (ja js c1 c2 c3 c4 k1 k2 o1 o2 o3 o4 : list byte)
                          (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
      rw_cells usegs mX (q + -208) [CB 32 ja] -> rw_cells usegs mX (q + -176) [CB 24 js] ->
      rw_cells usegs mX (q + -152) [CB 8 c1; CB 8 c2; CB 4 c3; CB 4 c4] -> rw_cells usegs mX (q + -128) [CB 8 k1; CB 8 k2] ->
      rw_cells usegs mX (q + -112) [C8 (Z_to_bv 64 (P + 1)); C8 (Z_to_bv 64 L0)] ->
      rw_cells usegs mX (q + -96) (obj_savedU ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10) ->
      rw_cells usegs mX out [CB 8 o1; CB 8 o2; CB 4 o3; CB 4 o4] ->
      rw_cells usegs mX node [C8 (Z_to_bv 64 (ae_DOC E)); C8 (Z_to_bv 64 i)] ->
      rw_cells usegs mX LX_ERRNO [C4 errv] -> mem_inv usegs mX -> stk usegs mX (ae_lo E) (q + -208) ->
      munch [(q - 336, q); (out, out + 24)] m mX -> wmono usegs m mX ->
      ptr_segs (47 :: rest0) = k :: REST -> k = firstn (Z.to_nat L) rest0 -> 0 <= L <= L0 ->
      ((sl = 18446744073709551615 /\ L = L0) \/ (0 <= sl < L0 /\ L = sl)) ->
      ((sl = 18446744073709551615 /\ REST = []) \/
       (0 <= sl < L0 /\ exists r, REST = ptr_segs (47 :: r) /\ ptr_at E (P + 1 + sl) (47 :: r) /\ zlength (47 :: r) = L0 - sl)) ->
      evt usegs (fun ms' => impl usegs (at_node usegs) (atp_walk lops (ptr_segs (47 :: rest0)) s)
                  (epost (fun p => hpost ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s (ae_lo E) (ae_B E) (lvl_R E q out m) (snd p))) ms')
        (MS (mkR y1 (Z_to_bv 64 (q + -208)) gp (Z_to_bv 64 RATP) y5 y6 y7 (Z_to_bv 64 out) (Z_to_bv 64 sl) y10 y11 y12 y13 y14 y15 y16 y17
                 (Z_to_bv 64 node) s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31)
            F (Z_to_bv 64 0x3f0dc) fc None mX (seg_rom usegs))).
    { clear SCR STRS REC FRK FRSV FRB OUT NODE ERR MI ST.
      intros mX sl L k REST ja js c1 c2 c3 c4 k1 k2 o1 o2 o3 o4 y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 SCR STRS REC FRK FRSV FRB OUT NODE ERR MI ST MU1 WM1 SEGS EK LL SLC RC.
      rewrite ELX in ERR. rewrite SEGS.

      assert (AT54 : forall yra ya2 ya3 ya4 ya5 : word,
        evt usegs (fun ms' => impl usegs (at_node usegs) (atp_walk lops (k :: REST) s)
                    (epost (fun p => hpost ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s (ae_lo E) (ae_B E) (lvl_R E q out m) (snd p))) ms')
          (MS (mkR yra (Z_to_bv 64 (q + -208)) gp (Z_to_bv 64 RATP) y5 y6 y7 (Z_to_bv 64 out) (Z_to_bv 64 sl) (Z_to_bv 64 (P + 1)) (Z_to_bv 64 L) ya2 ya3 ya4 ya5 y16 y17
                   (Z_to_bv 64 node) s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31)
              F (Z_to_bv 64 0x3f0ec) fc None mX (seg_rom usegs))).
      2:{ astep. astep. step. step. destruct SLC as [[SLN LE]|[SLR LE]]; subst L.
          - eapply substr_cps with (SV := q + -112) (A := P + 1) (n := L0) (pos := 0) (RA := 0x3f0ec);
              [exact FRSV| lia| lia| lia| | lia| lia| reflexivity| lia| reflexivity|].
            { subst sl. match goal with |- _ < bv_unsigned ?w => let v := eval vm_compute in (bv_unsigned w) in change (bv_unsigned w) with v end. lia. }
            intros ya3 ya4 ya5.
            eapply evt_eq; [| eapply AT54]. subst sl. atp_st_eq.
          - eapply substr_cps_le with (SV := q + -112) (A := P + 1) (n := L0) (pos := 0) (cnt := sl) (RA := 0x3f0ec);
              [exact FRSV| lia| lia| lia| lia| lia| lia| reflexivity| lia| reflexivity|].
            intros ya3 ya4 ya5.
            eapply evt_eq; [| eapply AT54]. atp_st_eq. }
      intros yra ya2 ya3 ya4 ya5.

      hstep. hstep. astep. hstep. hstep. hstep. name_mem m4.
      lazymatch goal with H : rw_cells usegs m4 (q + -128) _ |- _ => rename H into FRK4 end.
      lazymatch goal with H : mem_inv usegs m4 |- _ => rename H into MI4 end.
      lazymatch goal with H : stk usegs m4 _ _ |- _ => rename H into ST4 end.
      pose proof (RBX m4 MU1 WM1) as RB4.
      pose proof (bytes_at_firstn _ _ _ (Z.to_nat L) RB4) as KB4. rewrite firstn_map, <- EK in KB4. clear RB4.
      assert (LK : Z.of_nat (length k) = L) by (rewrite EK, firstn_length_le by (unfold L0, zlength in *; lia); lia).
      assert (LENK : Z.of_nat (length (map (Z_to_bv 8) k)) = L) by (rewrite length_map; exact LK).
      assert (KF : Forall (fun c => 0 <= c < 256) k).
      { rewrite EK. rewrite <- (firstn_skipn (Z.to_nat L) rest0) in KEYF. apply Forall_app in KEYF. tauto. }
      assert (PLO : P + 1 + L <= ae_lo E) by lia.

      astep. astep. astep. step.
      call svfind_spec; [exact FRK4| lia| lia| exact KB4| exact LENK| lia| exact PLO| lia| exact ST4| lia| exact MI4|].
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
      lazymatch goal with H : mem_inv usegs m5 |- _ => rename H into MI5 end.
      lazymatch goal with H : rw_cells usegs m5 (q + -128) _ |- _ => rename H into FRK5 end.
      lazymatch goal with H : rw_cells usegs m5 (q + -152) _ |- _ => rename H into REC5 end.
      lazymatch goal with H : rw_cells usegs m5 (q + -208) _ |- _ => rename H into SCR5 end.
      lazymatch goal with H : rw_cells usegs m5 (q + -176) _ |- _ => rename H into STRS5 end.
      lazymatch goal with H : rw_cells usegs m5 (q + -112) _ |- _ => rename H into FRSV5 end.
      lazymatch goal with H : rw_cells usegs m5 (q + -96) _ |- _ => rename H into FRB5 end.
      lazymatch goal with H : rw_cells usegs m5 out _ |- _ => rename H into OUT5 end.
      lazymatch goal with H : rw_cells usegs m5 node _ |- _ => rename H into NODE5 end.
      lazymatch goal with H : rw_cells usegs m5 980196 _ |- _ => rename H into ERR5 end.
      lazymatch goal with H : munch _ m m5 |- _ => rename H into MU5 end.
      lazymatch goal with H : wmono usegs m m5 |- _ => rename H into WM5 end.
      lazymatch goal with H : stk usegs m5 _ _ |- _ => rename H into ST5 end.
      pose proof (svfind_res_range L 126 (map (Z_to_bv 8) k) ltac:(lia)) as ESR.
      pose proof (RBX m5 MU5 WM5) as RB5.
      apply (rw_cells_merge usegs _ _ [] [_; _; _; _] []) in OUT5. cbn [cells_size csize cells_bytes cbytes Nat.add app] in OUT5.
      assert (HEAP5 : RHEAP s (ae_LB E) m5).
      { eapply LH_frame; [exact HEAP| exact MU5| exact WM5|]. constructor; [apply W_ok_stack; cbn; lia|]. constructor; [apply W_ok_stack; cbn; lia| constructor]. }
      assert (AUX5 : rauxv_ok m5 (ae_B E)).
      { eapply rauxv_ok_frame; [exact AUX| exact MU5| exact WM5|]. constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
      assert (PRES5 : lx_pres (ae_LB E) q [(out, out + 24)] m m5) by (eapply lx_pres_of_munch; [exact MU5| exact WM5| exact CLI]).
      assert (AI5 : AINV E m5).
      { unhide AI. eapply AINV_agree; [exact AI| eapply agree_on_of_munch; [exact MU5| exact WM5]| | | exact OK].
        - intros a Ha. pose proof (BLB a Ha). cbn [outside]. lia.
        - intros a Ha. cbn [outside]. lia. }
      apply (rw_cells_split_CB usegs _ _ [] 32 _ [] [8;8;8;4;4]%nat) in SCR5; [|reflexivity]. cbn [mk_CB_cells app] in SCR5.
      assert (MID : exists j0 j8 j16 j24 j28 jo', obj_mid E d m m5 s ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 out node i e c P L0 L sl rest0 k REST
                      j0 j8 j16 j24 j28 js c4 jo' errv).
      { do 6 eexists. unfold obj_mid.
        split; [exact SCR5|]. split; [exact STRS5|]. split; [exact REC5|]. split; [exact FRK5|]. split; [exact FRSV5|]. split; [exact FRB5|].
        split; [exact OUT5|]. split; [exact QO|]. split; [exact OB|]. split; [exact QD|]. split; [exact OD|].
        split; [exact AI5|]. split; [exact NODE5|]. split; [exact QN|]. split; [exact NB|].
        split; [exact TY|]. split; [exact NXT|]. split; [exact TILES|]. split; [exact I0|]. split; [exact EN|].
        split; [exact RB5|]. split; [exact KEYF|]. split; [reflexivity|]. split; [exact EK|].
        split; [exact LL|]. split; [unfold L0; lia|]. split; [lia|]. split; [exact PAT|]. split; [exact RC|].
        split; [exact HEAP5|]. split; [exact AUX5|]. split; [exact ST5|]. split; [exact LOF|]. split; [exact Q16|].
        split; [rewrite ELX; exact ERR5|]. split; [exact MI5| exact PRES5]. }
      clear SCR5 STRS5 REC5 FRSV5 FRB5 OUT5 NODE5 HEAP5 AUX5 PRES5 AI5 RB5. destruct MID as (mj0 & mj8 & mj16 & mj24 & mj28 & mjo & MID).

      pose proof (munch_refl ([] : list (Z * Z)) m5) as MU0. pose proof (wmono_refl usegs m5) as WM0.
      astep. step. if_cases K2; zify_cond K2; rewrite ?land64_mod in K2.
      { apply evt_done. eapply (obj_noesc E OK d HELEM). exact MID. }

      unfold svfind_res in *.
      destruct (find_byte 126 (firstn (Z.to_nat L) (map (Z_to_bv 8) k))) as [ix|] eqn:FB; [| exfalso; clear - K2; lia].
      pose proof (find_byte_zlist_Some 126 k (Z.to_nat L) ix KF ltac:(lia) FB) as (IX1 & IX2 & IXC & _).
      pose proof (has_tilde_nth _ ix IX1 IXC) as HT.

      step. step. astep. step. if_cases KD; zify_cond KD; rewrite ?land64_mod in KD; [exfalso; lia|]. step. astep. step. if_cases KH; zify_cond KH.
      - apply evt_done. eapply (obj_esc_heap E OK d HELEM HM HF) with (e0 := Z.of_nat ix); [exact MID| lia| exact HT| lia].
      - apply evt_done. eapply (obj_esc_sso E OK d HELEM) with (e0 := Z.of_nat ix); [exact MID| lia| exact HT| lia]. }

    astep. astep. astep. step.
    eapply substr_cps with (SV := q + -112) (A := P) (n := L0 + 1) (pos := 1) (RA := 0x3f0c0);
      [exact FRSV| lia| lia| lia| | lia| lia| reflexivity| lia| reflexivity|].
    { match goal with |- _ < bv_unsigned ?w => let v := eval vm_compute in (bv_unsigned w) in change (bv_unsigned w) with v end. lia. }
    intros ya3 ya4 ya5. replace (L0 + 1 - 1) with L0 by lia.

    hstep. hstep. name_mem m2.
    lazymatch goal with H : rw_cells usegs m2 (q + -112) _ |- _ => rename H into FRSV2 end.
    lazymatch goal with H : mem_inv usegs m2 |- _ => rename H into MI2 end.
    lazymatch goal with H : stk usegs m2 _ _ |- _ => rename H into ST2 end.
    pose proof (RBX m2 MU WM) as RB2.
    assert (LENM : Z.of_nat (length (map (Z_to_bv 8) rest0)) = L0) by (rewrite length_map; reflexivity).
    assert (PLO0 : P + 1 + L0 <= ae_lo E) by lia.

    astep. astep. astep. step.
    call svfind_spec; [exact FRSV2| lia| lia| exact RB2| exact LENM| lia| exact PLO0| lia| exact ST2| lia| exact MI2|].
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
    lazymatch goal with H : mem_inv usegs m3 |- _ => rename H into MI3 end.
    lazymatch goal with H : rw_cells usegs m3 (q + -112) _ |- _ => rename H into FRSV3 end.
    lazymatch goal with H : rw_cells usegs m3 (q + -208) _ |- _ => rename H into SCR3 end.
    lazymatch goal with H : rw_cells usegs m3 (q + -176) _ |- _ => rename H into STRS3 end.
    lazymatch goal with H : rw_cells usegs m3 (q + -152) _ |- _ => rename H into REC3 end.
    lazymatch goal with H : rw_cells usegs m3 (q + -128) _ |- _ => rename H into FRK3 end.
    lazymatch goal with H : rw_cells usegs m3 (q + -96) _ |- _ => rename H into FRB3 end.
    lazymatch goal with H : rw_cells usegs m3 out _ |- _ => rename H into OUT3 end.
    lazymatch goal with H : rw_cells usegs m3 node _ |- _ => rename H into NODE3 end.
    lazymatch goal with H : rw_cells usegs m3 980196 _ |- _ => rename H into ERR3 end.
    lazymatch goal with H : munch _ m m3 |- _ => rename H into MU3 end.
    lazymatch goal with H : wmono usegs m m3 |- _ => rename H into WM3 end.
    lazymatch goal with H : stk usegs m3 _ _ |- _ => rename H into ST3 end.

    step.
    unfold svfind_res.
    destruct (find_byte 47 (firstn (Z.to_nat L0) (map (Z_to_bv 8) rest0))) as [ix|] eqn:FB.
    - pose proof (find_byte_zlist_Some 47 rest0 (Z.to_nat L0) ix KEYF ltac:(lia) FB) as (IX1 & IX2 & IXC & IXN).
      destruct (seg_split rest0 ix ltac:(lia) IXN) as [E1 E2]. rewrite (skipn_cons_nth _ _ IX1), IXC in E1, E2.
      set (r := skipn (S ix) rest0) in *.
      change (take_seg (47 :: r)) with (@nil Z) in E1. change (drop_seg (47 :: r)) with (47 :: r) in E2. rewrite app_nil_r in E1.
      assert (PAT2 : ptr_at E (P + 1 + Z.of_nat ix) (47 :: r)).
      { pose proof (ptr_at_skip E P (47 :: rest0) (S ix) PAT ltac:(cbn [length]; lia)) as X.
        change (skipn (S ix) (47 :: rest0)) with (skipn ix rest0) in X. rewrite (skipn_cons_nth _ _ IX1), IXC in X. fold r in X.
        replace (P + Z.of_nat (S ix)) with (P + 1 + Z.of_nat ix) in X by lia. exact X. }
      assert (ZR : zlength (47 :: r) = L0 - Z.of_nat ix).
      { subst r. rewrite zlength_cons, zlength_skipn by lia. unfold L0. lia. }
      eapply evt_eq; [| eapply (AT44 m3 (Z.of_nat ix) (Z.of_nat ix) (firstn ix rest0) (ptr_segs (47 :: r)));
        [exact SCR3| exact STRS3| exact REC3| exact FRK3| exact FRSV3| exact FRB3| exact OUT3| exact NODE3| rewrite ELX; exact ERR3| exact MI3| exact ST3| exact MU3| exact WM3
        | rewrite ptr_segs_unfold, E1, E2; reflexivity| rewrite Nat2Z.id; reflexivity| unfold L0, zlength in *; lia| right; unfold L0, zlength in *; lia
        | right; split; [unfold L0, zlength in *; lia| exists r; split; [reflexivity| split; [exact PAT2| exact ZR]]]] ]; [atp_st_eq].
    - pose proof (find_byte_zlist_None 47 rest0 (Z.to_nat L0) KEYF ltac:(lia) FB) as IXN.
      destruct (seg_split rest0 (length rest0) ltac:(lia) ltac:(intros j Hj; apply IXN; unfold L0, zlength; lia)) as [E1 E2].
      rewrite skipn_all in E1, E2. cbn [take_seg drop_seg] in E1, E2. rewrite app_nil_r, firstn_all in E1.
      eapply evt_eq; [| eapply (AT44 m3 18446744073709551615 L0 rest0 []);
        [exact SCR3| exact STRS3| exact REC3| exact FRK3| exact FRSV3| exact FRB3| exact OUT3| exact NODE3| rewrite ELX; exact ERR3| exact MI3| exact ST3| exact MU3| exact WM3
        | rewrite ptr_segs_unfold, E1, E2; reflexivity| unfold L0, zlength; rewrite Nat2Z.id, firstn_all; reflexivity| unfold L0; lia| left; split; reflexivity| left; split; reflexivity] ];
        [atp_st_eq].
  Qed.
End Obj.
End WithCeiling0.
