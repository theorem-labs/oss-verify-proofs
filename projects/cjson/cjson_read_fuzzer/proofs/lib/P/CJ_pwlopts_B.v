(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Bytes SCPS FP.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import PImg CJ_iface CJ_tree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require CJ_phex4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_phex4.CJ_pbuf.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require CJ_phex4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_phex4.CJ_skipws.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require CJ_pvalue_A.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_pvalue_A.CJ_delete.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import Scan_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require CJ_phex4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_phex4.CJ_parse_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require CJ_phex4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_phex4.CJ_parse_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require CJ_pvalue_A.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_pvalue_A.CJ_pvalue_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import CJ_parse_main.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require CJ_pvalue_A.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_pvalue_A.CJ_pwlopts_A.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.
(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import LiaSplit.
Local Ltac lia ::= lia_cj.
Local Ltac flia ::= flia_cj.
Local Ltac simpl_sizes ::= simpl_sizes_cj.
Local Ltac simpl_arr_sizes ::= simpl_arr_sizes_cj.
(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require StoreCache.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import StoreCache.
Local Ltac mem_after_store ::= mem_after_store_cached.
Local Ltac addr_eq_tac ::= addr_eq_tac_cached.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_cached segs m m' MU WM.




(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Ltac zs_wrap e ::= rewrite (unsigned_lit_wrap e).
Ltac zs_wrap_in e H ::= rewrite (unsigned_lit_wrap e) in H.
Ltac zs_idioms ::=
  match goal with
  | |- context [Z_to_bv 64 (?e mod 18446744073709551616)%Z] => rewrite (Z_to_bv_mod64 e)
  | |- context [Z_to_bv 64 (?e mod 2^64)%Z] => rewrite (Z_to_bv_mod64 e)
  | |- context [Z.shiftr ((Z.shiftl ?x ?k) mod 2^64) ?k] => rewrite (zb_shl_shr x k) by (first [lia | zrange_nonneg])
  end.
Ltac zs_idioms_in H ::=
  match type of H with
  | context [Z_to_bv 64 (?e mod 18446744073709551616)%Z] => rewrite (Z_to_bv_mod64 e) in H
  | context [Z_to_bv 64 (?e mod 2^64)%Z] => rewrite (Z_to_bv_mod64 e) in H
  | context [Z.shiftr ((Z.shiftl ?x ?k) mod 2^64) ?k] => rewrite (zb_shl_shr x k) in H by (first [lia | zrange_nonneg])
  end.

Section WLB.
  Variable HI : cj_heap_iface.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word).
  Variables (m : word -> option byte) (SPB : Z) (LB : list cblock) (CA blen : Z) (bs : list byte) (D n lo : Z).
  Hypothesis WLC : wl_pure sp tp SPB LB CA blen bs D n lo.
  Hypothesis STRTOD : rstrtod_stmt.

  Notation SP := (bv_unsigned sp).
  Notation CST := (CSTW sp gp tp s5 s6 s7 s8 s9 s10 s11).
  Notation DPOST := (DPOST HI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m SPB LB CA bs lo).
  Notation MID := (MIDW HI sp m SPB LB CA bs lo).
  Notation FRSm := (FRS ra sp s0 s1 s2 s3 s4).

  Ltac lits := (nelimp (wlc_lits _ _ _ _ _ _ _ _ _ _ WLC) 11%nat; intros HDn CA0 LEN BLEN CEIL LO SPSPB SPB62 TP DRNG SPR).
  Ltac alia := rewrite ?alloc_ceiling_eq; unfold DELETE_STACK, PARSE_STACK, PARSE_STRING_STACK, PARSE_DOC_STACK; unfold RMALLOC_STACK; lia.
  Ltac zfeq := repeat (lazymatch goal with |- @eq Z _ _ => lia | |- _ => first [reflexivity | progress f_equal] end).
  Ltac eqcells H :=
    lazymatch goal with |- rw_cells _ _ _ ?cs =>
      lazymatch type of H with rw_cells _ _ _ ?cs' =>
        replace cs with cs'; [exact H| unfold pbuf_cells, node_cells, wz; zfeq] end end.
  Ltac dj := cbn [disjoint_from cells_size csize Nat.add length];
             repeat match goal with H : length ?l = _ |- context [length ?l] => rewrite H end;
             first [lia | split; [lia| exact I]].
  Ltac trc H MU WM := first [ eapply rw_cells_transport in H; [| exact MU| exact WM| dj]
                            | eapply bytes_at_transport in H; [| exact MU| dj]
                            | eapply stk_transport_disjoint in H; [| exact MU| exact WM| dj] ].

  (* [comment removed for export] *)
  Lemma zero_node_run_w : forall x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31 Fx fcx mm (A : Z) (junk : list byte),
    rw_cells psegs mm A [CB 64 junk] -> mem_inv psegs mm ->
    evt psegs (fun ms' => exists mm',
                 ms' = CST 0x128dc x1 x5 x6 x7 x8 x9 (Z_to_bv 64 A) (Z_to_bv 64 5) x12 x13 x14 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31 Fx fcx mm'
                 /\ munch [(A, A + 64)] mm mm' /\ wmono psegs mm mm' /\ mem_inv psegs mm'
                 /\ rw_cells psegs mm' A (node_cells 0 (wz 0) 0 0 (wz 0) 0 (wz 0) (wz 0) (wz 0) 0))
        (CST 0x128b8 x1 x5 x6 x7 x8 x9 (Z_to_bv 64 A) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31 Fx fcx mm).
  Proof.
    intros until junk. intros BLK MI. lits. unfold CSTW.
    pose proof (rw_cells_bound psegs _ _ _ BLK) as AB. cbn [cells_size csize Nat.add] in AB.
    pose proof (munch_refl [(A, A + 64)] mm) as MU. pose proof (wmono_refl psegs mm) as WM.
    do 4 (zstep; fix_lit_store). zstep. do 4 (zstep; fix_lit_store).
    apply evt_done. eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
    apply zero_node_cells. exact BLK.
  Qed.

  (* [comment removed for export] *)
  Lemma loopA : forall (cnt : nat) (i : Z) x1 x5 x6 x7 x8 x10 x13 x14 x15 x16 x17 x19 x20 x28 x29 x30 x31 Fx fcx mm,
    Z.of_nat cnt = blen - i -> 0 <= i <= blen -> bytes_at psegs mm CA bs -> mem_inv psegs mm ->
    evt psegs (fun ms' => exists x13',
                 (ms' = CST 0x129a8 x1 x5 x6 x7 x8 (Z_to_bv 64 CA) x10 (Z_to_bv 64 blen) (Z_to_bv 64 32) x13' x14 x15 x16 x17 (Z_to_bv 64 blen) x19 x20 x28 x29 x30 x31 Fx fcx mm
                  /\ fin blen bs i = blen - 1)
                 \/ (ms' = CST 0x1295c x1 x5 x6 x7 x8 (Z_to_bv 64 CA) x10 (Z_to_bv 64 (fin blen bs i)) (Z_to_bv 64 32) x13' x14 x15 x16 x17 (Z_to_bv 64 blen) x19 x20 x28 x29 x30 x31 Fx fcx mm
                  /\ fin blen bs i < blen))
        (CST 0x12930 x1 x5 x6 x7 x8 (Z_to_bv 64 CA) x10 (Z_to_bv 64 i) (Z_to_bv 64 32) x13 x14 x15 x16 x17 (Z_to_bv 64 blen) x19 x20 x28 x29 x30 x31 Fx fcx mm).
  Proof.
    induction cnt as [cnt IH] using lt_wf_ind.
    intros until mm. intros Hc Hi BY MI. lits. unfold CSTW.
    pose proof (bytes_at_bound _ _ _ _ BY) as BYB.
    assert (SEP : CA + blen <= SP + -104 \/ SP + -104 + 56 <= CA) by lia.
    zstep. if_cases Kend; zify_cond Kend.
    { (* [comment removed for export] *) apply evt_done. eexists. left. split; [subst i; reflexivity|].
      subst i. unfold fin. rewrite skipn_all2 by lia. cbn [ws_count Z.of_nat]. rewrite Z.add_0_r, Z.eqb_refl. reflexivity. }
    destruct (nth_error bs (Z.to_nat i)) as [b|] eqn:Hn; [| apply nth_error_None in Hn; lia].
    pose proof (u8ro_read psegs _ CA bs i b _ BY Hn ltac:(lia) eq_refl) as RD.
    pose proof (byte_range b) as Rb.
    zstep. zstep. zstep. zstep. if_cases K; zify_cond K.
    - (* [comment removed for export] *)
      rewrite (fin_ws (SP + -104) CA blen bs LEN ltac:(lia) ltac:(lia) i b) by first [lia | exact Hn].
      destruct (Z.eqb_spec (i + 1) blen) as [E|NE].
      + (* [comment removed for export] *)
        zstep. if_cases K2; zify_cond K2; [| exfalso; lia].
        apply evt_done. eexists. left. split; [rewrite E; reflexivity| reflexivity].
      + replace (CA + i + 1) with (CA + (i + 1)) by lia.
        eapply (IH (cnt - 1)%nat ltac:(lia) (i + 1)); [lia| lia| exact BY| exact MI].
    - (* [comment removed for export] *)
      zstep. zstep. apply evt_done. eexists. right.
      rewrite (fin_stop (SP + -104) CA blen bs LEN SEP i b) by first [lia | exact Hn].
      split; [| lia]. replace (i + 1 + -1) with i by lia. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma call_pv : forall (retpc : Z) (j : list byte) (off0 A : Z) (rnt : word) m1 mo1 LB1 errv1 fc
      x5 x6 x7 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31,
    (retpc = 0x1296c \/ retpc = 0x129bc) ->
    MID m1 mo1 LB1 errv1 -> Permutation ((A, 64) :: LB) LB1 -> A <> 0 ->
    rw_cells psegs m1 A (node_cells 0 (wz 0) 0 0 (wz 0) 0 (wz 0) (wz 0) (wz 0) 0) ->
    rw_cells psegs m1 (SP + -112) [CB 8 j] ->
    rw_cells psegs m1 (SP + -104) (pbuf_cells CA blen off0 0) -> 0 <= off0 <= blen ->
    FRSm m1 -> frm0 fc ->
    SCPS psegs DPOST (CST 0x12a64 (Z_to_bv 64 retpc) x5 x6 x7 (Z_to_bv 64 0) (Z_to_bv 64 CA) (Z_to_bv 64 A) (Z_to_bv 64 (SP + -104)) x12 x13 x14 x15 x16 x17
                          (Z_to_bv 64 A) (Z_to_bv 64 PGERROR) rnt x28 x29 x30 x31 F fc m1) mo1.
  Proof.
    intros until x31. intros Hret (HL & BY & CJ & ERR & MI & ST & PR) HP ANZ ND FJ PB Ho FS FRM. lits. unfold CSTW.
    pose proof (bytes_at_bound _ _ _ _ BY) as BYB. pose proof FS as FS'. unfold FRS in FS'.
    assert (Hret' : 0 <= retpc < 2^64 /\ retpc mod 2 = 0) by (destruct Hret as [-> | ->]; cbn; lia).
    assert (PI : parse_inv HI m1 mo1 SPB LB1 [] LB A (SP + -104) CA blen bs D n lo (SP + -112) errv1).
    { split; [exact HL|]. split; [exact HP|]. split; [exact (proj1 HDn)|]. split; [lia|]. split; [lia|]. split; [exact BY|].
      split; [exact LEN|]. split; [exact BLEN|]. split; [exact CJ|]. split; [exact ERR|]. split; [exact MI|]. split; [exact ST|]. split; [alia|]. lia. }
    eapply scps_bind.
    { pose proof (parse_value_spec HI STRTOD (Z.to_nat blen)) as PVS. unfold parse_value_at in PVS.
      eapply PVS with (U := A) (P := SP + -104) (off := off0) (depth := 0) (nx := 0) (ty := 0) (ky := 0); clear PVS; rewrite ?unsigned_lit by lia;
        first [exact PI | unfold pbuf_at; exact PB | eqcells ND | exact FRM | exact TP | reflexivity | alia ]. }
    cbv beta. intros ms5 mo5 PO'.
    (nelim PO' 32%nat; intros t0' t1' t2' a0' a1_ a2_ a3_ a4_ a5_ a6_ a7' t3' t4' t5' t6' F5 fc5 m5 r off5 depth5 LB5 X5 errv5 -> -> FA5 FRM5 PI5 PR5 PB5 RES)
.
    rewrite ?unsigned_lit in PI5, PR5 by lia.
    replace (ret_pc (Z_to_bv 64 retpc)) with (Z_to_bv 64 retpc) by (symmetry; apply ret_pc_even; lia).
    (nelim PI5 13%nat; intros HL5 HP5 _ _ _ BY5 _ _ CJ5 ERR5 MI5 ST5 _).
    apply (ppres_rw_cells_stack _ _ _ _ _ _ _ PR5) in FJ; [| lia| cbn; lia].
    apply (ppres_rw_cells_stack _ _ _ _ _ _ _ PR5) in FS'; [| lia| cbn; lia].
    assert (MID5 : MID m5 mo5 LB5 errv5).
    { split; [exact HL5|]. split; [exact BY5|]. split; [exact CJ5|]. split; [exact ERR5|]. split; [exact MI5|]. split; [exact ST5|].
      eapply dpres_trans; [exact PR|]. eapply dpres_of_ppres; [exact PR5| lia| lia]. }
    pose proof PB5 as PB5'. unfold pbuf_at, pbuf_cells in PB5'.
    eapply scps_step_evt; [eapply (lh_mok HI); exact HL5|].
    destruct RES as [(-> & -> & ND5) | (-> & -> & Ho5 & ch & ty' & vs & vi' & vd' & dc & Bv & Bc & -> & ND5 & HT & SV & CH & Hdc)].
    - (* [comment removed for export] *)
      assert (CH1 : cj_chain CJ_ANY m5 1 A ((A, 64) :: [] ++ [] ++ [])).
      { eapply cj_chain_one; [exact ANZ| exact ND5| lia| exact I| apply cj_str_null| apply cj_str_null| apply cj_chain_nil]. }
      cbn [app] in CH1.
      destruct Hret as [-> | ->]; unfold wz.
      + zstep. if_true. apply evt_done.
        eapply doc_fail_delete; [exact WLC| exact MID5| | exact CH1| lia| exact FJ| exact PB5'| exact FS'| exact FA5| exact FRM5]. exact HP5.
      + zstep. if_false. zstep. apply evt_done.
        eapply doc_fail_delete; [exact WLC| exact MID5| | exact CH1| lia| exact FJ| exact PB5'| exact FS'| exact FA5| exact FRM5]. exact HP5.
    - (* [comment removed for export] *)
      destruct Hret as [-> | ->]; unfold wz.
      + zstep. if_false. apply evt_done.
        eapply null_check; [exact WLC| exact MID5| exact HP5| exact ANZ| eqcells ND5| exact HT| exact SV| exact CH| lia| exact FJ| exact PB5| lia| exact FS'| exact FA5| exact FRM5].
      + zstep. if_true. apply evt_done.
        eapply null_check; [exact WLC| exact MID5| exact HP5| exact ANZ| eqcells ND5| exact HT| exact SV| exact CH| lia| exact FJ| exact PB5| lia| exact FS'| exact FA5| exact FRM5].
  Qed.

  (* [comment removed for export] *)
  Lemma first_ws : forall (j : list byte) (o0 A : Z) (rnt : word) m1 mo1 LB1 errv1 fc
      x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31,
    MID m1 mo1 LB1 errv1 -> Permutation ((A, 64) :: LB) LB1 -> A <> 0 ->
    rw_cells psegs m1 A (node_cells 0 (wz 0) 0 0 (wz 0) 0 (wz 0) (wz 0) (wz 0) 0) ->
    rw_cells psegs m1 (SP + -112) [CB 8 j] ->
    rw_cells psegs m1 (SP + -104) (pbuf_cells CA blen o0 0) -> 0 <= o0 < blen ->
    FRSm m1 -> frm0 fc ->
    SCPS psegs DPOST (CST 0x1291c x1 x5 x6 x7 (Z_to_bv 64 0) (Z_to_bv 64 CA) (Z_to_bv 64 A) (Z_to_bv 64 o0) x12 x13 x14 x15 x16 x17
                          (Z_to_bv 64 blen) (Z_to_bv 64 PGERROR) rnt x28 x29 x30 x31 F fc m1) mo1.
  Proof.
    intros until x31. intros MIDm HP ANZ ND FJ PB Ho FS FRM. lits. unfold CSTW.
    (nelimp MIDm 7%nat; intros HL BY CJ ERR MI ST PR).
    pose proof (bytes_at_bound _ _ _ _ BY) as BYB. pose proof FS as FS'. unfold FRS in FS'.
    pose proof (rw_cells_bound psegs _ _ _ ND) as NDB. rewrite node_cells_size in NDB.
    (nelimp (lh_block_range HI _ _ _ _ _ _ HL (perm_in_head _ _ _ HP)) 5%nat; intros A1 A2 A3 A4 A5).
    try rewrite alloc_ceiling_eq in A4. unfold PIMG_LO, PIMG_HI in A5.
    assert (INLB : forall b, In b LB -> In b LB1) by (intros b Hb; eapply Permutation_in; [exact HP| right; exact Hb]).
    unfold pbuf_cells, wz in PB. unfold node_cells, wz in ND. unfold PERRNO in ERR.
    (* [comment removed for export] *)
    assert (CALL : forall retpc o' m2 x5' x6' x7' x12' x13' x14' x15' x16' x17' x28' x29' x30' x31',
      (retpc = 0x1296c \/ retpc = 0x129bc) -> 0 <= o' <= blen ->
      rw_cells psegs m2 (SP + -104) (pbuf_cells CA blen o' 0) -> mem_inv psegs m2 ->
      munch [(SP + -88, SP + -80)] m1 m2 -> wmono psegs m1 m2 ->
      SCPS psegs DPOST (CST 0x12a64 (Z_to_bv 64 retpc) x5' x6' x7' (Z_to_bv 64 0) (Z_to_bv 64 CA) (Z_to_bv 64 A) (Z_to_bv 64 (SP + -104)) x12' x13' x14' x15' x16' x17'
                            (Z_to_bv 64 A) (Z_to_bv 64 PGERROR) rnt x28' x29' x30' x31' F fc m2) mo1).
    { intros until x31'. intros Hret Ho' PB2 MI2 MU2 WM2.
      pose proof FJ as FJ2. trc FJ2 MU2 WM2. pose proof FS' as FS2. trc FS2 MU2 WM2. pose proof ND as ND2. trc ND2 MU2 WM2.
      pose proof ERR as ERR2. trc ERR2 MU2 WM2. pose proof ST as ST2. trc ST2 MU2 WM2. pose proof BY as BY2. trc BY2 MU2 WM2.
      eapply (call_pv retpc _ o' A rnt m2 mo1 LB1 errv1 fc); [exact Hret| | exact HP| exact ANZ| eqcells ND2| exact FJ2| exact PB2| exact Ho'| exact FS2| exact FRM].
      split. { eapply (lheap_frame_store HI); [exact HL| exact MU2| exact WM2| alia| alia]. }
      split; [exact BY2|]. split. { eapply CJST_high_store; [exact CJ| exact MU2| exact WM2| alia]. }
      split; [unfold PERRNO; exact ERR2|]. split; [exact MI2|]. split; [exact ST2|].
      eapply dpres_trans; [exact PR|]. eapply dpres_of_munch; [exact MU2| exact WM2|].
      intros a Ha [[Hs|[[Hd _]|(A' & n' & Hin & Hr)]] _]; cbn; [lia| unfold PDATA_LO, PIMG_HI in Hd; lia|].
      (nelimp (lh_block_range HI _ _ _ _ _ _ HL (INLB _ Hin)) 5%nat; intros _ _ _ R4 _). try rewrite alloc_ceiling_eq in R4. lia. }
    eapply scps_step_evt; [eapply (lh_mok HI); exact HL|].
    zstep.
    (nelim (text_read m1 CA bs o0 (Z_to_bv 64 (CA + o0)) BY ltac:(lia) ltac:(lia) eq_refl) 4%nat; intros b Hb RD _).
    pose proof (byte_range b) as Rb.
    zstep. zstep. zstep. if_cases Kb; zify_cond Kb.
    { (* [comment removed for export] *)
      zstep.
      pose proof (munch_refl [(SP + -88, SP + -80)] m1) as MU. pose proof (wmono_refl psegs m1) as WM.
      zstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
      zstep. zstep. zstep. apply evt_done.
      eapply (CALL 0x1296c o0 m2); [left; reflexivity| lia| unfold pbuf_cells, wz; exact PB| exact MI| exact MU| exact WM]. }
    zstep.
    eapply evt_cut; [eapply (loopA (Z.to_nat (blen - (o0 + 1))) (o0 + 1)); [lia| lia| exact BY| exact MI]|].
    intros ms' (x13' & [[-> Hf]|[-> Hf]]); unfold CSTW.
    - (* [comment removed for export] *)
      zstep.
      pose proof (munch_refl [(SP + -88, SP + -80)] m1) as MU. pose proof (wmono_refl psegs m1) as WM.
      zstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
      zstep. zstep. zstep. apply evt_done.
      eapply (CALL 0x129bc (blen - 1) m2); [right; reflexivity| lia| unfold pbuf_cells, wz; eqcells PB| exact MI| exact MU| exact WM].
    - (* [comment removed for export] *)
      pose proof (munch_refl [(SP + -88, SP + -80)] m1) as MU. pose proof (wmono_refl psegs m1) as WM.
      zstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
      zstep. zstep. zstep. apply evt_done.
      pose proof (skipws_off_range bs (o0 + 1)) as OR. rewrite LEN in OR.
      eapply (CALL 0x1296c (fin blen bs (o0 + 1)) m2); [left; reflexivity| | unfold pbuf_cells, wz; exact PB| exact MI| exact MU| exact WM].
      destruct (Z.eq_dec (o0 + 1) blen) as [E|NE].
      + rewrite E in Hf |- *. unfold fin in Hf |- *. rewrite skipn_all2 in Hf |- * by lia. cbn [ws_count Z.of_nat] in Hf |- *. rewrite Z.add_0_r, Z.eqb_refl in Hf |- *. lia.
      + rewrite <- (fin_off0 blen (o0 + 1) bs LEN ltac:(lia)) in Hf |- *. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma wl_body : forall (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (fc : bv 32) (mo : Model) (errv : word),
    LHEAP HI SPB LB m mo -> bytes_at psegs m CA bs -> CJST m -> rw_cells psegs m PERRNO [C4 errv] -> mem_inv psegs m ->
    stk psegs m lo SP -> frm0 fc -> a0 = wz CA -> a1 = wz blen -> a2 = wz 0 ->
    SCPS psegs DPOST (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (wz PARSE_WLOPTS) fc None m (seg_rom psegs)) mo.
  Proof.
    intros until errv. intros HL BY CJ ERR MI ST FRM A0 A1 A2. lits.
    unfold wz in A0, A1, A2. subst a0 a1 a2. unfold PARSE_WLOPTS, wz.
    pose proof (bytes_at_bound _ _ _ _ BY) as BYB. unfold PERRNO in ERR.
    pose proof CJ as (HK & (e1 & e2 & GE) & LC). unfold PHOOKS, wz in HK. unfold PGERROR in GE. unfold PLCONV, wz in LC. clear CJ.
    eapply scps_step_evt; [eapply (lh_mok HI); exact HL|].
    (* [comment removed for export] *)
    pose proof (munch_refl [(SP + -112, SP); (0x337b0, 0x337b0 + 16)] m) as MU. pose proof (wmono_refl psegs m) as WM.
    zstep. carve_frame 112%nat ST. do 6 zstep. zstep. zstep.
    do 7 (zstep; fix_lit_store). zstep. zstep. zstep. fix_lit_store. zstep. fix_lit_store.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    lazymatch type of FR with rw_cells _ _ _ (CB 8 ?jj :: _) => set (j := jj) in FR; clearbody j end.
    (* [comment removed for export] *)
    apply (proj1 (rw_cells_split_app m1 _ [CB 8 j] _)) in FR. destruct FR as [FJ FR].
    cbn [cells_size csize Nat.add] in FR. replace (SP + -112 + Z.of_nat 8) with (SP + -104) in FR by lia.
    apply (proj1 (rw_cells_split_app m1 _ [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] _)) in FR.
    destruct FR as [PB FS]. cbn [cells_size csize Nat.add] in FS. replace (SP + -104 + Z.of_nat 56) with (SP + -48) in FS by lia.
    assert (HL1 : LHEAP HI SPB LB m1 mo).
    { eapply (lh_frame HI); [exact HL| exact MU| exact WM|]. constructor; [right; left; cbn; alia|]. constructor; [do 3 right; left; unfold PGERROR; cbn; lia| constructor]. }
    assert (PR1 : dpres LB SP m m1).
    { eapply dpres_of_munch; [exact MU| exact WM|]. intros a Ha [Hc Hg]. unfold PGERROR in Hg. cbn.
      destruct Hc as [Hs|[[Hd _]|(A' & n' & Hin & Hr)]]; [lia| unfold PDATA_LO, PIMG_HI in Hd; lia|].
      (nelimp (lh_block_range HI _ _ _ _ _ _ HL Hin) 5%nat; intros _ _ _ R4 _). try rewrite alloc_ceiling_eq in R4. lia. }
    assert (CJ1 : CJST m1).
    { split; [unfold PHOOKS, wz; exact HK|]. split; [do 2 eexists; unfold PGERROR; exact GE| unfold PLCONV, wz; exact LC]. }
    clear MU WM HL.
    assert (MID1 : MID m1 mo LB errv).
    { split; [exact HL1|]. split; [exact BY|]. split; [exact CJ1|]. split; [unfold PERRNO; exact ERR|]. split; [exact MI|]. split; [exact ST| exact PR1]. }
    (* [comment removed for export] *)
    zstep. if_cases KC; zify_cond KC; [exfalso; lia|].
    zstep. zstep. if_cases Kb0; zify_cond Kb0.
    { (* [comment removed for export] *)
      zstep. if_cases KC'; zify_cond KC'; [exfalso; lia|].
      apply evt_done. eapply doc_fail; [exact WLC| exact MID1| apply Permutation_refl| exact FJ| exact PB| exact FS| apply Fagree_refl| exact FRM]. }
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep.
    pose proof (munch_refl [(SP + -104, SP + -48)] m1) as MU. pose proof (wmono_refl psegs m1) as WM.
    zstep. zstep. zstep. zstep. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
    assert (HL2 : LHEAP HI SPB LB m2 mo) by (eapply (lheap_frame_store HI); [exact HL1| exact MU| exact WM| alia| alia]).
    assert (CJ2 : CJST m2) by (eapply CJST_high_store; [exact CJ1| exact MU| exact WM| alia]).
    assert (PR2 : dpres LB SP m m2).
    { eapply dpres_trans; [exact PR1|]. eapply dpres_of_munch; [exact MU| exact WM|].
      intros a Ha [[Hs|[[Hd _]|(A' & n' & Hin & Hr)]] _]; cbn; [lia| unfold PDATA_LO, PIMG_HI in Hd; lia|].
      (nelimp (lh_block_range HI _ _ _ _ _ _ HL1 Hin) 5%nat; intros _ _ _ R4 _). try rewrite alloc_ceiling_eq in R4. lia. }
    clear MU WM HL1 CJ1 PR1 MID1 HK GE LC.
    (* [comment removed for export] *)
    zstep. zstep.
    replace (ret_pc (Z_to_bv 64 PMALLOC)) with (wz PMALLOC) by (unfold wz, PMALLOC; symmetry; apply ret_pc_even; [lia| reflexivity]).
    apply evt_done. cbv beta.
    eapply scps_bind.
    { pose proof (lh_malloc HI) as LM. unfold malloc_scps_stmt in LM.
      eapply LM with (lo := lo) (n := 64); rewrite ?unsigned_lit by lia;
        first [ exact HL2 | exact ST | exact ERR | exact MI | exact TP | reflexivity | alia ]. }
    cbv beta. intros ms3 mo3 PO'.
    (nelim PO' 23%nat; intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m3 errv3 -> MI3 ST3 ERR3 PR3 RES)
.
    rewrite ?unsigned_lit in ST3, PR3 by lia.
    replace (ret_pc (Z_to_bv 64 0x128b4)) with (Z_to_bv 64 0x128b4) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    apply (cj_pres_rw_cells _ _ _ _ _ _ PR3) in FJ; [| left; cbn; lia].
    apply (cj_pres_rw_cells _ _ _ _ _ _ PR3) in PB; [| left; cbn; lia].
    apply (cj_pres_rw_cells _ _ _ _ _ _ PR3) in FS; [| left; cbn; lia].
    apply (cj_pres_bytes_at _ _ _ _ _ _ PR3) in BY; [| right; right; exists D, n; split; [apply (proj1 HDn)| lia]].
    apply (CJST_pres _ _ _ _ PR3) in CJ2.
    assert (PR4 : dpres LB SP m m3) by (eapply dpres_trans; [exact PR2| eapply dpres_of_cj_pres; [exact PR3| lia| intros b Hb; exact Hb]]).
    clear PR2 PR3 MI ST HL2 ERR. unfold PERRNO in ERR3.
    destruct RES as [[-> HL3] | (A & jk & -> & ARNG & ANEW & HL3 & BLK)].
    - (* [comment removed for export] *)
      eapply scps_step_evt; [eapply (lh_mok HI); exact HL3|].
      unfold wz. zstep. if_true. zstep. zstep. if_cases Kz; zify_cond Kz; [exfalso; lia|]. zstep.
      apply evt_done. eapply doc_fail_tail; [exact WLC| | apply Permutation_refl| exact FJ| exact PB| exact FS| apply Fagree_refl| exact FRM].
      split; [exact HL3|]. split; [exact BY|]. split; [exact CJ2|]. split; [unfold PERRNO; exact ERR3|]. split; [exact MI3|]. split; [exact ST3| exact PR4].
    - (* [comment removed for export] *)
      (nelimp ARNG 5%nat; intros R1 R2 R3 R4 R5). try rewrite alloc_ceiling_eq in R4. unfold PIMG_LO, PIMG_HI in R5.
      assert (APART : forall A' n', In (A', n') LB -> A' <> A /\ (A' + n' <= A \/ A + 64 <= A')).
      { intros A' n' Hin. eapply (lheap_perm_apart HI); [exact HL3| apply Permutation_refl| exact Hin]. }
      destruct (APART D n (proj1 HDn)) as [_ AD].
      eapply scps_step_evt; [eapply (lh_mok HI); exact HL3|].
      unfold wz. zstep. if_cases Kz; zify_cond Kz; [exfalso; lia|].
      eapply evt_cut; [eapply zero_node_run_w; [exact BLK| exact MI3]|].
      intros ms' nelH_; (nelim nelH_ 6%nat; intros m4 -> MU4 WM4 MI4 NDA). unfold CSTW.
      trc FJ MU4 WM4. trc PB MU4 WM4. trc FS MU4 WM4. trc ERR3 MU4 WM4. trc BY MU4 WM4. trc ST3 MU4 WM4.
      assert (HL4 : LHEAP HI SPB ((A, 64) :: LB) m4 mo3) by (eapply (lheap_block_store HI); [exact HL3| left; reflexivity| exact MU4| exact WM4| lia| lia]).
      assert (CJ4 : CJST m4) by (eapply (CJST_block_store HI); [exact HL3| left; reflexivity| exact CJ2| exact MU4| exact WM4| lia| lia]).
      assert (PR5 : dpres LB SP m m4).
      { eapply dpres_trans; [exact PR4|]. eapply dpres_of_munch; [exact MU4| exact WM4|].
        intros a Ha [[Hs|[[Hd _]|(A' & n' & Hin & Hr)]] _]; cbn; [lia| unfold PDATA_LO, PIMG_HI in Hd; lia|].
        destruct (APART A' n' Hin). lia. }
      assert (MID4 : MID m4 mo3 ((A, 64) :: LB) errv3).
      { split; [exact HL4|]. split; [exact BY|]. split; [exact CJ4|]. split; [unfold PERRNO; exact ERR3|]. split; [exact MI4|]. split; [exact ST3| exact PR5]. }
      clear MU4 WM4 MI3 CJ2 PR4 BLK HL3.
      (* [comment removed for export] *)
      assert (GO : forall (o0 : Z) m5 x11' x12' x13',
        0 <= o0 < blen -> rw_cells psegs m5 (SP + -104) (pbuf_cells CA blen o0 0) -> mem_inv psegs m5 ->
        munch [(SP + -88, SP + -80)] m4 m5 -> wmono psegs m4 m5 -> x11' = Z_to_bv 64 o0 ->
        evt psegs (fun ms' => SCPS psegs DPOST ms' mo3)
          (CST 0x1291c (Z_to_bv 64 0x128b4) t0' t1' t2' (Z_to_bv 64 0) (Z_to_bv 64 CA) (Z_to_bv 64 A) x11' x12' x13' a4' a5' a6' a7'
               (Z_to_bv 64 blen) (Z_to_bv 64 0x337b0) a3 t3' t4' t5' t6' F fc m5)).
      { intros o0 m5 x11' x12' x13' Ho0 PB5 MI5 MU5 WM5 ->. apply evt_done.
        pose proof FJ as FJ5. trc FJ5 MU5 WM5. pose proof FS as FS5. trc FS5 MU5 WM5.
        pose proof NDA as ND5. unfold node_cells, wz in ND5. trc ND5 MU5 WM5.
        pose proof ERR3 as ERR5. trc ERR5 MU5 WM5. pose proof ST3 as ST5. trc ST5 MU5 WM5. pose proof BY as BY5. trc BY5 MU5 WM5.
        change (Z_to_bv 64 0x337b0) with (Z_to_bv 64 PGERROR).
        eapply (first_ws _ o0 A a3 m5 mo3 ((A, 64) :: LB) errv3 fc); [| apply Permutation_refl| lia| eqcells ND5| exact FJ5| exact PB5| exact Ho0| exact FS5| exact FRM].
        split. { eapply (lheap_frame_store HI); [exact HL4| exact MU5| exact WM5| alia| alia]. }
        split; [exact BY5|]. split. { eapply CJST_high_store; [exact CJ4| exact MU5| exact WM5| alia]. }
        split; [unfold PERRNO; exact ERR5|]. split; [exact MI5|]. split; [exact ST5|].
        eapply dpres_trans; [exact PR5|]. eapply dpres_of_munch; [exact MU5| exact WM5|].
        intros a Ha [[Hs|[[Hd _]|(A' & n' & Hin & Hr)]] _]; cbn; [lia| unfold PDATA_LO, PIMG_HI in Hd; lia|].
        (nelimp (lh_block_range HI _ _ _ _ _ _ HL4 ltac:(right; exact Hin)) 5%nat; intros _ _ _ R4' _). try rewrite alloc_ceiling_eq in R4'. lia. }
      (* [comment removed for export] *)
      zstep. if_cases K5; zify_cond K5.
      { (* [comment removed for export] *)
        zstep. zstep. if_cases Kz2; zify_cond Kz2; [exfalso; lia|].
        eapply (GO 0); [lia| exact PB| exact MI4| apply munch_refl| apply wmono_refl| reflexivity]. }
      (nelim (text_read m4 CA bs 0 (Z_to_bv 64 CA) BY ltac:(lia) ltac:(lia) ltac:(unfold wa; f_equal; lia)) 4%nat; intros b0 Hb0 RD0 _).
      pose proof (byte_range b0) as Rb0.
      zstep. zstep. zstep. if_cases K239; zify_cond K239.
      { zstep. zstep. if_cases Kz2; zify_cond Kz2; [exfalso; lia|]. eapply (GO 0); [lia| exact PB| exact MI4| apply munch_refl| apply wmono_refl| reflexivity]. }
      (nelim (text_read m4 CA bs 1 (Z_to_bv 64 (CA + 1)) BY ltac:(lia) ltac:(lia) eq_refl) 4%nat; intros b1 Hb1 RD1 _).
      pose proof (byte_range b1) as Rb1.
      zstep. zstep. zstep. if_cases K187; zify_cond K187.
      { zstep. zstep. if_cases Kz2; zify_cond Kz2; [exfalso; lia|]. eapply (GO 0); [lia| exact PB| exact MI4| apply munch_refl| apply wmono_refl| reflexivity]. }
      (nelim (text_read m4 CA bs 2 (Z_to_bv 64 (CA + 2)) BY ltac:(lia) ltac:(lia) eq_refl) 4%nat; intros b2 Hb2 RD2 _).
      pose proof (byte_range b2) as Rb2.
      zstep. zstep. zstep. if_cases K191; zify_cond K191.
      { zstep. zstep. if_cases Kz2; zify_cond Kz2; [exfalso; lia|]. eapply (GO 0); [lia| exact PB| exact MI4| apply munch_refl| apply wmono_refl| reflexivity]. }
      (* [comment removed for export] *)
      zstep.
      pose proof (munch_refl [(SP + -88, SP + -80)] m4) as MU. pose proof (wmono_refl psegs m4) as WM.
      zstep. fix_lit_store.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
      zstep. if_cases K3; zify_cond K3; [| exfalso; lia].
      eapply (GO 3); [lia| unfold pbuf_cells, wz; exact PB| exact MI4| exact MU| exact WM| reflexivity].
  Qed.
End WLB.

Theorem parse_wlopts_spec : forall HI, rstrtod_stmt -> parse_wlopts_stmt HI.
Proof.
  intros HI STRTOD. unfold parse_wlopts_stmt. intros until errv.
  intros HL HD DCA CAD CA0 BY LEN BLEN CJ ERR MI ST CEIL LO SPSPB SPB62 FRM TP A0 A1 A2.
  eapply (wl_body HI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m SPB LB CA blen bs D n lo);
    [| exact STRTOD| exact HL| exact BY| exact CJ| exact ERR| exact MI| exact ST| exact FRM| exact A0| exact A1| exact A2].
  split; [split; [exact HD| split; [exact DCA| exact CAD]]|]. split; [exact CA0|]. split; [exact LEN|]. split; [exact BLEN|].
  split; [exact CEIL|]. split; [exact LO|]. split; [exact SPSPB|]. split; [exact SPB62|]. split; [exact TP|].
  eapply (lh_block_range HI); [exact HL| exact HD].
Qed.


End CeilWrap.
(* [comment removed for export] *)
Ltac zs_wrap e ::= rewrite (unsigned_lit_wrap e).
Ltac zs_wrap_in e H ::= rewrite (unsigned_lit_wrap e) in H.
Ltac zs_idioms ::=
  match goal with
  | |- context [Z_to_bv 64 (?e mod 18446744073709551616)%Z] => rewrite (Z_to_bv_mod64 e)
  | |- context [Z_to_bv 64 (?e mod 2^64)%Z] => rewrite (Z_to_bv_mod64 e)
  | |- context [Z.shiftr ((Z.shiftl ?x ?k) mod 2^64) ?k] => rewrite (zb_shl_shr x k) by (first [lia | zrange_nonneg])
  end.
Ltac zs_idioms_in H ::=
  match type of H with
  | context [Z_to_bv 64 (?e mod 18446744073709551616)%Z] => rewrite (Z_to_bv_mod64 e) in H
  | context [Z_to_bv 64 (?e mod 2^64)%Z] => rewrite (Z_to_bv_mod64 e) in H
  | context [Z.shiftr ((Z.shiftl ?x ?k) mod 2^64) ?k] => rewrite (zb_shl_shr x k) in H by (first [lia | zrange_nonneg])
  end.
