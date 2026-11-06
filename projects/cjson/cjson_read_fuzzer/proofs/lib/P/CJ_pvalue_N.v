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
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import Prelim FloatScan FloatScanProps.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import PImg CJ_iface CJ_tree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require CJ_phex4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_phex4.CJ_pbuf.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require CJ_phex4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_phex4.CJ_parse_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require CJ_phex4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_phex4.CJ_parse_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require CJ_pvalue_A.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_pvalue_A.CJ_pvalue_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require CJ_pvalue_A.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_pvalue_A.CJ_pvalue_ctx.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import FmtFp_facts3.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Scan_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_A.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import Scan_iface.
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

(* [comment removed for export] *)
Ltac fix_lit_store :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) =>
      change (Z_to_le_bytes 8 z) with (le8 (Z_to_bv 64 z)); mem_after_store
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) =>
      change (Z_to_le_bytes 4 z) with (le4 (Z_to_bv 64 z)); mem_after_store
  | _ => idtac
  end.

(* [comment removed for export] *)
Lemma map_Z_to_bv_unsigned : forall l : list byte, map (Z_to_bv 8) (map bv_unsigned l) = l.
Proof. induction l as [|b l IH]; [reflexivity|]. cbn. rewrite IH. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.

Lemma u8arr_prefix : forall m A l j, u8arr psegs m A l -> (j <= length l)%nat -> bytes_at psegs m A (firstn j l).
Proof.
  intros m A l j [BY _] Hj. rewrite <- (firstn_skipn j l) in BY. apply bytes_at_app in BY. exact (proj1 BY).
Qed.

Lemma Forall_firstn_nth : forall (l : list byte) (P : byte -> Prop) k d,
  (k <= length l)%nat -> (forall j, (j < k)%nat -> P (nth j l d)) -> Forall P (firstn k l).
Proof.
  intros l P k d Hk H. apply Forall_forall. intros x Hin.
  apply In_nth with (d := d) in Hin. (nelim Hin 3%nat; intros j Hj <-). rewrite length_firstn in Hj.
  rewrite nth_firstn. replace (j <? k)%nat with true by (symmetry; apply Nat.ltb_lt; lia). apply H. lia.
Qed.

Lemma firstn_S_nth : forall {X} (l : list X) k x, nth_error l k = Some x -> firstn (S k) l = firstn k l ++ [x].
Proof.
  induction l as [|a l IH]; intros k x H; [destruct k; discriminate|].
  destruct k as [|k]; cbn in H |- *; [inversion H; reflexivity|]. rewrite (IH _ _ H). reflexivity.
Qed.

Section PVN.
  Variable HI : cj_heap_iface.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word).
  Variables (m : word -> option byte) (SPB : Z) (LB LR : list cblock) (U P CA blen off depth : Z) (bs : list byte) (D n lo : Z).
  Variables (nx : Z) (pv : word) (ty : Z) (p1 : word) (vi p2 vd : word) (ky : Z).
  Hypothesis PVC : pv_pure sp tp SPB LB LR U P CA blen off depth bs D n lo.
  Hypothesis STRTOD : rstrtod_stmt.

  Notation SP := (bv_unsigned sp).
  Notation L z := (Z_to_bv 64 z) (only parsing).
  Notation CST := (CSTV sp gp tp s7 s8 s9 s10 s11).
  Notation POST := (POSTV HI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m SPB LR U P CA blen off depth bs D n lo nx pv ty p1 vi p2 vd ky).
  Notation MID := (MIDV HI sp m SPB LR P CA bs lo).
  Notation SAVED := (SAVEDV ra s0 s1 s2 s3 s4 s5 s6).
  Notation MASK := 288230376218820613.

  Ltac zfeq := repeat (lazymatch goal with |- @eq Z _ _ => lia | |- _ => first [reflexivity | progress f_equal] end).
  (* [comment removed for export] *)
  Ltac eqcells H :=
    lazymatch goal with |- rw_cells _ _ _ ?cs =>
      lazymatch type of H with rw_cells _ _ _ ?cs' =>
        replace cs with cs'; [exact H| unfold pbuf_cells, node_cells, wz; zfeq] end end.
  Ltac dj := cbn [disjoint_from cells_size csize Nat.add length];
             repeat match goal with H : length ?l = _ |- context [length ?l] => rewrite H end;
             first [lia | split; [lia| exact I]].
  Ltac trc H MU WM := first [ eapply rw_cells_transport in H; [| exact MU| exact WM| dj]
                            | eapply bytes_at_transport in H; [| exact MU| dj]
                            | eapply u8arr_transport in H; [| exact MU| exact WM| dj]
                            | eapply stk_transport_disjoint in H; [| exact MU| exact WM| dj] ].
  Ltac lits := (nelimp (pvc_lits _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ PVC) 14%nat; intros HPU HDn LEN BLEN CEIL LO PP OFF DEP TP URNG DRNG UD SPR).

  (* [comment removed for export] *)
  Definition NQ (m1 : word -> option byte) (Fx : bvmap 5 word) (fcx : bv 32) (x1 x19 x20 x21 x22 x29 x30 x31 : word) : machine_state -> Prop :=
    fun ms' => exists (k : Z) (nb : list byte) (mm : word -> option byte) (x6 x11 x28 : word),
      ms' = CST 0x12d00 x1 (Z_to_bv 64 3) x6 (Z_to_bv 64 k) (Z_to_bv 64 P) (Z_to_bv 64 U) (Z_to_bv 64 10) x11 (Z_to_bv 64 (SP + -136))
                (Z_to_bv 64 58) (Z_to_bv 64 46) (Z_to_bv 64 (CA + off)) (Z_to_bv 64 MASK) (Z_to_bv 64 (blen - off)) (Z_to_bv 64 off)
                x19 x20 x21 x22 x28 x29 x30 x31 Fx fcx mm
      /\ u8arr psegs mm (SP + -136) nb /\ length nb = 64%nat
      /\ 0 <= k <= 63 /\ k <= blen - off
      /\ (forall j, (j < Z.to_nat k)%nat -> is_numch (bv_unsigned (nth j nb (wb 0))) = true)
      /\ munch [(SP + -136, SP + -72)] m1 mm /\ wmono psegs m1 mm /\ mem_inv psegs mm.

  Lemma num_loop : forall m1 Fx fcx x1 x19 x20 x21 x22 x29 x30 x31 (cnt : nat) (i : Z) mm nb x6 x7 x28,
    bytes_at psegs m1 CA bs ->
    Z.of_nat cnt = 63 - i -> 0 <= i <= 62 -> i <= blen - off ->
    u8arr psegs mm (SP + -136) nb -> length nb = 64%nat ->
    (forall j, (j < Z.to_nat i)%nat -> is_numch (bv_unsigned (nth j nb (wb 0))) = true) ->
    munch [(SP + -136, SP + -72)] m1 mm -> wmono psegs m1 mm -> mem_inv psegs mm ->
    evt psegs (NQ m1 Fx fcx x1 x19 x20 x21 x22 x29 x30 x31)
      (CST 0x12c98 x1 (Z_to_bv 64 3) x6 x7 (Z_to_bv 64 P) (Z_to_bv 64 U) (Z_to_bv 64 10) (Z_to_bv 64 i) (Z_to_bv 64 (SP + -136))
           (Z_to_bv 64 58) (Z_to_bv 64 46) (Z_to_bv 64 (CA + off)) (Z_to_bv 64 MASK) (Z_to_bv 64 (blen - off)) (Z_to_bv 64 off)
           x19 x20 x21 x22 x28 x29 x30 x31 Fx fcx mm).
  Proof.
    intros until x31. induction cnt as [cnt IH] using lt_wf_ind.
    intros i mm nb x6 x7 x28 BY1 Hcnt Hi Hio BUF BL NUMCH MU WM MI. lits. unfold CSTV.
    pose proof (bytes_at_bound _ _ _ _ BY1) as BYB.
    assert (BY : bytes_at psegs mm CA bs). { eapply bytes_at_transport; [exact BY1| exact MU|]. cbn. lia. }
    assert (EXIT : forall x6' x11' x28' mm' nb' k, 
              u8arr psegs mm' (SP + -136) nb' -> length nb' = 64%nat -> 0 <= k <= 63 -> k <= blen - off ->
              (forall j, (j < Z.to_nat k)%nat -> is_numch (bv_unsigned (nth j nb' (wb 0))) = true) ->
              munch [(SP + -136, SP + -72)] m1 mm' -> wmono psegs m1 mm' -> mem_inv psegs mm' ->
              evt psegs (NQ m1 Fx fcx x1 x19 x20 x21 x22 x29 x30 x31)
                (CST 0x12d00 x1 (Z_to_bv 64 3) x6' (Z_to_bv 64 k) (Z_to_bv 64 P) (Z_to_bv 64 U) (Z_to_bv 64 10) x11' (Z_to_bv 64 (SP + -136))
                     (Z_to_bv 64 58) (Z_to_bv 64 46) (Z_to_bv 64 (CA + off)) (Z_to_bv 64 MASK) (Z_to_bv 64 (blen - off)) (Z_to_bv 64 off)
                     x19 x20 x21 x22 x28' x29 x30 x31 Fx fcx mm')).
    { intros. apply evt_done. unfold NQ. nexists 6%nat. split; [reflexivity|]. repeat (split; [eassumption|]). assumption. }
    zstep. if_cases Kend; zify_cond Kend.
    { (* [comment removed for export] *) zstep. eapply EXIT; try eassumption; try lia. intros j Hj. apply NUMCH. lia. }
    (nelim (text_read mm CA bs (off + i) (Z_to_bv 64 (CA + off + i)) BY ltac:(lia) ltac:(lia) ltac:(unfold wa; f_equal; lia)) 4%nat; intros c Hc RD Hat).
    pose proof (byte_range c) as Rc.
    (* [comment removed for export] *)
    assert (STORE : forall (cv : Z) x7' x28', is_numch cv = true -> 0 <= cv < 256 ->
      evt psegs (NQ m1 Fx fcx x1 x19 x20 x21 x22 x29 x30 x31)
        (CST 0x12c84 x1 (Z_to_bv 64 3) (Z_to_bv 64 cv) x7' (Z_to_bv 64 P) (Z_to_bv 64 U) (Z_to_bv 64 10) (Z_to_bv 64 i) (Z_to_bv 64 (SP + -136))
             (Z_to_bv 64 58) (Z_to_bv 64 46) (Z_to_bv 64 (CA + off)) (Z_to_bv 64 MASK) (Z_to_bv 64 (blen - off)) (Z_to_bv 64 off)
             x19 x20 x21 x22 x28' x29 x30 x31 Fx fcx mm)).
    { intros cv x7' x28' NC Rcv. unfold CSTV.
      pose proof (u8arr_store_ok psegs _ _ _ i (Z_to_bv 64 (SP + -136 + i)) BUF ltac:(lia) eq_refl) as SOK.
      zstep. zstep. zstep. zstep. rewrite le1_lit.
      pose proof (u8arr_write psegs _ _ _ i (Z_to_bv 8 cv) BUF ltac:(lia)) as BUF'. clear BUF. store_done. rename BUF' into BUF.
      assert (NUMCH' : forall j, (j < Z.to_nat (i + 1))%nat -> is_numch (bv_unsigned (nth j (upd nb (Z.to_nat i) (Z_to_bv 8 cv)) (wb 0))) = true).
      { intros j Hj. destruct (Nat.eq_dec j (Z.to_nat i)) as [->|NE].
        - erewrite nth_error_nth; [| apply nth_error_upd_same; lia]. rewrite Z_to_bv_unsigned. cbn. unfold bv_wrap.
          change (bv_modulus 8) with 256. rewrite Z.mod_small by lia. exact NC.
        - destruct (nth_error_lt_some nb j ltac:(lia)) as [b Hb].
          erewrite nth_error_nth; [| rewrite nth_error_upd_other by lia; exact Hb].
          specialize (NUMCH j ltac:(lia)). erewrite nth_error_nth in NUMCH; [exact NUMCH| exact Hb]. }
      zstep. if_cases K63; zify_cond K63.
      - eapply EXIT; [exact BUF| rewrite upd_length; exact BL| lia| lia| intros j Hj; apply NUMCH'; lia| exact MU| exact WM| exact MI].
      - eapply (IH (cnt - 1)%nat ltac:(lia) (i + 1)); [exact BY1| lia| lia| lia| exact BUF| rewrite upd_length; exact BL| exact NUMCH'| exact MU| exact WM| exact MI]. }
    zstep. zstep. zstep. zstep. if_cases Kdig; zify_cond Kdig.
    { (* [comment removed for export] *) apply STORE; [apply digit_numch; clear -Rc Kdig; Z.div_mod_to_equations; lia| lia]. }
    zstep. zstep. if_cases Kbig; zify_cond Kbig.
    { (* [comment removed for export] *) zstep. zstep. eapply EXIT; try eassumption; try lia. }
    zstep. zstep. zstep. if_cases Kmask; zify_cond Kmask.
    { (* [comment removed for export] *)
      assert (R43 : 0 <= bv_unsigned c + -43 <= 58) by (clear -Rc Kbig Kdig; Z.div_mod_to_equations; lia).
      apply STORE; [| lia]. replace (bv_unsigned c) with ((bv_unsigned c + -43) + 43) by lia.
      apply num_mask_numch; [lia|]. unfold NUM_MASK. rewrite Z.mod_small in Kmask by lia. exact Kmask. }
    zstep. if_cases Kdot; zify_cond Kdot.
    { (* [comment removed for export] *) zstep. apply STORE; [apply dot_numch| lia]. }
    (* [comment removed for export] *)
    zstep. zstep. eapply EXIT; try eassumption; try lia.
  Qed.

  (* [comment removed for export] *)
  Definition WN : list (Z * Z) := [(lo, SP + -64); (0x337ec, 0x337ec + 4); (U + 24, U + 56); (P + 16, P + 24)].

  Lemma WN_facts : forall m1 mo1 LB1 errv1 mc, MID m1 mo1 LB1 errv1 -> Permutation ((U, 64) :: LR) LB1 ->
    munch WN m1 mc -> wmono psegs m1 mc ->
    LHEAP HI SPB LB1 mc mo1 /\ CJST mc /\ ppres LR SP P m mc /\ bytes_at psegs mc CA bs.
  Proof.
    intros m1 mo1 LB1 errv1 mc (HL & BY & CJ & ERR & MI & ST & PR) HP1 MU WM. lits. unfold WN in *.
    assert (INU : In (U, 64) LB1) by (eapply perm_in_head; exact HP1).
    split; [|split; [|split]].
    - eapply (lh_frame HI); [exact HL| exact MU| exact WM|].
      constructor. { right; left. cbn. try rewrite alloc_ceiling_eq. lia. }
      constructor. { do 2 right; left. cbn. unfold PERRNO. lia. }
      constructor. { do 4 right. exists U, 64. cbn. split; [exact INU| lia]. }
      constructor. { right; left. cbn. try rewrite alloc_ceiling_eq. lia. }
      constructor.
    - eapply CJST_frame_gen; [exact CJ| exact MU| exact WM| | |]; unfold PHOOKS, PGERROR, PLCONV; cbn; lia.
    - eapply ppres_trans; [exact PR|]. eapply ppres_of_munch; [exact MU| exact WM|].
      intros a Ha Hp. cbn. unfold pv_addr, palloc_static, PDATA_LO, PIMG_HI, PERRNO, PLIBC, PCTX_END, PSSP, PGOT_SSP in Hp.
      destruct Hp as [[H1 H2]|[[H3 H4]|(A' & n' & Hin & Hr)]]; [lia| lia|].
      (nelimp (lh_block_range HI _ _ _ _ _ _ HL ltac:(eapply Permutation_in; [exact HP1| right; exact Hin])) 5%nat; intros R1 _ _ R4 R5).
      try rewrite alloc_ceiling_eq in R4. unfold PIMG_LO, PIMG_HI in R5.
      destruct (lheap_perm_apart HI _ _ _ _ _ _ _ HL HP1 A' n' Hin) as [_ DJ]. lia.
    - eapply bytes_at_transport; [exact BY| exact MU|]. cbn. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma num_finish : forall (j8 : list byte) (nb : list byte) (used : Z) m1 mo1 errv1 mc Fx fcx (w vdw ev : word)
      x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31,
    MID m1 mo1 LB errv1 ->
    munch WN m1 mc -> wmono psegs m1 mc -> mem_inv psegs mc -> stk psegs mc lo (SP + -144) ->
    rw_cells psegs mc (SP + -144) [CB 8 j8] -> u8arr psegs mc (SP + -136) nb -> length nb = 64%nat ->
    rw_cells psegs mc (SP + -72) (C8 (Z_to_bv 64 (SP + -136 + used)) :: SAVED) ->
    rw_cells psegs mc 0x337ec [C4 ev] ->
    pbuf_at mc P CA blen off depth ->
    rw_cells psegs mc U (node_cells nx pv 0 ty p1 0 vi p2 vdw ky) ->
    1 <= used <= blen - off ->
    Fagree F Fx -> frm0 fcx ->
    SCPS psegs POST (CST 0x12d54 x1 x5 x6 x7 (Z_to_bv 64 P) (Z_to_bv 64 U) (Z_to_bv 64 (SP + -136 + used)) w x12 x13 x14 x15 x16 x17
                         x18 x19 x20 x21 x22 x28 x29 x30 x31 Fx fcx mc) mo1.
  Proof.
    intros until x31. intros MIDm MU WM MI ST FR0 NB BL FR2 ERR PB ND Hu FA FRM. lits.
    pose proof MIDm as (HL1 & _). pose proof (pbuf_at_bound _ _ _ _ _ _ PB) as PBB.
    pose proof (rw_cells_bound psegs _ _ _ ND) as NDB. rewrite node_cells_size in NDB.
    unfold pbuf_at, pbuf_cells, wz in PB. unfold node_cells, wz in ND. unfold SAVEDV in FR2. unfold WN in MU. unfold CSTV.
    eapply scps_step_evt; [eapply (lh_mok HI); exact HL1|].
    zstep. zstep. zstep. fix_lit_store. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mf end.
    pose proof (rw_cells_of_u8arr psegs _ _ _ NB) as NBc.
    assert (FR : rw_cells psegs mf (SP + -144) (CB 80 (j8 ++ nb ++ le8 (Z_to_bv 64 (SP + -136 + used))) :: SAVED)).
    { unfold SAVEDV. apply (rw_cells_merge psegs mf (SP + -144) [] [CB 8 j8; CB 64 nb; C8 (Z_to_bv 64 (SP + -136 + used))]).
      cbn [app]. apply (proj2 (rw_cells_split_app mf (SP + -144) [CB 8 j8] _)). split; [exact FR0|].
      cbn [cells_size csize Nat.add]. replace (SP + -144 + Z.of_nat 8) with (SP + -136) by lia.
      apply (proj2 (rw_cells_split_app mf (SP + -136) [CB 64 nb] _)). split; [|].
      - replace 64%nat with (length nb). exact NBc.
      - cbn [cells_size csize Nat.add]. replace (SP + -136 + Z.of_nat 64) with (SP + -72) by lia. exact FR2. }
    eapply evt_cut; [eapply epilogue_run; [exact PVC| exact FR]|]. intros ms' ->.
    unfold SAVEDV in FR. release_frame FR ST (bv_unsigned sp).
    (nelim (WN_facts m1 mo1 LB errv1 mf MIDm HPU MU WM) 4%nat; intros HLf CJf PRf BYf).
    apply evt_done. apply scps_done. unfold POSTV, parse_value_post.
    nexists 17%nat. exists mf, 1, (off + used), depth, LB, ([] ++ []), ev.
    split; [reflexivity|]. split; [reflexivity|]. split; [exact FA|]. split; [exact FRM|].
    split.
    { split; [exact HLf|]. split; [exact HPU|].
      split; [apply (proj1 HDn)|]. split; [lia|]. split; [lia|]. split; [exact BYf|]. split; [exact LEN|]. split; [exact BLEN|].
      split; [exact CJf|]. split; [unfold PERRNO; exact ERR|]. split; [exact MI|]. split; [exact ST|]. split; [try rewrite alloc_ceiling_eq; exact CEIL|]. exact PP. }
    split; [exact PRf|].
    split. { unfold pbuf_at. eqcells PB. }
    right. split; [reflexivity|]. split; [reflexivity|]. split; [lia|].
    exists 0, 8, 0. do 2 eexists. exists 0%nat, [], []. split; [reflexivity|].
    split. { eqcells ND. }
    split; [cbn; auto 10|]. split; [apply cj_str_null|]. split; [apply cj_chain_nil| lia].
  Qed.

  (* [comment removed for export] *)
  Lemma number_tail : forall (junk0 : list byte) m1 mo1 errv1 Fx fcx
      x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x28 x29 x30 x31,
    MID m1 mo1 LB errv1 ->
    rw_cells psegs m1 (SP + -144) (CB 80 junk0 :: SAVED) ->
    pbuf_at m1 P CA blen off depth ->
    rw_cells psegs m1 U (node_cells nx pv 0 ty p1 0 vi p2 vd ky) ->
    Fagree F Fx -> frm0 fcx ->
    SCPS psegs POST (CST 0x12c20 x1 x5 x6 x7 (Z_to_bv 64 P) (Z_to_bv 64 U) x10 x11 x12 x13 x14 x15 x16 x17
                         (Z_to_bv 64 off) x19 x20 x21 x22 x28 x29 x30 x31 Fx fcx m1) mo1.
  Proof.
    intros until x31. intros MIDm FR PB ND FA FRM. lits. (nelimp MIDm 7%nat; intros HL1 BY CJ ERR MI ST PR).
    pose proof (pbuf_at_bound _ _ _ _ _ _ PB) as PBB. pose proof (rw_cells_bound psegs _ _ _ ND) as NDB. rewrite node_cells_size in NDB.
    pose proof (bytes_at_bound _ _ _ _ BY) as BYB.
    unfold pbuf_at, pbuf_cells, wz in PB. unfold node_cells, wz in ND. unfold SAVEDV in FR. unfold PERRNO in ERR. unfold CSTV.
    (nelimp CJ 3%nat; intros _ _ LC). unfold PLCONV, PDOTSTR, wz in LC.
    (* [comment removed for export] *)
    apply (rw_cells_split_CB psegs m1 _ [] 80 junk0 _ [8; 64; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
    apply (proj1 (rw_cells_split_app m1 _ [CB 8 (firstn 8 junk0)] _)) in FR. destruct FR as [FR0 FR].
    cbn [cells_size csize Nat.add] in FR. replace (SP + -144 + Z.of_nat 8) with (SP + -136) in FR by lia.
    apply (proj1 (rw_cells_split_app m1 _ [CB 64 (firstn 64 (skipn 8 junk0))] _)) in FR. destruct FR as [NBc FR2].
    cbn [cells_size csize Nat.add] in FR2. replace (SP + -136 + Z.of_nat 64) with (SP + -72) in FR2 by lia.
    assert (BL : length (firstn 64 (skipn 8 junk0)) = 64%nat) by (destruct NBc as [[Hwf _] _]; cbn in Hwf; lia).
    pose proof (u8arr_of_rw_cells psegs m1 _ _ _ NBc) as NB. clear NBc.
    pose proof (munch_refl WN m1) as MU. pose proof (wmono_refl psegs m1) as WM. unfold WN in MU.
    eapply scps_step_evt; [eapply (lh_mok HI); exact HL1|].
    zstep. fix_lit_store.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    replace (ret_pc (Z_to_bv 64 0x12c28)) with (Z_to_bv 64 0x12c28) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    zstep. zstep. if_cases Kc; zify_cond Kc; [exfalso; lia|].
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    replace (blen <? blen - off) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z].
    match goal with |- context [Z_to_bv 64 (Z.land ?x (blen - off))] =>
      replace (Z_to_bv 64 (Z.land x (blen - off))) with (Z_to_bv 64 (blen - off))
        by (f_equal; change x with (Z.ones 64); rewrite Z.land_comm, Z.land_ones by lia; rewrite Z.mod_small by lia; reflexivity) end.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
    eapply evt_cut.
    { eapply (num_loop m2 _ _ _ _ _ _ _ _ _ _ (Z.to_nat 63) 0 m2); [exact BY| lia| lia| lia| exact NB| exact BL| intros j Hj; lia| apply munch_refl| apply wmono_refl| exact MI]. }
    intros ms' NQH. (nelim NQH 15%nat; intros k nb m3 x6' x11' x28' -> NB3 BL3 Hk Hkb NUMCH MU3 WM3 MI3). unfold CSTV.
    clear NB.
    trc FR0 MU3 WM3. trc FR2 MU3 WM3. trc PB MU3 WM3. trc ND MU3 WM3. trc LC MU3 WM3. trc ERR MU3 WM3. trc BY MU3 WM3. trc ST MU3 WM3.
    apply (munch_weaken _ [(lo, SP + -64); (210924, 210924 + 4); (U + 24, U + 56); (P + 16, P + 24)]) in MU3.
    2:{ unfold sub_fp. cbn. intros. lia. }
    apply (munch_trans _ _ _ _ MU) in MU3. apply (wmono_trans _ _ _ _ WM) in WM3. clear MU WM MI m2. rename MU3 into MU. rename WM3 into WM. rename MI3 into MI.
    (* [comment removed for export] *)
    pose proof (u8arr_store_ok psegs _ _ _ k (Z_to_bv 64 (SP + -136 + k)) NB3 ltac:(lia) eq_refl) as SOK.
    zstep. zstep. zstep. rewrite le1_lit.
    pose proof (u8arr_write psegs _ _ _ k (Z_to_bv 8 0) NB3 ltac:(lia)) as NB4. clear NB3. store_done.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m4 end.
    zstep. zstep. zstep.
    (* [comment removed for export] *)
    set (nb4 := upd nb (Z.to_nat k) (Z_to_bv 8 0)) in *.
    assert (BL4 : length nb4 = 64%nat) by (unfold nb4; rewrite upd_length; exact BL3).
    set (pre := map bv_unsigned (firstn (Z.to_nat k) nb4)).
    assert (LPRE : length pre = Z.to_nat k) by (unfold pre; rewrite length_map, length_firstn; unfold nb4; rewrite upd_length; lia).
    assert (PRECH : Forall (fun c => is_numch c = true) pre).
    { unfold pre. apply Forall_map. apply (Forall_firstn_nth _ _ _ (wb 0)); [unfold nb4; rewrite upd_length; lia|].
      intros j Hj. unfold nb4. destruct (nth_error_lt_some nb j ltac:(lia)) as [b Hb].
      erewrite nth_error_nth; [| rewrite nth_error_upd_other by lia; exact Hb].
      specialize (NUMCH j Hj). erewrite nth_error_nth in NUMCH; [exact NUMCH| exact Hb]. }
    assert (TXT : bytes_at psegs m4 (SP + -136) (map (Z_to_bv 8) (pre ++ [0]))).
    { rewrite map_app. unfold pre. rewrite map_Z_to_bv_unsigned. cbn [map].
      replace (firstn (Z.to_nat k) nb4 ++ [Z_to_bv 8 0]) with (firstn (S (Z.to_nat k)) nb4).
      - apply (u8arr_prefix _ _ _ _ NB4). unfold nb4. rewrite upd_length. lia.
      - apply firstn_S_nth. unfold nb4. apply nth_error_upd_same. lia. }
    (* [comment removed for export] *)
    (nelim (WN_facts m1 mo1 LB errv1 m4 MIDm HPU MU WM) 4%nat; intros HL4 _ _ _).
    (nelim (lh_ssp HI _ _ _ _ HL4) 3%nat; intros GOT canary GUARD). unfold PGOT_SSP, PSSP, wz in GOT, GUARD.
    assert (PRER : Forall (fun c => 0 <= c < 256) pre) by (eapply Forall_impl; [| exact PRECH]; intros c Hc; apply numch_range; exact Hc).
    assert (PREX : Forall (fun c => c <> 120 /\ c <> 88) pre) by (eapply Forall_impl; [| exact PRECH]; intros c Hc; apply numch_not_x; exact Hc).
    (nelim (scan_strtod_total_gen pre PRER PREX) 4%nat; intros bits used SC Hused).
    pose proof STRTOD as RS. unfold rstrtod_stmt, rstrtod_post, RSTRTOD, RERRNO, RATP, RSTRTOD_DEPTH, RGLOBALS_TOP in RS.
    apply (proj1 (rw_cells_split_app m4 _ [C8 (Z_to_bv 64 0)] _)) in FR2. destruct FR2 as [PEc FRS].
    cbn [cells_size csize Nat.add] in FRS. replace (SP + -72 + Z.of_nat 8) with (SP + -64) in FRS by lia.
    unfold wz, PTP in TP.
    eapply evt_cut.
    { eapply RS with (T := SP + -136) (PE := SP + -72) (txt := pre ++ [0]) (post := []) (lo := lo) (bits := bits) (used := used) (canary := canary);
        rewrite ?unsigned_lit by lia.
      - exact TXT.
      - apply Forall_app. split; [exact PRER| constructor; [lia| constructor]].
      - reflexivity.
      - exact PRECH.
      - rewrite LPRE. lia.
      - unfold zlength. rewrite length_app, LPRE. cbn [length]. lia.
      - exact PEc.
      - exact SC.
      - exact ST.
      - lia.
      - lia.
      - lia.
      - lia.
      - lia.
      - lia.
      - lia.
      - right. unfold zlength. rewrite length_app, LPRE. cbn [length]. lia.
      - split; [exact GOT| exact GUARD].
      - exact ERR.
      - exact MI.
      - exact FRM.
      - exact TP.
      - reflexivity.
      - reflexivity. }
    intros ms' PO.
    (nelim PO 32%nat; intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' m5 ev' -> MU5 WM5 MI5 FRM5 FAG F10 ST5 PE5 TXT5 SSP5 ERR5 USED)
.
    rewrite ?unsigned_lit in MU5, ST5 by lia. unfold zlength in USED. rewrite LPRE in USED.
    replace (ret_pc (Z_to_bv 64 0x12d18)) with (Z_to_bv 64 0x12d18) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    trc FR0 MU5 WM5. trc NB4 MU5 WM5. trc FRS MU5 WM5. trc PB MU5 WM5. trc ND MU5 WM5. trc BY MU5 WM5. clear LC.
    apply (munch_weaken _ [(lo, SP + -64); (210924, 210924 + 4); (U + 24, U + 56); (P + 16, P + 24)]) in MU5.
    2:{ unfold sub_fp. cbn. intros. lia. }
    apply (munch_trans _ _ _ _ MU) in MU5. apply (wmono_trans _ _ _ _ WM) in WM5.
    clear MU WM MI ST HL4 GOT GUARD SSP5 PEc ERR TXT m4 RS. rename MU5 into MU. rename WM5 into WM. rename MI5 into MI.
    assert (FA5 : Fagree F F') by (eapply Fagree_trans; [exact FA| apply Fagree_of_strtod; exact FAG]).
    (* [comment removed for export] *)
    zstep. zstep. if_cases Ku; zify_cond Ku.
    { (* [comment removed for export] *)
      assert (FR : rw_cells psegs m5 (SP + -144) (CB 80 (firstn 8 junk0 ++ nb4 ++ le8 (Z_to_bv 64 (SP + -136 + used))) :: SAVED)).
      { unfold SAVEDV. apply (rw_cells_merge psegs m5 (SP + -144) [] [CB 8 (firstn 8 junk0); CB 64 nb4; C8 (Z_to_bv 64 (SP + -136 + used))]).
        cbn [app]. apply (proj2 (rw_cells_split_app m5 (SP + -144) [CB 8 (firstn 8 junk0)] _)). split; [exact FR0|].
        cbn [cells_size csize Nat.add]. replace (SP + -144 + Z.of_nat 8) with (SP + -136) by lia.
        apply (proj2 (rw_cells_split_app m5 (SP + -136) [CB 64 nb4] _)). split.
        - replace 64%nat with (length nb4) by (unfold nb4; rewrite upd_length; exact BL3). apply rw_cells_of_u8arr. exact NB4.
        - cbn [cells_size csize Nat.add]. replace (SP + -136 + Z.of_nat 64) with (SP + -72) by lia.
          apply (proj2 (rw_cells_split_app m5 (SP + -72) [C8 (Z_to_bv 64 (SP + -136 + used))] _)). split; [exact PE5|].
          cbn [cells_size csize Nat.add]. replace (SP + -72 + Z.of_nat 8) with (SP + -64) by lia. exact FRS. }
      (nelim (WN_facts m1 mo1 LB errv1 m5 MIDm HPU MU WM) 4%nat; intros HL5 CJ5 PR5 BY5).
      apply evt_done. eapply ret0_tail;
        [exact PVC| | exact HPU| exact FR| unfold pbuf_at; eqcells PB| eqcells ND| exact FA5| exact FRM5].
      split; [exact HL5|]. split; [exact BY5|]. split; [exact CJ5|]. split; [unfold PERRNO; exact ERR5|]. split; [exact MI|]. split; [exact ST5| exact PR5]. }
    (* [comment removed for export] *)
    assert (FR2' : rw_cells psegs m5 (SP + -72) (C8 (Z_to_bv 64 (SP + -136 + used)) :: SAVED)).
    { unfold SAVEDV. apply (proj2 (rw_cells_split_app m5 (SP + -72) [C8 (Z_to_bv 64 (SP + -136 + used))] _)). split; [exact PE5|].
      cbn [cells_size csize Nat.add]. replace (SP + -72 + Z.of_nat 8) with (SP + -64) by lia. exact FRS. }
    clear PE5 FRS.
    zstep. zstep. zstep. zstep. zstep.
    Ltac fin PVC MIDm MU WM MI ST5 FR0 NB4 BL4 FR2' ERR5 PB ND FA5 :=
      apply evt_done; eapply num_finish; [exact MIDm| exact MU| exact WM| exact MI| exact ST5| exact FR0| exact NB4| exact BL4| exact FR2'| exact ERR5
                         | unfold pbuf_at; eqcells PB| eqcells ND| lia| | assumption];
      repeat (apply Fagree_set; [| first [left; reflexivity | right; left; reflexivity | right; right; reflexivity]]); exact FA5.
    zstep. rewrite bword_nez. if_cases K1.
    - zstep. fin PVC MIDm MU WM MI ST5 FR0 NB4 BL4 FR2' ERR5 PB ND FA5.
    - zstep. zstep. zstep. zstep. rewrite bword_nez. if_cases K2.
      + fin PVC MIDm MU WM MI ST5 FR0 NB4 BL4 FR2' ERR5 PB ND FA5.
      + zstep. zstep. fin PVC MIDm MU WM MI ST5 FR0 NB4 BL4 FR2' ERR5 PB ND FA5.
  Qed.
End PVN.

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
Ltac fix_lit_store :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) =>
      change (Z_to_le_bytes 8 z) with (le8 (Z_to_bv 64 z)); mem_after_store
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) =>
      change (Z_to_le_bytes 4 z) with (le4 (Z_to_bv 64 z)); mem_after_store
  | _ => idtac
  end.
