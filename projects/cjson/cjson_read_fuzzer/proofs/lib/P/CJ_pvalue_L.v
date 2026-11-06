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
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require CJ_phex4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_phex4.CJ_parse_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require CJ_phex4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_phex4.CJ_parse_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require CJ_pvalue_A.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_pvalue_A.CJ_pvalue_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require CJ_pvalue_A.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_pvalue_A.CJ_pvalue_ctx.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import CJ_pvalue_A.
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

Ltac fix_lit_store :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) =>
      change (Z_to_le_bytes 8 z) with (le8 (Z_to_bv 64 z)); mem_after_store
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) =>
      change (Z_to_le_bytes 4 z) with (le4 (Z_to_bv 64 z)); mem_after_store
  | _ => idtac
  end.

Section PVL.
  Variable HI : cj_heap_iface.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word).
  Variables (m : word -> option byte) (SPB : Z) (LB LR : list cblock) (U P CA blen off depth : Z) (bs : list byte) (D n lo : Z).
  Variables (nx : Z) (pv : word) (ty : Z) (p1 : word) (vi p2 vd : word) (ky : Z).
  Hypothesis PVC : pv_pure sp tp SPB LB LR U P CA blen off depth bs D n lo.
  Variable nfuel : nat.
  Hypothesis FUEL : blen - off <= Z.of_nat nfuel.
  Hypothesis PVREC : forall nf, (nf < nfuel)%nat -> parse_value_at HI nf.

  Notation SP := (bv_unsigned sp).
  Notation CST := (CSTV sp gp tp s7 s8 s9 s10 s11).
  Notation POST := (POSTV HI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m SPB LR U P CA blen off depth bs D n lo nx pv ty p1 vi p2 vd ky).
  Notation MID := (MIDV HI sp m SPB LR P CA bs lo).
  Notation SAVED := (SAVEDV ra s0 s1 s2 s3 s4 s5 s6).
  Notation dch := (dch depth).

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
                            | eapply u8arr_transport in H; [| exact MU| exact WM| dj]
                            | eapply stk_transport_disjoint in H; [| exact MU| exact WM| dj] ].
  Ltac lits := (nelimp (pvc_lits _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ PVC) 14%nat; intros HPU HDn LEN BLEN CEIL LO PP OFF DEP TP URNG DRNG UD SPR).
  Ltac alia := rewrite ?alloc_ceiling_eq; unfold DELETE_STACK, PARSE_STACK, PARSE_STRING_STACK; unfold RMALLOC_STACK; lia.

  (* [comment removed for export] *)
  Lemma zero_node_run : forall x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31 Fx fcx mm (A : Z) (junk : list byte),
    rw_cells psegs mm A [CB 64 junk] -> mem_inv psegs mm ->
    evt psegs (fun ms' => exists mm',
                 ms' = CST 0x12dd8 x1 x5 x6 x7 x8 x9 (Z_to_bv 64 A) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 A) x19 x20 (Z_to_bv 64 A) x22 x28 x29 x30 x31 Fx fcx mm'
                 /\ munch [(A, A + 64)] mm mm' /\ wmono psegs mm mm' /\ mem_inv psegs mm'
                 /\ rw_cells psegs mm' A (node_cells 0 (wz 0) 0 0 (wz 0) 0 (wz 0) (wz 0) (wz 0) 0))
        (CST 0x12db0 x1 x5 x6 x7 x8 x9 (Z_to_bv 64 A) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31 Fx fcx mm).
  Proof using PVC nfuel.
    intros until junk. intros BLK MI. lits. unfold CSTV.
    pose proof (rw_cells_bound psegs _ _ _ BLK) as AB. cbn [cells_size csize Nat.add] in AB.
    pose proof (munch_refl [(A, A + 64)] mm) as MU. pose proof (wmono_refl psegs mm) as WM.
    zstep. do 8 (zstep; fix_lit_store). zstep.
    apply evt_done. eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
    apply zero_node_cells. exact BLK.
  Qed.

  Notation ALOOPc := (ALOOP HI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m SPB LR U P CA blen off depth bs D n lo nx pv ty p1 vi p2 vd ky).

  (* [comment removed for export] *)
  Lemma fail_13d24 : forall (junk : list byte) (off1 depth1 head : Z) (X : list cblock) (dd : nat) m1 mo1 LBX errv1 Fx fcx
      x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x28 x29 x30 x31,
    MID m1 mo1 LBX errv1 -> Permutation ((U, 64) :: X ++ LR) LBX ->
    cj_chain CJ_ANY m1 dd head X -> Z.of_nat dd <= 1000 - depth ->
    rw_cells psegs m1 (SP + -144) (CB 80 junk :: SAVED) ->
    pbuf_at m1 P CA blen off1 depth1 ->
    rw_cells psegs m1 U (node_cells nx pv 0 ty p1 0 vi p2 vd ky) ->
    Fagree F Fx -> frm0 fcx ->
    SCPS psegs POST (CST 0x12e54 x1 x5 x6 x7 (Z_to_bv 64 P) (Z_to_bv 64 U) x10 x11 x12 x13 x14 x15 x16 x17
                         x18 x19 x20 (Z_to_bv 64 head) x22 x28 x29 x30 x31 Fx fcx m1) mo1.
  Proof.
    intros until x31. intros MIDm HPX CH Hdd FR PB ND FA FRM. pose proof MIDm as (HL & _). unfold CSTV.
    eapply scps_step_evt; [eapply (lh_mok HI); exact HL|].
    zstep. apply evt_done. eapply arr_fail_delete; [exact PVC| exact nfuel| exact MIDm| exact HPX| exact CH| exact Hdd| exact FR| exact PB| exact ND| exact FA| exact FRM].
  Qed.

  (* [comment removed for export] *)
  Lemma close_ok : forall (junk : list byte) (o3 hd A : Z) (Xall : list cblock) m1 mo1 LBX errv1 Fx fcx
      x1 x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x19 x20 x22 x28 x29 x30 x31,
    MID m1 mo1 LBX errv1 -> Permutation ((U, 64) :: Xall ++ LR) LBX ->
    hd <> 0 -> cj_chain CJ_PRINTABLE m1 (S dch) hd Xall -> depth <= 999 ->
    rw_cells psegs m1 (SP + -144) (CB 80 junk :: SAVED) ->
    pbuf_at m1 P CA blen o3 (depth + 1) ->
    rw_cells psegs m1 U (node_cells nx pv 0 ty p1 0 vi p2 vd ky) ->
    off <= o3 < blen -> Fagree F Fx -> frm0 fcx ->
    SCPS psegs POST (CST 0x12e40 x1 x5 x6 x7 (Z_to_bv 64 P) (Z_to_bv 64 U) x10 (Z_to_bv 64 o3) x12 x13 x14 x15 x16 x17
                         (Z_to_bv 64 A) x19 x20 (Z_to_bv 64 hd) x22 x28 x29 x30 x31 Fx fcx m1) mo1.
  Proof.
    intros until x31. intros MIDm HPX HNZ CH Hd FR PB ND Ho FA FRM. lits. unfold CSTV.
    (nelimp MIDm 7%nat; intros HL BY CJ ERR MI ST PR).
    pose proof (pbuf_at_bound _ _ _ _ _ _ PB) as PBB. pose proof (rw_cells_bound psegs _ _ _ ND) as NDB. rewrite node_cells_size in NDB.
    pose proof (bytes_at_bound _ _ _ _ BY) as BYB.
    assert (INLR : forall b, In b LR -> In b LBX) by (intros b Hb; eapply Permutation_in; [exact HPX| right; apply in_or_app; right; exact Hb]).
    assert (INX : forall b, In b Xall -> In b LBX) by (intros b Hb; eapply Permutation_in; [exact HPX| right; apply in_or_app; left; exact Hb]).
    unfold pbuf_at, pbuf_cells, wz in PB. unfold node_cells, wz in ND. unfold PERRNO in ERR. unfold SAVEDV in FR.
    eapply scps_step_evt; [eapply (lh_mok HI); exact HL|].
    (* [comment removed for export] *)
    pose proof (munch_refl [(P + 24, P + 32)] m1) as MU. pose proof (wmono_refl psegs m1) as WM.
    zstep. zstep. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
    assert (HL2 : LHEAP HI SPB LBX m2 mo1) by (eapply (lheap_frame_store HI); [exact HL| exact MU| exact WM| alia| alia]).
    assert (CJ2 : CJST m2) by (eapply CJST_high_store; [exact CJ| exact MU| exact WM| alia]).
    assert (PR2 : ppres LR SP P m m2).
    { eapply ppres_trans; [exact PR|]. eapply (ppres_pbuf_store HI); [exact HL| exact INLR| exact MU| exact WM| alia| alia| alia]. }
    assert (CH2 : cj_chain CJ_PRINTABLE m2 (S dch) hd Xall).
    { eapply cj_chain_frame; [exact CH| exact MU| exact WM|].
      intros A' k Hin. cbn. split; [|exact I].
      (nelimp (lh_block_range HI _ _ _ _ _ _ HL (INX _ Hin)) 5%nat; intros _ _ _ R4 _). try rewrite alloc_ceiling_eq in R4. lia. }
    clear MU WM HL CJ PR CH.
    (* [comment removed for export] *)
    (nelim (cj_chain_cons_inv _ _ _ _ _ CH2 HNZ) 24%nat; intros d0 nxh pvh chh tyh p1h vsh vih p2h vdh kyh Bvh Bkh Bch Bnh Ed NDH TYH HTh SVh SKh CHCh CHNh EX)
.
    rewrite EX in HPX, INX.
    assert (HPh : Permutation ((hd, 64) :: (Bvh ++ Bkh ++ Bch ++ Bnh) ++ (U, 64) :: LR) LBX).
    { eapply Permutation_trans; [apply perm_pick_head| exact HPX]. }
    (nelimp (lh_block_range HI _ _ _ _ _ _ HL2 (perm_in_head _ _ _ HPh)) 5%nat; intros H1 H2 H3 H4 H5).
    try rewrite alloc_ceiling_eq in H4. unfold PIMG_LO, PIMG_HI in H5.
    destruct (lheap_perm_apart HI _ _ _ _ _ _ _ HL2 HPh U 64 ltac:(apply in_or_app; right; left; reflexivity)) as [_ HU].
    destruct (lheap_perm_apart HI _ _ _ _ _ _ _ HL2 HPh D n ltac:(apply in_or_app; right; right; exact (proj1 HDn))) as [_ HD].
    unfold node_cells, wz in NDH.
    pose proof (munch_refl [(hd + 8, hd + 16)] m2) as MU. pose proof (wmono_refl psegs m2) as WM.
    zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
    assert (INH : In (hd, 64) LBX) by (eapply perm_in_head; exact HPh).
    assert (HL3 : LHEAP HI SPB LBX m3 mo1) by (eapply (lheap_block_store HI); [exact HL2| exact INH| exact MU| exact WM| lia| lia]).
    assert (CJ3 : CJST m3) by (eapply (CJST_block_store HI); [exact HL2| exact INH| exact CJ2| exact MU| exact WM| lia| lia]).
    assert (PR3 : ppres LR SP P m m3).
    { eapply ppres_trans; [exact PR2|]. eapply (ppres_block_store HI); [exact HL2| exact HPh| intros b Hb; apply in_or_app; right; right; exact Hb| alia| exact MU| exact WM| lia| lia]. }
    assert (CH3 : cj_chain CJ_PRINTABLE m3 (S dch) hd Xall).
    { rewrite EX, Ed. eapply (cj_chain_relink HI); [exact HL2| exact HPh| exact HNZ| exact TYH| exact HTh| exact SVh| exact SKh| exact CHCh| exact CHNh| exact MU| exact WM| eqcells NDH]. }
    clear MU WM HL2 CJ2 PR2 CH2 SVh SKh CHCh CHNh. rewrite <- EX in HPX.
    zstep. apply evt_done.
    eapply arr_success; [exact PVC| exact nfuel| | exact HPX| exact CH3| exact Hd| exact FR| unfold pbuf_at; eqcells PB| eqcells ND| exact Ho| exact FA| exact FRM].
    split; [exact HL3|]. split; [exact BY|]. split; [exact CJ3|]. split; [unfold PERRNO; exact ERR|]. split; [exact MI|]. split; [exact ST| exact PR3].
  Qed.

  (* [comment removed for export] *)
  Lemma after_ws2 : forall (c : nat), (forall c', (c' < c)%nat -> ALOOPc c') ->
    forall (junk : list byte) (o o3 hd A : Z) (pvA : word) (chA tyA vsA : Z) (viA vdA : word) (X Bv Bc : list cblock) m1 mo1 LBX errv1 Fx fcx
           x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x22 x28 x29 x30 x31,
      Z.of_nat c = blen - o -> off <= o -> o < o3 <= blen -> depth <= 999 ->
      MID m1 mo1 LBX errv1 -> Permutation ((U, 64) :: (X ++ (A, 64) :: Bv ++ Bc) ++ LR) LBX ->
      hd <> 0 -> A <> 0 -> cj_lseg CJ_PRINTABLE m1 dch hd A X ->
      rw_cells psegs m1 A (node_cells 0 pvA chA tyA (wz 0) vsA viA (wz 0) vdA 0) ->
      CJ_PRINTABLE tyA -> cj_str m1 vsA Bv -> cj_chain CJ_PRINTABLE m1 dch chA Bc ->
      rw_cells psegs m1 (SP + -144) (CB 80 junk :: SAVED) ->
      pbuf_at m1 P CA blen o3 (depth + 1) ->
      rw_cells psegs m1 U (node_cells nx pv 0 ty p1 0 vi p2 vd ky) ->
      Fagree F Fx -> frm0 fcx ->
      SCPS psegs POST (CST 0x12e14 x1 x5 x6 x7 (Z_to_bv 64 P) (Z_to_bv 64 U) x10 x11 x12 x13 x14 x15 x16 x17
                           (Z_to_bv 64 A) x19 (Z_to_bv 64 44) (Z_to_bv 64 hd) x22 x28 x29 x30 x31 Fx fcx m1) mo1.
  Proof.
    intros c IHc. intros until x31. intros Hc Ho Ho3 Hd MIDm HPX HNZ ANZ SEG NDA HTA SVA CHA FR PB ND FA FRM. lits. unfold CSTV.
    (nelimp MIDm 7%nat; intros HL BY CJ ERR MI ST PR).
    pose proof (pbuf_at_bound _ _ _ _ _ _ PB) as PBB. pose proof (bytes_at_bound _ _ _ _ BY) as BYB.
    (* [comment removed for export] *)
    assert (CH : cj_chain CJ_PRINTABLE m1 (S dch) hd (X ++ (A, 64) :: Bv ++ [] ++ Bc)).
    { eapply cj_lseg_chain; [exact SEG|]. eapply cj_chain_one; [exact ANZ| exact NDA| apply CJ_PRINTABLE_range; exact HTA| exact HTA| exact SVA| apply cj_str_null| exact CHA]. }
    cbn [app] in CH.
    assert (FAIL : forall x10' x12' x19' x22',
      SCPS psegs POST (CST 0x12e54 x1 x5 x6 x7 (Z_to_bv 64 P) (Z_to_bv 64 U) x10' (Z_to_bv 64 o3) x12' x13 x14 x15 x16 x17
                           (Z_to_bv 64 A) x19' (Z_to_bv 64 44) (Z_to_bv 64 hd) x22' x28 x29 x30 x31 Fx fcx m1) mo1).
    { intros. eapply fail_13d24; [exact MIDm| exact HPX| eapply cj_chain_any; exact CH| unfold dch; lia| exact FR| exact PB| exact ND| exact FA| exact FRM]. }
    pose proof PB as PB'. unfold pbuf_at, pbuf_cells, wz in PB.
    eapply scps_step_evt; [eapply (lh_mok HI); exact HL|].
    zstep. zstep. zstep. if_cases Kend; zify_cond Kend.
    { (* [comment removed for export] *) unfold CSTV in FAIL. apply evt_done. apply FAIL. }
    zstep. zstep.
    (nelim (text_read m1 CA bs o3 (Z_to_bv 64 (CA + o3)) BY ltac:(lia) ltac:(lia) eq_refl) 4%nat; intros b Hb RD Hat).
    pose proof (byte_range b) as Rb.
    zstep. zstep. zstep. zstep. if_cases Kc; zify_cond Kc.
    { (* [comment removed for export] *)
      apply evt_done. pose proof (IHc (Z.to_nat (blen - o3)) ltac:(lia)) as IH. unfold ALOOP, CSTV in IH.
      eapply (IH o3 hd A (X ++ (A, 64) :: Bv ++ Bc) m1 mo1 LBX errv1); [lia| lia| exact Hd| exact MIDm| exact HPX| | exact FR| exact PB'| exact ND| exact FA| exact FRM].
      right. split; [exact HNZ|]. split; [exact ANZ|]. exists X, Bv, Bc, chA, tyA, vsA, pvA, (wz 0), viA, (wz 0), vdA.
      split; [reflexivity|]. split; [exact SEG|]. split; [exact NDA|]. split; [exact HTA|]. split; [exact SVA| exact CHA]. }
    zstep. zstep. if_cases K93; zify_cond K93.
    { (* [comment removed for export] *) unfold CSTV in FAIL. apply evt_done. apply FAIL. }
    (* [comment removed for export] *)
    apply evt_done. eapply close_ok; [exact MIDm| exact HPX| exact HNZ| exact CH| exact Hd| exact FR| exact PB'| exact ND| lia| exact FA| exact FRM].
  Qed.

  (* [comment removed for export] *)
  Lemma after_call : forall (c : nat), (forall c', (c' < c)%nat -> ALOOPc c') ->
    forall (junk : list byte) (o o1 hd A : Z) (pvA : word) (X : list cblock) (r off5 depth5 : Z) (X5 : list cblock) m1 mo1 LBX errv1 Fx fcx
           x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x22 x28 x29 x30 x31,
      Z.of_nat c = blen - o -> off <= o -> o < o1 -> depth <= 999 ->
      MID m1 mo1 LBX errv1 -> Permutation ((A, 64) :: X5 ++ (U, 64) :: X ++ LR) LBX ->
      hd <> 0 -> A <> 0 -> cj_lseg CJ_PRINTABLE m1 dch hd A X ->
      rw_cells psegs m1 (SP + -144) (CB 80 junk :: SAVED) ->
      pbuf_at m1 P CA blen off5 depth5 ->
      rw_cells psegs m1 U (node_cells nx pv 0 ty p1 0 vi p2 vd ky) ->
      Fagree F Fx -> frm0 fcx ->
      ( (r = 0 /\ X5 = [] /\ rw_cells psegs m1 A (node_cells 0 pvA 0 0 (wz 0) 0 (wz 0) (wz 0) (wz 0) 0))
        \/ (r = 1 /\ depth5 = depth + 1 /\ o1 <= off5 <= blen
             /\ exists (ch ty' vs : Z) (vi' vd' : word) (dc : nat) (Bv Bc : list cblock),
                  X5 = Bv ++ Bc
                  /\ rw_cells psegs m1 A (node_cells 0 pvA ch ty' (wz 0) vs vi' (wz 0) vd' 0)
                  /\ CJ_PRINTABLE ty' /\ cj_str m1 vs Bv /\ cj_chain CJ_PRINTABLE m1 dc ch Bc
                  /\ Z.of_nat dc + (depth + 1) <= 1000) ) ->
      SCPS psegs POST (CST 0x12e08 x1 x5 x6 x7 (Z_to_bv 64 P) (Z_to_bv 64 U) (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17
                           (Z_to_bv 64 A) x19 (Z_to_bv 64 44) (Z_to_bv 64 hd) x22 x28 x29 x30 x31 Fx fcx m1) mo1.
  Proof.
    intros c IHc. intros until x31. intros Hc Ho Ho1 Hd MIDm HPX HNZ ANZ SEG FR PB ND FA FRM RES. lits. unfold CSTV.
    (nelimp MIDm 7%nat; intros HL BY CJ ERR MI ST PR).
    pose proof (pbuf_at_bound _ _ _ _ _ _ PB) as PBB. pose proof (bytes_at_bound _ _ _ _ BY) as BYB.
    pose proof (rw_cells_bound psegs _ _ _ ND) as NDB. rewrite node_cells_size in NDB.
    assert (INLR : forall b, In b LR -> In b LBX) by (intros b Hb; eapply Permutation_in; [exact HPX| right; apply in_or_app; right; right; apply in_or_app; right; exact Hb]).
    assert (INX : forall b, In b X -> In b LBX) by (intros b Hb; eapply Permutation_in; [exact HPX| right; apply in_or_app; right; right; apply in_or_app; left; exact Hb]).
    (nelimp (lh_block_range HI _ _ _ _ _ _ HL (perm_in_head _ _ _ HPX)) 5%nat; intros A1 A2 A3 A4 A5).
    try rewrite alloc_ceiling_eq in A4. unfold PIMG_LO, PIMG_HI in A5.
    eapply scps_step_evt; [eapply (lh_mok HI); exact HL|].
    destruct RES as [(-> & -> & NDA) | (-> & -> & Ho5 & chA & tyA & vsA & viA & vdA & dc & Bv & Bc & -> & NDA & HTA & SVA & CHA & Hdc)].
    - (* [comment removed for export] *)
      zstep. if_true. apply evt_done.
      assert (CH : cj_chain CJ_ANY m1 (S dch) hd (X ++ (A, 64) :: [] ++ [] ++ [])).
      { eapply cj_lseg_chain; [eapply cj_lseg_mono; [exact SEG| intros; exact I| lia]|].
        eapply cj_chain_one; [exact ANZ| exact NDA| lia| exact I| apply cj_str_null| apply cj_str_null| apply cj_chain_nil]. }
      cbn [app] in CH.
      eapply fail_13d24; [exact MIDm| | exact CH| unfold dch; lia| exact FR| exact PB| exact ND| exact FA| exact FRM].
      eapply Permutation_trans; [| exact HPX]. apply Permutation_sym. apply (perm_new_done (U, 64) (A, 64) [] X LR).
    - (* [comment removed for export] *)
      pose proof (rw_cells_bound psegs _ _ _ NDA) as NAB. rewrite node_cells_size in NAB.
      assert (HPX' : Permutation ((U, 64) :: (X ++ (A, 64) :: Bv ++ Bc) ++ LR) LBX).
      { eapply Permutation_trans; [| exact HPX]. apply Permutation_sym. apply perm_new_done. }
      unfold pbuf_at, pbuf_cells, wz in PB. unfold node_cells, wz in ND. unfold node_cells, wz in NDA. unfold PERRNO in ERR. unfold SAVEDV in FR.
      zstep. if_false. zstep. zstep.
      eapply evt_cut.
      { eapply skipws_spec with (P := P) (content := CA) (len := blen) (offset := off5) (depth := depth + 1) (bs := bs);
          [unfold pbuf_at, pbuf_cells; exact PB| reflexivity| lia| lia| exact BY| exact LEN| lia| lia| exact MI]. }
      intros ms' PO. (nelim PO 13%nat; intros a1' a2' a3' a4' a5' a6' m4 -> MU4 WM4 MI4 PB4 BY4).
      replace (ret_pc (Z_to_bv 64 0x12e14)) with (Z_to_bv 64 0x12e14) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      trc FR MU4 WM4. trc ND MU4 WM4. trc NDA MU4 WM4. trc ERR MU4 WM4. trc ST MU4 WM4. clear PB BY MI.
      assert (HL4 : LHEAP HI SPB LBX m4 mo1) by (eapply (lheap_frame_store HI); [exact HL| exact MU4| exact WM4| alia| alia]).
      assert (CJ4 : CJST m4) by (eapply CJST_high_store; [exact CJ| exact MU4| exact WM4| alia]).
      assert (PR4 : ppres LR SP P m m4).
      { eapply ppres_trans; [exact PR|]. eapply (ppres_pbuf_store HI); [exact HL| exact INLR| exact MU4| exact WM4| alia| alia| alia]. }
      assert (BLK : forall A' k, In (A', k) LBX -> disjoint_from [(P + 16, P + 24)] A' k).
      { intros A' k Hin. cbn. split; [|exact I].
        (nelimp (lh_block_range HI _ _ _ _ _ _ HL Hin) 5%nat; intros _ _ _ R4 _). try rewrite alloc_ceiling_eq in R4. lia. }
      assert (SEG4 : cj_lseg CJ_PRINTABLE m4 dch hd A X).
      { eapply cj_lseg_frame; [exact SEG| exact MU4| exact WM4|]. intros A' k Hin. apply BLK. apply INX. exact Hin. }
      assert (SVA4 : cj_str m4 vsA Bv).
      { eapply cj_str_frame; [exact SVA| exact MU4| exact WM4|]. intros A' k Hin. apply BLK.
        eapply Permutation_in; [exact HPX|]. right. apply in_or_app. left. apply in_or_app. left. exact Hin. }
      assert (CHA4 : cj_chain CJ_PRINTABLE m4 dch chA Bc).
      { eapply cj_chain_frame; [eapply cj_chain_mono_d; [exact CHA| unfold dch; lia]| exact MU4| exact WM4|]. intros A' k Hin. apply BLK.
        eapply Permutation_in; [exact HPX|]. right. apply in_or_app. left. apply in_or_app. right. exact Hin. }
      clear MU4 WM4 HL CJ PR SEG SVA CHA.
      assert (O3 : off5 <= skipws_off bs off5 <= blen).
      { destruct (Z.eq_dec off5 blen) as [E|NE].
        - rewrite skipws_off_noop by lia. lia.
        - pose proof (skipws_off_range bs off5) as OR. rewrite LEN in OR. lia. }
      apply evt_done.
      eapply (after_ws2 c IHc _ o (skipws_off bs off5) hd A pvA chA tyA vsA viA vdA X Bv Bc m4 mo1 LBX errv1);
        [exact Hc| exact Ho| lia| exact Hd| | exact HPX'| exact HNZ| exact ANZ| exact SEG4| eqcells NDA| exact HTA| exact SVA4| exact CHA4| exact FR| exact PB4| eqcells ND| exact FA| exact FRM].
      split; [exact HL4|]. split; [exact BY4|]. split; [exact CJ4|]. split; [unfold PERRNO; exact ERR|]. split; [exact MI4|]. split; [exact ST| exact PR4].
  Qed.

  (* [comment removed for export] *)
  Lemma do_call : forall (c : nat), (forall c', (c' < c)%nat -> ALOOPc c') ->
    forall (junk : list byte) (o hd A : Z) (pvA : word) (X : list cblock) m2 mo2 LBX2 errv2 Fx fcx
           x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x22 x28 x29 x30 x31,
      Z.of_nat c = blen - o -> off <= o < blen -> depth <= 999 ->
      MID m2 mo2 LBX2 errv2 -> Permutation ((A, 64) :: (U, 64) :: X ++ LR) LBX2 ->
      hd <> 0 ->
      cj_lseg CJ_PRINTABLE m2 dch hd A X ->
      rw_cells psegs m2 A (node_cells 0 pvA 0 0 (wz 0) 0 (wz 0) (wz 0) (wz 0) 0) ->
      rw_cells psegs m2 (SP + -144) (CB 80 junk :: SAVED) ->
      pbuf_at m2 P CA blen o (depth + 1) ->
      rw_cells psegs m2 U (node_cells nx pv 0 ty p1 0 vi p2 vd ky) ->
      Fagree F Fx -> frm0 fcx ->
      SCPS psegs POST (CST 0x12de8 x1 x5 x6 x7 (Z_to_bv 64 P) (Z_to_bv 64 U) x10 x11 x12 x13 x14 x15 x16 x17
                           (Z_to_bv 64 A) x19 (Z_to_bv 64 44) (Z_to_bv 64 hd) x22 x28 x29 x30 x31 Fx fcx m2) mo2.
  Proof.
    intros c IHc. intros until x31. intros Hc Ho Hd MIDm HPX HNZ SEG NDA FR PB ND FA FRM. lits. unfold CSTV.
    (nelimp MIDm 7%nat; intros HL BY CJ ERR MI ST PR).
    pose proof (pbuf_at_bound _ _ _ _ _ _ PB) as PBB. pose proof (rw_cells_bound psegs _ _ _ ND) as NDB. rewrite node_cells_size in NDB.
    pose proof (rw_cells_bound psegs _ _ _ NDA) as NAB. rewrite node_cells_size in NAB.
    pose proof (bytes_at_bound _ _ _ _ BY) as BYB.
    (nelimp (lh_block_range HI _ _ _ _ _ _ HL (perm_in_head _ _ _ HPX)) 5%nat; intros A1 A2 A3 A4 A5).
    try rewrite alloc_ceiling_eq in A4. unfold PIMG_LO, PIMG_HI in A5.
    unfold pbuf_at, pbuf_cells, wz in PB. unfold node_cells, wz in ND. unfold node_cells, wz in NDA. unfold PERRNO in ERR. unfold SAVEDV in FR.
    assert (INLR : forall b, In b LR -> In b LBX2) by (intros b Hb; eapply Permutation_in; [exact HPX| right; right; apply in_or_app; right; exact Hb]).
    assert (INX : forall b, In b X -> In b LBX2) by (intros b Hb; eapply Permutation_in; [exact HPX| right; right; apply in_or_app; left; exact Hb]).
    assert (BLK : forall A' k, In (A', k) LBX2 -> disjoint_from [(P + 16, P + 24)] A' k).
    { intros A' k Hin. cbn. split; [|exact I].
      (nelimp (lh_block_range HI _ _ _ _ _ _ HL Hin) 5%nat; intros _ _ _ R4 _). try rewrite alloc_ceiling_eq in R4. lia. }
    eapply scps_step_evt; [eapply (lh_mok HI); exact HL|].
    (* [comment removed for export] *)
    pose proof (munch_refl [(P + 16, P + 24)] m2) as MU. pose proof (wmono_refl psegs m2) as WM.
    zstep. zstep. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
    (* [comment removed for export] *)
    zstep. zstep.
    eapply evt_cut.
    { eapply skipws_spec with (P := P) (content := CA) (len := blen) (offset := o + 1) (depth := depth + 1) (bs := bs);
        [unfold pbuf_at, pbuf_cells; exact PB| reflexivity| lia| lia| exact BY| exact LEN| lia| lia| exact MI]. }
    intros ms' PO. (nelim PO 13%nat; intros a1' a2' a3' a4' a5' a6' m4 -> MU4 WM4 MI4 PB4 BY4).
    replace (ret_pc (Z_to_bv 64 0x12dfc)) with (Z_to_bv 64 0x12dfc) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    trc FR MU4 WM4. trc ND MU4 WM4. trc NDA MU4 WM4. trc ERR MU4 WM4. trc ST MU4 WM4. clear PB BY MI.
    apply (munch_trans _ _ _ _ MU) in MU4. apply (wmono_trans _ _ _ _ WM) in WM4. clear MU WM m3.
    assert (HL4 : LHEAP HI SPB LBX2 m4 mo2) by (eapply (lheap_frame_store HI); [exact HL| exact MU4| exact WM4| alia| alia]).
    assert (CJ4 : CJST m4) by (eapply CJST_high_store; [exact CJ| exact MU4| exact WM4| alia]).
    assert (PR4 : ppres LR SP P m m4).
    { eapply ppres_trans; [exact PR|]. eapply (ppres_pbuf_store HI); [exact HL| exact INLR| exact MU4| exact WM4| alia| alia| alia]. }
    assert (SEG4 : cj_lseg CJ_PRINTABLE m4 dch hd A X).
    { eapply cj_lseg_frame; [exact SEG| exact MU4| exact WM4|]. intros A' k Hin. apply BLK. apply INX. exact Hin. }
    clear MU4 WM4 HL CJ PR SEG.
    assert (O1 : o + 1 <= skipws_off bs (o + 1) <= blen).
    { destruct (Z.eq_dec (o + 1) blen) as [E|NE].
      - rewrite skipws_off_noop by lia. lia.
      - pose proof (skipws_off_range bs (o + 1)) as OR. rewrite LEN in OR. lia. }
    set (o1 := skipws_off bs (o + 1)) in *.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    assert (PI : parse_inv HI m4 mo2 SPB LBX2 [] ((U, 64) :: X ++ LR) A P CA blen bs D n lo (SP + -144) errv2).
    { split; [exact HL4|]. split; [exact HPX|]. split; [right; apply in_or_app; right; exact (proj1 HDn)|].
      split; [lia|]. split; [lia|]. split; [exact BY4|]. split; [exact LEN|]. split; [exact BLEN|]. split; [exact CJ4|].
      split; [unfold PERRNO; exact ERR|]. split; [exact MI4|]. split; [exact ST|]. split; [alia|]. lia. }
    apply evt_done. cbv beta.
    eapply scps_bind.
    { pose proof (PVREC (Z.to_nat (blen - o1)) ltac:(lia)) as PVS. unfold parse_value_at in PVS.
      eapply PVS with (U := A) (P := P) (off := o1) (depth := depth + 1) (nx := 0) (ty := 0) (ky := 0); clear PVS; rewrite ?unsigned_lit by lia;
        first [exact PI | exact PB4 | eqcells NDA | exact FRM | exact TP | reflexivity | alia ]. }
    cbv beta. intros ms5 mo5 PO.
    (nelim PO 32%nat; intros t0' t1' t2' a0' a1_ a2_ a3_ a4_ a5_ a6_ a7' t3' t4' t5' t6' F5 fc5 m5 r off5 depth5 LB5 X5 errv5 -> -> FA5 FRM5 PI5 PR5 PB5 RES)
.
    rewrite ?unsigned_lit in PI5, PR5 by lia.
    replace (ret_pc (Z_to_bv 64 0x12e08)) with (Z_to_bv 64 0x12e08) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    (nelim PI5 13%nat; intros HL5 HP5 _ _ _ BY5 _ _ CJ5 ERR5 MI5 ST5 _).
    (* [comment removed for export] *)
    apply (ppres_rw_cells_stack _ _ _ _ _ _ _ PR5) in FR; [| lia| cbn; lia].
    apply (ppres_rw_cells_block _ _ _ _ _ _ _ U 64 PR5) in ND; [| left; reflexivity| lia| cbn; lia].
    apply (ppres_cj_lseg _ _ _ _ _ _ _ _ _ _ PR5) in SEG4; [| intros b Hb; right; apply in_or_app; left; exact Hb].
    assert (PR6 : ppres LR SP P m m5).
    { eapply ppres_trans; [exact PR4|]. eapply ppres_weaken; [exact PR5| lia| intros b Hb; right; apply in_or_app; right; exact Hb]. }
    unfold wz. eapply (after_call c IHc _ o o1 hd A pvA X r off5 depth5 X5 m5 mo5 LB5 errv5);
      [exact Hc| lia| lia| exact Hd| | exact HP5| exact HNZ| lia| exact SEG4| exact FR| exact PB5| eqcells ND| eapply Fagree_trans; [exact FA| exact FA5]| exact FRM5| exact RES].
    split; [exact HL5|]. split; [exact BY5|]. split; [exact CJ5|]. split; [exact ERR5|]. split; [exact MI5|]. split; [exact ST5| exact PR6].
  Qed.

  (* [comment removed for export] *)
  Lemma loop_body : forall (c : nat), (forall c', (c' < c)%nat -> ALOOPc c') -> ALOOPc c.
  Proof.
    intros c IHc. unfold ALOOP. intros until x31. intros Hc Ho Hd MIDm HPX AI FR PB ND FA FRM. lits. unfold CSTV.
    (nelimp MIDm 7%nat; intros HL BY CJ ERR MI ST PR).
    pose proof (pbuf_at_bound _ _ _ _ _ _ PB) as PBB. pose proof (rw_cells_bound psegs _ _ _ ND) as NDB. rewrite node_cells_size in NDB.
    pose proof (bytes_at_bound _ _ _ _ BY) as BYB.
    assert (INLR : forall b, In b LR -> In b LBX) by (intros b Hb; eapply Permutation_in; [exact HPX| right; apply in_or_app; right; exact Hb]).
    assert (INX : forall b, In b X -> In b LBX) by (intros b Hb; eapply Permutation_in; [exact HPX| right; apply in_or_app; left; exact Hb]).
    assert (INU : In (U, 64) LBX) by (eapply perm_in_head; exact HPX).
    pose proof PB as PB'. unfold pbuf_at, pbuf_cells, wz in PB. unfold node_cells, wz in ND. unfold PERRNO in ERR. unfold SAVEDV in FR.
    eapply scps_step_evt; [eapply (lh_mok HI); exact HL|].
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    replace (ret_pc (Z_to_bv 64 PMALLOC)) with (wz PMALLOC) by (unfold wz, PMALLOC; symmetry; apply ret_pc_even; [lia| reflexivity]).
    apply evt_done. cbv beta.
    eapply scps_bind.
    { pose proof (lh_malloc HI) as LM. unfold malloc_scps_stmt in LM.
      eapply LM with (lo := lo) (n := 64); rewrite ?unsigned_lit by lia;
        first [ exact HL | exact ST | exact ERR | exact MI | exact TP | reflexivity | alia ]. }
    cbv beta. intros ms2 mo2 PO.
    (nelim PO 23%nat; intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 errv2 -> MI2 ST2 ERR2 PR2 RES)
.
    rewrite ?unsigned_lit in ST2, PR2 by lia.
    replace (ret_pc (Z_to_bv 64 0x12dac)) with (Z_to_bv 64 0x12dac) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    apply (cj_pres_rw_cells _ _ _ _ _ _ PR2) in FR; [| left; lia].
    apply (cj_pres_rw_cells _ _ _ _ _ _ PR2) in PB; [| left; cbn; lia].
    pose proof PB' as PB2. unfold pbuf_at in PB2. apply (cj_pres_rw_cells _ _ _ _ _ _ PR2) in PB2; [| left; cbn; lia]. clear PB'.
    apply (cj_pres_rw_cells _ _ _ _ _ _ PR2) in ND; [| right; right; exists U, 64; split; [exact INU| cbn; lia]].
    apply (cj_pres_bytes_at _ _ _ _ _ _ PR2) in BY; [| right; right; exists D, n; split; [apply INLR; apply (proj1 HDn)| lia]].
    apply (CJST_pres _ _ _ _ PR2) in CJ.
    apply (arr_inv_magree _ nfuel m1 m2) in AI; [| eapply magree_blocks_of_cj_pres; [exact PR2| exact INX]].
    assert (PR3 : ppres LR SP P m m2) by (eapply ppres_trans; [exact PR| eapply ppres_of_cj_pres; [exact PR2| lia| exact INLR]]).
    clear PR PR2 MI ST HL ERR. unfold PERRNO in ERR2.
    destruct RES as [[-> HL2] | (A & jk & -> & ARNG & ANEW & HL2 & BLK)].
    - (* [comment removed for export] *)
      eapply scps_step_evt; [eapply (lh_mok HI); exact HL2|].
      (nelimp (cj_chain_ptr_range _ _ _ _ _ (arr_inv_chain _ _ _ _ _ AI)) 3%nat; intros HR1 _ HR2).
      unfold wz. zstep. if_true. zstep. if_cases Kh; zify_cond Kh.
      + (* [comment removed for export] *)
        apply evt_done. eapply arr_fail_delete; [exact PVC| exact nfuel| | exact HPX| eapply cj_chain_any; eapply arr_inv_chain; exact AI| unfold dch; lia| exact FR| unfold pbuf_at; exact PB2| eqcells ND| exact FA| exact FRM].
        split; [exact HL2|]. split; [exact BY|]. split; [exact CJ|]. split; [unfold PERRNO; exact ERR2|]. split; [exact MI2|]. split; [exact ST2| exact PR3].
      + (* [comment removed for export] *)
        destruct AI as [[_ ->]|(NZ & _)]; [| exfalso; exact (NZ Kh)]. cbn [app] in HPX.
        apply evt_done. eapply ret0_tail; [exact PVC| | exact HPX| exact FR| unfold pbuf_at; exact PB2| eqcells ND| exact FA| exact FRM].
        split; [exact HL2|]. split; [exact BY|]. split; [exact CJ|]. split; [unfold PERRNO; exact ERR2|]. split; [exact MI2|]. split; [exact ST2| exact PR3].
    - (* [comment removed for export] *)
      (nelimp ARNG 5%nat; intros A1 A2 A3 A4 A5). try rewrite alloc_ceiling_eq in A4. unfold PIMG_LO, PIMG_HI in A5.
      assert (APART : forall A' n', In (A', n') LBX -> A' <> A /\ (A' + n' <= A \/ A + 64 <= A')).
      { intros A' n' Hin. eapply (lheap_perm_apart HI); [exact HL2| apply Permutation_refl| exact Hin]. }
      destruct (APART U 64 INU) as [_ AU]. destruct (APART D n (INLR _ (proj1 HDn))) as [_ AD].
      eapply scps_step_evt; [eapply (lh_mok HI); exact HL2|].
      unfold wz. zstep. if_cases Kz; zify_cond Kz; [exfalso; lia|].
      eapply evt_cut; [eapply zero_node_run; [exact BLK| exact MI2]|].
      intros ms' nelH_; (nelim nelH_ 6%nat; intros m3 -> MU3 WM3 MI3 NDA). unfold CSTV.
      trc FR MU3 WM3. trc PB MU3 WM3. trc ND MU3 WM3. trc ERR2 MU3 WM3. trc BY MU3 WM3. trc ST2 MU3 WM3.
      apply (arr_inv_magree _ nfuel m2 m3) in AI.
      2:{ eapply magree_blocks_of_munch; [exact MU3| exact WM3|]. intros A' n' Hin. cbn. split; [|exact I]. destruct (APART A' n' (INX _ Hin)). lia. }
      assert (HL3 : LHEAP HI SPB ((A, 64) :: LBX) m3 mo2) by (eapply (lheap_block_store HI); [exact HL2| left; reflexivity| exact MU3| exact WM3| lia| lia]).
      assert (CJ3 : CJST m3) by (eapply (CJST_block_store HI); [exact HL2| left; reflexivity| exact CJ| exact MU3| exact WM3| lia| lia]).
      assert (PR4 : ppres LR SP P m m3).
      { eapply ppres_trans; [exact PR3|]. eapply (ppres_block_store HI); [exact HL2| apply Permutation_refl| exact INLR| alia| exact MU3| exact WM3| lia| lia]. }
      clear MU3 WM3 MI2 CJ PR3 BLK.
      (nelimp (cj_chain_ptr_range _ _ _ _ _ (arr_inv_chain _ _ _ _ _ AI)) 3%nat; intros HR1 _ HR2).
      zstep. if_cases Kh; zify_cond Kh.
      + (* [comment removed for export] *)
        destruct AI as [[_ ->]|(NZ & _)]; [| exfalso; exact (NZ Kh)]. cbn [app] in HPX.
        apply evt_done. eapply (do_call c IHc _ o A A (wz 0) [] m3 mo2 ((A, 64) :: LBX) errv2);
          [exact Hc| exact Ho| exact Hd| | apply perm_skip; exact HPX| lia| apply cj_lseg_nil| exact NDA| exact FR| unfold pbuf_at; eqcells PB| eqcells ND| exact FA| exact FRM].
        split; [exact HL3|]. split; [exact BY|]. split; [exact CJ3|]. split; [unfold PERRNO; exact ERR2|]. split; [exact MI3|]. split; [exact ST2| exact PR4].
      + (* [comment removed for export] *)
        destruct AI as [[E _]|(NZ & NZc & B1 & Bv & Bc & chc & tyc & vsc & pvc & p1c & vic & p2c & vdc & -> & SEG & NDC & TYC & SVC & CHC)]; [exfalso; exact (Kh E)|].
        assert (HPcur : Permutation ((cur, 64) :: (A, 64) :: (B1 ++ Bv ++ Bc) ++ (U, 64) :: LR) ((A, 64) :: LBX)).
        { eapply Permutation_trans; [apply perm_swap|]. apply perm_skip. eapply Permutation_trans; [apply perm_pick_mid| exact HPX]. }
        (nelimp (lh_block_range HI _ _ _ _ _ _ HL3 (perm_in_head _ _ _ HPcur)) 5%nat; intros C1 C2 C3 C4 C5).
        try rewrite alloc_ceiling_eq in C4. unfold PIMG_LO, PIMG_HI in C5.
        assert (CPART : forall A' n', In (A', n') ((A, 64) :: (B1 ++ Bv ++ Bc) ++ (U, 64) :: LR) -> A' <> cur /\ (A' + n' <= cur \/ cur + 64 <= A')).
        { intros A' n' Hin. eapply (lheap_perm_apart HI); [exact HL3| exact HPcur| exact Hin]. }
        destruct (CPART A 64 ltac:(left; reflexivity)) as [_ CA'].
        destruct (CPART U 64 ltac:(right; apply in_or_app; right; left; reflexivity)) as [_ CU].
        destruct (CPART D n ltac:(right; apply in_or_app; right; right; exact (proj1 HDn))) as [_ CD].
        pose proof (rw_cells_bound psegs _ _ _ NDC) as NCB. rewrite node_cells_size in NCB.
        unfold node_cells, wz in NDC. unfold node_cells, wz in NDA.
        (* [comment removed for export] *)
        pose proof (munch_refl [(cur, cur + 8)] m3) as MU. pose proof (wmono_refl psegs m3) as WM.
        zstep.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m4 end.
        assert (INC : In (cur, 64) ((A, 64) :: LBX)) by (eapply perm_in_head; exact HPcur).
        assert (HL4 : LHEAP HI SPB ((A, 64) :: LBX) m4 mo2) by (eapply (lheap_block_store HI); [exact HL3| exact INC| exact MU| exact WM| lia| lia]).
        assert (CJ4 : CJST m4) by (eapply (CJST_block_store HI); [exact HL3| exact INC| exact CJ3| exact MU| exact WM| lia| lia]).
        assert (PR5 : ppres LR SP P m m4).
        { eapply ppres_trans; [exact PR4|]. eapply (ppres_block_store HI); [exact HL3| exact HPcur| intros b Hb; right; apply in_or_app; right; right; exact Hb| alia| exact MU| exact WM| lia| lia]. }
        assert (DJ : forall A' n', In (A', n') (B1 ++ Bv ++ Bc) -> disjoint_from [(cur, cur + 8)] A' n').
        { intros A' n' Hin. cbn. split; [|exact I]. destruct (CPART A' n' ltac:(right; apply in_or_app; left; exact Hin)). lia. }
        assert (SEG4 : cj_lseg CJ_PRINTABLE m4 dch head cur B1).
        { eapply cj_lseg_frame; [exact SEG| exact MU| exact WM|]. intros A' n' Hin. apply DJ. apply in_or_app. left. exact Hin. }
        assert (SVC4 : cj_str m4 vsc Bv).
        { eapply cj_str_frame; [exact SVC| exact MU| exact WM|]. intros A' n' Hin. apply DJ. apply in_or_app. right. apply in_or_app. left. exact Hin. }
        assert (CHC4 : cj_chain CJ_PRINTABLE m4 dch chc Bc).
        { eapply cj_chain_frame; [exact CHC| exact MU| exact WM|]. intros A' n' Hin. apply DJ. apply in_or_app. right. apply in_or_app. right. exact Hin. }
        clear MU WM HL3 CJ3 PR4 SEG SVC CHC DJ.
        (* [comment removed for export] *)
        pose proof (munch_refl [(A + 8, A + 16)] m4) as MU. pose proof (wmono_refl psegs m4) as WM.
        zstep.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
        assert (HL5 : LHEAP HI SPB ((A, 64) :: LBX) m5 mo2) by (eapply (lheap_block_store HI); [exact HL4| left; reflexivity| exact MU| exact WM| lia| lia]).
        assert (CJ5 : CJST m5) by (eapply (CJST_block_store HI); [exact HL4| left; reflexivity| exact CJ4| exact MU| exact WM| lia| lia]).
        assert (PR6 : ppres LR SP P m m5).
        { eapply ppres_trans; [exact PR5|]. eapply (ppres_block_store HI); [exact HL4| apply Permutation_refl| exact INLR| alia| exact MU| exact WM| lia| lia]. }
        assert (DJ : forall A' n', In (A', n') (B1 ++ Bv ++ Bc) -> disjoint_from [(A + 8, A + 16)] A' n').
        { intros A' n' Hin. cbn. split; [|exact I].
          destruct (APART A' n') as [_ ?]; [| lia]. apply INX. apply in_app_or in Hin. apply in_or_app. destruct Hin as [Hin|Hin]; [left; exact Hin| right; right; exact Hin]. }
        assert (SEG5 : cj_lseg CJ_PRINTABLE m5 dch head cur B1).
        { eapply cj_lseg_frame; [exact SEG4| exact MU| exact WM|]. intros A' n' Hin. apply DJ. apply in_or_app. left. exact Hin. }
        assert (SVC5 : cj_str m5 vsc Bv).
        { eapply cj_str_frame; [exact SVC4| exact MU| exact WM|]. intros A' n' Hin. apply DJ. apply in_or_app. right. apply in_or_app. left. exact Hin. }
        assert (CHC5 : cj_chain CJ_PRINTABLE m5 dch chc Bc).
        { eapply cj_chain_frame; [exact CHC4| exact MU| exact WM|]. intros A' n' Hin. apply DJ. apply in_or_app. right. apply in_or_app. right. exact Hin. }
        clear MU WM HL4 CJ4 PR5 SEG4 SVC4 CHC4 DJ.
        zstep. apply evt_done.
        eapply (do_call c IHc _ o head A (Z_to_bv 64 cur) (B1 ++ (cur, 64) :: Bv ++ Bc) m5 mo2 ((A, 64) :: LBX) errv2);
          [exact Hc| exact Ho| exact Hd| | apply perm_skip; exact HPX| exact NZ| | eqcells NDA| exact FR| unfold pbuf_at; eqcells PB| eqcells ND| exact FA| exact FRM].
        * split; [exact HL5|]. split; [exact BY|]. split; [exact CJ5|]. split; [unfold PERRNO; exact ERR2|]. split; [exact MI3|]. split; [exact ST2| exact PR6].
        * eapply cj_lseg_snoc0; [exact SEG5| exact NZc| eqcells NDC| apply CJ_PRINTABLE_range; exact TYC| exact TYC| exact SVC5| exact CHC5].
  Qed.

  Theorem aloop : forall c, ALOOPc c.
  Proof. induction c as [c IH] using lt_wf_ind. apply loop_body. exact IH. Qed.

End PVL.


End CeilWrap.
(* [comment removed for export] *)
Ltac fix_lit_store :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) =>
      change (Z_to_le_bytes 8 z) with (le8 (Z_to_bv 64 z)); mem_after_store
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) =>
      change (Z_to_le_bytes 4 z) with (le4 (Z_to_bv 64 z)); mem_after_store
  | _ => idtac
  end.
