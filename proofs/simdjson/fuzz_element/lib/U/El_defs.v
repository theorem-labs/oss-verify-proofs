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
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim STree Malloc Monad Stdio StrFun SjModel AtpModel ElModel Target Prog AtpImpl.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjTape SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import Layout Exit Printf_wfile Sj_iface Sj_kit Sj_new Sj_new_t2 Sj_h_kit Atp_defs.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Definition EL_LFTOI : Z := 0x3c018.
Definition EL_EXIT : Z := 0x3c270.
Definition EL_EXIT2 : Z := 0x3c278.
Definition EL_CATCH : Z := 0x3c504.
Definition EL_CATCH_CONT : Z := 0x3c520.
Definition EL_JTAB : Z := 0x140c8.
Definition EL_GETDBL : Z := 0x3ccd8.
Definition EL_CAST : Z := 0x3d5b0.
Definition EL_BEGIN : Z := 0x3d918.
Definition EL_END : Z := 0x3d9a8.
Definition EL_ATKEY : Z := 0x3da20.
Definition EL_AT : Z := 0x3dc40.
Definition EL_ATKEY2 : Z := 0x3dce0.
Definition EL_ATKEYCI : Z := 0x3dd90.
Definition EL_OSCTOR : Z := 0x3de40.
Definition EL_OSDTOR : Z := 0x3df40.
Definition EL_PDTOR : Z := 0x3df90.
Definition EL_DUMP : Z := 0x3ff78.
Definition EL_STRNCASECMP : Z := 0xd11dc.
Definition EL_TOLOWER : Z := 0xbf504.

Definition ELF_RES : Z := 8.
Definition ELF_OS : Z := 136.
Definition ELF_ELEM : Z := 296.
Definition ELF_PARSER : Z := 312.
Definition ELF_DOC : Z := 336.
Definition ELF_VEC : Z := 392.
Definition ELF_SEL : Z := 420.
Definition ELF_FD : Z := 424.
Definition ELF_PAD : Z := 440.
Definition EL_FRAME : Z := 528.

Section WithCeilingT. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Lemma pres_X3 : forall LB SP m0 m, lx_pres LB SP [LXW_SJ; LXW_UNW] m0 m -> lx_pres LB SP [LXW_SJ; LXW_UNW; LXW_TP] m0 m.
Proof. intros LB SP m0 m H. eapply lx_pres_weaken; [exact H| lia| intros b Hb; exact Hb| intros a Ha; cbn [rin_ivs fst snd] in Ha |- *; tauto]. Qed.

Lemma tp_of_pres : forall LB SP m0 m, lx_statics m0 -> lx_pres LB SP [LXW_SJ; LXW_UNW] m0 m -> rw_cells usegs m EL_TPLOC [C8 (wz EL_GLOC)].
Proof.
  intros LB SP m0 m LXS PRES. pose proof (lx_statics_el _ LXS) as (_ & _ & _ & TP).
  eapply rw_cells_agree; [exact (agree_of_lx_pres _ _ _ _ _ PRES)| exact TP|]. intros a Ha. cbn in Ha. apply lxs_addr_client.
  - unfold lxs_addr. do 11 right. exact Ha.
  - unfold LXW_SJ, LXW_UNW, SJ_STATICS_LO, SJ_STATICS_HI. cbn [rin_ivs fst snd]. clear - Ha. lia.
Qed.

Lemma lx_statics_agree_tp : forall (P : Z -> Prop) m m',
  agree_on P m m' -> (forall a, lxs_addr a -> ~ (EL_TPLOC <= a < EL_TPLOC + 8) -> P a) ->
  rw_cells usegs m' EL_TPLOC [C8 (wz EL_GLOC)] -> lx_statics m -> lx_statics m'.
Proof.
  intros P m m' AG HP TP (A1 & A2 & A3 & A4 & A5 & A6 & (C1 & C2 & C3 & _)). unfold lx_statics, el_consts.
  unfold lxs_addr, LX_GOT_STDERR, LX_STDERR_PTR, SJ_GOT_NOTHROW, SJ_IMPL_VT24, SJ_DPI_VPTR in *.
  Ltac trt AG HP A := eapply rw_cells_agree; [exact AG| exact A| intros a Ha; cbn in Ha; apply HP; lia].
  split; [trt AG HP A1|]. split; [trt AG HP A2|]. split; [trt AG HP A3|]. split; [trt AG HP A4|]. split; [trt AG HP A5|].
  split; [eapply pj_consts_agree; [exact AG| | exact A6]; intros a Ha; apply HP; lia|].
  split; [trt AG HP C1|]. split; [trt AG HP C2|]. split; [trt AG HP C3| exact TP].
Qed.

Lemma lx_statics_pres_tp : forall LB SP m0 m, lx_pres LB SP [LXW_SJ; LXW_UNW; LXW_TP] m0 m ->
  rw_cells usegs m EL_TPLOC [C8 (wz EL_GLOC)] -> lx_statics m0 -> lx_statics m.
Proof.
  intros LB SP m0 m PRES TP LXS. eapply lx_statics_agree_tp; [exact (agree_of_lx_pres _ _ _ _ _ PRES)| | exact TP| exact LXS].
  intros a Ha NTP. apply lxs_addr_client; [exact Ha|]. pose proof (lxs_addr_lt a Ha) as [R1 _]. unfold GLOBALS_TOP in R1.
  unfold lxs_addr, LX_GOT_STDERR, LX_STDERR_PTR, SJ_GOT_NOTHROW, SJ_IMPL_VT24, SJ_DPI_VPTR in Ha.
  unfold LXW_SJ, LXW_UNW, LXW_TP, SJ_STATICS_LO, SJ_STATICS_HI. cbn [rin_ivs fst snd]. clear - Ha R1 NTP. lia.
Qed.

Lemma in_blocks_image : forall s LB m A n, RHEAP s LB m -> in_blocks LB A n -> 0 <= n -> A + n <= 0x10000 \/ 0x111000 <= A.
Proof.
  intros s LB m A n H (b & Hb & H1 & H2) Hn.
  pose proof (LH_block_range _ _ _ _ H Hb) as (R1 & R2 & R3 & R4 & R5). lia.
Qed.
End WithCeilingT.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Notation ae_T E := (Tf (ae_tws E)).
Notation ae_S E := (Tf (ae_sbs E)).
Notation ae_n E := (Z.of_nat (length (ae_tws E))).
Notation ae_sn E := (Z.of_nat (length (ae_sbs E))).

Definition el_root (E : aenv) (m : mem) (node : Z) : Prop :=
  rw_cells usegs m node [C8 (Z_to_bv 64 (ae_DOC E)); C8 (Z_to_bv 64 1)].

Lemma el_root_elem : forall E, aenv_ok E -> elem (ae_T E) (ae_S E) (ae_sn E) ck_any TAPE_MAX_DEPTH 1 (ae_n E - 1) /\ 2 < ae_n E < 2^32.
Proof. intros E OK. apply tape_wf_root. exact (ok_wf E OK). Qed.

Lemma el_elem_cases : forall E d i j, aenv_ok E -> elem (ae_T E) (ae_S E) (ae_sn E) ck_any d i j ->
  let w := ae_T E i in
  (j = i + 1 /\ (w = tword t_true 0 \/ w = tword t_false 0 \/ w = tword t_null 0))
  \/ (j = i + 2 /\ (w = tword t_i64 0 \/ w = tword t_u64 0 \/ w = tword t_dbl 0))
  \/ (j = i + 1 /\ is_str (ae_T E) (ae_S E) (ae_sn E) i /\ exists o, w = tword t_str o /\ 0 <= o < 2^56)
  \/ (exists e cv, i < e /\ e + 1 = j /\ 0 <= cv <= CNT_MAX /\ (w = cword t_arr (e + 1) cv \/ w = cword t_obj (e + 1) cv)).
Proof.
  intros E d i j OK EL. cbv zeta.
  pose proof (ok_wf E OK) as WF. destruct WF as (NR & SN & _ & _ & _).
  assert (SCAL : scalar (ae_T E) (ae_S E) (ae_sn E) i j ->
     (j = i + 1 /\ (ae_T E i = tword t_true 0 \/ ae_T E i = tword t_false 0 \/ ae_T E i = tword t_null 0))
  \/ (j = i + 2 /\ (ae_T E i = tword t_i64 0 \/ ae_T E i = tword t_u64 0 \/ ae_T E i = tword t_dbl 0))
  \/ (j = i + 1 /\ is_str (ae_T E) (ae_S E) (ae_sn E) i /\ exists o, ae_T E i = tword t_str o /\ 0 <= o < 2^56)
  \/ (exists e cv, i < e /\ e + 1 = j /\ 0 <= cv <= CNT_MAX /\ (ae_T E i = cword t_arr (e + 1) cv \/ ae_T E i = cword t_obj (e + 1) cv))).
  { intros [[-> H]|[[-> H]|[-> H]]]; [left; auto| right; left; auto| right; right; left].
    split; [reflexivity|]. split; [exact H|]. destruct H as (o & l & Hw & Hs). exists o. split; [exact Hw|].
    pose proof (str_at_bounds (ae_S E) (ae_sn E) ltac:(lia) o l Hs). lia. }
  destruct d as [|d']; cbn [elem] in EL.
  - destruct EL as [SC|[]]. exact (SCAL SC).
  - destruct EL as [SC|CO]; [exact (SCAL SC)|].
    right; right; right. destruct CO as (e & c & cv & -> & CK & HC).
    exists e, cv. unfold ck_any in CK.
    destruct HC as [(H1 & H2 & HT)|(H1 & H2 & HT)].
    + pose proof (tiles_le _ (elem_lt (ae_T E) (ae_S E) (ae_sn E) ck_any d') _ _ _ HT). split; [lia|]. split; [lia|]. split; [lia|]. left; exact H1.
    + pose proof (tiles_le _ (field_lt _ _ _ _ (elem_lt (ae_T E) (ae_S E) (ae_sn E) ck_any d')) _ _ _ HT). split; [lia|]. split; [lia|]. split; [lia|]. right; exact H1.
Qed.

Lemma el_le8_nth7 : forall v, (0 <= v < 2^64)%Z -> nth 7 (le8 (Z_to_bv 64 v)) (Z_to_bv 8 0) = Z_to_bv 8 (ttype v).
Proof.
  intros v Hv. unfold le8, word_to_le_bytes. rewrite a_u64_small by lia.
  cbn [Z_to_le_bytes nth]. rewrite !Z.shiftr_shiftr by lia. cbn [Z.add Pos.add Pos.succ]. rewrite a_shr56. reflexivity.
Qed.
Lemma el_u64s_read7 : forall (ws : list word) (i : nat), (i < length ws)%nat ->
  firstn 1 (skipn (8 * i + 7) (u64s ws)) = [nth 7 (le8 (nth i ws (Z_to_bv 64 0))) (Z_to_bv 8 0)].
Proof.
  induction ws as [|w ws IH]; intros i Hi; cbn [length] in Hi; [lia|].
  destruct i as [|i].
  - cbn [Nat.mul Nat.add u64s nth]. rewrite skipn_app, length_le8. replace (7 - 8)%nat with 0%nat by lia. cbn [skipn].
    pose proof (length_le8 w) as L. remember (le8 w) as l eqn:El. clear El.
    destruct l as [|b0 [|b1 [|b2 [|b3 [|b4 [|b5 [|b6 [|b7 [|b8 r]]]]]]]]]; cbn [length] in L; try lia. reflexivity.
  - replace (8 * S i + 7)%nat with (8 + (8 * i + 7))%nat by lia. cbn [u64s nth]. rewrite skipn_app, length_le8.
    replace (8 + (8 * i + 7) - 8)%nat with (8 * i + 7)%nat by lia. rewrite skipn_all2 by (rewrite length_le8; lia). cbn [app].
    apply IH. lia.
Qed.
Lemma tape_read_type : forall m TAPE (tws : list Z) (i : Z),
  bytes_at usegs m TAPE (u64s (map (Z_to_bv 64) tws)) -> 0 <= i < Z.of_nat (length tws) -> 0 <= Tf tws i < 2^64 ->
  ov_read_bytes usegs m (wa (TAPE + 8 * i + 7)) 1 = Some [Z_to_bv 8 (ttype (Tf tws i))].
Proof.
  intros m TAPE tws i HB Hi HT.
  replace (TAPE + 8 * i + 7) with (TAPE + (8 * i + 7)) by lia.
  rewrite (bytes_at_read usegs m TAPE _ (8 * i + 7) 1 HB); [| lia| rewrite u64s_length, length_map; lia].
  f_equal. replace (Z.to_nat (8 * i + 7)) with (8 * Z.to_nat i + 7)%nat by lia.
  rewrite el_u64s_read7 by (rewrite length_map; lia).
  rewrite <- el_le8_nth7 by exact HT. do 3 f_equal.
  unfold Tf. rewrite (map_nth (Z_to_bv 64)). reflexivity.
Qed.

Section ElemFacts.
  Variable E : aenv.
  Hypothesis OK : aenv_ok E.

  Lemma el_word_eq : forall d i j t, elem (ae_T E) (ae_S E) (ae_sn E) ck_any d i j -> 0 <= i -> j < 2^32 ->
    ae_T E i = tword t 0 -> (t = t_i64 \/ t = t_u64 \/ t = t_dbl) -> j = i + 2.
  Proof.
    intros d i j t EL Hi Hj HK Ht. pose proof (ok_wf E OK) as WF. destruct WF as (NR & SN & _ & _ & _).
    pose proof (el_elem_cases E _ _ _ OK EL) as CASES. cbv zeta in CASES. rewrite HK in CASES.
    unfold tword, cword, tword, t_true, t_false, t_null, t_i64, t_u64, t_dbl, t_str, t_arr, t_obj, CNT_MAX in *.
    destruct CASES as [[E1 [H|[H|H]]]|[[E1 [H|[H|H]]]|[(E1 & _ & o & H & Ho)|(e & cv & He & Hj' & Hcv & [H|H])]]]; lia.
  Qed.

End ElemFacts.

End WithCeiling0.
