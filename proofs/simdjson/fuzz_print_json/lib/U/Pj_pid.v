(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Spec Require Import Prelim STree Malloc Monad Stdio SjModel Target Prog.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.P Require Import Sj_h_arith.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.U Require Import Layout Exit Printf_wfile Sj_iface Sj_kit Sj_new Sj_h_kit Sj_h_alloc Sj_h_create Sj_h_active Sj_h_bom Sj_h_pid_front.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Sj Require Import SjS1Out SjStage1 SjStage1Out SjTape SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Sj Require SjAlloc.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.P Require Import Sj_stage1_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.U Require Import F_memset Sj_stage2_iface Sj_h_parse.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Lemma RHEAP_pairwise : forall s LB m, RHEAP s LB m ->
  forall L, (forall b, In b L -> In b LB) -> List.NoDup (map blk_id L) -> pairwise_disj (map (fun b => (blk_addr b, blk_size b)) L).
Proof.
  intros s LB m H L. induction L as [|b r IH]; intros HI ND; [exact I|].
  cbn [map] in ND. apply NoDup_cons_iff in ND. destruct ND as [NI ND]. cbn [map pairwise_disj]. split.
  - apply Forall_forall. intros iv Hiv. apply in_map_iff in Hiv. destruct Hiv as (b' & <- & Hb').
    assert (NE : blk_id b <> blk_id b') by (intros E; apply NI; rewrite E; apply in_map; exact Hb').
    pose proof (LH_disjoint _ _ _ b b' H (HI b ltac:(left; reflexivity)) (HI b' ltac:(right; exact Hb')) NE) as DJ.
    unfold ivl_disj. cbn [fst snd]. lia.
  - apply IH; [intros b' Hb'; apply HI; right; exact Hb'| exact ND].
Qed.

Lemma in_or_rin_app_l : forall X Y a, rin_ivs X a -> rin_ivs (X ++ Y) a.
Proof. induction X as [|iv X IH]; intros Y a H; [destruct H|]. cbn [app rin_ivs] in *. destruct H as [H|H]; [left; exact H| right; apply IH; exact H]. Qed.
Lemma in_or_rin_app_r : forall X Y a, rin_ivs Y a -> rin_ivs (X ++ Y) a.
Proof. induction X as [|iv X IH]; intros Y a H; [exact H|]. cbn [app rin_ivs]. right. apply IH. exact H. Qed.

Lemma NoDup_app_excl : forall {X} (l1 l2 : list X) x, List.NoDup (l1 ++ l2) -> In x l1 -> In x l2 -> False.
Proof.
  induction l1 as [|y r IH]; intros l2 x ND H1 H2; [destruct H1|]. cbn in ND. apply NoDup_cons_iff in ND. destruct ND as [NI ND].
  destruct H1 as [->|H1]; [apply NI; apply in_or_app; right; exact H2| eapply IH; eauto].
Qed.

Lemma RHEAP_prefix_disj : forall s L1 LB m, RHEAP s (L1 ++ LB) m ->
  forall b, In b L1 -> forall a, in_block LB a -> ~ (blk_addr b <= a < blk_addr b + blk_size b).
Proof.
  intros s L1 LB m H b Hb a (b' & Hb' & Hr) Ha.
  pose proof (LH_nodup _ _ _ H) as ND. rewrite map_app in ND.
  assert (NE : blk_id b <> blk_id b').
  { intros E. apply (NoDup_app_excl _ _ (blk_id b) ND); [apply in_map; exact Hb| rewrite E; apply in_map; exact Hb']. }
  pose proof (LH_disjoint _ _ _ b b' H ltac:(apply in_or_app; left; exact Hb) ltac:(apply in_or_app; right; exact Hb') NE) as DJ. lia.
Qed.

Lemma rw_cells_CB_split2 : forall m A (n1 n2 : nat) (bs : list byte), rw_cells usegs m A [CB (n1 + n2) bs] ->
  rw_cells usegs m A [CB n1 (firstn n1 bs)] /\ rw_cells usegs m (A + Z.of_nat n1) [CB n2 (skipn n1 bs)].
Proof.
  intros m A n1 n2 bs H.
  assert (L : length bs = (n1 + n2)%nat) by (destruct H as [[[HL _] _] _]; exact HL).
  assert (H2 : rw_cells usegs m A ([CB n1 (firstn n1 bs)] ++ [CB n2 (skipn n1 bs)])).
  { eapply rw_cells_recast; [exact H| | |].
    - cbn. rewrite firstn_length, skipn_length. repeat split; lia.
    - cbn [app cells_bytes cbytes]. rewrite !app_nil_r. apply firstn_skipn.
    - cbn. lia. }
  apply (proj1 (rw_cells_app usegs m A _ _)) in H2. cbn [cells_size csize Nat.add] in H2. rewrite Nat.add_0_r in H2. exact H2.
Qed.

Lemma s2_okres_agree : forall (P : Z -> Prop) m m' TAPE SBUF tcap scap r,
  agree_on P m m' -> (forall a, TAPE <= a < TAPE + 8 * tcap -> P a) -> (forall a, SBUF <= a < SBUF + scap -> P a) ->
  s2_okres TAPE SBUF tcap scap r m -> s2_okres TAPE SBUF tcap scap r m'.
Proof.
  intros P m m' TAPE SBUF tcap scap r AG HT HS [K|(E & tws & sbs & BT & BS & WF & RNG & LT & LS)]; [left; exact K| right].
  split; [exact E|]. exists tws, sbs. split; [| split; [| auto]].
  - eapply bytes_at_agree; [exact AG| exact BT|]. rewrite u64s_length, length_map. intros a Ha. apply HT. lia.
  - eapply bytes_at_agree; [exact AG| exact BS|]. rewrite length_map. intros a Ha. apply HS. lia.
Qed.

Definition pid_back_X (SRET PARSER : Z) : list (Z * Z) := [(PARSER + 64, PARSER + 80); (SRET, SRET + 24)].

Definition pj_res_cells (docp : Z) (r : word) (j20 : list byte) : list cell :=
  if bv_eqb r (Z_to_bv 64 0) then [C8 (Z_to_bv 64 docp); C8 (Z_to_bv 64 1); C4 (Z_to_bv 64 0); CB 4 j20]
  else [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 r; CB 4 j20].

Definition pid_R (LBall LB : list block) (q SRET PARSER : Z) (m : mem) (nas : byte) (j57 jr20 : list byte)
    (IMPL IDX OC IA TAPE SBUF cap : Z) (lbv lcapv : word) : word -> PState -> mem -> Prop :=
  fun _ s' m' =>
    RHEAP s' LBall m' /\ lx_pres LB q (pid_front_X PARSER ++ pid_back_X SRET PARSER) m m'
    /\ sj_ro m' /\ sj_statics m' true
    /\ rw_cells usegs m' (PARSER + 8) [C8 (Z_to_bv 64 IMPL)]
    /\ rw_cells usegs m' (PARSER + 24) [C8 (Z_to_bv 64 TAPE); C8 (Z_to_bv 64 SBUF); C8 (Z_to_bv 64 cap)]
    /\ rw_cells usegs m' (PARSER + 48) (p48_cells nas j57 lbv lcapv)
    /\ (exists r : word, rw_cells usegs m' SRET (pj_res_cells (PARSER + 24) r jr20)
                         /\ s2_okres TAPE SBUF (roundup64 (cap + 3)) (roundup64 (5 * (cap / 3) + 64)) r m'
                         /\ (lbv = Z_to_bv 64 0 -> r <> Z_to_bv 64 0))
    /\ (exists vptr nsi p12 nxt p28 capv md b48 b49 p50 bufv lenv docv,
          rw_cells usegs m' IMPL (impl_cells16 vptr nsi p12 (Z_to_bv 64 IDX) nxt p28 capv md b48 b49 p50 (Z_to_bv 64 OC) (Z_to_bv 64 IA) bufv lenv docv)
          /\ vptr = Z_to_bv 64 SJ_DPI_VPTR)
    /\ rblock_range TAPE (8 * roundup64 (cap + 3)) /\ rblock_range SBUF (roundup64 (5 * (cap / 3) + 64)).

Lemma mod8_of_mod16 : forall A, A mod 16 = 0 -> A mod 8 = 0.
Proof.
  intros A H. pose proof (Z.div_mod A 16 ltac:(lia)) as E. rewrite H, Z.add_0_r in E. rewrite E.
  replace (16 * (A / 16)) with ((2 * (A / 16)) * 8) by lia. apply Z.mod_mul. lia.
Qed.

Section Proofs.
  Hypothesis HM : rmalloc_stmt.
  Hypothesis HF : rfree_stmt.
  Hypothesis S2 : stage2t_stmt.

  Lemma pj_pid_copy_cps : forall {A} (k : bptr -> M PState A) (Q : A -> PState -> machine_state -> Prop)
      (ra0 gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (q : Z)
      (F : bvmap 5 word) (fc : bv 32) (s00 : PState) (LB : list block) (lo B : Z) (m00 : mem) (SRET PARSER D : Z) (d : list Z) (j57 : list byte)
      (psb ptp pim pix poc pia : bptr) (s : PState) (ms : machine_state) (jr0 jr8 jr16 jr20 : list byte),
    pid_mid ra0 q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s00 LB lo B m00 SRET PARSER D (zlength d) (Z.max (zlength d) 32) (Z_to_bv 8 0) j57 psb ptp pim pix poc pia s ms ->
    zlength d <= 1048512 ->
    RHEAP s00 LB m00 -> payload_ok m00 LB D d -> frm0 fc -> q <= B -> B < 2^63 -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= q - (80 + 32 + SJ_S2_STACK) -> 0 <= q < 2^64 -> q mod 16 = 0 ->
    q <= SRET -> SRET + 24 <= PARSER -> PARSER + 80 <= B -> PARSER mod 8 = 0 ->
    rw_cells usegs m00 SRET [CB 8 jr0; CB 8 jr8; CB 4 jr16; CB 4 jr20] ->
    (forall pcp s' ms',
        (exists IMPL IDX OC IA TAPE SBUF COPY,
          hpostF ra0 q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s00 lo B
            (pid_R ((pcp, COPY, zlength d + 64) :: (pia, IA, 1024) :: (poc, OC, 8192) :: (pix, IDX, 4 * (roundup64 (Z.max (zlength d) 32) + 9)) :: (pim, IMPL, 96)
                      :: (ptp, TAPE, 8 * roundup64 (Z.max (zlength d) 32 + 3)) :: (psb, SBUF, roundup64 (5 * (Z.max (zlength d) 32 / 3) + 64)) :: LB)
                   LB q SRET PARSER m00 (Z_to_bv 8 0) j57 jr20 IMPL IDX OC IA TAPE SBUF (Z.max (zlength d) 32) (Z_to_bv 64 COPY) (Z_to_bv 64 (zlength d))) s' ms') ->
        implM usegs (k pcp) s' Q ms') ->
    implM usegs (mbind (newnt lops (zlength d + 64)) (fun cp => mbind (parse_model (SjAlloc.strip_bom d)) (fun _ => k cp))) s Q ms.
  Proof.
    intros A k Q. intros until jr20. intros MID LEN HEAP00 PL FRM QB B63 CEIL GLO LO Hq Q16 QS SP PB ALP SRETC HK.
    unfold pid_mid in MID.
    destruct MID as (x1 & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m & errv & SBUF & TAPE & IMPL & IDX & OC & IA & ws & jsb & jtp & joc & jia
                     & p12 & p28 & p50 & -> & MI & ST & ERR & AUX & FA & SO & HEAP & PRES0 & (GOT & VT24 & VTD) & SJS & FR & PIMPL & DOCC & P48 & THISC & ARR & LWS
                     & BLKSB & BLKTP & BLKOC & BLKIA & BRSB & BRTP & BRIM & BRIX & BROC & BRIA).
    unfold SJ_PID_MID, SJ_S2_STACK, SJ_S2_FRAMES, RMALLOC_STACK, GLOBALS_TOP, p48_cells, pid_frame in *.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof CEIL as CEIL'. unfold OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Spec.Malloc.MCEIL in CEIL; try (pose proof alloc_ceiling_range as CEIL_RANGE__).
    set (len := zlength d) in *. assert (LEN0 : 0 <= len) by (subst len; unfold zlength; lia).
    set (cap := Z.max len 32) in *. assert (CAP : 32 <= cap <= 1048512) by (subst cap; lia).

    assert (BLB : forall a, in_block LB a -> a < alloc_ceiling).
    { intros a (b & Hb & Hr). pose proof (LH_block_range _ _ _ _ HEAP00 Hb) as (_ & _ & _ & BC & _).
      unfold OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Spec.Malloc.MCEIL in BC. lia. }
    assert (PL1 : payload_ok m LB D d).
    { eapply payload_ok_agree; [exact (agree_of_lx_pres _ _ _ _ _ PRES0)| exact PL|].
      intros b a Hb Ha. split; [| right; left; exists b; split; assumption].
      assert (AB : a < alloc_ceiling) by (apply BLB; exists b; split; assumption).
      unfold pid_front_X, LXW_SJ, SJ_STATICS_LO, SJ_STATICS_HI. cbn [rin_ivs fst snd].
      pose proof (LH_block_range _ _ _ _ HEAP00 Hb) as (_ & _ & _ & _ & BS). clear - Ha AB BS CEIL LO SP QS. lia. }
    apply (rw_cells_agree _ _ _ _ _ (agree_of_lx_pres _ _ _ _ _ PRES0)) in SRETC;
      [| intros a Ha; cbn in Ha; split; [unfold pid_front_X, LXW_SJ, SJ_STATICS_LO, SJ_STATICS_HI; cbn [rin_ivs fst snd]; clear - Ha SP QS LO GLO; lia| left; lia]].
    pose proof (munch_refl [(q - 80, q); (PARSER + 64, PARSER + 80); (SRET, SRET + 24)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
    assert (ELX : LX_ERRNO = 977220) by reflexivity. rewrite ELX in ERR.
    unfold SJ_GOT_NOTHROW, SJ_NOTHROW_TAG in GOT. unfold SJ_IMPL_VT24, SJ_CREATE_DPI in VT24. unfold SJ_DPI_VPTR, dpi_vtable_cells in VTD.
    unfold impl_cells16, SJ_DPI_VPTR in THISC.
    unfold implM. iprefix.

    step. if_false. step. step. if_true. step. step. step.
    if_cases K0; zify_cond K0; [exfalso; rewrite ?unsigned_lit in K0 by lia; lia|]. clear K0.

    do 4 step.
    ihere. to_implM. eapply implM_bind.
    { eapply (opnew_arr_nt_proof HM) with (B := B) (lo := lo);
        [exact HEAP| exact AUX| lia| exact ST| exact CEIL'| unfold SJ_OPNEW_STACK, RMALLOC_STACK; lia| rewrite ELX; exact ERR| exact MI| lia| lia]. }
    cbv beta. intros pcp s1' ms1 PO. unfold opnew_postZ in PO.
    destruct PO as (r5 & r6 & r7 & r11 & r12 & r13 & r14 & r15 & r16 & r17 & r28 & r29 & r30 & r31 & m1 & errv1 & COPY & jcp
                    & -> & MI1 & ST1 & ERR1 & AUX1 & HP & FA1 & SO1 & BRCP & HEAP1 & BLKCP).
    replace (ret_pc (Z_to_bv 64 251488)) with (Z_to_bv 64 251488) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (agree_of_heap_pres _ _ _ _ HP) as AG.
    apply (rw_cells_agree _ _ _ _ _ AG) in FR; [| intros a Ha; left; cbn in Ha; lia].
    apply (rw_cells_agree _ _ _ _ _ AG) in PIMPL; [| intros a Ha; left; cbn in Ha; lia].
    apply (rw_cells_agree _ _ _ _ _ AG) in DOCC; [| intros a Ha; left; cbn in Ha; lia].
    apply (rw_cells_agree _ _ _ _ _ AG) in P48; [| intros a Ha; left; cbn in Ha; lia].
    apply (rw_cells_agree _ _ _ _ _ AG) in SRETC; [| intros a Ha; left; cbn in Ha; lia].
    apply (rw_cells_agree _ _ _ _ _ AG) in GOT;
      [| intros a Ha; right; left; cbn in Ha; unfold ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RATP, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP; lia].
    apply (rw_cells_agree _ _ _ _ _ AG) in VTD;
      [| intros a Ha; right; left; cbn in Ha; unfold ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RATP, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP; lia].
    apply (rw_cells_agree _ _ _ _ _ AG) in VT24;
      [| intros a Ha; right; left; cbn in Ha; unfold ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RATP, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP; lia].
    apply (rw_cells_agree _ _ _ _ _ AG) in THISC;
      [| intros a Ha; right; right; exists (pim, IMPL, 96); split; [right; right; right; left; reflexivity| cbn in Ha |- *; lia]].
    pose proof (u32arr_bound _ _ _ _ ARR) as ARRB.
    apply (u32arr_agree _ _ _ _ _ AG) in ARR;
      [| intros a Ha; right; right; exists (pix, IDX, 4 * (roundup64 cap + 9)); split; [right; right; left; reflexivity| cbn [blk_addr blk_size fst snd]; rewrite LWS in Ha; clear - Ha CAP; pose proof (roundup64_ge cap); lia]].
    apply (rw_cells_agree _ _ _ _ _ AG) in BLKSB;
      [| intros a Ha; right; right; eexists; split; [do 5 right; left; reflexivity| cbn [blk_addr blk_size fst snd cells_size csize Nat.add] in Ha |- *;
           clear - Ha CAP; pose proof (roundup64_ge (5 * (cap / 3) + 64)); assert (0 <= cap / 3) by (apply Z.div_pos; lia); lia]].
    apply (rw_cells_agree _ _ _ _ _ AG) in BLKTP;
      [| intros a Ha; right; right; eexists; split; [do 4 right; left; reflexivity| cbn [blk_addr blk_size fst snd cells_size csize Nat.add] in Ha |- *;
           clear - Ha CAP; pose proof (roundup64_ge (cap + 3)); lia]].
    apply (rw_cells_agree _ _ _ _ _ AG) in BLKOC;
      [| intros a Ha; right; right; eexists; split; [right; left; reflexivity| cbn [blk_addr blk_size fst snd cells_size csize Nat.add] in Ha |- *; lia]].
    apply (rw_cells_agree _ _ _ _ _ AG) in BLKIA;
      [| intros a Ha; right; right; eexists; split; [left; reflexivity| cbn [blk_addr blk_size fst snd cells_size csize Nat.add] in Ha |- *; lia]].
    assert (PL2 : payload_ok m1 LB D d).
    { eapply payload_ok_heap; [| exact PL1]. eapply rheap_pres_weaken; [exact HP| apply Z.le_refl| intros b Hb; do 6 right; exact Hb]. }
    assert (SJS1 : sj_statics m1 true).
    { destruct (statics_heap _ _ _ _ HP ltac:(unfold GLOBALS_TOP; lia)) as (_ & K & _). apply K. exact SJS. }
    clear AG PL1 SJS.
    pose proof BRCP as (CP0 & _ & _ & CPC & CPS). unfold OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Spec.Malloc.MCEIL in CPC.
    replace (Z.to_nat (len + 64)) with (Z.to_nat len + 64)%nat in BLKCP by lia.
    apply rw_cells_CB_split2 in BLKCP. destruct BLKCP as [COPYA PAD]. rewrite Z2Nat.id in PAD by lia.
    assert (PRES1 : lx_pres LB q (pid_back_X SRET PARSER) m m1).
    { apply lx_pres_of_heap_pres. eapply rheap_pres_weaken; [exact HP| lia| intros b Hb; do 6 right; exact Hb]. }
    clear HP MU WM.
    pose proof (munch_refl [(q - 80, q); (PARSER + 64, PARSER + 80); (SRET, SRET + 24)]%Z m1) as MU. pose proof (wmono_refl usegs m1) as WM.
    rewrite ELX in ERR1.
    unfold implM. iprefix.

    step. if_cases K1; zify_cond K1; [exfalso; rewrite ?unsigned_lit in K1 by lia; lia|]. clear K1.

    step. zstep. step.
    rewrite (ZBridge.zb_lxor_ones COPY) by (unfold alloc_ceiling in *; lia).
    if_cases KN; zify_cond KN; [exfalso; rewrite ?unsigned_lit in KN by (unfold alloc_ceiling in *; lia); unfold alloc_ceiling in *; lia|]. clear KN.
    do 4 step.
    eapply evt_cut.
    { eapply (memset_callZ) with (D := COPY + len) (C := 0) (N := 64) (junk := skipn (Z.to_nat len) jcp); [exact PAD| assumption| lia| lia| lia| lia]. }
    intros ms' PO. unfold memset_postZ in PO.
    destruct PO as (u5 & u6 & u7 & u11 & u12 & u13 & u14 & u15 & u16 & u17 & u28 & u29 & u30 & u31 & m2 & -> & MU2 & WM2 & MI2 & PAD2).
    replace (ret_pc (Z_to_bv 64 251520)) with (Z_to_bv 64 251520) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (LH_head_disj _ _ _ _ _ _ HEAP1) as DJCP.
    assert (DJLB : forall a, in_block LB a -> ~ (COPY <= a < COPY + (len + 64))).
    { intros a Ha. apply DJCP. eapply in_block_incl; [| exact Ha]. intros b Hb. do 6 right. exact Hb. }
    pose proof (agree_on_of_munch _ _ _ MU2 WM2) as AG12.

    apply (rw_cells_agree _ _ _ _ _ AG12) in FR; [| intros a Ha; cbn in Ha; cbn [outside]; split; [clear - Ha CPC CEIL LO; lia| exact I]].
    apply (rw_cells_agree _ _ _ _ _ AG12) in P48; [| intros a Ha; cbn in Ha; cbn [outside]; split; [clear - Ha CPC CEIL LO QS SP; lia| exact I]].
    pose proof (rw_cells_bound _ _ _ _ COPYA) as CAB. cbn [cells_size csize Nat.add] in CAB.
    assert (COPYA2 : rw_cells usegs m2 COPY [CB (Z.to_nat len) (firstn (Z.to_nat len) jcp)]).
    { eapply (rw_cells_agree _ _ _ _ _ AG12); [exact COPYA|]. intros a Ha; cbn [cells_size csize Nat.add] in Ha; cbn [outside]; split; [clear - Ha LEN0; lia| exact I]. }
    assert (PL3 : payload_ok m2 LB D d).
    { eapply payload_ok_agree; [exact AG12| exact PL2|]. intros b a Hb Ha. cbn [outside]. split; [| exact I].
      intros Hc. apply (DJLB a); [exists b; split; assumption| clear - Hc LEN0; lia]. }
    assert (HEAP2 : RHEAP s1' ((pcp, COPY, len + 64) :: (pia, IA, 1024) :: (poc, OC, 8192) :: (pix, IDX, 4 * (roundup64 cap + 9)) :: (pim, IMPL, 96)
                      :: (ptp, TAPE, 8 * roundup64 (cap + 3)) :: (psb, SBUF, roundup64 (5 * (cap / 3) + 64)) :: LB) m2).
    { eapply LH_frame; [exact HEAP1| exact MU2| exact WM2|].
      constructor; [eapply (W_ok_block _ (pcp, COPY, len + 64)); [left; reflexivity| cbn; lia| cbn; lia]| constructor]. }
    assert (AUX2 : rauxv_ok m2 B).
    { eapply rauxv_ok_frame; [exact AUX1| exact MU2| exact WM2|]. constructor; [cbn; unfold RAUXV_CELL; clear - CPC CPS CEIL LO QB LEN0; lia| constructor]. }
    assert (CLICP : forall lo' hi', COPY <= lo' -> hi' <= COPY + (len + 64) ->
              forall a, 0 <= a < 2^64 -> lx_client LB q (pid_back_X SRET PARSER) a -> ~ (lo' <= a < hi')).
    { intros lo' hi' H1 H2 a Ha [HX HC] Hc. destruct HC as [HC|[HC|HC]]; [clear - HC Hc H2 CPC CEIL LO; lia| apply (DJLB a HC); lia| clear - HC Hc H1 H2 CPS; lia]. }
    assert (PRES2 : lx_pres LB q (pid_back_X SRET PARSER) m m2).
    { eapply lx_pres_trans; [exact PRES1|]. eapply lx_pres_of_munch; [exact MU2| exact WM2|].
      intros a Ha HC. cbn [outside]. split; [| exact I]. apply (CLICP (COPY + len) (COPY + len + 64)); [lia| lia| exact Ha| exact HC]. }
    clear MU2 WM2 PRES1 HEAP1 AUX1.
    pose proof (munch_refl [(q - 80, q); (PARSER + 64, PARSER + 80)]%Z m2) as MU3. pose proof (wmono_refl usegs m2) as WM3.

    step. step. step. if_true. step.
    if_cases K2; zify_cond K2; [exfalso; rewrite ?unsigned_lit in K2 by lia; lia|]. clear K2.
    do 5 step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
    assert (PL4 : payload_ok m3 LB D d).
    { eapply payload_ok_agree; [exact (agree_on_of_munch _ _ _ MU3 WM3)| exact PL3|]. intros b a Hb Ha. cbn [outside].
      assert (AB : a < alloc_ceiling) by (apply BLB; exists b; split; assumption). clear - AB CEIL LO QS SP. lia. }
    clear PL3. destruct PL4 as (PB3 & PRNG & D0 & DN & DLEN & PIN).
    assert (LPB : length (to_bytes d) = Z.to_nat len) by (rewrite to_bytes_length; subst len; unfold zlength; lia).
    eapply evt_cut.
    { eapply (memcpy_callZ) with (Dst := COPY) (Src := D) (N := len) (src := to_bytes d) (junk := firstn (Z.to_nat len) jcp);
        [exact PB3| exact LPB| exact COPYA2| | lia| subst len; lia| lia| assumption].
      destruct PIN as [E|(b & Hb & Hb1 & Hb2)]; [subst d; subst len; unfold zlength; cbn [length Z.of_nat]; lia|].
      destruct b as [[pb Ab] nb].
      pose proof (LH_head_sep _ _ _ _ _ _ _ _ _ HEAP2 ltac:(do 6 right; exact Hb)) as SEPB.
      cbn [blk_addr blk_size fst snd] in *. clear - SEPB Hb1 Hb2 LEN0. subst len. lia. }
    intros ms' PO. unfold memcpy_postZ in PO.
    destruct PO as (v5 & v6 & v7 & v11 & v12 & v13 & v14 & v15 & v16 & v17 & v28 & v29 & v30 & v31 & m4 & -> & MU4 & WM4 & MI4 & COPYB & PB4).
    replace (ret_pc (Z_to_bv 64 251572)) with (Z_to_bv 64 251572) by (symmetry; apply ret_pc_even; [lia| reflexivity]).

    assert (HEAP4 : RHEAP s1' ((pcp, COPY, len + 64) :: (pia, IA, 1024) :: (poc, OC, 8192) :: (pix, IDX, 4 * (roundup64 cap + 9)) :: (pim, IMPL, 96)
                      :: (ptp, TAPE, 8 * roundup64 (cap + 3)) :: (psb, SBUF, roundup64 (5 * (cap / 3) + 64)) :: LB) m4).
    { eapply LH_frame; [eapply LH_frame; [exact HEAP2| exact MU3| exact WM3|]| exact MU4| exact WM4|].
      - constructor; [apply W_ok_stack; cbn; lia|]. constructor; [apply W_ok_stack; cbn; lia| constructor].
      - constructor; [eapply (W_ok_block _ (pcp, COPY, len + 64)); [left; reflexivity| cbn; lia| cbn; lia]| constructor]. }
    assert (AUX4 : rauxv_ok m4 B).
    { eapply rauxv_ok_frame; [eapply rauxv_ok_frame; [exact AUX2| exact MU3| exact WM3|]| exact MU4| exact WM4|].
      - constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor].
      - constructor; [cbn; unfold RAUXV_CELL; clear - CPC CPS CEIL LO QB LEN0; lia| constructor]. }
    assert (PRES4 : lx_pres LB q (pid_back_X SRET PARSER) m m4).
    { eapply lx_pres_trans; [exact PRES2|]. eapply lx_pres_trans; eapply lx_pres_of_munch; [exact MU3| exact WM3| | exact MU4| exact WM4|].
      - intros a Ha [HX HC]. unfold pid_back_X in HX. cbn [rin_ivs fst snd] in HX. cbn [outside]. split; [| split; [lia| exact I]].
        destruct HC as [HC|[HC|HC]]; [lia| specialize (BLB a HC); lia| lia].
      - intros a Ha HC. cbn [outside]. split; [| exact I]. apply (CLICP COPY (COPY + len)); [lia| lia| exact Ha| exact HC]. }

    set (WALL := [(COPY, COPY + (len + 64)); (q - 80, q); (PARSER + 64, PARSER + 80)]%Z).
    assert (AG14 : agree_on (fun a => outside WALL a) m1 m4).
    { eapply agree_on_trans; [eapply agree_on_mono; [exact AG12|]| eapply agree_on_trans; eapply agree_on_mono;
        [exact (agree_on_of_munch _ _ _ MU3 WM3)| | exact (agree_on_of_munch _ _ _ MU4 WM4)|]];
      intros a (H1 & H2 & H3 & _); cbn [outside fst snd] in *; repeat split; clear - H1 H2 H3 LEN0; lia. }
    pose proof (agree_on_of_munch _ _ _ MU4 WM4) as AG34.
    apply (rw_cells_agree _ _ _ _ _ AG34) in FR; [| intros a Ha; cbn in Ha; cbn [outside]; split; [clear - Ha CPC CEIL LO; lia| exact I]].
    apply (rw_cells_agree _ _ _ _ _ AG34) in P48; [| intros a Ha; cbn in Ha; cbn [outside]; split; [clear - Ha CPC CEIL LO QS SP; lia| exact I]].
    assert (PAD4 : rw_cells usegs m4 (COPY + len) [CB (Z.to_nat 64) (repeat (Z_to_bv 8 (0 mod 256)) (Z.to_nat 64))]).
    { eapply (rw_cells_agree _ _ _ _ _ AG34); [exact PAD2|].
      intros a Ha; cbn in Ha; cbn [outside]; repeat split; clear - Ha CPC CEIL LO QS SP LEN0; lia. }
    subst WALL.
    apply (rw_cells_agree _ _ _ _ _ AG14) in PIMPL; [| intros a Ha; cbn in Ha; cbn [outside]; repeat split; clear - Ha CPC CEIL LO QS SP; lia].
    apply (rw_cells_agree _ _ _ _ _ AG14) in DOCC; [| intros a Ha; cbn in Ha; cbn [outside]; repeat split; clear - Ha CPC CEIL LO QS SP; lia].
    apply (rw_cells_agree _ _ _ _ _ AG14) in SRETC; [| intros a Ha; cbn in Ha; cbn [outside]; repeat split; clear - Ha CPC CEIL LO QS SP; lia].
    apply (rw_cells_agree _ _ _ _ _ AG14) in GOT; [| intros a Ha; cbn in Ha; cbn [outside]; repeat split; clear - Ha CPS CEIL LO GLO QS SP; lia].
    apply (rw_cells_agree _ _ _ _ _ AG14) in VTD; [| intros a Ha; cbn in Ha; cbn [outside]; repeat split; clear - Ha CPS CEIL LO GLO QS SP; lia].
    apply (rw_cells_agree _ _ _ _ _ AG14) in VT24; [| intros a Ha; cbn in Ha; cbn [outside]; repeat split; clear - Ha CPS CEIL LO GLO QS SP; lia].
    apply (rw_cells_agree _ _ _ _ _ AG14) in ERR1; [| intros a Ha; cbn in Ha; cbn [outside]; repeat split; clear - Ha CPS CEIL LO GLO QS SP; lia].
    assert (SJS4 : sj_statics m4 true).
    { eapply sj_statics_agree; [exact AG14| | exact SJS1]. intros a Ha. unfold sjs_addr, SJ_STATICS_LO, SJ_STATICS_HI in Ha.
      cbn [outside]; repeat split; clear - Ha CPS CEIL LO GLO QS SP; lia. }
    assert (ST4 : stk usegs m4 lo (q + -80)).
    { eapply stk_agree; [exact AG14| exact ST1|]. intros a Ha. cbn [outside]; repeat split; clear - Ha CPC CEIL LO QS SP; lia. }
    pose proof BRIM as (IM0 & _ & _ & IMC & IMS). pose proof BRIX as (IX0 & _ & _ & IXC & _). pose proof BRSB as (SB0 & _ & _ & SBC & _).
    pose proof BRTP as (TP0 & _ & _ & TPC & _). pose proof BROC as (OC0 & _ & _ & OCC & _). pose proof BRIA as (IA0 & _ & _ & IAC & _).
    unfold OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Spec.Malloc.MCEIL in IMC, IXC, SBC, TPC, OCC, IAC.
    pose proof (roundup64_ge cap) as RC1. pose proof (roundup64_ge (cap + 3)) as RC2. pose proof (roundup64_ge (5 * (cap / 3) + 64)) as RC3.
    pose proof (roundup64_lt cap) as RC4. pose proof (roundup64_lt (cap + 3)) as RC5. pose proof (roundup64_lt (5 * (cap / 3) + 64)) as RC6.
    assert (D3 : 0 <= cap / 3 <= cap) by (split; [apply Z.div_pos; lia| apply Z.div_le_upper_bound; lia]).
    apply (rw_cells_agree _ _ _ _ _ AG14) in THISC.
    2:{ intros a Ha; cbn in Ha; cbn [outside]. pose proof (LH_head_sep _ _ _ _ _ _ _ _ _ HEAP4 ltac:(do 3 right; left; reflexivity)) as SEP.
        repeat split; clear - Ha SEP IMC CEIL LO QS SP; lia. }
    apply (u32arr_agree _ _ _ _ _ AG14) in ARR.
    2:{ intros a Ha; rewrite LWS in Ha; cbn [outside]. pose proof (LH_head_sep _ _ _ _ _ _ _ _ _ HEAP4 ltac:(do 2 right; left; reflexivity)) as SEP.
        repeat split; clear - Ha SEP IXC CEIL LO QS SP RC1 CAP; lia. }
    apply (rw_cells_agree _ _ _ _ _ AG14) in BLKSB.
    2:{ intros a Ha; cbn [cells_size csize Nat.add] in Ha; cbn [outside]. pose proof (LH_head_sep _ _ _ _ _ _ _ _ _ HEAP4 ltac:(do 5 right; left; reflexivity)) as SEP.
        repeat split; clear - Ha SEP SBC CEIL LO QS SP RC3 D3 CAP; lia. }
    apply (rw_cells_agree _ _ _ _ _ AG14) in BLKTP.
    2:{ intros a Ha; cbn [cells_size csize Nat.add] in Ha; cbn [outside]. pose proof (LH_head_sep _ _ _ _ _ _ _ _ _ HEAP4 ltac:(do 4 right; left; reflexivity)) as SEP.
        repeat split; clear - Ha SEP TPC CEIL LO QS SP RC2 CAP; lia. }
    apply (rw_cells_agree _ _ _ _ _ AG14) in BLKOC.
    2:{ intros a Ha; cbn [cells_size csize Nat.add] in Ha; cbn [outside]. pose proof (LH_head_sep _ _ _ _ _ _ _ _ _ HEAP4 ltac:(do 1 right; left; reflexivity)) as SEP.
        repeat split; clear - Ha SEP OCC CEIL LO QS SP; lia. }
    apply (rw_cells_agree _ _ _ _ _ AG14) in BLKIA.
    2:{ intros a Ha; cbn [cells_size csize Nat.add] in Ha; cbn [outside]. pose proof (LH_head_sep _ _ _ _ _ _ _ _ _ HEAP4 ltac:(left; reflexivity)) as SEP.
        repeat split; clear - Ha SEP IAC CEIL LO QS SP; lia. }
    clear AG12 AG14 AG34 MU3 WM3 MU4 WM4 PRES2 HEAP2 AUX2 SJS1 ST1 PAD2 COPYA COPYA2 PAD PB3 MI2 MU WM.

    assert (PADDED : bytes_at usegs m4 COPY (padded_bytes d)).
    { unfold padded_bytes. apply bytes_at_app. split.
      - apply rw_cells_CB_bytes_at in COPYB. exact COPYB.
      - apply rw_cells_CB_bytes_at in PAD4. unfold zbytes. change (map (Z_to_bv 8) d) with (to_bytes d). rewrite LPB, Z2Nat.id by lia. exact PAD4. }
    lazymatch goal with |- evt _ ?QQ _ =>
      assert (GO2 : forall (BUF : Z) (bs : list Z) xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 xs6,
                 SjAlloc.strip_bom d = bs -> bytes_ok bs -> COPY <= BUF -> BUF + blen bs = COPY + len -> bytes_at usegs m4 BUF (padded_bytes bs) ->
                 evt usegs QQ
                   (MS (mkR xra (Z_to_bv 64 (q + -80)) gp (Z_to_bv 64 RATP) xt0 xt1 xt2 (Z_to_bv 64 SRET) (Z_to_bv 64 (PARSER + 24)) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
                            (Z_to_bv 64 (blen bs)) (Z_to_bv 64 BUF) (Z_to_bv 64 PARSER) (Z_to_bv 64 (PARSER + 8)) xs6 (Z_to_bv 64 COPY) (Z_to_bv 64 cap)
                            s9 s10 s11 xt3 xt4 xt5 xt6)
                       F (Z_to_bv 64 0x3d6e8) fc None m4 (seg_rom usegs))) end.
    2:{
        step. step. step.
        assert (BLD : blen d = len) by reflexivity.
        if_cases K3; zify_cond K3.
        -
          rewrite ?unsigned_lit in K3 by lia.
          eapply evt_eq; [| eapply (GO2 COPY d)]; [cbv delta [mkR]; rewrite BLD; reflexivity| | exact PRNG| lia| lia| exact PADDED].
          apply strip_bom_short. subst len. unfold zlength in K3. lia.
        - rewrite ?unsigned_lit in K3 by lia.
          destruct d as [|c0 [|c1 [|c2 r]]]; try (subst len; unfold zlength in K3; cbn [length] in K3; lia).

          do 6 step.
          inversion PRNG as [|? ? R0 PR1]; subst. inversion PR1 as [|? ? R1 PR2]; subst. inversion PR2 as [|? ? R2 PR3]; subst.
          eapply evt_cut.
          { eapply (bom_spec) with (A := COPY) (c0 := c0) (c1 := c1) (c2 := c2); [assumption| | exact R0| exact R1| exact R2| lia| lia].
            unfold padded_bytes, zbytes in PADDED. cbn [map app] in PADDED.
            change (Z_to_bv 8 c0 :: Z_to_bv 8 c1 :: Z_to_bv 8 c2 :: (map (Z_to_bv 8) r ++ repeat (Z_to_bv 8 0) 64))
              with ([Z_to_bv 8 c0; Z_to_bv 8 c1; Z_to_bv 8 c2] ++ (map (Z_to_bv 8) r ++ repeat (Z_to_bv 8 0) 64)) in PADDED.
            apply bytes_at_app in PADDED. exact (proj1 PADDED). }
          intros ms' PO. unfold bom_post in PO.
          destruct PO as (y5 & y6 & y7 & y10 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & -> & [(-> & -> & -> & ->)|(NZ & NM)]).
          +
            replace (ret_pc (Z_to_bv 64 251608)) with (Z_to_bv 64 251608) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
            step. if_false. step.
            step. if_cases KG; zify_cond KG; [exfalso; rewrite ?unsigned_lit in KG by lia; lia|]. clear KG.
            step.
            eapply evt_eq; [| eapply (GO2 (COPY + 3) r)]; [| apply strip_bom_hit| exact PR3| lia| | ].
            * cbv delta [mkR]. replace (blen r) with (len + -3) by (subst len; unfold blen, zlength; cbn [length]; lia). reflexivity.
            * subst len. unfold blen, zlength. cbn [length]. lia.
            * unfold padded_bytes, zbytes in PADDED. cbn [map app] in PADDED.
              change (Z_to_bv 8 239 :: Z_to_bv 8 187 :: Z_to_bv 8 191 :: (map (Z_to_bv 8) r ++ repeat (Z_to_bv 8 0) 64))
                with ([Z_to_bv 8 239; Z_to_bv 8 187; Z_to_bv 8 191] ++ (map (Z_to_bv 8) r ++ repeat (Z_to_bv 8 0) 64)) in PADDED.
              apply bytes_at_app in PADDED. exact (proj2 PADDED).
          + replace (ret_pc (Z_to_bv 64 251608)) with (Z_to_bv 64 251608) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
            step. rewrite NZ. cbn [negb].
            eapply evt_eq; [| eapply (GO2 COPY (c0 :: c1 :: c2 :: r))]; [cbv delta [mkR]; rewrite BLD; reflexivity| | exact PRNG| lia| lia| exact PADDED].
            apply strip_bom_miss. exact NM. }
    intros BUF bs xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 xs6 EBS BOKS BUF0 BUFL BUFB.
    pose proof (padded_bytes_blen bs) as PBL.
    assert (BL0 : 0 <= blen bs) by (unfold blen; lia).
    clear COPYB PAD4 PB4 PADDED.
    hide BLKSB. hide BLKTP. hide BLKOC. hide BLKIA. hide ARR. hide BUFB.
    pose proof (munch_refl [(q - 80, q); (IMPL, IMPL + 96)]%Z m4) as MU. pose proof (wmono_refl usegs m4) as WM.

    step. step. step. if_false. step. step.
    if_cases KI; zify_cond KI; [exfalso; rewrite ?unsigned_lit in KI by lia; lia|]. clear KI.
    zstep. step. rewrite (land7_aligned IMPL) by (destruct BRIM as (? & AL16 & _); first [lia| exact AL16]). if_false.
    step. hstep. do 5 step.
    replace (ret_pc (Z_to_bv 64 SJ_DPI_PARSE)) with (Z_to_bv 64 SJ_DPI_PARSE) by (symmetry; apply ret_pc_even; [unfold SJ_DPI_PARSE; lia| reflexivity]).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
    pose proof (RHEAP_pull _ [(pcp, COPY, len + 64); (pia, IA, 1024); (poc, OC, 8192); (pix, IDX, 4 * (roundup64 cap + 9))] _ _ _ HEAP4) as HEAPIM. cbn [app] in HEAPIM.
    pose proof (agree_on_of_munch _ _ _ MU WM) as AG.
    unhide BLKSB. apply (rw_cells_agree _ _ _ _ _ AG) in BLKSB.
    2:{ intros a Ha; cbn [cells_size csize Nat.add] in Ha; cbn [outside]. pose proof (LH_head_sep _ _ _ _ _ _ _ _ _ HEAPIM ltac:(do 5 right; left; reflexivity)) as SEP.
        repeat split; clear - Ha SEP SBC CEIL LO RC3 D3 CAP; lia. }
    unhide BLKTP. apply (rw_cells_agree _ _ _ _ _ AG) in BLKTP.
    2:{ intros a Ha; cbn [cells_size csize Nat.add] in Ha; cbn [outside]. pose proof (LH_head_sep _ _ _ _ _ _ _ _ _ HEAPIM ltac:(do 4 right; left; reflexivity)) as SEP.
        repeat split; clear - Ha SEP TPC CEIL LO RC2 CAP; lia. }
    unhide BLKOC. apply (rw_cells_agree _ _ _ _ _ AG) in BLKOC.
    2:{ intros a Ha; cbn [cells_size csize Nat.add] in Ha; cbn [outside]. pose proof (LH_head_sep _ _ _ _ _ _ _ _ _ HEAPIM ltac:(do 2 right; left; reflexivity)) as SEP.
        repeat split; clear - Ha SEP OCC CEIL LO; lia. }
    unhide BLKIA. apply (rw_cells_agree _ _ _ _ _ AG) in BLKIA.
    2:{ intros a Ha; cbn [cells_size csize Nat.add] in Ha; cbn [outside]. pose proof (LH_head_sep _ _ _ _ _ _ _ _ _ HEAPIM ltac:(do 1 right; left; reflexivity)) as SEP.
        repeat split; clear - Ha SEP IAC CEIL LO; lia. }
    unhide ARR. apply (u32arr_agree _ _ _ _ _ AG) in ARR.
    2:{ intros a Ha; rewrite LWS in Ha; cbn [outside]. pose proof (LH_head_sep _ _ _ _ _ _ _ _ _ HEAPIM ltac:(do 3 right; left; reflexivity)) as SEP.
        repeat split; clear - Ha SEP IXC CEIL LO RC1 CAP; lia. }
    unhide BUFB. apply (bytes_at_agree _ _ _ _ _ AG) in BUFB.
    2:{ intros a Ha; rewrite PBL in Ha; cbn [outside]. pose proof (LH_head_sep _ _ _ _ _ _ _ _ _ HEAPIM ltac:(left; reflexivity)) as SEP.
        repeat split; clear - Ha SEP CPC CEIL LO BUF0 BUFL BL0 LEN0; lia. }
    assert (SJS5 : sj_statics m5 true).
    { eapply sj_statics_agree; [exact AG| | exact SJS4]. intros a Ha. unfold sjs_addr, SJ_STATICS_LO, SJ_STATICS_HI in Ha.
      cbn [outside]; repeat split; clear - Ha IMS CEIL LO GLO; lia. }
    assert (HEAP5 : RHEAP s1' ((pcp, COPY, len + 64) :: (pia, IA, 1024) :: (poc, OC, 8192) :: (pix, IDX, 4 * (roundup64 cap + 9)) :: (pim, IMPL, 96)
                      :: (ptp, TAPE, 8 * roundup64 (cap + 3)) :: (psb, SBUF, roundup64 (5 * (cap / 3) + 64)) :: LB) m5).
    { eapply LH_frame; [exact HEAP4| exact MU| exact WM|].
      constructor; [apply W_ok_stack; cbn; lia|].
      constructor; [eapply (W_ok_block _ (pim, IMPL, 96)); [do 4 right; left; reflexivity| cbn; lia| cbn; lia]| constructor]. }
    assert (AUX5 : rauxv_ok m5 B).
    { eapply rauxv_ok_frame; [exact AUX4| exact MU| exact WM|].
      constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; clear - IMS IMC CEIL LO QB; lia| constructor]. }
    pose proof (LH_head_disj _ _ _ _ _ _ HEAPIM) as DJIM.
    assert (PRES5 : lx_pres LB q (pid_back_X SRET PARSER) m m5).
    { eapply lx_pres_trans; [exact PRES4|]. eapply lx_pres_of_munch; [exact MU| exact WM|].
      intros a Ha [HX HC]. cbn [outside]. split; [| split; [| exact I]].
      - destruct HC as [HC|[HC|HC]]; [lia| specialize (BLB a HC); lia| lia].
      - destruct HC as [HC|[HC|HC]]; [lia| | clear - HC IMS; lia].
        apply DJIM. eapply in_block_incl; [| exact HC]. intros b Hb. cbn [app]. do 6 right. exact Hb. }
    clear AG MU WM HEAP4 AUX4 PRES4 HEAPIM DJIM.
    set (tcap := roundup64 (cap + 3)) in *. set (scap := roundup64 (5 * (cap / 3) + 64)) in *.
    assert (LBS : blen bs <= len) by lia.
    assert (PW : pairwise_disj [(COPY, len + 64); (IA, 1024); (OC, 8192); (IDX, 4 * (roundup64 cap + 9)); (IMPL, 96); (TAPE, 8 * tcap); (SBUF, scap)]).
    { pose proof (RHEAP_pairwise _ _ _ HEAP5 [(pcp, COPY, len + 64); (pia, IA, 1024); (poc, OC, 8192); (pix, IDX, 4 * (roundup64 cap + 9)); (pim, IMPL, 96);
                                               (ptp, TAPE, 8 * tcap); (psb, SBUF, scap)]) as H.
      apply H.
      - intros b Hb. cbn [In] in Hb |- *. clear - Hb. tauto.
      - pose proof (LH_nodup _ _ _ HEAP5) as ND. cbn [map blk_id fst snd] in ND |- *.
        repeat (apply NoDup_cons_iff in ND; let NI := fresh "NI" in destruct ND as [NI ND]; apply NoDup_cons; [intros Hin; apply NI; cbn [In] in Hin |- *; clear - Hin; tauto|]).
        constructor. }
    assert (Q16' : (q + -80) mod 16 = 0) by (replace (q + -80) with (q + (-5) * 16) by lia; rewrite Z.mod_add by lia; exact Q16).
    assert (LWZ : 4 * Z.of_nat (length ws) = 4 * (roundup64 cap + 9)) by (rewrite LWS; lia).
    ihere. to_implM. rewrite EBS.
    eapply (parse_cps S2) with (B := B) (lo := lo) (THIS := IMPL) (DOC := PARSER + 24) (IDX := IDX) (BUF := BUF) (TAPE := TAPE) (SBUF := SBUF) (OC := OC) (IA := IA)
                                     (bs := bs) (ws0 := ws) (cap := cap) (tcap := tcap) (scap := scap).
    - exact BOKS.
    - lia.
    - subst tcap. lia.
    - subst tcap. change (2^40) with 1099511627776. lia.
    - subst scap. pose proof (Z.div_mod cap 3 ltac:(lia)). pose proof (Z.mod_pos_bound cap 3 ltac:(lia)). lia.
    - subst scap. change (2^40) with 1099511627776. lia.
    - rewrite LWS. lia.
    - exact HEAP5.
    - exact AUX5.
    - lia.
    - exact B63.
    - exact ST4.
    - exact CEIL'.
    - unfold GLOBALS_TOP. lia.
    - unfold SJ_S2_STACK, SJ_S2_FRAMES, RMALLOC_STACK. lia.
    - exact Q16'.
    - rewrite ELX. exact ERR1.
    - assumption.
    - exact FRM.
    - lia.
    - exact GOT.
    - exists (pim, IMPL, 96). split; [do 4 right; left; reflexivity| cbn [blk_addr blk_size fst snd]; lia].
    - exists (pix, IDX, 4 * (roundup64 cap + 9)). split; [do 3 right; left; reflexivity| cbn [blk_addr blk_size fst snd]; lia].
    - exists (pcp, COPY, len + 64). split; [left; reflexivity| cbn [blk_addr blk_size fst snd]; lia].
    - exists (ptp, TAPE, 8 * tcap). split; [do 5 right; left; reflexivity| cbn [blk_addr blk_size fst snd]; lia].
    - exists (psb, SBUF, scap). split; [do 6 right; left; reflexivity| cbn [blk_addr blk_size fst snd]; lia].
    - exists (poc, OC, 8192). split; [do 2 right; left; reflexivity| cbn [blk_addr blk_size fst snd]; lia].
    - exists (pia, IA, 1024). split; [right; left; reflexivity| cbn [blk_addr blk_size fst snd]; lia].
    -
      rewrite LWZ. cbn [pairwise_disj]. unfold ivl_disj. cbn [fst snd].
      pose proof (pairwise_disj_nth _ 3 4 _ _ PW eq_refl eq_refl ltac:(lia)) as P34. pose proof (pairwise_disj_nth _ 0 4 _ _ PW eq_refl eq_refl ltac:(lia)) as P04.
      pose proof (pairwise_disj_nth _ 4 5 _ _ PW eq_refl eq_refl ltac:(lia)) as P45. pose proof (pairwise_disj_nth _ 4 6 _ _ PW eq_refl eq_refl ltac:(lia)) as P46.
      pose proof (pairwise_disj_nth _ 2 4 _ _ PW eq_refl eq_refl ltac:(lia)) as P24. pose proof (pairwise_disj_nth _ 1 4 _ _ PW eq_refl eq_refl ltac:(lia)) as P14.
      pose proof (pairwise_disj_nth _ 0 3 _ _ PW eq_refl eq_refl ltac:(lia)) as P03. pose proof (pairwise_disj_nth _ 3 5 _ _ PW eq_refl eq_refl ltac:(lia)) as P35.
      pose proof (pairwise_disj_nth _ 3 6 _ _ PW eq_refl eq_refl ltac:(lia)) as P36. pose proof (pairwise_disj_nth _ 2 3 _ _ PW eq_refl eq_refl ltac:(lia)) as P23.
      pose proof (pairwise_disj_nth _ 1 3 _ _ PW eq_refl eq_refl ltac:(lia)) as P13. pose proof (pairwise_disj_nth _ 0 5 _ _ PW eq_refl eq_refl ltac:(lia)) as P05.
      pose proof (pairwise_disj_nth _ 0 6 _ _ PW eq_refl eq_refl ltac:(lia)) as P06. pose proof (pairwise_disj_nth _ 0 2 _ _ PW eq_refl eq_refl ltac:(lia)) as P02.
      pose proof (pairwise_disj_nth _ 0 1 _ _ PW eq_refl eq_refl ltac:(lia)) as P01. pose proof (pairwise_disj_nth _ 5 6 _ _ PW eq_refl eq_refl ltac:(lia)) as P56.
      pose proof (pairwise_disj_nth _ 2 5 _ _ PW eq_refl eq_refl ltac:(lia)) as P25. pose proof (pairwise_disj_nth _ 1 5 _ _ PW eq_refl eq_refl ltac:(lia)) as P15.
      pose proof (pairwise_disj_nth _ 2 6 _ _ PW eq_refl eq_refl ltac:(lia)) as P26. pose proof (pairwise_disj_nth _ 1 6 _ _ PW eq_refl eq_refl ltac:(lia)) as P16.
      pose proof (pairwise_disj_nth _ 1 2 _ _ PW eq_refl eq_refl ltac:(lia)) as P12.
      unfold ivl_disj in *. cbn [fst snd] in *.
      repeat split; repeat (apply Forall_cons; [| try apply Forall_nil]); cbv beta; cbn [fst snd];
        first [ apply Forall_nil | clear - P34; lia | clear - P04 BUF0 BUFL BL0 LEN0; lia | clear - P45; lia | clear - P46; lia | clear - P24; lia | clear - P14; lia
              | clear - P03 BUF0 BUFL BL0 LEN0; lia | clear - P35; lia | clear - P36; lia | clear - P23; lia | clear - P13; lia
              | clear - P05 BUF0 BUFL BL0 LEN0; lia | clear - P06 BUF0 BUFL BL0 LEN0; lia | clear - P02 BUF0 BUFL BL0 LEN0; lia | clear - P01 BUF0 BUFL BL0 LEN0; lia
              | clear - P56; lia | clear - P25; lia | clear - P15; lia | clear - P26; lia | clear - P16; lia | clear - P12; lia ].
    - lia.
    - lia.
    - apply mod4_of_mod16. destruct BRIX as (_ & AL16 & _). exact AL16.
    - apply mod8_of_mod16. destruct BRIM as (_ & AL16 & _). exact AL16.
    - rewrite <- Z.add_mod_idemp_l by lia. rewrite ALP. reflexivity.
    - apply mod8_of_mod16. destruct BRTP as (_ & AL16 & _). exact AL16.
    - apply mod8_of_mod16. destruct BROC as (_ & AL16 & _). exact AL16.
    - unfold impl_cells16, SJ_DPI_VPTR. exact THISC.
    - exact DOCC.
    - exact ARR.
    - exact BUFB.
    - eapply rw_cells_wr_at; [exact BLKTP|]. cbn [cells_size csize Nat.add]. subst tcap. lia.
    - eapply rw_cells_wr_at; [exact BLKSB|]. cbn [cells_size csize Nat.add]. subst scap. lia.
    - destruct (u32arr_of_block m5 OC _ joc 2048%nat BLKOC ltac:(reflexivity)) as (ocs & OCA & LOCS). exists ocs. split; assumption.
    - exists jia. split; [eapply u8arr_of_rw_cells; exact BLKIA| destruct BLKIA as [[[HL _] _] _]; cbn [cell_wf] in HL; rewrite HL; reflexivity].
    - intros s6' ms6 PO. unfold hpostF in PO.
      destruct PO as (z5 & z6 & z7 & z10 & z11 & z12 & z13 & z14 & z15 & z16 & z17 & z28 & z29 & z30 & z31 & F' & fc' & m6
                      & -> & FRM6 & MI6 & ST6 & (errv6 & ERR6) & AUX6 & FA6 & SO6 & RR).
      unfold parse_R in RR. destruct RR as (A064 & HEAP6 & PRES56 & (nsi6 & nxt6 & docv6 & THISC6) & OKRES6).
      replace (ret_pc (Z_to_bv 64 251680)) with (Z_to_bv 64 251680) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      assert (XLOW : forall a, rin_ivs (parse_X IMPL IDX TAPE SBUF OC IA (Z.of_nat (length ws)) tcap scap) a -> a < alloc_ceiling).
      { intros a Ha. unfold parse_X in Ha. cbn [rin_ivs fst snd] in Ha. clear - Ha IMC IXC TPC SBC OCC IAC LWZ. lia. }
      assert (XSTAT : forall a, 0xd5000 <= a < 0x110000 -> ~ rin_ivs (parse_X IMPL IDX TAPE SBUF OC IA (Z.of_nat (length ws)) tcap scap) a).
      { intros a Ha Hx. unfold parse_X in Hx. cbn [rin_ivs fst snd] in Hx.
        destruct BRIX as (_ & _ & _ & _ & IXS). destruct BRSB as (_ & _ & _ & _ & SBS). destruct BRTP as (_ & _ & _ & _ & TPS).
        destruct BROC as (_ & _ & _ & _ & OCS). destruct BRIA as (_ & _ & _ & _ & IAS).
        destruct Hx as [Hx|[Hx|[Hx|[Hx|[Hx|[Hx|[]]]]]]]; [clear - Ha Hx IMS| clear - Ha Hx IXS LWZ| clear - Ha Hx TPS| clear - Ha Hx SBS| clear - Ha Hx OCS| clear - Ha Hx IAS];
          lia. }
      pose proof (agree_of_lx_pres _ _ _ _ _ PRES56) as AG.
      apply (rw_cells_agree _ _ _ _ _ AG) in FR; [| intros a Ha; cbn in Ha; split; [intros Hx; apply XLOW in Hx; clear - Ha Hx CEIL LO; lia| left; lia]].
      apply (rw_cells_agree _ _ _ _ _ AG) in PIMPL; [| intros a Ha; cbn in Ha; split; [intros Hx; apply XLOW in Hx; clear - Ha Hx CEIL LO QS SP; lia| left; lia]].
      apply (rw_cells_agree _ _ _ _ _ AG) in DOCC; [| intros a Ha; cbn in Ha; split; [intros Hx; apply XLOW in Hx; clear - Ha Hx CEIL LO QS SP; lia| left; lia]].
      apply (rw_cells_agree _ _ _ _ _ AG) in P48; [| intros a Ha; cbn in Ha; split; [intros Hx; apply XLOW in Hx; clear - Ha Hx CEIL LO QS SP; lia| left; lia]].
      apply (rw_cells_agree _ _ _ _ _ AG) in SRETC; [| intros a Ha; cbn in Ha; split; [intros Hx; apply XLOW in Hx; clear - Ha Hx CEIL LO QS SP; lia| left; lia]].
      assert (STCL : forall a, 0xd5000 <= a < 0x110000 -> ~ ralloc_static a ->
                lx_client ((pcp, COPY, len + 64) :: (pia, IA, 1024) :: (poc, OC, 8192) :: (pix, IDX, 4 * (roundup64 cap + 9)) :: (pim, IMPL, 96) :: (ptp, TAPE, 8 * tcap) :: (psb, SBUF, scap) :: LB)
                          (q + -80) (parse_X IMPL IDX TAPE SBUF OC IA (Z.of_nat (length ws)) tcap scap) a).
      { intros a Ha Hs. split; [apply XSTAT; exact Ha| right; right; split; assumption]. }
      apply (rw_cells_agree _ _ _ _ _ AG) in GOT;
        [| intros a Ha; cbn in Ha; apply STCL; [lia| unfold ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RATP, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP; lia]].
      apply (rw_cells_agree _ _ _ _ _ AG) in VTD;
        [| intros a Ha; cbn in Ha; apply STCL; [lia| unfold ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RATP, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP; lia]].
      apply (rw_cells_agree _ _ _ _ _ AG) in VT24;
        [| intros a Ha; cbn in Ha; apply STCL; [lia| unfold ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RATP, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP; lia]].
      assert (SJS6 : sj_statics m6 true).
      { eapply sj_statics_agree; [exact AG| | exact SJS5]. intros a Ha. pose proof (sjs_addr_lt a Ha) as [R1 R2]. apply STCL; [unfold GLOBALS_TOP in R1; lia| exact R2]. }
      assert (PRES6 : lx_pres LB q (pid_back_X SRET PARSER) m m6).
      { eapply lx_pres_trans; [exact PRES5|].
        eapply (lx_pres_sub LB q _ _ _ _ _ _ PRES56); [lia| intros b Hb; do 7 right; exact Hb|].
        intros a Ha _. split; [apply XLOW in Ha; clear - Ha CEIL LO; lia|]. split; [| intros Hs; exact (XSTAT a Hs Ha)].
        intros IB. unfold parse_X in Ha. cbn [rin_ivs fst snd] in Ha.
        pose proof (RHEAP_prefix_disj _ [(pcp, COPY, len + 64); (pia, IA, 1024); (poc, OC, 8192); (pix, IDX, 4 * (roundup64 cap + 9)); (pim, IMPL, 96); (ptp, TAPE, 8 * tcap); (psb, SBUF, scap)] LB _ HEAP6) as PD.
        destruct Ha as [Ha|[Ha|[Ha|[Ha|[Ha|[Ha|[]]]]]]].
        - apply (PD (pim, IMPL, 96) ltac:(do 4 right; left; reflexivity) a IB). cbn [blk_addr blk_size fst snd]. lia.
        - apply (PD (pix, IDX, 4 * (roundup64 cap + 9)) ltac:(do 3 right; left; reflexivity) a IB). cbn [blk_addr blk_size fst snd]. lia.
        - apply (PD (ptp, TAPE, 8 * tcap) ltac:(do 5 right; left; reflexivity) a IB). cbn [blk_addr blk_size fst snd]. lia.
        - apply (PD (psb, SBUF, scap) ltac:(do 6 right; left; reflexivity) a IB). cbn [blk_addr blk_size fst snd]. lia.
        - apply (PD (poc, OC, 8192) ltac:(do 2 right; left; reflexivity) a IB). cbn [blk_addr blk_size fst snd]. lia.
        - apply (PD (pia, IA, 1024) ltac:(do 1 right; left; reflexivity) a IB). cbn [blk_addr blk_size fst snd]. lia. }
      clear AG PRES5 PRES56 HEAP5 AUX5 SJS4 SJS5 XLOW XSTAT STCL THISC BLKSB BLKTP BLKOC BLKIA ARR BUFB.
      unfold impl_cells16 in THISC6.
      pose proof (munch_refl [(q - 80, q); (SRET, SRET + 24)]%Z m6) as MU. pose proof (wmono_refl usegs m6) as WM.
      unfold implM. iprefix.

      step. step. if_cases KA; zify_cond KA; [exfalso; rewrite ?unsigned_lit in KA by lia; lia|]. clear KA.
      step. if_cases KR;
        [ step; (if_cases KS; zify_cond KS; [exfalso; rewrite ?unsigned_lit in KS by lia; lia|]); step; step; hstep; hstep; step
        | step; (if_cases KS; zify_cond KS; [exfalso; rewrite ?unsigned_lit in KS by lia; lia|]); hstep; hstep; step; step ].
      all:
        do 11 step; release_frame FR ST6 q; step.
      all: lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
          assert (HEAP7 : RHEAP s6' ((pcp, COPY, len + 64) :: (pia, IA, 1024) :: (poc, OC, 8192) :: (pix, IDX, 4 * (roundup64 cap + 9)) :: (pim, IMPL, 96)
                                        :: (ptp, TAPE, 8 * tcap) :: (psb, SBUF, scap) :: LB) mx)
            by (eapply LH_frame; [exact HEAP6| exact MU| exact WM|]; constructor; [apply W_ok_stack; cbn; lia|]; constructor; [apply W_ok_stack; cbn; lia| constructor]);
          assert (AUX7 : rauxv_ok mx B)
            by (eapply rauxv_ok_frame; [exact AUX6| exact MU| exact WM|]; constructor; [cbn; unfold RAUXV_CELL; lia|]; constructor; [cbn; unfold RAUXV_CELL; lia| constructor]);
          assert (SJS7 : sj_statics mx true)
            by (eapply sj_statics_agree; [exact (agree_on_of_munch _ _ _ MU WM)| | exact SJS6]; intros a Ha; unfold sjs_addr, SJ_STATICS_LO, SJ_STATICS_HI in Ha;
                cbn [outside]; repeat split; clear - Ha LO GLO QS; lia);
          assert (PRES7 : lx_pres LB q (pid_front_X PARSER ++ pid_back_X SRET PARSER) m00 mx)
            by (eapply lx_pres_trans; [eapply lx_pres_weaken; [exact PRES0| apply Z.le_refl| intros b0 Hb0; exact Hb0| intros a Ha; apply in_or_rin_app_l; exact Ha]|];
                eapply lx_pres_weaken; [eapply lx_pres_trans; [exact PRES6| eapply lx_pres_of_munch; [exact MU| exact WM|]]| apply Z.le_refl| intros b0 Hb0; exact Hb0| intros a Ha; apply in_or_rin_app_r; exact Ha];
                intros a Ha [HX HC]; unfold pid_back_X in HX; cbn [rin_ivs fst snd] in HX; cbn [outside]; split; [| split; [clear - HX; lia| exact I]];
                destruct HC as [HC|[HC|HC]]; [lia| specialize (BLB a HC); lia| lia]);
          assert (OKRES7 : s2_okres TAPE SBUF tcap scap z10 mx)
            by (eapply s2_okres_agree; [exact (agree_on_of_munch _ _ _ MU WM)| | | exact OKRES6];
                intros a Ha; cbn [outside]; repeat split; clear - Ha TPC SBC CEIL LO QS; subst tcap scap; lia)
        end.
      all: ihere; to_implM; apply HK; exists IMPL, IDX, OC, IA, TAPE, SBUF, COPY; unfold hpostF; do 15 eexists; eexists F', fc', _;
        (split; [cbv delta [mkR]; reflexivity|]); (split; [exact FRM6|]); (split; [eassumption|]); (split; [exact ST6|]); (split; [exists errv6; eassumption|]);
        (split; [exact AUX7|]); (split; [congruence|]); (split; [congruence|]);
        unfold pid_R; (split; [exact HEAP7|]); (split; [exact PRES7|]);
        (split; [unfold sj_ro, SJ_GOT_NOTHROW, SJ_NOTHROW_TAG, SJ_IMPL_VT24, SJ_CREATE_DPI, SJ_DPI_VPTR, dpi_vtable_cells; auto|]);
        (split; [exact SJS7|]); (split; [eassumption|]); (split; [eassumption|]); (split; [unfold p48_cells; eassumption|]);
        (split; [exists z10; split; [unfold pj_res_cells; rewrite KR; eassumption| split; [exact OKRES7|
                   intros E0; exfalso; apply (f_equal bv_unsigned) in E0; rewrite !unsigned_lit in E0 by lia; lia]]|]);
        (split; [do 13 eexists; (split; [unfold impl_cells16; eassumption| reflexivity])|]);
        (split; [exact BRTP| exact BRSB]).
  Qed.

  Lemma pj_pid_big_cps : forall {A} (k : M PState A) (Q : A -> PState -> machine_state -> Prop)
      (ra0 gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (q : Z)
      (F : bvmap 5 word) (fc : bv 32) (s00 : PState) (LB : list block) (lo B : Z) (m00 : mem) (SRET PARSER D len : Z) (j57 : list byte)
      (psb ptp pim pix poc pia : bptr) (s : PState) (ms : machine_state) (jr0 jr8 jr16 jr20 : list byte),
    pid_mid ra0 q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s00 LB lo B m00 SRET PARSER D len (Z.max len 32) (Z_to_bv 8 0) j57 psb ptp pim pix poc pia s ms ->
    1048512 < len < 2^64 ->
    RHEAP s00 LB m00 -> frm0 fc -> q <= B -> B < 2^63 -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= q - 80 -> 0 <= q < 2^64 ->
    q <= SRET -> SRET + 24 <= PARSER -> PARSER + 80 <= B ->
    rw_cells usegs m00 SRET [CB 8 jr0; CB 8 jr8; CB 4 jr16; CB 4 jr20] ->
    (forall s' ms',
        (exists IMPL IDX OC IA TAPE SBUF,
          hpostF ra0 q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s00 lo B
            (pid_R ((pia, IA, 1024) :: (poc, OC, 8192) :: (pix, IDX, 4 * (roundup64 (Z.max len 32) + 9)) :: (pim, IMPL, 96)
                      :: (ptp, TAPE, 8 * roundup64 (Z.max len 32 + 3)) :: (psb, SBUF, roundup64 (5 * (Z.max len 32 / 3) + 64)) :: LB)
                   LB q SRET PARSER m00 (Z_to_bv 8 0) j57 jr20 IMPL IDX OC IA TAPE SBUF (Z.max len 32) (Z_to_bv 64 0) (Z_to_bv 64 0)) s' ms') ->
        implM usegs k s' Q ms') ->
    implM usegs k s Q ms.
  Proof.
    intros A k Q. intros until jr20. intros MID LEN HEAP00 FRM QB B63 CEIL GLO LO Hq QS SP PB SRETC HK.
    unfold pid_mid in MID.
    destruct MID as (x1 & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m & errv & SBUF & TAPE & IMPL & IDX & OC & IA & ws & jsb & jtp & joc & jia
                     & p12 & p28 & p50 & -> & MI & ST & ERR & AUX & FA & SO & HEAP & PRES0 & (GOT & VT24 & VTD) & SJS & FR & PIMPL & DOCC & P48 & THISC & ARR & LWS
                     & BLKSB & BLKTP & BLKOC & BLKIA & BRSB & BRTP & BRIM & BRIX & BROC & BRIA).
    unfold SJ_PID_MID, GLOBALS_TOP, p48_cells, pid_frame in *.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof CEIL as CEIL'. unfold OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Spec.Malloc.MCEIL in CEIL; try (pose proof alloc_ceiling_range as CEIL_RANGE__).
    assert (BLB : forall a, in_block LB a -> a < alloc_ceiling).
    { intros a (b & Hb & Hr). pose proof (LH_block_range _ _ _ _ HEAP00 Hb) as (_ & _ & _ & BC & _).
      unfold OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Spec.Malloc.MCEIL in BC. lia. }
    apply (rw_cells_agree _ _ _ _ _ (agree_of_lx_pres _ _ _ _ _ PRES0)) in SRETC;
      [| intros a Ha; cbn in Ha; split; [unfold pid_front_X, LXW_SJ, SJ_STATICS_LO, SJ_STATICS_HI; cbn [rin_ivs fst snd]; clear - Ha SP QS LO GLO; lia| left; lia]].
    pose proof BRIM as (IM0 & _ & _ & IMC & IMS). unfold OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Spec.Malloc.MCEIL in IMC.
    pose proof (munch_refl [(q - 80, q); (PARSER + 64, PARSER + 80); (SRET, SRET + 24)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
    assert (ELX : LX_ERRNO = 977220) by reflexivity. rewrite ELX in ERR.
    unfold SJ_GOT_NOTHROW, SJ_NOTHROW_TAG in GOT. unfold SJ_IMPL_VT24, SJ_CREATE_DPI in VT24. unfold SJ_DPI_VPTR, dpi_vtable_cells in VTD.
    unfold impl_cells16, SJ_DPI_VPTR in THISC.
    hide BLKSB. hide BLKTP. hide BLKOC. hide BLKIA. hide ARR.
    unfold implM. iprefix.

    step. if_false. step. step. if_true. step. step. step.
    if_cases K0; zify_cond K0; [| exfalso; rewrite ?unsigned_lit in K0 by lia; lia]. clear K0.
    step. hstep. step. if_true. step. if_true.
    step. if_cases KS; zify_cond KS; [exfalso; rewrite ?unsigned_lit in KS by lia; lia|]. clear KS.
    step. step. hstep. hstep. hstep. step.
    do 11 step. release_frame FR ST q. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m7 end.
    ihere. to_implM. apply HK. exists IMPL, IDX, OC, IA, TAPE, SBUF. unfold hpostF. do 15 eexists. exists F, fc, m7.
    split; [cbv delta [mkR]; reflexivity|]. split; [exact FRM|]. split; [assumption|]. split; [exact ST|]. split; [exists errv; rewrite ELX; assumption|].
    split. { eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|].
             constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
    split; [exact FA|]. split; [exact SO|].
    unfold pid_R. split.
    { eapply LH_frame; [exact HEAP| exact MU| exact WM|].
      constructor; [apply W_ok_stack; cbn; lia|]. constructor; [apply W_ok_stack; cbn; lia|]. constructor; [apply W_ok_stack; cbn; lia| constructor]. }
    split.
    { eapply lx_pres_trans; [eapply lx_pres_weaken; [exact PRES0| apply Z.le_refl| intros b0 Hb0; exact Hb0| intros a Ha; apply in_or_rin_app_l; exact Ha]|].
      eapply lx_pres_weaken; [eapply lx_pres_of_munch; [exact MU| exact WM|]| apply Z.le_refl| intros b0 Hb0; exact Hb0| intros a Ha; apply in_or_rin_app_r; exact Ha].
      intros a Ha [HX HC]. unfold pid_back_X in HX. cbn [rin_ivs fst snd] in HX. cbn [outside]. split; [| split; [clear - HX; lia| split; [clear - HX; lia| exact I]]].
      destruct HC as [HC|[HC|HC]]; [lia| specialize (BLB a HC); lia| lia]. }
    split; [unfold sj_ro, SJ_GOT_NOTHROW, SJ_NOTHROW_TAG, SJ_IMPL_VT24, SJ_CREATE_DPI, SJ_DPI_VPTR, dpi_vtable_cells; auto|].
    split. { eapply sj_statics_agree; [exact (agree_on_of_munch _ _ _ MU WM)| | exact SJS]. intros a Ha. unfold sjs_addr, SJ_STATICS_LO, SJ_STATICS_HI in Ha.
             cbn [outside]; repeat split; clear - Ha LO GLO QS SP; lia. }
    split; [assumption|]. split; [assumption|]. split; [unfold p48_cells; assumption|].
    split. { exists (Z_to_bv 64 2). split; [unfold pj_res_cells; eassumption| split; [left; rewrite unsigned_lit by lia; lia|
               intros _ E0; apply (f_equal bv_unsigned) in E0; rewrite !unsigned_lit in E0 by lia; lia]]. }
    split; [do 13 eexists; split; [unfold impl_cells16; eassumption| reflexivity]|].
    split; [exact BRTP| exact BRSB].
  Qed.

End Proofs.
End WithCeiling0.
