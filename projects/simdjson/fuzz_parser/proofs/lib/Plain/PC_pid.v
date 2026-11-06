(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require InitMem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Common Require Import Stdio_pure Printf_pieces.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Plain Require Import PImg.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Plain Require Import RMallocRep RMallocTree RMalloc_iface ROpNew_iface ROpNew ROpNew_nt.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Plain Require RMalloc_ifaceP.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Plain Require Import F_memset F_memcpy.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import Prelim Monad Stdio Malloc HarnessP ProgP SjStage1 SjS1Bytes.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Plain Require Import RunDraw.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Plain Require Import PC_kit PC_docalloc PC_active PC_setcap PC_setdepth PC_create PC_docdtor PC_dtor PC_s12iface PU_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Notation mem := (word -> option byte).

Section CANSEC1. Context {rc : runConstT}.
Definition PPID : Z := 0x26ec8.
Definition PID_STACK : Z := 80 + PARSE_STACK.
Definition w64 (z : Z) : word := Z_to_bv 64 z.

(* [comment removed for export] *)
Definition pid_blocks (len : Z) (r : bptr * bptr * (bptr * bptr * bptr * bptr) * option bptr) (ASB ATP AIM ASI AOC AIA ACP : Z) : list block :=
  let '(sb, tpp, (im, si, oc, ia), lb) := r in
  copy_blk lb ACP (COPY_BYTES len)
  ++ six_blks ia oc si im tpp sb AIA AOC ASI AIM ATP ASB ISARR_BYTES OC_BYTES (SIDX_BYTES len) IMPL_BYTES (TAPE_BYTES len) (SB_BYTES len).

Definition pid_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (s : PState) (LB : list block) (len lo B P R : Z) (m : mem)
    (r : bptr * bptr * (bptr * bptr * bptr * bptr) * option bptr) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem) (errv' : word),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m' (seg_rom psegs)
    /\ frm0 fc'
    /\ mem_inv psegs m' /\ stk psegs m' lo (bv_unsigned sp)
    /\ rw_cells psegs m' (errno_addr tp) [C4 errv'] /\ rauxv_ok m' B
    /\ rheap_pres_W LB (bv_unsigned sp) ([(P, P + 80); (R, R + 24)] ++ client_wr) m m'
    /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
    /\ cstat_built m'
    /\ stk psegs m' R (P + 80)
    /\ exists ASB ATP AIM ASI AOC AIA ACP,
         RHEAP s' (pid_blocks len r ASB ATP AIM ASI AOC AIA ACP ++ LB) m'
         /\ rw_cells psegs m' (P + 8) [C8 (w64 AIM)] /\ rw_cells psegs m' (P + 24) [C8 (w64 ATP); C8 (w64 ASB)]
         /\ rw_cells psegs m' (P + 64) [C8 (w64 (copy_addr (snd r) ACP))]
         /\ rw_cells psegs m' AIM [C8 (w64 PVTAB_DOM)] /\ rw_cells psegs m' (AIM + 16) [C8 (w64 ASI)]
         /\ rw_cells psegs m' (AIM + 56) [C8 (w64 AOC); C8 (w64 AIA)].

Definition pid_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (s : PState) (LB : list block) (lo B : Z) (errv : word) (data : list Z) (D P R : Z) (jr : list byte),
    RHEAP s LB m ->
    bytes_at psegs m D (map (Z_to_bv 8) data) -> Forall (fun c => 0 <= c < 256) data ->
    rclient_range LB (P + 80) D (zlength data) -> 0 < D -> D + zlength data <= ATOP -> zlength data < 2^26 ->
    (forall a, D <= a < D + zlength data -> outside client_wr a) ->
    client_img m -> cstat_image m \/ cstat_built m ->
    rauxv_ok m B -> bv_unsigned sp <= B -> bv_unsigned sp <= 2^47 -> bv_unsigned sp mod 16 = 0 ->
    stk psegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - PID_STACK ->
    rw_cells psegs m (errno_addr tp) [C4 errv] ->
    mem_inv psegs m -> frm0 fc ->
    tp = Z_to_bv 64 RATP ->
    (* [comment removed for export] *)
    rw_cells psegs m (P + 8) [C8 (w64 0)] ->
    rw_cells psegs m (P + 24) [C8 (w64 0); C8 (w64 0); C8 (w64 0)] ->
    rw_cells psegs m (P + 48) [C8 (w64 4294967295); C1 (Z_to_bv 8 0)] ->
    rw_cells psegs m (P + 64) [C8 (w64 0); C8 (w64 0)] ->
    rw_cells psegs m R [CB 24 jr] ->
    bv_unsigned sp <= R -> R + 24 <= P -> P + 80 <= B -> P mod 8 = 0 -> stk psegs m R (P + 80) ->
    a0 = w64 R -> a1 = w64 P -> a2 = w64 (P + 24) -> a3 = w64 D -> a4 = w64 (zlength data) -> a5 = w64 1 ->
    implM psegs (HarnessP.parse_into_doc raw_malloc raw_free ProgP.new_handler data) s
          (pid_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB (zlength data) lo B P R m)
          (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 PPID) fc None m (seg_rom psegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma rclient_range_sp : forall LB SP SP' A n, rclient_range LB SP A n -> SP' <= SP -> rclient_range LB SP' A n.
Proof. intros LB SP SP' A n [H|[H|H]] HS; [left; lia| right; left; exact H| right; right; exact H]. Qed.
Lemma rclient_range_app_r : forall L1 LB SP A n, rclient_range LB SP A n -> rclient_range (L1 ++ LB) SP A n.
Proof.
  intros L1 LB SP A n [H|[H|(b & Hb & H1 & H2)]]; [left; exact H| right; left; exact H|].
  right; right. exists b. split; [apply in_or_app; right; exact Hb| lia].
Qed.

(* [comment removed for export] *)
Definition stat_pres (m m' : mem) : Prop :=
  forall a, (0x87198 <= a < 0x871a2 \/ 0x871c8 <= a < 0x871ca \/ 0x87210 <= a < 0x8723c) ->
    m' (wa a) = m (wa a) /\ (wview psegs m (wa a) <> None -> wview psegs m' (wa a) <> None).
Lemma stat_pres_cells : forall m m' A cs, stat_pres m m' -> rw_cells psegs m A cs ->
  (0x87198 <= A /\ A + Z.of_nat (cells_size cs) <= 0x871a2 \/ 0x871c8 <= A /\ A + Z.of_nat (cells_size cs) <= 0x871ca
   \/ 0x87210 <= A /\ A + Z.of_nat (cells_size cs) <= 0x8723c) -> rw_cells psegs m' A cs.
Proof.
  intros m m' A cs SP [[Hwf (B0 & B1 & HB)] (W0 & W1 & W)] HA. split; [split; [exact Hwf|]|].
  - split; [exact B0|]. split; [exact B1|]. intros i Hi. rewrite <- (HB i Hi). unfold mrd.
    rewrite cells_bytes_length in Hi by exact Hwf.
    destruct (SP (A + Z.of_nat i) ltac:(lia)) as [E _]. rewrite E. reflexivity.
  - split; [exact W0|]. split; [exact W1|]. intros i Hi.
    destruct (SP (A + i) ltac:(lia)) as [_ WW]. apply WW. apply W. exact Hi.
Qed.
Lemma cstat_transport : forall m m', stat_pres m m' -> cstat_image m \/ cstat_built m -> cstat_image m' \/ cstat_built m'.
Proof.
  intros m m' SP [CI|(C1 & C2 & C3 & C4)].
  - left. intros a Ha. pose proof (bv_unsigned_in_range 64 a) as Ra. unfold bv_modulus in Ra. cbn in Ra.
    destruct (SP (bv_unsigned a) Ha) as [E _]. unfold wa in E. rewrite Z_to_bv_bv_unsigned in E. rewrite E. exact (CI a Ha).
  - right. unfold cstat_built. unfold PACTIVE, PACTIVE_GUARD, PFALLBACK, PFALLBACK_GUARD, guard1, fallback_cells in *.
    split; [eapply stat_pres_cells; [exact SP| exact C1| cbn; lia]|]. split; [eapply stat_pres_cells; [exact SP| exact C2| cbn; lia]|].
    split; [eapply stat_pres_cells; [exact SP| exact C3| cbn; lia]| eapply stat_pres_cells; [exact SP| exact C4| cbn; lia]].
Qed.
Lemma stat_pres_of_x : forall LB SP X n m m', rheap_pres_x LB SP X n m m' -> (X + n <= 0x87198 \/ 0x8723c <= X) -> stat_pres m m'.
Proof.
  intros LB SP X n m m' H HX a Ha. apply H; [lia| right; left; unfold ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP; lia| lia].
Qed.
Lemma stat_pres_of_munch : forall W m m', munch W m m' -> wmono psegs m m' ->
  (forall a, (0x87198 <= a < 0x871a2 \/ 0x871c8 <= a < 0x871ca \/ 0x87210 <= a < 0x8723c) -> outside W a) -> stat_pres m m'.
Proof.
  intros W m m' MU WM HW a Ha. split; [apply MU; unfold wa; rewrite Z_to_bv_unsigned, bv_wrap_small by (unfold bv_modulus; cbn; lia); apply HW; exact Ha|].
  intros Hv. apply WM. exact Hv.
Qed.

Lemma bytes_at_transport_pw : forall W m m' A bs, bytes_at psegs m A bs -> munch W m m' ->
  (forall a, A <= a < A + Z.of_nat (length bs) -> outside W a) -> bytes_at psegs m' A bs.
Proof.
  intros W m m' A bs (H0 & H1 & HB) MU HW. split; [exact H0|]. split; [exact H1|]. intros i Hi.
  rewrite <- (HB i Hi). unfold mrd. rewrite MU; [reflexivity|]. unfold wa. rewrite Z_to_bv_unsigned, bv_wrap_small by (unfold bv_modulus; cbn; lia).
  apply HW. lia.
Qed.


(* [comment removed for export] *)
Lemma rw_cells_cons_split : forall m A c cs, rw_cells psegs m A (c :: cs) ->
  rw_cells psegs m A [c] /\ rw_cells psegs m (A + Z.of_nat (csize c)) cs.
Proof. intros m A c cs H. apply (rw_cells_app_split psegs m A [c] cs) in H. cbn [cells_size] in H. rewrite Nat.add_0_r in H. exact H. Qed.

(* [comment removed for export] *)
Lemma impl_split : forall m AIM p1 p2 pad ASI cap AOC AIA, rw_cells psegs m AIM (impl_cells p1 p2 pad ASI cap AOC AIA) ->
  rw_cells psegs m AIM [C8 (w64 PVTAB_DOM)] /\ rw_cells psegs m (AIM + 8) [C4 (w64 0)] /\
  rw_cells psegs m (AIM + 16) [C8 (w64 ASI)] /\ rw_cells psegs m (AIM + 24) [C4 (w64 0)] /\
  rw_cells psegs m (AIM + 40) [C8 (w64 MAX_DEPTH); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] /\
  rw_cells psegs m (AIM + 56) [C8 (w64 AOC); C8 (w64 AIA); C8 (w64 0); C8 (w64 0); C8 (w64 0)].
Proof.
  intros m AIM p1 p2 pad ASI cap AOC AIA H. unfold impl_cells, PC_create.w64 in H.
  apply rw_cells_cons_split in H as [H0 H]. apply rw_cells_cons_split in H as [H8 H]. apply rw_cells_cons_split in H as [_ H].
  apply rw_cells_cons_split in H as [H16 H]. apply rw_cells_cons_split in H as [H24 H]. apply rw_cells_cons_split in H as [_ H].
  apply rw_cells_cons_split in H as [_ H]. apply rw_cells_cons_split in H as [H40 H]. apply rw_cells_cons_split in H as [H48 H].
  apply rw_cells_cons_split in H as [_ H56].
  cbn [csize] in *.
  repeat match goal with Hh : context [Z.of_nat ?k] |- _ => let v := eval vm_compute in (Z.of_nat k) in change (Z.of_nat k) with v in Hh end.
  replace (AIM + 8 + 4 + 4) with (AIM + 16) in * by lia. replace (AIM + 16 + 8) with (AIM + 24) in * by lia.
  replace (AIM + 24 + 4 + 4 + 8) with (AIM + 40) in * by lia. replace (AIM + 40 + 8) with (AIM + 48) in * by lia.
  replace (AIM + 48 + 2 + 6) with (AIM + 56) in * by lia.
  unfold w64. split; [exact H0|]. split; [exact H8|]. split; [exact H16|]. split; [exact H24|]. split; [|exact H56].
  assert (H48' : rw_cells psegs m (AIM + 48) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]).
  { apply (InitMem.rw_cells_recast psegs m _ [C2 (Z_to_bv 64 0)]); [exact H48| cbn; repeat split; exact I| vm_compute; reflexivity| reflexivity]. }
  pose proof (rw_cells_app_join psegs m (AIM + 40) [C8 (Z_to_bv 64 MAX_DEPTH)] [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] H40) as J.
  cbn [cells_size csize app] in J. change (Z.of_nat 8) with 8 in J. replace (AIM + 40 + 8) with (AIM + 48) in J by lia. exact (J H48').
Qed.

Lemma nodup_app_disj : forall (A : Type) (l1 l2 : list A) x, List.NoDup (l1 ++ l2) -> In x l1 -> In x l2 -> False.
Proof.
  intros A l1. induction l1 as [|y l1 IH]; intros l2 x H H1 H2; [destruct H1|]. cbn in H. apply NoDup_cons_iff in H as [Hn Hd].
  destruct H1 as [E|H1]; [subst y; apply Hn; apply in_or_app; right; exact H2| exact (IH l2 x Hd H1 H2)].
Qed.
Definition hidden (P : Prop) : Prop := P.

(* [comment removed for export] *)
Lemma rheap_pres_blk_window : forall s L L' p A n m m' lo x y SP, RHEAP s L m -> In (p, A, n) L ->
  (forall b, In b L' -> In b L /\ blk_id b <> p) -> munch [(lo, SP); (x, y)] m m' -> wmono psegs m m' ->
  A <= x -> y <= A + n -> ATOP <= lo -> lo <= SP -> rheap_pres L' SP m m'.
Proof.
  intros s L L' p A n m m' lo x y SP HP IN HL MU WM H1 H2 HLO HSP.
  pose proof (RMalloc_ifaceP.RHEAP_block_range_proof _ _ _ _ HP IN) as (B1 & B2 & B3 & B4 & B5). cbn [blk_addr blk_size fst snd] in *.
  apply rheap_pres_of_munch with (W := [(lo, SP); (x, y)]); [exact MU| exact WM|].
  intros a Ha Hc. cbn. destruct Hc as [Hc|[Hc|(b & Hb & Hr)]].
  - split; [lia|]. split; [lia| exact I].
  - split; [lia|]. split; [unfold ralloc_static in Hc; lia| exact I].
  - destruct (HL b Hb) as [Hb' Hn].
    pose proof (RMalloc_ifaceP.RHEAP_blocks_disjoint_proof _ _ _ (p, A, n) b HP IN Hb' ltac:(cbn; congruence)) as D. cbn [blk_addr blk_size fst snd] in D.
    pose proof (RMalloc_ifaceP.RHEAP_block_range_proof _ _ _ _ HP Hb') as (C1 & C2 & C3 & C4 & C5).
    split; [lia|]. split; [lia| exact I].
Qed.
Lemma nodup_head_notin : forall b0 L b, List.NoDup (map blk_id (b0 :: L)) -> In b L -> blk_id b <> blk_id b0.
Proof. intros b0 L b ND Hb E. cbn [map] in ND. apply NoDup_cons_iff in ND as [NI _]. apply NI. rewrite <- E. apply in_map. exact Hb. Qed.
Lemma munch_cons_w : forall w W m m', munch W m m' -> munch (w :: W) m m'.
Proof. intros [lo hi] W m m' H x Hx. apply H. destruct Hx as [_ Hx]. exact Hx. Qed.

(* [comment removed for export] *)
Lemma rheap_pres_W_blk : forall s L L' (ex : list bptr) m m' lo SP Wa Wb,
  RHEAP s L m ->
  (forall b, In b L' -> In b L /\ ~ In (blk_id b) ex) ->
  munch ((lo, SP) :: Wa ++ Wb) m m' -> wmono psegs m m' ->
  (forall w, In w Wb -> exists b, In b L /\ In (blk_id b) ex /\ blk_addr b <= fst w /\ snd w <= blk_addr b + blk_size b) ->
  ATOP <= lo -> lo <= SP ->
  rheap_pres_W L' SP Wa m m'.
Proof.
  intros s L L' ex m m' lo SP Wa Wb HP HL MU WM HB HLO HSP. atop_facts.
  apply rheap_pres_W_of_munch with (W' := (lo, SP) :: Wa ++ Wb); [exact MU| exact WM|].
  intros a Ha Hc Hx. cbn [outside]. split.
  - destruct Hc as [Hc|[Hc|(b & Hb & Hr)]]; [lia| lia|]. destruct (HL b Hb) as [Hb' _].
    destruct (RMalloc_ifaceP.RHEAP_block_range_proof _ _ _ _ HP Hb') as (_ & _ & _ & R4 & _). lia.
  - apply outside_app. split; [exact Hx|].
    assert (OW : forall W, (forall w, In w W -> exists b, In b L /\ In (blk_id b) ex /\ blk_addr b <= fst w /\ snd w <= blk_addr b + blk_size b) ->
                           outside W a).
    { induction W as [|[x y] W IH]; intros HW; [exact I|]. cbn [outside]. split; [|apply IH; intros w Hw; apply HW; right; exact Hw].
      destruct (HW (x, y) (or_introl eq_refl)) as (b0 & Hb0 & He & H1 & H2). cbn [fst snd] in H1, H2.
      pose proof (RMalloc_ifaceP.RHEAP_block_range_proof _ _ _ _ HP Hb0) as (C1 & C2 & C3 & C4 & C5).
      destruct Hc as [Hc|[Hc|(b & Hb & Hr)]]; [lia| unfold ralloc_static in Hc; lia|].
      destruct (HL b Hb) as [Hb' Hn].
      assert (NE : blk_id b0 <> blk_id b) by (intros E; apply Hn; rewrite <- E; exact He).
      pose proof (RMalloc_ifaceP.RHEAP_blocks_disjoint_proof _ _ _ b0 b HP Hb0 Hb' NE). lia. }
    exact (OW Wb HB).
Qed.

Lemma rbr_lin : forall A n, rblock_range A n -> 0 < A /\ A mod 16 = 0 /\ 0 <= n /\ A + n <= ATOP.
Proof. intros A n (H1 & H2 & H3 & H4 & _). tauto. Qed.
Lemma rbr_img : forall A n, rblock_range A n -> A + n <= 0x10000 \/ 0xa9000 <= A.
Proof. intros A n (_ & _ & _ & _ & H). exact H. Qed.
(* [comment removed for export] *)
Lemma lb_apart : forall s L LB m b0 a, RHEAP s (L ++ LB) m -> In b0 L -> in_block LB a -> ~ (blk_addr b0 <= a < blk_addr b0 + blk_size b0).
Proof.
  intros s L LB m b0 a HP H0 (b & Hb & Hr) Ha.
  pose proof (RMalloc_ifaceP.RHEAP_blocks_nodup_proof _ _ _ HP) as ND. rewrite map_app in ND.
  assert (NE : blk_id b0 <> blk_id b).
  { intros E. apply (nodup_app_disj _ _ _ (blk_id b0) ND); [apply in_map; exact H0| rewrite E; apply in_map; exact Hb]. }
  destruct (RMalloc_ifaceP.RHEAP_blocks_disjoint_proof _ _ _ b0 b HP ltac:(apply in_or_app; left; exact H0) ltac:(apply in_or_app; right; exact Hb) NE); lia.
Qed.
Lemma wr_at_wmono : forall m m' A n, wr_at psegs m A n -> wmono psegs m m' -> wr_at psegs m' A n.
Proof. intros m m' A n (H0 & H1 & H) W. split; [exact H0|]. split; [exact H1|]. intros i Hi. apply W. apply H. exact Hi. Qed.
Lemma wr_at_of_rw : forall m A cs, rw_cells psegs m A cs -> wr_at psegs m A (Z.of_nat (cells_size cs)).
Proof. intros m A cs [_ W]. exact W. Qed.
Lemma wr_at_sub : forall m A n n', wr_at psegs m A n -> 0 <= n' <= n -> wr_at psegs m A n'.
Proof. intros m A n n' (H0 & H1 & H) Hn. split; [exact H0|]. split; [lia|]. intros i Hi. apply H. lia. Qed.
Lemma strip_bom_shape : forall data, strip_bom data = data \/ exists a b c, data = a :: b :: c :: strip_bom data.
Proof.
  intros [|a [|b [|c r]]]; try (left; reflexivity). cbn [strip_bom].
  destruct ((a =? 239) && (b =? 187) && (c =? 191)); [right; exists a, b, c; reflexivity| left; reflexivity].
Qed.
Lemma Forall_strip_bom : forall (P : Z -> Prop) data, Forall P data -> Forall P (strip_bom data).
Proof.
  intros P data H. destruct (strip_bom_shape data) as [E|(a & b & c & E)]; [rewrite E; exact H|].
  rewrite E in H. inversion H as [|? ? _ F1]. inversion F1 as [|? ? _ F2]. inversion F2 as [|? ? _ F3]. exact F3.
Qed.
Lemma zlength_strip_bom : forall data, zlength (strip_bom data) = zlength data \/ zlength (strip_bom data) = zlength data - 3.
Proof.
  intros data. destruct (strip_bom_shape data) as [E|(a & b & c & E)]; [left; rewrite E; reflexivity|].
  right. rewrite E at 2. unfold zlength. cbn [length]. lia.
Qed.
(* [comment removed for export] *)
Lemma copy_s1buf : forall m A data bs z,
  rw_cells psegs m A [CB (Z.to_nat (zlength data)) bs] -> rw_cells psegs m (A + zlength data) [CB 64 (repeat z 64)] ->
  bs = map (Z_to_bv 8) data -> z = Z_to_bv 8 0 -> bytes_at psegs m A (s1buf data).
Proof.
  intros m A data bs z [[_ H1] _] [[_ H2] _] E Ez. cbn [cells_bytes cbytes] in H1, H2. rewrite app_nil_r in H1, H2.
  unfold s1buf. rewrite map_app, map_repeat. rewrite <- E, <- Ez.
  apply bytes_at_app_join; [exact H1|]. subst bs. rewrite length_map. unfold zlength in H2. exact H2.
Qed.
Lemma buf_strip : forall m A data, bytes_at psegs m A (s1buf data) ->
  bytes_at psegs m (A + (zlength data - zlength (strip_bom data))) (s1buf (strip_bom data)).
Proof.
  intros m A data H. destruct (strip_bom_shape data) as [E|(a & b & c & E)].
  - rewrite E. replace (A + (zlength data - zlength data)) with A by lia. exact H.
  - set (r := strip_bom data) in *. rewrite E in H.
    replace (s1buf (a :: b :: c :: r)) with ([Z_to_bv 8 a; Z_to_bv 8 b; Z_to_bv 8 c] ++ s1buf r) in H by reflexivity.
    apply bytes_at_app_split in H as [_ H]. cbn [length] in H.
    replace (zlength data - zlength r) with 3 by (rewrite E; unfold zlength; cbn [length]; lia). exact H.
Qed.

Lemma nodup7 : forall (x1 x2 x3 x4 x5 x6 x7 : bptr), List.NoDup [x1; x2; x3; x4; x5; x6; x7] ->
  x1 <> x2 /\ x1 <> x3 /\ x1 <> x4 /\ x1 <> x5 /\ x1 <> x6 /\ x1 <> x7 /\ x2 <> x3 /\ x2 <> x4 /\ x2 <> x5 /\ x2 <> x6 /\ x2 <> x7
  /\ x3 <> x4 /\ x3 <> x5 /\ x3 <> x6 /\ x3 <> x7 /\ x4 <> x5 /\ x4 <> x6 /\ x4 <> x7 /\ x5 <> x6 /\ x5 <> x7 /\ x6 <> x7.
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 N. apply NoDup_cons_iff in N as [N1 N]. apply NoDup_cons_iff in N as [N2 N]. apply NoDup_cons_iff in N as [N3 N].
  apply NoDup_cons_iff in N as [N4 N]. apply NoDup_cons_iff in N as [N5 N]. apply NoDup_cons_iff in N as [N6 _].
  cbn [In] in N1, N2, N3, N4, N5, N6.
  repeat split; intro E; subst;
    first [ apply N1; solve [repeat (first [left; reflexivity| right])] | apply N2; solve [repeat (first [left; reflexivity| right])]
          | apply N3; solve [repeat (first [left; reflexivity| right])] | apply N4; solve [repeat (first [left; reflexivity| right])]
          | apply N5; solve [repeat (first [left; reflexivity| right])] | apply N6; solve [repeat (first [left; reflexivity| right])] ].
Qed.

Lemma nodup7_perm : forall (x1 x2 x3 x4 x5 x6 x7 : bptr), List.NoDup [x1; x2; x3; x4; x5; x6; x7] -> List.NoDup [x5; x4; x1; x6; x7; x3; x2].
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 N. destruct (nodup7 _ _ _ _ _ _ _ N) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16 & E17 & E18 & E19 & E20 & E21).
  repeat constructor; cbn [In]; intros H; repeat destruct H as [H|H]; subst; tauto.
Qed.
Lemma pid_sizes : forall len, 0 <= len <= 2^20 - 64 ->
  4 * len + 36 <= SIDX_BYTES len /\ TAPE_BYTES len mod 8 = 0 /\ 8 * (len + 3) <= TAPE_BYTES len <= 2^27
  /\ 5 * len + 182 <= 3 * SB_BYTES len /\ len + 60 <= SB_BYTES len <= 2^24.
Proof.
  intros len H. assert (C : 32 <= CAP len <= 2^20) by (unfold CAP; lia).
  pose proof (ROUNDUP64_bounds (CAP len) ltac:(lia)) as R1. pose proof (ROUNDUP64_bounds (CAP len + 3) ltac:(lia)) as R2.
  pose proof (Z.div_mod (CAP len) 3 ltac:(lia)) as D3. pose proof (Z.mod_pos_bound (CAP len) 3 ltac:(lia)) as M3.
  pose proof (ROUNDUP64_bounds (5 * (CAP len / 3) + 64) ltac:(lia)) as R3.
  unfold SIDX_BYTES, TAPE_BYTES, SB_BYTES. split; [unfold CAP in *; lia|]. split; [rewrite Z.mul_comm; apply Z.mod_mul; lia|].
  split; [unfold CAP in *; lia|]. split; [unfold CAP in *; lia| unfold CAP in *; lia].
Qed.

(* [comment removed for export] *)
Lemma new_apart : forall s L1 LB m b0 SP a, RHEAP s (L1 ++ LB) m -> In b0 L1 -> rclient_addr LB SP a -> ATOP <= SP ->
  ~ (blk_addr b0 <= a < blk_addr b0 + blk_size b0).
Proof.
  intros s L1 LB m b0 SP a HP H0 Hc HS.
  pose proof (RMalloc_ifaceP.RHEAP_block_range_proof _ _ _ _ HP ltac:(apply in_or_app; left; exact H0)) as (C1 & C2 & C3 & C4 & C5).
  destruct Hc as [Hc|[Hc|Hc]]; [lia| unfold ralloc_static in Hc; lia| exact (lb_apart _ _ _ _ _ _ HP H0 Hc)].
Qed.

(* [comment removed for export] *)
Lemma pid_chain_B : forall (LB L5 L10 : list block) (SP SP' lo P R ACP ncp AIM ASI nsi ATP ntp ASB nsb AOC AIA len : Z) (m m4 m6 m0 m11 m12 : mem),
  rheap_pres_W LB SP ([(P, P + 80); (R, R + 24)] ++ client_wr) m m4 ->
  rheap_pres L5 SP' m4 m6 -> (forall b, In b LB -> In b L5) ->
  munch [(lo, SP'); (P + 64, P + 80); (ACP, ACP + ncp); (AIM + 48, AIM + 49)] m6 m0 -> wmono psegs m6 m0 ->
  rheap_pres_W L10 SP' (parse_win SP' AIM ASI len ATP ntp ASB nsb AOC AIA) m0 m11 -> (forall b, In b LB -> In b L10) ->
  munch [(lo, SP); (R, R + 24)] m11 m12 -> wmono psegs m11 m12 ->
  SP' <= SP -> ATOP <= lo -> lo <= SP' -> SP <= R -> R + 24 <= P ->
  (forall b, In b LB -> blk_addr b + blk_size b <= ATOP) ->
  (forall a, rclient_addr LB SP a -> ~ (ACP <= a < ACP + ncp)) ->
  (forall a, rclient_addr LB SP a -> ~ (AIM <= a < AIM + 96)) ->
  (forall a, rclient_addr LB SP a -> ~ (ASI <= a < ASI + nsi)) -> 4 * len + 36 <= nsi ->
  (forall a, rclient_addr LB SP a -> ~ (ATP <= a < ATP + ntp)) ->
  (forall a, rclient_addr LB SP a -> ~ (ASB <= a < ASB + nsb)) ->
  (forall a, rclient_addr LB SP a -> ~ (AOC <= a < AOC + 8192)) ->
  (forall a, rclient_addr LB SP a -> ~ (AIA <= a < AIA + 1024)) ->
  rheap_pres_W LB SP ([(P, P + 80); (R, R + 24)] ++ client_wr) m m12.
Proof.
  intros LB L5 L10 SP SP' lo P R ACP ncp AIM ASI nsi ATP ntp ASB nsb AOC AIA len m m4 m6 m0 m11 m12 PW1 HPR6 IN5 MUall WMall RPW IN10 MU12 WM12
    HS1 HLO HLO2 HR HRP LBB NAC NAM NAS HSI NAT NAB NAO NAA.
  atop_facts.
  assert (LO : forall a, rclient_addr LB SP a -> SP <= a \/ a < lo).
  { intros a [Hc|[Hc|(b & Hb & Hr)]]; [left; lia| right; lia| right; pose proof (LBB b Hb); lia]. }
  eapply rheap_pres_W_trans; [exact PW1|].
  eapply rheap_pres_W_trans; [eapply rheap_pres_W_of_pres; [exact HPR6| lia| exact IN5]|].
  eapply rheap_pres_W_trans.
  { eapply rheap_pres_W_of_munch; [exact MUall| exact WMall|]. intros a Ha Hc Hx.
    pose proof (NAC a Hc). pose proof (NAM a Hc). pose proof (LO a Hc). cbn in Hx |- *. repeat split; try exact I; lia. }
  eapply rheap_pres_W_trans.
  { eapply rheap_pres_W_of_W; [exact RPW| lia| exact IN10|]. intros a Ha Hc Hx.
    pose proof (NAM a Hc). pose proof (NAS a Hc). pose proof (NAT a Hc). pose proof (NAB a Hc). pose proof (NAO a Hc). pose proof (NAA a Hc).
    unfold parse_win. cbn [outside]. repeat split; try exact I; lia. }
  eapply rheap_pres_W_of_munch; [exact MU12| exact WM12|]. intros a Ha Hc Hx. pose proof (LO a Hc). cbn in Hx |- *. repeat split; try exact I; lia.
Qed.

Lemma strip_bom_3 : forall a b c r, strip_bom (a :: b :: c :: r) = if (a =? 239) && (b =? 187) && (c =? 191) then r else a :: b :: c :: r.
Proof. reflexivity. Qed.
Lemma list3 : forall (l : list Z), (3 <= length l)%nat -> exists a b c r, l = a :: b :: c :: r.
Proof. intros [|a [|b [|c r]]] H; cbn in H; try lia. exists a, b, c, r. reflexivity. Qed.
Lemma strip_bom_short : forall data, (length data < 3)%nat -> strip_bom data = data.
Proof. intros [|a [|b [|c r]]] H; cbn in H; try lia; reflexivity. Qed.

(* [comment removed for export] *)
Ltac blk_find L X := lazymatch L with
  | (?p, X, ?n) :: _ => constr:((p, X, n))
  | _ :: ?L' => blk_find L' X
  end.
Ltac rcr := lazymatch goal with |- rclient_range ?L ?SP ?A ?n =>
  first [ is_Zlit A; right; left; unfold RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP; cbn; lia
        | let X := lazymatch A with ?X + _ => X | ?X => X end in
          let b := blk_find L X in
          right; right; exists b; split; [cbn [In]; repeat (first [left; reflexivity| right]) | cbn; lia]
        | left; cbn; lia ] end.
(* [comment removed for export] *)
Definition skipped (P : Prop) : Prop := P.
Ltac skip_it H := lazymatch type of H with ?T => change (skipped T) in H end.
Ltac unskip := repeat match goal with H : skipped _ |- _ => unfold skipped in H end.
Ltac trx HPR :=
  lazymatch type of HPR with rheap_pres_x ?L ?SP ?X ?n ?mo ?mn =>
  repeat match goal with
  | H : rw_cells psegs mo ?A ?cs |- _ =>
      let H' := fresh "T" in
      first [ assert (H' : rw_cells psegs mn A cs) by (eapply rheap_pres_x_rw_cells; [exact HPR| exact H| rcr | cbn; lia]); clear H; rename H' into H
            | skip_it H ]
  | H : bytes_at psegs mo ?A ?bs |- _ =>
      let H' := fresh "T" in
      first [ assert (H' : bytes_at psegs mn A bs) by (eapply rheap_pres_x_bytes_at; [exact HPR| exact H| rcr | cbn; lia]); clear H; rename H' into H
            | skip_it H ]
  end end; unskip.
(* [comment removed for export] *)
Ltac trW HPR :=
  lazymatch type of HPR with rheap_pres_W ?L ?SP ?W ?mo ?mn =>
  repeat match goal with
  | H : rw_cells psegs mo ?A ?cs |- _ =>
      let H' := fresh "T" in
      first [ assert (H' : rw_cells psegs mn A cs) by (eapply rheap_pres_W_rw_cells; [exact HPR| exact H| rcr | cbn; lia]); clear H; rename H' into H
            | skip_it H ]
  end end; unskip.
(* [comment removed for export] *)
Ltac trp HPR :=
  lazymatch type of HPR with rheap_pres ?L ?SP ?mo ?mn =>
  repeat match goal with
  | H : rw_cells psegs mo ?A ?cs |- _ =>
      let H' := fresh "T" in
      first [ assert (H' : rw_cells psegs mn A cs) by (eapply rheap_pres_rw_cells; [exact HPR| exact H| rcr]); clear H; rename H' into H
            | skip_it H ]
  | H : bytes_at psegs mo ?A ?bs |- _ =>
      let H' := fresh "T" in
      first [ assert (H' : bytes_at psegs mn A bs) by (eapply rheap_pres_bytes_at'; [exact HPR| exact H| rcr]); clear H; rename H' into H
            | skip_it H ]
  end end; unskip.
(* [comment removed for export] *)
Ltac trm MU WM :=
  lazymatch type of MU with munch ?W ?mo ?mn =>
  repeat match goal with
  | H : rw_cells psegs mo ?A ?cs |- _ =>
      let H' := fresh "T" in
      first [ assert (H' : rw_cells psegs mn A cs) by (eapply rw_cells_transport; [exact H| exact MU| exact WM| cbn; lia]); clear H; rename H' into H
            | skip_it H ]
  | H : bytes_at psegs mo ?A ?bs |- _ =>
      let H' := fresh "T" in
      first [ assert (H' : bytes_at psegs mn A bs) by (eapply bytes_at_transport; [exact H| exact MU| cbn; lia]); clear H; rename H' into H
            | skip_it H ]
  end end; unskip.

(* [comment removed for export] *)
Definition parked (P : Prop) : Prop := P.
Ltac park_mem m := repeat match goal with
  | H : rw_cells psegs m _ _ |- _ => lazymatch type of H with ?T => change (parked T) in H end
  | H : bytes_at psegs m _ _ |- _ => lazymatch type of H with ?T => change (parked T) in H end end.
Ltac unpark := repeat match goal with H : parked _ |- _ => unfold parked in H end.
Ltac lit_if := lazymatch goal with |- evt _ _ (MS ?R ?F (if ?c then ?x else ?y) ?fc ?rv ?mm ?ro) =>
   let v := eval vm_compute in c in
   lazymatch v with true => change (if c then x else y) with x | false => change (if c then x else y) with y end end.
Ltac ret_lit := lazymatch goal with |- context [ret_pc (Z_to_bv 64 ?r)] =>
      replace (ret_pc (Z_to_bv 64 r)) with (Z_to_bv 64 r) by (symmetry; rpc) end.

Section Proof.
  Hypothesis ONT : opnew_nt_stmt.
  Hypothesis PARSE : parse_stmt.

  Theorem pid_proof : pid_stmt.
  Proof.
    unfold pid_stmt. intros until jr. intros HP DAT DB DCR D0 DTOP DL DWR CI CS AUX SPB SP47 SPA ST LOA LOS ERR MI FZ TP
      PIM PDOC PMAX PCP PR RSP0 RP PTOP P8 RSTK A0 A1 A2 A3 A4 A5.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    unfold PID_STACK, PARSE_STACK, PS2_STACK, OPNEW_NT_STACK, OPNEW_STACK, RMALLOC_STACK in LOS. atop_facts.
    subst tp. rewrite errno_lit in ERR. unfold RERRNO in ERR.
    destruct CI as (VTI & VTD & GOT & FMIN).
    unfold PVTAB_IMPL, vtab_impl_cells in VTI. unfold PVTAB_DOM, vtab_dom_cells in VTD.
    unfold PGOT_NOTHROW, got_nothrow_cells, PNOTHROW in GOT. unfold PFMIN, fmin_cells in FMIN.
    set (len := zlength data) in *.
    assert (LEN0 : 0 <= len) by (unfold len, zlength; lia).
    pose proof (RMalloc_ifaceP.RHEAP_block_range_proof s LB m) as LBR.
    assert (LBB : forall b, In b LB -> blk_addr b + blk_size b <= ATOP) by (intros b Hb; destruct (LBR b HP Hb) as (_ & _ & _ & R4 & _); exact R4).
    clear LBR.
    assert (DSEP : hidden (D + len <= lo \/ P + 80 <= D)).
    { unfold hidden. destruct DCR as [H|[H|(b & Hb & H1 & H2)]]; [right; lia| left; lia| left; pose proof (LBB b Hb); lia]. }
    remember (map (Z_to_bv 8) data) as bs eqn:EBS.
    assert (BSL : Z.of_nat (length bs) = len) by (subst bs; unfold len, zlength; rewrite length_map; reflexivity).
    unfold HarnessP.parse_into_doc. fold len.
    apply implM_from_evt.
    pose proof (munch_refl [(lo, bv_unsigned sp); (P, P + 80); (R, R + 24)] m) as MU. pose proof (wmono_refl psegs m) as WM.
    carve_frame 80%nat ST.
    subst a0 a1 a2 a3 a4 a5. unfold PPID, w64 in *.
    assert (CAPR : 32 <= CAP len < 2^26 + 32) by (unfold CAP; lia).
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU0. pose proof (wmono_refl psegs m) as WM0.
    park_mem m. unfold parked in FR.
    do 19 zstep.
    unpark. unfold hidden in DSEP. trm MU0 WM0. change (D + len <= lo \/ P + 80 <= D) with (hidden (D + len <= lo \/ P + 80 <= D)) in DSEP.
    clear MU0 WM0.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      apply (evt_cut psegs (fun x => x = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -80)) gp (Z_to_bv 64 RATP) t0 t1 t2 (Z_to_bv 64 R) (Z_to_bv 64 (P + 24))
          (Z_to_bv 64 32) (Z_to_bv 64 P) (Z_to_bv 64 (P + 24)) (Z_to_bv 64 D) (Z_to_bv 64 len) (Z_to_bv 64 1) a6 a7 (Z_to_bv 64 len) (Z_to_bv 64 P)
          (Z_to_bv 64 D) (Z_to_bv 64 1) s6 (Z_to_bv 64 (CAP len)) s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x26f1c) fc None mm (seg_rom psegs)))
    end.
    { zstep. if_cases K0; zify_cond K0.
      - apply evt_done. unfold CAP. rewrite Z.max_l by lia. reflexivity.
      - zstep. apply evt_done. unfold CAP. rewrite Z.max_r by lia. reflexivity. }
    intros ms0 ->.
    do 2 zstep. lit_if.
    do 2 zstep.
    if_cases K1; zify_cond K1; [| exfalso; lia].
    do 3 zstep.
    if_cases K2; zify_cond K2; [exfalso; lia|].
    do 3 zstep.
    apply evt_done.
    (* [comment removed for export] *)
    pose proof (cstat_transport _ _ (stat_pres_of_munch _ _ _ MU WM ltac:(intros a Ha; cbn; lia)) CS) as CS1; clear CS.
    lazymatch goal with |- implM _ _ _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (HP1 : RHEAP s LB mx) by (eapply RHEAP_stack_frame; [exact HP| exact MU| exact WM| repeat constructor; cbn; lia]);
      assert (AUX1 : rauxv_ok mx B) by (eapply rauxv_ok_stack_frame; [exact AUX| exact MU| exact WM| repeat constructor; cbn; lia])
    end.
    clear HP AUX.
    eapply implM_bind.
    { eapply (docalloc_proof ONT) with (lo := lo) (B := B) (DOC := P + 24) (c0 := Z_to_bv 64 0); try reflexivity; unfold RATP; rewrite ?unsigned_lit by lia;
        first [exact HP1 | exact AUX1 | exact ST | exact MI | (rewrite errno_lit; unfold RERRNO; exact ERR) | exact PDOC | exact GOT
              | (unfold DOCALLOC_STACK, OPNEW_NT_STACK, OPNEW_STACK, RMALLOC_STACK; lia) | lia]. }
    cbv beta. intros [psb ptp] s1' ms1 PO.
    destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & errv1 & -> & MI2 & ST2 & ERR2 & AUX2 & HPR1 & FAE1 & SOE1 & RR1).
    destruct RR1 as (ASB & ATP & jsb & jtp & BRS & BRT & HP2 & BLKS & BLKT & DC2). cbn [fst snd] in *.
    rewrite ?unsigned_lit in ST2 by lia. rewrite ?unsigned_lit in HPR1 by lia. rewrite errno_lit in ERR2. unfold RERRNO in ERR2.
    ret_lit.
    pose proof (stat_pres_of_x _ _ _ _ _ _ HPR1 ltac:(lia)) as SP1.
    pose proof (cstat_transport _ _ SP1 CS1) as CS2. clear CS1 SP1.
    clear PDOC ERR.
    assert (RSTK2 : stk psegs m2 R (P + 80)).
    { eapply stk_of_x_stk; [exact HPR1| exact RSTK| | lia| lia| lia]. pose proof (stk_of_cells _ _ _ DC2) as X. cbn in X. exact X. }
    clear RSTK.
    assert (DAT2 : bytes_at psegs m2 D bs)
      by (eapply rheap_pres_x_bytes_at; [exact HPR1| exact DAT| rewrite BSL; eapply rclient_range_sp; [exact DCR| lia] | rewrite BSL; lia]).
    clear DAT.
    trx HPR1.
    (* [comment removed for export] *)
    apply implM_from_evt.
    do 3 zstep. lit_if. do 1 zstep.
    eapply evt_cut.
    { eapply active_proof with (lo := lo); rewrite ?unsigned_lit by lia; first [exact ST2 | exact MI2 | exact CS2 | (unfold ACTIVE_STACK; lia) | lia]. }
    intros ms2 PO.
    destruct PO as (v0 & v1 & v2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m3 & -> & MI3 & ST3 & MU3 & WM3 & CSB3).
    rewrite ?unsigned_lit in ST3, MU3 by lia. unfold active_W, client_wr in MU3.
    ret_lit.
    assert (DAT3 : bytes_at psegs m3 D bs).
    { eapply bytes_at_transport_pw; [exact DAT2| exact MU3|]. rewrite BSL. intros a Ha. cbn.
      pose proof (DWR a Ha) as Hw. cbn in Hw. split; [unfold hidden in DSEP; destruct DSEP; lia| tauto]. }
    clear DAT2.
    assert (RSTK3 : stk psegs m3 R (P + 80)) by (eapply stk_transport_disjoint; [exact RSTK2| exact MU3| exact WM3| cbn; lia]).
    clear RSTK2.
    pose proof (rbr_lin _ _ BRS) as (BRS1 & BRS2 & BRS3 & BRS4). pose proof (rbr_lin _ _ BRT) as (BRT1 & BRT2 & BRT3 & BRT4).
    pose proof (rbr_img _ _ BRS) as BRS5. pose proof (rbr_img _ _ BRT) as BRT5.
    trm MU3 WM3.
    clear BRS5 BRT5.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (HP3 : RHEAP s1' ((ptp, ATP, TAPE_BYTES len) :: (psb, ASB, SB_BYTES len) :: LB) mx)
        by (eapply RMalloc_ifaceP.RHEAP_frame_proof; [exact HP2| exact MU3| exact WM3|];
            apply Forall_cons; [left; cbn; lia|];
            repeat (apply Forall_cons; [right; left; unfold RLIBC, RCTX, RSSP_GUARD, RGOT_SSP; cbn; lia|]); apply Forall_nil);
      assert (AUX3 : rauxv_ok mx B)
        by (eapply rauxv_ok_frame; [exact AUX2| exact MU3| exact WM3| repeat (apply Forall_cons; [cbn; unfold RAUXV_CELL in *; lia|]); apply Forall_nil])
    end.
    clear HP2 AUX2.
    (* [comment removed for export] *)
    destruct CSB3 as (SA1 & SA2 & SA3 & SA4). unfold PACTIVE, PACTIVE_GUARD, PFALLBACK, PFALLBACK_GUARD, guard1, fallback_cells,
      PFALLBACK_VT, PFALLBACK_NAME, PFALLBACK_DESC, w0 in SA1, SA2, SA3, SA4.
    unfold PACTIVE.
    do 9 zstep.
    apply evt_done.
    eapply implM_bind.
    { eapply (create_proof ONT) with (lo := lo) (B := B) (DST := P + 8) (len := len); try reflexivity; unfold RATP; rewrite ?unsigned_lit by lia;
        first [exact HP3 | exact AUX3 | exact ST3 | exact MI3 | (rewrite errno_lit; unfold RERRNO; exact ERR2) | exact PIM | exact GOT | exact VTD
              | (unfold CREATE_STACK, OPNEW_NT_STACK, OPNEW_STACK, RMALLOC_STACK; lia) | lia]. }
    cbv beta. intros [[[pim psi] poc] pia] s2' ms3 PO.
    destruct PO as (w0' & w1 & w2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & m4 & errv4 & -> & MI4 & ST4 & ERR4 & AUX4 & HPR4 & FAE4 & SOE4 & RR4).
    destruct RR4 as (AIM & ASI & AOC & AIA & p1 & p2 & pad & jsi & joc & jia & BRM & BRI & BRO & BRA & HP4 & DST4 & OBJ4 & IDX4 & OC4 & IA4).
    rewrite ?unsigned_lit in ST4 by lia. rewrite ?unsigned_lit in HPR4 by lia. rewrite errno_lit in ERR4. unfold RERRNO in ERR4.
    ret_lit.
    unfold PC_create.w64 in *.
    assert (DAT4 : bytes_at psegs m4 D bs)
      by (eapply rheap_pres_x_bytes_at; [exact HPR4| exact DAT3| rewrite BSL; apply rclient_range_app_r with (L1 := [_; _]); eapply rclient_range_sp; [exact DCR| lia] | rewrite BSL; lia]).
    clear DAT3 ERR2.
    assert (RSTK4 : stk psegs m4 R (P + 80)).
    { eapply stk_of_x_stk; [exact HPR4| exact RSTK3| | lia| lia| lia]. pose proof (stk_of_cells _ _ _ DST4) as X. cbn in X. exact X. }
    clear RSTK3.
    trx HPR4.
    pose proof (wr_at_of_rw _ _ _ OBJ4) as WO4. cbn [impl_cells cells_size csize Nat.add] in WO4.
    destruct (impl_split _ _ _ _ _ _ _ _ _ OBJ4) as (OB0 & OB8 & OB16 & OB24 & OB40 & OB56). clear OBJ4.
    pose proof (rbr_lin _ _ BRM) as (BRM1 & BRM2 & BRM3 & BRM4). pose proof (rbr_lin _ _ BRI) as (BRI1 & BRI2 & BRI3 & BRI4).
    pose proof (rbr_lin _ _ BRO) as (BRO1 & BRO2 & BRO3 & BRO4). pose proof (rbr_lin _ _ BRA) as (BRA1 & BRA2 & BRA3 & BRA4).
    unfold IMPL_BYTES, OC_BYTES, ISARR_BYTES, MAX_DEPTH in *.
    apply implM_from_evt.
    zstep. lit_if. zstep. zstep. lit_if. zstep. lit_if. zstep. zstep. lit_if.
    zstep. zstep. zstep.
    pose proof (munch_refl [(lo, bv_unsigned sp); (P, P + 80); (R, R + 24)] m4) as MU5. pose proof (wmono_refl psegs m4) as WM5.
    (* [comment removed for export] *)
    assert (PW1 : rheap_pres_W LB (bv_unsigned sp) ([(P, P + 80); (R, R + 24)] ++ client_wr) m m4).
    { assert (OUT1 : forall a, 0 <= a < 2^64 -> rclient_addr LB (bv_unsigned sp) a -> outside ([(P, P + 80); (R, R + 24)] ++ client_wr) a ->
                 bv_unsigned sp <= a \/ a < lo).
      { intros a Ha Hc Hx. destruct Hc as [Hc|[Hc|(b & Hb & Hr)]]; [left; lia| right; lia| right; pose proof (LBB b Hb); lia]. }
      eapply rheap_pres_W_trans.
      { eapply rheap_pres_W_of_munch; [exact MU| exact WM|]. intros a Ha Hc Hx. pose proof (OUT1 a Ha Hc Hx). cbn in Hx |- *. lia. }
      eapply rheap_pres_W_trans.
      { eapply rheap_pres_W_of_x; [exact HPR1| lia| intros b Hb; exact Hb|]. intros a Ha Hc Hx. cbn in Hx. lia. }
      eapply rheap_pres_W_trans.
      { eapply rheap_pres_W_of_munch; [exact MU3| exact WM3|]. intros a Ha Hc Hx. pose proof (OUT1 a Ha Hc Hx). cbn in Hx |- *. lia. }
      eapply rheap_pres_W_of_x; [exact HPR4| lia| intros b Hb; right; right; exact Hb|]. intros a Ha Hc Hx. cbn in Hx. lia. }
    if_cases KC; zify_cond KC.
    - (* [comment removed for export] *)
      pose proof (munch_refl [(lo, bv_unsigned sp); (P + 64, P + 72); (R, R + 24)] m4) as MU6. pose proof (wmono_refl psegs m4) as WM6.
      park_mem m4. unfold parked in FR, PR, PCP.
      zstep. zstep. zstep. lit_if. zstep. lit_if. zstep. zstep.
      do 4 zstep.
      do 12 zstep.
      unpark. trm MU6 WM6. clear MU6 WM6.
      release_frame FR ST4 (bv_unsigned sp).
      apply evt_done.
      unfold HarnessP.padded_alloc. replace (copy_made len) with false
        by (unfold copy_made, COPY_BYTES, PADDING, COPY_LIMIT; symmetry; apply Z.leb_gt; lia).
      apply implM_retb. cbv beta iota. apply implM_retb. apply implM_ret. apply evt_done.
      unfold pid_post. do 15 eexists. exists F, fc. eexists. exists errv4. split; [reflexivity|].
      split; [exact FZ|]. split; [exact MI4|]. split; [exact ST4|]. split; [rewrite errno_lit; exact ERR4|].
      split; [eapply rauxv_ok_stack_frame; [exact AUX4| exact MU5| exact WM5| repeat constructor; cbn; lia]|].
      split.
      { eapply rheap_pres_W_trans; [exact PW1|]. eapply rheap_pres_W_of_munch; [exact MU5| exact WM5|].
        intros a Ha Hc Hx. destruct Hc as [Hc|[Hc|(b & Hb & Hr)]]; cbn in Hx |- *; [lia| lia| pose proof (LBB b Hb); lia]. }
      split; [congruence|]. split; [congruence|].
      split; [unfold cstat_built, PACTIVE, PACTIVE_GUARD, PFALLBACK, PFALLBACK_GUARD, guard1, fallback_cells, PFALLBACK_VT, PFALLBACK_NAME, PFALLBACK_DESC, w0;
              split; [exact SA1|]; split; [exact SA2|]; split; [exact SA3| exact SA4]|].
      split; [exact RSTK4|].
      exists ASB, ATP, AIM, ASI, AOC, AIA, 0.
      split; [eapply RHEAP_stack_frame; [exact HP4| exact MU5| exact WM5| repeat constructor; cbn; lia]|].
      split; [exact DST4|].
      split; [destruct (rw_cells_app_split psegs _ (P + 24) [C8 (Z_to_bv 64 ATP); C8 (Z_to_bv 64 ASB)] [_] DC2) as [X _]; exact X|].
      split; [destruct (rw_cells_cons_split _ _ _ _ PCP) as [X _]; exact X|].
      split; [exact OB0|]. split; [exact OB16|].
      destruct (rw_cells_app_split psegs _ (AIM + 56) [C8 (Z_to_bv 64 AOC); C8 (Z_to_bv 64 AIA)] [_; _; _] OB56) as [X _]; exact X.
    - (* [comment removed for export] *)
      destruct (pid_sizes len ltac:(lia)) as (SZ1 & SZ2 & SZ3 & SZ4 & SZ5).
      do 4 zstep.
      apply evt_done.
      unfold HarnessP.padded_alloc. replace (copy_made len) with true
        by (unfold copy_made, COPY_BYTES, PADDING, COPY_LIMIT; symmetry; apply Z.leb_le; lia).
      apply implM_bind_assoc.
      lazymatch goal with |- implM _ _ _ _ (MS _ _ _ _ _ ?mx _) =>
        assert (HP5 : RHEAP s2' ((pia, AIA, 1024) :: (poc, AOC, 8 * 1024) :: (psi, ASI, SIDX_BYTES len) :: (pim, AIM, 96)
                                 :: (ptp, ATP, TAPE_BYTES len) :: (psb, ASB, SB_BYTES len) :: LB) mx)
          by (eapply RHEAP_stack_frame; [exact HP4| exact MU5| exact WM5| repeat constructor; cbn; lia]);
        assert (AUX5 : rauxv_ok mx B) by (eapply rauxv_ok_stack_frame; [exact AUX4| exact MU5| exact WM5| repeat constructor; cbn; lia])
      end.
      eapply implM_bind.
      { eapply (proj2 ONT) with (lo := lo) (B := B) (n := COPY_BYTES len); try reflexivity; unfold RATP; rewrite ?unsigned_lit by lia;
          first [exact HP5 | exact AUX5 | exact ST4 | exact MI4 | (rewrite errno_lit; unfold RERRNO; exact ERR4) | (unfold OPNEW_NT_STACK, OPNEW_STACK, RMALLOC_STACK; lia)
                | (unfold COPY_BYTES, PADDING; reflexivity) | (unfold COPY_BYTES, PADDING; lia)]. }
      cbv beta. intros pcp s3' ms4 PO.
      destruct PO as (x0 & x1 & x2 & e0 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & x3 & x4 & x5 & x6 & m6 & errv6 & -> & MI6 & ST6 & ERR6 & AUX6 & HPR6 & FAE6 & SOE6 & RR6).
      destruct RR6 as (ACP & jcp & -> & BRC & HP6 & BLKC & _).
      rewrite ?unsigned_lit in ST6 by lia. rewrite ?unsigned_lit in HPR6 by lia. rewrite errno_lit in ERR6. unfold RERRNO in ERR6.
      ret_lit.
      apply implM_retb.
      pose proof (rbr_lin _ _ BRC) as (BRC1 & BRC2 & BRC3 & BRC4). unfold COPY_BYTES, PADDING in *.
      assert (DAT6 : bytes_at psegs m6 D bs)
        by (eapply rheap_pres_bytes_at'; [exact HPR6| exact DAT4| rewrite BSL; apply rclient_range_app_r with (L1 := [_; _; _; _; _; _]); eapply rclient_range_sp; [exact DCR| lia]]).
      clear DAT4 ERR4.
      assert (RSTK6 : stk psegs m6 R (P + 80)) by (eapply rheap_pres_stk; [exact HPR6| exact RSTK4| lia]). clear RSTK4.
      trp HPR6.
      (* [comment removed for export] *)
      apply implM_from_evt.
      zstep. if_cases KN; zify_cond KN; [exfalso; lia| clear KN].
      do 5 zstep.
      pose proof (rw_cells_split_CB psegs m6 ACP [] (Z.to_nat (len + 64)) jcp [] [Z.to_nat len; 64%nat] BLKC ltac:(cbn; lia)) as SPL.
      cbn [app mk_CB_cells] in SPL. apply rw_cells_cons_split in SPL as [CPA CPB]. cbn [csize] in CPB.
      rewrite Z2Nat.id in CPB by lia. clear BLKC.
      eapply evt_cut.
      { eapply memset_spec; rewrite ?unsigned_lit by lia; [exact CPB| exact MI6]. }
      intros ms7 PO. destruct PO as (y0 & y1 & y2 & f1 & f2 & f3 & f4 & f5 & f6 & f7 & y3 & y4 & y5 & y6 & m7 & -> & MU7 & WM7 & MI7 & SET7).
      rewrite ?unsigned_lit in MU7, SET7 by lia.
      ret_lit.
      (* [comment removed for export] *)
      assert (CPA7 : rw_cells psegs m7 ACP [CB (Z.to_nat len) (firstn (Z.to_nat len) jcp)])
        by (eapply rw_cells_transport; [exact CPA| exact MU7| exact WM7| cbn [disjoint_from cells_size csize]; rewrite ?Nat.add_0_r, ?Z2Nat.id by lia; lia]).
      assert (PCP7 : rw_cells psegs m7 (P + 64) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)])
        by (eapply rw_cells_transport; [exact PCP| exact MU7| exact WM7| cbn; lia]).
      assert (ST7 : stk psegs m7 lo (bv_unsigned sp + -80))
        by (eapply stk_transport_disjoint; [exact ST6| exact MU7| exact WM7| cbn; lia]).
      assert (RSTK7 : stk psegs m7 R (P + 80)) by (eapply stk_transport_disjoint; [exact RSTK6| exact MU7| exact WM7| cbn; lia]). clear RSTK6.
      (* [comment removed for export] *)
      assert (DSEPC : D + len <= ACP \/ ACP + (len + 64) <= D).
      { unfold hidden in DSEP. pose proof (rbr_img _ _ BRC) as BRC5.
        destruct DCR as [H|[H|(b & Hb & H1 & H2)]]; [lia| lia|].
        pose proof (new_block_disj _ _ _ _ _ _ b HP6 ltac:(do 6 right; exact Hb)) as DB'. lia. }
      assert (DAT7 : bytes_at psegs m7 D bs)
        by (eapply bytes_at_transport; [exact DAT6| exact MU7| cbn; rewrite BSL; lia]).
      change (munch ?W m6 m7) with (hidden (munch W m6 m7)) in MU7. change (wmono psegs m6 m7) with (hidden (wmono psegs m6 m7)) in WM7.
      pose proof (munch_refl [(lo, bv_unsigned sp + -80); (P + 64, P + 80)] m7) as MU8. pose proof (wmono_refl psegs m7) as WM8.
      (* [comment removed for export] *)
      zstep. zstep. zstep. lit_if. zstep. if_cases KN2; zify_cond KN2; [exfalso; lia| clear KN2].
      do 5 zstep.
      eapply evt_cut.
      { eapply memcpy_spec; rewrite ?unsigned_lit by lia; [exact DAT7| rewrite <- BSL, Nat2Z.id; reflexivity| exact CPA7| lia| exact MI7]. }
      intros ms9 PO. destruct PO as (z0 & z1 & z2 & g1 & g2 & g3 & g4 & g5 & g6 & g7 & z3 & z4 & z5 & z6 & m9 & -> & MU9 & WM9 & MI9 & CPY9 & DAT9).
      rewrite ?unsigned_lit in MU9 by lia. rewrite ?unsigned_lit in CPY9 by lia. rewrite ?unsigned_lit in DAT9 by lia.
      clear DSEPC.
      ret_lit.
      assert (PCP9 : rw_cells psegs m9 (P + 64) [C8 (Z_to_bv 64 ACP); C8 (Z_to_bv 64 len)])
        by (eapply rw_cells_transport; [exact PCP7| exact MU9| exact WM9| cbn; lia]).
      assert (ST9 : stk psegs m9 lo (bv_unsigned sp + -80))
        by (eapply stk_transport_disjoint; [exact ST7| exact MU9| exact WM9| cbn; lia]).
      assert (RSTK9 : stk psegs m9 R (P + 80)) by (eapply stk_transport_disjoint; [exact RSTK7| exact MU9| exact WM9| cbn; lia]). clear RSTK7.
      lazymatch type of SET7 with rw_cells _ _ _ ?cs =>
        assert (SET9 : rw_cells psegs m9 (ACP + len) cs) by (eapply rw_cells_transport; [exact SET7| exact MU9| exact WM9| cbn; lia]) end.
      clear PCP7 ST7 SET7 CPA7 DAT7.
      change (munch ?W m5 m9) with (hidden (munch W m5 m9)) in MU9. change (munch ?W m7 m5) with (hidden (munch W m7 m5)) in MU8.
      (* [comment removed for export] *)
      zstep. zstep. zstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      apply (evt_cut psegs (fun x => exists (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
          x = MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -80)) gp (Z_to_bv 64 RATP) t0' t1' t2' (Z_to_bv 64 R) (Z_to_bv 64 (P + 24))
                  a0' a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 (zlength (strip_bom data))) (Z_to_bv 64 P)
                  (Z_to_bv 64 (ACP + (len - zlength (strip_bom data)))) (Z_to_bv 64 0) (Z_to_bv 64 ACP) (Z_to_bv 64 (CAP len))
                  (Z_to_bv 64 (P + 8)) s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 0x27048) fc None mm (seg_rom psegs)))
      end.
      { if_cases K3; zify_cond K3.
        - (* [comment removed for export] *)
          assert (SB : strip_bom data = data) by (apply strip_bom_short; unfold len, zlength in K3; lia).
          rewrite SB. replace (ACP + (len - zlength data)) with ACP by (unfold len; lia).
          apply evt_done. do 16 eexists. reflexivity.
        - (* [comment removed for export] *)
          destruct (list3 data ltac:(unfold len, zlength in K3; lia)) as (q0 & q1 & q2 & r & EDATA).
          assert (XB : 0 <= q0 < 256 /\ 0 <= q1 < 256 /\ 0 <= q2 < 256).
          { rewrite EDATA in DB. inversion DB as [|? ? X0 DB1]; subst. inversion DB1 as [|? ? X1 DB2]; subst.
            inversion DB2 as [|? ? X2 _]; subst. exact (conj X0 (conj X1 X2)). }
          assert (RL : zlength r = len - 3) by (unfold len; rewrite EDATA; unfold zlength; cbn [length]; lia).
          assert (CPYb : rw_cells psegs m9 ACP [C1 (Z_to_bv 8 q0); C1 (Z_to_bv 8 q1); C1 (Z_to_bv 8 q2); CB (Z.to_nat (len - 3)) (map (Z_to_bv 8) r)]).
          { apply (InitMem.rw_cells_recast psegs m9 ACP _ _ CPY9).
            - cbn. split; [exact I|]. split; [exact I|]. split; [exact I|]. split; [|exact I]. rewrite length_map. unfold zlength in RL. lia.
            - cbn [cells_bytes cbytes app]. rewrite EBS, EDATA. cbn [map app]. rewrite ?app_nil_r. reflexivity.
            - cbn [cells_size csize]. unfold zlength in RL. lia. }
          assert (ROB0 : ro_cells psegs m9 0x1243d [C1 (Z_to_bv 8 239)]).
          { assert (R0 : ro_cells psegs m9 0x1243d [CB 1 [Z_to_bv 8 239]])
              by (apply (ro_cells_image psegs m9 0x1243d [Z_to_bv 8 239]); [exact MI9| vm_compute; reflexivity| lia| cbn; lia]).
            destruct R0 as [Hwf Hb]. split; [cbn; repeat split; exact I| exact Hb]. }
          assert (ROB1 : ro_cells psegs m9 0x1243e [C1 (Z_to_bv 8 187)]).
          { assert (R0 : ro_cells psegs m9 0x1243e [CB 1 [Z_to_bv 8 187]])
              by (apply (ro_cells_image psegs m9 0x1243e [Z_to_bv 8 187]); [exact MI9| vm_compute; reflexivity| lia| cbn; lia]).
            destruct R0 as [Hwf Hb]. split; [cbn; repeat split; exact I| exact Hb]. }
          assert (ROB2 : ro_cells psegs m9 0x1243f [C1 (Z_to_bv 8 191)]).
          { assert (R0 : ro_cells psegs m9 0x1243f [CB 1 [Z_to_bv 8 191]])
              by (apply (ro_cells_image psegs m9 0x1243f [Z_to_bv 8 191]); [exact MI9| vm_compute; reflexivity| lia| cbn; lia]).
            destruct R0 as [Hwf Hb]. split; [cbn; repeat split; exact I| exact Hb]. }
          clear CPY9.
          apply rw_cells_cons_split in CPYb as [CPY0 CPYb]. apply rw_cells_cons_split in CPYb as [CPY1 CPYb].
          apply rw_cells_cons_split in CPYb as [CPY2 CPYr]. cbn [csize] in CPY1, CPY2, CPYr.
          change (Z.of_nat 1) with 1 in CPY1, CPY2, CPYr.
          replace (ACP + 1 + 1) with (ACP + 2) in CPY2, CPYr by lia. replace (ACP + 2 + 1) with (ACP + 3) in CPYr by lia.
          assert (SBN : q0 <> 239 \/ q1 <> 187 \/ q2 <> 191 -> strip_bom data = data).
          { intros H. rewrite EDATA, strip_bom_3.
            destruct (Z.eqb_spec q0 239), (Z.eqb_spec q1 187), (Z.eqb_spec q2 191); cbn [andb]; try reflexivity. exfalso; lia. }
          assert (SBY : q0 = 239 -> q1 = 187 -> q2 = 191 -> strip_bom data = r).
          { intros H0 H1 H2. rewrite EDATA, strip_bom_3. subst q0 q1 q2. reflexivity. }
          destruct XB as (XB0 & XB1 & XB2).
          do 5 zstep. zstep. zstep. lit_if.
          zstep. zstep. zstep.
          if_cases K4; zify_cond K4; rewrite ?unsigned_byte in K4 by lia.
          + (* [comment removed for export] *)
            zstep. zstep. zstep.
            if_cases K5; zify_cond K5; [| exfalso; rewrite ?unsigned_byte in K5 by lia; change 18446744073709551615 with (Z.ones 64) in K5; rewrite Z.land_ones in K5 by lia; lia].
            rewrite (SBN ltac:(left; lia)). replace (ACP + (len - zlength data)) with ACP by (unfold len; lia).
            apply evt_done. do 16 eexists. reflexivity.
          + zstep. zstep. zstep. zstep. lit_if.
            zstep. zstep. zstep.
            if_cases K6; zify_cond K6; rewrite ?unsigned_byte in K6 by lia.
            * (* [comment removed for export] *)
              zstep. zstep. zstep.
              if_cases K7; zify_cond K7; [| exfalso; rewrite ?unsigned_byte in K7 by lia; change 18446744073709551615 with (Z.ones 64) in K7; rewrite Z.land_ones in K7 by lia; lia].
              rewrite (SBN ltac:(right; left; lia)). replace (ACP + (len - zlength data)) with ACP by (unfold len; lia).
              apply evt_done. do 16 eexists. reflexivity.
            * zstep. zstep. zstep. zstep. lit_if.
              zstep. zstep. zstep.
              if_cases K8; zify_cond K8; rewrite ?unsigned_byte in K8 by lia.
              -- (* [comment removed for export] *)
                 zstep. zstep. zstep.
                 if_cases K9; zify_cond K9; [| exfalso; rewrite ?unsigned_byte in K9 by lia; change 18446744073709551615 with (Z.ones 64) in K9; rewrite Z.land_ones in K9 by lia; lia].
                 rewrite (SBN ltac:(right; right; lia)). replace (ACP + (len - zlength data)) with ACP by (unfold len; lia).
                 apply evt_done. do 16 eexists. reflexivity.
              -- (* [comment removed for export] *)
                 zstep. zstep. zstep. zstep. lit_if.
                 zstep. zstep. zstep. lit_if.
                 zstep. zstep.
                 rewrite (SBY ltac:(lia) ltac:(lia) ltac:(lia)). replace (ACP + (len - zlength r)) with (ACP + 3) by lia.
                 replace (zlength r) with (len + -3) by lia.
                 apply evt_done. do 16 eexists. reflexivity. }
      intros ms10 (ra' & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & ->).
      clear DAT9.
      (* [comment removed for export] *)
      unfold hidden in MU7, WM7, MU8, MU9.
      assert (DCA : ACP + (len + 64) <= AIM \/ AIM + 96 <= ACP)
        by (pose proof (new_block_disj _ _ _ _ _ _ (pim, AIM, 96) HP6 ltac:(do 3 right; left; reflexivity)) as Dd; cbn in Dd; lia).
      pose proof (rbr_img _ _ BRC) as BRC5. pose proof (rbr_img _ _ BRM) as BRM5.
      assert (TR9 : forall A cs, rw_cells psegs m6 A cs ->
                (A + Z.of_nat (cells_size cs) <= ACP \/ ACP + (len + 64) <= A) ->
                (A + Z.of_nat (cells_size cs) <= lo \/ bv_unsigned sp + -80 <= A) ->
                (A + Z.of_nat (cells_size cs) <= P + 64 \/ P + 80 <= A) -> rw_cells psegs m9 A cs).
      { intros A cs H HA HB HC. eapply rw_cells_transport; [| exact MU9| exact WM9| cbn; lia].
        eapply rw_cells_transport; [| exact MU8| exact WM8| cbn; lia].
        eapply rw_cells_transport; [exact H| exact MU7| exact WM7| cbn; lia]. }
      assert (DST9 : rw_cells psegs m9 (P + 8) [C8 (Z_to_bv 64 AIM)]) by (apply TR9; [exact DST4| cbn; lia| cbn; lia| cbn; lia]).
      assert (PMAX9 : rw_cells psegs m9 (P + 48) [C8 (Z_to_bv 64 4294967295); C1 (Z_to_bv 8 0)]) by (apply TR9; [exact PMAX| cbn; lia| cbn; lia| cbn; lia]).
      assert (OB09 : rw_cells psegs m9 AIM [C8 (w64 PVTAB_DOM)]) by (apply TR9; [exact OB0| cbn; lia| cbn; lia| cbn; lia]).
      lazymatch type of OB40 with rw_cells _ _ _ ?cs =>
        assert (OB409 : rw_cells psegs m9 (AIM + 40) cs) by (apply TR9; [exact OB40| cbn; lia| cbn; lia| cbn; lia]) end.
      lazymatch type of VTD with rw_cells _ _ _ ?cs =>
        assert (VTD9 : rw_cells psegs m9 469712 cs) by (apply TR9; [exact VTD| cbn; lia| cbn; lia| cbn; lia]) end.
      unfold w64, PVTAB_DOM in OB09.
      pose proof (munch_refl [(lo, bv_unsigned sp + -80); (AIM + 48, AIM + 49)] m9) as MU10. pose proof (wmono_refl psegs m9) as WM10.
      change (munch ?W m5 m9) with (hidden (munch W m5 m9)) in MU9.
      (* [comment removed for export] *)
      park_mem m9. unfold parked in FR, DST9, PMAX9, OB09, OB409, VTD9.
      do 9 zstep.
      unpark. trm MU10 WM10.
      apply evt_done.
      change (?X \/ ?Y) with (hidden (X \/ Y)) in DCA, BRC5, BRM5.
      unfold hidden in MU9.
      (* [comment removed for export] *)
      assert (MUall : munch [(lo, bv_unsigned sp + -80); (P + 64, P + 80); (ACP, ACP + (len + 64)); (AIM + 48, AIM + 49)] m6 m0).
      { eapply munch_trans; [eapply munch_weaken; [| exact MU7]; intros x Hx; cbn in Hx |- *; repeat split; try exact I; lia|].
        eapply munch_trans; [eapply munch_weaken; [| exact MU8]; intros x Hx; cbn in Hx |- *; repeat split; try exact I; lia|].
        eapply munch_trans; [eapply munch_weaken; [| exact MU9]; intros x Hx; cbn in Hx |- *; repeat split; try exact I; lia|].
        eapply munch_weaken; [| exact MU10]; intros x Hx; cbn in Hx |- *; repeat split; try exact I; lia. }
      assert (WMall : wmono psegs m6 m0) by (eapply wmono_trans; [exact WM7| eapply wmono_trans; [exact WM8| exact WM9]]).
      clear MU7 MU8 MU9 MU10 WM7 WM8 WM9 WM10 TR9.
      assert (HP10 : RHEAP s3' ((pcp, ACP, len + 64) :: (pia, AIA, 1024) :: (poc, AOC, 8 * 1024) :: (psi, ASI, SIDX_BYTES len) :: (pim, AIM, 96)
                                :: (ptp, ATP, TAPE_BYTES len) :: (psb, ASB, SB_BYTES len) :: LB) m0).
      { eapply RMalloc_ifaceP.RHEAP_frame_proof; [exact HP6| exact MUall| exact WMall|].
        apply Forall_cons; [left; cbn; lia|]. apply Forall_cons; [left; cbn; lia|].
        apply Forall_cons; [right; right; exists (pcp, ACP, len + 64); split; [left; reflexivity| cbn; lia]|].
        apply Forall_cons; [right; right; exists (pim, AIM, 96); split; [do 4 right; left; reflexivity| cbn; lia]| apply Forall_nil]. }
      assert (AUX10 : rauxv_ok m0 B)
        by (unfold hidden in DCA, BRC5, BRM5; eapply rauxv_ok_frame; [exact AUX6| exact MUall| exact WMall| repeat (apply Forall_cons; [cbn; unfold RAUXV_CELL in *; lia|]); apply Forall_nil]).
      (* [comment removed for export] *)
      pose proof (RMalloc_ifaceP.RHEAP_blocks_nodup_proof _ _ _ HP10) as ND10.
      change (map blk_id ((pcp, ACP, len + 64) :: (pia, AIA, 1024) :: (poc, AOC, 8 * 1024) :: (psi, ASI, SIDX_BYTES len) :: (pim, AIM, 96)
                          :: (ptp, ATP, TAPE_BYTES len) :: (psb, ASB, SB_BYTES len) :: LB))
        with ([pcp; pia; poc; psi; pim; ptp; psb] ++ map blk_id LB) in ND10.
      assert (NLB : forall b, In b LB -> ~ In (blk_id b) [pcp; pia; poc; psi; pim; ptp; psb]).
      { intros b Hb Hin. apply (nodup_app_disj _ _ _ (blk_id b) ND10 Hin). apply in_map. exact Hb. }
      pose proof (NoDup_app_remove_r _ _ ND10) as ND7.
      destruct (nodup7 _ _ _ _ _ _ _ ND7) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16 & E17 & E18 & E19 & E20 & E21).
      (* [comment removed for export] *)
      assert (RPW : rheap_pres_W ((pia, AIA, 1024) :: (poc, AOC, 8 * 1024) :: (psi, ASI, SIDX_BYTES len) :: (ptp, ATP, TAPE_BYTES len)
                                   :: (psb, ASB, SB_BYTES len) :: LB) (bv_unsigned sp + -80) [(P + 64, P + 80)] m6 m0).
      { eapply (rheap_pres_W_blk _ _ _ [pcp; pim] m6 m0 lo (bv_unsigned sp + -80) [(P + 64, P + 80)] [(ACP, ACP + (len + 64)); (AIM + 48, AIM + 49)] HP6).
        - intros b Hb. cbn [In] in Hb.
          destruct Hb as [Hb|[Hb|[Hb|[Hb|[Hb|Hb]]]]]; [subst b ..|].
          + split; [right; left; reflexivity|]. cbn [blk_id fst In]. intros [Hc|[Hc|[]]]; [exact (E1 Hc)| exact (E9 (eq_sym Hc))].
          + split; [do 2 right; left; reflexivity|]. cbn [blk_id fst In]. intros [Hc|[Hc|[]]]; [exact (E2 Hc)| exact (E13 (eq_sym Hc))].
          + split; [do 3 right; left; reflexivity|]. cbn [blk_id fst In]. intros [Hc|[Hc|[]]]; [exact (E3 Hc)| exact (E16 (eq_sym Hc))].
          + split; [do 5 right; left; reflexivity|]. cbn [blk_id fst In]. intros [Hc|[Hc|[]]]; [exact (E5 Hc)| exact (E19 Hc)].
          + split; [do 6 right; left; reflexivity|]. cbn [blk_id fst In]. intros [Hc|[Hc|[]]]; [exact (E6 Hc)| exact (E20 Hc)].
          + split; [do 7 right; exact Hb|]. intros Hc. apply (NLB b Hb). cbn [In] in Hc |- *.
            destruct Hc as [Hc|[Hc|[]]]; [left; exact Hc| do 4 right; left; exact Hc].
        - exact MUall.
        - exact WMall.
        - intros w [Hw|[Hw|[]]]; subst w.
          + exists (pcp, ACP, len + 64). split; [left; reflexivity|]. split; [left; reflexivity|]. cbn; lia.
          + exists (pim, AIM, 96). split; [do 4 right; left; reflexivity|]. split; [right; left; reflexivity|]. cbn; lia.
        - lia.
        - lia. }
      trW RPW.
      (* [comment removed for export] *)
      assert (TRA : forall A cs, rw_cells psegs m6 A cs -> AIM <= A -> (A + Z.of_nat (cells_size cs) <= AIM + 48 \/ AIM + 49 <= A) ->
                A + Z.of_nat (cells_size cs) <= AIM + 96 -> rw_cells psegs m0 A cs).
      { intros A cs H H1 H2 H3. unfold hidden in DCA, BRC5, BRM5. eapply rw_cells_transport; [exact H| exact MUall| exact WMall| cbn; lia]. }
      lazymatch type of OB8 with rw_cells _ _ _ ?cs => assert (OB8' : rw_cells psegs m0 (AIM + 8) cs) by (apply TRA; [exact OB8| lia| cbn; lia| cbn; lia]) end.
      lazymatch type of OB16 with rw_cells _ _ _ ?cs => assert (OB16' : rw_cells psegs m0 (AIM + 16) cs) by (apply TRA; [exact OB16| lia| cbn; lia| cbn; lia]) end.
      lazymatch type of OB24 with rw_cells _ _ _ ?cs => assert (OB24' : rw_cells psegs m0 (AIM + 24) cs) by (apply TRA; [exact OB24| lia| cbn; lia| cbn; lia]) end.
      lazymatch type of OB56 with rw_cells _ _ _ ?cs => assert (OB56' : rw_cells psegs m0 (AIM + 56) cs) by (apply TRA; [exact OB56| lia| cbn; lia| cbn; lia]) end.
      clear TRA OB8 OB16 OB24 OB56.
      assert (ERR10 : rw_cells psegs m0 556252 [C4 errv6]) by (unfold hidden in DCA, BRC5, BRM5; eapply rw_cells_transport; [exact ERR6| exact MUall| exact WMall| cbn; lia]).
      clear ERR6.
      assert (WO10 : wr_at psegs m0 AIM 96).
      { eapply wr_at_wmono; [| exact WMall]. eapply rheap_pres_wr_at; [exact HPR6| exact WO4|].
        right; right. exists (pim, AIM, 96). split; [do 3 right; left; reflexivity| cbn; lia]. }
      (* [comment removed for export] *)
      assert (BUF10 : bytes_at psegs m0 (ACP + (len - zlength (strip_bom data))) (s1buf (strip_bom data))).
      { apply buf_strip. eapply copy_s1buf; [exact CPY9| exact SET9| exact EBS| vm_compute; reflexivity]. }
      pose proof (zlength_strip_bom data) as ZSB. fold len in ZSB.
      pose proof (nodup7_perm _ _ _ _ _ _ _ ND7) as NDP.
      destruct (rw_cells_app_split psegs _ (P + 24) [C8 (Z_to_bv 64 ATP); C8 (Z_to_bv 64 ASB)] [_] DC2) as [DOC10 _].
      (* [comment removed for export] *)
      eapply implM_bind.
      { eapply PARSE with (lo := lo) (B := B) (data := data) (THIS := AIM) (ASI := ASI) (ACP := ACP) (ATP := ATP) (ASB := ASB) (AOC := AOC)
          (AIA := AIA) (DOC := P + 24) (BUF := ACP + (len - zlength (strip_bom data))) (nim := 96) (nsi := SIDX_BYTES len) (ncp := len + 64)
          (ntp := TAPE_BYTES len) (nsb := SB_BYTES len) (noc := 8 * 1024) (nia := 1024);
          rewrite ?unsigned_lit by lia;
          [ exact HP10 | exact NDP | do 4 right; left; reflexivity | lia | do 3 right; left; reflexivity | lia | left; reflexivity | lia | lia
          | do 5 right; left; reflexivity | do 6 right; left; reflexivity | do 2 right; left; reflexivity | lia | right; left; reflexivity | lia
          | exact SZ2 | lia | lia | lia | exact BUF10 | exact (Forall_strip_bom _ _ DB) | lia
          | exact OB8' | exact OB16' | exact OB24' | exact OB409 | exact OB56' | exact WO10
          | eapply wr_at_sub; [exact (wr_at_of_rw _ _ _ IDX4)| cbn; lia]
          | exact DOC10 | lia | lia | lia | exact BLKT | exact BLKS | exact OC4 | exact IA4 | exact FMIN | exact GOT
          | exact AUX10 | lia | exact ST9 | lia | unfold PARSE_STACK, PS2_STACK, OPNEW_NT_STACK, OPNEW_STACK, RMALLOC_STACK; lia | lia | lia
          | rewrite errno_lit; unfold RERRNO; exact ERR10 | exact MI9 | exact FZ | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity ]. }
      cbv beta. intros [] s4' ms11 PO.
      assert (ZLD : zlength (strip_bom data) <= len) by lia. clear ZSB DCA.
      destruct PO as (h0 & h1 & h2 & k0 & k1 & k2 & k3 & k4 & k5 & k6 & k7 & h3 & h4 & h5 & h6 & F' & fc' & m11 & errv11 & -> & FZ11 & MI11 & ST11
                      & ERR11 & AUX11 & RPW11 & FAE11 & SOE11 & HP11).
      rewrite ?unsigned_lit in ST11 by lia. rewrite ?unsigned_lit in RPW11 by lia. rewrite errno_lit in ERR11. unfold RERRNO in ERR11.
      assert (RSTK11 : stk psegs m11 R (P + 80)).
      { eapply rheap_pres_W_stk; [exact RPW11| exact RSTK9| lia|]. intros a Ha. unfold parse_win. cbn [outside]. repeat split; try exact I; lia. }
      clear RSTK9.
      ret_lit.
      apply implM_ret.
      (* [comment removed for export] *)
      destruct (rw_cells_app_split psegs _ (AIM + 56) [C8 (Z_to_bv 64 AOC); C8 (Z_to_bv 64 AIA)] [_; _; _] OB56') as [OB56'' _].
      clear OB56' OB8' OB24' OB409 IDX4 BLKT BLKS OC4 IA4 ERR10 CPY9 SET9 BUF10 MI9 ST9 AUX10 VTD9 PMAX9.
      (* [comment removed for export] *)
      assert (SP11 : stat_pres m0 m11).
      { intros a Ha. apply RPW11; [lia| right; left; unfold ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP; lia|].
        pose proof (rbr_img _ _ BRM) as X1. pose proof (rbr_img _ _ BRI) as X2. pose proof (rbr_img _ _ BRT) as X3.
        pose proof (rbr_img _ _ BRS) as X4. pose proof (rbr_img _ _ BRO) as X5. pose proof (rbr_img _ _ BRA) as X6.
        unfold parse_win. cbn [outside]. clear - Ha X1 X2 X3 X4 X5 X6 SZ1 ZLD. repeat split; try exact I; lia. }
      assert (SA1' : rw_cells psegs m11 553368 [C8 (Z_to_bv 64 553488)]) by (eapply stat_pres_cells; [exact SP11| exact SA1| cbn; lia]).
      assert (SA2' : rw_cells psegs m11 553376 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1)]) by (eapply stat_pres_cells; [exact SP11| exact SA2| cbn; lia]).
      lazymatch type of SA3 with rw_cells _ _ _ ?cs =>
        assert (SA3' : rw_cells psegs m11 553488 cs) by (eapply stat_pres_cells; [exact SP11| exact SA3| cbn; lia]) end.
      assert (SA4' : rw_cells psegs m11 553416 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1)]) by (eapply stat_pres_cells; [exact SP11| exact SA4| cbn; lia]).
      clear SA1 SA2 SA3 SA4 SP11. rename SA1' into SA1. rename SA2' into SA2. rename SA3' into SA3. rename SA4' into SA4.
      assert (TRM : forall k cs, rw_cells psegs m0 (AIM + k) cs -> 0 <= k -> k + Z.of_nat (cells_size cs) <= 96 ->
                     (k + Z.of_nat (cells_size cs) <= 8 \/ 12 <= k) -> (k + Z.of_nat (cells_size cs) <= 24 \/ 28 <= k) ->
                     k + Z.of_nat (cells_size cs) <= 72 -> rw_cells psegs m11 (AIM + k) cs).
      { intros k cs H H1 H2 H3 H4 H5. eapply rheap_pres_W_rw_cells; [exact RPW11| exact H| right; right; exists (pim, AIM, 96); split; [do 4 right; left; reflexivity| cbn; lia]|].
        (* [comment removed for export] *)
        assert (APM : forall X nX q, In (q, X, nX) ((pcp, ACP, len + 64) :: (pia, AIA, 1024) :: (poc, AOC, 8 * 1024) :: (psi, ASI, SIDX_BYTES len)
                                :: (pim, AIM, 96) :: (ptp, ATP, TAPE_BYTES len) :: (psb, ASB, SB_BYTES len) :: LB) -> q <> pim -> X + nX <= AIM \/ AIM + 96 <= X).
        { intros X nX q Hq Hn. pose proof (RMalloc_ifaceP.RHEAP_blocks_disjoint_proof _ _ _ (pim, AIM, 96) (q, X, nX) HP10 ltac:(do 4 right; left; reflexivity) Hq
                                                         ltac:(cbn; congruence)) as Dd. cbn in Dd. lia. }
        pose proof (APM _ _ _ ltac:(do 3 right; left; reflexivity) E16) as AP1.
        pose proof (APM _ _ _ ltac:(do 5 right; left; reflexivity) ltac:(intros Hc; exact (E19 (eq_sym Hc)))) as AP2.
        pose proof (APM _ _ _ ltac:(do 6 right; left; reflexivity) ltac:(intros Hc; exact (E20 (eq_sym Hc)))) as AP3.
        pose proof (APM _ _ _ ltac:(do 2 right; left; reflexivity) E13) as AP4.
        pose proof (APM _ _ _ ltac:(right; left; reflexivity) E9) as AP5.
        clear APM.
        unfold parse_win. cbn [disjoint_from]. clear - H1 H2 H3 H4 H5 AP1 AP2 AP3 AP4 AP5 SZ1 ZLD. repeat split; try exact I; lia. }
      replace AIM with (AIM + 0) in OB09 by lia.
      pose proof (TRM 0 _ OB09 ltac:(lia) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia)) as OB0f. rewrite Z.add_0_r in OB0f.
      pose proof (TRM 16 _ OB16' ltac:(lia) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia)) as OB16f.
      pose proof (TRM 56 _ OB56'' ltac:(lia) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia)) as OB56f.
      clear TRM OB09 OB16' OB56''.
      trW RPW11.
      (* [comment removed for export] *)
      assert (HP10' : RHEAP s3' ([(pcp, ACP, len + 64); (pia, AIA, 1024); (poc, AOC, 8 * 1024); (psi, ASI, SIDX_BYTES len); (pim, AIM, 96);
                                  (ptp, ATP, TAPE_BYTES len); (psb, ASB, SB_BYTES len)] ++ LB) m0) by exact HP10.
      assert (NA : forall b0, In b0 [(pcp, ACP, len + 64); (pia, AIA, 1024); (poc, AOC, 8 * 1024); (psi, ASI, SIDX_BYTES len); (pim, AIM, 96);
                                     (ptp, ATP, TAPE_BYTES len); (psb, ASB, SB_BYTES len)] ->
                   forall a, rclient_addr LB (bv_unsigned sp) a -> ~ (blk_addr b0 <= a < blk_addr b0 + blk_size b0))
        by (intros b0 Hb0 a Hc; exact (new_apart _ _ _ _ b0 _ a HP10' Hb0 Hc ltac:(lia))).
      pose proof (NA _ (or_introl eq_refl)) as NAC. pose proof (NA _ (or_intror (or_introl eq_refl))) as NAA.
      pose proof (NA _ (or_intror (or_intror (or_introl eq_refl)))) as NAO. pose proof (NA _ (or_intror (or_intror (or_intror (or_introl eq_refl))))) as NAS.
      pose proof (NA _ (or_intror (or_intror (or_intror (or_intror (or_introl eq_refl)))))) as NAM.
      pose proof (NA _ (or_intror (or_intror (or_intror (or_intror (or_intror (or_introl eq_refl))))))) as NAT.
      pose proof (NA _ (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_introl eq_refl)))))))) as NAB.
      cbn [blk_addr blk_size fst snd] in NAC, NAA, NAO, NAS, NAM, NAT, NAB. clear NA HP10'.
      pose proof (munch_refl [(lo, bv_unsigned sp); (R, R + 24)] m11) as MU12. pose proof (wmono_refl psegs m11) as WM12.
      clear BRC5 BRM5.
      park_mem m11. unfold parked in FR, PR.
      zstep.
      if_cases KR; clear KR; [do 5 zstep | do 4 zstep].
      all: do 12 zstep.
      all: unpark; trm MU12 WM12.
      all: release_frame FR ST11 (bv_unsigned sp).
      all: apply evt_done.
      all: unfold pid_post; do 15 eexists; exists F', fc'; eexists; exists errv11; split; [reflexivity|].
      all: split; [exact FZ11|]. all: split; [exact MI11|]. all: split; [exact ST11|]. all: split; [rewrite errno_lit; exact ERR11|].
      all: split; [eapply rauxv_ok_stack_frame; [exact AUX11| exact MU12| exact WM12| repeat constructor; cbn; lia]|].
      all: split; [| split; [congruence|]; split; [congruence|]].
      1,3: (eapply (pid_chain_B _ _ _ _ _ lo P R ACP (len + 64) AIM ASI (SIDX_BYTES len) ATP (TAPE_BYTES len) ASB (SB_BYTES len) AOC AIA
                      (zlength (strip_bom data)) m m4 m6 m0 m11 _ PW1 HPR6 ltac:(intros b Hb; do 6 right; exact Hb) MUall WMall RPW11
                      ltac:(intros b Hb; do 7 right; exact Hb) MU12 WM12); first [exact LBB | exact NAC | exact NAM | exact NAS | exact NAT | exact NAB
                      | exact NAO | exact NAA | lia]).
      all: split; [unfold cstat_built, PACTIVE, PACTIVE_GUARD, PFALLBACK, PFALLBACK_GUARD, guard1, fallback_cells, PFALLBACK_VT, PFALLBACK_NAME, PFALLBACK_DESC, w0;
                   split; [exact SA1|]; split; [exact SA2|]; split; [exact SA3| exact SA4]|].
      all: split; [exact RSTK11|].
      all: exists ASB, ATP, AIM, ASI, AOC, AIA, ACP.
      all: split; [eapply RHEAP_stack_frame; [exact HP11| exact MU12| exact WM12| repeat constructor; cbn; lia]|].
      all: split; [exact DST9|]. all: split; [exact DOC10|].
      all: split; [destruct (rw_cells_cons_split _ _ _ _ PCP9) as [X _]; exact X|].
      all: split; [exact OB0f|]. all: split; [exact OB16f| exact OB56f].
  Qed.
End Proof.
End CANSEC1.
