(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.bzip2.bzip2_compress_target.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec ShapeAlg.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require Import SegsS0. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import EvtBridge.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Heap Require Import AllocIface. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Heap Require Import AllocLayout0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import U.S0TRInv.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require GlueAlloc. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require GlueCarve BzDefs. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzModel. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzTac BzTac2 BzInv. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzTables. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzContracts BzContracts0 DecCut S0_dec_U13 S0_decCuts. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require GlueTac. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require S0_glueDefs S0_glue10K S0_glue10A S0_glue10R.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require S0_glue10A.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require S0_glue10A.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.GlueAlloc OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.GlueCarve OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzDefs OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzModel OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzTac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzTac2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzInv OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTables OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzContracts OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzContracts0 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecCut OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_dec_U13 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_decCuts OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.GlueTac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_glueDefs OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_glue10K OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_glue10A OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_glue10R OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_glue10A.S0_glue10C OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_glue10A.S0_glue10D.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Heap Require Import AllocCover AllocDcv.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCStream BzDState.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDK BzDU2 BzDOKp.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDU5.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDU10M. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require DecCutF DecTacF DecTacFR S0F_decRet S0F_decCutsA S0F_decMain S0F_dec_U0F S0F_glueDefs S0F_glue10M DecCutF10.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDK OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOKp OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU5.BzDRv OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU10M OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecCutF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecTacF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecTacFR OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_decRet OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_decCutsA OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_decMain OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_dec_U0F OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_glueDefs OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_glue10M OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecCutF10.
From Stdlib Require Lia. Unset Lia Cache.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeilTac.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil RunW.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeilLia.
(* [comment removed for export] *)
Local Ltac zify_split_ranges ::= idtac.
Import ListNotations.
Open Scope Z_scope.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import LinSplit NatLit.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzImg0TacFR.
Local Ltac Zify.zify_pre_hook ::= NatLit.natlen_ctx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require RelLiaG.
Local Ltac lia ::= RelLiaG.lia_rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
(* [comment removed for export] *)
Section ACeilS1. Context {ACEIL__ : ACeil} {RUNW__ : RunW}.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma disjoint_from_Forall : forall (P : Z * Z -> Prop) W A n,
  Forall P W -> (forall l h, P (l, h) -> A + n <= l \/ h <= A) -> disjoint_from W A n.
Proof.
  intros P W A n F HP. induction F as [| [l h] W Hx F IH]; cbn; [exact I|].
  split; [exact (HP l h Hx) | exact IH].
Qed.

Lemma heap_pres_u32arr : forall L LB SP m m' A ws,
  heap_pres s0segs L LB SP m m' -> u32arr s0segs m A ws -> client_range L LB SP A (4 * Z.of_nat (length ws)) -> u32arr s0segs m' A ws.
Proof.
  intros L LB SP m m' A ws HP [B W] CRg. split.
  - eapply heap_pres_bytes_at; [exact HP | exact B |]. rewrite u32s_length, Nat2Z.inj_mul. exact CRg.
  - eapply heap_pres_wr_at; [exact HP | exact W | exact CRg].
Qed.

Lemma client_range_weaken : forall L LB LB' SP SP' A n,
  client_range L LB SP A n -> (forall b, In b LB -> In b LB') -> SP' <= SP -> client_range L LB' SP' A n.
Proof.
  intros L LB LB' SP SP' A n [C|[C|(b & Hb & C)]] SUB LE; [left; lia | right; left; exact C | right; right].
  exists b. split; [apply SUB; exact Hb | exact C].
Qed.

(* [comment removed for export] *)
Lemma save_zero_cells : forall m S,
  rw_cells s0segs m (S + 64036) [CB 108 (repeat (Z_to_bv 8 0) 108)] ->
  rw_cells s0segs m (S + 64036) (SAVE_CELLS (repeat (Z_to_bv 8 0) 44) 0 (repeat (Z_to_bv 8 0) 60)).
Proof.
  intros m S H.
  apply (rw_cells_split_CB s0segs m (S + 64036) [] 108%nat _ [] [44; 4; 60]%nat) in H; [| reflexivity].
  cbn [mk_CB_cells app firstn skipn repeat] in H.
  eapply (rw_cells_recell s0segs m (S + 64036) _ 44%nat (CB 4 (repeat (Z_to_bv 8 0) 4)) (C4 (Z_to_bv 64 0))) in H; [| reflexivity | reflexivity | reflexivity | exact I].
  exact H.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition NB (S src len dst dn A sz : Z) : Prop :=
  0 < A /\ A mod 16 = 0 /\ 0 <= sz /\ A + sz <= CEILING /\ (A + sz <= 65536 \/ 417792 <= A) /\   (* [comment removed for export] *)
  disj S DSTATE_SIZE A sz /\ disj src len A sz /\ disj dst dn A sz.

Lemma NB_mono : forall S src len dst dn A sz sz', NB S src len dst dn A sz -> 0 <= sz' <= sz -> NB S src len dst dn A sz'.
Proof.
  (intros S src len dst dn A sz sz'; cps_intros (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8); intros H).
  unfold NB, img_apart, disj, IHI in *. repeat split; try lia.
Qed.

Lemma ctx_ok_ext : forall S uspb src len dst dn small n tt l16 l4,
  ctx_ok (cx10 S uspb src len dst dn small) -> 0 <= n <= 9 ->
  (tt = 0 \/ NB S src len dst dn tt (400000 * n)) ->
  (l16 = 0 \/ NB S src len dst dn l16 (200000 * n)) ->
  (l4 = 0 \/ NB S src len dst dn l4 (50000 * n)) ->
  (l16 <> 0 -> l4 <> 0 -> disj l16 (200000 * n) l4 (50000 * n)) ->
  ctx_ok (cxN S uspb src len dst dn small n tt l16 l4).
Proof.
  (intros S uspb src len dst dn small n tt l16 l4; cps_intros (LIN & AL & SEP); intros N TT L16 L4 D64).
  unfold cx10, cxN, ctx_ok, ctx_lin, ctx_al, ctx_sep, NB in *. cbv zeta in *.
  cbn [b_s b_strm b_src b_len b_dst b_dlen b_pdl b_sp b_small b_n b_tt b_ll16 b_ll4] in *.
  cps_destruct LIN as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & Y10 & Y11 & Y12 & Y13 & Y14 & Y15 & Y16 & Y17 & Y18 & Y19).
  cps_destruct AL as (A1 & A2 & A3 & A4 & A5 & A6 & A7).
  cps_destruct SEP as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12).
  destruct TT as [-> | (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8)];
  destruct L16 as [-> | (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8)];
  destruct L4 as [-> | (O1 & O2 & O3 & O4 & O5 & O6 & O7 & O8)].
  all: split; [| split]; repeat match goal with |- _ /\ _ => split end;
       first [ assumption | reflexivity | lia | left; reflexivity | right; split; assumption
             | intros _; repeat match goal with |- _ /\ _ => split end; first [assumption | unfold img_apart, IHI; lia]
             | let X := fresh in intros X; exfalso; apply X; reflexivity
             | intros; apply D64; assumption
             | unfold img_apart, IHI; lia
             | idtac ].
Qed.

(* [comment removed for export] *)
Lemma skipn_nth_cons : forall {A} (l : list A) k x, nth_error l k = Some x -> skipn k l = x :: skipn (S k) l.
Proof.
  intros A l k. revert l. induction k as [|k IH]; intros [|y l] x H; cbn in H |- *; try discriminate.
  - injection H as E. rewrite E. reflexivity.
  - exact (IH l x H).
Qed.
Lemma pz_step : forall (p : list byte) (pre : list Z) (k : nat) (b : byte),
  map bv_unsigned p = pre ++ skipn k (map bv_unsigned p) -> length pre = k -> nth_error p k = Some b ->
  map bv_unsigned p = (pre ++ [bv_unsigned b]) ++ skipn (S k) (map bv_unsigned p).
Proof.
  intros p pre k b E L N. rewrite <- app_assoc. cbn [app].
  rewrite <- (skipn_nth_cons (map bv_unsigned p) k (bv_unsigned b)); [exact E|].
  rewrite nth_error_map, N. reflexivity.
Qed.
Lemma pz_end : forall (p : list byte) (pre : list Z) (k : nat),
  map bv_unsigned p = pre ++ skipn k (map bv_unsigned p) -> length pre = k -> length p = k -> map bv_unsigned p = pre.
Proof.
  intros p pre k E L N. rewrite E. rewrite skipn_all2; [apply app_nil_r|]. rewrite length_map. lia.
Qed.
Lemma byte_range : forall b : byte, 0 <= bv_unsigned b < 256.
Proof. intros b. pose proof (bv_unsigned_in_range 8 b) as H. unfold bv_modulus in H. cbn in H. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section G10.
  Context (AI : AllocIface s0segs S0_layout) (AC : AllocCover s0segs S0_layout AI).
  Let L := S0_layout.
  Hypothesis DCV : alloc_dcv_law s0segs S0_layout AI AC.

  (* [comment removed for export] *)
  Variables (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 gp tp sv g1 errv x9 x24 : word) (F : bvmap 5 word) (fc : bv 32)
            (m : word -> option byte) (MD : Model) (s : ai_AS AI) (LB : list ablock) (pS pD : bid) (kcr : nat)
            (S uspb src len dst dn small lo B : Z)
            (h0 : dsh) (nbu0 : Z) (cf0 : list word) (d0 : dsm) (r0 : drest) (js : list byte) (b0 : bzs) (payload : list byte)
            (K : TSet).
  Hypothesis CTX : ctx_ok (cx10 S uspb src len dst dn small).
  Hypothesis TP : tp = Z_to_bv 64 (al_tp L).
  Hypothesis HD : rw_cells s0segs m S (HEAD_CELLS h0).
  Hypothesis HWF : hwf10 h0 uspb small.
  Hypothesis NBU : rw_cells s0segs m (S + 1092) [C4 (Z_to_bv 64 nbu0)].
  Hypothesis Rnbu : 0 <= nbu0 < 2 ^ 32.
  Hypothesis CF : u32arr s0segs m (S + 1096) cf0.
  Hypothesis Lcf : length cf0 = 257%nat.
  Hypothesis MID : rw_cells s0segs m (S + 3152) (MID_CELLS d0).
  Hypothesis T0 : sm_tt d0 = 0.
  Hypothesis L160 : sm_ll16 d0 = 0.
  Hypothesis L40 : sm_ll4 d0 = 0.
  Hypothesis RnI : 0 <= sm_nInUse d0 < 2 ^ 32.
  Hypothesis DR : drest_at s0segs m S r0.
  Hypothesis SAV : rw_cells s0segs m (S + 64036) [CB 108 js].
  Hypothesis STRM : rw_cells s0segs m uspb (STRM_CELLS b0).
  Hypothesis BWF : bzs_wf b0.
  Hypothesis HbS : bs_S b0 = S.
  Hypothesis Hsrc : bs_src b0 = src.
  Hypothesis Hlen : bs_len b0 = len.
  Hypothesis Hdst : bs_dst b0 = dst.
  Hypothesis Hdlen : bs_dlen b0 = dn.
  Hypothesis BZA : bs_bzalloc b0 = Z_to_bv 64 0x13e24.
  Hypothesis BOP : bs_opaque b0 = Z_to_bv 64 0.
  Hypothesis Hai0 : bs_ai b0 = bs_len b0.
  Hypothesis Htil0 : bs_til b0 = Z_to_bv 64 0.
  Hypothesis PAY : bytes_at s0segs m src payload.
  Hypothesis PAYL : Z.of_nat (length payload) = len.
  Hypothesis CR : client_range L LB (uspb + 128) src len.
  Hypothesis GOT : rw_cells s0segs m 0x320e8 [C8 (Z_to_bv 64 0x32098); C8 g1; C8 (Z_to_bv 64 0x320a0); C8 (Z_to_bv 64 0x33178); C8 (Z_to_bv 64 0x335b0)].
  Hypothesis SEV : rw_cells s0segs m 0x32098 [C8 sv].
  Hypothesis RN : u32arr s0segs m 0x335b0 rnums_words.
  Hypothesis ST : stk s0segs m lo (uspb + -112).
  Hypothesis LOC : alloc_ceiling <= lo.
  Hypothesis LO : lo <= uspb - 8640.
  Hypothesis MI : mem_inv s0segs m.
  Hypothesis INV : ai_inv AI s LB m MD.
  Hypothesis INS : In (pS, S, 64144) LB.
  Hypothesis IND : In (pD, dst, dn) LB.
  Hypothesis AUX : ai_aux AI m B.
  Hypothesis HB : uspb + 128 <= B.
  Hypothesis ERR : rw_cells s0segs m (errno_cell L) [C4 errv].
  Hypothesis CC0 : sm_cccrc d0 = Z_to_bv 64 0.
  Hypothesis AV0 : bs_av b0 = bs_dlen b0.
  Hypothesis VMC : ac_vm AC (2 + kcr)%nat s MD.
  Hypothesis HK : forall (m' : word -> option byte) (MD' : Model) (s' : ai_AS AI) (c : bcfg) (n : Z) (rc : Z) (errv' : word)
              (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
          let cx' := cxN S uspb src len dst dn small n (cfg_tt c) (cfg_l16 c) (cfg_l4 c) in
          ai_inv AI s' (cfg_extra c ++ LB) m' MD' -> vm_only MD MD' -> ac_vm AC kcr s' MD' -> ai_aux AI m' B ->
          rw_cells s0segs m' (errno_cell L) [C4 errv'] -> mem_inv s0segs m' -> stk s0segs m' lo (uspb + -112) ->
          ctx_ok cx' -> cfg_sizes_ok c n -> cfg_shape_ok c small n -> 0 <= n <= 9 ->
          rw_cells s0segs m' 0x320e8 [C8 (Z_to_bv 64 0x32098); C8 g1; C8 (Z_to_bv 64 0x320a0); C8 (Z_to_bv 64 0x33178); C8 (Z_to_bv 64 0x335b0)] ->
          rw_cells s0segs m' 0x32098 [C8 sv] -> u32arr s0segs m' 0x335b0 rnums_words ->
          pres10 LB S uspb m m' ->
          ( (exists (junkD : BzDState.dst) (J' : jk),
               let '(rv, d1, s1) := decompress (dst_init junkD 0 small) (dstrm_init (map bv_unsigned payload) dn) in
               rc = rv /\
               dmem DI_S0 cx' g1 sv payload m' (dvF cx' J' d1 s1) /\
               dpureF cx' b0 payload J' d1 s1 /\
               dpost14W (rv, d1, s1))
            \/
            ((rc = BZ_MEM_ERROR \/
              exists junkD : BzDState.dst,
                let '(rv, d1, s1) := decompress (dst_init junkD 0 small) (dstrm_init (map bv_unsigned payload) dn) in
                rc = rv /\ (rv = BZ_OK \/ rv = BZ_DATA_ERROR_MAGIC) /\ 10 <= d_state d1 <= 13 /\
                s_out s1 = [] /\ s_avail_out s1 = dn) /\
             exists (h : dsh) (d : dsm) (ai : Z) (til tih : word),
               rw_cells s0segs m' S (HEAD_CELLS h) /\ sh_strm h = uspb /\ 0 <= sh_state h < 2 ^ 31 /\ sh_state h <> BZ_X_OUTPUT /\
               rw_cells s0segs m' (S + 3152) (MID_CELLS d) /\ sm_tt d = cfg_tt c /\ sm_ll16 d = cfg_l16 c /\ sm_ll4 d = cfg_l4 c /\
               rw_cells s0segs m' uspb (STRM_CELLS (bupd b0 ai til tih)) /\ 0 <= ai <= bs_ai b0) ) ->
          realizes s0segs
            (mkCfg (MS (mkR (Z_to_bv 64 0x1481c) (Z_to_bv 64 (uspb + -112)) gp tp t0' t1' t2' (Z_to_bv 64 S) x9
                            (Z_to_bv 64 rc) a1' a2' a3' a4' a5' a6' a7'
                            (Z_to_bv 64 (S + 1096)) (Z_to_bv 64 (-2)) (Z_to_bv 64 (S + 2047)) (Z_to_bv 64 1) (Z_to_bv 64 2) (Z_to_bv 64 (-1))
                            x24 (Z_to_bv 64 100000) (Z_to_bv 64 (S + 64080)) (Z_to_bv 64 10) t3' t4' t5' t6')
                       F (Z_to_bv 64 0x1481c) fc None m' (seg_rom s0segs)) MD') K.

  Local Notation usp := (uspb + -112).
  (* [comment removed for export] *)
  Definition PK (MDx : Model) : machine_state -> Prop := fun ms => realizes s0segs (mkCfg ms MDx) K.

  (* [comment removed for export] *)
  Definition zone (iv : Z * Z) : Prop :=
    (usp - 336 <= fst iv /\ snd iv <= usp) \/ (S <= fst iv /\ snd iv <= S + 68) \/ (S + 3152 <= fst iv /\ snd iv <= S + 3196) \/
    (S + 64036 <= fst iv /\ snd iv <= S + 64144) \/ (uspb <= fst iv /\ snd iv <= uspb + 20).

  (* [comment removed for export] *)
  Definition P10 (a : Z) : Prop :=
    (uspb - 112 <= a \/ (0x32000 <= a < 0x66000 /\ ~ S0_private a /\ ~ (0x4413c <= a < 0x44140)) \/ in_block LB a) /\
    ~ (S <= a < S + 64144) /\ ~ (uspb <= a < uspb + 20).

  Lemma pres10_of_pres : forall m', pres P10 m m' -> pres10 LB S uspb m m'.
  Proof. intros m' H a Ha X1 X2 X3. exact (H a Ha (conj X1 (conj X2 X3))). Qed.

  (* [comment removed for export] *)
  Definition REST (mx : word -> option byte) : Prop :=
    rw_cells s0segs mx (S + 1092) [C4 (Z_to_bv 64 nbu0)] /\ u32arr s0segs mx (S + 1096) cf0 /\ drest_at s0segs mx S r0 /\
    bytes_at s0segs mx src payload /\
    rw_cells s0segs mx 0x320e8 [C8 (Z_to_bv 64 0x32098); C8 g1; C8 (Z_to_bv 64 0x320a0); C8 (Z_to_bv 64 0x33178); C8 (Z_to_bv 64 0x335b0)] /\
    rw_cells s0segs mx 0x32098 [C8 sv] /\ u32arr s0segs mx 0x335b0 rnums_words.

  (* [comment removed for export] *)
  Lemma LINf :
    0 < S /\ S + 64144 <= alloc_ceiling /\ 0 < src /\ 0 <= len < 134217728 /\ src + len <= alloc_ceiling /\
    0 < dst /\ 0 <= dn /\ dn < 134217728 /\ dst + dn <= alloc_ceiling /\ alloc_ceiling <= uspb /\ uspb + 176 <= 140737488355328 /\
    alloc_ceiling <= lo /\ lo <= uspb - 8640 /\ uspb + 128 <= B /\
    sh_strm h0 = uspb /\ sh_state h0 = 10 /\ sh_bsBuff h0 = 0 /\ sh_bsLive h0 = 0 /\ bv_unsigned (sh_small h0) = small /\ sh_cbn h0 = 0 /\ sh_verb h0 = 0 /\
    length (sh_p1 h0) = 3%nat /\ length (sh_p2 h0) = 3%nat /\ length (sh_p3 h0) = 3%nat /\
    0 <= sh_solen h0 < 2 ^ 32 /\ 0 <= sh_rNToGo h0 < 2 ^ 32 /\ 0 <= sh_rTPos h0 < 2 ^ 32 /\ 0 <= sh_n h0 < 2 ^ 32 /\ 0 <= sh_origPtr h0 < 2 ^ 32 /\
    length (bs_q1 b0) = 4%nat /\ length (bs_q2 b0) = 4%nat /\ 0 <= bs_ai b0 <= len /\ 0 <= bs_av b0 <= dn /\ Z.of_nat (length payload) = len.
  Proof.
    pose proof CTX as X. unfold ctx_ok in X. cps_destruct X as (LIN & AL & SEP). unfold cx10, cxN, ctx_lin, ctx_sep in LIN, SEP. cbv zeta in LIN. cbv zeta in SEP.
    cbn [b_s b_strm b_src b_len b_dst b_dlen b_pdl b_sp b_small b_n b_tt b_ll16 b_ll4] in LIN, SEP.
    bz_ceil; unfold DSTATE_SIZE, CEILING, STACK_TOP, disj, img_apart, IHI in LIN, SEP.
    pose proof HWF as W. unfold hwf10 in W. pose proof BWF as BW. unfold bzs_wf in BW. rewrite Hlen, Hdlen in BW.
    bz_ceil.
    decompose [and] LIN. decompose [and] SEP. decompose [and] W. decompose [and] BW.
    repeat match goal with |- _ /\ _ => split end; first [assumption | lia].
  Qed.
  Lemma ALS : S mod 8 = 0 /\ uspb mod 8 = 0.
  Proof.
    pose proof CTX as X. unfold ctx_ok in X. cps_destruct X as (_ & AL & _). unfold cx10, cxN, ctx_al in AL. cbv zeta in AL.
    cbn [b_s b_strm b_src b_len b_dst b_dlen b_pdl b_sp b_small b_n b_tt b_ll16 b_ll4] in AL.
    destruct AL as (A1 & A2 & _). split; Z.div_mod_to_equations; lia.
  Qed.
  (* [comment removed for export] *)
  Lemma SM01 : small = 0 \/ small = 1.
  Proof.
    pose proof CTX as X. unfold ctx_ok in X. cps_destruct X as (X & _ & _). unfold cx10, cxN, ctx_lin in X. cbv zeta in X. cbn [b_small] in X.
    cps_destruct X as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & X & _). exact X.
  Qed.
  Lemma SEPS : S + 64144 <= src \/ src + len <= S.
  Proof.
    pose proof CTX as X. unfold ctx_ok in X. cps_destruct X as (_ & _ & X). unfold cx10, cxN, ctx_sep in X. cbv zeta in X. cbn [b_s b_src b_len] in X.
    destruct X as (X & _). unfold disj, DSTATE_SIZE in X. exact X.
  Qed.
  (* [comment removed for export] *)
  Lemma IMGS : S + 64144 <= 65536 \/ 417792 <= S.
  Proof.
    cps_pose (ai_inv_blocks AI INV INS) as (_ & _ & _ & _ & X). cbn [blk_addr blk_size fst snd] in X.
    unfold L, S0_layout in X; cbn [al_img_lo al_img_hi] in X. exact X.
  Qed.

  Lemma zone_dj : forall W A n, Forall zone W ->
    (A + n <= usp - 336 \/ usp <= A) -> (A + n <= S \/ S + 68 <= A) -> (A + n <= S + 3152 \/ S + 3196 <= A) ->
    (A + n <= S + 64036 \/ S + 64144 <= A) -> (A + n <= uspb \/ uspb + 20 <= A) -> 0 <= n -> disjoint_from W A n.
  Proof.
    intros W A n FW D1 D2 D3 D4 D5 Hn. eapply disjoint_from_Forall; [exact FW|]. intros l h Z. unfold zone in Z. cbn in Z. lia.
  Qed.

  Lemma REST0 : REST m.
  Proof. unfold REST. split; [exact NBU|]. split; [exact CF|]. split; [exact DR|]. split; [exact PAY|]. split; [exact GOT|]. split; [exact SEV| exact RN]. Qed.

  Lemma REST_munch : forall W mx my, Forall zone W -> munch W mx my -> wmono s0segs mx my -> REST mx -> REST my.
  Proof.
    (intros W mx my FW MU WM; cps_intros (R1 & R2 & R3 & R4 & R5 & R6 & R7)). pose proof LINf as LIN. lin_split LIN. pose proof rnums_words_length as RNL.
    pose proof SEPS as SP. pose proof IMGS as IG.
    unfold REST.
    split; [eapply rw_cells_transport; [exact R1 | exact MU | exact WM | apply (zone_dj _ _ _ FW); cbn; lia]|].
    split; [eapply u32arr_transport; [exact R2 | exact MU | exact WM | apply (zone_dj _ _ _ FW); rewrite ?Lcf; cbn; lia]|].
    split; [eapply drest_transport; [exact R3 | exact MU | exact WM | apply (zone_dj _ _ _ FW); lia | apply (zone_dj _ _ _ FW); lia | apply (zone_dj _ _ _ FW); lia]|].
    split; [eapply bytes_at_transport; [exact R4 | exact MU | apply (zone_dj _ _ _ FW); lia]|].
    split; [eapply rw_cells_transport; [exact R5 | exact MU | exact WM | apply (zone_dj _ _ _ FW); cbn; lia]|].
    split; [eapply rw_cells_transport; [exact R6 | exact MU | exact WM | apply (zone_dj _ _ _ FW); cbn; lia]|].
    eapply u32arr_transport; [exact R7 | exact MU | exact WM | apply (zone_dj _ _ _ FW); rewrite ?RNL; cbn; lia].
  Qed.

  Lemma crange_imgx : forall LBx SP A n, 0x32000 <= A -> A + n <= 0x440f0 -> client_range L LBx SP A n.
  Proof.
    intros LBx SP A n H1 H2. right; left. unfold L, S0_layout, errno_cell; cbn [al_rw_lo al_img_hi al_private al_tp].
    split; [lia|]. split; [lia|]. split; [| lia]. intros a Ha. unfold S0_private. lia.
  Qed.

  Lemma REST_heap : forall LBx SP mx my, heap_pres s0segs L LBx SP mx my -> In (pS, S, 64144) LBx -> (forall b, In b LB -> In b LBx) ->
    SP <= uspb + 128 -> REST mx -> REST my.
  Proof.
    (intros LBx SP mx my HP IS SUB HSP; cps_intros (R1 & R2 & R3 & R4 & R5 & R6 & R7)). pose proof LINf as LIN. lin_split LIN. pose proof rnums_words_length as RNL.
    assert (BS : forall A n, S <= A -> A + n <= S + 64144 -> client_range L LBx SP A n).
    { intros A n HA Hn. right; right. exists (pS, S, 64144). split; [exact IS| cbn; lia]. }
    unfold REST.
    split; [eapply heap_pres_rw_cells; [exact HP | exact R1 | apply BS; cbn; lia]|].
    split; [eapply heap_pres_u32arr; [exact HP | exact R2 | apply BS; rewrite ?Lcf; cbn; lia]|].
    split.
    { unfold drest_at. cps_destruct R3 as ((A1&E1)&(A2&E2)&(A3&E3)&(A4&E4)&(A5&E5)&(A6&E6)&(A7&E7)&(A8&E8)&(A9&E9)&(A10&E10)&(A11&E11)&(A12&E12)&(A13&E13)&(A14&E14)).
      repeat match goal with |- _ /\ _ => split end; try assumption;
        first [ eapply heap_pres_u32arr; [exact HP | eassumption | apply BS; lia]
              | eapply heap_pres_u8arr; [exact HP | eassumption | apply BS; lia]
              ]. }
    split; [eapply heap_pres_bytes_at; [exact HP | exact R4 | rewrite PAYL; eapply client_range_weaken; [exact CR | exact SUB | lia]]|].
    split; [eapply heap_pres_rw_cells; [exact HP | exact R5 | apply crange_imgx; cbn; lia]|].
    split; [eapply heap_pres_rw_cells; [exact HP | exact R6 | apply crange_imgx; cbn; lia]|].
    eapply heap_pres_u32arr; [exact HP | exact R7 | apply crange_imgx; rewrite ?RNL; cbn; lia].
  Qed.

  Lemma pres_zone : forall W mx my, Forall zone W -> munch W mx my -> wmono s0segs mx my -> pres P10 mx my.
  Proof.
    intros W mx my FW MU WM. pose proof LINf as LIN. lin_split LIN. eapply pres_mono; [| apply pres_of_munch; [exact MU | exact WM]].
    (intros a Ha; cps_intros (P1 & P2 & P3)). cbn.
    assert (BL : in_block LB a -> a < alloc_ceiling).
    { cps_intros (b & Hb & Hr). cps_pose (ai_inv_blocks AI INV Hb) as (_ & _ & _ & X & _). bz_ceil. lia. }
    lin_unbox LIN. clear - FW P1 P2 P3 BL LIN Ha. induction FW as [| [l h] W Zx FW IH]; cbn; [exact I|]. split; [| exact IH].
    unfold zone in Zx. cbn in Zx. destruct P1 as [P1|[P1|P1]]; [lia | lia | specialize (BL P1); lia].
  Qed.

  Lemma pres_heapx : forall LBx SP mx my, heap_pres s0segs L LBx SP mx my -> SP <= usp -> (forall b, In b LB -> In b LBx) -> pres P10 mx my.
  Proof.
    (intros LBx SP mx my HP HSP SUB a Ha; cps_intros (P1 & P2 & P3)). apply HP; [exact Ha|].
    destruct P1 as [P1|[P1|(b & Hb & Hr)]]; [left; lia | right; left | right; right; exists b; split; [apply SUB; exact Hb| exact Hr]].
    unfold L, S0_layout, errno_cell; cbn [al_rw_lo al_img_hi al_private al_tp]. exact P1.
  Qed.

  Lemma cwo_blockx : forall LBx b l h, In b LBx -> blk_addr b <= l -> h <= blk_addr b + blk_size b -> client_write_ok L LBx (l, h).
  Proof. intros. right; right. exists b. cbn. auto. Qed.

  Lemma inv_zone : forall W mx my sx LBx MDx, Forall zone W -> munch W mx my -> wmono s0segs mx my ->
    In (pS, S, 64144) LBx -> ai_inv AI sx LBx mx MDx -> ai_inv AI sx LBx my MDx.
  Proof.
    intros W mx my sx LBx MDx FW MU WM IS IV. pose proof LINf as LIN. lin_split LIN. eapply (ai_inv_frame AI); [exact IV | exact MU | exact WM |].
    apply Forall_forall. intros [l h] Hin. apply (proj1 (Forall_forall _ _) FW) in Hin. unfold zone in Hin. cbn in Hin.
    bz_ceil.
    destruct Hin as [Z|[Z|[Z|[Z|Z]]]];
      first [ left; cbn; bz_ceil; lia | apply (cwo_blockx _ (pS, S, 64144)); [exact IS| cbn; lia| cbn; lia] ].
  Qed.

  Lemma aux_zone : forall W mx my, Forall zone W -> munch W mx my -> wmono s0segs mx my -> ai_aux AI mx B -> ai_aux AI my B.
  Proof.
    intros W mx my FW MU WM AX. pose proof LINf as LIN. lin_split LIN. pose proof IMGS as IG. eapply (ai_aux_frame AI); [exact AX | exact MU | exact WM |].
    apply Forall_forall. intros [l h] Hin. apply (proj1 (Forall_forall _ _) FW) in Hin. unfold zone in Hin. cbn in Hin.
    cbn [fst snd al_static L S0_layout]. unfold S0_static. split; [lia|]. intros a Ha. lia.
  Qed.

  Lemma err_zone : forall W mx my ev, Forall zone W -> munch W mx my -> wmono s0segs mx my ->
    rw_cells s0segs mx (errno_cell L) [C4 ev] -> rw_cells s0segs my (errno_cell L) [C4 ev].
  Proof.
    intros W mx my ev FW MU WM E. pose proof LINf as LIN. lin_split LIN. pose proof IMGS as IG.
    eapply rw_cells_transport; [exact E | exact MU | exact WM |]. unfold errno_cell, L, S0_layout; cbn [al_tp].
    apply (zone_dj _ _ _ FW); cbn; lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition EARLY (r : Z) : Prop :=
    r = BZ_MEM_ERROR \/
    exists junkD : BzDState.dst,
      let '(rv, d1, s1) := decompress (dst_init junkD 0 small) (dstrm_init (map bv_unsigned payload) dn) in
      r = rv /\ (rv = BZ_OK \/ rv = BZ_DATA_ERROR_MAGIC) /\ 10 <= d_state d1 <= 13 /\ s_out s1 = [] /\ s_avail_out s1 = dn.

  Lemma EARLY_model : forall r junkD,
    early10 r dn (decompress (dst_init junkD 0 small) (s10 (map bv_unsigned payload) dn)) -> EARLY r.
  Proof. intros r junkD E. right. exists junkD. unfold early10, s10 in E. exact E. Qed.

  Lemma rk_finish : forall (MDx : Model) (sx : ai_AS AI) (c : bcfg) (mR : word -> option byte) (r : Z) (h : dsh) (b : bzs) (d : dsm) (ev : word)
      (x5 x6 x7 x15 x16 x17 x28 x29 x30 x31 f160 : word),
    ai_inv AI sx (cfg_extra c ++ LB) mR MDx -> vm_only MD MDx -> ac_vm AC kcr sx MDx -> ai_aux AI mR B -> rw_cells s0segs mR (errno_cell L) [C4 ev] ->
    REST mR ->
    rw_cells s0segs mR S (HEAD_CELLS h) -> sh_strm h = uspb -> 10 <= sh_state h <= 13 ->
    rw_cells s0segs mR (S + 3152) (MID_CELLS d) -> sm_tt d = cfg_tt c -> sm_ll16 d = cfg_l16 c -> sm_ll4 d = cfg_l4 c ->
    rw_cells s0segs mR uspb (STRM_CELLS b) -> b = bupd b0 (bs_ai b) (bs_til b) (bs_tih b) -> 0 <= bs_ai b <= bs_ai b0 ->
    ctx_ok (cxN S uspb src len dst dn small 0 (cfg_tt c) (cfg_l16 c) (cfg_l4 c)) -> cfg_sizes_ok c 0 -> cfg_shape_ok c small 0 ->
    EARLY r ->
    pres P10 m mR ->
    RK usp S lo gp tp F fc (PK MDx) mR r 0 x5 x6 x7 x15 x16 x17 x28 x29 x30 x31 f160
       (Z_to_bv 64 10) (Z_to_bv 64 (S + 64080)) (Z_to_bv 64 100000) x24 (Z_to_bv 64 (-1)) (Z_to_bv 64 2) (Z_to_bv 64 1)
       (Z_to_bv 64 (S + 2047)) (Z_to_bv 64 (-2)) (Z_to_bv 64 (S + 1096)) x9 (Z_to_bv 64 S) (Z_to_bv 64 0x1481c).
  Proof.
    intros until f160. intros INVx VMO VMx AUXx ERRx RE HDx Hstrm Hst MIDx Ett El16 El4 STRMx Eb Hai CTX' SZ SH EY PR.
    pose proof LINf as LIN. lin_split LIN.
    unfold RK. intros m' y12 y13 y14 j1 j2 SAV' L1 L2 ST' MU' WM' MI'.
    apply evt_done. unfold PK. rewrite ret_pc_lit by (lia || reflexivity).
    assert (FW : Forall zone [(S + 64036, S + 64144)]) by (constructor; [unfold zone; cbn; lia| constructor]).
    assert (IS : In (pS, S, 64144) (cfg_extra c ++ LB)) by (apply in_or_app; right; exact INS).
    cps_pose (REST_munch _ _ _ FW MU' WM' RE) as (R1 & R2 & R3 & R4 & R5 & R6 & R7).
    assert (HDm : rw_cells s0segs m' S (HEAD_CELLS h)).
    { eapply rw_cells_transport; [exact HDx | exact MU' | exact WM' | cbn; lia]. }
    assert (MIDm : rw_cells s0segs m' (S + 3152) (MID_CELLS d)).
    { eapply rw_cells_transport; [exact MIDx | exact MU' | exact WM' | cbn; lia]. }
    assert (STRMm : rw_cells s0segs m' uspb (STRM_CELLS (bupd b0 (bs_ai b) (bs_til b) (bs_tih b)))).
    { rewrite <- Eb. eapply rw_cells_transport; [exact STRMx | exact MU' | exact WM' | cbn; lia]. }
    eapply (HK m' MDx sx c 0 r ev).
    - eapply inv_zone; [exact FW | exact MU' | exact WM' | exact IS | exact INVx].
    - exact VMO.
    - exact VMx.
    - eapply aux_zone; [exact FW | exact MU' | exact WM' | exact AUXx].
    - eapply err_zone; [exact FW | exact MU' | exact WM' | exact ERRx].
    - exact MI'.
    - exact ST'.
    - exact CTX'.
    - exact SZ.
    - exact SH.
    - lia.
    - exact R5.
    - exact R6.
    - exact R7.
    - apply pres10_of_pres. eapply pres_trans; [exact PR | eapply pres_zone; [exact FW | exact MU' | exact WM']].
    - right. split; [exact EY|]. exists h, d, (bs_ai b), (bs_til b), (bs_tih b).
      split; [exact HDm|]. split; [exact Hstrm|]. split; [lia|]. split; [unfold BZ_X_OUTPUT; lia|].
      split; [exact MIDm|]. split; [exact Ett|]. split; [exact El16|]. split; [exact El4|]. split; [exact STRMm| exact Hai].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition WA : list (Z * Z) := [(usp + -336, usp); (S + 64036, S + 64144)].
  Definition WM : list (Z * Z) := [(S, S + 68); (uspb, uspb + 20)].
  Lemma FWA : Forall zone WA. Proof. unfold WA; repeat constructor; unfold zone; cbn; lia. Qed.
  Lemma FWM : Forall zone WM. Proof using S uspb cf0 payload Lcf. unfold WM; repeat constructor; unfold zone; cbn; lia. Qed.

  Notation Z0 := (Z_to_bv 64 0).
  (* [comment removed for export] *)
  Definition FRA (mx : word -> option byte) (j0 : list byte) (f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 : word) (pb : list byte) : Prop :=
    rw_cells s0segs mx (usp + -336)
     [CB 8 j0; C8 f8; C8 f16; C8 f24; C8 f32; C8 f40; C8 f48; C8 f56; C8 f64; C8 f72; C8 f80;
      C8 (Z_to_bv 64 (S + 2047)); C8 Z0; C8 Z0; C8 Z0; C8 Z0; C8 Z0; C8 Z0; C8 Z0; C8 Z0; C8 Z0; C8 Z0; C8 Z0; C8 Z0; C8 Z0;
      C8 (Z_to_bv 64 (S + 7820)); C8 Z0; C8 Z0;
      CB 8 pb; C8 (Z_to_bv 64 10); C8 (Z_to_bv 64 (S + 64080)); C8 (Z_to_bv 64 100000); C8 x24; C8 (Z_to_bv 64 (-1));
      C8 (Z_to_bv 64 2); C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 (S + 2047)); C8 (Z_to_bv 64 (-2)); C8 (Z_to_bv 64 (S + 1096)); C8 x9; C8 (Z_to_bv 64 S); C8 (Z_to_bv 64 0x1481c)].

  Lemma GEO_R : 0 < S /\ S + 64144 <= lo /\ alloc_ceiling <= lo /\ lo <= usp - 1024 /\ usp < 2 ^ 64.
  Proof.
    pose proof LINf as LIN. lin_split LIN. cps_pose (ai_inv_blocks AI INV INS) as (_ & _ & _ & X & _). cbn [blk_addr blk_size fst snd] in X.
    bz_ceil. lia.
  Qed.

  Lemma MXI : forall (m1 mk : word -> option byte) (h : dsh) (b : bzs) (OUT : Z -> Prop)
      (x5 x6 x7 x21 x28 x29 : word) (j0 : list byte) (f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 : word) (pb : list byte),
    FRA m1 j0 f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 pb ->
    rw_cells s0segs m1 (S + 64036) [CB 108 (repeat (Z_to_bv 8 0) 108)] ->
    stk s0segs m1 lo (usp + -336) ->
    munch WA m m1 -> wmono s0segs m m1 ->
    munch WM m1 mk -> wmono s0segs m1 mk ->
    sh_strm h = uspb ->
    b = bupd b0 (bs_ai b) (bs_til b) (bs_tih b) -> 0 <= bs_ai b <= bs_ai b0 ->
    (forall rc, (rc = 0 \/ rc = -5) -> OUT rc -> EARLY rc) ->
    MXF usp S uspb len gp tp F fc OUT (PK MD) mk h b Z0 x5 x6 x7 Z0 Z0 Z0 (Z_to_bv 64 (S + 64036)) x21 Z0 Z0 Z0 Z0 (Z_to_bv 64 (S + 3176)) x28 x29 (Z_to_bv 64 (S + 7884)) Z0.
  Proof.
    intros until pb. intros FR1 SAV1 ST1 MUA WMA MUk WMk Hstrm Eb Hai EQ.
    pose proof LINf as LIN. lin_split LIN. pose proof GEO_R as GR.
    unfold MXF. intros rc y11 y12 y13 y14 y15 y16 y17 m' st bsBuff' bsLive' nn ai' til' tih' HD' Hst HbB Hnn STRM' Hai' HbL MU' WM' MI' Hrc Ho.
    pose proof (munch_trans _ _ _ _ MUk MU') as MUm. pose proof (wmono_trans s0segs _ _ _ WMk WM') as WMm. fold WM in MUm.
    assert (FR' : FRA m' j0 f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 pb).
    { unfold FRA in *. eapply rw_cells_transport; [exact FR1 | exact MUm | exact WMm | unfold WM; cbn; lia]. }
    assert (SAV' : rw_cells s0segs m' (S + 64036) [CB 108 (repeat (Z_to_bv 8 0) 108)]).
    { eapply rw_cells_transport; [exact SAV1 | exact MUm | exact WMm | unfold WM; cbn; lia]. }
    apply save_zero_cells in SAV'.
    assert (ST' : stk s0segs m' lo (usp + -336)).
    { eapply stk_transport_disjoint; [exact ST1 | exact MUm | exact WMm | unfold WM; cbn; lia]. }
    unfold FRA in FR'. unfold MSd.
    eapply (g10_R usp S lo gp tp F fc GR); [exact FR' | exact SAV' | rewrite repeat_length; reflexivity | rewrite repeat_length; reflexivity | exact ST' | exact MI' | lia |].
    rewrite Eb, bupd_bupd in STRM'.
    eapply (rk_finish MD s BNone m' rc _ (bupd b0 ai' til' tih') d0 errv); cbn [cfg_extra cfg_tt cfg_l16 cfg_l4 app].
    - eapply inv_zone; [exact FWM | exact MUm | exact WMm | exact INS |]. eapply inv_zone; [exact FWA | exact MUA | exact WMA | exact INS | exact INV].
    - apply vm_only_refl.
    - eapply ac_vm_le; [exact VMC | lia].
    - eapply aux_zone; [exact FWM | exact MUm | exact WMm |]. eapply aux_zone; [exact FWA | exact MUA | exact WMA | exact AUX].
    - eapply err_zone; [exact FWM | exact MUm | exact WMm |]. eapply err_zone; [exact FWA | exact MUA | exact WMA | exact ERR].
    - eapply REST_munch; [exact FWM | exact MUm | exact WMm |]. eapply REST_munch; [exact FWA | exact MUA | exact WMA | exact REST0].
    - exact HD'.
    - cbn. exact Hstrm.
    - cbn. exact Hst.
    - eapply rw_cells_transport; [| exact MUm | exact WMm | unfold WM; cbn; lia]. eapply rw_cells_transport; [exact MID | exact MUA | exact WMA | unfold WA; cbn; lia].
    - exact T0.
    - exact L160.
    - exact L40.
    - exact STRM'.
    - unfold bupd. reflexivity.
    - cbn. lia.
    - exact CTX.
    - exact I.
    - reflexivity.
    - exact (EQ rc Hrc Ho).
    - eapply pres_trans; [eapply pres_zone; [exact FWA | exact MUA | exact WMA] | eapply pres_zone; [exact FWM | exact MUm | exact WMm]].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma new_blocks : forall (c : bcfg) (sx : ai_AS AI) (mx : word -> option byte) (MDx : Model),
    ai_inv AI sx (cfg_extra c ++ LB) mx MDx ->
    (forall bb, In bb (cfg_extra c) -> NB S src len dst dn (blk_addr bb) (blk_size bb)) /\
    (forall b1 b2, In b1 (cfg_extra c) -> In b2 (cfg_extra c) -> b1 <> b2 ->
        blk_addr b1 + blk_size b1 <= blk_addr b2 \/ blk_addr b2 + blk_size b2 <= blk_addr b1).
  Proof.
    intros c sx mx MDx INVx. pose proof LINf as LIN. lin_split LIN. pose proof (ai_inv_nodup AI INVx) as ND. rewrite map_app in ND.
    assert (DJ : forall bb b1, In bb (cfg_extra c) -> In b1 LB -> blk_addr bb + blk_size bb <= blk_addr b1 \/ blk_addr b1 + blk_size b1 <= blk_addr bb).
    { intros bb b1 Hbb Hb1. apply (ai_inv_disjoint AI INVx); [apply in_or_app; left; exact Hbb | apply in_or_app; right; exact Hb1 |].
      intros E. subst b1. eapply (nodup_app_disj _ _ (blk_id bb) ND); [apply in_map; exact Hbb | apply in_map; exact Hb1]. }
    split.
    - intros bb Hbb. cps_pose (ai_inv_blocks AI INVx ltac:(apply in_or_app; left; exact Hbb)) as (B1 & B2 & B3 & B4 & B5).
      bz_ceil. unfold L, S0_layout in B5; cbn [al_img_lo al_img_hi] in B5.
      bz_ceil; unfold NB, img_apart, IHI, disj, CEILING, DSTATE_SIZE.
      pose proof (DJ _ _ Hbb INS) as D1. pose proof (DJ _ _ Hbb IND) as D2. cbn [blk_addr blk_size fst snd] in D1, D2.
      repeat match goal with |- _ /\ _ => split end; try lia.
      destruct CR as [C|[(C1 & C2 & _)|(bq & Hbq & C1 & C2)]]; [lia | unfold L, S0_layout in C1, C2; cbn [al_rw_lo al_img_hi] in C1, C2; lia |].
      pose proof (DJ _ _ Hbb Hbq). lia.
    - intros b1 b2 H1 H2 NE. apply (ai_inv_disjoint AI INVx); [apply in_or_app; left; exact H1 | apply in_or_app; left; exact H2 | exact NE].
  Qed.

  Lemma outside_of_in : forall W x, (forall l h, In (l, h) W -> ~ (l <= x < h)) -> outside W x.
  Proof.
    induction W as [|[l h] W IH]; intros x H; cbn; [exact I|]. split; [apply H; left; reflexivity|]. apply IH. intros l' h' Hin. apply H. right. exact Hin.
  Qed.
  Lemma Forall_of_in : forall (P : Z * Z -> Prop) (W : list (Z * Z)), (forall l h, In (l, h) W -> P (l, h)) -> Forall P W.
  Proof. intros P W H. apply Forall_forall. intros [l h] Hin. apply H. exact Hin. Qed.

  Lemma pres_W14 : forall (c : bcfg) (n : Z) (sx : ai_AS AI) (mx my : word -> option byte) (MDx : Model),
    let cx' := cxN S uspb src len dst dn small n (cfg_tt c) (cfg_l16 c) (cfg_l4 c) in
    ai_inv AI sx (cfg_extra c ++ LB) mx MDx -> cfg_sizes_ok c n -> cfg_shape_ok c small n ->
    match c with BFast _ | BSmall _ _ => True | _ => False end ->
    munch (W14 DI_S0 cx' usp) mx my -> wmono s0segs mx my ->
    pres P10 mx my /\ ai_inv AI sx (cfg_extra c ++ LB) my MDx /\ (ai_aux AI mx B -> ai_aux AI my B) /\
    (forall ev, rw_cells s0segs mx (errno_cell L) [C4 ev] -> rw_cells s0segs my (errno_cell L) [C4 ev]).
  Proof.
    intros c n sx mx my MDx cx' INVx SZ SH CC MU WM. pose proof LINf as LIN. lin_split LIN.
    destruct (new_blocks c sx mx MDx INVx) as [NBs DJs].
    assert (BL : forall a, in_block LB a -> a < alloc_ceiling /\ forall bb, In bb (cfg_extra c) -> ~ (blk_addr bb <= a < blk_addr bb + blk_size bb)).
    { (intros a; cps_intros (b & Hb & Hr)). cps_pose (ai_inv_blocks AI INV Hb) as (_ & _ & _ & X & _). bz_ceil. split; [lia|].
      intros bb Hbb R. pose proof (ai_inv_disjoint AI INVx (b1 := bb) (b2 := b) ltac:(apply in_or_app; left; exact Hbb) ltac:(apply in_or_app; right; exact Hb)) as D.
      assert (NE : bb <> b).
      { intros E. subst b. pose proof (ai_inv_nodup AI INVx) as ND. rewrite map_app in ND. eapply (nodup_app_disj _ _ (blk_id bb) ND); apply in_map; assumption. }
      specialize (D NE). lia. }
    (* [comment removed for export] *)
    assert (IVS : forall l h, In (l, h) (W14 DI_S0 cx' usp) ->
              (l = S /\ h = S + 64144) \/ (l = uspb /\ h = uspb + 20) \/ (l = usp - 1024 /\ h = usp) \/
              (exists bb, In bb (cfg_extra c) /\ l = blk_addr bb /\ h = blk_addr bb + blk_size bb)).
    { intros l h Hin. subst cx'. unfold W14, blk_ivls, D14, DSTATE_SIZE in Hin. cbn [cxN b_s b_strm b_small b_tt b_ll16 b_ll4 b_n app] in Hin.
      destruct c as [|bt|b4 b6|b6|b4]; try contradiction; cbn [cfg_extra cfg_tt cfg_l16 cfg_l4 cfg_sizes_ok cfg_shape_ok] in *;
        rewrite SH in Hin; cbn in Hin.
      - destruct Hin as [E|[E|[E|[E|[]]]]]; inversion E; subst; [left | right; left | right; right; left | right; right; right]; try (split; reflexivity).
        exists bt. split; [left; reflexivity|]. rewrite SZ. split; reflexivity.
      - destruct SZ as [Z4 Z6].
        destruct Hin as [E|[E|[E|[E|[E|[]]]]]]; inversion E; subst; [left | right; left | right; right; left | right; right; right | right; right; right]; try (split; reflexivity).
        + exists b6. split; [right; left; reflexivity|]. rewrite Z6. split; reflexivity.
        + exists b4. split; [left; reflexivity|]. rewrite Z4. split; reflexivity. }
    split; [| split; [| split]].
    - eapply pres_mono; [| apply pres_of_munch; [exact MU | exact WM]]. (intros a Ha; cps_intros (P1 & P2 & P3)). apply outside_of_in.
      intros l h Hin. destruct (IVS l h Hin) as [[-> ->]|[[-> ->]|[[-> ->]|(bb & Hbb & -> & ->)]]]; try lia.
      + destruct P1 as [P1|[P1|P1]]; [lia | lia | pose proof (proj1 (BL _ P1)); lia].
      + cps_pose (NBs _ Hbb) as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8). bz_ceil; unfold img_apart, IHI, CEILING in *.
        destruct P1 as [P1|[P1|P1]]; [lia | lia | exact (proj2 (BL _ P1) bb Hbb)].
    - eapply (ai_inv_frame AI); [exact INVx | exact MU | exact WM |]. apply Forall_of_in. intros l h Hin.
      destruct (IVS l h Hin) as [[-> ->]|[[-> ->]|[[-> ->]|(bb & Hbb & -> & ->)]]].
      + apply (cwo_blockx _ (pS, S, 64144)); [apply in_or_app; right; exact INS | cbn; lia | cbn; lia].
      + left. cbn. bz_ceil. lia.
      + left. cbn. bz_ceil. lia.
      + apply (cwo_blockx _ bb); [apply in_or_app; left; exact Hbb | lia | lia].
    - intros AX. pose proof IMGS as IG. eapply (ai_aux_frame AI); [exact AX | exact MU | exact WM |]. apply Forall_of_in. intros l h Hin.
      cbn [fst snd al_static L S0_layout]. unfold S0_static.
      destruct (IVS l h Hin) as [[-> ->]|[[-> ->]|[[-> ->]|(bb & Hbb & -> & ->)]]]; try (split; [lia | intros; lia]).
      cps_pose (NBs _ Hbb) as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8). bz_ceil; unfold img_apart, IHI, CEILING in *. split; [lia | intros; lia].
    - intros ev E. pose proof IMGS as IG. eapply rw_cells_transport; [exact E | exact MU | exact WM |]. unfold errno_cell, L, S0_layout; cbn [al_tp cells_size csize Nat.add Z.of_nat Pos.of_succ_nat].
      eapply (disjoint_from_Forall (fun iv => In iv (W14 DI_S0 cx' usp))); [apply Forall_forall; intros iv Hiv; exact Hiv|].
      intros l h Hin. destruct (IVS l h Hin) as [[-> ->]|[[-> ->]|[[-> ->]|(bb & Hbb & -> & ->)]]]; try lia.
      cps_pose (NBs _ Hbb) as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8). bz_ceil; unfold img_apart, IHI, CEILING in *. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma dpureF_bupd : forall cx ai til tih pay J d st,
    dpureF cx (bupd b0 ai til tih) pay J d st -> ai <= bs_ai b0 -> dpureF cx b0 pay J d st.
  Proof.
    intros cx ai til tih pay J d st DP Hai. unfold dpureF, jk_static, bupd in *. destruct b0; cbn in *.
    decompose [and] DP. repeat match goal with |- _ /\ _ => split end; try assumption; lia.
  Qed.

  Lemma h14_finish : forall (c : bcfg) (n v : Z) (rest : list Z) (sx : ai_AS AI) (mH : word -> option byte) (MDx : Model) (hH : dsh) (bH : bzs) (dH : dsm) (ev : word)
      (x1 x5 x6 x7 x8 z9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x21 x23 z24 x25 x26 x28 x29 x31 : word)
      (j0 : list byte) (f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 : word) (pb : list byte),
    let cx' := cxN S uspb src len dst dn small n (cfg_tt c) (cfg_l16 c) (cfg_l4 c) in
    ai_inv AI sx (cfg_extra c ++ LB) mH MDx -> vm_only MD MDx -> ac_vm AC kcr sx MDx -> ai_aux AI mH B -> rw_cells s0segs mH (errno_cell L) [C4 ev] ->
    cfg_sizes_ok c n -> cfg_shape_ok c small n -> match c with BFast _ | BSmall _ _ => True | _ => False end ->
    n = v - 48 -> 49 <= v <= 57 -> map bv_unsigned payload = 66 :: 90 :: 104 :: v :: rest ->
    (forall bb, In bb (cfg_extra c) -> exists jk, rw_cells s0segs mH (blk_addr bb) [CB (Z.to_nat (blk_size bb)) jk]) ->
    REST mH -> stk s0segs mH lo (usp + -336) -> mem_inv s0segs mH ->
    FRA mH j0 f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 pb ->
    rw_cells s0segs mH (S + 64036) [CB 108 (repeat (Z_to_bv 8 0) 108)] ->
    rw_cells s0segs mH S (HEAD_CELLS hH) -> sh_strm hH = uspb -> sh_state hH = 13 -> sh_bsLive hH = 0 ->
    sh_bsBuff hH = ((66 * 256 + 90) * 256 + 104) * 256 + v ->
    sh_n hH = n -> bv_unsigned (sh_small hH) = small -> sh_cbn hH = 0 -> sh_verb hH = 0 ->
    length (sh_p1 hH) = 3%nat -> length (sh_p2 hH) = 3%nat -> length (sh_p3 hH) = 3%nat ->
    0 <= sh_solen hH < 2 ^ 32 -> 0 <= sh_rNToGo hH < 2 ^ 32 -> 0 <= sh_rTPos hH < 2 ^ 32 -> 0 <= sh_origPtr hH < 2 ^ 32 ->
    rw_cells s0segs mH (S + 3152) (MID_CELLS dH) -> sm_tt dH = cfg_tt c -> sm_ll16 dH = cfg_l16 c -> sm_ll4 dH = cfg_l4 c -> 0 <= sm_nInUse dH < 2 ^ 32 ->
    sm_cccrc dH = Z_to_bv 64 0 ->
    rw_cells s0segs mH uspb (STRM_CELLS bH) -> bH = bupd b0 (bs_ai bH) (bs_til bH) (bs_tih bH) -> bs_ai bH = len - 4 ->
    pres P10 m mH ->
    realizes s0segs
      (mkCfg (MS (mkR x1 (Z_to_bv 64 (usp + -336)) gp tp x5 x6 x7 x8 z9 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 S)
                      x19 (Z_to_bv 64 (S + 64036)) x21 Z0 x23 z24 x25 x26 (Z_to_bv 64 (S + 3176)) x28 x29 (Z_to_bv 64 (S + 7884)) x31)
                 F (Z_to_bv 64 0x24c3c) fc None mH (seg_rom s0segs)) MDx) K.
  Proof.
    intros until pb. cbv zeta.
    intros INVx VMO VMx AUXx ERRx SZ SH CC Hnv Hv PZ BLKJ RE STx MIx FRx SAVx HDx Hstrm Hst HbL HbB Hn Hsm Hcbn Hverb L1 L2 L3 R1 R2 R3 R4
           MIDx Ett El16 El4 RnIu Hcc STRMx Eb Hai PR.
    assert (N19 : 1 <= n <= 9) by lia. assert (Hv8 : 0 <= v < 256) by lia.
    pose proof LINf as LIN. lin_split LIN. pose proof GEO_R as GR. destruct (ai_inv_model AI INVx) as [Hh Hl].
    destruct (new_blocks c sx mH MDx INVx) as [NBs DJs].
    cps_pose RE as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7).
    assert (LL : Z.of_nat (length rest) = len - 4).
    { pose proof (f_equal (@length Z) PZ) as X. rewrite length_map in X. cbn [length] in X. lia. }
    apply save_zero_cells in SAVx.
    set (cx' := cxN S uspb src len dst dn small n (cfg_tt c) (cfg_l16 c) (cfg_l4 c)) in *.
    (* [comment removed for export] *)
    assert (CTX' : ctx_ok cx').
    { subst cx'. destruct c as [|bt|b4 b6|b6|b4]; try contradiction; cbn [cfg_extra cfg_tt cfg_l16 cfg_l4 cfg_sizes_ok cfg_shape_ok] in *.
      - apply ctx_ok_ext; [exact CTX | lia | right; rewrite <- SZ; apply NBs; left; reflexivity | left; reflexivity | left; reflexivity | intros X; exfalso; exact (X eq_refl)].
      - destruct SZ as [Z4 Z6]. apply ctx_ok_ext; [exact CTX | lia | left; reflexivity | right; rewrite <- Z6; apply NBs; right; left; reflexivity
          | right; rewrite <- Z4; apply NBs; left; reflexivity |].
        intros _ _. rewrite <- Z4, <- Z6. unfold disj.
        destruct (DJs b6 b4 ltac:(right; left; reflexivity) ltac:(left; reflexivity)) as [D|D]; [| left; exact D | right; exact D].
        intros E. pose proof (ai_inv_nodup AI INVx) as ND. cbn in ND. apply nodup_cons_inv in ND as [NI _]. apply NI. left. rewrite E. reflexivity. }
    (* [comment removed for export] *)
    assert (BLK : exists k, blk_at s0segs mH cx' k).
    { subst cx'. destruct c as [|bt|b4 b6|b6|b4]; try contradiction; cbn [cfg_extra cfg_tt cfg_l16 cfg_l4 cfg_sizes_ok cfg_shape_ok] in *.
      - destruct (BLKJ bt ltac:(left; reflexivity)) as [jk BJ]. rewrite SZ in BJ.
        pose proof (u8arr_of_rw_cells s0segs _ _ _ _ BJ) as [BB BW].
        pose proof (proj1 (proj1 BJ)) as W; cbn in W; destruct W as [W _].
        cps_destruct (u32arr_of_bw s0segs mH (blk_addr bt) jk (400000 * n) (Z.to_nat (100000 * n)) BB ltac:(rewrite W, Z2Nat.id in BW by lia; exact BW) ltac:(rewrite W, Z2Nat.id by lia; reflexivity) ltac:(rewrite Z2Nat.id by lia; lia)) as (ws & U & LU).
        exists (BlkF ws). cbn. split; [exact SH|]. split; [exact U| rewrite LU, Z2Nat.id by lia; lia].
      - destruct SZ as [Z4 Z6].
        destruct (BLKJ b6 ltac:(right; left; reflexivity)) as [j6 B6]. destruct (BLKJ b4 ltac:(left; reflexivity)) as [j4 B4].
        pose proof (proj1 (proj1 B6)) as W6; cbn in W6; destruct W6 as [W6 _]. pose proof (proj1 (proj1 B4)) as W4; cbn in W4; destruct W4 as [W4 _].
        exists (BlkS j6 j4). cbn. split; [exact SH|].
        split; [exact (u8arr_of_rw_cells s0segs _ _ _ _ B6)|]. split; [rewrite W6, Z6, Z2Nat.id by lia; lia|].
        split; [exact (u8arr_of_rw_cells s0segs _ _ _ _ B4)| rewrite W4, Z4, Z2Nat.id by lia; lia]. }
    destruct BLK as [k BLK].
    (* [comment removed for export] *)
    set (h14 := DSH uspb 14 (sh_soch hH) (sh_p1 hH) (sh_solen hH) (sh_brand hH) (sh_p2 hH) (sh_rNToGo hH) (sh_rTPos hH)
                    (sh_bsBuff hH) (sh_bsLive hH) n (sh_small hH) (sh_p3 hH) 0 0 (sh_origPtr hH) (sh_tPos hH) (sh_k0 hH)).
    set (A := ACT (Z_to_bv 64 0x1481c) (Z_to_bv 64 usp) gp tp (Z_to_bv 64 S) x9 (Z_to_bv 64 (S + 1096)) (Z_to_bv 64 (-2))
                  (Z_to_bv 64 (S + 2047)) (Z_to_bv 64 1) (Z_to_bv 64 2) (Z_to_bv 64 (-1)) x24 (Z_to_bv 64 100000) (Z_to_bv 64 (S + 64080)) (Z_to_bv 64 10)
                  F fc mH cx' h14 bH lo g1 sv payload).
    assert (BWF' : bzs_wf bH).
    { clear - Eb BWF Hai Hlen LL. rewrite Eb. unfold bzs_wf, bupd in *. destruct b0. cbn in *. lia. }
    assert (AOK : act_ok 320 A).
    { unfold act_ok. subst A. cbn [a_cx a_lo a_sp a_h0 a_b0 a_payload]. subst h14. cbn [sh_state sh_strm sh_n sh_small].
      rewrite unsigned_lit by lia. bz_ceil; unfold D14, CEILING.
      split; [exact CTX'|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [reflexivity|].
      split. { unfold dsh_wf. cbn. repeat match goal with |- _ /\ _ => split end; try assumption; try lia. }
      split; [exact BWF'|]. split; [subst cx'; cbn; exact PAYL|].
      split; [subst cx'; reflexivity|]. split; [subst cx'; reflexivity|]. split; [subst cx'; cbn; exact Hsm|]. split; [subst cx'; cbn; lia|].
      rewrite Eb. unfold bupd. subst cx'. cbn [bs_S bs_src bs_len bs_dst bs_dlen cxN b_s b_src b_len b_dst b_dlen b_strm b_small b_tt b_ll16 b_ll4].
      split; [exact HbS|]. split; [exact Hsrc|]. split; [exact Hlen|]. split; [exact Hdst|]. split; [exact Hdlen|]. split; [lia|].
      destruct c as [|bt|b4 b6|b6|b4]; try contradiction; cbn [cfg_extra cfg_tt cfg_l16 cfg_l4 cfg_sizes_ok cfg_shape_ok] in *.
      - pose proof (NBs bt ltac:(left; reflexivity)) as (X & _). split; [intros _; lia|]. split; [intros E; exfalso; lia| lia].
      - pose proof (NBs b6 ltac:(right; left; reflexivity)) as (X6 & _). pose proof (NBs b4 ltac:(left; reflexivity)) as (X4 & _).
        split; [intros E; exfalso; lia|]. split; [intros _; lia| lia]. }
    (* [comment removed for export] *)
    cps_pose (d14_fields (jd_of hH nbu0 cf0 dH r0 k) small v Hv8) as
      (Fst & FbL & FbB & Fn & Fsm & Fsv & Fbn & Fvb & Fcc & Ftal & Flal & Foc & Fol & Frd & Frn & Frt & Fop & Ftp & Fk0 & Fuz & Fnu & Frest).
    assert (RAW : dmem DI_S0 cx' g1 sv payload mH
                    (dvF cx' (jk_of hH (repeat (Z_to_bv 8 0) 44) (repeat (Z_to_bv 8 0) 60) b0 (bs_til bH) (bs_tih bH))
                         ((fun jd => d14 jd small v) (jd_of hH nbu0 cf0 dH r0 k)) (s14 rest dn))
                  /\ jk_wf (jk_of hH (repeat (Z_to_bv 8 0) 44) (repeat (Z_to_bv 8 0) 60) b0 (bs_til bH) (bs_tih bH))
                  /\ jk_static b0 (jk_of hH (repeat (Z_to_bv 8 0) 44) (repeat (Z_to_bv 8 0) 60) b0 (bs_til bH) (bs_tih bH))
                  /\ drep ((fun jd => d14 jd small v) (jd_of hH nbu0 cf0 dH r0 k))).
    { eapply (raw_dvF DI_S0 (fun jd => d14 jd small v) cx' g1 sv payload mH hH nbu0 cf0 dH
                (repeat (Z_to_bv 8 0) 44) 0 (repeat (Z_to_bv 8 0) 60) r0 b0 (len - 4) (bs_til bH) (bs_tih bH) k (s14 rest dn));
        cbv beta; try (subst cx'; cbn [b_s b_strm b_src b_tt b_ll16 b_ll4 b_len b_dst b_dlen b_small b_n cxN di_got di_stderrp di_crc di_rnums di_segs DI_S0]).
      - apply junk_kept_d14. exact Hv8.
      - exact HDx.
      - exact Q1.
      - exact Q2.
      - exact Lcf.
      - exact MIDx.
      - exact SAVx.
      - exact Q3.
      - rewrite Eb, Hai in STRMx. exact STRMx.
      - exact BLK.
      - exact Q4.
      - exact Q5.
      - exact Q6.
      - exact Q7.
      - exact Hstrm.
      - rewrite Fst. symmetry. exact Hst.
      - rewrite FbB. symmetry. exact HbB.
      - rewrite FbL. symmetry. exact HbL.
      - rewrite Fn, Hn. lia.
      - rewrite Fsm. symmetry. exact Hsm.
      - rewrite Fbn. symmetry. exact Hcbn.
      - rewrite Fvb. symmetry. exact Hverb.
      - rewrite Fcc, Hcc. reflexivity.
      - rewrite Fsv. reflexivity.
      - exact Ett.
      - exact El16.
      - exact El4.
      - exact HbS.
      - exact Hsrc.
      - exact Hlen.
      - exact Hdst.
      - exact Hdlen.
      - cbn [s_avail_out s14]. rewrite AV0. exact Hdlen.
      - cbn [s_in s14]. lia. }
    cbv beta in RAW. cps_destruct RAW as (DM & JW & JS & DRP).
    set (J := jk_of hH (repeat (Z_to_bv 8 0) 44) (repeat (Z_to_bv 8 0) 60) b0 (bs_til bH) (bs_tih bH)) in *.
    set (jd := jd_of hH nbu0 cf0 dH r0 k) in *.
    assert (NBU0 : d_nused jd = nbu0) by (subst jd; reflexivity).
    set (Fh := (9 * length rest + 92)%nat).
    (* [comment removed for export] *)
    eapply (evt_realizes s0segs (QF A (drun Fh 14 dsv_zero (d14 jd small v) (s14 rest dn)))); [exact Hh | exact Hl | |].
    { eapply evt_eq; [| eapply (S0F_dec_H14 A AOK Fh dsv_zero (d14 jd small v) (s14 rest dn) J)];
        subst A; cbn [a_ra a_sp a_gp a_tp a_s0 a_s1 a_s2 a_s3 a_s4 a_s5 a_s6 a_s7 a_s8 a_s9 a_s10 a_s11 a_F a_fc a_m0 a_cx a_h0 a_b0 a_lo a_g1 a_sv a_payload];
        rewrite ?unsigned_lit by lia.
      - subst cx'. cbn [b_s cxN sv_nblock dsv_zero]. st_eq.
      - exact DM.
      - unfold FRA in FRx. exact FRx.
      - exact STx.
      - apply munch_refl.
      - apply wmono_refl.
      - exact MIx.
      - unfold dpureF. rewrite Fn, Fsm, Fvb, FbB, FbL, Fbn, Fsv, Fnu, NBU0. cbn [s_avail_out s_in s14 sv_nblock dsv_zero].
        split; [exact JW|].
        split. { clear - JS Eb. rewrite Eb. unfold jk_static, bupd in *. destruct b0; cbn in *. exact JS. }
        split; [subst cx'; cbn [b_n cxN]; lia|].
        split; [subst cx'; cbn [b_small cxN]; reflexivity|].
        split; [reflexivity|].
        split; [rewrite Eb; unfold bupd; cbn [bs_av]; rewrite AV0, Hdlen; reflexivity|].
        split; [lia|].
        split. { exists 4%nat. replace rest with (skipn 4 (map bv_unsigned payload)) by (rewrite PZ; reflexivity). rewrite skipn_map. reflexivity. }
        split; [lia|]. split; [lia|]. split; [lia|].
        split; [rewrite Eb; unfold bupd; cbn [bs_len]; rewrite Hlen; lia|].
        split; [lia|]. split; [lia|]. exact DRP.
      - unfold dinv_H14, nb_ok. cbn [sv_nblock dsv_zero]. lia.
      - unfold fuel_ok. rewrite FbL. cbn [s_in s14]. subst Fh. lia. }
    (* [comment removed for export] *)
    intros ms' POST. unfold QF, FPOST14 in POST. cbv beta in POST. subst A.
    cbn [a_ra a_sp a_gp a_tp a_s0 a_s1 a_s2 a_s3 a_s4 a_s5 a_s6 a_s7 a_s8 a_s9 a_s10 a_s11 a_F a_fc a_m0 a_cx a_h0 a_b0 a_lo a_g1 a_sv a_payload
         di_segs di_got di_stderrp di_crc di_rnums DI_S0] in POST.
    subst Fh. rewrite <- (dec10_ok' jd small dn v rest Hv) in POST.
    pose proof (decompress_rv (dst_init jd 0 small) (s10 (66 :: 90 :: 104 :: v :: rest) dn)) as RV.
    remember (decompress (dst_init jd 0 small) (s10 (66 :: 90 :: 104 :: v :: rest) dn)) as R eqn:ED.
    destruct R as [[rv d'] s']. cbn in RV.
    cps_destruct POST as (u0 & u1 & u2 & ua1 & ua2 & ua3 & ua4 & ua5 & ua6 & ua7 & u3 & u4 & u5 & u6 & m' & J' & -> & MU' & WM' & MI' & DM' & ST' & DP' & PST).
    rewrite ret_pc_lit by (lia || reflexivity). rewrite (unsigned_lit usp) in MU' by lia. rewrite (unsigned_lit usp) in ST' by lia.
    cps_destruct (pres_W14 c n sx mH m' MDx INVx SZ SH CC MU' WM') as (PRW & INV' & AUXf & ERRf).
    pose proof DM' as X. unfold dmem in X. cbn [di_segs di_got di_stderrp di_crc di_rnums DI_S0] in X.
    cps_destruct X as (_ & _ & _ & _ & _ & _ & _ & _ & _ & GOT' & SEV' & RN').
    eapply (HK m' MDx sx c n rv ev).
    - exact INV'.
    - exact VMO.
    - exact VMx.
    - exact (AUXf AUXx).
    - exact (ERRf _ ERRx).
    - exact MI'.
    - exact ST'.
    - exact CTX'.
    - exact SZ.
    - exact SH.
    - lia.
    - exact GOT'.
    - exact SEV'.
    - exact RN'.
    - apply pres10_of_pres. eapply pres_trans; [exact PR | exact PRW].
    - left. exists jd, J'. rewrite PZ. unfold s10 in ED. rewrite <- ED. cbv beta iota.
      split; [reflexivity|]. split; [exact DM'|].
      split. { rewrite Eb in DP'. eapply dpureF_bupd; [exact DP' | lia]. }
      unfold dpost14W. split; [| split; [| exact RV]].
      + intros E2. exact (PST E2).
      + intros _. pose proof (dpureF_rep _ _ _ _ _ _ DP') as RP. unfold drep in RP. change (2^32)%Z with 4294967296%Z in RP. tauto.
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma GEO_M : 0 < S /\ S + 64144 <= uspb /\ alloc_ceiling <= usp - 1024 /\ usp + 112 <= uspb /\ uspb + 80 < 2 ^ 64 /\
                0 < src /\ src + len <= alloc_ceiling /\ 0 <= len < 2 ^ 27 /\ Z.of_nat (length payload) = len.
  Proof. pose proof LINf as LIN. lin_split LIN. lia. Qed.
  Lemma GEO_C : 0 < S /\ S + 64144 <= lo /\ alloc_ceiling <= lo /\ lo <= usp - 1024 /\ usp + 112 <= uspb /\ uspb + 80 < 2 ^ 64.
  Proof. pose proof LINf as LIN. lin_split LIN. pose proof GEO_R as GR. lia. Qed.

  (* [comment removed for export] *)
  Lemma bfacts : forall ai til tih, 0 <= ai <= bs_ai b0 ->
    let b := bupd b0 ai til tih in
    (0 <= bs_ai b <= bs_len b /\ 0 <= bs_av b <= bs_dlen b /\ 0 < bs_src b /\ bs_src b + bs_len b < 2 ^ 64 /\
     0 <= bs_dst b /\ bs_dst b + bs_dlen b < 2 ^ 64 /\ 0 <= bs_S b < 2 ^ 64).
  Proof.
    intros ai til tih H. pose proof LINf as LIN. lin_split LIN. unfold bupd. cbn. rewrite HbS, Hsrc, Hlen, Hdst, Hdlen. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma after_malloc : forall (LBx LB' : list ablock) (mx my : word -> option byte),
    heap_pres s0segs L LBx (usp + -336) mx my -> In (pS, S, 64144) LBx -> (forall b, In b LB -> In b LBx) ->
    (REST mx -> REST my) /\ (pres P10 m mx -> pres P10 m my) /\
    (forall A cs, rw_cells s0segs mx A cs -> (usp + -336 <= A \/ (S <= A /\ A + Z.of_nat (cells_size cs) <= S + 64144)) -> rw_cells s0segs my A cs).
  Proof.
    intros LBx LB' mx my HP IS SUB. pose proof LINf as LIN. lin_split LIN. split; [| split].
    - apply (REST_heap LBx (usp + -336) mx my HP IS SUB). lia.
    - intros PR. eapply pres_trans; [exact PR | eapply pres_heapx; [exact HP | lia | exact SUB]].
    - intros A cs H [HA|HA]; eapply heap_pres_rw_cells; [exact HP | exact H | left; lia | exact HP | exact H | right; right; exists (pS, S, 64144); split; [exact IS| cbn; lia]].
  Qed.

  Lemma main :
    realizes s0segs
      (mkCfg (MS (mkR (Z_to_bv 64 0x1481c) (Z_to_bv 64 usp) gp tp t0 t1 t2 (Z_to_bv 64 S) x9
                      (Z_to_bv 64 S) a1 a2 a3 a4 a5 a6 a7
                      (Z_to_bv 64 (S + 1096)) (Z_to_bv 64 (-2)) (Z_to_bv 64 (S + 2047)) (Z_to_bv 64 1) (Z_to_bv 64 2) (Z_to_bv 64 (-1))
                      x24 (Z_to_bv 64 100000) (Z_to_bv 64 (S + 64080)) (Z_to_bv 64 10) t3 t4 t5 t6)
                 F (Z_to_bv 64 0x2462c) fc None m (seg_rom s0segs)) MD) K.
  Proof.
    pose proof LINf as LIN. lin_split LIN. pose proof GEO_R as GR. pose proof GEO_M as GM. pose proof GEO_C as GC. pose proof SEPS as SP. pose proof IMGS as IG. pose proof SM01 as SM.
    pose proof ALS as (SAL & UAL).
    destruct (ai_inv_model AI INV) as [Hh Hl].
    assert (Hstrm0 : sh_strm h0 = uspb) by lia.
    assert (TIL0 : bs_til b0 = Z_to_bv 64 (len - bs_ai b0)) by (rewrite Htil0; f_equal; lia).
    pose proof (bfacts (bs_ai b0) (bs_til b0) (bs_tih b0) ltac:(lia)) as BF0. rewrite bupd_id in BF0. cbv zeta in BF0.
    set (pz := map bv_unsigned payload) in *.
    assert (PZ0 : pz = [] ++ skipn 0 pz) by reflexivity.
    (* [comment removed for export] *)
    eapply (evt_realizes s0segs (PK MD)); [exact Hh | exact Hl | | intros ms' X; exact X].
    eapply g10_A with (lo := lo) (h := h0) (js := js);
      [exact HD | lia | lia | lia | lia | lia | lia | exact SAV | exact ST | lia | lia | lia | lia | lia | exact IG | lia | exact SAL | exact MI |].
    intros m1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x21 x28 x29 j0 f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 pb FR1 HD1 SAV1 ST1 MU1 WM1 MI1.
    rewrite Hstrm0. fold WA in MU1.
    assert (PAY1 : bytes_at s0segs m1 src payload) by (eapply bytes_at_transport; [exact PAY | exact MU1 | unfold WA; cbn; lia]).
    assert (STRM1 : rw_cells s0segs m1 uspb (STRM_CELLS b0)) by (eapply rw_cells_transport; [exact STRM | exact MU1 | exact WM1 | unfold WA; cbn; lia]).
    (* [comment removed for export] *)
    eapply (g10F_M123 usp S uspb src len gp tp F fc payload GM SP UAL 0x247c4 10 66 0x24888 ltac:(left; repeat split; reflexivity)
              _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 h0 b0 (PK MD));
      [ exact HD1 | exact Hstrm0 | lia | lia | lia | lia | lia | lia
      | exact STRM1 | exact Hsrc | exact Hlen | lia | exact TIL0 | lia | lia | lia
      | exact PAY1 | exact MI1
      | eapply (MXI m1 m1); [exact FR1 | exact SAV1 | exact ST1 | exact MU1 | exact WM1 | apply munch_refl | apply wmono_refl
                            | lia | symmetry; apply bupd_id | lia |]
      | ].
    { (* [comment removed for export] *)
      intros rc _ [[-> A0]|[-> (bx & NX & NE)]]; eapply (EARLY_model _ dst_zero); subst pz.
      - rewrite (pz_end payload [] 0 PZ0 eq_refl ltac:(lia)). apply dec10_eof0'.
      - replace (Z.to_nat (len - bs_ai b0)) with 0%nat in NX by lia.
        rewrite (pz_step payload [] 0 bx PZ0 eq_refl NX). cbn [app skipn]. apply dec10_bad0'; [apply byte_range | exact NE]. }
    intros ? ? ? ? ? m2 b81 h1 HD2 NTH1 E81 STRM2 AI2 MU2 WM2 MI2.
    replace (Z.to_nat (len - bs_ai b0)) with 0%nat in NTH1 by lia.
    pose proof (pz_step payload [] 0 b81 PZ0 eq_refl NTH1) as PZ1. rewrite E81 in PZ1. cbn [app] in PZ1. fold pz in PZ1. clear PZ0.
    set (b1 := bupd b0 (bs_ai b0 - 1) (Z_to_bv 64 (len - (bs_ai b0 - 1))) (bs_tih b0)) in *.
    fold WM in MU2.
    assert (PAY2 : bytes_at s0segs m2 src payload) by (eapply bytes_at_transport; [exact PAY1 | exact MU2 | unfold WM; cbn; lia]).
    (* [comment removed for export] *)
    eapply (g10F_M123 usp S uspb src len gp tp F fc payload GM SP UAL 0x24888 11 90 0x2494c ltac:(right; left; repeat split; reflexivity)
              _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m2 h1 b1 (PK MD));
      [ exact HD2 | cbn; exact Hstrm0 | reflexivity | cbn; lia | cbn; lia | cbn; lia | cbn; lia | cbn; lia
      | exact STRM2 | cbn; exact Hsrc | cbn; exact Hlen | cbn; lia | cbn; f_equal; lia | cbn; lia | cbn; lia | cbn; lia
      | exact PAY2 | exact MI2
      | eapply (MXI m1 m2); [exact FR1 | exact SAV1 | exact ST1 | exact MU1 | exact WM1 | exact MU2 | exact WM2
                            | cbn; exact Hstrm0 | reflexivity | cbn; lia |]
      | ].
    { intros rc _ [[-> A0]|[-> (bx & NX & NE)]]; eapply (EARLY_model _ dst_zero); cbv delta [b1] in *; cbn [bs_ai bupd] in *; subst pz.
      - rewrite (pz_end payload [66] 1 PZ1 eq_refl ltac:(lia)). apply dec10_eof1.
      - replace (Z.to_nat (len - (bs_ai b0 - 1))) with 1%nat in NX by lia.
        rewrite (pz_step payload [66] 1 bx PZ1 eq_refl NX). cbn [app skipn]. apply dec10_bad1; [apply byte_range | exact NE]. }
    intros ? ? ? ? ? m3 b82 h2 HD3 NTH2 E82 STRM3 AI3 MU3 WM3 MI3. cbv delta [b1] in AI3, NTH2; cbn [bs_ai bupd] in AI3, NTH2.
    replace (Z.to_nat (len - (bs_ai b0 - 1))) with 1%nat in NTH2 by lia.
    pose proof (pz_step payload [66] 1 b82 PZ1 eq_refl NTH2) as PZ2. rewrite E82 in PZ2. cbn [app] in PZ2. fold pz in PZ2. clear PZ1.
    set (b2 := bupd b1 (bs_ai b1 - 1) (Z_to_bv 64 (len - (bs_ai b1 - 1))) (bs_tih b1)) in *.
    fold WM in MU3. pose proof (munch_trans _ _ _ _ MU2 MU3) as MUc3. pose proof (wmono_trans s0segs _ _ _ WM2 WM3) as WMc3.
    assert (PAY3 : bytes_at s0segs m3 src payload) by (eapply bytes_at_transport; [exact PAY2 | exact MU3 | unfold WM; cbn; lia]).
    (* [comment removed for export] *)
    eapply (g10F_M123 usp S uspb src len gp tp F fc payload GM SP UAL 0x2494c 12 104 0x24a0c ltac:(right; right; repeat split; reflexivity)
              _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m3 h2 b2 (PK MD));
      [ exact HD3 | cbn; exact Hstrm0 | reflexivity | cbn; lia | cbn; lia | cbn; lia | cbn; lia | cbn; lia
      | exact STRM3 | cbn; exact Hsrc | cbn; exact Hlen | cbn; lia | cbn; f_equal; lia | cbn; lia | cbn; lia | cbn; lia
      | exact PAY3 | exact MI3
      | eapply (MXI m1 m3); [exact FR1 | exact SAV1 | exact ST1 | exact MU1 | exact WM1 | exact MUc3 | exact WMc3
                            | cbn; exact Hstrm0 | reflexivity | cbn; lia |]
      | ].
    { intros rc _ [[-> A0]|[-> (bx & NX & NE)]]; eapply (EARLY_model _ dst_zero); cbv delta [b1 b2] in *; cbn [bs_ai bupd] in *; subst pz.
      - rewrite (pz_end payload [66; 90] 2 PZ2 eq_refl ltac:(lia)). apply dec10_eof2.
      - replace (Z.to_nat (len - (bs_ai b0 - 1 - 1))) with 2%nat in NX by lia.
        rewrite (pz_step payload [66; 90] 2 bx PZ2 eq_refl NX). cbn [app skipn]. apply dec10_bad2; [apply byte_range | exact NE]. }
    intros ? ? ? ? ? m4 b83 h3 HD4 NTH3 E83 STRM4 AI4 MU4 WM4 MI4. cbv delta [b1 b2] in AI4, NTH3; cbn [bs_ai bupd] in AI4, NTH3.
    replace (Z.to_nat (len - (bs_ai b0 - 1 - 1))) with 2%nat in NTH3 by lia.
    pose proof (pz_step payload [66; 90] 2 b83 PZ2 eq_refl NTH3) as PZ3. rewrite E83 in PZ3. cbn [app] in PZ3. fold pz in PZ3. clear PZ2.
    set (b3 := bupd b2 (bs_ai b2 - 1) (Z_to_bv 64 (len - (bs_ai b2 - 1))) (bs_tih b2)) in *.
    fold WM in MU4. pose proof (munch_trans _ _ _ _ MUc3 MU4) as MUc4. pose proof (wmono_trans s0segs _ _ _ WMc3 WM4) as WMc4.
    assert (PAY4 : bytes_at s0segs m4 src payload) by (eapply bytes_at_transport; [exact PAY3 | exact MU4 | unfold WM; cbn; lia]).
    (* [comment removed for export] *)
    eapply (g10F_M4 usp S uspb src len gp tp F fc payload GM SP UAL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m4 h3 b3 (PK MD));
      [ exact HD4 | cbn; exact Hstrm0 | reflexivity | cbn; lia | cbn; lia | cbn; lia | cbn; lia | cbn; lia
      | exact STRM4 | cbn; exact Hsrc | cbn; exact Hlen | cbn; lia | cbn; f_equal; lia | cbn; lia | cbn; lia | cbn; lia
      | exact PAY4 | exact MI4
      | eapply (MXI m1 m4); [exact FR1 | exact SAV1 | exact ST1 | exact MU1 | exact WM1 | exact MUc4 | exact WMc4
                            | cbn; exact Hstrm0 | reflexivity | cbn; lia |]
      | ].
    { intros rc _ [[-> A0]|[-> (bx & NX & NE)]]; eapply (EARLY_model _ dst_zero); cbv delta [b1 b2 b3] in *; cbn [bs_ai bupd] in *; subst pz.
      - rewrite (pz_end payload [66; 90; 104] 3 PZ3 eq_refl ltac:(lia)). apply dec10_eof3.
      - replace (Z.to_nat (len - (bs_ai b0 - 1 - 1 - 1))) with 3%nat in NX by lia.
        rewrite (pz_step payload [66; 90; 104] 3 bx PZ3 eq_refl NX). cbn [app skipn]. apply dec10_bad3; [apply byte_range | exact NE]. }
    intros ? ? ? ? ? ? m5 b84 uc5 h4 HD5 Ruc5 NTH4 E84 STRM5 AI5 MU5 WM5 MI5. cbv delta [b1 b2 b3] in AI5, NTH4; cbn [bs_ai bupd] in AI5, NTH4.
    replace (Z.to_nat (len - (bs_ai b0 - 1 - 1 - 1))) with 3%nat in NTH4 by lia.
    pose proof (pz_step payload [66; 90; 104] 3 b84 PZ3 eq_refl NTH4) as PZ4. rewrite E84 in PZ4. cbn [app] in PZ4. fold pz in PZ4. clear PZ3.
    set (b4 := bupd b3 (bs_ai b3 - 1) (Z_to_bv 64 (len - (bs_ai b3 - 1))) (bs_tih b3)) in *.
    fold WM in MU5. pose proof (munch_trans _ _ _ _ MUc4 MU5) as MUc5. pose proof (wmono_trans s0segs _ _ _ WMc4 WM5) as WMc5.
    assert (Eb4 : b4 = bupd b0 (bs_ai b4) (bs_til b4) (bs_tih b4)) by reflexivity.
    assert (Hai4 : 0 <= bs_ai b4 <= bs_ai b0) by (cbv delta [b1 b2 b3 b4]; cbn [bs_ai bupd]; lia).
    assert (Hai4' : bs_ai b4 = len - 4) by (cbv delta [b1 b2 b3 b4]; cbn [bs_ai bupd]; lia).
    (* [comment removed for export] *)
    assert (FR5 : FRA m5 j0 f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 pb).
    { unfold FRA in *. eapply rw_cells_transport; [exact FR1 | exact MUc5 | exact WMc5 | unfold WM; cbn; lia]. }
    assert (SAV5 : rw_cells s0segs m5 (S + 64036) [CB 108 (repeat (Z_to_bv 8 0) 108)]).
    { eapply rw_cells_transport; [exact SAV1 | exact MUc5 | exact WMc5 | unfold WM; cbn; lia]. }
    assert (ST5 : stk s0segs m5 lo (usp + -336)).
    { eapply stk_transport_disjoint; [exact ST1 | exact MUc5 | exact WMc5 | unfold WM; cbn; lia]. }
    assert (MID5 : rw_cells s0segs m5 (S + 3152) (MID_CELLS d0)).
    { eapply rw_cells_transport; [| exact MUc5 | exact WMc5 | unfold WM; cbn; lia]. eapply rw_cells_transport; [exact MID | exact MU1 | exact WM1 | unfold WA; cbn; lia]. }
    assert (REST5 : REST m5).
    { eapply REST_munch; [exact FWM | exact MUc5 | exact WMc5 |]. eapply REST_munch; [exact FWA | exact MU1 | exact WM1 | exact REST0]. }
    assert (INV5 : ai_inv AI s LB m5 MD).
    { eapply inv_zone; [exact FWM | exact MUc5 | exact WMc5 | exact INS |]. eapply inv_zone; [exact FWA | exact MU1 | exact WM1 | exact INS | exact INV]. }
    assert (AUX5 : ai_aux AI m5 B).
    { eapply aux_zone; [exact FWM | exact MUc5 | exact WMc5 |]. eapply aux_zone; [exact FWA | exact MU1 | exact WM1 | exact AUX]. }
    assert (ERR5 : rw_cells s0segs m5 (errno_cell L) [C4 errv]).
    { eapply err_zone; [exact FWM | exact MUc5 | exact WMc5 |]. eapply err_zone; [exact FWA | exact MU1 | exact WM1 | exact ERR]. }
    assert (PR5 : pres P10 m m5).
    { eapply pres_trans; [eapply pres_zone; [exact FWA | exact MU1 | exact WM1] | eapply pres_zone; [exact FWM | exact MUc5 | exact WMc5]]. }
    (* [comment removed for export] *)
    assert (VM1 : ac_vm AC (ac_cost ((uc5 - 48) * 400000) + (1 + kcr))%nat s MD).
    { eapply ac_vm_le; [exact VMC|]. unfold ac_cost. replace ((uc5 - 48) * 400000 <? 1024) with false by (symmetry; apply Z.ltb_ge; lia). lia. }
    assert (VM2 : ac_vm AC (ac_cost ((uc5 - 48) * 200000) + (1 + kcr))%nat s MD).
    { eapply ac_vm_le; [exact VMC|]. unfold ac_cost. replace ((uc5 - 48) * 200000 <? 1024) with false by (symmetry; apply Z.ltb_ge; lia). lia. }
    clear MU2 MU3 MU4 MU5 WM2 WM3 WM4 WM5 MUc3 MUc4 WMc3 WMc4 PAY1 PAY2 PAY3 PAY4 HD1 HD2 HD3 HD4 STRM1 STRM2 STRM3 STRM4 MI1 MI2 MI3 MI4.
    (* [comment removed for export] *)
    unfold FRA in FR5.
    eapply (g10_C1 usp S uspb lo gp tp F fc GC) with (uc := uc5) (small := small) (h := h4) (b := b4) (Q := PK MD);
      [ exact FR5 | exact HD5 | cbn; lia | exact SM | cbn; lia | cbn; lia | cbn; lia | cbn; lia | cbn; lia
      | exact STRM5 | cbn; exact BZA | cbn; lia | exact Ruc5 | exact MI5 | | ].
    (* [comment removed for export] *)
    { intros m6 ya1 ya2 ya3 h5 SM0 FR6 HD6 STRM6 MU6 WM6 MI6. unfold MSm.
      assert (FW6 : Forall zone [(usp + -336, usp); (S, S + 68)]) by (repeat constructor; unfold zone; cbn; lia).
      apply evt_done. unfold PK.
      eapply DCV with (s := s) (LB := LB) (k := (1 + kcr)%nat) (n := (uc5 - 48) * 400000) (lo := lo) (B := B) (errv := errv);
        [ eapply inv_zone; [exact FW6 | exact MU6 | exact WM6 | exact INS | exact INV5]
        | exact VM1
        | eapply aux_zone; [exact FW6 | exact MU6 | exact WM6 | exact AUX5]
        | rewrite unsigned_lit by lia; lia
        | rewrite unsigned_lit by lia; eapply stk_transport_disjoint; [exact ST5 | exact MU6 | exact WM6 | cbn; lia]
        | exact LOC
        | rewrite unsigned_lit by lia; cbn [al_stack L S0_layout]; lia
        | eapply err_zone; [exact FW6 | exact MU6 | exact WM6 | exact ERR5]
        | exact MI6 | exact TP | reflexivity | unfold MAX_REQ_D; lia |].
      intros s7 LB7 m7 MD7 r1 z0 z1 z2 za1 za2 za3 za4 za5 za6 za7 z3 z4 z5 z6 ev7 INV7 VMO7 VMC7 MI7 ST7 ERR7 AUX7 HP7 RES7.
      rewrite unsigned_lit in ST7, HP7 by lia. rewrite ret_pc_lit by (lia || reflexivity).
      assert (SUB7 : forall bq, In bq LB -> In bq LB7) by (destruct RES7 as [[_ ->]|(_ & _ & (p1 & -> & _) & _)]; [intros bq H; exact H | intros bq H; right; exact H]).
      assert (IS7 : In (pS, S, 64144) LB7) by (apply SUB7; exact INS).
      cps_destruct (after_malloc LB LB7 m6 m7 HP7 INS (fun bq H => H)) as (AMR & AMP & AMC).
      assert (R01 : 0 <= r1 < 2 ^ 64).
      { destruct RES7 as [[-> _]|(_ & (B1 & _ & B3 & B4 & _) & _ & _)]; [lia|]. bz_ceil. lia. }
      assert (VMk : ac_vm AC kcr s7 MD7) by (eapply ac_vm_le; [exact VMC7| lia]).
      destruct (ai_inv_model AI INV7) as [Hh7 Hl7].
      eapply (evt_realizes s0segs (PK MD7)); [exact Hh7 | exact Hl7 | | intros ms' X; exact X].
      eapply (g10_C2f usp S uspb lo gp tp F fc GC) with (d := d0) (Q := PK MD7);
        [ apply AMC; [exact FR6 | left; lia]
        | apply AMC; [| right; cbn; lia]; eapply rw_cells_transport; [exact MID5 | exact MU6 | exact WM6 | cbn; lia]
        | lia | lia | lia | exact R01 | exact MI7 | |].
      - (* [comment removed for export] *)
        intros m8 E0 MID8 MU8 WM8 MI8.
        assert (FW8 : Forall zone [(S + 3152, S + 3196)]) by (repeat constructor; unfold zone; cbn; lia).
        destruct RES7 as [[_ ->]|(NE & _)]; [| exfalso; exact (NE E0)].
        eapply (g10_R usp S lo gp tp F fc GR);
          [ eapply rw_cells_transport; [apply AMC; [exact FR6 | left; lia] | exact MU8 | exact WM8 | cbn; lia]
          | apply save_zero_cells; eapply rw_cells_transport; [apply AMC; [| right; cbn; lia] | exact MU8 | exact WM8 | cbn; lia];
            eapply rw_cells_transport; [exact SAV5 | exact MU6 | exact WM6 | cbn; lia]
          | rewrite repeat_length; reflexivity | rewrite repeat_length; reflexivity
          | eapply stk_transport_disjoint; [exact ST7 | exact MU8 | exact WM8 | cbn; lia]
          | exact MI8 | lia |].
        eapply (rk_finish MD7 s7 BNone m8 (-3) h5 b4 _ ev7); cbn [cfg_extra cfg_tt cfg_l16 cfg_l4 app].
        + eapply inv_zone; [exact FW8 | exact MU8 | exact WM8 | exact INS | exact INV7].
        + exact VMO7.
        + exact VMk.
        + eapply aux_zone; [exact FW8 | exact MU8 | exact WM8 | exact AUX7].
        + eapply err_zone; [exact FW8 | exact MU8 | exact WM8 | exact ERR7].
        + eapply REST_munch; [exact FW8 | exact MU8 | exact WM8 |]. apply AMR. eapply REST_munch; [exact FW6 | exact MU6 | exact WM6 | exact REST5].
        + eapply rw_cells_transport; [| exact MU8 | exact WM8 | cbn; lia]. apply AMC; [exact HD6 | right; cbn; lia].
        + cbn. exact Hstrm0.
        + cbn. lia.
        + exact MID8.
        + cbn. exact E0.
        + cbn. exact L160.
        + cbn. exact L40.
        + eapply rw_cells_transport; [| exact MU8 | exact WM8 | cbn; lia]. apply AMC; [exact STRM6 | left; lia].
        + exact Eb4.
        + exact Hai4.
        + exact CTX.
        + exact I.
        + reflexivity.
        + left. reflexivity.
        + eapply pres_trans; [| eapply pres_zone; [exact FW8 | exact MU8 | exact WM8]]. apply AMP.
          eapply pres_trans; [exact PR5 | eapply pres_zone; [exact FW6 | exact MU6 | exact WM6]].
      - (* [comment removed for export] *)
        intros m8 NE MID8 MU8 WM8 MI8.
        assert (FW8 : Forall zone [(S + 3152, S + 3196)]) by (repeat constructor; unfold zone; cbn; lia).
        destruct RES7 as [[E0 _]|(_ & BO & (p1 & -> & NIP) & [jk BJ])]; [exfalso; exact (NE E0)|].
        apply evt_done. unfold PK.
        eapply (h14_finish (BFast (p1, r1, (uc5 - 48) * 400000)) (uc5 - 48) uc5 (skipn 4 pz) s7 m8 MD7 h5 b4 _ ev7);
          cbn [cfg_extra cfg_tt cfg_l16 cfg_l4 cfg_sizes_ok cfg_shape_ok app blk_addr blk_size blk_id fst snd].
        + eapply inv_zone; [exact FW8 | exact MU8 | exact WM8 | right; exact INS | exact INV7].
        + exact VMO7.
        + exact VMk.
        + eapply aux_zone; [exact FW8 | exact MU8 | exact WM8 | exact AUX7].
        + eapply err_zone; [exact FW8 | exact MU8 | exact WM8 | exact ERR7].
        + lia.
        + exact SM0.
        + exact I.
        + lia.
        + exact Ruc5.
        + exact PZ4.
        + intros bb [<-|[]]. exists jk. cbn [blk_addr blk_size fst snd].
          destruct (new_blocks (BFast (p1, r1, (uc5 - 48) * 400000)) s7 m7 MD7 INV7) as [NBs _].
          cps_pose (NBs _ ltac:(left; reflexivity)) as (_ & _ & _ & _ & _ & N6 & _). cbn [blk_addr blk_size fst snd] in N6. unfold disj, DSTATE_SIZE in N6.
          eapply rw_cells_transport; [exact BJ | exact MU8 | exact WM8 | cbn [disjoint_from cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by lia; lia].
        + eapply REST_munch; [exact FW8 | exact MU8 | exact WM8 |]. apply AMR. eapply REST_munch; [exact FW6 | exact MU6 | exact WM6 | exact REST5].
        + eapply stk_transport_disjoint; [exact ST7 | exact MU8 | exact WM8 | cbn; lia].
        + exact MI8.
        + unfold FRA. eapply rw_cells_transport; [apply AMC; [exact FR6 | left; lia] | exact MU8 | exact WM8 | cbn; lia].
        + eapply rw_cells_transport; [apply AMC; [| right; cbn; lia] | exact MU8 | exact WM8 | cbn; lia].
          eapply rw_cells_transport; [exact SAV5 | exact MU6 | exact WM6 | cbn; lia].
        + eapply rw_cells_transport; [| exact MU8 | exact WM8 | cbn; lia]. apply AMC; [exact HD6 | right; cbn; lia].
        + cbn. exact Hstrm0.
        + reflexivity.
        + reflexivity.
        + cbn. lia.
        + reflexivity.
        + cbn. lia.
        + cbn. lia.
        + cbn. lia.
        + cbn. lia.
        + cbn. lia.
        + cbn. lia.
        + cbn. lia.
        + cbn. lia.
        + cbn. lia.
        + cbn. lia.
        + exact MID8.
        + reflexivity.
        + cbn. exact L160.
        + cbn. exact L40.
        + exact RnI.
        + cbn. exact CC0.
        + eapply rw_cells_transport; [| exact MU8 | exact WM8 | cbn; lia]. apply AMC; [exact STRM6 | left; lia].
        + exact Eb4.
        + exact Hai4'.
        + eapply pres_trans; [| eapply pres_zone; [exact FW8 | exact MU8 | exact WM8]]. apply AMP.
          eapply pres_trans; [exact PR5 | eapply pres_zone; [exact FW6 | exact MU6 | exact WM6]]. }
    (* [comment removed for export] *)
    { intros m6 ya1 ya2 ya3 h5 SM1 FR6 HD6 STRM6 MU6 WM6 MI6. unfold MSm.
      assert (FW6 : Forall zone [(usp + -336, usp); (S, S + 68)]) by (repeat constructor; unfold zone; cbn; lia).
      apply evt_done. unfold PK.
      eapply DCV with (s := s) (LB := LB) (k := (1 + kcr)%nat) (n := (uc5 - 48) * 200000) (lo := lo) (B := B) (errv := errv);
        [ eapply inv_zone; [exact FW6 | exact MU6 | exact WM6 | exact INS | exact INV5]
        | exact VM2
        | eapply aux_zone; [exact FW6 | exact MU6 | exact WM6 | exact AUX5]
        | rewrite unsigned_lit by lia; lia
        | rewrite unsigned_lit by lia; eapply stk_transport_disjoint; [exact ST5 | exact MU6 | exact WM6 | cbn; lia]
        | exact LOC
        | rewrite unsigned_lit by lia; cbn [al_stack L S0_layout]; lia
        | eapply err_zone; [exact FW6 | exact MU6 | exact WM6 | exact ERR5]
        | exact MI6 | exact TP | reflexivity | unfold MAX_REQ_D; lia |].
      intros s7 LB7 m7 MD7 r1 z0 z1 z2 za1 za2 za3 za4 za5 za6 za7 z3 z4 z5 z6 ev7 INV7 VMO7 VMC7 MI7 ST7 ERR7 AUX7 HP7 RES7.
      rewrite unsigned_lit in ST7, HP7 by lia. rewrite ret_pc_lit by (lia || reflexivity).
      assert (SUB7 : forall bq, In bq LB -> In bq LB7) by (destruct RES7 as [[_ ->]|(_ & _ & (p1 & -> & _) & _)]; [intros bq H; exact H | intros bq H; right; exact H]).
      assert (IS7 : In (pS, S, 64144) LB7) by (apply SUB7; exact INS).
      cps_destruct (after_malloc LB LB7 m6 m7 HP7 INS (fun bq H => H)) as (AMR & AMP & AMC).
      assert (R01 : 0 <= r1 < 2 ^ 64).
      { destruct RES7 as [[-> _]|(_ & (B1 & _ & B3 & B4 & _) & _ & _)]; [lia|]. bz_ceil. lia. }
      (* [comment removed for export] *)
      assert (FR7 : FRA m7 j0 f8 f16 f24 f32 f40 f48 f56 f64 Z0 Z0 pb) by (unfold FRA; apply AMC; [exact FR6 | left; lia]).
      assert (HD7 : rw_cells s0segs m7 S (HEAD_CELLS h5)) by (apply AMC; [exact HD6 | right; cbn; lia]).
      assert (STRM7 : rw_cells s0segs m7 uspb (STRM_CELLS b4)) by (apply AMC; [exact STRM6 | left; lia]).
      assert (MID7 : rw_cells s0segs m7 (S + 3152) (MID_CELLS d0)).
      { apply AMC; [| right; cbn; lia]. eapply rw_cells_transport; [exact MID5 | exact MU6 | exact WM6 | cbn; lia]. }
      assert (SAV7 : rw_cells s0segs m7 (S + 64036) [CB 108 (repeat (Z_to_bv 8 0) 108)]).
      { apply AMC; [| right; cbn; lia]. eapply rw_cells_transport; [exact SAV5 | exact MU6 | exact WM6 | cbn; lia]. }
      assert (REST7 : REST m7) by (apply AMR; eapply REST_munch; [exact FW6 | exact MU6 | exact WM6 | exact REST5]).
      assert (PR7 : pres P10 m m7) by (apply AMP; eapply pres_trans; [exact PR5 | eapply pres_zone; [exact FW6 | exact MU6 | exact WM6]]).
      clear AMR AMP AMC FR6 HD6 STRM6 MU6 WM6 MI6 HP7.
      destruct (ai_inv_model AI INV7) as [Hh7 Hl7].
      eapply (evt_realizes s0segs (PK MD7)); [exact Hh7 | exact Hl7 | | intros ms' X; exact X].
      unfold FRA in FR7.
      eapply (g10_C2s usp S uspb lo gp tp F fc GC) with (h := h5) (b := b4) (d := d0) (n := uc5 - 48) (Q := PK MD7);
        [ exact FR7 | exact HD7 | reflexivity | lia | cbn; lia | cbn; lia | cbn; lia | cbn; lia
        | exact STRM7 | cbn; exact BZA | cbv delta [b1 b2 b3 b4]; cbn [bupd bs_src bs_len bs_ai bs_til bs_tih bs_q1 bs_dst bs_dlen bs_av bs_tol bs_toh bs_q2 bs_S bs_bzalloc bs_bzfree bs_opaque]; lia
        | exact MID7 | lia | lia | lia | exact R01 | exact MI7 |].
      intros m8 yb1 yb2 yb3 MID8 MU8 WM8 MI8.
      assert (FW8 : Forall zone [(S + 3152, S + 3196)]) by (repeat constructor; unfold zone; cbn; lia).
      (* [comment removed for export] *)
      apply evt_done. unfold PK.
      eapply DCV with (s := s7) (LB := LB7) (k := kcr) (n := (uc5 - 48) * 50000) (lo := lo) (B := B) (errv := ev7);
        [ eapply inv_zone; [exact FW8 | exact MU8 | exact WM8 | exact IS7 | exact INV7]
        | eapply ac_vm_le; [exact VMC7|]; unfold ac_cost; replace ((uc5 - 48) * 50000 <? 1024) with false by (symmetry; apply Z.ltb_ge; lia); lia
        | eapply aux_zone; [exact FW8 | exact MU8 | exact WM8 | exact AUX7]
        | rewrite unsigned_lit by lia; lia
        | rewrite unsigned_lit by lia; eapply stk_transport_disjoint; [exact ST7 | exact MU8 | exact WM8 | cbn; lia]
        | exact LOC
        | rewrite unsigned_lit by lia; cbn [al_stack L S0_layout]; lia
        | eapply err_zone; [exact FW8 | exact MU8 | exact WM8 | exact ERR7]
        | exact MI8 | exact TP | f_equal; lia | unfold MAX_REQ_D; lia |].
      intros s9 LB9 m9 MD9 r2 w0 w1 w2 wa1 wa2 wa3 wa4 wa5 wa6 wa7 w3 w4 w5 w6 ev9 INV9 VMO9 VMC9 MI9 ST9 ERR9 AUX9 HP9 RES9.
      rewrite unsigned_lit in ST9, HP9 by lia. rewrite ret_pc_lit by (lia || reflexivity).
      assert (SUB9 : forall bq, In bq LB7 -> In bq LB9) by (destruct RES9 as [[_ ->]|(_ & _ & (p2 & -> & _) & _)]; [intros bq H; exact H | intros bq H; right; exact H]).
      cps_destruct (after_malloc LB7 LB9 m8 m9 HP9 IS7 SUB7) as (AMR9 & AMP9 & AMC9).
      assert (R02 : 0 <= r2 < 2 ^ 64).
      { destruct RES9 as [[-> _]|(_ & (B1 & _ & B3 & B4 & _) & _ & _)]; [lia|]. bz_ceil. lia. }
      pose proof (vm_only_trans _ _ _ VMO7 VMO9) as VMO.
      (* [comment removed for export] *)
      assert (FR9 : FRA m9 j0 f8 f16 f24 f32 f40 f48 f56 f64 Z0 Z0 pb).
      { unfold FRA in *. apply AMC9; [| left; lia]. eapply rw_cells_transport; [exact FR7 | exact MU8 | exact WM8 | cbn; lia]. }
      assert (HD9 : rw_cells s0segs m9 S (HEAD_CELLS h5)).
      { apply AMC9; [| right; cbn; lia]. eapply rw_cells_transport; [exact HD7 | exact MU8 | exact WM8 | cbn; lia]. }
      assert (STRM9 : rw_cells s0segs m9 uspb (STRM_CELLS b4)).
      { apply AMC9; [| left; lia]. eapply rw_cells_transport; [exact STRM7 | exact MU8 | exact WM8 | cbn; lia]. }
      assert (MID9 : rw_cells s0segs m9 (S + 3152) (MID_CELLS (DSM (sm_tt d0) r1 (sm_ll4 d0) (sm_sbcrc d0) (sm_sccrc d0) (sm_cbcrc d0) (sm_cccrc d0) (sm_nInUse d0)))).
      { apply AMC9; [exact MID8 | right; cbn; lia]. }
      assert (SAV9 : rw_cells s0segs m9 (S + 64036) [CB 108 (repeat (Z_to_bv 8 0) 108)]).
      { apply AMC9; [| right; cbn; lia]. eapply rw_cells_transport; [exact SAV7 | exact MU8 | exact WM8 | cbn; lia]. }
      assert (REST9 : REST m9) by (apply AMR9; eapply REST_munch; [exact FW8 | exact MU8 | exact WM8 | exact REST7]).
      assert (PR9 : pres P10 m m9) by (apply AMP9; eapply pres_trans; [exact PR7 | eapply pres_zone; [exact FW8 | exact MU8 | exact WM8]]).
      assert (ST9' : stk s0segs m9 lo (usp + -336)) by exact ST9.
      clear AMR9 AMP9 AMC9 FR7 HD7 STRM7 MID8 MI8 MID7 SAV7.
      destruct (ai_inv_model AI INV9) as [Hh9 Hl9].
      eapply (evt_realizes s0segs (PK MD9)); [exact Hh9 | exact Hl9 | | intros ms' X; exact X].
      unfold FRA in FR9.
      eapply (g10_C3s usp S uspb lo gp tp F fc GC) with (r1 := r1) (r2 := r2) (Q := PK MD9);
        [ exact FR9 | exact MID9 | reflexivity | exact R01 | cbn; lia | cbn; lia | exact R02 | exact MI9 | | |]; cbv zeta.
      - (* [comment removed for export] *)
        intros m10 E1 MID10 MU10 WM10 MI10.
        assert (FW10 : Forall zone [(S + 3152, S + 3196)]) by (repeat constructor; unfold zone; cbn; lia).
        destruct RES7 as [[_ E7]|(NE & _)]; [| exfalso; exact (NE E1)]. subst LB7.
        eapply (g10_Rc usp S lo gp tp F fc GR);
          [ eapply rw_cells_transport; [exact FR9 | exact MU10 | exact WM10 | cbn; lia]
          | apply save_zero_cells; eapply rw_cells_transport; [exact SAV9 | exact MU10 | exact WM10 | cbn; lia]
          | rewrite repeat_length; reflexivity | rewrite repeat_length; reflexivity
          | eapply stk_transport_disjoint; [exact ST9' | exact MU10 | exact WM10 | cbn; lia]
          | exact MI10 | lia |].
        destruct RES9 as [[-> ->]|(_ & BO2 & (p2 & -> & NIP2) & [jk2 BJ2])].
        + (* [comment removed for export] *)
          eapply (rk_finish MD9 s9 BNone m10 (-3) h5 b4 _ ev9); cbn [cfg_extra cfg_tt cfg_l16 cfg_l4 app].
          * eapply inv_zone; [exact FW10 | exact MU10 | exact WM10 | exact INS | exact INV9].
          * exact VMO.
          * exact VMC9.
          * eapply aux_zone; [exact FW10 | exact MU10 | exact WM10 | exact AUX9].
          * eapply err_zone; [exact FW10 | exact MU10 | exact WM10 | exact ERR9].
          * eapply REST_munch; [exact FW10 | exact MU10 | exact WM10 | exact REST9].
          * eapply rw_cells_transport; [exact HD9 | exact MU10 | exact WM10 | cbn; lia].
          * cbn. exact Hstrm0.
          * cbn. lia.
          * exact MID10.
          * cbn; lia.
          * cbn. exact E1.
          * reflexivity.
          * eapply rw_cells_transport; [exact STRM9 | exact MU10 | exact WM10 | cbn; lia].
          * exact Eb4.
          * exact Hai4.
          * exact CTX.
          * exact I.
          * reflexivity.
          * left. reflexivity.
          * eapply pres_trans; [exact PR9 | eapply pres_zone; [exact FW10 | exact MU10 | exact WM10]].
        + (* [comment removed for export] *)
          cps_pose BO2 as (Q1 & Q2 & Q3 & Q4 & Q5). bz_ceil.
          eapply (rk_finish MD9 s9 (BHalf4 (p2, r2, (uc5 - 48) * 50000)) m10 (-3) h5 b4 _ ev9); cbn [cfg_extra cfg_tt cfg_l16 cfg_l4 app blk_addr blk_size fst snd].
          * eapply inv_zone; [exact FW10 | exact MU10 | exact WM10 | right; exact INS | exact INV9].
          * exact VMO.
          * exact VMC9.
          * eapply aux_zone; [exact FW10 | exact MU10 | exact WM10 | exact AUX9].
          * eapply err_zone; [exact FW10 | exact MU10 | exact WM10 | exact ERR9].
          * eapply REST_munch; [exact FW10 | exact MU10 | exact WM10 | exact REST9].
          * eapply rw_cells_transport; [exact HD9 | exact MU10 | exact WM10 | cbn; lia].
          * cbn. exact Hstrm0.
          * cbn. lia.
          * exact MID10.
          * cbn; lia.
          * cbn. exact E1.
          * reflexivity.
          * eapply rw_cells_transport; [exact STRM9 | exact MU10 | exact WM10 | cbn; lia].
          * exact Eb4.
          * exact Hai4.
          * destruct (new_blocks (BHalf4 (p2, r2, (uc5 - 48) * 50000)) s9 m9 MD9 INV9) as [NBs _].
            pose proof (NBs _ ltac:(left; reflexivity)) as NB2. cbn [blk_addr blk_size fst snd] in NB2.
            apply ctx_ok_ext; [exact CTX | lia | left; reflexivity | left; reflexivity | right; eapply NB_mono; [exact NB2 | lia] | intros X; exfalso; exact (X eq_refl)].
          * exact I.
          * split; [exact SM1 | reflexivity].
          * left. reflexivity.
          * eapply pres_trans; [exact PR9 | eapply pres_zone; [exact FW10 | exact MU10 | exact WM10]].
      - (* [comment removed for export] *)
        intros m10 NE1 E2 MID10 MU10 WM10 MI10.
        assert (FW10 : Forall zone [(S + 3152, S + 3196)]) by (repeat constructor; unfold zone; cbn; lia).
        destruct RES7 as [[E7 _]|(_ & BO1 & (p1 & E7 & NIP1) & [jk1 BJ1])]; [exfalso; exact (NE1 E7)|]. subst LB7.
        destruct RES9 as [[_ ->]|(NE2 & _)]; [| exfalso; exact (NE2 E2)].
        cps_pose BO1 as (Q1 & Q2 & Q3 & Q4 & Q5). bz_ceil.
        eapply (g10_R usp S lo gp tp F fc GR);
          [ eapply rw_cells_transport; [exact FR9 | exact MU10 | exact WM10 | cbn; lia]
          | apply save_zero_cells; eapply rw_cells_transport; [exact SAV9 | exact MU10 | exact WM10 | cbn; lia]
          | rewrite repeat_length; reflexivity | rewrite repeat_length; reflexivity
          | eapply stk_transport_disjoint; [exact ST9' | exact MU10 | exact WM10 | cbn; lia]
          | exact MI10 | lia |].
        eapply (rk_finish MD9 s9 (BHalf (p1, r1, (uc5 - 48) * 200000)) m10 (-3) h5 b4 _ ev9); cbn [cfg_extra cfg_tt cfg_l16 cfg_l4 app blk_addr blk_size fst snd].
        + eapply inv_zone; [exact FW10 | exact MU10 | exact WM10 | right; exact INS | exact INV9].
        + exact VMO.
        + exact VMC9.
        + eapply aux_zone; [exact FW10 | exact MU10 | exact WM10 | exact AUX9].
        + eapply err_zone; [exact FW10 | exact MU10 | exact WM10 | exact ERR9].
        + eapply REST_munch; [exact FW10 | exact MU10 | exact WM10 | exact REST9].
        + eapply rw_cells_transport; [exact HD9 | exact MU10 | exact WM10 | cbn; lia].
        + cbn. exact Hstrm0.
        + cbn. lia.
        + exact MID10.
        + cbn; lia.
        + reflexivity.
        + cbn. exact E2.
        + eapply rw_cells_transport; [exact STRM9 | exact MU10 | exact WM10 | cbn; lia].
        + exact Eb4.
        + exact Hai4.
        + destruct (new_blocks (BHalf (p1, r1, (uc5 - 48) * 200000)) s9 m9 MD9 INV9) as [NBs _].
          pose proof (NBs _ ltac:(left; reflexivity)) as NB1. cbn [blk_addr blk_size fst snd] in NB1.
          apply ctx_ok_ext; [exact CTX | lia | left; reflexivity | right; eapply NB_mono; [exact NB1 | lia] | left; reflexivity | intros _ X; exfalso; exact (X eq_refl)].
        + exact I.
        + split; [exact SM1 | reflexivity].
        + left. reflexivity.
        + eapply pres_trans; [exact PR9 | eapply pres_zone; [exact FW10 | exact MU10 | exact WM10]].
      - (* [comment removed for export] *)
        intros m10 NE1 NE2 MID10 MU10 WM10 MI10.
        assert (FW10 : Forall zone [(S + 3152, S + 3196)]) by (repeat constructor; unfold zone; cbn; lia).
        destruct RES7 as [[E7 _]|(_ & BO1 & (p1 & E7 & NIP1) & [jk1 BJ1])]; [exfalso; exact (NE1 E7)|]. subst LB7.
        destruct RES9 as [[E9 _]|(_ & BO2 & (p2 & -> & NIP2) & [jk2 BJ2])]; [exfalso; exact (NE2 E9)|].
        cps_pose BO1 as (Q1 & Q2 & Q3 & Q4 & Q5). bz_ceil.
        apply evt_done. unfold PK.
        eapply (h14_finish (BSmall (p2, r2, (uc5 - 48) * 50000) (p1, r1, (uc5 - 48) * 200000)) (uc5 - 48) uc5 (skipn 4 pz) s9 m10 MD9 h5 b4 _ ev9);
          cbn [cfg_extra cfg_tt cfg_l16 cfg_l4 cfg_sizes_ok cfg_shape_ok app blk_addr blk_size blk_id fst snd].
        + eapply inv_zone; [exact FW10 | exact MU10 | exact WM10 | right; right; exact INS | exact INV9].
        + exact VMO.
        + exact VMC9.
        + eapply aux_zone; [exact FW10 | exact MU10 | exact WM10 | exact AUX9].
        + eapply err_zone; [exact FW10 | exact MU10 | exact WM10 | exact ERR9].
        + lia.
        + exact SM1.
        + exact I.
        + lia.
        + exact Ruc5.
        + exact PZ4.
        + destruct (new_blocks (BSmall (p2, r2, (uc5 - 48) * 50000) (p1, r1, (uc5 - 48) * 200000)) s9 m9 MD9 INV9) as [NBs _].
          intros bb [<-|[<-|[]]]; cbn [blk_addr blk_size fst snd].
          * exists jk2. cps_pose (NBs _ ltac:(left; reflexivity)) as (_ & _ & _ & _ & _ & N6 & _). cbn [blk_addr blk_size fst snd] in N6. unfold disj, DSTATE_SIZE in N6.
            eapply rw_cells_transport; [exact BJ2 | exact MU10 | exact WM10 | cbn [disjoint_from cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by lia; lia].
          * exists jk1. cps_pose (NBs _ ltac:(right; left; reflexivity)) as (_ & _ & _ & _ & _ & N6 & _). cbn [blk_addr blk_size fst snd] in N6. unfold disj, DSTATE_SIZE in N6.
            eapply rw_cells_transport; [| exact MU10 | exact WM10 | cbn [disjoint_from cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by lia; lia].
            eapply heap_pres_rw_cells; [exact HP9 | | right; right; exists (p1, r1, (uc5 - 48) * 200000); split; [left; reflexivity| cbn; rewrite Nat.add_0_r, Z2Nat.id by lia; lia]].
            eapply rw_cells_transport; [exact BJ1 | exact MU8 | exact WM8 | cbn [disjoint_from cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by lia; lia].
        + eapply REST_munch; [exact FW10 | exact MU10 | exact WM10 | exact REST9].
        + eapply stk_transport_disjoint; [exact ST9' | exact MU10 | exact WM10 | cbn; lia].
        + exact MI10.
        + unfold FRA. eapply rw_cells_transport; [exact FR9 | exact MU10 | exact WM10 | cbn; lia].
        + eapply rw_cells_transport; [exact SAV9 | exact MU10 | exact WM10 | cbn; lia].
        + eapply rw_cells_transport; [exact HD9 | exact MU10 | exact WM10 | cbn; lia].
        + cbn. exact Hstrm0.
        + reflexivity.
        + reflexivity.
        + cbn. lia.
        + reflexivity.
        + cbn. lia.
        + cbn. lia.
        + cbn. lia.
        + cbn. lia.
        + cbn. lia.
        + cbn. lia.
        + cbn. lia.
        + cbn. lia.
        + cbn. lia.
        + cbn. lia.
        + exact MID10.
        + cbn; lia.
        + reflexivity.
        + reflexivity.
        + exact RnI.
        + cbn. exact CC0.
        + eapply rw_cells_transport; [exact STRM9 | exact MU10 | exact WM10 | cbn; lia].
        + exact Eb4.
        + exact Hai4'.
        + eapply pres_trans; [exact PR9 | eapply pres_zone; [exact FW10 | exact MU10 | exact WM10]]. }
  Qed.
End G10.

(* [comment removed for export] *)
Theorem S0F_dec10F : forall (AI : AllocIface s0segs S0_layout) (AC : AllocCover s0segs S0_layout AI),
  alloc_dcv_law s0segs S0_layout AI AC -> dec10F_spec AI AC.
Proof.
  intros AI AC DCV. unfold dec10F_spec. intros.
  eapply (main AI AC DCV); eassumption.
Qed.

End ACeilS1.
