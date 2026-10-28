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
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim StrFun STree Malloc Monad Stdio SjModel AtpModel ElModel Target Prog AtpImpl.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import Layout Exit Printf_wfile Sj_iface Sj_kit Sj_new Sj_new_t2 Sj_h_kit Sj_h_alloc Sj_h_create Sj_h_active Sj_h_bom Sj_h_pid_front F_memcpy F_memset.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Sj_h_arith.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjS1Out SjStage1 SjStage1Out SjTape SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require SjAlloc.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import Sj_stage2_iface Sj_h_parse Atp_pid Atp_pid0.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Sj_stage1_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import Atp_defs Atp_h_defs Atp_h_find El_defs El_hdr.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition doc_cap (d : list Z) : Z := Z.max (zlength (el_doc d)) 32.

Definition gate_post (sp0 : Z) (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra : word) (F : bvmap 5 word)
    (s : PState) (LB : list block) (lo B D : Z) (d : list Z) (m0 : mem) (bv : bptr) (A cap : Z) (jr : list byte)
    (psb ptp pim pix poc pia : bptr) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists x1 t0 t1 t2 xs0 a0 a1 a2 a3 a4 a5 a6 a7 xs3 xs5 xs8 t3 t4 t5 t6 F' fc' m' (errv' : word)
                    (IMPL IDX OC IA TAPE SBUF : Z) (r : word) (e P0 : Z) (j0 c32 c40 j48 j313 j329 j361 jr28 j416 j441 : list byte)
                    (vptr nsi nxt capv md bufv lenv docv : word) (b48 b49 : byte) (p12 p28 p50 : list byte),
    ms' = MS (mkR x1 (Z_to_bv 64 sp0) gp (Z_to_bv 64 RATP) t0 t1 t2 xs0 (Z_to_bv 64 (zlength (el_str d))) a0 a1 a2 a3 a4 a5 a6 a7
                  (Z_to_bv 64 P0) xs3 (Z_to_bv 64 e) xs5 (Z_to_bv 64 (el_action d)) (Z_to_bv 64 0xffffffc0) xs8 s9 s10 s11 t3 t4 t5 t6)
             F' (Z_to_bv 64 (if e =? 0 then 0x3c2bc else 0x3c270)) fc' None m' (seg_rom usegs)
    /\ nth 0 (el_els D d) (0, 0) = (P0, zlength (el_str d))
    /\ 0 <= e < 2^32 /\ (e = 0 <-> r = Z_to_bv 64 0)
    /\ frm0 fc'
    /\ mem_inv usegs m' /\ stk usegs m' lo sp0 /\ rw_cells usegs m' LX_ERRNO [C4 errv'] /\ rauxv_ok m' B
    /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
    /\ RHEAP s' ((pia, IA, 1024) :: (poc, OC, 8192) :: (pix, IDX, 4 * (roundup64 (doc_cap d) + 9)) :: (pim, IMPL, 96)
                 :: (ptp, TAPE, 8 * roundup64 (doc_cap d + 3)) :: (psb, SBUF, roundup64 (5 * (doc_cap d / 3) + 64)) :: (bv, A, 16 * cap) :: LB) m'
    /\ lx_pres LB (sp0 + 528) [LXW_SJ; LXW_UNW] m0 m' /\ sj_statics m' true /\ payload_ok m' LB D d
    /\ vrep m' (sp0 + 392) A (cap, Z.of_nat (el_P d), Some bv) (el_els D d) jr
    /\ rw_cells usegs m' (sp0 + 8) (res_cells (sp0 + 336) r jr28)
    /\ s2_okres TAPE SBUF (roundup64 (doc_cap d + 3)) (roundup64 (5 * (doc_cap d / 3) + 64)) r m'
    /\ rblock_range TAPE (8 * roundup64 (doc_cap d + 3)) /\ rblock_range SBUF (roundup64 (5 * (doc_cap d / 3) + 64))
    /\ rw_cells usegs m' (sp0 + 296) (if bv_eqb r (Z_to_bv 64 0) then [C8 (Z_to_bv 64 (sp0 + 336)); C8 (Z_to_bv 64 1)] else [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)])
    /\ rw_cells usegs m' (sp0 + 312) [C1 (Z_to_bv 8 0); CB 7 j313]
    /\ rw_cells usegs m' (sp0 + 320) [C8 (Z_to_bv 64 IMPL)]
    /\ rw_cells usegs m' (sp0 + 328) [C1 (Z_to_bv 8 0); CB 3 j329; C4 (Z_to_bv 64 12)]
    /\ rw_cells usegs m' (sp0 + 336) [C8 (Z_to_bv 64 TAPE); C8 (Z_to_bv 64 SBUF); C8 (Z_to_bv 64 (doc_cap d))]
    /\ rw_cells usegs m' (sp0 + 360) (p48_cells (Z_to_bv 8 0) j361 (Z_to_bv 64 0) (Z_to_bv 64 0))
    /\ rw_cells usegs m' IMPL (impl_cells16 vptr nsi p12 (Z_to_bv 64 IDX) nxt p28 capv md b48 b49 p50 (Z_to_bv 64 OC) (Z_to_bv 64 IA) bufv lenv docv)
    /\ vptr = Z_to_bv 64 SJ_DPI_VPTR
    /\ rw_cells usegs m' sp0 [CB 8 j0]
    /\ rw_cells usegs m' (sp0 + 32) [CB 8 c32; CB 8 c40]
    /\ rw_cells usegs m' (sp0 + 48) [CB 248 j48]
    /\ rw_cells usegs m' (sp0 + 416) [CB 4 j416; C4 (Z_to_bv 64 (el_sel d))]
    /\ rw_cells usegs m' (sp0 + 424) [C8 (Z_to_bv 64 (D + zlength d)); C8 (Z_to_bv 64 0); C1 (Z_to_bv 8 0); CB 7 j441]
    /\ rw_cells usegs m' (sp0 + 448) [C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Definition view_of (D : Z) (r : list Z) (P : Z) (x : list Z) : Prop :=
  (P = 0 /\ x = []) \/ (exists o : nat, P = D + 10 + Z.of_nat o /\ x = firstn (length x) (skipn o r) /\ (o + length x <= length r)%nat).

Lemma el_els_shape : forall D d, exists P0 P1 rest,
  el_els D d = (P0, zlength (el_str d)) :: (P1, zlength (el_s1 d)) :: rest /\ view_of D (el_rem d) P0 (el_str d) /\ view_of D (el_rem d) P1 (el_s1 d).
Proof.
  intros D d. unfold el_els, el_P, el_str, el_s1, el_parts.
  pose proof (poffs_length (el_rem d)) as PL. pose proof (poffs_parts (el_rem d)) as PP. pose proof (poffs_bound (el_rem d)) as PB.
  rewrite <- PP. rewrite <- PP in PL.
  assert (VW : forall o n, In (o, n) (poffs (el_rem d)) ->
            view_of D (el_rem d) (D + 10 + Z.of_nat o) (firstn n (skipn o (el_rem d))) /\ zlength (firstn n (skipn o (el_rem d))) = Z.of_nat n).
  { intros o n Hin. specialize (PB _ Hin). cbn [fst snd] in PB.
    assert (LN : length (firstn n (skipn o (el_rem d))) = n) by (rewrite firstn_length, length_skipn; lia).
    split; [| unfold zlength; rewrite LN; reflexivity]. right. exists o. rewrite LN. split; [reflexivity|]. split; [reflexivity| lia]. }
  destruct (poffs (el_rem d)) as [|[o0 n0] [|[o1 n1] tl]] eqn:EP.
  - cbn. exists 0, 0, []. split; [reflexivity|]. split; left; split; reflexivity.
  - destruct (VW o0 n0 ltac:(left; reflexivity)) as [V0 L0]. cbn [map nth length Nat.max Nat.sub repeat app pview fst snd].
    exists (D + 10 + Z.of_nat o0), 0, []. rewrite L0. split; [reflexivity|]. split; [exact V0| left; split; reflexivity].
  - destruct (VW o0 n0 ltac:(left; reflexivity)) as [V0 L0]. destruct (VW o1 n1 ltac:(right; left; reflexivity)) as [V1 L1].
    cbn [map nth app]. rewrite L0, L1. do 3 eexists. split; [reflexivity|]. split; [exact V0| exact V1].
Qed.

Lemma view_bytes : forall m LB D d P x, payload_ok m LB D d -> el_fd_ok d = true -> view_of D (el_rem d) P x -> x <> [] ->
  bytes_at usegs m P (to_bytes x) /\ Forall (fun c => 0 <= c < 256) x /\ exists b0, In b0 LB /\ blk_addr b0 <= P /\ P + zlength x <= blk_addr b0 + blk_size b0.
Proof.
  intros m LB D d P x PL FD VW NE. pose proof (el_rem_fd d FD) as [ER EL]. destruct PL as (PB & PRNG & D0 & DN & DLEN & PIN).
  destruct VW as [[_ E]|(o & -> & EX & BO)]; [congruence|].
  unfold el_fd_ok, EL_HDR in FD. apply Z.leb_le in FD. unfold zlength in FD, EL. rewrite ER in EX, BO. rewrite length_skipn in BO.
  split; [| split].
  - rewrite EX, to_bytes_firstn, to_bytes_skipn, to_bytes_skipn. apply bytes_at_firstn.
    replace (D + 10 + Z.of_nat o) with (D + Z.of_nat 10 + Z.of_nat o) by lia. apply bytes_at_skipn; [apply bytes_at_skipn; [exact PB|]|]; rewrite ?length_skipn, to_bytes_length; lia.
  - rewrite EX. apply Forall_firstn'. apply Forall_skipn'. apply Forall_skipn'. exact PRNG.
  - destruct PIN as [E0|(b0 & Hb & H1 & H2)]; [exfalso; rewrite E0 in FD; cbn in FD; lia|]. exists b0. split; [exact Hb|]. unfold zlength in *. lia.
Qed.

Ltac readdr H e := lazymatch type of H with rw_cells _ _ ?a _ => replace a with e in H by lia end.

Lemma bv_eqb_zero : forall r : word, bv_eqb r (Z_to_bv 64 0) = true <-> r = Z_to_bv 64 0.
Proof.
  intros r. unfold bv_eqb. rewrite Z.eqb_eq, (unsigned_lit 0) by lia.
  split; [intros H; apply bv_eq; rewrite (unsigned_lit 0) by lia; exact H| intros ->; apply unsigned_lit; lia].
Qed.

Definition res_post (x1 : word) (sp0 : Z) (gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s7 : word) (c : Z) (s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (lo : Z) (r : word) (jr : list byte) : machine_state -> Prop :=
  fun ms' => exists (a0 a1 : word) (e : Z) (m' : mem),
    ms' = MS (mkR x1 (Z_to_bv 64 sp0) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 e) s5 s6 s7 (Z_to_bv 64 c) s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 (if c =? 0 then 0x3c264 else 0x3c248)) fc None m' (seg_rom usegs)
    /\ 0 <= e < 2^32 /\ (e = 0 <-> r = Z_to_bv 64 0)
    /\ munch [(sp0 + 296, sp0 + 312)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m' /\ stk usegs m' lo sp0
    /\ rw_cells usegs m' (sp0 + 8) (res_cells (sp0 + 336) r jr)
    /\ rw_cells usegs m' (sp0 + 296) (if bv_eqb r (Z_to_bv 64 0) then [C8 (Z_to_bv 64 (sp0 + 336)); C8 (Z_to_bv 64 1)] else [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]).

Lemma res_copy_spec : forall (x1 gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 : word) (c : Z) (s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (sp0 lo : Z) (r : word) (jr : list byte),
  stk usegs m lo sp0 -> GLOBALS_TOP <= lo -> lo <= sp0 -> sp0 + 528 <= 2^64 -> mem_inv usegs m ->
  (r = Z_to_bv 64 0 \/ 1 <= bv_unsigned r < 64) -> (c = 0 \/ c = 1) ->
  rw_cells usegs m (sp0 + 8) (res_cells (sp0 + 336) r jr) ->
  rw_cells usegs m (sp0 + 296) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
  evt usegs (res_post x1 sp0 gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s7 c s9 s10 s11 t3 t4 t5 t6 F fc m lo r jr)
    (MS (mkR x1 (Z_to_bv 64 sp0) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 (Z_to_bv 64 c) s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x3c234) fc None m (seg_rom usegs)).
Proof.
  intros until jr. intros ST GLO LO SPH MI RR C01 SRET JEL. unfold GLOBALS_TOP in GLO.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  pose proof (munch_refl [(sp0 + 296, sp0 + 312)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  unfold res_cells in SRET. destruct (bv_eqb r (Z_to_bv 64 0)) eqn:ER0.
  -
    step. replace (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0) by reflexivity.
    step. zstep. if_cases KG; zify_cond KG; [exfalso; lia|].
    zstep. if_cases KQ; zify_cond KQ; try (exfalso; lia). step. step. hstep. hstep.
    destruct C01 as [-> | ->]; zstep; if_cases KC; zify_cond KC; try (exfalso; lia);
    (apply evt_done; unfold res_post; do 2 eexists; exists 0; eexists;
     split; [cbv delta [mkR]; reflexivity|]; split; [lia|]; split; [split; intros _; [apply bv_eqb_zero; exact ER0| reflexivity]|];
     repeat (split; [eassumption|]); unfold res_cells; rewrite ER0; split; assumption).
  -
    assert (RNZ : r <> Z_to_bv 64 0) by (intros E; apply bv_eqb_zero in E; congruence).
    destruct RR as [E|RR]; [exfalso; exact (RNZ E)|].
    step. replace (sx32 r) with (Z_to_bv 64 (bv_unsigned r)) by (unfold sx32; f_equal; symmetry; apply a_swrap32_small; lia).
    step. zstep. if_cases KG; zify_cond KG; [exfalso; lia|].
    zstep. if_cases KQ; zify_cond KQ; [exfalso; lia|].
    destruct C01 as [-> | ->]; zstep; if_cases KC; zify_cond KC; try (exfalso; lia);
    (apply evt_done; unfold res_post; do 2 eexists; exists (bv_unsigned r); eexists; rewrite Z_to_bv_bv_unsigned;
     split; [cbv delta [mkR]; reflexivity|]; split; [lia|]; split; [split; intros E; exfalso; [lia| exact (RNZ E)]|];
     repeat (split; [eassumption|]); unfold res_cells; destruct (bv_eqb r (Z_to_bv 64 0)) eqn:ER1;
     [exfalso; apply RNZ; apply bv_eqb_zero; exact ER1| split; assumption]).
Qed.

Section Proofs.
  Hypothesis HM : rmalloc_stmt.
  Hypothesis HF : rfree_stmt.
  Hypothesis S2 : stage2t_stmt.

  Lemma lftoi_parse_cps : forall {R} (k : bptr -> bptr -> bptr -> bptr -> bptr -> bptr -> M PState R) (Q : R -> PState -> machine_state -> Prop)
      (x1 gp t0 t1 t2 xs0 xs1 a1 a2 a3 a4 a5 a6 a7 xs2 xs3 xs4 xs5 xs7 xs8 s9 s10 s11 t3 t4 t5 t6 : word) (s0 s1 s2 s3 s4 s5 s6 s7 s8 ra : word)
      (F : bvmap 5 word) (fc : bv 32) (m0 m : mem) (s00 s : PState) (LB : list block) (sp0 lo B D : Z) (d : list Z) (init : bool) (errv : word)
      (A cap : Z) (bv : bptr) (jr : list byte) (j0 c8 c16 c24 c32 c40 j48 jel jpa j416 j441 : list byte),

    RHEAP s00 LB m0 -> lx_statics m0 ->

    RHEAP s ((bv, A, 16 * cap) :: LB) m -> rauxv_ok m B -> sp0 + 528 <= B -> B < 2^62 ->
    stk usegs m lo sp0 -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= sp0 + 528 - LX_FUZZ_STACK ->
    rw_cells usegs m LX_ERRNO [C4 errv] -> mem_inv usegs m -> (sp0 + 528) mod 16 = 0 -> frm0 fc ->
    ps_fa s = ps_fa s00 -> ps_so s = ps_so s00 ->
    vrep m (sp0 + 392) A (cap, Z.of_nat (el_P d), Some bv) (el_els D d) jr -> cap < 2^26 ->
    lx_pres LB (sp0 + 528) [LXW_SJ; LXW_UNW] m0 m -> sj_statics m init -> payload_ok m LB D d -> el_fd_ok d = true ->
    rw_cells usegs m sp0 [CB 8 j0] ->
    rw_cells usegs m (sp0 + 8) [CB 8 c8; CB 8 c16; CB 8 c24; CB 8 c32; CB 8 c40] ->
    rw_cells usegs m (sp0 + 48) [CB 248 j48] ->
    rw_cells usegs m (sp0 + 296) [CB 16 jel] ->
    rw_cells usegs m (sp0 + 312) [CB 80 jpa] ->
    rw_cells usegs m (sp0 + 416) [CB 4 j416; C4 (Z_to_bv 64 (el_sel d))] ->
    rw_cells usegs m (sp0 + 424) [C8 (Z_to_bv 64 (D + zlength d)); C8 (Z_to_bv 64 0); C1 (Z_to_bv 8 0); CB 7 j441] ->
    rw_cells usegs m (sp0 + 448) [C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    (forall psb ptp pim pix poc pia s' ms',
        gate_post sp0 gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra F s00 LB lo B D d m0 bv A cap jr psb ptp pim pix poc pia s' ms' ->
        implM usegs (k psb ptp pim pix poc pia) s' Q ms') ->
    implM usegs
      (mbind (if zlength (el_s1 d) <=? 1048512 then mbind (newnt lops (zlength (el_s1 d) + 64)) (fun p => mret (Some p)) else mret None) (fun cpo =>
       mbind (newnt lops (roundup64 (5 * (Z.max (zlength (el_doc d)) 32 / 3) + 64))) (fun sb =>
       mbind (newnt lops (8 * roundup64 (Z.max (zlength (el_doc d)) 32 + 3))) (fun tp =>
       mbind (newnt lops 96) (fun im =>
       mbind (newnt lops (4 * (roundup64 (Z.max (zlength (el_doc d)) 32) + 9))) (fun ix =>
       mbind (newnt lops 8192) (fun oc =>
       mbind (newnt lops 1024) (fun ia =>
       mbind (parse_model (SjAlloc.strip_bom (el_doc d))) (fun _ =>
       mbind (match cpo with Some p => del lops p | None => mret tt end) (fun _ => k sb tp im ix oc ia))))))))))
      s Q
      (MS (mkR x1 (Z_to_bv 64 sp0) gp (Z_to_bv 64 RATP) t0 t1 t2 xs0 xs1 (Z_to_bv 64 A) a1 a2 a3 a4 a5 a6 a7 xs2 xs3 xs4 xs5
               (Z_to_bv 64 (el_action d)) xs7 xs8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x3c158) fc None m (seg_rom usegs)).
  Proof.
    intros until j441.
    intros HEAP00 LXS0 HEAP AUX QB B63 ST CEIL GLO LO ERR MI AL16 FRM FA SO VR CAPB PRES SJS PL FD J0 SCR J48 JEL JPA XSEL XFD SAVE HK.
    unfold LX_FUZZ_STACK, SJ_CLIENT_FRAMES, RMALLOC_STACK, GLOBALS_TOP in *.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof CEIL as CEIL'. unfold OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in CEIL; try (pose proof alloc_ceiling_range as CEIL_RANGE__).
    assert (ELX : LX_ERRNO = 980196) by reflexivity. rewrite ELX in ERR.
    pose proof PL as (PB & PRNG & D0 & DN & DLEN & PIN).
    assert (ZD : zlength d = Z.of_nat (length d)) by reflexivity. pose proof DLEN as DLEN'. change (2^26) with 67108864 in DLEN'.
    assert (LBL : length (to_bytes d) = length d) by apply to_bytes_length.
    pose proof (el_rem_fd d FD) as [ER EL].
    pose proof (el_s1_len d) as S1L. pose proof (el_str_len d) as S0L.
    pose proof (el_doc_len d) as [DCL DCP]. unfold SJ_PADMAX in DCP.
    remember (zlength (el_s1 d)) as len1 eqn:Elen1.
    assert (LEN1 : 0 <= len1 <= zlength d) by (subst len1; unfold zlength in *; lia).
    assert (LEN0 : 0 <= zlength (el_str d) <= zlength d) by (unfold zlength in *; lia).

    apply (rw_cells_split_CB usegs _ _ [] 80 jpa [] [1;7; 8; 1;3;4; 8;8;8; 8;1;7;8;8]%nat) in JPA; [|reflexivity]. cbn [mk_CB_cells app] in JPA.
    set (j313 := take 7 (drop 1 jpa)) in JPA. set (j329 := take 3 (drop 1 (drop 8 (drop 7 (drop 1 jpa))))) in JPA.
    set (j361 := take 7 (drop 1 (drop 8 (drop 8 (drop 8 (drop 8 (drop 4 (drop 3 (drop 1 (drop 8 (drop 7 (drop 1 jpa)))))))))))) in JPA.
    apply (rw_cells_split_CB usegs _ _ [CB 8 c8; CB 8 c16] 8 c24 [CB 8 c32; CB 8 c40] [4;4]%nat) in SCR; [|reflexivity]. cbn [mk_CB_cells app] in SCR.
    destruct (rw_cells_split_at1 _ _ _ 4%nat SCR) as [RES SCR2]. cbn [firstn skipn cells_size csize Nat.add] in RES, SCR2. clear SCR. readdr SCR2 (sp0 + 32).
    apply (rw_cells_split_CB usegs _ _ [] 16 jel [] [8;8]%nat) in JEL; [|reflexivity]. cbn [mk_CB_cells app] in JEL.

    destruct (el_els_shape D d) as (P0 & P1 & rest & EE & VW0 & VW1). rewrite <- Elen1 in EE. rewrite EE in VR.
    destruct VR as (ELS & SZ & SV & BLK). pose proof BLK as BLK'. unfold vblk in BLK'. destruct BLK' as (BE & BJ & BR & CAP1).
    pose proof (el_P_ge2 d) as PGE2. assert (CAP2 : 2 <= cap) by (clear - SZ PGE2; lia).
    pose proof BR as (A0 & _ & _ & AC & AS). unfold OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in AC.
    destruct (rw_cells_split_at1 _ _ _ 4%nat BE) as [BE4 BER]. cbn [velts fst snd firstn skipn cells_size csize Nat.add] in BE4, BER.
    change (firstn 0 (velts rest)) with (@nil cell) in BE4. hide BER.
    assert (P0R : 0 <= P0 < 2^64) by (destruct VW0 as [[-> _] | (o & -> & _ & BO)]; [lia| rewrite ER, length_skipn in BO; lia]).
    assert (P1R : 0 <= P1 < 2^64) by (destruct VW1 as [[-> _] | (o & -> & _ & BO)]; [lia| rewrite ER, length_skipn in BO; lia]).
    assert (BLB : forall a, in_block LB a -> a < alloc_ceiling).
    { intros a (b & Hb & Hr). pose proof (LH_block_range _ _ _ _ HEAP ltac:(right; exact Hb)) as (_ & _ & _ & BC & _).
      unfold OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in BC. lia. }
    assert (CLI : forall a, 0 <= a < 2^64 -> lx_client LB (sp0 + 528) [LXW_SJ; LXW_UNW] a -> outside [(sp0, sp0 + 528)] a).
    { intros a Ha [HX HC]. cbn [outside]. split; [| exact I]. destruct HC as [HC|[HC|HC]]; [lia| specialize (BLB a HC); lia| lia]. }
    pose proof (munch_refl [(sp0, sp0 + 528)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
    hide BJ. hide BE.
    unfold implM. iprefix.

    step. step. step. step.

    hstep. hstep. hstep. zstep. hstep. hstep. hstep. hstep. zstep. zstep. hstep. hstep. hstep. hstep. step. hstep. hstep.

    step. if_cases KG; zify_cond KG; [exfalso; lia|].
    step. step. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.

    destruct (rw_cells_split_at1 _ _ _ 2%nat JPA) as [PA0 Q1]. cbn [firstn skipn cells_size csize Nat.add] in PA0, Q1.
    destruct (rw_cells_split_at1 _ _ _ 1%nat Q1) as [PIMPL Q2]. cbn [firstn skipn cells_size csize Nat.add] in PIMPL, Q2.
    destruct (rw_cells_split_at1 _ _ _ 3%nat Q2) as [PA16 Q3]. cbn [firstn skipn cells_size csize Nat.add] in PA16, Q3.
    destruct (rw_cells_split_at1 _ _ _ 3%nat Q3) as [DOCC P48]. cbn [firstn skipn cells_size csize Nat.add] in DOCC, P48.
    clear JPA Q1 Q2 Q3.
    readdr PIMPL (sp0 + 312 + 8). readdr PA16 (sp0 + 328). readdr DOCC (sp0 + 312 + 24). readdr P48 (sp0 + 312 + 48).

    pose proof (agree_on_of_munch _ _ _ MU WM) as AG1.
    assert (HEAP1 : RHEAP s ((bv, A, 16 * cap) :: LB) m1).
    { eapply LH_frame; [exact HEAP| exact MU| exact WM|]. constructor; [apply W_ok_stack; cbn; lia| constructor]. }
    assert (AUX1 : rauxv_ok m1 B).
    { eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
    assert (PRES1 : lx_pres LB (sp0 + 528) [LXW_SJ; LXW_UNW] m0 m1).
    { eapply lx_pres_trans; [exact PRES|]. eapply lx_pres_of_munch; [exact MU| exact WM| exact CLI]. }
    assert (SJS1 : sj_statics m1 init).
    { eapply sj_statics_agree; [exact AG1| | exact SJS]. intros a Ha. unfold sjs_addr, SJ_STATICS_LO, SJ_STATICS_HI in Ha. cbn [outside]; split; [lia| exact I]. }
    assert (PL1 : payload_ok m1 LB D d).
    { eapply payload_ok_agree; [exact AG1| exact PL|]. intros b a Hb Ha. pose proof (LH_block_range _ _ _ _ HEAP00 Hb) as (_ & _ & _ & BC & _).
      unfold OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in BC. cbn [outside]. split; [lia| exact I]. }
    assert (LXS1 : lx_statics m1).
    { eapply lx_statics_agree; [exact (agree_of_lx_pres _ _ _ _ _ PRES1)| | exact LXS0]. intros a Ha. apply lxs_addr_client; [exact Ha|].
      pose proof (lxs_addr_lt a Ha) as [R1 _]. unfold GLOBALS_TOP in R1. unfold LXW_SJ, LXW_UNW, SJ_STATICS_LO, SJ_STATICS_HI. cbn [rin_ivs fst snd].
      unfold lxs_addr, LX_GOT_STDERR, LX_STDERR_PTR, SJ_GOT_NOTHROW, SJ_IMPL_VT24, SJ_DPI_VPTR in Ha.
      clear - Ha. lia. }
    pose proof LXS1 as (_ & _ & GOT1 & VT241 & VTD1 & _ & _).
    unhide BJ. unhide BER.
    apply (vblk_agree _ _ _ _ _ _ _ _ _ AG1) in BLK; [| intros a _ Ha; cbn [outside]; clear - Ha AC CEIL LO; lia| exact ELS| lia].
    clear BJ BER BE MU WM AG1.
    step. if_cases KB; zify_cond KB.
    -
      assert (EDOC : el_doc d = []) by (unfold el_doc; rewrite <- Elen1; replace (len1 <=? SJ_PADMAX) with false by (symmetry; apply Z.leb_gt; unfold SJ_PADMAX; lia); reflexivity).
      replace (len1 <=? 1048512) with false by (symmetry; apply Z.leb_gt; lia).
      assert (CAPD : doc_cap d = 32) by (unfold doc_cap; rewrite EDOC; reflexivity).
      rewrite EDOC. change (zlength (@nil Z)) with 0.

      step. step. step. step. step. step. step. step. step.
      replace (Z_to_bv 64 (sp0 + 336)) with (Z_to_bv 64 (sp0 + 312 + 24)) by (f_equal; lia).
      ihere. to_implM. apply implM_ret_bind.
      eapply (pid_front_cps HM) with (B := B) (lo := lo) (SRET := sp0 + 8) (PARSER := sp0 + 312) (init := init);
        [exact HEAP1| exact AUX1| lia| exact ST| exact CEIL'| unfold GLOBALS_TOP; lia| unfold SJ_OPNEW_STACK, RMALLOC_STACK; lia
        | rewrite ELX; eassumption| assumption| lia| lia| lia| lia
        | exact (conj GOT1 (conj VT241 VTD1))| exact SJS1| exact PIMPL| exact DOCC| exact P48|].
      intros psb ptp pim pix poc pia st2 ms2 MID.
      eapply pid_null_cps with (B := B) (lo := lo);
        [exact MID| exact HEAP1| exact FRM| lia| (clear - B63; lia)| exact CEIL'| unfold GLOBALS_TOP; lia| unfold SJ_S2_STACK, SJ_S2_FRAMES, RMALLOC_STACK; lia| lia
        | lia| lia| lia| clear - AL16; replace (sp0 + 312) with (sp0 + 528 + (-27) * 8) by lia; rewrite Z.mod_add by lia; apply mod8_of_mod16; exact AL16| exact RES|].
      intros st3 ms3 (IMPL & IDX & OC & IA & TAPE & SBUF & PO). unfold hpostF in PO.
      destruct PO as (u5 & u6 & u7 & u10 & u11 & u12 & u13 & u14 & u15 & u16 & u17 & u28 & u29 & u30 & u31 & F' & fc' & m3
                      & -> & FRM3 & MI3 & ST3 & (errv3 & ERR3) & AUX3 & FA3 & SO3 & RR).
      unfold pidn_R in RR.
      destruct RR as (HEAP3 & PRES13 & SJRO3 & SJS3 & PIMPL3 & DOCC3 & P483 & (r & SRET3 & OKR) & (vptr & nsi & p12 & nxt & p28 & capv & md & b48 & b49 & p50 & bufv & lenv & docv & THIS3 & EVP) & BRTP & BRSB).
      replace (ret_pc (Z_to_bv 64 0x3c234)) with (Z_to_bv 64 0x3c234) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      apply implM_ret_bind. apply implM_ret_bind.

      pose proof (agree_of_lx_pres _ _ _ _ _ PRES13) as AG13.
      assert (FRCL : forall a, sp0 <= a < sp0 + 528 -> ~ (sp0 + 8 <= a < sp0 + 32) -> ~ (sp0 + 320 <= a < sp0 + 328) -> ~ (sp0 + 336 <= a < sp0 + 360) ->
                lx_client ((bv, A, 16 * cap) :: LB) sp0 (pid_front_X (sp0 + 312) ++ pidn_X (sp0 + 8)) a).
      { intros a Ha N1 N2 N3. split; [| left; lia]. unfold pid_front_X, pidn_X, LXW_SJ, SJ_STATICS_LO, SJ_STATICS_HI. cbn [app rin_ivs fst snd]. clear - Ha N1 N2 N3 GLO LO. lia. }
      apply (rw_cells_agree _ _ _ _ _ AG13) in PA0; [| intros a Ha; cbn in Ha; apply FRCL; lia].
      apply (rw_cells_agree _ _ _ _ _ AG13) in PA16; [| intros a Ha; cbn in Ha; apply FRCL; lia].
      apply (rw_cells_agree _ _ _ _ _ AG13) in J0; [| intros a Ha; cbn in Ha; apply FRCL; lia].
      apply (rw_cells_agree _ _ _ _ _ AG13) in SCR2; [| intros a Ha; cbn in Ha; apply FRCL; lia].
      apply (rw_cells_agree _ _ _ _ _ AG13) in J48; [| intros a Ha; cbn in Ha; apply FRCL; lia].
      apply (rw_cells_agree _ _ _ _ _ AG13) in JEL; [| intros a Ha; cbn in Ha; apply FRCL; lia].
      apply (rw_cells_agree _ _ _ _ _ AG13) in XSEL; [| intros a Ha; cbn in Ha; apply FRCL; lia].
      apply (rw_cells_agree _ _ _ _ _ AG13) in XFD; [| intros a Ha; cbn in Ha; apply FRCL; lia].
      apply (rw_cells_agree _ _ _ _ _ AG13) in SAVE; [| intros a Ha; cbn in Ha; apply FRCL; lia].
      apply (rw_cells_agree _ _ _ _ _ AG13) in SV; [| intros a Ha; cbn in Ha; apply FRCL; lia].
      assert (BKCL : forall a, A <= a < A + 16 * cap -> lx_client ((bv, A, 16 * cap) :: LB) sp0 (pid_front_X (sp0 + 312) ++ pidn_X (sp0 + 8)) a).
      { intros a Ha. split; [| right; left; exists (bv, A, 16 * cap); split; [left; reflexivity| cbn [blk_addr blk_size fst snd]; lia]].
        unfold pid_front_X, pidn_X, LXW_SJ, SJ_STATICS_LO, SJ_STATICS_HI. cbn [app rin_ivs fst snd]. clear - Ha AC AS A0 CEIL LO. lia. }
      apply (vblk_agree _ _ _ _ _ _ _ _ _ AG13) in BLK; [| intros a _ Ha; apply BKCL; exact Ha| exact ELS| lia].
      assert (PL3 : payload_ok m3 LB D d).
      { eapply payload_ok_agree; [exact AG13| exact PL1|]. intros b a Hb Ha. pose proof (LH_block_range _ _ _ _ HEAP00 Hb) as (_ & _ & _ & BC & BS).
        unfold OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in BC. split; [| right; left; exists b; split; [right; exact Hb| exact Ha]].
        unfold pid_front_X, pidn_X, LXW_SJ, SJ_STATICS_LO, SJ_STATICS_HI. cbn [app rin_ivs fst snd]. clear - Ha BC BS CEIL LO. lia. }
      assert (PRES3 : lx_pres LB (sp0 + 528) [LXW_SJ; LXW_UNW] m0 m3).
      { eapply lx_pres_trans; [exact PRES1|]. eapply (lx_pres_sub LB (sp0 + 528) _ _ _ _ _ _ PRES13); [lia| intros b0 Hb0; right; exact Hb0|].
        intros a Ha NX. unfold pid_front_X, pidn_X, LXW_SJ, LXW_UNW, SJ_STATICS_LO, SJ_STATICS_HI in Ha, NX. cbn [app rin_ivs fst snd] in Ha, NX.
        split; [clear - Ha NX LO GLO; lia|]. split; [intros IB; specialize (BLB a IB); clear - Ha NX BLB CEIL LO; lia| clear - Ha NX LO GLO; lia]. }
      rewrite <- CAPD in HEAP3, OKR, BRTP, BRSB, DOCC3. replace (sp0 + 312 + 24) with (sp0 + 336) in SRET3 by lia.
      readdr PIMPL3 (sp0 + 320). readdr DOCC3 (sp0 + 336). readdr P483 (sp0 + 360).
      clear AG13 FRCL BKCL PRES13 MID HEAP1 AUX1 PRES1 SJS1 PL1 LXS1 GOT1 VT241 VTD1 PIMPL DOCC P48 ERR MI.
      rewrite ELX in ERR3.

      pose proof BRTP as (TP0 & _ & _ & TPC & _). pose proof BRSB as (SB0 & _ & _ & SBC & _). unfold OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in TPC, SBC.
      pose proof (LH_block_range _ _ _ _ HEAP3 ltac:(do 3 right; left; reflexivity)) as BRIM. cbn [blk_addr blk_size fst snd] in BRIM.
      pose proof BRIM as (IM0 & _ & _ & IMC & _). unfold OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in IMC.
      assert (OKRR : r = Z_to_bv 64 0 \/ 1 <= bv_unsigned r < 64) by (destruct OKR as [K|[K _]]; [right; exact K| left; exact K]).
      hide THIS3.
      pose proof (munch_refl [(sp0 + 296, sp0 + 312)]%Z m3) as MU. pose proof (wmono_refl usegs m3) as WM.
      unfold implM. iprefix.
      eapply evt_cut; [eapply res_copy_spec; [exact ST3| unfold GLOBALS_TOP; lia| lia| lia| exact MI3| exact OKRR| right; reflexivity| exact SRET3| exact JEL]|].
      cbv beta. intros ms4 PO. destruct PO as (a0' & a1' & e & m4 & -> & HE & EIFF & MU4 & WM4 & MI4 & ST4 & SRET4 & ELEM4).
      clear SRET3 JEL MU WM. transport_after_call usegs m3 m4 MU4 WM4.
      unhide THIS3.
      pose proof (agree_on_of_munch _ _ _ MU4 WM4) as AG4.
      apply (rw_cells_agree _ _ _ _ _ AG4) in THIS3; [| intros a Ha; unfold impl_cells16 in Ha; cbn in Ha; cbn [outside]; clear - Ha IMC CEIL LO; lia].
      apply (vblk_agree _ _ _ _ _ _ _ _ _ AG4) in BLK; [| intros a _ Ha; cbn [outside]; clear - Ha AC CEIL LO; lia| exact ELS| lia].
      apply (s2_okres_agree _ _ _ _ _ _ _ _ AG4) in OKR; [| intros a Ha; cbn [outside]; clear - Ha TPC CEIL LO; lia| intros a Ha; cbn [outside]; clear - Ha SBC CEIL LO; lia].
      assert (SJS4 : sj_statics m4 true).
      { eapply sj_statics_agree; [exact AG4| | exact SJS3]. intros a Ha. pose proof (sjs_addr_lt a Ha) as [R1 _]. unfold GLOBALS_TOP in R1. cbn [outside]. clear - R1 GLO LO. lia. }
      assert (PL4 : payload_ok m4 LB D d).
      { eapply payload_ok_agree; [exact AG4| exact PL3|]. intros b a Hb Ha.
        assert (BA : a < alloc_ceiling) by (apply BLB; exists b; split; [exact Hb| exact Ha]). cbn [outside]. clear - BA CEIL LO. lia. }
      assert (PRES4 : lx_pres LB (sp0 + 528) [LXW_SJ; LXW_UNW] m0 m4).
      { eapply lx_pres_trans; [exact PRES3|]. eapply lx_pres_of_munch; [exact MU4| exact WM4|].
        intros a Ha HC. pose proof (CLI a Ha HC) as OU. cbn [outside] in OU |- *. clear - OU. lia. }
      assert (HEAP4 : RHEAP st3 ((pia, IA, 1024) :: (poc, OC, 8192) :: (pix, IDX, 4 * (roundup64 (doc_cap d) + 9)) :: (pim, IMPL, 96)
                 :: (ptp, TAPE, 8 * roundup64 (doc_cap d + 3)) :: (psb, SBUF, roundup64 (5 * (doc_cap d / 3) + 64)) :: (bv, A, 16 * cap) :: LB) m4).
      { eapply LH_frame; [exact HEAP3| exact MU4| exact WM4|]. constructor; [apply W_ok_stack; cbn; lia| constructor]. }
      assert (AUX4 : rauxv_ok m4 B).
      { eapply rauxv_ok_frame; [exact AUX3| exact MU4| exact WM4|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
      clear AG4 MU4 WM4.

      change (if 1 =? 0 then 0x3c264 else 0x3c248) with 0x3c248.
      destruct (Z.eq_dec e 0) as [E0|E0];
        step; if_cases KS; zify_cond KS; rewrite ?unsigned_lit in KS by lia; try (exfalso; lia).
      1: step; replace (Z_to_bv 64 0x3c2bc) with (Z_to_bv 64 (if e =? 0 then 0x3c2bc else 0x3c270)) by (rewrite E0; reflexivity).
      2: replace (Z_to_bv 64 0x3c270) with (Z_to_bv 64 (if e =? 0 then 0x3c2bc else 0x3c270)) by (replace (e =? 0) with false by (symmetry; apply Z.eqb_neq; exact E0); reflexivity).
      all: ihere; to_implM; apply HK; unfold gate_post.
      all: do 20 eexists; exists F', fc', m4, errv3, IMPL, IDX, OC, IA, TAPE, SBUF, r, e, P0; do 10 eexists; exists vptr, nsi, nxt, capv, md, bufv, lenv, docv, b48, b49, p12, p28, p50.
      all: split; [cbv delta [mkR]; reflexivity|]. all: split; [rewrite EE; reflexivity|]. all: split; [exact HE|]. all: split; [exact EIFF|]. all: split; [exact FRM3|].
      all: split; [exact MI4|]. all: split; [exact ST4|]. all: split; [exact ERR3|]. all: split; [exact AUX4|]. all: split; [congruence|]. all: split; [congruence|].
      all: split; [exact HEAP4|]. all: split; [exact PRES4|]. all: split; [exact SJS4|]. all: split; [exact PL4|].
      all: split; [rewrite EE; split; [exact ELS|]; split; [exact SZ|]; split; [exact SV| exact BLK]|].
      all: split; [exact SRET4|]. all: split; [exact OKR|]. all: split; [exact BRTP|]. all: split; [exact BRSB|]. all: split; [exact ELEM4|].
      all: split; [exact PA0|]. all: split; [exact PIMPL3|]. all: split; [exact PA16|]. all: split; [exact DOCC3|]. all: split; [exact P483|]. all: split; [exact THIS3|]. all: split; [exact EVP|].
      all: split; [exact J0|]. all: split; [exact SCR2|]. all: split; [exact J48|]. all: split; [exact XSEL|]. all: split; [exact XFD| exact SAVE].
    -
      assert (EDOC : el_doc d = el_s1 d) by (unfold el_doc; rewrite <- Elen1; replace (len1 <=? SJ_PADMAX) with true by (symmetry; apply Z.leb_le; unfold SJ_PADMAX; lia); reflexivity).
      replace (len1 <=? 1048512) with true by (symmetry; apply Z.leb_le; lia).
      rewrite EDOC, <- Elen1.
      unfold SJ_GOT_NOTHROW, SJ_NOTHROW_TAG in GOT1. unfold MallocRep.wz in GOT1.

      step. zstep. step. step. step.
      ihere. to_implM. apply implM_bind_assoc.
      eapply implM_bind.
      { eapply (opnew_arr_nt_proof HM) with (B := B) (lo := lo);
          [exact HEAP1| exact AUX1| lia| exact ST| exact CEIL'| unfold SJ_OPNEW_STACK, RMALLOC_STACK; lia| rewrite ELX; eassumption| assumption| lia| lia]. }
      cbv beta. intros pcp st2 ms2 PO. unfold opnew_postZ in PO.
      destruct PO as (r5 & r6 & r7 & r11 & r12 & r13 & r14 & r15 & r16 & r17 & r28 & r29 & r30 & r31 & m2 & errv2 & COPY & junk2
                      & -> & MI2 & ST2 & ERR2 & AUX2 & HP2 & FA2 & SO2 & BRC & HEAP2 & BLKC).
      replace (ret_pc (Z_to_bv 64 0x3c1d4)) with (Z_to_bv 64 0x3c1d4) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      rewrite ELX in ERR2. apply implM_ret_bind.
      pose proof BRC as (C0 & _ & _ & CC & CS). unfold OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in CC.

      pose proof (agree_of_heap_pres _ _ _ _ HP2) as AG2.
      assert (FRH : forall a, sp0 <= a < sp0 + 528 -> rclient_addr ((bv, A, 16 * cap) :: LB) sp0 a) by (intros a Ha; left; lia).
      apply (rw_cells_agree _ _ _ _ _ AG2) in PA0; [| intros a Ha; cbn in Ha; apply FRH; lia].
      apply (rw_cells_agree _ _ _ _ _ AG2) in PIMPL; [| intros a Ha; cbn in Ha; apply FRH; lia].
      apply (rw_cells_agree _ _ _ _ _ AG2) in PA16; [| intros a Ha; cbn in Ha; apply FRH; lia].
      apply (rw_cells_agree _ _ _ _ _ AG2) in DOCC; [| intros a Ha; cbn in Ha; apply FRH; lia].
      apply (rw_cells_agree _ _ _ _ _ AG2) in P48; [| intros a Ha; cbn in Ha; apply FRH; lia].
      apply (rw_cells_agree _ _ _ _ _ AG2) in J0; [| intros a Ha; cbn in Ha; apply FRH; lia].
      apply (rw_cells_agree _ _ _ _ _ AG2) in RES; [| intros a Ha; cbn in Ha; apply FRH; lia].
      apply (rw_cells_agree _ _ _ _ _ AG2) in SCR2; [| intros a Ha; cbn in Ha; apply FRH; lia].
      apply (rw_cells_agree _ _ _ _ _ AG2) in J48; [| intros a Ha; cbn in Ha; apply FRH; lia].
      apply (rw_cells_agree _ _ _ _ _ AG2) in JEL; [| intros a Ha; cbn in Ha; apply FRH; lia].
      apply (rw_cells_agree _ _ _ _ _ AG2) in XSEL; [| intros a Ha; cbn in Ha; apply FRH; lia].
      apply (rw_cells_agree _ _ _ _ _ AG2) in XFD; [| intros a Ha; cbn in Ha; apply FRH; lia].
      apply (rw_cells_agree _ _ _ _ _ AG2) in SAVE; [| intros a Ha; cbn in Ha; apply FRH; lia].
      apply (rw_cells_agree _ _ _ _ _ AG2) in SV; [| intros a Ha; cbn in Ha; apply FRH; lia].
      apply (vblk_agree _ _ _ _ _ _ _ _ _ AG2) in BLK; [| intros a _ Ha; right; right; exists (bv, A, 16 * cap); split; [left; reflexivity| cbn [blk_addr blk_size fst snd]; lia]| exact ELS| lia].
      assert (PRES2 : lx_pres LB (sp0 + 528) [LXW_SJ; LXW_UNW] m0 m2).
      { eapply lx_pres_trans; [exact PRES1|]. apply lx_pres_of_heap_pres. eapply rheap_pres_weaken; [exact HP2| lia| intros b Hb; right; exact Hb]. }
      pose proof (statics_heap _ _ _ _ HP2 ltac:(unfold GLOBALS_TOP; lia)) as (LXSf & SJSf & _).
      pose proof (SJSf _ SJS1) as SJS2. pose proof (LXSf LXS1) as LXS2. clear LXSf SJSf.
      assert (PL2 : payload_ok m2 LB D d).
      { eapply payload_ok_agree; [exact AG2| exact PL1|]. intros b a Hb Ha. right; right. exists b. split; [right; exact Hb| exact Ha]. }
      pose proof LXS2 as (_ & _ & GOT2 & VT242 & VTD2 & _ & _).
      clear AG2 HP2 HEAP1 AUX1 PRES1 SJS1 PL1 LXS1 GOT1 VT241 VTD1.

      replace (Z.to_nat (len1 + 64)) with (Z.to_nat len1 + 64)%nat in BLKC by lia.
      apply rw_cells_CB_split2 in BLKC. destruct BLKC as [BDOC BPAD]. rewrite Z2Nat.id in BPAD by lia.
      pose proof (munch_refl [(sp0, sp0 + 528); (COPY, COPY + (len1 + 64))]%Z m2) as MU. pose proof (wmono_refl usegs m2) as WM.
      unfold implM. iprefix.

      step. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia| clear K].
      step. zstep. step.
      rewrite (ZBridge.zb_lxor_ones COPY) by lia.
      if_cases KN; zify_cond KN; [exfalso; rewrite ?unsigned_lit in KN by lia; lia| clear KN].
      zstep. step. step. step.
      eapply evt_cut.
      { eapply memset_callZ with (junk := drop (Z.to_nat len1) junk2); [exact BPAD| assumption| lia| lia| lia| lia]. }
      cbv beta. intros ms' PO. unfold memset_postZ in PO.
      destruct PO as (u5 & u6 & u7 & u11 & u12 & u13 & u14 & u15 & u16 & u17 & u28 & u29 & u30 & u31 & m3 & -> & MU3 & WM3 & MI3 & PAD3).
      replace (ret_pc (Z_to_bv 64 0x3c1f4)) with (Z_to_bv 64 0x3c1f4) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      change (0 mod 256) with 0 in PAD3.
      hide MU. hide WM. transport_after_call usegs m2 m3 MU3 WM3. unhide MU. unhide WM.

      pose proof (fun p' A' n' H => LH_head_sep _ _ _ _ _ _ p' A' n' HEAP2 H) as SEPC.
      assert (OUTC : forall a, 0xd6000 <= a < GLOBALS_TOP -> outside [(COPY + len1, COPY + len1 + 64)] a).
      { intros a Ha. unfold GLOBALS_TOP in Ha. cbn [outside]. clear - Ha CS C0 LEN1. lia. }
      pose proof (statics_munch _ _ _ rr_guard MU3 WM3 OUTC) as (LXSf & SJSf & _). pose proof (LXSf LXS2) as LXS3. pose proof (SJSf _ SJS2) as SJS3. clear LXSf SJSf.
      pose proof LXS3 as (_ & _ & GOT3 & VT243 & VTD3 & _ & _).
      pose proof (agree_on_of_munch _ _ _ MU3 WM3) as AG3.
      assert (PL3 : payload_ok m3 LB D d).
      { eapply payload_ok_agree; [exact AG3| exact PL2|]. intros [[bi ba] bn] a Hb Ha.
        pose proof (SEPC bi ba bn ltac:(right; exact Hb)) as SP. cbn [blk_addr blk_size blk_id fst snd outside] in *. clear - SP Ha LEN1. lia. }
      apply (vblk_agree _ _ _ _ _ _ _ _ _ AG3) in BLK; [| intros a _ Ha; pose proof (SEPC bv A (16 * cap) ltac:(left; reflexivity)) as SP; cbn [outside]; clear - SP Ha LEN1; lia| exact ELS| lia].
      assert (PRES3 : lx_pres LB (sp0 + 528) [LXW_SJ; LXW_UNW] m0 m3).
      { eapply lx_pres_trans; [exact PRES2|]. eapply lx_pres_of_munch; [exact MU3| exact WM3|].
        intros a Ha [HX HC]. cbn [outside]. split; [| exact I]. destruct HC as [HC|[([[bi ba] bn] & Hb & Hr)|HC]]; [clear - HC CC CEIL LO; lia| | clear - HC CS C0 LEN1; lia].
        pose proof (SEPC bi ba bn ltac:(right; exact Hb)) as SP. cbn [blk_addr blk_size blk_id fst snd] in *. clear - SP Hr LEN1. lia. }

      assert (MU3' : munch [(sp0, sp0 + 528); (COPY, COPY + (len1 + 64))]%Z m2 m3).
      { eapply munch_weaken; [| exact MU3]. unfold sub_fp. cbn [outside]. intros x Hx. lia. }
      pose proof (munch_trans _ _ _ _ MU MU3') as MU3''. pose proof (wmono_trans usegs _ _ _ WM WM3) as WM3''.
      clear MU WM MU3 MU3' AG3. rename MU3'' into MU. rename WM3'' into WM.

      assert (DOCB : len1 = 0 \/ (bytes_at usegs m3 P1 (to_bytes (el_s1 d)) /\ exists b0, In b0 LB /\ blk_addr b0 <= P1 /\ P1 + len1 <= blk_addr b0 + blk_size b0)).
      { destruct (Z.eq_dec len1 0) as [Z0|NZ]; [left; exact Z0| right].
        assert (NE : el_s1 d <> []) by (intros E; apply NZ; rewrite Elen1, E; reflexivity).
        destruct (view_bytes _ _ _ _ _ _ PL3 FD VW1 NE) as (VB & _ & VBLK). rewrite <- Elen1 in VBLK. split; [exact VB| exact VBLK]. }

      lazymatch goal with |- evt _ ?QQ _ =>
      assert (K48 : forall (m4 : mem) (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
        munch [(COPY, COPY + len1)]%Z m3 m4 -> wmono usegs m3 m4 -> mem_inv usegs m4 ->
        rw_cells usegs m4 COPY [CB (Z.to_nat len1) (to_bytes (el_s1 d))] ->
        evt usegs QQ (MS (mkR y1 (Z_to_bv 64 sp0) gp (Z_to_bv 64 RATP) y5 y6 y7 xs0 (Z_to_bv 64 (zlength (el_str d))) y10 y11 y12 y13 y14 y15 y16 y17
                               (Z_to_bv 64 P0) (Z_to_bv 64 COPY) (Z_to_bv 64 len1) (Z_to_bv 64 P1) (Z_to_bv 64 (el_action d)) (Z_to_bv 64 0xffffffc0) (Z_to_bv 64 0) s9 s10 s11 y28 y29 y30 y31)
                        F (Z_to_bv 64 0x3c218) fc None m4 (seg_rom usegs))) end.
      { intros m4 y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 MU4 WM4 MI4 BDOC4.
        clear BDOC DOCB. hide MU. hide WM. transport_after_call usegs m3 m4 MU4 WM4. unhide MU. unhide WM.
        assert (OUTC4 : forall a, 0xd6000 <= a < GLOBALS_TOP -> outside [(COPY, COPY + len1)] a).
        { intros a Ha. unfold GLOBALS_TOP in Ha. cbn [outside]. clear - Ha CS C0 LEN1. lia. }
        pose proof (statics_munch _ _ _ rr_guard MU4 WM4 OUTC4) as (LXSf & SJSf & _). pose proof (LXSf LXS3) as LXS4. pose proof (SJSf _ SJS3) as SJS4. clear LXSf SJSf.
        pose proof LXS4 as (_ & _ & GOT4 & VT244 & VTD4 & _ & _).
        pose proof (agree_on_of_munch _ _ _ MU4 WM4) as AG4.
        assert (PL4 : payload_ok m4 LB D d).
        { eapply payload_ok_agree; [exact AG4| exact PL3|]. intros [[bi ba] bn] a Hb Ha.
          pose proof (SEPC bi ba bn ltac:(right; exact Hb)) as SP. cbn [blk_addr blk_size blk_id fst snd outside] in *. clear - SP Ha LEN1. lia. }
        apply (vblk_agree _ _ _ _ _ _ _ _ _ AG4) in BLK; [| intros a _ Ha; pose proof (SEPC bv A (16 * cap) ltac:(left; reflexivity)) as SP; cbn [outside]; clear - SP Ha LEN1; lia| exact ELS| lia].
        assert (PRES4 : lx_pres LB (sp0 + 528) [LXW_SJ; LXW_UNW] m0 m4).
        { eapply lx_pres_trans; [exact PRES3|]. eapply lx_pres_of_munch; [exact MU4| exact WM4|].
          intros a Ha [HX HC]. cbn [outside]. split; [| exact I]. destruct HC as [HC|[([[bi ba] bn] & Hb & Hr)|HC]]; [clear - HC CC CEIL LO LEN1; lia| | clear - HC CS C0 LEN1; lia].
          pose proof (SEPC bi ba bn ltac:(right; exact Hb)) as SP. cbn [blk_addr blk_size blk_id fst snd] in *. clear - SP Hr LEN1. lia. }
        assert (HEAP4 : RHEAP st2 ((pcp, COPY, len1 + 64) :: (bv, A, 16 * cap) :: LB) m4).
        { eapply LH_frame; [eapply LH_frame; [exact HEAP2| exact MU| exact WM|]| exact MU4| exact WM4|].
          - constructor; [apply W_ok_stack; cbn; lia|]. constructor; [| constructor]. eapply (W_ok_block _ (pcp, COPY, len1 + 64)); [left; reflexivity| cbn; lia| cbn; lia].
          - constructor; [| constructor]. eapply (W_ok_block _ (pcp, COPY, len1 + 64)); [left; reflexivity| cbn; lia| cbn; lia]. }
        assert (AUX4 : rauxv_ok m4 B).
        { eapply rauxv_ok_frame; [eapply rauxv_ok_frame; [exact AUX2| exact MU| exact WM|]| exact MU4| exact WM4|].
          - constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; clear - CC CS C0 CEIL LO LEN1 QB; lia| constructor].
          - constructor; [cbn; unfold RAUXV_CELL; clear - CC CS C0 CEIL LO LEN1 QB; lia| constructor]. }

        lazymatch goal with H : rw_cells usegs m4 (COPY + len1) _ |- _ => rename H into PAD4 end.
        assert (BUF4 : bytes_at usegs m4 COPY (padded_bytes (el_s1 d))).
        { pose proof (rw_cells_join _ _ _ _ _ BDOC4 PAD4 ltac:(cbn [cells_size csize Nat.add]; lia)) as J. destruct J as [[_ HB] _].
          cbn [cells_bytes cbytes app] in HB. rewrite app_nil_r in HB. unfold padded_bytes, zbytes. exact HB. }
        clear MU WM MU4 WM4 AG4 PL3 PRES3 LXS3 SJS3 HEAP2 AUX2.
        pose proof (munch_refl ([] : list (Z * Z)) m4) as MU. pose proof (wmono_refl usegs m4) as WM.

        step. step. step. step. step. step. step.
        replace (Z_to_bv 64 (sp0 + 336)) with (Z_to_bv 64 (sp0 + 312 + 24)) by (f_equal; lia).
        unfold SJ_GOT_NOTHROW, SJ_NOTHROW_TAG, MallocRep.wz in GOT4. unfold SJ_IMPL_VT24, SJ_CREATE_DPI, MallocRep.wz in VT244. unfold MallocRep.wz in VTD4.
        ihere. to_implM.
        eapply (pid_front_cps HM) with (B := B) (lo := lo) (SRET := sp0 + 8) (PARSER := sp0 + 312) (init := init);
          [exact HEAP4| exact AUX4| lia| eassumption| exact CEIL'| unfold GLOBALS_TOP; lia| unfold SJ_OPNEW_STACK, RMALLOC_STACK; lia
          | rewrite ELX; eassumption| assumption| lia| lia| lia| lia
          | split; [exact GOT4| split; [exact VT244| exact VTD4]]| exact SJS4| exact PIMPL| exact DOCC| exact P48|].
        intros psb ptp pim pix poc pia st5 ms5 MID. subst len1.
        eapply (pid_nocopy_cps S2) with (B := B) (lo := lo) (pcp := pcp) (d := el_s1 d);
          [exact MID| lia| exact HEAP4| left; reflexivity| | exact BUF4| exact FRM| lia| (clear - B63; lia)| exact CEIL'| unfold GLOBALS_TOP; lia
          | unfold SJ_S2_STACK, SJ_S2_FRAMES, RMALLOC_STACK; lia| lia| clear - AL16; replace sp0 with (sp0 + 528 + (-33) * 16) by lia; rewrite Z.mod_add by lia; exact AL16
          | lia| lia| lia| clear - AL16; replace (sp0 + 312) with (sp0 + 528 + (-27) * 8) by lia; rewrite Z.mod_add by lia; apply mod8_of_mod16; exact AL16| exact RES|].
        { destruct VW1 as [[_ E]|(o & _ & EX & _)]; [rewrite E; constructor| rewrite EX; apply Forall_firstn'; apply Forall_skipn'; rewrite ER; apply Forall_skipn'; exact PRNG]. }
        intros st6 ms6 (IMPL & IDX & OC & IA & TAPE & SBUF & PO). unfold hpostF in PO.
        destruct PO as (w5 & w6 & w7 & w10 & w11 & w12 & w13 & w14 & w15 & w16 & w17 & w28 & w29 & w30 & w31 & F' & fc' & m6
                        & -> & FRM6 & MI6 & ST6 & (errv6 & ERR6) & AUX6 & FA6 & SO6 & RR).
        unfold pidn_R in RR.
        destruct RR as (HEAP6 & PRES46 & SJRO6 & SJS6 & PIMPL6 & DOCC6 & P486 & (r & SRET6 & OKR) & (vptr & nsi & p12 & nxt & p28 & capv & md & b48 & b49 & p50 & bufv & lenv & docv & THIS6 & EVP) & BRTP & BRSB).
        replace (ret_pc (Z_to_bv 64 0x3c234)) with (Z_to_bv 64 0x3c234) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        rewrite ELX in ERR6. remember (zlength (el_s1 d)) as len1 eqn:Elen1.
        remember (Z.max len1 32) as capd eqn:Ecapd.
        pose proof BRTP as (TP0 & _ & _ & TPC & TPS). pose proof BRSB as (SB0 & _ & _ & SBC & SBS). unfold OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in TPC, SBC.
        pose proof (roundup64_ge (capd + 3)) as RC2. pose proof (roundup64_ge (5 * (capd / 3) + 64)) as RC3.
        assert (D3 : 0 <= capd / 3) by (apply Z.div_pos; lia).
        pose proof (LH_block_range _ _ _ _ HEAP6 ltac:(do 3 right; left; reflexivity)) as BRIM. cbn [blk_addr blk_size fst snd] in BRIM.
        pose proof BRIM as (IM0 & _ & _ & IMC & _). unfold OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in IMC.
        assert (OKRR : r = Z_to_bv 64 0 \/ 1 <= bv_unsigned r < 64) by (destruct OKR as [K|[K _]]; [right; exact K| left; exact K]).

        pose proof (agree_of_lx_pres _ _ _ _ _ PRES46) as AG46.
        assert (FRCL : forall a, sp0 <= a < sp0 + 528 -> ~ (sp0 + 8 <= a < sp0 + 32) -> ~ (sp0 + 320 <= a < sp0 + 328) -> ~ (sp0 + 336 <= a < sp0 + 360) ->
                  lx_client ((pcp, COPY, len1 + 64) :: (bv, A, 16 * cap) :: LB) sp0 (pid_front_X (sp0 + 312) ++ pidn_X (sp0 + 8)) a).
        { intros a Ha N1 N2 N3. split; [| left; lia]. unfold pid_front_X, pidn_X, LXW_SJ, SJ_STATICS_LO, SJ_STATICS_HI. cbn [app rin_ivs fst snd]. clear - Ha N1 N2 N3 GLO LO. lia. }
        apply (rw_cells_agree _ _ _ _ _ AG46) in PA0; [| intros a Ha; cbn in Ha; apply FRCL; lia].
        apply (rw_cells_agree _ _ _ _ _ AG46) in PA16; [| intros a Ha; cbn in Ha; apply FRCL; lia].
        apply (rw_cells_agree _ _ _ _ _ AG46) in J0; [| intros a Ha; cbn in Ha; apply FRCL; lia].
        apply (rw_cells_agree _ _ _ _ _ AG46) in SCR2; [| intros a Ha; cbn in Ha; apply FRCL; lia].
        apply (rw_cells_agree _ _ _ _ _ AG46) in J48; [| intros a Ha; cbn in Ha; apply FRCL; lia].
        apply (rw_cells_agree _ _ _ _ _ AG46) in JEL; [| intros a Ha; cbn in Ha; apply FRCL; lia].
        apply (rw_cells_agree _ _ _ _ _ AG46) in XSEL; [| intros a Ha; cbn in Ha; apply FRCL; lia].
        apply (rw_cells_agree _ _ _ _ _ AG46) in XFD; [| intros a Ha; cbn in Ha; apply FRCL; lia].
        apply (rw_cells_agree _ _ _ _ _ AG46) in SAVE; [| intros a Ha; cbn in Ha; apply FRCL; lia].
        apply (rw_cells_agree _ _ _ _ _ AG46) in SV; [| intros a Ha; cbn in Ha; apply FRCL; lia].
        assert (BKCL : forall a, A <= a < A + 16 * cap -> lx_client ((pcp, COPY, len1 + 64) :: (bv, A, 16 * cap) :: LB) sp0 (pid_front_X (sp0 + 312) ++ pidn_X (sp0 + 8)) a).
        { intros a Ha. split; [| right; left; exists (bv, A, 16 * cap); split; [right; left; reflexivity| cbn [blk_addr blk_size fst snd]; lia]].
          unfold pid_front_X, pidn_X, LXW_SJ, SJ_STATICS_LO, SJ_STATICS_HI. cbn [app rin_ivs fst snd]. clear - Ha AC AS A0 CEIL LO. lia. }
        apply (vblk_agree _ _ _ _ _ _ _ _ _ AG46) in BLK; [| intros a _ Ha; apply BKCL; exact Ha| exact ELS| lia].
        assert (PL6 : payload_ok m6 LB D d).
        { eapply payload_ok_agree; [exact AG46| exact PL4|]. intros b a Hb Ha. pose proof (LH_block_range _ _ _ _ HEAP00 Hb) as (_ & _ & _ & BC & BS).
          unfold OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in BC. split; [| right; left; exists b; split; [right; right; exact Hb| exact Ha]].
          unfold pid_front_X, pidn_X, LXW_SJ, SJ_STATICS_LO, SJ_STATICS_HI. cbn [app rin_ivs fst snd]. clear - Ha BC BS CEIL LO. lia. }
        assert (PRES6 : lx_pres LB (sp0 + 528) [LXW_SJ; LXW_UNW] m0 m6).
        { eapply lx_pres_trans; [exact PRES4|]. eapply (lx_pres_sub LB (sp0 + 528) _ _ _ _ _ _ PRES46); [lia| intros b0 Hb0; right; right; exact Hb0|].
          intros a Ha NX. unfold pid_front_X, pidn_X, LXW_SJ, LXW_UNW, SJ_STATICS_LO, SJ_STATICS_HI in Ha, NX. cbn [app rin_ivs fst snd] in Ha, NX.
          split; [clear - Ha NX LO GLO; lia|]. split; [intros IB; specialize (BLB a IB); clear - Ha NX BLB CEIL LO; lia| clear - Ha NX LO GLO; lia]. }
        clear AG46 PRES46 FRCL BKCL HEAP4 AUX4 PRES4 PL4 MU WM.
        readdr PIMPL6 (sp0 + 320). readdr DOCC6 (sp0 + 336). readdr P486 (sp0 + 360). replace (sp0 + 312 + 24) with (sp0 + 336) in SRET6 by lia.

        hide THIS6.
        unfold implM. iprefix.
        eapply evt_cut; [eapply res_copy_spec; [exact ST6| unfold GLOBALS_TOP; lia| lia| lia| exact MI6| exact OKRR| left; reflexivity| exact SRET6| exact JEL]|].
        cbv beta. intros ms7 PO. destruct PO as (a0' & a1' & e & m7 & -> & HE & EIFF & MU7 & WM7 & MI7 & ST7 & SRET7 & ELEM7).
        clear SRET6 JEL. transport_after_call usegs m6 m7 MU7 WM7.
        unhide THIS6.
        pose proof (agree_on_of_munch _ _ _ MU7 WM7) as AG7.
        apply (rw_cells_agree _ _ _ _ _ AG7) in THIS6; [| intros a Ha; unfold impl_cells16 in Ha; cbn in Ha; cbn [outside]; clear - Ha IMC CEIL LO; lia].
        apply (vblk_agree _ _ _ _ _ _ _ _ _ AG7) in BLK; [| intros a _ Ha; cbn [outside]; clear - Ha AC CEIL LO; lia| exact ELS| lia].
        apply (s2_okres_agree _ _ _ _ _ _ _ _ AG7) in OKR; [| intros a Ha; cbn [outside]; clear - Ha TPC CEIL LO; lia| intros a Ha; cbn [outside]; clear - Ha SBC CEIL LO; lia].
        assert (SJS7 : sj_statics m7 true).
        { eapply sj_statics_agree; [exact AG7| | exact SJS6]. intros a Ha. pose proof (sjs_addr_lt a Ha) as [R1 _]. unfold GLOBALS_TOP in R1. cbn [outside]. clear - R1 GLO LO. lia. }
        assert (PL7 : payload_ok m7 LB D d).
        { eapply payload_ok_agree; [exact AG7| exact PL6|]. intros b a Hb Ha.
          assert (BA : a < alloc_ceiling) by (apply BLB; exists b; split; [exact Hb| exact Ha]). cbn [outside]. clear - BA CEIL LO. lia. }
        assert (PRES7 : lx_pres LB (sp0 + 528) [LXW_SJ; LXW_UNW] m0 m7).
        { eapply lx_pres_trans; [exact PRES6|]. eapply lx_pres_of_munch; [exact MU7| exact WM7|].
          intros a Ha HC. pose proof (CLI a Ha HC) as OU. cbn [outside] in OU |- *. clear - OU. lia. }
        assert (HEAP7 : RHEAP st6 ((pia, IA, 1024) :: (poc, OC, 8192) :: (pix, IDX, 4 * (roundup64 capd + 9)) :: (pim, IMPL, 96)
                   :: (ptp, TAPE, 8 * roundup64 (capd + 3)) :: (psb, SBUF, roundup64 (5 * (capd / 3) + 64)) :: (pcp, COPY, len1 + 64) :: (bv, A, 16 * cap) :: LB) m7).
        { eapply LH_frame; [exact HEAP6| exact MU7| exact WM7|]. constructor; [apply W_ok_stack; cbn; lia| constructor]. }
        assert (AUX7 : rauxv_ok m7 B).
        { eapply rauxv_ok_frame; [exact AUX6| exact MU7| exact WM7|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
        clear AG7 MU7 WM7 HEAP6 AUX6 SJS6 PL6 PRES6.

        pose proof (munch_refl ([] : list (Z * Z)) m7) as MU. pose proof (wmono_refl usegs m7) as WM.
        change (if 0 =? 0 then 0x3c264 else 0x3c248) with 0x3c264.
        step. step.
        pose proof (RHEAP_pull _ [(pia, IA, 1024); (poc, OC, 8192); (pix, IDX, 4 * (roundup64 capd + 9)); (pim, IMPL, 96); (ptp, TAPE, 8 * roundup64 (capd + 3)); (psb, SBUF, roundup64 (5 * (capd / 3) + 64))]
                      (pcp, COPY, len1 + 64) ((bv, A, 16 * cap) :: LB) _ HEAP7) as HEAP7'. cbn [app] in HEAP7'.
        assert (ND : List.NoDup (map blk_id ((pcp, COPY, len1 + 64) :: (pia, IA, 1024) :: (poc, OC, 8192) :: (pix, IDX, 4 * (roundup64 capd + 9)) :: (pim, IMPL, 96)
                                            :: (ptp, TAPE, 8 * roundup64 (capd + 3)) :: (psb, SBUF, roundup64 (5 * (capd / 3) + 64)) :: (bv, A, 16 * cap) :: LB))) by (eapply LH_nodup; exact HEAP7').
        ihere. to_implM. eapply implM_bind.
        { eapply (opdel_arr_proof HF) with (B := B) (lo := lo) (A := COPY) (n := len1 + 64);
            [exact HEAP7'| left; reflexivity| exact AUX7| lia| exact ST7| exact CEIL'| unfold RFREE_STACK; lia| exact ERR6| exact MI7| lia]. }
        cbv beta. intros [] st8 ms8 PO. unfold free_postZ in PO.
        destruct PO as (v5 & v6 & v7 & v10 & v11 & v12 & v13 & v14 & v15 & v16 & v17 & v28 & v29 & v30 & v31 & m8
                        & -> & MI8 & ST8 & ERR8 & AUX8 & HP8 & FA8 & SO8 & HEAP8).
        rewrite (lb_remove_hd _ _ _ _ ND) in HP8, HEAP8.
        replace (ret_pc (Z_to_bv 64 0x3c26c)) with (Z_to_bv 64 0x3c26c) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        pose proof (agree_of_heap_pres _ _ _ _ HP8) as AG8.
        pose proof (statics_heap _ _ _ _ HP8 ltac:(unfold GLOBALS_TOP; lia)) as (LXSf & SJSf & _). pose proof (SJSf _ SJS7) as SJS8. clear LXSf SJSf.
        assert (FRH8 : forall a, sp0 <= a < sp0 + 528 -> rclient_addr ((pia, IA, 1024) :: (poc, OC, 8192) :: (pix, IDX, 4 * (roundup64 capd + 9)) :: (pim, IMPL, 96)
                                            :: (ptp, TAPE, 8 * roundup64 (capd + 3)) :: (psb, SBUF, roundup64 (5 * (capd / 3) + 64)) :: (bv, A, 16 * cap) :: LB) sp0 a) by (intros a Ha; left; lia).
        apply (rw_cells_agree _ _ _ _ _ AG8) in PA0; [| intros a Ha; cbn in Ha; apply FRH8; lia].
        apply (rw_cells_agree _ _ _ _ _ AG8) in PA16; [| intros a Ha; cbn in Ha; apply FRH8; lia].
        apply (rw_cells_agree _ _ _ _ _ AG8) in J0; [| intros a Ha; cbn in Ha; apply FRH8; lia].
        apply (rw_cells_agree _ _ _ _ _ AG8) in SCR2; [| intros a Ha; cbn in Ha; apply FRH8; lia].
        apply (rw_cells_agree _ _ _ _ _ AG8) in J48; [| intros a Ha; cbn in Ha; apply FRH8; lia].
        apply (rw_cells_agree _ _ _ _ _ AG8) in ELEM7; [| intros a Ha; destruct (bv_eqb r (Z_to_bv 64 0)); cbn in Ha; apply FRH8; lia].
        apply (rw_cells_agree _ _ _ _ _ AG8) in XSEL; [| intros a Ha; cbn in Ha; apply FRH8; lia].
        apply (rw_cells_agree _ _ _ _ _ AG8) in XFD; [| intros a Ha; cbn in Ha; apply FRH8; lia].
        apply (rw_cells_agree _ _ _ _ _ AG8) in SAVE; [| intros a Ha; cbn in Ha; apply FRH8; lia].
        apply (rw_cells_agree _ _ _ _ _ AG8) in SV; [| intros a Ha; cbn in Ha; apply FRH8; lia].
        apply (rw_cells_agree _ _ _ _ _ AG8) in PIMPL6; [| intros a Ha; cbn in Ha; apply FRH8; lia].
        apply (rw_cells_agree _ _ _ _ _ AG8) in DOCC6; [| intros a Ha; cbn in Ha; apply FRH8; lia].
        apply (rw_cells_agree _ _ _ _ _ AG8) in P486; [| intros a Ha; cbn in Ha; apply FRH8; lia].
        apply (rw_cells_agree _ _ _ _ _ AG8) in SRET7; [| intros a Ha; unfold res_cells in Ha; destruct (bv_eqb r (Z_to_bv 64 0)); cbn in Ha; apply FRH8; lia].
        apply (rw_cells_agree _ _ _ _ _ AG8) in THIS6; [| intros a Ha; right; right; exists (pim, IMPL, 96); split; [do 3 right; left; reflexivity| unfold impl_cells16 in Ha; cbn in Ha; cbn [blk_addr blk_size fst snd]; lia]].
        apply (vblk_agree _ _ _ _ _ _ _ _ _ AG8) in BLK; [| intros a _ Ha; right; right; exists (bv, A, 16 * cap); split; [do 6 right; left; reflexivity| cbn [blk_addr blk_size fst snd]; lia]| exact ELS| lia].
        apply (s2_okres_agree _ _ _ _ _ _ _ _ AG8) in OKR;
          [| intros a Ha; right; right; exists (ptp, TAPE, 8 * roundup64 (capd + 3)); split; [do 4 right; left; reflexivity| cbn [blk_addr blk_size fst snd]; lia]
           | intros a Ha; right; right; exists (psb, SBUF, roundup64 (5 * (capd / 3) + 64)); split; [do 5 right; left; reflexivity| cbn [blk_addr blk_size fst snd]; lia]].
        assert (PL8 : payload_ok m8 LB D d).
        { eapply payload_ok_agree; [exact AG8| exact PL7|]. intros b a Hb Ha. right; right. exists b. split; [do 7 right; exact Hb| exact Ha]. }
        assert (PRES8 : lx_pres LB (sp0 + 528) [LXW_SJ; LXW_UNW] m0 m8).
        { eapply lx_pres_trans; [exact PRES7|]. apply lx_pres_of_heap_pres. eapply rheap_pres_weaken; [exact HP8| lia| intros b Hb; do 7 right; exact Hb]. }
        clear AG8 HP8 MU WM.

        assert (CAPD : doc_cap d = capd) by (unfold doc_cap; rewrite EDOC, <- Elen1, Ecapd; reflexivity).
        rewrite <- CAPD in HEAP8, OKR, BRTP, BRSB, DOCC6.
        unfold implM. iprefix.
        destruct (Z.eq_dec e 0) as [E0|E0];
          step; if_cases KS; zify_cond KS; rewrite ?unsigned_lit in KS by lia; try (exfalso; lia).
        1: replace (Z_to_bv 64 0x3c2bc) with (Z_to_bv 64 (if e =? 0 then 0x3c2bc else 0x3c270)) by (rewrite E0; reflexivity).
        2: replace (Z_to_bv 64 0x3c270) with (Z_to_bv 64 (if e =? 0 then 0x3c2bc else 0x3c270)) by (replace (e =? 0) with false by (symmetry; apply Z.eqb_neq; exact E0); reflexivity).
        all: ihere; to_implM; apply HK; unfold gate_post.
        all: do 20 eexists; exists F', fc', m8, errv6, IMPL, IDX, OC, IA, TAPE, SBUF, r, e, P0; do 10 eexists; exists vptr, nsi, nxt, capv, md, bufv, lenv, docv, b48, b49, p12, p28, p50.
        all: split; [cbv delta [mkR]; reflexivity|]. all: split; [rewrite EE; reflexivity|]. all: split; [exact HE|]. all: split; [exact EIFF|]. all: split; [exact FRM6|].
        all: split; [exact MI8|]. all: split; [exact ST8|]. all: split; [exact ERR8|]. all: split; [exact AUX8|]. all: split; [congruence|]. all: split; [congruence|].
        all: split; [exact HEAP8|]. all: split; [exact PRES8|]. all: split; [exact SJS8|]. all: split; [exact PL8|].
        all: split; [rewrite EE; split; [exact ELS|]; split; [exact SZ|]; split; [exact SV| exact BLK]|].
        all: split; [exact SRET7|]. all: split; [exact OKR|]. all: split; [exact BRTP|]. all: split; [exact BRSB|]. all: split; [exact ELEM7|].
        all: split; [exact PA0|]. all: split; [exact PIMPL6|]. all: split; [exact PA16|]. all: split; [exact DOCC6|]. all: split; [exact P486|]. all: split; [exact THIS6|]. all: split; [exact EVP|].
        all: split; [exact J0|]. all: split; [exact SCR2|]. all: split; [exact J48|]. all: split; [exact XSEL|]. all: split; [exact XFD| exact SAVE]. }

      step. if_cases KZ; zify_cond KZ.
      +
        step. step.
        eapply (K48 m3); [apply munch_refl| apply wmono_refl| assumption|].
        assert (ES0 : el_s1 d = []) by (destruct (el_s1 d) as [|c l] eqn:E0; [reflexivity| exfalso; rewrite Elen1 in KZ; unfold zlength in KZ; cbn in KZ; lia]).
        rewrite ES0. rewrite KZ in BDOC. cbn [Z.to_nat take to_bytes map] in BDOC. rewrite KZ. cbn [Z.to_nat]. exact BDOC.
      +
        destruct DOCB as [Z0|(SRCB & (b0 & Hb0 & Hb01 & Hb02))]; [exfalso; lia|].
        destruct b0 as [[b0i b0a] b0n]. pose proof (SEPC b0i b0a b0n ltac:(right; exact Hb0)) as SP0. cbn [blk_addr blk_size blk_id fst snd] in Hb01, Hb02, SP0.
        step. step. step. step.
        eapply evt_cut.
        { eapply memcpy_callZ with (src := to_bytes (el_s1 d)) (junk := take (Z.to_nat len1) junk2);
            [exact SRCB| rewrite to_bytes_length; rewrite Elen1; unfold zlength; lia| exact BDOC| clear - SP0 Hb01 Hb02 LEN1; lia| lia| lia| lia| assumption]. }
        cbv beta. intros ms' PO. unfold memcpy_postZ in PO.
        destruct PO as (z5 & z6 & z7 & z11 & z12 & z13 & z14 & z15 & z16 & z17 & z28 & z29 & z30 & z31 & m4 & -> & MU4 & WM4 & MI4 & DST4 & SRC4).
        replace (ret_pc (Z_to_bv 64 0x3c208)) with (Z_to_bv 64 0x3c208) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        hide MU. hide WM. transport_after_call usegs m3 m4 MU4 WM4. unhide MU. unhide WM.
        step. step.
        eapply (K48 m4); [exact MU4| exact WM4| exact MI4| exact DST4].
  Qed.
End Proofs.
End WithCeiling0.
