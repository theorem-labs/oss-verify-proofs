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
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import Layout Exit Printf_wfile Sj_iface Sj_kit Sj_new Sj_new_t2 Sj_h_kit Sj_h_pdtor.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjS1Out SjStage1 SjStage1Out SjTape SjTapeList SjTapeTile.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require SjAlloc.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import Sj_stage2_iface Atp_pid Atp_defs Atp_h_defs Atp_h_find El_defs El_hdr El_h2 El_exit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Sj_stage1_kit.
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

Definition EL_DISPATCH : Z := 0x3c2bc.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Lemma implM_gate_fail : forall {B} (rest : unit -> M PState B) (act : M PState unit) s Q ms,
  implM usegs (rest tt) s Q ms -> implM usegs (mbind mcho (fun ok => mbind (if ok =? 0 then mret tt else act) rest)) s Q ms.
Proof. intros B rest act s Q ms H. apply (implM_chok usegs 0). cbn [Z.eqb]. apply implM_retb. exact H. Qed.
Lemma implM_gate_ok : forall {B} (rest : unit -> M PState B) (act : M PState unit) s Q ms,
  implM usegs (mbind act rest) s Q ms -> implM usegs (mbind mcho (fun ok => mbind (if ok =? 0 then mret tt else act) rest)) s Q ms.
Proof. intros B rest act s Q ms H. apply (implM_chok usegs 1). cbn [Z.eqb Pos.eqb]. exact H. Qed.

Definition el_blocks (psb ptp pim pix poc pia bv : bptr) (IA OC IDX IMPL TAPE SBUF A cap capd : Z) (LB : list block) : list block :=
  (pia, IA, 1024) :: (poc, OC, 8192) :: (pix, IDX, 4 * (roundup64 capd + 9)) :: (pim, IMPL, 96) :: (ptp, TAPE, 8 * roundup64 (capd + 3)) :: (psb, SBUF, roundup64 (5 * (capd / 3) + 64))
  :: (bv, A, 16 * cap) :: LB.

Definition act_post (sp0 : Z) (gp s9 s10 s11 s0 s1 s2 s3 s4 s5 s6 s7 s8 ra : word) (st : PState) (LBall LB : list block) (lo B D : Z) (d : list Z) (m0 : mem)
    (A cap : Z) (P : nat) (IMPL IDX OC IA TAPE SBUF : Z) (capw : word) (st' : PState) : machine_state -> Prop :=
  fun ms' => exists x1 t0 t1 t2 y8 y9 y10 a1 a2 a3 a4 a5 a6 a7 y18 y19 y20 y21 y22 y23 y24 t3 t4 t5 t6 F' fc' m' (errv' : word) (init : bool)
                    (nsi nxt capv md bufv lenv docv : word) (b48 b49 : byte) (p12 p28 p50 j313 j329 j361 jlo jmid : list byte),
    ms' = MS (mkR x1 (Z_to_bv 64 sp0) gp (Z_to_bv 64 RATP) t0 t1 t2 y8 y9 y10 a1 a2 a3 a4 a5 a6 a7 y18 y19 y20 y21 y22 y23 y24 s9 s10 s11 t3 t4 t5 t6)
             F' (Z_to_bv 64 EL_EXIT) fc' None m' (seg_rom usegs)
    /\ RHEAP st' LBall m' /\ rauxv_ok m' B /\ mem_inv usegs m' /\ stk usegs m' lo sp0 /\ rw_cells usegs m' LX_ERRNO [C4 errv']
    /\ ps_fa st' = ps_fa st /\ ps_so st' = ps_so st /\ frm0 fc'
    /\ lx_pres LB (sp0 + 528) [LXW_SJ; LXW_UNW; LXW_TP] m0 m' /\ rw_cells usegs m' EL_TPLOC [C8 (wz EL_GLOC)] /\ sj_statics m' init /\ payload_ok m' LB D d
    /\ rw_cells usegs m' sp0 [CB 312 jlo]
    /\ rw_cells usegs m' (sp0 + 312) [C1 (Z_to_bv 8 0); CB 7 j313]
    /\ rw_cells usegs m' (sp0 + 320) [C8 (Z_to_bv 64 IMPL)]
    /\ rw_cells usegs m' (sp0 + 328) [C1 (Z_to_bv 8 0); CB 3 j329; C4 (Z_to_bv 64 12)]
    /\ rw_cells usegs m' (sp0 + 336) [C8 (Z_to_bv 64 TAPE); C8 (Z_to_bv 64 SBUF); C8 capw]
    /\ rw_cells usegs m' (sp0 + 360) (p48_cells (Z_to_bv 8 0) j361 (Z_to_bv 64 0) (Z_to_bv 64 0))
    /\ rw_cells usegs m' IMPL (impl_cells16 (Z_to_bv 64 SJ_DPI_VPTR) nsi p12 (Z_to_bv 64 IDX) nxt p28 capv md b48 b49 p50 (Z_to_bv 64 OC) (Z_to_bv 64 IA) bufv lenv docv)
    /\ rw_cells usegs m' (sp0 + 392) [C8 (Z_to_bv 64 A); C8 (Z_to_bv 64 (A + 16 * Z.of_nat P)); C8 (Z_to_bv 64 (A + 16 * cap))]
    /\ rw_cells usegs m' (sp0 + 416) [CB 32 jmid]
    /\ rw_cells usegs m' (sp0 + 448) [C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Definition el_act_stmt : Prop :=
  forall (R : Type) (k : unit -> M PState R) (Q : R -> PState -> machine_state -> Prop)
    (x1 gp t0 t1 t2 xs0 a0 a1 a2 a3 a4 a5 a6 a7 xs3 xs4 xs5 xs8 s9 s10 s11 t3 t4 t5 t6 : word) (s0 s1 s2 s3 s4 s5 s6 s7 s8 ra : word) (F : bvmap 5 word) (fc : bv 32)
    (m0 m : mem) (s00 st : PState) (LB : list block) (D : Z) (d : list Z) (sp0 lo B : Z) (E : aenv) (errv : word)
    (bv psb ptp pim pix poc pia : bptr) (A cap IMPL IDX OC IA : Z) (jr : list byte)
    (j0 jres jos j313 j329 j361 j416 j441 : list byte) (nsi nxt capv md bufv lenv docv : word) (b48 b49 : byte) (p12 p28 p50 : list byte),
  aenv_ok E -> AINV E m ->
  ae_LB E = el_blocks psb ptp pim pix poc pia bv IA OC IDX IMPL (ae_TAPE E) (ae_SBUF E) A cap (doc_cap d) LB -> ae_lo E = lo -> ae_B E = B -> ae_DOC E = sp0 + 336 -> ae_p1 E = el_str d ->
  RHEAP s00 LB m0 -> lx_statics m0 ->
  RHEAP st (ae_LB E) m -> rauxv_ok m B -> sp0 + 528 <= B -> B < 2^62 ->
  stk usegs m lo sp0 -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= sp0 + 528 - LX_FUZZ_STACK ->
  rw_cells usegs m LX_ERRNO [C4 errv] -> mem_inv usegs m -> (sp0 + 528) mod 16 = 0 -> frm0 fc ->
  lx_pres LB (sp0 + 528) [LXW_SJ; LXW_UNW] m0 m -> sj_statics m true -> payload_ok m LB D d -> el_fd_ok d = true ->
  vrep m (sp0 + 392) A (cap, Z.of_nat (el_P d), Some bv) (el_els D d) jr -> nth 0 (el_els D d) (0, 0) = (ae_PTR E, zlength (el_str d)) ->
  rw_cells usegs m sp0 [CB 8 j0] -> rw_cells usegs m (sp0 + 8) [CB 24 jres] -> rw_cells usegs m (sp0 + 32) [CB 264 jos] ->
  el_root E m (sp0 + 296) ->
  rw_cells usegs m (sp0 + 312) [C1 (Z_to_bv 8 0); CB 7 j313] -> rw_cells usegs m (sp0 + 320) [C8 (Z_to_bv 64 IMPL)] ->
  rw_cells usegs m (sp0 + 328) [C1 (Z_to_bv 8 0); CB 3 j329; C4 (Z_to_bv 64 12)] -> rw_cells usegs m (sp0 + 352) [C8 (Z_to_bv 64 (doc_cap d))] ->
  rw_cells usegs m (sp0 + 360) (p48_cells (Z_to_bv 8 0) j361 (Z_to_bv 64 0) (Z_to_bv 64 0)) ->
  rw_cells usegs m IMPL (impl_cells16 (Z_to_bv 64 SJ_DPI_VPTR) nsi p12 (Z_to_bv 64 IDX) nxt p28 capv md b48 b49 p50 (Z_to_bv 64 OC) (Z_to_bv 64 IA) bufv lenv docv) ->
  rw_cells usegs m (sp0 + 416) [CB 4 j416; C4 (Z_to_bv 64 (el_sel d))] ->
  rw_cells usegs m (sp0 + 424) [C8 (Z_to_bv 64 (D + zlength d)); C8 (Z_to_bv 64 0); C1 (Z_to_bv 8 0); CB 7 j441] ->
  rw_cells usegs m (sp0 + 448) [C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  (forall st' ms', act_post sp0 gp s9 s10 s11 s0 s1 s2 s3 s4 s5 s6 s7 s8 ra st (ae_LB E) LB lo B D d m0 A cap (el_P d) IMPL IDX OC IA (ae_TAPE E) (ae_SBUF E) (Z_to_bv 64 (doc_cap d)) st' ms' ->
      implM usegs (k tt) st' Q ms') ->
  implM usegs (mbind (el_act lops d) k) st Q
    (MS (mkR x1 (Z_to_bv 64 sp0) gp (Z_to_bv 64 RATP) t0 t1 t2 xs0 (Z_to_bv 64 (zlength (el_str d))) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 (ae_PTR E)) xs3 xs4 xs5 (Z_to_bv 64 (el_action d)) (Z_to_bv 64 0xFFFFFFC0) xs8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 EL_DISPATCH) fc None m (seg_rom usegs)).

Definition lftoi_rest (d : list Z) (v : @vec bptr) (psb ptp pim pix poc pia : bptr) : M PState Z :=
  mbind mcho (fun ok =>
  mbind (if ok =? 0 then mret tt else el_act lops d) (fun _ =>
  mbind (del lops psb) (fun _ => mbind (del lops ptp) (fun _ => mbind (del lops pia) (fun _ => mbind (del lops poc) (fun _ =>
  mbind (del lops pix) (fun _ => mbind (del lops pim) (fun _ =>
  mbind (vfree lops v) (fun _ => mret 0))))))))).

Ltac readdr H e := lazymatch type of H with rw_cells _ _ ?a _ => replace a with e in H by lia end.

Section Proofs.
  Hypothesis HF : rfree_stmt.
  Hypothesis ACT : el_act_stmt.

  Lemma lftoi_back : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
      (m0 : mem) (s00 : PState) (LB : list block) (D : Z) (d : list Z) (lo B : Z) (canary : word)
      (bv : bptr) (A cap : Z) (jr : list byte) (psb ptp pim pix poc pia : bptr) (s1' : PState) (ms1 : machine_state),
    RHEAP s00 LB m0 -> lx_statics m0 -> stderr_wfile m0 -> ssp_cells m0 canary ->
    bv_unsigned sp <= B -> B < 2^62 -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - LX_FUZZ_STACK ->
    tp = wz RATP -> bv_unsigned sp mod 16 = 0 -> cap < 2^26 -> el_fd_ok d = true ->
    gate_post (bv_unsigned sp - 528) gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra F s00 LB lo B D d m0 bv A cap jr psb ptp pim pix poc pia s1' ms1 ->
    implM usegs (lftoi_rest d (cap, Z.of_nat (el_P d), Some bv) psb ptp pim pix poc pia) s1'
          (rfuzz_one_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s00 LB D d lo B canary m0) ms1.
  Proof.
    intros until ms1. intros HEAP00 LXS0 SEW0 SSP0 SPB B63 CEIL GLO LO TP AL16 CAPB FD GP.
    unfold LX_FUZZ_STACK, SJ_CLIENT_FRAMES, RMALLOC_STACK, GLOBALS_TOP in *. unfold MallocRep.wz in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    remember (bv_unsigned sp) as usp eqn:Eusp.
    remember (usp - 528) as sp0 eqn:Esp0.
    pose proof CEIL as CEIL'. unfold OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in CEIL; try (pose proof alloc_ceiling_range as CEIL_RANGE__).
    subst tp.
    unfold gate_post in GP.
    destruct GP as (x1 & t0 & t1 & t2 & xs0 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & xs3 & xs5 & xs8 & t3 & t4 & t5 & t6 & F1 & fc1 & m1 & errv1
                    & IMPL & IDX & OC & IA & TAPE & SBUF & r & e & P0 & j0 & c32 & c40 & j48 & j313 & j329 & j361 & jr28 & j416 & j441
                    & vptr & nsi & nxt & capv & md & bufv & lenv & docv & b48 & b49 & p12 & p28 & p50
                    & -> & NTH0 & ER & EIFF & FRM1 & MI1 & ST1 & ERR1 & AUX1 & FA1 & SO1 & HEAP1 & PRES1 & SJS1 & PL1 & VR1 & RES & OKR & BRTP & BRSB
                    & ELEM & PA0 & PIMPL & PA16 & DOCC & P48 & THIS & EVP & J0 & SCR2 & J48 & XSEL & XFD & SAVE).
    assert (LO0 : 0 <= lo) by (destruct ST1 as [? _]; assumption).
    assert (ELX : LX_ERRNO = 980196) by reflexivity. rewrite ELX in ERR1.
    pose proof PL1 as (PB1 & PRNG & D0 & DN & DLEN & PIN).
    assert (BLB : forall a, in_block LB a -> a < alloc_ceiling).
    { intros a (b & Hb & Hr). pose proof (LH_block_range _ _ _ _ HEAP00 Hb) as (_ & _ & _ & BC & _). unfold OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in BC. lia. }
    remember (doc_cap d) as capd eqn:Ecapd. assert (CAPD : 32 <= capd) by (subst capd; unfold doc_cap; lia).
    pose proof BRTP as (TP0 & _ & _ & TPC & TPS). pose proof BRSB as (SB0 & _ & _ & SBC & SBS). unfold OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in TPC, SBC.
    pose proof (roundup64_ge (capd + 3)) as RC2. pose proof (roundup64_ge (5 * (capd / 3) + 64)) as RC3. assert (D3 : 0 <= capd / 3) by (apply Z.div_pos; lia).
    pose proof (LH_block_range _ _ _ _ HEAP1 ltac:(do 3 right; left; reflexivity)) as (IM0 & _ & _ & IMC & IMS).
    pose proof (LH_block_range _ _ _ _ HEAP1 ltac:(do 6 right; left; reflexivity)) as (A0 & _ & _ & AC & AS).
    cbn [blk_addr blk_size fst snd] in IM0, IMC, IMS, A0, AC, AS. unfold OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in IMC, AC.
    destruct VR1 as (ELS & SZ & SV & BLK).
    rewrite EVP in THIS.
    unfold lftoi_rest.
    pose proof (munch_refl ([] : list (Z * Z)) m1) as MU. pose proof (wmono_refl usegs m1) as WM.

    destruct (e =? 0) eqn:K; [apply Z.eqb_eq in K| apply Z.eqb_neq in K].
    -
      rewrite ?unsigned_lit in K by lia. assert (R0 : r = Z_to_bv 64 0) by (apply EIFF; exact K). subst r. subst e.
      pose proof RES as RESC. unfold res_cells in RESC. rewrite (proj2 (bv_eqb_zero _) eq_refl) in RESC, ELEM.
      apply implM_gate_ok.

      destruct OKR as [KK|(E0 & tws & sbs & BT & BS & WF & RNG & LT & LS)].
      { exfalso. rewrite unsigned_lit in KK by lia. clear - KK. lia. }

      destruct (el_els_shape D d) as (P0' & P1 & rest & EE & VW0 & VW1).
      assert (EP0 : P0' = P0) by (rewrite EE in NTH0; cbn in NTH0; congruence). subst P0'.
      pose proof (el_str_len d) as S0LEN. assert (ZP : zlength (el_str d) = Z.of_nat (length (el_str d))) by reflexivity.
      set (LBall := el_blocks psb ptp pim pix poc pia bv IA OC IDX IMPL TAPE SBUF A cap capd LB) in *.
      assert (STRF : bytes_at usegs m1 P0 (map (Z_to_bv 8) (el_str d)) /\ (el_str d = [] \/ in_blocks LBall P0 (zlength (el_str d))) /\ 0 <= P0 /\ P0 + zlength (el_str d) < 2^63).
      { destruct (el_str d) as [|c l] eqn:ES.
        - assert (P0B : 0 <= P0 < 2^63).
          { destruct VW0 as [[-> _]|(o & -> & _ & BO)]; [lia|]. pose proof (el_rem_fd d FD) as [_ EL]. unfold zlength in EL, DN. lia. }
          cbn [map]. split; [apply bytes_at_nil; lia|]. split; [left; reflexivity|]. unfold zlength. cbn [length Z.of_nat]. lia.
        - rewrite <- ES in *. destruct (view_bytes _ _ _ _ _ _ PL1 FD VW0 ltac:(rewrite ES; discriminate)) as (VB & _ & (b0 & Hb0 & Hb1 & Hb2)).
          split; [exact VB|]. split; [right; exists b0; split; [subst LBall; do 7 right; exact Hb0| lia]|].
          pose proof (LH_block_range _ _ _ _ HEAP00 Hb0) as (B00 & _ & _ & B0C & _). unfold OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in B0C. lia. }
      destruct STRF as (STRB & STRIN & STR0 & STRH).
      assert (S0F : Forall (fun c => 0 <= c < 256) (el_str d)).
      { destruct VW0 as [[_ L1]|(off & _ & EQ & _)]; [rewrite L1; constructor|]. rewrite EQ. apply Forall_firstn', Forall_skipn'. pose proof (el_rem_fd d FD) as [-> _]. apply Forall_skipn'. exact PRNG. }
      set (EN := mkAE LBall lo B (sp0 + 336) TAPE SBUF tws sbs P0 (el_str d)).
      assert (OKE : aenv_ok EN).
      { subst EN. constructor; cbn [ae_LB ae_lo ae_B ae_DOC ae_TAPE ae_SBUF ae_tws ae_sbs ae_PTR ae_p1].
        - apply SjTapeTile.tape_wfS_wf. exact WF. - exact RNG. - exact S0F. - change (2^26) with 67108864; unfold zlength in *; lia.
        - exists (ptp, TAPE, 8 * roundup64 (capd + 3)). split; [subst LBall; do 4 right; left; reflexivity| cbn [blk_addr blk_size fst snd]; lia].
        - exists (psb, SBUF, roundup64 (5 * (capd / 3) + 64)). split; [subst LBall; do 5 right; left; reflexivity| cbn [blk_addr blk_size fst snd]; lia].
        - exact STRIN. - split; [exact STR0| exact STRH]. - split; [exact CEIL'| unfold GLOBALS_TOP; lia]. - (clear - B63; lia). - lia.
        - destruct BRTP as (_ & TM16 & _). split; lia. }

      pose proof (rw_cells_forget _ _ _ _ RESC) as [jres RESJ]. cbn [cells_size csize Nat.add] in RESJ. clear RESC RES.
      pose proof (rw_cells_join _ _ _ _ _ SCR2 J48 ltac:(cbn [cells_size csize Nat.add]; lia)) as OSJ'. cbn [app] in OSJ'.
      pose proof (rw_cells_forget _ _ _ _ OSJ') as [jos OSJ]. cbn [cells_size csize Nat.add] in OSJ. clear OSJ' SCR2 J48.
      destruct (rw_cells_split_at1 _ _ _ 2%nat DOCC) as [DOC2 DCAP]. cbn [firstn skipn cells_size csize Nat.add] in DOC2, DCAP. readdr DCAP (sp0 + 352).
      eapply (ACT _ _ _ x1 gp t0 t1 t2 xs0 a0 a1 a2 a3 a4 a5 a6 a7 xs3 (Z_to_bv 64 0) xs5 xs8 s9 s10 s11 t3 t4 t5 t6 s0 s1 s2 s3 s4 s5 s6 s7 s8 ra F1 fc1 m0 m1 s00 s1' LB D d sp0 lo B EN errv1
                  bv psb ptp pim pix poc pia A cap IMPL IDX OC IA jr j0 jres jos j313 j329 j361 j416 j441 nsi nxt capv md bufv lenv docv b48 b49 p12 p28 p50);
        subst EN; cbn [ae_LB ae_lo ae_B ae_DOC ae_TAPE ae_SBUF ae_tws ae_sbs ae_PTR ae_p1];
        [exact OKE| split; [exact BT| split; [exact BS| split; [exact STRB| exact DOC2]]]| subst LBall capd; reflexivity| reflexivity| reflexivity| reflexivity| reflexivity
        | exact HEAP00| exact LXS0| exact HEAP1| exact AUX1| lia| (clear - B63; lia)| exact ST1| exact CEIL'| unfold GLOBALS_TOP; lia| unfold LX_FUZZ_STACK, SJ_CLIENT_FRAMES, RMALLOC_STACK; lia
        | rewrite ELX; exact ERR1| exact MI1| rewrite Esp0; replace (usp - 528 + 528) with usp by lia; exact AL16| exact FRM1
        | exact PRES1| exact SJS1| exact PL1| exact FD
        | split; [exact ELS| split; [exact SZ| split; [exact SV| exact BLK]]]| exact NTH0
        | exact J0| exact RESJ| exact OSJ| exact ELEM| exact PA0| exact PIMPL| exact PA16| subst capd; exact DCAP| exact P48| exact THIS| exact XSEL| exact XFD| exact SAVE|].
      intros st7 ms7 PO. unfold act_post in PO. subst LBall. unfold el_blocks in PO.
      destruct PO as (z1 & u0 & u1 & u2 & y8 & y9 & y10 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & y18 & y19 & y20 & y21 & y22 & y23 & y24 & u3 & u4 & u5 & u6 & F7 & fc7 & m7 & errv7 & init7
                      & nsi7 & nxt7 & capv7 & md7 & bufv7 & lenv7 & docv7 & b487 & b497 & p127 & p287 & p507 & j3137 & j3297 & j3617 & jlo & jmid
                      & -> & HEAP7 & AUX7 & MI7 & ST7 & ERR7 & FA7 & SO7 & FRM7 & PRES7 & TPC7 & SJS7 & PL7 & LOW7 & PA07 & PIMPL7 & PA167 & DOCC7 & P487 & THIS7 & SV7 & MID7 & SAVE7).
      subst sp0 usp capd.
      eapply (exit_cps HF); try eassumption; try lia; try congruence. all: replace (bv_unsigned sp) with (bv_unsigned sp - 528 + 528) by lia; exact PRES7.
    -
      rewrite ?unsigned_lit in K by lia.
      assert (RNZ : bv_eqb r (Z_to_bv 64 0) = false).
      { destruct (bv_eqb r (Z_to_bv 64 0)) eqn:EB; [| reflexivity]. exfalso. apply K. apply EIFF. apply bv_eqb_zero. exact EB. }
      unfold res_cells in RES. rewrite RNZ in RES, ELEM.
      apply implM_gate_fail.

      pose proof (rw_cells_join _ _ _ _ _ J0 RES ltac:(cbn [cells_size csize Nat.add]; lia)) as J1.
      pose proof (rw_cells_join _ _ _ _ _ J1 SCR2 ltac:(cbn [app cells_size csize Nat.add]; lia)) as J2.
      pose proof (rw_cells_join _ _ _ _ _ J2 J48 ltac:(cbn [app cells_size csize Nat.add]; lia)) as J3.
      pose proof (rw_cells_join _ _ _ _ _ J3 ELEM ltac:(cbn [app cells_size csize Nat.add]; lia)) as J4. cbn [app] in J4.
      destruct (rw_cells_forget _ _ _ _ J4) as [jlo LOW]. cbn [cells_size csize Nat.add] in LOW.
      destruct (rw_cells_forget _ _ _ _ XSEL) as [jsel XSEL']. cbn [cells_size csize Nat.add] in XSEL'.
      pose proof (rw_cells_join _ _ _ _ _ XSEL' XFD ltac:(cbn [cells_size csize Nat.add]; lia)) as J5. cbn [app] in J5.
      destruct (rw_cells_forget _ _ _ _ J5) as [jmid MID]. cbn [cells_size csize Nat.add] in MID.
      clear J1 J2 J3 J4 J5.
      subst sp0 usp capd.

      pose proof (tp_of_pres _ _ _ _ LXS0 PRES1) as TPC1.
      eapply (exit_cps HF); try eassumption; try lia. replace (bv_unsigned sp) with (bv_unsigned sp - 528 + 528) by lia; apply pres_X3; exact PRES1.
  Qed.
End Proofs.
End WithCeiling0.
