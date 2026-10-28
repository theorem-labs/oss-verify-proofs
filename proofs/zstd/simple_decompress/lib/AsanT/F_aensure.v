(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode SysStep.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import MM_syscalls.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import SysStepF.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg AProto ABase AKit AKit2 ARep ARepFrame RT_stubs F_apoison F_aalloc3 F_ammap.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Local Ltac band_keep :=
  ltac2:(Ltac2.Control.enter (fun () =>
    let keep := [@CEIL; @LO; @HC; @MFA; @NF4; @SP1; @SP2; @RU1; @RU2; @LSJ; @CX1; @CX2; @T1; @T2; @SHF1; @SHF2; @SHF3; @Hsp; @H] in
    let ids := Ltac2.List.map_filter (fun h => let (id, body, ty) := h in
                 match body with
                 | Ltac2.Init.Some _ => Ltac2.Init.None
                 | Ltac2.Init.None =>
                     if Ltac2.List.exist (Ltac2.Ident.equal id) keep then Ltac2.Init.None
                     else match Ltac2.Env.get [id] with
                          | Ltac2.Init.Some _ => Ltac2.Init.None          (* [comment removed for export] *)
                          | Ltac2.Init.None => if Ltac2.Constr.equal (Ltac2.Constr.type ty) constr:(Prop) then Ltac2.Init.Some id else Ltac2.Init.None
                          end
                 end) (Ltac2.Control.hyps ()) in
    Ltac2.Std.clear ids)).
Local Ltac OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib.Step.slia ::=
  first [ exact I
        | lazymatch goal with |- context [shad _] => idtac | |- ~ _ /\ _ => idtac end; band_keep; lia
        | lia | split; [lia|exact I] ].
(* [comment removed for export] *)
Local Ltac band_lin :=      (* [comment removed for export] *)
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.


Local Ltac ub H := let X := fresh "Y" in pose proof H as X; unbox X.
Local Ltac aload ST8 i AEXPR :=
  lazymatch type of ST8 with u64arr _ ?mm ?A ?ws =>
    let RD := fresh "RD" in
    pose proof (u64arr_read bsegs mm A ws i (nth (Z.to_nat i) ws w0) (wa AEXPR) ST8
                  ltac:(apply nth_error_nth'; rewrite ?upd_length; lia) ltac:(lia) ltac:(f_equal; lia)) as RD;
    step; clear RD
  end.
Local Ltac astore ST8 i :=
  lazymatch type of ST8 with u64arr _ ?mm ?A ?ws =>
    let SOK := fresh "SOK" in
    pose proof (u64arr_store_ok bsegs mm A ws i (wa (A + 8 * i)) ST8 ltac:(rewrite ?upd_length; lia) eq_refl) as SOK;
    step;
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ (wa ?E) (le8 ?v)) _) =>
      let S2 := fresh "STATS" in
      pose proof (u64arr_write bsegs mm A ws i v ST8 ltac:(rewrite ?upd_length; lia)) as S2;
      replace (A + 8 * i)%Z with E in S2 by lia;
      clear ST8; store_done; try clear SOK; rename S2 into ST8
    end
  end.

Section CANSEC1. Context {rc : runConstT}.
Definition ensure_entry := 0x367b8.
End CANSEC1.
Notation ENSURE_STACK := 448 (only parsing).    (* [comment removed for export] *)

(* [comment removed for export] *)
Section CANSEC2. Context {rc : runConstT}.
Definition m3_cells (L : alayout) (m : amem) : Prop :=
     poison_cells m /\ rmap_cells m
  /\ rw_cells bsegs m 0xcf560 [C1 (Z_to_bv 8 1)] /\ rw_cells bsegs m 0xcf564 [C4 (Z_to_bv 64 0)]
  /\ rw_cells bsegs m ATP88 [C8 (Z_to_bv 64 ATSD)] /\ rw_cells bsegs m ATSD [C8 (Z_to_bv 64 (al_ctx L))]
  /\ rw_cells bsegs m (al_ctx L + 152) [C8 (Z_to_bv 64 (al_t L))]
  /\ rw_cells bsegs m 0xcc6b8 [C8 (Z_to_bv 64 (al_space_beg L))]                      (* [comment removed for export] *)
  /\ rw_cells bsegs m 0xcc6c0 [C4 (Z_to_bv 64 4294967295)]                            (* [comment removed for export] *)
  /\ rw_cells bsegs m 0xcc6c8 [C8 (Z_to_bv 64 (al_space_beg L + K_SPACE_SIZE))]       (* [comment removed for export] *)
  /\ rw_cells bsegs m 0xcc6d0 [C1 (Z_to_bv 8 0)].                                      (* [comment removed for export] *)

Lemma m3_cells_frame : forall L m m' W, m3_cells L m -> munch W m m' -> wmono bsegs m m' ->
  Forall (fun iv => (AIMG_HI <= fst iv \/ snd iv <= AIMG_LO) /\ (snd iv <= al_ctx L + 152 \/ al_ctx L + 160 <= fst iv)) W -> m3_cells L m'.
Proof.
  intros L m m' W (PC & RC & C1' & C2 & C3 & C4' & C5 & C6 & C7 & C8' & C9) MU WM HW.
  assert (D : forall A k, 0 <= k -> A + k <= 0x625000 -> 0x10000 <= A -> disjoint_from W A k).   (* [comment removed for export] *)
  { clear -HW. intros A k Hk HA HA0. unfold AIMG_HI, AIMG_LO in HW. induction W as [|[lo hi] W IH]; cbn; [exact I|]. inversion HW; subst. cbn in *. split; [lia| apply IH; assumption]. }
  assert (DC : disjoint_from W (al_ctx L + 152) 8).
  { clear -HW. unfold AIMG_HI, AIMG_LO in HW. induction W as [|[lo hi] W IH]; cbn; [exact I|]. inversion HW; subst. cbn in *. split; [lia| apply IH; assumption]. }
  destruct PC as (P1 & P2 & P3 & P4 & P5 & P6 & P7). destruct RC as (Q1 & Q2 & Q3 & Q4 & Q5).
  split; [unfold poison_cells; repeat lazymatch goal with |- _ /\ _ => split end;
    (eapply rw_cells_transport; [eassumption | exact MU | exact WM | cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add]; apply D; lia])|].
  split; [unfold rmap_cells; repeat lazymatch goal with |- _ /\ _ => split end;
    (eapply rw_cells_transport; [eassumption | exact MU | exact WM | cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add]; apply D; lia])|].
  unfold ATP88, ATSD in *.
  repeat lazymatch goal with |- _ /\ _ => split end;
    (eapply rw_cells_transport; [eassumption | exact MU | exact WM | cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; first [exact DC | apply D; lia]]).
Qed.

Lemma m3_cells_frame_rc : forall L m m' W, m3_cells L m -> munch W m m' -> wmono bsegs m m' ->
  Forall (fun iv => (AIMG_HI <= fst iv \/ snd iv <= AIMG_LO) /\ (snd iv <= al_ctx L + 152 \/ al_ctx L + 160 <= fst iv)) W -> rmap_cells m'.
Proof. intros L m m' W MC MU WM HW. exact (proj1 (proj2 (m3_cells_frame L m m' W MC MU WM HW))). Qed.

(* [comment removed for export] *)
Definition ensure_ret (L : alayout) (RNG : footprint) (sp : word) (st : astate) (c nf lo : Z) (sj : list word) (m : amem)
    (st2 : astate) (RNG' : footprint) (m' : amem) : Prop :=
  let r := get_cls st c in let FA := afreearr L c in let mfa := c_mapped_free_array r in
  fp_le RNG RNG' /\
  exists new sj',
     (   (4 * nf <= mfa /\ new = mfa /\ st2 = st /\ RNG' = RNG)
      \/ (mfa < 4 * nf /\ new = rup (4 * nf) K_FREEARR_MAP /\ st2 = put_cls c (cls_set_mapped_free_array new r) st
          /\ rw_cells bsegs m' (FA + mfa) [CB (Z.to_nat (new - mfa)) (repeat (Z_to_bv 8 0) (Z.to_nat (new - mfa)))]
          /\ fill_at m' (shad (FA + mfa)) (shlen (new - mfa)) 0xfa
          /\ rng RNG' (FA + mfa) (new - mfa) /\ rng RNG' (shad (FA + mfa)) (shlen (new - mfa)) /\ fp_bw RNG'))
  /\ 4 * nf <= new <= K_FREEARR_MAX /\ mfa <= new /\ new mod K_FREEARR_MAP = 0
  /\ munch [(bv_unsigned sp - ENSURE_STACK, bv_unsigned sp); (FA + mfa, FA + new); (shad (FA + mfa), shad (FA + mfa) + shlen (new - mfa));
            (al_t L + 2800, al_t L + 3168); (aregion_info L c + 24, aregion_info L c + 32)]%Z m m'
  /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)
  /\ rw_cells bsegs m' (aregion_info L c + 16)
       [C8 (Z_to_bv 64 (c_num_freed r)); C8 (Z_to_bv 64 new); C8 (Z_to_bv 64 (c_allocated_user r)); C8 (Z_to_bv 64 0);
        C8 (Z_to_bv 64 (c_mapped_user r)); C8 (Z_to_bv 64 0)]
  /\ u64arr bsegs m' (al_t L + 2800) sj' /\ length sj' = 46%nat
  /\ azero m' (shad (FA + new)) (shlen (K_FREEARR_MAX - new))
  /\ m3_cells L m'.

Lemma rup18_facts : forall x, 0 <= x -> x <= rup x 262144 <= x + 262143 /\ rup x 262144 mod 262144 = 0 /\ (x mod 262144 = 0 -> rup x 262144 = x).
Proof. intros x Hx. unfold rup. Z.div_mod_to_equations. lia. Qed.

Lemma ensure_spec : forall RNG {R} (k : astate -> bool -> AM R) (Q : R -> footprint -> machine_state -> Prop)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (L : alayout) (st : astate) (c nf lo : Z) (sj : list word),
  let r := get_cls st c in let RI := aregion_info L c in let FA := afreearr L c in let mfa := c_mapped_free_array r in
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - ENSURE_STACK ->
  mem_inv bsegs m -> tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 AINSTANCE -> a1 = Z_to_bv 64 RI -> a2 = Z_to_bv 64 (aregion L c) -> a3 = Z_to_bv 64 nf ->
  m3_cells L m ->
  rw_cells bsegs m (RI + 16)
     [C8 (Z_to_bv 64 (c_num_freed r)); C8 (Z_to_bv 64 mfa); C8 (Z_to_bv 64 (c_allocated_user r)); C8 (Z_to_bv 64 0);
      C8 (Z_to_bv 64 (c_mapped_user r)); C8 (Z_to_bv 64 0)] ->
  u64arr bsegs m (al_t L + 2800) sj -> length sj = 46%nat ->
  azero m (shad (FA + mfa)) (shlen (K_FREEARR_MAX - mfa)) ->
  (* [comment removed for export] *)
  a_space_beg st = al_space_beg L -> 1 <= c < K_NUM_CLASSES ->
  0 <= mfa <= K_FREEARR_MAX -> mfa mod K_FREEARR_MAP = 0 -> 0 <= nf -> 4 * nf <= K_FREEARR_MAX ->
  0x10007fff8000 <= al_space_beg L -> al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= ATOP -> al_space_beg L mod K_ALIGN = 0 ->
  sclr (al_ctx L) 65536 -> al_ctx L + 4096 <= ATOP -> sclr (al_t L) 4096 -> al_t L + 4096 <= ATOP ->
  (al_ctx L + 4096 <= al_t L \/ al_t L + 4096 <= al_ctx L) ->
  (al_ctx L + 4096 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_ctx L) ->
  (al_t L + 4096 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_t L) ->
  (* [comment removed for export] *)
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (al_ctx L) 4096 -> rng RNG (al_t L) 4096 -> rng RNG RI 128 ->
  AIMG_HI <= al_ctx L ->      (* [comment removed for export] *)
  iclr (al_t L) 4096 ->      (* [comment removed for export] *)
  (forall st2 RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      ensure_ret L RNG sp st c nf lo sj m st2 RNG' m' ->
      implS bsegs RNG' (aembed ATOP (k st2 true)) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 1) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom bsegs))) ->
  implS bsegs RNG (aembed ATOP (ensure_free_array st c nf k)) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 ensure_entry) fc None m (seg_rom bsegs)).
Proof.
  intros until sj. cbv zeta.
  intros ST CEIL LO MI TP -> -> -> -> MC REG STATS LSJ AZ SBE HC MFA MFAM NF NF4 SP1 SP2 SP3 CX0 CX1 T0 T1 TCX SCX TSP RIMG RSTK RCTX RT RRI CXI TIC KONT. band_lin.   (* [comment removed for export] *)
  box TCX. box SCX. box TSP.
  pose proof MC as MC0. destruct MC0 as (PC & RC & TI & TK & T88 & TSD & CT & ISB & IREL & ISE & IPRE).
  unfold AIMG_HI, AINSTANCE, ATP88, ATSD, K_NUM_CLASSES, K_FREEARR_MAX, K_FREEARR_MAP, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN, ensure_entry in *.
  change (2^37) with 137438953472 in *.
  word_range sp SPR.
  set (mfa := c_mapped_free_array (get_cls st c)) in *.
  assert (RIE : aregion_info L c = al_space_beg L + 137438953472 + c * 128) by (unfold aregion_info, K_SPACE_SIZE, ARI_STRIDE; change (2^37) with 137438953472; reflexivity).
  assert (FAE : afreearr L c = al_space_beg L + c * 4294967296 + 3758096384) by (unfold afreearr, aregion, K_REGION, K_FREEARR_OFF; change (2^32) with 4294967296; reflexivity).
  pose proof (munch_refl [(bv_unsigned sp - ENSURE_STACK, bv_unsigned sp)]%Z m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  iprefix.
  carve_frame 48%nat ST.
  step. step. step. step. step. step.                          (* [comment removed for export] *)
  rewrite RIE in REG |- *. rewrite FAE in AZ.
  step.                                                        (* [comment removed for export] *)
  zstep. step.                                                 (* [comment removed for export] *)
  step. if_cases KE; zify_cond KE.                             (* [comment removed for export] *)
  { (* [comment removed for export] *)
    assert (KE' : 4 * nf <= mfa) by (rewrite Z.shiftl_mul_pow2, Z.mod_small in KE by (clear -NF NF4; lia); clear -KE; lia). clear KE.
    step. step. step. step. step. step. step. step.            (* [comment removed for export] *)
    lazymatch goal with FRM : rw_cells bsegs ?mm (bv_unsigned sp + -48) _, STK : stk bsegs _ lo _ |- _ => release_frame FRM STK (bv_unsigned sp) end.
    apply evtF_done. unfold ensure_free_array.
    replace (nf * 4 <=? c_mapped_free_array (get_cls st c)) with true by (symmetry; apply Z.leb_le; fold mfa; clear -KE'; lia).
    eapply KONT. unfold ensure_ret, K_FREEARR_MAX, K_FREEARR_MAP. cbv zeta. fold mfa. split; [apply fp_le_refl|].
    exists mfa, sj. split; [left; split; [exact KE'| split; [reflexivity| split; reflexivity]]|].
    split; [clear -KE' MFA NF4; lia|]. split; [clear; lia|]. split; [exact MFAM|].
    rewrite FAE, RIE.
    split. { eapply munch_weaken; [| exact MU]. unfold sub_fp. cbn [outside]. clear. intros x Hx. tauto. } split; [assumption|]. split; [assumption|]. split; [assumption|].
    split; [assumption|]. split; [assumption|]. split; [exact LSJ|].
    split.
    - eapply azero_frame; [exact AZ | exact MU | exact WM |]. intros Hp. cbn [disjoint_from].
      assert (SHR : 0x2008fff7000 <= shad (al_space_beg L + c * 4294967296 + 3758096384 + mfa)
                    /\ shad (al_space_beg L + c * 4294967296 + 3758096384 + mfa) + shlen (536870912 - mfa) <= 0x10007fff8000).
      { rewrite shad_div, shlen_div. unfold ASHOFF. clear -SP1 SP2 HC MFA. Z.div_mod_to_equations. lia. }
      clear -SHR CEIL LO. split; [lia| exact I].
    - eapply m3_cells_frame; [exact MC | exact MU | exact WM |].
      apply Forall_cons; [cbn [fst snd]; clear -CEIL LO CX1; unfold AIMG_HI, AIMG_LO; lia | apply Forall_nil]. }
  (* [comment removed for export] *)
  assert (KE' : mfa < 4 * nf) by (rewrite Z.shiftl_mul_pow2, Z.mod_small in KE by (clear -NF NF4; lia); clear -KE; lia). clear KE.
  pose proof (rup18_facts (4 * nf) ltac:(clear -NF; lia)) as (RU1 & RU2 & RU3).
  set (new := rup (4 * nf) 262144) in *.
  zstep. zstep. zstep. zstep. zstep.                           (* [comment removed for export] *)
  setreg 8 (Z_to_bv 64 new) ltac:(rewrite Z.shiftl_mul_pow2, land_align2p18 by (clear -NF NF4; lia); f_equal;
                                   subst new; unfold rup; clear -NF NF4; Z.div_mod_to_equations; lia).
  zstep. zstep. step. if_cases KC; zify_cond KC. { exfalso. clear -KC RU1 RU2 NF4. Z.div_mod_to_equations. lia. }   (* [comment removed for export] *)
  lstep.                                                       (* [comment removed for export] *)
  zstep. zstep. zstep. zstep.                                  (* [comment removed for export] *)
  unfold aregion, K_REGION. change (2^32) with 4294967296.
  setreg 9 (Z_to_bv 64 (al_space_beg L + c * 4294967296 + 3758096384 + mfa)) ltac:(f_equal; clear; lia).
  step. if_lit.                                                (* [comment removed for export] *)
  step. zstep. step. step. step. step.                         (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  (* [comment removed for export] *)
  apply evtF_done. unfold ensure_free_array.
  replace (nf * 4 <=? c_mapped_free_array (get_cls st c)) with false by (symmetry; apply Z.leb_gt; fold mfa; clear -KE'; lia).
  replace (rup (nf * 4) K_FREEARR_MAP) with new by (subst new; unfold K_FREEARR_MAP; f_equal; clear; lia).
  replace (K_FREEARR_MAX <? new) with false by (symmetry; apply Z.ltb_ge; unfold K_FREEARR_MAX; clear -KC; lia).
  cbv iota. unfold ev. rewrite aembed_vis. cbn [aev_tree]. unfold PROT_RW, F_FIXED.
  unfold region_beg, K_REGION, K_FREEARR_OFF. change (2^32) with 4294967296. rewrite SBE. fold mfa.
  set (FAM := al_space_beg L + c * 4294967296 + 3758096384 + mfa) in *.
  assert (FAM8 : FAM mod 4096 = 0 /\ 0x10007fff8000 <= FAM /\ FAM + (new - mfa) <= al_space_beg L + 137438953472 /\ (new - mfa) mod 4096 = 0 /\ 0 < new - mfa).
  { subst FAM. clear -SP1 SP3 HC MFA MFAM KE' RU1 RU2 KC NF. Z.div_mod_to_equations. lia. }
  destruct FAM8 as (FA1 & FA2 & FA3 & FA4 & FA5).
  assert (FA0 : al_space_beg L + 4096 <= FAM) by (unfold FAM; clear -HC MFA; lia).
  name_sp sp (-48).
  eapply rmap_spec with (addr := FAM) (size := new - mfa) (lo := lo).
  all: try lazymatch goal with
       | |- stk _ _ _ _ => rewrite Hsp; eassumption
       | |- ATOP <= _ => atop_facts; exact CEIL
       | |- _ <= bv_unsigned _ - _ => rewrite Hsp; clear -LO; lia
       | |- mem_inv _ _ => assumption
       | |- rmap_cells _ => eapply m3_cells_frame_rc; [exact MC | exact MU | exact WM | apply Forall_cons; [cbn [fst snd]; clear -CEIL LO CX1; unfold AIMG_HI, AIMG_LO; lia | apply Forall_nil]]
       | |- rng_aimg _ => exact RIMG
       | |- rng _ _ _ => solve_rng
       | |- @eq word _ _ => reflexivity
       | |- _ mod 4096 = 0 => assumption
       | |- 0 < _ - _ => exact FA5
       end.
  all: try (unfold AIMG_HI; clear -FA1 FA2 FA3 FA4 FA5 SP2 CEIL LO; rewrite ?unsigned_lit by lia; lia).
  { (* [comment removed for export] *)
    intros a RNG' ms' NE P1 P2. unfold fixed_answer_ok, is_err, TWO64.
    replace (2 ^ 64 - 4096 <? a) with false by (symmetry; apply Z.ltb_ge; clear -P2 FA5; atop_facts; lia).
    replace (a =? FAM) with false by (symmetry; apply Z.eqb_neq; exact NE). cbn [negb orb]. rewrite aembed_aundef_. apply implF_ret_unr. }
  (* [comment removed for export] *)
  intros RNG' m2 t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' RP.
  destruct RP as (FPLE & _ & MU2 & WM2 & MI2 & ST2 & ZNEW & GR1 & GR2 & BW & RC2). unname_sp.
  (* [comment removed for export] *)
  apply (rng_fp_le _ _ _ _ FPLE) in RIMG. apply (rng_fp_le _ _ _ _ FPLE) in RSTK. apply (rng_fp_le _ _ _ _ FPLE) in RCTX.
  apply (rng_fp_le _ _ _ _ FPLE) in RT. apply (rng_fp_le _ _ _ _ FPLE) in RRI.
  (* [comment removed for export] *)
  xport FR MU2 WM2 ltac:(clear -SPR CEIL LO FA2 FA3 SP2; lia).
  xport REG MU2 WM2 ltac:(clear -SPR CEIL LO FA2 FA3 SP2 HC; lia).
  xport STATS MU2 WM2 ltac:(rewrite LSJ; ub TSP; clear -SPR CEIL LO FA0 FA2 FA3 SP2 T0 T1 Y; lia).
  clear ST. rename ST2 into ST.
  assert (AZ2 : azero m2 (shad FAM) (shlen (536870912 - mfa))).
  { eapply azero_frame; [eapply azero_frame; [exact AZ | exact MU | exact WM |] | exact MU2 | exact WM2 |];
      intros _; cbn [disjoint_from]; subst FAM; rewrite ?shad_div, ?shlen_div; unfold ASHOFF;
      clear -SPR CEIL LO SP1 SP2 HC MFA KC RU1 KE'; Z.div_mod_to_equations; lia. }
  assert (MUF : munch [(bv_unsigned sp - ENSURE_STACK, bv_unsigned sp); (FAM, FAM + (new - mfa)); (shad FAM, shad FAM + shlen (new - mfa));
                       (al_t L + 2800, al_t L + 3168); (al_space_beg L + 137438953472 + c * 128 + 24, al_space_beg L + 137438953472 + c * 128 + 32)]%Z m m2).
  { eapply munch_trans; [eapply munch_weaken; [| exact MU] | eapply munch_weaken; [| exact MU2]]; unfold sub_fp; cbn [outside]; clear; intros x Hx; lia. }
  clear MU MU2. pose proof (wmono_trans _ _ _ _ WM WM2) as WMF. clear WM WM2.
  assert (WOK : Forall (fun iv => (AIMG_HI <= fst iv \/ snd iv <= AIMG_LO) /\ (snd iv <= al_ctx L + 152 \/ al_ctx L + 160 <= fst iv))
           [(bv_unsigned sp - ENSURE_STACK, bv_unsigned sp); (FAM, FAM + (new - mfa)); (shad FAM, shad FAM + shlen (new - mfa));
            (al_t L + 2800, al_t L + 3168); (al_space_beg L + 137438953472 + c * 128 + 24, al_space_beg L + 137438953472 + c * 128 + 32)]%Z).
  { ub TCX. ub SCX. unfold AIMG_HI, AIMG_LO.
    do 5 (apply Forall_cons; [cbn [fst snd]; clear -CEIL LO CX0 CX1 T0 T1 TIC SP1 SP2 HC MFA FA0 FA2 FA3 KC Y Y0;
                              with_band CX0 ltac:(rewrite ?shad_div, ?shlen_div; unfold ASHOFF; split; Z.div_mod_to_equations; lia) |]). apply Forall_nil. }   (* [comment removed for export] *)
  pose proof (m3_cells_frame L m m2 _ MC MUF WMF WOK) as MC2.
  clear TI TK T88 TSD CT ISB IREL ISE IPRE.
  pose proof MC2 as MC2'. destruct MC2' as (PC2 & _ & TI & TK & T88 & TSD & CT & ISB & IREL & ISE & IPRE). unfold ATP88, ATSD in T88, TSD.
  (* [comment removed for export] *)
  replace (ret_pc (Z_to_bv 64 223320)) with (Z_to_bv 64 223320 : word) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  iprefix.
  step. if_cases K1; zify_cond K1. { exfalso. clear -K1 FA2 FA3 SP2. rewrite ?unsigned_lit in K1 by lia. lia. }   (* [comment removed for export] *)
  step. step. if_cases K2; zify_cond K2. { exfalso. clear -K2. lia. }                                                (* [comment removed for export] *)
  step. step. step.                                            (* [comment removed for export] *)
  pose proof (azero_cb m2 _ _ (shlen (new - mfa)) AZ2 ltac:(rewrite !shlen_div; clear -MFA KC KE' RU1; Z.div_mod_to_equations; lia)) as SHCB.
  clear AZ2.
  assert (SHF : 0x2008fff7000 <= shad FAM /\ shad FAM + shlen (new - mfa) <= 0x10007fff8000 /\ 0 < shlen (new - mfa)).
  { rewrite shad_div, shlen_div. unfold ASHOFF. clear -FA2 FA3 FA4 FA5 SP2. Z.div_mod_to_equations. lia. }
  destruct SHF as (SHF1 & SHF2 & SHF3).
  step. with_band CX0 ltac:(with_band T0 ltac:(call_sp (poison_shadow_spec RNG' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FAM (new - mfa) 250 lo))).   (* [comment removed for export] *)
  all: try lazymatch goal with
       | |- evtF _ _ _ _ => idtac
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- ablk _ _ => first [assumption | unfold ablk; right; clear -FA2 FA3 SP2; lia]   (* [comment removed for export] *)
       | |- stk _ _ _ _ => eassumption
       | |- mem_inv _ _ => assumption
       | |- poison_cells _ => exact PC2
       | |- @eq word _ _ => reflexivity
       | |- rw_cells _ _ (shad _) _ => exact SHCB
       | |- rng _ (shad _) _ => exact GR2
       | |- rng _ _ _ => solve_rng
       end.
  all: try (atop_facts; clear -FA1 FA2 FA3 FA4 FA5 SP2 CEIL LO KC RU1 KE' MFA; rewrite ?shlen_div; first [lia | Z.div_mod_to_equations; lia]).
  (* [comment removed for export] *)
  step. with_band T0 ltac:(call_sp (thread_stats_spec RNG' (al_ctx L) (al_t L) lo)).   (* [comment removed for export] *)
  all: try lazymatch goal with
       | |- evtF _ _ _ _ => idtac
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- ablk _ _ => assumption   (* [comment removed for export] *)
       | |- stk _ _ _ _ => eassumption
       | |- mem_inv _ _ => assumption
       | |- @eq word _ _ => first [reflexivity | exact TP]
       | |- rw_cells _ _ _ _ => assumption
       | |- rng _ _ _ => solve_rng
       end.
  all: try (unfold AIMG_HI; clear -CEIL LO CX0 CX1 T0 T1 CXI TIC; lia).
  all: match goal with |- ?G => idtac "REMT" G end.
  aload STATS 10 (al_t L + 2800 + 80). aload STATS 9 (al_t L + 2800 + 72).
  zstep. zstep.                                                (* [comment removed for export] *)
  snapshot [(al_t L + 2800, al_t L + 3168)]%Z MUs WMs.
  box CT. box ZNEW. box REG.
  lazymatch goal with P : rw_cells bsegs _ (shad FAM) _ |- _ => rename P into SHPO end. box SHPO.   (* [comment removed for export] *)
  astore STATS 9. astore STATS 10.
  carry SHPO MUs WMs ltac:(with_band T0 ltac:(lia)).
  carry REG MUs WMs ltac:(ub TSP; clear -HC T0 T1 SP1 SP2 Y; lia).
  carry CT MUs WMs ltac:(ub TCX; clear -HC CX0 CX1 T0 T1 Y; lia).
  carry ZNEW MUs WMs ltac:(ub TSP; clear -HC T0 T1 SP1 SP2 FA0 FA2 FA3 FA5 Y; lia).
  clear MUs WMs.
  snapshot [(al_space_beg L + 137438953472 + c * 128 + 24, al_space_beg L + 137438953472 + c * 128 + 32)]%Z MUr WMr.
  box CT. box ZNEW. box STATS.
  step. step.                                                  (* [comment removed for export] *)
  carry CT MUr WMr ltac:(ub SCX; clear -HC CX0 CX1 SP1 SP2 Y; lia).
  carry ZNEW MUr WMr ltac:(clear -HC SP1 SP2 FA0 FA2 FA3 FA5; lia).
  carry STATS MUr WMr ltac:(rewrite ?upd_length, LSJ; ub TSP; clear -HC T0 T1 SP1 SP2 Y; lia).
  clear MUr WMr.
  step. step.                                                  (* [comment removed for export] *)
  step. step. step. step. step. step. step.                    (* [comment removed for export] *)
  lazymatch goal with FRM : rw_cells bsegs ?mm (bv_unsigned sp + -48) _, STK : stk bsegs _ lo _ |- _ => release_frame FRM STK (bv_unsigned sp) end.
  apply evtF_done.
  unfold fixed_answer_ok, is_err, TWO64. rewrite Z.eqb_refl.
  replace (2 ^ 64 - 4096 <? FAM) with false by (symmetry; apply Z.ltb_ge; clear -FA3 FA5 SP2; lia). cbn [negb orb].
  eapply KONT. unfold ensure_ret, K_FREEARR_MAX, K_FREEARR_MAP. cbv zeta. fold mfa. split; [exact FPLE|].
  lazymatch goal with |- context [u64arr bsegs _ _ ?ws] => idtac | H : u64arr bsegs _ (al_t L + 2800) ?ws |- _ => exists new, ws end.
  rewrite FAE, RIE. fold FAM.
  split. { right. split; [exact KE'|]. split; [subst new; f_equal; clear; lia|]. split; [reflexivity|].
           split; [exact ZNEW|]. split; [assumption|]. split; [exact GR1|]. split; [exact GR2| exact BW]. }
  split; [clear -RU1 KC; lia|]. split; [clear -RU1 KE'; lia|]. split; [exact RU2|].
  split. { eapply munch_weaken; [| exact MUF]. unfold sub_fp, FAM. cbn [outside]. clear. intros x Hx. lia. }
  split; [assumption|]. split; [assumption|]. split; [assumption|].
  split; [assumption|]. split; [assumption|]. split; [rewrite ?upd_length; exact LSJ|].
  split.
  { pose proof (azero_split m _ _ (shlen (new - mfa)) AZ ltac:(rewrite !shlen_div; clear -MFA KC KE' RU1; Z.div_mod_to_equations; lia)) as AZT.
    replace (shad FAM + shlen (new - mfa)) with (shad (FAM + (new - mfa))) in AZT by (apply shad_add_shlen; clear -FA1; Z.div_mod_to_equations; lia).
    replace (shlen (536870912 - mfa) - shlen (new - mfa)) with (shlen (536870912 - new)) in AZT by (rewrite !shlen_div; clear -FA4 MFAM RU2 MFA; Z.div_mod_to_equations; lia).
    replace (al_space_beg L + c * 4294967296 + 3758096384 + new) with (FAM + (new - mfa)) by (unfold FAM; clear; lia).
    eapply azero_frame; [exact AZT | exact MUF | exact WMF |]. intros Hp. cbn [disjoint_from].
    pose proof (shad_add_shlen FAM (new - mfa) ltac:(clear -FA1; Z.div_mod_to_equations; lia)) as SE.
    assert (SHT : shad (FAM + (new - mfa)) + shlen (536870912 - new) <= 0x10007fff8000).
    { rewrite shad_div, shlen_div. unfold ASHOFF, FAM. clear -SP2 KC RU1 MFA HC KE'. Z.div_mod_to_equations. lia. }
    clear -SE SHT SHF1 SHF2 SHF3 CEIL LO FA2 FA3 FA5 T0 SP1 SP2 HC. with_band T0 ltac:(repeat split; lia). }   (* [comment removed for export] *)
  eapply m3_cells_frame; [exact MC | eassumption | eassumption | exact WOK].
Qed.
End CANSEC2.
