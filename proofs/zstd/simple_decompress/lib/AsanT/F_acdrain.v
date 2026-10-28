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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import MM_syscalls WStr.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import SysStepF.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg AProto ABase AKit AKit2 AKitR ARep ARepKit ARepFrame RT_stubs
     F_apoison F_acache F_aalloc3 F_ammap F_aensure F_agetfrom F_amaybe F_areturn.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Local Ltac band_lin :=      (* [comment removed for export] *)
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.


Local Ltac ub H := let X := fresh "Y" in pose proof H as X; unbox X.

Section CANSEC1. Context {rc : runConstT}.
Definition cdrain_entry : Z := 0x362ec.
End CANSEC1.
Notation CDRAIN_STACK := 640 (only parsing).    (* [comment removed for export] *)

(* [comment removed for export] *)
Section CANSEC2. Context {rc : runConstT}.
Lemma disjoint_from_stack : forall W A k, Forall (fun iv => ATOP <= fst iv) W -> A + k <= ATOP -> disjoint_from W A k.
Proof.
  induction W as [|[lo hi] W IH]; intros A k HW LE; cbn; [exact I|].
  inversion HW; subst. cbn in *. split; [left; lia| apply IH; assumption].
Qed.

Lemma rta_ret_frame : forall L RNG sp st c n SRC lo src m st2 RNG' m2 m4,
  rta_ret L RNG sp st c n SRC lo src m st2 RNG' m2 ->
  munch [(bv_unsigned sp - 576, bv_unsigned sp)]%Z m2 m4 -> wmono bsegs m2 m4 -> ATOP <= lo -> lo <= bv_unsigned sp - 576 ->
  mem_inv bsegs m4 -> stk bsegs m4 lo (bv_unsigned sp) ->
  1 <= c < K_NUM_CLASSES -> 0 <= n -> length src = Z.to_nat n -> 0 <= c_num_freed (get_cls st c) -> 4 * (c_num_freed (get_cls st c) + n) <= K_FREEARR_MAX ->
  0x10007fff8000 <= al_space_beg L -> al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= ATOP ->
  al_t L + 4096 <= ATOP -> sclr (al_ctx L) 65536 -> al_ctx L + 4096 <= ATOP ->
  rta_ret L RNG sp st c n SRC lo src m st2 RNG' m4.
Proof.
  intros L RNG sp st c n SRC lo src m st2 RNG' m2 m4 RR MU WM CEIL LO MI4 ST4 HC N0 LS NF0 NFN SP1 SP2 T1 CX0 CX1. band_lin.   (* [comment removed for export] *)
  unfold rta_ret, K_FREEARR_MAX, K_FREEARR_MAP in *. cbv zeta in *.
  destruct RR as (FPLE & mfa' & sj' & UD & NEWB & NEWGE & NEWM & GC2 & ST2E & MU2 & WM2 & _ & _ & MTX & REG & J72 & STATS & LSJ & SRC3 & JR & AZF & MC).
  assert (RIE : aregion_info L c = al_space_beg L + 137438953472 + c * 128) by (unfold aregion_info, K_SPACE_SIZE, ARI_STRIDE; change (2^37) with 137438953472; reflexivity).
  assert (FAE : afreearr L c = al_space_beg L + c * 4294967296 + 3758096384) by (unfold afreearr, aregion, K_REGION, K_FREEARR_OFF; change (2^32) with 4294967296; reflexivity).
  unfold K_NUM_CLASSES, K_SPACE_SIZE, K_SPACE_EXTRA in *. change (2^37) with 137438953472 in *.
  assert (D : forall A k, A + k <= ATOP -> disjoint_from [(bv_unsigned sp - 576, bv_unsigned sp)]%Z A k) by (intros A k LE; cbn; split; [left; clear -LE CEIL LO; lia| exact I]).
  assert (SHF : shad (afreearr L c + c_mapped_free_array (get_cls st c)) + shlen (mfa' - c_mapped_free_array (get_cls st c)) <= 0x10007fff8000
                /\ shad (afreearr L c + mfa') + shlen (536870912 - mfa') <= 0x10007fff8000).
  { rewrite !shad_div, !shlen_div, FAE. unfold ASHOFF. clear -SP1 SP2 HC NEWB NEWGE NF0 N0. Z.div_mod_to_equations. lia. }
  destruct SHF as [SHF1 SHF2].
  split; [exact FPLE|]. exists mfa', sj'.
  split. { destruct UD as [E|(LT & E & FILL & R1 & R2 & BW)]; [left; exact E| right].
           split; [exact LT|]. split; [exact E|]. split; [| split; [exact R1| split; [exact R2| exact BW]]].
           eapply fill_frame; [exact FILL | exact MU | exact WM | intros _; apply D; clear -SHF1; lia]. }
  split; [exact NEWB|]. split; [exact NEWGE|]. split; [exact NEWM|]. split; [exact GC2|]. split; [exact ST2E|].
  split. { eapply munch_trans; [exact MU2|]. eapply munch_weaken; [| exact MU]. unfold sub_fp; cbn [outside]; clear; intros xq Hxq; lia. }
  split; [eapply wmono_trans; [exact WM2| exact WM]|]. split; [exact MI4|]. split; [exact ST4|].
  split; [eapply cells_frame; [exact MTX | exact MU | exact WM | cbn; apply D; rewrite RIE; clear -SP2 HC; lia]|].
  split; [eapply cells_frame; [exact REG | exact MU | exact WM | cbn; apply D; rewrite RIE; clear -SP2 HC; lia]|].
  split; [eapply junk_frame; [exact J72 | exact MU | exact WM | intros _; apply D; rewrite RIE; clear -SP2 HC; lia]|].
  split; [eapply u64arr_frame; [exact STATS | exact MU | exact WM | apply D; rewrite LSJ; clear -T1; lia]|].
  split; [exact LSJ|].
  split; [eapply u32arr_frame; [exact SRC3 | exact MU | exact WM | apply D; rewrite FAE, LS; clear -SP2 HC NEWB NF0 N0 NFN; lia]|].
  split; [eapply junk_frame; [exact JR | exact MU | exact WM | intros _; apply D; rewrite FAE; clear -SP2 HC NEWB NF0 N0; lia]|].
  split; [eapply azero_frame; [exact AZF | exact MU | exact WM | intros _; apply D; clear -SHF2; lia]|].
  eapply m3_cells_frame; [exact MC | exact MU | exact WM |]. unfold AIMG_HI, AIMG_LO.
  apply Forall_cons; [cbn [fst snd]; clear -CEIL LO CX0 CX1; pose proof atop_range; lia |]. apply Forall_nil.   (* [comment removed for export] *)
Qed.


(* [comment removed for export] *)
Definition cdrain_ret (L : alayout) (RNG : footprint) (sp : word) (st : astate) (c cnt mc csz lo : Z) (chunks : list word) (m : amem)
    (st2 : astate) (RNG' : footprint) (m' : amem) : Prop :=
  let half := mc / 2 in let CA := acache_addr L c in
  exists m1,
       munch [(bv_unsigned sp - 64, bv_unsigned sp); (CA, CA + 4)]%Z m m1 /\ wmono bsegs m m1
    /\ rta_ret L RNG (Z_to_bv 64 (bv_unsigned sp + -64)) st c half (CA + 16 + 4 * (cnt - half)) lo
               (firstn (Z.to_nat half) (skipn (Z.to_nat (cnt - half)) chunks)) m1 st2 RNG' m'
    /\ rw_cells bsegs m' CA [C4 (Z_to_bv 64 (cnt - half)); C4 (Z_to_bv 64 mc); C8 (Z_to_bv 64 csz)]
    /\ u32arr bsegs m' (CA + 16) chunks
    /\ stk bsegs m' lo (bv_unsigned sp).

Lemma cdrain_spec : forall RNG {R} (kb : astate -> bool -> AM R) (Q : R -> footprint -> machine_state -> Prop)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (L : alayout) (st : astate) (c cnt mc csz lo : Z) (sj chunks : list word),
  let r := get_cls st c in let RI := aregion_info L c in let FA := afreearr L c in let CA := acache_addr L c in
  let nf := c_num_freed r in let mfa := c_mapped_free_array r in let half := mc / 2 in
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - CDRAIN_STACK ->
  mem_inv bsegs m -> tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 (al_t L + 208) -> a1 = Z_to_bv 64 CA -> a2 = Z_to_bv 64 AINSTANCE -> a3 = Z_to_bv 64 c ->
  m3_cells L m ->
  rw_cells bsegs m RI [C8 (Z_to_bv 64 0)] ->
  rw_cells bsegs m (RI + 16)
     [C8 (Z_to_bv 64 nf); C8 (Z_to_bv 64 mfa); C8 (Z_to_bv 64 (c_allocated_user r)); C8 (Z_to_bv 64 0);
      C8 (Z_to_bv 64 (c_mapped_user r)); C8 (Z_to_bv 64 0)] ->
  junk_at m (RI + 72) 56 ->
  u64arr bsegs m (al_t L + 2800) sj -> length sj = 46%nat ->
  rw_cells bsegs m CA [C4 (Z_to_bv 64 cnt); C4 (Z_to_bv 64 mc); C8 (Z_to_bv 64 csz)] ->
  u32arr bsegs m (CA + 16) chunks -> length chunks = 16%nat -> Forall (fun w : word => bv_unsigned w < 2^31) (firstn (Z.to_nat cnt) chunks) ->
  junk_at m (FA + 4 * nf) (mfa - 4 * nf) ->
  azero m (shad (FA + mfa)) (shlen (K_FREEARR_MAX - mfa)) ->
  (* [comment removed for export] *)
  a_space_beg st = al_space_beg L -> 1 <= c < K_NUM_CLASSES -> 2 <= mc <= 16 -> half <= cnt <= 16 ->
  0 <= nf -> 4 * nf <= mfa <= K_FREEARR_MAX -> mfa mod K_FREEARR_MAP = 0 -> 4 * (nf + half) <= K_FREEARR_MAX ->
  0x10007fff8000 <= al_space_beg L -> al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= ATOP -> al_space_beg L mod K_ALIGN = 0 ->
  sclr (al_ctx L) 65536 -> al_ctx L + 4096 <= ATOP -> sclr (al_t L) 4096 -> al_t L + 4096 <= ATOP ->
  (al_ctx L + 4096 <= al_t L \/ al_t L + 4096 <= al_ctx L) ->
  (al_ctx L + 4096 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_ctx L) ->
  (al_t L + 4096 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_t L) ->
  (* [comment removed for export] *)
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (al_ctx L) 4096 -> rng RNG (al_t L) 4096 -> rng RNG RI 128 ->
  rng RNG FA mfa ->
  AIMG_HI <= al_ctx L ->      (* [comment removed for export] *)
  iclr (al_t L) 4096 ->      (* [comment removed for export] *)
  (forall st2 RNG' m' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      cdrain_ret L RNG sp st c cnt mc csz lo chunks m st2 RNG' m' ->
      implS bsegs RNG' (aembed ATOP (kb st2 true)) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom bsegs))) ->
  implS bsegs RNG (aembed ATOP (ensure_free_array st c (nf + half) kb)) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 cdrain_entry) fc None m (seg_rom bsegs)).
Proof.
  intros until chunks. cbv zeta.
  intros ST CEIL LO MI TP -> -> -> -> MC MTX REG J72 STATS LSJ CR CH LCH CH31 FJ AZF SBE HC MC16 CNT NF MFA MFAM NFN
         SP1 SP2 SP3 CX0 CX1 T0 T1 TCX SCX TSP RIMG RSTK RCTX RT RRI RFA CXI TIC KONT. band_lin.   (* [comment removed for export] *)
  unfold AIMG_HI, AINSTANCE, K_NUM_CLASSES, K_FREEARR_MAX, K_FREEARR_MAP, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN, cdrain_entry in *.
  change (2^37) with 137438953472 in *.
  word_range sp SPR.
  set (nf := c_num_freed (get_cls st c)) in *. set (mfa := c_mapped_free_array (get_cls st c)) in *.
  assert (CAE : acache_addr L c = al_t L + 208 + c * 80) by reflexivity.
  assert (RIE : aregion_info L c = al_space_beg L + 137438953472 + c * 128) by (unfold aregion_info, K_SPACE_SIZE, ARI_STRIDE; change (2^37) with 137438953472; reflexivity).
  assert (FAE : afreearr L c = al_space_beg L + c * 4294967296 + 3758096384) by (unfold afreearr, aregion, K_REGION, K_FREEARR_OFF; change (2^32) with 4294967296; reflexivity).
  assert (HALF : 1 <= mc / 2 <= 8) by (clear -MC16; Z.div_mod_to_equations; lia).
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (acache_addr L c, acache_addr L c + 4)]%Z m) as MUN.
  pose proof (wmono_refl bsegs m) as WM.
  box TCX. box SCX. box TSP.
  iprefix.
  carve_frame 64%nat ST.
  step. step. step. step.                                      (* [comment removed for export] *)
  step. step.                                                  (* [comment removed for export] *)
  step. step. step. step.                                      (* [comment removed for export] *)
  rewrite (sx32_lit cnt) by (clear -CNT HALF; lia). rewrite (zx32_lit mc) by (clear -MC16; lia).
  zstep. zstep. zstep.                                         (* [comment removed for export] *)
  rewrite ?(unsigned_lit mc) by (clear -MC16; lia). rewrite ?(unsigned_lit cnt) by (clear -CNT HALF; lia).
  rewrite ?Z.shiftr_div_pow2 by (clear; lia). change (2^1) with 2.
  rewrite ?(Z.mod_small cnt 4294967296) by (clear -CNT HALF; lia).
  step. if_cases KC; zify_cond KC. { exfalso. rewrite ?unsigned_lit in KC by (clear -CNT HALF MC16; lia). clear -KC CNT HALF. lia. }   (* [comment removed for export] *)
  zstep. zstep.                                                (* [comment removed for export] *)
  box MUN. snapshot [(acache_addr L c, acache_addr L c + 4)]%Z MUc WMc.
  box CH. box STATS. box MTX. box REG. box J72. box FJ. box AZF. box MC.
  step.                                                        (* [comment removed for export] *)
  carry CH MUc WMc ltac:(rewrite LCH; clear; lia).
  carry STATS MUc WMc ltac:(rewrite LSJ, CAE; clear -HC; lia).
  carry MTX MUc WMc ltac:(rewrite CAE; unfold aregion_info, K_SPACE_SIZE, ARI_STRIDE; change (2^37) with 137438953472; ub TSP; clear -HC Y; lia).
  carry REG MUc WMc ltac:(rewrite CAE; unfold aregion_info, K_SPACE_SIZE, ARI_STRIDE; change (2^37) with 137438953472; ub TSP; clear -HC Y; lia).
  unbox MUN.
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (MU01 : munch [(bv_unsigned sp - 64, bv_unsigned sp); (acache_addr L c, acache_addr L c + 4)]%Z m mm)
      by (eapply munch_trans; [eapply munch_weaken; [| exact MUN] | eapply munch_weaken; [| exact MUc]]; unfold sub_fp; cbn [outside]; clear; intros xq Hxq; lia)
  end.
  rename WM into WM01. clear MUN MUc WMc.
  unbox J72. eapply junk_frame in J72; [| exact MU01 | exact WM01 | intros _; cbn [disjoint_from]; rewrite CAE, RIE; ub TSP; clear -HC Y SPR CEIL LO SP1 SP2; lia].
  unbox FJ. eapply junk_frame in FJ; [| exact MU01 | exact WM01 | intros _; cbn [disjoint_from]; rewrite CAE, FAE; ub TSP; clear -HC Y NF MFA SPR CEIL LO SP1 SP2; lia].
  unbox AZF.
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (AZF1 : azero mm (shad (afreearr L c + mfa)) (shlen (536870912 - mfa)));
    [ eapply azero_frame; [exact AZF | exact MU01 | exact WM01 |]; intros _; cbn [disjoint_from];
      rewrite shad_div, shlen_div, CAE, FAE; unfold ASHOFF; clear -SP1 SP2 HC T0 T1 SPR CEIL LO MFA NF; pose proof atop_range as AR; unfold sclr, KLS in T0; Z.div_mod_to_equations; lia |];   (* [comment removed for export] *)
    unbox MC; assert (MC1 : m3_cells L mm);
    [ eapply m3_cells_frame; [exact MC | exact MU01 | exact WM01 |]; unfold AIMG_HI, AIMG_LO; ub TCX;
      do 2 (apply Forall_cons; [cbn [fst snd]; rewrite ?CAE; clear -T0 TIC CXI CX0 CX1 HC Y SPR CEIL LO; pose proof atop_range; lia |]); apply Forall_nil |]   (* [comment removed for export] *)
  end.
  clear AZF MC.
  zstep. zstep. zstep. zstep.                                  (* [comment removed for export] *)
  step. step. step.                                            (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  apply evtF_done.
  pose proof (u32arr_firstn _ _ _ (Z.to_nat (mc / 2)) (u32arr_skipn' _ _ chunks (Z.to_nat (cnt - mc / 2)) CH ltac:(rewrite LCH; clear -CNT HALF; lia))
                ltac:(rewrite length_skipn, LCH; clear -CNT HALF; lia)) as SRCA.
  rewrite Z2Nat.id in SRCA by (clear -CNT HALF; lia).
  name_sp sp (-64).
  eapply rta_spec with (lo := lo) (L := L) (sj := sj) (SRC := acache_addr L c + 16 + 4 * (cnt - mc / 2))
                       (src := firstn (Z.to_nat (mc / 2)) (skipn (Z.to_nat (cnt - mc / 2)) chunks));
  try lazymatch goal with
       | |- implS _ _ _ _ _ => idtac
       | |- stk _ _ _ _ => rewrite Hsp; exact ST
       | |- ATOP <= _ => atop_facts; exact CEIL
       | |- _ <= bv_unsigned _ - _ => rewrite Hsp; clear -LO; lia
       | |- mem_inv _ _ => assumption
       | |- iclr _ _ => assumption | |- AIMG_HI <= al_ctx _ => assumption   (* [comment removed for export] *)
       | |- m3_cells _ _ => exact MC1
       | |- rw_cells _ _ (aregion_info _ _) _ => exact MTX
       | |- rw_cells _ _ (aregion_info _ _ + 16) _ => exact REG
       | |- junk_at _ (aregion_info _ _ + 72) _ => exact J72
       | |- junk_at _ _ _ => exact FJ
       | |- u64arr _ _ _ _ => exact STATS
       | |- u32arr _ _ _ _ => eapply u32arr_addr_eq; [exact SRCA| clear; lia]
       | |- length _ = _ => first [exact LSJ | rewrite length_firstn, length_skipn, LCH; clear -CNT HALF; lia]
       | |- Forall _ _ => eapply Forall_firstn_skipn; [exact CH31| clear -CNT HALF; lia]
       | |- azero _ _ _ => exact AZF1
       | |- a_space_beg _ = _ => exact SBE
       | |- rng_aimg _ => exact RIMG
       | |- rng _ _ (bv_unsigned _ - _) => rewrite Hsp; solve_rng
       | |- rng _ (aregion_info _ _) _ => exact RRI
       | |- rng _ (afreearr _ _) _ => exact RFA
       | |- rng _ _ _ => solve_rng
       | |- @eq word _ _ => first [reflexivity | exact TP | rewrite ?Z.shiftl_mul_pow2 by (clear; lia); f_equal; clear; lia]
       | |- _ \/ _ => first [unboxed TCX | unboxed SCX | unboxed TSP]
       end.
  all: try (unfold K_NUM_CLASSES, K_FREEARR_MAX, K_FREEARR_MAP, K_FREEARR_OFF, K_USER_MAP, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN; change (2^37) with 137438953472;
            clear KONT; fold nf mfa; first [assumption | rewrite ?CAE; clear -NF MFA MFAM NFN HC SP1 SP2 SP3 CX0 CX1 T0 T1 CNT HALF MC16; lia]).
  (* [comment removed for export] *)
  intros st2 RNG' m2 t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' RR.
  pose proof RR as RR0. unfold rta_ret, K_FREEARR_MAX, K_FREEARR_MAP in RR0. cbv zeta in RR0. fold nf mfa in RR0.
  destruct RR0 as (FPLE & new & sj' & _ & NEWB & NEWGE & NEWM & _ & _ & MU2 & WM2 & MI2 & ST2 & _).
  rewrite Hsp in MU2, ST2. unname_sp.
  apply (rng_fp_le _ _ _ _ FPLE) in RIMG. apply (rng_fp_le _ _ _ _ FPLE) in RSTK. apply (rng_fp_le _ _ _ _ FPLE) in RT.
  assert (SHF : shad (al_space_beg L + c * 4294967296 + 3758096384 + mfa) + shlen (new - mfa) <= 0x10007fff8000).
  { rewrite !shad_div, !shlen_div. unfold ASHOFF. clear -SP1 SP2 HC MFA NF NEWB NEWGE. Z.div_mod_to_equations. lia. }
  rewrite RIE, FAE in MU2.
  assert (SHB2 : 2148256256 <= shad (al_space_beg L + c * 4294967296 + 3758096384 + mfa)) by (rewrite shad_div; unfold ASHOFF; clear -SP1 HC MFA NF; Z.div_mod_to_equations; lia).   (* [comment removed for export] *)
  pose proof T0 as T0u. unfold sclr, KLS in T0u.   (* [comment removed for export] *)
  xport FR MU2 WM2 ltac:(ub TSP; clear -SPR CEIL LO SP1 SP2 HC T0 T0u SHB2 T1 NF MFA NEWB NEWGE SHF Y; lia).
  xport CR MU2 WM2 ltac:(rewrite CAE; ub TSP; clear -SPR CEIL LO SP1 SP2 HC T0 T0u SHB2 T1 NF MFA NEWB NEWGE SHF Y; lia).
  xport CH MU2 WM2 ltac:(rewrite LCH, CAE; ub TSP; clear -SPR CEIL LO SP1 SP2 HC T0 T0u SHB2 T1 NF MFA NEWB NEWGE SHF Y; lia).
  clear ST MI MTX REG J72 STATS FJ AZF1 MC1 SRCA.
  replace (ret_pc (Z_to_bv 64 222032)) with (Z_to_bv 64 222032 : word) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  iprefix.
  snapshot [(bv_unsigned sp + -64 - 576, bv_unsigned sp + -64)]%Z MUk WMk.
  step. step. step.                                            (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  carve_frame 48%nat ST2.
  do 5 step.                                                   (* [comment removed for export] *)
  step. if_lit.                                                (* [comment removed for export] *)
  do 6 step.                                                   (* [comment removed for export] *)
  lazymatch goal with FRM : rw_cells bsegs ?mm (bv_unsigned sp + -112) _, STK : stk bsegs _ lo _ |- _ => release_frame FRM STK (bv_unsigned sp + -64) end.
  step. step. step.                                            (* [comment removed for export] *)
  lazymatch goal with FRM : rw_cells bsegs ?mm (bv_unsigned sp + -64) _, STK : stk bsegs _ lo _ |- _ => release_frame FRM STK (bv_unsigned sp) end.
  apply evtF_done. eapply KONT.
  unfold cdrain_ret. cbv zeta.
  exists m1.
  split; [exact MU01|]. split; [exact WM01|].
  split.
  { lazymatch goal with H : mem_inv bsegs ?mm, STK : stk bsegs ?mm lo _ |- rta_ret _ _ _ _ _ _ _ _ _ _ _ _ ?mm =>
      eapply rta_ret_frame;
      [ exact RR
      | eapply munch_weaken; [| exact MUk]; unfold sub_fp; cbn [outside]; rewrite ?unsigned_lit by (clear -SPR CEIL LO; lia); clear; intros xq Hxq; lia
      | exact WMk | atop_facts; exact CEIL | rewrite unsigned_lit by (clear -SPR CEIL LO; lia); clear -LO; lia | exact H
      | rewrite unsigned_lit by (clear -SPR CEIL LO; lia); exact (proj1 (stk_split bsegs _ lo (bv_unsigned sp + -64) (bv_unsigned sp) STK ltac:(clear -SPR CEIL LO; lia)))
      | unfold K_NUM_CLASSES; exact HC | clear -HALF; lia | rewrite length_firstn, length_skipn, LCH; clear -CNT HALF; lia
      | exact NF | unfold K_FREEARR_MAX; exact NFN | exact SP1 | unfold K_SPACE_SIZE, K_SPACE_EXTRA; change (2^37) with 137438953472; exact SP2
      | atop_facts; exact T1 | exact CX0 | atop_facts; exact CX1 ]
    end. }
  split; [exact CR|]. split; [exact CH|]. assumption.
Qed.
End CANSEC2.
