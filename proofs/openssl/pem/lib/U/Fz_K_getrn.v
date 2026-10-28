(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Ubs.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import MallocBlocks Malloc_iface ClientOwn LhPure.
From OssFuzzTheorems.Proofs.openssl.pem.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface RMalloc_ifaceP.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import Prelim STree Malloc Monad Stdio Harness Target Prog StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Layout Fz_iface Driver_iface Drv_kit Fz_kit Fz_I1_defs Fz_I1_getrn Fz_I2_ppi. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit Fz_T_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_K_hash Fz_K_rep.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Notation wz := (Z_to_bv 64) (only parsing).

Ltac ubs_slot i b :=
  replace (0 <? b) with true by (symmetry; apply Z.ltb_lt; lia); replace (8 * i + b <? 1) with false by (symmetry; apply Z.ltb_ge; lia); cbn [Z.b2z];
  zstep; th_if_lit; zstep; zstep;
  replace (8 * i + b <? b) with false by (symmetry; apply Z.ltb_ge; lia); rewrite (zlxor_sign (8 * i)) by lia;
  replace (8 * i + 9223372036854775808 <? 0 + 9223372036854775808) with false by (symmetry; apply Z.ltb_ge; lia); cbn [Z.b2z];
  zstep; zstep; zstep; th_if_lit; zstep; ubs_if; zstep; zstep; ubs_if.

Definition pgetrn_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : mem)
    (hp h rn : Z) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 rn) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(bv_unsigned sp - 96, bv_unsigned sp); (hp, hp + 8)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp)
    /\ rw_cells usegs m' hp [C8 (Z_to_bv 64 h)].

Theorem pgetrn_spec : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (LBall : list block) (L : @clist bptr) (lh : Z) (pl pb : bptr) (B items : Z) (bks : list (list pnode)) (d S hp lo : Z) (str : list byte) (old : word) (sH : PState) (mH : mem),
  plh_rep m LBall L lh pl pb B items bks ->
  rw_cells usegs m d [C8 (Z_to_bv 64 S)] -> (d + 8 <= lo \/ bv_unsigned sp <= d) -> (hp + 8 <= d \/ d + 8 <= hp) ->
  0 < S -> bytes_at usegs m S (str ++ [Z_to_bv 8 0]) -> ~ In (Z_to_bv 8 0) str -> str <> [] -> Z.of_nat (length str) < 2 ^ 40 ->
  (S + Z.of_nat (length str) + 1 <= lo \/ bv_unsigned sp <= S) -> (hp + 8 <= S \/ S + Z.of_nat (length str) + 1 <= hp) ->
  Forall (fun n : pnode => snd n <> lh_strhash str) (nth (Z.to_nat (lh_strhash str mod 8)) bks []) ->
  a0 = Z_to_bv 64 lh -> a1 = Z_to_bv 64 d -> a2 = Z_to_bv 64 hp ->
  rw_cells usegs m hp [C8 old] -> bv_unsigned sp <= hp -> hp mod 8 = 0 -> d mod 8 = 0 -> 0 < d -> RHEAP sH LBall mH ->
  stk usegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - GETRN_STACK -> mem_inv usegs m ->
  evt usegs (pgetrn_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m hp (lh_strhash str)
               (pend (B + 8 * (lh_strhash str mod 8)) (nth (Z.to_nat (lh_strhash str mod 8)) bks [])))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 FZ_GETRN) fc None m (seg_rom usegs)).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros until mH. intros REP DC DLOC DHP S0 STR NONUL NE LEN SLOC SHP HASHES -> -> -> HPC HPS HPAL DAL DNZ RH ST CLO SLO MI.
  pose proof REP as (OL & RL & (x40 & x48 & err & pad & SC) & OB & RB & LEN16 & IT & CH & EMP & ND).
  pose proof (cown_al8 _ _ _ _ _ _ _ _ RH OL) as (LAL & _). pose proof (cown_al8 _ _ _ _ _ _ _ _ RH OB) as (BAL & _).
  unfold lh_cells, PROP_FNS, PROP_GEO, lf_comp, lf_hash, lf_hashw, lf_compw, MallocRep.wz in SC. cbn [g_nn g_na g_p g_pmax g_items] in SC.
  unfold FZ_GETRN, GETRN_STACK in *.
  pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp); (hp, hp + 8)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  assert (CW : alloc_ceiling < 2^63) by (unfold ceil_window in *; lia).
  pose proof (rw_cells_bound _ _ _ _ HPC) as HPB. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in HPB.
  pose proof (rw_cells_bound _ _ _ _ DC) as DB. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in DB.
  pose proof (bytes_at_bound _ _ _ _ STR) as SB. rewrite length_app in SB. cbn [length] in SB.
  pose proof (lh_strhash_range str) as HR.
  (* [comment removed for export] *)
  step. carve_frame 64%nat ST. do 9 step. step. step. ubs_if. do 5 step.
  step. if_cases K0; zify_cond K0. { exfalso. rewrite ?unsigned_lit in K0 by lia. lia. }
  step.
  calle (eapply (prop_hashw_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ d S lo str)); try lia.
  remember (lh_strhash str) as h eqn:Eh.
  (* [comment removed for export] *)
  step. step. step. step. ubs_if.
  step. step. rewrite (zx32_small 8) by lia. step. if_cases KP; zify_cond KP. { exfalso. rewrite ?unsigned_lit in KP by lia. lia. }
  step. step.
  rewrite (zx32_small 0) by lia. rewrite m_remu by (rewrite unsigned_lit by lia; lia). rewrite (unsigned_lit 8) by lia.
  step. if_cases K1; zify_cond K1. 2:{ exfalso. rewrite ?unsigned_lit in K1 by lia. clear - K1 HR. pose proof (Z.mod_pos_bound h 8 ltac:(lia)). lia. }
  clear K1. rewrite ?(unsigned_lit h) by lia.
  set (idx := h mod 8) in *. assert (IDXR : 0 <= idx < 8) by (subst idx; apply Z.mod_pos_bound; lia).
  (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mc end.
  lazymatch goal with H : munch _ m mc |- _ => rename H into MUc end. lazymatch goal with H : wmono usegs m mc |- _ => rename H into WMc end.
  assert (WOUT : forall a, 0 <= a < alloc_ceiling -> outside [(bv_unsigned sp - 96, bv_unsigned sp); (hp, hp + 8)]%Z a) by (intros a Ha; cbn [outside]; lia).
  pose proof (plh_rep_munch _ _ _ _ _ _ _ _ _ _ _ REP MUc WMc WOUT) as REPc.
  pose proof REPc as (_ & _ & _ & _ & _ & _ & _ & CHc & _ & _).
  pose proof (CHc idx ltac:(lia)) as (cend & SEG & TERM).
  assert (SWR : forall z, 0 <= z < 2^31 -> bv_swrap 32 z = z).
  { intros z Hz. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32)%Z with (2^32)%Z. change (2 ^ 32 `div` 2)%Z with (2^31)%Z. rewrite Z.mod_small by lia. lia. }
  assert (EA : Z.land (bv_swrap 32 (idx + 0)) 18446744073709551615 ≪ 3 = 8 * idx).
  { rewrite Z.add_0_r, SWR by lia. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia. rewrite Z.mod_small by lia.
    rewrite Z.shiftl_mul_pow2 by lia. lia. }
  do 4 zstep. rewrite EA. zstep. zstep. ubs_slot idx B. replace (8 * idx + B) with (B + 8 * idx) by lia. clear EA SWR.
  (* [comment removed for export] *)
  assert (EXIT : forall (rn : Z) (y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y16 y17 y18 y19 y20 : word),
    rn = pend (B + 8 * idx) (nth (Z.to_nat idx) bks []) ->
    evt usegs (pgetrn_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m hp h rn)
      (MS (mkR (Z_to_bv 64 0xe9e98) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp y1 y2 y3 sp (Z_to_bv 64 lh) y4 y5 y6 y7 y8 y9 y10 y11 (Z_to_bv 64 d) (Z_to_bv 64 h)
               (Z_to_bv 64 rn) y16 s6 s7 s8 s9 s10 s11 y17 y18 y19 y20)
          F (Z_to_bv 64 0xe9f64) fc None mc (seg_rom usegs))).
  { intros rn y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y16 y17 y18 y19 y20 ->.
    do 9 step. lazymatch goal with FRh : rw_cells _ mc (bv_unsigned sp + -64) _, STh : stk _ mc _ _ |- _ => release_frame FRh STh (bv_unsigned sp) end. step.
    apply evt_done. unfold pgetrn_post. do 14 eexists. exists mc.
    split; [reflexivity|]. repeat match goal with |- _ /\ _ => split end; eassumption. }
  (* [comment removed for export] *)
  assert (LOOP : forall (rest ns1 : list pnode) (c : Z) (pn : bptr) (A hA : Z) (y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y17 y18 y19 y20 : word),
    nth (Z.to_nat idx) bks [] = ns1 ++ ((pn, A), hA) :: rest ->
    plseg mc LBall L (B + 8 * idx) ns1 c -> plseg mc LBall L c (((pn, A), hA) :: rest) cend ->
    evt usegs (pgetrn_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m hp h (pend (B + 8 * idx) (nth (Z.to_nat idx) bks [])))
      (MS (mkR (Z_to_bv 64 0xe9e98) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp y1 y2 y3 sp (Z_to_bv 64 lh) y4 y5 y6 y7 y8 y9 y10 y11 (Z_to_bv 64 d) (Z_to_bv 64 h)
               (Z_to_bv 64 c) (Z_to_bv 64 A) s6 s7 s8 s9 s10 s11 y17 y18 y19 y20)
          F (Z_to_bv 64 0xe9f14) fc None mc (seg_rom usegs))).
  { induction rest as [|[[q Bq] hq] rest IH]; intros ns1 c pn A hA y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y17 y18 y19 y20 ENTH S1 S2;
      pose proof S2 as (CC & OWN & RG & (dd & N1) & NH & HRA & RSEG); cbn [plseg] in RSEG.
    - (* [comment removed for export] *)
      subst cend.
      assert (NE1 : hA <> h). { pose proof (proj1 (Forall_forall _ _) HASHES ((pn, A), hA)) as X. cbn [snd] in X. apply X. rewrite ENTH. apply in_or_app. right. left. reflexivity. }
      pose proof (cown_al8 _ _ _ _ _ _ _ _ RH OWN) as (AAL & _). step. step. ubs_if.
      step. step. if_cases K5; zify_cond K5. 2:{ exfalso. rewrite ?unsigned_lit in K5 by lia. exact (NE1 K5). }
      do 2 step. step. if_cases K6; zify_cond K6. { exfalso. rewrite ?unsigned_lit in K6 by lia. lia. }
      assert (EE : A + 8 = pend (B + 8 * idx) (nth (Z.to_nat idx) bks [])) by (rewrite ENTH, pend_app; cbn [pend]; reflexivity).
      rewrite EE. apply EXIT. reflexivity.
    - pose proof RSEG as (CC2 & _ & RG2 & _).
      assert (NE1 : hA <> h). { pose proof (proj1 (Forall_forall _ _) HASHES ((pn, A), hA)) as X. cbn [snd] in X. apply X. rewrite ENTH. apply in_or_app. right. left. reflexivity. }
      pose proof (cown_al8 _ _ _ _ _ _ _ _ RH OWN) as (AAL & _). step. step. ubs_if.
      step. step. if_cases K5; zify_cond K5. 2:{ exfalso. rewrite ?unsigned_lit in K5 by lia. exact (NE1 K5). }
      do 2 step. step. if_cases K6; zify_cond K6. 2:{ exfalso. rewrite ?unsigned_lit in K6 by lia. lia. }
      apply (IH (ns1 ++ [((pn, A), hA)]) (A + 8) q Bq hq); [rewrite <- app_assoc; exact ENTH| | exact RSEG].
      eapply plseg_app; [exact S1|]. cbn [plseg]. split; [exact CC|]. split; [exact OWN|]. split; [exact RG|]. split; [exists dd; exact N1|]. split; [exact NH|]. split; [exact HRA| reflexivity]. }
  (* [comment removed for export] *)
  revert SEG. destruct (nth (Z.to_nat idx) bks []) as [|[[pn A] hA] rest] eqn:ENTH; intros SEG.
  - cbn [plseg] in SEG. subst cend.
    remember (B + 8 * idx) as cb eqn:ECB.
    step. step. if_cases K3; zify_cond K3. 2:{ exfalso. apply K3. reflexivity. }
    subst cb. apply EXIT. cbn [pend]. reflexivity.
  - pose proof SEG as (CC & _ & RG & _).
    remember (B + 8 * idx) as cb eqn:ECB.
    step. step. if_cases K3; zify_cond K3. { exfalso. rewrite ?unsigned_lit in K3 by lia. lia. }
    subst cb. eapply (LOOP rest [] (B + 8 * idx) pn A hA); [reflexivity| reflexivity| exact SEG].
Qed.
End WithCeiling0.
