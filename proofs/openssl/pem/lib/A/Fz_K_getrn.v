(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import ImageA Tac RzCPS.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import LhPure.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit Fz_T_kit.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow RT_cg.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface RT_iface_pem D_defs D_kit D_agree R_cache_defs Fz_kit I_ut Fz_chk Fz_fkit Fz_I1_getrn Fz_K_hash Fz_K_rep Fz_ukit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Notation wz := (Z_to_bv 64) (only parsing).
Definition GETRN_STACK : Z := 112.

Definition pgetrn_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : mem)
    (hp h rn : Z) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 rn) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 112, bv_unsigned sp); (hp, hp + 8)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' hp [C8 (Z_to_bv 64 h)].

(* [comment removed for export] *)
Definition pgetrn_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (lh B items : Z) (bks : list (list pnode)) (d S hp lo : Z) (str : list byte) (old : word),
  plh_rep m lh B items bks ->
  acc asegs m lh 104 -> 0 < lh -> lh + 104 <= lo -> acc asegs m B 128 -> 0 < B -> B + 128 <= lo ->
  (forall n, In n (concat bks) -> acc asegs m (fst n) 24 /\ 0 < fst n /\ fst n + 24 <= lo) ->
  rw_cells asegs m d [C8 (Z_to_bv 64 S)] -> acc asegs m d 8 -> d mod 8 = 0 -> 0 < d -> d + 8 < 2 ^ 47 -> (d + 8 <= lo \/ bv_unsigned sp <= d) -> (hp + 8 <= d \/ d + 8 <= hp) ->
  0 < S -> bytes_at asegs m S (str ++ [Z_to_bv 8 0]) -> ~ In (Z_to_bv 8 0) str -> str <> [] -> Z.of_nat (length str) < 2 ^ 40 ->
  acc asegs m S (Z.of_nat (length str) + 1) -> S + Z.of_nat (length str) + 1 < 2 ^ 47 ->
  (S + Z.of_nat (length str) + 1 <= lo \/ bv_unsigned sp <= S) -> (hp + 8 <= S \/ S + Z.of_nat (length str) + 1 <= hp) ->
  Forall (fun n : pnode => snd n <> lh_strhash str) (nth (Z.to_nat (lh_strhash str mod 8)) bks []) ->
  a0 = Z_to_bv 64 lh -> a1 = Z_to_bv 64 d -> a2 = Z_to_bv 64 hp ->
  rw_cells asegs m hp [C8 old] -> acc asegs m hp 8 -> hp mod 8 = 0 -> bv_unsigned sp <= hp -> hp + 8 <= USTACK_TOP ->
  img_untouched m -> ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 SHB)] ->
  stk asegs m lo (bv_unsigned sp) -> 0x10007fff8000 <= lo -> lo <= bv_unsigned sp - 112 -> bv_unsigned sp <= 2 ^ 47 ->
  mem_inv asegs m ->
  evt asegs (pgetrn_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m hp (lh_strhash str)
               (pend (B + 8 * (lh_strhash str mod 8)) (nth (Z.to_nat (lh_strhash str mod 8)) bks [])))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 e_getrn) fc None m (seg_rom asegs)).

Theorem pgetrn_proof : pgetrn_stmt.
Proof.
  unfold pgetrn_stmt, g_shadow_memory_dynamic_address, SHB, e_getrn.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lh B items bks d S hp lo str old
         REP ACCL L0 LLO ACCB B0 BLO NODES DC DA DAL D0 DHI DLO DHP S0 STR NONUL NE LEN SACC SHI SLO SHP HASHES -> -> -> HPC HPA HPAL HPS HPT UT SHC ST LO0 LO HTOP MI.
  pose proof REP as (SC & LAL & BAL & LEN16 & IT & CH & EMP & ND).
  unfold plh_cells, e_property_cmp, e_property_hash, T_HW, T_CW, T_DAW, T_DAAW in SC.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp); (hp, hp + 8)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia; assert (HWS : sh_fp W) by sh_fp_lia end.
  unfold USTACK_TOP in HPT.
  pose proof (rw_cells_bound _ _ _ _ DC) as KB. cbn [cells_size csize Nat.add] in KB.
  pose proof (rw_cells_bound _ _ _ _ HPC) as HB. cbn [cells_size csize Nat.add] in HB.
  pose proof (bytes_at_bound _ _ _ _ STR) as SB. rewrite length_app in SB. cbn [length] in SB.
  pose proof (lh_strhash_range str) as HR.
  assert (LAL8 : lh mod 8 = 0) by (clear - LAL; Z.div_mod_to_equations; lia). assert (BAL8 : B mod 8 = 0) by (clear - BAL; Z.div_mod_to_equations; lia).
  assert (SWR : forall z, 0 <= z < 2^31 -> bv_swrap 32 z = z).
  { intros z Hz. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32)%Z with (2^32)%Z. change (2 ^ 32 `div` 2)%Z with (2^31)%Z.
    rewrite Z.mod_small by lia. lia. }
  cl_eu (bv_unsigned sp) (-96) EU1.
  assert (SHCAT : forall mc, munch [(bv_unsigned sp - 112, bv_unsigned sp); (hp, hp + 8)]%Z m mc -> ro_cells asegs mc 6736696 [C8 (Z_to_bv 64 2147450880)]).
  { intros mc MUc. eapply ro_cells_transport; [exact SHC| exact MUc|]. cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. lia. }
  (* [comment removed for export] *)
  th_frame 96%nat [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat ST.
  do 14 zstep.
  do 8 zstep. zstep. th_if_lit. do 5 zstep. zstep. th_if_lit. do 3 zstep. zstep. th_if_lit. zstep.
  eapply evt_cut.
  { eapply (prop_hashw_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ d S lo str); repeat (rewrite unsigned_lit by lia); rewrite ?EU1; try reflexivity; try eassumption; try lia.
    all: try exact (acc_munch_sh _ m _ _ _ DA MU HWS ltac:(lia) ltac:(lia)).
    all: try exact (acc_munch_sh _ m _ _ _ SACC MU HWS ltac:(lia) ltac:(lia)).
    all: try exact (ut_munch _ m _ UT MU HWU).
    all: match goal with |- ?g => idtac g end. }
  cbv beta. intros ms' PO. hnf in PO. rewrite ?EU1 in PO. revert ms' PO. post_call asegs m0.
  rename POST into ST.
  remember (lh_strhash str) as h eqn:Eh.
  (* [comment removed for export] *)
  zstep. zstep.                                                            (* [comment removed for export] *)
  do 3 zstep. zstep. th_if_lit. zstep.
  do 4 zstep. zstep. th_if_lit.
  do 5 zstep. zstep. th_if_lit. zstep. zstep.
  rewrite ?(zx32_small 8) by lia. rewrite ?m_remu by (rewrite unsigned_lit by lia; lia). rewrite ?(unsigned_lit 8) by lia.
  zstep. if_cases K1; zify_cond K1.
  2:{ exfalso. rewrite ?(zx32_small 8), ?m_remu, ?unsigned_lit in K1 by (rewrite ?unsigned_lit by lia; lia). clear - K1 HR. pose proof (Z.mod_pos_bound h 8 ltac:(lia)). lia. }
  clear K1. rewrite ?(unsigned_lit h) by lia.
  set (idx := h mod 8) in *. assert (IDXR : 0 <= idx < 8) by (subst idx; apply Z.mod_pos_bound; lia).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mc end.
  lazymatch goal with H : munch _ m mc |- _ => rename H into MUc end. lazymatch goal with H : wmono asegs m mc |- _ => rename H into WMc end.
  lazymatch goal with H : mem_inv asegs mc |- _ => rename H into MIc end.
  lazymatch goal with H : rw_cells asegs mc hp _ |- _ => rename H into HPc end.
  pose proof (CH idx ltac:(lia)) as (cend & SEG & TERM).
  (* [comment removed for export] *)
  assert (EXIT : forall (rn : Z) (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 : word) (mx : mem),
    rn = pend (B + 8 * idx) (nth (Z.to_nat idx) bks []) ->
    rw_cells asegs mx (bv_unsigned sp + -96) [CB 8 (firstn 8 junk); C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk asegs mx lo (bv_unsigned sp + -96) -> rw_cells asegs mx hp [C8 (Z_to_bv 64 h)] ->
    munch [(bv_unsigned sp - 112, bv_unsigned sp); (hp, hp + 8)]%Z m mx -> wmono asegs m mx -> mem_inv asegs mx ->
    evt asegs (pgetrn_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m hp h (pend (B + 8 * idx) (nth (Z.to_nat idx) bks [])))
      (MS (mkR y0 (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13
               y14 y15 (Z_to_bv 64 rn) y16 y17 y18 y19 y20 s10 s11 y21 y22 y23 t6)
          F (Z_to_bv 64 0x200b10) fc None mx (seg_rom asegs))).
  { intros rn y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 mx -> FRx STx HPx MUx WMx MIx.
    do 13 zstep. release_frame FRx STx (bv_unsigned sp). zstep.
    apply evt_done. unfold pgetrn_post. do 14 eexists. exists mx.
    split; [reflexivity|]. split; [exact MUx|]. split; [exact WMx|]. split; [exact MIx|]. split; [exact STx| exact HPx]. }
  (* [comment removed for export] *)
  assert (LOOP : forall (rest ns1 : list pnode) (c A hA : Z) (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 : word) (mx : mem),
    nth (Z.to_nat idx) bks [] = ns1 ++ (A, hA) :: rest ->
    plseg m (B + 8 * idx) ns1 c -> plseg m c ((A, hA) :: rest) cend ->
    rw_cells asegs mx (bv_unsigned sp + -96) [CB 8 (firstn 8 junk); C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk asegs mx lo (bv_unsigned sp + -96) -> rw_cells asegs mx hp [C8 (Z_to_bv 64 h)] ->
    munch [(bv_unsigned sp - 112, bv_unsigned sp); (hp, hp + 8)]%Z m mx -> wmono asegs m mx -> mem_inv asegs mx ->
    evt asegs (pgetrn_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m hp h (pend (B + 8 * idx) (nth (Z.to_nat idx) bks [])))
      (MS (mkR y0 (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp y1 y2 y3 sp (Z_to_bv 64 d) y4 y5 y6 y7 y8 y9 y10 y11
              (Z_to_bv 64 h) (Z_to_bv 64 (lh + 32)) (Z_to_bv 64 c) (Z_to_bv 64 (lh + 8)) (Z_to_bv 64 A) (Z_to_bv 64 2147450880)
               (Z_to_bv 64 ((lh + 32) ≫ 3 + 2147450880)) (Z_to_bv 64 ((lh + 8) ≫ 3 + 2147450880)) s10 s11 y12 y13 y14 t6)
         F (Z_to_bv 64 0x200a6c) fc None mx (seg_rom asegs))).
  { induction rest as [|[Bq hq] rest IH]; intros ns1 c A hA y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 mx ENTH S1 S2 FRx STx HPx MUx WMx MIx;
      pose proof S2 as (CC & AAL & (dd & N1) & NH & HRA & RSEG); cbn [plseg] in RSEG.
    - (* [comment removed for export] *)
      subst cend.
      assert (INA : In (A, hA) (concat bks)) by (eapply in_concat_nthZ; rewrite ENTH; apply in_or_app; right; left; reflexivity).
      destruct (NODES _ INA) as (ACCA & A0 & ALO). cbn [fst] in ACCA, A0, ALO.
      pose proof (acc_munch_sh _ m _ _ _ ACCA MUx HWS ltac:(lia) ltac:(clear - ALO LO HTOP; lia)) as ACCAx.
      assert (NE1 : hA <> h). { pose proof (proj1 (Forall_forall _ _) HASHES (A, hA)) as X. cbn [snd] in X. apply X. rewrite ENTH. apply in_or_app. right. left. reflexivity. }
      assert (NHx : rw_cells asegs mx (A + 16) [C8 (Z_to_bv 64 hA)]).
      { eapply rw_cells_transport; [exact NH| exact MUx| exact WMx|]. cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. clear - ALO LO HPS. lia. }
      assert (TMx : rw_cells asegs mx (A + 8) [C8 (Z_to_bv 64 0)]).
      { eapply rw_cells_transport; [exact TERM| exact MUx| exact WMx|]. cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. clear - ALO LO HPS. lia. }
      do 4 zstep. zstep. th_if_lit. zstep.
      zstep. if_cases K5; zify_cond K5. 2:{ exfalso. rewrite ?unsigned_lit in K5 by lia. exact (NE1 K5). }
      do 4 zstep. zstep. th_if_lit. zstep.
      zstep. if_cases K9; zify_cond K9. { exfalso. rewrite ?unsigned_lit in K9 by lia. clear - K9. lia. }
      assert (EE : A + 8 = pend (B + 8 * idx) (nth (Z.to_nat idx) bks [])) by (rewrite ENTH, pend_app; cbn [pend]; reflexivity).
      rewrite EE. eapply EXIT; try eassumption. reflexivity.
    - pose proof RSEG as (CC2 & BAL2 & _).
      assert (INA : In (A, hA) (concat bks)) by (eapply in_concat_nthZ; rewrite ENTH; apply in_or_app; right; left; reflexivity).
      assert (INQ : In (Bq, hq) (concat bks)) by (eapply in_concat_nthZ; rewrite ENTH; apply in_or_app; right; right; left; reflexivity).
      destruct (NODES _ INA) as (ACCA & A0 & ALO). cbn [fst] in ACCA, A0, ALO.
      destruct (NODES _ INQ) as (_ & Q0 & QLO). cbn [fst] in Q0, QLO.
      pose proof (acc_munch_sh _ m _ _ _ ACCA MUx HWS ltac:(lia) ltac:(clear - ALO LO HTOP; lia)) as ACCAx.
      assert (NE1 : hA <> h). { pose proof (proj1 (Forall_forall _ _) HASHES (A, hA)) as X. cbn [snd] in X. apply X. rewrite ENTH. apply in_or_app. right. left. reflexivity. }
      assert (NHx : rw_cells asegs mx (A + 16) [C8 (Z_to_bv 64 hA)]).
      { eapply rw_cells_transport; [exact NH| exact MUx| exact WMx|]. cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. clear - ALO LO HPS. lia. }
      assert (TMx : rw_cells asegs mx (A + 8) [C8 (Z_to_bv 64 Bq)]).
      { eapply rw_cells_transport; [exact CC2| exact MUx| exact WMx|]. cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. clear - ALO LO HPS. lia. }
      do 4 zstep. zstep. th_if_lit. zstep.
      zstep. if_cases K5; zify_cond K5. 2:{ exfalso. rewrite ?unsigned_lit in K5 by lia. exact (NE1 K5). }
      do 4 zstep. zstep. th_if_lit. zstep.
      zstep. if_cases K9; zify_cond K9. 2:{ exfalso. rewrite ?unsigned_lit in K9 by lia. clear - K9 Q0. lia. }
      apply (IH (ns1 ++ [(A, hA)]) (A + 8) Bq hq); try eassumption; [rewrite <- app_assoc; exact ENTH|].
      eapply plseg_app; [exact S1|]. cbn [plseg]. split; [exact CC|]. split; [exact AAL|]. split; [exists dd; exact N1|]. split; [exact NH|]. split; [exact HRA| reflexivity]. }
  revert SEG. destruct (nth (Z.to_nat idx) bks []) as [|[A hA] rest] eqn:ENTH; intros SEG.
  - (* [comment removed for export] *)
    cbn [plseg] in SEG. subst cend.
    assert (TC : rw_cells asegs mc (B + 8 * idx) [C8 (Z_to_bv 64 0)]).
    { eapply rw_cells_transport; [exact TERM| exact MUc| exact WMc|]. cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. clear - BLO LO HPS IDXR. lia. }
    remember (B + 8 * idx) as cb eqn:ECB.
    assert (EA : Z.land (bv_swrap 32 (idx + 0)) 18446744073709551615 ≪ 3 = 8 * idx).
    { rewrite Z.add_0_r, SWR by lia. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia. rewrite Z.mod_small by lia.
      rewrite Z.shiftl_mul_pow2 by lia. lia. }
    do 3 zstep. zstep. th_if_lit. do 4 zstep. rewrite EA.
    rewrite ?(Z.add_comm (8 * idx) B), <- ?ECB.
    do 3 zstep. zstep. th_if_lit. zstep.
    zstep. if_cases K3; zify_cond K3. 2:{ exfalso. apply K3. reflexivity. }
    subst cb. eapply EXIT; try eassumption. cbn [pend]. reflexivity.
  - pose proof SEG as (CC & AAL & _).
    assert (INA : In (A, hA) (concat bks)) by (eapply in_concat_nthZ; rewrite ENTH; left; reflexivity).
    destruct (NODES _ INA) as (_ & A0 & ALO). cbn [fst] in A0, ALO.
    assert (TC : rw_cells asegs mc (B + 8 * idx) [C8 (Z_to_bv 64 A)]).
    { eapply rw_cells_transport; [exact CC| exact MUc| exact WMc|]. cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. clear - BLO LO HPS IDXR. lia. }
    remember (B + 8 * idx) as cb eqn:ECB.
    assert (EA : Z.land (bv_swrap 32 (idx + 0)) 18446744073709551615 ≪ 3 = 8 * idx).
    { rewrite Z.add_0_r, SWR by lia. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia. rewrite Z.mod_small by lia.
      rewrite Z.shiftl_mul_pow2 by lia. lia. }
    do 3 zstep. zstep. th_if_lit. do 4 zstep. rewrite EA.
    rewrite ?(Z.add_comm (8 * idx) B), <- ?ECB.
    do 3 zstep. zstep. th_if_lit. zstep.
    zstep. if_cases K3; zify_cond K3. { exfalso. rewrite ?unsigned_lit in K3 by lia. clear - K3 A0. lia. }
    do 6 zstep. subst cb.
    eapply (LOOP rest [] (B + 8 * idx) A hA); try eassumption; reflexivity.
Qed.
