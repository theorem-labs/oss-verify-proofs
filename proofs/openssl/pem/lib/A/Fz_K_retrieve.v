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
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface RT_iface_pem D_defs D_kit D_agree R_cache_defs Fz_kit I_ut Fz_chk Fz_fkit Fz_I1_getrn Fz_I1_retrieve Fz_K_hash Fz_K_rep Fz_K_getrn Fz_ukit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Notation wz := (Z_to_bv 64) (only parsing).
Definition RETRIEVE_STACK : Z := 144.

Definition plh_retrieve_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : mem)
    (lh B items : Z) (bks : list (list pnode)) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 144, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ plh_rep m' lh B items bks.

(* [comment removed for export] *)
Definition plh_retrieve_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (lh B items : Z) (bks : list (list pnode)) (d S lo : Z) (str : list byte),
  plh_rep m lh B items bks ->
  acc asegs m lh 104 -> 0 < lh -> lh + 104 <= lo -> acc asegs m B 128 -> 0 < B -> B + 128 <= lo ->
  (forall n, In n (concat bks) -> acc asegs m (fst n) 24 /\ 0 < fst n /\ fst n + 24 <= lo) ->
  rw_cells asegs m d [C8 (Z_to_bv 64 S)] -> acc asegs m d 8 -> d mod 8 = 0 -> 0 < d -> d + 8 <= lo ->
  0 < S -> bytes_at asegs m S (str ++ [Z_to_bv 8 0]) -> ~ In (Z_to_bv 8 0) str -> str <> [] -> Z.of_nat (length str) < 2 ^ 40 ->
  acc asegs m S (Z.of_nat (length str) + 1) -> S + Z.of_nat (length str) + 1 <= lo ->
  Forall (fun n : pnode => snd n <> lh_strhash str) (nth (Z.to_nat (lh_strhash str mod 8)) bks []) ->
  a0 = Z_to_bv 64 lh -> a1 = Z_to_bv 64 d ->
  acc asegs m (bv_unsigned sp - 32) 32 -> bv_unsigned sp mod 16 = 0 ->
  img_untouched m -> ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 SHB)] ->
  stk asegs m lo (bv_unsigned sp) -> 0x10007fff8000 <= lo -> lo <= bv_unsigned sp - 144 -> bv_unsigned sp <= 2 ^ 47 ->
  mem_inv asegs m ->
  evt asegs (plh_retrieve_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m lh B items bks)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 e_lh_retrieve) fc None m (seg_rom asegs)).

Theorem plh_retrieve_proof : plh_retrieve_stmt.
Proof.
  unfold plh_retrieve_stmt, g_shadow_memory_dynamic_address, SHB, e_lh_retrieve.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lh B items bks d S lo str
         REP ACCL L0 LLO ACCB B0 BLO NODES DC DA DAL D0 DLO S0 STR NONUL NE LEN SACC SLO HASHES -> -> ACCF SPAL UT SHC ST LO0 LO HTOP MI.
  pose proof REP as (SC & LAL & BAL & LEN16 & IT & CH & EMP & ND).
  unfold plh_cells, e_property_cmp, e_property_hash, T_HW, T_CW, T_DAW, T_DAAW in SC.
  unfold USTACK_TOP in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (rw_cells_bound _ _ _ _ DC) as KB. cbn [cells_size csize Nat.add] in KB.
  pose proof (bytes_at_bound _ _ _ _ STR) as SB. rewrite length_app in SB. cbn [length] in SB.
  pose proof (lh_strhash_range str) as HR.
  assert (LAL8 : lh mod 8 = 0) by (clear - LAL; Z.div_mod_to_equations; lia).
  pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia; assert (HWS : sh_fp W) by sh_fp_lia end.
  cl_eu (bv_unsigned sp) (-32) EU1.
  assert (WOUT : forall a, plh_fp lh B bks a -> outside [(bv_unsigned sp - 144, bv_unsigned sp)]%Z a).
  { intros a [Ha|[Ha|(n & Hn & Ha)]]; cbn [outside]; [clear - Ha LLO LO; lia| clear - Ha BLO LO; lia|].
    destruct (NODES n Hn) as (_ & _ & X). clear - Ha X LO. lia. }
  (* [comment removed for export] *)
  th_frame 32%nat [8; 8; 8; 8]%nat ST.
  do 5 zstep.
  do 3 zstep. do 4 zstep. zstep. th_if_lit. zstep.
  zstep. if_cases K. 2:{ exfalso. vm_compute in K. discriminate K. }
  apply (cb8_c8_in m0 _ [] _ _) in FR. cbn [app] in FR.
  lazymatch type of FR with rw_cells _ _ _ [C8 ?hs; C8 s1; C8 s0; C8 ra] => change [C8 hs; C8 s1; C8 s0; C8 ra] with ([C8 hs] ++ [C8 s1; C8 s0; C8 ra]) in FR end.
  apply (proj1 (rw_cells_app _ _ _ _)) in FR. destruct FR as [F0 FS]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FS.
  replace (bv_unsigned sp + -32 + 8) with (bv_unsigned sp + -24) in FS by lia.
  assert (HPA : acc asegs m0 (bv_unsigned sp + -32) 8).
  { pose proof (acc_munch_sh _ m _ _ _ ACCF MU HWS ltac:(lia) ltac:(lia)) as X. apply (acc_sub asegs m0 _ _ _ _ X); lia. }
  assert (REP0 : plh_rep m0 lh B items bks) by exact (plh_rep_munch _ _ _ _ _ _ _ REP MU WOUT).
  assert (NODES0 : forall n, In n (concat bks) -> acc asegs m0 (fst n) 24 /\ 0 < fst n /\ fst n + 24 <= lo).
  { intros n Hn. destruct (NODES n Hn) as (X1 & X2 & X3). split; [| split; [exact X2| exact X3]]. exact (acc_munch_sh _ m _ _ _ X1 MU HWS ltac:(lia) ltac:(clear - X3 LO HTOP; lia)). }
  zstep. zstep.
  eapply evt_cut; [eapply (pgetrn_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m0 lh B items bks d S (bv_unsigned sp + -32) lo str) | post_call asegs m0];
    [exact REP0| exact (acc_munch_sh _ m _ _ _ ACCL MU HWS ltac:(lia) ltac:(lia))| exact L0| exact LLO
    | exact (acc_munch_sh _ m _ _ _ ACCB MU HWS ltac:(lia) ltac:(lia))| exact B0| exact BLO| exact NODES0
    | exact DC| exact (acc_munch_sh _ m _ _ _ DA MU HWS ltac:(lia) ltac:(lia))| exact DAL| exact D0| clear - DLO LO HTOP; lia| left; exact DLO| right; clear - DLO LO; lia
    | exact S0| exact STR| exact NONUL| exact NE| exact LEN| exact (acc_munch_sh _ m _ _ _ SACC MU HWS ltac:(lia) ltac:(clear - SLO LO HTOP; lia))| clear - SLO LO HTOP; lia| left; exact SLO| right; clear - SLO LO; lia
    | exact HASHES| reflexivity| reflexivity| rewrite ?EU1; reflexivity
    | exact F0| exact HPA| clear - SPAL; Z.div_mod_to_equations; lia| rewrite ?EU1; lia| unfold USTACK_TOP; lia
    | exact (ut_munch _ m _ UT MU HWU)| exact SHC| rewrite ?EU1; exact ST| lia| rewrite ?EU1; lia| rewrite ?EU1; lia| assumption|].
  rename x13 into m2. rewrite EU1 in PC. rename PC into ST2. rename POST into HP2.
  set (idx := lh_strhash str mod 8) in *. assert (IDXR : 0 <= idx < 8) by (subst idx; apply Z.mod_pos_bound; lia).
  pose proof (CH idx ltac:(lia)) as (cend & SEG & TERM). pose proof (plseg_end _ _ _ _ SEG) as EE.
  set (rn := pend (B + 8 * idx) (nth (Z.to_nat idx) bks [])) in *. subst cend.
  assert (TERM2 : rw_cells asegs m2 rn [C8 (Z_to_bv 64 0)]).
  { eapply rw_cells_transport; [exact TERM| exact MU| exact WM|]. cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ].
    destruct (pend_where (nth (Z.to_nat idx) bks []) (B + 8 * idx)) as [[_ E2]|(pre & A & h & E1 & E2)]; fold rn in E2; rewrite E2.
    - clear - BLO LO IDXR. lia.
    - destruct (NODES (A, h) ltac:(eapply in_concat_nthZ; rewrite E1; apply in_or_app; right; left; reflexivity)) as (_ & _ & X). cbn [fst] in X. clear - X LO. lia. }
  (* [comment removed for export] *)
  assert (RNACC : exists p n, acc asegs m2 p n /\ p mod 8 = 0 /\ 0 <= p /\ p <= rn /\ rn + 8 <= p + n /\ p + n <= 2^47).
  { destruct (pend_where (nth (Z.to_nat idx) bks []) (B + 8 * idx)) as [[_ E2]|(pre & A & h & E1 & E2)]; fold rn in E2; rewrite E2.
    - exists B, 128. split; [exact (acc_munch_sh _ m _ _ _ ACCB MU HWS ltac:(lia) ltac:(lia))|]. split; [clear - BAL; Z.div_mod_to_equations; lia|]. clear - IDXR B0 BLO LO HTOP. lia.
    - assert (INA : In (A, h) (concat bks)) by (eapply in_concat_nthZ; rewrite E1; apply in_or_app; right; left; reflexivity).
      destruct (NODES _ INA) as (X1 & X2 & X3). cbn [fst] in X1, X2, X3.
      pose proof (plseg_aligned _ _ _ _ SEG (A, h) ltac:(rewrite E1; apply in_or_app; right; left; reflexivity)) as AAL. cbn [fst] in AAL.
      exists A, 24. split; [exact (acc_munch_sh _ m _ _ _ X1 MU HWS ltac:(lia) ltac:(clear - X3 LO HTOP; lia))|]. split; [exact AAL|]. clear - X2 X3 LO HTOP. lia. }
  assert (RNAL : rn mod 8 = 0).
  { destruct (pend_where (nth (Z.to_nat idx) bks []) (B + 8 * idx)) as [[_ E2]|(pre & A & h & E1 & E2)]; fold rn in E2; rewrite E2.
    - clear - BAL. Z.div_mod_to_equations; lia.
    - pose proof (plseg_aligned _ _ _ _ SEG (A, h) ltac:(rewrite E1; apply in_or_app; right; left; reflexivity)) as AAL. cbn [fst] in AAL.
      clear - AAL. Z.div_mod_to_equations; lia. }
  destruct RNACC as (pa & na' & PACC & PAL & PA0 & PA1 & PA2 & PA3).
  do 3 zstep. zstep. th_if_lit. zstep.
  zstep. if_cases K1; zify_cond K1. 2:{ exfalso. apply K1. reflexivity. }
  (* [comment removed for export] *)
  assert (FJ : rw_cells asegs m2 (bv_unsigned sp + -32) ([C8 (Z_to_bv 64 (lh_strhash str))] ++ [C8 s1; C8 s0; C8 ra])).
  { apply rw_cells_app. split; [exact HP2|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. replace (bv_unsigned sp + -32 + 8) with (bv_unsigned sp + -24) by lia. exact FS. }
  cbn [app] in FJ. clear HP2 FS.
  do 3 zstep. release_frame FJ ST2 (bv_unsigned sp). zstep. zstep.
  apply evt_done. unfold plh_retrieve_post. do 14 eexists. exists m2. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [assumption|].
  exact (plh_rep_munch _ _ _ _ _ _ _ REP MU WOUT).
Qed.
