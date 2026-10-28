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
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface RT_iface_pem D_defs D_kit D_agree R_cache_defs Fz_kit I_ut Fz_chk Fz_fkit Fz_I1_getrn Fz_I1_retrieve Fz_I1_split Fz_I1_insw Fz_I1_insx Fz_env Fz_M_malloc Fz_K_hash Fz_K_rep Fz_K_getrn Fz_ukit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Notation wz := (Z_to_bv 64) (only parsing).

(* [comment removed for export] *)
Definition ki_w0_post (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : mem) (lh data B items : Z) : machine_state -> Prop :=
  fun ms => exists (jl : list byte) (m' : mem),
    ms = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -192)) gp tp t0 t1 t2 sp (Z_to_bv 64 ((lh + 56) ≫ 3 + 2147450880))
                 (Z_to_bv 64 512) (Z_to_bv 64 (items * 256 / 8)) (Z_to_bv 64 8) a3 a4 a5 a6 a7
                 (Z_to_bv 64 (lh + 88)) (Z_to_bv 64 data) (Z_to_bv 64 lh) (Z_to_bv 64 (lh + 56)) (Z_to_bv 64 (lh + 96))
                 (Z_to_bv 64 ((lh + 88) ≫ 3 + 2147450880)) (Z_to_bv 64 ((lh + 96) ≫ 3 + 2147450880)) (Z_to_bv 64 2147450880) s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 LHI_SPLIT_EXIT) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 192, bv_unsigned sp); (lh + 96, lh + 100)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' (bv_unsigned sp + -192) (lhi_frame jl ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)
    /\ rw_cells asegs m' lh (plh_cells B items)
    /\ stk asegs m' lo (bv_unsigned sp + -192).

Lemma ki_w0 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (lo lh data B items : Z),
  a0 = Z_to_bv 64 lh -> a1 = Z_to_bv 64 data ->
  rw_cells asegs m lh (plh_cells B items) -> 0 <= items < 16 ->
  acc asegs m lh 104 -> lh mod 8 = 0 -> 0x10007fff8000 <= lh -> lh + 104 <= lo ->
  img_untouched m -> ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 SHB)] ->
  stk asegs m lo (bv_unsigned sp) -> 0x10007fff8000 <= lo -> lo <= bv_unsigned sp - 192 -> bv_unsigned sp <= 2 ^ 47 ->
  mem_inv asegs m ->
  evt asegs (ki_w0_post ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc lo m lh data B items)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 e_lh_insert) fc None m (seg_rom asegs)).
Proof.
  intros until items. intros -> -> SC IT ACL ALL HIL LLO UT SHC ST LO0 LO HTOP MI.
  unfold plh_cells, e_property_cmp, e_property_hash, T_HW, T_CW, T_DAW, T_DAAW in SC. unfold g_shadow_memory_dynamic_address, SHB in SHC. unfold e_lh_insert.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 192, bv_unsigned sp); (lh + 96, lh + 100)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia; assert (HWS : sh_fp W) by sh_fp_lia end.
  th_frame 192%nat [88; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat ST.
  do 15 zstep.
  do 9 zstep. zstep. th_if_lit.
  zstep. th_fix_lit_store.
  do 4 zstep. zstep. th_if_lit.
  do 4 zstep. zstep. th_if_lit. do 6 zstep. zstep. th_if_lit.
  zstep. zstep. zstep.
  rewrite (zx32_small 8) by lia. rewrite m_divu by (rewrite unsigned_lit by lia; lia). rewrite (unsigned_lit 8) by lia.
  rewrite (Z.shiftl_mul_pow2 items 8) by lia. change (2 ^ 8) with 256. rewrite (unsigned_lit (items * 256)) by lia.
  zstep.
  replace (negb (bv_ltu (Z_to_bv 64 (items * 256 / 8)) (Z_to_bv 64 512))) with false
    by (unfold bv_ltu; rewrite !unsigned_lit by lia; destruct (Z.ltb_spec (items * 256 / 8) 512); cbn; lia).
  apply evt_done. unfold ki_w0_post, lhi_frame, plh_cells, e_property_cmp, e_property_hash, T_HW, T_CW, T_DAW, T_DAAW. do 2 eexists.
  split; [cbv delta [mkR]; reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [eassumption|]. split; [eassumption| assumption].
Qed.

(* [comment removed for export] *)
Definition ki_wg_post (sp gp tp s3 s5 s10 s11 : word) (F0 : bvmap 5 word) (lo : Z) (m : mem) (lh B items : Z) (bks : list (list pnode)) (data : Z) (str : list byte)
    (jl : list byte) (rav s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v : word) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m' : mem) (rn : Z),
    rn = pend (B + 8 * (lh_strhash str mod 8)) (nth (Z.to_nat (lh_strhash str mod 8)) bks []) /\ mem_inv asegs m' /\ wmono asegs m m'
    /\ ms' = MS (mkR (Z_to_bv 64 SITE_lhi_malloc) (Z_to_bv 64 (bv_unsigned sp + -192)) gp tp t0 t1 t2 sp (Z_to_bv 64 (rn ≫ 3 + 2147450880))
                  (Z_to_bv 64 24) (Z_to_bv 64 LHI_FILE) (Z_to_bv 64 130) a3 a4 a5 a6 a7
                  (Z_to_bv 64 (lh + 88)) (Z_to_bv 64 data) (Z_to_bv 64 rn) s5 s3
                  (Z_to_bv 64 ((lh + 88) ≫ 3 + 2147450880)) (Z_to_bv 64 ((lh + 96) ≫ 3 + 2147450880)) (Z_to_bv 64 2147450880) s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 e_CRYPTO_malloc) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 304, bv_unsigned sp - 104)]%Z m m'
    /\ rw_cells asegs m' (bv_unsigned sp + -192) (CB 80 jl :: C8 (Z_to_bv 64 (lh_strhash str)) :: lhi_saved rav s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v)
    /\ rw_cells asegs m' rn [C8 (Z_to_bv 64 0)]
    /\ stk asegs m' lo (bv_unsigned sp + -192)
    /\ plh_rep m' lh B items bks.

Lemma ki_wg : forall (ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (lh B items : Z) (bks : list (list pnode)) (data S lo : Z) (str : list byte)
    (jl jh : list byte) (rav s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v : word),
  plh_rep m lh B items bks ->
  acc asegs m lh 104 -> 0 < lh -> lh + 104 <= lo -> acc asegs m B 128 -> 0 < B -> B + 128 <= lo ->
  (forall n, In n (concat bks) -> acc asegs m (fst n) 24 /\ 0 < fst n /\ fst n + 24 <= lo) ->
  rw_cells asegs m data [C8 (Z_to_bv 64 S)] -> acc asegs m data 8 -> data mod 8 = 0 -> 0 < data -> data + 8 <= lo ->
  0 < S -> bytes_at asegs m S (str ++ [Z_to_bv 8 0]) -> ~ In (Z_to_bv 8 0) str -> str <> [] -> Z.of_nat (length str) < 2 ^ 40 ->
  acc asegs m S (Z.of_nat (length str) + 1) -> S + Z.of_nat (length str) + 1 <= lo ->
  Forall (fun n : pnode => snd n <> lh_strhash str) (nth (Z.to_nat (lh_strhash str mod 8)) bks []) ->
  rw_cells asegs m (bv_unsigned sp + -192) (CB 80 jl :: CB 8 jh :: lhi_saved rav s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v) ->
  acc asegs m (bv_unsigned sp - 192) 192 -> bv_unsigned sp mod 16 = 0 ->
  img_untouched m -> ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 SHB)] ->
  stk asegs m lo (bv_unsigned sp + -192) -> 0x10007fff8000 <= lo -> lo <= bv_unsigned sp - 304 -> bv_unsigned sp <= 2 ^ 47 ->
  mem_inv asegs m ->
  evt asegs (ki_wg_post sp gp tp s3 s5 s10 s11 F lo m lh B items bks data str jl rav s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v)
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -192)) gp tp t0 t1 t2 sp s1 a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 (lh + 88)) (Z_to_bv 64 data) (Z_to_bv 64 lh) s5 s3
               (Z_to_bv 64 ((lh + 88) ≫ 3 + 2147450880)) (Z_to_bv 64 ((lh + 96) ≫ 3 + 2147450880)) (Z_to_bv 64 2147450880) s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 LHI_SPLIT_EXIT) fc None m (seg_rom asegs)).
Proof.
  intros until s11v. intros REP ACCL L0 LLO ACCB B0 BLO NODES DC DA DAL D0 DLO S0 STR NONUL NE LEN SACC SLO HASHES FR ACCF SPAL UT SHC ST LO0 LO HTOP MI.
  unfold g_shadow_memory_dynamic_address, SHB in SHC. unfold LHI_SPLIT_EXIT. unfold lhi_saved in FR.
  pose proof REP as (SC & LAL & BAL & LEN16 & IT & CH & EMP & ND).
  unfold USTACK_TOP in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (rw_cells_bound _ _ _ _ DC) as KB. cbn [cells_size csize Nat.add] in KB.
  pose proof (bytes_at_bound _ _ _ _ STR) as SB. rewrite length_app in SB. cbn [length] in SB.
  pose proof (lh_strhash_range str) as HR. assert (BAL8 : B mod 8 = 0) by (clear - BAL; Z.div_mod_to_equations; lia).
  pose proof (munch_refl [(bv_unsigned sp - 304, bv_unsigned sp - 104)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia; assert (HWS : sh_fp W) by sh_fp_lia end.
  cl_eu (bv_unsigned sp) (-192) EU1. cl_eu (bv_unsigned sp) 0 EU0. rewrite Z.add_0_r in EU0.
  assert (WOUT : forall a, plh_fp lh B bks a -> outside [(bv_unsigned sp - 304, bv_unsigned sp - 104)]%Z a).
  { intros a [Ha|[Ha|(n & Hn & Ha)]]; cbn [outside]; [clear - Ha LLO LO; lia| clear - Ha BLO LO; lia|].
    destruct (NODES n Hn) as (_ & _ & X). clear - Ha X LO. lia. }
  (* [comment removed for export] *)
  change (CB 80 jl :: CB 8 jh :: ?sv) with ([CB 80 jl] ++ CB 8 jh :: sv) in FR. apply (cb8_c8_in m _ [CB 80 jl] _ _) in FR.
  change ([CB 80 jl] ++ C8 (le_bytes_to_word jh) :: ?sv) with ([CB 80 jl] ++ [C8 (le_bytes_to_word jh)] ++ sv) in FR.
  apply (proj1 (rw_cells_app _ _ _ _)) in FR. destruct FR as [F80 FR]. apply (proj1 (rw_cells_app _ _ _ _)) in FR. destruct FR as [F0 FS].
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in F0, FS.
  replace (bv_unsigned sp + -192 + 80) with (bv_unsigned sp + -112) in F0 by lia. replace (bv_unsigned sp + -192 + 80 + 8) with (bv_unsigned sp + -104) in FS by lia.
  assert (HPA : acc asegs m (bv_unsigned sp + -112) 8) by (apply (acc_sub asegs m _ _ _ _ ACCF); lia).
  (* [comment removed for export] *)
  do 3 zstep. zstep.
  eapply evt_cut; [eapply (pgetrn_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m lh B items bks data S (bv_unsigned sp + -112) lo str) | post_call asegs m];
    [exact REP| exact ACCL| exact L0| exact LLO| exact ACCB| exact B0| exact BLO| exact NODES
    | exact DC| exact DA| exact DAL| exact D0| clear - DLO LO HTOP; lia| left; exact DLO| right; clear - DLO LO; lia
    | exact S0| exact STR| exact NONUL| exact NE| exact LEN| exact SACC| clear - SLO LO HTOP; lia| left; exact SLO| right; clear - SLO LO; lia
    | exact HASHES| reflexivity| reflexivity| first [reflexivity| rewrite ?EU0; reflexivity]
    | exact F0| exact HPA| clear - SPAL; Z.div_mod_to_equations; lia| rewrite ?EU1; lia| unfold USTACK_TOP; lia
    | exact UT| exact SHC| rewrite ?EU1; exact ST| lia| rewrite ?EU1; lia| rewrite ?EU1; lia| assumption|].
  rename x13 into m2. rewrite EU1 in PC. rename PC into ST2. rename POST into HP2.
  lazymatch goal with H : munch _ m m2 |- _ => rename H into MU2 end. lazymatch goal with H : wmono asegs m m2 |- _ => rename H into WM2 end.
  set (idx := lh_strhash str mod 8) in *. assert (IDXR : 0 <= idx < 8) by (subst idx; apply Z.mod_pos_bound; lia).
  pose proof (CH idx ltac:(lia)) as (cend & SEG & TERM). pose proof (plseg_end _ _ _ _ SEG) as EE.
  set (rn := pend (B + 8 * idx) (nth (Z.to_nat idx) bks [])) in *. subst cend.
  assert (TERM2 : rw_cells asegs m2 rn [C8 (Z_to_bv 64 0)]).
  { eapply rw_cells_transport; [exact TERM| exact MU2| exact WM2|]. cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ].
    destruct (pend_where (nth (Z.to_nat idx) bks []) (B + 8 * idx)) as [[_ E2]|(pre & A & h & E1 & E2)]; fold rn in E2; rewrite E2.
    - clear - BLO LO IDXR. lia.
    - destruct (NODES (A, h) ltac:(eapply in_concat_nthZ; rewrite E1; apply in_or_app; right; left; reflexivity)) as (_ & _ & X). cbn [fst] in X. clear - X LO. lia. }
  (* [comment removed for export] *)
  assert (RNACC : exists p n, acc asegs m2 p n /\ p mod 8 = 0 /\ 0 <= p /\ p <= rn /\ rn + 8 <= p + n /\ p + n <= 2^47).
  { destruct (pend_where (nth (Z.to_nat idx) bks []) (B + 8 * idx)) as [[_ E2]|(pre & A & h & E1 & E2)]; fold rn in E2; rewrite E2.
    - exists B, 128. split; [exact (acc_munch_sh _ m _ _ _ ACCB MU2 HWS ltac:(lia) ltac:(lia))|]. split; [exact BAL8|]. clear - IDXR B0 BLO LO HTOP. lia.
    - assert (INA : In (A, h) (concat bks)) by (eapply in_concat_nthZ; rewrite E1; apply in_or_app; right; left; reflexivity).
      destruct (NODES _ INA) as (X1 & X2 & X3). cbn [fst] in X1, X2, X3.
      pose proof (plseg_aligned _ _ _ _ SEG (A, h) ltac:(rewrite E1; apply in_or_app; right; left; reflexivity)) as AAL. cbn [fst] in AAL.
      exists A, 24. split; [exact (acc_munch_sh _ m _ _ _ X1 MU2 HWS ltac:(lia) ltac:(clear - X3 LO HTOP; lia))|]. split; [exact AAL|]. clear - X2 X3 LO HTOP. lia. }
  assert (RNAL : rn mod 8 = 0).
  { destruct (pend_where (nth (Z.to_nat idx) bks []) (B + 8 * idx)) as [[_ E2]|(pre & A & h & E1 & E2)]; fold rn in E2; rewrite E2.
    - clear - BAL8. Z.div_mod_to_equations; lia.
    - pose proof (plseg_aligned _ _ _ _ SEG (A, h) ltac:(rewrite E1; apply in_or_app; right; left; reflexivity)) as AAL. cbn [fst] in AAL.
      clear - AAL. Z.div_mod_to_equations; lia. }
  destruct RNACC as (pa & na' & PACC & PAL & PA0 & PA1 & PA2 & PA3).
  zstep.                                                                   (* [comment removed for export] *)
  do 3 zstep. zstep. th_if_lit. zstep.
  (* [comment removed for export] *)
  zstep. if_cases K1; zify_cond K1. 2:{ exfalso. apply K1. reflexivity. }
  do 4 zstep. zstep.
  apply evt_done. unfold ki_wg_post. do 12 eexists. exists F, fc, m2, rn.
  split; [reflexivity|]. split; [assumption|]. split; [exact WM2|].
  split; [unfold SITE_lhi_malloc, LHI_FILE, e_CRYPTO_malloc; cbv delta [mkR]; reflexivity|].
  split; [exact MU2|]. split; [| split; [exact TERM2| split; [exact ST2| exact (plh_rep_munch _ _ _ _ _ _ _ REP MU2 WOUT)]]].
  unfold lhi_saved. change (CB 80 jl :: C8 (Z_to_bv 64 (lh_strhash str)) :: ?sv) with ([CB 80 jl] ++ [C8 (Z_to_bv 64 (lh_strhash str))] ++ sv).
  apply rw_cells_app. split; [eassumption|]. apply rw_cells_app. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ].
  replace (bv_unsigned sp + -192 + 80) with (bv_unsigned sp + -112) by lia. replace (bv_unsigned sp + -112 + 8) with (bv_unsigned sp + -104) by lia.
  split; [exact HP2| eassumption].
  Unshelve. all: exact (Z_to_bv 64 0).
Qed.

(* [comment removed for export] *)
Definition ki_w5_post (sp gp tp : word) (lo : Z) (m : mem) (lh q rn data B items h : Z)
    (rav s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v : word) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m' : mem),
    ms' = MS (mkR rav sp gp tp t0 t1 t2 s0v s1v (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v t3 t4 t5 t6) F (ret_pc rav) fc None m' (seg_rom asegs)
    /\ munch [(q, q + 24); (rn, rn + 8); (lh + 88, lh + 96)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' q [C8 (Z_to_bv 64 data); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 h)]
    /\ rw_cells asegs m' rn [C8 (Z_to_bv 64 q)]
    /\ rw_cells asegs m' lh (plh_cells B (items + 1)).

Lemma ki_w5 : forall (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3 s5 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (lo lh q rn data B items pa na' h : Z) (jq : list byte) (LOC80 : list byte)
    (rav s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v : word),
  rw_cells asegs m lh (plh_cells B items) -> 0 <= items < 2^62 -> 0 <= h < 2 ^ 64 ->
  acc asegs m lh 104 -> lh mod 8 = 0 -> 0x10007fff8000 <= lh -> lh + 104 <= lo ->
  rw_cells asegs m q [CB 24 jq] -> acc asegs m q 24 -> q mod 8 = 0 -> 0x10007fff8000 <= q -> q + 24 <= lo ->
  rw_cells asegs m rn [C8 (Z_to_bv 64 0)] -> acc asegs m pa na' -> pa mod 8 = 0 -> 0 <= pa -> pa <= rn -> rn + 8 <= pa + na' -> pa + na' <= 2^47 -> 0x10007fff8000 <= rn -> rn + 8 <= lo ->
  (q + 24 <= lh \/ lh + 104 <= q) -> (q + 24 <= rn \/ rn + 8 <= q) -> (rn + 8 <= lh \/ lh + 104 <= rn) ->
  rw_cells asegs m (bv_unsigned sp + -192) ([CB 80 LOC80; C8 (Z_to_bv 64 h)] ++ lhi_saved rav s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v) ->
  stk asegs m lo (bv_unsigned sp + -192) -> 0x10007fff8000 <= lo -> lo <= bv_unsigned sp - 192 -> bv_unsigned sp <= 2 ^ 47 ->
  mem_inv asegs m ->
  evt asegs (ki_w5_post sp gp tp lo m lh q rn data B items h rav s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v)
      (MS (mkR (Z_to_bv 64 SITE_lhi_malloc) (Z_to_bv 64 (bv_unsigned sp + -192)) gp tp t0 t1 t2 sp (Z_to_bv 64 (rn ≫ 3 + 2147450880))
               (Z_to_bv 64 q) a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 (lh + 88)) (Z_to_bv 64 data) (Z_to_bv 64 rn) s5 s3
               (Z_to_bv 64 ((lh + 88) ≫ 3 + 2147450880)) (Z_to_bv 64 ((lh + 96) ≫ 3 + 2147450880)) (Z_to_bv 64 2147450880) s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 SITE_lhi_malloc) fc None m (seg_rom asegs)).
Proof.
  intros until s11v. intros SC IT HRG ACL ALL HIL LLO NQ ACQ ALQ HIQ QLO CRN PACC PAL PA0 PA1 PA2 PA3 HIR RLO SQL SQR SRL FR ST LO0 LO HTOP MI.
  unfold plh_cells, e_property_cmp, e_property_hash, T_HW, T_CW, T_DAW, T_DAAW in SC. unfold SITE_lhi_malloc. unfold lhi_saved in FR. cbn [app] in FR.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(q, q + 24); (rn, rn + 8); (lh + 88, lh + 96)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWS : sh_fp W) by sh_fp_lia end.
  cl_eu (bv_unsigned sp) 0 EU0. rewrite Z.add_0_r in EU0. cl_eu (bv_unsigned sp) (-192) EU1.
  apply (rw_cells_split_CB asegs m q [] 24 jq [] [8; 8; 8]%nat) in NQ; [| reflexivity]. cbn [mk_CB_cells app firstn skipn] in NQ.
  zstep. if_cases K0; zify_cond K0. { exfalso. rewrite ?unsigned_lit in K0 by lia. lia. }
  do 3 zstep. zstep. th_if_lit. zstep.
  do 4 zstep. zstep. th_if_lit. zstep. th_fix_lit_store.
  do 4 zstep. zstep. th_if_lit. zstep. zstep.
  zstep. zstep. th_if_lit. zstep.
  zstep. zstep. th_if_lit. zstep. zstep. zstep. zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m5 end.
  lazymatch goal with H : rw_cells asegs m5 (bv_unsigned sp + -192) _ |- _ => rename H into FRJ end.
  lazymatch goal with H : stk asegs m5 lo _ |- _ => rename H into ST5 end.
  eapply evt_cut; [eapply (lhi_epi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m5 lo sp rav s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v [CB 80 LOC80; C8 (Z_to_bv 64 h)]);
    [reflexivity| reflexivity| exact FRJ| exact ST5| lia| lia| lia| assumption] |].
  intros ms' [-> STF].
  apply evt_done. unfold ki_w5_post, plh_cells, e_property_cmp, e_property_hash, T_HW, T_CW, T_DAW, T_DAAW. do 14 eexists. exists F, fc, m5. split; [cbv delta [mkR]; reflexivity|].
  split; [eassumption|]. split; [eassumption|]. split; [assumption|]. split; [exact STF|].
  split; [exact NQ|]. split; [exact CRN| exact SC].
Qed.
