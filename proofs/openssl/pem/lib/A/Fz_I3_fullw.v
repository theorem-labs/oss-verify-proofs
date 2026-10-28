(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import ImageA Tac RzCPS NodesA SysStep FarCall.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import Prelim Malloc Prog StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import LhPure LhRep.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Str_cpy Th_kit Fz_T_kit.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow RT_cg.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout PLayout RT_iface RT_iface_pem D_defs D_kit D_agree D_clx R_cache_defs Fz_kit I_ut I_lkit Fz_chk Fz_fkit Fz_mkit Fz_G_kit Fz_ckit Fz_env Fz_M_malloc Fz_W5_icb Th_errno Th_tsd Th_key Th_once Th_mutex Fz_T_atomic Fz_T_once Fz_T_lock Fz_T_local Fz_T_initthread Fz_T_master1 Fz_I1_img Fz_I1_hash Fz_I1_defs Fz_I1_errload Fz_I1_crypto Fz_I3_shelve Fz_I3_loadstrw Fz_I3_loadstr Fz_I3_ibasew Fz_I3_ibase.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Notation z64 := (Z_to_bv 64 0) (only parsing).
Notation zeros n := (repeat (Z_to_bv 8 0) n) (only parsing).
Notation TP_A := (0xba3ef0)%Z (only parsing).

Definition OPT_LOAD_STRINGS : Z := 2.          (* [comment removed for export] *)
Definition SITE_icf_ibase : Z := 0x1f3748.      (* [comment removed for export] *)
Definition SITE_icf_ls : Z := 0x1f37b0.         (* [comment removed for export] *)
Definition SITE_icf_or : Z := 0x1f3964.         (* [comment removed for export] *)
Definition G_LS_ONCE : Z := 0xb9f300.           (* [comment removed for export] *)
Definition ICF_PC : Z := 0x1f3600.              (* [comment removed for export] *)
Definition ICF_DESCR : Z := 0x474dc.            (* [comment removed for export] *)

Definition if_w1_post (sp gp tp t0 t1 t2 a4 a5 a6 a7 s4 s6 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (ra0 s0' s1' s2' s3' s4' s5' s6' s7' s8' s9' : word) (f lo pad : Z) (oldcb canary : word) (m : mem) : machine_state -> Prop :=
  fun ms => exists (a0' a1' a2' a3' : word) (j8 fr8 fr16 junk : list byte) (m' : mem),
    ms = MS (mkR (Z_to_bv 64 ONCE_RET_INIT) (Z_to_bv 64 (bv_unsigned sp + -96 - pad + -128)) gp tp t0 t1 t2 (Z_to_bv 64 G_IC_BASE_ONCE) (Z_to_bv 64 e_ibase)
                 a0' a1' a2' a3' a4 a5 a6 a7 (Z_to_bv 64 0) (Z_to_bv 64 ssp_guard) (Z_to_bv 64 1) (Z_to_bv 64 3) (Z_to_bv 64 2)
                 (Z_to_bv 64 1) (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f) s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 e_ibase) fc None m' (seg_rom asegs)
    /\ munch [(f, f + 40); (f / 8 + 2147450880, f / 8 + 2147450880 + 8); (bv_unsigned sp - 96 - pad - 128, bv_unsigned sp - 88);
              (G_IC_BASE_ONCE, G_IC_BASE_ONCE + 4); (TP_A + -96, TP_A + -88)] m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' (bv_unsigned sp + -96) [CB 8 j8; C8 s9'; C8 s8'; C8 s7'; C8 s6'; C8 s5'; C8 s4'; C8 s3'; C8 s2'; C8 s1'; C8 s0'; C8 ra0]
    /\ rw_cells asegs m' f [C8 (Z_to_bv 64 ICB_MAGIC); C8 (Z_to_bv 64 ICF_DESCR); C8 (Z_to_bv 64 ICF_PC); CB 8 fr8]
    /\ rw_cells asegs m' (f + 32) [C8 (Z_to_bv 64 0)] /\ rw_cells asegs m' (f + 40) [CB 16 fr16]
    /\ rw_cells asegs m' (f / 8 + 2147450880) [C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 (-13)); C1 (Z_to_bv 8 (-13)); C1 (Z_to_bv 8 (-13))]
    /\ stk asegs m' (bv_unsigned sp + -96 - pad) (bv_unsigned sp + -96)
    /\ stk asegs m' lo (bv_unsigned sp + -96 - pad + -128)
    /\ ro_cells asegs m' G_IC_OPTSDONE [C8 (Z_to_bv 64 0)]
    /\ ssp_cells m' canary /\ rw_cells asegs m' G_IC_BASE_ONCE [C4 (Z_to_bv 64 1)]
    /\ rw_cells asegs m' (TP_A + -96) [C8 (Z_to_bv 64 (bv_unsigned sp + -96 - pad + -128))]
    /\ rw_cells asegs m' (bv_unsigned sp + -96 - pad + -128) (once_full_cells G_IC_BASE_ONCE oldcb canary s6 (Z_to_bv 64 (f + 32)) s4 (Z_to_bv 64 OPT_LOAD_STRINGS) (Z_to_bv 64 f)
                                                               (Z_to_bv 64 (bv_unsigned sp + -96 - pad)) (Z_to_bv 64 (bv_unsigned sp + -96 - pad)))
    /\ rw_cells asegs m' (bv_unsigned sp + -96 - pad + -32) [CB 8 junk; C8 (Z_to_bv 64 RUN_ONCE_RET)]
    /\ rw_cells asegs m' (bv_unsigned sp + -96 - pad + -16) [C8 sp; C8 (Z_to_bv 64 SITE_icf_ibase)].

Lemma if_w1 : forall sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6
    (ra0 s0' s1' s2' s3' s4' s5' s6' s7' s8' s9' : word) (F : bvmap 5 word) fc (m : mem) (f lo pad : Z) (fj sj : list byte) (oldcb canary : word),
  (pad = 0 \/ pad = 16) -> 0 < f -> f mod 64 = 0 -> 0xbc6000 <= f -> f + 64 <= lo -> (f + 64 <= 0x7fff8000 \/ 0x10007fff8000 <= f) ->
  lo <= bv_unsigned sp - 240 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 -> tp = Z_to_bv 64 TP_A ->
  img_untouched m -> ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 0x7fff8000)] ->
  rw_cells asegs m (bv_unsigned sp + -96) [C8 (Z_to_bv 64 0); C8 s9'; C8 s8'; C8 s7'; C8 s6'; C8 s5'; C8 s4'; C8 s3'; C8 s2'; C8 s1'; C8 s0'; C8 ra0] ->
  stk asegs m (bv_unsigned sp + -96 - pad) (bv_unsigned sp + -96) -> stk asegs m lo (bv_unsigned sp + -96 - pad) ->
  rw_cells asegs m f [CB 56 fj] -> rw_cells asegs m (f / 8 + 2147450880) [CB 8 sj] ->
  rw_cells asegs m G_IC_STOPPED [C1 (Z_to_bv 8 0)] -> rw_cells asegs m G_IC_OPTSDONE [C8 (Z_to_bv 64 0)] -> acc asegs m G_IC_OPTSDONE 8 ->
  rw_cells asegs m G_IC_BASE_ONCE [C4 (Z_to_bv 64 0)] ->
  ssp_cells m canary -> rw_cells asegs m (TP_A + -96) [C8 oldcb] ->
  mem_inv asegs m ->
  evt asegs (if_w1_post sp gp tp t0 t1 t2 a4 a5 a6 a7 s4 s6 s10 s11 t3 t4 t5 t6 F fc ra0 s0' s1' s2' s3' s4' s5' s6' s7' s8' s9' f lo pad oldcb canary m)
    (MS (mkR (Z_to_bv 64 SITE_icb_smalloc) (Z_to_bv 64 (bv_unsigned sp + -96 - pad)) gp tp t0 t1 t2 sp (Z_to_bv 64 (bv_unsigned sp + -96 - pad))
             (Z_to_bv 64 f) a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 OPT_LOAD_STRINGS) s4 s5 s6 s7 (Z_to_bv 64 0x7fff8000) s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_icb_smalloc) fc None m (seg_rom asegs)).
Proof.
  intros until canary. intros HP F0 F64 FIMG FLO FSH HLO HLOS SPH -> UT SHC FR GAP ST FB SB STP OD ACCO ONCE SSP CBC MI.
  destruct SSP as [GOT GU]. unfold got_ssp, ssp_guard in GOT, GU.
  unfold SITE_icb_smalloc, OPT_LOAD_STRINGS, G_IC_STOPPED, G_IC_OPTSDONE, G_IC_BASE_ONCE, G_IC_BASE_RET, g_shadow_memory_dynamic_address in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl [(f, f + 40); (f / 8 + 2147450880, f / 8 + 2147450880 + 8); (SP - 96 - pad - 128, SP - 88); (0xb9f2c0, 0xb9f2c0 + 4); (TP_A + -96, TP_A + -88)] m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  assert (SHR : 0x7fff8000 <= f / 8 + 2147450880 /\ f / 8 + 2147450880 + 8 <= 0x10007fff8000).
  { pose proof (Z.div_pos f 8 ltac:(lia) ltac:(lia)). assert (f / 8 + 8 <= 2^44) by (Z.div_mod_to_equations; lia). lia. }
  assert (HWU : ut_fp [(f, f + 40); (f / 8 + 2147450880, f / 8 + 2147450880 + 8); (SP - 96 - pad - 128, SP - 88); (0xb9f2c0, 0xb9f2c0 + 4); (TP_A + -96, TP_A + -88)])
    by (clear - F0 FIMG SHR HLO HLOS SPH FLO HP; ut_fp_lia).
  assert (EUf : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  pose proof (div8_facts f) as Q1.
  do 3 zstep. zstep. if_true.
  do 4 zstep. rewrite (shr3_div f) by lia.
  do 4 zstep.
  zstep; lfix. zstep; lfix. zstep; lfix.
  zstep. zstep; lfix. zstep; lfix. zstep; lfix. zstep; lfix.
  zstep. zstep; lfix. zstep; lfix. zstep; lfix. zstep; lfix.
  zstep. zstep. cbv beta.
  apply (proj1 (rw_cells_app _ f [C8 (Z_to_bv 64 1102416563); C8 (Z_to_bv 64 292060); C8 (Z_to_bv 64 2045440)] _)) in FB.
  destruct FB as [FBH FBT]. cbn [cells_size csize Nat.add] in FBT.
  remember (skipn 8 (skipn 8 (skipn 8 fj))) as fr eqn:Efr. clear Efr.
  apply (rw_cells_split_CB asegs _ (f + Z.of_nat 24) [] 32 fr [] [8; 8; 16]%nat) in FBT; [| reflexivity]. cbn [mk_CB_cells app] in FBT.
  assert (L8 : length (firstn 8 (skipn 8 fr)) = 8%nat) by (destruct FBT as [[WF _] _]; cbn in WF; tauto).
  apply (th_cells_congr asegs _ (f + Z.of_nat 24) _ [CB 8 (firstn 8 fr); C8 (bv_extract 0 64 (le_bytes_to_word (firstn 8 (skipn 8 fr)))); CB 16 (firstn 16 (skipn 8 (skipn 8 fr)))]) in FBT;
    [| cbn [cells_bytes cbytes]; rewrite (le8_ld _ L8); reflexivity | reflexivity | cbn; destruct FBT as [[WF _] _]; cbn in WF; tauto].
  replace (f + Z.of_nat 24) with (f + 24) in FBT by lia.
  apply (proj1 (rw_cells_app _ (f + 24) [CB 8 (firstn 8 fr)] _)) in FBT. destruct FBT as [FB24 FBT]. cbn [cells_size csize Nat.add] in FBT.
  apply (proj1 (rw_cells_app _ _ [C8 (bv_extract 0 64 (le_bytes_to_word (firstn 8 (skipn 8 fr))))] _)) in FBT. destruct FBT as [TMP FB40].
  cbn [cells_size csize Nat.add] in FB40. replace (f + 24 + Z.of_nat 8) with (f + 32) in TMP, FB40 by lia. replace (f + 32 + Z.of_nat 8) with (f + 40) in FB40 by lia.
  remember (bv_extract 0 64 (le_bytes_to_word (firstn 8 (skipn 8 fr)))) as w32 eqn:Ew. clear Ew L8.
  remember (firstn 8 fr) as fr8 eqn:E8. clear E8. remember (firstn 16 (skipn 8 (skipn 8 fr))) as fr16 eqn:E16. clear E16.
  (* [comment removed for export] *)
  destruct HP as [-> | ->].
  1: replace (SP + -96 - 0) with (SP + -96) in * by lia.
  2: replace (SP + -96 - 16) with (SP + -112) in * by lia; carve_frame 16%nat GAP.
  all: zstep.
  all: zstep; th_if_lit.
  2: th_release FR0 (SP + -96).
  all: do 5 zstep; zstep.
  (* [comment removed for export] *)
  all: lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (VA1 : acc asegs mX 12186272 8)
      by (apply (acc_agree m mX _ _ ACCO ltac:(lia)); apply (agree_of_munch _ m mX _ MU); intros x Hx; cbv beta in Hx; unfold shad, SHB in Hx; cbn [outside]; lia);
    assert (SB4 : rw_cells asegs mX (f / 8 + 2147450880 + 4) [C1 (Z_to_bv 8 0)])
      by (exact (rw_cells_head mX _ _ _ (rw_cells_skip mX (f / 8 + 2147450880) [C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15))] _ SB)));
    assert (RA1 : acc asegs mX (f + 32) 8)
      by (apply (acc_of_shadow0 mX (f + 32)); [replace (shad (f + 32)) with (f / 8 + 2147450880 + 4) by (unfold shad, SHB; Z.div_mod_to_equations; lia); exact (rw_C1_bytes mX _ _ SB4)
                                            | Z.div_mod_to_equations; lia | lia])
  end.
  all: tcall (T_atomic_load_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo (Z_to_bv 64 0) w32);
    [ exact (proj1 OD) | exact VA1 | reflexivity | exact TMP | exact RA1 | Z.div_mod_to_equations; lia | lia | unfold IMG_UT_LO, IMG_UT_HI; right; lia
    | clear - FSH; lia | exact (ut_munch _ m _ UT MU HWU) | exact SHC | eassumption | lia | lia | lia | lia | lia | assumption | ].
  all: cbv beta delta [mkR]; clear VA1 SB4 RA1 PC0.
  all: zstep. all: zstep; th_if_lit. all: do 3 zstep.
  all: if_true.
  all: do 4 zstep; zstep.
  (* [comment removed for export] *)
  all: tcall (T_run_once_enter_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo e_ibase oldcb canary).
  all: try first [eassumption | reflexivity | split; assumption | unfold e_ibase, got_ssp, ssp_guard; lia | unfold got_ssp, ssp_guard; left; lia].
  all: cbv beta delta [mkR]; rewrite (ret_pc_even e_ibase) by (unfold e_ibase; lia).
  1: pose proof (rw_cells_blur _ _ [_] _ FR) as FRB.
  2: pose proof (rw_cells_blur _ _ [_] _ FR) as FRB.
  all: cbn [cells_size csize Nat.add app cells_bytes cbytes] in FRB.
  all: subst SP; rewrite ?Z_to_bv_bv_unsigned.
  all: unfold if_w1_post, G_IC_BASE_ONCE, G_IC_OPTSDONE, ICB_MAGIC, ICF_DESCR, ICF_PC, OPT_LOAD_STRINGS, SITE_icf_ibase.
  all: try replace (bv_unsigned sp + -96 - 0) with (bv_unsigned sp + -96) by lia.
  all: try replace (bv_unsigned sp + -96 - 16) with (bv_unsigned sp + -112) by lia.
  all: apply evt_done; do 9 eexists; split; [reflexivity|].
  all: split; [eapply munch_weaken; [| exact MU]; unfold sub_fp; cbn [outside app]; intros; lia|].
  all: repeat (split; [eassumption|]).
  all: split; [apply (proj2 (rw_cells_app _ f [_; _; _] [CB 8 _])); split; [exact FBH| cbn [cells_size csize Nat.add]; replace (f + Z.of_nat 24) with (f + 24) by lia; exact FB24] |].
  all: rewrite ?Z_to_bv_bv_unsigned in POST0.
  all: repeat (split; [first [eassumption | exact (proj1 OD)]|]); eassumption.
Qed.

(* [comment removed for export] *)
Definition if_w2_post (sp gp tp t0 t1 t2 a4 a5 a6 a7 s4 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (f lo pad : Z) (oldcb canary : word) (m : mem) : machine_state -> Prop :=
  fun ms => exists (a0' a1' a2' a3' : word) (junk : list byte) (m' : mem),
    ms = MS (mkR (Z_to_bv 64 ONCE_RET_INIT) (Z_to_bv 64 (bv_unsigned sp + -96 - pad + -128)) gp tp t0 t1 t2 (Z_to_bv 64 G_LS_ONCE) (Z_to_bv 64 e_loadstr)
                 a0' a1' a2' a3' a4 a5 a6 a7 (Z_to_bv 64 0) (Z_to_bv 64 ssp_guard) (Z_to_bv 64 1) (Z_to_bv 64 3) (Z_to_bv 64 2)
                 (Z_to_bv 64 1) (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f) s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 e_loadstr) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 96 - pad - 160, bv_unsigned sp - 96 - pad); (G_IC_BASE_ONCE, G_IC_BASE_ONCE + 4); (G_LS_ONCE, G_LS_ONCE + 4); (TP_A + -96, TP_A + -88)] m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp + -96 - pad + -128)
    /\ ssp_cells m' canary /\ rw_cells asegs m' G_IC_BASE_ONCE [C4 (Z_to_bv 64 2)] /\ rw_cells asegs m' G_LS_ONCE [C4 (Z_to_bv 64 1)]
    /\ rw_cells asegs m' (TP_A + -96) [C8 (Z_to_bv 64 (bv_unsigned sp + -96 - pad + -128))]
    /\ rw_cells asegs m' (bv_unsigned sp + -96 - pad + -128) (once_full_cells G_LS_ONCE oldcb canary (Z_to_bv 64 1) (Z_to_bv 64 (f + 32)) s4 (Z_to_bv 64 OPT_LOAD_STRINGS) (Z_to_bv 64 f)
                                                               (Z_to_bv 64 (bv_unsigned sp + -96 - pad)) (Z_to_bv 64 (bv_unsigned sp + -96 - pad)))
    /\ rw_cells asegs m' (bv_unsigned sp + -96 - pad + -32) [CB 8 junk; C8 (Z_to_bv 64 RUN_ONCE_RET)]
    /\ rw_cells asegs m' (bv_unsigned sp + -96 - pad + -16) [C8 sp; C8 (Z_to_bv 64 SITE_icf_ls)].

Lemma if_w2 : forall sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s6 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (f lo pad : Z) (junk : list byte) (oldcb canary cb : word),
  (pad = 0 \/ pad = 16) -> 0 < f -> f + 64 <= lo ->
  lo <= bv_unsigned sp - 272 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 -> tp = Z_to_bv 64 TP_A ->
  img_untouched m ->
  rw_cells asegs m G_IC_BASE_ONCE [C4 (Z_to_bv 64 1)] -> ssp_cells m canary -> rw_cells asegs m (TP_A + -96) [C8 cb] ->
  rw_cells asegs m (bv_unsigned sp + -96 - pad + -128) (once_full_cells G_IC_BASE_ONCE oldcb canary s6 (Z_to_bv 64 (f + 32)) s4 (Z_to_bv 64 OPT_LOAD_STRINGS) (Z_to_bv 64 f)
                                                          (Z_to_bv 64 (bv_unsigned sp + -96 - pad)) (Z_to_bv 64 (bv_unsigned sp + -96 - pad))) ->
  rw_cells asegs m (bv_unsigned sp + -96 - pad + -32) [CB 8 junk; C8 (Z_to_bv 64 RUN_ONCE_RET)] ->
  rw_cells asegs m (bv_unsigned sp + -96 - pad + -16) [C8 sp; C8 (Z_to_bv 64 SITE_icf_ibase)] ->
  stk asegs m lo (bv_unsigned sp + -96 - pad + -128) ->
  rw_cells asegs m G_IC_BASE_RET [C4 (Z_to_bv 64 1)] -> rw_cells asegs m G_LS_ONCE [C4 (Z_to_bv 64 0)] ->
  mem_inv asegs m ->
  evt asegs (if_w2_post sp gp tp t0 t1 t2 a4 a5 a6 a7 s4 s10 s11 t3 t4 t5 t6 F fc f lo pad oldcb canary m)
    (MS (mkR (Z_to_bv 64 ONCE_RET_INIT) (Z_to_bv 64 (bv_unsigned sp + -96 - pad + -128)) gp tp t0 t1 t2 (Z_to_bv 64 G_IC_BASE_ONCE) (Z_to_bv 64 e_ibase)
             (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 0) (Z_to_bv 64 ssp_guard) (Z_to_bv 64 1) (Z_to_bv 64 3) (Z_to_bv 64 2)
             (Z_to_bv 64 1) (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f) s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 ONCE_RET_INIT) fc None m (seg_rom asegs)).
Proof.
  intros until cb. intros HP F0 FLO HLO HLOS SPH -> UT ONCE SSP CBC OF PO FRR ST BRET LSO MI.
  unfold OPT_LOAD_STRINGS, G_IC_BASE_ONCE, G_IC_BASE_RET, G_LS_ONCE, SITE_icf_ibase in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  set (SP0 := SP + -96 - pad) in *.
  assert (HSP0 : SP - 112 <= SP0 <= SP - 96) by (unfold SP0; lia).
  pose proof (munch_refl [(SP0 - 160, SP0); (0xb9f2c0, 0xb9f2c0 + 4); (0xb9f300, 0xb9f300 + 4); (TP_A + -96, TP_A + -88)] m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  assert (HWU : ut_fp [(SP0 - 160, SP0); (0xb9f2c0, 0xb9f2c0 + 4); (0xb9f300, 0xb9f300 + 4); (TP_A + -96, TP_A + -88)]) by (clear - HSP0 HLO HLOS SPH; ut_fp_lia).
  assert (EUf : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  (* [comment removed for export] *)
  tcall (T_run_once_leave_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo SP0 0xb9f2c0).
  all: try first [eassumption | reflexivity | unfold got_ssp, ssp_guard; lia | unfold got_ssp, ssp_guard; left; lia].
  cbv beta delta [mkR]. rewrite (ret_pc_even 2045768) by lia.
  zstep; th_if_lit. zstep. zstep. zstep; th_if_lit. zstep. zstep. zstep; th_if_lit. zstep; th_if_lit.
  zstep. zstep; th_if_lit. zstep. zstep; th_if_lit.
  do 4 zstep. zstep.
  (* [comment removed for export] *)
  tcall (T_run_once_enter_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo e_loadstr oldcb canary).
  all: try first [eassumption | reflexivity | unfold e_loadstr, got_ssp, ssp_guard; lia | unfold got_ssp, ssp_guard; left; lia].
  cbv beta delta [mkR]. rewrite (ret_pc_even e_loadstr) by (unfold e_loadstr; lia).
  subst SP0 SP. rewrite ?Z_to_bv_bv_unsigned in *.
  unfold if_w2_post, G_IC_BASE_ONCE, G_LS_ONCE, OPT_LOAD_STRINGS, SITE_icf_ls.
  apply evt_done; do 6 eexists; split; [reflexivity|].
  split; [eapply munch_weaken; [| exact MU]; unfold sub_fp; cbn [outside app]; intros; lia|].
  repeat (split; [eassumption|]); eassumption.
Qed.

(* [comment removed for export] *)
Definition if_w3_post (sp gp tp t0 t1 t2 a5 a6 a7 s4 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (f lo pad : Z) (oldcb canary : word) (m : mem) : machine_state -> Prop :=
  fun ms => exists (a0' a1' a2' a3' a4' : word) (m' : mem),
    ms = MS (mkR (Z_to_bv 64 SITE_icf_or) (Z_to_bv 64 (bv_unsigned sp + -96 - pad)) gp tp t0 t1 t2 sp (Z_to_bv 64 (bv_unsigned sp + -96 - pad))
                 a0' a1' a2' a3' a4' a5 a6 a7 (Z_to_bv 64 f) (Z_to_bv 64 OPT_LOAD_STRINGS) s4 (Z_to_bv 64 (f + 32)) (Z_to_bv 64 1)
                 (Z_to_bv 64 1) (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f) s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 SITE_icb_release) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 96 - pad - 160, bv_unsigned sp - 96 - pad); (G_LS_ONCE, G_LS_ONCE + 4); (TP_A + -96, TP_A + -88); (G_IC_OPTSDONE, G_IC_OPTSDONE + 8);
              (f, f + 8); (f + 32, f + 40); (f / 8 + 2147450880, f / 8 + 2147450880 + 8)] m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp + -96 - pad)
    /\ ssp_cells m' canary /\ rw_cells asegs m' G_LS_ONCE [C4 (Z_to_bv 64 2)] /\ rw_cells asegs m' (TP_A + -96) [C8 oldcb]
    /\ rw_cells asegs m' G_IC_OPTSDONE [C8 (Z_to_bv 64 OPT_LOAD_STRINGS)] /\ rw_cells asegs m' (f + 32) [C8 (Z_to_bv 64 OPT_LOAD_STRINGS)]
    /\ rw_cells asegs m' f [C8 (Z_to_bv 64 ICB_RETIRED)]
    /\ rw_cells asegs m' (f / 8 + 2147450880) [C1 (Z_to_bv 8 (-11)); C1 (Z_to_bv 8 (-11)); C1 (Z_to_bv 8 (-11)); C1 (Z_to_bv 8 (-11)); C1 (Z_to_bv 8 (-11)); C1 (Z_to_bv 8 (-11)); C1 (Z_to_bv 8 (-11)); C1 (Z_to_bv 8 (-11))].

Lemma if_w3 : forall sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (f lo pad p1 : Z) (junk : list byte) (oldcb canary cb mg : word) (b5 b6 b7 : byte),
  (pad = 0 \/ pad = 16) -> 0 < f -> f mod 64 = 0 -> 0xbc6000 <= f -> f + 64 <= lo -> (f + 64 <= 0x7fff8000 \/ 0x10007fff8000 <= f) ->
  lo <= bv_unsigned sp - 272 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 -> tp = Z_to_bv 64 TP_A ->
  img_untouched m -> ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 0x7fff8000)] ->
  rw_cells asegs m G_LS_ONCE [C4 (Z_to_bv 64 1)] -> ssp_cells m canary -> rw_cells asegs m (TP_A + -96) [C8 cb] ->
  rw_cells asegs m (bv_unsigned sp + -96 - pad + -128) (once_full_cells G_LS_ONCE oldcb canary (Z_to_bv 64 1) (Z_to_bv 64 (f + 32)) s4 (Z_to_bv 64 OPT_LOAD_STRINGS) (Z_to_bv 64 f)
                                                          (Z_to_bv 64 (bv_unsigned sp + -96 - pad)) (Z_to_bv 64 (bv_unsigned sp + -96 - pad))) ->
  rw_cells asegs m (bv_unsigned sp + -96 - pad + -32) [CB 8 junk; C8 (Z_to_bv 64 RUN_ONCE_RET)] ->
  rw_cells asegs m (bv_unsigned sp + -96 - pad + -16) [C8 sp; C8 (Z_to_bv 64 SITE_icf_ls)] ->
  stk asegs m lo (bv_unsigned sp + -96 - pad + -128) ->
  rw_cells asegs m G_LS_RET [C4 (Z_to_bv 64 1)] -> rw_cells asegs m G_IC_OPTS_LOCK [C8 (Z_to_bv 64 p1)] -> 0 <= p1 < 2^64 ->
  rw_cells asegs m G_IC_OPTSDONE [C8 (Z_to_bv 64 0)] -> acc asegs m G_IC_OPTSDONE 8 ->
  rw_cells asegs m (f + 32) [C8 (Z_to_bv 64 0)] ->
  rw_cells asegs m (f / 8 + 2147450880) [C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 0); C1 b5; C1 b6; C1 b7] ->
  rw_cells asegs m f [C8 mg] ->
  mem_inv asegs m ->
  evt asegs (if_w3_post sp gp tp t0 t1 t2 a5 a6 a7 s4 s10 s11 t3 t4 t5 t6 F fc f lo pad oldcb canary m)
    (MS (mkR (Z_to_bv 64 ONCE_RET_INIT) (Z_to_bv 64 (bv_unsigned sp + -96 - pad + -128)) gp tp t0 t1 t2 (Z_to_bv 64 G_LS_ONCE) (Z_to_bv 64 e_loadstr)
             a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 0) (Z_to_bv 64 ssp_guard) (Z_to_bv 64 1) (Z_to_bv 64 3) (Z_to_bv 64 2)
             (Z_to_bv 64 1) (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f) s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 ONCE_RET_INIT) fc None m (seg_rom asegs)).
Proof.
  intros until b7. intros HP F0 F64 FIMG FLO FSH HLO HLOS SPH -> UT SHC ONCE SSP CBC OF PO FRR ST LSR OLC HP1 OD ACCO TMP SB FM MI.
  unfold OPT_LOAD_STRINGS, G_LS_ONCE, G_LS_RET, G_IC_OPTS_LOCK, G_IC_OPTSDONE, SITE_icf_ls, g_shadow_memory_dynamic_address in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  set (SP0 := SP + -96 - pad) in *.
  assert (HSP0 : SP - 112 <= SP0 <= SP - 96) by (unfold SP0; lia).
  pose proof (munch_refl [(SP0 - 160, SP0); (0xb9f300, 0xb9f300 + 4); (TP_A + -96, TP_A + -88); (0xb9f2a0, 0xb9f2a0 + 8); (f, f + 8); (f + 32, f + 40);
                          (f / 8 + 2147450880, f / 8 + 2147450880 + 8)] m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  assert (SHR : 0x7fff8000 <= f / 8 + 2147450880 /\ f / 8 + 2147450880 + 8 <= 0x10007fff8000).
  { pose proof (Z.div_pos f 8 ltac:(lia) ltac:(lia)). assert (f / 8 + 8 <= 2^44) by (Z.div_mod_to_equations; lia). lia. }
  assert (HWU : ut_fp [(SP0 - 160, SP0); (0xb9f300, 0xb9f300 + 4); (TP_A + -96, TP_A + -88); (0xb9f2a0, 0xb9f2a0 + 8); (f, f + 8); (f + 32, f + 40);
                       (f / 8 + 2147450880, f / 8 + 2147450880 + 8)]) by (clear - HSP0 HLO HLOS SPH F0 FIMG FLO FSH SHR; ut_fp_lia).
  assert (EUf : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  pose proof (div8_facts f) as Q1.
  (* [comment removed for export] *)
  tcall (T_run_once_leave_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo SP0 0xb9f300).
  all: try first [eassumption | reflexivity | unfold got_ssp, ssp_guard; lia | unfold got_ssp, ssp_guard; left; lia].
  cbv beta delta [mkR]. rewrite (ret_pc_even 2045872) by lia. destruct PC0 as [GOT GU]. unfold got_ssp, ssp_guard in GOT, GU.
  zstep; th_if_lit. zstep. zstep. zstep; th_if_lit.
  do 10 (zstep; zstep; th_if_lit).
  do 6 zstep. zstep.
  (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (VA1 : acc asegs mX 12186272 8)
      by (apply (acc_agree m mX _ _ ACCO ltac:(lia)); apply (agree_of_munch _ m mX _ MU); intros y Hy; cbv beta in Hy; unfold shad, SHB in Hy; cbn [outside]; lia);
    assert (SB4 : rw_cells asegs mX (f / 8 + 2147450880 + 4) [C1 (Z_to_bv 8 0)])
      by (exact (rw_cells_head mX _ _ _ (rw_cells_skip mX (f / 8 + 2147450880) [C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15))] _ SB)));
    assert (RA1 : acc asegs mX (f + 32) 8)
      by (apply (acc_of_shadow0 mX (f + 32)); [replace (shad (f + 32)) with (f / 8 + 2147450880 + 4) by (unfold shad, SHB; Z.div_mod_to_equations; lia); exact (rw_C1_bytes mX _ _ SB4)
                                            | Z.div_mod_to_equations; lia | lia])
  end.
  tcall (T_atomic_or_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo (Z_to_bv 64 0) (Z_to_bv 64 0)).
  all: try first [eassumption | reflexivity | exact (ut_munch _ m _ UT MU HWU) | unfold IMG_UT_LO, IMG_UT_HI; lia | Z.div_mod_to_equations; lia].
  change (Z.lor 0 2) with 2 in PC2. subst x3.
  zstep. zstep.
  (* [comment removed for export] *)
  zstep. (zstep; lfix). zstep. zstep. (zstep; lfix).
  zstep; if_cases KF2; zify_cond KF2; [exfalso; lia|].
  zstep. do 8 (zstep; lfix).
  subst SP0 SP. rewrite ?Z_to_bv_bv_unsigned in *.
  unfold if_w3_post, G_LS_ONCE, G_IC_OPTSDONE, OPT_LOAD_STRINGS, SITE_icf_or, SITE_icb_release, ICB_RETIRED.
  apply evt_done; do 6 eexists; split; [reflexivity|].
  split; [eapply munch_weaken; [| exact MU]; unfold sub_fp; cbn [outside app]; intros; lia|].
  repeat (split; [first [eassumption | split; assumption]|]); eassumption.
Qed.
