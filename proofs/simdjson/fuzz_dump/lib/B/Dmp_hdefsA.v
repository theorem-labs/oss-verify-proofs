(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS StoreFast FP SysStep.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Spec Require Import Prelim SjModel.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Sj Require Import SjTape SjTapeList SjTapeTile.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import Layout RT_iface RT_iface2 RT_iface3 D_defs D_kit D_clx D_libiface Sj_rtf Sj_akit Sj_acps Sj_hkit Sj_num_akit Sj_h_alloc Sj_stage2_iface Atp_fzwA Atp_activewA Atp_defsA Atp_pidiA Pj_defsA Pj_os_defsA Pj_hdefsA El_defsA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition DMP_LFTOI_A : Z := 0xae648.
Definition DMP_SM3_A : Z := 0x64948.
Definition DMP_SMRET_A : Z := 0xae6b8.
Definition DMP_MS1RET_A : Z := 0xae854.
Definition DMP_MS2RET_A : Z := 0xae874.
Definition DMP_PIDRET_A : Z := 0xae890.
Definition DMP_OKARM_A : Z := 0xae8a8.
Definition DMP_CTORRET_A : Z := 0xae94c.
Definition DMP_PJ_A : Z := 0xaedf8.
Definition DMP_PJRET_A : Z := 0xae960.
Definition DMP_BORET_A : Z := 0xae974.
Definition DMP_LOCRET_A : Z := 0xae98c.
Definition DMP_IOSRET_A : Z := 0xae994.
Definition DMP_JOIN_A : Z := 0xaea28.
Definition DMP_PDRET_A : Z := 0xaea30.
Definition DMP_SSRET_A : Z := 0xaea70.
Definition DMP_VTT_A : Z := 0x1688c8.
Definition DMP_GOT_VT_A : Z := 0x16ee50.
Definition DMP_HDR_DESC_A : Z := 0x211f3.
Definition DMP_MAGIC0 : Z := 0x41b58ab3.
Definition DMP_MAGIC1 : Z := 0x45e0360e.

Definition DMP_PJ_FRAME_A : Z := 256.
Definition DMP_PJ_LEAF_A : Z := 12288 + 512 + RT_STACK.
Definition pj_needA (d : nat) : Z := DMP_PJ_FRAME_A * (Z.of_nat d + 1) + DMP_PJ_LEAF_A.
Definition DMP_OKARM_STACK_A : Z := pj_needA 1024%nat + 256.

Definition DMP_PJ_CW : Z := 12.
Definition DMP_PJ_C0 : Z := 16.
Definition pj_costA (i j : Z) : Z := DMP_PJ_CW * (j - i).

Definition dmp_okarm_cost (E : aenvA) : Z := DMP_PJ_C0 + DMP_PJ_CW * ae_n E.

Definition dmp_saved (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 : word) : list cell :=
  [C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
Lemma dmp_saved_size : forall ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10, cells_size (dmp_saved ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10) = 96%nat.
Proof. intros. reflexivity. Qed.

Definition dmp_locals0 (j0 jr : list byte) : list cell := [CB 8 j0; CB 24 jr].
Definition dmp_locals1 (f : Z) (jr : list byte) : list cell := [C8 (Z_to_bv 64 f); CB 24 jr].

Definition dmp_sh (par os : Z) : list byte :=
  repeat (Z_to_bv 8 (-15)) 4 ++ repeat (Z_to_bv 8 par) 10 ++ repeat (Z_to_bv 8 (-14)) 4 ++ repeat (Z_to_bv 8 os) 36 ++ repeat (Z_to_bv 8 (-13)) 10.
Definition dmp_sh_pro : list byte := dmp_sh 0 (-8).
Definition dmp_sh_ok : list byte := dmp_sh 0 0.
Definition dmp_sh_x : list byte := dmp_sh (-8) (-8).
Lemma dmp_sh_length : forall a b, length (dmp_sh a b) = 64%nat.
Proof. intros. reflexivity. Qed.
Lemma cells_size_map_C1 : forall bs : list byte, cells_size (map C1 bs) = length bs.
Proof. induction bs as [|b bs IH]; [reflexivity|]. cbn [map cells_size csize length]. rewrite IH. reflexivity. Qed.

Definition sj_lib_rng (x : Z) : Prop :=
  0x6a9840 <= x < 0x6a9848 \/ 0x6a9860 <= x < 0x6a9862 \/ 0x6a98e0 <= x < 0x6a990c \/ 0x6a9940 <= x < 0x6a9942.
Lemma sj_lib_agree : forall m m', sj_lib m -> agree_on sj_lib_rng m m' -> sj_lib m'.
Proof.
  intros m m' [(A & B & C & D)|(A & B & C & D)] AG; [left| right]; unfold lib0, lib1, sj_lib_rng in *;
    (split; [| split; [| split]]; [eapply rw_cells_agree_nw; [exact A|] | eapply rw_cells_agree_nw; [exact B|] | eapply rw_cells_agree_nw; [exact C|] | eapply rw_cells_agree_nw; [exact D|]];
     intros a Ha; apply AG; cbn [cells_size csize Nat.add] in Ha; lia).
Qed.
Lemma sj_lib_rng_fp : forall x, sj_lib_rng x -> in_ranges LIB_FP x.
Proof.
  intros x Hx. unfold sj_lib_rng, LIB_FP, in_ranges in *.
  destruct Hx as [H|[H|[H|H]]].
  - exists 0x6a9840, 0x6a9848. split; [cbn; tauto| lia].
  - exists 0x6a9860, 0x6a9868. split; [cbn; tauto| lia].
  - exists 0x6a98e0, 0x6a9910. split; [cbn; tauto| lia].
  - exists 0x6a9940, 0x6a9948. split; [cbn; tauto| lia].
Qed.
Lemma loc_rng_fp : forall x, PJ_LOC_LO_A <= x < PJ_LOC_HI_A -> in_ranges LIB_FP x.
Proof. intros x Hx. exists PJ_LOC_LO_A, PJ_LOC_HI_A. split; [unfold LIB_FP, PJ_LOC_LO_A, PJ_LOC_HI_A; cbn; tauto| exact Hx]. Qed.
Lemma lock_rng_fp : forall x, PJ_LOCKW_A <= x < PJ_LOCKW_A + 4 -> in_ranges LIB_FP x.
Proof. intros x Hx. exists PJ_LOCKW_A, (PJ_LOCKW_A + 4). split; [unfold LIB_FP, PJ_LOCKW_A; cbn; tauto| exact Hx]. Qed.
Lemma unw_rng_fp : forall x, EL_UNW_A <= x < EL_UNW_A + 8 -> in_ranges LIB_FP x.
Proof. intros x Hx. exists EL_UNW_A, (EL_UNW_A + 8). split; [unfold LIB_FP, EL_UNW_A; cbn; tauto| exact Hx]. Qed.
Lemma ehg_rng_fp : forall x, EL_EHG_A <= x < EL_EHG_A + 12 -> in_ranges LIB_FP x.
Proof. intros x Hx. exists EL_EHG_A, (EL_EHG_A + 12). split; [unfold LIB_FP, EL_EHG_A; cbn; tauto| exact Hx]. Qed.
Lemma tploc_rng_fp : forall x, EL_TPLOC_A <= x < EL_TPLOC_A + 8 -> in_ranges LIB_FP x.
Proof. intros x Hx. exists EL_TPLOC_A, (EL_TPLOC_A + 8). split; [unfold LIB_FP, EL_TPLOC_A, TPV_A; cbn; tauto| exact Hx]. Qed.

Lemma libc_nl_static : forall x, LIBC_NL <= x < LIBC_NL + 1 -> client_static x.
Proof. intros x Hx. apply client_static_intro. unfold LIBC_NL in Hx. lia. Qed.

Definition el_lib_rng (x : Z) : Prop := in_ranges LIB_FP x.
Lemma el_lib_rng_static : forall x, el_lib_rng x -> client_static x /\ 0x172920 <= x < 0x6cb6dc.
Proof. intros x H. exact (lib_fp_static x H). Qed.
Lemma el_libA_agree : forall m m', el_libA m -> agree_on el_lib_rng m m' -> el_libA m'.
Proof.
  intros m m' [(S & L & LW) (E & U & T)] AG. unfold el_lib_rng in AG. split; [split; [| split]| split; [| split]].
  - eapply sj_lib_agree; [exact S|]. intros a Ha. apply AG. exact (sj_lib_rng_fp _ Ha).
  - eapply pj_locA_agree; [exact L|]. intros a Ha. apply AG. exact (loc_rng_fp _ Ha).
  - eapply lockwA_agree; [exact LW|]. intros a Ha. apply AG. exact (lock_rng_fp _ Ha).
  - eapply rw_cells_agree_nw; [exact E|]. intros a Ha. apply AG. cbn [cells_size csize Nat.add] in Ha. apply ehg_rng_fp; lia.
  - destruct U as [uw U]. exists uw. eapply rw_cells_agree_nw; [exact U|]. intros a Ha. apply AG. rewrite uw_cellsA_size in Ha. apply unw_rng_fp; lia.
  - eapply rw_cells_agree_nw; [exact T|]. intros a Ha. apply AG. cbn [cells_size csize Nat.add] in Ha. apply tploc_rng_fp; lia.
Qed.

Lemma el_lib_loc : fp_local LIB_FP el_libA.
Proof. intros m m' H AG. apply (el_libA_agree m m' H). intros a Ha. apply AG. exact Ha. Qed.

Definition dmp_ftail (j112 jos j432 : list byte) : list cell := [CB 32 j112; CB 288 jos; CB 72 j432].

Definition lf_regs (pc : Z) (ra : word) (sp' : Z) (gp t0 t1 t2 : word) (usp : Z) (a0 a1 a2 a3 a4 a5 a6 a7 : word) (f : Z) (s5 s6 s7 s8 s11 : word)
    (t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state :=
  MS (mkR ra (Z_to_bv 64 sp') gp (Z_to_bv 64 TPV_A) t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 sp') a0 a1 a2 a3 a4 a5 a6 a7
          (Z_to_bv 64 f) (Z_to_bv 64 (shad f)) (Z_to_bv 64 (f + 32)) s5 s6 s7 s8 (Z_to_bv 64 f) (Z_to_bv 64 DMP_MAGIC1) s11 t3 t4 t5 t6)
     F (Z_to_bv 64 pc) fc None m (seg_rom bsegs).

Definition lf_regs10 (pc : Z) (ra : word) (sp' : Z) (gp t0 t1 t2 : word) (usp : Z) (a0 a1 a2 a3 a4 a5 a6 a7 : word) (f : Z) (s5 s6 s7 s8 s10 s11 : word)
    (t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state :=
  MS (mkR ra (Z_to_bv 64 sp') gp (Z_to_bv 64 TPV_A) t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 sp') a0 a1 a2 a3 a4 a5 a6 a7
          (Z_to_bv 64 f) (Z_to_bv 64 (shad f)) (Z_to_bv 64 (f + 32)) s5 s6 s7 s8 (Z_to_bv 64 f) s10 s11 t3 t4 t5 t6)
     F (Z_to_bv 64 pc) fc None m (seg_rom bsegs).

Section HStmts.
Variable RT : rt_sig.
Notation wz z := (Z_to_bv 64 z) (only parsing).

Section WithPM.
Variable PMc : Model -> Prop.
Notation aevt := (aevt RT PMc).

Definition dmp_okarm_W (X : lfA) : list (Z * Z) :=
  [(lf_F X + 144, lf_F X + 432); (shad (lf_F X) + 18, shad (lf_F X) + 54); (EL_TPLOC_A, EL_TPLOC_A + 8)] ++ EL_LIB_FP.

Definition dmp_okarm_cpsA : Prop :=
  forall (Σ : rts RT) (K : config -> Prop) (X : lfA) (E : aenvA)
         (ra gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s5 s6 s8 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (j20 j112 jos j432 : list byte),
  fdfs_only PMc -> mat_stable PMc ->
  lfA_ok X -> aenvA_ok E -> lf_envA X E -> ae_p1 E = [] -> tape_wfS (ae_T E) (ae_S E) (ae_sn E) ck_any (ae_n E) ->
  a_live RT Σ E -> rt_frames RT Σ = [(lf_F X, 3%nat)] ->
  AINV_A E m -> el_libA m -> libc_nl m -> io_ssp m ->
  rw_cells bsegs m (lf_S1 X + 8) (res_cellsA (lf_F X + 56) (wz 0) j20) ->
  rw_cells bsegs m (lf_F X + 112) (dmp_ftail j112 jos j432) ->
  rw_cells bsegs m (shad (lf_F X)) (map C1 dmp_sh_pro) ->
  ART RT Σ m -> mem_inv bsegs m -> stk bsegs m (lf_lo X) (lf_S1 X) -> lf_lo X + DMP_OKARM_STACK_A <= lf_S1 X -> frm0 fc ->
  dmp_okarm_cost E <= rt_credit RT Σ ->
  (forall (Σ' : rts RT) ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' m' j112' jos' j432',
     frm0 fc' -> ART RT Σ' m' -> mem_inv bsegs m' -> stk bsegs m' (lf_lo X) (lf_S1 X) ->
     rt_live RT Σ' = rt_live RT Σ -> rt_frames RT Σ' = rt_frames RT Σ -> rt_sp0 RT Σ' = rt_sp0 RT Σ ->
     rt_credit RT Σ - dmp_okarm_cost E <= rt_credit RT Σ' ->
     rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (lf_S1 X) (dmp_okarm_W X) m m' ->
     AINV_A E m' -> el_libA m' -> LOCBA m' ->
     rw_cells bsegs m' (lf_F X + 112) (dmp_ftail j112' jos' j432') ->
     rw_cells bsegs m' (shad (lf_F X)) (map C1 dmp_sh_pro) ->
     aevt Σ' K (lf_regs DMP_JOIN_A ra' (lf_S1 X) gp t0' t1' t2' (lf_usp X) a0' a1' a2' a3' a4' a5' a6' a7' (lf_F X)
                  (wz (lf_F X + 144)) (wz (lf_F X + 56)) (wz 1) (wz (lf_F X + 272)) s11 t3' t4' t5' t6' F' fc' m')) ->
  aevt Σ K (lf_regs DMP_OKARM_A ra (lf_S1 X) gp t0 t1 t2 (lf_usp X) (wz 0) a1 a2 a3 a4 a5 a6 a7 (lf_F X)
               s5 s6 (wz (lf_F X + 56)) s8 s11 t3 t4 t5 t6 F fc m).

End WithPM.
End HStmts.
