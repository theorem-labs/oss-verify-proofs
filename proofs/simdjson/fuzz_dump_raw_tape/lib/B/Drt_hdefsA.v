(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS StoreFast FP SysStep.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Spec Require Import Prelim SjModel.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Sj Require Import SjTape SjTapeList SjTapeTile.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import Layout RT_iface RT_iface2 RT_iface3 D_defs D_kit D_clx D_libiface Sj_rtf Sj_akit Sj_acps Sj_hkit Sj_num_akit Sj_h_alloc Sj_stage2_iface Atp_fzwA Atp_activewA Atp_defsA Atp_pidiA Pj_defsA Pj_os_defsA Pj_hdefsA El_defsA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition DRT_SM3_A : Z := 0x64f6c.
Definition DRT_SMRET_A : Z := 0xaecd4.
Definition DRT_MS1RET_A : Z := 0xaee70.
Definition DRT_MS2RET_A : Z := 0xaee90.
Definition DRT_PIDRET_A : Z := 0xaeeac.
Definition DRT_OKARM_A : Z := 0xaeebc.
Definition DRT_CTORRET_A : Z := 0xaef5c.
Definition DRT_BORET_A : Z := 0xaef8c.
Definition DRT_LOCRET_A : Z := 0xaefa4.
Definition DRT_IOSRET_A : Z := 0xaefac.
Definition DRT_JOIN_A : Z := 0xaf040.
Definition DRT_PDRET_A : Z := 0xaf048.
Definition DRT_SSRET_A : Z := 0xaf090.
Definition DRT_VTT_A : Z := 0x168e68.
Definition DRT_HDR_DESC_A : Z := 0x1a1af.
Definition DRT_MAGIC0 : Z := 0x41b58ab3.
Definition DRT_MAGIC1 : Z := 0x45e0360e.

Definition DRT_OKARM_STACK_A : Z := EL_DUMP_STACK_A.

Definition drt_saved (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 : word) : list cell :=
  [C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
Lemma drt_saved_size : forall ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9, cells_size (drt_saved ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9) = 80%nat.
Proof. intros. reflexivity. Qed.

Definition drt_locals0 (j0 j1 jr : list byte) : list cell := [CB 16 j0; CB 8 j1; CB 24 jr].
Definition drt_locals1 (j0 : list byte) (f : Z) (jr : list byte) : list cell := [CB 16 j0; C8 (Z_to_bv 64 f); CB 24 jr].

Definition drt_sh (par os : Z) : list byte :=
  repeat (Z_to_bv 8 (-15)) 4 ++ repeat (Z_to_bv 8 par) 10 ++ repeat (Z_to_bv 8 (-14)) 4 ++ repeat (Z_to_bv 8 os) 36 ++ repeat (Z_to_bv 8 (-13)) 10.
Definition drt_sh_pro : list byte := drt_sh 0 (-8).
Definition drt_sh_ok : list byte := drt_sh 0 0.
Definition drt_sh_x : list byte := drt_sh (-8) (-8).
Lemma drt_sh_length : forall a b, length (drt_sh a b) = 64%nat.
Proof. intros. reflexivity. Qed.
Lemma cells_size_map_C1 : forall bs : list byte, cells_size (map C1 bs) = length bs.
Proof. induction bs as [|b bs IH]; [reflexivity|]. cbn [map cells_size csize length]. rewrite IH. reflexivity. Qed.

Definition sj_lib_rng (x : Z) : Prop :=
  0x6aa2c0 <= x < 0x6aa2c8 \/ 0x6aa2e0 <= x < 0x6aa2e2 \/ 0x6aa360 <= x < 0x6aa38c \/ 0x6aa3c0 <= x < 0x6aa3c2.
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
  - exists 0x6aa2c0, 0x6aa2c8. split; [cbn; tauto| lia].
  - exists 0x6aa2e0, 0x6aa2e8. split; [cbn; tauto| lia].
  - exists 0x6aa360, 0x6aa390. split; [cbn; tauto| lia].
  - exists 0x6aa3c0, 0x6aa3c8. split; [cbn; tauto| lia].
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
Lemma el_lib_rng_static : forall x, el_lib_rng x -> client_static x /\ 0x172ec0 <= x < 0x6cc15c.
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

Definition drt_ftail (j112 jos j432 : list byte) : list cell := [CB 32 j112; CB 288 jos; CB 72 j432].

Definition lf_regs (pc : Z) (ra : word) (sp' : Z) (gp t0 t1 t2 : word) (usp : Z) (a0 a1 a2 a3 a4 a5 a6 a7 : word) (f : Z) (s5 s6 s7 s9 s10 s11 : word)
    (t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state :=
  MS (mkR ra (Z_to_bv 64 sp') gp (Z_to_bv 64 TPV_A) t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 sp') a0 a1 a2 a3 a4 a5 a6 a7
          (Z_to_bv 64 f) (Z_to_bv 64 (shad f)) (Z_to_bv 64 (f + 32)) s5 s6 s7 (Z_to_bv 64 f) s9 s10 s11 t3 t4 t5 t6)
     F (Z_to_bv 64 pc) fc None m (seg_rom bsegs).

Section HStmts.
Variable RT : rt_sig.
Notation wz z := (Z_to_bv 64 z) (only parsing).

Definition drt_sm3_contract : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 0x6abde8 ->
  (length (rt_frames RT Σ) < FRAMES_MAX)%nat -> 1 <= rt_credit RT Σ ->
  ART RT Σ m -> mem_inv bsegs m -> call_ok RT Σ m sp lo ->
  (rt_frames RT Σ = [] -> bv_unsigned sp + 0xa0 <= rt_sp0 RT Σ) ->
  cps bsegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc DRT_SM3_A m)))
    (fun c => exists (Σ' : rts RT) (f : Z),
       ASTA RT Σ' PMc (fun ms => exists m', ret_stF fc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 f) m' ms
         /\ rt_after RT Σ' (bv_unsigned sp) lo m m' /\ rt_pres (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) m m'
         /\ wr_at bsegs m' f (fs_size 3 - 8) /\ wr_at bsegs m' (shad f) (fs_size 3 / 8)) c
       /\ rt_frames RT Σ' = (f, 3%nat) :: rt_frames RT Σ /\ rt_live RT Σ' = rt_live RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ' = rt_credit RT Σ - 1 /\ 0 < f /\ f mod 64 = 0 /\ f + fs_size 3 < USTACK_TOP).

Section WithPM.
Variable PMc : Model -> Prop.
Notation aevt := (aevt RT PMc).

Definition drt_okarm_cost (E : aenvA) : Z := EL_DUMP_C0 + EL_DUMP_CW * ae_n E + EL_DUMP_CSB * ae_sn E.
Definition drt_okarm_W (X : lfA) : list (Z * Z) :=
  [(lf_F X + 144, lf_F X + 432); (shad (lf_F X) + 18, shad (lf_F X) + 54); (EL_TPLOC_A, EL_TPLOC_A + 8)] ++ EL_LIB_FP.

Definition drt_okarm_cpsA : Prop :=
  forall (Σ : rts RT) (K : config -> Prop) (X : lfA) (E : aenvA)
         (ra gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s5 s6 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (j20 j112 jos j432 : list byte),
  fdfs_only PMc -> mat_stable PMc ->
  lfA_ok X -> aenvA_ok E -> lf_envA X E -> ae_p1 E = [] -> tape_wfS (ae_T E) (ae_S E) (ae_sn E) ck_any (ae_n E) ->
  a_live RT Σ E -> rt_frames RT Σ = [(lf_F X, 3%nat)] ->
  AINV_A E m -> el_libA m -> libc_nl m -> io_ssp m ->
  rw_cells bsegs m (lf_S1 X + 24) (res_cellsA (lf_F X + 56) (wz 0) j20) ->
  rw_cells bsegs m (lf_F X + 112) (drt_ftail j112 jos j432) ->
  rw_cells bsegs m (shad (lf_F X)) (map C1 drt_sh_pro) ->
  ART RT Σ m -> mem_inv bsegs m -> stk bsegs m (lf_lo X) (lf_S1 X) -> lf_lo X + DRT_OKARM_STACK_A <= lf_S1 X -> frm0 fc ->
  drt_okarm_cost E <= rt_credit RT Σ ->
  (forall (Σ' : rts RT) ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' m' j112' jos' j432',
     frm0 fc' -> ART RT Σ' m' -> mem_inv bsegs m' -> stk bsegs m' (lf_lo X) (lf_S1 X) ->
     rt_live RT Σ' = rt_live RT Σ -> rt_frames RT Σ' = rt_frames RT Σ -> rt_sp0 RT Σ' = rt_sp0 RT Σ ->
     rt_credit RT Σ - drt_okarm_cost E <= rt_credit RT Σ' ->
     rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (lf_S1 X) (drt_okarm_W X) m m' ->
     AINV_A E m' -> el_libA m' -> LOCBA m' ->
     rw_cells bsegs m' (lf_F X + 112) (drt_ftail j112' jos' j432') ->
     rw_cells bsegs m' (shad (lf_F X)) (map C1 drt_sh_pro) ->
     aevt Σ' K (lf_regs DRT_JOIN_A ra' (lf_S1 X) gp t0' t1' t2' (lf_usp X) a0' a1' a2' a3' a4' a5' a6' a7' (lf_F X)
                  (wz (lf_F X + 144)) (wz (lf_F X + 56)) (wz (lf_F X + 272)) s9 s10 s11 t3' t4' t5' t6' F' fc' m')) ->
  aevt Σ K (lf_regs DRT_OKARM_A ra (lf_S1 X) gp t0 t1 t2 (lf_usp X) (wz 0) a1 a2 a3 a4 a5 a6 a7 (lf_F X)
               s5 s6 (wz (lf_F X + 56)) s9 s10 s11 t3 t4 t5 t6 F fc m).

End WithPM.
End HStmts.
