(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CallLit CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA RA_seql RA_sjs3 PF_low PF_file PF_vf.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIcp2qs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc AIcp7wm.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpkua.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpkua.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.AIcpdmn OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcp7wm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpkua.AIcpilj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpkua.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd Require Import DA_Eg3i DA_Cells DA_Ldix.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Storrsf.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import ExN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac hot_qset := lazymatch goal with |- evt _ ?Q _ => lazymatch Q with (fun _ => _) => set (hotQ := Q) | _ => idtac end | |- _ => idtac end.
Ltac hot_qend := lazymatch goal with |- evt _ ?Q _ => first [ is_var Q; subst Q | idtac ] | |- ?Q _ => first [ is_var Q; subst Q; cbv beta | idtac ] | |- _ => idtac end.
Import ListNotations.
Open Scope bv_scope.

Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
(* [comment removed for export] *)
From Ltac2 Require Ltac2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require KDrop.
Ltac hot_kdrop := ltac2:(Ltac2.Control.enter (fun () => OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.kdrop_marked ())).
Local Ltac transport_after_call segs m m' MU WM ::= hot_kdrop; transport_after_call_fast segs m m' MU WM.
(* [comment removed for export] *)
Local Ltac lia ::= lia3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require JunkName.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.split_for_access H segs m A cs kn n ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.JunkName.split_for_access_jn H segs m A cs kn n.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require LiaSec.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_sec.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.word_eq_guarded.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor0fe.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor0fe.sb_mem_after_store_sf.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Diet8ul.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Diet8ul.dlia_sec.
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac cbn_mfp := cbn [mf_set_flags mf_set_buf mf_set_w mf_set_rp mf_set_mode mf_set_write_lbf
   mf_flags mf_rpos mf_rend mf_close mf_wend mf_wpos mf_mbz1 mf_wbase mf_read mf_write mf_seek mf_buf mf_bufsize
   mf_prev mf_next mf_fd mf_pipepid mf_lockcount mf_mode mf_lock mf_lbf mf_pad148].
Ltac cbn_mfp_in H := cbn [mf_set_flags mf_set_buf mf_set_w mf_set_rp mf_set_mode mf_set_write_lbf
   mf_flags mf_rpos mf_rend mf_close mf_wend mf_wpos mf_mbz1 mf_wbase mf_read mf_write mf_seek mf_buf mf_bufsize
   mf_prev mf_next mf_fd mf_pipepid mf_lockcount mf_mode mf_lock mf_lbf mf_pad148] in H.
Local Ltac icpt_consts_in H ::= unfold PC1_DEPTH, pc1_post, towrite_post in H; cbn_mfp_in H.

Definition VF_WR_RET : Z := 0x9e4f0.   (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma split_ibuf : forall m a (jk : list byte),
  rw_cells rsegs m a [CB 248 jk] -> rw_cells rsegs m a [CB 80 (firstn 80 jk); CB 168 (skipn 80 jk)].
Proof.
  intros m a jk H. pose proof (rw_CB_length _ _ _ _ _ H) as L.
  eapply rw_cells_recast_pf; [exact H| |].
  - cbn [cells_wf cell_wf]. rewrite length_firstn, length_skipn. split; [lia| split; [lia| exact I]].
  - cbn [cells_bytes cbytes]. rewrite !app_nil_r. apply firstn_skipn.
Qed.

Section VFU.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Variables (FMT : list cell) (la : Z).
  Hypothesis HLA : Z.of_nat (cells_size FMT) = la.
  Hypothesis P1 : pass1_stmt FMT la.
  Hypothesis TOW : towrite_stmt.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (lo A Fa VA : Z) (canary : word) (f : mfile).
  #[local] Notation q := (bv_unsigned sp).
  #[local] Notation SB := (mf_buf f).            (* [comment removed for export] *)
  #[local] Notation ib := (q + -352)%Z.     (* [comment removed for export] *)
  Hypothesis LO : (lo <= q - VFB_DEPTH)%Z.
  Hypothesis QHI : (q <= 2^47)%Z.
  Hypothesis GT : (alloc_ceiling <= lo)%Z.   (* [comment removed for export] *)
  Hypothesis ARL : (IMG_LO <= A)%Z.
  Hypothesis ART : (A + la <= RO_TOP)%Z.
  Hypothesis VAR : (0 <= VA < 2^64)%Z.
  Hypothesis FL5 : mf_flags f = 5%Z.
  Hypothesis LCK : mf_lock f = (-1)%Z.
  Hypothesis BSZ : mf_bufsize f = 0%Z.
  Hypothesis SBR : (0 < SB < 2^63)%Z.
  Hypothesis MODE : (0 <= mf_mode f < 2^32)%Z.
  Hypothesis FAR : (FILE_LO <= Fa /\ Fa + 152 <= FILE_HI)%Z.

  (* [comment removed for export] *)
  Definition vfu_frame (m1 : word -> option byte) (jb jr : list byte) : Prop :=
       rw_cells rsegs m1 (q + -368) [C8 (Z_to_bv 64 VA)]
    /\ rw_cells rsegs m1 (q + -360) [C8 (Z_to_bv 64 VA)]
    /\ rw_cells rsegs m1 ib [CB 80 jb]
    /\ rw_cells rsegs m1 (q + -272) [CB 168 jr]
    /\ rw_cells rsegs m1 (q + -104) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
         C8 canary; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  (* [comment removed for export] *)
  Definition vfu_file1 (mo : Z) : mfile :=
    mf_set_mode (mf_set_rp (mf_set_w (mf_set_buf (mf_set_flags f 5) ib 80) (Z_to_bv 64 ib) (Z_to_bv 64 ib) (Z_to_bv 64 (ib + 80))) w0 w0) mo.

  Definition vfu_pre_post (m : word -> option byte) : machine_state -> Prop :=
    fun ms => exists (t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 : word) (jb jr : list byte) (mo : Z) (m' : word -> option byte),
      ms = MS (mkR (Z_to_bv 64 VF_PC2_RET) (Z_to_bv 64 (q + -368)) gp tp t0 t1 t2 (Z_to_bv 64 Fa) (Z_to_bv 64 A)
                   (Z_to_bv 64 Fa) (Z_to_bv 64 A) (Z_to_bv 64 (q + -368)) (Z_to_bv 64 (q + -272)) (Z_to_bv 64 (q + -104)) a5 a6 a7
                   (Z_to_bv 64 SSP_GUARD) (Z_to_bv 64 1) (Z_to_bv 64 SB) (Z_to_bv 64 5) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 PRINTF_CORE) fc None m' (seg_rom rsegs)
      /\ munch [(q - VFB_DEPTH, q); (Fa, Fa + 152)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
      /\ stk rsegs m' lo (q + -368)
      /\ vfu_frame m' jb jr
      /\ file_at m' Fa (vfu_file1 mo).

  #[using="FAR MODE BSZ LCK FL5 ART GT QHI LO TOW P1 HLA la Clg"] Lemma vfu_pre : forall t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (m : word -> option byte),
    a0 = Z_to_bv 64 Fa -> a1 = Z_to_bv 64 A -> a2 = Z_to_bv 64 VA ->
    stk rsegs m lo q -> ro_cells rsegs m A FMT -> ssp_cells m canary -> file_at m Fa f -> mem_inv rsegs m ->
    evt rsegs (vfu_pre_post m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x9e3c8) fc None m (seg_rom rsegs)).
  Proof.
    intros until m. intros -> -> -> ST HF [SSP1 SSP2] FILE MI.
    pose proof alloc_ceiling_val as CV. unfold vfu_pre_post, vfu_frame, vfu_file1.
    unfold RA_seql.GOT_SSP, RA_seql.SSP_GUARD, DA_Eg3i.SSP_GUARD, GLOBALS_TOP, RO_TOP, VFB_DEPTH, IMG_LO, IMG_HI, FILE_LO, FILE_HI, VF_PC2_RET, PRINTF_CORE in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (ro_cells_bound _ _ _ _ HF) as AB.
    pose proof (munch_refl [(bv_unsigned sp - 5296, bv_unsigned sp); (Fa, Fa + 152)]%Z m) as MU.
    pose proof (wmono_refl rsegs m) as WM.
    assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
    pose proof FILE as FILE'. unfold file_at, file_cells in FILE. rewrite FL5, LCK, BSZ in FILE.
    carve_frame 368%nat ST.
    hot_qset.
    zto 0x9e578%Z. name_junk FR.
    (* [comment removed for export] *)
    call_lit P1 by (idtac;
      lazymatch goal with
      | |- stk _ _ _ _ => rewrite ?unsigned_lit by lia; eassumption
      | |- ssp_cells _ _ => split; eassumption
      | |- ro_cells _ _ _ _ => eassumption
      | |- mem_inv _ _ => eassumption
      | |- @eq _ _ _ => reflexivity
      | |- _ => rewrite ?unsigned_lit by lia; unfold PC1_DEPTH, GLOBALS_TOP, RO_TOP in *; lia
      end || match goal with |- ?G => idtac "P1SIDE-FAIL:" G end).
    rename POST into ST.
    zto 0x9e45c%Z. rewrite !sx32_small by lia.
    (* [comment removed for export] *)
    zs. zs. zs.
    zs. br K. clear K.
    do 8 zs.
    (* [comment removed for export] *)
    zs. zs.
    pose proof TOW as TW. unfold towrite_stmt in TW.
    try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_FILE); call_icpt (TW _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ Fa
                 (mf_set_buf (mf_set_w (mf_set_flags f 5) w0 w0 w0) (bv_unsigned sp + -352)%Z 80)) by (idtac;
      cbn_mfp;
      lazymatch goal with
      | |- file_at ?mx _ _ => unfold file_at, file_cells; cbn_mfp; rewrite LCK; exact FILE
      | |- mem_inv _ _ => eassumption
      | |- @eq _ _ _ => first [reflexivity | rewrite ?unsigned_lit by lia; reflexivity]
      | |- _ => lia
      end || match goal with |- ?G => idtac "TOWSIDE-FAIL:" G end).
    lazymatch goal with H : file_at ?mx Fa ?fx |- _ => rename H into FILE1 end.
    replace (bv_unsigned sp + -352 + 80)%Z with (bv_unsigned sp + -272)%Z in FILE1 by lia.
    zs. br K. clear K.
    zto 0x9e578%Z.
    all: hot_qend.
    (* [comment removed for export] *)
    apply (proj1 (rw_cells_app rsegs _ _ [_] _)) in FR. destruct FR as [APC FR]. cbn [cells_size csize Nat.add] in FR.
    apply (proj1 (rw_cells_app rsegs _ _ [_] _)) in FR. destruct FR as [AP2 FR]. cbn [cells_size csize Nat.add] in FR.
    apply (proj1 (rw_cells_app rsegs _ _ [_] _)) in FR. destruct FR as [JB FR]. cbn [cells_size csize Nat.add] in FR.
    lazymatch type of JB with rw_cells _ _ _ [CB 248 ?jk] =>
      apply split_ibuf in JB; apply (proj1 (rw_cells_app rsegs _ _ [_] _)) in JB; destruct JB as [JB JR]; cbn [cells_size csize Nat.add] in JR end.
    hot_qend; apply evt_done.
    replace (ib + 80)%Z with (q + -272)%Z by lia.   (* [comment removed for export] *)
    hot_eexists_all.
    split; [reflexivity|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
    split. { split; [exact APC|]. split; [eapply rwc_eq; [exact AP2| lia]|]. split; [eapply rwc_eq; [exact JB| lia]|].
             split; [eapply rwc_eq; [exact JR| lia]|]. eapply rwc_eq; [exact FR| lia]. }
    lazymatch goal with H : file_at ?mx Fa (mf_set_mode ?fa ?mo1) |- file_at _ _ (mf_set_mode ?fb ?mo2) =>
      unify mo2 mo1; replace (mf_set_mode fb mo1) with (mf_set_mode fa mo1) by reflexivity; exact H end.
    Unshelve. all: try exact 0%Z; try exact [].
  Qed.

  (* [comment removed for export] *)
  Definition vfu_mid_post (r : word) (m : word -> option byte) : machine_state -> Prop :=
    fun ms => exists (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word),
      ms = MS (mkR (Z_to_bv 64 VF_WR_RET) (Z_to_bv 64 (q + -368)) gp tp t0 t1 t2 (Z_to_bv 64 Fa) r
                   (Z_to_bv 64 Fa) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 STDIO_WRITE) a4 a5 a6 a7
                   (Z_to_bv 64 SSP_GUARD) (Z_to_bv 64 1) (Z_to_bv 64 SB) (Z_to_bv 64 0) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 STDIO_WRITE) fc None m (seg_rom rsegs)
      /\ stk rsegs m lo (q + -368).

  #[using="SBR FMT Clg"] Lemma vfu_mid : forall t0 t1 t2 (r : word) a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (m : word -> option byte) (f2 : mfile),
    stk rsegs m lo (q + -368) -> file_at m Fa f2 -> mf_flags f2 = 5%Z -> mf_write f2 = STDIO_WRITE -> mem_inv rsegs m ->
    evt rsegs (vfu_mid_post r m)
      (MS (mkR (Z_to_bv 64 VF_PC2_RET) (Z_to_bv 64 (q + -368)) gp tp t0 t1 t2 (Z_to_bv 64 Fa) (Z_to_bv 64 A)
               r a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 SSP_GUARD) (Z_to_bv 64 1) (Z_to_bv 64 SB) (Z_to_bv 64 5) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 VF_PC2_RET) fc None m (seg_rom rsegs)).
  Proof.
    intros until f2. intros ST FILE FL2 WR2 MI. unfold vfu_mid_post.
    pose proof alloc_ceiling_val as CV.
    unfold RA_seql.GOT_SSP, RA_seql.SSP_GUARD, DA_Eg3i.SSP_GUARD, GLOBALS_TOP, RO_TOP, VFB_DEPTH, IMG_LO, IMG_HI, FILE_LO, FILE_HI, VF_PC2_RET, VF_WR_RET, STDIO_WRITE in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl ([] : list ivl) m) as MU. pose proof (wmono_refl rsegs m) as WM.
    unfold file_at, file_cells in FILE. rewrite FL2, WR2 in FILE.
    hot_qset.
    zs. zs. zs. br K. clear K.
    zs. zs. zs. zs. zs.
    all: hot_qend.
    hot_qend; apply evt_done. hot_eexists_all. split; [reflexivity| exact ST].
  Qed.

  (* [comment removed for export] *)
  Definition vfu_post_post (r : word) (f3 : mfile) (m : word -> option byte) : machine_state -> Prop :=
    fun ms => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : word -> option byte),
      ms = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 r a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (ret_pc ra) fc None m' (seg_rom rsegs)
      /\ munch [(q - VFB_DEPTH, q); (Fa, Fa + 152)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
      /\ stk rsegs m' lo q
      /\ file_at m' Fa (mf_set_buf (mf_set_w f3 w0 w0 w0) SB 0).

  #[using="FAR GT LO FMT Clg"] Lemma vfu_post : forall t0 t1 t2 (r : word) a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (m : word -> option byte) (f3 : mfile) (jb jr : list byte) (wp3 : Z) (apw : word),
    stk rsegs m lo (q + -368) -> ssp_cells m canary -> file_at m Fa f3 -> mf_flags f3 = 5%Z -> mf_wpos f3 = Z_to_bv 64 wp3 -> (0 < wp3 < 2^64)%Z ->
    mem_inv rsegs m ->
    rw_cells rsegs m (q + -368) [C8 apw] -> rw_cells rsegs m (q + -360) [C8 (Z_to_bv 64 VA)] -> rw_cells rsegs m ib [CB 80 jb] ->
    rw_cells rsegs m (q + -272) [CB 168 jr] ->
    rw_cells rsegs m (q + -104) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
         C8 canary; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    evt rsegs (vfu_post_post r f3 m)
      (MS (mkR (Z_to_bv 64 VF_WR_RET) (Z_to_bv 64 (q + -368)) gp tp t0 t1 t2 (Z_to_bv 64 Fa) r
               a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 SSP_GUARD) (Z_to_bv 64 1) (Z_to_bv 64 SB) (Z_to_bv 64 0) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 VF_WR_RET) fc None m (seg_rom rsegs)).
  Proof.
    intros until apw. intros ST [SSP1 SSP2] FILE FL3 WP3 WPR MI APC AP2 JB JR FR.
    pose proof alloc_ceiling_val as CV. unfold vfu_post_post.
    unfold RA_seql.GOT_SSP, RA_seql.SSP_GUARD, DA_Eg3i.SSP_GUARD, GLOBALS_TOP, RO_TOP, VFB_DEPTH, IMG_LO, IMG_HI, FILE_LO, FILE_HI, VF_WR_RET in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (munch_refl [(bv_unsigned sp - 5296, bv_unsigned sp); (Fa, Fa + 152)]%Z m) as MU.
    pose proof (wmono_refl rsegs m) as WM.
    assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
    unfold file_at, file_cells in FILE. rewrite FL3, WP3 in FILE.
    (* [comment removed for export] *)
    hot_qset.
    do 9 zs.
    replace (0 <? wp3) with true in * by (symmetry; apply Z.ltb_lt; lia).
    change (Z.b2z true + -1)%Z with 0%Z in *. rewrite (swrap32_id 0%Z) in * by lia. change (0 mod 18446744073709551616)%Z with 0%Z in *.
    rewrite Z.lor_0_l in *. rewrite Z_to_bv_bv_unsigned in *.
    (* [comment removed for export] *)
    zto 0x9e530%Z. rewrite !sx32_small by lia.
    lazymatch goal with H : rw_cells rsegs _ Fa _ |- _ => rewrite !sx32_small in H by lia end.
    rewrite !(unsigned_lit 5%Z) by lia. change (Z.land 5 32)%Z with 0%Z. change (Z.lor 5 0)%Z with 5%Z.
    change ((Z.b2z (0 <? 1) + -1))%Z with 0%Z. rewrite (swrap32_id 0%Z) by lia. change (0 mod 18446744073709551616)%Z with 0%Z.
    rewrite Z.lor_0_l, Z_to_bv_bv_unsigned.
    lazymatch goal with H : rw_cells rsegs _ Fa _ |- _ => rewrite !(unsigned_lit 5%Z) in H by lia; change (Z.land 5 32)%Z with 0%Z in H; change (Z.lor 5 0)%Z with 5%Z in H end.
    zs. br K. clear K.
    (* [comment removed for export] *)
    zto 0x9e54c%Z. zs. brf Kc. { exfalso. apply Kc. reflexivity. } clear Kc.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mq _) =>
      lazymatch goal with A1 : rw_cells rsegs mq (bv_unsigned sp + -368) ?c1 |- _ =>
      lazymatch goal with A2 : rw_cells rsegs mq (bv_unsigned sp + -360) ?c2 |- _ =>
      lazymatch goal with A3 : rw_cells rsegs mq (bv_unsigned sp + -352) ?c3 |- _ =>
      lazymatch goal with A4 : rw_cells rsegs mq (bv_unsigned sp + -272) ?c4 |- _ =>
      lazymatch goal with A5 : rw_cells rsegs mq (bv_unsigned sp + -104) ?c5 |- _ =>
        assert (FRall : rw_cells rsegs mq (bv_unsigned sp + -368) (c1 ++ c2 ++ c3 ++ c4 ++ c5));
        [ apply (proj2 (rw_cells_app rsegs _ _ _ _)); split; [exact A1|]; cbn [cells_size csize Nat.add];
          apply (proj2 (rw_cells_app rsegs _ _ _ _)); split; [eapply rwc_eq; [exact A2| lia]|]; cbn [cells_size csize Nat.add];
          apply (proj2 (rw_cells_app rsegs _ _ _ _)); split; [eapply rwc_eq; [exact A3| lia]|]; cbn [cells_size csize Nat.add];
          apply (proj2 (rw_cells_app rsegs _ _ _ _)); split; [eapply rwc_eq; [exact A4| lia]|]; cbn [cells_size csize Nat.add];
          eapply rwc_eq; [exact A5| lia]
        | clear A1 A2 A3 A4 A5; cbn [app] in FRall ] end end end end end end.
    do 8 zs.
    lazymatch goal with STq : stk rsegs _ lo _ |- _ => release_frame FRall STq (bv_unsigned sp) end.
    zs.
    all: hot_qend.
    hot_qend; apply evt_done.
    hot_eexists_all.
    split; [reflexivity|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
    unfold file_at, file_cells. cbn_mfp. rewrite FL3. eassumption.
  Qed.
End VFU.
