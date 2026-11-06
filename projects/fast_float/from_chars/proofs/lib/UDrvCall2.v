(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require PropExec CatExec CatSim SeqExec StepTac StoreOk.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require StepTac.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Frame RefMemcpyLib DriverCfg.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.PropExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.CatExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.CatSim OSSVerify.Proofs.fast_float.from_chars.lib.Common.SeqExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.StepTac OSSVerify.Proofs.fast_float.from_chars.lib.Common.StoreOk OSSVerify.Proofs.fast_float.from_chars.lib.Common.StepTac.Hoare OSSVerify.Proofs.fast_float.from_chars.lib.Common.Frame OSSVerify.Proofs.fast_float.from_chars.lib.Common.RefMemcpyLib OSSVerify.Proofs.fast_float.from_chars.lib.Common.DriverCfg.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound FxMem FxRgs FxFacts FxSubst FxStep FxDrv.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound.FxGlue OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxRgs OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxDrv.
From OSSVerify.Proofs.fast_float.from_chars.lib Require Import UDrvData UDrvCall UbStdioDefs UbStdioWrite.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition file_post (RF : region) (lbuf lbsz : lin) : region :=
  track RF 32 (bvs_of (ladd lbuf lbsz) 8 ++ bvs_of lbuf 8 ++ repeat (BK 0) 8 ++ bvs_of lbuf 8).

Definition sw_template (L : sst) (ret : Z) (i0 : nat) (o0 : Z) (i5 : nat) (lbuf lbsz lres : lin) : sst :=
  let L1 := havoc_call L ret KEEP [(i0, o0, 112); (i5, 32, 16); (i5, 56, 8)] (Some lres) in
  match nth_error (s_rgs L) i5 with
  | Some RF => upd_rg L1 i5 (file_post RF lbuf lbsz)
  | None => L1
  end.

Theorem fx_stdio_write : forall E L ms model K (su f wb wp fd : Z) (s l bufp bufsz can ret : word) (pending extra : list byte)
    (i0 : nat) (o0 : Z) (i5 : nat) (RF : region) (lbuf lbsz lres : lin),
  sden PSEGS E L ms -> s_pc L = 0x55e08 -> s_resv L = RNone -> ms_rom ms = seg_rom PSEGS ->
  havoc_ok L [(i0, o0, 112); (i5, 32, 16); (i5, 56, 8)] (Some lres) = true ->
  state_wf (sw_template L (bv_unsigned ret) i0 o0 i5 lbuf lbsz lres) = true ->
  frame_in E L i0 o0 112 (su - 112) ->
  nth_error (s_rgs L) i5 = Some RF -> rg_base RF = lconst f -> rg_size RF = lconst 232 -> wkind (rg_kind RF) = true ->
  getr (ms_regs ms) 2 = Z_to_bv 64 su -> getr (ms_regs ms) 10 = Z_to_bv 64 f ->
  getr (ms_regs ms) 11 = s -> getr (ms_regs ms) 12 = l -> getr (ms_regs ms) 1 = ret ->
  (4294967296 + 112 <= su)%Z -> (su <= 0x800000000000)%Z ->
  (0x66b70 <= f)%Z -> (f + 232 <= 0x97c00)%Z ->
  sw_file (ms_mem ms) f wb wp fd bufp bufsz -> ssp_cells (ms_mem ms) can ->
  rdn PSEGS (ms_mem ms) (Z_to_bv 64 (f + 48)) 8 = Some (repeat (Z_to_bv 8 0) 8) ->
  (0 < fd < 2147483648)%Z -> fd_lookup (m_fds model) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) ->
  m_halted model = None -> m_vm_lazy model = [] ->
  (0 <= wb <= wp)%Z -> (wp <= TASK_SIZE)%Z -> (wp - wb = Z.of_nat (length pending))%Z ->
  (bv_unsigned l = Z.of_nat (length extra))%Z ->
  (Z.of_nat (length pending) + Z.of_nat (length extra) <= 2 ^ 30)%Z ->
  (Z.of_nat (length pending) + Z.of_nat (length extra) <= 2 ^ 30)%Z ->
  (wp <= su - 112 \/ su <= wb)%Z -> (bv_unsigned s + bv_unsigned l <= su - 112 \/ su <= bv_unsigned s)%Z ->
  (bv_unsigned s + bv_unsigned l <= TASK_SIZE)%Z ->
  rdn PSEGS (ms_mem ms) (Z_to_bv 64 wb) (length pending) = Some pending ->
  rdn PSEGS (ms_mem ms) s (length extra) = Some extra ->
  bv_unsigned ret mod 2 = 0 -> K [] ->
  lden E lbuf = bufp -> lden E lbsz = bufsz -> lden E lres = l -> lwf (s_next L) lbuf = true -> lwf (s_next L) lbsz = true ->
  (forall E' ms', agree (s_next L) E E' -> sden PSEGS E' (sw_template L (bv_unsigned ret) i0 o0 i5 lbuf lbsz lres) ms' ->
      sw_post (ms_mem ms) su f bufp bufsz (ms_mem ms') -> ms_rom ms' = ms_rom ms ->
      realizes PSEGS (mkCfg ms' model) K) ->
  realizes PSEGS (mkCfg ms model) (t_emit (map (WriteEv (Z_to_bv 64 fd)) (pending ++ extra)) K).
Proof.
  intros E L ms model K su f wb wp fd s l bufp bufsz can ret pending extra i0 o0 i5 RF lbuf lbsz lres
         Hd Hpc Hrv Hrom Hok Hwf Hfi Hi5 HbF HsF HwF H2 H10 H11 H12 H1 Su1 Su2 F1 F2 SWF SSP H48 FD Hfd Hh Hl
         W1 W2 W3 W4 W5 W6 D1 D2 W7 R1 R2 Hret HKnil Hlb Hls Hlr Hwb Hws Hk.
  rewrite (sden_mkst PSEGS E L ms Hd Hrv). rewrite Hpc, Hrom.
  set (fxs := mkFP (ms_fregs ms) (ms_fcsr ms)).
  set (regs := ms_regs ms) in *. set (mem := ms_mem ms) in *.
  pose proof (frame_in_store_ok E L ms i0 o0 112 _ Hd Hfi ltac:(lia)) as Hst.
  replace (Z_to_bv 64 0x55e08) with (0x55e08%bv : word) by (apply bv_eq; reflexivity).
  apply (@ref_stdio_write fxs regs mem model su f wb wp fd s l bufp bufsz can ret pending extra K
           H2 H10 H11 H12 H1 Su1 Su2 Hst F1 F2 SWF SSP FD Hfd Hh Hl W1 W2 W3 W4 W5 W6 D1 D2 W7 R1 R2 (ret_ok_even ret Hret) HKnil).
  intros regs' mem' Q10 Q2 Q1 Q8 Q9 Q18 Q19 Q20 Q21 Q22 Q23 Q24 Q25 Q26 Q27 Q3 Q4 Hpost.
  set (ms' := @mkst fxs regs' ret mem' (seg_rom PSEGS)).
  assert (HszF : forall E0, rsz E0 RF = 232) by (intros E0; apply rsz_const; [exact HsF | unfold two64; lia]).
  destruct Hfi as (R0 & Hi0 & Ha0 & Hwk0 & Ho0 & Hn0).
  assert (HfA : bv_unsigned (lden E (rg_base RF)) = f).
  { rewrite HbF. unfold lconst, lden, lz. cbn [l_c l_t tsum]. rewrite Z.add_0_r, w64_mod, Z.mod_small by (unfold two64; lia).
    apply u_small64. unfold two64; lia. }
  assert (P1 : ms_pc_val ms' = Z_to_bv 64 (bv_unsigned ret)) by (cbn; symmetry; apply Z_to_bv_bv_unsigned).
  assert (P2 : forall r : reg, existsb (Pos.eqb (rkey r)) KEEP = true -> rkey r <> 11%positive \/ Some lres = None ->
                 getr (ms_regs ms') r = getr regs r).
  { intros r Hr _. unfold ms', mkst; cbn [ms_regs]. apply keep_cs in Hr. unfold callee_saved in Hr.
    repeat (destruct Hr as [<-|Hr]; [first [assumption | rewrite Q1, H1; reflexivity | rewrite Q2, H2; reflexivity]|]). destruct Hr. }
  assert (P3 : forall l0, Some lres = Some l0 -> getr (ms_regs ms') (Z_to_bv 5 10) = lden E l0).
  { intros l0 Hl0. injection Hl0 as <-. unfold ms', mkst; cbn [ms_regs]. rewrite Hlr. exact Q10. }
  assert (P4 : forall i R x, nth_error (s_rgs L) i = Some R -> in_rg E R x -> ~ in_fp E (s_rgs L) [(i0, o0, 112); (i5, 32, 16); (i5, 56, 8)] x ->
                 ms_mem ms' x = ms_mem ms x).
  { intros i R x Hi Hin Hnf. unfold ms', mkst; cbn [ms_mem]. apply (swp_agree _ _ _ _ _ _ Hpost).
    - intros Hx. apply Hnf. exists i0, o0, 112, R0. split; [left; reflexivity|]. split; [exact Hi0|]. lia.
    - intros Hx. apply Hnf. exists i5, 32, 16, RF. split; [right; left; reflexivity|]. split; [exact Hi5|]. lia.
    - intros Hx. apply Hnf. exists i5, 56, 8, RF. split; [right; right; left; reflexivity|]. split; [exact Hi5|]. lia. }
  assert (P5 : forall i R x, nth_error (s_rgs L) i = Some R -> in_rg E R x -> ms_mem ms x <> None -> ms_mem ms' x <> None).
  { intros i R x Hi Hin Hm. unfold ms', mkst; cbn [ms_mem]. exact (swp_grows _ _ _ _ _ _ Hpost x Hm). }
  destruct (havoc_call_sound PSEGS E L ms ms' (bv_unsigned ret) KEEP [(i0, o0, 112); (i5, 32, 16); (i5, 56, 8)] (Some lres) Hok Hd
              P1 eq_refl eq_refl (sden_frm _ _ _ _ Hd) P2 P3 P4 P5) as (E' & Ha' & Hd1).
  set (L1 := havoc_call L (bv_unsigned ret) KEEP [(i0, o0, 112); (i5, 32, 16); (i5, 56, 8)] (Some lres)) in *.
  assert (HRF1 : nth_error (s_rgs L1) i5 = Some (havoc_rg_i [(i0, o0, 112); (i5, 32, 16); (i5, 56, 8)] i5 RF)).
  { unfold L1, havoc_call. cbn [s_rgs]. rewrite (nth_map_i _ _ 0 i5 RF Hi5). reflexivity. }
  set (RF1 := havoc_rg_i [(i0, o0, 112); (i5, 32, 16); (i5, 56, 8)] i5 RF) in *.
  assert (HbF1 : rg_base RF1 = rg_base RF) by (unfold RF1, havoc_rg_i; destruct (fp_targets _ _); reflexivity).
  assert (HsF1 : rg_size RF1 = rg_size RF) by (unfold RF1, havoc_rg_i; destruct (fp_targets _ _); reflexivity).
  assert (HfA' : bv_unsigned (lden E' (rg_base RF)) = f).
  { rewrite HbF. unfold lconst, lden, lz. cbn [l_c l_t tsum]. rewrite Z.add_0_r, w64_mod, Z.mod_small by (unfold two64; lia).
    apply u_small64. unfold two64; lia. }
  assert (Hlb' : lden E' lbuf = bufp) by (rewrite <- Hlb; symmetry; exact (lden_agree _ E E' lbuf Hwb Ha')).
  assert (Hls' : lden E' lbsz = bufsz) by (rewrite <- Hls; symmetry; exact (lden_agree _ E E' lbsz Hws Ha')).
  (* [comment removed for export] *)
  assert (HR0 : rg_ok PSEGS E' mem RF).
  { unfold havoc_ok in Hok. apply andb_prop in Hok as [Hok _]. apply andb_prop in Hok as [Hwf0 _].
    unfold state_wf in Hwf0. apply andb_prop in Hwf0 as [Hwf0 _]. apply andb_prop in Hwf0 as [Hwf0 _].
    apply andb_prop in Hwf0 as [_ Hrw]. rewrite forallb_forall in Hrw.
    exact (rg_ok_agree PSEGS _ E E' mem RF (Hrw RF (nth_error_In _ _ Hi5)) Ha' (sden_rg _ _ _ _ _ _ Hd Hi5)). }
  assert (HR2 : rg_ok PSEGS E' mem' (file_post RF lbuf lbsz)).
  { unfold file_post. apply (rg_ok_refresh PSEGS E' mem mem' RF 32); [exact HR0 | exact HwF | lia | rewrite HszF; cbn [length app]; rewrite length_app; cbn; lia | | | ].
    - intros i Hi Hni. rewrite HszF in Hi. rewrite HfA'. apply (swp_agree _ _ _ _ _ _ Hpost).
      + rewrite u_small64 by (unfold two64; lia). lia.
      + rewrite u_small64 by (unfold two64; lia). cbn [length app] in Hni. rewrite length_app in Hni. cbn in Hni. lia.
      + rewrite u_small64 by (unfold two64; lia). cbn [length app] in Hni. rewrite length_app in Hni. cbn in Hni. lia.
    - intros i Hi Hm. exact (swp_grows _ _ _ _ _ _ Hpost _ Hm).
    - rewrite HfA'. rewrite !map_app, !bvs_of_den_lin, lden_ladd, Hlb', Hls'.
      change (length (bvs_of (ladd lbuf lbsz) 8 ++ bvs_of lbuf 8 ++ repeat (BK 0) 8 ++ bvs_of lbuf 8)) with (8 + (8 + (8 + 8)))%nat.
      apply rdn_app_some; [lia | unfold two64; lia | |].
      { rewrite (swp_wend _ _ _ _ _ _ Hpost). unfold v_add, word_to_le_bytes. rewrite bv_add_unsigned, Z_to_bv_unsigned. reflexivity. }
      apply rdn_app_some; [lia | unfold two64; lia | |].
      { replace (f + 32 + Z.of_nat 8) with (f + 40) by lia. rewrite (swp_wpos _ _ _ _ _ _ Hpost). reflexivity. }
      apply rdn_app_some; [lia | unfold two64; lia | |].
      { replace (f + 32 + Z.of_nat 8 + Z.of_nat 8) with (f + 48) by lia.
        rewrite (rdn_ext_rd1 PSEGS mem' mem (f + 48) 8); [ | lia | unfold two64; lia |].
        - rewrite H48. reflexivity.
        - intros i Hi. unfold rd1. rewrite (swp_agree _ _ _ _ _ _ Hpost); [reflexivity | | |]; rewrite u_small64 by (unfold two64; lia); lia. }
      { replace (f + 32 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8) with (f + 56) by lia. rewrite (swp_wbase _ _ _ _ _ _ Hpost). reflexivity. } }
  assert (Hd2 : sden PSEGS E' (upd_rg L1 i5 (file_post RF lbuf lbsz)) ms').
  { apply (fx_upd_rg PSEGS E' L1 ms' i5 RF1 _ Hd1 HRF1); [unfold file_post, track; rewrite HbF1; reflexivity | unfold file_post, track; rewrite HsF1; reflexivity | exact HR2 |].
    unfold sw_template in Hwf. fold L1 in Hwf. rewrite Hi5 in Hwf. exact Hwf. }
  apply (Hk E' ms' Ha'); [| exact Hpost | unfold ms', mkst; cbn [ms_rom]; symmetry; exact Hrom].
  unfold sw_template. fold L1. rewrite Hi5. exact Hd2.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.fast_float.from_chars.lib Require Import Spec UbExit.
Open Scope Z_scope.

Theorem fx_exit : forall E L ms model (code : word) (pending : list byte),
  sden PSEGS E L ms -> s_pc L = 0x52be0 -> s_resv L = RNone -> ms_rom ms = seg_rom PSEGS ->
  exit_pre (ms_regs ms) (ms_mem ms) model code pending ->
  realizes PSEGS (mkCfg ms model) (t_emit (W 1 pending) (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model))).
Proof.
  intros E L ms model code pending Hd Hpc Hrv Hrom Hpre.
  rewrite (sden_mkst PSEGS E L ms Hd Hrv). rewrite Hpc, Hrom.
  apply (@ref_exit_Z (mkFP (ms_fregs ms) (ms_fcsr ms))). exact Hpre.
Qed.
