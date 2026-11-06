(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Tac Bytes Arr SysStep ITree Nodes NodesCfg Decode SFModel.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Prelim Monad StdioBase Stdio.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Top Require Import TrzStdio TrzLeaf.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import AsanLayout.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA AImages LazyModel ITreeA NodesA ImplRzA MonadA TrzNodesA CompatE2.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import BM_kit BI_shadow BI_globals2 B_iface BI_iface BI_lowshadow BM_stdio_lib BX_file BI_memtoshadow BI_region_is_poisoned BX_trz BM_fwrite BI_fwrite_icp BX_Exit BX_adapt BI_adapt2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Ltac aceil := first [pose proof alloc_ceiling_range as CEILB | idtac].
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Section Adapt.
Variable APS : Type.
Variable AHK : APS -> list ablock -> list fblock -> mem -> Model -> Prop.
Variable SO : APS -> stdout_st.
Variables (aS : APS -> word -> Prop) (aN : APS -> nat) (aEB : APS -> Z).
Variable aalloc_same : APS -> APS -> Prop.
Notation C := ACONSTS.

(* [comment removed for export] *)
Definition stdio_ivs : list (Z * Z) := [(0xa9c68, 0xa9c68 + 232); (0xa9d58, 0xa9d58 + 232); (0x601c58, 0x602060)]%Z.

(* [comment removed for export] *)
Definition AHK_icp_stdio_upd_stmt : Prop :=
  forall s LB LF m mo m' W so' guard cdt thr sec tm1,
    AHK s LB LF m mo -> munch W m m' -> wmono bsegs m m' -> mem_inv bsegs m' ->
    Forall (fun iv => aclient_write_ok C LB iv \/ In iv stdio_ivs) W ->
    stdio_state m' so' guard cdt thr sec tm1 -> zlength (so_buf so') <= STDOUT_BUFSIZ ->
    exists s', AHK s' LB LF m' mo /\ SO s' = so' /\ aalloc_same s s' /\ aS s' = aS s /\ aN s' = aN s /\ aEB s' = aEB s.
Definition AHK_icp_lowpages_stmt : Prop :=
  forall s LB LF m mo lo hi, AHK s LB LF m mo -> 0x7fff7000 <= lo -> hi <= 0x8fff7000 -> pages_budgeted (aS s) lo hi.

Hypothesis Hkip : AHK_kip_stmt C APS AHK aS aN aEB.
Hypothesis Hmi : AHK_mem_inv_stmt bsegs APS AHK.
Hypothesis Hso : AHK_so_stmt APS AHK SO.
Hypothesis Hglob : AHK_icp_globals_stmt bsegs APS AHK.
Hypothesis Hglob2 : AHK_icp_globals2_stmt APS AHK.
Hypothesis Hexit : AHK_icp_exit_stmt APS AHK SO aS.
Hypothesis Hupd : AHK_icp_stdio_upd_stmt.
Hypothesis Hlow : AHK_icp_lowpages_stmt.

#[local] Notation wz := (fun z : Z => Z_to_bv 64 z).
#[local] Notation usp sp := (bv_unsigned sp).

Lemma afwrite_diag_rz :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (s : APS) (LB : list ablock) (LF : list fblock)
         (sa lo : Z) (zs : list Z) (K : TSet),
  K [] -> AHK s LB LF m mo ->
  bytes_at bsegs m sa (zb zs) -> Forall (fun c => 0 <= c < 256) zs -> 0 < zlength zs < 4096 -> c_img_lo C <= sa -> sa + zlength zs <= 0x21060 ->
  stk bsegs m lo (usp sp) -> alloc_ceiling <= lo -> lo <= usp sp - AICP_STACK -> usp sp < 2^47 -> tp = wz (c_tp C) -> frm0 fc ->
  a0 = wz sa -> a1 = wz (zlength zs) -> a2 = wz 1 -> a3 = wz (c_stderr_F C) ->
  (forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem) (mo' : Model) (s' : APS),
     stk bsegs m' lo (usp sp) -> munch [(lo, usp sp); (c_stderr_F C, c_stderr_F C + 232)] m m' -> wmono bsegs m m' -> frm0 fc' ->
     AHK s' LB LF m' mo' -> aalloc_same s s' -> SO s' = SO s -> m_fs mo' = m_fs mo -> m_fds mo' = m_fds mo -> magree mo mo' ->
     realizes_cfg acfg bsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F' (ret_pc ra) fc' None m' (seg_rom bsegs)) mo') K) ->
  realizes_cfg acfg bsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz (c_wrap_fwrite C)) fc None m (seg_rom bsegs)) mo) (ShapeAlg.t_emit (Wz 2 zs) K).
Proof. aceil.
  intros until K. intros HK0 HA SRC HF LEN HSA HSN ST LOC LO SPTS HTP FRM -> -> -> -> HK.
  cbv beta. unfold AICP_STACK in LO. cbn [c_img_lo ACONSTS] in HSA.
  destruct (Hkip _ _ _ _ _ HA) as (Hh & Hminv & HLI & POL & MAG).
  pose proof (Hmi _ _ _ _ _ HA) as MI.
  pose proof (Hglob _ _ _ _ _ HA) as G. pose proof (Hglob2 _ _ _ _ _ HA) as G2.
  destruct (Hexit _ _ _ _ _ HA) as (_ & (guard & cdt & thr & sec & tm1 & SS) & LS & _ & _ & LDS & LDI).
  destruct SS as (STAT & SIN & SOF & SEF & SSP).
  destruct (rodata_shadow_clean _ sa (zlength zs) LS ltac:(lia) ltac:(lia) ltac:(lia)) as (ws & SHW & RC).
  pose proof (shw_geom 0x7fff8000 sa (zlength zs) ltac:(lia) ltac:(lia) ltac:(lia)) as GD; cbv zeta in GD.
  assert (BLO : 0x7fffa000 <= shw_lo 0x7fff8000 sa).
  { unfold shw_lo, al8 in *. rewrite Z.shiftr_div_pow2 in * by lia. change (2^3) with 8 in *. Z.div_mod_to_equations. lia. }
  assert (BHI : shw_hi 0x7fff8000 sa (zlength zs) <= 0x7fffc8bc).
  { unfold shw_hi, al8 in *. rewrite Z.shiftr_div_pow2 in * by lia. change (2^3) with 8 in *. Z.div_mod_to_equations. lia. }
  pose proof (bv_unsigned_in_range 64 sp) as SR. unfold bv_modulus in SR. cbn in SR.
  aceil.
  set (P := acc_ok (m_vm_lazy mo) (aS s)).
  assert (IM : implMA bsegs P (stderr_fwrite zs : M stdout_st unit) (SO s) (fwrite_icp_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m sa (zlength zs) 0x7fff8000 ws lo guard (SO s))
                 (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz sa) (wz (zlength zs)) (wz 1) (wz 0xa9c68) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x42fe0) fc None m (seg_rom bsegs))).
  { unfold implMA. eapply implA_evtA. { stepA. apply evtA_done. eapply eq_refl. } cbv beta. intros ms' <-.
    eapply (fwrite_icp_body P ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m sa (zlength zs) 0x7fff8000 ws lo guard);
      try reflexivity.
    - exact LOC.   (* [comment removed for export] *)
    - unfold FWRITE_ICP_DEPTH. lia.
    - exact SPTS.
    - lia.
    - unfold range_in_mem, A_HIGHEND_VAL. left. lia.
    - lia. - lia.
    - destruct SHW as [_ L]. exact L.
    - exact RC.
    - right. lia.
    - lia.
    - intros a k H1 H2. apply POL. unfold adrv_acc. cbn [fst snd]. rewrite unsigned_lit by lia. left. aceil. lia.
    - intros a k H1 H2. apply POL. unfold adrv_acc. cbn [fst snd c_img_lo c_img_hi ACONSTS]. rewrite unsigned_lit by lia. right; left. lia.
    - intros a k H1 H2. right. eapply (pages_budgeted_acc_inS _ (shw_lo 0x7fff8000 sa) (shw_hi 0x7fff8000 sa (zlength zs))); [eapply (Hlow _ _ _ _ _ _ _ HA); lia | lia | exact H1 | exact H2 | lia].
    - intros a. right. split; [| intros k Hk; cbn in Hk; lia]. unfold acc_nowrap. cbn [fst snd].
      pose proof (bv_unsigned_in_range 64 (Z_to_bv 64 a)) as X. unfold bv_modulus in X. cbn in X. lia.
    - exact ST.
    - exact MI.
    - exact SRC.
    - exact HF.
    - exact SEF.
    - exact SSP.
    - exact G. - exact G2. - exact SHW. }
  unfold implMA in IM.
  eapply (implA_trzA_srealizes bsegs (aS s) (aN s) (aEB s) P (stderr_fwrite zs (SO s)) _ _ mo mo (fun _ _ => K) _ IM).
  - apply (trzA_stderr_fwrite zs (SO s) mo (fun _ _ => K) Hminv ltac:(unfold WRITEV_MAX; lia) HK0).
  - apply mequiv_refl.
  - split; [split; [exact HLI | split; [exact Hminv | exact Hh]] | intros x Hx; exact Hx].
  - intros r ms' mot' moa' Q L Heq HKP.
    apply (leaf_stderr_fwrite_ok zs (SO s)) in L as [-> ->]; [| unfold WRITEV_MAX; lia].
    cbn [epost fst snd] in Q. unfold fwrite_icp_post in Q.
    destruct Q as (x5 & x6 & x7 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & m' & -> & MU & WM & MI' & ST' & W1 & SSP1 & G1 & G21 & SW1 & _).
    (* [comment removed for export] *)
    assert (SS1 : stdio_state m' (SO s) guard cdt thr sec tm1).
    { split; [| split; [| split; [| split; [exact W1 | exact SSP1]]]].
      - destruct STAT as (L1 & L2 & L3 & L4 & L5). unfold stdio_statics.
        repeat split; (eapply rw_cells_transport; [eassumption | exact MU | exact WM | cbn; lia]).
      - unfold stdin_file, stdin_cells in *. eapply rw_cells_transport; [exact SIN | exact MU | exact WM | cbn; lia].
      - destruct SOF as (fl & md & tl & bb & FC & R1 & BUF & R2). exists fl, md, tl, bb. unfold file_cells in *.
        split; [eapply rw_cells_transport; [exact FC | exact MU | exact WM | cbn; lia]|].
        split; [exact R1|]. split; [eapply rw_cells_transport; [exact BUF | exact MU | exact WM | cbn; lia]| exact R2]. }
    destruct (Hupd s LB LF m mo m' _ (SO s) guard cdt thr sec tm1 HA MU WM MI'
                ltac:(constructor; [left; unfold aclient_write_ok; cbn [fst snd]; left; aceil; lia |];
                      constructor; [right; unfold stdio_ivs; cbn; left; reflexivity | constructor])
                SS1 (Hso _ _ _ _ _ HA)) as (s' & HA' & SO' & SAME & EaS & EaN & EaEB).
    pose proof (mequiv_magree _ _ Heq) as Hag.
    destruct HKP as [[HLIa _] _].
    destruct (Hkip _ _ _ _ _ HA') as (_ & _ & _ & _ & MAG').
    rewrite <- EaS, <- EaN, <- EaEB in HLIa.
    pose proof (MAG' moa' Hag HLIa) as HA''.
    pose proof (magree_frame _ _ Hag) as (Efds & _ & _ & Efs & _).
    eapply (HK _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m' moa' s').
    + exact ST'.
    + cbn [c_stderr_F ACONSTS]. exact MU.
    + exact WM. + exact FRM. + exact HA''. + exact SAME. + exact SO'.
    + exact Efs. + exact Efds.
    + exact Hag.
Qed.
End Adapt.
End RC__1.
