(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.ct.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac ITree Nodes Decode SysStep RzCPS NodesA. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim Monad Stdio Canon ProgDetTarget.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow X_bridge X_bridge2.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import SegRw.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface D_iface D_defs D_kit D_libiface D_clx R_thread D_cs RT_client_kit FX_Exit FX_Stdio_iface F_stdio_write F_stdio_exit I_iodefs F_fwrite I_fwrite X_atexit X_xdefs X_exitw.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtHXA Require HxaExitInit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtHXA Require HxaExit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition so_id (so : stdout_st) : stdout_st := so.
Definition so_set (so : stdout_st) (_ : stdout_st) : stdout_st := so.

Lemma TT_exit_flush : forall (so : stdout_st) (T : TSet),
  (so_first so = false \/ so_buf so = []) -> zlength (so_buf so) <= 2^26 -> T [] ->
  t_eq (TT ((stdout_exit_flush so_id so_set : @M stdout_st unit) so) (fun _ => T)) (t_emit (evw 1 (so_buf so)) T).
Proof.
  intros so T H Hl HT. unfold stdout_exit_flush, rd_so, mbind, mget, mret. cbn [ebind bind fst snd].
  unfold so_id at 1.
  destruct (Z.ltb_spec 0 (zlength (so_buf so))) as [Lt|Ge].
  - destruct H as [Hf|Hb]; [| rewrite Hb in Lt; unfold zlength in Lt; cbn in Lt; lia].
    unfold stdout_writefn, rd_so, mbind, mget, mret. cbn [ebind bind fst snd]. unfold so_id at 1. rewrite Hf.
    unfold stdout_stdio_write, rd_so, mbind, mget, mret, upd_so, mupd. cbn [ebind bind fst snd].
    rewrite TT_ebind. cbn [TT]. unfold so_id. unfold stdio_writev.
    assert (NE : so_buf so <> []) by (intros E; rewrite E in Lt; unfold zlength in Lt; cbn in Lt; lia).
    rewrite (iov_start_cons (so_buf so) [] NE).
    eapply t_eq_trans.
    { apply (TT_wv_loop (WV_FUEL [so_buf so; []]) 1 [so_buf so; []] so (fun _ => T)); [cbn; lia| | | exact HT];
        unfold WV_FUEL, iov_total; cbn [concat]; rewrite app_nil_r; lia. }
    cbn [concat]. rewrite app_nil_r. rewrite <- evw_to_bytes. apply t_eq_refl.
  - assert (E : so_buf so = []) by (destruct (so_buf so); [reflexivity| cbn in Ge; unfold zlength in Ge; cbn in Ge; lia]).
    rewrite E. cbn [TT evw map]. apply t_eq_sym, t_emit_nil_eq. exact HT.
Qed.

Lemma tok_exit_flush : forall (so : stdout_st),
  (so_first so = false \/ so_buf so = []) -> zlength (so_buf so) <= 2^26 ->
  tok [1] ((stdout_exit_flush so_id so_set : @M stdout_st unit) so).
Proof.
  intros so H Hl. unfold stdout_exit_flush, rd_so, mbind, mget, mret. cbn [ebind bind fst snd].
  unfold so_id at 1.
  destruct (Z.ltb_spec 0 (zlength (so_buf so))) as [Lt|Ge].
  - destruct H as [Hf|Hb]; [| rewrite Hb in Lt; unfold zlength in Lt; cbn in Lt; lia].
    unfold stdout_writefn, rd_so, mbind, mget, mret. cbn [ebind bind fst snd]. unfold so_id at 1. rewrite Hf.
    unfold stdout_stdio_write, rd_so, mbind, mget, mret, upd_so, mupd. cbn [ebind bind fst snd].
    apply tok_ebind; [| intros x; exact I].
    unfold so_id. unfold stdio_writev.
    assert (NE : so_buf so <> []) by (intros E; rewrite E in Lt; unfold zlength in Lt; cbn in Lt; lia).
    rewrite (iov_start_cons (so_buf so) [] NE).
    apply tok_wv_loop; [left; reflexivity| cbn; lia| |]; unfold WV_FUEL, iov_total; cbn [concat]; rewrite app_nil_r; lia.
  - cbn. exact I.
Qed.

(* [comment removed for export] *)
Lemma xe_wr_at_app : forall segs m a n1 n2, (0 <= n1)%Z -> (0 <= n2)%Z ->
  wr_at segs m a (n1 + n2) <-> wr_at segs m a n1 /\ wr_at segs m (a + n1) n2.
Proof.
  intros segs m a n1 n2 H1 H2. unfold wr_at. split.
  - intros (Ha & Hb & H). repeat split; try lia.
    + intros i Hi. apply H. lia.
    + intros i Hi. replace (a + n1 + i)%Z with (a + (n1 + i))%Z by lia. apply H. lia.
  - intros ((Ha & Hb & HA) & (Ha' & Hb' & HB)). repeat split; try lia.
    intros i Hi. destruct (Z.lt_ge_cases i n1).
    + apply HA. lia.
    + replace (a + i)%Z with (a + n1 + (i - n1))%Z by lia. apply HB. lia.
Qed.

Lemma xe_rw_cells_app : forall segs m A cs1 cs2,
  rw_cells segs m A (cs1 ++ cs2) <-> rw_cells segs m A cs1 /\ rw_cells segs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros segs m A cs1 cs2. unfold rw_cells, cells_at.
  rewrite cells_wf_app, cells_bytes_app, cells_size_app, Nat2Z.inj_add.
  rewrite xe_wr_at_app by lia. rewrite bytes_at_app.
  split.
  - intros (((W1 & W2) & (B1 & B2)) & (R1 & R2)).
    rewrite (cells_bytes_length cs1 W1) in B2. tauto.
  - intros (((W1 & B1) & R1) & ((W2 & B2) & R2)).
    rewrite <- (cells_bytes_length cs1 W1) in B2. tauto.
Qed.

Lemma xe_ro_cells_app : forall segs m A cs1 cs2,
  ro_cells segs m A (cs1 ++ cs2) <-> ro_cells segs m A cs1 /\ ro_cells segs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros segs m A cs1 cs2. unfold ro_cells, cells_at.
  rewrite cells_wf_app, cells_bytes_app. rewrite bytes_at_app.
  split.
  - intros ((W1 & W2) & (B1 & B2)). rewrite (cells_bytes_length cs1 W1) in B2. tauto.
  - intros ((W1 & B1) & (W2 & B2)). rewrite <- (cells_bytes_length cs1 W1) in B2. tauto.
Qed.

(* [comment removed for export] *)
Lemma xe_rw_sub : forall segs m A cs (k n : nat) A',
  rw_cells segs m A cs -> A' = A + Z.of_nat (cells_size (firstn k cs)) ->
  rw_cells segs m A' (firstn n (skipn k cs)).
Proof.
  intros segs m A cs k n A' H ->. rewrite <- (firstn_skipn k cs) in H. apply xe_rw_cells_app in H. destruct H as [_ H].
  rewrite <- (firstn_skipn n (skipn k cs)) in H. apply xe_rw_cells_app in H. exact (proj1 H).
Qed.
Lemma xe_ro_sub : forall segs m A cs (k n : nat) A',
  ro_cells segs m A cs -> A' = A + Z.of_nat (cells_size (firstn k cs)) ->
  ro_cells segs m A' (firstn n (skipn k cs)).
Proof.
  intros segs m A cs k n A' H ->. rewrite <- (firstn_skipn k cs) in H. apply xe_ro_cells_app in H. destruct H as [_ H].
  rewrite <- (firstn_skipn n (skipn k cs)) in H. apply xe_ro_cells_app in H. exact (proj1 H).
Qed.

Section XExit.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis AF_XIT : forall Σ m, ART RT Σ m -> xit_rt m.
Variable LIBX : mem -> Prop.
Hypothesis LIBX_exit : forall m, LIBX m -> lib_exit_cells m.

Local Ltac ul := unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK in *; lia.

(* [comment removed for export] *)
Definition xe_keep (x : Z) : Prop :=
  (0xbc9680 <= x < 0xbc9688) \/ (0xbc9ae8 <= x < 0xbca340) \/ (0x5af428 <= x < 0x5af720) \/ (0x5ab1e0 <= x < 0x5ab1e8) \/ (0xbc9430 <= x < 0xbc9438).

(* [comment removed for export] *)
Lemma exit_rest : forall (Σ : rts RT) F0 fs0 (gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (so : stdout_st) (code lo usp : Z) (jf : list byte) (cdt thr sec : byte) (tm1 g : word) T c,
  0 <= code < 256 -> tp = Z_to_bv 64 0xba93f0 ->
  (so = stdout_init \/ exists k, (k < 500)%nat /\ so = so_lines k) ->
  fd_lookup F0 (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)) ->
  SEGTOP_A + STACK_WIN <= rt_sp0 RT Σ <= USTACK_TOP -> 0x7fff80000000 <= rt_sp0 RT Σ ->
  mem_inv ctasegs m ->
  rw_cells ctasegs m (usp + -48) [CB 8 jf; C8 s1; C8 (Z_to_bv 64 code); C8 (Z_to_bv 64 0x51fc94)] ->
  stk ctasegs m lo (usp + -48) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo <= usp - 448 -> usp + 16 <= USTACK_TOP ->
  OUT_repA so m -> ERR_repA m ->
  rw_cells ctasegs m 0xbc9680 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->
  rw_cells ctasegs m 0xbc9ae8 [C8 (Z_to_bv 64 0)] ->
  rw_cells ctasegs m 0x5af510 [C8 (Z_to_bv 64 0x5af428)] ->
  rw_cells ctasegs m 0x5af6f0 [C8 (Z_to_bv 64 0x5af608)] ->
  stdin_file m -> rw_cells ctasegs m 0x5af600 [C8 (Z_to_bv 64 0x5af518)] ->
  ro_cells ctasegs m 0x5ab1e0 [C8 (Z_to_bv 64 0xbc9430)] -> ro_cells ctasegs m 0xbc9430 [C8 g] ->
  ASTA RT Σ (PMfd F0 fs0)
    (eq (MS (mkR (Z_to_bv 64 0x51fc10) (Z_to_bv 64 (usp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 0x533428) (Z_to_bv 64 0x533428)
                 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x51fc10) fc None m (seg_rom ctasegs))) c ->
  (forall c', EXITc fs0 code c' -> realizes ctasegs c' T) ->
  realizes ctasegs c (t_emit (evw 1 (so_buf so)) T).
Proof using AF.
  intros Σ F0 fs0 gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m so code lo usp jf
    cdt thr sec tm1 g T c Hcode Htp Hso HFD SP0R SP0W MI0 FR ST0 LOW LO448 SPT OUT ERR LIBC OFL SEU SOU SIN SINU G1 G2 Hc Hk.
  assert (LO0 : 0x7fff7f800000 <= lo) by ul.
  assert (SOK : (so_first so = false \/ so_buf so = []) /\ zlength (so_buf so) <= 2^26).
  { destruct Hso as [->|(k & Hk5 & ->)].
    - split; [right; reflexivity| unfold zlength; cbn; lia].
    - split; [left; reflexivity|]. cbn [so_lines so_buf]. rewrite zlength_zeros_out. lia. }
  set (ms0 := MS (mkR (Z_to_bv 64 0x51fc10) (Z_to_bv 64 (usp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 0x533428) (Z_to_bv 64 0x533428)
                 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x51fc10) fc None m (seg_rom ctasegs)) in *.
  (* [comment removed for export] *)
  set (Qfin := fun (x : unit * stdout_st) (ms' : machine_state) =>
                 ms_svc_pending ms' = Some (Z_to_bv 64 94) /\ areg ms' 10 = Z_to_bv 64 code).
  assert (IMPL : impl ctasegs (at_node ctasegs) ((stdout_exit_flush so_id so_set : @M stdout_st unit) so) (epost Qfin) ms0).
  { assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; ul).
    eapply impl_evt.
    { pose proof (exit_E_spec (Z_to_bv 64 usp) gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
               F fc m lo code jf ltac:(lia) ltac:(rewrite EU; exact FR) ltac:(rewrite EU; exact ST0)
               ltac:(rewrite EU; lia) ltac:(lia) ltac:(rewrite EU; ul) MI0) as W. rewrite EU in W. exact W. }
    intros ms1 PO. unfold exit_E_post in PO.
    destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & -> & ST1).
    rewrite EU in ST1.
    assert (OUT1 : stdout_file m so) by exact OUT.
    assert (ERR1 : stderr_file m) by (apply stderr_wfile0_file; exact ERR).
    assert (EU16 : bv_unsigned (Z_to_bv 64 (usp + -16)) = usp + -16) by (apply unsigned_lit; ul).
    pose proof (stdio_exit_proof so_id so_set (fun _ _ => eq_refl) (fun _ _ _ => eq_refl) (fun _ => eq_refl)) as SE.
    unfold stdio_exit_spec_stmt in SE.
    pose proof (SE (Z_to_bv 64 0x51fc98) (Z_to_bv 64 (usp + -16)) gp tp u0 u1 u2 (Z_to_bv 64 code) s1 b0 b1 b2 b3 b4 b5 b6 b7
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 F fc m lo so g cdt thr sec tm1
                  ltac:(rewrite EU16; exact ST1) LIBC OFL SINU SIN SOU SEU OUT1 ERR1 G1 G2 MI0 Htp
                  ltac:(rewrite EU16; ul) ltac:(ul)) as IM.
    clear SE. unfold implM in IM.
    rewrite EU.
    eapply impl_post_evt''; [exact IM|].
    intros [|[xr so']] ms2 H2; [apply evt_done; exact I|].
    cbn [epost fst snd] in H2 |- *. unfold stdio_exit_post in H2.
    destruct H2 as (v0 & v1 & v2 & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & so'' & m2 & -> & _ & _ & MI2 & _).
    rewrite (ret_pc_even 0x51fc98) by lia.
    eapply evt_mono; [exact (exit_tail_spec (usp + -16) code gp tp v0 v1 v2 s1 c0 c1 c2 c3 c4 c5 c6 c7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                               v3 v4 v5 v6 F fc m2 ltac:(lia) ltac:(assumption))|].
    intros ms3 (ra3 & ->). split; reflexivity. }
  (* [comment removed for export] *)
  assert (RZ : realizes ctasegs c (TT ((stdout_exit_flush so_id so_set : @M stdout_st unit) so) (fun _ => t_emit [] T))).
  { apply (impl_realizes ctasegs SEGTOP_A asegs_wx asegs_below [1] _ (rt_allow RT Σ) (fun mo => ARTM RT Σ mo /\ PMfd F0 fs0 mo) Qfin
             (fun _ => t_emit [] T) ms0 c
             (ASTA_PM_mat_stable RT AF Σ F0 fs0)); [| exact (tok_exit_flush so (proj1 SOK) (proj2 SOK))| exact Hc| exact IMPL|].
    - intros mo fd (HAR & HF & _) Hin. cbn in Hin. destruct Hin as [<-|[]]. rewrite HF. exact HFD.
    - intros x ms' c' (HS & HA0) Hc'.
      assert (R : realizes ctasegs c' T).
      { apply Hk.
        exists (rt_allow RT Σ), (eq ms'), (fun mo => ARTM RT Σ mo /\ PMfd F0 fs0 mo). split; [exact Hc'|]. split.
        + intros ms <-. split; [right; exact HS| exact HA0].
        + intros mo (_ & _ & HFS). exact HFS. }
      eapply rz_conseq; [exact R|]. apply t_eq_sym, t_emit_nil_eq. exact (realizes_nonempty ctasegs _ _ R). }
  eapply rz_conseq; [exact RZ|].
  eapply t_eq_trans; [apply TT_exit_flush; [exact (proj1 SOK)| exact (proj2 SOK)| apply t_emit_has_nil]|].
  eapply t_eq_trans; [apply t_eq_sym, t_emit_app|]. rewrite app_nil_r. apply t_eq_refl.
Qed.

(* [comment removed for export] *)
Lemma seg_stk : forall a b (m : mem), seg_rw_ok ctasegs a (b - a) = true -> stk ctasegs m a b.
Proof. intros a b m H. pose proof (proj2 (seg_rw_ok_sound ctasegs a (b - a) H m)) as S. replace (a + (b - a)) with b in S by lia. exact S. Qed.

(* [comment removed for export] *)
Lemma odr_ok : forallb (fun iv => seg_rw_ok ctasegs (fst iv) (snd iv - fst iv))
  [(12210080, 12210088); (12210528, 12210536); (12210848, 12210888); (12210976, 12210984); (12217824, 12217840); (12224032, 12224088);
   (12224128, 12224208); (12224288, 12224328); (12224384, 12224464); (12224512, 12224536); (12224640, 12225136)] = true.
Proof. vm_compute. reflexivity. Qed.

Theorem exit_ok : exit_contract RT XENVX OUT_repA ERR_repA LIBX.
Proof using AF AF_XIT LIBX_exit.
  intros Σ F0 fs0 ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m so code lo
    Ha0 Hcode Htp Hso HFD OUT ERR XE HLX ART0 MI0 CALL SSP LIVE E3.
  intros T c Hc Hk.
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R.
  pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  destruct CALL as (ST & LOW & LOR & SPT & SPA).
  pose proof (bv_unsigned_in_range 64 sp) as USR. unfold bv_modulus in USR.
  remember (bv_unsigned sp) as usp eqn:EUSP.
  destruct (AF_XIT Σ m ART0) as (FA & GF & GCX & (dso & DSO) & _ & _ & _ & _ & _ & _ & _ & COV & _).
  destruct XE as (n & f1 & a1v & ((tid & HT & TID) & (p1 & p2 & ATX) & ATA & EXL & (cdt & thr & sec & tm1 & LIBC) & OFL & SEU & SOU & SIN & SINU
                  & GDS & FLG & CPL) & NH & (pcb & ICB0)).
  assert (ICB : rw_cells ctasegs m 0xba4694 [C1 (Z_to_bv 8 0)])
    by exact (xe_rw_sub ctasegs m 0xba4691 [CB 3 pcb; C1 (Z_to_bv 8 0)] 1 1 0xba4694 ICB0 eq_refl).
  unfold AEF_CALLX, AEF_GUARDX in NH.
  destruct SSP as (g & G1 & G2).
  destruct (LIBX_exit m HLX) as (b0 & BI & DGC).
  assert (LO0 : 0x7fff7f800000 <= lo) by ul.
  assert (LOX : lo <= usp - 48 - 1024 - 448) by ul.
  assert (Htp' : tp = Z_to_bv 64 tpA) by exact Htp.
  (* [comment removed for export] *)
  pose proof (exit_A_spec ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                F fc m lo code tid (Z_to_bv 8 0) p1 p2 cdt thr sec tm1 dso b0 n f1 a1v Ha0 Htp' ltac:(lia)) as W1.
  rewrite <- EUSP in W1.
  specialize (W1 ST ltac:(lia) ltac:(ul) ltac:(ul) TID HT ATX ATA NH ICB EXL LIBC COV FA GF GCX DSO CPL BI DGC MI0).
  lazymatch type of W1 with evt ctasegs _ ?X =>
    assert (W1' : forall ms, eq X ms -> evt ctasegs _ ms) by (intros ms <-; exact W1) end.
  clear W1.
  apply (cps_realizes ctasegs _ _ _ c (asta_evt RT AF Σ _ fs0 _ _ W1') Hc).
  intros cf1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ cf1 Hc1) as (ms1 & PO1 & Hc1'). unfold exit_A_post in PO1. rewrite <- EUSP in PO1.
  destruct PO1 as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & s0x & jf & m1 & -> & MU1 & WM1 & MI1
                   & FRX & FRF & ST1).
  assert (ART1 : ART RT Σ m1).
  { apply (af_frame RT AF Σ m m1 (usp - 448) ART0); [ul| | exact WM1].
    intros a Ha. apply MU1. cbn [outside].
    repeat (split; [intros Hin; apply Ha; first [left; ul | right; left; apply D_cs.client_static_intro; lia] |]). exact I. }
  assert (AG01 : agree_on (fun x => xe_keep x \/ (GDESC_LO <= x < 0x66e988)) m m1).
  { apply (agree_of_munch _ _ _ _ MU1). intros x Hx. unfold xe_keep, GDESC_LO in Hx. cbn [outside]. ul. }
  destruct (AF_XIT Σ m1 ART1) as (_ & _ & _ & _ & RG & MUX & SHC & AI & CP & THR & RMS & _ & SHW).
  assert (DP : HxaExit.dtor_pre m1).
  { unfold HxaExit.dtor_pre.
    split; [intros a Ha; apply (af_relro RT AF Σ m1 ART1); rewrite wa_unsigned by lia; unfold RELRO_LO, RELRO_HI; lia|].
    split; [apply (gdesc_pristine_agree m m1 GDS); apply (agree_sub _ _ _ _ AG01); intros x Hx; right; unfold GDESC_LO, GDESC_HI in *; lia|].
    split; [exact RMS|].
    split; [apply (rw_cells_agree ctasegs m m1 _ _ FLG); [apply (agree_sub _ _ _ _ AG01); intros xa Hxa; cbn in Hxa; right; unfold GDESC_LO; lia| exact WM1]|].
    split; [exact RG|]. split; [exact MUX|]. split; [exact CP|]. split; [exact SHC|]. split; [exact AI|]. split; [exact THR|].
    pose proof odr_ok as OD. cbn [forallb fst snd] in OD.
    repeat (apply andb_prop in OD; destruct OD as [?OK OD]).
    repeat (apply Forall_cons; [cbn [fst snd]; first [apply seg_stk; assumption | exact SHW]|]). apply Forall_nil. }
  assert (EUD : bv_unsigned (Z_to_bv 64 (usp + -48)) = usp + -48) by (apply unsigned_lit; ul).
  (* [comment removed for export] *)
  pose proof (HxaExit.module_dtor_spec (Z_to_bv 64 0x51fc10) (Z_to_bv 64 (usp + -48)) gp (Z_to_bv 64 tpA) t0' t1' t2'
                (Z_to_bv 64 0x533428) (Z_to_bv 64 0x533428) a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6'
                F fc m1 lo) as W2.
  rewrite EUD in W2.
  specialize (W2 ST1 ltac:(unfold HxaExit.XSH_HI; lia) ltac:(unfold HxaExit.XD_STACK; lia)
                 ltac:(clear - SPA; Z.div_mod_to_equations; lia) MI1 eq_refl DP).
  lazymatch type of W2 with evt ctasegs _ ?X =>
    assert (W2' : forall ms, eq X ms -> evt ctasegs _ ms) by (intros ms <-; exact W2) end.
  clear W2.
  apply (cps_realizes ctasegs _ _ _ cf1 (asta_evt RT AF Σ _ fs0 _ _ W2') Hc1').
  intros cf2 Hc2.
  destruct (ASTA_unpack RT Σ _ _ cf2 Hc2) as (ms2 & PO2 & Hc2').
  destruct PO2 as (u0 & u1 & u2 & b0' & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & -> & MU2 & WM2 & MI2 & ST2).
  rewrite (ret_pc_even 0x51fc10) in Hc2' by lia.
  assert (AG12 : agree_on (fun x => xe_keep x \/ usp + -48 <= x < usp + -16) m1 m2).
  { apply (agree_of_munch _ _ _ _ MU2). intros x Hx. unfold xe_keep in Hx. unfold HxaExit.XD_STACK, HxaExitInit.WX. cbn [outside]. ul. }
  assert (AG02 : agree_on xe_keep m m2).
  { apply (agree_trans _ m m1 m2); [apply (agree_sub _ _ _ _ AG01); intros x Hx; left; exact Hx| apply (agree_sub _ _ _ _ AG12); intros x Hx; left; exact Hx]. }
  assert (WM02 : wmono ctasegs m m2) by exact (wmono_trans ctasegs _ _ _ WM1 WM2).
  Local Ltac tr4 AG WM H := apply (rw_cells_agree ctasegs _ _ _ _ H); [apply (agree_sub _ _ _ _ AG); intros xa Hxa; cbn in Hxa; unfold xe_keep; lia| exact WM].
  assert (FR2 : rw_cells ctasegs m2 (usp + -48) [CB 8 jf; C8 s1; C8 (Z_to_bv 64 code); C8 (Z_to_bv 64 0x51fc94)]).
  { apply (rw_cells_agree ctasegs m1 m2 _ _ FRF); [| exact WM2].
    apply (agree_sub _ _ _ _ AG12). intros xa Hxa. cbn in Hxa. right. lia. }
  apply (exit_rest Σ F0 fs0 gp (Z_to_bv 64 tpA) u0 u1 u2 b0' b1 b2 b3 b4 b5 b6 b7 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 F fc m2
           so code lo usp jf cdt thr sec tm1 g T cf2 Hcode eq_refl Hso HFD SP0R SP0W MI2 FR2 ST2 LOW ltac:(lia) SPT).
  - apply (stdout_file_agree so m m2); [| exact WM02| exact OUT]. apply (agree_sub _ _ _ _ AG02). intros xa Hxa. unfold xe_keep. lia.
  - apply (stderr_wfile0_agree m m2); [| exact WM02| exact ERR]. apply (agree_sub _ _ _ _ AG02). intros xa Hxa. unfold xe_keep. lia.
  - tr4 AG02 WM02 LIBC.
  - tr4 AG02 WM02 OFL.
  - tr4 AG02 WM02 SEU.
  - tr4 AG02 WM02 SOU.
  - destruct SIN as (j0 & j1 & j2 & j3 & j4 & C). exists j0, j1, j2, j3, j4. tr4 AG02 WM02 C.
  - tr4 AG02 WM02 SINU.
  - apply (ro_cells_agree ctasegs m m2 _ _ G1). apply (agree_sub _ _ _ _ AG02). intros xa Hxa. cbn in Hxa. unfold xe_keep. lia.
  - apply (ro_cells_agree ctasegs m m2 _ _ G2). apply (agree_sub _ _ _ _ AG02). intros xa Hxa. cbn in Hxa. unfold xe_keep. lia.
  - exact Hc2'.
  - exact Hk.
Qed.

(* [comment removed for export] *)
Lemma exit_contract_weaken : forall (X X' : mem -> Prop), (forall m, X m -> X' m) ->
  exit_contract RT X' OUT_repA ERR_repA LIBX -> exit_contract RT X OUT_repA ERR_repA LIBX.
Proof.
  intros X X' HX H Σ F0 fs0 ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m so code lo
    Ha0 Hcode Htp Hso HFD OUT ERR XE.
  exact (H Σ F0 fs0 ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m so code lo
           Ha0 Hcode Htp Hso HFD OUT ERR (HX m XE)).
Qed.

Theorem exit_ok0 : exit_contract RT XENVA OUT_repA ERR_repA LIBX.
Proof using AF AF_XIT LIBX_exit. exact (exit_contract_weaken XENVA XENVX XENVA_X exit_ok). Qed.

Theorem exit_ok1 : exit_contract RT (fun m => XENVA1 m /\ incb0 m) OUT_repA ERR_repA LIBX.
Proof using AF AF_XIT LIBX_exit. exact (exit_contract_weaken (fun m => XENVA1 m /\ incb0 m) XENVX XENVA1_X exit_ok). Qed.

End XExit.
