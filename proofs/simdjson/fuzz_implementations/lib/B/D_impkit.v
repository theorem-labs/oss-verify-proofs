(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import PropExec MState Mem Frame Cells Step Arr Exec ImageA RzCPS NodesA FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Spec Require Import Prelim Canon Stdio.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout RT_iface D_iface D_defs D_kit D_auxv D_libiface D_clx X_aexdefs D_aex X_vecxdefs X_xdefs X_xiface Sj_acps Atp_activewA Pj_defsA Imp_hdefs0A Imp_ios_defsA Imp_libifaceA I_iodefs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
#[local] Existing Instance OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A.Shadow.GWf.
Notation wz z := (Z_to_bv 64 z) (only parsing).

Definition impfp0 (m : mem) : Prop :=
  rw_cells bsegs m IMP_VEC_OBJ_A [C8 (wz 0); C8 (wz 0); C8 (wz 0)] /\ rw_cells bsegs m IMP_GUARD_A g00 /\ rw_cells bsegs m IMP_AVL_GUARD_A g00.

Definition libN (m : mem) : Prop :=
  (lib0 m /\ rw_cells bsegs m IMP_AVP_SPAN_A [C8 (wz 0); C8 (wz 0)] /\ rw_cells bsegs m IMP_AVP_GUARD_A g00 /\ rw_cells bsegs m IMP_AVP_ARR_A [C8 (wz 0)])
  /\ LOCBA m /\ locx3 m /\ imp_tplocA m /\ lockwA m.

Lemma imp_libA_None_iff : forall m, imp_libA None m <-> libN m /\ impfp0 m.
Proof.
  intros m. unfold imp_libA, imp_staticsA, libN, impfp0. tauto.
Qed.
Lemma imp_libA_None_of : forall m, libN m -> impfp0 m -> imp_libA None m.
Proof. intros m A B. apply (proj2 (imp_libA_None_iff m)). exact (conj A B). Qed.

Lemma libN_loc : fp_local LIB_FP libN.
Proof.
  intros m m' ((L0 & SP & GU & AR) & LB & LX & TP & LK) AG.
  assert (AGP : forall P : Z -> Prop, (forall x, P x -> in_ranges LIB_FP x) -> agree_on P m m') by (intros P HP a Ha; apply AG; apply HP; exact Ha).
  assert (IN : forall lo hi x, In (lo, hi) LIB_FP -> lo <= x < hi -> in_ranges LIB_FP x) by (intros lo hi x H1 H2; exists lo, hi; split; assumption).
  unfold LIB_FP in IN. unfold IMP_AVP_SPAN_A, IMP_AVP_GUARD_A, IMP_AVP_ARR_A in *.
  split; [split; [| split; [| split]]| split; [| split; [| split]]].
  - apply (lib0_agree m m' L0). apply AGP. intros x [H|[H|[H|H]]].
    + apply (IN 0x6bc120 0x6bc128 x); [cbn; tauto| lia]. + apply (IN 0x6bc140 0x6bc148 x); [cbn; tauto| lia].
    + apply (IN 0x6bc1c0 0x6bc1f0 x); [cbn; tauto| lia]. + apply (IN 0x6bc220 0x6bc228 x); [cbn; tauto| lia].
  - apply (rw_cells_agree_nw bsegs m m' _ _ SP). apply AGP. intros x Hx. cbn [cells_size csize Nat.add g00] in Hx. apply (IN 0x6bc160 0x6bc170 x); [cbn; tauto| lia].
  - apply (rw_cells_agree_nw bsegs m m' _ _ GU). apply AGP. intros x Hx. cbn [cells_size csize Nat.add g00] in Hx. apply (IN 0x6bc180 0x6bc188 x); [cbn; tauto| lia].
  - apply (rw_cells_agree_nw bsegs m m' _ _ AR). apply AGP. intros x Hx. cbn [cells_size csize Nat.add g00] in Hx. apply (IN 0x6bc1a0 0x6bc1a8 x); [cbn; tauto| lia].
  - apply (LOCBA_agree m m' LB). apply AGP. intros x Hx. unfold PJ_LOC_LO_A, PJ_LOC_HI_A in Hx. apply (IN 0x6bcc28 0x6bdad8 x); [cbn; tauto| lia].
  - destruct LX as (X1 & X2 & X3). unfold locx3, LOC_CVC, LOC_CVW in *.
    split; [| split]; (eapply rw_cells_agree_nw; [eassumption|]; apply AGP; intros x Hx; cbn [cells_size csize Nat.add] in Hx; apply (IN 0x6bcc28 0x6bdad8 x); [cbn; tauto| lia]).
  - unfold imp_tplocA, TPV_A in *. apply (rw_cells_agree_nw bsegs m m' _ _ TP). apply AGP. intros x Hx. cbn [cells_size csize Nat.add g00] in Hx. apply (IN 0x6be3b8 0x6be3c0 x); [cbn; tauto| lia].
  - apply (lockwA_agree m m' LK). apply AGP. intros x Hx. unfold PJ_LOCKW_A in Hx. apply (IN 0x6de758 0x6de75c x); [cbn; tauto| lia].
Qed.

Lemma impfp0_loc : fp_local IMP_FP_A impfp0.
Proof.
  intros m m' (V & G & A) AG.
  assert (IN : forall lo hi x, In (lo, hi) IMP_FP_A -> lo <= x < hi -> in_ranges IMP_FP_A x) by (intros lo hi x H1 H2; exists lo, hi; split; assumption).
  unfold impfp0, IMP_FP_A, IMP_VEC_OBJ_A, IMP_GUARD_A, IMP_AVL_GUARD_A, g00 in *.
  split; [| split]; (eapply rw_cells_agree_nw; [eassumption|]; intros a Ha; apply AG; cbn [cells_size csize Nat.add length] in Ha);
    [apply (IN 0x6bc000 (0x6bc000 + 24)); [cbn; tauto| lia]| apply (IN 0x6bc040 (0x6bc040 + 2)); [cbn; tauto| lia]| apply (IN 0x6bc100 (0x6bc100 + 2)); [cbn; tauto| lia]].
Qed.

Definition xcore0 (m : mem) : Prop := XENV_coreA m /\ impfp0 m.
Definition XENV0 (m : mem) : Prop := xcore0 m /\ aexA m.
Definition XCORE_FP0 : list (Z * Z) := XENV_CORE_FPA ++ IMP_FP_A.
Definition XENV_FP0 : list (Z * Z) := XENV_FPA ++ IMP_FP_A.

Lemma xcore0_loc : fp_local XCORE_FP0 xcore0.
Proof.
  intros m m' [C I] AG. split.
  - apply (XENV_coreA_loc m m' C). intros a Ha. apply AG. apply in_ranges_app_l. exact Ha.
  - apply (impfp0_loc m m' I). intros a Ha. apply AG. apply in_ranges_app_r. exact Ha.
Qed.

Lemma aex_imp_sep : forall x, in_ranges AEX_FPA x -> ~ in_ranges IMP_FP_A x.
Proof.
  intros x Hx (lo & hi & Hin & Hlh). apply in_AEX_FPA_iff in Hx. unfold AEX, AEX_A0, TR_LATCH, AEF_INCB in Hx.
  unfold IMP_FP_A, IMP_VEC_OBJ_A, IMP_GUARD_A, IMP_AVL_GUARD_A in Hin. cbn in Hin.
  repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]). destruct Hin.
Qed.

Lemma XENV0_loc : fp_local XENV_FP0 XENV0.
Proof.
  intros m m' [[C I] A] AG. split; [split|].
  - apply (XENV_coreA_loc m m' C). intros a Ha. apply AG. apply in_ranges_app_l. apply in_ranges_app_l. exact Ha.
  - apply (impfp0_loc m m' I). intros a Ha. apply AG. apply in_ranges_app_r. exact Ha.
  - apply (aexA_agree m m'); [| exact A]. intros a Ha. apply AG. apply in_ranges_app_l. apply in_ranges_app_r. exact Ha.
Qed.

Definition XENV_laws0 : xenv_laws XENV0 XENV_FP0.
Proof.
  refine {| xl_loc := XENV0_loc; xl_core := xcore0; xl_core_fp := XCORE_FP0; xl_split := _;
            xl_core_loc := xcore0_loc; xl_core_sep := _; xl_aex_in := _; xl_core_in := _; xl_libc := _; xl_xdata := _ |}.
  - intros m. unfold XENV0. tauto.
  - intros x Hx Hc. apply in_ranges_app_inv in Hc. destruct Hc as [Hc|Hc]; [exact (aex_core_sep x Hx Hc)| exact (aex_imp_sep x Hx Hc)].
  - intros x Hx. apply in_ranges_app_l. apply in_ranges_app_r. exact Hx.
  - intros x Hc. apply in_ranges_app_inv in Hc. destruct Hc as [Hc|Hc]; [apply in_ranges_app_l; apply in_ranges_app_l; exact Hc| apply in_ranges_app_r; exact Hc].
  - intros m [C _]. exact (xl_libc XENV_lawsA m C).
  - intros m [C _]. exact (xl_xdata XENV_lawsA m C).
Defined.

Lemma IMP_FP_A_img : forall x, in_ranges IMP_FP_A x -> client_static x /\ ~ drv_cell x /\ outside IO_FPA x /\ outside LIB_FP x.
Proof.
  intros x (lo & hi & Hin & Hx). unfold IMP_FP_A, IMP_VEC_OBJ_A, IMP_GUARD_A, IMP_AVL_GUARD_A in Hin. cbn in Hin.
  split; [| split; [| split]].
  - apply client_static_intro. repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]). destruct Hin.
  - unfold drv_cell, ERRNO_A, TP_A, SSP_GUARD, TR_INIT, g_read_stage. repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]). destruct Hin.
  - unfold IO_FPA. cbn. repeat (destruct Hin as [E|Hin]; [injection E as <- <-; (split; [lia| split; [lia| split; [lia| exact I]]])|]). destruct Hin.
  - unfold LIB_FP. cbn. repeat (destruct Hin as [E|Hin]; [injection E as <- <-; (repeat (split; [lia|])); try exact I|]). destruct Hin.
Qed.

Lemma XENV_img0A : forall x, in_ranges XENV_FP0 x -> client_static x /\ ~ drv_cell x /\ outside IO_FPA x /\ outside LIB_FP x.
Proof.
  intros x Hx. apply in_ranges_app_inv in Hx. destruct Hx as [Hx|Hx]; [exact (XENV_imgA x Hx)| exact (IMP_FP_A_img x Hx)].
Qed.

Lemma IO_img2A : forall x, in_ranges IO_FPA x -> outside IMP_FP_A x /\ ~ in_ranges AEX_FPA x.
Proof.
  intros x (lo & hi & Hin & Hx). unfold IO_FPA in Hin. cbn in Hin.
  unfold IMP_FP_A, IMP_VEC_OBJ_A, IMP_GUARD_A, IMP_AVL_GUARD_A. cbn [outside]. rewrite in_AEX_FPA_iff. unfold AEX, AEX_A0, TR_LATCH, AEF_INCB.
  repeat (destruct Hin as [E|Hin]; [injection E as <- <-; repeat split; try exact I; lia|]). destruct Hin.
Qed.

Section Exit0.
Variable RT : rt_sig.
Variable XENV : mem -> Prop.
Variable LIB : mem -> Prop.
Variable OUT_rep : stdout_st -> mem -> Prop.
Variable ERR_rep : mem -> Prop.

Definition exit_contract0 : Prop :=
  forall (Σ : rts RT) F0 fs0 (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (so : stdout_st) (code lo : Z),
  a0 = Z_to_bv 64 code -> 0 <= code < 256 -> tp = Z_to_bv 64 0x6be3e8 ->
  (so = stdout_init \/ exists k, (k < 500)%nat /\ so = so_lines k) ->
  fd_lookup F0 (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)) ->
  OUT_rep so m -> ERR_rep m -> XENV m -> LIB m ->
  ART RT Σ m -> mem_inv bsegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + X_DEPTH <= bv_unsigned sp -> io_ssp m ->
  cpsE bsegs (ASTA RT Σ (PMfd F0 fs0) (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9
                                                     s10 s11 t3 t4 t5 t6 F fc e_exit m)))
    (evw 1 (so_buf so)) (EXITc fs0 code).
End Exit0.

Lemma exit0_of_imp : forall RT OUT_rep ERR_rep,
  exit_contract_imp RT XENV_coreA OUT_rep ERR_rep imp_libA -> exit_contract0 RT XENV0 libN OUT_rep ERR_rep.
Proof.
  intros RT OUT_rep ERR_rep EXC Σ F0 fs0 ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m so code lo
         E0 C0 ETP SO FD OUT ERR [[CORE I0] AEX] LIB ART0 MI COK SL SSP.
  apply (EXC Σ F0 fs0 ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m so code lo None E0 C0 ETP SO FD OUT ERR CORE);
    [exact AEX| exact (imp_libA_None_of m LIB I0)| intros A8 E; discriminate E| exact ART0| exact MI| exact COK| exact SL| exact SSP].
Qed.

Lemma LIBX : forall v m, imp_libA v m -> libx v m.
Proof.
  intros v m (ST & LB & LX & TP & LK). split; [exact LX|]. split; [exact TP|].
  destruct v as [A8|]; [| exact I]. cbn in ST. destruct ST as (_ & _ & _ & _ & _ & VEC & _ & _ & _ & A16). unfold IMP_VEC_OBJ_A in VEC. split; [exact VEC| exact A16].
Qed.

Definition aexR (v : option Z) (m : mem) : Prop := match v with None => impfp0 m /\ aex_reg m | Some _ => aex_lib m end.

Lemma aexR_flag0 : forall v m, aexR v m -> rw_cells bsegs m AEF_INCB [C1 (Z_to_bv 8 0)].
Proof. intros [A8|] m H; [exact (proj2 (proj2 (proj2 H)))| exact (proj2 (proj2 (proj2 (proj2 H))))]. Qed.
Lemma aexR_latch1 : forall v m, aexR v m -> rw_cells bsegs m TR_LATCH [C1 (Z_to_bv 8 1)].
Proof. intros [A8|] m H; [exact (proj1 (proj2 (proj2 H)))| exact (proj1 (proj2 (proj2 (proj2 H))))]. Qed.
Lemma aexR_aexvA : forall v m, aexR v m -> aexvA v m.
Proof. intros [A8|] m H; [exact (aex_lib_aex6A m H)| exact (aex_reg_aex4A m (proj2 H))]. Qed.
Lemma aexR_libA : forall v m, aexR v m -> (match v with None => libN m | Some _ => imp_libA v m end) -> imp_libA v m.
Proof. intros [A8|] m H L; [exact L| exact (imp_libA_None_of m L (proj1 H))]. Qed.

Section CLXV.
Variable OUT_rep : stdout_st -> mem -> Prop.
Variable ERR_rep : mem -> Prop.
Variable IO_FP : list (Z * Z).
Hypothesis OUT_loc : forall so, fp_local IO_FP (OUT_rep so).
Hypothesis ERR_loc : fp_local IO_FP ERR_rep.
Hypothesis IO_img : forall x, in_ranges IO_FP x -> client_static x /\ ~ drv_cell x /\ outside LIB_FP x.
Hypothesis IO_img2 : forall x, in_ranges IO_FP x -> outside IMP_FP_A x /\ ~ in_ranges AEX_FPA x.
Hypothesis XENV_img : forall x, in_ranges XENV_FP0 x -> client_static x /\ ~ drv_cell x /\ outside IO_FP x /\ outside LIB_FP x.

Definition CLXv (v : option Z) (so : stdout_st) (m : mem) : Prop :=
  OUT_rep so m /\ ERR_rep m /\ XENV_coreA m /\ aexR v m /\ imp_libA v m
  /\ (exists g, ro_cells bsegs m SSP_GUARD [C8 g]) /\ (exists e, rw_cells bsegs m ERRNO_A [C4 e]) /\ stk bsegs m g_read_stage (g_read_stage + 65536).

Lemma CLXv_of_reg : forall so m, CLX OUT_rep ERR_rep XENV0 libN so m -> aex_reg m -> CLXv None so m.
Proof.
  intros so m (O & E & [[C I] _] & L & SG & ER & RS) REG.
  split; [exact O|]. split; [exact E|]. split; [exact C|]. split; [exact (conj I REG)|]. split; [exact (imp_libA_None_of m L I)|].
  split; [exact SG|]. split; [exact ER| exact RS].
Qed.

Definition CLXv_FP (v : option Z) (x : Z) : Prop :=
  in_ranges IO_FP x \/ in_ranges XENV_CORE_FPA x \/ in_ranges AEX_FPA x \/ in_ranges IMP_FP_A x \/ imp_lib_rng v x \/ drv_cell x.

Lemma CLXv_FP_cases : forall v x, CLXv_FP v x -> client_static x \/ (exists A8, v = Some A8 /\ A8 <= x < A8 + 8).
Proof using IO_img XENV_img.
  intros v x [H|[H|[H|[H|[H|H]]]]].
  - left. exact (proj1 (IO_img x H)).
  - left. apply (proj1 (XENV_img x ltac:(apply in_ranges_app_l; apply in_ranges_app_l; exact H))).
  - left. apply (proj1 (XENV_img x ltac:(apply in_ranges_app_l; apply in_ranges_app_r; exact H))).
  - left. exact (proj1 (IMP_FP_A_img x H)).
  - destruct (imp_lib_rng_cases v x H) as [[CS _]|R]; [left; exact CS| right; exact R].
  - left. exact (drv_cell_static x H).
Qed.

Lemma CLXv_agree_nw : forall v so m m', CLXv v so m -> agree_on (CLXv_FP v) m m' -> CLXv v so m'.
Proof using OUT_loc ERR_loc.
  intros v so m m' (O & E & C & AX & L & (g & SG) & (e & ER) & RS) AG.
  split; [apply (OUT_loc so m m' O); apply (agree_ranges_sub _ _ _ _ AG); intros x Hx; left; exact Hx|].
  split; [apply (ERR_loc m m' E); apply (agree_ranges_sub _ _ _ _ AG); intros x Hx; left; exact Hx|].
  split; [apply (XENV_coreA_loc m m' C); apply (agree_ranges_sub _ _ _ _ AG); intros x Hx; right; left; exact Hx|].
  split.
  { destruct v as [A8|]; cbn in AX |- *.
    - apply (aex_lib_agree m m'); [| exact AX]. apply (agree_ranges_sub _ _ _ _ AG). intros x Hx. right; right; left; exact Hx.
    - destruct AX as [I R]. split; [apply (impfp0_loc m m' I); apply (agree_ranges_sub _ _ _ _ AG); intros x Hx; right; right; right; left; exact Hx|].
      apply (aex_reg_agree m m'); [| exact R]. apply (agree_ranges_sub _ _ _ _ AG). intros x Hx. right; right; left; exact Hx. }
  split; [apply (imp_libA_agree v m m' L); eapply agree_sub; [exact AG|]; intros x Hx; right; right; right; right; left; exact Hx|].
  assert (AGD : forall lo n, (forall x, lo <= x < lo + n -> drv_cell x) -> agree_on (fun x => lo <= x < lo + n) m m').
  { intros lo n Hd. eapply agree_sub; [exact AG|]. intros x Hx. do 5 right. exact (Hd x Hx). }
  unfold drv_cell in AGD.
  split; [exists g; apply (ro_cells_agree bsegs m m' _ _ SG); apply AGD; cbn; lia|].
  split; [exists e; apply (rw_cells_agree_nw bsegs m m' _ _ ER); apply AGD; cbn; lia|].
  apply (stk_agree_nw bsegs m m' _ _ RS); eapply agree_sub; [apply (AGD g_read_stage 65536); lia| cbv beta; lia].
Qed.

Lemma CLXv_pres_nw : forall v so m m' live frames sp, CLXv v so m -> rt_pres live frames sp m m' ->
  (forall A8, v = Some A8 -> In (A8, 8) live) -> CLXv v so m'.
Proof using OUT_loc ERR_loc IO_img XENV_img.
  intros v so m m' live frames sp H PR HIN. apply (CLXv_agree_nw v so m m' H).
  apply (agree_of_pres _ _ _ _ _ _ PR). intros x Hx. destruct (CLXv_FP_cases v x Hx) as [CS|(A8 & -> & R)]; [right; left; exact CS|].
  right; right; left. exists A8, 8. split; [exact (HIN A8 eq_refl)| lia].
Qed.

Lemma CLXv_munch_stack : forall v so m m' W lo hi, CLXv v so m -> munch W m m' ->
  (forall x, in_ranges W x -> lo <= x < hi) -> SEGTOP_A <= lo -> (forall A8, v = Some A8 -> A8 + 8 <= lo \/ hi <= A8) -> CLXv v so m'.
Proof using OUT_loc ERR_loc IO_img XENV_img.
  intros v so m m' W lo hi H MU HW HLO HV. apply (CLXv_agree_nw v so m m' H). apply (agree_of_munch _ _ _ _ MU). intros x Hx.
  apply outside_of_not_in_ranges'. intros Hin. pose proof (HW x Hin) as R.
  destruct (CLXv_FP_cases v x Hx) as [CS|(A8 & E & RA)]; [pose proof (client_static_range x CS); lia| pose proof (HV A8 E); lia].
Qed.

Lemma CLXv_io : forall v so so' m m' live frames sp, CLXv v so m -> rt_pres_fp live frames sp IO_FP m m' ->
  (forall A8, v = Some A8 -> In (A8, 8) live) -> (forall A8, v = Some A8 -> A8 + 8 <= 0x10000 \/ SEGTOP_A <= A8) ->
  OUT_rep so' m' -> ERR_rep m' -> CLXv v so' m'.
Proof using OUT_loc ERR_loc IO_img IO_img2 XENV_img.
  intros v so so' m m' live frames sp (O & E & C & AX & L & (g & SG) & (e & ER) & RS) PR HIN HA8 O' E'.
  assert (AG : agree_on (fun x => in_ranges XENV_CORE_FPA x \/ in_ranges AEX_FPA x \/ in_ranges IMP_FP_A x \/ imp_lib_rng v x \/ drv_cell x) m m').
  { apply (agree_of_pres_fp _ _ _ _ _ _ _ PR). intros x Hx.
    assert (CL : client_static x \/ (exists A8, v = Some A8 /\ A8 <= x < A8 + 8)) by (apply (CLXv_FP_cases v x); right; exact Hx).
    split.
    - destruct CL as [CS|(A8 & E8 & R)]; [right; left; exact CS| right; right; left; exists A8, 8; split; [exact (HIN A8 E8)| lia]].
    - apply outside_of_not_in_ranges'. intros Hio. destruct Hx as [Hx|[Hx|[Hx|[Hx|Hx]]]].
      + exact (not_in_ranges_of_outside _ _ (proj1 (proj2 (proj2 (XENV_img x ltac:(apply in_ranges_app_l; apply in_ranges_app_l; exact Hx))))) Hio).
      + exact (proj2 (IO_img2 x Hio) Hx).
      + exact (not_in_ranges_of_outside _ _ (proj1 (IO_img2 x Hio)) Hx).
      + destruct (imp_lib_rng_fp v x Hx) as [Hf|(A8 & E8 & R)].
        * apply in_ranges_app_inv in Hf. destruct Hf as [Hf|Hf]; [exact (not_in_ranges_of_outside _ _ (proj2 (proj2 (IO_img x Hio))) Hf)| exact (not_in_ranges_of_outside _ _ (proj1 (IO_img2 x Hio)) Hf)].
        * pose proof (client_static_range x (proj1 (IO_img x Hio))) as CS. pose proof (HA8 A8 E8). lia.
      + exact (proj1 (proj2 (IO_img x Hio)) Hx). }
  split; [exact O'|]. split; [exact E'|].
  split; [apply (XENV_coreA_loc m m' C); apply (agree_ranges_sub _ _ _ _ AG); intros x Hx; left; exact Hx|].
  split.
  { destruct v as [A8|]; cbn in AX |- *.
    - apply (aex_lib_agree m m'); [| exact AX]. apply (agree_ranges_sub _ _ _ _ AG). intros x Hx. right; left; exact Hx.
    - destruct AX as [I R]. split; [apply (impfp0_loc m m' I); apply (agree_ranges_sub _ _ _ _ AG); intros x Hx; right; right; left; exact Hx|].
      apply (aex_reg_agree m m'); [| exact R]. apply (agree_ranges_sub _ _ _ _ AG). intros x Hx. right; left; exact Hx. }
  split; [apply (imp_libA_agree v m m' L); eapply agree_sub; [exact AG|]; intros x Hx; right; right; right; left; exact Hx|].
  assert (AGD : forall lo n, (forall x, lo <= x < lo + n -> drv_cell x) -> agree_on (fun x => lo <= x < lo + n) m m').
  { intros lo n Hd. eapply agree_sub; [exact AG|]. intros x Hx. do 4 right. exact (Hd x Hx). }
  unfold drv_cell in AGD.
  split; [exists g; apply (ro_cells_agree bsegs m m' _ _ SG); apply AGD; cbn; lia|].
  split; [exists e; apply (rw_cells_agree_nw bsegs m m' _ _ ER); apply AGD; cbn; lia|].
  apply (stk_agree_nw bsegs m m' _ _ RS); eapply agree_sub; [apply (AGD g_read_stage 65536); lia| cbv beta; lia].
Qed.

Lemma CLXv_io_ssp : forall v so m, CLXv v so m -> exists g, ro_cells bsegs m SSP_GUARD [C8 g].
Proof. intros v so m (_ & _ & _ & _ & _ & SG & _). exact SG. Qed.
End CLXV.

Lemma aex6A_agree : forall m m', aex6A m -> agree_on (fun x => AEX <= x < AEX + 80 \/ AEX_A0 <= x < AEX_A0 + 48) m m' -> aex6A m'.
Proof.
  intros m m' [(p1 & p2 & T) A] AG. split.
  - exists p1, p2. apply (rw_cells_agree_nw bsegs m m' _ _ T). intros a Ha. apply AG. cbn in Ha. unfold AEX in *. left. lia.
  - apply (rw_cells_agree_nw bsegs m m' _ _ A). intros a Ha. apply AG. cbn in Ha. unfold AEX_A0 in *. right. lia.
Qed.

Lemma core_imp_sep : forall x, in_ranges IMP_FP_A x -> ~ in_ranges XENV_CORE_FPA x.
Proof.
  intros x (lo & hi & Hin & Hlh) (lo' & hi' & Hin' & Hlh'). unfold IMP_FP_A, IMP_VEC_OBJ_A, IMP_GUARD_A, IMP_AVL_GUARD_A in Hin. unfold XENV_CORE_FPA in Hin'.
  cbn in Hin, Hin'. repeat (destruct Hin as [E|Hin]; [injection E as <- <-| ]);
    (destruct Hin || (repeat (destruct Hin' as [E'|Hin']; [injection E' as <- <-; lia|]); destruct Hin')).
Qed.

Lemma in_IMP_XFP_A : forall x, in_ranges IMP_XFP_A x -> in_ranges LIB_FP x \/ in_ranges IMP_FP_A x \/ (AEX <= x < AEX + 80 \/ AEX_A0 <= x < AEX_A0 + 48).
Proof.
  intros x Hx. unfold IMP_XFP_A in Hx. apply in_ranges_app_inv in Hx. destruct Hx as [Hx|Hx]; [left; exact Hx|].
  apply in_ranges_app_inv in Hx. destruct Hx as [Hx|Hx]; [right; left; exact Hx|].
  right; right. destruct Hx as (lo & hi & Hin & Hlh). unfold IMP_AEX_W in Hin. cbn in Hin.
  destruct Hin as [E|[E|[]]]; injection E as <- <-; lia.
Qed.
Lemma IMP_XFP_A_static : forall x, in_ranges IMP_XFP_A x -> client_static x.
Proof.
  intros x Hx. destruct (in_IMP_XFP_A x Hx) as [H|[H|H]]; [exact (proj1 (LIB_img x H))| exact (proj1 (IMP_FP_A_img x H))|].
  apply client_static_intro. unfold AEX, AEX_A0 in H. lia.
Qed.
Lemma IMP_XFP_A_aex : forall x, in_ranges IMP_XFP_A x -> AEX <= x < AEX + 80 \/ AEX_A0 <= x < AEX_A0 + 48 -> in_ranges AEX_FPA x.
Proof. intros x _ H. rewrite in_AEX_FPA_iff. lia. Qed.

Lemma IMP_XFP_A_misc : forall x, in_ranges IMP_XFP_A x -> x <> TR_LATCH /\ x <> AEF_INCB /\ ~ drv_cell x /\ ~ in_ranges XENV_CORE_FPA x.
Proof.
  intros x Hx. destruct (in_IMP_XFP_A x Hx) as [H|[H|H]].
  - pose proof (LIB_img x H) as [_ ND]. split; [| split; [| split; [exact ND|]]].
    + intros ->. destruct H as (lo & hi & Hin & Hlh). unfold LIB_FP in Hin. unfold TR_LATCH in Hlh. cbn in Hin. repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]). destruct Hin.
    + intros ->. destruct H as (lo & hi & Hin & Hlh). unfold LIB_FP in Hin. unfold AEF_INCB in Hlh. cbn in Hin. repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]). destruct Hin.
    + intros Hc. destruct H as (lo & hi & Hin & Hlh). destruct Hc as (lo' & hi' & Hin' & Hlh'). unfold LIB_FP in Hin. unfold XENV_CORE_FPA in Hin'. cbn in Hin, Hin'.
      repeat (destruct Hin as [E|Hin]; [injection E as <- <-| ]);
        (destruct Hin || (repeat (destruct Hin' as [E'|Hin']; [injection E' as <- <-; lia|]); destruct Hin')).
  - pose proof (IMP_FP_A_img x H) as (_ & ND & _). split; [| split; [| split; [exact ND| exact (core_imp_sep x H)]]];
      intros ->; destruct H as (lo & hi & Hin & Hlh); unfold IMP_FP_A, IMP_VEC_OBJ_A, IMP_GUARD_A, IMP_AVL_GUARD_A in Hin; unfold TR_LATCH, AEF_INCB in Hlh; cbn in Hin;
      repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]); destruct Hin.
  - assert (HA : in_ranges AEX_FPA x) by (rewrite in_AEX_FPA_iff; lia).
    split; [unfold AEX, AEX_A0, TR_LATCH in *; lia|]. split; [unfold AEX, AEX_A0, AEF_INCB in *; lia|].
    split; [exact (proj1 (proj2 (XENV_imgA x ltac:(unfold XENV_FPA; apply in_ranges_app_r; exact HA))))| exact (aex_core_sep x HA)].
Qed.

Lemma INCB_facts : client_static AEF_INCB /\ ~ drv_cell AEF_INCB /\ ~ in_ranges XENV_CORE_FPA AEF_INCB /\ ~ in_ranges IMP_FP_A AEF_INCB /\ ~ imp_lib_rng None AEF_INCB.
Proof.
  assert (HA : in_ranges AEX_FPA AEF_INCB) by (rewrite in_AEX_FPA_iff; right; right; right; reflexivity).
  pose proof (XENV_imgA AEF_INCB ltac:(unfold XENV_FPA; apply in_ranges_app_r; exact HA)) as (CS & ND & _).
  split; [exact CS|]. split; [exact ND|]. split; [exact (aex_core_sep _ HA)|]. split; [exact (aex_imp_sep _ HA)|].
  unfold imp_lib_rng, AEF_INCB, PJ_LOC_LO_A, PJ_LOCKW_A, TPV_A. lia.
Qed.

Lemma CLX_repack : forall (OUT_rep : stdout_st -> mem -> Prop) (ERR_rep : mem -> Prop) so m,
  CLX OUT_rep ERR_rep XENVA (imp_libA None) so m -> CLX OUT_rep ERR_rep XENV0 libN so m.
Proof.
  intros OUT_rep ERR_rep so m (O & E & [C A] & L & SG & ER & RS). apply (proj1 (imp_libA_None_iff m)) in L. destruct L as [LN I0].
  split; [exact O|]. split; [exact E|]. split; [exact (conj (conj C I0) A)|]. split; [exact LN|]. split; [exact SG|]. split; [exact ER| exact RS].
Qed.
Lemma START_repack : forall RT (OUT_rep : stdout_st -> mem -> Prop) (ERR_rep : mem -> Prop) argvb fs c,
  START RT OUT_rep ERR_rep XENVA (imp_libA None) argvb fs c -> START RT OUT_rep ERR_rep XENV0 libN argvb fs c.
Proof.
  intros RT OUT_rep ERR_rep argvb fs c H. unfold START in *.
  destruct H as (Σ & usp & ap & gp & t0 & t1 & t2 & s0 & s1 & a2 & a3 & a4 & a5 & a6 & a7 & s2 & s3 & s4 & s5 & s6 & s7 & s8 & s9 & s10 & s11 & t3 & t4 & t5 & t6 & F & fc & m
                 & FRM & HA & ART0 & MI & CLX0 & REST).
  exists Σ, usp, ap, gp, t0, t1, t2, s0, s1, a2, a3, a4, a5, a6, a7, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, t3, t4, t5, t6, F, fc, m.
  split; [exact FRM|]. split; [exact HA|]. split; [exact ART0|]. split; [exact MI|]. split; [exact (CLX_repack OUT_rep ERR_rep _ m CLX0)| exact REST].
Qed.
