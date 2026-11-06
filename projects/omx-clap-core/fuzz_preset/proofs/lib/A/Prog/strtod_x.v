From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0o YK14 YK15 YK18 YK1b YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YO0d YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require MState Mem Cells Step Exec Frame Regs6ss RegisterBridge.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib Require MemNorm AsanLift.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.P Require FmtFp_facts3.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import strtod_c strtod.
Import ListNotations.
Open Scope Z_scope.

(* measured: in the asan images frexpl recurses through __interceptor_trampoline_frexpl (printf path only); strtod's 30-function chain calls the same-named targets as the ubsan image *)

Lemma ret_pc_v_jalr : forall ra : word, MState.ret_pc ra = v_jalr ra 0.
Proof.
  intros ra. unfold MState.ret_pc.
  replace ra with (ra + sext 64 (Z_to_bv 12 0))%bv at 1.
  - rewrite b_jalr. reflexivity.
  - apply bv_eq. rewrite bv_add_unsigned. unfold sext. rewrite bv_sign_extend_unsigned. cbn.
    rewrite Z.add_0_r. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

Lemma getr_reg_get : forall (R : bvmap 5 word) (k : reg), is_x0 k = false -> getr R k = reg_get R k.
Proof. intros R k Hk. unfold getr. rewrite bv_eqb0_is_x0, Hk. reflexivity. Qed.

Lemma wx_rsegs : wx_segs_nowrap rsegs.
Proof. apply wx_segs_nowrap_of_b. vm_compute. reflexivity. Qed.

Lemma wview_agree : forall (m m' : word -> option byte) x, m' x = m x -> wview rsegs m' x = wview rsegs m x.
Proof. intros m m' x H. unfold wview. rewrite H. reflexivity. Qed.

Lemma mrd_agree : forall (m m' : word -> option byte) x, m' x = m x ->
  lib.Lib.Mem.mrd rsegs m' x = lib.Lib.Mem.mrd rsegs m x.
Proof. intros m m' x H. unfold lib.Lib.Mem.mrd. rewrite H. reflexivity. Qed.

Lemma bytes_at_agree : forall (m m' : word -> option byte) A bs,
  lib.Lib.Mem.bytes_at rsegs m A bs ->
  (forall x, A <= x < A + Z.of_nat (length bs) -> m' (Z_to_bv 64 x) = m (Z_to_bv 64 x)) ->
  lib.Lib.Mem.bytes_at rsegs m' A bs.
Proof.
  intros m m' A bs (Ha & Hl & Hr) Hag. split; [exact Ha|]. split; [exact Hl|].
  intros i Hi. unfold lib.Lib.Mem.wa in *. rewrite (mrd_agree m m') by (apply Hag; lia). exact (Hr i Hi).
Qed.

Lemma wr_at_agree : forall (m m' : word -> option byte) A n,
  lib.Lib.Mem.wr_at rsegs m A n ->
  (forall x, A <= x < A + n -> m' (Z_to_bv 64 x) = m (Z_to_bv 64 x)) ->
  lib.Lib.Mem.wr_at rsegs m' A n.
Proof.
  intros m m' A n (Ha & Hl & Hw) Hag. split; [exact Ha|]. split; [exact Hl|].
  intros i Hi. unfold lib.Lib.Mem.wa in *. rewrite (wview_agree m m') by (apply Hag; lia). exact (Hw i Hi).
Qed.

Lemma rw_cells_agree : forall (m m' : word -> option byte) A cs,
  lib.Lib.Step.rw_cells rsegs m A cs ->
  (forall x, A <= x < A + Z.of_nat (lib.Lib.Cells.cells_size cs) -> m' (Z_to_bv 64 x) = m (Z_to_bv 64 x)) ->
  lib.Lib.Step.rw_cells rsegs m' A cs.
Proof.
  intros m m' A cs [[Hwf Hb] Hw] Hag. split; [split; [exact Hwf|]|].
  - apply (bytes_at_agree m); [exact Hb|]. rewrite lib.Lib.Cells.cells_bytes_length by exact Hwf. exact Hag.
  - exact (wr_at_agree m m' A _ Hw Hag).
Qed.

Lemma stk_agree : forall (m m' : word -> option byte) lo hi,
  lib.Lib.Frame.stk rsegs m lo hi ->
  (forall x, lo <= x < hi -> m' (Z_to_bv 64 x) = m (Z_to_bv 64 x)) ->
  lib.Lib.Frame.stk rsegs m' lo hi.
Proof.
  intros m m' lo hi (H1 & H2 & H) Hag. split; [exact H1|]. split; [exact H2|].
  intros a Ha. unfold lib.Lib.Mem.wa in *.
  rewrite (wview_agree m m'), (mrd_agree m m') by (apply Hag; exact Ha). exact (H a Ha).
Qed.

(* strtod_scratch covers [sp-STRTOD_K, sp), the end-pointer cell [e, e+8) and the image's own errno cell (STRTOD_ERRNO of this image's strtod_c) *)
Definition strtod_scratch (regs : bvmap 5 word) (e a : Z) : Prop :=
  (YO0d.spZ regs - STRTOD_K <= a < YO0d.spZ regs) \/ (e <= a < e + 8) \/ (STRTOD_ERRNO <= a < STRTOD_ERRNO + 4).

Definition strtod_vis (regs : bvmap 5 word) (s e : Z) (txt : list Z) (a : Z) : Prop :=
  (s <= a < s + Z.of_nat (length txt) + 1) \/ strtod_scratch regs e a \/
  (STRTOD_GOT_GUARD <= a < STRTOD_GOT_GUARD + 8) \/ (STRTOD_GUARD <= a < STRTOD_GUARD + 8).

Section strtod_x.
Context {fx : YK11.FPState}.
(* allocator invariant: Section Variable until the ARcf names exist (h-mani-a8) *)
Variable ainv : (word -> option byte) -> Model -> Prop.
Variable aown : Z -> Prop.
Hypothesis ainv_frame : forall mem md mem' md',
  ainv mem md ->
  (forall a, 0 <= a < 2 ^ 64 -> aown a -> mbyte rsegs mem' a = mbyte rsegs mem a) ->
  (forall a, mbyte rsegs mem a <> None -> mbyte rsegs mem' a <> None) ->
  (forall a, YO0d.present mem a -> YO0d.present mem' a) ->
  same_but_materialized md md' ->
  ainv mem' md'.

Definition strtod_post_x (regs : bvmap 5 word) (s e : Z) (txt : list Z) (mem : word -> option byte) (md : Model)
    (fx' : FPState) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) : Prop :=
  exists (bits c : Z) (ev' : word),
    ainv mem' md' /\ same_but_materialized md md' /\
    strtod_model txt = Some (bits, c) /\ 0 <= c <= Z.of_nat (length txt) /\
    reg_get (@fp_regs fx') 10 = Z_to_bv 64 bits /\
    (forall k : bv 5, bv_unsigned k <> 10 -> bv_unsigned k <> 14 -> bv_unsigned k <> 15 ->
       reg_get (@fp_regs fx') k = reg_get (@fp_regs fx) k) /\
    YO0d.regs_preserved regs regs' /\ getr regs' 1 = getr regs 1 /\
    lib.Lib.Step.rw_cells rsegs mem' e [lib.Lib.Cells.C8 (Z_to_bv 64 (s + c))] /\
    lib.Lib.Step.rw_cells rsegs mem' STRTOD_ERRNO [lib.Lib.Cells.C4 ev'] /\
    (forall a, 0 <= a < 2 ^ 64 -> ~ strtod_scratch regs e a ->
       mbyte rsegs mem' a = mbyte rsegs mem a /\ (writable_at rsegs mem a <-> writable_at rsegs mem' a)) /\
    (forall a, YO0d.present mem a -> YO0d.present mem' a) /\
    (forall a, writable_at rsegs mem a -> writable_at rsegs mem' a) /\
    lib.Lib.Mem.mem_inv rsegs mem' /\ MemNorm.task_mem rsegs mem' /\
    lib.Lib.Frame.stk rsegs mem' (YO0d.spZ regs - STRTOD_K) (YO0d.spZ regs).

Definition strtod_contract_x : Prop :=
  forall (W : world rsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
         (s e : Z) (txt : list Z) (ejunk canary ev : word),
    getr regs 10 = Z_to_bv 64 s -> getr regs 11 = Z_to_bv 64 e -> getr regs 4 = Z_to_bv 64 STRTOD_TP ->
    lib.Lib.Mem.bytes_at rsegs mem s (map (Z_to_bv 8) (txt ++ [0])) ->
    Forall (fun c => FmtFp_facts3.is_numch c = true) txt -> Z.of_nat (length txt) < 2^30 ->
    lib.Lib.Step.rw_cells rsegs mem e [lib.Lib.Cells.C8 ejunk] ->
    lib.Lib.Frame.stk rsegs mem (YO0d.spZ regs - STRTOD_K) (YO0d.spZ regs) ->
    STRTOD_GLOBALS_TOP <= YO0d.spZ regs - STRTOD_K -> YO0d.spZ regs < 2^62 ->
    4096 <= s -> s + Z.of_nat (length txt) + 1 <= 2^62 ->
    ((s + Z.of_nat (length txt) + 1 <= STRTOD_IMG_LO \/ STRTOD_GLOBALS_TOP <= s)
       /\ s + Z.of_nat (length txt) + 1 <= YO0d.spZ regs - STRTOD_K
     \/ YO0d.spZ regs <= s) ->
    (STRTOD_GLOBALS_TOP <= e /\ e + 8 <= YO0d.spZ regs - STRTOD_K \/ YO0d.spZ regs <= e) -> e + 8 <= 2^62 ->
    (e + 8 <= s \/ s + Z.of_nat (length txt) + 1 <= e) ->
    lib.Lib.Step.rw_cells rsegs mem STRTOD_GOT_GUARD [lib.Lib.Cells.C8 (Z_to_bv 64 STRTOD_GUARD)] ->
    lib.Lib.Step.rw_cells rsegs mem STRTOD_GUARD [lib.Lib.Cells.C8 canary] ->
    lib.Lib.Step.rw_cells rsegs mem STRTOD_ERRNO [lib.Lib.Cells.C4 ev] ->
    lib.Lib.Mem.mem_inv rsegs mem -> MemNorm.task_mem rsegs mem -> frm_zero (@fp_csr fx) ->
    (forall a, strtod_vis regs s e txt a -> w_H W (Z_to_bv 64 a) = false) ->
    ainv mem md -> (forall a, strtod_scratch regs e a -> ~ aown a) ->
    SRr rsegs W (mkCfg (@mkst fx regs (Z_to_bv 64 STRTOD) mem (seg_rom rsegs)) md)
      (fun W' c' => W' = W /\
         exists (fx' : FPState) regs' mem' md',
           c' = mkCfg (@mkst fx' regs' (v_jalr (getr regs 1) 0) mem' (seg_rom rsegs)) md' /\
           frm_zero (@fp_csr fx') /\
           strtod_post_x regs s e txt mem md fx' regs' mem' md').

Theorem strtod_x_holds : strtod_contract_x.
Proof.
  unfold strtod_contract_x.
  intros W regs mem md s e txt ejunk canary ev Ha0 Ha1 Htp BY NUM LEN SLOT ST GT SPH S4 SE HT HE SE8 SEP GG QQ ERR
    MI TM FRM VIS AI NOWN.
  set (mr := mrestrict (w_H W) mem).
  assert (AG : forall a, strtod_vis regs s e txt a -> mr (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
  { intros a Ha. unfold mr, mrestrict. rewrite (VIS a Ha). reflexivity. }
  assert (BYr : lib.Lib.Mem.bytes_at rsegs mr s (map (Z_to_bv 8) (txt ++ [0]))).
  { apply (bytes_at_agree mem); [exact BY|]. intros x Hx. apply AG. left.
    rewrite length_map, length_app in Hx. cbn [length] in Hx. lia. }
  assert (SLOTr : lib.Lib.Step.rw_cells rsegs mr e [lib.Lib.Cells.C8 ejunk]).
  { apply (rw_cells_agree mem); [exact SLOT|]. intros x Hx. apply AG. right. left. right. left. cbn in Hx. lia. }
  assert (STr : lib.Lib.Frame.stk rsegs mr (YO0d.spZ regs - STRTOD_K) (YO0d.spZ regs)).
  { apply (stk_agree mem); [exact ST|]. intros x Hx. apply AG. right. left. left. exact Hx. }
  assert (GGr : lib.Lib.Step.rw_cells rsegs mr STRTOD_GOT_GUARD [lib.Lib.Cells.C8 (Z_to_bv 64 STRTOD_GUARD)]).
  { apply (rw_cells_agree mem); [exact GG|]. intros x Hx. apply AG. right. right. left. cbn in Hx. lia. }
  assert (QQr : lib.Lib.Step.rw_cells rsegs mr STRTOD_GUARD [lib.Lib.Cells.C8 canary]).
  { apply (rw_cells_agree mem); [exact QQ|]. intros x Hx. apply AG. right. right. right. cbn in Hx. lia. }
  assert (ERRr : lib.Lib.Step.rw_cells rsegs mr STRTOD_ERRNO [lib.Lib.Cells.C4 ev]).
  { apply (rw_cells_agree mem); [exact ERR|]. intros x Hx. apply AG. right. left. right. right. cbn in Hx. lia. }
  assert (MIr : lib.Lib.Mem.mem_inv rsegs mr).
  { intros x b Hb. unfold mr, mrestrict in Hb. destruct (w_H W x); [discriminate | exact (MI x b Hb)]. }
  assert (TMr : MemNorm.task_mem rsegs mr).
  { intros x b Hb. unfold mr, mrestrict in Hb. destruct (w_H W x); [discriminate | exact (TM x b Hb)]. }
  pose proof (strtod_holds (reg_get regs 1) (reg_get regs 2) (reg_get regs 3) (reg_get regs 4) (reg_get regs 5)
    (reg_get regs 6) (reg_get regs 7) (reg_get regs 8) (reg_get regs 9) (reg_get regs 10) (reg_get regs 11)
    (reg_get regs 12) (reg_get regs 13) (reg_get regs 14) (reg_get regs 15) (reg_get regs 16) (reg_get regs 17)
    (reg_get regs 18) (reg_get regs 19) (reg_get regs 20) (reg_get regs 21) (reg_get regs 22) (reg_get regs 23)
    (reg_get regs 24) (reg_get regs 25) (reg_get regs 26) (reg_get regs 27) (reg_get regs 28) (reg_get regs 29)
    (reg_get regs 30) (reg_get regs 31) fp_regs fp_csr mr s e txt ejunk canary ev
    Ha0 Ha1 Htp BYr NUM LEN SLOTr STr GT SPH S4 SE HT HE SE8 SEP GGr QQr ERRr MIr TMr FRM) as EV.
  destruct EV as (fin & RUN & POST).
  assert (EV : lib.Lib.Exec.evt rsegs
            (fun ms' => strtod_post (reg_get regs 1) (reg_get regs 2) (reg_get regs 3) (reg_get regs 4)
               (reg_get regs 8) (reg_get regs 9) (reg_get regs 18) (reg_get regs 19) (reg_get regs 20)
               (reg_get regs 21) (reg_get regs 22) (reg_get regs 23) (reg_get regs 24) (reg_get regs 25)
               (reg_get regs 26) (reg_get regs 27) fp_regs s e txt mr ms' /\ mem_grows mr (ms_mem ms'))
            (RegisterBridge.canonical_register_state
               (restrict (w_H W) (mkst regs (Z_to_bv 64 STRTOD) mem (seg_rom rsegs))))).
  { exists fin. split; [exact RUN|]. split; [exact POST|].
    exact (YI04.msteps_mem_grows rsegs _ fin (AsanLift.exec_msteps rsegs _ fin RUN)). }
  clear fin RUN POST.
  destruct (RegisterBridge.canonical_contract_transport rsegs _ _ EV) as (fin & RUN & can & (P & GROW) & EQV).
  apply (SRr_msteps rsegs wx_rsegs W _ fin md _ (AsanLift.exec_msteps rsegs _ fin RUN)).
  intros md' SBM _. apply SRr_ret. split; [reflexivity|].
  destruct P as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6'
                 & F' & fc' & m' & ev' & c & bits & Hcan & SC & Hc & PEC & FA0 & FOK & FRM' & ERR' & MU & WM
                 & MI' & TM' & ST').
  subst can. cbn [ms_mem] in GROW.
  destruct EQV as (XR & EF & EPC & ESV & ERV & EFC & EM & ERO).
  destruct fin as [R' F2 pc2 sv2 rv2 fc2 m2 ro2]. cbn in XR, EF, EPC, ESV, ERV, EFC, EM, ERO.
  subst F2 pc2 sv2 rv2 fc2 m2 ro2.
  set (M' := munrestrict (w_H W) mem m').
  assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ strtod_scratch regs e a -> M' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
  { intros a Ha NS. unfold M', munrestrict. destruct (w_H W (Z_to_bv 64 a)) eqn:Hh; [reflexivity|].
    rewrite MU.
    - unfold mr, mrestrict. rewrite Hh. reflexivity.
    - rewrite Z_to_bv_unsigned, bv_wrap_small by (unfold bv_modulus; cbn; lia).
      cbn [lib.Lib.Frame.outside]. unfold strtod_scratch in NS. tauto. }
  assert (VISK : forall a, strtod_scratch regs e a -> M' (Z_to_bv 64 a) = m' (Z_to_bv 64 a)).
  { intros a Ha. unfold M', munrestrict. rewrite (VIS a (or_intror (or_introl Ha))). reflexivity. }
  assert (GROWF : forall x, mem x <> None -> M' x <> None).
  { intros x Hx. unfold M', munrestrict. destruct (w_H W x) eqn:Hh; [exact Hx|].
    apply GROW. unfold mr, mrestrict. rewrite Hh. exact Hx. }
  exists (mkFP F' fc'), R', M', md'. split; [|split; [exact FRM'|]].
  { rewrite <- ret_pc_v_jalr. reflexivity. }
  exists bits, c, ev'.
  split.
  { apply (ainv_frame mem md M' md' AI).
    - intros a Ha Hown. unfold mbyte. rewrite (KEEP a Ha); [reflexivity|].
      intros NS. exact (NOWN a NS Hown).
    - intros a. unfold mbyte. destruct (mem (Z_to_bv 64 a)) as [b|] eqn:E1.
      + intros _. destruct (M' (Z_to_bv 64 a)) as [b'|] eqn:E2; [discriminate|].
        exfalso. apply (GROWF (Z_to_bv 64 a)); [rewrite E1; discriminate | exact E2].
      + intros Hr. destruct (M' (Z_to_bv 64 a)); [discriminate | exact Hr].
    - intros a. exact (YI04.present_grows mem M' a GROWF).
    - exact SBM. }
  split; [exact SBM|].
  split; [exact SC|].
  split; [exact Hc|].
  split; [exact FA0|].
  split; [exact FOK|].
  split.
  { intros r Hr. rewrite !getr_reg_get by (unfold YO0d.callee_saved in Hr; unfold is_x0; apply Z.eqb_neq;
      rewrite Z_to_bv_unsigned, bv_wrap_small by (unfold bv_modulus; cbn; lia); lia).
    rewrite <- XR by (unfold YO0d.callee_saved in Hr; unfold is_x0; apply Z.eqb_neq;
      rewrite Z_to_bv_unsigned, bv_wrap_small by (unfold bv_modulus; cbn; lia); lia).
    unfold YO0d.callee_saved in Hr.
    destruct Hr as [->|[->|[->|[->|[->|Hr]]]]]; [reflexivity..|].
    assert (r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) as Hr'
      by lia.
    destruct Hr' as [->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]; reflexivity. }
  split.
  { rewrite !getr_reg_get by reflexivity. rewrite <- XR by reflexivity. reflexivity. }
  split.
  { apply (rw_cells_agree m'); [exact PEC|]. intros x Hx. apply VISK. right. left. cbn in Hx. lia. }
  split.
  { apply (rw_cells_agree m'); [exact ERR'|]. intros x Hx. apply VISK. right. right. cbn in Hx. lia. }
  split.
  { intros a Ha NS. pose proof (KEEP a Ha NS) as Hk. unfold mbyte, writable_at, wview. rewrite Hk. tauto. }
  split; [intros a; exact (YI04.present_grows mem M' a GROWF)|].
  split.
  { intros a Hw. unfold writable_at in *. destruct (w_H W (Z_to_bv 64 a)) eqn:Hh.
    - rewrite (wview_agree mem M'); [exact Hw|]. unfold M', munrestrict. rewrite Hh. reflexivity.
    - rewrite (wview_agree m' M') by (unfold M', munrestrict; rewrite Hh; reflexivity).
      apply WM. rewrite (wview_agree mem mr) by (unfold mr, mrestrict; rewrite Hh; reflexivity). exact Hw. }
  split.
  { intros x b Hb. unfold M', munrestrict in Hb. destruct (w_H W x); [exact (MI x b Hb) | exact (MI' x b Hb)]. }
  split.
  { intros x b Hb. unfold M', munrestrict in Hb. destruct (w_H W x); [exact (TM x b Hb) | exact (TM' x b Hb)]. }
  apply (stk_agree m'); [exact ST'|]. intros x Hx. apply VISK. left. exact Hx.
Qed.

End strtod_x.
