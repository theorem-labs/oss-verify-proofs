(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Classical_Prop.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr Image MState Frame.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import Spec ShapeAlg PropExec.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Hull Restrict.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface LayoutPA AClient AIcpm9j AIcpnnp.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require Import A_World A_Img A_ImgAny.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd Require Import DA_Ey6n DA_Eg3i DA_Cells DA_Ldix DA_Entry DA_Mib4 DA_Inv DA_Main.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.

Notation wz z := (Z_to_bv 64 z) (only parsing).

Section FK.
  Context {Clg : Ceiling} {AI : AsanAlloc LPA}.   (* [comment removed for export] *)
  Variable usp : Z.
  Hypothesis HCEIL : alloc_ceiling = usp - 0x800000.   (* [comment removed for export] *)
  Variables argv envp : list (list byte).
  Variable fs : Fs.
  (* [comment removed for export] *)
  Variables (e0 e1 e2 e3 e4 e5 e6 e7 : word) (j8 : list byte).

  Definition MFR : list cell := [CB 8 j8; C8 e7; C8 e6; C8 e5; C8 e4; C8 e3; C8 e2; C8 e1; C8 e0; C8 (wz RA_MAIN)].   (* [comment removed for export] *)

  Record fview (A : AS) (m : word -> option byte) (md : Model)
               (fds : list (word * FdEntry)) (sof : stdout_form) (ini : Z) (tid : Z) : Prop := {
    fv_ainv : ainv A m md;
    fv_mi   : mem_inv rsegs (aview A m);
    fv_fs   : m_fs md = fs;
    fv_fds  : m_fds md = fds;
    fv_cc   : ccells (aview A m) tid sof ini;
    fv_args : args_at usp argv envp (aview A m);
    fv_sh   : forall a, in_stksh a -> aview A m (wz a) = Some (Z_to_bv 8 0);
    fv_stk  : stk rsegs (aview A m) (STK_LO usp) (SPF usp);
    fv_fr   : rw_cells rsegs (aview A m) (SPF usp) MFR
  }.

  (* [comment removed for export] *)
  Lemma fv_usp : forall A m md fds sof ini tid, fview A m md fds sof ini tid ->
    sp_window_lo <= usp /\ usp + e_span argv envp <= 2^47 /\ usp mod 16 = 0 /\ 0 <= e_span argv envp.
  Proof. intros A m md fds sof ini tid FV. exact (aa_usp _ _ _ _ (fv_args _ _ _ _ _ _ _ FV)). Qed.

  (* [comment removed for export] *)

  Lemma fv_consts : forall A m md fds sof ini tid, fview A m md fds sof ini tid -> consts_hold LPA (aview A m).
  Proof. intros A m md fds sof ini tid FV. exact (consts_hold_ainv LPA A m md (fv_ainv _ _ _ _ _ _ _ FV)). Qed.

  Lemma fv_gotc : forall A m md fds sof ini tid, fview A m md fds sof ini tid ->
    ro_cells rsegs (aview A m) 0xa9df8 [C8 (wz 0xa9088)].
  Proof.
    intros A m md fds sof ini tid FV. apply ro_C8_of_bytes. apply (consts_lookup _ 0xa9df8 _ (fv_consts _ _ _ _ _ _ _ FV)). vm_compute. reflexivity.
  Qed.

  Lemma fv_stderrp : forall A m md fds sof ini tid, fview A m md fds sof ini tid ->
    ro_cells rsegs (aview A m) STDERR_CELL [C8 (wz STDERR_F)].
  Proof. intros A m md fds sof ini tid FV. exact (mc_stderrp _ _ (proj1 (fv_cc _ _ _ _ _ _ _ FV))). Qed.

  Lemma fv_ceil : forall A m md fds sof ini tid, fview A m md fds sof ini tid -> alloc_ceiling <= STK_LO usp.
  Proof.
    intros A m md fds sof ini tid FV. unfold STK_LO. rewrite HCEIL. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma fview_stack : forall A m md fds sof ini tid m' md' fds' W,
    fview A m md fds sof ini tid ->
    ainv A m' md' -> mem_inv rsegs (aview A m') -> m_fs md' = fs -> m_fds md' = fds' ->
    munch W (aview A m) (aview A m') -> wmono rsegs (aview A m) (aview A m') ->
    stack_only usp W -> disjoint_from W (SPF usp) 80 ->
    stk rsegs (aview A m') (STK_LO usp) (SPF usp) ->
    fview A m' md' fds' sof ini tid.
  Proof.
    intros A m md fds sof ini tid m' md' fds' W FV AINV' MI' FS' FDS' MU WM SO DJ ST'.
    (first [ pose proof ((fv_usp _ _ _ _ _ _ _ FV)) as dR_1; dand4 dR_1 as U1 U2 U3 U4 | pose proof (fv_usp _ _ _ _ _ _ _ FV) as (U1 & U2 & U3 & U4) ]).
    destruct FV as [AINV MI FS FDS CC AR SH ST FR].
    (first [ pose proof ((bundle_stack usp argv envp HCEIL W _ _ tid sof ini MU SO U1 U2 CC AR SH)) as dR_2; dand4 dR_2 as CC' AR' SH' _ | destruct (bundle_stack usp argv envp HCEIL W _ _ tid sof ini MU SO U1 U2 CC AR SH) as (CC' & AR' & SH' & _) ]).
    constructor; try assumption.
    eapply (rw_cells_transport rsegs); [exact FR| exact MU| exact WM| exact DJ].
  Qed.

  (* [comment removed for export] *)
  Lemma fview_cframe : forall A A' m md m' md' fds fds' sof ini tid (sp win : Z) (V N : Z -> Prop),
    fview A m md fds sof ini tid ->
    ainv A' m' md' -> mem_inv rsegs (aview A' m') -> m_fs md' = fs -> m_fds md' = fds' ->
    cframe LPA (owned A) (owned A') sp win V N (aview A m) (aview A' m') -> heapish V ->
    alloc_ceiling <= sp - win -> STK_LO usp <= sp - win -> sp <= SPF usp ->
    stk rsegs (aview A' m') (STK_LO usp) (SPF usp) ->
    fview A' m' md' fds' sof ini tid.
  Proof.
    intros A A' m md m' md' fds fds' sof ini tid sp win V N FV AINV' MI' FS' FDS' CF HV CE WLO SPU ST'.
    (first [ pose proof ((fv_usp _ _ _ _ _ _ _ FV)) as dR_3; dand4 dR_3 as U1 U2 U3 U4 | pose proof (fv_usp _ _ _ _ _ _ _ FV) as (U1 & U2 & U3 & U4) ]). pose proof U1 as U1'. unfold sp_window_lo in U1'.
    destruct FV as [AINV MI FS FDS CC AR SH ST FR].
    (first [ pose proof ((bundle_cframe usp argv envp HCEIL A A' m md (aview A' m') sp win V N tid sof ini AINV CF CE ltac:(unfold SPF in SPU; lia) HV CC AR SH)) as dR_4; dand4 dR_4 as CC' AR' SH' _ | destruct (bundle_cframe usp argv envp HCEIL A A' m md (aview A' m') sp win V N tid sof ini AINV CF CE ltac:(unfold SPF in SPU; lia) HV CC AR SH)
      as (CC' & AR' & SH' & _) ]).
    constructor; try assumption.
    eapply (rw_cells_cframe A A' m md (aview A' m') sp win V N); try eassumption.
    - (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv). unfold SPF. lia.
    - cbn [cells_size MFR csize Nat.add]. cbn. unfold SPF. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma fview_ccall : forall A A' m md m' md' fds fds' sof ini tid (sp win : Z) (V N : Z -> Prop),
    fview A m md fds sof ini tid ->
    ainv A' m' md' -> mem_inv rsegs (aview A' m') -> m_fs md' = fs -> m_fds md' = fds' ->
    cframe LPA (owned A) (owned A') sp win V N (aview A m) (aview A' m') -> heapish V ->
    STK_LO usp <= sp - win -> sp <= SPF usp ->
    fview A' m' md' fds' sof ini tid.
  Proof.
    intros A A' m md m' md' fds fds' sof ini tid sp win V N FV AINV' MI' FS' FDS' CF HV WLO SPU.
    pose proof (fv_ceil _ _ _ _ _ _ _ FV) as CE.
    eapply fview_cframe; try eassumption; [lia|].
    eapply (stk_ccall LPA A A' m md); [exact (fv_ainv _ _ _ _ _ _ _ FV)| exact CF| exact (fv_stk _ _ _ _ _ _ _ FV)| exact CE| lia| exact SPU|].
    intros a Ha Va. heapish_elim HV a Va; (unfold STK_LO, SPF in *; heapish_case).
  Qed.

  (* [comment removed for export] *)
  Lemma ccells_after_fprintf : forall (v v' : word -> option byte) tid ini (lo hi : Z) fe',
    ccells v tid SO_pristine ini -> 0x60a000 <= lo ->
    munch [(lo, hi); (STDERR_F, STDERR_F + 152); (STDERR_BUFP, STDERR_BUFP + 8)] v v' ->
    stderr_ok fe' -> file_at v' STDERR_F fe' -> ccells v' tid SO_pristine ini.
  Proof.
    (intros v v' tid ini lo hi fe'; (first [ intro dR_11; dand4 dR_11 as MC1 _ SOUT1 TR1 | intros (MC1 & _ & SOUT1 & TR1) ]); intros LO MU2 FOK2 FE2).
    assert (AGM : agree_on (in_ranges MC_RANGES) v v') by (apply (agree_of_munch _ _ _ _ MU2); ranges_outside).
    assert (AGO : agree_on (in_ranges STDOUT_RANGES) v v') by (apply (agree_of_munch _ _ _ _ MU2); ranges_outside).
    assert (AGT : agree_on (in_ranges TR_RANGES) v v') by (apply (agree_of_munch _ _ _ _ MU2); ranges_outside).
    split; [eapply mcells_agree; [exact AGM| exact MC1]|]. split; [exists fe'; split; assumption|].
    split; [eapply stdout_at_agree; [exact AGO| exact SOUT1]|]. revert TR1 AGT. clear. intros TR1 AGT.
    exact (trcells_agree _ _ _ AGT TR1).   (* [comment removed for export] *)
  Qed.

  Lemma ccells_after_fwrite : forall (v v' : word -> option byte) tid ini (lo hi : Z) fe',
    ccells v tid SO_pristine ini -> 0x60a000 <= lo ->
    munch [(lo, hi); (STDERR_F, STDERR_F + 152)] v v' ->
    stderr_ok fe' -> file_at v' STDERR_F fe' -> ccells v' tid SO_pristine ini.
  Proof.
    (intros v v' tid ini lo hi fe'; (first [ intro dR_12; dand4 dR_12 as MC1 _ SOUT1 TR1 | intros (MC1 & _ & SOUT1 & TR1) ]); intros LO MU2 FOK2 FE2).
    assert (AGM : agree_on (in_ranges MC_RANGES) v v') by (apply (agree_of_munch _ _ _ _ MU2); ranges_outside).
    assert (AGO : agree_on (in_ranges STDOUT_RANGES) v v') by (apply (agree_of_munch _ _ _ _ MU2); ranges_outside).
    assert (AGT : agree_on (in_ranges TR_RANGES) v v') by (apply (agree_of_munch _ _ _ _ MU2); ranges_outside).
    split; [eapply mcells_agree; [exact AGM| exact MC1]|]. split; [exists fe'; split; assumption|].
    split; [eapply stdout_at_agree; [exact AGO| exact SOUT1]|]. revert TR1 AGT. clear. intros TR1 AGT.
    exact (trcells_agree _ _ _ AGT TR1).   (* [comment removed for export] *)
  Qed.

  (* [comment removed for export] *)
  Lemma fview_after_fwrite : forall A m md m' md' fds fds' ini tid (w : Z) fe',
    fview A m md fds SO_pristine ini tid ->
    ainv A m' md' -> mem_inv rsegs (aview A m') -> m_fs md' = fs -> m_fds md' = fds' ->
    munch [(SPF usp - w, SPF usp); (STDERR_F, STDERR_F + 152)] (aview A m) (aview A m') ->
    wmono rsegs (aview A m) (aview A m') -> 0 <= w -> STK_LO usp <= SPF usp - w ->
    stderr_ok fe' -> file_at (aview A m') STDERR_F fe' ->
    stk rsegs (aview A m') (STK_LO usp) (SPF usp) ->
    fview A m' md' fds' SO_pristine ini tid.
  Proof.
    intros A m md m' md' fds fds' ini tid w fe' FV AINV' MI' FS' FDS' MU WM W0 WLO FOK FE ST'.
    (first [ pose proof ((fv_usp _ _ _ _ _ _ _ FV)) as dR_5; dand4 dR_5 as U1 U2 U3 U4 | pose proof (fv_usp _ _ _ _ _ _ _ FV) as (U1 & U2 & U3 & U4) ]). pose proof U1 as U1'. unfold sp_window_lo in U1'.
    destruct FV as [AINV MI FS FDS CC AR SH ST FR].
    pose proof (aa_b0 _ _ _ _ AR) as B0. pose proof (aa_b1 _ _ _ _ AR) as B1.
    constructor; try assumption.
    - eapply (ccells_after_fwrite (aview A m)); [exact CC| | exact MU| exact FOK| exact FE]. unfold STK_LO, SPF in *. lia.
    - apply (args_at_agree usp argv envp (aview A m)); [| exact AR]. apply (agree_of_munch _ _ _ _ MU).
      intros a Ha. unfold in_args, e_p1a in *. unfold e_p0a, e_L0, e_L1, e_argc, e_envc, e_span, STDERR_F, SPF, STK_LO in *. cbn [outside].
      destruct Ha as [R|[[_ R]|[R|[H2 R]]]]; [| | | specialize (B1 H2)]; (split; [lia| OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try exact I; lia]).
    - intros a Ha. rewrite <- (SH a Ha). apply (MU (wz a)). unfold in_stksh, STKSH_LO, STKSH_HI, sh, kShadowOffset in Ha; (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv). rewrite unsigned_lit by lia.
      unfold STDERR_F, SPF, STK_LO in *. cbn [outside]. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try exact I; lia.
    - eapply (rw_cells_transport rsegs); [exact FR| exact MU| exact WM|]. unfold STDERR_F, SPF in *. cbn. lia.
  Qed.

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma mapped_rw_cells : forall (v : word -> option byte) a n,
    mapped v a n -> 0x60a000 <= a -> 0 <= n -> a + n <= 2^64 ->
    exists junk, rw_cells rsegs v a [CB (Z.to_nat n) junk].
  Proof.
    intros v a n MP LO N0 HI.
    set (f := fun i : nat => match v (wz (a + Z.of_nat i)) with Some b => b | None => Z_to_bv 8 0 end).
    exists (map f (seq 0 (Z.to_nat n))).
    assert (LEN : length (map f (seq 0 (Z.to_nat n))) = Z.to_nat n) by (rewrite length_map, length_seq; reflexivity).
    split; [split|].
    - cbn. rewrite LEN. split; [reflexivity| exact I].
    - cbn [cells_bytes cbytes]. rewrite app_nil_r. split; [lia|]. split; [rewrite LEN; lia|]. rewrite LEN. intros i Hi.
      rewrite (nth_error_nth' _ (f 0%nat)) by (rewrite LEN; exact Hi). rewrite map_nth, seq_nth by exact Hi. cbn [Nat.add].
      unfold f. pose proof (MP (Z.of_nat i) ltac:(lia)) as P. rewrite pa_mrd_overlay by (rewrite unsigned_lit by lia; lia). unfold wa.
      destruct (v (wz (a + Z.of_nat i))) as [b|]; [reflexivity| exfalso; apply P; reflexivity].
    - split; [lia|]. split; [cbn [cells_size csize Nat.add]; lia|]. cbn [cells_size csize Nat.add]. intros i Hi.
      pose proof (MP i ltac:(lia)) as P. unfold wa. rewrite pa_wview_overlay by (rewrite unsigned_lit by lia; lia). exact P.
  Qed.
End FK.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CBK.
  #[local] Notation mem := (word -> option byte).

  Lemma rwCB_elim : forall (v : mem) a n l,
    rw_cells rsegs v a [CB n l] -> length l = n /\ bytes_at rsegs v a l /\ wr_at rsegs v a (Z.of_nat n).
  Proof.
    intros v a n l [[WF B] W]. cbn in WF. destruct WF as [LEN _]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B.
    cbn [cells_size csize Nat.add] in W. rewrite Nat.add_0_r in W. split; [exact LEN|]. split; [exact B| exact W].
  Qed.

  Lemma rwCB_intro : forall (v : mem) a n l,
    length l = n -> bytes_at rsegs v a l -> wr_at rsegs v a (Z.of_nat n) -> rw_cells rsegs v a [CB n l].
  Proof.
    intros v a n l LEN B W. split; [split|].
    - cbn. split; [exact LEN| exact I].
    - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact B.
    - cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r. exact W.
  Qed.

  Lemma wr_at_app : forall (v : mem) a n1 n2, 0 <= n1 -> 0 <= n2 ->
    wr_at rsegs v a (n1 + n2) <-> wr_at rsegs v a n1 /\ wr_at rsegs v (a + n1) n2.
  Proof.
    intros v a n1 n2 N1 N2. unfold wr_at. split.
    - ((first [ intro dR_13; dand3 dR_13 as A0 A1 W | intros (A0 & A1 & W) ])). OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try lia.
      + intros i Hi. apply W. lia.
      + intros i Hi. replace (a + n1 + i) with (a + (n1 + i)) by lia. apply W. lia.
    - intros ((A0 & A1 & W1) & (B0 & B1 & W2)). OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try lia.
      intros i Hi. destruct (Z_lt_le_dec i n1); [apply W1; lia|].
      replace (a + i) with (a + n1 + (i - n1)) by lia. apply W2. lia.
  Qed.

  Lemma rwCB_app : forall (v : mem) a n1 n2 l1 l2,
    rw_cells rsegs v a [CB n1 l1] -> rw_cells rsegs v (a + Z.of_nat n1) [CB n2 l2] ->
    rw_cells rsegs v a [CB (n1 + n2) (l1 ++ l2)].
  Proof.
    intros v a n1 n2 l1 l2 R1 R2.
    (first [ pose proof ((rwCB_elim v a n1 l1 R1)) as dR_7; dand3 dR_7 as L1 B1 W1 | destruct (rwCB_elim v a n1 l1 R1) as (L1 & B1 & W1) ]). (first [ pose proof ((rwCB_elim v _ n2 l2 R2)) as dR_8; dand3 dR_8 as L2 B2 W2 | destruct (rwCB_elim v _ n2 l2 R2) as (L2 & B2 & W2) ]).
    apply rwCB_intro.
    - rewrite length_app. lia.
    - apply (proj2 (bytes_at_app rsegs v a l1 l2)). rewrite L1. split; assumption.
    - rewrite Nat2Z.inj_add. apply (proj2 (wr_at_app v a (Z.of_nat n1) (Z.of_nat n2) ltac:(lia) ltac:(lia))). split; assumption.
  Qed.

  Lemma rwCB_split : forall (v : mem) a n l (k : nat),
    rw_cells rsegs v a [CB n l] -> (k <= n)%nat ->
    rw_cells rsegs v a [CB k (firstn k l)] /\ rw_cells rsegs v (a + Z.of_nat k) [CB (n - k) (skipn k l)].
  Proof.
    intros v a n l k R K. (first [ pose proof ((rwCB_elim v a n l R)) as dR_9; dand3 dR_9 as LEN B W | destruct (rwCB_elim v a n l R) as (LEN & B & W) ]).
    rewrite <- (firstn_skipn k l) in B. apply (proj1 (bytes_at_app rsegs v a _ _)) in B. destruct B as [B1 B2].
    rewrite firstn_length_le in B2 by lia.
    replace (Z.of_nat n) with (Z.of_nat k + Z.of_nat (n - k)) in W by lia.
    apply (proj1 (wr_at_app v a (Z.of_nat k) (Z.of_nat (n - k)) ltac:(lia) ltac:(lia))) in W. destruct W as [W1 W2].
    split; apply rwCB_intro; try assumption.
    - rewrite firstn_length_le; lia.
    - rewrite length_skipn. lia.
  Qed.

  Lemma rwCB2_split : forall (v : mem) a n1 n2 l1 l2,
    rw_cells rsegs v a [CB n1 l1; CB n2 l2] ->
    rw_cells rsegs v a [CB n1 l1] /\ rw_cells rsegs v (a + Z.of_nat n1) [CB n2 l2].
  Proof.
    intros v a n1 n2 l1 l2 [[WF B] W]. cbn in WF. (first [ dand3 WF as L1 L2 _ | destruct WF as (L1 & L2 & _) ]).
    cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. apply (proj1 (bytes_at_app rsegs v a l1 l2)) in B. destruct B as [B1 B2].
    rewrite L1 in B2. cbn [cells_size csize] in W. rewrite Nat.add_0_r in W.
    replace (Z.of_nat (n1 + n2)) with (Z.of_nat n1 + Z.of_nat n2) in W by lia.
    apply (proj1 (wr_at_app v a (Z.of_nat n1) (Z.of_nat n2) ltac:(lia) ltac:(lia))) in W. destruct W as [W1 W2].
    split; apply rwCB_intro; assumption.
  Qed.

  (* [comment removed for export] *)
  Lemma firstn_min_length : forall (l : list byte) (cnt : nat), firstn (length (firstn cnt l)) l = firstn cnt l.
  Proof.
    intros l cnt. rewrite length_firstn. destruct (Nat.le_gt_cases cnt (length l)) as [A|A].
    - rewrite Nat.min_l by lia. reflexivity.
    - rewrite Nat.min_r by lia. rewrite firstn_all, firstn_all2 by lia. reflexivity.
  Qed.

  Lemma firstn_extend : forall (data : list byte) (len cnt : nat),
    firstn len data ++ firstn cnt (skipn len data) = firstn (len + length (firstn cnt (skipn len data))) data.
  Proof.
    induction data as [|x l IH]; intros len cnt.
    - rewrite !firstn_nil, skipn_nil, firstn_nil. reflexivity.
    - destruct len as [|len].
      + cbn [firstn skipn app Nat.add]. symmetry. apply firstn_min_length.
      + cbn [firstn skipn app Nat.add]. f_equal. apply IH.
  Qed.
End CBK.
