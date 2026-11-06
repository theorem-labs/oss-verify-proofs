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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr Image MState.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import Spec ShapeAlg PropExec.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Hull Restrict.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface LayoutPA AClient AIcpm9j AIcpnnp.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require Import A_World A_Img A_ImgAny.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd Require Import DA_Ey6n DA_Eg3i DA_Cells DA_Ldix DA_Entry DA_Mib4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.

Notation wz z := (Z_to_bv 64 z) (only parsing).

(* [comment removed for export] *)
Definition SPF (usp : Z) : Z := usp - 128.   (* [comment removed for export] *)

Definition in_ranges (l : list (Z * Z)) (a : Z) : Prop := exists lo hi, In (lo, hi) l /\ lo <= a < hi.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section S.
  Context {Clg : Ceiling} {AI : AsanAlloc LPA}.   (* [comment removed for export] *)
  Variable usp : Z.
  Variables argv envp : list (list byte).
  Variable fs : Fs.
  (* [comment removed for export] *)
  Hypothesis HCEIL : alloc_ceiling = usp - 0x800000.
  #[local] Notation p0a := (e_p0a usp argv envp).
  #[local] Notation p1a := (e_p1a usp argv envp).
  #[local] Notation argc := (e_argc argv).
  #[local] Notation span := (e_span argv envp).

  (* [comment removed for export] *)
  Record args_at (v : word -> option byte) : Prop := {
    aa_p0 : bytes_at rsegs v (usp + 8) (le8 (wz p0a));
    aa_p1 : 2 <= argc -> bytes_at rsegs v (usp + 16) (le8 (wz p1a));
    aa_s0 : bytes_at rsegs v p0a (nth 0 argv [] ++ [Z_to_bv 8 0]);
    aa_s1 : 2 <= argc -> bytes_at rsegs v p1a (nth 1 argv [] ++ [Z_to_bv 8 0]);
    (* [comment removed for export] *)
    aa_k0 : exists sl, length sl = 16%nat /\ bytes_at rsegs v (p0a + e_L0 argv + 1) sl;
    aa_k1 : 2 <= argc -> exists sl, length sl = 16%nat /\ bytes_at rsegs v (p1a + e_L1 argv + 1) sl;
    aa_b0 : usp + 24 <= p0a /\ p0a + e_L0 argv + 1 + 16 <= usp + span;
    aa_b1 : 2 <= argc -> p1a + e_L1 argv + 1 + 16 <= usp + span;
    aa_usp : sp_window_lo <= usp /\ usp + span <= 2^47 /\ usp mod 16 = 0 /\ 0 <= span
  }.

  (* [comment removed for export] *)
  Definition ccells (v : word -> option byte) (tid : Z) (sof : stdout_form) (ini : Z) : Prop :=
    mcells v tid /\ (exists fe, stderr_ok fe /\ file_at v STDERR_F fe) /\ stdout_at v sof
    /\ trcells v ini.   (* [comment removed for export] *)

  Lemma ccells_of_dcells : forall v tid sof ini, dcells v tid sof ini -> ccells v tid sof ini.
  Proof.
    (intros v tid sof ini; (first [ intro dR_20; dand4 dR_20 as MC FE SO TR | intros (MC & FE & SO & TR) ])). split; [exact MC|]. split; [| split; assumption].
    exists stderr0. split; [| exact FE]. exists w0, 0. split; [reflexivity| left; reflexivity].
  Qed.

  (* [comment removed for export] *)
  Record dinv (A : AS) (m : word -> option byte) (md : Model) (spc : Z)
              (fds : list (word * FdEntry)) (sof : stdout_form) (ini : Z) : Prop := {
    di_ainv  : ainv A m md;
    di_mi    : mem_inv rsegs (aview A m);
    di_fs    : m_fs md = fs;
    di_fds   : m_fds md = fds;
    di_frames : forall ff, a_frame A ff = None;
    di_stk   : stk rsegs (aview A m) (STK_LO usp) spc;
    di_spc   : STK_LO usp + 0x700000 <= spc <= usp;
    di_stksh : forall a, STKSH_LO <= a < STKSH_HI -> aview A m (wz a) = Some (Z_to_bv 8 0);
    di_cells : exists tid, ccells (aview A m) tid sof ini;
    di_sspgot : ro_cells rsegs (aview A m) SSP_GOT [C8 (wz SSP_GUARD)];
    di_args  : args_at (aview A m)
  }.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma dinv_of_main_view : forall A m md, main_view usp argv envp fs A m md -> dinv A m md usp fds_std SO_pristine 0.
  Proof.
    intros A m md MV. destruct MV. (first [ pose proof (mv_usp) as dR_1; dand4 dR_1 as U1 U2 U3 U4 | pose proof mv_usp as (U1 & U2 & U3 & U4) ]). unfold sp_window_lo in U1.
    constructor; try assumption.
    - exact (ea_frames _ _ _ mv_A0).
    - unfold STK_LO. lia.
    - destruct mv_cells as [tid DC]. exists tid. apply ccells_of_dcells. exact DC.
    - constructor; assumption.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition agree_on (P : Z -> Prop) (v v' : word -> option byte) : Prop := forall a, P a -> v' (wz a) = v (wz a).

  Lemma agree_on_mono : forall (P Q : Z -> Prop) v v', (forall a, Q a -> P a) -> agree_on P v v' -> agree_on Q v v'.
  Proof. intros P Q v v' H AG a Ha. apply AG, H, Ha. Qed.
  Lemma in_ranges_app : forall l1 l2 a, in_ranges (l1 ++ l2) a <-> in_ranges l1 a \/ in_ranges l2 a.
  Proof.
    intros l1 l2 a. unfold in_ranges. split.
    - ((first [ intro dR_21; dex2 dR_21 as lo hi; destruct dR_21 as [Hin R] | intro dR_21; dand4 dR_21 as lo hi Hin R | intros (lo & hi & Hin & R) ])). apply in_app_or in Hin as [H|H]; [left|right]; exists lo, hi; tauto.
    - intros [(lo & hi & Hin & R)|(lo & hi & Hin & R)]; exists lo, hi; split; try assumption; apply in_or_app; tauto.
  Qed.
  Lemma agree_app_l : forall l1 l2 v v', agree_on (in_ranges (l1 ++ l2)) v v' -> agree_on (in_ranges l1) v v'.
  Proof. intros. eapply agree_on_mono; [| eassumption]. intros a Ha. apply in_ranges_app. tauto. Qed.
  Lemma agree_app_r : forall l1 l2 v v', agree_on (in_ranges (l1 ++ l2)) v v' -> agree_on (in_ranges l2) v v'.
  Proof. intros. eapply agree_on_mono; [| eassumption]. intros a Ha. apply in_ranges_app. tauto. Qed.

  Lemma agree_ranges_cell : forall l v v' a n, agree_on (in_ranges l) v v' ->
    (exists lo hi, In (lo, hi) l /\ lo <= a /\ a + n <= hi) ->
    forall i, 0 <= i < n -> v' (wz (a + i)) = v (wz (a + i)).
  Proof. (intros l v v' a n AG; (first [ intro dR_22; dex2 dR_22 as lo hi; dand3 dR_22 as Hin H1 H2 | intro dR_22; dand5 dR_22 as lo hi Hin H1 H2 | intros (lo & hi & Hin & H1 & H2) ]); intros i Hi). apply AG. exists lo, hi. split; [exact Hin| lia]. Qed.

  Lemma cell_in_ranges_b : forall l a n,
    existsb (fun p => (fst p <=? a) && (a + n <=? snd p))%bool l = true ->
    exists lo hi, In (lo, hi) l /\ lo <= a /\ a + n <= hi.
  Proof.
    intros l a n H. apply existsb_exists in H as ([lo hi] & Hin & Hb). cbn in Hb.
    apply andb_prop in Hb as [B1 B2]. apply Z.leb_le in B1. apply Z.leb_le in B2. exists lo, hi. split; [exact Hin| lia].
  Qed.

  (* [comment removed for export] *)
  Ltac agree_rng l AG :=
    apply (agree_ranges_cell l _ _ _ _ AG); apply cell_in_ranges_b;
    cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ];
    unfold STDERR_F, STDOUT_F, STDIN_F, ATEXIT, STDOUT_BUF, STDERR_BUFP, STDERR_CELL, TID_CELL, EXIT_LOCK, NEED_LOCKS, OFL_HEAD,
           SSP_GUARD, SSP_GOT, TR_INITIALIZED, TR_INCB, TR_EMPTY; vm_compute; reflexivity.
  Ltac agree_cell l AG :=
    match goal with
    | H : ro_cells _ _ ?a ?cs |- ro_cells _ _ ?a ?cs => refine (ro_cells_agree rsegs _ _ a cs _ H); agree_rng l AG
    | H : rw_cells _ _ ?a ?cs |- rw_cells _ _ ?a ?cs => refine (rw_cells_agree rsegs _ _ a cs _ H); agree_rng l AG
    end.

  (* [comment removed for export] *)
  Definition MC_RANGES : list (Z * Z) :=
    [(TID_CELL, TID_CELL + 4); (EXIT_LOCK, EXIT_LOCK + 4);
     (ATEXIT, ATEXIT + 8); (ATEXIT + 16, ATEXIT + 40); (ATEXIT + 288, ATEXIT + 296);   (* [comment removed for export] *)
     (NEED_LOCKS, NEED_LOCKS + 1);
     (OFL_HEAD, OFL_HEAD + 8); (0xada10, 0xada18); (0xadb00, 0xadbf8); (0xadbf0, 0xadc20);
     (STDIN_F, STDIN_F + 152); (STDERR_CELL, STDERR_CELL + 8); (SSP_GUARD, SSP_GUARD + 8); (TR_EMPTY, TR_EMPTY + 16);
     (SSP_GOT, SSP_GOT + 8)].
  Definition STDERR_RANGES : list (Z * Z) := [(STDERR_F, STDERR_F + 152)].
  Definition STDOUT_RANGES : list (Z * Z) := [(STDOUT_F, STDOUT_F + 152); (STDOUT_BUF, STDOUT_BUF + 1024)].
  Definition TR_RANGES : list (Z * Z) :=   (* [comment removed for export] *)
    [(TR_INITIALIZED, TR_INITIALIZED + 1); (TR_INCB, TR_INCB + 1); (ATEXIT + 8, ATEXIT + 12); (ATEXIT + 40, ATEXIT + 48); (ATEXIT + 296, ATEXIT + 304)].
  Definition GOT_RANGES : list (Z * Z) := [(SSP_GOT, SSP_GOT + 8)].
  Definition CC_RANGES : list (Z * Z) := MC_RANGES ++ STDERR_RANGES ++ STDOUT_RANGES ++ TR_RANGES.

  Lemma stderr_agree : forall v v' f, agree_on (in_ranges STDERR_RANGES) v v' -> file_at v STDERR_F f -> file_at v' STDERR_F f.
  Proof.
    intros v v' f AG FA. unfold file_at in *. refine (rw_cells_agree rsegs _ _ _ _ _ FA). rewrite file_cells_size. agree_rng STDERR_RANGES AG.
  Qed.

  Lemma stdout_at_agree : forall v v' sof, agree_on (in_ranges STDOUT_RANGES) v v' -> stdout_at v sof -> stdout_at v' sof.
  Proof.
    intros v v' sof AG ST. destruct sof as [|p]; cbn [stdout_at] in *.
    - destruct ST as [FA [junk BUF]]. split.
      + unfold file_at in *. refine (rw_cells_agree rsegs _ _ _ _ _ FA). rewrite file_cells_size. agree_rng STDOUT_RANGES AG.
      + exists junk. agree_cell STDOUT_RANGES AG.
    - (first [ dex2 ST as mo junk; dand3 ST as FA BUF LEN | dand5 ST as mo junk FA BUF LEN | destruct ST as (mo & junk & FA & BUF & LEN) ]). exists mo, junk. split.
      + unfold file_at in *. refine (rw_cells_agree rsegs _ _ _ _ _ FA). rewrite file_cells_size. agree_rng STDOUT_RANGES AG.
      + split; [| exact LEN]. refine (rw_cells_agree rsegs _ _ _ _ _ BUF).
        apply (agree_ranges_cell STDOUT_RANGES _ _ _ _ AG). exists STDOUT_BUF, (STDOUT_BUF + 1024).
        split; [unfold STDOUT_RANGES; cbn [In]; tauto|]. cbn [cells_size csize]. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma errbuf_any : forall v, exists j8, rw_cells rsegs v STDERR_BUFP [CB 8 j8].
  Proof.
    intros v. (first [ pose proof ((junk_bytes v STDERR_BUFP 8 ltac:(vm_compute; discriminate) ltac:(unfold STDERR_BUFP; lia) ltac:(unfold STDERR_BUFP; lia))) as dR_3; dex1 dR_3 as j; destruct dR_3 as [L B] | pose proof ((junk_bytes v STDERR_BUFP 8 ltac:(vm_compute; discriminate) ltac:(unfold STDERR_BUFP; lia) ltac:(unfold STDERR_BUFP; lia))) as dR_3; dand3 dR_3 as j L B | destruct (junk_bytes v STDERR_BUFP 8 ltac:(vm_compute; discriminate) ltac:(unfold STDERR_BUFP; lia) ltac:(unfold STDERR_BUFP; lia)) as (j & L & B) ]).
    exists j. split; [split; [cbn; split; [exact L| exact I]| cbn [cells_bytes cbytes]; rewrite app_nil_r; exact B]|].
    cbn [cells_size csize Nat.add]. apply (wr_at_of_b v STDERR_BUFP 8); [unfold STDERR_BUFP; lia| unfold STDERR_BUFP; lia| vm_compute; reflexivity].
  Qed.

  Lemma mcells_agree : forall v v' tid, agree_on (in_ranges MC_RANGES) v v' -> mcells v tid -> mcells v' tid.
  Proof.
    intros v v' tid AG MC. destruct MC. constructor; try assumption.
    all: try (agree_cell MC_RANGES AG).
    - (first [ dex2 mc_in as wp rp; dand5 mc_in as H1 H2 H3 H4 H5 | dand7 mc_in as wp rp H1 H2 H3 H4 H5 | destruct mc_in as (wp & rp & H1 & H2 & H3 & H4 & H5) ]). exists wp, rp.
      unfold file_clean. split; [|split; [|split; [|split]]]; agree_cell MC_RANGES AG.
    - destruct mc_canary as [g H]. exists g. agree_cell MC_RANGES AG.
    - apply errbuf_any.
    - destruct mc_empty as [j H]. exists j. agree_cell MC_RANGES AG.
  Qed.

  (* [comment removed for export] *)
  Lemma trcells_agree : forall v v' ini, agree_on (in_ranges TR_RANGES) v v' -> trcells v ini -> trcells v' ini.
  Proof.
    intros v v' ini AG (I01 & T1 & T2 & T3 & T4 & T5). split; [exact I01|].
    split; [agree_cell TR_RANGES AG|]. split; [agree_cell TR_RANGES AG|]. split; [agree_cell TR_RANGES AG|].
    split; agree_cell TR_RANGES AG.
  Qed.

  Lemma ccells_agree : forall v v' tid sof ini, agree_on (in_ranges CC_RANGES) v v' ->
    ccells v tid sof ini -> ccells v' tid sof ini.
  Proof.
    (intros v v' tid sof ini AG; (first [ intro dR_23; dand4 dR_23 as MC [fe [FOK FE]] SO TR | intros (MC & [fe [FOK FE]] & SO & TR) ])). unfold CC_RANGES in AG.
    split; [exact (mcells_agree v v' tid (agree_app_l _ _ _ _ AG) MC)|]. apply agree_app_r in AG.
    split; [exists fe; split; [exact FOK| exact (stderr_agree v v' _ (agree_app_l _ _ _ _ AG) FE)]|]. apply agree_app_r in AG.
    split; [exact (stdout_at_agree v v' sof (agree_app_l _ _ _ _ AG) SO)|]. apply agree_app_r in AG.
    exact (trcells_agree v v' ini AG TR).
  Qed.

  Lemma sspgot_agree : forall v v', agree_on (in_ranges GOT_RANGES) v v' ->
    ro_cells rsegs v SSP_GOT [C8 (wz SSP_GUARD)] -> ro_cells rsegs v' SSP_GOT [C8 (wz SSP_GUARD)].
  Proof. intros v v' AG H. agree_cell GOT_RANGES AG. Qed.

  (* [comment removed for export] *)
  Definition trcells_x (v : word -> option byte) (ini cb : Z) : Prop :=
    (ini = 0 \/ ini = 1)
    /\ rw_cells rsegs v TR_INITIALIZED [C1 (Z_to_bv 8 ini)]
    /\ rw_cells rsegs v TR_INCB [C1 (Z_to_bv 8 cb)]
    /\ rw_cells rsegs v (ATEXIT + 8) [C4 (Z_to_bv 64 (1 + ini))]
    /\ rw_cells rsegs v (ATEXIT + 40) [C8 (Z_to_bv 64 (ini * CALL_TRAMP))]
    /\ rw_cells rsegs v (ATEXIT + 296) [C8 (Z_to_bv 64 (ini * AEF_GUARD))].
  Definition ccells_x (v : word -> option byte) (tid : Z) (sof : stdout_form) (ini cb : Z) : Prop :=
    mcells v tid /\ (exists fe, stderr_ok fe /\ file_at v STDERR_F fe) /\ stdout_at v sof /\ trcells_x v ini cb.
  Lemma trcells_x_0 : forall v ini, trcells_x v ini 0 = trcells v ini.
  Proof. reflexivity. Qed.
  Lemma ccells_x_0 : forall v tid sof ini, ccells_x v tid sof ini 0 = ccells v tid sof ini.
  Proof. reflexivity. Qed.

  Lemma trcells_x_agree : forall v v' ini cb, agree_on (in_ranges TR_RANGES) v v' -> trcells_x v ini cb -> trcells_x v' ini cb.
  Proof.
    intros v v' ini cb AG (I01 & T1 & T2 & T3 & T4 & T5). split; [exact I01|].
    split; [agree_cell TR_RANGES AG|]. split; [agree_cell TR_RANGES AG|]. split; [agree_cell TR_RANGES AG|].
    split; agree_cell TR_RANGES AG.
  Qed.

  Lemma ccells_x_agree : forall v v' tid sof ini cb, agree_on (in_ranges CC_RANGES) v v' ->
    ccells_x v tid sof ini cb -> ccells_x v' tid sof ini cb.
  Proof.
    (intros v v' tid sof ini cb AG; (first [ intro dR_23; dand4 dR_23 as MC [fe [FOK FE]] SO TR | intros (MC & [fe [FOK FE]] & SO & TR) ])). unfold CC_RANGES in AG.
    split; [exact (mcells_agree v v' tid (agree_app_l _ _ _ _ AG) MC)|]. apply agree_app_r in AG.
    split; [exists fe; split; [exact FOK| exact (stderr_agree v v' _ (agree_app_l _ _ _ _ AG) FE)]|]. apply agree_app_r in AG.
    split; [exact (stdout_at_agree v v' sof (agree_app_l _ _ _ _ AG) SO)|]. apply agree_app_r in AG.
    exact (trcells_x_agree v v' ini cb AG TR).
  Qed.

  (* [comment removed for export] *)
  Definition HBSS (a : Z) : Prop := (0x5e7a40 <= a < 0x5e7a40 + 8) \/ (0x5e7a60 <= a < 0x5e7a60 + 8).
(* [comment removed for export] *)
Ltac heapish_elim HV a Va :=
  let X := fresh "X" in destruct (HV a Va) as [X|[X|[X|[X|[X|[X|X]]]]]]; revert X.
Ltac heapish_case :=
  let X := fresh "X" in intros X;
  first [ unfold HBSS in X; lia
        | lazymatch goal with NB : ~ HBSS _ |- _ => exact (NB X) end
        | unfold HBSS, sh, kShadowOffset, kHighMemBeg, kLowShadowMapBeg in *;
          (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv); Z.div_mod_to_equations; lia ].


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma cc_ranges_where : forall a, in_ranges (CC_RANGES ++ GOT_RANGES) a ->
    0xa8000 <= a < 0x60a000 /\ ~ pa_static a /\ ~ (0x5e8334 <= a < 0x5e8334 + 4) /\ ~ HBSS a /\ ~ (0x5d7a10 <= a < 0x5e7a10).
  Proof.
    (intros a; (first [ intro dR_24; dex2 dR_24 as lo hi; destruct dR_24 as [Hin Hr] | intro dR_24; dand4 dR_24 as lo hi Hin Hr | intros (lo & hi & Hin & Hr) ])). unfold CC_RANGES, MC_RANGES, STDERR_RANGES, STDOUT_RANGES, TR_RANGES, GOT_RANGES in Hin.
    unfold SSP_GOT, STDERR_F, STDOUT_F, STDIN_F, STDERR_CELL, TR_INITIALIZED, TR_INCB, TR_EMPTY, TID_CELL, SSP_GUARD, ATEXIT, EXIT_LOCK,
      NEED_LOCKS, OFL_HEAD, STDERR_BUFP, STDOUT_BUF in Hin.
    cbn [In Z.add app] in Hin. unfold pa_static, HBSS.
    repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]). destruct Hin.
  Qed.

  (* [comment removed for export] *)
  Definition in_args (a : Z) : Prop :=
       (usp + 8 <= a < usp + 16) \/ (2 <= argc /\ usp + 16 <= a < usp + 24)
    \/ (p0a <= a < p0a + e_L0 argv + 1 + 16)
    \/ (2 <= argc /\ p1a <= a < p1a + e_L1 argv + 1 + 16).

  Ltac eun2 := unfold in_args, e_p1a in *; unfold e_p0a, e_L0, e_L1, e_argc, e_envc, e_span, sp_window_lo in *.

  Lemma args_at_agree : forall v v', agree_on in_args v v' -> args_at v -> args_at v'.
  Proof.
    intros v v' AG AR. destruct AR as [P0 P1 S0 S1 K0 K1 B0 B1 U]. (first [ pose proof (U) as dR_5; dand4 dR_5 as U1 U2 U3 U4 | pose proof U as (U1 & U2 & U3 & U4) ]).
    constructor; try assumption.
    - refine (bytes_at_agree rsegs _ _ _ _ _ P0). intros i Hi. apply AG. rewrite length_le8 in Hi. left. lia.
    - intros H2. refine (bytes_at_agree rsegs _ _ _ _ _ (P1 H2)). intros i Hi. apply AG. rewrite length_le8 in Hi. right. left. split; [exact H2| lia].
    - refine (bytes_at_agree rsegs _ _ _ _ _ S0). intros i Hi. apply AG. rewrite length_app in Hi. cbn [length] in Hi.
      right. right. left. unfold e_L0. lia.
    - intros H2. refine (bytes_at_agree rsegs _ _ _ _ _ (S1 H2)). intros i Hi. apply AG. rewrite length_app in Hi. cbn [length] in Hi.
      right. right. right. unfold e_L1. split; [exact H2| lia].
    - (first [ dex1 K0 as sl; destruct K0 as [L B] | dand3 K0 as sl L B | destruct K0 as (sl & L & B) ]). exists sl. split; [exact L|]. refine (bytes_at_agree rsegs _ _ _ _ _ B). intros i Hi. apply AG.
      rewrite L in Hi. right. right. left. unfold e_L0 in *. lia.
    - intros H2. (first [ pose proof ((K1 H2)) as dR_7; dex1 dR_7 as sl; destruct dR_7 as [L B] | pose proof ((K1 H2)) as dR_7; dand3 dR_7 as sl L B | destruct (K1 H2) as (sl & L & B) ]). exists sl. split; [exact L|]. refine (bytes_at_agree rsegs _ _ _ _ _ B). intros i Hi. apply AG.
      rewrite L in Hi. right. right. right. unfold e_L1 in *. split; [exact H2| lia].
  Qed.

  (* [comment removed for export] *)
  Lemma arg_slack : forall v pa (arg sl : list byte),
    bytes_at rsegs v pa (arg ++ [Z_to_bv 8 0]) -> bytes_at rsegs v (pa + Z.of_nat (length arg) + 1) sl ->
    bytes_at rsegs v pa (arg ++ Z_to_bv 8 0 :: sl).
  Proof.
    intros v pa arg sl H1 H2. replace (arg ++ Z_to_bv 8 0 :: sl) with ((arg ++ [Z_to_bv 8 0]) ++ sl) by (rewrite <- app_assoc; reflexivity).
    apply (proj2 (bytes_at_app rsegs v pa _ _)). split; [exact H1|]. rewrite length_app. cbn [length].
    replace (pa + Z.of_nat (length arg + 1)) with (pa + Z.of_nat (length arg) + 1) by lia. exact H2.
  Qed.
  Lemma aa_s0k : forall v, args_at v -> exists sl, length sl = 16%nat /\ bytes_at rsegs v p0a (nth 0 argv [] ++ Z_to_bv 8 0 :: sl).
  Proof.
    intros v AR. (first [ pose proof ((aa_k0 _ AR)) as dR_8; dex1 dR_8 as sl; destruct dR_8 as [L B] | pose proof ((aa_k0 _ AR)) as dR_8; dand3 dR_8 as sl L B | destruct (aa_k0 _ AR) as (sl & L & B) ]). exists sl. split; [exact L|]. apply arg_slack; [exact (aa_s0 _ AR)|].
    unfold e_L0 in B. exact B.
  Qed.
  Lemma aa_s1k : forall v, args_at v -> 2 <= argc -> exists sl, length sl = 16%nat /\ bytes_at rsegs v p1a (nth 1 argv [] ++ Z_to_bv 8 0 :: sl).
  Proof.
    intros v AR H2. (first [ pose proof ((aa_k1 _ AR H2)) as dR_9; dex1 dR_9 as sl; destruct dR_9 as [L B] | pose proof ((aa_k1 _ AR H2)) as dR_9; dand3 dR_9 as sl L B | destruct (aa_k1 _ AR H2) as (sl & L & B) ]). exists sl. split; [exact L|]. apply arg_slack; [exact (aa_s1 _ AR H2)|].
    unfold e_L1 in B. exact B.
  Qed.

  (* [comment removed for export] *)
  Lemma args_present : forall A m md, ainv A m md -> args_at (aview A m) ->
    forall a, in_args a -> aview A m (wz a) <> None.
  Proof.
    intros A m md AINV AR a Ha. destruct AR as [P0 P1 S0 S1 K0 K1 B0 B1 U]. (first [ pose proof (U) as dR_10; dand4 dR_10 as U1 U2 U3 U4 | pose proof U as (U1 & U2 & U3 & U4) ]). unfold sp_window_lo in U1.
    pose proof (layout_facts (L:=LPA)) as LO. cbn [cl_image_lo cl_rw_lo cl_image_hi cl_errno LPA] in LO.
    assert (GEN : forall b bs i, bytes_at rsegs (aview A m) b bs -> 0 <= i < Z.of_nat (length bs) -> 0x60a000 <= b ->
                   aview A m (wz (b + i)) <> None).
    { (intros b bs i; (first [ intro dR_25; dand3 dR_25 as H0 H1 H | intros (H0 & H1 & H) ]); intros Hi Hb). specialize (H (Z.to_nat i) ltac:(lia)). rewrite Z2Nat.id in H by lia.
      unfold mrd, wa in H. destruct (aview A m (wz (b + i))) eqn:E; [discriminate|].
      rewrite (as_seg_rom_outside LPA) in H; [| unfold in_image; cbn; rewrite unsigned_lit by lia; lia].
      symmetry in H. apply nth_error_None in H. lia. }
    destruct Ha as [R|[[A2 R]|[R|[H2 R]]]].
    - replace a with (usp + 8 + (a - (usp + 8))) by lia. apply (GEN _ _ _ P0); [rewrite length_le8; lia| lia].
    - replace a with (usp + 16 + (a - (usp + 16))) by lia. apply (GEN _ _ _ (P1 A2)); [rewrite length_le8; lia| lia].
    - destruct (classic (a < p0a + e_L0 argv + 1)) as [LT|GE].
      + replace a with (p0a + (a - p0a)) by lia. apply (GEN _ _ _ S0); [rewrite length_app; cbn [length]; unfold e_L0 in R, LT; lia| eun2; lia].
      + (first [ dex1 K0 as sl; destruct K0 as [L B] | dand3 K0 as sl L B | destruct K0 as (sl & L & B) ]). replace a with (p0a + e_L0 argv + 1 + (a - (p0a + e_L0 argv + 1))) by lia.
        apply (GEN _ _ _ B); [rewrite L; lia| eun2; lia].
    - destruct (classic (a < p1a + e_L1 argv + 1)) as [LT|GE].
      + replace a with (p1a + (a - p1a)) by lia. apply (GEN _ _ _ (S1 H2)); [rewrite length_app; cbn [length]; unfold e_L1 in R, LT; lia| specialize (B1 H2); eun2; lia].
      + (first [ pose proof ((K1 H2)) as dR_12; dex1 dR_12 as sl; destruct dR_12 as [L B] | pose proof ((K1 H2)) as dR_12; dand3 dR_12 as sl L B | destruct (K1 H2) as (sl & L & B) ]). replace a with (p1a + e_L1 argv + 1 + (a - (p1a + e_L1 argv + 1))) by lia.
        apply (GEN _ _ _ B); [rewrite L; lia| specialize (B1 H2); eun2; lia].
  Qed.

  (* [comment removed for export] *)
  Definition in_stksh (a : Z) : Prop := STKSH_LO <= a < STKSH_HI.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma agree_of_munch : forall (P : Z -> Prop) W v v',
    munch W v v' -> (forall a, P a -> 0 <= a < 2^64 /\ outside W a) -> agree_on P v v'.
  Proof.
    intros P W v v' MU HP a Ha. destruct (HP a Ha) as [Ra OUT].
    apply (MU (wz a)). rewrite unsigned_lit by lia. exact OUT.
  Qed.

  (* [comment removed for export] *)
  Lemma agree_of_cframe : forall A A' m md v' (sp win : Z) (V N : Z -> Prop) (P : Z -> Prop),
    ainv A m md ->
    cframe LPA (owned A) (owned A') sp win V N (aview A m) v' ->
    (forall a, P a -> 0 <= a < 2^64 /\ ~ owned A a /\ (aview A m (wz a) <> None \/ in_image LPA a)
                      /\ ~ (sp - win <= a < sp) /\ ~ (0x5e8334 <= a < 0x5e8334 + 4) /\ ~ V a) ->
    agree_on P (aview A m) v'.
  Proof.
    (intros A A' m md v' sp win V N P AINV; (first [ intro dR_26; dand3 dR_26 as C1 C2 C3 | intros (C1 & C2 & C3) ]); intros HP a Ha).
    (first [ pose proof ((HP a Ha)) as dR_13; dand6 dR_13 as Ra NO VIS NW NE NV | destruct (HP a Ha) as (Ra & NO & VIS & NW & NE & NV) ]).
    exact (proj1 (C1 a Ra NO VIS NW NE NV)).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition heapish (V : Z -> Prop) : Prop :=
    forall a, V a ->
         (4096 <= a < 0x10000) \/ (0x60a000 <= a < kLowShadowMapBeg)
      \/ (sh 4096 <= a < sh 0x10000) \/ (sh 0x60a000 <= a < sh kLowShadowMapBeg)
      \/ (kHighMemBeg <= a < alloc_ceiling) \/ (sh kHighMemBeg <= a < sh alloc_ceiling) \/ HBSS a.

  Lemma cc_ranges_cframe_ok : forall A m md (sp win : Z) V,
    ainv A m md -> alloc_ceiling <= sp - win -> heapish V ->
    forall a, in_ranges (CC_RANGES ++ GOT_RANGES) a -> 0 <= a < 2^64 /\ ~ owned A a /\ (aview A m (wz a) <> None \/ in_image LPA a)
                      /\ ~ (sp - win <= a < sp) /\ ~ (0x5e8334 <= a < 0x5e8334 + 4) /\ ~ V a.
  Proof.
    intros A m md sp win V AINV WLO HV a Ha.
    (first [ pose proof ((cc_ranges_where a Ha)) as dR_14; dand5 dR_14 as R NS NE NB NST | pose proof (cc_ranges_where a Ha) as (R & NS & NE & NB & NST) ]).
    pose proof (layout_facts (L:=LPA)) as LO. cbn [cl_image_lo cl_rw_lo cl_image_hi cl_errno LPA] in LO.
    split; [lia|]. split.
    { intros O. destruct (as_owned_where LPA A m md a AINV O) as [ST|[_ NI]]; [exact (NS ST)|]. apply NI. unfold in_image. cbn. lia. }
    split; [right; unfold in_image; cbn; lia|]. split; [lia|]. split; [exact NE|].
    intros Va. heapish_elim HV a Va; heapish_case.
  Qed.

  Lemma args_cframe_ok : forall A m md (sp win : Z) V,
    ainv A m md -> sp <= usp -> heapish V -> args_at (aview A m) ->
    forall a, in_args a -> 0 <= a < 2^64 /\ ~ owned A a /\ (aview A m (wz a) <> None \/ in_image LPA a)
                      /\ ~ (sp - win <= a < sp) /\ ~ (0x5e8334 <= a < 0x5e8334 + 4) /\ ~ V a.
  Proof.
    intros A m md sp win V AINV SPU HV AR a Ha. pose proof (args_present A m md AINV AR a Ha) as VIS.
    (first [ pose proof ((aa_usp _ AR)) as dR_15; dand4 dR_15 as U1 U2 U3 U4 | pose proof (aa_usp _ AR) as (U1 & U2 & U3 & U4) ]). pose proof (aa_b0 _ AR) as B0. pose proof (aa_b1 _ AR) as B1. unfold sp_window_lo in U1.
    assert (R : usp <= a < 2^47).
    { destruct Ha as [R|[[_ R]|[R|[H2 R]]]]; [eun2; lia| eun2; lia| eun2; lia| specialize (B1 H2); eun2; lia]. }
    pose proof (layout_facts (L:=LPA)) as LO. cbn [cl_image_lo cl_rw_lo cl_image_hi cl_errno LPA] in LO.
    split; [lia|]. split.
    { intros O. destruct (as_owned_where LPA A m md a AINV O) as [ST|[[_ LT] _]]; [apply (as_static_where LPA) in ST; cbn in ST; lia| lia]. }
    split; [left; exact VIS|]. split; [lia|]. split; [lia|].
    intros Va. heapish_elim HV a Va; heapish_case.
  Qed.

  Lemma stksh_cframe_ok : forall A m md (sp win : Z) V,
    ainv A m md -> alloc_ceiling <= sp - win -> heapish V ->
    (forall a, in_stksh a -> aview A m (wz a) = Some (Z_to_bv 8 0)) ->
    forall a, in_stksh a -> 0 <= a < 2^64 /\ ~ owned A a /\ (aview A m (wz a) <> None \/ in_image LPA a)
                       /\ ~ (sp - win <= a < sp) /\ ~ (0x5e8334 <= a < 0x5e8334 + 4) /\ ~ V a.
  Proof.
    intros A m md sp win V AINV WLO HV SH a Ha. pose proof (SH a Ha) as Z0. unfold in_stksh, STKSH_LO, STKSH_HI, sh, kShadowOffset in Ha; (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv).
    pose proof (layout_facts (L:=LPA)) as LO.
    split; [lia|]. split.
    { apply (as_owned_not_stack_shadow LPA A m md a AINV). unfold sh, kShadowOffset, kHighMemBeg. (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv). Z.div_mod_to_equations; lia. }
    split; [left; rewrite Z0; discriminate|]. split; [lia|]. split; [lia|].
    intros Va. heapish_elim HV a Va; heapish_case.
  Qed.

  (* [comment removed for export] *)
  Lemma stack_cells_cframe_ok : forall A m md (sp win : Z) V a cs,
    ainv A m md -> heapish V -> rw_cells rsegs (aview A m) a cs ->
    alloc_ceiling <= a -> sp <= a -> a + Z.of_nat (cells_size cs) <= 2^47 ->
    forall x, a <= x < a + Z.of_nat (cells_size cs) ->
      0 <= x < 2^64 /\ ~ owned A x /\ (aview A m (wz x) <> None \/ in_image LPA x)
      /\ ~ (sp - win <= x < sp) /\ ~ (0x5e8334 <= x < 0x5e8334 + 4) /\ ~ V x.
  Proof.
    intros A m md sp win V a cs AINV HV [[WF B] _] CE SA HI x Hx.
    pose proof (layout_facts (L:=LPA)) as LO. cbn [cl_image_lo cl_rw_lo cl_image_hi cl_errno LPA] in LO. (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv).
    split; [lia|]. split.
    { intros O. destruct (as_owned_where LPA A m md x AINV O) as [ST|[[_ LT] _]]; [apply (as_static_where LPA) in ST; cbn in ST; lia| (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv); lia]. }
    split.
    { left. (first [ dand3 B as _ _ B | destruct B as (_ & _ & B) ]). rewrite (cells_bytes_length cs WF) in B. specialize (B (Z.to_nat (x - a)) ltac:(lia)).
      rewrite Z2Nat.id in B by lia. replace (a + (x - a)) with x in B by lia.
      rewrite pa_mrd_overlay in B by (rewrite unsigned_lit by lia; lia). unfold wa in B. rewrite B.
      destruct (nth_error (cells_bytes cs) (Z.to_nat (x - a))) eqn:E; [discriminate|]. apply nth_error_None in E. rewrite (cells_bytes_length cs WF) in E. lia. }
    split; [lia|]. split; [lia|].
    intros Vx. heapish_elim HV x Vx; heapish_case.
  Qed.

  Lemma rw_cells_cframe : forall A A' m md v' (sp win : Z) (V N : Z -> Prop) a cs,
    ainv A m md -> cframe LPA (owned A) (owned A') sp win V N (aview A m) v' -> heapish V ->
    rw_cells rsegs (aview A m) a cs -> alloc_ceiling <= a -> sp <= a -> a + Z.of_nat (cells_size cs) <= 2^47 ->
    rw_cells rsegs v' a cs.
  Proof.
    intros A A' m md v' sp win V N a cs AINV CF HV RW CE SA HI.
    refine (rw_cells_agree rsegs _ _ a cs _ RW). intros i Hi.
    exact (agree_of_cframe A A' m md v' sp win V N (fun x => a <= x < a + Z.of_nat (cells_size cs)) AINV CF
             (stack_cells_cframe_ok A m md sp win V a cs AINV HV RW CE SA HI) (a + i) ltac:(cbv beta; lia)).
  Qed.

  (* [comment removed for export] *)
  Lemma blk_cells_cframe_ok : forall A m md (sp win : Z) (V : Z -> Prop) p n a cs,
    ainv A m md -> a_live A p = Some n -> rw_cells rsegs (aview A m) a cs ->
    p <= a -> a + Z.of_nat (cells_size cs) <= p + n -> alloc_ceiling <= sp - win ->
    (forall x, p <= x < p + n -> ~ V x) ->
    forall x, a <= x < a + Z.of_nat (cells_size cs) ->
      0 <= x < 2^64 /\ ~ owned A x /\ (aview A m (wz x) <> None \/ in_image LPA x)
      /\ ~ (sp - win <= x < sp) /\ ~ (0x5e8334 <= x < 0x5e8334 + 4) /\ ~ V x.
  Proof.
    intros A m md sp win V p n a cs AINV LV RW PA AN WLO NV x Hx.
    (first [ pose proof ((as_live_ok LPA A m md p n AINV LV)) as dR_17; dand8 dR_17 as N0 AL LO HI NI MP NO _ | destruct (as_live_ok LPA A m md p n AINV LV) as (N0 & AL & LO & HI & NI & MP & NO & _) ]).
    unfold app_range, app_lo, app_hi, kLowAppEnd, kLowShadowMapBeg, kHighMemBeg in LO. cbn [cl_image_lo cl_image_hi LPA] in LO.
    (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv).
    split; [lia|]. split.
    { replace x with (p + (x - p)) by lia. apply NO. lia. }
    split.
    { left. replace x with (p + (x - p)) by lia. apply MP. lia. }
    split; [lia|]. split; [lia|]. apply NV. lia.
  Qed.

  Lemma rw_cells_blk_cframe : forall A A' m md v' (sp win : Z) (V N : Z -> Prop) p n a cs,
    ainv A m md -> cframe LPA (owned A) (owned A') sp win V N (aview A m) v' ->
    a_live A p = Some n -> rw_cells rsegs (aview A m) a cs ->
    p <= a -> a + Z.of_nat (cells_size cs) <= p + n -> alloc_ceiling <= sp - win ->
    (forall x, p <= x < p + n -> ~ V x) ->
    rw_cells rsegs v' a cs.
  Proof.
    intros A A' m md v' sp win V N p n a cs AINV CF LV RW PA AN WLO NV.
    refine (rw_cells_agree rsegs _ _ a cs _ RW). intros i Hi.
    exact (agree_of_cframe A A' m md v' sp win V N (fun x => a <= x < a + Z.of_nat (cells_size cs)) AINV CF
             (blk_cells_cframe_ok A m md sp win V p n a cs AINV LV RW PA AN WLO NV) (a + i) ltac:(cbv beta; lia)).
  Qed.

  (* [comment removed for export] *)
  Lemma stksh_bytes : forall v, (forall a, in_stksh a -> v (wz a) = Some (Z_to_bv 8 0)) ->
    bytes_at rsegs v (sh alloc_ceiling) (zeros (Z.to_nat ((2^47 - alloc_ceiling) / 8))).
  Proof.
    intros v SH. (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv). unfold zeros.
    pose proof alloc_ceiling_mod16 as M16.
    assert (E1 : sh alloc_ceiling = STKSH_LO) by reflexivity.
    assert (E2 : (2^47 - alloc_ceiling) / 8 = STKSH_HI - STKSH_LO).
    { unfold STKSH_HI, STKSH_LO, sh, kShadowOffset. Z.div_mod_to_equations. lia. }
    rewrite E1, E2. split; [unfold STKSH_LO, sh, kShadowOffset; Z.div_mod_to_equations; lia|]. rewrite repeat_length.
    split; [unfold STKSH_LO, STKSH_HI, sh, kShadowOffset; Z.div_mod_to_equations; lia|].
    intros i Hi. rewrite nth_error_repeat by exact Hi. unfold mrd, wa. rewrite SH; [reflexivity|].
    unfold in_stksh, STKSH_LO, STKSH_HI in *. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition stack_only (W : list (Z * Z)) : Prop :=
    forall a, ~ outside W a -> STK_LO usp <= a < usp \/ 0x5e8334 <= a < 0x5e8334 + 4 \/ kHighMemBeg <= a < alloc_ceiling
                               \/ 4096 <= a < 0x10000 \/ 0x60a000 <= a < kLowShadowMapBeg \/ 0x5d7a10 <= a < 0x5e7a10.

  Lemma stack_only_cons_heap : forall lo hi W, app_range LPA lo (hi - lo) -> stack_only W -> stack_only ((lo, hi) :: W).
  Proof.
    intros lo hi W H12 SO a Ha. cbn [outside] in Ha.
    unfold app_range, app_lo, app_hi, kLowAppEnd in H12. cbn [cl_image_lo cl_image_hi LPA] in H12.
    destruct (classic (outside W a)) as [X|X]; [| apply SO; exact X].
    destruct (classic (lo <= a < hi)) as [Y|Y]; [lia|]. exfalso. apply Ha. split; assumption.
  Qed.

  Lemma stack_only_cons : forall lo hi W, STK_LO usp <= lo -> hi <= usp -> stack_only W -> stack_only ((lo, hi) :: W).
  Proof.
    intros lo hi W H1 H2 SO a Ha. cbn [outside] in Ha.
    destruct (classic (outside W a)) as [X|X]; [| apply SO; exact X].
    destruct (classic (lo <= a < hi)) as [Y|Y]; [lia|]. exfalso. apply Ha. split; assumption.
  Qed.
  Lemma stack_only_cons_errno : forall W, stack_only W -> stack_only ((0x5e8334, 0x5e8334 + 4) :: W).
  Proof.
    intros W SO a Ha. cbn [outside] in Ha.
    destruct (classic (outside W a)) as [X|X]; [| apply SO; exact X].
    destruct (classic (0x5e8334 <= a < 0x5e8334 + 4)) as [Y|Y]; [lia|]. exfalso. apply Ha. split; assumption.
  Qed.
  Lemma stack_only_cons_stage : forall hi W, hi <= 0x5e7a10 -> stack_only W -> stack_only ((0x5d7a10, hi) :: W).
  Proof.
    intros hi W HI SO a Ha. cbn [outside] in Ha.
    destruct (classic (outside W a)) as [X|X]; [| apply SO; exact X].
    destruct (classic (0x5d7a10 <= a < hi)) as [Y|Y]; [lia|]. exfalso. apply Ha. split; assumption.
  Qed.
  Lemma stack_only_nil : stack_only [].
  Proof. intros a Ha. exfalso. apply Ha. exact I. Qed.

  Lemma agree_stack_cc : forall W v v', munch W v v' -> stack_only W ->
    sp_window_lo <= usp -> agree_on (in_ranges (CC_RANGES ++ GOT_RANGES)) v v'.
  Proof.
    intros W v v' MU SO U1 a Ha. (first [ pose proof ((cc_ranges_where a Ha)) as dR_18; dand5 dR_18 as R _ NE _ NST | pose proof (cc_ranges_where a Ha) as (R & _ & NE & _ & NST) ]). unfold sp_window_lo in U1.
    apply (MU (wz a)). rewrite unsigned_lit by lia. destruct (classic (outside W (bv_unsigned (wz a)))) as [X|X]; [rewrite unsigned_lit in X by lia; exact X|].
    exfalso. rewrite unsigned_lit in X by lia. pose proof (SO a X). unfold STK_LO, kHighMemBeg, kLowShadowMapBeg in *. lia.
  Qed.
  Lemma agree_stack_args : forall W v v', munch W v v' -> stack_only W ->
    sp_window_lo <= usp -> usp + span <= 2^47 -> args_at v -> agree_on in_args v v'.
  Proof.
    intros W v v' MU SO U1 U2 AR a Ha. pose proof (aa_b0 _ AR) as B0. pose proof (aa_b1 _ AR) as B1. unfold sp_window_lo in *.
    assert (R : usp <= a < 2^47).
    { destruct Ha as [R|[[_ R]|[R|[H2 R]]]]; [eun2; lia| eun2; lia| eun2; lia| specialize (B1 H2); eun2; lia]. }
    apply (MU (wz a)). rewrite unsigned_lit by lia. destruct (classic (outside W a)) as [X|X]; [exact X|].
    exfalso. pose proof (SO a X). (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv). unfold STK_LO, kHighMemBeg, kLowShadowMapBeg in *. lia.
  Qed.
  Lemma agree_stack_stksh : forall W v v', munch W v v' -> stack_only W ->
    sp_window_lo <= usp -> agree_on in_stksh v v'.
  Proof.
    intros W v v' MU SO U1 a Ha. unfold in_stksh, STKSH_LO, STKSH_HI, sp_window_lo, sh, kShadowOffset in *.
    (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv).
    apply (MU (wz a)). rewrite unsigned_lit by (Z.div_mod_to_equations; lia). destruct (classic (outside W a)) as [X|X]; [exact X|].
    exfalso. pose proof (SO a X). unfold STK_LO, kHighMemBeg, kLowShadowMapBeg in *. Z.div_mod_to_equations; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma bundle_stack : forall W v v' tid sof ini, munch W v v' -> stack_only W ->
    sp_window_lo <= usp -> usp + span <= 2^47 ->
    ccells v tid sof ini -> args_at v -> (forall a, in_stksh a -> v (wz a) = Some (Z_to_bv 8 0)) ->
    ccells v' tid sof ini /\ args_at v' /\ (forall a, in_stksh a -> v' (wz a) = Some (Z_to_bv 8 0))
    /\ ro_cells rsegs v' SSP_GOT [C8 (wz SSP_GUARD)].
  Proof.
    intros W v v' tid sof ini MU SO U1 U2 CC AR SH.
    pose proof (agree_stack_cc W v v' MU SO U1) as AG.
    split; [exact (ccells_agree v v' tid sof ini (agree_app_l _ _ _ _ AG) CC)|].
    split; [exact (args_at_agree v v' (agree_stack_args W v v' MU SO U1 U2 AR) AR)|].
    split; [intros a Ha; rewrite (agree_stack_stksh W v v' MU SO U1 a Ha); apply SH; exact Ha|].
    apply (sspgot_agree v v' (agree_app_r _ _ _ _ AG)). exact (mc_sspgot _ _ (proj1 CC)).
  Qed.

  (* [comment removed for export] *)
  Lemma bundle_stack_x : forall W v v' tid sof ini cb, munch W v v' -> stack_only W ->
    sp_window_lo <= usp -> usp + span <= 2^47 ->
    ccells_x v tid sof ini cb -> args_at v -> (forall a, in_stksh a -> v (wz a) = Some (Z_to_bv 8 0)) ->
    ccells_x v' tid sof ini cb /\ args_at v' /\ (forall a, in_stksh a -> v' (wz a) = Some (Z_to_bv 8 0))
    /\ ro_cells rsegs v' SSP_GOT [C8 (wz SSP_GUARD)].
  Proof.
    intros W v v' tid sof ini cb MU SO U1 U2 CC AR SH.
    pose proof (agree_stack_cc W v v' MU SO U1) as AG.
    split; [exact (ccells_x_agree v v' tid sof ini cb (agree_app_l _ _ _ _ AG) CC)|].
    split; [exact (args_at_agree v v' (agree_stack_args W v v' MU SO U1 U2 AR) AR)|].
    split; [intros a Ha; rewrite (agree_stack_stksh W v v' MU SO U1 a Ha); apply SH; exact Ha|].
    apply (sspgot_agree v v' (agree_app_r _ _ _ _ AG)). exact (mc_sspgot _ _ (proj1 CC)).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma bundle_cframe : forall A A' m md v' (sp win : Z) (V N : Z -> Prop) tid sof ini,
    ainv A m md -> cframe LPA (owned A) (owned A') sp win V N (aview A m) v' ->
    alloc_ceiling <= sp - win -> sp <= usp -> heapish V ->
    ccells (aview A m) tid sof ini -> args_at (aview A m) ->
    (forall a, in_stksh a -> aview A m (wz a) = Some (Z_to_bv 8 0)) ->
    ccells v' tid sof ini /\ args_at v' /\ (forall a, in_stksh a -> v' (wz a) = Some (Z_to_bv 8 0))
    /\ ro_cells rsegs v' SSP_GOT [C8 (wz SSP_GUARD)].
  Proof.
    intros A A' m md v' sp win V N tid sof ini AINV CF WLO SPU HV CC AR SH.
    pose proof (agree_of_cframe A A' m md v' sp win V N _ AINV CF (cc_ranges_cframe_ok A m md sp win V AINV WLO HV)) as AG.
    split; [exact (ccells_agree _ v' tid sof ini (agree_app_l _ _ _ _ AG) CC)|].
    split; [exact (args_at_agree _ v' (agree_of_cframe A A' m md v' sp win V N _ AINV CF (args_cframe_ok A m md sp win V AINV SPU HV AR)) AR)|].
    split.
    - intros a Ha. rewrite (agree_of_cframe A A' m md v' sp win V N _ AINV CF (stksh_cframe_ok A m md sp win V AINV WLO HV SH) a Ha). apply SH. exact Ha.
    - apply (sspgot_agree _ v' (agree_app_r _ _ _ _ AG)). exact (mc_sspgot _ _ (proj1 CC)).
  Qed.

  (* [comment removed for export] *)
  Lemma bundle_cframe_x : forall A A' m md v' (sp win : Z) (V N : Z -> Prop) tid sof ini cb,
    ainv A m md -> cframe LPA (owned A) (owned A') sp win V N (aview A m) v' ->
    alloc_ceiling <= sp - win -> sp <= usp -> heapish V ->
    ccells_x (aview A m) tid sof ini cb -> args_at (aview A m) ->
    (forall a, in_stksh a -> aview A m (wz a) = Some (Z_to_bv 8 0)) ->
    ccells_x v' tid sof ini cb /\ args_at v' /\ (forall a, in_stksh a -> v' (wz a) = Some (Z_to_bv 8 0))
    /\ ro_cells rsegs v' SSP_GOT [C8 (wz SSP_GUARD)].
  Proof.
    intros A A' m md v' sp win V N tid sof ini cb AINV CF WLO SPU HV CC AR SH.
    pose proof (agree_of_cframe A A' m md v' sp win V N _ AINV CF (cc_ranges_cframe_ok A m md sp win V AINV WLO HV)) as AG.
    split; [exact (ccells_x_agree _ v' tid sof ini cb (agree_app_l _ _ _ _ AG) CC)|].
    split; [exact (args_at_agree _ v' (agree_of_cframe A A' m md v' sp win V N _ AINV CF (args_cframe_ok A m md sp win V AINV SPU HV AR)) AR)|].
    split.
    - intros a Ha. rewrite (agree_of_cframe A A' m md v' sp win V N _ AINV CF (stksh_cframe_ok A m md sp win V AINV WLO HV SH) a Ha). apply SH. exact Ha.
    - apply (sspgot_agree _ v' (agree_app_r _ _ _ _ AG)). exact (mc_sspgot _ _ (proj1 CC)).
  Qed.

  Lemma heapish_nowhere : heapish nowhere.
  Proof. intros a H. destruct H. Qed.
  (* [comment removed for export] *)
  Lemma heapish_newblk : forall A m md p n, ainv A m md -> a_live A p = Some n -> heapish (newblk p n).
  Proof.
    intros A m md p n AINV HL a Ha.
    (first [ pose proof ((as_live_ok LPA A m md p n AINV HL)) as dR_19; dand5 dR_19 as N0 AL PLO PHI _ | destruct (as_live_ok LPA A m md p n AINV HL) as (N0 & AL & PLO & PHI & _) ]).
    unfold newblk, blk in Ha.
    pose proof (layout_facts (L:=LPA)) as LOF. cbn [cl_image_lo cl_rw_lo cl_image_hi cl_errno LPA] in LOF.
    (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv).
    unfold app_range, app_lo, app_hi, kLowAppEnd in PLO. cbn [cl_image_lo cl_image_hi LPA] in PLO.
    pose proof alloc_ceiling_mod16 as M16.
    unfold sh, kShadowOffset, kHighMemBeg, kLowShadowMapBeg in *.
    destruct Ha as [[NZ B]|[NZ S]]; destruct PLO as [(P4 & _ & PE & PI)|(PH & _ & PC)].
    - destruct PI as [PI|PI]; [left; lia | right; left; lia].
    - do 4 right. left. lia.
    - destruct PI as [PI|PI]; [right; right; left | right; right; right; left]; Z.div_mod_to_equations; lia.
    - do 5 right. left. Z.div_mod_to_equations; lia.
  Qed.
  (* [comment removed for export] *)
End S.

(* [comment removed for export] *)
Ltac heapish_elim HV a Va :=
  let X := fresh "X" in destruct (HV a Va) as [X|[X|[X|[X|[X|[X|X]]]]]]; revert X.
Ltac heapish_case :=
  let X := fresh "X" in intros X;
  first [ unfold HBSS in X; lia
        | lazymatch goal with NB : ~ HBSS _ |- _ => exact (NB X) end
        | unfold HBSS, sh, kShadowOffset, kHighMemBeg, kLowShadowMapBeg in *;
          (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv); Z.div_mod_to_equations; lia ].

(* [comment removed for export] *)
Ltac ranges_outside :=
  intros ro_a (ro_lo & ro_hi & ro_in & ro_r);
  unfold CC_RANGES in ro_in; unfold MC_RANGES, STDERR_RANGES, STDOUT_RANGES, TR_RANGES, GOT_RANGES in ro_in;
  unfold SSP_GOT, STDERR_F, STDOUT_F, STDIN_F, STDERR_CELL, TR_INITIALIZED, TR_INCB, TR_EMPTY, TID_CELL, SSP_GUARD, ATEXIT, EXIT_LOCK,
         NEED_LOCKS, OFL_HEAD, STDERR_BUFP, STDOUT_BUF in *;
  unfold FPRINTF_ICPT_STACK, FWRITE_ICPT_STACK, VPRINTF_ICPT_STACK, OPEN_STACK, CLOSE_STACK, READ_ICPT_STACK in *;
  cbn [In Z.add app] in ro_in; cbn [outside];
  repeat (destruct ro_in as [ro_e|ro_in]; [injection ro_e as <- <-; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try exact I; lia|]); destruct ro_in.

