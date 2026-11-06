(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From OSSVerify.Proofs.openssl.ct.lib.Lib Require Import ITree Nodes Decode Ceiling Image.
From OSSVerify.Proofs.openssl.ct.lib Require Import TopLevel.
From OSSVerify.Proofs.openssl.ct.lib.Spec Require Import Prelim Monad MSafe STree Malloc Stdio HexModel Target Driver Prog
  KInv KStep KStepC ModelInv LB_Logic LB_Inv LB_Raw LB_Init LB_Alloc LB_PDriver LB_PTarget Unforced
  LibProg NLogic LibSafe LibOps ProgG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Section ProgGSafe.
Context {CE__ : Ceiling}.
Context {LM : LibModel}.
Variable P : Z -> Z.
Variable T : list Z.
Variable ok : list (bptr * Z) -> Z -> Prop.
Variable linv : LS -> list (bptr * Z) -> Prop.
Hypothesis HP0 : forall c, 0 <= P c.
Hypothesis HcT : capsT_ok P T.
Hypothesis HOK : ok_bridge P T ok.
Hypothesis H_init : lwf (okT T) lib_init [] (fun ls Li => linv ls [] /\ subms (map snd Li) T).
Hypothesis H_one : forall ls d X, linv ls X -> zlength d <= MAX_INPUT ->
  lwf ok (lib_one ls d) X (fun r X' => linv (fst r) X').
Hypothesis H_rc : forall ls d, lleaves (lib_one ls d) (fun r => snd r = 0).

Local Notation QIP := (fun X => QI X P).
Local Notation OQP := (OQ Gso P).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma PHI_le : PHI P <= LBUDGET.
Proof. exact (PHI_le_T P T HcT). Qed.

Lemma szle_drv1 : forall (b : bptr) cap, 65536 <= cap <= MAX_INPUT -> szle (MAX_INPUT + 1) [(b, cap)].
Proof. intros b cap H. constructor; [cbn [snd]; lia| constructor]. Qed.

Lemma szle_drv2 : forall (c b : bptr) plen cap, 0 <= plen <= MAX_INPUT -> 65536 <= cap <= MAX_INPUT ->
  szle (MAX_INPUT + 1) [(c, plen); (b, cap)].
Proof. intros. constructor; [cbn [snd]; lia| apply szle_drv1; assumption]. Qed.

Lemma mal_ok_first : mal_okP P [] 65536.
Proof.
  apply (libfit_drv P [] [] 65536 (libfit_nilT P T HcT)); [cbn; lia| constructor| unfold MAX_INPUT; lia].
Qed.

Lemma mal_ok_grow : forall (b : bptr) k, (k <= 9)%nat ->
  mal_okP P [(b, 65536 * 2 ^ Z.of_nat k)] (65536 * 2 ^ Z.of_nat k * 2).
Proof.
  intros b k Hk. assert (Hp1 : 0 < 2 ^ Z.of_nat k) by (apply Z.pow_pos_nonneg; lia).
  assert (Hp2 : 2 ^ Z.of_nat k <= 2 ^ 9) by (apply Z.pow_le_mono_r; lia). change (2 ^ 9) with 512 in Hp2.
  apply (libfit_drv P [] [(b, 65536 * 2 ^ Z.of_nat k)] _ (libfit_nilT P T HcT)); [cbn; lia| | unfold MAX_INPUT; lia].
  constructor; [cbn [snd]; unfold MAX_INPUT; lia| constructor].
Qed.

Lemma zlength_nonneg' {A} (l : list A) : 0 <= zlength l.
Proof. unfold zlength. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma QIP_minv : forall X s mo, QI X P s mo -> minv mo /\ m_halted mo = None.
Proof. intros X s mo H. exact (QI_minv _ _ _ _ H). Qed.
Lemma QIP_fds : forall X s mo mo', QI X P s mo -> m_vmmaps mo' = m_vmmaps mo -> minv mo' -> m_halted mo' = None -> QI X P s mo'.
Proof. intros X s mo mo' H. exact (QI_fds _ _ _ _ _ H). Qed.
Lemma QIP_live : forall X s mo, QI X P s mo -> live mo <= LBUDGET.
Proof. intros X s mo H. exact (QI_live _ _ _ _ H). Qed.
Lemma QIP_set_so : forall X s mo v, QI X P s mo -> QI X P (set_so_ps v s) mo.
Proof. intros X s mo v H. apply QI_set_so. exact H. Qed.
Lemma QIP_perm : forall X Y s mo, Permutation X Y -> QI X P s mo -> QI Y P s mo.
Proof. intros X Y s mo HP. apply QI_perm. exact HP. Qed.

Lemma writev_LP X fd bufs (dec : resp -> option Z) : mspecL LBUDGET (QI X P) (msys (NWritev fd bufs) dec) (fun _ => QI X P).
Proof. apply (writev_L LBUDGET (QI X P) (QIP_live X)). Qed.
Lemma ioctl_LP X fd req : mspecL LBUDGET (QI X P) (msys (NIoctl fd req) dec_ioctl) (fun _ => QI X P).
Proof. apply (ioctl_L LBUDGET (QI X P) (QIP_live X)). Qed.
Lemma out_LP : forall X ps, mspecL LBUDGET (QI X P) (stdout_vprintf ps_so set_so_ps ps) (fun _ => QI X P).
Proof. intros X ps. apply (stdout_vprintf_L ps_so set_so_ps LBUDGET (QI X P) (QIP_set_so X) (writev_LP X) (ioctl_LP X)). Qed.
Lemma diag_LP : forall X d, mspecL LBUDGET (QI X P) (io_diag io d) (fun _ => QI X P).
Proof. intros X d. unfold io, io_S. cbn [io_diag]. apply (s_diag_L LBUDGET (QI X P) (writev_LP X)). Qed.

Lemma raw_malloc_LP : forall X n, 0 <= n ->
  mspecL LBUDGET (fun s mo => QI X P s mo /\ mal_okP P X n) (raw_malloc n)
         (fun r s mo => match r with Some p => QI ((p, n) :: X) P s mo /\ n < 2^63 | None => QI X P s mo end).
Proof. intros X n Hn. exact (raw_malloc_LQ X P n Hn). Qed.
Lemma raw_free_LP : forall X p n, mspecL LBUDGET (QI ((p, n) :: X) P) (raw_free p) (fun _ => QI X P).
Proof. intros X p n. exact (raw_free_LQ X P p n). Qed.

(* [comment removed for export] *)
Definition ownL (X : list (bptr * Z)) : assn PState := fun s mo => exists L, QI (L ++ X) P s mo.

Lemma exitio_ownL : forall X, mspecL LBUDGET (ownL X) (io_exit io) (fun _ => ownL X).
Proof.
  intros X. unfold io, io_S. cbn [io_exit]. unfold ownL. apply mspecL_exI. intros L.
  eapply mspecL_post; [apply (stdout_exit_flush_L ps_so set_so_ps LBUDGET (QI (L ++ X) P) (QIP_set_so _) (writev_LP _) (ioctl_LP _))|].
  intros u s mo H. exists L. exact H.
Qed.

(* [comment removed for export] *)

Lemma run_callsG_L : forall D Li d, (length D <= 4)%nat -> szle (MAX_INPUT + 1) D -> subms (map snd Li) T ->
  zlength d <= MAX_INPUT ->
  forall n ls rc Xb, linv ls Xb ->
  mspecL LBUDGET (QI (Xb ++ (Li ++ D)) P) (run_callsG d n ls rc)
         (fun _ s mo => exists Xb', QI (Xb' ++ (Li ++ D)) P s mo).
Proof.
  intros D Li d HD SD HS Hd. induction n as [|n IH]; intros ls rc Xb Hinv; cbn [run_callsG].
  - apply mspecL_ret. intros s mo H. exists Xb. exact H.
  - eapply mspecL_bind.
    { apply (interp_L P ok (Li ++ D) (fun X n0 Hn0 Hok => HOK D Li X n0 HD SD HS Hn0 Hok)
               (lib_one ls d) Xb _ (H_one ls d Xb Hinv Hd)). }
    intros r. apply mspecL_exI. intros X'. apply mspecL_pure_l. intros Hinv'.
    eapply mspecL_seq; [apply out_LP|]. intros _. apply IH. exact Hinv'.
Qed.

Lemma runG_L : forall b cap cfg payload, 65536 <= cap <= MAX_INPUT -> zlength payload <= MAX_INPUT ->
  mspecL LBUDGET (QI [(b, cap)] P) (runG cfg payload) (fun _ s mo => exists L, QI (L ++ [(b, cap)]) P s mo).
Proof.
  intros b cap cfg payload Hcap Hpl. unfold runG, target_runG, lib_init_prog.
  pose proof (zlength_nonneg' payload) as Hpl0.
  eapply mspecL_bind.
  { apply (interp_L P (okT T) [(b, cap)]
             (fun X n0 Hn0 Hok => okT_mal_okT P T HcT [(b, cap)] X n0 ltac:(cbn; lia) (szle_drv1 b cap Hcap) Hn0 Hok)
             lib_init [] _ H_init). }
  intros ls0. apply mspecL_exI. intros Li. apply mspecL_pure_l. intros [Hinv0 HS].
  cbv zeta.
  eapply mspecL_bind with
    (Q1 := fun a s mo => match a with
                         | None => QI (Li ++ [(b, cap)]) P s mo
                         | Some None => QI ([] ++ (Li ++ [(b, cap)])) P s mo
                         | Some (Some c) => QI ([] ++ (Li ++ [(c, zlength payload); (b, cap)])) P s mo
                         end).
  { destruct (zlength payload =? 0) eqn:EZ.
    - apply mspecL_ret. intros s mo H. exact H.
    - eapply mspecL_bind.
      + eapply mspecL_pre; [apply (raw_malloc_LP (Li ++ [(b, cap)]) (zlength payload) Hpl0)|].
        intros s mo H. split; [exact H|].
        apply (libfit_drv P Li [(b, cap)] (zlength payload)); [|cbn; lia| apply szle_drv1; exact Hcap| lia].
        apply (libfit_of_T P T HcT Li Li); [apply Permutation_refl| exact HS].
      + intros [c|]; apply mspecL_ret; intros s mo H; [|exact H].
        destruct H as [H _]. cbn [app]. eapply QIP_perm; [|exact H]. apply Permutation_middle. }
  intros [[c|]|]; [| |apply mspecL_ret; intros s mo H; exists Li; exact H].
  - (* [comment removed for export] *)
    eapply mspecL_bind.
    { apply (run_callsG_L [(c, zlength payload); (b, cap)] Li payload ltac:(cbn; lia) (szle_drv2 c b (zlength payload) cap (conj Hpl0 Hpl) Hcap) HS Hpl
               (Z.to_nat (Z.land cfg 3 + 1)) ls0 0 [] Hinv0). }
    intros rc. apply mspecL_exI. intros Xb.
    eapply mspecL_seq with (R := QI (Xb ++ Li ++ [(b, cap)]) P).
    { cbn [lib_free_optG]. eapply mspecL_pre; [apply (raw_free_LP (Xb ++ Li ++ [(b, cap)]) c (zlength payload))|].
      intros s mo H. eapply QIP_perm; [|exact H]. rewrite !app_assoc. apply Permutation_sym. apply Permutation_middle. }
    intros _. apply mspecL_ret. intros s mo H. exists (Xb ++ Li). rewrite <- app_assoc. exact H.
  - (* [comment removed for export] *)
    eapply mspecL_bind.
    { apply (run_callsG_L [(b, cap)] Li payload ltac:(cbn; lia) (szle_drv1 b cap Hcap) HS Hpl
               (Z.to_nat (Z.land cfg 3 + 1)) ls0 0 [] Hinv0). }
    intros rc. apply mspecL_exI. intros Xb.
    eapply mspecL_seq with (R := QI (Xb ++ Li ++ [(b, cap)]) P).
    { cbn [lib_free_optG]. apply mspecL_ret. intros s mo H. exact H. }
    intros _. apply mspecL_ret. intros s mo H. exists (Xb ++ Li). rewrite <- app_assoc. exact H.
Qed.

(* [comment removed for export] *)

Lemma alloc_init_LP : forall X bm, mspecL LBUDGET (QI X P) (alloc_init bm) (fun _ => QI X P).
Proof. intros X bm. unfold alloc_init. apply mspecL_ret. auto. Qed.

Lemma main_modelG_L : forall rstage argv,
  Forall (fun a => zlength a < 2^32) argv -> Forall path_okZ (tl argv) ->
  mspecL LBUDGET (QI [] P) (main_model io raw_malloc raw_free rstage alloc_init runG alloc_count argv)
        (fun _ s mo => exists X', ownL X' s mo /\ exitX X').
Proof.
  intros rstage argv Hargv Hpaths. unfold main_model.
  assert (Hnth : forall i, zlength (nth i argv []) < 2^32).
  { intros i. destruct (nth_in_or_default i argv []) as [Hin| ->]; [|unfold zlength; cbn; lia].
    exact (proj1 (Forall_forall _ _) Hargv _ Hin). }
  assert (Hnil : forall s mo, QI [] P s mo -> exists X', ownL X' s mo /\ exitX X').
  { intros s mo Ho. exists []. split; [exists []; exact Ho| apply exitX_nil]. }
  apply mspecL_if; intros Hlen2.
  { eapply mspecL_seq; [apply diag_LP|]. intros _. apply mspecL_ret. exact Hnil. }
  assert (Hp1 : path_okZ (nth 1 argv [])).
  { apply Bool.negb_false_iff in Hlen2. apply Z.eqb_eq in Hlen2.
    destruct argv as [|a0 [|a1 rest]]; cbn in Hlen2; try lia. cbn. inversion Hpaths; assumption. }
  eapply mspecL_bind;
    [apply (read_all_L LBUDGET io raw_malloc raw_free rstage QIP (mal_okP P) raw_malloc_LP raw_free_LP QIP_perm diag_LP
              QIP_minv QIP_fds QIP_live mal_ok_first mal_ok_grow); [apply Hnth| exact Hp1]|].
  intros [|buf content]; cbn beta iota.
  { apply mspecL_ret. intros s mo (X' & H & HX). exists X'. split; [exists []; exact H| exact HX]. }
  apply mspecL_pure. intros Hlen. apply mspecL_exI. intros k. apply mspecL_pure_l. intros Hk.
  apply (mspecL_pre LBUDGET _ (fun s mo => QI [(buf, 65536 * 2 ^ Z.of_nat k)] P s mo /\ zlength content <= 65536 * 2 ^ Z.of_nat k)); [| intros s mo H; exact H].
  apply mspecL_pointwise. intros s0 mo0 [Ho0 Hck]. apply (mspecL_pre LBUDGET _ (QI [(buf, 65536 * 2 ^ Z.of_nat k)] P)); [| intros s mo [-> ->]; exact Ho0].
  pose proof (LB_PDriver.pow2_le_1024 k Hk) as Hp.
  apply mspecL_if; intros _.
  { eapply mspecL_seq; [apply diag_LP|]. intros _. eapply mspecL_seq; [apply raw_free_LP|]. intros _. apply mspecL_ret. exact Hnil. }
  apply mspecL_if; intros _.
  { eapply mspecL_seq; [apply diag_LP|]. intros _. eapply mspecL_seq; [apply raw_free_LP|]. intros _. apply mspecL_ret. exact Hnil. }
  eapply mspecL_seq; [apply alloc_init_LP|]. intros _.
  assert (Hcap : 65536 <= 65536 * 2 ^ Z.of_nat k <= MAX_INPUT) by (pose proof (Z.pow_pos_nonneg 2 (Z.of_nat k) ltac:(lia) ltac:(lia)); unfold MAX_INPUT; lia).
  eapply mspecL_bind; [apply (runG_L buf _ _ _ Hcap); etransitivity; [| exact Hlen]; unfold zlength; rewrite length_skipn; lia|]. intros status.
  apply mspecL_exI. intros L.
  eapply mspecL_seq with (R := QI (L ++ [(buf, 65536 * 2 ^ Z.of_nat k)]) P).
  { destruct (Z.testbit _ 15); [|apply mspecL_ret; intros s mo H; exact H].
    unfold alloc_count. eapply mspecL_seq; [apply mspecL_ret; intros s mo H; exact H|]. intros n. apply mspecL_ret. intros s mo H; exact H. }
  intros status'. eapply mspecL_seq with (R := QI L P).
  { eapply mspecL_pre; [apply (raw_free_LP L buf (65536 * 2 ^ Z.of_nat k))|]. intros s mo H.
    eapply QIP_perm; [|exact H]. apply Permutation_sym. apply Permutation_cons_append. }
  intros _. apply mspecL_ret. intros s mo Ho. exists []. split; [exists L; rewrite app_nil_r; exact Ho| apply exitX_nil].
Qed.

Lemma prog_withG_L : forall rstage argv,
  Forall (fun a => zlength a < 2^32) argv -> Forall path_okZ (tl argv) ->
  mspecL LBUDGET (QI [] P) (prog_withG rstage argv) (fun _ _ _ => False).
Proof.
  intros rstage argv Hargv Hpaths. unfold prog_withG.
  eapply mspecL_seq; [apply (startup_L LBUDGET (QI [] P)); [apply QIP_minv| apply QIP_fds| apply QIP_live]|]. intros u.
  eapply mspecL_bind; [apply main_modelG_L; assumption|].
  intros code. apply (exit_model_L LBUDGET io exit_hook ownL); [apply exitio_ownL|].
  intros X _. unfold exit_hook. apply mspecL_ret. intros s mo H. exists X. exact H.
Qed.

(* [comment removed for export] *)
Theorem progG_noerr_gen : forall segs rstage pc ph lim en inp,
  image_low segs -> KLIM + SMALLREQ <= lim ->
  valid_entry (mkImage segs pc ph) en inp -> valid_input_either inp ->
  bv_unsigned (en_sp en) - stack_max_size = alloc_ceiling ->
  tsafe nstep node_noerr (progG segs rstage (in_argv inp))
        (init_model (segments_reserved segs) (en_brk en) (en_mmap_base en) (en_sp en) lim inp).
Proof.
  intros segs rstage pc ph lim [sp brk0 mbase] inp Hsegs Hlim Hve Hvi Htop.
  destruct Hve as (_ & Hbrk & _). destruct Hvi as (Hargv & _ & _ & Hrel & _).
  unfold progG. cbn [en_brk en_mmap_base en_sp] in *.
  apply (mspecL_program_noerr LBUDGET (QI [] P) (prog_withG rstage (argv_Z (in_argv inp))) (fun _ _ _ => False)).
  - apply prog_withG_L; [apply argv_Z_short| apply argv_Z_paths]; exact Hargv.
  - unfold reservedZ. unfold valid_brk in Hbrk. cbn [img_segments] in Hbrk.
    apply QI_init; [exact Hbrk| exact (proj1 Hsegs)| exact (image_low_ceil segs Hsegs)| exact Htop| exact HP0| exact PHI_le| exact (proj2 Hsegs)| exact Hlim| exact Hrel].
  - intros [].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma OQP_GI : forall X s mo, OQP X s mo -> GI (map fst X) s mo.
Proof. intros X s mo [H _]. exact H. Qed.

Lemma pieces_emit_0_short : Forall (fun p : list Z => zlength p < 2^62) pieces_emit_0.
Proof. unfold pieces_emit_0. repeat constructor; unfold zlength; cbn; lia. Qed.

Lemma out_NP : forall X, mspecN (OQP X) (stdout_vprintf ps_so set_so_ps pieces_emit_0) (fun _ => OQP X).
Proof.
  intros X.
  eapply mspecN_conseq;
    [apply (mspecN_combine2 LBUDGET _ _ _ _ _ (stdout_vprintf_GI (map fst X) pieces_emit_0 pieces_emit_0_short) (out_LP X pieces_emit_0))| |].
  - intros s mo H. exact H.
  - intros u s mo H. exact H.
Qed.

Lemma run_callsG_N : forall D Li d, (length D <= 4)%nat -> szle (MAX_INPUT + 1) D -> subms (map snd Li) T ->
  zlength d <= MAX_INPUT ->
  forall n ls rc Xb, linv ls Xb ->
  mspecN (OQP (Xb ++ (Li ++ D))) (run_callsG d n ls rc)
         (fun _ s mo => exists Xb', OQP (Xb' ++ (Li ++ D)) s mo).
Proof.
  intros D Li d HD SD HS Hd. induction n as [|n IH]; intros ls rc Xb Hinv; cbn [run_callsG].
  - apply mspecN_ret. intros s mo H. exists Xb. exact H.
  - eapply mspecN_bind.
    { apply (interp_N Gso frame_ok_Gso P ok (Li ++ D)
               (fun X n0 Hn0 Hok => HOK D Li X n0 HD SD HS Hn0 Hok)
               (lib_one ls d) Xb _ (lwf_lleaves _ _ _ _ _ (H_one ls d Xb Hinv Hd) (H_rc ls d))). }
    intros r. apply mspecN_exI. intros X'. apply mspecN_pure_l. intros [Hinv' Hrc].
    unfold lib_one_prog. rewrite Hrc. change (pieces_emit_of (Zdecimal 0 ++ [10])) with pieces_emit_0.
    eapply mspecN_seq; [apply out_NP|]. intros _. apply IH. exact Hinv'.
Qed.

Lemma runG_N : forall b cap cfg payload, 65536 <= cap <= MAX_INPUT -> zlength payload <= MAX_INPUT ->
  mspecN (OQP [(b, cap)]) (runG cfg payload) (fun _ s mo => exists L, OQP (L ++ [(b, cap)]) s mo).
Proof.
  intros b cap cfg payload Hcap Hpl. unfold runG, target_runG, lib_init_prog.
  pose proof (zlength_nonneg' payload) as Hpl0.
  eapply mspecN_bind.
  { apply (interp_N Gso frame_ok_Gso P (okT T) [(b, cap)]
             (fun X n0 Hn0 Hok => okT_mal_okT P T HcT [(b, cap)] X n0 ltac:(cbn; lia) (szle_drv1 b cap Hcap) Hn0 Hok)
             lib_init [] _ H_init). }
  intros ls0. apply mspecN_exI. intros Li. apply mspecN_pure_l. intros [Hinv0 HS].
  cbv zeta.
  eapply mspecN_bind with
    (Q1 := fun a s mo => match a with
                         | None => False
                         | Some None => OQP ([] ++ (Li ++ [(b, cap)])) s mo
                         | Some (Some c) => OQP ([] ++ (Li ++ [(c, zlength payload); (b, cap)])) s mo
                         end).
  { destruct (zlength payload =? 0) eqn:EZ.
    - apply mspecN_ret. intros s mo H. exact H.
    - eapply mspecN_bind.
      + eapply mspecN_pre; [apply (raw_malloc_N Gso frame_ok_Gso P (Li ++ [(b, cap)]) (zlength payload)); unfold MAX_INPUT in Hpl; lia|].
        intros s mo H. split; [exact H|].
        apply (libfit_drv P Li [(b, cap)] (zlength payload)); [|cbn; lia| apply szle_drv1; exact Hcap| lia].
        apply (libfit_of_T P T HcT Li Li); [apply Permutation_refl| exact HS].
      + intros r. apply mspecN_ret. intros s mo (c & -> & H).
        cbn [app]. eapply OQ_perm; [|exact H]. apply Permutation_middle. }
  intros [[c|]|]; [| |apply mspecN_false].
  - eapply mspecN_bind.
    { apply (run_callsG_N [(c, zlength payload); (b, cap)] Li payload ltac:(cbn; lia)
               (szle_drv2 c b (zlength payload) cap (conj Hpl0 Hpl) Hcap) HS Hpl
               (Z.to_nat (Z.land cfg 3 + 1)) ls0 0 [] Hinv0). }
    intros rc. apply mspecN_exI. intros Xb.
    eapply mspecN_seq with (R := OQP (Xb ++ Li ++ [(b, cap)])).
    { cbn [lib_free_optG]. eapply mspecN_pre; [apply (raw_free_N Gso frame_ok_Gso P (Xb ++ Li ++ [(b, cap)]) c (zlength payload))|].
      intros s mo H. eapply OQ_perm; [|exact H]. rewrite !app_assoc. apply Permutation_sym. apply Permutation_middle. }
    intros _. apply mspecN_ret. intros s mo H. exists (Xb ++ Li). rewrite <- app_assoc. exact H.
  - eapply mspecN_bind.
    { apply (run_callsG_N [(b, cap)] Li payload ltac:(cbn; lia) (szle_drv1 b cap Hcap) HS Hpl
               (Z.to_nat (Z.land cfg 3 + 1)) ls0 0 [] Hinv0). }
    intros rc. apply mspecN_exI. intros Xb.
    eapply mspecN_seq with (R := OQP (Xb ++ Li ++ [(b, cap)])).
    { cbn [lib_free_optG]. apply mspecN_ret. intros s mo H. exact H. }
    intros _. apply mspecN_ret. intros s mo H. exists (Xb ++ Li). rewrite <- app_assoc. exact H.
Qed.

Lemma diag_GI' : forall X d, diag_ok d -> mspec (GI X) (io_diag io d) (fun _ => GI X).
Proof. intros X d Hd. apply s_diag_GI. exact Hd. Qed.

Lemma main_modelG_N : forall rstage argv,
  Forall (fun a => zlength a < 2^32) argv -> Forall path_okZ (tl argv) ->
  mspecN (OQP []) (main_model io raw_malloc raw_free rstage alloc_init runG alloc_count argv)
         (fun _ s mo => exists X', GI X' s mo).
Proof.
  intros rstage argv Hargv Hpaths. unfold main_model.
  assert (Hnth : forall i, zlength (nth i argv []) < 2^32).
  { intros i. destruct (nth_in_or_default i argv []) as [Hin| ->]; [|unfold zlength; cbn; lia].
    exact (proj1 (Forall_forall _ _) Hargv _ Hin). }
  apply mspecN_if; intros Hlen2.
  { eapply mspecN_pre; [apply mspec_N; eapply mspec_seq; [apply (diag_GI' []); cbn; apply Hnth|]; intros _; apply mspec_ret;
                        intros s mo Ho; exists []; exact Ho|].
    intros s mo H. exact (OQP_GI _ _ _ H). }
  assert (Hp1 : path_okZ (nth 1 argv [])).
  { apply Bool.negb_false_iff in Hlen2. apply Z.eqb_eq in Hlen2.
    destruct argv as [|a0 [|a1 rest]]; cbn in Hlen2; try lia. cbn. inversion Hpaths; assumption. }
  eapply mspecN_bind.
  { eapply mspecN_pre;
      [apply (mspecN_combine2 LBUDGET _ _ _ _ _
                (read_all_spec io raw_malloc raw_free rstage GI raw_malloc_GI raw_free_GI GI_perm diag_GI' GI_minv GI_fds
                               [] (nth 1 argv []) (Hnth 1%nat) Hp1)
                (read_all_L LBUDGET io raw_malloc raw_free rstage QIP (mal_okP P) raw_malloc_LP raw_free_LP QIP_perm diag_LP
                            QIP_minv QIP_fds QIP_live mal_ok_first mal_ok_grow (nth 1 argv []) (Hnth 1%nat) Hp1))|].
    intros s mo H. exact H. }
  intros [|buf content]; cbn beta iota.
  { apply mspecN_ret. intros s mo [H _]. exact H. }
  apply mspecN_pointwise. intros s0 mo0 [[HGI Hlen] [(k & Hk & HQ & Hck) _]].
  pose proof (LB_PDriver.pow2_le_1024 k Hk) as Hp.
  assert (Herr : forall d, diag_ok d ->
            mspecN (fun s mo => s = s0 /\ mo = mo0) (mbind (io_diag io d) (fun _ => mbind (raw_free buf) (fun _ => mret 2)))
                   (fun _ s mo => exists X', GI X' s mo)).
  { intros d Hd. eapply mspecN_pre; [apply mspec_N; eapply mspec_seq; [apply (diag_GI' [buf] d Hd)|]; intros _;
                                     eapply mspec_seq; [apply raw_free_GI|]; intros _; apply mspec_ret; intros s mo Ho; exists []; exact Ho|].
    intros s mo [-> ->]. exact HGI. }
  apply mspecN_if; intros _; [apply Herr; exact I|].
  apply mspecN_if; intros _; [apply Herr; exact I|].
  assert (Hcap : 65536 <= 65536 * 2 ^ Z.of_nat k <= MAX_INPUT) by (pose proof (Z.pow_pos_nonneg 2 (Z.of_nat k) ltac:(lia) ltac:(lia)); unfold MAX_INPUT; lia).
  eapply mspecN_seq with (R := OQP [(buf, 65536 * 2 ^ Z.of_nat k)]).
  { unfold alloc_init. apply mspecN_ret. intros s mo [-> ->]. split; [exact HGI| exact HQ]. }
  intros _.
  eapply mspecN_bind; [apply (runG_N buf _ _ _ Hcap); etransitivity; [| exact Hlen]; unfold zlength; rewrite length_skipn; lia|]. intros status.
  apply mspecN_exI. intros L.
  eapply mspecN_seq with (R := OQP (L ++ [(buf, 65536 * 2 ^ Z.of_nat k)])).
  { destruct (Z.testbit _ 15); [|apply mspecN_ret; intros s mo H; exact H].
    unfold alloc_count. eapply mspecN_seq; [apply mspecN_ret; intros s mo H; exact H|]. intros n. apply mspecN_ret. intros s mo H; exact H. }
  intros status'.
  eapply mspecN_pre; [apply mspec_N; eapply mspec_seq; [apply (raw_free_GI (map fst L) buf)|]; intros _; apply mspec_ret;
                      intros s mo Ho; exists (map fst L); exact Ho|].
  intros s mo H. apply OQP_GI in H. eapply GI_perm; [|exact H]. rewrite map_app. cbn [map fst].
  apply Permutation_sym. apply Permutation_cons_append.
Qed.

Lemma prog_withG_N : forall rstage argv,
  Forall (fun a => zlength a < 2^32) argv -> Forall path_okZ (tl argv) ->
  mspecN (OQP []) (prog_withG rstage argv) (fun _ _ _ => False).
Proof.
  intros rstage argv Hargv Hpaths. unfold prog_withG.
  eapply mspecN_seq with (R := OQP []).
  { eapply mspecN_conseq; [apply (mspecN_combine2 LBUDGET _ _ _ _ _ (startup_GI [])
                                    (startup_L LBUDGET (QI [] P) (QIP_minv []) (QIP_fds []) (QIP_live [])))| |].
    - intros s mo H. exact H.
    - intros u s mo H. exact H. }
  intros _. eapply mspecN_bind; [apply main_modelG_N; assumption|].
  intros code. apply mspec_N.
  eapply (exit_model_spec io exit_hook GI); [apply stdout_exit_flush_GI| apply exit_hook_GI].
Qed.

(* [comment removed for export] *)
Theorem progG_model_ok : forall segs rstage pc ph lim en inp,
  image_low segs -> KLIM + SMALLREQ <= lim ->
  valid_entry (mkImage segs pc ph) en inp -> valid_input_either inp ->
  bv_unsigned (en_sp en) - stack_max_size = alloc_ceiling ->
  leaves_unreachable_m nstep (progG segs rstage (in_argv inp)) (mo0 segs lim en inp)
  /\ tsafe nstep nsafe (progG segs rstage (in_argv inp)) (mo0 segs lim en inp).
Proof.
  intros segs rstage pc ph lim en inp Hlow Hlim Hve Hvi Htop.
  pose proof (progG_noerr_gen segs rstage pc ph lim en inp Hlow Hlim Hve Hvi Htop) as Hnoerr.
  destruct en as [sp brk0 mbase]. destruct Hve as (_ & Hbrk & _). destruct Hvi as (Hargv & _ & _ & Hrel & _).
  unfold progG, mo0 in *. cbn [en_brk en_mmap_base en_sp] in *.
  apply (mspecN_program (OQP []) (prog_withG rstage (argv_Z (in_argv inp)))).
  - apply prog_withG_N; [apply argv_Z_short| apply argv_Z_paths]; exact Hargv.
  - unfold reservedZ. cbn [img_segments] in Hbrk. split.
    + apply (GI_init segs); [exact Hbrk| exact (proj1 Hlow)| exact (image_low_ceil segs Hlow)| exact Htop| exact Hrel].
    + unfold valid_brk in Hbrk.
      apply QI_init; [exact Hbrk| exact (proj1 Hlow)| exact (image_low_ceil segs Hlow)| exact Htop| exact HP0| exact PHI_le| exact (proj2 Hlow)| exact Hlim| exact Hrel].
  - exact Hnoerr.
Qed.

End ProgGSafe.
