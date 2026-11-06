(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Specs Run.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AS Require Import CfgStep CatSim ShapeAlg AsanAcct AsanAcctShape.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import Exec.
Import ListNotations.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition HID (A : list (Z * Z)) (mo : Model) : word -> bool :=
  fun a => mkH (m_vm_lazy mo) A a || (2^47 <=? bv_unsigned a)%Z.

Definition macct (segtop : Z) (A : list (Z * Z)) (mo : Model) : Prop :=
  A_wf A /\ MInv A mo /\ m_halted mo = None /\ ranges_from_b (m_vm_lazy mo) segtop = true /\ (segtop <= 2^47)%Z.

(* [comment removed for export] *)
Definition HZ (A : list (Z * Z)) (c : config) : Prop :=
  forall a, mkH (m_vm_lazy (cfg_model c)) A a = true ->
    page_in_ranges (page_base a) (vm_noaccess (m_vmmaps (cfg_model c))) = false ->
    ms_mem (cfg_ms c) a = Some (Z_to_bv 8 0).

Definition AST (segtop : Z) (A : list (Z * Z)) (Pm : machine_state -> Prop) (PM : Model -> Prop) (c : config) : Prop :=
  macct segtop A (cfg_model c) /\ Pm (restrict (HID A (cfg_model c)) (cfg_ms c)) /\ PM (cfg_model c) /\ HZ A c.

Definition mat_stable (PM : Model -> Prop) : Prop :=
  forall mo mo', same_but_materialized mo mo' -> PM mo -> PM mo'.

Lemma mat_stable_true : mat_stable (fun _ => True).
Proof. intros mo mo' _ _. exact I. Qed.

Lemma mat_stable_and : forall P Q, mat_stable P -> mat_stable Q -> mat_stable (fun mo => P mo /\ Q mo).
Proof. intros P Q HP HQ mo mo' Hs [H1 H2]. split; [eapply HP| eapply HQ]; eassumption. Qed.

Lemma mat_stable_ex : forall {X} (P : X -> Model -> Prop), (forall x, mat_stable (P x)) -> mat_stable (fun mo => exists x, P x mo).
Proof. intros X P HP mo mo' Hs [x Hx]. exists x. eapply HP; eassumption. Qed.

Lemma mat_stable_pure : forall (phi : Prop), mat_stable (fun _ => phi).
Proof. intros phi mo mo' _ H. exact H. Qed.

(* [comment removed for export] *)
Lemma mat_stable_obs : forall (F : list (word * FdEntry) -> Fs.Fs -> VmMaps -> list (word * word) -> Z -> Prop),
  mat_stable (fun mo => F (m_fds mo) (m_fs mo) (m_vmmaps mo) (m_vm_lazy mo) (eager_used mo)).
Proof.
  intros F mo mo' Hs H. pose proof (same_but_materialized_frame mo mo' Hs) as Fr.
  destruct Fr as (_ & Hvm & Hlz & _ & _ & _ & _ & _ & Hfd & _ & _ & Hfs & _ & _ & _ & _ & Heu).
  rewrite Hfd, Hfs, Hvm, Hlz, Heu. exact H.
Qed.

(* [comment removed for export] *)
Ltac mat_stable_tac :=
  let mo := fresh "mo" in let mo' := fresh "mo'" in let Hs := fresh "Hs" in let Hp := fresh "Hp" in
  intros mo mo' Hs Hp;
  let Fr := fresh "Fr" in pose proof (same_but_materialized_frame mo mo' Hs) as Fr;
  let Hvm := fresh in let Hlz := fresh in let Hfd := fresh in let Hfs := fresh in
  let Hh := fresh in let Htid := fresh in let Heu := fresh in
  destruct Fr as (_ & Hvm & Hlz & _ & _ & _ & _ & _ & Hfd & _ & _ & Hfs & Hh & Htid & _ & _ & Heu);
  rewrite ?Hvm, ?Hlz, ?Hfd, ?Hfs, ?Hh, ?Htid, ?Heu; exact Hp.

Section RzCPS.
Variable segs : list Segment.
Variable segtop : Z.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition cps (P Q : config -> Prop) : Prop :=
  forall T c, P c -> (forall c', Q c' -> realizes segs c' T) -> realizes segs c T.

Definition cpsE (P : config -> Prop) (evs : list event) (Q : config -> Prop) : Prop :=
  forall T c, P c -> (forall c', Q c' -> realizes segs c' T) -> realizes segs c (t_emit evs T).

Definition cps2 (P Q1 Q2 : config -> Prop) : Prop :=
  forall T1 T2 c, P c -> (forall c', Q1 c' -> realizes segs c' T1) -> (forall c', Q2 c' -> realizes segs c' T2) ->
    realizes segs c (t_alt2 T1 T2).

Lemma cps_refl : forall P, cps P P.
Proof. intros P T c HP Hk. exact (Hk c HP). Qed.

Lemma cps_seq : forall P Q R, cps P Q -> cps Q R -> cps P R.
Proof. intros P Q R H1 H2 T c HP Hk. apply (H1 T c HP). intros c' HQ. exact (H2 T c' HQ Hk). Qed.

Lemma cps_conseq : forall P P' Q Q', cps P Q -> (forall c, P' c -> P c) -> (forall c, Q c -> Q' c) -> cps P' Q'.
Proof. intros P P' Q Q' H HP HQ T c HP' Hk. apply (H T c (HP c HP')). intros c' Hq. exact (Hk c' (HQ c' Hq)). Qed.

Lemma cps_or : forall P1 P2 Q, cps P1 Q -> cps P2 Q -> cps (fun c => P1 c \/ P2 c) Q.
Proof. intros P1 P2 Q H1 H2 T c [HP|HP] Hk; [exact (H1 T c HP Hk)| exact (H2 T c HP Hk)]. Qed.

Lemma cps_ex : forall {X} (P : X -> config -> Prop) Q, (forall x, cps (P x) Q) -> cps (fun c => exists x, P x c) Q.
Proof. intros X P Q H T c [x HP] Hk. exact (H x T c HP Hk). Qed.

Lemma cps_pure : forall P (phi : Prop) Q, (phi -> cps P Q) -> cps (fun c => P c /\ phi) Q.
Proof. intros P phi Q H T c [HP Hphi] Hk. exact (H Hphi T c HP Hk). Qed.

Lemma cps_false : forall Q, cps (fun _ => False) Q.
Proof. intros Q T c []. Qed.

Lemma cpsE_conseq : forall P P' evs Q Q', cpsE P evs Q -> (forall c, P' c -> P c) -> (forall c, Q c -> Q' c) -> cpsE P' evs Q'.
Proof. intros P P' evs Q Q' H HP HQ T c HP' Hk. apply (H T c (HP c HP')). intros c' Hq. exact (Hk c' (HQ c' Hq)). Qed.

Lemma cps_cpsE : forall P Q R evs, cps P Q -> cpsE Q evs R -> cpsE P evs R.
Proof. intros P Q R evs H1 H2 T c HP Hk. apply (H1 (t_emit evs T) c HP). intros c' HQ. exact (H2 T c' HQ Hk). Qed.

Lemma t_emit_app : forall e1 e2 T, t_eq (t_emit (e1 ++ e2) T) (t_emit e1 (t_emit e2 T)).
Proof.
  intros e1 e2 T tr. unfold t_emit. split.
  - intros [Hp|(tr' & -> & HT)].
    + apply is_prefix_app_split in Hp as [Hp|(b' & -> & Hp)]; [left; exact Hp|].
      right. exists b'. split; [reflexivity| left; exact Hp].
    + right. exists (e2 ++ tr'). split; [symmetry; apply app_assoc|]. right. exists tr'. auto.
  - intros [Hp|(tr' & -> & [Hp|(tr'' & -> & HT)])].
    + left. apply is_prefix_app_r. exact Hp.
    + left. apply is_prefix_app_mono. exact Hp.
    + right. exists tr''. split; [apply app_assoc| exact HT].
Qed.

Lemma cpsE_seq : forall P Q R e1 e2, cpsE P e1 Q -> cpsE Q e2 R -> cpsE P (e1 ++ e2) R.
Proof.
  intros P Q R e1 e2 H1 H2 T c HP Hk. eapply rz_conseq; [| apply t_eq_sym, t_emit_app].
  apply (H1 (t_emit e2 T) c HP). intros c' HQ. exact (H2 T c' HQ Hk).
Qed.

Lemma cpsE_nil : forall P Q, cps P Q -> cpsE P [] Q.
Proof.
  intros P Q H T c HP Hk. pose proof (H T c HP Hk) as R.
  eapply rz_conseq; [exact R|]. apply t_eq_sym. apply t_emit_nil_eq. eapply realizes_nonempty. exact R.
Qed.

Lemma cpsE_cps : forall P Q R evs, cpsE P evs Q -> cps Q R -> cpsE P evs R.
Proof. intros P Q R evs H1 H2 T c HP Hk. apply (H1 T c HP). intros c' HQ. exact (H2 T c' HQ Hk). Qed.

Lemma cps2_cps : forall P Q1 Q2 R1 R2, cps2 P Q1 Q2 -> cps Q1 R1 -> cps Q2 R2 -> cps2 P R1 R2.
Proof.
  intros P Q1 Q2 R1 R2 H H1 H2 T1 T2 c HP Hk1 Hk2. apply (H T1 T2 c HP).
  - intros c' HQ. exact (H1 T1 c' HQ Hk1).
  - intros c' HQ. exact (H2 T2 c' HQ Hk2).
Qed.

Lemma cps_realizes : forall P Q T c, cps P Q -> P c -> (forall c', Q c' -> realizes segs c' T) -> realizes segs c T.
Proof. intros P Q T c H HP Hk. exact (H T c HP Hk). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma AST_conseq : forall A Pm Pm' PM PM' c,
  AST segtop A Pm PM c -> (forall ms, Pm ms -> Pm' ms) -> (forall mo, PM mo -> PM' mo) -> AST segtop A Pm' PM' c.
Proof. intros A Pm Pm' PM PM' c (H1 & H2 & H3 & H4) HP HQ. split; [exact H1|]. split; [auto|]. split; [auto| exact H4]. Qed.

Lemma cps_AST_conseq : forall A Pm PM Pm' PM' Q,
  cps (AST segtop A Pm PM) Q -> (forall ms, Pm' ms -> Pm ms) -> (forall mo, PM' mo -> PM mo) -> cps (AST segtop A Pm' PM') Q.
Proof. intros A Pm PM Pm' PM' Q H HP HQ. eapply cps_conseq; [exact H| |auto]. intros c Hc. eapply AST_conseq; eauto. Qed.

Lemma AST_exI : forall {X} A (Pm : X -> machine_state -> Prop) PM c,
  AST segtop A (fun ms => exists x, Pm x ms) PM c -> exists x, AST segtop A (Pm x) PM c.
Proof. intros X A Pm PM c (H1 & [x H2] & H3 & H4). exists x. split; [exact H1|]. auto. Qed.

Lemma cps_AST_ex : forall {X} A (Pm : X -> machine_state -> Prop) PM Q,
  (forall x, cps (AST segtop A (Pm x) PM) Q) -> cps (AST segtop A (fun ms => exists x, Pm x ms) PM) Q.
Proof. intros X A Pm PM Q H T c Hc Hk. destruct (AST_exI A Pm PM c Hc) as [x Hx]. exact (H x T c Hx Hk). Qed.

Lemma cps_AST_pure : forall A Pm PM (phi : Prop) Q,
  (phi -> cps (AST segtop A Pm PM) Q) -> cps (AST segtop A (fun ms => Pm ms /\ phi) PM) Q.
Proof.
  intros A Pm PM phi Q H T c (H1 & [H2 Hphi] & H3 & H4) Hk. apply (H Hphi T c); [|exact Hk].
  split; [exact H1|]. split; [exact H2|]. split; [exact H3| exact H4].
Qed.

End RzCPS.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition set_mem (ms : machine_state) (m : word -> option byte) : machine_state :=
  {| ms_regs := ms_regs ms; ms_fregs := ms_fregs ms; ms_pc_val := ms_pc_val ms;
     ms_svc_pending := ms_svc_pending ms; ms_resv := ms_resv ms; ms_fcsr := ms_fcsr ms;
     ms_mem := m; ms_rom := ms_rom ms |}.

(* [comment removed for export] *)
Definition revealed (A A' : list (Z * Z)) (mo : Model) (ms0 ms : machine_state) : Prop :=
  ms = set_mem ms0 (ms_mem ms) /\
  (forall a, HID A mo a = false -> ms_mem ms a = ms_mem ms0 a) /\
  (forall a, HID A mo a = true -> HID A' mo a = false ->
     page_in_ranges (page_base a) (vm_noaccess (m_vmmaps mo)) = false -> ms_mem ms a = Some (Z_to_bv 8 0)).

Lemma A_bytes_app : forall X A, A_bytes (X ++ A) = (A_bytes X + A_bytes A)%Z.
Proof. induction X as [|iv X IH]; intros A; cbn [app A_bytes]; [lia|]. rewrite IH. lia. Qed.

Lemma A_wf_app : forall X A, A_wf X -> A_wf A -> A_wf (X ++ A).
Proof. intros X A HX HA. unfold A_wf in *. apply Forall_app. auto. Qed.

Lemma page_allowedb_app_l : forall X A p, page_allowedb A p = true -> page_allowedb (X ++ A) p = true.
Proof. intros X A p H. unfold page_allowedb in *. rewrite existsb_app, H. apply orb_true_r. Qed.

Lemma page_allowedb_app_r : forall X A p, page_allowedb X p = true -> page_allowedb (X ++ A) p = true.
Proof. intros X A p H. unfold page_allowedb in *. rewrite existsb_app, H. reflexivity. Qed.

Lemma mkH_mono : forall L A A' a, (forall p, page_allowedb A p = true -> page_allowedb A' p = true) ->
  mkH L A' a = true -> mkH L A a = true.
Proof.
  intros L A A' a HAA' H. unfold mkH in *. apply andb_prop in H as [H1 H2]. rewrite H1. cbn.
  destruct (page_allowedb A (page_base a)) eqn:E; [|reflexivity]. rewrite (HAA' _ E) in H2. discriminate.
Qed.

Lemma HID_mono : forall A A' mo a, (forall p, page_allowedb A p = true -> page_allowedb A' p = true) ->
  HID A' mo a = true -> HID A mo a = true.
Proof.
  intros A A' mo a HAA' H. unfold HID in *. apply orb_true_iff in H as [H|H]; apply orb_true_iff; [left| right; exact H].
  exact (mkH_mono _ A A' a HAA' H).
Qed.

Lemma HID_of_mkH : forall A mo a, mkH (m_vm_lazy mo) A a = true -> HID A mo a = true.
Proof. intros A mo a H. unfold HID. rewrite H. reflexivity. Qed.

Lemma mkH_of_HID : forall A A' mo a, HID A mo a = true -> HID A' mo a = false -> mkH (m_vm_lazy mo) A a = true.
Proof.
  intros A A' mo a H H'. unfold HID in *. apply orb_false_iff in H' as [_ H2]. rewrite H2, orb_false_r in H. exact H.
Qed.

Lemma HID_same : forall A mo mo', same_but_materialized mo mo' -> HID A mo' = HID A mo.
Proof.
  intros A mo mo' Hs. unfold HID. pose proof (same_but_materialized_frame mo mo' Hs) as Fr.
  destruct Fr as (_ & _ & Hlz & _). rewrite Hlz. reflexivity.
Qed.

Lemma macct_same : forall segtop A mo mo', same_but_materialized mo mo' -> MInv A mo' -> macct segtop A mo -> macct segtop A mo'.
Proof.
  intros segtop A mo mo' Hs Hinv (H1 & _ & H3 & H4 & H5). pose proof (same_but_materialized_frame mo mo' Hs) as Fr.
  destruct Fr as (_ & _ & Hlz & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hh & _). split; [exact H1|]. split; [exact Hinv|].
  rewrite Hlz, Hh. auto.
Qed.

Section Bridges.
Variable segs : list Segment.
Variable segtop : Z.
Hypothesis Hwx : wx_segs_nowrap segs.
Hypothesis Hsegs : segs_below_b segs segtop = true.

Lemma HID_off : forall A mo, macct segtop A mo -> H_off_segments segs (HID A mo).
Proof.
  intros A mo (_ & _ & _ & Hr & Ht). apply (H_off_segments_above segs (HID A mo) segtop Hsegs).
  intros a Ha. unfold HID in Ha. apply orb_true_iff in Ha as [Ha|Ha].
  - exact (mkH_above (m_vm_lazy mo) A segtop a Hr Ha).
  - apply Z.leb_le in Ha. lia.
Qed.

Lemma HID_cover : forall A mo, lazy_cover (HID A mo) (m_vm_lazy mo) A.
Proof.
  intros A mo w Hl Hw. unfold HID in Hw. apply orb_false_iff in Hw as [Hw _].
  exact (lazy_cover_mkH (m_vm_lazy mo) A (m_vm_lazy mo) (incl_refl _) w Hl Hw).
Qed.

Lemma msteps_CatSim : forall ms ms', Exec.msteps segs ms ms' -> CatSim.msteps segs ms ms'.
Proof.
  induction 1 as [ms|ms ms1 ms2 [Hsvc Hst] _ IH]; [apply mst_refl|]. eapply mst_step; [exact Hsvc| exact Hst| exact IH].
Qed.

(* [comment removed for export] *)
Lemma ast_evt : forall A Pm PM Q, mat_stable PM ->
  (forall ms, Pm ms -> evt segs Q ms) -> cps segs (AST segtop A Pm PM) (AST segtop A Q PM).
Proof.
  intros A Pm PM Q HPM HQ T [ms mo] (Hmc & HPm & HPMmo & HZ0) Hk. cbn [cfg_ms cfg_model] in *.
  destruct (HQ _ HPm) as (msr' & Hms & HQ').
  pose proof Hmc as (HAwf & HMInv & Hh & Hr & Ht).
  apply (rz_msteps_restricted_T segs (HID A mo) (HID_off A mo Hmc) Hwx A ms msr' mo T (HID_cover A mo) HAwf HMInv Hh
           (msteps_CatSim _ _ Hms)).
  intros mo' HMInv' Hsame Hcl. apply Hk.
  pose proof (same_but_materialized_frame mo mo' Hsame) as Fr.
  destruct Fr as (_ & Hvm & Hlz & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _).
  split; [exact (macct_same segtop A mo mo' Hsame HMInv' Hmc)|]. cbn [cfg_ms cfg_model].
  rewrite (HID_same A mo mo' Hsame), (restrict_unrestrict_clean _ _ _ Hcl).
  split; [exact HQ'|]. split; [exact (HPM _ _ Hsame HPMmo)|].
  intros a Ha Hna. cbn [cfg_ms cfg_model] in *. rewrite Hlz in Ha. rewrite Hvm in Hna.
  rewrite unrestrict_mem. unfold munrestrict. rewrite (HID_of_mkH A mo a Ha). exact (HZ0 a Ha Hna).
Qed.

(* [comment removed for export] *)
Lemma ast_widen : forall A A' Pm PM,
  (A_wf A -> A_wf A') -> (forall p, page_allowedb A p = true -> page_allowedb A' p = true) ->
  (forall mo, PM mo -> (eager_used mo + A_bytes A' <= vm_limit (m_vmmaps mo))%Z) ->
  cps segs (AST segtop A Pm PM) (AST segtop A' (fun ms => exists ms0 mo, PM mo /\ Pm ms0 /\ revealed A A' mo ms0 ms) PM).
Proof.
  intros A A' Pm PM HA' Hsub Hbud T [ms mo] (Hmc & HPm & HPMmo & HZ0) Hk. cbn [cfg_ms cfg_model] in *. apply Hk.
  pose proof Hmc as (HAwf & [M1 M2 M3 M4 M5] & Hh & Hr & Ht).
  split.
  { split; [exact (HA' HAwf)|]. split; [|split; [assumption| split; assumption]].
    constructor; [exact M1| exact M2| intros p Hp; apply Hsub; exact (M3 p Hp)| exact M4| exact (Hbud mo HPMmo)]. }
  cbn [cfg_ms cfg_model]. split; [|split; [exact HPMmo|]].
  - exists (restrict (HID A mo) ms), mo. split; [exact HPMmo|]. split; [exact HPm|]. split; [reflexivity|]. split.
    + intros a Ha. cbn. unfold mrestrict. rewrite Ha.
      destruct (HID A' mo a) eqn:E; [|reflexivity]. rewrite (HID_mono A A' mo a Hsub E) in Ha. discriminate.
    + intros a Ha Ha' Hna. cbn. unfold mrestrict. rewrite Ha'. exact (HZ0 a (mkH_of_HID A A' mo a Ha Ha') Hna).
  - intros a Ha Hna. exact (HZ0 a (mkH_mono _ A A' a Hsub Ha) Hna).
Qed.

(* [comment removed for export] *)
Lemma ast_allow : forall A X Pm PM,
  A_wf X ->
  (forall mo, PM mo -> (eager_used mo + A_bytes X + A_bytes A <= vm_limit (m_vmmaps mo))%Z) ->
  cps segs (AST segtop A Pm PM) (AST segtop (X ++ A) (fun ms => exists ms0 mo, PM mo /\ Pm ms0 /\ revealed A (X ++ A) mo ms0 ms) PM).
Proof.
  intros A X Pm PM HX Hb.
  apply ast_widen; [intros HA; apply A_wf_app; assumption| apply page_allowedb_app_l|].
  intros mo H. rewrite A_bytes_app. specialize (Hb mo H). lia.
Qed.

End Bridges.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition nretA (ms : machine_state) (eff : SyscallEffect) : machine_state := advance_past_svc (apply_effect ms eff).

Definition io_eff (eff : SyscallEffect) : Prop := eff_zeros eff = [] /\ eff_unmaps eff = [] /\ eff_copies eff = [].

Lemma ranges_avoid_cons_inv : forall H a n l, ranges_avoid H ((a, n) :: l) -> range_avoids H a n /\ ranges_avoid H l.
Proof. intros H a n l Hav. split; [apply Hav; left; reflexivity| intros a' n' Hin; apply Hav; right; exact Hin]. Qed.

Lemma ranges_avoid_app_inv : forall H l1 l2, ranges_avoid H (l1 ++ l2) -> ranges_avoid H l1 /\ ranges_avoid H l2.
Proof. intros H l1 l2 Hav. split; intros a n Hin; apply Hav; apply in_or_app; auto. Qed.

Lemma apply_writes_restrict : forall H ws m,
  ranges_avoid H (write_accesses ws) -> apply_writes (mrestrict H m) ws = mrestrict H (apply_writes m ws).
Proof.
  intros H. induction ws as [|[a bs] ws IH]; intros m Hav; [reflexivity|].
  cbn [apply_writes write_accesses] in *. apply ranges_avoid_cons_inv in Hav as [Ha Hr].
  rewrite (write_to_mem_restrict H bs m a Ha). apply IH. exact Hr.
Qed.

Lemma apply_writes_hidden : forall H ws m x,
  ranges_avoid H (write_accesses ws) -> H x = true -> apply_writes m ws x = m x.
Proof.
  intros H. induction ws as [|[a bs] ws IH]; intros m x Hav Hx; [reflexivity|].
  cbn [apply_writes write_accesses] in *. apply ranges_avoid_cons_inv in Hav as [Ha Hr].
  rewrite (IH _ x Hr Hx). exact (write_to_mem_hidden H bs m a x Ha Hx).
Qed.

Lemma ranges_avoid_writes : forall H eff, ranges_avoid H (syscall_effect_accesses eff) -> ranges_avoid H (write_accesses (eff_writes eff)).
Proof. intros H eff Hav. unfold syscall_effect_accesses in Hav. apply ranges_avoid_app_inv in Hav. tauto. Qed.

Lemma nretA_mem_io : forall ms eff, io_eff eff -> ms_mem (nretA ms eff) = apply_writes (ms_mem ms) (eff_writes eff).
Proof. intros ms [r ws zs us cs ci] (Hz & Hu & Hc). cbn in Hz, Hu, Hc. subst. reflexivity. Qed.

Lemma restrict_nretA_io : forall H ms eff, io_eff eff -> ranges_avoid H (syscall_effect_accesses eff) ->
  restrict H (nretA ms eff) = nretA (restrict H ms) eff.
Proof.
  intros H ms eff Hio Hav. pose proof (ranges_avoid_writes H eff Hav) as Hw.
  destruct ms, eff as [r ws zs us cs ci]. destruct Hio as (Hz & Hu & Hc). cbn in Hz, Hu, Hc. subst.
  unfold restrict, nretA, advance_past_svc, apply_effect. cbn. f_equal.
  symmetry. apply apply_writes_restrict. exact Hw.
Qed.

(* [comment removed for export] *)
Definition vm_same (mo mo' : Model) : Prop :=
  m_vmmaps mo' = m_vmmaps mo /\ m_vm_lazy mo' = m_vm_lazy mo /\ m_vm_materialized mo' = m_vm_materialized mo
  /\ m_halted mo' = m_halted mo.

Lemma eager_used_vm_same : forall mo mo', vm_same mo mo' -> eager_used mo' = eager_used mo.
Proof. intros mo mo' (H1 & H2 & _). unfold eager_used. rewrite H1, H2. reflexivity. Qed.

Lemma macct_vm_same : forall segtop A mo mo', vm_same mo mo' -> macct segtop A mo -> macct segtop A mo'.
Proof.
  intros segtop A mo mo' Hv (H1 & H2 & H3 & H4 & H5). pose proof Hv as (Hvm & Hlz & Hmt & Hh).
  split; [exact H1|]. split; [|rewrite Hlz, Hh; auto].
  apply (MInv_transport A mo mo' H2 Hmt Hlz). rewrite (eager_used_vm_same mo mo' Hv), Hvm. apply H2.
Qed.

Section SyscallNodeU.
Variable segs : list Segment.
Variable H : word -> bool.
Theorem node_syscall_restricted_u :
  forall A ms model x8 (I : Type)
         (eff : I -> SyscallEffect) (mdl : I -> Model) (evs : I -> list event),
  A_wf A ->
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  (forall i, syscall_spec (sys_input segs ms x8) model (Ok (eff i) (mdl i) (evs i))) ->
  (forall r, syscall_spec (sys_input segs ms x8) model r ->
             exists i, r = Ok (eff i) (mdl i) (evs i)) ->
  (forall i, m_halted (mdl i) = None) ->
  (forall i, lazy_cover H (m_vm_lazy (mdl i)) A) ->
  (forall i, MInv A (mdl i)) ->
  (forall i, ranges_avoid H (syscall_effect_accesses (eff i))) ->
  (forall i, MInv A (materialized_succ (mdl i) (syscall_effect_accesses (eff i)))
             /\ same_but_materialized (mdl i)
                  (materialized_succ (mdl i) (syscall_effect_accesses (eff i))))
  /\ node_ok_u segs (mkCfg ms model) I evs
       (fun i => mkCfg (advance_past_svc (apply_effect ms (eff i)))
                       (materialized_succ (mdl i) (syscall_effect_accesses (eff i)))).
Proof.
  intros A ms model x8 I eff mdl evs Hwf Hh Hsvc Hsound Hcompl Hnh Hcov Hinv Hav.
  assert (Hmat : forall i, exists mat',
            materialize_model_accesses (mdl i) (syscall_effect_accesses (eff i))
              = Some (with_vm_backing (m_vm_lazy (mdl i)) mat' (mdl i))
            /\ MInv A (with_vm_backing (m_vm_lazy (mdl i)) mat' (mdl i))).
  { intros i. exact (materialize_restricted H A (mdl i) _ (Hcov i) Hwf (Hinv i) (Hav i)). }
  split.
  - intros i. destruct (Hmat i) as (mat' & Hm & Hinv').
    unfold materialized_succ. rewrite Hm. split; [exact Hinv' | apply with_vm_backing_same].
  - split.
    + intros i. destruct (Hmat i) as (mat' & Hm & Hinv').
      unfold materialized_succ. rewrite Hm.
      eapply sstep_syscall; [exact Hh | exact Hsvc | exact (Hsound i) | exact (Hnh i) | exact Hm].
    + intros e st Hss. inversion Hss; subst;
        match goal with
        | Hp : ms_svc_pending ms = None |- _ => rewrite Hsvc in Hp; discriminate
        | Hp : ms_svc_pending ms = Some ?x |- _ =>
            rewrite Hsvc in Hp; injection Hp as <-
        end;
        match goal with
        | Hsp : syscall_spec _ _ ?r |- _ =>
            destruct (Hcompl _ Hsp) as [i Ei]; try discriminate Ei;
            injection Ei as -> -> ->
        end.
      * exists i. split; [reflexivity|].
        unfold materialized_succ.
        match goal with Hm : materialize_model_accesses _ _ = Some _ |- _ => rewrite Hm end.
        reflexivity.
      * destruct (Hmat i) as (mat' & Hm & _).
        match goal with Hn : materialize_model_accesses _ _ = None |- _ => rewrite Hm in Hn; discriminate end.
      * match goal with Hc : m_halted (mdl i) = Some _ |- _ => rewrite (Hnh i) in Hc; discriminate end.
      * match goal with Hk : m_killed (mdl i) = Some _ |- _ =>
          rewrite (m_killed_of_m_halted_none _ (Hnh i)) in Hk; discriminate end.
Qed.
End SyscallNodeU.
Lemma node_ok_single : forall segs c (evs : unit -> list event) (nx : unit -> config),
  node_ok_u segs c unit evs nx -> m_halted (cfg_model (nx tt)) = None -> node_ok segs c unit evs nx.
Proof.
  intros segs c evs nx Hu Hh. destruct (child_refusal_b segs c (nx tt)) eqn:E.
  - apply node_ok_forced; [exact Hu| intros []; exact Hh| intros []; exact E].
  - apply node_ok_no_refusals; [exact Hu| intros []; exact E].
Qed.

Section IONode.
Variable segs : list Segment.
Variable segtop : Z.
Hypothesis Hwx : wx_segs_nowrap segs.
Hypothesis Hsegs : segs_below_b segs segtop = true.

(* [comment removed for export] *)
Theorem ast_node_core_u : forall A Pm PM (I : Type) (evs : I -> list event)
    (K : I -> machine_state -> Prop) (KM : I -> Model -> Prop) ms mo x8
    (eff : I -> SyscallEffect) (mdl : I -> Model),
  AST segtop A Pm PM (mkCfg ms mo) ->
  ms_svc_pending ms = Some x8 ->
  (forall i, syscall_spec (sys_input segs ms x8) mo (Ok (eff i) (mdl i) (evs i))) ->
  (forall r, syscall_spec (sys_input segs ms x8) mo r -> exists i, r = Ok (eff i) (mdl i) (evs i)) ->
  (forall i, vm_same mo (mdl i)) ->
  (forall i, io_eff (eff i)) ->
  (forall i, ranges_avoid (HID A mo) (syscall_effect_accesses (eff i))) ->
  (forall i, K i (nretA (restrict (HID A mo) ms) (eff i))) ->
  (forall i, KM i (mdl i)) ->
  (forall i, mat_stable (KM i)) ->
  exists nx : I -> config, node_ok_u segs (mkCfg ms mo) I evs nx /\ (forall i, m_halted (cfg_model (nx i)) = None)
    /\ (forall i, cfg_ms (nx i) = nretA ms (eff i))
    /\ (forall i, AST segtop A (K i) (KM i) (nx i)).
Proof.
  intros A Pm PM I evs K KM ms mo x8 eff mdl Hc Hsvc Hsound Hcompl Hvm Hio Hav HK HKM Hms.
  destruct Hc as (Hmc & HPm & HPMmo & HZ0). cbn [cfg_ms cfg_model] in *.
  pose proof Hmc as (HAwf & HMInv & Hh & Hr & Ht).
  set (H := HID A mo) in *.
  assert (Hcov : forall i, lazy_cover H (m_vm_lazy (mdl i)) A).
  { intros i. destruct (Hvm i) as (_ & Hlz & _). rewrite Hlz. apply HID_cover. }
  assert (Hinv : forall i, MInv A (mdl i)) by (intros i; exact (proj1 (proj2 (macct_vm_same segtop A mo (mdl i) (Hvm i) Hmc)))).
  assert (Hnh : forall i, m_halted (mdl i) = None) by (intros i; destruct (Hvm i) as (_ & _ & _ & ->); exact Hh).
  destruct (node_syscall_restricted_u segs H A ms mo x8 I eff mdl evs HAwf Hh Hsvc Hsound Hcompl Hnh Hcov Hinv Hav)
    as [Hpost Hnode].
  eexists. split; [exact Hnode|].
  split.
  { intros i. cbn [cfg_model]. destruct (Hpost i) as [_ Hsame].
    pose proof (same_but_materialized_frame _ _ Hsame) as Fr.
    destruct Fr as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hhh & _). rewrite Hhh. exact (Hnh i). }
  split; [intros i; reflexivity|].
  intros i. destruct (Hpost i) as [HMInv' Hsame].
  set (mo' := materialized_succ (mdl i) (syscall_effect_accesses (eff i))) in *.
  assert (Hmc' : macct segtop A mo') by (apply (macct_same segtop A (mdl i) mo' Hsame HMInv'); apply (macct_vm_same segtop A mo); [exact (Hvm i)| exact Hmc]).
  assert (HH' : HID A mo' = H).
  { rewrite (HID_same A (mdl i) mo' Hsame). unfold HID, H. destruct (Hvm i) as (_ & -> & _). reflexivity. }
  split; [exact Hmc'|]. cbn [cfg_ms cfg_model]. rewrite HH'.
  change (advance_past_svc (apply_effect ms (eff i))) with (nretA ms (eff i)).
  rewrite (restrict_nretA_io H ms (eff i) (Hio i) (Hav i)).
  split; [exact (HK i)|]. split; [exact (Hms i _ _ Hsame (HKM i))|].
  intros a Ha Hna. cbn [cfg_ms cfg_model] in *.
  pose proof (same_but_materialized_frame (mdl i) mo' Hsame) as Fr. destruct Fr as (_ & Hvm' & Hlz' & _).
  rewrite Hvm' in Hna. destruct (Hvm i) as (Hvmi & Hlzi & _). rewrite Hvmi in Hna. rewrite Hlz', Hlzi in Ha.
  rewrite nretA_mem_io by exact (Hio i).
  rewrite (apply_writes_hidden H _ _ a (ranges_avoid_writes H _ (Hav i)) (HID_of_mkH A mo a Ha)).
  exact (HZ0 a Ha Hna).
Qed.
Theorem ast_node_core : forall A Pm PM (I : Type) (evs : I -> list event)
    (K : I -> machine_state -> Prop) (KM : I -> Model -> Prop) ms mo x8
    (eff : I -> SyscallEffect) (mdl : I -> Model),
  AST segtop A Pm PM (mkCfg ms mo) ->
  ms_svc_pending ms = Some x8 ->
  alloc_no_b (bv_unsigned x8) = false ->
  (forall i, syscall_spec (sys_input segs ms x8) mo (Ok (eff i) (mdl i) (evs i))) ->
  (forall r, syscall_spec (sys_input segs ms x8) mo r -> exists i, r = Ok (eff i) (mdl i) (evs i)) ->
  (forall i, vm_same mo (mdl i)) ->
  (forall i, io_eff (eff i)) ->
  (forall i, ranges_avoid (HID A mo) (syscall_effect_accesses (eff i))) ->
  (forall i, K i (nretA (restrict (HID A mo) ms) (eff i))) ->
  (forall i, KM i (mdl i)) ->
  (forall i, mat_stable (KM i)) ->
  exists nx : I -> config, node_ok segs (mkCfg ms mo) I evs nx /\ (forall i, AST segtop A (K i) (KM i) (nx i)).
Proof.
  intros A Pm PM I evs K KM ms mo x8 eff mdl Hc Hsvc Hnalloc Hsound Hcompl Hvm Hio Hav HK HKM Hms.
  destruct (ast_node_core_u A Pm PM I evs K KM ms mo x8 eff mdl Hc Hsvc Hsound Hcompl Hvm Hio Hav HK HKM Hms)
    as (nx & Hnode & _ & _ & Hnx).
  exists nx. split; [|exact Hnx].
  apply node_ok_of_u; [exact (kit_pending_on_sysno segs ms mo x8 _ Hsvc eq_refl Hnalloc)| exact Hnode].
Qed.
Theorem ast_node_core1 : forall A Pm PM (K : machine_state -> Prop) (KM : Model -> Prop) ms mo x8 eff mdl,
  AST segtop A Pm PM (mkCfg ms mo) ->
  ms_svc_pending ms = Some x8 ->
  (forall r, syscall_spec (sys_input segs ms x8) mo r <-> r = Ok eff mdl []) ->
  vm_same mo mdl -> io_eff eff -> ranges_avoid (HID A mo) (syscall_effect_accesses eff) ->
  K (nretA (restrict (HID A mo) ms) eff) -> KM mdl -> mat_stable KM ->
  exists nx : unit -> config, node_ok segs (mkCfg ms mo) unit (fun _ => []) nx /\ AST segtop A K KM (nx tt).
Proof.
  intros A Pm PM K KM ms mo x8 eff mdl Hc Hsvc Hchar Hvm Hio Hav HK HKMm HKM.
  destruct (ast_node_core_u A Pm PM unit (fun _ => []) (fun _ => K) (fun _ => KM) ms mo x8
             (fun _ => eff) (fun _ => mdl) Hc Hsvc) as (nx & Hnd & Hnh & _ & Hnx).
  - intros []. apply Hchar. reflexivity.
  - intros r Hr. exists tt. apply Hchar. exact Hr.
  - intros []. exact Hvm.
  - intros []. exact Hio.
  - intros []. exact Hav.
  - intros []. exact HK.
  - intros []. exact HKMm.
  - intros []. exact HKM.
  - exists nx. split; [exact (node_ok_single segs _ _ nx Hnd (Hnh tt))| exact (Hnx tt)].
Qed.

(* [comment removed for export] *)
Theorem ast_nodeI : forall A Pm PM (I : Type) (i0 : I) (evs : I -> list event)
    (K : I -> machine_state -> Prop) (KM : I -> Model -> Prop) (T : I -> TSet) ms mo x8
    (eff : I -> SyscallEffect) (mdl : I -> Model),
  AST segtop A Pm PM (mkCfg ms mo) ->
  ms_svc_pending ms = Some x8 ->
  alloc_no_b (bv_unsigned x8) = false ->
  (forall i, syscall_spec (sys_input segs ms x8) mo (Ok (eff i) (mdl i) (evs i))) ->
  (forall r, syscall_spec (sys_input segs ms x8) mo r -> exists i, r = Ok (eff i) (mdl i) (evs i)) ->
  (forall i, vm_same mo (mdl i)) ->
  (forall i, io_eff (eff i)) ->
  (forall i, ranges_avoid (HID A mo) (syscall_effect_accesses (eff i))) ->
  (forall i, K i (nretA (restrict (HID A mo) ms) (eff i))) ->
  (forall i, KM i (mdl i)) ->
  (forall i, mat_stable (KM i)) ->
  (forall i c', AST segtop A (K i) (KM i) c' -> realizes segs c' (T i)) ->
  realizes segs (mkCfg ms mo) (t_alt (fun i => t_emit (evs i) (T i))).
Proof.
  intros A Pm PM I i0 evs K KM T ms mo x8 eff mdl Hc Hsvc Hnalloc Hsound Hcompl Hvm Hio Hav HK HKM Hms Hk.
  destruct (ast_node_core A Pm PM I evs K KM ms mo x8 eff mdl Hc Hsvc Hnalloc Hsound Hcompl Hvm Hio Hav HK HKM Hms)
    as (nx & Hnode & Hnx).
  apply (rz_node segs _ I evs nx T i0 Hnode). intros i. exact (Hk i (nx i) (Hnx i)).
Qed.

End IONode.
