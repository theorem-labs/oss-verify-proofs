(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import String ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState ITree Nodes RelSpec Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad MSafe STree Malloc. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require KInv__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Inv. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Cnt__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_Inv. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_Quant. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_XferF__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Realloc2__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require ProgFullQ HeapFull Fmt StdioCore Stdio. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Pcap Prog. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MSafe OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.MallocRe OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.KLink OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Inv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Cnt__Spec.MI_Cnt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.LB_Tables OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_Inv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Cnt__Spec.LB_Sum OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_Quant OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_XferF__Spec.LB_StmtA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Realloc2__Spec.ProgFull OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.ProgFullQ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.HeapFull OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.Driver OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.Adapter OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv Require SimW HeapSim NodeSim ProgSim USim. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv Require SimStdio__Equiv. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv Require UFile UBase. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv Require UNodes__Equiv. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv Require UStdio UFmt. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.SimW OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.HeapSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.NodeSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.ProgSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.USim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.SimStdio__Equiv.SimStdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.SimStdio__Equiv.SimDriver OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.UFile OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.UBase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.UNodes__Equiv.UNodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.UStdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.UFmt.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

#[local] Notation PS := (PState fheap hptr).
#[local] Notation idl := (fun l : libc_st hptr => l).

(* [comment removed for export] *)
Section WithCeil.
(* [comment removed for export] *)
Context {CEG CEC : CEIL}.
#[local] Notation fopsG := (full_ops (CE:=CEG)).
#[local] Notation fopsC := (full_ops (CE:=CEC)).
Definition ARGMAX : Z := 131071.

Section UDriver.
Variable segs : list Segment.
Variables (stkG stkC : stack_site -> Z).
#[local] Notation npk := (npeek segs).
#[local] Notation usimS := (usim npk).
#[local] Notation RX := (UBase.RX (CEG:=CEG) (CEC:=CEC)).     (* [comment removed for export] *)
#[local] Notation RUK tm nx K C g W := (RX tm nx (UK nx K C g W)).
#[local] Notation W0 := (WF None [] []).
#[local] Notation runG := (Prog.run fopsG fo_nop stkG).
#[local] Notation runC := (Prog.run fopsC fo_nop stkC).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition exit_ok (K : list kfe) : Prop := forall e h, In e K -> k_own e = Some h -> k_kind e = KNull /\ k_data e = None.

(* [comment removed for export] *)
Hypothesis us_run : forall tm nx config payload,
  zlen (sizes tm) <= 1 -> R63N (sizes tm) <= B26 -> zlength payload < MAX_INPUT ->
  usimS (RUK tm nx [] [] idl W0) (runG config payload) (runC config payload)
        (eqpost (fun _ => fun sG moG sC moC => exists tm' nx' K' C' oh' hs' F',
                   EXT tm tm' /\ PHI P9 + R63N (sizes tm') <= BLIVE /\ exit_ok K' /\
                   RUK tm' nx' K' C' idl (WF oh' hs' F') sG moG sC moC)).

(* [comment removed for export] *)
#[using="Type"] Lemma RUK_lift tm nb nx' K C g W sG moG sC moC :
  RX tm nx' (UK nb K C g W) sG moG sC moC -> (nb <= nx')%N -> RX tm nx' (UK nx' K C g W) sG moG sC moC.
Proof. intros [HR [HF HW]] LE. split; [exact HR|]. split; [exact (FI_mono_nx _ _ _ _ _ _ LE HF)| exact HW]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma Forall_lt_of_le B (ps : list (list Z)) : B < 2^61 -> Forall (fun p => zlength p <= B) ps -> Forall (fun p => zlength p < 2^61) ps.
Proof. intros HB H. eapply Forall_impl; [| exact H]. cbn. intros; lia. Qed.

#[using="Type"] Lemma us_diag tm nx K C oh hs F d :
  match d with DUsage a | DCannotOpen a | DReadError a => zlength a <= ARGMAX | _ => True end ->
  usimS (RUK tm nx K C idl (WF oh hs F)) (Prog.diag d : Monad.M PS unit) (Prog.diag d) (eqpost (fun _ => RUK tm nx K C idl (WF oh hs F))).
Proof.
  intros Hd. destruct d; cbn [Prog.diag]; unfold diag_usage, diag_cannot_open, diag_read_error, diag_oom, diag_too_big, diag_short_hdr, diag_cfg_overrun.
  - apply us_eprintf. apply (Forall_lt_of_le ARGMAX); [unfold ARGMAX; lia|]. unfold pieces_usage. apply pieces_small; [unfold ARGMAX; lia| items_small_tac| args_small_tac].
  - apply us_eprintf. apply (Forall_lt_of_le ARGMAX); [unfold ARGMAX; lia|]. unfold pieces_cannot_open. apply pieces_small; [unfold ARGMAX; lia| items_small_tac| args_small_tac].
  - apply us_eprintf. apply (Forall_lt_of_le ARGMAX); [unfold ARGMAX; lia|]. unfold pieces_read_error. apply pieces_small; [unfold ARGMAX; lia| items_small_tac| args_small_tac].
  - apply us_efwrite. vm_compute. reflexivity.
  - apply us_eprintf. apply (Forall_lt_of_le 64); [lia|]. unfold pieces_too_big. apply pieces_small; [lia| items_small_tac| args_small_tac].
  - apply us_efwrite. vm_compute. reflexivity.
  - apply us_efwrite. vm_compute. reflexivity.
Qed.

#[using="Type"] Lemma us_emit_d tm nx K C oh hs F rc :
  usimS (RUK tm nx K C idl (WF oh hs F)) (emit_d ps_libc set_libc rc : Monad.M PS unit) (emit_d ps_libc set_libc rc) (eqpost (fun _ => RUK tm nx K C idl (WF oh hs F))).
Proof.
  unfold emit_d. apply us_printf. apply (Forall_lt_of_le 64); [lia|]. unfold pieces_emit_d. apply pieces_small; [lia| items_small_tac| args_small_tac].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
#[local] Notation read_loop_bodyG := (read_loop_body (@Prog.diag fheap hptr) (pmalloc fopsG) (pfree fopsG) (stkG SiteReadStage)).
#[local] Notation read_loop_bodyC := (read_loop_body (@Prog.diag fheap hptr) (pmalloc fopsC) (pfree fopsC) (stkC SiteReadStage)).
#[local] Notation read_allG := (read_all (@Prog.diag fheap hptr) (pmalloc fopsG) (pfree fopsG) (stkG SiteReadStage)).
#[local] Notation read_allC := (read_all (@Prog.diag fheap hptr) (pmalloc fopsC) (pfree fopsC) (stkC SiteReadStage)).

(* [comment removed for export] *)
#[using="Type"] Lemma ruk_useR {A} tm nx K C W (m m' : Monad.M PS A) Q :
  (forall sG moG sC moC, RQ (CEG:=CEG) (CEC:=CEC) P9 LCI tm nx sG moG sC moC -> usimS (RUK tm nx K C idl W) m m' Q) -> usimS (RUK tm nx K C idl W) m m' Q.
Proof. intros H. apply ru_use. intros ? ? ? ? [HR _]. exact (H _ _ _ _ HR). Qed.

Definition RDpostU (e : kfe) (st : @rd_st hptr) (r : @rd_st hptr + @rd_result hptr) : @rel PS PS := fun sG moG sC moC =>
  exists tm' nx', RUK tm' nx' [e] [] idl W0 sG moG sC moC /\
  match r with
  | inl st' => RD st' tm' /\ rd_len st < rd_len st'
  | inr RdExit => True
  | inr (RdDone buf content) => exists cap, tm' = {[ buf := cap ]} /\ zlength content < cap <= MAX_INPUT
  end.

#[using="Type"] Lemma us_read_loop_body e path nx st tm :
  k_own e = None -> k_data e = None -> zlength path <= ARGMAX ->
  RD st tm ->
  usimS (RUK tm nx [e] [] idl W0) (read_loop_bodyG (k_fd e) path st) (read_loop_bodyC (k_fd e) path st) (eqpost (RDpostU e st)).
Proof.
  intros Ho ED Hpath HRD. pose proof HRD as (Etm & Hcap & Hlen & Hcont & kc & Hk & Ek). unfold read_loop_body. cbv zeta.
  apply ruk_useR. intros sG0 moG0 sC0 moC0 HR0. pose proof (RQ_fresh P9 LCI tm nx _ _ _ _ HR0) as FR. clear HR0 sG0 moG0 sC0 moC0.
  assert (NEb : rd_buf st <> nx) by (intros E; rewrite <- E, Etm in FR; apply lookup_singleton_None in FR; exact (FR eq_refl)).
  (* [comment removed for export] *)
  eapply (ru_bind2 segs) with (Q1 := fun g g' => fun sG moG sC moC => g = g' /\ exists tm' nx',
      RUK tm' nx' [e] [] idl W0 sG moG sC moC /\ match g with None => True | Some st1 => RD st1 tm' /\ rd_len st1 = rd_len st /\ rd_len st1 < rd_cap st1 /\ rd_content st1 = rd_content st /\ rd_cap st <= rd_cap st1 end).
  { destruct (rd_len st =? rd_cap st) eqn:EL.
    - apply Z.eqb_eq in EL. destruct (MAX_INPUT <=? rd_cap st) eqn:EM.
      + eapply ru_bind2; [apply us_diag; exact I|]. intros [] []. apply usim_pure; intros _.
        apply usim_ret. intros ? ? ? ? HR. split; [reflexivity|]. exists tm, nx. split; [exact HR| exact I].
      + apply Z.leb_gt in EM. destruct (cap_double _ _ Hk Ek EM) as [C2 E2].
        destruct (RD_budget st tm (rd_cap st * 2) HRD ltac:(lia)) as (R1 & R2 & R3).
        eapply ru_bind2; [apply (ru_pmalloc (CEG:=CEG) (CEC:=CEC) segs tm nx _ _ (rd_cap st * 2) (UK_stable _ _ _ _ _)); [lia| unfold size_overflows; apply Z.leb_gt; unfold MAX_INPUT in *; lia| exact R3| exact R1| exact R2]|].
        intros a b. apply usim_pure; intros <-. apply usim_pure; intros ->.
        assert (Hold : <[nx := rd_cap st * 2]> tm !! rd_buf st = Some (rd_cap st)).
        { rewrite lookup_insert_ne by (intros E; exact (NEb (eq_sym E))). rewrite Etm. apply lookup_singleton_eq. }
        eapply ru_bind2.
        { apply (ru_pfree (CEG:=CEG) (CEC:=CEC) segs _ (N.succ nx) _ _ (rd_buf st) (rd_cap st) (UK_stable _ _ _ _ _) Hold).
          rewrite (R63N_insert tm nx _ FR). rewrite PHI_P9. rewrite Etm, sizes_single. unfold R63N. cbn [zsum map fold_right].
          pose proof (bigb_B26 (rd_cap st) ltac:(lia)). pose proof (bigb_B26 (rd_cap st * 2) ltac:(lia)). unfold B26, BLIVE, PGSZ in *. lia. }
        intros [] []. cbn beta. apply usim_pure; intros _. apply usim_ret. intros ? ? ? ? HR. split; [reflexivity|]. exists (delete (rd_buf st) (<[nx := rd_cap st * 2]> tm)), (N.succ nx).
        split; [exact (RUK_lift _ _ _ _ _ _ _ _ _ _ _ HR ltac:(lia))|].
        assert (EC : rd_content (mkRd nx (rd_cap st * 2) (rd_len st) (rd_chunks st)) = rd_content st) by reflexivity.
        unfold RD. cbn [rd_buf rd_cap rd_len rd_chunks]. rewrite EC.
        split; [| repeat split; lia].
        split; [| split; [lia| split; [lia| split; [exact Hcont| exists (kc + 1); split; [lia| exact E2]]]]].
        rewrite delete_insert_ne by exact NEb. rewrite Etm. rewrite delete_singleton_eq. reflexivity.
    - apply Z.eqb_neq in EL. apply usim_ret. intros ? ? ? ? HR. split; [reflexivity|]. exists tm, nx. split; [exact HR|]. split; [exact HRD|]. repeat split; lia.
  }
  intros g g'. apply usim_pure; intros <-. destruct g as [st1|].
  2:{ apply usim_exI; intros tm'. apply usim_exI; intros nx'. eapply ru_pre; [| intros ? ? ? ? [H _]; exact H].
      apply usim_ret. intros ? ? ? ? HR. split; [reflexivity|]. exists tm', nx'. split; [exact HR| exact I]. }
  apply usim_exI; intros tm1. apply usim_exI; intros nx1.
  eapply (ru_pre segs _ (fun sG moG sC moC => (RD st1 tm1 /\ rd_len st1 = rd_len st /\ rd_len st1 < rd_cap st1 /\ rd_content st1 = rd_content st /\ rd_cap st <= rd_cap st1) /\ RUK tm1 nx1 [e] [] idl W0 sG moG sC moC));
    [| intros ? ? ? ? [H1 H2]; split; [exact H2| exact H1]].
  apply usim_pure. intros (HRD1 & EL1 & LT1 & EC1 & LC1). pose proof HRD1 as (Etm1 & Hcap1 & Hlen1 & Hcont1 & k1 & Hk1 & Ek1).
  (* [comment removed for export] *)
  eapply ru_bind2; [apply ru_get|]. intros sG sC. apply usim_pointwise. intros ? ? ? ? (-> & -> & EL & EO & HRQ).
  eapply ru_pre; [| intros ? ? ? ? (-> & -> & -> & ->); exact HRQ]. cbv zeta.
  set (want := if READ_CHUNK <? rd_cap st1 - rd_len st then READ_CHUNK else rd_cap st1 - rd_len st) in *.
  assert (Hwant : 0 <= want <= rd_cap st1 - rd_len st) by (subst want; unfold READ_CHUNK; destruct (65536 <? rd_cap st1 - rd_len st) eqn:E'; [apply Z.ltb_lt in E'| apply Z.ltb_ge in E']; lia).
  eapply ru_bind.
  { eapply ru_post; [apply ru_read; eapply (unode_lift _ _ (FI nx1 [e] []) _ idl W0); apply (fn_read nx1 [e] [] e _ want ltac:(left; reflexivity)); unfold MAX_INPUT in *; lia|].
    intros a ? ? ? ? [HR [RP HW]]. instantiate (1 := fun a => fun sG moG sC moC => match a with RdErr _ => True | RdData bs => Z.of_nat (length bs) <= want end /\ RUK tm1 nx1 [e] [] idl W0 sG moG sC moC).
    cbn beta. destruct a as [err|bs]; cbn in RP.
    - split; [exact I|]. split; [exact HR|]. split; [exact (proj2 RP)| exact HW].
    - destruct RP as (_ & LEB & RP). rewrite ED in RP. split; [exact LEB|]. split; [exact HR|]. split; [exact RP| exact HW]. }
  intros a. cbv beta. apply usim_pure. intros HL0.
  destruct a as [err|bs].
  - eapply ru_bind2; [apply us_diag; exact Hpath|]. intros [] []. apply usim_pure; intros _.
    apply usim_ret. intros ? ? ? ? HR. split; [reflexivity|]. exists tm1, nx1. split; [exact HR| exact I].
  - assert (HL : zlength (of_bytes bs) = Z.of_nat (length bs)) by (unfold zlength, of_bytes; rewrite length_map; reflexivity).
    assert (HLb : zlength bs = Z.of_nat (length bs)) by reflexivity.
    destruct (length bs =? 0)%nat eqn:EB.
    + apply usim_ret. intros ? ? ? ? HR. split; [reflexivity|]. exists tm1, nx1. split; [exact HR|]. exists (rd_cap st1). split; [exact Etm1| rewrite Hcont1; lia].
    + apply Nat.eqb_neq in EB. apply usim_ret. intros ? ? ? ? HR. split; [reflexivity|]. exists tm1, nx1. split; [exact HR|]. split; [| cbn [rd_len]; lia].
      unfold RD. cbn [rd_cap rd_len rd_buf rd_chunks]. split; [exact Etm1|]. split; [lia|].
      split; [lia|]. split; [rewrite rd_content_app, OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.SimStdio__Equiv.SimDriver.zlength_app, Hcont1; lia| exists k1; auto].
Qed.

(* [comment removed for export] *)
Definition RLpostU (e : kfe) (r : @rd_result hptr) : @rel PS PS := fun sG moG sC moC =>
  exists tm' nx', RUK tm' nx' [e] [] idl W0 sG moG sC moC /\
  match r with
  | RdExit => True
  | RdDone buf content => exists cap, tm' = {[ buf := cap ]} /\ zlength content < cap <= MAX_INPUT
  end.

(* [comment removed for export] *)
Definition RApostU (r : @rd_result hptr) : @rel PS PS := fun sG moG sC moC =>
  exists tm' nx' K', exit_ok K' /\ RUK tm' nx' K' [] idl W0 sG moG sC moC /\
  match r with
  | RdExit => True
  | RdDone buf content => K' = [] /\ exists cap, tm' = {[ buf := cap ]} /\ zlength content < cap <= MAX_INPUT
  end.

#[using="Type"] Lemma us_read_all nx path :
  zlength path <= ARGMAX ->
  usimS (RUK ∅ nx [] [] idl W0) (read_allG path) (read_allC path) (eqpost RApostU).
Proof.
  intros Hpath. unfold read_all.
  (* [comment removed for export] *)
  eapply ru_bind.
  { eapply ru_post; [apply (ruk_node (CEG:=CEG) (CEC:=CEC) segs ∅ nx [] [] idl W0 (NOpen (to_bytes path)) dec_open _ I (fn_open nx [] [] (to_bytes path) ltac:(intros ? [])))|].
    intros r ? ? ? ? [HR [X HW]].
    instantiate (1 := fun r => fun sG moG sC moC => match r with
      | SErr _ => RUK ∅ nx [] [] idl W0 sG moG sC moC
      | SVal fd => 3 <= fd <= 4096 /\ exists kd, kd <> KW /\ RUK ∅ nx [mkKfe fd kd (to_bytes path) None None 0] [] idl W0 sG moG sC moC end).
    cbn beta. destruct r as [err|fd].
    - split; [exact HR|]. split; [exact (proj1 X)| exact HW].
    - destruct X as (R & kd & NK & HF). split; [exact R|]. exists kd. split; [exact NK|]. split; [exact HR|]. split; [cbn in HF; unfold cdel in HF; cbn in HF; exact HF| exact HW]. }
  assert (XK0 : exit_ok []) by (intros ? ? [] _).
  intros r. cbv beta. destruct r as [err|fd].
  - eapply ru_bind2; [apply us_diag; exact Hpath|]. intros [] []. apply usim_pure; intros _.
    apply usim_ret. intros ? ? ? ? HR. split; [reflexivity|]. exists ∅, nx, []. split; [exact XK0|]. split; [exact HR| exact I].
  - apply usim_pure. intros Hfd. apply usim_exI. intros kd. apply usim_pure. intros NK.
    set (e := mkKfe fd kd (to_bytes path) None None 0).
    assert (XK1 : exit_ok [e]) by (intros x h [<-|[]] Ho; cbn in Ho; discriminate).
    eapply ru_bind2.
    { apply (ru_pmalloc (CEG:=CEG) (CEC:=CEC) segs ∅ nx _ _ 65536 (UK_stable _ _ _ _ _)); [lia| reflexivity| unfold bigb, MMAP_THRESHOLD, QMAX; cbn; lia| |].
      - apply (ROOMN_of_len P9). intros c. rewrite sizes_empty. unfold zlen, P9. cbn. lia.
      - rewrite sizes_empty, PHI_P9. unfold R63N, bigb, MMAP_THRESHOLD, BLIVE. cbn. lia. }
    intros b b'. apply usim_pure; intros <-. apply usim_pure; intros ->.
    eapply ru_bind2.
    { eapply usim_pre.
      - eapply usim_post.
        + apply (usim_loopV npk (npk_inh segs)
                 (fun (x y : @rd_st hptr) => fun sG moG sC moC => y = x /\ exists tm1 nx1, RD x tm1 /\ RUK tm1 nx1 [e] [] idl W0 sG moG sC moC)
                 (fun x n => (Z.to_nat (MAX_INPUT - rd_len x) < n)%nat)
                 (fun (a b : @rd_result hptr) => fun sG moG sC moC => b = a /\ RLpostU e a sG moG sC moC)).
          * intros x y n HV. apply usim_pure; intros ->. apply usim_exI; intros tm1. apply usim_exI; intros nx1. apply usim_pure; intros HRD.
            pose proof HRD as (_ & HcapX & HlenX & _).
            eapply usim_post; [apply (us_read_loop_body e path nx1 x tm1 eq_refl eq_refl Hpath HRD)|].
            intros [x'|a] [y'|b'] ? ? ? ? [E H]; try discriminate E.
            -- injection E as <-. destruct H as (tm' & nx' & HR & HRD' & LT). pose proof HRD' as (_ & Hcap' & Hlen' & _).
               split; [lia|]. split; [reflexivity|]. exists tm', nx'. split; assumption.
            -- injection E as <-. split; [reflexivity|]. destruct H as (tm' & nx' & HR & HP). exists tm', nx'. split; [exact HR|]. destruct a; [exact I| exact HP].
          * intros x H. lia.
          * unfold READ_FUEL, MAX_INPUT. cbn [rd_len]. lia.
        + intros a b' ? ? ? ? HH. exact HH.
      - intros ? ? ? ? HR. split; [reflexivity|]. exists (<[nx := 65536]> ∅), (N.succ nx). split; [| exact (RUK_lift _ _ _ _ _ _ _ _ _ _ _ HR ltac:(lia))].
        unfold RD. cbn [rd_buf rd_cap rd_len rd_chunks]. split; [rewrite insert_empty; reflexivity|]. unfold MAX_INPUT, rd_content, zlength. cbn. repeat split; try lia. exists 0. split; [lia| reflexivity]. }
    intros res res'. cbv beta. apply usim_pure; intros ->. destruct res as [|buf' content].
    + apply usim_exI; intros tm'. apply usim_exI; intros nx'. eapply ru_pre; [| intros ? ? ? ? [H _]; exact H].
      apply usim_ret. intros ? ? ? ? HR. split; [reflexivity|]. exists tm', nx', [e]. split; [exact XK1|]. split; [exact HR| exact I].
    + apply usim_exI; intros tm'. apply usim_exI; intros nx'.
      eapply (ru_pre segs _ (fun sG moG sC moC => (exists cap, tm' = {[buf' := cap]} /\ zlength content < cap <= MAX_INPUT) /\ RUK tm' nx' [e] [] idl W0 sG moG sC moC)); [| intros ? ? ? ? [H1 H2]; split; assumption].
      apply usim_pure; intros HC.
      change fd with (k_fd e).
      eapply (ruk_bind (CEG:=CEG) (CEC:=CEC) segs tm' nx' [e] [] idl W0 (fun _ => True) (fun _ => []) (fun _ => []) (fun _ => idl) (fun _ => W0)).
      { eapply ruk_nodeK; [exact I| apply (fn_close nx' [e] [] e ltac:(left; reflexivity))|].
        intros r l mo [_ HF]. split; [exact I|]. unfold lrem, cclose in HF. cbn in HF. rewrite Z.eqb_refl in HF. cbn in HF. exact HF. }
      intros r _. cbn beta. apply usim_ret. intros ? ? ? ? HR. split; [reflexivity|]. exists tm', nx', []. split; [exact XK0|]. split; [exact HR|]. split; [reflexivity| exact HC].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="us_run"] Theorem us_main_prog nx argv :
  Forall (fun a => zlength a <= ARGMAX) argv ->
  usimS (RUK ∅ nx [] [] idl W0) (main_prog fopsG fo_nop stkG argv) (main_prog fopsC fo_nop stkC argv)
        (eqpost (fun _ => fun sG moG sC moC => exists tm' nx' K' C' oh' hs' F', exit_ok K' /\ RUK tm' nx' K' C' idl (WF oh' hs' F') sG moG sC moC)).
Proof.
  intros Hargv. unfold main_prog, main_model.
  assert (A0 : zlength (nth 0 argv []) <= ARGMAX).
  { destruct argv as [|a0 ?]; cbn; [unfold zlength, ARGMAX; cbn; lia|]. apply Forall_cons_iff in Hargv as [H _]. exact H. }
  assert (A1 : zlength (nth 1 argv []) <= ARGMAX).
  { destruct argv as [|a0 [|a1 ?]]; cbn; [unfold zlength, ARGMAX; cbn; lia| unfold zlength, ARGMAX; cbn; lia|].
    apply Forall_cons_iff in Hargv as [_ H]. apply Forall_cons_iff in H as [H _]. exact H. }
  assert (XK0 : exit_ok []) by (intros ? ? [] _).
  destruct (negb (Z.of_nat (length argv) =? 2)).
  { eapply ru_bind2; [apply us_diag; exact A0|]. intros [] []. apply usim_pure; intros _. apply usim_ret. intros ? ? ? ? HR. split; [reflexivity|]. exists ∅, nx, [], [], None, [], []. exact (conj XK0 HR). }
  eapply ru_bind; [apply us_read_all; exact A1|]. intros ra.
  apply usim_exI; intros tm. apply usim_exI; intros nx1. apply usim_exI; intros K1. apply usim_pure; intros XK1.
  destruct ra as [|buf content].
  { eapply ru_pre; [| intros ? ? ? ? [H _]; exact H]. apply usim_ret. intros ? ? ? ? HR. split; [reflexivity|]. exists tm, nx1, K1, [], None, [], []. exact (conj XK1 HR). }
  eapply (ru_pre segs _ (fun sG moG sC moC => (K1 = [] /\ exists cap, tm = {[buf := cap]} /\ zlength content < cap <= MAX_INPUT) /\ RUK tm nx1 K1 [] idl W0 sG moG sC moC)); [| intros ? ? ? ? [H1 H2]; split; assumption].
  apply usim_pure. intros (-> & cap & -> & Hcap). cbv zeta.
  pose proof (bigb_B26 cap) as HB26.
  assert (BUD : zlen (sizes {[buf := cap]}) <= 1 /\ R63N (sizes {[buf := cap]}) <= B26 /\ PHI P9 + R63N (sizes {[buf := cap]}) <= BLIVE).
  { rewrite sizes_single. unfold zlen, R63N. cbn [length zsum map fold_right Z.of_nat]. rewrite PHI_P9.
    pose proof (zlen_nonneg content). specialize (HB26 ltac:(unfold zlength in *; lia)). unfold B26, BLIVE, PGSZ in *. repeat split; lia. }
  destruct BUD as (BUD1 & BUD2 & BUD3).
  assert (FREE : forall tm' nx' K' C' oh' hs' F', EXT {[buf := cap]} tm' -> PHI P9 + R63N (sizes tm') <= BLIVE ->
            usim npk (RUK tm' nx' K' C' idl (WF oh' hs' F')) (pfree fopsG buf) (pfree fopsC buf) (eqpost (fun _ => RUK (delete buf tm') nx' K' C' idl (WF oh' hs' F')))).
  { intros tm' nx' K' C' oh' hs' F' HE HB. apply (ru_pfree (CEG:=CEG) (CEC:=CEC) segs tm' nx' _ _ buf cap (UK_stable _ _ _ _ _)); [apply HE; apply lookup_singleton_eq| exact HB]. }
  destruct (zlength content <? HDR_MIN).
  { eapply ru_bind2; [apply us_diag; exact I|]. intros [] []. apply usim_pure; intros _.
    eapply ru_bind; [apply (FREE _ nx1 [] [] None [] []); [intros k n H; exact H| exact BUD3]|]. intros []. apply usim_ret. intros ? ? ? ? HR. split; [reflexivity|]. exists (delete buf {[buf := cap]}), nx1, [], [], None, [], []. exact (conj XK0 HR). }
  destruct (zlength content <? HDR_MIN + Z.land (le16 content) 32767).
  { eapply ru_bind2; [apply us_diag; exact I|]. intros [] []. apply usim_pure; intros _.
    eapply ru_bind; [apply (FREE _ nx1 [] [] None [] []); [intros k n H; exact H| exact BUD3]|]. intros []. apply usim_ret. intros ? ? ? ? HR. split; [reflexivity|]. exists (delete buf {[buf := cap]}), nx1, [], [], None, [], []. exact (conj XK0 HR). }
  eapply ru_bind.
  { apply us_run; [exact BUD1| exact BUD2|]. pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.SimStdio__Equiv.SimDriver.zlength_skipn (Z.to_nat (6 + Z.land (le16 content) 32767)) content). lia. }
  intros status. apply usim_exI; intros tm'. apply usim_exI; intros nx'. apply usim_exI; intros K'. apply usim_exI; intros C'.
  apply usim_exI; intros oh'. apply usim_exI; intros hs'. apply usim_exI; intros F'.
  eapply (ru_pre segs _ (fun sG moG sC moC => (EXT {[buf := cap]} tm' /\ PHI P9 + R63N (sizes tm') <= BLIVE /\ exit_ok K') /\ RUK tm' nx' K' C' idl (WF oh' hs' F') sG moG sC moC));
    [| intros ? ? ? ? (H1 & H2 & H3 & H4); split; [exact (conj H1 (conj H2 H3))| exact H4]].
  apply usim_pure. intros (HE & HB & XK).
  eapply ru_bind; [apply (FREE _ nx' K' C' oh' hs' F' HE HB)|]. intros []. apply usim_ret. intros ? ? ? ? HR. split; [reflexivity|]. exists (delete buf tm'), nx', K', C', oh', hs', F'. exact (conj XK HR).
Qed.
End UDriver.

End WithCeil.
