(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require PropExec__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require CatSim__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require StoreOk StepTac. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require RefLayout__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require ArgvEnv__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AsanAcct__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AllocSim MmapSim. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AsanHexScan__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require FileSim__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require RefNodes. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AllocSim2__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require SpinAlg. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AsanNodesMmLib AsanNodesLibE BackingAlgebra. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.CatExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.CatSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.SeqExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.StoreOk OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.StepTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.RefLayout__Common.AgentLib OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.ArgvEnv__Common.StartupAux OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.RefLayout__Common.RefLayout OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.ArgvEnv__Common.ArgvEnv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.ArgvEnv__Common.MemSplit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanAcct__Common.Hoare OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AllocSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.MmapSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanHexScan__Common.ExitSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanHexScan__Common.SimInv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.FileSim__Common.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.FileSim__Common.AgentNodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.RefNodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanHexScan__Common.AsanCeil OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AllocSim2__Common.ShapeAlg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanAcct__Common.ErrEscape OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.SpinAlg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.DivergeSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanAcct__Common.AsanAcct OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.RefLayout__Common.AsanAcctShape OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanNodesMmLib OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanNodesLibE OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.BackingAlgebra OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanHexScan__Common.AsanPlacement.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AxSymExec3 AxSymExec3Sound. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AxSymRun3__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AsanPlanCore AsanPlan. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AxSymExec3F. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3Sound OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymRun3__Common.AxSymRun3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanPlanCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanPlan OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymRun3__Common.KnApart OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3F.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require EntryKn StdioSymDrive EntryGlue. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require AsanBlock__Lib. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require NodesFs__Lib. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require NodesMmDrive__Lib. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require AsanKnow. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require AsanNodes__Lib. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require AsanNodesDrive AsanHeapKit. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.EntryKn OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.StdioSymDrive OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.EntryGlue OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBlock__Lib.MallocSymAux OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.NodesFs__Lib.NodesMm OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.NodesMmDrive__Lib.NodesMmDrive OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBlock__Lib.AsanBlock OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanKnow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanNodes__Lib.AsanNodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanNodesDrive OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanHeapKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require A3Img. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require A3Syms__A3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Img OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3Syms OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3SymsBoot.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require AsanBootKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require NodesMmDrive__Lib. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require AsanBlock__Lib. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require AsanNodes__Lib. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBootKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.NodesMmDrive__Lib.AsanBootKn OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBlock__Lib.AsanBootTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanNodes__Lib.AsanNodesBoot.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require A3Syms__A3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootImg. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootKn1__A3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require Boot1 Boot2 Boot3 BootS1. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require A3RW__A3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootS2. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3SymsBootW OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn1 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.Boot1 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.Boot2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.Boot3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootS1 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3RW__A3.BootLedgerA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootS2.
Import ListNotations.
Import AX2. Import AX2S.
#[local] Instance bootstate_fx : OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec.FPState := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec.fx0.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition dl (E : env) (l : sivs) : list (word * word) :=
  List.map (fun p => (edenot E (fst p), Z_to_bv 64 (snd p))) l.

(* [comment removed for export] *)
Record ledger : Type := Ledger {
  l_maps  : sivs;     (* [comment removed for export] *)
  l_brk   : Z;        (* [comment removed for export] *)
  l_eager : Z         (* [comment removed for export] *) }.

Definition sivs_vars_lt (n : nat) (l : sivs) : bool := forallb (fun p => expr_vars_lt n (fst p)) l.
Definition ledger_vars_lt (n : nat) (L : ledger) : bool := sivs_vars_lt n (l_maps L).

(* [comment removed for export] *)
Fixpoint ivs_apart (l : list (word * word)) : Prop :=
  match l with
  | [] => True
  | (b, n) :: r => Forall (fun q => bv_unsigned b + bv_unsigned n <= bv_unsigned (fst q)
                                  \/ bv_unsigned (fst q) + bv_unsigned (snd q) <= bv_unsigned b) r /\ ivs_apart r
  end.

Lemma lazy_sub_cover : forall H (l1 l2 : list (word * word)) A,
  (forall p, page_in_ranges p l1 = true -> page_in_ranges p l2 = true) ->
  lazy_cover H l2 A -> lazy_cover H l1 A.
Proof. intros H l1 l2 A Hs HC w Hp Hh. apply HC; [apply Hs; exact Hp | exact Hh]. Qed.

Lemma dl_app_env : forall vals extra ebs l,
  sivs_vars_lt (length vals) l = true ->
  dl (Env (vals_ev (vals ++ extra)) ebs) l = dl (Env (vals_ev vals) ebs) l.
Proof.
  intros vals extra ebs l. induction l as [|[e n] l IH]; cbn [dl List.map sivs_vars_lt forallb fst snd]; intros H; [reflexivity|].
  apply andb_prop in H as [He Hl]. rewrite (env_app_edenot vals extra ebs e He). f_equal. apply IH. exact Hl.
Qed.

(* [comment removed for export] *)
Definition FDS0 : list (word * FdEntry) :=
  [(Z_to_bv 64 0, FdChannel (Z_to_bv 64 0)); (Z_to_bv 64 1, FdChannel (Z_to_bv 64 1)); (Z_to_bv 64 2, FdChannel (Z_to_bv 64 2))].

(* [comment removed for export] *)
Definition na_clear_l (l : list (word * word)) : Prop := region_free l LO_A LO_N = true /\ region_free l HI_A HI_N = true.
Definition na_clear (mdl : Model) : Prop := na_clear_l (vm_noaccess (m_vmmaps mdl)).

Lemma region_free_maps_subtract : forall l lo hi (b n : word),
  ivs_wf l -> region_free l b n = true -> region_free (maps_subtract l lo hi) b n = true.
Proof.
  intros l lo hi b n Hwf Hrf. apply RefNodes.region_free_intro. intros qb qs Hq.
  destruct (maps_subtract_pieces l lo hi (qb, qs) Hwf Hq) as ([rb rs] & Hr & H1 & H2 & _). cbn [fst snd] in *.
  pose proof (RefNodes.region_free_In l b n rb rs Hrf Hr). lia.
Qed.

Lemma na_clear_l_sub : forall l lo hi, ivs_wf l -> na_clear_l l -> na_clear_l (maps_subtract l lo hi).
Proof. intros l lo hi Hwf [H1 H2]. split; apply region_free_maps_subtract; assumption. Qed.

Lemma na_clear_l_cons : forall l (a n : word),
  bv_unsigned a + bv_unsigned n <= SHB_LO \/ SHB_HI <= bv_unsigned a -> na_clear_l l -> na_clear_l ((a, n) :: l).
Proof.
  intros l a n Hap [H1 H2]. unfold na_clear_l. cbn [region_free]. rewrite H1, H2, !andb_true_r. unfold iv_overlap.
  assert (LA : bv_unsigned LO_A = 0x7fff7000) by (vmeq_refl).
  pose proof LO_N_val as LN. pose proof HI_A_val as HA. pose proof HI_N_val as HN. rewrite LA, LN, HA, HN. unfold SHB_LO, SHB_HI in Hap.
  pose proof (u64_range n). pose proof (u64_range a).
  split; apply negb_true_iff; apply andb_false_iff; destruct Hap; [left | right | left | right]; apply Z.ltb_ge; lia.
Qed.

Section Theorems.
  Variables (sp brk mbase : word) (draw : EntryDraw) (lim : Z) (inp : ProcInput).
  Hypothesis VI : valid_input inp.
  Hypothesis VE : valid_entry IMG (mkEntry sp brk mbase draw) inp.

  Let argv := in_argv inp.
  Let envp := in_envp inp.
  Let uid := in_uid inp.
  Let hw := in_hwcap inp.
  Let usp := bv_unsigned sp.

  #[using="brk mbase draw inp VI VE"] Lemma SL' : 0x7fff80000000 <= usp. Proof. exact (SL sp brk mbase draw inp VI VE). Qed.
  #[using="brk mbase draw inp VI VE"] Lemma SH' : usp <= 0x800000000000. Proof. exact (SH sp brk mbase draw inp VI VE). Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition VB (a tid c : word) (pl : placements) (js : list word) : list word :=
    vals0 PH sp draw argv envp uid hw ++ [a; tid; c] ++ pl_list pl ++ js.
  Definition EB (a tid c : word) (pl : placements) (js : list word) : env := Env (vals_ev (VB a tid c pl js)) (blobs0 draw argv).

  #[using="Type"] Lemma EB_EJ : forall a tid c pl js, EB a tid c pl js = EJ sp draw inp a tid c pl js.
  Proof. reflexivity. Qed.
  #[using="Type"] Lemma EB_app : forall a tid c pl js ks, EB a tid c pl (js ++ ks) = Env (vals_ev (VB a tid c pl js ++ ks)) (blobs0 draw argv).
  Proof. intros. unfold EB, VB. rewrite <- !app_assoc. reflexivity. Qed.
  #[using="Type"] Lemma ev_EB_sp : forall a tid c pl js, ev (EB a tid c pl js) 0%nat = sp. Proof. reflexivity. Qed.
  #[using="Type"] Lemma ev_EB_tls : forall a tid c pl js, ev (EB a tid c pl js) V_TLS = a. Proof. reflexivity. Qed.
  #[using="usp"] Lemma length_VB : forall a tid c pl js, length (VB a tid c pl js) = (16 + length js)%nat.
  Proof. intros. unfold VB. rewrite !length_app. cbn. unfold vals0. cbn. lia. Qed.
  #[using="usp"] Lemma ev_EB_js : forall a tid c pl js k, ev (EB a tid c pl js) (16 + k)%nat = nth k js (Z_to_bv 64 0).
  Proof.
    intros. unfold EB, VB. cbn [ev].
    replace (16 + k)%nat with (length (vals0 PH sp draw argv envp uid hw ++ [a; tid; c] ++ pl_list pl) + k)%nat
      by (rewrite !length_app; cbn; unfold vals0; cbn; lia).
    rewrite (app_assoc _ [a; tid; c]), (app_assoc _ (pl_list pl)), vals_ev_app_r. reflexivity.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Record mfacts (E : env) (tid : word) (L : ledger) (mdl : Model) : Prop := MFacts {
    mf_halted : m_halted mdl = None;
    mf_res    : vm_reserved (m_vmmaps mdl) = segments_reserved SEGS;
    mf_isp    : vm_init_sp (m_vmmaps mdl) = sp;
    mf_lim    : vm_limit (m_vmmaps mdl) = lim;
    mf_sbrk   : vm_start_brk (m_vmmaps mdl) = brk;
    mf_brk    : vm_brk (m_vmmaps mdl) = Z_to_bv 64 (bv_unsigned brk + l_brk L);
    mf_mb     : vm_mmap_base (m_vmmaps mdl) = mbase;
    mf_maps   : vm_maps (m_vmmaps mdl) = dl E (l_maps L);
    mf_apart  : ivs_apart (dl E (l_maps L));
    mf_eager  : eager_used mdl <= l_eager L;
    mf_fs     : m_fs mdl = in_fs inp;
    mf_fds    : m_fds mdl = FDS0;
    mf_tid    : m_tid mdl = Some tid;
    mf_wf     : model_ivs_wf mdl;
    mf_na     : na_clear mdl }.

  #[using="Type"] Lemma mfacts_sbm : forall E tid L m m', mfacts E tid L m -> same_but_materialized m m' -> mfacts E tid L m'.
  Proof.
    intros E tid L m m' [F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 F13 F14 F15] HS.
    pose proof (same_but_materialized_frame m m' HS) as (_ & Svm & Slz & _ & _ & _ & _ & _ & Sfds & _ & _ & Sfs & Sh & Stid & _ & _ & Se).
    constructor; rewrite ?Svm, ?Slz, ?Sfds, ?Sfs, ?Sh, ?Stid, ?Se; try assumption.
    - unfold model_ivs_wf in *. rewrite Svm, Slz. exact F14.
    - unfold na_clear in *. rewrite Svm. exact F15.
  Qed.

  #[using="Type"] Lemma ivs_apart_lits : forall l, ivs_apart l <-> OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3RW__A3.BootLedgerA.apart_all l.
  Proof. induction l as [|[b n] l IH]; cbn; [tauto|]. rewrite IH. tauto. Qed.

  #[using="Type"] Lemma mfacts_env : forall a tid c pl js ks L m,
    ledger_vars_lt (length (VB a tid c pl js)) L = true ->
    mfacts (EB a tid c pl js) tid L m -> mfacts (EB a tid c pl (js ++ ks)) tid L m.
  Proof.
    intros a tid c pl js ks L m HL [F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 F13 F14 F15].
    unfold ledger_vars_lt in HL.
    constructor; try assumption; rewrite EB_app; unfold EB in *; rewrite dl_app_env by assumption; assumption.
  Qed.

  #[using="Type"] Lemma mfacts_alloc_top : forall E tid L m, mfacts E tid L m -> alloc_top (m_vmmaps m) = usp - stack_max_size.
  Proof. intros E tid L m F. unfold alloc_top. rewrite (mf_isp _ _ _ _ F). reflexivity. Qed.

  (* [comment removed for export] *)
  Definition map_ok (E : env) (p : expr * Z) : Prop :=
    let v := bv_unsigned (edenot E (fst p)) in
    v mod 4096 = 0 /\ 4096 <= v /\ 0 < snd p /\ v + snd p <= usp - stack_max_size /\ (v + snd p <= A_img_lo \/ A_img_hi <= v).
  Definition maps_ok (E : env) (L : ledger) : Prop := Forall (map_ok E) (l_maps L).

  #[using="Type"] Lemma maps_ok_env : forall a tid c pl js ks L,
    ledger_vars_lt (length (VB a tid c pl js)) L = true ->
    maps_ok (EB a tid c pl js) L -> maps_ok (EB a tid c pl (js ++ ks)) L.
  Proof.
    intros a tid c pl js ks L HL HM. unfold ledger_vars_lt in HL. rename HL into H1.
    unfold maps_ok in *. apply Forall_forall. intros [e n] Hin. pose proof (proj1 (Forall_forall _ _) HM _ Hin) as Hp.
    unfold map_ok in *. cbn [fst snd] in *. rewrite EB_app. unfold EB in Hp.
    pose proof (proj1 (forallb_forall _ _) H1 _ Hin) as He. cbn [fst] in He.
    rewrite (env_app_edenot _ ks _ e He). exact Hp.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition hfacts : Type := list (Z * Z * option byte).
  Definition hf_ok (H : word -> bool) (M : word -> option byte) (hc : hfacts) : Prop :=
    Forall (fun r => forall x : word, fst (fst r) <= bv_unsigned x < snd (fst r) -> H x = true -> M x = snd r) hc.
  Definition hf_inmaps (E : env) (L : ledger) (hc : hfacts) : Prop :=
    Forall (fun r => exists p, In p (l_maps L)
                     /\ bv_unsigned (edenot E (fst p)) <= fst (fst r) /\ snd (fst r) <= bv_unsigned (edenot E (fst p)) + snd p) hc.

  #[using="Type"] Lemma hf_ok_antimono : forall H H' M hc,
    (forall x, H' x = true -> H x = true) -> hf_ok H M hc -> hf_ok H' M hc.
  Proof.
    intros H H' M hc HH HF. unfold hf_ok in *. apply Forall_forall. intros r Hr x Hx Hh.
    exact (proj1 (Forall_forall _ _) HF r Hr x Hx (HH x Hh)).
  Qed.

  (* [comment removed for export] *)
  Definition H_in_maps (H : word -> bool) (E : env) (L : ledger) : Prop :=
    forall x : word, H x = true ->
      exists p, In p (l_maps L) /\ bv_unsigned (edenot E (fst p)) <= bv_unsigned x < bv_unsigned (edenot E (fst p)) + snd p.

  (* [comment removed for export] *)
  Record regime_ok (H : word -> bool) (A : list (Z * Z)) (hc : hfacts) (E : env) (L : ledger) (mdl : Model) : Prop := RegimeOk {
    rg_off    : H_off_segments SEGS H;
    rg_awf    : A_wf A;
    rg_cover  : lazy_cover H (m_vm_lazy mdl) A;
    rg_inmaps : H_in_maps H E L;
    rg_hcin   : hf_inmaps E L hc;
    rg_above  : forall x : word, usp <= bv_unsigned x -> H x = false;
    rg_lazy   : forall x : word, H x = true -> page_in_ranges (page_base x) (m_vm_lazy mdl) = true;
    rg_shadow : H_in_maps H2 E L   (* [comment removed for export] *) }.

  #[using="Type"] Lemma regime_ok_env : forall H A hc a tid c pl js ks L mdl,
    ledger_vars_lt (length (VB a tid c pl js)) L = true ->
    regime_ok H A hc (EB a tid c pl js) L mdl -> regime_ok H A hc (EB a tid c pl (js ++ ks)) L mdl.
  Proof.
    intros H A hc a tid c pl js ks L mdl HL [G1 G2 G3 G4 G5 G6 G7 G8].
    unfold ledger_vars_lt in HL. rename HL into H1.
    constructor; try assumption.
    - intros x Hx. destruct (G4 x Hx) as ([e n] & Hin & Hr). exists (e, n). split; [exact Hin|]. cbn [fst snd] in *.
      rewrite EB_app. unfold EB in Hr. pose proof (proj1 (forallb_forall _ _) H1 _ Hin) as He. cbn [fst] in He.
      rewrite (env_app_edenot _ ks _ e He). exact Hr.
    - unfold hf_inmaps in *. apply Forall_forall. intros r Hr0. destruct (proj1 (Forall_forall _ _) G5 r Hr0) as ([e n] & Hin & Hr).
      exists (e, n). split; [exact Hin|]. cbn [fst snd] in *.
      rewrite EB_app. unfold EB in Hr. pose proof (proj1 (forallb_forall _ _) H1 _ Hin) as He. cbn [fst] in He.
      rewrite (env_app_edenot _ ks _ e He). exact Hr.
    - intros x Hx. destruct (G8 x Hx) as ([e n] & Hin & Hr). exists (e, n). split; [exact Hin|]. cbn [fst snd] in *.
      rewrite EB_app. unfold EB in Hr. pose proof (proj1 (forallb_forall _ _) H1 _ Hin) as He. cbn [fst] in He.
      rewrite (env_app_edenot _ ks _ e He). exact Hr.
  Qed.

  #[using="Type"] Lemma regime_ok_sbm : forall H A hc E L mdl mdl',
    regime_ok H A hc E L mdl -> same_but_materialized mdl mdl' -> regime_ok H A hc E L mdl'.
  Proof. intros H A hc E L mdl mdl' [G1 G2 G3 G4 G5 G6 G7 G8] HS. constructor; try assumption; rewrite (sbm_lazy _ _ HS); assumption. Qed.

  (* [comment removed for export] *)
  Record bootS (H : word -> bool) (A : list (Z * Z)) (a tid c : word) (pl : placements) (js : list word)
               (sr : list expr) (kn : list kentry) (L : ledger) (hc : hfacts) (lz : list (word * word))
               (R : bvmap 5 word) (M : word -> option byte) (mdl : Model) : Prop := BootS {
    s_regs  : regs_ok (EB a tid c pl js) sr R;
    s_know  : know_ok SEGS (EB a tid c pl js) (mrestrict H M) kn;
    s_above : forall x : word, usp <= bv_unsigned x -> M x = wrap_mem PH sp argv envp uid hw draw x;
    s_hid   : hf_ok H M hc;
    s_lazy  : m_vm_lazy mdl = lz;
    s_minv  : MInv A mdl;
    s_mf    : mfacts (EB a tid c pl js) tid L mdl;
    s_mok   : maps_ok (EB a tid c pl js) L;
    s_rg    : regime_ok H A hc (EB a tid c pl js) L mdl;
    s_tls   : tls_ok sp a;
    s_clear : tls_clear a = true;
    s_tid   : 0 < bv_unsigned tid < 4194304 }.

  (* [comment removed for export] *)
  #[using="Type"] Lemma bootS_reknow : forall H A a tid c pl js sr kn sr' kn' L hc lz R M mdl,
    bootS H A a tid c pl js sr kn L hc lz R M mdl ->
    (regs_ok (EB a tid c pl js) sr R -> regs_ok (EB a tid c pl js) sr' R) ->
    (know_ok SEGS (EB a tid c pl js) (mrestrict H M) kn -> know_ok SEGS (EB a tid c pl js) (mrestrict H M) kn') ->
    bootS H A a tid c pl js sr' kn' L hc lz R M mdl.
  Proof. intros until mdl. intros [G1 G2 G3 G4 G4' G5 G6 G7 G8 G9 G10 G11] HR HK. constructor; auto. Qed.

  #[using="Type"] Lemma bootS_gc : forall H A a tid c pl js sr kn (keep : kentry -> bool) L hc lz R M mdl,
    bootS H A a tid c pl js sr kn L hc lz R M mdl -> bootS H A a tid c pl js sr (List.filter keep kn) L hc lz R M mdl.
  Proof. intros. eapply bootS_reknow; [eassumption | auto |]. intros HK. apply know_ok_filter. exact HK. Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma bootS_sbm : forall H A a tid c pl js sr kn L hc lz R M mdl mdl',
    bootS H A a tid c pl js sr kn L hc lz R M mdl -> MInv A mdl' -> same_but_materialized mdl mdl' ->
    bootS H A a tid c pl js sr kn L hc lz R M mdl'.
  Proof.
    intros until mdl'. intros [G1 G2 G3 G4 G4' G5 G6 G7 G8 G9 G10 G11] HM HS. constructor; auto.
    - rewrite (sbm_lazy _ _ HS). exact G4'.
    - eapply mfacts_sbm; eassumption.
    - eapply regime_ok_sbm; eassumption.
  Qed.

  (* [comment removed for export] *)
  #[using="brk mbase VI VE"] Lemma frame_blockS : forall H a tid c pl js M log hc (lows : list (expr * Z)),
    log_below_b 0%nat lows log = true ->
    lows_ok (EB a tid c pl js) usp lows ->
    (forall x : word, usp <= bv_unsigned x -> H x = false) ->
    (forall x : word, usp <= bv_unsigned x -> M x = wrap_mem PH sp argv envp uid hw draw x) ->
    hf_ok H M hc ->
    let M0 := munrestrict H M (mem_denot (EB a tid c pl js) (mrestrict H M) log) in
    (forall x : word, usp <= bv_unsigned x -> M0 x = wrap_mem PH sp argv envp uid hw draw x)
    /\ hf_ok H M0 hc.
  Proof.
    intros H a tid c pl js M log hc lows Hlog Hlows Hvis HA HZ M0. pose proof SL'. pose proof SH'. split.
    - intros x Hx. unfold M0.
      assert (Hv : H x = false) by (apply Hvis; exact Hx).
      rewrite (munrestrict_visible _ _ _ _ Hv).
      assert (L1 : 2 ^ 41 <= bv_unsigned (ev (EB a tid c pl js) 0%nat)) by (rewrite ev_EB_sp; unfold usp in *; lia).
      assert (L2 : bv_unsigned (ev (EB a tid c pl js) 0%nat) <= usp) by (rewrite ev_EB_sp; unfold usp in *; lia).
      assert (L3 : usp <= 2 ^ 64 - 2 ^ 41) by (unfold usp in *; lia).
      rewrite (mem_denot_above (EB a tid c pl js) (mrestrict H M) log 0%nat lows usp x Hlog L1 L2 L3 Hlows Hx).
      rewrite (mrestrict_visible' _ _ _ Hv). apply HA. exact Hx.
    - unfold hf_ok in *. apply Forall_forall. intros r Hr x Hx Hh. unfold M0.
      rewrite (munrestrict_hidden _ _ _ _ Hh). exact (proj1 (Forall_forall _ _) HZ r Hr x Hx Hh).
  Qed.

  (* [comment removed for export] *)
  Definition lows_of (L : ledger) : list (expr * Z) := l_maps L.
  #[using="Type"] Lemma lows_of_ok : forall E L, maps_ok E L -> lows_ok E usp (lows_of L).
  Proof.
    intros E L HM. unfold lows_ok, lows_of. apply Forall_forall. intros [e n] Hin.
    pose proof (proj1 (Forall_forall _ _) HM _ Hin) as (_ & _ & Hn & Htop & _). cbn [fst snd] in *.
    unfold stack_max_size in Htop. lia.
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Fixpoint gws (nZ : Z) (l : sivs) : Z :=
    match l with [] => 0 | (_, n) :: r => n + nZ + 4095 + gws nZ r end.

  Definition sivs_sizes_ok (l : sivs) : bool := forallb (fun p => (0 <=? snd p) && (snd p <? 2 ^ 64)) l.

  #[using="sp usp"] Lemma gap_weight_dl : forall E nZ l, sivs_sizes_ok l = true -> gap_weight nZ (dl E l) = gws nZ l.
  Proof.
    intros E nZ l. unfold dl. induction l as [|[e n] l IH]; cbn [List.map gap_weight gws sivs_sizes_ok forallb fst snd]; intros Hs; [reflexivity|].
    apply andb_prop in Hs as [Hn Hl]. apply andb_prop in Hn as [H0 H1]. apply Z.leb_le in H0. apply Z.ltb_lt in H1.
    unfold sivs_sizes_ok in IH. rewrite (IH Hl), u_small by lia. reflexivity.
  Qed.

  #[using="Type"] Lemma reserved_dead_above : List.filter (live_at IMG_HI) (segments_reserved SEGS) = [].
  Proof. vmeq_refl. Qed.

  (* [comment removed for export] *)
  #[using="draw VI VE usp"] Lemma grant_exists_L : forall E tid L mdl nZ,
    mfacts E tid L mdl -> 0 < nZ -> sivs_sizes_ok (l_maps L) = true ->
    IMG_HI + nZ + gws nZ (l_maps L) <= 0x7fff80000000 - stack_max_size ->
    exists p, grant_ok_na_pin mdl p nZ = true.
  Proof.
    intros E tid L mdl nZ F HnZ Hs Hw. pose proof SL' as SL. pose proof SH' as SH.
    apply (grant_exists_between mdl nZ IMG_HI HnZ ltac:(unfold IMG_HI; lia) ltac:(reflexivity)).
    rewrite (mf_res _ _ _ _ F), (mf_maps _ _ _ _ F), (mfacts_alloc_top _ _ _ _ F).
    rewrite filter_app, reserved_dead_above, app_nil_l.
    pose proof (gap_weight_filter_le nZ (live_at IMG_HI) (dl E (l_maps L)) ltac:(lia)) as Hle.
    rewrite (gap_weight_dl E nZ (l_maps L) Hs) in Hle. unfold usp in *. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition DS_std (L : ledger) : list (saddr * expr) :=
    [(SA (EVar 0) (- 0x800000), ELit 0x1800000); (SA (ELit 0) A_img_lo, ELit (A_img_hi - A_img_lo));
     (SA (ELit 0) SHB_LO, ELit (SHB_HI - SHB_LO))]
    ++ DS_maps (l_maps L).

  #[using="draw VI VE usp"] Lemma DS_std_claims : forall E tid L mdl nZ,
    mfacts E tid L mdl -> H_in_maps H2 E L -> ev E 0%nat = sp -> sivs_sizes_ok (l_maps L) = true -> 0 < nZ ->
    dsj_claims E (fun p => grant_ok_na_pin mdl p nZ = true) nZ (DS_std L).
  Proof.
    intros E tid L mdl nZ F HSB Hsp Hs HnZ. pose proof SL' as SL. pose proof SH' as SH.
    unfold dsj_claims, DS_std, DS_maps. apply Forall_app. split.
    - constructor; [|constructor; [|constructor; [|constructor]]]; cbn [fst snd]; intros p Hp;
        destruct (grant_ok_na_pin_unpack _ _ _ Hp) as (Hal & Hpos & Htop & Hrf);
        rewrite (mfacts_alloc_top _ _ _ _ F) in Htop; unfold estart, elenZ; cbn [a_base a_off edenot].
      + rewrite Hsp. unfold stack_max_size in Htop. rewrite u_small by lia. unfold usp in *. lia.
      + rewrite (mf_res _ _ _ _ F), (mf_maps _ _ _ _ F), region_free_app in Hrf. apply andb_prop in Hrf as [Hrf _].
        pose proof (u64_range p). pose proof img_hull as IH.
        rewrite !u_small by (unfold A_img_lo, A_img_hi; lia). change (bv_unsigned (Z_to_bv 64 0)) with 0.
        destruct (reserved_apart p nZ HnZ ltac:(unfold stack_max_size, usp in *; lia) Hrf); lia.
      + (* [comment removed for export] *)
        pose proof (u64_range p) as Hpr. unfold SHB_LO, SHB_HI. rewrite !u_small by lia. change (bv_unsigned (Z_to_bv 64 0)) with 0.
        rewrite (mf_res _ _ _ _ F), (mf_maps _ _ _ _ F), region_free_app in Hrf. apply andb_prop in Hrf as [_ Hrf].
        destruct (Z.lt_ge_cases (bv_unsigned p + nZ) (0x7fff7000 + 1)) as [|C1]; [lia|].
        destruct (Z.lt_ge_cases (bv_unsigned p) 0x10007fff8000) as [C2|]; [|lia]. exfalso.
        set (xz := Z.max (bv_unsigned p) 0x7fff7000).
        assert (Hx : exists x : word, bv_unsigned x = xz) by (exists (Z_to_bv 64 xz); apply u_small; unfold stack_max_size in *; lia).
        destruct Hx as (x & Hx).
        destruct (HSB x ltac:(unfold H2, SHB_LO, SHB_HI; rewrite Hx; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia))
          as ([e n] & Hin & Hr). cbn [fst snd] in Hr.
        pose proof (proj1 (forallb_forall _ _) Hs _ Hin) as Hn. cbn [snd] in Hn. apply andb_prop in Hn as [N0 N1].
        apply Z.leb_le in N0. apply Z.ltb_lt in N1.
        pose proof (region_free_In _ p (Z_to_bv 64 nZ) (edenot E e) (Z_to_bv 64 n) Hrf
                      ltac:(unfold dl; apply in_map_iff; exists (e, n); split; [reflexivity | exact Hin])) as Hov.
        rewrite !u_small in Hov by (unfold stack_max_size in *; lia). lia.
    - apply Forall_forall. intros d Hd p Hp. apply in_map_iff in Hd as ([e n] & <- & Hin). cbn [fst snd].
      destruct (grant_ok_na_pin_unpack _ _ _ Hp) as (Hal & Hpos & Htop & Hrf).
      rewrite (mf_res _ _ _ _ F), (mf_maps _ _ _ _ F), region_free_app in Hrf. apply andb_prop in Hrf as [_ Hrf].
      pose proof (proj1 (forallb_forall _ _) Hs _ Hin) as Hn. cbn [snd] in Hn. apply andb_prop in Hn as [H0 H1].
      apply Z.leb_le in H0. apply Z.ltb_lt in H1.
      rewrite (mfacts_alloc_top _ _ _ _ F) in Htop. unfold stack_max_size, usp in *. pose proof SH.
      pose proof (region_free_In _ p (Z_to_bv 64 nZ) (edenot E e) (Z_to_bv 64 n) Hrf
                    ltac:(unfold dl; apply in_map_iff; exists (e, n); split; [reflexivity | exact Hin])) as Hov.
      rewrite !u_small in Hov by lia. unfold estart, elenZ. cbn [a_base a_off edenot]. rewrite !u_small by lia.
      change (bv_unsigned (Z_to_bv 64 0)) with 0. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="draw VI VE usp"] Lemma grant_misses_shadow : forall E tid L mdl p nZ,
    mfacts E tid L mdl -> H_in_maps H2 E L -> ev E 0%nat = sp -> sivs_sizes_ok (l_maps L) = true -> 0 < nZ ->
    grant_ok_na_pin mdl p nZ = true -> bv_unsigned p + nZ <= SHB_LO \/ SHB_HI <= bv_unsigned p.
  Proof.
    intros E tid L mdl p nZ F HSB Hsp Hs HnZ Hp.
    pose proof (DS_std_claims E tid L mdl nZ F HSB Hsp Hs HnZ) as C. unfold dsj_claims, DS_std in C.
    apply Forall_app in C as [C _]. apply Forall_cons_iff in C as [_ C]. apply Forall_cons_iff in C as [_ C]. apply Forall_cons_iff in C as [C _].
    specialize (C p Hp). unfold estart, elenZ in C. cbn [fst snd a_base a_off edenot] in C.
    unfold SHB_LO, SHB_HI in *. rewrite !u_small in C by lia. change (bv_unsigned (Z_to_bv 64 0)) with 0 in C. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="usp"] Lemma grant_visible_L : forall H E tid L mdl p nZ,
    mfacts E tid L mdl -> H_in_maps H E L -> sivs_sizes_ok (l_maps L) = true -> 0 <= nZ ->
    grant_ok_na_pin mdl p nZ = true -> range_visible H p nZ.
  Proof.
    intros H E tid L mdl p nZ F Hin Hs HnZ Hp.
    apply (grant_visible_of_hidden_mapped H mdl p nZ); [| exact HnZ | exact Hp].
    intros x Hx. destruct (Hin x Hx) as ([e n] & Hi & Hr). cbn [fst snd] in Hr.
    pose proof (proj1 (forallb_forall _ _) Hs _ Hi) as Hn. cbn [snd] in Hn. apply andb_prop in Hn as [H0 H1].
    apply Z.leb_le in H0. apply Z.ltb_lt in H1.
    exists (edenot E e, Z_to_bv 64 n). split.
    - rewrite (mf_maps _ _ _ _ F). unfold dl. apply in_map_iff. exists (e, n). split; [reflexivity | exact Hi].
    - cbn [fst snd]. rewrite u_small by lia. exact Hr.
  Qed.

  (* [comment removed for export] *)
  Definition lgrant (L : ledger) (v : nat) (nZ : Z) : ledger :=
    Ledger ((EVar v, nZ) :: l_maps L) (l_brk L) (l_eager L + nZ).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition kn_grant (L : ledger) (v : nat) (nZ : Z) (kn : list kentry) : list kentry := kn_grant_d (DS_std L) v nZ kn.

  #[using="Type"] Lemma t_alt2_nil_l : forall (T : TSet), T [] -> t_eq (t_alt2 t_nil T) T.
  Proof. intros T HT tr. unfold t_alt2, t_nil. split; [intros [->|H]; assumption | intros H; right; exact H]. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="VI VE"] Theorem bs_mmap_rw_spin : forall H A a tid c pl js sr kn L zr lz (len pc : Z) w R M mdl (K : TSet),
    let E := EB a tid c pl js in
    let v := length (VB a tid c pl js) in
    let nZ := page_round_up_Z len in
    bootS H A a tid c pl js sr kn L zr lz R M mdl ->
    fetch_word SEGS (Z_to_bv 64 pc) = Some w -> is_ecall w = true -> 0 <= pc -> pc + 4 < 2 ^ 64 ->
    sr_vars_lt v sr = true -> kn_vars_lt v kn = true -> ledger_vars_lt v L = true -> sivs_sizes_ok (l_maps L) = true ->
    sr_get sr 17%bv = ELit 222 -> sr_get sr 10%bv = ELit 0 -> sr_get sr 11%bv = ELit len -> sr_get sr 12%bv = ELit 3 ->
    sr_get sr 13%bv = ELit 34 -> sr_get sr 14%bv = ELit (2 ^ 64 - 1) -> sr_get sr 15%bv = ELit 0 ->
    0 < len -> l_eager L + nZ + A_bytes A <= lim ->
    IMG_HI + nZ + gws nZ (l_maps L) <= 0x7fff80000000 - stack_max_size ->
    (forall p R' M' mdl', bootS H A a tid c pl (js ++ [p]) (sr_upd sr 10 (EVar v)) (kn_grant L v nZ kn) (lgrant L v nZ) zr lz R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 (pc + 4)) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 pc) M ROM) mdl) K.
  Proof.
    intros H A a tid c pl js sr kn L zr lz len pc w R M mdl K E v nZ HB HF HE Hpc0 Hpc4
           Hsr Hkn HL Hs S17 S10 S11 S12 S13 S14 S15 Hlen Hbud Hroom HK.
    destruct HB as [HR HKN HA HZ HLZ HM F HMO RG HT Hcl Ht]. pose proof RG as [HH HAW HCOV HIN Hhin Habv Hhl Hshd].
    pose proof SL' as SL. pose proof SH' as SH. assert (SMS : stack_max_size = 8388608) by reflexivity.
    assert (USP : usp = bv_unsigned sp) by reflexivity.
    assert (HnZ : len <= nZ /\ nZ < len + 4096) by (unfold nZ; pose proof (page_round_up_Z_bounds len ltac:(lia)); unfold page_size in *; lia).
    assert (Hlen64 : len < 2 ^ 64).
    { unfold stack_max_size, IMG_HI in Hroom. pose proof (gap_weight_nonneg nZ (dl E (l_maps L)) ltac:(lia)) as W.
      rewrite (gap_weight_dl E nZ _ Hs) in W. lia. }
    assert (G : forall r z, sr_get sr r = ELit z -> getr R r = Z_to_bv 64 z).
    { intros r z Hz. rewrite (HR r), Hz. reflexivity. }
    eapply (srz_mmap_rw_pin SEGS R (Z_to_bv 64 pc) M ROM mdl w len (Z_to_bv 64 34) K HF HE (mf_halted _ _ _ _ F)
              (G _ _ S17) (G _ _ S11) ltac:(lia) (G _ _ S12) (G _ _ S13) eq_refl).
    - rewrite (G _ _ S14). apply bv_eq. reflexivity.
    - exact (G _ _ S15).
    - exact (grant_exists_L E tid L mdl nZ F ltac:(lia) Hs Hroom).
    - (* [comment removed for export] *)
      unfold mmap_noreserve_backed_ok. cbn [mmap_noreserve_b]. change (negb _) with false. cbn [negb].
      apply Z.leb_le. rewrite vm_backing_used_split, (mf_lim _ _ _ _ F).
      destruct HM as [N1 N2 N3 N4 N5].
      pose proof (allowed_pages_bound A (m_vm_materialized mdl) HAW N1 N2 N3) as PB.
      pose proof (mf_eager _ _ _ _ F). rewrite (mf_lim _ _ _ _ F) in N5. lia.
    - (* [comment removed for export] *)
      intros p Hp. rewrite pc_lit_add4 by lia. rewrite with_mmap_backing_eager by reflexivity. fold nZ. fold nZ in Hp.
      destruct (grant_ok_na_pin_unpack _ _ _ Hp) as (Hal & Hpos & Htop & Hrf).
      rewrite (mfacts_alloc_top _ _ _ _ F) in Htop.
      pose proof (u64_range p) as Hpr.
      assert (Hvis : range_visible H p nZ) by (apply (grant_visible_L H E tid L mdl p nZ F HIN Hs ltac:(lia) Hp)).
      assert (Hev : edenot (EB a tid c pl (js ++ [p])) (EVar v) = p).
      { rewrite EB_app. cbn [edenot ev]. unfold v. rewrite <- (Nat.add_0_r (length _)), vals_ev_app_r. reflexivity. }
      set (n := Z_to_bv 64 nZ) in *.
      assert (Hun : bv_unsigned n = nZ) by (unfold n; apply u_small; unfold stack_max_size in Htop; unfold usp in *; lia).
      assert (Himg : bv_unsigned p + nZ <= A_img_lo \/ A_img_hi <= bv_unsigned p).
      { rewrite (mf_res _ _ _ _ F), (mf_maps _ _ _ _ F), region_free_app in Hrf. apply andb_prop in Hrf as [Hrf _].
        apply (reserved_apart p nZ); [lia | unfold stack_max_size, usp in *; lia | exact Hrf]. }
      apply (HK p). constructor.
      + (* [comment removed for export] *)
        apply regs_ok_set; [| intros X; apply (f_equal bv_unsigned) in X; discriminate X | exact Hev].
        rewrite EB_app. apply env_app_regs; [exact Hsr | exact HR].
      + (* [comment removed for export] *)
        rewrite (mrestrict_zfill H p n M) by (rewrite Hun; exact Hvis).
        assert (KO' : know_ok SEGS (EB a tid c pl (js ++ [p])) (mrestrict H M) kn).
        { rewrite EB_app. apply env_app_know; [exact Hkn | exact HKN]. }
        assert (KF : forall V, know_ok SEGS (EB a tid c pl (js ++ [p])) V
                       [KAlign (EVar v) 4096; KRange (EVar v) 4096 (2 ^ 64 - stack_max_size - nZ)]).
        { intros V. rewrite EB_app. unfold v. apply kfacts_grant; try assumption; unfold stack_max_size, usp in *; lia. }
        assert (KD : forall V, know_ok SEGS (EB a tid c pl (js ++ [p])) V (dsj_entries v nZ (DS_std L))).
        { intros V. rewrite EB_app. unfold v.
          apply (dsj_entries_ok SEGS (VB a tid c pl js) (blobs0 draw argv) V _ nZ (DS_std L) p ltac:(lia)
                   ltac:(unfold stack_max_size, usp in *; lia) (DS_std_claims E tid L mdl nZ F Hshd (ev_EB_sp a tid c pl js) Hs ltac:(lia)) Hp).
          unfold DS_std, DS_maps. apply Forall_app. split.
          - constructor; [cbn; split; reflexivity|]. constructor; [cbn; split; reflexivity|]. constructor; [cbn; split; reflexivity|]. constructor.
          - apply Forall_forall. intros d Hd. apply in_map_iff in Hd as ([e en] & <- & Hin). cbn [fst snd]. split; [|reflexivity].
            unfold ledger_vars_lt in HL.
            cbn [saddr_vars_lt a_base]. exact (proj1 (forallb_forall _ _) HL _ Hin). }
        unfold kn_grant, kn_grant_d. apply (proj2 (know_ok_app SEGS _ _ _ _)); split; [|apply (proj2 (know_ok_app SEGS _ _ _ _)); split].
        * unfold GF. rewrite <- Hun.
          constructor; [apply kzero_zfill; [exact Hev | lia | rewrite Hun; unfold stack_max_size, usp in *; lia]|].
          constructor; [apply kwr_zfill; [exact Hev | lia | rewrite Hun; unfold stack_max_size, usp in *; lia]|].
          rewrite Hun. apply KF.
        * apply KD.
        * apply (kn_keep_sound SEGS _ (mrestrict H M) (zfill p n (mrestrict H M)) MGrow).
          -- apply (proj2 (know_ok_app SEGS _ _ _ _)); split; [apply KF|].
             apply (proj2 (know_ok_app SEGS _ _ _ _)); split; [apply KD | exact KO'].
          -- exact KO'.
          -- unfold estart, elenZ. cbn [a_base a_off]. rewrite Hev. cbn [edenot]. fold n. rewrite Hun.
             rewrite Z.add_0_r, <- Hun. apply mem_change_zfill.
      + (* [comment removed for export] *)
        intros x Hx. rewrite zfill_out; [apply HA; exact Hx|]. rewrite Hun. unfold stack_max_size, usp in *. lia.
      + (* [comment removed for export] *)
        unfold hf_ok in HZ |- *.
        apply Forall_forall. intros r Hr x Hx Hhx. rewrite zfill_out; [exact (proj1 (Forall_forall _ _) HZ r Hr x Hx Hhx)|].
        rewrite Hun.
        destruct (Z.lt_ge_cases (bv_unsigned x) (bv_unsigned p)); [left; assumption|].
        destruct (Z.lt_ge_cases (bv_unsigned x) (bv_unsigned p + nZ)); [|right; assumption].
        exfalso. rewrite (Hvis x ltac:(lia)) in Hhx. discriminate.
      + (* [comment removed for export] *) rewrite mmap_model_lazy. exact HLZ.
      + (* [comment removed for export] *)
        pose proof (mf_wf _ _ _ _ F) as (W1 & W2 & W3 & W4).
        apply MInv_mmap_model; [exact W1 | apply iv_wf_intro; rewrite Hun; lia | exact HM |].
        rewrite Hun, (mf_lim _ _ _ _ F). pose proof (mf_eager _ _ _ _ F). lia.
      + (* [comment removed for export] *)
        pose proof (mf_wf _ _ _ _ F) as (W1 & W2 & W3 & W4).
        pose proof HL as HL1. unfold ledger_vars_lt in HL1.
        constructor; rewrite ?mmap_model_vm; cbn [vm_reserved vm_maps vm_noaccess vm_start_brk vm_brk vm_limit vm_mmap_base vm_init_sp];
          try (rewrite EB_app; unfold E, EB in F; rewrite (dl_app_env _ [p] _ _) by assumption).
        * rewrite mmap_model_halted. exact (mf_halted _ _ _ _ F).
        * exact (mf_res _ _ _ _ F).
        * exact (mf_isp _ _ _ _ F).
        * exact (mf_lim _ _ _ _ F).
        * exact (mf_sbrk _ _ _ _ F).
        * cbn [lgrant l_brk]. exact (mf_brk _ _ _ _ F).
        * exact (mf_mb _ _ _ _ F).
        * cbn [lgrant l_maps dl List.map fst snd]. rewrite Hev, (mf_maps _ _ _ _ F). fold (dl (EB a tid c pl (js ++ [p])) (l_maps L)).
          rewrite EB_app. unfold E, EB. rewrite (dl_app_env _ [p] _ _ HL1). reflexivity.
        * (* [comment removed for export] *)
          cbn [lgrant l_maps ivs_apart dl List.map fst snd]. fold (dl (EB a tid c pl (js ++ [p])) (l_maps L)). rewrite Hev.
          rewrite EB_app. unfold E, EB in F |- *. rewrite (dl_app_env _ [p] _ _ HL1). rewrite <- (mf_maps _ _ _ _ F).
          rewrite region_free_app in Hrf. apply andb_prop in Hrf as [_ Hrf2].
          split; [| rewrite (mf_maps _ _ _ _ F); exact (mf_apart _ _ _ _ F)].
          apply Forall_forall. intros [qb qn] Hq. cbn [fst snd].
          pose proof (region_free_In _ p n qb qn Hrf2 Hq) as Hov. rewrite Hun in Hov. fold n. rewrite Hun. lia.
        * cbn [lgrant l_eager]. pose proof (eager_used_mmap_model_le p n mdl W1 ltac:(apply iv_wf_intro; rewrite Hun; lia)).
          rewrite Hun in *. pose proof (mf_eager _ _ _ _ F). lia.
        * rewrite mmap_model_fs. exact (mf_fs _ _ _ _ F).
        * rewrite mmap_model_fds. exact (mf_fds _ _ _ _ F).
        * rewrite mmap_model_tid. exact (mf_tid _ _ _ _ F).
        * unfold model_ivs_wf. rewrite mmap_model_vm, mmap_model_lazy. cbn [vm_maps vm_noaccess vm_init_sp].
          split; [apply ivs_wf_cons; [apply iv_wf_intro; rewrite Hun; lia | exact W1]|]. split; [exact W2|]. split; [exact W3|]. exact W4.
        * unfold na_clear. rewrite mmap_model_vm. cbn [vm_noaccess]. exact (mf_na _ _ _ _ F).
      + (* [comment removed for export] *)
        unfold maps_ok, lgrant. cbn [l_maps]. constructor.
        * unfold map_ok. cbn [fst snd]. rewrite Hev. unfold stack_max_size, page_size in *.
          split; [exact Hal|]. split; [|split; [lia | split; [lia | exact Himg]]].
          pose proof (Z.mod_pos_bound (bv_unsigned p) 4096 ltac:(lia)). pose proof (Z.div_mod (bv_unsigned p) 4096 ltac:(lia)). nia.
        * exact (maps_ok_env a tid c pl js [p] L HL HMO).
      + (* [comment removed for export] *)
        pose proof (regime_ok_env H A zr a tid c pl js [p] L mdl HL RG) as [Q1 Q2 Q3 Q4 Q5 Q6 Q7 Q8].
        constructor; try assumption; try (rewrite mmap_model_lazy; assumption).
        -- intros x Hx. destruct (Q4 x Hx) as (q & Hq & Hr). exists q. split; [| exact Hr]. unfold lgrant. cbn [l_maps]. right. exact Hq.
        -- unfold hf_inmaps in *. apply Forall_forall. intros r Hr0. destruct (proj1 (Forall_forall _ _) Q5 r Hr0) as (q & Hq & Hr).
           exists q. split; [| exact Hr]. unfold lgrant. cbn [l_maps]. right. exact Hq.
        -- intros x Hx. destruct (Q8 x Hx) as (q & Hq & Hr). exists q. split; [| exact Hr]. unfold lgrant. cbn [l_maps]. right. exact Hq.
      + exact HT.
      + exact Hcl.
      + exact Ht.
  Qed.
End Theorems.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac rg_block VI VE HB HK RUN CAR :=
  lazymatch type of VE with valid_entry _ (mkEntry ?sp ?brk ?mbase ?draw) ?inp =>
    let HR := fresh "HR" in let HKN := fresh "HKN" in let HA := fresh "HA" in let HZ := fresh "HZ" in
    let HM := fresh "HM" in let F := fresh "F" in let HMO := fresh "HMO" in let RG := fresh "RG" in
    let HT := fresh "HT" in let Hcl := fresh "Hcl" in let Ht := fresh "Ht" in let HLZ := fresh "HLZ" in
    destruct HB as [HR HKN HA HZ HLZ HM F HMO RG HT Hcl Ht];
    let HH := fresh "HH" in let Hwx := fresh "Hwx" in let HAW := fresh "HAW" in let Hh := fresh "Hh" in let HL := fresh "HL" in
    pose proof (rg_off _ _ _ _ _ _ _ RG) as HH; pose proof wx_nowrap as Hwx; pose proof (rg_awf _ _ _ _ _ _ _ RG) as HAW;
    pose proof (mf_halted _ _ _ _ _ _ _ _ _ F) as Hh;
    pose proof (rg_cover _ _ _ _ _ _ _ RG) as HL;
    run_block_K HR HKN HM HL Hh HH Hwx HAW RUN CAR;
    lazymatch goal with |- srealizes _ (mkCfg (mkst _ _ ?m _) _) _ =>
      let body := eval unfold m in m in
      lazymatch body with munrestrict ?H ?M (mem_denot (EB _ _ _ ?a ?tid ?c ?pl ?js) _ ?lg) =>
        lazymatch type of F with mfacts _ _ _ _ _ _ _ ?L _ =>
          lazymatch type of HZ with hf_ok _ _ ?hc =>
            destruct (frame_blockS sp brk mbase draw inp VI VE H a tid c pl js M lg hc (lows_of L) ltac:(vmeq_refl)
                        (lows_of_ok sp _ L HMO) (rg_above _ _ _ _ _ _ _ RG) HA HZ) as [HA0 HZ0];
            subst m
          end end end end;
    apply HK; constructor; try assumption;
      [ erewrite sbm_lazy by eassumption; exact HLZ | eapply mfacts_sbm; eassumption | eapply regime_ok_sbm; eassumption]
  end.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.B3 Require BootS2.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import Stdlib.Logic.FunctionalExtensionality.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.CatExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.CatSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.SeqExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.StoreOk OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.StepTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.RefLayout__Common.AgentLib OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.ArgvEnv__Common.StartupAux OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.RefLayout__Common.RefLayout OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.ArgvEnv__Common.ArgvEnv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.ArgvEnv__Common.MemSplit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanAcct__Common.Hoare OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AllocSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.MmapSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanHexScan__Common.ExitSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanHexScan__Common.SimInv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.FileSim__Common.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.FileSim__Common.AgentNodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.RefNodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanHexScan__Common.AsanCeil OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AllocSim2__Common.ShapeAlg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanAcct__Common.ErrEscape OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.SpinAlg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.DivergeSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanAcct__Common.AsanAcct OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.RefLayout__Common.AsanAcctShape OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanNodesMmLib OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanNodesLibE OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.BackingAlgebra OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanHexScan__Common.AsanPlacement.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3Sound OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymRun3__Common.AxSymRun3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanPlanCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanPlan OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymRun3__Common.KnApart.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.EntryKn OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.StdioSymDrive OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.EntryGlue OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBlock__Lib.MallocSymAux OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.NodesFs__Lib.NodesMm OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.NodesMmDrive__Lib.NodesMmDrive OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBlock__Lib.AsanBlock OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanKnow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanNodes__Lib.AsanNodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanNodesDrive OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanHeapKit.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Img.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3Syms.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3SymsBoot.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBootKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.NodesMmDrive__Lib.AsanBootKn OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBlock__Lib.AsanBootTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanNodes__Lib.AsanNodesBoot.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3SymsBootW.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn1.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.Boot1.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.Boot2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.Boot3.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootS1.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3RW__A3.BootLedgerA.TwB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.B3.BootS2.
Import ListNotations.
Import AX2. Import AX2S.
#[local] Instance bootstate_fx : OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec.FPState := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec.fx0.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition dl (E : env) (l : sivs) : list (word * word) :=
  List.map (fun p => (edenot E (fst p), Z_to_bv 64 (snd p))) l.

(* [comment removed for export] *)
Record ledger : Type := Ledger {
  l_maps  : sivs;     (* [comment removed for export] *)
  l_brk   : Z;        (* [comment removed for export] *)
  l_eager : Z         (* [comment removed for export] *) }.

Definition sivs_vars_lt (n : nat) (l : sivs) : bool := forallb (fun p => expr_vars_lt n (fst p)) l.
Definition ledger_vars_lt (n : nat) (L : ledger) : bool := sivs_vars_lt n (l_maps L).

(* [comment removed for export] *)
Fixpoint ivs_apart (l : list (word * word)) : Prop :=
  match l with
  | [] => True
  | (b, n) :: r => Forall (fun q => bv_unsigned b + bv_unsigned n <= bv_unsigned (fst q)
                                  \/ bv_unsigned (fst q) + bv_unsigned (snd q) <= bv_unsigned b) r /\ ivs_apart r
  end.

Lemma lazy_sub_cover : forall H (l1 l2 : list (word * word)) A,
  (forall p, page_in_ranges p l1 = true -> page_in_ranges p l2 = true) ->
  lazy_cover H l2 A -> lazy_cover H l1 A.
Proof. intros H l1 l2 A Hs HC w Hp Hh. apply HC; [apply Hs; exact Hp | exact Hh]. Qed.

Lemma dl_app_env : forall vals extra ebs l,
  sivs_vars_lt (length vals) l = true ->
  dl (Env (vals_ev (vals ++ extra)) ebs) l = dl (Env (vals_ev vals) ebs) l.
Proof.
  intros vals extra ebs l. induction l as [|[e n] l IH]; cbn [dl List.map sivs_vars_lt forallb fst snd]; intros H; [reflexivity|].
  apply andb_prop in H as [He Hl]. rewrite (env_app_edenot vals extra ebs e He). f_equal. apply IH. exact Hl.
Qed.

(* [comment removed for export] *)
Definition FDS0 : list (word * FdEntry) :=
  [(Z_to_bv 64 0, FdChannel (Z_to_bv 64 0)); (Z_to_bv 64 1, FdChannel (Z_to_bv 64 1)); (Z_to_bv 64 2, FdChannel (Z_to_bv 64 2))].

(* [comment removed for export] *)
Definition na_clear_l (l : list (word * word)) : Prop := region_free l LO_A LO_N = true /\ region_free l HI_A HI_N = true.
Definition na_clear (mdl : Model) : Prop := na_clear_l (vm_noaccess (m_vmmaps mdl)).

Lemma region_free_maps_subtract : forall l lo hi (b n : word),
  ivs_wf l -> region_free l b n = true -> region_free (maps_subtract l lo hi) b n = true.
Proof.
  intros l lo hi b n Hwf Hrf. apply RefNodes.region_free_intro. intros qb qs Hq.
  destruct (maps_subtract_pieces l lo hi (qb, qs) Hwf Hq) as ([rb rs] & Hr & H1 & H2 & _). cbn [fst snd] in *.
  pose proof (RefNodes.region_free_In l b n rb rs Hrf Hr). lia.
Qed.

Lemma na_clear_l_sub : forall l lo hi, ivs_wf l -> na_clear_l l -> na_clear_l (maps_subtract l lo hi).
Proof. intros l lo hi Hwf [H1 H2]. split; apply region_free_maps_subtract; assumption. Qed.

Lemma na_clear_l_cons : forall l (a n : word),
  bv_unsigned a + bv_unsigned n <= SHB_LO \/ SHB_HI <= bv_unsigned a -> na_clear_l l -> na_clear_l ((a, n) :: l).
Proof.
  intros l a n Hap [H1 H2]. unfold na_clear_l. cbn [region_free]. rewrite H1, H2, !andb_true_r. unfold iv_overlap.
  assert (LA : bv_unsigned LO_A = 0x7fff7000) by (vmeq_refl).
  pose proof LO_N_val as LN. pose proof HI_A_val as HA. pose proof HI_N_val as HN. rewrite LA, LN, HA, HN. unfold SHB_LO, SHB_HI in Hap.
  pose proof (u64_range n). pose proof (u64_range a).
  split; apply negb_true_iff; apply andb_false_iff; destruct Hap; [left | right | left | right]; apply Z.ltb_ge; lia.
Qed.

Section Theorems.
  Variables (sp brk mbase : word) (draw : EntryDraw) (lim : Z) (inp : ProcInput).
  Hypothesis VI : valid_input inp.
  Hypothesis VE : valid_entry IMG (mkEntry sp brk mbase draw) inp.

  Let argv := in_argv inp.
  Let envp := in_envp inp.
  Let uid := in_uid inp.
  Let hw := in_hwcap inp.
  Let usp := bv_unsigned sp.

  #[using="brk mbase draw inp VI VE"] Lemma SL' : 0x7fff80000000 <= usp. Proof. exact (SL sp brk mbase draw inp VI VE). Qed.
  #[using="brk mbase draw inp VI VE"] Lemma SH' : usp <= 0x800000000000. Proof. exact (SH sp brk mbase draw inp VI VE). Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition VB (a tid c : word) (pl : placements) (js : list word) : list word :=
    vals0 PH sp draw argv envp uid hw ++ [a; tid; c] ++ pl_list pl ++ js.
  Definition EB (a tid c : word) (pl : placements) (js : list word) : env := Env (vals_ev (VB a tid c pl js)) (blobs0 draw argv).

  #[using="Type"] Lemma EB_EJ : forall a tid c pl js, EB a tid c pl js = EJ sp draw inp a tid c pl js.
  Proof. reflexivity. Qed.
  #[using="Type"] Lemma EB_app : forall a tid c pl js ks, EB a tid c pl (js ++ ks) = Env (vals_ev (VB a tid c pl js ++ ks)) (blobs0 draw argv).
  Proof. intros. unfold EB, VB. rewrite <- !app_assoc. reflexivity. Qed.
  #[using="Type"] Lemma ev_EB_sp : forall a tid c pl js, ev (EB a tid c pl js) 0%nat = sp. Proof. reflexivity. Qed.
  #[using="Type"] Lemma ev_EB_tls : forall a tid c pl js, ev (EB a tid c pl js) V_TLS = a. Proof. reflexivity. Qed.
  #[using="usp"] Lemma length_VB : forall a tid c pl js, length (VB a tid c pl js) = (16 + length js)%nat.
  Proof. intros. unfold VB. rewrite !length_app. cbn. unfold vals0. cbn. lia. Qed.
  #[using="usp"] Lemma ev_EB_js : forall a tid c pl js k, ev (EB a tid c pl js) (16 + k)%nat = nth k js (Z_to_bv 64 0).
  Proof.
    intros. unfold EB, VB. cbn [ev].
    replace (16 + k)%nat with (length (vals0 PH sp draw argv envp uid hw ++ [a; tid; c] ++ pl_list pl) + k)%nat
      by (rewrite !length_app; cbn; unfold vals0; cbn; lia).
    rewrite (app_assoc _ [a; tid; c]), (app_assoc _ (pl_list pl)), vals_ev_app_r. reflexivity.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Record mfacts (E : env) (tid : word) (L : ledger) (mdl : Model) : Prop := MFacts {
    mf_halted : m_halted mdl = None;
    mf_res    : vm_reserved (m_vmmaps mdl) = segments_reserved SEGS;
    mf_isp    : vm_init_sp (m_vmmaps mdl) = sp;
    mf_lim    : vm_limit (m_vmmaps mdl) = lim;
    mf_sbrk   : vm_start_brk (m_vmmaps mdl) = brk;
    mf_brk    : vm_brk (m_vmmaps mdl) = Z_to_bv 64 (bv_unsigned brk + l_brk L);
    mf_mb     : vm_mmap_base (m_vmmaps mdl) = mbase;
    mf_maps   : vm_maps (m_vmmaps mdl) = dl E (l_maps L);
    mf_apart  : ivs_apart (dl E (l_maps L));
    mf_eager  : eager_used mdl <= l_eager L;
    mf_fs     : m_fs mdl = in_fs inp;
    mf_fds    : m_fds mdl = FDS0;
    mf_tid    : m_tid mdl = Some tid;
    mf_wf     : model_ivs_wf mdl;
    mf_na     : na_clear mdl }.

  #[using="Type"] Lemma mfacts_sbm : forall E tid L m m', mfacts E tid L m -> same_but_materialized m m' -> mfacts E tid L m'.
  Proof.
    intros E tid L m m' [F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 F13 F14 F15] HS.
    pose proof (same_but_materialized_frame m m' HS) as (_ & Svm & Slz & _ & _ & _ & _ & _ & Sfds & _ & _ & Sfs & Sh & Stid & _ & _ & Se).
    constructor; rewrite ?Svm, ?Slz, ?Sfds, ?Sfs, ?Sh, ?Stid, ?Se; try assumption.
    - unfold model_ivs_wf in *. rewrite Svm, Slz. exact F14.
    - unfold na_clear in *. rewrite Svm. exact F15.
  Qed.

  #[using="Type"] Lemma ivs_apart_lits : forall l, ivs_apart l <-> OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3RW__A3.BootLedgerA.TwB.apart_all l.
  Proof. induction l as [|[b n] l IH]; cbn; [tauto|]. rewrite IH. tauto. Qed.

  #[using="Type"] Lemma mfacts_env : forall a tid c pl js ks L m,
    ledger_vars_lt (length (VB a tid c pl js)) L = true ->
    mfacts (EB a tid c pl js) tid L m -> mfacts (EB a tid c pl (js ++ ks)) tid L m.
  Proof.
    intros a tid c pl js ks L m HL [F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 F13 F14 F15].
    unfold ledger_vars_lt in HL.
    constructor; try assumption; rewrite EB_app; unfold EB in *; rewrite dl_app_env by assumption; assumption.
  Qed.

  #[using="Type"] Lemma mfacts_alloc_top : forall E tid L m, mfacts E tid L m -> alloc_top (m_vmmaps m) = usp - stack_max_size.
  Proof. intros E tid L m F. unfold alloc_top. rewrite (mf_isp _ _ _ _ F). reflexivity. Qed.

  (* [comment removed for export] *)
  Definition map_ok (E : env) (p : expr * Z) : Prop :=
    let v := bv_unsigned (edenot E (fst p)) in
    v mod 4096 = 0 /\ 4096 <= v /\ 0 < snd p /\ v + snd p <= usp - stack_max_size /\ (v + snd p <= A_img_lo \/ A_img_hi <= v).
  Definition maps_ok (E : env) (L : ledger) : Prop := Forall (map_ok E) (l_maps L).

  #[using="Type"] Lemma maps_ok_env : forall a tid c pl js ks L,
    ledger_vars_lt (length (VB a tid c pl js)) L = true ->
    maps_ok (EB a tid c pl js) L -> maps_ok (EB a tid c pl (js ++ ks)) L.
  Proof.
    intros a tid c pl js ks L HL HM. unfold ledger_vars_lt in HL. rename HL into H1.
    unfold maps_ok in *. apply Forall_forall. intros [e n] Hin. pose proof (proj1 (Forall_forall _ _) HM _ Hin) as Hp.
    unfold map_ok in *. cbn [fst snd] in *. rewrite EB_app. unfold EB in Hp.
    pose proof (proj1 (forallb_forall _ _) H1 _ Hin) as He. cbn [fst] in He.
    rewrite (env_app_edenot _ ks _ e He). exact Hp.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition hfacts : Type := list (Z * Z * option byte).
  Definition hf_ok (H : word -> bool) (M : word -> option byte) (hc : hfacts) : Prop :=
    Forall (fun r => forall x : word, fst (fst r) <= bv_unsigned x < snd (fst r) -> H x = true -> M x = snd r) hc.
  Definition hf_inmaps (E : env) (L : ledger) (hc : hfacts) : Prop :=
    Forall (fun r => exists p, In p (l_maps L)
                     /\ bv_unsigned (edenot E (fst p)) <= fst (fst r) /\ snd (fst r) <= bv_unsigned (edenot E (fst p)) + snd p) hc.

  #[using="Type"] Lemma hf_ok_antimono : forall H H' M hc,
    (forall x, H' x = true -> H x = true) -> hf_ok H M hc -> hf_ok H' M hc.
  Proof.
    intros H H' M hc HH HF. unfold hf_ok in *. apply Forall_forall. intros r Hr x Hx Hh.
    exact (proj1 (Forall_forall _ _) HF r Hr x Hx (HH x Hh)).
  Qed.

  (* [comment removed for export] *)
  Definition H_in_maps (H : word -> bool) (E : env) (L : ledger) : Prop :=
    forall x : word, H x = true ->
      exists p, In p (l_maps L) /\ bv_unsigned (edenot E (fst p)) <= bv_unsigned x < bv_unsigned (edenot E (fst p)) + snd p.

  (* [comment removed for export] *)
  Record regime_ok (H : word -> bool) (A : list (Z * Z)) (hc : hfacts) (E : env) (L : ledger) (mdl : Model) : Prop := RegimeOk {
    rg_off    : H_off_segments SEGS H;
    rg_awf    : A_wf A;
    rg_cover  : lazy_cover H (m_vm_lazy mdl) A;
    rg_inmaps : H_in_maps H E L;
    rg_hcin   : hf_inmaps E L hc;
    rg_above  : forall x : word, usp <= bv_unsigned x -> H x = false;
    rg_lazy   : forall x : word, H x = true -> page_in_ranges (page_base x) (m_vm_lazy mdl) = true;
    rg_shadow : H_in_maps H2 E L   (* [comment removed for export] *) }.

  #[using="Type"] Lemma regime_ok_env : forall H A hc a tid c pl js ks L mdl,
    ledger_vars_lt (length (VB a tid c pl js)) L = true ->
    regime_ok H A hc (EB a tid c pl js) L mdl -> regime_ok H A hc (EB a tid c pl (js ++ ks)) L mdl.
  Proof.
    intros H A hc a tid c pl js ks L mdl HL [G1 G2 G3 G4 G5 G6 G7 G8].
    unfold ledger_vars_lt in HL. rename HL into H1.
    constructor; try assumption.
    - intros x Hx. destruct (G4 x Hx) as ([e n] & Hin & Hr). exists (e, n). split; [exact Hin|]. cbn [fst snd] in *.
      rewrite EB_app. unfold EB in Hr. pose proof (proj1 (forallb_forall _ _) H1 _ Hin) as He. cbn [fst] in He.
      rewrite (env_app_edenot _ ks _ e He). exact Hr.
    - unfold hf_inmaps in *. apply Forall_forall. intros r Hr0. destruct (proj1 (Forall_forall _ _) G5 r Hr0) as ([e n] & Hin & Hr).
      exists (e, n). split; [exact Hin|]. cbn [fst snd] in *.
      rewrite EB_app. unfold EB in Hr. pose proof (proj1 (forallb_forall _ _) H1 _ Hin) as He. cbn [fst] in He.
      rewrite (env_app_edenot _ ks _ e He). exact Hr.
    - intros x Hx. destruct (G8 x Hx) as ([e n] & Hin & Hr). exists (e, n). split; [exact Hin|]. cbn [fst snd] in *.
      rewrite EB_app. unfold EB in Hr. pose proof (proj1 (forallb_forall _ _) H1 _ Hin) as He. cbn [fst] in He.
      rewrite (env_app_edenot _ ks _ e He). exact Hr.
  Qed.

  #[using="Type"] Lemma regime_ok_sbm : forall H A hc E L mdl mdl',
    regime_ok H A hc E L mdl -> same_but_materialized mdl mdl' -> regime_ok H A hc E L mdl'.
  Proof. intros H A hc E L mdl mdl' [G1 G2 G3 G4 G5 G6 G7 G8] HS. constructor; try assumption; rewrite (sbm_lazy _ _ HS); assumption. Qed.

  (* [comment removed for export] *)
  Record bootS (H : word -> bool) (A : list (Z * Z)) (a tid c : word) (pl : placements) (js : list word)
               (sr : list expr) (kn : list kentry) (L : ledger) (hc : hfacts) (lz : list (word * word))
               (R : bvmap 5 word) (M : word -> option byte) (mdl : Model) : Prop := BootS {
    s_regs  : regs_ok (EB a tid c pl js) sr R;
    s_know  : know_ok SEGS (EB a tid c pl js) (mrestrict H M) kn;
    s_above : forall x : word, usp <= bv_unsigned x -> M x = wrap_mem PH sp argv envp uid hw draw x;
    s_hid   : hf_ok H M hc;
    s_lazy  : m_vm_lazy mdl = lz;
    s_minv  : MInv A mdl;
    s_mf    : mfacts (EB a tid c pl js) tid L mdl;
    s_mok   : maps_ok (EB a tid c pl js) L;
    s_rg    : regime_ok H A hc (EB a tid c pl js) L mdl;
    s_tls   : tls_ok sp a;
    s_clear : tls_clear a = true;
    s_tid   : 0 < bv_unsigned tid < 4194304 }.

  (* [comment removed for export] *)
  #[using="Type"] Lemma bootS_reknow : forall H A a tid c pl js sr kn sr' kn' L hc lz R M mdl,
    bootS H A a tid c pl js sr kn L hc lz R M mdl ->
    (regs_ok (EB a tid c pl js) sr R -> regs_ok (EB a tid c pl js) sr' R) ->
    (know_ok SEGS (EB a tid c pl js) (mrestrict H M) kn -> know_ok SEGS (EB a tid c pl js) (mrestrict H M) kn') ->
    bootS H A a tid c pl js sr' kn' L hc lz R M mdl.
  Proof. intros until mdl. intros [G1 G2 G3 G4 G4' G5 G6 G7 G8 G9 G10 G11] HR HK. constructor; auto. Qed.

  #[using="Type"] Lemma bootS_gc : forall H A a tid c pl js sr kn (keep : kentry -> bool) L hc lz R M mdl,
    bootS H A a tid c pl js sr kn L hc lz R M mdl -> bootS H A a tid c pl js sr (List.filter keep kn) L hc lz R M mdl.
  Proof. intros. eapply bootS_reknow; [eassumption | auto |]. intros HK. apply know_ok_filter. exact HK. Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma bootS_sbm : forall H A a tid c pl js sr kn L hc lz R M mdl mdl',
    bootS H A a tid c pl js sr kn L hc lz R M mdl -> MInv A mdl' -> same_but_materialized mdl mdl' ->
    bootS H A a tid c pl js sr kn L hc lz R M mdl'.
  Proof.
    intros until mdl'. intros [G1 G2 G3 G4 G4' G5 G6 G7 G8 G9 G10 G11] HM HS. constructor; auto.
    - rewrite (sbm_lazy _ _ HS). exact G4'.
    - eapply mfacts_sbm; eassumption.
    - eapply regime_ok_sbm; eassumption.
  Qed.

  (* [comment removed for export] *)
  #[using="brk mbase VI VE"] Lemma frame_blockS : forall H a tid c pl js M log hc (lows : list (expr * Z)),
    log_below_b 0%nat lows log = true ->
    lows_ok (EB a tid c pl js) usp lows ->
    (forall x : word, usp <= bv_unsigned x -> H x = false) ->
    (forall x : word, usp <= bv_unsigned x -> M x = wrap_mem PH sp argv envp uid hw draw x) ->
    hf_ok H M hc ->
    let M0 := munrestrict H M (mem_denot (EB a tid c pl js) (mrestrict H M) log) in
    (forall x : word, usp <= bv_unsigned x -> M0 x = wrap_mem PH sp argv envp uid hw draw x)
    /\ hf_ok H M0 hc.
  Proof.
    intros H a tid c pl js M log hc lows Hlog Hlows Hvis HA HZ M0. pose proof SL'. pose proof SH'. split.
    - intros x Hx. unfold M0.
      assert (Hv : H x = false) by (apply Hvis; exact Hx).
      rewrite (munrestrict_visible _ _ _ _ Hv).
      assert (L1 : 2 ^ 41 <= bv_unsigned (ev (EB a tid c pl js) 0%nat)) by (rewrite ev_EB_sp; unfold usp in *; lia).
      assert (L2 : bv_unsigned (ev (EB a tid c pl js) 0%nat) <= usp) by (rewrite ev_EB_sp; unfold usp in *; lia).
      assert (L3 : usp <= 2 ^ 64 - 2 ^ 41) by (unfold usp in *; lia).
      rewrite (mem_denot_above (EB a tid c pl js) (mrestrict H M) log 0%nat lows usp x Hlog L1 L2 L3 Hlows Hx).
      rewrite (mrestrict_visible' _ _ _ Hv). apply HA. exact Hx.
    - unfold hf_ok in *. apply Forall_forall. intros r Hr x Hx Hh. unfold M0.
      rewrite (munrestrict_hidden _ _ _ _ Hh). exact (proj1 (Forall_forall _ _) HZ r Hr x Hx Hh).
  Qed.

  (* [comment removed for export] *)
  Definition lows_of (L : ledger) : list (expr * Z) := l_maps L.
  #[using="Type"] Lemma lows_of_ok : forall E L, maps_ok E L -> lows_ok E usp (lows_of L).
  Proof.
    intros E L HM. unfold lows_ok, lows_of. apply Forall_forall. intros [e n] Hin.
    pose proof (proj1 (Forall_forall _ _) HM _ Hin) as (_ & _ & Hn & Htop & _). cbn [fst snd] in *.
    unfold stack_max_size in Htop. lia.
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Fixpoint gws (nZ : Z) (l : sivs) : Z :=
    match l with [] => 0 | (_, n) :: r => n + nZ + 4095 + gws nZ r end.

  Definition sivs_sizes_ok (l : sivs) : bool := forallb (fun p => (0 <=? snd p) && (snd p <? 2 ^ 64)) l.

  #[using="sp usp"] Lemma gap_weight_dl : forall E nZ l, sivs_sizes_ok l = true -> gap_weight nZ (dl E l) = gws nZ l.
  Proof.
    intros E nZ l. unfold dl. induction l as [|[e n] l IH]; cbn [List.map gap_weight gws sivs_sizes_ok forallb fst snd]; intros Hs; [reflexivity|].
    apply andb_prop in Hs as [Hn Hl]. apply andb_prop in Hn as [H0 H1]. apply Z.leb_le in H0. apply Z.ltb_lt in H1.
    unfold sivs_sizes_ok in IH. rewrite (IH Hl), u_small by lia. reflexivity.
  Qed.

  #[using="Type"] Lemma reserved_dead_above : List.filter (live_at IMG_HI) (segments_reserved SEGS) = [].
  Proof. vmeq_refl. Qed.

  (* [comment removed for export] *)
  #[using="draw VI VE usp"] Lemma grant_exists_L : forall E tid L mdl nZ,
    mfacts E tid L mdl -> 0 < nZ -> sivs_sizes_ok (l_maps L) = true ->
    IMG_HI + nZ + gws nZ (l_maps L) <= 0x7fff80000000 - stack_max_size ->
    exists p, grant_ok_na_pin mdl p nZ = true.
  Proof.
    intros E tid L mdl nZ F HnZ Hs Hw. pose proof SL' as SL. pose proof SH' as SH.
    apply (grant_exists_between mdl nZ IMG_HI HnZ ltac:(unfold IMG_HI; lia) ltac:(reflexivity)).
    rewrite (mf_res _ _ _ _ F), (mf_maps _ _ _ _ F), (mfacts_alloc_top _ _ _ _ F).
    rewrite filter_app, reserved_dead_above, app_nil_l.
    pose proof (gap_weight_filter_le nZ (live_at IMG_HI) (dl E (l_maps L)) ltac:(lia)) as Hle.
    rewrite (gap_weight_dl E nZ (l_maps L) Hs) in Hle. unfold usp in *. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition DS_std (L : ledger) : list (saddr * expr) :=
    [(SA (EVar 0) (- 0x800000), ELit 0x1800000); (SA (ELit 0) A_img_lo, ELit (A_img_hi - A_img_lo));
     (SA (ELit 0) SHB_LO, ELit (SHB_HI - SHB_LO))]
    ++ DS_maps (l_maps L).

  #[using="draw VI VE usp"] Lemma DS_std_claims : forall E tid L mdl nZ,
    mfacts E tid L mdl -> H_in_maps H2 E L -> ev E 0%nat = sp -> sivs_sizes_ok (l_maps L) = true -> 0 < nZ ->
    dsj_claims E (fun p => grant_ok_na_pin mdl p nZ = true) nZ (DS_std L).
  Proof.
    intros E tid L mdl nZ F HSB Hsp Hs HnZ. pose proof SL' as SL. pose proof SH' as SH.
    unfold dsj_claims, DS_std, DS_maps. apply Forall_app. split.
    - constructor; [|constructor; [|constructor; [|constructor]]]; cbn [fst snd]; intros p Hp;
        destruct (grant_ok_na_pin_unpack _ _ _ Hp) as (Hal & Hpos & Htop & Hrf);
        rewrite (mfacts_alloc_top _ _ _ _ F) in Htop; unfold estart, elenZ; cbn [a_base a_off edenot].
      + rewrite Hsp. unfold stack_max_size in Htop. rewrite u_small by lia. unfold usp in *. lia.
      + rewrite (mf_res _ _ _ _ F), (mf_maps _ _ _ _ F), region_free_app in Hrf. apply andb_prop in Hrf as [Hrf _].
        pose proof (u64_range p). pose proof img_hull as IH.
        rewrite !u_small by (unfold A_img_lo, A_img_hi; lia). change (bv_unsigned (Z_to_bv 64 0)) with 0.
        destruct (reserved_apart p nZ HnZ ltac:(unfold stack_max_size, usp in *; lia) Hrf); lia.
      + (* [comment removed for export] *)
        pose proof (u64_range p) as Hpr. unfold SHB_LO, SHB_HI. rewrite !u_small by lia. change (bv_unsigned (Z_to_bv 64 0)) with 0.
        rewrite (mf_res _ _ _ _ F), (mf_maps _ _ _ _ F), region_free_app in Hrf. apply andb_prop in Hrf as [_ Hrf].
        destruct (Z.lt_ge_cases (bv_unsigned p + nZ) (0x7fff7000 + 1)) as [|C1]; [lia|].
        destruct (Z.lt_ge_cases (bv_unsigned p) 0x10007fff8000) as [C2|]; [|lia]. exfalso.
        set (xz := Z.max (bv_unsigned p) 0x7fff7000).
        assert (Hx : exists x : word, bv_unsigned x = xz) by (exists (Z_to_bv 64 xz); apply u_small; unfold stack_max_size in *; lia).
        destruct Hx as (x & Hx).
        destruct (HSB x ltac:(unfold H2, SHB_LO, SHB_HI; rewrite Hx; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia))
          as ([e n] & Hin & Hr). cbn [fst snd] in Hr.
        pose proof (proj1 (forallb_forall _ _) Hs _ Hin) as Hn. cbn [snd] in Hn. apply andb_prop in Hn as [N0 N1].
        apply Z.leb_le in N0. apply Z.ltb_lt in N1.
        pose proof (region_free_In _ p (Z_to_bv 64 nZ) (edenot E e) (Z_to_bv 64 n) Hrf
                      ltac:(unfold dl; apply in_map_iff; exists (e, n); split; [reflexivity | exact Hin])) as Hov.
        rewrite !u_small in Hov by (unfold stack_max_size in *; lia). lia.
    - apply Forall_forall. intros d Hd p Hp. apply in_map_iff in Hd as ([e n] & <- & Hin). cbn [fst snd].
      destruct (grant_ok_na_pin_unpack _ _ _ Hp) as (Hal & Hpos & Htop & Hrf).
      rewrite (mf_res _ _ _ _ F), (mf_maps _ _ _ _ F), region_free_app in Hrf. apply andb_prop in Hrf as [_ Hrf].
      pose proof (proj1 (forallb_forall _ _) Hs _ Hin) as Hn. cbn [snd] in Hn. apply andb_prop in Hn as [H0 H1].
      apply Z.leb_le in H0. apply Z.ltb_lt in H1.
      rewrite (mfacts_alloc_top _ _ _ _ F) in Htop. unfold stack_max_size, usp in *. pose proof SH.
      pose proof (region_free_In _ p (Z_to_bv 64 nZ) (edenot E e) (Z_to_bv 64 n) Hrf
                    ltac:(unfold dl; apply in_map_iff; exists (e, n); split; [reflexivity | exact Hin])) as Hov.
      rewrite !u_small in Hov by lia. unfold estart, elenZ. cbn [a_base a_off edenot]. rewrite !u_small by lia.
      change (bv_unsigned (Z_to_bv 64 0)) with 0. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="draw VI VE usp"] Lemma grant_misses_shadow : forall E tid L mdl p nZ,
    mfacts E tid L mdl -> H_in_maps H2 E L -> ev E 0%nat = sp -> sivs_sizes_ok (l_maps L) = true -> 0 < nZ ->
    grant_ok_na_pin mdl p nZ = true -> bv_unsigned p + nZ <= SHB_LO \/ SHB_HI <= bv_unsigned p.
  Proof.
    intros E tid L mdl p nZ F HSB Hsp Hs HnZ Hp.
    pose proof (DS_std_claims E tid L mdl nZ F HSB Hsp Hs HnZ) as C. unfold dsj_claims, DS_std in C.
    apply Forall_app in C as [C _]. apply Forall_cons_iff in C as [_ C]. apply Forall_cons_iff in C as [_ C]. apply Forall_cons_iff in C as [C _].
    specialize (C p Hp). unfold estart, elenZ in C. cbn [fst snd a_base a_off edenot] in C.
    unfold SHB_LO, SHB_HI in *. rewrite !u_small in C by lia. change (bv_unsigned (Z_to_bv 64 0)) with 0 in C. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="usp"] Lemma grant_visible_L : forall H E tid L mdl p nZ,
    mfacts E tid L mdl -> H_in_maps H E L -> sivs_sizes_ok (l_maps L) = true -> 0 <= nZ ->
    grant_ok_na_pin mdl p nZ = true -> range_visible H p nZ.
  Proof.
    intros H E tid L mdl p nZ F Hin Hs HnZ Hp.
    apply (grant_visible_of_hidden_mapped H mdl p nZ); [| exact HnZ | exact Hp].
    intros x Hx. destruct (Hin x Hx) as ([e n] & Hi & Hr). cbn [fst snd] in Hr.
    pose proof (proj1 (forallb_forall _ _) Hs _ Hi) as Hn. cbn [snd] in Hn. apply andb_prop in Hn as [H0 H1].
    apply Z.leb_le in H0. apply Z.ltb_lt in H1.
    exists (edenot E e, Z_to_bv 64 n). split.
    - rewrite (mf_maps _ _ _ _ F). unfold dl. apply in_map_iff. exists (e, n). split; [reflexivity | exact Hi].
    - cbn [fst snd]. rewrite u_small by lia. exact Hr.
  Qed.

  (* [comment removed for export] *)
  Definition lgrant (L : ledger) (v : nat) (nZ : Z) : ledger :=
    Ledger ((EVar v, nZ) :: l_maps L) (l_brk L) (l_eager L + nZ).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition kn_grant (L : ledger) (v : nat) (nZ : Z) (kn : list kentry) : list kentry := kn_grant_d (DS_std L) v nZ kn.

  #[using="Type"] Lemma t_alt2_nil_l : forall (T : TSet), T [] -> t_eq (t_alt2 t_nil T) T.
  Proof. intros T HT tr. unfold t_alt2, t_nil. split; [intros [->|H]; assumption | intros H; right; exact H]. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="VI VE"] Theorem bs_mmap_rw_spin : forall H A a tid c pl js sr kn L zr lz (len pc : Z) w R M mdl (K : TSet),
    let E := EB a tid c pl js in
    let v := length (VB a tid c pl js) in
    let nZ := page_round_up_Z len in
    bootS H A a tid c pl js sr kn L zr lz R M mdl ->
    fetch_word SEGS (Z_to_bv 64 pc) = Some w -> is_ecall w = true -> 0 <= pc -> pc + 4 < 2 ^ 64 ->
    sr_vars_lt v sr = true -> kn_vars_lt v kn = true -> ledger_vars_lt v L = true -> sivs_sizes_ok (l_maps L) = true ->
    sr_get sr 17%bv = ELit 222 -> sr_get sr 10%bv = ELit 0 -> sr_get sr 11%bv = ELit len -> sr_get sr 12%bv = ELit 3 ->
    sr_get sr 13%bv = ELit 34 -> sr_get sr 14%bv = ELit (2 ^ 64 - 1) -> sr_get sr 15%bv = ELit 0 ->
    0 < len -> l_eager L + nZ + A_bytes A <= lim ->
    IMG_HI + nZ + gws nZ (l_maps L) <= 0x7fff80000000 - stack_max_size ->
    (forall p R' M' mdl', bootS H A a tid c pl (js ++ [p]) (sr_upd sr 10 (EVar v)) (kn_grant L v nZ kn) (lgrant L v nZ) zr lz R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 (pc + 4)) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 pc) M ROM) mdl) K.
  Proof.
    intros H A a tid c pl js sr kn L zr lz len pc w R M mdl K E v nZ HB HF HE Hpc0 Hpc4
           Hsr Hkn HL Hs S17 S10 S11 S12 S13 S14 S15 Hlen Hbud Hroom HK.
    destruct HB as [HR HKN HA HZ HLZ HM F HMO RG HT Hcl Ht]. pose proof RG as [HH HAW HCOV HIN Hhin Habv Hhl Hshd].
    pose proof SL' as SL. pose proof SH' as SH. assert (SMS : stack_max_size = 8388608) by reflexivity.
    assert (USP : usp = bv_unsigned sp) by reflexivity.
    assert (HnZ : len <= nZ /\ nZ < len + 4096) by (unfold nZ; pose proof (page_round_up_Z_bounds len ltac:(lia)); unfold page_size in *; lia).
    assert (Hlen64 : len < 2 ^ 64).
    { unfold stack_max_size, IMG_HI in Hroom. pose proof (gap_weight_nonneg nZ (dl E (l_maps L)) ltac:(lia)) as W.
      rewrite (gap_weight_dl E nZ _ Hs) in W. lia. }
    assert (G : forall r z, sr_get sr r = ELit z -> getr R r = Z_to_bv 64 z).
    { intros r z Hz. rewrite (HR r), Hz. reflexivity. }
    eapply (srz_mmap_rw_pin SEGS R (Z_to_bv 64 pc) M ROM mdl w len (Z_to_bv 64 34) K HF HE (mf_halted _ _ _ _ F)
              (G _ _ S17) (G _ _ S11) ltac:(lia) (G _ _ S12) (G _ _ S13) eq_refl).
    - rewrite (G _ _ S14). apply bv_eq. reflexivity.
    - exact (G _ _ S15).
    - exact (grant_exists_L E tid L mdl nZ F ltac:(lia) Hs Hroom).
    - (* [comment removed for export] *)
      unfold mmap_noreserve_backed_ok. cbn [mmap_noreserve_b]. change (negb _) with false. cbn [negb].
      apply Z.leb_le. rewrite vm_backing_used_split, (mf_lim _ _ _ _ F).
      destruct HM as [N1 N2 N3 N4 N5].
      pose proof (allowed_pages_bound A (m_vm_materialized mdl) HAW N1 N2 N3) as PB.
      pose proof (mf_eager _ _ _ _ F). rewrite (mf_lim _ _ _ _ F) in N5. lia.
    - (* [comment removed for export] *)
      intros p Hp. rewrite pc_lit_add4 by lia. rewrite with_mmap_backing_eager by reflexivity. fold nZ. fold nZ in Hp.
      destruct (grant_ok_na_pin_unpack _ _ _ Hp) as (Hal & Hpos & Htop & Hrf).
      rewrite (mfacts_alloc_top _ _ _ _ F) in Htop.
      pose proof (u64_range p) as Hpr.
      assert (Hvis : range_visible H p nZ) by (apply (grant_visible_L H E tid L mdl p nZ F HIN Hs ltac:(lia) Hp)).
      assert (Hev : edenot (EB a tid c pl (js ++ [p])) (EVar v) = p).
      { rewrite EB_app. cbn [edenot ev]. unfold v. rewrite <- (Nat.add_0_r (length _)), vals_ev_app_r. reflexivity. }
      set (n := Z_to_bv 64 nZ) in *.
      assert (Hun : bv_unsigned n = nZ) by (unfold n; apply u_small; unfold stack_max_size in Htop; unfold usp in *; lia).
      assert (Himg : bv_unsigned p + nZ <= A_img_lo \/ A_img_hi <= bv_unsigned p).
      { rewrite (mf_res _ _ _ _ F), (mf_maps _ _ _ _ F), region_free_app in Hrf. apply andb_prop in Hrf as [Hrf _].
        apply (reserved_apart p nZ); [lia | unfold stack_max_size, usp in *; lia | exact Hrf]. }
      apply (HK p). constructor.
      + (* [comment removed for export] *)
        apply regs_ok_set; [| intros X; apply (f_equal bv_unsigned) in X; discriminate X | exact Hev].
        rewrite EB_app. apply env_app_regs; [exact Hsr | exact HR].
      + (* [comment removed for export] *)
        rewrite (mrestrict_zfill H p n M) by (rewrite Hun; exact Hvis).
        assert (KO' : know_ok SEGS (EB a tid c pl (js ++ [p])) (mrestrict H M) kn).
        { rewrite EB_app. apply env_app_know; [exact Hkn | exact HKN]. }
        assert (KF : forall V, know_ok SEGS (EB a tid c pl (js ++ [p])) V
                       [KAlign (EVar v) 4096; KRange (EVar v) 4096 (2 ^ 64 - stack_max_size - nZ)]).
        { intros V. rewrite EB_app. unfold v. apply kfacts_grant; try assumption; unfold stack_max_size, usp in *; lia. }
        assert (KD : forall V, know_ok SEGS (EB a tid c pl (js ++ [p])) V (dsj_entries v nZ (DS_std L))).
        { intros V. rewrite EB_app. unfold v.
          apply (dsj_entries_ok SEGS (VB a tid c pl js) (blobs0 draw argv) V _ nZ (DS_std L) p ltac:(lia)
                   ltac:(unfold stack_max_size, usp in *; lia) (DS_std_claims E tid L mdl nZ F Hshd (ev_EB_sp a tid c pl js) Hs ltac:(lia)) Hp).
          unfold DS_std, DS_maps. apply Forall_app. split.
          - constructor; [cbn; split; reflexivity|]. constructor; [cbn; split; reflexivity|]. constructor; [cbn; split; reflexivity|]. constructor.
          - apply Forall_forall. intros d Hd. apply in_map_iff in Hd as ([e en] & <- & Hin). cbn [fst snd]. split; [|reflexivity].
            unfold ledger_vars_lt in HL.
            cbn [saddr_vars_lt a_base]. exact (proj1 (forallb_forall _ _) HL _ Hin). }
        unfold kn_grant, kn_grant_d. apply (proj2 (know_ok_app SEGS _ _ _ _)); split; [|apply (proj2 (know_ok_app SEGS _ _ _ _)); split].
        * unfold GF. rewrite <- Hun.
          constructor; [apply kzero_zfill; [exact Hev | lia | rewrite Hun; unfold stack_max_size, usp in *; lia]|].
          constructor; [apply kwr_zfill; [exact Hev | lia | rewrite Hun; unfold stack_max_size, usp in *; lia]|].
          rewrite Hun. apply KF.
        * apply KD.
        * apply (kn_keep_sound SEGS _ (mrestrict H M) (zfill p n (mrestrict H M)) MGrow).
          -- apply (proj2 (know_ok_app SEGS _ _ _ _)); split; [apply KF|].
             apply (proj2 (know_ok_app SEGS _ _ _ _)); split; [apply KD | exact KO'].
          -- exact KO'.
          -- unfold estart, elenZ. cbn [a_base a_off]. rewrite Hev. cbn [edenot]. fold n. rewrite Hun.
             rewrite Z.add_0_r, <- Hun. apply mem_change_zfill.
      + (* [comment removed for export] *)
        intros x Hx. rewrite zfill_out; [apply HA; exact Hx|]. rewrite Hun. unfold stack_max_size, usp in *. lia.
      + (* [comment removed for export] *)
        unfold hf_ok in HZ |- *.
        apply Forall_forall. intros r Hr x Hx Hhx. rewrite zfill_out; [exact (proj1 (Forall_forall _ _) HZ r Hr x Hx Hhx)|].
        rewrite Hun.
        destruct (Z.lt_ge_cases (bv_unsigned x) (bv_unsigned p)); [left; assumption|].
        destruct (Z.lt_ge_cases (bv_unsigned x) (bv_unsigned p + nZ)); [|right; assumption].
        exfalso. rewrite (Hvis x ltac:(lia)) in Hhx. discriminate.
      + (* [comment removed for export] *) rewrite mmap_model_lazy. exact HLZ.
      + (* [comment removed for export] *)
        pose proof (mf_wf _ _ _ _ F) as (W1 & W2 & W3 & W4).
        apply MInv_mmap_model; [exact W1 | apply iv_wf_intro; rewrite Hun; lia | exact HM |].
        rewrite Hun, (mf_lim _ _ _ _ F). pose proof (mf_eager _ _ _ _ F). lia.
      + (* [comment removed for export] *)
        pose proof (mf_wf _ _ _ _ F) as (W1 & W2 & W3 & W4).
        pose proof HL as HL1. unfold ledger_vars_lt in HL1.
        constructor; rewrite ?mmap_model_vm; cbn [vm_reserved vm_maps vm_noaccess vm_start_brk vm_brk vm_limit vm_mmap_base vm_init_sp];
          try (rewrite EB_app; unfold E, EB in F; rewrite (dl_app_env _ [p] _ _) by assumption).
        * rewrite mmap_model_halted. exact (mf_halted _ _ _ _ F).
        * exact (mf_res _ _ _ _ F).
        * exact (mf_isp _ _ _ _ F).
        * exact (mf_lim _ _ _ _ F).
        * exact (mf_sbrk _ _ _ _ F).
        * cbn [lgrant l_brk]. exact (mf_brk _ _ _ _ F).
        * exact (mf_mb _ _ _ _ F).
        * cbn [lgrant l_maps dl List.map fst snd]. rewrite Hev, (mf_maps _ _ _ _ F). fold (dl (EB a tid c pl (js ++ [p])) (l_maps L)).
          rewrite EB_app. unfold E, EB. rewrite (dl_app_env _ [p] _ _ HL1). reflexivity.
        * (* [comment removed for export] *)
          cbn [lgrant l_maps ivs_apart dl List.map fst snd]. fold (dl (EB a tid c pl (js ++ [p])) (l_maps L)). rewrite Hev.
          rewrite EB_app. unfold E, EB in F |- *. rewrite (dl_app_env _ [p] _ _ HL1). rewrite <- (mf_maps _ _ _ _ F).
          rewrite region_free_app in Hrf. apply andb_prop in Hrf as [_ Hrf2].
          split; [| rewrite (mf_maps _ _ _ _ F); exact (mf_apart _ _ _ _ F)].
          apply Forall_forall. intros [qb qn] Hq. cbn [fst snd].
          pose proof (region_free_In _ p n qb qn Hrf2 Hq) as Hov. rewrite Hun in Hov. fold n. rewrite Hun. lia.
        * cbn [lgrant l_eager]. pose proof (eager_used_mmap_model_le p n mdl W1 ltac:(apply iv_wf_intro; rewrite Hun; lia)).
          rewrite Hun in *. pose proof (mf_eager _ _ _ _ F). lia.
        * rewrite mmap_model_fs. exact (mf_fs _ _ _ _ F).
        * rewrite mmap_model_fds. exact (mf_fds _ _ _ _ F).
        * rewrite mmap_model_tid. exact (mf_tid _ _ _ _ F).
        * unfold model_ivs_wf. rewrite mmap_model_vm, mmap_model_lazy. cbn [vm_maps vm_noaccess vm_init_sp].
          split; [apply ivs_wf_cons; [apply iv_wf_intro; rewrite Hun; lia | exact W1]|]. split; [exact W2|]. split; [exact W3|]. exact W4.
        * unfold na_clear. rewrite mmap_model_vm. cbn [vm_noaccess]. exact (mf_na _ _ _ _ F).
      + (* [comment removed for export] *)
        unfold maps_ok, lgrant. cbn [l_maps]. constructor.
        * unfold map_ok. cbn [fst snd]. rewrite Hev. unfold stack_max_size, page_size in *.
          split; [exact Hal|]. split; [|split; [lia | split; [lia | exact Himg]]].
          pose proof (Z.mod_pos_bound (bv_unsigned p) 4096 ltac:(lia)). pose proof (Z.div_mod (bv_unsigned p) 4096 ltac:(lia)). nia.
        * exact (maps_ok_env a tid c pl js [p] L HL HMO).
      + (* [comment removed for export] *)
        pose proof (regime_ok_env H A zr a tid c pl js [p] L mdl HL RG) as [Q1 Q2 Q3 Q4 Q5 Q6 Q7 Q8].
        constructor; try assumption; try (rewrite mmap_model_lazy; assumption).
        -- intros x Hx. destruct (Q4 x Hx) as (q & Hq & Hr). exists q. split; [| exact Hr]. unfold lgrant. cbn [l_maps]. right. exact Hq.
        -- unfold hf_inmaps in *. apply Forall_forall. intros r Hr0. destruct (proj1 (Forall_forall _ _) Q5 r Hr0) as (q & Hq & Hr).
           exists q. split; [| exact Hr]. unfold lgrant. cbn [l_maps]. right. exact Hq.
        -- intros x Hx. destruct (Q8 x Hx) as (q & Hq & Hr). exists q. split; [| exact Hr]. unfold lgrant. cbn [l_maps]. right. exact Hq.
      + exact HT.
      + exact Hcl.
      + exact Ht.
  Qed.
End Theorems.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac rg_block VI VE HB HK RUN CAR :=
  lazymatch type of VE with valid_entry _ (mkEntry ?sp ?brk ?mbase ?draw) ?inp =>
    let HR := fresh "HR" in let HKN := fresh "HKN" in let HA := fresh "HA" in let HZ := fresh "HZ" in
    let HM := fresh "HM" in let F := fresh "F" in let HMO := fresh "HMO" in let RG := fresh "RG" in
    let HT := fresh "HT" in let Hcl := fresh "Hcl" in let Ht := fresh "Ht" in let HLZ := fresh "HLZ" in
    destruct HB as [HR HKN HA HZ HLZ HM F HMO RG HT Hcl Ht];
    let HH := fresh "HH" in let Hwx := fresh "Hwx" in let HAW := fresh "HAW" in let Hh := fresh "Hh" in let HL := fresh "HL" in
    pose proof (rg_off _ _ _ _ _ _ _ RG) as HH; pose proof wx_nowrap as Hwx; pose proof (rg_awf _ _ _ _ _ _ _ RG) as HAW;
    pose proof (mf_halted _ _ _ _ _ _ _ _ _ F) as Hh;
    pose proof (rg_cover _ _ _ _ _ _ _ RG) as HL;
    run_block_K HR HKN HM HL Hh HH Hwx HAW RUN CAR;
    lazymatch goal with |- srealizes _ (mkCfg (mkst _ _ ?m _) _) _ =>
      let body := eval unfold m in m in
      lazymatch body with munrestrict ?H ?M (mem_denot (EB _ _ _ ?a ?tid ?c ?pl ?js) _ ?lg) =>
        lazymatch type of F with mfacts _ _ _ _ _ _ _ ?L _ =>
          lazymatch type of HZ with hf_ok _ _ ?hc =>
            destruct (frame_blockS sp brk mbase draw inp VI VE H a tid c pl js M lg hc (lows_of L) ltac:(vmeq_refl)
                        (lows_of_ok sp _ L HMO) (rg_above _ _ _ _ _ _ _ RG) HA HZ) as [HA0 HZ0];
            subst m
          end end end end;
    apply HK; constructor; try assumption;
      [ erewrite sbm_lazy by eassumption; exact HLZ | eapply mfacts_sbm; eassumption | eapply regime_ok_sbm; eassumption]
  end.
End TwB.
(* [comment removed for export] *) Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
