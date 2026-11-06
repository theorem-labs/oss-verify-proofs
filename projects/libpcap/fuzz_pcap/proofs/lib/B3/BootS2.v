(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require PropExec__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require CatSim__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require StoreOk StepTac. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require RefLayout__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require ArgvEnv__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AsanAcct__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AllocSim MmapSim. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AsanHexScan__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require FileSim__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require RefNodes. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AllocSim2__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require SpinAlg. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AsanNodesMmLib AsanNodesLibE BackingAlgebra. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.CatExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.CatSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.SeqExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.StoreOk OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.StepTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.RefLayout__Common.AgentLib OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.ArgvEnv__Common.StartupAux OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.RefLayout__Common.RefLayout OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.ArgvEnv__Common.ArgvEnv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.ArgvEnv__Common.MemSplit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanAcct__Common.Hoare OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AllocSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.MmapSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanHexScan__Common.ExitSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanHexScan__Common.SimInv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.FileSim__Common.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.FileSim__Common.AgentNodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.RefNodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanHexScan__Common.AsanCeil OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AllocSim2__Common.ShapeAlg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanAcct__Common.ErrEscape OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.SpinAlg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.DivergeSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanAcct__Common.AsanAcct OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.RefLayout__Common.AsanAcctShape OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanNodesMmLib OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanNodesLibE OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.BackingAlgebra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AxSymExec3 AxSymExec3Sound. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AxSymRun3__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AsanPlanCore AsanPlan. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AxSymExec3F. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3Sound OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymRun3__Common.AxSymRun3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanPlanCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanPlan OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymRun3__Common.KnApart OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3F.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require EntryKn StdioSymDrive EntryGlue. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require NodesFs__Lib. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require AsanBlock__Lib. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require AsanKnow. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.EntryKn OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.StdioSymDrive OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.EntryGlue OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.NodesFs__Lib.NodesMm OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBlock__Lib.AsanBlock OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanKnow.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require A3Img. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require A3Syms__A3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require A3Sums. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Img.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3Syms.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3SymsBoot.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Sums.TwB.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require ArgvEnv__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require RefLayout__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require SumsLib. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.ArgvEnv__Common.ZStores OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.RefLayout__Common.RefMemcpyLib OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.SumsLib.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require Import AsanIStrncpy.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require AsanBootKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require AsanNodes__Lib. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBootKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanNodes__Lib.AsanNodesBoot.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require A3Syms__A3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootImg. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootKn1__A3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require Boot1 Boot2 Boot3 BootS1. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require A3RW__A3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3SymsBootW.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn1.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.Boot1.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.Boot2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.Boot3.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootS1.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3RW__A3.BootLedgerA.TwB.
Import ListNotations.
Import AX2. Import AX2S.
#[local] Instance boots2_fx : OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec.FPState := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec.fx0.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition H2 (x : word) : bool := (SHB_LO <=? bv_unsigned x) && (bv_unsigned x <? SHB_HI).
Definition A2 : list (Z * Z) := [].

Lemma H2_off : H_off_segments SEGS H2.
Proof.
  apply H_off_segments_img. intros a Ha. unfold H2, SHB_LO, IMG_HI in *.
  apply andb_prop in Ha as [Ha _]. apply Z.leb_le in Ha. lia.
Qed.
Lemma A2_wf : A_wf A2. Proof. constructor. Qed.
Lemma H2_in : forall x : word, SHB_LO <= bv_unsigned x < SHB_HI -> H2 x = true.
Proof. intros x Hx. unfold H2. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. Qed.
Lemma H2_out : forall x : word, bv_unsigned x < SHB_LO \/ SHB_HI <= bv_unsigned x -> H2 x = false.
Proof.
  intros x Hx. unfold H2. destruct Hx as [Hx|Hx].
  - rewrite (proj2 (Z.leb_gt _ _)) by lia. reflexivity.
  - rewrite (proj2 (Z.ltb_ge _ _)) by lia. apply andb_false_r.
Qed.

(* [comment removed for export] *)
Definition FL_NR : word := Z_to_bv 64 0x104022.    (* [comment removed for export] *)
Lemma FL_NR_core : mmap_flags_core FL_NR = NR_CORE. Proof. vmeq_refl. Qed.
Lemma FL_NR_noreserve : mmap_noreserve_b FL_NR = true. Proof. vmeq_refl. Qed.

Definition LO_A : word := Z_to_bv 64 0x7fff7000.
Definition LO_LEN : Z := 2 ^ 28.
Definition LO_N : word := Z_to_bv 64 (page_round_up_Z LO_LEN).
Lemma LO_N_val : bv_unsigned LO_N = 2 ^ 28. Proof. vmeq_refl. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma KN_E3d_apart : List.filter (AP.kentry_apart_b KN_E3d (ELit 0) SHB_LO (ELit (SHB_HI - SHB_LO))) KN_E3d = KN_E3d.
Proof. vmeq_refl. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Theorems.
  Variables (sp brk mbase : word) (draw : EntryDraw) (lim : Z) (inp : ProcInput).
  Hypothesis VI : valid_input inp.
  Hypothesis VE : valid_entry IMG (mkEntry sp brk mbase draw) inp.

  Let argv := in_argv inp.
  Let envp := in_envp inp.
  Let uid := in_uid inp.
  Let hw := in_hwcap inp.
  Let usp := bv_unsigned sp.

  #[using="brk mbase draw inp VI VE"] Lemma SL : 0x7fff80000000 <= usp. Proof. destruct (Hsp sp brk mbase draw inp VI VE) as (H & _ & _). exact H. Qed.
  #[using="brk mbase draw inp VI VE"] Lemma SH : usp <= 0x800000000000. Proof. destruct (Hsp sp brk mbase draw inp VI VE) as (_ & H & _). exact H. Qed.

  (* [comment removed for export] *)
  Definition M_E3g (a tid : word) : Model := noreplace_model 3 FL_NR LO_A LO_N (M_E3 sp brk mbase lim inp a tid).

  #[using="Type"] Lemma M_E3_vm : forall a tid,
    m_vmmaps (M_E3 sp brk mbase lim inp a tid) = mkVmMapsFull (segments_reserved SEGS) [] [] brk brk lim mbase sp.
  Proof. intros. reflexivity. Qed.
  #[using="Type"] Lemma M_E3_halted : forall a tid, m_halted (M_E3 sp brk mbase lim inp a tid) = None. Proof. intros. reflexivity. Qed.
  #[using="Type"] Lemma M_E3_lazy : forall a tid, m_vm_lazy (M_E3 sp brk mbase lim inp a tid) = []. Proof. intros. reflexivity. Qed.
  #[using="Type"] Lemma M_E3_mat : forall a tid, m_vm_materialized (M_E3 sp brk mbase lim inp a tid) = []. Proof. intros. reflexivity. Qed.

  (* [comment removed for export] *)
  #[using="usp"] Lemma KN_E3d_ok : forall a tid c M,
    tls_ok sp a -> tls_clear a = true ->
    know_ok SEGS (E10 sp draw argv envp uid hw a tid c) M KN_E3 ->
    know_ok SEGS (E10 sp draw argv envp uid hw a tid c) M KN_E3d.
  Proof.
    intros a tid c M HT Hcl HK. unfold KN_E3d. constructor; [|exact HK].
    cbn [kentry_ok KDJ_TLS]. unfold estart, elenZ. cbn [a_base a_off edenot]. rewrite ev_E10_tls.
    rewrite !u_small by (unfold SHB_LO, SHB_HI; lia). unfold SHB_LO, SHB_HI.
    unfold tls_clear in Hcl. apply orb_prop in Hcl as [Hc|Hc]; [apply Z.leb_le in Hc | apply Z.leb_le in Hc]; lia.
  Qed.

  (* [comment removed for export] *)
  #[using="usp"] Lemma know_shadow_change : forall a tid c M M',
    know_ok SEGS (E10 sp draw argv envp uid hw a tid c) M KN_E3d ->
    (forall x : word, bv_unsigned x < SHB_LO \/ SHB_HI <= bv_unsigned x -> M' x = M x) ->
    know_ok SEGS (E10 sp draw argv envp uid hw a tid c) M' KN_E3d.
  Proof.
    intros a tid c M M' HK Hout. rewrite <- KN_E3d_apart.
    eapply KNA.know_ok_filter_apart; [exact HK | intros K _ Hb; left; exact Hb |].
    intros x Hx. apply Hout. unfold estart, elenZ in Hx. cbn [a_base a_off edenot] in Hx.
    rewrite !u_small in Hx by (unfold SHB_LO, SHB_HI; lia). unfold SHB_LO, SHB_HI in *. lia.
  Qed.
  (* [comment removed for export] *)
  #[using="Type"] Lemma e3_regs : forall a tid c R, regs_ok (E10 sp draw argv envp uid hw a tid c) SR_E3 R ->
    getr R 17%bv = Z_to_bv 64 222 /\ getr R 10%bv = LO_A /\ getr R 11%bv = Z_to_bv 64 LO_LEN
    /\ getr R 12%bv = Z_to_bv 64 3 /\ getr R 13%bv = FL_NR /\ getr R 15%bv = Z_to_bv 64 0.
  Proof. intros a tid c R HR. repeat split; rewrite (HR _); try reflexivity. Qed.

  (* [comment removed for export] *)
  #[using="draw VI VE usp"] Lemma M_E3_wf : forall a tid, model_ivs_wf (M_E3 sp brk mbase lim inp a tid).
  Proof.
    intros a tid. unfold model_ivs_wf. rewrite M_E3_vm, M_E3_lazy. cbn [vm_maps vm_noaccess].
    split; [apply ivs_wf_nil | split; [apply ivs_wf_nil | split; [apply ivs_wf_nil |]]].
    unfold init_sp_ok. cbn [vm_init_sp]. destruct (Hsp sp brk mbase draw inp VI VE) as (H & _ & _). exact H.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma M_E3g_post : forall a tid, grant_post AP.KRWLAZY LO_A LO_N (M_E3 sp brk mbase lim inp a tid) (M_E3g a tid).
  Proof.
    intros a tid. unfold M_E3g, noreplace_model, with_mmap_backing. rewrite FL_NR_noreserve.
    generalize (M_E3 sp brk mbase lim inp a tid) as m. intros m. destruct m. constructor; reflexivity.
  Qed.

  #[using="draw VI VE usp"] Lemma M_E3g_wf : forall a tid, model_ivs_wf (M_E3g a tid).
  Proof.
    intros a tid. pose proof (M_E3_wf a tid) as (W1 & W2 & W3 & W4). pose proof (M_E3g_post a tid) as GP.
    assert (ULO : bv_unsigned LO_A = SHB_LO) by (vmeq_refl).
    assert (IW : iv_wf (LO_A, LO_N)) by (unfold iv_wf, B, S; cbn [fst snd]; rewrite LO_N_val, ULO; unfold SHB_LO; lia).
    unfold model_ivs_wf.
    rewrite (gp_maps _ _ _ _ _ GP), (gp_noacc _ _ _ _ _ GP), (gp_lazy _ _ _ _ _ GP). cbn [kind_none kind_lazy].
    split; [apply ivs_wf_cons; assumption|]. split; [exact W2|]. split; [apply ivs_wf_cons; assumption|].
    unfold init_sp_ok in *. rewrite (gp_isp _ _ _ _ _ GP). exact W4.
  Qed.

  (* [comment removed for export] *)
  #[using="draw VI VE usp"] Lemma M_E3g_eager : forall a tid, eager_used (M_E3g a tid) = 0.
  Proof.
    intros a tid. pose proof (M_E3g_post a tid) as GP.
    rewrite (eager_used_sem _ (M_E3g_wf a tid)).
    rewrite (gp_maps _ _ _ _ _ GP), (gp_noacc _ _ _ _ _ GP), (gp_lazy _ _ _ _ _ GP), M_E3_vm, M_E3_lazy.
    cbn [kind_none kind_lazy vm_maps vm_noaccess app sum_count].
    unfold iv_count, B, S. cbn [fst snd]. rewrite LO_N_val.
    assert (ULO : bv_unsigned LO_A = SHB_LO) by (vmeq_refl). rewrite ULO.
    rewrite zcount_false; [lia|].
    intros x Hx. rewrite Z2Nat.id in Hx by lia.
    apply negb_false_iff. unfold covered. cbn [existsb]. unfold in_iv, in_rng, B, S. cbn [fst snd].
    rewrite ULO, LO_N_val. rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity.
  Qed.

  #[using="draw VI VE usp"] Lemma M_E3g_MInv : forall a tid, 4096 <= lim -> MInv A2 (M_E3g a tid).
  Proof.
    intros a tid Hlim. pose proof (M_E3g_post a tid) as GP.
    assert (MT : m_vm_materialized (M_E3g a tid) = []) by (rewrite (gp_mat _ _ _ _ _ GP); apply M_E3_mat).
    constructor; rewrite ?MT.
    - constructor.
    - intros p [].
    - intros p [].
    - intros p [].
    - rewrite (M_E3g_eager a tid), (gp_limit _ _ _ _ _ GP), M_E3_vm. cbn. lia.
  Qed.

  #[using="Type"] Lemma M_E3g_lazy : forall a tid, m_vm_lazy (M_E3g a tid) = [(LO_A, LO_N)].
  Proof. intros. rewrite (gp_lazy _ _ _ _ _ (M_E3g_post a tid)), M_E3_lazy. reflexivity. Qed.
  #[using="Type"] Lemma M_E3g_halted : forall a tid, m_halted (M_E3g a tid) = None.
  Proof. intros. rewrite (gp_halted _ _ _ _ _ (M_E3g_post a tid)). apply M_E3_halted. Qed.

  #[using="usp"] Lemma H2_cover_E3g : forall a tid, lazy_cover H2 (m_vm_lazy (M_E3g a tid)) A2.
  Proof.
    intros a tid w Hp Hh. exfalso. rewrite M_E3g_lazy in Hp.
    apply page_in_ranges_true in Hp as (iv & Hin & P1 & P2). destruct Hin as [<-|[]]. cbn [fst snd] in P1, P2.
    assert (ULO : bv_unsigned LO_A = SHB_LO) by (vmeq_refl).
    rewrite ULO in *. rewrite LO_N_val in *.
    assert (PB : bv_unsigned (page_base w) <= bv_unsigned w < bv_unsigned (page_base w) + page_size).
    { unfold page_base, page_base_of, page_size. pose proof (u64_range w) as W.
      pose proof (Z.div_mod (bv_unsigned w) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (bv_unsigned w) 4096 ltac:(lia)).
      rewrite u_small by lia. lia. }
    rewrite (H2_in w) in Hh; [discriminate|]. unfold page_size, SHB_LO, SHB_HI in *. lia.
  Qed.
  (* [comment removed for export] *)
  Record at_E3g (a tid c : word) (R : bvmap 5 word) (M : word -> option byte) (mdl : Model) : Prop := AtE3g {
    g3_regs  : regs_ok (E10 sp draw argv envp uid hw a tid c) SR8 R;
    g3_know  : know_ok SEGS (E10 sp draw argv envp uid hw a tid c) (mrestrict H2 M) KN_E3d;
    g3_above : forall x : word, usp <= bv_unsigned x -> M x = wrap_mem PH sp argv envp uid hw draw x;
    g3_lowz  : forall x : word, SHB_LO <= bv_unsigned x < SHB_LO + 2 ^ 28 -> M x = Some (Z_to_bv 8 0);
    g3_minv  : MInv A2 mdl;
    g3_same  : same_but_materialized (M_E3g a tid) mdl;
    g3_tls   : tls_ok sp a;
    g3_clear : tls_clear a = true;
    g3_tid   : 0 < bv_unsigned tid < 4194304 }.

  #[using="VI VE"] Theorem s2_e3 : forall a tid c R M K, 4096 <= lim ->
    at_E3 sp draw argv envp uid hw a tid c R M -> tls_clear a = true ->
    (forall R' M' mdl', at_E3g a tid c R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 A_internal_mmap_ret) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 A_internal_mmap_ecall) M ROM) (M_E3 sp brk mbase lim inp a tid)) K.
  Proof.
    intros a tid c R M K Hlim HE Hcl HK. destruct HE as [HR HKN HA HG HT Ht].
    pose proof SL as SL'. pose proof SH as SH'.
    destruct (e3_regs a tid c R HR) as (H17 & H10 & H11 & H12 & H13 & H15).
    assert (ULO : bv_unsigned LO_A = SHB_LO) by (vmeq_refl).
    assert (Htop : bv_unsigned LO_A + page_round_up_Z LO_LEN <= alloc_top (m_vmmaps (M_E3 sp brk mbase lim inp a tid))).
    { rewrite M_E3_vm. unfold alloc_top. cbn [vm_init_sp]. rewrite ULO. change (page_round_up_Z LO_LEN) with (2 ^ 28).
      unfold SHB_LO, stack_max_size, usp in *. lia. }
    eapply (srz_mmap_noreplace_free SEGS R (Z_to_bv 64 A_internal_mmap_ecall) M ROM _ ECALLW 3 FL_NR LO_A LO_LEN
              fetch_internal_mmap_ecall is_ecall_ECALLW (M_E3_halted a tid) H17 (or_intror eq_refl) FL_NR_core
              H10 ltac:(rewrite ULO; reflexivity) ltac:(rewrite ULO; unfold SHB_LO; lia) H11 ltac:(unfold LO_LEN; lia)
              H12 H13 H15 Htop ltac:(intros _; unfold mmap_noreserve_backed_ok; rewrite FL_NR_noreserve; reflexivity) K).
    - (* [comment removed for export] *)
      rewrite M_E3_vm. cbn [vm_reserved vm_maps]. rewrite region_free_app. apply andb_true_intro. split.
      + apply region_free_above_top. rewrite reserved_top_val, ULO. unfold IMG_HI, SHB_LO. lia.
      + reflexivity.
    - (* [comment removed for export] *)
      replace (v_addi (Z_to_bv 64 A_internal_mmap_ecall) 4) with (Z_to_bv 64 A_internal_mmap_ret) by (apply bv_eq; reflexivity).
      fold LO_N. change (noreplace_mem 3 LO_A LO_N M) with (zfill LO_A LO_N M). fold (M_E3g a tid).
      apply HK. constructor.
      + unfold SR8. apply regs_ok_set; [exact HR | intros HH; apply (f_equal bv_unsigned) in HH; discriminate HH |].
        symmetry. apply bv_eq. rewrite ULO. reflexivity.
      + apply (know_shadow_change a tid c M); [apply KN_E3d_ok; assumption|].
        intros x Hx. unfold mrestrict. rewrite (H2_out x Hx). apply zfill_out. rewrite ULO, LO_N_val. unfold SHB_LO, SHB_HI in *. lia.
      + intros x Hx. rewrite zfill_out; [apply HA; exact Hx|]. rewrite ULO, LO_N_val. unfold SHB_LO, usp in *. lia.
      + intros x Hx. apply zfill_in. rewrite ULO, LO_N_val. exact Hx.
      + apply M_E3g_MInv. exact Hlim.
      + apply same_but_materialized_refl.
      + exact HT.
      + exact Hcl.
      + exact Ht.
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Record bootA2 (a tid c : word) (sr : list expr) (kn : list kentry) (Mk : Model) (zr : list (Z * Z))
                 (R : bvmap 5 word) (M : word -> option byte) (mdl : Model) : Prop := BootA2 {
    b2_regs  : regs_ok (E10 sp draw argv envp uid hw a tid c) sr R;
    b2_know  : know_ok SEGS (E10 sp draw argv envp uid hw a tid c) (mrestrict H2 M) kn;
    b2_above : forall x : word, usp <= bv_unsigned x -> M x = wrap_mem PH sp argv envp uid hw draw x;
    b2_zero  : Forall (fun r => forall x : word, fst r <= bv_unsigned x < snd r -> M x = Some (Z_to_bv 8 0)) zr;
    b2_minv  : MInv A2 mdl;
    b2_same  : same_but_materialized Mk mdl;
    b2_tls   : tls_ok sp a;
    b2_clear : tls_clear a = true;
    b2_tid   : 0 < bv_unsigned tid < 4194304 }.

  #[using="Type"] Lemma at_E3g_bootA2 : forall a tid c R M mdl,
    at_E3g a tid c R M mdl -> bootA2 a tid c SR8 KN_E3d (M_E3g a tid) [(SHB_LO, SHB_LO + 2 ^ 28)] R M mdl.
  Proof.
    intros a tid c R M mdl [G1 G2 G3 G4 G5 G6 G7 G8 G9]. constructor; try assumption.
    constructor; [exact G4 | constructor].
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma munrestrict_mrestrict : forall H M, munrestrict H M (mrestrict H M) = M.
  Proof. intros H M. extensionality x. unfold munrestrict, mrestrict. destruct (H x); reflexivity. Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma munrestrict_denot_above : forall a tid c M log x,
    H2 x = false ->
    mem_denot (E10 sp draw argv envp uid hw a tid c) (mrestrict H2 M) log x = mrestrict H2 M x ->
    munrestrict H2 M (mem_denot (E10 sp draw argv envp uid hw a tid c) (mrestrict H2 M) log) x = M x.
  Proof.
    intros a tid c M log x Hh Heq. rewrite (munrestrict_visible _ _ _ _ Hh), Heq. apply mrestrict_visible'. exact Hh.
  Qed.
  (* [comment removed for export] *)
  #[using="Type"] Lemma sbm_noreplace : forall prot flags addr n m m',
    same_but_materialized m m' ->
    same_but_materialized (noreplace_model prot flags addr n m) (noreplace_model prot flags addr n m').
  Proof.
    intros prot flags addr n m m' H. unfold same_but_materialized in *. rewrite H at 1.
    unfold noreplace_model, with_mmap_backing, vm_add_lazy, with_vm_backing, with_vmmaps. destruct m, m'; cbn.
    destruct (mmap_noreserve_b flags); cbn; reflexivity.
  Qed.

  (* [comment removed for export] *)
  #[using="sp usp"] Lemma MInv_A2_transport : forall m m',
    MInv A2 m -> m_vm_materialized m' = m_vm_materialized m ->
    eager_used m' <= vm_limit (m_vmmaps m') -> MInv A2 m'.
  Proof.
    intros m m' [N1 N2 N3 N4 N5] Hm Hb. constructor; rewrite ?Hm.
    - exact N1.
    - exact N2.
    - exact N3.
    - intros p Hp. exfalso. pose proof (N3 p Hp) as X. cbn in X. discriminate.
    - cbn. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition GAP_A : word := Z_to_bv 64 0x8fff7000.
  Definition GAP_LEN : Z := 2 ^ 41.
  Definition GAP_N : word := Z_to_bv 64 (page_round_up_Z GAP_LEN).
  #[using="Type"] Lemma GAP_N_val : bv_unsigned GAP_N = 2 ^ 41. Proof. vmeq_refl. Qed.
  #[using="Type"] Lemma GAP_A_val : bv_unsigned GAP_A = 0x8fff7000. Proof. vmeq_refl. Qed.

  Definition M_E4g (a tid : word) : Model := noreplace_model 0 FL_NR GAP_A GAP_N (M_E3g a tid).

  #[using="Type"] Lemma M_E4g_post : forall a tid, grant_post AP.KNONELAZY GAP_A GAP_N (M_E3g a tid) (M_E4g a tid).
  Proof.
    intros. unfold M_E4g. unfold noreplace_model at 1. unfold with_mmap_backing. rewrite FL_NR_noreserve.
    generalize (M_E3g a tid) as m. intros m. destruct m. constructor; reflexivity.
  Qed.

  #[using="draw VI VE usp"] Lemma M_E4g_wf : forall a tid, model_ivs_wf (M_E4g a tid).
  Proof.
    intros a tid. pose proof (M_E3g_wf a tid) as (W1 & W2 & W3 & W4). pose proof (M_E4g_post a tid) as GP.
    assert (IW : iv_wf (GAP_A, GAP_N)) by (unfold iv_wf, B, S; cbn [fst snd]; rewrite GAP_N_val, GAP_A_val; lia).
    unfold model_ivs_wf.
    rewrite (gp_maps _ _ _ _ _ GP), (gp_noacc _ _ _ _ _ GP), (gp_lazy _ _ _ _ _ GP). cbn [kind_none kind_lazy].
    split; [apply ivs_wf_cons; assumption|]. split; [apply ivs_wf_cons; assumption|]. split; [apply ivs_wf_cons; assumption|].
    unfold init_sp_ok in *. rewrite (gp_isp _ _ _ _ _ GP). exact W4.
  Qed.

  #[using="draw VI VE usp"] Lemma M_E4g_eager : forall a tid, eager_used (M_E4g a tid) = 0.
  Proof.
    intros a tid. pose proof (M_E4g_post a tid) as GP. pose proof (M_E3g_post a tid) as GP3.
    rewrite (eager_used_sem _ (M_E4g_wf a tid)).
    rewrite (gp_maps _ _ _ _ _ GP), (gp_noacc _ _ _ _ _ GP), (gp_lazy _ _ _ _ _ GP).
    rewrite (gp_maps _ _ _ _ _ GP3), (gp_noacc _ _ _ _ _ GP3), (gp_lazy _ _ _ _ _ GP3), M_E3_vm, M_E3_lazy.
    cbn [kind_none kind_lazy vm_maps vm_noaccess app sum_count].
    assert (ULO : bv_unsigned LO_A = SHB_LO) by (vmeq_refl).
    set (P := fun x : Z => negb (covered [(GAP_A, GAP_N); (GAP_A, GAP_N); (LO_A, LO_N)] x)).
    assert (CV : forall x, 0x7fff7000 <= x < 0x8fff7000 + 2 ^ 41 -> P x = false).
    { intros x Hx. unfold P. apply negb_false_iff. unfold covered. cbn [existsb]. unfold in_iv, in_rng, B, S. cbn [fst snd].
      rewrite GAP_A_val, GAP_N_val, ULO, LO_N_val. unfold SHB_LO.
      destruct (Z.lt_ge_cases x 0x8fff7000).
      - rewrite (proj2 (Z.leb_gt 0x8fff7000 x)) by lia. cbn [andb orb].
        rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity.
      - rewrite (proj2 (Z.leb_le 0x8fff7000 x)) by lia. rewrite (proj2 (Z.ltb_lt x _)) by lia. reflexivity. }
    unfold iv_count, B, S. cbn [fst snd]. rewrite GAP_A_val, GAP_N_val, ULO, LO_N_val.
    rewrite (zcount_false P 0x8fff7000) by (intros x Hx; apply CV; rewrite Z2Nat.id in Hx by lia; lia).
    rewrite (zcount_false P SHB_LO) by (intros x Hx; apply CV; rewrite Z2Nat.id in Hx by lia; unfold SHB_LO in Hx; lia).
    lia.
  Qed.
  #[using="draw VI VE usp"] Lemma M_E4g_MInv : forall a tid mdl1, 4096 <= lim ->
    MInv A2 mdl1 -> same_but_materialized (M_E3g a tid) mdl1 ->
    MInv A2 (noreplace_model 0 FL_NR GAP_A GAP_N mdl1).
  Proof.
    intros a tid mdl1 Hlim HM HS.
    pose proof (sbm_noreplace 0 FL_NR GAP_A GAP_N _ _ HS) as HS'. fold (M_E4g a tid) in HS'.
    apply (MInv_A2_transport mdl1); [exact HM | |].
    - unfold noreplace_model, with_mmap_backing. rewrite FL_NR_noreserve. reflexivity.
    - rewrite (sbm_eager _ _ HS'), (sbm_vmmaps _ _ HS'), (M_E4g_eager a tid).
      rewrite (gp_limit _ _ _ _ _ (M_E4g_post a tid)), (gp_limit _ _ _ _ _ (M_E3g_post a tid)), M_E3_vm. cbn. lia.
  Qed.
  #[using="Type"] Lemma sr8e_regs : forall a tid c R, regs_ok (E10 sp draw argv envp uid hw a tid c) SR8e R ->
    getr R 17%bv = Z_to_bv 64 222 /\ getr R 10%bv = GAP_A /\ getr R 11%bv = Z_to_bv 64 GAP_LEN
    /\ getr R 12%bv = Z_to_bv 64 0 /\ getr R 13%bv = FL_NR /\ getr R 15%bv = Z_to_bv 64 0.
  Proof. intros a tid c R HR. repeat split; rewrite (HR _); try reflexivity; apply bv_eq; reflexivity. Qed.

  #[using="VI VE"] Theorem s2_e4 : forall a tid c R M mdl K, 4096 <= lim ->
    bootA2 a tid c SR8 KN_E3d (M_E3g a tid) [(SHB_LO, SHB_LO + 2 ^ 28)] R M mdl ->
    (forall R' M' mdl', bootA2 a tid c SR9 KN_E3d (M_E4g a tid) [(SHB_LO, SHB_LO + 2 ^ 28)] R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 A_internal_mmap_ret) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 A_internal_mmap_ret) M ROM) mdl) K.
  Proof.
    intros a tid c R M mdl K Hlim HB HK. destruct HB as [HR HKN HA HZ HM HS HT Hcl Ht].
    pose proof SL as SL'. pose proof SH as SH'.
    pose proof H2_off as HH. pose proof wx_nowrap as Hwx. pose proof A2_wf as HA2.
    assert (Hh : m_halted mdl = None) by (rewrite (sbm_halted _ _ HS); apply M_E3g_halted).
    assert (HL : lazy_cover H2 (m_vm_lazy mdl) A2) by (apply (sbm_lazy_cover _ _ HS); apply H2_cover_E3g).
    (* [comment removed for export] *)
    run_block_A HR HKN HM HL Hh HH Hwx HA2 FUEL SHADOW_STOPS noscr 10%nat.
    assert (EM0 : M0 = M) by (subst M0; cbn [mem_denot]; apply munrestrict_mrestrict). clearbody M0. subst M0.
    pose proof (same_but_materialized_trans _ _ _ HS HS0) as HS1.
    assert (Hh1 : m_halted mdl0 = None) by (rewrite (sbm_halted _ _ HS1); apply M_E3g_halted).
    (* [comment removed for export] *)
    destruct (sr8e_regs a tid c R0 HR) as (H17 & H10 & H11 & H12 & H13 & H15).
    assert (Htop : bv_unsigned GAP_A + page_round_up_Z GAP_LEN <= alloc_top (m_vmmaps mdl0)).
    { rewrite (sbm_vmmaps _ _ HS1). rewrite (gp_isp _ _ _ _ _ (M_E3g_post a tid)) || idtac.
      unfold alloc_top. rewrite (sbm_vmmaps _ _ HS1) || idtac.
      replace (vm_init_sp (m_vmmaps (M_E3g a tid))) with sp by (symmetry; exact (gp_isp _ _ _ _ _ (M_E3g_post a tid))).
      rewrite GAP_A_val. change (page_round_up_Z GAP_LEN) with (2 ^ 41). unfold stack_max_size, usp in *. lia. }
    eapply (srz_mmap_noreplace_free SEGS R0 (Z_to_bv 64 A_internal_mmap_ecall) M ROM mdl0 ECALLW 0 FL_NR GAP_A GAP_LEN
              fetch_internal_mmap_ecall is_ecall_ECALLW Hh1 H17 (or_introl eq_refl) FL_NR_core
              H10 ltac:(rewrite GAP_A_val; reflexivity) ltac:(rewrite GAP_A_val; lia) H11 ltac:(unfold GAP_LEN; lia)
              H12 H13 H15 Htop ltac:(intros X; discriminate X) K).
    - (* [comment removed for export] *)
      rewrite (sbm_vmmaps _ _ HS1), (gp_res _ _ _ _ _ (M_E3g_post a tid)), (gp_maps _ _ _ _ _ (M_E3g_post a tid)), M_E3_vm.
      cbn [vm_reserved vm_maps]. rewrite region_free_app. apply andb_true_intro. split.
      + apply region_free_above_top. rewrite reserved_top_val, GAP_A_val. unfold IMG_HI. lia.
      + assert (ULO : bv_unsigned LO_A = SHB_LO) by (vmeq_refl).
        cbn [region_free]. unfold iv_overlap. fold GAP_N. rewrite GAP_A_val, GAP_N_val, ULO, LO_N_val.
        unfold SHB_LO. rewrite (proj2 (Z.ltb_ge 0x8fff7000 _)) by lia. cbn [andb negb]. reflexivity.
    - (* [comment removed for export] *)
      replace (v_addi (Z_to_bv 64 A_internal_mmap_ecall) 4) with (Z_to_bv 64 A_internal_mmap_ret) by (apply bv_eq; reflexivity).
      fold GAP_N. change (noreplace_mem 0 GAP_A GAP_N M) with (unfill GAP_A GAP_N M).
      apply HK. constructor.
      + unfold SR9. apply regs_ok_set; [exact HR | intros HH'; apply (f_equal bv_unsigned) in HH'; discriminate HH' |].
        symmetry. apply bv_eq. rewrite GAP_A_val. reflexivity.
      + apply (know_shadow_change a tid c (mrestrict H2 M)); [exact HKN|].
        intros x Hx. unfold mrestrict. rewrite (H2_out x Hx). apply unfill_out. rewrite GAP_A_val, GAP_N_val. unfold SHB_LO, SHB_HI in Hx. lia.
      + intros x Hx. rewrite unfill_out; [apply HA; exact Hx|]. rewrite GAP_A_val, GAP_N_val. unfold usp in *. lia.
      + constructor; [|constructor]. cbn [fst snd]. intros x Hx. rewrite unfill_out.
        * apply Forall_inv in HZ. cbn [fst snd] in HZ. apply HZ. exact Hx.
        * rewrite GAP_A_val, GAP_N_val. unfold SHB_LO in Hx. lia.
      + apply (M_E4g_MInv a tid mdl0); assumption.
      + unfold M_E4g. apply sbm_noreplace. exact HS1.
      + exact HT.
      + exact Hcl.
      + exact Ht.
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition HI_A : word := Z_to_bv 64 0x2008fff7000.
  Definition HI_LEN : Z := 0xdfff0001000.
  Definition HI_N : word := Z_to_bv 64 (page_round_up_Z HI_LEN).
  #[using="Type"] Lemma HI_N_val : bv_unsigned HI_N = 0xdfff0001000. Proof. vmeq_refl. Qed.
  #[using="Type"] Lemma HI_A_val : bv_unsigned HI_A = 0x2008fff7000. Proof. vmeq_refl. Qed.
  #[using="Type"] Lemma HI_end : 0x2008fff7000 + 0xdfff0001000 = SHB_HI. Proof. reflexivity. Qed.

  Definition M_E5g (a tid : word) : Model := noreplace_model 3 FL_NR HI_A HI_N (M_E4g a tid).

  #[using="Type"] Lemma M_E5g_post : forall a tid, grant_post AP.KRWLAZY HI_A HI_N (M_E4g a tid) (M_E5g a tid).
  Proof.
    intros. unfold M_E5g. unfold noreplace_model at 1. unfold with_mmap_backing. rewrite FL_NR_noreserve.
    generalize (M_E4g a tid) as m. intros m. destruct m. constructor; reflexivity.
  Qed.

  #[using="draw VI VE usp"] Lemma M_E5g_wf : forall a tid, model_ivs_wf (M_E5g a tid).
  Proof.
    intros a tid. pose proof (M_E4g_wf a tid) as (W1 & W2 & W3 & W4). pose proof (M_E5g_post a tid) as GP.
    assert (IW : iv_wf (HI_A, HI_N)) by (unfold iv_wf, B, S; cbn [fst snd]; rewrite HI_N_val, HI_A_val; lia).
    unfold model_ivs_wf.
    rewrite (gp_maps _ _ _ _ _ GP), (gp_noacc _ _ _ _ _ GP), (gp_lazy _ _ _ _ _ GP). cbn [kind_none kind_lazy].
    split; [apply ivs_wf_cons; assumption|]. split; [assumption|]. split; [apply ivs_wf_cons; assumption|].
    unfold init_sp_ok in *. rewrite (gp_isp _ _ _ _ _ GP). exact W4.
  Qed.

  #[using="draw VI VE usp"] Lemma M_E5g_eager : forall a tid, eager_used (M_E5g a tid) = 0.
  Proof.
    intros a tid. pose proof (M_E5g_post a tid) as GP. pose proof (M_E4g_post a tid) as GP4. pose proof (M_E3g_post a tid) as GP3.
    rewrite (eager_used_sem _ (M_E5g_wf a tid)).
    rewrite (gp_maps _ _ _ _ _ GP), (gp_noacc _ _ _ _ _ GP), (gp_lazy _ _ _ _ _ GP).
    rewrite (gp_maps _ _ _ _ _ GP4), (gp_noacc _ _ _ _ _ GP4), (gp_lazy _ _ _ _ _ GP4).
    rewrite (gp_maps _ _ _ _ _ GP3), (gp_noacc _ _ _ _ _ GP3), (gp_lazy _ _ _ _ _ GP3), M_E3_vm, M_E3_lazy.
    cbn [kind_none kind_lazy vm_maps vm_noaccess app sum_count].
    assert (ULO : bv_unsigned LO_A = SHB_LO) by (vmeq_refl).
    set (P := fun x : Z => negb (covered [(GAP_A, GAP_N); (HI_A, HI_N); (GAP_A, GAP_N); (LO_A, LO_N)] x)).
    assert (CV : forall x, SHB_LO <= x < SHB_HI -> P x = false).
    { intros x Hx. unfold P. apply negb_false_iff. unfold covered. cbn [existsb]. unfold in_iv, in_rng, B, S. cbn [fst snd].
      rewrite GAP_A_val, GAP_N_val, HI_A_val, HI_N_val, ULO, LO_N_val. unfold SHB_LO, SHB_HI in *.
      destruct (Z.lt_ge_cases x 0x8fff7000); [|destruct (Z.lt_ge_cases x 0x2008fff7000)].
      - rewrite (proj2 (Z.leb_gt 0x8fff7000 x)) by lia. rewrite (proj2 (Z.leb_gt 0x2008fff7000 x)) by lia. cbn [andb orb].
        rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity.
      - rewrite (proj2 (Z.leb_le 0x8fff7000 x)) by lia. rewrite (proj2 (Z.ltb_lt x _)) by lia. reflexivity.
      - rewrite (proj2 (Z.ltb_ge x (0x8fff7000 + _))) by lia. rewrite (proj2 (Z.leb_le 0x2008fff7000 x)) by lia.
        rewrite (proj2 (Z.ltb_lt x (0x2008fff7000 + _))) by lia. cbn [andb orb]. rewrite andb_false_r. reflexivity. }
    unfold iv_count, B, S. cbn [fst snd]. rewrite GAP_A_val, GAP_N_val, HI_A_val, HI_N_val, ULO, LO_N_val.
    rewrite (zcount_false P 0x2008fff7000) by (intros x Hx; apply CV; rewrite Z2Nat.id in Hx by lia; unfold SHB_LO, SHB_HI; lia).
    rewrite (zcount_false P 0x8fff7000) by (intros x Hx; apply CV; rewrite Z2Nat.id in Hx by lia; unfold SHB_LO, SHB_HI; lia).
    rewrite (zcount_false P SHB_LO) by (intros x Hx; apply CV; rewrite Z2Nat.id in Hx by lia; unfold SHB_LO, SHB_HI in *; lia).
    lia.
  Qed.

  #[using="draw VI VE usp"] Lemma M_E5g_MInv : forall a tid mdl1, 4096 <= lim ->
    MInv A2 mdl1 -> same_but_materialized (M_E4g a tid) mdl1 ->
    MInv A2 (noreplace_model 3 FL_NR HI_A HI_N mdl1).
  Proof.
    intros a tid mdl1 Hlim HM HS.
    pose proof (sbm_noreplace 3 FL_NR HI_A HI_N _ _ HS) as HS'. fold (M_E5g a tid) in HS'.
    apply (MInv_A2_transport mdl1); [exact HM | |].
    - unfold noreplace_model, with_mmap_backing. rewrite FL_NR_noreserve. reflexivity.
    - rewrite (sbm_eager _ _ HS'), (sbm_vmmaps _ _ HS'), (M_E5g_eager a tid).
      rewrite (gp_limit _ _ _ _ _ (M_E5g_post a tid)), (gp_limit _ _ _ _ _ (M_E4g_post a tid)), (gp_limit _ _ _ _ _ (M_E3g_post a tid)), M_E3_vm. cbn. lia.
  Qed.

  #[using="Type"] Lemma M_E4g_halted : forall a tid, m_halted (M_E4g a tid) = None.
  Proof. intros. rewrite (gp_halted _ _ _ _ _ (M_E4g_post a tid)). apply M_E3g_halted. Qed.
  #[using="Type"] Lemma M_E4g_lazy : forall a tid, m_vm_lazy (M_E4g a tid) = [(GAP_A, GAP_N); (LO_A, LO_N)].
  Proof. intros. rewrite (gp_lazy _ _ _ _ _ (M_E4g_post a tid)), M_E3g_lazy. reflexivity. Qed.

  #[using="usp"] Lemma H2_cover_E4g : forall a tid, lazy_cover H2 (m_vm_lazy (M_E4g a tid)) A2.
  Proof.
    intros a tid w Hp Hh. exfalso. rewrite M_E4g_lazy in Hp.
    assert (ULO : bv_unsigned LO_A = SHB_LO) by (vmeq_refl).
    assert (PB : bv_unsigned (page_base w) <= bv_unsigned w < bv_unsigned (page_base w) + page_size).
    { unfold page_base, page_base_of, page_size. pose proof (u64_range w) as W.
      pose proof (Z.div_mod (bv_unsigned w) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (bv_unsigned w) 4096 ltac:(lia)).
      rewrite u_small by lia. lia. }
    apply page_in_ranges_true in Hp as (iv & Hin & P1 & P2).
    destruct Hin as [<-|[<-|[]]]; cbn [fst snd] in P1, P2.
    - rewrite GAP_A_val, GAP_N_val in *. rewrite (H2_in w) in Hh; [discriminate|]. unfold page_size, SHB_LO, SHB_HI in *. lia.
    - rewrite ULO, LO_N_val in *. rewrite (H2_in w) in Hh; [discriminate|]. unfold page_size, SHB_LO, SHB_HI in *. lia.
  Qed.

  #[using="Type"] Lemma sr9e_regs : forall a tid c R, regs_ok (E10 sp draw argv envp uid hw a tid c) SR9e R ->
    getr R 17%bv = Z_to_bv 64 222 /\ getr R 10%bv = HI_A /\ getr R 11%bv = Z_to_bv 64 HI_LEN
    /\ getr R 12%bv = Z_to_bv 64 3 /\ getr R 13%bv = FL_NR /\ getr R 15%bv = Z_to_bv 64 0.
  Proof. intros a tid c R HR. repeat split; rewrite (HR _); try reflexivity; apply bv_eq; reflexivity. Qed.

  #[using="VI VE"] Theorem s2_e5 : forall a tid c R M mdl K, 4096 <= lim ->
    bootA2 a tid c SR9 KN_E3d (M_E4g a tid) [(SHB_LO, SHB_LO + 2 ^ 28)] R M mdl ->
    (forall R' M' mdl', bootA2 a tid c SR10 KN_E3d (M_E5g a tid) [(0x2008fff7000, SHB_HI); (SHB_LO, SHB_LO + 2 ^ 28)] R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 A_internal_mmap_ret) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 A_internal_mmap_ret) M ROM) mdl) K.
  Proof.
    intros a tid c R M mdl K Hlim HB HK. destruct HB as [HR HKN HA HZ HM HS HT Hcl Ht].
    pose proof SL as SL'. pose proof SH as SH'.
    pose proof H2_off as HH. pose proof wx_nowrap as Hwx. pose proof A2_wf as HA2.
    assert (Hh : m_halted mdl = None) by (rewrite (sbm_halted _ _ HS); apply M_E4g_halted).
    assert (HL : lazy_cover H2 (m_vm_lazy mdl) A2) by (apply (sbm_lazy_cover _ _ HS); apply H2_cover_E4g).
    (* [comment removed for export] *)
    run_block_A HR HKN HM HL Hh HH Hwx HA2 FUEL SHADOW_STOPS noscr 10%nat.
    assert (EM0 : M0 = M) by (subst M0; cbn [mem_denot]; apply munrestrict_mrestrict). clearbody M0. subst M0.
    pose proof (same_but_materialized_trans _ _ _ HS HS0) as HS1.
    assert (Hh1 : m_halted mdl0 = None) by (rewrite (sbm_halted _ _ HS1); apply M_E4g_halted).
    (* [comment removed for export] *)
    destruct (sr9e_regs a tid c R0 HR) as (H17 & H10 & H11 & H12 & H13 & H15).
    assert (Htop : bv_unsigned HI_A + page_round_up_Z HI_LEN <= alloc_top (m_vmmaps mdl0)).
    { rewrite (sbm_vmmaps _ _ HS1). unfold alloc_top.
      replace (vm_init_sp (m_vmmaps (M_E4g a tid))) with sp
        by (symmetry; rewrite (gp_isp _ _ _ _ _ (M_E4g_post a tid)); exact (gp_isp _ _ _ _ _ (M_E3g_post a tid))).
      rewrite HI_A_val. change (page_round_up_Z HI_LEN) with 0xdfff0001000. unfold stack_max_size, usp in *. lia. }
    eapply (srz_mmap_noreplace_free SEGS R0 (Z_to_bv 64 A_internal_mmap_ecall) M ROM mdl0 ECALLW 3 FL_NR HI_A HI_LEN
              fetch_internal_mmap_ecall is_ecall_ECALLW Hh1 H17 (or_intror eq_refl) FL_NR_core
              H10 ltac:(rewrite HI_A_val; reflexivity) ltac:(rewrite HI_A_val; lia) H11 ltac:(unfold HI_LEN; lia)
              H12 H13 H15 Htop ltac:(intros _; unfold mmap_noreserve_backed_ok; rewrite FL_NR_noreserve; reflexivity) K).
    - (* [comment removed for export] *)
      rewrite (sbm_vmmaps _ _ HS1), (gp_res _ _ _ _ _ (M_E4g_post a tid)), (gp_maps _ _ _ _ _ (M_E4g_post a tid)),
              (gp_res _ _ _ _ _ (M_E3g_post a tid)), (gp_maps _ _ _ _ _ (M_E3g_post a tid)), M_E3_vm.
      cbn [vm_reserved vm_maps]. rewrite region_free_app. apply andb_true_intro. split.
      + apply region_free_above_top. rewrite reserved_top_val, HI_A_val. unfold IMG_HI. lia.
      + assert (ULO : bv_unsigned LO_A = SHB_LO) by (vmeq_refl).
        cbn [region_free]. unfold iv_overlap. fold HI_N.
        rewrite HI_A_val, HI_N_val, GAP_A_val, GAP_N_val, ULO, LO_N_val. unfold SHB_LO.
        rewrite (proj2 (Z.ltb_ge 0x2008fff7000 (0x8fff7000 + _))) by lia.
        rewrite (proj2 (Z.ltb_ge 0x2008fff7000 (0x7fff7000 + _))) by lia. cbn [andb negb]. reflexivity.
    - (* [comment removed for export] *)
      replace (v_addi (Z_to_bv 64 A_internal_mmap_ecall) 4) with (Z_to_bv 64 A_internal_mmap_ret) by (apply bv_eq; reflexivity).
      fold HI_N. change (noreplace_mem 3 HI_A HI_N M) with (zfill HI_A HI_N M).
      apply HK. constructor.
      + unfold SR10. apply regs_ok_set; [exact HR | intros HH'; apply (f_equal bv_unsigned) in HH'; discriminate HH' |].
        symmetry. apply bv_eq. rewrite HI_A_val. reflexivity.
      + apply (know_shadow_change a tid c (mrestrict H2 M)); [exact HKN|].
        intros x Hx. unfold mrestrict. rewrite (H2_out x Hx). apply zfill_out. rewrite HI_A_val, HI_N_val. unfold SHB_LO, SHB_HI in Hx. lia.
      + intros x Hx. rewrite zfill_out; [apply HA; exact Hx|]. rewrite HI_A_val, HI_N_val. unfold usp in *. lia.
      + constructor; [|constructor; [|constructor]]; cbn [fst snd].
        * intros x Hx. apply zfill_in. rewrite HI_A_val, HI_N_val. unfold SHB_HI in Hx. lia.
        * intros x Hx. rewrite zfill_out; [| rewrite HI_A_val, HI_N_val; unfold SHB_LO in Hx; lia].
          apply Forall_inv in HZ. cbn [fst snd] in HZ. apply HZ. exact Hx.
      + apply (M_E5g_MInv a tid mdl0); assumption.
      + unfold M_E5g. apply sbm_noreplace. exact HS1.
      + exact HT.
      + exact Hcl.
      + exact Ht.
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition VALS (a tid c : word) (pl : placements) (js : list word) : list word :=
    vals0 PH sp draw argv envp uid hw ++ [a; tid; c] ++ pl_list pl ++ js.
  Definition EJ (a tid c : word) (pl : placements) (js : list word) : env := Env (vals_ev (VALS a tid c pl js)) (blobs0 draw argv).

  #[using="Type"] Lemma EJ_app : forall a tid c pl js ks, EJ a tid c pl (js ++ ks) = Env (vals_ev (VALS a tid c pl js ++ ks)) (blobs0 draw argv).
  Proof. intros. unfold EJ, VALS. rewrite <- !app_assoc. reflexivity. Qed.
  #[using="Type"] Lemma EJ_nil : forall a tid c pl, EJ a tid c pl [] = Env (vals_ev ((vals0 PH sp draw argv envp uid hw ++ [a; tid; c]) ++ pl_list pl)) (blobs0 draw argv).
  Proof. intros. unfold EJ, VALS. rewrite app_nil_r, <- app_assoc. reflexivity. Qed.
  #[using="Type"] Lemma E10_eq : forall a tid c, E10 sp draw argv envp uid hw a tid c = Env (vals_ev (vals0 PH sp draw argv envp uid hw ++ [a; tid; c])) (blobs0 draw argv).
  Proof. reflexivity. Qed.
  #[using="usp"] Lemma length_E10_vals : forall a tid c, length (vals0 PH sp draw argv envp uid hw ++ [a; tid; c]) = 10%nat.
  Proof. intros. rewrite length_app. cbn. unfold vals0. cbn. lia. Qed.
  #[using="Type"] Lemma ev_EJ_sp : forall a tid c pl js, ev (EJ a tid c pl js) 0%nat = sp. Proof. reflexivity. Qed.
  #[using="Type"] Lemma ev_EJ_tls : forall a tid c pl js, ev (EJ a tid c pl js) V_TLS = a. Proof. reflexivity. Qed.
  #[using="usp"] Lemma length_VALS : forall a tid c pl js, length (VALS a tid c pl js) = (16 + length js)%nat.
  Proof. intros. unfold VALS. rewrite !length_app. cbn. unfold vals0. cbn. lia. Qed.

  Record bootA2j (a tid c : word) (pl : placements) (js : list word) (sr : list expr) (kn : list kentry) (Mk : Model) (zr : list (Z * Z))
                  (R : bvmap 5 word) (M : word -> option byte) (mdl : Model) : Prop := BootA2j {
    j2_regs  : regs_ok (EJ a tid c pl js) sr R;
    j2_know  : know_ok SEGS (EJ a tid c pl js) (mrestrict H2 M) kn;
    j2_above : forall x : word, usp <= bv_unsigned x -> M x = wrap_mem PH sp argv envp uid hw draw x;
    j2_zero  : Forall (fun r => forall x : word, fst r <= bv_unsigned x < snd r -> M x = Some (Z_to_bv 8 0)) zr;
    j2_minv  : MInv A2 mdl;
    j2_same  : same_but_materialized Mk mdl;
    j2_tls   : tls_ok sp a;
    j2_clear : tls_clear a = true;
    j2_tid   : 0 < bv_unsigned tid < 4194304 }.

  #[using="Type"] Lemma bootA2_j : forall a tid c pl sr kn Mk zr R M mdl,
    sr_vars_lt 10 sr = true -> kn_vars_lt 10 kn = true ->
    bootA2 a tid c sr kn Mk zr R M mdl -> bootA2j a tid c pl [] sr kn Mk zr R M mdl.
  Proof.
    intros a tid c pl sr kn Mk zr R M mdl Hsr Hkn [G1 G2 G3 G4 G5 G6 G7 G8 G9]. constructor; rewrite ?EJ_nil; try assumption.
    - apply env_app_regs; [rewrite length_E10_vals; exact Hsr | rewrite <- E10_eq; exact G1].
    - apply env_app_know; [rewrite length_E10_vals; exact Hkn | rewrite <- E10_eq; exact G2].
  Qed.

  (* [comment removed for export] *)
  #[using="brk mbase VI VE"] Lemma frame_block : forall a tid c pl js M log zr,
    log_below_b 0%nat [] log = true ->
    (forall x : word, usp <= bv_unsigned x -> M x = wrap_mem PH sp argv envp uid hw draw x) ->
    Forall (fun r => forall x : word, fst r <= bv_unsigned x < snd r -> M x = Some (Z_to_bv 8 0)) zr ->
    Forall (fun r => forall x : word, fst r <= bv_unsigned x < snd r -> H2 x = true) zr ->
    let M0 := munrestrict H2 M (mem_denot (EJ a tid c pl js) (mrestrict H2 M) log) in
    (forall x : word, usp <= bv_unsigned x -> M0 x = wrap_mem PH sp argv envp uid hw draw x)
    /\ Forall (fun r => forall x : word, fst r <= bv_unsigned x < snd r -> M0 x = Some (Z_to_bv 8 0)) zr.
  Proof.
    intros a tid c pl js M log zr Hlog HA HZ HH M0. pose proof SL. pose proof SH. split.
    - intros x Hx. unfold M0.
      assert (Hv : H2 x = false) by (apply H2_out; right; unfold SHB_HI, usp in *; lia).
      rewrite (munrestrict_visible _ _ _ _ Hv).
      assert (L1 : 2 ^ 41 <= bv_unsigned (ev (EJ a tid c pl js) 0%nat)) by (rewrite ev_EJ_sp; unfold usp in *; lia).
      assert (L2 : bv_unsigned (ev (EJ a tid c pl js) 0%nat) <= usp) by (rewrite ev_EJ_sp; unfold usp in *; lia).
      assert (L3 : usp <= 2 ^ 64 - 2 ^ 41) by (unfold usp in *; lia).
      rewrite (mem_denot_above (EJ a tid c pl js) (mrestrict H2 M) log 0%nat [] usp x Hlog L1 L2 L3 ltac:(constructor) Hx).
      rewrite (mrestrict_visible' _ _ _ Hv). apply HA. exact Hx.
    - apply Forall_forall. intros r Hr x Hx. unfold M0.
      pose proof (proj1 (Forall_forall _ _) HH r Hr x Hx) as Hh.
      rewrite (munrestrict_hidden _ _ _ _ Hh). exact (proj1 (Forall_forall _ _) HZ r Hr x Hx).
  Qed.

  Definition ZR5 : list (Z * Z) := [(0x2008fff7000, SHB_HI); (SHB_LO, SHB_LO + 2 ^ 28)].
  #[using="sp usp"] Lemma ZR5_hidden : Forall (fun r => forall x : word, fst r <= bv_unsigned x < snd r -> H2 x = true) ZR5.
  Proof.
    unfold ZR5. constructor; [|constructor; [|constructor]]; cbn [fst snd]; intros x Hx; apply H2_in; unfold SHB_LO, SHB_HI in *; lia.
  Qed.

  #[using="Type"] Lemma M_E5g_halted : forall a tid, m_halted (M_E5g a tid) = None.
  Proof. intros. rewrite (gp_halted _ _ _ _ _ (M_E5g_post a tid)). apply M_E4g_halted. Qed.
  #[using="Type"] Lemma M_E5g_lazy : forall a tid, m_vm_lazy (M_E5g a tid) = [(HI_A, HI_N); (GAP_A, GAP_N); (LO_A, LO_N)].
  Proof. intros. rewrite (gp_lazy _ _ _ _ _ (M_E5g_post a tid)), M_E4g_lazy. reflexivity. Qed.
  #[using="usp"] Lemma H2_cover_E5g : forall a tid, lazy_cover H2 (m_vm_lazy (M_E5g a tid)) A2.
  Proof.
    intros a tid w Hp Hh. exfalso. rewrite M_E5g_lazy in Hp.
    assert (ULO : bv_unsigned LO_A = SHB_LO) by (vmeq_refl).
    assert (PB : bv_unsigned (page_base w) <= bv_unsigned w < bv_unsigned (page_base w) + page_size).
    { unfold page_base, page_base_of, page_size. pose proof (u64_range w) as W.
      pose proof (Z.div_mod (bv_unsigned w) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (bv_unsigned w) 4096 ltac:(lia)).
      rewrite u_small by lia. lia. }
    apply page_in_ranges_true in Hp as (iv & Hin & P1 & P2).
    destruct Hin as [<-|[<-|[<-|[]]]]; cbn [fst snd] in P1, P2.
    - rewrite HI_A_val, HI_N_val in *. rewrite (H2_in w) in Hh; [discriminate|]. unfold page_size, SHB_LO, SHB_HI in *. lia.
    - rewrite GAP_A_val, GAP_N_val in *. rewrite (H2_in w) in Hh; [discriminate|]. unfold page_size, SHB_LO, SHB_HI in *. lia.
    - rewrite ULO, LO_N_val in *. rewrite (H2_in w) in Hh; [discriminate|]. unfold page_size, SHB_LO, SHB_HI in *. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="VI VE"] Theorem s2_b10 : forall a tid c pl R M mdl K,
    bootA2j a tid c pl [] SR10 KN_E3d (M_E5g a tid) ZR5 R M mdl ->
    (forall R' M' mdl', bootA2j a tid c pl [] SR10e KN10e (M_E5g a tid) ZR5 R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 A_istrncpy) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 A_internal_mmap_ret) M ROM) mdl) K.
  Proof.
    intros a tid c pl R M mdl K HB HK. destruct HB as [HR HKN HA HZ HM HS HT Hcl Ht].
    pose proof H2_off as HH. pose proof wx_nowrap as Hwx. pose proof A2_wf as HA2.
    assert (Hh : m_halted mdl = None) by (rewrite (sbm_halted _ _ HS); apply M_E5g_halted).
    assert (HL : lazy_cover H2 (m_vm_lazy mdl) A2) by (apply (sbm_lazy_cover _ _ HS); apply H2_cover_E5g).
    run_block_A HR HKN HM HL Hh HH Hwx HA2 FUEL SHADOW_STOPS noscr 16%nat.
    lazymatch goal with |- srealizes _ (mkCfg (mkst _ _ ?m _) _) _ =>
      let body := eval unfold m in m in
      lazymatch body with munrestrict H2 M (mem_denot _ _ ?lg) =>
        destruct (frame_block a tid c pl [] M lg ZR5 ltac:(vmeq_refl) HA HZ ZR5_hidden) as [HA0 HZ0];
        subst m
      end end.
    apply HK. constructor; try assumption.
    eapply same_but_materialized_trans; [exact HS | exact HS0].
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  #[using="Type"] Lemma sealed_bytes_word : firstn 8 strncpy_sealed_bytes = word_to_le_bytes 8 (Z_to_bv 64 SEALED_U64).
  Proof. vm_refl_bv. Qed.
  #[using="sp usp"] Lemma nth_repeat_any : forall {A} (d d' : A) n j, (j < n)%nat -> nth j (repeat d n) d' = d.
  Proof. intros A d d' n. induction n as [|n IH]; intros j Hj; [lia|]. destruct j; [reflexivity|]. cbn. apply IH. lia. Qed.
  #[using="sp usp"] Lemma sealed_bytes_zero : forall j, (8 <= j < 4095)%nat -> nth j strncpy_sealed_bytes (Z_to_bv 8 0) = Z_to_bv 8 0.
  Proof.
    intros j Hj. unfold strncpy_sealed_bytes. rewrite app_nth2 by (cbn; lia). cbn [length sealed8].
    unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.ArgvEnv__Common.ZStores.zeros. apply nth_repeat_any. lia.
  Qed.

  #[using="Type"] Lemma kn_vars_lt_kimg_cut : forall b lo hi kn, kn_vars_lt b kn = true -> kn_vars_lt b (kimg_cut lo hi kn) = true.
  Proof.
    intros b lo hi kn. induction kn as [|K t IH]; cbn [kimg_cut flat_map kn_vars_lt]; intros H; [reflexivity|].
    apply andb_prop in H as [HK Ht]. fold (kimg_cut lo hi t).
    assert (APP : forall l, forallb (kentry_vars_lt b) l = true -> kn_vars_lt b (l ++ kimg_cut lo hi t) = true).
    { intros l Hl. induction l as [|x l' IHl]; cbn [app kn_vars_lt]; [apply IH; exact Ht|].
      cbn [forallb] in Hl. apply andb_prop in Hl as [Hx Hl']. rewrite Hx, (IHl Hl'). reflexivity. }
    apply APP. destruct K; cbn [kimg_cut1]; try (cbn [forallb]; rewrite HK; reflexivity).
    destruct ((hi <=? lo0) || (hi0 <=? lo))%Z; [cbn [forallb]; rewrite HK; reflexivity|].
    destruct (lo0 <? lo)%Z, (hi <? hi0)%Z; reflexivity.
  Qed.

  #[using="brk mbase VI VE"] Theorem cross_istrncpy : forall a tid c pl js sr kn Mk zr (dst ret : Z) iK ilo ihi iW kk len R M mdl K,
    let n := length (VALS a tid c pl js) in
    bootA2j a tid c pl js sr kn Mk zr R M mdl ->
    m_halted Mk = None -> lazy_cover H2 (m_vm_lazy Mk) A2 ->
    sr_vars_lt n sr = true -> kn_vars_lt n kn = true ->
    sr_get sr 1%bv = ELit ret -> sr_get sr 10%bv = ELit dst -> sr_get sr 11%bv = ELit a3_sealed_src -> sr_get sr 12%bv = ELit 4095 ->
    (0 <= ret < 2 ^ 64) -> ret mod 2 = 0 ->
    nth_error kn iK = Some (KImg ilo ihi) -> ilo <= a3_sealed_src -> a3_sealed_src + 9 <= ihi ->
    nth_error kn iW = Some (KWr (SA (ELit 0) kk) (ELit len)) -> 0 <= len < 2 ^ 64 -> kk <= dst -> dst + 4095 <= kk + len ->
    a3_sealed_src + 9 <= dst -> dst + 4095 <= SHB_LO ->
    Forall (fun r => forall x : word, fst r <= bv_unsigned x < snd r -> H2 x = true) zr ->
    List.filter (EntryGlue.keep_b (kimg_cut dst (dst + 4095) kn) (ELit 0) dst (ELit 4095)) (kimg_cut dst (dst + 4095) kn)
      = kimg_cut dst (dst + 4095) kn ->
    (forall R' M' mdl',
       bootA2j a tid c pl (js ++ junk_c R' istrncpy_clob) (sr_after_call_c sr istrncpy_clob n) (sealed_kn dst kn) Mk zr R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 ret) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 A_istrncpy) M ROM) mdl) K.
  Proof.
    intros a tid c pl js sr kn Mk zr dst ret iK ilo ihi iW kk len R M mdl K n HB HhK HLK Hsr Hkn S1 S10 S11 S12 Hret Hret1
           HiK Hlo Hhi HiW Hlen Hkk Hdl Hsd Hds Hzr Hfilt HK.
    destruct HB as [HR HKN HA HZ HM HS HT Hcl Ht].
    pose proof SL as SL'. pose proof SH as SH'.
    set (E := EJ a tid c pl js) in *. set (V := mrestrict H2 M) in *.
    assert (Hsrc : 0 <= a3_sealed_src) by (unfold a3_sealed_src; lia).
    (* [comment removed for export] *)
    assert (Himg : forall i, a3_sealed_src <= i < a3_sealed_src + 9 -> V (Z_to_bv 64 i) = None).
    { pose proof (know_nth SEGS E V kn iK _ HKN HiK) as (_ & _ & Hn). intros i Hi. apply Hn. lia. }
    assert (Hst : store_ok SEGS V (Z_to_bv 64 dst) 4095%nat = true).
    { eapply (kwr_store_ok_lit SEGS E V kn iW); [exact HKN | exact HiW | lia | lia | cbn [Z.of_nat]; lia | unfold SHB_LO in Hds; lia]. }
    assert (G1 : getr R 1%bv = Z_to_bv 64 ret) by (rewrite (HR 1%bv), S1; reflexivity).
    assert (G10 : getr R 10%bv = Z_to_bv 64 dst) by (rewrite (HR 10%bv), S10; reflexivity).
    assert (G11 : getr R 11%bv = Z_to_bv 64 a3_sealed_src) by (rewrite (HR 11%bv), S11; reflexivity).
    assert (G12 : getr R 12%bv = Z_to_bv 64 4095) by (rewrite (HR 12%bv), S12; reflexivity).
    assert (Hrok : ret_ok (Z_to_bv 64 ret)) by (apply ret_ok_even; rewrite u_small by lia; exact Hret1).
    destruct (a3_istrncpy_sealed V (Z_to_bv 64 dst) ROM R (Z_to_bv 64 ret) Himg
                ltac:(exact Hst) ltac:(rewrite u_small; unfold SHB_LO in Hds; lia)
                ltac:(right; rewrite u_small; unfold SHB_LO in Hds; lia) Hrok G1 G10 G11 G12) as (R' & MS & AG).
    assert (Hh : m_halted mdl = None) by (rewrite (sbm_halted _ _ HS); exact HhK).
    assert (HL : lazy_cover H2 (m_vm_lazy mdl) A2) by (apply (sbm_lazy_cover _ _ HS); exact HLK).
    eapply (srz_msteps_A' SEGS H2 H2_off wx_nowrap A2 R (Z_to_bv 64 A_istrncpy) M ROM R' (Z_to_bv 64 ret) _ mdl K);
      [subst V; exact MS | exact HL | exact A2_wf | exact HM | exact Hh |].
    intros mdl' HM' HS' EQV.
    set (V' := wbytes V (Z_to_bv 64 dst) strncpy_sealed_bytes) in *.
    assert (LENB : length strncpy_sealed_bytes = 4095%nat) by apply length_strncpy_sealed_bytes.
    assert (Udst : bv_unsigned (Z_to_bv 64 dst) = dst) by (apply u_small; unfold SHB_LO in Hds; lia).
    assert (V'out : forall x : word, bv_unsigned x < dst \/ dst + 4095 <= bv_unsigned x -> V' x = V x).
    { intros x Hx. unfold V'. apply wbytes_outside; rewrite LENB, Udst; [unfold SHB_LO in Hds; lia | lia]. }
    assert (CLEAN : forall x : word, H2 x = true -> V' x = None).
    { intros x Hx. rewrite V'out.
      - unfold V, mrestrict. rewrite Hx. reflexivity.
      - unfold H2 in Hx. apply andb_prop in Hx as [Hx _]. apply Z.leb_le in Hx. lia. }
    apply HK. constructor.
    - (* [comment removed for export] *)
      unfold n, E, EJ. apply (regs_after_clob istrncpy_clob (VALS a tid c pl js) (blobs0 draw argv) sr R R' Hsr HR).
      + intros r Hr. apply AG. exact Hr.
      + cbn. intros [H|[H|[H|[H|[H|[]]]]]]; apply (f_equal bv_unsigned) in H; discriminate H.
      + repeat constructor; cbn; intros HH; repeat (destruct HH as [HH|HH]; [apply (f_equal bv_unsigned) in HH; discriminate HH|]); exact HH.
    - (* [comment removed for export] *)
      rewrite EQV.
      rewrite EJ_app. apply env_app_know.
      { unfold sealed_kn. cbn [app kn_vars_lt kentry_vars_lt saddr_vars_lt a_base expr_vars_lt andb]. apply kn_vars_lt_kimg_cut. exact Hkn. }
      fold E. unfold sealed_kn. apply (proj2 (know_ok_app SEGS E V' _ _)). split.
      + constructor; [|constructor; [|constructor]].
        * cbn [kentry_ok]. split; [lia|]. split.
          { unfold flat, estart. cbn [a_base a_off edenot]. rewrite u_small by lia. unfold SHB_LO in Hds. lia. }
          rewrite adenot_lit0. cbn [edenot]. rewrite <- sealed_bytes_word.
          pose proof (rdn_wbytes_hit SEGS strncpy_sealed_bytes V (Z_to_bv 64 dst) ltac:(rewrite LENB, Udst; unfold SHB_LO in Hds; lia)) as RD.
          fold V' in RD. rewrite LENB in RD.
          pose proof (rdn_sub SEGS V' 4095 (Z_to_bv 64 dst) strncpy_sealed_bytes 0 8 RD ltac:(lia)) as RD8.
          rewrite at_0 in RD8. unfold sub in RD8. cbn [skipn Z.of_nat] in RD8. exact RD8.
        * cbn [kentry_ok]. split.
          { unfold flat, estart, elenZ. cbn [a_base a_off edenot]. rewrite !u_small by lia. unfold SHB_LO in Hds. lia. }
          intros i Hi. unfold estart, elenZ in *. cbn [a_base a_off edenot] in *. rewrite !u_small in Hi |- * by lia.
          change (bv_unsigned (Z_to_bv 64 0)) with 0. rewrite Z.add_0_l.
          unfold V'. replace (Z_to_bv 64 (dst + 8 + i)) with (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 dst) + Z.of_nat (Z.to_nat (8 + i)))) by (f_equal; rewrite Udst; lia).
          rewrite wbytes_nth by (rewrite ?LENB, ?Udst; unfold SHB_LO in Hds; lia). f_equal. apply sealed_bytes_zero. lia.
      + rewrite <- Hfilt. apply (know_change_keep SEGS E V V').
        * apply know_kimg_cut. exact HKN.
        * intros x Hx. apply V'out. unfold estart, elenZ in Hx. cbn [a_base a_off edenot] in Hx. rewrite !u_small in Hx by lia. lia.
        * unfold V'. apply wbytes_grows.
    - (* [comment removed for export] *)
      intros x Hx. assert (Hv : H2 x = false) by (apply H2_out; right; unfold SHB_HI, usp in *; lia).
      rewrite (munrestrict_visible _ _ _ _ Hv), V'out by (unfold SHB_LO, usp in *; lia). unfold V. rewrite (mrestrict_visible' _ _ _ Hv). apply HA. exact Hx.
    - (* [comment removed for export] *)
      apply Forall_forall. intros r Hr x Hx. pose proof (proj1 (Forall_forall _ _) Hzr r Hr x Hx) as Hh2.
      rewrite (munrestrict_hidden _ _ _ _ Hh2). exact (proj1 (Forall_forall _ _) HZ r Hr x Hx).
    - exact HM'.
    - eapply same_but_materialized_trans; [exact HS | exact HS'].
    - exact HT.
    - exact Hcl.
    - exact Ht.
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="Type"] Lemma cbn1_filter :
    List.filter (EntryGlue.keep_b (kimg_cut A_binary_name_cache (A_binary_name_cache + 4095) KN10e) (ELit 0) A_binary_name_cache (ELit 4095))
                (kimg_cut A_binary_name_cache (A_binary_name_cache + 4095) KN10e)
    = kimg_cut A_binary_name_cache (A_binary_name_cache + 4095) KN10e.
  Proof. vmeq_refl. Qed.
  #[using="Type"] Lemma cbn2_filter :
    List.filter (EntryGlue.keep_b (kimg_cut A_process_name_cache (A_process_name_cache + 4095) KN11e) (ELit 0) A_process_name_cache (ELit 4095))
                (kimg_cut A_process_name_cache (A_process_name_cache + 4095) KN11e)
    = kimg_cut A_process_name_cache (A_process_name_cache + 4095) KN11e.
  Proof. vmeq_refl. Qed.
  #[using="Type"] Lemma SR11_eq : sr_after_call_c SR10e istrncpy_clob 16 = SR11. Proof. vmeq_refl. Qed.
  #[using="Type"] Lemma SR12_eq : sr_after_call_c SR11e istrncpy_clob 21 = SR12. Proof. vmeq_refl. Qed.

  Ltac kidx_img kn src :=
    kidx kn (fun K => match K with KImg lo hi => ((lo <=? src) && (src + 9 <=? hi))%Z | _ => false end).
  Ltac kidx_kwr kn dst :=
    kidx kn (fun K => match K with KWr (SA (ELit 0) kk) (ELit len) => ((kk <=? dst) && (dst + 4095 <=? kk + len))%Z | _ => false end).

  #[using="VI VE"] Theorem s2_cbn1 : forall a tid c pl R M mdl K,
    bootA2j a tid c pl [] SR10e KN10e (M_E5g a tid) ZR5 R M mdl ->
    (forall R' M' mdl', bootA2j a tid c pl (junk_c R' istrncpy_clob) SR11 KN11 (M_E5g a tid) ZR5 R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 A_cbn_mid) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 A_istrncpy) M ROM) mdl) K.
  Proof.
    intros a tid c pl R M mdl K HB HK.
    let iK := kidx_img KN10e a3_sealed_src in let iW := kidx_kwr KN10e A_binary_name_cache in
    eapply (cross_istrncpy a tid c pl [] SR10e KN10e (M_E5g a tid) ZR5 A_binary_name_cache A_cbn_mid iK _ _ iW _ _ R M mdl K HB
              (M_E5g_halted a tid) (H2_cover_E5g a tid)); try reflexivity.
    all: try exact ZR5_hidden. all: try exact cbn1_filter.
    all: try (unfold A_cbn_mid, A_binary_name_cache, a3_sealed_src, SHB_LO, A_rw_lo, A_rw_len; lia).
    intros R' M' mdl' HB'. apply HK. rewrite <- SR11_eq. exact HB'.
  Qed.
  (* [comment removed for export] *)
  Ltac s2_block HB HK STOPS NX :=
    let HR := fresh "HR" in let HKN := fresh "HKN" in let HA := fresh "HA" in let HZ := fresh "HZ" in
    let HM := fresh "HM" in let HS := fresh "HS" in let HT := fresh "HT" in let Hcl := fresh "Hcl" in let Ht := fresh "Ht" in
    destruct HB as [HR HKN HA HZ HM HS HT Hcl Ht];
    let HH := fresh "HH" in let Hwx := fresh "Hwx" in let HA2 := fresh "HA2" in let Hh := fresh "Hh" in let HL := fresh "HL" in
    pose proof H2_off as HH; pose proof wx_nowrap as Hwx; pose proof A2_wf as HA2;
    assert (Hh : m_halted _ = None) by (rewrite (sbm_halted _ _ HS); apply M_E5g_halted);
    assert (HL : lazy_cover H2 (m_vm_lazy _) A2) by (apply (sbm_lazy_cover _ _ HS); apply H2_cover_E5g);
    run_block_A HR HKN HM HL Hh HH Hwx HA2 FUEL STOPS noscr NX;
    lazymatch goal with |- srealizes _ (mkCfg (mkst _ _ ?m _) _) _ =>
      let body := eval unfold m in m in
      lazymatch body with munrestrict H2 ?M (mem_denot (EJ ?a ?tid ?c ?pl ?js) _ ?lg) =>
        destruct (frame_block a tid c pl js M lg ZR5 ltac:(vmeq_refl) HA HZ ZR5_hidden) as [HA0 HZ0];
        subst m
      end end;
    apply HK; constructor; try assumption; eapply same_but_materialized_trans; [exact HS | eassumption].

  #[using="VI VE"] Theorem s2_b11 : forall a tid c pl js R M mdl K,
    bootA2j a tid c pl js SR11 KN11 (M_E5g a tid) ZR5 R M mdl ->
    (forall R' M' mdl', bootA2j a tid c pl js SR11e KN11e (M_E5g a tid) ZR5 R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 A_istrncpy) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 A_cbn_mid) M ROM) mdl) K.
  Proof. intros a tid c pl js R M mdl K HB HK. s2_block HB HK SHADOW_STOPS 21%nat. Qed.

  #[using="VI VE"] Theorem s2_cbn2 : forall a tid c pl (js : list word) R M mdl K, length js = 5%nat ->
    bootA2j a tid c pl js SR11e KN11e (M_E5g a tid) ZR5 R M mdl ->
    (forall R' M' mdl', bootA2j a tid c pl (js ++ junk_c R' istrncpy_clob) SR12 KN12 (M_E5g a tid) ZR5 R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 A_init_after_cbn) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 A_istrncpy) M ROM) mdl) K.
  Proof.
    intros a tid c pl js R M mdl K Hjs HB HK.
    assert (LEN : length (VALS a tid c pl js) = 21%nat) by (rewrite length_VALS, Hjs; reflexivity).
    let iK := kidx_img KN11e a3_sealed_src in let iW := kidx_kwr KN11e A_process_name_cache in
    eapply (cross_istrncpy a tid c pl js SR11e KN11e (M_E5g a tid) ZR5 A_process_name_cache A_init_after_cbn iK _ _ iW _ _ R M mdl K HB
              (M_E5g_halted a tid) (H2_cover_E5g a tid)); rewrite ?LEN; try reflexivity.
    all: try exact ZR5_hidden. all: try exact cbn2_filter.
    all: try (unfold A_init_after_cbn, A_process_name_cache, a3_sealed_src, SHB_LO, A_rw_lo, A_rw_len; lia).
    intros R' M' mdl' HB'. apply HK. rewrite <- SR12_eq. exact HB'.
  Qed.

  (* [comment removed for export] *)
  Definition at_E6 (a tid c : word) (pl : placements) (js : list word) := bootA2j a tid c pl js SR_E6 KN_E6 (M_E5g a tid) ZR5.

  #[using="VI VE"] Theorem s2_b12 : forall a tid c pl js R M mdl K,
    bootA2j a tid c pl js SR12 KN12 (M_E5g a tid) ZR5 R M mdl ->
    (forall R' M' mdl', at_E6 a tid c pl js R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 A_internal_mmap_ecall) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 A_init_after_cbn) M ROM) mdl) K.
  Proof. intros a tid c pl js R M mdl K HB HK. unfold at_E6 in HK. s2_block HB HK SHADOW_STOPS 26%nat. Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="VI VE"] Theorem boot_s2 : forall a tid c pl R M K, 4096 <= lim ->
    at_E3 sp draw argv envp uid hw a tid c R M -> tls_clear a = true ->
    (forall js R' M' mdl', length js = 10%nat -> at_E6 a tid c pl js R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 A_internal_mmap_ecall) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 A_internal_mmap_ecall) M ROM) (M_E3 sp brk mbase lim inp a tid)) K.
  Proof.
    intros a tid c pl R M K Hlim HE Hcl HK.
    apply (s2_e3 a tid c R M K Hlim HE Hcl). intros R1 M1 m1 H1.
    apply (s2_e4 a tid c R1 M1 m1 K Hlim (at_E3g_bootA2 _ _ _ _ _ _ H1)). intros R2 M2 m2 H2'.
    apply (s2_e5 a tid c R2 M2 m2 K Hlim H2'). intros R3 M3 m3 H3.
    assert (V1 : sr_vars_lt 10 SR10 = true) by (vmeq_refl).
    assert (V2 : kn_vars_lt 10 KN_E3d = true) by (vmeq_refl).
    apply (s2_b10 a tid c pl R3 M3 m3 K (bootA2_j a tid c pl SR10 KN_E3d _ _ _ _ _ V1 V2 H3)). intros R4 M4 m4 H4.
    apply (s2_cbn1 a tid c pl R4 M4 m4 K H4). intros R5 M5 m5 H5.
    apply (s2_b11 a tid c pl _ R5 M5 m5 K H5). intros R6 M6 m6 H6.
    eapply (s2_cbn2 a tid c pl _ R6 M6 m6 K); [| exact H6 |]; [unfold junk_c; rewrite length_map; reflexivity|]. intros R7 M7 m7 H7.
    apply (s2_b12 a tid c pl _ R7 M7 m7 K H7). intros R8 M8 m8 H8.
    eapply (HK _ R8 M8 m8); [|exact H8]. rewrite length_app. unfold junk_c. rewrite !length_map. reflexivity.
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="VI VE"] Theorem boot_s12 : forall pl K, 4096 <= lim ->
    (forall a tid c js R M mdl, length js = 10%nat -> at_E6 a tid c pl js R M mdl ->
       srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 A_internal_mmap_ecall) M ROM) mdl) K) ->
    srealizes SEGS (init_config SEGS PC0 PH sp brk mbase draw lim inp) K.
  Proof.
    intros pl K Hlim HK. apply (boot_s1 sp brk mbase draw lim inp VI VE K Hlim).
    intros a tid c R M HE Hcl. apply (boot_s2 a tid c pl R M K Hlim HE Hcl).
    intros js R' M' mdl' Hjs H6. exact (HK a tid c js R' M' mdl' Hjs H6).
  Qed.
End Theorems.
