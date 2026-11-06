(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Lia.
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require PropExec MState Mem Exec ITree Nodes Decode SysStep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Exit__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require ExecF ITreeA Shadow RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg ABase AProto.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Tac Arr Bytes ZBridge Frame StoreFast.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require StepF SysStepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require GIA PcapRepA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require SfKitA__A3P.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require SfHandleA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require NDestr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require AsanHeap__SpecA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AMalloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require FmtFacts__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require UnwKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FrameKit__A3P.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FmtKitA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngchk_modelA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngchk_defsA__A3P.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require LibcKit2__A3P.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require LiaRel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P Require UbGuardB.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Image.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require LibcKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_iface_ngA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P Require UbGuardNgB__B3P.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require RegsEquiv.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require StrwF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_iface_ppA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require LiaPin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module LeafA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Exec ITree Nodes Decode SysStep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Exit__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Exit__S3.MLeaf.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg ABase AProto.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Import MonadG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Section LeafF.
  Variable node : Type.
  Variable segs : list Segment.
  Variable at_node : node -> footprint -> machine_state -> Prop.
  Variable sil : footprint -> machine_state -> machine_state -> Prop.
  Variable npeek : node -> option (machine_state -> resp).
  Variable fstep : node -> resp -> footprint -> footprint -> Prop.

  #[using="Type"] Lemma implF_has_leaf : forall {R} (t : itree node R) RNG Q ms,
    @implF node segs at_node sil npeek fstep R RNG t Q ms ->
    @implF node segs at_node sil npeek fstep R RNG t (fun r RNG' ms' => Q r RNG' ms' /\ has_leaf t r) ms.
  Proof.
    induction t as [r|n k IH]; intros RNG Q ms HI; cbn in *.
    - eapply evtS_mono; [exact HI|]. intros ms' HQ. split; [exact HQ| reflexivity].
    - eapply evtS_mono; [exact HI|]. intros ms1 [[Hat Hk]|(f & Hf & Hk)].
      + left. split; [exact Hat|]. intros rsp RNG' HF. eapply implF_mono; [apply IH; apply Hk; exact HF|].
        intros r RNG2 ms' [H1 H2]. split; [exact H1|]. exists rsp. exact H2.
      + right. exists f. split; [exact Hf|]. intros RNG' HF. eapply implF_mono; [apply IH; apply Hk; exact HF|].
        intros r RNG2 ms' [H1 H2]. split; [exact H1|]. exists (f ms1). exact H2.
  Qed.
End LeafF.

Section CANSEC1. Context {rc : runConstT}.
Section LeafG.
  Context {St : Type}.
  #[using="Type"] Lemma implMG_leaf : forall {A} RNG (c : Monad.M St A) s Q ms,
    implMG RNG c s Q ms -> implMG RNG c s (fun a s' RNG' ms' => Q a s' RNG' ms' /\ mleaf c s a s') ms.
  Proof.
    intros A RNG c s Q ms HI. unfold implMG in *. eapply implF_mono; [eapply implF_has_leaf; exact HI|].
    intros [|[a s']] RNG' ms'; cbn; [tauto|]. intros [H1 H2]. split; [exact H1| exact H2].
  Qed.
End LeafG.
End CANSEC1.

(* [comment removed for export] *)
Section FoLeaf.
  Context {H hptr : Type}.
  #[local] Notation PS := (PState H hptr).
  Record fo_leaf_laws (FO : @FrameOps H hptr) : Prop := mkFOL {
    fol_enter : forall (A : Type) f (body : Monad.M PS A) s a s', mleaf (fo_enter FO A f body) s a s' -> exists s1, mleaf body s1 a s';
    fol_ret : forall (A : Type) f (x : A) s a s', mleaf (fo_ret FO A f x) s a s' -> a = x
  }.
End FoLeaf.

(* [comment removed for export] *)
Ltac crawl_withA FOL tac L :=
  repeat (first
   [ lazymatch type of L with
     | mleaf (e_fenter _ _ _) _ _ _ => cbn [e_fenter prims] in L
     | mleaf (e_fret _ _ _) _ _ _ => cbn [e_fret prims] in L
     | mleaf (fo_enter _ _ _ _) _ _ _ => let s1 := fresh "ls" in apply (fol_enter _ FOL) in L as (s1 & L)
     | mleaf (fo_ret _ _ _ _) _ _ _ => apply (fol_ret _ FOL) in L; try (lazymatch type of L with ?x = _ => subst x end)
     | mleaf (mbind _ _) _ _ _ => let a := fresh "lv" in let s := fresh "ls" in let H1 := fresh "HL" in
         apply mleaf_bind in L as (a & s & H1 & L); crawl_withA FOL tac H1; try (lazymatch type of H1 with mleaf _ _ _ _ => clear H1 end)
     | mleaf (mo_bind MOps _ _) _ _ _ => let a := fresh "lv" in let s := fresh "ls" in let H1 := fresh "HL" in
         apply mleaf_mobind in L as (a & s & H1 & L); crawl_withA FOL tac H1; try (lazymatch type of H1 with mleaf _ _ _ _ => clear H1 end)
     | mleaf (mret _) _ _ _ => let E1 := fresh "E" in let E2 := fresh "E" in apply mleaf_ret in L as [E1 E2];
         try (lazymatch type of E2 with ?x = _ => subst x end); try (lazymatch type of E1 with ?x = _ => subst x end)
     | mleaf (mo_ret MOps _) _ _ _ => let E1 := fresh "E" in let E2 := fresh "E" in apply mleaf_moret in L as [E1 E2];
         try (lazymatch type of E2 with ?x = _ => subst x end); try (lazymatch type of E1 with ?x = _ => subst x end)
     | mleaf munr _ _ _ => destruct (mleaf_unr _ _ _ L)
     | mleaf (mo_unr MOps) _ _ _ => destruct (mleaf_mounr _ _ _ L)
     | mleaf ((fun _ => _) _) _ _ _ => cbv beta in L
     | mleaf (if ?b then _ else _) _ _ _ => destruct b
     | mleaf (match ?x with _ => _ end) _ _ _ => destruct x
     | mleaf (let _ := _ in _) _ _ _ => cbv zeta in L
     | mleaf _ _ _ _ => tac L
     end ]).

Section CANSEC2. Context {rc : runConstT}.
Section Rfile.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (stk : stack_site -> Z).
  Hypothesis FOL : fo_leaf_laws FO.
  #[local] Notation PS := (PState H hptr).
  #[local] Notation pcapT := (PcapTypes.pcap hptr hptr).
  #[local] Notation P := (prims HO FO stk).

  Ltac rf_simp := cbn [fst snd pc_rfile set_errbuf set_bufdata set_buffer set_header set_priv set_ng set_break_loop] in *.
  Ltac rf_fin := inj_all; rf_simp;
    repeat (match goal with
            | |- context [pc_rfile (if ?c then _ else _)] => destruct c; rf_simp
            | H : context [pc_rfile (if ?c then _ else _)] |- _ => destruct c; rf_simp
            end); congruence.

  #[using="rc"] Lemma grow_buffer_rfile : forall (p : pcapT) n s r s', mleaf (grow_buffer MOps P p n) s r s' -> pc_rfile (snd r) = pc_rfile p.
  Proof. intros p n s r s' L. unfold grow_buffer in L. crawl_withA FOL notac L. all: rf_fin. Qed.

  #[using="rc FOL"] Lemma read_block_rfile : forall d (p : pcapT) s r s', mleaf (read_block MOps P d p) s r s' ->
    match r with RB_Eof p' | RB_Err _ p' | RB_Ok _ p' => pc_rfile p' = pc_rfile p end.
  Proof. intros d p s r s' L. unfold read_block in L. crawl_withA FOL notac L. all: rf_fin. Qed.

  #[using="rc"] Lemma add_interface_rfile : forall (p : pcapT) off c s r s', mleaf (add_interface MOps P p off c) s r s' ->
    pc_rfile (snd (fst r)) = pc_rfile p.
  Proof. intros p off c s r s' L. unfold add_interface in L. crawl_withA FOL notac L. all: rf_fin. Qed.
  Ltac rf_heads H1 := first [ apply grow_buffer_rfile in H1 | apply read_block_rfile in H1 | apply add_interface_rfile in H1 ].

  #[using="rc FOL"] Lemma ng_scan_blocks_rfile : forall fuel (p : pcapT) s r s', mleaf (ng_scan_blocks MOps P fuel p) s r s' -> pc_rfile (snd r) = pc_rfile p.
  Proof.
    induction fuel as [|fuel IH]; intros p s r s' L; cbn [ng_scan_blocks] in L.
    - mleaf_inv L.
    - crawl_withA FOL ltac:(fun H1 => first [apply IH in H1 | rf_heads H1]) L. all: rf_fin.
  Qed.

  #[using="rc FOL"] Lemma pcap_next_packet_rfile : forall (p : pcapT) s r s', mleaf (pcap_next_packet MOps P p) s r s' -> pc_rfile (snd r) = pc_rfile p.
  Proof. intros p s r s' L. unfold pcap_next_packet in L. crawl_withA FOL rf_heads L. all: rf_fin. Qed.

  #[using="rc FOL"] Lemma pcap_ng_next_packet_rfile : forall fuel (p : pcapT) s r s', mleaf (pcap_ng_next_packet MOps P fuel p) s r s' -> pc_rfile (snd r) = pc_rfile p.
  Proof.
    intros fuel p s r s' L. unfold pcap_ng_next_packet in L.
    crawl_withA FOL ltac:(fun H1 => first [apply ng_scan_blocks_rfile in H1 | rf_heads H1]) L. all: rf_fin.
  Qed.

  #[using="rc FOL"] Lemma next_packet_op_rfile : forall fuel (p : pcapT) s r s', mleaf (next_packet_op MOps P fuel p) s r s' -> pc_rfile (snd r) = pc_rfile p.
  Proof.
    intros fuel p s r s' L. unfold next_packet_op in L.
    destruct (pc_priv p); [apply pcap_next_packet_rfile in L | apply pcap_ng_next_packet_rfile in L]; exact L.
  Qed.

  #[using="rc FOL"] Lemma offline_read_rfile : forall fuel (p : pcapT) s r s', mleaf (pcapint_offline_read_1 MOps P fuel p) s r s' -> pc_rfile (snd r) = pc_rfile p.
  Proof.
    intros fuel p s r s' L. unfold pcapint_offline_read_1 in L.
    crawl_withA FOL ltac:(fun H1 => apply next_packet_op_rfile in H1) L. all: rf_fin.
  Qed.

  (* [comment removed for export] *)
  #[using="rc FOL"] Lemma pcap_next_ex_rfile : forall fuel (p : pcapT) s st p' s',
    mleaf (Pcap.pcap_next_ex MOps P fuel p) s (st, p') s' -> pc_rfile p' = pc_rfile p.
  Proof.
    intros fuel p s st p' s' L. unfold Pcap.pcap_next_ex in L.
    crawl_withA FOL ltac:(fun H1 => apply offline_read_rfile in H1) L. all: rf_fin.
  Qed.

  #[using="rc"] Lemma pcap_stats_rfile : forall (p : pcapT) s sr p' s',
    mleaf (Pcap.pcap_stats (@MOps H hptr) p) s (sr, p') s' -> pc_rfile p' = pc_rfile p.
  Proof. intros p s sr p' s' L. unfold Pcap.pcap_stats in L. crawl_withA FOL notac L. all: rf_fin. Qed.
End Rfile.
End CANSEC2.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Strings.String.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MState OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Mem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Exec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Exit__S3.MLeaf.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Section LeafF.
  Variable node : Type.
  Variable segs : list Segment.
  Variable at_node : node -> footprint -> machine_state -> Prop.
  Variable sil : footprint -> machine_state -> machine_state -> Prop.
  Variable npeek : node -> option (machine_state -> resp).
  Variable fstep : node -> resp -> footprint -> footprint -> Prop.

  #[using="Type"] Lemma implF_has_leaf : forall {R} (t : itree node R) RNG Q ms,
    @implF node segs at_node sil npeek fstep R RNG t Q ms ->
    @implF node segs at_node sil npeek fstep R RNG t (fun r RNG' ms' => Q r RNG' ms' /\ has_leaf t r) ms.
  Proof.
    induction t as [r|n k IH]; intros RNG Q ms HI; cbn in *.
    - eapply evtS_mono; [exact HI|]. intros ms' HQ. split; [exact HQ| reflexivity].
    - eapply evtS_mono; [exact HI|]. intros ms1 [[Hat Hk]|(f & Hf & Hk)].
      + left. split; [exact Hat|]. intros rsp RNG' HF. eapply implF_mono; [apply IH; apply Hk; exact HF|].
        intros r RNG2 ms' [H1 H2]. split; [exact H1|]. exists rsp. exact H2.
      + right. exists f. split; [exact Hf|]. intros RNG' HF. eapply implF_mono; [apply IH; apply Hk; exact HF|].
        intros r RNG2 ms' [H1 H2]. split; [exact H1|]. exists (f ms1). exact H2.
  Qed.
End LeafF.

Section CANSEC1. Context {rc : runConstT}.
Section LeafG.
  Context {St : Type}.
  #[using="Type"] Lemma implMG_leaf : forall {A} RNG (c : Monad.M St A) s Q ms,
    implMG RNG c s Q ms -> implMG RNG c s (fun a s' RNG' ms' => Q a s' RNG' ms' /\ mleaf c s a s') ms.
  Proof.
    intros A RNG c s Q ms HI. unfold implMG in *. eapply implF_mono; [eapply implF_has_leaf; exact HI|].
    intros [|[a s']] RNG' ms'; cbn; [tauto|]. intros [H1 H2]. split; [exact H1| exact H2].
  Qed.
End LeafG.
End CANSEC1.

(* [comment removed for export] *)
Section FoLeaf.
  Context {H hptr : Type}.
  #[local] Notation PS := (PState H hptr).
  Record fo_leaf_laws (FO : @FrameOps H hptr) : Prop := mkFOL {
    fol_enter : forall (A : Type) f (body : Monad.M PS A) s a s', mleaf (fo_enter FO A f body) s a s' -> exists s1, mleaf body s1 a s';
    fol_ret : forall (A : Type) f (x : A) s a s', mleaf (fo_ret FO A f x) s a s' -> a = x
  }.
End FoLeaf.

(* [comment removed for export] *)
Ltac crawl_withA FOL tac L :=
  repeat (first
   [ lazymatch type of L with
     | mleaf (e_fenter _ _ _) _ _ _ => cbn [e_fenter prims] in L
     | mleaf (e_fret _ _ _) _ _ _ => cbn [e_fret prims] in L
     | mleaf (fo_enter _ _ _ _) _ _ _ => let s1 := fresh "ls" in apply (fol_enter _ FOL) in L as (s1 & L)
     | mleaf (fo_ret _ _ _ _) _ _ _ => apply (fol_ret _ FOL) in L; try (lazymatch type of L with ?x = _ => subst x end)
     | mleaf (mbind _ _) _ _ _ => let a := fresh "lv" in let s := fresh "ls" in let H1 := fresh "HL" in
         apply mleaf_bind in L as (a & s & H1 & L); crawl_withA FOL tac H1; try (lazymatch type of H1 with mleaf _ _ _ _ => clear H1 end)
     | mleaf (mo_bind MOps _ _) _ _ _ => let a := fresh "lv" in let s := fresh "ls" in let H1 := fresh "HL" in
         apply mleaf_mobind in L as (a & s & H1 & L); crawl_withA FOL tac H1; try (lazymatch type of H1 with mleaf _ _ _ _ => clear H1 end)
     | mleaf (mret _) _ _ _ => let E1 := fresh "E" in let E2 := fresh "E" in apply mleaf_ret in L as [E1 E2];
         try (lazymatch type of E2 with ?x = _ => subst x end); try (lazymatch type of E1 with ?x = _ => subst x end)
     | mleaf (mo_ret MOps _) _ _ _ => let E1 := fresh "E" in let E2 := fresh "E" in apply mleaf_moret in L as [E1 E2];
         try (lazymatch type of E2 with ?x = _ => subst x end); try (lazymatch type of E1 with ?x = _ => subst x end)
     | mleaf munr _ _ _ => destruct (mleaf_unr _ _ _ L)
     | mleaf (mo_unr MOps) _ _ _ => destruct (mleaf_mounr _ _ _ L)
     | mleaf ((fun _ => _) _) _ _ _ => cbv beta in L
     | mleaf (if ?b then _ else _) _ _ _ => destruct b
     | mleaf (match ?x with _ => _ end) _ _ _ => destruct x
     | mleaf (let _ := _ in _) _ _ _ => cbv zeta in L
     | mleaf _ _ _ _ => tac L
     end ]).

Section CANSEC2. Context {rc : runConstT}.
Section Rfile.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (stk : stack_site -> Z).
  Hypothesis FOL : fo_leaf_laws FO.
  #[local] Notation PS := (PState H hptr).
  #[local] Notation pcapT := (PcapTypes.pcap hptr hptr).
  #[local] Notation P := (prims HO FO stk).

  Ltac rf_simp := cbn [fst snd pc_rfile set_errbuf set_bufdata set_buffer set_header set_priv set_ng set_break_loop] in *.
  Ltac rf_fin := inj_all; rf_simp;
    repeat (match goal with
            | |- context [pc_rfile (if ?c then _ else _)] => destruct c; rf_simp
            | H : context [pc_rfile (if ?c then _ else _)] |- _ => destruct c; rf_simp
            end); congruence.

  #[using="rc"] Lemma grow_buffer_rfile : forall (p : pcapT) n s r s', mleaf (grow_buffer MOps P p n) s r s' -> pc_rfile (snd r) = pc_rfile p.
  Proof. intros p n s r s' L. unfold grow_buffer in L. crawl_withA FOL notac L. all: rf_fin. Qed.

  #[using="rc FOL"] Lemma read_block_rfile : forall d (p : pcapT) s r s', mleaf (read_block MOps P d p) s r s' ->
    match r with RB_Eof p' | RB_Err _ p' | RB_Ok _ p' => pc_rfile p' = pc_rfile p end.
  Proof. intros d p s r s' L. unfold read_block in L. crawl_withA FOL notac L. all: rf_fin. Qed.

  #[using="rc"] Lemma add_interface_rfile : forall (p : pcapT) off c s r s', mleaf (add_interface MOps P p off c) s r s' ->
    pc_rfile (snd (fst r)) = pc_rfile p.
  Proof. intros p off c s r s' L. unfold add_interface in L. crawl_withA FOL notac L. all: rf_fin. Qed.
  Ltac rf_heads H1 := first [ apply grow_buffer_rfile in H1 | apply read_block_rfile in H1 | apply add_interface_rfile in H1 ].

  #[using="rc FOL"] Lemma ng_scan_blocks_rfile : forall fuel (p : pcapT) s r s', mleaf (ng_scan_blocks MOps P fuel p) s r s' -> pc_rfile (snd r) = pc_rfile p.
  Proof.
    induction fuel as [|fuel IH]; intros p s r s' L; cbn [ng_scan_blocks] in L.
    - mleaf_inv L.
    - crawl_withA FOL ltac:(fun H1 => first [apply IH in H1 | rf_heads H1]) L. all: rf_fin.
  Qed.

  #[using="rc FOL"] Lemma pcap_next_packet_rfile : forall (p : pcapT) s r s', mleaf (pcap_next_packet MOps P p) s r s' -> pc_rfile (snd r) = pc_rfile p.
  Proof. intros p s r s' L. unfold pcap_next_packet in L. crawl_withA FOL rf_heads L. all: rf_fin. Qed.

  #[using="rc FOL"] Lemma pcap_ng_next_packet_rfile : forall fuel (p : pcapT) s r s', mleaf (pcap_ng_next_packet MOps P fuel p) s r s' -> pc_rfile (snd r) = pc_rfile p.
  Proof.
    intros fuel p s r s' L. unfold pcap_ng_next_packet in L.
    crawl_withA FOL ltac:(fun H1 => first [apply ng_scan_blocks_rfile in H1 | rf_heads H1]) L. all: rf_fin.
  Qed.

  #[using="rc FOL"] Lemma next_packet_op_rfile : forall fuel (p : pcapT) s r s', mleaf (next_packet_op MOps P fuel p) s r s' -> pc_rfile (snd r) = pc_rfile p.
  Proof.
    intros fuel p s r s' L. unfold next_packet_op in L.
    destruct (pc_priv p); [apply pcap_next_packet_rfile in L | apply pcap_ng_next_packet_rfile in L]; exact L.
  Qed.

  #[using="rc FOL"] Lemma offline_read_rfile : forall fuel (p : pcapT) s r s', mleaf (pcapint_offline_read_1 MOps P fuel p) s r s' -> pc_rfile (snd r) = pc_rfile p.
  Proof.
    intros fuel p s r s' L. unfold pcapint_offline_read_1 in L.
    crawl_withA FOL ltac:(fun H1 => apply next_packet_op_rfile in H1) L. all: rf_fin.
  Qed.

  (* [comment removed for export] *)
  #[using="rc FOL"] Lemma pcap_next_ex_rfile : forall fuel (p : pcapT) s st p' s',
    mleaf (Pcap.pcap_next_ex MOps P fuel p) s (st, p') s' -> pc_rfile p' = pc_rfile p.
  Proof.
    intros fuel p s st p' s' L. unfold Pcap.pcap_next_ex in L.
    crawl_withA FOL ltac:(fun H1 => apply offline_read_rfile in H1) L. all: rf_fin.
  Qed.

  #[using="rc"] Lemma pcap_stats_rfile : forall (p : pcapT) s sr p' s',
    mleaf (Pcap.pcap_stats (@MOps H hptr) p) s (sr, p') s' -> pc_rfile p' = pc_rfile p.
  Proof. intros p s sr p' s' L. unfold Pcap.pcap_stats in L. crawl_withA FOL notac L. all: rf_fin. Qed.
End Rfile.
End CANSEC2.
End TwB.
End LeafA.

(* [comment removed for export] *)
Module F_ngblk_segA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep Frame StoreFast.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow StepF SysStepF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg ABase.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.NpArith.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require GIA PcapRepA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require SfKitA__A3P. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.SfKitA__A3P.SfKitA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac qfold := try (lazymatch goal with |- evtF ?s ?r ?Q ?st => let QQ := fresh "QQ" in pose (QQ := Q); change Q with QQ end).
Import ListNotations.
Open Scope Z_scope.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= unp_store m a bs n Hn Ha Hl.


(* [comment removed for export] *)
Lemma le4_s32B : forall c, (0 <= c < 2^32)%Z -> le4 (Z_to_bv 64 (s32 c)) = le4 (Z_to_bv 64 c).
Proof.
  intros c Hc. pose proof (unsigned_s32 c Hc) as US.
  rewrite <- (Z_to_bv_bv_unsigned (Z_to_bv 64 (s32 c))). rewrite US.
  destruct (Z.ltb_spec c (2^31)); [reflexivity|].
  rewrite (le4_mod32 (c + 2^64 - 2^32)) by lia. f_equal. f_equal. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Local Ltac ck_live OK pc := lazymatch constr:((OK, pc)) with (573364%Z, 573364%Z) => idtac | (573364%Z, 573800%Z) => idtac | (573376%Z, 573376%Z) => idtac | (573376%Z, 573816%Z) => idtac | (573392%Z, 573392%Z) => idtac | (573392%Z, 573876%Z) => idtac | (573404%Z, 573404%Z) => idtac | (573404%Z, 573892%Z) => idtac | (573436%Z, 573436%Z) => idtac | (573436%Z, 573784%Z) => idtac | (573564%Z, 573564%Z) => idtac | (573564%Z, 573844%Z) => idtac end.
Local Ltac ck_arm OK n ::=
  lazymatch n with
  | O => fail "ck_join: step budget exhausted before reaching the join point" OK
  | S ?n' =>
    lazymatch goal with
    | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 OK) _ _ _ _) =>
        apply evtF_done; lazymatch goal with |- ?q _ => tryif is_var q then unfold q else idtac end; cbn [ck_post]; repeat eexists; simp_regs;
        first [ reflexivity | fail 1 "ck_join: a register outside the clobber list changed before" OK ]
    | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => zstep; rewrite ?sxb_sval; ck_arm OK n'
    | |- evtF _ _ _ (MS _ _ (if _ then _ else _) _ _ _ _) =>
        let K := fresh "Kck" in
        if_cases K; ck_zify K;
        lazymatch goal with
        | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) => tryif ck_live OK pc then first [ ck_arm OK n' | exfalso; ck_lia ] else first [ exfalso; ck_lia | ck_arm OK n' ]
        | _ => first [ exfalso; ck_lia | ck_arm OK n' ]
        end
    end
  end.
(* [comment removed for export] *)
Local Ltac cjq_fold := try (lazymatch goal with |- evtF ?s ?r ?Q ?st => let QQ := fresh "QQc" in pose (QQ := Q); change Q with QQ end).
Local Ltac ck_join_at UNP P N OK RS ::=
  ck_clear; cbv beta delta [mkR];
  lazymatch goal with
  | |- evtF ?segs ?RNG ?Q (MS ?R ?F ?pc ?fc ?rv ?m ?ro) =>
    lazymatch type of UNP with
    | unpoisoned m ?lo ?hi =>
      let b := fresh "shb" in let RD := fresh "RDsh" in let CK := fresh "CKsh" in let SR := fresh "SRsh" in
      destruct (ck_part_rd m lo hi P N UNP ltac:(ck_lia) ltac:(ck_lia) ltac:(lia) ltac:(ck_lia)) as (b & RD & CK);
      ck_fp_at lo P;
      pose proof (sval_range b) as SR;
      eapply (evtF_cut segs RNG (fun ms' => ck_post RS (fun R' => ms' = MS R' F (Z_to_bv 64 OK) fc rv m ro) R));
      [ cjq_fold; ck_arm OK 16%nat
      | let ms' := fresh "ms'" in let H := fresh "Hck" in
        intros ms' H; cbn [ck_post] in H; destruct_exs H; subst ms'; simp_regs; clear RD CK SR; ck_clear; try clear b ]
    | unpoisoned ?m' _ _ => fail "ck_join: the shadow fact" UNP "is about memory" m' "but the state's memory is" m
    end
  end.
Section CANSEC1. Context {rc : runConstT}.
Definition rb_hdr_swap_seq__stmt : Prop := forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : mem) (RNG : footprint) (HB : Z) (g0 g1 g2 g3 g4 g5 g6 g7 : Z),
    mem_inv asegs m -> (0 <= HB)%Z -> (HB + 8 < 2^64)%Z -> rng RNG HB 8 ->
    (0 <= g0 < 256)%Z -> (0 <= g1 < 256)%Z -> (0 <= g2 < 256)%Z -> (0 <= g3 < 256)%Z ->
    (0 <= g4 < 256)%Z -> (0 <= g5 < 256)%Z -> (0 <= g6 < 256)%Z -> (0 <= g7 < 256)%Z ->
    rw_cells asegs m HB [C4 (Z_to_bv 64 (le4val g0 g1 g2 g3)); C4 (Z_to_bv 64 (le4val g4 g5 g6 g7))] ->
    evtF asegs RNG (fun ms' => exists a0' a1' a2' a3' a4' a5' m',
        ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2' a3' a4' a5' a6 a7 s2 s3 s4 (Z_to_bv 64 HB) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 0x8bd04) fc None m' (seg_rom asegs)
        /\ munch [(HB, HB + 8)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
        /\ rw_cells asegs m' HB [C4 (Z_to_bv 64 (le4val g3 g2 g1 g0)); C4 (Z_to_bv 64 (le4val g7 g6 g5 g4))])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 (Z_to_bv 64 HB) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x8bca4) fc None m (seg_rom asegs)).
Section Sz2.
Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m RNG HB g0 g1 g2 g3 g4 g5 g6 g7 : ltac2:(SecDiet.SzSec.tyM 'rb_hdr_swap_seq__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
#[using="Type"] Lemma rb_hdr_swap_seq__body : ltac2:(SecDiet.SzSec.bodyP 'rb_hdr_swap_seq__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof.
 intros MI HB0 HBT RH B0 B1 B2 B3 B4 B5 B6 B7 FR.
 qfold.
  pose proof (munch_refl [(HB, HB + 8)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  do 24 zstep.
  apply evtF_done. do 7 eexists.
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
  eapply rw_cells_recell; [eassumption | cbn; repeat split; exact Logic.I |].
  cbn [cells_bytes cbytes app].
  rewrite (le4_lit g3 g2 g1 g0), (le4_lit g7 g6 g5 g4) by lia.
  rewrite (le4_of_val _ g3 g2 g1 g0 (g1 + 256 * g2 + 65536 * g3 + 16777216 * (((g3 / 128) * 4294967295) mod 256)));
    [| lia | lia | lia | lia | Z.div_mod_to_equations; lia
     | apply (swap32_valA _ g0 g1 g2 g3); [lia|lia|lia|lia| Z.div_mod_to_equations; lia | rewrite unsigned_sx32 by lia; unfold sxv, le4val; lia]].
  rewrite (le4_of_val _ g7 g6 g5 g4 (g5 + 256 * g6 + 65536 * g7 + 16777216 * (((g7 / 128) * 4294967295) mod 256)));
    [| lia | lia | lia | lia | Z.div_mod_to_equations; lia
     | apply (swap32_valA _ g4 g5 g6 g7); [lia|lia|lia|lia| Z.div_mod_to_equations; lia | rewrite unsigned_sx32 by lia; unfold sxv, le4val; lia]].
  reflexivity.
Qed.
End Sz2.
#[using="Type"] Lemma rb_hdr_swap_seq : ltac:(let t := eval cbv delta [rb_hdr_swap_seq__stmt] in rb_hdr_swap_seq__stmt in exact t).
Proof. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m RNG HB g0 g1 g2 g3 g4 g5 g6 g7. ltac2:(SecDiet.SzSec.closeP 'rb_hdr_swap_seq__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
(* [comment removed for export] *)
Ltac ck4_split_at UNP P OK RS :=
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch type of UNP with unpoisoned mm ?lo ?hi =>
      let b := fresh "shb" in let RD := fresh "RDsh" in let CK := fresh "CKsh" in let SR := fresh "SRsh" in
      destruct (ck_part_rd mm lo hi P 4 UNP ltac:(ck_lia) ltac:(ck_lia) ltac:(lia) ltac:(ck_lia)) as (b & RD & CK);
      ck_fp_at lo P; pose proof (sval_range b) as SR end end;
  zstep; zstep;
  cbv beta delta [mkR];
  lazymatch goal with |- evtF ?segs ?RNGx ?Q (MS ?R ?F ?pc ?fc ?rv ?mm ?ro) =>
    eapply (evtF_cut segs RNGx (fun ms' => ck_post RS (fun R' => ms' = MS R' F (Z_to_bv 64 OK) fc rv mm ro) R)) end;
  [ ck_arm OK 16%nat
  | let ms' := fresh "ms'" in let H := fresh "Hck" in
    intros ms' H; cbn [ck_post] in H; destruct_exs H; subst ms'; simp_regs; ck_clear ].

Definition rb_trl_swap_seq__stmt : Prop := forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : mem) (RNG : footprint) (TA B alloc bB u0 u1 u2 u3 : Z),
    mem_inv asegs m ->
    rw_cells asegs m TA [C4 (Z_to_bv 64 (le4val u0 u1 u2 u3))] ->
    unpoisoned m B (B + alloc) -> rng RNG B alloc -> rng RNG (shad B) (nshad alloc) ->
    (B mod 16 = 0)%Z -> (TA mod 4 = 0)%Z -> (B <= TA)%Z -> (TA + 4 <= B + alloc)%Z ->
    (B + alloc <= 2147446784 + bB * 140737479966720)%Z -> (17594333495296 * bB <= B)%Z -> (0 <= bB <= 1)%Z -> (6303744 <= B)%Z ->
    (0 <= u0 < 256)%Z -> (0 <= u1 < 256)%Z -> (0 <= u2 < 256)%Z -> (0 <= u3 < 256)%Z ->
    evtF asegs RNG (fun ms' => exists a2' a4' a5' a6' m',
        ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 TA) (Z_to_bv 64 (Z.shiftr TA 3)) a2' a3 a4' a5' a6' a7 s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 2147450880) s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 0x8bff0) fc None m' (seg_rom asegs)
        /\ munch [(TA, TA + 4)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
        /\ rw_cells asegs m' TA [C4 (Z_to_bv 64 (le4val u3 u2 u1 u0))])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 TA) (Z_to_bv 64 (Z.shiftr TA 3)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 2147450880) s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x8bfa8) fc None m (seg_rom asegs)).
Section Sz3.
Variables ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 F fc m RNG TA B alloc bB u0 u1 u2 u3 : ltac2:(SecDiet.SzSec.tyM 'rb_trl_swap_seq__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
#[using="Type"] Lemma rb_trl_swap_seq__body : ltac2:(SecDiet.SzSec.bodyP 'rb_trl_swap_seq__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof.
 intros MI TR BUNP BRNG BRSH B16 TA4 TALO TAHI bBhi bBlo bBr bBimg U0 U1 U2 U3.
 qfold.
  pose proof (munch_refl [(TA, TA + 4)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep.
  ck_join_at BUNP TA 4%Z 0x8bfb4%Z [14%Z; 15%Z].
  ck4_split_at BUNP TA 0x8bfc0%Z [14%Z; 15%Z].
  do 11 zstep. zstep.
  apply evtF_done. do 5 eexists.
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
  eapply rw_cells_recell; [eassumption | cbn; repeat split; exact Logic.I |].
  cbn [cells_bytes cbytes app].
  rewrite (le4_lit u3 u2 u1 u0) by lia.
  rewrite (le4_of_val _ u3 u2 u1 u0 (u1 + 256 * u2 + 65536 * u3 + 16777216 * (((u3 / 128) * 4294967295) mod 256)));
    [reflexivity | lia | lia | lia | lia | Z.div_mod_to_equations; lia
     | apply (swap32_valA _ u0 u1 u2 u3); [lia|lia|lia|lia| Z.div_mod_to_equations; lia | rewrite unsigned_sx32 by lia; unfold sxv, le4val; lia]].
Qed.
End Sz3.
#[using="Type"] Lemma rb_trl_swap_seq : ltac:(let t := eval cbv delta [rb_trl_swap_seq__stmt] in rb_trl_swap_seq__stmt in exact t).
Proof. intros ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 F fc m RNG TA B alloc bB u0 u1 u2 u3. ltac2:(SecDiet.SzSec.closeP 'rb_trl_swap_seq__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
Definition rb_trl_ck_seq__stmt : Prop := forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : mem) (RNG : footprint) (TA B alloc bB v0 v1 v2 v3 : Z),
    mem_inv asegs m ->
    rw_cells asegs m TA [C4 (Z_to_bv 64 (le4val v0 v1 v2 v3))] ->
    unpoisoned m B (B + alloc) -> rng RNG B alloc -> rng RNG (shad B) (nshad alloc) ->
    (B mod 16 = 0)%Z -> (TA mod 4 = 0)%Z -> (B <= TA)%Z -> (TA + 4 <= B + alloc)%Z ->
    (B + alloc <= 2147446784 + bB * 140737479966720)%Z -> (17594333495296 * bB <= B)%Z -> (0 <= bB <= 1)%Z -> (6303744 <= B)%Z ->
    a1 = Z_to_bv 64 (Z.shiftr TA 3) ->
    evtF asegs RNG (fun ms' => exists a1' a2',
        ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 TA) a1' a2' a3 (sx32 (Z_to_bv 64 (le4val v0 v1 v2 v3))) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 2147450880) s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 0x8c000) fc None m (seg_rom asegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 TA) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 2147450880) s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x8bff0) fc None m (seg_rom asegs)).
Section Sz4.
Variables ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 F fc m RNG TA B alloc bB v0 v1 v2 v3 : ltac2:(SecDiet.SzSec.tyM 'rb_trl_ck_seq__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
#[using="Type"] Lemma rb_trl_ck_seq__body : ltac2:(SecDiet.SzSec.bodyP 'rb_trl_ck_seq__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof.
 intros MI TR BUNP BRNG BRSH B16 TA4 TALO TAHI bBhi bBlo bBr bBimg ->.
 qfold.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep.
  ck_join_at BUNP TA 4%Z 0x8bffc%Z [11%Z; 12%Z].
  zstep.
  apply evtF_done. do 2 eexists. reflexivity.
Qed.
End Sz4.
#[using="Type"] Lemma rb_trl_ck_seq : ltac:(let t := eval cbv delta [rb_trl_ck_seq__stmt] in rb_trl_ck_seq__stmt in exact t).
Proof. intros ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 F fc m RNG TA B alloc bB v0 v1 v2 v3. ltac2:(SecDiet.SzSec.closeP 'rb_trl_ck_seq__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
(* [comment removed for export] *)
Definition rb_cur_seq__stmt : Prop := forall (ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s6 s7 s9 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : mem) (RNG : footprint) (SPA CUR HB Bd tl btw tlw : Z) (c0 c1 c2 c4 c5 c7 c8 c9 c10 : word) (cj : list byte),
    mem_inv asegs m ->
    rw_cells asegs m SPA [C8 c0; C8 c1; C8 c2; C8 (Z_to_bv 64 Bd); C8 c4; C8 c5; C8 (Z_to_bv 64 CUR); C8 c7; C8 c8; C8 c9; C8 c10] ->
    rw_cells asegs m CUR [CB 24 cj] ->
    rw_cells asegs m HB [C4 (Z_to_bv 64 btw); C4 (Z_to_bv 64 tlw)] ->
    unpoisoned m CUR (CUR + 24) -> rng RNG CUR 24 -> rng RNG (shad CUR) (nshad 24) -> rng RNG SPA 88 -> rng RNG HB 8 ->
    (CUR mod 8 = 0)%Z -> (SPA + 88 <= CUR)%Z -> (17594333495296 <= SPA)%Z -> (CUR + 24 <= 2^47)%Z ->
    (0 < HB)%Z -> (HB + 8 <= SPA)%Z -> (0 <= btw < 2^32)%Z -> (12 <= tl <= 2^30)%Z ->
    evtF asegs RNG (fun ms' => exists a1' a2' m' cpad,
        ms' = MS (mkR ra (Z_to_bv 64 SPA) gp tp t0 t1 t2 s0 (Z_to_bv 64 SPA) (Z_to_bv 64 1) a1' a2' a3 a4 a5 a6 a7
                      s2 s3 s4 (Z_to_bv 64 HB) s6 s7 (Z_to_bv 64 (tl - 12)) s9 (Z_to_bv 64 2147450880) s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 0x8bdb0) fc None m' (seg_rom asegs)
        /\ munch [(CUR, CUR + 24)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
        /\ rw_cells asegs m' CUR [C8 (Z_to_bv 64 Bd); C8 (Z_to_bv 64 (tl - 12)); C4 (Z_to_bv 64 btw); CB 4 cpad])
      (MS (mkR ra (Z_to_bv 64 SPA) gp tp t0 t1 t2 s0 (Z_to_bv 64 SPA) a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 (Z_to_bv 64 HB) s6 s7 (Z_to_bv 64 tl) s9 (Z_to_bv 64 2147450880) s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x8c004) fc None m (seg_rom asegs)).
Section Sz5.
Variables ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s6 s7 s9 s11 t3 t4 t5 t6 F fc m RNG SPA CUR HB Bd tl btw tlw c0 c1 c2 c4 c5 c7 c8 c9 c10 cj : ltac2:(SecDiet.SzSec.tyM 'rb_cur_seq__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
#[using="Type"] Lemma rb_cur_seq__body : ltac2:(SecDiet.SzSec.bodyP 'rb_cur_seq__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof.
 intros MI FRA HCUR HBH CURUNP CURRNG CURSH RSPA RHB CUR8 SPCUR SPALO CURHI HB0 HBSP BTW TL.
 qfold.
  assert (LJ : length cj = 24%nat) by (destruct HCUR as [[WF _] _]; cbn in WF; tauto).
  pose proof (munch_refl [(CUR, CUR + 24)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep.
  ck0 CURUNP; ck_go.
  do 2 zstep.
  zstep.
  ck0 CURUNP; ck_go.
  do 2 zstep.
  zstep.
  ck0 CURUNP; ck_go.
  zstep. do 2 zstep.
  apply evtF_done. do 3 eexists. exists (skipn 4 (skipn 8 (skipn 8 cj))).
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
  eapply rw_cells_recell; [exact HCUR | cbn; repeat split; try exact Logic.I; rewrite !length_skipn; lia |].
  cbn [cells_bytes cbytes app].
  replace (sx32 (Z_to_bv 64 btw)) with (Z_to_bv 64 (s32 btw)) by (unfold sx32, s32; rewrite unsigned_lit by lia; f_equal; unfold bv_swrap, bv_wrap; cbn; lia).
  rewrite (le4_s32B btw) by lia. reflexivity.
Qed.
End Sz5.
#[using="Type"] Lemma rb_cur_seq : ltac:(let t := eval cbv delta [rb_cur_seq__stmt] in rb_cur_seq__stmt in exact t).
Proof. intros ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s6 s7 s9 s11 t3 t4 t5 t6 F fc m RNG SPA CUR HB Bd tl btw tlw c0 c1 c2 c4 c5 c7 c8 c9 c10 cj. ltac2:(SecDiet.SzSec.closeP 'rb_cur_seq__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
(* [comment removed for export] *)
Ltac fix_sbA := try (lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 ?w)) _) => change (le1 w) with [Z_to_bv 8 (bv_unsigned w)]; mem_after_store end).
Ltac bzstep := zstep; fix_sbA.

(* [comment removed for export] *)
Definition rb_memcpy_seq__stmt : Prop := forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s6 s7 s8 s9 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : mem) (RNG : footprint) (P B alloc Fb V bufsize bB kPB kBF : Z) (jk : list byte),
    mem_inv asegs m ->
    rw_cells asegs m (P + 20) [C4 (Z_to_bv 64 bufsize); C8 (Z_to_bv 64 B)] ->
    rw_cells asegs m (Fb + 32) [C8 (Z_to_bv 64 V)] ->
    rw_cells asegs m B [CB 8 jk] ->
    unpoisoned m B (B + alloc) -> rng RNG B alloc -> rng RNG (shad B) (nshad alloc) -> rng RNG P 680 -> rng RNG Fb 64 ->
    (B mod 16 = 0)%Z -> (8 <= alloc)%Z -> (0 < P)%Z -> (0 < Fb)%Z -> (P + 680 <= 2^47)%Z -> (Fb + 64 <= 2^47)%Z -> (B + alloc <= 2^47)%Z ->
    (B + alloc <= 2147446784 + bB * 140737479966720)%Z -> (17594333495296 * bB <= B)%Z -> (0 <= bB <= 1)%Z -> (6303744 <= B)%Z ->
    (P + 680 <= B + kPB * 18446744073709551616)%Z -> (B + alloc <= P + (1 - kPB) * 18446744073709551616)%Z -> (0 <= kPB <= 1)%Z ->
    (B + alloc <= Fb + kBF * 18446744073709551616)%Z -> (Fb + 64 <= B + (1 - kBF) * 18446744073709551616)%Z -> (0 <= kBF <= 1)%Z ->
    (0 <= V < 2^64)%Z ->
    evtF asegs RNG (fun ms' => exists t0' a1' a2' a3' a4' a5' a6' a7' m',
        ms' = MS (mkR ra sp gp tp t0' t1 t2 s0 s1 (Z_to_bv 64 (P + 24)) a1' a2' a3' a4' a5' a6' a7'
                      s2 (Z_to_bv 64 B) s4 (Z_to_bv 64 (Fb + 32)) s6 s7 s8 s9 (Z_to_bv 64 2147450880) s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 0x8bf64) fc None m' (seg_rom asegs)
        /\ munch [(B, B + 8)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
        /\ rw_cells asegs m' B [CB 8 (le8 (Z_to_bv 64 V))])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (P + 24)) a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 (Z_to_bv 64 (Fb + 32)) s6 s7 s8 s9 (Z_to_bv 64 2147450880) s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x8bef8) fc None m (seg_rom asegs)).
Section Sz6.
Variables ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s6 s7 s8 s9 s11 t3 t4 t5 t6 F fc m RNG P B alloc Fb V bufsize bB kPB kBF jk : ltac2:(SecDiet.SzSec.tyM 'rb_memcpy_seq__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
#[using="Type"] Lemma rb_memcpy_seq__body : ltac2:(SecDiet.SzSec.bodyP 'rb_memcpy_seq__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof.
 intros MI HBS HBH HB BUNP BRNG BRSH PRNG FRNG B16 AL8 P0 Fb0 PHI FHI BHI bBhi bBlo bBr bBimg kPBa kPBb kPBr kBF1 kBF2 kBFr HV.
 qfold.
  pose proof (munch_refl [(B, B + 8)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep.
  ck0 BUNP; ck_go.
  zstep.
  ck0 BUNP; ck_go.
  do 6 zstep.
  bzstep.
  do 3 bzstep. zstep. do 4 bzstep.
  zstep.
  apply evtF_done. do 9 eexists.
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
  eapply rw_cells_recell; [exact HB | cbn; repeat split; exact Logic.I |].
  cbn [cells_bytes cbytes app]. unfold le8, word_to_le_bytes. rewrite !unsigned_lit_wrap. rewrite !(Z.mod_small V) by lia.
  cbn [Z_to_le_bytes]. rewrite !Z.shiftr_shiftr by lia. rewrite !Z.shiftr_div_pow2 by lia.
  cbn [Z.add Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul Pos.add]. rewrite ?app_nil_r.
  repeat match goal with |- (_ :: _) = (_ :: _) => f_equal end; try reflexivity; apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit.Z_to_bv8_mod; change (8 + 8)%Z with 16%Z; change (16 + 8)%Z with 24%Z; change (24 + 8)%Z with 32%Z;
    change (32 + 8)%Z with 40%Z; change (40 + 8)%Z with 48%Z; change (48 + 8)%Z with 56%Z; Z.div_mod_to_equations; lia.
Qed.
End Sz6.
#[using="Type"] Lemma rb_memcpy_seq : ltac:(let t := eval cbv delta [rb_memcpy_seq__stmt] in rb_memcpy_seq__stmt in exact t).
Proof. intros ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s6 s7 s8 s9 s11 t3 t4 t5 t6 F fc m RNG P B alloc Fb V bufsize bB kPB kBF jk. ltac2:(SecDiet.SzSec.closeP 'rb_memcpy_seq__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.StoreFast.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.NpArith.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.SfKitA__A3P.SfKitA.TwB.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac qfold := try (lazymatch goal with |- evtF ?s ?r ?Q ?st => let QQ := fresh "QQ" in pose (QQ := Q); change Q with QQ end).
Import ListNotations.
Open Scope Z_scope.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= unp_store m a bs n Hn Ha Hl.


(* [comment removed for export] *)
Lemma le4_s32B : forall c, (0 <= c < 2^32)%Z -> le4 (Z_to_bv 64 (s32 c)) = le4 (Z_to_bv 64 c).
Proof.
  intros c Hc. pose proof (unsigned_s32 c Hc) as US.
  rewrite <- (Z_to_bv_bv_unsigned (Z_to_bv 64 (s32 c))). rewrite US.
  destruct (Z.ltb_spec c (2^31)); [reflexivity|].
  rewrite (le4_mod32 (c + 2^64 - 2^32)) by lia. f_equal. f_equal. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Local Ltac ck_live OK pc := lazymatch constr:((OK, pc)) with (573324%Z, 573324%Z) => idtac | (573324%Z, 573760%Z) => idtac | (573336%Z, 573336%Z) => idtac | (573336%Z, 573776%Z) => idtac | (573352%Z, 573352%Z) => idtac | (573352%Z, 573836%Z) => idtac | (573364%Z, 573364%Z) => idtac | (573364%Z, 573852%Z) => idtac | (573396%Z, 573396%Z) => idtac | (573396%Z, 573744%Z) => idtac | (573524%Z, 573524%Z) => idtac | (573524%Z, 573804%Z) => idtac end.
Local Ltac ck_arm OK n ::=
  lazymatch n with
  | O => fail "ck_join: step budget exhausted before reaching the join point" OK
  | S ?n' =>
    lazymatch goal with
    | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 OK) _ _ _ _) =>
        apply evtF_done; lazymatch goal with |- ?q _ => tryif is_var q then unfold q else idtac end; cbn [ck_post]; repeat eexists; simp_regs;
        first [ reflexivity | fail 1 "ck_join: a register outside the clobber list changed before" OK ]
    | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => zstep; rewrite ?sxb_sval; ck_arm OK n'
    | |- evtF _ _ _ (MS _ _ (if _ then _ else _) _ _ _ _) =>
        let K := fresh "Kck" in
        if_cases K; ck_zify K;
        lazymatch goal with
        | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) => tryif ck_live OK pc then first [ ck_arm OK n' | exfalso; ck_lia ] else first [ exfalso; ck_lia | ck_arm OK n' ]
        | _ => first [ exfalso; ck_lia | ck_arm OK n' ]
        end
    end
  end.
(* [comment removed for export] *)
Local Ltac cjq_fold := try (lazymatch goal with |- evtF ?s ?r ?Q ?st => let QQ := fresh "QQc" in pose (QQ := Q); change Q with QQ end).
Local Ltac ck_join_at UNP P N OK RS ::=
  ck_clear; cbv beta delta [mkR];
  lazymatch goal with
  | |- evtF ?segs ?RNG ?Q (MS ?R ?F ?pc ?fc ?rv ?m ?ro) =>
    lazymatch type of UNP with
    | unpoisoned m ?lo ?hi =>
      let b := fresh "shb" in let RD := fresh "RDsh" in let CK := fresh "CKsh" in let SR := fresh "SRsh" in
      destruct (ck_part_rd m lo hi P N UNP ltac:(ck_lia) ltac:(ck_lia) ltac:(lia) ltac:(ck_lia)) as (b & RD & CK);
      ck_fp_at lo P;
      pose proof (sval_range b) as SR;
      eapply (evtF_cut segs RNG (fun ms' => ck_post RS (fun R' => ms' = MS R' F (Z_to_bv 64 OK) fc rv m ro) R));
      [ cjq_fold; ck_arm OK 16%nat
      | let ms' := fresh "ms'" in let H := fresh "Hck" in
        intros ms' H; cbn [ck_post] in H; destruct_exs H; subst ms'; simp_regs; clear RD CK SR; ck_clear; try clear b ]
    | unpoisoned ?m' _ _ => fail "ck_join: the shadow fact" UNP "is about memory" m' "but the state's memory is" m
    end
  end.
Section CANSEC1. Context {rc : runConstT}.
Definition rb_hdr_swap_seq__stmt : Prop := forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : mem) (RNG : footprint) (HB : Z) (g0 g1 g2 g3 g4 g5 g6 g7 : Z),
    mem_inv asegs m -> (0 <= HB)%Z -> (HB + 8 < 2^64)%Z -> rng RNG HB 8 ->
    (0 <= g0 < 256)%Z -> (0 <= g1 < 256)%Z -> (0 <= g2 < 256)%Z -> (0 <= g3 < 256)%Z ->
    (0 <= g4 < 256)%Z -> (0 <= g5 < 256)%Z -> (0 <= g6 < 256)%Z -> (0 <= g7 < 256)%Z ->
    rw_cells asegs m HB [C4 (Z_to_bv 64 (le4val g0 g1 g2 g3)); C4 (Z_to_bv 64 (le4val g4 g5 g6 g7))] ->
    evtF asegs RNG (fun ms' => exists a0' a1' a2' a3' a4' a5' m',
        ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2' a3' a4' a5' a6 a7 s11 s10 s2 (Z_to_bv 64 HB) s6 s8 s7 s9 s3 s4 t3 t4 t5 t6)
                 F (Z_to_bv 64 0x8bcb8) fc None m' (seg_rom asegs)
        /\ munch [(HB, HB + 8)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
        /\ rw_cells asegs m' HB [C4 (Z_to_bv 64 (le4val g3 g2 g1 g0)); C4 (Z_to_bv 64 (le4val g7 g6 g5 g4))])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s11 s10 s2 (Z_to_bv 64 HB) s6 s8 s7 s9 s3 s4 t3 t4 t5 t6)
          F (Z_to_bv 64 0x8bc58) fc None m (seg_rom asegs)).
Section Sz2.
Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m RNG HB g0 g1 g2 g3 g4 g5 g6 g7 : ltac2:(SecDiet.SzSec.tyM 'rb_hdr_swap_seq__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
#[using="Type"] Lemma rb_hdr_swap_seq__body : ltac2:(SecDiet.SzSec.bodyP 'rb_hdr_swap_seq__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof.
 intros MI HB0 HBT RH B0 B1 B2 B3 B4 B5 B6 B7 FR.
 qfold.
  pose proof (munch_refl [(HB, HB + 8)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  do 24 zstep.
  apply evtF_done. do 7 eexists.
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
  eapply rw_cells_recell; [eassumption | cbn; repeat split; exact Logic.I |].
  cbn [cells_bytes cbytes app].
  rewrite (le4_lit g3 g2 g1 g0), (le4_lit g7 g6 g5 g4) by lia.
  rewrite (le4_of_val _ g3 g2 g1 g0 (g1 + 256 * g2 + 65536 * g3 + 16777216 * (((g3 / 128) * 4294967295) mod 256)));
    [| lia | lia | lia | lia | Z.div_mod_to_equations; lia
     | apply (swap32_valA _ g0 g1 g2 g3); [lia|lia|lia|lia| Z.div_mod_to_equations; lia | rewrite unsigned_sx32 by lia; unfold sxv, le4val; lia]].
  rewrite (le4_of_val _ g7 g6 g5 g4 (g5 + 256 * g6 + 65536 * g7 + 16777216 * (((g7 / 128) * 4294967295) mod 256)));
    [| lia | lia | lia | lia | Z.div_mod_to_equations; lia
     | apply (swap32_valA _ g4 g5 g6 g7); [lia|lia|lia|lia| Z.div_mod_to_equations; lia | rewrite unsigned_sx32 by lia; unfold sxv, le4val; lia]].
  reflexivity.
Qed.
End Sz2.
#[using="Type"] Lemma rb_hdr_swap_seq : ltac:(let t := eval cbv delta [rb_hdr_swap_seq__stmt] in rb_hdr_swap_seq__stmt in exact t).
Proof. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m RNG HB g0 g1 g2 g3 g4 g5 g6 g7. ltac2:(SecDiet.SzSec.closeP 'rb_hdr_swap_seq__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
(* [comment removed for export] *)
Ltac ck4_split_at UNP P OK RS :=
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch type of UNP with unpoisoned mm ?lo ?hi =>
      let b := fresh "shb" in let RD := fresh "RDsh" in let CK := fresh "CKsh" in let SR := fresh "SRsh" in
      destruct (ck_part_rd mm lo hi P 4 UNP ltac:(ck_lia) ltac:(ck_lia) ltac:(lia) ltac:(ck_lia)) as (b & RD & CK);
      ck_fp_at lo P; pose proof (sval_range b) as SR end end;
  zstep; zstep;
  cbv beta delta [mkR];
  lazymatch goal with |- evtF ?segs ?RNGx ?Q (MS ?R ?F ?pc ?fc ?rv ?mm ?ro) =>
    eapply (evtF_cut segs RNGx (fun ms' => ck_post RS (fun R' => ms' = MS R' F (Z_to_bv 64 OK) fc rv mm ro) R)) end;
  [ ck_arm OK 16%nat
  | let ms' := fresh "ms'" in let H := fresh "Hck" in
    intros ms' H; cbn [ck_post] in H; destruct_exs H; subst ms'; simp_regs; ck_clear ].

Definition rb_trl_swap_seq__stmt : Prop := forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : mem) (RNG : footprint) (TA B alloc bB u0 u1 u2 u3 : Z),
    mem_inv asegs m ->
    rw_cells asegs m TA [C4 (Z_to_bv 64 (le4val u0 u1 u2 u3))] ->
    unpoisoned m B (B + alloc) -> rng RNG B alloc -> rng RNG (shad B) (nshad alloc) ->
    (B mod 16 = 0)%Z -> (TA mod 4 = 0)%Z -> (B <= TA)%Z -> (TA + 4 <= B + alloc)%Z ->
    (B + alloc <= 2147446784 + bB * 140737479966720)%Z -> (17594333495296 * bB <= B)%Z -> (0 <= bB <= 1)%Z -> (6307840 <= B)%Z ->
    (0 <= u0 < 256)%Z -> (0 <= u1 < 256)%Z -> (0 <= u2 < 256)%Z -> (0 <= u3 < 256)%Z ->
    evtF asegs RNG (fun ms' => exists a2' a4' a5' a6' m',
        ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 TA) (Z_to_bv 64 (Z.shiftr TA 3)) a2' a3 a4' a5' a6' a7 s11 (Z_to_bv 64 2147450880) s2 s5 s6 s8 s7 s9 s3 s4 t3 t4 t5 t6)
                 F (Z_to_bv 64 0x8c048) fc None m' (seg_rom asegs)
        /\ munch [(TA, TA + 4)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
        /\ rw_cells asegs m' TA [C4 (Z_to_bv 64 (le4val u3 u2 u1 u0))])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 TA) (Z_to_bv 64 (Z.shiftr TA 3)) a2 a3 a4 a5 a6 a7 s11 (Z_to_bv 64 2147450880) s2 s5 s6 s8 s7 s9 s3 s4 t3 t4 t5 t6)
          F (Z_to_bv 64 0x8bf9c) fc None m (seg_rom asegs)).
Section Sz3.
Variables ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 F fc m RNG TA B alloc bB u0 u1 u2 u3 : ltac2:(SecDiet.SzSec.tyM 'rb_trl_swap_seq__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
#[using="Type"] Lemma rb_trl_swap_seq__body : ltac2:(SecDiet.SzSec.bodyP 'rb_trl_swap_seq__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof.
 intros MI TR BUNP BRNG BRSH B16 TA4 TALO TAHI bBhi bBlo bBr bBimg U0 U1 U2 U3.
 qfold.
  pose proof (munch_refl [(TA, TA + 4)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep.
  ck_join_at BUNP TA 4%Z 0x8bfa8%Z [14%Z; 15%Z].
  ck4_split_at BUNP TA 0x8bfb4%Z [14%Z; 15%Z].
  do 11 zstep. zstep.
  zstep.   (* [comment removed for export] *)
  apply evtF_done. do 5 eexists.
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
  eapply rw_cells_recell; [eassumption | cbn; repeat split; exact Logic.I |].
  cbn [cells_bytes cbytes app].
  rewrite (le4_lit u3 u2 u1 u0) by lia.
  rewrite (le4_of_val _ u3 u2 u1 u0 (u1 + 256 * u2 + 65536 * u3 + 16777216 * (((u3 / 128) * 4294967295) mod 256)));
    [reflexivity | lia | lia | lia | lia | Z.div_mod_to_equations; lia
     | apply (swap32_valA _ u0 u1 u2 u3); [lia|lia|lia|lia| Z.div_mod_to_equations; lia | rewrite unsigned_sx32 by lia; unfold sxv, le4val; lia]].
Qed.
End Sz3.
#[using="Type"] Lemma rb_trl_swap_seq : ltac:(let t := eval cbv delta [rb_trl_swap_seq__stmt] in rb_trl_swap_seq__stmt in exact t).
Proof. intros ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 F fc m RNG TA B alloc bB u0 u1 u2 u3. ltac2:(SecDiet.SzSec.closeP 'rb_trl_swap_seq__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
Definition rb_trl_ck_seq__stmt : Prop := forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : mem) (RNG : footprint) (TA B alloc bB v0 v1 v2 v3 : Z),
    mem_inv asegs m ->
    rw_cells asegs m TA [C4 (Z_to_bv 64 (le4val v0 v1 v2 v3))] ->
    unpoisoned m B (B + alloc) -> rng RNG B alloc -> rng RNG (shad B) (nshad alloc) ->
    (B mod 16 = 0)%Z -> (TA mod 4 = 0)%Z -> (B <= TA)%Z -> (TA + 4 <= B + alloc)%Z ->
    (B + alloc <= 2147446784 + bB * 140737479966720)%Z -> (17594333495296 * bB <= B)%Z -> (0 <= bB <= 1)%Z -> (6307840 <= B)%Z ->
    a1 = Z_to_bv 64 (Z.shiftr TA 3) ->
    evtF asegs RNG (fun ms' => exists a1' a2',
        ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 TA) a1' a2' a3 (sx32 (Z_to_bv 64 (le4val v0 v1 v2 v3))) a5 a6 a7 s11 (Z_to_bv 64 2147450880) s2 s5 s6 s8 s7 s9 s3 s4 t3 t4 t5 t6)
                 F (Z_to_bv 64 0x8c058) fc None m (seg_rom asegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 TA) a1 a2 a3 a4 a5 a6 a7 s11 (Z_to_bv 64 2147450880) s2 s5 s6 s8 s7 s9 s3 s4 t3 t4 t5 t6)
          F (Z_to_bv 64 0x8c048) fc None m (seg_rom asegs)).
Section Sz4.
Variables ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 F fc m RNG TA B alloc bB v0 v1 v2 v3 : ltac2:(SecDiet.SzSec.tyM 'rb_trl_ck_seq__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
#[using="Type"] Lemma rb_trl_ck_seq__body : ltac2:(SecDiet.SzSec.bodyP 'rb_trl_ck_seq__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof.
 intros MI TR BUNP BRNG BRSH B16 TA4 TALO TAHI bBhi bBlo bBr bBimg ->.
 qfold.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep.
  ck_join_at BUNP TA 4%Z 0x8c054%Z [11%Z; 12%Z].
  zstep.
  apply evtF_done. do 2 eexists. reflexivity.
Qed.
End Sz4.
#[using="Type"] Lemma rb_trl_ck_seq : ltac:(let t := eval cbv delta [rb_trl_ck_seq__stmt] in rb_trl_ck_seq__stmt in exact t).
Proof. intros ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 F fc m RNG TA B alloc bB v0 v1 v2 v3. ltac2:(SecDiet.SzSec.closeP 'rb_trl_ck_seq__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
(* [comment removed for export] *)
Definition rb_cur_seq__stmt : Prop := forall (ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s6 s8 s9 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : mem) (RNG : footprint) (SPA CUR HB Bd tl btw tlw : Z) (c0 c1 c2 c3 c4 c5 c7 c8 c9 c10 : word) (cj : list byte),
    mem_inv asegs m ->
    rw_cells asegs m SPA [C8 c0; C8 c1; C8 c2; C8 c3; C8 c4; C8 c5; C8 (Z_to_bv 64 CUR); C8 c7; C8 c8; C8 c9; C8 c10] ->
    rw_cells asegs m CUR [CB 24 cj] ->
    rw_cells asegs m HB [C4 (Z_to_bv 64 btw); C4 (Z_to_bv 64 tlw)] ->
    unpoisoned m CUR (CUR + 24) -> rng RNG CUR 24 -> rng RNG (shad CUR) (nshad 24) -> rng RNG SPA 88 -> rng RNG HB 8 ->
    (CUR mod 8 = 0)%Z -> (SPA + 88 <= CUR)%Z -> (17594333495296 <= SPA)%Z -> (CUR + 24 <= 2^47)%Z ->
    (0 < HB)%Z -> (HB + 8 <= SPA)%Z -> (0 <= btw < 2^32)%Z -> (12 <= tl <= 2^30)%Z ->
    evtF asegs RNG (fun ms' => exists a1' a2' m' cpad,
        ms' = MS (mkR ra (Z_to_bv 64 SPA) gp tp t0 t1 t2 s0 (Z_to_bv 64 SPA) (Z_to_bv 64 1) a1' a2' a3 a4 a5 a6 a7
                      s2 (Z_to_bv 64 2147450880) s4 (Z_to_bv 64 HB) s6 (Z_to_bv 64 (tl - 12)) s8 s9 (Z_to_bv 64 Bd) s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 0x8bd70) fc None m' (seg_rom asegs)
        /\ munch [(CUR, CUR + 24)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
        /\ rw_cells asegs m' CUR [C8 (Z_to_bv 64 Bd); C8 (Z_to_bv 64 (tl - 12)); C4 (Z_to_bv 64 btw); CB 4 cpad])
      (MS (mkR ra (Z_to_bv 64 SPA) gp tp t0 t1 t2 s0 (Z_to_bv 64 SPA) a0 a1 a2 a3 a4 a5 a6 a7
               s2 (Z_to_bv 64 2147450880) s4 (Z_to_bv 64 HB) s6 (Z_to_bv 64 tl) s8 s9 (Z_to_bv 64 Bd) s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x8c05c) fc None m (seg_rom asegs)).
Section Sz5.
Variables ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s6 s8 s9 s11 t3 t4 t5 t6 F fc m RNG SPA CUR HB Bd tl btw tlw c0 c1 c2 c3 c4 c5 c7 c8 c9 c10 cj : ltac2:(SecDiet.SzSec.tyM 'rb_cur_seq__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
#[using="Type"] Lemma rb_cur_seq__body : ltac2:(SecDiet.SzSec.bodyP 'rb_cur_seq__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof.
 intros MI FRA HCUR HBH CURUNP CURRNG CURSH RSPA RHB CUR8 SPCUR SPALO CURHI HB0 HBSP BTW TL.
 qfold.
  assert (LJ : length cj = 24%nat) by (destruct HCUR as [[WF _] _]; cbn in WF; tauto).
  pose proof (munch_refl [(CUR, CUR + 24)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  do 2 zstep.   (* [comment removed for export] *)
  replace (Z.land CUR 7) with 0%Z by (rewrite land7_mod; lia).
  zstep. if_false.
  zstep.
  ck0 CURUNP; ck_go.
  zstep.   (* [comment removed for export] *)
  zstep.
  ck0 CURUNP; ck_go.
  do 2 zstep.
  zstep.
  ck0 CURUNP; ck_go.
  zstep. do 2 zstep.
  apply evtF_done. do 3 eexists. exists (skipn 4 (skipn 8 (skipn 8 cj))).
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
  eapply rw_cells_recell; [exact HCUR | cbn; repeat split; try exact Logic.I; rewrite !length_skipn; lia |].
  cbn [cells_bytes cbytes app].
  replace (sx32 (Z_to_bv 64 btw)) with (Z_to_bv 64 (s32 btw)) by (unfold sx32, s32; rewrite unsigned_lit by lia; f_equal; unfold bv_swrap, bv_wrap; cbn; lia).
  rewrite (le4_s32B btw) by lia. reflexivity.
Qed.
End Sz5.
#[using="Type"] Lemma rb_cur_seq : ltac:(let t := eval cbv delta [rb_cur_seq__stmt] in rb_cur_seq__stmt in exact t).
Proof. intros ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s6 s8 s9 s11 t3 t4 t5 t6 F fc m RNG SPA CUR HB Bd tl btw tlw c0 c1 c2 c3 c4 c5 c7 c8 c9 c10 cj. ltac2:(SecDiet.SzSec.closeP 'rb_cur_seq__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
(* [comment removed for export] *)
Ltac fix_sbA := try (lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 ?w)) _) => change (le1 w) with [Z_to_bv 8 (bv_unsigned w)]; mem_after_store end).
Ltac bzstep := zstep; fix_sbA.

(* [comment removed for export] *)
Definition rb_memcpy_seq__stmt : Prop := forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s6 s7 s8 s9 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : mem) (RNG : footprint) (P B alloc Fb V bufsize bB kPB kBF : Z) (jk : list byte),
    mem_inv asegs m ->
    rw_cells asegs m (P + 20) [C4 (Z_to_bv 64 bufsize); C8 (Z_to_bv 64 B)] ->
    rw_cells asegs m (Fb + 32) [C8 (Z_to_bv 64 V)] ->
    rw_cells asegs m B [CB 8 jk] ->
    unpoisoned m B (B + alloc) -> rng RNG B alloc -> rng RNG (shad B) (nshad alloc) -> rng RNG P 680 -> rng RNG Fb 64 ->
    (B mod 16 = 0)%Z -> (8 <= alloc)%Z -> (0 < P)%Z -> (0 < Fb)%Z -> (P + 680 <= 2^47)%Z -> (Fb + 64 <= 2^47)%Z -> (B + alloc <= 2^47)%Z ->
    (B + alloc <= 2147446784 + bB * 140737479966720)%Z -> (17594333495296 * bB <= B)%Z -> (0 <= bB <= 1)%Z -> (6307840 <= B)%Z ->
    (P + 680 <= B + kPB * 18446744073709551616)%Z -> (B + alloc <= P + (1 - kPB) * 18446744073709551616)%Z -> (0 <= kPB <= 1)%Z ->
    (B + alloc <= Fb + kBF * 18446744073709551616)%Z -> (Fb + 64 <= B + (1 - kBF) * 18446744073709551616)%Z -> (0 <= kBF <= 1)%Z ->
    (0 <= V < 2^64)%Z ->
    evtF asegs RNG (fun ms' => exists t0' a1' a2' a3' a4' a5' a6' a7' m',
        ms' = MS (mkR ra sp gp tp t0' t1 t2 s0 s1 (Z_to_bv 64 B) a1' a2' a3' a4' a5' a6' a7'
                      s11 (Z_to_bv 64 2147450880) s2 (Z_to_bv 64 (Fb + 32)) s6 s8 s7 s9 s3 s4 t3 t4 t5 t6)
                 F (Z_to_bv 64 0x8bf30) fc None m' (seg_rom asegs)
        /\ munch [(B, B + 8)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
        /\ rw_cells asegs m' B [CB 8 (le8 (Z_to_bv 64 V))])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (P + 24)) a1 a2 a3 a4 a5 a6 a7
               s11 (Z_to_bv 64 2147450880) s2 (Z_to_bv 64 (Fb + 32)) s6 s8 s7 s9 s3 s4 t3 t4 t5 t6)
          F (Z_to_bv 64 0x8bec4) fc None m (seg_rom asegs)).
Section Sz6.
Variables ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s6 s7 s8 s9 s11 t3 t4 t5 t6 F fc m RNG P B alloc Fb V bufsize bB kPB kBF jk : ltac2:(SecDiet.SzSec.tyM 'rb_memcpy_seq__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
#[using="Type"] Lemma rb_memcpy_seq__body : ltac2:(SecDiet.SzSec.bodyP 'rb_memcpy_seq__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof.
 intros MI HBS HBH HB BUNP BRNG BRSH PRNG FRNG B16 AL8 P0 Fb0 PHI FHI BHI bBhi bBlo bBr bBimg kPBa kPBb kPBr kBF1 kBF2 kBFr HV.
 qfold.
  pose proof (munch_refl [(B, B + 8)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep.
  ck0 BUNP; ck_go.
  zstep.
  ck0 BUNP; ck_go.
  do 6 zstep.
  bzstep.
  do 3 bzstep. zstep. do 4 bzstep.
  zstep.
  apply evtF_done. do 9 eexists.
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
  eapply rw_cells_recell; [exact HB | cbn; repeat split; exact Logic.I |].
  cbn [cells_bytes cbytes app]. unfold le8, word_to_le_bytes. rewrite !unsigned_lit_wrap. rewrite !(Z.mod_small V) by lia.
  cbn [Z_to_le_bytes]. rewrite !Z.shiftr_shiftr by lia. rewrite !Z.shiftr_div_pow2 by lia.
  cbn [Z.add Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul Pos.add]. rewrite ?app_nil_r.
  repeat match goal with |- (_ :: _) = (_ :: _) => f_equal end; try reflexivity; apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit.Z_to_bv8_mod; change (8 + 8)%Z with 16%Z; change (16 + 8)%Z with 24%Z; change (24 + 8)%Z with 32%Z;
    change (32 + 8)%Z with 40%Z; change (40 + 8)%Z with 48%Z; change (48 + 8)%Z with 56%Z; Z.div_mod_to_equations; lia.
Qed.
End Sz6.
#[using="Type"] Lemma rb_memcpy_seq : ltac:(let t := eval cbv delta [rb_memcpy_seq__stmt] in rb_memcpy_seq__stmt in exact t).
Proof. intros ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s6 s7 s8 s9 s11 t3 t4 t5 t6 F fc m RNG P B alloc Fb V bufsize bB kPB kBF jk. ltac2:(SecDiet.SzSec.closeP 'rb_memcpy_seq__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End CANSEC1.
End TwB.
End F_ngblk_segA.

(* [comment removed for export] *)
Module F_sfchk_msegA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep Frame StoreFast.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow StepF SysStepF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg ABase.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require GIA PcapRepA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require SfKitA__A3P. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.SfKitA__A3P.SfKitA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac qfold := try (lazymatch goal with |- evtF ?s ?r ?Q ?st => let QQ := fresh "QQ" in pose (QQ := Q); change Q with QQ end).
Import ListNotations.
Open Scope Z_scope.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= unp_store m a bs n Hn Ha Hl.

(* [comment removed for export] *)
Ltac ck4_split UNP P OK :=
  zstep;
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch type of UNP with unpoisoned mm ?lo ?hi =>
      let b := fresh "shb" in let RD := fresh "RDsh" in let CK := fresh "CKsh" in let SR := fresh "SRsh" in
      destruct (ck_part_rd mm lo hi P 4 UNP ltac:(ck_lia) ltac:(ck_lia) ltac:(lia) ltac:(ck_lia)) as (b & RD & CK);
      ck_fp_at lo P; pose proof (sval_range b) as SR end end;
  zstep; zstep;
  cbv beta delta [mkR];
  lazymatch goal with |- evtF ?segs ?RNGx ?Q (MS ?R ?F ?pc ?fc ?rv ?mm ?ro) =>
    eapply (evtF_cut segs RNGx (fun ms' => ck_post [10%Z; 11%Z] (fun R' => ms' = MS R' F (Z_to_bv 64 OK) fc rv mm ro) R)) end;
  [ ck_arm OK 16%nat
  | let ms' := fresh "ms'" in let H := fresh "Hck" in
    intros ms' H; cbn [ck_post] in H; destruct_exs H; subst ms'; simp_regs; ck_clear ].

Section CANSEC1. Context {rc : runConstT}.
Section MagicSeg.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 s2 s6 s8 s10 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (RNG : footprint).

  Definition magic_load_seq__stmt : Prop := forall (m : mem) (a0 a2 a3 a4 a5 a6 a7 s3 s5 : word) (SPA Fb ERR MG bE mg0 mg1 mg2 mg3 : Z)
      (j1 j2 j3 ecj : list byte) (c32 c56 : word),
    mem_inv asegs m ->
    rw_cells asegs m SPA [CB 32 j1; C8 c32; CB 16 j2; C8 c56; CB 24 j3] ->
    rw_cells asegs m ERR [CB 4 ecj] ->
    rw_cells asegs m MG [C1 (Z_to_bv 8 mg0); C1 (Z_to_bv 8 mg1); C1 (Z_to_bv 8 mg2); C1 (Z_to_bv 8 mg3)] ->
    unpoisoned m ERR (ERR + 4) -> unpoisoned m MG (MG + 4) ->
    rng RNG (shad (ERR - ERR mod 8)) (nshad (4 + ERR mod 8)) -> rng RNG (shad (MG - MG mod 8)) (nshad (4 + MG mod 8)) ->
    rng RNG ERR 4 -> rng RNG MG 4 -> rng RNG SPA 88 ->
    (ERR mod 4 = 0)%Z -> (ERR + 4 <= 2147446784 + bE * 140737479966720)%Z -> (17594333495296 * bE <= ERR)%Z -> (0 <= bE <= 1)%Z -> (6303744 <= ERR)%Z ->
    (6303744 <= MG)%Z -> (MG + 4 <= SPA)%Z -> (ERR + 4 <= SPA)%Z -> (17594333495296 <= SPA)%Z -> (SPA + 88 <= 2^47)%Z ->
    (MG + 4 <= ERR \/ ERR + 4 <= MG)%Z ->
    (0 <= mg0 < 256)%Z -> (0 <= mg1 < 256)%Z -> (0 <= mg2 < 256)%Z -> (0 <= mg3 < 256)%Z ->
    evtF asegs RNG (fun ms' => exists a2' a3' m',
        ms' = MS (mkR ra (Z_to_bv 64 SPA) gp tp t0 t1 t2 s0 (Z_to_bv 64 SPA) (Z_to_bv 64 (-1582154675)) (Z_to_bv 64 (-1582153728)) a2' a3' z64 a5
                      (Z_to_bv 64 (Z.shiftr ERR 3 + 2147450880)) a7 s2 (Z_to_bv 64 1) (Z_to_bv 64 ERR) (Z_to_bv 64 (magic_sx mg0 mg1 mg2 mg3)) s6 (Z_to_bv 64 MG)
                      s8 (Z_to_bv 64 Fb) s10 (Z_to_bv 64 2147450880) t3 t4 t5 t6) F (Z_to_bv 64 0x877d8) fc None m' (seg_rom asegs)
        /\ munch [(SPA, SPA + 88); (ERR, ERR + 4)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
        /\ rw_cells asegs m' SPA [CB 32 j1; C8 c32; CB 16 j2; C8 c56; CB 16 (firstn 16 j3); C8 (Z_to_bv 64 Fb)]
        /\ rw_cells asegs m' ERR [C4 z64]
        /\ rw_cells asegs m' MG [C1 (Z_to_bv 8 mg0); C1 (Z_to_bv 8 mg1); C1 (Z_to_bv 8 mg2); C1 (Z_to_bv 8 mg3)])
      (MS (mkR ra (Z_to_bv 64 SPA) gp tp t0 t1 t2 s0 (Z_to_bv 64 SPA) a0 (Z_to_bv 64 (Z.shiftr ERR 3)) a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 ERR) s5 s6 (Z_to_bv 64 MG)
               s8 (Z_to_bv 64 Fb) s10 (Z_to_bv 64 2147450880) t3 t4 t5 t6) F (Z_to_bv 64 0x87768) fc None m (seg_rom asegs)).
  Section Sz1.
  Variables m a0 a2 a3 a4 a5 a6 a7 s3 s5 SPA Fb ERR MG bE mg0 mg1 mg2 mg3 j1 j2 j3 ecj c32 c56 : ltac2:(SecDiet.SzSec.tyM 'magic_load_seq__stmt "vvvvvvvvvvvvvvvvvvvvvvvvv" @m).
  #[using="Type"] Lemma magic_load_seq__body : ltac2:(SecDiet.SzSec.bodyP 'magic_load_seq__stmt "vvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof.
    intros MI FRA HE MG4 ERUNP MGUNP ERRSH MGRSH ERRNG MGRNG RSP ERR4 bEhi bElo bEr bEimg MGLO MGSP ERSP SPALO SPAHI DME GM0 GM1 GM2 GM3.
    qfold.
    pose proof (munch_refl [(SPA, SPA + 88); (ERR, ERR + 4)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    ck4_split ERUNP ERR 0x87778%Z.
    zstep.
    ck MGUNP 1%Z 0x8778c%Z [10%Z; 11%Z].
    zstep.
    ck MGUNP 1%Z 0x877a0%Z [11%Z; 12%Z].
    do 5 zstep.
    do 9 zstep.
    rewrite (magic_wordA mg0 mg1 mg2 mg3) by lia.
    apply evtF_done. do 3 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
    split; [assumption|]. split; assumption.
  Qed.
  End Sz1.
  #[using="Type"] Lemma magic_load_seq : ltac:(let t := eval cbv delta [magic_load_seq__stmt] in magic_load_seq__stmt in exact t).
  Proof. intros m a0 a2 a3 a4 a5 a6 a7 s3 s5 SPA Fb ERR MG bE mg0 mg1 mg2 mg3 j1 j2 j3 ecj c32 c56. ltac2:(SecDiet.SzSec.closeP 'magic_load_seq__body "vvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  #[using="Type"] Lemma magic_swap_seq : forall (m : mem) (a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s7 s9 s11 : word) (W : Z), (0 <= W < 2^64)%Z ->
    evtF asegs RNG (fun ms' => exists a0' a2' s5',
        ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' (Z_to_bv 64 W) a2' (Z_to_bv 64 18446744072984179361) (Z_to_bv 64 1) a5 a6 a7 s2 s3 s4 s5' s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 0x879ac) fc None m (seg_rom asegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 (Z_to_bv 64 W) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x87970) fc None m (seg_rom asegs)).
  Proof.
    intros until W. intros WR.
    do 15 zstep.
    replace (Z_to_bv 64 (-725372255)) with (Z_to_bv 64 18446744072984179361) by (apply Z_to_bv_eqm; reflexivity).
    apply evtF_done. do 3 eexists. reflexivity.
  Qed.
End MagicSeg.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.StoreFast.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.SfKitA__A3P.SfKitA.TwB.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac qfold := try (lazymatch goal with |- evtF ?s ?r ?Q ?st => let QQ := fresh "QQ" in pose (QQ := Q); change Q with QQ end).
Import ListNotations.
Open Scope Z_scope.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= unp_store m a bs n Hn Ha Hl.

(* [comment removed for export] *)
Ltac ck4_split UNP P OK :=
  zstep; zstep;   (* [comment removed for export] *)
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch type of UNP with unpoisoned mm ?lo ?hi =>
      let b := fresh "shb" in let RD := fresh "RDsh" in let CK := fresh "CKsh" in let SR := fresh "SRsh" in
      destruct (ck_part_rd mm lo hi P 4 UNP ltac:(ck_lia) ltac:(ck_lia) ltac:(lia) ltac:(ck_lia)) as (b & RD & CK);
      ck_fp_at lo P; pose proof (sval_range b) as SR end end;
  zstep;   (* [comment removed for export] *)
  cbv beta delta [mkR];
  lazymatch goal with |- evtF ?segs ?RNGx ?Q (MS ?R ?F ?pc ?fc ?rv ?mm ?ro) =>
    eapply (evtF_cut segs RNGx (fun ms' => ck_post [10%Z; 11%Z] (fun R' => ms' = MS R' F (Z_to_bv 64 OK) fc rv mm ro) R)) end;
  [ ck_arm OK 16%nat
  | let ms' := fresh "ms'" in let H := fresh "Hck" in
    intros ms' H; cbn [ck_post] in H; destruct_exs H; subst ms'; simp_regs; ck_clear ].

Section CANSEC1. Context {rc : runConstT}.
Section MagicSeg.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 s6 s8 s10 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (RNG : footprint).

  (* [comment removed for export] *)
  Definition magic_load_seq__stmt : Prop := forall (m : mem) (a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s9 : word) (SPA ERR MG bE mg0 mg1 mg2 mg3 : Z)
      (j1 j2 j3 ecj : list byte) (c32 c48 c80 : word),
    mem_inv asegs m ->
    rw_cells asegs m SPA [CB 32 j1; C8 c32; CB 8 j2; C8 c48; CB 24 j3; C8 c80] ->
    rw_cells asegs m ERR [CB 4 ecj] ->
    rw_cells asegs m MG [C1 (Z_to_bv 8 mg0); C1 (Z_to_bv 8 mg1); C1 (Z_to_bv 8 mg2); C1 (Z_to_bv 8 mg3)] ->
    unpoisoned m ERR (ERR + 4) -> unpoisoned m MG (MG + 4) ->
    rng RNG (shad (ERR - ERR mod 8)) (nshad (4 + ERR mod 8)) -> rng RNG (shad (MG - MG mod 8)) (nshad (4 + MG mod 8)) ->
    rng RNG ERR 4 -> rng RNG MG 4 -> rng RNG SPA 88 ->
    (ERR mod 4 = 0)%Z -> (ERR + 4 <= 2147446784 + bE * 140737479966720)%Z -> (17594333495296 * bE <= ERR)%Z -> (0 <= bE <= 1)%Z -> (6307840 <= ERR)%Z ->
    (6307840 <= MG)%Z -> (MG + 4 <= SPA)%Z -> (ERR + 4 <= SPA)%Z -> (17594333495296 <= SPA)%Z -> (SPA + 88 <= 2^47)%Z ->
    (MG + 4 <= ERR \/ ERR + 4 <= MG)%Z ->
    (0 <= mg0 < 256)%Z -> (0 <= mg1 < 256)%Z -> (0 <= mg2 < 256)%Z -> (0 <= mg3 < 256)%Z ->
    evtF asegs RNG (fun ms' => exists a2' a3' m',
        ms' = MS (mkR ra (Z_to_bv 64 SPA) gp tp t0 t1 t2 s0 (Z_to_bv 64 SPA) (Z_to_bv 64 (-1582154675)) (Z_to_bv 64 (-1582153728)) a2' a3' z64
                      (Z_to_bv 64 (Z.shiftr ERR 3 + 2147450880)) a6 a7 (Z_to_bv 64 1) s3 s4 (Z_to_bv 64 (magic_sx mg0 mg1 mg2 mg3)) s6 (Z_to_bv 64 MG)
                      s8 s9 s10 (Z_to_bv 64 2147450880) t3 t4 t5 t6) F (Z_to_bv 64 0x87c9c) fc None m' (seg_rom asegs)
        /\ munch [(SPA, SPA + 88); (ERR, ERR + 4)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
        /\ rw_cells asegs m' SPA [CB 32 j1; C8 c32; CB 8 j2; C8 c48; C8 (Z_to_bv 64 ERR); CB 16 (skipn 8 j3); C8 c80]
        /\ rw_cells asegs m' ERR [C4 z64]
        /\ rw_cells asegs m' MG [C1 (Z_to_bv 8 mg0); C1 (Z_to_bv 8 mg1); C1 (Z_to_bv 8 mg2); C1 (Z_to_bv 8 mg3)])
      (MS (mkR ra (Z_to_bv 64 SPA) gp tp t0 t1 t2 s0 (Z_to_bv 64 SPA) a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 ERR) s3 s4 s5 s6 (Z_to_bv 64 MG)
               s8 s9 s10 (Z_to_bv 64 2147450880) t3 t4 t5 t6) F (Z_to_bv 64 0x87c1c) fc None m (seg_rom asegs)).
  Section Sz1.
  Variables m a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s9 SPA ERR MG bE mg0 mg1 mg2 mg3 j1 j2 j3 ecj c32 c48 c80 : ltac2:(SecDiet.SzSec.tyM 'magic_load_seq__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvv" @m).
  #[using="Type"] Lemma magic_load_seq__body : ltac2:(SecDiet.SzSec.bodyP 'magic_load_seq__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof.
 intros MI FRA HE MG4 ERUNP MGUNP ERRSH MGRSH ERRNG MGRNG RSP ERR4 bEhi bElo bEr bEimg MGLO MGSP ERSP SPALO SPAHI DME GM0 GM1 GM2 GM3.
 qfold.
    pose proof (munch_refl [(SPA, SPA + 88); (ERR, ERR + 4)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    (* [comment removed for export] *)
    assert (XX : (0 < ERR < 2 ^ 64)%Z) by lia.
    zstep. if_false_by (eqz_false ERR XX).
    zstep. replace (Z.land ERR 3) with 0%Z by (change 3%Z with (Z.ones 2); rewrite Z.land_ones by lia; exact (eq_sym ERR4)).
    zstep. if_false.
    ck4_split ERUNP ERR 0x87c38%Z.
    zstep.
    ck MGUNP 1%Z 0x87c4c%Z [10%Z; 11%Z].
    zstep.   (* [comment removed for export] *)
    zstep.
    ck MGUNP 1%Z 0x87c64%Z [11%Z; 12%Z].
    do 5 zstep.
    do 9 zstep.
    rewrite (magic_wordA mg0 mg1 mg2 mg3) by lia.
    apply evtF_done. do 3 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
    split; [assumption|]. split; assumption.
  Qed.
  End Sz1.
  #[using="Type"] Lemma magic_load_seq : ltac:(let t := eval cbv delta [magic_load_seq__stmt] in magic_load_seq__stmt in exact t).
  Proof. intros m a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s9 SPA ERR MG bE mg0 mg1 mg2 mg3 j1 j2 j3 ecj c32 c48 c80. ltac2:(SecDiet.SzSec.closeP 'magic_load_seq__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  #[using="Type"] Lemma magic_swap_seq : forall (m : mem) (a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s7 s9 s11 : word) (W : Z), (0 <= W < 2^64)%Z ->
    evtF asegs RNG (fun ms' => exists a0' a2' s5',
        ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' (Z_to_bv 64 W) a2' (Z_to_bv 64 18446744072984179361) (Z_to_bv 64 1) a5 a6 a7 s2 s3 s4 s5' s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 0x87e80) fc None m (seg_rom asegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 (Z_to_bv 64 W) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x87e44) fc None m (seg_rom asegs)).
  Proof.
    intros until W. intros WR.
    do 15 zstep.
    replace (Z_to_bv 64 (-725372255)) with (Z_to_bv 64 18446744072984179361) by (apply Z_to_bv_eqm; reflexivity).
    apply evtF_done. do 3 eexists. reflexivity.
  Qed.
End MagicSeg.
End CANSEC1.
End TwB.
End F_sfchk_msegA.

(* [comment removed for export] *)
Module F_ngchk_hsegA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep Frame StoreFast.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow StepF SysStepF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg ABase.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require GIA PcapRepA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require SfKitA__A3P. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.SfKitA__A3P.SfKitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LeafA__A3P.F_sfchk_msegA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac qfold := try (lazymatch goal with |- evtF ?s ?r ?Q ?st => let QQ := fresh "QQ" in pose (QQ := Q); change Q with QQ end).
Import ListNotations.
Open Scope Z_scope.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= unp_store m a bs n Hn Ha Hl.

Section CANSEC1. Context {rc : runConstT}.
Section NgcMagicSeg.
  Variables (ra sp gp tp t0 t1 t2 s0 s6 s7 s8 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (RNG : footprint).

  Definition ngc_magic_seq__stmt : Prop := forall (m : mem) (a0 a1 a2 a3 a4 a5 a6 a7 : word) (SPA Fb ERR MG bE mg0 mg1 mg2 mg3 : Z)
      (j1 ecj : list byte),
    mem_inv asegs m ->
    rw_cells asegs m SPA [CB 152 j1] ->
    rw_cells asegs m ERR [CB 4 ecj] ->
    rw_cells asegs m MG [C1 (Z_to_bv 8 mg0); C1 (Z_to_bv 8 mg1); C1 (Z_to_bv 8 mg2); C1 (Z_to_bv 8 mg3)] ->
    unpoisoned m ERR (ERR + 4) -> unpoisoned m MG (MG + 4) ->
    rng RNG (shad (ERR - ERR mod 8)) (nshad (4 + ERR mod 8)) -> rng RNG (shad (MG - MG mod 8)) (nshad (4 + MG mod 8)) ->
    rng RNG ERR 4 -> rng RNG MG 4 -> rng RNG SPA 152 ->
    (ERR mod 4 = 0)%Z -> (ERR + 4 <= 2147446784 + bE * 140737479966720)%Z -> (17594333495296 * bE <= ERR)%Z -> (0 <= bE <= 1)%Z -> (6303744 <= ERR)%Z ->
    (6303744 <= MG)%Z -> (MG + 4 <= SPA)%Z -> (ERR + 4 <= SPA)%Z -> (17594333495296 <= SPA)%Z -> (SPA + 152 <= 2^47)%Z ->
    (MG + 4 <= ERR \/ ERR + 4 <= MG)%Z ->
    (0 <= mg0 < 256)%Z -> (0 <= mg1 < 256)%Z -> (0 <= mg2 < 256)%Z -> (0 <= mg3 < 256)%Z ->
    evtF asegs RNG (fun ms' => exists a2' a3' m',
        ms' = MS (mkR ra (Z_to_bv 64 SPA) gp tp t0 t1 t2 s0 (Z_to_bv 64 SPA) (Z_to_bv 64 (magic_sx mg0 mg1 mg2 mg3)) (Z_to_bv 64 168627466) a2' a3' a4 a5 a6 a7
                      (Z_to_bv 64 Fb) (Z_to_bv 64 ERR) (Z_to_bv 64 (Z.shiftr ERR 3 + 2147450880)) (Z_to_bv 64 MG) s6 s7 s8
                      (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 2147450880) s11 t3 t4 t5 t6) F (Z_to_bv 64 0x8ae68) fc None m' (seg_rom asegs)
        /\ munch [(SPA, SPA + 152); (ERR, ERR + 4)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
        /\ rw_cells asegs m' SPA [CB 120 (firstn 120 j1); C8 (Z_to_bv 64 Fb); CB 24 (skipn 128 j1)]
        /\ rw_cells asegs m' ERR [C4 z64]
        /\ rw_cells asegs m' MG [C1 (Z_to_bv 8 mg0); C1 (Z_to_bv 8 mg1); C1 (Z_to_bv 8 mg2); C1 (Z_to_bv 8 mg3)])
      (MS (mkR ra (Z_to_bv 64 SPA) gp tp t0 t1 t2 s0 (Z_to_bv 64 SPA) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 Fb) (Z_to_bv 64 ERR) (Z_to_bv 64 (Z.shiftr ERR 3)) (Z_to_bv 64 MG) s6 s7 s8
               (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 2147450880) s11 t3 t4 t5 t6) F (Z_to_bv 64 0x8ae00) fc None m (seg_rom asegs)).
  Section Sz1.
  Variables m a0 a1 a2 a3 a4 a5 a6 a7 SPA Fb ERR MG bE mg0 mg1 mg2 mg3 j1 ecj : ltac2:(SecDiet.SzSec.tyM 'ngc_magic_seq__stmt "vvvvvvvvvvvvvvvvvvvv" @m).
  #[using="Type"] Lemma ngc_magic_seq__body : ltac2:(SecDiet.SzSec.bodyP 'ngc_magic_seq__stmt "vvvvvvvvvvvvvvvvvvvv").
  Proof.
 intros MI FRA HE MG4 ERUNP MGUNP ERRSH MGRSH ERRNG MGRNG RSP ERR4 bEhi bElo bEr bEimg MGLO MGSP ERSP SPALO SPAHI DME GM0 GM1 GM2 GM3.
 qfold.
    pose proof (munch_refl [(SPA, SPA + 152); (ERR, ERR + 4)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    ck4_split ERUNP ERR 0x8ae10%Z.
  zstep.
  ck MGUNP 1%Z 0x8ae24%Z [10%Z; 11%Z].
  zstep.
  ck MGUNP 1%Z 0x8ae38%Z [11%Z; 12%Z].
  do 4 zstep.
  do 8 zstep.
  rewrite (magic_wordA mg0 mg1 mg2 mg3) by lia.
  apply evtF_done. do 3 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
  split; [assumption|]. split; assumption.
  Qed.
  End Sz1.
  #[using="Type"] Lemma ngc_magic_seq : ltac:(let t := eval cbv delta [ngc_magic_seq__stmt] in ngc_magic_seq__stmt in exact t).
  Proof. intros m a0 a1 a2 a3 a4 a5 a6 a7 SPA Fb ERR MG bE mg0 mg1 mg2 mg3 j1 ecj. ltac2:(SecDiet.SzSec.closeP 'ngc_magic_seq__body "vvvvvvvvvvvvvvvvvvvv"). Qed.
End NgcMagicSeg.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.StoreFast.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.SfKitA__A3P.SfKitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LeafA__A3P.F_sfchk_msegA.TwB. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac qfold := try (lazymatch goal with |- evtF ?s ?r ?Q ?st => let QQ := fresh "QQ" in pose (QQ := Q); change Q with QQ end).
Import ListNotations.
Open Scope Z_scope.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= unp_store m a bs n Hn Ha Hl.

Section CANSEC1. Context {rc : runConstT}.
Section NgcMagicSeg.
  Variables (ra sp gp tp t0 t1 t2 s0 s4 s5 s7 s8 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (RNG : footprint).

  #[using="Type"] Lemma ngc_magic_seq : forall (m : mem) (a0 a1 a2 a3 a4 a5 a6 a7 : word) (SPA Fb ERR MG bE mg0 mg1 mg2 mg3 : Z)
      (ecj : list byte),
    mem_inv asegs m ->
    rw_cells asegs m ERR [CB 4 ecj] ->
    rw_cells asegs m MG [C1 (Z_to_bv 8 mg0); C1 (Z_to_bv 8 mg1); C1 (Z_to_bv 8 mg2); C1 (Z_to_bv 8 mg3)] ->
    unpoisoned m ERR (ERR + 4) -> unpoisoned m MG (MG + 4) ->
    rng RNG (shad (ERR - ERR mod 8)) (nshad (4 + ERR mod 8)) -> rng RNG (shad (MG - MG mod 8)) (nshad (4 + MG mod 8)) ->
    rng RNG ERR 4 -> rng RNG MG 4 ->
    (ERR mod 4 = 0)%Z -> (ERR + 4 <= 2147446784 + bE * 140737479966720)%Z -> (17594333495296 * bE <= ERR)%Z -> (0 <= bE <= 1)%Z -> (6307840 <= ERR)%Z ->
    (6307840 <= MG)%Z -> (MG + 4 <= SPA)%Z -> (ERR + 4 <= SPA)%Z -> (17594333495296 <= SPA)%Z -> (SPA + 152 <= 2^47)%Z ->
    (MG + 4 <= ERR \/ ERR + 4 <= MG)%Z ->
    (0 <= mg0 < 256)%Z -> (0 <= mg1 < 256)%Z -> (0 <= mg2 < 256)%Z -> (0 <= mg3 < 256)%Z ->
    evtF asegs RNG (fun ms' => exists a2' a3' m',
        ms' = MS (mkR ra (Z_to_bv 64 SPA) gp tp t0 t1 t2 s0 (Z_to_bv 64 SPA) (Z_to_bv 64 (magic_sx mg0 mg1 mg2 mg3)) (Z_to_bv 64 168627466) a2' a3' a4 a5 a6 a7
                      (Z_to_bv 64 Fb) (Z_to_bv 64 ERR) (Z_to_bv 64 (Z.shiftr ERR 3 + 2147450880)) s5 (Z_to_bv 64 MG) s7 s8
                      (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 2147450880) s11 t3 t4 t5 t6) F (Z_to_bv 64 0x8adb0) fc None m' (seg_rom asegs)
        /\ munch [(ERR, ERR + 4)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'      (* [comment removed for export] *)
        /\ rw_cells asegs m' ERR [C4 z64]
        /\ rw_cells asegs m' MG [C1 (Z_to_bv 8 mg0); C1 (Z_to_bv 8 mg1); C1 (Z_to_bv 8 mg2); C1 (Z_to_bv 8 mg3)])
      (MS (mkR ra (Z_to_bv 64 SPA) gp tp t0 t1 t2 s0 (Z_to_bv 64 SPA) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 Fb) (Z_to_bv 64 ERR) s4 s5 (Z_to_bv 64 MG) s7 s8
               (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 2147450880) s11 t3 t4 t5 t6) F (Z_to_bv 64 0x8ad48) fc None m (seg_rom asegs)).      (* [comment removed for export] *)
  Proof.
    intros until ecj. intros MI HE MG4 ERUNP MGUNP ERRSH MGRSH ERRNG MGRNG ERR4 bEhi bElo bEr bEimg MGLO MGSP ERSP SPALO SPAHI DME GM0 GM1 GM2 GM3.
    pose proof (munch_refl [(ERR, ERR + 4)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    ck4_split ERUNP ERR 0x8ad58%Z.
  zstep.
  ck MGUNP 1%Z 0x8ad6c%Z [10%Z; 11%Z].
  zstep.
  ck MGUNP 1%Z 0x8ad80%Z [11%Z; 12%Z].
  do 4 zstep.
  do 8 zstep.
  rewrite (magic_wordA mg0 mg1 mg2 mg3) by lia.
  apply evtF_done. do 3 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
  split; assumption.
  Qed.
End NgcMagicSeg.
End CANSEC1.
End TwB.
End F_ngchk_hsegA.

(* [comment removed for export] *)
Module F_sfchk_swapA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep Frame StoreFast.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow StepF SysStepF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg ABase.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require GIA PcapRepA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require SfKitA__A3P. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.SfKitA__A3P.SfKitA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac qfold := try (lazymatch goal with |- evtF ?s ?r ?Q ?st => let QQ := fresh "QQ" in pose (QQ := Q); change Q with QQ end).
Import ListNotations.
Open Scope Z_scope.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mem_after_store ::= mem_after_store_fast.

Section CANSEC1. Context {rc : runConstT}.
Definition swap_blockA__stmt : Prop := forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : mem) (RNG : footprint) (HB : Z) (g0 g1 g2 g3 e0 e1 e2 e3 h0 h1 h2 h3 : Z) (mid : list byte),
    mem_inv asegs m -> (0 <= HB)%Z -> (HB + 24 < 2^64)%Z -> rng RNG HB 24 ->
    (0 <= g0 < 256)%Z -> (0 <= g1 < 256)%Z -> (0 <= g2 < 256)%Z -> (0 <= g3 < 256)%Z ->
    (0 <= e0 < 256)%Z -> (0 <= e1 < 256)%Z -> (0 <= e2 < 256)%Z -> (0 <= e3 < 256)%Z ->
    (0 <= h0 < 256)%Z -> (0 <= h1 < 256)%Z -> (0 <= h2 < 256)%Z -> (0 <= h3 < 256)%Z ->
    rw_cells asegs m (HB + 4)
      [C2 (Z_to_bv 64 (g0 + 256 * g1)); C2 (Z_to_bv 64 (g2 + 256 * g3)); CB 8 mid; C4 (Z_to_bv 64 (le4val e0 e1 e2 e3)); C4 (Z_to_bv 64 (le4val h0 h1 h2 h3))] ->
    evtF asegs RNG (fun ms' => exists a0' a1' a2' a3' a4' a5' a6' a7' m',
        ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 (Z_to_bv 64 HB) s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 0x878b4) fc None m' (seg_rom asegs)
        /\ munch [(HB + 4, HB + 24)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
        /\ rw_cells asegs m' (HB + 4)
             [C2 (Z_to_bv 64 (g1 + 256 * g0)); C2 (Z_to_bv 64 (g3 + 256 * g2)); CB 8 mid; C4 (Z_to_bv 64 (le4val e3 e2 e1 e0)); C4 (Z_to_bv 64 (le4val h3 h2 h1 h0))])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 (Z_to_bv 64 HB) s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x8782c) fc None m (seg_rom asegs)).
Section Sz1.
Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 F fc m RNG HB g0 g1 g2 g3 e0 e1 e2 e3 h0 h1 h2 h3 mid : ltac2:(SecDiet.SzSec.tyM 'swap_blockA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
#[using="Type"] Lemma swap_blockA__body : ltac2:(SecDiet.SzSec.bodyP 'swap_blockA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof.
  intros MI HB0 HBT RH B0 B1 B2 B3 B4 B5 B6 B7 B8 B9 B10 B11 FR.
  qfold.
  pose proof (munch_refl [(HB + 4, HB + 24)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  do 34 zstep.
  apply evtF_done. do 9 eexists.
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
  assert (LM : length mid = 8%nat) by (destruct FR as [[WF _] _]; cbn in WF; tauto).
  eapply rw_cells_recell; [exact FR | cbn; repeat split; try exact Logic.I; exact LM |].
  cbn [cells_bytes cbytes app].
  rewrite (le2_lit g1 g0), (le2_lit g3 g2), (le4_lit e3 e2 e1 e0), (le4_lit h3 h2 h1 h0) by lia.
  rewrite (le2_of_val _ g1 g0 g1); [| lia | lia | lia | apply (swap16_valA _ g0 g1); [lia|lia| apply unsigned_zx16; lia]].
  rewrite (le2_of_val _ g3 g2 g3); [| lia | lia | lia | apply (swap16_valA _ g2 g3); [lia|lia| apply unsigned_zx16; lia]].
  rewrite (le4_of_val _ e3 e2 e1 e0 (e1 + 256 * e2 + 65536 * e3 + 16777216 * (((e3 / 128) * 4294967295) mod 256)));
    [| lia | lia | lia | lia | Z.div_mod_to_equations; lia
     | apply (swap32_valA _ e0 e1 e2 e3); [lia|lia|lia|lia| Z.div_mod_to_equations; lia | rewrite unsigned_sx32 by lia; unfold sxv, le4val; lia]].
  rewrite (le4_of_val _ h3 h2 h1 h0 (h1 + 256 * h2 + 65536 * h3 + 16777216 * (((h3 / 128) * 4294967295) mod 256)));
    [| lia | lia | lia | lia | Z.div_mod_to_equations; lia
     | apply (swap32_valA _ h0 h1 h2 h3); [lia|lia|lia|lia| Z.div_mod_to_equations; lia | rewrite unsigned_sx32 by lia; unfold sxv, le4val; lia]].
  reflexivity.
Qed.
End Sz1.
#[using="Type"] Lemma swap_blockA : ltac:(let t := eval cbv delta [swap_blockA__stmt] in swap_blockA__stmt in exact t).
Proof. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 F fc m RNG HB g0 g1 g2 g3 e0 e1 e2 e3 h0 h1 h2 h3 mid. ltac2:(SecDiet.SzSec.closeP 'swap_blockA__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.StoreFast.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.SfKitA__A3P.SfKitA.TwB.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac qfold := try (lazymatch goal with |- evtF ?s ?r ?Q ?st => let QQ := fresh "QQ" in pose (QQ := Q); change Q with QQ end).
Import ListNotations.
Open Scope Z_scope.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mem_after_store ::= mem_after_store_fast.

Section CANSEC1. Context {rc : runConstT}.
Definition swap_blockA__stmt : Prop := forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : mem) (RNG : footprint) (HB : Z) (g0 g1 g2 g3 e0 e1 e2 e3 h0 h1 h2 h3 : Z) (mid : list byte),
    mem_inv asegs m -> (0 <= HB)%Z -> (HB + 24 < 2^64)%Z -> rng RNG HB 24 ->
    (0 <= g0 < 256)%Z -> (0 <= g1 < 256)%Z -> (0 <= g2 < 256)%Z -> (0 <= g3 < 256)%Z ->
    (0 <= e0 < 256)%Z -> (0 <= e1 < 256)%Z -> (0 <= e2 < 256)%Z -> (0 <= e3 < 256)%Z ->
    (0 <= h0 < 256)%Z -> (0 <= h1 < 256)%Z -> (0 <= h2 < 256)%Z -> (0 <= h3 < 256)%Z ->
    rw_cells asegs m (HB + 4)
      [C2 (Z_to_bv 64 (g0 + 256 * g1)); C2 (Z_to_bv 64 (g2 + 256 * g3)); CB 8 mid; C4 (Z_to_bv 64 (le4val e0 e1 e2 e3)); C4 (Z_to_bv 64 (le4val h0 h1 h2 h3))] ->
    evtF asegs RNG (fun ms' => exists a0' a1' a2' a3' a4' a5' a6' a7' m',
        ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 (Z_to_bv 64 HB) s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 0x87d78) fc None m' (seg_rom asegs)
        /\ munch [(HB + 4, HB + 24)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
        /\ rw_cells asegs m' (HB + 4)
             [C2 (Z_to_bv 64 (g1 + 256 * g0)); C2 (Z_to_bv 64 (g3 + 256 * g2)); CB 8 mid; C4 (Z_to_bv 64 (le4val e3 e2 e1 e0)); C4 (Z_to_bv 64 (le4val h3 h2 h1 h0))])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 (Z_to_bv 64 HB) s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x87cf0) fc None m (seg_rom asegs)).
Section Sz1.
Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 F fc m RNG HB g0 g1 g2 g3 e0 e1 e2 e3 h0 h1 h2 h3 mid : ltac2:(SecDiet.SzSec.tyM 'swap_blockA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
#[using="Type"] Lemma swap_blockA__body : ltac2:(SecDiet.SzSec.bodyP 'swap_blockA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof.
 intros MI HB0 HBT RH B0 B1 B2 B3 B4 B5 B6 B7 B8 B9 B10 B11 FR.
 qfold.
  pose proof (munch_refl [(HB + 4, HB + 24)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  do 34 zstep.
  apply evtF_done. do 9 eexists.
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
  assert (LM : length mid = 8%nat) by (destruct FR as [[WF _] _]; cbn in WF; tauto).
  eapply rw_cells_recell; [exact FR | cbn; repeat split; try exact Logic.I; exact LM |].
  cbn [cells_bytes cbytes app].
  rewrite (le2_lit g1 g0), (le2_lit g3 g2), (le4_lit e3 e2 e1 e0), (le4_lit h3 h2 h1 h0) by lia.
  rewrite (le2_of_val _ g1 g0 g1); [| lia | lia | lia | apply (swap16_valA _ g0 g1); [lia|lia| apply unsigned_zx16; lia]].
  rewrite (le2_of_val _ g3 g2 g3); [| lia | lia | lia | apply (swap16_valA _ g2 g3); [lia|lia| apply unsigned_zx16; lia]].
  rewrite (le4_of_val _ e3 e2 e1 e0 (e1 + 256 * e2 + 65536 * e3 + 16777216 * (((e3 / 128) * 4294967295) mod 256)));
    [| lia | lia | lia | lia | Z.div_mod_to_equations; lia
     | apply (swap32_valA _ e0 e1 e2 e3); [lia|lia|lia|lia| Z.div_mod_to_equations; lia | rewrite unsigned_sx32 by lia; unfold sxv, le4val; lia]].
  rewrite (le4_of_val _ h3 h2 h1 h0 (h1 + 256 * h2 + 65536 * h3 + 16777216 * (((h3 / 128) * 4294967295) mod 256)));
    [| lia | lia | lia | lia | Z.div_mod_to_equations; lia
     | apply (swap32_valA _ h0 h1 h2 h3); [lia|lia|lia|lia| Z.div_mod_to_equations; lia | rewrite unsigned_sx32 by lia; unfold sxv, le4val; lia]].
  reflexivity.
Qed.
End Sz1.
#[using="Type"] Lemma swap_blockA : ltac:(let t := eval cbv delta [swap_blockA__stmt] in swap_blockA__stmt in exact t).
Proof. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 F fc m RNG HB g0 g1 g2 g3 e0 e1 e2 e3 h0 h1 h2 h3 mid. ltac2:(SecDiet.SzSec.closeP 'swap_blockA__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End CANSEC1.
End TwB.
End F_sfchk_swapA.

(* [comment removed for export] *)
Module F_sfchk_fsegA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep Frame StoreFast.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim PcapPrelim PcapTypes PcapPure Pcap.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow StepF SysStepF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg ABase.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require GIA PcapRepA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require SfKitA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require SfHandleA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.SfKitA__A3P.SfKitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.SfKitA__A3P.SfKitB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.SfHandleA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac qfold := try (lazymatch goal with |- evtF ?s ?r ?Q ?st => let QQ := fresh "QQ" in pose (QQ := Q); change Q with QQ end).
(* [comment removed for export] *)
Local Ltac qnorm := try change (2^64 - 2^32)%Z with 18446744069414584320%Z.
Import ListNotations.
Open Scope Z_scope.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= unp_store m a bs n Hn Ha Hl.
Local Ltac sl_store_extra m m' a bs n Hn Ha Hl CH ::= sl_store_extra_std m m' a bs n Hn Ha Hl CH.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition pblk_ok (RNG : footprint) (SPA P Fb bP kPF : Z) : Prop :=
  rng RNG P 664 /\ rng RNG (shad P) (nshad 664) /\ rng RNG SPA 88 /\ rng RNG Fb 128 /\ rng_aimg RNG
  /\ (P mod 16 = 0)%Z /\ (0 <= bP <= 1)%Z /\ (P + 664 <= 2147446784 + bP * 140737479966720)%Z /\ (17594333495296 * bP <= P)%Z /\ (6303744 <= P)%Z
  /\ (P + 664 <= SPA)%Z /\ (Fb + 128 <= SPA)%Z /\ (0 < Fb)%Z /\ (SPA + 88 <= 2^47)%Z /\ (17594333495296 <= SPA)%Z
  /\ (0 <= kPF <= 1)%Z /\ (P + 664 <= Fb + kPF * 18446744073709551616)%Z /\ (Fb + 128 <= P + (1 - kPF) * 18446744073709551616)%Z.
Definition hdrf_ok (mi maj min n0 n1 n2 n3 l0 l1 l2 l3 : Z) : Prop :=
  (2^31 <= mi < 2^32)%Z /\ (0 <= maj < 2^16)%Z /\ (0 <= min < 2^16)%Z
  /\ (0 <= n0 < 256)%Z /\ (0 <= n1 < 256)%Z /\ (0 <= n2 < 256)%Z /\ (0 <= n3 < 256)%Z
  /\ (0 <= l0 < 256)%Z /\ (0 <= l1 < 256)%Z /\ (0 <= l2 < 256)%Z /\ (0 <= l3 < 256)%Z /\ l2 = 0%Z /\ (l3 mod 4 = 0)%Z.

Section CANSEC1. Context {rc : runConstT}.
Section FillSeg.
  Variables (ra sp gp tp t0 t1 t2 s0 s3 s8 s9 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (RNG : footprint) (SPA P Fb EB ERR : Z) (bP kPF : Z).
  (* [comment removed for export] *)
  Variables (mi maj min n0 n1 n2 n3 l0 l1 l2 l3 : Z) (sw : bool) (j1 j3 pre mid post : list byte) (k0 k1 k2 flagw : word).
  (* [comment removed for export] *)
  Hypothesis PBK : pblk_ok RNG SPA P Fb bP kPF.
  Hypothesis HOK : hdrf_ok mi maj min n0 n1 n2 n3 l0 l1 l2 l3.
  (* [comment removed for export] *)
  Local Notation MW := (mi + (2^64 - 2^32))%Z.
  (* [comment removed for export] *)
  Local Notation FRAME := [C8 k0; C8 k1; C8 k2; CB 8 pre; C4 (Z_to_bv 64 MW); C2 (Z_to_bv 64 maj); C2 (Z_to_bv 64 min); CB 8 mid;
                           C4 (Z_to_bv 64 (le4val n0 n1 n2 n3)); C4 (Z_to_bv 64 (le4val l0 l1 l2 l3)); CB 64 post; C8 flagw].
  Local Notation REGS xra xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs4 xs6 :=
    (mkR xra (Z_to_bv 64 SPA) gp tp t0 t1 t2 s0 (Z_to_bv 64 SPA) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
         xs2 s3 xs4 (Z_to_bv 64 MW) xs6 (Z_to_bv 64 (Fb + 32)) s8 s9 (Z_to_bv 64 maj) (Z_to_bv 64 2147450880) t3 t4 t5 t6).
  (* [comment removed for export] *)
  Local Notation SPILL0 := [CB 24 j1; C8 (Z_to_bv 64 (Z.b2z sw)); C8 z64; C8 (Z_to_bv 64 (Z.shiftr ERR 3 + 2147450880));
                            C8 (Z_to_bv 64 Fb); C8 (Z_to_bv 64 EB); CB 16 j3; C8 (Z_to_bv 64 Fb)].
  Local Notation SPILL1 := [CB 8 (firstn 8 j1); C8 (Z_to_bv 64 (Z.shiftr (P + 100) 3 + 2147450880)); C8 (Z_to_bv 64 (P + 100)); C8 (Z_to_bv 64 P);
                            C8 z64; C8 (Z_to_bv 64 (Z.shiftr ERR 3 + 2147450880)); C8 (Z_to_bv 64 Fb); C8 (Z_to_bv 64 EB); CB 16 j3; C8 (Z_to_bv 64 Fb)].
  Local Notation B8 := (C8 (Z_to_bv 64 0)).
  Local Notation B4 := (C4 (Z_to_bv 64 0)).

  (* [comment removed for export] *)
  Definition fill_seg1__stmt : Prop := forall (m : mem) (a1 a2 a3 a4 a5 a6 a7 s2 s4 : word),
    mem_inv asegs m -> unpoisoned m P (P + 664) ->
    rw_cells asegs m SPA SPILL0 -> rw_cells asegs m Fb FRAME -> rw_cells asegs m P (blank_cells P) ->
    evtF asegs RNG (fun ms' => exists a1' a2' a3' m',
        ms' = MS (REGS (Z_to_bv 64 0x87bb8) (Z_to_bv 64 (l0 + 256 * l1)) a1' a2' a3' a4 a5 a6 a7 (Z_to_bv 64 P) (Z_to_bv 64 min) (Z_to_bv 64 (sxv l0 l1 l2 l3)))
                 F (Z_to_bv 64 LINKTYPE_TO_DLT_ENTRY) fc None m' (seg_rom asegs)
        /\ munch [(P, P + 664)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
        /\ rw_cells asegs m' P (pcells P sw maj min 0 0 B8 B4 B8 B4 B8 B8 B4 B4))
      (MS (REGS ra (Z_to_bv 64 P) a1 a2 a3 a4 a5 a6 a7 s2 s4 (Z_to_bv 64 (sxv l0 l1 l2 l3))) F (Z_to_bv 64 0x87b50) fc None m (seg_rom asegs)).
  Section Sz1.
  Variables m a1 a2 a3 a4 a5 a6 a7 s2 s4 : ltac2:(SecDiet.SzSec.tyM 'fill_seg1__stmt "vvvvvvvvvv" @m).
  #[using="bP kPF PBK HOK"] Lemma fill_seg1__body : ltac2:(SecDiet.SzSec.bodyP 'fill_seg1__stmt "vvvvvvvvvv").
  Proof.
    intros MI PUNP FRA FRC CELLS.
    qnorm.
    qfold.
    (pose proof PBK as ndP__; nd_pre ndP__ 18%nat; intros PRNG PRSH RSP RFR RIMG P16 bPr bPhi bPlo bPimg PSP FSP Fb0 SPAHI SPALO kPFr kPF1 kPF2; nd_post).
    (pose proof HOK as ndP__; nd_pre ndP__ 13%nat; intros MIB Bmaj Bmin N0 N1 N2 N3 L0 L1 L2 L3 Z2 Z3; nd_post).
    pose proof (munch_refl [(P, P + 664)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    unfold blank_cells, PCAP_PRIV_OFF in CELLS.
    zstep. ck0 PUNP; ck_go.
    do 2 zstep.
    zstep. ck0 PUNP; ck_go.
    zstep.
    zstep. ck0 PUNP; ck_go.
    rewrite ?zx16_lit by lia.
    zstep.
    do 4 zstep.
    zstep.
    rewrite (lt16_wordA l0 l1 l2 l3) by lia.
    apply evtF_done. do 4 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
    unfold pcells. exact CELLS.
  Qed.
  End Sz1.
  #[using="bP kPF PBK HOK"] Lemma fill_seg1 : ltac:(let t := eval cbv delta [fill_seg1__stmt] in fill_seg1__stmt in exact t).
  Proof. intros m a1 a2 a3 a4 a5 a6 a7 s2 s4. ltac2:(SecDiet.SzSec.closeP 'fill_seg1__body "vvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition fill_seg2__stmt : Prop := forall (m : mem) (a1 a2 a3 a4 a5 a6 a7 : word) (lt : Z),
    mem_inv asegs m -> unpoisoned m P (P + 664) ->
    rw_cells asegs m SPA SPILL0 -> rw_cells asegs m Fb FRAME -> rw_cells asegs m P (pcells P sw maj min 0 0 B8 B4 B8 B4 B8 B8 B4 B4) ->
    evtF asegs RNG (fun ms' => exists a2' a3' m',
        ms' = MS (REGS (Z_to_bv 64 0x87c0c) (Z_to_bv 64 lt) (Z_to_bv 64 (s32 (le4val n0 n1 n2 n3))) a2' a3' a4 a5 a6 a7 (Z_to_bv 64 P) (Z_to_bv 64 min) (Z_to_bv 64 (sxv l0 l1 l2 l3)))
                 F (Z_to_bv 64 PCAP_ADJUST_SNAPSHOT_ENTRY) fc None m' (seg_rom asegs)
        /\ munch [(SPA, SPA + 88); (P, P + 664)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
        /\ rw_cells asegs m' SPA SPILL1
        /\ rw_cells asegs m' P (pcells P sw maj min lt (s32 (Z.land (le4val l0 l1 l2 l3) 4294901760)) B8 B4 B8 B4 B8 B8 B4 B4))
      (MS (REGS (Z_to_bv 64 0x87bb8) (Z_to_bv 64 lt) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 P) (Z_to_bv 64 min) (Z_to_bv 64 (sxv l0 l1 l2 l3)))
          F (Z_to_bv 64 0x87bb8) fc None m (seg_rom asegs)).
  Section Sz2.
  Variables m a1 a2 a3 a4 a5 a6 a7 lt : ltac2:(SecDiet.SzSec.tyM 'fill_seg2__stmt "vvvvvvvvv" @m).
  #[using="bP kPF PBK HOK"] Lemma fill_seg2__body : ltac2:(SecDiet.SzSec.bodyP 'fill_seg2__stmt "vvvvvvvvv").
  Proof.
    intros MI PUNP FRA FRC CELLS.
    qnorm.
    qfold.
    (pose proof PBK as ndP__; nd_pre ndP__ 18%nat; intros PRNG PRSH RSP RFR RIMG P16 bPr bPhi bPlo bPimg PSP FSP Fb0 SPAHI SPALO kPFr kPF1 kPF2; nd_post).
    (pose proof HOK as ndP__; nd_pre ndP__ 13%nat; intros MIB Bmaj Bmin N0 N1 N2 N3 L0 L1 L2 L3 Z2 Z3; nd_post).
    pose proof (munch_refl [(SPA, SPA + 88); (P, P + 664)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    unfold pcells in CELLS.
    zstep.
    do 4 zstep. ck0_at PUNP (P + 100)%Z; ck_go.
    do 3 zstep.
    zstep. ck0 PUNP; ck_go.
    do 5 zstep.
    zstep.
    rewrite (ltext_wordA l0 l1 l2 l3) in * by assumption.
    rewrite (sx32_s32 (le4val n0 n1 n2 n3)) by (unfold le4val; lia).
    apply evtF_done. do 3 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
    split; [exact FRA|]. unfold pcells. exact CELLS.
  Qed.
  End Sz2.
  #[using="bP kPF PBK HOK"] Lemma fill_seg2 : ltac:(let t := eval cbv delta [fill_seg2__stmt] in fill_seg2__stmt in exact t).
  Proof. intros m a1 a2 a3 a4 a5 a6 a7 lt. ltac2:(SecDiet.SzSec.closeP 'fill_seg2__body "vvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition fill_seg3__stmt : Prop := forall (m : mem) (a1 a2 a3 a4 a5 a6 a7 : word) (lt ext snap : Z) (s6 : word),
    mem_inv asegs m -> unpoisoned m P (P + 664) ->
    rw_cells asegs m SPA SPILL1 -> rw_cells asegs m P (pcells P sw maj min lt ext B8 B4 B8 B4 B8 B8 B4 B4) ->
    evtF asegs RNG (fun ms' => exists m',
        ms' = MS (REGS (Z_to_bv 64 0x87c0c) (Z_to_bv 64 snap) (Z_to_bv 64 (P + 96)) (Z_to_bv 64 (P + 648)) (Z_to_bv 64 (P + 660)) a4
                       (Z_to_bv 64 (Z.shiftr (P + 96) 3 + 2147450880)) (Z_to_bv 64 (Z.shiftr (P + 660) 3 + 2147450880)) (Z_to_bv 64 18446744072127396941)
                       (Z_to_bv 64 P) (Z_to_bv 64 min) (Z_to_bv 64 P))
                 F (Z_to_bv 64 0x87ca0) fc None m' (seg_rom asegs)
        /\ munch [(P, P + 664)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
        /\ rw_cells asegs m' P (pcells P sw maj min lt ext (C8 (Z_to_bv 64 0x88188)) B4 B8 (C4 (Z_to_bv 64 snap)) B8 B8 B4 B4))
      (MS (REGS (Z_to_bv 64 0x87c0c) (Z_to_bv 64 snap) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 P) (Z_to_bv 64 min) s6) F (Z_to_bv 64 0x87c0c) fc None m (seg_rom asegs)).
  Section Sz3.
  Variables m a1 a2 a3 a4 a5 a6 a7 lt ext snap s6 : ltac2:(SecDiet.SzSec.tyM 'fill_seg3__stmt "vvvvvvvvvvvv" @m).
  #[using="bP kPF n0 n1 n2 n3 l0 l1 l2 l3 PBK HOK"] Lemma fill_seg3__body : ltac2:(SecDiet.SzSec.bodyP 'fill_seg3__stmt "vvvvvvvvvvvv").
  Proof.
    intros MI PUNP FRA CELLS.
    qnorm.
    qfold.
    (pose proof PBK as ndP__; nd_pre ndP__ 18%nat; intros PRNG PRSH RSP RFR RIMG P16 bPr bPhi bPlo bPimg PSP FSP Fb0 SPAHI SPALO kPFr kPF1 kPF2; nd_post).
    (pose proof HOK as ndP__; nd_pre ndP__ 13%nat; intros MIB Bmaj Bmin N0 N1 N2 N3 L0 L1 L2 L3 Z2 Z3; nd_post).
    pose proof (munch_refl [(P, P + 664)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    unfold pcells in CELLS.
    zstep. ck0 PUNP; ck_go.
    do 2 zstep.
    zstep. ck0 PUNP; ck_go.
    do 4 zstep.
    ck0 PUNP; ck_go.
    zstep. ck0 PUNP; ck_go.
    do 3 zstep.
    zstep. if_false.
    zstep.
    zstep. if_false.
    do 5 zstep.
    replace (Z_to_bv 64 (-1582154675)) with (Z_to_bv 64 18446744072127396941) by (apply Z_to_bv_eqm; reflexivity).
    apply evtF_done. eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
    unfold pcells. exact CELLS.
  Qed.
  End Sz3.
  #[using="bP kPF n0 n1 n2 n3 l0 l1 l2 l3 PBK HOK"] Lemma fill_seg3 : ltac:(let t := eval cbv delta [fill_seg3__stmt] in fill_seg3__stmt in exact t).
  Proof. intros m a1 a2 a3 a4 a5 a6 a7 lt ext snap s6. ltac2:(SecDiet.SzSec.closeP 'fill_seg3__body "vvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition fill_scale : sf_scale_t := if (mi =? NSEC_TCPDUMP_MAGIC)%Z then SF_SCALE_DOWN else SF_PASS_THROUGH.
  Definition fill_lensw : lenswap_t :=
    if (maj =? 2)%Z then (if (min <? 3)%Z then SWAPPED else if (min =? 3)%Z then MAYBE_SWAPPED else NOT_SWAPPED)
    else if (maj =? 543)%Z then SWAPPED else NOT_SWAPPED.
  Definition fill_hs_ss (lt snap : Z) : Z * Z :=
    if (mi =? KUZNETZOV_TCPDUMP_MAGIC)%Z
    then (24, if (lt =? DLT_EN10MB)%Z then (if (snap <=? INT_MAX - 14)%Z then snap + 14 else INT_MAX) else snap)%Z
    else (16, snap)%Z.

  (* [comment removed for export] *)
  Definition fill_seg4__stmt : Prop := forall (m : mem) (a0 a1 a4 a5 : word) (lt ext : Z) (nxtw snapw : word),
    mem_inv asegs m -> unpoisoned m P (P + 664) ->
    rw_cells asegs m P (pcells P sw maj min lt ext (C8 nxtw) B4 B8 (C4 snapw) B8 B8 B4 B4) ->
    evtF asegs RNG (fun ms' => exists a6' m',
        ms' = MS (REGS (Z_to_bv 64 0x87c0c) a0 a1 (Z_to_bv 64 (P + 648)) (Z_to_bv 64 (P + 660)) a4 a5 a6' (Z_to_bv 64 18446744072127396941)
                       (Z_to_bv 64 P) (Z_to_bv 64 min) (Z_to_bv 64 P))
                 F (Z_to_bv 64 0x87d64) fc None m' (seg_rom asegs)
        /\ munch [(P, P + 664)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
        /\ rw_cells asegs m' P (pcells P sw maj min lt ext (C8 nxtw) B4 B8 (C4 snapw) B8 B8 B4 (C4 (Z_to_bv 64 (sfscale_code fill_scale)))))
      (MS (REGS (Z_to_bv 64 0x87c0c) a0 a1 (Z_to_bv 64 (P + 648)) (Z_to_bv 64 (P + 660)) a4 a5 (Z_to_bv 64 (Z.shiftr (P + 660) 3 + 2147450880))
                (Z_to_bv 64 18446744072127396941) (Z_to_bv 64 P) (Z_to_bv 64 min) (Z_to_bv 64 P))
          F (Z_to_bv 64 0x87ca0) fc None m (seg_rom asegs)).
  Section Sz4.
  Variables m a0 a1 a4 a5 lt ext nxtw snapw : ltac2:(SecDiet.SzSec.tyM 'fill_seg4__stmt "vvvvvvvvv" @m).
  #[using="bP kPF n0 n1 n2 n3 l0 l1 l2 l3 PBK HOK"] Lemma fill_seg4__body : ltac2:(SecDiet.SzSec.bodyP 'fill_seg4__stmt "vvvvvvvvv").
  Proof.
    intros MI PUNP CELLS.
    qnorm.
    (pose proof PBK as ndP__; nd_pre ndP__ 18%nat; intros PRNG PRSH RSP RFR RIMG P16 bPr bPhi bPlo bPimg PSP FSP Fb0 SPAHI SPALO kPFr kPF1 kPF2; nd_post).
    (pose proof HOK as ndP__; nd_pre ndP__ 13%nat; intros MIB Bmaj Bmin N0 N1 N2 N3 L0 L1 L2 L3 Z2 Z3; nd_post).
    pose proof (munch_refl [(P, P + 664)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    unfold pcells in CELLS. unfold fill_scale.
    zstep.
    destruct (Z.eq_dec mi NSEC_TCPDUMP_MAGIC) as [EN|NN].
    - subst mi. rewrite Z.eqb_refl. if_false.
      ck0_at PUNP (P + 660)%Z; ck_go.
      do 3 zstep.
      apply evtF_done. do 2 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
      unfold pcells. exact CELLS.
    - replace (mi =? NSEC_TCPDUMP_MAGIC)%Z with false by (symmetry; apply Z.eqb_neq; exact NN).
      unfold NSEC_TCPDUMP_MAGIC in NN.
      if_cases KN; [|zify_cond KN; exfalso; lia].
      ck0_at PUNP (P + 660)%Z; ck_go.
      do 2 zstep.
      apply evtF_done. do 2 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
      unfold pcells. exact CELLS.
  Qed.
  End Sz4.
  #[using="bP kPF n0 n1 n2 n3 l0 l1 l2 l3 PBK HOK"] Lemma fill_seg4 : ltac:(let t := eval cbv delta [fill_seg4__stmt] in fill_seg4__stmt in exact t).
  Proof. intros m a0 a1 a4 a5 lt ext nxtw snapw. ltac2:(SecDiet.SzSec.closeP 'fill_seg4__body "vvvvvvvvv"). Qed.

  Local Tactic Notation "seg_done" integer(n) ident(MU) ident(WM) :=
    apply evtF_done; do n eexists; split; [reflexivity|]; split; [exact MU|]; split; [exact WM|]; split; [assumption|].
  Local Ltac decide_ifs :=
    repeat first [ rewrite (proj2 (Z.eqb_eq _ _)) by lia | rewrite (proj2 (Z.eqb_neq _ _)) by lia
                 | rewrite (proj2 (Z.ltb_lt _ _)) by lia | rewrite (proj2 (Z.ltb_ge _ _)) by lia
                 | rewrite (proj2 (Z.leb_le _ _)) by lia | rewrite (proj2 (Z.leb_gt _ _)) by lia ].

  (* [comment removed for export] *)
  Definition fill_segL__stmt : Prop := forall (m : mem) (a0 a1 a3 a4 a5 a6 a7 : word) (lt ext : Z) (nxtw snapw sclw : word),
    mem_inv asegs m -> unpoisoned m P (P + 664) ->
    rw_cells asegs m P (pcells P sw maj min lt ext (C8 nxtw) B4 B8 (C4 snapw) B8 B8 B4 (C4 sclw)) ->
    evtF asegs RNG (fun ms' => exists a3' a6' a7' m',
        ms' = MS (REGS (Z_to_bv 64 0x87c0c) a0 a1 (Z_to_bv 64 (P + 648)) a3' a4 a5 a6' a7' (Z_to_bv 64 P) (Z_to_bv 64 min) (Z_to_bv 64 P))
                 F (Z_to_bv 64 0x87e1c) fc None m' (seg_rom asegs)
        /\ munch [(P, P + 664)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
        /\ rw_cells asegs m' P (pcells P sw maj min lt ext (C8 nxtw) B4 B8 (C4 snapw) B8 B8 (C4 (Z_to_bv 64 (lenswap_code fill_lensw))) (C4 sclw)))
      (MS (REGS (Z_to_bv 64 0x87c0c) a0 a1 (Z_to_bv 64 (P + 648)) a3 a4 a5 a6 a7 (Z_to_bv 64 P) (Z_to_bv 64 min) (Z_to_bv 64 P))
          F (Z_to_bv 64 0x87d64) fc None m (seg_rom asegs)).
  Section Sz5.
  Variables m a0 a1 a3 a4 a5 a6 a7 lt ext nxtw snapw sclw : ltac2:(SecDiet.SzSec.tyM 'fill_segL__stmt "vvvvvvvvvvvvv" @m).
  #[using="bP kPF n0 n1 n2 n3 l0 l1 l2 l3 PBK HOK"] Lemma fill_segL__body : ltac2:(SecDiet.SzSec.bodyP 'fill_segL__stmt "vvvvvvvvvvvvv").
  Proof.
    intros MI PUNP CELLS.
    qnorm.
    qfold.
    (pose proof PBK as ndP__; nd_pre ndP__ 18%nat; intros PRNG PRSH RSP RFR RIMG P16 bPr bPhi bPlo bPimg PSP FSP Fb0 SPAHI SPALO kPFr kPF1 kPF2; nd_post).
    (pose proof HOK as ndP__; nd_pre ndP__ 13%nat; intros MIB Bmaj Bmin N0 N1 N2 N3 L0 L1 L2 L3 Z2 Z3; nd_post).
    pose proof (munch_refl [(P, P + 664)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    unfold pcells in CELLS.
    do 2 zstep. if_cases K543; zify_cond K543.
    - zstep. ck0 PUNP; ck_go. do 3 zstep.
      seg_done 4 MU WM. unfold pcells, fill_lensw. decide_ifs. exact CELLS.
    - do 2 zstep. if_cases K2; zify_cond K2.
      + zstep. ck0 PUNP; ck_go. zstep.
        seg_done 4 MU WM. unfold pcells, fill_lensw. decide_ifs. exact CELLS.
      + zstep. if_cases Klt; zify_cond Klt.
        * do 4 zstep. zstep. if_cases K3; zify_cond K3.
          -- ck0_at PUNP (P + 656)%Z; ck_go. zstep.
             seg_done 4 MU WM. unfold pcells, fill_lensw. decide_ifs. exact CELLS.
          -- ck0_at PUNP (P + 656)%Z; ck_go. do 3 zstep.
             seg_done 4 MU WM. unfold pcells, fill_lensw. decide_ifs. exact CELLS.
        * zstep. ck0 PUNP; ck_go. do 3 zstep.
          seg_done 4 MU WM. unfold pcells, fill_lensw. decide_ifs. exact CELLS.
  Qed.
  End Sz5.
  #[using="bP kPF n0 n1 n2 n3 l0 l1 l2 l3 PBK HOK"] Lemma fill_segL : ltac:(let t := eval cbv delta [fill_segL__stmt] in fill_segL__stmt in exact t).
  Proof. intros m a0 a1 a3 a4 a5 a6 a7 lt ext nxtw snapw sclw. ltac2:(SecDiet.SzSec.closeP 'fill_segL__body "vvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition fill_segH__stmt : Prop := forall (m : mem) (a3 a4 a6 a7 : word) (lt ext snap : Z) (nxtw lsww sclw : word),
    mem_inv asegs m -> unpoisoned m P (P + 664) -> (0 <= lt < 2^31)%Z -> (1 <= snap <= 2147483647)%Z ->
    rw_cells asegs m SPA SPILL1 ->
    rw_cells asegs m P (pcells P sw maj min lt ext (C8 nxtw) B4 B8 (C4 (Z_to_bv 64 snap)) B8 B8 (C4 lsww) (C4 sclw)) ->
    evtF asegs RNG (fun ms' => exists a0' a2' a3' a6' m',
        ms' = MS (REGS (Z_to_bv 64 0x87c0c) a0' (Z_to_bv 64 (P + 96)) a2' a3' a4 (Z_to_bv 64 (Z.shiftr (P + 96) 3 + 2147450880)) a6' a7
                       (Z_to_bv 64 P) (Z_to_bv 64 min) (Z_to_bv 64 P))
                 F (Z_to_bv 64 0x87e9c) fc None m' (seg_rom asegs)
        /\ munch [(P, P + 664)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
        /\ rw_cells asegs m' P (pcells P sw maj min lt ext (C8 nxtw) B4 B8 (C4 (Z_to_bv 64 (snd (fill_hs_ss lt snap)))) B8
                                       (C8 (Z_to_bv 64 (fst (fill_hs_ss lt snap)))) (C4 lsww) (C4 sclw)))
      (MS (REGS (Z_to_bv 64 0x87c0c) (Z_to_bv 64 snap) (Z_to_bv 64 (P + 96)) (Z_to_bv 64 (P + 648)) a3 a4 (Z_to_bv 64 (Z.shiftr (P + 96) 3 + 2147450880)) a6 a7
                (Z_to_bv 64 P) (Z_to_bv 64 min) (Z_to_bv 64 P))
          F (Z_to_bv 64 0x87e1c) fc None m (seg_rom asegs)).
  Section Sz6.
  Variables m a3 a4 a6 a7 lt ext snap nxtw lsww sclw : ltac2:(SecDiet.SzSec.tyM 'fill_segH__stmt "vvvvvvvvvvv" @m).
  #[using="bP kPF n0 n1 n2 n3 l0 l1 l2 l3 PBK HOK"] Lemma fill_segH__body : ltac2:(SecDiet.SzSec.bodyP 'fill_segH__stmt "vvvvvvvvvvv").
  Proof.
    intros MI PUNP LTR SNR FRA CELLS.
    qnorm.
    (pose proof PBK as ndP__; nd_pre ndP__ 18%nat; intros PRNG PRSH RSP RFR RIMG P16 bPr bPhi bPlo bPimg PSP FSP Fb0 SPAHI SPALO kPFr kPF1 kPF2; nd_post).
    (pose proof HOK as ndP__; nd_pre ndP__ 13%nat; intros MIB Bmaj Bmin N0 N1 N2 N3 L0 L1 L2 L3 Z2 Z3; nd_post).
    pose proof (munch_refl [(P, P + 664)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    unfold pcells in CELLS. unfold fill_hs_ss, INT_MAX, DLT_EN10MB.
    do 4 zstep.
    replace (Z_to_bv 64 (-1582117580)) with (Z_to_bv 64 18446744072127434036) by (apply Z_to_bv_eqm; reflexivity).
    zstep.
    destruct (Z.eq_dec mi KUZNETZOV_TCPDUMP_MAGIC) as [EK|NK].
    - subst mi. rewrite Z.eqb_refl. if_false.
      ck0_at PUNP (P + 648)%Z; ck_go.
      do 2 zstep.
      zstep. ck0_at PUNP (P + 100)%Z; ck_go.
      zstep. rewrite (sx32_small lt) by lia.
      do 2 zstep.
      destruct (Z.eq_dec lt 1) as [EL1|EL1].
      + subst lt. if_false.
        do 3 zstep.
        destruct (Z.le_gt_cases snap 2147483633) as [S1|S1].
        * if_cases Ks; [zify_cond Ks; rewrite ?signed_lit_small in Ks by lia; exfalso; lia|].
          ck0_at PUNP (P + 96)%Z; ck_go.
          do 2 zstep.
          ck0_at PUNP (P + 96)%Z; ck_go.
          seg_done 5 MU WM. cbn [fst snd]. decide_ifs. unfold pcells. exact CELLS.
        * if_cases Ks; [|zify_cond Ks; rewrite ?signed_lit_small in Ks by lia; exfalso; lia].
          ck0_at PUNP (P + 96)%Z; ck_go.
          do 3 zstep.
          ck0_at PUNP (P + 96)%Z; ck_go.
          seg_done 5 MU WM. cbn [fst snd]. decide_ifs. unfold pcells.
          lazymatch type of CELLS with rw_cells _ ?mm _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: ?c9 :: ?c10 :: ?c11 :: ?c12 :: ?c13 :: C4 ?w :: ?post) =>
            pose proof (rw_cells_C4_low mm P [c0; c1; c2; c3; c4; c5; c6; c7; c8; c9; c10; c11; c12; c13] w (Z_to_bv 64 2147483647) post CELLS le4_intmax) as CELLS2 end.
          cbn [app] in CELLS2. exact CELLS2.
      + if_cases Kl; [|zify_cond Kl; exfalso; lia].
        ck0_at PUNP (P + 96)%Z; ck_go.
        seg_done 5 MU WM. cbn [fst snd]. decide_ifs. unfold pcells. exact CELLS.
    - replace (mi =? KUZNETZOV_TCPDUMP_MAGIC)%Z with false by (symmetry; apply Z.eqb_neq; exact NK).
      unfold KUZNETZOV_TCPDUMP_MAGIC in NK.
      if_cases KK; [|zify_cond KK; exfalso; lia].
      ck0_at PUNP (P + 648)%Z; ck_go.
      do 2 zstep.
      ck0_at PUNP (P + 96)%Z; ck_go.
      seg_done 5 MU WM. cbn [fst snd]. unfold pcells. exact CELLS.
  Qed.
  End Sz6.
  #[using="bP kPF n0 n1 n2 n3 l0 l1 l2 l3 PBK HOK"] Lemma fill_segH : ltac:(let t := eval cbv delta [fill_segH__stmt] in fill_segH__stmt in exact t).
  Proof. intros m a3 a4 a6 a7 lt ext snap nxtw lsww sclw. ltac2:(SecDiet.SzSec.closeP 'fill_segH__body "vvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition fill_segB__stmt : Prop := forall (m : mem) (a0 a1 a2 a3 a4 a5 a6 a7 : word) (lt ext SS : Z) (nxtw hszw lsww sclw : word),
    mem_inv asegs m -> unpoisoned m P (P + 664) -> (1 <= SS <= 2147483647)%Z ->
    rw_cells asegs m P (pcells P sw maj min lt ext (C8 nxtw) B4 B8 (C4 (Z_to_bv 64 SS)) B8 (C8 hszw) (C4 lsww) (C4 sclw)) ->
    evtF asegs RNG (fun ms' => exists a1' a2' m',
        ms' = MS (REGS (Z_to_bv 64 0x87ecc) (Z_to_bv 64 (if 2048 <? SS then 2048 else SS)%Z) a1' a2' a3 a4 a5 a6 a7 (Z_to_bv 64 P) (Z_to_bv 64 min) (Z_to_bv 64 P))
                 F (Z_to_bv 64 0x56178) fc None m' (seg_rom asegs)
        /\ munch [(P, P + 664)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
        /\ rw_cells asegs m' P (pcells P sw maj min lt ext (C8 nxtw) (C4 (Z_to_bv 64 (if 2048 <? SS then 2048 else SS)%Z)) B8 (C4 (Z_to_bv 64 SS)) B8
                                       (C8 hszw) (C4 lsww) (C4 sclw)))
      (MS (REGS (Z_to_bv 64 0x87c0c) a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 P) (Z_to_bv 64 min) (Z_to_bv 64 P)) F (Z_to_bv 64 0x87e9c) fc None m (seg_rom asegs)).
  Section Sz7.
  Variables m a0 a1 a2 a3 a4 a5 a6 a7 lt ext SS nxtw hszw lsww sclw : ltac2:(SecDiet.SzSec.tyM 'fill_segB__stmt "vvvvvvvvvvvvvvvv" @m).
  #[using="bP kPF n0 n1 n2 n3 l0 l1 l2 l3 PBK HOK"] Lemma fill_segB__body : ltac2:(SecDiet.SzSec.bodyP 'fill_segB__stmt "vvvvvvvvvvvvvvvv").
  Proof.
    intros MI PUNP SSR CELLS.
    qnorm.
    qfold.
    (pose proof PBK as ndP__; nd_pre ndP__ 18%nat; intros PRNG PRSH RSP RFR RIMG P16 bPr bPhi bPlo bPimg PSP FSP Fb0 SPAHI SPALO kPFr kPF1 kPF2; nd_post).
    (pose proof HOK as ndP__; nd_pre ndP__ 13%nat; intros MIB Bmaj Bmin N0 N1 N2 N3 L0 L1 L2 L3 Z2 Z3; nd_post).
    pose proof (munch_refl [(P, P + 664)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    unfold pcells in CELLS.
    zstep. rewrite (sx32_small SS) by lia.
    do 3 zstep. zstep.
    destruct (Z.lt_ge_cases SS 2048) as [S2|S2].
    - if_cases Kt; [|zify_cond Kt; exfalso; lia].
      ck0 PUNP; ck_go. zstep. zstep.
      try unfold QQ. decide_ifs. seg_done 3 MU WM. unfold pcells. exact CELLS.
    - if_cases Kt; [zify_cond Kt; exfalso; lia|].
      zstep. ck0 PUNP; ck_go. zstep. zstep.
      destruct (Z.eq_dec SS 2048) as [E2|E2].
      + subst SS. change (2048 <? 2048)%Z with false. cbv iota. seg_done 3 MU WM. unfold pcells. exact CELLS.
      + try unfold QQ. decide_ifs. seg_done 3 MU WM. unfold pcells. exact CELLS.
  Qed.
  End Sz7.
  #[using="bP kPF n0 n1 n2 n3 l0 l1 l2 l3 PBK HOK"] Lemma fill_segB : ltac:(let t := eval cbv delta [fill_segB__stmt] in fill_segB__stmt in exact t).
  Proof. intros m a0 a1 a2 a3 a4 a5 a6 a7 lt ext SS nxtw hszw lsww sclw. ltac2:(SecDiet.SzSec.closeP 'fill_segB__body "vvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition fill_segE__stmt : Prop := forall (m : mem) (a1 a2 a3 a4 a5 a6 a7 : word) (lt ext B : Z) (nxtw bszw snapw hszw lsww sclw g0 g1 g2 : word),
    mem_inv asegs m -> unpoisoned m P (P + 664) -> (0 < B < 2^64)%Z ->
    rw_cells asegs m SPA SPILL1 ->
    rw_cells asegs m 0xa6128 [C8 g0; C8 g1; C8 g2; C8 (Z_to_bv 64 (pk_cleanup_sf PK))] ->
    rw_cells asegs m P (pcells P sw maj min lt ext (C8 nxtw) (C4 bszw) B8 (C4 snapw) B8 (C8 hszw) (C4 lsww) (C4 sclw)) ->
    evtF asegs RNG (fun ms' => exists a1' a2' m',
        ms' = MS (REGS (Z_to_bv 64 0x87ecc) (Z_to_bv 64 P) a1' a2' a3 a4 (Z_to_bv 64 Fb) a6 a7 (Z_to_bv 64 P) (Z_to_bv 64 min) (Z_to_bv 64 P))
                 F (Z_to_bv 64 0x87a50) fc None m' (seg_rom asegs)
        /\ munch [(P, P + 664)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
        /\ rw_cells asegs m' P (pcells P sw maj min lt ext (C8 nxtw) (C4 bszw) (C8 (Z_to_bv 64 B)) (C4 snapw) (C8 (Z_to_bv 64 (pk_cleanup_sf PK)))
                                       (C8 hszw) (C4 lsww) (C4 sclw)))
      (MS (REGS (Z_to_bv 64 0x87ecc) (Z_to_bv 64 B) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 P) (Z_to_bv 64 min) (Z_to_bv 64 P)) F (Z_to_bv 64 0x87ecc) fc None m (seg_rom asegs)).
  Section Sz8.
  Variables m a1 a2 a3 a4 a5 a6 a7 lt ext B nxtw bszw snapw hszw lsww sclw g0 g1 g2 : ltac2:(SecDiet.SzSec.tyM 'fill_segE__stmt "vvvvvvvvvvvvvvvvvvvv" @m).
  #[using="bP kPF n0 n1 n2 n3 l0 l1 l2 l3 PBK HOK"] Lemma fill_segE__body : ltac2:(SecDiet.SzSec.bodyP 'fill_segE__stmt "vvvvvvvvvvvvvvvvvvvv").
  Proof.
    intros MI PUNP BR FRA GOT CELLS.
    qnorm.
    qfold.
    (pose proof PBK as ndP__; nd_pre ndP__ 18%nat; intros PRNG PRSH RSP RFR RIMG P16 bPr bPhi bPlo bPimg PSP FSP Fb0 SPAHI SPALO kPFr kPF1 kPF2; nd_post).
    (pose proof HOK as ndP__; nd_pre ndP__ 13%nat; intros MIB Bmaj Bmin N0 N1 N2 N3 L0 L1 L2 L3 Z2 Z3; nd_post).
    pose proof (munch_refl [(P, P + 664)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    unfold pcells in CELLS. unfold PK in *. cbn [pk_cleanup_sf] in *.
    zstep. ck0 PUNP; ck_go.
    do 2 zstep.
    zstep. if_false_by (eqz_false B BR).
    do 2 zstep. ck0 PUNP; ck_go.
    do 2 zstep.
    do 2 zstep.
    seg_done 3 MU WM. unfold pcells. exact CELLS.
  Qed.
  End Sz8.
  #[using="bP kPF n0 n1 n2 n3 l0 l1 l2 l3 PBK HOK"] Lemma fill_segE : ltac:(let t := eval cbv delta [fill_segE__stmt] in fill_segE__stmt in exact t).
  Proof. intros m a1 a2 a3 a4 a5 a6 a7 lt ext B nxtw bszw snapw hszw lsww sclw g0 g1 g2. ltac2:(SecDiet.SzSec.closeP 'fill_segE__body "vvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma fill_hs_ss_range : forall lt snap, (1 <= snap <= 2147483647)%Z ->
    (1 <= snd (fill_hs_ss lt snap) <= 2147483647)%Z /\ (fst (fill_hs_ss lt snap) = 16 \/ fst (fill_hs_ss lt snap) = 24)%Z.
  Proof.
    intros lt snap SNR. unfold fill_hs_ss, INT_MAX. destruct (mi =? KUZNETZOV_TCPDUMP_MAGIC)%Z; cbn [fst snd]; [|lia].
    destruct (lt =? DLT_EN10MB)%Z; [|lia]. destruct (Z.leb_spec snap (2^31 - 1 - 14)); lia.
  Qed.
End FillSeg.

#[using="Type"] Lemma pblk_ok_fp_le : forall RNG RNG' SPA P Fb bP kPF, fp_le RNG RNG' -> pblk_ok RNG SPA P Fb bP kPF -> pblk_ok RNG' SPA P Fb bP kPF.
Proof.
  intros RNG RNG' SPA P Fb bP kPF FP (H1 & H2 & H3 & H4 & H5 & REST).
  split; [exact (rng_fp_le _ _ _ _ FP H1)|]. split; [exact (rng_fp_le _ _ _ _ FP H2)|]. split; [exact (rng_fp_le _ _ _ _ FP H3)|].
  split; [exact (rng_fp_le _ _ _ _ FP H4)|]. split; [exact (rng_fp_le _ _ _ _ FP H5)| exact REST].
Qed.
End CANSEC1.
End F_sfchk_fsegA.

(* [comment removed for export] *)
Module FoLeafReal.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Exec ITree Nodes Decode SysStep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Exit__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Exit__S3.MLeaf.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require AsanHeap__SpecA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanHeap__SpecA.AsanHeap.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LeafA__A3P.LeafA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
#[using="rc"] Lemma asan_fo_leaf_laws : forall site_frame, fo_leaf_laws (asan_fo site_frame).
Proof.
  intros site_frame. split.
  - intros A f body s a s' L. cbn [fo_enter asan_fo] in L.
    apply mleaf_bind in L as (B & s1 & _ & L). apply mleaf_bind in L as (u & s2 & _ & L). exists s2. exact L.
  - intros A f x s a s' L. cbn [fo_ret asan_fo] in L.
    apply mleaf_bind in L as (u & s1 & _ & L). apply mleaf_ret in L as [E _]. exact E.
Qed.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Strings.String.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MState OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Mem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Exec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Exit__S3.MLeaf.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanHeap__SpecA.AsanHeap.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LeafA__A3P.LeafA.TwB. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
#[using="rc"] Lemma asan_fo_leaf_laws : forall site_frame, fo_leaf_laws (asan_fo site_frame).
Proof.
  intros site_frame. split.
  - intros A f body s a s' L. cbn [fo_enter asan_fo] in L.
    apply mleaf_bind in L as (B & s1 & _ & L). apply mleaf_bind in L as (u & s2 & _ & L). exists s2. exact L.
  - intros A f x s a s' L. cbn [fo_ret asan_fo] in L.
    apply mleaf_bind in L as (u & s1 & _ & L). apply mleaf_ret in L as [E _]. exact E.
Qed.
End CANSEC1.
End TwB.
End FoLeafReal.

(* [comment removed for export] *)
Module F_ngchk_headA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep Frame StoreFast.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow StepF SysStepF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg ABase AMalloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require FmtFacts__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.FmtFacts.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FrameKit__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FmtKitA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require SfKitA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngchk_modelA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngchk_defsA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require LibcKit2__A3P. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.PerfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FmtKitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.MonadGX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.SfKitA__A3P.SfKitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_modelA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_defsA__A3P.F_ngchk_defsA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_defsA__A3P.F_ngchk_exitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit2__A3P.F_ngchk_failA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit2__A3P.F_ngchk_kitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_defsA__A3P.F_ngchk_fstmtA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_defsA__A3P.F_ngchk_hstmtA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_defsA__A3P.F_ngchk_hstmt2A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LeafA__A3P.F_ngchk_hsegA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaRel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac dm_plia := first [ atop_facts; once ltac2:(let _ := LiaRel.lr_prune_b 101 in ()); Z.div_mod_to_equations; lia_tiers
                            | Z.div_mod_to_equations; lia ].
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= unp_store m a bs n Hn Ha Hl.
Local Ltac sl_store_extra m m' a bs n Hn Ha Hl CH ::= sl_store_extra_std m m' a bs n Hn Ha Hl CH.   (* [comment removed for export] *)
Local Ltac transport_call_extra segs W m m' MU WM ::= unp_call W m m' MU.
(* [comment removed for export] *)
Local Ltac oiv_lo_base k := lazymatch goal with |- (?lo0 <= ?lo)%Z /\ _ => d_split lo0 ltac:(fun X0 _ _ => d_split lo ltac:(fun X _ _ => constr_eq X0 X; k)) end.
Local Ltac oiv_orig :=
  first [ left; cbn [fst snd]; lia
        | right; right; left; apply Exists_cons_hd; cbn [fb_addr fb_size fst snd]; lia
        | right; right; right; apply Exists_cons_hd; cbn [fb_addr fb_size fst snd]; shr_consts; lia
        | right; left; first [ apply Exists_cons_hd | apply Exists_cons_tl; apply Exists_cons_hd | apply Exists_cons_tl; apply Exists_cons_tl; apply Exists_cons_hd ];
          cbn [cb_addr cb_size fst snd]; lia ].
Local Ltac own_iv1 ::=
  unfold own_ivA, iv_in_block, iv_in_frames, iv_in_frame_shadow;
  first [ right; right; left; apply Exists_cons_hd; cbn [fb_addr fb_size fst snd]; oiv_lo_base ltac:(lia)
        | right; right; right; apply Exists_cons_hd; cbn [fb_addr fb_size fst snd]; shr_consts; oiv_lo_base ltac:(lia)
        | right; left; first [ apply Exists_cons_hd | apply Exists_cons_tl; apply Exists_cons_hd | apply Exists_cons_tl; apply Exists_cons_tl; apply Exists_cons_hd ];
          cbn [cb_addr cb_size fst snd]; oiv_lo_base ltac:(lia)
        | oiv_orig ].
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Ltac hide H := lazymatch type of H with ?T => let X := fresh "AUX" in set (X := T) in H end.
Ltac unhide H := lazymatch type of H with ?X => subst X end.
Ltac ienterG := lazymatch goal with |- implMG _ _ _ ?Q _ => let QQ := fresh "POSTQ" in set (QQ := Q) end; apply implMG_from_evtF.

Tactic Notation "xf1" constr(AG) hyp(HH) tactic3(loc) :=
  apply (agrees_rw_cells _ _ _ _ _ AG) in HH;
  [| let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; cbn [cells_size csize Nat.add] in Ha; loc].
Tactic Notation "xf2" constr(AG) hyp(HH) tactic3(loc) :=
  apply (agrees_rw_cells _ _ _ _ _ AG) in HH;
  [| let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [loc| lia]].

Lemma land_m32H : forall x, (0 <= x < 2^64)%Z -> Z.land x 18446744073709551584 = (x - x mod 32)%Z.
Proof. intros x Hx. exact (land_align_down x 5 Hx ltac:(lia)). Qed.

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section NgcHead.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis FENTER0 : fenter_stmt_o FO GIOA fflagA 0 STACK_MALLOC_0.
  Hypothesis FRET : fret_inline_law FO GIOA fflagA.
  Hypothesis FREAD : fread_stmt_o HO GIOA.
  Hypothesis SHORT : ngc_short_stmt HO FO sites GIOA TP fflagA.
  Hypothesis BOM : ngc_bom_stmt HO FO sites GIOA TP fflagA.

  Definition pcap_ng_check_header_headA__stmt : Prop := pcap_ng_check_header_stmt HO FO sites GIOA TP.
  Section Sz2.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CL FB FL trC lo MG FA EB ERR f magic ej ec : ltac2:(SecDiet.SzSec.tyM 'pcap_ng_check_header_headA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma pcap_ng_check_header_headA__body : ltac2:(SecDiet.SzSec.bodyP 'pcap_ng_check_header_headA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using BOM FENTER0 FREAD FRET GL SHORT.
 intros fuel PRE UC TR NF HinF -> -> -> -> -> HMG MGR MGL HEB HERR ECS OMG OERR DME OEB DEE DEM ERR4 EB8.
    destruct PRE as (G & ST & LO & BU & SPT & MI & TPE & ALN & RSTK & RIMG & RISH & RTLS).
    pose proof (gl_rt _ _ _ GL _ _ _ _ _ _ _ G) as ((_ & GOT & _ & _ & SHB & SUA & _) & GSU). unfold GOT_UAR in GSU.
    unfold PCAP_L2_STACK in BU.
    assert (RSPW : rng RNG lo (bv_unsigned sp - lo)) by (eapply rng_sub'; [exact RSTK| lia]).
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof (clocA_below _ _ _ GL _ _ _ _ _ _ _ _ _ G (proj1 OMG)) as (MGLO & MGHI).
    pose proof (clocA_below _ _ _ GL _ _ _ _ _ _ _ _ _ G (proj1 OERR)) as (ERLO & ERHI).
    pose proof (clocA_below _ _ _ GL _ _ _ _ _ _ _ _ _ G (proj1 OEB)) as (EBLO & EBHI).
    pose proof (clocA_ablk _ _ _ GL _ _ _ _ _ _ _ _ _ G (proj1 OMG) ltac:(lia)) as MGBAND.
    pose proof (clocA_ablk _ _ _ GL _ _ _ _ _ _ _ _ _ G (proj1 OERR) ltac:(lia)) as ERBAND.
    pose proof (clocA_ablk _ _ _ GL _ _ _ _ _ _ _ _ _ G (proj1 OEB) ltac:(lia)) as EBBAND.
    pose proof MGBAND as MGBAND'. pose proof ERBAND as ERBAND'. pose proof EBBAND as EBBAND'.
    band_ind MGBAND bM. band_ind ERBAND bE. band_ind EBBAND bB.
    destruct magic as [|mg0 [|mg1 [|mg2 [|mg3 [|? ?]]]]]; try discriminate MGL. clear MGL.
    pose proof MGR as GR'. apply Forall_cons_iff in GR' as [GM0 GR']. apply Forall_cons_iff in GR' as [GM1 GR']. apply Forall_cons_iff in GR' as [GM2 GR']. apply Forall_cons_iff in GR' as [GM3 _].
    cbn [map] in HMG.
    assert (MG4 : rw_cells asegs m MG [C1 (b8 mg0); C1 (b8 mg1); C1 (b8 mg2); C1 (b8 mg3)]).
    { eapply rw_cells_recell; [exact HMG | cbn; repeat split; exact Logic.I | reflexivity]. }
    clear HMG.
    destruct (rw_cells_forget _ _ _ _ HERR) as [ecj HE]. clear HERR. cbn [cells_size] in HE. rewrite ECS in HE. change (4 + 0)%nat with 4%nat in HE.
    rewrite (ngc_head_eq MOps (prims HO FO sites)). cbn [e_fenter prims]. unfold PCAP_NG_CHECK_HEADER_ENTRY.
    remember (bv_unsigned sp - 256 - (bv_unsigned sp - 256) mod 32)%Z as SPA eqn:ESPA.
    assert (SPAP : (bv_unsigned sp - 272 <= SPA <= bv_unsigned sp - 256 /\ SPA mod 32 = 0 /\ (bv_unsigned sp + -256) - (bv_unsigned sp + -256) mod 32 = SPA)%Z)
      by (rewrite ESPA; dm_plia).
    destruct SPAP as (SPAB & SPA32 & ESPA').
    assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(bv_unsigned sp - 272, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    ienterG.
    (* [comment removed for export] *)
    zstep.
    carve_frame 104%nat ST. carve_frame 152%nat ST.
    zstep.
    do 13 zstep.
    zstep.
    zstep.
  rewrite land_m32H by lia. rewrite ESPA'.
  release_frame FR0 ST (bv_unsigned sp + -104)%Z.
  destruct (stk_split asegs _ lo (SPA + 152) (bv_unsigned sp + -104) ST ltac:(lia)) as [ST1 STG]. clear ST.
  destruct (stk_carve asegs _ lo (SPA + 152) 152 ST1 ltac:(cbn; lia)) as [STL [jA FRA]]. clear ST1.
  change (Z.of_nat 152) with 152%Z in STL, FRA. replace (SPA + 152 - 152)%Z with SPA in STL, FRA by lia.
  assert (RSPA : rng RNG SPA (bv_unsigned sp - SPA)) by (eapply rng_sub'; [exact RSTK| lia]).
  do 7 zstep.
  do 2 zstep.
  zstep.
  replace (sx32 (Z_to_bv 64 1)) with (Z_to_bv 64 1) by (vm_compute; reflexivity).
  zstep.
  zstep.
  zstep. if_false.
  do 2 zstep.
  (* [comment removed for export] *)
  assert (Gn : GIOA L RNG s (CL ++ []) FB FL m) by (rewrite app_nil_r; exact G).
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (FW0 : Forall (pcap_iv FL ([] : list (@cblock hptr))) [(bv_unsigned sp - 272, bv_unsigned sp)]%Z)
      by (apply Forall_cons; [left; cbn [fst snd]; lia| apply Forall_nil]);
    assert (G0 : GIOA L RNG s (CL ++ []) FB FL mm) by (eapply (gl_frame _ _ _ GL); [exact Gn | exact MU | exact WM | exact FW0]);
    assert (AGa : agrees_on (client_keeps FL CL (bv_unsigned sp)) m mm)
      by (eapply (gl_keeps _ _ _ GL _ _ _ _ _ _ FL []); [exact Gn | exact MU | exact WM | | lia];
          apply Forall_cons; [left; cbn [fst snd]; lia| apply Forall_nil])
  end.
  rename MU into MU0. rename WM into WM0. clear FW0.
  remember (Z_to_bv 64 SPA) as spa eqn:Espa.
  assert (Hspa : bv_unsigned spa = SPA) by (rewrite Espa; apply unsigned_lit; lia).
  apply evtF_done. eapply (FENTER0 _ spa).
  { split; [rewrite app_nil_r in G0; exact G0|]. rewrite Hspa. split; [exact STL|]. split; [lia|]. split; [unfold FAKE_STACK; lia|]. split; [lia|].
    split; [assumption|]. split; [exact TPE|]. split; [dm_plia|].
    split; [exact RSTK|]. split; [exact RIMG|]. split; [exact RISH| exact RTLS]. }
  { reflexivity. }
  { unfold ff_size, ff_class. lia. }
  { apply NF. left. reflexivity. }
  { reflexivity. }
  intros Fb s1' m2 j0 j1 j2 fjunk t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' G1 OF1 LC1 TL1 MI1 ST1 AG1 Fb0 LJ FRC SHC.
  rewrite Hspa in *. clear Hspa. subst spa.
  change (ff_size FF_NG_CHECK_HEADER) with 64%Z in *.
  change (Z.to_nat (64 - 32)) with 32%nat in *. change (Z.to_nat (64 / 8)) with 8%nat in *.
  apply sh_zero_cells in SHC. cbn [repeat] in SHC.
  replace (ret_pc (Z_to_bv 64 568680)) with (Z_to_bv 64 568680) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  destruct (gl_frames _ _ _ GL _ _ _ _ _ _ _ G1) as [FAll FND]. pose proof (Forall_inv FAll) as (FBAND' & FTOP' & F64 & _ & FRNG & FSRNG & _ & FSWR).
  cbn [fb_addr fb_size fst snd] in FBAND', FTOP', F64, FRNG, FSRNG, FSWR. clear FAll.
  change (Z.shiftr 64 3) with 8%Z in FSRNG, FSWR.
  band_ind FBAND' bF.
  (* [comment removed for export] *)
  apply (keeps_rw_cells_stack _ _ _ _ _ _ _ AG1) in FR; [|lia]. apply (keeps_rw_cells_stack _ _ _ _ _ _ _ AG1) in FRA; [|lia].
  apply (agrees_stk _ _ _ _ _ AG1) in STG; [|intros a Ha; left; lia].
  apply (agrees_rw_cells _ _ _ _ _ AG1) in MG4; [|intros a Ha; eapply clocA_keeps; [exact (proj1 OMG)| exact Ha]].
  apply (agrees_rw_cells _ _ _ _ _ AG1) in HE; [|intros a Ha; eapply clocA_keeps; [exact (proj1 OERR)| exact Ha]].
  apply (agrees_rw_cells _ _ _ _ _ AG1) in HEB; [|intros a Ha; eapply clocA_keeps; [exact (proj1 OEB)| exact Ha]].
  destruct (clocA_apart_frame _ _ _ GL _ _ _ _ _ _ _ _ _ _ G1 (proj1 OMG) ltac:(lia)) as (kM & kMr & kM1 & kM2).
  destruct (clocA_apart_frame _ _ _ GL _ _ _ _ _ _ _ _ _ _ G1 (proj1 OERR) ltac:(lia)) as (kE & kEr & kE1 & kE2).
  destruct (clocA_apart_frame _ _ _ GL _ _ _ _ _ _ _ _ _ _ G1 (proj1 OEB) ltac:(lia)) as (kB & kBr & kB1 & kB2).
  cbn [fb_addr fb_size fst snd] in kM1, kM2, kE1, kE2, kB1, kB2.
  assert (AGb : agrees_on (client_keeps FL CL (bv_unsigned sp)) m m2).
  { eapply agrees_on_trans; [exact AGa|]. eapply client_keeps_weaken; [exact AG1| lia| intros a Ha; exact Ha| apply incl_refl]. }
  assert (SHLO : (0x7fff8000 <= Z.shiftr Fb 3 + 2147450880 /\ Z.shiftr Fb 3 + 2147450880 + 8 <= 0x10007fff8000
                 /\ (Fb + 64 <= 0x7fff7000 \/ Z.shiftr Fb 3 + 2147450880 + 8 <= Fb))%Z)
    by (rewrite Z.shiftr_div_pow2 by lia; change (2^3)%Z with 8%Z; dm_plia).
  pose proof (munch_refl [(bv_unsigned sp - 272, bv_unsigned sp); (Fb, Fb + 64); (Z.shiftr Fb 3 + 2147450880, Z.shiftr Fb 3 + 2147450880 + 8); (ERR, ERR + 4); (EB, EB + 256)]%Z m2) as MU.
  pose proof (wmono_refl asegs m2) as WM.
  ienterG.
  (* [comment removed for export] *)
  do 2 zstep.
  zstep. if_true_by (nez_true Fb ltac:(lia)).
  burst_begin [(Fb, Fb + 64); (Z.shiftr Fb 3 + 2147450880, Z.shiftr Fb 3 + 2147450880 + 8)]%Z [Fb; (Z.shiftr Fb 3 + 2147450880)%Z] MUb WMb.
  do 7 zstep. neg_lits.
  do 3 zstep.
  do 3 zstep.
  do 2 zstep.
  do 4 zstep.
  zstep.
  zstep_sh0. do 3 zstep.
  burst_end MUb WMb.
  (* [comment removed for export] *)
  assert (G1n : GIOA L RNG s1' (CL ++ []) FB ([(FF_NG_CHECK_HEADER, Fb, 64%Z)] ++ FL) m2) by (rewrite app_nil_r; exact G1).
  assert (FW : Forall (own_ivA [(FF_NG_CHECK_HEADER, Fb, 64%Z)] ([] : list (@cblock hptr)) (bv_unsigned sp))
                 [(bv_unsigned sp - 272, bv_unsigned sp); (Fb, Fb + 64); (Z.shiftr Fb 3 + 2147450880, Z.shiftr Fb 3 + 2147450880 + 8)]%Z) by own_ivs.
  assert (FX : Forall (cobj_iv FL CL) [(ERR, ERR + 4); (EB, EB + 256)]%Z) by cobj_ivs.
  assert (FXB : Forall (fun iv : Z * Z => ablk (fst iv) (snd iv)) [(ERR, ERR + 4); (EB, EB + 256)]%Z)
    by (apply Forall_cons; [exact ERBAND'| apply Forall_cons; [exact EBBAND'| apply Forall_nil]]).
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    destruct (own_writes _ _ _ GL _ _ _ _ _ _ _ _ _ mm _ _ _ FW FX G1n MU WM ltac:(lia)) as [G2 AG2];
    assert (AGsh : agrees_on (in_frame_sh FL) m mm)
      by (eapply agrees_on_trans; [exact (keeps_frame_sh _ _ _ _ _ AGb)|]; exact (keepsx_frame_sh _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ _ G1 (incl_tl _ (incl_refl _)) AG2 FXB))
  end.
  pose proof (cobjA_keep _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ _ OERR G2 (incl_appl _ (incl_refl _)) (incl_tl _ (incl_refl _)) AGsh ltac:(lia)) as (_ & _ & _ & ERUNP & ERRNG & ERRSH & _).
  pose proof (cobjA_keep _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ _ OMG G2 (incl_appl _ (incl_refl _)) (incl_tl _ (incl_refl _)) AGsh ltac:(lia)) as (_ & _ & _ & MGUNP & MGRNG & MGRSH & _).
  (* [comment removed for export] *)
  unfold b8 in *.
  assert (RSP152 : rng RNG SPA 152) by (eapply rng_sub'; [exact RSPA| lia]).
  assert (SPALO : (17594333495296 <= SPA)%Z) by (atop_facts; lia).
    call ngc_magic_seq; [try eassumption .. | ]; [lia .. | ].
    lazymatch goal with HH : rw_cells asegs _ SPA _ |- _ => rename HH into FRA end.
    lazymatch goal with HH : rw_cells asegs _ ERR _ |- _ => rename HH into HE end.
    pose proof (magic_sx_range mg0 mg1 mg2 mg3 GM0 GM1 GM2 GM3) as WR.
    set (W := magic_sx mg0 mg1 mg2 mg3) in *.
  (* [comment removed for export] *)
  clear G2 AG2 AGsh.
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    destruct (own_writes _ _ _ GL _ _ _ _ _ _ _ _ _ mm _ _ _ FW FX G1n MU WM ltac:(lia)) as [G5 AG5] end.
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (AGm : agrees_on (fun a => client_keeps FL CL (bv_unsigned sp) a /\ outside [(ERR, ERR + 4); (EB, EB + 256)]%Z a) m mm)
      by (eapply agrees_on_trans; [eapply agrees_on_weaken; [exact AGb|]; intros a (K & _); exact K| exact AG5]) end.
  assert (CTX : ngc_ctx TP ra sp tp s0 L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f [mg0; mg1; mg2; mg3] m).
  { unfold ngc_ctx, PCAP_L2_STACK. do 5 (split; [first [assumption | lia]|]).
    split; [split; [exact RSTK| split; [exact RIMG| split; [exact RISH| exact RTLS]]]|].
    repeat (split; [first [assumption | reflexivity | lia]|]). first [assumption | lia]. }
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (INV : ngc_inv GIOA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo MG EB ERR SPA Fb [mg0; mg1; mg2; mg3] (ps_outfile s) m RNG s1' [] mm)
      by (unfold ngc_inv, ngc_shadow; split; [apply fp_le_refl|]; split; [exact G5|]; repeat (split; [first [assumption | reflexivity]|]); assumption) end.
  destruct (Z.eq_dec (mg0 + 256 * mg1 + 65536 * mg2 + 16777216 * mg3) BT_SHB) as [EQM|NEM].
  2:{ (* [comment removed for export] *)
    assert (WNE : W <> 168627466%Z) by (subst W; unfold magic_sx; unfold BT_SHB in NEM; clear - NEM GM0 GM1 GM2 GM3; dm_plia).
    zstep.
    if_cases K1; [|zify_cond K1; exfalso; lia].
    do 2 zstep.
  apply evtF_done. unfold ngc_head. rewrite le_of_bytes_4. rewrite (proj2 (Z.eqb_neq _ _) NEM). cbn [negb]. cbn [e_fret prims].
  subst POSTQ0 POSTQ.
  apply (rw_cells_split_CB asegs _ _ [_; _; _] 32 _ [_] [32]%nat) in FRC; [|reflexivity]. cbn [mk_CB_cells app] in FRC.
  eapply (ngc_exit FO GIOA TP fflagA GL FRET) with (fcs := [CB 32 (firstn 32 fjunk)]) (r := CH_NotMe);
    [exact CTX | exact INV | exact FRA | reflexivity | exact FRC | reflexivity | exact HE |].
  cbn [ngc_result]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. exists ej; exact HEB.
  }
    (* [comment removed for export] *)
    assert (E128 : W = 168627466%Z) by (subst W; unfold magic_sx; unfold BT_SHB in EQM; clear - EQM GM0 GM1 GM2 GM3; dm_plia).
    zstep.
    if_cases K1; [zify_cond K1; exfalso; lia|].
    do 2 zstep.
    do 5 zstep.
    zstep.
    replace (ret_pc (Z_to_bv 64 568972)) with (Z_to_bv 64 568972) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    clear G5 AG5 AGm INV.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      destruct (own_writes _ _ _ GL _ _ _ _ _ _ _ _ _ mm _ _ _ FW FX G1n MU WM ltac:(lia)) as [G6 AG6];
      assert (AGm : agrees_on (fun a => client_keeps FL CL (bv_unsigned sp) a /\ outside [(ERR, ERR + 4); (EB, EB + 256)]%Z a) m mm)
        by (eapply agrees_on_trans; [eapply agrees_on_weaken; [exact AGb|]; intros a (K & _); exact K| exact AG6]) end.
    cbn [app] in G6. rewrite app_nil_r in G6.
    assert (FRIN : forall a, (Fb <= a < Fb + 64)%Z -> in_frames ((FF_NG_CHECK_HEADER, Fb, 64%Z) :: FL) a)
      by (intros a Ha; apply in_frames_In; exists (FF_NG_CHECK_HEADER, Fb, 64%Z); split; [left; reflexivity| cbn [fb_addr fb_size fst snd]; lia]).
    assert (SHIN : forall a, (Z.shiftr Fb 3 + 2147450880 <= a < Z.shiftr Fb 3 + 2147450880 + 8)%Z -> in_frame_sh ((FF_NG_CHECK_HEADER, Fb, 64%Z) :: FL) a)
      by (intros a Ha; apply in_frame_sh_In; exists (FF_NG_CHECK_HEADER, Fb, 64%Z); split; [left; reflexivity| cbn [fb_addr fb_size fst snd]; change (Z.shiftr 64 3) with 8%Z; lia]).
    (* [comment removed for export] *)
    apply (rw_cells_split_CB asegs _ _ [_; _; _] 32 _ [_] [8; 4; 12; 4; 4]%nat) in FRC; [|reflexivity]. cbn [mk_CB_cells app] in FRC.
    destruct (rw_cells_cut _ _ _ 4 FRC) as [FK0 T1]. clear FRC. cbn [firstn skipn cells_size csize Nat.add] in FK0, T1.
    destruct (rw_cells_cut _ _ _ 1 T1) as [TLc T2]. clear T1. cbn [firstn skipn cells_size csize Nat.add] in TLc, T2.
    replace (Fb + Z.of_nat 32)%Z with (Fb + 32)%Z in * by lia. replace (Fb + 32 + Z.of_nat 4)%Z with (Fb + 36)%Z in * by lia.
    destruct (gl_frames _ _ _ GL _ _ _ _ _ _ _ G6) as [FAll6 _]. pose proof (Forall_inv FAll6) as FRM6. clear FAll6.
    pose proof (unp_of_sh_part _ _ _ 4%nat 0%nat 4 SHC ltac:(dm_plia) ltac:(lia) ltac:(cbn [cells_size csize Nat.add]; lia) eq_refl ltac:(cbn; lia) ltac:(lia)) as UNPT.
    change (8 * Z.of_nat 4)%Z with 32%Z in UNPT. change (8 * Z.of_nat 0 + 4)%Z with 4%Z in UNPT.
    remember (Z_to_bv 64 SPA) as spa eqn:Espa.
    assert (Hspa : bv_unsigned spa = SPA) by (rewrite Espa; apply unsigned_lit; lia).
    apply evtF_done. unfold ngc_head. rewrite le_of_bytes_4, EQM, Z.eqb_refl. cbn [negb mo_bind mo_ret MOps e_fread prims].
    eapply implMG_bind.
    { apply implMG_mget. cbn [eval_rdest].
      rewrite (gl_site _ _ _ GL _ _ _ _ _ _ _ _ _ _ SiteNgTotalLength 32 G6 (or_introl eq_refl) eq_refl).
      replace (Fb + 32 + 0)%Z with (Fb + 32)%Z by lia.
      eapply FREAD with (L := L) (s := s1') (CL := CL) (FB := FB) (FL := (FF_NG_CHECK_HEADER, Fb, 64%Z) :: FL) (lo := lo) (f := f) (Af := FA) (D := (Fb + 32)%Z) (n := 4%Z);
        [ split; [exact G6|]; rewrite Hspa; split; [exact ST1|]; split; [lia|]; split; [unfold STDIO_STACK; lia|]; split; [lia|];
          split; [assumption|]; split; [exact TPE|]; split; [dm_plia|];
          split; [exact RSTK|]; split; [exact RIMG|]; split; [exact RISH| exact RTLS]
        | exact HinF | reflexivity | reflexivity | reflexivity | reflexivity | lia | exact TLc
        | split; [right; exists (FF_NG_CHECK_HEADER, Fb, 64%Z); split; [left; reflexivity| cbn [fb_addr fb_size fst snd]; lia]|];
          eapply frameA_aobj; [exact FRM6| cbn [fb_addr fb_size fst snd]; lia| cbn [fb_addr fb_size fst snd]; lia| lia| exact UNPT] ]. }
    intros tlb s2' RNG2 ms' PO. cbv beta in PO.
    destruct PO as (FP2 & av & m6 & junk' & E & OF2 & MI2 & ST2 & AG7 & G7 & -> & GLN & GR & TL2).
    unfold hpost_regs in E. destruct_exs E. subst ms'. rewrite Hspa in *. clear Hspa. subst spa.
    replace (ret_pc (Z_to_bv 64 568972)) with (Z_to_bv 64 568972) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    repeat match goal with HR : rng RNG _ _ |- _ => apply (rng_fp_le _ _ _ _ FP2) in HR end.
    assert (ICL : incl CL CL) by apply incl_refl.
    assert (IFL : incl FL ((FF_NG_CHECK_HEADER, Fb, 64%Z) :: FL)) by (apply incl_tl, incl_refl).
    xf2 AG7 FR (left; lia). xf2 AG7 FRA (left; lia).
    xf2 AG7 FK0 (right; right; left; apply FRIN; lia). xf2 AG7 T2 (right; right; left; apply FRIN; lia).
    xf2 AG7 SHC (right; right; right; apply SHIN; lia).
    xf2 AG7 HEB (eapply clocA_keeps; [exact (clocA_incl _ _ _ _ _ _ (proj1 OEB) ICL IFL)| lia]).
    xf2 AG7 HE (eapply clocA_keeps; [exact (clocA_incl _ _ _ _ _ _ (proj1 OERR) ICL IFL)| lia]).
    xf2 AG7 MG4 (eapply clocA_keeps; [exact (clocA_incl _ _ _ _ _ _ (proj1 OMG) ICL IFL)| lia]).
    apply (agrees_stk _ _ _ _ _ AG7) in STG; [|intros a Ha; split; [left; lia| lia]].
    assert (AGm7 : agrees_on (fun a => client_keeps FL CL (bv_unsigned sp) a /\ outside [(ERR, ERR + 4); (EB, EB + 256)]%Z a) m m6).
    { eapply agrees_on_trans; [exact AGm|].
      eapply (ngc_keeps_callee FO GIOA fflagA GL) with (SPA := SPA) (Pn := fun a => ~ (Fb + 32 <= a < Fb + 32 + 4)%Z); [exact G6| exact ICL| atop_facts; lia| lia| exact AG7|].
      intros a K O NF0. cbn [fb_addr fb_size fst snd] in NF0. lia. }
    assert (INVB : forall RNGy sy my, fp_le RNG RNGy -> GIOA L RNGy sy (CL ++ []) FB ((FF_NG_CHECK_HEADER, Fb, 64%Z) :: FL) my -> ps_outfile sy = ps_outfile s ->
              mem_inv asegs my -> stk asegs my lo SPA -> stk asegs my (SPA + 152) (bv_unsigned sp + -104) ->
              rw_cells asegs my (bv_unsigned sp + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
              agrees_on (fun a => client_keeps FL CL (bv_unsigned sp) a /\ outside [(ERR, ERR + 4); (EB, EB + 256)]%Z a) m my ->
              rw_cells asegs my MG [C1 (Z_to_bv 8 mg0); C1 (Z_to_bv 8 mg1); C1 (Z_to_bv 8 mg2); C1 (Z_to_bv 8 mg3)] ->
              rw_cells asegs my (Z.shiftr Fb 3 + 2147450880) ngc_shadow ->
              ngc_inv GIOA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo MG EB ERR SPA Fb [mg0; mg1; mg2; mg3] (ps_outfile s) m RNGy sy [] my).
    { intros RNGy sy my X0 X1 X1' X2 X3 X4 X5 X6 X7 X8. unfold ngc_inv. split; [exact X0|]. split; [exact X1|]. split; [exact X1'|].
      repeat (split; [assumption|]). assumption. }
    assert (INV7 : ngc_inv GIOA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo MG EB ERR SPA Fb [mg0; mg1; mg2; mg3] (ps_outfile s) m RNG2 s2' [] m6).
    { apply INVB; [exact FP2| rewrite app_nil_r; exact G7| congruence| assumption| assumption| assumption| assumption| exact AGm7| assumption| unfold ngc_shadow; assumption]. }
    unfold zlength in *.
    (* [comment removed for export] *)
    assert (FRC7 : forall tcs, rw_cells asegs m6 (Fb + 32) tcs -> cells_size tcs = 4%nat ->
              exists fcs, rw_cells asegs m6 Fb ([C8 (Z_to_bv 64 1102416563); C8 (Z_to_bv 64 88380); C8 (Z_to_bv 64 568552)] ++ fcs ++ [C8 (Z_to_bv 64 (fflagA L FF_NG_CHECK_HEADER Fb))])
                          /\ cells_size fcs = 32%nat).
    { intros tcs HT HS.
      pose proof (rw_cells_uncut _ _ _ _ _ HT T2 ltac:(rewrite HS; lia)) as U1.
      pose proof (rw_cells_uncut _ _ _ _ _ FK0 U1 ltac:(cbn; lia)) as U2.
      exists ([CB 8 (firstn 8 fjunk)] ++ tcs ++ [CB 12 (firstn 12 (skipn 4 (skipn 8 fjunk))); CB 4 (firstn 4 (skipn 12 (skipn 4 (skipn 8 fjunk))));
               CB 4 (firstn 4 (skipn 4 (skipn 12 (skipn 4 (skipn 8 fjunk)))))]).
      split; [|rewrite !cells_size_app, HS; reflexivity].
      cbn [app] in U2 |- *. rewrite <- app_assoc. cbn [app]. exact U2. }
    destruct (Z.eq_dec (Z.of_nat (length tlb)) 4) as [L4|L4].
    2:{ (* [comment removed for export] *)
      replace (Z.of_nat (length tlb) <? 4)%Z with true by (symmetry; apply Z.ltb_lt; lia).
      destruct (FRC7 _ TL2 ltac:(cbn [cells_size csize Nat.add]; lia)) as (fcs7 & FRC7' & Hfcs7).
      pose proof (munch_refl ([] : list (Z * Z)) m6) as MU7. pose proof (wmono_refl asegs m6) as WM7.
      ienterG. zstep. zstep.
      if_cases K2; [zify_cond K2; exfalso; lia|].
      apply evtF_done. subst POSTQ1 POSTQ0 POSTQ.
      lazymatch goal with |- implMG _ _ _ _ (MS _ _ _ _ _ ?mm _) =>
        eapply (SHORT ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f [mg0; mg1; mg2; mg3] m (ps_outfile s) RNG2 s2' mm) with (pcx := 0x8ae94%Z);
          [ exact CTX | exact INV7 | left; reflexivity | exact FRA | exact FRC7' | exact Hfcs7 | exact HE | exact HEB ] end.
    }
    (* [comment removed for export] *)
    replace (Z.of_nat (length tlb) <? 4)%Z with false by (symmetry; apply Z.ltb_ge; lia).
    destruct (rw_cells_cut _ _ _ 1 TL2) as [TLc4 _]. cbn [firstn] in TLc4. replace (length tlb) with 4%nat in TLc4 by lia.
    destruct (rw_cells_cut _ _ _ 1 T2) as [T2a T2b]. clear T2. cbn [firstn skipn cells_size csize Nat.add] in T2a, T2b.
    destruct (rw_cells_cut _ _ _ 1 T2b) as [BOMc T3]. clear T2b. cbn [firstn skipn cells_size csize Nat.add] in BOMc, T3.
    replace (Fb + 36 + Z.of_nat 12)%Z with (Fb + 48)%Z in * by lia. replace (Fb + 48 + Z.of_nat 4)%Z with (Fb + 52)%Z in * by lia.
    destruct (gl_frames _ _ _ GL _ _ _ _ _ _ _ G7) as [FAll7 _]. pose proof (Forall_inv FAll7) as FRM7. clear FAll7.
    pose proof (unp_of_sh_part _ _ _ 6%nat 0%nat 4 SHC ltac:(dm_plia) ltac:(lia) ltac:(cbn [cells_size csize Nat.add]; lia) eq_refl ltac:(cbn; lia) ltac:(lia)) as UNPB.
    change (8 * Z.of_nat 6)%Z with 48%Z in UNPB. change (8 * Z.of_nat 0 + 4)%Z with 4%Z in UNPB.
    pose proof (munch_refl ([] : list (Z * Z)) m6) as MU7. pose proof (wmono_refl asegs m6) as WM7.
    ienterG. zstep. zstep.
    if_cases K2; [|zify_cond K2; exfalso; lia].
    do 5 zstep. zstep.
    replace (ret_pc (Z_to_bv 64 569088)) with (Z_to_bv 64 569088) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    remember (Z_to_bv 64 SPA) as spa eqn:Espa.
    assert (Hspa : bv_unsigned spa = SPA) by (rewrite Espa; apply unsigned_lit; lia).
    apply evtF_done. cbn [mo_bind mo_ret MOps e_fread prims].
    eapply implMG_bind.
    { apply implMG_mget. cbn [eval_rdest].
      rewrite (gl_site _ _ _ GL _ _ _ _ _ _ _ _ _ _ SiteNgByteOrderMagic 48 G7 (or_introl eq_refl) eq_refl).
      replace (Fb + 48 + 0)%Z with (Fb + 48)%Z by lia.
      eapply FREAD with (L := L) (s := s2') (CL := CL) (FB := FB) (FL := (FF_NG_CHECK_HEADER, Fb, 64%Z) :: FL) (lo := lo) (f := f) (Af := FA) (D := (Fb + 48)%Z) (n := 4%Z);
        [ split; [exact G7|]; rewrite Hspa; split; [exact ST2|]; split; [lia|]; split; [unfold STDIO_STACK; lia|]; split; [lia|];
          split; [assumption|]; split; [exact TPE|]; split; [dm_plia|];
          split; [exact RSTK|]; split; [exact RIMG|]; split; [exact RISH| exact RTLS]
        | exact HinF | reflexivity | reflexivity | reflexivity | reflexivity | lia | exact BOMc
        | split; [right; exists (FF_NG_CHECK_HEADER, Fb, 64%Z); split; [left; reflexivity| cbn [fb_addr fb_size fst snd]; lia]|];
          eapply frameA_aobj; [exact FRM7| cbn [fb_addr fb_size fst snd]; lia| cbn [fb_addr fb_size fst snd]; lia| lia| exact UNPB] ]. }
    intros bomb s3' RNG3 ms' PO. cbv beta in PO.
    destruct PO as (FP3 & av3 & m8 & junk3' & E & OF3 & MI3 & ST3 & AG8 & G8 & -> & GLN3 & GR3 & BOM2).
    unfold hpost_regs in E. destruct_exs E. subst ms'. rewrite Hspa in *. clear Hspa. subst spa.
    replace (ret_pc (Z_to_bv 64 569088)) with (Z_to_bv 64 569088) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    repeat match goal with HR : rng RNG2 _ _ |- _ => apply (rng_fp_le _ _ _ _ FP3) in HR end.
    xf2 AG8 FR (left; lia). xf2 AG8 FRA (left; lia).
    xf2 AG8 FK0 (right; right; left; apply FRIN; lia). xf2 AG8 TLc4 (right; right; left; apply FRIN; lia).
    xf2 AG8 T2a (right; right; left; apply FRIN; lia). xf2 AG8 T3 (right; right; left; apply FRIN; lia).
    xf2 AG8 SHC (right; right; right; apply SHIN; lia).
    xf2 AG8 HEB (eapply clocA_keeps; [exact (clocA_incl _ _ _ _ _ _ (proj1 OEB) ICL IFL)| lia]).
    xf2 AG8 HE (eapply clocA_keeps; [exact (clocA_incl _ _ _ _ _ _ (proj1 OERR) ICL IFL)| lia]).
    xf2 AG8 MG4 (eapply clocA_keeps; [exact (clocA_incl _ _ _ _ _ _ (proj1 OMG) ICL IFL)| lia]).
    apply (agrees_stk _ _ _ _ _ AG8) in STG; [|intros a Ha; split; [left; lia| lia]].
    assert (AGm8 : agrees_on (fun a => client_keeps FL CL (bv_unsigned sp) a /\ outside [(ERR, ERR + 4); (EB, EB + 256)]%Z a) m m8).
    { eapply agrees_on_trans; [exact AGm7|].
      eapply (ngc_keeps_callee FO GIOA fflagA GL) with (SPA := SPA) (Pn := fun a => ~ (Fb + 48 <= a < Fb + 48 + 4)%Z); [exact G7| exact ICL| atop_facts; lia| lia| exact AG8|].
      intros a K O NF0. cbn [fb_addr fb_size fst snd] in NF0. lia. }
    assert (INV8 : ngc_inv GIOA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo MG EB ERR SPA Fb [mg0; mg1; mg2; mg3] (ps_outfile s) m RNG3 s3' [] m8).
    { apply INVB; [eapply fp_le_trans; [exact FP2| exact FP3]| rewrite app_nil_r; exact G8| congruence| assumption| assumption| assumption| assumption| exact AGm8| assumption| unfold ngc_shadow; assumption]. }
    unfold zlength in *.
    assert (BSZ : cells_size [CB (length bomb) (map b8 bomb); CB (Z.to_nat 4 - length bomb) junk3'] = 4%nat)
      by (cbn [cells_size csize Nat.add]; change (Z.to_nat 4) with 4%nat; lia).
    pose proof (rw_cells_uncut _ _ _ _ _ BOM2 T3 ltac:(rewrite BSZ; lia)) as U1.
    pose proof (rw_cells_uncut _ _ _ _ _ T2a U1 ltac:(cbn [cells_size csize Nat.add]; lia)) as U2.
    pose proof (rw_cells_uncut _ _ _ _ _ TLc4 U2 ltac:(cbn [cells_size csize Nat.add]; lia)) as U3.
    pose proof (rw_cells_uncut _ _ _ _ _ FK0 U3 ltac:(cbn [cells_size csize Nat.add]; lia)) as U4.
    cbn [app] in U4.
    destruct (Z.eq_dec (Z.of_nat (length bomb)) 4) as [L4b|L4b].
    2:{ (* [comment removed for export] *)
      replace (Z.of_nat (length bomb) <? 4)%Z with true by (symmetry; apply Z.ltb_lt; lia).
      pose proof (munch_refl ([] : list (Z * Z)) m8) as MU8. pose proof (wmono_refl asegs m8) as WM8.
      ienterG. zstep.
      if_cases K3; [zify_cond K3; exfalso; lia|].
      apply evtF_done. subst POSTQ2 POSTQ1 POSTQ0 POSTQ.
      lazymatch goal with |- implMG _ _ _ _ (MS _ _ _ _ _ ?mm _) =>
        eapply (SHORT ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f [mg0; mg1; mg2; mg3] m (ps_outfile s) RNG3 s3' mm) with (pcx := 0x8af04%Z)
               (fcs := [CB 8 (firstn 8 fjunk); CB 4 (map b8 tlb); CB 12 (firstn 12 (skipn 4 (skipn 8 fjunk)));
                        CB (length bomb) (map b8 bomb); CB (Z.to_nat 4 - length bomb) junk3'; CB 4 (firstn 4 (skipn 4 (skipn 12 (skipn 4 (skipn 8 fjunk)))))]);
          [ exact CTX | exact INV8 | right; reflexivity | exact FRA | exact U4 | cbn [cells_size csize Nat.add]; change (Z.to_nat 4) with 4%nat; lia | exact HE | exact HEB ] end.
    }
    (* [comment removed for export] *)
    replace (Z.of_nat (length bomb) <? 4)%Z with false by (symmetry; apply Z.ltb_ge; lia).
    replace (length bomb) with 4%nat in U4 by lia. change (Z.to_nat 4 - 4)%nat with 0%nat in U4.
    pose proof (munch_refl ([] : list (Z * Z)) m8) as MU8. pose proof (wmono_refl asegs m8) as WM8.
    ienterG. zstep.
    if_cases K3; [|zify_cond K3; exfalso; lia].
    apply evtF_done. subst POSTQ2 POSTQ1 POSTQ0 POSTQ.
    destruct (rw_cells_cut _ _ _ 1 BOM2) as [BOMc4 _]. cbn [firstn] in BOMc4. replace (length bomb) with 4%nat in BOMc4 by lia.
    pose proof (rw_cells_uncut _ _ _ _ _ BOMc4 T3 ltac:(cbn [cells_size csize Nat.add]; lia)) as V1.
    pose proof (rw_cells_uncut _ _ _ _ _ T2a V1 ltac:(cbn [cells_size csize Nat.add]; lia)) as V2.
    pose proof (rw_cells_uncut _ _ _ _ _ TLc4 V2 ltac:(cbn [cells_size csize Nat.add]; lia)) as V3.
    pose proof (rw_cells_uncut _ _ _ _ _ FK0 V3 ltac:(cbn [cells_size csize Nat.add]; lia)) as V4.
    cbn [app] in V4.
    lazymatch goal with |- implMG _ ?c _ _ _ => change c with (ngc_bomk HO FO sites fuel f tlb bomb) end.
    lazymatch goal with |- implMG _ _ _ _ (MS _ _ _ _ _ ?mm _) =>
      eapply (BOM fuel ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f [mg0; mg1; mg2; mg3] m (ps_outfile s) RNG3 s3' mm);
        [ exact CTX | exact INV8 | exact GR | lia | exact GR3 | lia | exact FRA | exact V4 | exact HE | exact HEB ] end.
  Qed.
  End Sz2.
  Theorem pcap_ng_check_header_headA : ltac:(let t := eval cbv delta [pcap_ng_check_header_headA__stmt] in pcap_ng_check_header_headA__stmt in exact t).
  Proof using BOM FENTER0 FREAD FRET GL SHORT. red. red. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CL FB FL trC lo MG FA EB ERR f magic ej ec. ltac2:(SecDiet.SzSec.closeP 'pcap_ng_check_header_headA__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End NgcHead.
End CANSEC1.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P Require UbGuardB.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Strings.String.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.StoreFast.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.FmtFacts.
(* [comment removed for export] *)
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.PerfKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FmtKitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.MonadGX.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.SfKitA__A3P.SfKitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_modelA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_defsA__A3P.F_ngchk_defsA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_defsA__A3P.F_ngchk_exitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit2__A3P.F_ngchk_failA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit2__A3P.F_ngchk_kitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_defsA__A3P.F_ngchk_fstmtA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_defsA__A3P.F_ngchk_hstmtA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_defsA__A3P.F_ngchk_hstmt2A.TwB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.UbGuardB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LeafA__A3P.F_ngchk_hsegA.TwB. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac dm_plia := first [ atop_facts; once ltac2:(let _ := LiaRel.lr_prune_b 101 in ()); Z.div_mod_to_equations; lia_tiers
                            | Z.div_mod_to_equations; lia ].
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= unp_store m a bs n Hn Ha Hl.
Local Ltac sl_store_extra m m' a bs n Hn Ha Hl CH ::= sl_store_extra_std m m' a bs n Hn Ha Hl CH.   (* [comment removed for export] *)
Local Ltac transport_call_extra segs W m m' MU WM ::= unp_call W m m' MU.
(* [comment removed for export] *)
Local Ltac oiv_lo_base k := lazymatch goal with |- (?lo0 <= ?lo)%Z /\ _ => d_split lo0 ltac:(fun X0 _ _ => d_split lo ltac:(fun X _ _ => constr_eq X0 X; k)) end.
Local Ltac oiv_orig :=
  first [ left; cbn [fst snd]; lia
        | right; right; left; apply Exists_cons_hd; cbn [fb_addr fb_size fst snd]; lia
        | right; right; right; apply Exists_cons_hd; cbn [fb_addr fb_size fst snd]; shr_consts; lia
        | right; left; first [ apply Exists_cons_hd | apply Exists_cons_tl; apply Exists_cons_hd | apply Exists_cons_tl; apply Exists_cons_tl; apply Exists_cons_hd ];
          cbn [cb_addr cb_size fst snd]; lia ].
Local Ltac own_iv1 ::=
  unfold own_ivA, iv_in_block, iv_in_frames, iv_in_frame_shadow;
  first [ right; right; left; apply Exists_cons_hd; cbn [fb_addr fb_size fst snd]; oiv_lo_base ltac:(lia)
        | right; right; right; apply Exists_cons_hd; cbn [fb_addr fb_size fst snd]; shr_consts; oiv_lo_base ltac:(lia)
        | right; left; first [ apply Exists_cons_hd | apply Exists_cons_tl; apply Exists_cons_hd | apply Exists_cons_tl; apply Exists_cons_tl; apply Exists_cons_hd ];
          cbn [cb_addr cb_size fst snd]; oiv_lo_base ltac:(lia)
        | oiv_orig ].
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Ltac hide H := lazymatch type of H with ?T => let X := fresh "AUX" in set (X := T) in H end.
Ltac unhide H := lazymatch type of H with ?X => subst X end.
Ltac ienterG := lazymatch goal with |- implMG _ _ _ ?Q _ => let QQ := fresh "POSTQ" in set (QQ := Q) end; apply implMG_from_evtF.

Tactic Notation "xf1" constr(AG) hyp(HH) tactic3(loc) :=
  apply (agrees_rw_cells _ _ _ _ _ AG) in HH;
  [| let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; cbn [cells_size csize Nat.add] in Ha; loc].
Tactic Notation "xf2" constr(AG) hyp(HH) tactic3(loc) :=
  apply (agrees_rw_cells _ _ _ _ _ AG) in HH;
  [| let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [loc| lia]].

Lemma land_m32H : forall x, (0 <= x < 2^64)%Z -> Z.land x 18446744073709551584 = (x - x mod 32)%Z.
Proof. intros x Hx. exact (land_align_down x 5 Hx ltac:(lia)). Qed.

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section NgcHead.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis FENTER0 : fenter_stmt_o FO GIOA fflagA 0 STACK_MALLOC_0.
  Hypothesis FRET : fret_inline_law FO GIOA fflagA.
  Hypothesis FREAD : fread_stmt_o HO GIOA.
  Hypothesis SHORT : ngc_short_stmt HO FO sites GIOA TP fflagA.
  Hypothesis BOM : ngc_bom_stmt HO FO sites GIOA TP fflagA.

  Definition pcap_ng_check_header_headA__stmt : Prop := pcap_ng_check_header_stmt HO FO sites GIOA TP.
  Section Sz2.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CL FB FL trC lo MG FA EB ERR f magic ej ec fuel : ltac2:(SecDiet.SzSec.tyM 'pcap_ng_check_header_headA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma pcap_ng_check_header_headA__body : ltac2:(SecDiet.SzSec.bodyP 'pcap_ng_check_header_headA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using BOM FENTER0 FREAD FRET GL SHORT.
    intros PRE UC TR NF HinF -> -> -> -> -> HMG MGR MGL HEB HERR ECS OMG OERR DME OEB DEE DEM ERR4 EB8.
    destruct PRE as (G & ST & LO & BU & SPT & MI & TPE & ALN & RSTK & RIMG & RISH & RTLS).
    pose proof (gl_rt _ _ _ GL _ _ _ _ _ _ _ G) as ((_ & GOT & _ & _ & SHB & SUA & _) & GSU). unfold GOT_UAR in GSU.
    unfold PCAP_L2_STACK in BU.
    assert (RSPW : rng RNG lo (bv_unsigned sp - lo)) by (eapply rng_sub'; [exact RSTK| lia]).
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof (clocA_below _ _ _ GL _ _ _ _ _ _ _ _ _ G (proj1 OMG)) as (MGLO & MGHI).
    pose proof (clocA_below _ _ _ GL _ _ _ _ _ _ _ _ _ G (proj1 OERR)) as (ERLO & ERHI).
    pose proof (clocA_below _ _ _ GL _ _ _ _ _ _ _ _ _ G (proj1 OEB)) as (EBLO & EBHI).
    pose proof (clocA_ablk _ _ _ GL _ _ _ _ _ _ _ _ _ G (proj1 OMG) ltac:(lia)) as MGBAND.
    pose proof (clocA_ablk _ _ _ GL _ _ _ _ _ _ _ _ _ G (proj1 OERR) ltac:(lia)) as ERBAND.
    pose proof (clocA_ablk _ _ _ GL _ _ _ _ _ _ _ _ _ G (proj1 OEB) ltac:(lia)) as EBBAND.
    pose proof MGBAND as MGBAND'. pose proof ERBAND as ERBAND'. pose proof EBBAND as EBBAND'.
    band_ind MGBAND bM. band_ind ERBAND bE. band_ind EBBAND bB.
    destruct magic as [|mg0 [|mg1 [|mg2 [|mg3 [|? ?]]]]]; try discriminate MGL. clear MGL.
    pose proof MGR as GR'. apply Forall_cons_iff in GR' as [GM0 GR']. apply Forall_cons_iff in GR' as [GM1 GR']. apply Forall_cons_iff in GR' as [GM2 GR']. apply Forall_cons_iff in GR' as [GM3 _].
    cbn [map] in HMG.
    assert (MG4 : rw_cells asegs m MG [C1 (b8 mg0); C1 (b8 mg1); C1 (b8 mg2); C1 (b8 mg3)]).
    { eapply rw_cells_recell; [exact HMG | cbn; repeat split; exact Logic.I | reflexivity]. }
    clear HMG.
    destruct (rw_cells_forget _ _ _ _ HERR) as [ecj HE]. clear HERR. cbn [cells_size] in HE. rewrite ECS in HE. change (4 + 0)%nat with 4%nat in HE.
    rewrite (ngc_head_eq MOps (prims HO FO sites)). cbn [e_fenter prims]. unfold PCAP_NG_CHECK_HEADER_ENTRY.
    remember (bv_unsigned sp - 256 - (bv_unsigned sp - 256) mod 32)%Z as SPA eqn:ESPA.
    assert (SPAP : (bv_unsigned sp - 272 <= SPA <= bv_unsigned sp - 256 /\ SPA mod 32 = 0 /\ (bv_unsigned sp + -256) - (bv_unsigned sp + -256) mod 32 = SPA)%Z)
      by (rewrite ESPA; dm_plia).
    destruct SPAP as (SPAB & SPA32 & ESPA').
    assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(bv_unsigned sp - 272, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    ienterG.
    (* [comment removed for export] *)
    zstep.
    carve_frame 104%nat ST. carve_frame 152%nat ST.
    zstep.
    do 13 zstep.
    zstep.
    zstep.
  rewrite land_m32H by lia. rewrite ESPA'.
  release_frame FR0 ST (bv_unsigned sp + -104)%Z.
  destruct (stk_split asegs _ lo (SPA + 152) (bv_unsigned sp + -104) ST ltac:(lia)) as [ST1 STG]. clear ST.
  destruct (stk_carve asegs _ lo (SPA + 152) 152 ST1 ltac:(cbn; lia)) as [STL [jA FRA]]. clear ST1.
  change (Z.of_nat 152) with 152%Z in STL, FRA. replace (SPA + 152 - 152)%Z with SPA in STL, FRA by lia.
  assert (RSPA : rng RNG SPA (bv_unsigned sp - SPA)) by (eapply rng_sub'; [exact RSTK| lia]).
  do 7 zstep.
  do 2 zstep.
  zstep.
  replace (sx32 (Z_to_bv 64 1)) with (Z_to_bv 64 1) by (vm_compute; reflexivity).
  zstep.
  zstep.
  zstep. if_false.
  do 2 zstep.
  (* [comment removed for export] *)
  assert (Gn : GIOA L RNG s (CL ++ []) FB FL m) by (rewrite app_nil_r; exact G).
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (FW0 : Forall (pcap_iv FL ([] : list (@cblock hptr))) [(bv_unsigned sp - 272, bv_unsigned sp)]%Z)
      by (apply Forall_cons; [left; cbn [fst snd]; lia| apply Forall_nil]);
    assert (G0 : GIOA L RNG s (CL ++ []) FB FL mm) by (eapply (gl_frame _ _ _ GL); [exact Gn | exact MU | exact WM | exact FW0]);
    assert (AGa : agrees_on (client_keeps FL CL (bv_unsigned sp)) m mm)
      by (eapply (gl_keeps _ _ _ GL _ _ _ _ _ _ FL []); [exact Gn | exact MU | exact WM | | lia];
          apply Forall_cons; [left; cbn [fst snd]; lia| apply Forall_nil])
  end.
  rename MU into MU0. rename WM into WM0. clear FW0.
  remember (Z_to_bv 64 SPA) as spa eqn:Espa.
  assert (Hspa : bv_unsigned spa = SPA) by (rewrite Espa; apply unsigned_lit; lia).
  apply evtF_done. eapply (FENTER0 _ spa).
  { split; [rewrite app_nil_r in G0; exact G0|]. rewrite Hspa. split; [exact STL|]. split; [lia|]. split; [unfold FAKE_STACK; lia|]. split; [lia|].
    split; [assumption|]. split; [exact TPE|]. split; [dm_plia|].
    split; [exact RSTK|]. split; [exact RIMG|]. split; [exact RISH| exact RTLS]. }
  { reflexivity. }
  { unfold ff_size, ff_class. lia. }
  { apply NF. left. reflexivity. }
  { reflexivity. }
  intros Fb s1' m2 j0 j1 j2 fjunk t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' G1 OF1 LC1 TL1 MI1 ST1 AG1 Fb0 LJ FRC SHC.
  rewrite Hspa in *. clear Hspa. subst spa.
  change (ff_size FF_NG_CHECK_HEADER) with 64%Z in *.
  change (Z.to_nat (64 - 32)) with 32%nat in *. change (Z.to_nat (64 / 8)) with 8%nat in *.
  apply sh_zero_cells in SHC. cbn [repeat] in SHC.
  replace (ret_pc (Z_to_bv 64 568476)) with (Z_to_bv 64 568476) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  destruct (gl_frames _ _ _ GL _ _ _ _ _ _ _ G1) as [FAll FND]. pose proof (Forall_inv FAll) as (FBAND' & FTOP' & F64 & _ & FRNG & FSRNG & _ & FSWR).
  cbn [fb_addr fb_size fst snd] in FBAND', FTOP', F64, FRNG, FSRNG, FSWR. clear FAll.
  change (Z.shiftr 64 3) with 8%Z in FSRNG, FSWR.
  band_ind FBAND' bF.
  (* [comment removed for export] *)
  apply (keeps_rw_cells_stack _ _ _ _ _ _ _ AG1) in FR; [|lia]. apply (keeps_rw_cells_stack _ _ _ _ _ _ _ AG1) in FRA; [|lia].
  apply (agrees_stk _ _ _ _ _ AG1) in STG; [|intros a Ha; left; lia].
  apply (agrees_rw_cells _ _ _ _ _ AG1) in MG4; [|intros a Ha; eapply clocA_keeps; [exact (proj1 OMG)| exact Ha]].
  apply (agrees_rw_cells _ _ _ _ _ AG1) in HE; [|intros a Ha; eapply clocA_keeps; [exact (proj1 OERR)| exact Ha]].
  apply (agrees_rw_cells _ _ _ _ _ AG1) in HEB; [|intros a Ha; eapply clocA_keeps; [exact (proj1 OEB)| exact Ha]].
  destruct (clocA_apart_frame _ _ _ GL _ _ _ _ _ _ _ _ _ _ G1 (proj1 OMG) ltac:(lia)) as (kM & kMr & kM1 & kM2).
  destruct (clocA_apart_frame _ _ _ GL _ _ _ _ _ _ _ _ _ _ G1 (proj1 OERR) ltac:(lia)) as (kE & kEr & kE1 & kE2).
  destruct (clocA_apart_frame _ _ _ GL _ _ _ _ _ _ _ _ _ _ G1 (proj1 OEB) ltac:(lia)) as (kB & kBr & kB1 & kB2).
  cbn [fb_addr fb_size fst snd] in kM1, kM2, kE1, kE2, kB1, kB2.
  assert (AGb : agrees_on (client_keeps FL CL (bv_unsigned sp)) m m2).
  { eapply agrees_on_trans; [exact AGa|]. eapply client_keeps_weaken; [exact AG1| lia| intros a Ha; exact Ha| apply incl_refl]. }
  assert (SHLO : (0x7fff8000 <= Z.shiftr Fb 3 + 2147450880 /\ Z.shiftr Fb 3 + 2147450880 + 8 <= 0x10007fff8000
                 /\ (Fb + 64 <= 0x7fff7000 \/ Z.shiftr Fb 3 + 2147450880 + 8 <= Fb))%Z)
    by (rewrite Z.shiftr_div_pow2 by lia; change (2^3)%Z with 8%Z; dm_plia).
  pose proof (munch_refl [(bv_unsigned sp - 272, bv_unsigned sp); (Fb, Fb + 64); (Z.shiftr Fb 3 + 2147450880, Z.shiftr Fb 3 + 2147450880 + 8); (ERR, ERR + 4); (EB, EB + 256)]%Z m2) as MU.
  pose proof (wmono_refl asegs m2) as WM.
  ienterG.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  do 3 zstep.
  zstep. if_true_by (nez_true Fb ltac:(lia)).
  zstep.
  burst_begin [(Fb, Fb + 64); (Z.shiftr Fb 3 + 2147450880, Z.shiftr Fb 3 + 2147450880 + 8)]%Z [Fb; (Z.shiftr Fb 3 + 2147450880)%Z] MUb WMb.
  do 6 zstep. neg_lits.
  do 3 zstep.
  do 3 zstep.
  do 2 zstep.
  do 4 zstep.
  zstep. neg_lits.
  zstep_sh0. do 3 zstep.
  burst_end MUb WMb.
  (* [comment removed for export] *)
  assert (G1n : GIOA L RNG s1' (CL ++ []) FB ([(FF_NG_CHECK_HEADER, Fb, 64%Z)] ++ FL) m2) by (rewrite app_nil_r; exact G1).
  assert (FW : Forall (own_ivA [(FF_NG_CHECK_HEADER, Fb, 64%Z)] ([] : list (@cblock hptr)) (bv_unsigned sp))
                 [(bv_unsigned sp - 272, bv_unsigned sp); (Fb, Fb + 64); (Z.shiftr Fb 3 + 2147450880, Z.shiftr Fb 3 + 2147450880 + 8)]%Z) by own_ivs.
  assert (FX : Forall (cobj_iv FL CL) [(ERR, ERR + 4); (EB, EB + 256)]%Z) by cobj_ivs.
  assert (FXB : Forall (fun iv : Z * Z => ablk (fst iv) (snd iv)) [(ERR, ERR + 4); (EB, EB + 256)]%Z)
    by (apply Forall_cons; [exact ERBAND'| apply Forall_cons; [exact EBBAND'| apply Forall_nil]]).
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    destruct (own_writes _ _ _ GL _ _ _ _ _ _ _ _ _ mm _ _ _ FW FX G1n MU WM ltac:(lia)) as [G2 AG2];
    assert (AGsh : agrees_on (in_frame_sh FL) m mm)
      by (eapply agrees_on_trans; [exact (keeps_frame_sh _ _ _ _ _ AGb)|]; exact (keepsx_frame_sh _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ _ G1 (incl_tl _ (incl_refl _)) AG2 FXB))
  end.
  pose proof (cobjA_keep _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ _ OERR G2 (incl_appl _ (incl_refl _)) (incl_tl _ (incl_refl _)) AGsh ltac:(lia)) as (_ & _ & _ & ERUNP & ERRNG & ERRSH & _).
  pose proof (cobjA_keep _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ _ OMG G2 (incl_appl _ (incl_refl _)) (incl_tl _ (incl_refl _)) AGsh ltac:(lia)) as (_ & _ & _ & MGUNP & MGRNG & MGRSH & _).
  (* [comment removed for export] *)
  unfold b8 in *.
  assert (RSP152 : rng RNG SPA 152) by (eapply rng_sub'; [exact RSPA| lia]).
  assert (SPALO : (17594333495296 <= SPA)%Z) by (atop_facts; lia).
    (* [comment removed for export] *)
    ub_null.
    zstep. ub_al 3%Z ltac:(exact ERR4). zstep. if_false.
    call ngc_magic_seq; [try eassumption .. | ]; [lia .. | ].
    lazymatch goal with HH : rw_cells asegs _ ERR _ |- _ => rename HH into HE end.
    pose proof (magic_sx_range mg0 mg1 mg2 mg3 GM0 GM1 GM2 GM3) as WR.
    set (W := magic_sx mg0 mg1 mg2 mg3) in *.
  (* [comment removed for export] *)
  clear G2 AG2 AGsh.
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    destruct (own_writes _ _ _ GL _ _ _ _ _ _ _ _ _ mm _ _ _ FW FX G1n MU WM ltac:(lia)) as [G5 AG5] end.
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (AGm : agrees_on (fun a => client_keeps FL CL (bv_unsigned sp) a /\ outside [(ERR, ERR + 4); (EB, EB + 256)]%Z a) m mm)
      by (eapply agrees_on_trans; [eapply agrees_on_weaken; [exact AGb|]; intros a (K & _); exact K| exact AG5]) end.
  assert (CTX : ngc_ctx TP ra sp tp s0 L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f [mg0; mg1; mg2; mg3] m).
  { unfold ngc_ctx, PCAP_L2_STACK. do 5 (split; [first [assumption | lia]|]).
    split; [split; [exact RSTK| split; [exact RIMG| split; [exact RISH| exact RTLS]]]|].
    repeat (split; [first [assumption | reflexivity | lia]|]). first [assumption | lia]. }
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (INV : ngc_inv GIOA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo MG EB ERR SPA Fb [mg0; mg1; mg2; mg3] (ps_outfile s) m RNG s1' [] mm)
      by (unfold ngc_inv, ngc_shadow; split; [apply fp_le_refl|]; split; [exact G5|]; repeat (split; [first [assumption | reflexivity]|]); assumption) end.
  destruct (Z.eq_dec (mg0 + 256 * mg1 + 65536 * mg2 + 16777216 * mg3) BT_SHB) as [EQM|NEM].
  2:{ (* [comment removed for export] *)
    assert (WNE : W <> 168627466%Z) by (subst W; unfold magic_sx; unfold BT_SHB in NEM; clear - NEM GM0 GM1 GM2 GM3; dm_plia).
    zstep.
    if_cases K1; [|zify_cond K1; exfalso; lia].
    do 2 zstep.
  apply evtF_done. unfold ngc_head. rewrite le_of_bytes_4. rewrite (proj2 (Z.eqb_neq _ _) NEM). cbn [negb]. cbn [e_fret prims].
  subst POSTQ0 POSTQ.
  apply (rw_cells_split_CB asegs _ _ [_; _; _] 32 _ [_] [32]%nat) in FRC; [|reflexivity]. cbn [mk_CB_cells app] in FRC.
  eapply (ngc_exit FO GIOA TP fflagA GL FRET) with (fcs := [CB 32 (firstn 32 fjunk)]) (r := CH_NotMe);
    [exact CTX | exact INV | exact FRA | reflexivity | exact FRC | reflexivity | exact HE |].
  cbn [ngc_result]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. exists ej; exact HEB.
  }
    (* [comment removed for export] *)
    assert (E128 : W = 168627466%Z) by (subst W; unfold magic_sx; unfold BT_SHB in EQM; clear - EQM GM0 GM1 GM2 GM3; dm_plia).
    zstep.
    if_cases K1; [zify_cond K1; exfalso; lia|].
    do 5 zstep.                          (* [comment removed for export] *)
    zstep.
    replace (ret_pc (Z_to_bv 64 568780)) with (Z_to_bv 64 568780) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    clear G5 AG5 AGm INV.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      destruct (own_writes _ _ _ GL _ _ _ _ _ _ _ _ _ mm _ _ _ FW FX G1n MU WM ltac:(lia)) as [G6 AG6];
      assert (AGm : agrees_on (fun a => client_keeps FL CL (bv_unsigned sp) a /\ outside [(ERR, ERR + 4); (EB, EB + 256)]%Z a) m mm)
        by (eapply agrees_on_trans; [eapply agrees_on_weaken; [exact AGb|]; intros a (K & _); exact K| exact AG6]) end.
    cbn [app] in G6. rewrite app_nil_r in G6.
    assert (FRIN : forall a, (Fb <= a < Fb + 64)%Z -> in_frames ((FF_NG_CHECK_HEADER, Fb, 64%Z) :: FL) a)
      by (intros a Ha; apply in_frames_In; exists (FF_NG_CHECK_HEADER, Fb, 64%Z); split; [left; reflexivity| cbn [fb_addr fb_size fst snd]; lia]).
    assert (SHIN : forall a, (Z.shiftr Fb 3 + 2147450880 <= a < Z.shiftr Fb 3 + 2147450880 + 8)%Z -> in_frame_sh ((FF_NG_CHECK_HEADER, Fb, 64%Z) :: FL) a)
      by (intros a Ha; apply in_frame_sh_In; exists (FF_NG_CHECK_HEADER, Fb, 64%Z); split; [left; reflexivity| cbn [fb_addr fb_size fst snd]; change (Z.shiftr 64 3) with 8%Z; lia]).
    (* [comment removed for export] *)
    apply (rw_cells_split_CB asegs _ _ [_; _; _] 32 _ [_] [8; 4; 12; 4; 4]%nat) in FRC; [|reflexivity]. cbn [mk_CB_cells app] in FRC.
    destruct (rw_cells_cut _ _ _ 4 FRC) as [FK0 T1]. clear FRC. cbn [firstn skipn cells_size csize Nat.add] in FK0, T1.
    destruct (rw_cells_cut _ _ _ 1 T1) as [TLc T2]. clear T1. cbn [firstn skipn cells_size csize Nat.add] in TLc, T2.
    replace (Fb + Z.of_nat 32)%Z with (Fb + 32)%Z in * by lia. replace (Fb + 32 + Z.of_nat 4)%Z with (Fb + 36)%Z in * by lia.
    destruct (gl_frames _ _ _ GL _ _ _ _ _ _ _ G6) as [FAll6 _]. pose proof (Forall_inv FAll6) as FRM6. clear FAll6.
    pose proof (unp_of_sh_part _ _ _ 4%nat 0%nat 4 SHC ltac:(dm_plia) ltac:(lia) ltac:(cbn [cells_size csize Nat.add]; lia) eq_refl ltac:(cbn; lia) ltac:(lia)) as UNPT.
    change (8 * Z.of_nat 4)%Z with 32%Z in UNPT. change (8 * Z.of_nat 0 + 4)%Z with 4%Z in UNPT.
    remember (Z_to_bv 64 SPA) as spa eqn:Espa.
    assert (Hspa : bv_unsigned spa = SPA) by (rewrite Espa; apply unsigned_lit; lia).
    apply evtF_done. unfold ngc_head. rewrite le_of_bytes_4, EQM, Z.eqb_refl. cbn [negb mo_bind mo_ret MOps e_fread prims].
    eapply implMG_bind.
    { apply implMG_mget. cbn [eval_rdest].
      rewrite (gl_site _ _ _ GL _ _ _ _ _ _ _ _ _ _ SiteNgTotalLength 32 G6 (or_introl eq_refl) eq_refl).
      replace (Fb + 32 + 0)%Z with (Fb + 32)%Z by lia.
      eapply FREAD with (L := L) (s := s1') (CL := CL) (FB := FB) (FL := (FF_NG_CHECK_HEADER, Fb, 64%Z) :: FL) (lo := lo) (f := f) (Af := FA) (D := (Fb + 32)%Z) (n := 4%Z);
        [ split; [exact G6|]; rewrite Hspa; split; [exact ST1|]; split; [lia|]; split; [unfold STDIO_STACK; lia|]; split; [lia|];
          split; [assumption|]; split; [exact TPE|]; split; [dm_plia|];
          split; [exact RSTK|]; split; [exact RIMG|]; split; [exact RISH| exact RTLS]
        | exact HinF | reflexivity | reflexivity | reflexivity | reflexivity | lia | exact TLc
        | split; [right; exists (FF_NG_CHECK_HEADER, Fb, 64%Z); split; [left; reflexivity| cbn [fb_addr fb_size fst snd]; lia]|];
          eapply frameA_aobj; [exact FRM6| cbn [fb_addr fb_size fst snd]; lia| cbn [fb_addr fb_size fst snd]; lia| lia| exact UNPT] ]. }
    intros tlb s2' RNG2 ms' PO. cbv beta in PO.
    destruct PO as (FP2 & av & m6 & junk' & E & OF2 & MI2 & ST2 & AG7 & G7 & -> & GLN & GR & TL2).
    unfold hpost_regs in E. destruct_exs E. subst ms'. rewrite Hspa in *. clear Hspa. subst spa.
    replace (ret_pc (Z_to_bv 64 568780)) with (Z_to_bv 64 568780) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    repeat match goal with HR : rng RNG _ _ |- _ => apply (rng_fp_le _ _ _ _ FP2) in HR end.
    assert (ICL : incl CL CL) by apply incl_refl.
    assert (IFL : incl FL ((FF_NG_CHECK_HEADER, Fb, 64%Z) :: FL)) by (apply incl_tl, incl_refl).
    xf2 AG7 FR (left; lia). xf2 AG7 FRA (left; lia).
    xf2 AG7 FK0 (right; right; left; apply FRIN; lia). xf2 AG7 T2 (right; right; left; apply FRIN; lia).
    xf2 AG7 SHC (right; right; right; apply SHIN; lia).
    xf2 AG7 HEB (eapply clocA_keeps; [exact (clocA_incl _ _ _ _ _ _ (proj1 OEB) ICL IFL)| lia]).
    xf2 AG7 HE (eapply clocA_keeps; [exact (clocA_incl _ _ _ _ _ _ (proj1 OERR) ICL IFL)| lia]).
    xf2 AG7 MG4 (eapply clocA_keeps; [exact (clocA_incl _ _ _ _ _ _ (proj1 OMG) ICL IFL)| lia]).
    apply (agrees_stk _ _ _ _ _ AG7) in STG; [|intros a Ha; split; [left; lia| lia]].
    assert (AGm7 : agrees_on (fun a => client_keeps FL CL (bv_unsigned sp) a /\ outside [(ERR, ERR + 4); (EB, EB + 256)]%Z a) m m6).
    { eapply agrees_on_trans; [exact AGm|].
      eapply (ngc_keeps_callee FO GIOA fflagA GL) with (SPA := SPA) (Pn := fun a => ~ (Fb + 32 <= a < Fb + 32 + 4)%Z); [exact G6| exact ICL| atop_facts; lia| lia| exact AG7|].
      intros a K O NF0. cbn [fb_addr fb_size fst snd] in NF0. lia. }
    assert (INVB : forall RNGy sy my, fp_le RNG RNGy -> GIOA L RNGy sy (CL ++ []) FB ((FF_NG_CHECK_HEADER, Fb, 64%Z) :: FL) my -> ps_outfile sy = ps_outfile s ->
              mem_inv asegs my -> stk asegs my lo SPA -> stk asegs my (SPA + 152) (bv_unsigned sp + -104) ->
              rw_cells asegs my (bv_unsigned sp + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
              agrees_on (fun a => client_keeps FL CL (bv_unsigned sp) a /\ outside [(ERR, ERR + 4); (EB, EB + 256)]%Z a) m my ->
              rw_cells asegs my MG [C1 (Z_to_bv 8 mg0); C1 (Z_to_bv 8 mg1); C1 (Z_to_bv 8 mg2); C1 (Z_to_bv 8 mg3)] ->
              rw_cells asegs my (Z.shiftr Fb 3 + 2147450880) ngc_shadow ->
              ngc_inv GIOA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo MG EB ERR SPA Fb [mg0; mg1; mg2; mg3] (ps_outfile s) m RNGy sy [] my).
    { intros RNGy sy my X0 X1 X1' X2 X3 X4 X5 X6 X7 X8. unfold ngc_inv. split; [exact X0|]. split; [exact X1|]. split; [exact X1'|].
      repeat (split; [assumption|]). assumption. }
    assert (INV7 : ngc_inv GIOA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo MG EB ERR SPA Fb [mg0; mg1; mg2; mg3] (ps_outfile s) m RNG2 s2' [] m6).
    { apply INVB; [exact FP2| rewrite app_nil_r; exact G7| congruence| assumption| assumption| assumption| assumption| exact AGm7| assumption| unfold ngc_shadow; assumption]. }
    unfold zlength in *.
    (* [comment removed for export] *)
    assert (FRC7 : forall tcs, rw_cells asegs m6 (Fb + 32) tcs -> cells_size tcs = 4%nat ->
              exists fcs, rw_cells asegs m6 Fb ([C8 (Z_to_bv 64 1102416563); C8 (Z_to_bv 64 88380); C8 (Z_to_bv 64 568348)] ++ fcs ++ [C8 (Z_to_bv 64 (fflagA L FF_NG_CHECK_HEADER Fb))])
                          /\ cells_size fcs = 32%nat).
    { intros tcs HT HS.
      pose proof (rw_cells_uncut _ _ _ _ _ HT T2 ltac:(rewrite HS; lia)) as U1.
      pose proof (rw_cells_uncut _ _ _ _ _ FK0 U1 ltac:(cbn; lia)) as U2.
      exists ([CB 8 (firstn 8 fjunk)] ++ tcs ++ [CB 12 (firstn 12 (skipn 4 (skipn 8 fjunk))); CB 4 (firstn 4 (skipn 12 (skipn 4 (skipn 8 fjunk))));
               CB 4 (firstn 4 (skipn 4 (skipn 12 (skipn 4 (skipn 8 fjunk)))))]).
      split; [|rewrite !cells_size_app, HS; reflexivity].
      cbn [app] in U2 |- *. rewrite <- app_assoc. cbn [app]. exact U2. }
    destruct (Z.eq_dec (Z.of_nat (length tlb)) 4) as [L4|L4].
    2:{ (* [comment removed for export] *)
      replace (Z.of_nat (length tlb) <? 4)%Z with true by (symmetry; apply Z.ltb_lt; lia).
      destruct (FRC7 _ TL2 ltac:(cbn [cells_size csize Nat.add]; lia)) as (fcs7 & FRC7' & Hfcs7).
      pose proof (munch_refl ([] : list (Z * Z)) m6) as MU7. pose proof (wmono_refl asegs m6) as WM7.
      ienterG. zstep. zstep.
      if_cases K2; [zify_cond K2; exfalso; lia|].
      apply evtF_done. subst POSTQ1 POSTQ0 POSTQ.
      lazymatch goal with |- implMG _ _ _ _ (MS _ _ _ _ _ ?mm _) =>
        eapply (SHORT ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f [mg0; mg1; mg2; mg3] m (ps_outfile s) RNG2 s2' mm) with (pcx := 0x8add4%Z);
          [ exact CTX | exact INV7 | left; reflexivity | exact FRA | exact FRC7' | exact Hfcs7 | exact HE | exact HEB ] end.
    }
    (* [comment removed for export] *)
    replace (Z.of_nat (length tlb) <? 4)%Z with false by (symmetry; apply Z.ltb_ge; lia).
    destruct (rw_cells_cut _ _ _ 1 TL2) as [TLc4 _]. cbn [firstn] in TLc4. replace (length tlb) with 4%nat in TLc4 by lia.
    destruct (rw_cells_cut _ _ _ 1 T2) as [T2a T2b]. clear T2. cbn [firstn skipn cells_size csize Nat.add] in T2a, T2b.
    destruct (rw_cells_cut _ _ _ 1 T2b) as [BOMc T3]. clear T2b. cbn [firstn skipn cells_size csize Nat.add] in BOMc, T3.
    replace (Fb + 36 + Z.of_nat 12)%Z with (Fb + 48)%Z in * by lia. replace (Fb + 48 + Z.of_nat 4)%Z with (Fb + 52)%Z in * by lia.
    destruct (gl_frames _ _ _ GL _ _ _ _ _ _ _ G7) as [FAll7 _]. pose proof (Forall_inv FAll7) as FRM7. clear FAll7.
    pose proof (unp_of_sh_part _ _ _ 6%nat 0%nat 4 SHC ltac:(dm_plia) ltac:(lia) ltac:(cbn [cells_size csize Nat.add]; lia) eq_refl ltac:(cbn; lia) ltac:(lia)) as UNPB.
    change (8 * Z.of_nat 6)%Z with 48%Z in UNPB. change (8 * Z.of_nat 0 + 4)%Z with 4%Z in UNPB.
    pose proof (munch_refl ([] : list (Z * Z)) m6) as MU7. pose proof (wmono_refl asegs m6) as WM7.
    ienterG. zstep. zstep.
    if_cases K2; [|zify_cond K2; exfalso; lia].
    do 5 zstep. zstep.
    replace (ret_pc (Z_to_bv 64 568908)) with (Z_to_bv 64 568908) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    remember (Z_to_bv 64 SPA) as spa eqn:Espa.
    assert (Hspa : bv_unsigned spa = SPA) by (rewrite Espa; apply unsigned_lit; lia).
    apply evtF_done. cbn [mo_bind mo_ret MOps e_fread prims].
    eapply implMG_bind.
    { apply implMG_mget. cbn [eval_rdest].
      rewrite (gl_site _ _ _ GL _ _ _ _ _ _ _ _ _ _ SiteNgByteOrderMagic 48 G7 (or_introl eq_refl) eq_refl).
      replace (Fb + 48 + 0)%Z with (Fb + 48)%Z by lia.
      eapply FREAD with (L := L) (s := s2') (CL := CL) (FB := FB) (FL := (FF_NG_CHECK_HEADER, Fb, 64%Z) :: FL) (lo := lo) (f := f) (Af := FA) (D := (Fb + 48)%Z) (n := 4%Z);
        [ split; [exact G7|]; rewrite Hspa; split; [exact ST2|]; split; [lia|]; split; [unfold STDIO_STACK; lia|]; split; [lia|];
          split; [assumption|]; split; [exact TPE|]; split; [dm_plia|];
          split; [exact RSTK|]; split; [exact RIMG|]; split; [exact RISH| exact RTLS]
        | exact HinF | reflexivity | reflexivity | reflexivity | reflexivity | lia | exact BOMc
        | split; [right; exists (FF_NG_CHECK_HEADER, Fb, 64%Z); split; [left; reflexivity| cbn [fb_addr fb_size fst snd]; lia]|];
          eapply frameA_aobj; [exact FRM7| cbn [fb_addr fb_size fst snd]; lia| cbn [fb_addr fb_size fst snd]; lia| lia| exact UNPB] ]. }
    intros bomb s3' RNG3 ms' PO. cbv beta in PO.
    destruct PO as (FP3 & av3 & m8 & junk3' & E & OF3 & MI3 & ST3 & AG8 & G8 & -> & GLN3 & GR3 & BOM2).
    unfold hpost_regs in E. destruct_exs E. subst ms'. rewrite Hspa in *. clear Hspa. subst spa.
    replace (ret_pc (Z_to_bv 64 568908)) with (Z_to_bv 64 568908) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    repeat match goal with HR : rng RNG2 _ _ |- _ => apply (rng_fp_le _ _ _ _ FP3) in HR end.
    xf2 AG8 FR (left; lia). xf2 AG8 FRA (left; lia).
    xf2 AG8 FK0 (right; right; left; apply FRIN; lia). xf2 AG8 TLc4 (right; right; left; apply FRIN; lia).
    xf2 AG8 T2a (right; right; left; apply FRIN; lia). xf2 AG8 T3 (right; right; left; apply FRIN; lia).
    xf2 AG8 SHC (right; right; right; apply SHIN; lia).
    xf2 AG8 HEB (eapply clocA_keeps; [exact (clocA_incl _ _ _ _ _ _ (proj1 OEB) ICL IFL)| lia]).
    xf2 AG8 HE (eapply clocA_keeps; [exact (clocA_incl _ _ _ _ _ _ (proj1 OERR) ICL IFL)| lia]).
    xf2 AG8 MG4 (eapply clocA_keeps; [exact (clocA_incl _ _ _ _ _ _ (proj1 OMG) ICL IFL)| lia]).
    apply (agrees_stk _ _ _ _ _ AG8) in STG; [|intros a Ha; split; [left; lia| lia]].
    assert (AGm8 : agrees_on (fun a => client_keeps FL CL (bv_unsigned sp) a /\ outside [(ERR, ERR + 4); (EB, EB + 256)]%Z a) m m8).
    { eapply agrees_on_trans; [exact AGm7|].
      eapply (ngc_keeps_callee FO GIOA fflagA GL) with (SPA := SPA) (Pn := fun a => ~ (Fb + 48 <= a < Fb + 48 + 4)%Z); [exact G7| exact ICL| atop_facts; lia| lia| exact AG8|].
      intros a K O NF0. cbn [fb_addr fb_size fst snd] in NF0. lia. }
    assert (INV8 : ngc_inv GIOA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo MG EB ERR SPA Fb [mg0; mg1; mg2; mg3] (ps_outfile s) m RNG3 s3' [] m8).
    { apply INVB; [eapply fp_le_trans; [exact FP2| exact FP3]| rewrite app_nil_r; exact G8| congruence| assumption| assumption| assumption| assumption| exact AGm8| assumption| unfold ngc_shadow; assumption]. }
    unfold zlength in *.
    assert (BSZ : cells_size [CB (length bomb) (map b8 bomb); CB (Z.to_nat 4 - length bomb) junk3'] = 4%nat)
      by (cbn [cells_size csize Nat.add]; change (Z.to_nat 4) with 4%nat; lia).
    pose proof (rw_cells_uncut _ _ _ _ _ BOM2 T3 ltac:(rewrite BSZ; lia)) as U1.
    pose proof (rw_cells_uncut _ _ _ _ _ T2a U1 ltac:(cbn [cells_size csize Nat.add]; lia)) as U2.
    pose proof (rw_cells_uncut _ _ _ _ _ TLc4 U2 ltac:(cbn [cells_size csize Nat.add]; lia)) as U3.
    pose proof (rw_cells_uncut _ _ _ _ _ FK0 U3 ltac:(cbn [cells_size csize Nat.add]; lia)) as U4.
    cbn [app] in U4.
    destruct (Z.eq_dec (Z.of_nat (length bomb)) 4) as [L4b|L4b].
    2:{ (* [comment removed for export] *)
      replace (Z.of_nat (length bomb) <? 4)%Z with true by (symmetry; apply Z.ltb_lt; lia).
      pose proof (munch_refl ([] : list (Z * Z)) m8) as MU8. pose proof (wmono_refl asegs m8) as WM8.
      ienterG. zstep.
      if_cases K3; [zify_cond K3; exfalso; lia|].
      apply evtF_done. subst POSTQ2 POSTQ1 POSTQ0 POSTQ.
      lazymatch goal with |- implMG _ _ _ _ (MS _ _ _ _ _ ?mm _) =>
        eapply (SHORT ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f [mg0; mg1; mg2; mg3] m (ps_outfile s) RNG3 s3' mm) with (pcx := 0x8ae50%Z)
               (fcs := [CB 8 (firstn 8 fjunk); CB 4 (map b8 tlb); CB 12 (firstn 12 (skipn 4 (skipn 8 fjunk)));
                        CB (length bomb) (map b8 bomb); CB (Z.to_nat 4 - length bomb) junk3'; CB 4 (firstn 4 (skipn 4 (skipn 12 (skipn 4 (skipn 8 fjunk)))))]);
          [ exact CTX | exact INV8 | right; reflexivity | exact FRA | exact U4 | cbn [cells_size csize Nat.add]; change (Z.to_nat 4) with 4%nat; lia | exact HE | exact HEB ] end.
    }
    (* [comment removed for export] *)
    replace (Z.of_nat (length bomb) <? 4)%Z with false by (symmetry; apply Z.ltb_ge; lia).
    replace (length bomb) with 4%nat in U4 by lia. change (Z.to_nat 4 - 4)%nat with 0%nat in U4.
    pose proof (munch_refl ([] : list (Z * Z)) m8) as MU8. pose proof (wmono_refl asegs m8) as WM8.
    ienterG. zstep.
    if_cases K3; [|zify_cond K3; exfalso; lia].
    apply evtF_done. subst POSTQ2 POSTQ1 POSTQ0 POSTQ.
    destruct (rw_cells_cut _ _ _ 1 BOM2) as [BOMc4 _]. cbn [firstn] in BOMc4. replace (length bomb) with 4%nat in BOMc4 by lia.
    pose proof (rw_cells_uncut _ _ _ _ _ BOMc4 T3 ltac:(cbn [cells_size csize Nat.add]; lia)) as V1.
    pose proof (rw_cells_uncut _ _ _ _ _ T2a V1 ltac:(cbn [cells_size csize Nat.add]; lia)) as V2.
    pose proof (rw_cells_uncut _ _ _ _ _ TLc4 V2 ltac:(cbn [cells_size csize Nat.add]; lia)) as V3.
    pose proof (rw_cells_uncut _ _ _ _ _ FK0 V3 ltac:(cbn [cells_size csize Nat.add]; lia)) as V4.
    cbn [app] in V4.
    lazymatch goal with |- implMG _ ?c _ _ _ => change c with (ngc_bomk HO FO sites fuel f tlb bomb) end.
    lazymatch goal with |- implMG _ _ _ _ (MS _ _ _ _ _ ?mm _) =>
      eapply (BOM fuel ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f [mg0; mg1; mg2; mg3] m (ps_outfile s) RNG3 s3' mm);
        [ exact CTX | exact INV8 | exact GR | lia | exact GR3 | lia | exact FRA | exact V4 | exact HE | exact HEB ] end.
  Qed.
  End Sz2.
  Theorem pcap_ng_check_header_headA : ltac:(let t := eval cbv delta [pcap_ng_check_header_headA__stmt] in pcap_ng_check_header_headA__stmt in exact t).
  Proof using BOM FENTER0 FREAD FRET GL SHORT. red. red. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CL FB FL trC lo MG FA EB ERR f magic ej ec fuel. ltac2:(SecDiet.SzSec.closeP 'pcap_ng_check_header_headA__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End NgcHead.
End CANSEC1.
End TwB.
End F_ngchk_headA.

(* [comment removed for export] *)
Module F_ngchk_hshortA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep Frame StoreFast Image.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require FmtFacts__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.FmtFacts.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow StepF SysStepF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg ABase AMalloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA LibcKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FrameKit__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FmtKitA F_ngchk_modelA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngchk_defsA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require LibcKit2__A3P. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.MonadGX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.PerfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FmtKitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_modelA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_defsA__A3P.F_ngchk_defsA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit2__A3P.F_ngchk_kitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_defsA__A3P.F_ngchk_exitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit2__A3P.F_ngchk_failA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_defsA__A3P.F_ngchk_hstmtA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= unp_store m a bs n Hn Ha Hl.
Local Ltac transport_call_extra segs W m m' MU WM ::= unp_call W m m' MU.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Ltac ienterG := lazymatch goal with |- implMG _ _ _ ?Q _ => let QQ := fresh "POSTQ" in set (QQ := Q) end; apply implMG_from_evtF.
Ltac post_regs E := unfold hpost_regs in E; destruct_exs E; lazymatch type of E with ?x = _ => subst x end;
  try (lazymatch goal with |- context [ret_pc (Z_to_bv 64 ?n)] =>
         replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) in * by (symmetry; apply ret_pc_even; [lia|reflexivity]) end).

Definition fmt_errmsg_length_ng__stmt : Prop := forall f args e, (length (fmt_errmsg f args e) <= 255)%nat.
Section Sz1.
Variables f args e : ltac2:(SecDiet.SzSec.tyM 'fmt_errmsg_length_ng__stmt "vvv" @f).
#[using="Type"] Lemma fmt_errmsg_length_ng__body : ltac2:(SecDiet.SzSec.bodyP 'fmt_errmsg_length_ng__stmt "vvv").
Proof.
 unfold fmt_errmsg, snprintf, snprintf_out, PCAP_ERRBUF_SIZE, zlength.
  set (mm := firstn (Z.to_nat (256 - 1)) (fmt_output (fmt f) args)).
  assert (Hm : (length mm <= 255)%nat) by (subst mm; rewrite length_firstn; apply Nat.le_min_l).
  destruct (256 <? Z.of_nat (length mm) + 3)%Z eqn:E; [exact Hm|].
  apply Z.ltb_ge in E. rewrite !length_app, length_firstn. cbn [length str String.list_ascii_of_string map].
  unfold str. cbn [String.list_ascii_of_string map length]. lia.
Qed.
End Sz1.
Lemma fmt_errmsg_length_ng : ltac:(let t := eval cbv delta [fmt_errmsg_length_ng__stmt] in fmt_errmsg_length_ng__stmt in exact t).
Proof. intros f args e. ltac2:(SecDiet.SzSec.closeP 'fmt_errmsg_length_ng__body "vvv"). Qed.

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section NgcShort.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis FRET : fret_inline_law FO GIOA fflagA.
  Hypothesis FERROR : ferror_stmt_o HO GIOA.
  Hypothesis FMT : fmt_errmsg_stmt FO GIOA.
  #[local] Notation cblk := (@cblock hptr).
  #[local] Notation NGFR Fb := (FF_NG_CHECK_HEADER, Fb, 64%Z).

  #[using="Type"] Lemma implMG_errno_ll : forall {B C} (f : Z -> Monad.M (PState H hptr) B) (g : B -> Monad.M (PState H hptr) C) (s : PState H hptr) RNG Q ms,
    implMG RNG (mbind (f (lc_errno (ps_libc s))) g) s Q ms -> implMG RNG (mbind (mbind (s_get_errno (H:=H) (hptr:=hptr)) f) g) s Q ms.
  Proof. intros B C f g s RNG Q ms HH. exact HH. Qed.

  Definition ngc_short__stmt : Prop := ngc_short_stmt HO FO sites GIOA TP fflagA.
  Section Sz3.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic m o RNGx sx mm ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r21 r23 r24 t3 t4 t5 t6 pcx j0 j j2 fcs k0 k1 k2 e : ltac2:(SecDiet.SzSec.tyM 'ngc_short__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma ngc_short__body : ltac2:(SecDiet.SzSec.bodyP 'ngc_short__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL FRET FERROR FMT.
 intros CTX INV HPC FRA FRC Hfcs HE HEB.
    ngc_setup GL CTX INV.
    assert (ESPA : bv_unsigned (Z_to_bv 64 SPA) = SPA) by (apply unsigned_lit; lia).
    cbn [mo_bind mo_ret MOps e_ferror e_fret prims].
    pose proof (munch_refl ([] : list (Z * Z)) mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    ienterG.
    destruct HPC as [-> | ->].
    all: zstep; zstep.
    all: clear MU WM.
    all: apply evtF_done; subst POSTQ; eapply implMG_bind;
      [ eapply FERROR with (L := L) (s := sx) (CL := (CL ++ [])%list) (FB := FB) (FL := NGFR Fb :: FL) (lo := lo) (f := f) (Af := FA);
        [ eapply (ngc_spo GIOA TP); [exact CTX| exact FP| exact G| exact ST| exact MI| unfold STDIO_STACK, PCAP_L2_STACK; lia] | exact HinF | reflexivity ] |].
    all: intros r sy RNGy msy PO; cbv beta in PO; destruct PO as (FPy & a0v & my & E & MIy & STy & AGy & Gy & -> & -> & ERRNO).
    all: rewrite ESPA in *; post_regs E.
    all: assert (INVy : ngc_inv GIOA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo MG EB ERR SPA Fb [mg0; mg1; mg2; mg3] o m RNGy sx [] my)
           by (eapply (ngc_inv_keep FO GIOA TP fflagA GL) with (CLk := (CL ++ [])%list) (Pn := fun _ : Z => True);
               [exact CTX| exact INV| exact FPy| exact Gy| reflexivity| exact MIy| exact STy| eapply agrees_on_weaken; [exact AGy| intros a (K & _); exact K]
               | apply incl_appl, incl_refl| exact G| intros; exact Logic.I]).
    all: assert (KEEP : forall A cs, rw_cells asegs mm A cs ->
                     ((SPA <= A) \/ (Fb <= A /\ A + Z.of_nat (cells_size cs) <= Fb + 64) \/ (ERR = A /\ cells_size cs = 4%nat) \/ (EB = A /\ cells_size cs = 256%nat))%Z -> rw_cells asegs my A cs)
           by (intros A cs HC HA; eapply agrees_rw_cells; [exact AGy| exact HC|]; intros a Ha;
               destruct HA as [HA|[HA|[HA|HA]]];
               [ left; lia
               | right; right; left; apply Exists_cons_hd; cbn [fb_addr fb_size fst snd]; lia
               | destruct HA as (<- & HS); rewrite HS in Ha; eapply clocA_keeps; [exact (clocA_incl _ _ _ _ _ _ (proj1 OERR) ICL IFL)| lia]
               | destruct HA as (<- & HS); rewrite HS in Ha; eapply clocA_keeps; [exact (clocA_incl _ _ _ _ _ _ (proj1 OEB) ICL IFL)| lia] ]).
    all: pose proof (KEEP _ _ FRA ltac:(left; lia)) as FRAy.
    all: pose proof (KEEP _ _ FRC ltac:(right; left; rewrite !cells_size_app, Hfcs; cbn [cells_size csize Nat.add]; lia)) as FRCy.
    all: pose proof (KEEP _ _ HE ltac:(right; right; left; split; reflexivity)) as HEy.
    all: pose proof (KEEP _ _ HEB ltac:(right; right; right; split; reflexivity)) as HEBy.
    all: clear KEEP.
    all: repeat match goal with HR : rng _ _ _ |- _ => apply (rng_fp_le _ _ _ _ FPy) in HR end.
    all: pose proof (munch_refl ([] : list (Z * Z)) my) as MU; pose proof (wmono_refl asegs my) as WM.
    all: destruct r.
    (* [comment removed for export] *)
    2,4: apply implMG_retb; cbn [Z.b2z]; ienterG; zstep; if_true;
         apply evtF_done; subst POSTQ;
         eapply (ngc_exit FO GIOA TP fflagA GL FRET) with (PB := ([] : list cblk)) (fcs := fcs) (k0 := k0) (k1 := k1) (k2 := k2) (ew := z64) (r := CH_NotMe);
           [ exact CTX | exact INVy | exact FRAy | reflexivity | exact FRCy | exact Hfcs | exact HEy
           | cbn [ngc_result]; split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|]; exists e; exact HEBy ].
    all: destruct (ERRNO eq_refl) as [EN2 ER]; clear ERRNO.
    all: unfold errmsg_for_errno; cbn [mo_bind mo_ret MOps e_last_errno e_fenter e_fret prims].
    all: apply implMG_errno_ll; set (en := lc_errno (ps_libc sx)) in *.
    all: destruct (gl_tls _ _ _ GL _ _ _ _ _ _ _ Gy RTLS) as (T0 & T47 & TUNP & TRNG & (RLO & RHI & TA1 & TA2 & TA3 & TA4 & TA5 & TA6 & TA7 & TA8) & _).
    all: assert (ETP : bv_unsigned tp = ATP) by (rewrite TPE; unfold ATP; pose proof atp_lin; apply unsigned_lit; lia).
    all: assert (MSG : fmt_at my 0x22080 "error reading dump file"%string)
           by (split; [exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image asegs my 0x22080 (map (fun c => Z_to_bv 8 (Z.of_nat (Ascii.nat_of_ascii c))) (String.list_ascii_of_string "error reading dump file"%string) ++ [Z_to_bv 8 0])
                                MIy ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)))|];
               split; [lia|]; split; [cbn; lia|]; unfold client_globals; repeat (first [left; reflexivity | right])).
    all: edestruct (ngc_cobj_now FO GIOA TP fflagA GL) as (_ & _ & OEB'); [exact CTX| exact INVy|].
    all: cbn [Z.b2z]; ienterG; zstep; if_false.
    all: zstep; do 3 zstep; rewrite ETP.
    1: ck TUNP 4%Z 0x8aeb4%Z [11%Z; 12%Z].
    2: ck TUNP 4%Z 0x8af24%Z [11%Z; 12%Z].
    all: zstep.
    all: do 4 zstep; zstep.
    all: replace (sx32 (Z_to_bv 64 en)) with (Z_to_bv 64 (s32 en)) by (unfold sx32, s32; rewrite unsigned_lit by lia; f_equal; unfold bv_swrap, bv_wrap; cbn; lia).
    all: apply evtF_done; subst POSTQ; eapply implMG_bind;
      [ eapply FMT with (L := L) (s := sx) (CL := (CL ++ [])%list) (FB := FB) (FL := NGFR Fb :: FL) (lo := lo) (EB := EB)
                        (FMTA := 0x22080%Z) (e := en) (fs := "error reading dump file"%string) (args := ([] : list farg)) (junk := e);
          [ eapply (ngc_spo GIOA TP); [exact CTX| eapply fp_le_trans; [exact FP| exact FPy]| exact Gy| exact STy| exact MIy| unfold PCAP_L1_STACK, PCAP_L2_STACK; lia]
          | cbn [map fb_fn fst]; intros [X|X]; [discriminate X|];
            exact (NF FF_FMT_ERRMSG ltac:(unfold frames_check_header, frames_pcap_ng_check_header; right; left; reflexivity) X)
          | reflexivity | reflexivity | reflexivity | lia | reflexivity | exact MSG | reflexivity | cbn; lia | constructor
          | exact HEBy | split; [exact (clocA_incl _ _ _ _ _ _ (proj1 OEB') ICL IFL)| exact (proj2 OEB')] | exact EB8 ] |].
    all: intros r4 s4' RNG4 ms4 PO; cbv beta in PO; destruct PO as (FP4 & -> & PO); destruct_exs PO.
    all: destruct PO as (-> & OF4 & LC4 & TL4 & MI4 & ST4 & AG4 & G4 & HEB4).
    all: rewrite ESPA in *.
    all: try (lazymatch goal with |- context [ret_pc (Z_to_bv 64 ?n)] =>
         replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) in * by (symmetry; apply ret_pc_even; [lia|reflexivity]) end).
    all: lazymatch type of AG4 with agrees_on _ _ ?m4 =>
           assert (INV4 : ngc_inv GIOA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo MG EB ERR SPA Fb [mg0; mg1; mg2; mg3] o m RNG4 s4' [] m4)
             by (eapply (ngc_inv_keep FO GIOA TP fflagA GL) with (CLk := (CL ++ [])%list) (Pn := fun a : Z => ~ (EB <= a < EB + 256)%Z);
                 [exact CTX| exact INVy| exact FP4| exact G4| exact OF4| exact MI4| exact ST4| exact AG4| apply incl_appl, incl_refl| exact Gy| intros a N1 N2; exact N1]);
           assert (KEEP : forall A cs, rw_cells asegs my A cs ->
                     ((SPA <= A) \/ (Fb <= A /\ A + Z.of_nat (cells_size cs) <= Fb + 64) \/ (ERR = A /\ cells_size cs = 4%nat))%Z -> rw_cells asegs m4 A cs)
             by (intros A cs HC HA; eapply agrees_rw_cells; [exact AG4| exact HC|]; intros a Ha;
                 destruct HA as [HA|[HA|HA]];
                 [ split; [left; lia| lia]
                 | split; [right; right; left; apply Exists_cons_hd; cbn [fb_addr fb_size fst snd]; lia| lia]
                 | destruct HA as (<- & HS); rewrite HS in Ha; split; [eapply clocA_keeps; [exact (clocA_incl _ _ _ _ _ _ (proj1 OERR) ICL IFL)| lia]| lia] ]) end.
    all: pose proof (KEEP _ _ FRAy ltac:(left; lia)) as FRA4.
    all: pose proof (KEEP _ _ FRCy ltac:(right; left; rewrite !cells_size_app, Hfcs; cbn [cells_size csize Nat.add]; lia)) as FRC4.
    all: pose proof (KEEP _ _ HEy ltac:(right; right; split; reflexivity)) as HE4.
    1: eapply (ngc_failx FO GIOA TP fflagA GL FRET) with (fcs := fcs) (k0 := k0) (k1 := k1) (k2 := k2) (pcX := 0x8aecc%Z) (msg := fmt_errmsg "error reading dump file" [] en);
        [ exact CTX | exact INV4 | left; reflexivity | exact FRA4 | reflexivity | exact FRC4 | exact Hfcs | exact HE4 | exact HEB4
        | pose proof (fmt_errmsg_length_ng "error reading dump file" [] en); lia
        | apply fmt_errmsg_ok; [vm_compute; reflexivity| apply args_ok_nil] ].
    eapply (ngc_failx FO GIOA TP fflagA GL FRET) with (fcs := fcs) (k0 := k0) (k1 := k1) (k2 := k2) (pcX := 0x8af3c%Z) (msg := fmt_errmsg "error reading dump file" [] en);
        [ exact CTX | exact INV4 | right; left; reflexivity | exact FRA4 | reflexivity | exact FRC4 | exact Hfcs | exact HE4 | exact HEB4
        | pose proof (fmt_errmsg_length_ng "error reading dump file" [] en); lia
        | apply fmt_errmsg_ok; [vm_compute; reflexivity| apply args_ok_nil] ].
  Qed.
  End Sz3.
  Theorem ngc_short : ltac:(let t := eval cbv delta [ngc_short__stmt] in ngc_short__stmt in exact t).
  Proof using GL FRET FERROR FMT. red. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic m o RNGx sx mm ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r21 r23 r24 t3 t4 t5 t6 pcx j0 j j2 fcs k0 k1 k2 e. ltac2:(SecDiet.SzSec.closeP 'ngc_short__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End NgcShort.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Strings.String.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.StoreFast OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Image.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.FmtFacts.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB.
(* [comment removed for export] *)
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.MonadGX.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.PerfKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FmtKitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_modelA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_defsA__A3P.F_ngchk_defsA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit2__A3P.F_ngchk_kitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_defsA__A3P.F_ngchk_exitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit2__A3P.F_ngchk_failA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_defsA__A3P.F_ngchk_hstmtA.TwB. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= unp_store m a bs n Hn Ha Hl.
Local Ltac transport_call_extra segs W m m' MU WM ::= unp_call W m m' MU.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Ltac ienterG := lazymatch goal with |- implMG _ _ _ ?Q _ => let QQ := fresh "POSTQ" in set (QQ := Q) end; apply implMG_from_evtF.
Ltac post_regs E := unfold hpost_regs in E; destruct_exs E; lazymatch type of E with ?x = _ => subst x end;
  try (lazymatch goal with |- context [ret_pc (Z_to_bv 64 ?n)] =>
         replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) in * by (symmetry; apply ret_pc_even; [lia|reflexivity]) end).

Definition fmt_errmsg_length_ng__stmt : Prop := forall f args e, (length (fmt_errmsg f args e) <= 255)%nat.
Section Sz1.
Variables f args e : ltac2:(SecDiet.SzSec.tyM 'fmt_errmsg_length_ng__stmt "vvv" @f).
#[using="Type"] Lemma fmt_errmsg_length_ng__body : ltac2:(SecDiet.SzSec.bodyP 'fmt_errmsg_length_ng__stmt "vvv").
Proof.
 unfold fmt_errmsg, snprintf, snprintf_out, PCAP_ERRBUF_SIZE, zlength.
  set (mm := firstn (Z.to_nat (256 - 1)) (fmt_output (fmt f) args)).
  assert (Hm : (length mm <= 255)%nat) by (subst mm; rewrite length_firstn; apply Nat.le_min_l).
  destruct (256 <? Z.of_nat (length mm) + 3)%Z eqn:E; [exact Hm|].
  apply Z.ltb_ge in E. rewrite !length_app, length_firstn. cbn [length str String.list_ascii_of_string map].
  unfold str. cbn [String.list_ascii_of_string map length]. lia.
Qed.
End Sz1.
Lemma fmt_errmsg_length_ng : ltac:(let t := eval cbv delta [fmt_errmsg_length_ng__stmt] in fmt_errmsg_length_ng__stmt in exact t).
Proof. intros f args e. ltac2:(SecDiet.SzSec.closeP 'fmt_errmsg_length_ng__body "vvv"). Qed.

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section NgcShort.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis FRET : fret_inline_law FO GIOA fflagA.
  Hypothesis FERROR : ferror_stmt_o HO GIOA.
  Hypothesis FMT : fmt_errmsg_stmt FO GIOA.
  #[local] Notation cblk := (@cblock hptr).
  #[local] Notation NGFR Fb := (FF_NG_CHECK_HEADER, Fb, 64%Z).

  #[using="Type"] Lemma implMG_errno_ll : forall {B C} (f : Z -> Monad.M (PState H hptr) B) (g : B -> Monad.M (PState H hptr) C) (s : PState H hptr) RNG Q ms,
    implMG RNG (mbind (f (lc_errno (ps_libc s))) g) s Q ms -> implMG RNG (mbind (mbind (s_get_errno (H:=H) (hptr:=hptr)) f) g) s Q ms.
  Proof. intros B C f g s RNG Q ms HH. exact HH. Qed.

  Definition ngc_short__stmt : Prop := ngc_short_stmt HO FO sites GIOA TP fflagA.
  Section Sz3.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic m o RNGx sx mm ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r22 r23 r24 t3 t4 t5 t6 pcx j0 j j2 fcs k0 k1 k2 e : ltac2:(SecDiet.SzSec.tyM 'ngc_short__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma ngc_short__body : ltac2:(SecDiet.SzSec.bodyP 'ngc_short__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL FRET FERROR FMT.
 intros CTX INV HPC FRA FRC Hfcs HE HEB.
    ngc_setup GL CTX INV.
    assert (ESPA : bv_unsigned (Z_to_bv 64 SPA) = SPA) by (apply unsigned_lit; lia).
    cbn [mo_bind mo_ret MOps e_ferror e_fret prims].
    pose proof (munch_refl ([] : list (Z * Z)) mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    ienterG.
    destruct HPC as [-> | ->].
    all: zstep; zstep.
    all: clear MU WM.
    all: apply evtF_done; subst POSTQ; eapply implMG_bind;
      [ eapply FERROR with (L := L) (s := sx) (CL := (CL ++ [])%list) (FB := FB) (FL := NGFR Fb :: FL) (lo := lo) (f := f) (Af := FA);
        [ eapply (ngc_spo GIOA TP); [exact CTX| exact FP| exact G| exact ST| exact MI| unfold STDIO_STACK, PCAP_L2_STACK; lia] | exact HinF | reflexivity ] |].
    all: intros r sy RNGy msy PO; cbv beta in PO; destruct PO as (FPy & a0v & my & E & MIy & STy & AGy & Gy & -> & -> & ERRNO).
    all: rewrite ESPA in *; post_regs E.
    all: assert (INVy : ngc_inv GIOA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo MG EB ERR SPA Fb [mg0; mg1; mg2; mg3] o m RNGy sx [] my)
           by (eapply (ngc_inv_keep FO GIOA TP fflagA GL) with (CLk := (CL ++ [])%list) (Pn := fun _ : Z => True);
               [exact CTX| exact INV| exact FPy| exact Gy| reflexivity| exact MIy| exact STy| eapply agrees_on_weaken; [exact AGy| intros a (K & _); exact K]
               | apply incl_appl, incl_refl| exact G| intros; exact Logic.I]).
    all: assert (KEEP : forall A cs, rw_cells asegs mm A cs ->
                     ((SPA <= A) \/ (Fb <= A /\ A + Z.of_nat (cells_size cs) <= Fb + 64) \/ (ERR = A /\ cells_size cs = 4%nat) \/ (EB = A /\ cells_size cs = 256%nat))%Z -> rw_cells asegs my A cs)
           by (intros A cs HC HA; eapply agrees_rw_cells; [exact AGy| exact HC|]; intros a Ha;
               destruct HA as [HA|[HA|[HA|HA]]];
               [ left; lia
               | right; right; left; apply Exists_cons_hd; cbn [fb_addr fb_size fst snd]; lia
               | destruct HA as (<- & HS); rewrite HS in Ha; eapply clocA_keeps; [exact (clocA_incl _ _ _ _ _ _ (proj1 OERR) ICL IFL)| lia]
               | destruct HA as (<- & HS); rewrite HS in Ha; eapply clocA_keeps; [exact (clocA_incl _ _ _ _ _ _ (proj1 OEB) ICL IFL)| lia] ]).
    all: pose proof (KEEP _ _ FRA ltac:(left; lia)) as FRAy.
    all: pose proof (KEEP _ _ FRC ltac:(right; left; rewrite !cells_size_app, Hfcs; cbn [cells_size csize Nat.add]; lia)) as FRCy.
    all: pose proof (KEEP _ _ HE ltac:(right; right; left; split; reflexivity)) as HEy.
    all: pose proof (KEEP _ _ HEB ltac:(right; right; right; split; reflexivity)) as HEBy.
    all: clear KEEP.
    all: repeat match goal with HR : rng _ _ _ |- _ => apply (rng_fp_le _ _ _ _ FPy) in HR end.
    all: pose proof (munch_refl ([] : list (Z * Z)) my) as MU; pose proof (wmono_refl asegs my) as WM.
    all: destruct r.
    (* [comment removed for export] *)
    2,4: apply implMG_retb; cbn [Z.b2z]; ienterG; zstep; if_true;
         apply evtF_done; subst POSTQ;
         eapply (ngc_exit FO GIOA TP fflagA GL FRET) with (PB := ([] : list cblk)) (fcs := fcs) (k0 := k0) (k1 := k1) (k2 := k2) (ew := z64) (r := CH_NotMe);
           [ exact CTX | exact INVy | exact FRAy | reflexivity | exact FRCy | exact Hfcs | exact HEy
           | cbn [ngc_result]; split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|]; exists e; exact HEBy ].
    all: destruct (ERRNO eq_refl) as [EN2 ER]; clear ERRNO.
    all: unfold errmsg_for_errno; cbn [mo_bind mo_ret MOps e_last_errno e_fenter e_fret prims].
    all: apply implMG_errno_ll; set (en := lc_errno (ps_libc sx)) in *.
    all: destruct (gl_tls _ _ _ GL _ _ _ _ _ _ _ Gy RTLS) as (T0 & T47 & TUNP & TRNG & (RLO & RHI & TA1 & TA2 & TA3 & TA4 & TA5 & TA6 & TA7 & TA8) & _).
    all: assert (ETP : bv_unsigned tp = ATP) by (rewrite TPE; unfold ATP; pose proof atp_lin; apply unsigned_lit; lia).
    all: assert (MSG : fmt_at my 0x22080 "error reading dump file"%string)
           by (split; [exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image asegs my 0x22080 (map (fun c => Z_to_bv 8 (Z.of_nat (Ascii.nat_of_ascii c))) (String.list_ascii_of_string "error reading dump file"%string) ++ [Z_to_bv 8 0])
                                MIy ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)))|];
               split; [lia|]; split; [cbn; lia|]; unfold client_globals; repeat (first [left; reflexivity | right])).
    all: edestruct (ngc_cobj_now FO GIOA TP fflagA GL) as (_ & _ & OEB'); [exact CTX| exact INVy|].
    all: cbn [Z.b2z]; ienterG; zstep; if_false.
    all: zstep; do 3 zstep; rewrite ETP.
    (* [comment removed for export] *)
    all: pose proof ATPv_pg as TPG; pose proof atp_lin as ((TPLO & _) & _).
    all: assert (ERN : (0 < ATP + -164 < 2^64)%Z) by (unfold ATP; atop_facts; lia).
    all: zstep; if_false_by (eqz_false (ATP + -164) ERN).
    all: zstep; replace (Z.land (ATP + -164) 3) with 0%Z by (change 3%Z with (Z.ones 2); rewrite Z.land_ones by lia; unfold ATP; Z.div_mod_to_equations; lia).
    all: zstep; if_false.
    1: ck TUNP 4%Z 0x8ae00%Z [11%Z; 12%Z].
    2: ck TUNP 4%Z 0x8ae7c%Z [11%Z; 12%Z].
    all: zstep.
    all: do 4 zstep; zstep.
    all: replace (sx32 (Z_to_bv 64 en)) with (Z_to_bv 64 (s32 en)) by (unfold sx32, s32; rewrite unsigned_lit by lia; f_equal; unfold bv_swrap, bv_wrap; cbn; lia).
    all: apply evtF_done; subst POSTQ; eapply implMG_bind;
      [ eapply FMT with (L := L) (s := sx) (CL := (CL ++ [])%list) (FB := FB) (FL := NGFR Fb :: FL) (lo := lo) (EB := EB)
                        (FMTA := 0x22080%Z) (e := en) (fs := "error reading dump file"%string) (args := ([] : list farg)) (junk := e);
          [ eapply (ngc_spo GIOA TP); [exact CTX| eapply fp_le_trans; [exact FP| exact FPy]| exact Gy| exact STy| exact MIy| unfold PCAP_L1_STACK, PCAP_L2_STACK; lia]
          | cbn [map fb_fn fst]; intros [X|X]; [discriminate X|];
            exact (NF FF_FMT_ERRMSG ltac:(unfold frames_check_header, frames_pcap_ng_check_header; right; left; reflexivity) X)
          | reflexivity | reflexivity | reflexivity | lia | reflexivity | exact MSG | reflexivity | cbn; lia | constructor
          | exact HEBy | split; [exact (clocA_incl _ _ _ _ _ _ (proj1 OEB') ICL IFL)| exact (proj2 OEB')] | exact EB8 ] |].
    all: intros r4 s4' RNG4 ms4 PO; cbv beta in PO; destruct PO as (FP4 & -> & PO); destruct_exs PO.
    all: destruct PO as (-> & OF4 & LC4 & TL4 & MI4 & ST4 & AG4 & G4 & HEB4).
    all: rewrite ESPA in *.
    all: try (lazymatch goal with |- context [ret_pc (Z_to_bv 64 ?n)] =>
         replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) in * by (symmetry; apply ret_pc_even; [lia|reflexivity]) end).
    all: lazymatch type of AG4 with agrees_on _ _ ?m4 =>
           assert (INV4 : ngc_inv GIOA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo MG EB ERR SPA Fb [mg0; mg1; mg2; mg3] o m RNG4 s4' [] m4)
             by (eapply (ngc_inv_keep FO GIOA TP fflagA GL) with (CLk := (CL ++ [])%list) (Pn := fun a : Z => ~ (EB <= a < EB + 256)%Z);
                 [exact CTX| exact INVy| exact FP4| exact G4| exact OF4| exact MI4| exact ST4| exact AG4| apply incl_appl, incl_refl| exact Gy| intros a N1 N2; exact N1]);
           assert (KEEP : forall A cs, rw_cells asegs my A cs ->
                     ((SPA <= A) \/ (Fb <= A /\ A + Z.of_nat (cells_size cs) <= Fb + 64) \/ (ERR = A /\ cells_size cs = 4%nat))%Z -> rw_cells asegs m4 A cs)
             by (intros A cs HC HA; eapply agrees_rw_cells; [exact AG4| exact HC|]; intros a Ha;
                 destruct HA as [HA|[HA|HA]];
                 [ split; [left; lia| lia]
                 | split; [right; right; left; apply Exists_cons_hd; cbn [fb_addr fb_size fst snd]; lia| lia]
                 | destruct HA as (<- & HS); rewrite HS in Ha; split; [eapply clocA_keeps; [exact (clocA_incl _ _ _ _ _ _ (proj1 OERR) ICL IFL)| lia]| lia] ]) end.
    all: pose proof (KEEP _ _ FRAy ltac:(left; lia)) as FRA4.
    all: pose proof (KEEP _ _ FRCy ltac:(right; left; rewrite !cells_size_app, Hfcs; cbn [cells_size csize Nat.add]; lia)) as FRC4.
    all: pose proof (KEEP _ _ HEy ltac:(right; right; split; reflexivity)) as HE4.
    1: eapply (ngc_failx FO GIOA TP fflagA GL FRET) with (fcs := fcs) (k0 := k0) (k1 := k1) (k2 := k2) (pcX := 0x8ae18%Z) (msg := fmt_errmsg "error reading dump file" [] en);
        [ exact CTX | exact INV4 | left; reflexivity | exact FRA4 | reflexivity | exact FRC4 | exact Hfcs | exact HE4 | exact HEB4
        | pose proof (fmt_errmsg_length_ng "error reading dump file" [] en); lia
        | apply fmt_errmsg_ok; [vm_compute; reflexivity| apply args_ok_nil] ].
    eapply (ngc_failx FO GIOA TP fflagA GL FRET) with (fcs := fcs) (k0 := k0) (k1 := k1) (k2 := k2) (pcX := 0x8ae94%Z) (msg := fmt_errmsg "error reading dump file" [] en);
        [ exact CTX | exact INV4 | right; left; reflexivity | exact FRA4 | reflexivity | exact FRC4 | exact Hfcs | exact HE4 | exact HEB4
        | pose proof (fmt_errmsg_length_ng "error reading dump file" [] en); lia
        | apply fmt_errmsg_ok; [vm_compute; reflexivity| apply args_ok_nil] ].
  Qed.
  End Sz3.
  Theorem ngc_short : ltac:(let t := eval cbv delta [ngc_short__stmt] in ngc_short__stmt in exact t).
  Proof using GL FRET FERROR FMT. red. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic m o RNGx sx mm ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r22 r23 r24 t3 t4 t5 t6 pcx j0 j j2 fcs k0 k1 k2 e. ltac2:(SecDiet.SzSec.closeP 'ngc_short__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End NgcShort.
End CANSEC1.
End TwB.
End F_ngchk_hshortA.

(* [comment removed for export] *)
Module F_ngchk_hbomA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep Frame StoreFast Image.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow StepF SysStepF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg ABase AMalloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA LibcKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FrameKit__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require SfKitA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngchk_modelA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngchk_defsA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require LibcKit2__A3P. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.MonadGX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.PerfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.SfKitA__A3P.SfKitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_modelA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_defsA__A3P.F_ngchk_defsA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit2__A3P.F_ngchk_kitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_defsA__A3P.F_ngchk_exitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit2__A3P.F_ngchk_ngiA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_defsA__A3P.F_ngchk_fstmtA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_defsA__A3P.F_ngchk_hstmtA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_defsA__A3P.F_ngchk_hstmt2A.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaRel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac dm_plia := first [ atop_facts; once ltac2:(let _ := LiaRel.lr_prune_b 101 in ()); Z.div_mod_to_equations; lia_tiers
                            | Z.div_mod_to_equations; lia ].
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= unp_store m a bs n Hn Ha Hl.
Local Ltac transport_call_extra segs W m m' MU WM ::= unp_call W m m' MU.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Ltac ienterG := lazymatch goal with |- implMG _ _ _ ?Q _ => let QQ := fresh "POSTQ" in set (QQ := Q) end; apply implMG_from_evtF.
Ltac hide H := lazymatch type of H with ?T => let X := fresh "AUX" in set (X := T) in H end.
Ltac unhide H := lazymatch type of H with ?X => subst X end.

(* [comment removed for export] *)
Local Ltac zrange_gz_g :=
  lazymatch goal with
  | |- inr64 (sxv _ _ _ _) => fail   (* [comment removed for export] *)
  | |- inr64 (Z.shiftl (Z.modulo (sxv _ _ _ _) (18446744073709551616)%Z) (24)%Z) => fail   (* [comment removed for export] *)
  | |- inr64 (Z.shiftl (Z.land (Z.modulo (sxv _ _ _ _) (18446744073709551616)%Z) (65280)%Z) (8)%Z) => fail   (* [comment removed for export] *)
  | |- _ => zrange
  end.
Local Ltac zrange_gz_i :=
  lazymatch goal with
  | |- _ => zrange
  end.
Local Ltac zsimp ::=
  rewrite ?v_sltu_b2z, ?v_slt_b2z, ?v_sltiu_b2z, ?v_slti_b2z;
  cbv delta [zxb];
  zb_fold_lits;
  repeat match goal with
  | |- context [bv_unsigned (Z_to_bv 64 ?e)] =>
      first [ rewrite (inr64_unsigned_lit e) by zrange_gz_g
            | zs_wrap e ]            (* [comment removed for export] *)
  | |- _ => progress zs_idioms
  end; zb_fold_lits.
Local Ltac zsimp_in H ::=
  rewrite ?v_sltu_b2z, ?v_slt_b2z, ?v_sltiu_b2z, ?v_slti_b2z in H;
  cbv delta [zxb] in H;
  zb_fold_lits_in H;
  repeat match type of H with
  | context [bv_unsigned (Z_to_bv 64 ?e)] =>
      first [ rewrite (inr64_unsigned_lit e) in H by zrange_gz_i
            | zs_wrap_in e H ]
  | _ => progress (zs_idioms_in H)
  end; zb_fold_lits_in H.
Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section NgcBom.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis FRET : fret_inline_law FO GIOA fflagA.
  Hypothesis FILL : ngc_fill_stmt HO FO sites GIOA TP fflagA.
  Hypothesis LENFAIL : ngc_lenfail_stmt HO FO sites GIOA TP fflagA.
  #[local] Notation cblk := (@cblock hptr).
  #[local] Notation NGFR Fb := (FF_NG_CHECK_HEADER, Fb, 64%Z).

  Definition ngc_bom__stmt : Prop := ngc_bom_stmt HO FO sites GIOA TP fflagA.
  Section Sz1.
  Variables fuel ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic m o RNGx sx mm ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r23 t3 t4 t5 t6 tlb bomb j0 j j2 fpre fmid fpost k0 k1 k2 e : ltac2:(SecDiet.SzSec.tyM 'ngc_bom__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @fuel).
  Lemma ngc_bom__body : ltac2:(SecDiet.SzSec.bodyP 'ngc_bom__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL FRET FILL LENFAIL.
 intros CTX INV TR TLn BR BLn FRA FRC HE HEB.
    destruct tlb as [|q0 [|q1 [|q2 [|q3 [|? ?]]]]]; try discriminate TLn. destruct bomb as [|b0 [|b1 [|b2 [|b3 [|? ?]]]]]; try discriminate BLn.
    pose proof (Forall_inv TR) as Q0. pose proof (Forall_inv (Forall_inv_tail TR)) as Q1.
    pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail TR))) as Q2. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail TR)))) as Q3.
    pose proof (Forall_inv BR) as B0. pose proof (Forall_inv (Forall_inv_tail BR)) as B1.
    pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail BR))) as B2. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail BR)))) as B3.
    cbv beta in Q0, Q1, Q2, Q3, B0, B1, B2, B3. clear TR TLn BR BLn.
    ngc_setup GL CTX INV.
    (* [comment removed for export] *)
    assert (FRC4 : rw_cells asegs mm Fb [C8 k0; C8 k1; C8 k2; CB 8 fpre; C4 (Z_to_bv 64 (le4val q0 q1 q2 q3)); CB 12 fmid; C4 (Z_to_bv 64 (le4val b0 b1 b2 b3)); CB 4 fpost;
                                          C8 (Z_to_bv 64 (fflagA L FF_NG_CHECK_HEADER Fb))]).
    { eapply rw_cells_recell; [exact FRC | pose proof (proj1 (proj1 FRC)) as WF; cbn in WF |- *; repeat split; clear - WF; tauto |].
      cbn [cells_bytes cbytes map app]. rewrite (le4_lit q0 q1 q2 q3), (le4_lit b0 b1 b2 b3) by lia. reflexivity. }
    clear FRC.
    (* [comment removed for export] *)
    unfold ngc_bomk, get_le32, zslice, zfirstn, zskipn. change (Z.to_nat 0) with 0%nat. change (Z.to_nat 4) with 4%nat. cbn [firstn skipn].
    rewrite (bswap32_bytes b0 b1 b2 b3), (bswap32_bytes q0 q1 q2 q3) by lia. rewrite !le_of_bytes_4.
    change (b0 + 256 * b1 + 65536 * b2 + 16777216 * b3)%Z with (le4val b0 b1 b2 b3).
    change (q0 + 256 * q1 + 65536 * q2 + 16777216 * q3)%Z with (le4val q0 q1 q2 q3).
    change (b3 + 256 * b2 + 65536 * b1 + 16777216 * b0)%Z with (le4val b3 b2 b1 b0).
    change (q3 + 256 * q2 + 65536 * q1 + 16777216 * q0)%Z with (le4val q3 q2 q1 q0).
    set (PR := prims HO FO sites) in *.
    assert (EQB : forall v, (0 <= v < 2^31)%Z -> bv_eqb (Z_to_bv 64 (sxv b0 b1 b2 b3)) (Z_to_bv 64 v) = (le4val b0 b1 b2 b3 =? v)%Z).
    { intros v Hv. unfold bv_eqb. rewrite (unsigned_lit (sxv b0 b1 b2 b3)), (unsigned_lit v) by (unfold sxv, le4val; dm_plia).
      unfold sxv. destruct (Z.eqb_spec (le4val b0 b1 b2 b3) v) as [E|NE]; [apply Z.eqb_eq | apply Z.eqb_neq]; unfold le4val in *; dm_plia. }
    (* [comment removed for export] *)
    assert (AT6 : forall (m6 : mem) (fcs6 : list cell), mem_inv asegs m6 -> munch [(Fb + 32, Fb + 52)]%Z mm m6 -> wmono asegs mm m6 -> cells_size fcs6 = 32%nat ->
              rw_cells asegs m6 Fb ([C8 k0; C8 k1; C8 k2] ++ fcs6 ++ [C8 (Z_to_bv 64 (fflagA L FF_NG_CHECK_HEADER Fb))]) ->
              ngc_inv GIOA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo MG EB ERR SPA Fb [mg0; mg1; mg2; mg3] o m RNGx sx [] m6
              /\ rw_cells asegs m6 SPA [CB 80 j0; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 EB); CB 24 j; C8 (Z_to_bv 64 Fb); CB 24 j2]
              /\ rw_cells asegs m6 ERR [C4 z64] /\ rw_cells asegs m6 EB [CB 256 e]).
    { intros m6 fcs6 MI6 MU6 WM6 Hf6 FRC6.
      assert (AGS : agrees_on (fun a => outside [(Fb + 32, Fb + 52)]%Z a) mm m6) by (eapply agrees_on_of_munch; [exact MU6 | exact WM6 | intros a _ Ho; exact Ho]).
      assert (ST6 : stk asegs m6 lo SPA) by (eapply agrees_stk; [exact AGS| exact ST| intros a Ha; cbn [outside fst snd]; lia]).
      split.
      { eapply (ngc_inv_own FO GIOA TP fflagA GL); [exact CTX| exact INV| | exact MU6| exact WM6| exact MI6| exact ST6| ].
        - apply Forall_cons; [|apply Forall_nil]. right; right; left. apply Exists_cons_hd. cbn [fb_addr fb_size fst snd]. lia.
        - intros a Ha. cbn [outside fst snd]. lia. }
      split; [eapply agrees_rw_cells; [exact AGS| exact FRA|]; intros a Ha; cbn [cells_size csize Nat.add] in Ha; cbn [outside fst snd]; lia|].
      split; [eapply agrees_rw_cells; [exact AGS| exact HE|]; intros a Ha; cbn [cells_size csize Nat.add] in Ha; cbn [outside fst snd]; lia|].
      eapply agrees_rw_cells; [exact AGS| exact HEB|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. cbn [outside fst snd]. lia. }
    (* [comment removed for export] *)
    assert (GOFILL : forall (m6 : mem) (sw : bool) (c0 c1 c2 c3 : Z) (POSTQ' : check_result -> PState H hptr -> footprint -> machine_state -> Prop)
                       (rax t0x t1x t2x a0x a1x a2x a3x a4x a5x a6x a7x t3x t4x t5x t6x : word),
              POSTQ' = check_header_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CL FB lo MG EB ERR [mg0; mg1; mg2; mg3] f m o ->
              (0 <= c0 < 256)%Z -> (0 <= c1 < 256)%Z -> (0 <= c2 < 256)%Z -> (0 <= c3 < 256)%Z -> (28 <= le4val c0 c1 c2 c3 <= 1048576)%Z ->
              mem_inv asegs m6 -> munch [(Fb + 32, Fb + 52)]%Z mm m6 -> wmono asegs mm m6 ->
              rw_cells asegs m6 Fb [C8 k0; C8 k1; C8 k2; CB 8 fpre; C4 (Z_to_bv 64 (le4val c0 c1 c2 c3)); CB 12 fmid; C4 (Z_to_bv 64 BYTE_ORDER_MAGIC); CB 4 fpost;
                                    C8 (Z_to_bv 64 (fflagA L FF_NG_CHECK_HEADER Fb))] ->
              evtF asegs RNGx (fun ms' => implMG RNGx (ngc_open MOps PR fuel f 0 BT_SHB sw (le4val c0 c1 c2 c3)) sx POSTQ' ms')
                (MS (mkR rax (Z_to_bv 64 SPA) gp tp t0x t1x t2x sp (Z_to_bv 64 SPA) a0x a1x a2x a3x a4x a5x a6x a7x
                         (Z_to_bv 64 Fb) (Z_to_bv 64 ERR) (Z_to_bv 64 (Z.shiftr ERR 3 + 2147450880)) (Z_to_bv 64 (Fb + 48)) (Z_to_bv 64 FA) (Z_to_bv 64 (Z.b2z sw)) (Z_to_bv 64 (sxv c0 c1 c2 c3))
                         (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 2147450880) (Z_to_bv 64 Fb) t3x t4x t5x t6x)
                    F (Z_to_bv 64 0x8b044) fc None m6 (seg_rom asegs))).
    { intros until t6x. intros -> C0 C1 C2 C3 TLR MI6 MU6 WM6 FRC6.
      destruct (AT6 m6 [CB 8 fpre; C4 (Z_to_bv 64 (le4val c0 c1 c2 c3)); CB 12 fmid; C4 (Z_to_bv 64 BYTE_ORDER_MAGIC); CB 4 fpost] MI6 MU6 WM6 eq_refl FRC6) as (INV6 & FRA6 & HE6 & HEB6).
      replace (sxv c0 c1 c2 c3) with (le4val c0 c1 c2 c3) by (unfold sxv, le4val in *; dm_plia).
      destruct (rw_cells_cut _ _ _ 5 FRA6) as [FRA5 FCUR6]. cbn [firstn skipn cells_size csize Nat.add] in FRA5, FCUR6.
      lazymatch type of FCUR6 with rw_cells _ _ ?A _ => replace A with (SPA + 128)%Z in FCUR6 by lia end.
      apply evtF_done.
      eapply (FILL fuel) with (sw := sw) (TL := le4val c0 c1 c2 c3) (j0 := j0) (j := j) (ccs := [CB 24 j2]) (fpre := fpre) (fmid := fmid) (fpost := fpost) (k0 := k0) (k1 := k1) (k2 := k2)
               (tlw := Z_to_bv 64 (le4val c0 c1 c2 c3)) (e := e);
        [ exact CTX | exact INV6 | exact TLR | exact FRA5 | exact FCUR6 | reflexivity | exact FRC6 | exact HE6 | exact HEB6 ]. }
    assert (GOLEN : forall (m6 : mem) (c0 c1 c2 c3 : Z) (POSTQ' : check_result -> PState H hptr -> footprint -> machine_state -> Prop) (fcs6 : list cell)
                      (rax t0x t1x t2x a0x a1x a2x a3x a4x a5x a6x a7x r21 r22 r23 t3x t4x t5x t6x : word),
              POSTQ' = check_header_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CL FB lo MG EB ERR [mg0; mg1; mg2; mg3] f m o ->
              (0 <= c0 < 256)%Z -> (0 <= c1 < 256)%Z -> (0 <= c2 < 256)%Z -> (0 <= c3 < 256)%Z ->
              mem_inv asegs m6 -> munch [(Fb + 32, Fb + 52)]%Z mm m6 -> wmono asegs mm m6 -> cells_size fcs6 = 32%nat ->
              rw_cells asegs m6 Fb ([C8 k0; C8 k1; C8 k2] ++ fcs6 ++ [C8 (Z_to_bv 64 (fflagA L FF_NG_CHECK_HEADER Fb))]) ->
              evtF asegs RNGx (fun ms' => implMG RNGx (e_fret PR FF_NG_CHECK_HEADER (CH_Err (Msg.shb_invalid_length (le4val c0 c1 c2 c3)))) sx POSTQ' ms')
                (MS (mkR rax (Z_to_bv 64 SPA) gp tp t0x t1x t2x sp (Z_to_bv 64 SPA) a0x a1x a2x a3x a4x a5x a6x a7x
                         (Z_to_bv 64 Fb) (Z_to_bv 64 ERR) (Z_to_bv 64 (Z.shiftr ERR 3 + 2147450880)) r21 r22 r23 (Z_to_bv 64 (sxv c0 c1 c2 c3))
                         (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 2147450880) (Z_to_bv 64 Fb) t3x t4x t5x t6x)
                    F (Z_to_bv 64 0x8af84) fc None m6 (seg_rom asegs))).
    { intros until t6x. intros -> C0 C1 C2 C3 MI6 MU6 WM6 Hf6 FRC6.
      destruct (AT6 m6 fcs6 MI6 MU6 WM6 Hf6 FRC6) as (INV6 & FRA6 & HE6 & HEB6).
      apply evtF_done.
      eapply LENFAIL with (TL := le4val c0 c1 c2 c3) (hi := (c3 / 128 * 4294967295)%Z) (j0 := j0) (j := j) (j2 := j2) (fcs := fcs6) (k0 := k0) (k1 := k1) (k2 := k2) (e := e);
        [ exact CTX | exact INV6 | rewrite unsigned_lit by (unfold sxv, le4val; dm_plia); unfold sxv; reflexivity
        | unfold le4val; lia | dm_plia | exact FRA6 | exact FRC6 | exact Hf6 | exact HE6 | exact HEB6 ]. }
    (* [comment removed for export] *)
    assert (LENCK : forall c0 c1 c2 c3, (0 <= c0 < 256)%Z -> (0 <= c1 < 256)%Z -> (0 <= c2 < 256)%Z -> (0 <= c3 < 256)%Z ->
              bv_ltu (Z_to_bv 64 (-1048550)) (Z_to_bv 64 (bv_swrap 32 (sxv c0 c1 c2 c3 mod 18446744073709551616 + 18446744073708503039)))
              = ((28 <=? le4val c0 c1 c2 c3) && (le4val c0 c1 c2 c3 <=? 1048576))%Z).
    { intros c0 c1 c2 c3 C0 C1 C2 C3. unfold bv_ltu. rewrite !unsigned_lit_wrap.
      unfold sxv, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. cbn -[Z.add Z.sub Z.modulo Z.mul Z.div Z.ltb Z.leb andb Z.pow le4val].
      change (2^64)%Z with 18446744073709551616%Z. change (2 ^ (32 - 1))%Z with 2147483648%Z. change (2^32)%Z with 4294967296%Z.
      assert (LR : (0 <= le4val c0 c1 c2 c3 < 4294967296)%Z) by (unfold le4val; lia).
      destruct (Z.leb_spec 28 (le4val c0 c1 c2 c3)); destruct (Z.leb_spec (le4val c0 c1 c2 c3) 1048576); cbn [andb];
        first [apply Z.ltb_lt | apply Z.ltb_ge]; dm_plia. }
    hide FRA. hide HE. hide HEB. hide FR. hide MGc. hide SHC.
    pose proof (munch_refl [(Fb + 32, Fb + 52)]%Z mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    ienterG.
    zstep. rewrite (sx32_lit b0 b1 b2 b3) by lia. do 3 zstep.
    rewrite (EQB 439041101%Z) by lia.
    destruct (Z.eqb_spec (le4val b0 b1 b2 b3) 439041101) as [EQN|NEN]; cbn [negb]; cbv iota.
    - (* [comment removed for export] *)
      replace (le4val b0 b1 b2 b3 =? BYTE_ORDER_MAGIC)%Z with true by (symmetry; apply Z.eqb_eq; exact EQN). cbv beta iota. cbn [negb]. cbv iota.
      zstep. zstep. rewrite (sx32_lit q0 q1 q2 q3) by lia. do 4 zstep. zstep.
      rewrite (LENCK q0 q1 q2 q3) by lia.
      rewrite EQN in FRC4.
      destruct ((28 <=? le4val q0 q1 q2 q3) && (le4val q0 q1 q2 q3 <=? 1048576))%Z eqn:LC.
      + replace ((le4val q0 q1 q2 q3 <? 28) || (BT_SHB_INSANE_MAX <? le4val q0 q1 q2 q3))%Z with false by (unfold BT_SHB_INSANE_MAX; lia). cbv iota.
        eapply (GOFILL mm false q0 q1 q2 q3); [reflexivity| lia| lia| lia| lia| lia| exact MI| exact MU| exact WM| exact FRC4].
      + replace ((le4val q0 q1 q2 q3 <? 28) || (BT_SHB_INSANE_MAX <? le4val q0 q1 q2 q3))%Z with true by (unfold BT_SHB_INSANE_MAX; lia). cbv iota.
        eapply (GOLEN mm q0 q1 q2 q3) with (fcs6 := [CB 8 fpre; C4 (Z_to_bv 64 (le4val q0 q1 q2 q3)); CB 12 fmid; C4 (Z_to_bv 64 439041101); CB 4 fpost]);
          [reflexivity| lia| lia| lia| lia| exact MI| exact MU| exact WM| reflexivity| exact FRC4].
    - (* [comment removed for export] *)
      replace (le4val b0 b1 b2 b3 =? BYTE_ORDER_MAGIC)%Z with false by (symmetry; apply Z.eqb_neq; exact NEN).
      do 13 zstep. zstep. zstep.
      assert (SWV : forall a b c d, (0 <= a < 256)%Z -> (0 <= b < 256)%Z -> (0 <= c < 256)%Z -> (0 <= d < 256)%Z ->
        le4 (Z_to_bv 64 (Z.lor (Z.lor (Z.shiftl (sxv a b c d mod 18446744073709551616) 24 mod 18446744073709551616)
                                      (Z.shiftl (Z.land (sxv a b c d mod 18446744073709551616) 65280) 8 mod 18446744073709551616))
                               (Z.lor (Z.land (Z.shiftr (sxv a b c d mod 18446744073709551616) 8) 65280)
                                      (bv_swrap 32 (Z.shiftr (bv_wrap 32 (sxv a b c d mod 18446744073709551616)) 24) mod 18446744073709551616))))
        = le4 (Z_to_bv 64 (le4val d c b a))).
      { intros a b c d Ha Hb Hc Hd.
        assert (SR : (0 <= sxv a b c d < 2^64)%Z) by (unfold sxv, le4val; dm_plia).
        replace (sxv a b c d mod 18446744073709551616)%Z with (bv_unsigned (Z_to_bv 64 (sxv a b c d))) by (rewrite unsigned_lit by lia; symmetry; apply Z.mod_small; lia).
        rewrite (le4_lit d c b a) by lia.
        apply (le4_of_val _ d c b a (b + 256 * c + 65536 * d + 16777216 * ((d / 128 * 4294967295) mod 256))); [lia|lia|lia|lia| dm_plia|].
        apply (swap32_valA _ a b c d (d / 128 * 4294967295)); [lia|lia|lia|lia| dm_plia| rewrite unsigned_lit by lia; unfold sxv, le4val; lia]. }
      lazymatch goal with HC : rw_cells asegs ?mx Fb [C8 k0; C8 k1; C8 k2; CB 8 fpre; ?c1; CB 12 fmid; C4 ?w; CB 4 fpost; ?fl] |- _ =>
        assert (FRC5 : rw_cells asegs mx Fb [C8 k0; C8 k1; C8 k2; CB 8 fpre; c1; CB 12 fmid; C4 (Z_to_bv 64 (le4val b3 b2 b1 b0)); CB 4 fpost; fl])
          by (eapply rw_cells_recell; [exact HC | pose proof (proj1 (proj1 HC)) as WF; cbn in WF |- *; repeat split; clear - WF; tauto |];
              cbn [cells_bytes cbytes app]; rewrite (SWV b0 b1 b2 b3) by lia; reflexivity);
        clear HC end.
      rewrite (EQB 1295788826%Z) by lia.
      destruct (Z.eqb_spec (le4val b0 b1 b2 b3) 1295788826) as [EQS|NES]; cbn [negb]; cbv iota.
      + (* [comment removed for export] *)
        replace (le4val b3 b2 b1 b0 =? BYTE_ORDER_MAGIC)%Z with true by (symmetry; apply Z.eqb_eq; unfold le4val, BYTE_ORDER_MAGIC in *; lia).
        cbv beta iota. cbn [negb]. cbv iota.
        zstep. rewrite (sx32_lit q0 q1 q2 q3) by lia.
        do 9 zstep. zstep.
        lazymatch goal with HC : rw_cells asegs ?mx Fb [C8 k0; C8 k1; C8 k2; CB 8 fpre; C4 ?w; CB 12 fmid; ?c2; CB 4 fpost; ?fl] |- _ =>
          assert (FRC6 : rw_cells asegs mx Fb [C8 k0; C8 k1; C8 k2; CB 8 fpre; C4 (Z_to_bv 64 (le4val q3 q2 q1 q0)); CB 12 fmid; c2; CB 4 fpost; fl])
            by (eapply rw_cells_recell; [exact HC | pose proof (proj1 (proj1 HC)) as WF; cbn in WF |- *; repeat split; clear - WF; tauto |];
                cbn [cells_bytes cbytes app]; rewrite (SWV q0 q1 q2 q3) by lia; reflexivity);
          clear HC end.
        zstep. zstep. rewrite (sx32_lit q3 q2 q1 q0) by lia.
        do 4 zstep. zstep.
        rewrite (LENCK q3 q2 q1 q0) by lia.
        assert (EQM : le4val b3 b2 b1 b0 = BYTE_ORDER_MAGIC) by (unfold le4val, BYTE_ORDER_MAGIC in *; lia).
        rewrite EQM in FRC6.
        destruct ((28 <=? le4val q3 q2 q1 q0) && (le4val q3 q2 q1 q0 <=? 1048576))%Z eqn:LC.
        * replace ((le4val q3 q2 q1 q0 <? 28) || (BT_SHB_INSANE_MAX <? le4val q3 q2 q1 q0))%Z with false by (unfold BT_SHB_INSANE_MAX; lia). cbv iota.
          eapply (GOFILL m1 true q3 q2 q1 q0); [reflexivity| lia| lia| lia| lia| lia| exact MI| exact MU| exact WM| exact FRC6].
        * replace ((le4val q3 q2 q1 q0 <? 28) || (BT_SHB_INSANE_MAX <? le4val q3 q2 q1 q0))%Z with true by (unfold BT_SHB_INSANE_MAX; lia). cbv iota.
          eapply (GOLEN m1 q3 q2 q1 q0) with (fcs6 := [CB 8 fpre; C4 (Z_to_bv 64 (le4val q3 q2 q1 q0)); CB 12 fmid; C4 (Z_to_bv 64 BYTE_ORDER_MAGIC); CB 4 fpost]);
            [reflexivity| lia| lia| lia| lia| exact MI| exact MU| exact WM| reflexivity| exact FRC6].
      + (* [comment removed for export] *)
        replace (le4val b3 b2 b1 b0 =? BYTE_ORDER_MAGIC)%Z with false by (symmetry; apply Z.eqb_neq; unfold le4val, BYTE_ORDER_MAGIC in *; lia).
        cbv beta iota. cbn [negb]. cbv iota.
        destruct (AT6 m0 [CB 8 fpre; C4 (Z_to_bv 64 (le4val q0 q1 q2 q3)); CB 12 fmid; C4 (Z_to_bv 64 (le4val b3 b2 b1 b0)); CB 4 fpost] MI MU WM eq_refl FRC5) as (INV6 & FRA6 & HE6 & HEB6).
        zstep. zstep.
        apply evtF_done. subst POSTQ.
        eapply (ngc_exit FO GIOA TP fflagA GL FRET) with (PB := ([] : list cblk)) (fcs := [CB 8 fpre; C4 (Z_to_bv 64 (le4val q0 q1 q2 q3)); CB 12 fmid; C4 (Z_to_bv 64 (le4val b3 b2 b1 b0)); CB 4 fpost])
            (k0 := k0) (k1 := k1) (k2 := k2) (ew := z64) (r := CH_NotMe);
          [ exact CTX | exact INV6 | exact FRA6 | reflexivity | exact FRC5 | reflexivity | exact HE6
          | cbn [ngc_result]; split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|]; exists e; exact HEB6 ].
  Qed.
  End Sz1.
  Theorem ngc_bom : ltac:(let t := eval cbv delta [ngc_bom__stmt] in ngc_bom__stmt in exact t).
  Proof using GL FRET FILL LENFAIL. red. intros fuel ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic m o RNGx sx mm ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r23 t3 t4 t5 t6 tlb bomb j0 j j2 fpre fmid fpost k0 k1 k2 e. ltac2:(SecDiet.SzSec.closeP 'ngc_bom__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End NgcBom.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Strings.String.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.StoreFast OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Image.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB.
(* [comment removed for export] *)
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.MonadGX.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.PerfKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.SfKitA__A3P.SfKitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_modelA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_defsA__A3P.F_ngchk_defsA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit2__A3P.F_ngchk_kitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_defsA__A3P.F_ngchk_exitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit2__A3P.F_ngchk_ngiA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_defsA__A3P.F_ngchk_fstmtA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_defsA__A3P.F_ngchk_hstmtA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_defsA__A3P.F_ngchk_hstmt2A.TwB. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac dm_plia := first [ atop_facts; once ltac2:(let _ := LiaRel.lr_prune_b 101 in ()); Z.div_mod_to_equations; lia_tiers
                            | Z.div_mod_to_equations; lia ].
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= unp_store m a bs n Hn Ha Hl.
Local Ltac transport_call_extra segs W m m' MU WM ::= unp_call W m m' MU.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Ltac ienterG := lazymatch goal with |- implMG _ _ _ ?Q _ => let QQ := fresh "POSTQ" in set (QQ := Q) end; apply implMG_from_evtF.
Ltac hide H := lazymatch type of H with ?T => let X := fresh "AUX" in set (X := T) in H end.
Ltac unhide H := lazymatch type of H with ?X => subst X end.

(* [comment removed for export] *)
Local Ltac zrange_gz_g :=
  lazymatch goal with
  | |- inr64 (sxv _ _ _ _) => fail   (* [comment removed for export] *)
  | |- inr64 (Z.shiftl (Z.modulo (sxv _ _ _ _) (18446744073709551616)%Z) (24)%Z) => fail   (* [comment removed for export] *)
  | |- inr64 (Z.shiftl (Z.land (Z.modulo (sxv _ _ _ _) (18446744073709551616)%Z) (65280)%Z) (8)%Z) => fail   (* [comment removed for export] *)
  | |- _ => zrange
  end.
Local Ltac zrange_gz_i :=
  lazymatch goal with
  | |- _ => zrange
  end.
Local Ltac zsimp ::=
  rewrite ?v_sltu_b2z, ?v_slt_b2z, ?v_sltiu_b2z, ?v_slti_b2z;
  cbv delta [zxb];
  zb_fold_lits;
  repeat match goal with
  | |- context [bv_unsigned (Z_to_bv 64 ?e)] =>
      first [ rewrite (inr64_unsigned_lit e) by zrange_gz_g
            | zs_wrap e ]            (* [comment removed for export] *)
  | |- _ => progress zs_idioms
  end; zb_fold_lits.
Local Ltac zsimp_in H ::=
  rewrite ?v_sltu_b2z, ?v_slt_b2z, ?v_sltiu_b2z, ?v_slti_b2z in H;
  cbv delta [zxb] in H;
  zb_fold_lits_in H;
  repeat match type of H with
  | context [bv_unsigned (Z_to_bv 64 ?e)] =>
      first [ rewrite (inr64_unsigned_lit e) in H by zrange_gz_i
            | zs_wrap_in e H ]
  | _ => progress (zs_idioms_in H)
  end; zb_fold_lits_in H.
Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section NgcBom.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis FRET : fret_inline_law FO GIOA fflagA.
  Hypothesis FILL : ngc_fill_stmt HO FO sites GIOA TP fflagA.
  Hypothesis LENFAIL : ngc_lenfail_stmt HO FO sites GIOA TP fflagA.
  #[local] Notation cblk := (@cblock hptr).
  #[local] Notation NGFR Fb := (FF_NG_CHECK_HEADER, Fb, 64%Z).

  Definition ngc_bom__stmt : Prop := ngc_bom_stmt HO FO sites GIOA TP fflagA.
  Section Sz1.
  Variables fuel ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic m o RNGx sx mm ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r23 t3 t4 t5 t6 tlb bomb j0 j j2 fpre fmid fpost k0 k1 k2 e : ltac2:(SecDiet.SzSec.tyM 'ngc_bom__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @fuel).
  Lemma ngc_bom__body : ltac2:(SecDiet.SzSec.bodyP 'ngc_bom__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL FRET FILL LENFAIL.
 intros CTX INV TR TLn BR BLn FRA FRC HE HEB.
    destruct tlb as [|q0 [|q1 [|q2 [|q3 [|? ?]]]]]; try discriminate TLn. destruct bomb as [|b0 [|b1 [|b2 [|b3 [|? ?]]]]]; try discriminate BLn.
    pose proof (Forall_inv TR) as Q0. pose proof (Forall_inv (Forall_inv_tail TR)) as Q1.
    pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail TR))) as Q2. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail TR)))) as Q3.
    pose proof (Forall_inv BR) as B0. pose proof (Forall_inv (Forall_inv_tail BR)) as B1.
    pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail BR))) as B2. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail BR)))) as B3.
    cbv beta in Q0, Q1, Q2, Q3, B0, B1, B2, B3. clear TR TLn BR BLn.
    ngc_setup GL CTX INV.
    (* [comment removed for export] *)
    assert (FRC4 : rw_cells asegs mm Fb [C8 k0; C8 k1; C8 k2; CB 8 fpre; C4 (Z_to_bv 64 (le4val q0 q1 q2 q3)); CB 12 fmid; C4 (Z_to_bv 64 (le4val b0 b1 b2 b3)); CB 4 fpost;
                                          C8 (Z_to_bv 64 (fflagA L FF_NG_CHECK_HEADER Fb))]).
    { eapply rw_cells_recell; [exact FRC | pose proof (proj1 (proj1 FRC)) as WF; cbn in WF |- *; repeat split; clear - WF; tauto |].
      cbn [cells_bytes cbytes map app]. rewrite (le4_lit q0 q1 q2 q3), (le4_lit b0 b1 b2 b3) by lia. reflexivity. }
    clear FRC.
    (* [comment removed for export] *)
    unfold ngc_bomk, get_le32, zslice, zfirstn, zskipn. change (Z.to_nat 0) with 0%nat. change (Z.to_nat 4) with 4%nat. cbn [firstn skipn].
    rewrite (bswap32_bytes b0 b1 b2 b3), (bswap32_bytes q0 q1 q2 q3) by lia. rewrite !le_of_bytes_4.
    change (b0 + 256 * b1 + 65536 * b2 + 16777216 * b3)%Z with (le4val b0 b1 b2 b3).
    change (q0 + 256 * q1 + 65536 * q2 + 16777216 * q3)%Z with (le4val q0 q1 q2 q3).
    change (b3 + 256 * b2 + 65536 * b1 + 16777216 * b0)%Z with (le4val b3 b2 b1 b0).
    change (q3 + 256 * q2 + 65536 * q1 + 16777216 * q0)%Z with (le4val q3 q2 q1 q0).
    set (PR := prims HO FO sites) in *.
    assert (EQB : forall v, (0 <= v < 2^31)%Z -> bv_eqb (Z_to_bv 64 (sxv b0 b1 b2 b3)) (Z_to_bv 64 v) = (le4val b0 b1 b2 b3 =? v)%Z).
    { intros v Hv. unfold bv_eqb. rewrite (unsigned_lit (sxv b0 b1 b2 b3)), (unsigned_lit v) by (unfold sxv, le4val; dm_plia).
      unfold sxv. destruct (Z.eqb_spec (le4val b0 b1 b2 b3) v) as [E|NE]; [apply Z.eqb_eq | apply Z.eqb_neq]; unfold le4val in *; dm_plia. }
    (* [comment removed for export] *)
    assert (AT6 : forall (m6 : mem) (fcs6 : list cell), mem_inv asegs m6 -> munch [(Fb + 32, Fb + 52)]%Z mm m6 -> wmono asegs mm m6 -> cells_size fcs6 = 32%nat ->
              rw_cells asegs m6 Fb ([C8 k0; C8 k1; C8 k2] ++ fcs6 ++ [C8 (Z_to_bv 64 (fflagA L FF_NG_CHECK_HEADER Fb))]) ->
              ngc_inv GIOA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo MG EB ERR SPA Fb [mg0; mg1; mg2; mg3] o m RNGx sx [] m6
              /\ rw_cells asegs m6 SPA [CB 80 j0; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 EB); CB 24 j; C8 (Z_to_bv 64 Fb); CB 24 j2]
              /\ rw_cells asegs m6 ERR [C4 z64] /\ rw_cells asegs m6 EB [CB 256 e]).
    { intros m6 fcs6 MI6 MU6 WM6 Hf6 FRC6.
      assert (AGS : agrees_on (fun a => outside [(Fb + 32, Fb + 52)]%Z a) mm m6) by (eapply agrees_on_of_munch; [exact MU6 | exact WM6 | intros a _ Ho; exact Ho]).
      assert (ST6 : stk asegs m6 lo SPA) by (eapply agrees_stk; [exact AGS| exact ST| intros a Ha; cbn [outside fst snd]; lia]).
      split.
      { eapply (ngc_inv_own FO GIOA TP fflagA GL); [exact CTX| exact INV| | exact MU6| exact WM6| exact MI6| exact ST6| ].
        - apply Forall_cons; [|apply Forall_nil]. right; right; left. apply Exists_cons_hd. cbn [fb_addr fb_size fst snd]. lia.
        - intros a Ha. cbn [outside fst snd]. lia. }
      split; [eapply agrees_rw_cells; [exact AGS| exact FRA|]; intros a Ha; cbn [cells_size csize Nat.add] in Ha; cbn [outside fst snd]; lia|].
      split; [eapply agrees_rw_cells; [exact AGS| exact HE|]; intros a Ha; cbn [cells_size csize Nat.add] in Ha; cbn [outside fst snd]; lia|].
      eapply agrees_rw_cells; [exact AGS| exact HEB|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. cbn [outside fst snd]. lia. }
    (* [comment removed for export] *)
    assert (GOFILL : forall (m6 : mem) (sw : bool) (c0 c1 c2 c3 : Z) (POSTQ' : check_result -> PState H hptr -> footprint -> machine_state -> Prop)
                       (rax t0x t1x t2x a0x a1x a2x a3x a4x a5x a6x a7x t3x t4x t5x t6x : word),
              POSTQ' = check_header_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CL FB lo MG EB ERR [mg0; mg1; mg2; mg3] f m o ->
              (0 <= c0 < 256)%Z -> (0 <= c1 < 256)%Z -> (0 <= c2 < 256)%Z -> (0 <= c3 < 256)%Z -> (28 <= le4val c0 c1 c2 c3 <= 1048576)%Z ->
              mem_inv asegs m6 -> munch [(Fb + 32, Fb + 52)]%Z mm m6 -> wmono asegs mm m6 ->
              rw_cells asegs m6 Fb [C8 k0; C8 k1; C8 k2; CB 8 fpre; C4 (Z_to_bv 64 (le4val c0 c1 c2 c3)); CB 12 fmid; C4 (Z_to_bv 64 BYTE_ORDER_MAGIC); CB 4 fpost;
                                    C8 (Z_to_bv 64 (fflagA L FF_NG_CHECK_HEADER Fb))] ->
              evtF asegs RNGx (fun ms' => implMG RNGx (ngc_open MOps PR fuel f 0 BT_SHB sw (le4val c0 c1 c2 c3)) sx POSTQ' ms')
                (MS (mkR rax (Z_to_bv 64 SPA) gp tp t0x t1x t2x sp (Z_to_bv 64 SPA) a0x a1x a2x a3x a4x a5x a6x a7x
                         (Z_to_bv 64 Fb) (Z_to_bv 64 ERR) (Z_to_bv 64 (Z.shiftr ERR 3 + 2147450880)) (Z_to_bv 64 FA) (Z_to_bv 64 (Fb + 48)) (Z_to_bv 64 (Z.b2z sw)) (Z_to_bv 64 (sxv c0 c1 c2 c3))
                         (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 2147450880) (Z_to_bv 64 Fb) t3x t4x t5x t6x)
                    F (Z_to_bv 64 0x8af9c) fc None m6 (seg_rom asegs))).
    { intros until t6x. intros -> C0 C1 C2 C3 TLR MI6 MU6 WM6 FRC6.
      destruct (AT6 m6 [CB 8 fpre; C4 (Z_to_bv 64 (le4val c0 c1 c2 c3)); CB 12 fmid; C4 (Z_to_bv 64 BYTE_ORDER_MAGIC); CB 4 fpost] MI6 MU6 WM6 eq_refl FRC6) as (INV6 & FRA6 & HE6 & HEB6).
      replace (sxv c0 c1 c2 c3) with (le4val c0 c1 c2 c3) by (unfold sxv, le4val in *; dm_plia).
      destruct (rw_cells_cut _ _ _ 5 FRA6) as [FRA5 FCUR6]. cbn [firstn skipn cells_size csize Nat.add] in FRA5, FCUR6.
      lazymatch type of FCUR6 with rw_cells _ _ ?A _ => replace A with (SPA + 128)%Z in FCUR6 by lia end.
      apply evtF_done.
      eapply (FILL fuel) with (sw := sw) (TL := le4val c0 c1 c2 c3) (j0 := j0) (j := j) (ccs := [CB 24 j2]) (fpre := fpre) (fmid := fmid) (fpost := fpost) (k0 := k0) (k1 := k1) (k2 := k2)
               (tlw := Z_to_bv 64 (le4val c0 c1 c2 c3)) (e := e);
        [ exact CTX | exact INV6 | exact TLR | exact FRA5 | exact FCUR6 | reflexivity | exact FRC6 | exact HE6 | exact HEB6 ]. }
    assert (GOLEN : forall (m6 : mem) (c0 c1 c2 c3 : Z) (POSTQ' : check_result -> PState H hptr -> footprint -> machine_state -> Prop) (fcs6 : list cell)
                      (rax t0x t1x t2x a0x a1x a2x a3x a4x a5x a6x a7x r21 r22 r23 t3x t4x t5x t6x : word),
              POSTQ' = check_header_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CL FB lo MG EB ERR [mg0; mg1; mg2; mg3] f m o ->
              (0 <= c0 < 256)%Z -> (0 <= c1 < 256)%Z -> (0 <= c2 < 256)%Z -> (0 <= c3 < 256)%Z ->
              mem_inv asegs m6 -> munch [(Fb + 32, Fb + 52)]%Z mm m6 -> wmono asegs mm m6 -> cells_size fcs6 = 32%nat ->
              rw_cells asegs m6 Fb ([C8 k0; C8 k1; C8 k2] ++ fcs6 ++ [C8 (Z_to_bv 64 (fflagA L FF_NG_CHECK_HEADER Fb))]) ->
              evtF asegs RNGx (fun ms' => implMG RNGx (e_fret PR FF_NG_CHECK_HEADER (CH_Err (Msg.shb_invalid_length (le4val c0 c1 c2 c3)))) sx POSTQ' ms')
                (MS (mkR rax (Z_to_bv 64 SPA) gp tp t0x t1x t2x sp (Z_to_bv 64 SPA) a0x a1x a2x a3x a4x a5x a6x a7x
                         (Z_to_bv 64 Fb) (Z_to_bv 64 ERR) (Z_to_bv 64 (Z.shiftr ERR 3 + 2147450880)) r21 r22 r23 (Z_to_bv 64 (sxv c0 c1 c2 c3))
                         (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 2147450880) (Z_to_bv 64 Fb) t3x t4x t5x t6x)
                    F (Z_to_bv 64 0x8aedc) fc None m6 (seg_rom asegs))).
    { intros until t6x. intros -> C0 C1 C2 C3 MI6 MU6 WM6 Hf6 FRC6.
      destruct (AT6 m6 fcs6 MI6 MU6 WM6 Hf6 FRC6) as (INV6 & FRA6 & HE6 & HEB6).
      apply evtF_done.
      eapply LENFAIL with (TL := le4val c0 c1 c2 c3) (hi := (c3 / 128 * 4294967295)%Z) (j0 := j0) (j := j) (j2 := j2) (fcs := fcs6) (k0 := k0) (k1 := k1) (k2 := k2) (e := e);
        [ exact CTX | exact INV6 | rewrite unsigned_lit by (unfold sxv, le4val; dm_plia); unfold sxv; reflexivity
        | unfold le4val; lia | dm_plia | exact FRA6 | exact FRC6 | exact Hf6 | exact HE6 | exact HEB6 ]. }
    (* [comment removed for export] *)
    assert (LENCK : forall c0 c1 c2 c3, (0 <= c0 < 256)%Z -> (0 <= c1 < 256)%Z -> (0 <= c2 < 256)%Z -> (0 <= c3 < 256)%Z ->
              bv_ltu (Z_to_bv 64 (-1048550)) (Z_to_bv 64 (bv_swrap 32 (sxv c0 c1 c2 c3 mod 18446744073709551616 + 18446744073708503039)))
              = ((28 <=? le4val c0 c1 c2 c3) && (le4val c0 c1 c2 c3 <=? 1048576))%Z).
    { intros c0 c1 c2 c3 C0 C1 C2 C3. unfold bv_ltu. rewrite !unsigned_lit_wrap.
      unfold sxv, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. cbn -[Z.add Z.sub Z.modulo Z.mul Z.div Z.ltb Z.leb andb Z.pow le4val].
      change (2^64)%Z with 18446744073709551616%Z. change (2 ^ (32 - 1))%Z with 2147483648%Z. change (2^32)%Z with 4294967296%Z.
      assert (LR : (0 <= le4val c0 c1 c2 c3 < 4294967296)%Z) by (unfold le4val; lia).
      destruct (Z.leb_spec 28 (le4val c0 c1 c2 c3)); destruct (Z.leb_spec (le4val c0 c1 c2 c3) 1048576); cbn [andb];
        first [apply Z.ltb_lt | apply Z.ltb_ge]; dm_plia. }
    hide FRA. hide HE. hide HEB. hide FR. hide MGc. hide SHC.
    pose proof (munch_refl [(Fb + 32, Fb + 52)]%Z mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    ienterG.
    zstep. rewrite (sx32_lit b0 b1 b2 b3) by lia. do 3 zstep.
    rewrite (EQB 439041101%Z) by lia.
    destruct (Z.eqb_spec (le4val b0 b1 b2 b3) 439041101) as [EQN|NEN]; cbn [negb]; cbv iota.
    - (* [comment removed for export] *)
      replace (le4val b0 b1 b2 b3 =? BYTE_ORDER_MAGIC)%Z with true by (symmetry; apply Z.eqb_eq; exact EQN). cbv beta iota. cbn [negb]. cbv iota.
      zstep. zstep. rewrite (sx32_lit q0 q1 q2 q3) by lia. do 4 zstep. zstep.
      rewrite (LENCK q0 q1 q2 q3) by lia.
      rewrite EQN in FRC4.
      destruct ((28 <=? le4val q0 q1 q2 q3) && (le4val q0 q1 q2 q3 <=? 1048576))%Z eqn:LC.
      + replace ((le4val q0 q1 q2 q3 <? 28) || (BT_SHB_INSANE_MAX <? le4val q0 q1 q2 q3))%Z with false by (unfold BT_SHB_INSANE_MAX; lia). cbv iota.
        eapply (GOFILL mm false q0 q1 q2 q3); [reflexivity| lia| lia| lia| lia| lia| exact MI| exact MU| exact WM| exact FRC4].
      + replace ((le4val q0 q1 q2 q3 <? 28) || (BT_SHB_INSANE_MAX <? le4val q0 q1 q2 q3))%Z with true by (unfold BT_SHB_INSANE_MAX; lia). cbv iota.
        eapply (GOLEN mm q0 q1 q2 q3) with (fcs6 := [CB 8 fpre; C4 (Z_to_bv 64 (le4val q0 q1 q2 q3)); CB 12 fmid; C4 (Z_to_bv 64 439041101); CB 4 fpost]);
          [reflexivity| lia| lia| lia| lia| exact MI| exact MU| exact WM| reflexivity| exact FRC4].
    - (* [comment removed for export] *)
      replace (le4val b0 b1 b2 b3 =? BYTE_ORDER_MAGIC)%Z with false by (symmetry; apply Z.eqb_neq; exact NEN).
      do 13 zstep. zstep. zstep.
      assert (SWV : forall a b c d, (0 <= a < 256)%Z -> (0 <= b < 256)%Z -> (0 <= c < 256)%Z -> (0 <= d < 256)%Z ->
        le4 (Z_to_bv 64 (Z.lor (Z.lor (Z.shiftl (sxv a b c d mod 18446744073709551616) 24 mod 18446744073709551616)
                                      (Z.shiftl (Z.land (sxv a b c d mod 18446744073709551616) 65280) 8 mod 18446744073709551616))
                               (Z.lor (Z.land (Z.shiftr (sxv a b c d mod 18446744073709551616) 8) 65280)
                                      (bv_swrap 32 (Z.shiftr (bv_wrap 32 (sxv a b c d mod 18446744073709551616)) 24) mod 18446744073709551616))))
        = le4 (Z_to_bv 64 (le4val d c b a))).
      { intros a b c d Ha Hb Hc Hd.
        assert (SR : (0 <= sxv a b c d < 2^64)%Z) by (unfold sxv, le4val; dm_plia).
        replace (sxv a b c d mod 18446744073709551616)%Z with (bv_unsigned (Z_to_bv 64 (sxv a b c d))) by (rewrite unsigned_lit by lia; symmetry; apply Z.mod_small; lia).
        rewrite (le4_lit d c b a) by lia.
        apply (le4_of_val _ d c b a (b + 256 * c + 65536 * d + 16777216 * ((d / 128 * 4294967295) mod 256))); [lia|lia|lia|lia| dm_plia|].
        apply (swap32_valA _ a b c d (d / 128 * 4294967295)); [lia|lia|lia|lia| dm_plia| rewrite unsigned_lit by lia; unfold sxv, le4val; lia]. }
      lazymatch goal with HC : rw_cells asegs ?mx Fb [C8 k0; C8 k1; C8 k2; CB 8 fpre; ?c1; CB 12 fmid; C4 ?w; CB 4 fpost; ?fl] |- _ =>
        assert (FRC5 : rw_cells asegs mx Fb [C8 k0; C8 k1; C8 k2; CB 8 fpre; c1; CB 12 fmid; C4 (Z_to_bv 64 (le4val b3 b2 b1 b0)); CB 4 fpost; fl])
          by (eapply rw_cells_recell; [exact HC | pose proof (proj1 (proj1 HC)) as WF; cbn in WF |- *; repeat split; clear - WF; tauto |];
              cbn [cells_bytes cbytes app]; rewrite (SWV b0 b1 b2 b3) by lia; reflexivity);
        clear HC end.
      rewrite (EQB 1295788826%Z) by lia.
      destruct (Z.eqb_spec (le4val b0 b1 b2 b3) 1295788826) as [EQS|NES]; cbn [negb]; cbv iota.
      + (* [comment removed for export] *)
        replace (le4val b3 b2 b1 b0 =? BYTE_ORDER_MAGIC)%Z with true by (symmetry; apply Z.eqb_eq; unfold le4val, BYTE_ORDER_MAGIC in *; lia).
        cbv beta iota. cbn [negb]. cbv iota.
        zstep. rewrite (sx32_lit q0 q1 q2 q3) by lia.
        do 9 zstep. zstep.
        lazymatch goal with HC : rw_cells asegs ?mx Fb [C8 k0; C8 k1; C8 k2; CB 8 fpre; C4 ?w; CB 12 fmid; ?c2; CB 4 fpost; ?fl] |- _ =>
          assert (FRC6 : rw_cells asegs mx Fb [C8 k0; C8 k1; C8 k2; CB 8 fpre; C4 (Z_to_bv 64 (le4val q3 q2 q1 q0)); CB 12 fmid; c2; CB 4 fpost; fl])
            by (eapply rw_cells_recell; [exact HC | pose proof (proj1 (proj1 HC)) as WF; cbn in WF |- *; repeat split; clear - WF; tauto |];
                cbn [cells_bytes cbytes app]; rewrite (SWV q0 q1 q2 q3) by lia; reflexivity);
          clear HC end.
        zstep. zstep. rewrite (sx32_lit q3 q2 q1 q0) by lia.
        do 4 zstep. zstep.
        rewrite (LENCK q3 q2 q1 q0) by lia.
        assert (EQM : le4val b3 b2 b1 b0 = BYTE_ORDER_MAGIC) by (unfold le4val, BYTE_ORDER_MAGIC in *; lia).
        rewrite EQM in FRC6.
        destruct ((28 <=? le4val q3 q2 q1 q0) && (le4val q3 q2 q1 q0 <=? 1048576))%Z eqn:LC.
        * replace ((le4val q3 q2 q1 q0 <? 28) || (BT_SHB_INSANE_MAX <? le4val q3 q2 q1 q0))%Z with false by (unfold BT_SHB_INSANE_MAX; lia). cbv iota.
          eapply (GOFILL m1 true q3 q2 q1 q0); [reflexivity| lia| lia| lia| lia| lia| exact MI| exact MU| exact WM| exact FRC6].
        * replace ((le4val q3 q2 q1 q0 <? 28) || (BT_SHB_INSANE_MAX <? le4val q3 q2 q1 q0))%Z with true by (unfold BT_SHB_INSANE_MAX; lia). cbv iota.
          eapply (GOLEN m1 q3 q2 q1 q0) with (fcs6 := [CB 8 fpre; C4 (Z_to_bv 64 (le4val q3 q2 q1 q0)); CB 12 fmid; C4 (Z_to_bv 64 BYTE_ORDER_MAGIC); CB 4 fpost]);
            [reflexivity| lia| lia| lia| lia| exact MI| exact MU| exact WM| reflexivity| exact FRC6].
      + (* [comment removed for export] *)
        replace (le4val b3 b2 b1 b0 =? BYTE_ORDER_MAGIC)%Z with false by (symmetry; apply Z.eqb_neq; unfold le4val, BYTE_ORDER_MAGIC in *; lia).
        cbv beta iota. cbn [negb]. cbv iota.
        destruct (AT6 m0 [CB 8 fpre; C4 (Z_to_bv 64 (le4val q0 q1 q2 q3)); CB 12 fmid; C4 (Z_to_bv 64 (le4val b3 b2 b1 b0)); CB 4 fpost] MI MU WM eq_refl FRC5) as (INV6 & FRA6 & HE6 & HEB6).
        zstep. zstep.
        apply evtF_done. subst POSTQ.
        eapply (ngc_exit FO GIOA TP fflagA GL FRET) with (PB := ([] : list cblk)) (fcs := [CB 8 fpre; C4 (Z_to_bv 64 (le4val q0 q1 q2 q3)); CB 12 fmid; C4 (Z_to_bv 64 (le4val b3 b2 b1 b0)); CB 4 fpost])
            (k0 := k0) (k1 := k1) (k2 := k2) (ew := z64) (r := CH_NotMe);
          [ exact CTX | exact INV6 | exact FRA6 | reflexivity | exact FRC5 | reflexivity | exact HE6
          | cbn [ngc_result]; split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|]; exists e; exact HEB6 ].
  Qed.
  End Sz1.
  Theorem ngc_bom : ltac:(let t := eval cbv delta [ngc_bom__stmt] in ngc_bom__stmt in exact t).
  Proof using GL FRET FILL LENFAIL. red. intros fuel ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic m o RNGx sx mm ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r23 t3 t4 t5 t6 tlb bomb j0 j j2 fpre fmid fpost k0 k1 k2 e. ltac2:(SecDiet.SzSec.closeP 'ngc_bom__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End NgcBom.
End CANSEC1.
End TwB.
End F_ngchk_hbomA.

(* [comment removed for export] *)
Module F_ngchk_msgA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep Frame StoreFast Image.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require FmtFacts__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.FmtFacts.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow StepF SysStepF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg ABase AMalloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA Pcap_iface_ngA LibcKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FrameKit__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FmtKitA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngchk_defsA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require LibcKit2__A3P. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.MonadGX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ngA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.PerfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FmtKitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_defsA__A3P.F_ngchk_defsA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit2__A3P.F_ngchk_kitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit2__A3P.F_ngchk_ngiA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit2__A3P.F_ngchk_fail3A.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= unp_store m a bs n Hn Ha Hl.
Local Ltac transport_call_extra segs W m m' MU WM ::= unp_call W m m' MU.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Ltac ienterG := lazymatch goal with |- implMG _ _ _ ?Q _ => let QQ := fresh "POSTQ" in set (QQ := Q) end; apply implMG_from_evtF.

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section NgcMsg.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis FRET : fret_inline_law FO GIOA fflagA.
  Hypothesis FREE : free_stmt_o HO GIOA.
  Hypothesis FREENULL : free_null_stmt_o GIOA.
  Hypothesis SNPRINTF : snprintf_spec_stmt GIOA.
  #[local] Notation cblk := (@cblock hptr).
  #[local] Notation NGFR Fb := (FF_NG_CHECK_HEADER, Fb, 64%Z).

  (* [comment removed for export] *)
  Definition ngc_inv_munch__stmt : Prop := forall ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic o m
      RNGx sx PB mm my (wlo n : Z),
    ngc_ctx TP ra sp tp s0 L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic m ->
    ngc_inv GIOA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo MG EB ERR SPA Fb magic o m RNGx sx PB mm ->
    munch [(wlo, SPA); (EB, EB + n)]%Z mm my -> wmono asegs mm my -> mem_inv asegs my -> stk asegs my lo SPA ->
    (ATOP + 4096 <= wlo)%Z -> (0 < n <= 256)%Z ->
    ngc_inv GIOA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo MG EB ERR SPA Fb magic o m RNGx sx PB my.
  Section Sz1.
  Variables ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic o m RNGx sx PB mm my wlo n : ltac2:(SecDiet.SzSec.tyM 'ngc_inv_munch__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma ngc_inv_munch__body : ltac2:(SecDiet.SzSec.bodyP 'ngc_inv_munch__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL.
 intros CTX INV MU WM MIy STy HW Hn.
    pose proof CTX as (LO & BU & (SPT & TOP47) & TPE & ALN & (RSTK & RIMG & RISH & RTLS) & UC & TR & NF & HinF & MGR & MGL & OMG & OERR & DME & OEB & DEE & DEM & ERR4 & EB8 & SPAB & SPA32).
    pose proof INV as (FP & G & OF & MI & ST & STG & FR & AG & MGc & SHC).
    unfold PCAP_L2_STACK in BU.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. atop_facts.
    assert (FWs : Forall (own_ivA [NGFR Fb] PB (bv_unsigned sp)) [(wlo, SPA)]%Z) by (apply Forall_cons; [left; cbn [fst snd]; lia| apply Forall_nil]).
    assert (FXs : Forall (cobj_iv FL CL) [(EB, EB + n)]%Z).
    { apply Forall_cons; [|apply Forall_nil]. split; [cbn [fst snd]| cbn [fst snd]; lia]. replace (EB + n - EB)%Z with n by lia.
      destruct (proj1 OEB) as [(b & Hb & H1 & H2)|(fr & Hf & H1 & H2)]; [left; exists b| right; exists fr]; (split; [assumption|]; split; lia). }
    destruct (own_writes _ _ _ GL _ _ _ _ _ _ _ _ _ my _ _ _ FWs FXs G MU WM ltac:(lia)) as [Gy AGy].
    assert (AGS : agrees_on (fun a => outside [(wlo, SPA); (EB, EB + n)]%Z a) mm my) by (eapply agrees_on_of_munch; [exact MU | exact WM | intros a _ Ho; exact Ho]).
    assert (ICL : incl CL (CL ++ PB)) by (apply incl_appl, incl_refl).
    assert (IFL : incl FL (NGFR Fb :: FL)) by (apply incl_tl, incl_refl).
    pose proof (clocA_below _ _ _ GL _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OMG) ICL IFL)) as (MGLO & MGHI).
    pose proof (clocA_below _ _ _ GL _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OEB) ICL IFL)) as (EBLO & EBHI).
    destruct (gl_frames _ _ _ GL _ _ _ _ _ _ _ G) as [FAll _]. pose proof (Forall_inv FAll) as (FBAND & FTOP & F64 & _ & _ & _ & _ & _).
    cbn [fb_addr fb_size fst snd] in FBAND, FTOP, F64. pose proof (ablk_lin _ _ FBAND) as (FIMG & Fb0 & _ & _). unfold AIMG_HI in FIMG.
    band_ind FBAND bF.
    pose proof (clocA_ablk _ _ _ GL _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OEB) ICL IFL) ltac:(lia)) as EBBAND. band_ind EBBAND bB.
    assert (SHE : (Z.shiftr Fb 3 + 2147450880 = Fb / 8 + 2147450880)%Z) by (rewrite Z.shiftr_div_pow2 by lia; reflexivity).
    split; [exact FP|]. split; [exact Gy|]. split; [exact OF|]. split; [exact MIy|]. split; [exact STy|].
    split. { eapply agrees_stk; [exact AGS| exact STG|]. intros a Ha. cbn [outside fst snd]. lia. }
    split. { eapply agrees_rw_cells; [exact AGS| exact FR|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. cbn [outside fst snd]. lia. }
    split. { eapply agrees_on_trans; [exact AG|]. eapply agrees_on_weaken; [exact AGy|]. intros a (K & N1 & N2 & _). split; [exact K|]. cbn [outside fst snd] in *. lia. }
    split. { destruct magic as [|mg0 [|mg1 [|mg2 [|mg3 [|? ?]]]]]; try discriminate MGL. cbn [map] in MGc |- *.
             eapply agrees_rw_cells; [exact AGS| exact MGc|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. cbn [outside fst snd]. lia. }
    eapply agrees_rw_cells; [exact AGS| exact SHC|]. intros a Ha. unfold ngc_shadow in Ha. cbn [cells_size csize Nat.add] in Ha. cbn [outside fst snd].
    rewrite SHE in Ha. Z.div_mod_to_equations. lia.
  Qed.
  End Sz1.
  Lemma ngc_inv_munch : ltac:(let t := eval cbv delta [ngc_inv_munch__stmt] in ngc_inv_munch__stmt in exact t).
  Proof using GL. intros ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic o m RNGx sx PB mm my wlo n. ltac2:(SecDiet.SzSec.closeP 'ngc_inv_munch__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
  (* [comment removed for export] *)
  Definition ngc_failM (i : option hptr) (qb qs : hptr) (msg : list Z) : Monad.M (PState H hptr) (@check_result hptr hptr) :=
    mbind (match i with Some qi => pfree HO qi | None => mret tt end)
          (fun _ => mbind (pfree HO qb) (fun _ => mbind (pfree HO qs) (fun _ => fo_ret FO _ FF_NG_CHECK_HEADER (CH_Err msg)))).

  (* [comment removed for export] *)
  Definition ngc_mcp_fail__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (CL FB : list cblk) (FL : list fblock) (trC : list Z)
      (lo MG FA EB ERR SPA Fb : Z) (f : hptr) (magic : list Z) (m : mem) (o : option hptr)
      (RNGx : footprint) (sx : PState H hptr) (mm : mem)
      (ra0 t0 t1 t2 a0 a3 a4 a5 a6 a7 r21 r22 r23 r24 t3 t4 t5 t6 : word)
      (j : list byte) (ccs fcs : list cell) (k0 k1 k2 : word) (e : list byte)
      (i : option hptr) (sg : pcap_ng_sf) (qs qb : hptr) (P B I nb : Z) (SRC n : Z) (msg : list Z),
    ngc_ctx TP ra sp tp s0 L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic m ->
    ngc_inv GIOA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo MG EB ERR SPA Fb magic o m RNGx sx ((qs, P, 680%Z) :: (qb, B, nb) :: IBLK i I sg) mm ->
    match i with Some _ => True | None => I = 0%Z end ->
    rw_cells asegs mm SPA (ngc_spill P EB Fb j) -> rw_cells asegs mm (SPA + 128) ccs -> cells_size ccs = 24%nat ->
    rw_cells asegs mm Fb ([C8 k0; C8 k1; C8 k2] ++ fcs ++ [C8 (Z_to_bv 64 (fflagA L FF_NG_CHECK_HEADER Fb))]) -> cells_size fcs = 32%nat ->
    rw_cells asegs mm ERR [C4 z64] -> rw_cells asegs mm EB [CB 256 e] ->
    rw_cells asegs mm (P + 24) [C8 (Z_to_bv 64 B)] -> rw_cells asegs mm (P + 672) [C8 (Z_to_bv 64 I)] ->
    bytes_at asegs mm SRC (map b8 msg ++ [Z_to_bv 8 0]) -> (Z.of_nat (length msg) + 1 = n)%Z -> (n <= 256)%Z -> In (SRC, n) client_globals ->
    Forall (fun z => 0 < z < 256)%Z msg ->
    implMG RNGx (ngc_failM i qb qs msg) sx
      (check_header_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CL FB lo MG EB ERR magic f m o)
      (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) a0 (Z_to_bv 64 SRC) (Z_to_bv 64 n) a3 a4 a5 a6 a7
               (Z_to_bv 64 Fb) (Z_to_bv 64 ERR) (Z_to_bv 64 (Z.shiftr ERR 3 + 2147450880)) r21 r22 r23 r24 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880))
               (Z_to_bv 64 2147450880) (Z_to_bv 64 Fb) t3 t4 t5 t6)
          F (Z_to_bv 64 0x8b434) fc None mm (seg_rom asegs)).
  Section Sz2.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic m o RNGx sx mm ra0 t0 t1 t2 a0 a3 a4 a5 a6 a7 r21 r22 r23 r24 t3 t4 t5 t6 j ccs fcs k0 k1 k2 e i sg qs qb P B I nb SRC n msg : ltac2:(SecDiet.SzSec.tyM 'ngc_mcp_fail__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma ngc_mcp_fail__body : ltac2:(SecDiet.SzSec.bodyP 'ngc_mcp_fail__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL FRET FREE FREENULL.
 intros CTX INV HI FRA FCUR Hccs FRC Hfcs HE HEB HPB HPI SRCB LN NB HG MOK.
    ngc_setup GL CTX INV.
    assert (ESPA : bv_unsigned (Z_to_bv 64 SPA) = SPA) by (apply unsigned_lit; lia).
    assert (HinP : In (qs, P, 680%Z) ((qs, P, 680%Z) :: (qb, B, nb) :: IBLK i I sg)) by (left; reflexivity).
    pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G ltac:(apply in_or_app; left; apply in_or_app; right; exact HinP)) as ((PBAND & _ & PTOP & P16) & P0 & _).
    cbn [cb_addr cb_size fst snd] in PBAND, PTOP, P16, P0. band_ind PBAND bP.
    destruct (clocA_apart_block _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OEB) (incl_refl _) IFL) HinP ltac:(lia) ltac:(cbn; lia)) as (kP & kPr & kP1 & kP2).
    cbn [cb_addr cb_size fst snd] in kP1, kP2.
    pose proof (gl_rt _ _ _ GL _ _ _ _ _ _ _ G) as (RT & _).
    pose proof (gia_global_mobjA _ _ _ GL _ _ _ _ _ _ _ _ _ G HG RIMG RISH) as OSRC.
    edestruct (ngc_cobj_now FO GIOA TP fflagA GL) as (_ & _ & OEB'); [exact CTX| exact INV|].
    pose proof (client_globals_lo (SRC, n) HG) as (GLO & GN & GHI). cbn [fst snd] in GLO, GN, GHI.
    assert (LM : Z.to_nat n = (length msg + 1)%nat) by lia.
    assert (LS : length (map b8 msg ++ [Z_to_bv 8 0]) = Z.to_nat n) by (rewrite length_app, length_map; cbn [length]; lia).
    pose proof (rw_cells_split_CB asegs _ _ [] _ _ [] [Z.to_nat n; (256 - Z.to_nat n)%nat] HEB ltac:(cbn; lia)) as HE'. clear HEB. cbn [mk_CB_cells app] in HE'.
    destruct (rw_cells_cut _ _ _ 1 HE') as [HE1 HE2]. clear HE'. cbn [firstn skipn cells_size csize Nat.add] in HE1, HE2.
    lazymatch type of HE2 with rw_cells _ _ ?A _ => replace A with (EB + n)%Z in HE2 by lia end.
    unfold ngc_spill in FRA.
    pose proof (munch_refl [(SPA - 2224, SPA); (EB, EB + n)]%Z mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    ienterG.
    zstep. zstep.
    remember (Z_to_bv 64 SPA) as spa eqn:Espa.
    assert (Hspa : bv_unsigned spa = SPA) by (rewrite Espa; apply unsigned_lit; lia).
    eapply evtF_cut.
    { eapply (asan_memcpy_specZ RNGx _ spa) with (lo := lo) (Dst := EB) (Src := SRC) (n := n) (src := map b8 msg ++ [Z_to_bv 8 0]) (junk := firstn (Z.to_nat n) e);
        [ reflexivity | reflexivity | reflexivity | exact MI | rewrite Hspa; exact ST | rewrite Hspa; lia | lia | exact RT | exact SRCB | exact LS | lia | exact HE1
        | lia
        | exact OSRC
        | eapply mobjA_sub; [apply aobjA_mobjA; [exact (proj2 OEB')| lia]| lia| lia| lia]
        | atop_facts; lia | atop_facts; lia | exact RIMG | rewrite Hspa; eapply rng_sub'; [exact RSPW| lia] ]. }
    cbv beta. intros ms' PO. destruct_exs PO. destruct PO as (-> & MU7 & WM7 & MI7 & ST7 & HD7 & SRC7).
    rewrite Hspa in *. clear Hspa. subst spa.
    replace (ret_pc (Z_to_bv 64 570428)) with (Z_to_bv 64 570428) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    lazymatch type of MU7 with munch _ _ ?mb =>
      assert (INV7 : ngc_inv GIOA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo MG EB ERR SPA Fb [mg0; mg1; mg2; mg3] o m RNGx sx ((qs, P, 680%Z) :: (qb, B, nb) :: IBLK i I sg) mb)
        by (eapply ngc_inv_munch; [exact CTX| exact INV| exact MU7| exact WM7| exact MI7| exact ST7| lia| lia]) end.
    lazymatch type of MU7 with munch _ _ ?mb =>
      assert (AGS : agrees_on (fun a => outside [(SPA - 2224, SPA); (EB, EB + n)]%Z a) mm mb) by (eapply agrees_on_of_munch; [exact MU7 | exact WM7 | intros a _ Ho; exact Ho]);
      assert (FRC7 : rw_cells asegs mb Fb ([C8 k0; C8 k1; C8 k2] ++ fcs ++ [C8 (Z_to_bv 64 (fflagA L FF_NG_CHECK_HEADER Fb))]))
        by (eapply agrees_rw_cells; [exact AGS| exact FRC|]; intros a Ha; rewrite !cells_size_app, Hfcs in Ha; cbn [cells_size csize Nat.add] in Ha; cbn [outside fst snd]; lia) end.
    clear FRC SRCB.
    lazymatch type of MU7 with munch _ ?ma ?mb => transport_after_call asegs ma mb MU7 WM7 end.
    lazymatch type of HE2 with rw_cells _ ?mb _ [CB _ ?jj] =>
      assert (HEB7 : rw_cells asegs mb EB [CB (length msg + 1) (map b8 msg ++ [Z_to_bv 8 0]); CB (255 - length msg) jj]) end.
    { replace (EB + n)%Z with (EB + Z.of_nat (cells_size [CB (Z.to_nat n) (map b8 msg ++ [Z_to_bv 8 0])]))%Z in HE2 by (cbn [cells_size csize Nat.add]; lia).
      pose proof (rw_cells_uncut _ _ _ _ _ HD7 HE2 ltac:(reflexivity)) as X. cbn [app] in X. rewrite LM in X |- *.
      replace (256 - (length msg + 1))%nat with (255 - length msg)%nat in X |- * by lia. exact X. }
    apply evtF_done. subst POSTQ. unfold ngc_failM.
    eapply (ngc_fail3 HO FO GIOA TP fflagA GL FRET FREE FREENULL) with (j := j) (ccs := ccs) (fcs := fcs) (k0 := k0) (k1 := k1) (k2 := k2);
      [ exact CTX | exact INV7 | exact HI | exact FRA | exact FCUR | exact Hccs | exact FRC7 | exact Hfcs | exact HE | exact HEB7 | lia | exact MOK | exact HPB | exact HPI ].
  Qed.
  End Sz2.
  Lemma ngc_mcp_fail : ltac:(let t := eval cbv delta [ngc_mcp_fail__stmt] in ngc_mcp_fail__stmt in exact t).
  Proof using GL FRET FREE FREENULL. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic m o RNGx sx mm ra0 t0 t1 t2 a0 a3 a4 a5 a6 a7 r21 r22 r23 r24 t3 t4 t5 t6 j ccs fcs k0 k1 k2 e i sg qs qb P B I nb SRC n msg. ltac2:(SecDiet.SzSec.closeP 'ngc_mcp_fail__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
  (* [comment removed for export] *)
  Definition ngc_snp_fail__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (CL FB : list cblk) (FL : list fblock) (trC : list Z)
      (lo MG FA EB ERR SPA Fb : Z) (f : hptr) (magic : list Z) (m : mem) (o : option hptr)
      (RNGx : footprint) (sx : PState H hptr) (mm : mem)
      (t0 t1 t2 a3 a4 a5 a6 a7 r21 r22 r23 r24 t3 t4 t5 t6 : word)
      (j : list byte) (ccs fcs : list cell) (k0 k1 k2 : word) (e : list byte)
      (i : option hptr) (sg : pcap_ng_sf) (qs qb : hptr) (P B I nb : Z) (RA FMTA : Z) (fs : string) (args : list farg) (msg : list Z),
    ngc_ctx TP ra sp tp s0 L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic m ->
    ngc_inv GIOA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo MG EB ERR SPA Fb magic o m RNGx sx ((qs, P, 680%Z) :: (qb, B, nb) :: IBLK i I sg) mm ->
    match i with Some _ => True | None => I = 0%Z end ->
    rw_cells asegs mm SPA (ngc_spill P EB Fb j) -> rw_cells asegs mm (SPA + 128) ccs -> cells_size ccs = 24%nat ->
    rw_cells asegs mm Fb ([C8 k0; C8 k1; C8 k2] ++ fcs ++ [C8 (Z_to_bv 64 (fflagA L FF_NG_CHECK_HEADER Fb))]) -> cells_size fcs = 32%nat ->
    rw_cells asegs mm ERR [C4 z64] -> rw_cells asegs mm EB [CB 256 e] ->
    rw_cells asegs mm (P + 24) [C8 (Z_to_bv 64 B)] -> rw_cells asegs mm (P + 672) [C8 (Z_to_bv 64 I)] ->
    (RA = 0x8b374 \/ RA = 0x8b414)%Z ->
    fmt_at mm FMTA fs -> fmt_ok fs args = true -> (length args <= 3)%nat ->
    Forall2 (farg_word true L RNGx (NGFR Fb :: FL) (CL ++ (qs, P, 680%Z) :: (qb, B, nb) :: IBLK i I sg) SPA EB 256 mm) args (firstn (length args) [a3; a4; a5]) ->
    items_okb (fmt fs) = true -> Forall arg_ok args -> Fmt.snprintf 256 fs args = msg ->
    implMG RNGx (ngc_failM i qb qs msg) sx
      (check_header_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CL FB lo MG EB ERR magic f m o)
      (MS (mkR (Z_to_bv 64 RA) (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) (Z_to_bv 64 EB) (Z_to_bv 64 256) (Z_to_bv 64 FMTA) a3 a4 a5 a6 a7
               (Z_to_bv 64 Fb) (Z_to_bv 64 ERR) (Z_to_bv 64 (Z.shiftr ERR 3 + 2147450880)) r21 r22 r23 r24 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880))
               (Z_to_bv 64 2147450880) (Z_to_bv 64 Fb) t3 t4 t5 t6)
          F (Z_to_bv 64 SNPRINTF_ENTRY) fc None mm (seg_rom asegs)).
  Section Sz3.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic m o RNGx sx mm t0 t1 t2 a3 a4 a5 a6 a7 r21 r22 r23 r24 t3 t4 t5 t6 j ccs fcs k0 k1 k2 e i sg qs qb P B I nb RA FMTA fs args msg : ltac2:(SecDiet.SzSec.tyM 'ngc_snp_fail__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma ngc_snp_fail__body : ltac2:(SecDiet.SzSec.bodyP 'ngc_snp_fail__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL FRET FREE FREENULL SNPRINTF.
 intros CTX INV HI FRA FCUR Hccs FRC Hfcs HE HEB HPB HPI HRA FAT FOK ALEN FW FIT AOK EMSG.
    ngc_setup GL CTX INV.
    assert (ESPA : bv_unsigned (Z_to_bv 64 SPA) = SPA) by (apply unsigned_lit; lia).
    assert (HinP : In (qs, P, 680%Z) ((qs, P, 680%Z) :: (qb, B, nb) :: IBLK i I sg)) by (left; reflexivity).
    pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G ltac:(apply in_or_app; left; apply in_or_app; right; exact HinP)) as ((PBAND & _ & PTOP & P16) & P0 & _).
    cbn [cb_addr cb_size fst snd] in PBAND, PTOP, P16, P0. band_ind PBAND bP.
    destruct (clocA_apart_block _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OEB) (incl_refl _) IFL) HinP ltac:(lia) ltac:(cbn; lia)) as (kP & kPr & kP1 & kP2).
    cbn [cb_addr cb_size fst snd] in kP1, kP2.
    edestruct (ngc_cobj_now FO GIOA TP fflagA GL) as (_ & _ & OEB'); [exact CTX| exact INV|].
    assert (OEBx : cobjA RNGx mm (NGFR Fb :: FL) (CL ++ (qs, P, 680%Z) :: (qb, B, nb) :: IBLK i I sg) EB 256)
      by (split; [exact (clocA_incl _ _ _ _ _ _ (proj1 OEB') ICL IFL)| exact (proj2 OEB')]).
    unfold ngc_spill in FRA.
    pose proof (munch_refl [(SPA - 16384, SPA); (EB, EB + 256)]%Z mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    ienterG.
    remember (Z_to_bv 64 SPA) as spa eqn:Espa.
    assert (Hspa : bv_unsigned spa = SPA) by (rewrite Espa; apply unsigned_lit; lia).
    eapply evtF_cut.
    { eapply SNPRINTF with (L := L) (s := sx) (CL := (CL ++ (qs, P, 680%Z) :: (qb, B, nb) :: IBLK i I sg)%list) (FB := FB) (FL := NGFR Fb :: FL) (lo := lo) (DST := EB) (n := 256%Z) (FMTA := FMTA)
                           (fs := fs) (args := args) (junk := e);
        [ rewrite Espa; eapply (ngc_spo GIOA TP); [exact CTX| exact FP| exact G| exact ST| exact MI| unfold STDIO_STACK, PCAP_L2_STACK; lia]
        | reflexivity | reflexivity | reflexivity | lia | exact FAT | exact FOK | exact ALEN | rewrite Hspa; exact FW | exact HEB | exact OEBx ]. }
    cbv beta. intros ms' PO. destruct PO as (av6 & m6 & junk6 & E & MU6 & WM6 & MI6 & ST6 & -> & HEB6).
    unfold hpost_regs in E. destruct_exs E. subst ms'. rewrite Hspa in *. clear Hspa. subst spa.
    unfold STDIO_STACK in MU6.
    assert (INV6 : ngc_inv GIOA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo MG EB ERR SPA Fb [mg0; mg1; mg2; mg3] o m RNGx sx ((qs, P, 680%Z) :: (qb, B, nb) :: IBLK i I sg) m6)
      by (eapply ngc_inv_munch with (n := 256%Z); [exact CTX| exact INV| exact MU6| exact WM6| exact MI6| exact ST6| lia| lia]).
    assert (AGS : agrees_on (fun a => outside [(SPA - 16384, SPA); (EB, EB + 256)]%Z a) mm m6) by (eapply agrees_on_of_munch; [exact MU6 | exact WM6 | intros a _ Ho; exact Ho]).
    assert (FRC6 : rw_cells asegs m6 Fb ([C8 k0; C8 k1; C8 k2] ++ fcs ++ [C8 (Z_to_bv 64 (fflagA L FF_NG_CHECK_HEADER Fb))]))
      by (eapply agrees_rw_cells; [exact AGS| exact FRC|]; intros a Ha; rewrite !cells_size_app, Hfcs in Ha; cbn [cells_size csize Nat.add] in Ha; cbn [outside fst snd]; lia).
    clear FRC HEB.
    transport_after_call asegs mm m6 MU6 WM6.
    pose proof (snprintf_length_le 256 fs args ltac:(lia)) as LS. rewrite EMSG in LS, HEB6.
    change (Z.to_nat 256) with 256%nat in HEB6.
    replace (256 - length msg - 1)%nat with (255 - length msg)%nat in HEB6 by lia.
    assert (MOK : Forall (fun z => 0 < z < 256)%Z msg) by (rewrite <- EMSG; apply snprintf_ok; [exact FIT| exact AOK]).
    destruct HRA as [-> | ->];
      [ replace (ret_pc (Z_to_bv 64 0x8b374)) with (Z_to_bv 64 0x8b374) by (symmetry; apply ret_pc_even; [lia|reflexivity])
      | replace (ret_pc (Z_to_bv 64 0x8b414)) with (Z_to_bv 64 0x8b414) by (symmetry; apply ret_pc_even; [lia|reflexivity]) ].
    all: zstep.
    all: apply evtF_done; subst POSTQ; unfold ngc_failM;
      eapply (ngc_fail3 HO FO GIOA TP fflagA GL FRET FREE FREENULL) with (j := j) (ccs := ccs) (fcs := fcs) (k0 := k0) (k1 := k1) (k2 := k2);
      [ exact CTX | exact INV6 | exact HI | exact FRA | exact FCUR | exact Hccs | exact FRC6 | exact Hfcs | exact HE | exact HEB6 | lia | exact MOK | exact HPB | exact HPI ].
  Qed.
  End Sz3.
  Lemma ngc_snp_fail : ltac:(let t := eval cbv delta [ngc_snp_fail__stmt] in ngc_snp_fail__stmt in exact t).
  Proof using GL FRET FREE FREENULL SNPRINTF. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic m o RNGx sx mm t0 t1 t2 a3 a4 a5 a6 a7 r21 r22 r23 r24 t3 t4 t5 t6 j ccs fcs k0 k1 k2 e i sg qs qb P B I nb RA FMTA fs args msg. ltac2:(SecDiet.SzSec.closeP 'ngc_snp_fail__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End NgcMsg.
End CANSEC1.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P Require UbGuardB. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P Require UbGuardNgB__B3P.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Strings.String.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.StoreFast OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Image.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.FmtFacts.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB.
(* [comment removed for export] *)
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.MonadGX.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ngA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.PerfKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FmtKitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_defsA__A3P.F_ngchk_defsA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit2__A3P.F_ngchk_kitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit2__A3P.F_ngchk_ngiA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit2__A3P.F_ngchk_fail3A.TwB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.UbGuardB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.UbGuardNgB__B3P.UbGuardNgB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.UbGuardNgB__B3P.F_gfbdB.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= unp_store m a bs n Hn Ha Hl.
Local Ltac transport_call_extra segs W m m' MU WM ::= unp_call W m m' MU.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Ltac ienterG := lazymatch goal with |- implMG _ _ _ ?Q _ => let QQ := fresh "POSTQ" in set (QQ := Q) end; apply implMG_from_evtF.

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section NgcMsg.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis FRET : fret_inline_law FO GIOA fflagA.
  Hypothesis FREE : free_stmt_o HO GIOA.
  Hypothesis FREENULL : free_null_stmt_o GIOA.
  Hypothesis SNPRINTF : snprintf_spec_stmt GIOA.
  #[local] Notation cblk := (@cblock hptr).
  #[local] Notation NGFR Fb := (FF_NG_CHECK_HEADER, Fb, 64%Z).

  (* [comment removed for export] *)
  Definition ngc_inv_munch__stmt : Prop := forall ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic o m
      RNGx sx PB mm my (wlo n : Z),
    ngc_ctx TP ra sp tp s0 L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic m ->
    ngc_inv GIOA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo MG EB ERR SPA Fb magic o m RNGx sx PB mm ->
    munch [(wlo, SPA); (EB, EB + n)]%Z mm my -> wmono asegs mm my -> mem_inv asegs my -> stk asegs my lo SPA ->
    (ATOP + 4096 <= wlo)%Z -> (0 < n <= 256)%Z ->
    ngc_inv GIOA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo MG EB ERR SPA Fb magic o m RNGx sx PB my.
  Section Sz1.
  Variables ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic o m RNGx sx PB mm my wlo n : ltac2:(SecDiet.SzSec.tyM 'ngc_inv_munch__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma ngc_inv_munch__body : ltac2:(SecDiet.SzSec.bodyP 'ngc_inv_munch__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL.
 intros CTX INV MU WM MIy STy HW Hn.
    pose proof CTX as (LO & BU & (SPT & TOP47) & TPE & ALN & (RSTK & RIMG & RISH & RTLS) & UC & TR & NF & HinF & MGR & MGL & OMG & OERR & DME & OEB & DEE & DEM & ERR4 & EB8 & SPAB & SPA32).
    pose proof INV as (FP & G & OF & MI & ST & STG & FR & AG & MGc & SHC).
    unfold PCAP_L2_STACK in BU.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. atop_facts.
    assert (FWs : Forall (own_ivA [NGFR Fb] PB (bv_unsigned sp)) [(wlo, SPA)]%Z) by (apply Forall_cons; [left; cbn [fst snd]; lia| apply Forall_nil]).
    assert (FXs : Forall (cobj_iv FL CL) [(EB, EB + n)]%Z).
    { apply Forall_cons; [|apply Forall_nil]. split; [cbn [fst snd]| cbn [fst snd]; lia]. replace (EB + n - EB)%Z with n by lia.
      destruct (proj1 OEB) as [(b & Hb & H1 & H2)|(fr & Hf & H1 & H2)]; [left; exists b| right; exists fr]; (split; [assumption|]; split; lia). }
    destruct (own_writes _ _ _ GL _ _ _ _ _ _ _ _ _ my _ _ _ FWs FXs G MU WM ltac:(lia)) as [Gy AGy].
    assert (AGS : agrees_on (fun a => outside [(wlo, SPA); (EB, EB + n)]%Z a) mm my) by (eapply agrees_on_of_munch; [exact MU | exact WM | intros a _ Ho; exact Ho]).
    assert (ICL : incl CL (CL ++ PB)) by (apply incl_appl, incl_refl).
    assert (IFL : incl FL (NGFR Fb :: FL)) by (apply incl_tl, incl_refl).
    pose proof (clocA_below _ _ _ GL _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OMG) ICL IFL)) as (MGLO & MGHI).
    pose proof (clocA_below _ _ _ GL _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OEB) ICL IFL)) as (EBLO & EBHI).
    destruct (gl_frames _ _ _ GL _ _ _ _ _ _ _ G) as [FAll _]. pose proof (Forall_inv FAll) as (FBAND & FTOP & F64 & _ & _ & _ & _ & _).
    cbn [fb_addr fb_size fst snd] in FBAND, FTOP, F64. pose proof (ablk_lin _ _ FBAND) as (FIMG & Fb0 & _ & _). unfold AIMG_HI in FIMG.
    band_ind FBAND bF.
    pose proof (clocA_ablk _ _ _ GL _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OEB) ICL IFL) ltac:(lia)) as EBBAND. band_ind EBBAND bB.
    assert (SHE : (Z.shiftr Fb 3 + 2147450880 = Fb / 8 + 2147450880)%Z) by (rewrite Z.shiftr_div_pow2 by lia; reflexivity).
    split; [exact FP|]. split; [exact Gy|]. split; [exact OF|]. split; [exact MIy|]. split; [exact STy|].
    split. { eapply agrees_stk; [exact AGS| exact STG|]. intros a Ha. cbn [outside fst snd]. lia. }
    split. { eapply agrees_rw_cells; [exact AGS| exact FR|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. cbn [outside fst snd]. lia. }
    split. { eapply agrees_on_trans; [exact AG|]. eapply agrees_on_weaken; [exact AGy|]. intros a (K & N1 & N2 & _). split; [exact K|]. cbn [outside fst snd] in *. lia. }
    split. { destruct magic as [|mg0 [|mg1 [|mg2 [|mg3 [|? ?]]]]]; try discriminate MGL. cbn [map] in MGc |- *.
             eapply agrees_rw_cells; [exact AGS| exact MGc|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. cbn [outside fst snd]. lia. }
    eapply agrees_rw_cells; [exact AGS| exact SHC|]. intros a Ha. unfold ngc_shadow in Ha. cbn [cells_size csize Nat.add] in Ha. cbn [outside fst snd].
    rewrite SHE in Ha. Z.div_mod_to_equations. lia.
  Qed.
  End Sz1.
  Lemma ngc_inv_munch : ltac:(let t := eval cbv delta [ngc_inv_munch__stmt] in ngc_inv_munch__stmt in exact t).
  Proof using GL. intros ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic o m RNGx sx PB mm my wlo n. ltac2:(SecDiet.SzSec.closeP 'ngc_inv_munch__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
  (* [comment removed for export] *)
  Definition ngc_failM (i : option hptr) (qb qs : hptr) (msg : list Z) : Monad.M (PState H hptr) (@check_result hptr hptr) :=
    mbind (match i with Some qi => pfree HO qi | None => mret tt end)
          (fun _ => mbind (pfree HO qb) (fun _ => mbind (pfree HO qs) (fun _ => fo_ret FO _ FF_NG_CHECK_HEADER (CH_Err msg)))).

  (* [comment removed for export] *)
  Definition ngc_mcp_fail__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (CL FB : list cblk) (FL : list fblock) (trC : list Z)
      (lo MG FA EB ERR SPA Fb : Z) (f : hptr) (magic : list Z) (m : mem) (o : option hptr)
      (RNGx : footprint) (sx : PState H hptr) (mm : mem)
      (ra0 t0 t1 t2 a0 a3 a4 a5 a6 a7 r21 r22 r23 r24 t3 t4 t5 t6 : word)
      (j : list byte) (ccs fcs : list cell) (k0 k1 k2 : word) (e : list byte)
      (i : option hptr) (sg : pcap_ng_sf) (qs qb : hptr) (P B I nb : Z) (SRC n : Z) (msg : list Z),
    ngc_ctx TP ra sp tp s0 L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic m ->
    ngc_inv GIOA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo MG EB ERR SPA Fb magic o m RNGx sx ((qs, P, 680%Z) :: (qb, B, nb) :: IBLK i I sg) mm ->
    match i with Some _ => True | None => I = 0%Z end ->
    rw_cells asegs mm SPA (ngc_spill P EB Fb j) -> rw_cells asegs mm (SPA + 128) ccs -> cells_size ccs = 24%nat ->
    rw_cells asegs mm Fb ([C8 k0; C8 k1; C8 k2] ++ fcs ++ [C8 (Z_to_bv 64 (fflagA L FF_NG_CHECK_HEADER Fb))]) -> cells_size fcs = 32%nat ->
    rw_cells asegs mm ERR [C4 z64] -> rw_cells asegs mm EB [CB 256 e] ->
    rw_cells asegs mm (P + 24) [C8 (Z_to_bv 64 B)] -> rw_cells asegs mm (P + 672) [C8 (Z_to_bv 64 I)] ->
    bytes_at asegs mm SRC (map b8 msg ++ [Z_to_bv 8 0]) -> (Z.of_nat (length msg) + 1 = n)%Z -> (n <= 256)%Z -> In (SRC, n) client_globals ->
    Forall (fun z => 0 < z < 256)%Z msg ->
    implMG RNGx (ngc_failM i qb qs msg) sx
      (check_header_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CL FB lo MG EB ERR magic f m o)
      (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) a0 (Z_to_bv 64 SRC) (Z_to_bv 64 n) a3 a4 a5 a6 a7
               (Z_to_bv 64 Fb) (Z_to_bv 64 ERR) (Z_to_bv 64 (Z.shiftr ERR 3 + 2147450880)) r21 r22 r23 r24 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880))
               (Z_to_bv 64 2147450880) (Z_to_bv 64 Fb) t3 t4 t5 t6)
          F (Z_to_bv 64 0x8b5b8) fc None mm (seg_rom asegs)).
  Section Sz2.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic m o RNGx sx mm ra0 t0 t1 t2 a0 a3 a4 a5 a6 a7 r21 r22 r23 r24 t3 t4 t5 t6 j ccs fcs k0 k1 k2 e i sg qs qb P B I nb SRC n msg : ltac2:(SecDiet.SzSec.tyM 'ngc_mcp_fail__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma ngc_mcp_fail__body : ltac2:(SecDiet.SzSec.bodyP 'ngc_mcp_fail__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL FRET FREE FREENULL.
 intros CTX INV HI FRA FCUR Hccs FRC Hfcs HE HEB HPB HPI SRCB LN NB HG MOK.
    ngc_setup GL CTX INV.
    assert (ESPA : bv_unsigned (Z_to_bv 64 SPA) = SPA) by (apply unsigned_lit; lia).
    assert (HinP : In (qs, P, 680%Z) ((qs, P, 680%Z) :: (qb, B, nb) :: IBLK i I sg)) by (left; reflexivity).
    pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G ltac:(apply in_or_app; left; apply in_or_app; right; exact HinP)) as ((PBAND & _ & PTOP & P16) & P0 & _).
    cbn [cb_addr cb_size fst snd] in PBAND, PTOP, P16, P0. band_ind PBAND bP.
    destruct (clocA_apart_block _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OEB) (incl_refl _) IFL) HinP ltac:(lia) ltac:(cbn; lia)) as (kP & kPr & kP1 & kP2).
    cbn [cb_addr cb_size fst snd] in kP1, kP2.
    pose proof (gl_rt _ _ _ GL _ _ _ _ _ _ _ G) as (RT & _).
    pose proof (gia_global_mobjA _ _ _ GL _ _ _ _ _ _ _ _ _ G HG RIMG RISH) as OSRC.
    edestruct (ngc_cobj_now FO GIOA TP fflagA GL) as (_ & _ & OEB'); [exact CTX| exact INV|].
    pose proof (client_globals_lo (SRC, n) HG) as (GLO & GN & GHI). cbn [fst snd] in GLO, GN, GHI.
    assert (LM : Z.to_nat n = (length msg + 1)%nat) by lia.
    assert (LS : length (map b8 msg ++ [Z_to_bv 8 0]) = Z.to_nat n) by (rewrite length_app, length_map; cbn [length]; lia).
    pose proof (rw_cells_split_CB asegs _ _ [] _ _ [] [Z.to_nat n; (256 - Z.to_nat n)%nat] HEB ltac:(cbn; lia)) as HE'. clear HEB. cbn [mk_CB_cells app] in HE'.
    destruct (rw_cells_cut _ _ _ 1 HE') as [HE1 HE2]. clear HE'. cbn [firstn skipn cells_size csize Nat.add] in HE1, HE2.
    lazymatch type of HE2 with rw_cells _ _ ?A _ => replace A with (EB + n)%Z in HE2 by lia end.
    unfold ngc_spill in FRA.
    pose proof (munch_refl [(SPA - 2224, SPA); (EB, EB + n)]%Z mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    ienterG.
    zstep. zstep.
    remember (Z_to_bv 64 SPA) as spa eqn:Espa.
    assert (Hspa : bv_unsigned spa = SPA) by (rewrite Espa; apply unsigned_lit; lia).
    eapply evtF_cut.
    { eapply (asan_memcpy_specZ RNGx _ spa) with (lo := lo) (Dst := EB) (Src := SRC) (n := n) (src := map b8 msg ++ [Z_to_bv 8 0]) (junk := firstn (Z.to_nat n) e);
        [ reflexivity | reflexivity | reflexivity | exact MI | rewrite Hspa; exact ST | rewrite Hspa; lia | lia | exact RT | exact SRCB | exact LS | lia | exact HE1
        | lia
        | exact OSRC
        | eapply mobjA_sub; [apply aobjA_mobjA; [exact (proj2 OEB')| lia]| lia| lia| lia]
        | atop_facts; lia | atop_facts; lia | exact RIMG | rewrite Hspa; eapply rng_sub'; [exact RSPW| lia] ]. }
    cbv beta. intros ms' PO. destruct_exs PO. destruct PO as (-> & MU7 & WM7 & MI7 & ST7 & HD7 & SRC7).
    rewrite Hspa in *. clear Hspa. subst spa.
    replace (ret_pc (Z_to_bv 64 570816)) with (Z_to_bv 64 570816) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    lazymatch type of MU7 with munch _ _ ?mb =>
      assert (INV7 : ngc_inv GIOA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo MG EB ERR SPA Fb [mg0; mg1; mg2; mg3] o m RNGx sx ((qs, P, 680%Z) :: (qb, B, nb) :: IBLK i I sg) mb)
        by (eapply ngc_inv_munch; [exact CTX| exact INV| exact MU7| exact WM7| exact MI7| exact ST7| lia| lia]) end.
    lazymatch type of MU7 with munch _ _ ?mb =>
      assert (AGS : agrees_on (fun a => outside [(SPA - 2224, SPA); (EB, EB + n)]%Z a) mm mb) by (eapply agrees_on_of_munch; [exact MU7 | exact WM7 | intros a _ Ho; exact Ho]);
      assert (FRC7 : rw_cells asegs mb Fb ([C8 k0; C8 k1; C8 k2] ++ fcs ++ [C8 (Z_to_bv 64 (fflagA L FF_NG_CHECK_HEADER Fb))]))
        by (eapply agrees_rw_cells; [exact AGS| exact FRC|]; intros a Ha; rewrite !cells_size_app, Hfcs in Ha; cbn [cells_size csize Nat.add] in Ha; cbn [outside fst snd]; lia) end.
    clear FRC SRCB.
    lazymatch type of MU7 with munch _ ?ma ?mb => transport_after_call asegs ma mb MU7 WM7 end.
    lazymatch type of HE2 with rw_cells _ ?mb _ [CB _ ?jj] =>
      assert (HEB7 : rw_cells asegs mb EB [CB (length msg + 1) (map b8 msg ++ [Z_to_bv 8 0]); CB (255 - length msg) jj]) end.
    { replace (EB + n)%Z with (EB + Z.of_nat (cells_size [CB (Z.to_nat n) (map b8 msg ++ [Z_to_bv 8 0])]))%Z in HE2 by (cbn [cells_size csize Nat.add]; lia).
      pose proof (rw_cells_uncut _ _ _ _ _ HD7 HE2 ltac:(reflexivity)) as X. cbn [app] in X. rewrite LM in X |- *.
      replace (256 - (length msg + 1))%nat with (255 - length msg)%nat in X |- * by lia. exact X. }
    apply evtF_done. subst POSTQ. unfold ngc_failM.
    eapply (ngc_fail3 HO FO GIOA TP fflagA GL FRET FREE FREENULL) with (j := j) (ccs := ccs) (fcs := fcs) (k0 := k0) (k1 := k1) (k2 := k2);
      [ exact CTX | exact INV7 | exact HI | exact FRA | exact FCUR | exact Hccs | exact FRC7 | exact Hfcs | exact HE | exact HEB7 | lia | exact MOK | exact HPB | exact HPI ].
  Qed.
  End Sz2.
  Lemma ngc_mcp_fail : ltac:(let t := eval cbv delta [ngc_mcp_fail__stmt] in ngc_mcp_fail__stmt in exact t).
  Proof using GL FRET FREE FREENULL. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic m o RNGx sx mm ra0 t0 t1 t2 a0 a3 a4 a5 a6 a7 r21 r22 r23 r24 t3 t4 t5 t6 j ccs fcs k0 k1 k2 e i sg qs qb P B I nb SRC n msg. ltac2:(SecDiet.SzSec.closeP 'ngc_mcp_fail__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
  (* [comment removed for export] *)
  Definition ngc_snp_fail__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (CL FB : list cblk) (FL : list fblock) (trC : list Z)
      (lo MG FA EB ERR SPA Fb : Z) (f : hptr) (magic : list Z) (m : mem) (o : option hptr)
      (RNGx : footprint) (sx : PState H hptr) (mm : mem)
      (t0 t1 t2 a3 a4 a5 a6 a7 r21 r22 r23 r24 t3 t4 t5 t6 : word)
      (j : list byte) (ccs fcs : list cell) (k0 k1 k2 : word) (e : list byte)
      (i : option hptr) (sg : pcap_ng_sf) (qs qb : hptr) (P B I nb : Z) (RA FMTA : Z) (fs : string) (args : list farg) (msg : list Z),
    ngc_ctx TP ra sp tp s0 L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic m ->
    ngc_inv GIOA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo MG EB ERR SPA Fb magic o m RNGx sx ((qs, P, 680%Z) :: (qb, B, nb) :: IBLK i I sg) mm ->
    match i with Some _ => True | None => I = 0%Z end ->
    rw_cells asegs mm SPA (ngc_spill P EB Fb j) -> rw_cells asegs mm (SPA + 128) ccs -> cells_size ccs = 24%nat ->
    rw_cells asegs mm Fb ([C8 k0; C8 k1; C8 k2] ++ fcs ++ [C8 (Z_to_bv 64 (fflagA L FF_NG_CHECK_HEADER Fb))]) -> cells_size fcs = 32%nat ->
    rw_cells asegs mm ERR [C4 z64] -> rw_cells asegs mm EB [CB 256 e] ->
    rw_cells asegs mm (P + 24) [C8 (Z_to_bv 64 B)] -> rw_cells asegs mm (P + 672) [C8 (Z_to_bv 64 I)] ->
    (RA = 0x8b598)%Z ->   (* [comment removed for export] *)
    fmt_at mm FMTA fs -> fmt_ok fs args = true -> (length args <= 3)%nat ->
    Forall2 (farg_word true L RNGx (NGFR Fb :: FL) (CL ++ (qs, P, 680%Z) :: (qb, B, nb) :: IBLK i I sg) SPA EB 256 mm) args (firstn (length args) [a3; a4; a5]) ->
    items_okb (fmt fs) = true -> Forall arg_ok args -> Fmt.snprintf 256 fs args = msg ->
    implMG RNGx (ngc_failM i qb qs msg) sx
      (check_header_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CL FB lo MG EB ERR magic f m o)
      (MS (mkR (Z_to_bv 64 RA) (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) (Z_to_bv 64 EB) (Z_to_bv 64 256) (Z_to_bv 64 FMTA) a3 a4 a5 a6 a7
               (Z_to_bv 64 Fb) (Z_to_bv 64 ERR) (Z_to_bv 64 (Z.shiftr ERR 3 + 2147450880)) r21 r22 r23 r24 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880))
               (Z_to_bv 64 2147450880) (Z_to_bv 64 Fb) t3 t4 t5 t6)
          F (Z_to_bv 64 SNPRINTF_ENTRY) fc None mm (seg_rom asegs)).
  Section Sz3.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic m o RNGx sx mm t0 t1 t2 a3 a4 a5 a6 a7 r21 r22 r23 r24 t3 t4 t5 t6 j ccs fcs k0 k1 k2 e i sg qs qb P B I nb RA FMTA fs args msg : ltac2:(SecDiet.SzSec.tyM 'ngc_snp_fail__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma ngc_snp_fail__body : ltac2:(SecDiet.SzSec.bodyP 'ngc_snp_fail__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL FRET FREE FREENULL SNPRINTF.
 intros CTX INV HI FRA FCUR Hccs FRC Hfcs HE HEB HPB HPI HRA FAT FOK ALEN FW FIT AOK EMSG.
    ngc_setup GL CTX INV.
    assert (ESPA : bv_unsigned (Z_to_bv 64 SPA) = SPA) by (apply unsigned_lit; lia).
    assert (HinP : In (qs, P, 680%Z) ((qs, P, 680%Z) :: (qb, B, nb) :: IBLK i I sg)) by (left; reflexivity).
    pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G ltac:(apply in_or_app; left; apply in_or_app; right; exact HinP)) as ((PBAND & _ & PTOP & P16) & P0 & _).
    cbn [cb_addr cb_size fst snd] in PBAND, PTOP, P16, P0. band_ind PBAND bP.
    destruct (clocA_apart_block _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OEB) (incl_refl _) IFL) HinP ltac:(lia) ltac:(cbn; lia)) as (kP & kPr & kP1 & kP2).
    cbn [cb_addr cb_size fst snd] in kP1, kP2.
    edestruct (ngc_cobj_now FO GIOA TP fflagA GL) as (_ & _ & OEB'); [exact CTX| exact INV|].
    assert (OEBx : cobjA RNGx mm (NGFR Fb :: FL) (CL ++ (qs, P, 680%Z) :: (qb, B, nb) :: IBLK i I sg) EB 256)
      by (split; [exact (clocA_incl _ _ _ _ _ _ (proj1 OEB') ICL IFL)| exact (proj2 OEB')]).
    unfold ngc_spill in FRA.
    pose proof (munch_refl [(SPA - 16384, SPA); (EB, EB + 256)]%Z mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    ienterG.
    remember (Z_to_bv 64 SPA) as spa eqn:Espa.
    assert (Hspa : bv_unsigned spa = SPA) by (rewrite Espa; apply unsigned_lit; lia).
    eapply evtF_cut.
    { eapply SNPRINTF with (L := L) (s := sx) (CL := (CL ++ (qs, P, 680%Z) :: (qb, B, nb) :: IBLK i I sg)%list) (FB := FB) (FL := NGFR Fb :: FL) (lo := lo) (DST := EB) (n := 256%Z) (FMTA := FMTA)
                           (fs := fs) (args := args) (junk := e);
        [ rewrite Espa; eapply (ngc_spo GIOA TP); [exact CTX| exact FP| exact G| exact ST| exact MI| unfold STDIO_STACK, PCAP_L2_STACK; lia]
        | reflexivity | reflexivity | reflexivity | lia | exact FAT | exact FOK | exact ALEN | rewrite Hspa; exact FW | exact HEB | exact OEBx ]. }
    cbv beta. intros ms' PO. destruct PO as (av6 & m6 & junk6 & E & MU6 & WM6 & MI6 & ST6 & -> & HEB6).
    unfold hpost_regs in E. destruct_exs E. subst ms'. rewrite Hspa in *. clear Hspa. subst spa.
    unfold STDIO_STACK in MU6.
    assert (INV6 : ngc_inv GIOA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo MG EB ERR SPA Fb [mg0; mg1; mg2; mg3] o m RNGx sx ((qs, P, 680%Z) :: (qb, B, nb) :: IBLK i I sg) m6)
      by (eapply ngc_inv_munch with (n := 256%Z); [exact CTX| exact INV| exact MU6| exact WM6| exact MI6| exact ST6| lia| lia]).
    assert (AGS : agrees_on (fun a => outside [(SPA - 16384, SPA); (EB, EB + 256)]%Z a) mm m6) by (eapply agrees_on_of_munch; [exact MU6 | exact WM6 | intros a _ Ho; exact Ho]).
    assert (FRC6 : rw_cells asegs m6 Fb ([C8 k0; C8 k1; C8 k2] ++ fcs ++ [C8 (Z_to_bv 64 (fflagA L FF_NG_CHECK_HEADER Fb))]))
      by (eapply agrees_rw_cells; [exact AGS| exact FRC|]; intros a Ha; rewrite !cells_size_app, Hfcs in Ha; cbn [cells_size csize Nat.add] in Ha; cbn [outside fst snd]; lia).
    clear FRC HEB.
    transport_after_call asegs mm m6 MU6 WM6.
    pose proof (snprintf_length_le 256 fs args ltac:(lia)) as LS. rewrite EMSG in LS, HEB6.
    change (Z.to_nat 256) with 256%nat in HEB6.
    replace (256 - length msg - 1)%nat with (255 - length msg)%nat in HEB6 by lia.
    assert (MOK : Forall (fun z => 0 < z < 256)%Z msg) by (rewrite <- EMSG; apply snprintf_ok; [exact FIT| exact AOK]).
    subst RA.
    replace (ret_pc (Z_to_bv 64 0x8b598)) with (Z_to_bv 64 0x8b598) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    all: zstep.
    all: apply evtF_done; subst POSTQ; unfold ngc_failM;
      eapply (ngc_fail3 HO FO GIOA TP fflagA GL FRET FREE FREENULL) with (j := j) (ccs := ccs) (fcs := fcs) (k0 := k0) (k1 := k1) (k2 := k2);
      [ exact CTX | exact INV6 | exact HI | exact FRA | exact FCUR | exact Hccs | exact FRC6 | exact Hfcs | exact HE | exact HEB6 | lia | exact MOK | exact HPB | exact HPI ].
  Qed.
  End Sz3.
  Lemma ngc_snp_fail : ltac:(let t := eval cbv delta [ngc_snp_fail__stmt] in ngc_snp_fail__stmt in exact t).
  Proof using GL FRET FREE FREENULL SNPRINTF. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic m o RNGx sx mm t0 t1 t2 a3 a4 a5 a6 a7 r21 r22 r23 r24 t3 t4 t5 t6 j ccs fcs k0 k1 k2 e i sg qs qb P B I nb RA FMTA fs args msg. ltac2:(SecDiet.SzSec.closeP 'ngc_snp_fail__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition ngc_gfbd_fail__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (CL FB : list cblk) (FL : list fblock) (trC : list Z)
      (lo MG FA EB ERR SPA Fb : Z) (f : hptr) (magic : list Z) (m : mem) (o : option hptr)
      (RNGx : footprint) (sx : PState H hptr) (mm : mem)
      (t0 t1 t2 a3 a4 a5 a6 a7 r21 r22 r23 r24 t3 t4 t5 t6 : word)
      (j : list byte) (fcs : list cell) (k0 k1 k2 : word) (e : list byte)
      (i : option hptr) (sg : pcap_ng_sf) (qs qb : hptr) (P B I nb : Z) (D R BT : Z) (cpad : list byte),
    ngc_ctx TP ra sp tp s0 L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic m ->
    ngc_inv GIOA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo MG EB ERR SPA Fb magic o m RNGx sx ((qs, P, 680%Z) :: (qb, B, nb) :: IBLK i I sg) mm ->
    match i with Some _ => True | None => I = 0%Z end ->
    rw_cells asegs mm SPA (ngc_spill P EB Fb j) ->
    rw_cells asegs mm (SPA + 128) [C8 (Z_to_bv 64 D); C8 (Z_to_bv 64 R); C4 (Z_to_bv 64 BT); CB 4 cpad] ->
    rw_cells asegs mm Fb ([C8 k0; C8 k1; C8 k2] ++ fcs ++ [C8 (Z_to_bv 64 (fflagA L FF_NG_CHECK_HEADER Fb))]) -> cells_size fcs = 32%nat ->
    rw_cells asegs mm ERR [C4 z64] -> rw_cells asegs mm EB [CB 256 e] ->
    rw_cells asegs mm (P + 24) [C8 (Z_to_bv 64 B)] -> rw_cells asegs mm (P + 672) [C8 (Z_to_bv 64 I)] ->
    (0 <= R < 8)%Z -> (0 <= BT < 2^31)%Z ->
    implMG RNGx (ngc_failM i qb qs (Msg.block_too_short BT)) sx
      (check_header_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CL FB lo MG EB ERR magic f m o)
      (MS (mkR (Z_to_bv 64 0x8b308) (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) (Z_to_bv 64 (SPA + 128)) (Z_to_bv 64 8) (Z_to_bv 64 EB) a3 a4 a5 a6 a7
               (Z_to_bv 64 Fb) (Z_to_bv 64 ERR) (Z_to_bv 64 (Z.shiftr ERR 3 + 2147450880)) r21 r22 r23 r24 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880))
               (Z_to_bv 64 2147450880) (Z_to_bv 64 Fb) t3 t4 t5 t6)
          F (Z_to_bv 64 GFBD_ENTRY) fc None mm (seg_rom asegs)).
  Section Sz4.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic m o RNGx sx mm t0 t1 t2 a3 a4 a5 a6 a7 r21 r22 r23 r24 t3 t4 t5 t6 j fcs k0 k1 k2 e i sg qs qb P B I nb D R BT cpad : ltac2:(SecDiet.SzSec.tyM 'ngc_gfbd_fail__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma ngc_gfbd_fail__body : ltac2:(SecDiet.SzSec.bodyP 'ngc_gfbd_fail__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL FRET FREE FREENULL SNPRINTF.
 intros CTX INV HI FRA FCUR FRC Hfcs HE HEB HPB HPI HR HBT.
    ngc_setup GL CTX INV.
    assert (ESPA : bv_unsigned (Z_to_bv 64 SPA) = SPA) by (apply unsigned_lit; lia).
    atop_facts.
    assert (HinP : In (qs, P, 680%Z) ((qs, P, 680%Z) :: (qb, B, nb) :: IBLK i I sg)) by (left; reflexivity).
    pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G ltac:(apply in_or_app; left; apply in_or_app; right; exact HinP)) as ((PBAND & _ & PTOP & P16) & P0 & _).
    cbn [cb_addr cb_size fst snd] in PBAND, PTOP, P16, P0. band_ind PBAND bP.
    destruct (clocA_apart_block _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OEB) (incl_refl _) IFL) HinP ltac:(lia) ltac:(cbn; lia)) as (kP & kPr & kP1 & kP2).
    cbn [cb_addr cb_size fst snd] in kP1, kP2.
    (* [comment removed for export] *)
    pose proof (gia_stack_sobjA _ _ _ GL _ _ _ _ _ _ _ lo SPA (SPA + 128) 24 G ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(exact RSTK)) as (_ & _ & CUNP & CRNG & CRSH).
    replace ((SPA + 128) mod 8)%Z with 0%Z in CRSH by (Z.div_mod_to_equations; lia).
    rewrite Z.sub_0_r, Z.add_0_r in CRSH.
    pose proof (gl_rt _ _ _ GL _ _ _ _ _ _ _ G) as (RT & _).
    pose proof (munch_refl [(SPA - 16400, SPA); (EB, EB + 256)]%Z mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    ienterG.
    remember (Z_to_bv 64 SPA) as spa eqn:Espa.
    assert (Hspa : bv_unsigned spa = SPA) by (rewrite Espa; apply unsigned_lit; lia).
    (* [comment removed for export] *)
    eapply evtF_cut.
    { eapply (gfbd_short_pre (Z_to_bv 64 0x8b308) spa gp tp sp spa (Z_to_bv 64 Fb) (Z_to_bv 64 ERR) (Z_to_bv 64 (Z.shiftr ERR 3 + 2147450880)) r21 r22 r23 r24
                (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 2147450880) (Z_to_bv 64 Fb) F fc RNGx lo (SPA + 128)%Z) with (D := D) (R := R) (BT := BT) (N := 8%Z) (cpad := cpad);
        rewrite ?Hspa;
        first [ exact MI | exact ST | exact RT | exact FCUR | exact CUNP | exact CRNG | exact CRSH | exact RSPW
              | exact RIMG | (eapply rng_sub'; [exact RSPW | lia]) | lia | (Z.div_mod_to_equations; lia)
              | match goal with |- ?g => idtac "GF side:" g end ]. }
    cbv beta. intros ms1 PO. destruct PO as (a4' & a5' & a6' & jk & m1 & -> & MU1 & WM1 & MI1 & ST1 & FR1 & FCUR1 & CUNP1).
    rewrite Hspa in *.
    (* [comment removed for export] *)
    assert (MU1w : munch [(SPA - 16, SPA); (EB, EB + 1)]%Z mm m1).
    { eapply munch_weaken; [| exact MU1]. unfold sub_fp. cbn [outside]. intros x (O1 & _ & _). split; [exact O1 | exact Logic.I]. }
    assert (STS : stk asegs m1 lo SPA).
    { pose proof (stk_release asegs m1 lo (SPA + -16) _ ST1 FR1 ltac:(lia)) as X. cbn [cells_size csize Nat.add] in X.
      replace (SPA + -16 + Z.of_nat 16)%Z with SPA in X by lia. exact X. }
    assert (INV1 : ngc_inv GIOA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo MG EB ERR SPA Fb [mg0; mg1; mg2; mg3] o m RNGx sx ((qs, P, 680%Z) :: (qb, B, nb) :: IBLK i I sg) m1)
      by (eapply ngc_inv_munch with (n := 1%Z); [exact CTX| exact INV| exact MU1w| exact WM1| exact MI1| exact STS| lia| lia]).
    pose proof INV1 as (_ & G1 & _).
    assert (AGS1 : agrees_on (fun a => outside [(SPA - 16, SPA)]%Z a) mm m1) by (eapply agrees_on_of_munch; [exact MU1 | exact WM1 | intros a _ Ho; exact Ho]).
    assert (HEB1 : rw_cells asegs m1 EB [CB 256 e]) by (eapply agrees_rw_cells; [exact AGS1| exact HEB|]; intros a Ha; cbn [cells_size csize Nat.add] in Ha; cbn [outside fst snd]; lia).
    edestruct (ngc_cobj_now FO GIOA TP fflagA GL) as (_ & _ & OEB'); [exact CTX| exact INV1|].
    assert (OEBx : cobjA RNGx m1 (NGFR Fb :: FL) (CL ++ (qs, P, 680%Z) :: (qb, B, nb) :: IBLK i I sg) EB 256)
      by (split; [exact (clocA_incl _ _ _ _ _ _ (proj1 OEB') ICL IFL)| exact (proj2 OEB')]).
    assert (MSG : fmt_at m1 GFBD_FMT "block of type %u in pcapng dump file is too short"%string)
      by (unfold GFBD_FMT; split; [exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image asegs m1 0x22520 (map (fun c => Z_to_bv 8 (Z.of_nat (Ascii.nat_of_ascii c))) (String.list_ascii_of_string "block of type %u in pcapng dump file is too short"%string) ++ [Z_to_bv 8 0])
                                 MI1 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)))|];
            split; [lia|]; split; [cbn; lia|]; unfold client_globals; repeat (first [left; reflexivity | right])).
    rewrite (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit.sx32_small BT) by lia.
    (* [comment removed for export] *)
    remember (Z_to_bv 64 (SPA + -16)) as spb eqn:Espb.
    assert (Hspb : bv_unsigned spb = (SPA + -16)%Z) by (rewrite Espb; apply unsigned_lit; lia).
    assert (SPO : std_pre_o GIOA L RNGx spb tp sx (CL ++ (qs, P, 680%Z) :: (qb, B, nb) :: IBLK i I sg) FB (NGFR Fb :: FL) lo STDIO_STACK m1).
    { unfold std_pre_o, STDIO_STACK. rewrite Hspb.
      split; [exact G1|]. split; [exact ST1|]. split; [exact LO|]. split; [lia|]. split; [lia|]. split; [exact MI1|]. split; [exact TPE|].
      split; [Z.div_mod_to_equations; lia|].
      split; [exact RSTK|]. split; [exact RIMG|]. split; [exact RISH | exact RTLS]. }
    eapply evtF_cut.
    { eapply SNPRINTF with (L := L) (s := sx) (CL := (CL ++ (qs, P, 680%Z) :: (qb, B, nb) :: IBLK i I sg)%list) (FB := FB) (FL := NGFR Fb :: FL) (lo := lo) (DST := EB) (n := 256%Z) (FMTA := GFBD_FMT)
                           (fs := "block of type %u in pcapng dump file is too short"%string) (args := [AInt BT]) (junk := e);
        [ exact SPO | reflexivity | reflexivity | reflexivity | lia | exact MSG | reflexivity | cbn; lia
        | cbn [length firstn]; constructor; [reflexivity| constructor] | exact HEB1 | exact OEBx ]. }
    cbv beta. intros ms' PO. destruct PO as (av6 & m6 & junk6 & E & MU6 & WM6 & MI6 & ST6 & EAV & HEB6).
    unfold hpost_regs in E. destruct_exs E. subst ms'. clear EAV. rewrite Hspb in MU6, ST6.
    unfold STDIO_STACK in MU6.
    assert (AGS6 : agrees_on (fun a => outside [(SPA + -16 - 16384, SPA + -16); (EB, EB + 256)]%Z a) m1 m6) by (eapply agrees_on_of_munch; [exact MU6 | exact WM6 | intros a _ Ho; exact Ho]).
    assert (FR6 : rw_cells asegs m6 (SPA + -16) [CB 8 jk; C8 (Z_to_bv 64 0x8b308)])
      by (eapply agrees_rw_cells; [exact AGS6| exact FR1|]; intros a Ha; cbn [cells_size csize Nat.add] in Ha; cbn [outside fst snd]; lia).
    (* [comment removed for export] *)
    assert (MUT : munch [(SPA - 16400, SPA); (EB, EB + 256)]%Z mm m6).
    { apply (munch_trans _ mm m1 m6); [eapply munch_weaken; [| exact MU1] | eapply munch_weaken; [| exact MU6]]; unfold sub_fp; cbn [outside]; intros; lia. }
    assert (WMT : wmono asegs mm m6) by (eapply wmono_trans; [exact WM1 | exact WM6]).
    unfold GFBD_SNPRINTF_RA.
    replace (ret_pc (Z_to_bv 64 0x8c244)) with (Z_to_bv 64 0x8c244) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    (* [comment removed for export] *)
    rewrite Espb. rewrite <- Hspa at 1.
    eapply evtF_cut.
    { eapply (gfbd_short_post (Z_to_bv 64 0x8b308) spa) with (lo := lo) (jk := jk); rewrite ?Hspa;
        first [ exact MI6 | exact ST6 | exact FR6 | exact RSTK | exact RIMG | (eapply rng_sub'; [exact RSPW | lia]) | lia | (Z.div_mod_to_equations; lia)
              | match goal with |- ?g => idtac "GP side:" g end ]. }
    cbv beta. intros ms7 (a1' & -> & ST7). rewrite Hspa in *. clear Hspa Hspb. subst spa spb.
    replace (ret_pc (Z_to_bv 64 0x8b308)) with (Z_to_bv 64 0x8b308) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    (* [comment removed for export] *)
    zstep. if_true.
    assert (INV6 : ngc_inv GIOA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo MG EB ERR SPA Fb [mg0; mg1; mg2; mg3] o m RNGx sx ((qs, P, 680%Z) :: (qb, B, nb) :: IBLK i I sg) m6)
      by (eapply ngc_inv_munch with (n := 256%Z); [exact CTX| exact INV| exact MUT| exact WMT| exact MI6| exact ST7| lia| lia]).
    assert (AGS : agrees_on (fun a => outside [(SPA - 16400, SPA); (EB, EB + 256)]%Z a) mm m6) by (eapply agrees_on_of_munch; [exact MUT | exact WMT | intros a _ Ho; exact Ho]).
    assert (FRC6 : rw_cells asegs m6 Fb ([C8 k0; C8 k1; C8 k2] ++ fcs ++ [C8 (Z_to_bv 64 (fflagA L FF_NG_CHECK_HEADER Fb))]))
      by (eapply agrees_rw_cells; [exact AGS| exact FRC|]; intros a Ha; rewrite !cells_size_app, Hfcs in Ha; cbn [cells_size csize Nat.add] in Ha; cbn [outside fst snd]; lia).
    clear FRC HEB.
    transport_after_call asegs mm m6 MUT WMT.
    pose proof (snprintf_length_le 256 "block of type %u in pcapng dump file is too short"%string [AInt BT] ltac:(lia)) as LS.
    assert (EMSG : Fmt.snprintf 256 "block of type %u in pcapng dump file is too short"%string [AInt BT] = Msg.block_too_short BT)
      by (unfold Msg.block_too_short, PCAP_ERRBUF_SIZE; reflexivity).
    rewrite EMSG in LS, HEB6.
    change (Z.to_nat 256) with 256%nat in HEB6.
    replace (256 - length (Msg.block_too_short BT) - 1)%nat with (255 - length (Msg.block_too_short BT))%nat in HEB6 by lia.
    assert (MOK : Forall (fun z => 0 < z < 256)%Z (Msg.block_too_short BT)) by (rewrite <- EMSG; apply snprintf_ok; [vm_compute; reflexivity | repeat constructor]).
    apply evtF_done; subst POSTQ; unfold ngc_failM;
      eapply (ngc_fail3 HO FO GIOA TP fflagA GL FRET FREE FREENULL) with (j := j) (ccs := [C8 (Z_to_bv 64 D); C8 (Z_to_bv 64 R); C4 (Z_to_bv 64 BT); CB 4 cpad]) (fcs := fcs) (k0 := k0) (k1 := k1) (k2 := k2);
      [ exact CTX | exact INV6 | exact HI | exact FRA | exact FCUR | reflexivity | exact FRC6 | exact Hfcs | exact HE | exact HEB6 | lia | exact MOK | exact HPB | exact HPI ].
  Qed.
  End Sz4.
  Lemma ngc_gfbd_fail : ltac:(let t := eval cbv delta [ngc_gfbd_fail__stmt] in ngc_gfbd_fail__stmt in exact t).
  Proof using GL FRET FREE FREENULL SNPRINTF. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic m o RNGx sx mm t0 t1 t2 a3 a4 a5 a6 a7 r21 r22 r23 r24 t3 t4 t5 t6 j fcs k0 k1 k2 e i sg qs qb P B I nb D R BT cpad. ltac2:(SecDiet.SzSec.closeP 'ngc_gfbd_fail__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End NgcMsg.
End CANSEC1.
End TwB.
End F_ngchk_msgA.

(* [comment removed for export] *)
Module PP_kitA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes Image ZBridge ITree Nodes Decode SysStep RegsEquiv.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim PcapPrelim PcapTypes PcapPure.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow StepF StrwF SysStepF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg ABase.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Import Pcap_iface_ppA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma zbytes_length : forall d, length (zbytes d) = length d.
Proof. intros. unfold zbytes. apply length_map. Qed.

Lemma Forall_range_firstn : forall (P : Z -> Prop) n (d : list Z), Forall P d -> Forall P (firstn n d).
Proof. intros P n d H. rewrite <- (firstn_skipn n d) in H. apply Forall_app in H as [H _]. exact H. Qed.
Lemma Forall_range_skipn : forall (P : Z -> Prop) n (d : list Z), Forall P d -> Forall P (skipn n d).
Proof. intros P n d H. rewrite <- (firstn_skipn n d) in H. apply Forall_app in H as [_ H]. exact H. Qed.
Lemma Forall_rev : forall (P : Z -> Prop) (d : list Z), Forall P d -> Forall P (rev d).
Proof. intros P d H. apply Forall_forall. intros x Hx. apply in_rev in Hx. exact (proj1 (Forall_forall _ _) H x Hx). Qed.

Lemma zslice_length : forall off n (d : list Z), 0 <= off -> 0 <= n -> off + n <= Z.of_nat (length d) ->
  length (zslice off n d) = Z.to_nat n.
Proof. intros. unfold zslice, zfirstn, zskipn. rewrite length_firstn, length_skipn. lia. Qed.

Lemma buf_write_at_length : forall off l (d : list Z), 0 <= off -> off + Z.of_nat (length l) <= Z.of_nat (length d) ->
  length (buf_write_at off l d) = length d.
Proof.
  intros. unfold buf_write_at, zfirstn, zskipn, zlength. rewrite !length_app, length_firstn, length_skipn. lia.
Qed.

Lemma buf_write_at_range : forall off l (d : list Z),
  Forall (fun x => 0 <= x < 256) d -> Forall (fun x => 0 <= x < 256) l -> Forall (fun x => 0 <= x < 256) (buf_write_at off l d).
Proof.
  intros. unfold buf_write_at, zfirstn, zskipn. apply Forall_app. split; [apply Forall_range_firstn; assumption|].
  apply Forall_app. split; [assumption| apply Forall_range_skipn; assumption].
Qed.

Lemma swap_field_length : forall k off (d : list Z), 0 <= off -> 0 <= k -> off + k <= Z.of_nat (length d) ->
  length (swap_field k off d) = length d.
Proof.
  intros. unfold swap_field. apply buf_write_at_length; [lia|]. rewrite length_rev, zslice_length by lia. lia.
Qed.

Lemma swap_field_range : forall k off (d : list Z),
  Forall (fun x => 0 <= x < 256) d -> Forall (fun x => 0 <= x < 256) (swap_field k off d).
Proof.
  intros. unfold swap_field. apply buf_write_at_range; [assumption|]. apply Forall_rev. unfold zslice, zfirstn, zskipn.
  apply Forall_range_firstn. apply Forall_range_skipn. assumption.
Qed.

(* [comment removed for export] *)
Lemma zslice_4 : forall off (d : list Z), 0 <= off -> off + 4 <= Z.of_nat (length d) ->
  exists x0 x1 x2 x3, zslice off 4 d = [x0; x1; x2; x3].
Proof.
  intros off d Ho Hl. pose proof (zslice_length off 4 d Ho ltac:(lia) Hl) as L.
  destruct (zslice off 4 d) as [|x0 [|x1 [|x2 [|x3 [|]]]]]; cbn in L; try lia. repeat eexists.
Qed.
Lemma zslice_2 : forall off (d : list Z), 0 <= off -> off + 2 <= Z.of_nat (length d) ->
  exists x0 x1, zslice off 2 d = [x0; x1].
Proof.
  intros off d Ho Hl. pose proof (zslice_length off 2 d Ho ltac:(lia) Hl) as L.
  destruct (zslice off 2 d) as [|x0 [|x1 [|]]]; cbn in L; try lia. repeat eexists.
Qed.

Lemma zslice_range : forall off n (d : list Z), Forall (fun x => 0 <= x < 256) d -> Forall (fun x => 0 <= x < 256) (zslice off n d).
Proof. intros. unfold zslice, zfirstn, zskipn. apply Forall_range_firstn. apply Forall_range_skipn. assumption. Qed.

(* [comment removed for export] *)
Lemma znth_slice : forall (d : list Z) off n j, 0 <= off -> 0 <= j < n -> off + n <= Z.of_nat (length d) ->
  nth_error (zslice off n d) (Z.to_nat j) = Some (znth d (off + j)).
Proof.
  intros d off n j Ho Hj Hl. unfold zslice, zfirstn, zskipn.
  rewrite (nth_error_nth' _ 0).
  2:{ rewrite length_firstn, length_skipn. lia. }
  f_equal. rewrite nth_firstn. replace (Z.to_nat j <? Z.to_nat n)%nat with true by (symmetry; apply Nat.ltb_lt; lia). rewrite nth_skipn. unfold znth.
  replace (off + j <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
  f_equal. lia.
Qed.

Lemma get_u8_of_slice4 : forall off d x0 x1 x2 x3, 0 <= off -> off + 4 <= Z.of_nat (length d) ->
  zslice off 4 d = [x0; x1; x2; x3] ->
  get_u8 d off = x0 /\ get_u8 d (off + 1) = x1 /\ get_u8 d (off + 2) = x2 /\ get_u8 d (off + 3) = x3.
Proof.
  intros off d x0 x1 x2 x3 Ho Hl E. unfold get_u8.
  pose proof (znth_slice d off 4 0 Ho ltac:(lia) Hl) as E0. change (Z.to_nat 0) with 0%nat in E0.
  pose proof (znth_slice d off 4 1 Ho ltac:(lia) Hl) as E1. change (Z.to_nat 1) with 1%nat in E1.
  pose proof (znth_slice d off 4 2 Ho ltac:(lia) Hl) as E2. change (Z.to_nat 2) with 2%nat in E2.
  pose proof (znth_slice d off 4 3 Ho ltac:(lia) Hl) as E3. change (Z.to_nat 3) with 3%nat in E3.
  rewrite E in E0, E1, E2, E3. cbn [nth_error] in E0, E1, E2, E3. rewrite Z.add_0_r in E0.
  injection E0 as <-. injection E1 as <-. injection E2 as <-. injection E3 as <-. repeat split; reflexivity.
Qed.
Lemma get_u8_of_slice2 : forall off d x0 x1, 0 <= off -> off + 2 <= Z.of_nat (length d) ->
  zslice off 2 d = [x0; x1] -> get_u8 d off = x0 /\ get_u8 d (off + 1) = x1.
Proof.
  intros off d x0 x1 Ho Hl E. unfold get_u8.
  pose proof (znth_slice d off 2 0 Ho ltac:(lia) Hl) as E0. change (Z.to_nat 0) with 0%nat in E0.
  pose proof (znth_slice d off 2 1 Ho ltac:(lia) Hl) as E1. change (Z.to_nat 1) with 1%nat in E1.
  rewrite E in E0, E1. cbn [nth_error] in E0, E1. rewrite Z.add_0_r in E0.
  injection E0 as <-. injection E1 as <-. split; reflexivity.
Qed.
Lemma get_u8_single : forall off d, 0 <= off -> off + 1 <= Z.of_nat (length d) -> zslice off 1 d = [get_u8 d off].
Proof.
  intros off d Ho Hl. pose proof (zslice_length off 1 d Ho ltac:(lia) Hl) as L.
  pose proof (znth_slice d off 1 0 Ho ltac:(lia) Hl) as E0. change (Z.to_nat 0) with 0%nat in E0.
  destruct (zslice off 1 d) as [|y [|]]; cbn in L; try lia. cbn [nth_error] in E0. rewrite Z.add_0_r in E0. unfold get_u8. injection E0 as ->. reflexivity.
Qed.

Lemma get_le32_of_slice : forall off d x0 x1 x2 x3, zslice off 4 d = [x0; x1; x2; x3] ->
  get_le32 d off = x0 + 256 * x1 + 65536 * x2 + 16777216 * x3.
Proof. intros off d x0 x1 x2 x3 E. unfold get_le32. rewrite E. cbn. lia. Qed.
Lemma get_le16_of_slice : forall off d x0 x1, zslice off 2 d = [x0; x1] -> get_le16 d off = x0 + 256 * x1.
Proof. intros off d x0 x1 E. unfold get_le16. rewrite E. cbn. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section ZA.
  Notation segs := asegs.

  #[using="Type"] Lemma zarr_bound : forall m A d, zarr m A d -> 0 <= A /\ A + Z.of_nat (length d) <= 2^64.
  Proof. intros m A d (B & _ & _). apply bytes_at_bound in B. rewrite zbytes_length in B. exact B. Qed.

  #[using="Type"] Lemma zarr_read_raw : forall m A d off n, zarr m A d -> 0 <= off -> 0 <= n -> off + n <= Z.of_nat (length d) ->
    ov_read_bytes segs m (wa (A + off)) (Z.to_nat n) = Some (zbytes (zslice off n d)).
  Proof.
    intros m A d off n (B & _ & _) Ho Hn Hl.
    rewrite (bytes_at_read segs m A (zbytes d) off (Z.to_nat n) B) by (rewrite ?zbytes_length; lia).
    unfold zslice, zfirstn, zskipn, zbytes. rewrite skipn_map, firstn_map. reflexivity.
  Qed.

  #[using="Type"] Lemma zb_eq : forall a b, a mod 256 = b mod 256 -> Z_to_bv 8 a = Z_to_bv 8 b.
  Proof. intros a b E. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. exact E. Qed.

  #[using="Type"] Lemma le4_zbytes : forall x0 x1 x2 x3, 0 <= x0 < 256 -> 0 <= x1 < 256 -> 0 <= x2 < 256 -> 0 <= x3 < 256 ->
    le4 (Z_to_bv 64 (x0 + 256 * x1 + 65536 * x2 + 16777216 * x3)) = zbytes [x0; x1; x2; x3].
  Proof.
    intros. unfold le4. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64). rewrite Z.mod_small by lia.
    cbn [Z_to_le_bytes zbytes map]. rewrite !Z.shiftr_div_pow2 by lia. change (2^8) with 256.
    f_equal; [apply zb_eq; Z.div_mod_to_equations; lia|].
    f_equal; [apply zb_eq; Z.div_mod_to_equations; lia|].
    f_equal; [apply zb_eq; Z.div_mod_to_equations; lia|].
    f_equal. apply zb_eq; Z.div_mod_to_equations; lia.
  Qed.

  #[using="Type"] Lemma le2_zbytes : forall x0 x1, 0 <= x0 < 256 -> 0 <= x1 < 256 ->
    le2 (Z_to_bv 64 (x0 + 256 * x1)) = zbytes [x0; x1].
  Proof.
    intros. unfold le2. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64). rewrite Z.mod_small by lia.
    cbn [Z_to_le_bytes zbytes map]. rewrite !Z.shiftr_div_pow2 by lia. change (2^8) with 256.
    f_equal; [apply zb_eq; Z.div_mod_to_equations; lia|].
    f_equal. apply zb_eq; Z.div_mod_to_equations; lia.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma zarr_read4 : forall m A d off, zarr m A d -> 0 <= off -> off + 4 <= Z.of_nat (length d) ->
    ov_read_bytes segs m (wa (A + off)) 4 = Some (le4 (Z_to_bv 64 (get_le32 d off))) /\ 0 <= get_le32 d off < 2^32.
  Proof.
    intros m A d off ZA Ho Hl.
    destruct (zslice_4 off d Ho Hl) as (x0 & x1 & x2 & x3 & E).
    pose proof (zslice_range off 4 d (proj2 (proj2 ZA))) as R. rewrite E in R.
    apply Forall_cons_iff in R as [R0 R]. apply Forall_cons_iff in R as [R1 R]. apply Forall_cons_iff in R as [R2 R]. apply Forall_cons_iff in R as [R3 _].
    rewrite (get_le32_of_slice _ _ _ _ _ _ E). split; [|lia].
    rewrite (le4_zbytes x0 x1 x2 x3) by lia. rewrite <- E. change 4%nat with (Z.to_nat 4). apply zarr_read_raw; [exact ZA|lia|lia|lia].
  Qed.

  #[using="Type"] Lemma zarr_read2 : forall m A d off, zarr m A d -> 0 <= off -> off + 2 <= Z.of_nat (length d) ->
    ov_read_bytes segs m (wa (A + off)) 2 = Some (le2 (Z_to_bv 64 (get_le16 d off))) /\ 0 <= get_le16 d off < 65536.
  Proof.
    intros m A d off ZA Ho Hl.
    destruct (zslice_2 off d Ho Hl) as (x0 & x1 & E).
    pose proof (zslice_range off 2 d (proj2 (proj2 ZA))) as R. rewrite E in R.
    apply Forall_cons_iff in R as [R0 R]. apply Forall_cons_iff in R as [R1 _].
    rewrite (get_le16_of_slice _ _ _ _ E). split; [|lia].
    rewrite (le2_zbytes x0 x1) by lia. rewrite <- E. change 2%nat with (Z.to_nat 2). apply zarr_read_raw; [exact ZA|lia|lia|lia].
  Qed.

  #[using="Type"] Lemma zarr_read1 : forall m A d off, zarr m A d -> 0 <= off -> off + 1 <= Z.of_nat (length d) ->
    ov_read_bytes segs m (wa (A + off)) 1 = Some [Z_to_bv 8 (get_u8 d off)] /\ 0 <= get_u8 d off < 256.
  Proof.
    intros m A d off ZA Ho Hl. split.
    - change 1%nat with (Z.to_nat 1). rewrite (zarr_read_raw m A d off 1 ZA) by lia. rewrite (get_u8_single off d) by lia. reflexivity.
    - pose proof (zslice_range off 1 d (proj2 (proj2 ZA))) as R. rewrite (get_u8_single off d) in R by lia. apply Forall_cons_iff in R as [R _]. exact R.
  Qed.

  #[using="Type"] Lemma zarr_store_ok : forall m A d off n a, zarr m A d -> 0 <= off -> off + Z.of_nat n <= Z.of_nat (length d) -> a = wa (A + off) ->
    store_ok segs m a n = true.
  Proof. intros m A d off n a (_ & W & _) Ho Hl ->. eapply wr_at_store_ok; [exact W| lia | lia]. Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma zarr_write : forall m A d off l, zarr m A d -> 0 <= off -> off + Z.of_nat (length l) <= Z.of_nat (length d) ->
    Forall (fun x => 0 <= x < 256) l ->
    zarr (write_to_mem m (wa (A + off)) (zbytes l)) A (buf_write_at off l d).
  Proof.
    intros m A d off l (B & W & R) Ho Hl Rl. split; [|split].
    - pose proof (bytes_at_write_inside segs m A (zbytes d) off (zbytes l) B Ho ltac:(rewrite !zbytes_length; lia)) as B'.
      eapply bytes_at_ext; [exact B'|]. unfold upd_bytes, buf_write_at, zbytes, zfirstn, zskipn, zlength.
      rewrite map_app, map_app, firstn_map, skipn_map, length_map. do 2 f_equal. f_equal. f_equal. lia.
    - rewrite buf_write_at_length by lia. apply wr_at_write. exact W.
    - apply buf_write_at_range; assumption.
  Qed.

  #[using="Type"] Lemma zarr_mem_inv : forall m A d off l, zarr m A d -> mem_inv segs m -> 0 <= off -> off + Z.of_nat (length l) <= Z.of_nat (length d) ->
    mem_inv segs (write_to_mem m (wa (A + off)) (zbytes l)).
  Proof.
    intros m A d off l ZA MI Ho Hl. apply mem_inv_store; [exact MI|]. rewrite zbytes_length.
    eapply zarr_store_ok; [exact ZA| exact Ho| exact Hl| reflexivity].
  Qed.
End ZA.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma sx32_small : forall x, 0 <= x < 2^31 -> sx32 (Z_to_bv 64 x) = Z_to_bv 64 x.
Proof.
  intros x Hx. unfold sx32. f_equal. rewrite unsigned_lit by lia. rewrite bv_swrap32_eq.
  rewrite Z.mod_small by lia. lia.
Qed.
Lemma zx32_small : forall x, 0 <= x < 2^32 -> zx32 (Z_to_bv 64 x) = Z_to_bv 64 x.
Proof. intros x Hx. unfold zx32. f_equal. rewrite unsigned_lit by lia. apply Z.mod_small. lia. Qed.
Lemma zx16_small : forall x, 0 <= x < 2^16 -> zx16 (Z_to_bv 64 x) = Z_to_bv 64 x.
Proof. intros x Hx. unfold zx16. f_equal. rewrite unsigned_lit by lia. apply Z.mod_small. lia. Qed.
Lemma zxb_small : forall x, 0 <= x < 256 -> zxb (Z_to_bv 8 x) = Z_to_bv 64 x.
Proof. intros x Hx. unfold zxb. f_equal. rewrite Z_to_bv_unsigned. apply Z.mod_small. exact Hx. Qed.
Lemma sxb_small : forall x, 0 <= x < 256 -> sxb (Z_to_bv 8 x) = Z_to_bv 64 (if x <? 128 then x else x - 256).
Proof.
  intros x Hx. unfold sxb. f_equal. unfold bv_signed. rewrite Z_to_bv_unsigned. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (Z.of_N 8) with 8. change (2^8) with 256. cbn [Z.div Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul].
  destruct (Z.ltb_spec x 128); Z.div_mod_to_equations; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ltu_falseZ : forall x y, 0 <= y <= x -> x < 2^64 -> bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y) = false.
Proof. intros. rewrite bv_ltu_Z, !unsigned_lit by lia. apply Z.ltb_ge. lia. Qed.
Lemma ltu_trueZ : forall x y, 0 <= x < y -> y < 2^64 -> bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y) = true.
Proof. intros. rewrite bv_ltu_Z, !unsigned_lit by lia. apply Z.ltb_lt. lia. Qed.
Lemma eqb_falseZ : forall x y, 0 <= x < 2^64 -> 0 <= y < 2^64 -> x <> y -> bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = false.
Proof. intros. unfold bv_eqb. rewrite !unsigned_lit by lia. apply Z.eqb_neq. lia. Qed.
Lemma eqb_trueZ : forall x y, x = y -> bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = true.
Proof. intros x y ->. unfold bv_eqb. apply Z.eqb_refl. Qed.
Lemma signed_small : forall x, 0 <= x < 2^63 -> bv_signed (Z_to_bv 64 x) = x.
Proof.
  intros x Hx. unfold bv_signed. rewrite Z_to_bv_unsigned. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (Z.of_N 64) with 64. change (2^64 `div` 2) with (2^63). rewrite (Z.mod_small x) by lia. rewrite Z.mod_small by lia. lia.
Qed.
Lemma lts_falseZ : forall x y, 0 <= y <= x -> x < 2^63 -> bv_lts (Z_to_bv 64 x) (Z_to_bv 64 y) = false.
Proof. intros. unfold bv_lts. rewrite !signed_small by lia. apply Z.ltb_ge. lia. Qed.
Lemma lts_trueZ : forall x y, 0 <= x < y -> y < 2^63 -> bv_lts (Z_to_bv 64 x) (Z_to_bv 64 y) = true.
Proof. intros. unfold bv_lts. rewrite !signed_small by lia. apply Z.ltb_lt. lia. Qed.

(* [comment removed for export] *)
Lemma unsigned_sx32 : forall x, 0 <= x < 2^32 ->
  bv_unsigned (sx32 (Z_to_bv 64 x)) = (if x <? 2^31 then x else x + 2^64 - 2^32).
Proof.
  intros x Hx. unfold sx32. rewrite (unsigned_lit x) by lia. rewrite unsigned_lit_wrap, bv_swrap32_eq.
  destruct (Z.ltb_spec x (2^31)).
  - rewrite (Z.mod_small (x + 2^31)) by lia. rewrite Z.mod_small by lia. lia.
  - replace ((x + 2 ^ 31) mod 2 ^ 32) with (x + 2^31 - 2^32) by (Z.div_mod_to_equations; lia).
    Z.div_mod_to_equations. lia.
Qed.
Lemma ltu_sx32_lit : forall x k, 0 <= x < 2^32 -> 0 <= k < 2^31 ->
  bv_ltu (sx32 (Z_to_bv 64 x)) (Z_to_bv 64 k) = (x <? k).
Proof.
  intros x k Hx Hk. rewrite bv_ltu_Z, unsigned_sx32, (unsigned_lit k) by lia.
  destruct (Z.ltb_spec x (2^31)); destruct (Z.ltb_spec x k); fastfirst (first [ noevar_assumption |reflexivity | apply Z.ltb_lt; lia | apply Z.ltb_ge; lia]).
Qed.

(* [comment removed for export] *)
Lemma lor_be16 : forall a b, 0 <= a < 256 -> 0 <= b < 256 -> Z.lor ((Z.shiftl a 8) mod 2^64) b = a * 256 + b.
Proof.
  intros a b Ha Hb. rewrite Z.shiftl_mul_pow2 by lia. change (2^8) with 256. rewrite Z.mod_small by lia.
  rewrite (lor_add (a * 256) b 8); [lia| lia | change (2^8) with 256; lia |]. change (2^8) with 256. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Lemma ltu_minus12 : forall p, 0 <= p < 65536 ->
  bv_ltu (Z_to_bv 64 (p + -12)) (Z_to_bv 64 2) = ((p =? 12) || (p =? 13))%bool.
Proof.
  intros p Hp. rewrite bv_ltu_Z, (unsigned_lit 2), unsigned_lit_wrap by lia.
  destruct (Z.eqb_spec p 12) as [->|N1]; [reflexivity|]. destruct (Z.eqb_spec p 13) as [->|N2]; [reflexivity|]. cbn [orb].
  apply Z.ltb_ge. destruct (Z_lt_le_dec p 12).
  - replace ((p + -12) mod 2^64) with (p + -12 + 2^64) by (Z.div_mod_to_equations; lia). lia.
  - rewrite Z.mod_small by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma swrap32_small : forall x, -2^31 <= x < 2^31 -> bv_swrap 32 x = x.
Proof. intros x Hx. rewrite bv_swrap32_eq. Z.div_mod_to_equations. lia. Qed.
Lemma swrap32_period : forall x k, bv_swrap 32 (x + k * 2^32) = bv_swrap 32 x.
Proof. intros. rewrite !bv_swrap32_eq. f_equal. replace (x + k * 2^32 + 2^31) with (x + 2^31 + k * 2^32) by lia. apply Z.mod_add. lia. Qed.
Lemma swrap_of_sx32 : forall x k, 0 <= x < 2^32 -> bv_swrap 32 (bv_unsigned (sx32 (Z_to_bv 64 x)) + k) = bv_swrap 32 (x + k).
Proof.
  intros x k Hx. rewrite unsigned_sx32 by lia. destruct (Z.ltb_spec x (2^31)); [reflexivity|].
  replace (x + 2^64 - 2^32 + k) with (x + k + (2^32 - 1) * 2^32) by lia. apply swrap32_period.
Qed.
Lemma sx32_swrap : forall x, 0 <= x < 2^32 -> sx32 (Z_to_bv 64 x) = Z_to_bv 64 (bv_swrap 32 x).
Proof. intros. unfold sx32. rewrite unsigned_lit by lia. reflexivity. Qed.
Lemma unsigned_swrap32 : forall x, bv_unsigned (Z_to_bv 64 (bv_swrap 32 x)) = (if x mod 2^32 <? 2^31 then x mod 2^32 else x mod 2^32 + 2^64 - 2^32).
Proof.
  intros x. rewrite unsigned_lit_wrap, bv_swrap32_eq.
  replace ((x + 2^31) mod 2^32) with ((x mod 2^32 + 2^31) mod 2^32) by (Z.div_mod_to_equations; nia || lia).
  pose proof (Z.mod_pos_bound x (2^32) ltac:(lia)) as R. set (y := x mod 2^32) in *.
  destruct (Z.ltb_spec y (2^31)).
  - rewrite (Z.mod_small (y + 2^31)) by lia. rewrite Z.mod_small by lia. lia.
  - replace ((y + 2^31) mod 2^32) with (y + 2^31 - 2^32) by (Z.div_mod_to_equations; lia). Z.div_mod_to_equations. lia.
Qed.
Lemma ltu_swrap_lit : forall x k, 0 <= k < 2^31 ->
  bv_ltu (Z_to_bv 64 (bv_swrap 32 x)) (Z_to_bv 64 k) = (x mod 2^32 <? k).
Proof.
  intros x k Hk. rewrite bv_ltu_Z, unsigned_swrap32, (unsigned_lit k) by lia.
  pose proof (Z.mod_pos_bound x (2^32) ltac:(lia)) as R.
  destruct (Z.ltb_spec (x mod 2^32) (2^31)); destruct (Z.ltb_spec (x mod 2^32) k); fastfirst (first [ noevar_assumption |reflexivity | apply Z.ltb_lt; lia | apply Z.ltb_ge; lia]).
Qed.

Lemma ltu_swrap_falseZ : forall x k, 0 <= x < 2^32 -> 0 <= k < 2^31 -> k <= x ->
  bv_ltu (Z_to_bv 64 (bv_swrap 32 x)) (Z_to_bv 64 k) = false.
Proof. intros. rewrite ltu_swrap_lit by lia. rewrite Z.mod_small by lia. apply Z.ltb_ge. lia. Qed.
Lemma ltu_swrap_trueZ : forall x k, 0 <= x < 2^32 -> 0 <= k < 2^31 -> x < k ->
  bv_ltu (Z_to_bv 64 (bv_swrap 32 x)) (Z_to_bv 64 k) = true.
Proof. intros. rewrite ltu_swrap_lit by lia. rewrite Z.mod_small by lia. apply Z.ltb_lt. lia. Qed.
Lemma ltu_sx32_falseZ : forall x k, 0 <= x < 2^32 -> 0 <= k < 2^31 -> k <= x ->
  bv_ltu (sx32 (Z_to_bv 64 x)) (Z_to_bv 64 k) = false.
Proof. intros. rewrite ltu_sx32_lit by lia. apply Z.ltb_ge. lia. Qed.
Lemma ltu_sx32_trueZ : forall x k, 0 <= x < 2^32 -> 0 <= k < 2^31 -> x < k ->
  bv_ltu (sx32 (Z_to_bv 64 x)) (Z_to_bv 64 k) = true.
Proof. intros. rewrite ltu_sx32_lit by lia. apply Z.ltb_lt. lia. Qed.

Ltac cond_side :=
  fastfirst (first [ noevar_assumption | apply ltu_falseZ; lia | apply ltu_trueZ; lia | apply eqb_falseZ; lia | apply eqb_trueZ; lia
        | apply lts_falseZ; lia | apply lts_trueZ; lia
        | apply ltu_swrap_falseZ; lia | apply ltu_swrap_trueZ; lia | apply ltu_sx32_falseZ; lia | apply ltu_sx32_trueZ; lia
        | apply (proj2 (Bool.negb_false_iff _)); cond_side_t
        | apply (proj2 (Bool.negb_true_iff _)); cond_side ])
with cond_side_t :=
  fastfirst (first [ noevar_assumption | apply ltu_trueZ; lia | apply eqb_trueZ; lia | apply lts_trueZ; lia
        | apply ltu_swrap_trueZ; lia | apply ltu_sx32_trueZ; lia
        | apply (proj2 (Bool.negb_true_iff _)); cond_side ]).
(* [comment removed for export] *)
Ltac bfalse :=
  lazymatch goal with |- evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
    replace c with false; [cbv iota| symmetry; cond_side] end.
Ltac btrue :=
  lazymatch goal with |- evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
    replace c with true; [cbv iota| symmetry; cond_side_t] end.
(* [comment removed for export] *)
Ltac bstep := lstep; try (lazymatch goal with |- evtF _ _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => first [bfalse | btrue] end).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma land_mask8 : forall y k, 0 <= y -> 0 <= k -> Z.land y (255 * 2^k) = ((y / 2^k) mod 256) * 2^k.
Proof.
  intros y k Hy Hk. apply Z.bits_inj'. intros n Hn.
  rewrite Z.land_spec.
  replace (255 * 2^k) with (Z.shiftl (Z.ones 8) k) by (rewrite Z.shiftl_mul_pow2 by lia; reflexivity).
  replace ((y / 2^k) mod 256 * 2^k) with (Z.shiftl ((Z.shiftr y k) mod 2^8) k)
    by (rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia; reflexivity).
  destruct (Z_lt_le_dec n k).
  - rewrite !Z.shiftl_spec_low by lia. apply Bool.andb_false_r.
  - rewrite !Z.shiftl_spec_high by lia.
    destruct (Z_lt_le_dec (n - k) 8).
    + rewrite Z.ones_spec_low, Z.mod_pow2_bits_low, Z.shiftr_spec by lia. rewrite Bool.andb_true_r. f_equal. lia.
    + rewrite Z.ones_spec_high, Z.mod_pow2_bits_high by lia. apply Bool.andb_false_r.
Qed.

Lemma land_65280 : forall y, 0 <= y -> Z.land y 65280 = ((y / 256) mod 256) * 256.
Proof. intros. change 65280 with (255 * 2^8). rewrite land_mask8 by lia. reflexivity. Qed.
Lemma land_16711680 : forall y, 0 <= y -> Z.land y 16711680 = ((y / 65536) mod 256) * 65536.
Proof. intros. change 16711680 with (255 * 2^16). rewrite land_mask8 by lia. reflexivity. Qed.



Lemma sx32_mod32 : forall x, 0 <= x < 2^32 -> bv_unsigned (sx32 (Z_to_bv 64 x)) mod 2^32 = x.
Proof.
  intros x Hx. rewrite unsigned_sx32 by lia. destruct (Z.ltb_spec x (2^31)).
  - apply Z.mod_small. lia.
  - Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Lemma le4_bswap32 : forall X x0 x1 x2 x3,
  0 <= X < 2^64 -> 0 <= x0 < 256 -> 0 <= x1 < 256 -> 0 <= x2 < 256 -> 0 <= x3 < 256 ->
  X mod 2^32 = x0 + 256 * x1 + 65536 * x2 + 16777216 * x3 ->
  le4 (Z_to_bv 64 (Z.lor (Z.lor ((Z.shiftl X 24) mod 18446744073709551616) ((Z.shiftl (Z.land X 65280) 8) mod 18446744073709551616))
                           (Z.lor (Z.land (Z.shiftr X 8) 65280) ((bv_swrap 32 (Z.shiftr (bv_wrap 32 X) 24)) mod 18446744073709551616))))
  = zbytes [x3; x2; x1; x0].
Proof.
  intros X x0 x1 x2 x3 HX H0 H1 H2 H3 HV.
  rewrite bv_wrap32_eq.
  rewrite !land_65280 by (try apply Z.shiftr_nonneg; lia).
  rewrite !Z.shiftl_mul_pow2, !Z.shiftr_div_pow2 by lia.
  assert (E1 : (X / 256) mod 256 = x1) by (Z.div_mod_to_equations; lia).
  assert (E2 : (X / 2^8 / 256) mod 256 = x2) by (Z.div_mod_to_equations; lia).
  assert (E3 : X mod 2^32 / 2^24 = x3) by (Z.div_mod_to_equations; lia).
  rewrite E1, E2, E3. rewrite (swrap32_small x3) by lia.
  rewrite (Z.mod_small x3) by lia.
  rewrite (Z.mod_small (x1 * 256 * 2^8)) by lia.
  rewrite (lor_add (x2 * 256) x3 8) by (try lia; Z.div_mod_to_equations; lia).
  rewrite (lor_add ((X * 2^24) mod 18446744073709551616) (x1 * 256 * 2^8) 24) by (try lia; Z.div_mod_to_equations; lia).
  rewrite (lor_add _ (x2 * 256 + x3) 16) by (try lia; Z.div_mod_to_equations; lia).
  apply le4_of_mod32; [reflexivity|]. cbn [zbytes map le_val]. rewrite !Z_to_bv_unsigned.
  unfold bv_wrap. change (bv_modulus 64) with (2^64). change (bv_modulus 8) with 256.
  rewrite !(Z.mod_small _ 256) by lia. Z.div_mod_to_equations. lia.
Qed.

Lemma word_range : forall w : word, 0 <= bv_unsigned w < 2^64.
Proof. intros w. pose proof (bv_unsigned_in_range 64 w) as H. unfold bv_modulus in H. cbn in H. cbn. lia. Qed.

(* [comment removed for export] *)
Lemma le2_of_mod16 : forall (v : word) (bs : list byte), length bs = 2%nat ->
  bv_unsigned v mod 2^16 = le_val (map bv_unsigned bs) -> le2 v = bs.
Proof.
  intros v bs Hl Hv. unfold le2.
  rewrite <- (Z_to_le_bytes_mod 2 _ 16) by (cbn; lia). change (2 ^ 16) with (2^16) in *. rewrite Hv.
  rewrite <- bytes_le_to_Z_le_val, <- Hl. apply Z_to_le_bytes_to_Z.
Qed.

Lemma le2_bswap16 : forall X x0 x1, 0 <= x0 < 256 -> 0 <= x1 < 256 -> X = x0 + 256 * x1 ->
  le2 (Z_to_bv 64 (Z.lor ((Z.shiftl X 8) mod 18446744073709551616) (Z.shiftr X 8))) = zbytes [x1; x0].
Proof.
  intros X x0 x1 H0 H1 ->.
  rewrite !Z.shiftl_mul_pow2, !Z.shiftr_div_pow2 by lia. change (2^8) with 256.
  replace ((x0 + 256 * x1) / 256) with x1 by (Z.div_mod_to_equations; lia).
  rewrite (Z.mod_small _ 18446744073709551616) by lia.
  rewrite (lor_add ((x0 + 256 * x1) * 256) x1 8); [| lia | change (2^8) with 256; lia | change (2^8) with 256; Z.div_mod_to_equations; lia].
  apply le2_of_mod16; [reflexivity|]. cbn [zbytes map le_val]. rewrite !Z_to_bv_unsigned.
  unfold bv_wrap. change (bv_modulus 64) with (2^64). change (bv_modulus 8) with 256.
  rewrite !(Z.mod_small _ 256) by lia. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Image OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.RegsEquiv.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StrwF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ppA.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma zbytes_length : forall d, length (zbytes d) = length d.
Proof. intros. unfold zbytes. apply length_map. Qed.

Lemma Forall_range_firstn : forall (P : Z -> Prop) n (d : list Z), Forall P d -> Forall P (firstn n d).
Proof. intros P n d H. rewrite <- (firstn_skipn n d) in H. apply Forall_app in H as [H _]. exact H. Qed.
Lemma Forall_range_skipn : forall (P : Z -> Prop) n (d : list Z), Forall P d -> Forall P (skipn n d).
Proof. intros P n d H. rewrite <- (firstn_skipn n d) in H. apply Forall_app in H as [_ H]. exact H. Qed.
Lemma Forall_rev : forall (P : Z -> Prop) (d : list Z), Forall P d -> Forall P (rev d).
Proof. intros P d H. apply Forall_forall. intros x Hx. apply in_rev in Hx. exact (proj1 (Forall_forall _ _) H x Hx). Qed.

Lemma zslice_length : forall off n (d : list Z), 0 <= off -> 0 <= n -> off + n <= Z.of_nat (length d) ->
  length (zslice off n d) = Z.to_nat n.
Proof. intros. unfold zslice, zfirstn, zskipn. rewrite length_firstn, length_skipn. lia. Qed.

Lemma buf_write_at_length : forall off l (d : list Z), 0 <= off -> off + Z.of_nat (length l) <= Z.of_nat (length d) ->
  length (buf_write_at off l d) = length d.
Proof.
  intros. unfold buf_write_at, zfirstn, zskipn, zlength. rewrite !length_app, length_firstn, length_skipn. lia.
Qed.

Lemma buf_write_at_range : forall off l (d : list Z),
  Forall (fun x => 0 <= x < 256) d -> Forall (fun x => 0 <= x < 256) l -> Forall (fun x => 0 <= x < 256) (buf_write_at off l d).
Proof.
  intros. unfold buf_write_at, zfirstn, zskipn. apply Forall_app. split; [apply Forall_range_firstn; assumption|].
  apply Forall_app. split; [assumption| apply Forall_range_skipn; assumption].
Qed.

Lemma swap_field_length : forall k off (d : list Z), 0 <= off -> 0 <= k -> off + k <= Z.of_nat (length d) ->
  length (swap_field k off d) = length d.
Proof.
  intros. unfold swap_field. apply buf_write_at_length; [lia|]. rewrite length_rev, zslice_length by lia. lia.
Qed.

Lemma swap_field_range : forall k off (d : list Z),
  Forall (fun x => 0 <= x < 256) d -> Forall (fun x => 0 <= x < 256) (swap_field k off d).
Proof.
  intros. unfold swap_field. apply buf_write_at_range; [assumption|]. apply Forall_rev. unfold zslice, zfirstn, zskipn.
  apply Forall_range_firstn. apply Forall_range_skipn. assumption.
Qed.

(* [comment removed for export] *)
Lemma zslice_4 : forall off (d : list Z), 0 <= off -> off + 4 <= Z.of_nat (length d) ->
  exists x0 x1 x2 x3, zslice off 4 d = [x0; x1; x2; x3].
Proof.
  intros off d Ho Hl. pose proof (zslice_length off 4 d Ho ltac:(lia) Hl) as L.
  destruct (zslice off 4 d) as [|x0 [|x1 [|x2 [|x3 [|]]]]]; cbn in L; try lia. repeat eexists.
Qed.
Lemma zslice_2 : forall off (d : list Z), 0 <= off -> off + 2 <= Z.of_nat (length d) ->
  exists x0 x1, zslice off 2 d = [x0; x1].
Proof.
  intros off d Ho Hl. pose proof (zslice_length off 2 d Ho ltac:(lia) Hl) as L.
  destruct (zslice off 2 d) as [|x0 [|x1 [|]]]; cbn in L; try lia. repeat eexists.
Qed.

Lemma zslice_range : forall off n (d : list Z), Forall (fun x => 0 <= x < 256) d -> Forall (fun x => 0 <= x < 256) (zslice off n d).
Proof. intros. unfold zslice, zfirstn, zskipn. apply Forall_range_firstn. apply Forall_range_skipn. assumption. Qed.

(* [comment removed for export] *)
Lemma znth_slice : forall (d : list Z) off n j, 0 <= off -> 0 <= j < n -> off + n <= Z.of_nat (length d) ->
  nth_error (zslice off n d) (Z.to_nat j) = Some (znth d (off + j)).
Proof.
  intros d off n j Ho Hj Hl. unfold zslice, zfirstn, zskipn.
  rewrite (nth_error_nth' _ 0).
  2:{ rewrite length_firstn, length_skipn. lia. }
  f_equal. rewrite nth_firstn. replace (Z.to_nat j <? Z.to_nat n)%nat with true by (symmetry; apply Nat.ltb_lt; lia). rewrite nth_skipn. unfold znth.
  replace (off + j <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
  f_equal. lia.
Qed.

Lemma get_u8_of_slice4 : forall off d x0 x1 x2 x3, 0 <= off -> off + 4 <= Z.of_nat (length d) ->
  zslice off 4 d = [x0; x1; x2; x3] ->
  get_u8 d off = x0 /\ get_u8 d (off + 1) = x1 /\ get_u8 d (off + 2) = x2 /\ get_u8 d (off + 3) = x3.
Proof.
  intros off d x0 x1 x2 x3 Ho Hl E. unfold get_u8.
  pose proof (znth_slice d off 4 0 Ho ltac:(lia) Hl) as E0. change (Z.to_nat 0) with 0%nat in E0.
  pose proof (znth_slice d off 4 1 Ho ltac:(lia) Hl) as E1. change (Z.to_nat 1) with 1%nat in E1.
  pose proof (znth_slice d off 4 2 Ho ltac:(lia) Hl) as E2. change (Z.to_nat 2) with 2%nat in E2.
  pose proof (znth_slice d off 4 3 Ho ltac:(lia) Hl) as E3. change (Z.to_nat 3) with 3%nat in E3.
  rewrite E in E0, E1, E2, E3. cbn [nth_error] in E0, E1, E2, E3. rewrite Z.add_0_r in E0.
  injection E0 as <-. injection E1 as <-. injection E2 as <-. injection E3 as <-. repeat split; reflexivity.
Qed.
Lemma get_u8_of_slice2 : forall off d x0 x1, 0 <= off -> off + 2 <= Z.of_nat (length d) ->
  zslice off 2 d = [x0; x1] -> get_u8 d off = x0 /\ get_u8 d (off + 1) = x1.
Proof.
  intros off d x0 x1 Ho Hl E. unfold get_u8.
  pose proof (znth_slice d off 2 0 Ho ltac:(lia) Hl) as E0. change (Z.to_nat 0) with 0%nat in E0.
  pose proof (znth_slice d off 2 1 Ho ltac:(lia) Hl) as E1. change (Z.to_nat 1) with 1%nat in E1.
  rewrite E in E0, E1. cbn [nth_error] in E0, E1. rewrite Z.add_0_r in E0.
  injection E0 as <-. injection E1 as <-. split; reflexivity.
Qed.
Lemma get_u8_single : forall off d, 0 <= off -> off + 1 <= Z.of_nat (length d) -> zslice off 1 d = [get_u8 d off].
Proof.
  intros off d Ho Hl. pose proof (zslice_length off 1 d Ho ltac:(lia) Hl) as L.
  pose proof (znth_slice d off 1 0 Ho ltac:(lia) Hl) as E0. change (Z.to_nat 0) with 0%nat in E0.
  destruct (zslice off 1 d) as [|y [|]]; cbn in L; try lia. cbn [nth_error] in E0. rewrite Z.add_0_r in E0. unfold get_u8. injection E0 as ->. reflexivity.
Qed.

Lemma get_le32_of_slice : forall off d x0 x1 x2 x3, zslice off 4 d = [x0; x1; x2; x3] ->
  get_le32 d off = x0 + 256 * x1 + 65536 * x2 + 16777216 * x3.
Proof. intros off d x0 x1 x2 x3 E. unfold get_le32. rewrite E. cbn. lia. Qed.
Lemma get_le16_of_slice : forall off d x0 x1, zslice off 2 d = [x0; x1] -> get_le16 d off = x0 + 256 * x1.
Proof. intros off d x0 x1 E. unfold get_le16. rewrite E. cbn. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section ZA.
  Notation segs := asegs.

  #[using="Type"] Lemma zarr_bound : forall m A d, zarr m A d -> 0 <= A /\ A + Z.of_nat (length d) <= 2^64.
  Proof. intros m A d (B & _ & _). apply bytes_at_bound in B. rewrite zbytes_length in B. exact B. Qed.

  #[using="Type"] Lemma zarr_read_raw : forall m A d off n, zarr m A d -> 0 <= off -> 0 <= n -> off + n <= Z.of_nat (length d) ->
    ov_read_bytes segs m (wa (A + off)) (Z.to_nat n) = Some (zbytes (zslice off n d)).
  Proof.
    intros m A d off n (B & _ & _) Ho Hn Hl.
    rewrite (bytes_at_read segs m A (zbytes d) off (Z.to_nat n) B) by (rewrite ?zbytes_length; lia).
    unfold zslice, zfirstn, zskipn, zbytes. rewrite skipn_map, firstn_map. reflexivity.
  Qed.

  #[using="Type"] Lemma zb_eq : forall a b, a mod 256 = b mod 256 -> Z_to_bv 8 a = Z_to_bv 8 b.
  Proof. intros a b E. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. exact E. Qed.

  #[using="Type"] Lemma le4_zbytes : forall x0 x1 x2 x3, 0 <= x0 < 256 -> 0 <= x1 < 256 -> 0 <= x2 < 256 -> 0 <= x3 < 256 ->
    le4 (Z_to_bv 64 (x0 + 256 * x1 + 65536 * x2 + 16777216 * x3)) = zbytes [x0; x1; x2; x3].
  Proof.
    intros. unfold le4. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64). rewrite Z.mod_small by lia.
    cbn [Z_to_le_bytes zbytes map]. rewrite !Z.shiftr_div_pow2 by lia. change (2^8) with 256.
    f_equal; [apply zb_eq; Z.div_mod_to_equations; lia|].
    f_equal; [apply zb_eq; Z.div_mod_to_equations; lia|].
    f_equal; [apply zb_eq; Z.div_mod_to_equations; lia|].
    f_equal. apply zb_eq; Z.div_mod_to_equations; lia.
  Qed.

  #[using="Type"] Lemma le2_zbytes : forall x0 x1, 0 <= x0 < 256 -> 0 <= x1 < 256 ->
    le2 (Z_to_bv 64 (x0 + 256 * x1)) = zbytes [x0; x1].
  Proof.
    intros. unfold le2. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64). rewrite Z.mod_small by lia.
    cbn [Z_to_le_bytes zbytes map]. rewrite !Z.shiftr_div_pow2 by lia. change (2^8) with 256.
    f_equal; [apply zb_eq; Z.div_mod_to_equations; lia|].
    f_equal. apply zb_eq; Z.div_mod_to_equations; lia.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma zarr_read4 : forall m A d off, zarr m A d -> 0 <= off -> off + 4 <= Z.of_nat (length d) ->
    ov_read_bytes segs m (wa (A + off)) 4 = Some (le4 (Z_to_bv 64 (get_le32 d off))) /\ 0 <= get_le32 d off < 2^32.
  Proof.
    intros m A d off ZA Ho Hl.
    destruct (zslice_4 off d Ho Hl) as (x0 & x1 & x2 & x3 & E).
    pose proof (zslice_range off 4 d (proj2 (proj2 ZA))) as R. rewrite E in R.
    apply Forall_cons_iff in R as [R0 R]. apply Forall_cons_iff in R as [R1 R]. apply Forall_cons_iff in R as [R2 R]. apply Forall_cons_iff in R as [R3 _].
    rewrite (get_le32_of_slice _ _ _ _ _ _ E). split; [|lia].
    rewrite (le4_zbytes x0 x1 x2 x3) by lia. rewrite <- E. change 4%nat with (Z.to_nat 4). apply zarr_read_raw; [exact ZA|lia|lia|lia].
  Qed.

  #[using="Type"] Lemma zarr_read2 : forall m A d off, zarr m A d -> 0 <= off -> off + 2 <= Z.of_nat (length d) ->
    ov_read_bytes segs m (wa (A + off)) 2 = Some (le2 (Z_to_bv 64 (get_le16 d off))) /\ 0 <= get_le16 d off < 65536.
  Proof.
    intros m A d off ZA Ho Hl.
    destruct (zslice_2 off d Ho Hl) as (x0 & x1 & E).
    pose proof (zslice_range off 2 d (proj2 (proj2 ZA))) as R. rewrite E in R.
    apply Forall_cons_iff in R as [R0 R]. apply Forall_cons_iff in R as [R1 _].
    rewrite (get_le16_of_slice _ _ _ _ E). split; [|lia].
    rewrite (le2_zbytes x0 x1) by lia. rewrite <- E. change 2%nat with (Z.to_nat 2). apply zarr_read_raw; [exact ZA|lia|lia|lia].
  Qed.

  #[using="Type"] Lemma zarr_read1 : forall m A d off, zarr m A d -> 0 <= off -> off + 1 <= Z.of_nat (length d) ->
    ov_read_bytes segs m (wa (A + off)) 1 = Some [Z_to_bv 8 (get_u8 d off)] /\ 0 <= get_u8 d off < 256.
  Proof.
    intros m A d off ZA Ho Hl. split.
    - change 1%nat with (Z.to_nat 1). rewrite (zarr_read_raw m A d off 1 ZA) by lia. rewrite (get_u8_single off d) by lia. reflexivity.
    - pose proof (zslice_range off 1 d (proj2 (proj2 ZA))) as R. rewrite (get_u8_single off d) in R by lia. apply Forall_cons_iff in R as [R _]. exact R.
  Qed.

  #[using="Type"] Lemma zarr_store_ok : forall m A d off n a, zarr m A d -> 0 <= off -> off + Z.of_nat n <= Z.of_nat (length d) -> a = wa (A + off) ->
    store_ok segs m a n = true.
  Proof. intros m A d off n a (_ & W & _) Ho Hl ->. eapply wr_at_store_ok; [exact W| lia | lia]. Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma zarr_write : forall m A d off l, zarr m A d -> 0 <= off -> off + Z.of_nat (length l) <= Z.of_nat (length d) ->
    Forall (fun x => 0 <= x < 256) l ->
    zarr (write_to_mem m (wa (A + off)) (zbytes l)) A (buf_write_at off l d).
  Proof.
    intros m A d off l (B & W & R) Ho Hl Rl. split; [|split].
    - pose proof (bytes_at_write_inside segs m A (zbytes d) off (zbytes l) B Ho ltac:(rewrite !zbytes_length; lia)) as B'.
      eapply bytes_at_ext; [exact B'|]. unfold upd_bytes, buf_write_at, zbytes, zfirstn, zskipn, zlength.
      rewrite map_app, map_app, firstn_map, skipn_map, length_map. do 2 f_equal. f_equal. f_equal. lia.
    - rewrite buf_write_at_length by lia. apply wr_at_write. exact W.
    - apply buf_write_at_range; assumption.
  Qed.

  #[using="Type"] Lemma zarr_mem_inv : forall m A d off l, zarr m A d -> mem_inv segs m -> 0 <= off -> off + Z.of_nat (length l) <= Z.of_nat (length d) ->
    mem_inv segs (write_to_mem m (wa (A + off)) (zbytes l)).
  Proof.
    intros m A d off l ZA MI Ho Hl. apply mem_inv_store; [exact MI|]. rewrite zbytes_length.
    eapply zarr_store_ok; [exact ZA| exact Ho| exact Hl| reflexivity].
  Qed.
End ZA.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma sx32_small : forall x, 0 <= x < 2^31 -> sx32 (Z_to_bv 64 x) = Z_to_bv 64 x.
Proof.
  intros x Hx. unfold sx32. f_equal. rewrite unsigned_lit by lia. rewrite bv_swrap32_eq.
  rewrite Z.mod_small by lia. lia.
Qed.
Lemma zx32_small : forall x, 0 <= x < 2^32 -> zx32 (Z_to_bv 64 x) = Z_to_bv 64 x.
Proof. intros x Hx. unfold zx32. f_equal. rewrite unsigned_lit by lia. apply Z.mod_small. lia. Qed.
Lemma zx16_small : forall x, 0 <= x < 2^16 -> zx16 (Z_to_bv 64 x) = Z_to_bv 64 x.
Proof. intros x Hx. unfold zx16. f_equal. rewrite unsigned_lit by lia. apply Z.mod_small. lia. Qed.
Lemma zxb_small : forall x, 0 <= x < 256 -> zxb (Z_to_bv 8 x) = Z_to_bv 64 x.
Proof. intros x Hx. unfold zxb. f_equal. rewrite Z_to_bv_unsigned. apply Z.mod_small. exact Hx. Qed.
Lemma sxb_small : forall x, 0 <= x < 256 -> sxb (Z_to_bv 8 x) = Z_to_bv 64 (if x <? 128 then x else x - 256).
Proof.
  intros x Hx. unfold sxb. f_equal. unfold bv_signed. rewrite Z_to_bv_unsigned. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (Z.of_N 8) with 8. change (2^8) with 256. cbn [Z.div Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul].
  destruct (Z.ltb_spec x 128); Z.div_mod_to_equations; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ltu_falseZ : forall x y, 0 <= y <= x -> x < 2^64 -> bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y) = false.
Proof. intros. rewrite bv_ltu_Z, !unsigned_lit by lia. apply Z.ltb_ge. lia. Qed.
Lemma ltu_trueZ : forall x y, 0 <= x < y -> y < 2^64 -> bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y) = true.
Proof. intros. rewrite bv_ltu_Z, !unsigned_lit by lia. apply Z.ltb_lt. lia. Qed.
Lemma eqb_falseZ : forall x y, 0 <= x < 2^64 -> 0 <= y < 2^64 -> x <> y -> bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = false.
Proof. intros. unfold bv_eqb. rewrite !unsigned_lit by lia. apply Z.eqb_neq. lia. Qed.
Lemma eqb_trueZ : forall x y, x = y -> bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = true.
Proof. intros x y ->. unfold bv_eqb. apply Z.eqb_refl. Qed.
Lemma signed_small : forall x, 0 <= x < 2^63 -> bv_signed (Z_to_bv 64 x) = x.
Proof.
  intros x Hx. unfold bv_signed. rewrite Z_to_bv_unsigned. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (Z.of_N 64) with 64. change (2^64 `div` 2) with (2^63). rewrite (Z.mod_small x) by lia. rewrite Z.mod_small by lia. lia.
Qed.
Lemma lts_falseZ : forall x y, 0 <= y <= x -> x < 2^63 -> bv_lts (Z_to_bv 64 x) (Z_to_bv 64 y) = false.
Proof. intros. unfold bv_lts. rewrite !signed_small by lia. apply Z.ltb_ge. lia. Qed.
Lemma lts_trueZ : forall x y, 0 <= x < y -> y < 2^63 -> bv_lts (Z_to_bv 64 x) (Z_to_bv 64 y) = true.
Proof. intros. unfold bv_lts. rewrite !signed_small by lia. apply Z.ltb_lt. lia. Qed.

(* [comment removed for export] *)
Lemma unsigned_sx32 : forall x, 0 <= x < 2^32 ->
  bv_unsigned (sx32 (Z_to_bv 64 x)) = (if x <? 2^31 then x else x + 2^64 - 2^32).
Proof.
  intros x Hx. unfold sx32. rewrite (unsigned_lit x) by lia. rewrite unsigned_lit_wrap, bv_swrap32_eq.
  destruct (Z.ltb_spec x (2^31)).
  - rewrite (Z.mod_small (x + 2^31)) by lia. rewrite Z.mod_small by lia. lia.
  - replace ((x + 2 ^ 31) mod 2 ^ 32) with (x + 2^31 - 2^32) by (Z.div_mod_to_equations; lia).
    Z.div_mod_to_equations. lia.
Qed.
Lemma ltu_sx32_lit : forall x k, 0 <= x < 2^32 -> 0 <= k < 2^31 ->
  bv_ltu (sx32 (Z_to_bv 64 x)) (Z_to_bv 64 k) = (x <? k).
Proof.
  intros x k Hx Hk. rewrite bv_ltu_Z, unsigned_sx32, (unsigned_lit k) by lia.
  destruct (Z.ltb_spec x (2^31)); destruct (Z.ltb_spec x k); fastfirst (first [ noevar_assumption |reflexivity | apply Z.ltb_lt; lia | apply Z.ltb_ge; lia]).
Qed.

(* [comment removed for export] *)
Lemma lor_be16 : forall a b, 0 <= a < 256 -> 0 <= b < 256 -> Z.lor ((Z.shiftl a 8) mod 2^64) b = a * 256 + b.
Proof.
  intros a b Ha Hb. rewrite Z.shiftl_mul_pow2 by lia. change (2^8) with 256. rewrite Z.mod_small by lia.
  rewrite (lor_add (a * 256) b 8); [lia| lia | change (2^8) with 256; lia |]. change (2^8) with 256. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Lemma ltu_minus12 : forall p, 0 <= p < 65536 ->
  bv_ltu (Z_to_bv 64 (p + -12)) (Z_to_bv 64 2) = ((p =? 12) || (p =? 13))%bool.
Proof.
  intros p Hp. rewrite bv_ltu_Z, (unsigned_lit 2), unsigned_lit_wrap by lia.
  destruct (Z.eqb_spec p 12) as [->|N1]; [reflexivity|]. destruct (Z.eqb_spec p 13) as [->|N2]; [reflexivity|]. cbn [orb].
  apply Z.ltb_ge. destruct (Z_lt_le_dec p 12).
  - replace ((p + -12) mod 2^64) with (p + -12 + 2^64) by (Z.div_mod_to_equations; lia). lia.
  - rewrite Z.mod_small by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma swrap32_small : forall x, -2^31 <= x < 2^31 -> bv_swrap 32 x = x.
Proof. intros x Hx. rewrite bv_swrap32_eq. Z.div_mod_to_equations. lia. Qed.
Lemma swrap32_period : forall x k, bv_swrap 32 (x + k * 2^32) = bv_swrap 32 x.
Proof. intros. rewrite !bv_swrap32_eq. f_equal. replace (x + k * 2^32 + 2^31) with (x + 2^31 + k * 2^32) by lia. apply Z.mod_add. lia. Qed.
Lemma swrap_of_sx32 : forall x k, 0 <= x < 2^32 -> bv_swrap 32 (bv_unsigned (sx32 (Z_to_bv 64 x)) + k) = bv_swrap 32 (x + k).
Proof.
  intros x k Hx. rewrite unsigned_sx32 by lia. destruct (Z.ltb_spec x (2^31)); [reflexivity|].
  replace (x + 2^64 - 2^32 + k) with (x + k + (2^32 - 1) * 2^32) by lia. apply swrap32_period.
Qed.
Lemma sx32_swrap : forall x, 0 <= x < 2^32 -> sx32 (Z_to_bv 64 x) = Z_to_bv 64 (bv_swrap 32 x).
Proof. intros. unfold sx32. rewrite unsigned_lit by lia. reflexivity. Qed.
Lemma unsigned_swrap32 : forall x, bv_unsigned (Z_to_bv 64 (bv_swrap 32 x)) = (if x mod 2^32 <? 2^31 then x mod 2^32 else x mod 2^32 + 2^64 - 2^32).
Proof.
  intros x. rewrite unsigned_lit_wrap, bv_swrap32_eq.
  replace ((x + 2^31) mod 2^32) with ((x mod 2^32 + 2^31) mod 2^32) by (Z.div_mod_to_equations; nia || lia).
  pose proof (Z.mod_pos_bound x (2^32) ltac:(lia)) as R. set (y := x mod 2^32) in *.
  destruct (Z.ltb_spec y (2^31)).
  - rewrite (Z.mod_small (y + 2^31)) by lia. rewrite Z.mod_small by lia. lia.
  - replace ((y + 2^31) mod 2^32) with (y + 2^31 - 2^32) by (Z.div_mod_to_equations; lia). Z.div_mod_to_equations. lia.
Qed.
Lemma ltu_swrap_lit : forall x k, 0 <= k < 2^31 ->
  bv_ltu (Z_to_bv 64 (bv_swrap 32 x)) (Z_to_bv 64 k) = (x mod 2^32 <? k).
Proof.
  intros x k Hk. rewrite bv_ltu_Z, unsigned_swrap32, (unsigned_lit k) by lia.
  pose proof (Z.mod_pos_bound x (2^32) ltac:(lia)) as R.
  destruct (Z.ltb_spec (x mod 2^32) (2^31)); destruct (Z.ltb_spec (x mod 2^32) k); fastfirst (first [ noevar_assumption |reflexivity | apply Z.ltb_lt; lia | apply Z.ltb_ge; lia]).
Qed.

Lemma ltu_swrap_falseZ : forall x k, 0 <= x < 2^32 -> 0 <= k < 2^31 -> k <= x ->
  bv_ltu (Z_to_bv 64 (bv_swrap 32 x)) (Z_to_bv 64 k) = false.
Proof. intros. rewrite ltu_swrap_lit by lia. rewrite Z.mod_small by lia. apply Z.ltb_ge. lia. Qed.
Lemma ltu_swrap_trueZ : forall x k, 0 <= x < 2^32 -> 0 <= k < 2^31 -> x < k ->
  bv_ltu (Z_to_bv 64 (bv_swrap 32 x)) (Z_to_bv 64 k) = true.
Proof. intros. rewrite ltu_swrap_lit by lia. rewrite Z.mod_small by lia. apply Z.ltb_lt. lia. Qed.
Lemma ltu_sx32_falseZ : forall x k, 0 <= x < 2^32 -> 0 <= k < 2^31 -> k <= x ->
  bv_ltu (sx32 (Z_to_bv 64 x)) (Z_to_bv 64 k) = false.
Proof. intros. rewrite ltu_sx32_lit by lia. apply Z.ltb_ge. lia. Qed.
Lemma ltu_sx32_trueZ : forall x k, 0 <= x < 2^32 -> 0 <= k < 2^31 -> x < k ->
  bv_ltu (sx32 (Z_to_bv 64 x)) (Z_to_bv 64 k) = true.
Proof. intros. rewrite ltu_sx32_lit by lia. apply Z.ltb_lt. lia. Qed.

Ltac cond_side :=
  fastfirst (first [ noevar_assumption | apply ltu_falseZ; lia | apply ltu_trueZ; lia | apply eqb_falseZ; lia | apply eqb_trueZ; lia
        | apply lts_falseZ; lia | apply lts_trueZ; lia
        | apply ltu_swrap_falseZ; lia | apply ltu_swrap_trueZ; lia | apply ltu_sx32_falseZ; lia | apply ltu_sx32_trueZ; lia
        | apply (proj2 (Bool.negb_false_iff _)); cond_side_t
        | apply (proj2 (Bool.negb_true_iff _)); cond_side ])
with cond_side_t :=
  fastfirst (first [ noevar_assumption | apply ltu_trueZ; lia | apply eqb_trueZ; lia | apply lts_trueZ; lia
        | apply ltu_swrap_trueZ; lia | apply ltu_sx32_trueZ; lia
        | apply (proj2 (Bool.negb_true_iff _)); cond_side ]).
(* [comment removed for export] *)
Ltac bfalse :=
  lazymatch goal with |- evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
    replace c with false; [cbv iota| symmetry; cond_side] end.
Ltac btrue :=
  lazymatch goal with |- evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
    replace c with true; [cbv iota| symmetry; cond_side_t] end.
(* [comment removed for export] *)
Ltac bstep := lstep; try (lazymatch goal with |- evtF _ _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => first [bfalse | btrue] end).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma land_mask8 : forall y k, 0 <= y -> 0 <= k -> Z.land y (255 * 2^k) = ((y / 2^k) mod 256) * 2^k.
Proof.
  intros y k Hy Hk. apply Z.bits_inj'. intros n Hn.
  rewrite Z.land_spec.
  replace (255 * 2^k) with (Z.shiftl (Z.ones 8) k) by (rewrite Z.shiftl_mul_pow2 by lia; reflexivity).
  replace ((y / 2^k) mod 256 * 2^k) with (Z.shiftl ((Z.shiftr y k) mod 2^8) k)
    by (rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia; reflexivity).
  destruct (Z_lt_le_dec n k).
  - rewrite !Z.shiftl_spec_low by lia. apply Bool.andb_false_r.
  - rewrite !Z.shiftl_spec_high by lia.
    destruct (Z_lt_le_dec (n - k) 8).
    + rewrite Z.ones_spec_low, Z.mod_pow2_bits_low, Z.shiftr_spec by lia. rewrite Bool.andb_true_r. f_equal. lia.
    + rewrite Z.ones_spec_high, Z.mod_pow2_bits_high by lia. apply Bool.andb_false_r.
Qed.

Lemma land_65280 : forall y, 0 <= y -> Z.land y 65280 = ((y / 256) mod 256) * 256.
Proof. intros. change 65280 with (255 * 2^8). rewrite land_mask8 by lia. reflexivity. Qed.
Lemma land_16711680 : forall y, 0 <= y -> Z.land y 16711680 = ((y / 65536) mod 256) * 65536.
Proof. intros. change 16711680 with (255 * 2^16). rewrite land_mask8 by lia. reflexivity. Qed.



Lemma sx32_mod32 : forall x, 0 <= x < 2^32 -> bv_unsigned (sx32 (Z_to_bv 64 x)) mod 2^32 = x.
Proof.
  intros x Hx. rewrite unsigned_sx32 by lia. destruct (Z.ltb_spec x (2^31)).
  - apply Z.mod_small. lia.
  - Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Lemma le4_bswap32 : forall X x0 x1 x2 x3,
  0 <= X < 2^64 -> 0 <= x0 < 256 -> 0 <= x1 < 256 -> 0 <= x2 < 256 -> 0 <= x3 < 256 ->
  X mod 2^32 = x0 + 256 * x1 + 65536 * x2 + 16777216 * x3 ->
  le4 (Z_to_bv 64 (Z.lor (Z.lor ((Z.shiftl X 24) mod 18446744073709551616) ((Z.shiftl (Z.land X 65280) 8) mod 18446744073709551616))
                           (Z.lor (Z.land (Z.shiftr X 8) 65280) ((bv_swrap 32 (Z.shiftr (bv_wrap 32 X) 24)) mod 18446744073709551616))))
  = zbytes [x3; x2; x1; x0].
Proof.
  intros X x0 x1 x2 x3 HX H0 H1 H2 H3 HV.
  rewrite bv_wrap32_eq.
  rewrite !land_65280 by (try apply Z.shiftr_nonneg; lia).
  rewrite !Z.shiftl_mul_pow2, !Z.shiftr_div_pow2 by lia.
  assert (E1 : (X / 256) mod 256 = x1) by (Z.div_mod_to_equations; lia).
  assert (E2 : (X / 2^8 / 256) mod 256 = x2) by (Z.div_mod_to_equations; lia).
  assert (E3 : X mod 2^32 / 2^24 = x3) by (Z.div_mod_to_equations; lia).
  rewrite E1, E2, E3. rewrite (swrap32_small x3) by lia.
  rewrite (Z.mod_small x3) by lia.
  rewrite (Z.mod_small (x1 * 256 * 2^8)) by lia.
  rewrite (lor_add (x2 * 256) x3 8) by (try lia; Z.div_mod_to_equations; lia).
  rewrite (lor_add ((X * 2^24) mod 18446744073709551616) (x1 * 256 * 2^8) 24) by (try lia; Z.div_mod_to_equations; lia).
  rewrite (lor_add _ (x2 * 256 + x3) 16) by (try lia; Z.div_mod_to_equations; lia).
  apply le4_of_mod32; [reflexivity|]. cbn [zbytes map le_val]. rewrite !Z_to_bv_unsigned.
  unfold bv_wrap. change (bv_modulus 64) with (2^64). change (bv_modulus 8) with 256.
  rewrite !(Z.mod_small _ 256) by lia. Z.div_mod_to_equations. lia.
Qed.

Lemma word_range : forall w : word, 0 <= bv_unsigned w < 2^64.
Proof. intros w. pose proof (bv_unsigned_in_range 64 w) as H. unfold bv_modulus in H. cbn in H. cbn. lia. Qed.

(* [comment removed for export] *)
Lemma le2_of_mod16 : forall (v : word) (bs : list byte), length bs = 2%nat ->
  bv_unsigned v mod 2^16 = le_val (map bv_unsigned bs) -> le2 v = bs.
Proof.
  intros v bs Hl Hv. unfold le2.
  rewrite <- (Z_to_le_bytes_mod 2 _ 16) by (cbn; lia). change (2 ^ 16) with (2^16) in *. rewrite Hv.
  rewrite <- bytes_le_to_Z_le_val, <- Hl. apply Z_to_le_bytes_to_Z.
Qed.

Lemma le2_bswap16 : forall X x0 x1, 0 <= x0 < 256 -> 0 <= x1 < 256 -> X = x0 + 256 * x1 ->
  le2 (Z_to_bv 64 (Z.lor ((Z.shiftl X 8) mod 18446744073709551616) (Z.shiftr X 8))) = zbytes [x1; x0].
Proof.
  intros X x0 x1 H0 H1 ->.
  rewrite !Z.shiftl_mul_pow2, !Z.shiftr_div_pow2 by lia. change (2^8) with 256.
  replace ((x0 + 256 * x1) / 256) with x1 by (Z.div_mod_to_equations; lia).
  rewrite (Z.mod_small _ 18446744073709551616) by lia.
  rewrite (lor_add ((x0 + 256 * x1) * 256) x1 8); [| lia | change (2^8) with 256; lia | change (2^8) with 256; Z.div_mod_to_equations; lia].
  apply le2_of_mod16; [reflexivity|]. cbn [zbytes map le_val]. rewrite !Z_to_bv_unsigned.
  unfold bv_wrap. change (bv_modulus 64) with (2^64). change (bv_modulus 8) with 256.
  rewrite !(Z.mod_small _ 256) by lia. Z.div_mod_to_equations. lia.
Qed.
End TwB.
End PP_kitA.
