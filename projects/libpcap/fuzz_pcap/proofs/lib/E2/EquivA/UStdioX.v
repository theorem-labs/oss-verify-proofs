(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState ITree Nodes RelSpec Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad MSafe STree Malloc. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require KInv__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Inv. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Fuel__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_Inv LB_Quant. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_XferF__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Realloc2__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require ProgFullQ HeapFull Fmt StdioCore Stdio. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prog. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MSafe OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.MallocRe OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.KLink OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Inv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Addr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_Inv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_Quant OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_XferF__Spec.LB_StmtA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Realloc2__Spec.ProgFull OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.ProgFullQ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.HeapFull OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv Require SimW NodeSim ProgSim. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv Require SimStdio__Equiv. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv Require UFile UFrame. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.SimW OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.NodeSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.ProgSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.SimStdio__Equiv.SimStdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.SimStdio__Equiv.SimDriver OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.UFile OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.UFrame.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import NodesA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require Import MSafeX.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require USimX. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require NodeSimX__EquivA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require HeapIface. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require RelX. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require HeapI_S__EquivA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.USimX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.NodeSimX__EquivA.UFrameX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.NodeSimX__EquivA.DecodeX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.HeapIface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.NodeSimX__EquivA.NodeSimX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.RelX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.HeapI_S__EquivA.UNodesX.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Section WithCeil.
Context {CE : CEIL}.
Definition kapp (e : kfe) (bs : list byte) : kfe :=
  match k_data e with
  | Some d => kmove (Some (d ++ bs)) (k_off e + Z.of_nat (length bs)) e
  | None => e
  end.

(* [comment removed for export] *)
Definition kpos (e : kfe) (f : file_st) : kfe := kmove (k_data e) (k_off e - zlength (f_rbuf f)) e.

(* [comment removed for export] *)
Definition ktgt (eo : option kfe) (fl : list byte) (K : list kfe) : list kfe :=
  match eo with None => K | Some e => kset (kapp e fl) K end.
Definition etgt (eo : option kfe) (fl : list byte) : option kfe :=
  match eo with None => None | Some e => Some (kapp e fl) end.

#[using="Type"] Lemma kapp_fd e bs : k_fd (kapp e bs) = k_fd e. Proof. unfold kapp. destruct (k_data e); reflexivity. Qed.
#[using="Type"] Lemma kapp_kind e bs : k_kind (kapp e bs) = k_kind e. Proof. unfold kapp. destruct (k_data e); reflexivity. Qed.
#[using="Type"] Lemma kapp_path e bs : k_path (kapp e bs) = k_path e. Proof. unfold kapp. destruct (k_data e); reflexivity. Qed.
#[using="Type"] Lemma kapp_own e bs : k_own (kapp e bs) = k_own e. Proof. unfold kapp. destruct (k_data e); reflexivity. Qed.
#[using="Type"] Lemma kapp_kwr e bs : kwr e -> kwr (kapp e bs).
Proof. unfold kwr, kapp. destruct (k_data e) as [d|] eqn:ED; cbn; [| rewrite ED; auto]. intros [[KD _]|KN]; [left; split; [exact KD| discriminate]| right; exact KN]. Qed.
#[using="Type"] Lemma kapp_nil e : kapp e [] = e.
Proof. unfold kapp, kmove. destruct e as [? ? ? ? [d|] ?]; cbn; [rewrite app_nil_r, Z.add_0_r|]; reflexivity. Qed.
#[using="Type"] Lemma kapp_app e a b : kapp (kapp e a) b = kapp e (a ++ b).
Proof. unfold kapp, kmove. destruct e as [? ? ? ? [d|] ?]; cbn; [| reflexivity]. rewrite <- app_assoc, length_app. f_equal. lia. Qed.
#[using="Type"] Lemma kapp_off e bs : 0 <= k_off e -> 0 <= k_off (kapp e bs).
Proof. unfold kapp. destruct (k_data e); cbn; lia. Qed.

#[using="Type"] Lemma kset_kset e1 e2 K : k_fd e2 = k_fd e1 -> kset e2 (kset e1 K) = kset e2 K.
Proof.
  intros E. unfold kset. rewrite map_map. apply map_ext. intros x.
  destruct (Z.eqb_spec (k_fd x) (k_fd e1)) as [E1|N1].
  - rewrite <- E, Z.eqb_refl. rewrite E1, <- E, Z.eqb_refl. reflexivity.
  - replace (k_fd x =? k_fd e2) with false by (symmetry; apply Z.eqb_neq; congruence). reflexivity.
Qed.

#[using="Type"] Lemma In_kset_new e' K e : In e K -> k_fd e = k_fd e' -> In e' (kset e' K).
Proof. intros He E. apply In_kset. left. exists e. auto. Qed.

#[using="Type"] Lemma ktgt_app eo a b K : (forall e, eo = Some e -> In e K) -> ktgt (etgt eo a) b (ktgt eo a K) = ktgt eo (a ++ b) K.
Proof.
  intros _. destruct eo as [e|]; cbn [ktgt etgt]; [| reflexivity]. rewrite kset_kset by (rewrite !kapp_fd; reflexivity). rewrite kapp_app. reflexivity.
Qed.
#[using="Type"] Lemma etgt_app eo a b : etgt (etgt eo a) b = etgt eo (a ++ b).
Proof. destruct eo; cbn [etgt]; [rewrite kapp_app|]; reflexivity. Qed.
#[using="Type"] Lemma ktgt_nil eo K : (forall e, eo = Some e -> In e K) -> List.NoDup (map k_fd K) -> ktgt eo [] K = K.
Proof. intros HI ND. destruct eo as [e|]; cbn [ktgt]; [| reflexivity]. rewrite kapp_nil. apply kset_self; [exact (HI e eq_refl)| exact ND]. Qed.
#[using="Type"] Lemma etgt_nil eo : etgt eo [] = eo.
Proof. destruct eo; cbn [etgt]; [rewrite kapp_nil|]; reflexivity. Qed.
#[using="Type"] Lemma etgt_In eo fl K e' : (forall e, eo = Some e -> In e K) -> etgt eo fl = Some e' -> In e' (ktgt eo fl K).
Proof. intros HI E. destruct eo as [e|]; cbn [etgt ktgt] in *; [| discriminate]. injection E as <-. apply (In_kset_new _ K e); [exact (HI e eq_refl)| rewrite kapp_fd; reflexivity]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition wok (f : file_st) : Prop :=
  file_ok f /\ f_nowr f = false /\ f_rbuf f = [] /\ zlength (f_wbuf f) <= f_bufsize f /\ (f_wactive f = false -> f_wbuf f = []).

(* [comment removed for export] *)
Definition WT (eo : option kfe) (f : file_st) : Prop :=
  wok f /\
  match eo with
  | None => f_chan f = true
  | Some e => f_chan f = false /\ f_fd f = k_fd e /\ kwr e /\ f_bufsize f = BUFSIZ
  end.

#[using="Type"] Lemma WT_fshape e f : WT (Some e) f -> fshape f e.
Proof.
  intros ((F1 & F2 & F3 & F4 & F5) & C1 & C2 & C3 & C4). unfold fshape. split; [exact C1|]. split; [exact F1|]. split; [exact C2|].
  destruct C3 as [[E _]|E]; rewrite E; (split; [exact F2|]; split; [exact F3|]; split; [exact F4|]; split; [exact F5| exact C4]).
Qed.

#[using="Type"] Lemma fshape_WT e f : fshape f e -> kwr e -> WT (Some e) f.
Proof.
  intros (C1 & F1 & C2 & X) KD.
  assert (X' : f_nowr f = false /\ f_rbuf f = [] /\ zlength (f_wbuf f) <= f_bufsize f /\ (f_wactive f = false -> f_wbuf f = []) /\ f_bufsize f = BUFSIZ)
    by (destruct KD as [[E _]|E]; rewrite E in X; exact X).
  clear X. destruct X' as (F2 & F3 & F4 & W & B). split; [| split; [exact C1| split; [exact C2| split; [exact KD| exact B]]]]. split; [exact F1|]. split; [exact F2|]. split; [exact F3|]. split; [exact F4| exact W].
Qed.

(* [comment removed for export] *)
Definition wbud (eo : option kfe) (f : file_st) (extra : Z) : Prop :=
  match eo with
  | Some e => match k_data e with Some d => Z.of_nat (length d) + zlength (f_wbuf f) + extra <= FLEN | None => True end
  | None => True
  end.

#[using="Type"] Lemma wbud_mono eo f f' x x' : wbud eo f x -> zlength (f_wbuf f') + x' <= zlength (f_wbuf f) + x -> wbud eo f' x'.
Proof. unfold wbud. destruct eo as [e|]; [destruct (k_data e)|]; intros; lia. Qed.

#[using="Type"] Lemma wbud_tgt eo f f' fl x :
  wbud eo f x -> Z.of_nat (length fl) + zlength (f_wbuf f') <= zlength (f_wbuf f) + x -> wbud (etgt eo fl) f' 0.
Proof.
  unfold wbud, etgt. destruct eo as [e|]; [| auto]. unfold kapp. destruct (k_data e) as [d|] eqn:ED; cbn; [| rewrite ED; auto].
  rewrite length_app, Nat2Z.inj_add. intros; lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma zlength_nil {A} : zlength (@nil A) = 0. Proof. reflexivity. Qed.
#[using="Type"] Lemma zlength_app {A} (a b : list A) : zlength (a ++ b) = zlength a + zlength b.
Proof. unfold zlength. rewrite length_app. lia. Qed.
#[using="Type"] Lemma zlength_to_bytes l : Z.of_nat (length (to_bytes l)) = zlength l.
Proof. unfold to_bytes, zlength. rewrite length_map. reflexivity. Qed.
#[using="Type"] Lemma to_bytes_app a b : to_bytes (a ++ b) = to_bytes a ++ to_bytes b.
Proof. unfold to_bytes. apply map_app. Qed.
#[using="Type"] Lemma concat_map_to_bytes (l : list (list Z)) : concat (map to_bytes l) = to_bytes (concat l).
Proof. unfold to_bytes. rewrite concat_map. reflexivity. Qed.
#[using="Type"] Lemma zlength_nonneg {A} (l : list A) : 0 <= zlength l. Proof. unfold zlength. lia. Qed.
#[using="Type"] Lemma zlength_skipn {A} n (l : list A) : zlength (skipn n l) = Z.max 0 (zlength l - Z.of_nat n).
Proof. unfold zlength. rewrite length_skipn. lia. Qed.
#[using="Type"] Lemma zlength_firstn {A} n (l : list A) : zlength (firstn n l) = Z.min (Z.of_nat n) (zlength l).
Proof. unfold zlength. rewrite length_firstn. lia. Qed.
End WithCeil.


Ltac fsimp := cbn [f_fd f_chan f_bufsize f_nord f_nowr f_eof f_wactive f_wbuf f_rbuf f_lbf_nl f_stdoutw
                   set_w set_rbuf set_eof set_bufsize after_ioctl fdopen_file fst snd] in *.

Section WithCeil.
(* [comment removed for export] *)
#[using="Type"] Lemma WT_set_w eo f wb : WT eo f -> zlength wb <= f_bufsize f -> WT eo (set_w true wb f).
Proof.
  intros ((F1 & F2 & F3 & F4 & F5) & X) Hl. split; [| destruct eo; fsimp; exact X].
  unfold wok, file_ok in *; fsimp. repeat split; auto; try lia; try (intros; discriminate).
Qed.
#[using="Type"] Lemma WT_after_ioctl eo f : WT eo f -> WT eo (after_ioctl f).
Proof. intros ((F1 & F2 & F3 & F4 & F5) & X). split; [| destruct eo; fsimp; exact X]. unfold wok, file_ok in *; fsimp. repeat split; auto; lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Section UKdef.
Context {HG : Type}.
Definition UK (nx : N) (K : list kfe) (C : list (list byte * list byte))
    (g : libc_st hptr -> libc_st hptr) (W : libc_st hptr -> option hptr -> Prop) : PState HG hptr -> Model -> Prop :=
  fun s mo => FI nx K C (g (ps_libc s)) mo /\ W (ps_libc s) (ps_outfile s).

#[using="Type"] Lemma UK_stable nx K C g W : ustable (UK nx K C g W).
Proof. intros s s' mo mo' EL EO VM [H HW]. unfold UK. rewrite EL, EO. split; [exact (FI_vm_only _ _ _ _ _ _ VM H)| exact HW]. Qed.
End UKdef.

Section UStdio.
(* [comment removed for export] *)
Variable Uk : UKit.
#[local] Notation G := (uk_G Uk).
#[local] Notation nsafeP := (uk_nsafeP Uk).
#[local] Notation gstepP := (uk_gstepP Uk).
#[local] Notation GK_safe := (uk_GK_safe Uk).
#[local] Notation GK_step := (uk_GK_step Uk).
#[local] Notation HG := (uk_HG Uk).
#[local] Notation HC := (uk_HC Uk).
#[local] Notation HOG := (uk_HOG Uk).
#[local] Notation HOC := (uk_HOC Uk).
#[local] Notation eqbG := (uk_eqbG Uk).
#[local] Notation eqbC := (uk_eqbC Uk).
#[local] Notation segs := (uk_segs Uk).
#[local] Notation hi := (uk_hi Uk).
#[local] Notation PSG := (PState (uk_HG Uk) hptr).
#[local] Notation PSC := (PState (uk_HC Uk) hptr).
#[local] Notation npk := (npeek (uk_segs Uk)).
#[local] Notation relX := (USimX.relX (uk_G Uk) (PState (uk_HG Uk) hptr) (PState (uk_HC Uk) hptr)).
#[local] Notation usimS := (usimX (uk_nsafeP Uk) (uk_gstepP Uk) (npeek (uk_segs Uk))).
#[local] Notation RQ := (RelX.RQ (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk)).
#[local] Notation RX := (RelX.RX (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk)).
#[local] Notation RU := (RelX.RU (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk)).
#[local] Notation RX_RQ := (RelX.RX_RQ (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk)).
#[local] Notation RX_U := (RelX.RX_U (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk)).
#[local] Notation RQ_G := (RelX.RQ_G (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk)).
#[local] Notation RQ_C := (RelX.RQ_C (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk)).
#[local] Notation RQ_minvX := (RelX.RQ_minvX (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk)).
#[local] Notation RQ_halted := (RelX.RQ_halted (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk)).
#[local] Notation RQ_libc := (RelX.RQ_libc (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk)).
#[local] Notation RQ_outfile := (RelX.RQ_outfile (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk)).
#[local] Notation RQ_mq := (RelX.RQ_mq (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk)).
#[local] Notation RQ_lci := (RelX.RQ_lci (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk)).
#[local] Notation RQ_fresh := (RelX.RQ_fresh (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk)).
#[local] Notation RQ_toks_below := (RelX.RQ_toks_below (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk)).
#[local] Notation RQ_pot := (RelX.RQ_pot (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk)).
#[local] Notation blk_addr_range := (RelX.blk_addr_range (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk)).
#[local] Notation RQ_same_heap := (RelX.RQ_same_heap (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk)).
#[local] Notation RQ_libc_upd := (RelX.RQ_libc_upd (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk)).
#[local] Notation RQ_outfile_upd := (RelX.RQ_outfile_upd (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk)).
#[local] Notation RQ_xstep := (RelX.RQ_xstep (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk)).
#[local] Notation RQ_after := (RelX.RQ_after (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk)).
#[local] Definition ru_get := @RelX.ru_get (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HG Uk) (uk_HC Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk).
#[local] Definition ru_rd_lc := @RelX.ru_rd_lc (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HG Uk) (uk_HC Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk).
#[local] Definition ru_upd_lc := @RelX.ru_upd_lc (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HG Uk) (uk_HC Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk).
#[local] Definition ru_upd_outfile := @RelX.ru_upd_outfile (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HG Uk) (uk_HC Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk).
#[local] Definition ru_heap_op := @RelX.ru_heap_op (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HG Uk) (uk_HC Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk).
Arguments ru_heap_op {A}.
#[local] Definition ru_heap_opu := @RelX.ru_heap_opu (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HG Uk) (uk_HC Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk).
#[local] Definition ru_pmalloc := @RelX.ru_pmalloc (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HG Uk) (uk_HC Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk).
#[local] Definition ru_pcalloc := @RelX.ru_pcalloc (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HG Uk) (uk_HC Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk).
#[local] Definition ru_prealloc := @RelX.ru_prealloc (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HG Uk) (uk_HC Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk).
#[local] Definition ru_pfree := @RelX.ru_pfree (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HG Uk) (uk_HC Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk).
#[local] Definition ru_sys := @RelX.ru_sys (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HG Uk) (uk_HC Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk) (uk_GK_safe Uk).
Arguments ru_sys {A}.
#[local] Definition ru_read := @RelX.ru_read (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HG Uk) (uk_HC Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk) (uk_GK_safe Uk).
#[local] Definition ru_readv := @RelX.ru_readv (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HG Uk) (uk_HC Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk) (uk_GK_safe Uk).
#[local] Definition ru_exit := @RelX.ru_exit (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HG Uk) (uk_HC Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk) (uk_GK_safe Uk).
#[local] Definition ru_bind := @RelX.ru_bind (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HG Uk) (uk_HC Uk) (uk_segs Uk).
Arguments ru_bind {A B}.
#[local] Definition ru_bind2 := @RelX.ru_bind2 (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HG Uk) (uk_HC Uk) (uk_segs Uk).
Arguments ru_bind2 {A B A' B'}.
#[local] Definition ru_seq := @RelX.ru_seq (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HG Uk) (uk_HC Uk) (uk_segs Uk).
Arguments ru_seq {A B A' B'}.
#[local] Definition ru_ret := @RelX.ru_ret (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HG Uk) (uk_HC Uk) (uk_segs Uk).
Arguments ru_ret {A}.
#[local] Definition ru_post := @RelX.ru_post (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HG Uk) (uk_HC Uk) (uk_segs Uk).
Arguments ru_post {A}.
#[local] Definition ru_pre := @RelX.ru_pre (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HG Uk) (uk_HC Uk) (uk_segs Uk).
Arguments ru_pre {A B}.
#[local] Definition ru_munr := @RelX.ru_munr (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HG Uk) (uk_HC Uk) (uk_segs Uk).
Arguments ru_munr {A B}.
#[local] Definition ru_use := @RelX.ru_use (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HG Uk) (uk_HC Uk) (uk_segs Uk).
Arguments ru_use {A B}.
#[local] Definition ru_bind_retl := @RelX.ru_bind_retl (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HG Uk) (uk_HC Uk) (uk_segs Uk).
Arguments ru_bind_retl {A B}.
#[local] Definition usim_pure := @usimX_pure (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (PState (uk_HG Uk) hptr) (PState (uk_HC Uk) hptr) (npeek (uk_segs Uk)).
Arguments usim_pure {A B}.
#[local] Definition usim_exI := @usimX_exI (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (PState (uk_HG Uk) hptr) (PState (uk_HC Uk) hptr) (npeek (uk_segs Uk)).
Arguments usim_exI {A B X}.
#[local] Definition usim_ret := @usimX_ret (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (PState (uk_HG Uk) hptr) (PState (uk_HC Uk) hptr) (npeek (uk_segs Uk)).
Arguments usim_ret {A B}.
#[local] Definition usim_get := @usimX_get (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (PState (uk_HG Uk) hptr) (PState (uk_HC Uk) hptr) (npeek (uk_segs Uk)).
#[local] Definition usim_upd := @usimX_upd (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (PState (uk_HG Uk) hptr) (PState (uk_HC Uk) hptr) (npeek (uk_segs Uk)).
#[local] Definition usim_post := @usimX_post (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (PState (uk_HG Uk) hptr) (PState (uk_HC Uk) hptr) (npeek (uk_segs Uk)).
Arguments usim_post {A B}.
#[local] Definition usim_pre := @usimX_pre (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (PState (uk_HG Uk) hptr) (PState (uk_HC Uk) hptr) (npeek (uk_segs Uk)).
Arguments usim_pre {A B}.
#[local] Definition usim_conseq := @usimX_conseq (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (PState (uk_HG Uk) hptr) (PState (uk_HC Uk) hptr) (npeek (uk_segs Uk)).
Arguments usim_conseq {A B}.
#[local] Definition usim_munr := @usimX_munr (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (PState (uk_HG Uk) hptr) (PState (uk_HC Uk) hptr) (npeek (uk_segs Uk)).
Arguments usim_munr {A B}.
#[local] Definition usim_false := @usimX_false (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (PState (uk_HG Uk) hptr) (PState (uk_HC Uk) hptr) (npeek (uk_segs Uk)).
Arguments usim_false {A B}.
#[local] Definition usim_if := @usimX_if (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (PState (uk_HG Uk) hptr) (PState (uk_HC Uk) hptr) (npeek (uk_segs Uk)).
Arguments usim_if {A B}.
#[local] Definition usim_pointwise := @usimX_pointwise (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (PState (uk_HG Uk) hptr) (PState (uk_HC Uk) hptr) (npeek (uk_segs Uk)).
Arguments usim_pointwise {A B}.
#[local] Definition usim_sys := @usimX_sys (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (PState (uk_HG Uk) hptr) (PState (uk_HC Uk) hptr) (npeek (uk_segs Uk)).
Arguments usim_sys {A B}.
#[local] Definition usim_of_paths := @usimX_of_paths (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (PState (uk_HG Uk) hptr) (PState (uk_HC Uk) hptr) (npeek (uk_segs Uk)).
Arguments usim_of_paths {A B}.
#[local] Definition usim_bind := @usimX_bind (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (PState (uk_HG Uk) hptr) (PState (uk_HC Uk) hptr) (npeek (uk_segs Uk)) (npk_inh (uk_segs Uk)).
Arguments usim_bind {A B A' B'}.
#[local] Definition usim_seq := @usimX_seq (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (PState (uk_HG Uk) hptr) (PState (uk_HC Uk) hptr) (npeek (uk_segs Uk)) (npk_inh (uk_segs Uk)).
Arguments usim_seq {A B A' B'}.
#[local] Definition usim_bind_eq := @usimX_bind_eq (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (PState (uk_HG Uk) hptr) (PState (uk_HC Uk) hptr) (npeek (uk_segs Uk)) (npk_inh (uk_segs Uk)).
Arguments usim_bind_eq {A A' B'}.
#[local] Definition usim_loopV := @usimX_loopV (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (PState (uk_HG Uk) hptr) (PState (uk_HC Uk) hptr) (npeek (uk_segs Uk)) (npk_inh (uk_segs Uk)).
Arguments usim_loopV {X Y A B}.
(* [comment removed for export] *)
#[local] Notation framed I R := (framedX I R) (only parsing).
#[local] Definition usim_ND := fun A B p => @usimX_ND (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (PState (uk_HG Uk) hptr) (PState (uk_HC Uk) hptr) A B p.
Arguments usim_ND {A B}.
#[local] Notation RUK tm nx pt K C g W := (RX tm nx pt (UK nx K C g W)).

Implicit Types (tm : gmap N Z) (nx : N) (pt : Z) (K : list kfe) (C : list (list byte * list byte))
         (g : libc_st hptr -> libc_st hptr) (W : libc_st hptr -> option hptr -> Prop).

(* [comment removed for export] *)
#[using="Type"] Lemma ruk_use {A} tm nx pt K C g W (m : Monad.M PSG A) (m' : Monad.M PSC A) Q :
  (forall l mo, FI nx K C (g l) mo -> usimS (RUK tm nx pt K C g W) m m' Q) -> usimS (RUK tm nx pt K C g W) m m' Q.
Proof. intros H. apply ru_use. intros gh sG moG sC moC [_ [HF _]]. exact (H _ _ HF). Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma ruk_node {A} tm nx pt K C g W n (dec : resp -> option A) (Qf : A -> libc_st hptr -> Model -> Prop) :
  fdnodeX n -> fnode n dec (FI nx K C) Qf ->
  usimS (RUK tm nx pt K C g W) (msys n dec) (msys n dec)
        (eqpost (fun a => RX tm nx pt (fun s mo => Qf a (g (ps_libc s)) mo /\ W (ps_libc s) (ps_outfile s)))).
Proof. intros Hn HF. apply ru_sys; [exact Hn|]. apply (unode_lift n dec (FI nx K C) Qf g W). exact HF. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma ruk_nodeK {A} tm nx pt K C g W n (dec : resp -> option A) (Qf : A -> libc_st hptr -> Model -> Prop)
      (phi : A -> Prop) (K' : A -> list kfe) (C' : A -> list (list byte * list byte)) (g' : A -> libc_st hptr -> libc_st hptr) :
  fdnodeX n -> fnode n dec (FI nx K C) Qf ->
  (forall a l mo, Qf a (g l) mo -> phi a /\ FI nx (K' a) (C' a) (g' a l) mo) ->
  usimS (RUK tm nx pt K C g W) (msys n dec) (msys n dec)
        (eqpost (fun a => fun gh sG moG sC moC => phi a /\ RUK tm nx pt (K' a) (C' a) (g' a) W gh sG moG sC moC)).
Proof.
  intros Hn HF HQ. eapply ru_post; [apply (ruk_node tm nx pt K C g W n dec Qf Hn HF)|].
  intros a gh sG moG sC moC [HR [X HW]]. destruct (HQ _ _ _ X) as [H1 H2]. split; [exact H1|]. split; [exact HR|]. split; [exact H2| exact HW].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma ruk_nodeKM {A} tm nx pt K C g W n (dec : resp -> option A) (Qf : A -> libc_st hptr -> Model -> Prop)
      (phi : A -> Prop) (K' : A -> list kfe) (C' : A -> list (list byte * list byte)) (g' : A -> libc_st hptr -> libc_st hptr) (psi : A -> Model -> Prop) :
  fdnodeX n -> fnode n dec (FI nx K C) Qf ->
  (forall a l mo, Qf a (g l) mo -> phi a /\ FI nx (K' a) (C' a) (g' a l) mo /\ psi a mo) ->
  usimS (RUK tm nx pt K C g W) (msys n dec) (msys n dec)
        (eqpost (fun a => fun gh sG moG sC moC => phi a /\ RUK tm nx pt (K' a) (C' a) (g' a) W gh sG moG sC moC /\ psi a moG)).
Proof.
  intros Hn HF HQ. eapply ru_post; [apply (ruk_node tm nx pt K C g W n dec Qf Hn HF)|].
  intros a gh sG moG sC moC [HR [X HW]]. destruct (HQ _ _ _ X) as (H1 & H2 & H3). split; [exact H1|]. split; [| exact H3]. split; [exact HR|]. split; [exact H2| exact HW].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma ruk_nodeK_nd {A} p tm nx pt K C g W n (dec : resp -> option A) (Qf : A -> libc_st hptr -> Model -> Prop)
      (phi : A -> Prop) (K' : A -> list kfe) (C' : A -> list (list byte * list byte)) (g' : A -> libc_st hptr -> libc_st hptr) :
  fdnodeX n -> fnode n dec (fun l mo => FI nx K C l mo /\ ND p mo) Qf ->
  (forall a l mo, Qf a (g l) mo -> phi a /\ FI nx (K' a) (C' a) (g' a l) mo /\ ND p mo) ->
  usimS (framed (ND p) (RUK tm nx pt K C g W)) (msys n dec) (msys n dec)
        (eqpost (fun a => fun gh sG moG sC moC => phi a /\ framed (ND p) (RUK tm nx pt (K' a) (C' a) (g' a) W) gh sG moG sC moC)).
Proof.
  intros Hn HF HQ. eapply usim_conseq.
  - eapply (ru_sys tm nx pt (fun s mo => (FI nx K C (g (ps_libc s)) mo /\ ND p mo) /\ W (ps_libc s) (ps_outfile s))); [exact Hn|].
    apply (unode_lift n dec (fun l mo => FI nx K C l mo /\ ND p mo) Qf g W). exact HF.
  - intros gh sG moG sC moC [[HR [HFI HW]] HN]. split; [exact HR|]. split; [split; [exact HFI| exact HN]| exact HW].
  - intros a b gh sG moG sC moC [-> [HR [X HW]]]. destruct (HQ _ _ _ X) as (H1 & H2 & H3). split; [reflexivity|]. split; [exact H1|]. split; [| exact H3]. split; [exact HR|]. split; [exact H2| exact HW].
Qed.

#[using="Type"] Lemma ruk_ret {A} tm nx pt K C g W (a : A) (phi : A -> Prop) :
  phi a -> usimS (RUK tm nx pt K C g W) (mret a) (mret a) (eqpost (fun a => fun gh sG moG sC moC => phi a /\ RUK tm nx pt K C g W gh sG moG sC moC)).
Proof. intros Ha. apply ru_ret. intros; split; [exact Ha| assumption]. Qed.

#[using="Type"] Lemma ruk_munr {A} tm nx pt K C g W (m' : Monad.M PSC A) (Q : A -> A -> relX) :
  (forall l mo, FI nx K C (g l) mo -> False) -> usimS (RUK tm nx pt K C g W) munr m' Q.
Proof. intros H. apply ru_munr. intros ? ? ? ? ? [_ [HF _]]. exact (H _ _ HF). Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma ruk_bind {A B} tm nx pt K C g W (phi : A -> Prop) (K1 : A -> list kfe) (C1 : A -> list (list byte * list byte)) (g1 : A -> libc_st hptr -> libc_st hptr)
      (W1 : A -> libc_st hptr -> option hptr -> Prop) (m : Monad.M PSG A) (m' : Monad.M PSC A) (k : A -> Monad.M PSG B) (k' : A -> Monad.M PSC B) Q :
  usimS (RUK tm nx pt K C g W) m m' (eqpost (fun a => fun gh sG moG sC moC => phi a /\ RUK tm nx pt (K1 a) (C1 a) (g1 a) (W1 a) gh sG moG sC moC)) ->
  (forall a, phi a -> usimS (RUK tm nx pt (K1 a) (C1 a) (g1 a) (W1 a)) (k a) (k' a) Q) ->
  usimS (RUK tm nx pt K C g W) (mbind m k) (mbind m' k') Q.
Proof. intros H1 H2. eapply ru_bind; [exact H1|]. intros a. apply usim_pure. exact (H2 a). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition wpost tm nx pt K C g W (eo : option kfe) (f : file_st) (s : list Z) : file_st -> file_st -> relX :=
  eqpost (fun f' => fun gh sG moG sC moC =>
    exists fl, WT (etgt eo fl) f' /\ fl ++ to_bytes (f_wbuf f') = to_bytes (f_wbuf f) ++ to_bytes s
      /\ f_bufsize f' = f_bufsize f /\ f_fd f' = f_fd f /\ wbud (etgt eo fl) f' 0
      /\ RUK tm nx pt (ktgt eo fl K) C g W gh sG moG sC moC).

(* [comment removed for export] *)
Definition tgt_ok (eo : option kfe) (K : list kfe) : Prop := forall e, eo = Some e -> In e K.
#[using="Type"] Lemma tgt_ok_none K : tgt_ok None K. Proof. intros e; discriminate. Qed.
#[using="Type"] Lemma tgt_ok_some e K : In e K -> tgt_ok (Some e) K. Proof. intros He e' E; injection E as <-; exact He. Qed.
#[using="Type"] Lemma tgt_ok_tgt eo fl K : tgt_ok eo K -> tgt_ok (etgt eo fl) (ktgt eo fl K).
Proof. intros HI e' E. exact (etgt_In eo fl K e' HI E). Qed.

#[using="Type"] Lemma ru_wpost_ret tm nx pt K C g W eo f s f' :
  tgt_ok eo K ->
  WT eo f' -> to_bytes (f_wbuf f') = to_bytes (f_wbuf f) ++ to_bytes s -> f_bufsize f' = f_bufsize f -> f_fd f' = f_fd f -> wbud eo f' 0 ->
  usimS (RUK tm nx pt K C g W) (mret f') (mret f') (wpost tm nx pt K C g W eo f s).
Proof.
  intros HI W1 E B1 FD BU. apply ruk_use. intros l mo HF. apply ru_ret. intros gh sG moG sC moC HR. exists []. rewrite etgt_nil, ktgt_nil; [| exact HI| exact (proj1 (FI_KP _ _ _ _ _ HF))].
  cbn. auto 10.
Qed.

#[using="Type"] Lemma us_towrite tm nx pt K C g W eo f :
  tgt_ok eo K -> WT eo f -> f_wactive f = false -> wbud eo f 0 ->
  usimS (RUK tm nx pt K C g W) (towrite f) (towrite f)
        (eqpost (fun f' => fun gh sG moG sC moC => f' = set_w true [] (set_rbuf [] f) /\ RUK tm nx pt K C g W gh sG moG sC moC)).
Proof.
  intros HI HW HA HB. unfold towrite. pose proof HW as ((F1 & F2 & F3 & F4 & F5) & X). rewrite F2. apply ruk_ret. reflexivity.
Qed.

#[using="Type"] Lemma us_ensure_w tm nx pt K C g W eo f :
  tgt_ok eo K -> WT eo f ->
  usimS (RUK tm nx pt K C g W) (ensure_w f) (ensure_w f)
        (eqpost (fun f' => fun gh sG moG sC moC =>
           (WT eo f' /\ f_wbuf f' = f_wbuf f /\ f_wactive f' = true /\ f_bufsize f' = f_bufsize f /\ f_lbf_nl f' = f_lbf_nl f /\ f_stdoutw f' = f_stdoutw f /\ f_fd f' = f_fd f)
           /\ RUK tm nx pt K C g W gh sG moG sC moC)).
Proof.
  intros HI HW. unfold ensure_w. pose proof HW as ((F1 & F2 & F3 & F4 & F5) & X). destruct (f_wactive f) eqn:EA.
  - apply ruk_ret. split; [exact HW|]. repeat split; auto.
  - unfold towrite. rewrite F2. apply ruk_ret. rewrite (F5 eq_refl). split; [| fsimp; repeat split; reflexivity].
    split; [| destruct eo; fsimp; exact X]. unfold wok, file_ok in *; fsimp. repeat split; auto; try lia. unfold zlength; cbn; lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma concat_advance_iovs iovs cnt :
  (length iovs <= 2)%nat -> 0 <= cnt <= zlength (concat iovs) ->
  concat (advance_iovs iovs cnt) = skipn (Z.to_nat cnt) (concat iovs) /\ (length (advance_iovs iovs cnt) <= 2)%nat.
Proof.
  intros HL Hc. destruct iovs as [|b0 [|b1 [|b2 rest]]]; cbn in HL; [| | | lia].
  - cbn in *. rewrite skipn_nil. split; [reflexivity| lia].
  - cbn [advance_iovs concat] in *. rewrite !app_nil_r in *. unfold zlength in *.
    destruct (Z.ltb_spec (Z.of_nat (length b0)) cnt) as [LT|GE]; [lia|]. cbn. rewrite app_nil_r. split; [reflexivity| lia].
  - cbn [advance_iovs concat] in *. rewrite !app_nil_r in *. unfold zlength in *. rewrite length_app in Hc.
    destruct (Z.ltb_spec (Z.of_nat (length b0)) cnt) as [LT|GE].
    + cbn. rewrite app_nil_r. split; [| lia]. rewrite skipn_app. rewrite (skipn_all2 b0) by lia. cbn. f_equal. lia.
    + cbn. rewrite app_nil_r. split; [| lia]. rewrite skipn_app. replace (Z.to_nat cnt - length b0)%nat with 0%nat by lia. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma us_writev_loop tm nx pt K C g W eo f : forall fuel iovs rem,
  tgt_ok eo K -> WT eo f -> (length iovs <= 2)%nat -> rem = zlength (concat iovs) -> rem < 2^63 -> (Z.to_nat rem < fuel)%nat ->
  match eo with Some e => match k_data e with Some d => Z.of_nat (length d) + rem <= FLEN | None => True end | None => True end ->
  usimS (RUK tm nx pt K C g W) (writev_loop fuel f iovs rem) (writev_loop fuel f iovs rem)
        (eqpost (fun _ => RUK tm nx pt (ktgt eo (to_bytes (concat iovs)) K) C g W)).
Proof.
  induction fuel as [|fuel IH]; intros iovs rem HI HW HL Hrem Hlt Hfuel HB; [lia|]. cbn [writev_loop].
  pose proof HW as (WOK & X). pose proof (zlength_nonneg (concat iovs)) as NN.
  assert (LEN : Z.of_nat (length (concat (map to_bytes iovs))) = rem) by (rewrite concat_map_to_bytes, zlength_to_bytes; exact (eq_sym Hrem)).
  unfold wnode, wdec. destruct eo as [e|].
  - (* [comment removed for export] *)
    destruct X as (C1 & C2 & C3 & C4). rewrite C1, C2. rewrite <- LEN.
    eapply ruk_bind with (W1 := fun _ => W).
    + eapply ruk_nodeK with (phi := fun a => a = Z.of_nat (length (concat (map to_bytes iovs))))
        (K' := fun _ => kset (kapp e (to_bytes (concat iovs))) K) (C' := fun _ => C) (g' := fun _ => g);
        [exact I| apply (fn_writevf nx K C e (map to_bytes iovs) (HI e eq_refl) C3)|].
      * rewrite LEN. destruct (k_data e); lia.
      * intros a l mo [Ha HF]. split; [exact Ha|]. rewrite concat_map_to_bytes in HF. cbn beta.
        unfold kapp. destruct (k_data e) as [d|]; [exact HF|]. rewrite kset_self; [exact HF| exact (HI e eq_refl)| exact (proj1 (FI_KP _ _ _ _ _ HF))].
    + intros a ->. cbn beta. rewrite Z.eqb_refl. cbn [ktgt]. apply ru_ret. intros; assumption.
  - (* [comment removed for export] *)
    rewrite X. rewrite <- LEN. eapply ruk_bind with (W1 := fun _ => W).
    + eapply ruk_nodeK with (phi := fun k => (length (concat (map to_bytes iovs)) = 0%nat /\ k = 0) \/ 1 <= k <= Z.of_nat (length (concat (map to_bytes iovs))))
        (K' := fun _ => K) (C' := fun _ => C) (g' := fun _ => g); [exact I| apply (fn_writev nx K C (f_fd f) (map to_bytes iovs)); lia|].
      intros k l mo [HF Hk]. cbn beta. exact (conj Hk HF).
    + intros k Hk. cbn beta. cbn [ktgt]. rewrite !LEN in Hk |- *. destruct (Z.eqb_spec k rem) as [->|NE]; [apply ru_ret; intros; assumption|].
      assert (HK : 1 <= k < rem) by lia.
      destruct (concat_advance_iovs iovs k HL ltac:(lia)) as [CA LA].
      eapply usim_post; [apply (IH (advance_iovs iovs k) (rem - k) HI HW LA); [rewrite CA, zlength_skipn; lia| lia| lia| exact I]|].
      intros a b ? ? ? ? ? [-> H]. split; [reflexivity| exact H].
Qed.

#[using="Type"] Lemma us_stdio_write tm nx pt K C g W eo f s :
  tgt_ok eo K -> WT eo f -> zlength s < 2^61 -> wbud eo f (zlength s) ->
  usimS (RUK tm nx pt K C g W) (stdio_write f s) (stdio_write f s)
        (eqpost (fun f' => fun gh sG moG sC moC => f' = set_w true [] f /\ RUK tm nx pt (ktgt eo (to_bytes (f_wbuf f ++ s)) K) C g W gh sG moG sC moC)).
Proof.
  intros HI HW Hs HB. unfold stdio_write. cbv zeta. pose proof HW as ((F1 & F2 & F3 & F4 & F5) & X). unfold file_ok in F1.
  pose proof (zlength_nonneg (f_wbuf f)) as N1. pose proof (zlength_nonneg s) as N2.
  set (iovs := match f_wbuf f with [] => [s] | _ :: _ => [f_wbuf f; s] end).
  assert (CI : concat iovs = f_wbuf f ++ s /\ (length iovs <= 2)%nat).
  { subst iovs. destruct (f_wbuf f); cbn; rewrite ?app_nil_r; split; reflexivity || lia. }
  destruct CI as [CI LI].
  eapply ru_bind.
  - eapply usim_post; [apply (us_writev_loop tm nx pt K C g W eo f (S (Z.to_nat (zlength (f_wbuf f) + zlength s))) iovs (zlength (f_wbuf f) + zlength s) HI HW LI)|].
    + rewrite CI, zlength_app. reflexivity.
    + lia.
    + lia.
    + unfold wbud in HB. destruct eo as [e|]; [destruct (k_data e)|]; try exact I. lia.
    + intros a b ? ? ? ? ? [-> H]. split; [reflexivity|]. exact (conj I H).
  - intros []. apply usim_pure. intros _. rewrite CI. apply ru_ret. intros; split; [reflexivity| assumption].
Qed.

(* [comment removed for export] *)
Definition wfn_post tm nx pt K C g W eo f s : file_st -> file_st -> relX :=
  eqpost (fun f' => fun gh sG moG sC moC =>
    (WT (etgt eo (to_bytes (f_wbuf f ++ s))) f' /\ f_wbuf f' = [] /\ f_wactive f' = true /\ f_bufsize f' = f_bufsize f /\ f_fd f' = f_fd f /\ f_stdoutw f' = false
     /\ (f_lbf_nl f' = true -> f_lbf_nl f = true))
    /\ RUK tm nx pt (ktgt eo (to_bytes (f_wbuf f ++ s)) K) C g W gh sG moG sC moC).

#[using="Type"] Lemma WT_tgt eo f fl : WT eo f -> WT (etgt eo fl) f.
Proof. intros [WOK X]. split; [exact WOK|]. destruct eo as [e|]; cbn; [rewrite kapp_fd; destruct X as (X1 & X2 & X3 & X4); exact (conj X1 (conj X2 (conj (kapp_kwr e fl X3) X4)))| exact X]. Qed.

#[using="Type"] Lemma us_file_writefn tm nx pt K C g W eo f s :
  tgt_ok eo K -> WT eo f -> zlength s < 2^61 -> wbud eo f (zlength s) ->
  usimS (RUK tm nx pt K C g W) (file_writefn f s) (file_writefn f s) (wfn_post tm nx pt K C g W eo f s).
Proof.
  intros HI HW Hs HB. unfold file_writefn. pose proof HW as ((F1 & F2 & F3 & F4 & F5) & X).
  destruct (f_stdoutw f) eqn:ESW.
  - eapply ruk_bind with (W1 := fun _ => W).
    + eapply ruk_nodeK with (K' := fun _ => K) (C' := fun _ => C) (g' := fun _ => g); [exact I| apply fn_ioctl|]. intros a l mo [HF Ha]. exact (conj Ha HF).
    + intros r [e ->]. cbn beta. eapply ru_post; [apply (us_stdio_write tm nx pt K C g W eo (after_ioctl f) s HI (WT_after_ioctl _ _ HW) Hs)|].
      { unfold wbud in *; fsimp; exact HB. }
      intros f' gh sG moG sC moC [-> H]. fsimp. split; [| exact H]. split; [| fsimp; repeat split; auto; intros; discriminate].
      apply WT_set_w; [apply WT_tgt; apply WT_after_ioctl; exact HW| fsimp; unfold zlength, file_ok in *; cbn; lia].
  - eapply ru_post; [apply (us_stdio_write tm nx pt K C g W eo f s HI HW Hs HB)|].
    intros f' gh sG moG sC moC [-> H]. split; [| exact H]. fsimp. split; [| repeat split; auto].
    apply WT_set_w; [apply WT_tgt; exact HW| unfold zlength, file_ok in *; cbn; lia].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma ruk_bindX {A B X} tm nx pt K C g W (phi : X -> A -> Prop) (K1 : X -> A -> list kfe) (C1 : X -> A -> list (list byte * list byte))
      (g1 : X -> A -> libc_st hptr -> libc_st hptr) (W1 : X -> A -> libc_st hptr -> option hptr -> Prop) (m : Monad.M PSG A) (m' : Monad.M PSC A) (k : A -> Monad.M PSG B) (k' : A -> Monad.M PSC B) Q :
  usimS (RUK tm nx pt K C g W) m m' (eqpost (fun a => fun gh sG moG sC moC => exists x, phi x a /\ RUK tm nx pt (K1 x a) (C1 x a) (g1 x a) (W1 x a) gh sG moG sC moC)) ->
  (forall x a, phi x a -> usimS (RUK tm nx pt (K1 x a) (C1 x a) (g1 x a) (W1 x a)) (k a) (k' a) Q) ->
  usimS (RUK tm nx pt K C g W) (mbind m k) (mbind m' k') Q.
Proof.
  intros H1 H2. eapply ru_bind; [exact H1|]. intros a.
  eapply usim_pre; [eapply usim_exI; intros x; apply usim_pure; exact (H2 x a)|].
  intros gh sG moG sC moC (x & Hx & HR). exists x. exact (conj Hx HR).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma after_last_nl_range s : 0 <= after_last_nl s <= zlength s.
Proof.
  unfold after_last_nl.
  assert (G : forall (l : list (Z * Z)) acc n, Forall (fun ib => 0 <= fst ib < n) l -> 0 <= acc <= n ->
             0 <= fold_left (fun acc ib => if snd ib =? 10 then fst ib + 1 else acc) l acc <= n).
  { induction l as [|ib l IH]; intros acc n HF Ha; cbn; [exact Ha|]. apply Forall_cons_iff in HF as [H1 HF].
    apply IH; [exact HF|]. destruct (snd ib =? 10); lia. }
  apply G; [| unfold zlength; lia].
  apply Forall_forall. intros [i c] Hin. apply in_combine_l in Hin. apply in_map_iff in Hin as (k & E & Hk). apply in_seq in Hk. cbn. unfold zlength. lia.
Qed.

#[using="Type"] Lemma us_fwritex tm nx pt K C g W eo f s :
  tgt_ok eo K -> WT eo f -> zlength s < 2^61 -> wbud eo f (zlength s) ->
  usimS (RUK tm nx pt K C g W) (fwritex f s) (fwritex f s) (wpost tm nx pt K C g W eo f s).
Proof.
  intros HI HW Hs HB. unfold fwritex. pose proof (zlength_nonneg s) as NS. pose proof (zlength_nonneg (f_wbuf f)) as NW.
  eapply ruk_bind with (W1 := fun _ => W) (K1 := fun _ => K) (C1 := fun _ => C) (g1 := fun _ => g); [apply (us_ensure_w tm nx pt K C g W eo f HI HW)|].
  intros f1 (W1 & EB & EA & EBS & ELB & ESW & EFD). cbn beta.
  pose proof W1 as ((F1 & F2 & F3 & F4 & F5) & X1). unfold file_ok in F1.
  assert (HB1 : wbud eo f1 (zlength s)) by (eapply wbud_mono; [exact HB| rewrite EB; lia]).
  destruct (Z.ltb_spec (f_bufsize f1 - zlength (f_wbuf f1)) (zlength s)) as [LT|GE].
  - eapply ru_post; [apply (us_file_writefn tm nx pt K C g W eo f1 s HI W1 Hs HB1)|].
    intros f' gh sG moG sC moC ((W' & EB' & EA' & EBS' & EFD' & _) & H). exists (to_bytes (f_wbuf f1 ++ s)).
    rewrite EB' in *. rewrite EB in *. split; [exact W'|]. split; [cbn [to_bytes map]; rewrite app_nil_r, to_bytes_app; reflexivity|]. split; [congruence|]. split; [congruence|].
    split; [| exact H]. eapply wbud_tgt; [exact HB|]. rewrite EB', zlength_to_bytes, zlength_app. unfold zlength in *. cbn [length] in *. lia.
  - destruct (f_lbf_nl f1) eqn:EL.
    + pose proof (after_last_nl_range s) as HIR. set (i := after_last_nl s) in *.
      destruct (Z.ltb_spec 0 i) as [IP|IZ].
      * eapply ruk_bind with (W1 := fun _ => W) (K1 := fun _ => ktgt eo (to_bytes (f_wbuf f1 ++ firstn (Z.to_nat i) s)) K) (C1 := fun _ => C) (g1 := fun _ => g).
        { eapply ru_post; [apply (us_file_writefn tm nx pt K C g W eo f1 (firstn (Z.to_nat i) s) HI W1)|].
          - rewrite zlength_firstn. lia.
          - eapply wbud_mono; [exact HB1|]. rewrite zlength_firstn. lia.
          - intros f2 gh sG moG sC moC [P2 H2]. exact (conj P2 H2). }
        intros f2 (W2 & EB2 & EA2 & EBS2 & EFD2 & _). cbn beta. apply ruk_use. intros l mo HF.
        apply ru_ret. intros gh sG moG sC moC HR. exists (to_bytes (f_wbuf f1 ++ firstn (Z.to_nat i) s)). rewrite EB in *. fsimp.
        split.
        { apply WT_set_w; [exact W2|]. rewrite EBS2, EB2. cbn [app]. rewrite zlength_skipn. lia. }
        split; [rewrite EB2; cbn [app]; rewrite !to_bytes_app, <- app_assoc, <- to_bytes_app, firstn_skipn; reflexivity|].
        split; [congruence|]. split; [congruence|]. split; [| exact HR].
        eapply wbud_tgt; [exact HB|]. rewrite zlength_to_bytes, !zlength_app, EB2, zlength_firstn, zlength_skipn. unfold zlength in *. cbn [length Z.of_nat] in *. lia.
      * rewrite EB in *. apply ru_bind_retl. apply (ru_wpost_ret tm nx pt K C g W eo f s); [exact HI| | | | |]; fsimp; rewrite ?EB in *.
        -- apply WT_set_w; [exact W1|]. rewrite zlength_app, zlength_skipn. lia.
        -- replace (Z.to_nat i) with 0%nat by lia. cbn [skipn]. apply to_bytes_app.
        -- exact EBS.
        -- exact EFD.
        -- eapply wbud_mono; [exact HB|]. fsimp. rewrite zlength_app, zlength_skipn. lia.
    + rewrite EB in *. apply (ru_wpost_ret tm nx pt K C g W eo f s); [exact HI| | | | |]; fsimp.
      * apply WT_set_w; [exact W1|]. rewrite zlength_app. lia.
      * apply to_bytes_app.
      * exact EBS.
      * exact EFD.
      * eapply wbud_mono; [exact HB|]. fsimp. rewrite zlength_app. lia.
Qed.

#[using="Type"] Lemma us_fwrite_file tm nx pt K C g W eo f s :
  tgt_ok eo K -> WT eo f -> zlength s < 2^61 -> wbud eo f (zlength s) ->
  usimS (RUK tm nx pt K C g W) (fwrite_file f s) (fwrite_file f s) (wpost tm nx pt K C g W eo f s).
Proof. intros. unfold fwrite_file. apply us_fwritex; assumption. Qed.

#[using="Type"] Lemma us_out_pieces tm nx pt C g W ps : forall eo K f,
  tgt_ok eo K -> WT eo f -> Forall (fun p => zlength p < 2^61) ps -> wbud eo f (zlength (concat ps)) ->
  usimS (RUK tm nx pt K C g W) (out_pieces f ps) (out_pieces f ps) (wpost tm nx pt K C g W eo f (concat ps)).
Proof.
  induction ps as [|p ps IH]; intros eo K f HI HW HF HB; cbn [out_pieces].
  - apply (ru_wpost_ret tm nx pt K C g W eo f (concat [])); [exact HI| exact HW| cbn; rewrite app_nil_r; reflexivity| reflexivity| reflexivity| eapply wbud_mono; [exact HB| unfold zlength; cbn; lia]].
  - apply Forall_cons_iff in HF as [Hp HF]. pose proof (zlength_nonneg p). pose proof (zlength_nonneg (concat ps)). change (concat (p :: ps)) with (p ++ concat ps) in *.
    eapply (ruk_bindX tm nx pt K C g W (fun fl f' => WT (etgt eo fl) f' /\ fl ++ to_bytes (f_wbuf f') = to_bytes (f_wbuf f) ++ to_bytes p /\ f_bufsize f' = f_bufsize f /\ f_fd f' = f_fd f /\ wbud (etgt eo fl) f' (zlength (concat ps)))
              (fun fl _ => ktgt eo fl K) (fun _ _ => C) (fun _ _ => g) (fun _ _ => W)).
    + eapply ru_post; [apply (us_fwritex tm nx pt K C g W eo f p HI HW Hp)|].
      { eapply wbud_mono; [exact HB|]. rewrite zlength_app. lia. }
      intros f1 gh sG moG sC moC (fl & W1 & E1 & B1 & FD1 & BU1 & H1). exists fl. split; [| exact H1]. split; [exact W1|]. split; [exact E1|]. split; [exact B1|]. split; [exact FD1|].
      unfold wbud in *. destruct eo as [e|]; cbn [etgt] in *; [| exact I]. unfold kapp in *. destruct (k_data e) as [d|] eqn:ED; cbn in *; [| rewrite ED; exact I].
      apply (f_equal (@length byte)) in E1. rewrite length_app in E1. rewrite length_app in E1. rewrite length_app.
      pose proof (zlength_to_bytes (f_wbuf f1)). pose proof (zlength_to_bytes (f_wbuf f)). pose proof (zlength_to_bytes p). rewrite zlength_app in HB. lia.
    + intros fl f1 (W1 & E1 & B1 & FD1 & BU1). cbn beta.
      eapply ru_post; [apply (IH (etgt eo fl) (ktgt eo fl K) f1 (tgt_ok_tgt eo fl K HI) W1 HF BU1)|].
      intros f' gh sG moG sC moC (fl2 & W2 & E2 & B2 & FD2 & BU2 & H2). exists (fl ++ fl2).
      rewrite etgt_app in W2, BU2. rewrite ktgt_app in H2 by exact HI.
      split; [exact W2|]. split; [| split; [congruence| split; [congruence| split; [exact BU2| exact H2]]]].
      rewrite to_bytes_app, <- app_assoc, E2, app_assoc, E1, <- app_assoc. reflexivity.
Qed.

#[using="Type"] Lemma us_vfprintf tm nx pt K C g W eo f ps :
  tgt_ok eo K -> WT eo f -> Forall (fun p => zlength p < 2^61) ps -> wbud eo f (zlength (concat ps)) ->
  usimS (RUK tm nx pt K C g W) (vfprintf f ps) (vfprintf f ps) (wpost tm nx pt K C g W eo f (concat ps)).
Proof.
  intros HI HW HF HB. unfold vfprintf. pose proof HW as ((F1 & F2 & F3 & F4 & F5) & X). pose proof (zlength_nonneg (concat ps)) as NC.
  destruct (Z.eqb_spec (f_bufsize f) 0) as [EZ|NZ].
  - destruct eo as [e|]. { exfalso. destruct X as (_ & _ & _ & B). unfold BUFSIZ in B. lia. }
    assert (EWB : f_wbuf f = []). { destruct (f_wbuf f) eqn:E; [reflexivity|]. exfalso. unfold zlength in F4. cbn in F4. lia. }
    assert (W0 : WT None (set_w false [] (set_bufsize INTERNAL_BUFSIZ f))).
    { split; [| fsimp; exact X]. unfold wok, file_ok, INTERNAL_BUFSIZ in *; fsimp. unfold zlength; cbn. repeat split; auto; lia. }
    eapply ruk_bind with (W1 := fun _ => W) (K1 := fun _ => K) (C1 := fun _ => C) (g1 := fun _ => g); [apply (us_towrite tm nx pt K C g W None _ HI W0); [reflexivity| exact I]|].
    intros f1 ->. cbn beta.
    assert (W1 : WT None (set_w true [] (set_rbuf [] (set_w false [] (set_bufsize INTERNAL_BUFSIZ f))))).
    { split; [| fsimp; exact X]. unfold wok, file_ok, INTERNAL_BUFSIZ in *; fsimp. unfold zlength; cbn. repeat split; auto; try lia; try (intros; discriminate). }
    eapply (ruk_bindX tm nx pt K C g W _ (fun fl _ => ktgt None fl K) (fun _ _ => C) (fun _ _ => g) (fun _ _ => W)).
    + eapply ru_post; [apply (us_out_pieces tm nx pt C g W ps None K _ HI W1 HF); exact I|].
      intros f2 gh sG moG sC moC (fl & P1 & P2 & P3 & P4 & P5 & H). exists fl. exact (conj (conj P1 (conj P2 (conj P3 (conj P4 P5)))) H).
    + intros fl f2 (W2 & E2 & B2 & FD2 & BU2). cbn beta. fsimp. cbn [ktgt etgt] in *.
      eapply ruk_bind with (W1 := fun _ => W) (K1 := fun _ => K) (C1 := fun _ => C) (g1 := fun _ => g).
      { eapply ru_post; [apply (us_file_writefn tm nx pt K C g W None f2 [] (tgt_ok_none K) W2); [unfold zlength; cbn; lia| exact I]|].
        intros f3 ? ? ? ? ? [P3 H3]. exact (conj P3 H3). }
      intros f3 (W3 & EB3 & EA3 & EBS3 & EFD3 & _). cbn beta. cbn [ktgt etgt] in *. rewrite ?app_nil_r in *.
      apply ru_ret. intros gh sG moG sC moC HR. exists (fl ++ to_bytes (f_wbuf f2)). fsimp.
      split.
      { split; [| exact (proj2 W3)]. destruct W3 as [(G1 & G2 & G3 & G4 & G5) _]. unfold wok, file_ok in *; fsimp. unfold zlength; cbn. repeat split; auto; lia. }
      split; [cbn [to_bytes map]; rewrite app_nil_r, E2, EWB; reflexivity|].
      split; [symmetry; exact EZ|]. split; [congruence|]. split; [exact I| exact HR].
  - eapply ruk_bind with (W1 := fun _ => W) (K1 := fun _ => K) (C1 := fun _ => C) (g1 := fun _ => g); [apply (us_ensure_w tm nx pt K C g W eo f HI HW)|].
    intros f1 (W1 & EB & EA & EBS & ELB & ESW & EFD). cbn beta.
    eapply ru_post; [apply (us_out_pieces tm nx pt C g W ps eo K f1 HI W1 HF); eapply wbud_mono; [exact HB| rewrite EB; lia]|].
    intros f' gh sG moG sC moC (fl & W' & E' & B' & FD' & BU' & H'). exists fl. rewrite EB in E'.
    split; [exact W'|]. split; [exact E'|]. split; [congruence|]. split; [congruence|]. split; [exact BU'| exact H'].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition pos (e : kfe) (f : file_st) : Z := k_off e - zlength (f_rbuf f).
(* [comment removed for export] *)
Definition kat (e : kfe) (off : Z) : kfe := kmove (k_data e) off e.

#[using="Type"] Lemma kat_fd e off : k_fd (kat e off) = k_fd e. Proof. reflexivity. Qed.
#[using="Type"] Lemma kat_self e : kat e (k_off e) = e. Proof. destruct e; reflexivity. Qed.
#[using="Type"] Lemma kat_kat e a b : kat (kat e a) b = kat e b. Proof. destruct e; reflexivity. Qed.

(* [comment removed for export] *)
Definition dsl (d : list byte) (p n : Z) : list Z := of_bytes (firstn (Z.to_nat n) (skipn (Z.to_nat p) d)).

#[using="Type"] Lemma firstn_add_skipn {A} (a b : nat) (l : list A) : firstn (a + b) l = firstn a l ++ firstn b (skipn a l).
Proof. revert l; induction a as [|a IH]; intros [|x l]; cbn; [reflexivity| reflexivity| now rewrite firstn_nil| now rewrite IH]. Qed.
#[using="Type"] Lemma skipn_add {A} (a b : nat) (l : list A) : skipn (a + b) l = skipn b (skipn a l).
Proof. revert l; induction a as [|a IH]; intros [|x l]; cbn; [reflexivity| reflexivity| now rewrite skipn_nil| apply IH]. Qed.
#[using="Type"] Lemma firstn_length_firstn {A} (c : nat) (l : list A) : firstn (length (firstn c l)) l = firstn c l.
Proof. revert l; induction c as [|c IH]; intros [|x l]; cbn; [reflexivity| reflexivity| reflexivity| now rewrite IH]. Qed.

#[using="Type"] Lemma dsl_0 d p : dsl d p 0 = []. Proof. reflexivity. Qed.
#[using="Type"] Lemma dsl_nil' d p : dsl d p (zlength (@nil Z)) = []. Proof. reflexivity. Qed.
#[using="Type"] Lemma dsl_app d p a b : 0 <= p -> 0 <= a -> 0 <= b -> dsl d p a ++ dsl d (p + a) b = dsl d p (a + b).
Proof.
  intros Hp Ha Hb. unfold dsl, of_bytes. rewrite <- map_app. f_equal. rewrite (Z2Nat.inj_add a b), firstn_add_skipn by lia. f_equal. f_equal.
  rewrite (Z2Nat.inj_add p a) by lia. apply skipn_add.
Qed.
#[using="Type"] Lemma dsl_firstn d p n k : 0 <= k <= n -> firstn (Z.to_nat k) (dsl d p n) = dsl d p k.
Proof. intros Hk. unfold dsl, of_bytes. rewrite firstn_map. f_equal. rewrite firstn_firstn. f_equal. lia. Qed.
#[using="Type"] Lemma dsl_skipn d p n k : 0 <= p -> 0 <= k <= n -> skipn (Z.to_nat k) (dsl d p n) = dsl d (p + k) (n - k).
Proof.
  intros Hp Hk. unfold dsl, of_bytes. rewrite skipn_map. f_equal. rewrite skipn_firstn_comm. rewrite (Z2Nat.inj_add p k), skipn_add by lia. f_equal. lia.
Qed.
(* [comment removed for export] *)
#[using="Type"] Lemma dsl_cat d p q a r1 r2 : r1 = dsl d p a -> r2 = dsl d q (zlength r2) -> a = zlength r1 -> q = p + a -> 0 <= p -> r1 ++ r2 = dsl d p (a + zlength r2).
Proof.
  intros H1 H2 Ha Hq Hp. pose proof (zlength_nonneg r1). pose proof (zlength_nonneg r2). rewrite H2 at 1. rewrite H1, Hq. apply dsl_app; lia.
Qed.

(* [comment removed for export] *)
Definition RT (e : kfe) (d : list byte) (f : file_st) : Prop :=
  fshape f e /\ k_kind e = KR /\ k_data e = Some d /\ 0 <= zlength (f_rbuf f) <= k_off e /\ k_off e <= Z.of_nat (length d)
  /\ (f_eof f = true -> pos e f = Z.of_nat (length d))
  /\ f_rbuf f = dsl d (k_off e - zlength (f_rbuf f)) (zlength (f_rbuf f)).   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition rpost tm nx pt K C g W (e : kfe) (d : list byte) (f : file_st) (n : Z) : (list Z * file_st) -> (list Z * file_st) -> relX :=
  eqpost (fun r => fun gh sG moG sC moC =>
    let bs := fst r in let f' := snd r in let e' := kat e (pos e f + zlength bs + zlength (f_rbuf f')) in
    zlength bs <= n /\ bs = dsl d (pos e f) (zlength bs) /\ RT e' d f' /\ pos e' f' = pos e f + zlength bs /\ (zlength bs < n -> pos e' f' = Z.of_nat (length d))
    /\ f_bufsize f' = f_bufsize f
    /\ RUK tm nx pt (kset e' K) C g W gh sG moG sC moC).

#[using="Type"] Lemma us_toread tm nx pt K C g W e d f :
  RT e d f -> f_rbuf f = [] ->
  usimS (RUK tm nx pt K C g W) (toread f) (toread f)
        (eqpost (fun r => fun gh sG moG sC moC => r = (f_eof f, set_rbuf [] (set_w false [] f)) /\ RUK tm nx pt K C g W gh sG moG sC moC)).
Proof.
  intros (S1 & S2 & S3 & S4 & S5 & S6 & S7) HR. unfold toread. destruct S1 as (C1 & F1 & C2 & X). rewrite S2 in X. destruct X as (N1 & WB & WA).
  rewrite WB. apply ru_bind_retl. fsimp. rewrite N1. apply ruk_ret. reflexivity.
Qed.

#[using="Type"] Lemma of_bytes_length l : zlength (of_bytes l) = Z.of_nat (length l).
Proof. unfold of_bytes, zlength. rewrite length_map. reflexivity. Qed.

#[using="Type"] Lemma file_read_short d off count :
  0 <= off <= Z.of_nat (length d) -> 0 <= count < 2^64 -> Z.of_nat (length d) < 2^64 ->
  Z.of_nat (length (file_read d (Z_to_bv 64 off) (Z_to_bv 64 count))) <= count /\
  (Z.of_nat (length (file_read d (Z_to_bv 64 off) (Z_to_bv 64 count))) < count -> off + Z.of_nat (length (file_read d (Z_to_bv 64 off) (Z_to_bv 64 count))) = Z.of_nat (length d)) /\
  off + Z.of_nat (length (file_read d (Z_to_bv 64 off) (Z_to_bv 64 count))) <= Z.of_nat (length d).
Proof.
  intros Ho Hc Hd. rewrite file_read_unguarded, length_firstn, length_skipn. unfold word_to_nat. rewrite !unsigned_lit by lia. lia.
Qed.

#[using="Type"] Lemma file_read_dsl d off count :
  0 <= off < 2^64 -> 0 <= count < 2^64 ->
  of_bytes (file_read d (Z_to_bv 64 off) (Z_to_bv 64 count)) = dsl d off (Z.of_nat (length (file_read d (Z_to_bv 64 off) (Z_to_bv 64 count)))).
Proof.
  intros Ho Hc. rewrite file_read_unguarded. unfold dsl, word_to_nat. rewrite !unsigned_lit by lia. rewrite Nat2Z.id, firstn_length_firstn. reflexivity.
Qed.

#[using="Type"] Lemma us_stdio_read tm nx pt K C g W e d f bufG bufC destG destC len :
  In e K -> RT e d f -> f_rbuf f = [] -> 1 <= len < 2^62 ->
  0 <= bufG < 2^64 -> 0 <= destG < 2^64 ->
  usimS (RUK tm nx pt K C g W) (stdio_read f bufG destG len) (stdio_read f bufC destC len) (rpost tm nx pt K C g W e d f len).
Proof.
  intros He HRT HRB Hlen HbG HdG. pose proof HRT as (S1 & S2 & S3 & S4 & S5 & S6 & S7). pose proof S1 as (C1 & F1 & C2 & X). unfold file_ok in F1.
  unfold stdio_read. cbv zeta.
  set (len0 := len - (if f_bufsize f =? 0 then 0 else 1)).
  assert (HL0 : 0 <= len0 < 2^62 /\ (f_bufsize f = 0 -> len0 = len) /\ (f_bufsize f <> 0 -> len0 = len - 1)).
  { subst len0. destruct (Z.eqb_spec (f_bufsize f) 0); lia. }
  set (cnt := len0 + f_bufsize f).
  assert (HC : 1 <= cnt < 2^63) by (subst cnt; lia).
  rewrite C2.
  (* [comment removed for export] *)
  assert (POST : forall count a l mo, count = cnt -> read_post nx K C e count a (g l) mo ->
            match a with RdErr _ => False | RdData rd =>
              Z.of_nat (length rd) <= cnt /\ (Z.of_nat (length rd) < cnt -> k_off e + Z.of_nat (length rd) = Z.of_nat (length d)) /\ k_off e + Z.of_nat (length rd) <= Z.of_nat (length d)
              /\ of_bytes rd = dsl d (k_off e) (Z.of_nat (length rd)) end
            /\ FI nx (match a with RdData rd => kset (kmove (Some d) (k_off e + Z.of_nat (length rd)) e) K | RdErr _ => K end) C (g l) mo).
  { intros count [err|rd] l mo -> RP; cbn in RP.
    - destruct RP as [NK _]. exfalso. exact (NK S2).
    - destruct RP as (_ & LEB & RP). rewrite S3 in RP. destruct RP as (Ebs & LE & HF). split; [| exact HF].
      pose proof HF as HF'. 
      assert (DL : Z.of_nat (length d) < 2^64).
      { pose proof (FI_kwf _ _ _ _ _ HF) as KW. (* [comment removed for export] *)
        specialize (KW (kmove (Some d) (k_off e + Z.of_nat (length rd)) e) ltac:(apply (In_kset_new _ K e); [exact He| reflexivity])).
        unfold kwf, kmove in KW; cbn in KW. unfold FLEN in KW. lia. }
      destruct (file_read_short d (k_off e) cnt ltac:(lia) ltac:(lia) DL) as (A1 & A2 & A3).
      pose proof (file_read_dsl d (k_off e) cnt ltac:(lia) ltac:(lia)) as A4.
      rewrite <- Ebs in *. auto. }
  eapply (ruk_bind tm nx pt K C g W
            (fun a => match a with RdErr _ => False | RdData rd =>
               Z.of_nat (length rd) <= cnt /\ (Z.of_nat (length rd) < cnt -> k_off e + Z.of_nat (length rd) = Z.of_nat (length d)) /\ k_off e + Z.of_nat (length rd) <= Z.of_nat (length d)
               /\ of_bytes rd = dsl d (k_off e) (Z.of_nat (length rd)) end)
            (fun a => match a with RdData rd => kset (kmove (Some d) (k_off e + Z.of_nat (length rd)) e) K | RdErr _ => K end) (fun _ => C) (fun _ => g) (fun _ => W)).
  - destruct (Z.eqb_spec len0 0) as [EZ|NZ].
    + eapply ru_post; [apply ru_read; eapply (unode_lift _ _ (FI nx K C) _ g W); apply (fn_read nx K C e bufG (f_bufsize f) He); lia|].
      intros a gh sG moG sC moC [HR [RP HW]]. destruct (POST (f_bufsize f) a _ _ ltac:(subst cnt; lia) RP) as [P1 P2]. split; [exact P1|]. split; [exact HR|]. exact (conj P2 HW).
    + eapply ru_post; [apply ru_readv; [reflexivity| | eapply (unode_lift _ _ (FI nx K C) _ g W); apply (fn_readv nx K C e _ He)]|].
      * unfold lens_okX. constructor; [cbn; lia|]. constructor; [cbn; lia|]. constructor.
      * constructor; [cbn; lia|]. constructor; [cbn; lia|]. constructor.
      * (* [comment removed for export] *)
        cbn [dsts_total snd]. rewrite S2 in X. destruct X as (_ & _ & _ & XB). unfold BUFSIZ in XB. lia.
      * (* [comment removed for export] *) intros _. rewrite S3. discriminate.
      * intros a gh sG moG sC moC [HR [RP HW]]. cbn [dsts_total snd] in RP. destruct (POST (len0 + (f_bufsize f + 0)) a _ _ ltac:(subst cnt; lia) RP) as [P1 P2]. split; [exact P1|]. split; [exact HR|]. exact (conj P2 HW).
  - intros [err|rd] PA; [destruct PA|]. destruct PA as (LEB & SHORT & LE & CNT). cbn beta.
    pose proof (of_bytes_length rd) as OL. set (bs := of_bytes rd) in *.
    assert (RET : forall r f', 
              zlength r <= len -> f_bufsize f' = f_bufsize f -> fshape f' e -> 0 <= zlength (f_rbuf f') ->
              zlength r + zlength (f_rbuf f') = Z.of_nat (length rd) ->
              (f_eof f' = true -> k_off e + zlength r = Z.of_nat (length d)) ->
              (zlength r < len -> k_off e + zlength r = Z.of_nat (length d)) ->
              r = dsl d (k_off e) (zlength r) -> f_rbuf f' = dsl d (k_off e + zlength r) (Z.of_nat (length rd) - zlength r) ->
              usimS (RUK tm nx pt (kset (kmove (Some d) (k_off e + Z.of_nat (length rd)) e) K) C g W) (mret (r, f')) (mret (r, f')) (rpost tm nx pt K C g W e d f len)).
    { intros r f' Hr HB Hsh Hnn Hc Heof Hshort Hcr Hcb. apply ru_ret. intros gh sG moG sC moC HRU. cbn [fst snd]. cbv zeta.
      unfold pos. rewrite HRB. cbn [zlength length Z.of_nat]. rewrite Z.sub_0_r.
      replace (k_off e + zlength r + zlength (f_rbuf f')) with (k_off e + Z.of_nat (length rd)) by lia.
      split; [exact Hr|]. split; [exact Hcr|]. split.
      { unfold RT, kat, kmove. rewrite S3. destruct e; cbn in *. split; [exact Hsh|]. split; [exact S2|]. split; [reflexivity|]. split; [lia|]. split; [lia|].
        split; [intros E; specialize (Heof E); unfold pos; cbn; lia|].
        rewrite Hcb at 1. f_equal; lia. }
      unfold kat. rewrite S3. destruct e; cbn in *. split; [lia|]. split; [intros SH; specialize (Hshort SH); lia|]. split; [exact HB|]. exact HRU. }
    destruct (Z.eqb_spec (zlength bs) 0) as [E0|N0].
    + apply (RET [] (set_eof f)); fsimp.
      * unfold zlength; cbn; lia.
      * reflexivity.
      * unfold fshape in *; fsimp. exact S1.
      * rewrite HRB. unfold zlength; cbn; lia.
      * rewrite HRB. unfold zlength in *; cbn in *; lia.
      * intros _. unfold zlength in *; cbn in *. lia.
      * intros _. unfold zlength in *; cbn in *. lia.
      * symmetry. apply dsl_nil'.
      * rewrite HRB. symmetry. rewrite <- OL, E0, Z.sub_0_r. apply dsl_0.
    + destruct (Z.leb_spec (zlength bs) len0) as [LE0|GT0].
      * apply (RET bs f).
        -- lia.
        -- reflexivity.
        -- exact S1.
        -- rewrite HRB. unfold zlength; cbn; lia.
        -- rewrite HRB. unfold zlength in *; cbn in *; lia.
        -- intros E. specialize (S6 E). unfold pos in S6. rewrite HRB in S6. unfold zlength in *; cbn in *. lia.
        -- intros SH. rewrite OL. apply SHORT. lia.
        -- rewrite OL. exact CNT.
        -- rewrite HRB, <- OL, Z.sub_diag. symmetry. apply dsl_0.
      * destruct (Z.eqb_spec (f_bufsize f) 0) as [BZ|BNZ]; [exfalso; lia|].
        assert (LEN2 : zlength (firstn (Z.to_nat len0) bs ++ firstn 1 (skipn (Z.to_nat len0) bs)) = len0 + 1) by (rewrite zlength_app, !zlength_firstn, zlength_skipn; lia).
        apply (RET (firstn (Z.to_nat len0) bs ++ firstn 1 (skipn (Z.to_nat len0) bs)) (set_rbuf (skipn 1 (skipn (Z.to_nat len0) bs)) f)); fsimp.
        -- rewrite zlength_app, !zlength_firstn, zlength_skipn. lia.
        -- reflexivity.
        -- unfold fshape in *; fsimp. rewrite S2 in *. exact S1.
        -- apply zlength_nonneg.
        -- rewrite zlength_app, !zlength_firstn, !zlength_skipn. lia.
        -- intros E. specialize (S6 E). unfold pos in S6. rewrite HRB in S6. unfold zlength in S6; cbn in S6. rewrite zlength_app, !zlength_firstn, zlength_skipn. lia.
        -- rewrite zlength_app, !zlength_firstn, zlength_skipn. intros; exfalso; lia.
        -- rewrite LEN2, <- firstn_add_skipn. replace (Z.to_nat len0 + 1)%nat with (Z.to_nat (len0 + 1)) by lia. rewrite CNT. apply dsl_firstn. lia.
        -- rewrite LEN2, <- skipn_add. replace (Z.to_nat len0 + 1)%nat with (Z.to_nat (len0 + 1)) by lia. rewrite CNT. rewrite dsl_skipn by lia. f_equal; lia.
Qed.

#[using="Type"] Lemma RT_rd0 e d f : RT e d f -> f_rbuf f = [] -> RT e d (set_rbuf [] (set_w false [] f)).
Proof.
  intros ((C1 & F1 & C2 & X) & S2 & S3 & S4 & S5 & S6 & S7) HRB. rewrite S2 in X. destruct X as (N1 & WB & WA).
  unfold RT, fshape, pos, file_ok in *; fsimp. rewrite S2. rewrite HRB in *.
  split; [repeat split; auto; lia|]. split; [reflexivity|]. split; [exact S3|]. split; [lia|]. split; [lia|]. split; [exact S6| symmetry; apply dsl_nil'].
Qed.

#[using="Type"] Lemma us_fread_loop tm nx pt C g W d bufG bufC : forall fuel e K f destG destC l acc,
  In e K -> RT e d f -> (0 < l -> f_rbuf f = []) -> l < 2^62 -> (Z.to_nat l < fuel)%nat ->
  0 <= bufG < 2^64 -> 0 <= destG -> destG + l < 2^64 ->
  usimS (RUK tm nx pt K C g W) (fread_loop fuel f bufG destG l acc) (fread_loop fuel f bufC destC l acc)
        (eqpost (fun r => fun gh sG moG sC moC => exists r1, fst r = acc ++ r1 /\
           rpost tm nx pt K C g W e d f (Z.max l 0) (r1, snd r) (r1, snd r) gh sG moG sC moC)).
Proof.
  induction fuel as [|fuel IH]; intros e K f destG destC l acc He HRT HRB Hl Hfuel HbG HdG HdG'; [lia|]. cbn [fread_loop].
  pose proof HRT as (S1 & S2 & S3 & S4 & S5 & S6 & S7).
  assert (RET0 : forall f', RT e d f' -> f_rbuf f' = f_rbuf f -> f_bufsize f' = f_bufsize f -> (0 < l -> f_eof f' = true) ->
            usimS (RUK tm nx pt K C g W) (mret (acc, f')) (mret (acc, f'))
                  (eqpost (fun r => fun gh sG moG sC moC => exists r1, fst r = acc ++ r1 /\ rpost tm nx pt K C g W e d f (Z.max l 0) (r1, snd r) (r1, snd r) gh sG moG sC moC))).
  { intros f' HRT' ERB EBS EOF. apply ruk_use. intros l0 mo HF. apply ru_ret. intros gh sG moG sC moC HR. exists []. cbn [fst snd]. rewrite app_nil_r. split; [reflexivity|].
    split; [reflexivity|]. cbv zeta. cbn [fst snd]. unfold pos. rewrite ERB. rewrite !(@zlength_nil Z).
    replace (k_off e - zlength (f_rbuf f) + 0 + zlength (f_rbuf f)) with (k_off e) by lia. rewrite kat_self.
    split; [lia|]. split; [reflexivity|]. split; [exact HRT'|]. split; [lia|]. split; [| split; [exact EBS| rewrite kset_self; [exact HR| exact He| exact (proj1 (FI_KP _ _ _ _ _ HF))]]].
    intros LT. destruct HRT' as (_ & _ & _ & _ & _ & E6 & _). unfold pos in E6. rewrite ERB in E6. apply E6. apply EOF. lia. }
  destruct (Z.leb_spec l 0) as [LE|GT]; [apply (RET0 f HRT eq_refl eq_refl); intros; lia|].
  specialize (HRB GT).
  eapply ruk_bind with (W1 := fun _ => W) (K1 := fun _ => K) (C1 := fun _ => C) (g1 := fun _ => g); [apply (us_toread tm nx pt K C g W e d f HRT HRB)|].
  intros ef ->. cbn [fst snd]. destruct (f_eof f) eqn:EEOF.
  - apply ru_bind_retl. cbn [fst snd]. apply RET0; [apply RT_rd0; [exact HRT| exact HRB]| fsimp; symmetry; exact HRB| reflexivity| intros; fsimp; exact EEOF].
  - pose proof (RT_rd0 e d f HRT HRB) as HRT2.
    eapply ru_bind.
    { eapply ru_post; [apply (us_stdio_read tm nx pt K C g W e d _ bufG bufC destG destC l He HRT2 eq_refl ltac:(lia) HbG ltac:(lia))|].
      intros r ? ? ? ? ? HP0. exact HP0. }
    intros [bs f1]. cbv zeta. cbn [fst snd].
    apply usim_pure; intros LB. apply usim_pure; intros CB. apply usim_pure; intros HRT1. apply usim_pure; intros P1. apply usim_pure; intros SH1. apply usim_pure; intros BS1.
    apply ruk_use. intros l0 mo HF0.
    assert (POS0 : pos e (set_rbuf [] (set_w false [] f)) = pos e f) by (unfold pos; fsimp; rewrite HRB; reflexivity).
    rewrite POS0 in *.
    set (e1 := kat e (pos e f + zlength bs + zlength (f_rbuf f1))) in *.
    pose proof (zlength_nonneg bs) as NB.
    destruct bs as [|b bs'] eqn:EBS.
    + subst e1. apply ru_ret. intros gh sG moG sC moC HR. exists []. cbn [fst snd]. rewrite app_nil_r. split; [reflexivity|]. split; [reflexivity|]. cbv zeta.
      cbn [fst snd] in *. rewrite !(@zlength_nil Z) in *. rewrite !Z.add_0_r in *.
      split; [lia|]. split; [reflexivity|]. split; [exact HRT1|]. split; [exact P1|]. split; [intros _; apply SH1; lia|]. split; [fsimp; exact BS1| exact HR].
    + rewrite <- EBS in *. assert (HB1 : 1 <= zlength bs) by (rewrite EBS; unfold zlength; cbn [length]; lia).
      assert (He1 : In e1 (kset e1 K)) by (apply (In_kset_new _ K e); [exact He| reflexivity]).
      eapply usim_post; [apply (IH e1 (kset e1 K) f1 (destG + zlength bs) (destC + zlength bs) (l - zlength bs) (acc ++ bs) He1 HRT1)|].
      * intros GT1. destruct (f_rbuf f1) eqn:ER1; [reflexivity|]. exfalso.
        (* [comment removed for export] *)
        pose proof HRT1 as (_ & _ & _ & R4 & R5 & _). rewrite ER1 in R4.
        assert (HS : zlength bs < l) by lia. specialize (SH1 HS).
        subst e1. unfold pos, kat, kmove in SH1, P1, R4, R5. destruct e; cbn in SH1, P1, R4, R5. rewrite ?ER1 in SH1, P1.
        unfold zlength in *. cbn [length] in *. lia.
      * lia.
      * lia.
      * exact HbG.
      * lia.
      * lia.
      * intros [rr rf] r' gh sG moG sC moC [<- (r1 & E1 & _ & Q)]. split; [reflexivity|]. exists (bs ++ r1). cbn [fst snd] in *. split; [rewrite E1, app_assoc; reflexivity|]. split; [reflexivity|].
        cbv zeta in Q. cbv zeta. cbn [fst snd] in *. destruct Q as (Q1 & QC & Q2 & Q3 & Q4 & Q5 & Q6).
        rewrite zlength_app. subst e1. rewrite <- ?EBS in *. rewrite kat_kat in *. rewrite kset_kset in Q6 by reflexivity.
        unfold pos in *. unfold kat, kmove in *. destruct e; cbn in *.
        replace (k_off - zlength (f_rbuf f) + (zlength bs + zlength r1) + zlength (f_rbuf rf))
          with (k_off - zlength (f_rbuf f) + zlength bs + zlength (f_rbuf f1) - zlength (f_rbuf f1) + zlength r1 + zlength (f_rbuf rf)) by lia.
        split; [lia|]. split; [apply (dsl_cat _ _ _ _ _ _ CB QC); lia|]. split; [exact Q2|]. split; [lia|]. split; [intros; apply Q4; lia|]. split; [fsimp; congruence| exact Q6].
Qed.

#[using="Type"] Lemma us_fread_file tm nx pt K C g W e d f bufG bufC destG destC n :
  In e K -> RT e d f -> 0 <= n < 2^62 -> 0 <= bufG < 2^64 -> 0 <= destG -> destG + n < 2^64 ->
  usimS (RUK tm nx pt K C g W) (fread_file f bufG destG n) (fread_file f bufC destC n) (rpost tm nx pt K C g W e d f n).
Proof.
  intros He HRT Hn HbG HdG HdG'. unfold fread_file. cbv zeta. pose proof HRT as (S1 & S2 & S3 & S4 & S5 & S6 & S7).
  set (k := Z.min (zlength (f_rbuf f)) n). pose proof (zlength_nonneg (f_rbuf f)) as NR.
  assert (HK : 0 <= k <= n /\ k <= zlength (f_rbuf f)) by (subst k; lia).
  assert (FK : firstn (Z.to_nat k) (f_rbuf f) = dsl d (pos e f) k).
  { etransitivity; [apply f_equal; exact S7|]. unfold pos. apply dsl_firstn. lia. }
  assert (HRT' : RT e d (set_rbuf (skipn (Z.to_nat k) (f_rbuf f)) f)).
  { unfold RT, fshape, pos, file_ok in *; fsimp. rewrite S2 in *. rewrite zlength_skipn.
    split; [exact S1|]. split; [reflexivity|]. split; [exact S3|]. split; [lia|]. split; [lia|]. split; [intros E; specialize (S6 E); lia|].
    etransitivity; [apply f_equal; exact S7|]. rewrite dsl_skipn by lia. f_equal; lia. }
  eapply usim_post; [apply (us_fread_loop tm nx pt C g W d bufG bufC (S (Z.to_nat n)) e K _ (destG + k) (destC + k) (n - k) (firstn (Z.to_nat k) (f_rbuf f)) He HRT')|]; try lia.
  - intros GT. fsimp. apply skipn_all2. subst k. unfold zlength in *. lia.
  - intros [rr rf] r' gh sG moG sC moC [<- (r1 & E1 & _ & Q)]. split; [reflexivity|]. cbv zeta in Q. cbv zeta. cbn [fst snd] in *.
    destruct Q as (Q1 & QC & Q2 & Q3 & Q4 & Q5 & Q6). rewrite E1. rewrite zlength_app, zlength_firstn.
    assert (PK : pos e (set_rbuf (skipn (Z.to_nat k) (f_rbuf f)) f) = pos e f + k) by (unfold pos; fsimp; rewrite zlength_skipn; lia).
    rewrite PK in *. replace (Z.of_nat (Z.to_nat k) `min` zlength (f_rbuf f)) with k by lia.
    replace (pos e f + (k + zlength r1) + zlength (f_rbuf rf)) with (pos e f + k + zlength r1 + zlength (f_rbuf rf)) by lia.
    split; [lia|]. split; [apply (dsl_cat _ _ _ _ _ _ FK QC); [rewrite zlength_firstn| | unfold pos]; lia|].
    split; [exact Q2|]. split; [lia|]. split; [intros; apply Q4; lia|]. split; [fsimp; exact Q5| exact Q6].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Inductive tgt := TC (fd : Z) | TW (e : kfe) | TR (e : kfe) (d : list byte).

Definition TT (t : tgt) (f : file_st) : Prop :=
  match t with TC fd => WT None f /\ f_fd f = fd | TW e => WT (Some e) f | TR e d => RT e d f end.
Definition tgt_in (t : tgt) (K : list kfe) : Prop := match t with TC _ => True | TW e | TR e _ => In e K end.
Definition tbud (t : tgt) (f : file_st) : Prop := match t with TW e => wbud (Some e) f 0 | _ => True end.

(* [comment removed for export] *)
Definition ftgt (t : tgt) (f : file_st) : tgt :=
  match t with TC fd => TC fd | TW e => TW (kapp e (to_bytes (f_wbuf f))) | TR e d => TR (kpos e f) d end.
Definition ftgt_K (t : tgt) (f : file_st) (K : list kfe) : list kfe :=
  match t with TC _ => K | TW e => kset (kapp e (to_bytes (f_wbuf f))) K | TR e _ => kset (kpos e f) K end.
Definition ftgt_g (t : tgt) (g : libc_st hptr -> libc_st hptr) : libc_st hptr -> libc_st hptr :=
  match t with TR e _ => fun l => lrem e (g l) | _ => g end.
Definition tent (t : tgt) : option kfe := match t with TC _ => None | TW e | TR e _ => Some e end.

#[using="Type"] Lemma FI_lrem nx K C l mo e : FI nx K C l mo -> FI nx K C (lrem e l) mo.
Proof.
  intros (A & B & M & (D1 & D2 & D3 & D4 & D5)). split; [exact A|]. split; [exact B|]. split; [exact M|].
  unfold lrem. destruct (k_own e) as [h|]; [| exact (conj D1 (conj D2 (conj D3 (conj D4 D5))))]. cbn.
  split; [exact D1|]. split; [exact D2|]. split; [apply NoDup_files_remove; exact D3|]. split; [| exact D5].
  intros h' f' Hin. apply (In_files_remove _ _ _ D3) in Hin as [Hin _]. exact (D4 h' f' Hin).
Qed.

#[using="Type"] Lemma kpos_nil e f : f_rbuf f = [] -> kpos e f = e.
Proof. intros H. unfold kpos. rewrite H, (@zlength_nil Z), Z.sub_0_r. destruct e; reflexivity. Qed.

#[using="Type"] Lemma us_sync_read_pos tm nx pt K C g W t f :
  tgt_in t K -> TT t f ->
  usimS (RUK tm nx pt K C g W) (sync_read_pos f) (sync_read_pos f)
        (eqpost (fun _ => RUK tm nx pt (match t with TR e _ => kset (kpos e f) K | _ => K end) C (ftgt_g t g) W)).
Proof.
  intros HI HT. unfold sync_read_pos. destruct t as [fd|e|e d]; cbn [ftgt_g].
  - destruct HT as [[(F1 & F2 & F3 & F4 & F5) _] _]. rewrite F3. apply ru_ret. intros; assumption.
  - destruct HT as [(F1 & F2 & F3 & F4 & F5) _]. rewrite F3. apply ru_ret. intros; assumption.
  - cbn in HI. pose proof HT as (S1 & S2 & S3 & S4 & S5 & S6). pose proof S1 as (C1 & F1 & C2 & X).
    destruct (f_rbuf f) as [|c rb] eqn:ERB.
    + apply ruk_use. intros l mo HF. apply ru_ret. intros gh sG moG sC moC [HR [HF' HW]]. rewrite (kpos_nil e f ERB), kset_self; [| exact HI| exact (proj1 (FI_KP _ _ _ _ _ HF))].
      split; [exact HR|]. split; [apply FI_lrem; exact HF'| exact HW].
    + rewrite <- ERB in *. rewrite C2. eapply ruk_bind with (W1 := fun _ => W) (K1 := fun _ => kset (kpos e f) K) (C1 := fun _ => C) (g1 := fun _ => fun l => lrem e (g l)).
      * eapply ruk_nodeK; [exact I| apply (fn_lseek nx K C e d (zlength (f_rbuf f)) HI S2 S3); lia|].
        intros r l mo [Er HF]. split; [exact Er|]. unfold kpos. rewrite S3. exact HF.
      * intros r _. cbn beta. apply ru_ret. intros; assumption.
Qed.

(* [comment removed for export] *)
Definition flpost tm nx pt K C g W (t : tgt) (f : file_st) : file_st -> file_st -> relX :=
  eqpost (fun f' => fun gh sG moG sC moC =>
    (TT (ftgt t f) f' /\ f_wbuf f' = [] /\ f_rbuf f' = [] /\ f_wactive f' = false /\ f_bufsize f' = f_bufsize f /\ f_fd f' = f_fd f /\ tbud (ftgt t f) f')
    /\ RUK tm nx pt (ftgt_K t f K) C (ftgt_g t g) W gh sG moG sC moC).

(* [comment removed for export] *)
#[using="Type"] Lemma us_flush_w tm nx pt K C g W t f :
  tgt_in t K -> TT t f -> tbud t f ->
  usimS (RUK tm nx pt K C g W) (match f_wbuf f with [] => mret f | _ :: _ => file_writefn f [] end) (match f_wbuf f with [] => mret f | _ :: _ => file_writefn f [] end)
        (eqpost (fun f1 => fun gh sG moG sC moC =>
           (TT (match t with TR _ _ => t | _ => ftgt t f end) f1 /\ f_wbuf f1 = [] /\ f_rbuf f1 = f_rbuf f /\ f_bufsize f1 = f_bufsize f /\ f_fd f1 = f_fd f
            /\ (f_wactive f1 = false -> f1 = f) /\ tbud (ftgt t f) f1)
           /\ RUK tm nx pt (match t with TR _ _ => K | _ => ftgt_K t f K end) C g W gh sG moG sC moC)).
Proof.
  intros HI HT HB.
  assert (WCASE : forall eo, tgt_ok eo K -> WT eo f -> wbud eo f 0 ->
            usimS (RUK tm nx pt K C g W) (match f_wbuf f with [] => mret f | _ :: _ => file_writefn f [] end) (match f_wbuf f with [] => mret f | _ :: _ => file_writefn f [] end)
                  (eqpost (fun f1 => fun gh sG moG sC moC =>
                     (WT (etgt eo (to_bytes (f_wbuf f))) f1 /\ f_wbuf f1 = [] /\ f_rbuf f1 = f_rbuf f /\ f_bufsize f1 = f_bufsize f /\ f_fd f1 = f_fd f
                      /\ (f_wactive f1 = false -> f1 = f) /\ wbud (etgt eo (to_bytes (f_wbuf f))) f1 0)
                     /\ RUK tm nx pt (ktgt eo (to_bytes (f_wbuf f)) K) C g W gh sG moG sC moC))).
  { intros eo HIo HW HBo. pose proof HW as ((F1 & F2 & F3 & F4 & F5) & X). destruct (f_wbuf f) as [|c wb] eqn:EWB.
    - apply ruk_use. intros l mo HF. apply ru_ret. intros gh sG moG sC moC HR. cbn [to_bytes map]. rewrite etgt_nil, ktgt_nil; [| exact HIo| exact (proj1 (FI_KP _ _ _ _ _ HF))].
      split; [| exact HR]. split; [exact HW|]. split; [exact EWB|]. repeat split; auto.
    - rewrite <- EWB. eapply ru_post; [apply (us_file_writefn tm nx pt K C g W eo f [] HIo HW); [unfold zlength; cbn; lia| eapply wbud_mono; [exact HBo| unfold zlength; cbn; lia]]|].
      intros f1 gh sG moG sC moC [(W1 & EB1 & EA1 & EBS1 & EFD1 & _) H1]. rewrite app_nil_r in *. split; [| exact H1].
      split; [exact W1|]. split; [exact EB1|]. split; [destruct W1 as [(_ & _ & R1 & _) _]; rewrite R1, F3; reflexivity|]. split; [exact EBS1|]. split; [exact EFD1|].
      split; [intros EA; rewrite EA in EA1; discriminate|].
      eapply wbud_tgt; [exact HBo|]. rewrite EB1, zlength_to_bytes. unfold zlength; cbn; lia. }
  destruct t as [fd|e|e d]; cbn [TT ftgt ftgt_K tbud tgt_in] in *.
  - destruct HT as [HW EFD]. eapply ru_post; [apply (WCASE None (tgt_ok_none K) HW I)|]. cbn [etgt ktgt].
    intros f1 gh sG moG sC moC [(W1 & EB1 & ER1 & EBS1 & EFD1 & EA1 & _) H1]. split; [| exact H1].
    split; [split; [exact W1| congruence]|]. split; [exact EB1|]. split; [exact ER1|]. split; [exact EBS1|]. split; [exact EFD1|]. split; [exact EA1| exact I].
  - eapply ru_post; [apply (WCASE (Some e) (tgt_ok_some e K HI) HT HB)|]. cbn [etgt ktgt].
    intros f1 gh sG moG sC moC [(W1 & EB1 & ER1 & EBS1 & EFD1 & EA1 & BU1) H1]. split; [| exact H1].
    split; [exact W1|]. split; [exact EB1|]. split; [exact ER1|]. split; [exact EBS1|]. split; [exact EFD1|]. split; [exact EA1| exact BU1].
  - pose proof HT as (S1 & S2 & S3 & S4 & S5 & S6 & S7). pose proof S1 as (C1 & F1 & C2 & X). rewrite S2 in X. destruct X as (N1 & WB & WA).
    rewrite WB. apply ru_ret. intros gh sG moG sC moC HR. split; [| exact HR]. split; [exact HT|]. split; [exact WB|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [intros; reflexivity| exact I].
Qed.

#[using="Type"] Lemma TT_flushed t f f1 :
  TT (match t with TR _ _ => t | _ => ftgt t f end) f1 -> f_wbuf f1 = [] -> f_rbuf f1 = f_rbuf f -> f_bufsize f1 = f_bufsize f -> f_fd f1 = f_fd f ->
  TT (ftgt t f) (set_rbuf [] (set_w false [] f1)) /\ tbud (ftgt t f) f1 = tbud (ftgt t f) (set_rbuf [] (set_w false [] f1)).
Proof.
  intros HT EB ER EBS EFD. destruct t as [fd|e|e d]; cbn [TT ftgt tbud] in *.
  - destruct HT as [[(F1 & F2 & F3 & F4 & F5) X] FD]. split; [| reflexivity]. unfold WT, wok, file_ok in *; fsimp. unfold zlength; cbn. repeat split; auto; lia.
  - destruct HT as [(F1 & F2 & F3 & F4 & F5) X]. split; [| unfold wbud; fsimp; destruct (k_data _); rewrite ?EB; reflexivity].
    unfold WT, wok, file_ok in *; fsimp. unfold zlength; cbn. repeat split; auto; try lia. all: tauto.
  - split; [| reflexivity]. pose proof HT as (S1 & S2 & S3 & S4 & S5 & S6 & S7). pose proof S1 as (C1 & F1 & C2 & X). rewrite S2 in X.
    unfold RT, fshape, pos, kpos, kmove, file_ok in *; fsimp. rewrite S2, S3 in *. destruct e; cbn in *. rewrite ?ER in *. rewrite ?(@zlength_nil Z) in *.
    destruct X as (N1 & _ & _).
    split; [repeat split; auto; lia|]. split; [reflexivity|]. split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [intros E; specialize (S6 E); lia|].
    rewrite Z.sub_0_r. symmetry. apply dsl_0.
Qed.

#[using="Type"] Lemma us_fflush_file tm nx pt K C g W t f :
  tgt_in t K -> TT t f -> tbud t f ->
  usimS (RUK tm nx pt K C g W) (fflush_file f) (fflush_file f) (flpost tm nx pt K C g W t f).
Proof.
  intros HI HT HB. unfold fflush_file.
  eapply ruk_bind with (W1 := fun _ => W); [apply (us_flush_w tm nx pt K C g W t f HI HT HB)|]. intros f1 (T1 & EB1 & ER1 & EBS1 & EFD1 & EA1 & BU1). cbn beta.
  assert (HI1 : tgt_in (match t with TR _ _ => t | _ => ftgt t f end) (match t with TR _ _ => K | _ => ftgt_K t f K end)).
  { destruct t as [fd|e|e d]; cbn in *; [exact I| | exact HI]. apply (In_kset_new _ K e); [exact HI| rewrite kapp_fd; reflexivity]. }
  eapply ruk_bind with (W1 := fun _ => W) (phi := fun _ => True) (K1 := fun _ => ftgt_K t f K) (C1 := fun _ => C) (g1 := fun _ => ftgt_g t g).
  - eapply ru_post; [apply (us_sync_read_pos tm nx pt _ C g W _ f1 HI1 T1)|]. intros [] gh sG moG sC moC H. split; [exact I|].
    destruct t as [fd|e|e d]; cbn [ftgt_K ftgt_g ftgt] in *; try exact H. unfold kpos in *. rewrite ER1 in H. exact H.
  - intros [] _. apply ru_ret. intros gh sG moG sC moC HR. destruct (TT_flushed t f f1 T1 EB1 ER1 EBS1 EFD1) as [TT' TB']. fsimp.
    split; [| exact HR]. split; [exact TT'|]. rewrite <- TB'. repeat split; auto.
Qed.

#[using="Type"] Lemma us_close_file tm nx pt K C g W t f :
  tgt_in t K -> TT t f -> tbud t f ->
  usimS (RUK tm nx pt K C g W) (close_file f) (close_file f) (eqpost (fun _ => RUK tm nx pt (ftgt_K t f K) C (ftgt_g t g) W)).
Proof.
  intros HI HT HB. unfold close_file.
  eapply ruk_bind with (W1 := fun _ => W); [apply (us_flush_w tm nx pt K C g W t f HI HT HB)|]. intros f1 (T1 & EB1 & ER1 & EBS1 & EFD1 & EA1 & BU1). cbn beta.
  assert (HI1 : tgt_in (match t with TR _ _ => t | _ => ftgt t f end) (match t with TR _ _ => K | _ => ftgt_K t f K end)).
  { destruct t as [fd|e|e d]; cbn in *; [exact I| | exact HI]. apply (In_kset_new _ K e); [exact HI| rewrite kapp_fd; reflexivity]. }
  eapply ru_post; [apply (us_sync_read_pos tm nx pt _ C g W _ f1 HI1 T1)|]. intros [] gh sG moG sC moC H.
  destruct t as [fd|e|e d]; cbn [ftgt_K ftgt_g ftgt] in *; try exact H. unfold kpos in *. rewrite ER1 in H. exact H.
Qed.

(* [comment removed for export] *)
Definition ctgt_e (t : tgt) (f : file_st) : option kfe := tent (ftgt t f).

#[using="Type"] Lemma kdel_kset e' K : kdel (k_fd e') (kset e' K) = kdel (k_fd e') K.
Proof.
  unfold kdel, kset. induction K as [|x K IH]; cbn; [reflexivity|].
  destruct (Z.eqb_spec (k_fd x) (k_fd e')) as [E|NE].
  - rewrite Z.eqb_refl. cbn. exact IH.
  - rewrite (proj2 (Z.eqb_neq _ _) NE). cbn. rewrite IH. reflexivity.
Qed.

#[using="Type"] Lemma us_fclose_file tm nx pt K C g W t f e0 :
  tgt_in t K -> TT t f -> tbud t f -> tent t = Some e0 ->
  usimS (RUK tm nx pt K C g W) (fclose_file f) (fclose_file f)
        (eqpost (fun _ => fun gh sG moG sC moC => exists e', ctgt_e t f = Some e' /\ k_fd e' = k_fd e0 /\ k_own e' = k_own e0 /\ k_path e' = k_path e0 /\
           RUK tm nx pt (kdel (k_fd e0) K) (cclose e' C) (fun l => lrem e' (ftgt_g t g l)) W gh sG moG sC moC)).
Proof.
  intros HI HT HB HE. unfold fclose_file.
  eapply ruk_bind with (W1 := fun _ => W); [eapply ru_post; [apply (us_fflush_file tm nx pt K C g W t f HI HT HB)| intros f1 ? ? ? ? ? [HP0 H]; exact (conj HP0 H)]|].
  intros f1 (T1 & EB1 & ER1 & EA1 & EBS1 & EFD1 & BU1). cbn beta.
  destruct t as [fd|e|e d]; cbn in HE; [discriminate| |]; injection HE as ->.
  - cbn [ftgt ftgt_K ftgt_g TT ctgt_e tent] in *. pose proof T1 as [_ (C1 & C2 & C3 & C4)]. rewrite EFD1.
    destruct HT as [_ (_ & C2' & _)]. rewrite C2'.
    assert (HI1 : In (kapp e0 (to_bytes (f_wbuf f))) (kset (kapp e0 (to_bytes (f_wbuf f))) K)) by (apply (In_kset_new _ K e0); [exact HI| rewrite kapp_fd; reflexivity]).
    rewrite <- (kapp_fd e0 (to_bytes (f_wbuf f))).
    eapply ru_post; [eapply ruk_nodeK with (phi := fun _ => True) (K' := fun _ => kdel (k_fd (kapp e0 (to_bytes (f_wbuf f)))) (kset (kapp e0 (to_bytes (f_wbuf f))) K))
      (C' := fun _ => cclose (kapp e0 (to_bytes (f_wbuf f))) C) (g' := fun _ => fun l => lrem (kapp e0 (to_bytes (f_wbuf f))) (g l));
      [exact I| apply (fn_close_ok nx _ C _ HI1)| intros a l mo HF; exact (conj I HF)]|].
    intros [] gh sG moG sC moC [_ H]. exists (kapp e0 (to_bytes (f_wbuf f))). rewrite kdel_kset in H.
    split; [reflexivity|]. split; [reflexivity|]. split; [apply kapp_own|]. split; [apply kapp_path|]. exact H.
  - cbn [ftgt ftgt_K ftgt_g TT ctgt_e tent] in *. pose proof T1 as ((C1 & F1 & C2 & X) & _). rewrite EFD1.
    destruct HT as ((_ & _ & C2' & _) & _). rewrite C2'.
    assert (HI1 : In (kpos e0 f) (kset (kpos e0 f) K)) by (apply (In_kset_new _ K e0); [exact HI| reflexivity]).
    change (k_fd e0) with (k_fd (kpos e0 f)).
    eapply ru_post; [eapply ruk_nodeK with (phi := fun _ => True) (K' := fun _ => kdel (k_fd (kpos e0 f)) (kset (kpos e0 f) K))
      (C' := fun _ => cclose (kpos e0 f) C) (g' := fun _ => fun l => lrem (kpos e0 f) (lrem e0 (g l)));
      [exact I| apply (fn_close_ok nx _ C _ HI1)| intros a l mo HF; exact (conj I HF)]|].
    intros [] gh sG moG sC moC [_ H]. exists (kpos e0 f). rewrite kdel_kset in H.
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. exact H.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma RQ_blk_addr tm nx pt gh sG moG sC moC k n :
  RQ tm nx pt gh sG moG sC moC -> tm !! k = Some n ->
  0 <= blk_addr HOG sG k /\ blk_addr HOG sG k + n <= 2^62 /\ 0 <= n.
Proof. intros HR Hk. exact (blk_addr_range _ _ _ _ _ _ _ _ _ _ HR Hk). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition WS (hs : list hptr) (l : libc_st hptr) : Prop :=
  forall h, In h hs -> In h (map fst (lc_files l)).

#[using="Type"] Lemma WS_files hs l l' : map fst (lc_files l') = map fst (lc_files l) -> WS hs l -> WS hs l'.
Proof. intros E H h Hh. rewrite E. exact (H h Hh). Qed.
#[using="Type"] Lemma WS_mono hs hs' l : (forall h, In h hs' -> In h hs) -> WS hs l -> WS hs' l.
Proof. intros SUB H h Hh; apply H; exact (SUB h Hh). Qed.

#[local] Notation lookup_fileP := (@lookup_file _ hptr ps_libc N.eqb).
#[local] Notation store_fileP := (@store_file _ hptr ps_libc set_libc N.eqb).
#[local] Notation with_fileP := (@with_file _ hptr ps_libc set_libc N.eqb _).
#[local] Notation with_file_P := (@with_file_ _ hptr ps_libc set_libc N.eqb).
#[local] Notation idl := (fun l : libc_st hptr => l).

(* [comment removed for export] *)
#[using="Type"] Lemma ruk_rd_lc tm nx pt K C g W :
  usimS (RUK tm nx pt K C g W) (rd_lc ps_libc) (rd_lc ps_libc)
        (eqpost (fun l => fun gh sG moG sC moC => (LCI l /\ (exists mo, FI nx K C (g l) mo) /\ (exists o, W l o))
                                              /\ RUK tm nx pt K C g (fun l' o => W l' o /\ l' = l) gh sG moG sC moC)).
Proof.
  eapply usim_post; [apply ru_rd_lc|]. intros a b gh sG moG sC moC [<- (-> & HL & HR & HF & HW)]. split; [reflexivity|].
  split; [split; [exact HL| split; [exists moG; exact HF| exists (ps_outfile sG); exact HW]]|]. split; [exact HR|]. split; [exact HF|]. split; [exact HW| reflexivity].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma ruk_frame_weaken {A} tm nx pt K C g (W W' : libc_st hptr -> option hptr -> Prop) (m : Monad.M PSG A) (m' : Monad.M PSC A) Q :
  (forall l o, W l o -> W' l o) -> usimS (RUK tm nx pt K C g W') m m' Q -> usimS (RUK tm nx pt K C g W) m m' Q.
Proof. intros HW H. eapply ru_pre; [exact H|]. intros gh sG moG sC moC [HR [HF X]]. split; [exact HR|]. split; [exact HF| apply HW; exact X]. Qed.

#[using="Type"] Lemma ruk_post_weaken {A} tm nx pt (K : A -> list kfe) (C : A -> list (list byte * list byte)) (g : A -> libc_st hptr -> libc_st hptr) (W W' : A -> libc_st hptr -> option hptr -> Prop) (phi phi' : A -> Prop) R (m : Monad.M PSG A) (m' : Monad.M PSC A) :
  usimS R m m' (eqpost (fun a => fun gh sG moG sC moC => phi a /\ RUK tm nx pt (K a) (C a) (g a) (W a) gh sG moG sC moC)) ->
  (forall a, phi a -> phi' a) -> (forall a l o, phi a -> W a l o -> W' a l o) ->
  usimS R m m' (eqpost (fun a => fun gh sG moG sC moC => phi' a /\ RUK tm nx pt (K a) (C a) (g a) (W' a) gh sG moG sC moC)).
Proof.
  intros H HP HW. eapply ru_post; [exact H|]. intros a gh sG moG sC moC [Ha [HR [HF X]]]. split; [exact (HP a Ha)|]. split; [exact HR|]. split; [exact HF| exact (HW a _ _ Ha X)].
Qed.

(* [comment removed for export] *)
Definition fpm : Type := list (hptr * (file_st -> Prop)).
(* [comment removed for export] *)
Definition WF (oh : option hptr) (hs : list hptr) (F : fpm) (l : libc_st hptr) (o : option hptr) : Prop :=
  o = oh /\ List.NoDup (map fst (lc_files l)) /\ WS hs l /\ forall h P f, In (h, P) F -> In (h, f) (lc_files l) -> P f.
Definition fupd (h : hptr) (P : file_st -> Prop) (F : fpm) : fpm := (h, P) :: List.filter (fun hp => negb (N.eqb (fst hp) h)) F.
Definition fdel (h : hptr) (F : fpm) : fpm := List.filter (fun hp => negb (N.eqb (fst hp) h)) F.

#[using="Type"] Lemma In_fdel h F h' P : In (h', P) (fdel h F) <-> In (h', P) F /\ h' <> h.
Proof.
  unfold fdel. rewrite filter_In. cbn. split.
  - intros [H1 H2]. split; [exact H1|]. intros ->. rewrite N.eqb_refl in H2. discriminate.
  - intros [H1 NE]. split; [exact H1|]. destruct (N.eqb_spec h' h); [contradiction| reflexivity].
Qed.
#[using="Type"] Lemma In_fupd h P F h' P' : In (h', P') (fupd h P F) <-> (h' = h /\ P' = P) \/ (In (h', P') F /\ h' <> h).
Proof.
  unfold fupd. cbn. fold (fdel h F). rewrite In_fdel. split.
  - intros [E|X]; [injection E as -> ->; left; auto| right; exact X].
  - intros [[-> ->]|X]; [left; reflexivity| right; exact X].
Qed.

#[using="Type"] Lemma WF_WS oh hs F l o : WF oh hs F l o -> WS hs l. Proof. intros (_ & _ & H & _); exact H. Qed.

#[using="Type"] Lemma us_lookup_file tm nx pt K C oh hs F h e P :
  In e K -> k_own e = Some h -> In h hs -> In (h, P) F ->
  usimS (RUK tm nx pt K C idl (WF oh hs F)) (lookup_fileP h) (lookup_fileP h)
        (eqpost (fun f => fun gh sG moG sC moC => (fshape f e /\ zlength (f_rbuf f) <= k_off e /\ file_ok f /\ P f)
                   /\ RUK tm nx pt K C idl (fun l o => WF oh hs F l o /\ In (h, f) (lc_files l)) gh sG moG sC moC)).
Proof.
  intros He Ho Hh HP. unfold lookup_file.
  eapply ruk_bind with (K1 := fun _ => K) (C1 := fun _ => C) (g1 := fun _ => idl); [apply ruk_rd_lc|].
  intros l (HL & [mo HF] & [o (HO & HND & HW & HFP)]). cbn beta.
  pose proof (HW h Hh) as Hin. apply in_map_iff in Hin as ([h' f] & E & Hin). cbn in E; subst h'.
  rewrite (In_files_lookup _ _ _ (FI_nodup_files _ _ _ _ _ HF) Hin).
  apply ru_ret. intros gh sG moG sC moC [HR [HF' [HW' E]]].
  destruct (FI_owner_file _ _ _ _ _ _ _ _ HF He Ho Hin) as [Sh LE].
  split; [split; [exact Sh| split; [exact LE| split; [exact (proj1 (proj2 Sh))| exact (HFP h P f HP Hin)]]]|].
  split; [exact HR|]. split; [exact HF'|]. split; [exact HW'|]. cbn beta. rewrite E. exact Hin.
Qed.

#[using="Type"] Lemma us_store_file tm nx pt K C oh hs F h e f0 f (P' : file_st -> Prop) :
  In e K -> k_own e = Some h -> fshape f e -> zlength (f_rbuf f) <= k_off e -> P' f ->
  usimS (RUK tm nx pt K C idl (fun l o => WF oh hs F l o /\ In (h, f0) (lc_files l))) (store_fileP h f) (store_fileP h f)
        (eqpost (fun _ => RUK tm nx pt K C idl (WF oh hs (fupd h P' F)))).
Proof.
  intros He Ho Sh LE HP'. unfold store_file. apply ru_upd_lc.
  - intros l Hl. apply LCI_files_update; [exact (proj1 (proj2 Sh))| exact Hl].
  - intros s mo [HF [(HO & HND & HW & HFP) Hin]] HL. cbn. pose proof (FI_nodup_files _ _ _ _ _ HF) as ND. split; [eapply FI_store; eauto|]. split; [exact HO|]. split; [cbn; rewrite map_fst_files_update; exact HND|]. split.
    + eapply WS_files; [| exact HW]. cbn. apply map_fst_files_update.
    + cbn. intros h' P f' HP Hin'. apply (In_files_update _ _ _ _ ND) in Hin' as [[Hin' NE]|[E _]].
      * apply In_fupd in HP as [[-> ->]|[HP _]]; [exfalso; exact (NE eq_refl)|]. exact (HFP h' P f' HP Hin').
      * injection E as -> ->. apply In_fupd in HP as [[_ ->]|[_ NE]]; [exact HP'| exfalso; exact (NE eq_refl)].
Qed.

(* [comment removed for export] *)
Definition PW (e : kfe) (c : list byte) (f : file_st) : Prop :=
  WT (Some e) f /\ match k_data e with Some d => d ++ to_bytes (f_wbuf f) = c | None => True end.
Definition PR (e : kfe) (d : list byte) (p : Z) (f : file_st) : Prop := RT e d f /\ pos e f = p.

#[using="Type"] Lemma kapp_data_none e fl : k_data e = None -> kapp e fl = e.
Proof. intros H. unfold kapp. rewrite H. reflexivity. Qed.

(* [comment removed for export] *)
#[using="Type"] Theorem us_fwrite tm nx pt K C oh hs F h e c s :
  In e K -> k_own e = Some h -> kwr e -> In h hs -> In (h, PW e c) F -> zlength s < 2^61 ->
  match k_data e with Some _ => Z.of_nat (length c) + zlength s <= FLEN | None => True end ->
  usimS (RUK tm nx pt K C idl (WF oh hs F)) (s_fwrite HOG h s) (s_fwrite HOC h s)
        (eqpost (fun r => fun gh sG moG sC moC => exists fl, r = zlength s /\
           RUK tm nx pt (kset (kapp e fl) K) C idl (WF oh hs (fupd h (PW (kapp e fl) (c ++ to_bytes s)) F)) gh sG moG sC moC)).
Proof.
  intros He Ho KD Hh HP Hs HB. unfold s_fwrite, fwrite, with_file_. rewrite ?eqbG, ?eqbC.
  eapply ruk_bindX with (K1 := fun fl _ => kset (kapp e fl) K) (C1 := fun _ _ => C) (g1 := fun _ _ => idl)
    (W1 := fun fl _ => WF oh hs (fupd h (PW (kapp e fl) (c ++ to_bytes s)) F)) (phi := fun fl _ => True).
  2:{ intros fl [] _. apply ru_ret. intros gh sG moG sC moC HR. exists fl. split; [reflexivity| exact HR]. }
  eapply ruk_bind with (K1 := fun _ => K) (C1 := fun _ => C) (g1 := fun _ => idl); [apply (us_lookup_file tm nx pt K C oh hs F h e _ He Ho Hh HP)|].
  intros f0 (Sh & LE & FOK & [HW0 HC0]). cbn beta.
  pose proof (fshape_WT _ _ Sh KD) as HWT.
  assert (HBw : wbud (Some e) f0 (zlength s)).
  { unfold wbud. destruct (k_data e) as [d|]; [| exact I]. apply (f_equal (@length byte)) in HC0. rewrite length_app in HC0.
    pose proof (zlength_to_bytes (f_wbuf f0)). unfold zlength in *. lia. }
  eapply (ruk_bindX tm nx pt K C idl _ _ (fun fl _ => kset (kapp e fl) K) (fun _ _ => C) (fun _ _ => idl) (fun _ _ => fun l o => WF oh hs F l o /\ In (h, f0) (lc_files l))).
  - eapply ru_post; [apply (us_fwrite_file tm nx pt K C idl _ (Some e) f0 s (tgt_ok_some e K He) HWT Hs HBw)|].
    intros f' gh sG moG sC moC (fl & W' & E' & B' & FD' & BU' & H'). exists fl. split; [exact (conj W' (conj E' (conj B' (conj FD' BU'))))| exact H'].
  - intros fl f' (W' & E' & B' & FD' & BU'). cbn beta. cbn [etgt] in W'.
    apply ruk_use. intros l mo HFl.
    pose proof (FI_kwf _ _ _ _ _ HFl (kapp e fl) ltac:(apply (In_kset_new _ K e); [exact He| symmetry; apply kapp_fd])) as (_ & KO & _).
    eapply ru_post; [apply (us_store_file tm nx pt (kset (kapp e fl) K) C oh hs F h (kapp e fl) f0 f' (PW (kapp e fl) (c ++ to_bytes s)))|].
    + apply (In_kset_new _ K e); [exact He| symmetry; apply kapp_fd].
    + rewrite kapp_own. exact Ho.
    + apply WT_fshape. exact W'.
    + destruct W' as [(_ & _ & R3 & _) _]. rewrite R3. unfold zlength; cbn. exact KO.
    + split; [exact W'|]. unfold kapp. destruct (k_data e) as [d|] eqn:ED; cbn; [| rewrite ED; exact I]. rewrite ?ED in HC0. rewrite <- HC0, <- app_assoc, E', app_assoc. reflexivity.
    + intros [] gh sG moG sC moC H. exists fl. split; [exact I| exact H].
Qed.

(* [comment removed for export] *)
#[using="Type"] Theorem us_fprintf tm nx pt K C oh hs F h e c ps :
  In e K -> k_own e = Some h -> kwr e -> In h hs -> In (h, PW e c) F -> Forall (fun p => zlength p < 2^61) ps ->
  match k_data e with Some _ => Z.of_nat (length c) + zlength (concat ps) <= FLEN | None => True end ->
  usimS (RUK tm nx pt K C idl (WF oh hs F)) (s_fprintf HOG h ps) (s_fprintf HOC h ps)
        (eqpost (fun _ => fun gh sG moG sC moC => exists fl,
           RUK tm nx pt (kset (kapp e fl) K) C idl (WF oh hs (fupd h (PW (kapp e fl) (c ++ to_bytes (concat ps))) F)) gh sG moG sC moC)).
Proof.
  intros He Ho KD Hh HP Hps HB. unfold s_fprintf, fprintf, with_file_. rewrite ?eqbG, ?eqbC. pose proof (zlength_nonneg (concat ps)) as NC.
  eapply ruk_bind with (K1 := fun _ => K) (C1 := fun _ => C) (g1 := fun _ => idl); [apply (us_lookup_file tm nx pt K C oh hs F h e _ He Ho Hh HP)|].
  intros f0 (Sh & LE & FOK & [HW0 HC0]). cbn beta.
  pose proof (fshape_WT _ _ Sh KD) as HWT.
  assert (HBw : wbud (Some e) f0 (zlength (concat ps))).
  { unfold wbud. destruct (k_data e) as [d|]; [| exact I]. apply (f_equal (@length byte)) in HC0. rewrite length_app in HC0.
    pose proof (zlength_to_bytes (f_wbuf f0)). unfold zlength in *. lia. }
  eapply (ruk_bindX tm nx pt K C idl _ _ (fun fl _ => kset (kapp e fl) K) (fun _ _ => C) (fun _ _ => idl) (fun _ _ => fun l o => WF oh hs F l o /\ In (h, f0) (lc_files l))).
  - eapply ru_post; [apply (us_vfprintf tm nx pt K C idl _ (Some e) f0 ps (tgt_ok_some e K He) HWT Hps HBw)|].
    intros f' gh sG moG sC moC (fl & W' & E' & B' & FD' & BU' & H'). exists fl. split; [exact (conj W' (conj E' (conj B' (conj FD' BU'))))| exact H'].
  - intros fl f' (W' & E' & B' & FD' & BU'). cbn beta. cbn [etgt] in W'.
    apply ruk_use. intros l mo HFl.
    pose proof (FI_kwf _ _ _ _ _ HFl (kapp e fl) ltac:(apply (In_kset_new _ K e); [exact He| symmetry; apply kapp_fd])) as (_ & KO & _).
    eapply ru_post; [apply (us_store_file tm nx pt (kset (kapp e fl) K) C oh hs F h (kapp e fl) f0 f' (PW (kapp e fl) (c ++ to_bytes (concat ps))))|].
    + apply (In_kset_new _ K e); [exact He| symmetry; apply kapp_fd].
    + rewrite kapp_own. exact Ho.
    + apply WT_fshape. exact W'.
    + destruct W' as [(_ & _ & R3 & _) _]. rewrite R3. unfold zlength; cbn. exact KO.
    + split; [exact W'|]. unfold kapp. destruct (k_data e) as [d|] eqn:ED; cbn; [| rewrite ED; exact I]. rewrite ?ED in HC0. rewrite <- HC0, <- app_assoc, E', app_assoc. reflexivity.
    + intros [] gh sG moG sC moC H. exists fl. exact H.
Qed.

(* [comment removed for export] *)
#[using="Type"] Theorem us_fread tm nx pt K C oh hs F h e d p destG destC n :
  In e K -> k_own e = Some h -> In h hs -> In (h, PR e d p) F -> tm !! h = Some FILE_ALLOC ->
  0 <= n < 2^62 -> 0 <= destG -> destG + n < 2^64 ->
  usimS (RUK tm nx pt K C idl (WF oh hs F)) (s_fread HOG h destG n) (s_fread HOC h destC n)
        (eqpost (fun r => fun gh sG moG sC moC => exists off',
           (zlength r <= n /\ (zlength r < n -> p + zlength r = Z.of_nat (length d)) /\ 0 <= p /\ p + zlength r <= Z.of_nat (length d)
            /\ r = dsl d p (zlength r)) /\
           RUK tm nx pt (kset (kat e off') K) C idl (WF oh hs (fupd h (PR (kat e off') d (p + zlength r)) F)) gh sG moG sC moC)).
Proof.
  intros He Ho Hh HP Hk Hn Hd1 Hd2. unfold s_fread, fread, with_file. rewrite ?eqbG, ?eqbC.
  eapply ru_bind2; [apply ru_get|]. intros a b. apply usim_pointwise. intros gh0 sG0 moG0 sC0 moC0 (-> & -> & EL & EO & HR0).
  pose proof (RQ_blk_addr _ _ _ _ _ _ _ _ h FILE_ALLOC (RX_RQ _ _ _ _ _ _ _ _ _ HR0) Hk) as (A1 & A2 & A3).
  eapply ru_pre with (R' := RUK tm nx pt K C idl (WF oh hs F)); [| intros ? ? ? ? ? (-> & -> & -> & -> & ->); exact HR0].
  eapply ruk_bind with (K1 := fun _ => K) (C1 := fun _ => C) (g1 := fun _ => idl); [apply (us_lookup_file tm nx pt K C oh hs F h e _ He Ho Hh HP)|].
  intros f0 (Sh & LE & FOK & [HRT0 HP0]). cbn beta.
  pose proof HRT0 as (S1 & S2 & S3 & S4 & S5 & S6 & S7).
  eapply (ruk_bindX tm nx pt K C idl _
            (fun off' r => zlength (fst r) <= n /\ RT (kat e off') d (snd r) /\ pos (kat e off') (snd r) = pos e f0 + zlength (fst r)
                           /\ (zlength (fst r) < n -> pos (kat e off') (snd r) = Z.of_nat (length d)) /\ f_bufsize (snd r) = f_bufsize f0
                           /\ fst r = dsl d p (zlength (fst r)))
            (fun off' _ => kset (kat e off') K) (fun _ _ => C) (fun _ _ => idl) (fun _ _ => fun l o => WF oh hs F l o /\ In (h, f0) (lc_files l))).
  - eapply ru_post; [apply (us_fread_file tm nx pt K C idl _ e d f0 (file_buf_addr HOG sG0 h) (file_buf_addr HOC sC0 h) destG destC n He HRT0 Hn)|].
    + unfold file_buf_addr, FILE_BUF_OFF, FILE_ALLOC in *. lia.
    + exact Hd1.
    + exact Hd2.
    + intros r gh sG moG sC moC Q. cbv zeta in Q. destruct Q as (Q1 & QC & Q2 & Q3 & Q4 & Q5 & Q6).
      exists (pos e f0 + zlength (fst r) + zlength (f_rbuf (snd r))). split; [| exact Q6]. rewrite HP0 in QC. exact (conj Q1 (conj Q2 (conj Q3 (conj Q4 (conj Q5 QC))))).
  - intros off' [r f'] (Q1 & Q2 & Q3 & Q4 & Q5 & QC). cbn [fst snd] in *.
    eapply ruk_bind with (K1 := fun _ => kset (kat e off') K) (C1 := fun _ => C) (g1 := fun _ => idl) (W1 := fun _ => WF oh hs (fupd h (PR (kat e off') d (p + zlength r)) F)) (phi := fun _ => True).
    + eapply ru_post; [apply (us_store_file tm nx pt (kset (kat e off') K) C oh hs F h (kat e off') f0 f' (PR (kat e off') d (p + zlength r)))|].
      * apply (In_kset_new _ K e); [exact He| reflexivity].
      * unfold kat, kmove. destruct e; cbn in *. exact Ho.
      * exact (proj1 Q2).
      * destruct Q2 as (_ & _ & _ & R4 & _). lia.
      * split; [exact Q2|]. rewrite Q3, HP0. reflexivity.
      * intros [] ? ? ? ? ? H. exact (conj I H).
    + intros [] _. cbn beta. apply ru_ret. intros gh sG moG sC moC HR. exists off'. split; [| exact HR].
      rewrite HP0 in *. split; [exact Q1|]. split; [intros LT; rewrite <- Q3; exact (Q4 LT)|].
      destruct Q2 as (_ & _ & _ & R4 & R5 & _). unfold pos in *. split; [unfold pos in HP0; lia|]. split; [lia| exact QC].
Qed.

#[using="Type"] Lemma us_ferror tm nx pt K C oh hs F h e P :
  In e K -> k_own e = Some h -> In h hs -> In (h, P) F ->
  usimS (RUK tm nx pt K C idl (WF oh hs F)) (s_ferror HOG h) (s_ferror HOC h)
        (eqpost (fun r => fun gh sG moG sC moC => r = false /\ RUK tm nx pt K C idl (WF oh hs F) gh sG moG sC moC)).
Proof.
  intros He Ho Hh HP. unfold s_ferror, ferror. rewrite ?eqbG, ?eqbC.
  eapply ruk_bind with (K1 := fun _ => K) (C1 := fun _ => C) (g1 := fun _ => idl); [apply (us_lookup_file tm nx pt K C oh hs F h e _ He Ho Hh HP)|].
  intros f _. cbn beta. eapply ruk_frame_weaken; [| apply ruk_ret; reflexivity]. intros l o [H _]; exact H.
Qed.

#[using="Type"] Lemma us_fileno tm nx pt K C oh hs F h e P :
  In e K -> k_own e = Some h -> In h hs -> In (h, P) F ->
  usimS (RUK tm nx pt K C idl (WF oh hs F)) (s_fileno HOG h) (s_fileno HOC h)
        (eqpost (fun r => fun gh sG moG sC moC => r = k_fd e /\ RUK tm nx pt K C idl (WF oh hs F) gh sG moG sC moC)).
Proof.
  intros He Ho Hh HP. unfold s_fileno, fileno. rewrite ?eqbG, ?eqbC.
  eapply ruk_bind with (K1 := fun _ => K) (C1 := fun _ => C) (g1 := fun _ => idl); [apply (us_lookup_file tm nx pt K C oh hs F h e _ He Ho Hh HP)|].
  intros f (Sh & _). cbn beta. eapply ruk_frame_weaken; [| apply ruk_ret; exact (proj1 (proj2 (proj2 Sh)))]. intros l o [H _]; exact H.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma ruk_frame_intro {A} tm nx pt K C g (W W' : libc_st hptr -> option hptr -> Prop) (m : Monad.M PSG A) (m' : Monad.M PSC A) Q :
  (forall l o mo, FI nx K C (g l) mo -> W l o -> W' l o) -> usimS (RUK tm nx pt K C g W') m m' Q -> usimS (RUK tm nx pt K C g W) m m' Q.
Proof. intros HW H. eapply ru_pre; [exact H|]. intros gh sG moG sC moC [HR [HF X]]. split; [exact HR|]. split; [exact HF| exact (HW _ _ _ HF X)]. Qed.

#[using="Type"] Lemma kset_snoc_new K e0 e1 : (forall x, In x K -> k_fd x <> k_fd e0) -> k_fd e1 = k_fd e0 -> kset e1 (K ++ [e0]) = K ++ [e1].
Proof.
  intros HK E. unfold kset. rewrite map_app. cbn. rewrite <- E, Z.eqb_refl. f_equal.
  rewrite <- (map_id K) at 2. apply map_ext_in. intros x Hx. rewrite E. rewrite (proj2 (Z.eqb_neq _ _) (HK x Hx)). reflexivity.
Qed.

#[using="Type"] Lemma us_set_errno tm nx pt K C oh hs F err :
  usimS (RUK tm nx pt K C idl (WF oh hs F)) (set_errno ps_libc set_libc err) (set_errno ps_libc set_libc err) (eqpost (fun _ => RUK tm nx pt K C idl (WF oh hs F))).
Proof.
  unfold set_errno. apply ru_upd_lc; [intros l Hl; apply LCI_errno; exact Hl|].
  intros s mo [HF (HO & HND & HW & HFP)] HL. cbn. split; [apply FI_errno; exact HF|]. split; [exact HO|]. split; [exact HND|]. split; [eapply WS_files; [| exact HW]; reflexivity| exact HFP].
Qed.

#[using="Type"] Lemma us_get_errno tm nx pt K C oh hs F :
  usimS (RUK tm nx pt K C idl (WF oh hs F)) (s_get_errno : Monad.M PSG Z) s_get_errno (eqpost (fun _ => RUK tm nx pt K C idl (WF oh hs F))).
Proof.
  unfold s_get_errno, get_errno. eapply ruk_bind with (K1 := fun _ => K) (C1 := fun _ => C) (g1 := fun _ => idl); [apply ruk_rd_lc|].
  intros l _. cbn beta. eapply ruk_frame_weaken; [| apply ru_ret; intros; eassumption]. intros l0 o [H _]; exact H.
Qed.

(* [comment removed for export] *)
Definition fopen_tail {H} (HO : HeapOps H hptr) (wr : bool) (fd : Z) : Monad.M (PState H hptr) (option hptr) :=
  po <- pmalloc HO FILE_ALLOC ;;
  match po with
  | None => set_errno ps_libc set_libc ENOMEM ;;; _ <- msys (NClose fd) dec_close ;; mret None
  | Some p =>
      (if wr then r <- msys (NIoctl fd TIOCGWINSZ) dec_ioctl ;; match r with SErr _ => mret tt | SVal _ => munr end else mret tt) ;;;
      upd_lc ps_libc set_libc (fun l => set_files ((p, fdopen_file fd wr) :: lc_files l) l) ;;;
      mret (Some p)
  end.

#[using="Type"] Lemma fopen_unfold {H} (HO : HeapOps H hptr) name wr :
  s_fopen HO name wr =
  (r <- msys (if wr then NOpenW (to_bytes name) FOPEN_MODE else NOpen (to_bytes name)) (if wr then dec_openw else dec_open) ;;
   match r with SErr e => set_errno ps_libc set_libc e ;;; mret None | SVal fd => fopen_tail HO wr fd end).
Proof. reflexivity. Qed.

#[using="Type"] Lemma fshape_fdopen fd (wr : bool) e : k_fd e = fd -> (if wr then k_kind e = KW \/ k_kind e = KNull else k_kind e = KR) -> fshape (fdopen_file fd wr) e.
Proof.
  intros E K0. unfold fshape, fdopen_file, file_ok, BUFSIZ; fsimp. destruct wr; [destruct K0 as [K0|K0]|]; rewrite K0; cbn; unfold zlength; cbn; repeat split; auto; try lia; try (intros; reflexivity).
Qed.

#[using="Type"] Lemma us_fopen_tail tm nx pt K C oh hs F (wr : bool) e0 (Pnew : file_st -> Prop) :
  In e0 K -> k_own e0 = None -> (if wr then k_kind e0 = KW \/ k_kind e0 = KNull else k_kind e0 = KR) -> 0 <= k_off e0 ->
  Pnew (fdopen_file (k_fd e0) wr) ->
  pre_malloc tm pt FILE_ALLOC ->
  usimS (RUK tm nx pt K C idl (WF oh hs F)) (fopen_tail HOG wr (k_fd e0)) (fopen_tail HOC wr (k_fd e0))
        (eqpost (fun r => fun gh sG moG sC moC => r = Some nx /\
           RX (<[nx := FILE_ALLOC]> tm) (N.succ nx) (pt + n1 FILE_ALLOC) (UK (N.succ nx) (kset (kown nx e0) K) C idl (WF oh (nx :: hs) (fupd nx Pnew F))) gh sG moG sC moC)).
Proof.
  intros He Ho KD KO HPn HPRE. unfold fopen_tail.
  (* [comment removed for export] *)
  apply ruk_use. intros l0 mo0 HF0.
  assert (POWN : forall x h, In x K -> k_own x = Some h -> h <> nx).
  { intros x h Hx Ox E. pose proof (FI_owner _ _ _ _ _ HF0 x h Hx Ox). subst h. lia. }
  apply (ruk_frame_intro tm nx pt K C idl (WF oh hs F) (fun l o => WF oh hs F l o /\ ~ In nx (map fst (lc_files l)))).
  { intros l o mo HF HW. split; [exact HW|]. intros Hin. apply in_map_iff in Hin as ([h f] & E & Hin). cbn in E; subst h.
    destruct (FI_file _ _ _ _ _ HF nx f Hin) as [Hlt _]. lia. }
  eapply ru_bind.
  { eapply ru_post; [apply (ru_pmalloc tm nx pt (UK nx K C idl (fun l o => WF oh hs F l o /\ ~ In nx (map fst (lc_files l)))) _ FILE_ALLOC (UK_stable _ _ _ _ _) HPRE)|].
    intros a ? ? ? ? ? [Ha H]. exact (conj Ha H). }
  intros po. apply usim_pure. intros ->. cbn iota.
  (* [comment removed for export] *)
  apply (ru_pre _ (RX (<[nx := FILE_ALLOC]> tm) (N.succ nx) (pt + n1 FILE_ALLOC) (UK (N.succ nx) K C idl (fun l o => WF oh hs F l o /\ ~ In nx (map fst (lc_files l)))))).
  2:{ intros gh sG moG sC moC [HR [HF HW]]. split; [exact HR|]. split; [apply (FI_mono_nx nx); [lia| exact HF]| exact HW]. }
  eapply ruk_bind with (phi := fun _ => True) (K1 := fun _ => K) (C1 := fun _ => C) (g1 := fun _ => idl) (W1 := fun _ => fun l o => WF oh hs F l o /\ ~ In nx (map fst (lc_files l))).
  { destruct wr.
    - eapply ruk_bind with (K1 := fun _ => K) (C1 := fun _ => C) (g1 := fun _ => idl) (W1 := fun _ => fun l o => WF oh hs F l o /\ ~ In nx (map fst (lc_files l))).
      + eapply ruk_nodeK; [exact I| apply fn_ioctl|]. intros r l mo [HF Hr]. exact (conj Hr HF).
      + intros r [err ->]. cbn beta. apply ruk_ret. exact I.
    - apply ruk_ret. exact I. }
  intros [] _. cbn beta.
  eapply ruk_bind with (phi := fun _ => True) (K1 := fun _ => kset (kown nx e0) K) (C1 := fun _ => C) (g1 := fun _ => idl) (W1 := fun _ => WF oh (nx :: hs) (fupd nx Pnew F)).
  { eapply ru_post; [apply ru_upd_lc|]; [intros l Hl; apply LCI_files_cons; [apply fdopen_file_ok| exact Hl]| | intros [] ? ? ? ? ? H; exact (conj I H)].
    intros s mo [HF [(HO & HND & HW & HFP) NI]] HL. cbn. split.
    - eapply FI_adopt; [exact HF| exact He| exact Ho| lia| lia| exact NI| intros x Hx Ox; exact (POWN x nx Hx Ox eq_refl)| |].
      + apply fshape_fdopen; [reflexivity| cbn; exact KD].
      + unfold fdopen_file; fsimp. unfold zlength; cbn. exact KO.
    - split; [exact HO|]. split; [cbn; constructor; [exact NI| exact HND]|]. split.
      + intros h [<-|Hh]; cbn; [left; reflexivity| right; apply HW; exact Hh].
      + intros h P f HP Hin. cbn in Hin. apply In_fupd in HP as [[-> ->]|[HP NE]].
        * destruct Hin as [E|Hin]; [injection E as <-; exact HPn|]. exfalso. apply NI. apply in_map_iff. exists (nx, f). auto.
        * destruct Hin as [E|Hin]; [injection E as -> _; exfalso; exact (NE eq_refl)|]. exact (HFP h P f HP Hin). }
  intros [] _. cbn beta. apply ru_ret. intros gh sG moG sC moC H. split; [reflexivity| exact H].
Qed.

#[using="Type"] Lemma NoDup_snoc_fd K e0 x : List.NoDup (map k_fd (K ++ [e0])) -> In x K -> k_fd x <> k_fd e0.
Proof.
  rewrite map_app. cbn. induction K as [|y K IH]; intros ND Hx; [destruct Hx|]. cbn in ND. inversion ND as [|? ? NI ND']; subst.
  destruct Hx as [<-|Hx]; [| exact (IH ND' Hx)]. intros E. apply NI. rewrite in_app_iff. right. left. exact (eq_sym E).
Qed.

#[using="Type"] Lemma RX_fopen_fix tm nb nx' pt h K e0 C W gh sG moG sC moC :
  RX tm nx' pt (UK nb (kset (kown h e0) (K ++ [e0])) C idl W) gh sG moG sC moC ->
  RX tm nx' pt (UK nb (K ++ [kown h e0]) C idl W) gh sG moG sC moC.
Proof.
  intros [HR [HF HW]].
  assert (EK : kset (kown h e0) (K ++ [e0]) = K ++ [kown h e0]).
  { apply kset_snoc_new; [| reflexivity]. intros x Hx. pose proof (proj1 (FI_KP _ _ _ _ _ HF)) as ND. rewrite map_fd_kset in ND by (right; exact I).
    exact (NoDup_snoc_fd K e0 x ND Hx). }
  rewrite EK in HF. exact (conj HR (conj HF HW)).
Qed.

(* [comment removed for export] *)
#[using="Type"] Theorem us_fopen_w tm nx pt K C oh hs F name (track : bool) :
  K_clear K (to_bytes name) -> track = negb (path_eqb (to_bytes name) devnull_path) ->
  pre_malloc tm pt FILE_ALLOC ->
  usimS (RUK tm nx pt K C idl (WF oh hs F)) (s_fopen HOG name true) (s_fopen HOC name true)
        (eqpost (fun r => fun gh sG moG sC moC =>
           match r with
           | None => RUK tm nx pt K C idl (WF oh hs F) gh sG moG sC moC
           | Some p => p = nx /\ exists fd, 3 <= fd <= 4096 /\
               let e := mkKfe fd (wkind (to_bytes name)) (to_bytes name) (Some nx) (if track then Some [] else None) 0 in
               RX (<[nx := FILE_ALLOC]> tm) (N.succ nx) (pt + n1 FILE_ALLOC) (UK (N.succ nx) (K ++ [e]) (cdel (to_bytes name) C) idl (WF oh (nx :: hs) (fupd nx (PW e []) F))) gh sG moG sC moC
           end)).
Proof.
  intros HC HTR HPRE. rewrite (fopen_unfold HOG name true), (fopen_unfold HOC name true).
  assert (TRK : to_bytes name = devnull_path -> track = false) by (intros E; rewrite HTR, E, path_eqb_refl; reflexivity).
  assert (KWR : forall fd, kwr (mkKfe fd (wkind (to_bytes name)) (to_bytes name) (Some nx) (if track then Some [] else None) 0)).
  { intros fd. unfold kwr, wkind. cbn [k_kind k_data]. rewrite HTR. destruct (path_eqb (to_bytes name) devnull_path); cbn [negb]; [right; reflexivity| left; split; [reflexivity| discriminate]]. }
  eapply ruk_bind with (phi := fun r => match r with SErr _ => True | SVal fd => 3 <= fd <= 4096 end)
    (K1 := fun r => match r with SErr _ => K | SVal fd => K ++ [mkKfe fd (wkind (to_bytes name)) (to_bytes name) None (if track then Some [] else None) 0] end)
    (C1 := fun r => match r with SErr _ => C | SVal _ => cdel (to_bytes name) C end) (g1 := fun _ => idl) (W1 := fun _ => WF oh hs F).
  { eapply ruk_nodeK; [exact I| apply (fn_openw nx K C (to_bytes name) FOPEN_MODE track HC TRK)|]. intros [e|fd] l mo X; cbn in X; [exact (conj I (proj1 X))| exact (conj (proj1 X) (proj1 (proj2 X)))]. }
  intros [err|fd] Hfd; cbn beta.
  - eapply ruk_bind with (K1 := fun _ => K) (C1 := fun _ => C) (g1 := fun _ => idl) (W1 := fun _ => WF oh hs F) (phi := fun _ => True).
    + eapply ru_post; [apply us_set_errno|]. intros [] ? ? ? ? ? H; exact (conj I H).
    + intros [] _. apply ru_ret. intros; assumption.
  - set (e0 := mkKfe fd (wkind (to_bytes name)) (to_bytes name) None (if track then Some [] else None) 0).
    change fd with (k_fd e0).
    eapply ru_post; [apply (us_fopen_tail tm nx pt _ _ oh hs F true e0 (PW (kown nx e0) []))|].
    + apply in_app_iff. right. left. reflexivity.
    + reflexivity.
    + cbn [k_kind e0]. unfold wkind. destruct (path_eqb (to_bytes name) devnull_path); [right| left]; reflexivity.
    + cbn. lia.
    + split; [apply fshape_WT; [apply fshape_fdopen; [reflexivity| cbn [k_kind kown e0]; unfold wkind; destruct (path_eqb (to_bytes name) devnull_path); [right| left]; reflexivity]| exact (KWR fd)]|].
      cbn. destruct track; cbn; [reflexivity| exact I].
    + exact HPRE.
    + intros r gh sG moG sC moC [-> H]. split; [reflexivity|]. exists fd. split; [exact Hfd|]. exact (RX_fopen_fix _ _ _ _ _ _ _ _ _ _ _ _ _ _ H).
Qed.

(* [comment removed for export] *)
#[using="Type"] Theorem us_fopen_r tm nx pt K C oh hs F name d :
  K_clear K (to_bytes name) -> clookup C (to_bytes name) = Some d -> to_bytes name <> dot_path ->
  pre_malloc tm pt FILE_ALLOC ->
  usimS (RUK tm nx pt K C idl (WF oh hs F)) (s_fopen HOG name false) (s_fopen HOC name false)
        (eqpost (fun r => fun gh sG moG sC moC =>
           match r with
           | None => RUK tm nx pt K C idl (WF oh hs F) gh sG moG sC moC
           | Some p => p = nx /\ exists fd, 3 <= fd <= 4096 /\
               let e := mkKfe fd KR (to_bytes name) (Some nx) (Some d) 0 in
               RX (<[nx := FILE_ALLOC]> tm) (N.succ nx) (pt + n1 FILE_ALLOC) (UK (N.succ nx) (K ++ [e]) (cdel (to_bytes name) C) idl (WF oh (nx :: hs) (fupd nx (PR e d 0) F))) gh sG moG sC moC
           end)).
Proof.
  intros HC HCd ND HPRE. rewrite (fopen_unfold HOG name false), (fopen_unfold HOC name false).
  eapply ruk_bind with (phi := fun r => match r with SErr _ => True | SVal fd => 3 <= fd <= 4096 end)
    (K1 := fun r => match r with SErr _ => K | SVal fd => K ++ [mkKfe fd KR (to_bytes name) None (Some d) 0] end)
    (C1 := fun r => match r with SErr _ => C | SVal _ => cdel (to_bytes name) C end) (g1 := fun _ => idl) (W1 := fun _ => WF oh hs F).
  { eapply ruk_nodeK; [exact I| apply (fn_open_known nx K C (to_bytes name) d HC HCd ND)|]. intros [e|fd] l mo X; cbn in X; [exact (conj I (proj1 X))| exact (conj (proj1 X) (proj2 X))]. }
  intros [err|fd] Hfd; cbn beta.
  - eapply ruk_bind with (K1 := fun _ => K) (C1 := fun _ => C) (g1 := fun _ => idl) (W1 := fun _ => WF oh hs F) (phi := fun _ => True).
    + eapply ru_post; [apply us_set_errno|]. intros [] ? ? ? ? ? H; exact (conj I H).
    + intros [] _. apply ru_ret. intros; assumption.
  - set (e0 := mkKfe fd KR (to_bytes name) None (Some d) 0).
    change fd with (k_fd e0).
    pose proof (clookup_In _ _ _ HCd) as HinC.
    eapply ru_post; [apply (us_fopen_tail tm nx pt _ _ oh hs F false e0 (PR (kown nx e0) d 0))|].
    + apply in_app_iff. right. left. reflexivity.
    + reflexivity.
    + exact eq_refl.
    + cbn. lia.
    + split; [| unfold pos, fdopen_file; fsimp; unfold zlength; cbn; reflexivity].
      unfold RT. split; [apply fshape_fdopen; [reflexivity| exact eq_refl]|]. cbn. unfold fdopen_file, pos; fsimp. unfold zlength; cbn. repeat split; try lia; try (intros; discriminate).
    + exact HPRE.
    + intros r gh sG moG sC moC [-> H]. split; [reflexivity|]. exists fd. split; [exact Hfd|]. exact (RX_fopen_fix _ _ _ _ _ _ _ _ _ _ _ _ _ _ H).
Qed.

Definition hrem (h : hptr) (hs : list hptr) : list hptr := List.filter (fun h' => negb (N.eqb h' h)) hs.
#[using="Type"] Lemma In_hrem h hs h' : In h' (hrem h hs) <-> In h' hs /\ h' <> h.
Proof.
  unfold hrem. rewrite filter_In. split.
  - intros [H1 H2]. split; [exact H1|]. intros ->. rewrite N.eqb_refl in H2. discriminate.
  - intros [H1 NE]. split; [exact H1|]. destruct (N.eqb_spec h' h); [contradiction| reflexivity].
Qed.


#[using="Type"] Lemma In_files_remove_keep (fs : list (hptr * file_st)) h h' f : In (h', f) fs -> h' <> h -> In (h', f) (files_remove N.eqb fs h).
Proof.
  induction fs as [|[k v] fs IH]; intros Hin NE; [destruct Hin|]. cbn. destruct (N.eqb_spec k h) as [->|NK].
  - destruct Hin as [E|Hin]; [injection E as -> ->; exfalso; exact (NE eq_refl)| exact Hin].
  - destruct Hin as [E|Hin]; [left; exact E| right; exact (IH Hin NE)].
Qed.
#[using="Type"] Lemma In_files_remove_sub (fs : list (hptr * file_st)) h hf : In hf (files_remove N.eqb fs h) -> In hf fs.
Proof.
  induction fs as [|[k v] fs IH]; cbn; [tauto|]. destruct (N.eqb k h); [intros H; right; exact H|].
  intros [E|H]; [left; exact E| right; exact (IH H)].
Qed.

#[using="Type"] Lemma files_remove_notin (fs : list (hptr * file_st)) h : ~ In h (map fst fs) -> files_remove N.eqb fs h = fs.
Proof.
  induction fs as [|[k v] fs IH]; intros NI; [reflexivity|]. cbn. destruct (N.eqb_spec k h) as [->|NE]; [exfalso; apply NI; left; reflexivity|].
  rewrite IH; [reflexivity|]. intros Hin. apply NI. right. exact Hin.
Qed.
#[using="Type"] Lemma files_remove_idem (fs : list (hptr * file_st)) h : List.NoDup (map fst fs) -> files_remove N.eqb (files_remove N.eqb fs h) h = files_remove N.eqb fs h.
Proof.
  induction fs as [|[k v] fs IH]; intros ND; [reflexivity|]. cbn in ND. inversion ND as [|? ? NI ND']; subst. cbn.
  destruct (N.eqb_spec k h) as [->|NE]; [apply files_remove_notin; exact NI|]. cbn. rewrite (proj2 (N.eqb_neq _ _) NE). rewrite (IH ND'). reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma us_fclose_tail tm nx pt K C oh hs F h e' f0 n :
  k_own e' = Some h -> oh <> Some h -> pre_free tm h n ->
  usimS (RUK tm nx pt K C (fun l => lrem e' l) (fun l o => WF oh hs F l o /\ In (h, f0) (lc_files l)))
        (upd_lc ps_libc set_libc (fun l => set_files (files_remove N.eqb (lc_files l) h) l) ;;; pfree HOG h)
        (upd_lc ps_libc set_libc (fun l => set_files (files_remove N.eqb (lc_files l) h) l) ;;; pfree HOC h)
        (eqpost (fun _ => RX (delete h tm) nx pt (UK nx K C idl (WF oh (hrem h hs) (fdel h F))))).
Proof.
  intros Ho NOH HPRE.
  eapply ruk_bind with (phi := fun _ => True) (K1 := fun _ => K) (C1 := fun _ => C) (g1 := fun _ => idl) (W1 := fun _ => WF oh (hrem h hs) (fdel h F)).
  - eapply ru_post; [apply ru_upd_lc|]; [intros l Hl; apply LCI_files_remove; exact Hl| | intros [] ? ? ? ? ? H; exact (conj I H)].
    intros s mo [HF [(HO & HND & HW & HFP) Hin]] HL. cbn. unfold lrem in HF. rewrite Ho in HF. split; [exact HF|]. split; [exact HO|]. split; [cbn; apply NoDup_files_remove; exact HND|]. split.
    + intros h' Hh'. apply In_hrem in Hh' as [Hh' NE]. pose proof (HW h' Hh') as X. apply in_map_iff in X as ([h'' f] & E & X). cbn in E; subst h''.
      apply in_map_iff. exists (h', f). split; [reflexivity|]. cbn. apply In_files_remove_keep; [exact X| exact NE].
    + intros h' P f HP Hin'. apply In_fdel in HP as [HP NE]. cbn in Hin'. apply In_files_remove_sub in Hin'. exact (HFP h' P f HP Hin').
  - intros [] _. cbn beta. eapply usim_post; [apply (ru_pfree tm nx pt _ _ h n (UK_stable _ _ _ _ _) HPRE)|]. intros [] [] ? ? ? ? ? [_ H]. split; [reflexivity| exact H].
Qed.

#[using="Type"] Lemma fclose_unfold {H} (HO : HeapOps H hptr) h : ho_eqb HO = N.eqb ->
  s_fclose HO h = (f <- @lookup_file _ hptr ps_libc N.eqb h ;; fclose_file f ;;; upd_lc ps_libc set_libc (fun l => set_files (files_remove N.eqb (lc_files l) h) l) ;;; pfree HO h).
Proof. intros E. unfold s_fclose, fclose. rewrite E. reflexivity. Qed.

(* [comment removed for export] *)
#[using="Type"] Theorem us_fclose_w tm nx pt K C oh hs F h e c n :
  In e K -> k_own e = Some h -> k_kind e = KW -> In h hs -> In (h, PW e c) F -> oh <> Some h ->
  pre_free tm h n ->
  match k_data e with Some _ => Z.of_nat (length c) <= FLEN | None => True end ->
  usimS (RUK tm nx pt K C idl (WF oh hs F)) (s_fclose HOG h) (s_fclose HOC h)
        (eqpost (fun _ => RX (delete h tm) nx pt (UK nx (kdel (k_fd e) K) (match k_data e with Some _ => (k_path e, c) :: C | None => C end) idl (WF oh (hrem h hs) (fdel h F))))).
Proof.
  intros He Ho KD Hh HP NOH HPRE HBc. rewrite (fclose_unfold HOG h eqbG), (fclose_unfold HOC h eqbC).
  eapply ruk_bind with (K1 := fun _ => K) (C1 := fun _ => C) (g1 := fun _ => idl); [apply (us_lookup_file tm nx pt K C oh hs F h e _ He Ho Hh HP)|].
  intros f0 (Sh & LE & FOK & [HW0 HC0]). cbn beta.
  assert (HBf : tbud (TW e) f0).
  { unfold tbud, wbud. destruct (k_data e) as [d|]; [| exact I]. apply (f_equal (@length byte)) in HC0. rewrite length_app in HC0.
    pose proof (zlength_to_bytes (f_wbuf f0)). unfold zlength in *. lia. }
  eapply ruk_bindX with (phi := fun e' _ => ctgt_e (TW e) f0 = Some e' /\ k_fd e' = k_fd e /\ k_own e' = k_own e /\ k_path e' = k_path e)
    (K1 := fun e' _ => kdel (k_fd e) K) (C1 := fun e' _ => cclose e' C) (g1 := fun e' _ => fun l => lrem e' l) (W1 := fun _ _ => fun l o => WF oh hs F l o /\ In (h, f0) (lc_files l)).
  { eapply ru_post; [apply (us_fclose_file tm nx pt K C idl _ (TW e) f0 e (ltac:(exact He) : tgt_in (TW e) K) HW0 HBf eq_refl)|].
    intros [] ? ? ? ? ? (e' & X1 & X2 & X3 & X4 & H). exists e'. cbn [ftgt_g] in H. exact (conj (conj X1 (conj X2 (conj X3 X4))) H). }
  intros e' [] (X1 & X2 & X3 & X4). cbn [ctgt_e tent ftgt] in X1. injection X1 as <-.
  assert (EC : cclose (kapp e (to_bytes (f_wbuf f0))) C = match k_data e with Some _ => (k_path e, c) :: C | None => C end).
  { unfold cclose, kapp. destruct (k_data e) as [d|] eqn:ED; cbn; [| rewrite ED; reflexivity]. rewrite KD. rewrite HC0. reflexivity. }
  rewrite EC. eapply (us_fclose_tail tm nx pt _ _ oh hs F h _ f0 n); [rewrite kapp_own; exact Ho| exact NOH| exact HPRE].
Qed.

(* [comment removed for export] *)
#[using="Type"] Theorem us_fclose_r tm nx pt K C oh hs F h e d p n :
  In e K -> k_own e = Some h -> In h hs -> In (h, PR e d p) F -> oh <> Some h ->
  pre_free tm h n ->
  usimS (RUK tm nx pt K C idl (WF oh hs F)) (s_fclose HOG h) (s_fclose HOC h)
        (eqpost (fun _ => RX (delete h tm) nx pt (UK nx (kdel (k_fd e) K) ((k_path e, d) :: C) idl (WF oh (hrem h hs) (fdel h F))))).
Proof.
  intros He Ho Hh HP NOH HPRE. rewrite (fclose_unfold HOG h eqbG), (fclose_unfold HOC h eqbC).
  eapply ruk_bind with (K1 := fun _ => K) (C1 := fun _ => C) (g1 := fun _ => idl); [apply (us_lookup_file tm nx pt K C oh hs F h e _ He Ho Hh HP)|].
  intros f0 (Sh & LE & FOK & [HRT0 HP0]). cbn beta. pose proof HRT0 as (S1 & S2 & S3 & _).
  eapply ruk_bindX with (phi := fun e' _ => ctgt_e (TR e d) f0 = Some e' /\ k_fd e' = k_fd e /\ k_own e' = k_own e /\ k_path e' = k_path e)
    (K1 := fun e' _ => kdel (k_fd e) K) (C1 := fun e' _ => cclose e' C) (g1 := fun e' _ => fun l => lrem e' (lrem e l)) (W1 := fun _ _ => fun l o => WF oh hs F l o /\ In (h, f0) (lc_files l)).
  { eapply ru_post; [apply (us_fclose_file tm nx pt K C idl _ (TR e d) f0 e (ltac:(exact He) : tgt_in (TR e d) K) HRT0 I eq_refl)|].
    intros [] ? ? ? ? ? (e' & X1 & X2 & X3 & X4 & H). exists e'. cbn [ftgt_g] in H. exact (conj (conj X1 (conj X2 (conj X3 X4))) H). }
  intros e' [] (X1 & X2 & X3 & X4). cbn [ctgt_e tent ftgt] in X1. injection X1 as <-.
  assert (EC : cclose (kpos e f0) C = (k_path e, d) :: C).
  { unfold cclose, kpos, kmove. rewrite S3. destruct e; cbn in *. rewrite S2. reflexivity. }
  rewrite EC.
  (* [comment removed for export] *)
  eapply ru_pre; [eapply (us_fclose_tail tm nx pt _ _ oh hs F h (kpos e f0) f0 n); [unfold kpos, kmove; destruct e; cbn in *; exact Ho| exact NOH| exact HPRE]|].
  intros gh sG moG sC moC [HR [HF [(HO & HND & HW & HFP) Hin]]]. split; [exact HR|]. split; [| exact (conj (conj HO (conj HND (conj HW HFP))) Hin)].
  revert HF. unfold lrem, kpos, kmove. destruct e; cbn in *. subst. cbn. rewrite (files_remove_idem _ _ HND). intros HF; exact HF.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma stdx_WT f fd : stdx_ok f fd -> WT None f /\ f_fd f = fd.
Proof. intros (S1 & S2 & S3 & S4 & S5 & S6 & S7). split; [| exact S1]. split; [| exact S2]. exact (conj S5 (conj S3 (conj S4 (conj S6 S7)))). Qed.
#[using="Type"] Lemma WT_stdx f fd : WT None f -> f_fd f = fd -> stdx_ok f fd.
Proof. intros [(F1 & F2 & F3 & F4 & F5) C1] E. exact (conj E (conj C1 (conj F2 (conj F3 (conj F1 (conj F4 F5)))))). Qed.

#[using="Type"] Theorem us_printf tm nx pt K C oh hs F ps :
  Forall (fun p => zlength p < 2^61) ps ->
  usimS (RUK tm nx pt K C idl (WF oh hs F)) (s_printf ps : Monad.M PSG unit) (s_printf ps) (eqpost (fun _ => RUK tm nx pt K C idl (WF oh hs F))).
Proof.
  intros Hps. unfold s_printf, printf.
  eapply ruk_bind with (K1 := fun _ => K) (C1 := fun _ => C) (g1 := fun _ => idl); [apply ruk_rd_lc|].
  intros l (HL & [mo HF] & [o HW]). cbn beta. destruct (stdx_WT _ _ (FI_stdout _ _ _ _ _ HF)) as [HWT EFD].
  eapply (ruk_bindX tm nx pt K C idl _ _ (fun _ _ => K) (fun _ _ => C) (fun _ _ => idl) (fun _ _ => fun l' o => WF oh hs F l' o /\ l' = l)).
  - eapply ru_post; [apply (us_vfprintf tm nx pt K C idl _ None (lc_stdout l) ps (tgt_ok_none K) HWT Hps I)|].
    intros f' ? ? ? ? ? (fl & P1 & P2 & P3 & P4 & P5 & H). exists fl. cbn [ktgt] in H. exact (conj (conj P1 (conj P2 (conj P3 (conj P4 P5)))) H).
  - intros fl f' (W' & E' & B' & FD' & _). cbn beta. cbn [etgt] in W'.
    eapply ru_post; [apply ru_upd_lc|]; [intros l0 Hl0; apply LCI_stdout; [exact (proj1 (proj1 W'))| exact Hl0]| | intros [] ? ? ? ? ? H; exact H].
    intros s mo0 [HF0 [(HO & HND & HWS & HFP) <-]] HL0. cbn. split; [apply FI_stdout_upd; [apply WT_stdx; [exact W'| rewrite FD'; exact EFD]| exact HF0]|].
    split; [exact HO|]. split; [exact HND|]. split; [exact HWS| exact HFP].
Qed.

#[using="Type"] Theorem us_eprintf tm nx pt K C oh hs F ps :
  Forall (fun p => zlength p < 2^61) ps ->
  usimS (RUK tm nx pt K C idl (WF oh hs F)) (eprintf ps_libc set_libc ps : Monad.M PSG unit) (eprintf ps_libc set_libc ps) (eqpost (fun _ => RUK tm nx pt K C idl (WF oh hs F))).
Proof.
  intros Hps. unfold eprintf.
  eapply ruk_bind with (K1 := fun _ => K) (C1 := fun _ => C) (g1 := fun _ => idl); [apply ruk_rd_lc|].
  intros l (HL & [mo HF] & [o HW]). cbn beta. destruct (stdx_WT _ _ (FI_stderr _ _ _ _ _ HF)) as [HWT EFD].
  eapply (ruk_bindX tm nx pt K C idl _ _ (fun _ _ => K) (fun _ _ => C) (fun _ _ => idl) (fun _ _ => fun l' o => WF oh hs F l' o /\ l' = l)).
  - eapply ru_post; [apply (us_vfprintf tm nx pt K C idl _ None (lc_stderr l) ps (tgt_ok_none K) HWT Hps I)|].
    intros f' ? ? ? ? ? (fl & P1 & P2 & P3 & P4 & P5 & H). exists fl. cbn [ktgt] in H. exact (conj (conj P1 (conj P2 (conj P3 (conj P4 P5)))) H).
  - intros fl f' (W' & E' & B' & FD' & _). cbn beta. cbn [etgt] in W'.
    eapply ru_post; [apply ru_upd_lc|]; [intros l0 Hl0; apply LCI_stderr; [exact (proj1 (proj1 W'))| exact Hl0]| | intros [] ? ? ? ? ? H; exact H].
    intros s mo0 [HF0 [(HO & HND & HWS & HFP) <-]] HL0. cbn. split; [apply FI_stderr_upd; [apply WT_stdx; [exact W'| rewrite FD'; exact EFD]| exact HF0]|].
    split; [exact HO|]. split; [exact HND|]. split; [exact HWS| exact HFP].
Qed.

#[using="Type"] Theorem us_efwrite tm nx pt K C oh hs F bs :
  zlength bs < 2^61 ->
  usimS (RUK tm nx pt K C idl (WF oh hs F)) (efwrite ps_libc set_libc bs : Monad.M PSG unit) (efwrite ps_libc set_libc bs) (eqpost (fun _ => RUK tm nx pt K C idl (WF oh hs F))).
Proof.
  intros Hbs. unfold efwrite.
  eapply ruk_bind with (K1 := fun _ => K) (C1 := fun _ => C) (g1 := fun _ => idl); [apply ruk_rd_lc|].
  intros l (HL & [mo HF] & [o HW]). cbn beta. destruct (stdx_WT _ _ (FI_stderr _ _ _ _ _ HF)) as [HWT EFD].
  eapply (ruk_bindX tm nx pt K C idl _ _ (fun _ _ => K) (fun _ _ => C) (fun _ _ => idl) (fun _ _ => fun l' o => WF oh hs F l' o /\ l' = l)).
  - eapply ru_post; [apply (us_fwrite_file tm nx pt K C idl _ None (lc_stderr l) bs (tgt_ok_none K) HWT Hbs I)|].
    intros f' ? ? ? ? ? (fl & P1 & P2 & P3 & P4 & P5 & H). exists fl. cbn [ktgt] in H. exact (conj (conj P1 (conj P2 (conj P3 (conj P4 P5)))) H).
  - intros fl f' (W' & E' & B' & FD' & _). cbn beta. cbn [etgt] in W'.
    eapply ru_post; [apply ru_upd_lc|]; [intros l0 Hl0; apply LCI_stderr; [exact (proj1 (proj1 W'))| exact Hl0]| | intros [] ? ? ? ? ? H; exact H].
    intros s mo0 [HF0 [(HO & HND & HWS & HFP) <-]] HL0. cbn. split; [apply FI_stderr_upd; [apply WT_stdx; [exact W'| rewrite FD'; exact EFD]| exact HF0]|].
    split; [exact HO|]. split; [exact HND|]. split; [exact HWS| exact HFP].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Theorem us_remove tm nx pt K C oh hs F path :
  K_clear K (to_bytes path) ->
  usimS (framed (ND (to_bytes path)) (RUK tm nx pt K C idl (WF oh hs F))) (s_remove path : Monad.M PSG Z) (s_remove path)
        (eqpost (fun r => fun gh sG moG sC moC => (r = 0 \/ r = -1) /\ framed (ND (to_bytes path)) (RUK tm nx pt K (if r =? 0 then cdel (to_bytes path) C else C) idl (WF oh hs F)) gh sG moG sC moC)).
Proof.
  intros HC. unfold s_remove, remove.
  (* [comment removed for export] *)
  assert (TAIL : forall (r2 : sret) C2, (match r2 with SErr _ => C2 = C | SVal v => v = 0 /\ C2 = cdel (to_bytes path) C end) ->
            usimS (framed (ND (to_bytes path)) (RUK tm nx pt K C2 idl (WF oh hs F)))
                  (match r2 with SErr e => set_errno ps_libc set_libc e ;;; mret (-1) | SVal _ => mret 0 end : Monad.M PSG Z)
                  (match r2 with SErr e => set_errno ps_libc set_libc e ;;; mret (-1) | SVal _ => mret 0 end)
                  (eqpost (fun r => fun gh sG moG sC moC => (r = 0 \/ r = -1) /\ framed (ND (to_bytes path)) (RUK tm nx pt K (if r =? 0 then cdel (to_bytes path) C else C) idl (WF oh hs F)) gh sG moG sC moC))).
  { intros r2 C2 HC2. eapply usim_post; [apply (usim_ND (to_bytes path) npk _ _ _
        (eqpost (fun r => fun gh sG moG sC moC => (r = 0 \/ r = -1) /\ RUK tm nx pt K (if r =? 0 then cdel (to_bytes path) C else C) idl (WF oh hs F) gh sG moG sC moC)))|].
    - destruct r2 as [err|v].
      + subst C2. eapply ruk_bind with (phi := fun _ => True) (K1 := fun _ => K) (C1 := fun _ => C) (g1 := fun _ => idl) (W1 := fun _ => WF oh hs F); [eapply ru_post; [apply us_set_errno| intros [] ? ? ? ? ? H; exact (conj I H)]|].
        intros [] _. apply ru_ret. intros ? ? ? ? ? H. split; [right; reflexivity| cbn; exact H].
      + destruct HC2 as [-> ->]. apply ru_ret. intros ? ? ? ? ? H. split; [left; reflexivity| cbn; exact H].
    - intros a b gh sG moG sC moC [[-> [Hr HR]] HN]. split; [reflexivity|]. split; [exact Hr|]. exact (conj HR HN). }
  eapply ru_bind.
  { eapply (ruk_nodeK_nd (to_bytes path) tm nx pt K C idl (WF oh hs F) (NUnlink (to_bytes path) false) dec_unlink _ (fun r => match r with SErr _ => True | SVal v => v = 0 end) (fun _ => K)
             (fun r => match r with SErr _ => C | SVal _ => cdel (to_bytes path) C end) (fun _ => idl)); [exact I| apply (fn_unlink nx K C (to_bytes path) false HC)|].
    intros [e|v] l mo [NDP X]; cbn in X; [exact (conj I (conj (proj1 X) NDP))| exact (conj (proj1 X) (conj (proj2 (proj2 X)) NDP))]. }
  intros r. apply usim_pure. intros Hv. destruct r as [err|v]; cbn beta.
  - destruct (err =? EISDIR).
    + (* [comment removed for export] *)
      eapply ru_bind.
      { eapply (ruk_nodeK_nd (to_bytes path) tm nx pt K C idl (WF oh hs F) (NUnlink (to_bytes path) true) dec_unlink _ (fun r => match r with SErr _ => True | SVal v => False end) (fun _ => K)
                 (fun _ => C) (fun _ => idl)); [exact I| apply (fn_unlink nx K C (to_bytes path) true HC)|].
        intros [e|v] l mo [NDP X]; cbn in X; [exact (conj I (conj (proj1 X) NDP))| destruct X as (_ & X & _); discriminate]. }
      intros [err'|v]; apply usim_pure; intros Hv'; [| destruct Hv']. cbn beta. exact (TAIL (SErr err') C eq_refl).
    + apply ru_bind_retl. cbn beta. exact (TAIL (SErr err) C eq_refl).
  - subst v. apply ru_bind_retl. cbn beta. exact (TAIL (SVal 0) (cdel (to_bytes path) C) (conj eq_refl eq_refl)).
Qed.

#[using="Type"] Theorem us_unlink tm nx pt K C oh hs F path :
  K_clear K (to_bytes path) ->
  usimS (framed (ND (to_bytes path)) (RUK tm nx pt K C idl (WF oh hs F))) (s_unlink path : Monad.M PSG Z) (s_unlink path)
        (eqpost (fun r => fun gh sG moG sC moC => (r = 0 \/ r = -1) /\ framed (ND (to_bytes path)) (RUK tm nx pt K (if r =? 0 then cdel (to_bytes path) C else C) idl (WF oh hs F)) gh sG moG sC moC)).
Proof.
  intros HC. unfold s_unlink, unlink.
  eapply ru_bind.
  { eapply (ruk_nodeK_nd (to_bytes path) tm nx pt K C idl (WF oh hs F) (NUnlink (to_bytes path) false) dec_unlink _ (fun r => match r with SErr _ => True | SVal v => v = 0 end) (fun _ => K)
             (fun r => match r with SErr _ => C | SVal _ => cdel (to_bytes path) C end) (fun _ => idl)); [exact I| apply (fn_unlink nx K C (to_bytes path) false HC)|].
    intros [e|v] l mo [NDP X]; cbn in X; [exact (conj I (conj (proj1 X) NDP))| exact (conj (proj1 X) (conj (proj2 (proj2 X)) NDP))]. }
  intros r. apply usim_pure. intros Hv. destruct r as [err|v]; cbn beta.
  - eapply usim_post; [apply (usim_ND (to_bytes path) npk _ _ _
        (eqpost (fun r => fun gh sG moG sC moC => (r = 0 \/ r = -1) /\ RUK tm nx pt K (if r =? 0 then cdel (to_bytes path) C else C) idl (WF oh hs F) gh sG moG sC moC)))|].
    + eapply ruk_bind with (phi := fun _ => True) (K1 := fun _ => K) (C1 := fun _ => C) (g1 := fun _ => idl) (W1 := fun _ => WF oh hs F); [eapply ru_post; [apply us_set_errno| intros [] ? ? ? ? ? H; exact (conj I H)]|].
      intros [] _. apply ru_ret. intros ? ? ? ? ? H. split; [right; reflexivity| cbn; exact H].
    + intros a b gh sG moG sC moC [[-> [Hr HR]] HN]. split; [reflexivity|]. split; [exact Hr|]. exact (conj HR HN).
  - subst v. cbn. apply ru_ret. intros ? ? ? ? ? H. split; [left; reflexivity| cbn; exact H].
Qed.

(* [comment removed for export] *)
#[using="Type"] Theorem us_mkstemp tm nx pt K C oh hs F t name (track : bool) :
  seal_name t = Some name -> K_clear K (to_bytes name) -> to_bytes name <> devnull_path ->
  usimS (RUK tm nx pt K C idl (WF oh hs F)) (s_mkstemp t : Monad.M PSG (list Z * Z)) (s_mkstemp t)
        (eqpost (fun r => fun gh sG moG sC moC => fst r = name /\ (snd r = -1 \/ 3 <= snd r <= 4096) /\
           RUK tm nx pt (if snd r =? -1 then K else K ++ [mkKfe (snd r) KW (to_bytes name) None (if track then Some [] else None) 0])
               (if snd r =? -1 then C else cdel (to_bytes name) C) idl (WF oh hs F) gh sG moG sC moC
           /\ (snd r <> -1 -> ND (to_bytes name) moG))).
Proof.
  intros HS HC NDV. unfold s_mkstemp, mkstemp. rewrite HS.
  eapply ru_bind.
  { eapply (ruk_nodeKM tm nx pt K C idl (WF oh hs F) (NOpenW (to_bytes name) MKSTEMP_MODE) dec_openw _ (fun r => match r with SErr _ => True | SVal fd => 3 <= fd <= 4096 end)
             (fun r => match r with SErr _ => K | SVal fd => K ++ [mkKfe fd KW (to_bytes name) None (if track then Some [] else None) 0] end)
             (fun r => match r with SErr _ => C | SVal _ => cdel (to_bytes name) C end) (fun _ => idl)
             (fun r mo => match r with SErr _ => True | SVal _ => ND (to_bytes name) mo end));
      [exact I| apply (fn_openw nx K C (to_bytes name) MKSTEMP_MODE track HC (fun E => False_ind _ (NDV E)))|].
    intros [e|fd] l mo X; cbn in X; [exact (conj I (conj (proj1 X) I))|].
    destruct X as (X1 & X2 & X3). rewrite (wkind_other _ NDV) in X2. exact (conj X1 (conj X2 (X3 NDV))). }
  intros [err|fd]; apply usim_pure; intros Hfd; cbn beta.
  - eapply ru_pre with (R' := RUK tm nx pt K C idl (WF oh hs F)); [| intros ? ? ? ? ? [H _]; exact H].
    eapply ruk_bind with (phi := fun _ => True) (K1 := fun _ => K) (C1 := fun _ => C) (g1 := fun _ => idl) (W1 := fun _ => WF oh hs F); [eapply ru_post; [apply us_set_errno| intros [] ? ? ? ? ? H; exact (conj I H)]|].
    intros [] _. apply ru_ret. intros ? ? ? ? ? H. cbn. split; [reflexivity|]. split; [left; reflexivity|]. split; [exact H| intros X; exfalso; exact (X eq_refl)].
  - apply ru_ret. intros gh sG moG sC moC [H HN]. cbn [fst snd].
    replace (fd =? -1) with false by (symmetry; apply Z.eqb_neq; lia). split; [reflexivity|]. split; [right; exact Hfd|]. split; [exact H| intros _; exact HN].
Qed.

(* [comment removed for export] *)
#[using="Type"] Theorem us_close tm nx pt K C oh hs F e :
  In e K -> k_own e = None ->
  usimS (RUK tm nx pt K C idl (WF oh hs F)) (s_close (k_fd e) : Monad.M PSG Z) (s_close (k_fd e))
        (eqpost (fun r => fun gh sG moG sC moC => r = 0 /\ RUK tm nx pt (kdel (k_fd e) K) (cclose e C) idl (WF oh hs F) gh sG moG sC moC)).
Proof.
  intros He Ho. unfold s_close, close.
  eapply ruk_bind with (phi := fun _ => True) (K1 := fun _ => kdel (k_fd e) K) (C1 := fun _ => cclose e C) (g1 := fun _ => idl) (W1 := fun _ => WF oh hs F).
  { eapply ruk_nodeK; [exact I| apply (fn_close_ok nx K C e He)|]. intros [] l mo HF. unfold lrem in HF. rewrite Ho in HF. exact (conj I HF). }
  intros [] _. apply ruk_ret. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma us_close_files tm nx pt K C oh hs F : forall fs,
  (forall h f, In (h, f) fs -> exists e, In e K /\ k_own e = Some h /\ k_kind e = KNull /\ k_data e = None /\ fshape f e) ->
  usimS (RUK tm nx pt K C idl (WF oh hs F)) (close_files fs : Monad.M PSG unit) (close_files fs) (eqpost (fun _ => RUK tm nx pt K C idl (WF oh hs F))).
Proof.
  induction fs as [|[h f] fs IH]; intros HFS; cbn [close_files].
  - apply ru_ret. intros; assumption.
  - destruct (HFS h f (or_introl eq_refl)) as (e & He & Ho & KD & ED & Sh).
    apply ruk_use. intros l0 mo0 HFK. pose proof (proj1 (FI_KP _ _ _ _ _ HFK)) as ND.
    eapply ruk_bind with (phi := fun _ => True) (K1 := fun _ => K) (C1 := fun _ => C) (g1 := fun _ => idl) (W1 := fun _ => WF oh hs F).
    + eapply ru_post; [apply (us_close_file tm nx pt K C idl _ (TW e) f (ltac:(exact He) : tgt_in (TW e) K) (fshape_WT _ _ Sh (or_intror KD)))|].
      { unfold tbud, wbud. rewrite ED. exact I. }
      intros [] ? ? ? ? ? H. cbn [ftgt_K ftgt_g] in H. rewrite (kapp_data_none _ _ ED), kset_self in H; [exact (conj I H)| exact He| exact ND].
    + intros [] _. apply IH. intros h' f' Hin. exact (HFS h' f' (or_intror Hin)).
Qed.

#[using="Type"] Theorem us_stdio_exit tm nx pt K C oh hs F :
  (forall e h, In e K -> k_own e = Some h -> k_kind e = KNull /\ k_data e = None) ->
  usimS (RUK tm nx pt K C idl (WF oh hs F)) (s_stdio_exit : Monad.M PSG unit) s_stdio_exit (eqpost (fun _ => RUK tm nx pt K C idl (WF oh hs F))).
Proof.
  intros HK. unfold s_stdio_exit, stdio_exit.
  eapply ruk_bind with (K1 := fun _ => K) (C1 := fun _ => C) (g1 := fun _ => idl); [apply ruk_rd_lc|].
  intros l (HL & [mo HF] & [o HW]). cbn beta.
  destruct (stdx_WT _ _ (FI_stdout _ _ _ _ _ HF)) as [W1 FD1]. destruct (stdx_WT _ _ (FI_stderr _ _ _ _ _ HF)) as [W2 FD2].
  apply (ruk_frame_weaken tm nx pt K C idl _ (WF oh hs F)); [intros l0 o0 [X _]; exact X|].
  eapply ruk_bind with (phi := fun _ => True) (K1 := fun _ => K) (C1 := fun _ => C) (g1 := fun _ => idl) (W1 := fun _ => WF oh hs F).
  { eapply ru_post; [apply us_close_files|]; [| intros [] ? ? ? ? ? H; exact (conj I H)].
    intros h f Hin. destruct (FI_file _ _ _ _ _ HF h f Hin) as [_ (e & He & Ho & Sh & _)]. destruct (HK e h He Ho) as [KD ED]. exists e. auto 6. }
  intros [] _. cbn beta.
  eapply ruk_bind with (phi := fun _ => True) (K1 := fun _ => K) (C1 := fun _ => C) (g1 := fun _ => idl) (W1 := fun _ => WF oh hs F).
  { eapply ru_post; [apply (us_close_file tm nx pt K C idl _ (TC 1) (lc_stdout l) I (conj W1 FD1) I)|]. intros [] ? ? ? ? ? H. exact (conj I H). }
  intros [] _. cbn beta.
  eapply ru_post; [apply (us_close_file tm nx pt K C idl _ (TC 2) (lc_stderr l) I (conj W2 FD2) I)|]. intros [] ? ? ? ? ? H. exact H.
Qed.

(* [comment removed for export] *)
#[using="Type"] Theorem us_exit_model tm nx pt K C oh hs F code (Q : Empty_set -> Empty_set -> relX) :
  (forall e h, In e K -> k_own e = Some h -> k_kind e = KNull /\ k_data e = None) ->
  usimS (RUK tm nx pt K C idl (WF oh hs F)) (exit_model s_stdio_exit code : Monad.M PSG Empty_set) (exit_model s_stdio_exit code) Q.
Proof.
  intros HK. unfold exit_model. eapply ru_bind2; [apply (us_stdio_exit tm nx pt K C oh hs F HK)|].
  intros [] []. apply usim_pure. intros _. apply ru_exit.
Qed.


End UStdio.

End WithCeil.
