(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Exec ITree Nodes Decode Ceiling.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad STree Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require AsanHeap__SpecA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanHeap__SpecA.AsanHeap.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA NodesA SysStepF ProtoS RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg AProto.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Section Rules.
Context {CE : CEIL}.
Variable segs : list Segment.

#[local] Abbreviation PS := (PState aheap aptr) (only parsing).
#[local] Abbreviation MP := (@Monad.M (PState aheap aptr)) (only parsing).

(* [comment removed for export] *)
Definition a0_of (ms : machine_state) : Z := bv_unsigned (areg ms (Z_to_bv 5 REG_A0)).

(* [comment removed for export] *)
#[using="Type"] Lemma implF_peekS_now : forall {R} RNG a (k : resp -> itree node R) Q ms,
  implS segs RNG (k (peek_rsp (peekA_val segs ms a))) Q ms -> implS segs RNG (Vis (NPeek a) k) Q ms.
Proof.
  intros R RNG a k Q ms H. eapply (implF_peek_now node segs); [reflexivity|].
  intros RNG' HF. destruct HF as [HF _]. cbn in HF. subst RNG'. exact H.
Qed.
#[using="Type"] Lemma implF_epeekS : forall {X Y} RNG a (pl : resp -> option X) (f : X -> itree node (exc Y)) Q ms,
  implS segs RNG (match pl (peek_rsp (peekA_val segs ms a)) with Some x => f x | None => Ret Unr end) Q ms ->
  implS segs RNG (ebind (enode (NPeek a) pl) f) Q ms.
Proof.
  intros X Y RNG a pl f Q ms H. unfold ebind, enode. cbn [bind]. apply implF_peekS_now.
  destruct (pl (peek_rsp (peekA_val segs ms a))) as [x|]; cbn [bind]; exact H.
Qed.
Local Ltac ipeek ::= first [ eapply implF_epeekS | eapply implF_peekS_now ].

(* [comment removed for export] *)
#[using="Type"] Lemma implS_mpeek_reg64 : forall {B} (r : Z) (k : Z -> MP B) (s : PS) RNG Q ms, 0 <= r < 32 ->
  implS segs RNG (k (bv_unsigned (areg ms (Z_to_bv 5 r))) s) Q ms ->
  implS segs RNG (mbind (mpeek_reg64 r) k s) Q ms.
Proof.
  intros B r k s RNG Q ms Hr H.
  unfold mpeek_reg64, mpeek, mbind, msys.
  change (- (1 + 8 * r + 0)) with (peek_reg_code r 0). change (- (1 + 8 * r + 1)) with (peek_reg_code r 1).
  change (- (1 + 8 * r + 2)) with (peek_reg_code r 2). change (- (1 + 8 * r + 3)) with (peek_reg_code r 3).
  change (- (1 + 8 * r + 4)) with (peek_reg_code r 4). change (- (1 + 8 * r + 5)) with (peek_reg_code r 5).
  change (- (1 + 8 * r + 6)) with (peek_reg_code r 6). change (- (1 + 8 * r + 7)) with (peek_reg_code r 7).
  repeat (ipeek; cbn [fst snd]; rewrite (dec_peek_reg segs ms r) by lia).
  cbn [mret ebind bind fst snd].
  rewrite reg_bytes_sum. { exact H. }
  pose proof (bv_unsigned_in_range 64 (areg ms (Z_to_bv 5 r))) as HR. change (bv_modulus 64) with (2^64) in HR. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma reg_bytes_sum48 : forall x, 0 <= x < 2^48 ->
  (x / 2^(8*0)) mod 256 + 2^8 * ((x / 2^(8*1)) mod 256) + 2^16 * ((x / 2^(8*2)) mod 256) + 2^24 * ((x / 2^(8*3)) mod 256)
  + 2^32 * ((x / 2^(8*4)) mod 256) + 2^40 * ((x / 2^(8*5)) mod 256) = x.
Proof.
  intros x Hx. pose proof (reg_bytes_sum x ltac:(lia)) as E.
  assert (E6 : (x / 2^(8*6)) mod 256 = 0) by (rewrite (Z.div_small x (2^(8*6))) by (change (2^(8*6)) with (2^48); lia); reflexivity).
  assert (E7 : (x / 2^(8*7)) mod 256 = 0) by (rewrite (Z.div_small x (2^(8*7))) by (change (2^(8*7)) with (2^56); lia); reflexivity).
  rewrite E6, E7 in E. lia.
Qed.

#[using="Type"] Lemma implS_mpeek_reg48 : forall {B} (r : Z) (k : Z -> MP B) (s : PS) RNG Q ms, 0 <= r < 32 ->
  bv_unsigned (areg ms (Z_to_bv 5 r)) < 2^48 ->
  implS segs RNG (k (bv_unsigned (areg ms (Z_to_bv 5 r))) s) Q ms ->
  implS segs RNG (mbind (mpeek_reg48 r) k s) Q ms.
Proof.
  intros B r k s RNG Q ms Hr H48 H.
  unfold mpeek_reg48, mpeek, mbind, msys.
  change (- (1 + 8 * r + 0)) with (peek_reg_code r 0). change (- (1 + 8 * r + 1)) with (peek_reg_code r 1).
  change (- (1 + 8 * r + 2)) with (peek_reg_code r 2). change (- (1 + 8 * r + 3)) with (peek_reg_code r 3).
  change (- (1 + 8 * r + 4)) with (peek_reg_code r 4). change (- (1 + 8 * r + 5)) with (peek_reg_code r 5).
  repeat (ipeek; cbn [fst snd]; rewrite (dec_peek_reg segs ms r) by lia).
  cbn [mret ebind bind fst snd].
  rewrite reg_bytes_sum48. { exact H. }
  pose proof (bv_unsigned_in_range 64 (areg ms (Z_to_bv 5 r))) as HR. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma implS_alift : forall {R B} (t : AM R) (k : R -> MP B) (s : PS) RNG (P : R -> footprint -> machine_state -> Prop)
    (Q : B * PS -> footprint -> machine_state -> Prop) ms,
  implS segs RNG (aembed alloc_ceiling t) (epostF P) ms ->
  (forall r RNG' ms', P r RNG' ms' -> implS segs RNG' (k r s) (epostF Q) ms') ->
  implS segs RNG (mbind (alift t) k s) (epostF Q) ms.
Proof.
  intros R B t k s RNG P Q ms HT HK. unfold mbind, alift.
  eapply implF_ebind with (Q1 := fun p RNG' ms' => snd p = s /\ P (fst p) RNG' ms').
  - eapply implF_ebind; [exact HT|]. intros r RNG' ms' HP. apply implF_ret_ok. apply evtF_done. split; [reflexivity| exact HP].
  - intros [r s'] RNG' ms' [E HP]. cbn [fst snd] in *. subst s'. apply HK. exact HP.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma implS_ebind_assoc : forall {X Y Z0} (t : itree node (exc X)) (g : X -> itree node (exc Y)) (f : Y -> itree node (exc Z0)) RNG Q ms,
  implS segs RNG (ebind t (fun a => ebind (g a) f)) Q ms ->
  implS segs RNG (ebind (ebind t g) f) Q ms.
Proof.
  intros X Y Z0 t g f. induction t as [[|a]|n k IH]; intros RNG Q ms H.
  - exact H.
  - exact H.
  - unfold ebind in *. cbn [bind implF] in *. eapply evtS_mono; [exact H|].
    intros ms1 [[Hat Hk]|(p & Hp & Hk)].
    + left. split; [exact Hat|]. intros rsp RNG' HF. apply IH. apply Hk. exact HF.
    + right. exists p. split; [exact Hp|]. intros RNG' HF. apply IH. apply Hk. exact HF.
Qed.

#[using="Type"] Lemma implS_mbind_assoc : forall {A B C} (m : MP A) (f : A -> MP B) (k : B -> MP C) (s : PS) RNG Q ms,
  implS segs RNG (mbind m (fun a => mbind (f a) k) s) Q ms ->
  implS segs RNG (mbind (mbind m f) k s) Q ms.
Proof. intros A B C m f k s RNG Q ms H. unfold mbind in *. apply implS_ebind_assoc. exact H. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma implS_alloc_tail : forall {B} forget (x : astate * option aptr) (k : option aptr -> MP B) (s : PS) RNG Q ms,
  match snd x with
  | Some id => a0_of ms < 2^48 /\ implS segs RNG
                 (k (Some id) (set_heap (ah_set_addr (<[id := a0_of ms]> (forget (ah_addr (ps_heap s)))) (ah_set_st (fst x) (ps_heap s))) s)) Q ms
  | None => implS segs RNG (k None (set_heap (ah_set_st (fst x) (ps_heap s)) s)) Q ms
  end ->
  implS segs RNG (mbind (ah_alloc_tail forget x) k s) Q ms.
Proof.
  intros B forget [st' [id|]] k s RNG Q ms H; unfold ah_alloc_tail; cbn [fst snd] in *.
  - destruct H as [H48 H]. apply implS_mbind_assoc. apply implS_mpeek_reg48; [unfold REG_A0; lia| exact H48 |].
    unfold mbind, upd_heap, mupd, mret. cbn [ebind bind fst snd]. exact H.
  - unfold mbind, upd_heap, mupd, mret. cbn [ebind bind fst snd]. exact H.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma implS_ah_malloc : forall {B} n (k : option aptr -> MP B) (s : PS) RNG (P : astate * option aptr -> footprint -> machine_state -> Prop)
    (Q : B * PS -> footprint -> machine_state -> Prop) ms,
  implS segs RNG (aembed alloc_ceiling (amalloc alloc_ceiling (ah_resv (ps_heap s)) (ah_st (ps_heap s)) n)) (epostF P) ms ->
  (forall x RNG' ms', P x RNG' ms' ->
     match snd x with
     | Some id => a0_of ms' < 2^48 /\ implS segs RNG'
                    (k (Some id) (set_heap (ah_set_addr (<[id := a0_of ms']> (ah_addr (ps_heap s))) (ah_set_st (fst x) (ps_heap s))) s)) (epostF Q) ms'
     | None => implS segs RNG' (k None (set_heap (ah_set_st (fst x) (ps_heap s)) s)) (epostF Q) ms'
     end) ->
  implS segs RNG (mbind (ah_malloc n) k s) (epostF Q) ms.
Proof.
  intros B n k s RNG P Q ms HT HK. unfold ah_malloc.
  apply implS_mbind_assoc. unfold mbind at 1. unfold mget. cbn [ebind bind fst snd].
  apply implS_mbind_assoc. eapply implS_alift; [exact HT|].
  intros x RNG' ms' HP. apply implS_alloc_tail. exact (HK x RNG' ms' HP).
Qed.

#[using="Type"] Lemma implS_ah_calloc : forall {B} m n (k : option aptr -> MP B) (s : PS) RNG (P : astate * option aptr -> footprint -> machine_state -> Prop)
    (Q : B * PS -> footprint -> machine_state -> Prop) ms,
  implS segs RNG (aembed alloc_ceiling (acalloc alloc_ceiling (ah_resv (ps_heap s)) (ah_st (ps_heap s)) m n)) (epostF P) ms ->
  (forall x RNG' ms', P x RNG' ms' ->
     match snd x with
     | Some id => a0_of ms' < 2^48 /\ implS segs RNG'
                    (k (Some id) (set_heap (ah_set_addr (<[id := a0_of ms']> (ah_addr (ps_heap s))) (ah_set_st (fst x) (ps_heap s))) s)) (epostF Q) ms'
     | None => implS segs RNG' (k None (set_heap (ah_set_st (fst x) (ps_heap s)) s)) (epostF Q) ms'
     end) ->
  implS segs RNG (mbind (ah_calloc m n) k s) (epostF Q) ms.
Proof.
  intros B m n k s RNG P Q ms HT HK. unfold ah_calloc.
  apply implS_mbind_assoc. unfold mbind at 1. unfold mget. cbn [ebind bind fst snd].
  apply implS_mbind_assoc. eapply implS_alift; [exact HT|].
  intros x RNG' ms' HP. apply implS_alloc_tail. exact (HK x RNG' ms' HP).
Qed.

#[using="Type"] Lemma implS_ah_realloc : forall {B} p n (k : option aptr -> MP B) (s : PS) RNG (P : astate * option aptr -> footprint -> machine_state -> Prop)
    (Q : B * PS -> footprint -> machine_state -> Prop) ms,
  implS segs RNG (aembed alloc_ceiling (arealloc alloc_ceiling (ah_resv (ps_heap s)) (ah_st (ps_heap s)) p n)) (epostF P) ms ->
  (forall x RNG' ms', P x RNG' ms' ->
     match snd x with
     | Some id => a0_of ms' < 2^48 /\ implS segs RNG'
                    (k (Some id) (set_heap (ah_set_addr (<[id := a0_of ms']> (delete p (ah_addr (ps_heap s)))) (ah_set_st (fst x) (ps_heap s))) s)) (epostF Q) ms'
     | None => implS segs RNG' (k None (set_heap (ah_set_st (fst x) (ps_heap s)) s)) (epostF Q) ms'
     end) ->
  implS segs RNG (mbind (ah_realloc p n) k s) (epostF Q) ms.
Proof.
  intros B p n k s RNG P Q ms HT HK. unfold ah_realloc.
  apply implS_mbind_assoc. unfold mbind at 1. unfold mget. cbn [ebind bind fst snd].
  apply implS_mbind_assoc. eapply implS_alift; [exact HT|].
  intros x RNG' ms' HP. apply implS_alloc_tail. exact (HK x RNG' ms' HP).
Qed.

#[using="Type"] Lemma implS_ah_free : forall {B} p (k : unit -> MP B) (s : PS) RNG (P : astate -> footprint -> machine_state -> Prop)
    (Q : B * PS -> footprint -> machine_state -> Prop) ms,
  implS segs RNG (aembed alloc_ceiling (afree (ah_st (ps_heap s)) (Some p))) (epostF P) ms ->
  (forall st' RNG' ms', P st' RNG' ms' ->
     implS segs RNG' (k tt (set_heap (ah_set_addr (delete p (ah_addr (ps_heap s))) (ah_set_st st' (ps_heap s))) s)) (epostF Q) ms') ->
  implS segs RNG (mbind (ah_free p) k s) (epostF Q) ms.
Proof.
  intros B p k s RNG P Q ms HT HK. unfold ah_free.
  apply implS_mbind_assoc. unfold mbind at 1. unfold mget. cbn [ebind bind fst snd].
  apply implS_mbind_assoc. eapply implS_alift; [exact HT|].
  intros st' RNG' ms' HP. unfold mbind, upd_heap, mupd. cbn [ebind bind fst snd]. exact (HK st' RNG' ms' HP).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma implS_ah_free0 : forall p (s : PS) RNG (P : astate -> footprint -> machine_state -> Prop)
    (Q : unit * PS -> footprint -> machine_state -> Prop) ms,
  implS segs RNG (aembed alloc_ceiling (afree (ah_st (ps_heap s)) (Some p))) (epostF P) ms ->
  (forall st' RNG' ms', P st' RNG' ms' ->
     Q (tt, set_heap (ah_set_addr (delete p (ah_addr (ps_heap s))) (ah_set_st st' (ps_heap s))) s) RNG' ms') ->
  implS segs RNG (ah_free p s) (epostF Q) ms.
Proof.
  intros p s RNG P Q ms HT HK. unfold ah_free.
  unfold mbind at 1. unfold mget. cbn [ebind bind fst snd].
  eapply implS_alift; [exact HT|].
  intros st' RNG' ms' HP. unfold upd_heap, mupd. apply implF_ret_ok. apply evtF_done. exact (HK st' RNG' ms' HP).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma implS_fo_enter : forall {A B} site_frame f (m : MP A) (k : A -> MP B) (s : PS) RNG Q ms,
  a0_of ms < 2^48 ->
  implS segs RNG (mbind m k (set_heap (ah_set_frames ((f, a0_of ms) :: ah_frames (ps_heap s)) (ps_heap s)) s)) Q ms ->
  implS segs RNG (mbind (fo_enter (asan_fo site_frame) _ f m) k s) Q ms.
Proof.
  intros A B site_frame f m k s RNG Q ms H48 H. cbn [fo_enter asan_fo].
  apply implS_mbind_assoc. apply implS_mpeek_reg48; [unfold REG_A0; lia| exact H48 |].
  apply implS_mbind_assoc. unfold mbind at 1. unfold upd_heap, mupd. cbn [ebind bind fst snd]. exact H.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma implS_fo_enter0 : forall {A} site_frame f (m : MP A) (s : PS) RNG Q ms,
  a0_of ms < 2^48 ->
  implS segs RNG (m (set_heap (ah_set_frames ((f, a0_of ms) :: ah_frames (ps_heap s)) (ps_heap s)) s)) Q ms ->
  implS segs RNG (fo_enter (asan_fo site_frame) _ f m s) Q ms.
Proof.
  intros A site_frame f m s RNG Q ms H48 H. cbn [fo_enter asan_fo].
  apply implS_mpeek_reg48; [unfold REG_A0; lia| exact H48 |].
  unfold mbind at 1. unfold upd_heap, mupd. cbn [ebind bind fst snd]. exact H.
Qed.
#[using="Type"] Lemma implS_fo_ret0 : forall {A} site_frame f (x : A) (s : PS) RNG (Q : A * PS -> footprint -> machine_state -> Prop) ms,
  evtF segs RNG (Q (x, set_heap (ah_set_frames (tl (ah_frames (ps_heap s))) (ps_heap s)) s) RNG) ms ->
  implS segs RNG (fo_ret (asan_fo site_frame) _ f x s) (epostF Q) ms.
Proof.
  intros A site_frame f x s RNG Q ms H. cbn [fo_ret asan_fo].
  unfold mbind, upd_heap, mupd, mret. cbn [ebind bind fst snd]. apply implF_ret_ok. exact H.
Qed.

#[using="Type"] Lemma implS_fo_ret : forall {A B} site_frame f (x : A) (k : A -> MP B) (s : PS) RNG Q ms,
  implS segs RNG (k x (set_heap (ah_set_frames (tl (ah_frames (ps_heap s))) (ps_heap s)) s)) Q ms ->
  implS segs RNG (mbind (fo_ret (asan_fo site_frame) _ f x) k s) Q ms.
Proof.
  intros A B site_frame f x k s RNG Q ms H. cbn [fo_ret asan_fo].
  unfold mbind, upd_heap, mupd, mret. cbn [ebind bind fst snd]. exact H.
Qed.
End Rules.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MState OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Mem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Exec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Ceiling.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanHeap__SpecA.AsanHeap.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.NodesA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ProtoS OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Section Rules.
Context {CE : CEIL}.
Variable segs : list Segment.

#[local] Abbreviation PS := (PState aheap aptr) (only parsing).
#[local] Abbreviation MP := (@Monad.M (PState aheap aptr)) (only parsing).

(* [comment removed for export] *)
Definition a0_of (ms : machine_state) : Z := bv_unsigned (areg ms (Z_to_bv 5 REG_A0)).

(* [comment removed for export] *)
#[using="Type"] Lemma implF_peekS_now : forall {R} RNG a (k : resp -> itree node R) Q ms,
  implS segs RNG (k (peek_rsp (peekA_val segs ms a))) Q ms -> implS segs RNG (Vis (NPeek a) k) Q ms.
Proof.
  intros R RNG a k Q ms H. eapply (implF_peek_now node segs); [reflexivity|].
  intros RNG' HF. destruct HF as [HF _]. cbn in HF. subst RNG'. exact H.
Qed.
#[using="Type"] Lemma implF_epeekS : forall {X Y} RNG a (pl : resp -> option X) (f : X -> itree node (exc Y)) Q ms,
  implS segs RNG (match pl (peek_rsp (peekA_val segs ms a)) with Some x => f x | None => Ret Unr end) Q ms ->
  implS segs RNG (ebind (enode (NPeek a) pl) f) Q ms.
Proof.
  intros X Y RNG a pl f Q ms H. unfold ebind, enode. cbn [bind]. apply implF_peekS_now.
  destruct (pl (peek_rsp (peekA_val segs ms a))) as [x|]; cbn [bind]; exact H.
Qed.
Local Ltac ipeek ::= first [ eapply implF_epeekS | eapply implF_peekS_now ].

(* [comment removed for export] *)
#[using="Type"] Lemma implS_mpeek_reg64 : forall {B} (r : Z) (k : Z -> MP B) (s : PS) RNG Q ms, 0 <= r < 32 ->
  implS segs RNG (k (bv_unsigned (areg ms (Z_to_bv 5 r))) s) Q ms ->
  implS segs RNG (mbind (mpeek_reg64 r) k s) Q ms.
Proof.
  intros B r k s RNG Q ms Hr H.
  unfold mpeek_reg64, mpeek, mbind, msys.
  change (- (1 + 8 * r + 0)) with (peek_reg_code r 0). change (- (1 + 8 * r + 1)) with (peek_reg_code r 1).
  change (- (1 + 8 * r + 2)) with (peek_reg_code r 2). change (- (1 + 8 * r + 3)) with (peek_reg_code r 3).
  change (- (1 + 8 * r + 4)) with (peek_reg_code r 4). change (- (1 + 8 * r + 5)) with (peek_reg_code r 5).
  change (- (1 + 8 * r + 6)) with (peek_reg_code r 6). change (- (1 + 8 * r + 7)) with (peek_reg_code r 7).
  repeat (ipeek; cbn [fst snd]; rewrite (dec_peek_reg segs ms r) by lia).
  cbn [mret ebind bind fst snd].
  rewrite reg_bytes_sum. { exact H. }
  pose proof (bv_unsigned_in_range 64 (areg ms (Z_to_bv 5 r))) as HR. change (bv_modulus 64) with (2^64) in HR. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma reg_bytes_sum48 : forall x, 0 <= x < 2^48 ->
  (x / 2^(8*0)) mod 256 + 2^8 * ((x / 2^(8*1)) mod 256) + 2^16 * ((x / 2^(8*2)) mod 256) + 2^24 * ((x / 2^(8*3)) mod 256)
  + 2^32 * ((x / 2^(8*4)) mod 256) + 2^40 * ((x / 2^(8*5)) mod 256) = x.
Proof.
  intros x Hx. pose proof (reg_bytes_sum x ltac:(lia)) as E.
  assert (E6 : (x / 2^(8*6)) mod 256 = 0) by (rewrite (Z.div_small x (2^(8*6))) by (change (2^(8*6)) with (2^48); lia); reflexivity).
  assert (E7 : (x / 2^(8*7)) mod 256 = 0) by (rewrite (Z.div_small x (2^(8*7))) by (change (2^(8*7)) with (2^56); lia); reflexivity).
  rewrite E6, E7 in E. lia.
Qed.

#[using="Type"] Lemma implS_mpeek_reg48 : forall {B} (r : Z) (k : Z -> MP B) (s : PS) RNG Q ms, 0 <= r < 32 ->
  bv_unsigned (areg ms (Z_to_bv 5 r)) < 2^48 ->
  implS segs RNG (k (bv_unsigned (areg ms (Z_to_bv 5 r))) s) Q ms ->
  implS segs RNG (mbind (mpeek_reg48 r) k s) Q ms.
Proof.
  intros B r k s RNG Q ms Hr H48 H.
  unfold mpeek_reg48, mpeek, mbind, msys.
  change (- (1 + 8 * r + 0)) with (peek_reg_code r 0). change (- (1 + 8 * r + 1)) with (peek_reg_code r 1).
  change (- (1 + 8 * r + 2)) with (peek_reg_code r 2). change (- (1 + 8 * r + 3)) with (peek_reg_code r 3).
  change (- (1 + 8 * r + 4)) with (peek_reg_code r 4). change (- (1 + 8 * r + 5)) with (peek_reg_code r 5).
  repeat (ipeek; cbn [fst snd]; rewrite (dec_peek_reg segs ms r) by lia).
  cbn [mret ebind bind fst snd].
  rewrite reg_bytes_sum48. { exact H. }
  pose proof (bv_unsigned_in_range 64 (areg ms (Z_to_bv 5 r))) as HR. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma implS_alift : forall {R B} (t : AM R) (k : R -> MP B) (s : PS) RNG (P : R -> footprint -> machine_state -> Prop)
    (Q : B * PS -> footprint -> machine_state -> Prop) ms,
  implS segs RNG (aembed alloc_ceiling t) (epostF P) ms ->
  (forall r RNG' ms', P r RNG' ms' -> implS segs RNG' (k r s) (epostF Q) ms') ->
  implS segs RNG (mbind (alift t) k s) (epostF Q) ms.
Proof.
  intros R B t k s RNG P Q ms HT HK. unfold mbind, alift.
  eapply implF_ebind with (Q1 := fun p RNG' ms' => snd p = s /\ P (fst p) RNG' ms').
  - eapply implF_ebind; [exact HT|]. intros r RNG' ms' HP. apply implF_ret_ok. apply evtF_done. split; [reflexivity| exact HP].
  - intros [r s'] RNG' ms' [E HP]. cbn [fst snd] in *. subst s'. apply HK. exact HP.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma implS_ebind_assoc : forall {X Y Z0} (t : itree node (exc X)) (g : X -> itree node (exc Y)) (f : Y -> itree node (exc Z0)) RNG Q ms,
  implS segs RNG (ebind t (fun a => ebind (g a) f)) Q ms ->
  implS segs RNG (ebind (ebind t g) f) Q ms.
Proof.
  intros X Y Z0 t g f. induction t as [[|a]|n k IH]; intros RNG Q ms H.
  - exact H.
  - exact H.
  - unfold ebind in *. cbn [bind implF] in *. eapply evtS_mono; [exact H|].
    intros ms1 [[Hat Hk]|(p & Hp & Hk)].
    + left. split; [exact Hat|]. intros rsp RNG' HF. apply IH. apply Hk. exact HF.
    + right. exists p. split; [exact Hp|]. intros RNG' HF. apply IH. apply Hk. exact HF.
Qed.

#[using="Type"] Lemma implS_mbind_assoc : forall {A B C} (m : MP A) (f : A -> MP B) (k : B -> MP C) (s : PS) RNG Q ms,
  implS segs RNG (mbind m (fun a => mbind (f a) k) s) Q ms ->
  implS segs RNG (mbind (mbind m f) k s) Q ms.
Proof. intros A B C m f k s RNG Q ms H. unfold mbind in *. apply implS_ebind_assoc. exact H. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma implS_alloc_tail : forall {B} forget (x : astate * option aptr) (k : option aptr -> MP B) (s : PS) RNG Q ms,
  match snd x with
  | Some id => a0_of ms < 2^48 /\ implS segs RNG
                 (k (Some id) (set_heap (ah_set_addr (<[id := a0_of ms]> (forget (ah_addr (ps_heap s)))) (ah_set_st (fst x) (ps_heap s))) s)) Q ms
  | None => implS segs RNG (k None (set_heap (ah_set_st (fst x) (ps_heap s)) s)) Q ms
  end ->
  implS segs RNG (mbind (ah_alloc_tail forget x) k s) Q ms.
Proof.
  intros B forget [st' [id|]] k s RNG Q ms H; unfold ah_alloc_tail; cbn [fst snd] in *.
  - destruct H as [H48 H]. apply implS_mbind_assoc. apply implS_mpeek_reg48; [unfold REG_A0; lia| exact H48 |].
    unfold mbind, upd_heap, mupd, mret. cbn [ebind bind fst snd]. exact H.
  - unfold mbind, upd_heap, mupd, mret. cbn [ebind bind fst snd]. exact H.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma implS_ah_malloc : forall {B} n (k : option aptr -> MP B) (s : PS) RNG (P : astate * option aptr -> footprint -> machine_state -> Prop)
    (Q : B * PS -> footprint -> machine_state -> Prop) ms,
  implS segs RNG (aembed alloc_ceiling (amalloc alloc_ceiling (ah_resv (ps_heap s)) (ah_st (ps_heap s)) n)) (epostF P) ms ->
  (forall x RNG' ms', P x RNG' ms' ->
     match snd x with
     | Some id => a0_of ms' < 2^48 /\ implS segs RNG'
                    (k (Some id) (set_heap (ah_set_addr (<[id := a0_of ms']> (ah_addr (ps_heap s))) (ah_set_st (fst x) (ps_heap s))) s)) (epostF Q) ms'
     | None => implS segs RNG' (k None (set_heap (ah_set_st (fst x) (ps_heap s)) s)) (epostF Q) ms'
     end) ->
  implS segs RNG (mbind (ah_malloc n) k s) (epostF Q) ms.
Proof.
  intros B n k s RNG P Q ms HT HK. unfold ah_malloc.
  apply implS_mbind_assoc. unfold mbind at 1. unfold mget. cbn [ebind bind fst snd].
  apply implS_mbind_assoc. eapply implS_alift; [exact HT|].
  intros x RNG' ms' HP. apply implS_alloc_tail. exact (HK x RNG' ms' HP).
Qed.

#[using="Type"] Lemma implS_ah_calloc : forall {B} m n (k : option aptr -> MP B) (s : PS) RNG (P : astate * option aptr -> footprint -> machine_state -> Prop)
    (Q : B * PS -> footprint -> machine_state -> Prop) ms,
  implS segs RNG (aembed alloc_ceiling (acalloc alloc_ceiling (ah_resv (ps_heap s)) (ah_st (ps_heap s)) m n)) (epostF P) ms ->
  (forall x RNG' ms', P x RNG' ms' ->
     match snd x with
     | Some id => a0_of ms' < 2^48 /\ implS segs RNG'
                    (k (Some id) (set_heap (ah_set_addr (<[id := a0_of ms']> (ah_addr (ps_heap s))) (ah_set_st (fst x) (ps_heap s))) s)) (epostF Q) ms'
     | None => implS segs RNG' (k None (set_heap (ah_set_st (fst x) (ps_heap s)) s)) (epostF Q) ms'
     end) ->
  implS segs RNG (mbind (ah_calloc m n) k s) (epostF Q) ms.
Proof.
  intros B m n k s RNG P Q ms HT HK. unfold ah_calloc.
  apply implS_mbind_assoc. unfold mbind at 1. unfold mget. cbn [ebind bind fst snd].
  apply implS_mbind_assoc. eapply implS_alift; [exact HT|].
  intros x RNG' ms' HP. apply implS_alloc_tail. exact (HK x RNG' ms' HP).
Qed.

#[using="Type"] Lemma implS_ah_realloc : forall {B} p n (k : option aptr -> MP B) (s : PS) RNG (P : astate * option aptr -> footprint -> machine_state -> Prop)
    (Q : B * PS -> footprint -> machine_state -> Prop) ms,
  implS segs RNG (aembed alloc_ceiling (arealloc alloc_ceiling (ah_resv (ps_heap s)) (ah_st (ps_heap s)) p n)) (epostF P) ms ->
  (forall x RNG' ms', P x RNG' ms' ->
     match snd x with
     | Some id => a0_of ms' < 2^48 /\ implS segs RNG'
                    (k (Some id) (set_heap (ah_set_addr (<[id := a0_of ms']> (delete p (ah_addr (ps_heap s)))) (ah_set_st (fst x) (ps_heap s))) s)) (epostF Q) ms'
     | None => implS segs RNG' (k None (set_heap (ah_set_st (fst x) (ps_heap s)) s)) (epostF Q) ms'
     end) ->
  implS segs RNG (mbind (ah_realloc p n) k s) (epostF Q) ms.
Proof.
  intros B p n k s RNG P Q ms HT HK. unfold ah_realloc.
  apply implS_mbind_assoc. unfold mbind at 1. unfold mget. cbn [ebind bind fst snd].
  apply implS_mbind_assoc. eapply implS_alift; [exact HT|].
  intros x RNG' ms' HP. apply implS_alloc_tail. exact (HK x RNG' ms' HP).
Qed.

#[using="Type"] Lemma implS_ah_free : forall {B} p (k : unit -> MP B) (s : PS) RNG (P : astate -> footprint -> machine_state -> Prop)
    (Q : B * PS -> footprint -> machine_state -> Prop) ms,
  implS segs RNG (aembed alloc_ceiling (afree (ah_st (ps_heap s)) (Some p))) (epostF P) ms ->
  (forall st' RNG' ms', P st' RNG' ms' ->
     implS segs RNG' (k tt (set_heap (ah_set_addr (delete p (ah_addr (ps_heap s))) (ah_set_st st' (ps_heap s))) s)) (epostF Q) ms') ->
  implS segs RNG (mbind (ah_free p) k s) (epostF Q) ms.
Proof.
  intros B p k s RNG P Q ms HT HK. unfold ah_free.
  apply implS_mbind_assoc. unfold mbind at 1. unfold mget. cbn [ebind bind fst snd].
  apply implS_mbind_assoc. eapply implS_alift; [exact HT|].
  intros st' RNG' ms' HP. unfold mbind, upd_heap, mupd. cbn [ebind bind fst snd]. exact (HK st' RNG' ms' HP).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma implS_ah_free0 : forall p (s : PS) RNG (P : astate -> footprint -> machine_state -> Prop)
    (Q : unit * PS -> footprint -> machine_state -> Prop) ms,
  implS segs RNG (aembed alloc_ceiling (afree (ah_st (ps_heap s)) (Some p))) (epostF P) ms ->
  (forall st' RNG' ms', P st' RNG' ms' ->
     Q (tt, set_heap (ah_set_addr (delete p (ah_addr (ps_heap s))) (ah_set_st st' (ps_heap s))) s) RNG' ms') ->
  implS segs RNG (ah_free p s) (epostF Q) ms.
Proof.
  intros p s RNG P Q ms HT HK. unfold ah_free.
  unfold mbind at 1. unfold mget. cbn [ebind bind fst snd].
  eapply implS_alift; [exact HT|].
  intros st' RNG' ms' HP. unfold upd_heap, mupd. apply implF_ret_ok. apply evtF_done. exact (HK st' RNG' ms' HP).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma implS_fo_enter : forall {A B} site_frame f (m : MP A) (k : A -> MP B) (s : PS) RNG Q ms,
  a0_of ms < 2^48 ->
  implS segs RNG (mbind m k (set_heap (ah_set_frames ((f, a0_of ms) :: ah_frames (ps_heap s)) (ps_heap s)) s)) Q ms ->
  implS segs RNG (mbind (fo_enter (asan_fo site_frame) _ f m) k s) Q ms.
Proof.
  intros A B site_frame f m k s RNG Q ms H48 H. cbn [fo_enter asan_fo].
  apply implS_mbind_assoc. apply implS_mpeek_reg48; [unfold REG_A0; lia| exact H48 |].
  apply implS_mbind_assoc. unfold mbind at 1. unfold upd_heap, mupd. cbn [ebind bind fst snd]. exact H.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma implS_fo_enter0 : forall {A} site_frame f (m : MP A) (s : PS) RNG Q ms,
  a0_of ms < 2^48 ->
  implS segs RNG (m (set_heap (ah_set_frames ((f, a0_of ms) :: ah_frames (ps_heap s)) (ps_heap s)) s)) Q ms ->
  implS segs RNG (fo_enter (asan_fo site_frame) _ f m s) Q ms.
Proof.
  intros A site_frame f m s RNG Q ms H48 H. cbn [fo_enter asan_fo].
  apply implS_mpeek_reg48; [unfold REG_A0; lia| exact H48 |].
  unfold mbind at 1. unfold upd_heap, mupd. cbn [ebind bind fst snd]. exact H.
Qed.
#[using="Type"] Lemma implS_fo_ret0 : forall {A} site_frame f (x : A) (s : PS) RNG (Q : A * PS -> footprint -> machine_state -> Prop) ms,
  evtF segs RNG (Q (x, set_heap (ah_set_frames (tl (ah_frames (ps_heap s))) (ps_heap s)) s) RNG) ms ->
  implS segs RNG (fo_ret (asan_fo site_frame) _ f x s) (epostF Q) ms.
Proof.
  intros A site_frame f x s RNG Q ms H. cbn [fo_ret asan_fo].
  unfold mbind, upd_heap, mupd, mret. cbn [ebind bind fst snd]. apply implF_ret_ok. exact H.
Qed.

#[using="Type"] Lemma implS_fo_ret : forall {A B} site_frame f (x : A) (k : A -> MP B) (s : PS) RNG Q ms,
  implS segs RNG (k x (set_heap (ah_set_frames (tl (ah_frames (ps_heap s))) (ps_heap s)) s)) Q ms ->
  implS segs RNG (mbind (fo_ret (asan_fo site_frame) _ f x) k s) Q ms.
Proof.
  intros A B site_frame f x k s RNG Q ms H. cbn [fo_ret asan_fo].
  unfold mbind, upd_heap, mupd, mret. cbn [ebind bind fst snd]. exact H.
Qed.
End Rules.
End TwB.
