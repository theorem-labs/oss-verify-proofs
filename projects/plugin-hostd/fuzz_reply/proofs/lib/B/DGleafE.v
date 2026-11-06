(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/DGleafE.v (commit 30a1993588f, c5 + memnorm; file sha256 3c2f7302bdb1) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; taken by path: no numeral of it names an image address, none changed. *)
(* Modified by Theorem Labs, 2026-10: relocated from lib/A/DGleafE.v (commit d2dafa219c1, file sha256 5b1188edfda0) onto plugin-hostd/fuzz_reply's asan-ubsan image (unstripped fuzz_reply.asan-ubsan, sha256 3389287e1d61; pin 10ffb5f9202a) by alreloc ced0368250cb6538 (A -> B, direct map 541d2a13b9d2): 0 numerals moved; module paths lib.A -> lib.B and the image twins A<r> -> Y<r>. *)
(* The errno-kept forms the Deallocate arms and DGtop share (step 2 of the errno-kept twins, beside DIfaceR).

   DIfaceR gives the arms one proof for both frames ([rawb]: the view frame, plus the raw frame when [rawb = true]).
   The errno twins keep that shape: when [rawb = true] errno is kept on the raw memory (ErrnoG.errno_kept, the form of
   ErrnoG.dealloc_leaf_raw_e), when [rawb = false] on the view (ErrnoG.errno_kept_v, the form of
   ErrnoG.dealloc_leaf_e).  The Enqueue / Drain contracts follow the same split: ErrnoG's view add-ons
   (de_enqueue_v_t / de_drain_v_t, from DIfaceE) at [false], its raw ones (de_enqueue_t / de_drain_t, from DIfaceRE)
   at [true].  amreal has no rule for joining two contracts (ErrnoG's header), so each form is one contract.

   - [errno_kept_b] / [acall_e_b]: errno at the leaf's form, and the callee conjunct of that form;
   - [enq_spec_b_e] / [drain_spec_b_e]: DIfaceR.enq_spec_g / drain_spec_g over [acall_e_b], from ErrnoG's add-ons;
   - [dealloc_leaf_b_e]: DIfaceR.dealloc_leaf_b plus errno at its form, with the bridges to ErrnoG.dealloc_leaf_e
     ([false]), ErrnoG.dealloc_leaf_raw_e ([true]) and DIfaceR.dealloc_leaf_b;
   - [dealloc_leaf_raw_ee]: DeallocG.dealloc_leaf_raw plus errno on both forms, for the arms that cross no callee
     with a memory frame (NULL, common), whose walks end in the world they start in; it gives [dealloc_leaf_b_e] at
     either form. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import DMspec DMiface.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import DeallocG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ImgBaseDG DGif0 DIfaceR.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ErrnoG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {IM : AImg} {DI : DImg}.
Local Open Scope am_scope.

(* errno at the leaf's form: the raw memory when [rawb = true], the view otherwise. *)
Definition errno_kept_b (rawb : bool) (B : asyms) (W W' : world im_segs) (mem mem' : word -> option byte) : Prop :=
if rawb then ErrnoG.errno_kept B mem mem' else ErrnoG.errno_kept_v im_segs B W W' mem mem'.

(* The callee conjunct of that form: ErrnoG's raw add-on (acall_raw_x and errno on the raw memory) when
   [rawb = true], its view add-on (errno on the view) otherwise. *)
Definition acall_e_b (rawb : bool) (B : asyms) (AOX : alayout -> astate -> Z -> Prop) : fxrel :=
if rawb then ErrnoG.acall_raw_e_x B AOX else ErrnoG.acall_errno_v_x B.

Lemma acall_e_b_raw : forall rawb B AOX inst stk ly S W regs mem md E ly' S' W' regs' mem' md',
acall_e_b rawb B AOX inst stk ly S W regs mem md E ly' S' W' regs' mem' md' ->
rawif rawb (acall_raw_x B AOX) inst stk ly S W regs mem md E ly' S' W' regs' mem' md'.
Proof.
intros [|] B AOX inst stk ly S W regs mem md E ly' S' W' regs' mem' md' H T.
- exact (proj1 H).
- discriminate T.
Qed.

Lemma acall_e_b_errno : forall rawb B AOX inst stk ly S W regs mem md E ly' S' W' regs' mem' md',
acall_e_b rawb B AOX inst stk ly S W regs mem md E ly' S' W' regs' mem' md' ->
errno_kept_b rawb B W W' mem mem'.
Proof. intros [|] B AOX inst stk ly S W regs mem md E ly' S' W' regs' mem' md' H; [exact (proj2 H) | exact H]. Qed.

Section b.
Variable B : asyms.
Variable U : list Z -> astate -> Prop.
Variable ft : sptr -> list Z -> M unit.
Variable ARX : Z -> alayout -> astate -> world im_segs -> (word -> option byte) -> Model -> Prop.
Variable AOX : alayout -> astate -> Z -> Prop.
Variable rpre : astate -> Z -> Prop.
Variable lpost : astate -> Prop.
Variable fpre : alayout -> astate -> world im_segs -> (word -> option byte) -> sptr -> Z -> Prop.
Variable dpost : Z -> alayout -> astate -> world im_segs -> list Z -> Z -> (word -> option byte) -> Prop.
Variable dbody : astate -> M unit.
Variable L24 : Z.
Variable QB : astate -> Prop.
(* DGif0.DIface's memory predicate at Put's call of Enqueue (DIfaceR.enq_spec_g's premise). *)
Variable MP : (word -> option byte) -> Prop.

(* The Enqueue and Drain contracts with errno at the leaf's form. *)
Definition enq_spec_b_e (rawb : bool) : Prop := enq_spec_g B U ARX AOX rpre lpost fpre dpost L24 QB MP (acall_e_b rawb B AOX).
Definition drain_spec_b_e (rawb : bool) : Prop := drain_spec_g B ARX AOX dbody L24 QB (acall_e_b rawb B AOX).

Lemma enq_spec_b_e_false : ErrnoG.de_enqueue_v_t B U ARX AOX rpre lpost fpre dpost L24 QB MP -> enq_spec_b_e false.
Proof. intros H. exact H. Qed.
Lemma enq_spec_b_e_true : ErrnoG.de_enqueue_t B U ARX AOX rpre lpost fpre dpost L24 QB MP -> enq_spec_b_e true.
Proof. intros H. exact H. Qed.
Lemma drain_spec_b_e_false : ErrnoG.de_drain_v_t B ARX AOX dbody L24 QB -> drain_spec_b_e false.
Proof. intros H. exact H. Qed.
Lemma drain_spec_b_e_true : ErrnoG.de_drain_t B ARX AOX dbody L24 QB -> drain_spec_b_e true.
Proof. intros H. exact H. Qed.

(* DIfaceR.dealloc_leaf_b, with errno kept at its form. *)
Definition dealloc_leaf_b_e (rawb : bool) (inst : Z) (ly : alayout) (S : astate) (W : world im_segs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (p : sptr) (n : Z) (tr : list Z)
(r : unit * astate) (W' : world im_segs) (c' : config) : Prop :=
exists ly' regs' mem' md',
c' = cfg_at im_segs (raZ regs) regs' mem' md' /\
dealloc_post im_segs B ARX AOX inst ly S W regs mem md
  (fun a => p <> PNull /\ sptr_addr B ly p <= a < sptr_addr B ly p + req_size n) ly' (snd r) W' regs' mem' md' /\
(rawb = true -> forall x : word, ~ AOX ly S (bv_unsigned x) -> ~ AOX ly' (snd r) (bv_unsigned x) ->
  ~ ascratch B DFSTACK_G regs (bv_unsigned x) ->
  ~ (p <> PNull /\ sptr_addr B ly p <= bv_unsigned x < sptr_addr B ly p + req_size n) -> mem' x = mem x) /\
errno_kept_b rawb B W W' mem mem' /\
lpost (snd r) /\
(exists trc, apath (ft p tr S) trc r /\ gflag trc = true).

Lemma leaf_b_e_b : forall rawb inst ly S W regs mem md p n tr r W' c',
dealloc_leaf_b_e rawb inst ly S W regs mem md p n tr r W' c' ->
dealloc_leaf_b B ft ARX AOX lpost rawb inst ly S W regs mem md p n tr r W' c'.
Proof.
intros rawb inst ly S W regs mem md p n tr r W' c' (ly' & regs' & mem' & md' & Hc & HP & HR & _ & HL & HT).
exists ly', regs', mem', md'. split; [exact Hc|]. split; [exact HP|]. split; [exact HR|]. split; [exact HL | exact HT].
Qed.

Lemma leaf_b_e_view : forall inst ly S W regs mem md p n tr r W' c',
dealloc_leaf_b_e false inst ly S W regs mem md p n tr r W' c' ->
ErrnoG.dealloc_leaf_e im_segs B ft ARX AOX lpost inst ly S W regs mem md p n tr r W' c'.
Proof.
intros inst ly S W regs mem md p n tr r W' c' (ly' & regs' & mem' & md' & Hc & HP & _ & HE & HL & HT).
exists ly', regs', mem', md'. split; [exact Hc|]. split; [exact HP|]. split; [exact HE|]. split; [exact HL | exact HT].
Qed.

Lemma leaf_b_e_raw : forall inst ly S W regs mem md p n tr r W' c',
dealloc_leaf_b_e true inst ly S W regs mem md p n tr r W' c' ->
ErrnoG.dealloc_leaf_raw_e im_segs B ft ARX AOX lpost inst ly S W regs mem md p n tr r W' c'.
Proof.
intros inst ly S W regs mem md p n tr r W' c'
  (ly' & regs' & mem' & md' & Hc & (H1 & H2 & H3 & H4 & H5 & H6 & H7) & HR & HE & HL & HT).
exists ly', regs', mem', md'. split; [exact Hc|].
split; [|split; [exact HE | split; [exact HL | exact HT]]].
repeat (split; [assumption|]). split; [exact (HR eq_refl)|]. exact H7.
Qed.

(* DeallocG.dealloc_leaf_raw, with errno kept on the raw memory and on the view (an arm whose walk returns to the
   world it starts in has both). *)
Definition dealloc_leaf_raw_ee (inst : Z) (ly : alayout) (S : astate) (W : world im_segs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (p : sptr) (n : Z) (tr : list Z)
(r : unit * astate) (W' : world im_segs) (c' : config) : Prop :=
exists ly' regs' mem' md',
c' = cfg_at im_segs (raZ regs) regs' mem' md' /\
dealloc_post_raw im_segs B ARX AOX inst ly S W regs mem md
  (fun a => p <> PNull /\ sptr_addr B ly p <= a < sptr_addr B ly p + req_size n) ly' (snd r) W' regs' mem' md' /\
ErrnoG.errno_kept B mem mem' /\
ErrnoG.errno_kept_v im_segs B W W' mem mem' /\
lpost (snd r) /\
(exists trc, apath (ft p tr S) trc r /\ gflag trc = true).

Lemma leaf_raw_ee_raw_e : forall inst ly S W regs mem md p n tr r W' c',
dealloc_leaf_raw_ee inst ly S W regs mem md p n tr r W' c' ->
ErrnoG.dealloc_leaf_raw_e im_segs B ft ARX AOX lpost inst ly S W regs mem md p n tr r W' c'.
Proof.
intros inst ly S W regs mem md p n tr r W' c' (ly' & regs' & mem' & md' & Hc & HP & HE & _ & HL & HT).
exists ly', regs', mem', md'. split; [exact Hc|]. split; [exact HP|]. split; [exact HE|]. split; [exact HL | exact HT].
Qed.

Lemma leaf_raw_ee_b_e : forall rawb inst ly S W regs mem md p n tr r W' c',
dealloc_leaf_raw_ee inst ly S W regs mem md p n tr r W' c' ->
dealloc_leaf_b_e rawb inst ly S W regs mem md p n tr r W' c'.
Proof.
intros rawb inst ly S W regs mem md p n tr r W' c'
  (ly' & regs' & mem' & md' & Hc & (H1 & H2 & H3 & H4 & H5 & H6 & HR & H7) & HE & HEv & HL & HT).
exists ly', regs', mem', md'. split; [exact Hc|].
split; [repeat (split; [assumption|]); exact H7|].
split; [intros _; exact HR|].
split; [destruct rawb; [exact HE | exact HEv]|].
split; [exact HL | exact HT].
Qed.
End b.
End a.
