(** * reac-pw/fuzz_link (asan, image A): the side-stack entries link's code calls, and the contract of each.

    Link's own code calls __asan_stack_malloc_0, _1, _3, _4, _8, _9 and __asan_stack_free_8, _9, and no other
    __asan_stack_malloc_N / __asan_stack_free_N (script check: proofs/reac-pw/fuzz_link/provenance/evidence/af/
    af_stack_classes.out, against the pinned fuzz_link.asan, sha256 059dae63e07c...). The contracts:
    - classes 0, 1, 3, 4 (each <= 6): their entries (0x3d914, 0x3da88, 0x3dc18, 0x3ddc4) zero the WHOLE new
      frame's shadow ((64 << N) / 8 bytes, by inline stores after MemToShadow), which is what the AsanAPI record's
      [aa_stack_malloc] / [astack_malloc_realizes] states. The record admits them through [Tfib_code]'s table
      (lib/A/AF0l.v), and only them ([link_fs_admitted]);
    - classes 8 and 9: their entries (0x3df90, 0x3e15c) mark only the bytes the caller asks (the entry's a0 is kept in
      s1, then [mv a1, s1] before PoisonShadow(frame, n, 0)), so [astack_malloc_realizes]'s whole-frame zero shadow
      is false there and they are NOT in the record (the table maps them to 0, [link_fs_sized_out]; released
      libreac/fuzz_scene keeps its class 8 outside the record the same way). They carry the size-premised contract
      [astack_malloc_sz_realizes] (lib/Reusable/AsStackSz.v) as the Section hypotheses [SM8] / [SM9], which the
      walks of those two entries discharge ([link_stack_malloc_8] / [link_stack_malloc_9] of lib/A/Rt/StackSideInst.v,
      for every [B] with [PcapSyms B]);
    - releases: classes <= 6 release inline in the caller (the record's [aa_stack_free], [astack_free_law]);
      classes 8 and 9 call __asan_stack_free_8 / _9 (0x3e10c, 0x3e2d4), whose contract [astack_free_realizes]
      (lib/Reusable/StackFreeDef.v) is carried as the Section hypotheses [SF8] / [SF9].
    After the Section closes, each lemma takes the contracts it uses as premises ([link_stack_malloc_inline]: the
    record and [as_code B = Tfib_code]; [link_stack_malloc_sized]: [SM8], [SM9]; [link_stack_free_called]: [SF8],
    [SF9]); a consumer's walk states them as its own Section hypotheses (as fuzz_scene's
    P_LLVMFuzzerTestOneInput.v:281 does) or applies those walks' instances.

    Where the texts come from. [AsanAPI.aa_stack_malloc] (lib/Reusable/YG0d.v) admits a class iff
    [pc_stack_malloc (as_code B) cid <> 0], the released text of every libreac unit; link's [Tfib_code] (lib/A/AF0l.v)
    maps classes 0, 1, 3, 4 to the entries above and every other class to 0 (the script check above, with its two
    controls af_stack_classes.before.out and af_stack_classes.control.out). lib/Reusable/AsStackSz.v,
    StackFreeDef.v, StackFreeJournal.v and StackFreeRaw.v are released files taken by path (libreac/fuzz_scene and
    libreac/fuzz_disco at ossv/recipes 7cbe5270d908), byte-equal but for the module prefix (provenance/evidence/af/
    bypath_check.out); their headers describe the unit they come from: AsStackSz.v's says its record maps classes 1
    and 2, while in link the record maps 0, 1, 3, 4 and AsStackSz.v's contract serves classes 8 and 9. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import AsStackSz StackFreeDef.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AF0l.
Import ListNotations.
Local Open Scope Z_scope.

(** The classes the record admits, and the size-premised and out-of-line release entries, with their pcs. *)
Definition link_fs_inline : list Z := [0; 1; 3; 4].
Definition link_fs_sized : list (Z * Z) := [(8, 0x3df90); (9, 0x3e15c)].
Definition link_fs_free : list (Z * Z) := [(8, 0x3e10c); (9, 0x3e2d4)].

(** The record admits exactly the classes 0, 1, 3, 4 at link's code table. *)
Lemma link_fs_admitted : forall cid, pc_stack_malloc Tfib_code cid <> 0 <-> In cid link_fs_inline.
Proof.
  intros cid. cbn [pc_stack_malloc Tfib_code]. unfold link_fs_inline.
  destruct (Z.eqb_spec cid 0) as [->|H0]; [cbn; split; [intros _; left; reflexivity | intros _; discriminate]|].
  destruct (Z.eqb_spec cid 1) as [->|H1]; [cbn; split; [intros _; right; left; reflexivity | intros _; discriminate]|].
  destruct (Z.eqb_spec cid 3) as [->|H3]; [cbn; split; [intros _; do 2 right; left; reflexivity | intros _; discriminate]|].
  destruct (Z.eqb_spec cid 4) as [->|H4]; [cbn; split; [intros _; do 3 right; left; reflexivity | intros _; discriminate]|].
  split; [intros H; exfalso; apply H; reflexivity | intros Hin; cbn in Hin; lia].
Qed.

(** Classes 8 and 9 are outside the record: the table maps them to 0. *)
Lemma link_fs_sized_out : forall cid pc, In (cid, pc) link_fs_sized -> pc_stack_malloc Tfib_code cid = 0.
Proof. intros cid pc [E | [E | []]]; injection E as <- <-; reflexivity. Qed.

(** Every admitted class is in the model's class range and at most 6. *)
Lemma link_fs_inline_range : Forall (fun c => 0 <= c <= 6) link_fs_inline.
Proof. repeat constructor; lia. Qed.

Section s.
Context {rc : YM05.RunCeil}.
Variable segs : list Segment.
Variable B : asyms.
Hypothesis API : AsanAPI segs B.
Hypothesis CODE : as_code B = Tfib_code.
Hypothesis SM8 : forall fq : YK11.FPState, astack_malloc_sz_realizes (fx := fq) segs B 0x3df90 8.
Hypothesis SM9 : forall fq : YK11.FPState, astack_malloc_sz_realizes (fx := fq) segs B 0x3e15c 9.
Hypothesis SF8 : forall fq : YK11.FPState, astack_free_realizes (fx := fq) segs B 0x3e10c 8.
Hypothesis SF9 : forall fq : YK11.FPState, astack_free_realizes (fx := fq) segs B 0x3e2d4 9.

(** The contract of each stack-frame allocation entry link's code calls. *)
Lemma link_stack_malloc_inline : forall (fq : YK11.FPState) cid, In cid link_fs_inline ->
  astack_malloc_realizes (fx := fq) segs B cid.
Proof.
  intros fq cid H. apply (@aa_stack_malloc rc segs B API fq cid). rewrite CODE. apply link_fs_admitted. exact H.
Qed.

Lemma link_stack_malloc_sized : forall (fq : YK11.FPState) cid pc, In (cid, pc) link_fs_sized ->
  astack_malloc_sz_realizes (fx := fq) segs B pc cid.
Proof. intros fq cid pc [E | [E | []]]; injection E as <- <-; [exact (SM8 fq) | exact (SM9 fq)]. Qed.

(** The contract of each out-of-line release entry link's code calls. *)
Lemma link_stack_free_called : forall (fq : YK11.FPState) cid pc, In (cid, pc) link_fs_free ->
  astack_free_realizes (fx := fq) segs B pc cid.
Proof. intros fq cid pc [E | [E | []]]; injection E as <- <-; [exact (SF8 fq) | exact (SF9 fq)]. Qed.

End s.
