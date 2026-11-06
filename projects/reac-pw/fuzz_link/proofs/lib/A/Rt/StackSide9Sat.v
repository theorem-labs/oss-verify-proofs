(* Satisfiability of the class-9 side-stack contracts' own premises (lib/A/Rt/StackSide9.v) at link's code.
   The shared premise ecall_pre (AR, the stack window, ra / gp / tp) is the premise of every runtime contract of the
   unit; the premises below are the class-9 ones:
   - frame_alloc_9: `getr regs 10 = w64 n`, `8 <= n <= fs_frame_bytes 9`, `n mod 8 = 0`,
     `count_cid 9 (frames S) < fs_frames 9`, `apath (stack_malloc 9 S) [] (PFake 9 pos, S')`;
   - frame_release_9: `In (9, pos) (frames S)`, a0 = frame_addr ly 9 pos, a1 = n with the same bounds, and the
     word at frame_addr ly 9 pos + fs_frame_bytes 9 - 8 equal to flag_addr ly 9 pos.
   side9_size_sat: nl_talk's n = 0x4120 (16672; `lui a0,4; addiw a0,a0,0x120` at 0x889f0 before the call at 0x889f8,
   and `lui a0,4; addiw a1,a0,0x120` at 0x88e7c before the call at 0x88e88) meets both size premises.
   side9_model_sat: in every AR state with a free class-9 slot the model takes a slot pos (so the apath premise is
   met for some pos and S'), and that slot is live in S' (the release's `In (9, pos) (frames S)` at S := S').
   side9_release_pre_of_alloc_post: the alloc Post's a0 and flag-word conjuncts are the release's a0 and flag-word
   premises for the same pos, and its AR at S' carries the model state the release names; so the release contract
   applies to the frame the alloc contract returns (nl_talk keeps a0 in s4 / [s1 + 0x20] and does not write the
   frame's last word: its frame use is 16672 bytes < 32760). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YG05.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 AsStackSz StackFreeDef.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB1v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require Import StackSide9.
Import ListNotations.
Open Scope Z_scope.

Lemma side9_size_sat : 8 <= 0x4120 <= fs_frame_bytes CID9 /\ 0x4120 mod 8 = 0.
Proof. change (fs_frame_bytes CID9) with 32768. split; [lia | reflexivity]. Qed.

(* The model's stack_malloc puts the slot it takes on the live list. *)
Lemma stack_malloc_path_live : forall s cid pos s',
apath (stack_malloc cid s) [] (PFake cid pos, s') -> In (cid, pos) (frames s').
Proof.
intros s cid pos s' H. unfold stack_malloc, bind, get, put, ret in H. cbn [ibind] in H.
destruct (fs_probe _ _ _ _) as [[p h']|]; cbn [ibind apath] in H; [|discriminate].
injection H as E1 E2. subst. unfold frames. cbn. left. reflexivity.
Qed.

Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

Lemma side9_model_sat : forall B ly S (W : world tfibsegs) mem md,
AR tfibsegs B ly S W mem md -> count_cid CID9 (frames S) < fs_frames CID9 ->
exists pos S', apath (stack_malloc CID9 S) [] (PFake CID9 pos, S') /\ In (CID9, pos) (frames S').
Proof.
intros B ly S W mem md HAR Hc. destruct HAR as [MA _].
pose proof (am_wf B ly S _ MA) as WF.
destruct (stack_malloc_progress _ S CID9 WF ltac:(unfold CID9; lia) Hc) as (pos & S' & P).
exists pos, S'. split; [exact P | exact (stack_malloc_path_live S CID9 pos S' P)].
Qed.

(* With no live class-9 frame (nl_talk is the only class-9 user and is not re-entered), the count premise holds. *)
Lemma side9_count_sat : forall S, count_cid CID9 (frames S) = 0 -> count_cid CID9 (frames S) < fs_frames CID9.
Proof. intros S H. rewrite H. change (fs_frames CID9) with 32. lia. Qed.

Lemma side9_release_pre_of_alloc_post : forall ly S' (W : world tfibsegs) regs' mem' pos n,
getr regs' 10 = w64 (frame_addr ly CID9 pos) ->
rdword (aview tfibsegs (w_H W) mem') (frame_addr ly CID9 pos + fs_frame_bytes CID9 - 8) = Some (flag_addr ly CID9 pos) ->
In (CID9, pos) (frames S') -> 8 <= n <= fs_frame_bytes CID9 -> n mod 8 = 0 ->
forall regs2, getr regs2 10 = getr regs' 10 -> getr regs2 11 = w64 n ->
In (CID9, pos) (frames S') /\ getr regs2 10 = w64 (frame_addr ly CID9 pos) /\ getr regs2 11 = w64 n /\
8 <= n <= fs_frame_bytes CID9 /\ n mod 8 = 0 /\
rdword (aview tfibsegs (w_H W) mem') (frame_addr ly CID9 pos + fs_frame_bytes CID9 - 8) = Some (flag_addr ly CID9 pos).
Proof.
intros ly S' W regs' mem' pos n Ha0 Hfl Hin Hn Hm regs2 E10 E11.
split; [exact Hin|]. split; [rewrite E10; exact Ha0|]. split; [exact E11|]. split; [exact Hn|]. split; [exact Hm|]. exact Hfl.
Qed.

(* Both contracts at nl_talk's size, chained: an AR state with no live class-9 frame meets every class-9 premise of
   frame_alloc_9 for n = 0x4120, and the slot it takes is live for frame_release_9. *)
Theorem side9_pre_sat : forall B ly S (W : world tfibsegs) mem md,
AR tfibsegs B ly S W mem md -> count_cid CID9 (frames S) = 0 ->
exists pos S',
(8 <= 0x4120 <= fs_frame_bytes CID9 /\ 0x4120 mod 8 = 0) /\
count_cid CID9 (frames S) < fs_frames CID9 /\
apath (stack_malloc CID9 S) [] (PFake CID9 pos, S') /\
In (CID9, pos) (frames S').
Proof.
intros B ly S W mem md HAR H0.
pose proof (side9_count_sat S H0) as Hc.
destruct (side9_model_sat B ly S W mem md HAR Hc) as (pos & S' & P & L).
exists pos, S'. split; [exact side9_size_sat|]. split; [exact Hc|]. split; [exact P | exact L].
Qed.
End s.
