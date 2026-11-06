(* reac-pw/fuzz_headamp image B (fuzz_headamp.asan-ubsan, pinned sha256
   53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94): the walk Section hypothesis HBerrno of the
   parse's image-B walk (lib/AU/HPgParse.v: as_errno B = 0x5d812c) at image B's real instance. The cell 0x5d812c is
   the start-up record's TFIB_ERRNO (lib/AU/YF0m.v), which its field ts_errno makes as_errno of the run's symbol
   record, so the assembly discharges HBerrno by that field. Here: HBerrno and errno_low (api_env) are satisfiable
   together on image B's segments (the cell lies in a loaded segment below kLowMemEnd: api_env's first two
   clauses), and the cell is apart from every image address the walk reads after the strtol call (which may write
   errno): the doubles [0x10340, 0x103f8), the key and strcmp literals [0x214a0, 0x21505), the .got word
   [0x9d478, 0x9d480) below the cell, and the stack-guard object [0x5f8210, 0x5f8218) above it. Proves no function
   (kind: statement text satisfiability). *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YM05 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import Img0U.
Import ListNotations.
Local Open Scope Z_scope.

Definition PB_ERRNO : Z := 0x5d812c.

Lemma pb_errno_img : 0 <= PB_ERRNO /\ PB_ERRNO + 4 <= kLowMemEnd /\
  forall a, PB_ERRNO <= a < PB_ERRNO + 4 -> in_img rsegs a.
Proof.
unfold PB_ERRNO. split; [lia|]. split; [unfold kLowMemEnd; lia|].
intros a Ha.
assert (E : existsb (fun s : Segment => (Z.of_N (seg_base s) <=? 0x5d812c) &&
  (0x5d812c + 4 <=? Z.of_N (seg_base s) + Z.of_N (seg_size s))) rsegs = true) by (vm_compute; reflexivity).
apply existsb_exists in E as (sg & Hin & Hb). apply andb_prop in Hb as [H1 H2].
apply Z.leb_le in H1. apply Z.leb_le in H2. exists sg. split; [exact Hin | lia].
Qed.

Lemma pb_errno_apart : 0x103f8 <= PB_ERRNO /\ 0x21505 <= PB_ERRNO /\ 0x9d480 <= PB_ERRNO /\
  PB_ERRNO + 4 <= 0x5f8210.
Proof. unfold PB_ERRNO. lia. Qed.

Print Assumptions pb_errno_img.
