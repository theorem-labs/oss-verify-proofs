(* Modified by Theorem Labs, 2026-10: relocated from omx-clap-core/fuzz_manifest lib/A/FMgxaSeamDef.v (a working branch 7e395de08f5) to libreac/fuzz_boxreg.asan-ubsan: module paths changed; 0 address numerals relocated (port_addr_check 5033540ba83b predict mode, symbol + offset); re-pointed Requires: FMsnprintfShared, FMsnprintfPf, FMupoison -> lib.A.Rt. *)
(* THE SEAM'S FAMILY, and why the seam's statement has the shape it has.

   The statement, `sh_avfprintf_icpt_realizesUx`, has one home: a Theorem Labs lane's lib/A/FMsnprintfSx.v
   (a working branch 53d633d5fe5), copied verbatim from this file's earlier text.  It is
   Param's `sh_avfprintf_icpt_realizesU` (lib/A/FMsnprintfShared.v) with

   FOUR PREMISES ADDED, each a fact the released GXA statement asks for
   (lib/CJ/RL/GXA/VfprintfCall.v:22 vfprintf_guarded_stmt) and the frozen text does not carry.  All
   of them hold at musl vsnprintf's call site; Param discharges them there.
     (1) dest_nul       the destination already holds the NUL musl vsnprintf wrote (`*c.s = 0`);
                        with an empty output musl vfprintf never calls sn_write, so that byte is the
                        only NUL the post can report  (VfprintfCall.v:31)
     (2) frame order    sp <= fp, fp + 232 <= cp, cp + 16 <= ap  (VfprintfCall.v:40)
     (3) dest_off_slots the destination lies below the stack window or above the caller's slots
                        (VfprintfCall.v:42, first disjunction)
     (4) below 2^47     the FILE, the cookie and the slots lie below TASK_SIZE, where the normalized
                        store GXA runs on (FMgxaSeamNorm.v) keeps every byte
   The contract's dest_off_globals (the destination off the image range (ilo, ihi), which the caller
   names) gives GXA's `D + dn <= 65536 \/ GLOBALS_TOP <= D` (VfprintfCall.v:42, second disjunction)
   when ilo <= 65536 and GLOBALS_TOP <= ihi.
   The post's FP state is existential, as Param's text already states it (since 401616133a7): fa0
   is caller-saved and printf_core writes it through pop_arg for a double argument, so the released
   theorem states only `reg_get Ft k = reg_get F k` for k <> 10 and `frm0 fc'`
   (G_vfprintf_snf.v:69-70), while the harness's `cfg_at` pins both to the ambient FPState.  The
   seam hands over exactly GXA's two facts about the new FPState (FMgxaSeamFP.v fp_clause_of_gxa).
   Stream decision (a Theorem Labs lane, 03:44Z): the GXA-route contracts take this post; the pinned form stays
   only as fm's own instance, whose chain steps a walk that executes no FP instruction.

   The family is refined (pf_family_ro) because GXA reads the format as image data
   (`65536 <= A /\ A + |fmt| <= sym 0x22e18`, G_vfprintf_snf.v:210 and vf_ready_a:221), and it reads
   the slack word past each string, so pf_family's `amem_range w (|s| + 1)` must cover `str_end w s`.
   Both constrain only f and ws, which the family sees, so they stay on this side of the seam. *)
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Rt Require Import FMupoison FMsnprintfPf FMsnprintfShared.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Rt Require Import FMgxaSeamBase.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B Require Import AB1v.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.Lib Require Mem.
Import ListNotations.
Local Open Scope Z_scope.

(* ---- the family the GXA route proves the contract for ---- *)
(* the slack word past each string: GXA's args_ok asks the bytes from w + |s| + 1 up to str_end w s
   to be app memory, not only the string and its NUL.  Same walk over ws and args as pf_args_asan. *)
Fixpoint pf_args_slack (ws : list Z) (args : list pf_arg) : Prop :=
  match args, ws with
  | [], _ => True
  | APtr s :: args', w :: ws' => amem_range w (str_end w s - w) /\ pf_args_slack ws' args'
  | _ :: args', _ :: ws' => pf_args_slack ws' args'
  | _ :: _, [] => False
  end.

(* pf_family (FMsnprintfShared.v:92) refined by where the format lives and by that slack.
   ilo / ihi are the image range the caller names; at fuzz_boxreg.asan-ubsan, 0x10000 and sym 0x35000 = 0x5f6000. *)
Definition pf_family_ro (PK : pf_piece -> Prop) (ilo ihi : Z) : fmt_fam := fun rd rs f ws T =>
  exists (fmt : list Z) (ps : list pf_piece) (args : list pf_arg),
    fmt_at rd rs f fmt /\ pf_parse fmt = Some ps /\ Forall PK ps /\ pf_args_asan rd rs ws args /\
    pf_text ps args = Some T /\ pf_prec_pos ps args /\
    ilo <= f /\ f + Z.of_nat (length fmt) + 1 <= ihi /\ pf_args_slack ws args.

Lemma pf_family_ro_sub : forall PK ilo ihi rd rs f ws T,
  pf_family_ro PK ilo ihi rd rs f ws T -> pf_family PK rd rs f ws T.
Proof.
intros PK ilo ihi rd rs f ws T (fmt & ps & args & A & B & C & D & E & F & _ & _ & _).
exists fmt, ps, args. repeat (split; [assumption|]). exact F.
Qed.
