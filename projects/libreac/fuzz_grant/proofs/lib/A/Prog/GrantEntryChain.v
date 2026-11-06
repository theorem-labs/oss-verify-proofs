(* The phase machine of the ASan walk of LLVMFuzzerTestOneInput: the twelve phase
   lemmas (:33-47), seven of the form `ge_from POST GI_next -> ge_from POST GI_self` (ph_init and ph_setup take two next cuts, ph_head two and ends at `ge_start`, ph_end and ph_leave none), chained into
   the whole call from its first slot (`ge_start`), at the post-condition `ge_post`.

   The order of the cuts (lib/A/Prog/GrantEntryDefs.v):
     0x806b0 entry -> 0x80944 GI_hdr -> 0x8098c GI_mallocT -> 0x80aa4 GI_set (loop)
     -> 0x80cd0 GI_unset0 -> 0x80d90 GI_admit -> 0x80e58 GI_sweep -> 0x812ac GI_raw
     -> 0x813b8 GI_sched0 -> 0x815c4 GI_sched (loop) -> 0x817c8 GI_freeT
     -> 0x818b8 GI_leave -> ret.
   Two cuts have a second way in: GI_unset0 (an input that sets no cell skips the set
   loop) and GI_freeT (a frame count of 0 skips the scheduler). *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import
YK11 YK0s YK14 YK15 YK18 YP09 YCbn YI04 YI09 YI00 YN3v YG0v YK04 YA0i YA0n YCbm YCbq YI16 YC5d YM05.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaJournal GrantSyms GrantList GrantPa GrantPaLib GrantBase GrantEntryDefs.
Import ListNotations.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {PI : PAImg grant_listing}.
Variable B : asyms.
Variable MT : ameter_ops.

#[local] Notation P := (ge_post B MT).

(* Each phase, at the post-condition of the call; the phase files prove them for every
   POST, so each statement is that phase's theorem applied to `ge_post B MT`. *)
Definition ph_head : Prop :=
  ge_from B MT P (GI_hdr B) -> ge_from B MT P (GI_leave B MT) -> ge_start B MT P.
Definition ph_hdr : Prop := ge_from B MT P (GI_mallocT B) -> ge_from B MT P (GI_hdr B).
Definition ph_init : Prop :=
  ge_from B MT P (GI_set B MT) -> ge_from B MT P (GI_unset0 B MT) -> ge_from B MT P (GI_mallocT B).
Definition ph_set : Prop := ge_from B MT P (GI_unset0 B MT) -> ge_from B MT P (GI_set B MT).
Definition ph_unset : Prop := ge_from B MT P (GI_admit B MT) -> ge_from B MT P (GI_unset0 B MT).
Definition ph_admit : Prop := ge_from B MT P (GI_sweep B MT) -> ge_from B MT P (GI_admit B MT).
Definition ph_sweep : Prop := ge_from B MT P (GI_raw B MT) -> ge_from B MT P (GI_sweep B MT).
Definition ph_raw : Prop := ge_from B MT P (GI_sched0 B MT) -> ge_from B MT P (GI_raw B MT).
Definition ph_setup : Prop :=
  ge_from B MT P (GI_sched B MT) -> ge_from B MT P (GI_freeT B MT) -> ge_from B MT P (GI_sched0 B MT).
Definition ph_turn : Prop := ge_from B MT P (GI_freeT B MT) -> ge_from B MT P (GI_sched B MT).
Definition ph_end : Prop := ge_from B MT P (GI_freeT B MT).
Definition ph_leave : Prop := ge_from B MT P (GI_leave B MT).

Theorem ge_chain : ph_head -> ph_hdr -> ph_init -> ph_set -> ph_unset -> ph_admit ->
  ph_sweep -> ph_raw -> ph_setup -> ph_turn -> ph_end -> ph_leave -> ge_start B MT P.
Proof.
  intros PH_head PH_hdr PH_init PH_set PH_unset PH_admit PH_sweep PH_raw PH_setup PH_turn
    PH_end PH_leave.
  pose proof (PH_turn PH_end) as Hsched.
  pose proof (PH_setup Hsched PH_end) as Hsched0.
  pose proof (PH_unset (PH_admit (PH_sweep (PH_raw Hsched0)))) as Hunset0.
  exact (PH_head (PH_hdr (PH_init (PH_set Hunset0) Hunset0)) PH_leave).
Qed.

End a.
