(* reac-pw/fuzz_link, image A (the asan build, pin 059dae63e07c): fmemopen's contract at link's own instance, the
   form mark_quietly's walk cites at 0x88410 (`jal 0x430a8`): LinkFoSpec.v afmemopen_w_spec at the sink head
   link_asink_head, the segments tfibsegs, the asyms record PcapB, the memory FILE link_amf, the wrapper's jump
   LA_W_FMEMOPEN 0x430a8, the malloc call's return address LA_FM_MALLOC_RA 0x96ab8 (fmemopen +0x9c) and
   __strchrnul's constant window [0x10360, 0x10380) (lib/A/AE39.v MC_LO / MC_HI).
   The caller passes its own meter MT (the frame's malloc rule at PcapB is at the trivial meter, lib/A/PcapBFacts.v
   PcapB_AMALLOC4) and CTX = [[]]: at 0x88410 s0 is mark_quietly's second argument (0x883e8 `mv s0, a1`), an image
   address or 0, below alloc_ceiling, so the frame chain is empty (YCbq.v achain's first arm) and its spine is [];
   the image's trace universe holds the malloc row [0x5436c; 0x96ab8] (lib/A/ACej.v TRACES_fmemopen).
   The proof is LinkFoOk.v (afmemopen_w_ok, afmemopen_w_ok_pcapb). Statement only. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YM05 YG0f YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB1v AD2l AMemFile.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require Import LinkMfDefs LinkFoSpec.
Import ListNotations.
Local Open Scope Z_scope.

Definition link_afmemopen_contract {fx : YK11.FPState} {rc : YM05.RunCeil} (MT : ameter_ops) (CTX : list (list Z))
    : Prop :=
  afmemopen_w_spec link_asink_head tfibsegs PcapB link_amf MT CTX LA_W_FMEMOPEN LA_FM_MALLOC_RA 0x10360 0x10380.

(* the context mark_quietly's call passes *)
Definition link_afmemopen_ctx : list (list Z) := [[]].
