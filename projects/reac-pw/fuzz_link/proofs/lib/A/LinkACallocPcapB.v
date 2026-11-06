(* reac-pw/fuzz_link image A: lib/A/LinkACalloc.v's calloc contract and call rule at link's own certificate
   B := AD2l.PcapB (PcapSyms: AD2l.PcapB_syms; TfibLib: PcapBFacts.PcapB_lib; the depot hash is tfib_dhash by the
   definition of PcapB, as lib/A/AF0w.v pcap_amalloc_realizes uses it). *)
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YM05 YG00 YG0f YCbq YC5d YCbp YGCalloc.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import DecodeCallocKit.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB1v AD2l PcapBFacts DecodeCalloc LinkACalloc.
Open Scope Z_scope.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}
  {SK : OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable.YI16.sink_head}.
(* The realizes form at PcapB. *)
Theorem PcapB_calloc_realizes : decode_acalloc_A PcapB.
Proof. exact (link_calloc_realizes PcapB PcapB_syms PcapB_lib (fun _ => eq_refl)). Qed.
(* The call rule at PcapB, beside PcapBFacts.v's PcapB_AMALLOC4 / PcapB_AFREE4. *)
Definition PcapB_ACALLOC4 :
  acalloc04_rule tfibsegs PcapB (as_universe PcapB) (@ajournal rc SK tfibsegs PcapB) (@acall_kept rc tfibsegs PcapB)
    (mo_ok ameter_triv) (mo_le ameter_triv) (mo_malloc ameter_triv)
    DEC_A_wrap_calloc DEC_A_calloc_ra0 DEC_CALLOC_MAX DEC_CALLOC_DEPTH :=
  link_acalloc04 (SK := SK) PcapB PcapB_syms PcapB_lib (fun _ => eq_refl).
End b.
