(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac SysStep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
Section WithCeil.
Context {CEILV : CEIL}.
Definition tls_ok (tb : Z) : Prop :=
  tb mod 16 = 0 /\ 0 < tb /\ tb + 4096 <= alloc_ceiling /\ (tb = 0x34190 \/ (0x34190 <= tb /\ tb + 4096 <= 0x54260)).
(* [comment removed for export] *)

Class TlsBase : Type := mkTB { the_tb : Z ; the_tb_ok : tls_ok the_tb }.
End WithCeil.


Notation RATP := (the_tb + 200).
Notation RERRNO := (the_tb + 36).

(* [comment removed for export] *)
Notation ps_fa := ps_rest (only parsing).
Notation ps_so := ps_rest (only parsing).

Section WithCeil.
Context {CEILV : CEIL}.
Section Facts.
Context {TB : TlsBase}.

#[using="Type"] Lemma the_tb_facts : the_tb mod 16 = 0 /\ 0 < the_tb /\ the_tb + 4096 <= alloc_ceiling
                     /\ (the_tb = 0x34190 \/ (0x34190 <= the_tb /\ the_tb + 4096 <= 0x54260)).
Proof. exact the_tb_ok. Qed.

#[using="Type"] Lemma RATP_range : 0 <= the_tb + 200 < 2^64.
Proof. pose proof the_tb_facts. ceil_facts. lia. Qed.

#[using="Type"] Lemma RATP_unsigned : bv_unsigned (Z_to_bv 64 (the_tb + 200)) = the_tb + 200.
Proof. apply unsigned_lit. apply RATP_range. Qed.

#[using="Type"] Lemma rerrno_addr : forall tp : bv 64, tp = Z_to_bv 64 (the_tb + 200) -> errno_addr tp = the_tb + 36.
Proof. intros tp ->. rewrite RATP_unsigned. lia. Qed.

#[using="Type"] Lemma tls_page_below_ceiling : the_tb + 4096 <= alloc_ceiling.
Proof. pose proof the_tb_facts. lia. Qed.

End Facts.

End WithCeil.
