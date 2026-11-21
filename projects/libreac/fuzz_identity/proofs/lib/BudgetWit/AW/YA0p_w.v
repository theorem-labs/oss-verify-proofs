(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from projects/cgif/cgif_file_fuzzer/proofs/lib/YA0p.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from Reusable/YA0p.v for the ASan run at the 16 GiB limit (lib/BudgetWit/AW), with the modules it imports from that set renamed to their twins (suffix _w). *)
(* Theorem Labs, 2026-11: cut for the usage path at 16 GiB: the pruning removed declarations that this path does not use; some unused declarations can remain. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK0n.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import YK18_w.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK0j YP0n.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YP0m YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP0i YP0j.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import YA0n_w YA0o_w.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Section d.
Variable segs : list Segment.
Context {fx : FPState}.
Variable tbl : ctable.
Hypothesis tbl_ok : table_ok segs tbl.
Hypothesis Hwx : wx_segs_nowrap segs.
Local Notation run_post := (@run_post segs fx).
Local Notation SRr_of_restricted_chain := (@SRr_of_restricted_chain segs fx Hwx).

Lemma SRr_run_sh_gen : forall W n E ss ss' st ms model Q,
st_ok segs E ss (restrict (w_H W) ms) ->
sym_runN_sh segs tbl n ss = (ss', st) ->
run_post W E ss ss' st ms model Q ->
SRr segs W (mkCfg ms model) Q.
Proof.
intros W n E ss ss' st ms model Q HS Hrun Hk.
destruct (msteps_run_sh segs tbl tbl_ok n E ss ss' st _ HS Hrun) as (msr' & Hms & HS' & Hfr).
exact (SRr_of_restricted_chain W E ss ss' st ms msr' model Q Hms HS' Hfr Hk).
Qed.

Lemma SRr_run_to_sh_gen : forall W n stop E ss ss' st ms model Q,
st_ok segs E ss (restrict (w_H W) ms) ->
sym_run_toN_sh segs tbl n stop ss = (ss', st) ->
run_post W E ss ss' st ms model Q ->
SRr segs W (mkCfg ms model) Q.
Proof.
intros W n stop E ss ss' st ms model Q HS Hrun Hk.
destruct (msteps_run_to_sh segs tbl tbl_ok n stop E ss ss' st _ HS Hrun) as (msr' & Hms & HS' & Hfr).
exact (SRr_of_restricted_chain W E ss ss' st ms msr' model Q Hms HS' Hfr Hk).
Qed.
End d.

Ltac srr_run_sh tblok HS :=
lazymatch type of HS with
| st_ok ?segs ?E ?ss (restrict (w_H ?W) ?ms) =>
lazymatch type of tblok with
| table_ok _ ?tbl =>
let r := eval vm_compute in (sym_runN_sh segs tbl FUEL ss) in
lazymatch r with
| (?ss', ?st) =>
let Hrun := fresh "Hrun" in
assert (Hrun : sym_runN_sh segs tbl FUEL ss = (ss', st)) by (vm_compute; reflexivity);
let HWX := lazymatch goal with HWX : wx_segs_nowrap segs |- _ => HWX
| _ => fail "srr_run_sh: no hypothesis  wx_segs_nowrap segs" end in
eapply (SRr_run_sh_gen segs tbl tblok HWX W FUEL E ss ss' st ms _ _ HS Hrun);
clear Hrun HS;
try match type of ms with machine_state => clear ms | _ => idtac end;
srr_after_run HS
end
end
| _ => fail "srr_run_sh: HS must be  st_ok segs E ss (restrict (w_H W) ms)"
end.

Ltac srr_run_to_sh tblok HS stop :=
lazymatch type of HS with
| st_ok ?segs ?E ?ss (restrict (w_H ?W) ?ms) =>
lazymatch type of tblok with
| table_ok _ ?tbl =>
let r := eval vm_compute in (sym_run_toN_sh segs tbl FUEL stop ss) in
lazymatch r with
| (?ss', ?st) =>
let Hrun := fresh "Hrun" in
assert (Hrun : sym_run_toN_sh segs tbl FUEL stop ss = (ss', st)) by (vm_compute; reflexivity);
let HWX := lazymatch goal with HWX : wx_segs_nowrap segs |- _ => HWX
| _ => fail "srr_run_to_sh: no hypothesis  wx_segs_nowrap segs" end in
eapply (SRr_run_to_sh_gen segs tbl tblok HWX W FUEL stop E ss ss' st ms _ _ HS Hrun);
clear Hrun HS;
try match type of ms with machine_state => clear ms | _ => idtac end;
cbv beta iota;
srr_after_run HS
end
end
| _ => fail "srr_run_to_sh: HS must be  st_ok segs E ss (restrict (w_H W) ms)"
end.

Ltac srr_branch_sh tblok HS :=
lazymatch type of HS with
| st_ok ?segs ?E ?ss (restrict (w_H ?W) ?ms) =>
lazymatch type of tblok with
| table_ok _ ?tbl =>
let why := sym_why_sh segs tbl ss in
lazymatch why with
| SR_branch ?c ?a ?b =>
apply (SRr_sym_branch segs W E ss ms _ _ c a b HS);
clear HS;
let Hc := fresh "Hc" in
intros Hc HS
| _ => fail "srr_branch_sh: state is not stuck at a branch:" why
end
end
end.
