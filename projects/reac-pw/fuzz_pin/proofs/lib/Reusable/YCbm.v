(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YCbm.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_knock/lib/Reusable/YCbm.v at origin/ossv/recipes 6ebe35ba632 (fuzz_knock's released ASan tree); module paths changed to reac-pw/fuzz_pin. *)
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK0n YK18 YK0j YP0n.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import
YP0m YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YK04 YA0i YA0n YA0o.
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
Definition run_post_tok (W : world segs) (E : env) (K : nat) (Bx : sv) (SH : list shent) (ss : sstate) (st' : shst)
(r : trun_status) (ms : machine_state) (model : Model) (Q : world segs -> config -> Prop) : Prop :=
forall ws ms' mat',
length ws = sh_j st' ->
match r with TS_ecall => st_ok_ecall segs (extK E K ws) (sh_ss st') (restrict (w_H W) ms')
| _ => st_ok segs (extK E K ws) (sh_ss st') (restrict (w_H W) ms') end ->
sh_ok segs Bx SH (extK E K ws) (mrestrict (w_H W) (ms_mem ms')) ->
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms') ->
frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
SRr segs W (mkCfg ms' (with_vm_backing (m_vm_lazy model) mat' model)) Q.
Lemma SRr_run_tok_gen : forall W n E K Bx Bspan SH ss st' r ms model Q,
st_ok segs E ss (restrict (w_H W) ms) ->
sh_ok segs Bx SH E (mrestrict (w_H W) (ms_mem ms)) ->
sh_static_ok K Bx Bspan SH (ss_facts ss) (ss_mem ss) = true ->
sym_runN_tok segs tbl K Bx Bspan SH n ss = (st', r) ->
Forall (ob_holds segs Bx E (mrestrict (w_H W) (ms_mem ms))) (sh_obls st') ->
run_post_tok W E K Bx SH ss st' r ms model Q ->
SRr segs W (mkCfg ms model) Q.
Proof.
intros W n E K Bx Bspan SH ss st' r ms model Q HS Hsh Hchk Hrun Hobl Hk.
destruct (sym_run_tok_sound segs tbl K Bx Bspan SH tbl_ok n E ss _ st' r HS Hsh Hchk Hrun Hobl)
as (ws & msr' & Hlen & Hms & HS' & Hsh' & _ & Hfr).
apply (SRr_msteps segs Hwx W ms msr' model Q Hms).
intros model' Hsame Hcl.
rewrite (same_but_materialized_wvb model model' Hsame).
pose proof (restrict_unrestrict_clean (w_H W) (ms_mem ms) msr' Hcl) as Hrr.
apply (Hk ws (unrestrict (w_H W) (ms_mem ms) msr') (m_vm_materialized model') Hlen).
- rewrite Hrr. exact HS'.
- change (mrestrict (w_H W) (ms_mem (unrestrict (w_H W) (ms_mem ms) msr')))
with (ms_mem (restrict (w_H W) (unrestrict (w_H W) (ms_mem ms) msr'))).
rewrite Hrr. exact Hsh'.
- cbn [unrestrict ms_mem]. apply frame_of_unrestrict. exact Hfr.
- change (mrestrict (w_H W) (ms_mem (unrestrict (w_H W) (ms_mem ms) msr')))
with (ms_mem (restrict (w_H W) (unrestrict (w_H W) (ms_mem ms) msr'))).
rewrite Hrr. exact Hfr.
Qed.
Lemma SRr_run_to_tok_gen : forall W n stop E K Bx Bspan SH ss st' r ms model Q,
st_ok segs E ss (restrict (w_H W) ms) ->
sh_ok segs Bx SH E (mrestrict (w_H W) (ms_mem ms)) ->
sh_static_ok K Bx Bspan SH (ss_facts ss) (ss_mem ss) = true ->
sym_run_toN_tok segs tbl K Bx Bspan SH n stop ss = (st', r) ->
Forall (ob_holds segs Bx E (mrestrict (w_H W) (ms_mem ms))) (sh_obls st') ->
run_post_tok W E K Bx SH ss st' r ms model Q ->
SRr segs W (mkCfg ms model) Q.
Proof.
intros W n stop E K Bx Bspan SH ss st' r ms model Q HS Hsh Hchk Hrun Hobl Hk.
destruct (sym_run_to_tok_sound segs tbl K Bx Bspan SH tbl_ok n stop E ss _ st' r HS Hsh Hchk Hrun Hobl)
as (ws & msr' & Hlen & Hms & HS' & Hsh' & _ & Hfr).
apply (SRr_msteps segs Hwx W ms msr' model Q Hms).
intros model' Hsame Hcl.
rewrite (same_but_materialized_wvb model model' Hsame).
pose proof (restrict_unrestrict_clean (w_H W) (ms_mem ms) msr' Hcl) as Hrr.
apply (Hk ws (unrestrict (w_H W) (ms_mem ms) msr') (m_vm_materialized model') Hlen).
- rewrite Hrr. exact HS'.
- change (mrestrict (w_H W) (ms_mem (unrestrict (w_H W) (ms_mem ms) msr')))
with (ms_mem (restrict (w_H W) (unrestrict (w_H W) (ms_mem ms) msr'))).
rewrite Hrr. exact Hsh'.
- cbn [unrestrict ms_mem]. apply frame_of_unrestrict. exact Hfr.
- change (mrestrict (w_H W) (ms_mem (unrestrict (w_H W) (ms_mem ms) msr')))
with (ms_mem (restrict (w_H W) (unrestrict (w_H W) (ms_mem ms) msr'))).
rewrite Hrr. exact Hfr.
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
Ltac srr_after_run_tok HS SHOK :=
let ws := fresh "ws" in let ms' := fresh "ms" in let mat' := fresh "mat" in
let Hlen := fresh "Hlen" in let HF := fresh "HF" in let HFr := fresh "HFr" in
intros ws ms' mat' Hlen HS SHOK HF HFr;
cbn [sh_j sh_ss] in Hlen, HS, SHOK;
repeat (let w := fresh "w" in
destruct ws as [|w ws]; [discriminate Hlen | cbn [length] in Hlen; apply eq_add_S in Hlen || injection Hlen as Hlen]);
(destruct ws; [clear Hlen | discriminate Hlen]);
cbn [extK] in HS, SHOK;
cbn [ms_mem mkst pend_at] in HF, HFr;
try match type of HS with context [restrict _ ?msn] =>
repeat match goal with
| old : machine_state |- _ => lazymatch old with msn => fail | _ => clear old end
end
end;
srr_norm_model.
Ltac srr_obls :=
lazymatch goal with
| |- Forall _ nil => apply Forall_nil
| |- Forall _ _ => repeat (apply Forall_cons; [unfold ob_holds; cbn [ob_x ob_n]|]); [..|apply Forall_nil]
| _ => idtac
end.
Ltac srr_run_tok tblok HS SHOK Bspan :=
lazymatch type of HS with
| st_ok ?segs ?E ?ss (restrict (w_H ?W) ?ms) =>
lazymatch type of SHOK with
| sh_ok _ ?Bx ?SH _ _ =>
lazymatch type of tblok with
| table_ok _ ?tbl =>
let K := eval vm_compute in (run_K 0 Bx SH ss) in
let r := eval vm_compute in (sym_runN_tok segs tbl K Bx Bspan SH FUEL ss) in
lazymatch r with
| (?st', ?rs) =>
let Hrun := fresh "Hrun" in
assert (Hrun : sym_runN_tok segs tbl K Bx Bspan SH FUEL ss = (st', rs)) by (vm_compute; reflexivity);
let HWX := lazymatch goal with HWX : wx_segs_nowrap segs |- _ => HWX
| _ => fail "srr_run_tok: no hypothesis  wx_segs_nowrap segs" end in
eapply (SRr_run_tok_gen segs tbl tblok HWX W FUEL E K Bx Bspan SH ss st' rs ms _ _ HS SHOK
ltac:(vm_compute; reflexivity) Hrun);
[ clear Hrun; cbn [sh_obls]; srr_obls
| clear Hrun HS SHOK;
try match type of ms with machine_state => clear ms | _ => idtac end;
srr_after_run_tok HS SHOK ]
end
end end
| _ => fail "srr_run_tok: HS must be  st_ok segs E ss (restrict (w_H W) ms)"
end.
Ltac srr_run_to_tok tblok HS SHOK Bspan stop :=
lazymatch type of HS with
| st_ok ?segs ?E ?ss (restrict (w_H ?W) ?ms) =>
lazymatch type of SHOK with
| sh_ok _ ?Bx ?SH _ _ =>
lazymatch type of tblok with
| table_ok _ ?tbl =>
let K := eval vm_compute in (run_K 0 Bx SH ss) in
let r := eval vm_compute in (sym_run_toN_tok segs tbl K Bx Bspan SH FUEL stop ss) in
lazymatch r with
| (?st', ?rs) =>
let Hrun := fresh "Hrun" in
assert (Hrun : sym_run_toN_tok segs tbl K Bx Bspan SH FUEL stop ss = (st', rs)) by (vm_compute; reflexivity);
let HWX := lazymatch goal with HWX : wx_segs_nowrap segs |- _ => HWX
| _ => fail "srr_run_to_tok: no hypothesis  wx_segs_nowrap segs" end in
eapply (SRr_run_to_tok_gen segs tbl tblok HWX W FUEL stop E K Bx Bspan SH ss st' rs ms _ _ HS SHOK
ltac:(vm_compute; reflexivity) Hrun);
[ clear Hrun; cbn [sh_obls]; srr_obls
| clear Hrun HS SHOK;
try match type of ms with machine_state => clear ms | _ => idtac end;
srr_after_run_tok HS SHOK ]
end
end end
| _ => fail "srr_run_to_tok: HS must be  st_ok segs E ss (restrict (w_H W) ms)"
end.
Ltac srr_branch_tok tblok HS SHOK Bspan :=
lazymatch type of HS with
| st_ok ?segs ?E ?ss (restrict (w_H ?W) ?ms) =>
lazymatch type of SHOK with
| sh_ok _ ?Bx ?SH _ _ =>
lazymatch type of tblok with
| table_ok _ ?tbl =>
let K := eval vm_compute in (run_K 0 Bx SH ss) in
let why := sym_why_tok segs tbl K Bx Bspan SH (start K Bx Bspan SH ss) in
lazymatch why with
| SR_branch ?c ?a ?b =>
apply (SRr_sym_branch segs W E ss ms _ _ c a b HS);
clear HS;
let Hc := fresh "Hc" in
intros Hc HS
| _ => fail "srr_branch_tok: state is not stuck at a branch:" why
end
end end
end.
