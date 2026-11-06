(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/YP03.v, with its module paths and module names changed; 148 of its 218 lines of code are new or changed and 811 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: ported from libreac/fuzz_decode proofs/libreac/fuzz_decode/lib/Reusable/SymTac_cfw.v at bf7779f81ed764787b77895d2f5c0db2627f33f3 for libdiginet/fuzz_transport; no image value changed; module path OSSVerify.Proofs.libdiginet.fuzz_transport.lib. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK0n YK0p YP0n YM06 YM02.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP0f YP04 YN3v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YO0i YO0f YO0x YO0d YO05.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YH00 YH01 YH03 YH02 YN3e YN35.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YN03 YL07 YL01 YL08 YL0d YL0k.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05 YK15_cfw YP03_cfw YN35_cfw.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib Require Import SlotAgree AgreeLift.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac csym_run_with tblok HS :=
lazymatch goal with |- crealizes ?B _ _ =>
lazymatch type of HS with
| st_ok ?segs ?E ?ss ?ms =>
lazymatch type of tblok with
| table_ok _ ?tbl =>
let r := eval vm_compute in (sym_runN segs tbl FUEL ss) in
lazymatch r with
| (?ss', ?st) =>
let Hrun := fresh "Hrun" in
assert (Hrun : sym_runN segs tbl FUEL ss = (ss', st)) by (vm_compute; reflexivity);
let ms' := fresh "ms" in let HF := fresh "HF" in
lazymatch st with
| RS_ecall =>
eapply (crz_run_ecall B tbl tblok FUEL E ss ss' ms);
[ | | exact HS | exact Hrun | clear Hrun HS; intros ms' HS HF ]; [assumption|assumption|];
sym_transport_ecall segs E ss ss' ms' HS HF
| RS_stopped ?why =>
eapply (crz_run_stop B tbl tblok FUEL E ss ss' why ms);
[ | | exact HS | exact Hrun | clear Hrun HS; intros ms' HS HF ]; [assumption|assumption|];
sym_transport segs E ss ss' ms' HS HF
| RS_running =>
eapply (crz_run_running B tbl tblok FUEL E ss ss' ms);
[ | | exact HS | exact Hrun | clear Hrun HS; intros ms' HS HF ]; [assumption|assumption|];
sym_transport segs E ss ss' ms' HS HF
end
end
end
end
end.
Ltac csym_run_to_with tblok HS stop :=
lazymatch goal with |- crealizes ?B _ _ =>
lazymatch type of HS with
| st_ok ?segs ?E ?ss ?ms =>
lazymatch type of tblok with
| table_ok _ ?tbl =>
let r := eval vm_compute in (sym_run_toN segs tbl FUEL stop ss) in
lazymatch r with
| (?ss', ?st) =>
let Hrun := fresh "Hrun" in
assert (Hrun : sym_run_toN segs tbl FUEL stop ss = (ss', st)) by (vm_compute; reflexivity);
let ms' := fresh "ms" in let HF := fresh "HF" in
lazymatch st with
| RS_ecall =>
eapply (crz_run_to_ecall B tbl tblok FUEL stop E ss ss' ms);
[ | | exact HS | exact Hrun | clear Hrun HS; intros ms' HS HF ]; [assumption|assumption|];
sym_transport_ecall segs E ss ss' ms' HS HF
| RS_stopped ?why =>
eapply (crz_run_to_stop B tbl tblok FUEL stop E ss ss' why ms);
[ | | exact HS | exact Hrun | clear Hrun HS; intros ms' HS HF ]; [assumption|assumption|];
sym_transport segs E ss ss' ms' HS HF
| RS_running =>
eapply (crz_run_to_running B tbl tblok FUEL stop E ss ss' ms);
[ | | exact HS | exact Hrun | clear Hrun HS; intros ms' HS HF ]; [assumption|assumption|];
sym_transport segs E ss ss' ms' HS HF
end
end
end
end
end.
Ltac csym_run3_with tblok HS :=
lazymatch goal with |- crealizes ?B _ _ =>
lazymatch type of HS with
| st_ok ?segs ?E ?ss ?ms =>
lazymatch type of tblok with
| table_ok _ ?tbl =>
let r := eval vm_compute in (sym_runN segs tbl FUEL ss) in
lazymatch r with
| (?ss', ?st) =>
let Hrun := fresh "Hrun" in
assert (Hrun : sym_runN segs tbl FUEL ss = (ss', st)) by (vm_compute; reflexivity);
let ms' := fresh "ms" in let HF := fresh "HF" in
lazymatch st with
| RS_ecall =>
eapply (crz_run_ecall B tbl tblok FUEL E ss ss' ms);
[ | | exact HS | exact Hrun | clear Hrun HS; intros ms' HS HF ]; [assumption|assumption|];
sym_transport3_ecall segs E ss ss' ms' HS HF
| RS_stopped ?why =>
eapply (crz_run_stop B tbl tblok FUEL E ss ss' why ms);
[ | | exact HS | exact Hrun | clear Hrun HS; intros ms' HS HF ]; [assumption|assumption|];
sym_transport3 segs E ss ss' ms' HS HF
| RS_running =>
eapply (crz_run_running B tbl tblok FUEL E ss ss' ms);
[ | | exact HS | exact Hrun | clear Hrun HS; intros ms' HS HF ]; [assumption|assumption|];
sym_transport3 segs E ss ss' ms' HS HF
end
end
end
end
end.
Ltac csym_run3_to_with tblok HS stop :=
lazymatch goal with |- crealizes ?B _ _ =>
lazymatch type of HS with
| st_ok ?segs ?E ?ss ?ms =>
lazymatch type of tblok with
| table_ok _ ?tbl =>
let r := eval vm_compute in (sym_run_toN segs tbl FUEL stop ss) in
lazymatch r with
| (?ss', ?st) =>
let Hrun := fresh "Hrun" in
assert (Hrun : sym_run_toN segs tbl FUEL stop ss = (ss', st)) by (vm_compute; reflexivity);
let ms' := fresh "ms" in let HF := fresh "HF" in
eapply (crz_run_to_gen B tbl tblok FUEL stop E ss ss' st ms);
[ | | exact HS | exact Hrun | clear Hrun HS; intros ms' HS HF ]; [assumption|assumption|];
lazymatch st with
| RS_ecall => change (st_ok_ecall segs E ss' ms') in HS; sym_transport3_ecall segs E ss ss' ms' HS HF
| _ => change (st_ok segs E ss' ms') in HS; sym_transport3 segs E ss ss' ms' HS HF
end
end
end
end
end.
Ltac csym_branch_with tblok HS :=
lazymatch goal with |- crealizes ?B _ _ =>
lazymatch type of HS with
| st_ok ?segs ?E ?ss ?ms =>
lazymatch type of tblok with
| table_ok _ ?tbl =>
let why := sym_why segs tbl ss in
lazymatch why with
| SR_branch ?c ?a ?b =>
apply (crz_branch B E ss ms _ _ c a b HS);
clear HS;
let Hc := fresh "Hc" in
intros Hc HS
| _ => fail "csym_branch: state is not stuck at a branch:" why
end
end
end
end.
Ltac csym_exit_with HS :=
lazymatch type of HS with
| st_ok_ecall ?segs ?E ?ss ?ms =>
lazymatch goal with |- crealizes ?B (mkCfg _ ?model) (t_exit (Z_to_bv 64 ?code) _) =>
apply (crz_sym_exit B E ss ms model code);
[ assumption | assumption | exact HS | reflexivity
| first [left; reflexivity | right; reflexivity]
| reflexivity | lia ]
end
end.
Ltac csym_splice_havoc HS Hms k upd rl :=
lazymatch type of HS with st_ok ?segs ?E ?ss ?ms =>
lazymatch type of Hms with msteps _ _ (mkst ?regs' (Z_to_bv 64 ?pc') ?mem' _) =>
let Hshape := fresh "Hshape" in
pose proof (st_ok_mkst segs E ss ms HS eq_refl) as Hshape;
rewrite Hshape; eapply crealizes_msteps; [assumption | assumption | exact Hms | ];
rewrite Hshape in HS; clear Hshape;
let H := fresh "HS'" in
unshelve epose proof (st_ok_splice_havoc segs k E ss (ms_regs ms) regs' _ pc' (ms_mem ms) mem' (ss_mem ss) upd rl
HS _ _ _ _ _ _ _ _) as H;
[ vm_compute; reflexivity
| vm_compute; reflexivity
| vm_compute; reflexivity
| vm_compute; reflexivity
| vm_compute; reflexivity
| | |
| env_transport (havoc E k (map (getr regs') rl)) (env_agree_havoc E k (map (getr regs') rl));
clear HS Hms; rename H into HS; sym_norm HS ]
end end.
Ltac csym_step_manual HS Hstep upd :=
lazymatch type of HS with st_ok ?segs ?E ?ss ?ms =>
lazymatch type of Hstep with _ = MachineOk (mkst ?regs' (Z_to_bv 64 ?pc') _ _) =>
let Hshape := fresh "Hshape" in
pose proof (st_ok_mkst segs E ss ms HS eq_refl) as Hshape;
rewrite Hshape; eapply crealizes_msteps; [assumption | assumption | eapply msteps_one; [reflexivity | exact Hstep] | ];
rewrite Hshape in HS; clear Hshape;
let H := fresh "HS'" in
unshelve epose proof (st_ok_set_regs segs 1000%nat E E ss (ms_regs ms) regs' _ pc' (ms_mem ms) upd
HS (env_agree_refl 1000%nat E) _ _ _ _ _) as H;
[ vm_compute; reflexivity
| reflexivity
| vm_compute; reflexivity
| |
| clear HS Hstep; rename H into HS; sym_norm HS ]
end end.
Ltac csrc0_exit_tac HS :=
first
[ lazymatch type of HS with st_ok _ ?E ?ss ?ms =>
lazymatch goal with |- crealizes _ (mkCfg _ ?model) (t_exit (Z_to_bv 64 ?code) _) =>
apply (src0_exit_cf E ss ms model code HS); [lia | vm_compute; reflexivity | assumption | assumption]
end end
| csym_run_with src0tbl_ok HS; csym_exit_with HS ].
Ltac cat_node k :=
lazymatch goal with
| Hregs : regs_ok ?E ?sr _, Hmem : mem_ok _ _ _ ?rs, HG : facts_ok _ ?G
|- crealizes _ (mkCfg (mkst (regupd _ 10 ?RET) (v_addi (Z_to_bv 64 ?pc) 4) _ _) _) _ =>
k E (mkSS pc sr rs (@None sv) G) RET
end.
Ltac cresume_sv segs rv :=
cat_node ltac:(fun E ss RET =>
lazymatch goal with
| Hregs : regs_ok _ _ ?regs, Hmem : mem_ok _ _ ?mem _, HG : facts_ok _ _ |- _ =>
let H := fresh "HS" in
unshelve epose proof (st_ok_resume_sv segs E ss regs mem rv RET Hregs Hmem HG _) as H;
[ | clear Hregs Hmem HG; sym_norm H ]
end).
Ltac cresume_atom segs n f :=
cat_node ltac:(fun E ss RET =>
lazymatch goal with
| Hregs : regs_ok _ _ ?regs, Hmem : mem_ok _ _ ?mem _, HG : facts_ok _ _ |- _ =>
let H := fresh "HS" in
unshelve epose proof (st_ok_resume_atom segs n f E ss regs mem RET Hregs Hmem HG
ltac:(vm_compute; reflexivity) _ _ _) as H;
[ | | | clear Hregs Hmem HG; sym_norm H ]
end).
