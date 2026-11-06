(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YL0k.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/Reusable/YL0k.v, with its module paths and module names changed; 30 of its 89 lines of code are new or changed and 195 lines of the source are left out. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK0n YK0p YP0n YM06 YM02.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP0f YP04 YN3v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YO0i YO0f YO0x YO0d YO05.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YH00 YH01 YH03 YH02 YN3e YN35 YN3f YN3g YN34 YN3d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN03 YL07 YL01 YL08 YL0d YL0k YL0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YP03_cfw YN3d_cfw.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require Import SlotAgree.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac cdrv_run_with tblok HS HF :=
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
let ms' := fresh "ms" in
lazymatch st with
| RS_ecall =>
eapply (crz_run_ecall B tbl tblok FUEL E ss ss' ms);
[ | | exact HS | exact Hrun | clear Hrun HS; intros ms' HS HF ]; [assumption|assumption|];
cbn [ms_mem mkst pend_at] in HF
| RS_stopped ?why =>
eapply (crz_run_stop B tbl tblok FUEL E ss ss' why ms);
[ | | exact HS | exact Hrun | clear Hrun HS; intros ms' HS HF ]; [assumption|assumption|];
cbn [ms_mem mkst pend_at] in HF
| RS_running =>
eapply (crz_run_running B tbl tblok FUEL E ss ss' ms);
[ | | exact HS | exact Hrun | clear Hrun HS; intros ms' HS HF ]; [assumption|assumption|];
cbn [ms_mem mkst pend_at] in HF
end
end
end
end
end.
Ltac cdrv_run_to_with tblok HS stop HF :=
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
let ms' := fresh "ms" in
lazymatch st with
| RS_ecall =>
eapply (crz_run_to_ecall B tbl tblok FUEL stop E ss ss' ms);
[ | | exact HS | exact Hrun | clear Hrun HS; intros ms' HS HF ]; [assumption|assumption|];
cbn [ms_mem mkst pend_at] in HF
| RS_stopped ?why =>
eapply (crz_run_to_stop B tbl tblok FUEL stop E ss ss' why ms);
[ | | exact HS | exact Hrun | clear Hrun HS; intros ms' HS HF ]; [assumption|assumption|];
cbn [ms_mem mkst pend_at] in HF
| RS_running =>
eapply (crz_run_to_running B tbl tblok FUEL stop E ss ss' ms);
[ | | exact HS | exact Hrun | clear Hrun HS; intros ms' HS HF ]; [assumption|assumption|];
cbn [ms_mem mkst pend_at] in HF
end
end
end
end
end.
Ltac cdrv_printf0 HS Hch k ret HF :=
lazymatch type of HS with st_ok _ ?E ?ss ?ms =>
lazymatch type of Hch with fdchan (Z_to_bv 64 1) ?ch ?model =>
let r := eval vm_compute in (pf0_check k ss ret) in
lazymatch r with
| Some (?s5, ?zs) =>
let Hck := fresh "Hck" in
assert (Hck : pf0_check k ss ret = Some (s5, zs)) by (vm_compute; reflexivity);
apply (crealizes_printf0_by_run E ss ms model ch k ret s5 zs _ HS ltac:(assumption) ltac:(assumption) Hck Hch);
clear Hck HS;
let ms' := fresh "ms" in let ws := fresh "ws" in
intros ms' ws HS HF; cbn [ms_mem mkst pend_at] in HF;
apply (frame_of_havoc k E ws (ss_mem ss)) in HF; [| vm_compute; reflexivity]
| None => fail "cdrv_printf0: pf0_check failed on this state"
end
end end.
