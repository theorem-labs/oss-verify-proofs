(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s YP0c.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YQ0g.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YA0n YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF00 YF03.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations.
Local Open Scope Z_scope.
Ltac img_app ik t := let T := type of t in lazymatch T with forall _ : img, _ => constr:(t ik) | _ => t end.
Ltac img_vmr := img_case; vm_compute; reflexivity.
Ltac img_run_eq ik := clear - ik; destruct ik; vm_compute; reflexivity.
Ltac sym_why segs tbl ss :=
lazymatch goal with
| ik := _ : img |- _ => YQ04.sym_why segs tbl ss
| ik : img |- _ =>
let tbl := img_app ik tbl in
let g := img_abs ik constr:(sym_step segs tbl ss) in
let r1 := eval vm_compute in (g K_tra) in let r2 := eval vm_compute in (g K_trb) in
lazymatch r1 with
| SStop (SR_branch ?c ?a1 ?b1) =>
lazymatch r2 with
| SStop (SR_branch _ ?a2 ?b2) =>
let a := img_cbv (msv ik a1 a2) in let b := img_cbv (msv ik b1 b2) in constr:(SR_branch c a b)
end
| SStop ?why => why
| SEcall _ => constr:(SR_unsupported)
| SRun _ => constr:(SR_unsupported)
end
| _ => YQ04.sym_why segs tbl ss
end.
Ltac sym_why_sh segs tbl ss :=
lazymatch goal with
| ik := _ : img |- _ => YQ0f.sym_why_sh segs tbl ss
| ik : img |- _ =>
let tbl := img_app ik tbl in
let g := img_abs ik constr:(sym_step_sh segs tbl ss) in
let r1 := eval vm_compute in (g K_tra) in let r2 := eval vm_compute in (g K_trb) in
lazymatch r1 with
| SStop (SR_branch ?c ?a1 ?b1) =>
lazymatch r2 with
| SStop (SR_branch _ ?a2 ?b2) =>
let a := img_cbv (msv ik a1 a2) in let b := img_cbv (msv ik b1 b2) in constr:(SR_branch c a b)
end
| SStop ?why => why
| _ => fail "sym_why_sh: state is not stuck"
end
| _ => YQ0f.sym_why_sh segs tbl ss
end.
Ltac srr_run_with tblok HS :=
lazymatch goal with
| ik := _ : img |- _ => YA0m.srr_run_with tblok HS
| ik : img |- _ =>
let tblok := img_app ik tblok in
lazymatch type of HS with
| st_ok ?segs ?E ?ss (restrict (w_H ?W) ?ms) =>
lazymatch type of tblok with
| table_ok _ ?tbl =>
let g := img_abs ik constr:(sym_runN segs tbl FUEL ss) in
let r1 := eval vm_compute in (g K_tra) in let r2 := eval vm_compute in (g K_trb) in
lazymatch r1 with
| (?s1, ?st) =>
lazymatch r2 with
| (?s2, ?st2) =>
let stm := lazymatch st with st2 => st | _ => img_merge ik st st2 end in
let ss' := img_cbv (msstate ik s1 s2) in
let Hrun := fresh "Hrun" in
assert (Hrun : sym_runN segs tbl FUEL ss = (ss', stm)) by (img_run_eq ik);
let HWX := lazymatch goal with HWX : wx_segs_nowrap segs |- _ => HWX
| _ => fail "srr_run_with: no hypothesis  wx_segs_nowrap segs" end in
eapply (SRr_run_gen segs tbl tblok HWX W FUEL E ss ss' stm ms _ _ HS Hrun);
clear Hrun HS;
srr_after_run HS
end
end
end
| _ => fail "srr_run_with: HS must be  st_ok segs E ss (restrict (w_H W) ms)"
end
| _ => YA0m.srr_run_with tblok HS
end.
Ltac srr_run_to_with tblok HS stop :=
lazymatch goal with
| ik := _ : img |- _ => YA0m.srr_run_to_with tblok HS stop
| ik : img |- _ =>
let tblok := img_app ik tblok in
let stop := img_app ik stop in
lazymatch type of HS with
| st_ok ?segs ?E ?ss (restrict (w_H ?W) ?ms) =>
lazymatch type of tblok with
| table_ok _ ?tbl =>
let g := img_abs ik constr:(sym_run_toN segs tbl FUEL stop ss) in
let r1 := eval vm_compute in (g K_tra) in let r2 := eval vm_compute in (g K_trb) in
lazymatch r1 with
| (?s1, ?st) =>
lazymatch r2 with
| (?s2, ?st2) =>
let stm := lazymatch st with st2 => st | _ => img_merge ik st st2 end in
let ss' := img_cbv (msstate ik s1 s2) in
let Hrun := fresh "Hrun" in
assert (Hrun : sym_run_toN segs tbl FUEL stop ss = (ss', stm)) by (img_run_eq ik);
let HWX := lazymatch goal with HWX : wx_segs_nowrap segs |- _ => HWX
| _ => fail "srr_run_to_with: no hypothesis  wx_segs_nowrap segs" end in
eapply (SRr_run_to_gen segs tbl tblok HWX W FUEL stop E ss ss' stm ms _ _ HS Hrun);
clear Hrun HS;
cbv beta iota; srr_after_run HS
end
end
end
| _ => fail "srr_run_to_with: HS must be  st_ok segs E ss (restrict (w_H W) ms)"
end
| _ => YA0m.srr_run_to_with tblok HS stop
end.
Ltac srr_run_sh tblok HS :=
lazymatch goal with
| ik := _ : img |- _ => YA0n.srr_run_sh tblok HS
| ik : img |- _ =>
let tblok := img_app ik tblok in
lazymatch type of HS with
| st_ok ?segs ?E ?ss (restrict (w_H ?W) ?ms) =>
lazymatch type of tblok with
| table_ok _ ?tbl =>
let g := img_abs ik constr:(sym_runN_sh segs tbl FUEL ss) in
let r1 := eval vm_compute in (g K_tra) in let r2 := eval vm_compute in (g K_trb) in
lazymatch r1 with
| (?s1, ?st) =>
lazymatch r2 with
| (?s2, ?st2) =>
let stm := lazymatch st with st2 => st | _ => img_merge ik st st2 end in
let ss' := img_cbv (msstate ik s1 s2) in
let Hrun := fresh "Hrun" in
assert (Hrun : sym_runN_sh segs tbl FUEL ss = (ss', stm)) by (img_run_eq ik);
let HWX := lazymatch goal with HWX : wx_segs_nowrap segs |- _ => HWX
| _ => fail "srr_run_sh: no hypothesis  wx_segs_nowrap segs" end in
eapply (SRr_run_sh_gen segs tbl tblok HWX W FUEL E ss ss' stm ms _ _ HS Hrun);
clear Hrun HS;
try match type of ms with machine_state => clear ms | _ => idtac end; srr_after_run HS
end
end
end
| _ => fail "srr_run_sh: HS must be  st_ok segs E ss (restrict (w_H W) ms)"
end
| _ => YA0n.srr_run_sh tblok HS
end.
Ltac srr_run_to_sh tblok HS stop :=
lazymatch goal with
| ik := _ : img |- _ => YA0n.srr_run_to_sh tblok HS stop
| ik : img |- _ =>
let tblok := img_app ik tblok in
let stop := img_app ik stop in
lazymatch type of HS with
| st_ok ?segs ?E ?ss (restrict (w_H ?W) ?ms) =>
lazymatch type of tblok with
| table_ok _ ?tbl =>
let g := img_abs ik constr:(sym_run_toN_sh segs tbl FUEL stop ss) in
let r1 := eval vm_compute in (g K_tra) in let r2 := eval vm_compute in (g K_trb) in
lazymatch r1 with
| (?s1, ?st) =>
lazymatch r2 with
| (?s2, ?st2) =>
let stm := lazymatch st with st2 => st | _ => img_merge ik st st2 end in
let ss' := img_cbv (msstate ik s1 s2) in
let Hrun := fresh "Hrun" in
assert (Hrun : sym_run_toN_sh segs tbl FUEL stop ss = (ss', stm)) by (img_run_eq ik);
let HWX := lazymatch goal with HWX : wx_segs_nowrap segs |- _ => HWX
| _ => fail "srr_run_to_sh: no hypothesis  wx_segs_nowrap segs" end in
eapply (SRr_run_to_sh_gen segs tbl tblok HWX W FUEL stop E ss ss' stm ms _ _ HS Hrun);
clear Hrun HS;
try match type of ms with machine_state => clear ms | _ => idtac end; cbv beta iota; srr_after_run HS
end
end
end
| _ => fail "srr_run_to_sh: HS must be  st_ok segs E ss (restrict (w_H W) ms)"
end
| _ => YA0n.srr_run_to_sh tblok HS stop
end.
Ltac srr_branch_with tblok HS :=
lazymatch type of HS with
| st_ok ?segs ?E ?ss (restrict (w_H ?W) ?ms) =>
let tblok := lazymatch goal with ik := _ : img |- _ => tblok | ik : img |- _ => img_app ik tblok | _ => tblok end in
lazymatch type of tblok with
| table_ok _ ?tbl =>
let why := sym_why segs tbl ss in
lazymatch why with
| SR_branch ?c ?a ?b =>
apply (SRr_sym_branch segs W E ss ms _ _ c a b HS);
clear HS;
let Hc := fresh "Hc" in
intros Hc HS
| _ => fail "srr_branch: state is not stuck at a branch:" why
end
end
end.
Ltac srr_branch_sh tblok HS :=
lazymatch type of HS with
| st_ok ?segs ?E ?ss (restrict (w_H ?W) ?ms) =>
let tblok := lazymatch goal with ik := _ : img |- _ => tblok | ik : img |- _ => img_app ik tblok | _ => tblok end in
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
Ltac rreg HS r Hr :=
lazymatch type of HS with
| st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
let e := img_ev (sr_get (ss_regs ss) r) in
let v := eval cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub] in (sv_denot E e) in
let v := simp_off0 v in
let rg := eval cbn [ms_regs restrict mkst] in (ms_regs ms) in
assert (Hr : getr rg r = v)
by (refine (eq_trans (st_ok_restrict_reg segs H E ss ms r HS) _);
first [ change (sv_denot E e = v) | replace (sr_get (ss_regs ss) r) with e by img_eq_by_case ];
cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub];
rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; reflexivity)
end.
Ltac jafter_call HS k regs2 mem2 HP HS2 :=
lazymatch type of HS with
| st_ok ?segs ?E ?ss ?ms =>
let rs := img_ev (ss_mem ss) in
let retpc := img_ev (match sr_get (ss_regs ss) 1 with SLit z => z | _ => 0 end) in
pose proof (st_ok_after_call segs k E ss ms regs2 mem2 rs retpc HS eq_refl
ltac:(img_vmr) ltac:(img_vmr) ltac:(img_vmr)
ltac:(img_vmr) (submem_refl rs) ltac:(img_vmr) HP) as HS2;
let ss2 := img_ev (ss_after_call ss rs k retpc) in
first [ change (ss_after_call ss rs k retpc) with ss2 in HS2 | replace (ss_after_call ss rs k retpc) with ss2 in HS2 by img_eq_by_case ]
end.
Ltac jafter_call2 HS k regs2 mem2 HP stklo idxs HS2 :=
lazymatch type of HS with
| st_ok ?segs ?E ?ss ?ms =>
let m := img_ev (ss_mem ss) in
let rs := lazymatch m with
| ?r0 :: ?rest => let kept := img_ev (pick rest idxs) in constr:(trim_lo r0 stklo :: kept)
end in
let retpc := img_ev (match sr_get (ss_regs ss) 1 with SLit z => z | _ => 0 end) in
pose proof (st_ok_after_call segs k E ss ms regs2 mem2 rs retpc HS eq_refl
ltac:(img_vmr) ltac:(img_vmr) ltac:(img_vmr)
ltac:(img_vmr)
ltac:(apply submem_keep; [apply subregion_trim_lo | submem_tac])
ltac:(img_vmr) HP) as HS2;
let rsv := img_ev rs in
first [ change rs with rsv in HS2 | replace rs with rsv in HS2 by img_eq_by_case ];
let ss2 := img_ev (ss_after_call ss rsv k retpc) in
first [ change (ss_after_call ss rsv k retpc) with ss2 in HS2 | replace (ss_after_call ss rsv k retpc) with ss2 in HS2 by img_eq_by_case ]
end.
