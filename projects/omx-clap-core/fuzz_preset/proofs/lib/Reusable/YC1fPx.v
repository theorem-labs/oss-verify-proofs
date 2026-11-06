(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: for omx-clap-core/fuzz_preset, the journal-bound part of
   proofs/cgif/cgif_file_fuzzer/lib/YC1f.v (origin/ossv/recipes c8557374ad2e :45-48 paj_run / paj_run_to, :431-476
   Ltac paj_run_tok / paj_run_to_tok) over YC80x.v's runner (journal ajournal_x of YCbqG.v, allocator invariant a
   parameter ARx, program statics PST). Every journal-free lemma and tactic is YC1fP.v's, imported, not copied.
   Generic over YC4aP's listing / image classes: no address, no image instance, no ledger.
   SK (YI16.sink_head) is a Context parameter: write `@paj_run_x fx rc SK L PL PI …` (and every runner / tactic use)
   with SK explicit; global sink_head instances exist (YI5b.v, YE2k.v, AE2k.v) and an inferred one is the wrong image's.
   Theorem Labs, 2026-10: the memory-invariant twins (suffix _inv, moved here from YSRrMemnorm.v): paj_run_x_inv /
   paj_run_to_x_inv / paj_run_x_m_inv / paj_run_to_x_m_inv over YC80x's _inv runner lemmas (Section g's binders, then
   P and its laws PLAW, YC80x.srr_inv_laws), and the tactics paj_after_run_tok_inv / paj_run_tok_x_inv /
   paj_run_to_tok_x_inv: paj_after_run_tok (YC1fP) / paj_run_tok_x / paj_run_to_tok_x with one more hypothesis HPM.
   The tactics above take the runner as an argument, but they fix its premise list and the post's intro list, which
   the P premise changes; in every _inv form the P premise comes right after the journal premise (AJ), so a tactic
   passes HPM after HJ and the post introduces HPM after HJ. *)
(* Modified by Theorem Labs, 2026-10: the runners over a world relation R (suffix R): paj_run_xR / paj_run_to_xR /
   paj_run_x_mR / paj_run_to_x_mR and the _invR forms, over YC80x.v's R runner lemmas. A free or realloc of a live
   block can hide shadow again, so a walk that crosses one proves YA0nH.SRrG at a relation wider than wle. Each R
   runner takes R and its two laws (reflexive, transitive) first, so a caller writes
   `pose (RUN := @paj_run_xR fx rc SK L PL PI B PST ARx _ LAWS R R_refl R_trans)` and the result has the plain runner's
   binders W n [stop] E K Bx Bspan SH ss st' r ms, the 16 journal binders and the premises in the plain order, with
   the journal at R (YCbqG.v ajournal_xR) and the conclusion SRrG pa_segs R. The tactics paj_run_tok_xR /
   paj_run_to_tok_xR / paj_run_tok_x_invR / paj_run_to_tok_x_invR are therefore the plain tactics: they apply RUN to
   those binders by position and introduce the post's binders, which are the same. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn
YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbqG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section g.
Context {L : ptable asym} {PL : PAListing L} {PI : PAImg L}.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world pa_segs -> (word -> option byte) -> Model -> Prop.
Context {HL : Z}.  (* AR_laws_x's head length (YCbqG.v), implicit: inferred from LAWS *)
Hypothesis LAWS : AR_laws_x pa_segs B ARx HL.
Hypothesis PST_ok : forall a, Exists (in_zr a) PST -> in_img pa_segs a /\ ~ Exists (in_zr a) (as_owned_static B).
(* cgif YC1f.v:45-48 (origin/ossv/recipes) at YC80x's runner; the _m twins take the mixed write premise. *)
Definition paj_run_x := SRr_run_pi_tok_AJx asym pa_segs B PST ARx LAWS pa_segs_low pa_wx (clookup pa_tbl) pa_val pa_sigma L
pl_tpi pl_tw pa_fetch_ok pa_cert pa_B_ok A_LIM A_LIM_text pl_lim pl_len pl_tpi_eq pl_tw_eq.
Definition paj_run_to_x := SRr_run_to_pi_tok_AJx asym pa_segs B PST ARx LAWS pa_segs_low pa_wx (clookup pa_tbl) pa_val pa_sigma L
pl_tpi pl_tw pa_fetch_ok pa_cert pa_B_ok A_LIM A_LIM_text pl_lim pl_len pl_tpi_eq pl_tw_eq.
Definition paj_run_x_m := SRr_run_pi_tok_AJxm asym pa_segs B PST ARx LAWS pa_segs_low PST_ok pa_wx (clookup pa_tbl) pa_val pa_sigma L
pl_tpi pl_tw pa_fetch_ok pa_cert pa_B_ok A_LIM A_LIM_text pl_lim pl_len pl_tpi_eq pl_tw_eq.
Definition paj_run_to_x_m := SRr_run_to_pi_tok_AJxm asym pa_segs B PST ARx LAWS pa_segs_low PST_ok pa_wx (clookup pa_tbl) pa_val pa_sigma L
pl_tpi pl_tw pa_fetch_ok pa_cert pa_B_ok A_LIM A_LIM_text pl_lim pl_len pl_tpi_eq pl_tw_eq.
(* The runners over a world relation R: R and its two laws first, then the plain runner's binders. *)
Definition paj_run_xR := SRr_run_pi_tok_AJxR asym pa_segs B PST ARx LAWS pa_segs_low pa_wx (clookup pa_tbl) pa_val pa_sigma L
pl_tpi pl_tw pa_fetch_ok pa_cert pa_B_ok A_LIM A_LIM_text pl_lim pl_len pl_tpi_eq pl_tw_eq.
Definition paj_run_to_xR := SRr_run_to_pi_tok_AJxR asym pa_segs B PST ARx LAWS pa_segs_low pa_wx (clookup pa_tbl) pa_val pa_sigma L
pl_tpi pl_tw pa_fetch_ok pa_cert pa_B_ok A_LIM A_LIM_text pl_lim pl_len pl_tpi_eq pl_tw_eq.
Definition paj_run_x_mR := SRr_run_pi_tok_AJxmR asym pa_segs B PST ARx LAWS pa_segs_low PST_ok pa_wx (clookup pa_tbl) pa_val pa_sigma L
pl_tpi pl_tw pa_fetch_ok pa_cert pa_B_ok A_LIM A_LIM_text pl_lim pl_len pl_tpi_eq pl_tw_eq.
Definition paj_run_to_x_mR := SRr_run_to_pi_tok_AJxmR asym pa_segs B PST ARx LAWS pa_segs_low PST_ok pa_wx (clookup pa_tbl) pa_val pa_sigma L
pl_tpi pl_tw pa_fetch_ok pa_cert pa_B_ok A_LIM A_LIM_text pl_lim pl_len pl_tpi_eq pl_tw_eq.
(* The memory-invariant twins: P and its laws, then the four runners above over YC80x's _inv runner lemmas. *)
Variable P : (word -> option byte) -> Prop.
Hypothesis PLAW : srr_inv_laws pa_segs P.
Definition paj_run_x_inv := SRr_run_pi_tok_AJx_inv asym pa_segs B PST ARx LAWS pa_segs_low pa_wx (clookup pa_tbl) pa_val pa_sigma L
pl_tpi pl_tw pa_fetch_ok pa_cert pa_B_ok A_LIM A_LIM_text pl_lim pl_len pl_tpi_eq pl_tw_eq P PLAW.
Definition paj_run_to_x_inv := SRr_run_to_pi_tok_AJx_inv asym pa_segs B PST ARx LAWS pa_segs_low pa_wx (clookup pa_tbl) pa_val pa_sigma L
pl_tpi pl_tw pa_fetch_ok pa_cert pa_B_ok A_LIM A_LIM_text pl_lim pl_len pl_tpi_eq pl_tw_eq P PLAW.
Definition paj_run_x_m_inv := SRr_run_pi_tok_AJxm_inv asym pa_segs B PST ARx LAWS pa_segs_low PST_ok pa_wx (clookup pa_tbl) pa_val pa_sigma L
pl_tpi pl_tw pa_fetch_ok pa_cert pa_B_ok A_LIM A_LIM_text pl_lim pl_len pl_tpi_eq pl_tw_eq P PLAW.
Definition paj_run_to_x_m_inv := SRr_run_to_pi_tok_AJxm_inv asym pa_segs B PST ARx LAWS pa_segs_low PST_ok pa_wx (clookup pa_tbl) pa_val pa_sigma L
pl_tpi pl_tw pa_fetch_ok pa_cert pa_B_ok A_LIM A_LIM_text pl_lim pl_len pl_tpi_eq pl_tw_eq P PLAW.
(* The memory-invariant runners over a world relation R: P and its laws, then R and its two laws. *)
Definition paj_run_x_invR := SRr_run_pi_tok_AJx_invR asym pa_segs B PST ARx LAWS pa_segs_low pa_wx (clookup pa_tbl) pa_val pa_sigma L
pl_tpi pl_tw pa_fetch_ok pa_cert pa_B_ok A_LIM A_LIM_text pl_lim pl_len pl_tpi_eq pl_tw_eq P PLAW.
Definition paj_run_to_x_invR := SRr_run_to_pi_tok_AJx_invR asym pa_segs B PST ARx LAWS pa_segs_low pa_wx (clookup pa_tbl) pa_val pa_sigma L
pl_tpi pl_tw pa_fetch_ok pa_cert pa_B_ok A_LIM A_LIM_text pl_lim pl_len pl_tpi_eq pl_tw_eq P PLAW.
Definition paj_run_x_m_invR := SRr_run_pi_tok_AJxm_invR asym pa_segs B PST ARx LAWS pa_segs_low PST_ok pa_wx (clookup pa_tbl) pa_val pa_sigma L
pl_tpi pl_tw pa_fetch_ok pa_cert pa_B_ok A_LIM A_LIM_text pl_lim pl_len pl_tpi_eq pl_tw_eq P PLAW.
Definition paj_run_to_x_m_invR := SRr_run_to_pi_tok_AJxm_invR asym pa_segs B PST ARx LAWS pa_segs_low PST_ok pa_wx (clookup pa_tbl) pa_val pa_sigma L
pl_tpi pl_tw pa_fetch_ok pa_cert pa_B_ok A_LIM A_LIM_text pl_lim pl_len pl_tpi_eq pl_tw_eq P PLAW.
End g.
End d.
(* cgif YC1f.v:431-476 (origin/ossv/recipes). RUN / RUNTO is paj_run_x / paj_run_to_x (write premise awr_ok) or
   paj_run_x_m / paj_run_to_x_m (write premise awr_byte \/ PST); both have the binders W n [stop] E K Bx Bspan SH ss st' r ms,
   then the 16 journal binders STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q, then the premises in one order, so one
   tactic serves both. Goals left: the obligations (srr_obls tried), the write premise, the post (paj_after_run_tok). *)
Ltac paj_run_tok_x RUN HS HJ SHOK Bspan :=
lazymatch type of HS with
| st_ok_pi ?segs ?val ?E ?ss (restrict (w_H ?W) ?ms) =>
lazymatch type of SHOK with
| sh_ok _ ?Bx ?SH _ _ =>
lazymatch paj_tables RUN with (?tpi, ?tw) =>
let K := eval vm_compute in (run_K A_LIM Bx SH ss) in
let r := eval vm_compute in (sym_runN_pi_tok tpi tw K Bx Bspan SH FUEL ss) in
lazymatch r with
| (?st', ?rs) =>
let Hrun := fresh "Hrun" in
assert (Hrun : sym_runN_pi_tok tpi tw K Bx Bspan SH FUEL ss = (st', rs)) by (vm_compute; reflexivity);
let HEI := lazymatch goal with HEI : img_env _ _ E |- _ => HEI | _ => fail "paj_run_tok_x: no hypothesis  img_env _ _ E" end in
eapply (RUN W FUEL E K Bx Bspan SH ss st' rs ms _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ltac:(unfold A_LIM; cbn; lia) HEI HS SHOK
ltac:(vm_compute; reflexivity) Hrun HJ);
[ clear Hrun; cbn [sh_obls]; srr_obls
| clear Hrun
| clear Hrun HS HJ SHOK; try match type of ms with machine_state => clear ms | _ => idtac end;
paj_after_run_tok HS HJ SHOK ]
end end
end
| _ => fail "paj_run_tok_x: HS must be  st_ok_pi segs val E ss (restrict (w_H W) ms)"
end.
Ltac paj_run_to_tok_x RUNTO HS HJ SHOK Bspan stop :=
lazymatch type of HS with
| st_ok_pi ?segs ?val ?E ?ss (restrict (w_H ?W) ?ms) =>
lazymatch type of SHOK with
| sh_ok _ ?Bx ?SH _ _ =>
lazymatch paj_tables RUNTO with (?tpi, ?tw) =>
let K := eval vm_compute in (run_K A_LIM Bx SH ss) in
let r := eval vm_compute in (sym_run_toN_pi_tok tpi tw K Bx Bspan SH FUEL stop ss) in
lazymatch r with
| (?st', ?rs) =>
let Hrun := fresh "Hrun" in
assert (Hrun : sym_run_toN_pi_tok tpi tw K Bx Bspan SH FUEL stop ss = (st', rs)) by (vm_compute; reflexivity);
let HEI := lazymatch goal with HEI : img_env _ _ E |- _ => HEI | _ => fail "paj_run_to_tok_x: no hypothesis  img_env _ _ E" end in
eapply (RUNTO W FUEL stop E K Bx Bspan SH ss st' rs ms _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ltac:(unfold A_LIM; cbn; lia) HEI HS SHOK
ltac:(vm_compute; reflexivity) Hrun HJ);
[ clear Hrun; cbn [sh_obls]; srr_obls
| clear Hrun
| clear Hrun HS HJ SHOK; try match type of ms with machine_state => clear ms | _ => idtac end;
paj_after_run_tok HS HJ SHOK ]
end end
end
| _ => fail "paj_run_to_tok_x: HS must be  st_ok_pi segs val E ss (restrict (w_H W) ms)"
end.
(* RUN / RUNTO an R runner applied to R and its two laws (paj_run_xR .. R R_refl R_trans, or the _mR forms): the
   binders and the post are the plain runner's, so the tactic is the plain one. *)
Ltac paj_run_tok_xR RUN HS HJ SHOK Bspan := paj_run_tok_x RUN HS HJ SHOK Bspan.
Ltac paj_run_to_tok_xR RUNTO HS HJ SHOK Bspan stop := paj_run_to_tok_x RUNTO HS HJ SHOK Bspan stop.
(* YC1fP.v:450 paj_after_run_tok, introducing the post's P premise (after HJ) as HPM. *)
Ltac paj_after_run_tok_inv HS HJ SHOK HPM :=
let ws := fresh "ws" in let ms' := fresh "ms" in let mat' := fresh "mat" in
let Hlen := fresh "Hlen" in let HF := fresh "HF" in let HFr := fresh "HFr" in let HG := fresh "HG" in let HEI := fresh "HEI" in
intros ws ms' mat' Hlen HEI HS SHOK HJ HPM HF HFr HG;
cbn [sh_j sh_ss] in Hlen, HS, SHOK;
repeat (let w := fresh "w" in
destruct ws as [|w ws]; [discriminate Hlen | cbn [length] in Hlen; apply eq_add_S in Hlen || injection Hlen as Hlen]);
(destruct ws; [clear Hlen | discriminate Hlen]);
cbn [extK length Nat.add] in HS, SHOK, HEI;
cbn [ms_mem mkst] in HF, HFr, HG, HJ, HPM;
try match type of HS with context [restrict _ ?msn] =>
repeat match goal with
| old : machine_state |- _ => lazymatch old with msn => fail | _ => clear old end
end
end;
srr_norm_model.
(* paj_run_tok_x / paj_run_to_tok_x above with HPM. RUN / RUNTO is paj_run_x_inv / paj_run_to_x_inv or the _m_inv forms
   applied to P and its laws; HPM : P (ms_mem ms) is the start memory's P hypothesis, passed after HJ and re-introduced
   under the same name for the end memory. Goals left as above: the obligations (srr_obls tried), the write premise,
   the post (paj_after_run_tok_inv). *)
Ltac paj_run_tok_x_inv RUN HS HJ SHOK HPM Bspan :=
lazymatch type of HS with
| st_ok_pi ?segs ?val ?E ?ss (restrict (w_H ?W) ?ms) =>
lazymatch type of SHOK with
| sh_ok _ ?Bx ?SH _ _ =>
lazymatch paj_tables RUN with (?tpi, ?tw) =>
let K := eval vm_compute in (run_K A_LIM Bx SH ss) in
let r := eval vm_compute in (sym_runN_pi_tok tpi tw K Bx Bspan SH FUEL ss) in
lazymatch r with
| (?st', ?rs) =>
let Hrun := fresh "Hrun" in
assert (Hrun : sym_runN_pi_tok tpi tw K Bx Bspan SH FUEL ss = (st', rs)) by (vm_compute; reflexivity);
let HEI := lazymatch goal with HEI : img_env _ _ E |- _ => HEI | _ => fail "paj_run_tok_x_inv: no hypothesis  img_env _ _ E" end in
eapply (RUN W FUEL E K Bx Bspan SH ss st' rs ms _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ltac:(unfold A_LIM; cbn; lia) HEI HS SHOK
ltac:(vm_compute; reflexivity) Hrun HJ HPM);
[ clear Hrun; cbn [sh_obls]; srr_obls
| clear Hrun
| clear Hrun HS HJ SHOK HPM; try match type of ms with machine_state => clear ms | _ => idtac end;
paj_after_run_tok_inv HS HJ SHOK HPM ]
end end
end
| _ => fail "paj_run_tok_x_inv: HS must be  st_ok_pi segs val E ss (restrict (w_H W) ms)"
end.
Ltac paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM Bspan stop :=
lazymatch type of HS with
| st_ok_pi ?segs ?val ?E ?ss (restrict (w_H ?W) ?ms) =>
lazymatch type of SHOK with
| sh_ok _ ?Bx ?SH _ _ =>
lazymatch paj_tables RUNTO with (?tpi, ?tw) =>
let K := eval vm_compute in (run_K A_LIM Bx SH ss) in
let r := eval vm_compute in (sym_run_toN_pi_tok tpi tw K Bx Bspan SH FUEL stop ss) in
lazymatch r with
| (?st', ?rs) =>
let Hrun := fresh "Hrun" in
assert (Hrun : sym_run_toN_pi_tok tpi tw K Bx Bspan SH FUEL stop ss = (st', rs)) by (vm_compute; reflexivity);
let HEI := lazymatch goal with HEI : img_env _ _ E |- _ => HEI | _ => fail "paj_run_to_tok_x_inv: no hypothesis  img_env _ _ E" end in
eapply (RUNTO W FUEL stop E K Bx Bspan SH ss st' rs ms _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ltac:(unfold A_LIM; cbn; lia) HEI HS SHOK
ltac:(vm_compute; reflexivity) Hrun HJ HPM);
[ clear Hrun; cbn [sh_obls]; srr_obls
| clear Hrun
| clear Hrun HS HJ SHOK HPM; try match type of ms with machine_state => clear ms | _ => idtac end;
paj_after_run_tok_inv HS HJ SHOK HPM ]
end end
end
| _ => fail "paj_run_to_tok_x_inv: HS must be  st_ok_pi segs val E ss (restrict (w_H W) ms)"
end.
(* RUN / RUNTO an _invR runner applied to P, its laws, R and R's two laws: the plain _inv tactic. *)
Ltac paj_run_tok_x_invR RUN HS HJ SHOK HPM Bspan := paj_run_tok_x_inv RUN HS HJ SHOK HPM Bspan.
Ltac paj_run_to_tok_x_invR RUNTO HS HJ SHOK HPM Bspan stop := paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM Bspan stop.
