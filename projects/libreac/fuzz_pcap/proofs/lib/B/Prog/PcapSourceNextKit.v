(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the lib/A (ASan build) part of libreac/fuzz_pcap's pcap_source_next kit, from proofs/cgif/cgif_file_fuzzer (origin/ossv/recipes c8557374ad2e) and a Theorem Labs lane's libreac/fuzz_grant lib/A/Prog: it Require-Exports the image-free kit lib/A/Prog/PcapSourceNextKitG.v (ajournal_sub_own, cl_callS_ownG, acall_keptO, the region_kept_*_ajO lemmas, the generic lemmas and the tactics that name no image) and states over lib/A's listing and kit (PcapPa, PcapPaLib, PcapFrame, YC1g, YC1h): cl_callS_own (cgif lib/YC85.v's cl_callS with ajournal_sub_own's side condition, from cl_callS_ownG at pa_segs), region_ok_rechunk, and the tactics of cgif lib/A/ACjr.v, ACj1.v and ACja.v (as a Theorem Labs lane's GrantACjr.v, ACj1.v, GrantACja.v state them) that name lib/A's kit lemmas or records: getTL, rnTL, rnTLF, hei_pose, hei_havoc, rebaseE, creg, flag0, set_regs_rec, ra_join, ra_join_fact, reseat, rregU, img_factsF / img_hull_factsF (fuzz_pcap.asan's objects 0 (atom 241, the GOT word of the side-stack flag), 1 (242, the GOT word of the shadow-base cell), 15 (256, the shadow-base cell) and 16 (257, the side-stack flag cell)), keptFL_at / keptFL_with / keptFL (keeps those four words, the own frame (atom aF, 516 by default) and its shadow (aS, 529), the stacks (2 and aR, 60), blocks and the caller's frames, over acall_keptO or acall_kept), aconstsF, fs_roF(_at), fs_rwF(_at), rechunk, rechunk_off, add_atom; cgif's malloc, LZW-context and FRAME-block cases and fuzz_grant's U_front_isfirst and POW_* are left out; module paths changed. *)
(* Modified by Theorem Labs, 2026-10: the lib/B (asan-ubsan) twin of lib/A/Prog/PcapSourceNextKit.v: it Require-Exports the image-free kit lib/A/Prog/PcapSourceNextKitG.v (never lib/A's PcapSourceNextKit, whose Require closure holds lib/A's image: porter) and states, over lib/B's listing and kit (lib/B/Prog PcapPa, PcapPaLib, PcapFrame, YC1g, YC1h), the parts that name an image: cl_callS_own (cl_callS_ownG at lib/B's pa_segs), region_ok_rechunk over lib/B's list_upd, lib/A/Prog/YC45.v (cgif lib/YC45.v: run_post_pi_AJ_call, SRr_run_pi_AJ_call, zone2_of_app, paj_run_shc, paj_run_to_shc, psrr_branch_pi; lib/B has no YC45), and the tactics that name the kit's lemmas or records (getTL, rnTL, rnTLF, hei_pose, hei_havoc, rebaseE, creg, flag0, set_regs_rec, ra_join, ra_join_fact, reseat, rregU, img_factsF, img_hull_factsF, keptFL_at / keptFL_with / keptFL, aconstsF, fs_roF(_at), fs_rwF(_at), rechunk, rechunk_off, add_atom), text unchanged from lib/A's; lib/B's PcapPaLib.PALib places the four image words at the same objects as lib/A's (0 the GOT word of the side-stack flag, 1 the GOT word of the shadow-base cell, 15 the shadow-base cell, 16 the side-stack flag cell; atoms 241, 242, 256, 257). *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import PcapImgEnd.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0n YI0s YG0s.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YO0d.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YI16 YG0p YC5d YM05.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import PaRun PaShadow.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PaJournal YC4b YC81.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require Import
PcapSyms PcapList PcapPa PcapPaLib YC1g YC1h PcapFrame.
(* The image-free kit (lib/A/Prog/PcapSourceNextKitG.v): its names are this file's names too. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Export PcapSourceNextKitG.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ============================================================================================== *)
(* 1. The call-site wrapper at lib/B's image (cl_callS_ownG at pa_segs).                          *)
(* ============================================================================================== *)

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section j.
Context {L : ptable psym} {PI : PAImg L}.
#[local] Notation SEGS := (@pa_segs _ L PI).
#[local] Notation VAL := (@pa_val _ L PI).
Section l.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Lemma cl_callS_own : forall W (regsc : bvmap 5 word) memc pc STK sp0 FP ly S W0 mem md own lyc Sc mdc k STK1 FP1 EV1 (o : Z) raw ch1
(K : alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k ->
spZ regsc = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 0 <= STK1 -> STK1 - o <= STK ->
getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
getr regsc 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
achain lyc (aview SEGS (w_H W) memc) (sp0 + o) (s0Z regsc) ch1 ->
(afn_pre SEGS B STK1 lyc Sc W regsc memc mdc ch1 ->
SRr SEGS W (mkCfg (mkst regsc pc memc (seg_rom SEGS)) mdc)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
ajournal SEGS B STK1 (spZ regsc) FP1 lyc Sc W memc mdc [] ly2 S2 W2 mem2 md2 EV1 /\
aregs_preserved regsc regs2 /\ K ly2 S2 W2 regs2 mem2 md2)) ->
(forall a, inFP FP1 a -> inFP FP a \/ awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a) ->
SRr SEGS W (mkCfg (mkst regsc pc memc (seg_rom SEGS)) mdc)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
ajournal SEGS B STK sp0 FP ly S W0 mem md own ly2 S2 W2 mem2 md2 (k + EV1) /\
ajournal SEGS B STK1 (sp0 + o) FP1 lyc Sc W memc mdc [] ly2 S2 W2 mem2 md2 EV1 /\
aregs_preserved regsc regs2 /\ K ly2 S2 W2 regs2 mem2 md2).
Proof. exact (cl_callS_ownG SEGS B LAWS pa_segs_low). Qed.
End l.
End j.
End c.

(* ============================================================================================== *)
(* 2. The lemma and the tactics that name lib/B's kit (lib/A's text, unchanged).                  *)
(* ============================================================================================== *)

Ltac getTL := lazymatch goal with T : PALib _ |- _ => T end.
Ltac reseat HS HJ2 HP2 keep AG kept_tac :=
let K := lazymatch type of HS with st_ok_pi _ _ _ ?ss _ => eval vm_compute in (run_K A_LIM (SOff 32 0) [] ss) | st_ok _ _ ?ss _ => eval vm_compute in (run_K A_LIM (SOff 32 0) [] ss)  end in
let HS2 := fresh "HS2" in
lazymatch type of HJ2 with ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ ?W2 ?mem2 _ _ =>
lazymatch type of HP2 with aregs_preserved _ ?regs2 =>
jafter_call_keep_hi HS K regs2 (mrestrict (w_H W2) mem2) HP2 keep HS2 end end;
match type of HS2 with ?Q -> _ =>
let HQ := fresh "HQ" in
assert (HQ : Q); [ cbn [ms_mem restrict]; repeat apply Forall_cons; try apply Forall_nil; kept_tac | specialize (HS2 HQ); clear HQ ] end;
clear HS; rewrite <- restrict_mkst_fx in HS2; rename HS2 into HS;
let AG2 := fresh "AG" in let Ev := fresh "E" in let HEv := fresh "HE" in
lazymatch type of AG with forall n, _ -> _ = ew ?E0 n =>
lazymatch type of HS with st_ok_pi _ _ ?Enew _ _ =>
remember Enew as Ev eqn:HEv in HS;
let HEIv := fresh "HEI" in
lazymatch type of HEv with
| _ = havoc ?Eo ?kk ?ws => lazymatch goal with Ho : img_env ?val ?lim Eo |- _ =>
pose proof (img_env_havoc_hi Eo kk ws Ho ltac:(cbv; lia)) as HEIv; rewrite <- HEv in HEIv end
| _ = ?En => try (lazymatch goal with Hn : img_env _ _ En |- _ => rewrite <- HEv in Hn end) end;
repeat match goal with H : img_env _ _ (ewset _ _ _) |- _ => clear H end;
assert (AG2 : forall n, (n < 33)%nat -> ew Ev n = ew E0 n)
by (intros nn Hnn; rewrite HEv; rewrite ew_havoc_old by lia; rewrite ?ew_ewset_other by lia; apply AG; exact Hnn);
repeat match goal with H : ew ?Eo ?n = ?v |- _ =>
lazymatch Eo with
| Ev => fail
| _ => lazymatch (eval cbv in (Nat.leb 33 n)) with
| true => let H2 := fresh H in
assert (H2 : ew Ev n = v) by (rewrite HEv; rewrite ew_havoc_old by lia; rewrite ?ew_ewset_other by lia; exact H);
clear H; rename H2 into H
end end end;
clear HEv AG; rename AG2 into AG | st_ok _ ?Enew _ _ =>
remember Enew as Ev eqn:HEv in HS;
let HEIv := fresh "HEI" in
lazymatch type of HEv with
| _ = havoc ?Eo ?kk ?ws => lazymatch goal with Ho : img_env ?val ?lim Eo |- _ =>
pose proof (img_env_havoc_hi Eo kk ws Ho ltac:(cbv; lia)) as HEIv; rewrite <- HEv in HEIv end
| _ = ?En => try (lazymatch goal with Hn : img_env _ _ En |- _ => rewrite <- HEv in Hn end) end;
repeat match goal with H : img_env _ _ (ewset _ _ _) |- _ => clear H end;
assert (AG2 : forall n, (n < 33)%nat -> ew Ev n = ew E0 n)
by (intros nn Hnn; rewrite HEv; rewrite ew_havoc_old by lia; rewrite ?ew_ewset_other by lia; apply AG; exact Hnn);
repeat match goal with H : ew ?Eo ?n = ?v |- _ =>
lazymatch Eo with
| Ev => fail
| _ => lazymatch (eval cbv in (Nat.leb 33 n)) with
| true => let H2 := fresh H in
assert (H2 : ew Ev n = v) by (rewrite HEv; rewrite ew_havoc_old by lia; rewrite ?ew_ewset_other by lia; exact H);
clear H; rename H2 into H
end end end;
clear HEv AG; rename AG2 into AG  end end.
Ltac rregU HS r v Utac H :=
lazymatch type of HS with
| st_ok_pi ?segs ?val ?Ex ?ss (restrict ?Hh ?ms) =>
let e := eval vm_compute in (sr_get (ss_regs ss) r) in
let rg := eval cbn [ms_regs restrict mkst] in (ms_regs ms) in
assert (H : getr rg r = Z_to_bv 64 v)
by (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ss ms r HS) _);
change (sv_denot Ex e = Z_to_bv 64 v); rewrite denot_lit_U; f_equal; Utac)
| st_ok ?segs ?Ex ?ss (restrict ?Hh ?ms) =>
let e := eval vm_compute in (sr_get (ss_regs ss) r) in
let rg := eval cbn [ms_regs restrict mkst] in (ms_regs ms) in
assert (H : getr rg r = Z_to_bv 64 v)
by (refine (eq_trans (st_ok_restrict_reg segs Hh Ex ss ms r HS) _);
change (sv_denot Ex e = Z_to_bv 64 v); rewrite denot_lit_U; f_equal; Utac)
end.
Ltac rnTL := lazymatch goal with T : PALib _ |- _ => T end.
Ltac rnTLF := lazymatch goal with T : PALibF _ |- _ => T end.
Ltac hei_pose Eo kk ws :=
let Ho := rnHEI Eo in let H := fresh "HEIh" in
first [ pose proof (img_env_havoc_hi Eo kk ws Ho ltac:(cbv; lia)) as H | pose proof (img_env_havoc Eo kk ws Ho ltac:(cbv; lia)) as H ].
Ltac hei_havoc HS :=
lazymatch type of HS with
| st_ok_pi _ _ (havoc ?Eo ?kk ?ws) _ _ => first [ let H0 := rnHEI constr:(havoc Eo kk ws) in idtac | hei_pose Eo kk ws ]
| _ => idtac end.
Ltac rebaseE HS AG HEv :=
let AG2 := fresh "AG" in let Ev := fresh "E" in
lazymatch type of AG with forall n, _ -> _ = ew ?E0 n =>
lazymatch type of HS with st_ok_pi _ _ ?Enew _ _ =>
remember Enew as Ev eqn:HEv in HS;
let HEIv := fresh "HEI" in
lazymatch type of HEv with
| _ = havoc ?Eo ?kk ?ws => lazymatch goal with Ho : img_env ?val ?lim Eo |- _ =>
first [ pose proof (img_env_havoc_hi Eo kk ws Ho ltac:(cbv; lia)) as HEIv | pose proof (img_env_havoc Eo kk ws Ho ltac:(cbv; lia)) as HEIv ];
rewrite <- HEv in HEIv end
| _ = ?En => try (lazymatch goal with Hn : img_env _ _ En |- _ => rewrite <- HEv in Hn end) end;
repeat match goal with H : img_env _ _ (ewset _ _ _) |- _ => clear H end;
assert (AG2 : forall n, (n < 33)%nat -> ew Ev n = ew E0 n)
by (intros nn Hnn; rewrite HEv; rewrite ?ew_ewset_other, ?ew_havoc_old by lia; rewrite ?ew_ewset_other, ?ew_havoc_old by lia; apply AG; exact Hnn);
repeat match goal with H : ew ?Eo ?n = ?v |- _ =>
lazymatch Eo with
| Ev => fail
| _ => lazymatch (eval cbv in (Nat.leb 33 n)) with
| true => let H2 := fresh H in
assert (H2 : ew Ev n = v) by (rewrite HEv; rewrite ?ew_ewset_other, ?ew_havoc_old, ?ew_havoc_above by nat_side; rewrite ?ew_ewset_other, ?ew_havoc_old, ?ew_havoc_above by nat_side; exact H);
clear H; rename H2 into H
end end end;
clear AG; rename AG2 into AG | st_ok _ ?Enew _ _ =>
remember Enew as Ev eqn:HEv in HS;
let HEIv := fresh "HEI" in
lazymatch type of HEv with
| _ = havoc ?Eo ?kk ?ws => lazymatch goal with Ho : img_env ?val ?lim Eo |- _ =>
first [ pose proof (img_env_havoc_hi Eo kk ws Ho ltac:(cbv; lia)) as HEIv | pose proof (img_env_havoc Eo kk ws Ho ltac:(cbv; lia)) as HEIv ];
rewrite <- HEv in HEIv end
| _ = ?En => try (lazymatch goal with Hn : img_env _ _ En |- _ => rewrite <- HEv in Hn end) end;
repeat match goal with H : img_env _ _ (ewset _ _ _) |- _ => clear H end;
assert (AG2 : forall n, (n < 33)%nat -> ew Ev n = ew E0 n)
by (intros nn Hnn; rewrite HEv; rewrite ?ew_ewset_other, ?ew_havoc_old by lia; rewrite ?ew_ewset_other, ?ew_havoc_old by lia; apply AG; exact Hnn);
repeat match goal with H : ew ?Eo ?n = ?v |- _ =>
lazymatch Eo with
| Ev => fail
| _ => lazymatch (eval cbv in (Nat.leb 33 n)) with
| true => let H2 := fresh H in
assert (H2 : ew Ev n = v) by (rewrite HEv; rewrite ?ew_ewset_other, ?ew_havoc_old, ?ew_havoc_above by nat_side; rewrite ?ew_ewset_other, ?ew_havoc_old, ?ew_havoc_above by nat_side; exact H);
clear H; rename H2 into H
end end end;
clear AG; rename AG2 into AG  end end.
Ltac creg HS AG EE :=
lazymatch goal with |- getr _ ?r = getr _ _ =>
let R := fresh "R" in prreg HS r R; rewrite R; clear R;
cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite AG by lia;
apply EE; reflexivity end.
Ltac flag0 E57 EFL :=
let msr := fresh "msr" in let HSr := fresh "HSr" in let HR := fresh "HR" in let V := fresh "V" in
intros msr HSr; rewrite ?EFL;
lazymatch type of HSr with st_ok_pi _ _ ?Ex ?ssx _ =>
pose proof (st_ok_pi_region_nth Ex ssx msr 0 _ HSr eq_refl) as HR;
lazymatch type of HR with region_ok _ _ _ (YP09.mkRegion (Some ?n) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex (ms_mem msr) n _ cs lo hi wlo whi 0 1%N (SLit 0) 0 HR
ltac:(cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E57; apply unsigned_lit_small; lia)
ltac:(left; reflexivity) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as V end | st_ok _ ?Ex ?ssx _ =>
pose proof (st_ok_region_nth Ex ssx msr 0 _ HSr eq_refl) as HR;
lazymatch type of HR with region_ok _ _ _ (YP09.mkRegion (Some ?n) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex (ms_mem msr) n _ cs lo hi wlo whi 0 1%N (SLit 0) 0 HR
ltac:(cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E57; apply unsigned_lit_small; lia)
ltac:(left; reflexivity) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as V end  end;
rewrite Z.add_0_r in V; pose proof (V 0%nat ltac:(lia)) as V0; cbn [Z.of_nat] in V0; rewrite Z.add_0_r in V0; exact V0.
Ltac set_regs_rec HS N vals i rl :=
lazymatch rl with
| [] => idtac
| ?r :: ?rl' =>
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
let HS3 := fresh "HS3" in let Hv := fresh "Hv" in
let n := eval vm_compute in (N + i)%nat in
assert (Hv : sv_denot Ev (SOff n 0) = getr (ms_regs msx) r);
[ cbn [sv_denot]; rewrite Z.add_0_r; rewrite Z_to_bv_bv_unsigned; change n with (N + i)%nat;
rewrite (ew_havoc_new _ N vals i (Z_to_bv 64 0)) by (cbn [length]; lia); cbn [nth ms_regs restrict]; reflexivity | ];
pose proof (ast_ok_pi_set_reg_fp Ev ssx msx r (SOff n 0) HS ltac:(vm_compute; reflexivity) Hv) as HS3;
clear HS Hv; rename HS3 into HS; norm_ss HS; set_regs_rec HS N vals (S i) rl' | st_ok _ ?Ev ?ssx ?msx =>
let HS3 := fresh "HS3" in let Hv := fresh "Hv" in
let n := eval vm_compute in (N + i)%nat in
assert (Hv : sv_denot Ev (SOff n 0) = getr (ms_regs msx) r);
[ cbn [sv_denot]; rewrite Z.add_0_r; rewrite Z_to_bv_bv_unsigned; change n with (N + i)%nat;
rewrite (ew_havoc_new _ N vals i (Z_to_bv 64 0)) by (cbn [length]; lia); cbn [nth ms_regs restrict]; reflexivity | ];
pose proof (ast_ok_set_reg_fp _ Ev ssx msx r (SOff n 0) HS ltac:(vm_compute; reflexivity) Hv) as HS3;
clear HS Hv; rename HS3 into HS; norm_ss HS; set_regs_rec HS N vals (S i) rl'  end
end.
Ltac ra_join HS target N deads hook :=
norm_ss HS;
let tg := eval red in target in
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let HS3 := fresh "HS3" in
let rs := eval cbn [ss_mem] in (ss_mem tg) in
pose proof (st_ok_pi_submem Ex ssx msx rs HS ltac:(cbn [ss_mem]; submem_to) ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS | st_ok _ ?Ex ?ssx ?msx =>
let HS3 := fresh "HS3" in
let rs := eval cbn [ss_mem] in (ss_mem tg) in
pose proof (st_ok_submem _ Ex ssx msx rs HS ltac:(cbn [ss_mem]; submem_to) ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS  end;
norm_ss HS;
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let HS3 := fresh "HS3" in
let dl := eval cbv in deads in
let vals := constr:(map (fun r : bv 5 => getr (ms_regs msx) r) dl) in
let vals' := eval cbn [map ms_regs restrict] in vals in
pose proof (st_ok_pi_havoc_hi N Ex ssx msx vals' HS ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS;
set_regs_rec HS N vals' 0%nat dl | st_ok _ ?Ex ?ssx ?msx =>
let HS3 := fresh "HS3" in
let dl := eval cbv in deads in
let vals := constr:(map (fun r : bv 5 => getr (ms_regs msx) r) dl) in
let vals' := eval cbn [map ms_regs restrict] in vals in
pose proof (st_ok_havoc _ N Ex ssx msx vals' HS ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS;
set_regs_rec HS N vals' 0%nat dl  end;
norm_ss HS;
hook;
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let HS3 := fresh "HS3" in
let fa := eval cbn [ss_facts f_atoms] in (f_atoms (ss_facts tg)) in
let cs := eval cbn [ss_facts f_conds] in (f_conds (ss_facts tg)) in
let al := eval cbn [ss_facts f_alias] in (f_alias (ss_facts tg)) in
pose proof (st_ok_pi_facts_incl3 Ex ssx msx fa cs al HS ltac:(incl_lit_tac) ltac:(incl_lit_tac) ltac:(incl_lit_tac)) as HS3;
clear HS; rename HS3 into HS | st_ok _ ?Ex ?ssx ?msx =>
let HS3 := fresh "HS3" in
let fa := eval cbn [ss_facts f_atoms] in (f_atoms (ss_facts tg)) in
let cs := eval cbn [ss_facts f_conds] in (f_conds (ss_facts tg)) in
let al := eval cbn [ss_facts f_alias] in (f_alias (ss_facts tg)) in
pose proof (st_ok_facts_incl3 _ Ex ssx msx fa cs al HS ltac:(incl_lit_tac) ltac:(incl_lit_tac) ltac:(incl_lit_tac)) as HS3;
clear HS; rename HS3 into HS  end;
norm_ss HS;
lazymatch type of HS with st_ok_pi _ _ _ ?ssx _ => first [change ssx with target in HS | idtac "JOIN-MISMATCH" ssx tg] | st_ok _ _ ?ssx _ => first [change ssx with target in HS | idtac "JOIN-MISMATCH" ssx tg]  end.
Ltac ra_join_fact HS n af tac :=
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
let HS3 := fresh "HS3" in
pose proof (st_ok_pi_add_fact Ev ssx msx n af HS ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; tac)) as HS3;
clear HS; rename HS3 into HS | st_ok _ ?Ev ?ssx ?msx =>
let HS3 := fresh "HS3" in
pose proof (st_ok_pi_add_fact Ev ssx msx n af HS ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; tac)) as HS3;
clear HS; rename HS3 into HS  end.
Ltac img_factsF E :=
let H := rnHEI E in
repeat match goal with G : ew E 240%nat = _ |- _ => clear G | G : ew E 241%nat = _ |- _ => clear G | G : ew E 242%nat = _ |- _ => clear G
| G : ew E 256%nat = _ |- _ => clear G | G : ew E 257%nat = _ |- _ => clear G end;
let E240 := fresh "E240" in let E241 := fresh "E241" in let E242 := fresh "E242" in let E256 := fresh "E256" in let E257 := fresh "E257" in
pose proof (img_env_atomP E 240%nat H ltac:(unfold A_TEXT, A_LIM; lia)) as E240;
pose proof (img_env_atomP E 241%nat H ltac:(unfold A_TEXT, A_LIM; lia)) as E241;
pose proof (img_env_atomP E 242%nat H ltac:(unfold A_TEXT, A_LIM; lia)) as E242;
pose proof (img_env_atomP E 256%nat H ltac:(unfold A_TEXT, A_LIM; lia)) as E256;
pose proof (img_env_atomP E 257%nat H ltac:(unfold A_TEXT, A_LIM; lia)) as E257.
Ltac img_hull_factsF :=
let TL := rnTL in let TLF := rnTLF in
pose proof (pa_obj_img 1 ltac:(lia)) as Hob242; pose proof (pa_obj_img 0 ltac:(lia)) as Hob241;
pose proof (pa_obj_img 15 ltac:(lia)) as Hob256; pose proof (pa_obj_img 16 ltac:(lia)) as Hob257;
cbv [A_OBJ Nat.add] in Hob241, Hob242, Hob256, Hob257;
pose proof (palf_uar_img _ TL) as Huar; pose proof (palf_uar_al _ TLF) as Huar4.

Ltac keptFL_at aF aS aR hd HK HJx AG Kg Kg2 Kc Kc2 Kgu Kgu2 Ku Ku2 ErT PrT :=
first [ hd |
lazymatch goal with
| |- region_kept _ _ _ _ (YP09.mkRegion (Some 2%nat) _ _ _ _ _) =>
eapply (region_kept_stack_ajO _ _); [kexact HK | exact HJx | evalE AG | unfold ESTACK, ASTACK; zconst_lits; lia | unfold ESTACK, ASTACK; zconst_lits; lia | lia | lia | lia]
| |- region_kept _ _ _ _ (YP09.mkRegion (Some aR) _ _ _ _ _) =>
eapply (region_kept_stack_ajO _ _); [kexact HK | exact HJx | evalE AG | unfold ESTACK, ASTACK; zconst_lits; lia | unfold ESTACK, ASTACK; zconst_lits; lia | lia | lia | lia]
| |- region_kept _ ?Ex _ _ (YP09.mkRegion (Some 242%nat) _ _ _ _ _) =>
let H := rnHEI Ex in apply (region_kept_val_at Ex _ _ (A_OBJ 1) (pa_val (A_OBJ 1)) 8 (pa_val (A_OBJ 15)));
[exact (H (A_OBJ 1) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact Kg | exact Kg2 | lia]
| |- region_kept _ ?Ex _ _ (YP09.mkRegion (Some 256%nat) _ _ _ _ _) =>
let H := rnHEI Ex in apply (region_kept_val_at Ex _ _ (A_OBJ 15) (pa_val (A_OBJ 15)) 8 SHADOW_OFF);
[exact (H (A_OBJ 15) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact Kc | exact Kc2 | lia]
| |- region_kept _ ?Ex _ _ (YP09.mkRegion (Some 241%nat) _ _ _ _ _) =>
let H := rnHEI Ex in let Bv := rnB in apply (region_kept_val_at Ex _ _ (A_OBJ 0) (pa_val (A_OBJ 0)) 8 (as_uar_cell Bv));
[exact (H (A_OBJ 0) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact Kgu | exact Kgu2 | lia]
| |- region_kept _ ?Ex _ _ (YP09.mkRegion (Some 257%nat) _ _ _ _ _) =>
let H := rnHEI Ex in let Bv := rnB in let TL := rnTL in apply (region_kept_val_at Ex _ _ (A_OBJ 16) (as_uar_cell Bv) 4 1);
[rewrite (pal_uar_cell _ TL); exact (H (A_OBJ 16) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact Ku | exact Ku2 | lia]
| |- region_kept _ _ _ _ (YP09.mkRegion (Some aF) _ _ _ _ _) =>
eapply (region_kept_ownframe_ajO _ _); [kexact HK | evalE AG | eassumption
| left; rewrite_frame_addr; fsb_lits; lia | intros a Ha; cbn beta; first [exact (fun Hn : False => Hn) | ErT] | intros a Ha; PrT ]
| |- region_kept _ _ _ _ (YP09.mkRegion (Some aS) _ _ _ _ _) =>
eapply (region_kept_ownframe_ajO _ _); [kexact HK | evalE AG | eassumption
| right; rewrite_frame_addr; unfold shadow_addr; rewrite <- SB_SHADOW_OFF; fsb_lits; unfold SB; lia
| intros a Ha; cbn beta; first [exact (fun Hn : False => Hn) | ErT] | intros a Ha; first [lia | PrT] ]
| |- region_kept _ _ _ _ (YP09.mkRegion (Some ?n) _ _ ?wlo ?whi _) =>
lazymatch goal with Hb : ew _ n = Z_to_bv 64 ?b |- _ =>
let L := rnLAWS in
first
[
lazymatch (eval vm_compute in (Z.leb whi wlo)) with true =>
first [ eapply (region_kept_block_ajO _ _ _ _ _ _ _ _ _ _ _ _ n _ _ _ _ _ b); [kexact HK | evalE AG | eassumption | lia | rqs_goal; lia | lia | intros a Ha Hn; first [exact Hn | ErT] ]
| eapply (region_kept_frame_ajO _ _ _ _ _ _ _ _ _ _ _ _ n _ _ _ _ _ b); [kexact HK | evalE AG | eassumption | rewrite_frame_addr; lia | rewrite_frame_addr; lia | lia | intros a Ha Hn; first [exact Hn | ErT] ] ] end
|
eapply (region_kept_block_ajw2O _ _ L _ _ _ _ _ _ _ _ _ _ n _ _ _ _ _ b); [kexact HK | exact (proj1 HJx) | eassumption | evalE AG | eassumption | lia | rqs_goal; lia | lia | lia | intros a Ha Hn; first [exact Hn | ErT] ]
| match goal with |- ?g => idtac "KEPTFL-FAIL" g end; fail ] end
end ].
Ltac keptFL_with hd HK HJx AG Kg Kg2 Kc Kc2 Kgu Kgu2 Ku Ku2 ErT PrT :=
keptFL_at 516%nat 529%nat 60%nat hd HK HJx AG Kg Kg2 Kc Kc2 Kgu Kgu2 Ku Ku2 ErT PrT.
Ltac keptFL HK HJx AG Kg Kg2 Kc Kc2 Kgu Kgu2 Ku Ku2 ErT PrT := keptFL_with ltac:(idtac; fail) HK HJx AG Kg Kg2 Kc Kc2 Kgu Kgu2 Ku Ku2 ErT PrT.
Ltac aconstsF HJx Kgot Kcell Kguar Kuar :=
let L := rnLAWS in let TL := rnTL in
let Kc := fresh "Kc" in let Ku := fresh "Ku" in let Kg := fresh "Kg" in let Kgu := fresh "Kgu" in
destruct (al_const _ _ L _ _ _ _ _ (proj1 HJx)) as (Kc & Ku & Kg & Kgu);
rewrite (pal_got_shadow _ TL), (pal_cell _ TL) in Kg; rewrite (pal_cell _ TL) in Kc;
rewrite (palf_got_uar _ TL) in Kgu;
pose proof (val_mem_of_rdword _ _ _ _ _ Kg) as Kgot; pose proof (val_mem_of_rdword _ _ _ _ _ Kc) as Kcell;
pose proof (val_mem_of_rdword _ _ _ _ _ Kgu) as Kguar; pose proof (val_mem_of_rd32 _ _ _ _ _ Ku) as Kuar;
clear Kc Ku Kg Kgu.
Ltac fs_roF_at aS HS :=
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs aS in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rs got_regionP) in
let HS3 := fresh "HS3" in
pose proof (ast_ok_pi_set_region Ex ssx msx i r (set_window r 0 0) HS ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity)
(region_ok_rewindow _ Ex _ r 0 0 (st_ok_pi_region_nth Ex ssx msx i r HS ltac:(vm_compute; reflexivity)) ltac:(intros o Ho; lia))) as HS3;
clear HS; rename HS3 into HS; norm_ss HS | st_ok _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs aS in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rs got_regionP) in
let HS3 := fresh "HS3" in
pose proof (ast_ok_set_region _ Ex ssx msx i r (set_window r 0 0) HS ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity)
(region_ok_rewindow _ Ex _ r 0 0 (st_ok_region_nth Ex ssx msx i r HS ltac:(vm_compute; reflexivity)) ltac:(intros o Ho; lia))) as HS3;
clear HS; rename HS3 into HS; norm_ss HS  end.
Ltac fs_rwF_at aS HS E529 Hp :=
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs aS in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rs got_regionP) in
let hi := eval vm_compute in (YP09.r_hi r) in
let HS3 := fresh "HS3" in
pose proof (ast_ok_pi_set_region Ex ssx msx i r (set_window r 0 hi) HS ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity)
(region_ok_rewindow _ Ex _ r 0 hi (st_ok_pi_region_nth Ex ssx msx i r HS ltac:(vm_compute; reflexivity))
ltac:(cbn [YP09.r_base base_val ms_mem restrict mkst]; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia;
rewrite E529, unsigned_lit_small by (unfold SB; lia);
intros o Ho; apply (apresent_writable _); unfold shadow_addr in Hp; rewrite <- SB_SHADOW_OFF in Hp;
apply (proj1 (Hp o ltac:(clear - Ho; lia)))))) as HS3;
clear HS; rename HS3 into HS; norm_ss HS | st_ok _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs aS in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rs got_regionP) in
let hi := eval vm_compute in (YP09.r_hi r) in
let HS3 := fresh "HS3" in
pose proof (ast_ok_set_region _ Ex ssx msx i r (set_window r 0 hi) HS ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity)
(region_ok_rewindow _ Ex _ r 0 hi (st_ok_region_nth Ex ssx msx i r HS ltac:(vm_compute; reflexivity))
ltac:(cbn [YP09.r_base base_val ms_mem restrict mkst]; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia;
rewrite E529, unsigned_lit_small by (unfold SB; lia);
intros o Ho; apply (apresent_writable _); unfold shadow_addr in Hp; rewrite <- SB_SHADOW_OFF in Hp;
apply (proj1 (Hp o ltac:(clear - Ho; lia)))))) as HS3;
clear HS; rename HS3 into HS; norm_ss HS  end.
Ltac fs_roF HS := fs_roF_at 529%nat HS.
Ltac fs_rwF HS E529 Hp := fs_rwF_at 529%nat HS E529 Hp.
Lemma region_ok_rechunk : forall segs E m r j off w e e',
region_ok segs E m r -> nth_error (YP09.r_chunks r) j = Some (YP09.mkChunk off (CVal w e)) -> sv_denot E e' = sv_denot E e ->
region_ok segs E m (YP09.mkRegion (YP09.r_base r) (YP09.r_lo r) (YP09.r_hi r) (YP09.r_wlo r) (YP09.r_whi r)
(list_upd (YP09.r_chunks r) j (YP09.mkChunk off (CVal w e')))).
Proof.
intros segs E m r j off w e e' (H1 & H2 & H3 & H4) Hj He. unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
apply Forall_list_upd; [exact H4|]. apply (chunk_ok_redenote segs E m _ off w e e' He).
exact (proj1 (Forall_forall _ _) H4 _ (nth_error_In _ _ Hj)).
Qed.
Ltac rechunk HS i j e' tac :=
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (ss_mem ssx) in
let r := eval vm_compute in (nth i rs got_regionP) in
lazymatch (eval vm_compute in (nth_error (YP09.r_chunks r) j)) with Some (YP09.mkChunk ?off (CVal ?w ?e)) =>
let r' := eval vm_compute in (YP09.mkRegion (YP09.r_base r) (YP09.r_lo r) (YP09.r_hi r) (YP09.r_wlo r) (YP09.r_whi r)
(list_upd (YP09.r_chunks r) j (YP09.mkChunk off (CVal w e')))) in
let HS3 := fresh "HS3" in
pose proof (ast_ok_pi_set_region Ex ssx msx i r r' HS ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity)
(region_ok_rechunk _ Ex _ r j off w e e' (st_ok_pi_region_nth Ex ssx msx i r HS ltac:(vm_compute; reflexivity)) ltac:(vm_compute; reflexivity) ltac:(tac))) as HS3;
clear HS; rename HS3 into HS; norm_ss HS end | st_ok _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (ss_mem ssx) in
let r := eval vm_compute in (nth i rs got_regionP) in
lazymatch (eval vm_compute in (nth_error (YP09.r_chunks r) j)) with Some (YP09.mkChunk ?off (CVal ?w ?e)) =>
let r' := eval vm_compute in (YP09.mkRegion (YP09.r_base r) (YP09.r_lo r) (YP09.r_hi r) (YP09.r_wlo r) (YP09.r_whi r)
(list_upd (YP09.r_chunks r) j (YP09.mkChunk off (CVal w e')))) in
let HS3 := fresh "HS3" in
pose proof (ast_ok_set_region _ Ex ssx msx i r r' HS ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity)
(region_ok_rechunk _ Ex _ r j off w e e' (st_ok_region_nth Ex ssx msx i r HS ltac:(vm_compute; reflexivity)) ltac:(vm_compute; reflexivity) ltac:(tac))) as HS3;
clear HS; rename HS3 into HS; norm_ss HS end  end.
Ltac rechunk_off HS n off e' tac :=
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs n in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rs got_regionP) in
let cs := eval vm_compute in (YP09.r_chunks r) in
let j := idx_of_off cs off in let j := eval vm_compute in j in
rechunk HS i j e' tac | st_ok _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs n in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rs got_regionP) in
let cs := eval vm_compute in (YP09.r_chunks r) in
let j := idx_of_off cs off in let j := eval vm_compute in j in
rechunk HS i j e' tac  end.
Ltac add_atom HS n w En :=
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
let HS3 := fresh "HS3" in
pose proof (st_ok_pi_havoc_hi n Ev ssv msv [w] HS ltac:(vm_compute; reflexivity)) as HS3; hei_pose Ev n%nat [w];
clear HS; rename HS3 into HS;
assert (En : ew (havoc Ev n [w]) n = w) by (exact (ew_havoc_new _ n [w] 0 (Z_to_bv 64 0) ltac:(cbn; lia))) | st_ok _ ?Ev ?ssv ?msv =>
let HS3 := fresh "HS3" in
pose proof (st_ok_pi_havoc_hi n Ev ssv msv [w] HS ltac:(vm_compute; reflexivity)) as HS3; hei_pose Ev n%nat [w];
clear HS; rename HS3 into HS;
assert (En : ew (havoc Ev n [w]) n = w) by (exact (ew_havoc_new _ n [w] 0 (Z_to_bv 64 0) ltac:(cbn; lia)))  end.

(* ============================================================================================== *)
(* 2b. The plain-engine call run (lib/A/Prog/YC45.v = cgif lib/YC45.v, text unchanged) over lib/B's listing. *)
(* ============================================================================================== *)

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section e.
Context {L : ptable psym} {PL : PAListing L} {PI : PAImg L}.
Variable B : asyms.
Hypothesis LAWS : AR_laws pa_segs B.
#[local] Notation SEGS := (pa_segs).
#[local] Notation VAL := (pa_val).
Definition run_post_pi_AJ_call (W : world SEGS) (E : env) (ss ssc : sstate)
(ms : machine_state) (STK sp0 : Z) (FP : list (Z * Z)) ly S W0 mem md own lyc Sc (mdc : Model) (k : Z)
(Q : world SEGS -> config -> Prop) : Prop :=
forall ms' mat',
st_ok SEGS E ssc (restrict (w_H W) ms') ->
ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W (ms_mem ms') (with_vm_backing (m_vm_lazy mdc) mat' mdc) k ->
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms') ->
frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
mem_grows (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
SRr SEGS W (mkCfg ms' (with_vm_backing (m_vm_lazy mdc) mat' mdc)) Q.
Lemma SRr_run_pi_AJ_call : forall W n E ss ss' s ms STK sp0 FP ly S W0 mem md own lyc Sc mdc k Q,
img_env VAL A_LIM E ->
st_ok_pi SEGS VAL E ss (restrict (w_H W) ms) ->
sym_runN_pi pl_tpi n ss = (ss', PRS_call s) ->
ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W (ms_mem ms) mdc k ->
awr_ok E (ss_mem ss) STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own ->
run_post_pi_AJ_call W E ss (setpc ss' (pa_sigma s)) ms STK sp0 FP ly S W0 mem md own lyc Sc mdc k Q ->
SRr SEGS W (mkCfg ms mdc) Q.
Proof.
intros W n E ss ss' s ms STK sp0 FP ly S W0 mem md own lyc Sc mdc k Q HE HS Hrun HJ Hwr Hk.
unfold sym_runN_pi in Hrun. rewrite <- pl_tpi_eq in Hrun.
destruct (PaRun.sym_run_pi_sound psym SEGS (clookup pa_tbl) VAL pa_sigma L pa_fetch_ok pa_cert pa_B_ok A_LIM A_LIM_text pl_lim
_ E ss ss' (PRS_call s) _ HE HS Hrun) as (msr' & Hms & HP & _ & Hfr).
cbn [PaRun.prun_post] in HP.
eapply (SRr_chain_AJ SEGS B LAWS pa_segs_low pa_wx W E (abs_ss VAL ss) (setpc ss' (pa_sigma s)) ms msr');
[ exact Hms | exact HP | destruct ss; exact Hfr | exact HJ | destruct ss; exact Hwr | ].
intros ms' mat' HS' HJ' HF HF' HG. apply (Hk ms' mat' HS' HJ'); destruct ss; first [exact HF | exact HF' | exact HG].
Qed.
End e.
End d.
Lemma zone2_of_app {rc : YM05.RunCeil} : forall a n, in_app a n -> off_img a n -> zone2 a n.
Proof. intros a n [_ H] Hi. split; [exact Hi|]. unfold kLowShadowBeg, kHighMemBeg in H. lia. Qed.
Ltac paj_run_shc RUNP RUNC HS HJ :=
lazymatch type of HS with
| st_ok_pi ?segs ?val ?E ?ss (restrict (w_H ?W) ?ms) =>
lazymatch type of RUNP with
| forall W n E ss ss' st ms STK sp0 FP ly S W0 mem md own lyc Sc mdc k Q, _ -> _ -> sym_runN_pi ?tpi n ss = _ -> _ =>
let r := eval vm_compute in (sym_runN_pi tpi FUEL ss) in
lazymatch r with
| (?ss', PRS_call ?s) =>
let Hrun := fresh "Hrun" in
assert (Hrun : sym_runN_pi tpi FUEL ss = (ss', PRS_call s)) by (vm_compute; reflexivity);
let HEI := lazymatch goal with HEI : img_env _ _ E |- _ => HEI | _ => fail "paj_run_shc: no hypothesis  img_env _ _ E" end in
eapply (RUNC W FUEL E ss ss' s ms _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEI HS Hrun HJ);
[ clear Hrun | clear Hrun HS HJ; cbn [setpc];
let ms' := fresh "ms" in let mat := fresh "mat" in let HF := fresh "HF" in let HFr := fresh "HFr" in let HG := fresh "HG" in
intros ms' mat HS HJ HF HFr HG; cbn [ms_mem mkst] in HF, HFr, HG, HJ ]
| (?ss', ?st) =>
let Hrun := fresh "Hrun" in
assert (Hrun : sym_runN_pi tpi FUEL ss = (ss', st)) by (vm_compute; reflexivity);
let HEI := lazymatch goal with HEI : img_env _ _ E |- _ => HEI | _ => fail "paj_run_shc: no hypothesis  img_env _ _ E" end in
eapply (RUNP W FUEL E ss ss' st ms _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEI HS Hrun I HJ);
[ clear Hrun | clear Hrun HS HJ;
let ms' := fresh "ms" in let mat := fresh "mat" in let HF := fresh "HF" in let HFr := fresh "HFr" in let HG := fresh "HG" in
intros ms' mat HS HJ HF HFr HG; cbn [ms_mem mkst] in HF, HFr, HG, HJ ]
end
end
| _ => fail "paj_run_shc: HS must be  st_ok_pi segs val E ss (restrict (w_H W) ms)"
end.
Ltac paj_run_to_shc RUNTOP HS HJ stop :=
paj_run_to_sh RUNTOP HS HJ stop;
[ | try (lazymatch goal with HFx : frame_of _ _ _ _ |- _ =>
repeat match goal with H : context [ms_mem (mkst _ _ _ _)] |- _ => progress cbn [ms_mem mkst] in H end end) ].
Ltac psrr_branch_pi RUNP BR HS :=
lazymatch type of HS with
| st_ok_pi ?segs ?val ?E ?ss (restrict (w_H ?W) ?ms) =>
lazymatch type of RUNP with
| forall W n E ss ss' st ms STK sp0 FP ly S W0 mem md own lyc Sc mdc k Q, _ -> _ -> sym_runN_pi ?tpi n ss = _ -> _ =>
let r := eval vm_compute in (sym_step_pi tpi ss) in
lazymatch r with
| PStop (SR_branch ?c ?a ?b) => apply (BR W E ss ms _ _ c a b HS); clear HS; let Hc := fresh "Hc" in intros Hc HS
| _ => fail "psrr_branch_pi: state is not stuck at a branch:" r
end end
end.

(* ============================================================================================== *)
(* 3. The tactics on small goals at lib/B's image.                                                 *)
(* ============================================================================================== *)

Section t.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {L : ptable psym} {PI : PAImg L}.
Lemma kitb_check_img : forall E, img_env pa_val A_LIM E -> bv_unsigned (ew E 242%nat) = pa_val (A_OBJ 1).
Proof. intros E HEI. img_factsF E. rewrite E242. apply unsigned_lit_small. apply pa_val_range. Qed.
Lemma kitb_check_kept : forall E (m m' : word -> option byte) cs,
img_env pa_val A_LIM E ->
val_mem pa_segs m (pa_val (A_OBJ 1)) 8 (pa_val (A_OBJ 15)) -> val_mem pa_segs m' (pa_val (A_OBJ 1)) 8 (pa_val (A_OBJ 15)) ->
region_kept pa_segs E m m' (YP09.mkRegion (Some 242%nat) 0 8 0 0 cs).
Proof.
intros E m m' cs HEI Kg Kg2.
keptFL I I I Kg Kg2 I I I I I I idtac idtac.
Qed.
Lemma kitb_check_upd : forall (W : world pa_segs) (E0 E : env) (m0 : word -> option byte) (ms : machine_state) (regs : bvmap 5 word),
(forall n, (n < 33)%nat -> ew E n = ew E0 n) ->
frame_of E [] (mrestrict (w_H W) m0) (mrestrict (w_H W) (ms_mem ms)) ->
bv_unsigned (ew E0 2) = spZ regs -> 0 <= spZ regs ->
forall a, spZ regs <= a < 2 ^ 64 -> aview pa_segs (w_H W) (ms_mem ms) a = aview pa_segs (w_H W) m0 a.
Proof. intros W E0 E m0 ms regs AG HFr Usp Hsp. upd_aboveW_init HFr AG HUP. exact HUP. Qed.
End t.
