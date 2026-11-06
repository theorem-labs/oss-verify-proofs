(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the generic part of proofs/cgif/cgif_file_fuzzer/lib/A/ACja.v for libreac/fuzz_disco's program walk, over fuzz_disco's listing. Image objects follow fuzz_disco.asan: the GOT word of the shadow-base cell is object 1 (atom 242), the GOT word of the side-stack flag is object 0 (atom 241), the shadow-base cell is object 66 (atom 307) and the side-stack flag cell is object 67 (atom 308), so img_factsF and img_hull_factsF give E240 E241 E242 E307 E308 and Hob241 Hob242 Hob307 Hob308, keptFL keeps those four regions, and aconstsF rewrites with PALib's pal_got_shadow, pal_cell and DiscoFrame's palf_got_uar. awrFL, keptFL, fs_roF and fs_rwF keep the walks' atoms for the own side-stack frame (516), its shadow (529), the realigned stack (60) and the stack (2), for any frame class; stack bounds compute the walk's own STK constant; cgif's case for its 40-byte FRAME block (atom 11) is left out, and awrFL_with/keptFL_with take a tactic for a walk's own head regions. Module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/DiscoACja.v, with its module paths, module names and numbers changed; 352 of its 420 lines of code are new or changed and 263 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YCkd.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP0d YP0c YP07 YI0w YI0z YI12 YC4a YC8i.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YC80 YC1f YC1g YC1h YC81 YC4b YC44 YC45 YC85 YC88.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YC8g YC1i.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YCjr YCj1 YCja.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require Import SnShared SnprintfDef PfFacts.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require SnprintfDefR.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Rt Require Import SnprintfConsts.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YRo.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YA0j.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import ReacDiscoTableJson TjBase TjCuts.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_json_text.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require tj_lemmas.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require disco_table_c reac_disco_table_json_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Ltac tjl_hd AG HSK :=
lazymatch goal with
| |- awr_ok _ (YP09.mkRegion (Some 2%nat) _ _ _ _ _ :: _) _ _ _ _ _ _ _ =>
eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat 0); [reflexivity | evalE AG | clear - HSK; cbn; lia | clear; cbn; lia |]
| |- awr_ok _ (YP09.mkRegion (Some 60%nat) _ _ _ _ _ :: _) _ ?sp0 _ _ _ _ _ =>
lazymatch goal with Hsp1 : sp0 - _ <= ?sp1 <= sp0 - _ |- _ =>
eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 60%nat (sp1 - sp0)); [reflexivity | evalE AG | clear - Hsp1 HSK; cbn; lia | clear - Hsp1; cbn; lia |] end
end.
Ltac tjl_fsb := repeat match goal with
| |- context [fs_frame_bytes ?c / 8] => let v := eval vm_compute in (fs_frame_bytes c / 8) in
lazymatch v with Zpos _ => change (fs_frame_bytes c / 8) with v end
| |- context [fs_frame_bytes ?c] => let v := eval vm_compute in (fs_frame_bytes c) in
lazymatch v with Zpos _ => change (fs_frame_bytes c) with v end
end.
Ltac tjl_awr_rec hd AG fpos F EFA :=
lazymatch goal with
| |- awr_ok _ [] _ _ _ _ _ _ _ => apply awr_ok_nil
| |- awr_ok _ (YP09.mkRegion _ _ _ ?wlo ?whi _ :: _) _ _ _ _ _ _ _ =>
first
[ lazymatch (eval vm_compute in (Z.leb whi wlo)) with true => apply awr_ok_cons_ro; [clear; cbn; lia|] end
| hd
| lazymatch goal with
| |- awr_ok _ (YP09.mkRegion (Some 529%nat) _ _ _ _ _ :: _) _ _ _ _ _ _ ((?c, _) :: _) =>
eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 529%nat); [reflexivity | evalE AG | | ];
[ cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; right; right; right; exists c, fpos; split; [left; reflexivity|]; right;
unfold in_zr, shadow_addr; cbn [fst snd]; rewrite <- SB_SHADOW_OFF; tjl_fsb; rewrite ?EFA; fold F; unfold SB; clear - Ha; lia
| ]
| |- awr_ok _ (YP09.mkRegion (Some 516%nat) _ _ _ _ _ :: _) _ _ _ _ _ _ ((?c, _) :: _) =>
eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 516%nat); [reflexivity | evalE AG | | ];
[ cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; right; right; right; exists c, fpos; split; [left; reflexivity|]; left;
unfold in_zr; cbn [fst snd]; tjl_fsb; rewrite ?EFA; fold F; clear - Ha; lia
| ]
end
| match goal with |- awr_ok _ (?r :: _) _ _ _ _ _ _ _ => idtac "AWR-HEAD" r end; fail 1 "tjl_awr: no rule for the head region" ];
tjl_awr_rec hd AG fpos F EFA
end.
Ltac tjl_awr hd AG fpos F EFA :=
lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fp b0 bc ly own) end;
tjl_awr_rec hd AG fpos F EFA.
Ltac tjl_rw HS E529 Hp :=
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs 529%nat in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rs got_regionP) in
let HS3 := fresh "HS3" in
pose proof (ast_ok_pi_set_region Ex ssx msx i r (set_window r 0 32) HS ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity)
(region_ok_rewindow _ Ex _ r 0 32 (st_ok_pi_region_nth Ex ssx msx i r HS ltac:(vm_compute; reflexivity))
ltac:(cbn [YP09.r_base base_val ms_mem restrict mkst]; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia;
rewrite E529, unsigned_lit_small by (unfold SB; lia);
intros o Ho; apply (apresent_writable _); unfold shadow_addr in Hp; rewrite <- SB_SHADOW_OFF in Hp;
apply (proj1 (Hp o ltac:(clear - Ho; lia)))))) as HS3;
clear HS; rename HS3 into HS; norm_ss HS end.
Ltac tjl_notw AG :=
let rg := fresh "rg" in let Hin := fresh "Hin" in let Hrg := fresh "Hrg" in
intros (rg & Hin & Hrg);
lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In rg rs1) in Hin end; cbn [In] in Hin;
repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrg; revert Hrg; evalE AG; intros Hrg; lia|]);
destruct Hin.
Ltac tjl_carry HG HFr AG :=
lazymatch type of HFr with frame_of _ _ (mrestrict _ ?m0) (mrestrict _ ?m1) =>
lazymatch type of HG with garr8 ?sg (mrestrict ?Hh m0) ?b ?l =>
let HG2 := fresh "HG" in
assert (HG2 : garr8 sg (mrestrict Hh m1) b l);
[ apply (garr8_aview_kept sg Hh Hh m0 m1 b l);
  [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; cbn in Ha; unbox; eapply aview_kept_out; [exact HFr | lia | tjl_notw AG]
  | exact HG ]
| clear HG; rename HG2 into HG ] end end.
Ltac tjl_get HS n Hr :=
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs n in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rs got_regionP) in
pose proof (st_ok_pi_region_nth Ex ssx msx i r HS ltac:(vm_compute; reflexivity)) as Hr;
cbn [ms_mem restrict] in Hr end.
Ltac tjl_drop HS bs :=
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (filter (fun r => negb (existsb (fun n => match YP09.r_base r with Some m => Nat.eqb m n | None => false end) bs)) (ss_mem ssx)) in
let HS3 := fresh "HS3" in
pose proof (st_ok_pi_submem Ex ssx msx rs HS ltac:(cbn [ss_mem]; submem_to) ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS end; norm_ss HS.
Ltac tjl_move Hr HFr AG :=
lazymatch type of HFr with frame_of _ _ (mrestrict ?Hh ?m0) (mrestrict ?Hh ?m1) =>
lazymatch type of Hr with region_ok ?sg ?Ex (mrestrict Hh m0) ?r =>
let Hr2 := fresh "Hr" in
assert (Hr2 : region_ok sg Ex (mrestrict Hh m1) r);
[ apply (region_ok_transport sg Ex Ex (mrestrict Hh m0) (mrestrict Hh m1) r Hr eq_refl);
  [ let c := fresh "c" in let Hc := fresh "Hc" in
    intros c Hc; cbn [YP09.r_chunks In] in Hc; repeat (destruct Hc as [<- | Hc]; [reflexivity|]); destruct Hc
  | let a := fresh "a" in let Ha := fresh "Ha" in
    intros a Ha; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val] in Ha; revert Ha; evalE AG; intros Ha;
    unfold mbyte; rewrite (HFr (Z_to_bv 64 a)); [reflexivity|];
    unbox; rewrite unsigned_lit_small by lia; tjl_notw AG
  | let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; lia
  | vm_compute; reflexivity ]
| clear Hr; rename Hr2 into Hr ] end end.
Lemma tjl_all_disjoint_app : forall E r l1 l2, all_disjoint E r l1 -> all_disjoint E r l2 -> all_disjoint E r (l1 ++ l2).
Proof. intros E r l1 l2. induction l1 as [|r1 l1 IH]; cbn [app all_disjoint]; [tauto|]. intros [H1 H2] H3. split; [exact H1 | apply IH; assumption]. Qed.
Lemma tjl_pairwise_app : forall E l1 l2, pairwise_disjoint E l1 -> pairwise_disjoint E l2 ->
Forall (fun r => all_disjoint E r l2) l1 -> pairwise_disjoint E (l1 ++ l2).
Proof.
intros E l1 l2. induction l1 as [|r1 l1 IH]; cbn [app pairwise_disjoint]; [tauto|].
intros [H1 H2] H3 H4. inversion H4 as [|x l Hx Hl]; subst. split; [apply tjl_all_disjoint_app; assumption | apply IH; assumption].
Qed.
Lemma tjl_regions_wf_app : forall l1 l2, regions_wf l1 = true -> regions_wf l2 = true -> regions_wf (l1 ++ l2) = true.
Proof.
intros l1 l2. induction l1 as [|r1 l1 IH]; cbn [app regions_wf]; [tauto|].
intros H1 H2. apply andb_prop in H1 as [H1a H1b]. rewrite H1a, (IH H1b H2). reflexivity.
Qed.
Lemma tjl_st_ok_app : forall segs (fq : YK11.FPState) E ss ms rs2,
YP0l.st_ok (fx := fq) segs E ss ms -> regions_wf rs2 = true -> Forall (region_ok segs E (ms_mem ms)) rs2 -> pairwise_disjoint E rs2 ->
Forall (fun r => all_disjoint E r rs2) (ss_mem ss) ->
YP0l.st_ok (fx := fq) segs E (mkSS (ss_pc ss) (ss_regs ss) (ss_mem ss ++ rs2) (ss_resv ss) (ss_facts ss)) ms.
Proof.
intros segs fq E ss ms rs2 (H1 & H2 & H3 & H4 & H5 & H6 & H7 & (Hwf & Hok & Hpd) & H9) Hwf2 Hok2 Hpd2 Hx.
unfold YP0l.st_ok; cbn [ss_pc ss_regs ss_mem ss_resv ss_facts]. repeat (split; [assumption|]). split; [|exact H9].
unfold mem_ok.
split; [apply tjl_regions_wf_app; assumption|]. split; [apply Forall_app; split; assumption|].
apply tjl_pairwise_app; assumption.
Qed.
Definition ss_tjPL : sstate :=
(mkSS 23600 [SLit 0; SOff 530 0; SOff 60 0; SOff 3 0; SOff 4 0; SOff 531 0; SOff 532 0; SOff 533 0; SOff 2 0; SOff 60 0; SExt true 32 (SOff 600 0); SOff 535 0; SOff 536 0; SOff 10 384; SOff 538 0; SOff 539 0; SOff 540 0; SOff 541 0; SOff 516 0; SOff 516 0; SOff 13 0; SOff 12 0; SOff 529 0; SLit 18446744073709551615; SOff 11 0; SOff 32 0; SLit 1; SOff 10 0; SOff 542 0; SOff 543 0; SOff 544 0; SOff 545 0] [YP09.mkRegion (Some 10%nat) 384 388 0 0 [YP09.mkChunk 384 (CVal 4 (SOff 600 0))]; YP09.mkRegion (Some 529%nat) 0 32 0 0 [YP09.mkChunk 27 (CVal 1 (SLit 18446744073709551603)); YP09.mkChunk 26 (CVal 1 (SLit 18446744073709551603)); YP09.mkChunk 25 (CVal 1 (SLit 18446744073709551608)); YP09.mkChunk 24 (CVal 1 (SLit 18446744073709551608)); YP09.mkChunk 31 (CVal 1 (SLit 18446744073709551603)); YP09.mkChunk 30 (CVal 1 (SLit 18446744073709551603)); YP09.mkChunk 29 (CVal 1 (SLit 18446744073709551603)); YP09.mkChunk 28 (CVal 1 (SLit 18446744073709551603)); YP09.mkChunk 23 (CVal 1 (SLit 18446744073709551608)); YP09.mkChunk 22 (CVal 1 (SLit 18446744073709551608)); YP09.mkChunk 21 (CVal 1 (SLit 18446744073709551608)); YP09.mkChunk 20 (CVal 1 (SLit 18446744073709551608)); YP09.mkChunk 19 (CVal 1 (SLit 18446744073709551602)); YP09.mkChunk 18 (CVal 1 (SLit 18446744073709551602)); YP09.mkChunk 17 (CVal 1 (SLit 18446744073709551602)); YP09.mkChunk 16 (CVal 1 (SLit 18446744073709551602)); YP09.mkChunk 11 (CVal 1 (SLit 18446744073709551602)); YP09.mkChunk 10 (CVal 1 (SLit 18446744073709551602)); YP09.mkChunk 9 (CVal 1 (SLit 18446744073709551602)); YP09.mkChunk 8 (CVal 1 (SLit 18446744073709551602)); YP09.mkChunk 15 (CVal 1 (SLit 18446744073709551602)); YP09.mkChunk 14 (CVal 1 (SLit 18446744073709551608)); YP09.mkChunk 13 (CVal 1 (SLit 18446744073709551608)); YP09.mkChunk 12 (CVal 1 (SLit 18446744073709551608)); YP09.mkChunk 7 (CVal 1 (SLit 18446744073709551602)); YP09.mkChunk 6 (CVal 1 (SLit 18446744073709551608)); YP09.mkChunk 5 (CVal 1 (SLit 18446744073709551608)); YP09.mkChunk 4 (CVal 1 (SLit 18446744073709551608)); YP09.mkChunk 3 (CVal 1 (SLit 18446744073709551601)); YP09.mkChunk 2 (CVal 1 (SLit 18446744073709551601)); YP09.mkChunk 1 (CVal 1 (SLit 18446744073709551601)); YP09.mkChunk 0 (CVal 1 (SLit 18446744073709551601))]; YP09.mkRegion (Some 516%nat) 0 256 0 256 [YP09.mkChunk 16 (CVal 8 (SOff 279 0)); YP09.mkChunk 8 (CVal 8 (SOff 278 0)); YP09.mkChunk 0 (CVal 8 (SLit 1102416563)); YP09.mkChunk 248 (CVal 8 (SOff 528 0))]; YP09.mkRegion (Some 60%nat) 0 184 0 184 [YP09.mkChunk 80 (CVal 8 (SOff 516 0)); YP09.mkChunk 96 (CVal 8 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 384) (SLit 3)) (SOff 32 0))); YP09.mkChunk 176 (CVal 8 (SOff 516 0))]; YP09.mkRegion (Some 2%nat) (-104) 0 (-104) 0 [YP09.mkChunk (-104) (CVal 8 (SOff 27 0)); YP09.mkChunk (-96) (CVal 8 (SOff 26 0)); YP09.mkChunk (-88) (CVal 8 (SOff 25 0)); YP09.mkChunk (-80) (CVal 8 (SOff 24 0)); YP09.mkChunk (-72) (CVal 8 (SOff 23 0)); YP09.mkChunk (-64) (CVal 8 (SOff 22 0)); YP09.mkChunk (-56) (CVal 8 (SOff 21 0)); YP09.mkChunk (-48) (CVal 8 (SOff 20 0)); YP09.mkChunk (-40) (CVal 8 (SOff 19 0)); YP09.mkChunk (-32) (CVal 8 (SOff 18 0)); YP09.mkChunk (-24) (CVal 8 (SOff 9 0)); YP09.mkChunk (-16) (CVal 8 (SOff 8 0)); YP09.mkChunk (-8) (CVal 8 (SOff 1 0))]; YP09.mkRegion (Some 241%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 253 0))]; YP09.mkRegion (Some 253%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 32 0))]; YP09.mkRegion (Some 242%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 33 0))]; YP09.mkRegion (Some 33%nat) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SLit 1))]] None (mkFacts [(12%nat, mkAF 4096 140737479966720 4); (10%nat, mkAF 4096 140737479966720 3); (529%nat, mkAF 2147451392 17594333495296 2); (528%nat, mkAF 4096 140737479966720 0); (516%nat, mkAF 4096 140737479966720 5); (60%nat, mkAF 70368744177152 140737488355328 5); (2%nat, mkAF 70368744177664 140737488355328 4); (32%nat, mkAF 2147450880 2147450880 0); (13%nat, mkAF 0 2147483647 0)] [mkAC BC_LT (SLit 0) (SExt true 32 (SOff 600 0)); mkAC BC_LTU (SLit 1) (SOff 13 0); mkAC BC_GEU (SOff 13 0) (SLit 3)] [(SAlu ALU_ADD (SAlu ALU_SRL (SOff 516 0) (SLit 3)) (SOff 32 0), SOff 529 0)])).
Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
Context {RO : ro_below_ofl (@pa_segs _ lib_both3_0_listing PI) (@pa_relro_lo _ lib_both3_0_listing PI) (@pa_relro_hi _ lib_both3_0_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
Lemma tjl_st_ok_pi_app : forall (fq : YK11.FPState) E ss ms rs2,
st_ok_pi (fx := fq) SEGS VAL E ss ms -> regions_wf rs2 = true -> Forall (region_ok SEGS E (ms_mem ms)) rs2 -> pairwise_disjoint E rs2 ->
Forall (fun r => all_disjoint E r rs2) (ss_mem ss) ->
st_ok_pi (fx := fq) SEGS VAL E (mkSS (ss_pc ss) (ss_regs ss) (ss_mem ss ++ rs2) (ss_resv ss) (ss_facts ss)) ms.
Proof.
intros fq E ss ms rs2 HS Hwf2 Hok2 Hpd2 Hx. destruct ss as [pc0 sr0 fr0 sm0 rv0 fs0].
exact (tjl_st_ok_app SEGS fq E _ ms rs2 HS Hwf2 Hok2 Hpd2 Hx).
Qed.
Definition tjl_nt : YP09.chunk := YP09.mkChunk 128 (CVal 8 (SAlu ALU_XOR (SOff 10 0) (SLit 18446744073709551615))).
Definition tjl_fix (c : YP09.chunk) : YP09.chunk := if (YP09.c_off c =? 128) then tjl_nt else c.
Lemma tjl_region_ok_fix : forall E m b lo hi wlo whi cs,
region_ok SEGS E m (YP09.mkRegion b lo hi wlo whi cs) ->
(forall c, In c cs -> YP09.c_off c = 128 -> c = YP09.mkChunk 128 (CVal 8 (SAlu ALU_XOR (SOff 10 0) (SLit (-1))))) ->
region_ok SEGS E m (YP09.mkRegion b lo hi wlo whi (map tjl_fix cs)).
Proof.
intros E m b lo hi wlo whi cs (H1 & H2 & H3 & H4) Hc.
split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
cbn [YP09.r_chunks YP09.r_base] in H4 |- *.
apply Forall_forall. intros c' Hc'. apply in_map_iff in Hc' as (c & <- & Hin).
pose proof (proj1 (Forall_forall _ _) H4 c Hin) as Hck.
unfold tjl_fix. destruct (Z.eqb_spec (YP09.c_off c) 128) as [E128|E128]; [|exact Hck].
rewrite (Hc c Hin E128) in Hck. unfold tjl_nt.
intros i Hi. destruct (Hck i Hi) as (bt & Hb1 & Hb2). exists bt. split; [|exact Hb2].
cbn [YP09.cbyte YP09.c_val YP09.c_off] in Hb1 |- *. rewrite <- Hb1. reflexivity.
Qed.
Ltac tjl_fix60 HS :=
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs 60%nat in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rs got_regionP) in
lazymatch r with YP09.mkRegion ?b ?lo ?hi ?wlo ?whi ?cs =>
let HS3 := fresh "HS3" in
pose proof (ast_ok_pi_set_region Ex ssx msx i r (YP09.mkRegion b lo hi wlo whi (map tjl_fix cs)) HS ltac:(vm_compute; reflexivity) eq_refl
ltac:(vm_compute; reflexivity)
(tjl_region_ok_fix Ex _ b lo hi wlo whi cs (st_ok_pi_region_nth Ex ssx msx i r HS ltac:(vm_compute; reflexivity))
ltac:(let c := fresh "c" in let Hc := fresh "Hc" in let Ho := fresh "Ho" in intros c Hc Ho; cbn [In] in Hc;
repeat (destruct Hc as [<- | Hc]; [first [reflexivity | cbn [YP09.c_off] in Ho; lia] |]); destruct Hc))) as HS3;
clear HS; rename HS3 into HS end end; norm_ss HS.
Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TLF : PALibF B.
Variables SNPC GC GV IMGLO IMGHI : Z.
Variable CR : list (Z * Z).
Hypothesis HSNPC : SIGMA AS___interceptor_trampoline_snprintf = SNPC.
Hypothesis ASNP : forall fq : YK11.FPState,
SnprintfDefR.sh_asnprintf_realizesR (fx := fq) SEGS B pa_relro_lo pa_relro_hi (SnFF.FF_disco disco_fmt_lo disco_fmt_hi) SNPRINTF_STK GC GV IMGLO IMGHI CR SNPC.
Hypothesis tj_snp_consts : forall (W : world SEGS) mem, arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) -> consts_view SEGS W mem CR.
Hypothesis tj_snp_cr : Forall (fun r => IMG_LO <= fst r /\ 0 <= snd r /\ fst r + snd r <= IMG_TOP) CR.
Hypothesis tj_snp_canary : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
exists cval, rdword (aview SEGS (w_H W) mem) GC = Some GV /\ rdword (aview SEGS (w_H W) mem) GV = Some cval.
Hypothesis tj_snp_gcgv : IMG_LO <= GC /\ GC + 8 <= IMG_TOP /\ IMG_LO <= GV /\ GV + 8 <= IMG_TOP.
Hypothesis tj_snp_img : IMG_LO <= IMGLO /\ IMGHI <= IMG_TOP.
Hypothesis GM : globs_marked SEGS B tfib_globs.
Hypothesis HV : img_shadow_vis SEGS B.
Hypothesis DRO : tfib_ro_unowned B.
Hypothesis TJS : tj_strs.
Variable IMG : world SEGS -> (word -> option byte) -> Prop.
Lemma tjl_keep_journal : forall (cx : tjcx) own ly' S' (W' : world SEGS) mem' md' k,
tj_baseX B IMG cx ->
ajournal SEGS B REAC_DISCO_TABLE_JSON_STK (spZ (c_regs cx)) (tj_fp (c_buf cx) (c_cap cx)) (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
own ly' S' W' mem' md' k ->
tj_keep B cx W' mem'.
Proof.
intros cx own ly' S' W' mem' md' k HB HJ.
destruct cx as [fq ly S W regs mem md ch t now buf cap Nb T fpos sp1 E0].
unfold tj_baseX in HB. unfold tj_keep.
cbn [c_fq c_ly c_S c_W c_regs c_mem c_md c_ch c_t c_now c_buf c_cap c_Nb c_T c_fpos c_sp1 c_E0] in HB, HJ |- *.
destruct HB as (HPRE & Hroom & HROD & HIM & H10 & H11 & H12 & H13 & Hnow & Hcap & Hobj & Harr & HlenT & Hok
& Hbuf & Hsp1b & HE0 & HE032 & HE033 & HE02 & Hfrm).
pose proof HPRE as (HAR & _).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
pose proof Hobj as ((cid & pos & Hin & Hcid & Hal8 & Hflo & Hfhi) & Ht8 & Hra).
assert (HnF : forall x, inFP (tj_fp buf cap) x -> (x < kLowShadowBeg \/ kHighShadowEnd <= x) /\
~ (frame_addr ly cid pos <= x < frame_addr ly cid pos + fs_frame_bytes cid)).
{ intros x Hx. unfold tj_fp in Hx. destruct (Z.ltb_spec cap 3) as [Hc|Hc]; [destruct Hx as (r & [] & _)|].
destruct (Hbuf Hc) as (Hbin & Hbsz).
destruct (al_blocks _ _ LAWS _ _ _ _ _ buf Nb HAR Hbin) as (_ & Hb4096 & Hbceil & Hbapp & _).
pose proof (sep_block_frame SEGS B LAWS ly S W mem md buf Nb cid pos HAR Hbin Hin) as HdBF.
unfold zdisjoint in HdBF. cbn [fst snd] in HdBF.
destruct Hx as (r & [<- | []] & Hr). cbn [fst snd] in Hr.
unfold in_app, kLowShadowBeg, kHighShadowEnd, kHighMemBeg, ASAN_CEIL in *. split; lia. }
split; [exact (arodata_ok_journalP SEGS pa_relro_lo pa_relro_hi pa_relro_img B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ HROD)|].
split.
- intros j Hj. destruct (Harr j Hj) as (Hv & Hr). split; [|exact Hr].
rewrite length_map, HlenT in Hj.
eapply val_mem_entry_frame; [exact HJ | exact Hin | lia | lia | | exact Hv].
intros x Hx HF. destruct (HnF x HF) as (_ & Hn). apply Hn. lia.
- split; [exists cid, pos; repeat split; assumption|]. split; [exact Ht8|].
eapply range_addressable_entry_frame; [exact LAWS | exact HJ | exact Hin | exact Hcid | exact Hflo | exact Hfhi | exact Hal8 | | exact HAR | exact Hra].
intros x HF. exact (proj1 (HnF x HF)).
Qed.
Hypothesis FL : tj_fromL B IMG 0.
Lemma pb_tj_pre_L : forall fq ly S W regs mem md ch t now buf cap Nb T fpos sp1 E0 (k : Z) ly3 S3 (W3 : world SEGS)
(ms : machine_state) (md2 : Model) (Ev : env),
tj_baseX B IMG (mkTJCX fq ly S W regs mem md ch t now buf cap Nb T fpos sp1 E0) ->
frames S3 = (2, fpos) :: frames S ->
k <= 0 ->
ablocks B ly3 S3 = ablocks B ly S ->
3 <= cap ->
0 < disco_table_c.n_of T ->
ajournal SEGS B REAC_DISCO_TABLE_JSON_STK (spZ regs) (tj_fp buf cap) ly S W mem md [(2, fpos)] ly3 S3 W3 (ms_mem ms) md2 k ->
garr8 SEGS (mrestrict (w_H W3) (ms_mem ms)) buf ([91] ++ [0]) ->
(forall n, (n < 33)%nat -> ew Ev n = ew E0 n) ->
ew Ev 33 = Z_to_bv 64 (as_uar_cell B) ->
ew Ev 60 = Z_to_bv 64 sp1 ->
ew Ev 516 = Z_to_bv 64 (frame_addr ly 2 fpos) ->
ew Ev 528 = Z_to_bv 64 (flag_addr ly 2 fpos) ->
ew Ev 529 = Z_to_bv 64 (SB + frame_addr ly 2 fpos / 8) ->
img_env VAL A_LIM Ev ->
sh_ok SEGS (SOff 32 0) [mkSHE 10 0 400; mkSHE 516 256 0] Ev (mrestrict (w_H W3) (ms_mem ms)) ->
st_ok_pi (fx := fq) SEGS VAL Ev ss_tjPL (restrict (w_H W3) ms) ->
SRr SEGS W3 (mkCfg ms md2) (tj_postX B (mkTJCX fq ly S W regs mem md ch t now buf cap Nb T fpos sp1 E0)).
Proof.
intros fq ly S W regs mem md ch t now buf cap Nb T fpos sp1 E0 k ly3 S3 W3 ms md2 Ev HBASE HFR Hk0 Hab Hc3 Hnpos HJ2 HG91
AG E33 E60 E516 E528 E529 HEI SHOK HS.
pose proof HBASE as HB0. unfold tj_baseX in HB0.
cbn [c_fq c_ly c_S c_W c_regs c_mem c_md c_ch c_t c_now c_buf c_cap c_Nb c_T c_fpos c_sp1 c_E0] in HB0.
destruct HB0 as (HPRE & Hroom & HROD & HIM & H10 & H11 & H12 & H13 & Hnow & Hcap & Hobj & Harr & HlenT & Hok
& Hbuf & Hsp1b & HE0 & HE032 & HE033 & HE02 & Hfrm).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (HSNP : SNPRINTF_STK = 11776) by reflexivity.
assert (HSK : 12416 <= REAC_DISCO_TABLE_JSON_STK) by (unfold REAC_DISCO_TABLE_JSON_STK; lia). clear HSNP.
destruct (sp1_facts (spZ regs + -288) ltac:(clear - Hceil Hslo Hstk0 HSK C1; lia)
ltac:(rewrite <- Zplus_mod_idemp_l, Hal16; reflexivity)) as (Hsp1r & Hsp1al & Hsp1al16).
rewrite <- Hsp1b in Hsp1r, Hsp1al, Hsp1al16.
assert (Hsp1 : spZ regs - 304 <= sp1 <= spZ regs - 288) by (clear - Hsp1r; lia). clear Hsp1r Hsp1al Hsp1al16 Hsp1b Hal16.
pose (RUNTO := paj_run_to (fx := fq) B LAWS).
pose proof HJ2 as (HAR3 & Hly3 & _).
destruct (al_layout _ _ LAWS ly S W mem md ly3 HAR Hly3) as (Eab3 & EFA & Eown3).
assert (EFA0 : forall c p, frame_addr ly3 c p = frame_addr ly c p) by exact EFA.
set (F := frame_addr ly 2 fpos) in *. set (FLg := flag_addr ly 2 fpos) in *.
assert (Hfin : In (2, fpos) (frames S3)) by (rewrite HFR; left; reflexivity).
assert (E10v : ew Ev 10 = Z_to_bv 64 t) by (rewrite (AG 10%nat ltac:(lia)); rewrite (HE0 10%nat 10%bv eq_refl); exact H10).
assert (E12v : ew Ev 12 = Z_to_bv 64 buf) by (rewrite (AG 12%nat ltac:(lia)); rewrite (HE0 12%nat 12%bv eq_refl); exact H12).
assert (E32v : ew Ev 32 = Z_to_bv 64 SB) by (rewrite (AG 32%nat ltac:(lia)); exact HE032).
img_factsF Ev.
pose proof (pa_obj_img 0 ltac:(lia)) as Hob241. pose proof (pa_obj_img 1 ltac:(lia)) as Hob242.
pose proof (pa_obj_img 12 ltac:(lia)) as Hob253.
cbv [A_OBJ Nat.add] in Hob241, Hob242, Hob253.
pose proof (palf_uar_img B TLF) as Huar.
unfold IMG_LO, IMG_TOP in Hob241, Hob242, Hob253, Huar.
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 2 fpos HAR3 Hfin) as (HF4096 & HFceil & HFhigh).
rewrite EFA in HF4096, HFceil, HFhigh. fold F in HF4096, HFceil, HFhigh.
pose proof (frm_off_imgP _ _ _ _ _ _ _ _ HAR3 Hfin) as HFhigh_img. rewrite EFA in HFhigh_img. fold F in HFhigh_img.
change (fs_frame_bytes 2) with 256 in *.
assert (HF3 : frame_addr ly3 2 fpos = F) by (rewrite EFA; reflexivity).
assert (HFoff : F + 256 <= 65536 \/ 6283264 <= F) by (clear - HFhigh_img; unfold off_img, IMG_LO, IMG_TOP in HFhigh_img; lia).
destruct (Hbuf Hc3) as (Hbin & Hbsz).
assert (Hbin3 : In (buf, Nb) (ablocks B ly3 S3)) by (rewrite Hab; exact Hbin).
destruct (al_blocks _ _ LAWS _ _ _ _ _ buf Nb HAR3 Hbin3) as (_ & Hb4096 & Hbceil & Hbapp & _).
pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ buf Nb 2 fpos HAR3 Hbin3 Hfin) as HdBF.
unfold zdisjoint in HdBF. cbn [fst snd] in HdBF. rewrite HF3 in HdBF. change (fs_frame_bytes 2) with 256 in HdBF.
pose proof Hbapp as Hbapp'. unfold in_app, kLowShadowBeg, kHighMemBeg in Hbapp'.
pose proof (tjl_keep_journal (mkTJCX fq ly S W regs mem md ch t now buf cap Nb T fpos sp1 E0) _ _ _ _ _ _ _ HBASE HJ2) as HK2.
unfold tj_keep in HK2. cbn [c_t c_T c_ly c_S] in HK2.
destruct HK2 as (HROD2 & _ & HobjT2).
pose proof HobjT2 as ((tcid & tpos & Htin & _ & _ & Htflo & Htfhi) & _ & _).
assert (HtF : In (tcid, tpos) (frames S3)) by (rewrite HFR; right; exact Htin).
pose proof (frm_off_imgP _ _ _ _ _ _ _ _ HAR3 HtF) as Htimg. rewrite EFA in Htimg.
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ tcid tpos HAR3 HtF) as (Ht4096 & Htceil & _). rewrite EFA in Ht4096, Htceil.
assert (Htoff : t + 400 <= 65536 \/ 6283264 <= t) by (clear - Htimg Htflo Htfhi; unfold off_img, IMG_LO, IMG_TOP in Htimg; lia).
assert (Ht0 : 4096 <= t /\ t + 400 <= alloc_ceiling) by (clear - Ht4096 Htflo Htfhi Htceil; lia).
clear Htimg Htflo Htfhi Ht4096 Htceil HFhigh_img HFhigh Hbapp Hbuf HobjT2.
box Htoff. box HFoff. box HdBF. box Hbapp'.
pose proof TJS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & TJKD).
destruct TJKD as (Hkdin & Hkdro & Hkdby).
cbn [A_OBJ Nat.add] in Hkdin, Hkdro, Hkdby.
assert (Hkdv : 66320 <= VAL 258 /\ VAL 258 + 8 <= 66528).
{ clear - Hkdin. unfold tfib_ro_extra in Hkdin. cbn [In] in Hkdin.
repeat (destruct Hkdin as [Hkd | Hkdin];
[pose proof (f_equal fst Hkd) as Hk1; pose proof (f_equal snd Hkd) as Hk2; cbn [fst snd] in Hk1, Hk2; clear - Hk1 Hk2; lia|]).
destruct Hkdin. }
assert (Hin17 : In (VAL 258, 8) tfib_ro_ranges) by (unfold tfib_ro_ranges; apply in_or_app; right; exact Hkdin).
pose proof (tfib_ro_unowned_at B (VAL 258) 8 DRO Hin17) as Hun17.
assert (E258 : ew Ev 258 = Z_to_bv 64 (VAL 258)) by (apply img_env_atomP; [assumption | unfold A_TEXT, A_LIM; lia]).
assert (HKD : val_mem SEGS (mrestrict (w_H W3) (ms_mem ms)) (VAL 258 + 0) 8 tj_KD).
{ rewrite Z.add_0_r. intros kk Hkk.
pose proof (ro_bytes SEGS pa_relro_lo pa_relro_hi B _ (VAL 258) 8 (VAL 258 + Z.of_nat kk) HROD2
(Hkdro (VAL 258 + Z.of_nat kk) ltac:(clear - Hkk; lia)) Hun17 ltac:(clear - Hkk; lia)) as Hr.
rewrite (Hkdby kk ltac:(cbn; clear - Hkk; lia)) in Hr.
destruct (aview_byte SEGS _ _ _ _ Hr) as (b & Hb & Hbv & _). rewrite Hb. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned, <- Hbv.
do 8 (destruct kk as [|kk]; [vm_compute; reflexivity|]). lia. }
clear Hkdin Hkdro Hkdby Hin17 Hun17.
norm_ss HS.
tjl_get HS 241%nat R241. tjl_get HS 253%nat R253. tjl_get HS 242%nat R242. tjl_get HS 33%nat R33.
tjl_drop HS [241; 253; 242; 33]%nat.
lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
pose proof (st_ok_pi_add_region Ex _ _ (YP09.mkRegion (Some 258%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SLit tj_KD))]) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
rewrite E258, unsigned_lit_small by (clear - Hkdv; lia); split; [clear - Hkdv; lia|]; split; [clear - Hkdv; lia|];
split; [intros o Ho; clear - Ho; lia|];
apply Forall_cons; [|apply Forall_nil];
apply (chunk_ok_val SEGS Ex _ (VAL 258) 0 8 (SLit tj_KD) tj_KD); [reflexivity | unfold tj_KD; cbn; lia | zside | exact HKD])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite E258; evalE AG; unfold SB; unbox;
repeat split; clear - Hkdv Htoff Ht0 HFoff HF4096 HFceil Hsp1 Hslo Hceil HSK C1 Hshi H47; lia)) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS.
hei_havoc HS; paj_run_to_tok RUNTO HS HJ2 SHOK Bspan 0x5c94. { tjl_awr ltac:(idtac; tjl_hd AG HSK) AG fpos F EFA0. }
tjl_carry HG91 HFr AG.
tjl_move R241 HFr AG. tjl_move R253 HFr AG. tjl_move R242 HFr AG. tjl_move R33 HFr AG.
clear_frames.
tjl_drop HS [258]%nat.
lazymatch type of R241 with region_ok _ _ _ ?r241 =>
lazymatch type of R253 with region_ok _ _ _ ?r253 =>
lazymatch type of R242 with region_ok _ _ _ ?r242 =>
lazymatch type of R33 with region_ok _ _ _ ?r33 =>
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
pose proof (tjl_st_ok_pi_app fq Ex ssx msx [r241; r253; r242; r33] HS eq_refl
ltac:(cbn [ms_mem restrict];
apply Forall_cons; [exact R241|]; apply Forall_cons; [exact R253|]; apply Forall_cons; [exact R242|];
apply Forall_cons; [exact R33|]; apply Forall_nil)
ltac:(cbn [pairwise_disjoint all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
evalE AG; pose proof (palf_sep B TLF) as Hsep4; cbv [A_OBJ Nat.add] in Hsep4; cbn [zseps zseps_from fst snd] in Hsep4;
repeat split; clear - Hsep4; lia)
ltac:(lazymatch goal with |- Forall _ ?rsy => let rs2 := eval vm_compute in rsy in change rsy with rs2 end;
repeat (apply Forall_cons; [cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
evalE AG; unfold SB; unbox; repeat split; clear - Hob241 Hob242 Hob253 Huar Htoff Ht0 HFoff HF4096 HFceil Hsp1 Hslo Hceil HSK C1 Hshi H47; lia|]);
apply Forall_nil)) as HS3;
clear HS; rename HS3 into HS end end end end end.
norm_ss HS.
clear R241 R253 R242 R33.
pose proof HJ2 as (HARx & _).
destruct (al_frames _ _ LAWS _ _ _ _ _ 2 fpos HARx Hfin) as (_ & _ & _ & HFSx).
rewrite HF3 in HFSx. change (fs_frame_bytes 2 / 8) with 32 in HFSx.
tjl_rw HS E529 HFSx. tjl_fix60 HS.
prreg HS (19%bv : bv 5) R19. prreg HS (14%bv : bv 5) R14. prreg HS (26%bv : bv 5) R26.
ra_join HS ss_tjL 720%nat ([1; 19; 14; 5; 6; 7; 10; 11; 12; 15; 16; 17; 23; 26; 24; 27; 28; 29; 30; 31]%bv : list (bv 5)) idtac.
ra_join_val HS 720%nat 1%nat R19 E721. ra_join_val HS 720%nat 2%nat R14 E722. ra_join_val HS 720%nat 13%nat R26 E733.
hei_havoc HS. rebaseE HS AG HEv. clear HEv.
lazymatch goal with |- SRr _ ?Wg (mkCfg ?msF ?mdF) _ =>
lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
eapply (FL (mkTJCX fq ly S W regs mem md ch t now buf cap Nb T fpos sp1 E0) Ex k _ _ Wg msF mdF) end end.
- exact HBASE.
- unfold tj_EX, tj_F, tj_FL. cbn [c_ly c_fpos c_E0 c_sp1]. fold F FLg.
split; [intros n Hn; destruct (Nat.eq_dec n 33) as [->|Hn33]; [rewrite E33; symmetry; exact HE033 | apply AG; lia]|].
split; [exact E60|]. split; [exact E516|]. split; [exact E528|]. split; [exact E529 | assumption].
- cbn [c_regs c_ly c_S c_W c_mem c_md c_fpos c_buf c_cap]. exact HJ2.
- cbn [c_S c_fpos]. exact HFR.
- unfold INV_tjL. cbn [c_ly c_S c_cap c_T c_now c_buf].
split; [lia|]. split; [rewrite Hab; apply Permutation_refl|].
split; [exact (tjl_keep_journal _ _ _ _ _ _ _ _ HBASE HJ2)|]. split; [lia|]. split; [lia|].
split; [rewrite E721; reflexivity|]. split; [rewrite E722; reflexivity|].
exists [91]. split; [rewrite E733; reflexivity|]. split; [cbn [length Z.of_nat]; lia|].
split; [exact (tj_lemmas.tj_rest_0 T now) | exact HG91].
- exact HS.
Qed.
End h.
End f.
End d.
