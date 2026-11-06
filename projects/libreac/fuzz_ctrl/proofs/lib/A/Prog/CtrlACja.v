(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the generic part of proofs/cgif/cgif_file_fuzzer/lib/A/ACja.v for libreac/fuzz_grant's program walk, over fuzz_grant's listing. Image objects follow fuzz_grant.asan: the GOT word of the shadow-base cell is object 1 (atom 242), the GOT word of the side-stack flag is object 0 (atom 241), the shadow-base cell is object 32 (atom 273) and the side-stack flag cell is object 33 (atom 274), so img_factsF and img_hull_factsF give E240 E241 E242 E273 E274 and Hob241 Hob242 Hob273 Hob274, keptFL keeps those four regions, and aconstsF rewrites with PALib's pal_got_shadow, pal_cell and GrantFrame's palf_got_uar. awrFL, keptFL, fs_roF and fs_rwF keep the walks' atoms for the own side-stack frame (516), its shadow (529), the realigned stack (60) and the stack (2), for any frame class; stack bounds compute the walk's own STK constant; cgif's case for its 40-byte FRAME block (atom 11) is left out, and awrFL_with/keptFL_with take a tactic for a walk's own head regions. Module paths changed. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_grant/lib/A/Prog/GrantACja.v of a working branch ca2ec2ecd18 and re-keyed to fuzz_ctrl.asan, whose shadow-base cell is object 30 (atom 271) and whose side-stack flag cell is object 31 (atom 272): img_factsF and img_hull_factsF now give E240 E241 E242 E271 E272 and Hob241 Hob242 Hob271 Hob272, and keptFL keeps the regions of atoms 241, 242, 271 and 272. The two GOT words (objects 0 and 1, atoms 241 and 242) are unchanged. Module paths and module names re-keyed to fuzz_ctrl. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import YCkd.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import PaRun PaShadow CtrlSyms CtrlList CtrlPa.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import PaJournal CtrlPaLib YC1g YC1h YC81 YC4b CtrlFrame YC45.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import CtrlBase.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import CtrlACjr ACj1.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac evalE AG ::=
cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia;
repeat match goal with H : ew ?Ex ?n = Z_to_bv 64 _ |- context [ew ?Ex ?n] => rewrite H end;
lazymatch type of AG with forall n, _ -> ew ?Ev n = _ =>
repeat match goal with |- context [ew Ev ?n] => lazymatch (eval cbv in (Nat.ltb n 33)) with true => rewrite (AG n) by lia end end end;
repeat match goal with H : ew ?Ex ?n = Z_to_bv 64 _ |- context [ew ?Ex ?n] => rewrite H end;
repeat match goal with H : bv_unsigned (ew ?Ex 2) = _ |- context [bv_unsigned (ew ?Ex 2)] => rewrite H end;
rewrite ?unsigned_lit_small by (unfold SB; lia); unfold SB;
first [ reflexivity
| lazymatch goal with |- _ = _ => lia | |- _ <= _ => lia | |- _ < _ => lia | |- _ <= _ < _ => lia | |- _ <= _ <= _ => lia | |- _ < _ <= _ => lia end
| idtac ].
Ltac img_factsF E :=
let H := rnHEI E in
repeat match goal with G : ew E 240%nat = _ |- _ => clear G | G : ew E 241%nat = _ |- _ => clear G | G : ew E 242%nat = _ |- _ => clear G
| G : ew E 271%nat = _ |- _ => clear G | G : ew E 272%nat = _ |- _ => clear G end;
let E240 := fresh "E240" in let E241 := fresh "E241" in let E242 := fresh "E242" in let E271 := fresh "E271" in let E272 := fresh "E272" in
pose proof (img_env_atomP E 240%nat H ltac:(unfold A_TEXT, A_LIM; lia)) as E240;
pose proof (img_env_atomP E 241%nat H ltac:(unfold A_TEXT, A_LIM; lia)) as E241;
pose proof (img_env_atomP E 242%nat H ltac:(unfold A_TEXT, A_LIM; lia)) as E242;
pose proof (img_env_atomP E 271%nat H ltac:(unfold A_TEXT, A_LIM; lia)) as E271;
pose proof (img_env_atomP E 272%nat H ltac:(unfold A_TEXT, A_LIM; lia)) as E272.
Ltac img_hull_factsF :=
let TL := rnTL in let TLF := rnTLF in
pose proof (pa_obj_img 1 ltac:(lia)) as Hob242; pose proof (pa_obj_img 0 ltac:(lia)) as Hob241;
pose proof (pa_obj_img 30 ltac:(lia)) as Hob271; pose proof (pa_obj_img 31 ltac:(lia)) as Hob272;
cbv [A_OBJ Nat.add] in Hob241, Hob242, Hob271, Hob272;
pose proof (palf_uar_img _ TL) as Huar; pose proof (palf_uar_al _ TLF) as Huar4.
Ltac fsb_lits := repeat match goal with
| |- context [fs_frame_bytes ?c / 8] => let v := eval vm_compute in (fs_frame_bytes c / 8) in
lazymatch v with Zpos _ => change (fs_frame_bytes c / 8) with v end
| |- context [fs_frame_bytes ?c] => let v := eval vm_compute in (fs_frame_bytes c) in
lazymatch v with Zpos _ => change (fs_frame_bytes c) with v end
end.
Ltac zconst_lits := repeat match goal with
| |- context [?s] => is_const s; lazymatch type of s with Z =>
let v := eval vm_compute in s in
lazymatch v with Zpos _ => change s with v | Zneg _ => change s with v | Z0 => change s with v end end
end.
Ltac awrF_rec_with hd AG fpos F EFA :=
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
unfold in_zr, shadow_addr; cbn [fst snd]; rewrite <- SB_SHADOW_OFF; fsb_lits; rewrite ?EFA; fold F; unfold SB; clear - Ha; lia
| ]
| |- awr_ok _ (YP09.mkRegion (Some 516%nat) _ _ _ _ _ :: _) _ _ _ _ _ _ ((?c, _) :: _) =>
eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 516%nat); [reflexivity | evalE AG | | ];
[ cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; right; right; right; exists c, fpos; split; [left; reflexivity|]; left;
unfold in_zr; cbn [fst snd]; fsb_lits; rewrite ?EFA; fold F; clear - Ha; lia
| ]
| |- awr_ok _ (YP09.mkRegion (Some 2%nat) _ _ _ _ _ :: _) _ _ _ _ _ _ _ =>
eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat 0); [reflexivity | evalE AG | clear; cbn; unfold ASTACK, ESTACK; zconst_lits; lia | clear; cbn; lia |]
| |- awr_ok _ (YP09.mkRegion (Some 60%nat) _ _ _ _ _ :: _) _ ?sp0 _ _ _ _ _ =>
lazymatch goal with Hsp1 : sp0 - _ <= ?sp1 <= sp0 - _ |- _ =>
eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 60%nat (sp1 - sp0)); [reflexivity | evalE AG | clear - Hsp1; cbn; unfold ASTACK, ESTACK; zconst_lits; lia | clear -Hsp1; cbn; lia |] end
end
| match goal with |- awr_ok _ (?r :: _) _ _ _ _ _ _ _ => idtac "AWR-HEAD" r end; fail 1 "awrFL: no rule for the head region" ];
awrF_rec_with hd AG fpos F EFA
end.
Ltac awrF_rec AG fpos F EFA := awrF_rec_with ltac:(idtac; fail) AG fpos F EFA.
Ltac awrFL_with hd AG fpos F EFA :=
lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fp b0 bc ly own) end;
awrF_rec_with hd AG fpos F EFA.
Ltac awrFL AG fpos F EFA := awrFL_with ltac:(idtac; fail) AG fpos F EFA.
Lemma land_m32 : forall x, 0 <= x < 2 ^ 64 -> Z.land x (2 ^ 64 - 32) = 32 * (x / 32).
Proof.
intros x Hx.
assert (E1 : 2 ^ 64 - 32 = Z.ldiff (Z.ones 64) (Z.ones 5)) by reflexivity. rewrite E1.
rewrite Z.ldiff_land, Z.land_assoc, <- Z.ldiff_land.
rewrite Z.land_ones, Z.mod_small by lia.
rewrite Z.ldiff_ones_r by lia. rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia. change (2 ^ 5) with 32. lia.
Qed.
Lemma denot_and_m32 : forall E n v c, ew E n = Z_to_bv 64 v -> 0 <= v + c -> v + c < 2 ^ 64 -> 0 <= v < 2 ^ 64 ->
sv_denot E (SAlu ALU_AND (SOff n c) (SLit (-32))) = Z_to_bv 64 (32 * ((v + c) / 32)).
Proof.
intros E n v c Hn H0 H1 Hv. rewrite denot_lit_U. f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit, (U_atom_off E n v c Hn) by lia.
change (zcanon (-32)) with (2 ^ 64 - 32). rewrite land_m32 by lia. apply zcanon_id. rewrite M64_val.
split; [apply Z.mul_nonneg_nonneg; [lia | apply Z.div_pos; lia]|].
pose proof (Z.mul_div_le (v + c) 32 ltac:(lia)). lia.
Qed.
Lemma sp1_facts : forall x, 0 <= x -> x mod 16 = 0 -> x - 16 <= 32 * (x / 32) <= x /\ (32 * (x / 32)) mod 32 = 0 /\ (32 * (x / 32)) mod 16 = 0.
Proof.
intros x Hx H16. pose proof (Z.div_mod x 32 ltac:(lia)) as D. pose proof (Z.mod_pos_bound x 32 ltac:(lia)) as M.
pose proof (Z.div_mod x 16 ltac:(lia)) as D16.
assert (x mod 32 = 0 \/ x mod 32 = 16) by lia.
split; [lia|]. split; [rewrite Z.mul_comm; apply Z_mod_mult|].
replace (32 * (x / 32)) with ((2 * (x / 32)) * 16) by lia. apply Z_mod_mult.
Qed.
Ltac rqs_goal := repeat (match goal with |- context [req_size ?n] =>
let v := eval vm_compute in (req_size n) in
lazymatch v with Zpos _ => change (req_size n) with v | Z0 => change (req_size n) with v end end).
Ltac rewrite_frame_addr := repeat match goal with H : forall c p, frame_addr ?l3 c p = frame_addr ?l c p |- context [frame_addr ?l3 _ _] => rewrite H end;
repeat match goal with F := frame_addr _ _ _ |- _ => fold F end.
Ltac keptFL_with hd HK HJx AG Kg Kg2 Kc Kc2 Kgu Kgu2 Ku Ku2 ErT PrT :=
first [ hd |
lazymatch goal with
| |- region_kept _ _ _ _ (YP09.mkRegion (Some 2%nat) _ _ _ _ _) =>
eapply (region_kept_stack_aj _ _); [exact HK | exact HJx | evalE AG | unfold ESTACK, ASTACK; zconst_lits; lia | unfold ESTACK, ASTACK; zconst_lits; lia | lia | lia | lia]
| |- region_kept _ _ _ _ (YP09.mkRegion (Some 60%nat) _ _ _ _ _) =>
eapply (region_kept_stack_aj _ _); [exact HK | exact HJx | evalE AG | unfold ESTACK, ASTACK; zconst_lits; lia | unfold ESTACK, ASTACK; zconst_lits; lia | lia | lia | lia]
| |- region_kept _ ?Ex _ _ (YP09.mkRegion (Some 242%nat) _ _ _ _ _) =>
let H := rnHEI Ex in apply (region_kept_val_at Ex _ _ (A_OBJ 1) (pa_val (A_OBJ 1)) 8 (pa_val (A_OBJ 30)));
[exact (H (A_OBJ 1) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact Kg | exact Kg2 | lia]
| |- region_kept _ ?Ex _ _ (YP09.mkRegion (Some 271%nat) _ _ _ _ _) =>
let H := rnHEI Ex in apply (region_kept_val_at Ex _ _ (A_OBJ 30) (pa_val (A_OBJ 30)) 8 SHADOW_OFF);
[exact (H (A_OBJ 30) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact Kc | exact Kc2 | lia]
| |- region_kept _ ?Ex _ _ (YP09.mkRegion (Some 241%nat) _ _ _ _ _) =>
let H := rnHEI Ex in let Bv := rnB in apply (region_kept_val_at Ex _ _ (A_OBJ 0) (pa_val (A_OBJ 0)) 8 (as_uar_cell Bv));
[exact (H (A_OBJ 0) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact Kgu | exact Kgu2 | lia]
| |- region_kept _ ?Ex _ _ (YP09.mkRegion (Some 272%nat) _ _ _ _ _) =>
let H := rnHEI Ex in let Bv := rnB in let TL := rnTL in apply (region_kept_val_at Ex _ _ (A_OBJ 31) (as_uar_cell Bv) 4 1);
[rewrite (pal_uar_cell _ TL); exact (H (A_OBJ 31) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact Ku | exact Ku2 | lia]
| |- region_kept _ _ _ _ (YP09.mkRegion (Some 516%nat) _ _ _ _ _) =>
eapply (region_kept_ownframe_aj _ _); [exact HK | evalE AG | eassumption
| left; rewrite_frame_addr; fsb_lits; lia | intros a Ha; cbn beta; first [exact (fun Hn : False => Hn) | ErT] | intros a Ha; PrT ]
| |- region_kept _ _ _ _ (YP09.mkRegion (Some 529%nat) _ _ _ _ _) =>
eapply (region_kept_ownframe_aj _ _); [exact HK | evalE AG | eassumption
| right; rewrite_frame_addr; unfold shadow_addr; rewrite <- SB_SHADOW_OFF; fsb_lits; unfold SB; lia
| intros a Ha; cbn beta; first [exact (fun Hn : False => Hn) | ErT] | intros a Ha; first [lia | PrT] ]
| |- region_kept _ _ _ _ (YP09.mkRegion (Some ?n) _ _ ?wlo ?whi _) =>
lazymatch goal with Hb : ew _ n = Z_to_bv 64 ?b |- _ =>
let L := rnLAWS in
first
[
lazymatch (eval vm_compute in (Z.leb whi wlo)) with true =>
first [ eapply (region_kept_block_aj _ _ _ _ _ _ _ _ _ _ _ _ n _ _ _ _ _ b); [exact HK | evalE AG | eassumption | lia | rqs_goal; lia | lia | intros a Ha Hn; first [exact Hn | ErT] ]
| eapply (region_kept_frame_aj _ _ _ _ _ _ _ _ _ _ _ _ n _ _ _ _ _ b); [exact HK | evalE AG | eassumption | rewrite_frame_addr; lia | rewrite_frame_addr; lia | lia | intros a Ha Hn; first [exact Hn | ErT] ] ] end
|
eapply (region_kept_block_ajw2 _ _ L _ _ _ _ _ _ _ _ _ _ n _ _ _ _ _ b); [exact HK | exact (proj1 HJx) | eassumption | evalE AG | eassumption | lia | rqs_goal; lia | lia | lia | intros a Ha Hn; first [exact Hn | ErT] ]
| match goal with |- ?g => idtac "KEPTFL-FAIL" g end; fail ] end
end ].
Ltac keptFL HK HJx AG Kg Kg2 Kc Kc2 Kgu Kgu2 Ku Ku2 ErT PrT := keptFL_with ltac:(idtac; fail) HK HJx AG Kg Kg2 Kc Kc2 Kgu Kgu2 Ku Ku2 ErT PrT.
Ltac upd_aboveW_init HFr AG HUP :=
lazymatch type of HFr with frame_of ?Ef ?rs (mrestrict (w_H ?Wx) ?m0) (mrestrict _ (ms_mem ?msX)) =>
lazymatch goal with Usp : bv_unsigned (ew _ 2) = spZ ?regs |- _ =>
assert (HUP : forall a, spZ regs <= a < 2 ^ 64 -> aview pa_segs (w_H Wx) (ms_mem msX) a = aview pa_segs (w_H Wx) m0 a);
[ eapply (aview_kept_frame Ef rs _ _ _ (spZ regs) HFr); [lia|];
let a := fresh "a" in let Ha := fresh "Ha" in let rg := fresh "rg" in let Hin := fresh "Hin" in let Hrg := fresh "Hrg" in
intros a Ha (rg & Hin & Hrg);
lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In rg rs1) in Hin end; cbn [In] in Hin;
repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrg; revert Hrg; evalE AG; intros Hrg; lia|]);
destruct Hin
| ] end end.
Ltac aconstsF HJx Kgot Kcell Kguar Kuar :=
let L := rnLAWS in let TL := rnTL in
let Kc := fresh "Kc" in let Ku := fresh "Ku" in let Kg := fresh "Kg" in let Kgu := fresh "Kgu" in
destruct (al_const _ _ L _ _ _ _ _ (proj1 HJx)) as (Kc & Ku & Kg & Kgu);
rewrite (pal_got_shadow _ TL), (pal_cell _ TL) in Kg; rewrite (pal_cell _ TL) in Kc;
rewrite (palf_got_uar _ TL) in Kgu;
pose proof (val_mem_of_rdword _ _ _ _ _ Kg) as Kgot; pose proof (val_mem_of_rdword _ _ _ _ _ Kc) as Kcell;
pose proof (val_mem_of_rdword _ _ _ _ _ Kgu) as Kguar; pose proof (val_mem_of_rd32 _ _ _ _ _ Ku) as Kuar;
clear Kc Ku Kg Kgu.
Ltac fs_roF HS :=
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs 529%nat in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rs got_regionP) in
let HS3 := fresh "HS3" in
pose proof (ast_ok_pi_set_region Ex ssx msx i r (set_window r 0 0) HS ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity)
(region_ok_rewindow _ Ex _ r 0 0 (st_ok_pi_region_nth Ex ssx msx i r HS ltac:(vm_compute; reflexivity)) ltac:(intros o Ho; lia))) as HS3;
clear HS; rename HS3 into HS; norm_ss HS | st_ok _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs 529%nat in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rs got_regionP) in
let HS3 := fresh "HS3" in
pose proof (ast_ok_set_region _ Ex ssx msx i r (set_window r 0 0) HS ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity)
(region_ok_rewindow _ Ex _ r 0 0 (st_ok_region_nth Ex ssx msx i r HS ltac:(vm_compute; reflexivity)) ltac:(intros o Ho; lia))) as HS3;
clear HS; rename HS3 into HS; norm_ss HS  end.
Ltac fs_rwF HS E529 Hp :=
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs 529%nat in let i := eval vm_compute in i in
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
let i := idx_of_base rs 529%nat in let i := eval vm_compute in i in
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
Lemma chunk_ok_redenote : forall segs E m base off w e e',
sv_denot E e' = sv_denot E e -> YP09.chunk_ok segs E m base (YP09.mkChunk off (CVal w e)) -> YP09.chunk_ok segs E m base (YP09.mkChunk off (CVal w e')).
Proof. intros segs E m base off w e e' He H i Hi. cbn [YP09.c_off YP09.c_val YP09.c_len cbyte] in *. rewrite He. exact (H i Hi). Qed.
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
Ltac idx_of_off cs off :=
lazymatch cs with
| YP09.mkChunk off _ :: _ => constr:(0%nat)
| _ :: ?tl => let i := idx_of_off tl off in constr:(S i)
end.
Ltac hc_bool H tac :=
rewrite ?branch_eq_U, ?branch_ne_U, ?branch_ltu_U, ?branch_geu_U in H;
rewrite ?U_and_lit in H by lia; tac H; rewrite ?U_lit in H by lia;
try (apply (proj1 (negb_true_iff _)) in H); try (apply (proj1 (negb_false_iff _)) in H).
Ltac hc_prop H :=
first [ apply (proj1 (Z.eqb_eq _ _)) in H | apply (proj1 (Z.eqb_neq _ _)) in H
| apply (proj1 (Z.ltb_lt _ _)) in H | apply (proj1 (Z.ltb_ge _ _)) in H | idtac ].
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
Ltac oblG HJx E10n E32n Hing := obl_blk HJx E10n E32n Hing.
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
Lemma land_m4 : forall x, 0 <= x < 2 ^ 64 -> Z.land x (2 ^ 64 - 4) = 4 * (x / 4).
Proof.
intros x Hx. assert (E1 : 2 ^ 64 - 4 = Z.ldiff (Z.ones 64) (Z.ones 2)) by reflexivity. rewrite E1.
rewrite Z.ldiff_land, Z.land_assoc, <- Z.ldiff_land. rewrite Z.land_ones, Z.mod_small by lia.
rewrite Z.ldiff_ones_r by lia. rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4. lia.
Qed.
Lemma land_m2 : forall x, 0 <= x < 2 ^ 64 -> Z.land x (2 ^ 64 - 2) = 2 * (x / 2).
Proof.
intros x Hx. assert (E1 : 2 ^ 64 - 2 = Z.ldiff (Z.ones 64) (Z.ones 1)) by reflexivity. rewrite E1.
rewrite Z.ldiff_land, Z.land_assoc, <- Z.ldiff_land. rewrite Z.land_ones, Z.mod_small by lia.
rewrite Z.ldiff_ones_r by lia. rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2. lia.
Qed.
Lemma U_and_m4 : forall E a, U E (SAlu ALU_AND a (SLit (-4))) = 4 * (U E a / 4).
Proof. intros E a. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit. change (zcanon (-4)) with (2 ^ 64 - 4). pose proof (U_range E a). rewrite land_m4 by (rewrite <- M64_val; lia). apply zcanon_id. rewrite M64_val in *. pose proof (Z.mul_div_le (U E a) 4 ltac:(lia)). split; [apply Z.mul_nonneg_nonneg; [lia | apply Z.div_pos; lia] | lia]. Qed.
Lemma U_and_m2 : forall E a, U E (SAlu ALU_AND a (SLit (-2))) = 2 * (U E a / 2).
Proof. intros E a. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit. change (zcanon (-2)) with (2 ^ 64 - 2). pose proof (U_range E a). rewrite land_m2 by (rewrite <- M64_val; lia). apply zcanon_id. rewrite M64_val in *. pose proof (Z.mul_div_le (U E a) 2 ltac:(lia)). split; [apply Z.mul_nonneg_nonneg; [lia | apply Z.div_pos; lia] | lia]. Qed.
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
Lemma sv_denot_SOff0 : forall E n, sv_denot E (SOff n 0) = ew E n.
Proof. intros E n. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. Qed.
Lemma zcanon_01 : forall b : bool, zcanon (if b then 1 else 0) = (if b then 1 else 0).
Proof. intros b. apply zcanon_id. rewrite M64_val. destruct b; lia. Qed.
Lemma U_front_isfirst : forall E y, U E (SAlu ALU_AND (SAlu ALU_OR (SAlu ALU_SLTU (SOff 12 0) (SLit 1)) (SAlu ALU_SLTU (SLit 0) y)) (SLit 1)) = 0 -> U E (SOff 12 0) <> 0.
Proof.
intros E y H. rewrite U_and_lit in H by lia. rewrite U_SAlu in H. cbn [zalu_raw] in H.
rewrite !U_SAlu in H. cbn [zalu_raw] in H. rewrite !U_SLit in H. rewrite (zcanon_id 1), (zcanon_id 0) in H by (rewrite M64_val; lia).
rewrite !zcanon_01 in H.
destruct (U E (SOff 12 0) <? 1) eqn:Q; destruct (0 <? U E y); vm_compute in H; try discriminate H; apply Z.ltb_ge in Q; lia.
Qed.
Lemma clr2_rng : forall x, 0 <= x -> 0 <= 2 * (x / 2) <= x.
Proof. intros x Hx. pose proof (Z.mul_div_le x 2 ltac:(lia)). pose proof (Z.div_pos x 2 Hx ltac:(lia)). lia. Qed.
Lemma clr4_rng : forall x, 0 <= x -> 0 <= 4 * (x / 4) <= x.
Proof. intros x Hx. pose proof (Z.mul_div_le x 4 ltac:(lia)). pose proof (Z.div_pos x 4 Hx ltac:(lia)). lia. Qed.
Lemma clr42 : forall x, 0 <= x -> 2 * (4 * (x / 4) / 2) = 4 * (x / 4).
Proof. intros x Hx. replace (4 * (x / 4)) with ((2 * (x / 4)) * 2) by lia. rewrite Z.div_mul by lia. lia. Qed.
