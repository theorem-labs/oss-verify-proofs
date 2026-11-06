(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/ACkc.v and lib/A/ACja.v, the
   walk-tactic kit of cgif's ASan program walks, over fuzz_command's listing: module paths, csym; the image-class
   section is over any listing (PAImg L) instead of cgif's. One copy of each name ACkc.v and ACja.v both define;
   evalE is ACja.v's (ACj1.v's) final form. Also copied: boxed, box and unbox from lib/A/ACj1.v, relowF from
   lib/A/ACjb.v. fuzz_command's PaDenot.v has YC4b.v's norm_ss and reshok_bx, which match st_ok only; ACkc.v ran on
   lib/A/ACjr.v's, which also match st_ok_pi: they are here as norm_ss_pi and reshok_bx_pi, and the copied tactics
   call them. Dropped: awrF_rec's rule for cgif's Frame block (atom 11, FRAME_SIZE); the names TFLUSH_STK,
   TRAWADD_STK and LZW_TSTK from the unfold lists of awrF_rec and keptFL (awrFL computes the stack size of its goal
   instead, and keptFL the stack size of its ajournal hypothesis, by stk_lit); the RO (ro_below_ofl) context, which
   no lemma used. Changed: fuzz_command's awr_ok (lib/Reusable/YCbq.v) takes segs, B and an fr0 list that cgif's
   does not, and its awr_byte has a fifth case, so awrF_rec's and awrFL's patterns and lemma arguments have three
   more places and the frame rules pick the fourth case (in_frames) with right; right; right; left. The frame rules
   of awrF_rec and keptFL (atoms 516 and 529) take the frame class from the goal (the head of the owned-frame
   list, or the frames hypothesis) and compute its frame size by ffb_goal, where cgif's wrote class 2 and 256 / 32
   bytes; awrF_rec's rule for atom 60 takes any bounds sp0 - x <= sp1 <= sp0 - y, where cgif's wrote 400 and 384;
   upd_aboveW_init takes the segment list from the world's type, where ACja.v let typeclass search find pa_segs;
   add_atom's st_ok arm uses st_ok_havoc_hi (new here), where ACja.v used the st_ok_pi lemma, which does not apply
   to an st_ok hypothesis. *)
(* Modified by Theorem Labs, 2026-10: copied from lib/A/Prog/PaWalk.v for fuzz_command.asan-ubsan: module paths;
   sp1_facts, land_m32 and denot_and_m32 are gone for the kit's CmdSnText.snt_sp1_facts, snt_land_m32 and
   snt_denot_and_m32 (the same statements). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0n YI0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaStep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YO0f.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaRun PaShadow CmdSyms CmdList CmdPa PaJournal.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdPaLib PaLibG PaLibH PaSB PaDenot PaLibF.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Definition chunk_in (lo hi : Z) (c : YP09.chunk) : bool :=
Z.leb lo (YP09.c_off c) && Z.leb (YP09.c_off c + YP09.c_len c) hi.
Ltac rnLAWS := lazymatch goal with L : AR_laws _ _ |- _ => L end.
Ltac rnTL := lazymatch goal with T : PALib _ |- _ => T end.
Ltac rnB := lazymatch goal with L : AR_laws _ ?Bv |- _ => Bv end.
Ltac rnTLF := lazymatch goal with T : PALibF _ |- _ => T end.
Ltac rnFFL := lazymatch goal with H : frame_flag_lawP _ _ |- _ => H end.
Ltac rnHEI E := lazymatch goal with H : img_env _ _ E |- _ => H | _ => fail "rnHEI: no img_env fact for" E end.
Ltac hei_pose Eo kk ws :=
let Ho := rnHEI Eo in let H := fresh "HEIh" in
first [ pose proof (img_env_havoc_hi Eo kk ws Ho ltac:(cbv; lia)) as H | pose proof (img_env_havoc Eo kk ws Ho ltac:(cbv; lia)) as H ].
Ltac hei_havoc HS :=
lazymatch type of HS with
| st_ok_pi _ _ (havoc ?Eo ?kk ?ws) _ _ => first [ let H0 := rnHEI constr:(havoc Eo kk ws) in idtac | hei_pose Eo kk ws ]
| _ => idtac end.
Ltac nat_side := first [ apply (proj1 (PeanoNat.Nat.ltb_lt _ _)); vm_compute; reflexivity
| apply (proj1 (PeanoNat.Nat.eqb_neq _ _)); vm_compute; reflexivity
| apply (proj1 (PeanoNat.Nat.leb_le _ _)); vm_compute; reflexivity ].
Ltac evalE AG :=
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
Ltac idx_of_base rs n :=
lazymatch rs with
| YP09.mkRegion (Some n) _ _ _ _ _ :: _ => constr:(0%nat)
| _ :: ?tl => let i := idx_of_base tl n in constr:(S i)
end.
Ltac idx_of_off cs off :=
lazymatch cs with
| YP09.mkChunk off _ :: _ => constr:(0%nat)
| _ :: ?tl => let i := idx_of_off tl off in constr:(S i)
end.
Ltac incl_lit_tac :=
let x := fresh "x" in let Hx := fresh "Hx" in
intros x Hx; cbn in Hx; cbn;
repeat (destruct Hx as [<- | Hx]; [repeat (first [left; reflexivity | right]) |]); destruct Hx.
Ltac norm_ss_pi HS := lazymatch type of HS with st_ok_pi _ _ _ ?ss3 _ => let v := eval vm_compute in ss3 in change ss3 with v in HS | st_ok _ _ ?ss3 _ => let v := eval vm_compute in ss3 in change ss3 with v in HS end.
Ltac reshok_bx_pi HS bx :=
try match goal with H : sh_ok _ _ _ _ _ |- _ => clear H end;
lazymatch type of HS with st_ok_pi _ _ ?Ex _ (restrict (w_H ?Wx) ?msx) =>
let SH := fresh "SHOK" in
shok_auto SH (SOff bx 0) Ex (mrestrict (w_H Wx) (ms_mem msx)) | st_ok _ ?Ex _ (restrict (w_H ?Wx) ?msx) =>
let SH := fresh "SHOK" in
shok_auto SH (SOff bx 0) Ex (mrestrict (w_H Wx) (ms_mem msx)) end.
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
clear HS Hv; rename HS3 into HS; norm_ss_pi HS; set_regs_rec HS N vals (S i) rl' | st_ok _ ?Ev ?ssx ?msx =>
let HS3 := fresh "HS3" in let Hv := fresh "Hv" in
let n := eval vm_compute in (N + i)%nat in
assert (Hv : sv_denot Ev (SOff n 0) = getr (ms_regs msx) r);
[ cbn [sv_denot]; rewrite Z.add_0_r; rewrite Z_to_bv_bv_unsigned; change n with (N + i)%nat;
rewrite (ew_havoc_new _ N vals i (Z_to_bv 64 0)) by (cbn [length]; lia); cbn [nth ms_regs restrict]; reflexivity | ];
pose proof (ast_ok_set_reg_fp _ Ev ssx msx r (SOff n 0) HS ltac:(vm_compute; reflexivity) Hv) as HS3;
clear HS Hv; rename HS3 into HS; norm_ss_pi HS; set_regs_rec HS N vals (S i) rl'  end
end.
Ltac creg HS AG EE :=
lazymatch goal with |- getr _ ?r = getr _ _ =>
let R := fresh "R" in prreg HS r R; rewrite R; clear R;
cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite AG by lia;
apply EE; reflexivity end.
Ltac clear_frames := repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
Ltac subregion_tac :=
unfold subregion; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks];
split; [reflexivity|]; split; [lia|]; split; [lia|]; split; [lia|];
let c := fresh "c" in let Hc := fresh "Hc" in intros c Hc; cbn in Hc |- *;
first [exact Hc | solve [destruct Hc] | tauto].
Ltac submem_to := repeat (first [apply submem_keep; [subregion_tac|] | apply submem_drop]); apply submem_nil.
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
Ltac obl_blk HJx HEn HEbx Hin :=
let L := rnLAWS in
lazymatch goal with |- range_addressable _ (U ?Ex (SOff ?bx 0)) (U _ (SOff ?n ?c)) ?len =>
lazymatch type of HEn with _ = Z_to_bv 64 ?p =>
lazymatch type of Hin with In (_, ?sz) _ =>
first [ rewrite (U_atom_off Ex n p c); [| cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact HEn | lia | lia]
| rewrite (U_atom Ex n p); [| cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact HEn | lia] ];
eapply (obl_of_block _ _ L _ _ _ _ _ Ex (SOff bx 0) _ len p sz (proj1 HJx) Hin);
[ rewrite (U_atom Ex bx SB); [reflexivity | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact HEbx | unfold SB; lia]
| lia | let v := eval vm_compute in (req_size sz) in change (req_size sz) with v; lia ] end end end.
Fixpoint list_set {A} (l : list A) (i : nat) (x : A) : list A :=
match l, i with [], _ => [] | _ :: t, O => x :: t | h :: t, S j => h :: list_set t j x end.
Definition ss_set_reg (s : sstate) (r : nat) (e : sv) : sstate := mkSS (ss_pc s) (list_set (ss_regs s) r e) (ss_mem s) (ss_resv s) (ss_facts s).
Definition ss_set_pc (s : sstate) (pc : Z) : sstate := mkSS pc (ss_regs s) (ss_mem s) (ss_resv s) (ss_facts s).
Fixpoint ss_set_regs (s : sstate) (l : list (nat * sv)) : sstate :=
match l with [] => s | (r, e) :: t => ss_set_regs (ss_set_reg s r e) t end.
Definition ss_set_mem (s : sstate) (m : smem) : sstate := mkSS (ss_pc s) (ss_regs s) m (ss_resv s) (ss_facts s).
Definition ss_set_facts (s : sstate) (fa : list (nat * afact)) : sstate :=
mkSS (ss_pc s) (ss_regs s) (ss_mem s) (ss_resv s) (mkFacts fa (f_conds (ss_facts s)) (f_alias (ss_facts s))).
Fixpoint ss_havoc_regs (s : sstate) (N : nat) (deads : list nat) : sstate :=
match deads with [] => s | r :: t => ss_havoc_regs (ss_set_reg s r (SOff N 0)) (S N) t end.
Ltac rreg_by HS r v pf H :=
lazymatch type of HS with st_ok_pi _ ?segs ?Ex ?ss (restrict ?Hh ?ms) =>
let e := eval vm_compute in (sr_get (ss_regs ss) r) in
let rg := eval cbn [ms_regs restrict mkst] in (ms_regs ms) in
assert (H : getr rg r = v) by (refine (eq_trans (st_ok_restrict_reg _ Hh Ex _ ms r HS) _); change (sv_denot Ex e = v); exact pf) | st_ok ?segs ?Ex ?ss (restrict ?Hh ?ms) =>
let e := eval vm_compute in (sr_get (ss_regs ss) r) in
let rg := eval cbn [ms_regs restrict mkst] in (ms_regs ms) in
assert (H : getr rg r = v) by (refine (eq_trans (st_ok_restrict_reg segs Hh Ex ss ms r HS) _); change (sv_denot Ex e = v); exact pf)  end.
Ltac upd_aboveW HUP HFr AG :=
let HUP' := fresh "HUP" in
lazymatch type of HFr with frame_of ?Ef ?rs (mrestrict _ ?m0) (mrestrict _ (ms_mem ?msX)) =>
lazymatch type of HUP with forall a, ?lo <= a < _ -> aview ?sg ?Hh _ a = aview _ ?Hw ?me a =>
assert (HUP' : forall a, lo <= a < 2 ^ 64 -> aview sg Hh (ms_mem msX) a = aview sg Hw me a);
[ let a := fresh "a" in let Ha := fresh "Ha" in
intros a Ha; rewrite <- (HUP a Ha); eapply (aview_kept_frame Ef rs _ _ _ lo HFr); [lia| |exact Ha];
let b := fresh "b" in let Hb := fresh "Hb" in let rg := fresh "rg" in let Hin := fresh "Hin" in let Hrg := fresh "Hrg" in
intros b Hb (rg & Hin & Hrg);
lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In rg rs1) in Hin end; cbn [In] in Hin;
repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrg; revert Hrg; evalE AG; intros Hrg; lia|]);
destruct Hin
| clear HUP; rename HUP' into HUP ] end end.
Definition trim_region (r : YP09.region) (lo hi : Z) : YP09.region :=
YP09.mkRegion (YP09.r_base r) lo hi (Z.max (YP09.r_wlo r) lo) (Z.min (YP09.r_whi r) hi)
(filter (chunk_in lo hi) (YP09.r_chunks r)).
Fixpoint trim_stack (rs : smem) (lo hi : Z) : smem :=
match rs with
| [] => []
| r :: t => match YP09.r_base r with
| Some 2%nat => trim_region r lo hi :: t
| _ => r :: trim_stack t lo hi end end.
Lemma sv_denot_SOff0 : forall E n, sv_denot E (SOff n 0) = ew E n.
Proof. intros E n. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. Qed.
Ltac aconstsF HJx Kgot Kcell Kguar Kuar :=
let L := rnLAWS in let TL := rnTL in
let Kc := fresh "Kc" in let Ku := fresh "Ku" in let Kg := fresh "Kg" in let Kgu := fresh "Kgu" in
destruct (al_const _ _ L _ _ _ _ _ (proj1 HJx)) as (Kc & Ku & Kg & Kgu);
let TLF := rnTLF in
rewrite (pal_got_shadow _ TL), (pal_cell _ TL) in Kg; rewrite (pal_cell _ TL) in Kc;
rewrite (palf_got_uar _ TLF) in Kgu;
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
clear HS; rename HS3 into HS; norm_ss_pi HS | st_ok _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs 529%nat in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rs got_regionP) in
let HS3 := fresh "HS3" in
pose proof (ast_ok_set_region _ Ex ssx msx i r (set_window r 0 0) HS ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity)
(region_ok_rewindow _ Ex _ r 0 0 (st_ok_region_nth Ex ssx msx i r HS ltac:(vm_compute; reflexivity)) ltac:(intros o Ho; lia))) as HS3;
clear HS; rename HS3 into HS; norm_ss_pi HS  end.
Ltac fs_rwF HS E529 Hp :=
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
clear HS; rename HS3 into HS; norm_ss_pi HS | st_ok _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs 529%nat in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rs got_regionP) in
let HS3 := fresh "HS3" in
pose proof (ast_ok_set_region _ Ex ssx msx i r (set_window r 0 32) HS ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity)
(region_ok_rewindow _ Ex _ r 0 32 (st_ok_region_nth Ex ssx msx i r HS ltac:(vm_compute; reflexivity))
ltac:(cbn [YP09.r_base base_val ms_mem restrict mkst]; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia;
rewrite E529, unsigned_lit_small by (unfold SB; lia);
intros o Ho; apply (apresent_writable _); unfold shadow_addr in Hp; rewrite <- SB_SHADOW_OFF in Hp;
apply (proj1 (Hp o ltac:(clear - Ho; lia)))))) as HS3;
clear HS; rename HS3 into HS; norm_ss_pi HS  end.
Ltac hc_bool H tac :=
rewrite ?branch_eq_U, ?branch_ne_U, ?branch_ltu_U, ?branch_geu_U in H;
rewrite ?U_and_lit in H by lia; tac H; rewrite ?U_lit in H by lia;
try (apply (proj1 (negb_true_iff _)) in H); try (apply (proj1 (negb_false_iff _)) in H).
Ltac hc_prop H :=
first [ apply (proj1 (Z.eqb_eq _ _)) in H | apply (proj1 (Z.eqb_neq _ _)) in H
| apply (proj1 (Z.ltb_lt _ _)) in H | apply (proj1 (Z.ltb_ge _ _)) in H | idtac ].
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
clear HS; rename HS3 into HS; norm_ss_pi HS end | st_ok _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (ss_mem ssx) in
let r := eval vm_compute in (nth i rs got_regionP) in
lazymatch (eval vm_compute in (nth_error (YP09.r_chunks r) j)) with Some (YP09.mkChunk ?off (CVal ?w ?e)) =>
let r' := eval vm_compute in (YP09.mkRegion (YP09.r_base r) (YP09.r_lo r) (YP09.r_hi r) (YP09.r_wlo r) (YP09.r_whi r)
(list_upd (YP09.r_chunks r) j (YP09.mkChunk off (CVal w e')))) in
let HS3 := fresh "HS3" in
pose proof (ast_ok_set_region _ Ex ssx msx i r r' HS ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity)
(region_ok_rechunk _ Ex _ r j off w e e' (st_ok_region_nth Ex ssx msx i r HS ltac:(vm_compute; reflexivity)) ltac:(vm_compute; reflexivity) ltac:(tac))) as HS3;
clear HS; rename HS3 into HS; norm_ss_pi HS end  end.
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
Ltac rqs_goal := repeat (match goal with |- context [req_size ?n] =>
let v := eval vm_compute in (req_size n) in
lazymatch v with Zpos _ => change (req_size n) with v | Z0 => change (req_size n) with v end end).
Ltac rewrite_frame_addr := repeat match goal with H : forall c p, frame_addr ?l3 c p = frame_addr ?l c p |- context [frame_addr ?l3 _ _] => rewrite H end;
repeat match goal with F := frame_addr _ _ _ |- _ => fold F end.
Ltac upd_aboveW_init HFr AG HUP :=
lazymatch type of HFr with frame_of ?Ef ?rs (mrestrict (w_H ?Wx) ?m0) (mrestrict _ (ms_mem ?msX)) =>
let sg := lazymatch type of Wx with world ?s => s end in
lazymatch goal with Usp : bv_unsigned (ew _ 2) = spZ ?regs |- _ =>
assert (HUP : forall a, spZ regs <= a < 2 ^ 64 -> aview sg (w_H Wx) (ms_mem msX) a = aview sg (w_H Wx) m0 a);
[ eapply (aview_kept_frame Ef rs _ _ _ (spZ regs) HFr); [lia|];
let a := fresh "a" in let Ha := fresh "Ha" in let rg := fresh "rg" in let Hin := fresh "Hin" in let Hrg := fresh "Hrg" in
intros a Ha (rg & Hin & Hrg);
lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In rg rs1) in Hin end; cbn [In] in Hin;
repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrg; revert Hrg; evalE AG; intros Hrg; lia|]);
destruct Hin
| ] end end.
Lemma denot_atom_mod : forall E n v M, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
(bv_unsigned (Z_to_bv 64 (bv_unsigned (ew E n) + 0))) mod M = v mod M.
Proof. intros E n v M Hn Hv. rewrite Hn, Z.add_0_r, !unsigned_lit_small by (rewrite ?unsigned_lit_small by lia; lia). reflexivity. Qed.
Lemma val_mem_mod : forall segs (m : word -> option byte) a n v,
val_mem segs m a n (v mod 2 ^ (8 * Z.of_nat n)) <-> val_mem segs m a n v.
Proof.
intros segs m a n v. unfold val_mem, YO0f.le_byte.
assert (E : (v mod 2 ^ (8 * Z.of_nat n)) mod 2 ^ (8 * Z.of_nat n) = v mod 2 ^ (8 * Z.of_nat n)).
{ apply Z.mod_mod. apply Z.pow_nonzero; lia. }
rewrite E. tauto.
Qed.
Ltac upd_aboveF HUP HFr AG ltac :=
let HUP' := fresh "HUP" in
lazymatch type of HFr with frame_of ?Ef ?rs (mrestrict _ ?m0) (mrestrict _ (ms_mem ?msX)) =>
lazymatch type of HUP with forall a, ?lo <= a < _ -> aview ?sg ?Hh _ a = aview _ ?Hw ?me a =>
assert (HUP' : forall a, lo <= a < 2 ^ 64 -> aview sg Hh (ms_mem msX) a = aview sg Hw me a);
[ let a := fresh "a" in let Ha := fresh "Ha" in
intros a Ha; rewrite <- (HUP a Ha); eapply (aview_kept_frame Ef rs _ _ _ lo HFr); [lia| |exact Ha];
let b := fresh "b" in let Hb := fresh "Hb" in let rg := fresh "rg" in let Hin := fresh "Hin" in let Hrg := fresh "Hrg" in
intros b Hb (rg & Hin & Hrg);
lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In rg rs1) in Hin end; cbn [In] in Hin;
repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrg; revert Hrg; evalE AG; intros Hrg; ltac Hb Hrg|]);
destruct Hin
| clear HUP; rename HUP' into HUP ] end end.
Lemma zero_shadow_of_bytes : forall (rd : Z -> option Z) a len,
a mod 8 = 0 -> len mod 8 = 0 -> 0 <= len ->
(forall i, 0 <= i < len / 8 -> rd (SHADOW_OFF + a / 8 + i) = Some 0) ->
range_addressable rd SHADOW_OFF a len.
Proof.
intros rd a len Ha Hl Hlen Hz. apply zero_shadow_range; [exact Ha | exact Hl |].
intros i Hi. unfold shadow_of_addr. apply Hz. exact Hi.
Qed.
Ltac reshok HS := reshok_bx_pi HS 32%nat.
Ltac eimg_low := rewrite ?Eimg_low by (unfold A_TEXT; lia).
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {L : ptable csym} {PI : PAImg L}.
#[local] Notation SEGS := (pa_segs).
#[local] Notation VAL := (pa_val).
Lemma st_ok_pin_rege0 : forall E ss ms (r : bv 5) e,
st_ok SEGS E ss ms -> r <> 0%bv -> sv_denot E e = getr (ms_regs ms) r ->
st_ok SEGS E (mkSS (ss_pc ss) (sr_set (ss_regs ss) r e) (ss_mem ss) (ss_resv ss) (ss_facts ss)) ms.
Proof.
intros E ss ms r e HS Hr He.
apply (st_ok_regs SEGS E ss ms (sr_set (ss_regs ss) r e)); [exact HS|].
intros x. destruct (base.decide (x = r)) as [->|Hne].
- rewrite sr_get_set_same; [| destruct (bv_eqb r 0) eqn:Hb; [apply bv_eqb_eq in Hb; congruence | reflexivity]].
rewrite He. exact (st_ok_reg SEGS E ss ms r HS).
- rewrite sr_get_set_other by exact Hne. reflexivity.
Qed.
Lemma st_ok_pin_rege : forall E ss ms (r : bv 5) e,
st_ok_pi SEGS VAL E ss ms -> r <> 0%bv -> sv_denot E e = getr (ms_regs ms) r ->
st_ok_pi SEGS VAL E (mkSS (ss_pc ss) (sr_set (ss_regs ss) r e) (ss_mem ss) (ss_resv ss) (ss_facts ss)) ms.
Proof.
intros E ss ms r e HS Hr He. destruct ss as [pc0 sr0 fr0 sm0 rv0 fs0]. exact (st_ok_pin_rege0 E _ ms r e HS Hr He).
Qed.
Section g.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Lemma sep_tmp_entry : forall ly3 S3 W3 m3 md3 (entry : list (Z * Z)) pt n b m,
AR SEGS B ly3 S3 W3 m3 md3 -> Permutation (ablocks B ly3 S3) (entry ++ [(pt, n)]) -> In (b, m) entry ->
b + req_size m <= pt \/ pt + req_size n <= b.
Proof.
intros ly3 S3 W3 m3 md3 entry pt n b m HAR HP Hin.
apply in_split in Hin as (l1 & l2 & El). rewrite El in HP.
assert (HP2 : Permutation (ablocks B ly3 S3) ((pt, n) :: (b, m) :: l1 ++ l2)).
{ eapply Permutation_trans; [exact HP|]. eapply Permutation_trans; [apply Permutation_app_comm|]. cbn [app]. apply perm_skip.
apply Permutation_sym. apply Permutation_middle. }
pose proof (sep_blocks_perm SEGS B LAWS _ _ _ _ _ _ _ _ HAR HP2) as Hs. unfold zdisjoint, block_rng in Hs. cbn [fst snd] in Hs. lia.
Qed.
End g.
End f.
End d.
Ltac img_factsF E :=
let H := rnHEI E in
repeat match goal with G : ew E 240%nat = _ |- _ => clear G | G : ew E 241%nat = _ |- _ => clear G | G : ew E 242%nat = _ |- _ => clear G
| G : ew E 253%nat = _ |- _ => clear G end;
let E240 := fresh "E240" in let E241 := fresh "E241" in let E242 := fresh "E242" in let E253 := fresh "E253" in
pose proof (img_env_atomP E 240%nat H ltac:(unfold A_TEXT, A_LIM; lia)) as E240;
pose proof (img_env_atomP E 241%nat H ltac:(unfold A_TEXT, A_LIM; lia)) as E241;
pose proof (img_env_atomP E 242%nat H ltac:(unfold A_TEXT, A_LIM; lia)) as E242;
pose proof (img_env_atomP E 253%nat H ltac:(unfold A_TEXT, A_LIM; lia)) as E253.
Ltac img_hull_factsF :=
let TLF := rnTLF in
pose proof (pa_obj_img 0 ltac:(lia)) as Hob241; pose proof (pa_obj_img 1 ltac:(lia)) as Hob242; pose proof (pa_obj_img 12 ltac:(lia)) as Hob253;
cbv [A_OBJ Nat.add] in Hob241, Hob242, Hob253;
pose proof (palf_uar_img _ TLF) as Huar; pose proof (palf_uar_al _ TLF) as Huar4.
Ltac ffb_goal := repeat (match goal with
| |- context [fs_frame_bytes ?c / 8] =>
let v := eval vm_compute in (fs_frame_bytes c / 8) in lazymatch v with Zpos _ => change (fs_frame_bytes c / 8) with v end
| |- context [fs_frame_bytes ?c] =>
let v := eval vm_compute in (fs_frame_bytes c) in lazymatch v with Zpos _ => change (fs_frame_bytes c) with v end end).
Ltac stk_lit HJ :=
lazymatch type of HJ with ajournal _ _ ?STK _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
let v := eval vm_compute in STK in try (change STK with v) end.
Ltac awrF_rec AG fpos F EFA :=
lazymatch goal with
| |- awr_ok _ _ _ [] _ _ _ _ _ _ _ _ => apply awr_ok_nil
| |- awr_ok _ _ _ (YP09.mkRegion _ _ _ ?wlo ?whi _ :: _) _ _ _ _ _ _ _ _ =>
first
[ lazymatch (eval vm_compute in (Z.leb whi wlo)) with true => apply awr_ok_cons_ro; [clear; cbn; lia|] end
| lazymatch goal with
| |- awr_ok _ _ _ (YP09.mkRegion (Some 529%nat) _ _ _ _ _ :: _) _ _ _ _ _ _ _ ((?cid, _) :: _) =>
eapply (YCbq.awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ _ _ _ 529%nat); [reflexivity | evalE AG | | ];
[ cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; right; right; right; left; exists cid, fpos; split; [left; reflexivity|]; right;
unfold in_zr, shadow_addr; cbn [fst snd]; rewrite <- SB_SHADOW_OFF; ffb_goal; rewrite ?EFA; fold F; unfold SB; clear - Ha; lia
| ]
| |- awr_ok _ _ _ (YP09.mkRegion (Some 516%nat) _ _ _ _ _ :: _) _ _ _ _ _ _ _ ((?cid, _) :: _) =>
eapply (YCbq.awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ _ _ _ 516%nat); [reflexivity | evalE AG | | ];
[ cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; right; right; right; left; exists cid, fpos; split; [left; reflexivity|]; left;
unfold in_zr; cbn [fst snd]; ffb_goal; rewrite ?EFA; fold F; clear - Ha; lia
| ]
| |- awr_ok _ _ _ (YP09.mkRegion (Some 2%nat) _ _ _ _ _ :: _) _ _ _ _ _ _ _ _ =>
eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ _ _ _ 2%nat 0); [reflexivity | evalE AG | clear; cbn; unfold ASTACK; lia | clear; cbn; lia |]
| |- awr_ok _ _ _ (YP09.mkRegion (Some 60%nat) _ _ _ _ _ :: _) _ ?sp0 _ _ _ _ _ _ =>
lazymatch goal with Hsp1 : sp0 - _ <= ?sp1 <= sp0 - _ |- _ =>
eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ _ _ _ 60%nat (sp1 - sp0)); [reflexivity | evalE AG | clear - Hsp1; cbn; unfold ASTACK; lia | clear -Hsp1; cbn; lia |] end
end
| match goal with |- awr_ok _ _ _ (?r :: _) _ _ _ _ _ _ _ _ => idtac "AWR-HEAD" r end; fail 1 "awrFL: no rule for the head region" ];
awrF_rec AG fpos F EFA
end.
Ltac awrFL AG fpos F EFA :=
lazymatch goal with |- awr_ok ?sg ?Bv ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?f0 ?ly ?own =>
let rs' := eval vm_compute in rs in let stk' := eval vm_compute in stk in change (awr_ok sg Bv E rs' stk' sp0 fp b0 bc f0 ly own) end;
awrF_rec AG fpos F EFA.
Ltac keptFL HK HJx AG Kg Kg2 Kc Kc2 Kgu Kgu2 Ku Ku2 ErT PrT :=
lazymatch goal with
| |- region_kept _ _ _ _ (YP09.mkRegion (Some 2%nat) _ _ _ _ _) =>
eapply (region_kept_stack_aj _ _); [exact HK | exact HJx | evalE AG | unfold ESTACK, ASTACK; lia | unfold ASTACK; stk_lit HJx; lia | lia | lia | lia]
| |- region_kept _ _ _ _ (YP09.mkRegion (Some 60%nat) _ _ _ _ _) =>
eapply (region_kept_stack_aj _ _); [exact HK | exact HJx | evalE AG | unfold ESTACK, ASTACK; lia | unfold ASTACK; stk_lit HJx; lia | lia | lia | lia]
| |- region_kept _ ?Ex _ _ (YP09.mkRegion (Some 241%nat) _ _ _ _ _) =>
let H := rnHEI Ex in apply (region_kept_val_at Ex _ _ (A_OBJ 0) (pa_val (A_OBJ 0)) 8 (pa_val (A_OBJ 12)));
[exact (H (A_OBJ 0) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact Kg | exact Kg2 | lia]
| |- region_kept _ ?Ex _ _ (YP09.mkRegion (Some 253%nat) _ _ _ _ _) =>
let H := rnHEI Ex in apply (region_kept_val_at Ex _ _ (A_OBJ 12) (pa_val (A_OBJ 12)) 8 SHADOW_OFF);
[exact (H (A_OBJ 12) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact Kc | exact Kc2 | lia]
| |- region_kept _ ?Ex _ _ (YP09.mkRegion (Some 242%nat) _ _ _ _ _) =>
let H := rnHEI Ex in let Bv := rnB in apply (region_kept_val_at Ex _ _ (A_OBJ 1) (pa_val (A_OBJ 1)) 8 (as_uar_cell Bv));
[exact (H (A_OBJ 1) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact Kgu | exact Kgu2 | lia]
| |- region_kept _ ?Ex _ _ (YP09.mkRegion (Some 59%nat) _ _ _ _ _) =>
let AGx := lazymatch goal with A : forall n, (n < 33)%nat -> ew _ n = ew _ n |- _ => A end in
let Bv := rnB in apply (region_kept_val_at Ex _ _ 59%nat (as_uar_cell Bv) 4 1); [evalE AGx | exact Ku | exact Ku2 | lia]
| |- region_kept _ _ _ _ (YP09.mkRegion (Some 516%nat) _ _ _ _ _) =>
eapply (region_kept_ownframe_aj _ _); [exact HK | evalE AG | eassumption
| left; rewrite_frame_addr; ffb_goal; lia | intros a Ha; cbn beta; first [exact (fun Hn : False => Hn) | ErT] | intros a Ha; PrT ]
| |- region_kept _ _ _ _ (YP09.mkRegion (Some 529%nat) _ _ _ _ _) =>
eapply (region_kept_ownframe_aj _ _); [exact HK | evalE AG | eassumption
| right; rewrite_frame_addr; unfold shadow_addr; rewrite <- SB_SHADOW_OFF; ffb_goal; unfold SB; lia
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
end.
Ltac oblG HJx E10n E32n Hing := obl_blk HJx E10n E32n Hing.
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
Section h. Context {fx : YK11.FPState}.
Lemma st_ok_havoc_hi : forall segs k E ss ms ws,
st_ok segs E ss ms -> ss_atoms_p (pband k (k + length ws)) ss = true -> st_ok segs (havoc E k ws) ss ms.
Proof.
intros segs k E ss ms ws HS Hat.
eapply (st_ok_agree_p (pband k (k + length ws)) segs); [exact HS | | exact Hat].
apply env_agree_p_havoc. apply le_n.
Qed.
End h.
Ltac add_atom HS n w En :=
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
let HS3 := fresh "HS3" in
pose proof (st_ok_pi_havoc_hi n Ev ssv msv [w] HS ltac:(vm_compute; reflexivity)) as HS3; hei_pose Ev n%nat [w];
clear HS; rename HS3 into HS;
assert (En : ew (havoc Ev n [w]) n = w) by (exact (ew_havoc_new _ n [w] 0 (Z_to_bv 64 0) ltac:(cbn; lia))) | st_ok _ ?Ev ?ssv ?msv =>
let HS3 := fresh "HS3" in
pose proof (st_ok_havoc_hi _ n Ev ssv msv [w] HS ltac:(vm_compute; reflexivity)) as HS3; hei_pose Ev n%nat [w];
clear HS; rename HS3 into HS;
assert (En : ew (havoc Ev n [w]) n = w) by (exact (ew_havoc_new _ n [w] 0 (Z_to_bv 64 0) ltac:(cbn; lia)))  end.
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
Definition boxed (P : Prop) : Prop := P.
Ltac box H := lazymatch type of H with ?T => change T with (boxed T) in H end.
Ltac unbox := unfold boxed in *.
Ltac relowF HS AG E10 E11 E32 E10n E11n E32n :=
try clear E10n; try clear E11n; try clear E32n;
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
lazymatch type of E10 with _ = ?v => assert (E10n : ew Ev 10 = v) by (rewrite (AG 10%nat) by lia; exact E10) end;
lazymatch type of E11 with _ = ?v => assert (E11n : ew Ev 11 = v) by (rewrite (AG 11%nat) by lia; exact E11) end;
lazymatch type of E32 with _ = ?v => assert (E32n : ew Ev 32 = v) by (rewrite (AG 32%nat) by lia; exact E32) end | st_ok _ ?Ev _ _ =>
lazymatch type of E10 with _ = ?v => assert (E10n : ew Ev 10 = v) by (rewrite (AG 10%nat) by lia; exact E10) end;
lazymatch type of E11 with _ = ?v => assert (E11n : ew Ev 11 = v) by (rewrite (AG 11%nat) by lia; exact E11) end;
lazymatch type of E32 with _ = ?v => assert (E32n : ew Ev 32 = v) by (rewrite (AG 32%nat) by lia; exact E32) end  end.
(* reseat_pi: lib/A/ACjr.v's reseat, which takes the symbolic state across a runtime call on the
   position-abstract listing (jafter_call_keep_hi, a return address SOff A_TEXT retk) and matches st_ok_pi as
   well as st_ok. PaDenot.v's reseat is YC4b.v's form for an absolute return address, so the name differs. *)
Ltac reseat_pi HS HJ2 HP2 keep AG kept_tac :=
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
