(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YC02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YI02 YI04 YI1i YI08.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YCcz.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB1u YCe7 YF9i YCeb YCe8 YCfq YCdy YCe9 YCfx
YCi1 YCib YCie YCif.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section f.
Variable B : asyms.
Lemma rg_region_kept_frame_sub : forall E STK1 sp1 FP1 lyc Sc W memc mdc ly2 S2 W2 mem2 md2 k1 n b lo hi wlo whi cs cid pos,
ajournal trbsegs B STK1 sp1 FP1 lyc Sc W memc mdc [] ly2 S2 W2 mem2 md2 k1 ->
bv_unsigned (ew E n) = b -> In (cid, pos) (frames Sc) ->
frame_addr lyc cid pos <= b + lo -> b + hi <= frame_addr lyc cid pos + fs_frame_bytes cid ->
(forall a, b + lo <= a < b + hi -> ~ inFP FP1 a) ->
(forall a, b + wlo <= a < b + whi -> apresent (w_H W2) mem2 a) ->
region_kept trbsegs E (mrestrict (w_H W) memc) (mrestrict (w_H W2) mem2) (YQ0b.mkRegion (Some n) lo hi wlo whi cs).
Proof.
intros E STK1 sp1 FP1 lyc Sc W memc mdc ly2 S2 W2 mem2 md2 k1 n b lo hi wlo whi cs cid pos HJ1 Hn Hin Hlo Hhi HnF Hp2.
pose proof HJ1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & K4 & _).
split; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi base_val]; rewrite Hn; intros a Ha.
- apply (mbyte_of_aview trbsegs). apply (K4 cid pos a Hin); [left; unfold in_zr, frame_rng; cbn [fst snd]; lia | apply HnF; exact Ha].
- intros _. apply (apresent_writable trbsegs). apply Hp2. lia.
Qed.
Lemma rg_region_kept_fshadow_sub : forall E STK1 sp1 FP1 lyc Sc W memc mdc ly2 S2 W2 mem2 md2 k1 n b lo hi wlo whi cs cid pos,
ajournal trbsegs B STK1 sp1 FP1 lyc Sc W memc mdc [] ly2 S2 W2 mem2 md2 k1 ->
bv_unsigned (ew E n) = b -> In (cid, pos) (frames Sc) ->
shadow_addr (frame_addr lyc cid pos) <= b + lo -> b + hi <= shadow_addr (frame_addr lyc cid pos) + fs_frame_bytes cid / 8 ->
(forall a, b + lo <= a < b + hi -> ~ inFP FP1 a) ->
(forall a, b + wlo <= a < b + whi -> apresent (w_H W2) mem2 a) ->
region_kept trbsegs E (mrestrict (w_H W) memc) (mrestrict (w_H W2) mem2) (YQ0b.mkRegion (Some n) lo hi wlo whi cs).
Proof.
intros E STK1 sp1 FP1 lyc Sc W memc mdc ly2 S2 W2 mem2 md2 k1 n b lo hi wlo whi cs cid pos HJ1 Hn Hin Hlo Hhi HnF Hp2.
pose proof HJ1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & K4 & _).
split; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi base_val]; rewrite Hn; intros a Ha.
- apply (mbyte_of_aview trbsegs). apply (K4 cid pos a Hin); [right; unfold in_zr; cbn [fst snd]; lia | apply HnF; exact Ha].
- intros _. apply (apresent_writable trbsegs). apply Hp2. lia.
Qed.

Hypothesis LAWS : AR_laws trbsegs B.
Lemma rg_region_kept_block_subw2 : forall E STK1 sp1 FP1 lyc Sc W memc mdc ly2 S2 W2 mem2 md2 k1 n lo hi wlo whi cs b m,
ajournal trbsegs B STK1 sp1 FP1 lyc Sc W memc mdc [] ly2 S2 W2 mem2 md2 k1 ->
bv_unsigned (ew E n) = b -> In (b, m) (ablocks B lyc Sc) -> In (b, m) (ablocks B ly2 S2) ->
0 <= lo -> hi <= req_size m -> lo <= wlo -> whi <= hi ->
(forall a, b + lo <= a < b + hi -> ~ inFP FP1 a) ->
region_kept trbsegs E (mrestrict (w_H W) memc) (mrestrict (w_H W2) mem2) (YQ0b.mkRegion (Some n) lo hi wlo whi cs).
Proof.
intros E STK1 sp1 FP1 lyc Sc W memc mdc ly2 S2 W2 mem2 md2 k1 n lo hi wlo whi cs b m HJ1 Hn Hin Hin2 Hlo Hhi Hw1 Hw2 HnF.
pose proof HJ1 as (HAR2 & _ & _ & _ & _ & _ & _ & _ & _ & G2 & _).
split; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi base_val]; rewrite Hn; intros a Ha.
- apply (mbyte_of_aview trbsegs). replace a with (b + (a - b)) by lia. apply (G2 b m (a - b) Hin Hin2); [lia|].
replace (b + (a - b)) with a by lia. apply HnF. exact Ha.
- intros _. apply (apresent_writable trbsegs). destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR2 Hin2) as (_ & _ & _ & _ & HP & _). apply HP. lia.
Qed.
End f.
End d.
Ltac rnLAWS := lazymatch goal with L : AR_laws trbsegs _ |- _ => L end.
Ltac rnTL := lazymatch goal with T : TrbLib _ |- _ => T end.
Ltac rnFFL := lazymatch goal with H : frame_flag_lawP _ _ |- _ => H end.
Ltac nat_side := first [ apply (proj1 (PeanoNat.Nat.ltb_lt _ _)); vm_compute; reflexivity
| apply (proj1 (PeanoNat.Nat.eqb_neq _ _)); vm_compute; reflexivity ].
Ltac rebaseE HS AG HEv :=
let AG2 := fresh "AG" in let Ev := fresh "E" in
lazymatch type of AG with forall n, _ -> _ = ew ?E0 n =>
lazymatch type of HS with st_ok _ ?Enew _ _ =>
remember Enew as Ev eqn:HEv in HS;
assert (AG2 : forall n, (n < 33)%nat -> ew Ev n = ew E0 n)
by (intros nn Hnn; rewrite HEv; rewrite ?ew_ewset_other, ?ew_havoc_old by lia; rewrite ?ew_ewset_other, ?ew_havoc_old by lia; apply AG; exact Hnn);
repeat match goal with H : ew ?Eo ?n = ?v |- _ =>
lazymatch Eo with
| Ev => fail
| _ => lazymatch (eval cbv in (Nat.leb 33 n)) with
| true => let H2 := fresh H in
assert (H2 : ew Ev n = v) by (rewrite HEv; rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; exact H);
clear H; rename H2 into H
end end end;
clear AG; rename AG2 into AG end end.
Ltac evalE AG :=
cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia;
repeat match goal with H : ew ?Ex ?n = Z_to_bv 64 _ |- context [ew ?Ex ?n] => rewrite H end;
lazymatch type of AG with forall n, _ -> ew ?Ev n = _ =>
repeat match goal with |- context [ew Ev ?n] => lazymatch (eval cbv in (Nat.ltb n 33)) with true => rewrite (AG n) by lia end end end;
repeat match goal with H : ew ?Ex ?n = Z_to_bv 64 _ |- context [ew ?Ex ?n] => rewrite H end;
repeat match goal with H : bv_unsigned (ew ?Ex 2) = _ |- context [bv_unsigned (ew ?Ex 2)] => rewrite H end;
rewrite ?unsigned_lit_small by (unfold SB; lia); unfold SB; first [reflexivity | lia | idtac].
Ltac evalE0 AG :=
cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia;
repeat match goal with H : ew ?Ex ?n = Z_to_bv 64 _ |- context [ew ?Ex ?n] => rewrite H end;
lazymatch type of AG with forall n, _ -> ew ?Ev n = _ =>
repeat match goal with |- context [ew Ev ?n] => lazymatch (eval cbv in (Nat.ltb n 33)) with true => rewrite (AG n) by lia end end end;
repeat match goal with H : ew ?Ex ?n = Z_to_bv 64 _ |- context [ew ?Ex ?n] => rewrite H end;
repeat match goal with H : bv_unsigned (ew ?Ex 2) = _ |- context [bv_unsigned (ew ?Ex 2)] => rewrite H end;
rewrite ?unsigned_lit_small by (unfold SB; lia); unfold SB.
Ltac clear_frames := repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
Ltac idx_of_base rs n :=
lazymatch rs with
| YQ0b.mkRegion (Some n) _ _ _ _ _ :: _ => constr:(0%nat)
| _ :: ?tl => let i := idx_of_base tl n in constr:(S i)
end.
Ltac aconsts HROD HJx Kgot Kcell Kguar Kuar Vgr :=
let Kc := fresh "Kc" in let Ku := fresh "Ku" in let Kg := fresh "Kg" in let Kgu := fresh "Kgu" in
let LAWS := rnLAWS in let TL := rnTL in
destruct (al_const _ _ LAWS _ _ _ _ _ (proj1 HJx)) as (Kc & Ku & Kg & Kgu);
rewrite (tl_got_shadow _ TL), (tl_shadow_cell _ TL) in Kg; rewrite (tl_shadow_cell _ TL) in Kc;
rewrite (tl_got_uar _ TL), (tl_uar_cell _ TL) in Kgu; rewrite (tl_uar_cell _ TL) in Ku;
pose proof (val_mem_of_rdword trbsegs _ _ _ _ Kg) as Kgot; pose proof (val_mem_of_rdword trbsegs _ _ _ _ Kc) as Kcell;
pose proof (val_mem_of_rdword trbsegs _ _ _ _ Kgu) as Kguar; pose proof (val_mem_of_rd32 trbsegs _ _ _ _ Ku) as Kuar;
clear Kc Ku Kg Kgu;
pose proof (arodata_val8 _ _ _ A_GOT_rgb_newgif A_cgif_rgb_newgif TL
(arodata_ok_journal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJx HROD)
ltac:(unfold A_GOT_rgb_newgif; lia) ltac:(unfold A_GOT_rgb_newgif; lia)
ltac:(intros x Hx; unfold lib_const_addr, A_GOT_rgb_newgif in *; lia)
ltac:(intros kk Hkk; do 8 (destruct kk as [|kk]; [vm_compute; reflexivity|]); lia)) as Vgr.
Ltac rqs Hn := repeat (lazymatch type of Hn with context [req_size ?n] =>
let v := eval vm_compute in (req_size n) in
lazymatch v with Zpos _ => change (req_size n) with v in Hn | Z0 => change (req_size n) with v in Hn end end).
Ltac kept_consts Kg Kg2 Kc Kc2 Kgu Kgu2 Ku Ku2 Vg Vg2 :=
lazymatch goal with
| |- region_kept _ _ _ _ (YQ0b.mkRegion None A_GOT_shadow _ _ _ _) => apply (region_kept_val trbsegs _ _ _ A_GOT_shadow 8 A_shadow_glob); [exact Kg | exact Kg2 | lia]
| |- region_kept _ _ _ _ (YQ0b.mkRegion None A_shadow_glob _ _ _ _) => apply (region_kept_val trbsegs _ _ _ A_shadow_glob 8 SHADOW_OFF); [exact Kc | exact Kc2 | lia]
| |- region_kept _ _ _ _ (YQ0b.mkRegion None A_GOT_uar _ _ _ _) => apply (region_kept_val trbsegs _ _ _ A_GOT_uar 8 A_uar_glob); [exact Kgu | exact Kgu2 | lia]
| |- region_kept _ _ _ _ (YQ0b.mkRegion None A_uar_glob _ _ _ _) => apply (region_kept_val trbsegs _ _ _ A_uar_glob 4 1); [exact Ku | exact Ku2 | lia]
| |- region_kept _ _ _ _ (YQ0b.mkRegion None A_GOT_rgb_newgif _ _ _ _) => apply (region_kept_val trbsegs _ _ _ A_GOT_rgb_newgif 8 A_cgif_rgb_newgif); [exact Vg | exact Vg2 | lia]
| |- region_kept _ _ _ _ (YQ0b.mkRegion None ?a _ _ _ _) =>
first [ change a with A_GOT_shadow | change a with A_shadow_glob | change a with A_GOT_uar | change a with A_uar_glob | change a with A_GOT_rgb_newgif ];
kept_consts Kg Kg2 Kc Kc2 Kgu Kgu2 Ku Ku2 Vg Vg2
end.
Ltac keptR HK HJx AG Usp E10 Hfin Kg Kg2 Kc Kc2 Kgu Kgu2 Ku Ku2 Vg Vg2 EFA :=
lazymatch goal with
| |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 2%nat) _ _ _ _ _) =>
eapply (region_kept_stack_aj trbsegs _); [exact HK | exact HJx | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?(AG 2%nat) by lia; exact Usp
| lia | unfold TRGBNEWGIF_STK, TNEWGIF_STK, TRAWNEW_STK, ASTACK; lia | lia | lia | lia]
| |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 10%nat) _ _ _ _ _) =>
eapply (region_kept_frame_aj trbsegs _); [exact HK | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?(AG 10%nat) by lia; rewrite E10; apply unsigned_lit_small; lia
| exact Hfin | rewrite ?EFA; lia | rewrite ?EFA; lia | lia | intros a Ha Hn; first [exact Hn | lia | rqs Hn; zone_lia]]
| |- region_kept _ _ _ _ (YQ0b.mkRegion None _ _ _ _ _) => kept_consts Kg Kg2 Kc Kc2 Kgu Kgu2 Ku Ku2 Vg Vg2
end.
Ltac awrR_rec AG fpos F EFA aF aFS :=
lazymatch goal with
| |- awr_ok _ [] _ _ _ _ _ _ _ => apply awr_ok_nil
| |- awr_ok _ (YQ0b.mkRegion ?bs _ _ ?wlo ?whi _ :: _) _ _ _ _ ?blc _ _ =>
first
[ apply awr_ok_cons_ro; [cbn; lia|]
| lazymatch bs with
| Some aFS =>
eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ aFS); [reflexivity | evalE AG | | ];
[ cbn [YQ0b.r_wlo YQ0b.r_whi]; intros a Ha; right; right; right; exists 1, fpos; split; [left; reflexivity|]; right;
unfold in_zr, shadow_addr; cbn [fst snd]; rewrite <- SB_SHADOW_OFF; change (fs_frame_bytes 1 / 8) with 16; rewrite ?EFA; fold F; unfold SB; clear - Ha; lia
| ]
| Some aF =>
eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ aF); [reflexivity | evalE AG | | ];
[ cbn [YQ0b.r_wlo YQ0b.r_whi]; intros a Ha; right; right; right; exists 1, fpos; split; [left; reflexivity|]; left;
unfold in_zr; cbn [fst snd]; change (fs_frame_bytes 1) with 128; rewrite ?EFA; fold F; clear - Ha; lia
| ]
| Some 2%nat =>
eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat 0); [reflexivity | evalE AG | cbn; lia | cbn; lia |]
| Some ?nb =>
match goal with Rb : ew _ nb = Z_to_bv 64 ?b, Ab : forall blc' lyq ownq i, In (?b', ?sz) blc' -> _, Hin : In (?b', ?sz) blc |- _ =>
constr_eq b b';
eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ nb); [reflexivity | evalE AG | | ];
[ cbn [YQ0b.r_wlo YQ0b.r_whi]; let a := fresh "a" in let Ha := fresh "Ha" in
intros a Ha; replace a with (b + (a - b)) by lia; apply Ab; [exact Hin | clear - Ha; lia]
| ] end
end
| fail 1 "awrR: no rule for the head region" ];
awrR_rec AG fpos F EFA aF aFS
end.
Ltac awrR AG fpos F EFA aF aFS :=
lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fp b0 bc ly own) end;
awrR_rec AG fpos F EFA aF aFS.
Ltac upd_above HUP HFr AG :=
let HUP' := fresh "HUP" in
lazymatch type of HFr with frame_of ?Ef ?rs (mrestrict _ ?m0) (mrestrict _ (ms_mem ?msX)) =>
lazymatch type of HUP with forall a, ?lo <= a < _ -> aview ?sg ?Hh _ a = aview _ _ ?me a =>
assert (HUP' : forall a, lo <= a < 2 ^ 64 -> aview sg Hh (ms_mem msX) a = aview sg Hh me a);
[ let a := fresh "a" in let Ha := fresh "Ha" in
intros a Ha; rewrite <- (HUP a Ha); eapply (aview_kept_frame Ef rs _ _ _ lo HFr); [lia| |exact Ha];
let b := fresh "b" in let Hb := fresh "Hb" in let rg := fresh "rg" in let Hin := fresh "Hin" in let Hrg := fresh "Hrg" in
intros b Hb (rg & Hin & Hrg);
lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In rg rs1) in Hin end; cbn [In] in Hin;
repeat (destruct Hin as [<- | Hin]; [cbn [YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi base_val] in Hrg; revert Hrg; evalE AG; intros Hrg; clear - Hb Hrg; lia|]);
destruct Hin
| clear HUP; rename HUP' into HUP ] end end.
Ltac keptI Hfr Hpres AG Kg Kg2 Kc Kc2 Kgu Kgu2 Ku Ku2 Vg Vg2 :=
lazymatch goal with
| |- region_kept _ _ _ _ (YQ0b.mkRegion (Some ?n) _ _ _ _ _) =>
eapply region_kept_aview; [evalE AG | intros a Ha; apply Hfr; unfold ESTACK; zone_lia | exact Hpres]
| |- region_kept _ _ _ _ (YQ0b.mkRegion None _ _ _ _ _) => kept_consts Kg Kg2 Kc Kc2 Kgu Kgu2 Ku Ku2 Vg Vg2
end.
Ltac rng_chain HS HJx AG EE :=
let Vra := fresh "Vra" in let Vs0 := fresh "Vs0" in let HUP := fresh "HUPc" in let Hch1 := fresh "Hch1" in
let Qceil := fresh "Qceil" in let Qal8 := fresh "Qal8" in let Qtop := fresh "Qtop" in let Qtop64 := fresh "Qtop64" in
let Qsp := fresh "Qsp" in let Qra := fresh "Qra" in let Qs0 := fresh "Qs0" in
lazymatch goal with Hch : achain ?ly (aview _ (w_H ?W) ?mem) (spZ ?regs) (s0Z _) ?ch |- _ =>
assert (Qceil : alloc_ceiling <= spZ regs) by lia;
assert (Qal8 : spZ regs mod 8 = 0) by (let D := fresh "D" in lazymatch goal with Hal32 : spZ regs mod 32 = 0 |- _ =>
pose proof (Z.div_mod (spZ regs) 32 ltac:(lia)) as D; rewrite Hal32, Z.add_0_r in D; rewrite D;
replace (32 * (spZ regs / 32)) with ((4 * (spZ regs / 32)) * 8) by lia; apply Z_mod_mult end);
assert (Qtop : spZ regs < ly_top ly - 16) by lia; assert (Qtop64 : ly_top ly <= 2 ^ 64) by lia; assert (Qsp : spZ regs - 96 + 16 <= spZ regs) by lia;
assert (Qra : 0 <= raZ regs < 2 ^ 64) by (unfold raZ; let Hq := fresh "Hq" in pose proof (bv_unsigned_in_range 64 (getr regs 1)) as Hq; change (bv_modulus 64) with (2 ^ 64) in Hq; exact Hq);
assert (Qs0 : 0 <= s0Z regs < 2 ^ 64) by (unfold s0Z; let Hq := fresh "Hq" in pose proof (bv_unsigned_in_range 64 (getr regs 8)) as Hq; change (bv_modulus 64) with (2 ^ 64) in Hq; exact Hq);
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict (w_H ?W3) ?msX) =>
assert (HUP : forall a, spZ regs <= a < 2 ^ 64 -> aview trbsegs (w_H W3) (ms_mem msX) a = aview trbsegs (w_H W) mem a)
by (let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
let F1 := fresh "F1" in pose proof HJx as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _); apply F1; [clear - Ha Qceil; lia | clear - Ha; lia]);
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs 2%nat in let i := eval vm_compute in i in
let HRstk := fresh "HRstk" in
pose proof (st_ok_region_nth Ex ssx (restrict (w_H W3) msX) i _ HS eq_refl) as HRstk; cbn [ms_mem restrict] in HRstk;
lazymatch type of HRstk with region_ok _ _ _ (YQ0b.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 2 (spZ regs) cs lo hi wlo whi (-8) 8%N (SOff 1 0) (raZ regs) HRstk
ltac:(evalE AG) ltac:(cbn; tauto) ltac:(cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 1%nat) by lia; rewrite (EE 1%nat 1%bv eq_refl), Z.add_0_r; reflexivity)
ltac:(unfold raZ; let Hq := fresh "Hq" in pose proof (bv_unsigned_in_range 64 (getr regs 1)) as Hq; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Hq; exact Hq) ltac:(cbn; lia)) as Vra;
pose proof (field_of_region Ex _ 2 (spZ regs) cs lo hi wlo whi (-16) 8%N (SOff 8 0) (s0Z regs) HRstk
ltac:(evalE AG) ltac:(cbn; tauto) ltac:(cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 8%nat) by lia; rewrite (EE 8%nat 8%bv eq_refl), Z.add_0_r; reflexivity)
ltac:(unfold s0Z; let Hq := fresh "Hq" in pose proof (bv_unsigned_in_range 64 (getr regs 8)) as Hq; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Hq; exact Hq) ltac:(cbn; lia)) as Vs0 end;
clear HRstk;
assert (Hch1 : achain ly (aview trbsegs (w_H W3) (ms_mem msX)) (spZ regs - 96) (spZ regs) ((spZ regs, raZ regs, s0Z regs) :: ch));
[ replace (spZ regs - 8) with (spZ regs + -8) in Vra by lia; replace (spZ regs - 16) with (spZ regs + -16) in Vs0 by lia;
lazymatch goal with Hra4 : 4096 <= raZ regs |- _ =>
exact (achain_push ly _ _ (spZ regs) (s0Z regs) (raZ regs) _ (spZ regs - 96) Hch Qtop64 HUP
(rdword_of_val_mem trbsegs _ _ _ _ Vra Qra) (rdword_of_val_mem trbsegs _ _ _ _ Vs0 Qs0) Hra4 Qceil Qal8 Qtop Qsp) end
| ] end end.
Ltac fs_ro HS :=
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs 55%nat in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rs got_region) in
let HS3 := fresh "HS3" in
pose proof (ast_ok_set_region trbsegs Ex ssx msx i r (set_window r 0 0) HS ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity)
(region_ok_rewindow trbsegs Ex _ r 0 0 (st_ok_region_nth Ex ssx msx i r HS ltac:(vm_compute; reflexivity)) ltac:(intros o Ho; lia))) as HS3;
clear HS; rename HS3 into HS; norm_ss HS end.
Ltac fs_rw HS E55 Hp :=
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs 55%nat in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rs got_region) in
let HS3 := fresh "HS3" in
pose proof (ast_ok_set_region trbsegs Ex ssx msx i r (set_window r 0 16) HS ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity)
(region_ok_rewindow trbsegs Ex _ r 0 16 (st_ok_region_nth Ex ssx msx i r HS ltac:(vm_compute; reflexivity))
ltac:(cbn [YQ0b.r_base base_val ms_mem restrict mkst]; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia;
rewrite E55, unsigned_lit_small by (unfold SB; lia);
intros o Ho; apply (apresent_writable trbsegs); unfold shadow_addr in Hp; rewrite <- SB_SHADOW_OFF in Hp;
apply (proj1 (Hp o ltac:(clear - Ho; lia)))))) as HS3;
clear HS; rename HS3 into HS; norm_ss HS end.
Ltac creg HS AG EE :=
lazymatch goal with |- getr _ ?r = getr _ _ =>
let R := fresh "R" in rreg HS r R; rewrite R; clear R;
cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite AG by lia;
apply EE; reflexivity end.
Ltac add_flag_region HS AG E54 Hp HFLrng HFLown HnoG HnoC HnoF :=
let Qceil := match goal with H : alloc_ceiling <= ly_stk_lo _ |- _ => H end in
let Qslo := match goal with H : ly_stk_lo _ + _ <= spZ _ |- _ => H end in
let QC1 := match goal with H : _ <= alloc_ceiling <= _ |- _ => H end in
let QC3 := match goal with H : kHighMemBeg = _ |- _ => H end in
let QFFS := match goal with H : TRGBNEWGIF_STK = _ |- _ => H end in
let QFq := match goal with H : ?Fr = 32 * (?Fr / 32) |- _ => H end in
let QF8 := match goal with H : ?Fr / 8 = 4 * (?Fr / 32) |- _ => H end in
let QFceil := match goal with H : ?Fr + 128 <= alloc_ceiling |- _ => H end in
let QF8lo := match goal with H : 512 <= ?Fr / 8 |- _ => H | _ => QFq end in
let QF8hi := match goal with H : ?Fr / 8 < 17592186044416 |- _ => H | _ => QFq end in
lazymatch type of HS with st_ok _ ?Ev _ _ =>
let HS3 := fresh "HS3" in
pose proof (ast_ok_add_region trbsegs Ev _ _ (YQ0b.mkRegion (Some 54%nat) 0 1 0 1 []) HS eq_refl
ltac:(unfold region_ok; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val ms_mem restrict mkst];
rewrite ?ew_ewset_other by lia; rewrite E54, unsigned_lit_small by lia; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
intros o Ho; apply (apresent_writable trbsegs); lazymatch goal with |- apresent _ _ (?fl + ?oo) => replace (fl + oo) with fl by lia end; exact Hp)
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val]; evalE0 AG;
unfold A_GOT_shadow, A_shadow_glob, A_GOT_uar, A_uar_glob, A_GOT_rgb_newgif;
repeat split; first [clear - HFLrng Qceil Qslo QC1 QC3 QFFS QFq QF8 QFceil QF8lo QF8hi; zone_lia |
lazymatch goal with |- ?fl + 1 <= ?x + ?l \/ ?x + ?h <= ?fl + 0 =>
let Hlt := fresh "Hlt" in let Hge := fresh "Hge" in let Hlt2 := fresh "Hlt2" in let Hge2 := fresh "Hge2" in
destruct (Z_lt_ge_dec fl (x + l)) as [Hlt | Hge]; [left; clear - Hlt; lia|];
destruct (Z_lt_ge_dec fl (x + h)) as [Hlt2 | Hge2]; [exfalso | right; clear - Hge2; lia];
first [apply (HnoG fl); [clear - Hge Hlt2; lia | exact HFLown] | apply (HnoC fl); [clear - Hge Hlt2; lia | exact HFLown]
| apply (HnoF fl); [clear - Hge Hlt2; lia | exact HFLown]
| match goal with Hn : forall a, _ -> ~ aowned _ _ _ a |- _ => apply (Hn fl); [clear - Hge Hlt2; lia | exact HFLown] end
| match goal with |- ?g => idtac "DISJFAIL" g end] end
| match goal with |- ?g => idtac "DISJ?" g end ])) as HS3;
clear HS; rename HS3 into HS; norm_ss HS end.
Ltac wrangeR AG fpos F EFA EFL :=
let a := fresh "a" in let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
intros a (r & Hin & Hr); rewrite ?EFA, ?EFL;
lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end;
cbn [In] in Hin;
repeat (destruct Hin as [<- | Hin];
[ cbn [YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi base_val] in Hr; revert Hr; evalE0 AG; intros Hr;
first [ exfalso; clear - Hr; lia
| right; clear - Hr; lia
| left; left; clear - Hr; unfold TRGBNEWGIF_STK, TNEWGIF_STK, TRAWNEW_STK, ASTACK; lia
| left; right; right; right; exists 1, fpos; split; [left; reflexivity|];
first [ left; unfold in_zr; cbn [fst snd]; change (fs_frame_bytes 1) with 128; rewrite ?EFA; fold F; clear - Hr; lia
| right; unfold in_zr, shadow_addr; cbn [fst snd]; rewrite <- SB_SHADOW_OFF; change (fs_frame_bytes 1 / 8) with 16; rewrite ?EFA; fold F; unfold SB; clear - Hr; lia ]
| left; match goal with A : forall blc lyq ownq i, In (?r, 64) blc -> _, Hin : In (?r, 64) (ablocks _ _ _) |- _ =>
replace a with (r + (a - r)) by lia; apply A; [exact Hin | clear - Hr; lia] end
| match goal with |- ?g => match type of Hr with ?t => idtac "WRFAIL" t g end end; fail 2 "wrangeR" ]
| ]);
destruct Hin.
Ltac flag0 E54 EFL :=
let msr := fresh "msr" in let HSr := fresh "HSr" in let HR := fresh "HR" in let V := fresh "V" in
intros msr HSr; rewrite ?EFL;
lazymatch type of HSr with st_ok _ ?Ex ?ssx _ =>
pose proof (st_ok_region_nth Ex ssx msr 0 _ HSr eq_refl) as HR;
lazymatch type of HR with region_ok _ _ _ (YQ0b.mkRegion (Some ?n) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex (ms_mem msr) n _ cs lo hi wlo whi 0 1%N (SLit 0) 0 HR
ltac:(cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E54; apply unsigned_lit_small; lia)
ltac:(left; reflexivity) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as V end end;
rewrite Z.add_0_r in V; pose proof (V 0%nat ltac:(lia)) as V0; cbn [Z.of_nat] in V0; rewrite Z.add_0_r in V0; exact V0.
Ltac exitG HS HJx AG fpos F cfgp E54 E55 Hfin HfinS EE Hra HEV EFA EFL :=
let HFLpres' := fresh "HFLpres'" in let HFLown := fresh "HFLown'" in let HFLrng := fresh "HFLrng'" in
let HFpres' := fresh "HFpres'" in let HFSpres' := fresh "HFSpres'" in
let HCpres' := fresh "HCpres'" in
let HnoC := fresh "HnoC" in let HnoF := fresh "HnoF" in
let FFL := rnFFL in let LAWS := rnLAWS in destruct (FFL _ _ _ _ _ 1 fpos (proj1 HJx) Hfin) as (HFLpres' & HFLown & HFLrng); rewrite ?EFL in HFLpres'; rewrite ?EFL in HFLown; rewrite ?EFL in HFLrng; fold F in HFLrng;
destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos (proj1 HJx) Hfin) as (_ & _ & HFpres' & HFSpres'); change (fs_frame_bytes 1) with 128 in HFpres', HFSpres';
change (128 / 8) with 16 in HFSpres'; rewrite ?EFA in HFpres'; rewrite ?EFA in HFSpres'; fold F in HFpres', HFSpres';
destruct (al_frames _ _ LAWS _ _ _ _ _ _ _ (proj1 HJx) HfinS) as (_ & _ & HCpres' & _); rewrite ?EFA in HCpres';
lazymatch type of HFpres' with forall a, _ -> _ /\ ~ aowned ?B ?lyx ?Sx a =>
assert (HnoC : forall a, cfgp <= a < cfgp + 40 -> ~ aowned B lyx Sx a) by (intros a Ha; apply (fun H => proj2 (HCpres' a H)); lia);
assert (HnoF : forall a, F <= a < F + 128 -> ~ aowned B lyx Sx a) by (intros a Ha; exact (proj2 (HFpres' a Ha))) end;
fs_rw HS E55 HFSpres';
add_flag_region HS AG E54 HFLpres' HFLrng HFLown HnoC HnoC HnoF;
aj_run_flag_sh trbtbl_lib_ok HS HJx; [lia | wrangeR AG fpos F EFA EFL | flag0 E54 EFL |];
let R1 := fresh "R1" in let R10 := fresh "R10" in
rreg HS (1%bv : bv 5) R1; rreg HS (10%bv : bv 5) R10;
lazymatch goal with |- SRr _ ?Wx _ _ =>
eapply (SRr_ret_at trbsegs trbtbl_lib trbtbl_lib_ok Hwx_tfa Wx _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)) end;
let mat' := fresh "mat'" in intros mat'; unfold trgb_newgif_post, apost_base;
lazymatch type of HJx with ajournal _ _ _ _ _ _ _ _ _ _ _ ?lyx ?Sx _ _ _ _ =>
lazymatch goal with |- exists ly' S' regs' mem' md', mkCfg (mkst ?rg _ ?mm _) ?mdx = _ /\ _ => exists lyx, Sx, rg, mm, mdx end end;
split; [rewrite R1; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 1%nat) by lia; rewrite (EE 1%nat 1%bv eq_refl), Hra; reflexivity|];
split; [cbn [ms_mem]; eapply (ajournal_mono_k trbsegs _); [apply (ajournal_materialize trbsegs _ LAWS trb_segs_low); exact HJx | rewrite HEV; unfold EV_NEWGIF, EV_RAWNEW; lia]|];
split; [apply aregs_preserved_eqs; creg HS AG EE|];
rewrite R10.
Ltac keptF HK AG RF E55 HfinX HFP HFSP HEr F EFA :=
lazymatch goal with
| |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 42%nat) _ _ _ _ _) =>
eapply (region_kept_ownframe_aj trbsegs _); [exact HK | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite RF; apply unsigned_lit_small; lia
| exact HfinX | left; change (fs_frame_bytes 1) with 128; rewrite ?EFA; fold F; lia
| let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; cbn beta; first [exact (fun Hn : False => Hn) | apply HEr; lia]
| let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; apply (fun H => proj1 (HFP a H)); lia ]
| |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 55%nat) _ _ _ _ _) =>
eapply (region_kept_ownframe_aj trbsegs _); [exact HK | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E55; apply unsigned_lit_small; unfold SB; lia
| exact HfinX | right; unfold shadow_addr; rewrite <- SB_SHADOW_OFF; change (fs_frame_bytes 1 / 8) with 16; rewrite ?EFA; fold F; lia
| let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; first [exact (fun Hn : False => Hn) | let Hn := fresh "Hn" in intros Hn; rqs Hn; unfold SB in Ha; zone_lia]
| let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; unfold shadow_addr in HFSP; rewrite <- ?SB_SHADOW_OFF in HFSP;
first [lia | apply (fun H => proj1 (HFSP (a - (SB + F / 8)) H)); lia | replace a with (SB + F / 8 + (a - (SB + F / 8))) by lia; apply (fun H => proj1 (HFSP (a - (SB + F / 8)) H)); lia] ]
end.
Ltac oblF HJx HE10 HE35 HRA HAR Hfin Hcid0 Hflo Hfhi Hfal :=
lazymatch goal with |- range_addressable _ (U ?Ex _) (U _ (SOff 10 ?c)) ?len =>
lazymatch type of HE10 with _ = Z_to_bv 64 ?cfgp =>
first [ rewrite (U_atom_off Ex 10 cfgp c); [| cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact HE10 | lia | lia]
| rewrite (U_atom Ex 10 cfgp); [| cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact HE10 | lia] ];
eapply (obl_of_range trbsegs _ _ Ex (SOff 35 0) _ len cfgp 40);
[ let L := rnLAWS in eapply (range_addressable_entry_frame trbsegs _ L); [exact HJx | exact Hfin | exact Hcid0 | exact Hflo | exact Hfhi | exact Hfal
| intros x Hx; exfalso; exact (inFP_nil x Hx) | exact HAR | exact HRA]
| rewrite (U_atom Ex 35 SB); [reflexivity | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact HE35 | unfold SB; lia]
| lia | lia ] end end.
Ltac keptJ HJc HJx AG Usp E10 RF E55 Hfin HfinS FFS Kg Kg2 Kc Kc2 Kgu Kgu2 Ku Ku2 Vg Vg2 EFA HFP HFSP HCP F fptac :=
let L := rnLAWS in
lazymatch goal with
| |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 2%nat) _ _ _ _ _) =>
eapply (region_kept_stack_sub trbsegs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 2%nat);
[exact HJc | exact HJx | evalE AG; exact Usp | clear; lia | rewrite FFS; clear; lia | clear; lia | clear; lia | clear; lia]
| |- region_kept _ _ _ _ (YQ0b.mkRegion None A_GOT_shadow _ _ _ _) => apply (region_kept_val trbsegs _ _ _ A_GOT_shadow 8 A_shadow_glob); [exact Kg | exact Kg2 | clear; lia]
| |- region_kept _ _ _ _ (YQ0b.mkRegion None A_shadow_glob _ _ _ _) => apply (region_kept_val trbsegs _ _ _ A_shadow_glob 8 SHADOW_OFF); [exact Kc | exact Kc2 | clear; lia]
| |- region_kept _ _ _ _ (YQ0b.mkRegion None A_GOT_uar _ _ _ _) => apply (region_kept_val trbsegs _ _ _ A_GOT_uar 8 A_uar_glob); [exact Kgu | exact Kgu2 | clear; lia]
| |- region_kept _ _ _ _ (YQ0b.mkRegion None A_uar_glob _ _ _ _) => apply (region_kept_val trbsegs _ _ _ A_uar_glob 4 1); [exact Ku | exact Ku2 | clear; lia]
| |- region_kept _ _ _ _ (YQ0b.mkRegion None A_GOT_rgb_newgif _ _ _ _) => apply (region_kept_val trbsegs _ _ _ A_GOT_rgb_newgif 8 A_cgif_rgb_newgif); [exact Vg | exact Vg2 | clear; lia]
| |- region_kept _ _ _ _ (YQ0b.mkRegion None ?a _ _ _ _) =>
first [ change a with A_GOT_shadow | change a with A_shadow_glob | change a with A_GOT_uar | change a with A_uar_glob | change a with A_GOT_rgb_newgif ];
keptJ HJc HJx AG Usp E10 RF E55 Hfin HfinS FFS Kg Kg2 Kc Kc2 Kgu Kgu2 Ku Ku2 Vg Vg2 EFA HFP HFSP HCP F fptac
| |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 10%nat) _ _ _ _ _) =>
eapply (rg_region_kept_frame_sub _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 10%nat); [exact HJc | evalE AG; first [exact E10 | rewrite E10; apply unsigned_lit_small; lia] | exact HfinS
| rewrite ?EFA; lia | rewrite ?EFA; lia
| first [let a := fresh "a" in let Ha := fresh "Ha" in let Hn := fresh "Hn" in intros a Ha Hn; exact (inFP_nil _ Hn) | fptac]
| let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; first [lia | apply (fun H => proj1 (HCP a H)); lia] ]
| |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 42%nat) _ _ _ _ _) =>
eapply (rg_region_kept_frame_sub _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 42%nat); [exact HJc | evalE AG; first [exact RF | rewrite RF; apply unsigned_lit_small; lia] | exact Hfin
| rewrite ?EFA; fold F; change (fs_frame_bytes 1) with 128; lia | rewrite ?EFA; fold F; change (fs_frame_bytes 1) with 128; lia
| first [let a := fresh "a" in let Ha := fresh "Ha" in let Hn := fresh "Hn" in intros a Ha Hn; exact (inFP_nil _ Hn) | fptac]
| let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; apply (fun H => proj1 (HFP a H)); lia ]
| |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 55%nat) _ _ _ _ _) =>
eapply (rg_region_kept_fshadow_sub _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 55%nat); [exact HJc | evalE AG; first [exact E55 | rewrite E55; apply unsigned_lit_small; unfold SB; lia] | exact Hfin
| rewrite ?EFA; fold F; unfold shadow_addr; rewrite <- SB_SHADOW_OFF; unfold SB; lia | rewrite ?EFA; fold F; unfold shadow_addr; rewrite <- SB_SHADOW_OFF; change (fs_frame_bytes 1 / 8) with 16; unfold SB; lia
| first [let a := fresh "a" in let Ha := fresh "Ha" in let Hn := fresh "Hn" in intros a Ha Hn; exact (inFP_nil _ Hn) | fptac]
| let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; unfold SB in Ha; lia ]
| |- region_kept _ _ _ _ (YQ0b.mkRegion (Some ?nb) _ _ _ _ ?cs) =>
match goal with Rb : ew _ nb = Z_to_bv 64 ?b, Hin : In (?b', ?sz) (ablocks _ _ _), Hin2 : In (?b'', ?sz') (ablocks _ _ _) |- _ =>
constr_eq b b'; constr_eq b b''; constr_eq sz sz';
let L := rnLAWS in eapply (rg_region_kept_block_subw2 _ L); [exact HJc | evalE AG; first [exact Rb | rewrite Rb; apply unsigned_lit_small; lia] | exact Hin | exact Hin2
| clear; lia | let v := eval vm_compute in (req_size sz) in change (req_size sz) with v; clear; lia | clear; lia | clear; lia
| first [let a := fresh "a" in let Ha := fresh "Ha" in let Hn := fresh "Hn" in intros a Ha Hn; exact (inFP_nil _ Hn) | fptac] ] end
end.
Ltac obl_blk HJx HEn HEbx Hin :=
let L := rnLAWS in
lazymatch goal with |- range_addressable _ (U ?Ex (SOff ?bx 0)) (U _ (SOff ?n ?c)) ?len =>
lazymatch type of HEn with _ = Z_to_bv 64 ?p =>
lazymatch type of Hin with In (_, ?sz) _ =>
first [ rewrite (U_atom_off Ex n p c); [| cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact HEn | lia | lia]
| rewrite (U_atom Ex n p); [| cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact HEn | lia] ];
eapply (obl_of_block trbsegs _ L _ _ _ _ _ Ex (SOff bx 0) _ len p sz (proj1 HJx) Hin);
[ rewrite (U_atom Ex bx SB); [reflexivity | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact HEbx | unfold SB; lia]
| lia | let v := eval vm_compute in (req_size sz) in change (req_size sz) with v; lia ] end end end.
Section q. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section u.
Variable B : asyms.
Hypothesis TL : TrbLib B.
Hypothesis LAWS : AR_laws trbsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis AMALLOC : amalloc_realizes trbsegs B.
Hypothesis AFREE : afree_realizes trbsegs B.
Hypothesis AMEMSET : aintrin_realizes trbsegs B OSet A_asan_memset.
Hypothesis AMEMCPY : aintrin_realizes trbsegs B OCpy A_asan_memcpy.
Hypothesis ASM1 : astack_malloc_realizes trbsegs B 1.
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis ASF : astack_free_law trbsegs B.
Hypothesis FFL : frame_flag_lawP trbsegs B.
Hypothesis NEWGIF : tnewgif_spec B.
Let HBcode := tl_code B TL. Let HBgot := tl_got_shadow B TL. Let HBcell := tl_shadow_cell B TL.
Let HBguar := tl_got_uar B TL. Let HBuar := tl_uar_cell B TL. Let errno_low := tl_env B TL.
Local Notation code := (as_code B).
Lemma rg_val_mem_zero : forall H (m : word -> option byte) a (n : nat),
(forall i, 0 <= i < Z.of_nat n -> aview trbsegs H m (a + i) = Some 0) -> val_mem trbsegs (mrestrict H m) a n 0.
Proof.
intros H m a n Hz j Hj. destruct (aview_byte trbsegs H m (a + Z.of_nat j) 0 (Hz (Z.of_nat j) ltac:(lia))) as (b & Hb & Hv & _).
rewrite Hb. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned. unfold YP0g.le_byte, bv_wrap.
rewrite Z.mod_0_l by (apply Z.pow_nonzero; lia). rewrite Z.shiftr_0_l. rewrite Z.mod_0_l by (vm_compute; discriminate). lia.
Qed.
Lemma rg_val_of_chunk_any : forall E mem base off (n : N) (e : sv),
YQ0b.chunk_ok trbsegs E mem base (YQ0b.mkChunk off (CVal n e)) -> (Z.of_N n <= 8) ->
val_mem trbsegs mem (base + off) (N.to_nat n) (bv_unsigned (sv_denot E e) mod 2 ^ (8 * Z.of_N n)).
Proof.
intros E mem base off n e H Hn k Hk. unfold YQ0b.chunk_ok in H. cbn [YQ0b.c_off YQ0b.c_val YQ0b.c_len YQ0b.cv_len] in H.
pose proof (N_nat_Z n) as Hnn.
destruct (H (Z.of_nat k) ltac:(lia)) as (b & Hb1 & Hb2). cbn [YQ0b.cbyte] in Hb1.
unfold YQ0b.byte_of_word in Hb1. injection Hb1 as <-. rewrite Hb2. f_equal.
apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with (2 ^ 8).
unfold YP0g.le_byte. rewrite N_nat_Z. rewrite Z.mod_mod by lia.
set (v := bv_unsigned (sv_denot E e)).
rewrite !Z.shiftr_div_pow2 by lia.
apply Z.bits_inj'. intros m Hm.
destruct (Z_lt_le_dec m 8) as [Hm8|Hm8].
- rewrite !Z.mod_pow2_bits_low by lia. rewrite !Z.div_pow2_bits by lia.
assert (Hlt : m + 8 * Z.of_nat k < 8 * Z.of_N n) by nia.
rewrite !(Z.mod_pow2_bits_low _ _ _ Hlt). reflexivity.
- rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.
Lemma rg_field_of_region_any : forall E m n b cs lo hi wlo whi od (w : N) e,
region_ok trbsegs E m (YQ0b.mkRegion (Some n) lo hi wlo whi cs) ->
bv_unsigned (ew E n) = b -> In (YQ0b.mkChunk od (CVal w e)) cs -> (Z.of_N w <= 8) ->
val_mem trbsegs m (b + od) (N.to_nat w) (bv_unsigned (sv_denot E e) mod 2 ^ (8 * Z.of_N w)).
Proof.
intros E m n b cs lo hi wlo whi od w e (_ & _ & _ & Hcs) Hn Hc Hw.
pose proof (proj1 (Forall_forall _ _) Hcs _ Hc) as Hck. cbn [YQ0b.r_base base_val] in Hck. rewrite Hn in Hck.
exact (rg_val_of_chunk_any E m b od w e Hck Hw).
Qed.
Lemma rg_U_sext16_mod : forall E a v, U E a = v -> 0 <= v < 2 ^ 16 -> U E (SExt true 16 a) mod 2 ^ 16 = v.
Proof.
intros E a v Ha Hv. rewrite U_SExt, Ha. change (2 ^ Z.of_N 16) with (2 ^ 16). rewrite (Z.mod_small v) by lia.
unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 16) with (2 ^ 16). change (2 ^ 16 / 2) with (2 ^ 15).
unfold zcanon, M64.
destruct (Z_lt_ge_dec v (2 ^ 15)) as [Hl | Hh].
- rewrite (Z.mod_small (v + 2 ^ 15)) by lia. replace (v + 2 ^ 15 - 2 ^ 15) with v by lia. rewrite (Z.mod_small v) by lia. apply Z.mod_small. lia.
- replace ((v + 2 ^ 15) mod 2 ^ 16) with (v + 2 ^ 15 - 2 ^ 16).
2:{ replace (v + 2 ^ 15) with ((v + 2 ^ 15 - 2 ^ 16) + 1 * 2 ^ 16) at 2 by lia. rewrite Z_mod_plus_full. rewrite Z.mod_small by lia. reflexivity. }
replace (v + 2 ^ 15 - 2 ^ 16 - 2 ^ 15) with ((v - 2 ^ 16 + 2 ^ 64) + (-1) * 2 ^ 64) by lia. rewrite Z_mod_plus_full.
rewrite (Z.mod_small (v - 2 ^ 16 + 2 ^ 64)) by lia.
replace (v - 2 ^ 16 + 2 ^ 64) with (v + (2 ^ 48 - 1) * 2 ^ 16) by lia. rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.
Lemma rg_kept_of_frame : forall E rs H (m m' : word -> option byte) (Zs : Z -> Prop),
frame_of E rs (mrestrict H m) (mrestrict H m') ->
(forall b wlo whi a, In (b, wlo, whi) (windows rs) -> base_val E b + wlo <= a < base_val E b + whi -> Zs a) ->
forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> aview trbsegs H m' a = aview trbsegs H m a.
Proof.
intros E rs H m m' Zs HFR Hw a Ha Hn. apply (aview_eq_of trbsegs). apply HFR. rewrite unsigned_lit_small by lia.
intros Hin. destruct (in_wrange_windows E rs a Hin) as (b & wlo & whi & Hi & Hr). exact (Hn (Hw b wlo whi a Hi Hr)).
Qed.
Lemma rg_awr_byte_callee0 : forall STK STK' sp sp' (bl0 bl0' blc : list (Z * Z)) lyq lyq' a,
awr_byte STK' sp' [] bl0' blc lyq' [] a -> sp - STK <= sp' - STK' -> sp' <= sp -> (forall b, In b bl0 -> In b bl0') ->
awr_byte STK sp [] bl0 blc lyq [] a.
Proof.
intros STK STK' sp sp' bl0 bl0' blc lyq lyq' a [H | [[Hf _] | [(b & n & Hin & Hn0 & Hb) | (c & p & Hin & _)]]] H1 H2 Hsub.
- left. lia.
- exfalso. exact (inFP_nil _ Hf).
- right; right; left. exists b, n. split; [exact Hin|]. split; [intros Hc; exact (Hn0 (Hsub _ Hc)) | exact Hb].
- destruct Hin.
Qed.
Theorem trb_cgif_rgb_newgif : trgb_newgif_spec B.
Proof.
unfold trgb_newgif_spec.
intros ly S W regs mem md ch cfgp attr gen loops Wd Hd HPRE Hal32 Hctx Hroom Htop32 HROD H10 HFO Hcfg HWH Hev Hlive.
pose proof Hwx_tfa as Hwx. pose proof trb_segs_low as Hsegs.
pose proof (rng_entry B TL LAWS W ly S regs mem md ch cfgp attr gen loops Wd Hd HPRE Hal32 HROD H10 HFO Hcfg) as HS.
pose proof (ajournal_init trbsegs B TRGBNEWGIF_STK [] ly S W regs mem md ch HPRE) as HJ.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5). assert (FFS : TRGBNEWGIF_STK = 16864) by reflexivity.
assert (Hes : ESTACK = 4096) by reflexivity.
assert (HEV : EV_RGBNEWGIF = 14) by reflexivity.
cbn [CTX_cgif_rgb_newgif In] in Hctx.
assert (Hra88 : 0x81498 = raZ regs) by (destruct Hctx as [H | [H | []]]; injection H as Hr Hs; exact Hr).
assert (Hspine : spine ch = [] \/ spine ch = [0x8116c])
by (destruct Hctx as [H | [H | []]]; injection H as Hr Hs; rewrite <- Hs; [left | right]; reflexivity).
remember (Ereg regs (rng_extra attr gen loops Wd Hd)) as E eqn:HE.
assert (E2 : ew E 2 = getr regs 2) by (subst E; exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
unfold cfg_at. change (w64 A_cgif_rgb_newgif) with (Z_to_bv 64 A_cgif_rgb_newgif).
shok_auto SHOK RBx E (mrestrict (w_H W) mem).
aj_run_tok trbtbl_lib_ok HS HJ SHOK RBspan. { awr_ok_tac. exact Usp. }
lazymatch type of HFr with frame_of ?Ef ?rs (mrestrict _ _) (mrestrict _ (ms_mem ?msX)) =>
assert (HUP : forall a, spZ regs <= a < 2 ^ 64 -> aview trbsegs (w_H W) (ms_mem msX) a = aview trbsegs (w_H W) mem a);
[ eapply (aview_kept_frame Ef rs _ _ _ (spZ regs) HFr); [lia|];
intros a Ha (rg & Hin & Hrg);
lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In rg rs1) in Hin end; cbn [In] in Hin;
repeat (destruct Hin as [<- | Hin]; [cbn [YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi base_val] in Hrg; rewrite ?Usp in Hrg; lia|]);
destruct Hin | ] end.
clear HF HFr HG.
aconsts HROD HJ Kgot0 Kcell0 Kguar0 Kuar0 Vgr0.
destruct HFO as ((cid & pos & Hfin & Hcid0 & Hfal & Hflo & Hfhi) & Hcal & HRA). unfold RGBCONFIG_SIZE in Hfhi, HRA.
destruct (frames_bounds trbsegs B LAWS ly S W mem md cid pos HAR Hfin) as (Hf4096 & Hfceil & Hfhigh).
pose proof (frm_off_img _ _ _ _ _ _ _ _ HAR Hfin) as Hfhigh_img.
assert (EFA0 : forall c p, frame_addr ly c p = frame_addr ly c p) by reflexivity.
assert (E10 : ew E 10 = Z_to_bv 64 cfgp) by (subst E; rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E3 : ew E 3 = getr regs 3) by (subst E; exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (subst E; exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (E35 : ew E 35 = Z_to_bv 64 SB) by (subst E; exact (ew_Ereg_extra regs _ 3)).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r) by (intros n r Hn; rewrite HE; apply ew_Ereg_nat; exact Hn).
assert (E32 : ew E 32 = Z_to_bv 64 attr) by (subst E; exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 gen) by (subst E; exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 loops) by (subst E; exact (ew_Ereg_extra regs _ 2)).
assert (E36 : ew E 36 = Z_to_bv 64 Wd) by (subst E; exact (ew_Ereg_extra regs _ 4)).
assert (E37 : ew E 37 = Z_to_bv 64 Hd) by (subst E; exact (ew_Ereg_extra regs _ 5)).
pose proof Hcfg as Hcfg'. cbn [obj_at LAY_RgbConfig] in Hcfg'.
destruct Hcfg' as ([CV0 _] & [CV8 _] & [CV16 _] & [CV24 CR24] & [CV28 CR28] & [CV32 CR32] & [CV34 CR34] & [CV36 CR36] & _).
cbn [fst snd Z.of_N N.to_nat] in CV0, CV8, CV16, CV24, CV28, CV32, CV34, CV36, CR24, CR28, CR32, CR34, CR36. change (2 ^ (8 * 4)) with (2 ^ 32) in *. change (2 ^ (8 * 2)) with (2 ^ 16) in *.
clear HE.
rreg HS (2%bv : bv 5) Q2. rreg HS (3%bv : bv 5) Q3. rreg HS (4%bv : bv 5) Q4. rreg HS (1%bv : bv 5) Q1.
rewrite (st_ok_restrict_mkst trbsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
replace 250224 with (pc_stack_malloc code 1) by (rewrite HBcode; reflexivity).
pose proof (count_cid_le_length 1 (frames S)) as Hcnt.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
eapply (aj_stack_malloc_at trbsegs B LAWS Hsegs errno_low ML SMP 1 ASM1 ltac:(lia) W (ms_regs msX) (ms_mem msX) TRGBNEWGIF_STK (spZ regs) [] ly S W mem md [] ly S _ 0 (-96) _ HJ) end.
- unfold spZ. rewrite Q2, E2. fold (spZ regs). rewrite unsigned_lit_small by lia. lia.
- reflexivity. - lia. - rewrite FFS, Hes; lia.
- rewrite Q3, E3. exact Hgp. - rewrite Q4, E4. exact Htp.
- exact Q1. - vm_compute. reflexivity.
- change (fs_frames 1) with 8192. lia. }
cbv beta. clear Q2 Q3 Q4 Q1 HJ SHOK.
intros W2 c2 _ (-> & S2 & regs2 & mem2 & md2 & fpos & -> & HJ2 & HP2 & Ha0 & Eab & Hfrs2 & Hnin & Hnev2 & Hbb2 & Hz & Hflag & HK).
rewrite Hes in HK. replace (spZ regs + -96 - 4096) with (spZ regs - 4192) in HK by lia. replace (spZ regs + -96) with (spZ regs - 96) in HK by lia.
assert (HUP2 : forall a, spZ regs <= a < 2 ^ 64 -> aview trbsegs (w_H W) mem2 a = aview trbsegs (w_H W) mem a).
{ intros a Ha. rewrite <- (HUP a Ha). pose proof HK as (K1 & _). apply K1; lia. }
clear HUP.
aconsts HROD HJ2 Kgot2 Kcell2 Kguar2 Kuar2 Vgr2.
pose proof (proj1 HJ2) as HAR2.
assert (Hfin2 : In (1, fpos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
assert (HfinS2 : In (cid, pos) (frames S2)) by (rewrite Hfrs2; right; exact Hfin).
destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos HAR2 Hfin2) as (HFal & [HFhi _] & HFpres & HFSpres).
destruct (frames_bounds trbsegs B LAWS _ _ _ _ _ 1 fpos HAR2 Hfin2) as (HF4096 & HFceil & HFhigh).
pose proof (frm_off_img _ _ _ _ _ _ _ _ HAR2 Hfin2) as HFhigh_img.
change (fs_frame_bytes 1) with 128 in *.
set (F := frame_addr ly 1 fpos) in *. set (FL := flag_addr ly 1 fpos) in *.
destruct (in_split _ _ Hfin) as (fl1 & fl2 & Efl).
pose proof (sep_frames_pos trbsegs B LAWS ly S2 W mem2 md2 (1, fpos) (cid, pos) [] fl1 fl2 HAR2 ltac:(rewrite Hfrs2, Efl; reflexivity)) as HdFC.
unfold zdisjoint, frame_rng in HdFC. cbn [fst snd] in HdFC. change (fs_frame_bytes 1) with 128 in HdFC. fold F in HdFC.
assert (AG : forall n, (n < 33)%nat -> ew E n = ew E n) by (intros; reflexivity).
reseat HS HJ2 HP2 [0; 1; 2; 3; 4; 5; 6]%nat AG
ltac:(idtac; first [ keptR HK HJ2 AG Usp E10 Hfin Kgot0 Kgot2 Kcell0 Kcell2 Kguar0 Kguar2 Kuar0 Kuar2 Vgr0 Vgr2 EFA0 | match goal with |- ?g => idtac "KEPTFAIL" g end; fail ]).
rreg HS (10%bv : bv 5) RF. cbn [ms_regs] in RF. rewrite Ha0 in RF. symmetry in RF. unfold w64 in RF. fold F in RF.
lazymatch type of HS with st_ok _ ?Ev ?ssv ?msv =>
pose proof (st_ok_agree trbsegs 54 Ev (havoc Ev 54 [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)]) ssv msv HS
(env_agree_havoc_ge 54 54 Ev Ev _ ltac:(lia) (env_agree_refl 54 Ev)) ltac:(vm_compute; reflexivity)) as HS3 end.
clear HS. rename HS3 into HS. rebaseE HS AG HEv.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
assert (E54 : ew Ev 54 = Z_to_bv 64 FL) by (rewrite HEv; exact (ew_havoc_new _ 54 [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] 0 (Z_to_bv 64 0) ltac:(cbn; lia)));
assert (E55 : ew Ev 55 = Z_to_bv 64 (SB + F / 8)) by (rewrite HEv; exact (ew_havoc_new _ 54 [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] 1 (Z_to_bv 64 0) ltac:(cbn; lia))) end.
clear HEv.
assert (HFq : F = 32 * (F / 32)) by (pose proof (Z.div_mod F 32 ltac:(lia)); lia).
assert (HF8 : F / 8 = 4 * (F / 32)) by (rewrite HFq at 1; replace (32 * (F / 32)) with (4 * (F / 32) * 8) by lia; rewrite Z.div_mul by lia; reflexivity).
assert (HF8lo : 512 <= F / 8) by (apply Z.div_le_lower_bound; lia).
assert (HF8hi : F / 8 < 17592186044416) by (apply Z.div_lt_upper_bound; lia).
destruct (FFL ly S2 W mem2 md2 1 fpos HAR2 Hfin2) as (HFLpres & HFLown & HFLrng). fold FL in HFLpres, HFLown, HFLrng.
assert (HFrng : 0 <= F < 2 ^ 64) by (clear - HF4096 HFceil C1; lia).
lazymatch type of HS with st_ok _ ?Ev _ _ =>
pose proof (st_ok_add_fact trbsegs Ev _ _ 42 (HPTR 5) HS
ltac:(unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite RF, unsigned_lit_small by lia; change (2 ^ 5) with 32; lia)) as HS3;
clear HS; rename HS3 into HS;
pose proof (st_ok_add_fact trbsegs Ev _ _ 54 (HPTR 0) HS
ltac:(unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite E54, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia)) as HS3;
clear HS; rename HS3 into HS;
pose proof (st_ok_add_fact trbsegs Ev _ _ 55 (mkAF (SB + 512) (SB + 17592186044416) 2) HS
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E55, unsigned_lit_small by (unfold SB; lia); change (2 ^ 2) with 4; unfold SB;
split; [lia|]; split; [rewrite HF8; replace (2147450880 + 4 * (F / 32)) with ((536862720 + F / 32) * 4) by lia; apply Z_mod_mult | lia])) as HS3;
clear HS; rename HS3 into HS;
pose proof (st_ok_add_alias trbsegs Ev _ _ _ _ HS (shadow_decl_ok Ev 42 35 55 F SB RF HFrng E35 E55)) as HS3;
clear HS; rename HS3 into HS;
pose proof (ast_ok_add_region trbsegs Ev _ _ (fframe_region 42 54 1 []) HS eq_refl
ltac:(unfold region_ok, fframe_region; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val ms_mem restrict mkst app];
change (fs_frame_bytes 1) with 128; rewrite RF, unsigned_lit_small by lia; split; [lia|]; split; [lia|]; split;
[ intros o Ho; apply (apresent_writable trbsegs); apply (proj1 (HFpres (F + o) ltac:(lia)))
| apply Forall_cons; [|apply Forall_nil]; apply (chunk_ok_val trbsegs Ev _ F (128 - 8) 8 _ FL);
[cbn [sv_denot]; rewrite E54, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | replace (F + (128 - 8)) with (F + 128 - 8) by lia; exact (val_mem_of_rdword trbsegs _ _ _ _ Hflag)] ])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint, fframe_region; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val];
change (fs_frame_bytes 1) with 128;
rewrite RF, ?(AG 2%nat), ?(AG 10%nat), ?Usp, ?E10, !unsigned_lit_small by lia; unfold A_GOT_shadow, A_shadow_glob, A_GOT_uar, A_uar_glob, A_GOT_rgb_newgif;
repeat split; zone_lia)) as HS3;
clear HS; rename HS3 into HS end.
assert (ZS : forall j, 0 <= j < 2 -> val_mem trbsegs (mrestrict (w_H W) mem2) (SB + F / 8 + 8 * j) 8 0).
{ intros j Hj. apply val_mem_zero8. intros i Hi. unfold zero_shadow, shadow_of_addr in Hz. rewrite <- SB_SHADOW_OFF in Hz.
replace (SB + F / 8 + 8 * j + i) with (SB + F / 8 + (8 * j + i)) by lia. apply Hz. change (128 / 8) with 16. lia. }
lazymatch type of HS with st_ok _ ?Ev _ _ =>
pose proof (ast_ok_add_region trbsegs Ev _ _
(fshadow_region 55 1 0 16 [YQ0b.mkChunk 0 (CVal 8 (SLit 0)); YQ0b.mkChunk 8 (CVal 8 (SLit 0))]) HS eq_refl
ltac:(unfold region_ok, fshadow_region; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val ms_mem restrict mkst app];
change (fs_frame_bytes 1 / 8) with 16; rewrite E55, unsigned_lit_small by (unfold SB; lia); split; [unfold SB; lia|]; split; [unfold SB; lia|]; split;
[ intros o Ho; apply (apresent_writable trbsegs); unfold shadow_addr in HFSpres; rewrite <- SB_SHADOW_OFF in HFSpres;
apply (proj1 (HFSpres o ltac:(change (128 / 8) with 16; lia)))
| apply Forall_cons; [apply (chunk_ok_val trbsegs Ev _ (SB + F / 8) 0 8 _ 0); [reflexivity | zside | zside | rewrite Z.add_0_r; replace (SB + F / 8) with (SB + F / 8 + 8 * 0) by lia; apply ZS; lia]|];
apply Forall_cons; [apply (chunk_ok_val trbsegs Ev _ (SB + F / 8) 8 8 _ 0); [reflexivity | zside | zside | replace (SB + F / 8 + 8) with (SB + F / 8 + 8 * 1) by lia; apply ZS; lia]|];
apply Forall_nil ])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint, fshadow_region; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val];
change (fs_frame_bytes 1 / 8) with 16;
rewrite E55, RF, ?(AG 2%nat), ?(AG 10%nat), ?Usp, ?E10, !unsigned_lit_small by (unfold SB; lia);
unfold A_GOT_shadow, A_shadow_glob, A_GOT_uar, A_uar_glob, A_GOT_rgb_newgif, SB; repeat split; zone_lia)) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS.
aj_run_to_sh trbtbl_lib_ok HS HJ2 A_asan_memset. { awrR AG fpos F EFA0 42%nat 55%nat. }
upd_above HUP2 HFr AG. rename HUP2 into HUP.
clear HF HFr HG.
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
pose proof (st_ok_region_nth Ex ssx (restrict (w_H W) msX) 0 _ HS eq_refl) as HRfs; cbn [ms_mem restrict] in HRfs;
lazymatch type of HRfs with region_ok _ _ _ (YQ0b.mkRegion (Some 55%nat) ?lo ?hi ?wlo ?whi ?cs) =>
assert (ZS5 : forall j, 4 <= j <= 9 -> val_mem trbsegs (mrestrict (w_H W) (ms_mem msX)) (SB + F / 8 + j) 1 0);
[ intros j Hj;
assert (Hj5 : j = 4 \/ j = 5 \/ j = 6 \/ j = 7 \/ j = 8 \/ j = 9) by lia;
destruct Hj5 as [-> | [-> | [-> | [-> | [-> | ->]]]]];
(eapply (field_of_region Ex _ 55 (SB + F / 8) cs lo hi wlo whi _ 1%N (SLit 0) 0 HRfs);
[evalE AG | cbn; tauto | reflexivity | cbn; lia | cbn; lia])
| ] end;
clear HRfs;
assert (HRA48 : range_addressable (aview trbsegs (w_H W) (ms_mem msX)) SHADOW_OFF (F + 32) 48);
[ apply zero_shadow_range; [rewrite HFq; replace (32 * (F / 32) + 32) with ((4 * (F / 32) + 4) * 8) by lia; apply Z_mod_mult | reflexivity |];
intros i Hi; change (48 / 8) with 6 in Hi; unfold shadow_of_addr; rewrite <- SB_SHADOW_OFF;
replace (SB + (F + 32) / 8 + i) with (SB + F / 8 + (4 + i)) by (rewrite HFq at 2; rewrite HF8; replace (32 * (F / 32) + 32) with ((4 * (F / 32) + 4) * 8) by lia; rewrite Z.div_mul by lia; lia);
apply (aview_of_val_mem1 trbsegs); [apply ZS5; lia | lia]
| ] end.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msX) =>
assert (Hpres2F : forall a, F <= a < F + 128 -> apresent (w_H W) (ms_mem msX) a) end.
{ destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos (proj1 HJ2) Hfin2) as (_ & _ & HFpresX & _). change (fs_frame_bytes 1) with 128 in HFpresX. fold F in HFpresX.
intros a Ha. exact (proj1 (HFpresX a Ha)). }
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs 42%nat in let i := eval vm_compute in i in
pose proof (st_ok_submem trbsegs Ex ssx msx (firstn i (ss_mem ssx) ++ trim_lo (nth i (ss_mem ssx) got_region) 80 :: skipn (Datatypes.S i) (ss_mem ssx)) HS
ltac:(cbn [ss_mem nth skipn firstn app]; repeat (apply submem_keep; [first [apply subregion_trim_lo | apply subregion_refl]|]); apply submem_refl)
ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS.
lazymatch type of HS with st_ok _ ?Ex _ _ =>
pose proof (ast_ok_add_region trbsegs Ex _ _ (YQ0b.mkRegion (Some 42%nat) 0 32 0 32 []) HS eq_refl
ltac:(unfold region_ok; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val ms_mem restrict mkst];
cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia;
rewrite RF, unsigned_lit_small by lia; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
intros o Ho; apply (apresent_writable trbsegs); apply Hpres2F; lia)
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val];
rewrite RF; evalE AG; unfold A_GOT_shadow, A_shadow_glob, A_GOT_uar, A_uar_glob, A_GOT_rgb_newgif; repeat split; first [zone_lia | match goal with |- ?g => idtac "DISJ" g; fail end])) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS.
rreg HS (10%bv : bv 5) Ra0. rreg HS (11%bv : bv 5) Ra1. rreg HS (12%bv : bv 5) Ra2. rreg HS (1%bv : bv 5) Rra.
rreg HS (2%bv : bv 5) Rsp. rreg HS (3%bv : bv 5) Rgp. rreg HS (4%bv : bv 5) Rtp.
rewrite (st_ok_restrict_mkst trbsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
change (Z_to_bv 64 337168) with (Z_to_bv 64 A_asan_memset).
clear Kgot2 Kcell2 Kguar2 Kuar2 Vgr2. aconsts HROD HJ2 Kgot2 Kcell2 Kguar2 Kuar2 Vgr2.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
eapply (aj_intrin_at trbsegs B LAWS Hsegs OSet A_asan_memset AMEMSET _ (ms_regs msX) (ms_mem msX) TRGBNEWGIF_STK (spZ regs) [] ly S W mem md [(1, fpos)]
ly S2 _ _ (F + 32) 0 48 (-96) (Z_to_bv 64 0x81bc0) HJ2) end.
- rewrite Ra0. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite RF. unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
- exact Ra1.
- exact Ra2.
- lia. - lia. - lia.
- unfold spZ at 1. rewrite Rsp. evalE AG.
- reflexivity. - lia. - rewrite FFS. unfold ESTACK. lia.
- rewrite Rgp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (AG 3%nat) by lia. rewrite (EE 3%nat 3%bv eq_refl). exact Hgp.
- rewrite Rtp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (AG 4%nat) by lia. rewrite (EE 4%nat 4%bv eq_refl). exact Htp.
- exact Rra.
- vm_compute. reflexivity.
- intros a Ha. split; [| unfold ESTACK; lia]. right. right. right. exists 1, fpos. split; [left; reflexivity|]. left.
unfold in_zr, frame_rng. cbn [fst snd]. change (fs_frame_bytes 1) with 128. fold F. lia.
- apply amem_range_high; [clear; lia | destruct HFhigh as [_ HFz]; unfold kLowShadowBeg, kHighMemBeg in HFz; clear - HFz; lia | clear - HFceil; lia].
- apply (range_addressable_sub _ _ _ _ _ _ HRA48); lia.
- intros _. eapply (shadow_hull_vis_of_frame trbsegs B LAWS ly S2 _ _ _ 1 fpos (F + 32) 48 (proj1 HJ2) Hfin2);
[fold F; lia | fold F; change (fs_frame_bytes 1) with 128; lia | lia].
- exact I. }
cbv beta. intros W4 c4 _ (-> & regs4 & mem4 & md4 & -> & HJ4 & HP4 & Ha04 & Heff & Hfr4 & Hpres4).
clear Ra0 Ra1 Ra2 Rra Rsp Rgp Rtp ZS5.
aconsts HROD HJ4 Kgot4 Kcell4 Kguar4 Kuar4 Vgr4.
reseat HS HJ4 HP4 [0; 1; 2; 3; 4; 5; 6; 7; 8; 9]%nat AG
ltac:(idtac; first [ keptI Hfr4 Hpres4 AG Kgot2 Kgot4 Kcell2 Kcell4 Kguar2 Kguar4 Kuar2 Kuar4 Vgr2 Vgr4
| match goal with |- ?g => idtac "KEPTFAIL" g end ]).
destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos (proj1 HJ4) Hfin2) as (_ & _ & HFpres4' & _). change (fs_frame_bytes 1) with 128 in HFpres4'. fold F in HFpres4'.
assert (ZC : forall off (n : nat), 32 <= off -> off + Z.of_nat n <= 80 -> val_mem trbsegs (mrestrict (w_H W) mem4) (F + off) n 0).
{ intros off n Ho1 Ho2. apply rg_val_mem_zero. intros i Hi. replace (F + off + i) with (F + 32 + (off - 32 + i)) by lia. rewrite (Heff (off - 32 + i)) by lia. reflexivity. }
lazymatch type of HS with st_ok _ ?Ev _ _ =>
pose proof (ast_ok_add_region trbsegs Ev _ _
(YQ0b.mkRegion (Some 42%nat) 32 80 32 80
[YQ0b.mkChunk 32 (CVal 8 (SLit 0)); YQ0b.mkChunk 40 (CVal 8 (SLit 0)); YQ0b.mkChunk 48 (CVal 4 (SLit 0)); YQ0b.mkChunk 52 (CVal 4 (SLit 0));
YQ0b.mkChunk 56 (CVal 2 (SLit 0)); YQ0b.mkChunk 58 (CVal 2 (SLit 0)); YQ0b.mkChunk 60 (CVal 2 (SLit 0)); YQ0b.mkChunk 62 (CVal 2 (SLit 0));
YQ0b.mkChunk 64 (CVal 8 (SLit 0)); YQ0b.mkChunk 72 (CVal 8 (SLit 0))]) HS eq_refl
ltac:(unfold region_ok; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val ms_mem restrict mkst];
cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia;
rewrite RF, unsigned_lit_small by lia; split; [lia|]; split; [lia|]; split;
[ intros o Ho; apply (apresent_writable trbsegs); apply (proj1 (HFpres4' (F + o) ltac:(lia)))
| repeat (apply Forall_cons; [eapply (chunk_ok_val trbsegs Ev _ F _ _ (SLit 0) 0); [reflexivity | zside | zside | apply ZC; cbn; lia] |]); apply Forall_nil ])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val];
rewrite RF; evalE AG; unfold A_GOT_shadow, A_shadow_glob, A_GOT_uar, A_uar_glob, A_GOT_rgb_newgif; repeat split; first [zone_lia | match goal with |- ?g => idtac "DISJ" g; fail end])) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS. clear_frames.
assert (HUP4 : forall a, spZ regs <= a < 2 ^ 64 -> aview trbsegs (w_H W) mem4 a = aview trbsegs (w_H W) mem a).
{ intros a Ha. rewrite <- (HUP a Ha). apply Hfr4; [lia | lia | unfold ESTACK; lia]. }
clear HUP. rename HUP4 into HUP.
lazymatch type of HS with st_ok _ _ _ (restrict _ (mkst ?rg ?pcx ?mm ?rm)) => change mm with (ms_mem (mkst rg pcx mm rm)) in HJ4 end.
aj_run_to_sh trbtbl_lib_ok HS HJ4 A_wrap_malloc. { awrR AG fpos F EFA0 42%nat 55%nat. }
upd_above HUP HFr AG. clear HF HFr HG.
clear Kgot4 Kcell4 Kguar4 Kuar4 Vgr4. aconsts HROD HJ4 Kgot4 Kcell4 Kguar4 Kuar4 Vgr4.
rreg HS (10%bv : bv 5) Ra0. rreg HS (1%bv : bv 5) Rra. rreg HS (2%bv : bv 5) Rsp. rreg HS (3%bv : bv 5) Rgp. rreg HS (4%bv : bv 5) Rtp. rreg HS (8%bv : bv 5) Rs0.
rng_chain HS HJ4 AG EE.
rewrite (st_ok_restrict_mkst trbsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
replace (Z_to_bv 64 340936) with (Z_to_bv 64 (pc_wrap_malloc (as_code B))) by (rewrite HBcode; vm_compute; reflexivity).
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
eapply (aj_malloc_at trbsegs B LAWS Hsegs errno_low ML AMALLOC _ (ms_regs msX) (ms_mem msX) TRGBNEWGIF_STK (spZ regs) [] ly S W mem md [(1, fpos)]
ly S2 _ 0 64 (-96) (Z_to_bv 64 0x81bc8) ((spZ regs, raZ regs, s0Z regs) :: ch) HJ4) end.
- exact Ra0.
- unfold MALLOC_MAX. lia.
- rewrite Hbb2. unfold LIVE_RGBNEWGIF, LIVE_NEWGIF, LIVE_MAX in *. lia.
- unfold spZ. rewrite Rsp. evalE AG.
- reflexivity.
- lia.
- rewrite FFS. unfold ASTACK. lia.
- rewrite Rgp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (AG 3%nat) by lia. rewrite (EE 3%nat 3%bv eq_refl). exact Hgp.
- rewrite Rtp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (AG 4%nat) by lia. rewrite (EE 4%nat 4%bv eq_refl). exact Htp.
- exact Rra.
- vm_compute. reflexivity.
- rewrite Hnev2. rewrite HEV in Hev. unfold VEV_MAX in *. lia.
- apply (achain_chain_pre ly _ (spZ regs - 96) (spZ regs) _ _ Hch1);
[ unfold spZ at 1 2; rewrite Rsp; evalE AG
| unfold s0Z; rewrite Rs0; evalE AG
| unfold raZ; rewrite Rra, unsigned_lit_small by lia; lia ].
- rewrite call_trace_of_spine. cbn [spine map fst snd]. fold (spine ch). unfold raZ at 1. rewrite Rra, unsigned_lit_small by lia. rewrite <- Hra88.
rewrite HBcode. rewrite (tl_universe B TL). apply TRACES_cgif_rgb_newgif_U. apply memZL_In.
destruct Hspine as [Hsp | Hsp]; rewrite Hsp; vm_compute; reflexivity. }
cbv beta. intros W5 c5 Hwle5 (ly5 & S5 & regs5 & mem5 & md5 & blk & -> & HJ5 & HP5 & Ha05 & Hfrs5 & Hres5).
clear Ra0 Rra Rsp Rgp Rtp Rs0 Hch1 HUPc Vra Vs0 Qceil Qal8 Qtop Qtop64 Qsp Qra Qs0.
destruct (mres_kept B ly S2 W _ W5 mem5 ly5 S5 _ _ blk 64 Hres5) as (HK5 & HBin5 & HblkIn).
pose proof (mres_range B LAWS ly5 S5 W5 mem5 md5 ly S2 blk 64 _ _ (proj1 HJ5) Hres5) as Hrng. change (req_size 64) with 64 in Hrng, HK5.
pose proof HJ5 as (HAR5 & Hly5 & _).
assert (EFA5 : forall c p, frame_addr ly5 c p = frame_addr ly c p)
by (intros c p; unfold frame_addr; destruct Hly5 as (_ & _ & _ & _ & _ & -> & _); reflexivity).
assert (EFL5 : forall c p, flag_addr ly5 c p = flag_addr ly c p)
by (intros c p; unfold flag_addr; destruct Hly5 as (_ & _ & _ & _ & _ & -> & _); reflexivity).
assert (Hfin5 : In (1, fpos) (frames S5)) by (rewrite Hfrs5; exact Hfin2).
assert (HfinS5 : In (cid, pos) (frames S5)) by (rewrite Hfrs5; exact HfinS2).
destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos HAR5 Hfin5) as (_ & _ & HFpres5 & HFSpres5). change (fs_frame_bytes 1) with 128 in HFpres5, HFSpres5.
change (128 / 8) with 16 in HFSpres5. rewrite EFA5 in HFpres5, HFSpres5. fold F in HFpres5, HFSpres5.
assert (HnewF : forall a, F <= a < F + 128 -> ~ (blk <> 0 /\ blk <= a < blk + 64)).
{ intros a Ha [Hnz Hin]. pose proof (sep_block_frame trbsegs B LAWS _ _ _ _ _ blk 64 1 fpos HAR5 (HblkIn Hnz) Hfin5) as Dd.
rewrite EFA5 in Dd. fold F in Dd. unfold zdisjoint in Dd. cbn [fst snd] in Dd. change (req_size 64) with 64 in Dd. change (fs_frame_bytes 1) with 128 in Dd. clear - Dd Ha Hin. lia. }
aconsts HROD HJ5 Kgot5 Kcell5 Kguar5 Kuar5 Vgr5.
destruct Hrng as [Hblk0 | (Hb4096 & Hbzone & Hbceil & Hb16 & HbIn)].
{
subst blk.
reseat HS HJ5 HP5 [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10]%nat AG
ltac:(idtac; first [ keptR HK5 HJ5 AG Usp E10 HfinS2 Kgot4 Kgot5 Kcell4 Kcell5 Kguar4 Kguar5 Kuar4 Kuar5 Vgr4 Vgr5 EFA0
| keptF HK5 AG RF E55 Hfin2 HFpres5 HFSpres5 HnewF F EFA0
| match goal with |- ?g => idtac "KEPTFAIL" g end; fail ]).
pose proof (st_ok_pin_reg' trbsegs _ _ _ (10%bv : bv 5) 0 HS ltac:(cbn [ms_regs restrict mkst]; rewrite Ha05; reflexivity) eq_refl) as HS3.
norm_ss HS3. clear HS. rename HS3 into HS.
lazymatch type of HS with st_ok _ _ _ (restrict _ (mkst ?rg ?pcx ?mm ?rm)) => change mm with (ms_mem (mkst rg pcx mm rm)) in HJ5 end.
exitG HS HJ5 AG fpos F cfgp E54 E55 Hfin5 HfinS5 EE Hra HEV EFA5 EFL5.
exists 0. split; [reflexivity|]. left. split; [reflexivity|].
unfold ablocks. rewrite blocks_stack_free_state. fold (ablocks B ly5 S5).
destruct Hres5 as [(_ & Ebl5 & _) | (Hnz & _)]; [| exfalso; clear - Hnz; lia]. rewrite Ebl5, Eab. apply Permutation_refl. }
destruct Hres5 as [(Hz5 & _) | (_ & Ebl5 & _)]; [exfalso; clear - Hz5 Hb4096; lia|].
assert (Hblk_in : In (blk, 64) (ablocks B ly5 S5)) by exact HbIn.
destruct (al_blocks _ _ LAWS _ _ _ _ _ blk 64 HAR5 Hblk_in) as (_ & _ & _ & Hbh_ia & Hbpres & _). change (req_size 64) with 64 in Hbh_ia, Hbpres.
pose proof (blk_off_img _ _ _ _ _ _ blk 64 HAR5 Hblk_in) as Hbh_img. change (req_size 64) with 64 in Hbh_img.
pose proof (aftok_new_block trbsegs B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ blk 64 HJ4 HAR5 Ebl5 ltac:(lia)) as Tblk.
assert (Ablk : forall blc lyq ownq i, In (blk, 64) blc -> 0 <= i < 64 -> awr_byte TRGBNEWGIF_STK (spZ regs) [] (ablocks B ly S) blc lyq ownq (blk + i)).
{ intros blc lyq ownq i Hbl Hi. exact (awr_new_block_any trbsegs B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ blk 64 blc i lyq ownq HJ4 HAR5 Ebl5 ltac:(lia) Hbl ltac:(change (req_size 64) with 64; lia)). }
pose proof (sep_block_frame trbsegs B LAWS ly5 S5 _ _ _ blk 64 1 fpos HAR5 Hblk_in Hfin5) as HdBF.
unfold zdisjoint in HdBF. cbn [fst snd] in HdBF. change (req_size 64) with 64 in HdBF. change (fs_frame_bytes 1) with 128 in HdBF. rewrite EFA5 in HdBF. fold F in HdBF.
pose proof (sep_block_frame trbsegs B LAWS ly5 S5 _ _ _ blk 64 cid pos HAR5 Hblk_in HfinS5) as HdBC.
unfold zdisjoint in HdBC. cbn [fst snd] in HdBC. change (req_size 64) with 64 in HdBC. rewrite EFA5 in HdBC.
reseat HS HJ5 HP5 [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10]%nat AG
ltac:(idtac; first [ keptR HK5 HJ5 AG Usp E10 HfinS2 Kgot4 Kgot5 Kcell4 Kcell5 Kguar4 Kguar5 Kuar4 Kuar5 Vgr4 Vgr5 EFA0
| keptF HK5 AG RF E55 Hfin2 HFpres5 HFSpres5 HnewF F EFA0
| match goal with |- ?g => idtac "KEPTFAIL" g end; fail ]).
rreg HS (10%bv : bv 5) Rblk. cbn [ms_regs] in Rblk. rewrite Ha05 in Rblk. symmetry in Rblk. unfold w64 in Rblk.
lazymatch type of Rblk with ew ?Ex ?nx = _ =>
pose proof (st_ok_add_fact trbsegs Ex _ _ nx (HPTR 4) HS
ltac:(unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite Rblk, unsigned_lit_small by lia; change (2 ^ 4) with 16; lia)) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS.
lazymatch type of HS with st_ok _ _ _ (restrict _ (mkst ?rg ?pcx ?mm ?rm)) => change mm with (ms_mem (mkst rg pcx mm rm)) in HJ5 end.
aj_run_to_sh trbtbl_lib_ok HS HJ5 A_asan_memset. { awrR AG fpos F EFA5 42%nat 55%nat. }
clear HF HFr HG.
rreg HS (10%bv : bv 5) Ra0. rreg HS (11%bv : bv 5) Ra1. rreg HS (12%bv : bv 5) Ra2. rreg HS (1%bv : bv 5) Rra.
rreg HS (2%bv : bv 5) Rsp. rreg HS (3%bv : bv 5) Rgp. rreg HS (4%bv : bv 5) Rtp.
rewrite (st_ok_restrict_mkst trbsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
change (Z_to_bv 64 337168) with (Z_to_bv 64 A_asan_memset).
clear Kgot5 Kcell5 Kguar5 Kuar5 Vgr5. aconsts HROD HJ5 Kgot5 Kcell5 Kguar5 Kuar5 Vgr5.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
eapply (aj_intrin_at trbsegs B LAWS Hsegs OSet A_asan_memset AMEMSET _ (ms_regs msX) (ms_mem msX) TRGBNEWGIF_STK (spZ regs) [] ly S W mem md [(1, fpos)]
ly5 S5 _ _ blk 0 64 (-96) (Z_to_bv 64 0x81bdc) HJ5) end.
- rewrite Ra0. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite Rblk. reflexivity.
- exact Ra1.
- exact Ra2.
- lia. - lia. - lia.
- unfold spZ at 1. rewrite Rsp. evalE AG.
- reflexivity. - lia. - rewrite FFS. unfold ESTACK. lia.
- rewrite Rgp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (AG 3%nat) by lia. rewrite (EE 3%nat 3%bv eq_refl). exact Hgp.
- rewrite Rtp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (AG 4%nat) by lia. rewrite (EE 4%nat 4%bv eq_refl). exact Htp.
- exact Rra.
- vm_compute. reflexivity.
- intros a Ha. split; [replace a with (blk + (a - blk)) by lia; apply Ablk; [exact Hblk_in | lia] | unfold ESTACK; lia].
- eapply (amem_range_of_block trbsegs B LAWS ly5 S5 _ _ _ blk 64 blk 64 (proj1 HJ5) Hblk_in); change (req_size 64) with 64; lia.
- eapply (range_addressable_of_block trbsegs B LAWS ly5 S5 _ _ _ blk 64 blk 64 (proj1 HJ5) Hblk_in); change (req_size 64) with 64; lia.
- intros _. eapply (shadow_hull_vis_of_block trbsegs B LAWS ly5 S5 _ _ _ blk 64 blk 64 (proj1 HJ5) Hblk_in); change (req_size 64) with 64; lia.
- exact I. }
cbv beta. intros W6 c6 _ (-> & regs6 & mem6 & md6 & -> & HJ6 & HP6 & Ha06 & Heff6 & Hfr6 & Hpres6).
clear Ra0 Ra1 Ra2 Rra Rsp Rgp Rtp.
aconsts HROD HJ6 Kgot6 Kcell6 Kguar6 Kuar6 Vgr6.
reseat HS HJ6 HP6 [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10]%nat AG
ltac:(idtac; first [ keptI Hfr6 Hpres6 AG Kgot5 Kgot6 Kcell5 Kcell6 Kguar5 Kguar6 Kuar5 Kuar6 Vgr5 Vgr6
| match goal with |- ?g => idtac "KEPTFAIL" g end ]).
destruct (al_blocks _ _ LAWS _ _ _ _ _ blk 64 (proj1 HJ6) Hblk_in) as (_ & _ & _ & _ & Hbpres6 & _). change (req_size 64) with 64 in Hbpres6.
assert (ZB : forall off (n : nat), 0 <= off -> off + Z.of_nat n <= 64 -> val_mem trbsegs (mrestrict (w_H W5) mem6) (blk + off) n 0).
{ intros off n Ho1 Ho2. apply rg_val_mem_zero. intros i Hi. replace (blk + off + i) with (blk + (off + i)) by lia. rewrite (Heff6 (off + i)) by lia. reflexivity. }
lazymatch type of HS with st_ok _ ?Ev _ _ =>
pose proof (ast_ok_add_region trbsegs Ev _ _
(YQ0b.mkRegion (Some 76%nat) 0 64 0 64
[YQ0b.mkChunk 0 (CVal 8 (SLit 0)); YQ0b.mkChunk 48 (CVal 8 (SLit 0)); YQ0b.mkChunk 56 (CVal 4 (SLit 0)); YQ0b.mkChunk 60 (CVal 4 (SLit 0))]) HS eq_refl
ltac:(unfold region_ok; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val ms_mem restrict mkst];
cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia;
rewrite Rblk, unsigned_lit_small by lia; split; [lia|]; split; [lia|]; split;
[ intros o Ho; apply (apresent_writable trbsegs); apply (proj1 (Hbpres6 (blk + o) ltac:(lia)))
| repeat (apply Forall_cons; [eapply (chunk_ok_val trbsegs Ev _ blk _ _ (SLit 0) 0); [reflexivity | zside | zside | apply ZB; cbn; lia] |]); apply Forall_nil ])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val];
rewrite Rblk; change (fs_frame_bytes 1) with 128; change (fs_frame_bytes 1 / 8) with 16; evalE AG;
unfold A_GOT_shadow, A_shadow_glob, A_GOT_uar, A_uar_glob, A_GOT_rgb_newgif; repeat split; zone_lia)) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS. clear_frames.
fs_ro HS. reshok_bx HS 35%nat.
lazymatch type of HS with st_ok _ _ _ (restrict _ (mkst ?rg ?pcx ?mm ?rm)) => change mm with (ms_mem (mkst rg pcx mm rm)) in HJ6 end.
lazymatch type of HS with st_ok _ ?Ev _ _ => assert (E10n : ew Ev 10 = Z_to_bv 64 cfgp) by (rewrite (AG 10%nat) by lia; exact E10) end.
aj_run_to_tok trbtbl_lib_ok HS HJ6 SHOK RBspan A_cgif_newgif.
1-6: oblF HJ6 E10n E35 HRA HAR Hfin Hcid0 Hflo Hfhi Hfal.
{ awrR AG fpos F EFA5 42%nat 55%nat. }
clear_frames.
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
assert (HB42 : bv_unsigned (ew Ex 42) = F) by (cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite RF; apply unsigned_lit_small; clear - HF4096 HFceil C1; lia);
pose proof (st_ok_region_nth Ex ssx (restrict (w_H W5) msX) 1 _ HS eq_refl) as HRc; cbn [ms_mem restrict] in HRc;
lazymatch type of HRc with region_ok _ _ _ (YQ0b.mkRegion (Some 42%nat) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 42 F cs lo hi wlo whi 32 8%N (SLit 0) 0 HRc HB42 ltac:(cbn; tauto) eq_refl ltac:(zside) ltac:(cbn; lia)) as Vpal;
pose proof (field_of_region Ex _ 42 F cs lo hi wlo whi 40 8%N (SLit 0) 0 HRc HB42 ltac:(cbn; tauto) eq_refl ltac:(zside) ltac:(cbn; lia)) as Vpath;
pose proof (field_of_region Ex _ 42 F cs lo hi wlo whi 48 4%N (SLit 6) 6 HRc HB42 ltac:(cbn; tauto) eq_refl ltac:(zside) ltac:(cbn; lia)) as Vattr;
pose proof (field_of_region Ex _ 42 F cs lo hi wlo whi 52 4%N (SLit 0) 0 HRc HB42 ltac:(cbn; tauto) eq_refl ltac:(zside) ltac:(cbn; lia)) as Vgen;
pose proof (field_of_region Ex _ 42 F cs lo hi wlo whi 60 2%N (SLit 0) 0 HRc HB42 ltac:(cbn; tauto) eq_refl ltac:(zside) ltac:(cbn; lia)) as Vngp;
let gh off e n v Hn Rv V := pose proof (rg_field_of_region_any Ex _ 42 F cs lo hi wlo whi off 2%N e HRc HB42 ltac:(cbn; tauto) ltac:(cbn; lia)) as V;
change (bv_unsigned (sv_denot Ex e)) with (U Ex e) in V; change (2 ^ (8 * Z.of_N 2)) with (2 ^ 16) in V;
rewrite (rg_U_sext16_mod Ex (SOff n 0) v ltac:(apply (U_atom Ex n v); [cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact Hn | clear - Rv; lia]) Rv) in V in
gh 56 (SExt true 16 (SOff 36 0)) 36%nat Wd E36 CR34 VW;
gh 58 (SExt true 16 (SOff 37 0)) 37%nat Hd E37 CR36 VH;
gh 62 (SExt true 16 (SOff 34 0)) 34%nat loops E34 CR32 Vlp;
pose proof (field_of_region Ex _ 42 F cs lo hi wlo whi 64 8%N (SLit A_writecb) A_writecb HRc HB42 ltac:(cbn; tauto) eq_refl ltac:(unfold A_writecb; zside) ltac:(cbn; lia)) as Vwfn;
pose proof (field_of_region Ex _ 42 F cs lo hi wlo whi 72 8%N (SLit 0) 0 HRc HB42 ltac:(cbn; tauto) eq_refl ltac:(zside) ltac:(cbn; lia)) as Vctx
end; clear HRc end.
cbn [N.to_nat] in Vpal, Vpath, Vattr, Vgen, Vngp, VW, VH, Vlp, Vwfn, Vctx.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msX) =>
assert (Ocfg : obj_at trbsegs (mrestrict (w_H W5) (ms_mem msX)) (F + 32) LAY_Config [0; 0; 6; 0; Wd; Hd; 0; loops; A_writecb; 0]) end.
{ cbn [obj_at LAY_Config]. unfold field_ok. cbn [fst snd N.to_nat Z.of_N].
replace (F + 32 + 0) with (F + 32) by lia. replace (F + 32 + 8) with (F + 40) by lia. replace (F + 32 + 16) with (F + 48) by lia.
replace (F + 32 + 20) with (F + 52) by lia. replace (F + 32 + 24) with (F + 56) by lia. replace (F + 32 + 26) with (F + 58) by lia.
replace (F + 32 + 28) with (F + 60) by lia. replace (F + 32 + 30) with (F + 62) by lia.
replace (F + 32 + 32) with (F + 64) by lia. replace (F + 32 + 40) with (F + 72) by lia.
repeat split; try assumption; clear - CR32 CR34 CR36; unfold A_writecb; lia. }
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs 55%nat in let i := eval vm_compute in i in
pose proof (st_ok_region_nth Ex ssx (restrict (w_H W5) msX) i _ HS eq_refl) as HRfs; cbn [ms_mem restrict] in HRfs;
lazymatch type of HRfs with region_ok _ _ _ (YQ0b.mkRegion (Some 55%nat) ?lo ?hi ?wlo ?whi ?cs) =>
assert (ZS5 : forall j, 4 <= j <= 9 -> val_mem trbsegs (mrestrict (w_H W5) (ms_mem msX)) (SB + F / 8 + j) 1 0);
[ let j := fresh "j" in let Hj := fresh "Hj" in let Hj5 := fresh "Hj5" in intros j Hj;
assert (Hj5 : j = 4 \/ j = 5 \/ j = 6 \/ j = 7 \/ j = 8 \/ j = 9) by (clear - Hj; lia);
destruct Hj5 as [-> | [-> | [-> | [-> | [-> | ->]]]]];
(eapply (field_of_region Ex _ 55 (SB + F / 8) cs lo hi wlo whi _ 1%N (SLit 0) 0 HRfs);
[evalE AG | cbn; tauto | reflexivity | cbn; lia | cbn; lia])
| ] end;
clear HRfs;
assert (HRA48c : range_addressable (aview trbsegs (w_H W5) (ms_mem msX)) SHADOW_OFF (F + 32) 48);
[ apply zero_shadow_range; [rewrite HFq; replace (32 * (F / 32) + 32) with ((4 * (F / 32) + 4) * 8) by lia; apply Z_mod_mult | reflexivity |];
let ii := fresh "ii" in let Hii := fresh "Hii" in
intros ii Hii; change (48 / 8) with 6 in Hii; unfold shadow_of_addr; rewrite <- SB_SHADOW_OFF;
replace (SB + (F + 32) / 8 + ii) with (SB + F / 8 + (4 + ii)) by (rewrite HFq at 2; rewrite HF8; replace (32 * (F / 32) + 32) with ((4 * (F / 32) + 4) * 8) by lia; rewrite Z.div_mul by lia; lia);
apply (aview_of_val_mem1 trbsegs); [apply ZS5; clear - Hii; lia | clear; lia]
| ] end.
assert (HEVc : vev S5 + EV_NEWGIF <= VEV_MAX).
{ pose proof HJ6 as (_ & _ & _ & _ & _ & _ & Hnev6 & _). unfold EV_RGBNEWGIF in Hev. clear - Hnev6 Hev. lia. }
assert (HLIVEc : blocks_bytes S5 + LIVE_NEWGIF <= LIVE_MAX).
{ rewrite (blocks_bytes_bsum B ly5 S5), Ebl5, Eab, !bsum_app, <- (blocks_bytes_bsum B ly S). cbn [bsum fold_right snd]. unfold LIVE_RGBNEWGIF in Hlive. clear - Hlive. lia. }
clear Kgot6 Kcell6 Kguar6 Kuar6 Vgr6. aconsts HROD HJ6 Kgot6 Kcell6 Kguar6 Kuar6 Vgr6.
rreg HS (10%bv : bv 5) Ra0. rreg HS (1%bv : bv 5) Rra. rreg HS (2%bv : bv 5) Rsp. rreg HS (3%bv : bv 5) Rgp.
rreg HS (4%bv : bv 5) Rtp. rreg HS (8%bv : bv 5) Rs0.
rng_chain HS HJ6 AG EE.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msX) =>
assert (HspX : spZ (ms_regs msX) = spZ regs - 96) by (unfold spZ at 1; rewrite Rsp; evalE AG; clear; lia) end.
pose proof (proj1 (proj2 HJ6)) as HLY6. pose proof HLY6 as (_ & _ & _ & _ & _ & _ & _ & _ & Etop6 & _).
lazymatch type of HS with st_ok _ ?Ex ?ssX (restrict _ ?msX) =>
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdX) _ =>
eapply SRr_bind;
[ eapply (aj_call trbsegs B LAWS trb_segs_low W5 Ex ssX msX TRGBNEWGIF_STK (spZ regs) [] ly S W mem md [(1, fpos)] ly5 S5 mdX (0 + 1)
TNEWGIF_STK [] EV_NEWGIF (-96) (ew Ex 2) (Z_to_bv 64 0x81c9c) ((spZ regs, raZ regs, s0Z regs) :: ch)
(fun ly2 S2 W2 regs2 mem2 md2 => exists res : Z, getr regs2 10 = w64 res /\
((res = 0 /\ Permutation (ablocks B ly2 S2) (ablocks B ly5 S5)) \/
(res <> 0 /\ exists s,
tcgif_at (mrestrict (w_H W2) mem2) res s /\ cgif_wf s (Wd * Hd) /\
cg_frames s = [None; None; None] /\ cg_W s = Wd /\ cg_H s = Hd /\ cg_attr s = 6 /\
cg_cur s = R_PENDING /\ cg_ihead s = 1 /\
Permutation (ablocks B ly2 S2) (cgif_blocks res s (Wd * Hd) ++ ablocks B ly5 S5) /\
(forall b, In b (cgif_blocks res s (Wd * Hd)) ->
aftok [] (ablocks B ly5 S5) b /\
forall blc i, In b blc -> 0 <= i < req_size (snd b) ->
awr_byte TNEWGIF_STK (spZ regs - 96) [] (ablocks B ly5 S5) blc ly2 [] (fst b + i))))) HS eq_refl HJ6);
[ rewrite Rsp; cbn [sv_denot]; reflexivity
| reflexivity
| evalE AG
| reflexivity
| clear; lia
| unfold TNEWGIF_STK, TRAWNEW_STK, ASTACK; clear; lia
| rewrite FFS; unfold TNEWGIF_STK, TRAWNEW_STK, ASTACK; clear; lia
| rewrite Rgp; evalE AG; rewrite (EE 3%nat 3%bv eq_refl); exact Hgp
| rewrite Rtp; evalE AG; rewrite (EE 4%nat 4%bv eq_refl); exact Htp
| exact Rra
| apply ret_ok_even; vm_compute; reflexivity
| rewrite unsigned_lit_small by (clear; lia); clear; lia
| unfold s0Z; rewrite Rs0; cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 2%nat) by lia; rewrite Usp;
replace (spZ regs + -96) with (spZ regs - 96) by (clear; lia); exact (achain_ly_top ly ly5 _ _ _ _ Etop6 Hch1)
| intros HPRE1; eapply SRr_mono;
[ pose proof (NEWGIF ly5 S5 W5 (ms_regs msX) (ms_mem msX) mdX ((spZ regs, raZ regs, s0Z regs) :: ch) (F + 32) 0 0 6 0 Wd Hd 0 loops (ablocks B ly5 S5) HPRE1) as CALL;
unfold cfg_at, apost_base in CALL; cbn [ss_pc]; change (w64 A_cgif_newgif) with (Z_to_bv 64 547988) in CALL;
apply CALL; clear CALL;
[ unfold spZ; rewrite Rsp; evalE AG; first [rewrite Z.add_mod by (clear; lia) | rewrite Zminus_mod]; rewrite Hal32; reflexivity
| unfold raZ at 1; rewrite Rra, unsigned_lit_small by (clear; lia); cbn [spine map fst snd]; fold (spine ch); rewrite <- ?Hra88; destruct Hspine as [Hs | Hs]; rewrite Hs; cbn; rewrite <- ?Hra88; tauto
| rewrite Hfrs5, Hfrs2; cbn [length]; clear - Hroom; lia
| rewrite HspX, Etop6; clear - Htop32; lia
| eapply arodata_ok_journal; [exact HJ6 | exact HROD]
| rewrite Ra0; cbn [sv_denot]; evalE AG
| split; [exists 1, fpos; split; [exact Hfin5 | split; [clear; lia | rewrite EFA5; fold F; split; [rewrite HFq; replace (32 * (F / 32)) with ((4 * (F / 32)) * 8) by lia; apply Z_mod_mult | change (fs_frame_bytes 1) with 128; clear; lia]]]
| split; [rewrite HFq; replace (32 * (F / 32) + 32) with ((4 * (F / 32) + 4) * 8) by lia; apply Z_mod_mult | exact HRA48c]]
| exact Ocfg
| exact HWH
| reflexivity
| cbn; apply Permutation_refl
| exact HEVc | exact HLIVEc ]
| cbv beta; intros W7 c7 _ (ly7 & S7 & regs7 & mem7 & md7 & -> & HJc & HPc & res & Hres & HK7);
exists ly7, S7, regs7, mem7, md7; split; [rewrite Rra; reflexivity|]; split; [exact HJc|]; split; [exact HPc|]; exists res; split; [exact Hres | rewrite ?HspX in HK7; exact HK7] ]
| intros a Ha; exfalso; exact (inFP_nil a Ha) ]
| ] end end.
cbv beta. intros W7 c7 Hwle7 (ly7 & S7 & regs7 & mem7 & md7 & -> & HJ7 & HJc & HP7 & res & Ha07 & Hres).
clear Ra0 Rra Rsp Rgp Rtp Rs0 Hch1 HUPc Vra Vs0 Qceil Qal8 Qtop Qtop64 Qsp Qra Qs0 ZS5 HRA48c.
pose proof (proj1 HJ7) as HAR7. aconsts HROD HJ7 Kgot7 Kcell7 Kguar7 Kuar7 Vgr7.
pose proof HJ7 as (_ & Hly7 & _).
assert (EFA7 : forall c p, frame_addr ly7 c p = frame_addr ly c p)
by (intros c p; unfold frame_addr; destruct Hly7 as (_ & _ & _ & _ & _ & -> & _); reflexivity).
assert (EFL7 : forall c p, flag_addr ly7 c p = flag_addr ly c p)
by (intros c p; unfold flag_addr; destruct Hly7 as (_ & _ & _ & _ & _ & -> & _); reflexivity).
pose proof HJc as (_ & _ & _ & _ & _ & Hfrs7 & _). cbn [app] in Hfrs7.
assert (Hfin7 : In (1, fpos) (frames S7)) by (rewrite Hfrs7; exact Hfin5).
assert (HfinS7 : In (cid, pos) (frames S7)) by (rewrite Hfrs7; exact HfinS5).
destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos HAR7 Hfin7) as (_ & _ & HFpres7 & HFSpres7). change (fs_frame_bytes 1) with 128 in HFpres7, HFSpres7.
change (128 / 8) with 16 in HFSpres7. rewrite !EFA7 in HFpres7, HFSpres7. fold F in HFpres7, HFSpres7.
destruct (al_frames _ _ LAWS _ _ _ _ _ cid pos HAR7 HfinS7) as (_ & _ & HCpres7 & _). rewrite EFA7 in HCpres7.
destruct Hres as [(Hres0 & HPerm7) | (Hresnz & st & Hat7 & Hwf7 & Hfr7 & HW7 & HH7 & Hattr7 & Hcur7 & Hih7 & HPerm7 & Hnew7)].
{
assert (Hblk_in7 : In (blk, 64) (ablocks B ly7 S7)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm7 | exact Hblk_in]).
reseat HS HJ7 HP7 [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11]%nat AG
ltac:(idtac; first [ keptJ HJc HJ7 AG Usp E10 RF E55 Hfin5 HfinS5 FFS Kgot6 Kgot7 Kcell6 Kcell7 Kguar6 Kguar7 Kuar6 Kuar7 Vgr6 Vgr7 EFA5 HFpres7 HFSpres7 HCpres7 F ltac:(fail)
| match goal with |- ?g => idtac "KEPTFAIL" g end ]).
pose proof (st_ok_pin_reg' trbsegs _ _ _ (10%bv : bv 5) 0 HS ltac:(cbn [ms_regs restrict mkst]; rewrite Ha07, Hres0; reflexivity) eq_refl) as HS3.
clear HS. rename HS3 into HS. norm_ss HS. reshok_bx HS 35%nat.
lazymatch type of HS with st_ok _ _ _ (restrict _ (mkst ?rg ?pcx ?mm ?rm)) => change mm with (ms_mem (mkst rg pcx mm rm)) in HJ7 end.
aj_run_to_tok trbtbl_lib_ok HS HJ7 SHOK RBspan A_wrap_free; [obl_blk HJ7 Rblk E35 Hblk_in7 | awrR AG fpos F EFA7 42%nat 55%nat |]. clear_frames.
clear Kgot7 Kcell7 Kguar7 Kuar7 Vgr7. aconsts HROD HJ7 Kgot7 Kcell7 Kguar7 Kuar7 Vgr7.
rreg HS (10%bv : bv 5) Ra0. rreg HS (1%bv : bv 5) Rra. rreg HS (2%bv : bv 5) Rsp. rreg HS (3%bv : bv 5) Rgp.
rreg HS (4%bv : bv 5) Rtp. rreg HS (8%bv : bv 5) Rs0.
rng_chain HS HJ7 AG EE.
rewrite (st_ok_restrict_mkst trbsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
replace (Z_to_bv 64 340932) with (Z_to_bv 64 (pc_wrap_free (as_code B))) by (rewrite HBcode; vm_compute; reflexivity).
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
eapply (aj_free_at trbsegs B LAWS Hsegs errno_low ML AFREE _ (ms_regs msX) (ms_mem msX) TRGBNEWGIF_STK (spZ regs) [] ly S W mem md [(1, fpos)]
ly7 S7 _ (0 + 1 + EV_NEWGIF) blk 64 (-96) (Z_to_bv 64 0x81cf4) ((spZ regs, raZ regs, s0Z regs) :: ch) HJ7 Hblk_in7) end.
- rewrite Ra0. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite Rblk. reflexivity.
- unfold spZ. rewrite Rsp. evalE AG.
- reflexivity.
- lia.
- rewrite FFS. unfold ASTACK. lia.
- rewrite Rgp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (AG 3%nat) by lia. rewrite (EE 3%nat 3%bv eq_refl). exact Hgp.
- rewrite Rtp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (AG 4%nat) by lia. rewrite (EE 4%nat 4%bv eq_refl). exact Htp.
- exact Rra.
- vm_compute. reflexivity.
- pose proof HJ7 as (_ & _ & _ & _ & _ & _ & Hnev7 & _). unfold EV_RGBNEWGIF in Hev. clear - Hnev7 Hev. lia.
- pose proof (proj1 (proj2 HJ7)) as HLY7. pose proof HLY7 as (_ & _ & _ & _ & _ & _ & _ & _ & Etop7 & _).
apply (achain_chain_pre ly7 _ (spZ regs - 96) (spZ regs) _ _ (achain_ly_top ly ly7 _ _ _ _ Etop7 Hch1));
[ unfold spZ at 1 2; rewrite Rsp; evalE AG
| unfold s0Z; rewrite Rs0; evalE AG
| unfold raZ; rewrite Rra, unsigned_lit_small by lia; lia ].
- rewrite call_trace_of_spine. cbn [spine map fst snd]. fold (spine ch). unfold raZ at 1. rewrite Rra, unsigned_lit_small by lia. rewrite <- Hra88.
rewrite HBcode. rewrite (tl_universe B TL). apply TRACES_cgif_rgb_newgif_U. apply memZL_In.
destruct Hspine as [Hsp | Hsp]; rewrite Hsp; vm_compute; reflexivity.
- exact Tblk. }
cbv beta. intros W8 c8 Hwle8 (ly8 & S8 & regs8 & mem8 & md8 & -> & HJ8 & HP8 & (l1 & l2 & El1 & Eab8) & Hfrs8 & HK8).
clear Ra0 Rra Rsp Rgp Rtp Rs0 Hch1 HUPc Vra Vs0 Qceil Qal8 Qtop Qtop64 Qsp Qra Qs0.
unfold ASTACK in HK8. replace (spZ regs + -96 - 16384) with (spZ regs - 16480) in HK8 by lia. replace (spZ regs + -96) with (spZ regs - 96) in HK8 by lia.
pose proof (proj1 HJ8) as HAR8. aconsts HROD HJ8 Kgot8 Kcell8 Kguar8 Kuar8 Vgr8.
pose proof HJ8 as (_ & Hly8 & _).
assert (EFA8 : forall c p, frame_addr ly8 c p = frame_addr ly c p)
by (intros c p; unfold frame_addr; destruct Hly8 as (_ & _ & _ & _ & _ & -> & _); reflexivity).
assert (EFL8 : forall c p, flag_addr ly8 c p = flag_addr ly c p)
by (intros c p; unfold flag_addr; destruct Hly8 as (_ & _ & _ & _ & _ & -> & _); reflexivity).
assert (Hfin8 : In (1, fpos) (frames S8)) by (rewrite Hfrs8; exact Hfin7).
assert (HfinS8 : In (cid, pos) (frames S8)) by (rewrite Hfrs8; exact HfinS7).
destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos HAR8 Hfin8) as (_ & _ & HFpres8 & HFSpres8). change (fs_frame_bytes 1) with 128 in HFpres8, HFSpres8.
change (128 / 8) with 16 in HFSpres8. rewrite !EFA8 in HFpres8, HFSpres8. fold F in HFpres8, HFSpres8.
assert (HErF : forall a, F <= a < F + 128 -> ~ (blk <= a < blk + req_size 64)) by (change (req_size 64) with 64; intros a Ha; clear - Ha HdBF; lia).
reseat HS HJ8 HP8 [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11]%nat AG
ltac:(idtac; first [ keptR HK8 HJ8 AG Usp E10 HfinS7 Kgot7 Kgot8 Kcell7 Kcell8 Kguar7 Kguar8 Kuar7 Kuar8 Vgr7 Vgr8 EFA7
| keptF HK8 AG RF E55 Hfin7 HFpres8 HFSpres8 HErF F EFA7
| match goal with |- ?g => idtac "KEPTFAIL" g end; fail ]).
lazymatch type of HS with st_ok _ _ _ (restrict _ (mkst ?rg ?pcx ?mm ?rm)) => change mm with (ms_mem (mkst rg pcx mm rm)) in HJ8 end.
exitG HS HJ8 AG fpos F cfgp E54 E55 Hfin8 HfinS8 EE Hra HEV EFA8 EFL8.
exists 0. split; [reflexivity|]. left. split; [reflexivity|].
unfold ablocks. rewrite blocks_stack_free_state. fold (ablocks B ly8 S8). rewrite Eab8.
apply Permutation_sym. apply (Permutation_cons_app_inv l1 l2 (a := (blk, 64))). rewrite <- El1.
apply Permutation_sym. eapply Permutation_trans; [exact HPerm7|]. rewrite Ebl5, Eab. apply Permutation_sym. apply Permutation_cons_append. }
assert (Hblk_in7 : In (blk, 64) (ablocks B ly7 S7)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm7|]. apply in_app_iff. right. exact Hblk_in. }
assert (Hres_in7 : In (res, CGIF_SIZE) (ablocks B ly7 S7)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm7|]. apply in_app_iff. left. apply rg_cgif_blocks_in_g. }
destruct (al_blocks _ _ LAWS _ _ _ _ _ res CGIF_SIZE HAR7 Hres_in7) as (Hres16 & Hres4096 & Hresceil & _). change (req_size CGIF_SIZE) with 96 in Hresceil.
reseat HS HJ7 HP7 [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11]%nat AG
ltac:(idtac; first [ keptJ HJc HJ7 AG Usp E10 RF E55 Hfin5 HfinS5 FFS Kgot6 Kgot7 Kcell6 Kcell7 Kguar6 Kguar7 Kuar6 Kuar7 Vgr6 Vgr7 EFA5 HFpres7 HFSpres7 HCpres7 F ltac:(fail)
| match goal with |- ?g => idtac "KEPTFAIL" g end ]).
rreg HS (10%bv : bv 5) Rres. cbn [ms_regs] in Rres. rewrite Ha07 in Rres. symmetry in Rres. unfold w64 in Rres.
lazymatch type of Rres with ew ?Ex ?nx = _ =>
pose proof (st_ok_add_fact trbsegs Ex _ _ nx (HPTR 4) HS
ltac:(unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite Rres, unsigned_lit_small by lia; change (2 ^ 4) with 16; lia)) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS. reshok_bx HS 35%nat.
lazymatch type of HS with st_ok _ _ _ (restrict _ (mkst ?rg ?pcx ?mm ?rm)) => change mm with (ms_mem (mkst rg pcx mm rm)) in HJ7 end.
set (ZsP := fun a => (blk <= a < blk + 64) \/ (SB + F / 8 <= a < SB + F / 8 + 16) \/ (F <= a < F + 128) \/ (spZ regs - 96 <= a < spZ regs) \/ (FL <= a < FL + 1)).
aj_run_to_tok trbtbl_lib_ok HS HJ7 SHOK RBspan A_asan_memcpy; [obl_blk HJ7 Rblk E35 Hblk_in7 | awrR AG fpos F EFA7 42%nat 55%nat |].
pose proof (rg_kept_of_frame _ _ _ _ _ ZsP HFr
ltac:(let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let a := fresh "a" in
let Hin := fresh "Hin" in let Hrr := fresh "Hrr" in let Hq := fresh "Hq" in
intros b wlo whi a Hin Hrr; vm_compute in Hin;
repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi base_val] in Hrr; revert Hrr; evalE AG;
first [rewrite Rblk | rewrite RF | idtac]; rewrite ?unsigned_lit_small by lia; intros Hrr; unfold ZsP, SB; clear - Hrr; lia |]);
destruct Hin)) as UN5.
clear_frames.
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
pose proof (st_ok_region_nth Ex ssx (restrict (w_H W7) msX) 0 _ HS eq_refl) as HRg; cbn [ms_mem restrict] in HRg;
lazymatch type of HRg with region_ok _ _ _ (YQ0b.mkRegion (Some 76%nat) ?lo ?hi ?wlo ?whi ?cs) =>
assert (HB76 : bv_unsigned (ew Ex 76) = blk) by (cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite Rblk; apply unsigned_lit_small; lia);
let gf off w v V := pose proof (field_of_region Ex _ 76 blk cs lo hi wlo whi off w (SLit v) v HRg HB76 ltac:(cbn; tauto) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as V in
gf 48 8%N 0 U48; gf 56 4%N 0 U56; gf 60 4%N 0 U60;
lazymatch type of Rres with ew _ ?nx = _ =>
pose proof (field_of_region Ex _ 76 blk cs lo hi wlo whi 0 8%N (SOff nx 0) res HRg HB76 ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite Rres, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
ltac:(cbn; lia) ltac:(cbn; lia)) as U0 end
end; clear HRg end.
cbn [N.to_nat] in U0, U48, U56, U60. rewrite Z.add_0_r in U0.
rreg HS (10%bv : bv 5) Ra0. rreg HS (11%bv : bv 5) Ra1. rreg HS (12%bv : bv 5) Ra2. rreg HS (1%bv : bv 5) Rra.
rreg HS (2%bv : bv 5) Rsp. rreg HS (3%bv : bv 5) Rgp. rreg HS (4%bv : bv 5) Rtp.
rewrite (st_ok_restrict_mkst trbsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
change (Z_to_bv 64 335988) with (Z_to_bv 64 A_asan_memcpy).
destruct (al_frames _ _ LAWS _ _ _ _ _ cid pos (proj1 HJ7) HfinS7) as (_ & _ & HCpres7' & _). rewrite EFA7 in HCpres7'.
clear Kgot7 Kcell7 Kguar7 Kuar7 Vgr7. aconsts HROD HJ7 Kgot7 Kcell7 Kguar7 Kuar7 Vgr7.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
eapply (aj_intrin_at trbsegs B LAWS Hsegs OCpy A_asan_memcpy AMEMCPY _ (ms_regs msX) (ms_mem msX) TRGBNEWGIF_STK (spZ regs) [] ly S W mem md [(1, fpos)]
ly7 S7 _ _ (blk + 8) cfgp 40 (-96) (Z_to_bv 64 0x81ccc) HJ7) end.
- rewrite Ra0. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite Rblk. unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
- rewrite Ra1. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (AG 10%nat) by lia. rewrite E10. reflexivity.
- exact Ra2.
- lia. - lia. - lia.
- unfold spZ at 1. rewrite Rsp. evalE AG.
- reflexivity. - lia. - rewrite FFS. unfold ESTACK. lia.
- rewrite Rgp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (AG 3%nat) by lia. rewrite (EE 3%nat 3%bv eq_refl). exact Hgp.
- rewrite Rtp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (AG 4%nat) by lia. rewrite (EE 4%nat 4%bv eq_refl). exact Htp.
- exact Rra.
- vm_compute. reflexivity.
- intros a Ha. split; [replace a with (blk + (a - blk)) by lia; apply Ablk; [exact Hblk_in7 | lia] | unfold ESTACK; lia].
- apply (amem_range_of_block trbsegs B LAWS ly7 S7 _ _ _ blk 64 _ _ (proj1 HJ7) Hblk_in7); change (req_size 64) with 64; lia.
- apply (range_addressable_of_block trbsegs B LAWS ly7 S7 _ _ _ blk 64 _ _ (proj1 HJ7) Hblk_in7); change (req_size 64) with 64; lia.
- intros _. apply (shadow_hull_vis_of_block trbsegs B LAWS ly7 S7 _ _ _ blk 64 _ _ (proj1 HJ7) Hblk_in7); change (req_size 64) with 64; lia.
- split; [lia|]. split; [lia|]. split.
{ intros a Ha. split; [| unfold spZ; rewrite Rsp; evalE AG].
apply (aview_some_of_apresent trbsegs). apply (proj1 (HCpres7' a ltac:(lia))). }
split; [clear - HdBC Hflo Hfhi; lia|]. split; [apply amem_range_high; [clear; lia | destruct Hfhigh as [_ Hfz]; unfold kLowShadowBeg, kHighMemBeg in Hfz; clear - Hfz Hflo Hfhi; lia | clear - Hfceil Hfhi; lia]|]. split.
+ eapply (range_addressable_entry_frame trbsegs B LAWS); [exact HJ7 | exact Hfin | exact Hcid0 | exact Hflo | exact Hfhi | exact Hfal
| intros x Hx; exfalso; exact (inFP_nil x Hx) | exact HAR | exact HRA].
+ intros _. eapply (shadow_hull_vis_of_frame trbsegs B LAWS ly7 S7 _ _ _ cid pos cfgp 40 (proj1 HJ7) HfinS7); [rewrite EFA7; exact Hflo | rewrite EFA7; exact Hfhi | lia]. }
cbv beta. intros W9 c9 _ (-> & regs9 & mem9 & md9 & -> & HJ9 & HP9 & Ha09 & Heff9 & Hfr9 & Hpres9).
clear Ra0 Ra1 Ra2 Rra Rsp Rgp Rtp.
lazymatch type of Heff9 with forall i, _ -> aview _ _ _ _ = aview _ _ ?memT _ =>
let cmove off w v V Vr :=
pose proof (val_mem_moved trbsegs (w_H W7) (w_H W7) memT mem9 (cfgp + off) (blk + 8 + off) w v
ltac:(intros kk Hk; replace (blk + 8 + off + kk) with (blk + 8 + (off + kk)) by lia; replace (cfgp + off + kk) with (cfgp + (off + kk)) by lia;
apply Heff9; cbn [Z.of_nat Pos.to_nat Pos.iter_op Nat.add] in Hk; lia)
(val_mem_entry_frame trbsegs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ cid pos (cfgp + off) w v HJ7 Hfin
ltac:(lia) ltac:(cbn [Z.of_nat Pos.to_nat Pos.iter_op Nat.add]; lia) ltac:(intros x Hx HF; exact (inFP_nil x HF)) V)) as Vr in
cmove 0 8%nat A_writecb CV0 Y0; cmove 8 8%nat 0 CV8 Y8; cmove 16 8%nat 0 CV16 Y16; cmove 24 4%nat attr CV24 Y24;
cmove 28 4%nat gen CV28 Y28; cmove 32 2%nat loops CV32 Y32; cmove 34 2%nat Wd CV34 Y34; cmove 36 2%nat Hd CV36 Y36 end.
lazymatch type of Heff9 with forall i, _ -> aview _ _ _ _ = aview _ _ ?memT _ =>
let keep off w v U Ur :=
pose proof (val_mem_moved trbsegs (w_H W7) (w_H W7) memT mem9 (blk + off) (blk + off) w v
ltac:(intros kk Hk; apply Hfr9; [lia | cbn [Z.of_nat Pos.to_nat Pos.iter_op Nat.add] in Hk; lia | unfold ESTACK; lia]) U) as Ur in
keep 48 8%nat 0 U48 X48; keep 56 4%nat 0 U56 X56; keep 60 4%nat 0 U60 X60;
pose proof (val_mem_moved trbsegs (w_H W7) (w_H W7) memT mem9 blk blk 8%nat res
ltac:(intros kk Hk; apply Hfr9; [lia | cbn [Z.of_nat Pos.to_nat Pos.iter_op Nat.add] in Hk; lia | unfold ESTACK; lia]) U0) as X0 end.
clear U0 U48 U56 U60.
aconsts HROD HJ9 Kgot9 Kcell9 Kguar9 Kuar9 Vgr9.
destruct (al_blocks _ _ LAWS _ _ _ _ _ blk 64 (proj1 HJ9) Hblk_in7) as (_ & _ & _ & _ & Hbpres9 & _). change (req_size 64) with 64 in Hbpres9.
reseat HS HJ9 HP9 [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11]%nat AG
ltac:(idtac; first [ keptI Hfr9 Hpres9 AG Kgot7 Kgot9 Kcell7 Kcell9 Kguar7 Kguar9 Kuar7 Kuar9 Vgr7 Vgr9
| match goal with |- ?g => idtac "KEPTFAIL" g end ]).
lazymatch type of Rres with ew _ ?nres = _ =>
lazymatch type of HS with st_ok _ ?Ev _ _ =>
let ckv HE := cbn [sv_denot]; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia;
try rewrite (AG 32%nat) by lia; rewrite HE; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity in
pose proof (ast_ok_add_region trbsegs Ev _ _
(YQ0b.mkRegion (Some 76%nat) 0 64 0 64
[YQ0b.mkChunk 0 (CVal 8 (SOff nres 0)); YQ0b.mkChunk 8 (CVal 8 (SLit A_writecb)); YQ0b.mkChunk 16 (CVal 8 (SLit 0)); YQ0b.mkChunk 24 (CVal 8 (SLit 0));
YQ0b.mkChunk 32 (CVal 4 (SOff 32 0)); YQ0b.mkChunk 36 (CVal 4 (SOff 33 0));
YQ0b.mkChunk 40 (CVal 2 (SOff 34 0)); YQ0b.mkChunk 42 (CVal 2 (SOff 36 0)); YQ0b.mkChunk 44 (CVal 2 (SOff 37 0));
YQ0b.mkChunk 48 (CVal 8 (SLit 0)); YQ0b.mkChunk 56 (CVal 4 (SLit 0)); YQ0b.mkChunk 60 (CVal 4 (SLit 0))]) HS eq_refl
ltac:(unfold region_ok; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val ms_mem restrict mkst];
cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite Rblk, unsigned_lit_small by lia;
split; [lia|]; split; [lia|]; split; [intros o Ho; apply (apresent_writable trbsegs); apply (proj1 (Hbpres9 (blk + o) ltac:(lia)))|];
apply Forall_cons; [apply (chunk_ok_val trbsegs Ev _ blk 0 8 _ res); [ckv Rres | zside | zside | rewrite Z.add_0_r; exact X0]|];
apply Forall_cons; [apply (chunk_ok_val trbsegs Ev _ blk 8 8 _ A_writecb); [reflexivity | unfold A_writecb; zside | zside | replace (blk + 8) with (blk + 8 + 0) by lia; exact Y0]|];
apply Forall_cons; [apply (chunk_ok_val trbsegs Ev _ blk 16 8 _ 0); [reflexivity | zside | zside | replace (blk + 16) with (blk + 8 + 8) by lia; exact Y8]|];
apply Forall_cons; [apply (chunk_ok_val trbsegs Ev _ blk 24 8 _ 0); [reflexivity | zside | zside | replace (blk + 24) with (blk + 8 + 16) by lia; exact Y16]|];
apply Forall_cons; [apply (chunk_ok_val trbsegs Ev _ blk 32 4 _ attr); [ckv E32 | zside | zside | replace (blk + 32) with (blk + 8 + 24) by lia; exact Y24]|];
apply Forall_cons; [apply (chunk_ok_val trbsegs Ev _ blk 36 4 _ gen); [ckv E33 | zside | zside | replace (blk + 36) with (blk + 8 + 28) by lia; exact Y28]|];
apply Forall_cons; [apply (chunk_ok_val trbsegs Ev _ blk 40 2 _ loops); [ckv E34 | zside | zside | replace (blk + 40) with (blk + 8 + 32) by lia; exact Y32]|];
apply Forall_cons; [apply (chunk_ok_val trbsegs Ev _ blk 42 2 _ Wd); [ckv E36 | zside | zside | replace (blk + 42) with (blk + 8 + 34) by lia; exact Y34]|];
apply Forall_cons; [apply (chunk_ok_val trbsegs Ev _ blk 44 2 _ Hd); [ckv E37 | zside | zside | replace (blk + 44) with (blk + 8 + 36) by lia; exact Y36]|];
apply Forall_cons; [apply (chunk_ok_val trbsegs Ev _ blk 48 8 _ 0); [reflexivity | zside | zside | exact X48]|];
apply Forall_cons; [apply (chunk_ok_val trbsegs Ev _ blk 56 4 _ 0); [reflexivity | zside | zside | exact X56]|];
apply Forall_cons; [apply (chunk_ok_val trbsegs Ev _ blk 60 4 _ 0); [reflexivity | zside | zside | exact X60]|];
apply Forall_nil)
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val];
rewrite Rblk; change (fs_frame_bytes 1) with 128; change (fs_frame_bytes 1 / 8) with 16; evalE AG;
unfold A_GOT_shadow, A_shadow_glob, A_GOT_uar, A_uar_glob, A_GOT_rgb_newgif; repeat split; zone_lia)) as HS3;
clear HS; rename HS3 into HS end end.
norm_ss HS. reshok_bx HS 35%nat. clear_frames.
lazymatch type of HS with st_ok _ _ _ (restrict _ (mkst ?rg ?pcx ?mm ?rm)) => change mm with (ms_mem (mkst rg pcx mm rm)) in HJ9 end.
aj_run_to_tok trbtbl_lib_ok HS HJ9 SHOK RBspan 0x81cf8; [obl_blk HJ9 Rblk E35 Hblk_in7 | awrR AG fpos F EFA7 42%nat 55%nat |].
pose proof (rg_kept_of_frame _ _ _ _ _ ZsP HFr
ltac:(let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let a := fresh "a" in
let Hin := fresh "Hin" in let Hrr := fresh "Hrr" in let Hq := fresh "Hq" in
intros b wlo whi a Hin Hrr; vm_compute in Hin;
repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi base_val] in Hrr; revert Hrr; evalE AG;
first [rewrite Rblk | rewrite RF | idtac]; rewrite ?unsigned_lit_small by lia; intros Hrr; unfold ZsP, SB; clear - Hrr; lia |]);
destruct Hin)) as UN6.
clear_frames.
cbn [ms_mem mkst] in UN5, UN6.
assert (HnoB : forall a, blk <= a < blk + 64 -> ~ aowned B ly7 S7 a) by (intros a Ha; exact (proj2 (Hbpres9 a Ha))).
exitG HS HJ9 AG fpos F cfgp E54 E55 Hfin7 HfinS7 EE Hra HEV EFA7 EFL7.
exists blk. split; [cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by nat_side; rewrite Rblk; reflexivity|].
right. split; [clear - Hb4096; lia|].
exists res, st.
lazymatch goal with HFr : frame_of _ _ _ _ |- _ =>
pose proof (rg_kept_of_frame _ _ _ _ _ ZsP HFr
ltac:(let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let a := fresh "a" in
let Hin := fresh "Hin" in let Hrr := fresh "Hrr" in let Hq := fresh "Hq" in
intros b wlo whi a Hin Hrr; vm_compute in Hin;
repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi base_val] in Hrr; revert Hrr; evalE AG;
first [rewrite Rblk | rewrite RF | idtac]; rewrite ?unsigned_lit_small by lia; intros Hrr; unfold ZsP, SB; clear - Hrr; lia |]);
destruct Hin)) as UNx end.
split.
{
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs 76%nat in let i := eval vm_compute in i in
pose proof (st_ok_region_nth Ex ssx (restrict (w_H W7) msX) i _ HS eq_refl) as HRgf; cbn [ms_mem restrict] in HRgf;
assert (HB76f : bv_unsigned (ew Ex 76) = blk) by (cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by nat_side; rewrite Rblk; apply unsigned_lit_small; clear - Hb4096 Hbceil C1; lia) end.
lazymatch type of HRgf with region_ok _ ?Ex _ (YQ0b.mkRegion (Some 76%nat) ?lo ?hi ?wlo ?whi ?cs) =>
let lit off n v Rt Q := pose proof (field_of_region Ex _ 76 blk cs lo hi wlo whi off n (SLit v) v HRgf HB76f ltac:(cbn; tauto) eq_refl ltac:(Rt) ltac:(cbn; lia)) as Q in
let atm off n e v He Rt Q := pose proof (field_of_region Ex _ 76 blk cs lo hi wlo whi off n e v HRgf HB76f ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by nat_side;
try rewrite (AG 32%nat) by lia; rewrite He, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(Rt) ltac:(cbn; lia)) as Q in
lazymatch type of Rres with ew _ ?nr = _ => atm 0 8%N (SOff nr 0) res Rres ltac:(cbn; clear - Hres4096 Hresceil C1; lia) Q0 end;
lit 8 8%N A_writecb ltac:(unfold A_writecb; zside) Q8; lit 16 8%N 0 ltac:(zside) Q16; lit 24 8%N 0 ltac:(zside) Q24;
atm 32 4%N (SOff 32 0) attr E32 ltac:(cbn; clear - CR24; lia) Q32; atm 36 4%N (SOff 33 0) gen E33 ltac:(cbn; clear - CR28; lia) Q36;
atm 40 2%N (SOff 34 0) loops E34 ltac:(cbn; clear - CR32; lia) Q40; atm 42 2%N (SOff 36 0) Wd E36 ltac:(cbn; clear - CR34; lia) Q42;
atm 44 2%N (SOff 37 0) Hd E37 ltac:(cbn; clear - CR36; lia) Q44;
lit 48 8%N 0 ltac:(zside) Q48; lit 56 4%N 0 ltac:(zside) Q56; lit 60 4%N R_PENDING ltac:(unfold R_PENDING; zside) Q60
end.
cbn [N.to_nat] in Q0, Q8, Q16, Q24, Q32, Q36, Q40, Q42, Q44, Q48, Q56, Q60.
cbn [obj_at LAY_Rgb]. unfold field_ok. cbn [fst snd N.to_nat Z.of_N].
change (2 ^ (8 * 8)) with (2 ^ 64). change (2 ^ (8 * 4)) with (2 ^ 32). change (2 ^ (8 * 2)) with 65536.
repeat split; try assumption;
first [unfold A_writecb, R_PENDING; clear; lia | clear - CR24 CR28 CR32 CR34 CR36 Hres4096 Hresceil C1; lia
| match goal with |- ?G => idtac "OBJLEFT" G end]. }
split.
{
lazymatch goal with |- tcgif_at (mrestrict _ ?mF) _ _ =>
apply (rg_tcgif_at_blocks_kept (w_H W7) (w_H W7) mem7 mF res st (Wd * Hd) Hat7) end.
intros b sz Hbin i Hi.
assert (Hbin7 : In (b, sz) (ablocks B ly7 S7)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm7 | apply in_app_iff; left; exact Hbin]).
destruct (al_blocks _ _ LAWS _ _ _ _ _ b sz HAR7 Hbin7) as (_ & Hq4096 & Hqceil & [_ Hqz] & Hqpres & _).
pose proof (rg_sep_app_in B LAWS ly7 S7 W7 mem7 md7 _ _ (b, sz) (blk, 64) HAR7 HPerm7 Hbin Hblk_in) as Dqb.
unfold zdisjoint, block_rng in Dqb. cbn [fst snd] in Dqb. change (req_size 64) with 64 in Dqb.
pose proof (sep_block_frame trbsegs B LAWS ly7 S7 _ _ _ b sz 1 fpos HAR7 Hbin7 Hfin7) as Dqf.
unfold zdisjoint in Dqf. cbn [fst snd] in Dqf. change (fs_frame_bytes 1) with 128 in Dqf. rewrite EFA7 in Dqf. fold F in Dqf.
assert (Hb : 0 <= b + i < 2 ^ 64) by (clear - Hi Hq4096 Hqceil C1; lia).
assert (HnZ : ~ ZsP (b + i)).
{ unfold ZsP. intros [Hq | [Hq | [Hq | [Hq | Hq]]]].
- clear - Hq Hi Dqb. lia.
- assert (HF8t : F / 8 <= 17592184995840) by (apply Z.div_le_upper_bound; [lia | clear - HFceil C1; lia]).
clear - Hq Hi Hqz HF8lo HF8t. unfold SB, kLowShadowBeg, kHighMemBeg in *. lia.
- clear - Hq Hi Dqf. lia.
- clear - Hq Hi Hqceil Hceil Hslo FFS. lia.
- apply (proj2 (Hqpres (b + i) ltac:(clear - Hi; lia))). replace (b + i) with FL by (clear - Hq; lia). exact HFLown'. }
rewrite (UNx (b + i) Hb HnZ), (UN6 (b + i) Hb HnZ).
rewrite Hfr9; [| exact Hb | unfold ZsP in HnZ; clear - HnZ; lia | unfold ZsP in HnZ; unfold ESTACK; clear - HnZ Hi Hqceil Hceil Hslo FFS; lia].
exact (UN5 (b + i) Hb HnZ). }
split; [exact Hwf7|]. split; [exact Hfr7|]. split; [exact HW7|]. split; [exact HH7|]. split; [exact Hattr7|]. split; [exact Hcur7|]. split; [exact Hih7|].
split.
{ unfold ablocks. rewrite blocks_stack_free_state. fold (ablocks B ly7 S7).
eapply Permutation_trans; [exact HPerm7|]. rewrite Ebl5, Eab. unfold RGB_SIZE.
rewrite app_assoc. apply Permutation_sym. apply Permutation_cons_append. }
intros b Hb. destruct Hb as [<- | Hb]; cbn [fst snd].
- split; [exact Tblk | intros blc i Hbl Hi; apply Ablk; [exact Hbl | change (req_size RGB_SIZE) with 64 in Hi; exact Hi]].
- destruct (Hnew7 b Hb) as [Tb Ab]. split.
+ intros Hin0 i Hi. apply Tb; [| exact Hi]. rewrite Ebl5, Eab. apply in_app_iff. left. exact Hin0.
+ intros blc i Hbl Hi. apply (rg_awr_byte_callee0 TRGBNEWGIF_STK TNEWGIF_STK (spZ regs) (spZ regs - 96) (ablocks B ly S) (ablocks B ly5 S5) blc ly7 ly7 (fst b + i));
[ apply Ab; [exact Hbl | exact Hi] | unfold TRGBNEWGIF_STK; clear; lia | clear; lia
| intros x Hx; rewrite Ebl5, Eab; apply in_app_iff; left; exact Hx ].
Qed.
End u.
End q.
