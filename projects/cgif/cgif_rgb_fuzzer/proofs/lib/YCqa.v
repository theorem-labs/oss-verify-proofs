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
YCi1 YCib YCie YCif YCid.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YI0c YG0e YCd0.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCph YCjr.
Section d. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Lemma region_kept_aview_w : forall E H (m m2 : word -> option byte) n b lo hi wlo whi cs,
bv_unsigned (ew E n) = b ->
(forall a, b + lo <= a < b + hi -> aview trbsegs H m2 a = aview trbsegs H m a) ->
(forall a, b + wlo <= a < b + whi -> apresent H m a -> apresent H m2 a) ->
region_kept trbsegs E (mrestrict H m) (mrestrict H m2) (YQ0b.mkRegion (Some n) lo hi wlo whi cs).
Proof.
intros E H m m2 n b lo hi wlo whi cs Hn Hav Hp.
split; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi base_val]; rewrite Hn; intros a Ha.
- apply (mbyte_of_aview trbsegs). apply Hav. exact Ha.
- apply writable_kept. apply Hp. exact Ha.
Qed.
Lemma aview_zero_of_val_mem : forall H (mem : word -> option byte) a (n : nat),
val_mem trbsegs (mrestrict H mem) a n 0 -> forall i, 0 <= i < Z.of_nat n -> aview trbsegs H mem (a + i) = Some 0.
Proof.
intros H mem a n Hv i Hi. unfold aview. specialize (Hv (Z.to_nat i) ltac:(lia)). rewrite Z2Nat.id in Hv by lia. rewrite Hv. cbn [option_map].
f_equal. rewrite Z_to_bv_unsigned. unfold bv_wrap, YP0g.le_byte. rewrite Z.mod_0_l by (apply Z.pow_nonzero; lia).
rewrite Z.shiftr_0_l. rewrite Z.mod_0_l by (vm_compute; discriminate). reflexivity.
Qed.
Lemma rga_ra_zero : forall H (mem : word -> option byte) F lo m,
F = 32 * (F / 32) -> 0 <= lo -> 0 <= m ->
(forall i, lo <= i < lo + m -> aview trbsegs H mem (SB + F / 8 + i) = Some 0) ->
range_addressable (aview trbsegs H mem) SHADOW_OFF (F + 8 * lo) (8 * m).
Proof.
intros H mem F lo m HFq Hlo Hm Hz.
assert (HF8 : F / 8 = 4 * (F / 32)) by (rewrite HFq at 1; replace (32 * (F / 32)) with (4 * (F / 32) * 8) by lia; rewrite Z.div_mul by lia; reflexivity).
apply zero_shadow_range.
- rewrite HFq. replace (32 * (F / 32) + 8 * lo) with ((4 * (F / 32) + lo) * 8) by lia. apply Z_mod_mult.
- rewrite Z.mul_comm. apply Z_mod_mult.
- intros i Hi. rewrite Z.mul_comm, Z.div_mul in Hi by lia. unfold shadow_of_addr. rewrite <- SB_SHADOW_OFF.
replace (SB + (F + 8 * lo) / 8 + i) with (SB + F / 8 + (lo + i)).
+ apply Hz. lia.
+ rewrite HFq at 2. rewrite HF8. replace (32 * (F / 32) + 8 * lo) with ((4 * (F / 32) + lo) * 8) by lia. rewrite Z.div_mul by lia. lia.
Qed.
End d.
Ltac rnLAWS := lazymatch goal with L : AR_laws trbsegs _ |- _ => L end.
Ltac rnTL := lazymatch goal with T : TrbLib _ |- _ => T end.
Ltac rnFFL := lazymatch goal with H : frame_flag_lawP _ _ |- _ => H end.
Ltac ga_nat_side := first [ apply (proj1 (PeanoNat.Nat.ltb_lt _ _)); vm_compute; reflexivity
| apply (proj1 (PeanoNat.Nat.eqb_neq _ _)); vm_compute; reflexivity ].
Ltac ga_rebaseE HS AG HEv :=
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
assert (H2 : ew Ev n = v) by (rewrite HEv; rewrite ?ew_ewset_other, ?ew_havoc_old by ga_nat_side; rewrite ?ew_ewset_other, ?ew_havoc_old by ga_nat_side; exact H);
clear H; rename H2 into H
end end end;
clear AG; rename AG2 into AG end end.
Ltac ga_evalE AG :=
cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia;
repeat match goal with H : ew ?Ex ?n = Z_to_bv 64 _ |- context [ew ?Ex ?n] => rewrite H end;
lazymatch type of AG with forall n, _ -> ew ?Ev n = _ =>
repeat match goal with |- context [ew Ev ?n] => lazymatch (eval cbv in (Nat.ltb n 33)) with true => rewrite (AG n) by lia end end end;
repeat match goal with H : ew ?Ex ?n = Z_to_bv 64 _ |- context [ew ?Ex ?n] => rewrite H end;
repeat match goal with H : bv_unsigned (ew ?Ex 2) = _ |- context [bv_unsigned (ew ?Ex 2)] => rewrite H end;
rewrite ?unsigned_lit_small by (unfold SB; lia); unfold SB; first [reflexivity | lia | idtac].
Ltac ga_evalE0 AG :=
cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia;
repeat match goal with H : ew ?Ex ?n = Z_to_bv 64 _ |- context [ew ?Ex ?n] => rewrite H end;
lazymatch type of AG with forall n, _ -> ew ?Ev n = _ =>
repeat match goal with |- context [ew Ev ?n] => lazymatch (eval cbv in (Nat.ltb n 33)) with true => rewrite (AG n) by lia end end end;
repeat match goal with H : ew ?Ex ?n = Z_to_bv 64 _ |- context [ew ?Ex ?n] => rewrite H end;
repeat match goal with H : bv_unsigned (ew ?Ex 2) = _ |- context [bv_unsigned (ew ?Ex 2)] => rewrite H end;
rewrite ?unsigned_lit_small by (unfold SB; lia); unfold SB.
Ltac ga_clear_frames := repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
Ltac ga_idx_of_base rs n :=
lazymatch rs with
| YQ0b.mkRegion (Some n) _ _ _ _ _ :: _ => constr:(0%nat)
| _ :: ?tl => let i := ga_idx_of_base tl n in constr:(S i)
end.
Ltac ga_aconsts HROD HJx Kgot Kcell Kguar Kuar Vgr :=
let Kc := fresh "Kc" in let Ku := fresh "Ku" in let Kg := fresh "Kg" in let Kgu := fresh "Kgu" in
let LAWS := rnLAWS in let TL := rnTL in
destruct (al_const _ _ LAWS _ _ _ _ _ (proj1 HJx)) as (Kc & Ku & Kg & Kgu);
rewrite (tl_got_shadow _ TL), (tl_shadow_cell _ TL) in Kg; rewrite (tl_shadow_cell _ TL) in Kc;
rewrite (tl_got_uar _ TL), (tl_uar_cell _ TL) in Kgu; rewrite (tl_uar_cell _ TL) in Ku;
pose proof (val_mem_of_rdword trbsegs _ _ _ _ Kg) as Kgot; pose proof (val_mem_of_rdword trbsegs _ _ _ _ Kc) as Kcell;
pose proof (val_mem_of_rdword trbsegs _ _ _ _ Kgu) as Kguar; pose proof (val_mem_of_rd32 trbsegs _ _ _ _ Ku) as Kuar;
clear Kc Ku Kg Kgu;
pose proof (arodata_val8 _ _ _ A_GOT_rgb_addframe A_cgif_rgb_addframe TL
(arodata_ok_journal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJx HROD)
ltac:(unfold A_GOT_rgb_addframe; lia) ltac:(unfold A_GOT_rgb_addframe; lia)
ltac:(intros x Hx; unfold lib_const_addr, A_GOT_rgb_addframe in *; lia)
ltac:(intros kk Hkk; do 8 (destruct kk as [|kk]; [vm_compute; reflexivity|]); lia)) as Vgr.
Ltac ga_rqs Hn := repeat (lazymatch type of Hn with context [req_size ?n] =>
let v := eval vm_compute in (req_size n) in
lazymatch v with Zpos _ => change (req_size n) with v in Hn | Z0 => change (req_size n) with v in Hn end end).
Ltac ga_kept_consts Kg Kg2 Kc Kc2 Kgu Kgu2 Ku Ku2 Vg Vg2 :=
lazymatch goal with
| |- region_kept _ _ _ _ (YQ0b.mkRegion None A_GOT_shadow _ _ _ _) => apply (region_kept_val trbsegs _ _ _ A_GOT_shadow 8 A_shadow_glob); [exact Kg | exact Kg2 | lia]
| |- region_kept _ _ _ _ (YQ0b.mkRegion None A_shadow_glob _ _ _ _) => apply (region_kept_val trbsegs _ _ _ A_shadow_glob 8 SHADOW_OFF); [exact Kc | exact Kc2 | lia]
| |- region_kept _ _ _ _ (YQ0b.mkRegion None A_GOT_uar _ _ _ _) => apply (region_kept_val trbsegs _ _ _ A_GOT_uar 8 A_uar_glob); [exact Kgu | exact Kgu2 | lia]
| |- region_kept _ _ _ _ (YQ0b.mkRegion None A_uar_glob _ _ _ _) => apply (region_kept_val trbsegs _ _ _ A_uar_glob 4 1); [exact Ku | exact Ku2 | lia]
| |- region_kept _ _ _ _ (YQ0b.mkRegion None A_GOT_rgb_addframe _ _ _ _) => apply (region_kept_val trbsegs _ _ _ A_GOT_rgb_addframe 8 A_cgif_rgb_addframe); [exact Vg | exact Vg2 | lia]
| |- region_kept _ _ _ _ (YQ0b.mkRegion None ?a _ _ _ _) =>
first [ change a with A_GOT_shadow | change a with A_shadow_glob | change a with A_GOT_uar | change a with A_uar_glob | change a with A_GOT_rgb_addframe ];
ga_kept_consts Kg Kg2 Kc Kc2 Kgu Kgu2 Ku Ku2 Vg Vg2
end.
Ltac ga_keptR HK HJx AG Usp E10 Hfin Kg Kg2 Kc Kc2 Kgu Kgu2 Ku Ku2 Vg Vg2 EFA :=
lazymatch goal with
| |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 2%nat) _ _ _ _ _) =>
eapply (region_kept_stack_aj trbsegs _); [exact HK | exact HJx | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?(AG 2%nat) by lia; exact Usp
| lia | unfold TRGBADD_STK, TRGBADD_FRAME, FDT_STK, TREE_HMAX, ASTACK; lia | lia | lia | lia]
| |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 10%nat) _ _ _ _ _) =>
eapply (region_kept_frame_aj trbsegs _); [exact HK | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?(AG 10%nat) by lia; rewrite E10; apply unsigned_lit_small; lia
| exact Hfin | rewrite ?EFA; lia | rewrite ?EFA; lia | lia | intros a Ha Hn; first [exact Hn | lia | ga_rqs Hn; zone_lia]]
| |- region_kept _ _ _ _ (YQ0b.mkRegion None _ _ _ _ _) => ga_kept_consts Kg Kg2 Kc Kc2 Kgu Kgu2 Ku Ku2 Vg Vg2
end.
Ltac ga_awrR_rec AG fpos F EFA aF aFS :=
lazymatch goal with
| |- awr_ok _ [] _ _ _ _ _ _ _ => apply awr_ok_nil
| |- awr_ok _ (YQ0b.mkRegion ?bs _ _ ?wlo ?whi _ :: _) _ _ _ _ ?blc _ _ =>
first
[ apply awr_ok_cons_ro; [cbn; lia|]
| lazymatch bs with
| Some aFS =>
eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ aFS); [reflexivity | ga_evalE AG | | ];
[ cbn [YQ0b.r_wlo YQ0b.r_whi]; intros a Ha; right; right; right; exists 7, fpos; split; [left; reflexivity|]; right;
unfold in_zr, shadow_addr; cbn [fst snd]; rewrite <- SB_SHADOW_OFF; change (fs_frame_bytes 7 / 8) with 1024; rewrite ?EFA; fold F; unfold SB; clear - Ha; lia
| ]
| Some aF =>
eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ aF); [reflexivity | ga_evalE AG | | ];
[ cbn [YQ0b.r_wlo YQ0b.r_whi]; intros a Ha; right; right; right; exists 7, fpos; split; [left; reflexivity|]; left;
unfold in_zr; cbn [fst snd]; change (fs_frame_bytes 7) with 8192; rewrite ?EFA; fold F; clear - Ha; lia
| ]
| Some 2%nat =>
eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat 0); [reflexivity | ga_evalE AG | cbn; lia | cbn; lia |]
| Some ?nb =>
match goal with Rb : ew _ nb = Z_to_bv 64 ?b, Ab : forall blc' lyq ownq i, In (?b', ?sz) blc' -> _, Hin : In (?b', ?sz) blc |- _ =>
constr_eq b b';
eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ nb); [reflexivity | ga_evalE AG | | ];
[ cbn [YQ0b.r_wlo YQ0b.r_whi]; let a := fresh "a" in let Ha := fresh "Ha" in
intros a Ha; replace a with (b + (a - b)) by lia; apply Ab; [exact Hin | clear - Ha; lia]
| ] end
end
| fail 1 "ga_awrR: no rule for the head region" ];
ga_awrR_rec AG fpos F EFA aF aFS
end.
Ltac ga_awrR AG fpos F EFA aF aFS :=
lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fp b0 bc ly own) end;
ga_awrR_rec AG fpos F EFA aF aFS.
Ltac ga_upd_above HUP HFr AG :=
let HUP' := fresh "HUP" in
lazymatch type of HFr with frame_of ?Ef ?rs (mrestrict _ ?m0) (mrestrict _ (ms_mem ?msX)) =>
lazymatch type of HUP with forall a, ?lo <= a < _ -> aview ?sg ?Hh _ a = aview _ _ ?me a =>
assert (HUP' : forall a, lo <= a < 2 ^ 64 -> aview sg Hh (ms_mem msX) a = aview sg Hh me a);
[ let a := fresh "a" in let Ha := fresh "Ha" in
intros a Ha; rewrite <- (HUP a Ha); eapply (aview_kept_frame Ef rs _ _ _ lo HFr); [lia| |exact Ha];
let b := fresh "b" in let Hb := fresh "Hb" in let rg := fresh "rg" in let Hin := fresh "Hin" in let Hrg := fresh "Hrg" in
intros b Hb (rg & Hin & Hrg);
lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In rg rs1) in Hin end; cbn [In] in Hin;
repeat (destruct Hin as [<- | Hin]; [cbn [YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi base_val] in Hrg; revert Hrg; ga_evalE AG; intros Hrg; clear - Hb Hrg; lia|]);
destruct Hin
| clear HUP; rename HUP' into HUP ] end end.
Ltac ga_keptI Hfr Hpres AG Kg Kg2 Kc Kc2 Kgu Kgu2 Ku Ku2 Vg Vg2 :=
lazymatch goal with
| |- region_kept _ _ _ _ (YQ0b.mkRegion (Some ?n) _ _ _ _ _) =>
eapply region_kept_aview; [ga_evalE AG | intros a Ha; apply Hfr; unfold ESTACK; zone_lia | exact Hpres]
| |- region_kept _ _ _ _ (YQ0b.mkRegion None _ _ _ _ _) => ga_kept_consts Kg Kg2 Kc Kc2 Kgu Kgu2 Ku Ku2 Vg Vg2
end.
Ltac rga_chain HS HJx AG EE :=
let Vra := fresh "Vra" in let Vs0 := fresh "Vs0" in let HUP := fresh "HUPc" in let Hch1 := fresh "Hch1" in
let Qceil := fresh "Qceil" in let Qal8 := fresh "Qal8" in let Qtop := fresh "Qtop" in let Qtop64 := fresh "Qtop64" in
let Qsp := fresh "Qsp" in let Qra := fresh "Qra" in let Qs0 := fresh "Qs0" in
lazymatch goal with Hch : achain ?ly (aview _ (w_H ?W) ?mem) (spZ ?regs) (s0Z _) ?ch |- _ =>
assert (Qceil : alloc_ceiling <= spZ regs) by lia;
assert (Qal8 : spZ regs mod 8 = 0) by (let D := fresh "D" in lazymatch goal with Hal32 : spZ regs mod 32 = 0 |- _ =>
pose proof (Z.div_mod (spZ regs) 32 ltac:(lia)) as D; rewrite Hal32, Z.add_0_r in D; rewrite D;
replace (32 * (spZ regs / 32)) with ((4 * (spZ regs / 32)) * 8) by lia; apply Z_mod_mult end);
assert (Qtop : spZ regs < ly_top ly - 16) by lia; assert (Qtop64 : ly_top ly <= 2 ^ 64) by lia; assert (Qsp : spZ regs - 576 + 16 <= spZ regs) by lia;
assert (Qra : 0 <= raZ regs < 2 ^ 64) by (unfold raZ; let Hq := fresh "Hq" in pose proof (bv_unsigned_in_range 64 (getr regs 1)) as Hq; change (bv_modulus 64) with (2 ^ 64) in Hq; exact Hq);
assert (Qs0 : 0 <= s0Z regs < 2 ^ 64) by (unfold s0Z; let Hq := fresh "Hq" in pose proof (bv_unsigned_in_range 64 (getr regs 8)) as Hq; change (bv_modulus 64) with (2 ^ 64) in Hq; exact Hq);
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict (w_H ?W3) ?msX) =>
assert (HUP : forall a, spZ regs <= a < 2 ^ 64 -> aview trbsegs (w_H W3) (ms_mem msX) a = aview trbsegs (w_H W) mem a)
by (let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
let F1 := fresh "F1" in pose proof HJx as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _); apply F1; [clear - Ha Qceil; lia | clear - Ha; lia]);
let rs := eval vm_compute in (ss_mem ssx) in
let i := ga_idx_of_base rs 2%nat in let i := eval vm_compute in i in
let HRstk := fresh "HRstk" in
pose proof (st_ok_region_nth Ex ssx (restrict (w_H W3) msX) i _ HS eq_refl) as HRstk; cbn [ms_mem restrict] in HRstk;
lazymatch type of HRstk with region_ok _ _ _ (YQ0b.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 2 (spZ regs) cs lo hi wlo whi (-8) 8%N (SOff 1 0) (raZ regs) HRstk
ltac:(ga_evalE AG) ltac:(cbn; tauto) ltac:(cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 1%nat) by lia; rewrite (EE 1%nat 1%bv eq_refl), Z.add_0_r; reflexivity)
ltac:(unfold raZ; let Hq := fresh "Hq" in pose proof (bv_unsigned_in_range 64 (getr regs 1)) as Hq; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Hq; exact Hq) ltac:(cbn; lia)) as Vra;
pose proof (field_of_region Ex _ 2 (spZ regs) cs lo hi wlo whi (-16) 8%N (SOff 8 0) (s0Z regs) HRstk
ltac:(ga_evalE AG) ltac:(cbn; tauto) ltac:(cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 8%nat) by lia; rewrite (EE 8%nat 8%bv eq_refl), Z.add_0_r; reflexivity)
ltac:(unfold s0Z; let Hq := fresh "Hq" in pose proof (bv_unsigned_in_range 64 (getr regs 8)) as Hq; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Hq; exact Hq) ltac:(cbn; lia)) as Vs0 end;
clear HRstk;
assert (Hch1 : achain ly (aview trbsegs (w_H W3) (ms_mem msX)) (spZ regs - 576) (spZ regs) ((spZ regs, raZ regs, s0Z regs) :: ch));
[ replace (spZ regs - 8) with (spZ regs + -8) in Vra by lia; replace (spZ regs - 16) with (spZ regs + -16) in Vs0 by lia;
lazymatch goal with Hra4 : 4096 <= raZ regs |- _ =>
exact (achain_push ly _ _ (spZ regs) (s0Z regs) (raZ regs) _ (spZ regs - 576) Hch Qtop64 HUP
(rdword_of_val_mem trbsegs _ _ _ _ Vra Qra) (rdword_of_val_mem trbsegs _ _ _ _ Vs0 Qs0) Hra4 Qceil Qal8 Qtop Qsp) end
| ] end end.
Ltac ga_fs_ro HS :=
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := ga_idx_of_base rs 67%nat in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rs got_region) in
let HS3 := fresh "HS3" in
pose proof (ast_ok_set_region trbsegs Ex ssx msx i r (set_window r 0 0) HS ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity)
(region_ok_rewindow trbsegs Ex _ r 0 0 (st_ok_region_nth Ex ssx msx i r HS ltac:(vm_compute; reflexivity)) ltac:(intros o Ho; lia))) as HS3;
clear HS; rename HS3 into HS; norm_ss HS end.
Ltac ga_fs_rw HS E55 Hp :=
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := ga_idx_of_base rs 67%nat in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rs got_region) in
let HS3 := fresh "HS3" in
pose proof (ast_ok_set_region trbsegs Ex ssx msx i r (set_window r 0 16) HS ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity)
(region_ok_rewindow trbsegs Ex _ r 0 16 (st_ok_region_nth Ex ssx msx i r HS ltac:(vm_compute; reflexivity))
ltac:(cbn [YQ0b.r_base base_val ms_mem restrict mkst]; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia;
rewrite E55, unsigned_lit_small by (unfold SB; lia);
intros o Ho; apply (apresent_writable trbsegs); unfold shadow_addr in Hp; rewrite <- SB_SHADOW_OFF in Hp;
apply (proj1 (Hp o ltac:(clear - Ho; lia)))))) as HS3;
clear HS; rename HS3 into HS; norm_ss HS end.
Ltac ga_creg HS AG EE :=
lazymatch goal with |- getr _ ?r = getr _ _ =>
let R := fresh "R" in rreg HS r R; rewrite R; clear R;
cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite AG by lia;
apply EE; reflexivity end.
Ltac ga_add_flag_region HS AG E54 Hp HFLrng HFLown HnoG HnoC HnoF :=
let Qceil := match goal with H : alloc_ceiling <= ly_stk_lo _ |- _ => H end in
let Qslo := match goal with H : ly_stk_lo _ + _ <= spZ _ |- _ => H end in
let QC1 := match goal with H : _ <= alloc_ceiling <= _ |- _ => H end in
let QC3 := match goal with H : kHighMemBeg = _ |- _ => H end in
let QFFS := match goal with H : TRGBADD_STK = _ |- _ => H end in
let QFq := match goal with H : ?Fr = 32 * (?Fr / 32) |- _ => H end in
let QF8 := match goal with H : ?Fr / 8 = 4 * (?Fr / 32) |- _ => H end in
let QFceil := match goal with H : ?Fr + 8192 <= alloc_ceiling |- _ => H end in
let QF8lo := match goal with H : 512 <= ?Fr / 8 |- _ => H | _ => QFq end in
let QF8hi := match goal with H : ?Fr / 8 < 17592186044416 |- _ => H | _ => QFq end in
lazymatch type of HS with st_ok _ ?Ev _ _ =>
let HS3 := fresh "HS3" in
pose proof (ast_ok_add_region trbsegs Ev _ _ (YQ0b.mkRegion (Some 66%nat) 0 1 0 1 []) HS eq_refl
ltac:(unfold region_ok; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val ms_mem restrict mkst];
rewrite ?ew_ewset_other by lia; rewrite E54, unsigned_lit_small by lia; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
intros o Ho; apply (apresent_writable trbsegs); lazymatch goal with |- apresent _ _ (?fl + ?oo) => replace (fl + oo) with fl by lia end; exact Hp)
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val]; ga_evalE0 AG;
unfold A_GOT_shadow, A_shadow_glob, A_GOT_uar, A_uar_glob, A_GOT_rgb_addframe;
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
Ltac ga_wrangeR AG fpos F EFA EFL :=
let a := fresh "a" in let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
intros a (r & Hin & Hr); rewrite ?EFA, ?EFL;
lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end;
cbn [In] in Hin;
repeat (destruct Hin as [<- | Hin];
[ cbn [YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi base_val] in Hr; revert Hr; ga_evalE0 AG; intros Hr;
first [ exfalso; clear - Hr; lia
| right; clear - Hr; lia
| left; left; clear - Hr; unfold TRGBADD_STK, TRGBADD_FRAME, FDT_STK, TREE_HMAX, ASTACK; lia
| left; right; right; right; exists 7, fpos; split; [left; reflexivity|];
first [ left; unfold in_zr; cbn [fst snd]; change (fs_frame_bytes 7) with 8192; rewrite ?EFA; fold F; clear - Hr; lia
| right; unfold in_zr, shadow_addr; cbn [fst snd]; rewrite <- SB_SHADOW_OFF; change (fs_frame_bytes 7 / 8) with 1024; rewrite ?EFA; fold F; unfold SB; clear - Hr; lia ]
| left; match goal with A : forall blc lyq ownq i, In (?r, 64) blc -> _, Hin : In (?r, 64) (ablocks _ _ _) |- _ =>
replace a with (r + (a - r)) by lia; apply A; [exact Hin | clear - Hr; lia] end
| match goal with |- ?g => match type of Hr with ?t => idtac "WRFAIL" t g end end; fail 2 "ga_wrangeR" ]
| ]);
destruct Hin.
Ltac ga_flag0 E54 EFL :=
let msr := fresh "msr" in let HSr := fresh "HSr" in let HR := fresh "HR" in let V := fresh "V" in
intros msr HSr; rewrite ?EFL;
lazymatch type of HSr with st_ok _ ?Ex ?ssx _ =>
pose proof (st_ok_region_nth Ex ssx msr 0 _ HSr eq_refl) as HR;
lazymatch type of HR with region_ok _ _ _ (YQ0b.mkRegion (Some ?n) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex (ms_mem msr) n _ cs lo hi wlo whi 0 1%N (SLit 0) 0 HR
ltac:(cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E54; apply unsigned_lit_small; lia)
ltac:(left; reflexivity) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as V end end;
rewrite Z.add_0_r in V; pose proof (V 0%nat ltac:(lia)) as V0; cbn [Z.of_nat] in V0; rewrite Z.add_0_r in V0; exact V0.
Ltac ga_exitG HS HJx AG fpos F cfgp E54 E55 Hfin HfinS EE Hra HEV EFA EFL :=
let HFLpres' := fresh "HFLpres'" in let HFLown := fresh "HFLown'" in let HFLrng := fresh "HFLrng'" in
let HFpres' := fresh "HFpres'" in let HFSpres' := fresh "HFSpres'" in
let HCpres' := fresh "HCpres'" in
let HnoC := fresh "HnoC" in let HnoF := fresh "HnoF" in
let FFL := rnFFL in let LAWS := rnLAWS in destruct (FFL _ _ _ _ _ 7 fpos (proj1 HJx) Hfin) as (HFLpres' & HFLown & HFLrng); rewrite ?EFL in HFLpres'; rewrite ?EFL in HFLown; rewrite ?EFL in HFLrng; fold F in HFLrng;
destruct (al_frames _ _ LAWS _ _ _ _ _ 7 fpos (proj1 HJx) Hfin) as (_ & _ & HFpres' & HFSpres'); change (fs_frame_bytes 7) with 8192 in HFpres', HFSpres';
change (8192 / 8) with 1024 in HFSpres'; rewrite ?EFA in HFpres'; rewrite ?EFA in HFSpres'; fold F in HFpres', HFSpres';
destruct (al_frames _ _ LAWS _ _ _ _ _ _ _ (proj1 HJx) HfinS) as (_ & _ & HCpres' & _); rewrite ?EFA in HCpres';
lazymatch type of HFpres' with forall a, _ -> _ /\ ~ aowned ?B ?lyx ?Sx a =>
assert (HnoC : forall a, cfgp <= a < cfgp + 40 -> ~ aowned B lyx Sx a) by (intros a Ha; apply (fun H => proj2 (HCpres' a H)); lia);
assert (HnoF : forall a, F <= a < F + 8192 -> ~ aowned B lyx Sx a) by (intros a Ha; exact (proj2 (HFpres' a Ha))) end;
ga_fs_rw HS E55 HFSpres';
ga_add_flag_region HS AG E54 HFLpres' HFLrng HFLown HnoC HnoC HnoF;
aj_run_flag_sh trbtbl_lib_ok HS HJx; [lia | ga_wrangeR AG fpos F EFA EFL | ga_flag0 E54 EFL |];
let R1 := fresh "R1" in let R10 := fresh "R10" in
rreg HS (1%bv : bv 5) R1; rreg HS (10%bv : bv 5) R10;
lazymatch goal with |- SRr _ ?Wx _ _ =>
eapply (SRr_ret_at trbsegs trbtbl_lib trbtbl_lib_ok Hwx_tfa Wx _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)) end;
let mat' := fresh "mat'" in intros mat'; unfold trgb_addframe_post, apost_base;
lazymatch type of HJx with ajournal _ _ _ _ _ _ _ _ _ _ _ ?lyx ?Sx _ _ _ _ =>
lazymatch goal with |- exists ly' S' regs' mem' md', mkCfg (mkst ?rg _ ?mm _) ?mdx = _ /\ _ => exists lyx, Sx, rg, mm, mdx end end;
split; [rewrite R1; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 1%nat) by lia; rewrite (EE 1%nat 1%bv eq_refl), Hra; reflexivity|];
split; [cbn [ms_mem]; eapply (ajournal_mono_k trbsegs _); [apply (ajournal_materialize trbsegs _ LAWS trb_segs_low); exact HJx | rewrite HEV; unfold EV_NEWGIF, EV_RAWNEW; lia]|];
split; [apply aregs_preserved_eqs; ga_creg HS AG EE|];
rewrite R10.
Ltac ga_keptF HK AG RF E55 HfinX HFP HFSP HEr F EFA :=
lazymatch goal with
| |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 66%nat) _ _ _ _ _) =>
eapply (region_kept_ownframe_aj trbsegs _); [exact HK | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite RF; apply unsigned_lit_small; lia
| exact HfinX | left; change (fs_frame_bytes 7) with 8192; rewrite ?EFA; fold F; lia
| let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; cbn beta; first [exact (fun Hn : False => Hn) | apply HEr; lia]
| let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; apply (fun H => proj1 (HFP a H)); lia ]
| |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 67%nat) _ _ _ _ _) =>
eapply (region_kept_ownframe_aj trbsegs _); [exact HK | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E55; apply unsigned_lit_small; unfold SB; lia
| exact HfinX | right; unfold shadow_addr; rewrite <- SB_SHADOW_OFF; change (fs_frame_bytes 7 / 8) with 1024; rewrite ?EFA; fold F; lia
| let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; first [exact (fun Hn : False => Hn) | let Hn := fresh "Hn" in intros Hn; ga_rqs Hn; unfold SB in Ha; zone_lia]
| let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; unfold shadow_addr in HFSP; rewrite <- ?SB_SHADOW_OFF in HFSP;
first [lia | apply (fun H => proj1 (HFSP (a - (SB + F / 8)) H)); lia | replace a with (SB + F / 8 + (a - (SB + F / 8))) by lia; apply (fun H => proj1 (HFSP (a - (SB + F / 8)) H)); lia] ]
end.
Ltac ga_oblF HJx HE10 HE35 HRA HAR Hfin Hcid0 Hflo Hfhi Hfal :=
lazymatch goal with |- range_addressable _ (U ?Ex _) (U _ (SOff 10 ?c)) ?len =>
lazymatch type of HE10 with _ = Z_to_bv 64 ?cfgp =>
first [ rewrite (U_atom_off Ex 10 cfgp c); [| cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact HE10 | lia | lia]
| rewrite (U_atom Ex 10 cfgp); [| cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact HE10 | lia] ];
eapply (obl_of_range trbsegs _ _ Ex (SOff 44 0) _ len cfgp 40);
[ let L := rnLAWS in eapply (range_addressable_entry_frame trbsegs _ L); [exact HJx | exact Hfin | exact Hcid0 | exact Hflo | exact Hfhi | exact Hfal
| intros x Hx; exfalso; exact (inFP_nil x Hx) | exact HAR | exact HRA]
| rewrite (U_atom Ex 44 SB); [reflexivity | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact HE35 | unfold SB; lia]
| lia | lia ] end end.
Ltac ga_keptJ HJc HJx AG Usp E10 RF E55 Hfin HfinS FFS Kg Kg2 Kc Kc2 Kgu Kgu2 Ku Ku2 Vg Vg2 EFA HFP HFSP HCP F fptac :=
let L := rnLAWS in
lazymatch goal with
| |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 2%nat) _ _ _ _ _) =>
eapply (region_kept_stack_sub trbsegs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 2%nat);
[exact HJc | exact HJx | ga_evalE AG; exact Usp | clear; lia | rewrite FFS; clear; lia | clear; lia | clear; lia | clear; lia]
| |- region_kept _ _ _ _ (YQ0b.mkRegion None A_GOT_shadow _ _ _ _) => apply (region_kept_val trbsegs _ _ _ A_GOT_shadow 8 A_shadow_glob); [exact Kg | exact Kg2 | clear; lia]
| |- region_kept _ _ _ _ (YQ0b.mkRegion None A_shadow_glob _ _ _ _) => apply (region_kept_val trbsegs _ _ _ A_shadow_glob 8 SHADOW_OFF); [exact Kc | exact Kc2 | clear; lia]
| |- region_kept _ _ _ _ (YQ0b.mkRegion None A_GOT_uar _ _ _ _) => apply (region_kept_val trbsegs _ _ _ A_GOT_uar 8 A_uar_glob); [exact Kgu | exact Kgu2 | clear; lia]
| |- region_kept _ _ _ _ (YQ0b.mkRegion None A_uar_glob _ _ _ _) => apply (region_kept_val trbsegs _ _ _ A_uar_glob 4 1); [exact Ku | exact Ku2 | clear; lia]
| |- region_kept _ _ _ _ (YQ0b.mkRegion None A_GOT_rgb_addframe _ _ _ _) => apply (region_kept_val trbsegs _ _ _ A_GOT_rgb_addframe 8 A_cgif_rgb_addframe); [exact Vg | exact Vg2 | clear; lia]
| |- region_kept _ _ _ _ (YQ0b.mkRegion None ?a _ _ _ _) =>
first [ change a with A_GOT_shadow | change a with A_shadow_glob | change a with A_GOT_uar | change a with A_uar_glob | change a with A_GOT_rgb_addframe ];
ga_keptJ HJc HJx AG Usp E10 RF E55 Hfin HfinS FFS Kg Kg2 Kc Kc2 Kgu Kgu2 Ku Ku2 Vg Vg2 EFA HFP HFSP HCP F fptac
| |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 10%nat) _ _ _ _ _) =>
eapply (rg_region_kept_frame_sub _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 10%nat); [exact HJc | ga_evalE AG; first [exact E10 | rewrite E10; apply unsigned_lit_small; lia] | exact HfinS
| rewrite ?EFA; lia | rewrite ?EFA; lia
| first [let a := fresh "a" in let Ha := fresh "Ha" in let Hn := fresh "Hn" in intros a Ha Hn; exact (inFP_nil _ Hn) | fptac]
| let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; first [lia | apply (fun H => proj1 (HCP a H)); lia] ]
| |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 66%nat) _ _ _ _ _) =>
eapply (rg_region_kept_frame_sub _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 54%nat); [exact HJc | ga_evalE AG; first [exact RF | rewrite RF; apply unsigned_lit_small; lia] | exact Hfin
| rewrite ?EFA; fold F; change (fs_frame_bytes 7) with 8192; lia | rewrite ?EFA; fold F; change (fs_frame_bytes 7) with 8192; lia
| first [let a := fresh "a" in let Ha := fresh "Ha" in let Hn := fresh "Hn" in intros a Ha Hn; exact (inFP_nil _ Hn) | fptac]
| let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; apply (fun H => proj1 (HFP a H)); lia ]
| |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 67%nat) _ _ _ _ _) =>
eapply (rg_region_kept_fshadow_sub _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 67%nat); [exact HJc | ga_evalE AG; first [exact E55 | rewrite E55; apply unsigned_lit_small; unfold SB; lia] | exact Hfin
| rewrite ?EFA; fold F; unfold shadow_addr; rewrite <- SB_SHADOW_OFF; unfold SB; lia | rewrite ?EFA; fold F; unfold shadow_addr; rewrite <- SB_SHADOW_OFF; change (fs_frame_bytes 7 / 8) with 1024; unfold SB; lia
| first [let a := fresh "a" in let Ha := fresh "Ha" in let Hn := fresh "Hn" in intros a Ha Hn; exact (inFP_nil _ Hn) | fptac]
| let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; unfold SB in Ha; lia ]
| |- region_kept _ _ _ _ (YQ0b.mkRegion (Some ?nb) _ _ _ _ ?cs) =>
match goal with Rb : ew _ nb = Z_to_bv 64 ?b, Hin : In (?b', ?sz) (ablocks _ _ _), Hin2 : In (?b'', ?sz') (ablocks _ _ _) |- _ =>
constr_eq b b'; constr_eq b b''; constr_eq sz sz';
let L := rnLAWS in eapply (rg_region_kept_block_subw2 _ L); [exact HJc | ga_evalE AG; first [exact Rb | rewrite Rb; apply unsigned_lit_small; lia] | exact Hin | exact Hin2
| clear; lia | let v := eval vm_compute in (req_size sz) in change (req_size sz) with v; clear; lia | clear; lia | clear; lia
| first [let a := fresh "a" in let Ha := fresh "Ha" in let Hn := fresh "Hn" in intros a Ha Hn; exact (inFP_nil _ Hn) | fptac] ] end
end.
Ltac ga_obl_blk HJx HEn HEbx Hin :=
let L := rnLAWS in
lazymatch goal with |- range_addressable _ (U ?Ex (SOff ?bx 0)) (U _ (SOff ?n ?c)) ?len =>
lazymatch type of HEn with _ = Z_to_bv 64 ?p =>
lazymatch type of Hin with In (_, ?sz) _ =>
first [ rewrite (U_atom_off Ex n p c); [| cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact HEn | lia | lia]
| rewrite (U_atom Ex n p); [| cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact HEn | lia] ];
eapply (obl_of_block trbsegs _ L _ _ _ _ _ Ex (SOff bx 0) _ len p sz (proj1 HJx) Hin);
[ rewrite (U_atom Ex bx SB); [reflexivity | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact HEbx | unfold SB; lia]
| lia | let v := eval vm_compute in (req_size sz) in change (req_size sz) with v; lia ] end end end.
Definition gbox (P : Prop) : Prop := P.
Ltac gboxh H := lazymatch type of H with ?T => change T with (gbox T) in H end.
Ltac gunbox := unfold gbox in *.
Ltac ga_zl1 := unfold SB, A_GOT_shadow, A_shadow_glob, A_GOT_uar, A_uar_glob, A_GOT_rgb_addframe in *; zones; lia.
Ltac ga_zlia_k k :=
repeat match goal with |- forall _ : Z, _ => intro | |- _ -> _ => intro end;
first
[ match goal with H : gbox ?T |- _ => lazymatch T with context [k] => idtac end; solve [unfold gbox in H; ga_zl1] end
| solve [ga_zl1]
| match goal with H : gbox _ |- _ => solve [unfold gbox in H; ga_zl1] end
| match goal with H1 : gbox _ |- _ => match goal with H2 : gbox _ |- _ => solve [unfold gbox in H1, H2; ga_zl1] end end
| idtac "ga_zlia_k: FALLBACK (all boxes open)" k; gunbox; unfold SB in *; zone_lia ].
Ltac ga_zlia :=
repeat match goal with |- forall _ : Z, _ => intro | |- _ -> _ => intro end;
first
[ solve [ga_zl1]
| match goal with H : gbox _ |- _ => solve [unfold gbox in H; ga_zl1] end
| match goal with H1 : gbox _ |- _ => match goal with H2 : gbox _ |- _ => solve [unfold gbox in H1, H2; ga_zl1] end end
| idtac "ga_zlia: FALLBACK (all boxes open)"; gunbox; unfold SB in *; zone_lia ].
Ltac ga_key b := lazymatch b with | _ + ?y / 8 => y | _ + ?y / 8 + _ => y | _ => b end.
Ltac ga_keptV Hfr Hoff AG Kg Kg2 Kc Kc2 Kgu Kgu2 Ku Ku2 Vg Vg2 :=
lazymatch goal with
| |- region_kept _ _ _ _ (YQ0b.mkRegion (Some ?n) _ _ _ _ _) =>
eapply region_kept_aview_w;
[ ga_evalE AG
| lazymatch goal with |- forall a, ?b + _ <= a < _ -> _ => let k := ga_key b in
let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; apply Hfr; [ga_zlia_k k | ga_zlia_k k] end
| lazymatch goal with |- forall a, ?b + ?wlo <= a < ?b + ?whi -> _ => let k := ga_key b in
let a := fresh "a" in let Ha := fresh "Ha" in let Hp := fresh "Hp" in let Hi := fresh "Hi" in let Hq := fresh "Hq" in
intros a Ha Hp;
first [ exfalso; clear - Ha; lia
| apply Hoff; [ga_zlia_k k | intros Hi; pose proof (trb_img_range a Hi) as Hq; clear Hi; ga_zlia_k k | exact Hp] ] end ]
| |- region_kept _ _ _ _ (YQ0b.mkRegion None _ _ _ _ _) => ga_kept_consts Kg Kg2 Kc Kc2 Kgu Kgu2 Ku Ku2 Vg Vg2
end.
Ltac ga_keptI2 Hfr Hpres AG Kg Kg2 Kc Kc2 Kgu Kgu2 Ku Ku2 Vg Vg2 :=
lazymatch goal with
| |- region_kept _ _ _ _ (YQ0b.mkRegion (Some ?n) _ _ _ _ _) =>
eapply region_kept_aview;
[ ga_evalE AG
| lazymatch goal with |- forall a, ?b + _ <= a < _ -> _ => let k := ga_key b in
let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; apply Hfr; unfold ESTACK; [ga_zlia_k k | ga_zlia_k k | ga_zlia_k k] end
| exact Hpres ]
| |- region_kept _ _ _ _ (YQ0b.mkRegion None _ _ _ _ _) => ga_kept_consts Kg Kg2 Kc Kc2 Kgu Kgu2 Ku Ku2 Vg Vg2
end.
Ltac ga_idx_of_base_lo rs n lo :=
lazymatch rs with
| YQ0b.mkRegion (Some n) lo _ _ _ _ :: _ => constr:(0%nat)
| _ :: ?tl => let i := ga_idx_of_base_lo tl n lo in constr:(S i)
end.
Ltac ga_find_zero_chunk cs cur :=
lazymatch cs with
| YQ0b.mkChunk cur (CVal ?w (SLit 0)) :: _ => w
| _ :: ?tl => ga_find_zero_chunk tl cur
end.
Ltac ga_zero_cases Ex HR n b cs lo hi wlo whi i AG cur fuel :=
lazymatch fuel with
| O => exfalso; lia
| S ?fuel' =>
first
[ let w := ga_find_zero_chunk cs cur in
let wz := eval vm_compute in (Z.of_N w) in
let nxt := eval vm_compute in (cur + wz) in
let H2 := fresh "Hc" in
destruct (Z_lt_ge_dec i nxt) as [H2|H2];
[ replace (b + i) with (b + cur + (i - cur)) by lia;
eapply (aview_zero_of_val_mem _ _ _ (N.to_nat w));
[ eapply (field_of_region Ex _ n b _ lo hi wlo whi cur w (SLit 0) 0 HR); [ga_evalE AG | cbn; tauto | reflexivity | cbn; lia | cbn; lia]
| cbn; lia ]
| ga_zero_cases Ex HR n b cs lo hi wlo whi i AG nxt fuel' ]
| exfalso; lia ]
end.
Ltac ga_ra_frame HS AG HFq F rlo lo m H :=
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict (w_H ?Wx) ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let idx := ga_idx_of_base_lo rs 67%nat rlo in let idx := eval vm_compute in idx in
let HR := fresh "HRfs" in
pose proof (st_ok_region_nth Ex ssx (restrict (w_H Wx) msX) idx _ HS eq_refl) as HR; cbn [ms_mem restrict] in HR;
lazymatch type of HR with region_ok _ _ _ (YQ0b.mkRegion (Some ?n) ?rl ?rh ?wlo ?whi ?cs) =>
assert (H : range_addressable (aview trbsegs (w_H Wx) (ms_mem msX)) SHADOW_OFF (F + 8 * lo) (8 * m));
[ apply (rga_ra_zero _ _ F lo m HFq); [lia | lia |];
let i := fresh "i" in let Hi := fresh "Hi" in intros i Hi;
ga_zero_cases Ex HR n (SB + F / 8) cs rl rh wlo whi i AG lo 200%nat
| clear HR ] end end.
Ltac ga_fs_ro_lo HS lo :=
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := ga_idx_of_base_lo rs 67%nat lo in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rs got_region) in
let HS3 := fresh "HS3" in
pose proof (ast_ok_set_region trbsegs Ex ssx msx i r (set_window r 0 0) HS ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity)
(region_ok_rewindow trbsegs Ex _ r 0 0 (st_ok_region_nth Ex ssx msx i r HS ltac:(vm_compute; reflexivity)) ltac:(intros o Ho; lia))) as HS3;
clear HS; rename HS3 into HS; norm_ss HS end.
Ltac ga_subregion_tac :=
unfold subregion; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks];
split; [reflexivity|]; split; [lia|]; split; [lia|]; split; [lia|];
let c := fresh "c" in let Hc := fresh "Hc" in intros c Hc; cbn in Hc |- *;
first [exact Hc | solve [destruct Hc] | tauto].
Ltac ga_submem_to := repeat (first [apply submem_keep; [ga_subregion_tac|] | apply submem_drop]); apply submem_nil.
Ltac ga_incl_lit_tac :=
let x := fresh "x" in let Hx := fresh "Hx" in
intros x Hx; cbn in Hx; cbn;
repeat (destruct Hx as [<- | Hx]; [repeat (first [left; reflexivity | right]) |]); destruct Hx.
Ltac ga_set_regs_rec HS N vals i rl :=
lazymatch rl with
| [] => idtac
| ?r :: ?rl' =>
lazymatch type of HS with st_ok _ ?Ev ?ssx ?msx =>
let HS3 := fresh "HS3" in let Hv := fresh "Hv" in
let n := eval vm_compute in (N + i)%nat in
assert (Hv : sv_denot Ev (SOff n 0) = getr (ms_regs msx) r);
[ cbn [sv_denot]; rewrite Z.add_0_r; rewrite Z_to_bv_bv_unsigned; change n with (N + i)%nat;
rewrite (ew_havoc_new _ N vals i (Z_to_bv 64 0)) by (cbn [length]; lia); cbn [nth ms_regs restrict]; reflexivity | ];
pose proof (ast_ok_set_reg_fp trbsegs Ev ssx msx r (SOff n 0) HS ltac:(vm_compute; reflexivity) Hv) as HS3;
clear HS Hv; rename HS3 into HS; norm_ss HS; ga_set_regs_rec HS N vals (S i) rl' end
end.
Ltac ga_join HS target N deads hook :=
norm_ss HS;
let tg := eval red in target in
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
let HS3 := fresh "HS3" in
let rs := eval cbn [ss_mem] in (ss_mem tg) in
pose proof (st_ok_submem trbsegs Ex ssx msx rs HS ltac:(cbn [ss_mem]; ga_submem_to) ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS end;
norm_ss HS;
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
let HS3 := fresh "HS3" in
let dl := eval cbv in deads in
let vals := constr:(map (fun r : bv 5 => getr (ms_regs msx) r) dl) in
let vals' := eval cbn [map ms_regs restrict] in vals in
pose proof (st_ok_havoc trbsegs N Ex ssx msx vals' HS ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS;
ga_set_regs_rec HS N vals' 0%nat dl end;
norm_ss HS;
hook;
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
let HS3 := fresh "HS3" in
let fa := eval cbn [ss_facts f_atoms] in (f_atoms (ss_facts tg)) in
let cs := eval cbn [ss_facts f_conds] in (f_conds (ss_facts tg)) in
let al := eval cbn [ss_facts f_alias] in (f_alias (ss_facts tg)) in
pose proof (st_ok_facts_incl3 trbsegs Ex ssx msx fa cs al HS ltac:(ga_incl_lit_tac) ltac:(ga_incl_lit_tac) ltac:(ga_incl_lit_tac)) as HS3;
clear HS; rename HS3 into HS end;
norm_ss HS;
lazymatch type of HS with st_ok _ _ ?ssx _ => first [change ssx with target in HS | idtac "JOIN-MISMATCH" ssx tg] end.
Ltac ga_join_val HS N i R En :=
lazymatch type of HS with st_ok _ ?Ev _ _ =>
lazymatch Ev with havoc _ _ ?vals =>
lazymatch type of R with _ = ?v =>
let n := eval vm_compute in (N + i)%nat in
assert (En : ew Ev n = v);
[ change n with (N + i)%nat; rewrite (ew_havoc_new _ N vals i (Z_to_bv 64 0)) by (cbn [length]; lia); cbn [nth]; exact R | ] end end end.
Ltac ga_join_fact HS n af tac :=
lazymatch type of HS with st_ok _ ?Ev ?ssx ?msx =>
let HS3 := fresh "HS3" in
pose proof (st_ok_add_fact trbsegs Ev ssx msx n af HS ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; tac)) as HS3;
clear HS; rename HS3 into HS end.
