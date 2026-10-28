(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI09 YI08 YI0m YI0n YI0s YCbw.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0d YP0c YI0w YI0x YC4a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC80 YC1f YC1g YC1h YC81 YC4b YC44 YC45 YC44.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC20.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC1i.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACjr.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
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
Ltac evalE AG :=
cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia;
repeat match goal with H : ew ?Ex ?n = Z_to_bv 64 _ |- context [ew ?Ex ?n] => rewrite H end;
lazymatch type of AG with forall n, _ -> ew ?Ev n = _ =>
repeat match goal with |- context [ew Ev ?n] => lazymatch (eval cbv in (Nat.ltb n 33)) with true => rewrite (AG n) by lia end end end;
repeat match goal with H : ew ?Ex ?n = Z_to_bv 64 _ |- context [ew ?Ex ?n] => rewrite H end;
repeat match goal with H : bv_unsigned (ew ?Ex 2) = _ |- context [bv_unsigned (ew ?Ex 2)] => rewrite H end;
rewrite ?unsigned_lit_small by (unfold SB; lia); unfold SB; first [reflexivity | lia | idtac].
Ltac idx_of_base rs n :=
lazymatch rs with
| YP09.mkRegion (Some n) _ _ _ _ _ :: _ => constr:(0%nat)
| _ :: ?tl => let i := idx_of_base tl n in constr:(S i)
end.
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
Ltac clear_frames := repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
Ltac subregion_tac :=
unfold subregion; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks];
split; [reflexivity|]; split; [lia|]; split; [lia|]; split; [lia|];
let c := fresh "c" in let Hc := fresh "Hc" in intros c Hc; cbn in Hc |- *;
first [exact Hc | solve [destruct Hc] | tauto].
Ltac submem_to := repeat (first [apply submem_keep; [subregion_tac|] | apply submem_drop]); apply submem_nil.
Ltac incl_lit_tac :=
let x := fresh "x" in let Hx := fresh "Hx" in
intros x Hx; cbn in Hx; cbn;
repeat (destruct Hx as [<- | Hx]; [repeat (first [left; reflexivity | right]) |]); destruct Hx.
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
Ltac jafter_stretch_keep HS k regs2 mem2 clob newpc idxs HS2 :=
lazymatch type of HS with
| st_ok ?segs ?E ?ss ?ms =>
let rs := eval vm_compute in (pick (ss_mem ss) idxs) in
pose proof (st_ok_after_stretch segs k E ss ms regs2 mem2 rs newpc clob HS eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(vm_compute; reflexivity) ltac:(submem_tac) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) as HS2;
let ss2 := eval vm_compute in (ss_after_stretch ss rs k clob newpc) in
change (ss_after_stretch ss rs k clob newpc) with ss2 in HS2
end.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg lib_asan3_0_listing}.
Context {RO : YC20.ro_below_ofl (@pa_segs _ lib_asan3_0_listing PI) (@pa_relro_lo _ lib_asan3_0_listing PI) (@pa_relro_hi _ lib_asan3_0_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ lib_asan3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_asan3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_asan3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_asan3_0_listing PI A_TEXT).
Ltac eimg_low := rewrite ?Eimg_low by (unfold A_TEXT; lia).
Lemma rn_st_ok_any : forall E pc sr (regsM : bvmap 5 word) (rs : smem) (G : facts) mem,
regs_ok E sr regsM -> regions_wf rs = true -> Forall (region_ok SEGS E mem) rs -> pairwise_disjoint E rs -> facts_ok E G ->
st_ok SEGS E (mkSS pc sr rs None G) (mkst regsM (Z_to_bv 64 pc) mem (seg_rom SEGS)).
Proof.
intros E pc sr regsM rs G mem Hsr Hwf Hrs Hpd HG.
unfold st_ok. cbn [ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_regs ms_mem mkst ss_pc ss_regs ss_mem ss_resv ss_facts resv_denot].
repeat (split; [reflexivity|]). split; [exact Hsr|]. split; [| exact HG]. split; [exact Hwf|]. split; [exact Hrs | exact Hpd].
Qed.
Lemma aview_wrap : forall H (m : word -> option byte) a, aview SEGS H m a = aview SEGS H m (a mod 2 ^ 64).
Proof.
intros H m a. unfold aview, mbyte, mrestrict.
replace (Z_to_bv 64 (a mod 2 ^ 64)) with (Z_to_bv 64 a); [reflexivity|].
apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_mod by lia. reflexivity.
Qed.
Lemma aview_kept_nil : forall E H (m m' : word -> option byte),
frame_of E [] (mrestrict H m) (mrestrict H m') -> forall a, aview SEGS H m' a = aview SEGS H m a.
Proof.
intros E H m m' HF a. rewrite (aview_wrap H m' a), (aview_wrap H m a).
apply (aview_kept_frame E [] H m m' 0 HF ltac:(lia)); [| apply Z.mod_pos_bound; lia].
intros x Hx (r & Hin & _). exact Hin.
Qed.
Lemma regions_kept_all : forall E H (m m2 : word -> option byte) rs,
(forall a, aview SEGS H m2 a = aview SEGS H m a) -> (forall a, apresent H m a -> apresent H m2 a) ->
Forall (region_kept SEGS E (mrestrict H m) (mrestrict H m2)) rs.
Proof.
intros E H m m2 rs Hav Hpr. apply Forall_forall. intros r _. split; intros a Ha.
- apply (mbyte_of_aview SEGS). apply Hav.
- apply writable_kept. apply Hpr.
Qed.
Lemma aview_kept_out : forall E rs H (m m' : word -> option byte),
frame_of E rs (mrestrict H m) (mrestrict H m') ->
forall a, 0 <= a < 2 ^ 64 -> ~ in_wrange E rs a -> aview SEGS H m' a = aview SEGS H m a.
Proof.
intros E rs H m m' HF a Ha Hno. apply aview_eq_of. apply HF. rewrite unsigned_lit_small by lia. exact Hno.
Qed.
Definition POW_CLOB_A : list (bv 5) := [10; 12; 13]%bv.
Definition POW_KEPT_A : list (bv 5) := [1; 2; 3; 4; 5; 6; 7; 8; 9; 11; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Lemma pow_clob_kept_A : forall r : bv 5, reg_in r POW_CLOB_A = false -> r = 0%bv \/ In r POW_KEPT_A.
Proof.
intros r Hr. pose proof (all_regs_in r) as Hin. cbv [all_regs In] in Hin.
repeat (destruct Hin as [<-|Hin]; [first [left; reflexivity | vm_compute in Hr; discriminate | right; cbv; tauto] |]).
destruct Hin.
Qed.
End f.
End d.
Definition boxed (P : Prop) : Prop := P.
Ltac box H := lazymatch type of H with ?T => change T with (boxed T) in H end.
Ltac unbox := unfold boxed in *.
Section g. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section o.
Context {PI : PAImg lib_asan3_0_listing}.
Context {RO : YC20.ro_below_ofl (@pa_segs _ lib_asan3_0_listing PI) (@pa_relro_lo _ lib_asan3_0_listing PI) (@pa_relro_hi _ lib_asan3_0_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ lib_asan3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_asan3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_asan3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_asan3_0_listing PI A_TEXT).
Ltac eimg_low := rewrite ?Eimg_low by (unfold A_TEXT; lia).
Definition ss_set_pc (s : sstate) (pc : Z) : sstate := mkSS pc (ss_regs s) (ss_mem s) (ss_resv s) (ss_facts s).
Fixpoint list_set {A} (l : list A) (i : nat) (x : A) : list A :=
match l, i with [], _ => [] | _ :: t, O => x :: t | h :: t, S j => h :: list_set t j x end.
Definition ss_set_reg (s : sstate) (r : nat) (e : sv) : sstate := mkSS (ss_pc s) (list_set (ss_regs s) r e) (ss_mem s) (ss_resv s) (ss_facts s).
Fixpoint ss_set_regs (s : sstate) (l : list (nat * sv)) : sstate :=
match l with [] => s | (r, e) :: t => ss_set_regs (ss_set_reg s r e) t end.
Fixpoint ss_havoc_regs (s : sstate) (N : nat) (deads : list nat) : sstate :=
match deads with [] => s | r :: t => ss_havoc_regs (ss_set_reg s r (SOff N 0)) (S N) t end.
Definition ss_set_mem (s : sstate) (m : smem) : sstate := mkSS (ss_pc s) (ss_regs s) m (ss_resv s) (ss_facts s).
Definition ss_set_facts (s : sstate) (fa : list (nat * afact)) : sstate :=
mkSS (ss_pc s) (ss_regs s) (ss_mem s) (ss_resv s) (mkFacts fa (f_conds (ss_facts s)) (f_alias (ss_facts s))).
End o.
End g.
Ltac evalE AG ::=
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
Ltac ra_join_val HS N i R En :=
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
lazymatch Ev with havoc _ _ ?vals =>
lazymatch type of R with _ = ?v =>
let n := eval vm_compute in (N + i)%nat in
assert (En : ew Ev n = v);
[ change n with (N + i)%nat; rewrite (ew_havoc_new _ N vals i (Z_to_bv 64 0)) by (cbn [length]; lia); cbn [nth]; exact R | ] end end | st_ok _ ?Ev _ _ =>
lazymatch Ev with havoc _ _ ?vals =>
lazymatch type of R with _ = ?v =>
let n := eval vm_compute in (N + i)%nat in
assert (En : ew Ev n = v);
[ change n with (N + i)%nat; rewrite (ew_havoc_new _ N vals i (Z_to_bv 64 0)) by (cbn [length]; lia); cbn [nth]; exact R | ] end end  end.
Ltac ra_join_fact HS n af tac :=
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
let HS3 := fresh "HS3" in
pose proof (st_ok_pi_add_fact Ev ssx msx n af HS ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; tac)) as HS3;
clear HS; rename HS3 into HS | st_ok _ ?Ev ?ssx ?msx =>
let HS3 := fresh "HS3" in
pose proof (st_ok_pi_add_fact Ev ssx msx n af HS ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; tac)) as HS3;
clear HS; rename HS3 into HS  end.
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
Section q. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section u.
Context {PI : PAImg lib_asan3_0_listing}.
Context {RO : YC20.ro_below_ofl (@pa_segs _ lib_asan3_0_listing PI) (@pa_relro_lo _ lib_asan3_0_listing PI) (@pa_relro_hi _ lib_asan3_0_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ lib_asan3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_asan3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_asan3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_asan3_0_listing PI A_TEXT).
Ltac eimg_low := rewrite ?Eimg_low by (unfold A_TEXT; lia).
Lemma denot_add_atoms : forall E n1 n2 a b, ew E n1 = Z_to_bv 64 a -> ew E n2 = Z_to_bv 64 b ->
0 <= a -> 0 <= b -> a + b < 2 ^ 64 -> sv_denot E (SAlu ALU_ADD (SOff n1 0) (SOff n2 0)) = Z_to_bv 64 (a + b).
Proof.
intros E n1 n2 a b H1 H2 Ha Hb Hab. rewrite denot_lit_U. f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E n1 a H1), (U_atom E n2 b H2) by lia. apply zcanon_id. rewrite M64_val. lia.
Qed.
Lemma regions_kept_out2 : forall E H (m m2 : word -> option byte) lo hi lo2 hi2 rs,
(forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> ~ (lo2 <= a < hi2) -> aview SEGS H m2 a = aview SEGS H m a) ->
(forall a, apresent H m a -> apresent H m2 a) ->
Forall (fun r => 0 <= base_val E (YP09.r_base r) + YP09.r_lo r /\ base_val E (YP09.r_base r) + YP09.r_hi r <= 2 ^ 64 /\
(base_val E (YP09.r_base r) + YP09.r_hi r <= lo \/ hi <= base_val E (YP09.r_base r) + YP09.r_lo r) /\
(base_val E (YP09.r_base r) + YP09.r_hi r <= lo2 \/ hi2 <= base_val E (YP09.r_base r) + YP09.r_lo r)) rs ->
Forall (region_kept SEGS E (mrestrict H m) (mrestrict H m2)) rs.
Proof.
intros E H m m2 lo hi lo2 hi2 rs Hav Hpr Hrs. apply Forall_forall. intros r Hr.
pose proof (proj1 (Forall_forall _ _) Hrs r Hr) as (H1 & H2 & H3 & H4). split; intros a Ha.
- apply (mbyte_of_aview SEGS). apply Hav; lia.
- apply writable_kept. apply Hpr.
Qed.
Lemma denot_mul_hw : forall E nh nw h w, ew E nh = Z_to_bv 64 h -> ew E nw = Z_to_bv 64 w ->
0 <= h < 2 ^ 32 -> 0 <= w < 2 ^ 32 -> sv_denot E (SMd M_MUL (SOff nh 0) (SOff nw 0)) = Z_to_bv 64 (h * w).
Proof.
intros E nh nw h w Hh Hw Rh Rw. assert (0 <= h * w) by (apply Z.mul_nonneg_nonneg; lia).
assert (h * w <= (2 ^ 32 - 1) * (2 ^ 32 - 1)) by (apply Z.mul_le_mono_nonneg; lia).
rewrite denot_lit_U. f_equal. rewrite U_SMd. cbn [zmd_raw]. rewrite (U_atom E nh h Hh) by lia. rewrite (U_atom E nw w Hw) by lia.
apply zcanon_id. rewrite M64_val. lia.
Qed.
End u.
End q.
Definition chunk_in (lo hi : Z) (c : YP09.chunk) : bool :=
Z.leb lo (YP09.c_off c) && Z.leb (YP09.c_off c + YP09.c_len c) hi.
Definition trim_region (r : YP09.region) (lo hi : Z) : YP09.region :=
YP09.mkRegion (YP09.r_base r) lo hi (Z.max (YP09.r_wlo r) lo) (Z.min (YP09.r_whi r) hi)
(filter (chunk_in lo hi) (YP09.r_chunks r)).
Fixpoint trim_stack (rs : smem) (lo hi : Z) : smem :=
match rs with
| [] => []
| r :: t => match YP09.r_base r with
| Some 2%nat => trim_region r lo hi :: t
| _ => r :: trim_stack t lo hi end end.
Lemma land_mod256 : forall x m, 0 <= m < 256 -> Z.land (x mod 256) m = Z.land x m.
Proof.
intros x m Hm. change 256 with (2 ^ 8). rewrite <- Z.land_ones by lia. rewrite <- Z.land_assoc. f_equal.
rewrite Z.land_comm, Z.land_ones by lia. apply Z.mod_small. change (2 ^ 8) with 256. lia.
Qed.
Lemma U_and_zext8 : forall E a m, 0 <= m < 256 -> U E (SAlu ALU_AND (SExt false 8 a) (SLit m)) = Z.land (U E a) m.
Proof.
intros E a m Hm. rewrite U_and_lit by lia. rewrite U_zext. change (2 ^ Z.of_N 8) with 256. apply land_mod256. exact Hm.
Qed.
