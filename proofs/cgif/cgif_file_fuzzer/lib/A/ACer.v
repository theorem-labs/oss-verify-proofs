(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI09 YI08 YI0n YI0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v ACef AF0l ACej ACeh ACem ACei ACep.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Definition chunk_in (lo hi : Z) (c : YP09.chunk) : bool :=
Z.leb lo (YP09.c_off c) && Z.leb (YP09.c_off c + YP09.c_len c) hi.
Ltac rnLAWS := lazymatch goal with L : AR_laws tfibsegs _ |- _ => L end.
Ltac rnTL := lazymatch goal with T : TfibLib _ |- _ => T end.
Ltac nat_side := first [ apply (proj1 (PeanoNat.Nat.ltb_lt _ _)); vm_compute; reflexivity
| apply (proj1 (PeanoNat.Nat.eqb_neq _ _)); vm_compute; reflexivity ].
Ltac evalE AG :=
cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia;
repeat match goal with H : ew ?Ex ?n = Z_to_bv 64 _ |- context [ew ?Ex ?n] => rewrite H end;
lazymatch type of AG with forall n, _ -> ew ?Ev n = _ =>
repeat match goal with |- context [ew Ev ?n] => lazymatch (eval cbv in (Nat.ltb n 33)) with true => rewrite (AG n) by lia end end end;
repeat match goal with H : ew ?Ex ?n = Z_to_bv 64 _ |- context [ew ?Ex ?n] => rewrite H end;
repeat match goal with H : bv_unsigned (ew ?Ex 2) = _ |- context [bv_unsigned (ew ?Ex 2)] => rewrite H end;
rewrite ?unsigned_lit_small by (unfold SB; lia); unfold SB;
first [ reflexivity
| lazymatch goal with |- _ = _ => lia | |- _ <= _ => lia | |- _ < _ => lia | |- _ <= _ < _ => lia | |- _ <= _ <= _ => lia | |- _ < _ <= _ => lia
| |- _ <> _ => lia | |- _ > _ => lia | |- _ >= _ => lia | |- ~ _ => lia | |- False => lia end
| idtac ].
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
Ltac idx_of_base rs n :=
lazymatch rs with
| YP09.mkRegion (Some n) _ _ _ _ _ :: _ => constr:(0%nat)
| _ :: ?tl => let i := idx_of_base tl n in constr:(S i)
end.
Ltac incl_lit_tac :=
let x := fresh "x" in let Hx := fresh "Hx" in
intros x Hx; cbn in Hx; cbn;
repeat (destruct Hx as [<- | Hx]; [repeat (first [left; reflexivity | right]) |]); destruct Hx.
Ltac set_regs_rec HS N vals i rl :=
lazymatch rl with
| [] => idtac
| ?r :: ?rl' =>
lazymatch type of HS with st_ok _ ?Ev ?ssx ?msx =>
let HS3 := fresh "HS3" in let Hv := fresh "Hv" in
let n := eval vm_compute in (N + i)%nat in
assert (Hv : sv_denot Ev (SOff n 0) = getr (ms_regs msx) r);
[ cbn [sv_denot]; rewrite Z.add_0_r; rewrite Z_to_bv_bv_unsigned; change n with (N + i)%nat;
rewrite (ew_havoc_new _ N vals i (Z_to_bv 64 0)) by (cbn [length]; lia); cbn [nth ms_regs restrict]; reflexivity | ];
pose proof (ast_ok_set_reg_fp tfibsegs Ev ssx msx r (SOff n 0) HS ltac:(vm_compute; reflexivity) Hv) as HS3;
clear HS Hv; rename HS3 into HS; norm_ss HS; set_regs_rec HS N vals (S i) rl' end
end.
Ltac creg HS AG EE :=
lazymatch goal with |- getr _ ?r = getr _ _ =>
let R := fresh "R" in rreg HS r R; rewrite R; clear R;
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
lazymatch type of HSr with st_ok _ ?Ex ?ssx _ =>
pose proof (st_ok_region_nth Ex ssx msr 0 _ HSr eq_refl) as HR;
lazymatch type of HR with region_ok _ _ _ (YP09.mkRegion (Some ?n) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex (ms_mem msr) n _ cs lo hi wlo whi 0 1%N (SLit 0) 0 HR
ltac:(cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E57; apply unsigned_lit_small; lia)
ltac:(left; reflexivity) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as V end end;
rewrite Z.add_0_r in V; pose proof (V 0%nat ltac:(lia)) as V0; cbn [Z.of_nat] in V0; rewrite Z.add_0_r in V0; exact V0.
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
lazymatch type of HS with st_ok ?segs ?Ex ?ss (restrict ?Hh ?ms) =>
let e := eval vm_compute in (sr_get (ss_regs ss) r) in
let rg := eval cbn [ms_regs restrict mkst] in (ms_regs ms) in
assert (H : getr rg r = v) by (refine (eq_trans (st_ok_restrict_reg segs Hh Ex ss ms r HS) _); change (sv_denot Ex e = v); exact pf) end.
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
Lemma sp1_facts : forall x, 0 <= x -> x mod 16 = 0 -> x - 16 <= 32 * (x / 32) <= x /\ (32 * (x / 32)) mod 32 = 0 /\ (32 * (x / 32)) mod 16 = 0.
Proof.
intros x Hx H16. pose proof (Z.div_mod x 32 ltac:(lia)) as D. pose proof (Z.mod_pos_bound x 32 ltac:(lia)) as M.
pose proof (Z.div_mod x 16 ltac:(lia)) as D16.
assert (x mod 32 = 0 \/ x mod 32 = 16) by lia.
split; [lia|]. split; [rewrite Z.mul_comm; apply Z_mod_mult|].
replace (32 * (x / 32)) with ((2 * (x / 32)) * 16) by lia. apply Z_mod_mult.
Qed.
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
Lemma sv_denot_SOff0 : forall E n, sv_denot E (SOff n 0) = ew E n.
Proof. intros E n. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. Qed.
Ltac aconstsF HJx Kgot Kcell Kguar Kuar :=
let L := rnLAWS in let TL := rnTL in
let Kc := fresh "Kc" in let Ku := fresh "Ku" in let Kg := fresh "Kg" in let Kgu := fresh "Kgu" in
destruct (al_const _ _ L _ _ _ _ _ (proj1 HJx)) as (Kc & Ku & Kg & Kgu);
rewrite (tl_got_shadow _ TL), (tl_shadow_cell _ TL) in Kg; rewrite (tl_shadow_cell _ TL) in Kc;
rewrite (tl_got_uar _ TL), (tl_uar_cell _ TL) in Kgu; rewrite (tl_uar_cell _ TL) in Ku;
pose proof (val_mem_of_rdword tfibsegs _ _ _ _ Kg) as Kgot; pose proof (val_mem_of_rdword tfibsegs _ _ _ _ Kc) as Kcell;
pose proof (val_mem_of_rdword tfibsegs _ _ _ _ Kgu) as Kguar; pose proof (val_mem_of_rd32 tfibsegs _ _ _ _ Ku) as Kuar;
clear Kc Ku Kg Kgu.
Ltac fs_roF HS :=
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs 88%nat in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rs got_region) in
let HS3 := fresh "HS3" in
pose proof (ast_ok_set_region tfibsegs Ex ssx msx i r (set_window r 0 0) HS ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity)
(region_ok_rewindow tfibsegs Ex _ r 0 0 (st_ok_region_nth Ex ssx msx i r HS ltac:(vm_compute; reflexivity)) ltac:(intros o Ho; lia))) as HS3;
clear HS; rename HS3 into HS; norm_ss HS end.
Ltac fs_rwF HS E88 Hp :=
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs 88%nat in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rs got_region) in
let HS3 := fresh "HS3" in
pose proof (ast_ok_set_region tfibsegs Ex ssx msx i r (set_window r 0 32) HS ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity)
(region_ok_rewindow tfibsegs Ex _ r 0 32 (st_ok_region_nth Ex ssx msx i r HS ltac:(vm_compute; reflexivity))
ltac:(cbn [YP09.r_base base_val ms_mem restrict mkst]; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia;
rewrite E88, unsigned_lit_small by (unfold SB; lia);
intros o Ho; apply (apresent_writable tfibsegs); unfold shadow_addr in Hp; rewrite <- SB_SHADOW_OFF in Hp;
apply (proj1 (Hp o ltac:(clear - Ho; lia)))))) as HS3;
clear HS; rename HS3 into HS; norm_ss HS end.
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
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (ss_mem ssx) in
let r := eval vm_compute in (nth i rs got_region) in
lazymatch (eval vm_compute in (nth_error (YP09.r_chunks r) j)) with Some (YP09.mkChunk ?off (CVal ?w ?e)) =>
let r' := eval vm_compute in (YP09.mkRegion (YP09.r_base r) (YP09.r_lo r) (YP09.r_hi r) (YP09.r_wlo r) (YP09.r_whi r)
(list_upd (YP09.r_chunks r) j (YP09.mkChunk off (CVal w e')))) in
let HS3 := fresh "HS3" in
pose proof (ast_ok_set_region tfibsegs Ex ssx msx i r r' HS ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity)
(region_ok_rechunk tfibsegs Ex _ r j off w e e' (st_ok_region_nth Ex ssx msx i r HS ltac:(vm_compute; reflexivity)) ltac:(vm_compute; reflexivity) ltac:(tac))) as HS3;
clear HS; rename HS3 into HS; norm_ss HS end end.
Ltac rqs_goal := repeat (match goal with |- context [req_size ?n] =>
let v := eval vm_compute in (req_size n) in
lazymatch v with Zpos _ => change (req_size n) with v | Z0 => change (req_size n) with v end end).
Ltac rewrite_frame_addr := repeat match goal with H : forall c p, frame_addr ?l3 c p = frame_addr ?l c p |- context [frame_addr ?l3 _ _] => rewrite H end;
repeat match goal with F := frame_addr _ _ _ |- _ => fold F end.
Ltac upd_aboveW_init HFr AG HUP :=
lazymatch type of HFr with frame_of ?Ef ?rs (mrestrict (w_H ?Wx) ?m0) (mrestrict _ (ms_mem ?msX)) =>
lazymatch goal with Usp : bv_unsigned (ew _ 2) = spZ ?regs |- _ =>
assert (HUP : forall a, spZ regs <= a < 2 ^ 64 -> aview tfibsegs (w_H Wx) (ms_mem msX) a = aview tfibsegs (w_H Wx) m0 a);
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
Ltac reshok HS := reshok_bx HS 32%nat.
Section d.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Lemma st_ok_pin_rege : forall E ss ms (r : bv 5) e,
st_ok tfibsegs E ss ms -> r <> 0%bv -> sv_denot E e = getr (ms_regs ms) r ->
st_ok tfibsegs E (mkSS (ss_pc ss) (sr_set (ss_regs ss) r e) (ss_mem ss) (ss_resv ss) (ss_facts ss)) ms.
Proof.
intros E ss ms r e HS Hr He.
apply (st_ok_regs tfibsegs E ss ms (sr_set (ss_regs ss) r e)); [exact HS|].
intros x. destruct (base.decide (x = r)) as [->|Hne].
- rewrite sr_get_set_same; [| destruct (bv_eqb r 0) eqn:Hb; [apply bv_eqb_eq in Hb; congruence | reflexivity]].
rewrite He. exact (st_ok_reg tfibsegs E ss ms r HS).
- rewrite sr_get_set_other by exact Hne. reflexivity.
Qed.
Section f.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Lemma sep_tmp_entry : forall ly3 S3 W3 m3 md3 (entry : list (Z * Z)) pt n b m,
AR tfibsegs B ly3 S3 W3 m3 md3 -> Permutation (ablocks B ly3 S3) (entry ++ [(pt, n)]) -> In (b, m) entry ->
b + req_size m <= pt \/ pt + req_size n <= b.
Proof.
intros ly3 S3 W3 m3 md3 entry pt n b m HAR HP Hin.
apply in_split in Hin as (l1 & l2 & El). rewrite El in HP.
assert (HP2 : Permutation (ablocks B ly3 S3) ((pt, n) :: (b, m) :: l1 ++ l2)).
{ eapply Permutation_trans; [exact HP|]. eapply Permutation_trans; [apply Permutation_app_comm|]. cbn [app]. apply perm_skip.
apply Permutation_sym. apply Permutation_middle. }
pose proof (sep_blocks_perm tfibsegs B LAWS _ _ _ _ _ _ _ _ HAR HP2) as Hs. unfold zdisjoint, block_rng in Hs. cbn [fst snd] in Hs. lia.
Qed.
End f.
End d.
