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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI09.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v ACef AF0l ACej ACeh ACem ACei ACep ACfm.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Definition A_readdata : Z := 0x80b84.
Definition RD_CPY : Z := 0x80c2c.
Definition A_asan_memcpy_tfb : Z := 0x515dc.
Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Definition RBx : sv := SOff 32 0.
Definition RBspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition rd_st_region (curv : sv) : YP09.region := YP09.mkRegion (Some 10%nat) 0 24 16 24
[YP09.mkChunk 0 (CVal 8 (SOff 33 0)); YP09.mkChunk 8 (CVal 8 (SOff 34 0)); YP09.mkChunk 16 (CVal 8 curv)].
Definition rd_alias : list (sv * sv) :=
[ (SAlu ALU_ADD (SOff 35 0) (SOff 33 0), SOff 36 0); (SAlu ALU_ADD (SOff 33 0) (SOff 35 0), SOff 36 0) ].
Definition rd_facts : list (nat * afact) :=
[ (2%nat, mkAF (2^46) (2^47) 4); (10%nat, mkAF (2^46) (2^47 - 24) 3); (12%nat, mkAF 0 (2^32) 0);
(32%nat, mkAF SB SB 0); (33%nat, mkAF 4096 0x7fffff800000 4); (34%nat, mkAF 0 (2^28) 0); (35%nat, mkAF 0 (2^28) 0);
(36%nat, mkAF 4096 0x7fffff800000 0) ].
Definition ss_rd : sstate :=
mkSS A_readdata sr_atoms [stack_region 32; got_region; bcell_region 32; rd_st_region (SOff 35 0)] None (mkFacts rd_facts [] rd_alias).
Definition ss_rd_c : sstate := Eval vm_compute in ss_rd.
Definition rd_extra (pdata nb cur : Z) : list word := map (Z_to_bv 64) [SB; pdata; nb; cur; pdata + cur].
Definition rd_src (B : asyms) (lyc : alayout) (Sc : astate) (pdata nb : Z) : Prop :=
(0 < nb /\ In (pdata, nb) (ablocks B lyc Sc)) \/ (nb = 0 /\ pdata = A_EMPTY).
End f.
Ltac enorm := cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia.
Ltac agnorm := try match goal with AGh : forall m : nat, (m < 33)%nat -> ew _ m = ew _ m |- _ => rewrite ?AGh by lia end.
Ltac oblRD RA E10x E32x :=
lazymatch goal with |- range_addressable _ (U ?Ex _) (U _ (SOff 10 ?c)) _ =>
rewrite (U_atom_off Ex 10 _ c ltac:(enorm; agnorm; exact E10x)) by lia;
eapply obl_of_range; [exact RA | rewrite (U_atom Ex 32 SB ltac:(enorm; agnorm; exact E32x)) by (unfold SB; lia); reflexivity | lia | lia] end.
Ltac awrRD Usp E10 :=
lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fp b0 bc ly own) end;
repeat first
[ apply awr_ok_nil
| apply awr_ok_cons_ro; [azlit_tac|]
| lazymatch goal with
| |- awr_ok ?E (YP09.mkRegion (Some 2%nat) _ _ _ _ _ :: _) _ ?sp0 _ _ _ _ _ =>
eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (bv_unsigned (ew E 2%nat) - sp0));
[ reflexivity | enorm; agnorm; lia
| cbn [YP09.r_wlo]; enorm; agnorm; rewrite Usp; lia
| cbn [YP09.r_whi]; enorm; agnorm; rewrite Usp; lia | ]
| |- awr_ok ?E (YP09.mkRegion (Some 10%nat) _ _ _ _ _ :: _) _ ?sp0 _ _ _ _ _ =>
eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 10%nat (bv_unsigned (ew E 10%nat) - sp0));
[ reflexivity | enorm; agnorm; lia
| cbn [YP09.r_wlo]; enorm; agnorm; rewrite E10, unsigned_lit_small by lia; lia
| cbn [YP09.r_whi]; enorm; agnorm; rewrite E10, unsigned_lit_small by lia; lia | ]
end ].
Section h. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Lemma RA_kept_band : forall (rd1 rd2 : Z -> option Z) x n,
(forall a, SB <= a < kHighShadowEnd -> rd2 a = rd1 a) -> 0 <= x -> x + n <= kHighMemEnd ->
range_addressable rd1 SHADOW_OFF x n -> range_addressable rd2 SHADOW_OFF x n.
Proof.
intros rd1 rd2 x n Heq Hx1 Hx2 HRA. eapply range_addressable_agree; [|exact HRA]. intros y Hy. apply Heq.
pose proof (shadow_addr_bounds y ltac:(lia)). pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). unfold SB, shadow_of_addr, shadow_addr in *. lia.
Qed.
Lemma hull_kept_band : forall (rd1 rd2 : Z -> option Z) x n,
(forall a, SB <= a < kHighShadowEnd -> rd2 a = rd1 a) -> 0 <= x -> 0 < n -> x + n <= kHighMemEnd ->
shadow_hull_vis rd1 x n -> shadow_hull_vis rd2 x n.
Proof.
intros rd1 rd2 x n Heq Hx1 Hn Hx2 H s Hs. rewrite Heq; [exact (H s Hs)|].
assert (B0 : 0 <= x < kHighMemEnd) by (clear - Hx1 Hn Hx2; lia). assert (B0' : 0 <= x + n - 1 < kHighMemEnd) by (clear - Hx1 Hn Hx2; lia).
pose proof (shadow_addr_bounds x B0) as B1. pose proof (shadow_addr_bounds _ B0') as B2. clear - Hs B1 B2.
set (u := shadow_addr x) in *. set (v := shadow_addr (x + n - 1)) in *.
pose proof (Z.div_mod u 8 ltac:(lia)). pose proof (Z.mod_pos_bound u 8 ltac:(lia)).
pose proof (Z.div_mod v 8 ltac:(lia)). pose proof (Z.mod_pos_bound v 8 ltac:(lia)).
unfold SB, kLowMemEnd, kHighShadowEnd in *. lia.
Qed.
End h.
Ltac unrunRD HFr Zs Usp B10 Hsp UN :=
pose proof (kept_of_frame _ _ _ _ _ Zs HFr
ltac:(let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let a := fresh "a" in
let Hi := fresh "Hi" in let Hr := fresh "Hr" in let Hq := fresh "Hq" in
intros b wlo whi a Hi Hr; vm_compute in Hi;
repeat (destruct Hi as [Hq | Hi]; [injection Hq as <- <- <-; cbn [base_val] in Hr; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub] in Hr; rewrite ?ew_ewset_other in Hr by lia; rewrite ?ew_havoc_old in Hr by lia;
try match goal with AGh : forall m : nat, (m < 33)%nat -> ew _ m = ew _ m |- _ => rewrite ?AGh in Hr by lia end;
rewrite ?Usp, ?B10 in Hr; repeat match goal with Hb : bv_unsigned (ew _ _) = _ |- _ => progress (rewrite Hb in Hr) end;
clear - Hr Hsp; try (cbv delta [Zs]; cbn beta); unfold TRFC_STK, TRAWNEW_STK, TNEWGIF_STK, ASTACK, ESTACK; lia |]); destruct Hi)) as UN.
Ltac evalER AG :=
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
Ltac prStep HG PR :=
first
[ lazymatch type of PR with forall a, apresent ?Hh ?m0 a -> apresent _ ?m1 a =>
lazymatch type of HG with mem_grows (mrestrict _ m1) (mrestrict _ ?m2) =>
let PR2 := fresh "PR" in
assert (PR2 : forall a, apresent Hh m0 a -> apresent Hh m2 a) by (intros a' Ha'; exact (apresent_grows _ _ _ _ HG (PR a' Ha')));
clear PR; rename PR2 into PR end end
| lazymatch type of HG with mem_grows (mrestrict ?Hh ?m1) (mrestrict _ ?m2) =>
assert (PR : forall a, apresent Hh m1 a -> apresent Hh m2 a) by (intros a' Ha'; exact (apresent_grows _ _ _ _ HG Ha')) end ];
clear HG.
Ltac keStep HF HFr HG KE PR Zs Usp B10 Hsp :=
let UN := fresh "UN" in
unrunRD HFr Zs Usp B10 Hsp UN; clear HF HFr; prStep HG PR;
first
[ lazymatch type of KE with forall a, _ -> _ -> aview _ _ ?m1 a = aview _ _ ?m0 a =>
lazymatch type of UN with forall a, _ -> _ -> aview ?sg ?Hh ?m2 a = aview _ _ m1 a =>
let KE2 := fresh "KE" in
assert (KE2 : forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> aview sg Hh m2 a = aview sg Hh m0 a)
by (intros a' Ha' Hn'; rewrite (UN a' Ha' Hn'); exact (KE a' Ha' Hn'));
clear KE UN; rename KE2 into KE end end
| rename UN into KE ].
Ltac shkOf KE ZB SHK :=
lazymatch type of KE with forall a, _ -> _ -> aview ?sg ?Hh ?m2 a = aview _ _ ?m0 a =>
assert (SHK : forall a, SB <= a < kHighShadowEnd -> aview sg Hh m2 a = aview sg Hh m0 a)
by (intros a' Ha'; apply KE; [clear - Ha'; unfold SB, kHighShadowEnd in Ha'; lia | exact (ZB a' Ha')]) end.
Lemma denot_add_atoms : forall E a b x y,
ew E a = Z_to_bv 64 x -> ew E b = Z_to_bv 64 y -> 0 <= x -> 0 <= y -> x + y < 2 ^ 64 ->
sv_denot E (SAlu ALU_ADD (SOff a 0) (SOff b 0)) = Z_to_bv 64 (x + y).
Proof.
intros E a b x y Ha Hb Hx Hy Hxy. rewrite denot_lit_U. f_equal. rewrite U_SAlu. cbn [zalu_raw].
rewrite (U_atom E a x Ha), (U_atom E b y Hb) by lia. apply zcanon_id. unfold M64. lia.
Qed.
Ltac cregRD HS HAE :=
lazymatch goal with |- getr _ ?r = getr ?regsT _ =>
let R := fresh "R" in rreg HS r R; rewrite R; clear R; enorm; agnorm;
lazymatch goal with |- ew _ ?n = _ => rewrite (proj1 HAE n) by lia; exact (ew_Ereg_nat regsT _ n r eq_refl) end end.
Ltac fieldRD HS i B10 od v dtac Vname :=
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
let r := eval vm_compute in (nth i (ss_mem ssx) got_region) in
let HRr := fresh "HRr" in
pose proof (st_ok_region_nth Ex ssx (restrict _ msX) i r HS ltac:(vm_compute; reflexivity)) as HRr; cbn [ms_mem restrict] in HRr;
lazymatch type of HRr with region_ok _ _ _ (YP09.mkRegion (Some 10%nat) ?lo ?hi ?wlo ?whi ?cs) =>
lazymatch eval cbv in (find (fun c => Z.eqb (YP09.c_off c) od) cs) with Some (YP09.mkChunk _ (CVal 8 ?e)) =>
pose proof (field_of_region Ex _ 10%nat _ cs lo hi wlo whi od 8 e v HRr ltac:(enorm; agnorm; exact B10) ltac:(cbn; tauto) ltac:(dtac) ltac:(cbn; lia) ltac:(cbn; lia)) as Vname end end;
clear HRr; rewrite ?Z.add_0_r in Vname end.
Section p. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section RD.
Variable B : asyms.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Let HBgot := tl_got_shadow B TL. Let HBcell := tl_shadow_cell B TL.
Lemma rd_entry : forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k (st d n pdata nb cur o : Z),
ajournal tfibsegs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
getr regsT 10 = w64 st -> getr regsT 11 = w64 d -> getr regsT 12 = w64 n ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 32 + ESTACK - o <= STK ->
st mod 8 = 0 -> sp0 + o <= st -> st + 24 <= sp0 ->
val_mem tfibsegs (mrestrict (w_H W) memT) st 8 pdata -> val_mem tfibsegs (mrestrict (w_H W) memT) (st + 8) 8 nb ->
val_mem tfibsegs (mrestrict (w_H W) memT) (st + 16) 8 cur ->
rd_src B lyc Sc pdata nb -> 0 <= cur <= nb -> 0 <= n < 2 ^ 32 ->
st_ok tfibsegs (Ereg regsT (rd_extra pdata nb cur)) ss_rd_c (restrict (w_H W) (mkst regsT (Z_to_bv 64 A_readdata) memT (seg_rom tfibsegs))).
Proof.
intros W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k st d n pdata nb cur o
HJ G10 G11 G12 Hsp' Hal Hneg Hbud Hst8 Hst1 Hst2 Wp Wn Wc HB Hcur Hn.
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & Hpres & (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _) & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). assert (ESTACK = 4096) as Hes by reflexivity.
assert (HPF : pdata mod 16 = 0 /\ 4096 <= pdata /\ pdata + req_size nb <= alloc_ceiling /\ 0 <= nb < 2 ^ 28).
{ destruct HB as [[Hnb Hpd] | [Hnb0 HpE]].
- destruct (al_blocks _ _ LAWS _ _ _ _ _ pdata nb HAR Hpd) as (Hp16 & Hp4096 & Hpceil & _ & _ & _ & HnbM). unfold MALLOC_MAX in HnbM. repeat split; lia.
- rewrite HpE, Hnb0. unfold A_EMPTY. change (req_size 0) with 1. clear - C1. repeat split; lia. }
destruct HPF as (Hp16 & Hp4096 & Hpceil & HnbM). pose proof Hp4096 as Hph.
pose proof (req_size_pos nb ltac:(lia)) as [Hrq1 Hrq2].
destruct (al_const _ _ LAWS _ _ _ _ _ HAR) as (Kcell & _ & Kgot & _). rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
rewrite restrict_mkst_fx. change ss_rd_c with ss_rd.
set (E := Ereg regsT (rd_extra pdata nb cur)).
assert (E2 : ew E 2 = getr regsT 2) by (subst E; exact (ew_Ereg_nat regsT _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 st) by (subst E; rewrite (ew_Ereg_nat regsT _ 10 10%bv eq_refl); exact G10).
assert (E12 : ew E 12 = Z_to_bv 64 n) by (subst E; rewrite (ew_Ereg_nat regsT _ 12 12%bv eq_refl); exact G12).
assert (EX : forall j, ew E (32 + j) = nth j (rd_extra pdata nb cur) (Z_to_bv 64 0)) by (intros j; subst E; apply ew_Ereg_extra).
pose proof (EX 0%nat) as E32. pose proof (EX 1%nat) as E33. pose proof (EX 2%nat) as E34. pose proof (EX 3%nat) as E35. pose proof (EX 4%nat) as E36.
cbn [Nat.add nth rd_extra map] in E32, E33, E34, E35, E36. clear EX.
assert (Usp : bv_unsigned (ew E 2) = spZ regsT) by (rewrite E2; reflexivity).
assert (VB : forall m v, ew E m = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some m) = v).
{ intros m v Hm Hv. cbn [base_val]. rewrite Hm. apply unsigned_lit_small. exact Hv. }
unfold ss_rd. apply (entry_st_ok_full tfibsegs); change (Ereg regsT (rd_extra pdata nb cur)) with E.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- unfold stack_region, got_region, bcell_region, rd_st_region.
repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
+ cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
intros q Hq. apply (apresent_writable tfibsegs). apply Hpres. lia.
+ cbn [base_val]. unfold A_GOT_shadow. split; [lia|]. split; [lia|]. split; [intros q Hq; lia|].
constructor; [|constructor]. rewrite <- (Z.add_0_l 0x9df98) at 1.
apply (chunk_ok_val tfibsegs E _ 0 0x9df98 8 (SLit A_shadow_glob) A_shadow_glob); [reflexivity | unfold A_shadow_glob; zside | zside |].
exact (val_mem_of_rdword tfibsegs (w_H W) memT _ _ Kgot).
+ cbn [base_val]. unfold A_shadow_glob. split; [lia|]. split; [lia|]. split; [intros q Hq; lia|].
constructor; [|constructor]. rewrite <- (Z.add_0_l 0xa5ff8) at 1.
apply (chunk_ok_val tfibsegs E _ 0 0xa5ff8 8 (SOff 32 0) SB);
[cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
exact (val_mem_of_rdword tfibsegs (w_H W) memT _ _ Kcell).
+   rewrite (VB 10%nat st E10) by lia. split; [lia|]. split; [lia|]. split.
{ intros q Hq. apply (apresent_writable tfibsegs). apply Hpres. lia. }
constructor; [|constructor; [|constructor; [|constructor]]].
* apply (chunk_ok_val tfibsegs E _ st 0 8 _ pdata); [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | rewrite Z.add_0_r; exact Wp].
* apply (chunk_ok_val tfibsegs E _ st 8 8 _ nb); [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Wn].
* apply (chunk_ok_val tfibsegs E _ st 16 8 _ cur); [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Wc].
- apply pairwise_disjoint_of_extents. unfold stack_region, got_region, bcell_region, rd_st_region, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite (VB 10%nat st E10) by lia. cbn [base_val]. rewrite Usp.
unfold A_GOT_shadow, A_shadow_glob.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
revert Hslo Hshi H47 Hceil Hsp' Hneg Hbud C1 C3 Hes Hstk0 Hst1 Hst2. clear. ceil; unfold ASAN_CEIL. intros. repeat split; lia.
- split; [|split; [exact I |]].
+ cbn [f_atoms rd_facts atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite Usp, E10, E12, E32, E33, E34, E35, E36, !unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
assert (Hspal : spZ regsT mod 16 = 0) by (rewrite Hsp', Z.add_mod, Hsp0al, Hal by lia; reflexivity).
revert Hslo Hshi H47 Hceil Hsp' Hspal Hneg Hbud Hst1 Hst2 Hst8 Hn Hcur Hp16 Hp4096 Hpceil Hph HnbM Hrq1 Hrq2 C1 C3 Hes Hstk0. clear.
ceil; unfold SB, ASAN_CEIL, kLowShadowBeg, kHighMemBeg. intros. repeat match goal with |- _ /\ _ => split end; try lia.
all: match goal with |- ?g => idtac "ENTRYFACT" g end; fail.
+
cbn [f_alias alias_ok rd_alias].
assert (AL1 : sv_denot E (SAlu ALU_ADD (SOff 35 0) (SOff 33 0)) = sv_denot E (SOff 36 0)).
{ apply U_inj. rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E 33 pdata E33), (U_atom E 35 cur E35), (U_atom E 36 (pdata + cur) E36) by lia.
rewrite zcanon_id by (unfold M64; lia). lia. }
assert (AL2 : sv_denot E (SAlu ALU_ADD (SOff 33 0) (SOff 35 0)) = sv_denot E (SOff 36 0)).
{ apply U_inj. rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E 33 pdata E33), (U_atom E 35 cur E35), (U_atom E 36 (pdata + cur) E36) by lia.
rewrite zcanon_id by (unfold M64; lia). lia. }
repeat split; first [exact AL1 | exact AL2].
Qed.
Lemma same_io_wvb : forall (a md : Model) l mat, same_io a md -> same_io a (with_vm_backing l mat md).
Proof. intros a md l mat (E1 & E2 & E3 & E4). unfold same_io, with_vm_backing in *. destruct md; cbn in *. repeat split; assumption. Qed.
Lemma ajournal_closed_same_io : forall STK sp0 FP ly S (W : world tfibsegs) mem md own ly' S' W' mem' md' k,
~ YI16.sink_open_fp FP ->
ajournal tfibsegs B STK sp0 FP ly S W mem md own ly' S' W' mem' md' k -> same_io md md'.
Proof. intros until 0. intros Hcl HJ. pose proof HJ as (_ & _ & _ & _ & Hos & _). exact (aos_step_closed_same_io FP md md' Hcl Hos). Qed.
Lemma aj_intrin_at_io : forall op pc, aintrin_realizes tfibsegs B op pc ->
forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k d x n (o : Z) raw,
ajournal tfibsegs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
getr regsT 10 = w64 d -> getr regsT 11 = w64 x -> getr regsT 12 = w64 n -> 0 <= n < 2 ^ 32 -> 0 <= d -> d + n <= 2 ^ 63 ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
(forall a, d <= a < d + n -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a /\ ~ (sp0 + o - ESTACK <= a < sp0 + o)) ->
amem_range d n ->
range_addressable (aview tfibsegs (w_H W) memT) SHADOW_OFF d n ->
(0 < n -> shadow_hull_vis (aview tfibsegs (w_H W) memT) d n) ->
(match op with
| OCpy => 0 <= x /\ x + n <= 2 ^ 63 /\ src_ok tfibsegs W regsT memT x n /\ (d + n <= x \/ x + n <= d) /\ amem_range x n /\
range_addressable (aview tfibsegs (w_H W) memT) SHADOW_OFF x n /\ (0 < n -> shadow_hull_vis (aview tfibsegs (w_H W) memT) x n)
| OSet => True end) ->
SRr tfibsegs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom tfibsegs)) mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom tfibsegs)) md2 /\
ajournal tfibsegs B STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\
aregs_preserved regsT regs2 /\ getr regs2 10 = w64 d /\
(forall i, 0 <= i < n -> aview tfibsegs (w_H W) mem2 (d + i) =
match op with OCpy => aview tfibsegs (w_H W) memT (x + i) | OSet => Some (x mod 256) end) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + n) -> ~ (sp0 + o - ESTACK <= a < sp0 + o) -> aview tfibsegs (w_H W) mem2 a = aview tfibsegs (w_H W) memT a) /\
(forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a) /\
same_io mdc md2).
Proof.
intros op pc AI W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k d x n o raw
HJ Ha0 Ha1 Ha2 Hn Hd0 Hdn Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw Hdest Hamr Hra_d Hhull Hsrc.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & _ & _ & _ & _ & _ & Hpres & Hstatic & F5 & HQT).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
assert (ESTACK = 4096) as Hes by reflexivity. assert (ASTACK = 16384) as Has by reflexivity.
assert (HPRE : ecall_pre tfibsegs B lyc Sc W regsT memT mdc).
{ eapply (ecall_pre_at tfibsegs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k regsT o); try eassumption. rewrite Hra. exact Hraw. }
assert (HDEST : dest_ok tfibsegs B lyc Sc W regsT memT d n).
{ intros a Ha. destruct (Hdest a Ha) as [Hw Hns].
destruct (awr_byte_present tfibsegs B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ Hw) as [Hp Hno]. rewrite Hsp'.
split; [apply apresent_writable; exact Hp | auto]. }
eapply SRr_mono.
{ exact (AI lyc Sc W regsT memT mdc d x n HPRE Ha0 Ha1 Ha2 Hn Hd0 Hdn HDEST Hamr Hra_d Hhull Hsrc). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsame & Hres & Heff & Hfr & Hpres2).
rewrite Hsp' in Hfr.
split; [reflexivity|]. exists regs2, mem2, md2.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ eapply (ajournal_after_write tfibsegs B LAWS tfib_segs_low STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k mem2 md2
(fun a => (d <= a < d + n) \/ (sp0 + o - ESTACK <= a < sp0 + o)) Sc own HJ).
- intros a Ha Hna. apply (Hfr a Ha); intros H'; apply Hna; [left | right]; exact H'.
- exact Hpres2.
- exact Hsame.
- intros a [Ha | Ha]; left; [exact (proj1 (Hdest a Ha)) | left; lia].
- exact HAR2.
- reflexivity. - reflexivity. - lia. - exact Hfrs. - exact HQT. }
split; [exact HP|]. split; [exact Hres|]. split; [exact Heff|]. split; [exact Hfr|]. split; [exact Hpres2|].
exact (same_io_materialized mdc md2 Hsame).
Qed.
End RD.
End p.
