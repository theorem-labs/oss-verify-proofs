(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI08.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0d YP0c YI0w YI0y YC4a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC80 YC1f YC1g YC81 YC4b YC4b.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC20.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Definition A_LZW : Z := AF_asan3_LZW_GenerateStream.
Definition lzw_traces (code : acode) (base : Z) : list (list Z) :=
map (fun k => [pc_malloc_ra0 code; base + k]) [0x14d0; 0x1510; 0x152c; 0x154c; 0x15a0; 0x1630; 0x208c; 0x2098]
++ map (fun k => [pc_free_ra0 code; base + k]) [0x20e8; 0x212c; 0x2134; 0x2150; 0x2160; 0x2178; 0x2190; 0x21a8; 0x21c0; 0x21c8].
Ltac getHUL := lazymatch goal with H : forall t, In t (lzw_traces _ _) -> _ |- _ => H end.
Ltac pHUL := let H := getHUL in exact H.
Ltac hul_tac := let H := getHUL in apply H; unfold lzw_traces; cbn [map app In]; repeat (first [left; reflexivity | right]).
Section e. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg lib_asan3_1_listing}.
Context {RO : YC20.ro_below_ofl (@pa_segs _ lib_asan3_1_listing PI) (@pa_relro_lo _ lib_asan3_1_listing PI) (@pa_relro_hi _ lib_asan3_1_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ lib_asan3_1_listing PI).
#[local] Notation VAL := (@pa_val _ lib_asan3_1_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_asan3_1_listing PI).
#[local] Notation BASE := (@pa_val _ lib_asan3_1_listing PI A_TEXT).
Ltac eimg_low := rewrite ?Eimg_low by (unfold A_TEXT; lia).
Definition PC_CLEAN : Z := 0x2138.
Definition PC_LEAVE : Z := 0x21c8.
Definition tnz (l : list (Z * Z)) : list (Z * Z) := List.filter (fun b => negb (fst b =? 0)) l.
Lemma tnz_cons0 : forall n l, tnz ((0, n) :: l) = tnz l.
Proof. intros n l. reflexivity. Qed.
Lemma tnz_cons_nz : forall p n l, p <> 0 -> tnz ((p, n) :: l) = (p, n) :: tnz l.
Proof. intros p n l Hp. unfold tnz. cbn. destruct (Z.eqb_spec p 0); [lia | reflexivity]. Qed.
Lemma In_tnz : forall b l, In b (tnz l) -> In b l.
Proof. intros b l H. unfold tnz in H. apply filter_In in H. tauto. Qed.
Definition TSAVED : list (Z * bv 5) :=
[(8, 1%bv); (16, 8%bv); (24, 9%bv); (32, 18%bv); (40, 19%bv); (48, 20%bv); (56, 21%bv); (64, 22%bv); (72, 23%bv);
(80, 24%bv); (88, 25%bv); (96, 26%bv); (104, 27%bv)].
Definition tlzw_frame (m : word -> option byte) (spe : Z) (regs0 : bvmap 5 word) : Prop :=
Forall (fun p => val_mem SEGS m (spe - fst p) 8 (bv_unsigned (getr regs0 (snd p)))) TSAVED.
Definition tsaved_vals (regs0 : bvmap 5 word) : list word := map (fun p => getr regs0 (snd p)) TSAVED.
Definition tsaved_chunks (k : nat) : list YP09.chunk :=
map (fun jp => YP09.mkChunk (320 - fst (snd jp)) (CVal 8 (SOff (k + fst jp)%nat 0)))
(combine (seq 0 13) TSAVED).
Lemma tlzw_frame_agree : forall m m' spe regs0,
tlzw_frame m spe regs0 -> (forall a, spe - 104 <= a < spe -> mbyte SEGS m' a = mbyte SEGS m a) -> tlzw_frame m' spe regs0.
Proof.
intros m m' spe regs0 H Heq. unfold tlzw_frame in *. rewrite Forall_forall in H |- *. intros [o r] Hin.
specialize (H _ Hin). cbn [fst snd] in *.
assert (Ho : 8 <= o <= 104).
{ cbv [TSAVED In] in Hin. repeat (destruct Hin as [Hin|Hin]; [apply pair_equal_spec in Hin as [<- _]; lia|]). destruct Hin. }
intros j Hj. rewrite (Heq (spe - o + Z.of_nat j)) by lia. exact (H j Hj).
Qed.
Lemma aregs_preserved_of_eqs : forall regs0 regs2 : bvmap 5 word,
getr regs2 2 = getr regs0 2 -> getr regs2 3 = getr regs0 3 -> getr regs2 4 = getr regs0 4 ->
getr regs2 8 = getr regs0 8 -> getr regs2 9 = getr regs0 9 ->
getr regs2 18 = getr regs0 18 -> getr regs2 19 = getr regs0 19 -> getr regs2 20 = getr regs0 20 ->
getr regs2 21 = getr regs0 21 -> getr regs2 22 = getr regs0 22 -> getr regs2 23 = getr regs0 23 ->
getr regs2 24 = getr regs0 24 -> getr regs2 25 = getr regs0 25 -> getr regs2 26 = getr regs0 26 ->
getr regs2 27 = getr regs0 27 -> aregs_preserved regs0 regs2.
Proof.
intros regs0 regs2 H2 H3 H4 H8 H9 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 r Hr.
assert (Hr0 : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by (unfold acallee_saved in Hr; lia).
clear Hr. repeat (destruct Hr0 as [-> | Hr0]; [assumption|]). subst r. assumption.
Qed.
Lemma getr_Z5 : forall (regs : bvmap 5 word) (r : bv 5), getr regs (Z_to_bv 5 (bv_unsigned r)) = getr regs r.
Proof. intros regs r. rewrite Z_to_bv_bv_unsigned. reflexivity. Qed.
Ltac apreserved HP r X :=
pose proof (HP (bv_unsigned r) ltac:(unfold acallee_saved; rewrite !bv_unsigned_BV; lia)) as X; rewrite !getr_Z5 in X.
Section h.
Variable B : asyms.
Hypothesis TL : PALib B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis AFREE : afree_realizes SEGS B.
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL. Let errno_low := pal_env B TL. Let HBfree := pal_free B TL. Let HBmalloc := pal_malloc B TL.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_asan3_1) (PI := PI).
Hypothesis HUL : forall t, In t (lzw_traces (as_code B) BASE) -> In t (as_universe B).
Let PBASE := @pa_B_ok _ _ PI. Let PBLO := @pa_base_lo _ _ PL_asan3_1 PI.
Definition ss_leave : sstate :=
mkSS PC_LEAVE sr_atoms [ YP09.mkRegion (Some 2%nat) 0 320 0 0 (tsaved_chunks 32) ] None
(mkFacts [ (2%nat, mkAF (2^46) (2^47) 4) ] [] []).
Definition ss_leave_c : sstate := Eval vm_compute in ss_leave.
Lemma tsaved_chunks_ok : forall E (m : word -> option byte) spe regs0 k,
(forall j, (j < 13)%nat -> ew E (k + j)%nat = nth j (tsaved_vals regs0) (Z_to_bv 64 0)) ->
tlzw_frame m spe regs0 ->
Forall (YP09.chunk_ok SEGS E m (spe - 320)) (tsaved_chunks k).
Proof.
intros E m spe regs0 k HE HF. unfold tlzw_frame in HF. unfold tsaved_chunks.
cbn [combine seq TSAVED map fst snd].
repeat (apply Forall_cons; [
lazymatch goal with |- YP09.chunk_ok _ _ _ _ (YP09.mkChunk ?o (CVal 8 (SOff (_ + ?j)%nat 0))) =>
eapply (chunk_ok_val SEGS E m (spe - 320) o 8 _ (bv_unsigned (nth j (tsaved_vals regs0) (Z_to_bv 64 0))))
end |]).
all: try apply Forall_nil.
all: lazymatch goal with
| HE' : forall j, _ -> ew ?E' _ = _ |- sv_denot _ (SOff (_ + ?j)%nat 0) = _ =>
cbn [sv_denot]; rewrite (HE' j) by lia; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
| |- 0 <= bv_unsigned ?v < _ => pose proof (bv_unsigned_in_range 64 v) as Hr; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Hr; exact Hr
| |- (Z.of_N 8 <= 8) => cbn; lia
| HF' : Forall _ TSAVED |- val_mem _ _ (?sp' - 320 + (320 - ?o)) _ _ =>
change (N.to_nat 8) with 8%nat; unfold tsaved_vals; cbn [nth map snd TSAVED];
replace (sp' - 320 + (320 - o)) with (sp' - o) by lia;
refine (proj1 (Forall_forall _ _) HF' (o, _) _); cbv; tauto
end.
Qed.
Lemma tlzw_leave : forall W regs1 mem1 md1 (regs0 : bvmap 5 word) STK sp0 FP ly S W0 mem0 md0 own lyc Sc k r,
ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem1 md1 k ->
spZ regs1 = spZ regs0 - 320 -> spZ regs0 <= sp0 -> sp0 - STK <= spZ regs0 - LZW_TSTK -> spZ regs0 mod 16 = 0 ->
getr regs1 3 = getr regs0 3 -> getr regs1 4 = getr regs0 4 -> getr regs1 21 = w64 r -> 0 <= r < 2 ^ 64 ->
YK0s.ret_ok (getr regs0 1) ->
tlzw_frame (mrestrict (w_H W) mem1) (spZ regs0) regs0 ->
SRr SEGS W (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + PC_LEAVE)) mem1 (seg_rom SEGS)) md1)
(fun W' c' => W' = W /\ exists regs2 md2,
c' = mkCfg (mkst regs2 (getr regs0 1) mem1 (seg_rom SEGS)) md2 /\
ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem1 md2 k /\
aregs_preserved regs0 regs2 /\ getr regs2 10 = w64 r).
Proof.
intros W regs1 mem1 md1 regs0 STK sp0 FP ly S W0 mem0 md0 own lyc Sc k r HJ Hsp Hspe Hwlo Hal16 G3 G4 G21 Hr Hra0 HFR.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & (_ & Hstk0 & Hceil & Hslo & Hshi & H47 & _) & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). assert (HTS : LZW_TSTK = 336 + ASTACK) by reflexivity. assert (ASTACK = 16384) as Has by reflexivity.
remember (Eimg (Ereg regs1 (tsaved_vals regs0))) as E eqn:HE. assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HX : forall j, (j < 13)%nat -> ew E (32 + j)%nat = nth j (tsaved_vals regs0) (Z_to_bv 64 0)).
{ intros j Hj. rewrite HE, Eimg_low, ew_Ereg_extra by (unfold A_TEXT; lia). reflexivity. }
assert (E2 : ew E 2 = getr regs1 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs1 _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regs1 3) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs1 _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs1 4) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs1 _ 4 4%bv eq_refl)).
assert (E21 : ew E 21 = getr regs1 21) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs1 _ 21 21%bv eq_refl)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs0 - 320) by (rewrite E2; exact Hsp).
assert (HS : st_ok_pi SEGS VAL E ss_leave_c (restrict (w_H W) (mkst regs1 (Z_to_bv 64 (BASE + PC_LEAVE)) mem1 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. change ss_leave_c with ss_leave. unfold ss_leave. rewrite HE. apply pa_entry_st_ok_full; rewrite <- ?HE.
- rewrite HE. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- constructor; [|constructor]. unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite Usp. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
exact (tsaved_chunks_ok E _ (spZ regs0) regs0 32 HX HFR).
- cbn [pairwise_disjoint all_disjoint]. repeat split.
- split; [| split; [exact I | exact I]].
cbn [atoms_ok f_atoms]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite Usp.
change (2 ^ 4) with 16. split; [|exact I]. repeat split; try lia.
replace (spZ regs0 - 320) with (spZ regs0 + (-20) * 16) by lia. rewrite Z.mod_add by lia. exact Hal16. }
shok_auto SHOK (SOff 20 0) E (mrestrict (w_H W) mem1).
paj_run_tok RUN HS HJ SHOK Bspan. { awr_ok_tac. }
prreg HS (10%bv : bv 5) Ra0. prreg HS (1%bv : bv 5) Rra. prreg HS (2%bv : bv 5) Rsp. prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp.
lazymatch goal with |- SRr _ _ (mkCfg ?msx _) _ =>
assert (EQM : ms_mem msx = mem1)
by (apply functional_extensionality; intros x; apply HF; intros (rg & Hin & Hrg); cbn in Hin; destruct Hin as [<-|[]]; cbn in Hrg; lia) end.
eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. split; [reflexivity|]. cbn [ms_regs ms_mem]. rewrite EQM in HJ |- *.
lazymatch goal with |- exists _ _, mkCfg (mkst ?rg _ _ _) ?d = _ /\ _ => exists rg, d end.
Local Ltac saved HX j H := pose proof (HX j ltac:(lia)) as H; cbn [Nat.add nth tsaved_vals map snd TSAVED] in H.
saved HX 0%nat X0. saved HX 1%nat X1. saved HX 2%nat X2. saved HX 3%nat X3. saved HX 4%nat X4. saved HX 5%nat X5. saved HX 6%nat X6.
saved HX 7%nat X7. saved HX 8%nat X8. saved HX 9%nat X9. saved HX 10%nat X10. saved HX 11%nat X11. saved HX 12%nat X12.
split; [cbn [ms_regs]; rewrite Rra; cbn [ew ewset Nat.eqb]; rewrite X0;
replace (getr regs0 (Z_to_bv 5 1)) with (getr regs0 1) by reflexivity; rewrite Hra0; reflexivity|].
split; [cbn [ms_mem]; apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ|].
split.
{ cbn [ms_regs].
Local Ltac savedreg HS X := let Hq := fresh "Hq" in
lazymatch goal with |- getr _ ?rr = _ => prreg HS rr Hq; rewrite Hq; cbn [ew ewset Nat.eqb]; rewrite X; reflexivity end.
apply aregs_preserved_of_eqs.
- rewrite Rsp. cbn [ew ewset Nat.eqb]. rewrite Usp. unfold spZ.
replace (bv_unsigned (getr regs0 2) - 320 + 320) with (bv_unsigned (getr regs0 2)) by lia. apply Z_to_bv_bv_unsigned.
- rewrite Rgp. cbn [ew ewset Nat.eqb]. rewrite E3. exact G3.
- rewrite Rtp. cbn [ew ewset Nat.eqb]. rewrite E4. exact G4.
- savedreg HS X1. - savedreg HS X2. - savedreg HS X3. - savedreg HS X4. - savedreg HS X5. - savedreg HS X6.
- savedreg HS X7. - savedreg HS X8. - savedreg HS X9. - savedreg HS X10. - savedreg HS X11. - savedreg HS X12. }
cbn [ms_regs]; rewrite Ra0; cbn [ew ewset Nat.eqb]; rewrite E21; exact G21.
Qed.
Lemma tfree_any : forall W regsT memT STK1 sp1 FP1 lyb Sb W0 memb mdb lyc Sc mdc k p n raw v0,
ajournal SEGS B STK1 sp1 FP1 lyb Sb W0 memb mdb [] lyc Sc W memT mdc k ->
(p = 0 \/ (In (p, n) (ablocks B lyc Sc) /\ aftok FP1 (ablocks B lyb Sb) (p, n))) ->
getr regsT 10 = w64 p -> spZ regsT = sp1 -> ASTACK <= STK1 ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
getr regsT 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
s0Z regsT = v0 -> v0 < alloc_ceiling ->
st_nev Sc < EV_MAX ->
bv_unsigned raw <> pc_free_ra0 (as_code B) -> In [pc_free_ra0 (as_code B); bv_unsigned raw] (as_universe B) ->
SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 (pc_wrap_free (as_code B))) memT (seg_rom SEGS)) mdc)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
ajournal SEGS B STK1 sp1 FP1 lyb Sb W0 memb mdb [] ly2 S2 W2 mem2 md2 (k + 1) /\
aregs_preserved regsT regs2 /\ frames S2 = frames Sc /\
((p = 0 /\ Permutation (ablocks B ly2 S2) (ablocks B lyc Sc)) \/
(p <> 0 /\ exists l1 l2, ablocks B lyc Sc = l1 ++ (p, n) :: l2 /\ ablocks B ly2 S2 = l1 ++ l2)) /\
acall_kept SEGS B lyc Sc W memT W2 mem2 (sp1 - ASTACK) sp1 (fun a => p <> 0 /\ p <= a < p + req_size n)).
Proof.
intros W regsT memT STK1 sp1 FP1 lyb Sb W0 memb mdb lyc Sc mdc k p n raw v0
HJ Hcase Ha0 Hsp Hstk Hgp Htp Hra Hraw Hra4 Hs0 Hv0 Hev Hrane Htr.
pose proof pa_segs_low as Hsegs.
assert (Hch : chain_pre lyc (aview SEGS (w_H W) memT) regsT []).
{ eapply (achain_chain_pre lyc _ sp1 v0 []); [apply achain_low; exact Hv0 | | exact Hs0 | unfold raZ; rewrite Hra; exact Hra4].
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & Hstk0 & Hceil & Hslo & _) & _). pose proof asan_consts as (C1 & _).
rewrite Hsp. lia. }
assert (Htr' : In (call_trace0 (pc_free_ra0 (as_code B)) regsT []) (as_universe B)).
{ rewrite call_trace_nil. unfold raZ. rewrite Hra. replace (bv_unsigned raw =? pc_free_ra0 (as_code B)) with false; [exact Htr|].
symmetry. apply Z.eqb_neq. exact Hrane. }
destruct Hcase as [-> | [Hin Htok]].
- eapply SRr_mono.
{ eapply (aj_free_null_at SEGS B LAWS Hsegs errno_low ML AFREE W regsT memT STK1 sp1 FP1 lyb Sb W0 memb mdb [] lyc Sc mdc k 0 raw []
HJ Ha0); try eassumption; try lia. reflexivity. }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HP & HPerm & Hfrs & HK).
exists ly2, S2, regs2, mem2, md2. split; [reflexivity|]. split; [exact HJ2|]. split; [exact HP|]. split; [exact Hfrs|].
split; [left; split; [reflexivity | exact HPerm]|].
replace (sp1 + 0 - ASTACK) with (sp1 - ASTACK) in HK by lia. replace (sp1 + 0) with sp1 in HK by lia.
eapply acall_kept_mono_E; [exact HK|]. intros a [].
- eapply SRr_mono.
{ eapply (aj_free_at SEGS B LAWS Hsegs errno_low ML AFREE W regsT memT STK1 sp1 FP1 lyb Sb W0 memb mdb [] lyc Sc mdc k p n 0 raw []
HJ Hin Ha0); try eassumption; try lia; try reflexivity.
all: try (intros H0 i Hi; exact (Htok H0 i Hi)).
all: match goal with |- ?g => idtac "FREELEFT" g end. }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HP & Hl & Hfrs & HK).
exists ly2, S2, regs2, mem2, md2. split; [reflexivity|]. split; [exact HJ2|]. split; [exact HP|]. split; [exact Hfrs|].
assert (Hp0 : p <> 0).
{ destruct (al_blocks _ _ LAWS _ _ _ _ _ p n (proj1 HJ) Hin) as (_ & H4096 & _). lia. }
split; [right; split; [exact Hp0 | exact Hl]|].
replace (sp1 + 0 - ASTACK) with (sp1 - ASTACK) in HK by lia. replace (sp1 + 0) with sp1 in HK by lia.
eapply acall_kept_mono_E; [exact HK|]. intros a Ha. split; [exact Hp0 | exact Ha].
Qed.
Lemma tfree_pre_case : forall (p n : Z) rest C (bl : list (Z * Z)) (T : Z * Z -> Prop),
Permutation bl (tnz ((p, n) :: rest) ++ C) -> (forall b, In b (tnz ((p, n) :: rest)) -> T b) ->
p = 0 \/ (In (p, n) bl /\ T (p, n)).
Proof.
intros p n rest C bl T HP HT. destruct (Z.eq_dec p 0) as [-> | Hp]; [left; reflexivity | right].
assert (Hin : In (p, n) (tnz ((p, n) :: rest))) by (rewrite tnz_cons_nz by exact Hp; left; reflexivity).
split; [| exact (HT _ Hin)].
eapply Permutation_in; [apply Permutation_sym; exact HP |]. apply in_app_iff. left. exact Hin.
Qed.
Lemma tfree_post_step : forall (p n : Z) rest C (blc bl2 : list (Z * Z)),
Permutation blc (tnz ((p, n) :: rest) ++ C) ->
((p = 0 /\ Permutation bl2 blc) \/ (p <> 0 /\ exists l1 l2, blc = l1 ++ (p, n) :: l2 /\ bl2 = l1 ++ l2)) ->
Permutation bl2 (tnz rest ++ C).
Proof.
intros p n rest C blc bl2 HP [[-> HQ] | [Hp (l1 & l2 & -> & ->)]].
- rewrite tnz_cons0 in HP. eapply Permutation_trans; [exact HQ | exact HP].
- rewrite tnz_cons_nz in HP by exact Hp. cbn [app] in HP.
apply Permutation_sym. apply (@Permutation_cons_app_inv _ _ l1 l2 (p, n)). apply Permutation_sym. exact HP.
Qed.
Lemma tnz_tl : forall (b : Z * Z) rest (T : Z * Z -> Prop),
(forall x, In x (tnz (b :: rest)) -> T x) -> forall x, In x (tnz rest) -> T x.
Proof.
intros b rest T H x Hx. apply H. unfold tnz in *. cbn [List.filter]. destruct (negb (fst b =? 0)); [right|]; exact Hx.
Qed.
Lemma tnz_in_tl : forall (b : Z * Z) rest x, In x (tnz rest) -> In x (tnz (b :: rest)).
Proof. intros b rest x Hx. unfold tnz in *. cbn [List.filter]. destruct (negb (fst b =? 0)); [right|]; exact Hx. Qed.
Lemma in_cfin : forall (l C bl : list (Z * Z)) x, Permutation bl (l ++ C) -> In x C -> In x bl.
Proof. intros l C bl x HP Hx. eapply Permutation_in; [apply Permutation_sym; exact HP|]. apply in_app_iff. right. exact Hx. Qed.
Lemma region_kept_high_aj : forall E lyc Sc W memc W2 mem2 slo shi (Er : Z -> Prop) n lo hi cs b,
acall_kept SEGS B lyc Sc W memc W2 mem2 slo shi Er ->
bv_unsigned (ew E n) = b -> alloc_ceiling <= b + lo -> b + hi <= 2 ^ 64 -> shi <= b + lo ->
region_kept SEGS E (mrestrict (w_H W) memc) (mrestrict (w_H W2) mem2) (YP09.mkRegion (Some n) lo hi 0 0 cs).
Proof.
intros E lyc Sc W memc W2 mem2 slo shi Er n lo hi cs b (K1 & _) Hn Hlo Hhi Hshi.
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Hn; intros a Ha; [|lia].
apply (mbyte_of_aview SEGS). apply K1; lia.
Qed.
Lemma tlzw_frame_call_kept : forall lyc Sc W memc W2 mem2 slo shi Er spe regs0,
acall_kept SEGS B lyc Sc W memc W2 mem2 slo shi Er ->
shi <= spe - 320 -> alloc_ceiling <= spe - 320 -> spe <= 2 ^ 64 ->
tlzw_frame (mrestrict (w_H W) memc) spe regs0 -> tlzw_frame (mrestrict (w_H W2) mem2) spe regs0.
Proof.
intros lyc Sc W memc W2 mem2 slo shi Er spe regs0 (K1 & _) Hshi Hceil Htop HF.
eapply tlzw_frame_agree; [exact HF|]. intros a Ha. apply (mbyte_of_aview SEGS). apply K1; lia.
Qed.
Definition sv_s1 : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff 8%nat 0) (SLit 3)) (SOff 27%nat 0).
Definition sr_clean : list sv :=
sr_set (sr_set (sr_set (sr_set (sr_set (sr_set sr_atoms 22%bv sv_s1) 20%bv (SOff 8 8)) 19%bv (SOff 8 16))
18%bv (SOff 8 24)) 9%bv (SOff 8 32)) 1%bv (SOff 8 40).
Definition ctx_region : YP09.region := YP09.mkRegion (Some 8%nat) 0 72 0 0
[YP09.mkChunk 0 (CVal 8 (SOff 45 0)); YP09.mkChunk 8 (CVal 8 (SOff 46 0)); YP09.mkChunk 16 (CVal 8 (SOff 47 0));
YP09.mkChunk 24 (CVal 8 (SOff 48 0)); YP09.mkChunk 32 (CVal 8 (SOff 49 0)); YP09.mkChunk 40 (CVal 8 (SOff 50 0))].
Definition ss_clean : sstate :=
mkSS PC_CLEAN sr_clean [ YP09.mkRegion (Some 2%nat) 0 320 0 0 (tsaved_chunks 32); ctx_region ] None
(mkFacts [ (2%nat, mkAF (2^46) (2^47) 4); (8%nat, PTR 4); (27%nat, mkAF SB SB 0) ] [] []).
Definition ss_clean_c : sstate := Eval vm_compute in ss_clean.
Lemma tlzw_clean : forall W regs1 mem1 md1 (regs0 : bvmap 5 word) STK sp0 FP ly S W0 mem0 md0 own ly1 S1 k
(ctx pti nti plm nlm plc nlc pli nli ptm ntm pld nld : Z) (Cfin : list (Z * Z)) (r : Z),
let tabs := [(pld, nld); (pti, nti); (plm, nlm); (plc, nlc); (pli, nli); (ptm, ntm)] in
ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own ly1 S1 W mem1 md1 k ->
Permutation (ablocks B ly1 S1) (tnz tabs ++ (ctx, 72) :: Cfin) ->
(forall b, In b ((ctx, 72) :: tnz tabs) -> aftok FP (ablocks B ly S) b) ->
(forall b, In b tabs -> 0 <= fst b < 2 ^ 64) ->
val_mem SEGS (mrestrict (w_H W) mem1) ctx 8 pti -> val_mem SEGS (mrestrict (w_H W) mem1) (ctx + 8) 8 plm ->
val_mem SEGS (mrestrict (w_H W) mem1) (ctx + 16) 8 plc -> val_mem SEGS (mrestrict (w_H W) mem1) (ctx + 24) 8 pli ->
val_mem SEGS (mrestrict (w_H W) mem1) (ctx + 32) 8 ptm -> val_mem SEGS (mrestrict (w_H W) mem1) (ctx + 40) 8 pld ->
YK0s.ret_ok (getr regs0 1) -> spZ regs0 mod 16 = 0 -> sp0 - STK <= spZ regs0 - LZW_TSTK -> spZ regs0 <= sp0 ->
getr regs0 3 = w64 (as_gp B) -> getr regs0 4 = w64 (as_tp B) ->
spZ regs1 = spZ regs0 - 320 -> getr regs1 3 = getr regs0 3 -> getr regs1 4 = getr regs0 4 ->
getr regs1 8 = w64 ctx -> getr regs1 27 = w64 SB -> getr regs1 21 = w64 r -> 0 <= r < 2 ^ 64 ->
getr regs1 22 = alu64 ALU_ADD (alu64 ALU_SRL (Z_to_bv 64 ctx) (Z_to_bv 64 3)) (Z_to_bv 64 SB) ->
getr regs1 20 = w64 (ctx + 8) -> getr regs1 19 = w64 (ctx + 16) -> getr regs1 18 = w64 (ctx + 24) ->
getr regs1 9 = w64 (ctx + 32) -> getr regs1 1 = w64 (ctx + 40) ->
tlzw_frame (mrestrict (w_H W) mem1) (spZ regs0) regs0 ->
st_nev S1 + 7 <= EV_MAX ->
SRr SEGS W (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + PC_CLEAN)) mem1 (seg_rom SEGS)) md1)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
c2 = mkCfg (mkst regs2 (getr regs0 1) mem2 (seg_rom SEGS)) md2 /\
ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 (k + 7) /\
aregs_preserved regs0 regs2 /\ getr regs2 10 = w64 r /\ frames S2 = frames S1 /\
Permutation (ablocks B ly2 S2) Cfin /\
acall_kept SEGS B ly1 S1 W mem1 W2 mem2 (spZ regs0 - 320 - ASTACK) (spZ regs0 - 320)
(fun a => exists b, In b ((ctx, 72) :: tnz tabs) /\ fst b <= a < fst b + req_size (snd b))).
Proof.
intros W regs1 mem1 md1 regs0 STK sp0 FP ly S W0 mem0 md0 own ly1 S1 k ctx pti nti plm nlm plc nlc pli nli ptm ntm pld nld Cfin r tabs
HJ HB Htok Hrng Mti Mlm Mlc Mli Mtm Mld Hra0 Hal16 Hwlo Hwhi Hgp Htp Hsp G3 G4 G8 G20 G21 Hr G9 G18 G27 G24 G19 G26 HFR Hev.
subst tabs.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof HJ as (HAR1 & Hly1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & (_ & Hstk0 & Hceil & Hslo & Hshi & H47 & _) & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). assert (HTS : LZW_TSTK = 336 + ASTACK) by reflexivity. assert (ASTACK = 16384) as Has by reflexivity.
assert (Hctx : In (ctx, 72) (ablocks B ly1 S1)) by (eapply in_cfin; [exact HB | left; reflexivity]).
destruct (al_blocks _ _ LAWS _ _ _ _ _ ctx 72 HAR1 Hctx) as (Hc16 & Hc4096 & Hcceil & Hch_ia & _ & _). pose proof (proj1 Hch_ia) as Hch. change (req_size 72) with 72 in *.
pose proof (blk_off_imgP _ _ _ _ _ _ ctx 72 HAR1 Hctx) as Hch_img.
set (sp := spZ regs0 - 320) in *.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hsp0al & _) & _).
assert (Hom : (sp - sp0) mod 16 = 0).
{ subst sp. pose proof (Z.div_mod sp0 16 ltac:(lia)) as D0. pose proof (Z.div_mod (spZ regs0) 16 ltac:(lia)) as D1.
rewrite Hsp0al, Z.add_0_r in D0. rewrite Hal16, Z.add_0_r in D1.
replace (spZ regs0 - 320 - sp0) with ((spZ regs0 / 16 - 20 - sp0 / 16) * 16) by lia. apply Z_mod_mult. }
pose proof (ajournal_sub_init SEGS B _ _ _ _ _ _ _ _ _ _ _ W mem1 md1 _ ASTACK sp
(ablocks_fp ((ctx, 72) :: tnz [(pld, nld); (pti, nti); (plm, nlm); (plc, nlc); (pli, nli); (ptm, ntm)])) (sp - sp0)
HJ ltac:(lia) Hom ltac:(lia) ltac:(lia) ltac:(lia)) as HJL.
remember (Eimg (Ereg regs1 (tsaved_vals regs0 ++ map (Z_to_bv 64) [pti; plm; plc; pli; ptm; pld]))) as E eqn:HE. assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HX : forall j, (j < 13)%nat -> ew E (32 + j)%nat = nth j (tsaved_vals regs0) (Z_to_bv 64 0)).
{ intros j Hj. rewrite HE, Eimg_low, ew_Ereg_extra by (unfold A_TEXT; lia). rewrite app_nth1; [reflexivity|]. unfold tsaved_vals. rewrite length_map. cbn. exact Hj. }
assert (HY : forall j, (j < 6)%nat -> ew E (45 + j)%nat = nth j (map (Z_to_bv 64) [pti; plm; plc; pli; ptm; pld]) (Z_to_bv 64 0)).
{ intros j Hj. replace (45 + j)%nat with (32 + (13 + j))%nat by lia. rewrite HE, Eimg_low, ew_Ereg_extra by (unfold A_TEXT; lia).
rewrite app_nth2 by (unfold tsaved_vals; rewrite length_map; cbn; lia).
unfold tsaved_vals. rewrite length_map. replace (13 + j - length TSAVED)%nat with j by (cbn; lia). reflexivity. }
assert (E2 : ew E 2 = getr regs1 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs1 _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regs1 3) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs1 _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs1 4) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs1 _ 4 4%bv eq_refl)).
assert (E8 : ew E 8 = Z_to_bv 64 ctx) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs1 _ 8 8%bv eq_refl); exact G8).
assert (E20 : ew E 27 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs1 _ 27 27%bv eq_refl); exact G20).
assert (E21 : ew E 21 = Z_to_bv 64 r) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs1 _ 21 21%bv eq_refl); exact G21).
pose proof (HY 0%nat ltac:(lia)) as E45. pose proof (HY 1%nat ltac:(lia)) as E46. pose proof (HY 2%nat ltac:(lia)) as E47.
pose proof (HY 3%nat ltac:(lia)) as E48. pose proof (HY 4%nat ltac:(lia)) as E49. pose proof (HY 5%nat ltac:(lia)) as E50.
cbn [Nat.add nth map] in E45, E46, E47, E48, E49, E50.
assert (Usp : bv_unsigned (ew E 2) = sp) by (rewrite E2; exact Hsp).
assert (HBx : U E (SOff 27 0) = SHADOW_OFF) by (rewrite (U_atom E 27 SB E20) by (unfold SB; lia); reflexivity).
assert (HS : st_ok_pi SEGS VAL E ss_clean_c (restrict (w_H W) (mkst regs1 (Z_to_bv 64 (BASE + PC_CLEAN)) mem1 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. change ss_clean_c with ss_clean. unfold ss_clean. rewrite HE. apply pa_entry_st_ok_full; rewrite <- ?HE.
- rewrite HE. unfold sr_clean.
repeat (apply regs_ok_pin; [| intros X'; discriminate X' |]); [apply regs_ok_Eimg_Ereg | ..]; rewrite <- ?HE; cbn [sv_denot];
rewrite ?Z_to_bv_bv_unsigned, ?E8, ?E20; rewrite ?unsigned_lit_small by lia.
all: first [exact G18 | exact G27 | exact G24 | exact G19 | exact G26
| unfold sv_s1; cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned, E8, E20; exact G9
| match goal with |- ?g => idtac "PINLEFT" g end].
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor]]; unfold region_ok, ctx_region;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
+ rewrite Usp. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
replace sp with (spZ regs0 - 320) by reflexivity. exact (tsaved_chunks_ok E _ (spZ regs0) regs0 32 HX HFR).
+ rewrite E8, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
repeat apply Forall_cons; try apply Forall_nil.
all: lazymatch goal with |- YP09.chunk_ok _ ?Ex _ ?cx (YP09.mkChunk ?o (CVal 8 (SOff ?a 0))) =>
lazymatch goal with Ea : ew Ex a = Z_to_bv 64 ?v, HR : forall b, In b _ -> 0 <= fst b < 2 ^ 64 |- _ =>
apply (chunk_ok_val SEGS Ex _ cx o 8 (SOff a 0) v);
[ cbn [sv_denot]; rewrite Ea, Z.add_0_r, unsigned_lit_small; [reflexivity | ]
| change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64) | cbn; lia | rewrite ?Z.add_0_r; assumption ] end end.
all: first [ exact (Hrng (pti, nti) ltac:(cbv; tauto)) | exact (Hrng (plm, nlm) ltac:(cbv; tauto)) | exact (Hrng (plc, nlc) ltac:(cbv; tauto))
| exact (Hrng (pli, nli) ltac:(cbv; tauto)) | exact (Hrng (ptm, ntm) ltac:(cbv; tauto)) | exact (Hrng (pld, nld) ltac:(cbv; tauto))
| match goal with |- ?g => idtac "CHUNKLEFT" g end ].
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint, ctx_region. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
rewrite Usp, E8, unsigned_lit_small by lia. repeat split. lia.
- split; [| split; [exact I | exact I]].
cbn [atoms_ok f_atoms]. unfold afact_ok, PTR. cbn [af_lo af_hi af_al2]. rewrite Usp, E8, E20, !unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r. ceil; unfold SB, ASAN_CEIL, kLowShadowBeg, kHighMemBeg. rewrite ?C3 in *. idtac.
repeat match goal with |- _ /\ _ => split end; try lia.
subst sp. replace (spZ regs0 - 320) with (spZ regs0 + (-20) * 16) by lia. rewrite Z.mod_add by lia. exact Hal16. }
clear HE.
shok_auto SHOK (SOff 27 0) E (mrestrict (w_H W) mem1).
assert (SEP : forall lyq Sq Wq memq mdq (x y : Z * Z) l1 l2,
AR SEGS B lyq Sq Wq memq mdq -> Permutation (ablocks B lyq Sq) (l1 ++ x :: l2) -> In y l1 \/ In y l2 ->
zdisjoint (block_rng x) (block_rng y)).
{ intros lyq Sq Wq memq mdq x y l1 l2 HARq HPq Hy.
assert (Hy' : In y (l1 ++ l2)) by (apply in_app_iff; exact Hy).
apply in_split in Hy' as (m1 & m2 & Em).
apply (sep_blocks_perm SEGS B LAWS lyq Sq Wq memq mdq x y (m1 ++ m2) HARq).
eapply Permutation_trans; [exact HPq|]. eapply Permutation_trans; [apply Permutation_sym; apply Permutation_middle|].
apply perm_skip. rewrite Em. apply Permutation_sym. apply Permutation_middle. }
pose proof HB as HB0.
assert (AG : forall n, (n < 51)%nat -> ew E n = ew E n) by (intros; reflexivity).
Local Ltac mem_unchanged HFR :=
lazymatch goal with HF : frame_of _ _ ?m0 (ms_mem ?msx) |- _ =>
let EQM := fresh "EQM" in
assert (EQM : ms_mem msx = m0)
by (apply functional_extensionality; intros x; apply HF; intros (rg & Hin & Hrg); cbn in Hin;
repeat (destruct Hin as [<-|Hin]; [cbn in Hrg; lia|]); destruct Hin);
cbn [ms_mem] in EQM; rewrite <- EQM in HFR; clear EQM end;
repeat lazymatch goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
Local Ltac run_to_free HS HJL SHOK AG E8 E20 Hctx :=
paj_run_tok RUN HS HJL SHOK Bspan;
[ lazymatch goal with |- range_addressable _ (U ?Ex _) (U _ (SOff 8 ?c)) _ =>
rewrite (U_atom_off Ex 8 _ c) by (first [cbn [ew ewset Nat.eqb]; rewrite ?(AG 8%nat) by lia; exact E8 | lia]);
eapply (obl_of_block SEGS B LAWS _ _ _ _ _ Ex (SOff 27 0) _ 8 _ 72 (proj1 HJL) Hctx);
[ rewrite (U_atom Ex 27 SB) by (first [cbn [ew ewset Nat.eqb]; rewrite ?(AG 27%nat) by lia; exact E20 | unfold SB; lia]); reflexivity
| lia | change (req_size 72) with 72; lia ] end
| awr_ok_tac | ].
Local Ltac call_free HS HJL HB AG Ea E3 E4 E8 Usp Hgp Htp Hcceil TL G3 G4 casetac :=
let Ra0 := fresh "Ra0" in let Rra := fresh "Rra" in let Rsp := fresh "Rsp" in let Rgp := fresh "Rgp" in
let Rtp := fresh "Rtp" in let Rs0 := fresh "Rs0" in
prreg HS (10%bv : bv 5) Ra0; prreg HS (1%bv : bv 5) Rra; prreg HS (2%bv : bv 5) Rsp; prreg HS (3%bv : bv 5) Rgp;
prreg HS (4%bv : bv 5) Rtp; prreg HS (8%bv : bv 5) Rs0;
cbn [ew ewset Nat.eqb] in Ra0, Rsp, Rgp, Rtp, Rs0;
pmkst HS; ppcs;
lazymatch type of HJL with ajournal _ _ ?STK1 ?sp1 ?FP1 ?lyb ?Sb ?W0 ?memb ?mdb [] ?lyc ?Sc ?Wc (ms_mem ?msX) ?mdc ?kk =>
lazymatch type of Rra with _ = Z_to_bv 64 ?ra =>
lazymatch type of Ea with ew _ ?na = Z_to_bv 64 ?p =>
eapply SRr_bind;
[ eapply (tfree_any Wc (ms_regs msX) (ms_mem msX) STK1 sp1 FP1 lyb Sb W0 memb mdb lyc Sc mdc kk p _ (Z_to_bv 64 ra) _ HJL);
[ casetac HB
| rewrite Ra0, ?(AG na) by lia; rewrite Ea; reflexivity
| unfold spZ; rewrite Rsp, ?(AG 2%nat) by lia; rewrite Usp; lia
| lia
| rewrite Rgp, ?(AG 3%nat) by lia; rewrite E3, G3; exact Hgp | rewrite Rtp, ?(AG 4%nat) by lia; rewrite E4, G4; exact Htp
| exact Rra | apply ret_ok_codeptr_v; [cbv; split; [congruence | reflexivity] | reflexivity] | rewrite unsigned_lit_small by lia; lia
| unfold s0Z; rewrite Rs0, ?(AG 8%nat) by lia; rewrite E8; apply unsigned_lit_small; lia
| clear -Hcceil; lia
| let Hnev := fresh "Hnev" in pose proof HJL as (_ & _ & _ & _ & _ & _ & Hnev & _); lia
| rewrite unsigned_lit_small by lia; pose proof (proj1 (pal_rt_below B TL)); lia
| rewrite unsigned_lit_small by lia; hul_tac ]
| clear Ra0 Rra Rsp Rgp Rtp Rs0 ]
end end end.
Local Ltac case_tab HSUB HB :=
eapply tfree_pre_case; [exact HB|]; intros b Hb _ i Hi;
destruct b as [bp bn]; apply (inFP_ablocks_fp _ bp bn i); [right; apply HSUB; exact Hb | exact Hi].
Local Ltac after_free HS HJL HB Hctx SEP AG Usp E8 Hcceil SHOK HFR keep :=
let W2 := fresh "W" in let c2 := fresh "c" in let Hwle := fresh "Hwle" in
let ly2 := fresh "ly" in let S2 := fresh "S" in let regs2 := fresh "regs" in let mem2 := fresh "mem" in let md2 := fresh "md" in
let HJL2 := fresh "HJL" in let HP2 := fresh "HP" in let Hfrs2 := fresh "Hfrs" in let Hpost := fresh "Hpost" in let HK2 := fresh "HK" in
cbv beta; intros W2 c2 Hwle (ly2 & S2 & regs2 & mem2 & md2 & -> & HJL2 & HP2 & Hfrs2 & Hpost & HK2);
let HB2 := fresh "HB" in pose proof (tfree_post_step _ _ _ _ _ _ HB Hpost) as HB2;
let Hctx2 := fresh "Hctx" in pose proof (in_cfin _ _ _ _ HB2 ltac:(left; reflexivity)) as Hctx2;
let K := lazymatch type of HS with st_ok_pi _ _ _ ?ss _ => eval vm_compute in (run_K_lo 0 (SOff 27 0) [] ss) | st_ok _ _ ?ss _ => eval vm_compute in (run_K_lo 0 (SOff 27 0) [] ss)  end in
let HS2 := fresh "HS2" in
jafter_call_keep_pi HS K regs2 (mrestrict (w_H W2) mem2) HP2 keep HS2;
match type of HS2 with ?Q -> _ =>
let HQ := fresh "HQ" in
assert (HQ : Q);
[ cbn [ms_mem restrict]; repeat apply Forall_cons; try apply Forall_nil;
first
[ eapply (region_kept_high_aj _ _ _ _ _ _ _ _ _ _ 2%nat); [exact HK2 | cbn [ew ewset Nat.eqb]; rewrite ?(AG 2%nat) by lia; exact Usp | lia | lia | lia]
| eapply (region_kept_block_aj SEGS B _ _ _ _ _ _ _ _ _ _ 8%nat 0 72 0 0 _ _ 72);
[ exact HK2 | cbn [ew ewset Nat.eqb]; rewrite ?(AG 8%nat) by lia; rewrite E8; apply unsigned_lit_small; lia
| exact Hctx | lia | change (req_size 72) with 72; lia | lia
| intros a Ha [Hp0 Hpa];
lazymatch type of HB with Permutation _ (tnz ((?p, ?n) :: ?rest) ++ _) =>
pose proof (SEP _ _ _ _ _ (p, n) (_, 72) [] (tnz rest ++ (_, 72) :: _) (proj1 HJL)
ltac:(rewrite tnz_cons_nz in HB by exact Hp0; exact HB)
ltac:(right; apply in_app_iff; right; left; reflexivity)) as Hd;
unfold zdisjoint, block_rng in Hd; cbn [fst snd] in Hd; change (req_size 72) with 72 in Hd; lia end ] ]
| specialize (HS2 HQ); clear HQ ] end;
clear HS; rewrite <- restrict_mkst_fx in HS2; rename HS2 into HS;
let AG2 := fresh "AG" in let Ev := fresh "E" in let HEv := fresh "HE" in
lazymatch type of AG with forall n, _ -> _ = ew ?E0 n =>
lazymatch type of HS with st_ok_pi _ _ ?Enew _ _ =>
remember Enew as Ev eqn:HEv in HS;
let HEIv := fresh "HEI" in
lazymatch type of HEv with
| _ = havoc ?Eo ?kk ?ws => lazymatch goal with Ho : img_env ?val ?lim Eo |- _ =>
pose proof (img_env_havoc Eo kk ws Ho ltac:(cbv; lia)) as HEIv; rewrite <- HEv in HEIv end
| _ = ?En => try (lazymatch goal with Hn : img_env _ _ En |- _ => rewrite <- HEv in Hn end) end;
repeat match goal with H : img_env _ _ (ewset _ _ _) |- _ => clear H end;
assert (AG2 : forall n, (n < 51)%nat -> ew Ev n = ew E0 n)
by (intros nn Hnn; rewrite HEv; rewrite ew_havoc_old by lia; rewrite ?ew_ewset_other by lia; apply AG; exact Hnn);
clear HEv | st_ok _ ?Enew _ _ =>
remember Enew as Ev eqn:HEv in HS;
let HEIv := fresh "HEI" in
lazymatch type of HEv with
| _ = havoc ?Eo ?kk ?ws => lazymatch goal with Ho : img_env ?val ?lim Eo |- _ =>
pose proof (img_env_havoc Eo kk ws Ho ltac:(cbv; lia)) as HEIv; rewrite <- HEv in HEIv end
| _ = ?En => try (lazymatch goal with Hn : img_env _ _ En |- _ => rewrite <- HEv in Hn end) end;
repeat match goal with H : img_env _ _ (ewset _ _ _) |- _ => clear H end;
assert (AG2 : forall n, (n < 51)%nat -> ew Ev n = ew E0 n)
by (intros nn Hnn; rewrite HEv; rewrite ew_havoc_old by lia; rewrite ?ew_ewset_other by lia; apply AG; exact Hnn);
clear HEv  end end;
let HFR2 := fresh "HFR" in
lazymatch type of HFR with tlzw_frame _ ?spe ?rg0 =>
pose proof (tlzw_frame_call_kept _ _ _ _ _ _ _ _ _ spe rg0 HK2 ltac:(lia) ltac:(lia) ltac:(lia) HFR) as HFR2 end;
clear HFR; rename HFR2 into HFR;
clear AG HB Hctx HJL HK2 HP2 Hpost SHOK; rename AG2 into AG; rename HB2 into HB; rename Hctx2 into Hctx; rename HJL2 into HJL;
lazymatch type of HS with st_ok_pi _ _ ?Enew _ (restrict (w_H ?Wn) ?msn) =>
shok_auto SHOK (SOff 27 0) Enew (mrestrict (w_H Wn) (ms_mem msn)) | st_ok _ ?Enew _ (restrict (w_H ?Wn) ?msn) =>
shok_auto SHOK (SOff 27 0) Enew (mrestrict (w_H Wn) (ms_mem msn))  end.
Local Ltac one_free HS HJL SHOK HB Hctx SEP AG Ea E3 E4 E8 E20 Usp Hgp Htp Hcceil TL G3 G4 HSUB HFR :=
run_to_free HS HJL SHOK AG E8 E20 Hctx;
mem_unchanged HFR;
call_free HS HJL HB AG Ea E3 E4 E8 Usp Hgp Htp Hcceil TL G3 G4 ltac:(case_tab HSUB);
after_free HS HJL HB Hctx SEP AG Usp E8 Hcceil SHOK HFR [0%nat; 1%nat];
let HSUB2 := fresh "HSUB" in
pose proof (fun x Hx => HSUB x (tnz_in_tl _ _ x Hx)) as HSUB2; cbv beta in HSUB2; clear HSUB; rename HSUB2 into HSUB.
assert (HSUB : forall x, In x (tnz [(pld, nld); (pti, nti); (plm, nlm); (plc, nlc); (pli, nli); (ptm, ntm)]) ->
In x (tnz [(pld, nld); (pti, nti); (plm, nlm); (plc, nlc); (pli, nli); (ptm, ntm)])) by (intros x Hx; exact Hx).
one_free HS HJL SHOK HB Hctx SEP AG E50 E3 E4 E8 E20 Usp Hgp Htp Hcceil TL G3 G4 HSUB HFR. rename Hfrs into Hfrs1.
one_free HS HJL SHOK HB Hctx SEP AG E45 E3 E4 E8 E20 Usp Hgp Htp Hcceil TL G3 G4 HSUB HFR. rename Hfrs into Hfrs2.
one_free HS HJL SHOK HB Hctx SEP AG E46 E3 E4 E8 E20 Usp Hgp Htp Hcceil TL G3 G4 HSUB HFR. rename Hfrs into Hfrs3.
one_free HS HJL SHOK HB Hctx SEP AG E47 E3 E4 E8 E20 Usp Hgp Htp Hcceil TL G3 G4 HSUB HFR. rename Hfrs into Hfrs4.
one_free HS HJL SHOK HB Hctx SEP AG E48 E3 E4 E8 E20 Usp Hgp Htp Hcceil TL G3 G4 HSUB HFR. rename Hfrs into Hfrs5.
one_free HS HJL SHOK HB Hctx SEP AG E49 E3 E4 E8 E20 Usp Hgp Htp Hcceil TL G3 G4 HSUB HFR. rename Hfrs into Hfrs6.
idtac "FREE6 DONE".
paj_run_tok RUN HS HJL SHOK Bspan; [awr_ok_tac|].
mem_unchanged HFR.
call_free HS HJL HB AG E8 E3 E4 E8 Usp Hgp Htp Hcceil TL G3 G4
ltac:(fun HB' => right; split; [exact Hctx | intros _ i Hi; apply (inFP_ablocks_fp _ ctx 72 i); [left; reflexivity | exact Hi]]).
cbv beta. intros W7 c7 Hwle7 (ly7 & S7 & regs7 & mem7 & md7 & -> & HJL7 & HP7 & Hfrs7 & Hpost7 & HK7).
assert (HB7 : Permutation (ablocks B ly7 S7) Cfin).
{ destruct Hpost7 as [[Hc0 _] | [_ (l1 & l2 & Ebl & ->)]]; [exfalso; clear -Hc0 Hc4096; lia|].
cbn [tnz List.filter app] in HB. rewrite Ebl in HB.
apply Permutation_sym. apply (@Permutation_cons_app_inv _ Cfin l1 l2 (ctx, 72)). apply Permutation_sym. exact HB. }
pose proof (tlzw_frame_call_kept _ _ _ _ _ _ _ _ _ (spZ regs0) regs0 HK7 ltac:(lia) ltac:(lia) ltac:(lia) HFR) as HFR7.
idtac "FREE7 DONE".
assert (HJ7 : ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own ly7 S7 W7 mem7 md7 (k + 7)).
{ change own with ([] ++ own).
eapply (ajournal_sub SEGS B LAWS Hsegs); [exact HJ | exact HJL7 | lia | lia |].
intros a Ha. apply inFP_ablocks_fp_inv in Ha as (p & n & Hpn & Hpa).
assert (Hlive : In (p, n) (ablocks B ly1 S1)).
{ eapply Permutation_in; [apply Permutation_sym; exact HB0|].
pose proof Hpn as Hpn0.
destruct Hpn0 as [Epn | Hpn']; [apply in_app_iff; right; left; exact Epn | apply in_app_iff; left; exact Hpn']. }
destruct (in_dec (fun x y : Z * Z => ltac:(decide equality; apply Z.eq_dec)) (p, n) (ablocks B ly S)) as [He | He].
- left. split; [| exists p, n; split; [exact Hlive | exact Hpa]].
replace a with (p + (a - p)) by lia. apply (Htok (p, n) Hpn He). cbn [snd]. lia.
- right. exists p, n. split; [exact Hlive | split; [exact He | exact Hpa]]. }
prreg HS (2%bv : bv 5) Rsp7. prreg HS (3%bv : bv 5) Rgp7. prreg HS (4%bv : bv 5) Rtp7. prreg HS (21%bv : bv 5) Rs5.
cbn [ew ewset Nat.eqb] in Rsp7, Rgp7, Rtp7, Rs5.
apreserved HP7 (2%bv : bv 5) X2. apreserved HP7 (3%bv : bv 5) X3. apreserved HP7 (4%bv : bv 5) X4. apreserved HP7 (21%bv : bv 5) X21.
assert (Q2 : spZ regs7 = spZ regs0 - 320).
{ unfold spZ at 1. rewrite X2, Rsp7, ?(AG 2%nat) by lia. exact Usp. }
assert (Q3 : getr regs7 3 = getr regs0 3) by (rewrite X3, Rgp7, ?(AG 3%nat) by lia; rewrite E3; exact G3).
assert (Q4 : getr regs7 4 = getr regs0 4) by (rewrite X4, Rtp7, ?(AG 4%nat) by lia; rewrite E4; exact G4).
assert (Q21 : getr regs7 21 = w64 r) by (rewrite X21, Rs5, ?(AG 21%nat) by lia; rewrite E21; reflexivity).
eapply SRr_mono.
{ exact (tlzw_leave W7 regs7 mem7 md7 regs0 STK sp0 FP ly S W0 mem0 md0 own ly7 S7 (k + 7) r HJ7 Q2 Hwhi Hwlo Hal16 Q3 Q4 Q21 Hr Hra0 HFR7). }
cbv beta. intros W8 c8 _ (-> & regs8 & md8 & -> & HJ8 & HP8 & Ha0).
exists ly7, S7, regs8, mem7, md8. split; [reflexivity|]. split; [exact HJ8|]. split; [exact HP8|]. split; [exact Ha0|].
split; [rewrite Hfrs7, Hfrs6, Hfrs5, Hfrs4, Hfrs3, Hfrs2, Hfrs1; reflexivity|].
split; [exact HB7|].
eapply (acall_kept_of_journal SEGS B pa_segs_low); [exact HJL7 | exact HAR1 | | |].
- intros a Ha. apply inFP_ablocks_fp_inv in Ha as (p & n & Hpn & Hpa). exists (p, n). split; [exact Hpn | exact Hpa].
- intros b m i Hb Hi HnE.
lazymatch type of HB0 with Permutation _ ?L => assert (Hb' : In (b, m) L) by (eapply Permutation_in; [exact HB0 | exact Hb]) end.
apply in_app_iff in Hb' as [Hb' | [Hb' | Hb']].
+ exfalso. apply HnE. exists (b, m). split; [right; exact Hb' | cbn [fst snd]; lia].
+ exfalso. apply HnE. exists (b, m). split; [left; exact Hb' | cbn [fst snd]; lia].
+ eapply Permutation_in; [apply Permutation_sym; exact HB7 | exact Hb'].
-
apply sink_closed_ablocks_fp. constructor; [cbn [fst]; clear - Hc4096; lia|].
apply Forall_forall. intros b Hb. pose proof (Hrng b (In_tnz _ _ Hb)) as Hb0.
unfold tnz in Hb. apply filter_In in Hb as [_ Hnzb]. destruct (Z.eqb_spec (fst b) 0); [discriminate | lia].
Qed.
End h.
End f.
End e.
