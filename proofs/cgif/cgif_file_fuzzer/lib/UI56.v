(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YM06 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0i YO0f YO0x YO0d YO0e
YO0p YO0j YO0m YO0l YO0n YO0k YO0o.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UH00 UH03 UH02 UN3b YI06 UI5b YI09 YI08 YI0r UI1w UI5o
YI00 YI05 YI5a UI5f UIZs.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Section e. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma rx_garr8_skipn : forall m p (P : list Z) (c : nat),
garr8 ubs0segs m p P -> garr8 ubs0segs m (p + Z.of_nat c) (skipn c P).
Proof using.
intros m p P c H. destruct (Nat.le_gt_cases c (length P)) as [Hc|Hc].
- rewrite <- (firstn_skipn c P) in H. apply garr8_app in H as [_ H2]. rewrite firstn_length_le in H2 by exact Hc. exact H2.
- rewrite skipn_all2 by lia. apply garr8_nil.
Qed.
Lemma rx_garr8_firstn : forall m p (l : list Z) (n : nat), garr8 ubs0segs m p l -> garr8 ubs0segs m p (firstn n l).
Proof using. intros m p l n H. rewrite <- (firstn_skipn n l) in H. apply garr8_app in H as [H1 _]. exact H1. Qed.
Lemma rx_garr8_copy : forall m m' s d (l : list Z),
garr8 ubs0segs m s l -> (forall i, 0 <= i < Z.of_nat (length l) -> mbyte ubs0segs m' (d + i) = mbyte ubs0segs m (s + i)) ->
garr8 ubs0segs m' d l.
Proof using.
intros m m' s d l H Hc j Hj. destruct (H j Hj) as [Hv Hr]. split; [|exact Hr].
intros k Hk. replace (d + Z.of_nat j + Z.of_nat k) with (d + (Z.of_nat j + Z.of_nat k)) by lia.
rewrite Hc by (cbn in Hk; lia). replace (s + (Z.of_nat j + Z.of_nat k)) with (s + Z.of_nat j + Z.of_nat k) by lia. apply Hv. exact Hk.
Qed.
Lemma rx_garr8_slice_copy : forall m m' p (P : list Z) d c n,
garr8 ubs0segs m p P -> 0 <= c -> 0 <= n -> c + n <= Z.of_nat (length P) ->
(forall i, 0 <= i < n -> mbyte ubs0segs m' (d + i) = mbyte ubs0segs m (p + c + i)) ->
garr8 ubs0segs m' d (firstn (Z.to_nat n) (skipn (Z.to_nat c) P)) /\ Z.of_nat (length (firstn (Z.to_nat n) (skipn (Z.to_nat c) P))) = n.
Proof using.
intros m m' p P d c n H Hc Hn Hcn Hcp.
assert (Hlen : Z.of_nat (length (firstn (Z.to_nat n) (skipn (Z.to_nat c) P))) = n) by (rewrite length_firstn, length_skipn; lia).
split; [|exact Hlen]. eapply rx_garr8_copy.
- apply rx_garr8_firstn. apply (rx_garr8_skipn m p P (Z.to_nat c)). exact H.
- intros i Hi. rewrite Hlen in Hi. rewrite Hcp by lia. f_equal. lia.
Qed.
Lemma st_ok_pin_rx : forall segs E ss ms (r : reg) z,
st_ok segs E ss ms -> getr (ms_regs ms) r = Z_to_bv 64 z -> bv_eqb r 0 = false ->
st_ok segs E (mkSS (ss_pc ss) (sr_set (ss_regs ss) r (SLit z)) (ss_mem ss) (ss_resv ss) (ss_facts ss)) ms.
Proof using.
intros segs E ss ms r z HS Hr Hr0. apply st_ok_regs; [exact HS|].
intros rr. destruct (decide (rr = r)) as [->|Hne].
- rewrite sr_get_set_same by exact Hr0. cbn [sv_denot]. rewrite <- (st_ok_reg segs E ss ms r HS), Hr. reflexivity.
- rewrite sr_get_set_other by exact Hne. reflexivity.
Qed.
Lemma mbyte_of_rd : forall (m m' : word -> option byte) spc d n st a,
(forall x : word, ~ (spc - RD_FRAME <= bv_unsigned x < spc) -> ~ (d <= bv_unsigned x < d + n) ->
~ (st + 16 <= bv_unsigned x < st + 24) -> m' x = m x) ->
0 <= a < 2 ^ 64 -> ~ (spc - RD_FRAME <= a < spc) -> ~ (d <= a < d + n) -> ~ (st + 16 <= a < st + 24) ->
mbyte ubs0segs m' a = mbyte ubs0segs m a.
Proof using.
intros m m' spc d n st a H Ha H1 H2 H3. unfold mbyte.
rewrite H; [reflexivity | rewrite unsigned_lit_small by exact Ha; exact H1 | rewrite unsigned_lit_small by exact Ha; exact H2 | rewrite unsigned_lit_small by exact Ha; exact H3].
Qed.
Section S.
Variable API : AllocAPI ubs0_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs0_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs0_msyms MR.
Definition ss_frees : sstate :=
mkSS FREESPC (sr_set sr_atoms 9%bv (SLit (2 ^ 64 - 1)))
[ YP09.mkRegion (Some 2%nat) 0 RFC_FRAME 0 RFC_FRAME
[mkChunk 56 (CVal 8 (SOff 32 0)); mkChunk 48 (CVal 8 (SOff 33 0)); mkChunk 40 (CVal 8 (SOff 34 0));
mkChunk 32 (CVal 8 (SOff 35 0)); mkChunk 24 (CVal 8 (SOff 36 0)); mkChunk 16 (CVal 8 (SOff 37 0));
mkChunk 8 (CVal 8 (SOff 38 0))] ;
YP09.mkRegion (Some 8%nat) 0 16 0 0 [mkChunk 0 (CVal 8 (SOff 40 0)); mkChunk 8 (CVal 8 (SOff 39 0))] ]
None
(mkFacts [ (2%nat, mkAF (CEIL_MIN + ALLOC_STACK) (2^63) 4); (8%nat, mkAF CEIL_MIN (2^63) 3) ] [] []).
Definition ss_frees_c : sstate := Eval vm_compute in ss_frees.
Lemma rfc_frees_x :
forall STK sp0 FP L A mem md Lc Ac mdc (regs0 regs1 : bvmap 5 word) (mem1 : word -> option byte)
(Bb lpb : list (Z * Z)) (dst img N lp palsz : Z) (bq : rbound),
journal ubs0_msyms MR STK sp0 FP L A mem md Lc Ac mem1 mdc ->
(forall b, In b (blocks L A) -> In b Bb) ->
Permutation (blocks Lc Ac) ((img, N) :: lpb ++ Bb) ->
~ In (img, N) (blocks L A) -> 0 < N ->
((lp = 0 /\ lpb = []) \/ (exists lpa, lpb = [(lpa, palsz)] /\ Z_to_bv 64 lpa = Z_to_bv 64 lp /\ (In (lpa, palsz) (blocks L A) -> palsz <= 0) /\ 0 <= palsz)) ->
0 <= lp < 2 ^ 64 ->
YK0s.ret_ok (getr regs0 1) -> getr regs0 4 = Z_to_bv 64 (ms_tp ubs0_msyms) ->
spZ regs0 mod 16 = 0 -> sp0 - STK <= spZ regs0 - RFC_DEPTH -> spZ regs0 <= sp0 -> sp0 < 2 ^ 63 ->
spZ regs0 <= dst -> dst + 32 <= sp0 -> dst mod 8 = 0 ->
getr regs1 2 = Z_to_bv 64 (spZ regs0 - RFC_FRAME) -> getr regs1 3 = getr regs0 3 -> getr regs1 4 = getr regs0 4 ->
getr regs1 8 = Z_to_bv 64 dst ->
getr regs1 9 = Z_to_bv 64 (2 ^ 64 - 1) ->
getr regs1 22 = getr regs0 22 -> getr regs1 23 = getr regs0 23 ->
getr regs1 24 = getr regs0 24 -> getr regs1 25 = getr regs0 25 -> getr regs1 26 = getr regs0 26 -> getr regs1 27 = getr regs0 27 ->
word_mem ubs0segs mem1 (spZ regs0 - 8) (bv_unsigned (getr regs0 1)) ->
word_mem ubs0segs mem1 (spZ regs0 - 16) (bv_unsigned (getr regs0 8)) ->
word_mem ubs0segs mem1 (spZ regs0 - 24) (bv_unsigned (getr regs0 9)) ->
word_mem ubs0segs mem1 (spZ regs0 - 32) (bv_unsigned (getr regs0 18)) ->
word_mem ubs0segs mem1 (spZ regs0 - 40) (bv_unsigned (getr regs0 19)) ->
word_mem ubs0segs mem1 (spZ regs0 - 48) (bv_unsigned (getr regs0 20)) ->
word_mem ubs0segs mem1 (spZ regs0 - 56) (bv_unsigned (getr regs0 21)) ->
word_mem ubs0segs mem1 dst lp -> word_mem ubs0segs mem1 (dst + 8) img ->
res_ok Ac bq ->
SR ubs0segs (mkCfg (mkst regs1 (Z_to_bv 64 FREESPC) mem1 (seg_rom ubs0segs)) mdc)
(fun c' => exists L2 A2 regs2 mem2 md2,
c' = mkCfg (mkst regs2 (getr regs0 1) mem2 (seg_rom ubs0segs)) md2 /\
journal ubs0_msyms MR STK sp0 FP L A mem md L2 A2 mem2 md2 /\
st_init_done A2 = true /\
regs_preserved regs0 regs2 /\
getr regs2 10 = Z_to_bv 64 0 /\
(forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (spZ regs0 - RFC_DEPTH <= a < spZ regs0) ->
mbyte ubs0segs mem2 a = mbyte ubs0segs mem1 a) /\
(forall b m i, In (b, m) Bb -> 0 <= i < m -> mbyte ubs0segs mem2 (b + i) = mbyte ubs0segs mem1 (b + i)) /\
Permutation (blocks L2 A2) Bb /\
res_ok A2 (rb_free bq N)).
Proof using IMG LAWS.
intros STK sp0 FP L A mem md Lc Ac mdc regs0 regs1 mem1 Bb lpb dst img N lp palsz bq
HJ Hbase HBc Himgold HN Hlp Hlp64 Hra0 Htp0 Hal16 Hwlo Hwhi H63 Hdst1 Hdst2 Hdst8
G2 G3 G4 G8 G9 G22 G23 G24 G25 G26 G27
W1 W8 W9 W18 W19 W20 W21 Wl Wi HRq.
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HASv : ALLOC_STACK = 8192) by reflexivity.
assert (HFRv : RFC_FRAME = 64) by reflexivity. assert (HDPv : RFC_DEPTH = 8256) by reflexivity.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HH.
pose proof HJ as (_ & _ & _ & _ & _ & (Hsp0al & Hstk0 & Hceil & Hsp063 & Hstw) & _).
set (sp := spZ regs0) in *.
assert (Hspm : (sp - RFC_FRAME) mod 16 = 0).
{ rewrite HFRv. replace (sp - 64) with (sp + (-4) * 16) by lia. rewrite Z.mod_add by lia. exact Hal16. }
assert (Himg : In (img, N) (blocks Lc Ac)) by (eapply Permutation_in; [apply Permutation_sym; exact HBc | left; reflexivity]).
destruct (heap_blocks_range _ _ LAWS Lc Ac mem1 mdc img N HH Himg HN) as (Hi0 & Hi1 & _).
assert (Hlpr : 0 <= lp < 2 ^ 64) by exact Hlp64.
set (extra := [getr regs0 1; getr regs0 8; getr regs0 9; getr regs0 18; getr regs0 19; getr regs0 20; getr regs0 21; Z_to_bv 64 img; Z_to_bv 64 lp]).
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew (Ereg regs1 extra) n = getr regs1 rr) by (intros; apply ew_Ereg_nat; assumption).
assert (HX : forall n j v, (n = 32 + j)%nat -> nth_error extra j = Some v -> ew (Ereg regs1 extra) n = v).
{ intros n j v -> Hj. rewrite ew_Ereg_extra. apply nth_error_nth. exact Hj. }
assert (HE2 : bv_unsigned (ew (Ereg regs1 extra) 2) = sp - RFC_FRAME) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; lia).
assert (HE8 : bv_unsigned (ew (Ereg regs1 extra) 8) = dst) by (rewrite (HE 8%nat 8%bv eq_refl), G8; apply unsigned_lit_small; lia).
assert (HS : st_ok ubs0segs (Ereg regs1 extra) ss_frees_c (mkst regs1 (Z_to_bv 64 FREESPC) mem1 (seg_rom ubs0segs))).
{ change ss_frees_c with ss_frees. unfold ss_frees. apply entry_st_ok_full.
- apply regs_ok_pin; [apply regs_ok_Ereg | intros H0; discriminate H0 |]. cbn [sv_denot]. exact G9.
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor]].
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HE2.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply (journal_stack_w _ _ _ _ _ _ _ _ _ _ _ _ _ HJ). lia. }
assert (CK : forall off j (w : word) (W : word_mem ubs0segs mem1 (sp - RFC_FRAME + off) (bv_unsigned w)),
nth_error extra j = Some w ->
chunk_ok ubs0segs (Ereg regs1 extra) mem1 (sp - RFC_FRAME) (mkChunk off (CVal 8 (SOff (32 + j) 0)))).
{ intros off j w W Hj. eapply (chunk_ok_val _ _ _ _ _ _ _ (bv_unsigned w)); [| pose proof (bv_unsigned_in_range 64 w) as Rw; change (bv_modulus 64) with (2 ^ 64) in Rw; cbn; lia | cbn; lia | apply val_mem_word_mem; exact W].
cbn [sv_denot]. rewrite Z.add_0_r, (HX (32 + j)%nat j w eq_refl Hj), Z_to_bv_bv_unsigned. reflexivity. }
repeat (apply Forall_cons; [ first [ eapply (CK 56 0%nat); [replace (sp - RFC_FRAME + 56) with (sp - 8) by lia; exact W1 | reflexivity]
| eapply (CK 48 1%nat); [replace (sp - RFC_FRAME + 48) with (sp - 16) by lia; exact W8 | reflexivity]
| eapply (CK 40 2%nat); [replace (sp - RFC_FRAME + 40) with (sp - 24) by lia; exact W9 | reflexivity]
| eapply (CK 32 3%nat); [replace (sp - RFC_FRAME + 32) with (sp - 32) by lia; exact W18 | reflexivity]
| eapply (CK 24 4%nat); [replace (sp - RFC_FRAME + 24) with (sp - 40) by lia; exact W19 | reflexivity]
| eapply (CK 16 5%nat); [replace (sp - RFC_FRAME + 16) with (sp - 48) by lia; exact W20 | reflexivity]
| eapply (CK 8 6%nat); [replace (sp - RFC_FRAME + 8) with (sp - 56) by lia; exact W21 | reflexivity] ] | ]).
apply Forall_nil.
+
unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HE8.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. lia. }
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ lp); [cbn [sv_denot]; rewrite Z.add_0_r, (HX 40%nat 8%nat _ eq_refl eq_refl), Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | rewrite Z.add_0_r; apply val_mem_word_mem; exact Wl]. }
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ img); [cbn [sv_denot]; rewrite Z.add_0_r, (HX 39%nat 7%nat _ eq_refl eq_refl), Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact Wi]. }
apply Forall_nil.
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val].
rewrite HE2, HE8. repeat split; lia.
- split; [| split; constructor].
cbn [atoms_ok f_atoms]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite HE2, HE8.
change (2 ^ 4) with 16. change (2 ^ 3) with 8.
repeat split; try lia; assumption. }
change mem1 with (ms_mem (mkst regs1 (Z_to_bv 64 FREESPC) mem1 (seg_rom ubs0segs))) in HJ.
jrun_to LAWS ubs0tbl_ok HS HJ ubs0_A_free.
{ eapply wr_ok_cons_win; [reflexivity | exact HE2 | cbn [r_wlo r_whi]; intros _; lia |].
eapply wr_ok_cons_win; [reflexivity | exact HE8 | cbn [r_wlo r_whi]; intros Hw; lia |]. apply wr_ok_nil. }
jreg HS (10%bv:reg) as F10. rewrite (HX 39%nat 7%nat _ eq_refl eq_refl) in F10.
jreg HS (2%bv:reg) as F2. rewrite (HE 2%nat 2%bv eq_refl), G2 in F2.
jreg HS (4%bv:reg) as F4. rewrite (HE 4%nat 4%bv eq_refl), G4, Htp0 in F4.
jreg HS (1%bv:reg) as F1.
eapply SR_bind.
{ eapply (jfree_at_res API IMG) with (a := img) (n := N) (spc := sp - RFC_FRAME);
[ exact HS | reflexivity | reflexivity | exact HJ | exact Himg | exact HRq | exact F10
| exact F2 | lia | exact Hspm | lia | lia | exact F4 | exact F1 | apply ret_ok_even; vm_compute; reflexivity
| intros Hin; exfalso; exact (Himgold Hin) ]. }
intros c' (L3 & A3 & regs3 & mem3 & md3 & -> & HJ3 & HP3 & Hrm3 & Hkeep3 & Hhi3 & Hid3 & HR3). clear HJ.
change (ms_segs ubs0_msyms) with ubs0segs in Hkeep3, Hhi3.
assert (HB3 : Permutation (blocks L3 A3) (lpb ++ Bb)) by (eapply perm_after_rm1; [exact HBc | exact Hrm3]).
jafter_call2 HS 41%nat regs3 mem3 HP3 0 [0%nat] HS2.
match type of HS2 with ?P -> _ => assert (HK : P); [|specialize (HS2 HK)] end.
{ constructor; [|constructor; [|constructor]].
- eapply (region_kept_stack ubs0segs _ _ _ 2); [exact HE2 | exact Hhi3 | lia | lia | lia | cbn; lia | cbn; lia].
- eapply (region_kept_stack ubs0segs _ _ _ 8); [exact HE8 | exact Hhi3 | lia | lia | lia | cbn; lia | cbn; lia]. }
clear HS. rename HS2 into HS.
jrun_to LAWS ubs0tbl_ok HS HJ3 ubs0_A_free.
{ eapply wr_ok_cons_win; [reflexivity | ew_havoc; exact HE2 | cbn [r_wlo r_whi]; intros _; lia |].
eapply wr_ok_cons_win; [reflexivity | ew_havoc; exact HE8 | cbn [r_wlo r_whi]; intros Hw; lia |]. apply wr_ok_nil. }
jreg HS (10%bv:reg) as K10. rewrite (HX 40%nat 8%nat _ eq_refl eq_refl) in K10.
jreg HS (2%bv:reg) as K2. rewrite (HE 2%nat 2%bv eq_refl), G2 in K2.
jreg HS (4%bv:reg) as K4. rewrite (HE 4%nat 4%bv eq_refl), G4, Htp0 in K4.
jreg HS (1%bv:reg) as K1.
lazymatch goal with |- SR _ (mkCfg ?msq ?mdq) _ =>
assert (STEP : SR ubs0segs (mkCfg msq mdq)
(fun c' => exists L4 A4 regs4 mem4 md4,
c' = mkCfg (mkst regs4 (Z_to_bv 64 RA_FREE2) mem4 (seg_rom ubs0segs)) md4 /\
journal ubs0_msyms MR STK sp0 FP L A mem md L4 A4 mem4 md4 /\ st_init_done A4 = true /\
regs_preserved (ms_regs msq) regs4 /\ Permutation (blocks L4 A4) Bb /\
(forall b m i, In (b, m) (blocks L4 A4) -> 0 <= i < m -> mbyte ubs0segs mem4 (b + i) = mbyte ubs0segs (ms_mem msq) (b + i)) /\
(forall x, alloc_ceiling <= x < 2 ^ 64 -> ~ (sp - RFC_FRAME - ALLOC_STACK <= x < sp - RFC_FRAME) ->
mbyte ubs0segs mem4 x = mbyte ubs0segs (ms_mem msq) x /\ (writable_at ubs0segs (ms_mem msq) x <-> writable_at ubs0segs mem4 x)) /\
res_ok A4 (rb_free bq N)))
end.
{ destruct Hlp as [[-> ->] | (lpa & -> & Hbv & Hnot & Hpz)].
-
destruct (heap_model _ _ LAWS _ _ _ _ (proj1 HJ3)) as (Hh3 & Hl3 & _).
eapply SR_mono; [eapply (jfree_null _ (aa_free_null API)); [exact HS | reflexivity | reflexivity | exact Hh3 | exact Hl3 | exact K10 | exact K1 | apply ret_ok_even; vm_compute; reflexivity] |].
intros c' ->. lazymatch goal with |- context [mkst (ms_regs ?m0) _ (ms_mem _) _] => exists L3, A3, (ms_regs m0), (ms_mem m0), md3 end.
split; [reflexivity|]. split; [exact HJ3|]. split; [exact Hid3|]. split; [intros rr _; reflexivity|].
split; [exact HB3|]. split; [intros; reflexivity|]. split; [intros x _ _; split; [reflexivity | tauto] | exact HR3].
-
assert (Hlp3 : In (lpa, palsz) (blocks L3 A3)) by (eapply Permutation_in; [apply Permutation_sym; exact HB3 | left; reflexivity]).
eapply SR_mono.
{ eapply (jfree_at_res API IMG) with (a := lpa) (n := palsz) (spc := sp - RFC_FRAME);
[ exact HS | reflexivity | reflexivity | exact HJ3 | exact Hlp3 | exact HR3 | rewrite Hbv; exact K10
| exact K2 | lia | exact Hspm | lia | lia | exact K4 | exact K1 | apply ret_ok_even; vm_compute; reflexivity
| intros Hin i Hi; exfalso; pose proof (Hnot Hin); lia ]. }
intros c' (L4 & A4 & regs4 & mem4 & md4 & -> & HJ4 & HP4 & Hrm4 & Hkeep4 & Hhi4 & Hid4 & HR4).
exists L4, A4, regs4, mem4, md4. split; [reflexivity|]. split; [exact HJ4|]. split; [exact Hid4|]. split; [exact HP4|].
split; [eapply perm_after_rm1; [exact HB3 | exact Hrm4]|]. split; [exact Hkeep4 | split; [exact Hhi4 | eapply res_ok_mono; [apply rb_free_le | exact HR4]]]. }
eapply SR_bind; [exact STEP|]. clear STEP.
intros c' (L4 & A4 & regs4 & mem4 & md4 & -> & HJ4 & Hid4 & HP4 & HB4 & Kkeep4 & Hhi4 & HR4'). rename Kkeep4 into Hkeep4.
clear HK. jafter_call2 HS 58%nat regs4 mem4 HP4 0 (@nil nat) HS2.
match type of HS2 with ?P -> _ => assert (HK : P); [|specialize (HS2 HK)] end.
{ constructor; [|constructor].
eapply (region_kept_stack ubs0segs _ _ _ 2); [ew_havoc; exact HE2 | exact Hhi4 | lia | lia | lia | cbn; lia | cbn; lia]. }
clear HS. rename HS2 into HS.
jrun LAWS ubs0tbl_ok HS HJ4.
{ eapply wr_ok_cons_win; [reflexivity | ew_havoc; exact HE2 | cbn [r_wlo r_whi]; intros _; lia |]. apply wr_ok_nil. }
eapply (SR_ret_at ubs0segs ubs0tbl); [exact ubs0tbl_ok | | | exact HS | reflexivity | vm_compute; reflexivity |].
{ exact (proj1 (heap_model _ _ LAWS _ _ _ _ (proj1 HJ4))). }
{ exact (proj1 (proj2 (heap_model _ _ LAWS _ _ _ _ (proj1 HJ4)))). }
lazymatch type of HS with st_ok _ ?Ef ?ssf ?msf =>
pose proof (st_ok_reg ubs0segs Ef ssf msf 1%bv HS) as Q1; eval_sr_get_in Q1; cbn [sv_denot] in Q1;
repeat (rewrite ew_havoc_old in Q1; [|cbv; lia]); rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned in Q1;
rewrite (HX 32%nat 0%nat _ eq_refl eq_refl) in Q1;
exists L4, A4, (ms_regs msf), (ms_mem msf), md4;
split; [ cbn [ms_regs mkst]; rewrite Q1, Hra0; reflexivity |];
split; [ exact HJ4 |];
split; [ exact Hid4 |];
split; [ apply regs_preserved_intro;
[ reg_final HS HX HE HE2 (2%bv:reg) | reg_final HS HX HE HE2 (3%bv:reg) | reg_final HS HX HE HE2 (4%bv:reg) | reg_final HS HX HE HE2 (8%bv:reg)
| reg_final HS HX HE HE2 (9%bv:reg) | reg_final HS HX HE HE2 (18%bv:reg) | reg_final HS HX HE HE2 (19%bv:reg) | reg_final HS HX HE HE2 (20%bv:reg)
| reg_final HS HX HE HE2 (21%bv:reg) | reg_final HS HX HE HE2 (22%bv:reg) | reg_final HS HX HE HE2 (23%bv:reg) | reg_final HS HX HE HE2 (24%bv:reg)
| reg_final HS HX HE HE2 (25%bv:reg) | reg_final HS HX HE HE2 (26%bv:reg) | reg_final HS HX HE HE2 (27%bv:reg) ] |];
split; [ pose proof (st_ok_reg ubs0segs Ef ssf msf 10%bv HS) as Q10; eval_sr_get_in Q10; cbn [sv_denot] in Q10; cbn [ms_regs mkst]; rewrite Q10; reflexivity |];
split; [| split; [| split; [exact HB4 | exact HR4'] ]]
end.
-   intros a Ha Hna. cbn [ms_mem mkst] in *.
mb_frame HF1; try (rewrite ?HE2, ?HE8; lia).
rewrite (proj1 (Hhi4 a Ha ltac:(lia))).
mb_frame HF0; try (rewrite ?HE2, ?HE8; lia).
rewrite (proj1 (Hhi3 a Ha ltac:(lia))).
mb_frame HF; try (rewrite ?HE2, ?HE8; lia). reflexivity.
-   intros b m i Hb Hi. cbn [ms_mem mkst] in *.
assert (Hb4 : In (b, m) (blocks L4 A4)) by (eapply Permutation_in; [apply Permutation_sym; exact HB4 | exact Hb]).
assert (Hb3 : In (b, m) (blocks L3 A3)) by (eapply Permutation_in; [apply Permutation_sym; exact HB3 | apply in_app_iff; right; exact Hb]).
assert (Hbc : In (b, m) (blocks Lc Ac)) by (eapply Permutation_in; [apply Permutation_sym; exact HBc | right; apply in_app_iff; right; exact Hb]).
destruct (heap_blocks _ _ LAWS Lc Ac _ mdc b m i HH Hbc Hi) as (_ & Hb0 & Hb1 & _).
mb_frame HF1; try (rewrite ?HE2, ?HE8; lia).
rewrite (Hkeep4 b m i Hb4 Hi).
mb_frame HF0; try (rewrite ?HE2, ?HE8; lia).
rewrite (Hkeep3 b m i Hb3 Hi).
mb_frame HF; try (rewrite ?HE2, ?HE8; lia). reflexivity.
Qed.
Definition ss_img (r : Z) : sstate :=
mkSS IMGPC (sr_set sr_atoms 20%bv (SLit r))
[ YP09.mkRegion (Some 2%nat) 0 RFC_FRAME 0 RFC_FRAME
[mkChunk 56 (CVal 8 (SOff 32 0)); mkChunk 48 (CVal 8 (SOff 33 0)); mkChunk 40 (CVal 8 (SOff 34 0)); mkChunk 32 (CVal 8 (SOff 35 0));
mkChunk 24 (CVal 8 (SOff 36 0)); mkChunk 16 (CVal 8 (SOff 37 0)); mkChunk 8 (CVal 8 (SOff 38 0))] ;
YP09.mkRegion (Some 18%nat) 0 24 16 24 [mkChunk 0 (CVal 8 (SOff 39 0)); mkChunk 8 (CVal 8 (SOff 40 0)); mkChunk 16 (CVal 8 (SOff 41 0))] ;
YP09.mkRegion (Some 8%nat) 0 16 8 16 [mkChunk 0 (CVal 8 (SOff 42 0))] ]
None
(mkFacts [ (2%nat, mkAF (CEIL_MIN + ALLOC_STACK) (2^63) 4); (18%nat, mkAF CEIL_MIN (2^63) 3);
(8%nat, mkAF CEIL_MIN (2^63) 3); (9%nat, mkAF 1 100000000 0);
(39%nat, mkAF 4096 CEIL_MAX 0); (40%nat, mkAF 1 CEIL_MAX 0);
(41%nat, mkAF 0 CEIL_MAX 0) ] [] []).
Definition img_post_x (regs0 : bvmap 5 word) (STK sp0 : Z) (FP : list (Z * Z)) L A mem md
(Bb : list (Z * Z)) (lpb : list (Z * Z)) (st dst N nb cur lp r : Z) (mem1 : word -> option byte)
(pdata : Z) (PAYLOAD : list Z) (bq : rbound)
(c' : config) : Prop :=
exists L2 A2 regs2 mem2 md2 (res cur2 img : Z),
c' = mkCfg (mkst regs2 (getr regs0 1) mem2 (seg_rom ubs0segs)) md2 /\
journal ubs0_msyms MR STK sp0 FP L A mem md L2 A2 mem2 md2 /\
st_init_done A2 = true /\
regs_preserved regs0 regs2 /\
getr regs2 10 = Z_to_bv 64 res /\
(forall a, alloc_ceiling <= a < 2 ^ 64 ->
~ (spZ regs0 - RFC_DEPTH <= a < spZ regs0) -> ~ (dst <= a < dst + 16) -> ~ (st + 16 <= a < st + 24) ->
mbyte ubs0segs mem2 a = mbyte ubs0segs mem1 a) /\
(forall b m i, In (b, m) Bb -> 0 <= i < m -> mbyte ubs0segs mem2 (b + i) = mbyte ubs0segs mem1 (b + i)) /\
word_mem ubs0segs mem2 (st + 16) cur2 /\ cur <= cur2 <= nb /\
((res = 0 /\ (exists leak, Permutation (blocks L2 A2) (leak ++ Bb)) /\ (r <> 0 \/ nb < cur + N) /\
res_ok A2 (rb_free (rb_malloc bq N) N)) \/
(res = 1 /\ r = 0 /\ word_mem ubs0segs mem2 dst lp /\ word_mem ubs0segs mem2 (dst + 8) img /\
Permutation (blocks L2 A2) ((img, N) :: lpb ++ Bb) /\
cur + N <= nb /\ cur2 = cur + N /\
(forall b m i, In (b, m) lpb -> 0 <= i < m -> mbyte ubs0segs mem2 (b + i) = mbyte ubs0segs mem1 (b + i)) /\
garr8 ubs0segs mem2 img (firstn (Z.to_nat N) (skipn (Z.to_nat cur) PAYLOAD)) /\
res_ok A2 (rb_malloc bq N))).
Lemma rfc_img_x : forall r : Z, (r = 0 \/ r = 2 ^ 64 - 1) ->
forall STK sp0 FP L A mem md Lc Ac mdc (regs0 regs1 : bvmap 5 word) (mem1 : word -> option byte)
(Bb lpb : list (Z * Z)) (st dst N pdata nb cur lp palsz : Z) (PAYLOAD : list Z) (bq : rbound),
journal ubs0_msyms MR STK sp0 FP L A mem md Lc Ac mem1 mdc -> st_init_done Ac = true ->
(forall b, In b (blocks L A) -> In b Bb) ->
Permutation (blocks Lc Ac) (lpb ++ Bb) ->
In (pdata, nb) Bb ->
((lp = 0 /\ lpb = []) \/ (exists lpa, lpb = [(lpa, palsz)] /\ Z_to_bv 64 lpa = Z_to_bv 64 lp /\ (In (lpa, palsz) (blocks L A) -> palsz <= 0) /\ 0 <= palsz)) ->
0 <= lp < 2 ^ 64 ->
YK0s.ret_ok (getr regs0 1) -> getr regs0 4 = Z_to_bv 64 (ms_tp ubs0_msyms) ->
spZ regs0 mod 16 = 0 -> sp0 - STK <= spZ regs0 - RFC_DEPTH -> spZ regs0 <= sp0 ->
spZ regs0 <= st -> st + 24 <= sp0 -> spZ regs0 <= dst -> dst + 32 <= sp0 -> (st + 24 <= dst \/ dst + 32 <= st) ->
st mod 8 = 0 -> dst mod 8 = 0 -> sp0 < 2 ^ 63 ->
1 <= N <= 100000000 -> 0 <= cur <= nb -> 0 < nb ->
getr regs1 2 = Z_to_bv 64 (spZ regs0 - RFC_FRAME) -> getr regs1 3 = getr regs0 3 -> getr regs1 4 = getr regs0 4 ->
getr regs1 8 = Z_to_bv 64 dst -> getr regs1 9 = Z_to_bv 64 N -> getr regs1 18 = Z_to_bv 64 st ->
getr regs1 20 = Z_to_bv 64 r ->
getr regs1 22 = getr regs0 22 -> getr regs1 23 = getr regs0 23 ->
getr regs1 24 = getr regs0 24 -> getr regs1 25 = getr regs0 25 -> getr regs1 26 = getr regs0 26 -> getr regs1 27 = getr regs0 27 ->
word_mem ubs0segs mem1 (spZ regs0 - 8) (bv_unsigned (getr regs0 1)) ->
word_mem ubs0segs mem1 (spZ regs0 - 16) (bv_unsigned (getr regs0 8)) ->
word_mem ubs0segs mem1 (spZ regs0 - 24) (bv_unsigned (getr regs0 9)) ->
word_mem ubs0segs mem1 (spZ regs0 - 32) (bv_unsigned (getr regs0 18)) ->
word_mem ubs0segs mem1 (spZ regs0 - 40) (bv_unsigned (getr regs0 19)) ->
word_mem ubs0segs mem1 (spZ regs0 - 48) (bv_unsigned (getr regs0 20)) ->
word_mem ubs0segs mem1 (spZ regs0 - 56) (bv_unsigned (getr regs0 21)) ->
word_mem ubs0segs mem1 st pdata -> word_mem ubs0segs mem1 (st + 8) nb -> word_mem ubs0segs mem1 (st + 16) cur -> word_mem ubs0segs mem1 dst lp ->
garr8 ubs0segs mem1 pdata PAYLOAD -> Z.of_nat (length PAYLOAD) = nb ->
res_ok Ac bq -> room bq N ->
SR ubs0segs (mkCfg (mkst regs1 (Z_to_bv 64 IMGPC) mem1 (seg_rom ubs0segs)) mdc)
(img_post_x regs0 STK sp0 FP L A mem md Bb lpb st dst N nb cur lp r mem1 pdata PAYLOAD bq).
Proof using IMG.
intros r Hr STK sp0 FP L A mem md Lc Ac mdc regs0 regs1 mem1 Bb lpb st dst N pdata nb cur lp palsz PAYLOAD bq
HJ Hid Hbase HBc Hpd Hlp Hlp64 Hra0 Htp0 Hal16 Hwlo Hwhi Hst1 Hst2 Hdst1 Hdst2 Hsd Hst8 Hdst8 H63 HN Hcur Hnb
G2 G3 G4 G8 G9 G18 G20 G22 G23 G24 G25 G26 G27
W1 W8 W9 W18 W19 W20 W21 Wp Wn Wc Wl HPL HPLn HRq HRm.
apply hideP_i in Hsd. apply hideP_i in Hr. apply hideP_i in Hlp.
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HASv : ALLOC_STACK = 8192) by reflexivity.
assert (HFRv : RFC_FRAME = 64) by reflexivity. assert (HDPv : RFC_DEPTH = 8256) by reflexivity.
assert (HRDv : RD_FRAME = 32) by reflexivity.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HH.
pose proof HJ as (_ & _ & _ & _ & _ & (Hsp0al & Hstk0 & Hceil & Hsp063 & Hstw) & _).
assert (Hpdc : In (pdata, nb) (blocks Lc Ac)) by (eapply Permutation_in; [apply Permutation_sym; exact HBc | apply in_app_iff; right; exact Hpd]).
destruct (heap_blocks_range _ _ LAWS Lc Ac mem1 mdc pdata nb HH Hpdc ltac:(lia)) as (Hp0 & Hp1 & _).
set (sp := spZ regs0) in *.
assert (Hspm : (sp - RFC_FRAME) mod 16 = 0).
{ rewrite HFRv. replace (sp - 64) with (sp + (-4) * 16) by lia. rewrite Z.mod_add by lia. exact Hal16. }
set (extra := [getr regs0 1; getr regs0 8; getr regs0 9; getr regs0 18; getr regs0 19; getr regs0 20; getr regs0 21;
Z_to_bv 64 pdata; Z_to_bv 64 nb; Z_to_bv 64 cur; Z_to_bv 64 lp]).
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew (Ereg regs1 extra) n = getr regs1 rr) by (intros; apply ew_Ereg_nat; assumption).
assert (HX : forall n j v, (n = 32 + j)%nat -> nth_error extra j = Some v -> ew (Ereg regs1 extra) n = v).
{ intros n j v -> Hj. rewrite ew_Ereg_extra. apply nth_error_nth. exact Hj. }
assert (HE2 : bv_unsigned (ew (Ereg regs1 extra) 2) = sp - RFC_FRAME) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; lia).
assert (HE18 : bv_unsigned (ew (Ereg regs1 extra) 18) = st) by (rewrite (HE 18%nat 18%bv eq_refl), G18; apply unsigned_lit_small; lia).
assert (HE8 : bv_unsigned (ew (Ereg regs1 extra) 8) = dst) by (rewrite (HE 8%nat 8%bv eq_refl), G8; apply unsigned_lit_small; lia).
assert (HS : st_ok ubs0segs (Ereg regs1 extra) (ss_img r) (mkst regs1 (Z_to_bv 64 IMGPC) mem1 (seg_rom ubs0segs))).
{ unfold ss_img. apply entry_st_ok_full.
- apply regs_ok_pin; [apply regs_ok_Ereg | intros H0; discriminate H0 |]. cbn [sv_denot]. exact G20.
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor; [|constructor]]].
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val].
rewrite HE2.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply (journal_stack_w _ _ _ _ _ _ _ _ _ _ _ _ _ HJ). lia. }
assert (CK : forall off j (w : word) (W : word_mem ubs0segs mem1 (sp - RFC_FRAME + off) (bv_unsigned w)),
nth_error extra j = Some w ->
chunk_ok ubs0segs (Ereg regs1 extra) mem1 (sp - RFC_FRAME) (mkChunk off (CVal 8 (SOff (32 + j) 0)))).
{ intros off j w W Hj. eapply (chunk_ok_val _ _ _ _ _ _ _ (bv_unsigned w)); [| pose proof (bv_unsigned_in_range 64 w) as Rw; change (bv_modulus 64) with (2 ^ 64) in Rw; cbn; lia | cbn; lia | apply val_mem_word_mem; exact W].
cbn [sv_denot]. rewrite Z.add_0_r, (HX (32 + j)%nat j w eq_refl Hj), Z_to_bv_bv_unsigned. reflexivity. }
repeat (apply Forall_cons; [ first [ eapply (CK 56 0%nat); [replace (sp - RFC_FRAME + 56) with (sp - 8) by lia; exact W1 | reflexivity]
| eapply (CK 48 1%nat); [replace (sp - RFC_FRAME + 48) with (sp - 16) by lia; exact W8 | reflexivity]
| eapply (CK 40 2%nat); [replace (sp - RFC_FRAME + 40) with (sp - 24) by lia; exact W9 | reflexivity]
| eapply (CK 32 3%nat); [replace (sp - RFC_FRAME + 32) with (sp - 32) by lia; exact W18 | reflexivity]
| eapply (CK 24 4%nat); [replace (sp - RFC_FRAME + 24) with (sp - 40) by lia; exact W19 | reflexivity]
| eapply (CK 16 5%nat); [replace (sp - RFC_FRAME + 16) with (sp - 48) by lia; exact W20 | reflexivity]
| eapply (CK 8 6%nat); [replace (sp - RFC_FRAME + 8) with (sp - 56) by lia; exact W21 | reflexivity] ] | ]).
apply Forall_nil.
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val].
rewrite HE18.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply (journal_stack_w _ _ _ _ _ _ _ _ _ _ _ _ _ HJ). lia. }
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ pdata); [cbn [sv_denot]; rewrite Z.add_0_r, (HX 39%nat 7%nat _ eq_refl eq_refl), Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | rewrite Z.add_0_r; apply val_mem_word_mem; exact Wp]. }
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ nb); [cbn [sv_denot]; rewrite Z.add_0_r, (HX 40%nat 8%nat _ eq_refl eq_refl), Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact Wn]. }
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ cur); [cbn [sv_denot]; rewrite Z.add_0_r, (HX 41%nat 9%nat _ eq_refl eq_refl), Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact Wc]. }
apply Forall_nil.
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val].
rewrite HE8.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply (journal_stack_w _ _ _ _ _ _ _ _ _ _ _ _ _ HJ). lia. }
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ lp); [cbn [sv_denot]; rewrite Z.add_0_r, (HX 42%nat 10%nat _ eq_refl eq_refl), Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | rewrite Z.add_0_r; apply val_mem_word_mem; exact Wl]. }
apply Forall_nil.
- unfold hideP in Hsd. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val].
rewrite HE2, HE18, HE8. repeat split; lia.
- split; [| split; constructor].
cbn [atoms_ok f_atoms]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite HE2, HE18, HE8, (HE 9%nat 9%bv eq_refl), (HX 39%nat 7%nat _ eq_refl eq_refl), (HX 40%nat 8%nat _ eq_refl eq_refl),
(HX 41%nat 9%nat _ eq_refl eq_refl), G9, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 3) with 8. change (2 ^ 0) with 1.
rewrite ?Z.mod_1_r.
repeat split; try lia; assumption. }
change mem1 with (ms_mem (mkst regs1 (Z_to_bv 64 IMGPC) mem1 (seg_rom ubs0segs))) in HJ.
jrun_to LAWS ubs0tbl_ok HS HJ ubs0_A_malloc.
{ wr3_tac_with HE2 HE18 HE8 ltac:(clear - Hwlo Hwhi Hst1 Hst2 Hdst1 Hdst2 HFRv HDPv HASv; lia). }
cbn [ms_mem mkst] in HF. rename HF into HFa.
jreg HS (10%bv:reg) as Hr10. rewrite (HE 9%nat 9%bv eq_refl), G9 in Hr10.
jreg HS (2%bv:reg) as Hr2. rewrite (HE 2%nat 2%bv eq_refl), G2 in Hr2.
jreg HS (4%bv:reg) as Hr4. rewrite (HE 4%nat 4%bv eq_refl), G4, Htp0 in Hr4.
jreg HS (1%bv:reg) as Hr1.
eapply SR_bind.
{ eapply (jmalloc_at_res API IMG) with (n := N) (spc := sp - RFC_FRAME);
[ exact HS | reflexivity | reflexivity | exact HJ | exact Hid | exact Hr10 | exact HRq | exact HRm
| exact Hr2 | lia | exact Hspm | lia | lia | exact Hr4 | exact Hr1 | apply ret_ok_even; vm_compute; reflexivity ]. }
intros c' (L2 & A2 & regs2 & mem2 & md2 & res & -> & HJ2 & Hid2 & HP2 & Hres10 & Hres & Hkeep2 & Hhi2 & HR2). clear HJ.
change (ms_segs ubs0_msyms) with ubs0segs in Hkeep2, Hhi2.
jafter_call2 HS 43%nat regs2 mem2 HP2 0 [0%nat; 1%nat] HS2.
match type of HS2 with ?P -> _ => assert (HK : P); [|specialize (HS2 HK)] end.
{ constructor; [|constructor; [|constructor; [|constructor]]].
- eapply (region_kept_stack ubs0segs _ _ _ 2); [exact HE2 | exact Hhi2 | lia | lia | lia | cbn; lia | cbn; lia].
- eapply (region_kept_stack ubs0segs _ _ _ 18); [exact HE18 | exact Hhi2 | lia | lia | lia | cbn; lia | cbn; lia].
- eapply (region_kept_stack ubs0segs _ _ _ 8); [exact HE8 | exact Hhi2 | lia | lia | lia | cbn; lia | cbn; lia]. }
clear HS. rename HS2 into HS.
jreg HS (10%bv:reg) as Hq10. cbn [ms_regs mkst] in Hq10. rewrite Hres10 in Hq10. symmetry in Hq10.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HH2.
destruct Hres as (Hnz & Hres16 & (b1 & b2 & Hbl2 & Hblc) & Hwr).
assert (Himg2 : In (res, N) (blocks L2 A2)) by (rewrite Hbl2; apply in_app_iff; right; left; reflexivity).
destruct (heap_blocks_range _ _ LAWS L2 A2 mem2 md2 res N HH2 Himg2 ltac:(lia)) as (Rr0 & Rr1 & _).
assert (HBnow : Permutation (blocks L2 A2) ((res, N) :: lpb ++ Bb)).
{ rewrite Hbl2. eapply Permutation_trans; [apply Permutation_sym; apply Permutation_middle|]. apply perm_skip. rewrite <- Hblc. exact HBc. }
assert (Hfresh : ~ In (res, N) (blocks L A)).
{ intros Hin. apply (fresh_not_in API L2 A2 mem2 md2 b1 b2 res N HH2 Hbl2 ltac:(lia)). rewrite <- Hblc.
eapply Permutation_in; [apply Permutation_sym; exact HBc|]. apply in_app_iff. right. apply Hbase. exact Hin. }
assert (HPLk : forall mx : word -> option byte,
(forall b m i, In (b, m) (blocks Lc Ac) -> 0 <= i < m -> mbyte ubs0segs mx (b + i) = mbyte ubs0segs mem1 (b + i)) ->
garr8 ubs0segs mx pdata PAYLOAD).
{ intros mx Hbk. eapply (garr8_frame ubs0segs); [exact HPL|]. intros a Ha. rewrite HPLn in Ha.
replace a with (pdata + (a - pdata)) by lia. apply (Hbk pdata nb (a - pdata) Hpdc). lia. }
jrun LAWS ubs0tbl_ok HS HJ2.
{ wr3_tac_with HE2 HE18 HE8 ltac:(clear - Hwlo Hwhi Hst1 Hst2 Hdst1 Hdst2 HFRv HDPv HASv; lia). }
cbn [ms_mem mkst] in HF. rename HF into HFb.
jbranch ubs0tbl HS.
{ exfalso. rewrite branch_eq_U, (U_atom _ 47 res), U_SLit in Hc by (first [exact Hq10 | lia]).
change (zcanon 0) with 0 in Hc. apply Z.eqb_eq in Hc. exact (Hnz Hc). }
clear Hc.
jrun_to LAWS ubs0tbl_ok HS HJ2 ubs0_A_readdata.
{ wr3_tac_with HE2 HE18 HE8 ltac:(clear - Hwlo Hwhi Hst1 Hst2 Hdst1 Hdst2 HFRv HDPv HASv; lia). }
cbn [ms_mem mkst] in HF. rename HF into HFc.
lazymatch type of HS with st_ok _ _ _ ?msr =>
assert (Wp_r : word_mem ubs0segs (ms_mem msr) st pdata)
by (rewrite <- (Z.add_0_r st); eapply (st_chunk_word _ _ _ 1%nat _ 18%nat 0 (SOff 39 0) st _ HS);
[reflexivity | reflexivity | cbv; auto 12 | ew_havocF; exact HE18
| cbn [sv_denot]; ew_havocF; rewrite Z.add_0_r, (HX 39%nat 7%nat _ eq_refl eq_refl), Z_to_bv_bv_unsigned; reflexivity | lia]);
assert (Wn_r : word_mem ubs0segs (ms_mem msr) (st + 8) nb)
by (eapply (st_chunk_word _ _ _ 1%nat _ 18%nat 8 (SOff 40 0) st _ HS);
[reflexivity | reflexivity | cbv; auto 12 | ew_havocF; exact HE18
| cbn [sv_denot]; ew_havocF; rewrite Z.add_0_r, (HX 40%nat 8%nat _ eq_refl eq_refl), Z_to_bv_bv_unsigned; reflexivity | lia]);
assert (Wc_r : word_mem ubs0segs (ms_mem msr) (st + 16) cur)
by (eapply (st_chunk_word _ _ _ 1%nat _ 18%nat 16 (SOff 41 0) st _ HS);
[reflexivity | reflexivity | cbv; auto 12 | ew_havocF; exact HE18
| cbn [sv_denot]; ew_havocF; rewrite Z.add_0_r, (HX 41%nat 9%nat _ eq_refl eq_refl), Z_to_bv_bv_unsigned; reflexivity | lia]);
assert (Hbk_r : forall b m i, In (b, m) (blocks Lc Ac) -> 0 <= i < m -> mbyte ubs0segs (ms_mem msr) (b + i) = mbyte ubs0segs mem1 (b + i))
by (intros b m i Hbc Hi;
destruct (heap_blocks _ _ LAWS Lc Ac mem1 mdc b m i HH Hbc Hi) as (_ & Hb0 & Hb1 & _);
mbfB HFc Hb0 Hb1 Hi Hac Hceil Hwlo Hst1 Hdst1 HFRv HDPv HASv HE2 HE8 HE18;
mbfB HFb Hb0 Hb1 Hi Hac Hceil Hwlo Hst1 Hdst1 HFRv HDPv HASv HE2 HE8 HE18;
rewrite (Hkeep2 b m i Hbc Hi);
mbfB HFa Hb0 Hb1 Hi Hac Hceil Hwlo Hst1 Hdst1 HFRv HDPv HASv HE2 HE8 HE18; reflexivity);
assert (Hfr_r : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp - RFC_DEPTH <= a < sp) -> ~ (dst <= a < dst + 16) -> ~ (st + 16 <= a < st + 24) ->
mbyte ubs0segs (ms_mem msr) a = mbyte ubs0segs mem1 a)
by (intros a Ha Hn1 Hn2 Hn3;
mbfA HFc Ha Hn1 Hn2 Hn3 Hac HFRv HDPv HASv HE2 HE8 HE18;
mbfA HFb Ha Hn1 Hn2 Hn3 Hac HFRv HDPv HASv HE2 HE8 HE18;
rewrite (proj1 (Hhi2 a Ha ltac:(clear - Ha Hn1 HFRv HDPv HASv; lia)));
mbfA HFa Ha Hn1 Hn2 Hn3 Hac HFRv HDPv HASv HE2 HE8 HE18; reflexivity)
end.
jreg HS (10%bv:reg) as M10. rewrite (HE 18%nat 18%bv eq_refl), G18 in M10.
jreg HS (11%bv:reg) as M11. rewrite Hq10 in M11.
jreg HS (12%bv:reg) as M12. rewrite (HE 9%nat 9%bv eq_refl), G9 in M12.
jreg HS (2%bv:reg) as M2. rewrite (HE 2%nat 2%bv eq_refl), G2 in M2.
jreg HS (1%bv:reg) as M1.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HH3.
assert (Hpd2 : In (pdata, nb) (blocks L2 A2)) by (eapply Permutation_in; [apply Permutation_sym; exact HBnow | right; apply in_app_iff; right; exact Hpd]).
eapply SR_bind.
{ eapply (jreaddata API IMG _ _ _ STK sp0 FP L A mem md L2 A2 md2 st res N pdata nb cur (sp - RFC_FRAME)).
- exact HS. - reflexivity. - reflexivity. - exact HJ2.
- exact M10. - exact M11. - exact M12. - exact M2.
- exact Hspm. - rewrite HRDv; lia. - lia. - exact H63.
- exact M1. - apply ret_ok_even; vm_compute; reflexivity.
- lia. - lia. - exact Hst8.
- exact Wp_r. - exact Wn_r. - exact Wc_r.
- lia. - lia. - lia. - lia. - lia. - intros; lia.
- intros j Hj. exact (proj1 (heap_blocks _ _ LAWS L2 A2 _ md2 pdata nb j HH3 Hpd2 Hj)).
- lia. - lia.
- intros i Hi. exact (proj1 (heap_blocks _ _ LAWS L2 A2 _ md2 res N i HH3 Himg2 Hi)).
- intros a Ha. replace a with (res + (a - res)) by lia. apply Hwr; [exact Himg2 | lia].
- intros a Ha. unfold wr_byte. left. lia.
- right. lia.
- left. rewrite HRDv. lia.
- intros _. left. rewrite HRDv. lia.
- intros _. left. lia.
- left. lia.
- intros _. destruct (heap_sep _ _ LAWS L2 A2 _ md2 b1 (res, N) b2 (pdata, nb) HH3 Hbl2 ltac:(rewrite <- Hblc; exact Hpdc)) as [H0|H0]; cbn [fst snd] in H0; lia. }
cbv beta. intros c' (regs3 & mem3 & -> & HJ3 & HP3 & Hout3 & Hgr3 & Hcase).
jafter_call2 HS 59%nat regs3 mem3 HP3 0 [1%nat] HS3.
match type of HS3 with ?P -> _ => assert (HK3 : P); [|specialize (HS3 HK3)] end.
{ unfold hideP in Hsd. constructor; [|constructor; [|constructor]].
- eapply region_kept_rd; [exact Hout3 | exact Hgr3 | ..]; cbn [r_base r_lo r_hi r_wlo r_whi base_val]; ew_havocF; rewrite ?HE2, ?HRDv; lia.
- eapply region_kept_rd; [exact Hout3 | exact Hgr3 | ..]; cbn [r_base r_lo r_hi r_wlo r_whi base_val]; ew_havocF; rewrite ?HE8, ?HRDv; lia. }
clear HS. rename HS3 into HS.
assert (TOFREE : forall cur2 (msx : machine_state) (Ex : env) (ssx : sstate),
cur <= cur2 <= nb -> (r <> 0 \/ nb < cur + N) ->
st_ok ubs0segs Ex ssx msx -> ss_pc ssx = FREESPC -> ss_resv ssx = None ->
journal ubs0_msyms MR STK sp0 FP L A mem md L2 A2 (ms_mem msx) md2 ->
getr (ms_regs msx) 2 = Z_to_bv 64 (sp - RFC_FRAME) -> getr (ms_regs msx) 3 = getr regs0 3 -> getr (ms_regs msx) 4 = getr regs0 4 ->
getr (ms_regs msx) 8 = Z_to_bv 64 dst -> getr (ms_regs msx) 9 = Z_to_bv 64 (2 ^ 64 - 1) ->
getr (ms_regs msx) 22 = getr regs0 22 -> getr (ms_regs msx) 23 = getr regs0 23 ->
getr (ms_regs msx) 24 = getr regs0 24 -> getr (ms_regs msx) 25 = getr regs0 25 -> getr (ms_regs msx) 26 = getr regs0 26 -> getr (ms_regs msx) 27 = getr regs0 27 ->
word_mem ubs0segs (ms_mem msx) (sp - 8) (bv_unsigned (getr regs0 1)) ->
word_mem ubs0segs (ms_mem msx) (sp - 16) (bv_unsigned (getr regs0 8)) ->
word_mem ubs0segs (ms_mem msx) (sp - 24) (bv_unsigned (getr regs0 9)) ->
word_mem ubs0segs (ms_mem msx) (sp - 32) (bv_unsigned (getr regs0 18)) ->
word_mem ubs0segs (ms_mem msx) (sp - 40) (bv_unsigned (getr regs0 19)) ->
word_mem ubs0segs (ms_mem msx) (sp - 48) (bv_unsigned (getr regs0 20)) ->
word_mem ubs0segs (ms_mem msx) (sp - 56) (bv_unsigned (getr regs0 21)) ->
word_mem ubs0segs (ms_mem msx) dst lp -> word_mem ubs0segs (ms_mem msx) (dst + 8) res ->
word_mem ubs0segs (ms_mem msx) (st + 16) cur2 ->
(forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp - RFC_DEPTH <= a < sp) -> ~ (dst <= a < dst + 16) -> ~ (st + 16 <= a < st + 24) ->
mbyte ubs0segs (ms_mem msx) a = mbyte ubs0segs mem1 a) ->
(forall b m i, In (b, m) Bb -> 0 <= i < m -> mbyte ubs0segs (ms_mem msx) (b + i) = mbyte ubs0segs mem1 (b + i)) ->
SR ubs0segs (mkCfg msx md2) (img_post_x regs0 STK sp0 FP L A mem md Bb lpb st dst N nb cur lp r mem1 pdata PAYLOAD bq)).
{ intros cur2 msx Ex ssx Hc2 Hwhy HSx Hpcx Hrvx HJx X2 X3 X4 X8 X9 X22 X23 X24 X25 X26 X27 V1 V8 V9 V18 V19 V20 V21 Vl Vi Vc Hfr1 Hbk1.
rewrite (st_ok_mkst ubs0segs Ex ssx msx HSx Hrvx), Hpcx.
eapply SR_mono.
{ eapply (rfc_frees_x STK sp0 FP L A mem md L2 A2 md2 regs0 (ms_regs msx) (ms_mem msx) Bb lpb dst res N lp palsz (rb_malloc bq N)
HJx Hbase HBnow Hfresh ltac:(lia) Hlp Hlp64 Hra0 Htp0 Hal16 Hwlo Hwhi H63 Hdst1 Hdst2 Hdst8
X2 X3 X4 X8 X9 X22 X23 X24 X25 X26 X27 V1 V8 V9 V18 V19 V20 V21 Vl Vi HR2). }
cbv beta. intros c' (L4 & A4 & regs4 & mem4 & md4 & -> & HJ4 & Hid4 & HP4 & Hq0 & Hhi4 & Hkeep4 & HB4 & HR4).
exists L4, A4, regs4, mem4, md4, 0, cur2, 0.
split; [reflexivity|]. split; [exact HJ4|]. split; [exact Hid4|]. split; [exact HP4|]. split; [exact Hq0|].
split; [intros a Ha Hn1 Hn2 Hn3; rewrite (Hhi4 a Ha Hn1); exact (Hfr1 a Ha Hn1 Hn2 Hn3)|].
split; [intros b m i Hb Hi; rewrite (Hkeep4 b m i Hb Hi); exact (Hbk1 b m i Hb Hi)|].
split; [eapply word_mem_frame; [exact Vc | intros i Hi; apply Hhi4; lia]|].
split; [lia|]. left. split; [reflexivity|]. split; [exists []; exact HB4|]. split; [exact Hwhy | exact HR4]. }
unfold hideP in Hsd.
destruct Hcase as [(Hfit & Ha3 & Hcw3 & Hcp3) | (Hnfit & Ha3 & Hcw3 & Hcp3)];
[ pose proof (st_ok_pin_rx ubs0segs _ _ _ 10%bv 0 HS Ha3 eq_refl) as HSp
| pose proof (st_ok_pin_rx ubs0segs _ _ _ 10%bv (2 ^ 64 - 1) HS Ha3 eq_refl) as HSp ];
clear HS; rename HSp into HS; unfold hideP in Hr; destruct Hr as [-> | ->].
4: jrun_to LAWS ubs0tbl_ok HS HJ3 FREESPC.
3: jrun_to LAWS ubs0tbl_ok HS HJ3 FREESPC.
2: jrun_to LAWS ubs0tbl_ok HS HJ3 FREESPC.
1: jrun LAWS ubs0tbl_ok HS HJ3.
all: lazymatch goal with
| |- wr_ok _ _ _ _ _ _ _ =>
eapply wr_ok_cons_win; [reflexivity | ew_havocF; exact HE2 | cbn [r_wlo r_whi]; intros _; clear - Hwlo Hwhi Hst1 Hst2 Hdst1 Hdst2 HFRv HDPv HASv; lia |];
eapply wr_ok_cons_win; [reflexivity | ew_havocF; exact HE8 | cbn [r_wlo r_whi]; intros _; clear - Hwlo Hwhi Hst1 Hst2 Hdst1 Hdst2 HFRv HDPv HASv; lia |];
apply wr_ok_nil
| |- _ => cbn [ms_mem mkst] in HF; rename HF into HFd
end.
1: eapply (SR_ret_at ubs0segs ubs0tbl); [exact ubs0tbl_ok | | | exact HS | reflexivity | vm_compute; reflexivity |].
1: exact (proj1 (heap_model _ _ LAWS _ _ _ _ (proj1 HJ3))).
1: exact (proj1 (proj2 (heap_model _ _ LAWS _ _ _ _ (proj1 HJ3)))).
1: rfc_img_post HS HJ3 Hid2 HX HE HE2 G3 G4 G24 G25 G26 G27 Hra0 1 (cur + N) res.
4: split; [lia | right; split; [reflexivity|]; split; [reflexivity|]; split; [| split; [| split; [exact HBnow | split; [exact Hfit | split; [reflexivity | split; [| split; [| exact HR2]]]]]]]].
10: eapply (TOFREE nb).
9: eapply (TOFREE nb).
8: eapply (TOFREE (cur + N)).
all: cbn [ms_mem mkst] in *.
all: lazymatch goal with
| |- _ \/ _ => first [left; lia | right; lia]
| |- _ <= _ <= _ => lia
| |- st_ok _ _ _ _ => exact HS
| |- ss_pc _ = _ => reflexivity
| |- ss_resv _ = _ => reflexivity
| |- journal _ _ _ _ _ _ _ _ _ _ _ _ _ => exact HJ3
| |- getr _ 2 = _ => reg_nowF HS ltac:(rewrite <- HE2, ?Z_to_bv_bv_unsigned; reflexivity)
| |- getr _ 3 = _ => reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 3%nat 3%bv eq_refl); exact G3)
| |- getr _ 4 = _ => reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 4%nat 4%bv eq_refl); exact G4)
| |- getr _ 8 = _ => reg_nowF HS ltac:(rewrite <- HE8, ?Z_to_bv_bv_unsigned; reflexivity)
| |- getr _ 9 = _ => reg_nowF HS ltac:(first [reflexivity | apply bv_eq; vm_compute; reflexivity])
| |- getr _ 22 = _ => reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 22%nat 22%bv eq_refl); exact G22)
| |- getr _ 23 = _ => reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 23%nat 23%bv eq_refl); exact G23)
| |- getr _ 24 = _ => reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 24%nat 24%bv eq_refl); exact G24)
| |- getr _ 25 = _ => reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 25%nat 25%bv eq_refl); exact G25)
| |- getr _ 26 = _ => reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 26%nat 26%bv eq_refl); exact G26)
| |- getr _ 27 = _ => reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 27%nat 27%bv eq_refl); exact G27)
| |- word_mem _ _ (?spv - ?dd) (bv_unsigned _) =>
let off := eval vm_compute in (RFC_FRAME - dd) in
let j := eval vm_compute in (Z.to_nat (dd / 8 - 1)) in
frame_wordF HS HX HE2 off j dd
| |- word_mem _ _ _ _ =>
first
[ solve [ eapply word_mem_frame; [exact Hcw3 |]; intros i Hi;
mb_frame_with HFd ltac:(lia) ltac:(rewrite ?HE2, ?HE8; lia); reflexivity ]
| solve [ rewrite <- (Z.add_0_r dst); eapply (st_chunk_word _ _ _ 1%nat _ 8%nat 0 (SOff 42 0) dst _ HS);
[ reflexivity | reflexivity | cbv; auto 12 | ew_havocF; exact HE8
| cbn [sv_denot]; ew_havocF; rewrite Z.add_0_r, (HX 42%nat 10%nat _ eq_refl eq_refl), Z_to_bv_bv_unsigned; reflexivity | lia ] ]
| solve [ eapply (st_chunk_word _ _ _ 1%nat _ 8%nat 8 (SOff 47 0) dst _ HS);
[ reflexivity | reflexivity | cbv; auto 12 | ew_havocF; exact HE8
| cbn [sv_denot]; ew_havocF; rewrite Z.add_0_r, Hq10, Z_to_bv_bv_unsigned; reflexivity | lia ] ] ]
| |- forall a : Z, alloc_ceiling <= a < _ -> _ =>
intros a Ha Hn1 Hn2 Hn3;
mbfA HFd Ha Hn1 Hn2 Hn3 Hac HFRv HDPv HASv HE2 HE8 HE18;
rewrite (mbyte_of_rd _ _ (sp - RFC_FRAME) res N st _ Hout3) by (rewrite ?HRDv; lia);
exact (Hfr_r a Ha Hn1 Hn2 Hn3)
| |- forall (b m i : Z), In (b, m) _ -> _ =>
intros b m i Hb Hi;
assert (Hbc : In (b, m) (blocks Lc Ac)) by (eapply Permutation_in; [apply Permutation_sym; exact HBc | apply in_app_iff; first [right; exact Hb | left; exact Hb]]);
destruct (heap_blocks _ _ LAWS Lc Ac mem1 mdc b m i HH Hbc Hi) as (_ & Hb0 & Hb1 & _);
destruct (heap_sep _ _ LAWS L2 A2 _ md2 b1 (res, N) b2 (b, m) HH2 Hbl2 ltac:(rewrite <- Hblc; exact Hbc)) as [Hs|Hs]; cbn [fst snd] in Hs;
mbfB HFd Hb0 Hb1 Hi Hac Hceil Hwlo Hst1 Hdst1 HFRv HDPv HASv HE2 HE8 HE18;
rewrite (mbyte_of_rd _ _ (sp - RFC_FRAME) res N st _ Hout3) by (rewrite ?HRDv; lia);
exact (Hbk_r b m i Hbc Hi)
| |- garr8 _ _ _ _ =>
refine (proj1 (rx_garr8_slice_copy _ _ pdata PAYLOAD res cur N (HPLk _ Hbk_r) ltac:(lia) ltac:(lia) ltac:(rewrite HPLn; lia) _));
intros i Hi;
mbfB HFd Rr0 Rr1 Hi Hac Hceil Hwlo Hst1 Hdst1 HFRv HDPv HASv HE2 HE8 HE18;
exact (Hcp3 i Hi)
end.
Qed.
End S.
End e.
