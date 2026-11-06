(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YM06 YK0s.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0i YO0f YO0x YO0d YO0e
YO0p YO0j YO0m YO0l YO0n YO0k YO0o.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YH00 YH03 YH02 YN3b YI06 YI5b YI09 YI08 YI0r YI1w YI5o
YI00 YI05 YI5a YI5f.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Section e. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma rx_garr8_skipn : forall m p (P : list Z) (c : nat),
garr8 src0segs m p P -> garr8 src0segs m (p + Z.of_nat c) (skipn c P).
Proof.
intros m p P c H. destruct (Nat.le_gt_cases c (length P)) as [Hc|Hc].
- rewrite <- (firstn_skipn c P) in H. apply garr8_app in H as [_ H2]. rewrite firstn_length_le in H2 by exact Hc. exact H2.
- rewrite skipn_all2 by lia. apply garr8_nil.
Qed.
Lemma rx_garr8_firstn : forall m p (l : list Z) (n : nat), garr8 src0segs m p l -> garr8 src0segs m p (firstn n l).
Proof. intros m p l n H. rewrite <- (firstn_skipn n l) in H. apply garr8_app in H as [H1 _]. exact H1. Qed.
Lemma rx_garr8_copy : forall m m' s d (l : list Z),
garr8 src0segs m s l -> (forall i, 0 <= i < Z.of_nat (length l) -> mbyte src0segs m' (d + i) = mbyte src0segs m (s + i)) ->
garr8 src0segs m' d l.
Proof.
intros m m' s d l H Hc j Hj. destruct (H j Hj) as [Hv Hr]. split; [|exact Hr].
intros k Hk. replace (d + Z.of_nat j + Z.of_nat k) with (d + (Z.of_nat j + Z.of_nat k)) by lia.
rewrite Hc by (cbn in Hk; lia). replace (s + (Z.of_nat j + Z.of_nat k)) with (s + Z.of_nat j + Z.of_nat k) by lia. apply Hv. exact Hk.
Qed.
Lemma rx_garr8_slice_copy : forall m m' p (P : list Z) d c n,
garr8 src0segs m p P -> 0 <= c -> 0 <= n -> c + n <= Z.of_nat (length P) ->
(forall i, 0 <= i < n -> mbyte src0segs m' (d + i) = mbyte src0segs m (p + c + i)) ->
garr8 src0segs m' d (firstn (Z.to_nat n) (skipn (Z.to_nat c) P)) /\ Z.of_nat (length (firstn (Z.to_nat n) (skipn (Z.to_nat c) P))) = n.
Proof.
intros m m' p P d c n H Hc Hn Hcn Hcp.
assert (Hlen : Z.of_nat (length (firstn (Z.to_nat n) (skipn (Z.to_nat c) P))) = n) by (rewrite length_firstn, length_skipn; lia).
split; [|exact Hlen]. eapply rx_garr8_copy.
- apply rx_garr8_firstn. apply (rx_garr8_skipn m p P (Z.to_nat c)). exact H.
- intros i Hi. rewrite Hlen in Hi. rewrite Hcp by lia. f_equal. lia.
Qed.
Section S.
Variable API : AllocAPI src0_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws src0_msyms MR := aa_laws API.
Hypothesis IMG : img_laws src0_msyms MR.
Definition ss_frees : sstate :=
mkSS FREESPC (sr_set sr_atoms 18%bv (SLit (2 ^ 64 - 1)))
[ YP09.mkRegion (Some 2%nat) 0 RFC_FRAME 0 RFC_FRAME
[mkChunk 40 (CVal 8 (SOff 32 0)); mkChunk 32 (CVal 8 (SOff 33 0)); mkChunk 24 (CVal 8 (SOff 34 0));
mkChunk 16 (CVal 8 (SOff 35 0)); mkChunk 8 (CVal 8 (SOff 36 0)); mkChunk 0 (CVal 8 (SOff 37 0))] ;
YP09.mkRegion (Some 8%nat) 0 16 0 0 [mkChunk 0 (CVal 8 (SOff 39 0)); mkChunk 8 (CVal 8 (SOff 38 0))] ]
None
(mkFacts [ (2%nat, mkAF (CEIL_MIN + ALLOC_STACK) (2^63) 4); (8%nat, mkAF CEIL_MIN (2^63) 3) ] [] []).
Definition ss_frees_c : sstate := Eval vm_compute in ss_frees.
Lemma rfc_frees_x :
forall STK sp0 FP L A mem md Lc Ac mdc (regs0 regs1 : bvmap 5 word) (mem1 : word -> option byte)
(Bb lpb : list (Z * Z)) (dst img N lp palsz : Z) (bq : rbound),
journal src0_msyms MR STK sp0 FP L A mem md Lc Ac mem1 mdc ->
(forall b, In b (blocks L A) -> In b Bb) ->
Permutation (blocks Lc Ac) ((img, N) :: lpb ++ Bb) ->
~ In (img, N) (blocks L A) -> 0 < N ->
((lp = 0 /\ lpb = []) \/ (exists lpa, lpb = [(lpa, palsz)] /\ Z_to_bv 64 lpa = Z_to_bv 64 lp /\ (In (lpa, palsz) (blocks L A) -> palsz <= 0) /\ 0 <= palsz)) ->
0 <= lp < 2 ^ 64 ->
YK0s.ret_ok (getr regs0 1) -> getr regs0 4 = Z_to_bv 64 (ms_tp src0_msyms) ->
spZ regs0 mod 16 = 0 -> sp0 - STK <= spZ regs0 - RFC_DEPTH -> spZ regs0 <= sp0 -> sp0 < 2 ^ 63 ->
spZ regs0 <= dst -> dst + 32 <= sp0 -> dst mod 8 = 0 ->
getr regs1 2 = Z_to_bv 64 (spZ regs0 - RFC_FRAME) -> getr regs1 3 = getr regs0 3 -> getr regs1 4 = getr regs0 4 ->
getr regs1 8 = Z_to_bv 64 dst ->
getr regs1 18 = Z_to_bv 64 (2 ^ 64 - 1) ->
getr regs1 21 = getr regs0 21 -> getr regs1 22 = getr regs0 22 -> getr regs1 23 = getr regs0 23 ->
getr regs1 24 = getr regs0 24 -> getr regs1 25 = getr regs0 25 -> getr regs1 26 = getr regs0 26 -> getr regs1 27 = getr regs0 27 ->
word_mem src0segs mem1 (spZ regs0 - 8) (bv_unsigned (getr regs0 1)) ->
word_mem src0segs mem1 (spZ regs0 - 16) (bv_unsigned (getr regs0 8)) ->
word_mem src0segs mem1 (spZ regs0 - 24) (bv_unsigned (getr regs0 9)) ->
word_mem src0segs mem1 (spZ regs0 - 32) (bv_unsigned (getr regs0 18)) ->
word_mem src0segs mem1 (spZ regs0 - 40) (bv_unsigned (getr regs0 19)) ->
word_mem src0segs mem1 (spZ regs0 - 48) (bv_unsigned (getr regs0 20)) ->
word_mem src0segs mem1 dst lp -> word_mem src0segs mem1 (dst + 8) img ->
res_ok Ac bq ->
SR src0segs (mkCfg (mkst regs1 (Z_to_bv 64 FREESPC) mem1 (seg_rom src0segs)) mdc)
(fun c' => exists L2 A2 regs2 mem2 md2,
c' = mkCfg (mkst regs2 (getr regs0 1) mem2 (seg_rom src0segs)) md2 /\
journal src0_msyms MR STK sp0 FP L A mem md L2 A2 mem2 md2 /\
st_init_done A2 = true /\
regs_preserved regs0 regs2 /\
getr regs2 10 = Z_to_bv 64 0 /\
(forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (spZ regs0 - RFC_DEPTH <= a < spZ regs0) ->
mbyte src0segs mem2 a = mbyte src0segs mem1 a) /\
(forall b m i, In (b, m) Bb -> 0 <= i < m -> mbyte src0segs mem2 (b + i) = mbyte src0segs mem1 (b + i)) /\
Permutation (blocks L2 A2) Bb /\
res_ok A2 (rb_free bq N)).
Proof.
intros STK sp0 FP L A mem md Lc Ac mdc regs0 regs1 mem1 Bb lpb dst img N lp palsz bq
HJ Hbase HBc Himgold HN Hlp Hlp64 Hra0 Htp0 Hal16 Hwlo Hwhi H63 Hdst1 Hdst2 Hdst8
G2 G3 G4 G8 G18 G21 G22 G23 G24 G25 G26 G27
W1 W8 W9 W18 W19 W20 Wl Wi HRq.
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HASv : ALLOC_STACK = 8192) by reflexivity.
assert (HFRv : RFC_FRAME = 48) by reflexivity. assert (HDPv : RFC_DEPTH = 8240) by reflexivity.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HH.
pose proof HJ as (_ & _ & _ & _ & _ & (Hsp0al & Hstk0 & Hceil & Hsp063 & Hstw) & _).
set (sp := spZ regs0) in *.
assert (Hspm : (sp - RFC_FRAME) mod 16 = 0).
{ rewrite HFRv. replace (sp - 48) with (sp + (-3) * 16) by lia. rewrite Z.mod_add by lia. exact Hal16. }
assert (Himg : In (img, N) (blocks Lc Ac)) by (eapply Permutation_in; [apply Permutation_sym; exact HBc | left; reflexivity]).
destruct (heap_blocks_range _ _ LAWS Lc Ac mem1 mdc img N HH Himg HN) as (Hi0 & Hi1 & _).
assert (Hlpr : 0 <= lp < 2 ^ 64) by exact Hlp64.
set (extra := [getr regs0 1; getr regs0 8; getr regs0 9; getr regs0 18; getr regs0 19; getr regs0 20; Z_to_bv 64 img; Z_to_bv 64 lp]).
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew (Ereg regs1 extra) n = getr regs1 rr) by (intros; apply ew_Ereg_nat; assumption).
assert (HX : forall n j v, (n = 32 + j)%nat -> nth_error extra j = Some v -> ew (Ereg regs1 extra) n = v).
{ intros n j v -> Hj. rewrite ew_Ereg_extra. apply nth_error_nth. exact Hj. }
assert (HE2 : bv_unsigned (ew (Ereg regs1 extra) 2) = sp - RFC_FRAME) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; lia).
assert (HE8 : bv_unsigned (ew (Ereg regs1 extra) 8) = dst) by (rewrite (HE 8%nat 8%bv eq_refl), G8; apply unsigned_lit_small; lia).
assert (HS : st_ok src0segs (Ereg regs1 extra) ss_frees_c (mkst regs1 (Z_to_bv 64 FREESPC) mem1 (seg_rom src0segs))).
{ change ss_frees_c with ss_frees. unfold ss_frees. apply entry_st_ok_full.
- apply regs_ok_pin; [apply regs_ok_Ereg | intros H0; discriminate H0 |]. cbn [sv_denot]. exact G18.
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor]].
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HE2.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply (journal_stack_w _ _ _ _ _ _ _ _ _ _ _ _ _ HJ). lia. }
assert (CK : forall off j (w : word) (W : word_mem src0segs mem1 (sp - RFC_FRAME + off) (bv_unsigned w)),
nth_error extra j = Some w ->
chunk_ok src0segs (Ereg regs1 extra) mem1 (sp - RFC_FRAME) (mkChunk off (CVal 8 (SOff (32 + j) 0)))).
{ intros off j w W Hj. eapply (chunk_ok_val _ _ _ _ _ _ _ (bv_unsigned w)); [| pose proof (bv_unsigned_in_range 64 w) as Rw; change (bv_modulus 64) with (2 ^ 64) in Rw; cbn; lia | cbn; lia | apply val_mem_word_mem; exact W].
cbn [sv_denot]. rewrite Z.add_0_r, (HX (32 + j)%nat j w eq_refl Hj), Z_to_bv_bv_unsigned. reflexivity. }
repeat (apply Forall_cons; [ first [ eapply (CK 40 0%nat); [replace (sp - RFC_FRAME + 40) with (sp - 8) by lia; exact W1 | reflexivity]
| eapply (CK 32 1%nat); [replace (sp - RFC_FRAME + 32) with (sp - 16) by lia; exact W8 | reflexivity]
| eapply (CK 24 2%nat); [replace (sp - RFC_FRAME + 24) with (sp - 24) by lia; exact W9 | reflexivity]
| eapply (CK 16 3%nat); [replace (sp - RFC_FRAME + 16) with (sp - 32) by lia; exact W18 | reflexivity]
| eapply (CK 8 4%nat); [replace (sp - RFC_FRAME + 8) with (sp - 40) by lia; exact W19 | reflexivity]
| eapply (CK 0 5%nat); [replace (sp - RFC_FRAME + 0) with (sp - 48) by lia; exact W20 | reflexivity] ] | ]).
apply Forall_nil.
+
unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HE8.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. lia. }
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ lp); [cbn [sv_denot]; rewrite Z.add_0_r, (HX 39%nat 7%nat _ eq_refl eq_refl), Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | rewrite Z.add_0_r; apply val_mem_word_mem; exact Wl]. }
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ img); [cbn [sv_denot]; rewrite Z.add_0_r, (HX 38%nat 6%nat _ eq_refl eq_refl), Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact Wi]. }
apply Forall_nil.
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val].
rewrite HE2, HE8. repeat split; lia.
- split; [| split; constructor].
cbn [atoms_ok f_atoms]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite HE2, HE8.
change (2 ^ 4) with 16. change (2 ^ 3) with 8.
repeat split; try lia; assumption. }
change mem1 with (ms_mem (mkst regs1 (Z_to_bv 64 FREESPC) mem1 (seg_rom src0segs))) in HJ.
jrun_to LAWS src0tbl_ok HS HJ src0_A_free.
{ eapply wr_ok_cons_win; [reflexivity | exact HE2 | cbn [r_wlo r_whi]; intros _; lia |].
eapply wr_ok_cons_win; [reflexivity | exact HE8 | cbn [r_wlo r_whi]; intros Hw; lia |]. apply wr_ok_nil. }
jreg HS (10%bv:reg) as F10. rewrite (HX 38%nat 6%nat _ eq_refl eq_refl) in F10.
jreg HS (2%bv:reg) as F2. rewrite (HE 2%nat 2%bv eq_refl), G2 in F2.
jreg HS (4%bv:reg) as F4. rewrite (HE 4%nat 4%bv eq_refl), G4, Htp0 in F4.
jreg HS (1%bv:reg) as F1.
assert (Hbl1 : exists b1 b2, blocks Lc Ac = b1 ++ (img, N) :: b2).
{ destruct (in_split _ _ Himg) as (b1 & b2 & Hb). exists b1, b2. exact Hb. }
eapply SR_bind.
{ eapply (jfree_at_res API IMG) with (a := img) (n := N) (spc := sp - RFC_FRAME);
[ exact HS | reflexivity | reflexivity | exact HJ | exact Himg | exact HRq | exact F10
| exact F2 | lia | exact Hspm | lia | lia | exact F4 | exact F1 | apply ret_ok_even; vm_compute; reflexivity
| intros Hin; exfalso; exact (Himgold Hin) ]. }
intros c' (L3 & A3 & regs3 & mem3 & md3 & -> & HJ3 & HP3 & Hrm3 & Hkeep3 & Hhi3 & Hid3 & HR3). clear HJ.
change (ms_segs src0_msyms) with src0segs in Hkeep3, Hhi3.
assert (HB3 : Permutation (blocks L3 A3) (lpb ++ Bb)) by (eapply perm_after_rm1; [exact HBc | exact Hrm3]).
jafter_call2 HS 40%nat regs3 mem3 HP3 0 [0%nat] HS2.
match type of HS2 with ?P -> _ => assert (HK : P); [|specialize (HS2 HK)] end.
{ constructor; [|constructor; [|constructor]].
- eapply (region_kept_stack src0segs _ _ _ 2); [exact HE2 | exact Hhi3 | lia | lia | lia | cbn; lia | cbn; lia].
- eapply (region_kept_stack src0segs _ _ _ 8); [exact HE8 | exact Hhi3 | lia | lia | lia | cbn; lia | cbn; lia]. }
clear HS. rename HS2 into HS.
jrun_to LAWS src0tbl_ok HS HJ3 src0_A_free.
{ eapply wr_ok_cons_win; [reflexivity | ew_havoc; exact HE2 | cbn [r_wlo r_whi]; intros _; lia |].
eapply wr_ok_cons_win; [reflexivity | ew_havoc; exact HE8 | cbn [r_wlo r_whi]; intros Hw; lia |]. apply wr_ok_nil. }
jreg HS (10%bv:reg) as K10. rewrite (HX 39%nat 7%nat _ eq_refl eq_refl) in K10.
jreg HS (2%bv:reg) as K2. rewrite (HE 2%nat 2%bv eq_refl), G2 in K2.
jreg HS (4%bv:reg) as K4. rewrite (HE 4%nat 4%bv eq_refl), G4, Htp0 in K4.
jreg HS (1%bv:reg) as K1.
lazymatch goal with |- SR _ (mkCfg ?msq ?mdq) _ =>
assert (STEP : SR src0segs (mkCfg msq mdq)
(fun c' => exists L4 A4 regs4 mem4 md4,
c' = mkCfg (mkst regs4 (Z_to_bv 64 RA_FREE2) mem4 (seg_rom src0segs)) md4 /\
journal src0_msyms MR STK sp0 FP L A mem md L4 A4 mem4 md4 /\ st_init_done A4 = true /\
regs_preserved (ms_regs msq) regs4 /\ Permutation (blocks L4 A4) Bb /\
(forall b m i, In (b, m) (blocks L4 A4) -> 0 <= i < m -> mbyte src0segs mem4 (b + i) = mbyte src0segs (ms_mem msq) (b + i)) /\
(forall x, alloc_ceiling <= x < 2 ^ 64 -> ~ (sp - RFC_FRAME - ALLOC_STACK <= x < sp - RFC_FRAME) ->
mbyte src0segs mem4 x = mbyte src0segs (ms_mem msq) x /\ (writable_at src0segs (ms_mem msq) x <-> writable_at src0segs mem4 x)) /\
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
clear HK. jafter_call2 HS 57%nat regs4 mem4 HP4 0 (@nil nat) HS2.
match type of HS2 with ?P -> _ => assert (HK : P); [|specialize (HS2 HK)] end.
{ constructor; [|constructor].
eapply (region_kept_stack src0segs _ _ _ 2); [ew_havoc; exact HE2 | exact Hhi4 | lia | lia | lia | cbn; lia | cbn; lia]. }
clear HS. rename HS2 into HS.
jrun LAWS src0tbl_ok HS HJ4.
{ eapply wr_ok_cons_win; [reflexivity | ew_havoc; exact HE2 | cbn [r_wlo r_whi]; intros _; lia |]. apply wr_ok_nil. }
eapply (SR_ret_at src0segs src0tbl); [exact src0tbl_ok | | | exact HS | reflexivity | vm_compute; reflexivity |].
{ exact (proj1 (heap_model _ _ LAWS _ _ _ _ (proj1 HJ4))). }
{ exact (proj1 (proj2 (heap_model _ _ LAWS _ _ _ _ (proj1 HJ4)))). }
lazymatch type of HS with st_ok _ ?Ef ?ssf ?msf =>
pose proof (st_ok_reg src0segs Ef ssf msf 1%bv HS) as Q1; eval_sr_get_in Q1; cbn [sv_denot] in Q1;
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
split; [ pose proof (st_ok_reg src0segs Ef ssf msf 10%bv HS) as Q10; eval_sr_get_in Q10; cbn [sv_denot] in Q10; cbn [ms_regs mkst]; rewrite Q10; reflexivity |];
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
Ltac frees_tac HS HJ HX HE HE2 HE8 Hbase Hra0 Htp0 Hal16 Hwlo Hwhi H63 Hdst1 Hdst2 Hdst8 G3 G4 G21 G22 G23 G24 G25 G26 G27 dst img N lp palsz lpb Bb bq :=
lazymatch type of HS with st_ok _ ?Ec ?ssc ?msc =>
let T2 := fresh "T2" in let T3 := fresh "T3" in let T4 := fresh "T4" in let T8 := fresh "T8" in
let T18 := fresh "T18" in let T21 := fresh "T21" in let T22 := fresh "T22" in let T23 := fresh "T23" in
let T24 := fresh "T24" in let T25 := fresh "T25" in
let T26 := fresh "T26" in let T27 := fresh "T27" in
pose proof (st_ok_reg src0segs Ec ssc msc 2%bv HS) as T2; pose proof (st_ok_reg src0segs Ec ssc msc 3%bv HS) as T3;
pose proof (st_ok_reg src0segs Ec ssc msc 4%bv HS) as T4; pose proof (st_ok_reg src0segs Ec ssc msc 8%bv HS) as T8;
pose proof (st_ok_reg src0segs Ec ssc msc 18%bv HS) as T18;
pose proof (st_ok_reg src0segs Ec ssc msc 21%bv HS) as T21; pose proof (st_ok_reg src0segs Ec ssc msc 22%bv HS) as T22;
pose proof (st_ok_reg src0segs Ec ssc msc 23%bv HS) as T23;
pose proof (st_ok_reg src0segs Ec ssc msc 24%bv HS) as T24; pose proof (st_ok_reg src0segs Ec ssc msc 25%bv HS) as T25;
pose proof (st_ok_reg src0segs Ec ssc msc 26%bv HS) as T26; pose proof (st_ok_reg src0segs Ec ssc msc 27%bv HS) as T27;
eval_sr_get_in T2; eval_sr_get_in T3; eval_sr_get_in T4; eval_sr_get_in T8; eval_sr_get_in T18;
eval_sr_get_in T21; eval_sr_get_in T22; eval_sr_get_in T23;
eval_sr_get_in T24; eval_sr_get_in T25; eval_sr_get_in T26; eval_sr_get_in T27;
cbn [sv_denot] in T2, T3, T4, T8, T18, T21, T22, T23, T24, T25, T26, T27;
repeat (rewrite ew_havoc_old in T2; [|cbv; lia]); repeat (rewrite ew_havoc_old in T3; [|cbv; lia]);
repeat (rewrite ew_havoc_old in T4; [|cbv; lia]); repeat (rewrite ew_havoc_old in T8; [|cbv; lia]);
repeat (rewrite ew_havoc_old in T21; [|cbv; lia]); repeat (rewrite ew_havoc_old in T22; [|cbv; lia]);
repeat (rewrite ew_havoc_old in T23; [|cbv; lia]); repeat (rewrite ew_havoc_old in T24; [|cbv; lia]);
repeat (rewrite ew_havoc_old in T25; [|cbv; lia]); repeat (rewrite ew_havoc_old in T26; [|cbv; lia]);
repeat (rewrite ew_havoc_old in T27; [|cbv; lia]);
rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned in T2, T3, T4, T8, T21, T22, T23, T24, T25, T26, T27;
rewrite (st_ok_mkst src0segs Ec ssc msc HS eq_refl);
eapply SR_mono;
[ eapply (rfc_frees_x _ _ _ _ _ _ _ _ _ _ _ (ms_regs msc) (ms_mem msc) Bb lpb dst img N lp palsz bq HJ Hbase);
[ | | lia | | | exact Hra0 | exact Htp0 | exact Hal16 | exact Hwlo | exact Hwhi | exact H63
| exact Hdst1 | exact Hdst2 | exact Hdst8
| rewrite T2, <- (Z_to_bv_bv_unsigned 64 (ew _ 2)), HE2; reflexivity
| rewrite T3, (HE 3%nat 3%bv eq_refl); exact G3
| rewrite T4, (HE 4%nat 4%bv eq_refl); exact G4
| rewrite T8, <- (Z_to_bv_bv_unsigned 64 (ew _ 8)), HE8; reflexivity
| exact T18
| rewrite T21, (HE 21%nat 21%bv eq_refl); exact G21
| rewrite T22, (HE 22%nat 22%bv eq_refl); exact G22
| rewrite T23, (HE 23%nat 23%bv eq_refl); exact G23
| rewrite T24, (HE 24%nat 24%bv eq_refl); exact G24
| rewrite T25, (HE 25%nat 25%bv eq_refl); exact G25
| rewrite T26, (HE 26%nat 26%bv eq_refl); exact G26
| rewrite T27, (HE 27%nat 27%bv eq_refl); exact G27
| frame_word HS HX HE2 40 0%nat 8 | frame_word HS HX HE2 32 1%nat 16 | frame_word HS HX HE2 24 2%nat 24
| frame_word HS HX HE2 16 3%nat 32 | frame_word HS HX HE2 8 4%nat 40 | frame_word HS HX HE2 0 5%nat 48
| | | ]
| cbv beta ]
end.
Definition ss_img (r : Z) : sstate :=
mkSS IMGPC (sr_set sr_atoms 20%bv (SLit r))
[ YP09.mkRegion (Some 2%nat) 0 RFC_FRAME 0 RFC_FRAME
[mkChunk 40 (CVal 8 (SOff 32 0)); mkChunk 32 (CVal 8 (SOff 33 0)); mkChunk 24 (CVal 8 (SOff 34 0));
mkChunk 16 (CVal 8 (SOff 35 0)); mkChunk 8 (CVal 8 (SOff 36 0)); mkChunk 0 (CVal 8 (SOff 37 0))] ;
YP09.mkRegion (Some 9%nat) 0 24 16 24 [mkChunk 0 (CVal 8 (SOff 38 0)); mkChunk 8 (CVal 8 (SOff 39 0)); mkChunk 16 (CVal 8 (SOff 40 0))] ;
YP09.mkRegion (Some 8%nat) 0 16 0 16 [mkChunk 0 (CVal 8 (SOff 41 0))] ]
None
(mkFacts [ (2%nat, mkAF (CEIL_MIN + ALLOC_STACK) (2^63) 4); (9%nat, mkAF CEIL_MIN (2^63) 3);
(8%nat, mkAF CEIL_MIN (2^63) 3); (18%nat, mkAF 1 100000000 0);
(38%nat, mkAF 4096 CEIL_MAX 0); (39%nat, mkAF 1 CEIL_MAX 0);
(40%nat, mkAF 0 CEIL_MAX 0) ] [] []).
Definition img_post_x (regs0 : bvmap 5 word) (STK sp0 : Z) (FP : list (Z * Z)) L A mem md
(Bb : list (Z * Z)) (lpb : list (Z * Z)) (st dst N nb cur lp r : Z) (mem1 : word -> option byte)
(pdata : Z) (PAYLOAD : list Z) (bq : rbound)
(c' : config) : Prop :=
exists L2 A2 regs2 mem2 md2 (res cur2 img : Z),
c' = mkCfg (mkst regs2 (getr regs0 1) mem2 (seg_rom src0segs)) md2 /\
journal src0_msyms MR STK sp0 FP L A mem md L2 A2 mem2 md2 /\
st_init_done A2 = true /\
regs_preserved regs0 regs2 /\
getr regs2 10 = Z_to_bv 64 res /\
(forall a, alloc_ceiling <= a < 2 ^ 64 ->
~ (spZ regs0 - RFC_DEPTH <= a < spZ regs0) -> ~ (dst <= a < dst + 16) -> ~ (st + 16 <= a < st + 24) ->
mbyte src0segs mem2 a = mbyte src0segs mem1 a) /\
(forall b m i, In (b, m) Bb -> 0 <= i < m -> mbyte src0segs mem2 (b + i) = mbyte src0segs mem1 (b + i)) /\
word_mem src0segs mem2 (st + 16) cur2 /\ cur <= cur2 <= nb /\
((res = 0 /\ (exists leak, Permutation (blocks L2 A2) (leak ++ Bb)) /\ (r <> 0 \/ nb < cur + N) /\
res_ok A2 (rb_free (rb_malloc bq N) N)) \/
(res = 1 /\ r = 0 /\ word_mem src0segs mem2 dst lp /\ word_mem src0segs mem2 (dst + 8) img /\
Permutation (blocks L2 A2) ((img, N) :: lpb ++ Bb) /\
cur + N <= nb /\ cur2 = cur + N /\
(forall b m i, In (b, m) lpb -> 0 <= i < m -> mbyte src0segs mem2 (b + i) = mbyte src0segs mem1 (b + i)) /\
garr8 src0segs mem2 img (firstn (Z.to_nat N) (skipn (Z.to_nat cur) PAYLOAD)) /\
res_ok A2 (rb_malloc bq N))).
Lemma rfc_img_x : forall r : Z, (r = 0 \/ r = 2 ^ 64 - 1) ->
forall STK sp0 FP L A mem md Lc Ac mdc (regs0 regs1 : bvmap 5 word) (mem1 : word -> option byte)
(Bb lpb : list (Z * Z)) (st dst N pdata nb cur lp palsz : Z) (PAYLOAD : list Z) (bq : rbound),
journal src0_msyms MR STK sp0 FP L A mem md Lc Ac mem1 mdc -> st_init_done Ac = true ->
(forall b, In b (blocks L A) -> In b Bb) ->
Permutation (blocks Lc Ac) (lpb ++ Bb) ->
In (pdata, nb) Bb ->
((lp = 0 /\ lpb = []) \/ (exists lpa, lpb = [(lpa, palsz)] /\ Z_to_bv 64 lpa = Z_to_bv 64 lp /\ (In (lpa, palsz) (blocks L A) -> palsz <= 0) /\ 0 <= palsz)) ->
0 <= lp < 2 ^ 64 ->
YK0s.ret_ok (getr regs0 1) -> getr regs0 4 = Z_to_bv 64 (ms_tp src0_msyms) ->
spZ regs0 mod 16 = 0 -> sp0 - STK <= spZ regs0 - RFC_DEPTH -> spZ regs0 <= sp0 ->
spZ regs0 <= st -> st + 24 <= sp0 -> spZ regs0 <= dst -> dst + 32 <= sp0 -> (st + 24 <= dst \/ dst + 32 <= st) ->
st mod 8 = 0 -> dst mod 8 = 0 -> sp0 < 2 ^ 63 ->
1 <= N <= 100000000 -> 0 <= cur <= nb -> 0 < nb ->
getr regs1 2 = Z_to_bv 64 (spZ regs0 - RFC_FRAME) -> getr regs1 3 = getr regs0 3 -> getr regs1 4 = getr regs0 4 ->
getr regs1 8 = Z_to_bv 64 dst -> getr regs1 9 = Z_to_bv 64 st -> getr regs1 18 = Z_to_bv 64 N ->
getr regs1 20 = Z_to_bv 64 r ->
getr regs1 21 = getr regs0 21 -> getr regs1 22 = getr regs0 22 -> getr regs1 23 = getr regs0 23 ->
getr regs1 24 = getr regs0 24 -> getr regs1 25 = getr regs0 25 -> getr regs1 26 = getr regs0 26 -> getr regs1 27 = getr regs0 27 ->
word_mem src0segs mem1 (spZ regs0 - 8) (bv_unsigned (getr regs0 1)) ->
word_mem src0segs mem1 (spZ regs0 - 16) (bv_unsigned (getr regs0 8)) ->
word_mem src0segs mem1 (spZ regs0 - 24) (bv_unsigned (getr regs0 9)) ->
word_mem src0segs mem1 (spZ regs0 - 32) (bv_unsigned (getr regs0 18)) ->
word_mem src0segs mem1 (spZ regs0 - 40) (bv_unsigned (getr regs0 19)) ->
word_mem src0segs mem1 (spZ regs0 - 48) (bv_unsigned (getr regs0 20)) ->
word_mem src0segs mem1 st pdata -> word_mem src0segs mem1 (st + 8) nb -> word_mem src0segs mem1 (st + 16) cur -> word_mem src0segs mem1 dst lp ->
garr8 src0segs mem1 pdata PAYLOAD -> Z.of_nat (length PAYLOAD) = nb ->
res_ok Ac bq -> room bq N ->
SR src0segs (mkCfg (mkst regs1 (Z_to_bv 64 IMGPC) mem1 (seg_rom src0segs)) mdc)
(img_post_x regs0 STK sp0 FP L A mem md Bb lpb st dst N nb cur lp r mem1 pdata PAYLOAD bq).
Proof.
intros r Hr STK sp0 FP L A mem md Lc Ac mdc regs0 regs1 mem1 Bb lpb st dst N pdata nb cur lp palsz PAYLOAD bq
HJ Hid Hbase HBc Hpd Hlp Hlp64 Hra0 Htp0 Hal16 Hwlo Hwhi Hst1 Hst2 Hdst1 Hdst2 Hsd Hst8 Hdst8 H63 HN Hcur Hnb
G2 G3 G4 G8 G9 G18 G20 G21 G22 G23 G24 G25 G26 G27
W1 W8 W9 W18 W19 W20 Wp Wn Wc Wl HPL HPLn HRq HRm.
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HASv : ALLOC_STACK = 8192) by reflexivity.
assert (HFRv : RFC_FRAME = 48) by reflexivity. assert (HDPv : RFC_DEPTH = 8240) by reflexivity.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HH.
pose proof HJ as (_ & _ & _ & _ & _ & (Hsp0al & Hstk0 & Hceil & Hsp063 & Hstw) & _).
assert (Hpdc : In (pdata, nb) (blocks Lc Ac)) by (eapply Permutation_in; [apply Permutation_sym; exact HBc | apply in_app_iff; right; exact Hpd]).
destruct (heap_blocks_range _ _ LAWS Lc Ac mem1 mdc pdata nb HH Hpdc ltac:(lia)) as (Hp0 & Hp1 & _).
set (sp := spZ regs0) in *.
assert (Hspm : (sp - RFC_FRAME) mod 16 = 0).
{ rewrite HFRv. replace (sp - 48) with (sp + (-3) * 16) by lia. rewrite Z.mod_add by lia. exact Hal16. }
set (extra := [getr regs0 1; getr regs0 8; getr regs0 9; getr regs0 18; getr regs0 19; getr regs0 20;
Z_to_bv 64 pdata; Z_to_bv 64 nb; Z_to_bv 64 cur; Z_to_bv 64 lp]).
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew (Ereg regs1 extra) n = getr regs1 rr) by (intros; apply ew_Ereg_nat; assumption).
assert (HX : forall n j v, (n = 32 + j)%nat -> nth_error extra j = Some v -> ew (Ereg regs1 extra) n = v).
{ intros n j v -> Hj. rewrite ew_Ereg_extra. apply nth_error_nth. exact Hj. }
assert (Hlpr : 0 <= lp < 2 ^ 64) by exact Hlp64.
assert (HS : st_ok src0segs (Ereg regs1 extra) (ss_img r) (mkst regs1 (Z_to_bv 64 IMGPC) mem1 (seg_rom src0segs))).
{ unfold ss_img. apply entry_st_ok_full.
- apply regs_ok_pin; [apply regs_ok_Ereg | intros H0; discriminate H0 |]. cbn [sv_denot]. exact G20.
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor; [|constructor]]].
+
unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val].
rewrite (HE 2%nat 2%bv eq_refl), G2, unsigned_lit_small by lia.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply (journal_stack_w _ _ _ _ _ _ _ _ _ _ _ _ _ HJ). lia. }
assert (CK : forall off j (w : word) (W : word_mem src0segs mem1 (sp - RFC_FRAME + off) (bv_unsigned w)),
nth_error extra j = Some w ->
chunk_ok src0segs (Ereg regs1 extra) mem1 (sp - RFC_FRAME) (mkChunk off (CVal 8 (SOff (32 + j) 0)))).
{ intros off j w W Hj. eapply (chunk_ok_val _ _ _ _ _ _ _ (bv_unsigned w)); [| pose proof (bv_unsigned_in_range 64 w) as Rw; change (bv_modulus 64) with (2 ^ 64) in Rw; cbn; lia | cbn; lia | apply val_mem_word_mem; exact W].
cbn [sv_denot]. rewrite Z.add_0_r, (HX (32 + j)%nat j w eq_refl Hj), Z_to_bv_bv_unsigned. reflexivity. }
repeat (apply Forall_cons; [ first [ eapply (CK 40 0%nat); [replace (sp - RFC_FRAME + 40) with (sp - 8) by lia; exact W1 | reflexivity]
| eapply (CK 32 1%nat); [replace (sp - RFC_FRAME + 32) with (sp - 16) by lia; exact W8 | reflexivity]
| eapply (CK 24 2%nat); [replace (sp - RFC_FRAME + 24) with (sp - 24) by lia; exact W9 | reflexivity]
| eapply (CK 16 3%nat); [replace (sp - RFC_FRAME + 16) with (sp - 32) by lia; exact W18 | reflexivity]
| eapply (CK 8 4%nat); [replace (sp - RFC_FRAME + 8) with (sp - 40) by lia; exact W19 | reflexivity]
| eapply (CK 0 5%nat); [replace (sp - RFC_FRAME + 0) with (sp - 48) by lia; exact W20 | reflexivity] ] | ]).
apply Forall_nil.
+
unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val].
rewrite (HE 9%nat 9%bv eq_refl), G9, unsigned_lit_small by lia.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply (journal_stack_w _ _ _ _ _ _ _ _ _ _ _ _ _ HJ). lia. }
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ pdata); [cbn [sv_denot]; rewrite Z.add_0_r, (HX 38%nat 6%nat _ eq_refl eq_refl), Z_to_bv_bv_unsigned; reflexivity | lia | cbn; lia | rewrite Z.add_0_r; apply val_mem_word_mem; exact Wp]. }
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ nb); [cbn [sv_denot]; rewrite Z.add_0_r, (HX 39%nat 7%nat _ eq_refl eq_refl), Z_to_bv_bv_unsigned; reflexivity | lia | cbn; lia | apply val_mem_word_mem; exact Wn]. }
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ cur); [cbn [sv_denot]; rewrite Z.add_0_r, (HX 40%nat 8%nat _ eq_refl eq_refl), Z_to_bv_bv_unsigned; reflexivity | lia | cbn; lia | apply val_mem_word_mem; exact Wc]. }
apply Forall_nil.
+
unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val].
rewrite (HE 8%nat 8%bv eq_refl), G8, unsigned_lit_small by lia.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply (journal_stack_w _ _ _ _ _ _ _ _ _ _ _ _ _ HJ). lia. }
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ lp); [cbn [sv_denot]; rewrite Z.add_0_r, (HX 41%nat 9%nat _ eq_refl eq_refl), Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | rewrite Z.add_0_r; apply val_mem_word_mem; exact Wl]. }
apply Forall_nil.
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val].
rewrite (HE 2%nat 2%bv eq_refl), (HE 9%nat 9%bv eq_refl), (HE 8%nat 8%bv eq_refl), G2, G9, G8, !unsigned_lit_small by lia.
repeat split; lia.
- split; [| split; constructor].
cbn [atoms_ok f_atoms]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite (HE 2%nat 2%bv eq_refl), (HE 9%nat 9%bv eq_refl), (HE 8%nat 8%bv eq_refl), (HE 18%nat 18%bv eq_refl),
(HX 38%nat 6%nat _ eq_refl eq_refl), (HX 39%nat 7%nat _ eq_refl eq_refl), (HX 40%nat 8%nat _ eq_refl eq_refl),
G2, G9, G8, G18, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 3) with 8. change (2 ^ 0) with 1.
rewrite !Z.mod_1_r.
repeat split; try lia; assumption. }
change mem1 with (ms_mem (mkst regs1 (Z_to_bv 64 IMGPC) mem1 (seg_rom src0segs))) in HJ.
assert (HE2 : bv_unsigned (ew (Ereg regs1 extra) 2) = sp - RFC_FRAME) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; lia).
assert (HE9 : bv_unsigned (ew (Ereg regs1 extra) 9) = st) by (rewrite (HE 9%nat 9%bv eq_refl), G9; apply unsigned_lit_small; lia).
assert (HE8 : bv_unsigned (ew (Ereg regs1 extra) 8) = dst) by (rewrite (HE 8%nat 8%bv eq_refl), G8; apply unsigned_lit_small; lia).
assert (WROK : forall blc, wr_ok (Ereg regs1 extra) (ss_mem (ss_img r)) STK sp0 FP (blocks L A) blc).
{ intros blc. unfold ss_img. cbn [ss_mem].
eapply wr_ok_cons_win; [reflexivity | exact HE2 | cbn [r_wlo r_whi]; intros _; lia |].
eapply wr_ok_cons_win; [reflexivity | exact HE9 | cbn [r_wlo r_whi]; intros _; lia |].
eapply wr_ok_cons_win; [reflexivity | exact HE8 | cbn [r_wlo r_whi]; intros _; lia |].
apply wr_ok_nil. }
jrun_to LAWS src0tbl_ok HS HJ src0_A_malloc.
{ apply WROK. }
jreg HS (10%bv:reg) as Hr10. rewrite (HE 18%nat 18%bv eq_refl), G18 in Hr10.
jreg HS (2%bv:reg) as Hr2. rewrite (HE 2%nat 2%bv eq_refl), G2 in Hr2.
jreg HS (4%bv:reg) as Hr4. rewrite (HE 4%nat 4%bv eq_refl), G4, Htp0 in Hr4.
jreg HS (1%bv:reg) as Hr1.
eapply SR_bind.
{ eapply (jmalloc_at_res API IMG) with (n := N) (spc := sp - RFC_FRAME);
[ exact HS | reflexivity | reflexivity | exact HJ | exact Hid | exact Hr10 | exact HRq | exact HRm
| exact Hr2 | lia | exact Hspm | lia | lia | exact Hr4 | exact Hr1 | apply ret_ok_even; vm_compute; reflexivity ]. }
intros c' (L2 & A2 & regs2 & mem2 & md2 & res & -> & HJ2 & Hid2 & HP2 & Hres10 & Hres & Hkeep2 & Hhi2 & HR2). clear HJ.
change (ms_segs src0_msyms) with src0segs in Hkeep2, Hhi2.
jafter_call2 HS 42%nat regs2 mem2 HP2 0 [0%nat; 1%nat] HS2.
match type of HS2 with ?P -> _ => assert (HK : P); [|specialize (HS2 HK)] end.
{ constructor; [|constructor; [|constructor; [|constructor]]].
- eapply (region_kept_stack src0segs _ _ _ 2); [exact HE2 | exact Hhi2 | lia | lia | lia | cbn; lia | cbn; lia].
- eapply (region_kept_stack src0segs _ _ _ 9); [exact HE9 | exact Hhi2 | lia | lia | lia | cbn; lia | cbn; lia].
- eapply (region_kept_stack src0segs _ _ _ 8); [exact HE8 | exact Hhi2 | lia | lia | lia | cbn; lia | cbn; lia]. }
clear HS. rename HS2 into HS.
jreg HS (10%bv:reg) as Hq10. cbn [ms_regs mkst] in Hq10. rewrite Hres10 in Hq10. symmetry in Hq10.
destruct Hres as (Hnz & Hres16 & (b1 & b2 & Hbl2 & Hblc) & Hwr).
assert (Himg2 : In (res, N) (blocks L2 A2)) by (rewrite Hbl2; apply in_app_iff; right; left; reflexivity).
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HH2.
destruct (heap_blocks_range _ _ LAWS L2 A2 mem2 md2 res N HH2 Himg2 ltac:(lia)) as (Hi0 & Hi1 & _).
lazymatch type of HS with st_ok _ ?E1 ?ss1 ?ms1 =>
apply (st_ok_add_fact src0segs E1 ss1 ms1 46 (mkAF 4096 CEIL_MAX 4)) in HS;
[| unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite Hq10, unsigned_lit_small by lia; change (2 ^ 4) with 16; lia ] end.
lazymatch type of HS with st_ok _ _ ?ss1 _ => let v := eval vm_compute in ss1 in change ss1 with v in HS end.
jrun LAWS src0tbl_ok HS HJ2.
{ lazymatch goal with |- wr_ok ?E1 _ _ _ _ _ ?blc =>
eapply wr_ok_cons_win; [reflexivity | ew_havoc; exact HE2 | cbn [r_wlo r_whi]; intros _; lia |];
eapply wr_ok_cons_win; [reflexivity | ew_havoc; exact HE9 | cbn [r_wlo r_whi]; intros _; lia |];
eapply wr_ok_cons_win; [reflexivity | ew_havoc; exact HE8 | cbn [r_wlo r_whi]; intros _; lia |];
apply wr_ok_nil end. }
jbranch src0tbl HS.
*
rewrite branch_geu_U in Hc.
jrun_to LAWS src0tbl_ok HS HJ2 src0_A_memcpy.
{ lazymatch goal with |- wr_ok ?E1 _ _ _ _ _ ?blc =>
eapply wr_ok_cons_win; [reflexivity | ew_havoc; exact HE2 | cbn [r_wlo r_whi]; intros _; lia |];
eapply wr_ok_cons_win; [reflexivity | ew_havoc; exact HE9 | cbn [r_wlo r_whi]; intros _; lia |];
eapply wr_ok_cons_win; [reflexivity | ew_havoc; exact HE8 | cbn [r_wlo r_whi]; intros _; lia |];
apply wr_ok_nil end. }
jreg HS (10%bv:reg) as M10. rewrite Hq10 in M10.
jreg HS (11%bv:reg) as M11. rewrite (HX 38%nat 6%nat _ eq_refl eq_refl), (HX 40%nat 8%nat _ eq_refl eq_refl), alu64_add_lit in M11.
jreg HS (12%bv:reg) as M12. rewrite (HE 18%nat 18%bv eq_refl), G18 in M12.
jreg HS (1%bv:reg) as M1.
rewrite (U_atom _ 39 nb) in Hc by (first [lia | ew_havoc; rewrite (HX 39%nat 7%nat _ eq_refl eq_refl); reflexivity]).
rewrite U_SAlu in Hc. cbn [zalu_raw] in Hc.
rewrite (U_atom _ 18 N) in Hc by (first [lia | ew_havoc; rewrite (HE 18%nat 18%bv eq_refl); exact G18]).
rewrite (U_atom _ 40 cur) in Hc by (first [lia | ew_havoc; rewrite (HX 40%nat 8%nat _ eq_refl eq_refl); reflexivity]).
rewrite zcanon_id in Hc by (unfold M64; lia).
assert (Hfit : cur + N <= nb) by (destruct (Z.ltb_spec nb (N + cur)); [discriminate | lia]). clear Hc.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HHc. cbn [ms_mem mkst] in HHc.
eapply SR_bind.
{ eapply (jmemcpy _ _ LAWS IMG _ src0_memcpy) with (d := res) (src := pdata + cur) (n := N);
[ exact HS | reflexivity | reflexivity | exact HJ2 | exact M10 | exact M11
| exact M12 | exact M1 | apply ret_ok_even; vm_compute; reflexivity | lia | lia | lia | lia | lia | | | | ].
- intros i Hi. apply (proj1 (heap_blocks _ _ LAWS L2 A2 _ md2 res N i HHc Himg2 Hi)).
- intros i Hi. replace (pdata + cur + i) with (pdata + (cur + i)) by lia.
assert (Hpd2 : In (pdata, nb) (blocks L2 A2)) by (rewrite Hbl2; apply in_app_iff; destruct (in_app_or b1 b2 (pdata, nb) ltac:(rewrite <- Hblc; exact Hpdc)) as [H0|H0]; [left; exact H0 | right; right; exact H0]).
apply (proj1 (heap_blocks _ _ LAWS L2 A2 _ md2 pdata nb (cur + i) HHc Hpd2 ltac:(lia))).
-
destruct (heap_sep _ _ LAWS L2 A2 _ md2 b1 (res, N) b2 (pdata, nb) HHc Hbl2 ltac:(rewrite <- Hblc; exact Hpdc)) as [H0|H0]; cbn [fst snd] in H0; lia.
- intros a Ha. replace a with (res + (a - res)) by lia. apply (Hwr (blocks L2 A2)); [exact Himg2 | lia]. }
cbv beta. intros c' (regs3 & mem3 & -> & HJ3 & Hd10 & Hfr3 & Hout3 & Hgr3 & Hcp3).
jafter_stretch HS 60%nat regs3 mem3 MEMCPY_CLOB RA_IMC HS2.
match type of HS2 with ?P -> ?Q -> _ => assert (HKr : P); [| assert (HKm : Q); [| specialize (HS2 HKr HKm); clear HKr HKm]] end.
{ intros rr Hrr. apply Hfr3. exact Hrr. }
{ constructor; [|constructor; [|constructor; [|constructor]]].
- eapply region_kept_outside; [exact Hout3 | exact Hgr3 | cbn [r_base r_lo base_val]; ew_havoc; rewrite HE2; lia | cbn [r_base r_lo r_hi base_val]; ew_havoc; rewrite HE2; lia | cbn [r_base r_hi base_val]; ew_havoc; rewrite HE2; lia | cbn; lia | cbn; lia].
- eapply region_kept_outside; [exact Hout3 | exact Hgr3 | cbn [r_base r_lo base_val]; ew_havoc; rewrite HE9; lia | cbn [r_base r_lo r_hi base_val]; ew_havoc; rewrite HE9; lia | cbn [r_base r_hi base_val]; ew_havoc; rewrite HE9; lia | cbn; lia | cbn; lia].
- eapply region_kept_outside; [exact Hout3 | exact Hgr3 | cbn [r_base r_lo base_val]; ew_havoc; rewrite HE8; lia | cbn [r_base r_lo r_hi base_val]; ew_havoc; rewrite HE8; lia | cbn [r_base r_hi base_val]; ew_havoc; rewrite HE8; lia | cbn; lia | cbn; lia]. }
clear HS. rename HS2 into HS.
jrun_to LAWS src0tbl_ok HS HJ3 ORPC.
{ lazymatch goal with |- wr_ok ?E1 _ _ _ _ _ ?blc =>
eapply wr_ok_cons_win; [reflexivity | ew_havoc; exact HE2 | cbn [r_wlo r_whi]; intros _; lia |];
eapply wr_ok_cons_win; [reflexivity | ew_havoc; exact HE9 | cbn [r_wlo r_whi]; intros _; lia |];
eapply wr_ok_cons_win; [reflexivity | ew_havoc; exact HE8 | cbn [r_wlo r_whi]; intros _; lia |];
apply wr_ok_nil end. }
assert (HBnow : Permutation (blocks L2 A2) ((res, N) :: lpb ++ Bb)).
{ rewrite Hbl2. eapply Permutation_trans; [apply Permutation_sym; apply Permutation_middle|]. apply perm_skip. rewrite <- Hblc. exact HBc. }
destruct Hr as [-> | ->].
--
jrun LAWS src0tbl_ok HS HJ3.
{ lazymatch goal with |- wr_ok ?E1 _ _ _ _ _ ?blc =>
eapply wr_ok_cons_win; [reflexivity | ew_havoc; exact HE2 | cbn [r_wlo r_whi]; intros _; lia |];
eapply wr_ok_cons_win; [reflexivity | ew_havoc; exact HE9 | cbn [r_wlo r_whi]; intros _; lia |];
eapply wr_ok_cons_win; [reflexivity | ew_havoc; exact HE8 | cbn [r_wlo r_whi]; intros _; lia |];
apply wr_ok_nil end. }
eapply (SR_ret_at src0segs src0tbl); [exact src0tbl_ok | | | exact HS | reflexivity | vm_compute; reflexivity |].
{ exact (proj1 (heap_model _ _ LAWS _ _ _ _ (proj1 HJ3))). }
{ exact (proj1 (proj2 (heap_model _ _ LAWS _ _ _ _ (proj1 HJ3)))). }
rfc_img_post HS HJ3 Hid2 HX HE HE2 G3 G4 G24 G25 G26 G27 Hra0 1 (cur + N) res; cbn [ms_mem mkst] in *.
++ intros a Ha Hn1 Hn2 Hn3.
mb_frame HF3; try (rewrite ?HE2, ?HE9, ?HE8; lia).
mb_frame HF2; try (rewrite ?HE2, ?HE9, ?HE8; lia).
rewrite (mbyte_of_out _ _ res N a Hout3) by lia.
mb_frame HF1; try (rewrite ?HE2, ?HE9, ?HE8; lia).
mb_frame HF0; try (rewrite ?HE2, ?HE9, ?HE8; lia).
rewrite (proj1 (Hhi2 a Ha ltac:(lia))).
mb_frame HF; try (rewrite ?HE2, ?HE9, ?HE8; lia). reflexivity.
++ intros b m i Hb Hi.
assert (Hbc : In (b, m) (blocks Lc Ac)) by (eapply Permutation_in; [apply Permutation_sym; exact HBc | apply in_app_iff; right; exact Hb]).
destruct (heap_blocks _ _ LAWS Lc Ac mem1 mdc b m i HH Hbc Hi) as (_ & Hb0 & Hb1 & _).
destruct (heap_sep _ _ LAWS L2 A2 _ md2 b1 (res, N) b2 (b, m) HH2 Hbl2 ltac:(rewrite <- Hblc; exact Hbc)) as [Hs|Hs]; cbn [fst snd] in Hs.
all: mb_frame HF3; try (rewrite ?HE2, ?HE9, ?HE8; lia).
all: mb_frame HF2; try (rewrite ?HE2, ?HE9, ?HE8; lia).
all: rewrite (mbyte_of_out _ _ res N (b + i) Hout3) by lia.
all: mb_frame HF1; try (rewrite ?HE2, ?HE9, ?HE8; lia).
all: mb_frame HF0; try (rewrite ?HE2, ?HE9, ?HE8; lia).
all: rewrite (Hkeep2 b m i Hbc Hi).
all: mb_frame HF; try (rewrite ?HE2, ?HE9, ?HE8; lia); reflexivity.
++ eapply (st_chunk_word _ _ _ 1%nat _ 9%nat 16 _ st (cur + N) HS); [reflexivity | reflexivity | cbv; auto 10 | | | lia].
{ repeat (rewrite ew_havoc_old; [|cbv; lia]). exact HE9. }
{ cbn [sv_denot]. repeat (rewrite ew_havoc_old; [|cbv; lia]). rewrite !Z.add_0_r, (HE 18%nat 18%bv eq_refl), (HX 40%nat 8%nat _ eq_refl eq_refl), G18.
rewrite ?Z_to_bv_bv_unsigned, ?alu64_add_lit. f_equal. lia. }
++ split; [lia|]. right. split; [reflexivity|]. split; [reflexivity|].
split; [| split; [| split; [exact HBnow|]; split; [exact Hfit|]; split; [reflexivity|]; split; [| split; [| exact HR2]]]].
** rewrite <- (Z.add_0_r dst). eapply (st_chunk_word _ _ _ 2%nat _ 8%nat 0 _ dst lp HS); [reflexivity | reflexivity | cbv; auto 10 | | | lia].
{ repeat (rewrite ew_havoc_old; [|cbv; lia]). exact HE8. }
{ cbn [sv_denot]. repeat (rewrite ew_havoc_old; [|cbv; lia]). rewrite !Z.add_0_r, (HX 41%nat 9%nat _ eq_refl eq_refl), Z_to_bv_bv_unsigned. reflexivity. }
** replace (dst + 8) with (dst + 8) by reflexivity.
eapply (st_chunk_word _ _ _ 2%nat _ 8%nat 8 _ dst res HS); [reflexivity | reflexivity | cbv; auto 10 | | | lia].
{ repeat (rewrite ew_havoc_old; [|cbv; lia]). exact HE8. }
{ cbn [sv_denot]. repeat (rewrite ew_havoc_old; [|cbv; lia]). rewrite !Z.add_0_r, Hq10, Z_to_bv_bv_unsigned. reflexivity. }
**
intros b m i Hb Hi.
assert (Hbc : In (b, m) (blocks Lc Ac)) by (eapply Permutation_in; [apply Permutation_sym; exact HBc | apply in_app_iff; left; exact Hb]).
destruct (heap_blocks _ _ LAWS Lc Ac mem1 mdc b m i HH Hbc Hi) as (_ & Hb0 & Hb1 & _).
destruct (heap_sep _ _ LAWS L2 A2 _ md2 b1 (res, N) b2 (b, m) HH2 Hbl2 ltac:(rewrite <- Hblc; exact Hbc)) as [Hs|Hs]; cbn [fst snd] in Hs.
all: mb_frame HF3; try (rewrite ?HE2, ?HE9, ?HE8; lia).
all: mb_frame HF2; try (rewrite ?HE2, ?HE9, ?HE8; lia).
all: rewrite (mbyte_of_out _ _ res N (b + i) Hout3) by lia.
all: mb_frame HF1; try (rewrite ?HE2, ?HE9, ?HE8; lia).
all: mb_frame HF0; try (rewrite ?HE2, ?HE9, ?HE8; lia).
all: rewrite (Hkeep2 b m i Hbc Hi).
all: mb_frame HF; try (rewrite ?HE2, ?HE9, ?HE8; lia); reflexivity.
**
refine (proj1 (rx_garr8_slice_copy mem1 _ pdata PAYLOAD res cur N HPL ltac:(clear - Hcur; lia) ltac:(clear - HN; lia) ltac:(rewrite HPLn; exact Hfit) _)).
intros i Hi. change (ms_segs src0_msyms) with src0segs in Hcp3.
mb_frame HF3; try (rewrite ?HE2, ?HE9, ?HE8; lia).
mb_frame HF2; try (rewrite ?HE2, ?HE9, ?HE8; lia).
rewrite (Hcp3 i Hi).
mb_frame HF1; try (rewrite ?HE2, ?HE9, ?HE8; lia).
mb_frame HF0; try (rewrite ?HE2, ?HE9, ?HE8; lia).
replace (pdata + cur + i) with (pdata + (cur + i)) by lia. rewrite (Hkeep2 pdata nb (cur + i) Hpdc ltac:(lia)).
mb_frame HF; try (rewrite ?HE2, ?HE9, ?HE8; lia); reflexivity.
--
jrun_to LAWS src0tbl_ok HS HJ3 FREESPC.
{ lazymatch goal with |- wr_ok ?E1 _ _ _ _ _ ?blc =>
eapply wr_ok_cons_win; [reflexivity | ew_havoc; exact HE2 | cbn [r_wlo r_whi]; intros _; lia |];
eapply wr_ok_cons_win; [reflexivity | ew_havoc; exact HE9 | cbn [r_wlo r_whi]; intros _; lia |];
eapply wr_ok_cons_win; [reflexivity | ew_havoc; exact HE8 | cbn [r_wlo r_whi]; intros _; lia |];
apply wr_ok_nil end. }
frees_tac HS HJ3 HX HE HE2 HE8 Hbase Hra0 Htp0 Hal16 Hwlo Hwhi H63 Hdst1 Hdst2 Hdst8 G3 G4 G21 G22 G23 G24 G25 G26 G27 dst res N lp palsz lpb Bb (rb_malloc bq N);
[ exact HBnow
| intros Hin; apply (fresh_not_in API L2 A2 mem2 md2 b1 b2 res N HH2 Hbl2 ltac:(lia)); rewrite <- Hblc;
eapply Permutation_in; [apply Permutation_sym; exact HBc|]; apply in_app_iff; right; apply Hbase; exact Hin
| exact Hlp | exact Hlp64
| rewrite <- (Z.add_0_r dst); eapply (st_chunk_word _ _ _ 2%nat _ 8%nat 0 _ dst lp HS);
[ reflexivity | reflexivity | cbv; auto 10 | repeat (rewrite ew_havoc_old; [|cbv; lia]); exact HE8
| cbn [sv_denot]; repeat (rewrite ew_havoc_old; [|cbv; lia]); rewrite !Z.add_0_r, (HX 41%nat 9%nat _ eq_refl eq_refl), Z_to_bv_bv_unsigned; reflexivity | lia ]
| eapply (st_chunk_word _ _ _ 2%nat _ 8%nat 8 _ dst res HS);
[ reflexivity | reflexivity | cbv; auto 10 | repeat (rewrite ew_havoc_old; [|cbv; lia]); exact HE8
| cbn [sv_denot]; repeat (rewrite ew_havoc_old; [|cbv; lia]); rewrite !Z.add_0_r, Hq10, Z_to_bv_bv_unsigned; reflexivity | lia ]
| exact HR2
| ].
intros c' (L4 & A4 & regs4 & mem4 & md4 & -> & HJ4 & Hid4 & HP4 & Hq0 & Hhi4 & Hkeep4 & HB4 & HR4).
eexists L4, A4, regs4, mem4, md4. exists 0, (cur + N), 0.
split; [reflexivity|]. split; [exact HJ4|]. split; [exact Hid4|]. split; [exact HP4|]. split; [exact Hq0|].
split; [| split; [| split; [| split; [lia | left; split; [reflexivity|]; split; [exists []; exact HB4|]; split; [left; lia | exact HR4]]]]]; cbn [ms_mem mkst] in *.
++ intros a Ha Hn1 Hn2 Hn3. rewrite (Hhi4 a Ha Hn1).
mb_frame HF3; try (rewrite ?HE2, ?HE9, ?HE8; lia).
mb_frame HF2; try (rewrite ?HE2, ?HE9, ?HE8; lia).
rewrite (mbyte_of_out _ _ res N a Hout3) by lia.
mb_frame HF1; try (rewrite ?HE2, ?HE9, ?HE8; lia).
mb_frame HF0; try (rewrite ?HE2, ?HE9, ?HE8; lia).
rewrite (proj1 (Hhi2 a Ha ltac:(lia))).
mb_frame HF; try (rewrite ?HE2, ?HE9, ?HE8; lia). reflexivity.
++ intros b m i Hb Hi.
assert (Hbc : In (b, m) (blocks Lc Ac)) by (eapply Permutation_in; [apply Permutation_sym; exact HBc | apply in_app_iff; right; exact Hb]).
destruct (heap_blocks _ _ LAWS Lc Ac mem1 mdc b m i HH Hbc Hi) as (_ & Hb0 & Hb1 & _).
destruct (heap_sep _ _ LAWS L2 A2 _ md2 b1 (res, N) b2 (b, m) HH2 Hbl2 ltac:(rewrite <- Hblc; exact Hbc)) as [Hs|Hs]; cbn [fst snd] in Hs.
all: rewrite (Hkeep4 b m i Hb Hi).
all: mb_frame HF3; try (rewrite ?HE2, ?HE9, ?HE8; lia).
all: mb_frame HF2; try (rewrite ?HE2, ?HE9, ?HE8; lia).
all: rewrite (mbyte_of_out _ _ res N (b + i) Hout3) by lia.
all: mb_frame HF1; try (rewrite ?HE2, ?HE9, ?HE8; lia).
all: mb_frame HF0; try (rewrite ?HE2, ?HE9, ?HE8; lia).
all: rewrite (Hkeep2 b m i Hbc Hi).
all: mb_frame HF; try (rewrite ?HE2, ?HE9, ?HE8; lia); reflexivity.
++ eapply word_mem_frame; [| intros i Hi; apply Hhi4; lia].
replace (st + 16) with (st + 16) by reflexivity.
eapply (st_chunk_word _ _ _ 1%nat _ 9%nat 16 _ st (cur + N) HS); [reflexivity | reflexivity | cbv; auto 10 | | | lia].
{ repeat (rewrite ew_havoc_old; [|cbv; lia]). exact HE9. }
{ cbn [sv_denot]. repeat (rewrite ew_havoc_old; [|cbv; lia]). rewrite !Z.add_0_r, (HE 18%nat 18%bv eq_refl), (HX 40%nat 8%nat _ eq_refl eq_refl), G18.
rewrite ?Z_to_bv_bv_unsigned, ?alu64_add_lit. f_equal. lia. }
*
rewrite branch_geu_U in Hc.
rewrite (U_atom _ 39 nb) in Hc by (first [lia | ew_havoc; rewrite (HX 39%nat 7%nat _ eq_refl eq_refl); reflexivity]).
rewrite U_SAlu in Hc. cbn [zalu_raw] in Hc.
rewrite (U_atom _ 18 N) in Hc by (first [lia | ew_havoc; rewrite (HE 18%nat 18%bv eq_refl); exact G18]).
rewrite (U_atom _ 40 cur) in Hc by (first [lia | ew_havoc; rewrite (HX 40%nat 8%nat _ eq_refl eq_refl); reflexivity]).
rewrite zcanon_id in Hc by (unfold M64; lia).
assert (Hnfit : nb < cur + N) by (destruct (Z.ltb_spec nb (N + cur)); [lia | discriminate]). clear Hc.
jrun_to LAWS src0tbl_ok HS HJ2 ORPC.
{ lazymatch goal with |- wr_ok ?E1 _ _ _ _ _ ?blc =>
eapply wr_ok_cons_win; [reflexivity | ew_havoc; exact HE2 | cbn [r_wlo r_whi]; intros _; lia |];
eapply wr_ok_cons_win; [reflexivity | ew_havoc; exact HE9 | cbn [r_wlo r_whi]; intros _; lia |];
eapply wr_ok_cons_win; [reflexivity | ew_havoc; exact HE8 | cbn [r_wlo r_whi]; intros _; lia |];
apply wr_ok_nil end. }
destruct Hr as [-> | ->].
all: jrun_to LAWS src0tbl_ok HS HJ2 FREESPC;
[ eapply wr_ok_cons_win; [reflexivity | ew_havoc; exact HE2 | cbn [r_wlo r_whi]; intros _; lia |];
eapply wr_ok_cons_win; [reflexivity | ew_havoc; exact HE9 | cbn [r_wlo r_whi]; intros _; lia |];
eapply wr_ok_cons_win; [reflexivity | ew_havoc; exact HE8 | cbn [r_wlo r_whi]; intros _; lia |];
apply wr_ok_nil | ].
all: frees_tac HS HJ2 HX HE HE2 HE8 Hbase Hra0 Htp0 Hal16 Hwlo Hwhi H63 Hdst1 Hdst2 Hdst8 G3 G4 G21 G22 G23 G24 G25 G26 G27 dst res N lp palsz lpb Bb (rb_malloc bq N);
[ rewrite Hbl2; eapply Permutation_trans; [apply Permutation_sym; apply Permutation_middle|]; apply perm_skip; rewrite <- Hblc; exact HBc
| intros Hin; apply (fresh_not_in API L2 A2 mem2 md2 b1 b2 res N HH2 Hbl2 ltac:(lia)); rewrite <- Hblc;
eapply Permutation_in; [apply Permutation_sym; exact HBc|]; apply in_app_iff; right; apply Hbase; exact Hin
| exact Hlp | exact Hlp64
| rewrite <- (Z.add_0_r dst); eapply (st_chunk_word _ _ _ 2%nat _ 8%nat 0 _ dst lp HS);
[ reflexivity | reflexivity | cbv; auto 10 | repeat (rewrite ew_havoc_old; [|cbv; lia]); exact HE8
| cbn [sv_denot]; repeat (rewrite ew_havoc_old; [|cbv; lia]); rewrite !Z.add_0_r, (HX 41%nat 9%nat _ eq_refl eq_refl), Z_to_bv_bv_unsigned; reflexivity | lia ]
| eapply (st_chunk_word _ _ _ 2%nat _ 8%nat 8 _ dst res HS);
[ reflexivity | reflexivity | cbv; auto 10 | repeat (rewrite ew_havoc_old; [|cbv; lia]); exact HE8
| cbn [sv_denot]; repeat (rewrite ew_havoc_old; [|cbv; lia]); rewrite !Z.add_0_r, Hq10, Z_to_bv_bv_unsigned; reflexivity | lia ]
| exact HR2
| ].
all: intros c' (L4 & A4 & regs4 & mem4 & md4 & -> & HJ4 & Hid4 & HP4 & Hq0 & Hhi4 & Hkeep4 & HB4 & HR4);
eexists L4, A4, regs4, mem4, md4; exists 0, nb, 0;
split; [reflexivity|]; split; [exact HJ4|]; split; [exact Hid4|]; split; [exact HP4|]; split; [exact Hq0|];
split; [| split; [| split; [| split; [lia | left; split; [reflexivity|]; split; [exists []; exact HB4|]; split; [right; exact Hnfit | exact HR4]]]]];
cbn [ms_mem mkst] in *.
1,4: intros a Ha Hn1 Hn2 Hn3; rewrite (Hhi4 a Ha Hn1);
mb_frame HF2; try (rewrite ?HE2, ?HE9, ?HE8; lia);
mb_frame HF1; try (rewrite ?HE2, ?HE9, ?HE8; lia);
mb_frame HF0; try (rewrite ?HE2, ?HE9, ?HE8; lia);
rewrite (proj1 (Hhi2 a Ha ltac:(lia)));
mb_frame HF; try (rewrite ?HE2, ?HE9, ?HE8; lia); reflexivity.
1,3: intros b m i Hb Hi;
assert (Hbc : In (b, m) (blocks Lc Ac)) by (eapply Permutation_in; [apply Permutation_sym; exact HBc | apply in_app_iff; right; exact Hb]);
destruct (heap_blocks _ _ LAWS Lc Ac mem1 mdc b m i HH Hbc Hi) as (_ & Hb0 & Hb1 & _);
rewrite (Hkeep4 b m i Hb Hi);
mb_frame HF2; try (rewrite ?HE2, ?HE9, ?HE8; lia);
mb_frame HF1; try (rewrite ?HE2, ?HE9, ?HE8; lia);
mb_frame HF0; try (rewrite ?HE2, ?HE9, ?HE8; lia);
rewrite (Hkeep2 b m i Hbc Hi);
mb_frame HF; try (rewrite ?HE2, ?HE9, ?HE8; lia); reflexivity.
all: eapply word_mem_frame; [| intros i Hi; apply Hhi4; lia];
eapply (st_chunk_word _ _ _ 1%nat _ 9%nat 16 (SOff 39 0) st nb HS); [reflexivity | reflexivity | cbv; auto 10 | | | lia];
[ repeat (rewrite ew_havoc_old; [|cbv; lia]); exact HE9
| cbn [sv_denot]; repeat (rewrite ew_havoc_old; [|cbv; lia]); rewrite Z.add_0_r, (HX 39%nat 7%nat _ eq_refl eq_refl), Z_to_bv_bv_unsigned; reflexivity ].
Qed.
End S.
End e.
