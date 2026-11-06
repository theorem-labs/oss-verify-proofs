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
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0i YO0f YO0x YO0d YO0e.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YH00 YH03 YH02 YN3b YI06 YI5b YI09 YI08 YI0r YI1w YI5o YI5p.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma U_mul3_atom : forall E n x,
ew E n = Z_to_bv 64 x -> 0 <= x < 65536 -> U E (SMd M_MUL (SOff n 0) (SLit 3)) = 3 * x.
Proof.
intros E n x Hn Hx. rewrite U_SMd. cbn [zmd_raw]. rewrite (U_atom E n x Hn), U_SLit by lia.
change (zcanon 3) with 3. rewrite zcanon_id by (unfold M64; lia). lia.
Qed.
Lemma mul_div_mul3 : forall x, 0 <= x < 65536 -> mul_div M_MUL (Z_to_bv 64 x) (Z_to_bv 64 3) = Z_to_bv 64 (3 * x).
Proof.
intros x Hx. rewrite zmd64_sound. f_equal. unfold zmd64. cbn [zmd_raw].
rewrite (zcanon_id x), (zcanon_id 3) by (unfold M64; lia). rewrite zcanon_id by (unfold M64; lia). lia.
Qed.
Lemma denot_mul3_atom : forall E n x,
ew E n = Z_to_bv 64 x -> 0 <= x < 65536 -> sv_denot E (SMd M_MUL (SOff n 0) (SLit 3)) = Z_to_bv 64 (3 * x).
Proof. intros E n x Hn Hx. rewrite denot_lit_U. f_equal. apply U_mul3_atom; assumption. Qed.
Section S.
Variable API : AllocAPI src0_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws src0_msyms MR := aa_laws API.
Hypothesis IMG : img_laws src0_msyms MR.
Definition ss_pal (r : Z) : sstate :=
mkSS PALPC (sr_set sr_atoms 20%bv (SLit r))
[ YP09.mkRegion (Some 2%nat) 0 RFC_FRAME 0 RFC_FRAME
[mkChunk 40 (CVal 8 (SOff 32 0)); mkChunk 32 (CVal 8 (SOff 33 0)); mkChunk 24 (CVal 8 (SOff 34 0));
mkChunk 16 (CVal 8 (SOff 35 0)); mkChunk 8 (CVal 8 (SOff 36 0)); mkChunk 0 (CVal 8 (SOff 37 0))] ;
YP09.mkRegion (Some 9%nat) 0 24 16 24 [mkChunk 0 (CVal 8 (SOff 38 0)); mkChunk 8 (CVal 8 (SOff 39 0)); mkChunk 16 (CVal 8 (SOff 40 0))] ;
YP09.mkRegion (Some 8%nat) 0 32 0 16 [mkChunk 26 (CVal 2 (SOff 41 0))] ]
None
(mkFacts [ (2%nat, mkAF (CEIL_MIN + ALLOC_STACK) (2^63) 4); (9%nat, mkAF CEIL_MIN (2^63) 3);
(8%nat, mkAF CEIL_MIN (2^63) 3); (18%nat, mkAF 1 100000000 0);
(38%nat, mkAF 4096 CEIL_MAX 0); (39%nat, mkAF 1 CEIL_MAX 0);
(40%nat, mkAF 0 CEIL_MAX 0); (41%nat, mkAF 0 65535 0); (10%nat, mkAF 0 196605 0) ] [] []).
Definition pal_post (regs0 : bvmap 5 word) (STK sp0 : Z) (FP : list (Z * Z)) L A mem md
(Bb : list (Z * Z)) (st dst N nb cur palsz r : Z) (mem1 : word -> option byte) (c' : config) : Prop :=
exists L2 A2 regs2 mem2 md2 (res cur2 img lp : Z) (lpb : list (Z * Z)),
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
((res = 0 /\ exists leak, Permutation (blocks L2 A2) (leak ++ Bb)) \/
(res = 1 /\ r = 0 /\ word_mem src0segs mem2 dst lp /\ word_mem src0segs mem2 (dst + 8) img /\
(exists lpa, lpb = [(lpa, palsz)] /\ Z_to_bv 64 lpa = Z_to_bv 64 lp) /\
Permutation (blocks L2 A2) ((img, N) :: lpb ++ Bb))).
Lemma rfc_pal : forall r : Z, (r = 0 \/ r = 2 ^ 64 - 1) ->
forall STK sp0 FP L A mem md Lc Ac mdc (regs0 regs1 : bvmap 5 word) (mem1 : word -> option byte)
(Bb : list (Z * Z)) (st dst N pdata nb cur palsz nlp : Z),
journal src0_msyms MR STK sp0 FP L A mem md Lc Ac mem1 mdc -> st_init_done Ac = true ->
(forall b, In b (blocks L A) -> In b Bb) ->
Permutation (blocks Lc Ac) Bb ->
In (pdata, nb) Bb ->
0 <= nlp <= 65535 -> palsz = 3 * nlp ->
YK0s.ret_ok (getr regs0 1) -> getr regs0 4 = Z_to_bv 64 (ms_tp src0_msyms) ->
spZ regs0 mod 16 = 0 -> sp0 - STK <= spZ regs0 - RFC_DEPTH -> spZ regs0 <= sp0 ->
spZ regs0 <= st -> st + 24 <= sp0 -> spZ regs0 <= dst -> dst + 32 <= sp0 -> (st + 24 <= dst \/ dst + 32 <= st) ->
st mod 8 = 0 -> dst mod 8 = 0 -> sp0 < 2 ^ 63 ->
1 <= N <= 100000000 -> 0 <= cur <= nb -> 0 < nb ->
getr regs1 2 = Z_to_bv 64 (spZ regs0 - RFC_FRAME) -> getr regs1 3 = getr regs0 3 -> getr regs1 4 = getr regs0 4 ->
getr regs1 8 = Z_to_bv 64 dst -> getr regs1 9 = Z_to_bv 64 st -> getr regs1 18 = Z_to_bv 64 N ->
getr regs1 10 = Z_to_bv 64 palsz -> getr regs1 20 = Z_to_bv 64 r ->
getr regs1 21 = getr regs0 21 -> getr regs1 22 = getr regs0 22 -> getr regs1 23 = getr regs0 23 ->
getr regs1 24 = getr regs0 24 -> getr regs1 25 = getr regs0 25 -> getr regs1 26 = getr regs0 26 -> getr regs1 27 = getr regs0 27 ->
word_mem src0segs mem1 (spZ regs0 - 8) (bv_unsigned (getr regs0 1)) ->
word_mem src0segs mem1 (spZ regs0 - 16) (bv_unsigned (getr regs0 8)) ->
word_mem src0segs mem1 (spZ regs0 - 24) (bv_unsigned (getr regs0 9)) ->
word_mem src0segs mem1 (spZ regs0 - 32) (bv_unsigned (getr regs0 18)) ->
word_mem src0segs mem1 (spZ regs0 - 40) (bv_unsigned (getr regs0 19)) ->
word_mem src0segs mem1 (spZ regs0 - 48) (bv_unsigned (getr regs0 20)) ->
word_mem src0segs mem1 st pdata -> word_mem src0segs mem1 (st + 8) nb -> word_mem src0segs mem1 (st + 16) cur ->
val_mem src0segs mem1 (dst + 26) 2 nlp ->
SR src0segs (mkCfg (mkst regs1 (Z_to_bv 64 PALPC) mem1 (seg_rom src0segs)) mdc)
(pal_post regs0 STK sp0 FP L A mem md Bb st dst N nb cur palsz r mem1).
Proof.
intros r Hr STK sp0 FP L A mem md Lc Ac mdc regs0 regs1 mem1 Bb st dst N pdata nb cur palsz nlp
HJ Hid Hbase HBc Hpd Hnlp Hpznlp Hra0 Htp0 Hal16 Hwlo Hwhi Hst1 Hst2 Hdst1 Hdst2 Hsd Hst8 Hdst8 H63 HN Hcur Hnb
G2 G3 G4 G8 G9 G18 G10 G20 G21 G22 G23 G24 G25 G26 G27
W1 W8 W9 W18 W19 W20 Wp Wn Wc Wnlp.
assert (Hpz : 0 <= palsz <= 196605) by (clear - Hnlp Hpznlp; lia).
apply hideP_i in Hsd. apply hideP_i in Hr.
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HASv : ALLOC_STACK = 8192) by reflexivity.
assert (HFRv : RFC_FRAME = 48) by reflexivity. assert (HDPv : RFC_DEPTH = 8240) by reflexivity.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HH.
pose proof HJ as (_ & _ & _ & _ & _ & (Hsp0al & Hstk0 & Hceil & Hsp063 & Hstw) & _).
assert (Hpdc : In (pdata, nb) (blocks Lc Ac)) by (eapply Permutation_in; [apply Permutation_sym; exact HBc | exact Hpd]).
destruct (heap_blocks_range _ _ LAWS Lc Ac mem1 mdc pdata nb HH Hpdc ltac:(lia)) as (Hp0 & Hp1 & _).
set (sp := spZ regs0) in *.
assert (Hspm : (sp - RFC_FRAME) mod 16 = 0).
{ rewrite HFRv. replace (sp - 48) with (sp + (-3) * 16) by lia. rewrite Z.mod_add by lia. exact Hal16. }
set (extra := [getr regs0 1; getr regs0 8; getr regs0 9; getr regs0 18; getr regs0 19; getr regs0 20;
Z_to_bv 64 pdata; Z_to_bv 64 nb; Z_to_bv 64 cur; Z_to_bv 64 nlp]).
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew (Ereg regs1 extra) n = getr regs1 rr) by (intros; apply ew_Ereg_nat; assumption).
assert (HX : forall n j v, (n = 32 + j)%nat -> nth_error extra j = Some v -> ew (Ereg regs1 extra) n = v).
{ intros n j v -> Hj. rewrite ew_Ereg_extra. apply nth_error_nth. exact Hj. }
assert (HS : st_ok src0segs (Ereg regs1 extra) (ss_pal r) (mkst regs1 (Z_to_bv 64 PALPC) mem1 (seg_rom src0segs))).
{ unfold ss_pal. apply entry_st_ok_full.
- apply regs_ok_pin; [apply regs_ok_Ereg | intros H0; discriminate H0 |]. cbn [sv_denot]. exact G20.
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor; [|constructor]]].
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val].
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
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ nlp); [cbn [sv_denot]; rewrite Z.add_0_r, (HX 41%nat 9%nat _ eq_refl eq_refl), Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | exact Wnlp]. }
apply Forall_nil.
- unfold hideP in Hsd. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val].
rewrite (HE 2%nat 2%bv eq_refl), (HE 9%nat 9%bv eq_refl), (HE 8%nat 8%bv eq_refl), G2, G9, G8, !unsigned_lit_small by lia.
repeat split; lia.
- split; [| split; constructor].
cbn [atoms_ok f_atoms]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite (HE 2%nat 2%bv eq_refl), (HE 9%nat 9%bv eq_refl), (HE 8%nat 8%bv eq_refl), (HE 18%nat 18%bv eq_refl),
(HE 10%nat 10%bv eq_refl), (HX 38%nat 6%nat _ eq_refl eq_refl), (HX 39%nat 7%nat _ eq_refl eq_refl),
(HX 40%nat 8%nat _ eq_refl eq_refl), (HX 41%nat 9%nat _ eq_refl eq_refl),
G2, G9, G8, G18, G10, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 3) with 8. change (2 ^ 0) with 1.
rewrite ?Z.mod_1_r.
repeat split; try lia; assumption. }
change mem1 with (ms_mem (mkst regs1 (Z_to_bv 64 PALPC) mem1 (seg_rom src0segs))) in HJ.
assert (HE2 : bv_unsigned (ew (Ereg regs1 extra) 2) = sp - RFC_FRAME) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; lia).
assert (HE9 : bv_unsigned (ew (Ereg regs1 extra) 9) = st) by (rewrite (HE 9%nat 9%bv eq_refl), G9; apply unsigned_lit_small; lia).
assert (HE8 : bv_unsigned (ew (Ereg regs1 extra) 8) = dst) by (rewrite (HE 8%nat 8%bv eq_refl), G8; apply unsigned_lit_small; lia).
jrun_to LAWS src0tbl_ok HS HJ src0_A_malloc.
{ eapply wr_ok_cons_win; [reflexivity | exact HE2 | cbn [r_wlo r_whi]; intros _; clear - Hwlo Hwhi Hst1 Hst2 Hdst1 Hdst2 HFRv HDPv HASv; lia |].
eapply wr_ok_cons_win; [reflexivity | exact HE9 | cbn [r_wlo r_whi]; intros _; clear - Hwlo Hwhi Hst1 Hst2 Hdst1 Hdst2 HFRv HDPv HASv; lia |].
eapply wr_ok_cons_win; [reflexivity | exact HE8 | cbn [r_wlo r_whi]; intros _; clear - Hwlo Hwhi Hst1 Hst2 Hdst1 Hdst2 HFRv HDPv HASv; lia |]. apply wr_ok_nil. }
jreg HS (10%bv:reg) as Hr10. rewrite (HE 10%nat 10%bv eq_refl), G10 in Hr10.
jreg HS (2%bv:reg) as Hr2. rewrite (HE 2%nat 2%bv eq_refl), G2 in Hr2.
jreg HS (4%bv:reg) as Hr4. rewrite (HE 4%nat 4%bv eq_refl), G4, Htp0 in Hr4.
jreg HS (1%bv:reg) as Hr1.
eapply SR_bind.
{ eapply (jmalloc_at _ _ LAWS src0_errno_low IMG (aa_malloc API)) with (n := palsz) (spc := sp - RFC_FRAME);
[ exact HS | reflexivity | reflexivity | exact HJ | exact Hid | exact Hr10 | lia
| exact Hr2 | lia | exact Hspm | lia | lia | exact Hr4 | exact Hr1 | apply ret_ok_even; vm_compute; reflexivity ]. }
intros c' (L2 & A2 & regs2 & mem2 & md2 & res & -> & HJ2 & Hid2 & HP2 & Hres10 & Hres & Hkeep2 & Hhi2). clear HJ.
change (ms_segs src0_msyms) with src0segs in Hkeep2, Hhi2.
jafter_call2 HS 42%nat regs2 mem2 HP2 0 [0%nat; 1%nat] HS2.
match type of HS2 with ?P -> _ => assert (HK : P); [|specialize (HS2 HK)] end.
{ constructor; [|constructor; [|constructor; [|constructor]]].
- eapply (region_kept_stack src0segs _ _ _ 2); [exact HE2 | exact Hhi2 | lia | lia | lia | cbn; lia | cbn; lia].
- eapply (region_kept_stack src0segs _ _ _ 9); [exact HE9 | exact Hhi2 | lia | lia | lia | cbn; lia | cbn; lia].
- eapply (region_kept_stack src0segs _ _ _ 8); [exact HE8 | exact Hhi2 | lia | lia | lia | cbn; lia | cbn; lia]. }
clear HS. rename HS2 into HS.
jreg HS (10%bv:reg) as Hq10. cbn [ms_regs mkst] in Hq10. rewrite Hres10 in Hq10. symmetry in Hq10.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HH2.
assert (WR3 : forall E1 blc, bv_unsigned (ew E1 2) = sp - RFC_FRAME -> bv_unsigned (ew E1 9) = st -> bv_unsigned (ew E1 8) = dst ->
wr_ok E1 (ss_mem (ss_pal r)) STK sp0 FP (blocks L A) blc).
{ intros E1 blc E1a E1b E1c. unfold ss_pal. cbn [ss_mem].
eapply wr_ok_cons_win; [reflexivity | exact E1a | cbn [r_wlo r_whi]; intros _; clear - Hwlo Hwhi Hst1 Hst2 Hdst1 Hdst2 HFRv HDPv HASv; lia |].
eapply wr_ok_cons_win; [reflexivity | exact E1b | cbn [r_wlo r_whi]; intros _; clear - Hwlo Hwhi Hst1 Hst2 Hdst1 Hdst2 HFRv HDPv HASv; lia |].
eapply wr_ok_cons_win; [reflexivity | exact E1c | cbn [r_wlo r_whi]; intros _; clear - Hwlo Hwhi Hst1 Hst2 Hdst1 Hdst2 HFRv HDPv HASv; lia |]. apply wr_ok_nil. }
destruct Hres as [[-> Hbl] | (Hnz & Hres16 & (b1 & b2 & Hbl2 & Hblc) & Hwr)].
-
lazymatch type of HS with st_ok _ ?E1 ?ss1 ?ms1 =>
apply (st_ok_regs src0segs E1 ss1 ms1 (sr_set (ss_regs ss1) 10%bv (SLit 0))) in HS;
[| intros rr; destruct (decide (rr = 10%bv)) as [->|Hne];
[ rewrite sr_get_set_same by reflexivity;
match goal with |- _ = sv_denot _ ?v => let v' := eval vm_compute in v in change v with v' end;
cbn [sv_denot]; rewrite Z.add_0_r, Hq10, Z_to_bv_bv_unsigned; reflexivity
| rewrite sr_get_set_other by exact Hne; reflexivity ] ] end.
lazymatch type of HS with st_ok _ _ ?ss1 _ => let v := eval vm_compute in ss1 in change ss1 with v in HS end.
jrun LAWS src0tbl_ok HS HJ2.
{ wr3_tac_with HE2 HE9 HE8 ltac:(clear - Hwlo Hwhi Hst1 Hst2 Hdst1 Hdst2 HFRv HDPv HASv; lia). }
eapply (SR_ret_at src0segs src0tbl); [exact src0tbl_ok | | | exact HS | reflexivity | vm_compute; reflexivity |].
{ exact (proj1 (heap_model _ _ LAWS _ _ _ _ (proj1 HJ2))). }
{ exact (proj1 (proj2 (heap_model _ _ LAWS _ _ _ _ (proj1 HJ2)))). }
pal_post_tac HS HJ2 Hid2 HX HE HE2 G3 G4 G24 G25 G26 G27 Hra0 0 cur 0 0 (@nil (Z * Z)); cbn [ms_mem mkst] in *.
+ intros a Ha Hn1 Hn2 Hn3.
mbfA HF0 Ha Hn1 Hn2 Hn3 Hac HFRv HDPv HASv HE2 HE9 HE8.
rewrite (proj1 (Hhi2 a Ha ltac:(clear - Ha Hn1 HFRv HDPv HASv; lia))).
mbfA HF Ha Hn1 Hn2 Hn3 Hac HFRv HDPv HASv HE2 HE9 HE8. reflexivity.
+ intros b m i Hb Hi.
assert (Hbc : In (b, m) (blocks Lc Ac)) by (eapply Permutation_in; [apply Permutation_sym; exact HBc | exact Hb]).
destruct (heap_blocks _ _ LAWS Lc Ac mem1 mdc b m i HH Hbc Hi) as (_ & Hb0 & Hb1 & _).
mbfB HF0 Hb0 Hb1 Hi Hac Hceil Hwlo Hst1 Hdst1 HFRv HDPv HASv HE2 HE9 HE8.
rewrite (Hkeep2 b m i Hbc Hi).
mbfB HF Hb0 Hb1 Hi Hac Hceil Hwlo Hst1 Hdst1 HFRv HDPv HASv HE2 HE9 HE8. reflexivity.
+ eapply (st_chunk_word _ _ _ 1%nat _ 9%nat 16 (SOff 40 0) st cur HS); [reflexivity | reflexivity | cbv; auto 10 | | | lia].
{ ew_havocF. exact HE9. }
{ cbn [sv_denot]. ew_havocF. rewrite Z.add_0_r, (HX 40%nat 8%nat _ eq_refl eq_refl), Z_to_bv_bv_unsigned. reflexivity. }
+ split; [lia|]. left. split; [reflexivity|]. exists []. rewrite Hbl. exact HBc.
-
assert (Hlpin2 : In (res, palsz) (blocks L2 A2)) by (rewrite Hbl2; apply in_app_iff; right; left; reflexivity).
assert (HBnow : Permutation (blocks L2 A2) ([(res, palsz)] ++ Bb)).
{ rewrite Hbl2. eapply Permutation_trans; [apply Permutation_sym; apply Permutation_middle|]. cbn [app]. apply perm_skip. rewrite <- Hblc. exact HBc. }
assert (Hfresh : In (res, palsz) (blocks L A) -> palsz <= 0).
{ intros Hin. destruct (Z_le_gt_dec palsz 0) as [|Hgt]; [assumption|]. exfalso.
apply (fresh_not_in API L2 A2 mem2 md2 b1 b2 res palsz HH2 Hbl2 ltac:(lia)). rewrite <- Hblc.
eapply Permutation_in; [apply Permutation_sym; exact HBc|]. apply Hbase. exact Hin. }
jrun LAWS src0tbl_ok HS HJ2.
{ wr3_tac_with HE2 HE9 HE8 ltac:(clear - Hwlo Hwhi Hst1 Hst2 Hdst1 Hdst2 HFRv HDPv HASv; lia). }
jbranch src0tbl HS.
+
rewrite branch_eq_U, U_SLit, U_SOff, Z.add_0_r in Hc. apply Z.eqb_eq in Hc. change (zcanon 0) with 0 in Hc.
assert (H46z : ew (havoc (Ereg regs1 extra) 42 (map (getr regs2) CLOB)) 46 = Z_to_bv 64 0).
{ pose proof (bv_unsigned_in_range 64 (ew (havoc (Ereg regs1 extra) 42 (map (getr regs2) CLOB)) 46)) as R47.
change (bv_modulus 64) with (2 ^ 64) in R47. rewrite zcanon_id in Hc by (unfold M64; lia).
apply bv_eq. rewrite Hc. reflexivity. }
lazymatch type of HS with st_ok _ ?E1 ?ss1 ?ms1 =>
apply (st_ok_regs src0segs E1 ss1 ms1 (sr_set (ss_regs ss1) 10%bv (SLit 0))) in HS;
[| intros rr; destruct (decide (rr = 10%bv)) as [->|Hne];
[ rewrite sr_get_set_same by reflexivity;
match goal with |- _ = sv_denot _ ?v => let v' := eval vm_compute in v in change v with v' end;
cbn [sv_denot]; rewrite Z.add_0_r, H46z, Z_to_bv_bv_unsigned; reflexivity
| rewrite sr_get_set_other by exact Hne; reflexivity ] ] end.
lazymatch type of HS with st_ok _ _ ?ss1 _ => let v := eval vm_compute in ss1 in change ss1 with v in HS end.
jrun LAWS src0tbl_ok HS HJ2.
{ wr3_tac_with HE2 HE9 HE8 ltac:(clear - Hwlo Hwhi Hst1 Hst2 Hdst1 Hdst2 HFRv HDPv HASv; lia). }
eapply (SR_ret_at src0segs src0tbl); [exact src0tbl_ok | | | exact HS | reflexivity | vm_compute; reflexivity |].
{ exact (proj1 (heap_model _ _ LAWS _ _ _ _ (proj1 HJ2))). }
{ exact (proj1 (proj2 (heap_model _ _ LAWS _ _ _ _ (proj1 HJ2)))). }
pal_post_tac HS HJ2 Hid2 HX HE HE2 G3 G4 G24 G25 G26 G27 Hra0 0 cur 0 0 (@nil (Z * Z)); cbn [ms_mem mkst] in *.
* intros a Ha Hn1 Hn2 Hn3.
mbfA HF1 Ha Hn1 Hn2 Hn3 Hac HFRv HDPv HASv HE2 HE9 HE8.
mbfA HF0 Ha Hn1 Hn2 Hn3 Hac HFRv HDPv HASv HE2 HE9 HE8.
rewrite (proj1 (Hhi2 a Ha ltac:(clear - Ha Hn1 HFRv HDPv HASv; lia))).
mbfA HF Ha Hn1 Hn2 Hn3 Hac HFRv HDPv HASv HE2 HE9 HE8. reflexivity.
* intros b m i Hb Hi.
assert (Hbc : In (b, m) (blocks Lc Ac)) by (eapply Permutation_in; [apply Permutation_sym; exact HBc | exact Hb]).
destruct (heap_blocks _ _ LAWS Lc Ac mem1 mdc b m i HH Hbc Hi) as (_ & Hb0 & Hb1 & _).
mbfB HF1 Hb0 Hb1 Hi Hac Hceil Hwlo Hst1 Hdst1 HFRv HDPv HASv HE2 HE9 HE8.
mbfB HF0 Hb0 Hb1 Hi Hac Hceil Hwlo Hst1 Hdst1 HFRv HDPv HASv HE2 HE9 HE8.
rewrite (Hkeep2 b m i Hbc Hi).
mbfB HF Hb0 Hb1 Hi Hac Hceil Hwlo Hst1 Hdst1 HFRv HDPv HASv HE2 HE9 HE8. reflexivity.
* eapply (st_chunk_word _ _ _ 1%nat _ 9%nat 16 (SOff 40 0) st cur HS); [reflexivity | reflexivity | cbv; auto 10 | | | lia].
{ ew_havocF. exact HE9. }
{ cbn [sv_denot]. ew_havocF. rewrite Z.add_0_r, (HX 40%nat 8%nat _ eq_refl eq_refl), Z_to_bv_bv_unsigned. reflexivity. }
* split; [lia|]. left. split; [reflexivity|]. exists [(res, palsz)]. exact HBnow.
+
set (lp := bv_unsigned (ew (havoc (Ereg regs1 extra) 42 (map (getr regs2) CLOB)) 46)).
assert (Hlp64 : 0 <= lp < 2 ^ 64) by (pose proof (bv_unsigned_in_range 64 (ew (havoc (Ereg regs1 extra) 42 (map (getr regs2) CLOB)) 46)); change (bv_modulus 64) with (2 ^ 64) in *; lia).
assert (Hlpbv : Z_to_bv 64 res = Z_to_bv 64 lp) by (unfold lp; rewrite Z_to_bv_bv_unsigned, Hq10; reflexivity).
assert (Hlpres : 0 < palsz -> lp = res).
{ intros Hgt. destruct (heap_blocks_range _ _ LAWS L2 A2 mem2 md2 res palsz HH2 Hlpin2 ltac:(lia)) as (R0 & R1 & _).
unfold lp. rewrite Hq10, unsigned_lit_small by lia. reflexivity. }
jrun LAWS src0tbl_ok HS HJ2.
{ wr3_tac_with HE2 HE9 HE8 ltac:(clear - Hwlo Hwhi Hst1 Hst2 Hdst1 Hdst2 HFRv HDPv HASv; lia). }
assert (TOIMG : forall rr cur2 (msx : machine_state) (Ex : env) (ssx : sstate),
(rr = 0 \/ rr = 2 ^ 64 - 1) -> (rr = 0 -> r = 0) -> cur <= cur2 <= nb ->
st_ok src0segs Ex ssx msx -> ss_pc ssx = IMGPC -> ss_resv ssx = None ->
journal src0_msyms MR STK sp0 FP L A mem md L2 A2 (ms_mem msx) md2 ->
getr (ms_regs msx) 2 = Z_to_bv 64 (sp - RFC_FRAME) -> getr (ms_regs msx) 3 = getr regs0 3 -> getr (ms_regs msx) 4 = getr regs0 4 ->
getr (ms_regs msx) 8 = Z_to_bv 64 dst -> getr (ms_regs msx) 9 = Z_to_bv 64 st -> getr (ms_regs msx) 18 = Z_to_bv 64 N ->
getr (ms_regs msx) 20 = Z_to_bv 64 rr ->
getr (ms_regs msx) 21 = getr regs0 21 -> getr (ms_regs msx) 22 = getr regs0 22 -> getr (ms_regs msx) 23 = getr regs0 23 ->
getr (ms_regs msx) 24 = getr regs0 24 -> getr (ms_regs msx) 25 = getr regs0 25 -> getr (ms_regs msx) 26 = getr regs0 26 -> getr (ms_regs msx) 27 = getr regs0 27 ->
word_mem src0segs (ms_mem msx) (sp - 8) (bv_unsigned (getr regs0 1)) ->
word_mem src0segs (ms_mem msx) (sp - 16) (bv_unsigned (getr regs0 8)) ->
word_mem src0segs (ms_mem msx) (sp - 24) (bv_unsigned (getr regs0 9)) ->
word_mem src0segs (ms_mem msx) (sp - 32) (bv_unsigned (getr regs0 18)) ->
word_mem src0segs (ms_mem msx) (sp - 40) (bv_unsigned (getr regs0 19)) ->
word_mem src0segs (ms_mem msx) (sp - 48) (bv_unsigned (getr regs0 20)) ->
word_mem src0segs (ms_mem msx) st pdata -> word_mem src0segs (ms_mem msx) (st + 8) nb ->
word_mem src0segs (ms_mem msx) (st + 16) cur2 -> word_mem src0segs (ms_mem msx) dst lp ->
(forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp - RFC_DEPTH <= a < sp) -> ~ (dst <= a < dst + 16) -> ~ (st + 16 <= a < st + 24) ->
mbyte src0segs (ms_mem msx) a = mbyte src0segs mem1 a) ->
(forall b m i, In (b, m) Bb -> 0 <= i < m -> mbyte src0segs (ms_mem msx) (b + i) = mbyte src0segs mem1 (b + i)) ->
SR src0segs (mkCfg msx md2) (pal_post regs0 STK sp0 FP L A mem md Bb st dst N nb cur palsz r mem1)).
{ intros rr cur2 msx Ex ssx Hrr Hrr0 Hcur2 HSx Hpcx Hrvx HJx X2 X3 X4 X8 X9 X18 X20 X21 X22 X23 X24 X25 X26 X27 V1 V8 V9 V18 V19 V20 Vp Vn Vc Vl Hfr1 Hbk1.
rewrite (st_ok_mkst src0segs Ex ssx msx HSx Hrvx), Hpcx.
eapply SR_mono.
{ eapply (rfc_img API IMG rr Hrr STK sp0 FP L A mem md L2 A2 md2 regs0 (ms_regs msx) (ms_mem msx) Bb [(res, palsz)] st dst N pdata nb cur2 lp palsz HJx Hid2 Hbase HBnow Hpd);
try assumption; try lia.
right. exists res. split; [reflexivity|]. split; [exact Hlpbv|]. split; [exact Hfresh | lia]. }
cbv beta. intros c' (L4 & A4 & regs4 & mem4 & md4 & res' & cur4 & img & -> & HJ4 & Hid4 & HP4 & Hq0 & Hfr4 & Hbk4 & Hcw & Hc4 & Hres').
exists L4, A4, regs4, mem4, md4, res', cur4, img, lp, [(res, palsz)].
split; [reflexivity|]. split; [exact HJ4|]. split; [exact Hid4|]. split; [exact HP4|]. split; [exact Hq0|].
split; [intros a Ha Hn1 Hn2 Hn3; rewrite (Hfr4 a Ha Hn1 Hn2 Hn3); exact (Hfr1 a Ha Hn1 Hn2 Hn3)|].
split; [intros b m i Hb Hi; rewrite (Hbk4 b m i Hb Hi); exact (Hbk1 b m i Hb Hi)|].
split; [exact Hcw|]. split; [lia|].
destruct Hres' as [[-> Hleak] | (-> & -> & Hw1 & Hw2 & HPm)]; [left; auto | right].
split; [reflexivity|]. split; [apply Hrr0; reflexivity|]. split; [exact Hw1|]. split; [exact Hw2|]. split; [| exact HPm].
exists res. split; [reflexivity | exact Hlpbv]. }
clear Hc. jbranch src0tbl HS.
*
rewrite branch_geu_U in Hc.
rewrite (U_atom _ 39 nb) in Hc by (first [ew_havocF; rewrite (HX 39%nat 7%nat _ eq_refl eq_refl); reflexivity | lia]).
rewrite U_SAlu in Hc. cbn [zalu_raw] in Hc.
rewrite (U_mul3_atom _ 41 nlp) in Hc by (first [ew_havocF; rewrite (HX 41%nat 9%nat _ eq_refl eq_refl); reflexivity | lia]).
rewrite (U_atom _ 40 cur) in Hc by (first [ew_havocF; rewrite (HX 40%nat 8%nat _ eq_refl eq_refl); reflexivity | lia]).
rewrite zcanon_id in Hc by (unfold M64; lia).
assert (Hfit : cur + palsz <= nb) by (destruct (Z.ltb_spec nb (cur + 3 * nlp)); [discriminate | lia]). clear Hc.
jrun_to LAWS src0tbl_ok HS HJ2 src0_A_memcpy.
{ wr3_tac_with HE2 HE9 HE8 ltac:(clear - Hwlo Hwhi Hst1 Hst2 Hdst1 Hdst2 HFRv HDPv HASv; lia). }
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HHc. cbn [ms_mem mkst] in HHc.
assert (Hlpbound : palsz = 0 \/ (lp = res /\ 4096 <= res /\ res + palsz <= alloc_ceiling)).
{ destruct (Z_le_gt_dec palsz 0) as [Hz|Hgt]; [left; lia | right].
destruct (heap_blocks_range _ _ LAWS L2 A2 mem2 md2 res palsz HH2 Hlpin2 ltac:(lia)) as (R0 & R1 & _). split; [exact (Hlpres ltac:(lia)) | lia]. }
jreg HS (10%bv:reg) as M10. jreg HS (11%bv:reg) as M11. jreg HS (12%bv:reg) as M12. jreg HS (1%bv:reg) as M1.
rewrite (HX 38%nat 6%nat _ eq_refl eq_refl), (HX 40%nat 8%nat _ eq_refl eq_refl), alu64_add_lit in M11.
rewrite (HX 41%nat 9%nat _ eq_refl eq_refl), mul_div_mul3, <- Hpznlp in M12 by (clear - Hnlp; lia).
eapply SR_bind.
{ eapply (jmemcpy _ _ LAWS IMG _ src0_memcpy) with (d := lp) (src := pdata + cur) (n := palsz);
[ exact HS | reflexivity | reflexivity | exact HJ2 | rewrite M10; unfold lp; rewrite Z_to_bv_bv_unsigned; reflexivity | exact M11
| exact M12 | exact M1 | apply ret_ok_even; vm_compute; reflexivity | lia | lia | lia | lia | lia | | | | ].
- intros i Hi. rewrite (Hlpres ltac:(lia)). apply (proj1 (heap_blocks _ _ LAWS L2 A2 _ md2 res palsz i HHc Hlpin2 Hi)).
- intros i Hi. replace (pdata + cur + i) with (pdata + (cur + i)) by lia.
assert (Hpd2 : In (pdata, nb) (blocks L2 A2)) by (eapply Permutation_in; [apply Permutation_sym; exact HBnow | right; exact Hpd]).
apply (proj1 (heap_blocks _ _ LAWS L2 A2 _ md2 pdata nb (cur + i) HHc Hpd2 ltac:(lia))).
- destruct (Z_le_gt_dec palsz 0) as [Hz|Hgt]; [lia|]. rewrite (Hlpres ltac:(lia)).
destruct (heap_sep _ _ LAWS L2 A2 _ md2 b1 (res, palsz) b2 (pdata, nb) HHc Hbl2 ltac:(rewrite <- Hblc; exact Hpdc)) as [H0|H0]; cbn [fst snd] in H0; lia.
- intros a Ha. rewrite (Hlpres ltac:(lia)) in Ha. replace a with (res + (a - res)) by lia. apply (Hwr (blocks L2 A2)); [exact Hlpin2 | lia]. }
cbv beta. intros c' (regs3 & mem3 & -> & HJ3 & Hd10 & Hfr3 & Hout3 & Hgr3 & Hcp3).
assert (Hlpdis : forall a, alloc_ceiling <= a -> a < lp \/ lp + palsz <= a).
{ intros a Ha. destruct (Z_le_gt_dec palsz 0) as [Hz|Hgt]; [lia|]. rewrite (Hlpres ltac:(lia)).
destruct (heap_blocks_range _ _ LAWS L2 A2 mem2 md2 res palsz HH2 Hlpin2 ltac:(lia)). lia. }
jafter_stretch HS 60%nat regs3 mem3 MEMCPY_CLOB RA_PMC HS2.
match type of HS2 with ?P -> ?Q -> _ => assert (HKr : P); [| assert (HKm : Q); [| specialize (HS2 HKr HKm); clear HKr HKm]] end.
{ intros rr Hrr. apply Hfr3. exact Hrr. }
{ constructor; [|constructor; [|constructor; [|constructor]]].
- eapply region_kept_disj; [exact Hout3 | exact Hgr3 | cbn [r_base r_lo base_val]; ew_havocF; rewrite HE2; lia | cbn [r_base r_hi base_val]; ew_havocF; rewrite HE2; lia | cbn [r_base r_lo r_hi base_val]; ew_havocF; rewrite HE2; intros a Ha; apply Hlpdis; lia | cbn; lia | cbn; lia].
- eapply region_kept_disj; [exact Hout3 | exact Hgr3 | cbn [r_base r_lo base_val]; ew_havocF; rewrite HE9; lia | cbn [r_base r_hi base_val]; ew_havocF; rewrite HE9; lia | cbn [r_base r_lo r_hi base_val]; ew_havocF; rewrite HE9; intros a Ha; apply Hlpdis; lia | cbn; lia | cbn; lia].
- eapply region_kept_disj; [exact Hout3 | exact Hgr3 | cbn [r_base r_lo base_val]; ew_havocF; rewrite HE8; lia | cbn [r_base r_hi base_val]; ew_havocF; rewrite HE8; lia | cbn [r_base r_lo r_hi base_val]; ew_havocF; rewrite HE8; intros a Ha; apply Hlpdis; lia | cbn; lia | cbn; lia]. }
clear HS. rename HS2 into HS.
jrun_to LAWS src0tbl_ok HS HJ3 OR1PC.
{ wr3_tac_with HE2 HE9 HE8 ltac:(clear - Hwlo Hwhi Hst1 Hst2 Hdst1 Hdst2 HFRv HDPv HASv; lia). }
destruct Hr as [-> | ->].
all: jrun_to LAWS src0tbl_ok HS HJ3 IMGPC; [wr3_tac_with HE2 HE9 HE8 ltac:(clear - Hwlo Hwhi Hst1 Hst2 Hdst1 Hdst2 HFRv HDPv HASv; lia)|].
all: lazymatch goal with |- SR _ _ (pal_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?rv _) => eapply (TOIMG rv (cur + palsz)) end.
all: lazymatch goal with
| |- _ \/ _ => first [left; reflexivity | right; reflexivity | lia]
| |- _ = 0 -> _ = 0 => intros HH0; first [reflexivity | discriminate HH0 | lia]
| |- _ <= _ <= _ => lia
| |- st_ok _ _ _ _ => exact HS
| |- ss_pc _ = _ => reflexivity
| |- ss_resv _ = _ => reflexivity
| |- journal _ _ _ _ _ _ _ _ _ _ _ _ _ => exact HJ3
| |- _ => idtac
end.
all: cbn [ms_mem mkst] in *.
all: lazymatch goal with
| |- getr _ 2 = _ => reg_nowF HS ltac:(rewrite <- HE2, ?Z_to_bv_bv_unsigned; reflexivity)
| |- getr _ 3 = _ => reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 3%nat 3%bv eq_refl); exact G3)
| |- getr _ 4 = _ => reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 4%nat 4%bv eq_refl); exact G4)
| |- getr _ 8 = _ => reg_nowF HS ltac:(rewrite <- HE8, ?Z_to_bv_bv_unsigned; reflexivity)
| |- getr _ 9 = _ => reg_nowF HS ltac:(rewrite <- HE9, ?Z_to_bv_bv_unsigned; reflexivity)
| |- getr _ 18 = _ => reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 18%nat 18%bv eq_refl); exact G18)
| |- getr _ 20 = _ => reg_nowF HS ltac:(first [reflexivity | apply bv_eq; vm_compute; reflexivity])
| |- getr _ 21 = _ => reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 21%nat 21%bv eq_refl); exact G21)
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
| |- word_mem _ _ (?bb + 8) _ => eapply (st_chunk_word _ _ _ 1%nat _ 9%nat 8 (SOff 39 0) bb _ HS);
[ reflexivity | reflexivity | cbv; auto 12 | ew_havocF; exact HE9
| cbn [sv_denot]; ew_havocF; rewrite Z.add_0_r, (HX 39%nat 7%nat _ eq_refl eq_refl), Z_to_bv_bv_unsigned; reflexivity | lia ]
| |- word_mem _ _ (?bb + 16) _ => eapply (st_chunk_word _ _ _ 1%nat _ 9%nat 16 _ bb _ HS);
[ reflexivity | reflexivity | cbv; auto 12 | ew_havocF; exact HE9
| cbn [sv_denot]; ew_havocF; rewrite ?Z.add_0_r, (HX 40%nat 8%nat _ eq_refl eq_refl), (HX 41%nat 9%nat _ eq_refl eq_refl), ?Z_to_bv_bv_unsigned;
rewrite mul_div_mul3 by (clear - Hnlp; lia); rewrite alu64_add_lit, <- Hpznlp; reflexivity
| lia ]
| |- word_mem _ _ ?bb ?vv =>
tryif constr_eq vv pdata then
(rewrite <- (Z.add_0_r bb); eapply (st_chunk_word _ _ _ 1%nat _ 9%nat 0 (SOff 38 0) bb _ HS);
[ reflexivity | reflexivity | cbv; auto 12 | ew_havocF; exact HE9
| cbn [sv_denot]; ew_havocF; rewrite Z.add_0_r, (HX 38%nat 6%nat _ eq_refl eq_refl), Z_to_bv_bv_unsigned; reflexivity | lia ])
else
(rewrite <- (Z.add_0_r bb); eapply (st_chunk_word _ _ _ 2%nat _ 8%nat 0 (SOff 46 0) bb _ HS);
[ reflexivity | reflexivity | cbv; auto 12 | ew_havocF; exact HE8
| cbn [sv_denot]; ew_havocF; rewrite Z.add_0_r; unfold lp; rewrite Z_to_bv_bv_unsigned; reflexivity | lia ])
| |- _ => idtac
end.
all: lazymatch goal with
| |- forall a : Z, alloc_ceiling <= a < _ -> _ =>
intros a Ha Hn1 Hn2 Hn3;
mbfA HF4 Ha Hn1 Hn2 Hn3 Hac HFRv HDPv HASv HE2 HE9 HE8;
mbfA HF3 Ha Hn1 Hn2 Hn3 Hac HFRv HDPv HASv HE2 HE9 HE8;
(rewrite (mbyte_of_out _ _ lp palsz a Hout3); [| clear - Ha Hac; lia | apply Hlpdis; clear - Ha; lia]);
mbfA HF2 Ha Hn1 Hn2 Hn3 Hac HFRv HDPv HASv HE2 HE9 HE8;
mbfA HF1 Ha Hn1 Hn2 Hn3 Hac HFRv HDPv HASv HE2 HE9 HE8;
mbfA HF0 Ha Hn1 Hn2 Hn3 Hac HFRv HDPv HASv HE2 HE9 HE8;
rewrite (proj1 (Hhi2 a Ha ltac:(clear - Ha Hn1 HFRv HDPv HASv; lia)));
mbfA HF Ha Hn1 Hn2 Hn3 Hac HFRv HDPv HASv HE2 HE9 HE8; reflexivity
| |- forall (b m i : Z), In (b, m) _ -> _ =>
intros b m i Hb Hi;
assert (Hbc : In (b, m) (blocks Lc Ac)) by (eapply Permutation_in; [apply Permutation_sym; exact HBc | exact Hb]);
destruct (heap_blocks _ _ LAWS Lc Ac mem1 mdc b m i HH Hbc Hi) as (_ & Hb0 & Hb1 & _);
destruct (heap_sep _ _ LAWS L2 A2 _ md2 b1 (res, palsz) b2 (b, m) HH2 Hbl2 ltac:(rewrite <- Hblc; exact Hbc)) as [Hs|Hs]; cbn [fst snd] in Hs;
mbfB HF4 Hb0 Hb1 Hi Hac Hceil Hwlo Hst1 Hdst1 HFRv HDPv HASv HE2 HE9 HE8;
mbfB HF3 Hb0 Hb1 Hi Hac Hceil Hwlo Hst1 Hdst1 HFRv HDPv HASv HE2 HE9 HE8;
(rewrite (mbyte_of_out _ _ lp palsz (b + i) Hout3); [| clear - Hb0 Hb1 Hi Hac; lia | destruct Hlpbound as [Hz | (Hl & _ & _)]; [clear - Hz; lia | rewrite Hl; clear - Hs Hi; lia]]);
mbfB HF2 Hb0 Hb1 Hi Hac Hceil Hwlo Hst1 Hdst1 HFRv HDPv HASv HE2 HE9 HE8;
mbfB HF1 Hb0 Hb1 Hi Hac Hceil Hwlo Hst1 Hdst1 HFRv HDPv HASv HE2 HE9 HE8;
mbfB HF0 Hb0 Hb1 Hi Hac Hceil Hwlo Hst1 Hdst1 HFRv HDPv HASv HE2 HE9 HE8;
rewrite (Hkeep2 b m i Hbc Hi);
mbfB HF Hb0 Hb1 Hi Hac Hceil Hwlo Hst1 Hdst1 HFRv HDPv HASv HE2 HE9 HE8; reflexivity
| |- ?G => idtac "LEFTOVER"; idtac G
end.
*
rewrite branch_geu_U in Hc.
jrun_to LAWS src0tbl_ok HS HJ2 OR1PC.
{ wr3_tac_with HE2 HE9 HE8 ltac:(clear - Hwlo Hwhi Hst1 Hst2 Hdst1 Hdst2 HFRv HDPv HASv; lia). }
destruct Hr as [-> | ->].
all: jrun_to LAWS src0tbl_ok HS HJ2 IMGPC; [wr3_tac_with HE2 HE9 HE8 ltac:(clear - Hwlo Hwhi Hst1 Hst2 Hdst1 Hdst2 HFRv HDPv HASv; lia)|].
all: eapply (TOIMG (2 ^ 64 - 1) nb).
all: lazymatch goal with
| |- _ \/ _ => first [left; reflexivity | right; reflexivity | lia]
| |- _ = 0 -> _ = 0 => intros HH0; first [reflexivity | discriminate HH0 | lia]
| |- _ <= _ <= _ => lia
| |- st_ok _ _ _ _ => exact HS
| |- ss_pc _ = _ => reflexivity
| |- ss_resv _ = _ => reflexivity
| |- journal _ _ _ _ _ _ _ _ _ _ _ _ _ => exact HJ2
| |- _ => idtac
end.
all: cbn [ms_mem mkst] in *.
all: lazymatch goal with
| |- getr _ 2 = _ => reg_nowF HS ltac:(rewrite <- HE2, ?Z_to_bv_bv_unsigned; reflexivity)
| |- getr _ 3 = _ => reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 3%nat 3%bv eq_refl); exact G3)
| |- getr _ 4 = _ => reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 4%nat 4%bv eq_refl); exact G4)
| |- getr _ 8 = _ => reg_nowF HS ltac:(rewrite <- HE8, ?Z_to_bv_bv_unsigned; reflexivity)
| |- getr _ 9 = _ => reg_nowF HS ltac:(rewrite <- HE9, ?Z_to_bv_bv_unsigned; reflexivity)
| |- getr _ 18 = _ => reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 18%nat 18%bv eq_refl); exact G18)
| |- getr _ 20 = _ => reg_nowF HS ltac:(first [reflexivity | apply bv_eq; vm_compute; reflexivity])
| |- getr _ 21 = _ => reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 21%nat 21%bv eq_refl); exact G21)
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
| |- word_mem _ _ (?bb + 8) _ => eapply (st_chunk_word _ _ _ 1%nat _ 9%nat 8 (SOff 39 0) bb _ HS);
[ reflexivity | reflexivity | cbv; auto 12 | ew_havocF; exact HE9
| cbn [sv_denot]; ew_havocF; rewrite Z.add_0_r, (HX 39%nat 7%nat _ eq_refl eq_refl), Z_to_bv_bv_unsigned; reflexivity | lia ]
| |- word_mem _ _ (?bb + 16) _ => eapply (st_chunk_word _ _ _ 1%nat _ 9%nat 16 (SOff 39 0) bb _ HS);
[ reflexivity | reflexivity | cbv; auto 12 | ew_havocF; exact HE9
| cbn [sv_denot]; ew_havocF; rewrite Z.add_0_r, (HX 39%nat 7%nat _ eq_refl eq_refl), Z_to_bv_bv_unsigned; reflexivity | lia ]
| |- word_mem _ _ ?bb ?vv =>
tryif constr_eq vv pdata then
(rewrite <- (Z.add_0_r bb); eapply (st_chunk_word _ _ _ 1%nat _ 9%nat 0 (SOff 38 0) bb _ HS);
[ reflexivity | reflexivity | cbv; auto 12 | ew_havocF; exact HE9
| cbn [sv_denot]; ew_havocF; rewrite Z.add_0_r, (HX 38%nat 6%nat _ eq_refl eq_refl), Z_to_bv_bv_unsigned; reflexivity | lia ])
else
(rewrite <- (Z.add_0_r bb); eapply (st_chunk_word _ _ _ 2%nat _ 8%nat 0 (SOff 46 0) bb _ HS);
[ reflexivity | reflexivity | cbv; auto 12 | ew_havocF; exact HE8
| cbn [sv_denot]; ew_havocF; rewrite Z.add_0_r; unfold lp; rewrite Z_to_bv_bv_unsigned; reflexivity | lia ])
| |- _ => idtac
end.
all: lazymatch goal with
| |- forall a : Z, alloc_ceiling <= a < _ -> _ =>
intros a Ha Hn1 Hn2 Hn3;
mbfA HF3 Ha Hn1 Hn2 Hn3 Hac HFRv HDPv HASv HE2 HE9 HE8;
mbfA HF2 Ha Hn1 Hn2 Hn3 Hac HFRv HDPv HASv HE2 HE9 HE8;
mbfA HF1 Ha Hn1 Hn2 Hn3 Hac HFRv HDPv HASv HE2 HE9 HE8;
mbfA HF0 Ha Hn1 Hn2 Hn3 Hac HFRv HDPv HASv HE2 HE9 HE8;
rewrite (proj1 (Hhi2 a Ha ltac:(clear - Ha Hn1 HFRv HDPv HASv; lia)));
mbfA HF Ha Hn1 Hn2 Hn3 Hac HFRv HDPv HASv HE2 HE9 HE8; reflexivity
| |- forall (b m i : Z), In (b, m) _ -> _ =>
intros b m i Hb Hi;
assert (Hbc : In (b, m) (blocks Lc Ac)) by (eapply Permutation_in; [apply Permutation_sym; exact HBc | exact Hb]);
destruct (heap_blocks _ _ LAWS Lc Ac mem1 mdc b m i HH Hbc Hi) as (_ & Hb0 & Hb1 & _);
mbfB HF3 Hb0 Hb1 Hi Hac Hceil Hwlo Hst1 Hdst1 HFRv HDPv HASv HE2 HE9 HE8;
mbfB HF2 Hb0 Hb1 Hi Hac Hceil Hwlo Hst1 Hdst1 HFRv HDPv HASv HE2 HE9 HE8;
mbfB HF1 Hb0 Hb1 Hi Hac Hceil Hwlo Hst1 Hdst1 HFRv HDPv HASv HE2 HE9 HE8;
mbfB HF0 Hb0 Hb1 Hi Hac Hceil Hwlo Hst1 Hdst1 HFRv HDPv HASv HE2 HE9 HE8;
rewrite (Hkeep2 b m i Hbc Hi);
mbfB HF Hb0 Hb1 Hi Hac Hceil Hwlo Hst1 Hdst1 HFRv HDPv HASv HE2 HE9 HE8; reflexivity
| |- ?G => idtac "LEFTOVER"; idtac G
end.
Qed.
End S.
End c.
