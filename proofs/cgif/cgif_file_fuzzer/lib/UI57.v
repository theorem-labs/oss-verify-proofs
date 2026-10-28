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
YO03 YO0p YO0j YO0m YO0l YO0n YO0k YO0o.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UH00 UH03 UH02 UN3b YI06 UI5b YI09 YI08 YI0r UI1w UI5o
YI00 YI05 YI5a UI5f UI56 UIZs.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma U_mul3_atom : forall E n x,
ew E n = Z_to_bv 64 x -> 0 <= x < 65536 -> U E (SMd M_MUL (SOff n 0) (SLit 3)) = 3 * x.
Proof using.
intros E n x Hn Hx. rewrite U_SMd. cbn [zmd_raw]. rewrite (U_atom E n x Hn), U_SLit by lia.
change (zcanon 3) with 3. rewrite zcanon_id by (unfold M64; lia). lia.
Qed.
Lemma mul_div_mul3 : forall x, 0 <= x < 65536 -> mul_div M_MUL (Z_to_bv 64 x) (Z_to_bv 64 3) = Z_to_bv 64 (3 * x).
Proof using.
intros x Hx. rewrite zmd64_sound. f_equal. unfold zmd64. cbn [zmd_raw].
rewrite (zcanon_id x), (zcanon_id 3) by (unfold M64; lia). rewrite zcanon_id by (unfold M64; lia). lia.
Qed.
Lemma denot_mul3_atom : forall E n x,
ew E n = Z_to_bv 64 x -> 0 <= x < 65536 -> sv_denot E (SMd M_MUL (SOff n 0) (SLit 3)) = Z_to_bv 64 (3 * x).
Proof using. intros E n x Hn Hx. rewrite denot_lit_U. f_equal. apply U_mul3_atom; assumption. Qed.
Lemma rb_malloc_small_acc : forall b n x, 0 <= n -> n <= 196605 -> 0 <= x -> rb_le (rb_malloc b n) (rb_acc b 1 x).
Proof using.
intros b n x Hn Hle Hx. unfold rb_le, rb_malloc, rb_acc, mdelta. cbn [rb_bytes rb_cnt rb_hand rb_brk].
pose proof (page_round_bounds (n + IB + UNIT)) as Hp. unfold MMAP_THRESHOLD, IB, UNIT, MMAX, PGSZ in *.
destruct (131052 <=? n); lia.
Qed.
Lemma rb_free_malloc_acc : forall b n x, 0 <= n -> 0 <= x -> rb_le (rb_free (rb_malloc b n) n) (rb_acc b 1 x).
Proof using.
intros b n x Hn Hx. unfold rb_le, rb_free, rb_malloc, rb_acc, mdelta. cbn [rb_bytes rb_cnt rb_hand rb_brk].
pose proof (page_round_bounds (n + IB + UNIT)) as Hp. unfold MMAP_THRESHOLD, IB, UNIT, MMAX, PGSZ in *.
destruct (Z.ltb_spec 131052 n); destruct (Z.leb_spec 131052 n); cbn [rb_bytes rb_cnt rb_hand rb_brk]; lia.
Qed.
Lemma rfc_room_pal : forall b N palsz, rfc_room b N -> 0 <= palsz <= 196605 -> room b palsz.
Proof using.
intros b N palsz HR Hp. apply (room_mono b (rb_acc b 1 PALSLACK) palsz (Z.max N PALMAX)); [apply rb_acc_le; unfold PALSLACK; lia | unfold PALMAX; lia | exact HR].
Qed.
Lemma rfc_room_img : forall b N palsz, rfc_room b N -> 0 <= palsz <= 196605 -> 0 <= N -> room (rb_malloc b palsz) N.
Proof using.
intros b N palsz HR Hp HN. apply (room_mono (rb_malloc b palsz) (rb_acc b 1 PALSLACK) N (Z.max N PALMAX)); [| lia | exact HR].
apply rb_malloc_small_acc; unfold PALSLACK; lia.
Qed.
Lemma rfc_fail_of_pal : forall b palsz N, 0 <= palsz <= 196605 -> 0 <= N -> rb_le (rb_free (rb_malloc (rb_malloc b palsz) N) N) (rfc_rb_fail b).
Proof using.
intros b palsz N Hp HN. unfold rfc_rb_fail. apply (rb_le_trans _ (rb_acc (rb_malloc b palsz) 1 0)); [apply rb_free_malloc_acc; lia|].
replace (rb_acc b 2 0) with (rb_acc (rb_acc b 1 0) 1 0) by (rewrite rb_acc_acc; reflexivity).
apply rb_acc_mono; [apply rb_malloc_small_acc; lia | lia | lia].
Qed.
Section S.
Variable API : AllocAPI ubs0_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs0_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs0_msyms MR.
Lemma heap_blocks_range0 : forall L A mem md a n,
heap_ok MR L A mem md -> In (a, n) (blocks L A) -> 4096 <= a /\ a + n <= alloc_ceiling.
Proof using LAWS.
intros L A mem md a n (HM & _) Hin. apply blocks_In in Hin as (p & <- & Hin).
exact (mr_blocks_range _ _ LAWS L A mem md p n HM Hin).
Qed.
Definition ss_pal (r : Z) : sstate :=
mkSS PALPC (sr_set (sr_set sr_atoms 20%bv (SLit r)) 19%bv (SOff 8 26))
[ YP09.mkRegion (Some 2%nat) 0 RFC_FRAME 0 RFC_FRAME
[mkChunk 56 (CVal 8 (SOff 32 0)); mkChunk 48 (CVal 8 (SOff 33 0)); mkChunk 40 (CVal 8 (SOff 34 0)); mkChunk 32 (CVal 8 (SOff 35 0));
mkChunk 24 (CVal 8 (SOff 36 0)); mkChunk 16 (CVal 8 (SOff 37 0)); mkChunk 8 (CVal 8 (SOff 38 0))] ;
YP09.mkRegion (Some 18%nat) 0 24 16 24 [mkChunk 0 (CVal 8 (SOff 39 0)); mkChunk 8 (CVal 8 (SOff 40 0)); mkChunk 16 (CVal 8 (SOff 41 0))] ;
YP09.mkRegion (Some 8%nat) 0 32 0 16 [mkChunk 26 (CVal 2 (SOff 42 0))] ]
None
(mkFacts [ (2%nat, mkAF (CEIL_MIN + ALLOC_STACK) (2^63) 4); (18%nat, mkAF CEIL_MIN (2^63) 3);
(8%nat, mkAF CEIL_MIN (2^63) 3); (9%nat, mkAF 1 100000000 0);
(39%nat, mkAF 4096 CEIL_MAX 0); (40%nat, mkAF 1 CEIL_MAX 0);
(41%nat, mkAF 0 CEIL_MAX 0); (42%nat, mkAF 0 65535 0) ] [] []).
Definition pal_post_x (regs0 : bvmap 5 word) (STK sp0 : Z) (FP : list (Z * Z)) L A mem md
(Bb : list (Z * Z)) (st dst N nb cur palsz r : Z) (mem1 : word -> option byte)
(pdata : Z) (PAYLOAD : list Z) (bq : rbound) (c' : config) : Prop :=
exists L2 A2 regs2 mem2 md2 (res cur2 img lp : Z) (lpb : list (Z * Z)),
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
((res = 0 /\ (exists leak, Permutation (blocks L2 A2) (leak ++ Bb)) /\ (r <> 0 \/ nb < cur + palsz + N) /\ res_ok A2 (rfc_rb_fail bq)) \/
(res = 1 /\ r = 0 /\ word_mem ubs0segs mem2 dst lp /\ word_mem ubs0segs mem2 (dst + 8) img /\
(exists lpa, lpb = [(lpa, palsz)] /\ Z_to_bv 64 lpa = Z_to_bv 64 lp /\
garr8 ubs0segs mem2 lpa (firstn (Z.to_nat palsz) (skipn (Z.to_nat cur) PAYLOAD))) /\
Permutation (blocks L2 A2) ((img, N) :: lpb ++ Bb) /\
cur + palsz + N <= nb /\ cur2 = cur + palsz + N /\
garr8 ubs0segs mem2 img (firstn (Z.to_nat N) (skipn (Z.to_nat (cur + palsz)) PAYLOAD)) /\
res_ok A2 (rb_malloc (rb_malloc bq palsz) N))).
Lemma rfc_pal_x : forall r : Z, (r = 0 \/ r = 2 ^ 64 - 1) ->
forall STK sp0 FP L A mem md Lc Ac mdc (regs0 regs1 : bvmap 5 word) (mem1 : word -> option byte)
(Bb : list (Z * Z)) (st dst N pdata nb cur palsz nlp : Z) (PAYLOAD : list Z) (bq : rbound),
journal ubs0_msyms MR STK sp0 FP L A mem md Lc Ac mem1 mdc -> st_init_done Ac = true ->
(forall b, In b (blocks L A) -> In b Bb) ->
Permutation (blocks Lc Ac) Bb ->
In (pdata, nb) Bb ->
0 <= nlp <= 65535 -> palsz = 3 * nlp ->
YK0s.ret_ok (getr regs0 1) -> getr regs0 4 = Z_to_bv 64 (ms_tp ubs0_msyms) ->
spZ regs0 mod 16 = 0 -> sp0 - STK <= spZ regs0 - RFC_DEPTH -> spZ regs0 <= sp0 ->
spZ regs0 <= st -> st + 24 <= sp0 -> spZ regs0 <= dst -> dst + 32 <= sp0 -> (st + 24 <= dst \/ dst + 32 <= st) ->
st mod 8 = 0 -> dst mod 8 = 0 -> sp0 < 2 ^ 63 ->
1 <= N <= 100000000 -> 0 <= cur <= nb -> 0 < nb ->
getr regs1 2 = Z_to_bv 64 (spZ regs0 - RFC_FRAME) -> getr regs1 3 = getr regs0 3 -> getr regs1 4 = getr regs0 4 ->
getr regs1 8 = Z_to_bv 64 dst -> getr regs1 9 = Z_to_bv 64 N -> getr regs1 18 = Z_to_bv 64 st ->
getr regs1 19 = Z_to_bv 64 (dst + 26) -> getr regs1 20 = Z_to_bv 64 r ->
getr regs1 22 = getr regs0 22 -> getr regs1 23 = getr regs0 23 ->
getr regs1 24 = getr regs0 24 -> getr regs1 25 = getr regs0 25 -> getr regs1 26 = getr regs0 26 -> getr regs1 27 = getr regs0 27 ->
word_mem ubs0segs mem1 (spZ regs0 - 8) (bv_unsigned (getr regs0 1)) ->
word_mem ubs0segs mem1 (spZ regs0 - 16) (bv_unsigned (getr regs0 8)) ->
word_mem ubs0segs mem1 (spZ regs0 - 24) (bv_unsigned (getr regs0 9)) ->
word_mem ubs0segs mem1 (spZ regs0 - 32) (bv_unsigned (getr regs0 18)) ->
word_mem ubs0segs mem1 (spZ regs0 - 40) (bv_unsigned (getr regs0 19)) ->
word_mem ubs0segs mem1 (spZ regs0 - 48) (bv_unsigned (getr regs0 20)) ->
word_mem ubs0segs mem1 (spZ regs0 - 56) (bv_unsigned (getr regs0 21)) ->
word_mem ubs0segs mem1 st pdata -> word_mem ubs0segs mem1 (st + 8) nb -> word_mem ubs0segs mem1 (st + 16) cur ->
val_mem ubs0segs mem1 (dst + 26) 2 nlp ->
garr8 ubs0segs mem1 pdata PAYLOAD -> Z.of_nat (length PAYLOAD) = nb ->
res_ok Ac bq -> rfc_room bq N ->
SR ubs0segs (mkCfg (mkst regs1 (Z_to_bv 64 PALPC) mem1 (seg_rom ubs0segs)) mdc)
(pal_post_x regs0 STK sp0 FP L A mem md Bb st dst N nb cur palsz r mem1 pdata PAYLOAD bq).
Proof using IMG.
intros r Hr STK sp0 FP L A mem md Lc Ac mdc regs0 regs1 mem1 Bb st dst N pdata nb cur palsz nlp PAYLOAD bq
HJ Hid Hbase HBc Hpd Hnlp Hpznlp Hra0 Htp0 Hal16 Hwlo Hwhi Hst1 Hst2 Hdst1 Hdst2 Hsd Hst8 Hdst8 H63 HN Hcur Hnb
G2 G3 G4 G8 G9 G18 G19 G20 G22 G23 G24 G25 G26 G27
W1 W8 W9 W18 W19 W20 W21 Wp Wn Wc Wnlp HPL HPLn HRq HRm.
assert (Hpz : 0 <= palsz <= 196605) by (clear - Hnlp Hpznlp; lia).
assert (HRm1 : room bq palsz) by (apply (rfc_room_pal bq N palsz HRm Hpz)).
assert (HRm2 : room (rb_malloc bq palsz) N) by (apply (rfc_room_img bq N palsz HRm Hpz); clear - HN; lia).
apply hideP_i in Hsd. apply hideP_i in Hr.
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HASv : ALLOC_STACK = 8192) by reflexivity.
assert (HFRv : RFC_FRAME = 64) by reflexivity. assert (HDPv : RFC_DEPTH = 8256) by reflexivity.
assert (HRDv : RD_FRAME = 32) by reflexivity.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HH.
pose proof HJ as (_ & _ & _ & _ & _ & (Hsp0al & Hstk0 & Hceil & Hsp063 & Hstw) & _).
assert (Hpdc : In (pdata, nb) (blocks Lc Ac)) by (eapply Permutation_in; [apply Permutation_sym; exact HBc | exact Hpd]).
destruct (heap_blocks_range _ _ LAWS Lc Ac mem1 mdc pdata nb HH Hpdc ltac:(lia)) as (Hp0 & Hp1 & _).
set (sp := spZ regs0) in *.
assert (Hspm : (sp - RFC_FRAME) mod 16 = 0).
{ rewrite HFRv. replace (sp - 64) with (sp + (-4) * 16) by lia. rewrite Z.mod_add by lia. exact Hal16. }
set (extra := [getr regs0 1; getr regs0 8; getr regs0 9; getr regs0 18; getr regs0 19; getr regs0 20; getr regs0 21;
Z_to_bv 64 pdata; Z_to_bv 64 nb; Z_to_bv 64 cur; Z_to_bv 64 nlp]).
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew (Ereg regs1 extra) n = getr regs1 rr) by (intros; apply ew_Ereg_nat; assumption).
assert (HX : forall n j v, (n = 32 + j)%nat -> nth_error extra j = Some v -> ew (Ereg regs1 extra) n = v).
{ intros n j v -> Hj. rewrite ew_Ereg_extra. apply nth_error_nth. exact Hj. }
assert (HE2 : bv_unsigned (ew (Ereg regs1 extra) 2) = sp - RFC_FRAME) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; lia).
assert (HE18 : bv_unsigned (ew (Ereg regs1 extra) 18) = st) by (rewrite (HE 18%nat 18%bv eq_refl), G18; apply unsigned_lit_small; lia).
assert (HE8 : bv_unsigned (ew (Ereg regs1 extra) 8) = dst) by (rewrite (HE 8%nat 8%bv eq_refl), G8; apply unsigned_lit_small; lia).
assert (HS : st_ok ubs0segs (Ereg regs1 extra) (ss_pal r) (mkst regs1 (Z_to_bv 64 PALPC) mem1 (seg_rom ubs0segs))).
{ unfold ss_pal. apply entry_st_ok_full.
- apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_Ereg | intros H0; discriminate H0 | cbn [sv_denot]; exact G20] | intros H0; discriminate H0 |].
cbn [sv_denot]. rewrite HE8. exact G19.
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
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ nlp); [cbn [sv_denot]; rewrite Z.add_0_r, (HX 42%nat 10%nat _ eq_refl eq_refl), Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | exact Wnlp]. }
apply Forall_nil.
- unfold hideP in Hsd. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val].
rewrite HE2, HE18, HE8. repeat split; lia.
- split; [| split; constructor].
cbn [atoms_ok f_atoms]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite HE2, HE18, HE8, (HE 9%nat 9%bv eq_refl), (HX 39%nat 7%nat _ eq_refl eq_refl), (HX 40%nat 8%nat _ eq_refl eq_refl),
(HX 41%nat 9%nat _ eq_refl eq_refl), (HX 42%nat 10%nat _ eq_refl eq_refl), G9, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 3) with 8. change (2 ^ 0) with 1.
rewrite ?Z.mod_1_r.
repeat split; try lia; assumption. }
change mem1 with (ms_mem (mkst regs1 (Z_to_bv 64 PALPC) mem1 (seg_rom ubs0segs))) in HJ.
jrun_to LAWS ubs0tbl_ok HS HJ ubs0_A_malloc.
{ wr3_tac_with HE2 HE18 HE8 ltac:(clear - Hwlo Hwhi Hst1 Hst2 Hdst1 Hdst2 HFRv HDPv HASv; lia). }
cbn [ms_mem mkst] in HF. rename HF into HFa.
lazymatch type of HS with st_ok _ ?Ec ?ssc ?msc =>
assert (Hr10 : getr (ms_regs msc) 10 = Z_to_bv 64 palsz);
[ rewrite (st_ok_reg ubs0segs Ec ssc msc 10%bv HS); eval_sr_get;
rewrite Hpznlp; apply denot_mul3_atom; [ew_havocF; exact (HX 42%nat 10%nat _ eq_refl eq_refl) | lia] | ] end.
jreg HS (2%bv:reg) as Hr2. rewrite (HE 2%nat 2%bv eq_refl), G2 in Hr2.
jreg HS (4%bv:reg) as Hr4. rewrite (HE 4%nat 4%bv eq_refl), G4, Htp0 in Hr4.
jreg HS (1%bv:reg) as Hr1.
eapply SR_bind.
{ eapply (jmalloc_at_res API IMG) with (n := palsz) (spc := sp - RFC_FRAME);
[ exact HS | reflexivity | reflexivity | exact HJ | exact Hid | exact Hr10 | exact HRq | exact HRm1
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
assert (Hlpin2 : In (res, palsz) (blocks L2 A2)) by (rewrite Hbl2; apply in_app_iff; right; left; reflexivity).
destruct (heap_blocks_range0 L2 A2 mem2 md2 res palsz HH2 Hlpin2) as [Rr0 Rr1].
assert (HBnow : Permutation (blocks L2 A2) ([(res, palsz)] ++ Bb)).
{ rewrite Hbl2. eapply Permutation_trans; [apply Permutation_sym; apply Permutation_middle|]. cbn [app]. apply perm_skip. rewrite <- Hblc. exact HBc. }
assert (Hfresh : In (res, palsz) (blocks L A) -> palsz <= 0).
{ intros Hin. destruct (Z_le_gt_dec palsz 0) as [|Hgt]; [assumption|]. exfalso.
apply (fresh_not_in API L2 A2 mem2 md2 b1 b2 res palsz HH2 Hbl2 ltac:(lia)). rewrite <- Hblc.
eapply Permutation_in; [apply Permutation_sym; exact HBc|]. apply Hbase. exact Hin. }
assert (HPLk : forall mx : word -> option byte,
(forall b m i, In (b, m) Bb -> 0 <= i < m -> mbyte ubs0segs mx (b + i) = mbyte ubs0segs mem1 (b + i)) ->
garr8 ubs0segs mx pdata PAYLOAD).
{ intros mx Hbk. eapply (garr8_frame ubs0segs); [exact HPL|]. intros a Ha. rewrite HPLn in Ha.
replace a with (pdata + (a - pdata)) by lia. apply (Hbk pdata nb (a - pdata) Hpd). lia. }
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
assert (Hbk_r : forall b m i, In (b, m) Bb -> 0 <= i < m -> mbyte ubs0segs (ms_mem msr) (b + i) = mbyte ubs0segs mem1 (b + i))
by (intros b m i Hb Hi;
assert (Hbc : In (b, m) (blocks Lc Ac)) by (eapply Permutation_in; [apply Permutation_sym; exact HBc | exact Hb]);
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
mbfA HFa Ha Hn1 Hn2 Hn3 Hac HFRv HDPv HASv HE2 HE8 HE18; reflexivity);
assert (M12 : getr (ms_regs msr) 12 = Z_to_bv 64 palsz)
by (rewrite (st_ok_reg ubs0segs _ _ _ 12%bv HS); eval_sr_get; rewrite Hpznlp;
apply denot_mul3_atom; [ew_havocF; exact (HX 42%nat 10%nat _ eq_refl eq_refl) | lia])
end.
jreg HS (10%bv:reg) as M10. rewrite (HE 18%nat 18%bv eq_refl), G18 in M10.
jreg HS (11%bv:reg) as M11. rewrite Hq10 in M11.
jreg HS (2%bv:reg) as M2. rewrite (HE 2%nat 2%bv eq_refl), G2 in M2.
jreg HS (1%bv:reg) as M1.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HH3.
assert (Hpd2 : In (pdata, nb) (blocks L2 A2)) by (eapply Permutation_in; [apply Permutation_sym; exact HBnow | right; exact Hpd]).
eapply SR_bind.
{ eapply (jreaddata API IMG _ _ _ STK sp0 FP L A mem md L2 A2 md2 st res palsz pdata nb cur (sp - RFC_FRAME)).
- exact HS. - reflexivity. - reflexivity. - exact HJ2.
- exact M10. - exact M11. - exact M12. - exact M2.
- exact Hspm. - rewrite HRDv; lia. - lia. - exact H63.
- exact M1. - apply ret_ok_even; vm_compute; reflexivity.
- lia. - lia. - exact Hst8.
- exact Wp_r. - exact Wn_r. - exact Wc_r.
- lia. - lia. - lia. - lia. - lia. - intros; lia.
- intros j Hj. exact (proj1 (heap_blocks _ _ LAWS L2 A2 _ md2 pdata nb j HH3 Hpd2 Hj)).
- lia. - lia.
- intros i Hi. exact (proj1 (heap_blocks _ _ LAWS L2 A2 _ md2 res palsz i HH3 Hlpin2 Hi)).
- intros a Ha. replace a with (res + (a - res)) by lia. apply Hwr; [exact Hlpin2 | lia].
- intros a Ha. unfold wr_byte. left. lia.
- right. lia.
- left. rewrite HRDv. lia.
- intros _. left. rewrite HRDv. lia.
- intros _. left. lia.
- left. lia.
- intros _. destruct (heap_sep _ _ LAWS L2 A2 _ md2 b1 (res, palsz) b2 (pdata, nb) HH3 Hbl2 ltac:(rewrite <- Hblc; exact Hpdc)) as [H0|H0]; cbn [fst snd] in H0; lia. }
cbv beta. intros c' (regs3 & mem3 & -> & HJ3 & HP3 & Hout3 & Hgr3 & Hcase).
jafter_call2 HS 59%nat regs3 mem3 HP3 0 [1%nat] HS3.
match type of HS3 with ?P -> _ => assert (HK3 : P); [|specialize (HS3 HK3)] end.
{ unfold hideP in Hsd. constructor; [|constructor; [|constructor]].
- eapply region_kept_rd; [exact Hout3 | exact Hgr3 | ..]; cbn [r_base r_lo r_hi r_wlo r_whi base_val]; ew_havocF; rewrite ?HE2, ?HRDv; lia.
- eapply region_kept_rd; [exact Hout3 | exact Hgr3 | ..]; cbn [r_base r_lo r_hi r_wlo r_whi base_val]; ew_havocF; rewrite ?HE8, ?HRDv; lia. }
clear HS. rename HS3 into HS.
assert (TOIMG : forall rr cur2 (msx : machine_state) (Ex : env) (ssx : sstate),
(rr = 0 \/ rr = 2 ^ 64 - 1) -> (rr = 0 -> r = 0) -> cur <= cur2 <= nb ->
(rr = 0 -> cur2 = cur + palsz /\ garr8 ubs0segs (ms_mem msx) res (firstn (Z.to_nat palsz) (skipn (Z.to_nat cur) PAYLOAD))) ->
(rr <> 0 -> r <> 0 \/ nb < cur + palsz) ->
st_ok ubs0segs Ex ssx msx -> ss_pc ssx = IMGPC -> ss_resv ssx = None ->
journal ubs0_msyms MR STK sp0 FP L A mem md L2 A2 (ms_mem msx) md2 ->
getr (ms_regs msx) 2 = Z_to_bv 64 (sp - RFC_FRAME) -> getr (ms_regs msx) 3 = getr regs0 3 -> getr (ms_regs msx) 4 = getr regs0 4 ->
getr (ms_regs msx) 8 = Z_to_bv 64 dst -> getr (ms_regs msx) 9 = Z_to_bv 64 N -> getr (ms_regs msx) 18 = Z_to_bv 64 st ->
getr (ms_regs msx) 20 = Z_to_bv 64 rr ->
getr (ms_regs msx) 22 = getr regs0 22 -> getr (ms_regs msx) 23 = getr regs0 23 ->
getr (ms_regs msx) 24 = getr regs0 24 -> getr (ms_regs msx) 25 = getr regs0 25 -> getr (ms_regs msx) 26 = getr regs0 26 -> getr (ms_regs msx) 27 = getr regs0 27 ->
word_mem ubs0segs (ms_mem msx) (sp - 8) (bv_unsigned (getr regs0 1)) ->
word_mem ubs0segs (ms_mem msx) (sp - 16) (bv_unsigned (getr regs0 8)) ->
word_mem ubs0segs (ms_mem msx) (sp - 24) (bv_unsigned (getr regs0 9)) ->
word_mem ubs0segs (ms_mem msx) (sp - 32) (bv_unsigned (getr regs0 18)) ->
word_mem ubs0segs (ms_mem msx) (sp - 40) (bv_unsigned (getr regs0 19)) ->
word_mem ubs0segs (ms_mem msx) (sp - 48) (bv_unsigned (getr regs0 20)) ->
word_mem ubs0segs (ms_mem msx) (sp - 56) (bv_unsigned (getr regs0 21)) ->
word_mem ubs0segs (ms_mem msx) st pdata -> word_mem ubs0segs (ms_mem msx) (st + 8) nb ->
word_mem ubs0segs (ms_mem msx) (st + 16) cur2 -> word_mem ubs0segs (ms_mem msx) dst res ->
(forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp - RFC_DEPTH <= a < sp) -> ~ (dst <= a < dst + 16) -> ~ (st + 16 <= a < st + 24) ->
mbyte ubs0segs (ms_mem msx) a = mbyte ubs0segs mem1 a) ->
(forall b m i, In (b, m) Bb -> 0 <= i < m -> mbyte ubs0segs (ms_mem msx) (b + i) = mbyte ubs0segs mem1 (b + i)) ->
SR ubs0segs (mkCfg msx md2) (pal_post_x regs0 STK sp0 FP L A mem md Bb st dst N nb cur palsz r mem1 pdata PAYLOAD bq)).
{ intros rr cur2 msx Ex ssx Hrr Hrr0 Hcur2 Hrrv Hrrs HSx Hpcx Hrvx HJx X2 X3 X4 X8 X9 X18 X20 X22 X23 X24 X25 X26 X27 V1 V8 V9 V18 V19 V20 V21 Vp Vn Vc Vl Hfr1 Hbk1.
rewrite (st_ok_mkst ubs0segs Ex ssx msx HSx Hrvx), Hpcx.
eapply SR_mono.
{ eapply (rfc_img_x API IMG rr Hrr STK sp0 FP L A mem md L2 A2 md2 regs0 (ms_regs msx) (ms_mem msx) Bb [(res, palsz)] st dst N pdata nb cur2 res palsz PAYLOAD (rb_malloc bq palsz) HJx Hid2 Hbase HBnow Hpd);
try assumption; try lia.
{ right. exists res. split; [reflexivity|]. split; [reflexivity|]. split; [exact Hfresh | lia]. }
{ apply HPLk. exact Hbk1. } }
cbv beta. intros c' (L4 & A4 & regs4 & mem4 & md4 & res' & cur4 & img & -> & HJ4 & Hid4 & HP4 & Hq0 & Hfr4 & Hbk4 & Hcw & Hc4 & Hres').
exists L4, A4, regs4, mem4, md4, res', cur4, img, res, [(res, palsz)].
split; [reflexivity|]. split; [exact HJ4|]. split; [exact Hid4|]. split; [exact HP4|]. split; [exact Hq0|].
split; [intros a Ha Hn1 Hn2 Hn3; rewrite (Hfr4 a Ha Hn1 Hn2 Hn3); exact (Hfr1 a Ha Hn1 Hn2 Hn3)|].
split; [intros b m i Hb Hi; rewrite (Hbk4 b m i Hb Hi); exact (Hbk1 b m i Hb Hi)|].
split; [exact Hcw|]. split; [lia|].
destruct Hres' as [(-> & Hleak & Hwhy & HRf) | (-> & -> & Hw1 & Hw2 & HPm & Hfit4 & Hcur4 & Hlpk4 & Himg4 & HRok)]; [left | right].
{ split; [reflexivity|]. split; [exact Hleak|]. split.
- destruct (Z.eq_dec rr 0) as [Hz|Hz].
+ destruct (Hrrv Hz) as [Hc2 _]. destruct Hwhy as [Hw|Hw]; [exfalso; exact (Hw Hz) | right; clear - Hw Hc2; lia].
+ destruct (Hrrs Hz) as [Hw|Hw]; [left; exact Hw | right; clear - Hw HN; lia].
- exact (res_ok_mono _ _ _ (rfc_fail_of_pal bq palsz N Hpz ltac:(clear - HN; lia)) HRf). }
destruct (Hrrv eq_refl) as [Hc2 Hpal]. subst cur4.
split; [reflexivity|]. split; [apply Hrr0; reflexivity|]. split; [exact Hw1|]. split; [exact Hw2|]. split.
{ exists res. split; [reflexivity|]. split; [reflexivity|].
eapply (garr8_frame ubs0segs); [exact Hpal|]. intros a Ha. rewrite length_firstn, length_skipn in Ha.
replace a with (res + (a - res)) by lia. apply (Hlpk4 res palsz (a - res)); [left; reflexivity | lia]. }
split; [exact HPm|]. split; [lia|]. split; [lia|]. split; [rewrite <- Hc2; exact Himg4 | exact HRok]. }
destruct Hcase as [(Hfit & Ha3 & Hcw3 & Hcp3) | (Hnfit & Ha3 & Hcw3 & Hkp3)].
all: jreg HS (10%bv:reg) as Q10; cbn [ms_regs mkst] in Q10; rewrite Ha3 in Q10; symmetry in Q10.
all: jrun_to LAWS ubs0tbl_ok HS HJ3 IMGPC.
all: lazymatch goal with
| |- wr_ok _ _ _ _ _ _ _ =>
eapply wr_ok_cons_win; [reflexivity | ew_havocF; exact HE2 | cbn [r_wlo r_whi]; intros _; clear - Hwlo Hwhi Hst1 Hst2 Hdst1 Hdst2 HFRv HDPv HASv; lia |];
eapply wr_ok_cons_win; [reflexivity | ew_havocF; exact HE8 | cbn [r_wlo r_whi]; intros _; clear - Hwlo Hwhi Hst1 Hst2 Hdst1 Hdst2 HFRv HDPv HASv; lia |];
apply wr_ok_nil
| |- _ => cbn [ms_mem mkst] in HF; rename HF into HFd
end.
all: unfold hideP in Hsd.
all: destruct Hr as [-> | ->].
all: lazymatch goal with |- SR _ _ (pal_post_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?rv _ _ _ _) =>
first [ assert_succeeds (assert (cur + palsz <= nb) by assumption); eapply (TOIMG rv (cur + palsz))
| eapply (TOIMG (2 ^ 64 - 1) nb) ] end.
all: lazymatch goal with
| |- _ \/ _ => first [left; reflexivity | right; reflexivity]
| |- _ = 0 -> _ = 0 => intros HH0; first [reflexivity | exfalso; clear - HH0; lia]
| |- _ = 0 -> _ /\ _ => intros HH0; first [exfalso; clear - HH0; lia | split; [reflexivity | ]]
| |- _ <> 0 -> _ => intros HH0; first [exfalso; apply HH0; reflexivity | right; assumption | left; exact HH0]
| |- _ <= _ <= _ => lia
| |- st_ok _ _ _ _ => exact HS
| |- ss_pc _ = _ => reflexivity
| |- ss_resv _ = _ => reflexivity
| |- journal _ _ _ _ _ _ _ _ _ _ _ _ _ => exact HJ3
| |- _ => idtac
end.
all: lazymatch goal with
| |- getr _ 2 = _ => reg_nowF HS ltac:(rewrite <- HE2, ?Z_to_bv_bv_unsigned; reflexivity)
| |- getr _ 3 = _ => reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 3%nat 3%bv eq_refl); exact G3)
| |- getr _ 4 = _ => reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 4%nat 4%bv eq_refl); exact G4)
| |- getr _ 8 = _ => reg_nowF HS ltac:(rewrite <- HE8, ?Z_to_bv_bv_unsigned; reflexivity)
| |- getr _ 9 = _ => reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 9%nat 9%bv eq_refl); exact G9)
| |- getr _ 18 = _ => reg_nowF HS ltac:(rewrite <- HE18, ?Z_to_bv_bv_unsigned; reflexivity)
| |- getr _ 20 = _ => reg_nowF HS ltac:(rewrite Q10, ?Z_to_bv_bv_unsigned; first [reflexivity | apply bv_eq; vm_compute; reflexivity])
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
[ solve [ eapply word_mem_frame; [first [exact Wp_r | exact Wn_r | exact Hcw3] |]; intros i Hi;
mb_frame_with HFd ltac:(lia) ltac:(rewrite ?HE2, ?HE8; lia);
first [ reflexivity | rewrite (mbyte_of_rd _ _ (sp - RFC_FRAME) res palsz st _ Hout3) by (rewrite ?HRDv; lia); reflexivity ] ]
| solve [ rewrite <- (Z.add_0_r dst); eapply (st_chunk_word _ _ _ 1%nat _ 8%nat 0 (SOff 47 0) dst _ HS);
[ reflexivity | reflexivity | cbv; auto 12 | ew_havocF; exact HE8
| cbn [sv_denot]; ew_havocF; rewrite Z.add_0_r, Hq10, Z_to_bv_bv_unsigned; reflexivity | lia ] ] ]
| |- forall a : Z, alloc_ceiling <= a < _ -> _ =>
intros a Ha Hn1 Hn2 Hn3;
mbfA HFd Ha Hn1 Hn2 Hn3 Hac HFRv HDPv HASv HE2 HE8 HE18;
rewrite (mbyte_of_rd _ _ (sp - RFC_FRAME) res palsz st _ Hout3) by (rewrite ?HRDv; lia);
exact (Hfr_r a Ha Hn1 Hn2 Hn3)
| |- forall (b m i : Z), In (b, m) _ -> _ =>
intros b m i Hb Hi;
assert (Hbc : In (b, m) (blocks Lc Ac)) by (eapply Permutation_in; [apply Permutation_sym; exact HBc | exact Hb]);
destruct (heap_blocks _ _ LAWS Lc Ac mem1 mdc b m i HH Hbc Hi) as (_ & Hb0 & Hb1 & _);
destruct (heap_sep _ _ LAWS L2 A2 _ md2 b1 (res, palsz) b2 (b, m) HH2 Hbl2 ltac:(rewrite <- Hblc; exact Hbc)) as [Hs|Hs]; cbn [fst snd] in Hs;
mbfB HFd Hb0 Hb1 Hi Hac Hceil Hwlo Hst1 Hdst1 HFRv HDPv HASv HE2 HE8 HE18;
rewrite (mbyte_of_rd _ _ (sp - RFC_FRAME) res palsz st _ Hout3) by (rewrite ?HRDv; lia);
exact (Hbk_r b m i Hb Hi)
| |- garr8 _ _ _ _ =>
refine (proj1 (rx_garr8_slice_copy _ _ pdata PAYLOAD res cur palsz (HPLk _ Hbk_r) ltac:(lia) ltac:(lia) ltac:(rewrite HPLn; lia) _));
intros i Hi;
mbfB HFd Rr0 Rr1 Hi Hac Hceil Hwlo Hst1 Hdst1 HFRv HDPv HASv HE2 HE8 HE18;
exact (Hcp3 i Hi)
end.
Qed.
End S.
End c.
