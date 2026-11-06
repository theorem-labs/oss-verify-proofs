(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0p YK0i YK0j YK14 YK1b YK1a YK15 YN06 YK0s.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ00.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP0j YP0g YP0r YP0c YP0e.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YH04 YH07 YH06 YO3m YI00 YI02 YI01 YI03
YI1e YI1i YI59 YI56 YI0x YL0e YI08 YI0c YI3h
YI4y YO0e.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Ltac rreg_final HS HX HE HE2 rr :=
lazymatch type of HS with st_ok _ ?Ef ?ssf ?msf =>
let Q := fresh "Q" in
pose proof (st_ok_reg src2segs Ef ssf msf rr HS) as Q; eval_sr_get_in Q; cbn [sv_denot] in Q;
repeat (rewrite ew_havoc_old in Q; [|cbv; lia]); rewrite ?Z.add_0_r in Q;
cbn [ms_regs mkst]; rewrite Q; clear Q;
first [ rewrite Z_to_bv_bv_unsigned;
first [ rewrite (HX 32%nat 0%nat _ eq_refl eq_refl) | rewrite (HX 33%nat 1%nat _ eq_refl eq_refl) | rewrite (HX 34%nat 2%nat _ eq_refl eq_refl)
| rewrite (HX 35%nat 3%nat _ eq_refl eq_refl) | rewrite (HX 36%nat 4%nat _ eq_refl eq_refl) | rewrite (HX 37%nat 5%nat _ eq_refl eq_refl)
| rewrite (HX 38%nat 6%nat _ eq_refl eq_refl)
| rewrite (HE 3%nat 3%bv eq_refl) | rewrite (HE 4%nat 4%bv eq_refl)
| rewrite (HE 22%nat 22%bv eq_refl) | rewrite (HE 23%nat 23%bv eq_refl) | rewrite (HE 24%nat 24%bv eq_refl)
| rewrite (HE 25%nat 25%bv eq_refl) | rewrite (HE 26%nat 26%bv eq_refl) | rewrite (HE 27%nat 27%bv eq_refl) ];
first [ reflexivity | assumption | symmetry; assumption ]
| rewrite HE2; unfold RRFC_FRAME;
match goal with |- Z_to_bv 64 ?x = getr ?rg0 _ => replace x with (spZ rg0) by lia end;
unfold spZ; rewrite Z_to_bv_bv_unsigned; reflexivity
| idtac ]
end.
Ltac rimg_fin HS HJ Hid HX HE HE2 Hra0 res cur2 img :=
lazymatch type of HS with st_ok _ ?Ef ?ssf ?msf =>
let Q1 := fresh "Q1" in let Q10 := fresh "Q10" in
pose proof (st_ok_reg src2segs Ef ssf msf 1%bv HS) as Q1; eval_sr_get_in Q1; cbn [sv_denot] in Q1;
repeat (rewrite ew_havoc_old in Q1; [|cbv; lia]); rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned in Q1;
rewrite (HX 32%nat 0%nat _ eq_refl eq_refl) in Q1;
lazymatch goal with |- context [mkCfg (mkst ?rg _ ?mm _) ?mdl] =>
eexists _, _, rg, mm, mdl end;
exists res, cur2, img;
split; [ cbn [ms_regs mkst]; rewrite Q1, Hra0; reflexivity |];
split; [ exact HJ |];
split; [ exact Hid |];
split; [ apply regs_preserved_intro;
[ rreg_final HS HX HE HE2 (2%bv:reg) | rreg_final HS HX HE HE2 (3%bv:reg) | rreg_final HS HX HE HE2 (4%bv:reg) | rreg_final HS HX HE HE2 (8%bv:reg)
| rreg_final HS HX HE HE2 (9%bv:reg) | rreg_final HS HX HE HE2 (18%bv:reg) | rreg_final HS HX HE HE2 (19%bv:reg) | rreg_final HS HX HE HE2 (20%bv:reg)
| rreg_final HS HX HE HE2 (21%bv:reg) | rreg_final HS HX HE HE2 (22%bv:reg) | rreg_final HS HX HE HE2 (23%bv:reg) | rreg_final HS HX HE HE2 (24%bv:reg)
| rreg_final HS HX HE HE2 (25%bv:reg) | rreg_final HS HX HE HE2 (26%bv:reg) | rreg_final HS HX HE HE2 (27%bv:reg) ] |];
split; [ pose proof (st_ok_reg src2segs Ef ssf msf 10%bv HS) as Q10; eval_sr_get_in Q10; cbn [sv_denot] in Q10; cbn [ms_regs mkst]; rewrite Q10; reflexivity |];
split; [| split; [| split; [| split ]]]
end.
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition ss_rimg : sstate :=
mkSS RR_MAL (sr_set (sr_set (sr_set sr_atoms 19%bv (SLit 0)) 20%bv (SLit 0)) 21%bv (SLit 0))
[ YQ0b.mkRegion (Some 2%nat) 0 RRFC_FRAME 0 RRFC_FRAME
[mkChunk 56 (CVal 8 (SOff 32 0)); mkChunk 48 (CVal 8 (SOff 33 0)); mkChunk 40 (CVal 8 (SOff 34 0));
mkChunk 32 (CVal 8 (SOff 35 0)); mkChunk 24 (CVal 8 (SOff 36 0)); mkChunk 16 (CVal 8 (SOff 37 0));
mkChunk 8 (CVal 8 (SOff 38 0))] ;
YQ0b.mkRegion (Some 9%nat) 0 24 16 24 [mkChunk 0 (CVal 8 (SOff 39 0)); mkChunk 8 (CVal 8 (SOff 40 0)); mkChunk 16 (CVal 8 (SOff 41 0))] ;
YQ0b.mkRegion (Some 8%nat) 0 12 0 12 [] ]
None
(mkFacts [ (2%nat, mkAF (CEIL_MIN + ALLOC_STACK) (2^63) 4); (9%nat, mkAF CEIL_MIN (2^63) 3);
(8%nat, mkAF CEIL_MIN (2^63) 3); (10%nat, mkAF 3 4 0); (18%nat, mkAF 1 RGB_NMAX 0);
(40%nat, mkAF 1 CEIL_MAX 0); (41%nat, mkAF 0 CEIL_MAX 0); (39%nat, mkAF 4096 CEIL_MAX 0) ] [] []).
Definition ss_rimg_c : sstate := Eval vm_compute in ss_rimg.
Lemma denot_add0_mul : forall E a b x y,
ew E a = Z_to_bv 64 x -> ew E b = Z_to_bv 64 y -> 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> x * y < 2 ^ 64 ->
sv_denot E (SAlu ALU_ADD (SMd M_MUL (SOff a 0) (SOff b 0)) (SLit 0)) = Z_to_bv 64 (x * y).
Proof.
intros E a b x y Ha Hb Hx Hy Hxy. rewrite denot_lit_U. f_equal. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SMd. cbn [zmd_raw].
rewrite (U_atom E a x Ha), (U_atom E b y Hb), U_SLit by lia. change (zcanon 0) with 0.
rewrite Z.add_0_r, (zcanon_id (x * y)) by (unfold M64; nia). apply zcanon_id. unfold M64; nia.
Qed.
Section S.
Variable API : AllocAPI src2_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws src2_msyms MR := aa_laws API.
Hypothesis IMG : img_laws src2_msyms MR.
Definition rimg_post (regs0 : bvmap 5 word) (STK sp0 : Z) (FP : list (Z * Z)) L A mem md
(Bb : list (Z * Z)) (st dst N nb cur fmt : Z) (mem1 : word -> option byte) (c' : config) : Prop :=
exists L2 A2 regs2 mem2 md2 (res cur2 img : Z),
c' = mkCfg (mkst regs2 (getr regs0 1) mem2 (seg_rom src2segs)) md2 /\
journal src2_msyms MR STK sp0 FP L A mem md L2 A2 mem2 md2 /\
st_init_done A2 = true /\
regs_preserved regs0 regs2 /\
getr regs2 10 = Z_to_bv 64 res /\ (res = 0 \/ res = 1) /\
(forall a, alloc_ceiling <= a < 2 ^ 64 ->
~ (spZ regs0 - RRFC_STK <= a < spZ regs0) -> ~ (dst <= a < dst + 12) -> ~ (st + 16 <= a < st + 24) ->
mbyte src2segs mem2 a = mbyte src2segs mem1 a) /\
(forall b m i, In (b, m) Bb -> 0 <= i < m -> mbyte src2segs mem2 (b + i) = mbyte src2segs mem1 (b + i)) /\
word_mem src2segs mem2 (st + 16) cur2 /\ cur <= cur2 <= nb /\
((res = 0 /\ Permutation (blocks L2 A2) Bb) \/
(res = 1 /\ word_mem src2segs mem2 dst img /\ 0 <= img < 2 ^ 64 /\ val_mem src2segs mem2 (dst + 8) 4 fmt /\
Permutation (blocks L2 A2) ((img, fmt * N) :: Bb))).
Lemma rfc_img :
forall STK sp0 FP L A mem md Lc Ac mdc (regs0 regs1 : bvmap 5 word) (mem1 : word -> option byte)
(Bb : list (Z * Z)) (st dst N pdata nb cur fmt : Z),
journal src2_msyms MR STK sp0 FP L A mem md Lc Ac mem1 mdc -> st_init_done Ac = true ->
(forall b, In b (blocks L A) -> In b Bb) ->
Permutation (blocks Lc Ac) Bb ->
In (pdata, nb) Bb ->
YK0s.ret_ok (getr regs0 1) -> getr regs0 4 = Z_to_bv 64 (ms_tp src2_msyms) ->
spZ regs0 mod 16 = 0 -> sp0 - STK <= spZ regs0 - RRFC_STK -> spZ regs0 <= sp0 ->
spZ regs0 <= st -> st + 24 <= sp0 -> spZ regs0 <= dst -> dst + RGBFC_SIZE <= sp0 -> (st + 24 <= dst \/ dst + RGBFC_SIZE <= st) ->
st mod 8 = 0 -> dst mod 8 = 0 -> sp0 < 2 ^ 63 ->
1 <= N <= RGB_NMAX -> 0 <= cur <= nb -> 0 < nb -> (fmt = 3 \/ fmt = 4) ->
getr regs1 2 = Z_to_bv 64 (spZ regs0 - RRFC_FRAME) -> getr regs1 3 = getr regs0 3 -> getr regs1 4 = getr regs0 4 ->
getr regs1 8 = Z_to_bv 64 dst -> getr regs1 9 = Z_to_bv 64 st -> getr regs1 10 = Z_to_bv 64 fmt -> getr regs1 18 = Z_to_bv 64 N ->
getr regs1 19 = Z_to_bv 64 0 -> getr regs1 20 = Z_to_bv 64 0 -> getr regs1 21 = Z_to_bv 64 0 ->
getr regs1 22 = getr regs0 22 -> getr regs1 23 = getr regs0 23 -> getr regs1 24 = getr regs0 24 -> getr regs1 25 = getr regs0 25 ->
getr regs1 26 = getr regs0 26 -> getr regs1 27 = getr regs0 27 ->
word_mem src2segs mem1 (spZ regs0 - 8) (bv_unsigned (getr regs0 1)) ->
word_mem src2segs mem1 (spZ regs0 - 16) (bv_unsigned (getr regs0 8)) ->
word_mem src2segs mem1 (spZ regs0 - 24) (bv_unsigned (getr regs0 9)) ->
word_mem src2segs mem1 (spZ regs0 - 32) (bv_unsigned (getr regs0 18)) ->
word_mem src2segs mem1 (spZ regs0 - 40) (bv_unsigned (getr regs0 19)) ->
word_mem src2segs mem1 (spZ regs0 - 48) (bv_unsigned (getr regs0 20)) ->
word_mem src2segs mem1 (spZ regs0 - 56) (bv_unsigned (getr regs0 21)) ->
word_mem src2segs mem1 st pdata -> word_mem src2segs mem1 (st + 8) nb -> word_mem src2segs mem1 (st + 16) cur ->
SR src2segs (mkCfg (mkst regs1 (Z_to_bv 64 RR_MAL) mem1 (seg_rom src2segs)) mdc)
(rimg_post regs0 STK sp0 FP L A mem md Bb st dst N nb cur fmt mem1).
Proof.
intros STK sp0 FP L A mem md Lc Ac mdc regs0 regs1 mem1 Bb st dst N pdata nb cur fmt
HJ Hid Hbase HBc Hpd Hra0 Htp0 Hal16 Hwlo Hwhi Hst1 Hst2 Hdst1 Hdst2 Hsd Hst8 Hdst8 H63 HN Hcur Hnb Hfmt
G2 G3 G4 G8 G9 G10 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27
W1 W8 W9 W18 W19 W20 W21 Wp Wn Wc.
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HASv : ALLOC_STACK = 8192) by reflexivity.
assert (HFRv : RRFC_FRAME = 64) by reflexivity. assert (HDPv : RRFC_STK = 8256) by reflexivity.
assert (HFCv : RGBFC_SIZE = 24) by reflexivity. assert (HNMv : RGB_NMAX = 10000) by reflexivity.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HH.
pose proof HJ as (_ & _ & _ & _ & _ & (Hsp0al & Hstk0 & Hceil & Hsp063 & Hstw) & _).
assert (Hpdc : In (pdata, nb) (blocks Lc Ac)) by (eapply Permutation_in; [apply Permutation_sym; exact HBc | exact Hpd]).
destruct (heap_blocks_range _ _ LAWS Lc Ac mem1 mdc pdata nb HH Hpdc ltac:(lia)) as (Hp0 & Hp1 & _).
set (sp := spZ regs0) in *.
assert (Hspm : (sp - RRFC_FRAME) mod 16 = 0).
{ rewrite HFRv. replace (sp - 64) with (sp + (-4) * 16) by lia. rewrite Z.mod_add by lia. exact Hal16. }
set (extra := [getr regs0 1; getr regs0 8; getr regs0 9; getr regs0 18; getr regs0 19; getr regs0 20; getr regs0 21;
Z_to_bv 64 pdata; Z_to_bv 64 nb; Z_to_bv 64 cur]).
set (E := Ereg regs1 extra).
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HX : forall n j v, (n = 32 + j)%nat -> nth_error extra j = Some v -> ew E n = v).
{ intros n j v -> Hj. subst E. rewrite ew_Ereg_extra. apply nth_error_nth. exact Hj. }
assert (HE2 : bv_unsigned (ew E 2) = sp - RRFC_FRAME) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; lia).
assert (HEs : bv_unsigned (ew E 9) = st) by (rewrite (HE 9%nat 9%bv eq_refl), G9; apply unsigned_lit_small; lia).
assert (HEd : bv_unsigned (ew E 8) = dst) by (rewrite (HE 8%nat 8%bv eq_refl), G8; apply unsigned_lit_small; lia).
assert (HE10 : ew E 10 = Z_to_bv 64 fmt) by (rewrite (HE 10%nat 10%bv eq_refl); exact G10).
assert (HE12 : ew E 18 = Z_to_bv 64 N) by (rewrite (HE 18%nat 18%bv eq_refl); exact G18).
assert (HE25 : ew E 39 = Z_to_bv 64 pdata) by (apply (HX 39%nat 7%nat _ eq_refl eq_refl)).
assert (HE22 : ew E 40 = Z_to_bv 64 nb) by (apply (HX 40%nat 8%nat _ eq_refl eq_refl)).
assert (HE24 : ew E 41 = Z_to_bv 64 cur) by (apply (HX 41%nat 9%nat _ eq_refl eq_refl)).
assert (HS : st_ok src2segs E ss_rimg_c (mkst regs1 (Z_to_bv 64 RR_MAL) mem1 (seg_rom src2segs))).
{ change ss_rimg_c with ss_rimg. unfold ss_rimg. subst E. apply entry_st_ok_full.
- apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_Ereg | intros H0; discriminate H0 | cbn [sv_denot]; exact G19]
| intros H0; discriminate H0 | cbn [sv_denot]; exact G20]
| intros H0; discriminate H0 | cbn [sv_denot]; exact G21].
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor; [|constructor]]].
+
unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HE2.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply (journal_stack_w _ _ _ _ _ _ _ _ _ _ _ _ _ HJ). lia. }
assert (CK : forall off j (w : word) (W : word_mem src2segs mem1 (sp - RRFC_FRAME + off) (bv_unsigned w)),
nth_error extra j = Some w ->
chunk_ok src2segs (Ereg regs1 extra) mem1 (sp - RRFC_FRAME) (mkChunk off (CVal 8 (SOff (32 + j) 0)))).
{ intros off j w W Hj. eapply (chunk_ok_val _ _ _ _ _ _ _ (bv_unsigned w)); [| pose proof (bv_unsigned_in_range 64 w) as Rw; change (bv_modulus 64) with (2 ^ 64) in Rw; cbn; lia | cbn; lia | apply val_mem_word_mem; exact W].
cbn [sv_denot]. rewrite Z.add_0_r, (HX (32 + j)%nat j w eq_refl Hj), Z_to_bv_bv_unsigned. reflexivity. }
repeat (apply Forall_cons; [ first [ eapply (CK 56 0%nat); [replace (sp - RRFC_FRAME + 56) with (sp - 8) by lia; exact W1 | reflexivity]
| eapply (CK 48 1%nat); [replace (sp - RRFC_FRAME + 48) with (sp - 16) by lia; exact W8 | reflexivity]
| eapply (CK 40 2%nat); [replace (sp - RRFC_FRAME + 40) with (sp - 24) by lia; exact W9 | reflexivity]
| eapply (CK 32 3%nat); [replace (sp - RRFC_FRAME + 32) with (sp - 32) by lia; exact W18 | reflexivity]
| eapply (CK 24 4%nat); [replace (sp - RRFC_FRAME + 24) with (sp - 40) by lia; exact W19 | reflexivity]
| eapply (CK 16 5%nat); [replace (sp - RRFC_FRAME + 16) with (sp - 48) by lia; exact W20 | reflexivity]
| eapply (CK 8 6%nat); [replace (sp - RRFC_FRAME + 8) with (sp - 56) by lia; exact W21 | reflexivity] ] | ]).
apply Forall_nil.
+
unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HEs.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply (journal_stack_w _ _ _ _ _ _ _ _ _ _ _ _ _ HJ). lia. }
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ pdata); [cbn [sv_denot]; rewrite Z.add_0_r, HE25, Z_to_bv_bv_unsigned; reflexivity | lia | cbn; lia | rewrite Z.add_0_r; apply val_mem_word_mem; exact Wp]. }
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ nb); [cbn [sv_denot]; rewrite Z.add_0_r, HE22, Z_to_bv_bv_unsigned; reflexivity | lia | cbn; lia | apply val_mem_word_mem; exact Wn]. }
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ cur); [cbn [sv_denot]; rewrite Z.add_0_r, HE24, Z_to_bv_bv_unsigned; reflexivity | lia | cbn; lia | apply val_mem_word_mem; exact Wc]. }
apply Forall_nil.
+
unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HEd.
split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
intros o Ho. apply (journal_stack_w _ _ _ _ _ _ _ _ _ _ _ _ _ HJ). lia.
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val].
rewrite HE2, HEs, HEd. repeat split; lia.
- split; [| split; constructor].
cbn [atoms_ok f_atoms]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite HE2, HEs, HEd, HE10, HE12, HE22, HE24, HE25, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 3) with 8. change (2 ^ 0) with 1.
rewrite !Z.mod_1_r.
repeat split; try lia; assumption. }
change mem1 with (ms_mem (mkst regs1 (Z_to_bv 64 RR_MAL) mem1 (seg_rom src2segs))) in HJ.
Ltac wr3 HE2 HEs HEd :=
eapply wr_ok_cons_win; [reflexivity | ew_havoc; exact HE2 | cbn [r_wlo r_whi]; intros _; lia |];
eapply wr_ok_cons_win; [reflexivity | ew_havoc; exact HEs | cbn [r_wlo r_whi]; intros _; lia |];
eapply wr_ok_cons_win; [reflexivity | ew_havoc; exact HEd | cbn [r_wlo r_whi]; intros _; lia |];
apply wr_ok_nil.
jrun_to LAWS src2tbl_ok HS HJ src2_A_malloc. { wr3 HE2 HEs HEd. }
lazymatch type of HS with st_ok _ ?Ec ?ssc ?msc => pose proof (st_ok_reg src2segs Ec ssc msc (10%bv:reg) HS) as Hr10; eval_sr_get_in Hr10 end.
rewrite (denot_mul_atoms_r _ 18 10 N fmt HE12 HE10) in Hr10 by lia.
jreg HS (2%bv:reg) as Hr2. rewrite (HE 2%nat 2%bv eq_refl), G2 in Hr2.
jreg HS (4%bv:reg) as Hr4. rewrite (HE 4%nat 4%bv eq_refl), G4, Htp0 in Hr4.
jreg HS (1%bv:reg) as Hr1.
eapply SR_bind.
{ eapply (jmalloc_at _ _ LAWS src2_errno_low IMG (aa_malloc API)) with (n := N * fmt) (spc := sp - RRFC_FRAME);
[ exact HS | reflexivity | reflexivity | exact HJ | exact Hid | exact Hr10 | lia
| exact Hr2 | lia | exact Hspm | lia | lia | exact Hr4 | exact Hr1 | apply ret_ok_even; vm_compute; reflexivity ]. }
intros c' (L2 & A2 & regs2 & mem2 & md2 & res & -> & HJ2 & Hid2 & HP2 & Hres10 & Hres & Hkeep2 & Hhi2). clear HJ.
change (ms_segs src2_msyms) with src2segs in Hkeep2, Hhi2.
jafter_call2 HS 42%nat regs2 mem2 HP2 0 [0%nat; 1%nat] HS2.
match type of HS2 with ?P -> _ => assert (HK : P); [|specialize (HS2 HK); clear HK] end.
{ constructor; [|constructor; [|constructor; [|constructor]]].
- eapply (region_kept_stack src2segs _ _ _ 2); [exact HE2 | exact Hhi2 | lia | lia | lia | cbn; lia | cbn; lia].
- eapply (region_kept_stack src2segs _ _ _ 9); [exact HEs | exact Hhi2 | lia | lia | lia | cbn; lia | cbn; lia].
- eapply (region_kept_stack src2segs _ _ _ 8); [exact HEd | exact Hhi2 | lia | lia | lia | cbn; lia | cbn; lia]. }
clear HS. rename HS2 into HS.
jreg HS (10%bv:reg) as Hq10. cbn [ms_regs mkst] in Hq10. rewrite Hres10 in Hq10. symmetry in Hq10.
destruct Hres as [[-> Hbl] | (Hnz & Hres16 & (b1 & b2 & Hbl2 & Hblc) & Hwr)].
+
lazymatch type of HS with st_ok _ ?E1 ?ss1 ?ms1 =>
apply (st_ok_regs src2segs E1 ss1 ms1 (sr_set (ss_regs ss1) 10%bv (SLit 0))) in HS;
[| intros rr; destruct (decide (rr = 10%bv)) as [->|Hne];
[ rewrite sr_get_set_same by reflexivity;
match goal with |- _ = sv_denot _ ?v => let v' := eval vm_compute in v in change v with v' end;
cbn [sv_denot]; rewrite Z.add_0_r, Hq10, Z_to_bv_bv_unsigned; reflexivity
| rewrite sr_get_set_other by exact Hne; reflexivity ] ] end.
lazymatch type of HS with st_ok _ _ ?ss1 _ => let v := eval vm_compute in ss1 in change ss1 with v in HS end.
jrun LAWS src2tbl_ok HS HJ2. { wr3 HE2 HEs HEd. }
eapply (SR_ret_at src2segs src2tbl); [exact src2tbl_ok | | | exact HS | reflexivity | vm_compute; reflexivity |].
{ exact (proj1 (heap_model _ _ LAWS _ _ _ _ (proj1 HJ2))). }
{ exact (proj1 (proj2 (heap_model _ _ LAWS _ _ _ _ (proj1 HJ2)))). }
rimg_fin HS HJ2 Hid2 HX HE HE2 Hra0 0 cur 0.
* left; reflexivity.
*   intros a Ha Hn1 Hn2 Hn3. cbn [ms_mem mkst] in HF0, Hhi2, HF.
mb_frame HF0; try (rewrite ?HE2, ?HEs, ?HEd; lia).
rewrite (proj1 (Hhi2 a Ha ltac:(lia))).
mb_frame HF; try (rewrite ?HE2, ?HEs, ?HEd; lia). reflexivity.
*   intros b m i Hb Hi. cbn [ms_mem mkst] in HF0, Hhi2, Hkeep2, HF.
assert (Hbc : In (b, m) (blocks Lc Ac)) by (eapply Permutation_in; [apply Permutation_sym; exact HBc | exact Hb]).
destruct (heap_blocks _ _ LAWS Lc Ac mem1 mdc b m i HH Hbc Hi) as (_ & Hb0 & Hb1 & _).
mb_frame HF0; try (rewrite ?HE2, ?HEs, ?HEd; lia).
rewrite (Hkeep2 b m i Hbc Hi).
mb_frame HF; try (rewrite ?HE2, ?HEs, ?HEd; lia). reflexivity.
*   eapply (st_chunk_word _ _ _ 1%nat _ 9%nat 16 (SOff 41 0) st cur HS); [reflexivity | reflexivity | cbv; auto 10 | | | lia].
{ repeat (rewrite ew_havoc_old; [|cbv; lia]). exact HEs. }
{ cbn [sv_denot]. repeat (rewrite ew_havoc_old; [|cbv; lia]). rewrite Z.add_0_r, HE24, Z_to_bv_bv_unsigned. reflexivity. }
* split; [lia|]. left. split; [reflexivity|]. rewrite Hbl. exact HBc.
+
assert (Himg2 : In (res, N * fmt) (blocks L2 A2)) by (rewrite Hbl2; apply in_app_iff; right; left; reflexivity).
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HH2.
destruct (heap_blocks_range _ _ LAWS L2 A2 mem2 md2 res (N * fmt) HH2 Himg2 ltac:(lia)) as (Hi0 & Hi1 & _).
lazymatch type of HS with st_ok _ ?E1 ?ss1 ?ms1 =>
apply (st_ok_add_fact src2segs E1 ss1 ms1 46 (mkAF 4096 CEIL_MAX 4)) in HS;
[| unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite Hq10, unsigned_lit_small by lia; change (2 ^ 4) with 16; lia ] end.
lazymatch type of HS with st_ok _ _ ?ss1 _ => let v := eval vm_compute in ss1 in change ss1 with v in HS end.
jrun LAWS src2tbl_ok HS HJ2. { wr3 HE2 HEs HEd. }
assert (HU20 : U (havoc E 42 (map (getr regs2) CLOB)) (SAlu ALU_ADD (SMd M_MUL (SOff 18 0) (SOff 10 0)) (SOff 41 0)) = N * fmt + cur).
{ rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SMd. cbn [zmd_raw].
rewrite (U_atom _ 18 N), (U_atom _ 10 fmt), (U_atom _ 41 cur) by first [lia | ew_havoc; assumption].
rewrite (zcanon_id (N * fmt)) by (unfold M64; nia). apply zcanon_id. unfold M64; nia. }
jbranch src2tbl HS.
*
rewrite branch_geu_U, HU20, (U_atom _ 40 nb) in Hc by first [lia | ew_havoc; exact HE22].
assert (Hfit : cur + N * fmt <= nb) by (destruct (Z.ltb_spec nb (N * fmt + cur)); [discriminate Hc | lia]). clear Hc.
jrun_to LAWS src2tbl_ok HS HJ2 src2_A_memcpy. { wr3 HE2 HEs HEd. }
jreg HS (10%bv:reg) as M10. rewrite Hq10 in M10.
jreg HS (11%bv:reg) as M11. rewrite HE25, HE24, alu64_add_lit, ?(Z.add_comm cur pdata) in M11.
lazymatch type of HS with st_ok _ ?Ec ?ssc ?msc => pose proof (st_ok_reg src2segs Ec ssc msc (12%bv:reg) HS) as M12; eval_sr_get_in M12 end.
first [ rewrite (denot_add0_mul _ 18 10 N fmt) in M12 by first [lia | ew_havoc; assumption] | rewrite (denot_mul_atoms_r _ 18 10 N fmt) in M12 by first [lia | ew_havoc; assumption] ].
jreg HS (1%bv:reg) as M1.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HHc. cbn [ms_mem mkst] in HHc.
assert (Hpd2 : In (pdata, nb) (blocks L2 A2)).
{ rewrite Hbl2. apply in_app_iff. destruct (in_app_or b1 b2 (pdata, nb) ltac:(rewrite <- Hblc; exact Hpdc)) as [H0|H0]; [left; exact H0 | right; right; exact H0]. }
eapply SR_bind.
{ eapply (jmemcpy _ _ LAWS IMG _ src2_memcpy) with (d := res) (src := pdata + cur) (n := N * fmt);
[ exact HS | reflexivity | reflexivity | exact HJ2 | exact M10 | exact M11
| exact M12 | exact M1 | apply ret_ok_even; vm_compute; reflexivity | lia | lia | lia | lia | lia | | | | ].
- intros i Hi. apply (proj1 (heap_blocks _ _ LAWS L2 A2 _ md2 res (N * fmt) i HHc Himg2 Hi)).
- intros i Hi. replace (pdata + cur + i) with (pdata + (cur + i)) by lia.
apply (proj1 (heap_blocks _ _ LAWS L2 A2 _ md2 pdata nb (cur + i) HHc Hpd2 ltac:(lia))).
- destruct (heap_sep _ _ LAWS L2 A2 _ md2 b1 (res, N * fmt) b2 (pdata, nb) HHc Hbl2 ltac:(rewrite <- Hblc; exact Hpdc)) as [H0|H0]; cbn [fst snd] in H0; lia.
- intros a Ha. replace a with (res + (a - res)) by lia. apply (Hwr (blocks L2 A2)); [exact Himg2 | lia]. }
cbv beta. intros c' (regs3 & mem3 & -> & HJ3 & Hd10 & Hfr3 & Hout3 & Hgr3 & Hcp3).
jafter_stretch HS 59%nat regs3 mem3 MEMCPY_CLOB RR_AMC HS2.
match type of HS2 with ?P -> ?Q -> _ => assert (HKr : P); [| assert (HKm : Q); [| specialize (HS2 HKr HKm); clear HKr HKm]] end.
{ intros rr Hrr. apply Hfr3. exact Hrr. }
{ constructor; [|constructor; [|constructor; [|constructor]]].
- eapply region_kept_outside; [exact Hout3 | exact Hgr3 | cbn [r_base r_lo base_val]; ew_havoc; rewrite HE2; lia | cbn [r_base r_lo r_hi base_val]; ew_havoc; rewrite HE2; lia | cbn [r_base r_hi base_val]; ew_havoc; rewrite HE2; lia | cbn; lia | cbn; lia].
- eapply region_kept_outside; [exact Hout3 | exact Hgr3 | cbn [r_base r_lo base_val]; ew_havoc; rewrite HEs; lia | cbn [r_base r_lo r_hi base_val]; ew_havoc; rewrite HEs; lia | cbn [r_base r_hi base_val]; ew_havoc; rewrite HEs; lia | cbn; lia | cbn; lia].
- eapply region_kept_outside; [exact Hout3 | exact Hgr3 | cbn [r_base r_lo base_val]; ew_havoc; rewrite HEd; lia | cbn [r_base r_lo r_hi base_val]; ew_havoc; rewrite HEd; lia | cbn [r_base r_hi base_val]; ew_havoc; rewrite HEd; lia | cbn; lia | cbn; lia]. }
clear HS. rename HS2 into HS.
jrun LAWS src2tbl_ok HS HJ3. { wr3 HE2 HEs HEd. }
assert (HBnow : Permutation (blocks L2 A2) ((res, fmt * N) :: Bb)).
{ rewrite Hbl2, (Z.mul_comm fmt N). eapply Permutation_trans; [apply Permutation_sym; apply Permutation_middle|]. apply perm_skip. rewrite <- Hblc. exact HBc. }
eapply (SR_ret_at src2segs src2tbl); [exact src2tbl_ok | | | exact HS | reflexivity | vm_compute; reflexivity |].
{ exact (proj1 (heap_model _ _ LAWS _ _ _ _ (proj1 HJ3))). }
{ exact (proj1 (proj2 (heap_model _ _ LAWS _ _ _ _ (proj1 HJ3)))). }
rimg_fin HS HJ3 Hid2 HX HE HE2 Hra0 1 (cur + N * fmt) res; cbn [ms_mem mkst] in *.
-- right; reflexivity.
-- intros a Ha Hn1 Hn2 Hn3.
mb_frame HF2; try (rewrite ?HE2, ?HEs, ?HEd; lia).
rewrite (mbyte_of_out _ _ res (N * fmt) a Hout3) by lia.
mb_frame HF1; try (rewrite ?HE2, ?HEs, ?HEd; lia).
mb_frame HF0; try (rewrite ?HE2, ?HEs, ?HEd; lia).
rewrite (proj1 (Hhi2 a Ha ltac:(lia))).
mb_frame HF; try (rewrite ?HE2, ?HEs, ?HEd; lia). reflexivity.
-- intros b m i Hb Hi.
assert (Hbc : In (b, m) (blocks Lc Ac)) by (eapply Permutation_in; [apply Permutation_sym; exact HBc | exact Hb]).
destruct (heap_blocks _ _ LAWS Lc Ac mem1 mdc b m i HH Hbc Hi) as (_ & Hb0 & Hb1 & _).
destruct (heap_sep _ _ LAWS L2 A2 _ md2 b1 (res, N * fmt) b2 (b, m) HH2 Hbl2 ltac:(rewrite <- Hblc; exact Hbc)) as [Hs|Hs]; cbn [fst snd] in Hs.
all: mb_frame HF2; try (rewrite ?HE2, ?HEs, ?HEd; lia).
all: rewrite (mbyte_of_out _ _ res (N * fmt) (b + i) Hout3) by lia.
all: mb_frame HF1; try (rewrite ?HE2, ?HEs, ?HEd; lia).
all: mb_frame HF0; try (rewrite ?HE2, ?HEs, ?HEd; lia).
all: rewrite (Hkeep2 b m i Hbc Hi).
all: mb_frame HF; try (rewrite ?HE2, ?HEs, ?HEd; lia); reflexivity.
-- eapply (st_chunk_word _ _ _ 1%nat _ 9%nat 16 _ st (cur + N * fmt) HS); [reflexivity | reflexivity | cbv; auto 10 | | | lia].
{ repeat (rewrite ew_havoc_old; [|cbv; lia]). exact HEs. }
{ rewrite denot_lit_U. f_equal. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SMd. cbn [zmd_raw].
rewrite (U_atom _ 41 cur), (U_atom _ 18 N), (U_atom _ 10 fmt) by first [lia | repeat (rewrite ew_havoc_old; [|cbv; lia]); assumption].
rewrite (zcanon_id (N * fmt)) by (unfold M64; nia). apply zcanon_id. unfold M64; nia. }
-- split; [lia|]. right. split; [reflexivity|]. split; [| split; [lia | split; [| exact HBnow]]].
** rewrite <- (Z.add_0_r dst). eapply (st_chunk_word _ _ _ 2%nat _ 8%nat 0 _ dst res HS); [reflexivity | reflexivity | cbv; auto 10 | | | lia].
{ repeat (rewrite ew_havoc_old; [|cbv; lia]). exact HEd. }
{ cbn [sv_denot]. repeat (rewrite ew_havoc_old; [|cbv; lia]). rewrite !Z.add_0_r, Hq10, Z_to_bv_bv_unsigned. reflexivity. }
** eapply (st_chunk_val src2segs _ _ _ 2%nat _ 8%nat 8 4%N _ dst fmt HS); [reflexivity | reflexivity | cbv; auto 10 | | | cbn; lia | cbn; lia].
{ repeat (rewrite ew_havoc_old; [|cbv; lia]). exact HEd. }
{ cbn [sv_denot]. repeat (rewrite ew_havoc_old; [|cbv; lia]). rewrite !Z.add_0_r, HE10, Z_to_bv_bv_unsigned. reflexivity. }
*
rewrite branch_geu_U, HU20, (U_atom _ 40 nb) in Hc by first [lia | ew_havoc; exact HE22].
assert (Hnofit : nb < cur + N * fmt) by (destruct (Z.ltb_spec nb (N * fmt + cur)); [lia | discriminate Hc]). clear Hc.
jrun_to LAWS src2tbl_ok HS HJ2 src2_A_free. { wr3 HE2 HEs HEd. }
jreg HS (10%bv:reg) as F10. rewrite Hq10 in F10.
jreg HS (2%bv:reg) as F2. rewrite (HE 2%nat 2%bv eq_refl), G2 in F2.
jreg HS (4%bv:reg) as F4. rewrite (HE 4%nat 4%bv eq_refl), G4, Htp0 in F4.
jreg HS (1%bv:reg) as F1.
eapply SR_bind.
{ eapply (jfree_at _ _ LAWS src2_errno_low IMG (aa_free API)) with (a := res) (n := N * fmt) (spc := sp - RRFC_FRAME);
[ exact HS | reflexivity | reflexivity | exact HJ2 | exact Himg2 | exact F10
| exact F2 | lia | exact Hspm | lia | lia | exact F4 | exact F1 | apply ret_ok_even; vm_compute; reflexivity | ].
intros Hin. exfalso. apply Hbase in Hin.
apply (fresh_not_in API L2 A2 _ md2 b1 b2 res (N * fmt) HH2 Hbl2 ltac:(lia)). rewrite <- Hblc.
eapply Permutation_in; [apply Permutation_sym; exact HBc | exact Hin]. }
intros c' (L3 & A3 & regs3 & mem3 & md3 & -> & HJ3 & HP3 & Hrm3 & Hkeep3 & Hhi3 & Hid3).
change (ms_segs src2_msyms) with src2segs in Hkeep3, Hhi3. cbn [ms_regs ms_mem mkst] in HP3, Hkeep3, Hhi3, HJ3, Hrm3.
assert (HB3 : Permutation (blocks L3 A3) Bb).
{ eapply perm_after_rm1; [| exact Hrm3]. rewrite Hbl2. eapply Permutation_trans; [apply Permutation_sym; apply Permutation_middle|]. apply perm_skip. rewrite <- Hblc. exact HBc. }
jafter_call2 HS 59%nat regs3 mem3 HP3 0 [0%nat; 1%nat] HS2.
match type of HS2 with ?P -> _ => assert (HK : P); [|specialize (HS2 HK); clear HK] end.
{ constructor; [|constructor; [|constructor; [|constructor]]].
- eapply (region_kept_stack src2segs _ _ _ 2); [ew_havoc; exact HE2 | exact Hhi3 | lia | lia | lia | cbn; lia | cbn; lia].
- eapply (region_kept_stack src2segs _ _ _ 9); [ew_havoc; exact HEs | exact Hhi3 | lia | lia | lia | cbn; lia | cbn; lia].
- eapply (region_kept_stack src2segs _ _ _ 8); [ew_havoc; exact HEd | exact Hhi3 | lia | lia | lia | cbn; lia | cbn; lia]. }
clear HS. rename HS2 into HS.
jrun LAWS src2tbl_ok HS HJ3. { wr3 HE2 HEs HEd. }
eapply (SR_ret_at src2segs src2tbl); [exact src2tbl_ok | | | exact HS | reflexivity | vm_compute; reflexivity |].
{ exact (proj1 (heap_model _ _ LAWS _ _ _ _ (proj1 HJ3))). }
{ exact (proj1 (proj2 (heap_model _ _ LAWS _ _ _ _ (proj1 HJ3)))). }
rimg_fin HS HJ3 Hid3 HX HE HE2 Hra0 0 nb 0; cbn [ms_mem mkst] in *.
-- left; reflexivity.
-- intros a Ha Hn1 Hn2 Hn3.
mb_frame HF2; try (rewrite ?HE2, ?HEs, ?HEd; lia).
rewrite (proj1 (Hhi3 a Ha ltac:(lia))).
mb_frame HF1; try (rewrite ?HE2, ?HEs, ?HEd; lia).
mb_frame HF0; try (rewrite ?HE2, ?HEs, ?HEd; lia).
rewrite (proj1 (Hhi2 a Ha ltac:(lia))).
mb_frame HF; try (rewrite ?HE2, ?HEs, ?HEd; lia). reflexivity.
-- intros b m i Hb Hi.
assert (Hbc : In (b, m) (blocks Lc Ac)) by (eapply Permutation_in; [apply Permutation_sym; exact HBc | exact Hb]).
destruct (heap_blocks _ _ LAWS Lc Ac mem1 mdc b m i HH Hbc Hi) as (_ & Hb0 & Hb1 & _).
assert (Hb3 : In (b, m) (blocks L3 A3)) by (eapply Permutation_in; [apply Permutation_sym; exact HB3 | exact Hb]).
mb_frame HF2; try (rewrite ?HE2, ?HEs, ?HEd; lia).
rewrite (Hkeep3 b m i Hb3 Hi).
mb_frame HF1; try (rewrite ?HE2, ?HEs, ?HEd; lia).
mb_frame HF0; try (rewrite ?HE2, ?HEs, ?HEd; lia).
rewrite (Hkeep2 b m i Hbc Hi).
mb_frame HF; try (rewrite ?HE2, ?HEs, ?HEd; lia). reflexivity.
-- eapply (st_chunk_word _ _ _ 1%nat _ 9%nat 16 _ st nb HS); [reflexivity | reflexivity | cbv; auto 10 | | | lia].
{ repeat (rewrite ew_havoc_old; [|cbv; lia]). exact HEs. }
{ cbn [sv_denot]. repeat (rewrite ew_havoc_old; [|cbv; lia]). rewrite !Z.add_0_r, HE22, Z_to_bv_bv_unsigned. reflexivity. }
-- split; [lia|]. left. split; [reflexivity|]. exact HB3.
Qed.
End S.
End c.
