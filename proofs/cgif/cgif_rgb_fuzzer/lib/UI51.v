(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0p YK0i YK0j YK14 YK1b YK1a YK15 YN06 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ00.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP0j YP0g YP0r YP0c YP0e.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import UH04 UH07 UH06 UO3m YI00 YI02 YI01 YI03
UI1e UI1i UI59 UI56 YI0x YL0e YI08 YI0c UI3h UI3d
UI39 UI57 UI58 UI4y UI55 UI4z UO0e.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Definition RL_AFT : Z := Eval vm_compute in (ubs2_A_LLVMFuzzerTestOneInput + 0xf8).
Lemma perm_img_front : forall (x y : Z * Z) (l1 l2 l3 : list (Z * Z)),
Permutation (x :: l1 ++ l2 ++ [y] ++ l3) (y :: x :: l1 ++ l2 ++ l3).
Proof.
intros x y l1 l2 l3.
replace (x :: l1 ++ l2 ++ [y] ++ l3) with ((x :: l1 ++ l2) ++ y :: l3) by (cbn; rewrite <- app_assoc; reflexivity).
replace (y :: x :: l1 ++ l2 ++ l3) with (y :: (x :: l1 ++ l2) ++ l3) by (cbn; rewrite <- app_assoc; reflexivity).
apply Permutation_sym, Permutation_middle.
Qed.
Ltac rstack_word HS HU2 n Hn :=
lazymatch goal with |- word_mem _ _ (?spv - ?dd) ?v =>
replace (spv - dd) with (spv - 128 + (128 - dd)) by lia;
eapply (st_chunk_word _ _ _ 0%nat _ 2%nat (128 - dd) (SOff n 0) (spv - 128) v HS);
[ reflexivity | reflexivity | cbv; auto 60
| ew_havocA; exact HU2
| cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, Hn; first [reflexivity | rewrite Z_to_bv_bv_unsigned; reflexivity]
| ]
end.
Ltac rsaved_ok_tac HS HU2 H32 H33 H34 H35 :=
unfold rsaved_ok;
split; [rstack_word HS HU2 32%nat H32; apply u64_range'|];
split; [rstack_word HS HU2 33%nat H33; apply u64_range'|];
split; [rstack_word HS HU2 34%nat H34; apply u64_range'|];
rstack_word HS HU2 35%nat H35; apply u64_range'.
Ltac runtouched_tac HS HE G3 G4 G19 G20 G21 G22 G23 G24 G25 G26 G27 :=
split; [reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 3%nat 3%bv eq_refl); exact G3)|];
split; [reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 4%nat 4%bv eq_refl); exact G4)|];
split; [reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 19%nat 19%bv eq_refl); exact G19)|];
split; [reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 20%nat 20%bv eq_refl); exact G20)|];
split; [reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 21%nat 21%bv eq_refl); exact G21)|];
split; [reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 22%nat 22%bv eq_refl); exact G22)|];
split; [reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 23%nat 23%bv eq_refl); exact G23)|];
split; [reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 24%nat 24%bv eq_refl); exact G24)|];
split; [reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 25%nat 25%bv eq_refl); exact G25)|];
split; [reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 26%nat 26%bv eq_refl); exact G26)|];
reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 27%nat 27%bv eq_refl); exact G27).
Lemma perm_ib_back : forall (ib : list (Z * Z)) (x : Z * Z) (l1 l2 l3 : list (Z * Z)),
Permutation (ib ++ x :: l1 ++ l2 ++ l3) (x :: l1 ++ l2 ++ ib ++ l3).
Proof.
intros ib x l1 l2 l3.
replace (ib ++ x :: l1 ++ l2 ++ l3) with (ib ++ (x :: l1 ++ l2) ++ l3) by (cbn; rewrite <- app_assoc; reflexivity).
replace (x :: l1 ++ l2 ++ ib ++ l3) with ((x :: l1 ++ l2) ++ ib ++ l3) by (cbn; rewrite <- app_assoc; reflexivity).
apply Permutation_app_swap_app.
Qed.
Ltac reg_nowR HS tac :=
lazymatch type of HS with st_ok _ ?Ec ?ssc ?msc =>
lazymatch goal with |- getr _ ?rr = _ =>
let T := fresh "T" in
pose proof (st_ok_reg ubs2segs Ec ssc msc rr HS) as T; eval_sr_get_in T; cbn [sv_denot ms_regs mkst] in T;
repeat (rewrite ew_havoc_old in T; [|nat_lt_lit]); rewrite ?Z.add_0_r in T;
cbn [ms_regs mkst]; rewrite T; clear T; tac
end
end.
Ltac runtouched_tacR HS HE G3 G4 G19 G20 G21 G22 G23 G24 G25 G26 G27 :=
split; [reg_nowR HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 3%nat 3%bv eq_refl); exact G3)|];
split; [reg_nowR HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 4%nat 4%bv eq_refl); exact G4)|];
split; [reg_nowR HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 19%nat 19%bv eq_refl); exact G19)|];
split; [reg_nowR HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 20%nat 20%bv eq_refl); exact G20)|];
split; [reg_nowR HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 21%nat 21%bv eq_refl); exact G21)|];
split; [reg_nowR HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 22%nat 22%bv eq_refl); exact G22)|];
split; [reg_nowR HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 23%nat 23%bv eq_refl); exact G23)|];
split; [reg_nowR HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 24%nat 24%bv eq_refl); exact G24)|];
split; [reg_nowR HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 25%nat 25%bv eq_refl); exact G25)|];
split; [reg_nowR HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 26%nat 26%bv eq_refl); exact G26)|];
reg_nowR HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 27%nat 27%bv eq_refl); exact G27).
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section J.
Variable B : malloc_syms.
Variable MR : MR_t.
Hypothesis LAWS : MR_laws B MR.
Local Notation segs := (ms_segs B).
Lemma jcall_tmpF : forall E ss ms STK sp0 FP L A mem md Lc Ac mdc STK1 FP1
(K : FPState -> layout -> astate -> bvmap 5 word -> (word -> option byte) -> Model -> Prop) raw,
st_ok segs E ss ms -> ss_resv ss = None ->
journal B MR STK sp0 FP L A mem md Lc Ac (ms_mem ms) mdc ->
getr (ms_regs ms) 1 = raw ->
(fn_pre B MR STK1 Lc Ac (ms_regs ms) (ms_mem ms) mdc ->
SR segs (mkCfg (mkst (ms_regs ms) (Z_to_bv 64 (ss_pc ss)) (ms_mem ms) (seg_rom segs)) mdc)
(fun c' => exists (fx' : FPState) L2 A2 regs2 mem2 md2,
c' = mkCfg (@mkst fx' regs2 raw mem2 (seg_rom segs)) md2 /\
journal B MR STK1 (spZ (ms_regs ms)) FP1 Lc Ac (ms_mem ms) mdc L2 A2 mem2 md2 /\
regs_preserved (ms_regs ms) regs2 /\ K fx' L2 A2 regs2 mem2 md2)) ->
YK0s.ret_ok raw -> spZ (ms_regs ms) mod 16 = 0 -> 0 <= STK1 ->
sp0 - STK <= spZ (ms_regs ms) - STK1 -> spZ (ms_regs ms) <= sp0 ->
getr (ms_regs ms) 4 = Z_to_bv 64 (ms_tp B) ->
(forall a, inFP FP1 a -> (inFP FP a /\ a < alloc_ceiling) \/
(exists b n, In (b, n) (blocks Lc Ac) /\ ~ In (b, n) (blocks L A) /\ b <= a < b + n)) ->
SR segs (mkCfg ms mdc)
(fun c' => exists (fx' : FPState) L2 A2 regs2 mem2 md2,
c' = mkCfg (@mkst fx' regs2 raw mem2 (seg_rom segs)) md2 /\
journal B MR STK sp0 FP L A mem md L2 A2 mem2 md2 /\
journal B MR STK1 (spZ (ms_regs ms)) FP1 Lc Ac (ms_mem ms) mdc L2 A2 mem2 md2 /\
regs_preserved (ms_regs ms) regs2 /\ K fx' L2 A2 regs2 mem2 md2).
Proof.
intros E ss ms STK sp0 FP L A mem md Lc Ac mdc STK1 FP1 K raw HS Hrv HJ Hra Hcallee Hraw Hal16 Hstk1 Hlo Hhi Htp HF.
rewrite (st_ok_mkst segs E ss ms HS Hrv).
eapply SR_mono.
{ apply Hcallee. eapply (fn_pre_of_journal B MR); [exact HJ | rewrite Hra; exact Hraw | exact Hal16 | exact Hstk1 | exact Hlo | exact Hhi | exact Htp]. }
intros c' (fx' & L2 & A2 & regs2 & mem2 & md2 & -> & HJ1 & HP & HK).
exists fx', L2, A2, regs2, mem2, md2. split; [reflexivity|]. split; [| split; [exact HJ1 | split; [exact HP | exact HK]]].
eapply (journal_sub_gen B MR LAWS); [exact HJ | exact HJ1 | exact Hlo | exact Hhi | exact HF].
Qed.
End J.
Definition ss_raft : sstate :=
mkSS RL_AFT sr_atoms
[ YQ0b.mkRegion (Some 2%nat) 8 128 8 128
([mkChunk 8 (CVal 8 (SOff 36 0)); mkChunk 16 (CVal 8 (SOff 37 0)); mkChunk 24 (CVal 8 (SOff 38 0))]
++ obj_chunks_gen (lay_shift 32 LAY_RgbFrameConfig) 39 [] ++ rsaved_chunks 32) ]
None
(mkFacts [ (2%nat, mkAF (CEIL_MIN + LIB_STACK_RGB - 128) (2^63 - 128) 4);
(8%nat, mkAF 1 RGB_NMAX 0); (9%nat, mkAF 4096 (CEIL_MAX - 64) 4);
(18%nat, mkAF 1 16 0); (36%nat, mkAF 4096 CEIL_MAX 0);
(37%nat, mkAF 1 CEIL_MAX 0); (38%nat, mkAF 0 CEIL_MAX 0); (39%nat, mkAF 0 (2^64 - 1) 0) ] [] []).
Definition ss_raft_c : sstate := Eval vm_compute in ss_raft.
Section S.
Variable API : AllocAPI ubs2_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs2_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs2_msyms MR.
Hypothesis CLOSE : forall fx', rgb_close_spec (fx:=fx') API.
Hypothesis ADDF : forall fx', rgb_addframe_spec (fx:=fx') API.
Definition RLH (fx1 : FPState) (k : nat) : Prop :=
forall L A mem md (regs0 regs1 : bvmap 5 word) Lc Ac memc mdc
(r g wfn ctx path attr gen loops W H bef beffmt cres : Z) (s : cgif_st) (N : Z) (rest : list (Z * Z))
(pdata nb cur img fmt fattr fgen delay : Z),
frm_zero (@fp_csr fx1) ->
journal ubs2_msyms MR LIB_STACK_RGB (spZ regs0) [] L A mem md Lc Ac memc mdc -> st_init_done Ac = true ->
YK0s.ret_ok (getr regs0 1) -> getr regs0 4 = Z_to_bv 64 (ms_tp ubs2_msyms) -> spZ regs0 mod 16 = 0 ->
ubs2_rgb_rodata_ok mem ->
obj_at ubs2segs memc r LAY_Rgb [g; wfn; ctx; path; attr; gen; loops; W; H; bef; beffmt; cres] ->
cgif_at memc g s -> cgif_wf s N -> cg_W s = W -> cg_H s = H -> N <= RGB_NMAX -> (bef = 0 \/ beffmt = 3 \/ beffmt = 4) ->
Permutation (blocks Lc Ac) ((r, RGB_SIZE) :: cgif_blocks g s N ++ optb bef (beffmt * N) ++ img_block img fmt N ++ rest) ->
(forall b, In b (blocks L A) -> In b rest) -> In (pdata, nb) (blocks L A) -> 0 < nb ->
rsaved_ok memc (spZ regs0) regs0 ->
word_mem ubs2segs memc (spZ regs0 - 120) pdata -> word_mem ubs2segs memc (spZ regs0 - 112) nb ->
word_mem ubs2segs memc (spZ regs0 - 104) cur -> 0 <= cur <= nb ->
obj_at ubs2segs memc (spZ regs0 - 96) LAY_RgbFrameConfig [img; fmt; fattr; fgen; delay] ->
(fmt_okb fmt = false -> img = 0) -> 0 <= img < 2 ^ 64 ->
getr regs1 2 = Z_to_bv 64 (spZ regs0 - 128) -> getr regs1 8 = Z_to_bv 64 N -> getr regs1 9 = Z_to_bv 64 r ->
getr regs1 18 = Z_to_bv 64 (Z.of_nat k) -> runtouched_ok regs0 regs1 ->
SR ubs2segs (mkCfg (@mkst fx1 regs1 (Z_to_bv 64 RL_LH) memc (seg_rom ubs2segs)) mdc)
(rllvm_post API regs0 L A mem md).
Lemma rl_after : forall (k : nat),
((1 <= k)%nat -> forall fx', RLH fx' k) ->
forall L A mem md (regs0 regs1 : bvmap 5 word) Lc Ac memc mdc
(r g wfn ctx path attr gen loops W H bef beffmt cres : Z) (s : cgif_st) (N : Z) (rest : list (Z * Z))
(pdata nb cur img fmt fattr fgen delay : Z),
(k <= 15)%nat ->
frm_zero fp_csr ->
journal ubs2_msyms MR LIB_STACK_RGB (spZ regs0) [] L A mem md Lc Ac memc mdc -> st_init_done Ac = true ->
YK0s.ret_ok (getr regs0 1) -> getr regs0 4 = Z_to_bv 64 (ms_tp ubs2_msyms) -> spZ regs0 mod 16 = 0 ->
ubs2_rgb_rodata_ok mem ->
obj_at ubs2segs memc r LAY_Rgb [g; wfn; ctx; path; attr; gen; loops; W; H; bef; beffmt; cres] ->
cgif_at memc g s -> cgif_wf s N -> cg_W s = W -> cg_H s = H -> N <= RGB_NMAX -> (bef = 0 \/ beffmt = 3 \/ beffmt = 4) ->
Permutation (blocks Lc Ac) ((r, RGB_SIZE) :: cgif_blocks g s N ++ optb bef (beffmt * N) ++ img_block img fmt N ++ rest) ->
(forall b, In b (blocks L A) -> In b rest) -> In (pdata, nb) (blocks L A) -> 0 < nb ->
rsaved_ok memc (spZ regs0) regs0 ->
word_mem ubs2segs memc (spZ regs0 - 120) pdata -> word_mem ubs2segs memc (spZ regs0 - 112) nb ->
word_mem ubs2segs memc (spZ regs0 - 104) cur -> 0 <= cur <= nb ->
obj_at ubs2segs memc (spZ regs0 - 96) LAY_RgbFrameConfig [img; fmt; fattr; fgen; delay] ->
(fmt_okb fmt = false -> img = 0) -> 0 <= img < 2 ^ 64 ->
getr regs1 2 = Z_to_bv 64 (spZ regs0 - 128) -> getr regs1 8 = Z_to_bv 64 N -> getr regs1 9 = Z_to_bv 64 r ->
getr regs1 18 = Z_to_bv 64 (Z.of_nat (Datatypes.S k)) -> runtouched_ok regs0 regs1 ->
SR ubs2segs (mkCfg (mkst regs1 (Z_to_bv 64 RL_AFT) memc (seg_rom ubs2segs)) mdc)
(rllvm_post API regs0 L A mem md).
Proof.
intros k KLH L A mem md regs0 regs1 Lc Ac memc mdc r g wfn ctx path attr gen loops W H bef beffmt cres s N rest
pdata nb cur img fmt fattr fgen delay
Hk HFZ HJ Hid Hra0 Htp0 Hal16 HRO Hobj Hat Hwf HsW HsH HNmax Hbef HB Hbase Hpd Hnb HSV Wp Wn Wc Hcur Hfc Himg0 Himg
G2 G8 G9 G18 HUT.
pose proof HUT as (G3 & G4 & G19 & G20 & G21 & G22 & G23 & G24 & G25 & G26 & G27).
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HLSv : LIB_STACK_RGB = 61440) by reflexivity.
assert (HRSv : RRFC_STK = 8272) by reflexivity. assert (HALv : ALLOC_STACK = 8192) by reflexivity.
assert (HNMv : RGB_NMAX = 10000) by reflexivity. assert (HFCv : RGBFC_SIZE = 24) by reflexivity.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HH0.
pose proof HJ as (_ & _ & _ & _ & _ & (Hsp0al & Hstk0 & Hceil & Hsp063 & Hstw) & _).
set (sp0 := spZ regs0) in *.
assert (Hspm : (sp0 - 128) mod 16 = 0) by (replace (sp0 - 128) with (sp0 + (-8) * 16) by lia; rewrite Z.mod_add by lia; exact Hal16).
assert (Hcf8 : (sp0 - 96) mod 8 = 0).
{ pose proof (proj2 (Z.div_exact sp0 16 ltac:(lia)) Hal16) as E16. replace (sp0 - 96) with ((2 * (sp0 / 16) - 12) * 8) by lia. apply Z_mod_mult. }
assert (Hst8 : (sp0 - 120) mod 8 = 0).
{ pose proof (proj2 (Z.div_exact sp0 16 ltac:(lia)) Hal16) as E16. replace (sp0 - 120) with ((2 * (sp0 / 16) - 15) * 8) by lia. apply Z_mod_mult. }
pose proof Hwf as (Hlen3 & HW1 & HH1 & HN & HNle & Hngp & Hih & Hfwf).
assert (Hrin : In (r, RGB_SIZE) (blocks Lc Ac)) by (eapply Permutation_in; [apply Permutation_sym; exact HB | left; reflexivity]).
destruct (heap_blocks_range _ _ LAWS Lc Ac memc mdc r RGB_SIZE HH0 Hrin ltac:(unfold RGB_SIZE; lia)) as (Hr0 & Hr1 & Hr16). unfold RGB_SIZE in Hr1.
assert (Hpdc : In (pdata, nb) (blocks Lc Ac)).
{ eapply Permutation_in; [apply Permutation_sym; exact HB|]. right. apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. right. apply Hbase. exact Hpd. }
destruct (blocks_range _ _ LAWS Lc Ac memc mdc pdata nb HH0 Hpdc) as [Hp0 Hp1].
pose proof (obj_at_range _ _ _ _ _ Hfc) as Rfc.
set (fvals := [img; fmt; fattr; fgen; delay]) in *.
set (E := Ereg regs1 (map (Z_to_bv 64) (rsaved_vals regs0) ++ map (Z_to_bv 64) ([pdata; nb; cur] ++ fvals) ++ [])).
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HSV' : forall j v, nth_error (rsaved_vals regs0) j = Some v -> ew E (32 + j) = Z_to_bv 64 v) by (intros j v Hj; subst E; apply Ereg_vals; exact Hj).
assert (HY : forall j v, nth_error ([pdata; nb; cur] ++ fvals) j = Some v -> ew E (36 + j) = Z_to_bv 64 v).
{ intros j v Hj. subst E. replace (36 + j)%nat with (32 + (length (rsaved_vals regs0) + j))%nat by reflexivity. apply Ereg_vals2. exact Hj. }
assert (HFV : forall j v, nth_error fvals j = Some v -> ew E (39 + j) = Z_to_bv 64 v).
{ intros j v Hj. replace (39 + j)%nat with (36 + (3 + j))%nat by lia. apply HY. exact Hj. }
assert (HW32 : ew E 32 = getr regs0 1) by (etransitivity; [apply (HSV' 0%nat); reflexivity | apply Z_to_bv_bv_unsigned]).
assert (HW33 : ew E 33 = getr regs0 8) by (etransitivity; [apply (HSV' 1%nat); reflexivity | apply Z_to_bv_bv_unsigned]).
assert (HW34 : ew E 34 = getr regs0 9) by (etransitivity; [apply (HSV' 2%nat); reflexivity | apply Z_to_bv_bv_unsigned]).
assert (HW35 : ew E 35 = getr regs0 18) by (etransitivity; [apply (HSV' 3%nat); reflexivity | apply Z_to_bv_bv_unsigned]).
assert (HU2 : bv_unsigned (ew E 2) = sp0 - 128) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; lia).
assert (HU8 : bv_unsigned (ew E 8) = N) by (rewrite (HE 8%nat 8%bv eq_refl), G8; apply unsigned_lit_small; lia).
assert (HU9 : bv_unsigned (ew E 9) = r) by (rewrite (HE 9%nat 9%bv eq_refl), G9; apply unsigned_lit_small; lia).
assert (HU18 : bv_unsigned (ew E 18) = Z.of_nat (Datatypes.S k)) by (rewrite (HE 18%nat 18%bv eq_refl), G18; apply unsigned_lit_small; lia).
assert (HX36 : ew E 36 = Z_to_bv 64 pdata) by (apply (HY 0%nat); reflexivity).
assert (HX37 : ew E 37 = Z_to_bv 64 nb) by (apply (HY 1%nat); reflexivity).
assert (HX38 : ew E 38 = Z_to_bv 64 cur) by (apply (HY 2%nat); reflexivity).
assert (HX39 : ew E 39 = Z_to_bv 64 img) by (apply (HY 3%nat); reflexivity).
pose proof HSV as (W1 & W8 & W9 & W18).
assert (HS : st_ok ubs2segs E ss_raft_c (mkst regs1 (Z_to_bv 64 RL_AFT) memc (seg_rom ubs2segs))).
{ change ss_raft_c with ss_raft. unfold ss_raft. subst E. apply entry_st_ok.
- vm_compute. reflexivity.
- constructor; [|constructor].
unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU2.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply (journal_stack_w _ _ _ _ _ _ _ _ _ _ _ _ _ HJ). lia. }
apply Forall_app; split; [|apply Forall_app; split].
+ apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ pdata); [cbn [sv_denot]; rewrite Z.add_0_r, HX36, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | replace (sp0 - 128 + 8) with (sp0 - 120) by lia; apply val_mem_word_mem; exact Wp]. }
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ nb); [cbn [sv_denot]; rewrite Z.add_0_r, HX37, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | replace (sp0 - 128 + 16) with (sp0 - 112) by lia; apply val_mem_word_mem; exact Wn]. }
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ cur); [cbn [sv_denot]; rewrite Z.add_0_r, HX38, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | replace (sp0 - 128 + 24) with (sp0 - 104) by lia; apply val_mem_word_mem; exact Wc]. }
apply Forall_nil.
+ eapply (obj_chunks_gen_ok ubs2segs _ _ (sp0 - 128) _ fvals 39 []); [| reflexivity | | intros j z Hj; destruct j; discriminate Hj].
* apply (proj1 (obj_at_shift _ _ (sp0 - 128) 32 LAY_RgbFrameConfig fvals)). replace (sp0 - 128 + 32) with (sp0 - 96) by lia. exact Hfc.
* intros j v Hj. apply (HFV j v Hj).
+ assert (CK : forall off j (w : Z), nth_error (rsaved_vals regs0) j = Some w -> word_mem ubs2segs memc (sp0 - 128 + off) w -> 0 <= w < 2 ^ 64 ->
chunk_ok ubs2segs (Ereg regs1 (map (Z_to_bv 64) (rsaved_vals regs0) ++ map (Z_to_bv 64) ([pdata; nb; cur] ++ fvals) ++ [])) memc (sp0 - 128) (mkChunk off (CVal 8 (SOff (32 + j) 0)))).
{ intros off j w Hj Wm Rw. eapply (chunk_ok_val _ _ _ _ _ _ _ w); [| cbn; lia | cbn; lia | apply val_mem_word_mem; exact Wm].
cbn [sv_denot]. rewrite Z.add_0_r, (HSV' j w Hj), Z_to_bv_bv_unsigned. reflexivity. }
assert (RU : forall w : word, 0 <= bv_unsigned w < 2 ^ 64).
{ intros w. pose proof (bv_unsigned_in_range 64 w) as Rw. change (bv_modulus 64) with (2 ^ 64) in Rw. lia. }
unfold rsaved_chunks. cbn [Nat.add].
repeat (apply Forall_cons;
[ first [ apply (CK 120 0%nat _ eq_refl); [replace (sp0 - 128 + 120) with (sp0 - 8) by lia; exact W1 | apply RU]
| apply (CK 112 1%nat _ eq_refl); [replace (sp0 - 128 + 112) with (sp0 - 16) by lia; exact W8 | apply RU]
| apply (CK 104 2%nat _ eq_refl); [replace (sp0 - 128 + 104) with (sp0 - 24) by lia; exact W9 | apply RU]
| apply (CK 96 3%nat _ eq_refl); [replace (sp0 - 128 + 96) with (sp0 - 32) by lia; exact W18 | apply RU] ] | ]).
apply Forall_nil.
- cbn [pairwise_disjoint all_disjoint]. repeat split.
- cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HU2, HU8, HU9, HU18, HX36, HX37, HX38, HX39, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
repeat split; try lia; assumption. }
change memc with (ms_mem (mkst regs1 (Z_to_bv 64 RL_AFT) memc (seg_rom ubs2segs))) in HJ.
assert (Hio : img_block img fmt N = optb img (fmt * N)).
{ unfold img_block, optb. destruct (fmt_okb fmt) eqn:Hfo.
- destruct (Z.eqb_spec img 0) as [Hz|Hz]; [|reflexivity]. exfalso.
assert (Himgc : In (img, fmt * N) (blocks Lc Ac)).
{ eapply Permutation_in; [apply Permutation_sym; exact HB|]. right. apply in_app_iff. right. apply in_app_iff. right. unfold img_block. rewrite Hfo. left. reflexivity. }
apply fmt_okb_true in Hfo.
destruct (heap_blocks_range _ _ LAWS Lc Ac memc mdc img (fmt * N) HH0 Himgc ltac:(lia)) as (H00 & _). lia.
- rewrite (Himg0 eq_refl). reflexivity. }
assert (HBo : Permutation (blocks Lc Ac) (optb img (fmt * N) ++ (r, RGB_SIZE) :: cgif_blocks g s N ++ optb bef (beffmt * N) ++ rest)).
{ eapply Permutation_trans; [exact HB|]. rewrite Hio. unfold optb. destruct (img =? 0); [apply Permutation_refl|].
cbn [app]. apply perm_img_front. }
jrun_to LAWS ubs2tbl_ok HS HJ ubs2_A_free.
{ eapply wr_ok_cons_win; [reflexivity | exact HU2 | cbn [r_wlo r_whi]; intros _; lia |]. apply wr_ok_nil. }
jreg HS (10%bv:reg) as Hb10. rewrite HX39 in Hb10.
jreg HS (2%bv:reg) as Hb2. rewrite (HE 2%nat 2%bv eq_refl), G2 in Hb2.
jreg HS (4%bv:reg) as Hb4. rewrite (HE 4%nat 4%bv eq_refl), G4, Htp0 in Hb4.
jreg HS (1%bv:reg) as Hb1.
eapply SR_bind.
{ eapply (jfree_opt _ _ LAWS ubs2_errno_low IMG (aa_free API) (aa_free_null API)) with (p := img) (n := fmt * N) (spc := sp0 - 128);
[ exact HS | reflexivity | reflexivity | exact HJ | exact HBo | exact Hb10
| exact Hb2 | lia | exact Hspm | lia | lia | exact Hb4 | exact Hb1 | apply ret_ok_even; vm_compute; reflexivity | ].
intros Hnz Hin i Hi. exfalso. apply Hbase in Hin.
unfold optb in HBo. destruct (Z.eqb_spec img 0) as [Hz|Hz]; [lia|]. cbn [app] in HBo.
destruct (heap_sep_perm _ _ LAWS Lc Ac memc mdc (img, fmt * N) _ (img, fmt * N) HH0 HBo ltac:(right; apply in_app_iff; right; apply in_app_iff; right; exact Hin)) as [H1|H1]; cbn [fst snd] in H1; lia. }
intros c' (L5 & A5 & regs5 & mem5 & md5 & -> & HJ5 & HP5 & HB5 & Hkeep5 & Hhi5). clear HJ.
change (ms_segs ubs2_msyms) with ubs2segs in Hkeep5, Hhi5. cbn [ms_regs ms_mem mkst] in HP5, Hkeep5, Hhi5, HJ5, HB5.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ5) as HH5.
assert (Hid5 : st_init_done A5 = true).
{ assert (Hr5 : In (r, RGB_SIZE) (blocks L5 A5)) by (eapply Permutation_in; [apply Permutation_sym; exact HB5 | left; reflexivity]).
apply blocks_In in Hr5 as (q & _ & Hq). exact (init_done_of_block A5 (q, RGB_SIZE) (proj1 (proj2 HH5)) Hq). }
jafter_call_keep HS 44%nat regs5 mem5 HP5 [0%nat] HS2.
match type of HS2 with ?P -> _ => assert (HK : P); [|specialize (HS2 HK); clear HK] end.
{ constructor; [|constructor].
eapply (region_kept_stack ubs2segs _ _ _ 2); [ew_havocA; exact HU2 | exact Hhi5 | lia | lia | lia | cbn; lia | cbn; lia]. }
clear HS. rename HS2 into HS.
assert (Hr5 : In (r, RGB_SIZE) (blocks L5 A5)) by (eapply Permutation_in; [apply Permutation_sym; exact HB5 | left; reflexivity]).
assert (Hobj5 : obj_at ubs2segs mem5 r LAY_Rgb [g; wfn; ctx; path; attr; gen; loops; W; H; bef; beffmt; cres]).
{ eapply obj_at_transport_range; [exact Hobj | apply lay_inside_Rgb |]. intros i Hi. unfold RGB_SIZE in Hi.
rewrite (Hkeep5 r RGB_SIZE i Hr5) by (unfold RGB_SIZE; lia). mem_back ltac:(rewrite ?HU2) ltac:(lia). }
assert (Hat5 : cgif_at mem5 g s).
{ eapply (cgif_at_kept _ _ g s N (blocks L5 A5) ((r, RGB_SIZE) :: optb bef (beffmt * N) ++ rest)); [| | exact Hkeep5].
{ eapply Permutation_trans; [exact HB5 | apply Permutation_middle]. }
eapply (cgif_at_low API); [exact HH0 | | exact Hat |].
{ eapply Permutation_trans; [exact HB | apply Permutation_middle]. }
intros a Ha. mem_back ltac:(rewrite ?HU2) ltac:(lia). }
jrun LAWS ubs2tbl_ok HS HJ5.
{ eapply wr_ok_cons_win; [reflexivity | ew_havocA; exact HU2 | cbn [r_wlo r_whi]; intros _; lia |]. apply wr_ok_nil. }
jbranch ubs2tbl HS.
-
jrun_to LAWS ubs2tbl_ok HS HJ5 RL_CLOSE.
{ eapply wr_ok_cons_win; [reflexivity | ew_havocA; exact HU2 | cbn [r_wlo r_whi]; intros _; lia |]. apply wr_ok_nil. }
rewrite (st_ok_mkst ubs2segs _ _ _ HS eq_refl). cbn [ss_pc].
lazymatch goal with |- SR _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
eapply (rl_close API IMG (CLOSE fx) L A mem md regs0 rg L5 A5 mm md5 r _ g s N bef (beffmt * N) rest) end.
+ exact HFZ. + exact HJ5. + exact Hid5. + exact Hra0. + exact Htp0. + exact Hal16.
+ eapply obj_at_transport_range; [exact Hobj5 | apply lay_inside_Rgb |]. intros i Hi. unfold RGB_SIZE in Hi. mem_back ltac:(rewrite ?HU2) ltac:(lia).
+ reflexivity. + reflexivity.
+ eapply (cgif_at_low API); [exact HH5 | | exact Hat5 |]; [eapply Permutation_trans; [exact HB5 | apply Permutation_middle] |].
intros a Ha. mem_back ltac:(rewrite ?HU2) ltac:(lia).
+ exact Hwf. + exact HB5. + exact Hbase.
+ exists (pdata, nb). split; [exact Hpd | cbn; lia].
+ rsaved_ok_tac HS HU2 HW32 HW33 HW34 HW35.
+ reg_nowF HS ltac:(rewrite HU2; f_equal; lia).
+ reg_nowF HS ltac:(rewrite HU9; reflexivity).
+ runtouched_tac HS HE G3 G4 G19 G20 G21 G22 G23 G24 G25 G26 G27.
-
rewrite branch_eq_U, U_lit, (U_atom_off _ 18 (Z.of_nat (Datatypes.S k)) (-1)) in Hc by first [lia | ew_havocA; rewrite (HE 18%nat 18%bv eq_refl); exact G18].
assert (Hk1 : (1 <= k)%nat) by (destruct (Z.eqb_spec (Z.of_nat (Datatypes.S k) + -1) 0); [discriminate Hc | lia]). clear Hc.
jrun_to LAWS ubs2tbl_ok HS HJ5 ubs2_A_read_frameconfig.
{ eapply wr_ok_cons_win; [reflexivity | ew_havocA; exact HU2 | cbn [r_wlo r_whi]; intros _; lia |]. apply wr_ok_nil. }
jreg HS (10%bv:reg) as Hd10. rewrite HU2 in Hd10. jreg HS (11%bv:reg) as Hd11. rewrite HU2 in Hd11.
jreg HS (12%bv:reg) as Hd12. rewrite (HE 8%nat 8%bv eq_refl), G8 in Hd12.
jreg HS (2%bv:reg) as Hd2. rewrite (HE 2%nat 2%bv eq_refl), G2 in Hd2.
jreg HS (4%bv:reg) as Hd4. rewrite (HE 4%nat 4%bv eq_refl), G4, Htp0 in Hd4. jreg HS (1%bv:reg) as Hd1.
lazymatch goal with |- SR _ (mkCfg ?msx _) _ =>
assert (Hsp : spZ (ms_regs msx) = sp0 - 128) by (unfold spZ; rewrite Hd2; apply unsigned_lit_small; lia) end.
rewrite (st_ok_mkst ubs2segs _ _ _ HS eq_refl). cbn [ss_pc].
eapply SR_bind.
{ lazymatch goal with |- SR _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
eapply (ubs2_read_frameconfig API IMG LIB_STACK_RGB sp0 [] L A mem md L5 A5 mm md5 rg ((r, RGB_SIZE) :: cgif_blocks g s N ++ optb bef (beffmt * N) ++ rest) (sp0 - 120) (sp0 - 96) N pdata nb cur) end.
+ exact HJ5. + exact Hid5.
+ intros b Hb. right. apply in_app_iff. right. apply in_app_iff. right. apply Hbase. exact Hb.
+ exact HB5.
+ right. apply in_app_iff. right. apply in_app_iff. right. apply Hbase. exact Hpd.
+ rewrite Hd1. apply ret_ok_even. vm_compute. reflexivity.
+ exact Hd4.
+ rewrite Hd10. f_equal. lia. + rewrite Hd11. f_equal. lia. + exact Hd12.
+ rewrite Hsp. exact Hspm. + rewrite Hsp. lia. + rewrite Hsp. lia. + lia. + rewrite Hsp. lia. + unfold RGBFC_SIZE. lia. + unfold RGBFC_SIZE. lia.
+ exact Hst8. + exact Hcf8. + lia. + lia. + exact Hcur. + exact Hnb.
+ rstack_word HS HU2 36%nat HX36. lia.
+ replace (sp0 - 120 + 8) with (sp0 - 112) by lia. rstack_word HS HU2 37%nat HX37. lia.
+ replace (sp0 - 120 + 16) with (sp0 - 104) by lia. rstack_word HS HU2 38%nat HX38. lia. }
cbv beta. intros c' (L7 & A7 & regs7 & mem7 & md7 & res & cur2 & -> & HJ7 & Hid7 & HP7 & Hr10 & Hres & Hfr7 & Hbb7 & Wp7 & Wn7 & Wc7 & Hcur7 & ALT). clear HJ5.
cbn [ms_regs ms_mem mkst] in HP7, Hfr7, Hbb7, Hr10.
rewrite Hsp in Hfr7. rewrite Hd1.
lazymatch type of HS with st_ok _ ?E1 ?ss1 ?ms1 =>
pose proof (st_ok_after_call ubs2segs 76 E1 ss1 ms1 regs7 mem7
[YQ0b.mkRegion (Some 2%nat) 56 128 56 128 (rsaved_chunks 32)] (ubs2_A_LLVMFuzzerTestOneInput + 0x118) HS eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(apply submem_keep; [| apply submem_nil]; split; [reflexivity|]; split; [cbn; lia|]; split; [cbn; lia|]; split; [cbn; lia|];
apply incl_chunks_sound; vm_compute; reflexivity)
ltac:(vm_compute; reflexivity) HP7) as HS2;
let ss2 := eval vm_compute in (ss_after_call ss1 [YQ0b.mkRegion (Some 2%nat) 56 128 56 128 (rsaved_chunks 32)] 76 (ubs2_A_LLVMFuzzerTestOneInput + 0x118)) in
change (ss_after_call ss1 _ 76 _) with ss2 in HS2 end.
match type of HS2 with ?P -> _ => assert (HK : P); [|specialize (HS2 HK); clear HK] end.
{ constructor; [|constructor].
split; cbn [r_base r_lo r_hi r_wlo r_whi base_val]; ew_havocA; rewrite HU2; intros a Ha.
- apply Hfr7; unfold RGBFC_SIZE; lia.
- intros _. apply (journal_stack_w _ _ _ _ _ _ _ _ _ _ _ _ _ HJ7). lia. }
clear HS. rename HS2 into HS.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ7) as HH7.
assert (Hr_bb : In (r, RGB_SIZE) ((r, RGB_SIZE) :: cgif_blocks g s N ++ optb bef (beffmt * N) ++ rest)) by (left; reflexivity).
assert (Hobj7 : obj_at ubs2segs mem7 r LAY_Rgb [g; wfn; ctx; path; attr; gen; loops; W; H; bef; beffmt; cres]).
{ eapply obj_at_transport_range; [exact Hobj5 | apply lay_inside_Rgb |]. intros i Hi. unfold RGB_SIZE in Hi.
rewrite (Hbb7 r RGB_SIZE i Hr_bb) by (unfold RGB_SIZE; lia). mem_back ltac:(rewrite ?HU2) ltac:(lia). }
assert (Hat7 : cgif_at mem7 g s).
{ eapply (cgif_at_kept _ _ g s N ((r, RGB_SIZE) :: cgif_blocks g s N ++ optb bef (beffmt * N) ++ rest) ((r, RGB_SIZE) :: optb bef (beffmt * N) ++ rest)); [apply Permutation_middle | | exact Hbb7].
eapply (cgif_at_low API); [exact HH5 | | exact Hat5 |]; [eapply Permutation_trans; [exact HB5 | apply Permutation_middle] |].
intros a Ha. mem_back ltac:(rewrite ?HU2) ltac:(lia). }
clear HF HF0 HF1.
destruct ALT as [(-> & HB7) | (Hnz & img' & fmt' & fattr' & fgen' & delay' & Hfc7 & Himg07 & Rimg7 & HB7)].
+
pin_reg HS (10%bv:reg) 0 Hr10.
jrun_to LAWS ubs2tbl_ok HS HJ7 RL_CLOSE.
{ eapply wr_ok_cons_win; [reflexivity | ew_havocA; exact HU2 | cbn [r_wlo r_whi]; intros _; lia |]. apply wr_ok_nil. }
rewrite (st_ok_mkst ubs2segs _ _ _ HS eq_refl). cbn [ss_pc].
lazymatch goal with |- SR _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
eapply (rl_close API IMG (CLOSE fx) L A mem md regs0 rg L7 A7 mm md7 r _ g s N bef (beffmt * N) rest) end.
* exact HFZ. * exact HJ7. * exact Hid7. * exact Hra0. * exact Htp0. * exact Hal16.
* eapply obj_at_transport_range; [exact Hobj7 | apply lay_inside_Rgb |]. intros i Hi. unfold RGB_SIZE in Hi. mem_back ltac:(rewrite ?HU2) ltac:(lia).
* reflexivity. * reflexivity.
* eapply (cgif_at_low API); [exact HH7 | | exact Hat7 |]; [eapply Permutation_trans; [exact HB7 | apply Permutation_middle] |].
intros a Ha. mem_back ltac:(rewrite ?HU2) ltac:(lia).
* exact Hwf. * exact HB7. * exact Hbase.
* exists (pdata, nb). split; [exact Hpd | cbn; lia].
* rsaved_ok_tac HS HU2 HW32 HW33 HW34 HW35.
* reg_nowF HS ltac:(rewrite HU2; f_equal; lia).
* reg_nowF HS ltac:(rewrite HU9; reflexivity).
* runtouched_tac HS HE G3 G4 G19 G20 G21 G22 G23 G24 G25 G26 G27.
+
lazymatch type of HS with st_ok _ ?E1 ?ss1 ?ms1 =>
apply (st_ok_add_fact ubs2segs E1 ss1 ms1 80 (mkAF 1 (2 ^ 64 - 1) 0)) in HS;
[| unfold afact_ok; cbn [af_lo af_hi af_al2 ms_regs mkst];
lazymatch goal with |- context [ew ?Ex 80] =>
replace (ew Ex 80) with (getr regs7 10) by reflexivity end;
rewrite Hr10, unsigned_lit_small by lia; change (2 ^ 0) with 1; rewrite Z.mod_1_r; lia ] end.
lazymatch type of HS with st_ok _ _ ?ss1 _ => let v := eval vm_compute in ss1 in change ss1 with v in HS end.
jrun_to LAWS ubs2tbl_ok HS HJ7 RL_LH.
{ eapply wr_ok_cons_win; [reflexivity | ew_havocA; exact HU2 | cbn [r_wlo r_whi]; intros _; lia |]. apply wr_ok_nil. }
rewrite (st_ok_mkst ubs2segs _ _ _ HS eq_refl). cbn [ss_pc].
lazymatch goal with |- SR _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
eapply (KLH Hk1 fx L A mem md regs0 rg L7 A7 mm md7 r g wfn ctx path attr gen loops W H bef beffmt cres s N rest pdata nb cur2 img' fmt' fattr' fgen' delay') end.
* exact HFZ. * exact HJ7. * exact Hid7. * exact Hra0. * exact Htp0. * exact Hal16. * exact HRO.
* eapply obj_at_transport_range; [exact Hobj7 | apply lay_inside_Rgb |]. intros i Hi. unfold RGB_SIZE in Hi. mem_back ltac:(rewrite ?HU2) ltac:(lia).
* eapply (cgif_at_low API); [exact HH7 | | exact Hat7 |].
{ eapply Permutation_trans; [exact HB7|]. eapply Permutation_trans; [apply perm_ib_back | apply Permutation_middle]. }
intros a Ha. mem_back ltac:(rewrite ?HU2) ltac:(lia).
* exact Hwf. * exact HsW. * exact HsH. * exact HNmax. * exact Hbef.
* eapply Permutation_trans; [exact HB7 | apply perm_ib_back].
* exact Hbase. * exact Hpd. * exact Hnb.
* rsaved_ok_tac HS HU2 HW32 HW33 HW34 HW35.
* intros kk Hkk. fold sp0. cbn [ms_mem mkst] in *. mb_frame_with HF ltac:(lia) ltac:(ew_havocA; rewrite ?HU2; lia). apply Wp7. exact Hkk.
* intros kk Hkk. fold sp0. cbn [ms_mem mkst] in *. mb_frame_with HF ltac:(lia) ltac:(ew_havocA; rewrite ?HU2; lia). replace (sp0 - 112 + Z.of_nat kk) with (sp0 - 120 + 8 + Z.of_nat kk) by lia. apply Wn7. exact Hkk.
* intros kk Hkk. fold sp0. cbn [ms_mem mkst] in *. mb_frame_with HF ltac:(lia) ltac:(ew_havocA; rewrite ?HU2; lia). replace (sp0 - 104 + Z.of_nat kk) with (sp0 - 120 + 16 + Z.of_nat kk) by lia. apply Wc7. exact Hkk.
* lia.
* fold sp0. eapply (obj_at_transport_range _ _ _ _ _ _ 24); [exact Hfc7 | reflexivity |]. intros i Hi. cbn [ms_mem mkst] in *.
mb_frame_with HF ltac:(lia) ltac:(ew_havocA; rewrite ?HU2; lia). reflexivity.
* exact Himg07. * exact Rimg7.
* reg_nowF HS ltac:(rewrite HU2; f_equal; lia).
* reg_nowF HS ltac:(rewrite HU8; reflexivity).
* reg_nowF HS ltac:(rewrite HU9; reflexivity).
* reg_nowF HS ltac:(rewrite HU18; f_equal; lia).
* runtouched_tac HS HE G3 G4 G19 G20 G21 G22 G23 G24 G25 G26 G27.
Qed.
End S.
End c.
Section d. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition ss_rlh : sstate :=
mkSS RL_LH sr_atoms
[ YQ0b.mkRegion (Some 2%nat) 8 128 8 128
([mkChunk 8 (CVal 8 (SOff 36 0)); mkChunk 16 (CVal 8 (SOff 37 0)); mkChunk 24 (CVal 8 (SOff 38 0))]
++ obj_chunks_gen (lay_shift 32 LAY_RgbFrameConfig) 39 [] ++ rsaved_chunks 32) ]
None
(mkFacts [ (2%nat, mkAF (CEIL_MIN + LIB_STACK_RGB - 128) (2^63 - 128) 4);
(8%nat, mkAF 1 RGB_NMAX 0); (9%nat, mkAF 4096 (CEIL_MAX - 64) 4);
(18%nat, mkAF 1 16 0); (36%nat, mkAF 4096 CEIL_MAX 0);
(37%nat, mkAF 1 CEIL_MAX 0); (38%nat, mkAF 0 CEIL_MAX 0); (39%nat, mkAF 0 (2^64 - 1) 0) ] [] []).
Definition ss_rlh_c : sstate := Eval vm_compute in ss_rlh.
Section S2.
Variable API : AllocAPI ubs2_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs2_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs2_msyms MR.
Hypothesis CLOSE : forall fx', rgb_close_spec (fx:=fx') API.
Hypothesis ADDF : forall fx', rgb_addframe_spec (fx:=fx') API.
Lemma rl_head : forall (k : nat), (k <= 15)%nat -> ((1 <= k)%nat -> forall fx', RLH API fx' k) -> RLH API fx (Datatypes.S k).
Proof.
intros k Hk KLH L A mem md regs0 regs1 Lc Ac memc mdc r g wfn ctx path attr gen loops W H bef beffmt cres s N rest
pdata nb cur img fmt fattr fgen delay
HFZ HJ Hid Hra0 Htp0 Hal16 HRO Hobj Hat Hwf HsW HsH HNmax Hbef HB Hbase Hpd Hnb HSV Wp Wn Wc Hcur Hfc Himg0 Himg
G2 G8 G9 G18 HUT.
pose proof HUT as (G3 & G4 & G19 & G20 & G21 & G22 & G23 & G24 & G25 & G26 & G27).
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HLSv : LIB_STACK_RGB = 61440) by reflexivity.
assert (HASv : RGBA_STK = 24576) by reflexivity. assert (HALv : ALLOC_STACK = 8192) by reflexivity.
assert (HNMv : RGB_NMAX = 10000) by reflexivity. assert (HFCv : RGBFC_SIZE = 24) by reflexivity.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HH0.
pose proof HJ as (_ & _ & _ & _ & _ & (Hsp0al & Hstk0 & Hceil & Hsp063 & Hstw) & _ & Hik).
set (sp0 := spZ regs0) in *.
assert (Hspm : (sp0 - 128) mod 16 = 0) by (replace (sp0 - 128) with (sp0 + (-8) * 16) by lia; rewrite Z.mod_add by lia; exact Hal16).
assert (Hcf8 : (sp0 - 96) mod 8 = 0).
{ pose proof (proj2 (Z.div_exact sp0 16 ltac:(lia)) Hal16) as E16. replace (sp0 - 96) with ((2 * (sp0 / 16) - 12) * 8) by lia. apply Z_mod_mult. }
pose proof Hwf as (Hlen3 & HW1 & HH1 & HN & HNle & Hngp & Hih & Hfwf).
assert (Hrin : In (r, RGB_SIZE) (blocks Lc Ac)) by (eapply Permutation_in; [apply Permutation_sym; exact HB | left; reflexivity]).
destruct (heap_blocks_range _ _ LAWS Lc Ac memc mdc r RGB_SIZE HH0 Hrin ltac:(unfold RGB_SIZE; lia)) as (Hr0 & Hr1 & Hr16). unfold RGB_SIZE in Hr1.
assert (Hpdc : In (pdata, nb) (blocks Lc Ac)).
{ eapply Permutation_in; [apply Permutation_sym; exact HB|]. right. apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. right. apply Hbase. exact Hpd. }
destruct (blocks_range _ _ LAWS Lc Ac memc mdc pdata nb HH0 Hpdc) as [Hp0 Hp1].
pose proof (obj_at_range _ _ _ _ _ Hfc) as Rfc.
set (fvals := [img; fmt; fattr; fgen; delay]) in *.
set (E := Ereg regs1 (map (Z_to_bv 64) (rsaved_vals regs0) ++ map (Z_to_bv 64) ([pdata; nb; cur] ++ fvals) ++ [])).
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HSV' : forall j v, nth_error (rsaved_vals regs0) j = Some v -> ew E (32 + j) = Z_to_bv 64 v) by (intros j v Hj; subst E; apply Ereg_vals; exact Hj).
assert (HY : forall j v, nth_error ([pdata; nb; cur] ++ fvals) j = Some v -> ew E (36 + j) = Z_to_bv 64 v).
{ intros j v Hj. subst E. replace (36 + j)%nat with (32 + (length (rsaved_vals regs0) + j))%nat by reflexivity. apply Ereg_vals2. exact Hj. }
assert (HFV : forall j v, nth_error fvals j = Some v -> ew E (39 + j) = Z_to_bv 64 v).
{ intros j v Hj. replace (39 + j)%nat with (36 + (3 + j))%nat by lia. apply HY. exact Hj. }
assert (HW32 : ew E 32 = getr regs0 1) by (etransitivity; [apply (HSV' 0%nat); reflexivity | apply Z_to_bv_bv_unsigned]).
assert (HW33 : ew E 33 = getr regs0 8) by (etransitivity; [apply (HSV' 1%nat); reflexivity | apply Z_to_bv_bv_unsigned]).
assert (HW34 : ew E 34 = getr regs0 9) by (etransitivity; [apply (HSV' 2%nat); reflexivity | apply Z_to_bv_bv_unsigned]).
assert (HW35 : ew E 35 = getr regs0 18) by (etransitivity; [apply (HSV' 3%nat); reflexivity | apply Z_to_bv_bv_unsigned]).
assert (HU2 : bv_unsigned (ew E 2) = sp0 - 128) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; lia).
assert (HU8 : bv_unsigned (ew E 8) = N) by (rewrite (HE 8%nat 8%bv eq_refl), G8; apply unsigned_lit_small; lia).
assert (HU9 : bv_unsigned (ew E 9) = r) by (rewrite (HE 9%nat 9%bv eq_refl), G9; apply unsigned_lit_small; lia).
assert (HU18 : bv_unsigned (ew E 18) = Z.of_nat (Datatypes.S k)) by (rewrite (HE 18%nat 18%bv eq_refl), G18; apply unsigned_lit_small; lia).
assert (HX36 : ew E 36 = Z_to_bv 64 pdata) by (apply (HY 0%nat); reflexivity).
assert (HX37 : ew E 37 = Z_to_bv 64 nb) by (apply (HY 1%nat); reflexivity).
assert (HX38 : ew E 38 = Z_to_bv 64 cur) by (apply (HY 2%nat); reflexivity).
assert (HX39 : ew E 39 = Z_to_bv 64 img) by (apply (HY 3%nat); reflexivity).
pose proof HSV as (W1 & W8 & W9 & W18).
assert (HS : st_ok ubs2segs E ss_rlh_c (mkst regs1 (Z_to_bv 64 RL_LH) memc (seg_rom ubs2segs))).
{ change ss_rlh_c with ss_rlh. unfold ss_rlh. subst E. apply entry_st_ok.
- vm_compute. reflexivity.
- constructor; [|constructor].
unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU2.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply (journal_stack_w _ _ _ _ _ _ _ _ _ _ _ _ _ HJ). lia. }
apply Forall_app; split; [|apply Forall_app; split].
+ apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ pdata); [cbn [sv_denot]; rewrite Z.add_0_r, HX36, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | replace (sp0 - 128 + 8) with (sp0 - 120) by lia; apply val_mem_word_mem; exact Wp]. }
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ nb); [cbn [sv_denot]; rewrite Z.add_0_r, HX37, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | replace (sp0 - 128 + 16) with (sp0 - 112) by lia; apply val_mem_word_mem; exact Wn]. }
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ cur); [cbn [sv_denot]; rewrite Z.add_0_r, HX38, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | replace (sp0 - 128 + 24) with (sp0 - 104) by lia; apply val_mem_word_mem; exact Wc]. }
apply Forall_nil.
+ eapply (obj_chunks_gen_ok ubs2segs _ _ (sp0 - 128) _ fvals 39 []); [| reflexivity | | intros j z Hj; destruct j; discriminate Hj].
* apply (proj1 (obj_at_shift _ _ (sp0 - 128) 32 LAY_RgbFrameConfig fvals)). replace (sp0 - 128 + 32) with (sp0 - 96) by lia. exact Hfc.
* intros j v Hj. apply (HFV j v Hj).
+ assert (CK : forall off j (w : Z), nth_error (rsaved_vals regs0) j = Some w -> word_mem ubs2segs memc (sp0 - 128 + off) w -> 0 <= w < 2 ^ 64 ->
chunk_ok ubs2segs (Ereg regs1 (map (Z_to_bv 64) (rsaved_vals regs0) ++ map (Z_to_bv 64) ([pdata; nb; cur] ++ fvals) ++ [])) memc (sp0 - 128) (mkChunk off (CVal 8 (SOff (32 + j) 0)))).
{ intros off j w Hj Wm Rw. eapply (chunk_ok_val _ _ _ _ _ _ _ w); [| cbn; lia | cbn; lia | apply val_mem_word_mem; exact Wm].
cbn [sv_denot]. rewrite Z.add_0_r, (HSV' j w Hj), Z_to_bv_bv_unsigned. reflexivity. }
assert (RU : forall w : word, 0 <= bv_unsigned w < 2 ^ 64).
{ intros w. pose proof (bv_unsigned_in_range 64 w) as Rw. change (bv_modulus 64) with (2 ^ 64) in Rw. lia. }
unfold rsaved_chunks. cbn [Nat.add].
repeat (apply Forall_cons;
[ first [ apply (CK 120 0%nat _ eq_refl); [replace (sp0 - 128 + 120) with (sp0 - 8) by lia; exact W1 | apply RU]
| apply (CK 112 1%nat _ eq_refl); [replace (sp0 - 128 + 112) with (sp0 - 16) by lia; exact W8 | apply RU]
| apply (CK 104 2%nat _ eq_refl); [replace (sp0 - 128 + 104) with (sp0 - 24) by lia; exact W9 | apply RU]
| apply (CK 96 3%nat _ eq_refl); [replace (sp0 - 128 + 96) with (sp0 - 32) by lia; exact W18 | apply RU] ] | ]).
apply Forall_nil.
- cbn [pairwise_disjoint all_disjoint]. repeat split.
- cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HU2, HU8, HU9, HU18, HX36, HX37, HX38, HX39, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
repeat split; try lia; assumption. }
change memc with (ms_mem (mkst regs1 (Z_to_bv 64 RL_LH) memc (seg_rom ubs2segs))) in HJ.
jrun_to LAWS ubs2tbl_ok HS HJ ubs2_A_cgif_rgb_addframe.
{ eapply wr_ok_cons_win; [reflexivity | exact HU2 | cbn [r_wlo r_whi]; intros _; lia |]. apply wr_ok_nil. }
jreg HS (10%bv:reg) as Ha10. rewrite (HE 9%nat 9%bv eq_refl), G9 in Ha10.
jreg HS (11%bv:reg) as Ha11. rewrite HU2 in Ha11.
jreg HS (2%bv:reg) as Ha2. rewrite (HE 2%nat 2%bv eq_refl), G2 in Ha2.
jreg HS (4%bv:reg) as Ha4. rewrite (HE 4%nat 4%bv eq_refl), G4, Htp0 in Ha4.
jreg HS (1%bv:reg) as Ha1.
eapply SR_bind.
{ eapply (jcall_tmpF _ _ LAWS) with (STK1 := RGBA_STK) (FP1 := (r, r + RGB_SIZE) :: blocks_fp (cgif_blocks g s N) ++ optfp bef (beffmt * N))
(K := fun fx4 L4 A4 (regs4 : bvmap 5 word) (mem4 : word -> option byte) (md4 : Model) =>
frm_zero (@fp_csr fx4) /\ st_init_done A4 = true /\
exists (s' : cgif_st) (bef' beffmt' cres' : Z),
obj_at ubs2segs mem4 r LAY_Rgb [g; wfn; ctx; path; attr; gen; loops; W; H; bef'; beffmt'; cres'] /\
cgif_at mem4 g s' /\ cgif_wf s' N /\ cg_W s' = W /\ cg_H s' = H /\ (bef' = 0 \/ beffmt' = 3 \/ beffmt' = 4) /\
Permutation (blocks L4 A4) ((r, RGB_SIZE) :: cgif_blocks g s' N ++ optb bef' (beffmt' * N) ++ img_block img fmt N ++ rest));
[ exact HS | reflexivity | exact HJ | exact Ha1 | | apply ret_ok_even; vm_compute; reflexivity
| unfold spZ; rewrite Ha2, unsigned_lit_small by lia; exact Hspm | lia
| unfold spZ; rewrite Ha2, unsigned_lit_small by lia; lia
| unfold spZ; rewrite Ha2, unsigned_lit_small by lia; lia | exact Ha4 | ].
- intros HPRE1. eapply SR_mono.
{ eapply (ADDF fx _ _ _ _ _ r (sp0 - 96) g wfn ctx path attr gen loops W H bef beffmt cres s N img fmt fattr fgen delay rest HPRE1 Hid HFZ Ha10);
[ rewrite Ha11; f_equal; lia | exact Hcf8 | unfold spZ; rewrite Ha2, unsigned_lit_small by lia; lia | lia | | | | exact Hwf | exact HsW | exact HsH | exact HNmax | exact Hbef | | exact HB ].
+ apply (proj2 (obj_at_shift _ _ (sp0 - 128) 32 LAY_RgbFrameConfig fvals)) || (replace (sp0 - 96) with (sp0 - 128 + 32) by lia; apply (proj1 (iff_sym (obj_at_shift _ _ (sp0 - 128) 32 LAY_RgbFrameConfig fvals)))).
eapply (st_obj_at ubs2segs _ _ _ 0%nat _ 2%nat (sp0 - 128) _ fvals 39 [] HS eq_refl eq_refl HU2);
[ apply incl_chunks_sound; vm_compute; reflexivity | reflexivity | reflexivity | ].
intros j v Hj. split; [rewrite nth_lay_shift_snd; exact (Rfc j v Hj)|].
replace (nth_error (@nil (option Z)) j) with (@None (option Z)) by (destruct j; reflexivity). exact (HFV j v Hj).
+ eapply obj_at_transport_range; [exact Hobj | apply lay_inside_Rgb |]. intros i Hi. unfold RGB_SIZE in Hi. mem_back ltac:(rewrite ?HU2) ltac:(lia).
+ eapply (cgif_at_low API); [exact HH0 | | exact Hat |]; [eapply Permutation_trans; [exact HB | apply Permutation_middle] |].
intros a Ha. mem_back ltac:(rewrite ?HU2) ltac:(lia).
+ intros a Ha. rewrite <- (ubs2_rgb_rodata_kept MR mem _ HRO Hik a Ha). unfold SRC2_RO_LO, SRC2_RO_HI in Ha.
mem_back ltac:(rewrite ?HU2) ltac:(lia). }
cbv beta. intros c' (fx4 & L4 & A4 & regs4 & mem4 & md4 & s' & bef' & beffmt' & cres' & -> & HFZ4 & HJc4 & HP4 & Hid4 & Hobj4 & Hat4 & Hwf4 & HW4 & HH4 & _ & _ & Hbef4 & HB4).
exists fx4, L4, A4, regs4, mem4, md4. split; [rewrite Ha1; reflexivity|]. split; [exact HJc4|]. split; [exact HP4|].
split; [exact HFZ4|]. split; [exact Hid4|]. exists s', bef', beffmt', cres'.
split; [exact Hobj4|]. split; [exact Hat4|]. split; [exact Hwf4|]. split; [exact HW4|]. split; [exact HH4|]. split; [exact Hbef4 | exact HB4].
- intros a Ha. right. rewrite rgb_fp_eq in Ha. eapply (tmp_blocks_fp API); [exact HH0 | | | exact Ha].
+ eapply Permutation_trans; [exact HB|]. cbn [app]. apply perm_skip. rewrite app_assoc. apply Permutation_refl.
+ intros b Hb. apply in_app_iff. right. apply Hbase. exact Hb. }
cbv beta. intros c' (fx4 & L4 & A4 & regs4 & mem4 & md4 & -> & HJ4 & HJc4 & HP4 & HFZ4 & Hid4 & s' & bef' & beffmt' & cres' & Hobj4 & Hat4 & Hwf4 & HW4 & HH4 & Hbef4 & HB4). clear HJ.
cbn [ms_regs ms_mem mkst] in HJc4, HP4, Hat4, HJ4, Hobj4.
pose proof HJc4 as (_ & _ & Hhi4 & _).
jafter_call_keep HS 44%nat regs4 mem4 HP4 [0%nat] HS2.
match type of HS2 with ?P -> _ => assert (HK : P); [|specialize (HS2 HK); clear HK] end.
{ constructor; [|constructor].
eapply (region_kept_stack ubs2segs _ _ _ 2); [exact HU2 | exact Hhi4 | lia | lia | unfold spZ; rewrite Ha2, unsigned_lit_small by lia; lia | cbn; lia | cbn; lia]. }
clear HS. rename HS2 into HS.
apply (rl_after (fx:=fx4) API IMG CLOSE k KLH L A mem md regs0 regs4 L4 A4 mem4 md4 r g wfn ctx path attr gen loops W H bef' beffmt' cres' s' N rest
pdata nb cur img fmt fattr fgen delay Hk HFZ4 HJ4 Hid4 Hra0 Htp0 Hal16 HRO Hobj4 Hat4 Hwf4 HW4 HH4 HNmax Hbef4 HB4 Hbase Hpd Hnb).
- rsaved_ok_tac HS HU2 HW32 HW33 HW34 HW35.
- rstack_word HS HU2 36%nat HX36. lia.
- rstack_word HS HU2 37%nat HX37. lia.
- rstack_word HS HU2 38%nat HX38. lia.
- exact Hcur.
- fold sp0. fold fvals. replace (sp0 - 96) with (sp0 - 128 + 32) by lia. apply (proj2 (obj_at_shift _ _ (sp0 - 128) 32 LAY_RgbFrameConfig fvals)).
cbn [ms_mem mkst] in HS.
eapply (st_obj_at ubs2segs _ _ _ 0%nat _ 2%nat (sp0 - 128) _ fvals 39 [] HS eq_refl eq_refl ltac:(ew_havocA; exact HU2));
[ apply incl_chunks_sound; vm_compute; reflexivity | reflexivity | reflexivity | ].
intros j v Hj. split; [rewrite nth_lay_shift_snd; exact (Rfc j v Hj)|].
replace (nth_error (@nil (option Z)) j) with (@None (option Z)) by (destruct j; reflexivity).
rewrite ew_havoc_old; [exact (HFV j v Hj) |].
destruct (Nat.lt_ge_cases j 5) as [Hl|Hl]; [lia|]. rewrite (proj2 (nth_error_None fvals j)) in Hj; [discriminate Hj | subst fvals; cbn; lia].
- exact Himg0.
- exact Himg.
- reg_nowR HS ltac:(rewrite HU2; reflexivity).
- reg_nowR HS ltac:(rewrite HU8; reflexivity).
- reg_nowR HS ltac:(rewrite HU9; reflexivity).
- reg_nowR HS ltac:(rewrite HU18; reflexivity).
- runtouched_tacR HS HE G3 G4 G19 G20 G21 G22 G23 G24 G25 G26 G27.
Qed.
End S2.
End d.
Section e. Context {rc : YN05.RunCeil}.
Lemma rl_loop : forall (API : AllocAPI ubs2_msyms),
img_laws ubs2_msyms (aa_MR API) -> (forall fx', rgb_close_spec (fx:=fx') API) -> (forall fx', rgb_addframe_spec (fx:=fx') API) ->
forall (k : nat), (1 <= k <= 16)%nat -> forall fx', RLH API fx' k.
Proof.
intros API IMG CLOSE ADDF. induction k as [|k IH]; intros Hk fx'; [lia|].
apply (rl_head (fx:=fx') API IMG CLOSE ADDF k); [lia|]. intros Hk1 fx''. apply IH. lia.
Qed.
End e.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
