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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0i YO0f YO0x YO0d YO0e.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UH00 UH03 UH02 UN3b YI06 UI5b YI09 YI08 YI0r
UI1w UI4l UI21 UI5o UI5l YI6b YL0g YI0o
YI16 YI17 YI14 YI18 YI1a UI5c YI00 UI3u UI22 UI2u UI0l
YI5a UI23 YI0a YL00 YI05 UI5n.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO03 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YO07.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UI5f UI5e.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition ss_lh : sstate :=
mkSS L_LH sr_atoms
[ YP09.mkRegion (Some 2%nat) 8 144 8 144
([mkChunk 8 (CVal 8 (SOff 36 0)); mkChunk 16 (CVal 8 (SOff 37 0)); mkChunk 24 (CVal 8 (SOff 38 0))]
++ obj_chunks_gen (lay_shift 32 LAY_FrameConfig) 39 [] ++ saved_chunks 32) ]
None
(mkFacts [ (2%nat, mkAF (CEIL_MIN + LIB_STACK - 144) (2^63 - 144) 4);
(8%nat, mkAF 1 100000000 0); (9%nat, mkAF 4096 (CEIL_MAX - 96) 4);
(18%nat, mkAF 1 16 0); (36%nat, mkAF 4096 CEIL_MAX 0);
(37%nat, mkAF 1 CEIL_MAX 0); (38%nat, mkAF 0 CEIL_MAX 0) ] [] []).
Definition ss_lh_c : sstate := Eval vm_compute in ss_lh.
Lemma nth_lay_shift_snd : forall d lay j, snd (nth j (lay_shift d lay) (0, 8%N)) = snd (nth j lay (0, 8%N)).
Proof using. intros d lay. induction lay as [|f lay IH]; intros [|j]; cbn; try reflexivity. apply IH. Qed.
Lemma u64_range' : forall w : word, 0 <= bv_unsigned w < 2 ^ 64.
Proof using. intros w. pose proof (bv_unsigned_in_range 64 w) as H. change (bv_modulus 64) with (2 ^ 64) in H. lia. Qed.
End c.
Section e. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section S.
Variable API : AllocAPI ubs0_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs0_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs0_msyms MR.
Hypothesis CLOSE : close_specX API.
Hypothesis ADDF : addframe_specX API.
Hypothesis UNLINK : unlink_x ubs0_msyms MR ubs0_A_unlink.
Hypothesis RFC : rfc_specX API.
Variables (regs0 : bvmap 5 word) (L : layout) (A : astate) (mem : word -> option byte) (md : Model) (b0 : rbound) (plen : Z) (K : lleaf -> TSet).
Hypothesis HSORT : Fs.fs_sorted (m_fs md) = true.
Hypothesis HK : forall fs' c', leaf_post API regs0 L A mem md (ff_delta plen b0) fs' c' -> realizes ubs0segs c' (K (LL 0 fs' [])).
Hypothesis HROOM : ff_room b0 plen.
Lemma llvm_loop_x : forall (k : nat),
forall (regs1 : bvmap 5 word) Lc Ac memc mdc (g : Z) (s : cgif_st) (N : Z) (rest : list (Z * Z))
(pdata nb cur lpal lpa img fattr fgen delay nlp tidx : Z)
(PAYLOAD GPAL IMGV LPALV : list Z) (G : YO07.gcfg) (gs : YO07.gif_st) (bc : rbound),
(1 <= k <= 16)%nat ->
journal ubs0_msyms MR LIB_STACK (spZ regs0) [sink_token] L A mem md Lc Ac memc mdc -> st_init_done Ac = true ->
YK0s.ret_ok (getr regs0 1) -> getr regs0 4 = Z_to_bv 64 (ms_tp ubs0_msyms) -> spZ regs0 mod 16 = 0 -> spZ regs0 <= 2 ^ 47 ->
cgif_at memc g s -> cgif_wf s N ->
Permutation (blocks Lc Ac) (cgif_blocks g s N ++ (img, N) :: (if Z.land fattr 1 =? 0 then [] else [(lpa, 3 * nlp)]) ++ rest) ->
(forall b, In b (blocks L A) -> In b rest) -> In (pdata, nb) (blocks L A) -> 0 < nb ->
saved_ok memc (spZ regs0) regs0 ->
word_mem ubs0segs memc (spZ regs0 - 136) pdata -> word_mem ubs0segs memc (spZ regs0 - 128) nb ->
word_mem ubs0segs memc (spZ regs0 - 120) cur -> 0 <= cur <= nb ->
obj_at ubs0segs memc (spZ regs0 - 112) LAY_FrameConfig [lpal; img; fattr; fgen; delay; nlp; tidx] ->
(Z.land fattr 1 = 0 -> lpal = 0) -> Z_to_bv 64 lpa = Z_to_bv 64 lpal ->
getr regs1 2 = Z_to_bv 64 (spZ regs0 - 144) -> getr regs1 8 = Z_to_bv 64 N -> getr regs1 9 = Z_to_bv 64 g ->
getr regs1 18 = Z_to_bv 64 (Z.of_nat k) -> untouched_ok regs0 regs1 ->
garr8 ubs0segs mem pdata PAYLOAD -> Z.of_nat (length PAYLOAD) = nb ->
cgif_rel memc mdc s N GPAL gs ->
Z.of_nat (length (concat (YO07.s_out gs))) <= HDR_OUT + (17 - Z.of_nat k) * FRAME_OUT N ->
gcfg_of s GPAL = G ->
garr8 ubs0segs memc img IMGV -> Z.of_nat (length IMGV) = N ->
(Z.land fattr 1 <> 0 -> garr8 ubs0segs memc lpa LPALV /\ Z.of_nat (length LPALV) = 3 * nlp) ->
res_ok Ac bc -> rb_le bc (loop_bud b0 N (Z.of_nat k) (qcount gs)) ->
realizes ubs0segs (mkCfg (mkst regs1 (Z_to_bv 64 L_LH) memc (seg_rom ubs0segs)) mdc)
(ff_unl K (Fs.fs_set (m_fs md) sink_path
(bytes (loop_file G (Nat.pred k) (YO07.add_frame G gs fattr fgen delay tidx nlp LPALV IMGV) (skipn (Z.to_nat cur) PAYLOAD))))).
Proof using ADDF CLOSE HK HROOM HSORT IMG LAWS RFC UNLINK.
induction k as [|k IH]; [lia|].
intros regs1 Lc Ac memc mdc g s N rest pdata nb cur lpal lpa img fattr fgen delay nlp tidx PAYLOAD GPAL IMGV LPALV G gs bc
Hk HJ Hid Hra0 Htp0 Hal16 Hsp47 Hat Hwf HB Hbase Hpd Hnb HSV Wp Wn Wc Hcur Hfc Hlp0 Hlpa G2 G8 G9 G18 HUT
HPL HPLn HREL HLEN HG HIMG HIMGn HLP HRES HBLE.
cbn [Nat.pred]. apply realizes_via_SR.
pose proof (qcount_range gs) as HQ.
pose proof HUT as (G3 & G4 & G19 & G20 & G21 & G22 & G23 & G24 & G25 & G26 & G27).
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HLSv : LIB_STACK = 16384) by reflexivity.
assert (HASv : ADDFRAME_STK = 9728) by reflexivity. assert (HRSv : RFC_STK = 8272) by reflexivity. assert (HALv : ALLOC_STACK = 8192) by reflexivity.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HH0.
pose proof HJ as (_ & _ & _ & _ & _ & (Hsp0al & Hstk0 & Hceil & Hsp063 & Hstw) & _).
set (sp0 := spZ regs0) in *.
assert (Hspm : (sp0 - 144) mod 16 = 0) by (replace (sp0 - 144) with (sp0 + (-9) * 16) by lia; rewrite Z.mod_add by lia; exact Hal16).
assert (Hcf8 : (sp0 - 112) mod 8 = 0).
{ pose proof (proj2 (Z.div_exact sp0 16 ltac:(lia)) Hal16) as E16. replace (sp0 - 112) with ((2 * (sp0 / 16) - 14) * 8) by lia. apply Z_mod_mult. }
pose proof Hwf as (Hlen3 & HW1 & HH1 & HN & HNle & Hngp & Hih & Hfwf).
assert (HN1 : 1 <= N) by (clear - HN HW1 HH1; nia). assert (HNr : 1 <= N <= 100000000) by (clear - HN1 HNle; lia).
assert (Hkz : 1 <= Z.of_nat (Datatypes.S k) <= 16) by (clear - Hk; lia).
assert (HFO : 0 <= (17 - Z.of_nat (Datatypes.S k)) * FRAME_OUT N <= 16 * FRAME_OUT N).
{ clear - Hk HN1. unfold FRAME_OUT. split; [apply Z.mul_nonneg_nonneg; lia | apply Z.mul_le_mono_nonneg_r; lia]. }
assert (Hgin : In (g, CGIF_SIZE) (blocks Lc Ac)) by (eapply Permutation_in; [apply Permutation_sym; exact HB | left; reflexivity]).
destruct (blocks_range _ _ LAWS Lc Ac memc mdc g CGIF_SIZE HH0 Hgin) as [Hg0 Hg1]. unfold CGIF_SIZE in Hg1.
assert (Hpdc : In (pdata, nb) (blocks Lc Ac)).
{ eapply Permutation_in; [apply Permutation_sym; exact HB|]. apply in_app_iff. right. right. apply in_app_iff. right. apply Hbase. exact Hpd. }
destruct (blocks_range _ _ LAWS Lc Ac memc mdc pdata nb HH0 Hpdc) as [Hp0 Hp1].
pose proof (obj_at_range _ _ _ _ _ Hfc) as Rfc.
set (fvals := [lpal; img; fattr; fgen; delay; nlp; tidx]) in *.
set (E := Ereg regs1 (map (Z_to_bv 64) (saved_vals regs0) ++ map (Z_to_bv 64) ([pdata; nb; cur] ++ fvals) ++ [])).
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HSV' : forall j v, nth_error (saved_vals regs0) j = Some v -> ew E (32 + j) = Z_to_bv 64 v) by (intros j v Hj; subst E; apply Ereg_vals; exact Hj).
assert (HY : forall j v, nth_error ([pdata; nb; cur] ++ fvals) j = Some v -> ew E (36 + j) = Z_to_bv 64 v).
{ intros j v Hj. subst E. replace (36 + j)%nat with (32 + (length (saved_vals regs0) + j))%nat by reflexivity. apply Ereg_vals2. exact Hj. }
assert (HFV : forall j v, nth_error fvals j = Some v -> ew E (39 + j) = Z_to_bv 64 v).
{ intros j v Hj. replace (39 + j)%nat with (36 + (3 + j))%nat by lia. apply HY. exact Hj. }
assert (HW32 : ew E 32 = getr regs0 1) by (etransitivity; [apply (HSV' 0%nat); reflexivity | apply Z_to_bv_bv_unsigned]).
assert (HW33 : ew E 33 = getr regs0 8) by (etransitivity; [apply (HSV' 1%nat); reflexivity | apply Z_to_bv_bv_unsigned]).
assert (HW34 : ew E 34 = getr regs0 9) by (etransitivity; [apply (HSV' 2%nat); reflexivity | apply Z_to_bv_bv_unsigned]).
assert (HW35 : ew E 35 = getr regs0 18) by (etransitivity; [apply (HSV' 3%nat); reflexivity | apply Z_to_bv_bv_unsigned]).
assert (HU2 : bv_unsigned (ew E 2) = sp0 - 144) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; lia).
assert (HU8 : bv_unsigned (ew E 8) = N) by (rewrite (HE 8%nat 8%bv eq_refl), G8; apply unsigned_lit_small; lia).
assert (HU9 : bv_unsigned (ew E 9) = g) by (rewrite (HE 9%nat 9%bv eq_refl), G9; apply unsigned_lit_small; lia).
assert (HU18 : bv_unsigned (ew E 18) = Z.of_nat (Datatypes.S k)) by (rewrite (HE 18%nat 18%bv eq_refl), G18; apply unsigned_lit_small; lia).
assert (HX36 : ew E 36 = Z_to_bv 64 pdata) by (apply (HY 0%nat); reflexivity).
assert (HX37 : ew E 37 = Z_to_bv 64 nb) by (apply (HY 1%nat); reflexivity).
assert (HX38 : ew E 38 = Z_to_bv 64 cur) by (apply (HY 2%nat); reflexivity).
assert (HX39 : ew E 39 = Z_to_bv 64 lpal) by (apply (HY 3%nat); reflexivity).
assert (HX40 : ew E 40 = Z_to_bv 64 img) by (apply (HY 4%nat); reflexivity).
pose proof HSV as (W1 & W8 & W9 & W18).
assert (HS : st_ok ubs0segs E ss_lh_c (mkst regs1 (Z_to_bv 64 L_LH) memc (seg_rom ubs0segs))).
{ change ss_lh_c with ss_lh. unfold ss_lh. subst E. apply entry_st_ok.
- vm_compute. reflexivity.
- constructor; [|constructor].
unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU2.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply (journal_stack_w _ _ _ _ _ _ _ _ _ _ _ _ _ HJ). lia. }
apply Forall_app; split; [|apply Forall_app; split].
+ apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ pdata); [cbn [sv_denot]; rewrite Z.add_0_r, HX36, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | replace (sp0 - 144 + 8) with (sp0 - 136) by lia; apply val_mem_word_mem; exact Wp]. }
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ nb); [cbn [sv_denot]; rewrite Z.add_0_r, HX37, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | replace (sp0 - 144 + 16) with (sp0 - 128) by lia; apply val_mem_word_mem; exact Wn]. }
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ cur); [cbn [sv_denot]; rewrite Z.add_0_r, HX38, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | replace (sp0 - 144 + 24) with (sp0 - 120) by lia; apply val_mem_word_mem; exact Wc]. }
apply Forall_nil.
+ eapply (obj_chunks_gen_ok ubs0segs _ _ (sp0 - 144) _ fvals 39 []); [| reflexivity | | intros j z Hj; destruct j; discriminate Hj].
* apply (proj1 (obj_at_shift _ _ (sp0 - 144) 32 LAY_FrameConfig fvals)). replace (sp0 - 144 + 32) with (sp0 - 112) by lia. exact Hfc.
* intros j v Hj. apply (HFV j v Hj).
+ assert (CK : forall off j (w : Z), nth_error (saved_vals regs0) j = Some w -> word_mem ubs0segs memc (sp0 - 144 + off) w -> 0 <= w < 2 ^ 64 ->
chunk_ok ubs0segs (Ereg regs1 (map (Z_to_bv 64) (saved_vals regs0) ++ map (Z_to_bv 64) ([pdata; nb; cur] ++ fvals) ++ [])) memc (sp0 - 144) (mkChunk off (CVal 8 (SOff (32 + j) 0)))).
{ intros off j w Hj Wm Rw. eapply (chunk_ok_val _ _ _ _ _ _ _ w); [| cbn; lia | cbn; lia | apply val_mem_word_mem; exact Wm].
cbn [sv_denot]. rewrite Z.add_0_r, (HSV' j w Hj), Z_to_bv_bv_unsigned. reflexivity. }
assert (RU : forall w : word, 0 <= bv_unsigned w < 2 ^ 64).
{ intros w. pose proof (bv_unsigned_in_range 64 w) as Rw. change (bv_modulus 64) with (2 ^ 64) in Rw. lia. }
unfold saved_chunks. cbn [Nat.add].
repeat (apply Forall_cons;
[ first [ apply (CK 136 0%nat _ eq_refl); [replace (sp0 - 144 + 136) with (sp0 - 8) by lia; exact W1 | apply RU]
| apply (CK 128 1%nat _ eq_refl); [replace (sp0 - 144 + 128) with (sp0 - 16) by lia; exact W8 | apply RU]
| apply (CK 120 2%nat _ eq_refl); [replace (sp0 - 144 + 120) with (sp0 - 24) by lia; exact W9 | apply RU]
| apply (CK 112 3%nat _ eq_refl); [replace (sp0 - 144 + 112) with (sp0 - 32) by lia; exact W18 | apply RU] ] | ]).
apply Forall_nil.
- cbn [pairwise_disjoint all_disjoint]. repeat split.
- cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HU2, HU8, HU9, HU18, HX36, HX37, HX38, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
destruct (heap_blocks_range _ _ LAWS Lc Ac memc mdc g CGIF_SIZE HH0 Hgin ltac:(unfold CGIF_SIZE; lia)) as (_ & _ & Hg16).
repeat split; try lia; assumption. }
change memc with (ms_mem (mkst regs1 (Z_to_bv 64 L_LH) memc (seg_rom ubs0segs))) in HJ.
assert (Himgc : In (img, N) (blocks Lc Ac)) by (eapply Permutation_in; [apply Permutation_sym; exact HB|]; apply in_app_iff; right; left; reflexivity).
assert (Himgfresh : ~ In (img, N) (blocks L A)).
{ intros H0. apply Hbase in H0.
assert (HP' : Permutation (blocks Lc Ac) ((img, N) :: cgif_blocks g s N ++ (if Z.land fattr 1 =? 0 then [] else [(lpa, 3 * nlp)]) ++ rest)).
{ eapply Permutation_trans; [exact HB|]. apply Permutation_sym. apply Permutation_middle. }
destruct (heap_sep_perm _ _ LAWS Lc Ac memc mdc (img, N) _ (img, N) HH0 HP' ltac:(apply in_app_iff; right; apply in_app_iff; right; exact H0)) as [H1|H1]; cbn [fst snd] in H1; lia. }
destruct (blocks_range _ _ LAWS Lc Ac memc mdc img N HH0 Himgc) as [Hi0 Hi1].
assert (Hlpr : Z.land fattr 1 <> 0 -> 4096 <= lpa /\ lpa + 3 * nlp <= alloc_ceiling).
{ intros Hf1. eapply (blocks_range _ _ LAWS); [exact HH0|]. eapply Permutation_in; [apply Permutation_sym; exact HB|].
apply in_app_iff. right. right. destruct (Z.eqb_spec (Z.land fattr 1) 0) as [E0|E0]; [exfalso; exact (Hf1 E0)|]. left. reflexivity. }
jrun_to LAWS ubs0tbl_ok HS HJ ubs0_A_cgif_addframe.
{ eapply wr_ok_cons_win; [reflexivity | exact HU2 | cbn [r_wlo r_whi]; intros _; lia |]. apply wr_ok_nil. }
jreg HS (10%bv:reg) as Ha10. rewrite (HE 9%nat 9%bv eq_refl), G9 in Ha10.
jreg HS (11%bv:reg) as Ha11. rewrite HU2 in Ha11.
jreg HS (2%bv:reg) as Ha2. rewrite (HE 2%nat 2%bv eq_refl), G2 in Ha2.
jreg HS (4%bv:reg) as Ha4. rewrite (HE 4%nat 4%bv eq_refl), G4, Htp0 in Ha4.
jreg HS (1%bv:reg) as Ha1.
eapply SR_bind.
{ eapply (jcall_tmp _ _ LAWS) with (STK1 := ADDFRAME_STK) (FP1 := cgif_fp g s N)
(K := fun L4 A4 (regs4 : bvmap 5 word) (mem4 : word -> option byte) (md4 : Model) =>
st_init_done A4 = true /\ exists s' gs', cgif_at mem4 g s' /\ cgif_wf s' N /\ gcfg_of s' GPAL = gcfg_of s GPAL /\
Permutation (blocks L4 A4) (cgif_blocks g s' N ++ (img, N) :: (if Z.land fattr 1 =? 0 then [] else [(lpa, 3 * nlp)]) ++ rest) /\
cgif_rel mem4 md4 s' N GPAL gs' /\
Z.of_nat (length (concat (YO07.s_out gs'))) <= Z.of_nat (length (concat (YO07.s_out gs))) + FRAME_OUT N /\
gs' = YO07.add_frame (gcfg_of s GPAL) gs fattr fgen delay tidx nlp LPALV IMGV /\
res_ok A4 (af_rb bc N (qcount gs) (qcount gs')));
[ exact HS | reflexivity | exact HJ | exact Ha1 | | apply ret_ok_even; vm_compute; reflexivity
| unfold spZ; rewrite Ha2, unsigned_lit_small by lia; exact Hspm | lia
| unfold spZ; rewrite Ha2, unsigned_lit_small by lia; lia
| unfold spZ; rewrite Ha2, unsigned_lit_small by lia; lia | exact Ha4 | ].
- intros HPRE1. eapply SR_mono.
{ eapply (ADDF _ _ _ _ _ g (sp0 - 112) s N lpal lpa img fattr fgen delay nlp tidx rest GPAL IMGV LPALV gs bc HPRE1 Hid);
[ clear - HLEN HFO HN1 HNle; unfold HDR_OUT, FRAME_OUT, SINK_MAX in *; lia
| unfold spZ; rewrite Ha2, unsigned_lit_small by lia; lia
| exact Ha10 | rewrite Ha11; f_equal; lia | exact Hcf8 | unfold spZ; rewrite Ha2, unsigned_lit_small by lia; lia | lia | | | exact Hwf | exact Hlpa | exact HB
| | | exact HIMGn | | exact HRES | exact (loop_af_room b0 plen N HROOM HNr bc _ _ Hkz HQ HBLE) ].
+ replace (sp0 - 112) with (sp0 - 144 + 32) by lia. apply (proj2 (obj_at_shift _ _ (sp0 - 144) 32 LAY_FrameConfig fvals)).
eapply (st_obj_at ubs0segs _ _ _ 0%nat _ 2%nat (sp0 - 144) _ fvals 39 [] HS eq_refl eq_refl HU2);
[ apply incl_chunks_sound; vm_compute; reflexivity | reflexivity | reflexivity | ].
intros j v Hj. split; [rewrite nth_lay_shift_snd; exact (Rfc j v Hj)|].
replace (nth_error (@nil (option Z)) j) with (@None (option Z)) by (destruct j; reflexivity). exact (HFV j v Hj).
+ eapply (cgif_at_low API); [exact HH0 | | exact Hat |]; [eapply Permutation_trans; [exact HB|]; apply Permutation_refl |].
intros a Ha. mem_back ltac:(rewrite ?HU2) ltac:(lia).
+ eapply (cgif_rel_low API); [exact HH0 | exact HB | exact HREL |]. intros a Ha. mem_back ltac:(rewrite ?HU2) ltac:(lia).
+ eapply garr8_frame; [exact HIMG|]. intros a Ha. rewrite HIMGn in Ha. mem_back ltac:(rewrite ?HU2) ltac:(lia).
+ intros Hf1. destruct (HLP Hf1) as [HG1 HL1]. destruct (Hlpr Hf1) as [Hl0 Hl1]. split; [|exact HL1].
eapply garr8_frame; [exact HG1|]. intros a Ha. rewrite HL1 in Ha. mem_back ltac:(rewrite ?HU2) ltac:(lia). }
cbv beta. intros c' (L4 & A4 & regs4 & mem4 & md4 & s' & -> & HJc4 & HP4 & Hid4 & Hat4 & Hwf4 & HW4 & HH4' & Hattr4 & _ & _ & HB4 & Hgen4 & Hngp4 & _ & HREL4 & HLEN4 & HR4).
exists L4, A4, regs4, mem4, md4. split; [rewrite Ha1; reflexivity|]. split; [exact HJc4|]. split; [exact HP4|].
split; [exact Hid4|]. exists s', (YO07.add_frame (gcfg_of s GPAL) gs fattr fgen delay tidx nlp LPALV IMGV). split; [exact Hat4|]. split; [exact Hwf4|].
split; [unfold gcfg_of; rewrite HW4, HH4', Hattr4, Hgen4, Hngp4; reflexivity|].
split; [exact HB4|]. split; [exact HREL4|]. split; [exact HLEN4|]. split; [reflexivity | exact HR4].
- intros a (r & [<- | Hr] & Ha).
+ left. split; [exists sink_token; split; [left; reflexivity | exact Ha]|]. cbn in Ha. lia.
+ right. eapply (tmp_blocks_fp API); [exact HH0 | exact HB | | exists r; split; [exact Hr | exact Ha]].
intros b Hb. right. apply in_app_iff. right. apply Hbase. exact Hb. }
cbv beta. intros c' (L4 & A4 & regs4 & mem4 & md4 & -> & HJ4 & HJc4 & HP4 & Hid4 & s' & gs' & Hat4 & Hwf4 & HG4 & HB4 & HREL4 & HLEN4 & HSTEP4 & HR4). clear HJ.
rewrite HG in HSTEP4. rewrite HG in HG4. rewrite <- HSTEP4. pose proof (qcount_range gs') as HQ'.
cbn [ms_regs ms_mem mkst] in HJc4, HP4, Hat4, HJ4.
pose proof HJc4 as (_ & _ & Hhi4 & _).
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ4) as HH4.
jafter_call_keep HS 52%nat regs4 mem4 HP4 [0%nat] HS2.
match type of HS2 with ?P -> _ => assert (HK2 : P); [|specialize (HS2 HK2); clear HK2] end.
{ constructor; [|constructor].
eapply (region_kept_stack ubs0segs _ _ _ 2); [exact HU2 | exact Hhi4 | lia | lia | unfold spZ; rewrite Ha2, unsigned_lit_small by lia; lia | cbn; lia | cbn; lia]. }
clear HS. rename HS2 into HS.
assert (HB4' : Permutation (blocks L4 A4) ((img, N) :: cgif_blocks g s' N ++ (if Z.land fattr 1 =? 0 then [] else [(lpa, 3 * nlp)]) ++ rest)).
{ eapply Permutation_trans; [exact HB4|]. apply Permutation_sym. apply Permutation_middle. }
assert (Himg4 : In (img, N) (blocks L4 A4)) by (eapply blocks_perm_in; [exact HB4' | left; reflexivity]).
jrun_to LAWS ubs0tbl_ok HS HJ4 ubs0_A_free.
{ eapply wr_ok_cons_win; [reflexivity | ew_havocA; exact HU2 | cbn [r_wlo r_whi]; intros _; lia |]. apply wr_ok_nil. }
jreg HS (10%bv:reg) as Hb10. rewrite HX40 in Hb10.
jreg HS (2%bv:reg) as Hb2. rewrite (HE 2%nat 2%bv eq_refl), G2 in Hb2.
jreg HS (4%bv:reg) as Hb4. rewrite (HE 4%nat 4%bv eq_refl), G4, Htp0 in Hb4.
jreg HS (1%bv:reg) as Hb1.
pose proof (proj1 (cgif_ghost_blocks g s' N)) as Hfbl.
assert (Hfin4 : In (cg_file s', FILE_BLOCK) (blocks L4 A4)) by (eapply Permutation_in; [apply Permutation_sym; exact HB4 | apply in_or_app; left; exact Hfbl]).
lazymatch goal with |- SR _ (mkCfg ?msx _) _ =>
assert (HRELb : cgif_rel (ms_mem msx) md4 s' N GPAL gs')
by (eapply (cgif_rel_low API); [exact HH4 | exact HB4 | exact HREL4 |]; intros a Ha; mem_back ltac:(rewrite ?HU2) ltac:(lia)) end.
eapply SR_bind.
{ eapply (jfree_tmp_sink_res API IMG) with (a := img) (n := N) (spc := sp0 - 144) (f := cg_file s') (S := concat (YO07.s_out gs'));
[ exact HS | reflexivity | reflexivity | exact HJ4 | exact Hid4 | exact Himg4 | intros Hin i Hi; exact (Himgfresh Hin) | exact Hfin4
| | exact (proj1 (proj2 HRELb)) | exact HR4 | exact Hb10
| exact Hb2 | lia | exact Hspm | lia | lia | exact Hb4 | exact Hb1 | apply ret_ok_even; vm_compute; reflexivity ].
destruct (heap_sep_perm _ _ LAWS L4 A4 mem4 md4 (img, N) _ (cg_file s', FILE_BLOCK) HH4 HB4' ltac:(apply in_app_iff; left; exact Hfbl)) as [H1|H1]; cbn [fst snd] in H1; lia. }
intros c' (L5 & A5 & regs5 & mem5 & md5 & -> & HJ5 & Hid5 & HP5 & Hrm5 & Hkeep5 & Hhi5 & (HSK5 & Hfin5) & HR5). clear HJ4.
change (ms_segs ubs0_msyms) with ubs0segs in Hkeep5, Hhi5. cbn [ms_regs ms_mem mkst] in HP5, Hkeep5, Hhi5, HJ5, Hrm5, HSK5.
assert (HB5 : Permutation (blocks L5 A5) (cgif_blocks g s' N ++ (if Z.land fattr 1 =? 0 then [] else [(lpa, 3 * nlp)]) ++ rest)).
{ eapply perm_after_rm1; [exact HB4' | exact Hrm5]. }
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ5) as HH5.
assert (HREL5 : cgif_rel mem5 md5 s' N GPAL gs') by (eapply (cgif_rel_resink _ mem5 md4 md5 g s' N GPAL gs' (blocks L5 A5)); [exact HB5 | exact Hkeep5 | exact HRELb | exact HSK5]).
clear HRELb.
jafter_call_keep HS 68%nat regs5 mem5 HP5 [0%nat] HS2.
match type of HS2 with ?P -> _ => assert (HK2 : P); [|specialize (HS2 HK2); clear HK2] end.
{ constructor; [|constructor].
eapply (region_kept_stack ubs0segs _ _ _ 2); [ew_havocA; exact HU2 | exact Hhi5 | lia | lia | lia | cbn; lia | cbn; lia]. }
clear HS. rename HS2 into HS.
jrun_to LAWS ubs0tbl_ok HS HJ5 ubs0_A_free.
{ eapply wr_ok_cons_win; [reflexivity | ew_havocA; exact HU2 | cbn [r_wlo r_whi]; intros _; lia |]. apply wr_ok_nil. }
jreg HS (10%bv:reg) as Hc10. rewrite HX39 in Hc10.
jreg HS (2%bv:reg) as Hc2. rewrite (HE 2%nat 2%bv eq_refl), G2 in Hc2.
jreg HS (4%bv:reg) as Hc4. rewrite (HE 4%nat 4%bv eq_refl), G4, Htp0 in Hc4.
jreg HS (1%bv:reg) as Hc1.
lazymatch goal with |- SR _ (mkCfg ?msx _) _ =>
assert (HRELc : cgif_rel (ms_mem msx) md5 s' N GPAL gs')
by (eapply (cgif_rel_low API); [exact HH5 | exact HB5 | exact HREL5 |]; intros a Ha; mem_back ltac:(rewrite ?HU2) ltac:(lia)) end.
lazymatch goal with |- SR _ (mkCfg ?msq ?mdq) _ =>
eapply SR_bind with (R := fun c' => exists L6 A6 regs6 mem6 md6,
c' = mkCfg (mkst regs6 (Z_to_bv 64 (ubs0_A_LLVMFuzzerTestOneInput + 0x174)) mem6 (seg_rom ubs0segs)) md6 /\
journal ubs0_msyms MR LIB_STACK sp0 [sink_token] L A mem md L6 A6 mem6 md6 /\ st_init_done A6 = true /\
regs_preserved (ms_regs msq) regs6 /\ Permutation (blocks L6 A6) (cgif_blocks g s' N ++ rest) /\
(forall b m i, In (b, m) (blocks L6 A6) -> 0 <= i < m -> mbyte ubs0segs mem6 (b + i) = mbyte ubs0segs (ms_mem msq) (b + i)) /\
(forall x, alloc_ceiling <= x < 2 ^ 64 -> ~ (sp0 - 144 - ALLOC_STACK <= x < sp0 - 144) ->
mbyte ubs0segs mem6 x = mbyte ubs0segs (ms_mem msq) x /\ (writable_at ubs0segs (ms_mem msq) x <-> writable_at ubs0segs mem6 x)) /\
cgif_rel mem6 md6 s' N GPAL gs' /\ res_ok A6 (loop_bud3 b0 N (Z.of_nat (Datatypes.S k)) (qcount gs')))
end.
{ destruct (Z.eqb_spec (Z.land fattr 1) 0) as [Hz|Hz].
-
rewrite (Hlp0 Hz) in Hc10.
destruct (heap_model _ _ LAWS _ _ _ _ (proj1 HJ5)) as (Hh5 & Hl5 & _).
eapply SR_mono; [eapply (jfree_null _ (aa_free_null API)); [exact HS | reflexivity | reflexivity | exact Hh5 | exact Hl5 | exact Hc10 | exact Hc1 | apply ret_ok_even; vm_compute; reflexivity] |].
intros c' ->. lazymatch goal with |- context [mkst (ms_regs ?m0) _ (ms_mem _) _] => exists L5, A5, (ms_regs m0), (ms_mem m0), md5 end.
split; [reflexivity|]. split; [exact HJ5|]. split; [exact Hid5|]. split; [intros rr _; reflexivity|].
split; [rewrite app_nil_l in HB5; exact HB5|]. split; [intros; reflexivity|]. split; [intros x _ _; split; [reflexivity | tauto] |].
split; [exact HRELc|]. eapply res_ok_mono; [| exact HR5]. exact (loop_to_bud3 b0 N HNr bc _ _ _ HQ HQ' HBLE).
-
assert (Hlp5 : In (lpa, 3 * nlp) (blocks L5 A5)) by (eapply Permutation_in; [apply Permutation_sym; exact HB5 | apply in_app_iff; right; left; reflexivity]).
assert (HP' : Permutation (blocks L5 A5) ((lpa, 3 * nlp) :: cgif_blocks g s' N ++ rest)).
{ eapply Permutation_trans; [exact HB5|]. apply Permutation_sym. change ((lpa, 3 * nlp) :: cgif_blocks g s' N ++ rest) with ((lpa, 3 * nlp) :: cgif_blocks g s' N ++ ([] ++ rest)). apply Permutation_middle. }
eapply SR_mono.
{ eapply (jfree_tmp_sink_res API IMG) with (a := lpa) (n := 3 * nlp) (spc := sp0 - 144) (f := cg_file s') (S := concat (YO07.s_out gs'));
[ exact HS | reflexivity | reflexivity | exact HJ5 | exact Hid5 | exact Hlp5 | | exact Hfin5
| | exact (proj1 (proj2 HRELc)) | exact HR5 | rewrite Hlpa; exact Hc10
| exact Hc2 | lia | exact Hspm | lia | lia | exact Hc4 | exact Hc1 | apply ret_ok_even; vm_compute; reflexivity ].
+ intros Hin i Hi. apply Hbase in Hin.
destruct (heap_sep_perm _ _ LAWS L5 A5 mem5 md5 (lpa, 3 * nlp) _ (lpa, 3 * nlp) HH5 HP' ltac:(apply in_app_iff; right; exact Hin)) as [H1|H1]; cbn [fst snd] in H1; lia.
+ destruct (heap_sep_perm _ _ LAWS L5 A5 mem5 md5 (lpa, 3 * nlp) _ (cg_file s', FILE_BLOCK) HH5 HP' ltac:(apply in_app_iff; left; exact Hfbl)) as [H1|H1]; cbn [fst snd] in H1; lia. }
intros c' (L6 & A6 & regs6 & mem6 & md6 & -> & HJ6 & Hid6 & HP6 & Hrm6 & Hkeep6 & Hhi6 & (HSK6 & Hfin6) & HR6).
assert (HB6 : Permutation (blocks L6 A6) (cgif_blocks g s' N ++ rest)).
{ eapply perm_after_rm1; [| exact Hrm6]. exact HP'. }
exists L6, A6, regs6, mem6, md6. split; [reflexivity|]. split; [exact HJ6|]. split; [exact Hid6|]. split; [exact HP6|].
split; [exact HB6|]. split; [exact Hkeep6|]. split; [exact Hhi6|]. split.
{ eapply (cgif_rel_resink _ mem6 md5 md6 g s' N GPAL gs' (blocks L6 A6)); [exact HB6 | exact Hkeep6 | exact HRELc | exact HSK6]. }
eapply res_ok_mono; [| exact HR6]. apply rb_free_le_trans. exact (loop_to_bud3 b0 N HNr bc _ _ _ HQ HQ' HBLE). }
cbv beta. intros c' (L6 & A6 & regs6 & mem6 & md6 & -> & HJ6 & Hid6 & HP6 & HB6 & Kkeep6 & Hhi6 & HREL6 & HR6). clear HJ5 HRELc. rename Kkeep6 into Hkeep6.
cbn [ms_regs ms_mem mkst] in HP6, Hkeep6, Hhi6.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ6) as HH6.
jafter_call_keep HS 84%nat regs6 mem6 HP6 [0%nat] HS2.
match type of HS2 with ?P -> _ => assert (HK2 : P); [|specialize (HS2 HK2); clear HK2] end.
{ constructor; [|constructor].
eapply (region_kept_stack ubs0segs _ _ _ 2); [ew_havocA; exact HU2 | exact Hhi6 | lia | lia | lia | cbn; lia | cbn; lia]. }
clear HS. rename HS2 into HS.
jrun LAWS ubs0tbl_ok HS HJ6.
{ eapply wr_ok_cons_win; [reflexivity | ew_havocA; exact HU2 | cbn [r_wlo r_whi]; intros _; lia |]. apply wr_ok_nil. }
assert (Hat6 : cgif_at mem6 g s').
{ eapply (cgif_at_kept _ _ g s' N (blocks L6 A6) rest HB6); [| exact Hkeep6].
eapply (cgif_at_low API); [exact HH5 | exact HB5 | |].
{ eapply (cgif_at_kept _ _ g s' N (blocks L5 A5) _ HB5); [| exact Hkeep5].
eapply (cgif_at_low API); [exact HH4 | exact HB4 | exact Hat4 |].
intros a Ha. mem_back ltac:(rewrite ?HU2) ltac:(lia). }
intros a Ha. mem_back ltac:(rewrite ?HU2) ltac:(lia). }
assert (Hcf8' : (sp0 - 136) mod 8 = 0).
{ pose proof (proj2 (Z.div_exact sp0 16 ltac:(lia)) Hal16) as E16. replace (sp0 - 136) with ((2 * (sp0 / 16) - 17) * 8) by lia. apply Z_mod_mult. }
jbranch ubs0tbl HS.
-
jrun_to LAWS ubs0tbl_ok HS HJ6 L_CLOSE.
{ eapply wr_ok_cons_win; [reflexivity | ew_havocA; exact HU2 | cbn [r_wlo r_whi]; intros _; lia |]. apply wr_ok_nil. }
rewrite (st_ok_mkst ubs0segs _ _ _ HS eq_refl). cbn [ss_pc]. apply SR_here.
rewrite branch_eq_U, U_lit, (U_atom_off _ 18 (Z.of_nat (Datatypes.S k)) (-1)) in Hc by first [lia | ew_havocA; rewrite (HE 18%nat 18%bv eq_refl); exact G18].
assert (Hk0 : k = 0%nat) by (destruct (Z.eqb_spec (Z.of_nat (Datatypes.S k) + -1) 0); [lia | discriminate Hc]). clear Hc.
subst k || rewrite Hk0. change (loop_file G 0 gs' (skipn (Z.to_nat cur) PAYLOAD)) with (concat (YO07.close_gif G gs') ++ [59]). rewrite <- HG4.
lazymatch goal with |- realizes _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
eapply (llvm_close_x API IMG CLOSE UNLINK regs0 L A mem md b0 plen K HSORT HK rg L6 A6 mm md6 g s' N rest GPAL gs' _) end.
+ exact HJ6. + exact Hid6. + exact Hra0. + exact Htp0. + exact Hal16. + exact Hsp47.
+ eapply (cgif_at_low API); [exact HH6 | exact HB6 | exact Hat6 |]. intros a Ha. mem_back ltac:(rewrite ?HU2) ltac:(lia).
+ exact Hwf4. + exact HB6. + exact Hbase.
+ exists (pdata, nb). split; [exact Hpd | cbn; lia].
+ saved_ok_tac HS HU2 HW32 HW33 HW34 HW35.
+ reg_nowF HS ltac:(rewrite HU2; f_equal; lia).
+ reg_nowF HS ltac:(rewrite HU9; reflexivity).
+ ut_tac HS HE.
+ eapply (cgif_rel_low API); [exact HH6 | exact HB6 | exact HREL6 |]. intros a Ha. mem_back ltac:(rewrite ?HU2) ltac:(lia).
+ clear - HLEN HLEN4 HFO HN1 HNle. unfold CLOSE_OUT, HDR_OUT, FRAME_OUT, SINK_MAX in *. lia.
+ exact HR6.
+ eapply (bud3_close_room b0 plen N HROOM HNr); [exact Hkz | exact HQ' | apply rb_le_refl].
+ eapply (bud3_close_fin b0 plen N HNr); [exact Hkz | exact HQ' | apply rb_le_refl].
-
rewrite branch_eq_U, U_lit, (U_atom_off _ 18 (Z.of_nat (Datatypes.S k)) (-1)) in Hc by first [lia | ew_havocA; rewrite (HE 18%nat 18%bv eq_refl); exact G18].
assert (Hk1 : (1 <= k)%nat) by (destruct (Z.eqb_spec (Z.of_nat (Datatypes.S k) + -1) 0); [discriminate Hc | lia]). clear Hc.
assert (Hkz2 : 2 <= Z.of_nat (Datatypes.S k) <= 16) by (clear - Hk Hk1; lia).
jrun_to LAWS ubs0tbl_ok HS HJ6 ubs0_A_read_frameconfig.
{ eapply wr_ok_cons_win; [reflexivity | ew_havocA; exact HU2 | cbn [r_wlo r_whi]; intros _; lia |]. apply wr_ok_nil. }
jreg HS (10%bv:reg) as Hd10. rewrite HU2 in Hd10. jreg HS (11%bv:reg) as Hd11. rewrite HU2 in Hd11.
jreg HS (12%bv:reg) as Hd12. rewrite (HE 8%nat 8%bv eq_refl), G8 in Hd12.
jreg HS (2%bv:reg) as Hd2. rewrite (HE 2%nat 2%bv eq_refl), G2 in Hd2.
jreg HS (4%bv:reg) as Hd4. rewrite (HE 4%nat 4%bv eq_refl), G4, Htp0 in Hd4. jreg HS (1%bv:reg) as Hd1.
lazymatch goal with |- SR _ (mkCfg ?msx _) _ =>
assert (Hsp : spZ (ms_regs msx) = sp0 - 144) by (unfold spZ; rewrite Hd2; apply unsigned_lit_small; lia) end.
rewrite (st_ok_mkst ubs0segs _ _ _ HS eq_refl). cbn [ss_pc].
lazymatch goal with |- SR _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
assert (HRELq : cgif_rel mm md6 s' N GPAL gs')
by (eapply (cgif_rel_low API); [exact HH6 | exact HB6 | exact HREL6 |]; intros a Ha; mem_back ltac:(rewrite ?HU2) ltac:(lia));
assert (Hfin6' : In (cg_file s', FILE_BLOCK) (blocks L6 A6)) by (eapply Permutation_in; [apply Permutation_sym; exact HB6 | apply in_or_app; left; exact Hfbl]);
assert (HPLq : garr8 ubs0segs mm pdata PAYLOAD)
by (eapply (payload_kept API); [exact HJ6 | rewrite HPLn; exact Hpd | rewrite HPLn; eapply Permutation_in; [apply Permutation_sym; exact HB6 | apply in_or_app; right; apply Hbase; exact Hpd] | exact inFP_token | exact HPL]);
pose proof (journal_restart ubs0_msyms MR _ _ _ _ _ _ _ _ _ _ _ [] HJ6) as HJr end.
eapply SR_bind.
{ lazymatch goal with |- SR _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
eapply (RFC LIB_STACK sp0 [] L6 A6 mm md6 L6 A6 mm md6 rg (cgif_blocks g s' N ++ rest) (sp0 - 136) (sp0 - 112) N pdata nb cur PAYLOAD
(loop_bud3 b0 N (Z.of_nat (Datatypes.S k)) (qcount gs'))) end.
+ exact HJr. + exact Hid6.
+ intros b Hb. eapply Permutation_in; [exact HB6 | exact Hb].
+ exact HB6.
+ apply in_app_iff. right. apply Hbase. exact Hpd.
+ rewrite Hd1. apply ret_ok_even. vm_compute. reflexivity.
+ exact Hd4.
+ rewrite Hd10. f_equal. lia. + rewrite Hd11. f_equal. lia. + exact Hd12.
+ rewrite Hsp. exact Hspm. + rewrite Hsp. lia. + rewrite Hsp. lia. + lia. + rewrite Hsp. lia. + lia. + lia.
+ exact Hcf8'. + exact Hcf8. + lia. + lia. + exact Hcur. + exact Hnb.
+ stack_word HS HU2 36%nat HX36. lia.
+ replace (sp0 - 136 + 8) with (sp0 - 128) by lia. stack_word HS HU2 37%nat HX37. lia.
+ replace (sp0 - 136 + 16) with (sp0 - 120) by lia. stack_word HS HU2 38%nat HX38. lia.
+ exact HPLq. + exact HPLn. + exact HR6.
+ eapply (bud3_rfc_room b0 plen N HROOM HNr); [exact Hkz | exact HQ' | apply rb_le_refl]. }
cbv beta. intros c' (L7 & A7 & regs7 & mem7 & md7 & res & cur2 & -> & HJ7r & Hid7 & HP7 & Hr10 & Hfr7 & Hbb7 & Wp7 & Wn7 & Wc7 & Hcur7 & ALT).
cbn [ms_regs ms_mem mkst] in HP7, Hfr7, Hbb7, Hr10, HJ7r.
assert (HJ7 : journal ubs0_msyms MR LIB_STACK sp0 [sink_token] L A mem md L7 A7 mem7 md7).
{ eapply (journal_sub_gen ubs0_msyms MR LAWS); [exact HJ6 | exact HJ7r | lia | lia | intros a0 (r & [] & _)]. }
assert (HSK7 : sink_at ubs0_msyms mem7 md7 (cg_file s') (concat (YO07.s_out gs')) /\ In (cg_file s', FILE_BLOCK) (blocks L7 A7)).
{ eapply (sink_kept ubs0_msyms MR); [exact HJ7r | intros (r & [] & _) | exact Hfin6' | intros x Hx (r & [] & _) | exact (proj1 (proj2 HRELq))]. }
assert (HREL7 : cgif_rel mem7 md7 s' N GPAL gs').
{ eapply (cgif_rel_resink _ mem7 md6 md7 g s' N GPAL gs' (cgif_blocks g s' N ++ rest) rest (Permutation_refl _)); [exact Hbb7 | exact HRELq | exact (proj1 HSK7)]. }
clear HJ6 HJr HRELq.
rewrite Hsp in Hfr7. rewrite Hd1.
lazymatch type of HS with st_ok _ ?E1 ?ss1 ?ms1 =>
pose proof (st_ok_after_call ubs0segs 100 E1 ss1 ms1 regs7 mem7
[YP09.mkRegion (Some 2%nat) 64 144 64 144 (saved_chunks 32)] (ubs0_A_LLVMFuzzerTestOneInput + 0x18c) HS eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(apply submem_keep; [| apply submem_nil]; split; [reflexivity|]; split; [cbn; lia|]; split; [cbn; lia|]; split; [cbn; lia|];
apply incl_chunks_sound; vm_compute; reflexivity)
ltac:(vm_compute; reflexivity) HP7) as HS2;
let ss2 := eval vm_compute in (ss_after_call ss1 [YP09.mkRegion (Some 2%nat) 64 144 64 144 (saved_chunks 32)] 100 (ubs0_A_LLVMFuzzerTestOneInput + 0x18c)) in
change (ss_after_call ss1 _ 100 _) with ss2 in HS2 end.
match type of HS2 with ?P -> _ => assert (HK2 : P); [|specialize (HS2 HK2); clear HK2] end.
{ constructor; [|constructor].
split; cbn [r_base r_lo r_hi r_wlo r_whi base_val]; ew_havocA; rewrite HU2; intros a Ha.
- apply Hfr7; lia.
- intros _. apply (journal_stack_w _ _ _ _ _ _ _ _ _ _ _ _ _ HJ7). lia. }
clear HS. rename HS2 into HS.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ7) as HH7.
assert (Hat7 : cgif_at mem7 g s').
{ eapply (cgif_at_kept _ _ g s' N (cgif_blocks g s' N ++ rest) rest (Permutation_refl _)); [| exact Hbb7].
eapply (cgif_at_low API); [exact HH6 | exact HB6 | exact Hat6 |]. intros a Ha. mem_back ltac:(rewrite ?HU2) ltac:(lia). }
destruct ALT as [(-> & HPFf & (leak & HB7) & HR7) | (-> & lpal' & lpa' & img' & fattr' & fgen' & delay' & nlp' & tidx' & LPALV' & IMGV' & Hfc7 & Hlp07 & Hlpa7 & HB7 & HPFN & HGI7 & HGIn7 & HGL7 & HR7)].
+
pin_reg HS (10%bv:reg) 0 Hr10.
jrun_to LAWS ubs0tbl_ok HS HJ7 L_CLOSE.
{ eapply wr_ok_cons_win; [reflexivity | ew_havocA; exact HU2 | cbn [r_wlo r_whi]; intros _; lia |]. apply wr_ok_nil. }
rewrite (st_ok_mkst ubs0segs _ _ _ HS eq_refl). cbn [ss_pc]. apply SR_here.
assert (HPFf' : fst (fst (parse_frame G (skipn (Z.to_nat cur) PAYLOAD))) = false).
{ rewrite <- HG4. unfold parse_frame. cbn [YO07.g_w YO07.g_h gcfg_of]. rewrite <- (proj1 (proj2 (proj2 (proj2 Hwf4)))). exact HPFf. }
rewrite (loop_file_stop G k gs' _ HPFf'). change (loop_file G 0 gs' (skipn (Z.to_nat cur) PAYLOAD)) with (concat (YO07.close_gif G gs') ++ [59]). rewrite <- HG4.
destruct (bud3_rfc_fail b0 plen N HROOM HNr _ _ _ Hkz HQ' (rb_le_refl _)) as [HCR7 HCF7].
lazymatch goal with |- realizes _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
eapply (llvm_close_x API IMG CLOSE UNLINK regs0 L A mem md b0 plen K HSORT HK rg L7 A7 mm md7 g s' N (leak ++ rest) GPAL gs' _) end.
* exact HJ7. * exact Hid7. * exact Hra0. * exact Htp0. * exact Hal16. * exact Hsp47.
* eapply (cgif_at_low API); [exact HH7 | | exact Hat7 |].
{ eapply Permutation_trans; [exact HB7 | apply Permutation_app_swap_app]. }
intros a Ha. mem_back ltac:(rewrite ?HU2) ltac:(lia).
* exact Hwf4.
* eapply Permutation_trans; [exact HB7 | apply Permutation_app_swap_app].
* intros b Hb. apply in_app_iff. right. apply Hbase. exact Hb.
* exists (pdata, nb). split; [exact Hpd | cbn; lia].
* saved_ok_tac HS HU2 HW32 HW33 HW34 HW35.
* reg_nowF HS ltac:(rewrite HU2; f_equal; lia).
* reg_nowF HS ltac:(rewrite HU9; reflexivity).
* ut_tac HS HE.
* eapply (cgif_rel_low API); [exact HH7 | | exact HREL7 |].
{ eapply Permutation_trans; [exact HB7 | apply Permutation_app_swap_app]. }
intros a Ha. mem_back ltac:(rewrite ?HU2) ltac:(lia).
* clear - HLEN HLEN4 HFO HN1 HNle. unfold CLOSE_OUT, HDR_OUT, FRAME_OUT, SINK_MAX in *. lia.
* exact HR7. * exact HCR7. * exact HCF7.
+
assert (HPF7 : parse_frame G (skipn (Z.to_nat cur) PAYLOAD) = (true, (fattr', fgen', delay', tidx', nlp', LPALV', IMGV'), skipn (Z.to_nat cur2) PAYLOAD)).
{ rewrite <- HG4. unfold parse_frame. cbn [YO07.g_w YO07.g_h gcfg_of]. rewrite <- (proj1 (proj2 (proj2 (proj2 Hwf4)))). exact HPFN. }
assert (Himg7 : In (img', N) (blocks L7 A7)) by (eapply blocks_perm_in; [exact HB7 | left; reflexivity]).
destruct (blocks_range _ _ LAWS L7 A7 mem7 md7 img' N HH7 Himg7) as [Hi0' Hi1'].
assert (Hlpr' : Z.land fattr' 1 <> 0 -> 4096 <= lpa' /\ lpa' + 3 * nlp' <= alloc_ceiling).
{ intros Hf1. eapply (blocks_range _ _ LAWS); [exact HH7|]. eapply blocks_perm_in; [exact HB7|].
right. apply in_or_app. left. destruct (Z.eqb_spec (Z.land fattr' 1) 0) as [E0|E0]; [exfalso; exact (Hf1 E0)|]. left. reflexivity. }
pin_reg HS (10%bv:reg) 1 Hr10.
jrun_to LAWS ubs0tbl_ok HS HJ7 L_LH.
{ eapply wr_ok_cons_win; [reflexivity | ew_havocA; exact HU2 | cbn [r_wlo r_whi]; intros _; lia |]. apply wr_ok_nil. }
rewrite (st_ok_mkst ubs0segs _ _ _ HS eq_refl). cbn [ss_pc]. apply SR_here.
destruct k as [|k1]; [lia|]. rewrite (loop_file_step G k1 gs' _ _ _ _ _ _ _ _ _ HPF7). change k1 with (Nat.pred (Datatypes.S k1)).
pose proof (obj_at_range _ _ _ _ _ Hfc7 5%nat nlp' eq_refl) as Hnlp'. cbn in Hnlp'.
lazymatch goal with |- realizes _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
eapply (IH rg L7 A7 mm md7 g s' N rest pdata nb cur2 lpal' lpa' img' fattr' fgen' delay' nlp' tidx' PAYLOAD GPAL IMGV' LPALV' G gs' (rfc_rb_ok (loop_bud3 b0 N (Z.of_nat (Datatypes.S (Datatypes.S k1))) (qcount gs')) fattr' nlp' N)) end.
* lia. * exact HJ7. * exact Hid7. * exact Hra0. * exact Htp0. * exact Hal16. * exact Hsp47.
* eapply (cgif_at_low API); [exact HH7 | | exact Hat7 |].
{ eapply Permutation_trans; [exact HB7|].
change ((img', N) :: (if Z.land fattr' 1 =? 0 then [] else [(lpa', 3 * nlp')]) ++ cgif_blocks g s' N ++ rest)
with (((img', N) :: (if Z.land fattr' 1 =? 0 then [] else [(lpa', 3 * nlp')])) ++ (cgif_blocks g s' N ++ rest)).
apply Permutation_app_swap_app. }
intros a Ha. mem_back ltac:(rewrite ?HU2) ltac:(lia).
* exact Hwf4.
* eapply Permutation_trans; [exact HB7|].
change ((img', N) :: (if Z.land fattr' 1 =? 0 then [] else [(lpa', 3 * nlp')]) ++ cgif_blocks g s' N ++ rest)
with (((img', N) :: (if Z.land fattr' 1 =? 0 then [] else [(lpa', 3 * nlp')])) ++ (cgif_blocks g s' N ++ rest)).
apply Permutation_app_swap_app.
* exact Hbase. * exact Hpd. * exact Hnb.
* saved_ok_tac HS HU2 HW32 HW33 HW34 HW35.
* intros kk Hkk. fold sp0. cbn [ms_mem mkst] in *. mb_frame_with HF4 ltac:(lia) ltac:(ew_havocA; rewrite ?HU2; lia). apply Wp7. exact Hkk.
* intros kk Hkk. fold sp0. cbn [ms_mem mkst] in *. mb_frame_with HF4 ltac:(lia) ltac:(ew_havocA; rewrite ?HU2; lia). replace (sp0 - 128 + Z.of_nat kk) with (sp0 - 136 + 8 + Z.of_nat kk) by lia. apply Wn7. exact Hkk.
* intros kk Hkk. fold sp0. cbn [ms_mem mkst] in *. mb_frame_with HF4 ltac:(lia) ltac:(ew_havocA; rewrite ?HU2; lia). replace (sp0 - 120 + Z.of_nat kk) with (sp0 - 136 + 16 + Z.of_nat kk) by lia. apply Wc7. exact Hkk.
* lia.
* fold sp0. eapply (obj_at_transport_range _ _ _ _ _ _ 32); [exact Hfc7 | reflexivity |]. intros i Hi. cbn [ms_mem mkst] in *.
mb_frame_with HF4 ltac:(lia) ltac:(ew_havocA; rewrite ?HU2; lia). reflexivity.
* exact Hlp07. * exact Hlpa7.
* reg_nowF HS ltac:(rewrite HU2; f_equal; lia).
* reg_nowF HS ltac:(rewrite HU8; reflexivity).
* reg_nowF HS ltac:(rewrite HU9; reflexivity).
* reg_nowF HS ltac:(rewrite HU18; f_equal; lia).
* ut_tac HS HE.
* exact HPL. * exact HPLn.
* eapply (cgif_rel_low API); [exact HH7 | | exact HREL7 |].
{ eapply Permutation_trans; [exact HB7|].
change ((img', N) :: (if Z.land fattr' 1 =? 0 then [] else [(lpa', 3 * nlp')]) ++ cgif_blocks g s' N ++ rest)
with (((img', N) :: (if Z.land fattr' 1 =? 0 then [] else [(lpa', 3 * nlp')])) ++ (cgif_blocks g s' N ++ rest)).
apply Permutation_app_swap_app. }
intros a Ha. mem_back ltac:(rewrite ?HU2) ltac:(lia).
* clear - HLEN HLEN4. replace (17 - Z.of_nat (Datatypes.S k1)) with (17 - Z.of_nat (Datatypes.S (Datatypes.S k1)) + 1) by lia. rewrite Z.mul_add_distr_r, Z.mul_1_l. lia.
* exact HG4.
* eapply garr8_frame; [exact HGI7|]. intros a Ha. rewrite HGIn7 in Ha. cbn [ms_mem mkst] in *.
mb_frame_with HF4 ltac:(clear - Ha Hi0' Hi1' Hac; lia) ltac:(ew_havocA; rewrite ?HU2; clear - Ha Hi0' Hi1' Hac Hsp0al Hstk0 Hceil Hsp063 HLSv; lia). reflexivity.
* exact HGIn7.
* intros Hf1. destruct (HGL7 Hf1) as [HGL HGLn]. destruct (Hlpr' Hf1) as [Hl0' Hl1']. split; [|exact HGLn].
eapply garr8_frame; [exact HGL|]. intros a Ha. rewrite HGLn in Ha. cbn [ms_mem mkst] in *.
mb_frame_with HF4 ltac:(clear - Ha Hl0' Hl1' Hac; lia) ltac:(ew_havocA; rewrite ?HU2; clear - Ha Hl0' Hl1' Hac Hsp0al Hstk0 Hceil Hsp063 HLSv; lia). reflexivity.
* exact HR7.
* replace (Z.of_nat (Datatypes.S k1)) with (Z.of_nat (Datatypes.S (Datatypes.S k1)) - 1) by lia.
eapply (bud3_rfc_ok b0 N HNr); [exact Hkz2 | exact HQ' | clear - Hnlp'; lia | apply rb_le_refl].
Qed.
End S.
End e.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
