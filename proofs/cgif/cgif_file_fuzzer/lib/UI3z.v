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
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YN32 YK0w.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0i YO0f YO0x YO0d YO0e YO03
YO0p YO0j YO0m YO0l YO0n YO0k YO0o.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UH00 UH03 UH02 UN3b
YI06 UI5b YI09 YI08 YI0r YI0o YI6a UI1w UI3p UI3m UI3t.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YI14 YI13 YI00 YI02 UI5c UI2z YI0j YI0k YI6c YI01.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YO07.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UI3w UI4j UI4g.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI5a YI2w UI2v UI3x.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition ssT3 : sstate :=
ra_ss3W PC_T3 (sr_set (sr_set (sr_set sr_atoms 18%bv (SOff 44%nat 0)) 20%bv (SLit ubs0_A_cgif_writecb)) 19%bv (SLit 0)) 0 0
(enc_chunks ++ [ch7 71]) true [(70%nat, mkAF 0 (2^32-1) 0); (69%nat, mkAF 4096 CEIL_MAX 4); (71%nat, mkAF 0 255 0)] [] [].
Ltac raw_kept HE8 Hblk HJc Hrawin2 cx :=
split; cbn [r_base r_lo r_hi r_wlo r_whi base_val]; ew_havoc; rewrite HE8, unsigned_lit_small by lia; intros a Ha;
[ replace a with (c_raw cx + (a - c_raw cx)) by lia; apply (Hblk (c_raw cx) RAW_SIZE (a - c_raw cx) Hrawin2); [lia|];
replace (c_raw cx + (a - c_raw cx)) with a by lia;
let r := fresh "r" in let Hr := fresh "Hr" in intros (r & [<- | [<- | []]] & Hr); cbn [fst snd sink_token] in Hr; lia
| intros _; replace a with (c_raw cx + (a - c_raw cx)) by lia; apply (present_writable ubs0_msyms);
apply (proj1 (heap_blocks _ _ (aa_laws _) _ _ _ _ (c_raw cx) 48 (a - c_raw cx) (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJc) Hrawin2 ltac:(lia))) ].
Section S.
Variable API : AllocAPI ubs0_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs0_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs0_msyms MR.
Variables (IMGV LCTV : list Z).
Hypothesis FWRITE : fwrite_spec ubs0_msyms MR ubs0_A_fwrite.
Lemma wtok_new : forall STK sp0 FP bl0 p n,
wtok' STK sp0 FP bl0 (p, n) -> 0 < n -> p + n <= alloc_ceiling -> alloc_ceiling + STK <= sp0 ->
~ inFP FP p -> ~ In (p, n) bl0.
Proof using.
intros STK sp0 FP bl0 p n HW Hn Hpn Hsp Hfp Hin.
destruct (HW [(p, n)] 0 ltac:(left; reflexivity) ltac:(cbn [snd]; lia)) as [Hs | [[Hf _] | (b & m & Hb & Hnb & Hr)]]; cbn [fst snd] in *.
- lia.
- rewrite Z.add_0_r in Hf. exact (Hfp Hf).
- destruct Hb as [Hb | []]. injection Hb as <- <-. exact (Hnb Hin).
Qed.
Lemma jfree_sink_R :
forall E ss ms STK sp0 FP L A mem md Lc Ac mdc a n spc raw f S (bo : rbound),
st_ok ubs0segs E ss ms -> ss_pc ss = ubs0_A_free -> ss_resv ss = None ->
journal ubs0_msyms MR STK sp0 FP L A mem md Lc Ac (ms_mem ms) mdc -> st_init_done Ac = true ->
In (a, n) (blocks Lc Ac) -> ~ In (a, n) (blocks L A) -> 0 < n ->
In (f, FILE_BLOCK) (blocks Lc Ac) -> (a + n <= f \/ f + FILE_BLOCK <= a) ->
sink_at ubs0_msyms (ms_mem ms) mdc f S -> res_ok Ac bo ->
getr (ms_regs ms) 10 = Z_to_bv 64 a ->
getr (ms_regs ms) 2 = Z_to_bv 64 spc -> 0 <= spc < 2 ^ 64 -> spc mod 16 = 0 ->
sp0 - STK <= spc - ALLOC_STACK -> spc <= sp0 ->
getr (ms_regs ms) 4 = Z_to_bv 64 (ms_tp ubs0_msyms) ->
getr (ms_regs ms) 1 = raw -> YK0s.ret_ok raw ->
SR ubs0segs (mkCfg ms mdc)
(fun c' => exists L2 A2 regs2 mem2 md2,
c' = mkCfg (mkst regs2 raw mem2 (seg_rom ubs0segs)) md2 /\
journal ubs0_msyms MR STK sp0 FP L A mem md L2 A2 mem2 md2 /\
st_init_done A2 = true /\
regs_preserved (ms_regs ms) regs2 /\
rm1 (a, n) (blocks Lc Ac) (blocks L2 A2) /\
(forall b m i, In (b, m) (blocks L2 A2) -> 0 <= i < m -> mbyte ubs0segs mem2 (b + i) = mbyte ubs0segs (ms_mem ms) (b + i)) /\
(forall x, alloc_ceiling <= x < 2 ^ 64 -> ~ (spc - ALLOC_STACK <= x < spc) ->
mbyte ubs0segs mem2 x = mbyte ubs0segs (ms_mem ms) x /\ (writable_at ubs0segs (ms_mem ms) x <-> writable_at ubs0segs mem2 x)) /\
sink_at ubs0_msyms mem2 md2 f S /\ In (f, FILE_BLOCK) (blocks L2 A2) /\ res_ok A2 (rb_free bo n)).
Proof using IMG LAWS.
intros E ss ms STK sp0 FP L A mem md Lc Ac mdc a n spc raw f S bo HS Hpc Hrv HJ Hid Hin Hnew Hn Hfin Hsep HSK HRbo H10 H2 Hspc Hal Hlo Hhi H4 H1 Hraw.
pose proof (proj1 alloc_ceiling_val) as Hac.
pose proof (journal_restart ubs0_msyms MR _ _ _ _ _ _ _ _ _ _ _ [(a, a + n)] HJ) as HJl.
destruct (heap_blocks_range _ _ LAWS Lc Ac (ms_mem ms) mdc a n (proj1 HJ) Hin Hn) as (Ha0 & Ha1 & Ha16).
eapply SR_mono.
{ eapply (jfree_tok_res API IMG) with (a := a) (n := n) (spc := spc);
[ exact HS | exact Hpc | exact Hrv | exact HJl | exact Hid | | exact HRbo | exact H10 | exact H2 | exact Hspc | exact Hal | exact Hlo | exact Hhi | exact H4 | exact H1 | exact Hraw ].
split; [exact Hin|]. intros _ i Hi. cbn [fst snd] in Hi |- *. exists (a, a + n). split; [left; reflexivity | cbn [fst snd]; lia]. }
cbv beta. intros c' (L2 & A2 & regs2 & mem2 & md2 & -> & HJ2 & Hid2 & HP2 & Hrm & Hkeep & Hhi2 & HRo2).
assert (HK : sink_at ubs0_msyms mem2 md2 f S /\ In (f, FILE_BLOCK) (blocks L2 A2)).
{ eapply (sink_kept ubs0_msyms MR); [exact HJ2 | | exact Hfin | | exact HSK].
- intros (r & [<- | []] & Hr). cbn [fst snd] in Hr. lia.
- intros x Hx (r & [<- | []] & Hr). cbn [fst snd] in Hr. lia. }
exists L2, A2, regs2, mem2, md2. split; [reflexivity|]. split.
{ eapply (journal_sub_gen ubs0_msyms MR LAWS); [exact HJ | exact HJ2 | lia | lia |].
intros x (r & [<- | []] & Hr). cbn [fst snd] in Hr. right. exists a, n. split; [exact Hin|]. split; [exact Hnew | lia]. }
split; [exact Hid2|]. split; [exact HP2|]. split; [exact Hrm|]. split; [exact Hkeep|]. split; [exact Hhi2|]. split; [exact (proj1 HK)|]. split; [exact (proj2 HK) | exact HRo2].
Qed.
Definition QT3 (cx : ra_cx) (S : list Z) (res rcur' : Z) (m' : word -> option byte) (md' : Model) : Prop :=
res = 0 /\ rcur' = 0 /\
exists raster, YO07.lzw_stream (2 ^ (ra_iclen cx - 1)) (ra_iclen cx) (ra_pix cx IMGV) = Some raster /\
sink_at ubs0_msyms m' md' (c_f cx) (S ++ ra_gce cx ++ ra_hdr cx ++ ra_lctb cx LCTV ++ [ra_iclen cx - 1] ++ raster) /\
Z.of_nat (length raster) <= 2 * c_nP cx + 16.
Lemma ra_t3_R : forall cx L A mem md regs0 (S : list Z) (b : rbound) c1,
rcx_ok cx -> ra_origin cx regs0 -> Permutation (blocks L A) (c_blocks cx) ->
Z.of_nat (length S) + 2 * c_nP cx + 2048 <= SINK_MAX ->
at_T3 API IMGV LCTV cx L A mem md regs0 S b c1 ->
SR ubs0segs c1 (ra_post4R API ((c_raw cx + 40, c_raw cx + 44) :: sink_fp (c_f cx)) (QT3 cx S) (fun s => res_ok s (rawadd_rb b)) cx L A mem md regs0).
Proof using FWRITE IMG.
intros cx L A mem md regs0 S b c1 Hcx HO HB Hroom
(L2 & A2 & regs2 & mem2 & md2 & bb & Lbb & M & -> & HJ & Hid & (bo & HRbo & HRimp) & G2 & G8 & G4 & G3 & G27 & G18 & G20 & HB2 & Hwt & W32 & W40 & HM & Hobjs & HFS
& HVOK & HM2 & HFB7 & HSK & G19).
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HSTKv : RAWADD_STK = 8704) by reflexivity. assert (HASv : ALLOC_STACK = 8192) by reflexivity.
assert (HRSv : RAW_SIZE = 48) by reflexivity. assert (HGSv : CGIF_SIZE = 96) by reflexivity.
assert (HWv : WRITECB_STK = 528) by reflexivity. assert (HFBv : FILE_BLOCK = 1264) by reflexivity.
pose proof HO as (Hspe & Htp0 & Hgp0 & Hra0 & Hgp & H25o & H26o & H27o).
pose proof Hcx as ((Hspal & Hsplo & Hcfplo & Hcfphi & Hcfpal & Hraw0 & Hraw1 & Hraw16 & Hg0 & Hg1 & Hg16 & Himg0 & Himg1 & Himg16 &
Hs1 & Hs2 & Hs3 & Hw1 & Hh1 & HnP & HnP2 & Hsgct & Hwfn & Hfile & Htpv & Hf0 & Hf1 & Hfin & Hsp47) & Hslct).
pose proof (objs_fields_ok _ _ _ Hobjs) as (F0 & F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & G1' & G2' & G3' & G4' & G5' & G6' & G7' & G8' & LG).
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HH2.
pose proof HJ as (_ & _ & _ & _ & _ & (Hsp0al & Hstk0 & Hceil & Hsp063 & Hstw) & _). cbn beta in Hstw.
assert (Hbbin : In (bb, Lbb) (blocks L2 A2)) by (eapply Permutation_in; [apply Permutation_sym; exact HB2 | left; reflexivity]).
destruct (heap_blocks_range _ _ LAWS L2 A2 mem2 md2 bb Lbb HH2 Hbbin ltac:(lia)) as (Hbb0 & Hbb1 & Hbb16).
assert (Hrawin : In (c_raw cx, RAW_SIZE) (blocks L A)) by (eapply blocks_perm_in; [exact HB | left; reflexivity]).
assert (Hrawin2 : In (c_raw cx, 48) (blocks L2 A2)) by (rewrite <- HRSv; eapply Permutation_in; [apply Permutation_sym; exact HB2 | right; exact Hrawin]).
assert (Hgin : In (c_g cx, CGIF_SIZE) (blocks L A)) by (eapply blocks_perm_in; [exact HB | right; left; reflexivity]).
assert (HfinA : In (c_f cx, FILE_BLOCK) (blocks L A)) by (eapply blocks_perm_in; [exact HB | right; right; right; exact Hfin]).
assert (Hgin2 : In (c_g cx, CGIF_SIZE) (blocks L2 A2)) by (eapply Permutation_in; [apply Permutation_sym; exact HB2 | right; exact Hgin]).
assert (Hfin2 : In (c_f cx, FILE_BLOCK) (blocks L2 A2)) by (eapply Permutation_in; [apply Permutation_sym; exact HB2 | right; exact HfinA]).
assert (Hrf : c_raw cx + 48 <= c_f cx \/ c_f cx + FILE_BLOCK <= c_raw cx).
{ pose proof (heap_sep_in2 ubs0_msyms MR LAWS L2 A2 _ md2 (c_raw cx, RAW_SIZE) (c_f cx, FILE_BLOCK) HH2 Hrawin2 Hfin2 ltac:(intros X; injection X; lia)) as Hd. cbn [fst snd] in Hd. lia. }
assert (Hgf : c_g cx + 96 <= c_f cx \/ c_f cx + FILE_BLOCK <= c_g cx).
{ pose proof (heap_sep_in2 ubs0_msyms MR LAWS L2 A2 _ md2 (c_g cx, CGIF_SIZE) (c_f cx, FILE_BLOCK) HH2 Hgin2 Hfin2 ltac:(intros X; injection X; lia)) as Hd. cbn [fst snd] in Hd. lia. }
assert (Hbf : bb + Lbb <= c_f cx \/ c_f cx + FILE_BLOCK <= bb).
{ pose proof (heap_sep_perm ubs0_msyms MR LAWS L2 A2 _ md2 (bb, Lbb) _ (c_f cx, FILE_BLOCK) HH2 HB2 HfinA) as Hd. cbn [fst snd] in Hd. exact Hd. }
assert (Hbr : bb + Lbb <= c_raw cx \/ c_raw cx + 48 <= bb).
{ pose proof (heap_sep_perm ubs0_msyms MR LAWS L2 A2 _ md2 (bb, Lbb) _ (c_raw cx, RAW_SIZE) HH2 HB2 Hrawin) as Hd. cbn [fst snd] in Hd. lia. }
assert (Hgr : c_g cx + 96 <= c_raw cx \/ c_raw cx + 48 <= c_g cx).
{ pose proof (heap_sep_in2 ubs0_msyms MR LAWS L2 A2 _ md2 (c_g cx, CGIF_SIZE) (c_raw cx, 48) HH2 Hgin2 Hrawin2 ltac:(intros X; injection X; lia)) as Hd. cbn [fst snd] in Hd. lia. }
assert (Hsinkaddr : forall a, c_f cx <= a < c_f cx + FILE_BLOCK \/ env_addr a -> 0 <= a < 2 ^ 64 /\ ~ (c_raw cx + 40 <= a < c_raw cx + 44)).
{ intros a [Ha | Ha]; [split; lia|]. pose proof (ubs0_env_addr_range a Ha) as Hr. split; [lia|]. intros Hin.
pose proof Hrawin2 as Hin1. apply blocks_In in Hin1 as (q & Hq & Hqin).
destruct (skl_env ubs0_msyms a Ha) as (HimgA & _).
apply (il_blocks IMG L2 A2 mem2 md2 q 48 (a - c_raw cx) (proj1 HH2) Hqin ltac:(lia)). rewrite Hq. replace (c_raw cx + (a - c_raw cx)) with a by lia. exact HimgA. }
assert (Hbnew : ~ In (bb, Lbb) (blocks L A)).
{ apply (wtok_new _ _ _ _ _ _ Hwt); [lia | lia | lia |].
intros (r & [<- | [<- | [<- | []]]] & Hr); cbn [fst snd sink_token] in Hr; lia. }
set (M' := M mod 2 ^ 32).
pose proof (Z.mod_pos_bound M (2 ^ 32) ltac:(lia)) as HM'. fold M' in HM'.
assert (HMM : M' = M) by (subst M'; apply Z.mod_small; clear - HM HM2 HnP HnP2 Himg0 Himg1 Hac Hw1 Hh1; unfold c_nP in *; nia).
assert (W40' : val_mem ubs0segs mem2 (c_sp cx + 16) 4 M') by (subst M'; change (2 ^ 32) with (2 ^ (8 * Z.of_nat 4)); apply (proj1 (val_mem_mod _ _ _ _)); exact W40).
assert (Ric : 0 <= ra_iclen cx - 1 < 256).
{ unfold ra_iclen, YO07.calcInitCodeLen.
assert (Hne : 0 <= ra_ne cx <= 256) by (unfold ra_ne, num_eff; destruct (negb (c_slct cx =? 0)); destruct (_ && _ && _); lia).
assert (Hc8 : exists k, 0 <= k <= 8 /\ (k = 0 -> ra_ne cx <= 1) /\ (0 < k -> 2 ^ (k - 1) < ra_ne cx) /\ ra_ne cx <= 2 ^ k).
{ assert (Hcases : ra_ne cx <= 1 \/ ra_ne cx = 2 \/ (3 <= ra_ne cx <= 4) \/ (5 <= ra_ne cx <= 8) \/ (9 <= ra_ne cx <= 16) \/
(17 <= ra_ne cx <= 32) \/ (33 <= ra_ne cx <= 64) \/ (65 <= ra_ne cx <= 128) \/ (129 <= ra_ne cx <= 256)) by lia.
destruct Hcases as [Hk | [Hk | [Hk | [Hk | [Hk | [Hk | [Hk | [Hk | Hk]]]]]]]];
[exists 0 | exists 1 | exists 2 | exists 3 | exists 4 | exists 5 | exists 6 | exists 7 | exists 8]; (split; [lia | split; [intros; lia | split; [intros; cbn; lia | cbn; lia]]]). }
destruct Hc8 as (k & Hk & H0 & Hlo & Hhi). rewrite (YI0j.np2_class k (ra_ne cx) ltac:(lia) H0 Hlo Hhi). destruct (Z.ltb_spec k 3); lia. }
remember (Ereg regs2 (ra_extra cx (c_rcur cx) [bb; M'; ra_iclen cx - 1])) as E eqn:HE0.
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs2 rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
pose proof (E_rv regs2 cx (c_rcur cx) [bb; M'; ra_iclen cx - 1]) as HY. rewrite <- HE0 in HY.
pose proof (E_morev regs2 cx (c_rcur cx) [bb; M'; ra_iclen cx - 1] LG) as HMo. rewrite <- HE0 in HMo.
assert (HE2 : bv_unsigned (ew E 2) = c_sp cx) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; lia).
assert (HE8 : ew E 8 = Z_to_bv 64 (c_raw cx)) by (rewrite (HE 8%nat 8%bv eq_refl); exact G8).
assert (HE44 : ew E 44 = Z_to_bv 64 (c_g cx)) by (apply (HY 1%nat); reflexivity).
assert (HE69 : ew E 69 = Z_to_bv 64 bb) by (apply (HMo 0%nat); reflexivity).
assert (HE70 : ew E 70 = Z_to_bv 64 M') by (apply (HMo 1%nat); reflexivity).
assert (HE71 : ew E 71 = Z_to_bv 64 (ra_iclen cx - 1)) by (apply (HMo 2%nat); reflexivity).
assert (HS : st_ok ubs0segs E ssT3 (mkst regs2 (Z_to_bv 64 PC_T3) mem2 (seg_rom ubs0segs))).
{ subst E. unfold ssT3.
apply (ra_st_ok3W cx (c_rcur cx) regs2 [bb; M'; ra_iclen cx - 1] mem2 PC_T3 _ 0 0 true _ _ [] [] Hcx Hobjs G2 G8); rewrite <- ?HE0.
- apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_Ereg | intros X; discriminate X | cbn [sv_denot]; rewrite HE44, unsigned_lit_small, Z.add_0_r by lia; exact G18] | intros X; discriminate X | cbn [sv_denot]; exact G20] | intros X; discriminate X | cbn [sv_denot]; exact G19].
- intros a Ha. lia.
- intros _ a Ha. replace a with (c_raw cx + (a - c_raw cx)) by lia. apply (present_writable ubs0_msyms). apply (proj1 (heap_blocks _ _ LAWS L2 A2 mem2 md2 (c_raw cx) 48 (a - c_raw cx) HH2 Hrawin2 ltac:(lia))).
- reflexivity.
- constructor; [|constructor; [|constructor; [apply (ch7_ok _ _ cx 71 HE71 Ric HFB7) | constructor]]].
+ eapply chunk_ok_val; [cbn [sv_denot]; rewrite HE69, unsigned_lit_small, Z.add_0_r by lia; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact W32].
+ eapply chunk_ok_val; [cbn [sv_denot]; rewrite HE70, unsigned_lit_small, Z.add_0_r by lia; reflexivity | cbn; lia | cbn; lia | exact W40'].
- cbn [atoms_ok]. unfold afact_ok, AC. cbn [af_lo af_hi af_al2]. rewrite HE70, HE69, HE71, !unsigned_lit_small by lia.
change (2 ^ 0) with 1. change (2 ^ 4) with 16. rewrite !Z.mod_1_r. repeat split; first [lia | exact Hbb16].
- constructor.
- constructor. }
change mem2 with (ms_mem (mkst regs2 (Z_to_bv 64 PC_T3) mem2 (seg_rom ubs0segs))) in HJ.
jrun_to LAWS ubs0tbl_ok HS HJ ubs0_A_cgif_writecb.
{ eapply ra_wr_ok3W; [exact HE2 | lia | lia | intros X; lia | right].
split; [rewrite HE8; apply unsigned_lit_small; lia|]. split; [exact Hrawin2|]. split; [lia|]. split; [lia|].
intros a Ha. exists (c_raw cx + 40, c_raw cx + 44). split; [left; reflexivity | cbn; lia]. }
jreg HS (10%bv:reg) as Wa10. jreg HS (11%bv:reg) as Wa11. jreg HS (12%bv:reg) as Wa12. jreg HS (2%bv:reg) as Wa2. jreg HS (4%bv:reg) as Wa4. jreg HS (1%bv:reg) as Wa1.
rewrite HE44 in Wa10. rewrite HE2 in Wa11.
lazymatch goal with |- SR _ (mkCfg ?msx _) _ =>
assert (Wsp : spZ (ms_regs msx) = c_sp cx) by (unfold spZ; rewrite Wa2, <- (Z_to_bv_bv_unsigned 64 (ew E 2)), HE2; apply unsigned_lit_small; lia) end.
lazymatch type of HS with st_ok _ _ _ ?msx =>
assert (MEQ1 : forall a, 0 <= a < 2 ^ 64 -> ~ (c_raw cx + 40 <= a < c_raw cx + 44) -> mbyte ubs0segs (ms_mem msx) a = mbyte ubs0segs mem2 a)
by (intros a Ha Hna; mbyte_chain ltac:(fun H => rewrite ?HE2, ?HE8 in H));
assert (HOG1 : obj_at ubs0segs (ms_mem msx) (c_g cx) LAY_CGIF (c_gvals cx))
by (eapply obj_at_transport_range; [exact (proj2 (proj2 Hobjs)) | exact (proj1 LAY_CGIF_ok) |]; intros i Hi; apply MEQ1; lia);
assert (HSK1 : sink_at ubs0_msyms (ms_mem msx) md2 (c_f cx) (S ++ ra_gce cx ++ ra_hdr cx ++ ra_lctb cx LCTV))
by (apply (sink_at_frame ubs0_msyms mem2 _ md2 (c_f cx)); [| exact HSK]; intros a Ha; destruct (Hsinkaddr a Ha) as [Ha1 Ha2]; apply MEQ1; [exact Ha1 | exact Ha2]);
assert (HG5 : garr8 ubs0segs (ms_mem msx) (c_sp cx + 7) [ra_iclen cx - 1])
by (apply garr8_one; [| exact Ric]; eapply fb_kept1; [exact HFB7 | intros a Ha; cbn in Ha; apply MEQ1; lia])
end.
assert (Lgce : (length (ra_gce cx) <= 8)%nat) by (unfold ra_gce; destruct (_ || _); cbn; lia).
assert (Lhdr : length (ra_hdr cx) = 10%nat) by reflexivity.
assert (Llct : (length (ra_lctb cx LCTV) <= 768)%nat).
{ unfold ra_lctb, YO07.zeros. destruct (negb (c_slct cx =? 0)); [| cbn; lia]. rewrite length_app, length_firstn, repeat_length.
assert (Hp2 : c_slct cx <= 2 ^ YO07.pal_pow (c_slct cx) <= 256).
{ unfold YO07.pal_pow.
assert (Hc8 : exists k, 0 <= k <= 8 /\ (k = 0 -> c_slct cx <= 1) /\ (0 < k -> 2 ^ (k - 1) < c_slct cx) /\ c_slct cx <= 2 ^ k).
{ assert (Hcases : c_slct cx <= 1 \/ c_slct cx = 2 \/ (3 <= c_slct cx <= 4) \/ (5 <= c_slct cx <= 8) \/ (9 <= c_slct cx <= 16) \/
(17 <= c_slct cx <= 32) \/ (33 <= c_slct cx <= 64) \/ (65 <= c_slct cx <= 128) \/ (129 <= c_slct cx <= 256)) by lia.
destruct Hcases as [Hk | [Hk | [Hk | [Hk | [Hk | [Hk | [Hk | [Hk | Hk]]]]]]]];
[exists 0 | exists 1 | exists 2 | exists 3 | exists 4 | exists 5 | exists 6 | exists 7 | exists 8]; (split; [lia | split; [intros; lia | split; [intros; cbn; lia | cbn; lia]]]). }
destruct Hc8 as (k & Hk & H0 & Hlo & Hhi). rewrite (YI0j.np2_class k (c_slct cx) ltac:(lia) H0 Hlo Hhi).
pose proof (Z.pow_le_mono_r 2 k 8 ltac:(lia) ltac:(lia)) as Hk8. change (2 ^ 8) with 256 in Hk8.
assert (Hmx : (Z.max 1 k = 1 /\ k = 0) \/ Z.max 1 k = k) by lia. destruct Hmx as [[Hmx ->] | Hmx]; rewrite Hmx; [change (2 ^ 1) with 2; lia | lia]. }
rewrite Z.mod_small by lia. lia. }
eapply SR_bind.
{ eapply (jwrite ubs0_msyms MR LAWS ubs0_A_cgif_writecb (ubs0_cgif_writecb API IMG FWRITE))
with (g := c_g cx) (gvals := c_gvals cx) (src := c_sp cx + 7) (n := 1) (f := c_f cx) (S := S ++ ra_gce cx ++ ra_hdr cx ++ ra_lctb cx LCTV) (bs := [ra_iclen cx - 1]);
[ exact HS | reflexivity | reflexivity | exact HJ | exact Wa1 | apply ret_ok_even; vm_compute; reflexivity
| exact Wa10 | exact Wa11 | exact Wa12 | rewrite Wsp; exact Hspal | rewrite Wsp; lia | rewrite Wsp; lia | rewrite Wsp; lia
| rewrite Wa4, (HE 4%nat 4%bv eq_refl), G4, Htpv; reflexivity
| exact HOG1 | exact Hwfn | exact Hfile | exact Hgin2 | exact Hfin2 | exact HSK1 | exact HG5 | reflexivity
| lia | lia | lia | rewrite Wsp; lia | rewrite !length_app, Lhdr; unfold c_nP in Hroom; lia | lia | ].
intros a Ha. destruct Ha as (r & Hr & Har). exists r. split; [right; exact Hr | exact Har]. }
cbv beta. intros c' (regsW & memW & mdW & -> & HJW & HPW & Hr10W & HSKW & HhiW & HblkW). rewrite Wsp in HhiW.
jafter_call2 HS 72%nat regsW memW HPW 0 [0%nat; 1%nat] HS2.
match type of HS2 with ?P -> _ => assert (HKP : P); [|specialize (HS2 HKP); clear HKP] end.
{ constructor; [|constructor; [|constructor; [|constructor]]].
- eapply (region_kept_stack ubs0segs _ _ _ 2); [exact HE2 | exact HhiW | lia | lia | lia | cbn; lia | cbn; lia].
- raw_kept HE8 HblkW HJW Hrawin2 cx.
- eapply (region_kept_pointwise ubs0segs _ _ _ 44); [rewrite HE44; apply unsigned_lit_small; lia | | cbn; lia].
cbn [r_lo r_hi]. intros a Ha. replace a with (c_g cx + (a - c_g cx)) by lia. apply (HblkW (c_g cx) CGIF_SIZE (a - c_g cx) Hgin2); [lia|].
replace (c_g cx + (a - c_g cx)) with a by lia. intros (r & [<- | [<- | []]] & Hr); cbn [fst snd sink_token] in Hr; lia. }
clear HS. rename HS2 into HS.
pin_regR HS (10%bv:reg) 0 Hr10W.
lazymatch type of HS with st_ok _ _ _ ?msx => change memW with (ms_mem msx) in HJW end.
assert (KW_stk : forall a, c_sp cx <= a < c_sp cx + 144 -> mbyte ubs0segs memW a = mbyte ubs0segs mem2 a)
by (clear - HhiW MEQ1 Hsplo Hac Hsp47 HWv Hraw1; intros a H1; etransitivity; [apply (proj1 (HhiW a ltac:(lia) ltac:(lia)))|]; apply MEQ1; lia).
assert (KW_blk : forall b n i, In (b, n) (blocks L2 A2) -> b + n <= alloc_ceiling -> 4096 <= b -> (b + n <= c_f cx \/ c_f cx + FILE_BLOCK <= b) ->
(b + n <= c_raw cx \/ c_raw cx + 48 <= b) -> 0 <= i < n ->
mbyte ubs0segs memW (b + i) = mbyte ubs0segs mem2 (b + i))
by (clear - HblkW MEQ1 Hsplo Hac HFBv; intros b n i Hin Hhi Hlo Hsep Hsr Hi; etransitivity; [apply (HblkW b n i Hin Hi); intros (r & [<- | [<- | []]] & Hr); cbn [fst snd sink_token] in Hr; lia|];
apply MEQ1; lia).
assert (KW_raw : forall i, 0 <= i < 40 -> mbyte ubs0segs memW (c_raw cx + i) = mbyte ubs0segs mem2 (c_raw cx + i))
by (clear - HblkW MEQ1 Hraw0 Hraw1 Hrawin2 Hrf HFBv Hac; intros i Hi; etransitivity; [apply (HblkW (c_raw cx) 48 i Hrawin2 ltac:(lia)); intros (r & [<- | [<- | []]] & Hr); cbn [fst snd sink_token] in Hr; lia|];
apply MEQ1; lia).
assert (HOGW : obj_at ubs0segs memW (c_g cx) LAY_CGIF (c_gvals cx))
by (eapply obj_at_transport_range; [exact (proj2 (proj2 Hobjs)) | exact (proj1 LAY_CGIF_ok) |]; intros i Hi; apply (KW_blk _ _ i Hgin2); lia).
jrun_to LAWS ubs0tbl_ok HS HJW ubs0_A_cgif_writecb.
{ eapply wr_ok_cons_win; [reflexivity | ew_havoc; exact HE2 | cbn [r_wlo r_whi]; intros _; lia |].
eapply wr_ok_cons_block; [reflexivity | ew_havoc; rewrite HE8; apply unsigned_lit_small; lia | exact Hrawin2 | cbn [r_wlo]; lia | cbn [r_whi]; lia
| cbn [r_wlo r_whi]; intros a Ha; exists (c_raw cx + 40, c_raw cx + 44); split; [left; reflexivity | cbn; lia] |].
apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
destruct HVOK as (out & Hout & HGout & HMout).
jreg HS (10%bv:reg) as Xa10. jreg HS (11%bv:reg) as Xa11. jreg HS (2%bv:reg) as Xa2. jreg HS (4%bv:reg) as Xa4. jreg HS (1%bv:reg) as Xa1.
pose proof (st_ok_reg _ _ _ _ (12%bv:reg) HS) as Xa12. eval_sr_get_in Xa12. cbn [sv_denot] in Xa12.
rewrite HE44 in Xa10. rewrite ?ew_havoc_old in Xa11 by (cbv; lia). rewrite HE69 in Xa11.
rewrite ?ew_havoc_old in Xa12 by (cbv; lia). rewrite HE70, ?unsigned_lit_small, ?Z.add_0_r in Xa12 by lia.
rewrite ?(Z.mod_small M' (2 ^ 32)) in Xa12 by lia. rewrite HMM in Xa12.
lazymatch goal with |- SR _ (mkCfg ?msx _) _ =>
assert (Xsp : spZ (ms_regs msx) = c_sp cx) by (unfold spZ; rewrite Xa2, <- (Z_to_bv_bv_unsigned 64 (ew E 2)), HE2; apply unsigned_lit_small; lia) end.
lazymatch type of HS with st_ok _ _ _ ?msx =>
assert (MEQ2 : forall a, 0 <= a < 2 ^ 64 -> ~ (c_raw cx + 40 <= a < c_raw cx + 44) -> mbyte ubs0segs (ms_mem msx) a = mbyte ubs0segs memW a)
by (intros a Ha Hna; mbyte_chain ltac:(fun H => rewrite ?HE2, ?HE8 in H));
assert (HOG2 : obj_at ubs0segs (ms_mem msx) (c_g cx) LAY_CGIF (c_gvals cx))
by (eapply obj_at_transport_range; [exact HOGW | exact (proj1 LAY_CGIF_ok) |]; intros i Hi; apply MEQ2; lia);
assert (HSK2 : sink_at ubs0_msyms (ms_mem msx) mdW (c_f cx) ((S ++ ra_gce cx ++ ra_hdr cx ++ ra_lctb cx LCTV) ++ [ra_iclen cx - 1]))
by (apply (sink_at_frame ubs0_msyms memW _ mdW (c_f cx)); [| exact HSKW]; intros a Ha; destruct (Hsinkaddr a Ha) as [Ha1 Ha2]; apply MEQ2; [exact Ha1 | exact Ha2]);
assert (HG6 : garr8 ubs0segs (ms_mem msx) bb out)
by (apply (garr8_frame ubs0segs mem2 _ bb out HGout); intros a Ha; rewrite <- HMout in Ha; rewrite MEQ2 by lia;
replace a with (bb + (a - bb)) by lia; apply (KW_blk _ _ (a - bb) Hbbin); lia)
end.
eapply SR_bind.
{ eapply (jwrite ubs0_msyms MR LAWS ubs0_A_cgif_writecb (ubs0_cgif_writecb API IMG FWRITE))
with (g := c_g cx) (gvals := c_gvals cx) (src := bb) (n := M) (f := c_f cx) (S := (S ++ ra_gce cx ++ ra_hdr cx ++ ra_lctb cx LCTV) ++ [ra_iclen cx - 1]) (bs := out);
[ exact HS | reflexivity | reflexivity | exact HJW | exact Xa1 | apply ret_ok_even; vm_compute; reflexivity
| exact Xa10 | exact Xa11 | exact Xa12 | rewrite Xsp; exact Hspal
| rewrite Xsp; clear - Hspe HSTKv Hsplo Hac HWv; lia | rewrite Xsp; clear - Hspe; lia | rewrite Xsp; clear - Hsp47; lia
| rewrite Xa4, (HE 4%nat 4%bv eq_refl), G4, Htpv; reflexivity
| exact HOG2 | exact Hwfn | exact Hfile | exact Hgin2 | exact Hfin2 | exact HSK2 | exact HG6 | rewrite HMout; reflexivity
| clear - Hbb0; lia | clear - Hbb1 Hac HM; lia | clear - Hbf HM; lia | rewrite Xsp; clear - Hbb1 HM Hac Hsplo HWv; lia
| rewrite !length_app, Lhdr; cbn [length]; unfold c_nP in Hroom, HM2; clear - Hroom HM2 Lgce Llct Hw1 Hh1; lia
| unfold c_nP in HM2; clear - HM2 HnP HnP2 Hw1 Hh1; nia | ].
intros a Ha. destruct Ha as (r & Hr & Har). exists r. split; [right; exact Hr | exact Har]. }
cbv beta. intros c' (regsX & memX & mdX & -> & HJX & HPX & Hr10X & HSKX & HhiX & HblkX). rewrite Xsp in HhiX.
lazymatch type of HS with st_ok _ ?Ec _ _ => lazymatch Ec with havoc _ ?k0 ?l0 => let k := eval vm_compute in (k0 + length l0)%nat in
jafter_call2 HS k regsX memX HPX 0 [0%nat; 1%nat] HS2 end end.
match type of HS2 with ?P -> _ => assert (HKP : P); [|specialize (HS2 HKP); clear HKP] end.
{ constructor; [|constructor; [|constructor; [|constructor]]].
- eapply (region_kept_stack ubs0segs _ _ _ 2); [ew_havoc; exact HE2 | exact HhiX | lia | lia | lia | cbn; lia | cbn; lia].
- raw_kept HE8 HblkX HJX Hrawin2 cx.
- eapply (region_kept_pointwise ubs0segs _ _ _ 44); [ew_havoc; rewrite HE44; apply unsigned_lit_small; lia | | cbn; lia].
cbn [r_lo r_hi]. intros a Ha. replace a with (c_g cx + (a - c_g cx)) by lia. apply (HblkX (c_g cx) CGIF_SIZE (a - c_g cx) Hgin2); [lia|].
replace (c_g cx + (a - c_g cx)) with a by lia. intros (r & [<- | [<- | []]] & Hr); cbn [fst snd sink_token] in Hr; lia. }
clear HS. rename HS2 into HS.
pin_regR HS (10%bv:reg) 0 Hr10X.
lazymatch type of HS with st_ok _ _ _ ?msx => change memX with (ms_mem msx) in HJX end.
assert (KX_stk : forall a, c_sp cx <= a < c_sp cx + 144 -> mbyte ubs0segs memX a = mbyte ubs0segs mem2 a)
by (clear - HhiX MEQ2 KW_stk Hsplo Hac Hsp47 HWv Hraw1; intros a H1; etransitivity; [apply (proj1 (HhiX a ltac:(lia) ltac:(lia)))|]; rewrite MEQ2 by lia; apply KW_stk; lia).
assert (KX_blk : forall b n i, In (b, n) (blocks L2 A2) -> b + n <= alloc_ceiling -> 4096 <= b -> (b + n <= c_f cx \/ c_f cx + FILE_BLOCK <= b) ->
(b + n <= c_raw cx \/ c_raw cx + 48 <= b) -> 0 <= i < n ->
mbyte ubs0segs memX (b + i) = mbyte ubs0segs mem2 (b + i))
by (clear - HblkX MEQ2 KW_blk Hsplo Hac HFBv; intros b n i Hin Hhi Hlo Hsep Hsr Hi; etransitivity; [apply (HblkX b n i Hin Hi); intros (r & [<- | [<- | []]] & Hr); cbn [fst snd sink_token] in Hr; lia|];
rewrite MEQ2 by lia; apply (KW_blk b n i Hin Hhi Hlo Hsep Hsr Hi)).
assert (KX_raw : forall i, 0 <= i < 40 -> mbyte ubs0segs memX (c_raw cx + i) = mbyte ubs0segs mem2 (c_raw cx + i))
by (clear - HblkX MEQ2 KW_raw Hraw0 Hraw1 Hrawin2 Hrf HFBv Hac; intros i Hi; etransitivity; [apply (HblkX (c_raw cx) 48 i Hrawin2 ltac:(lia)); intros (r & [<- | [<- | []]] & Hr); cbn [fst snd sink_token] in Hr; lia|];
rewrite MEQ2 by lia; apply KW_raw; lia).
jrun_to LAWS ubs0tbl_ok HS HJX ubs0_A_free.
{ eapply wr_ok_cons_win; [reflexivity | ew_havoc; exact HE2 | cbn [r_wlo r_whi]; intros _; lia |].
eapply wr_ok_cons_block; [reflexivity | ew_havoc; rewrite HE8; apply unsigned_lit_small; lia | exact Hrawin2 | cbn [r_wlo]; lia | cbn [r_whi]; lia
| cbn [r_wlo r_whi]; intros a Ha; exists (c_raw cx + 40, c_raw cx + 44); split; [left; reflexivity | cbn; lia] |].
apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
jreg HS (10%bv:reg) as K10. rewrite ?ew_havoc_old in K10 by (cbv; lia). rewrite HE69 in K10.
jreg HS (2%bv:reg) as K2. rewrite ?ew_havoc_old in K2 by (cbv; lia). rewrite <- (Z_to_bv_bv_unsigned 64 (ew E 2)), HE2 in K2.
jreg HS (4%bv:reg) as K4. rewrite ?ew_havoc_old in K4 by (cbv; lia). rewrite (HE 4%nat 4%bv eq_refl), G4, Htpv in K4.
jreg HS (1%bv:reg) as K1.
pose proof (regs_kept_of_st_ok _ _ _ _ regs2 _ [2; 3; 4; 8; 27]%bv HS
ltac:(apply env_agree_havoc_ge; [cbv; lia | apply env_agree_havoc_ge; [cbv; lia | rewrite HE0; apply env_agree_refl]]) ltac:(vm_compute; reflexivity)) as HK.
cbn [ms_regs mkst] in HK.
lazymatch type of HS with st_ok _ _ _ ?msx =>
pose proof (st_ok_region_nth _ _ _ 1%nat _ HS eq_refl) as HRr;
assert (Vcur : val_mem ubs0segs (ms_mem msx) (c_raw cx + 40) 4 0);
[ destruct HRr as (_ & _ & _ & Hcs); cbn [r_chunks r_base base_val] in Hcs; rewrite ?ew_havoc_old in Hcs by (cbv; lia); rewrite HE8, unsigned_lit_small in Hcs by lia;
eapply (val_of_chunk_ok ubs0segs _ _ _ 40 4%N (SLit 0)); [eapply (proj1 (Forall_forall _ _) Hcs); cbv; tauto | reflexivity | cbn; lia | cbn; lia]
| ];
rename msx into msA
end.
assert (MEQA : forall a, 0 <= a < 2 ^ 64 -> ~ (c_raw cx + 40 <= a < c_raw cx + 44) -> mbyte ubs0segs (ms_mem msA) a = mbyte ubs0segs memX a).
{ intros a Ha Hn2. mbyte_chain ltac:(fun H => rewrite ?ew_havoc_old in H by (cbv; lia); rewrite ?HE2, ?HE8 in H). }
assert (HORA : obj_at ubs0segs (ms_mem msA) (c_raw cx) LAY_Raw (rvals' cx 0)).
{ eapply obj_at_raw_cur; [exact (proj1 (proj2 Hobjs)) | | exact Vcur | lia]. intros i Hi. rewrite MEQA by lia. apply KX_raw. exact Hi. }
assert (HFSA : frame_savedN ubs0_msyms 12 regs0 (ms_mem msA) (spZ regs0)).
{ eapply (frame_savedN_kept ubs0_msyms 12); [lia | exact HFS|]. intros a Ha. rewrite MEQA by lia. apply KX_stk. lia. }
assert (HSKA : sink_at ubs0_msyms (ms_mem msA) mdX (c_f cx) (((S ++ ra_gce cx ++ ra_hdr cx ++ ra_lctb cx LCTV) ++ [ra_iclen cx - 1]) ++ out)).
{ apply (sink_at_frame ubs0_msyms memX _ mdX (c_f cx)); [| exact HSKX]. intros a Ha. destruct (Hsinkaddr a Ha) as [Ha1 Ha2]. apply MEQA; [exact Ha1 | exact Ha2]. }
eapply SR_bind.
{ eapply (jfree_sink_R) with (a := bb) (n := Lbb) (spc := c_sp cx) (bo := bo);
[ exact HS | reflexivity | reflexivity | exact HJX | exact Hid | exact Hbbin | exact Hbnew | lia | exact Hfin2 | exact Hbf | exact HSKA | exact HRbo
| exact K10 | exact K2 | lia | exact Hspal | lia | lia | exact K4 | exact K1 | apply ret_ok_even; vm_compute; reflexivity ]. }
cbv beta. intros c' (L3 & A3 & regs3 & mem3 & md3 & -> & HJ3 & Hid3 & HP3 & Hrm & Hkeep3 & Hhi3 & HSK3 & Hfin3 & HRo3).
change (ms_segs ubs0_msyms) with ubs0segs in Hkeep3, Hhi3. cbn [ms_regs ms_mem mkst] in HP3, Hkeep3, Hhi3, Hrm, HSK3.
assert (HB3 : Permutation (blocks L3 A3) (blocks L A)) by (eapply perm_after_rm1; [exact HB2 | exact Hrm]).
assert (Hrawin3 : In (c_raw cx, 48) (blocks L3 A3)) by (eapply Permutation_in; [apply Permutation_sym; exact HB3 | rewrite <- HRSv; exact Hrawin]).
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as HH3.
assert (MHI3 : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (c_sp cx - 8192 <= a < c_sp cx) -> mbyte ubs0segs mem3 a = mbyte ubs0segs (ms_mem msA) a).
{ intros a Ha Hna. apply (proj1 (Hhi3 a Ha Hna)). }
assert (HOR3 : obj_at ubs0segs mem3 (c_raw cx) LAY_Raw (rvals' cx 0)).
{ eapply obj_at_transport_range; [exact HORA | exact (proj1 LAY_Raw_ok) |]. intros i Hi. apply (Hkeep3 _ _ i Hrawin3). lia. }
assert (HFS3 : frame_savedN ubs0_msyms 12 regs0 mem3 (spZ regs0)).
{ eapply (frame_savedN_kept ubs0_msyms 12); [lia | exact HFSA|]. intros a Ha. apply MHI3; lia. }
assert (HP3' : forall r : reg, In r [2; 3; 4; 8; 27]%bv -> getr regs3 r = getr regs2 r).
{ intros r Hr. rewrite <- (HK r Hr).
cbv [In] in Hr. destruct Hr as [<-|[<-|[<-|[<-|[<-|[]]]]]];
[exact (HP3 2 ltac:(cbv; lia)) | exact (HP3 3 ltac:(cbv; lia)) | exact (HP3 4 ltac:(cbv; lia)) | exact (HP3 8 ltac:(cbv; lia))
| exact (HP3 27 ltac:(unfold callee_saved; lia))]. }
clear HS.
remember (Ereg regs3 (map (Z_to_bv 64) (rvals' cx 0) ++ [])) as E3 eqn:HE3.
assert (X8 : ew E3 8 = Z_to_bv 64 (c_raw cx)) by (subst E3; rewrite (ew_Ereg_nat regs3 _ 8 8%bv) by reflexivity; rewrite HP3' by (cbv; tauto); exact G8).
assert (X40 : ew E3 40 = Z_to_bv 64 0) by (subst E3; apply (Ereg_vals regs3 (rvals' cx 0) [] 8%nat 0); reflexivity).
assert (HS : st_ok ubs0segs E3 (mkSS (RA0 + 0x5c4) sr_atoms [YP09.mkRegion (Some 8%nat) 0 RAW_SIZE 0 0 (obj_chunks_gen LAY_Raw 32 lits_Raw)] None
(mkFacts [(8%nat, mkAF 4096 (CEIL_MAX - 48) 4)] [] []))
(mkst regs3 (Z_to_bv 64 (RA0 + 0x5c4)) mem3 (seg_rom ubs0segs))).
{ subst E3. apply entry_st_ok.
- reflexivity.
- constructor; [|constructor].
eapply (region_ok_obj_gen ubs0segs _ mem3 8 (c_raw cx)); [rewrite X8; apply unsigned_lit_small; lia | lia | lia | exact HOR3 | reflexivity | | apply lits_Raw_ok; reflexivity | intros i Hi; lia].
intros jj v Hj. apply Ereg_vals. exact Hj.
- cbn. repeat split.
- cbn [atoms_ok]. unfold afact_ok, AC. cbn [af_lo af_hi af_al2]. rewrite X8, unsigned_lit_small by lia.
change (2 ^ 4) with 16. repeat split; first [lia | exact Hraw16]. }
change mem3 with (ms_mem (mkst regs3 (Z_to_bv 64 (RA0 + 0x5c4)) mem3 (seg_rom ubs0segs))) in HJ3.
jrun_to LAWS ubs0tbl_ok HS HJ3 PC_RET; [apply wr_ok_cons_ro; [cbn; lia | apply wr_ok_nil]|].
pose proof (regs_kept_of_st_ok _ _ _ _ regs3 _ [2; 3; 4; 27]%bv HS ltac:(rewrite HE3; apply env_agree_refl) ltac:(vm_compute; reflexivity)) as HK3.
lazymatch type of HS with st_ok _ _ _ ?msf => rename msf into msF end.
assert (MEQ3 : forall a, 0 <= a < 2 ^ 64 -> mbyte ubs0segs (ms_mem msF) a = mbyte ubs0segs mem3 a).
{ intros a Ha. apply mbyte_eq_of1'. lazymatch goal with HF : frame_of _ _ _ _ |- _ => exact (frame_of_ro' _ _ _ _ HF ltac:(vm_compute; reflexivity) _) end. }
jreg HS (18%bv:reg) as Q18. rewrite X40 in Q18.
rewrite (st_ok_mkst _ _ _ _ HS eq_refl). cbn [ss_pc].
eapply (ra_ret4_R API IMG _ _ (fun s => res_ok s (rawadd_rb b)) cx L A mem md L3 A3 md3 regs0 (ms_regs msF) (ms_mem msF) 0 (getr (ms_regs msF) 18));
[ exact (proj1 Hcx) | exact HO | exact HJ3 | exact Hid3 | exact (HRimp _ HRo3) | exact HB3 | | | | | | | reflexivity | ]; cbn [ms_regs ms_mem].
- eapply obj_at_transport_range; [exact HOR3 | exact (proj1 LAY_Raw_ok) |]. intros i Hi. apply MEQ3. lia.
- eapply (frame_savedN_kept ubs0_msyms 12); [lia | exact HFS3|]. intros a Ha. apply MEQ3; lia.
- rewrite HK3 by (cbv; tauto). rewrite HP3' by (cbv; tauto). exact G2.
- rewrite HK3 by (cbv; tauto). rewrite HP3' by (cbv; tauto). rewrite G3, Hgp0. reflexivity.
- rewrite HK3 by (cbv; tauto). rewrite HP3' by (cbv; tauto). rewrite G4, Htp0. reflexivity.
- rewrite HK3 by (cbv; tauto). rewrite HP3' by (cbv; tauto). rewrite G27, H27o. reflexivity.
-
intros m' Hm'. cbn [ms_regs] in Q18. split; [| split; [reflexivity|]].
+ first [rewrite Q18; vm_compute; reflexivity | rewrite Q18; reflexivity].
+ exists out. split; [exact Hout|]. split; [| rewrite <- HMout; exact HM2]. rewrite <- !app_assoc in HSK3. cbn [app] in HSK3.
apply (sink_at_frame ubs0_msyms mem3 _ md3 (c_f cx)); [| exact HSK3].
intros a Ha. assert (Ha' : 0 <= a < alloc_ceiling) by (destruct Ha as [Ha|Ha]; [lia | pose proof (ubs0_env_addr_range a Ha); lia]). rewrite Hm' by lia. apply MEQ3. lia.
Qed.
End S.
End c.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
