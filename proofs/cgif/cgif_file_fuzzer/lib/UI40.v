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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YI14 YI13 YI00 YI02 UI5c UI2z YI0j YI0k YI6c YI01 YI0g.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YO07.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UI3w UI4j UI4h UI4d UI42.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI5a YI2w UI2v UI3x.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition ssLX (pc : Z) : sstate :=
ra_ssW pc sr_atoms 0 0 [] false [(10%nat, mkAF 1 65535 0); (12%nat, mkAF 1 65535 0)] [] [].
Section S.
Variable API : AllocAPI ubs0_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs0_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs0_msyms MR.
Variables (IMGV LCTV : list Z).
Definition at_LX (pc : Z) (cx : ra_cx) L A mem md (regs0 : bvmap 5 word) (p icl idl R : Z) (PFX : list Z) (b : rbound) (c' : config) : Prop :=
exists L2 A2 regs2 mem2 md2 (pint : Z),
c' = mkCfg (mkst regs2 (Z_to_bv 64 pc) mem2 (seg_rom ubs0segs)) md2 /\
journal ubs0_msyms MR RAWADD_STK (spZ regs0) [(c_raw cx + 40, c_raw cx + 44)] L A mem md L2 A2 mem2 md2 /\
st_init_done A2 = true /\   res_ok A2 (rb_acc b 1 (prN (c_nP cx))) /\
Permutation (blocks L2 A2) ((pint, c_nP cx) :: blocks L A) /\
wtok' RAWADD_STK (spZ regs0) [(c_raw cx + 40, c_raw cx + 44)] (blocks L A) (pint, c_nP cx) /\ pint <> 0 /\
ra_regs regs2 cx /\ getr regs2 23 = Z_to_bv 64 (c_slct cx) /\ getr regs2 24 = Z_to_bv 64 p /\ getr regs2 22 = Z_to_bv 64 (c_cfp cx + 30) /\
getr regs2 18 = Z_to_bv 64 icl /\ getr regs2 25 = Z_to_bv 64 idl /\
getr regs2 19 = Z_to_bv 64 pint /\ getr regs2 20 = Z_to_bv 64 (pint + c_w cx * R) /\ getr regs2 21 = Z_to_bv 64 (pint + c_w cx * R) /\
getr regs2 10 = Z_to_bv 64 (c_h cx) /\ getr regs2 12 = Z_to_bv 64 (c_w cx) /\
objs_at mem2 cx (c_rcur cx) /\ frame_savedN ubs0_msyms 12 regs0 mem2 (spZ regs0) /\
garr8 ubs0segs mem2 pint PFX /\ Z.of_nat (length PFX) = c_w cx * R /\ garr8 ubs0segs mem2 (c_img cx) IMGV /\ fbC mem2 cx.
Lemma pint_seps : forall cx L A L2 A2 mem2 md2 pint,
rcx_ok cx -> Permutation (blocks L A) (c_blocks cx) -> heap_ok MR L2 A2 mem2 md2 ->
Permutation (blocks L2 A2) ((pint, c_nP cx) :: blocks L A) ->
(4096 <= pint /\ pint + c_nP cx <= alloc_ceiling /\ pint mod 16 = 0) /\
(c_raw cx + 48 <= pint \/ pint + c_nP cx <= c_raw cx) /\
(c_g cx + 96 <= pint \/ pint + c_nP cx <= c_g cx) /\
(c_img cx + c_Nimg cx <= pint \/ pint + c_nP cx <= c_img cx).
Proof using LAWS.
intros cx L A L2 A2 mem2 md2 pint Hcx HB HH HB2.
pose proof Hcx as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hw1 & Hh1 & HnP & _) & _).
assert (HP : Permutation (blocks L2 A2) ((pint, c_nP cx) :: c_blocks cx)).
{ eapply Permutation_trans; [exact HB2|]. apply perm_skip. exact HB. }
split; [|split; [|split]].
- apply (heap_blocks_range _ _ LAWS L2 A2 mem2 md2 pint (c_nP cx) HH). { eapply Permutation_in; [apply Permutation_sym; exact HP | left; reflexivity]. } unfold c_nP; nia.
- pose proof (heap_sep_perm _ _ LAWS L2 A2 mem2 md2 (pint, c_nP cx) _ (c_raw cx, RAW_SIZE) HH HP ltac:(left; reflexivity)) as X. cbn [fst snd] in X. unfold RAW_SIZE in X. lia.
- pose proof (heap_sep_perm _ _ LAWS L2 A2 mem2 md2 (pint, c_nP cx) _ (c_g cx, CGIF_SIZE) HH HP ltac:(right; left; reflexivity)) as X. cbn [fst snd] in X. unfold CGIF_SIZE in X. lia.
- pose proof (heap_sep_perm _ _ LAWS L2 A2 mem2 md2 (pint, c_nP cx) _ (c_img cx, c_Nimg cx) HH HP ltac:(right; right; left; reflexivity)) as X. cbn [fst snd] in X. lia.
Qed.
Lemma after_loop_mem : forall cx (memc mem' : word -> option byte) pint cur regs0 R PFX,
rcx_ok cx -> 4096 <= pint -> pint + c_nP cx <= alloc_ceiling ->
(c_raw cx + 48 <= pint \/ pint + c_nP cx <= c_raw cx) -> (c_g cx + 96 <= pint \/ pint + c_nP cx <= c_g cx) ->
(c_img cx + c_Nimg cx <= pint \/ pint + c_nP cx <= c_img cx) ->
(forall x : word, bv_unsigned x < pint + c_w cx * R \/ pint + c_nP cx <= bv_unsigned x -> mem' x = memc x) -> 0 <= c_w cx * R <= c_nP cx ->
spZ regs0 = c_sp cx + 144 ->
objs_at memc cx cur -> frame_savedN ubs0_msyms 12 regs0 memc (spZ regs0) ->
garr8 ubs0segs memc pint PFX -> Z.of_nat (length PFX) = c_w cx * R -> garr8 ubs0segs memc (c_img cx) IMGV -> Z.of_nat (length IMGV) = c_nP cx -> fbC memc cx ->
objs_at mem' cx cur /\ frame_savedN ubs0_msyms 12 regs0 mem' (spZ regs0) /\ garr8 ubs0segs mem' pint PFX /\ garr8 ubs0segs mem' (c_img cx) IMGV /\ fbC mem' cx.
Proof using.
intros cx memc mem' pint cur regs0 R PFX Hcx Hp0 Hp1 Hsr Hsg Hsi Hout HR Hspe Hobjs HFS HGP HLP HGI HLI HFBC.
pose proof (proj1 alloc_ceiling_val) as Hac.
pose proof Hcx as ((Hspal & Hsplo & Hcfplo & Hcfphi & Hcfpal & Hraw0 & Hraw1 & Hraw16 & Hg0 & Hg1 & Hg16 & Himg0 & Himg1 & Himg16 &
Hs1 & Hs2 & Hs3 & Hw1 & Hh1 & HnP & HnP2 & Hsgct & Hwfn & Hfile & Htpv & Hf0 & Hf1 & Hfin & Hsp47) & Hslct).
assert (MEQ : forall a, 0 <= a < 2 ^ 64 -> (a < pint + c_w cx * R \/ pint + c_nP cx <= a) -> mbyte ubs0segs mem' a = mbyte ubs0segs memc a).
{ intros a Ha Hd. apply mbyte_eq_of1'. apply Hout. rewrite unsigned_lit_small by lia. lia. }
split; [|split; [|split; [|split]]].
- eapply objs_at_kept; [exact Hobjs | | |]; intros i Hi; apply MEQ; lia.
- eapply (frame_savedN_kept ubs0_msyms 12); [lia | exact HFS|]. intros a Ha. apply MEQ; lia.
- apply (garr8_frame ubs0segs memc mem' pint PFX HGP). rewrite HLP. intros a Ha. apply MEQ; lia.
- apply (garr8_frame ubs0segs memc mem' (c_img cx) IMGV HGI). rewrite HLI. unfold c_nP. intros a Ha. apply MEQ; [lia|]. unfold c_nP in *. nia.
- eapply fbC_kept; [exact HFBC | |]; intros a Ha; apply MEQ; lia.
Qed.
Lemma img_now : forall cx L A mem md L2 A2 mem2 md2 (regs0 : bvmap 5 word) pint,
rcx_ok cx -> Permutation (blocks L A) (c_blocks cx) ->
journal ubs0_msyms MR RAWADD_STK (spZ regs0) [(c_raw cx + 40, c_raw cx + 44)] L A mem md L2 A2 mem2 md2 ->
Permutation (blocks L2 A2) ((pint, c_nP cx) :: blocks L A) ->
garr8 ubs0segs mem (c_img cx) IMGV -> Z.of_nat (length IMGV) = c_nP cx -> garr8 ubs0segs mem2 (c_img cx) IMGV.
Proof using LAWS.
intros cx L A mem md L2 A2 mem2 md2 regs0 pint Hcx HB HJ HB2 HG HL.
pose proof Hcx as ((Hspal & Hsplo & Hcfplo & Hcfphi & Hcfpal & Hraw0 & Hraw1 & Hraw16 & Hg0 & Hg1 & Hg16 & Himg0 & Himg1 & Himg16 &
Hs1 & Hs2 & Hs3 & Hw1 & Hh1 & HnP & HnP2 & Hsgct & Hwfn & Hfile & Htpv & Hf0 & Hf1 & Hfin & Hsp47) & Hslct).
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HH2. pose proof HJ as (_ & _ & _ & Hkeep & _).
assert (Himgin : In (c_img cx, c_Nimg cx) (blocks L A)) by (eapply blocks_perm_in; [exact HB | right; right; left; reflexivity]).
assert (Himgin2 : In (c_img cx, c_Nimg cx) (blocks L2 A2)) by (eapply Permutation_in; [apply Permutation_sym; exact HB2 | right; exact Himgin]).
assert (HP : Permutation (blocks L2 A2) ((c_raw cx, RAW_SIZE) :: (pint, c_nP cx) :: (c_g cx, CGIF_SIZE) :: (c_img cx, c_Nimg cx) :: c_rest cx)).
{ eapply Permutation_trans; [exact HB2|]. eapply Permutation_trans; [apply perm_skip; exact HB | apply perm_swap]. }
pose proof (heap_sep_perm _ _ LAWS L2 A2 mem2 md2 (c_raw cx, RAW_SIZE) _ (c_img cx, c_Nimg cx) HH2 HP ltac:(right; right; left; reflexivity)) as Hsep. cbn [fst snd] in Hsep. unfold RAW_SIZE in Hsep.
apply (garr8_frame ubs0segs mem mem2 (c_img cx) IMGV HG). rewrite HL. unfold c_nP. intros a Ha.
replace a with (c_img cx + (a - c_img cx)) by lia. apply (Hkeep (c_img cx) (c_Nimg cx) (a - c_img cx) Himgin Himgin2); [nia|].
intros (r & [<- | []] & Hr); cbn [fst snd] in Hr; lia.
Qed.
Lemma ra_W1 : forall cx L A mem md regs0 p icl idl b c1,
rcx_ok cx -> ra_origin cx regs0 -> Permutation (blocks L A) (c_blocks cx) ->
garr8 ubs0segs mem (c_img cx) IMGV -> Z.of_nat (length IMGV) = c_nP cx ->
at_L1 API cx L A mem md regs0 p icl idl b c1 ->
SR ubs0segs c1 (fun c' => exists m1, 1 <= m1 /\ 8 * (m1 - 1) < c_h cx <= 8 * m1 /\
at_LX PC_L1X cx L A mem md regs0 p icl idl m1 (ipassZ IMGV (c_w cx) 0 8 m1) b c').
Proof using IMG.
intros cx L A mem md regs0 p icl idl b c1 Hcx HO HB HIMG0 HIMGlen
(L2 & A2 & regs2 & mem2 & md2 & pint & -> & HJ2 & Hid2 & HRq2 & HB2 & Hwt & Hpnz & HR & G23 & G24 & G22 & G18 & G25 & G19 & G20 & G26 & G12 & Hobjs & HFS & HFBC).
pose proof (proj1 alloc_ceiling_val) as Hac.
pose proof HO as (Hspe & Htp0 & Hgp0 & Hra0 & Hgp & H25o & H26o & H27o).
pose proof Hcx as ((Hspal & Hsplo & Hcfplo & Hcfphi & Hcfpal & Hraw0 & Hraw1 & Hraw16 & Hg0 & Hg1 & Hg16 & Himg0 & Himg1 & Himg16 &
Hs1 & Hs2 & Hs3 & Hw1 & Hh1 & HnP & HnP2 & Hsgct & Hwfn & Hfile & Htpv & Hf0 & Hf1 & Hfin & Hsp47) & Hslct).
pose proof (objs_fields_ok _ _ _ Hobjs) as (F0 & F1 & F2 & F3 & F4 & _).
pose proof HR as (R2 & R8 & R9 & R4 & R3 & R27).
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HH2.
destruct (pint_seps cx L A L2 A2 mem2 md2 pint Hcx HB HH2 HB2) as ((Hp0 & Hp1 & Hp16) & Hsr & Hsg & Hsi).
assert (Hsi' : pint + c_nP cx <= c_img cx \/ c_img cx + c_Nimg cx <= pint) by (clear - Hsi; lia).
apply hideR_i in Hsr. apply hideR_i in Hsg. apply hideR_i in Hsi. apply hideR_i in Hsi'.
assert (Hpin : In (pint, c_nP cx) (blocks L2 A2)) by (eapply Permutation_in; [apply Permutation_sym; exact HB2 | left; reflexivity]).
assert (Himgin : In (c_img cx, c_Nimg cx) (blocks L2 A2)).
{ eapply Permutation_in; [apply Permutation_sym; exact HB2 | right]. eapply blocks_perm_in; [exact HB | right; right; left; reflexivity]. }
assert (HnPe : c_nP cx = c_w cx * c_h cx) by reflexivity.
eapply SR_mono.
{ eapply (il_loop1 API IMG (Z.to_nat (c_h cx)) 0 0 regs2 mem2 RAWADD_STK (spZ regs0) _ L A mem md L2 A2 md2 pint (c_nP cx) (c_img cx) (c_Nimg cx) (c_w cx) (c_h cx) (c_cfp cx) (cvals cx));
[ lia | lia | lia | intros j Hj Hjh; lia | lia | lia | lia | lia | exact HJ2 | exact Hpin | exact Hwt | exact Himgin | exact (hideR_e _ Hsi')
| exact (proj1 Hobjs) | reflexivity | reflexivity | reflexivity | lia | lia | exact Hcfpal | exact R9
| rewrite G20; f_equal; lia | exact G26 | exact G12 ]. }
cbv beta. intros c' (regs' & mem' & m & -> & HJ' & Hm1 & Hm2 & Hm3 & P20 & P21 & P10 & P12 & HKf & Hout & Hgr & Hcp).
rewrite <- HnPe in Hout.
pose proof (img_now cx L A mem md L2 A2 mem2 md2 regs0 pint Hcx HB HJ2 HB2 HIMG0 HIMGlen) as HIMG2.
destruct (after_loop_mem cx mem2 mem' pint (c_rcur cx) regs0 0 [] Hcx Hp0 Hp1 (hideR_e _ Hsr) (hideR_e _ Hsg) (hideR_e _ Hsi) Hout ltac:(unfold c_nP; nia) Hspe Hobjs HFS
(garr8_nil ubs0segs mem2 pint) ltac:(cbn; lia) HIMG2 HIMGlen HFBC) as (Hobjs' & HFS' & _ & HIMG' & HFBC').
pose proof (garr8_ipass ubs0segs mem2 mem' (c_img cx) pint IMGV (c_w cx) (c_h cx) 0 8 m 0 HIMG2 HIMGlen ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros; lia) Hcp) as HGP.
rewrite Z.mul_0_r, Z.add_0_r in HGP.
exists m. split; [lia|]. split; [lia|].
exists L2, A2, regs', mem', md2, pint. split; [reflexivity|]. split; [exact HJ'|]. split; [exact Hid2|]. split; [exact HRq2|].
split; [exact HB2|]. split; [exact Hwt|]. split; [exact Hpnz|].
split; [unfold ra_regs in *; rewrite !HKf by (cbv; tauto); exact HR|].
split; [rewrite HKf by (cbv; tauto); exact G23|]. split; [rewrite HKf by (cbv; tauto); exact G24|]. split; [rewrite HKf by (cbv; tauto); exact G22|].
split; [rewrite HKf by (cbv; tauto); exact G18|]. split; [rewrite HKf by (cbv; tauto); exact G25|].
split; [rewrite HKf by (cbv; tauto); exact G19|].
split; [rewrite P20; f_equal; lia|]. split; [rewrite P21; f_equal; lia|]. split; [exact P10|]. split; [exact P12|].
split; [exact Hobjs'|]. split; [exact HFS'|]. split; [exact HGP|].
split; [rewrite (ipassZ_length IMGV (c_w cx) (c_h cx) 0 8 m HIMGlen) by (first [lia | intros; lia]); lia|].
split; [exact HIMG' | exact HFBC'].
Qed.
Ltac wr2 HE2 := eapply ra_wr_okW; [exact HE2 | lia | lia | intros X; lia | left; cbn; lia].
Lemma ra_W2 : forall cx L A mem md regs0 p icl idl R b c1,
rcx_ok cx -> ra_origin cx regs0 -> Permutation (blocks L A) (c_blocks cx) ->
0 <= R -> c_w cx * R <= c_nP cx -> (forall j, 0 <= j -> 4 + 8 * j < c_h cx -> R + j + 1 <= c_h cx) ->
forall PFX, Z.of_nat (length IMGV) = c_nP cx ->
at_LX PC_L1X cx L A mem md regs0 p icl idl R PFX b c1 ->
SR ubs0segs c1 (fun c' => exists m, ((5 <= c_h cx /\ 1 <= m /\ 4 + 8 * (m - 1) < c_h cx <= 4 + 8 * m) \/ (c_h cx < 5 /\ m = 0)) /\
at_LX PC_L2X cx L A mem md regs0 p icl idl (R + m) (PFX ++ ipassZ IMGV (c_w cx) 4 8 m) b c').
Proof using IMG.
intros cx L A mem md regs0 p icl idl R b c1 Hcx HO HB HR0 HRn Hrows PFX HIMGlen
(L2 & A2 & regs2 & mem2 & md2 & pint & -> & HJ2 & Hid2 & HRq2 & HB2 & Hwt & Hpnz & HR & G23 & G24 & G22 & G18 & G25 & G19 & G20 & G21 & G10 & G12 & Hobjs & HFS & HGP & HLP & HIMG2 & HFBC).
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HSTKv : RAWADD_STK = 8704) by reflexivity.
pose proof HO as (Hspe & Htp0 & Hgp0 & Hra0 & Hgp & H25o & H26o & H27o).
pose proof Hcx as ((Hspal & Hsplo & Hcfplo & Hcfphi & Hcfpal & Hraw0 & Hraw1 & Hraw16 & Hg0 & Hg1 & Hg16 & Himg0 & Himg1 & Himg16 &
Hs1 & Hs2 & Hs3 & Hw1 & Hh1 & HnP & HnP2 & Hsgct & Hwfn & Hfile & Htpv & Hf0 & Hf1 & Hfin & Hsp47) & Hslct).
pose proof (objs_fields_ok _ _ _ Hobjs) as (F0 & F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & G1' & G2' & G3' & G4' & G5' & G6' & G7' & G8' & LG).
pose proof HR as (R2 & R8 & R9 & R4 & R3 & R27).
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HH2.
pose proof HJ2 as (_ & _ & _ & _ & _ & (Hsp0al & Hstk0 & Hceil & Hsp063 & Hstw) & _). cbn beta in Hstw.
destruct (pint_seps cx L A L2 A2 mem2 md2 pint Hcx HB HH2 HB2) as ((Hp0 & Hp1 & Hp16) & Hsr & Hsg & Hsi).
assert (Hsi' : pint + c_nP cx <= c_img cx \/ c_img cx + c_Nimg cx <= pint) by (clear - Hsi; lia).
apply hideR_i in Hsr. apply hideR_i in Hsg. apply hideR_i in Hsi. apply hideR_i in Hsi'.
assert (Hpin : In (pint, c_nP cx) (blocks L2 A2)) by (eapply Permutation_in; [apply Permutation_sym; exact HB2 | left; reflexivity]).
assert (Himgin : In (c_img cx, c_Nimg cx) (blocks L2 A2)).
{ eapply Permutation_in; [apply Permutation_sym; exact HB2 | right]. eapply blocks_perm_in; [exact HB | right; right; left; reflexivity]. }
assert (HnPlo : 1 <= c_nP cx) by (unfold c_nP; nia). assert (HnPe : c_nP cx = c_w cx * c_h cx) by reflexivity.
remember (Ereg regs2 (ra_extra cx (c_rcur cx) [])) as E eqn:HE0.
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs2 rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HE2 : bv_unsigned (ew E 2) = c_sp cx) by (rewrite (HE 2%nat 2%bv eq_refl), R2; apply unsigned_lit_small; lia).
assert (HE10 : ew E 10 = Z_to_bv 64 (c_h cx)) by (rewrite (HE 10%nat 10%bv eq_refl); exact G10).
assert (HE12 : ew E 12 = Z_to_bv 64 (c_w cx)) by (rewrite (HE 12%nat 12%bv eq_refl); exact G12).
assert (HE21 : ew E 21 = Z_to_bv 64 (pint + c_w cx * R)) by (rewrite (HE 21%nat 21%bv eq_refl); exact G21).
assert (HE20 : ew E 20 = Z_to_bv 64 (pint + c_w cx * R)) by (rewrite (HE 20%nat 20%bv eq_refl); exact G20).
pose proof (E_cv regs2 cx (c_rcur cx) []) as HX. rewrite <- HE0 in HX.
assert (HE35 : ew E 35 = Z_to_bv 64 (c_w cx)) by (apply (HX 3%nat); reflexivity).
assert (HS : st_ok ubs0segs E (ssLX PC_L1X) (mkst regs2 (Z_to_bv 64 PC_L1X) mem2 (seg_rom ubs0segs))).
{ subst E. unfold ssLX.
apply (ra_st_okW cx (c_rcur cx) regs2 [] mem2 PC_L1X _ 0 0 false _ _ [] [] Hcx Hobjs HR); rewrite <- ?HE0.
- apply regs_ok_Ereg.
- intros a Ha. apply Hstw. lia.
- intros X. discriminate X.
- reflexivity.
- constructor.
- cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HE10, HE12, !unsigned_lit_small by lia.
change (2 ^ 0) with 1. rewrite !Z.mod_1_r. repeat split; lia.
- constructor.
- constructor. }
change mem2 with (ms_mem (mkst regs2 (Z_to_bv 64 PC_L1X) mem2 (seg_rom ubs0segs))) in HJ2.
jrun_to LAWS ubs0tbl_ok HS HJ2 PC_L2; [wr2 HE2|].
jbranch ubs0tbl HS.
-
rewrite branch_ltu_U, (U_atom _ 10 _ HE10), U_lit in Hc by lia.
assert (Hh5 : c_h cx < 5) by (destruct (Z.ltb_spec (c_h cx) 5); [lia | discriminate]). clear Hc.
jrun_to LAWS ubs0tbl_ok HS HJ2 PC_L2X; [wr2 HE2|].
pose proof (regs_kept_of_st_ok _ _ _ _ regs2 _ [2; 3; 4; 8; 9; 10; 12; 18; 19; 21; 22; 23; 24; 25; 27]%bv HS ltac:(rewrite HE0; apply env_agree_refl) ltac:(vm_compute; reflexivity)) as HK.
jreg HS (20%bv:reg) as Q20.
lazymatch type of HS with st_ok _ _ _ ?msf => rename msf into msF end.
rewrite (st_ok_mkst _ _ _ _ HS eq_refl). cbn [ss_pc]. apply SR_ret.
exists 0. split; [right; lia|].
exists L2, A2, (ms_regs msF), (ms_mem msF), md2, pint. split; [reflexivity|]. split; [exact HJ2|]. split; [exact Hid2|]. split; [exact HRq2|].
split; [exact HB2|]. split; [exact Hwt|]. split; [exact Hpnz|].
split; [unfold ra_regs in *; rewrite !HK by (cbv; tauto); exact HR|].
split; [rewrite HK by (cbv; tauto); exact G23|]. split; [rewrite HK by (cbv; tauto); exact G24|]. split; [rewrite HK by (cbv; tauto); exact G22|].
split; [rewrite HK by (cbv; tauto); exact G18|]. split; [rewrite HK by (cbv; tauto); exact G25|].
split; [rewrite HK by (cbv; tauto); exact G19|].
split; [rewrite Q20; cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned, HE21; f_equal; lia|].
split; [rewrite HK by (cbv; tauto); rewrite G21; f_equal; lia|].
split; [rewrite HK by (cbv; tauto); exact G10|]. split; [rewrite HK by (cbv; tauto); exact G12|].
assert (MEQs : forall a, 0 <= a < 2 ^ 64 -> mbyte ubs0segs (ms_mem msF) a = mbyte ubs0segs mem2 a) by (intros a Ha; mbyte_chain ltac:(fun H => rewrite ?HE2 in H)).
split; [eapply objs_at_kept; [exact Hobjs | | |]; intros i Hi; apply MEQs; lia|].
split; [eapply (frame_savedN_kept ubs0_msyms 12); [lia | exact HFS|]; intros a Ha; apply MEQs; lia|].
rewrite app_nil_r, Z.add_0_r.
split; [apply (garr8_frame ubs0segs mem2 _ pint PFX HGP); intros a Ha; apply MEQs; lia|]. split; [exact HLP|].
split; [apply (garr8_frame ubs0segs mem2 _ (c_img cx) IMGV HIMG2); intros a Ha; apply MEQs; unfold c_nP in *; lia | eapply fbC_kept; [exact HFBC | |]; intros a Ha; apply MEQs; lia].
-
rewrite branch_ltu_U, (U_atom _ 10 _ HE10), U_lit in Hc by lia.
assert (Hh5 : 5 <= c_h cx) by (destruct (Z.ltb_spec (c_h cx) 5); [discriminate | lia]). clear Hc.
jrun_to LAWS ubs0tbl_ok HS HJ2 PC_L2; [wr2 HE2|].
pose proof (regs_kept_of_st_ok _ _ _ _ regs2 _ [2; 3; 4; 8; 9; 10; 18; 19; 20; 21; 22; 23; 24; 25; 27]%bv HS ltac:(rewrite HE0; apply env_agree_refl) ltac:(vm_compute; reflexivity)) as HK.
jreg HS (26%bv:reg) as Q26. cbn [ms_regs mkst] in Q26.
jreg HS (12%bv:reg) as Q12. cbn [ms_regs mkst] in Q12.
lazymatch type of HS with st_ok _ _ _ ?msf => rename msf into msF end.
assert (Hobjs' : objs_at (ms_mem msF) cx (c_rcur cx)).
{ eapply objs_at_kept; [exact Hobjs | | |]; intros i Hi; mbyte_chain ltac:(fun H => rewrite ?HE2 in H). }
assert (HFS' : frame_savedN ubs0_msyms 12 regs0 (ms_mem msF) (spZ regs0)).
{ eapply (frame_savedN_kept ubs0_msyms 12); [lia | exact HFS|]; intros a Ha; mbyte_chain ltac:(fun H => rewrite ?HE2 in H). }
assert (MEQs : forall a, 0 <= a < 2 ^ 64 -> mbyte ubs0segs (ms_mem msF) a = mbyte ubs0segs mem2 a) by (intros a Ha; mbyte_chain ltac:(fun H => rewrite ?HE2 in H)).
assert (HGP' : garr8 ubs0segs (ms_mem msF) pint PFX) by (apply (garr8_frame ubs0segs mem2 _ pint PFX HGP); intros a Ha; apply MEQs; lia).
assert (HIMG' : garr8 ubs0segs (ms_mem msF) (c_img cx) IMGV) by (apply (garr8_frame ubs0segs mem2 _ (c_img cx) IMGV HIMG2); intros a Ha; apply MEQs; unfold c_nP in *; lia).
assert (HFBC' : fbC (ms_mem msF) cx) by (eapply fbC_kept; [exact HFBC | |]; intros a Ha; apply MEQs; lia).
rewrite (st_ok_mkst _ _ _ _ HS eq_refl). cbn [ss_pc].
eapply SR_mono.
{ eapply (il_loop2 API IMG (Z.to_nat (c_h cx)) 4 R (ms_regs msF) (ms_mem msF) RAWADD_STK (spZ regs0) _ L A mem md L2 A2 md2 pint (c_nP cx) (c_img cx) (c_Nimg cx) (c_w cx) (c_h cx) (c_cfp cx) (cvals cx));
cbn [ms_regs ms_mem];
[ lia | lia | lia | exact Hrows | lia | lia | lia | lia | exact HJ2 | exact Hpin | exact Hwt | exact Himgin | exact (hideR_e _ Hsi')
| exact (proj1 Hobjs') | reflexivity | reflexivity | reflexivity | lia | lia | exact Hcfpal | rewrite HK by (cbv; tauto); exact R9
| rewrite HK by (cbv; tauto); exact G21 | exact Q26 | first [exact Q12 | rewrite Q12; cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; exact HE35] ]. }
cbv beta. intros c' (regs' & mem' & m & -> & HJ' & Hm1 & Hm2 & Hm3 & P21 & P20 & P10 & P12 & HKf & Hout & Hgr & Hcp).
rewrite <- HnPe in Hout.
destruct (after_loop_mem cx (ms_mem msF) mem' pint (c_rcur cx) regs0 R PFX Hcx Hp0 Hp1 (hideR_e _ Hsr) (hideR_e _ Hsg) (hideR_e _ Hsi) Hout ltac:(pose proof (Hrows 0 ltac:(lia) ltac:(lia)); unfold c_nP; nia) Hspe Hobjs' HFS'
HGP' HLP HIMG' HIMGlen HFBC') as (Hobjs'' & HFS'' & HGP'' & HIMG'' & HFBC'').
pose proof (garr8_ipass ubs0segs (ms_mem msF) mem' (c_img cx) pint IMGV (c_w cx) (c_h cx) 4 8 m R HIMG' HIMGlen ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros; lia) Hcp) as HGQ.
exists m. split; [left; lia|].
exists L2, A2, regs', mem', md2, pint. split; [reflexivity|]. split; [exact HJ'|]. split; [exact Hid2|]. split; [exact HRq2|].
split; [exact HB2|]. split; [exact Hwt|]. split; [exact Hpnz|].
split; [unfold ra_regs in *; rewrite !HKf, !HK by (cbv; tauto); exact HR|].
split; [rewrite HKf, HK by (cbv; tauto); exact G23|]. split; [rewrite HKf, HK by (cbv; tauto); exact G24|]. split; [rewrite HKf, HK by (cbv; tauto); exact G22|].
split; [rewrite HKf, HK by (cbv; tauto); exact G18|]. split; [rewrite HKf, HK by (cbv; tauto); exact G25|].
split; [rewrite HKf, HK by (cbv; tauto); exact G19|].
split; [rewrite P20; f_equal; lia|]. split; [rewrite P21; f_equal; lia|]. split; [exact P10|]. split; [exact P12|].
split; [exact Hobjs''|]. split; [exact HFS''|].
split; [apply (proj2 (garr8_app ubs0segs mem' pint PFX _)); split; [exact HGP'' | rewrite HLP; exact HGQ]|].
split; [rewrite length_app, Nat2Z.inj_add, HLP; lazymatch goal with |- _ + Z.of_nat (length (ipassZ _ _ ?s0 ?t0 _)) = _ =>
rewrite (ipassZ_length IMGV (c_w cx) (c_h cx) s0 t0 m HIMGlen) by (first [lia | intros; lia]) end; lia|].
split; [exact HIMG'' | exact HFBC''].
Qed.
Lemma ra_W3 : forall cx L A mem md regs0 p icl idl R b c1,
rcx_ok cx -> ra_origin cx regs0 -> Permutation (blocks L A) (c_blocks cx) ->
0 <= R -> c_w cx * R <= c_nP cx -> (forall j, 0 <= j -> 2 + 4 * j < c_h cx -> R + j + 1 <= c_h cx) ->
forall PFX, Z.of_nat (length IMGV) = c_nP cx ->
at_LX PC_L2X cx L A mem md regs0 p icl idl R PFX b c1 ->
SR ubs0segs c1 (fun c' => exists m, ((3 <= c_h cx /\ 1 <= m /\ 2 + 4 * (m - 1) < c_h cx <= 2 + 4 * m) \/ (c_h cx < 3 /\ m = 0)) /\
at_LX PC_L4P cx L A mem md regs0 p icl idl (R + m) (PFX ++ ipassZ IMGV (c_w cx) 2 4 m) b c').
Proof using IMG.
intros cx L A mem md regs0 p icl idl R b c1 Hcx HO HB HR0 HRn Hrows PFX HIMGlen
(L2 & A2 & regs2 & mem2 & md2 & pint & -> & HJ2 & Hid2 & HRq2 & HB2 & Hwt & Hpnz & HR & G23 & G24 & G22 & G18 & G25 & G19 & G20 & G21 & G10 & G12 & Hobjs & HFS & HGP & HLP & HIMG2 & HFBC).
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HSTKv : RAWADD_STK = 8704) by reflexivity.
pose proof HO as (Hspe & Htp0 & Hgp0 & Hra0 & Hgp & H25o & H26o & H27o).
pose proof Hcx as ((Hspal & Hsplo & Hcfplo & Hcfphi & Hcfpal & Hraw0 & Hraw1 & Hraw16 & Hg0 & Hg1 & Hg16 & Himg0 & Himg1 & Himg16 &
Hs1 & Hs2 & Hs3 & Hw1 & Hh1 & HnP & HnP2 & Hsgct & Hwfn & Hfile & Htpv & Hf0 & Hf1 & Hfin & Hsp47) & Hslct).
pose proof (objs_fields_ok _ _ _ Hobjs) as (F0 & F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & G1' & G2' & G3' & G4' & G5' & G6' & G7' & G8' & LG).
pose proof HR as (R2 & R8 & R9 & R4 & R3 & R27).
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HH2.
pose proof HJ2 as (_ & _ & _ & _ & _ & (Hsp0al & Hstk0 & Hceil & Hsp063 & Hstw) & _). cbn beta in Hstw.
destruct (pint_seps cx L A L2 A2 mem2 md2 pint Hcx HB HH2 HB2) as ((Hp0 & Hp1 & Hp16) & Hsr & Hsg & Hsi).
assert (Hsi' : pint + c_nP cx <= c_img cx \/ c_img cx + c_Nimg cx <= pint) by (clear - Hsi; lia).
apply hideR_i in Hsr. apply hideR_i in Hsg. apply hideR_i in Hsi. apply hideR_i in Hsi'.
assert (Hpin : In (pint, c_nP cx) (blocks L2 A2)) by (eapply Permutation_in; [apply Permutation_sym; exact HB2 | left; reflexivity]).
assert (Himgin : In (c_img cx, c_Nimg cx) (blocks L2 A2)).
{ eapply Permutation_in; [apply Permutation_sym; exact HB2 | right]. eapply blocks_perm_in; [exact HB | right; right; left; reflexivity]. }
assert (HnPlo : 1 <= c_nP cx) by (unfold c_nP; nia). assert (HnPe : c_nP cx = c_w cx * c_h cx) by reflexivity.
remember (Ereg regs2 (ra_extra cx (c_rcur cx) [])) as E eqn:HE0.
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs2 rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HE2 : bv_unsigned (ew E 2) = c_sp cx) by (rewrite (HE 2%nat 2%bv eq_refl), R2; apply unsigned_lit_small; lia).
assert (HE10 : ew E 10 = Z_to_bv 64 (c_h cx)) by (rewrite (HE 10%nat 10%bv eq_refl); exact G10).
assert (HE12 : ew E 12 = Z_to_bv 64 (c_w cx)) by (rewrite (HE 12%nat 12%bv eq_refl); exact G12).
assert (HE21 : ew E 21 = Z_to_bv 64 (pint + c_w cx * R)) by (rewrite (HE 21%nat 21%bv eq_refl); exact G21).
assert (HE20 : ew E 20 = Z_to_bv 64 (pint + c_w cx * R)) by (rewrite (HE 20%nat 20%bv eq_refl); exact G20).
pose proof (E_cv regs2 cx (c_rcur cx) []) as HX. rewrite <- HE0 in HX.
assert (HE35 : ew E 35 = Z_to_bv 64 (c_w cx)) by (apply (HX 3%nat); reflexivity).
assert (HS : st_ok ubs0segs E (ssLX PC_L2X) (mkst regs2 (Z_to_bv 64 PC_L2X) mem2 (seg_rom ubs0segs))).
{ subst E. unfold ssLX.
apply (ra_st_okW cx (c_rcur cx) regs2 [] mem2 PC_L2X _ 0 0 false _ _ [] [] Hcx Hobjs HR); rewrite <- ?HE0.
- apply regs_ok_Ereg.
- intros a Ha. apply Hstw. lia.
- intros X. discriminate X.
- reflexivity.
- constructor.
- cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HE10, HE12, !unsigned_lit_small by lia.
change (2 ^ 0) with 1. rewrite !Z.mod_1_r. repeat split; lia.
- constructor.
- constructor. }
change mem2 with (ms_mem (mkst regs2 (Z_to_bv 64 PC_L2X) mem2 (seg_rom ubs0segs))) in HJ2.
jrun_to LAWS ubs0tbl_ok HS HJ2 PC_L3; [wr2 HE2|].
jbranch ubs0tbl HS.
-
rewrite branch_geu_U, U_lit, (U_atom _ 10 _ HE10) in Hc by lia.
assert (Hh5 : c_h cx < 3) by (destruct (Z.ltb_spec 2 (c_h cx)); [discriminate | lia]). clear Hc.
jrun_to LAWS ubs0tbl_ok HS HJ2 PC_L4P; [wr2 HE2|].
pose proof (regs_kept_of_st_ok _ _ _ _ regs2 _ [2; 3; 4; 8; 9; 10; 12; 18; 19; 20; 22; 23; 24; 25; 27]%bv HS ltac:(rewrite HE0; apply env_agree_refl) ltac:(vm_compute; reflexivity)) as HK.
jreg HS (21%bv:reg) as Q21.
lazymatch type of HS with st_ok _ _ _ ?msf => rename msf into msF end.
rewrite (st_ok_mkst _ _ _ _ HS eq_refl). cbn [ss_pc]. apply SR_ret.
exists 0. split; [right; lia|].
exists L2, A2, (ms_regs msF), (ms_mem msF), md2, pint. split; [reflexivity|]. split; [exact HJ2|]. split; [exact Hid2|]. split; [exact HRq2|].
split; [exact HB2|]. split; [exact Hwt|]. split; [exact Hpnz|].
split; [unfold ra_regs in *; rewrite !HK by (cbv; tauto); exact HR|].
split; [rewrite HK by (cbv; tauto); exact G23|]. split; [rewrite HK by (cbv; tauto); exact G24|]. split; [rewrite HK by (cbv; tauto); exact G22|].
split; [rewrite HK by (cbv; tauto); exact G18|]. split; [rewrite HK by (cbv; tauto); exact G25|].
split; [rewrite HK by (cbv; tauto); exact G19|].
split; [rewrite HK by (cbv; tauto); rewrite G20; f_equal; lia|].
split; [rewrite Q21; cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned, HE20; f_equal; lia|].
split; [rewrite HK by (cbv; tauto); exact G10|]. split; [rewrite HK by (cbv; tauto); exact G12|].
assert (MEQs : forall a, 0 <= a < 2 ^ 64 -> mbyte ubs0segs (ms_mem msF) a = mbyte ubs0segs mem2 a) by (intros a Ha; mbyte_chain ltac:(fun H => rewrite ?HE2 in H)).
split; [eapply objs_at_kept; [exact Hobjs | | |]; intros i Hi; apply MEQs; lia|].
split; [eapply (frame_savedN_kept ubs0_msyms 12); [lia | exact HFS|]; intros a Ha; apply MEQs; lia|].
rewrite app_nil_r, Z.add_0_r.
split; [apply (garr8_frame ubs0segs mem2 _ pint PFX HGP); intros a Ha; apply MEQs; lia|]. split; [exact HLP|].
split; [apply (garr8_frame ubs0segs mem2 _ (c_img cx) IMGV HIMG2); intros a Ha; apply MEQs; unfold c_nP in *; lia | eapply fbC_kept; [exact HFBC | |]; intros a Ha; apply MEQs; lia].
-
rewrite branch_geu_U, U_lit, (U_atom _ 10 _ HE10) in Hc by lia.
assert (Hh5 : 3 <= c_h cx) by (destruct (Z.ltb_spec 2 (c_h cx)); [lia | discriminate]). clear Hc.
jrun_to LAWS ubs0tbl_ok HS HJ2 PC_L3; [wr2 HE2|].
pose proof (regs_kept_of_st_ok _ _ _ _ regs2 _ [2; 3; 4; 8; 9; 10; 18; 19; 20; 21; 22; 23; 24; 25; 27]%bv HS ltac:(rewrite HE0; apply env_agree_refl) ltac:(vm_compute; reflexivity)) as HK.
jreg HS (26%bv:reg) as Q26. cbn [ms_regs mkst] in Q26.
jreg HS (12%bv:reg) as Q12. cbn [ms_regs mkst] in Q12.
lazymatch type of HS with st_ok _ _ _ ?msf => rename msf into msF end.
assert (Hobjs' : objs_at (ms_mem msF) cx (c_rcur cx)).
{ eapply objs_at_kept; [exact Hobjs | | |]; intros i Hi; mbyte_chain ltac:(fun H => rewrite ?HE2 in H). }
assert (HFS' : frame_savedN ubs0_msyms 12 regs0 (ms_mem msF) (spZ regs0)).
{ eapply (frame_savedN_kept ubs0_msyms 12); [lia | exact HFS|]; intros a Ha; mbyte_chain ltac:(fun H => rewrite ?HE2 in H). }
assert (MEQs : forall a, 0 <= a < 2 ^ 64 -> mbyte ubs0segs (ms_mem msF) a = mbyte ubs0segs mem2 a) by (intros a Ha; mbyte_chain ltac:(fun H => rewrite ?HE2 in H)).
assert (HGP' : garr8 ubs0segs (ms_mem msF) pint PFX) by (apply (garr8_frame ubs0segs mem2 _ pint PFX HGP); intros a Ha; apply MEQs; lia).
assert (HIMG' : garr8 ubs0segs (ms_mem msF) (c_img cx) IMGV) by (apply (garr8_frame ubs0segs mem2 _ (c_img cx) IMGV HIMG2); intros a Ha; apply MEQs; unfold c_nP in *; lia).
assert (HFBC' : fbC (ms_mem msF) cx) by (eapply fbC_kept; [exact HFBC | |]; intros a Ha; apply MEQs; lia).
rewrite (st_ok_mkst _ _ _ _ HS eq_refl). cbn [ss_pc].
eapply SR_mono.
{ eapply (il_loop3 API IMG (Z.to_nat (c_h cx)) 2 R (ms_regs msF) (ms_mem msF) RAWADD_STK (spZ regs0) _ L A mem md L2 A2 md2 pint (c_nP cx) (c_img cx) (c_Nimg cx) (c_w cx) (c_h cx) (c_cfp cx) (cvals cx));
cbn [ms_regs ms_mem];
[ lia | lia | lia | exact Hrows | lia | lia | lia | lia | exact HJ2 | exact Hpin | exact Hwt | exact Himgin | exact (hideR_e _ Hsi')
| exact (proj1 Hobjs') | reflexivity | reflexivity | reflexivity | lia | lia | exact Hcfpal | rewrite HK by (cbv; tauto); exact R9
| rewrite HK by (cbv; tauto); exact G20 | exact Q26 | first [exact Q12 | rewrite Q12; cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; exact HE35] ]. }
cbv beta. intros c' (regs' & mem' & m & -> & HJ' & Hm1 & Hm2 & Hm3 & P20 & P21 & P10 & P12 & HKf & Hout & Hgr & Hcp).
rewrite <- HnPe in Hout.
destruct (after_loop_mem cx (ms_mem msF) mem' pint (c_rcur cx) regs0 R PFX Hcx Hp0 Hp1 (hideR_e _ Hsr) (hideR_e _ Hsg) (hideR_e _ Hsi) Hout ltac:(pose proof (Hrows 0 ltac:(lia) ltac:(lia)); unfold c_nP; nia) Hspe Hobjs' HFS'
HGP' HLP HIMG' HIMGlen HFBC') as (Hobjs'' & HFS'' & HGP'' & HIMG'' & HFBC'').
pose proof (garr8_ipass ubs0segs (ms_mem msF) mem' (c_img cx) pint IMGV (c_w cx) (c_h cx) 2 4 m R HIMG' HIMGlen ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros; lia) Hcp) as HGQ.
exists m. split; [left; lia|].
exists L2, A2, regs', mem', md2, pint. split; [reflexivity|]. split; [exact HJ'|]. split; [exact Hid2|]. split; [exact HRq2|].
split; [exact HB2|]. split; [exact Hwt|]. split; [exact Hpnz|].
split; [unfold ra_regs in *; rewrite !HKf, !HK by (cbv; tauto); exact HR|].
split; [rewrite HKf, HK by (cbv; tauto); exact G23|]. split; [rewrite HKf, HK by (cbv; tauto); exact G24|]. split; [rewrite HKf, HK by (cbv; tauto); exact G22|].
split; [rewrite HKf, HK by (cbv; tauto); exact G18|]. split; [rewrite HKf, HK by (cbv; tauto); exact G25|].
split; [rewrite HKf, HK by (cbv; tauto); exact G19|].
split; [rewrite P20; f_equal; lia|]. split; [rewrite P21; f_equal; lia|]. split; [exact P10|]. split; [exact P12|].
split; [exact Hobjs''|]. split; [exact HFS''|].
split; [apply (proj2 (garr8_app ubs0segs mem' pint PFX _)); split; [exact HGP'' | rewrite HLP; exact HGQ]|].
split; [rewrite length_app, Nat2Z.inj_add, HLP; lazymatch goal with |- _ + Z.of_nat (length (ipassZ _ _ ?s0 ?t0 _)) = _ =>
rewrite (ipassZ_length IMGV (c_w cx) (c_h cx) s0 t0 m HIMGlen) by (first [lia | intros; lia]) end; lia|].
split; [exact HIMG'' | exact HFBC''].
Qed.
End S.
End c.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
