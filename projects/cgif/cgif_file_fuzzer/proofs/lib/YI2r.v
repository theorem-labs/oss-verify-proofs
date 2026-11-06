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
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YH00 YH03 YH02 YN3a YN3b YI06 YI5b YI09 YI08 YI0r YI1w YI1v YI4l YI21 YI2m YI3t YI5o YI5l YI6b YI5n YI20 YI1d YI2l.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI25 YI2o YI2p.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI2q.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YI14 YI13 YI5c.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO03 YO0p YO0j YO0m YO0l YO0n YO0k YO0o.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI00 YI01 YI3u YI22 YI5a YI5d YI0f YI2w YI2v.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI2s.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require YO07.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO08.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition t2_stk : list YP09.chunk := fl_stk_saved 32 ++ [mkChunk 112 (CVal 8 (SOff 45 0))].
Definition ss_p2x : sstate :=
mkSS FL_P2X sr_atoms [ YP09.mkRegion (Some 2%nat) 0 272 0 168 t2_stk ] None
(mkFacts [(2%nat, mkAF (CEIL_MIN + FLUSH_STK - 272) (2^63 - 272) 4); (12%nat, mkAF 0 16 0); (15%nat, mkAF 0 65535 0)] [] []).
Definition ss_T (z : bool) : sstate :=
mkSS FL_T sr_atoms [ YP09.mkRegion (Some 2%nat) 0 272 0 0 t2_stk ] None
(mkFacts [(2%nat, mkAF (CEIL_MIN + FLUSH_STK - 272) (2^63 - 272) 4); (15%nat, mkAF 0 65535 0)]
[mkAC (if z then BC_EQ else BC_NE) (SAlu ALU_AND (SOff 11 0) (SLit 1)) (SLit 0)] []).
Section S.
Variable API : AllocAPI src0_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws src0_msyms MR := aa_laws API.
Hypothesis IMG : img_laws src0_msyms MR.
Hypothesis RAWADDX : rawadd_specX API.
Definition t2_pre L A mem md (regs0 regs1 : bvmap 5 word) Lc Ac memc mdc (g N : Z) (s : cgif_st) (i : nat) (f : frame_st) (gen1 : Z)
(rest FP tmp : list (Z * Z)) (pTmp Nt tv w h top left : Z) : Prop :=
let sp0 := spZ regs0 in
journal src0_msyms MR FLUSH_STK sp0 FP L A mem md Lc Ac memc mdc /\ st_init_done Ac = true /\
YK0s.ret_ok (getr regs0 1) /\ sp0 mod 16 = 0 /\ getr regs0 4 = Z_to_bv 64 (ms_tp src0_msyms) /\
cgif_at memc g (flush_upd s i gen1 (rw_cur s)) /\ cgif_wf s N /\ (i = 1%nat \/ i = 2%nat) /\ nth_error (cg_frames s) i = Some (Some f) /\
fl_fp FP s f /\
Permutation (blocks Lc Ac) (tmp ++ cgif_blocks0 g s N ++ rest) /\
((tmp = [] /\ pTmp = 0) \/ (tmp = [(pTmp, Nt)] /\ pTmp <> 0 /\ w * h <= Nt)) /\
(In (pTmp, Nt) (blocks L A) -> forall k, 0 <= k < Nt -> inFP FP (pTmp + k)) /\
1 <= w /\ 0 <= left /\ left + w <= cg_W s /\ 1 <= h /\ 0 <= top /\ top + h <= cg_H s /\ 0 <= tv < 2 ^ 64 /\
fl_saved_ok memc sp0 regs0 /\
word_mem src0segs memc (sp0 - 272 + 112) tv /\
getr regs1 2 = Z_to_bv 64 (sp0 - 272) /\ getr regs1 8 = Z_to_bv 64 g /\ getr regs1 9 = Z_to_bv 64 (fr_ptr f) /\
getr regs1 20 = Z_to_bv 64 (fr_ptr f + 26) /\ getr regs1 22 = Z_to_bv 64 pTmp /\
getr regs1 19 = Z_to_bv 64 (Z.land (fr_attr f) 1) /\ getr regs1 27 = Z_to_bv 64 (cg_W s) /\ getr regs1 14 = Z_to_bv 64 (cg_H s) /\
getr regs1 26 = Z_to_bv 64 h /\ getr regs1 16 = Z_to_bv 64 w /\ getr regs1 17 = Z_to_bv 64 top /\ getr regs1 5 = Z_to_bv 64 left /\
fl_untouched regs0 regs1.
Lemma fl_t2 :
forall L A mem md (regs0 regs1 : bvmap 5 word) Lc Ac memc mdc (g N : Z) (s : cgif_st) (i : nat) (f b : frame_st)
(rest FP FPw tmp : list (Z * Z)) (pTmp Nt tv w h top left p np : Z)
(S GPAL : list Z) (cur befr : YO07.frame) (brb bc : rbound) (ha : Z),
let sp0 := spZ regs0 in
let G := gcfg_of s GPAL in
let gen1 := fl_gen3 G cur (Some befr) in
t2_pre L A mem md regs0 regs1 Lc Ac memc mdc g N s i f gen1 rest FP tmp pTmp Nt tv w h top left ->
nth_error (cg_frames s) (i - 1) = Some (Some b) -> getr regs1 18 = Z_to_bv 64 (fr_ptr b) ->
getr regs1 12 = Z_to_bv 64 p -> 0 <= p <= 16 -> getr regs1 15 = Z_to_bv 64 np -> 0 <= np <= 65535 ->
fl_sink g s N rest FP FPw S L A mem md sp0 ->
fl_vals memc s N f (Some b) GPAL cur (Some befr) ->
getr regs1 23 = Z_to_bv 64 (fr_disp f) -> getr regs1 24 = Z_to_bv 64 (Z.land (fr_attr f) 4) -> getr regs1 25 = Z_to_bv 64 ha ->
ha = (if fl_hasAlpha G cur then 1 else 0) ->
w = fl_w G cur (Some befr) -> h = fl_h G cur (Some befr) -> top = fl_top G cur (Some befr) -> left = fl_left G cur (Some befr) ->
YO07.flag (fl_gen3 G cur (Some befr)) 1 = true ->
np = fl_npal G cur -> p = YO07.calcNextPower2Ex np ->
garr8 src0segs memc (if pTmp =? 0 then fr_img f else pTmp) (fl_tmp G cur (Some befr)) -> Z.of_nat (length (fl_tmp G cur (Some befr))) = w * h ->
res_ok Ac bc ->
(pTmp = 0 -> room bc N /\ rawadd_room (rb_malloc bc N) (w * h) /\ rb_le (rb_free (rawadd_rb (rb_malloc bc N)) N) (flush_rb brb)) ->
(pTmp <> 0 -> rawadd_room bc (w * h) /\ rb_le (rb_free (rawadd_rb bc) Nt) (flush_rb brb)) ->
SR src0segs (mkCfg (mkst regs1 (Z_to_bv 64 FL_P2X) memc (seg_rom src0segs)) mdc) (fl_post API regs0 g s N i rest FPw S GPAL cur (Some befr) brb L A mem md).
Proof.
intros L A mem md regs0 regs1 Lc Ac memc mdc g N s i f b rest FP FPw tmp pTmp Nt tv w h top left p np S GPAL cur befr brb bc ha sp0 G gen1
(HJ & Hid & Hra0 & Hal16 & Htp0 & Hat & Hwf & Hi & Hf & HFP & HB & Htmp & Htmp_fp & Hw & Hl0 & Hlw & Hh & Ht0 & Hth & Htv & HSV & Wtv
& G2 & G8 & G9 & G20 & G22 & G19 & G27 & G14 & G26 & G16 & G17 & G5 & G3 & G4) Hb G18 G12 Hp G15 Hnp
HSINK HVALS G23 G24 G25 Xha Xw Xh Xtop Xleft XT1 Xnp Xp XTMP XTMPL HRq HNUM0 HNUM1.
change (spZ regs0) with sp0 in HSV, Wtv, G2.
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HFSv : FLUSH_STK = 9216) by reflexivity.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HH0.
pose proof HJ as (_ & _ & _ & _ & _ & (Hsp0al & Hstk0 & Hceil & Hsp063 & Hstw) & _).
pose proof Hwf as (Hlen & HW1 & HH1 & HN & HNle & _).
pose proof Hat as (Hobj & _ & _). rewrite (cgif_vals_flush_upd s i gen1 (rw_cur s)) in Hobj.
pose proof (obj_at_range _ _ _ _ _ Hobj) as Rg. pose proof (Rg 7%nat (cg_W s) eq_refl) as RW. cbn [nth snd LAY_CGIF Z.of_N] in RW.
assert (Hfin : In (Some f) (cg_frames s)) by (eapply nth_error_In; exact Hf).
assert (HBc : Permutation (blocks Lc Ac) (cgif_blocks0 g s N ++ (tmp ++ rest))) by (eapply Permutation_trans; [exact HB|]; apply Permutation_app_swap_app).
assert (XB : exists nn, In ((if pTmp =? 0 then fr_img f else pTmp), nn) (blocks Lc Ac) /\ w * h <= nn).
{ destruct Htmp as [[T1 T2] | (T1 & T2 & T3)].
- exists N. rewrite T2. cbn [Z.eqb]. split; [| rewrite HN; clear - Hw Hl0 Hlw Hh Ht0 Hth; nia].
apply (Permutation_in _ (Permutation_sym HBc)). apply in_app_iff. left. apply (frame_blocks_in_cgif0 g s N f); [exact Hfin | right; left; reflexivity].
- exists Nt. destruct (Z.eqb_spec pTmp 0) as [Hz|Hz]; [exfalso; exact (T2 Hz)|]. split; [| exact T3].
apply (Permutation_in _ (Permutation_sym HB)). rewrite T1. left. reflexivity. }
set (E := Ereg regs1 (map (Z_to_bv 64) (fl_saved_vals regs0 ++ [tv]) ++ [])).
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HA : forall j v, nth_error (fl_saved_vals regs0 ++ [tv]) j = Some v -> ew E (32 + j) = Z_to_bv 64 v) by (intros j v Hj; subst E; apply Ereg_vals; exact Hj).
assert (HK : forall j v, nth_error (fl_saved_vals regs0) j = Some v -> ew E (32 + j) = Z_to_bv 64 v).
{ intros j v Hj. apply HA. rewrite nth_error_app1; [exact Hj|]. apply (proj1 (nth_error_Some _ _)). rewrite Hj. discriminate. }
assert (HE45 : ew E 45 = Z_to_bv 64 tv) by (apply (HA 13%nat); reflexivity).
assert (HU2 : bv_unsigned (ew E 2) = sp0 - 272) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; clear - Hceil Hsp063 HFSv Hac; lia).
assert (HR0 : region_ok src0segs E memc (YP09.mkRegion (Some 2%nat) 0 272 0 168 t2_stk)).
{ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU2.
split; [lia|]. split; [lia|]. split; [intros o Ho; apply Hstw; lia|].
unfold t2_stk. apply Forall_app; split; [apply (fl_saved_chunks_ok E memc sp0 regs0 32 HSV); intros j v Hj; exact (HK j v Hj)|].
constructor; [| constructor].
eapply (chunk_ok_val _ _ _ _ _ _ _ tv); [cbn [sv_denot]; rewrite Z.add_0_r, HE45, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact Wtv]. }
assert (HFA : atoms_ok E [(2%nat, mkAF (CEIL_MIN + FLUSH_STK - 272) (2^63 - 272) 4); (12%nat, mkAF 0 16 0); (15%nat, mkAF 0 65535 0)]).
{ cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HU2, (HE 12%nat 12%bv eq_refl), (HE 15%nat 15%bv eq_refl), G12, G15, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. rewrite !Z.mod_1_r. try pose proof (proj1 alloc_ceiling_val) as HacR; clear - HacR Hceil Hsp063 Hal16 Hp Hnp HFSv. repeat split; try lia.
replace (sp0 - 272) with (sp0 + (-17) * 16) by lia. rewrite Z.mod_add by lia. exact Hal16. }
assert (HS : st_ok src0segs E ss_p2x (mkst regs1 (Z_to_bv 64 FL_P2X) memc (seg_rom src0segs))).
{ unfold ss_p2x. apply entry_st_ok_full; [apply regs_ok_Ereg | vm_compute; reflexivity | constructor; [exact HR0 | constructor] | cbn [pairwise_disjoint all_disjoint]; split; exact I | split; [exact HFA | split; exact I]]. }
clear HR0 HFA.
change memc with (ms_mem (mkst regs1 (Z_to_bv 64 FL_P2X) memc (seg_rom src0segs))) in HJ.
assert (WR : forall E0 cs, bv_unsigned (ew E0 2) = sp0 - 272 -> wr_ok E0 [YP09.mkRegion (Some 2%nat) 0 272 0 168 cs] FLUSH_STK sp0 FP (blocks L A) (blocks Lc Ac)).
{ intros E0 cs H2. eapply wr_ok_cons_win; [reflexivity | exact H2 | cbn [r_wlo r_whi]; intros _; lia | apply wr_ok_nil]. }
assert (HP8 : U E (SAlu ALU_AND (SOff 12 0) (SLit 255)) = p).
{ rewrite U_and_lit, (U_atom _ 12 p ltac:(rewrite (HE 12%nat 12%bv eq_refl); exact G12)) by lia. rewrite Z.land_ones with (n := 8) by lia. apply Z.mod_small. lia. }
assert (TW : U E (SAlu ALU_XOR (SAluw ALU_SLL (SLit 18446744073709551615) (SAlu ALU_AND (SOff 12 0) (SLit 255))) (SLit (-1))) = 2 ^ p - 1 /\
U E (SAlu ALU_ADD (SAluw ALU_SLL (SLit 2) (SAlu ALU_AND (SOff 12 0) (SLit 255))) (SLit (-1))) = 2 ^ (p + 1) - 1).
{ clear - HP8 Hp. rewrite !U_SAlu. cbn [zalu_raw]. rewrite !(U_of_S E (SAluw _ _ _)), !S_SAluw. cbn [zalu_raw]. rewrite HP8, !U_SLit.
assert (Hk : exists k, p = Z.of_nat k /\ (k <= 16)%nat) by (exists (Z.to_nat p); split; lia).
destruct Hk as (k & -> & Hk).
do 17 (destruct k as [|k]; [split; vm_compute; reflexivity|]). exfalso; lia. }
pose proof TW as [TW1 TW2].
assert (HU15 : U E (SOff 15 0) = np) by (apply (U_atom _ 15 np); [rewrite (HE 15%nat 15%bv eq_refl); exact G15 | lia]).
assert (C1t : branch_taken BC_LTU (sv_denot E (SLit 2)) (sv_denot E (SAlu ALU_AND (SOff 12 0) (SLit 255))) = (2 <? p)) by (rewrite branch_ltu_U, U_SLit, HP8; reflexivity).
assert (C1f : branch_taken BC_GEU (sv_denot E (SLit 2)) (sv_denot E (SAlu ALU_AND (SOff 12 0) (SLit 255))) = negb (2 <? p)) by (rewrite branch_geu_U, U_SLit, HP8; reflexivity).
assert (C3t : branch_taken BC_GEU (sv_denot E (SLit 3)) (sv_denot E (SOff 15 0)) = negb (3 <? np)) by (rewrite branch_geu_U, U_SLit, HU15; reflexivity).
assert (C3f : branch_taken BC_LTU (sv_denot E (SLit 3)) (sv_denot E (SOff 15 0)) = (3 <? np)) by (rewrite branch_ltu_U, U_SLit, HU15; reflexivity).
assert (C2t : branch_taken BC_GEU (sv_denot E (SAlu ALU_AND (SAlu ALU_XOR (SAluw ALU_SLL (SLit 18446744073709551615) (SAlu ALU_AND (SOff 12 0) (SLit 255))) (SLit (-1))) (SLit 255))) (sv_denot E (SOff 15 0))
= negb ((2 ^ p - 1) mod 256 <? np)).
{ rewrite branch_geu_U, U_and_lit, TW1, HU15 by lia. rewrite Z.land_ones with (n := 8) by lia. reflexivity. }
assert (C2f : branch_taken BC_LTU (sv_denot E (SAlu ALU_AND (SAlu ALU_XOR (SAluw ALU_SLL (SLit 18446744073709551615) (SAlu ALU_AND (SOff 12 0) (SLit 255))) (SLit (-1))) (SLit 255))) (sv_denot E (SOff 15 0))
= ((2 ^ p - 1) mod 256 <? np)).
{ rewrite branch_ltu_U, U_and_lit, TW1, HU15 by lia. rewrite Z.land_ones with (n := 8) by lia. reflexivity. }
assert (XTO : fl_tidx G cur (Some befr) = (if (2 ^ Z.max 2 p - 1) mod 256 <? np then (2 ^ (Z.max 2 p + 1) - 1) mod 256 else (2 ^ Z.max 2 p - 1) mod 256)).
{ unfold fl_tidx. rewrite XT1. unfold fl_tOpt, fl_t0, fl_p. rewrite <- Xnp, <- Xp. reflexivity. }
assert (GO : forall ss ms' rg0 (e : sv), st_ok src0segs E ss ms' -> ss_pc ss = FL_T2B -> ss_resv ss = None ->
nth_error (ss_mem ss) 0 = Some rg0 -> r_base rg0 = Some 2%nat ->
In (mkChunk 112 (CVal 8 e)) (r_chunks rg0) ->
(U E e) mod 256 = fl_tidx G cur (Some befr) ->
forallb (fun r : reg => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) [2; 3; 4; 17; 5; 8; 9; 14; 26; 16; 18; 20; 22; 27; 19; 23; 24; 25]%bv = true ->
journal src0_msyms MR FLUSH_STK sp0 FP L A mem md Lc Ac (ms_mem ms') mdc ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 272 <= a < sp0 - 272 + 168) -> mbyte src0segs (ms_mem ms') a = mbyte src0segs memc a) ->
SR src0segs (mkCfg ms' mdc) (fl_post API regs0 g s N i rest FPw S GPAL cur (Some befr) brb L A mem md)).
{ intros ss ms' rg0 e HS' Hpc Hrv Hrg0 Hb0 Hin112 He Hkl HJ' K.
pose proof (regs_kept_of_st_ok src0segs _ ss ms' regs1 _ _ HS' (env_agree_refl _ _) Hkl) as R.
pose proof (st_region_chunks src0segs E ss ms' 0 rg0 2%nat (sp0 - 272) HS' Hrg0 Hb0 HU2) as Hcs.
assert (KB : forall bb nn k, In (bb, nn) (blocks Lc Ac) -> 0 <= k < nn -> mbyte src0segs (ms_mem ms') (bb + k) = mbyte src0segs memc (bb + k)).
{ intros bb nn k Hbn' Hk. destruct (blocks_range _ _ LAWS Lc Ac memc mdc bb nn HH0 Hbn') as [R0 R1]. apply K; clear - R0 R1 Hk Hceil HFSv Hac; lia. }
assert (KB0 : forall bb nn k, In (bb, nn) (cgif_blocks0 g s N) -> 0 <= k < nn -> mbyte src0segs (ms_mem ms') (bb + k) = mbyte src0segs memc (bb + k)).
{ intros bb nn k Hbn Hk. apply (KB bb nn k); [| exact Hk]. apply (Permutation_in _ (Permutation_sym HBc)). apply in_app_iff. left. exact Hbn. }
rewrite (st_ok_mkst src0segs _ _ _ HS' Hrv), Hpc.
eapply (fl_t2b API IMG RAWADDX L A mem md regs0 (ms_regs ms') Lc Ac (ms_mem ms') mdc g N s i f b rest FP FPw tmp pTmp Nt (U E e) w h top left S GPAL cur befr brb bc ha);
[ exact HJ' | exact Hid | exact Hra0 | exact Hal16 | exact Htp0 | | exact Hwf | exact Hi | exact Hf | exact Hb | exact HFP | exact HB | exact Htmp | exact Htmp_fp
| exact Hw | exact Hl0 | exact Hlw | exact Hh | exact Ht0 | exact Hth | apply U_range
| apply (fl_saved_ok_kept memc); [exact HSV | intros a Ha; apply K; clear - Ha Hceil Hsp063 HFSv Hac; lia]
| apply (chunk_word E _ _ 112 _ _ (proj1 (Forall_forall _ _) Hcs _ Hin112)); [apply denot_of_U'; reflexivity | apply U_range]
| rewrite (R 2%bv ltac:(cbv; auto 50)); exact G2 | rewrite (R 8%bv ltac:(cbv; auto 50)); exact G8 | rewrite (R 9%bv ltac:(cbv; auto 50)); exact G9
| rewrite (R 18%bv ltac:(cbv; auto 50)); exact G18 | rewrite (R 20%bv ltac:(cbv; auto 50)); exact G20 | rewrite (R 22%bv ltac:(cbv; auto 50)); exact G22
| rewrite (R 19%bv ltac:(cbv; auto 50)); exact G19 | rewrite (R 27%bv ltac:(cbv; auto 50)); exact G27 | rewrite (R 14%bv ltac:(cbv; auto 50)); exact G14
| rewrite (R 26%bv ltac:(cbv; auto 50)); exact G26 | rewrite (R 16%bv ltac:(cbv; auto 50)); exact G16 | rewrite (R 17%bv ltac:(cbv; auto 50)); exact G17
| rewrite (R 5%bv ltac:(cbv; auto 50)); exact G5
| split; [rewrite (R 3%bv ltac:(cbv; auto 50)); exact G3 | rewrite (R 4%bv ltac:(cbv; auto 50)); exact G4]
| exact HSINK
| eapply fl_vals_kept; [| exact HVALS]; intros a0 n0 k Hin Hk; apply (KB0 a0 n0 k); [| exact Hk];
exact (fl_vblocks_sub g s N f (Some b) i Hf ltac:(right; exists (i - 1)%nat; exact Hb) _ Hin)
| rewrite (R 23%bv ltac:(cbv; auto 50)); exact G23 | rewrite (R 24%bv ltac:(cbv; auto 50)); exact G24 | rewrite (R 25%bv ltac:(cbv; auto 50)); exact G25
| exact Xha | exact Xw | exact Xh | exact Xtop | exact Xleft | exact XT1 | exact He
| destruct XB as (nn & Hbn & Hnn); eapply garr8_frame; [exact XTMP|]; intros a Ha; replace a with ((if pTmp =? 0 then fr_img f else pTmp) + (a - (if pTmp =? 0 then fr_img f else pTmp))) by lia;
apply (KB _ nn); [exact Hbn | clear - Ha Hnn XTMPL; subst G; lia]
| exact XTMPL | exact HRq | exact HNUM0 | exact HNUM1 ].
eapply (cgif_at_kept0 memc _ g (flush_upd s i gen1 (rw_cur s)) N (cgif_blocks0 g s N ++ []) []); [rewrite (cgif_blocks_flush_upd0 g s N i gen1 (rw_cur s) f Hf); apply Permutation_refl | exact Hat |].
intros bb nn k Hbn Hk. rewrite app_nil_r in Hbn. exact (KB0 bb nn k Hbn Hk). }
assert (K0 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 272 <= a < sp0 - 272 + 168) -> mbyte src0segs memc a = mbyte src0segs memc a) by (intros; reflexivity).
br_tree ltac:(idtac; runW LAWS FL_T2B ltac:(apply WR; exact HU2) HU2 (sp0 - 272) (sp0 - 272 + 168))
ltac:(idtac; let HS := get_HS in let HJ := get_HJ in
lazymatch goal with K : forall a, _ -> _ -> mbyte src0segs _ a = mbyte src0segs memc a |- _ =>
eapply (GO _ _ _ _ HS); [ reflexivity | reflexivity | reflexivity | reflexivity
| cbn [r_chunks]; repeat (first [left; reflexivity | right])
| rewrite XTO;
generalize (proj1 (proj2 (st_ok_facts_ok src0segs E _ _ HS))); cbn [ss_facts f_conds conds_ok]; unfold acond_ok; cbn [ac_c ac_a ac_b];
rewrite ?C1t, ?C1f, ?C2t, ?C2f, ?C3t, ?C3f, ?U_SLit, ?TW1, ?TW2; clear - Hp Hnp;
destruct (Z.ltb_spec 2 p); rewrite ?(Z.max_r 2 p) by lia; rewrite ?(Z.max_l 2 p) by lia;
change ((2 ^ 2 - 1) mod 256) with 3; change ((2 ^ (2 + 1) - 1) mod 256) with 7;
lazymatch goal with |- context [3 <? np] => destruct (3 <? np) | |- _ => destruct ((2 ^ p - 1) mod 256 <? np) end;
cbn [negb]; intros (B1 & B2 & _); first [discriminate B1 | discriminate B2 | reflexivity]
| vm_compute; reflexivity | exact HJ | exact K ] end)
4%nat.
Qed.
Lemma fl_trans :
forall L A mem md (regs0 regs1 : bvmap 5 word) Lc Ac memc mdc (g N : Z) (s : cgif_st) (i : nat) (f : frame_st)
(rest FP FPw tmp : list (Z * Z)) (pTmp Nt tv w h top left np : Z)
(S GPAL : list Z) (cur : YO07.frame) (bfr : option frame_st) (bef : option YO07.frame) (brb bc : rbound) (ha : Z),
let sp0 := spZ regs0 in
let G := gcfg_of s GPAL in
let gen1 := fl_gen3 G cur bef in
t2_pre L A mem md regs0 regs1 Lc Ac memc mdc g N s i f gen1 rest FP tmp pTmp Nt tv w h top left ->
forall g13, getr regs1 11 = Z_to_bv 64 g13 -> 0 <= g13 < 2 ^ 64 -> getr regs1 15 = Z_to_bv 64 np -> 0 <= np <= 65535 ->
(Z.land g13 1 <> 0 -> exists b befr, bfr = Some b /\ bef = Some befr /\ nth_error (cg_frames s) (i - 1) = Some (Some b) /\ getr regs1 18 = Z_to_bv 64 (fr_ptr b)) ->
nth (i - 1) (cg_frames s) None = bfr ->
fl_sink g s N rest FP FPw S L A mem md sp0 ->
fl_vals memc s N f bfr GPAL cur bef ->
getr regs1 23 = Z_to_bv 64 (fr_disp f) -> getr regs1 24 = Z_to_bv 64 (Z.land (fr_attr f) 4) -> getr regs1 25 = Z_to_bv 64 ha ->
ha = (if fl_hasAlpha G cur then 1 else 0) ->
w = fl_w G cur bef -> h = fl_h G cur bef -> top = fl_top G cur bef -> left = fl_left G cur bef ->
(Z.land g13 1 <> 0 <-> fl_trans_on G cur bef = true) ->
np = fl_npal G cur -> tv mod 256 = YO07.f_trans cur ->
garr8 src0segs memc (if pTmp =? 0 then fr_img f else pTmp) (fl_tmp G cur bef) -> Z.of_nat (length (fl_tmp G cur bef)) = w * h ->
res_ok Ac bc ->
(pTmp = 0 -> rawadd_room bc (w * h) /\ rb_le (rawadd_rb bc) (flush_rb brb) /\
(fl_trans_on G cur bef = true -> room bc N /\ rawadd_room (rb_malloc bc N) (w * h) /\ rb_le (rb_free (rawadd_rb (rb_malloc bc N)) N) (flush_rb brb))) ->
(pTmp <> 0 -> rawadd_room bc (w * h) /\ rb_le (rb_free (rawadd_rb bc) Nt) (flush_rb brb)) ->
SR src0segs (mkCfg (mkst regs1 (Z_to_bv 64 FL_T) memc (seg_rom src0segs)) mdc) (fl_post API regs0 g s N i rest FPw S GPAL cur bef brb L A mem md).
Proof.
intros L A mem md regs0 regs1 Lc Ac memc mdc g N s i f rest FP FPw tmp pTmp Nt tv w h top left np S GPAL cur bfr bef brb bc ha sp0 G gen1 PRE g13 G11 Hgen G15 Hnp Hbx
Hbfr HSINK HVALS G23 G24 G25 Xha Xw Xh Xtop Xleft XTON Xnp Xtv0 XTMP XTMPL HRq HNUM0 HNUM1.
pose proof PRE as (HJ & Hid & Hra0 & Hal16 & Htp0 & Hat & Hwf & Hi & Hf & HFP & HB & Htmp & Htmp_fp & Hw & Hl0 & Hlw & Hh & Ht0 & Hth & Htv & HSV & Wtv
& G2 & G8 & G9 & G20 & G22 & G19 & G27 & G14 & G26 & G16 & G17 & G5 & G3 & G4).
change (spZ regs0) with sp0 in HSV, Wtv, G2.
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HFSv : FLUSH_STK = 9216) by reflexivity.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HH0.
pose proof HJ as (_ & _ & _ & _ & _ & (Hsp0al & Hstk0 & Hceil & Hsp063 & Hstw) & _).
pose proof Hwf as (Hlen & HW1 & HH1 & HN & HNle & _).
pose proof Hat as (Hobj & _ & _). rewrite (cgif_vals_flush_upd s i gen1 (rw_cur s)) in Hobj.
pose proof (obj_at_range _ _ _ _ _ Hobj) as Rg. pose proof (Rg 7%nat (cg_W s) eq_refl) as RW. cbn [nth snd LAY_CGIF Z.of_N] in RW.
set (E := Ereg regs1 (map (Z_to_bv 64) (fl_saved_vals regs0 ++ [tv]) ++ [])).
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HA : forall j v, nth_error (fl_saved_vals regs0 ++ [tv]) j = Some v -> ew E (32 + j) = Z_to_bv 64 v) by (intros j v Hj; subst E; apply Ereg_vals; exact Hj).
assert (HK : forall j v, nth_error (fl_saved_vals regs0) j = Some v -> ew E (32 + j) = Z_to_bv 64 v).
{ intros j v Hj. apply HA. rewrite nth_error_app1; [exact Hj|]. apply (proj1 (nth_error_Some _ _)). rewrite Hj. discriminate. }
assert (HE45 : ew E 45 = Z_to_bv 64 tv) by (apply (HA 13%nat); reflexivity).
assert (HU2 : bv_unsigned (ew E 2) = sp0 - 272) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; clear - Hceil Hsp063 HFSv Hac; lia).
assert (HR0 : region_ok src0segs E memc (YP09.mkRegion (Some 2%nat) 0 272 0 0 t2_stk)).
{ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU2.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
unfold t2_stk. apply Forall_app; split; [apply (fl_saved_chunks_ok E memc sp0 regs0 32 HSV); intros j v Hj; exact (HK j v Hj)|].
constructor; [| constructor].
eapply (chunk_ok_val _ _ _ _ _ _ _ tv); [cbn [sv_denot]; rewrite Z.add_0_r, HE45, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact Wtv]. }
assert (HFA : atoms_ok E [(2%nat, mkAF (CEIL_MIN + FLUSH_STK - 272) (2^63 - 272) 4); (15%nat, mkAF 0 65535 0)]).
{ cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HU2, (HE 15%nat 15%bv eq_refl), G15, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. rewrite !Z.mod_1_r. try pose proof (proj1 alloc_ceiling_val) as HacR; clear - HacR Hceil Hsp063 Hal16 Hnp HFSv. repeat split; try lia.
replace (sp0 - 272) with (sp0 + (-17) * 16) by lia. rewrite Z.mod_add by lia. exact Hal16. }
assert (HCF : forall z : bool, (if z then Z.land g13 1 = 0 else Z.land g13 1 <> 0) ->
conds_ok E [mkAC (if z then BC_EQ else BC_NE) (SAlu ALU_AND (SOff 11 0) (SLit 1)) (SLit 0)]).
{ intros z Hz. cbn [conds_ok]. split; [|exact I]. unfold acond_ok.
destruct z; cbn [ac_c ac_a ac_b]; rewrite ?branch_eq_U, ?branch_ne_U, U_and_lit, U_lit, (U_atom _ 11 g13 ltac:(rewrite (HE 11%nat 11%bv eq_refl); exact G11)) by lia;
[rewrite Hz; reflexivity | destruct (Z.eqb_spec (Z.land g13 1) 0); [lia | reflexivity]]. }
assert (MK : forall z : bool, (if z then Z.land g13 1 = 0 else Z.land g13 1 <> 0) ->
st_ok src0segs E (ss_T z) (mkst regs1 (Z_to_bv 64 FL_T) memc (seg_rom src0segs))).
{ intros z Hz. unfold ss_T. apply entry_st_ok_full; [apply regs_ok_Ereg | vm_compute; destruct z; reflexivity | constructor; [exact HR0 | constructor] | cbn [pairwise_disjoint all_disjoint]; split; exact I | split; [exact HFA | split; [exact (HCF z Hz) | exact I]]]. }
clear HR0 HFA HCF.
change memc with (ms_mem (mkst regs1 (Z_to_bv 64 FL_T) memc (seg_rom src0segs))) in HJ.
destruct (Z.eq_dec (Z.land g13 1) 0) as [Hz | Hz].
-
pose proof (MK true Hz) as HS. clear MK.
jrun_to LAWS src0tbl_ok HS HJ FL_RAW. { apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
assert (K1 : forall x, ms_mem ms x = memc x).
{ intros x. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. reflexivity. }
clear HF HG.
lazymatch type of HS with st_ok _ ?Ef ?ssf ?msf =>
pose proof (regs_kept_of_st_ok src0segs Ef ssf msf regs1 _ [2; 3; 4; 8; 9; 26; 16; 20; 22; 19; 17; 5; 23; 24; 25]%bv HS (env_agree_refl _ _) ltac:(vm_compute; reflexivity)) as R end.
rewrite (st_ok_mkst src0segs _ _ _ HS eq_refl). cbn [ss_pc].
assert (XOFF : fl_tidx (gcfg_of s GPAL) cur bef = YO07.f_trans cur /\ fl_img (gcfg_of s GPAL) cur bef = fl_tmp (gcfg_of s GPAL) cur bef).
{ clear - Hz XTON. subst G. unfold fl_tidx, fl_img. unfold fl_trans_on in XTON. destruct bef as [bb|]; [| split; reflexivity].
destruct (YO07.flag (fl_gen3 (gcfg_of s GPAL) cur (Some bb)) 1); [exfalso; apply (proj2 XTON eq_refl); exact Hz |]. split; reflexivity. }
destruct XOFF as [XO1 XO2].
eapply (fl_tail API IMG RAWADDX L A mem md regs0 (ms_regs ms) Lc Ac (ms_mem ms) mdc g N s i f rest FP FPw tmp pTmp Nt tv w h FL_RAW S GPAL cur bef bfr brb bc top left ha);
[ exact HJ | exact Hid | exact Hra0 | exact Hal16 | exact Htp0 | | exact Hwf | exact Hi | exact Hf | exact HFP | exact HB
| destruct Htmp as [[A1 A2] | (A1 & A2 & A3)]; [left; split; [exact A1 | split; [exact A2 | rewrite HN; clear - Hw Hlw Hl0 Hh Hth Ht0; nia]] | right; auto]
| exact Htmp_fp | left; reflexivity
| clear - Hw Hlw Hl0; lia | clear - Hh Hth Ht0; lia | exact Htv
| apply (fl_saved_ok_kept memc); [exact HSV | intros a Ha; apply mbyte_of_eq; exact K1]
| intros k Hk; rewrite (mbyte_of_eq _ _ _ _ K1); exact (Wtv k Hk)
| rewrite (R 2%bv ltac:(cbv; auto 50)); exact G2 | rewrite (R 8%bv ltac:(cbv; auto 50)); exact G8 | rewrite (R 9%bv ltac:(cbv; auto 50)); exact G9
| rewrite (R 20%bv ltac:(cbv; auto 50)); exact G20 | rewrite (R 22%bv ltac:(cbv; auto 50)); exact G22 | rewrite (R 19%bv ltac:(cbv; auto 50)); exact G19
| rewrite (R 16%bv ltac:(cbv; auto 50)); exact G16 | rewrite (R 26%bv ltac:(cbv; auto 50)); exact G26
| split; [rewrite (R 3%bv ltac:(cbv; auto 50)); exact G3 | rewrite (R 4%bv ltac:(cbv; auto 50)); exact G4]
| exact Hbfr | exact HSINK
| eapply fl_vals_kept; [| exact HVALS]; intros a0 n0 k Hin Hk; apply mbyte_of_eq; exact K1
| rewrite (R 17%bv ltac:(cbv; auto 50)); exact G17 | rewrite (R 5%bv ltac:(cbv; auto 50)); exact G5
| rewrite (R 23%bv ltac:(cbv; auto 50)); exact G23 | rewrite (R 24%bv ltac:(cbv; auto 50)); exact G24 | rewrite (R 25%bv ltac:(cbv; auto 50)); exact G25
| exact Xha | exact Xw | exact Xh | exact Xtop | exact Xleft | exact Ht0 | exact Hth | exact Hl0 | exact Hlw
| rewrite XO1; exact Xtv0
| rewrite XO2; eapply garr8_frame; [exact XTMP|]; intros a Ha; apply mbyte_of_eq; exact K1
| rewrite XO2; exact XTMPL
| exact HRq
| destruct (Z.eq_dec pTmp 0) as [Hp0|Hp0]; [exact (proj1 (HNUM0 Hp0)) | exact (proj1 (HNUM1 Hp0))]
| intros Hp0; exact (proj1 (proj2 (HNUM0 Hp0)))
| intros Hp0; exact (proj2 (HNUM1 Hp0)) ].
eapply (cgif_at_kept0 memc _ g (flush_upd s i gen1 (rw_cur s)) N (cgif_blocks0 g s N ++ []) []); [rewrite (cgif_blocks_flush_upd0 g s N i gen1 (rw_cur s) f Hf); apply Permutation_refl | exact Hat |].
intros bb nn k Hbn Hk. apply mbyte_of_eq. exact K1.
-
destruct (Hbx Hz) as (b & befr & Hbfrb & Hbef & Hb & G18). subst bef.
pose proof (proj1 XTON Hz) as XT1. cbn [fl_trans_on] in XT1.
pose proof (MK false Hz) as HS. clear MK.
jrun_to LAWS src0tbl_ok HS HJ FL_P2. { apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
assert (K1 : forall x, ms_mem ms x = memc x).
{ intros x. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. reflexivity. }
clear HF HG.
lazymatch type of HS with st_ok _ ?Ef ?ssf ?msf =>
pose proof (regs_kept_of_st_ok src0segs Ef ssf msf regs1 _ [2; 3; 4; 17; 5; 8; 9; 14; 15; 26; 16; 18; 20; 22; 27; 19; 23; 24; 25]%bv HS (env_agree_refl _ _) ltac:(vm_compute; reflexivity)) as R end.
rewrite (st_ok_mkst src0segs _ _ _ HS eq_refl). cbn [ss_pc].
eapply SR_bind.
{ eapply (fl_pow2 API IMG 17%nat 0 FLUSH_STK sp0 FP L A mem md Lc Ac mdc (ms_regs ms) (ms_mem ms) np HJ ltac:(clear; lia) eq_refl Hnp).
- reg_nowF HS ltac:(reflexivity).
- reg_nowF HS ltac:(reflexivity).
- rewrite (R 15%bv ltac:(cbv; auto 50)). exact G15. }
cbv beta. intros c' (regs2 & mem2 & p & -> & Hm2 & HJ2 & Gp & Hp & XP & HK2).
assert (R2 : forall r : reg, In r [2; 3; 4; 17; 5; 8; 9; 14; 15; 26; 16; 18; 20; 22; 27; 19; 23; 24; 25]%bv -> getr regs2 r = getr regs1 r).
{ intros rr Hrr. rewrite <- (R rr Hrr). apply HK2. cbv in Hrr. repeat (destruct Hrr as [<- | Hrr]; [cbv; auto 50 |]). destruct Hrr. }
assert (Km : forall x, mem2 x = memc x) by (intros x; rewrite Hm2; apply K1).
eapply (fl_t2 L A mem md regs0 regs2 Lc Ac mem2 mdc g N s i f b rest FP FPw tmp pTmp Nt tv w h top left p np S GPAL cur befr brb bc ha);
[| exact Hb | | exact Gp | exact Hp | | exact Hnp
| exact HSINK
| eapply fl_vals_kept; [| rewrite <- Hbfrb; exact HVALS]; intros a0 n0 k Hin Hk; apply mbyte_of_eq; exact Km
| rewrite (R2 23%bv ltac:(cbv; auto 50)); exact G23 | rewrite (R2 24%bv ltac:(cbv; auto 50)); exact G24 | rewrite (R2 25%bv ltac:(cbv; auto 50)); exact G25
| exact Xha | exact Xw | exact Xh | exact Xtop | exact Xleft | exact XT1 | exact Xnp | rewrite XP; reflexivity
| eapply garr8_frame; [exact XTMP|]; intros a Ha; apply mbyte_of_eq; exact Km
| exact XTMPL | exact HRq
| intros Hp0; exact (proj2 (proj2 (HNUM0 Hp0)) XT1)
| exact HNUM1 ].
2:{ rewrite (R2 18%bv ltac:(cbv; auto 50)). exact G18. }
2:{ rewrite (R2 15%bv ltac:(cbv; auto 50)). exact G15. }
split; [exact HJ2|]. split; [exact Hid|]. split; [exact Hra0|]. split; [exact Hal16|]. split; [exact Htp0|].
split.
{ eapply (cgif_at_kept0 memc _ g (flush_upd s i gen1 (rw_cur s)) N (cgif_blocks0 g s N ++ []) []); [rewrite (cgif_blocks_flush_upd0 g s N i gen1 (rw_cur s) f Hf); apply Permutation_refl | exact Hat |].
intros bb nn k Hbn Hk. apply mbyte_of_eq. exact Km. }
split; [exact Hwf|]. split; [exact Hi|]. split; [exact Hf|]. split; [exact HFP|]. split; [exact HB|]. split; [exact Htmp|]. split; [exact Htmp_fp|].
split; [exact Hw|]. split; [exact Hl0|]. split; [exact Hlw|]. split; [exact Hh|]. split; [exact Ht0|]. split; [exact Hth|]. split; [exact Htv|].
split; [apply (fl_saved_ok_kept memc); [exact HSV | intros a Ha; apply mbyte_of_eq; exact Km]|].
split; [intros k Hk; rewrite (mbyte_of_eq _ _ _ _ Km); exact (Wtv k Hk)|].
split; [rewrite (R2 2%bv ltac:(cbv; auto 50)); exact G2|]. split; [rewrite (R2 8%bv ltac:(cbv; auto 50)); exact G8|]. split; [rewrite (R2 9%bv ltac:(cbv; auto 50)); exact G9|].
split; [rewrite (R2 20%bv ltac:(cbv; auto 50)); exact G20|]. split; [rewrite (R2 22%bv ltac:(cbv; auto 50)); exact G22|].
split; [rewrite (R2 19%bv ltac:(cbv; auto 50)); exact G19|]. split; [rewrite (R2 27%bv ltac:(cbv; auto 50)); exact G27|]. split; [rewrite (R2 14%bv ltac:(cbv; auto 50)); exact G14|].
split; [rewrite (R2 26%bv ltac:(cbv; auto 50)); exact G26|]. split; [rewrite (R2 16%bv ltac:(cbv; auto 50)); exact G16|].
split; [rewrite (R2 17%bv ltac:(cbv; auto 50)); exact G17|]. split; [rewrite (R2 5%bv ltac:(cbv; auto 50)); exact G5|].
split; [rewrite (R2 3%bv ltac:(cbv; auto 50)); exact G3 | rewrite (R2 4%bv ltac:(cbv; auto 50)); exact G4].
Qed.
End S.
End c.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
