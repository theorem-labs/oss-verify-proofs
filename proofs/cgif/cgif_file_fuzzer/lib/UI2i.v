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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UH00 UH03 UH02 UN3a UN3b YI06 UI5b YI09 YI08 YI0r UI1w UI1v UI4l UI21 UI2m UI3t UI5o UI5l YI6b UI5n UI20 UI1d UI2l.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UI25 UI2o UI2p.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UI2q UI2r.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YI14 YI13 UI5c.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO03 YO0p YO0j YO0m YO0l YO0n YO0k YO0o.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI00 YI01 UI3u UI22 YI5a UI5d YI0f YI2w UI2v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YO07.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO08.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition FL_F2 : Z := Eval vm_compute in (ubs0_A_flushFrame + 0xb4).
End d.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Section h. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma land3_mod4 : forall x, Z.land x 3 = x mod 4.
Proof using. intros x. change 3 with (Z.ones 2). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma U_and_slit : forall E x c, U E (SAlu ALU_AND x (SLit c)) = Z.land (U E x) (zcanon c).
Proof using.
intros E x c. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit. pose proof (U_range E x) as Hx.
assert (H0 : 0 <= zcanon c < M64) by (unfold zcanon, M64; apply Z.mod_pos_bound; lia).
apply zcanon_id. pose proof (land_le (U E x) (zcanon c) ltac:(lia)). unfold M64 in *. lia.
Qed.
Lemma land3_and_m4 : forall E x, Z.land (U E (SAlu ALU_AND x (SLit (-4)))) 3 = 0.
Proof using.
intros E x. rewrite U_and_slit. rewrite <- Z.land_assoc. change (Z.land (zcanon (-4)) 3) with 0. apply Z.land_0_r.
Qed.
Lemma land3_and_keep : forall E x c, Z.land (U E x) 3 = 0 -> Z.land (U E (SAlu ALU_AND x (SLit c))) 3 = 0.
Proof using.
intros E x c H. rewrite U_and_slit. rewrite (Z.land_comm (U E x)), <- Z.land_assoc, H. apply Z.land_0_r.
Qed.
Lemma land3_sext32 : forall E x, Z.land (U E (SExt true 32 x)) 3 = Z.land (U E x) 3.
Proof using.
intros E x. rewrite U_SExt. cbn [Z.of_N]. pose proof (U_range E x) as Hx.
rewrite !land3_mod4. unfold zcanon, M64, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
set (u := U E x) in *. clearbody u.
change (2 ^ Z.of_N 32) with (4 * 1073741824). change (2 ^ 64)%Z with (4 * 4611686018427387904).
change (2 ^ Z.of_N (32 - 1)) with (2 * 1073741824).
change (2 ^ 32) with (4 * 1073741824).
nia.
Qed.
Lemma land_bit_of3 : forall x m, (m = 1 \/ m = 2) -> Z.land x 3 = 0 -> Z.land x m = 0.
Proof using.
intros x m Hm H3. replace m with (Z.land 3 m) by (destruct Hm; subst; reflexivity).
rewrite Z.land_assoc, H3. apply Z.land_0_l.
Qed.
Lemma land3_mod32 : forall v, 0 <= v -> Z.land (v mod 2 ^ 32) 3 = Z.land v 3.
Proof using.
intros v Hv. rewrite !land3_mod4. change (2 ^ 32) with (4 * 1073741824). nia.
Qed.
End h.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section l. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma fl_trans_on_bit : forall g cur bef, (Z.land (fl_gen3 g cur bef) 1 <> 0 <-> fl_trans_on g cur bef = true).
Proof using.
intros g cur bef. unfold fl_trans_on. destruct bef as [b|].
- unfold YO07.flag. rewrite Bool.negb_true_iff, Z.eqb_neq. tauto.
- assert (Z0 : Z.land (fl_gen3 g cur None) 1 = 0).
{ unfold fl_gen3, fl_gen2, fl_gen1, YO07.clr.
assert (A3 : forall v, Z.land (Z.land v (Z.lnot 3)) 1 = 0) by (intros v; rewrite <- Z.land_assoc; change (Z.land (Z.lnot 3) 1) with 0; apply Z.land_0_r).
assert (A1 : forall v, Z.land v 1 = 0 -> Z.land (Z.land v (Z.lnot 1)) 1 = 0) by (intros v Hv; rewrite <- Z.land_assoc; change (Z.land (Z.lnot 1) 1) with 0; apply Z.land_0_r).
destruct (fl_npal g cur =? 256); destruct (fl_hasSet cur); repeat apply A1; apply A3. }
rewrite Z0. split; [intros H; exfalso; exact (H eq_refl) | intros H; discriminate H].
Qed.
Lemma fl_diff_some : forall g cur bef, YO07.flag (fl_gen3 g cur bef) 2 = true -> exists b, bef = Some b.
Proof using.
intros g cur bef H. destruct bef as [b|]; [exists b; reflexivity|]. exfalso.
assert (Z0 : Z.land (fl_gen3 g cur None) 2 = 0).
{ unfold fl_gen3, fl_gen2, fl_gen1, YO07.clr.
assert (A3 : forall v, Z.land (Z.land v (Z.lnot 3)) 2 = 0) by (intros v; rewrite <- Z.land_assoc; change (Z.land (Z.lnot 3) 2) with 0; apply Z.land_0_r).
assert (A1 : forall v, Z.land v 2 = 0 -> Z.land (Z.land v (Z.lnot 1)) 2 = 0) by (intros v Hv; rewrite <- Z.land_assoc, (Z.land_comm (Z.lnot 1) 2), Z.land_assoc, Hv; reflexivity).
destruct (fl_npal g cur =? 256); destruct (fl_hasSet cur); repeat apply A1; apply A3. }
unfold YO07.flag in H. rewrite Z0 in H. discriminate H.
Qed.
Lemma fl_dims_nodiff : forall g cur bef, YO07.flag (fl_gen3 g cur bef) 2 = false ->
fl_dims g cur bef = (YO07.g_w g, YO07.g_h g, 0, 0) /\ fl_tmp g cur bef = YO07.f_img cur.
Proof using. intros g cur bef H. unfold fl_tmp, fl_dims. destruct bef; [rewrite H|]; split; reflexivity. Qed.
Lemma land_mod_pow2 : forall a b n, 0 <= n -> (Z.land a b) mod 2 ^ n = Z.land (a mod 2 ^ n) (b mod 2 ^ n).
Proof using.
intros a b n Hn. apply Z.bits_inj'. intros k Hk. rewrite Z.land_spec.
destruct (Z.ltb_spec k n) as [Hlt|Hge].
- rewrite !Z.mod_pow2_bits_low by lia. apply Z.land_spec.
- rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.
Lemma land_low32_small : forall x m, 0 <= m < 2 ^ 32 -> Z.land (x mod 2 ^ 32) m = Z.land x m.
Proof using.
intros x m Hm. rewrite <- (Z.mod_small m (2 ^ 32)) at 1 by lia. rewrite <- land_mod_pow2 by lia.
apply Z.mod_small. pose proof (land_le x m ltac:(lia)). lia.
Qed.
Lemma clr1_low32 : forall v, 0 <= v < 2 ^ 32 -> Z.land v (2 ^ 32 - 2) = YO07.clr v 1.
Proof using.
intros v Hv. unfold YO07.clr. change (2 ^ 32 - 2) with ((Z.lnot 1) mod 2 ^ 32).
apply Z.bits_inj'. intros k Hk. rewrite !Z.land_spec.
destruct (Z.ltb_spec k 32) as [Hlt|Hge].
- rewrite Z.mod_pow2_bits_low by lia. reflexivity.
- assert (Hb : Z.testbit v k = false).
{ destruct (Z.eq_dec v 0) as [->|Hz]; [apply Z.bits_0|]. apply Z.bits_above_log2; [lia|]. assert (Z.log2 v < 32) by (apply Z.log2_lt_pow2; lia). lia. }
rewrite Hb. reflexivity.
Qed.
Definition fl_RgM : YP09.region := YP09.mkRegion (Some 80%nat) 0 96 0 0 (obj_chunks_gen LAY_CGIF A_X fl_litsG).
Definition fl_Rf16 (wlo whi : Z) : YP09.region := YP09.mkRegion (Some 16%nat) 0 40 wlo whi (obj_chunks_gen LAY_Frame A_F []).
Definition fl_f2_stk : list YP09.chunk := fl_stk_saved 32 ++ [mkChunk 112 (CVal 8 (SOff 80 0)); mkChunk 120 (CVal 8 (SOff 16 0))].
Definition fl_f2_facts : list (nat * afact) :=
[ (2%nat, mkAF (CEIL_MIN + FLUSH_STK - 272) (2^63 - 272) 4); (80%nat, mkAF 4096 (CEIL_MAX - 96) 4);
(16%nat, mkAF 4096 (CEIL_MAX - 40) 3) ].
Definition ss_f2 (u : Z) : sstate :=
mkSS FL_F2 (sr_set sr_atoms 12%bv (SLit u))
[ YP09.mkRegion (Some 2%nat) 0 272 0 168 fl_f2_stk ; fl_RgM ; fl_Rf16 20 24 ] None
(mkFacts (fl_f2_facts ++ fl_gfacts ++ fl_ffacts) [] []).
Section S.
Variable API : AllocAPI ubs0_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs0_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs0_msyms MR.
Hypothesis RAWADDX : rawadd_specX API.
Definition diff_pre L A mem md (regs0 regs1 : bvmap 5 word) Lc Ac memc mdc (g N : Z) (s : cgif_st) (i : nat) (f b : frame_st) (gen1 : Z)
(rest FP : list (Z * Z)) (tv np : Z) : Prop :=
let sp0 := spZ regs0 in
journal ubs0_msyms MR FLUSH_STK sp0 FP L A mem md Lc Ac memc mdc /\ st_init_done Ac = true /\
YK0s.ret_ok (getr regs0 1) /\ sp0 mod 16 = 0 /\ getr regs0 4 = Z_to_bv 64 (ms_tp ubs0_msyms) /\
cgif_at memc g (flush_upd s i gen1 (rw_cur s)) /\ cgif_wf s N /\ (i = 1%nat \/ i = 2%nat) /\ nth_error (cg_frames s) i = Some (Some f) /\
nth_error (cg_frames s) (i - 1) = Some (Some b) /\
fl_fp FP s f /\
Permutation (blocks Lc Ac) (cgif_blocks0 g s N ++ rest) /\ 0 <= tv < 2 ^ 64 /\ 0 <= np <= 65535 /\
fl_saved_ok memc sp0 regs0 /\
word_mem ubs0segs memc (sp0 - 272 + 112) g /\ word_mem ubs0segs memc (sp0 - 272 + 120) (fr_ptr f) /\
word_mem ubs0segs memc (sp0 - 272 + 56) (Z.land (fr_attr f) 1) /\ word_mem ubs0segs memc (sp0 - 272 + 104) (cg_W s) /\
getr regs1 2 = Z_to_bv 64 (sp0 - 272) /\ getr regs1 9 = Z_to_bv 64 tv /\
getr regs1 18 = Z_to_bv 64 (fr_ptr b) /\ getr regs1 19 = Z_to_bv 64 (cg_H s) /\ getr regs1 27 = Z_to_bv 64 (cg_W s) /\
getr regs1 20 = Z_to_bv 64 np /\
fl_untouched regs0 regs1.
Definition diff_specX : Prop :=
forall L A mem md regs0 regs1 Lc Ac memc mdc g N s i f b rest FP FPw tv np S GPAL cur befr brb bc ha,
diff_pre L A mem md regs0 regs1 Lc Ac memc mdc g N s i f b (fl_gen3 (gcfg_of s GPAL) cur (Some befr)) rest FP tv np ->
fl_sink g s N rest FP FPw S L A mem md (spZ regs0) ->
fl_vals memc s N f (Some b) GPAL cur (Some befr) ->
bv_unsigned (getr regs1 10) mod 2 ^ 32 = fr_attr f ->
getr regs1 14 = Z_to_bv 64 (fr_disp f) -> word_mem ubs0segs memc (spZ regs0 - 272 + 32) (fr_disp f) ->
word_mem ubs0segs memc (spZ regs0 - 272 + 16) (Z.land (fr_attr f) 4) ->
getr regs1 15 = Z_to_bv 64 ha -> word_mem ubs0segs memc (spZ regs0 - 272 + 24) ha ->
ha = (if fl_hasAlpha (gcfg_of s GPAL) cur then 1 else 0) ->
np = fl_npal (gcfg_of s GPAL) cur -> tv mod 256 = YO07.f_trans cur ->
YO07.flag (fl_gen3 (gcfg_of s GPAL) cur (Some befr)) 2 = true ->
(forall n, 0 < n <= N -> room bc n /\ rawadd_room (rb_malloc bc n) n /\ rb_le (rb_free (rawadd_rb (rb_malloc bc n)) n) (flush_rb brb)) -> res_ok Ac bc ->
SR ubs0segs (mkCfg (mkst regs1 (Z_to_bv 64 FL_DIFF) memc (seg_rom ubs0segs)) mdc) (fl_post API regs0 g s N i rest FPw S GPAL cur (Some befr) brb L A mem md).
Hypothesis DIFFX : diff_specX.
Lemma fl_vblocks_sep0 : forall L A m md g s N rest i f bfr y,
heap_ok MR L A m md -> Permutation (blocks L A) (cgif_blocks0 g s N ++ rest) ->
nth_error (cg_frames s) i = Some (Some f) -> (bfr = None \/ exists j b', bfr = Some b' /\ nth_error (cg_frames s) j = Some (Some b') /\ j <> i) ->
In y (fl_vblocks s N f bfr) -> fr_ptr f + FRAME_SIZE <= fst y \/ fst y + snd y <= fr_ptr f.
Proof using LAWS.
intros L A m md g s N rest i f bfr y HH HB Hf Hbfr Hy.
destruct (nth_error_split _ _ Hf) as (l1 & l2 & Hfr & Hl1).
assert (HP : Permutation (cgif_blocks0 g s N ++ rest)
((fr_ptr f, FRAME_SIZE) :: (g, CGIF_SIZE) :: (cg_raw s, RAW_SIZE) ::
(pal_blocks s ++ frames_blocks N l1 ++ (fr_img f, N) :: (if Z.land (fr_attr f) 1 =? 0 then [] else [(fr_lpal f, 3 * fr_nlp f)]) ++ frames_blocks N l2) ++ rest)).
{ unfold cgif_blocks0. rewrite Hfr, frames_blocks_app. cbn [frames_blocks flat_map]. fold (frames_blocks N l2). unfold frame_blocks at 1.
apply perm_frame_front. }
pose proof (heap_sep_perm _ _ LAWS L A m md (fr_ptr f, FRAME_SIZE) _ y HH (Permutation_trans HB HP)) as Hs.
cbn [fst snd] in Hs. apply Hs. right. right. apply in_app_iff. left.
unfold fl_vblocks in Hy. apply in_app_iff in Hy as [Hy|Hy]; [apply in_app_iff; left; exact Hy|].
apply in_app_iff. right. apply in_app_iff in Hy as [Hy|Hy].
- apply in_app_iff. right. unfold fr_vblocks in Hy. destruct Hy as [<-|Hy]; [left; reflexivity | right; apply in_app_iff; left; exact Hy].
- destruct Hbfr as [-> | (j & b' & -> & Hj & Hji)]; [destruct Hy|].
assert (Hb2 : In (Some b') (l1 ++ l2)).
{ rewrite Hfr in Hj. destruct (Nat.lt_ge_cases j (length l1)) as [Hlt|Hge].
- apply in_app_iff. left. rewrite nth_error_app1 in Hj by exact Hlt. eapply nth_error_In. exact Hj.
- apply in_app_iff. right. rewrite nth_error_app2 in Hj by exact Hge.
destruct (j - length l1)%nat as [|k] eqn:Hk; [lia|]. cbn in Hj. eapply nth_error_In. exact Hj. }
pose proof (fr_vblocks_frame_blocks N b' y Hy) as Hy'.
apply in_app_iff in Hb2 as [Hb2|Hb2].
+ apply in_app_iff. left. unfold frames_blocks. apply in_flat_map. exists (Some b'). split; [exact Hb2 | exact Hy'].
+ apply in_app_iff. right. right. apply in_app_iff. right. unfold frames_blocks. apply in_flat_map. exists (Some b'). split; [exact Hb2 | exact Hy'].
Qed.
Lemma fl_f2 :
forall L A mem md (regs0 regs1 : bvmap 5 word) Lc Ac memc mdc (g N : Z) (s : cgif_st) (i : nat) (f : frame_st) (gena : Z) (rest FP FPw : list (Z * Z))
(S GPAL : list Z) (cur : YO07.frame) (bfr : option frame_st) (bef : option YO07.frame) (brb : rbound) (ha : Z),
let sp0 := spZ regs0 in
let G := gcfg_of s GPAL in
journal ubs0_msyms MR FLUSH_STK sp0 FP L A mem md Lc Ac memc mdc -> st_init_done Ac = true ->
YK0s.ret_ok (getr regs0 1) -> sp0 mod 16 = 0 -> getr regs0 4 = Z_to_bv 64 (ms_tp ubs0_msyms) ->
cgif_at memc g (flush_upd s i gena (rw_cur s)) -> cgif_wf s N -> (i = 1%nat \/ i = 2%nat) -> nth_error (cg_frames s) i = Some (Some f) ->
(nth (i - 1) (cg_frames s) None = None -> Z.land gena 3 = 0) -> 0 <= gena < 2 ^ 32 ->
fl_fp FP s f ->
Permutation (blocks Lc Ac) (cgif_blocks0 g s N ++ rest) ->
fl_saved_ok memc sp0 regs0 ->
getr regs1 2 = Z_to_bv 64 (sp0 - 272) -> word_mem ubs0segs memc (sp0 - 272 + 112) g -> word_mem ubs0segs memc (sp0 - 272 + 120) (fr_ptr f) ->
getr regs1 16 = Z_to_bv 64 (fr_ptr f) ->
getr regs1 18 = Z_to_bv 64 (frame_ptr (nth (i - 1) (cg_frames s) None)) ->
getr regs1 12 = Z_to_bv 64 (Z.land (fr_attr f) 1) -> getr regs1 27 = Z_to_bv 64 (cg_W s) -> getr regs1 19 = Z_to_bv 64 (cg_H s) ->
fl_untouched regs0 regs1 ->
nth (i - 1) (cg_frames s) None = bfr ->
fl_sink g s N rest FP FPw S L A mem md sp0 ->
fl_vals memc s N f bfr GPAL cur bef ->
bv_unsigned (getr regs1 10) mod 2 ^ 32 = fr_attr f ->
getr regs1 13 = Z_to_bv 64 (Z.land (fr_attr f) 4) -> getr regs1 15 = Z_to_bv 64 ha -> ha = (if fl_hasAlpha G cur then 1 else 0) ->
gena = fl_gen2 G cur bef ->
(forall n, 0 < n <= N -> room brb n /\ rawadd_room (rb_malloc brb n) n /\ rb_le (rb_free (rawadd_rb (rb_malloc brb n)) n) (flush_rb brb)) ->
rawadd_room brb N -> rb_le (rawadd_rb brb) (flush_rb brb) -> res_ok Ac brb ->
SR ubs0segs (mkCfg (mkst regs1 (Z_to_bv 64 FL_F2) memc (seg_rom ubs0segs)) mdc) (fl_post API regs0 g s N i rest FPw S GPAL cur bef brb L A mem md).
Proof using DIFFX IMG RAWADDX.
intros L A mem md regs0 regs1 Lc Ac memc mdc g N s i f gena rest FP FPw S GPAL cur bfr bef brb ha sp0 G
HJ Hid Hra0 Hal16 Htp0 Hat Hwf Hi Hf Hgena Rgena HFP HB HSV G2 W112 W120 G16 G18 G12 G27 G19 [G3 G4]
Hbfr HSINK HVALS R10f G13 G15 Xha Xgena HNUM HRR0 HRB0 HRq.
pose proof HVALS as (HVg & HVf & HVb & HVra). pose proof HVf as (XA1 & XA2 & XA3 & XA4 & XA5 & XA6 & XA7 & XVI & XVIl & HVlp).
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HFSv : FLUSH_STK = 9216) by reflexivity.
assert (HGSv : CGIF_SIZE = 96) by reflexivity. assert (HRWv : RAW_SIZE = 48) by reflexivity. assert (HFRv : FRAME_SIZE = 40) by reflexivity.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HH0.
pose proof HJ as (_ & _ & _ & _ & _ & (Hsp0al & Hstk0 & Hceil & Hsp063 & Hstw) & _).
pose proof Hwf as (Hlen & HW1 & HH1 & HN & HNle & Hngp & _ & Hfwf).
set (s1 := flush_upd s i gena (rw_cur s)) in Hat. set (f1 := set_fr_gen f gena).
assert (Hfin : In (Some f) (cg_frames s)) by (eapply nth_error_In; exact Hf).
assert (Hilt : (i < length (cg_frames s))%nat) by (apply (proj1 (nth_error_Some _ _)); rewrite Hf; discriminate).
assert (Hfr1 : cg_frames s1 = list_set (cg_frames s) i (Some f1)) by (subst s1 f1; apply cg_frames_flush_upd; exact Hf).
assert (Hf1in : In (Some f1) (cg_frames s1)) by (rewrite Hfr1; eapply nth_error_In; apply nth_error_list_set_same; exact Hilt).
destruct (af_cgif_geom0 API Lc Ac memc mdc g s N _ HH0 HB) as ((Hr0 & Hr1 & Hrg) & Hfgeom & (Hg0 & Hg1 & Hg16)).
destruct (Hfgeom f Hfin) as (Hp0 & Hp1 & Hpg).
destruct (fl_img_geom0 API Lc Ac memc mdc g s N _ f HH0 HB Hfin ltac:(rewrite HN; clear - HW1 HH1; nia)) as [Him0 Him1].
pose proof Hat as (Hobj & Hraw & Hfrs). rewrite (cgif_vals_flush_upd s i gena (rw_cur s) : cgif_vals s1 = cgif_vals s) in Hobj.
pose proof (Hfrs f1 Hf1in) as Hfobj. change (fr_ptr f1) with (fr_ptr f) in Hfobj.
pose proof (obj_at_range _ _ _ _ _ Hobj) as Rg. pose proof (obj_at_range _ _ _ _ _ Hfobj) as Rf.
pose proof (Rg 7%nat (cg_W s) eq_refl) as RW. pose proof (Rg 8%nat (cg_H s) eq_refl) as RH. pose proof (Rg 9%nat (cg_ngp s) eq_refl) as Rngp. cbn [nth snd LAY_CGIF Z.of_N] in RW, RH, Rngp.
pose proof (Rf 2%nat (fr_attr f) eq_refl) as Rfattr. pose proof (Rf 5%nat (fr_nlp f) eq_refl) as Rnlp. pose proof (Rf 8%nat (fr_tidx f) eq_refl) as Rtidx.
cbn [nth snd LAY_Frame LAY_FrameConfig app Z.of_N] in Rfattr, Rnlp, Rtidx.
set (u := Z.land (fr_attr f) 1) in G12. assert (Hu : u = 0 \/ u = 1) by (subst u; apply land1_cases; clear - Rfattr; lia).
assert (Hudef : u = Z.land (fr_attr f) 1) by reflexivity. clearbody u.
set (E := fl_E regs1 regs0 s f1 None [g]).
pose proof (fl_HE regs1 regs0 s f1 None [g] : forall n rr, _ -> ew E n = _) as HE.
pose proof (fl_HK regs1 regs0 s f1 None [g] : forall n j v, _ -> _ -> ew E n = _) as HK.
pose proof (fl_HX regs1 regs0 s f1 None [g] : forall n j v, _ -> _ -> ew E n = _) as HX.
pose proof (fl_HF regs1 regs0 s f1 None [g] : forall n j v, _ -> _ -> ew E n = _) as HFf.
assert (HE80 : ew E 80 = Z_to_bv 64 g) by (apply (fl_HM regs1 regs0 s f1 None [g] 80%nat 0%nat g eq_refl eq_refl)).
assert (HU2 : bv_unsigned (ew E 2) = sp0 - 272) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; clear - Hceil Hsp063 HFSv Hac; lia).
assert (HU80 : bv_unsigned (ew E 80) = g) by (rewrite HE80; apply unsigned_lit_small; clear - Hg0 Hg1 Hac HGSv; lia).
assert (HU16 : bv_unsigned (ew E 16) = fr_ptr f) by (rewrite (HE 16%nat 16%bv eq_refl), G16; apply unsigned_lit_small; clear - Hp0 Hp1 Hac HFRv; lia).
assert (HE65 : ew E 65 = Z_to_bv 64 gena) by (apply (HFf 65%nat 3%nat _ eq_refl eq_refl)).
assert (HE70 : ew E 70 = Z_to_bv 64 (fr_tidx f)) by (apply (HFf 70%nat 8%nat _ eq_refl eq_refl)).
assert (HE54 : ew E 54 = Z_to_bv 64 (cg_ngp s)) by (apply (HX 54%nat 9%nat _ eq_refl eq_refl)).
assert (HE67 : ew E 67 = Z_to_bv 64 (fr_nlp f)) by (apply (HFf 67%nat 5%nat _ eq_refl eq_refl)).
assert (HE69 : ew E 69 = Z_to_bv 64 (fr_disp f)) by (apply (HFf 69%nat 7%nat _ eq_refl eq_refl)).
pose proof (Rf 7%nat (fr_disp f) eq_refl) as Rdisp. cbn [nth snd LAY_Frame LAY_FrameConfig app Z.of_N] in Rdisp.
assert (XNP0 : u = 0 -> U E (SOff 54 0) = fl_npal G cur).
{ intros Hu0. rewrite (U_atom _ 54 (cg_ngp s) HE54) by (clear - Rngp; lia). unfold fl_npal, fl_useLCT, YO07.flag. rewrite <- XA1, <- Hudef, Hu0. reflexivity. }
assert (XNP1 : u = 1 -> U E (SOff 67 0) = fl_npal G cur).
{ intros Hu1. rewrite (U_atom _ 67 (fr_nlp f) HE67) by (clear - Rnlp; lia). unfold fl_npal, fl_useLCT, YO07.flag. rewrite <- XA1, <- Hudef, Hu1. cbn. exact XA4. }
assert (UE0 : U E (SOff 65 0) mod 2 ^ 32 = gena) by (rewrite (U_atom _ 65 gena HE65) by (clear - Rgena; lia); apply Z.mod_small; exact Rgena).
assert (UE2 : U E (SAlu ALU_AND (SOff 65 0) (SLit (-2))) mod 2 ^ 32 = YO07.clr gena 1).
{ rewrite U_and_slit, land_mod_pow2, UE0 by (clear; lia). change (zcanon (-2) mod 2 ^ 32) with (2 ^ 32 - 2). apply clr1_low32. exact Rgena. }
assert (XG3 : forall np, np = fl_npal G cur -> (np <> 256 -> fl_gen3 G cur bef = gena) /\ (np = 256 -> fl_gen3 G cur bef = YO07.clr gena 1)).
{ intros np Hnp. unfold fl_gen3. fold G. rewrite <- Hnp, <- Xgena. split; intros H256.
- destruct (Z.eqb_spec np 256); [exfalso; exact (H256 ltac:(assumption)) | reflexivity].
- rewrite H256. reflexivity. }
assert (Hfblk : In (fr_ptr f, FRAME_SIZE) (blocks Lc Ac)).
{ apply (Permutation_in _ (Permutation_sym HB)). apply in_app_iff. left. apply (frame_blocks_in_cgif0 g s N f); [exact Hfin | left; reflexivity]. }
assert (HR0 : region_ok ubs0segs E memc (YP09.mkRegion (Some 2%nat) 0 272 0 168 fl_f2_stk)).
{ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU2.
split; [lia|]. split; [lia|]. split; [intros o Ho; apply Hstw; lia|].
unfold fl_f2_stk. apply Forall_app; split; [apply (fl_saved_chunks_ok E memc sp0 regs0 32 HSV); intros j v Hj; exact (HK _ j v eq_refl Hj)|].
constructor; [| constructor; [| constructor]].
- eapply (chunk_ok_val _ _ _ _ _ _ _ g); [cbn [sv_denot]; rewrite Z.add_0_r, HE80, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact W112].
- eapply (chunk_ok_val _ _ _ _ _ _ _ (fr_ptr f)); [cbn [sv_denot]; rewrite Z.add_0_r, (HE 16%nat 16%bv eq_refl), G16, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact W120]. }
assert (HR1 : region_ok ubs0segs E memc fl_RgM).
{ unfold fl_RgM, fl_litsG, A_X. eapply (region_ok_obj_gen ubs0segs E memc 80 g 96 0 0 LAY_CGIF (cgif_vals s) 45 (litsG None None None None));
[exact HU80 | lia | lia | exact Hobj | reflexivity | | apply (litsG_ok s); exact I | intros k Hk; lia].
intros j v Hj. apply (HX (45 + j)%nat j v eq_refl Hj). }
assert (HR2 : region_ok ubs0segs E memc (fl_Rf16 20 24)).
{ unfold fl_Rf16, A_F. eapply (region_ok_obj_gen ubs0segs E memc 16 (fr_ptr f) 40 20 24 LAY_Frame (frame_vals f1) 62 []);
[exact HU16 | lia | lia | exact Hfobj | reflexivity | | intros [|j] z Hz; discriminate Hz | ].
- intros j v Hj. apply (HFf (62 + j)%nat j v eq_refl Hj).
- intros k Hk. apply (present_writable ubs0_msyms). apply (proj1 (heap_blocks _ _ LAWS Lc Ac memc mdc (fr_ptr f) FRAME_SIZE k HH0 Hfblk ltac:(clear - Hk HFRv; lia))). }
assert (HPD : pairwise_disjoint E (ss_mem (ss_f2 u))).
{ cbn [ss_mem ss_f2]. unfold fl_RgM, fl_Rf16. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val].
rewrite HU2, HU80, HU16. clear - Hg1 Hp1 Hpg Hceil HFSv HGSv HFRv Hac. repeat split; lia. }
assert (Hp8 : fr_ptr f mod 8 = 0).
{ pose proof (heap_blocks_range _ _ LAWS Lc Ac memc mdc (fr_ptr f) FRAME_SIZE HH0 Hfblk ltac:(lia)) as (_ & _ & H16).
clear - H16. apply Z.mod_divide in H16; [|lia]. apply Z.mod_divide; [lia|]. destruct H16 as [q Hq]. exists (q * 2). lia. }
assert (HFA : atoms_ok E (fl_f2_facts ++ fl_gfacts ++ fl_ffacts)).
{ apply atoms_ok_app; [| apply atoms_ok_app; [exact (fl_gfacts_ok regs1 regs0 s f1 None [g] memc g N Hobj Hwf ltac:(lia) ltac:(lia))
| exact (fl_ffacts_ok regs1 regs0 s f1 None [g] memc (fr_ptr f) Hfobj Him0 ltac:(change (fr_img f1) with (fr_img f); clear - Him1 HN HW1 HH1; nia))]].
cbn [atoms_ok fl_f2_facts]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HU2, HU80, HU16.
change (2 ^ 4) with 16. change (2 ^ 3) with 8. clear - Hceil Hsp063 Hal16 Hg0 Hg1 Hg16 Hp0 Hp1 Hp8 HFSv HGSv HFRv Hac. repeat split; try lia.
replace (sp0 - 272) with (sp0 + (-17) * 16) by lia. rewrite Z.mod_add by lia. exact Hal16. }
assert (HS : st_ok ubs0segs E (ss_f2 u) (mkst regs1 (Z_to_bv 64 FL_F2) memc (seg_rom ubs0segs))).
{ unfold ss_f2. apply entry_st_ok_full; [| vm_compute; reflexivity | | exact HPD | split; [exact HFA | split; exact I]].
- apply regs_ok_pin; [apply regs_ok_Ereg | intros Hx; discriminate Hx |]. rewrite G12. reflexivity.
- constructor; [exact HR0|]. constructor; [exact HR1|]. constructor; [exact HR2|]. constructor. }
clear HR0 HR1 HR2 HPD HFA.
change memc with (ms_mem (mkst regs1 (Z_to_bv 64 FL_F2) memc (seg_rom ubs0segs))) in HJ.
assert (WR : forall E0 cs fcs, bv_unsigned (ew E0 2) = sp0 - 272 -> bv_unsigned (ew E0 16) = fr_ptr f ->
wr_ok E0 [YP09.mkRegion (Some 2%nat) 0 272 0 168 cs; fl_RgM; YP09.mkRegion (Some 16%nat) 0 40 20 24 fcs] FLUSH_STK sp0 FP (blocks L A) (blocks Lc Ac)).
{ intros E0 cs fcs H2 H16. eapply wr_ok_cons_win; [reflexivity | exact H2 | cbn [r_wlo r_whi]; intros _; lia |].
apply wr_ok_cons_ro; [cbn; lia|].
eapply (wr_ok_cons_block E0 (YP09.mkRegion (Some 16%nat) 0 40 20 24 fcs) [] FLUSH_STK sp0 FP (blocks L A) (blocks Lc Ac) 16 (fr_ptr f) FRAME_SIZE eq_refl H16 Hfblk); [cbn; lia | cbn; clear - HFRv; lia | | apply wr_ok_nil].
cbn [r_wlo r_whi]. intros a Ha. exact (proj2 HFP a Ha). }
assert (KSTEP : forall E0 cs fcs (m m' : word -> option byte),
bv_unsigned (ew E0 2) = sp0 - 272 -> bv_unsigned (ew E0 16) = fr_ptr f ->
frame_of E0 [YP09.mkRegion (Some 2%nat) 0 272 0 168 cs; fl_RgM; YP09.mkRegion (Some 16%nat) 0 40 20 24 fcs] m m' ->
forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 272 <= a < sp0 - 272 + 168) -> ~ (fr_ptr f + 20 <= a < fr_ptr f + 24) -> mbyte ubs0segs m' a = mbyte ubs0segs m a).
{ intros E0 cs fcs m m' H2 H16 HFx a Ha Hn1 Hn2. apply (mbyte_of_frame _ _ _ _ a HFx Ha). intros r Hr. cbv [In] in Hr.
repeat (destruct Hr as [<- | Hr]; [cbn [r_base r_wlo r_whi base_val fl_RgM]; rewrite ?H2, ?H16; clear - Hn1 Hn2; lia |]). destruct Hr. }
assert (FRo : forall x j v rcur, nth_error (cg_frames s) j = Some (Some x) -> j <> i -> In (Some x) (cg_frames (flush_upd s i v rcur))).
{ intros x j v rcur Hj Hji. rewrite (cg_frames_flush_upd s i v rcur f Hf). eapply (nth_error_In _ j). rewrite nth_error_list_set_other by lia. exact Hj. }
assert (CGAT : forall (m : word -> option byte) (v : Z),
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 272 <= a < sp0 - 272 + 168) -> ~ (fr_ptr f + 20 <= a < fr_ptr f + 24) -> mbyte ubs0segs m a = mbyte ubs0segs memc a) ->
field_ok ubs0segs m (fr_ptr f) (20, 4%N) v ->
cgif_at m g (flush_upd s i v (rw_cur s))).
{ intros m v K Hfld.
assert (KB : forall bb nn k, In (bb, nn) (cgif_blocks0 g s N) -> 0 <= k < nn -> (bb + nn <= fr_ptr f \/ fr_ptr f + FRAME_SIZE <= bb) ->
mbyte ubs0segs m (bb + k) = mbyte ubs0segs memc (bb + k)).
{ intros bb nn k Hbn Hk Hsep. assert (Hbn' : In (bb, nn) (blocks Lc Ac)) by (apply (Permutation_in _ (Permutation_sym HB)); apply in_app_iff; left; exact Hbn).
destruct (blocks_range _ _ LAWS Lc Ac memc mdc bb nn HH0 Hbn') as [R0 R1]. apply K; clear - R0 R1 Hk Hsep Hceil HFSv HFRv Hac; lia. }
split; [| split].
- rewrite (cgif_vals_flush_upd s i v (rw_cur s)). eapply obj_at_transport_range; [exact Hobj | exact (proj1 LAY_CGIF_ok) | intros k Hk; apply (KB g CGIF_SIZE k); [left; reflexivity | clear - Hk HGSv; lia | clear - Hpg; lia]].
- change (cg_raw (flush_upd s i v (rw_cur s))) with (cg_raw s).
pose proof (af_raw_frame_sep0 API Lc Ac memc mdc g s N _ f HH0 HB Hfin) as Hrf.
eapply obj_at_transport_range; [exact Hraw | exact (proj1 LAY_Raw_ok) | intros k Hk; apply (KB (cg_raw s) RAW_SIZE k); [right; left; reflexivity | clear - Hk HRWv; lia | clear - Hrf; lia]].
- intros x Hx. destruct (In_frames_flush_upd s i v (rw_cur s) f x Hf Hx) as [-> | [Hin (j & Hj & Hji)]].
+ change (fr_ptr (set_fr_gen f v)) with (fr_ptr f). rewrite frame_vals_set_fr_gen.
replace (list_set (frame_vals f) 3 v) with (list_set (frame_vals f1) 3 v) by reflexivity.
eapply (obj_at_upd ubs0segs memc m (fr_ptr f) LAY_Frame FRAME_SIZE (frame_vals f1) _ [3%nat] [(20, 24)]);
[exact Hfobj | exact (proj1 LAY_Frame_ok) | reflexivity | reflexivity | | | ].
* intros k Hk Hw. apply K; [clear - Hk Hp0 Hp1 HFRv Hac; lia | clear - Hk Hp1 Hceil HFSv HFRv Hac; lia |].
cbn [in_wins existsb fst snd] in Hw. clear - Hk Hw. intros Hc.
assert (Hb1 : (20 <=? k) && (k <? 24) = true) by (apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia). rewrite Hb1 in Hw. discriminate Hw.
* intros j0 fd v' Hj0 Hfd Hv'. destruct Hj0 as [<- | []]. cbn in Hfd, Hv'. injection Hfd as <-. injection Hv' as <-. exact Hfld.
* intros j0 Hj0. destruct (Nat.eq_dec j0 3) as [-> | Hne]; [exfalso; apply Hj0; left; reflexivity|].
do 9 (destruct j0 as [|j0]; [first [reflexivity | exfalso; lia] |]). reflexivity.
+ destruct (Hfgeom x Hin) as (X0 & X1 & _). pose proof (af_frames_sep0 API Lc Ac memc mdc g s N _ j i x f HH0 HB Hj Hf Hji) as Xf.
eapply obj_at_transport_range; [exact (Hfrs x (FRo x j gena (rw_cur s) Hj Hji)) | exact (proj1 LAY_Frame_ok) |].
intros k Hk. apply (KB (fr_ptr x) FRAME_SIZE k); [| clear - Hk HFRv; lia | clear - Xf; lia].
apply (frame_blocks_in_cgif0 g s N x _ _ Hin). left. reflexivity. }
assert (Hi1lt : (i - 1 < length (cg_frames s))%nat) by lia.
assert (SLOT : forall P : Prop, (forall b, nth_error (cg_frames s) (i - 1) = Some (Some b) -> frame_ptr (nth (i - 1) (cg_frames s) None) = fr_ptr b -> P) ->
(nth (i - 1) (cg_frames s) None = None -> Z.land gena 3 = 0 -> P) -> P).
{ intros P H1 H2. destruct (nth (i - 1) (cg_frames s) None) as [b|] eqn:Hn.
- apply (H1 b); [| reflexivity]. rewrite (nth_error_nth' _ None Hi1lt), Hn. reflexivity.
- apply H2; [reflexivity | apply Hgena; reflexivity]. }
assert (VSEP : forall y, In y (fl_vblocks s N f bfr) -> fr_ptr f + FRAME_SIZE <= fst y \/ fst y + snd y <= fr_ptr f).
{ intros y Hy. apply (fl_vblocks_sep0 Lc Ac memc mdc g s N rest i f bfr y HH0 HB Hf); [| exact Hy].
destruct bfr as [b'|]; [right | left; reflexivity]. exists (i - 1)%nat, b'. split; [reflexivity|]. split; [| clear - Hi; lia].
rewrite (nth_error_nth' _ None) by (clear - Hilt; lia). rewrite Hbfr. reflexivity. }
assert (VK : forall m, (forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 272 <= a < sp0 - 272 + 168) -> ~ (fr_ptr f + 20 <= a < fr_ptr f + 24) -> mbyte ubs0segs m a = mbyte ubs0segs memc a) ->
fl_vals m s N f bfr GPAL cur bef).
{ intros m K. eapply fl_vals_kept; [| exact HVALS]. intros a0 n0 k Hin Hk.
assert (Hbn' : In (a0, n0) (blocks Lc Ac)).
{ apply (Permutation_in _ (Permutation_sym HB)). apply in_app_iff. left.
apply (fl_vblocks_sub g s N f bfr i Hf); [| exact Hin]. destruct bfr as [b'|]; [right | left; reflexivity]. exists (i - 1)%nat.
rewrite (nth_error_nth' _ None) by (clear - Hilt; lia). rewrite Hbfr. reflexivity. }
destruct (blocks_range _ _ LAWS Lc Ac memc mdc a0 n0 HH0 Hbn') as [R0 R1]. pose proof (VSEP _ Hin) as X. cbn [fst snd] in X.
apply K; clear - R0 R1 Hk X Hceil HFSv HFRv Hac; lia. }
assert (NPE : forall npe, (npe = SOff 54 0 \/ npe = SOff 67 0) -> 0 <= U E npe <= 65535).
{ intros npe [-> | ->]; [rewrite (U_atom _ 54 (cg_ngp s) HE54) by (clear - Rngp; lia) | rewrite (U_atom _ 67 (fr_nlp f) HE67) by (clear - Rnlp; lia)]; [clear - Rngp | clear - Rnlp]; lia. }
assert (AE : forall ae, (ae = SOff 65 0 \/ ae = SAlu ALU_AND (SOff 65 0) (SLit (-2))) -> Z.land gena 3 = 0 -> Z.land (U E ae) 3 = 0).
{ intros ae [-> | ->] Hg3; [| apply land3_and_keep]; rewrite (U_atom _ 65 gena HE65) by (clear - Rgena; lia); exact Hg3. }
assert (K0 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 272 <= a < sp0 - 272 + 168) -> ~ (fr_ptr f + 20 <= a < fr_ptr f + 24) -> mbyte ubs0segs memc a = mbyte ubs0segs memc a) by (intros; reflexivity).
assert (GO_D : forall ss ms' (ae npe : sv), st_ok ubs0segs E ss ms' -> ss_pc ss = FL_DIFF -> ss_resv ss = None ->
(exists rg0 rg2, nth_error (ss_mem ss) 0 = Some rg0 /\ r_base rg0 = Some 2%nat /\ nth_error (ss_mem ss) 2 = Some rg2 /\ r_base rg2 = Some 16%nat /\
incl_chunks [mkChunk 112 (CVal 8 (SOff 80 0)); mkChunk 120 (CVal 8 (SOff 16 0)); mkChunk 56 (CVal 8 (SLit u)); mkChunk 104 (CVal 8 (SOff 27 0));
mkChunk 32 (CVal 8 (SOff 69 0)); mkChunk 16 (CVal 8 (SOff 13 0)); mkChunk 24 (CVal 8 (SOff 15 0))] (r_chunks rg0) = true /\
In (mkChunk 20 (CVal 4 ae)) (r_chunks rg2)) ->
forallb (fun r : reg => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) [2; 3; 4; 10; 15; 18; 19; 27]%bv = true ->
sr_get (ss_regs ss) 9%bv = SOff 70 0 -> sr_get (ss_regs ss) 14%bv = SOff 69 0 ->
sr_get (ss_regs ss) 11%bv = ae -> (Z.land gena 3 = 0 -> Z.land (U E ae) 3 = 0) -> Z.land (U E ae) 2 <> 0 ->
sr_get (ss_regs ss) 20%bv = npe -> 0 <= U E npe <= 65535 ->
U E npe = fl_npal G cur -> U E ae mod 2 ^ 32 = fl_gen3 G cur bef ->
journal ubs0_msyms MR FLUSH_STK sp0 FP L A mem md Lc Ac (ms_mem ms') mdc ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 272 <= a < sp0 - 272 + 168) -> ~ (fr_ptr f + 20 <= a < fr_ptr f + 24) -> mbyte ubs0segs (ms_mem ms') a = mbyte ubs0segs memc a) ->
SR ubs0segs (mkCfg ms' mdc) (fl_post API regs0 g s N i rest FPw S GPAL cur bef brb L A mem md)).
{ intros ss ms' ae npe HS' Hpc Hrv (rg0 & rg2 & Hrg0 & Hb0 & Hrg2 & Hb2 & Hincl & Hin20) Hkl Q9 Q14 Q11 Hae Hbit2 Q20 Hnpe Vnp Vae HJ' K.
assert (XG2 : YO07.flag (fl_gen3 G cur bef) 2 = true).
{ unfold YO07.flag. rewrite <- Vae, land_low32_small by (clear; lia). destruct (Z.eqb_spec (Z.land (U E ae) 2) 0) as [Hz|Hz]; [exfalso; exact (Hbit2 Hz) | reflexivity]. }
destruct (fl_diff_some G cur bef XG2) as [befr Hbef]. subst bef.
destruct bfr as [b'|]; [| exfalso; exact HVb].
pose proof (regs_kept_of_st_ok ubs0segs _ ss ms' regs1 _ _ HS' (env_agree_refl _ _) Hkl) as R.
pose proof (st_region_chunks ubs0segs E ss ms' 0 rg0 2%nat (sp0 - 272) HS' Hrg0 Hb0 HU2) as Hcs0.
apply incl_chunks_sound in Hincl.
assert (CW : forall off e v, In (mkChunk off (CVal 8 e)) [mkChunk 112 (CVal 8 (SOff 80 0)); mkChunk 120 (CVal 8 (SOff 16 0)); mkChunk 56 (CVal 8 (SLit u)); mkChunk 104 (CVal 8 (SOff 27 0));
mkChunk 32 (CVal 8 (SOff 69 0)); mkChunk 16 (CVal 8 (SOff 13 0)); mkChunk 24 (CVal 8 (SOff 15 0))] ->
sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> word_mem ubs0segs (ms_mem ms') (sp0 - 272 + off) v).
{ intros off e v Hin Hd Hv. exact (chunk_word E _ _ off e v (proj1 (Forall_forall _ _) Hcs0 _ (Hincl _ Hin)) Hd Hv). }
assert (RGx : forall (r : reg) sv, sr_get (ss_regs ss) r = sv -> getr (ms_regs ms') r = sv_denot E sv).
{ intros r sv Hr. rewrite (st_ok_reg ubs0segs E ss ms' r HS'), Hr. reflexivity. }
rewrite (st_ok_mkst ubs0segs _ _ _ HS' Hrv), Hpc.
apply SLOT; [| intros _ Hg3; exfalso; apply Hbit2; apply (land_bit_of3 _ 2 (or_intror eq_refl)); apply Hae; exact Hg3].
intros b Hb Hpb.
assert (Hbb : b' = b) by (pose proof (nth_error_nth _ _ None Hb) as X; rewrite Hbfr in X; injection X as X'; exact X'). subst b'.
pose proof (land_le (fr_attr f) 4 ltac:(clear; lia)) as L4.
apply (DIFFX L A mem md regs0 (ms_regs ms') Lc Ac (ms_mem ms') mdc g N s i f b rest FP FPw (fr_tidx f) (U E npe) S GPAL cur befr brb brb ha);
[| exact HSINK | apply VK; exact K
| rewrite (R 10%bv ltac:(cbv; auto 50)); exact R10f
| rewrite (RGx _ _ Q14); cbn [sv_denot]; rewrite Z.add_0_r, HE69, Z_to_bv_bv_unsigned; reflexivity
| apply (CW 32 (SOff 69 0)); [repeat (first [left; reflexivity | right]) | cbn [sv_denot]; rewrite Z.add_0_r, HE69, Z_to_bv_bv_unsigned; reflexivity | clear - Rdisp; lia]
| apply (CW 16 (SOff 13 0)); [repeat (first [left; reflexivity | right]) | cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (HE 13%nat 13%bv eq_refl); exact G13 | clear - L4; lia]
| rewrite (R 15%bv ltac:(cbv; auto 50)); exact G15
| apply (CW 24 (SOff 15 0)); [repeat (first [left; reflexivity | right]) | cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (HE 15%nat 15%bv eq_refl); exact G15 | rewrite Xha; destruct (fl_hasAlpha G cur); clear; lia]
| exact Xha | exact Vnp | rewrite XA7; apply Z.mod_small; rewrite <- XA7; exact Rtidx | exact XG2 | exact HNUM | exact HRq ].
split; [exact HJ'|]. split; [exact Hid|]. split; [exact Hra0|]. split; [exact Hal16|]. split; [exact Htp0|].
split.
{ change (fl_gen3 (gcfg_of s GPAL) cur (Some befr)) with (fl_gen3 G cur (Some befr)). rewrite <- Vae. apply (CGAT (ms_mem ms') (U E ae mod 2 ^ 32) K).
eapply (st_field_low ubs0segs E ss ms' 2 rg2 16 (fr_ptr f) 20 4 ae (2 ^ 32) HS' Hrg2 Hb2 Hin20 HU16 ltac:(cbn; lia) eq_refl). }
split; [exact Hwf|]. split; [exact Hi|]. split; [exact Hf|]. split; [exact Hb|]. split; [exact HFP|]. split; [exact HB|].
split; [clear - Rtidx; lia|]. split; [exact Hnpe|].
split; [apply (fl_saved_ok_kept memc); [exact HSV | intros a Ha; apply K; [clear - Ha Hceil Hsp063 HFSv Hac; lia | clear - Ha; lia | clear - Ha Hp1 Hceil HFSv HFRv Hac; lia]]|].
split; [apply (CW 112 (SOff 80 0)); [repeat (first [left; reflexivity | right]) | cbn [sv_denot]; rewrite Z.add_0_r, HE80, Z_to_bv_bv_unsigned; reflexivity | clear - Hg0 Hg1 Hac HGSv; lia]|].
split; [apply (CW 120 (SOff 16 0)); [repeat (first [left; reflexivity | right]) | cbn [sv_denot]; rewrite Z.add_0_r, (HE 16%nat 16%bv eq_refl), G16, Z_to_bv_bv_unsigned; reflexivity | clear - Hp0 Hp1 Hac HFRv; lia]|].
split; [apply (CW 56 (SLit u)); [repeat (first [left; reflexivity | right]) | cbn [sv_denot]; rewrite Hudef; reflexivity | rewrite <- Hudef; clear - Hu; lia]|].
split; [apply (CW 104 (SOff 27 0)); [repeat (first [left; reflexivity | right]) | cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (HE 27%nat 27%bv eq_refl); exact G27 | clear - RW; lia]|].
split; [rewrite (R 2%bv ltac:(cbv; auto 50)); exact G2|].
split; [rewrite (RGx _ _ Q9); cbn [sv_denot]; rewrite Z.add_0_r, HE70, Z_to_bv_bv_unsigned; reflexivity|].
split; [rewrite (R 18%bv ltac:(cbv; auto 50)), G18, Hpb; reflexivity|].
split; [rewrite (R 19%bv ltac:(cbv; auto 50)); exact G19|]. split; [rewrite (R 27%bv ltac:(cbv; auto 50)); exact G27|].
split; [rewrite (RGx _ _ Q20); apply denot_of_U'; reflexivity|].
split; [rewrite (R 3%bv ltac:(cbv; auto 50)); exact G3 | rewrite (R 4%bv ltac:(cbv; auto 50)); exact G4]. }
assert (GO_T : forall ss ms' (ae npe : sv), st_ok ubs0segs E ss ms' -> ss_pc ss = FL_T -> ss_resv ss = None ->
(exists rg0 rg2, nth_error (ss_mem ss) 0 = Some rg0 /\ r_base rg0 = Some 2%nat /\ nth_error (ss_mem ss) 2 = Some rg2 /\ r_base rg2 = Some 16%nat /\
incl_chunks [mkChunk 96 (CVal 8 (SLit 0)); mkChunk 112 (CVal 8 (SOff 80 0)); mkChunk 120 (CVal 8 (SOff 16 0)); mkChunk 56 (CVal 8 (SLit u)); mkChunk 104 (CVal 8 (SOff 27 0));
mkChunk 32 (CVal 8 (SOff 69 0)); mkChunk 16 (CVal 8 (SOff 13 0)); mkChunk 24 (CVal 8 (SOff 15 0))] (r_chunks rg0) = true /\
In (mkChunk 20 (CVal 4 ae)) (r_chunks rg2)) ->
forallb (fun r : reg => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) [2; 3; 4; 15; 18; 19; 27]%bv = true ->
sr_get (ss_regs ss) 9%bv = SOff 70 0 -> sr_get (ss_regs ss) 14%bv = SOff 69 0 -> sr_get (ss_regs ss) 8%bv = SLit 0 -> sr_get (ss_regs ss) 22%bv = SLit 0 ->
sr_get (ss_regs ss) 16%bv = SOff 19 0 -> sr_get (ss_regs ss) 23%bv = SOff 27 0 ->
sr_get (ss_regs ss) 11%bv = ae -> sr_get (ss_regs ss) 20%bv = npe -> 0 <= U E npe <= 65535 ->
U E npe = fl_npal G cur -> U E ae mod 2 ^ 32 = fl_gen3 G cur bef -> Z.land (U E ae) 2 = 0 ->
journal ubs0_msyms MR FLUSH_STK sp0 FP L A mem md Lc Ac (ms_mem ms') mdc ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 272 <= a < sp0 - 272 + 168) -> ~ (fr_ptr f + 20 <= a < fr_ptr f + 24) -> mbyte ubs0segs (ms_mem ms') a = mbyte ubs0segs memc a) ->
SR ubs0segs (mkCfg ms' mdc) (fl_post API regs0 g s N i rest FPw S GPAL cur bef brb L A mem md)).
{ intros ss ms' ae npe HS' Hpc Hrv (rg0 & rg2 & Hrg0 & Hb0 & Hrg2 & Hb2 & Hincl & Hin20) Hkl Q9 Q14 Q8 Q22 Q16 Q23 Q11 Q20 Hnpe Vnp Vae Vbit2 HJ' K.
assert (XG2f : YO07.flag (fl_gen3 G cur bef) 2 = false).
{ unfold YO07.flag. rewrite <- Vae, land_low32_small, Vbit2 by (clear; lia). reflexivity. }
destruct (fl_dims_nodiff G cur bef XG2f) as [XDIM XTMPe].
pose proof (regs_kept_of_st_ok ubs0segs _ ss ms' regs1 _ _ HS' (env_agree_refl _ _) Hkl) as R.
pose proof (st_region_chunks ubs0segs E ss ms' 0 rg0 2%nat (sp0 - 272) HS' Hrg0 Hb0 HU2) as Hcs0.
apply incl_chunks_sound in Hincl.
assert (CW : forall off e v, In (mkChunk off (CVal 8 e)) [mkChunk 96 (CVal 8 (SLit 0)); mkChunk 112 (CVal 8 (SOff 80 0)); mkChunk 120 (CVal 8 (SOff 16 0)); mkChunk 56 (CVal 8 (SLit u));
mkChunk 104 (CVal 8 (SOff 27 0)); mkChunk 32 (CVal 8 (SOff 69 0)); mkChunk 16 (CVal 8 (SOff 13 0)); mkChunk 24 (CVal 8 (SOff 15 0))] ->
sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> word_mem ubs0segs (ms_mem ms') (sp0 - 272 + off) v).
{ intros off e v Hin Hd Hv. exact (chunk_word E _ _ off e v (proj1 (Forall_forall _ _) Hcs0 _ (Hincl _ Hin)) Hd Hv). }
assert (RGx : forall (r : reg) sv, sr_get (ss_regs ss) r = sv -> getr (ms_regs ms') r = sv_denot E sv).
{ intros r sv Hr. rewrite (st_ok_reg ubs0segs E ss ms' r HS'), Hr. reflexivity. }
rewrite (st_ok_mkst ubs0segs _ _ _ HS' Hrv), Hpc.
pose proof (land_le (fr_attr f) 4 ltac:(clear; lia)) as L4.
assert (PRE : t2_pre API L A mem md regs0 (ms_regs ms') Lc Ac (ms_mem ms') mdc g N s i f (fl_gen3 G cur bef) rest FP [] 0 0 (fr_tidx f) (cg_W s) (cg_H s) 0 0).
{ split; [exact HJ'|]. split; [exact Hid|]. split; [exact Hra0|]. split; [exact Hal16|]. split; [exact Htp0|].
split.
{ rewrite <- Vae. apply (CGAT (ms_mem ms') (U E ae mod 2 ^ 32) K).
eapply (st_field_low ubs0segs E ss ms' 2 rg2 16 (fr_ptr f) 20 4 ae (2 ^ 32) HS' Hrg2 Hb2 Hin20 HU16 ltac:(cbn; lia) eq_refl). }
split; [exact Hwf|]. split; [exact Hi|]. split; [exact Hf|]. split; [exact HFP|]. split; [exact HB|].
split; [left; split; reflexivity|]. split; [intros _ k Hk; exfalso; clear - Hk; lia|].
split; [exact HW1|]. split; [clear; lia|]. split; [clear; lia|]. split; [exact HH1|]. split; [clear; lia|]. split; [clear; lia|]. split; [clear - Rtidx; lia|].
split; [apply (fl_saved_ok_kept memc); [exact HSV | intros a Ha; apply K; [clear - Ha Hceil Hsp063 HFSv Hac; lia | clear - Ha; lia | clear - Ha Hp1 Hceil HFSv HFRv Hac; lia]]|].
split; [rewrite (RGx _ _ Q9); cbn [sv_denot]; rewrite Z.add_0_r, HE70, Z_to_bv_bv_unsigned; reflexivity|].
split; [rewrite (R 2%bv ltac:(cbv; auto 50)); exact G2|].
split; [apply (CW 112 (SOff 80 0)); [repeat (first [left; reflexivity | right]) | cbn [sv_denot]; rewrite Z.add_0_r, HE80, Z_to_bv_bv_unsigned; reflexivity | clear - Hg0 Hg1 Hac HGSv; lia]|].
split; [apply (CW 120 (SOff 16 0)); [repeat (first [left; reflexivity | right]) | cbn [sv_denot]; rewrite Z.add_0_r, (HE 16%nat 16%bv eq_refl), G16, Z_to_bv_bv_unsigned; reflexivity | clear - Hp0 Hp1 Hac HFRv; lia]|].
split; [rewrite (RGx _ _ Q8); reflexivity|].
split; [apply (CW 56 (SLit u)); [repeat (first [left; reflexivity | right]) | cbn [sv_denot]; rewrite Hudef; reflexivity | rewrite <- Hudef; clear - Hu; lia]|].
split; [rewrite (R 27%bv ltac:(cbv; auto 50)); exact G27|].
split; [apply (CW 104 (SOff 27 0)); [repeat (first [left; reflexivity | right]) | cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (HE 27%nat 27%bv eq_refl); exact G27 | clear - RW; lia]|].
split; [rewrite (R 19%bv ltac:(cbv; auto 50)); exact G19|].
split; [rewrite (RGx _ _ Q16); cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (HE 19%nat 19%bv eq_refl); exact G19|].
split; [rewrite (RGx _ _ Q23); cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (HE 27%nat 27%bv eq_refl); exact G27|].
split; [apply (CW 96 (SLit 0)); [repeat (first [left; reflexivity | right]) | reflexivity | clear; lia]|].
split; [rewrite (RGx _ _ Q22); reflexivity|].
split; [rewrite (R 3%bv ltac:(cbv; auto 50)); exact G3 | rewrite (R 4%bv ltac:(cbv; auto 50)); exact G4]. }
apply (fl_trans API IMG RAWADDX L A mem md regs0 (ms_regs ms') Lc Ac (ms_mem ms') mdc g N s i f rest FP FPw [] 0 0 (fr_tidx f) (cg_W s) (cg_H s) 0 0 (U E npe)
S GPAL cur bfr bef brb brb ha PRE (U E ae)).
- rewrite (RGx _ _ Q11). apply denot_of_U'. reflexivity.
- apply U_range.
- rewrite (RGx _ _ Q20). apply denot_of_U'. reflexivity.
- exact Hnpe.
- intros Hb1.
assert (Hbit : Z.land (fl_gen3 G cur bef) 1 <> 0) by (rewrite <- Vae, land_low32_small by (clear; lia); exact Hb1).
pose proof (proj1 (fl_trans_on_bit G cur bef) Hbit) as Hon. unfold fl_trans_on in Hon.
destruct bef as [befr|]; [| discriminate Hon].
destruct bfr as [b'|]; [| exfalso; exact HVb].
apply SLOT.
+ intros b Hb Hpb. exists b, befr.
assert (Hbb : b' = b) by (pose proof (nth_error_nth _ _ None Hb) as X; rewrite Hbfr in X; injection X as X'; exact X').
subst b'. split; [reflexivity|]. split; [reflexivity|]. split; [exact Hb|]. rewrite (R 18%bv ltac:(cbv; auto 50)), G18, Hpb. reflexivity.
+ intros Hnone _. exfalso. rewrite Hnone in Hbfr. discriminate Hbfr.
- exact Hbfr.
- exact HSINK.
- apply VK. exact K.
- rewrite (RGx _ _ Q14). cbn [sv_denot]. rewrite Z.add_0_r, HE69, Z_to_bv_bv_unsigned. reflexivity.
- rewrite (R 15%bv ltac:(cbv; auto 50)). exact G15.
- apply (CW 32 (SOff 69 0)); [repeat (first [left; reflexivity | right]) | cbn [sv_denot]; rewrite Z.add_0_r, HE69, Z_to_bv_bv_unsigned; reflexivity | clear - Rdisp; lia].
- apply (CW 16 (SOff 13 0)); [repeat (first [left; reflexivity | right]) | cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (HE 13%nat 13%bv eq_refl); exact G13 | clear - L4; lia].
- apply (CW 24 (SOff 15 0)); [repeat (first [left; reflexivity | right]) | cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (HE 15%nat 15%bv eq_refl); exact G15 | rewrite Xha; destruct (fl_hasAlpha G cur); clear; lia].
- exact Xha.
- unfold fl_w. change (gcfg_of s GPAL) with G. rewrite XDIM. reflexivity.
- unfold fl_h. change (gcfg_of s GPAL) with G. rewrite XDIM. reflexivity.
- unfold fl_top. change (gcfg_of s GPAL) with G. rewrite XDIM. reflexivity.
- unfold fl_left. change (gcfg_of s GPAL) with G. rewrite XDIM. reflexivity.
- pose proof (fl_trans_on_bit G cur bef) as TB. rewrite <- Vae, land_low32_small in TB by (clear; lia). exact TB.
- exact Vnp.
- rewrite XA7. apply Z.mod_small. rewrite <- XA7. exact Rtidx.
- cbn [Z.eqb]. change (gcfg_of s GPAL) with G. rewrite XTMPe. pose proof (VK _ K) as (_ & (_ & _ & _ & _ & _ & _ & _ & XI & _) & _). exact XI.
- change (gcfg_of s GPAL) with G. rewrite XTMPe, XVIl, HN. reflexivity.
- exact HRq.
- intros _. rewrite <- HN.
split; [exact HRR0|]. split; [exact HRB0|]. intros _. exact (HNUM N ltac:(clear - HN HW1 HH1 HNle; nia)).
- intros Hz. exfalso. exact (Hz eq_refl). }
Ltac kstep2 KSTEP HU2 HU9 :=
let HF := get_HF in cbn [ms_mem mkst] in HF; clear_HG;
lazymatch goal with K : forall a, _ -> _ -> _ -> mbyte ubs0segs ?m a = mbyte ubs0segs ?m0 a |- _ =>
lazymatch type of HF with frame_of ?E1 ?rs m ?m2 =>
let K2 := fresh "K" in
assert (K2 : forall a, 0 <= a < 2 ^ 64 -> ~ (_ <= a < _) -> ~ (_ <= a < _) -> mbyte ubs0segs m2 a = mbyte ubs0segs m0 a)
by (intros a Ha Hn1 Hn2; try rewrite <- (K a Ha Hn1 Hn2); exact (KSTEP E1 _ _ m m2 HU2 HU9 HF a Ha Hn1 Hn2));
clear HF K
end
end.
destruct Hu as [Hu | Hu]; subst u.
all: jrun_to LAWS ubs0tbl_ok HS HJ FL_T; [apply WR; [exact HU2 | exact HU16] |]; kstep2 KSTEP HU2 HU16.
all: jbranch ubs0tbl HS; rename Hc into Hc256.
all: jrun_to LAWS ubs0tbl_ok HS HJ FL_T; [apply WR; [exact HU2 | exact HU16] |]; kstep2 KSTEP HU2 HU16.
all: jbranch ubs0tbl HS.
all: match goal with
| Hc : branch_taken BC_NE (sv_denot _ (SAlu ALU_AND _ (SLit 2))) _ = true |- _ =>
jrun_to LAWS ubs0tbl_ok HS HJ FL_DIFF; [apply WR; [exact HU2 | exact HU16] |]; kstep2 KSTEP HU2 HU16;
lazymatch goal with K : forall a, _ -> _ -> _ -> mbyte ubs0segs _ a = mbyte ubs0segs _ a |- _ =>
eapply (GO_D _ _ _ _ HS); [ reflexivity | reflexivity
| do 2 eexists; split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|];
split; [vm_compute; reflexivity | cbn [r_chunks]; repeat (first [left; reflexivity | right])]
| vm_compute; reflexivity | reflexivity | reflexivity | reflexivity
| apply AE; first [left; reflexivity | right; reflexivity]
| rewrite branch_ne_U, U_and_slit, U_lit in Hc by (clear; lia); change (zcanon 2) with 2 in Hc;
apply Bool.negb_true_iff in Hc; apply Z.eqb_neq in Hc; exact Hc
| reflexivity | apply NPE; first [left; reflexivity | right; reflexivity]
| lazymatch goal with |- U ?ee ?x = ?r => let x' := eval vm_compute in x in change (U ee x' = r) end;
first [exact (XNP0 eq_refl) | exact (XNP1 eq_refl)]
| lazymatch goal with |- U ?ee ?x mod 2 ^ 32 = ?r => let x' := eval vm_compute in x in change (U ee x' mod 2 ^ 32 = r) end;
lazymatch type of Hc256 with branch_taken BC_NE (sv_denot _ ?npx) _ = _ =>
first [ rewrite (proj1 (XG3 (U E npx) ltac:(first [exact (XNP0 eq_refl) | exact (XNP1 eq_refl)]))
ltac:(rewrite branch_ne_U, U_lit in Hc256 by (clear; lia); apply Bool.negb_true_iff in Hc256; apply Z.eqb_neq in Hc256; exact Hc256));
exact UE0
| rewrite (proj2 (XG3 (U E npx) ltac:(first [exact (XNP0 eq_refl) | exact (XNP1 eq_refl)]))
ltac:(rewrite branch_ne_U, U_lit in Hc256 by (clear; lia); apply Bool.negb_false_iff in Hc256; apply Z.eqb_eq in Hc256; exact Hc256));
exact UE2 ] end
| exact HJ | exact K ] end
| Hc : branch_taken BC_NE (sv_denot _ (SAlu ALU_AND _ (SLit 2))) _ = false |- _ =>
jrun_to LAWS ubs0tbl_ok HS HJ FL_T; [apply WR; [exact HU2 | exact HU16] |]; kstep2 KSTEP HU2 HU16;
lazymatch goal with K : forall a, _ -> _ -> _ -> mbyte ubs0segs _ a = mbyte ubs0segs _ a |- _ =>
eapply (GO_T _ _ _ _ HS); [ reflexivity | reflexivity
| do 2 eexists; split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|];
split; [vm_compute; reflexivity | cbn [r_chunks]; repeat (first [left; reflexivity | right])]
| vm_compute; reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
| reflexivity | apply NPE; first [left; reflexivity | right; reflexivity]
| lazymatch goal with |- U ?ee ?x = ?r => let x' := eval vm_compute in x in change (U ee x' = r) end;
first [exact (XNP0 eq_refl) | exact (XNP1 eq_refl)]
| lazymatch goal with |- U ?ee ?x mod 2 ^ 32 = ?r => let x' := eval vm_compute in x in change (U ee x' mod 2 ^ 32 = r) end;
lazymatch type of Hc256 with branch_taken BC_NE (sv_denot _ ?npx) _ = _ =>
first [ rewrite (proj1 (XG3 (U E npx) ltac:(first [exact (XNP0 eq_refl) | exact (XNP1 eq_refl)]))
ltac:(rewrite branch_ne_U, U_lit in Hc256 by (clear; lia); apply Bool.negb_true_iff in Hc256; apply Z.eqb_neq in Hc256; exact Hc256));
exact UE0
| rewrite (proj2 (XG3 (U E npx) ltac:(first [exact (XNP0 eq_refl) | exact (XNP1 eq_refl)]))
ltac:(rewrite branch_ne_U, U_lit in Hc256 by (clear; lia); apply Bool.negb_false_iff in Hc256; apply Z.eqb_eq in Hc256; exact Hc256));
exact UE2 ] end
| rewrite branch_ne_U, U_and_slit, U_lit in Hc by (clear; lia); change (zcanon 2) with 2 in Hc;
apply Bool.negb_false_iff in Hc; apply Z.eqb_eq in Hc; exact Hc
| exact HJ | exact K ] end
end.
Qed.
End S.
End l.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
