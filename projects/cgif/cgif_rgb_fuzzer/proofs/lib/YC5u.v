(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YC02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YI02 YI04 YI1i YI08.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YC04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB0z YC19 YF8z YC1d YC1a YC2o YC10 YC1b YC2u
YC4u YC4z YC52 YC53 YC51.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK0p YI0c YM01 YG0e YC05.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCaq YC6j YCbj YCas YCat YCau YCbh YCbk
YC7e YC7j YCbl YC6e YCav YC7f YCaw YCax YCay YCaz YC7g YCbm YCb0 YCb1 YCb2 YCb3 YCb4 YCb5 YCb6 YCbn YCb7 YCba YCbb YCbc YCbd YCbf YCbe YCbg.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG0f YC07 YP14 YP15 YI0g YC4t YC7i YC6w YC6v YC7d YC6k YC6t YC7c YC6u YC77 YC78 YC79 YC7a YC7b YC6z YC76.
Section d. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Lemma hlg_byte_of_av : forall H (m : word -> option byte) a v, aview trasegs H m a = Some v -> mbyte trasegs (mrestrict H m) a = Some (Z_to_bv 8 v).
Proof.
intros H m a v Hv. unfold aview in Hv. destruct (mbyte trasegs (mrestrict H m) a) as [b|]; [|discriminate].
cbn [option_map] in Hv. injection Hv as <-. rewrite Z_to_bv_bv_unsigned. reflexivity.
Qed.
Lemma hlg_denot_off0 : forall E n p, ew E n = Z_to_bv 64 p -> 0 <= p < 2 ^ 64 -> sv_denot E (SOff n 0) = Z_to_bv 64 p.
Proof. intros E n p Hn Hp. rewrite (denot_off E n p 0 Hn Hp), Z.add_0_r. reflexivity. Qed.
Lemma hlg_denot_shx : forall E n m p c, ew E n = Z_to_bv 64 p -> ew E m = Z_to_bv 64 SB -> 0 <= p -> p + c < 2 ^ 47 -> 0 <= c ->
sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff n c) (SLit 3)) (SOff m 0)) = Z_to_bv 64 (SB + (p + c) / 8).
Proof.
intros E n m p c Hn Hb Hp Hk Hk0. rewrite denot_lit_U. f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit.
rewrite (U_atom_off E n p c Hn) by lia. rewrite (U_atom E m SB Hb) by (unfold SB; lia).
rewrite (zcanon_id 3) by (unfold M64; lia). change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
rewrite (zcanon_id ((p + c) / 8)) by (unfold M64; split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
assert (0 <= (p + c) / 8) by (apply Z.div_pos; lia). assert ((p + c) / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia).
rewrite (Z.add_comm SB). apply zcanon_id. unfold M64, SB. lia.
Qed.
Lemma hlg_denot_sext32 : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 31 -> sv_denot E (SExt true 32 (SOff n 0)) = Z_to_bv 64 v.
Proof. intros E n v Hn Hv. rewrite denot_lit_U. f_equal. apply U_sext32_small; assumption. Qed.
Lemma hlg_denot_and255 : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 256 ->
sv_denot E (SAlu ALU_AND (SExt true 32 (SOff n 0)) (SLit 255)) = Z_to_bv 64 v.
Proof.
intros E n v Hn Hv. rewrite denot_lit_U. f_equal. rewrite U_and_lit by lia. rewrite (U_sext32_small E n v Hn) by lia.
change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_small. lia.
Qed.
Lemma hlg_denot_N : forall E nh nw Hd Wd, ew E nh = Z_to_bv 64 Hd -> ew E nw = Z_to_bv 64 Wd -> 0 <= Hd < 2 ^ 16 -> 0 <= Wd < 2 ^ 16 -> 0 <= Hd * Wd < 2 ^ 31 ->
sv_denot E (SAlu ALU_SRL (SAlu ALU_SLL (SMdw M_MUL (SOff nh 0) (SOff nw 0)) (SLit 32)) (SLit 32)) = Z_to_bv 64 (Hd * Wd).
Proof.
intros E nh nw Hd Wd Hh Hw H1 H2 H3. rewrite denot_lit_U. f_equal.
apply U_zext32_shifts; [apply U_HW; assumption | lia].
Qed.
Lemma hlg_slot_of_state : forall E ss ms (H : word -> bool) idx lo hi wlo whi cs sp0 off e v,
st_ok trasegs E ss (restrict H ms) -> nth_error (ss_mem ss) idx = Some (YQ0b.mkRegion (Some 2%nat) lo hi wlo whi cs) ->
In (YQ0b.mkChunk (off - 512) (CVal 8 e)) cs -> bv_unsigned (ew E 2) = sp0 -> sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
val_mem trasegs (mrestrict H (ms_mem ms)) (sp0 - 512 + off) 8 v.
Proof.
intros E ss ms H idx lo hi wlo whi cs sp0 off e v HS Hnth Hin U2 He Hv.
destruct (st_ok_mem_ok trasegs E ss _ HS) as (_ & Hrs & _).
pose proof (proj1 (Forall_forall _ _) Hrs _ (nth_error_In _ _ Hnth)) as HR. cbn [ms_mem restrict] in HR.
replace (sp0 - 512 + off) with (sp0 + (off - 512)) by lia.
exact (field_of_region E _ 2 sp0 cs lo hi wlo whi (off - 512) 8%N e v HR U2 Hin He Hv ltac:(lia)).
Qed.
Lemma hlg_div8_44 : forall b, b mod 16 = 0 -> (b + 44) / 8 = (b + 40) / 8.
Proof.
intros b Hb. pose proof (Z.div_mod b 16 ltac:(lia)) as Hq. rewrite Hb, Z.add_0_r in Hq.
rewrite Hq at 1 2. replace (16 * (b / 16) + 44) with (4 + (2 * (b / 16) + 5) * 8) by lia.
replace (16 * (b / 16) + 40) with (0 + (2 * (b / 16) + 5) * 8) by lia.
rewrite !Z.div_add by lia. reflexivity.
Qed.
Lemma hlg_kept_ck : forall E H H' (m m2 : word -> option byte) r b,
base_val E (r_base r) = b ->
(forall c, In c (r_chunks r) -> forall i, 0 <= i < c_len c -> aview trasegs H' m2 (b + c_off c + i) = aview trasegs H m (b + c_off c + i)) ->
(forall a, b + r_wlo r <= a < b + r_whi r -> apresent H' m2 a) ->
region_kept_ck trasegs E (mrestrict H m) (mrestrict H' m2) r.
Proof.
intros E H H' m m2 r b Hb Hav Hp. split; rewrite Hb.
- intros c Hc i Hi. apply (mbyte_of_aview trasegs). apply Hav; assumption.
- intros a Ha _. apply (apresent_writable trasegs). apply Hp. exact Ha.
Qed.
Lemma hlg_kept_rng : forall E H H' (m m2 : word -> option byte) r b,
base_val E (r_base r) = b -> forallb (chunk_inside r) (r_chunks r) = true ->
(forall a, b + r_lo r <= a < b + r_hi r -> aview trasegs H' m2 a = aview trasegs H m a) ->
(forall a, b + r_wlo r <= a < b + r_whi r -> apresent H' m2 a) ->
region_kept_ck trasegs E (mrestrict H m) (mrestrict H' m2) r.
Proof.
intros E H H' m m2 r b Hb Hin Hav Hp. apply (hlg_kept_ck E H H' m m2 r b Hb); [|exact Hp].
intros c Hc i Hi. pose proof (proj1 (forallb_forall _ _) Hin c Hc) as Hci. unfold chunk_inside in Hci.
apply andb_prop in Hci as [Hci _]. apply andb_prop in Hci as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
apply Hav. lia.
Qed.
Definition hlg_ck_off_w (c : YQ0b.chunk) : bool :=
let o := c_off c + 512 in let e := o + c_len c in
((e <=? 56) || (64 <=? o)) && ((e <=? 72) || (80 <=? o)) && ((e <=? 160) || (184 <=? o)) && ((e <=? 296) || (304 <=? o)) && (0 <=? o) && (e <=? 512).
Lemma hlg_kept_stack : forall E H H' (m m2 : word -> option byte) r sp0,
base_val E (r_base r) = sp0 -> forallb hlg_ck_off_w (r_chunks r) = true ->
(forall a, sp0 - 512 <= a < sp0 - 512 + 512 -> ~ wslot (a - (sp0 - 512)) -> aview trasegs H' m2 a = aview trasegs H m a) ->
(forall a, sp0 + r_wlo r <= a < sp0 + r_whi r -> apresent H' m2 a) ->
region_kept_ck trasegs E (mrestrict H m) (mrestrict H' m2) r.
Proof.
intros E H H' m m2 r sp0 Hb Hin Hav Hp. apply (hlg_kept_ck E H H' m m2 r sp0 Hb); [|exact Hp].
intros c Hc i Hi. pose proof (proj1 (forallb_forall _ _) Hin c Hc) as Hci. unfold hlg_ck_off_w in Hci. cbv zeta in Hci.
repeat (apply andb_prop in Hci as [Hci ?]).
repeat match goal with X : (_ || _) = true |- _ => apply orb_prop in X | X : (_ <=? _) = true |- _ => apply Z.leb_le in X end.
apply Hav; [lia|]. unfold wslot. lia.
Qed.
End d.
Section f. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section h.
Variable B : asyms.
Hypothesis TL : TraLib B.
Hypothesis LAWS : AR_laws trasegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis FFL : frame_flag_lawP trasegs B.
Hypothesis AMALLOC : amalloc_realizes trasegs B.
Hypothesis AFREE : afree_realizes trasegs B.
Hypothesis AREALLOC : arealloc_realizes trasegs B 0x53108 0x53640.
Hypothesis AMEMCPY : aintrin_realizes trasegs B OCpy A_asan_memcpy.
Hypothesis AMEMSET : aintrin_realizes trasegs B OSet A_asan_memset.
Hypothesis ABCMP : abcmp_realizes trasegs B A_bcmp_tra.
Hypothesis TCOLHASH : tcolhash_spec B.
Let HBcode := tl_code B TL. Let errno_low := tl_env B TL.
Lemma rga_HL : rga_fromA B ss_HD (fun _ => INV_HD B) -> rga_fromA B ss_X38b (fun _ => INV_X38b B) -> rga_from B ss_HL0 (INV_A11z B).
Proof.
intros RC RCX. rga_prelude.
destruct HINV as [HINV Hz0]. red in HINV. rga_cbn_cx HINV. rga_cbn_cx Hz0.
destruct HINV as (bs & Hk0 & Hfmt & Eab3 & Hnews & av & E300 & Hav).
destruct Hk0 as [Hk0 Hbud].
unfold news_A9, news_A2, news_A1 in Eab3, Hnews. rga_cbn_cx Eab3. rga_cbn_cx Hnews. cbn [app] in Eab3, Hnews.
cbn [rga_news] in Hnews. destruct bs as [|blk bs]; [contradiction|]. cbn [rga_news] in Hnews. destruct Hnews as ((Rblk & Tblk & Ablk) & Hnews).
cbn [rga_news] in Hnews. destruct bs as [|fim bs]; [contradiction|]. cbn [rga_news] in Hnews. destruct Hnews as ((Rfim & Tfim & Afim) & Hnews).
cbn [rga_news] in Hnews. destruct bs as [|tb bs]; [contradiction|]. cbn [rga_news] in Hnews. destruct Hnews as ((Rtb & Ttb & Atb) & Hnews).
cbn [rga_news] in Hnews. destruct bs as [|fq bs]; [contradiction|]. cbn [rga_news] in Hnews. destruct Hnews as ((Rfq & Tfq & Afq) & Hnews).
cbn [rga_news] in Hnews. destruct bs as [|hh bs]; [contradiction|]. cbn [rga_news] in Hnews. destruct Hnews as ((Rhh & Thh & Ahh) & Hnews).
cbn [rga_news] in Hnews. destruct bs as [|uu bs]; [contradiction|]. cbn [rga_news] in Hnews. destruct Hnews as ((Ruu & Tuu & Auu) & Hnews).
cbn [rga_news] in Hnews. destruct bs as [|pp bs]; [contradiction|]. cbn [rga_news] in Hnews. destruct Hnews as ((Rpp & Tpp & App) & Hnews).
cbn [rga_news] in Hnews. destruct bs as [|xx bs]; [contradiction|]. cbn [rga_news] in Hnews. destruct Hnews as ((Rxx & Txx & Axx) & Hnews).
cbn [rga_news] in Hnews. destruct bs as [|? ?]; [|contradiction]. clear Hnews. cbn [combine map snd] in Eab3.
assert (Hrin3 : In (r, 64) (ablocks B ly3 S3)) by (rewrite Eab3; apply in_or_app; left; exact Hrin).
pose proof (EFA3 7 fpos) as EFA37. fold F in EFA37.
assert (Hfb7 : fs_frame_bytes 7 = 8192) by reflexivity.
assert (E10n : ew E 10 = Z_to_bv 64 r) by (rewrite (AG 10%nat) by lia; exact E10).
assert (E11n : ew E 11 = Z_to_bv 64 cfp) by (rewrite (AG 11%nat) by lia; exact E11).
destruct Hwf as (Hwf1 & HW1 & HH1 & HNWH & HNmax & Hwf6).
assert (HN1 : 1 <= N) by (rewrite HNWH; clear - HW1 HH1; nia).
assert (Hra88 : 0x81368 = raZ regs) by (cbn [CTX_cgif_rgb_addframe In] in Hctx; destruct Hctx as [H | [H | []]]; injection H as Hr Hs; exact Hr).
assert (Hspine : spine ch = [] \/ spine ch = [0x80ea8])
by (cbn [CTX_cgif_rgb_addframe In] in Hctx; destruct Hctx as [H | [H | []]]; injection H as Hr Hs; rewrite <- Hs; [left | right]; reflexivity).
assert (HfN : 3 <= fmt * N <= 4 * RGB_NMAX) by (clear - Hfmt HN1 HN; unfold RGB_NMAX in *; nia).
assert (HNhw : N = Hd * Wd) by (rewrite HNWH, HcW, HcH; lia).
let v := eval vm_compute in EV_RGBADD in assert (HEVv : EV_RGBADD = v) by reflexivity.
pose proof Hrgb as Hrgb'. cbn [obj_at LAY_Rgb] in Hrgb'.
destruct Hrgb' as ([_ R0v] & [_ R8v] & [_ R16v] & [_ R24v] & [_ R32v] & [_ R36v] & [_ R40v] & [_ R42v] & [_ R44v] & [_ R48v] & [_ R56v] & [_ R60v] & _).
cbn [fst snd N.to_nat Z.of_N] in R0v, R8v, R16v, R24v, R32v, R36v, R40v, R42v, R44v, R48v, R56v, R60v.
assert (Htb_in3 : In (tb, 48) (ablocks B ly3 S3)) by (rewrite Eab3; apply in_or_app; right; right; right; left; reflexivity).
assert (Hrqtb : 48 <= req_size 48 <= 48) by (change (req_size 48) with 48; clear; lia).
destruct (rga_blk_range B LAWS ly3 S3 _ _ _ tb 48 HAR3 Htb_in3) as (Htb4096 & Htbzone & Htbceil & Htb16). gboxh Htbzone.
assert (Htb_rng : 0 <= tb < 2 ^ 64) by (clear - Htb4096 Htbceil Hrqtb C1; lia).
assert (U2 : bv_unsigned (ew E 2) = spZ regs) by (rewrite (AG 2%nat) by lia; exact Usp).
assert (Hsp47 : alloc_ceiling + 25088 <= spZ regs /\ spZ regs <= 2 ^ 47) by (clear - Hceil Hslo Hshi H47 FFS; lia).
assert (E8n : ew E 8 = Z_to_bv 64 (s0Z regs)) by (rewrite (AG 8%nat) by lia; rewrite (EE 8%nat 8%bv eq_refl); unfold s0Z; rewrite Z_to_bv_bv_unsigned; reflexivity).
assert (E1n : ew E 1 = Z_to_bv 64 (raZ regs)) by (rewrite (AG 1%nat) by lia; rewrite (EE 1%nat 1%bv eq_refl); unfold raZ; rewrite Z_to_bv_bv_unsigned; reflexivity).
assert (E3n : ew E 3 = Z_to_bv 64 (as_gp B)) by (rewrite (AG 3%nat) by lia; rewrite (EE 3%nat 3%bv eq_refl); exact Hgp).
assert (E4n : ew E 4 = Z_to_bv 64 (as_tp B)) by (rewrite (AG 4%nat) by lia; rewrite (EE 4%nat 4%bv eq_refl); exact Htp).
assert (E2n : ew E 2 = Z_to_bv 64 (spZ regs)) by (rewrite (AG 2%nat) by lia; rewrite (EE 2%nat 2%bv eq_refl); unfold spZ; rewrite Z_to_bv_bv_unsigned; reflexivity).
assert (Hs0rng : 0 <= s0Z regs < 2 ^ 64) by (unfold s0Z; apply bv_unsigned_in_range).
assert (Hrarng : 0 <= raZ regs < 2 ^ 64) by (unfold raZ; apply bv_unsigned_in_range).
assert (Hsprng : 0 <= spZ regs < 2 ^ 64) by (clear - Hsp47 C1; lia).
assert (Hrrng : 0 <= r < 2 ^ 64) by (clear - Hr4096 Hrceil C1; lia).
assert (Hcfprng : 4096 <= cfp /\ cfp + 24 <= alloc_ceiling) by (clear - Hflo Hfhi Hf4096 Hfceil; lia).
assert (HSBF : 0 <= SB + F / 8 /\ SB + F / 8 + 1024 < 2 ^ 47) by (clear - HF8lo HF8hi; unfold SB; lia).
assert (Hfmt31 : 0 <= fmt < 256) by (clear - Hfmt; lia).
assert (HWd16 : 0 <= Wd < 2 ^ 16) by (clear - R42v; cbn in R42v; lia).
assert (HHd16 : 0 <= Hd < 2 ^ 16) by (clear - R44v; cbn in R44v; lia).
assert (HN31 : 0 <= Hd * Wd < 2 ^ 31) by (rewrite <- HNhw; clear - HN1 HN; unfold RGB_NMAX in *; lia).
assert (Himg_in : In (img, fmt * N) (ablocks B ly S)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm|]. apply in_or_app. right. apply in_or_app. left.
unfold timg_block. destruct Hfmt as [-> | ->]; left; reflexivity. }
assert (Himg_in3 : In (img, fmt * N) (ablocks B ly3 S3)) by (rewrite Eab3; apply in_or_app; left; exact Himg_in).
destruct (al_blocks _ _ LAWS _ _ _ _ _ img (fmt * N) HAR3 Himg_in3) as (_ & Himg4096 & Himgceil & _ & Himgpres & _ & _).
pose proof (req_size_pos (fmt * N) ltac:(clear - HfN; lia)) as Hrqimg.
destruct (arr8_of_present trasegs (mrestrict (w_H W3) (ms_mem ms3)) img (Z.to_nat (fmt * N))) as (imgl & Aimg & Limg).
{ intros i Hi. apply mbyte_of_apresent. apply (proj1 (Himgpres (img + i) ltac:(clear - Hi Hrqimg HfN; lia))). }
assert (Himgl : zlen imgl = fmt * N) by (unfold zlen; rewrite Limg; clear - HfN; lia).
assert (HSHR : forall p c, 0 <= p -> p + c < 2 ^ 47 -> 0 <= c -> 0 <= SB + (p + c) / 8 < 2 ^ 64).
{ intros p0 c0 Hp0 Hpc Hc0. assert (0 <= (p0 + c0) / 8) by (apply Z.div_pos; lia). assert ((p0 + c0) / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia). unfold SB. lia. }
assert (Hslots : hk_slots (spZ regs - 512) tb img fmt N (r + 60) F (SB + F / 8 + 532) r F (F + 5152) (SB + (r + 42) / 8) cfp (s0Z regs) (raZ regs)
(mrestrict (w_H W3) (ms_mem ms3))).
{ pose proof (fun off e v => hlg_slot_of_state E ss_HL0 ms3 (w_H W3) 8%nat _ _ _ _ _ (spZ regs) off e v HS eq_refl) as SL0.
lazymatch type of SL0 with forall off e v, In _ ?cs -> _ =>
assert (SL : forall off e v j, nth_error cs j = Some (YQ0b.mkChunk (off - 512) (CVal 8 e)) -> sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
val_mem trasegs (mrestrict (w_H W3) (ms_mem ms3)) (spZ regs - 512 + off) 8 v)
by (intros off e v j Hj He Hv; exact (SL0 off e v (nth_error_In _ _ Hj) U2 He Hv)) end.
clear SL0. intros off v Hin. cbv [hk_tab In] in Hin.
destruct Hin as [Hin|Hin]; [injection Hin as <- <-; exact (SL 16 (SLit 7) 7 1%nat eq_refl eq_refl ltac:(clear; lia))|].
destruct Hin as [Hin|Hin]; [injection Hin as <- <-; exact (SL 24 (SLit 65537) 65537 0%nat eq_refl eq_refl ltac:(clear; lia))|].
destruct Hin as [Hin|Hin]; [injection Hin as <- <-; exact (SL 32 (SOff 10 60) (r + 60) 5%nat eq_refl (denot_off E 10 r 60 E10n Hrrng) ltac:(clear - Hr4096 Hrceil C1; lia))|].
destruct Hin as [Hin|Hin]; [injection Hin as <- <-; exact (SL 40 (SOff 54 0) F 8%nat eq_refl (hlg_denot_off0 E 54 F RF HFrng) HFrng)|].
destruct Hin as [Hin|Hin]; [injection Hin as <- <-; exact (SL 80 (SAlu ALU_SRL (SAlu ALU_SLL (SMdw M_MUL (SOff 40 0) (SOff 39 0)) (SLit 32)) (SLit 32)) N 2%nat eq_refl ltac:(rewrite HNhw; exact (hlg_denot_N E 40 39 Hd Wd E40 E39 HHd16 HWd16 HN31)) ltac:(clear - HN1 HN; unfold RGB_NMAX in *; lia))|].
destruct Hin as [Hin|Hin]; [injection Hin as <- <-; exact (SL 88 (SAlu ALU_AND (SExt true 32 (SOff 46 0)) (SLit 255)) fmt 4%nat eq_refl (hlg_denot_and255 E 46 fmt E46 Hfmt31) ltac:(clear - Hfmt31; lia))|].
destruct Hin as [Hin|Hin]; [injection Hin as <- <-; exact (SL 96 (SOff 67 532) (SB + F / 8 + 532) 7%nat eq_refl (denot_off E 67 (SB + F / 8) 532 E67 ltac:(clear - HSBF; lia)) ltac:(clear - HSBF; lia))|].
destruct Hin as [Hin|Hin]; [injection Hin as <- <-; exact (SL 104 (SExt true 32 (SOff 46 0)) fmt 25%nat eq_refl (hlg_denot_sext32 E 46 fmt E46 ltac:(clear - Hfmt31; lia)) ltac:(clear - Hfmt31; lia))|].
destruct Hin as [Hin|Hin]; [injection Hin as <- <-; exact (SL 112 (SLit 4294967295) 4294967295 3%nat eq_refl eq_refl ltac:(clear; lia))|].
destruct Hin as [Hin|Hin]; [injection Hin as <- <-; exact (SL 120 (SOff 45 0) img 26%nat eq_refl (hlg_denot_off0 E 45 img E45 ltac:(clear - Himg4096 Himgceil Hrqimg C1; lia)) ltac:(clear - Himg4096 Himgceil Hrqimg C1; lia))|].
destruct Hin as [Hin|Hin]; [injection Hin as <- <-; exact (SL 128 (SOff 10 0) r 6%nat eq_refl (hlg_denot_off0 E 10 r E10n Hrrng) Hrrng)|].
destruct Hin as [Hin|Hin]; [injection Hin as <- <-; exact (SL 152 (SOff 305 24) (tb + 24) 11%nat eq_refl (denot_off E 305 tb 24 Rtb Htb_rng) ltac:(clear - Htb4096 Htbceil Hrqtb C1; lia))|].
destruct Hin as [Hin|Hin]; [injection Hin as <- <-; exact (SL 192 (SOff 54 0) F 31%nat eq_refl (hlg_denot_off0 E 54 F RF HFrng) HFrng)|].
destruct Hin as [Hin|Hin]; [injection Hin as <- <-; exact (SL 200 (SOff 54 5152) (F + 5152) 24%nat eq_refl (denot_off E 54 F 5152 RF HFrng) ltac:(clear - HF4096 HFceil C1; lia))|].
destruct Hin as [Hin|Hin]; [injection Hin as <- <-; exact (SL 208 (SOff 305 0) tb 9%nat eq_refl (hlg_denot_off0 E 305 tb Rtb Htb_rng) Htb_rng)|].
destruct Hin as [Hin|Hin]; [injection Hin as <- <-; exact (SL 216 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 305 24) (SLit 3)) (SOff 44 0)) (SB + (tb + 24) / 8) 15%nat eq_refl (hlg_denot_shx E 305 44 tb 24 Rtb E44 ltac:(clear - Htb4096; lia) ltac:(clear - Htbceil Hrqtb C1; lia) ltac:(clear; lia)) (HSHR tb 24 ltac:(clear - Htb4096; lia) ltac:(clear - Htbceil Hrqtb C1; lia) ltac:(clear; lia)))|].
destruct Hin as [Hin|Hin]; [injection Hin as <- <-; exact (SL 224 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 305 40) (SLit 3)) (SOff 44 0)) (SB + (tb + 40) / 8) 12%nat eq_refl (hlg_denot_shx E 305 44 tb 40 Rtb E44 ltac:(clear - Htb4096; lia) ltac:(clear - Htbceil Hrqtb C1; lia) ltac:(clear; lia)) (HSHR tb 40 ltac:(clear - Htb4096; lia) ltac:(clear - Htbceil Hrqtb C1; lia) ltac:(clear; lia)))|].
destruct Hin as [Hin|Hin]; [injection Hin as <- <-; exact (SL 232 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 305 32) (SLit 3)) (SOff 44 0)) (SB + (tb + 32) / 8) 13%nat eq_refl (hlg_denot_shx E 305 44 tb 32 Rtb E44 ltac:(clear - Htb4096; lia) ltac:(clear - Htbceil Hrqtb C1; lia) ltac:(clear; lia)) (HSHR tb 32 ltac:(clear - Htb4096; lia) ltac:(clear - Htbceil Hrqtb C1; lia) ltac:(clear; lia)))|].
destruct Hin as [Hin|Hin]; [injection Hin as <- <-; exact (SL 240 (SOff 305 32) (tb + 32) 14%nat eq_refl (denot_off E 305 tb 32 Rtb Htb_rng) ltac:(clear - Htb4096 Htbceil Hrqtb C1; lia))|].
destruct Hin as [Hin|Hin]; [injection Hin as <- <-; exact (SL 248 (SOff 305 40) (tb + 40) 10%nat eq_refl (denot_off E 305 tb 40 Rtb Htb_rng) ltac:(clear - Htb4096 Htbceil Hrqtb C1; lia))|].
destruct Hin as [Hin|Hin]; [injection Hin as <- <-; exact (SL 272 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 305 0) (SLit 3)) (SOff 44 0)) (SB + (tb + 0) / 8) 21%nat eq_refl (hlg_denot_shx E 305 44 tb 0 Rtb E44 ltac:(clear - Htb4096; lia) ltac:(clear - Htbceil Hrqtb C1; lia) ltac:(clear; lia)) (HSHR tb 0 ltac:(clear - Htb4096; lia) ltac:(clear - Htbceil Hrqtb C1; lia) ltac:(clear; lia)))|].
destruct Hin as [Hin|Hin]; [injection Hin as <- <-; exact (SL 280 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 42) (SLit 3)) (SOff 44 0)) (SB + (r + 42) / 8) 35%nat eq_refl (hlg_denot_shx E 10 44 r 42 E10n E44 ltac:(clear - Hr4096; lia) ltac:(clear - Hrceil C1; lia) ltac:(clear; lia)) (HSHR r 42 ltac:(clear - Hr4096; lia) ltac:(clear - Hrceil C1; lia) ltac:(clear; lia)))|].
destruct Hin as [Hin|Hin]; [injection Hin as <- <-; exact (SL 304 (SOff 305 16) (tb + 16) 16%nat eq_refl (denot_off E 305 tb 16 Rtb Htb_rng) ltac:(clear - Htb4096 Htbceil Hrqtb C1; lia))|].
destruct Hin as [Hin|Hin]; [injection Hin as <- <-; exact (SL 312 (SOff 305 44) (tb + 44) 23%nat eq_refl (denot_off E 305 tb 44 Rtb Htb_rng) ltac:(clear - Htb4096 Htbceil Hrqtb C1; lia))|].
destruct Hin as [Hin|Hin]; [injection Hin as <- <-; exact (SL 320 (SOff 305 8) (tb + 8) 19%nat eq_refl (denot_off E 305 tb 8 Rtb Htb_rng) ltac:(clear - Htb4096 Htbceil Hrqtb C1; lia))|].
destruct Hin as [Hin|Hin]; [injection Hin as <- <-; exact (SL 336 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 305 8) (SLit 3)) (SOff 44 0)) (SB + (tb + 8) / 8) 20%nat eq_refl (hlg_denot_shx E 305 44 tb 8 Rtb E44 ltac:(clear - Htb4096; lia) ltac:(clear - Htbceil Hrqtb C1; lia) ltac:(clear; lia)) (HSHR tb 8 ltac:(clear - Htb4096; lia) ltac:(clear - Htbceil Hrqtb C1; lia) ltac:(clear; lia)))|].
destruct Hin as [Hin|Hin]; [injection Hin as <- <-; exact (SL 352 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 305 16) (SLit 3)) (SOff 44 0)) (SB + (tb + 16) / 8) 18%nat eq_refl (hlg_denot_shx E 305 44 tb 16 Rtb E44 ltac:(clear - Htb4096; lia) ltac:(clear - Htbceil Hrqtb C1; lia) ltac:(clear; lia)) (HSHR tb 16 ltac:(clear - Htb4096; lia) ltac:(clear - Htbceil Hrqtb C1; lia) ltac:(clear; lia)))|].
destruct Hin as [Hin|Hin]; [injection Hin as <- <-; exact (SL 368 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 305 44) (SLit 3)) (SOff 44 0)) (SB + (tb + 40) / 8) 22%nat eq_refl ltac:(rewrite <- (hlg_div8_44 tb Htb16); exact (hlg_denot_shx E 305 44 tb 44 Rtb E44 ltac:(clear - Htb4096; lia) ltac:(clear - Htbceil Hrqtb C1; lia) ltac:(clear; lia))) (HSHR tb 40 ltac:(clear - Htb4096; lia) ltac:(clear - Htbceil Hrqtb C1; lia) ltac:(clear; lia)))|].
destruct Hin as [Hin|Hin]; [injection Hin as <- <-; exact (SL 376 (SOff 11 0) cfp 40%nat eq_refl (hlg_denot_off0 E 11 cfp E11n ltac:(clear - Hcfprng C1; lia)) ltac:(clear - Hcfprng C1; lia))|].
destruct Hin as [Hin|Hin]; [injection Hin as <- <-; exact (SL 496 (SOff 8 0) (s0Z regs) 52%nat eq_refl (hlg_denot_off0 E 8 (s0Z regs) E8n Hs0rng) Hs0rng)|].
destruct Hin as [Hin|Hin]; [injection Hin as <- <-; exact (SL 504 (SOff 1 0) (raZ regs) 53%nat eq_refl (hlg_denot_off0 E 1 (raZ regs) E1n Hrarng) Hrarng)|].
destruct Hin. }
assert (RD : forall (rr : bv 5) e z, sr_get (ss_regs ss_HL0) rr = e -> sv_denot E e = Z_to_bv 64 z -> getr (ms_regs ms3) rr = Z_to_bv 64 z)
by (intros rr e z Q Dv; rewrite (st_ok_restrict_reg trasegs (w_H W3) E ss_HL0 ms3 rr HS), Q; exact Dv).
assert (G2 : getr (ms_regs ms3) 2 = Z_to_bv 64 (spZ regs - 512)) by exact (RD 2%bv (SOff 2 (-512)) _ eq_refl (denot_off E 2 (spZ regs) (-512) E2n Hsprng)).
assert (G9 : getr (ms_regs ms3) 9 = Z_to_bv 64 (spZ regs - 512)) by exact (RD 9%bv (SOff 2 (-512)) _ eq_refl (denot_off E 2 (spZ regs) (-512) E2n Hsprng)).
assert (G8 : getr (ms_regs ms3) 8 = Z_to_bv 64 (spZ regs - 512 + 512))
by (replace (spZ regs - 512 + 512) with (spZ regs) by lia; exact (RD 8%bv (SOff 2 0) _ eq_refl (hlg_denot_off0 E 2 (spZ regs) E2n Hsprng))).
assert (G3 : getr (ms_regs ms3) 3 = Z_to_bv 64 (as_gp B)).
{ rewrite (st_ok_restrict_reg trasegs (w_H W3) E ss_HL0 ms3 3%bv HS). change (sr_get (ss_regs ss_HL0) 3%bv) with (SOff 3 0).
cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact E3n. }
assert (G4 : getr (ms_regs ms3) 4 = Z_to_bv 64 (as_tp B)).
{ rewrite (st_ok_restrict_reg trasegs (w_H W3) E ss_HL0 ms3 4%bv HS). change (sr_get (ss_regs ss_HL0) 4%bv) with (SOff 4 0).
cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact E4n. }
assert (G25 : getr (ms_regs ms3) 25 = Z_to_bv 64 SB) by exact (RD 25%bv (SOff 44 0) _ eq_refl (hlg_denot_off0 E 44 SB E44 ltac:(unfold SB; clear; lia))).
assert (G18 : getr (ms_regs ms3) 18 = Z_to_bv 64 F) by exact (RD 18%bv (SOff 54 0) _ eq_refl (hlg_denot_off0 E 54 F RF HFrng)).
assert (G19 : getr (ms_regs ms3) 19 = Z_to_bv 64 (SB + F / 8)) by exact (RD 19%bv (SOff 67 0) _ eq_refl (hlg_denot_off0 E 67 (SB + F / 8) E67 ltac:(clear - HSBF; lia))).
assert (G5 : getr (ms_regs ms3) 5 = Z_to_bv 64 (tb + 8)) by exact (RD 5%bv (SOff 305 8) _ eq_refl (denot_off E 305 tb 8 Rtb Htb_rng)).
assert (G6 : getr (ms_regs ms3) 6 = Z_to_bv 64 (tb + 16)) by exact (RD 6%bv (SOff 305 16) _ eq_refl (denot_off E 305 tb 16 Rtb Htb_rng)).
assert (G7 : getr (ms_regs ms3) 7 = Z_to_bv 64 fmt) by exact (RD 7%bv (SExt true 32 (SOff 46 0)) _ eq_refl (hlg_denot_sext32 E 46 fmt E46 ltac:(clear - Hfmt31; lia))).
assert (G16 : getr (ms_regs ms3) 16 = Z_to_bv 64 cfp) by exact (RD 16%bv (SOff 11 0) _ eq_refl (hlg_denot_off0 E 11 cfp E11n ltac:(clear - Hcfprng C1; lia))).
assert (G17 : getr (ms_regs ms3) 17 = Z_to_bv 64 (SB + (r + 42) / 8))
by exact (RD 17%bv (SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 42) (SLit 3)) (SOff 44 0)) _ eq_refl
(hlg_denot_shx E 10 44 r 42 E10n E44 ltac:(clear - Hr4096; lia) ltac:(clear - Hrceil C1; lia) ltac:(clear; lia))).
assert (G22 : getr (ms_regs ms3) 22 = Z_to_bv 64 (F + 5152)) by exact (RD 22%bv (SOff 54 5152) _ eq_refl (denot_off E 54 F 5152 RF HFrng)).
assert (G23 : getr (ms_regs ms3) 23 = Z_to_bv 64 r) by exact (RD 23%bv (SOff 10 0) _ eq_refl (hlg_denot_off0 E 10 r E10n Hrrng)).
assert (G26 : getr (ms_regs ms3) 26 = Z_to_bv 64 (SB + F / 8 + 532)) by exact (RD 26%bv (SOff 67 532) _ eq_refl (denot_off E 67 (SB + F / 8) 532 E67 ltac:(clear - HSBF; lia))).
assert (G27 : getr (ms_regs ms3) 27 = Z_to_bv 64 F) by exact (RD 27%bv (SOff 54 0) _ eq_refl (hlg_denot_off0 E 54 F RF HFrng)).
assert (G28 : getr (ms_regs ms3) 28 = Z_to_bv 64 0) by exact (RD 28%bv (SLit 0) _ eq_refl eq_refl).
assert (G29 : getr (ms_regs ms3) 29 = Z_to_bv 64 0) by exact (RD 29%bv (SLit 0) _ eq_refl eq_refl).
assert (G20 : getr (ms_regs ms3) 20 = Z_to_bv 64 tb) by exact (RD 20%bv (SOff 305 0) _ eq_refl (hlg_denot_off0 E 305 tb Rtb Htb_rng)).
assert (G24 : getr (ms_regs ms3) 24 = Z_to_bv 64 (r + 60)) by exact (RD 24%bv (SOff 10 60) _ eq_refl (denot_off E 10 r 60 E10n Hrrng)).
assert (Hfq_in3 : In (fq, 4 * 524309) (ablocks B ly3 S3)) by (rewrite Eab3; apply in_or_app; right; do 3 right; left; reflexivity).
assert (Hhh_in3 : In (hh, 3 * 524309) (ablocks B ly3 S3)) by (rewrite Eab3; apply in_or_app; right; do 4 right; left; reflexivity).
assert (Huu_in3 : In (uu, 524309) (ablocks B ly3 S3)) by (rewrite Eab3; apply in_or_app; right; do 5 right; left; reflexivity).
assert (Hpp_in3 : In (pp, 3 * 524309) (ablocks B ly3 S3)) by (rewrite Eab3; apply in_or_app; right; do 6 right; left; reflexivity).
assert (Hxx_in3 : In (xx, 4 * 524309) (ablocks B ly3 S3)) by (rewrite Eab3; apply in_or_app; right; do 7 right; left; reflexivity).
assert (BLK : forall b n, In (b, n) (ablocks B ly3 S3) -> 0 <= n ->
4096 <= b /\ b + n <= alloc_ceiling /\ b mod 16 = 0 /\ (forall a, b <= a < b + n -> apresent (w_H W3) (ms_mem ms3) a)).
{ intros b n Hb Hn0. destruct (al_blocks _ _ LAWS _ _ _ _ _ b n HAR3 Hb) as (Hb16 & Hb4096 & Hbceil & _ & Hbpres & _ & _).
pose proof (req_size_pos n Hn0) as [_ Hrq]. split; [exact Hb4096|]. split; [clear - Hbceil Hrq; lia|]. split; [exact Hb16|].
intros a Ha. apply (proj1 (Hbpres a ltac:(clear - Ha Hrq; lia))). }
destruct (BLK fq _ Hfq_in3 ltac:(clear; lia)) as (Hfq4096 & Hfqceil & Hfq16 & Hfqpres).
destruct (BLK hh _ Hhh_in3 ltac:(clear; lia)) as (Hhh4096 & Hhhceil & Hhh16 & Hhhpres).
destruct (BLK uu _ Huu_in3 ltac:(clear; lia)) as (Huu4096 & Huuceil & Huu16 & Huupres).
destruct (BLK pp _ Hpp_in3 ltac:(clear; lia)) as (Hpp4096 & Hppceil & Hpp16 & Hpppres).
destruct (BLK xx _ Hxx_in3 ltac:(clear; lia)) as (Hxx4096 & Hxxceil & Hxx16 & Hxxpres).
assert (Bfq : 0 <= fq < 2 ^ 64) by (clear - Hfq4096 Hfqceil C1; lia).
assert (Bhh : 0 <= hh < 2 ^ 64) by (clear - Hhh4096 Hhhceil C1; lia).
assert (Buu : 0 <= uu < 2 ^ 64) by (clear - Huu4096 Huuceil C1; lia).
assert (Bpp : 0 <= pp < 2 ^ 64) by (clear - Hpp4096 Hppceil C1; lia).
assert (Bxx : 0 <= xx < 2 ^ 64) by (clear - Hxx4096 Hxxceil C1; lia).
destruct (st_ok_mem_ok trasegs E ss_HL0 _ HS) as (_ & Hrs0 & _).
pose proof (proj1 (Forall_forall _ _) Hrs0 _ (nth_error_In (ss_mem ss_HL0) 0%nat eq_refl)) as HRtb. cbn [ms_mem restrict] in HRtb.
assert (U305 : bv_unsigned (ew E 305) = tb) by (rewrite Rtb; apply unsigned_lit_small; exact Htb_rng).
assert (Hobj : obj_at trasegs (mrestrict (w_H W3) (ms_mem ms3)) tb LAY_Cht [fq; hh; uu; pp; xx; 0; 524309]).
{ pose proof (field_of_region E _ 305 tb _ 0 48 0 48 0 8%N (SOff 337 0) fq HRtb U305 ltac:(cbn; clear; tauto) (hlg_denot_off0 E 337 fq Rfq Bfq) Bfq ltac:(clear; lia)) as Vf.
pose proof (field_of_region E _ 305 tb _ 0 48 0 48 8 8%N (SOff 353 0) hh HRtb U305 ltac:(cbn; clear; tauto) (hlg_denot_off0 E 353 hh Rhh Bhh) Bhh ltac:(clear; lia)) as Vh.
pose proof (field_of_region E _ 305 tb _ 0 48 0 48 16 8%N (SOff 369 0) uu HRtb U305 ltac:(cbn; clear; tauto) (hlg_denot_off0 E 369 uu Ruu Buu) Buu ltac:(clear; lia)) as Vu.
pose proof (field_of_region E _ 305 tb _ 0 48 0 48 24 8%N (SOff 385 0) pp HRtb U305 ltac:(cbn; clear; tauto) (hlg_denot_off0 E 385 pp Rpp Bpp) Bpp ltac:(clear; lia)) as Vp.
pose proof (field_of_region E _ 305 tb _ 0 48 0 48 32 8%N (SOff 401 0) xx HRtb U305 ltac:(cbn; clear; tauto) (hlg_denot_off0 E 401 xx Rxx Bxx) Bxx ltac:(clear; lia)) as Vx.
pose proof (field_of_region E _ 305 tb _ 0 48 0 48 40 4%N (SLit 0) 0 HRtb U305 ltac:(cbn; clear; tauto) eq_refl ltac:(cbn; clear; lia) ltac:(clear; lia)) as Vc.
pose proof (field_of_region E _ 305 tb _ 0 48 0 48 44 4%N (SLit 524309) 524309 HRtb U305 ltac:(cbn; clear; tauto) eq_refl ltac:(cbn; clear; lia) ltac:(clear; lia)) as VT.
rewrite !Z.add_0_r in Vf.
cbn [obj_at LAY_Cht]. unfold field_ok. cbn [fst snd N.to_nat Pos.to_nat Pos.iter_op Nat.add]. rewrite Z.add_0_r.
change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32).
split; [split; [exact Vf | exact Bfq]|]. split; [split; [exact Vh | exact Bhh]|]. split; [split; [exact Vu | exact Buu]|].
split; [split; [exact Vp | exact Bpp]|]. split; [split; [exact Vx | exact Bxx]|]. split; [split; [exact Vc | clear; lia]|].
split; [split; [exact VT | clear; lia]|]. exact I. }
rewrite Ruu, unsigned_lit_small in Hz0 by exact Buu.
destruct (arr32_of_present trasegs (mrestrict (w_H W3) (ms_mem ms3)) fq (Z.to_nat 524309)) as (frN & AfrN & LfrN);
[intros a Ha; apply mbyte_of_apresent; apply Hfqpres; clear - Ha; lia|].
destruct (arr8_of_present trasegs (mrestrict (w_H W3) (ms_mem ms3)) hh (Z.to_nat (3 * 524309))) as (keysN & AkN & LkN);
[intros a Ha; apply mbyte_of_apresent; apply Hhhpres; clear - Ha; lia|].
destruct (arr8_of_present trasegs (mrestrict (w_H W3) (ms_mem ms3)) pp (Z.to_nat (3 * 524309))) as (palN & ApN & LpN);
[intros a Ha; apply mbyte_of_apresent; apply Hpppres; clear - Ha; lia|].
destruct (arr32_of_present trasegs (mrestrict (w_H W3) (ms_mem ms3)) xx (Z.to_nat 524309)) as (cixN & AcN & LcN);
[intros a Ha; apply mbyte_of_apresent; apply Hxxpres; clear - Ha; lia|].
assert (AuN : arr8 trasegs (mrestrict (w_H W3) (ms_mem ms3)) uu (repeat 0 (Z.to_nat 524309)))
by (apply arr8_zero; intros j Hj; apply hlg_byte_of_av; exact (Hz0 j Hj)).
set (K0 := mkHT frN keysN (repeat 0 (Z.to_nat 524309)) palN cixN 0 524309).
assert (INV0 : ht_inv K0 []).
{ subst K0. apply ht_empty_inv; [clear; lia | unfold zlen; rewrite LfrN; clear; lia | unfold zlen; rewrite LkN; clear; lia
| unfold zlen; rewrite LpN; clear; lia | unfold zlen; rewrite LcN; clear; lia | exact (arr8_Forall _ _ _ _ AkN) | exact (arr8_Forall _ _ _ _ ApN)]. }
set (C0 := mkACHT fq hh uu pp xx K0 []).
set (PROT := ablocks B ly S ++ [(blk, fmt * N); (fim, N)]).
assert (HHL : at_HL B TRGBADD_STK (spZ regs) (ablocks_fp [(r, RGB_SIZE)]) ly S W mem md [(7, fpos)]
(spZ regs - 512) tb img fmt N imgl (r + 60) F (SB + F / 8 + 532) r F (F + 5152) (SB + (r + 42) / 8) cfp (s0Z regs) (raZ regs) (SB + F / 8)
PROT ly3 S3 W3 (ms_mem ms3) ly3 S3 W3 (ms_regs ms3) (ms_mem ms3) md3 k C0 0 0).
{ unfold at_HL, hcore, hcore_raw.
split; [split; [| exact INV0] |].
- split; [exact HJ3|].
split; [split; [exact G2|]; split; [exact G9|]; split; [exact G8|]; split; [exact G3|]; split; [exact G4|]; split; [exact G25|]; split; [exact G18 | exact G19]|].
split; [exact Hslots|]. split; [exact Hobj|].
split; [split; [exact AfrN | split; [exact AkN | split; [exact AuN | split; [exact ApN | exact AcN]]]]|].
split; [exact Aimg|].
split; [unfold ht_lens, C0, K0; cbn [ac_H ht_used ht_keys ht_frequ ht_colidx ht_pal ht_T]; unfold zlen; rewrite repeat_length, LfrN, LkN, LpN, LcN; clear; lia|].
split; [left; reflexivity|].
split; [rewrite Eab3; unfold PROT; rewrite <- app_assoc; apply Permutation_refl|].
split.
{ intros b n Hin. unfold C0, K0, ac_blocks, cht_blocks in Hin. cbn [In ac_f ac_h ac_u ac_p ac_x ac_T ac_H ht_T] in Hin.
destruct Hin as [Hin|[Hin|[Hin|[Hin|[Hin|[Hin|[]]]]]]]; injection Hin as <- <-.
- split; [exact Ttb | exact Atb].
- split; [exact Tfq | exact Afq].
- split; [exact Thh | exact Ahh].
- split; [exact Tuu | exact Auu].
- split; [exact Tpp | exact App].
- split; [exact Txx | exact Axx]. }
split; [split; [replace (ts_rank (ac_T C0)) with 0 by reflexivity; clear - Hk0; lia | exact (gbud_of_rga_bud _ _ _ Hbud)]|].
unfold hk_kept. split; [reflexivity|]. split; [intros; reflexivity|]. split; [intros; reflexivity|]. split; intros; reflexivity.
- split; [split; [exact G5|]; split; [exact G6|]; split; [exact G7|]; split; [exact G16|]; split; [exact G17|]; split; [exact G22|]; split; [exact G23|];
split; [exact G26 | exact G27]|].
split; [exact G28|]. split; [exact G29|]. split; [clear - HN1; lia|]. split; [left; reflexivity|]. cbn. clear; lia. }
assert (HOPv : hk_opaque_ok (r + 60) F (SB + F / 8 + 532) r F (F + 5152) (SB + (r + 42) / 8) cfp (s0Z regs) (raZ regs)).
{ unfold hk_opaque_ok. split; [clear - Hr4096 Hrceil C1; lia|]. split; [exact HFrng|]. split; [clear - HSBF; lia|]. split; [exact Hrrng|]. split; [exact HFrng|].
split; [clear - HF4096 HFceil C1; lia|]. split; [exact (HSHR r 42 ltac:(clear - Hr4096; lia) ltac:(clear - Hrceil C1; lia) ltac:(clear; lia))|].
split; [clear - Hcfprng C1; lia|]. split; [exact Hs0rng | exact Hrarng]. }
assert (HNv : 1 <= N <= 10000) by (clear - HN1 HN; unfold RGB_NMAX in HN; lia).
assert (HimgP : In (img, fmt * N) PROT) by (unfold PROT; apply in_or_app; left; exact Himg_in).
assert (HEV100 : vev S + 80 <= VEV_MAX) by (apply YG0t.vev_of_bud; eapply bud_ok_mono; [exact Hev | clear; rga_lia ..]).
assert (HLIVEv : bsum PROT + 2 ^ 30 <= LIVE_MAX).
{ unfold PROT. rewrite bsum_app, <- (blocks_bytes_bsum B ly S).
let v := eval vm_compute in LIVE_RGBADD in assert (HLv : LIVE_RGBADD = v) by reflexivity.
clear - Hlive HLv HfN HNv. unfold RGB_NMAX in HfN. rewrite !bsum_cons. change (bsum []) with 0. cbn [snd]. lia. }
pose proof HS as HS0.
rewrite (st_ok_restrict_mkst trasegs _ _ _ _ HS eq_refl). cbn [ss_pc ss_HL0].
change (Z_to_bv 64 534188) with (Z_to_bv 64 HL_HEAD).
eapply SRr_bind.
{ exact (hl_hist B LAWS TRGBADD_STK (spZ regs) (ablocks_fp [(r, RGB_SIZE)]) ly S W mem md [(7, fpos)]
(spZ regs - 512) tb img fmt N imgl (r + 60) F (SB + F / 8 + 532) r F (F + 5152) (SB + (r + 42) / 8) cfp (s0Z regs) (raZ regs) (SB + F / 8)
PROT ly3 S3 W3 (ms_mem ms3)
eq_refl ltac:(rewrite FFS; clear; lia) Hal32 HOPv Hfmt HNv HimgP Himgl AMEMSET TL ML AMALLOC AFREE AREALLOC ch
ltac:(rewrite FFS; unfold ASTACK; clear; lia) Htop32 Hch (eq_sym Hra88) Hspine HEV100 HLIVEv TCOLHASH AMEMCPY ABCMP
ly3 S3 W3 (ms_regs ms3) (ms_mem ms3) md3 k C0 0 0 HHL). }
cbv beta. intros W2 c2 _ [HXF | (ly2 & S2 & regs2 & mem2 & md2 & k2 & Cf & ha2 & -> & HHX)].
2: {
destruct HHX as ((HCr & HinvF) & HhomeF & G12f & HhaF & HzsF).
pose proof HCr as (HJ2 & (G2f & G9f & G8f & G3f & G4f & G25f & G18f & G19f) & HslF & HobjF & HarrF & HimgF & HlensF & HTF & HPermF & HpermF & Hk2 & HkeptF).
destruct HhomeF as (G5f & G6f & G7f & G16f & G17f & G22f & G23f & G26f & G27f).
destruct HkeptF as (KfrS & KfrA & Kstk & Kfrm & Kprot).
pose proof (proj1 HJ2) as HAR2.
destruct (hk_frame_facts B TRGBADD_STK (spZ regs) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl ltac:(rewrite FFS; clear; lia) Hal32 _ _ _ _ _ _ _ _ HCr)
as (_ & _ & _ & Hstkpres2).
assert (Hfin2 : In (7, fpos) (frames S2)) by (rewrite KfrS; exact Hfin3).
destruct (al_frames _ _ LAWS _ _ _ _ _ 7 fpos HAR2 Hfin2) as (_ & _ & HFpres2 & _).
rewrite (KfrA 7 fpos), EFA3 in HFpres2. fold F in HFpres2. change (fs_frame_bytes 7) with 8192 in HFpres2.
assert (Hrin2 : In (r, 64) (ablocks B ly2 S2)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPermF|]. apply in_or_app. left. unfold PROT. apply in_or_app. left. exact Hrin. }
destruct (al_blocks _ _ LAWS _ _ _ _ _ r 64 HAR2 Hrin2) as (_ & _ & _ & _ & Hrpres2 & _). change (req_size 64) with 64 in Hrpres2.
ga_aconsts HROD HJ2 Kgot6 Kcell6 Kguar6 Kuar6 Vgr6.
assert (Hsame : forall r0 : bv 5, reg_in r0 [1; 7; 10; 11; 12; 13; 14; 15; 20; 21; 24; 28; 29; 30; 31]%bv = false -> getr regs2 r0 = getr (ms_regs (restrict (w_H W3) ms3)) r0).
{ intros r0 Hr0. cbn [ms_regs restrict]. pose proof (all_regs_in r0) as Hin. cbv [all_regs In] in Hin.
repeat (destruct Hin as [<-|Hin]; [first [ reflexivity | vm_compute in Hr0; discriminate
| etransitivity; [eassumption | symmetry; eassumption] ] |]). destruct Hin. }
jafter_stretch_ck HS0 600%nat regs2 (mrestrict (w_H W2) mem2) ([1; 7; 10; 11; 12; 13; 14; 15; 20; 21; 24; 28; 29; 30; 31]%bv : list (bv 5)) 536800
[1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15]%nat HS2.
specialize (HS2 Hsame).
match type of HS2 with ?Q -> _ => assert (HQ : Q) end.
{ cbn [ms_mem restrict].
assert (U54 : base_val E (Some 54%nat) = F) by (cbn [base_val]; rewrite RF; apply unsigned_lit_small; exact HFrng).
assert (U67 : base_val E (Some 67%nat) = SB + F / 8) by (cbn [base_val]; rewrite E67; apply unsigned_lit_small; clear - HSBF; lia).
assert (U10 : base_val E (Some 10%nat) = r) by (cbn [base_val]; rewrite E10n; apply unsigned_lit_small; exact Hrrng).
assert (U11 : base_val E (Some 11%nat) = cfp) by (cbn [base_val]; rewrite E11n; apply unsigned_lit_small; clear - Hcfprng C1; lia).
assert (KF : forall a, F <= a < F + 8192 -> aview trasegs (w_H W2) mem2 a = aview trasegs (w_H W3) (ms_mem ms3) a).
{ intros a Ha. apply (Kfrm 7 fpos a Hfin3). left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite EFA3. fold F. change (fs_frame_bytes 7) with 8192. exact Ha. }
assert (KFS : forall a, SB + F / 8 <= a < SB + F / 8 + 1024 -> aview trasegs (w_H W2) mem2 a = aview trasegs (w_H W3) (ms_mem ms3) a).
{ intros a Ha. apply (Kfrm 7 fpos a Hfin3). right. unfold in_zr. cbn [fst snd]. rewrite EFA3. fold F. unfold shadow_addr.
change (fs_frame_bytes 7 / 8) with 1024. change SHADOW_OFF with SB. exact Ha. }
assert (KC : forall a, cfp <= a < cfp + 24 -> aview trasegs (w_H W2) mem2 a = aview trasegs (w_H W3) (ms_mem ms3) a).
{ intros a Ha. apply (Kfrm cid pos a HfinS3). left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite EFA3. clear - Ha Hflo Hfhi. lia. }
assert (KR : forall a, r <= a < r + 64 -> aview trasegs (w_H W2) mem2 a = aview trasegs (w_H W3) (ms_mem ms3) a).
{ intros a Ha. replace a with (r + (a - r)) by lia. apply (Kprot r 64); [unfold PROT; apply in_or_app; left; exact Hrin | change (req_size 64) with 64; clear - Ha; lia]. }
repeat apply Forall_cons; try apply Forall_nil.
all: lazymatch goal with |- region_kept_ck _ _ _ _ ?rr => lazymatch rr with
| YQ0b.mkRegion (Some 54%nat) _ _ _ _ _ =>
apply (hlg_kept_rng E _ _ _ _ rr F U54 ltac:(vm_compute; reflexivity));
cbn [YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi]; [intros a Ha; apply KF; clear - Ha; lia | intros a Ha; apply (proj1 (HFpres2 a ltac:(clear - Ha; lia)))]
| YQ0b.mkRegion (Some 67%nat) _ _ _ _ _ =>
apply (hlg_kept_rng E _ _ _ _ rr (SB + F / 8) U67 ltac:(vm_compute; reflexivity));
cbn [YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi]; [intros a Ha; apply KFS; clear - Ha; lia | intros a Ha; exfalso; clear - Ha; lia]
| YQ0b.mkRegion (Some 11%nat) _ _ _ _ _ =>
apply (hlg_kept_rng E _ _ _ _ rr cfp U11 ltac:(vm_compute; reflexivity));
cbn [YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi]; [intros a Ha; apply KC; clear - Ha; lia | intros a Ha; exfalso; clear - Ha; lia]
| YQ0b.mkRegion (Some 10%nat) _ _ _ _ _ =>
apply (hlg_kept_rng E _ _ _ _ rr r U10 ltac:(vm_compute; reflexivity));
cbn [YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi]; [intros a Ha; apply KR; clear - Ha; lia | intros a Ha; apply (proj1 (Hrpres2 a ltac:(clear - Ha; lia)))]
| YQ0b.mkRegion (Some 2%nat) _ _ _ _ _ =>
apply (hlg_kept_stack E _ _ _ _ rr (spZ regs) U2 ltac:(vm_compute; reflexivity));
cbn [YQ0b.r_wlo YQ0b.r_whi]; [exact Kstk | intros a Ha; apply Hstkpres2; clear - Ha; lia]
| YQ0b.mkRegion None _ _ _ _ _ =>
apply region_kept_ck_of_kept; [vm_compute; reflexivity | ga_kept_consts Kgot0 Kgot6 Kcell0 Kcell6 Kguar0 Kguar6 Kuar0 Kuar6 Vgr0 Vgr6]
end end. }
specialize (HS2 HQ). clear HQ.
set (Tf := ac_T Cf) in *.
assert (HTf : 524309 <= Tf <= 16777259) by (clear - HTF; cbv [ts_chain In] in HTF; lia).
pose proof HobjF as OBJ. cbn [obj_at LAY_Cht] in OBJ. unfold field_ok in OBJ. cbn [fst snd N.to_nat Pos.to_nat Pos.iter_op Nat.add] in OBJ.
destruct OBJ as ([Vf _] & [Vh _] & [Vu _] & [Vp _] & [Vx _] & [Vc Bc] & [VT BT] & _). rewrite Z.add_0_r in Vf.
change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32) in Bc, BT.
assert (BLK2 : forall b n, In (b, n) (ac_blocks tb Cf) -> 0 <= n ->
In (b, n) (ablocks B ly2 S2) /\ 4096 <= b /\ b + n <= alloc_ceiling /\ b mod 16 = 0).
{ intros b n Hb Hn0.
assert (Hb2 : In (b, n) (ablocks B ly2 S2)) by (eapply Permutation_in; [apply Permutation_sym; exact HPermF|]; apply in_or_app; right; exact Hb).
destruct (al_blocks _ _ LAWS _ _ _ _ _ b n HAR2 Hb2) as (Hb16 & Hb4096 & Hbceil & _).
pose proof (req_size_pos n Hn0) as [_ Hrq]. split; [exact Hb2|]. split; [exact Hb4096|]. split; [clear - Hbceil Hrq; lia | exact Hb16]. }
destruct (BLK2 tb CHT_SIZE ltac:(left; reflexivity) ltac:(unfold CHT_SIZE; clear; lia)) as (Htb_in2 & _).
destruct (BLK2 (ac_f Cf) (4 * Tf) ltac:(right; left; reflexivity) ltac:(clear - HTf; lia)) as (Qf_in & Qf4096 & Qfceil & Qf16).
destruct (BLK2 (ac_h Cf) (3 * Tf) ltac:(do 2 right; left; reflexivity) ltac:(clear - HTf; lia)) as (Qh_in & Qh4096 & Qhceil & Qh16).
destruct (BLK2 (ac_u Cf) Tf ltac:(do 3 right; left; reflexivity) ltac:(clear - HTf; lia)) as (Qu_in & Qu4096 & Quceil & Qu16).
destruct (BLK2 (ac_p Cf) (3 * Tf) ltac:(do 4 right; left; reflexivity) ltac:(clear - HTf; lia)) as (Qp_in & Qp4096 & Qpceil & Qp16).
destruct (BLK2 (ac_x Cf) (4 * Tf) ltac:(do 5 right; left; reflexivity) ltac:(clear - HTf; lia)) as (Qx_in & Qx4096 & Qxceil & Qx16).
destruct (al_blocks _ _ LAWS _ _ _ _ _ tb CHT_SIZE HAR2 Htb_in2) as (_ & _ & _ & _ & Htbpres2 & _). change (req_size CHT_SIZE) with 48 in Htbpres2.
pose proof (st_ok_havoc trasegs 615 _ _ _
[Z_to_bv 64 (ac_f Cf); Z_to_bv 64 (ac_h Cf); Z_to_bv 64 (ac_u Cf); Z_to_bv 64 (ac_p Cf); Z_to_bv 64 (ac_x Cf); Z_to_bv 64 (ht_cnt (ac_H Cf)); Z_to_bv 64 Tf]
HS2 ltac:(vm_compute; reflexivity)) as HS3.
clear HS2.
lazymatch type of HS3 with st_ok _ ?Ev _ _ => set (Ex := Ev) in * end.
assert (AGx : forall n, (n < 600)%nat -> ew Ex n = ew E n) by (intros n Hn; unfold Ex; rewrite !ew_havoc_old by lia; reflexivity).
assert (E615 : ew Ex 615 = Z_to_bv 64 (ac_f Cf)) by (unfold Ex; change 615%nat with (615 + 0)%nat; rewrite (ew_havoc_new _ 615 _ 0 (Z_to_bv 64 0)) by (cbn [length]; lia); reflexivity).
assert (E616 : ew Ex 616 = Z_to_bv 64 (ac_h Cf)) by (unfold Ex; change 616%nat with (615 + 1)%nat; rewrite (ew_havoc_new _ 615 _ 1 (Z_to_bv 64 0)) by (cbn [length]; lia); reflexivity).
assert (E617 : ew Ex 617 = Z_to_bv 64 (ac_u Cf)) by (unfold Ex; change 617%nat with (615 + 2)%nat; rewrite (ew_havoc_new _ 615 _ 2 (Z_to_bv 64 0)) by (cbn [length]; lia); reflexivity).
assert (E618 : ew Ex 618 = Z_to_bv 64 (ac_p Cf)) by (unfold Ex; change 618%nat with (615 + 3)%nat; rewrite (ew_havoc_new _ 615 _ 3 (Z_to_bv 64 0)) by (cbn [length]; lia); reflexivity).
assert (E619 : ew Ex 619 = Z_to_bv 64 (ac_x Cf)) by (unfold Ex; change 619%nat with (615 + 4)%nat; rewrite (ew_havoc_new _ 615 _ 4 (Z_to_bv 64 0)) by (cbn [length]; lia); reflexivity).
assert (E620 : ew Ex 620 = Z_to_bv 64 (ht_cnt (ac_H Cf))) by (unfold Ex; change 620%nat with (615 + 5)%nat; rewrite (ew_havoc_new _ 615 _ 5 (Z_to_bv 64 0)) by (cbn [length]; lia); reflexivity).
assert (E621 : ew Ex 621 = Z_to_bv 64 Tf) by (unfold Ex; change 621%nat with (615 + 6)%nat; rewrite (ew_havoc_new _ 615 _ 6 (Z_to_bv 64 0)) by (cbn [length]; lia); reflexivity).
assert (E604 : ew Ex 604 = Z_to_bv 64 ha2).
{ unfold Ex. rewrite ew_havoc_old by lia. change 604%nat with (600 + 4)%nat. rewrite (ew_havoc_new _ 600 _ 4 (Z_to_bv 64 0)) by (cbn [length map]; lia). cbn [nth map]. exact G12f. }
pose proof (rga_perm_sep B LAWS ly3 S3 _ _ _ _ _ (r, 64) (tb, 48) HAR3 ltac:(rewrite Eab3; apply Permutation_refl) Hrin ltac:(right; right; left; reflexivity)) as HzR_tb.
unfold zdisjoint, block_rng in HzR_tb. cbn [fst snd] in HzR_tb. change (req_size 64) with 64 in HzR_tb. change (req_size 48) with 48 in HzR_tb.
pose proof (sep_block_frame trasegs B LAWS ly3 S3 _ _ _ tb (48) 7 fpos HAR3 Htb_in3 Hfin3) as HdF_tb.
unfold zdisjoint in HdF_tb. cbn [fst snd] in HdF_tb. change (fs_frame_bytes 7) with 8192 in HdF_tb. rewrite EFA3 in HdF_tb. fold F in HdF_tb. change (req_size 48) with 48 in HdF_tb.
pose proof (sep_block_frame trasegs B LAWS ly3 S3 _ _ _ tb (48) cid pos HAR3 Htb_in3 HfinS3) as HdC_tb.
unfold zdisjoint in HdC_tb. cbn [fst snd] in HdC_tb. rewrite EFA3 in HdC_tb. change (req_size 48) with 48 in HdC_tb.
assert (UX305 : bv_unsigned (ew Ex 305) = tb) by (rewrite AGx by lia; exact U305).
assert (UX54 : bv_unsigned (ew Ex 54) = F) by (rewrite AGx by lia; rewrite RF; apply unsigned_lit_small; exact HFrng).
assert (UX67 : bv_unsigned (ew Ex 67) = SB + F / 8) by (rewrite AGx by lia; rewrite E67; apply unsigned_lit_small; clear - HSBF; lia).
assert (UX2 : bv_unsigned (ew Ex 2) = spZ regs) by (rewrite AGx by lia; exact U2).
assert (UX10 : bv_unsigned (ew Ex 10) = r) by (rewrite AGx by lia; rewrite E10n; apply unsigned_lit_small; exact Hrrng).
assert (UX11 : bv_unsigned (ew Ex 11) = cfp) by (rewrite AGx by lia; rewrite E11n; apply unsigned_lit_small; clear - Hcfprng C1; lia).
assert (HFS8 : F / 8 + 1024 <= 17592186044416) by (clear - HFq HF8 HFceil C1; lia).
assert (Bf64 : 0 <= ac_f Cf < 2 ^ 64) by (clear - Qf4096 Qfceil C1 HTf; lia).
assert (Bh64 : 0 <= ac_h Cf < 2 ^ 64) by (clear - Qh4096 Qhceil C1 HTf; lia).
assert (Bu64 : 0 <= ac_u Cf < 2 ^ 64) by (clear - Qu4096 Quceil C1 HTf; lia).
assert (Bp64 : 0 <= ac_p Cf < 2 ^ 64) by (clear - Qp4096 Qpceil C1 HTf; lia).
assert (Bx64 : 0 <= ac_x Cf < 2 ^ 64) by (clear - Qx4096 Qxceil C1 HTf; lia).
pose proof (ast_ok_add_region trasegs Ex _ _
(YQ0b.mkRegion (Some 305%nat) 0 48 0 48
[YQ0b.mkChunk 0 (CVal 8 (SOff 615 0)); YQ0b.mkChunk 8 (CVal 8 (SOff 616 0)); YQ0b.mkChunk 16 (CVal 8 (SOff 617 0));
YQ0b.mkChunk 24 (CVal 8 (SOff 618 0)); YQ0b.mkChunk 32 (CVal 8 (SOff 619 0)); YQ0b.mkChunk 40 (CVal 4 (SOff 620 0)); YQ0b.mkChunk 44 (CVal 4 (SOff 621 0))])
HS3 eq_refl) as HS4.
cbn [ms_mem mkst] in HS4.
assert (HRK : region_ok trasegs Ex (mrestrict (w_H W2) mem2)
(YQ0b.mkRegion (Some 305%nat) 0 48 0 48
[YQ0b.mkChunk 0 (CVal 8 (SOff 615 0)); YQ0b.mkChunk 8 (CVal 8 (SOff 616 0)); YQ0b.mkChunk 16 (CVal 8 (SOff 617 0));
YQ0b.mkChunk 24 (CVal 8 (SOff 618 0)); YQ0b.mkChunk 32 (CVal 8 (SOff 619 0)); YQ0b.mkChunk 40 (CVal 4 (SOff 620 0)); YQ0b.mkChunk 44 (CVal 4 (SOff 621 0))])).
{ unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val]. rewrite UX305.
split; [clear - Htb4096; lia|]. split; [clear - Htbceil Hrqtb C1; lia|]. split.
- intros o Ho. apply (apresent_writable trasegs). apply (proj1 (Htbpres2 (tb + o) ltac:(clear - Ho; lia))).
- apply Forall_cons; [apply (chunk_ok_val trasegs Ex _ tb 0 8 _ (ac_f Cf) (hlg_denot_off0 Ex 615 _ E615 Bf64) Bf64 ltac:(clear; lia)); rewrite Z.add_0_r; exact Vf|].
apply Forall_cons; [exact (chunk_ok_val trasegs Ex _ tb 8 8 _ (ac_h Cf) (hlg_denot_off0 Ex 616 _ E616 Bh64) Bh64 ltac:(clear; lia) Vh)|].
apply Forall_cons; [exact (chunk_ok_val trasegs Ex _ tb 16 8 _ (ac_u Cf) (hlg_denot_off0 Ex 617 _ E617 Bu64) Bu64 ltac:(clear; lia) Vu)|].
apply Forall_cons; [exact (chunk_ok_val trasegs Ex _ tb 24 8 _ (ac_p Cf) (hlg_denot_off0 Ex 618 _ E618 Bp64) Bp64 ltac:(clear; lia) Vp)|].
apply Forall_cons; [exact (chunk_ok_val trasegs Ex _ tb 32 8 _ (ac_x Cf) (hlg_denot_off0 Ex 619 _ E619 Bx64) Bx64 ltac:(clear; lia) Vx)|].
apply Forall_cons; [exact (chunk_ok_val trasegs Ex _ tb 40 4 _ (ht_cnt (ac_H Cf)) (hlg_denot_off0 Ex 620 _ E620 ltac:(clear - Bc; lia)) Bc ltac:(clear; lia) Vc)|].
apply Forall_cons; [exact (chunk_ok_val trasegs Ex _ tb 44 4 _ Tf (hlg_denot_off0 Ex 621 _ E621 ltac:(clear - BT; lia)) BT ltac:(clear; lia) VT)|].
apply Forall_nil. }
specialize (HS4 HRK).
match type of HS4 with ?Q -> _ => assert (HQ : Q) end.
{ lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end.
cbn [all_disjoint]. unfold extent_disjoint. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val]. rewrite ?UX305, ?UX54, ?UX67, ?UX2, ?UX10, ?UX11.
repeat split; lazymatch goal with
| |- context [spZ regs] => clear - Htbceil Hrqtb Hsp47; lia
| |- context [F / 8] => clear - Htbzone Hrqtb Htb4096 HFS8 HF8lo; unfold gbox, SB in *; lia
| |- context [F] => clear - HdF_tb; lia
| |- context [cfp] => clear - HdC_tb Hflo Hfhi; lia
| |- context [r] => clear - HzR_tb; lia
| |- _ => clear - Htbzone Hrqtb Htb4096; unfold gbox in *; lia
end. }
specialize (HS4 HQ). clear HQ HS3.
ga_join_fact HS4 604%nat (mkAF 0 1 0) ltac:(rewrite E604; rewrite unsigned_lit_small by (clear - HhaF; lia); change (2 ^ 0) with 1; split; [clear - HhaF; lia|]; split; [apply Z.mod_1_r | clear; lia]).
ga_join_fact HS4 621%nat (mkAF 0 4294967295 0) ltac:(rewrite E621; rewrite unsigned_lit_small by (clear - BT; lia); change (2 ^ 0) with 1; split; [clear - BT; lia|]; split; [apply Z.mod_1_r | clear; lia]).
ga_join_fact HS4 620%nat (mkAF 0 4294967295 0) ltac:(rewrite E620; rewrite unsigned_lit_small by (clear - Bc; lia); change (2 ^ 0) with 1; split; [clear - Bc; lia|]; split; [apply Z.mod_1_r | clear; lia]).
ga_join_fact HS4 619%nat (mkAF 4096 140737479966720 4) ltac:(rewrite E619; rewrite unsigned_lit_small by exact Bx64; change (2 ^ 4) with 16; split; [clear - Qx4096 Qxceil C1 HTf; lia|]; split; [exact Qx16 | clear; lia]).
ga_join_fact HS4 618%nat (mkAF 4096 140737479966720 4) ltac:(rewrite E618; rewrite unsigned_lit_small by exact Bp64; change (2 ^ 4) with 16; split; [clear - Qp4096 Qpceil C1 HTf; lia|]; split; [exact Qp16 | clear; lia]).
ga_join_fact HS4 617%nat (mkAF 4096 140737479966720 4) ltac:(rewrite E617; rewrite unsigned_lit_small by exact Bu64; change (2 ^ 4) with 16; split; [clear - Qu4096 Quceil C1 HTf; lia|]; split; [exact Qu16 | clear; lia]).
ga_join_fact HS4 616%nat (mkAF 4096 140737479966720 4) ltac:(rewrite E616; rewrite unsigned_lit_small by exact Bh64; change (2 ^ 4) with 16; split; [clear - Qh4096 Qhceil C1 HTf; lia|]; split; [exact Qh16 | clear; lia]).
ga_join_fact HS4 615%nat (mkAF 4096 140737479966720 4) ltac:(rewrite E615; rewrite unsigned_lit_small by exact Bf64; change (2 ^ 4) with 16; split; [clear - Qf4096 Qfceil C1 HTf; lia|]; split; [exact Qf16 | clear; lia]).
norm_ss HS4.
lazymatch type of HS4 with st_ok _ ?Exx ?ssx ?msx =>
let tg := eval red in ss_HD in
let fa := eval cbn [ss_facts f_atoms] in (f_atoms (ss_facts tg)) in
let cs := eval cbn [ss_facts f_conds] in (f_conds (ss_facts tg)) in
let al := eval cbn [ss_facts f_alias] in (f_alias (ss_facts tg)) in
pose proof (st_ok_facts_incl3 trasegs Exx ssx msx fa cs al HS4 ltac:(ga_incl_lit_tac) ltac:(ga_incl_lit_tac) ltac:(ga_incl_lit_tac)) as HS5 end.
clear HS4. norm_ss HS5.
lazymatch type of HS5 with st_ok _ _ ?ssx _ => first [change ssx with ss_HD in HS5 | idtac "JOIN-MISMATCH" ssx] end.
rewrite <- restrict_mkst_fx in HS5.
assert (Hfrs2 : frames S2 = (7, fpos) :: frames S) by (rewrite KfrS; exact Hfrs3).
change (Z_to_bv 64 HL_EXIT) with (Z_to_bv 64 536800).
rga_hand RC HS5 HJ2 k2; [unfold Ex; rga_E_tac HEE0 | ].
exists blk, fim, tb, (ac_f Cf), (ac_h Cf), (ac_u Cf), (ac_p Cf), (ac_x Cf), ha2, (ac_H Cf), (ac_ent Cf).
split; [split; [pose proof (ts_rank_range Tf) as Hrk; unfold EV_HD; clear - Hk2 Hrk; lia | (apply rga_bud_of_gbud; exact (proj2 Hk2))]|].
split; [exact Hfmt|].
split; [unfold PROT in HPermF; rewrite <- app_assoc in HPermF; exact HPermF|].
split; [split; [rewrite AGx by lia; exact Rblk | split; [exact Tblk | exact Ablk]]|].
split; [split; [rewrite AGx by lia; exact Rfim | split; [exact Tfim | exact Afim]]|].
split; [split; [rewrite AGx by lia; exact Rtb | split; [exact Ttb | exact Atb]]|].
split; [split; [exact E615 | exact (HpermF (ac_f Cf) (4 * Tf) ltac:(right; left; reflexivity))]|].
split; [split; [exact E616 | exact (HpermF (ac_h Cf) (3 * Tf) ltac:(do 2 right; left; reflexivity))]|].
split; [split; [exact E617 | exact (HpermF (ac_u Cf) Tf ltac:(do 3 right; left; reflexivity))]|].
split; [split; [exact E618 | exact (HpermF (ac_p Cf) (3 * Tf) ltac:(do 4 right; left; reflexivity))]|].
split; [split; [exact E619 | exact (HpermF (ac_x Cf) (4 * Tf) ltac:(do 5 right; left; reflexivity))]|].
split; [exact E620|]. split; [exact E621|]. split; [exact E604|]. split; [exact HhaF|].
split; [exact HarrF|]. split; [exact HinvF|]. split; [exact HTF|]. split; [exact HzsF|].
exists av. split; [rewrite AGx by lia; exact E300 | exact Hav].
}
destruct HXF as (ly2 & S2 & regs2 & mem2 & md2 & k2 & Cx & ix & hax & p1 & x1 & -> & HXc & G27x).
pose proof HXc as (HCr & HFx & Hk2 & _ & Hokp & Hokx & G20x & G24x & G26x).
pose proof HCr as (HJ2 & (G2f & G9f & G8f & G3f & G4f & G25f & G18f & G19f) & HslF & HobjF & HimgF & HPermF & HpermF & HkeptF).
destruct HkeptF as (KfrS & KfrA & Kstk & Kfrm & Kprot).
pose proof (proj1 HJ2) as HAR2.
pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
assert (Hstkpres2 : forall a, spZ regs - 512 <= a < spZ regs - 512 + 512 -> apresent (w_H W2) mem2 a) by (intros a Ha; apply Hpres2; rewrite FFS; clear - Ha; lia).
assert (Hfin2 : In (7, fpos) (frames S2)) by (rewrite KfrS; exact Hfin3).
destruct (al_frames _ _ LAWS _ _ _ _ _ 7 fpos HAR2 Hfin2) as (_ & _ & HFpres2 & _).
rewrite (KfrA 7 fpos), EFA3 in HFpres2. fold F in HFpres2. change (fs_frame_bytes 7) with 8192 in HFpres2.
assert (Hrin2 : In (r, 64) (ablocks B ly2 S2)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPermF|]. apply in_or_app. left. unfold PROT. apply in_or_app. left. exact Hrin. }
destruct (al_blocks _ _ LAWS _ _ _ _ _ r 64 HAR2 Hrin2) as (_ & _ & _ & _ & Hrpres2 & _). change (req_size 64) with 64 in Hrpres2.
assert (Hsame : forall r0 : bv 5, reg_in r0 [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 21; 22; 23; 28; 29; 30; 31]%bv = false -> getr regs2 r0 = getr (ms_regs (restrict (w_H W3) ms3)) r0).
{ intros r0 Hr0. cbn [ms_regs restrict]. pose proof (all_regs_in r0) as Hin. cbv [all_regs In] in Hin.
repeat (destruct Hin as [<-|Hin]; [first [ reflexivity | vm_compute in Hr0; discriminate
| etransitivity; [eassumption | symmetry; eassumption] ] |]). destruct Hin. }
pose proof (st_ok_after_stretch_ck trasegs 500%nat E ss_HL0 _ regs2 (mrestrict (w_H W2) mem2)
ltac:(let v := eval vm_compute in rga_XB_mem in exact v) 0x83ae8
([1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 21; 22; 23; 28; 29; 30; 31]%bv : list (bv 5)) HS0 eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(unfold ss_HL0; cbn [ss_mem]; ga_submem_to) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) Hsame) as HS2.
match type of HS2 with ?Q -> _ => assert (HQ : Q) end.
{ cbn [ms_mem restrict].
assert (U54 : base_val E (Some 54%nat) = F) by (cbn [base_val]; rewrite RF; apply unsigned_lit_small; exact HFrng).
assert (U67 : base_val E (Some 67%nat) = SB + F / 8) by (cbn [base_val]; rewrite E67; apply unsigned_lit_small; clear - HSBF; lia).
assert (U10 : base_val E (Some 10%nat) = r) by (cbn [base_val]; rewrite E10n; apply unsigned_lit_small; exact Hrrng).
assert (KF : forall a, F <= a < F + 8192 -> aview trasegs (w_H W2) mem2 a = aview trasegs (w_H W3) (ms_mem ms3) a).
{ intros a Ha. apply (Kfrm 7 fpos a Hfin3). left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite EFA3. fold F. change (fs_frame_bytes 7) with 8192. exact Ha. }
assert (KFS : forall a, SB + F / 8 <= a < SB + F / 8 + 1024 -> aview trasegs (w_H W2) mem2 a = aview trasegs (w_H W3) (ms_mem ms3) a).
{ intros a Ha. apply (Kfrm 7 fpos a Hfin3). right. unfold in_zr. cbn [fst snd]. rewrite EFA3. fold F. unfold shadow_addr.
change (fs_frame_bytes 7 / 8) with 1024. change SHADOW_OFF with SB. exact Ha. }
assert (KR : forall a, r <= a < r + 64 -> aview trasegs (w_H W2) mem2 a = aview trasegs (w_H W3) (ms_mem ms3) a).
{ intros a Ha. replace a with (r + (a - r)) by lia. apply (Kprot r 64); [unfold PROT; apply in_or_app; left; exact Hrin | change (req_size 64) with 64; clear - Ha; lia]. }
repeat apply Forall_cons; try apply Forall_nil.
all: lazymatch goal with |- region_kept_ck _ _ _ _ ?rr => lazymatch rr with
| YQ0b.mkRegion (Some 54%nat) _ _ _ _ _ =>
apply (hlg_kept_rng E _ _ _ _ rr F U54 ltac:(vm_compute; reflexivity));
cbn [YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi]; [intros a Ha; apply KF; clear - Ha; lia | intros a Ha; apply (proj1 (HFpres2 a ltac:(clear - Ha; lia)))]
| YQ0b.mkRegion (Some 67%nat) _ _ _ _ _ =>
apply (hlg_kept_rng E _ _ _ _ rr (SB + F / 8) U67 ltac:(vm_compute; reflexivity));
cbn [YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi]; [intros a Ha; apply KFS; clear - Ha; lia | intros a Ha; exfalso; clear - Ha; lia]
| YQ0b.mkRegion (Some 10%nat) _ _ _ _ _ =>
apply (hlg_kept_rng E _ _ _ _ rr r U10 ltac:(vm_compute; reflexivity));
cbn [YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi]; [intros a Ha; apply KR; clear - Ha; lia | intros a Ha; apply (proj1 (Hrpres2 a ltac:(clear - Ha; lia)))]
| YQ0b.mkRegion (Some 2%nat) _ _ _ _ _ =>
apply (hlg_kept_stack E _ _ _ _ rr (spZ regs) U2 ltac:(vm_compute; reflexivity));
cbn [YQ0b.r_wlo YQ0b.r_whi]; [exact Kstk | intros a Ha; apply Hstkpres2; clear - Ha; lia]
end end. }
specialize (HS2 HQ). clear HQ.
set (Tx := ac_T Cx) in *. set (Tn := ac_Tn Cx) in *.
set (pv := rsel (ac_p Cx) p1). set (xv := rsel (ac_x Cx) x1).
set (npv := if p1 =? 0 then 3 * Tx else 3 * Tn). set (nxv := if x1 =? 0 then 4 * Tx else 4 * Tn).
assert (Erp : rbk (ac_p Cx, 3 * Tx) p1 (3 * Tn) = (pv, npv)) by (unfold rbk, pv, npv, rsel; destruct (p1 =? 0); reflexivity).
assert (Erx : rbk (ac_x Cx, 4 * Tx) x1 (4 * Tn) = (xv, nxv)) by (unfold rbk, xv, nxv, rsel; destruct (x1 =? 0); reflexivity).
assert (EBL : rz_BL Cx p1 x1 = [(ac_f Cx, 4 * Tx); (ac_h Cx, 3 * Tx); (ac_u Cx, Tx); (pv, npv); (xv, nxv)]) by (unfold rz_BL; fold Tx Tn; rewrite Erp, Erx; reflexivity).
rewrite EBL in HPermF, HpermF.
pose proof HobjF as OBJ. unfold xf_cells in OBJ. fold pv xv in OBJ. cbn [obj_at LAY_Cht] in OBJ. unfold field_ok in OBJ. cbn [fst snd N.to_nat Pos.to_nat Pos.iter_op Nat.add] in OBJ.
destruct OBJ as ([Vf _] & [Vh _] & [Vu _] & [Vp _] & [Vx _] & _). rewrite Z.add_0_r in Vf.
assert (BLK2 : forall b n, In (b, n) [(ac_f Cx, 4 * Tx); (ac_h Cx, 3 * Tx); (ac_u Cx, Tx); (pv, npv); (xv, nxv)] -> 4096 <= b < 2 ^ 64).
{ intros b n Hb.
assert (Hb2 : In (b, n) (ablocks B ly2 S2)) by (eapply Permutation_in; [apply Permutation_sym; exact HPermF|]; apply in_or_app; right; right; exact Hb).
destruct (al_blocks _ _ LAWS _ _ _ _ _ b n HAR2 Hb2) as (_ & Hb4096 & Hbceil & _ & _ & _ & Hn0).
pose proof (req_size_pos n (proj1 Hn0)) as [Hrq _]. clear - Hb4096 Hbceil Hrq C1. lia. }
pose proof (BLK2 _ _ ltac:(left; reflexivity)) as Qf. pose proof (BLK2 _ _ ltac:(right; left; reflexivity)) as Qh.
pose proof (BLK2 _ _ ltac:(do 2 right; left; reflexivity)) as Qu. pose proof (BLK2 _ _ ltac:(do 3 right; left; reflexivity)) as Qp.
pose proof (BLK2 _ _ ltac:(do 4 right; left; reflexivity)) as Qx.
assert (Htb_in2 : In (tb, CHT_SIZE) (ablocks B ly2 S2)) by (eapply Permutation_in; [apply Permutation_sym; exact HPermF|]; apply in_or_app; right; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ tb CHT_SIZE HAR2 Htb_in2) as (_ & _ & _ & _ & Htbpres2 & _). change (req_size CHT_SIZE) with 48 in Htbpres2.
pose proof (st_ok_havoc trasegs 519 _ _ _ [Z_to_bv 64 (ac_f Cx); Z_to_bv 64 (ac_h Cx); Z_to_bv 64 (ac_u Cx); Z_to_bv 64 pv; Z_to_bv 64 xv]
HS2 ltac:(vm_compute; reflexivity)) as HS3.
clear HS2.
lazymatch type of HS3 with st_ok _ ?Ev _ _ => set (Ex := Ev) in * end.
assert (AGx : forall n, (n < 500)%nat -> ew Ex n = ew E n) by (intros n Hn; unfold Ex; rewrite !ew_havoc_old by lia; reflexivity).
assert (E519 : ew Ex 519 = Z_to_bv 64 (ac_f Cx)) by (unfold Ex; change 519%nat with (519 + 0)%nat; rewrite (ew_havoc_new _ 519 _ 0 (Z_to_bv 64 0)) by (cbn [length]; lia); reflexivity).
assert (E520 : ew Ex 520 = Z_to_bv 64 (ac_h Cx)) by (unfold Ex; change 520%nat with (519 + 1)%nat; rewrite (ew_havoc_new _ 519 _ 1 (Z_to_bv 64 0)) by (cbn [length]; lia); reflexivity).
assert (E521 : ew Ex 521 = Z_to_bv 64 (ac_u Cx)) by (unfold Ex; change 521%nat with (519 + 2)%nat; rewrite (ew_havoc_new _ 519 _ 2 (Z_to_bv 64 0)) by (cbn [length]; lia); reflexivity).
assert (E522 : ew Ex 522 = Z_to_bv 64 pv) by (unfold Ex; change 522%nat with (519 + 3)%nat; rewrite (ew_havoc_new _ 519 _ 3 (Z_to_bv 64 0)) by (cbn [length]; lia); reflexivity).
assert (E523 : ew Ex 523 = Z_to_bv 64 xv) by (unfold Ex; change 523%nat with (519 + 4)%nat; rewrite (ew_havoc_new _ 519 _ 4 (Z_to_bv 64 0)) by (cbn [length]; lia); reflexivity).
pose proof (rga_perm_sep B LAWS ly3 S3 _ _ _ _ _ (r, 64) (tb, 48) HAR3 ltac:(rewrite Eab3; apply Permutation_refl) Hrin ltac:(right; right; left; reflexivity)) as HzR_tb.
unfold zdisjoint, block_rng in HzR_tb. cbn [fst snd] in HzR_tb. change (req_size 64) with 64 in HzR_tb. change (req_size 48) with 48 in HzR_tb.
pose proof (sep_block_frame trasegs B LAWS ly3 S3 _ _ _ tb (48) 7 fpos HAR3 Htb_in3 Hfin3) as HdF_tb.
unfold zdisjoint in HdF_tb. cbn [fst snd] in HdF_tb. change (fs_frame_bytes 7) with 8192 in HdF_tb. rewrite EFA3 in HdF_tb. fold F in HdF_tb. change (req_size 48) with 48 in HdF_tb.
assert (UX305 : bv_unsigned (ew Ex 305) = tb) by (rewrite AGx by lia; exact U305).
assert (UX54 : bv_unsigned (ew Ex 54) = F) by (rewrite AGx by lia; rewrite RF; apply unsigned_lit_small; exact HFrng).
assert (UX67 : bv_unsigned (ew Ex 67) = SB + F / 8) by (rewrite AGx by lia; rewrite E67; apply unsigned_lit_small; clear - HSBF; lia).
assert (UX2 : bv_unsigned (ew Ex 2) = spZ regs) by (rewrite AGx by lia; exact U2).
assert (UX10 : bv_unsigned (ew Ex 10) = r) by (rewrite AGx by lia; rewrite E10n; apply unsigned_lit_small; exact Hrrng).
assert (HFS8 : F / 8 + 1024 <= 17592186044416) by (clear - HFq HF8 HFceil C1; lia).
pose proof (ast_ok_add_region trasegs Ex _ _
(YQ0b.mkRegion (Some 305%nat) 0 48 0 48
[YQ0b.mkChunk 32 (CVal 8 (SOff 523 0)); YQ0b.mkChunk 24 (CVal 8 (SOff 522 0)); YQ0b.mkChunk 16 (CVal 8 (SOff 521 0));
YQ0b.mkChunk 8 (CVal 8 (SOff 520 0)); YQ0b.mkChunk 0 (CVal 8 (SOff 519 0))])
HS3 eq_refl) as HS4.
cbn [ms_mem mkst] in HS4.
assert (HRK : region_ok trasegs Ex (mrestrict (w_H W2) mem2)
(YQ0b.mkRegion (Some 305%nat) 0 48 0 48
[YQ0b.mkChunk 32 (CVal 8 (SOff 523 0)); YQ0b.mkChunk 24 (CVal 8 (SOff 522 0)); YQ0b.mkChunk 16 (CVal 8 (SOff 521 0));
YQ0b.mkChunk 8 (CVal 8 (SOff 520 0)); YQ0b.mkChunk 0 (CVal 8 (SOff 519 0))])).
{ unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val]. rewrite UX305.
split; [clear - Htb4096; lia|]. split; [clear - Htbceil Hrqtb C1; lia|]. split.
- intros o Ho. apply (apresent_writable trasegs). apply (proj1 (Htbpres2 (tb + o) ltac:(clear - Ho; lia))).
- apply Forall_cons; [exact (chunk_ok_val trasegs Ex _ tb 32 8 _ xv (hlg_denot_off0 Ex 523 _ E523 ltac:(clear - Qx; lia)) ltac:(clear - Qx; lia) ltac:(clear; lia) Vx)|].
apply Forall_cons; [exact (chunk_ok_val trasegs Ex _ tb 24 8 _ pv (hlg_denot_off0 Ex 522 _ E522 ltac:(clear - Qp; lia)) ltac:(clear - Qp; lia) ltac:(clear; lia) Vp)|].
apply Forall_cons; [exact (chunk_ok_val trasegs Ex _ tb 16 8 _ (ac_u Cx) (hlg_denot_off0 Ex 521 _ E521 ltac:(clear - Qu; lia)) ltac:(clear - Qu; lia) ltac:(clear; lia) Vu)|].
apply Forall_cons; [exact (chunk_ok_val trasegs Ex _ tb 8 8 _ (ac_h Cx) (hlg_denot_off0 Ex 520 _ E520 ltac:(clear - Qh; lia)) ltac:(clear - Qh; lia) ltac:(clear; lia) Vh)|].
apply Forall_cons; [apply (chunk_ok_val trasegs Ex _ tb 0 8 _ (ac_f Cx) (hlg_denot_off0 Ex 519 _ E519 ltac:(clear - Qf; lia)) ltac:(clear - Qf; lia) ltac:(clear; lia)); rewrite Z.add_0_r; exact Vf|].
apply Forall_nil. }
specialize (HS4 HRK).
match type of HS4 with ?Q -> _ => assert (HQ : Q) end.
{ lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end.
cbn [all_disjoint]. unfold extent_disjoint. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val]. rewrite ?UX305, ?UX54, ?UX67, ?UX2, ?UX10.
repeat split; lazymatch goal with
| |- context [spZ regs] => clear - Htbceil Hrqtb Hsp47; lia
| |- context [F / 8] => clear - Htbzone Hrqtb Htb4096 HFS8 HF8lo; unfold gbox, SB in *; lia
| |- context [F] => clear - HdF_tb; lia
| |- context [r] => clear - HzR_tb; lia
end. }
specialize (HS4 HQ). clear HQ HS3.
norm_ss HS4.
lazymatch type of HS4 with st_ok _ ?Exx ?ssx ?msx =>
let tg := eval red in ss_X38b in
let fa := eval cbn [ss_facts f_atoms] in (f_atoms (ss_facts tg)) in
let cs := eval cbn [ss_facts f_conds] in (f_conds (ss_facts tg)) in
let al := eval cbn [ss_facts f_alias] in (f_alias (ss_facts tg)) in
pose proof (st_ok_facts_incl3 trasegs Exx ssx msx fa cs al HS4 ltac:(ga_incl_lit_tac) ltac:(ga_incl_lit_tac) ltac:(ga_incl_lit_tac)) as HS5 end.
clear HS4. norm_ss HS5.
lazymatch type of HS5 with st_ok _ _ ?ssx _ => first [change ssx with ss_X38b in HS5 | idtac "JOIN-MISMATCH" ssx] end.
rewrite <- restrict_mkst_fx in HS5.
assert (Hfrs2 : frames S2 = (7, fpos) :: frames S) by (rewrite KfrS; exact Hfrs3).
change (Z_to_bv 64 HL_XF) with (Z_to_bv 64 539368).
rga_hand RCX HS5 HJ2 k2; [unfold Ex; rga_E_tac HEE0 | ].
assert (OPT : forall v n, 4096 <= v < 2 ^ 64 -> optb v n = [(v, n)])
by (intros v n Hv; unfold optb; destruct (Z.eqb_spec v 0) as [X | _]; [exfalso; clear - X Hv; lia | reflexivity]).
assert (OB : forall a v n, ew Ex a = Z_to_bv 64 v -> 4096 <= v < 2 ^ 64 ->
In (v, n) ((tb, CHT_SIZE) :: [(ac_f Cx, 4 * Tx); (ac_h Cx, 3 * Tx); (ac_u Cx, Tx); (pv, npv); (xv, nxv)]) ->
rga_optblk B {| c_ly := ly; c_S := S; c_W := W; c_regs := regs; c_mem := mem; c_md := md; c_ch := ch; c_r := r; c_cfp := cfp; c_g := g; c_wfn := wfn;
c_ctx := ctx; c_path := path; c_attr := attr; c_gen := gen; c_loops := loops; c_Wd := Wd; c_Hd := Hd; c_bef := bef;
c_beffmt := beffmt; c_cur := cur; c_s := s; c_N := N; c_img := img; c_fmt := fmt; c_fattr := fattr; c_fgen := fgen;
c_delay := delay; c_rest := rest; c_cid := cid; c_pos := pos; c_fpos := fpos; c_E0 := E0 |} Ex a v n).
{ intros a v n Ea Hv Hin. split; [exact Ea|]. split; [clear - Hv; lia|]. intros _. exact (HpermF v n Hin). }
exists blk, fim, tb, (ac_f Cx), (ac_h Cx), (ac_u Cx), pv, xv, (4 * Tx), (3 * Tx), Tx, npv, nxv.
split; [split; [pose proof (ts_rank_range Tx) as Hrk; rewrite HEVv; clear - Hk2 Hrk; lia | (unfold rga_bud; cbn [c_S]; eapply bud_le_mono; [eapply ajournal_bud; exact HJ2 | ..]; assert (Hr4 : ts_rank Tx <= 4) by (destruct HFx as (_ & HTcx & HTltx & _); fold Tx in HTcx, HTltx; unfold MAX_TABLE_SIZE in HTltx; cbv [ts_chain In] in HTcx; destruct HTcx as [Q|[Q|[Q|[Q|[Q|[Q|[]]]]]]]; rewrite <- Q in *; first [vm_compute; discriminate | exfalso; clear - HTltx; lia]); clear - Hk2 Hr4; rga_lia)]|].
split; [exact Hfmt|].
split; [rewrite !OPT by assumption; cbn [app]; unfold PROT in HPermF; rewrite <- app_assoc in HPermF; exact HPermF|].
split; [split; [rewrite AGx by lia; exact Rblk | split; [exact Tblk | exact Ablk]]|].
split; [split; [rewrite AGx by lia; exact Rfim | split; [exact Tfim | exact Afim]]|].
split; [split; [rewrite AGx by lia; exact Rtb | split; [exact Ttb | exact Atb]]|].
split; [exact (OB 519%nat _ _ E519 Qf ltac:(right; left; reflexivity))|].
split; [exact (OB 520%nat _ _ E520 Qh ltac:(do 2 right; left; reflexivity))|].
split; [exact (OB 521%nat _ _ E521 Qu ltac:(do 3 right; left; reflexivity))|].
split; [exact (OB 522%nat _ _ E522 Qp ltac:(do 4 right; left; reflexivity)) | exact (OB 523%nat _ _ E523 Qx ltac:(do 5 right; left; reflexivity))].
Qed.
End h.
End f.
