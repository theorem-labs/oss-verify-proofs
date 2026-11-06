(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI09 YI08 YI0m YI0n YI0s YCbw.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI5w.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0d YP0c YI0w YI0z YC4a YC8i YC80 YC1f YC1g YC1h YC81 YC4b YC44 YC45 YC44.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YCj2 YC8g YC8a YChd YCjr YCj1 YCj0.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Notation SB := YC81.SB.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
Context {RO : YC8g.ro_below_ofl (@pa_segs _ lib_both3_0_listing PI) (@pa_relro_lo _ lib_both3_0_listing PI) (@pa_relro_hi _ lib_both3_0_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
Ltac eimg_low := rewrite ?Eimg_low by (unfold A_TEXT; lia).
Lemma achain_raise : forall ly rd sp sp' v ch, achain ly rd sp v ch -> sp' + 16 <= v -> achain ly rd sp' v ch.
Proof.
intros ly rd sp sp' v ch [H | (H1 & H2 & H3 & H4 & H5)] Hle; [left; exact H|]. right.
split; [exact Hle|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|].
pose proof (fpchain_fps_increase _ _ _ _ H4) as Hf. eapply Forall_impl; [|exact Hf]. intros r Hr. cbn beta in Hr. lia.
Qed.
Lemma val_mem_frame : forall E rs (m m' : word -> option byte) a n v,
frame_of E rs m m' -> (forall k, 0 <= k < Z.of_nat n -> ~ in_wrange E rs (a + k)) -> 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
val_mem SEGS m a n v -> val_mem SEGS m' a n v.
Proof.
intros E rs m m' a n v HF Hout Ha Han Hv kk Hkk. rewrite <- (Hv kk Hkk). unfold mbyte.
rewrite (HF (Z_to_bv 64 (a + Z.of_nat kk))); [reflexivity|]. rewrite unsigned_lit_small by lia. apply Hout. lia.
Qed.
Lemma mod16_mod8 : forall x, x mod 16 = 0 -> x mod 8 = 0.
Proof.
intros x H. pose proof (Z.div_mod x 16 ltac:(lia)) as D. rewrite H, Z.add_0_r in D. rewrite D.
replace (16 * (x / 16)) with ((2 * (x / 16)) * 8) by lia. apply Z_mod_mult.
Qed.
Lemma st_ok_pin_rege0 : forall E ss ms (r : bv 5) e,
st_ok SEGS E ss ms -> r <> 0%bv -> sv_denot E e = getr (ms_regs ms) r ->
st_ok SEGS E (mkSS (ss_pc ss) (sr_set (ss_regs ss) r e) (ss_mem ss) (ss_resv ss) (ss_facts ss)) ms.
Proof.
intros E ss ms r e HS Hr He.
apply (st_ok_regs SEGS E ss ms (sr_set (ss_regs ss) r e)); [exact HS|].
intros x. destruct (base.decide (x = r)) as [->|Hne].
- rewrite sr_get_set_same; [| destruct (bv_eqb r 0) eqn:Hb; [apply bv_eqb_eq in Hb; congruence | reflexivity]].
rewrite He. exact (st_ok_reg SEGS E ss ms r HS).
- rewrite sr_get_set_other by exact Hne. reflexivity.
Qed.
Lemma st_ok_pin_rege : forall E ss ms (r : bv 5) e,
st_ok_pi SEGS VAL E ss ms -> r <> 0%bv -> sv_denot E e = getr (ms_regs ms) r ->
st_ok_pi SEGS VAL E (mkSS (ss_pc ss) (sr_set (ss_regs ss) r e) (ss_mem ss) (ss_resv ss) (ss_facts ss)) ms.
Proof.
intros E ss ms r e HS Hr He. destruct ss as [pc0 sr0 fr0 sm0 rv0 fs0]. exact (st_ok_pin_rege0 E _ ms r e HS Hr He).
Qed.
Lemma denot_add_and32 : forall E nb ni b i, ew E nb = Z_to_bv 64 b -> ew E ni = Z_to_bv 64 i ->
0 <= b -> 0 <= i < 2 ^ 32 -> b + i < 2 ^ 64 ->
sv_denot E (SAlu ALU_ADD (SOff nb 0) (SAlu ALU_AND (SOff ni 0) (SLit 4294967295))) = Z_to_bv 64 (b + i).
Proof.
intros E nb ni b i Hb Hi Rb Ri Hbi. rewrite denot_lit_U. f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E nb b Hb), (U_atom E ni i Hi), U_SLit by lia.
change (zcanon 4294967295) with (Z.ones 32). rewrite Z.land_ones by lia. rewrite (Z.mod_small i) by lia.
rewrite (zcanon_id i) by (rewrite M64_val; lia). apply zcanon_id. rewrite M64_val. lia.
Qed.
Lemma U_zext32 : forall E a, U E (SAlu ALU_SRL (SAlu ALU_SLL a (SLit 32)) (SLit 32)) = U E a mod 2 ^ 32.
Proof.
intros E a. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SLit.
rewrite (zcanon_id 32) by (rewrite M64_val; lia). change (Z.land 32 63) with 32.
pose proof (U_range E a) as Hr. rewrite M64_val in Hr.
rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
unfold zcanon. rewrite M64_val. change (2 ^ 64) with (2 ^ 32 * 2 ^ 32).
rewrite Z.mul_mod_distr_r by lia. rewrite Z.div_mul by lia.
apply Z.mod_small. pose proof (Z.mod_pos_bound (U E a) (2 ^ 32) ltac:(lia)). lia.
Qed.
Lemma U_add_atom_zext32 : forall E nb a b, ew E nb = Z_to_bv 64 b -> 0 <= b -> b + 2 ^ 32 <= 2 ^ 64 ->
U E (SAlu ALU_ADD (SOff nb 0) (SAlu ALU_SRL (SAlu ALU_SLL a (SLit 32)) (SLit 32))) = b + U E a mod 2 ^ 32.
Proof.
intros E nb a b Hb Rb Hhi. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_zext32, (U_atom E nb b Hb) by lia.
pose proof (Z.mod_pos_bound (U E a) (2 ^ 32) ltac:(lia)). apply zcanon_id. rewrite M64_val. lia.
Qed.
Lemma denot_add_zext32 : forall E nb ni b i, ew E nb = Z_to_bv 64 b -> ew E ni = Z_to_bv 64 i ->
0 <= b -> 0 <= i < 2 ^ 32 -> b + 2 ^ 32 <= 2 ^ 64 ->
sv_denot E (SAlu ALU_ADD (SOff nb 0) (SAlu ALU_SRL (SAlu ALU_SLL (SOff ni 0) (SLit 32)) (SLit 32))) = Z_to_bv 64 (b + i).
Proof.
intros E nb ni b i Hb Hi Rb Ri Hbi. rewrite denot_lit_U. f_equal.
rewrite (U_add_atom_zext32 E nb (SOff ni 0) b Hb Rb Hbi), (U_atom E ni i Hi) by lia. rewrite (Z.mod_small i) by lia. reflexivity.
Qed.
Lemma U_add_atoms2 : forall E n1 n2 a b, ew E n1 = Z_to_bv 64 a -> ew E n2 = Z_to_bv 64 b -> 0 <= a -> 0 <= b -> a + b < 2 ^ 64 ->
U E (SAlu ALU_ADD (SOff n1 0) (SOff n2 0)) = a + b.
Proof.
intros E n1 n2 a b H1 H2 Ha Hb Hab. rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E n1 a H1), (U_atom E n2 b H2) by lia. apply zcanon_id. rewrite M64_val. lia.
Qed.
Section TL.
Variable B : asyms.
Hypothesis TL : PALib B.
Hypothesis LAWS : AR_laws SEGS B.
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL. Let errno_low := pal_env B TL. Let HBfree := pal_free B TL. Let HBmalloc := pal_malloc B TL.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_both3_0) (PI := PI).
Let PBASE := @pa_B_ok _ _ PI. Let PBLO := @pa_base_lo _ _ PL_both3_0 PI.
Let RUNP := SRr_run_pi_AJ B LAWS. Let RUNTOP := SRr_run_to_pi_AJ B LAWS. Let RUNC := SRr_run_pi_AJ_call B LAWS.
Hypothesis TCMP : tcmp_spec B.
Lemma shent_ok_sub : forall ly S W mem md E Bx (m : nat) x p n lo hi,
AR SEGS B ly S W mem md -> In (p, n) (ablocks B ly S) ->
U E Bx = SHADOW_OFF -> U E (SOff m 0) = x -> p <= x + lo -> x + hi <= p + req_size n -> lo <= hi ->
shent_ok SEGS Bx E (mrestrict (w_H W) mem) (mkSHE m lo hi).
Proof.
intros ly S W mem md E Bx m x p n lo hi HAR Hin HB Hm Hlo Hhi Hlh.
unfold shent_ok, app_apart. cbn [she_m she_lo she_hi]. rewrite HB, Hm. rewrite <- (aview_rd_of SEGS). split.
- destruct (Z_lt_le_dec lo hi); [|apply range_addressable_nil; lia].
apply (range_addressable_of_block SEGS B LAWS ly S W mem md p n (x + lo) (hi - lo) HAR Hin); lia.
-
destruct (al_blocks _ _ LAWS ly S W mem md p n HAR Hin) as (_ & _ & _ & Happ & _).
rewrite Z.min_l, Z.max_r by lia.
intros a Ha. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia.
Qed.
Lemma acall_kept_trans : forall lyc Sc W m0 m1 m2 slo shi (Er : Z -> Prop),
acall_kept SEGS B lyc Sc W m0 W m1 slo shi Er -> acall_kept SEGS B lyc Sc W m1 W m2 slo shi Er ->
acall_kept SEGS B lyc Sc W m0 W m2 slo shi Er.
Proof.
intros lyc Sc W m0 m1 m2 slo shi Er (A1 & A2 & A3 & A4 & A5 & A6) (K1 & K2 & K3 & K4 & K5 & K6).
split; [intros a Ha Hs; rewrite (K1 a Ha Hs); exact (A1 a Ha Hs)|].
split; [intros b m i Hb Hi Hn; rewrite (K2 b m i Hb Hi Hn); exact (A2 b m i Hb Hi Hn)|].
split; [intros a H1 H2 H3; rewrite (K3 a H1 H2 H3); exact (A3 a H1 H2 H3)|].
split; [intros cid pos a Hf Hz Hn; rewrite (K4 cid pos a Hf Hz Hn); exact (A4 cid pos a Hf Hz Hn)|].
split; [intros a Ha Hs Hp; exact (K5 a Ha Hs (A5 a Ha Hs Hp)) | exact K6].
Qed.
Lemma acall_kept_band : forall lyc Sc W m0 m1 slo shi slo' shi' (Er : Z -> Prop),
acall_kept SEGS B lyc Sc W m0 W m1 slo shi Er -> slo' <= slo -> shi <= shi' ->
(forall a, slo' <= a < shi' -> apresent (w_H W) m1 a) ->
acall_kept SEGS B lyc Sc W m0 W m1 slo' shi' Er.
Proof.
intros lyc Sc W m0 m1 slo shi slo' shi' Er (K1 & K2 & K3 & K4 & K5 & K6) H1 H2 Hp.
split; [intros a Ha Hs; apply K1; [exact Ha | lia]|]. split; [exact K2|]. split; [exact K3|]. split; [exact K4|].
split; [intros a Ha Hs Hq; apply K5; [exact Ha | lia | exact Hq] | exact Hp].
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma acall_kept_of_run : forall E rs lyc Sc W (m m' : word -> option byte) md slo shi (Er : Z -> Prop),
AR SEGS B lyc Sc W m md ->
frame_of E rs (mrestrict (w_H W) m) (mrestrict (w_H W) m') ->
mem_grows (mrestrict (w_H W) m) (mrestrict (w_H W) m') ->
(forall a, in_wrange E rs a -> Er a \/ (slo <= a < shi)) ->
(forall a, Er a -> a < alloc_ceiling /\ off_img a 1) -> alloc_ceiling <= slo ->
(forall a, slo <= a < shi -> apresent (w_H W) m a) ->
acall_kept SEGS B lyc Sc W m W m' slo shi Er.
Proof.
intros E rs lyc Sc W m m' md slo shi Er HAR HFr HG Hwr HEr Hslo Hband.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (KO : forall a, 0 <= a < 2 ^ 64 -> ~ Er a -> ~ (slo <= a < shi) -> aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a).
{ intros a Ha He Hs. apply (aview_kept_out E rs _ m m' HFr a Ha). intros Hw. destruct (Hwr a Hw) as [X | X]; [exact (He X) | exact (Hs X)]. }
split.
{ intros a Ha Hs. apply KO; [lia | intros He; pose proof (HEr a He) as [He1 _]; lia | exact Hs]. }
split.
{ intros b n i Hb Hi Hn. destruct (al_blocks _ _ LAWS _ _ _ _ _ b n HAR Hb) as (_ & Hb4096 & Hbceil & _).
apply KO; [lia | exact Hn | lia]. }
split.
{ intros a Him _ _. pose proof (pa_segs_low a Him) as Hl. pose proof (pa_img_range a Him) as Hl2. apply KO; [unfold kLowMemEnd in Hl; lia | intros He; pose proof (HEr a He) as [_ He2]; unfold off_img in He2; clear - He2 Hl2; lia | unfold kLowMemEnd in Hl; ceil; lia]. }
split.
{ intros cid pos a Hf Hz Hn. destruct (frames_bounds SEGS B LAWS _ _ _ _ _ cid pos HAR Hf) as (Hf4096 & Hfceil & Hfhigh).
pose proof (fs_frame_bytes_nonneg cid) as Hnn.
destruct Hz as [Hz | Hz]; unfold in_zr, frame_rng in Hz; cbn [fst snd] in Hz.
- apply KO; [lia | exact Hn | lia].
- unfold shadow_addr, SHADOW_OFF in Hz. idtac.
apply KO; [clear - Hz Hfceil Hfhigh Hnn; ceil; zone_lia | exact Hn | clear - Hz Hfceil Hfhigh Hnn Hslo; ceil; zone_lia]. }
split.
{ intros a Ha Hs Hp. eapply apresent_grows; [exact HG | exact Hp]. }
intros a Ha. eapply apresent_grows; [exact HG | apply Hband; exact Ha].
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Lemma aj_call_sp : forall W (regsc : bvmap 5 word) memc pc STK sp0 FP ly S W0 mem md own lyc Sc mdc k STK1 FP1 EV1 (o : Z) raw ch1
(K : alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k ->
spZ regsc = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 0 <= STK1 -> STK1 - o <= STK ->
getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
getr regsc 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
achain lyc (aview SEGS (w_H W) memc) (sp0 + o) (s0Z regsc) ch1 ->
(afn_pre SEGS B STK1 lyc Sc W regsc memc mdc ch1 ->
SRr SEGS W (mkCfg (mkst regsc pc memc (seg_rom SEGS)) mdc)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
ajournal SEGS B STK1 (spZ regsc) FP1 lyc Sc W memc mdc [] ly2 S2 W2 mem2 md2 EV1 /\
aregs_preserved regsc regs2 /\ K ly2 S2 W2 regs2 mem2 md2)) ->
(forall a, inFP FP1 a -> (inFP FP a /\ exists b n, In (b, n) (ablocks B lyc Sc) /\ b <= a < b + req_size n) \/
in_tmp_block (ablocks B ly S) (ablocks B lyc Sc) a) ->
SRr SEGS W (mkCfg (mkst regsc pc memc (seg_rom SEGS)) mdc)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
ajournal SEGS B STK sp0 FP ly S W0 mem md own ly2 S2 W2 mem2 md2 (k + EV1) /\
ajournal SEGS B STK1 (sp0 + o) FP1 lyc Sc W memc mdc [] ly2 S2 W2 mem2 md2 EV1 /\
aregs_preserved regsc regs2 /\ K ly2 S2 W2 regs2 mem2 md2).
Proof.
intros W regsc memc pc STK sp0 FP ly S W0 mem md own lyc Sc mdc k STK1 FP1 EV1 o raw ch1 K
HJ Hsp' Hal Hneg Hstk1 Hbud Hgp Htp Hra Hraw Hra4 Hch Hcallee HF.
eapply SRr_mono.
{ apply Hcallee. eapply (afn_pre_at SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k regsc STK1 o ch1);
try eassumption. - rewrite Hra. exact Hraw. - unfold raZ. rewrite Hra. exact Hra4. - rewrite Hsp'. exact Hch. }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ1 & HP & HK).
exists ly2, S2, regs2, mem2, md2. split; [reflexivity|]. rewrite Hsp' in HJ1.
split; [| split; [exact HJ1 | split; [exact HP | exact HK]]].
change own with ([] ++ own). eapply (ajournal_sub SEGS B LAWS pa_segs_low); [exact HJ | exact HJ1 | lia | lia | exact HF].
Qed.
Definition TIN_CLOB : list (bv 5) := [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 20; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Definition TIN_KEPT19 : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 21; 22; 23]%bv.
Definition TIN_KEPT : list (bv 5) := [2; 3; 4; 8; 9; 18; 21; 22; 23]%bv.
Lemma tin_clob_cases : forall r : bv 5, reg_in r TIN_CLOB = false -> r = 0%bv \/ In r TIN_KEPT19.
Proof.
intros r Hr. pose proof (all_regs_in r) as Hin. cbv [all_regs In] in Hin.
repeat (destruct Hin as [<-|Hin]; [first [left; reflexivity | vm_compute in Hr; discriminate | right; cbv; tauto] |]). destruct Hin.
Qed.
Lemma tin_clob_cases3 : forall r : bv 5, reg_in r TIN_CLOB = false -> r = 0%bv \/ r = 19%bv \/ In r TIN_KEPT.
Proof.
intros r Hr. pose proof (all_regs_in r) as Hin. cbv [all_regs In] in Hin.
repeat (destruct Hin as [<-|Hin]; [first [left; reflexivity | right; left; reflexivity | vm_compute in Hr; discriminate | right; right; cbv; tauto] |]). destruct Hin.
Qed.
Definition tin_regs := sr_set sr_atoms 19%bv (SLit 1).
Definition tin_loc : YP09.region :=
YP09.mkRegion (Some 9%nat) 184 224 184 184
[YP09.mkChunk 184 (CVal 8 (SOff 32 0)); YP09.mkChunk 192 (CVal 8 (SOff 17 0)); YP09.mkChunk 200 (CVal 8 (SOff 15 0));
YP09.mkChunk 208 (CVal 8 (SOff 16 0)); YP09.mkChunk 216 (CVal 8 (SOff 29 0))].
Definition tin_facts : facts :=
mkFacts [ (9%nat, mkAF 70368744177664 140737488355328 4); (29%nat, mkAF SB SB 0); (21%nat, HPTR 0); (20%nat, mkAF 1 65535 0);
(24%nat, mkAF 0 4294967295 0); (26%nat, mkAF 0 4294967295 0); (18%nat, HPTR 0); (15%nat, HPTR 4); (16%nat, HPTR 3); (17%nat, HPTR 3) ] [] [].
Definition ss_tin : sstate := mkSS 0x287c tin_regs [tin_loc] None tin_facts.
Definition ttl_facts : facts := mkFacts [ (20%nat, mkAF 1 65535 0); (24%nat, mkAF 0 4294967295 0); (26%nat, mkAF 0 4294967295 0) ] [] [].
Definition ss_ttl : sstate := mkSS 0x290c sr_atoms [] None ttl_facts.
Lemma val_mem_byte1 : forall (H : word -> bool) (m : word -> option byte) a,
apresent H m a -> exists v, 0 <= v < 256 /\ val_mem SEGS (mrestrict H m) a 1 v.
Proof.
intros H m a [Hh [b Hb]]. exists (bv_unsigned b). pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. cbn [Z.of_N] in R. change (2 ^ 8) with 256 in R.
split; [lia|]. intros k Hk. destruct k; [|lia]. cbn [Z.of_nat]. rewrite Z.add_0_r. unfold mbyte, mrestrict. rewrite Hh. cbn. rewrite Hb. f_equal.
unfold YO0f.le_byte. change (8 * Z.of_nat 0) with 0. change (2 ^ (8 * Z.of_nat 1)) with 256.
rewrite Z.shiftr_0_r. rewrite (Z.mod_small (bv_unsigned b) 256) by lia. rewrite (Z.mod_small (bv_unsigned b) 256) by lia.
symmetry. apply Z_to_bv_bv_unsigned.
Qed.
Lemma obj_at_keptK : forall lyc Sc W (m m' : word -> option byte) slo shi (Er : Z -> Prop) b sz lay vals,
acall_kept SEGS B lyc Sc W m W m' slo shi Er -> In (b, sz) (ablocks B lyc Sc) ->
lay_inside lay (req_size sz) = true -> (forall i, 0 <= i < req_size sz -> ~ Er (b + i)) ->
obj_at SEGS (mrestrict (w_H W) m) b lay vals -> obj_at SEGS (mrestrict (w_H W) m') b lay vals.
Proof.
intros lyc Sc W m m' slo shi Er b sz lay vals (_ & K2 & _) Hin Hlay HnE Hobj.
eapply (obj_at_transport_range SEGS); [exact Hobj | exact Hlay |]. intros i Hi. apply (mbyte_of_aview SEGS). exact (K2 b sz i Hin Hi (HnE i Hi)).
Qed.
Lemma val_mem_keptK : forall lyc Sc W (m m' : word -> option byte) slo shi (Er : Z -> Prop) a n v,
acall_kept SEGS B lyc Sc W m W m' slo shi Er -> alloc_ceiling <= a -> a + Z.of_nat n <= 2 ^ 64 -> (shi <= a \/ a + Z.of_nat n <= slo) ->
val_mem SEGS (mrestrict (w_H W) m) a n v -> val_mem SEGS (mrestrict (w_H W) m') a n v.
Proof.
intros lyc Sc W m m' slo shi Er a n v (K1 & _) Ha Han Hs Hv kk Hkk. rewrite <- (Hv kk Hkk). apply (mbyte_of_aview SEGS). apply K1; lia.
Qed.
Lemma achain_keptK : forall lyc Sc W (m m' : word -> option byte) slo shi (Er : Z -> Prop) sp v ch,
acall_kept SEGS B lyc Sc W m W m' slo shi Er -> achain lyc (aview SEGS (w_H W) m) sp v ch ->
shi <= sp -> alloc_ceiling <= sp -> ly_top lyc <= 2 ^ 64 -> achain lyc (aview SEGS (w_H W) m') sp v ch.
Proof.
intros lyc Sc W m m' slo shi Er sp v ch (K1 & _) Hch Hshi Hsp Htop.
eapply (achain_kept lyc _ _ sp v ch sp); [exact Hch | lia | exact Htop | intros a Ha; apply K1; lia].
Qed.
Lemma achain_keptK2 : forall lyc Sc W (m m' : word -> option byte) slo shi (Er : Z -> Prop) sp v ch,
acall_kept SEGS B lyc Sc W m W m' slo shi Er -> achain lyc (aview SEGS (w_H W) m) sp v ch ->
sp <= shi -> shi + 16 <= v -> alloc_ceiling <= shi -> ly_top lyc <= 2 ^ 64 -> achain lyc (aview SEGS (w_H W) m') sp v ch.
Proof.
intros lyc Sc W m m' slo shi Er sp v ch (K1 & _) Hch H1 H2 H3 Htop.
apply (achain_lower _ _ shi sp); [|lia].
eapply (achain_kept lyc _ _ shi v ch shi); [apply (achain_raise _ _ sp shi); [exact Hch | lia] | lia | exact Htop | intros a Ha; apply K1; lia].
Qed.
Lemma region_kept_sub_ajw : forall E lyc Sc W memc W2 mem2 slo shi (Er : Z -> Prop) n lo hi wlo whi cs x b m ly2 S2 md2,
acall_kept SEGS B lyc Sc W memc W2 mem2 slo shi Er -> AR SEGS B ly2 S2 W2 mem2 md2 -> In (b, m) (ablocks B ly2 S2) ->
bv_unsigned (ew E n) = x -> In (b, m) (ablocks B lyc Sc) -> b <= x + lo -> x + hi <= b + req_size m -> lo <= wlo -> whi <= hi ->
(forall a, x + lo <= a < x + hi -> ~ Er a) ->
region_kept SEGS E (mrestrict (w_H W) memc) (mrestrict (w_H W2) mem2) (YP09.mkRegion (Some n) lo hi wlo whi cs).
Proof.
intros E lyc Sc W memc W2 mem2 slo shi Er n lo hi wlo whi cs x b m ly2 S2 md2 (_ & K2 & _) HAR2 Hin2 Hn Hin Hlo Hhi Hwlo Hwhi HnE.
destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR2 Hin2) as (_ & _ & _ & _ & Hpres2 & _).
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Hn; intros a Ha.
- apply (mbyte_of_aview SEGS). replace a with (b + (a - b)) by lia. apply (K2 b m (a - b) Hin); [lia|].
replace (b + (a - b)) with a by lia. apply HnE. exact Ha.
- intros _. apply (apresent_writable SEGS). apply (proj1 (Hpres2 a ltac:(lia))).
Qed.
Ltac env_agree32 HAE :=
lazymatch goal with
| |- env_agree 32 _ (ewset ?X ?n ?v) => apply (env_agree_trans 32 _ X); [env_agree32 HAE | apply (YP03.env_agree_le 32 n); [lia | apply env_agree_ewset]]
| |- env_agree 32 _ (havoc ?X ?n ?ws) => apply (env_agree_trans 32 _ X); [env_agree32 HAE | apply (YP03.env_agree_le 32 n); [lia | apply env_agree_havoc]]
| |- _ => exact HAE
end.
Definition tin_post (W : world SEGS) (regs : bvmap 5 word) (memc : word -> option byte) (sp0 sp1 : Z) (FP : list (Z * Z))
(ly : alayout) (S : astate) (W0 : world SEGS) (mem0 : word -> option byte) (md0 : Model)
(lyc : alayout) (Sc : astate) (k : Z) (fpos pt npt g cfp bfp : Z) : world SEGS -> config -> Prop :=
fun W' c' => W' = W /\ exists regs' mem' md',
c' = mkCfg (mkst regs' (Z_to_bv 64 (BASE + 0x2944)) mem' (seg_rom SEGS)) md' /\
ajournal SEGS B TFLUSH_STK sp0 FP ly S W0 mem0 md0 [(1, fpos)] lyc Sc W mem' md' k /\
(forall r : bv 5, reg_in r TIN_CLOB = false -> getr regs' r = getr regs r) /\
getr regs' 29 = Z_to_bv 64 SB /\ getr regs' 15 = Z_to_bv 64 g /\ getr regs' 16 = Z_to_bv 64 cfp /\ getr regs' 17 = Z_to_bv 64 bfp /\
acall_kept SEGS B lyc Sc W memc W mem' (sp1 - TCMP_STK) sp1 (fun a => pt <= a < pt + npt).
Definition tin_ctx (W : world SEGS) (regs : bvmap 5 word) (memc : word -> option byte) (mdc : Model) (sp0 sp1 : Z) (FP : list (Z * Z))
(ly : alayout) (S : astate) (W0 : world SEGS) (mem0 : word -> option byte) (md0 : Model) (lyc : alayout) (Sc : astate) (k : Z) (fpos : Z)
(ch1 : list (Z * Z * Z)) (pt npt bimg Nb g cfp bfp tidx : Z) (gvals cvals bvals : list Z) (gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx : Z) : Prop :=
ajournal SEGS B TFLUSH_STK sp0 FP ly S W0 mem0 md0 [(1, fpos)] lyc Sc W memc mdc k /\
In (pt, npt) (ablocks B lyc Sc) /\
(forall blc lyq ownq a, In (pt, npt) blc -> pt <= a < pt + npt -> awr_byte TFLUSH_STK sp0 FP (ablocks B ly S) blc lyq ownq a) /\
In (bimg, Nb) (ablocks B lyc Sc) /\ Nb < 2 ^ 32 /\ (pt + req_size npt <= bimg \/ bimg + req_size Nb <= pt) /\
In (g, CGIF_SIZE) (ablocks B lyc Sc) /\ In (cfp, FRAME_SIZE) (ablocks B lyc Sc) /\ In (bfp, FRAME_SIZE) (ablocks B lyc Sc) /\ cfp <> bfp /\
(pt + req_size npt <= g \/ g + 96 <= pt) /\ (pt + req_size npt <= cfp \/ cfp + 40 <= pt) /\ (pt + req_size npt <= bfp \/ bfp + 40 <= pt) /\
obj_at SEGS (mrestrict (w_H W) memc) g LAY_CGIF gvals /\ nth_error gvals CG_pal = Some gpal /\ nth_error gvals CG_ngp = Some ngp /\
obj_at SEGS (mrestrict (w_H W) memc) cfp LAY_Frame cvals /\ nth_error cvals FR_lpal = Some cpal /\ nth_error cvals FR_attr = Some cattr /\
nth_error cvals FR_nlp = Some cnlp /\ nth_error cvals FR_ctidx = Some ctidx /\
obj_at SEGS (mrestrict (w_H W) memc) bfp LAY_Frame bvals /\ nth_error bvals FR_lpal = Some bpal /\ nth_error bvals FR_attr = Some battr /\
nth_error bvals FR_nlp = Some bnlp /\ nth_error bvals FR_ctidx = Some btidx /\
(Z.land cattr 1 <> 0 -> exists Nl, In (cpal, Nl) (ablocks B lyc Sc) /\ 3 * cnlp <= Nl) /\
(Z.land battr 1 <> 0 -> exists Nl, In (bpal, Nl) (ablocks B lyc Sc) /\ 3 * bnlp <= Nl) /\
(Z.land cattr 1 = 0 \/ Z.land battr 1 = 0 -> exists Np, In (gpal, Np) (ablocks B lyc Sc) /\ 3 * ngp <= Np) /\
spZ regs = sp1 /\ sp0 - 368 <= sp1 <= sp0 - 352 /\ sp1 mod 16 = 0 /\
getr regs 9 = Z_to_bv 64 sp1 /\ getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\
achain lyc (aview SEGS (w_H W) memc) sp1 (s0Z regs) ch1 /\ s0Z regs = sp0 /\
val_mem SEGS (mrestrict (w_H W) memc) (sp1 + 184) 8 tidx /\ 0 <= tidx < 2 ^ 64 /\
val_mem SEGS (mrestrict (w_H W) memc) (sp1 + 216) 8 SB /\
val_mem SEGS (mrestrict (w_H W) memc) (sp1 + 192) 8 bfp /\
val_mem SEGS (mrestrict (w_H W) memc) (sp1 + 200) 8 g /\
val_mem SEGS (mrestrict (w_H W) memc) (sp1 + 208) 8 cfp /\
npt < 2 ^ 32 /\
getr regs 18 = Z_to_bv 64 bimg /\ getr regs 19 = Z_to_bv 64 1 /\ getr regs 21 = Z_to_bv 64 pt.
Ltac tin_ctx_names H :=
destruct H as (HJ & Hpt & Hpawr & Hbi & HNb & HsepI & Hg & Hcf & Hbf & Hcb & HsepG & HsepC & HsepB
& Og & Ogpal & Ongp & Oc & Ocpal & Ocattr & Ocnlp & Octidx & Ob & Obpal & Obattr & Obnlp & Obtidx & HLc & HLb & HGp
& Hsp & Hsp1 & Hsp1al & H9 & Hgp & Htp & Hch & Hs0 & Vtidx & Rtidx & Vsb & Vbfp & Vg & Vcfp & Hnpt32 & H18 & H19 & H21).
Definition tin_stmt (m : nat) : Prop :=
forall (c : Z) W (regs : bvmap 5 word) memc mdc sp0 sp1 FP ly S W0 mem0 md0 lyc Sc k fpos ch1
(pt npt ti bimg Nb idx g cfp bfp tidx : Z) (gvals cvals bvals : list Z) (gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx : Z),
c <= Z.of_nat m -> 1 <= c <= 65535 ->
tin_ctx W regs memc mdc sp0 sp1 FP ly S W0 mem0 md0 lyc Sc k fpos ch1 pt npt bimg Nb g cfp bfp tidx gvals cvals bvals gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx ->
0 <= ti -> ti + c <= npt -> 0 <= idx -> idx + c <= Nb ->
getr regs 29 = Z_to_bv 64 SB -> getr regs 15 = Z_to_bv 64 g -> getr regs 16 = Z_to_bv 64 cfp -> getr regs 17 = Z_to_bv 64 bfp ->
getr regs 26 = Z_to_bv 64 ti -> getr regs 20 = Z_to_bv 64 c -> getr regs 24 = Z_to_bv 64 idx ->
SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + 0x287c)) memc (seg_rom SEGS)) mdc)
(tin_post W regs memc sp0 sp1 FP ly S W0 mem0 md0 lyc Sc k fpos pt npt g cfp bfp).
Ltac tin_prelude HJ :=
pose proof pa_wx as Hwx; pose proof pa_segs_low as Hsegs;
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5);
pose proof (proj1 HJ) as HAR;
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSpres & Hstk & _);
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2);
assert (FFS : TFLUSH_STK = 17440) by reflexivity; assert (WS : TCMP_STK = 4112) by reflexivity; assert (Hes : ESTACK = 4096) by reflexivity.
Definition TCTX_REGS : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 21]%bv.
Ltac tctx_regs_of HK := let r := fresh "r" in let Hr := fresh "Hr" in
intros r Hr; apply HK; cbv [TCTX_REGS In] in Hr; repeat (destruct Hr as [<- | Hr]; [reflexivity|]); destruct Hr.
Lemma tin_ctx_kept : forall W (regs regsN : bvmap 5 word) memc mdc memN mdN sp0 sp1 FP ly S W0 mem0 md0 lyc Sc k fpos ch1
pt npt bimg Nb g cfp bfp tidx gvals cvals bvals gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx slo shi,
tin_ctx W regs memc mdc sp0 sp1 FP ly S W0 mem0 md0 lyc Sc k fpos ch1 pt npt bimg Nb g cfp bfp tidx gvals cvals bvals gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx ->
ajournal SEGS B TFLUSH_STK sp0 FP ly S W0 mem0 md0 [(1, fpos)] lyc Sc W memN mdN k ->
acall_kept SEGS B lyc Sc W memc W memN slo shi (fun a => pt <= a < pt + npt) -> sp1 <= shi <= sp1 + 184 ->
(forall r : bv 5, In r TCTX_REGS -> getr regsN r = getr regs r) ->
tin_ctx W regsN memN mdN sp0 sp1 FP ly S W0 mem0 md0 lyc Sc k fpos ch1 pt npt bimg Nb g cfp bfp tidx gvals cvals bvals gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx.
Proof.
intros W regs regsN memc mdc memN mdN sp0 sp1 FP ly S W0 mem0 md0 lyc Sc k fpos ch1
pt npt bimg Nb g cfp bfp tidx gvals cvals bvals gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx slo shi HCTX HJN K Hband HK.
tin_ctx_names HCTX. tin_prelude HJ.
destruct (al_blocks _ _ LAWS lyc Sc W memc mdc pt npt HAR Hpt) as (Hq16 & Hq4096 & Hqceil & Hqh_ia & _ & _ & Hnpt & _). pose proof (proj1 Hqh_ia) as Hqh.
pose proof (blk_off_imgP _ _ _ _ _ _ pt npt HAR Hpt) as Hqh_img.
pose proof (req_size_pos' npt ltac:(lia)) as [_ Hrnp].
pose proof (proj1 (proj2 HJN)) as HLY. destruct HLY as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
assert (QS : forall r : bv 5, In r TCTX_REGS -> forall v, getr regs r = v -> getr regsN r = v) by (intros r Hr v Hv; rewrite (HK r Hr); exact Hv).
split; [exact HJN|]. split; [exact Hpt|]. split; [exact Hpawr|]. split; [exact Hbi|]. split; [exact HNb|]. split; [exact HsepI|].
split; [exact Hg|]. split; [exact Hcf|]. split; [exact Hbf|]. split; [exact Hcb|]. split; [exact HsepG|]. split; [exact HsepC|]. split; [exact HsepB|].
split; [eapply (obj_at_keptK _ _ _ _ _ _ _ _ g CGIF_SIZE); [exact K | exact Hg | vm_compute; reflexivity | change (req_size CGIF_SIZE) with 96; intros i Hi Hn; lia | exact Og]|].
split; [exact Ogpal|]. split; [exact Ongp|].
split; [eapply (obj_at_keptK _ _ _ _ _ _ _ _ cfp FRAME_SIZE); [exact K | exact Hcf | vm_compute; reflexivity | change (req_size FRAME_SIZE) with 40; intros i Hi Hn; lia | exact Oc]|].
split; [exact Ocpal|]. split; [exact Ocattr|]. split; [exact Ocnlp|]. split; [exact Octidx|].
split; [eapply (obj_at_keptK _ _ _ _ _ _ _ _ bfp FRAME_SIZE); [exact K | exact Hbf | vm_compute; reflexivity | change (req_size FRAME_SIZE) with 40; intros i Hi Hn; lia | exact Ob]|].
split; [exact Obpal|]. split; [exact Obattr|]. split; [exact Obnlp|]. split; [exact Obtidx|].
split; [exact HLc|]. split; [exact HLb|]. split; [exact HGp|].
split; [unfold spZ; rewrite (HK 2%bv ltac:(cbv; tauto)); exact Hsp|]. split; [exact Hsp1|]. split; [exact Hsp1al|].
split; [exact (QS 9%bv ltac:(cbv; tauto) _ H9)|]. split; [exact (QS 3%bv ltac:(cbv; tauto) _ Hgp)|]. split; [exact (QS 4%bv ltac:(cbv; tauto) _ Htp)|].
split; [unfold s0Z; rewrite (HK 8%bv ltac:(cbv; tauto)); eapply achain_keptK2; [exact K | exact Hch | lia | unfold s0Z in Hs0; rewrite Hs0; lia | idtac; lia | lia]|].
split; [unfold s0Z; rewrite (HK 8%bv ltac:(cbv; tauto)); exact Hs0|].
split; [eapply val_mem_keptK; [exact K | lia | cbn [Z.of_nat]; lia | left; lia | exact Vtidx]|]. split; [exact Rtidx|].
split; [eapply val_mem_keptK; [exact K | lia | cbn [Z.of_nat]; lia | left; lia | exact Vsb]|].
split; [eapply val_mem_keptK; [exact K | lia | cbn [Z.of_nat]; lia | left; lia | exact Vbfp]|].
split; [eapply val_mem_keptK; [exact K | lia | cbn [Z.of_nat]; lia | left; lia | exact Vg]|].
split; [eapply val_mem_keptK; [exact K | lia | cbn [Z.of_nat]; lia | left; lia | exact Vcfp]|].
split; [exact Hnpt32|].
split; [exact (QS 18%bv ltac:(cbv; tauto) _ H18)|]. split; [exact (QS 19%bv ltac:(cbv; tauto) _ H19) | exact (QS 21%bv ltac:(cbv; tauto) _ H21)].
Qed.
Lemma fl_tin_tail : forall m, tin_stmt m ->
forall (c : Z) W (regs regsN : bvmap 5 word) memc mdc memN mdN sp0 sp1 FP ly S W0 mem0 md0 lyc Sc k fpos ch1
(pt npt ti bimg Nb idx g cfp bfp tidx : Z) (gvals cvals bvals : list Z) (gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx : Z),
c - 1 <= Z.of_nat m -> 1 <= c <= 65535 ->
tin_ctx W regs memc mdc sp0 sp1 FP ly S W0 mem0 md0 lyc Sc k fpos ch1 pt npt bimg Nb g cfp bfp tidx gvals cvals bvals gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx ->
0 <= ti -> ti + c <= npt -> 0 <= idx -> idx + c <= Nb ->
ajournal SEGS B TFLUSH_STK sp0 FP ly S W0 mem0 md0 [(1, fpos)] lyc Sc W memN mdN k ->
acall_kept SEGS B lyc Sc W memc W memN (sp1 - TCMP_STK) sp1 (fun a => pt <= a < pt + npt) ->
(forall r : bv 5, reg_in r TIN_CLOB = false -> getr regsN r = getr regs r) ->
getr regsN 29 = Z_to_bv 64 SB -> getr regsN 15 = Z_to_bv 64 g -> getr regsN 16 = Z_to_bv 64 cfp -> getr regsN 17 = Z_to_bv 64 bfp ->
getr regsN 26 = Z_to_bv 64 ti -> getr regsN 20 = Z_to_bv 64 c -> getr regsN 24 = Z_to_bv 64 idx ->
SRr SEGS W (mkCfg (mkst regsN (Z_to_bv 64 (BASE + 0x290c)) memN (seg_rom SEGS)) mdN)
(tin_post W regs memc sp0 sp1 FP ly S W0 mem0 md0 lyc Sc k fpos pt npt g cfp bfp).
Proof.
intros m IH c W regs regsN memc mdc memN mdN sp0 sp1 FP ly S W0 mem0 md0 lyc Sc k fpos ch1
pt npt ti bimg Nb idx g cfp bfp tidx gvals cvals bvals gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx
Hm Hcnt HCTX Hti1 Hti2 Hidx1 Hidx2 HJN K HK N29 N15 N16 N17 N26 N20 N24.
pose proof HCTX as HCTX0. tin_ctx_names HCTX.
tin_prelude HJN. pose proof HJN as HJN0.
assert (HSpresN : forall a, sp1 - TCMP_STK <= a < sp1 -> apresent (w_H W) memN a) by (intros a Ha; apply HSpres; lia).
destruct (al_blocks _ _ LAWS lyc Sc W memN mdN pt npt HAR Hpt) as (Hq16 & Hq4096 & Hqceil & Hqh_ia & Hqpres & _ & Hnpt & _). pose proof (proj1 Hqh_ia) as Hqh.
pose proof (blk_off_imgP _ _ _ _ _ _ pt npt HAR Hpt) as Hqh_img.
pose proof (req_size_pos' npt ltac:(lia)) as [_ Hrnp]. pose proof (req_size_pos' Nb ltac:(lia)) as [_ HrNb].
remember (Eimg (Ereg regsN [])) as E eqn:HE. assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regsN []) E) by (rewrite HE; split; [intros nn Hnn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regsN r) by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
pose proof (EE 26%nat 26%bv eq_refl) as E26. rewrite N26 in E26.
pose proof (EE 20%nat 20%bv eq_refl) as E20. rewrite N20 in E20. pose proof (EE 24%nat 24%bv eq_refl) as E24. rewrite N24 in E24.
assert (HS : st_ok_pi SEGS VAL E ss_ttl (restrict (w_H W) (mkst regsN (Z_to_bv 64 (BASE + 0x290c)) memN (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_ttl. unfold st_ok_pi, abs_ss, setpc. cbn [ss_pc ss_regs ss_fregs ss_mem ss_resv ss_facts].
apply (rn_st_ok_any E (BASE + 0x290c) _ regsN _ _ (mrestrict (w_H W) memN)).
- subst E. apply regs_ok_Eimg_Ereg.
- reflexivity.
- apply Forall_nil.
- cbn [pairwise_disjoint all_disjoint]. repeat split.
- split; [|split; exact I]. cbn [ttl_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E20, E24, E26, !unsigned_lit_small by lia. rewrite !Z.pow_0_r, !Z.mod_1_r.
repeat match goal with |- _ /\ _ => split end; lia. }
clear HE. pose proof HS as HS0.
shok_auto SHOK (SOff 29 0) E (mrestrict (w_H W) memN).
hei_havoc HS; paj_run_tok RUN HS HJN SHOK FLBspan.
1: apply awr_ok_nil.
rename HFr into HFra. rename HG into HGa. clear HF.
pose proof (acall_kept_of_run E _ lyc Sc W memN _ mdN (sp1 - TCMP_STK) sp1 (fun a => pt <= a < pt + npt) (proj1 HJN0) HFra HGa
ltac:(unfold ss_ttl; cbn [ss_mem]; intros a (r & Hr & Hw); destruct Hr)
ltac:(intros a Ha; cbn beta in Ha; split; [lia | pose proof (req_size_pos0 npt ltac:(lia)) as [_ Hrqa]; clear - Ha Hqh_img Hrqa; unfold off_img in *; lia]) ltac:(lia) ltac:(intros a Ha; apply HSpresN; lia)) as Ka.
hei_havoc HS; psrr_branch_tok RUN BR HS SHOK FLBspan.
-
rewrite branch_ne_U in Hc. rewrite (U_atom_off _ 20 c (-1)) in Hc by (first [exact E20 | lia]). rewrite U_lit in Hc by lia.
apply (proj1 (negb_true_iff _)) in Hc. apply Z.eqb_neq in Hc.
reshok_bx HS 29%nat. pose proof (proj1 HJN) as HARb.
hei_havoc HS; paj_run_to_tok RUNTO HS HJN SHOK FLBspan 0x287c.
1: apply awr_ok_nil.
rename HFr into HFrb. rename HG into HGb. clear HF.
pose proof (acall_kept_of_run _ _ lyc Sc W _ _ _ (sp1 - TCMP_STK) sp1 (fun a => pt <= a < pt + npt) HARb HFrb HGb
ltac:(cbn [ss_mem]; intros a (r & Hr & Hw); destruct Hr)
ltac:(intros a Ha; cbn beta in Ha; split; [lia | pose proof (req_size_pos0 npt ltac:(lia)) as [_ Hrqa]; clear - Ha Hqh_img Hrqa; unfold off_img in *; lia]) ltac:(lia) ltac:(intros a Ha; pose proof Ka as (_ & _ & _ & _ & _ & K6); apply K6; lia)) as Kb.
pose proof (acall_kept_trans _ _ _ _ _ _ _ _ _ K (acall_kept_trans _ _ _ _ _ _ _ _ _ Ka Kb)) as Kab.
pose proof (regs_kept_of_st_ok_pi _ _ _ regsN _ TIN_KEPT19 HS ltac:(env_agree32 HAE) ltac:(vm_compute; reflexivity)) as HKr. cbn [ms_regs restrict] in HKr.
assert (HK2 : forall r : bv 5, reg_in r TIN_CLOB = false -> getr (ms_regs ms0) r = getr regs r).
{ intros r Hr. transitivity (getr regsN r); [|exact (HK r Hr)].
destruct (tin_clob_cases r Hr) as [-> | Hr']; [rewrite (st_ok_reg SEGS _ _ _ 0%bv HS), (st_ok_reg SEGS _ _ _ 0%bv HS0); reflexivity | exact (HKr r Hr')]. }
prreg HS (29%bv : bv 5) R29. prreg HS (15%bv : bv 5) R15. prreg HS (16%bv : bv 5) R16. prreg HS (17%bv : bv 5) R17.
prreg HS (26%bv : bv 5) R26. prreg HS (20%bv : bv 5) R20. prreg HS (24%bv : bv 5) R24.
pmkst HS.
lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem _) _) ?mdX) _ =>
pose proof (tin_ctx_kept W regs (ms_regs msX) memc mdc (ms_mem msX) mdX sp0 sp1 FP ly S W0 mem0 md0 lyc Sc k fpos ch1
pt npt bimg Nb g cfp bfp tidx gvals cvals bvals gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx _ _ HCTX0 HJN Kab ltac:(lia) ltac:(tctx_regs_of HK2)) as HCTX2 end.
eapply SRr_mono.
{ unfold tin_stmt in IH. eapply (IH (c - 1) _ _ _ _ sp0 sp1 FP ly S W0 mem0 md0 lyc Sc k fpos ch1 pt npt (ti + 1) bimg Nb (idx + 1) g cfp bfp tidx);
[ lia | lia | exact HCTX2 | lia | lia | lia | lia
| rewrite R29, ?ew_ewset_other by lia; rewrite (EE 29%nat 29%bv eq_refl); exact N29
| rewrite R15, ?ew_ewset_other by lia; rewrite (EE 15%nat 15%bv eq_refl); exact N15
| rewrite R16, ?ew_ewset_other by lia; rewrite (EE 16%nat 16%bv eq_refl); exact N16
| rewrite R17, ?ew_ewset_other by lia; rewrite (EE 17%nat 17%bv eq_refl); exact N17
| rewrite R26, ?ew_ewset_other by lia; rewrite E26, unsigned_lit_small by lia; reflexivity
| rewrite R20, ?ew_ewset_other by lia; rewrite E20, unsigned_lit_small by lia; f_equal; lia
| rewrite R24, ?ew_ewset_other by lia; rewrite E24, unsigned_lit_small by lia; reflexivity ]. }
cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HK3 & H293 & H153 & H163 & H173 & K3).
split; [reflexivity|]. exists regs3, mem3, md3. split; [reflexivity|]. split; [exact HJ3|].
split; [intros r Hr; rewrite (HK3 r Hr); exact (HK2 r Hr)|].
split; [exact H293|]. split; [exact H153|]. split; [exact H163|]. split; [exact H173|].
eapply acall_kept_trans; [exact Kab | exact K3].
-
rewrite branch_ne_U in Hc. rewrite (U_atom_off _ 20 c (-1)) in Hc by (first [exact E20 | lia]). rewrite U_lit in Hc by lia.
apply (proj1 (negb_false_iff _)) in Hc. apply Z.eqb_eq in Hc.
reshok_bx HS 29%nat. pose proof (proj1 HJN) as HARb.
hei_havoc HS; paj_run_to_tok RUNTO HS HJN SHOK FLBspan 0x2944.
1: apply awr_ok_nil.
rename HFr into HFrc. rename HG into HGc. clear HF.
pose proof (acall_kept_of_run _ _ lyc Sc W _ _ _ (sp1 - TCMP_STK) sp1 (fun a => pt <= a < pt + npt) HARb HFrc HGc
ltac:(cbn [ss_mem]; intros a (r & Hr & Hw); destruct Hr)
ltac:(intros a Ha; cbn beta in Ha; split; [lia | pose proof (req_size_pos0 npt ltac:(lia)) as [_ Hrqa]; clear - Ha Hqh_img Hrqa; unfold off_img in *; lia]) ltac:(lia) ltac:(intros a Ha; pose proof Ka as (_ & _ & _ & _ & _ & K6); apply K6; lia)) as Kc.
pose proof (regs_kept_of_st_ok_pi _ _ _ regsN _ TIN_KEPT19 HS ltac:(env_agree32 HAE) ltac:(vm_compute; reflexivity)) as HKr. cbn [ms_regs restrict] in HKr.
prreg HS (29%bv : bv 5) R29. prreg HS (15%bv : bv 5) R15. prreg HS (16%bv : bv 5) R16. prreg HS (17%bv : bv 5) R17.
pmkst HS.
apply SRr_ret. split; [reflexivity|].
lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] => exists (ms_regs msx), (ms_mem msx), mdx end.
split; [reflexivity|]. split; [exact HJN|].
split; [intros r Hr; transitivity (getr regsN r); [destruct (tin_clob_cases r Hr) as [-> | Hr']; [cbn [ms_regs]; rewrite (st_ok_reg SEGS _ _ _ 0%bv HS), (st_ok_reg SEGS _ _ _ 0%bv HS0); reflexivity | exact (HKr r Hr')] | exact (HK r Hr)]|].
split; [rewrite R29, ?ew_ewset_other by lia; rewrite (EE 29%nat 29%bv eq_refl); exact N29|].
split; [rewrite R15, ?ew_ewset_other by lia; rewrite (EE 15%nat 15%bv eq_refl); exact N15|].
split; [rewrite R16, ?ew_ewset_other by lia; rewrite (EE 16%nat 16%bv eq_refl); exact N16|].
split; [rewrite R17, ?ew_ewset_other by lia; rewrite (EE 17%nat 17%bv eq_refl); exact N17|].
eapply acall_kept_trans; [exact K | eapply acall_kept_trans; [exact Ka | exact Kc]].
Qed.
Lemma fl_tin_step : forall m, tin_stmt m -> tin_stmt (S m).
Proof.
intros m IH. unfold tin_stmt.
intros c W regs memc mdc sp0 sp1 FP ly S W0 mem0 md0 lyc Sc k fpos ch1
pt npt ti bimg Nb idx g cfp bfp tidx gvals cvals bvals gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx
Hm Hcnt HCTX Hti1 Hti2 Hidx1 Hidx2 H29 H15 H16 H17 H26 H20 H24.
pose proof HCTX as HCTX0. tin_ctx_names HCTX.
tin_prelude HJ. pose proof HJ as HJ0.
assert (HSpres1 : forall a, sp1 - TCMP_STK <= a < sp1 -> apresent (w_H W) memc a) by (intros a Ha; apply HSpres; lia).
destruct (al_blocks _ _ LAWS lyc Sc W memc mdc pt npt HAR Hpt) as (Hq16 & Hq4096 & Hqceil & Hqh_ia & Hqpres & _ & Hnpt & _). pose proof (proj1 Hqh_ia) as Hqh.
pose proof (blk_off_imgP _ _ _ _ _ _ pt npt HAR Hpt) as Hqh_img.
destruct (al_blocks _ _ LAWS lyc Sc W memc mdc bimg Nb HAR Hbi) as (Hi16 & Hi4096 & Hiceil & Hih_ia & Hipres & _). pose proof (proj1 Hih_ia) as Hih.
pose proof (blk_off_imgP _ _ _ _ _ _ bimg Nb HAR Hbi) as Hih_img.
destruct (al_blocks _ _ LAWS lyc Sc W memc mdc g CGIF_SIZE HAR Hg) as (Hg16 & Hg4096 & Hgceil & Hgh_ia & Hgpres & _). pose proof (proj1 Hgh_ia) as Hgh.
pose proof (blk_off_imgP _ _ _ _ _ _ g CGIF_SIZE HAR Hg) as Hgh_img.
destruct (al_blocks _ _ LAWS lyc Sc W memc mdc cfp FRAME_SIZE HAR Hcf) as (Hc16 & Hc4096 & Hcceil & Hcfh_ia & Hcpres & _). pose proof (proj1 Hcfh_ia) as Hcfh.
pose proof (blk_off_imgP _ _ _ _ _ _ cfp FRAME_SIZE HAR Hcf) as Hcfh_img.
destruct (al_blocks _ _ LAWS lyc Sc W memc mdc bfp FRAME_SIZE HAR Hbf) as (Hb16 & Hb4096 & Hbceil & Hbfh_ia & Hbpres & _). pose proof (proj1 Hbfh_ia) as Hbfh.
pose proof (blk_off_imgP _ _ _ _ _ _ bfp FRAME_SIZE HAR Hbf) as Hbfh_img.
change (req_size CGIF_SIZE) with 96 in *. change (req_size FRAME_SIZE) with 40 in *.
pose proof (req_size_pos' npt ltac:(lia)) as [_ Hrnp]. pose proof (req_size_pos' Nb ltac:(lia)) as [_ HrNb].
pose proof (proj1 (proj2 HJ)) as HLY. destruct HLY as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
remember (pt + ti) as p eqn:Ep.
assert (Hp1 : pt <= p) by lia. assert (Hp2 : p + c <= pt + npt) by lia.
destruct (val_mem_byte1 (w_H W) memc p (proj1 (Hqpres p ltac:(lia)))) as (vb & Rvb & Vvb).
remember (Eimg (Ereg regs [Z_to_bv 64 tidx])) as E eqn:HE. assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs [Z_to_bv 64 tidx]) E) by (rewrite HE; split; [intros nn Hnn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r) by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
pose proof (EE 9%nat 9%bv eq_refl) as E9. rewrite H9 in E9. pose proof (EE 29%nat 29%bv eq_refl) as E29. rewrite H29 in E29.
pose proof (EE 21%nat 21%bv eq_refl) as E21. rewrite H21 in E21. pose proof (EE 20%nat 20%bv eq_refl) as E20. rewrite H20 in E20.
pose proof (EE 24%nat 24%bv eq_refl) as E24. rewrite H24 in E24. pose proof (EE 26%nat 26%bv eq_refl) as E26. rewrite H26 in E26.
pose proof (EE 18%nat 18%bv eq_refl) as E18. rewrite H18 in E18.
pose proof (EE 15%nat 15%bv eq_refl) as E15. rewrite H15 in E15. pose proof (EE 16%nat 16%bv eq_refl) as E16. rewrite H16 in E16.
pose proof (EE 17%nat 17%bv eq_refl) as E17. rewrite H17 in E17.
pose proof (EE 1%nat 1%bv eq_refl) as E1. pose proof (EE 2%nat 2%bv eq_refl) as E2. pose proof (EE 3%nat 3%bv eq_refl) as E3.
pose proof (EE 4%nat 4%bv eq_refl) as E4. pose proof (EE 8%nat 8%bv eq_refl) as E8.
assert (E32 : ew E 32 = Z_to_bv 64 tidx) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (Usp : bv_unsigned (ew E 2) = sp1) by (rewrite E2; exact Hsp).
assert (HS : st_ok_pi SEGS VAL E ss_tin (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + 0x287c)) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_tin, tin_regs. unfold st_ok_pi, abs_ss, setpc. cbn [ss_pc ss_regs ss_fregs ss_mem ss_resv ss_facts].
apply (rn_st_ok_any E (BASE + 0x287c) _ regs _ _ (mrestrict (w_H W) memc)).
- subst E. apply regs_ok_pin; [apply regs_ok_Eimg_Ereg | intros X; discriminate X |]. rewrite H19. cbn [sv_denot]. reflexivity.
- reflexivity.
- apply Forall_cons; [|apply Forall_nil]; unfold region_ok, tin_loc; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite E9, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [apply (chunk_ok_val SEGS E _ sp1 184 8 _ tidx); [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Vtidx]|].
apply Forall_cons; [apply (chunk_ok_val SEGS E _ sp1 192 8 _ bfp); [cbn [sv_denot]; rewrite E17, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Vbfp]|].
apply Forall_cons; [apply (chunk_ok_val SEGS E _ sp1 200 8 _ g); [cbn [sv_denot]; rewrite E15, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Vg]|].
apply Forall_cons; [apply (chunk_ok_val SEGS E _ sp1 208 8 _ cfp); [cbn [sv_denot]; rewrite E16, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Vcfp]|].
apply Forall_cons; [apply (chunk_ok_val SEGS E _ sp1 216 8 _ SB); [cbn [sv_denot]; rewrite E29, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | unfold SB; zside | exact Vsb]|].
apply Forall_nil.
- cbn [pairwise_disjoint all_disjoint]. repeat split.
- split; [|split; exact I]. cbn [tin_facts f_atoms atoms_ok]. unfold afact_ok, HPTR. cbn [af_lo af_hi af_al2].
rewrite E9, E29, E21, E20, E24, E26, E18, E15, E16, E17, !unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
rewrite ?C3 in *. unfold SB. repeat match goal with |- _ /\ _ => split end; try (apply mod16_mod8; assumption);
first [lia | match goal with |- ?g => idtac "FACT-LEFT" g end]. }
clear HE. pose proof HS as HS0.
shok_auto SHOK (SOff 29 0) E (mrestrict (w_H W) memc).
hei_havoc HS; paj_run_tok RUN HS HJ SHOK FLBspan.
1: { apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
rename HFr into HFr1. rename HG into HG1. clear HF.
pose proof (acall_kept_of_run E _ lyc Sc W memc _ mdc (sp1 - TCMP_STK) sp1 (fun a => pt <= a < pt + npt) HAR HFr1 HG1
ltac:(unfold ss_tin, tin_loc; cbn [ss_mem]; intros a (r & Hr & Hw); cbn [In] in Hr; destruct Hr as [<- | []]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw; lia)
ltac:(intros a Ha; cbn beta in Ha; split; [lia | pose proof (req_size_pos0 npt ltac:(lia)) as [_ Hrqa]; clear - Ha Hqh_img Hrqa; unfold off_img in *; lia]) ltac:(lia) HSpres1) as K1.
lazymatch type of HS with st_ok_pi _ _ ?E1 _ _ =>
assert (F21 : ew E1 21 = Z_to_bv 64 pt) by (cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E21);
assert (F26 : ew E1 26 = Z_to_bv 64 ti) by (cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E26);
assert (F18 : ew E1 18 = Z_to_bv 64 bimg) by (cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E18);
assert (F24 : ew E1 24 = Z_to_bv 64 idx) by (cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E24) | st_ok _ ?E1 _ _ =>
assert (F21 : ew E1 21 = Z_to_bv 64 pt) by (cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E21);
assert (F26 : ew E1 26 = Z_to_bv 64 ti) by (cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E26);
assert (F18 : ew E1 18 = Z_to_bv 64 bimg) by (cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E18);
assert (F24 : ew E1 24 = Z_to_bv 64 idx) by (cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E24)  end.
pose proof (proj1 HJ) as HAR1.
destruct (al_blocks _ _ LAWS _ _ _ _ _ pt npt HAR1 Hpt) as (_ & _ & _ & _ & Hqpres1 & _).
lazymatch type of HS with st_ok_pi _ _ ?E1 ?ssv ?msv =>
rreg_by HS (27%bv : bv 5) (Z_to_bv 64 (pt + ti)) (denot_add_atoms E1 21 26 pt ti F21 F26 ltac:(lia) ltac:(lia) ltac:(lia)) Rs11;
rewrite <- Ep in Rs11;
pose proof (st_ok_pi_havoc_hi 37 E1 ssv msv [Z_to_bv 64 p; Z_to_bv 64 vb] HS ltac:(vm_compute; reflexivity)) as HS3; hei_pose E1 37%nat [Z_to_bv 64 p; Z_to_bv 64 vb];
clear HS; rename HS3 into HS | st_ok _ ?E1 ?ssv ?msv =>
rreg_by HS (27%bv : bv 5) (Z_to_bv 64 (pt + ti)) (denot_add_atoms E1 21 26 pt ti F21 F26 ltac:(lia) ltac:(lia) ltac:(lia)) Rs11;
rewrite <- Ep in Rs11;
pose proof (st_ok_pi_havoc_hi 37 E1 ssv msv [Z_to_bv 64 p; Z_to_bv 64 vb] HS ltac:(vm_compute; reflexivity)) as HS3; hei_pose E1 37%nat [Z_to_bv 64 p; Z_to_bv 64 vb];
clear HS; rename HS3 into HS  end.
lazymatch type of HS with st_ok_pi _ _ ?E3 ?ssv ?msv =>
lazymatch E3 with havoc ?E1 _ ?ws =>
assert (E37 : ew E3 37 = Z_to_bv 64 p) by (exact (ew_havoc_new E1 37 ws 0 (Z_to_bv 64 0) ltac:(cbn; lia)));
assert (E38 : ew E3 38 = Z_to_bv 64 vb) by (exact (ew_havoc_new E1 37 ws 1 (Z_to_bv 64 0) ltac:(cbn; lia))) end;
assert (Vvb1 : val_mem SEGS (ms_mem msv) p 1 vb)
by (cbn [ms_mem restrict mkst]; apply (val_mem_frame E _ _ _ _ 1 vb HFr1); [| lia | cbn [Z.of_nat]; lia | exact Vvb];
intros kk Hkk; unfold ss_tin, tin_loc; cbn [ss_mem]; intros (r & Hr & Hw); cbn [In] in Hr;
destruct Hr as [<- | []]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw; lia);
pose proof (st_ok_pin_rege E3 ssv msv 27%bv (SOff 37 0) HS ltac:(intros X; discriminate X)
ltac:(cbn [ms_regs restrict mkst]; rewrite Rs11; cbn [sv_denot]; rewrite E37, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)) as HS3;
clear HS; rename HS3 into HS | st_ok _ ?E3 ?ssv ?msv =>
lazymatch E3 with havoc ?E1 _ ?ws =>
assert (E37 : ew E3 37 = Z_to_bv 64 p) by (exact (ew_havoc_new E1 37 ws 0 (Z_to_bv 64 0) ltac:(cbn; lia)));
assert (E38 : ew E3 38 = Z_to_bv 64 vb) by (exact (ew_havoc_new E1 37 ws 1 (Z_to_bv 64 0) ltac:(cbn; lia))) end;
assert (Vvb1 : val_mem SEGS (ms_mem msv) p 1 vb)
by (cbn [ms_mem restrict mkst]; apply (val_mem_frame E _ _ _ _ 1 vb HFr1); [| lia | cbn [Z.of_nat]; lia | exact Vvb];
intros kk Hkk; unfold ss_tin, tin_loc; cbn [ss_mem]; intros (r & Hr & Hw); cbn [In] in Hr;
destruct Hr as [<- | []]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw; lia);
pose proof (st_ok_pin_rege E3 ssv msv 27%bv (SOff 37 0) HS ltac:(intros X; discriminate X)
ltac:(cbn [ms_regs restrict mkst]; rewrite Rs11; cbn [sv_denot]; rewrite E37, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)) as HS3;
clear HS; rename HS3 into HS  end.
norm_ss HS.
lazymatch type of HS with st_ok_pi _ _ ?E3 ?ssv ?msv =>
pose proof (st_ok_pi_add_fact E3 ssv msv 37 (HPTR 0) HS
ltac:(unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite E37, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia)) as HS3;
clear HS; rename HS3 into HS | st_ok _ ?E3 ?ssv ?msv =>
pose proof (st_ok_pi_add_fact E3 ssv msv 37 (HPTR 0) HS
ltac:(unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite E37, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia)) as HS3;
clear HS; rename HS3 into HS  end.
norm_ss HS.
lazymatch type of HS with st_ok_pi _ _ ?E3 ?ssv ?msv =>
pose proof (st_ok_pi_add_fact E3 ssv msv 38 (mkAF 0 255 0) HS
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E38, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia)) as HS3;
clear HS; rename HS3 into HS | st_ok _ ?E3 ?ssv ?msv =>
pose proof (st_ok_pi_add_fact E3 ssv msv 38 (mkAF 0 255 0) HS
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E38, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia)) as HS3;
clear HS; rename HS3 into HS  end.
norm_ss HS.
lazymatch type of HS with st_ok_pi _ _ ?E3 ?ssv ?msv =>
pose proof (st_ok_pi_add_region E3 ssv msv (YP09.mkRegion (Some 37%nat) 0 1 0 1 [YP09.mkChunk 0 (CVal 1 (SOff 38 0))]) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
rewrite E37, unsigned_lit_small by lia; split; [lia|]; split; [lia|];
split; [intros o Ho; apply (apresent_writable SEGS); apply (proj1 (Hqpres1 (p + o) ltac:(lia)))|];
apply Forall_cons; [|apply Forall_nil];
apply (chunk_ok_val SEGS E3 _ p 0 1 _ vb); [cbn [sv_denot]; rewrite E38, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | rewrite Z.add_0_r; exact Vvb1])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E9, !unsigned_lit_small by lia;
repeat split; lia)) as HS3;
clear HS; rename HS3 into HS | st_ok _ ?E3 ?ssv ?msv =>
pose proof (st_ok_pi_add_region E3 ssv msv (YP09.mkRegion (Some 37%nat) 0 1 0 1 [YP09.mkChunk 0 (CVal 1 (SOff 38 0))]) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
rewrite E37, unsigned_lit_small by lia; split; [lia|]; split; [lia|];
split; [intros o Ho; apply (apresent_writable SEGS); apply (proj1 (Hqpres1 (p + o) ltac:(lia)))|];
apply Forall_cons; [|apply Forall_nil];
apply (chunk_ok_val SEGS E3 _ p 0 1 _ vb); [cbn [sv_denot]; rewrite E38, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | rewrite Z.add_0_r; exact Vvb1])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E9, !unsigned_lit_small by lia;
repeat split; lia)) as HS3;
clear HS; rename HS3 into HS  end.
norm_ss HS.
lazymatch type of HS with st_ok_pi _ _ ?E3 _ _ =>
assert (F29 : ew E3 29 = Z_to_bv 64 SB) by (rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E29);
assert (G18 : ew E3 18 = Z_to_bv 64 bimg) by (rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E18);
assert (G24 : ew E3 24 = Z_to_bv 64 idx) by (rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E24) | st_ok _ ?E3 _ _ =>
assert (F29 : ew E3 29 = Z_to_bv 64 SB) by (rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E29);
assert (G18 : ew E3 18 = Z_to_bv 64 bimg) by (rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E18);
assert (G24 : ew E3 24 = Z_to_bv 64 idx) by (rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E24)  end.
lazymatch type of HS with st_ok_pi _ _ ?E3 _ _ =>
assert (G26 : ew E3 26 = Z_to_bv 64 ti) by (rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E26) | st_ok _ ?E3 _ _ =>
assert (G26 : ew E3 26 = Z_to_bv 64 ti) by (rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E26)  end.
hei_havoc HS; psrr_branch_tok RUN BR HS SHOK FLBspan.
1: {
exfalso. match goal with Hb : branch_taken BC_LTU _ _ = true |- _ => rewrite branch_ltu_U in Hb; rewrite (U_atom _ 37 p E37), (U_atom _ 26 ti G26) in Hb by lia; apply Z.ltb_lt in Hb; lia end. }
reshok_bx HS 29%nat.
hei_havoc HS; paj_run_tok RUN HS HJ SHOK FLBspan.
all: try (lazymatch goal with |- range_addressable _ (U ?Ex _) (U _ (SOff 37 ?cc)) ?len =>
first [rewrite (U_atom_off Ex 37 p cc E37) by lia | rewrite (U_atom Ex 37 p E37) by lia];
eapply (obl_of_block SEGS _ LAWS _ _ _ _ _ Ex (SOff 29 0) _ len pt npt HAR1 Hpt); [rewrite (U_atom Ex 29 SB F29); [reflexivity | unfold SB; lia] | lia | lia] end).
1: { eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 37%nat); [reflexivity | rewrite E37; apply unsigned_lit_small; lia
| intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; apply (Hpawr (ablocks B lyc Sc)); [exact Hpt | clear - Ha Hp1 Hp2 Hcnt; lia] |].
apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
rename HFr into HFr2. rename HG into HG2. clear HF.
pose proof (acall_kept_of_run _ _ lyc Sc W _ _ _ (sp1 - TCMP_STK) sp1 (fun a => pt <= a < pt + npt) HAR1 HFr2 HG2
ltac:(intros a (r & Hr & Hw); cbn [In] in Hr; destruct Hr as [<- | [<- | []]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw;
[rewrite E37, unsigned_lit_small in Hw by lia; left; lia | lia])
ltac:(intros a Ha; cbn beta in Ha; split; [lia | pose proof (req_size_pos0 npt ltac:(lia)) as [_ Hrqa]; clear - Ha Hqh_img Hrqa; unfold off_img in *; lia]) ltac:(lia) ltac:(pose proof K1 as (_ & _ & _ & _ & _ & K6); exact K6)) as K2.
pose proof (acall_kept_trans _ _ _ _ _ _ _ _ _ K1 K2) as K12.
lazymatch type of HS with st_ok_pi _ _ ?E1 _ _ =>
assert (F18b : ew E1 18 = Z_to_bv 64 bimg) by (rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E18);
assert (F24b : ew E1 24 = Z_to_bv 64 idx) by (rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E24) | st_ok _ ?E1 _ _ =>
assert (F18b : ew E1 18 = Z_to_bv 64 bimg) by (rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E18);
assert (F24b : ew E1 24 = Z_to_bv 64 idx) by (rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E24)  end.
pose proof (proj1 HJ) as HAR2.
assert (Hbx : bimg <= bimg + idx < bimg + req_size Nb) by lia.
destruct (al_blocks _ _ LAWS _ _ _ _ _ bimg Nb HAR2 Hbi) as (_ & _ & _ & _ & Hipres2 & _).
destruct (val_mem_byte1 (w_H W) _ (bimg + idx) (proj1 (Hipres2 (bimg + idx) Hbx))) as (vbb & Rvbb & Vvbb).
lazymatch type of HS with st_ok_pi _ _ ?E1 ?ssv ?msv =>
rreg_by HS (10%bv : bv 5) (Z_to_bv 64 (bimg + idx)) (denot_add_atoms E1 18 24 bimg idx F18b F24b ltac:(lia) ltac:(lia) ltac:(lia)) Ra0;
pose proof (st_ok_pi_havoc_hi 45 E1 ssv msv [Z_to_bv 64 (bimg + idx); Z_to_bv 64 vbb] HS ltac:(vm_compute; reflexivity)) as HS3; hei_pose E1 45%nat [Z_to_bv 64 (bimg + idx); Z_to_bv 64 vbb];
clear HS; rename HS3 into HS | st_ok _ ?E1 ?ssv ?msv =>
rreg_by HS (10%bv : bv 5) (Z_to_bv 64 (bimg + idx)) (denot_add_atoms E1 18 24 bimg idx F18b F24b ltac:(lia) ltac:(lia) ltac:(lia)) Ra0;
pose proof (st_ok_pi_havoc_hi 45 E1 ssv msv [Z_to_bv 64 (bimg + idx); Z_to_bv 64 vbb] HS ltac:(vm_compute; reflexivity)) as HS3; hei_pose E1 45%nat [Z_to_bv 64 (bimg + idx); Z_to_bv 64 vbb];
clear HS; rename HS3 into HS  end.
lazymatch type of HS with st_ok_pi _ _ ?E3 ?ssv ?msv =>
lazymatch E3 with havoc ?E1 _ ?ws =>
assert (E39 : ew E3 45 = Z_to_bv 64 (bimg + idx)) by (exact (ew_havoc_new E1 45 ws 0 (Z_to_bv 64 0) ltac:(cbn; lia)));
assert (E40 : ew E3 46 = Z_to_bv 64 vbb) by (exact (ew_havoc_new E1 45 ws 1 (Z_to_bv 64 0) ltac:(cbn; lia))) end;
pose proof (st_ok_pin_rege E3 ssv msv 10%bv (SOff 45 0) HS ltac:(intros X; discriminate X)
ltac:(cbn [ms_regs restrict mkst]; rewrite Ra0; cbn [sv_denot]; rewrite E39, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)) as HS3;
clear HS; rename HS3 into HS | st_ok _ ?E3 ?ssv ?msv =>
lazymatch E3 with havoc ?E1 _ ?ws =>
assert (E39 : ew E3 45 = Z_to_bv 64 (bimg + idx)) by (exact (ew_havoc_new E1 45 ws 0 (Z_to_bv 64 0) ltac:(cbn; lia)));
assert (E40 : ew E3 46 = Z_to_bv 64 vbb) by (exact (ew_havoc_new E1 45 ws 1 (Z_to_bv 64 0) ltac:(cbn; lia))) end;
pose proof (st_ok_pin_rege E3 ssv msv 10%bv (SOff 45 0) HS ltac:(intros X; discriminate X)
ltac:(cbn [ms_regs restrict mkst]; rewrite Ra0; cbn [sv_denot]; rewrite E39, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)) as HS3;
clear HS; rename HS3 into HS  end.
norm_ss HS.
lazymatch type of HS with st_ok_pi _ _ ?E3 ?ssv ?msv =>
pose proof (st_ok_pi_add_fact E3 ssv msv 45 (HPTR 0) HS
ltac:(unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite E39, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia)) as HS3;
clear HS; rename HS3 into HS | st_ok _ ?E3 ?ssv ?msv =>
pose proof (st_ok_pi_add_fact E3 ssv msv 45 (HPTR 0) HS
ltac:(unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite E39, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia)) as HS3;
clear HS; rename HS3 into HS  end.
norm_ss HS.
lazymatch type of HS with st_ok_pi _ _ ?E3 ?ssv ?msv =>
pose proof (st_ok_pi_add_fact E3 ssv msv 46 (mkAF 0 255 0) HS
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E40, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia)) as HS3;
clear HS; rename HS3 into HS | st_ok _ ?E3 ?ssv ?msv =>
pose proof (st_ok_pi_add_fact E3 ssv msv 46 (mkAF 0 255 0) HS
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E40, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia)) as HS3;
clear HS; rename HS3 into HS  end.
norm_ss HS.
lazymatch type of HS with st_ok_pi _ _ ?E3 ?ssv ?msv =>
assert (G37 : ew E3 37 = Z_to_bv 64 p) by (rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; first [reflexivity | exact E37]);
pose proof (st_ok_pi_add_region E3 ssv msv (YP09.mkRegion (Some 45%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 46 0))]) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
rewrite E39, unsigned_lit_small by lia; split; [lia|]; split; [lia|]; split; [intros o Ho; lia|];
apply Forall_cons; [|apply Forall_nil];
apply (chunk_ok_val SEGS E3 _ (bimg + idx) 0 1 _ vbb); [cbn [sv_denot]; rewrite E40, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | rewrite Z.add_0_r; exact Vvbb])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite G37, E39; rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E9, !unsigned_lit_small by lia;
repeat split; lia)) as HS3;
clear HS; rename HS3 into HS | st_ok _ ?E3 ?ssv ?msv =>
assert (G37 : ew E3 37 = Z_to_bv 64 p) by (rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; first [reflexivity | exact E37]);
pose proof (st_ok_pi_add_region E3 ssv msv (YP09.mkRegion (Some 45%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 46 0))]) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
rewrite E39, unsigned_lit_small by lia; split; [lia|]; split; [lia|]; split; [intros o Ho; lia|];
apply Forall_cons; [|apply Forall_nil];
apply (chunk_ok_val SEGS E3 _ (bimg + idx) 0 1 _ vbb); [cbn [sv_denot]; rewrite E40, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | rewrite Z.add_0_r; exact Vvbb])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite G37, E39; rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E9, !unsigned_lit_small by lia;
repeat split; lia)) as HS3;
clear HS; rename HS3 into HS  end.
norm_ss HS.
lazymatch type of HS with st_ok_pi _ _ ?E3 _ _ =>
assert (G18c : ew E3 18 = Z_to_bv 64 bimg) by (rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E18) | st_ok _ ?E3 _ _ =>
assert (G18c : ew E3 18 = Z_to_bv 64 bimg) by (rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E18)  end.
hei_havoc HS; psrr_branch_tok RUN BR HS SHOK FLBspan.
1: {
exfalso. match goal with Hb : branch_taken BC_LTU _ _ = true |- _ => rewrite branch_ltu_U in Hb; rewrite (U_atom _ 45 (bimg + idx) E39), (U_atom _ 18 bimg G18c) in Hb by lia; apply Z.ltb_lt in Hb; lia end. }
lazymatch type of HS with st_ok_pi _ _ ?E3 _ _ =>
assert (F6 : ew E3 29 = Z_to_bv 64 SB) by (rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E29) | st_ok _ ?E3 _ _ =>
assert (F6 : ew E3 29 = Z_to_bv 64 SB) by (rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E29)  end.
reshok_bx HS 29%nat.
hei_havoc HS; paj_run_to_tok RUNTO HS HJ SHOK FLBspan AF_both3_cmpPixel.
all: try (lazymatch goal with |- range_addressable _ (U ?Ex _) (U _ (SOff 45 ?cc)) ?len =>
first [rewrite (U_atom_off Ex 45 (bimg + idx) cc E39) by lia | rewrite (U_atom Ex 45 (bimg + idx) E39) by lia];
eapply (obl_of_block SEGS _ LAWS _ _ _ _ _ Ex (SOff 29 0) _ len bimg Nb HAR2 Hbi); [rewrite (U_atom Ex 29 SB F6); [reflexivity | unfold SB; lia] | lia | lia] end).
1: { apply awr_ok_cons_ro; [cbn; lia|].
eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 37%nat); [reflexivity | rewrite G37; apply unsigned_lit_small; lia
| intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; apply (Hpawr (ablocks B lyc Sc)); [exact Hpt | clear - Ha Hp1 Hp2 Hcnt; lia] |].
apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
rename HFr into HFr3. rename HG into HG3. clear HF.
pose proof (acall_kept_of_run _ _ lyc Sc W _ _ _ (sp1 - TCMP_STK) sp1 (fun a => pt <= a < pt + npt) HAR2 HFr3 HG3
ltac:(intros a (r & Hr & Hw); cbn [In] in Hr; destruct Hr as [<- | [<- | [<- | []]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw;
[lia | rewrite G37, unsigned_lit_small in Hw by lia; left; lia | lia])
ltac:(intros a Ha; cbn beta in Ha; split; [lia | pose proof (req_size_pos0 npt ltac:(lia)) as [_ Hrqa]; clear - Ha Hqh_img Hrqa; unfold off_img in *; lia]) ltac:(lia) ltac:(pose proof K12 as (_ & _ & _ & _ & _ & K6); exact K6)) as K3.
pose proof (acall_kept_trans _ _ _ _ _ _ _ _ _ K12 K3) as K123.
prreg HS (10%bv : bv 5) Qa0. prreg HS (11%bv : bv 5) Qa1. prreg HS (12%bv : bv 5) Qa2. prreg HS (13%bv : bv 5) Qa3. prreg HS (14%bv : bv 5) Qa4.
prreg HS (1%bv : bv 5) Qra. prreg HS (2%bv : bv 5) Qsp. prreg HS (3%bv : bv 5) Qgp. prreg HS (4%bv : bv 5) Qtp. prreg HS (8%bv : bv 5) Qs0.
pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ TIN_KEPT HS ltac:(env_agree32 HAE) ltac:(vm_compute; reflexivity)) as HKrX. cbn [ms_regs restrict] in HKrX.
pose proof (proj1 HJ) as HARX.
pmkst HS.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) ?pcX (ms_mem _) _) ?mdX) _ =>
eapply (aj_call_sp W (ms_regs msX) (ms_mem msX) pcX TFLUSH_STK sp0 FP ly S W0 mem0 md0 [(1, fpos)] lyc Sc mdX k TCMP_STK [] 0 (sp1 - sp0) (Z_to_bv 64 (BASE + 0x28e4)) ch1
(fun ly2 S2 W2 regs2 mem2 md2 => ly2 = lyc /\ S2 = Sc /\ W2 = W /\ exists v : word, getr regs2 10 = v /\
(v = w64 0 <-> tcmp_zero (aview SEGS (w_H W) (ms_mem msX)) gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx vb vbb)) HJ) end.
- unfold spZ. rewrite Qsp. rewrite Usp. lia.
- rewrite Zminus_mod, Hsp1al, Hal16. reflexivity.
- lia. - rewrite WS. lia. - rewrite WS, FFS. lia.
- rewrite Qgp, E3. exact Hgp. - rewrite Qtp, E4. exact Htp.
- exact Qra. - apply ret_ok_codeptr_v; [lazymatch goal with |- _ <= ?k < _ => try unfold k end; lia | reflexivity]. - rewrite unsigned_lit_small by lia. lia.
- unfold s0Z. rewrite Qs0, E8. replace (sp0 + (sp1 - sp0)) with sp1 by lia. eapply achain_keptK; [exact K123 | exact Hch | lia | lia | lia].
- intros HPRE1. eapply SRr_mono.
+ eapply (TCMP lyc Sc W _ _ _ ch1 g cfp bfp vb vbb gvals cvals bvals gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx HPRE1).
* rewrite Qa0, E15. reflexivity. * rewrite Qa1, E16. reflexivity. * rewrite Qa2, E17. reflexivity.
* first [exact Qa3 | rewrite Qa3, E38; reflexivity | rewrite Qa3; reflexivity]. * first [exact Qa4 | rewrite Qa4, E40; reflexivity | rewrite Qa4; reflexivity]. * lia. * lia.
* exact Hg. * exact Hcf. * exact Hbf. * exact Hcb.
* eapply obj_at_keptK; [exact K123 | exact Hg | vm_compute; reflexivity | change (req_size CGIF_SIZE) with 96; intros i Hi Hn; lia | exact Og].
* exact Ogpal. * exact Ongp.
* eapply obj_at_keptK; [exact K123 | exact Hcf | vm_compute; reflexivity | change (req_size FRAME_SIZE) with 40; intros i Hi Hn; lia | exact Oc].
* exact Ocpal. * exact Ocattr. * exact Ocnlp. * exact Octidx.
* eapply obj_at_keptK; [exact K123 | exact Hbf | vm_compute; reflexivity | change (req_size FRAME_SIZE) with 40; intros i Hi Hn; lia | exact Ob].
* exact Obpal. * exact Obattr. * exact Obnlp. * exact Obtidx.
* exact HLc. * exact HLb. * exact HGp.
+ cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & v & -> & HJc & HPc & Hv & Hz).
exists lyc, Sc, regs2, mem2, md2. split; [rewrite Qra; reflexivity|]. split; [exact HJc|]. split; [exact HPc|].
split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. exists v. split; [exact Hv | exact Hz].
- intros a (r & Hr & _). destruct Hr. }
cbv beta. intros W2 c2 Hwle2 (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJc & HP2 & -> & -> & -> & v & Hv & Hz).
rewrite Z.add_0_r in HJ2. replace (sp0 + (sp1 - sp0)) with sp1 in HJc by lia.
clear Qa0 Qa1 Qa2 Qa3 Qa4 Qra Qsp Qgp Qtp Qs0.
pose proof (acall_kept_of_journal SEGS B pa_segs_low TCMP_STK sp1 [] [] lyc Sc W _ _ lyc Sc W mem2 md2 0 (fun _ => False) HJc HARX
ltac:(intros a (r & Hr & _); destruct Hr) ltac:(intros b mm i Hb _ _; exact Hb) sink_closed_nil) as Kc0.
pose proof (acall_kept_mono_E SEGS B _ _ _ _ _ _ _ _ _ (fun a => pt <= a < pt + npt) Kc0 ltac:(intros a HF; destruct HF)) as Kc.
pose proof (acall_kept_trans _ _ _ _ _ _ _ _ _ K123 Kc) as K12c.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx _ =>
let kk := eval vm_compute in (run_K A_LIM (SOff 29 0) [] ssx) in
jafter_call_keep_hi HS kk regs2 (mrestrict (w_H W) mem2) HP2 [1; 2]%nat HS2 | st_ok _ ?Ev ?ssx _ =>
let kk := eval vm_compute in (run_K A_LIM (SOff 29 0) [] ssx) in
jafter_call_keep_hi HS kk regs2 (mrestrict (w_H W) mem2) HP2 [1; 2]%nat HS2  end.
match type of HS2 with ?Q -> _ =>
assert (HQ : Q);
[ cbn [ms_mem restrict]; apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]
| specialize (HS2 HQ); clear HQ ] end.
{ eapply (region_kept_sub_ajw _ lyc Sc W _ W mem2 _ _ _ 37 0 1 0 1 _ p pt npt lyc Sc md2);
[ exact Kc0 | exact (proj1 HJ2) | exact Hpt
| rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; first [apply unsigned_lit_small; lia | rewrite E37; apply unsigned_lit_small; lia]
| exact Hpt | lia | lia | lia | lia | intros a Ha Hn; exact Hn ]. }
{ eapply (region_kept_stack_aj SEGS _); [exact Kc0 | exact HJ2
| rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E9; apply unsigned_lit_small; lia
| lia | rewrite FFS; lia | lia | lia | lia]. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
lazymatch type of HS with st_ok_pi _ _ ?Ecur _ _ =>
assert (H37 : ew Ecur 37 = Z_to_bv 64 p) by (rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; first [reflexivity | exact E37]);
assert (G29 : ew Ecur 29 = Z_to_bv 64 SB) by (rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E29) | st_ok _ ?Ecur _ _ =>
assert (H37 : ew Ecur 37 = Z_to_bv 64 p) by (rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; first [reflexivity | exact E37]);
assert (G29 : ew Ecur 29 = Z_to_bv 64 SB) by (rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E29)  end.
reshok_bx HS 29%nat.
pose proof (proj1 HJ2) as HAR3.
hei_havoc HS; paj_run_tok RUN HS HJ2 SHOK FLBspan.
1: { eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 37%nat); [reflexivity | rewrite H37; apply unsigned_lit_small; lia
| intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; apply (Hpawr (ablocks B lyc Sc)); [exact Hpt | clear - Ha Hp1 Hp2 Hcnt; lia] |].
apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
rename HFr into HFr4. rename HG into HG4. clear HF.
pose proof (acall_kept_of_run _ _ lyc Sc W _ _ _ (sp1 - TCMP_STK) sp1 (fun a => pt <= a < pt + npt) HAR3 HFr4 HG4
ltac:(intros a (r & Hr & Hw); cbn [In] in Hr; destruct Hr as [<- | [<- | []]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw;
[rewrite H37, unsigned_lit_small in Hw by lia; left; lia | lia])
ltac:(intros a Ha; cbn beta in Ha; split; [lia | pose proof (req_size_pos0 npt ltac:(lia)) as [_ Hrqa]; clear - Ha Hqh_img Hrqa; unfold off_img in *; lia]) ltac:(lia) ltac:(pose proof Kc as (_ & _ & _ & _ & _ & K6); exact K6)) as K4.
pose proof (acall_kept_trans _ _ _ _ _ _ _ _ _ K12c K4) as K1234.
assert (TAIL : forall Ex ssx msx mdx, st_ok_pi SEGS VAL Ex ssx (restrict (w_H W) msx) -> ss_pc ssx = 0x290c -> ss_resv ssx = None ->
env_agree 32 (Ereg regs [Z_to_bv 64 tidx]) Ex ->
forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ssx) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) TIN_KEPT = true ->
sr_get (ss_regs ssx) 0%bv = SLit 0 -> sr_get (ss_regs ssx) 19%bv = SLit 1 ->
sr_get (ss_regs ssx) 29%bv = SOff 29 0 -> sr_get (ss_regs ssx) 15%bv = SOff 15 0 -> sr_get (ss_regs ssx) 16%bv = SOff 16 0 -> sr_get (ss_regs ssx) 17%bv = SOff 17 0 ->
sr_get (ss_regs ssx) 26%bv = SOff 26 0 -> sr_get (ss_regs ssx) 20%bv = SOff 20 0 -> sr_get (ss_regs ssx) 24%bv = SOff 24 0 ->
ajournal SEGS B TFLUSH_STK sp0 FP ly S W0 mem0 md0 [(1, fpos)] lyc Sc W (ms_mem msx) mdx k ->
acall_kept SEGS B lyc Sc W memc W (ms_mem msx) (sp1 - TCMP_STK) sp1 (fun a => pt <= a < pt + npt) ->
SRr SEGS W (mkCfg msx mdx) (tin_post W regs memc sp0 sp1 FP ly S W0 mem0 md0 lyc Sc k fpos pt npt g cfp bfp)).
{ intros Ex ssx msx mdx HSx Hpc Hrv HAEx Hkept H0 H19x H29x H15x H16x H17x H26x H20x H24x HJx Kx.
pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ TIN_KEPT HSx HAEx Hkept) as HKx. cbn [ms_regs restrict] in HKx.
assert (XX : forall n (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew Ex n = getr regs r).
{ intros n r Hn32 Hn. rewrite (proj1 HAEx n Hn32). apply ew_Ereg_nat. exact Hn. }
rewrite (st_ok_pi_restrict_mkst _ _ _ _ HSx Hrv). rewrite Hpc.
eapply (fl_tin_tail m IH c W regs (ms_regs msx) memc mdc (ms_mem msx) mdx sp0 sp1 FP ly S W0 mem0 md0 lyc Sc k fpos ch1
pt npt ti bimg Nb idx g cfp bfp tidx gvals cvals bvals gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx);
[ lia | exact Hcnt | exact HCTX0 | exact Hti1 | exact Hti2 | exact Hidx1 | exact Hidx2 | exact HJx | exact Kx | | | | | | | | ].
- intros r Hr. destruct (tin_clob_cases3 r Hr) as [-> | [-> | Hr']].
+ rewrite (st_ok_pi_restrict_reg _ _ _ _ 0%bv HSx), H0. rewrite (st_ok_restrict_reg SEGS _ _ _ _ 0%bv HS0). reflexivity.
+ rewrite (st_ok_pi_restrict_reg _ _ _ _ 19%bv HSx), H19x, H19. reflexivity.
+ exact (HKx r Hr').
- rewrite (st_ok_pi_restrict_reg _ _ _ _ 29%bv HSx), H29x. cbn [sv_denot]. rewrite (XX 29%nat 29%bv ltac:(lia) eq_refl), H29, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
- rewrite (st_ok_pi_restrict_reg _ _ _ _ 15%bv HSx), H15x. cbn [sv_denot]. rewrite (XX 15%nat 15%bv ltac:(lia) eq_refl), H15, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
- rewrite (st_ok_pi_restrict_reg _ _ _ _ 16%bv HSx), H16x. cbn [sv_denot]. rewrite (XX 16%nat 16%bv ltac:(lia) eq_refl), H16, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
- rewrite (st_ok_pi_restrict_reg _ _ _ _ 17%bv HSx), H17x. cbn [sv_denot]. rewrite (XX 17%nat 17%bv ltac:(lia) eq_refl), H17, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
- rewrite (st_ok_pi_restrict_reg _ _ _ _ 26%bv HSx), H26x. cbn [sv_denot]. rewrite (XX 26%nat 26%bv ltac:(lia) eq_refl), H26, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
- rewrite (st_ok_pi_restrict_reg _ _ _ _ 20%bv HSx), H20x. cbn [sv_denot]. rewrite (XX 20%nat 20%bv ltac:(lia) eq_refl), H20, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
- rewrite (st_ok_pi_restrict_reg _ _ _ _ 24%bv HSx), H24x. cbn [sv_denot]. rewrite (XX 24%nat 24%bv ltac:(lia) eq_refl), H24, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
hei_havoc HS; psrr_branch_tok RUN BR HS SHOK FLBspan.
-
reshok_bx HS 29%nat. pose proof (proj1 HJ2) as HAR4.
hei_havoc HS; paj_run_to_tok RUNTO HS HJ2 SHOK FLBspan 0x290c.
1: { eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 37%nat); [reflexivity | rewrite H37; apply unsigned_lit_small; lia
| intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; apply (Hpawr (ablocks B lyc Sc)); [exact Hpt | clear - Ha Hp1 Hp2 Hcnt; lia] |].
apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
rename HFr into HFr5. rename HG into HG5. clear HF.
pose proof (acall_kept_of_run _ _ lyc Sc W _ _ _ (sp1 - TCMP_STK) sp1 (fun a => pt <= a < pt + npt) HAR4 HFr5 HG5
ltac:(intros a (r & Hr & Hw); cbn [In] in Hr; destruct Hr as [<- | [<- | []]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw;
[rewrite H37, unsigned_lit_small in Hw by lia; left; lia | lia])
ltac:(intros a Ha; cbn beta in Ha; split; [lia | pose proof (req_size_pos0 npt ltac:(lia)) as [_ Hrqa]; clear - Ha Hqh_img Hrqa; unfold off_img in *; lia]) ltac:(lia) ltac:(pose proof K4 as (_ & _ & _ & _ & _ & K6); exact K6)) as K5.
eapply (TAIL _ _ _ _ HS); [reflexivity | reflexivity | env_agree32 HAE | vm_compute; reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
| reflexivity | reflexivity | reflexivity | exact HJ2 | exact (acall_kept_trans _ _ _ _ _ _ _ _ _ K1234 K5) ].
-
reshok_bx HS 29%nat. pose proof (proj1 HJ2) as HAR4.
hei_havoc HS; paj_run_to_tok RUNTO HS HJ2 SHOK FLBspan 0x290c.
all: try (lazymatch goal with |- range_addressable _ (U ?Ex _) (U _ (SOff 37 ?cc)) ?len =>
first [rewrite (U_atom_off Ex 37 p cc H37) by lia | rewrite (U_atom Ex 37 p H37) by lia];
eapply (obl_of_block SEGS _ LAWS _ _ _ _ _ Ex (SOff 29 0) _ len pt npt HAR4 Hpt); [rewrite (U_atom Ex 29 SB G29); [reflexivity | unfold SB; lia] | lia | lia] end).
1: { eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 37%nat); [reflexivity | rewrite H37; apply unsigned_lit_small; lia
| intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; apply (Hpawr (ablocks B lyc Sc)); [exact Hpt | clear - Ha Hp1 Hp2 Hcnt; lia] |].
apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
rename HFr into HFr5. rename HG into HG5. clear HF.
pose proof (acall_kept_of_run _ _ lyc Sc W _ _ _ (sp1 - TCMP_STK) sp1 (fun a => pt <= a < pt + npt) HAR4 HFr5 HG5
ltac:(intros a (r & Hr & Hw); cbn [In] in Hr; destruct Hr as [<- | [<- | []]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw;
[rewrite H37, unsigned_lit_small in Hw by lia; left; lia | lia])
ltac:(intros a Ha; cbn beta in Ha; split; [lia | pose proof (req_size_pos0 npt ltac:(lia)) as [_ Hrqa]; clear - Ha Hqh_img Hrqa; unfold off_img in *; lia]) ltac:(lia) ltac:(pose proof K4 as (_ & _ & _ & _ & _ & K6); exact K6)) as K5.
eapply (TAIL _ _ _ _ HS); [reflexivity | reflexivity | env_agree32 HAE | vm_compute; reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
| reflexivity | reflexivity | reflexivity | exact HJ2 | exact (acall_kept_trans _ _ _ _ _ _ _ _ _ K1234 K5) ].
Qed.
Lemma fl_tin : forall m, tin_stmt m.
Proof.
induction m as [|m IH]; [|exact (fl_tin_step m IH)].
unfold tin_stmt. intros. exfalso. lia.
Qed.
End TL.
End f.
End d.
