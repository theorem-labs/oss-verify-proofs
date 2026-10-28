(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI09 YI08 YI0m YI0n YI0s YCbw.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI5w.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0d YP0c YI0w YI0x YC4a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC80 YC1f YC1g YC1h YC81 YC4b YC44 YC45 YC44.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACj2.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC20.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AC8a AChd ACjr ACj1 ACj0.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
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
Context {PI : PAImg lib_asan3_0_listing}.
Context {RO : YC20.ro_below_ofl (@pa_segs _ lib_asan3_0_listing PI) (@pa_relro_lo _ lib_asan3_0_listing PI) (@pa_relro_hi _ lib_asan3_0_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ lib_asan3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_asan3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_asan3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_asan3_0_listing PI A_TEXT).
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
Let RET := paj_ret_at (PL := PL_asan3_0) (PI := PI).
Let PBASE := @pa_B_ok _ _ PI. Let PBLO := @pa_base_lo _ _ PL_asan3_0 PI.
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
Definition TIN_CLOB : list (bv 5) := [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 18; 20; 23; 24; 25; 28; 29; 30; 31]%bv.
Definition TIN_KEPT27 : list (bv 5) := [2; 3; 4; 8; 9; 19; 21; 22; 26; 27]%bv.
Definition TIN_KEPT : list (bv 5) := [2; 3; 4; 8; 9; 19; 21; 22; 26]%bv.
Lemma tin_clob_cases : forall r : bv 5, reg_in r TIN_CLOB = false -> r = 0%bv \/ In r TIN_KEPT27.
Proof.
intros r Hr. pose proof (all_regs_in r) as Hin. cbv [all_regs In] in Hin.
repeat (destruct Hin as [<-|Hin]; [first [left; reflexivity | vm_compute in Hr; discriminate | right; cbv; tauto] |]). destruct Hin.
Qed.
Lemma tin_clob_cases3 : forall r : bv 5, reg_in r TIN_CLOB = false -> r = 0%bv \/ r = 27%bv \/ In r TIN_KEPT.
Proof.
intros r Hr. pose proof (all_regs_in r) as Hin. cbv [all_regs In] in Hin.
repeat (destruct Hin as [<-|Hin]; [first [left; reflexivity | right; left; reflexivity | vm_compute in Hr; discriminate | right; right; cbv; tauto] |]). destruct Hin.
Qed.
Definition tin_regs := sr_set (sr_set sr_atoms 18%bv (SOff 23 0)) 27%bv (SLit 4294967295).
Definition tin_loc : YP09.region :=
YP09.mkRegion (Some 9%nat) 232 256 232 232
[YP09.mkChunk 232 (CVal 8 (SOff 32 0)); YP09.mkChunk 240 (CVal 8 (SOff 6 0)); YP09.mkChunk 248 (CVal 8 (SOff 33 0))].
Definition tin_tmp : YP09.region := YP09.mkRegion (Some 23%nat) 0 1 0 1 [YP09.mkChunk 0 (CVal 1 (SOff 34 0))].
Definition tin_facts : facts :=
mkFacts [ (9%nat, mkAF 70368744177664 140737488355328 4); (6%nat, mkAF SB SB 0); (23%nat, HPTR 0); (20%nat, mkAF 1 65535 0);
(24%nat, mkAF 0 4294967295 0); (26%nat, HPTR 0); (21%nat, HPTR 4); (22%nat, HPTR 3); (33%nat, HPTR 3); (34%nat, mkAF 0 255 0) ] [] [].
Definition ss_tin : sstate := mkSS 0x220c tin_regs [tin_loc; tin_tmp] None tin_facts.
Definition ttl_loc : YP09.region := YP09.mkRegion (Some 9%nat) 240 248 240 240 [YP09.mkChunk 240 (CVal 8 (SOff 32 0))].
Definition ttl_facts : facts := mkFacts [ (20%nat, mkAF 1 65535 0); (23%nat, HPTR 0); (24%nat, mkAF 0 4294967295 0); (32%nat, mkAF SB SB 0) ] [] [].
Definition ss_ttl : sstate := mkSS 0x2260 (sr_set sr_atoms 18%bv (SOff 23 0)) [ttl_loc] None ttl_facts.
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
(lyc : alayout) (Sc : astate) (k : Z) (fpos pt npt : Z) : world SEGS -> config -> Prop :=
fun W' c' => W' = W /\ exists regs' mem' md',
c' = mkCfg (mkst regs' (Z_to_bv 64 (BASE + 0x22a0)) mem' (seg_rom SEGS)) md' /\
ajournal SEGS B TFLUSH_STK sp0 FP ly S W0 mem0 md0 [(2, fpos)] lyc Sc W mem' md' k /\
(forall r : bv 5, reg_in r TIN_CLOB = false -> getr regs' r = getr regs r) /\
getr regs' 6 = Z_to_bv 64 SB /\
acall_kept SEGS B lyc Sc W memc W mem' (sp1 - TCMP_STK) sp1 (fun a => pt <= a < pt + npt).
Definition tin_ctx (W : world SEGS) (regs : bvmap 5 word) (memc : word -> option byte) (mdc : Model) (sp0 sp1 : Z) (FP : list (Z * Z))
(ly : alayout) (S : astate) (W0 : world SEGS) (mem0 : word -> option byte) (md0 : Model) (lyc : alayout) (Sc : astate) (k : Z) (fpos : Z)
(ch1 : list (Z * Z * Z)) (pt npt bimg Nb g cfp bfp tidx : Z) (gvals cvals bvals : list Z) (gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx : Z) : Prop :=
ajournal SEGS B TFLUSH_STK sp0 FP ly S W0 mem0 md0 [(2, fpos)] lyc Sc W memc mdc k /\
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
spZ regs = sp1 /\ sp0 - 400 <= sp1 <= sp0 - 384 /\ sp1 mod 16 = 0 /\
getr regs 9 = Z_to_bv 64 sp1 /\ getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\
achain lyc (aview SEGS (w_H W) memc) sp1 (s0Z regs) ch1 /\ s0Z regs = sp0 /\
val_mem SEGS (mrestrict (w_H W) memc) (sp1 + 232) 8 tidx /\ 0 <= tidx < 2 ^ 64 /\
val_mem SEGS (mrestrict (w_H W) memc) (sp1 + 240) 8 SB /\
val_mem SEGS (mrestrict (w_H W) memc) (sp1 + 248) 8 bfp /\
getr regs 26 = Z_to_bv 64 bimg /\ getr regs 27 = Z_to_bv 64 4294967295 /\ getr regs 21 = Z_to_bv 64 g /\ getr regs 22 = Z_to_bv 64 cfp.
Ltac tin_ctx_names H :=
destruct H as (HJ & Hpt & Hpawr & Hbi & HNb & HsepI & Hg & Hcf & Hbf & Hcb & HsepG & HsepC & HsepB
& Og & Ogpal & Ongp & Oc & Ocpal & Ocattr & Ocnlp & Octidx & Ob & Obpal & Obattr & Obnlp & Obtidx & HLc & HLb & HGp
& Hsp & Hsp1 & Hsp1al & H9 & Hgp & Htp & Hch & Hs0 & Vtidx & Rtidx & Vsb & Vbfp & H26 & H27 & H21 & H22).
Definition tin_stmt (m : nat) : Prop :=
forall (c : Z) W (regs : bvmap 5 word) memc mdc sp0 sp1 FP ly S W0 mem0 md0 lyc Sc k fpos ch1
(pt npt p bimg Nb idx g cfp bfp tidx : Z) (gvals cvals bvals : list Z) (gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx : Z),
c <= Z.of_nat m -> 1 <= c <= 65535 ->
tin_ctx W regs memc mdc sp0 sp1 FP ly S W0 mem0 md0 lyc Sc k fpos ch1 pt npt bimg Nb g cfp bfp tidx gvals cvals bvals gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx ->
pt <= p -> p + c <= pt + npt -> 0 <= idx -> idx + c <= Nb ->
getr regs 6 = Z_to_bv 64 SB -> getr regs 23 = Z_to_bv 64 p -> getr regs 18 = Z_to_bv 64 p -> getr regs 20 = Z_to_bv 64 c -> getr regs 24 = Z_to_bv 64 idx ->
SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + 0x220c)) memc (seg_rom SEGS)) mdc)
(tin_post W regs memc sp0 sp1 FP ly S W0 mem0 md0 lyc Sc k fpos pt npt).
Ltac tin_prelude HJ :=
pose proof pa_wx as Hwx; pose proof pa_segs_low as Hsegs;
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5);
pose proof (proj1 HJ) as HAR;
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSpres & Hstk & _);
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2);
assert (FFS : TFLUSH_STK = 17440) by reflexivity; assert (WS : TCMP_STK = 4112) by reflexivity; assert (Hes : ESTACK = 4096) by reflexivity.
Definition TCTX_REGS : list (bv 5) := [2; 3; 4; 8; 9; 21; 22; 26; 27]%bv.
Ltac tctx_regs_of HK := let r := fresh "r" in let Hr := fresh "Hr" in
intros r Hr; apply HK; cbv [TCTX_REGS In] in Hr; repeat (destruct Hr as [<- | Hr]; [reflexivity|]); destruct Hr.
Lemma tin_ctx_kept : forall W (regs regsN : bvmap 5 word) memc mdc memN mdN sp0 sp1 FP ly S W0 mem0 md0 lyc Sc k fpos ch1
pt npt bimg Nb g cfp bfp tidx gvals cvals bvals gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx slo shi,
tin_ctx W regs memc mdc sp0 sp1 FP ly S W0 mem0 md0 lyc Sc k fpos ch1 pt npt bimg Nb g cfp bfp tidx gvals cvals bvals gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx ->
ajournal SEGS B TFLUSH_STK sp0 FP ly S W0 mem0 md0 [(2, fpos)] lyc Sc W memN mdN k ->
acall_kept SEGS B lyc Sc W memc W memN slo shi (fun a => pt <= a < pt + npt) -> sp1 <= shi <= sp1 + 232 ->
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
split; [exact (QS 26%bv ltac:(cbv; tauto) _ H26)|]. split; [exact (QS 27%bv ltac:(cbv; tauto) _ H27)|]. split; [exact (QS 21%bv ltac:(cbv; tauto) _ H21) | exact (QS 22%bv ltac:(cbv; tauto) _ H22)].
Qed.
End TL.
End f.
End d.
