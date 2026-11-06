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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YI02 YI01 YI03 YI04 YI06 YC2v.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YC04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YI1i.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB0z YC19 YF8z YC1d YC1a YC2o YC0x YC17 YC1b YC2u YC1z YC1y.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Lemma achain_raise : forall ly rd sp sp' v ch, achain ly rd sp v ch -> sp' + 16 <= v -> achain ly rd sp' v ch.
Proof.
intros ly rd sp sp' v ch [H | (H1 & H2 & H3 & H4 & H5)] Hle; [left; exact H|]. right.
split; [exact Hle|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|].
pose proof (fpchain_fps_increase _ _ _ _ H4) as Hf. eapply Forall_impl; [|exact Hf]. intros r Hr. cbn beta in Hr. lia.
Qed.
Lemma val_mem_frame : forall E rs (m m' : word -> option byte) a n v,
frame_of E rs m m' -> (forall k, 0 <= k < Z.of_nat n -> ~ in_wrange E rs (a + k)) -> 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
val_mem trasegs m a n v -> val_mem trasegs m' a n v.
Proof.
intros E rs m m' a n v HF Hout Ha Han Hv kk Hkk. rewrite <- (Hv kk Hkk). unfold mbyte.
rewrite (HF (Z_to_bv 64 (a + Z.of_nat kk))); [reflexivity|]. rewrite unsigned_lit_small by lia. apply Hout. lia.
Qed.
Lemma mod16_mod8 : forall x, x mod 16 = 0 -> x mod 8 = 0.
Proof.
intros x H. pose proof (Z.div_mod x 16 ltac:(lia)) as D. rewrite H, Z.add_0_r in D. rewrite D.
replace (16 * (x / 16)) with ((2 * (x / 16)) * 8) by lia. apply Z_mod_mult.
Qed.
Lemma st_ok_pin_rege : forall E ss ms (r : bv 5) e,
st_ok trasegs E ss ms -> r <> 0%bv -> sv_denot E e = getr (ms_regs ms) r ->
st_ok trasegs E (mkSS (ss_pc ss) (sr_set (ss_regs ss) r e) (ss_mem ss) (ss_resv ss) (ss_facts ss)) ms.
Proof.
intros E ss ms r e HS Hr He.
apply (st_ok_regs trasegs E ss ms (sr_set (ss_regs ss) r e)); [exact HS|].
intros x. destruct (base.decide (x = r)) as [->|Hne].
- rewrite sr_get_set_same; [| destruct (bv_eqb r 0) eqn:Hb; [apply bv_eqb_eq in Hb; congruence | reflexivity]].
rewrite He. exact (st_ok_reg trasegs E ss ms r HS).
- rewrite sr_get_set_other by exact Hne. reflexivity.
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
Section TL.
Variable B : asyms.
Hypothesis TL : TraLib B.
Hypothesis LAWS : AR_laws trasegs B.
Hypothesis TCMP : tcmp_spec B.

Lemma acall_kept_trans : forall lyc Sc W m0 m1 m2 slo shi (Er : Z -> Prop),
acall_kept trasegs B lyc Sc W m0 W m1 slo shi Er -> acall_kept trasegs B lyc Sc W m1 W m2 slo shi Er ->
acall_kept trasegs B lyc Sc W m0 W m2 slo shi Er.
Proof.
intros lyc Sc W m0 m1 m2 slo shi Er (A1 & A2 & A3 & A4 & A5 & A6) (K1 & K2 & K3 & K4 & K5 & K6).
split; [intros a Ha Hs; rewrite (K1 a Ha Hs); exact (A1 a Ha Hs)|].
split; [intros b m i Hb Hi Hn; rewrite (K2 b m i Hb Hi Hn); exact (A2 b m i Hb Hi Hn)|].
split; [intros a H1 H2 H3; rewrite (K3 a H1 H2 H3); exact (A3 a H1 H2 H3)|].
split; [intros cid pos a Hf Hz Hn; rewrite (K4 cid pos a Hf Hz Hn); exact (A4 cid pos a Hf Hz Hn)|].
split; [intros a Ha Hs Hp; exact (K5 a Ha Hs (A5 a Ha Hs Hp)) | exact K6].
Qed.
Lemma acall_kept_band : forall lyc Sc W m0 m1 slo shi slo' shi' (Er : Z -> Prop),
acall_kept trasegs B lyc Sc W m0 W m1 slo shi Er -> slo' <= slo -> shi <= shi' ->
(forall a, slo' <= a < shi' -> apresent (w_H W) m1 a) ->
acall_kept trasegs B lyc Sc W m0 W m1 slo' shi' Er.
Proof.
intros lyc Sc W m0 m1 slo shi slo' shi' Er (K1 & K2 & K3 & K4 & K5 & K6) H1 H2 Hp.
split; [intros a Ha Hs; apply K1; [exact Ha | lia]|]. split; [exact K2|]. split; [exact K3|]. split; [exact K4|].
split; [intros a Ha Hs Hq; apply K5; [exact Ha | lia | exact Hq] | exact Hp].
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma acall_kept_of_run : forall E rs lyc Sc W (m m' : word -> option byte) md slo shi (Er : Z -> Prop),
AR trasegs B lyc Sc W m md ->
frame_of E rs (mrestrict (w_H W) m) (mrestrict (w_H W) m') ->
mem_grows (mrestrict (w_H W) m) (mrestrict (w_H W) m') ->
(forall a, in_wrange E rs a -> Er a \/ (slo <= a < shi)) ->
(forall a, Er a -> a < alloc_ceiling /\ off_img a 1) -> alloc_ceiling <= slo ->
(forall a, slo <= a < shi -> apresent (w_H W) m a) ->
acall_kept trasegs B lyc Sc W m W m' slo shi Er.
Proof.
intros E rs lyc Sc W m m' md slo shi Er HAR HFr HG Hwr HEr Hslo Hband.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (KO : forall a, 0 <= a < 2 ^ 64 -> ~ Er a -> ~ (slo <= a < shi) -> aview trasegs (w_H W) m' a = aview trasegs (w_H W) m a).
{ intros a Ha He Hs. apply (aview_kept_out E rs _ m m' HFr a Ha). intros Hw. destruct (Hwr a Hw) as [X | X]; [exact (He X) | exact (Hs X)]. }
split.
{ intros a Ha Hs. apply KO; [lia | intros He; pose proof (HEr a He) as [He1 _]; lia | exact Hs]. }
split.
{ intros b n i Hb Hi Hn. destruct (al_blocks _ _ LAWS _ _ _ _ _ b n HAR Hb) as (_ & Hb4096 & Hbceil & _).
apply KO; [lia | exact Hn | lia]. }
split.
{ intros a Him _ _. pose proof (tra_segs_low a Him) as Hl. pose proof (tra_img_range a Him) as Hl2. apply KO; [unfold kLowMemEnd in Hl; lia | intros He; pose proof (HEr a He) as [_ He2]; unfold off_img in He2; clear - He2 Hl2; lia | unfold kLowMemEnd in Hl; ceil; lia]. }
split.
{ intros cid pos a Hf Hz Hn. destruct (frames_bounds trasegs B LAWS _ _ _ _ _ cid pos HAR Hf) as (Hf4096 & Hfceil & Hfhigh).
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
(K : alayout -> astate -> world trasegs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
ajournal trasegs B STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k ->
spZ regsc = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 0 <= STK1 -> STK1 - o <= STK ->
getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
getr regsc 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
achain lyc (aview trasegs (w_H W) memc) (sp0 + o) (s0Z regsc) ch1 ->
(afn_pre trasegs B STK1 lyc Sc W regsc memc mdc ch1 ->
SRr trasegs W (mkCfg (mkst regsc pc memc (seg_rom trasegs)) mdc)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom trasegs)) md2 /\
ajournal trasegs B STK1 (spZ regsc) FP1 lyc Sc W memc mdc [] ly2 S2 W2 mem2 md2 EV1 /\
aregs_preserved regsc regs2 /\ K ly2 S2 W2 regs2 mem2 md2)) ->
(forall a, inFP FP1 a -> (inFP FP a /\ exists b n, In (b, n) (ablocks B lyc Sc) /\ b <= a < b + req_size n) \/
in_tmp_block (ablocks B ly S) (ablocks B lyc Sc) a) ->
SRr trasegs W (mkCfg (mkst regsc pc memc (seg_rom trasegs)) mdc)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom trasegs)) md2 /\
ajournal trasegs B STK sp0 FP ly S W0 mem md own ly2 S2 W2 mem2 md2 (k + EV1) /\
ajournal trasegs B STK1 (sp0 + o) FP1 lyc Sc W memc mdc [] ly2 S2 W2 mem2 md2 EV1 /\
aregs_preserved regsc regs2 /\ K ly2 S2 W2 regs2 mem2 md2).
Proof.
intros W regsc memc pc STK sp0 FP ly S W0 mem md own lyc Sc mdc k STK1 FP1 EV1 o raw ch1 K
HJ Hsp' Hal Hneg Hstk1 Hbud Hgp Htp Hra Hraw Hra4 Hch Hcallee HF.
eapply SRr_mono.
{ apply Hcallee. eapply (afn_pre_at trasegs B STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k regsc STK1 o ch1);
try eassumption. - rewrite Hra. exact Hraw. - unfold raZ. rewrite Hra. exact Hra4. - rewrite Hsp'. exact Hch. }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ1 & HP & HK).
exists ly2, S2, regs2, mem2, md2. split; [reflexivity|]. rewrite Hsp' in HJ1.
split; [| split; [exact HJ1 | split; [exact HP | exact HK]]].
change own with ([] ++ own). eapply (ajournal_sub trasegs B LAWS tra_segs_low); [exact HJ | exact HJ1 | lia | lia | exact HF].
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
Definition tin_loc : YQ0b.region :=
YQ0b.mkRegion (Some 9%nat) 232 256 232 232
[YQ0b.mkChunk 232 (CVal 8 (SOff 32 0)); YQ0b.mkChunk 240 (CVal 8 (SOff 6 0)); YQ0b.mkChunk 248 (CVal 8 (SOff 33 0))].
Definition tin_tmp : YQ0b.region := YQ0b.mkRegion (Some 23%nat) 0 1 0 1 [YQ0b.mkChunk 0 (CVal 1 (SOff 34 0))].
Definition tin_facts : facts :=
mkFacts [ (9%nat, mkAF 70368744177664 140737488355328 4); (6%nat, mkAF SB SB 0); (23%nat, HPTR 0); (20%nat, mkAF 1 65535 0);
(24%nat, mkAF 0 4294967295 0); (26%nat, HPTR 0); (21%nat, HPTR 4); (22%nat, HPTR 3); (33%nat, HPTR 3); (34%nat, mkAF 0 255 0) ] [] [].
Definition ss_tin : sstate := mkSS 0x877dc tin_regs [tin_loc; tin_tmp] None tin_facts.
Definition ttl_loc : YQ0b.region := YQ0b.mkRegion (Some 9%nat) 240 248 240 240 [YQ0b.mkChunk 240 (CVal 8 (SOff 32 0))].
Definition ttl_facts : facts := mkFacts [ (20%nat, mkAF 1 65535 0); (23%nat, HPTR 0); (24%nat, mkAF 0 4294967295 0); (32%nat, mkAF SB SB 0) ] [] [].
Definition ss_ttl : sstate := mkSS 0x87830 (sr_set sr_atoms 18%bv (SOff 23 0)) [ttl_loc] None ttl_facts.
Lemma val_mem_byte1 : forall (H : word -> bool) (m : word -> option byte) a,
apresent H m a -> exists v, 0 <= v < 256 /\ val_mem trasegs (mrestrict H m) a 1 v.
Proof.
intros H m a [Hh [b Hb]]. exists (bv_unsigned b). pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. cbn [Z.of_N] in R. change (2 ^ 8) with 256 in R.
split; [lia|]. intros k Hk. destruct k; [|lia]. cbn [Z.of_nat]. rewrite Z.add_0_r. unfold mbyte, mrestrict. rewrite Hh. cbn. rewrite Hb. f_equal.
unfold YP0g.le_byte. change (8 * Z.of_nat 0) with 0. change (2 ^ (8 * Z.of_nat 1)) with 256.
rewrite Z.shiftr_0_r. rewrite (Z.mod_small (bv_unsigned b) 256) by lia. rewrite (Z.mod_small (bv_unsigned b) 256) by lia.
symmetry. apply Z_to_bv_bv_unsigned.
Qed.
Lemma obj_at_keptK : forall lyc Sc W (m m' : word -> option byte) slo shi (Er : Z -> Prop) b sz lay vals,
acall_kept trasegs B lyc Sc W m W m' slo shi Er -> In (b, sz) (ablocks B lyc Sc) ->
lay_inside lay (req_size sz) = true -> (forall i, 0 <= i < req_size sz -> ~ Er (b + i)) ->
obj_at trasegs (mrestrict (w_H W) m) b lay vals -> obj_at trasegs (mrestrict (w_H W) m') b lay vals.
Proof.
intros lyc Sc W m m' slo shi Er b sz lay vals (_ & K2 & _) Hin Hlay HnE Hobj.
eapply (obj_at_transport_range trasegs); [exact Hobj | exact Hlay |]. intros i Hi. apply (mbyte_of_aview trasegs). exact (K2 b sz i Hin Hi (HnE i Hi)).
Qed.
Lemma val_mem_keptK : forall lyc Sc W (m m' : word -> option byte) slo shi (Er : Z -> Prop) a n v,
acall_kept trasegs B lyc Sc W m W m' slo shi Er -> alloc_ceiling <= a -> a + Z.of_nat n <= 2 ^ 64 -> (shi <= a \/ a + Z.of_nat n <= slo) ->
val_mem trasegs (mrestrict (w_H W) m) a n v -> val_mem trasegs (mrestrict (w_H W) m') a n v.
Proof.
intros lyc Sc W m m' slo shi Er a n v (K1 & _) Ha Han Hs Hv kk Hkk. rewrite <- (Hv kk Hkk). apply (mbyte_of_aview trasegs). apply K1; lia.
Qed.
Lemma achain_keptK : forall lyc Sc W (m m' : word -> option byte) slo shi (Er : Z -> Prop) sp v ch,
acall_kept trasegs B lyc Sc W m W m' slo shi Er -> achain lyc (aview trasegs (w_H W) m) sp v ch ->
shi <= sp -> alloc_ceiling <= sp -> ly_top lyc <= 2 ^ 64 -> achain lyc (aview trasegs (w_H W) m') sp v ch.
Proof.
intros lyc Sc W m m' slo shi Er sp v ch (K1 & _) Hch Hshi Hsp Htop.
eapply (achain_kept lyc _ _ sp v ch sp); [exact Hch | lia | exact Htop | intros a Ha; apply K1; lia].
Qed.
Lemma achain_keptK2 : forall lyc Sc W (m m' : word -> option byte) slo shi (Er : Z -> Prop) sp v ch,
acall_kept trasegs B lyc Sc W m W m' slo shi Er -> achain lyc (aview trasegs (w_H W) m) sp v ch ->
sp <= shi -> shi + 16 <= v -> alloc_ceiling <= shi -> ly_top lyc <= 2 ^ 64 -> achain lyc (aview trasegs (w_H W) m') sp v ch.
Proof.
intros lyc Sc W m m' slo shi Er sp v ch (K1 & _) Hch H1 H2 H3 Htop.
apply (achain_lower _ _ shi sp); [|lia].
eapply (achain_kept lyc _ _ shi v ch shi); [apply (achain_raise _ _ sp shi); [exact Hch | lia] | lia | exact Htop | intros a Ha; apply K1; lia].
Qed.
Lemma region_kept_sub_ajw : forall E lyc Sc W memc W2 mem2 slo shi (Er : Z -> Prop) n lo hi wlo whi cs x b m ly2 S2 md2,
acall_kept trasegs B lyc Sc W memc W2 mem2 slo shi Er -> AR trasegs B ly2 S2 W2 mem2 md2 -> In (b, m) (ablocks B ly2 S2) ->
bv_unsigned (ew E n) = x -> In (b, m) (ablocks B lyc Sc) -> b <= x + lo -> x + hi <= b + req_size m -> lo <= wlo -> whi <= hi ->
(forall a, x + lo <= a < x + hi -> ~ Er a) ->
region_kept trasegs E (mrestrict (w_H W) memc) (mrestrict (w_H W2) mem2) (YQ0b.mkRegion (Some n) lo hi wlo whi cs).
Proof.
intros E lyc Sc W memc W2 mem2 slo shi Er n lo hi wlo whi cs x b m ly2 S2 md2 (_ & K2 & _) HAR2 Hin2 Hn Hin Hlo Hhi Hwlo Hwhi HnE.
destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR2 Hin2) as (_ & _ & _ & _ & Hpres2 & _).
split; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi base_val]; rewrite Hn; intros a Ha.
- apply (mbyte_of_aview trasegs). replace a with (b + (a - b)) by lia. apply (K2 b m (a - b) Hin); [lia|].
replace (b + (a - b)) with a by lia. apply HnE. exact Ha.
- intros _. apply (apresent_writable trasegs). apply (proj1 (Hpres2 a ltac:(lia))).
Qed.
Ltac env_agree32 HAE :=
lazymatch goal with
| |- env_agree 32 _ (ewset ?X ?n ?v) => apply (env_agree_trans 32 _ X); [env_agree32 HAE | apply (YQ04.env_agree_le 32 n); [lia | apply env_agree_ewset]]
| |- env_agree 32 _ (havoc ?X ?n ?ws) => apply (env_agree_trans 32 _ X); [env_agree32 HAE | apply (YQ04.env_agree_le 32 n); [lia | apply env_agree_havoc]]
| |- _ => exact HAE
end.
Definition tin_post (W : world trasegs) (regs : bvmap 5 word) (memc : word -> option byte) (sp0 sp1 : Z) (FP : list (Z * Z))
(ly : alayout) (S : astate) (W0 : world trasegs) (mem0 : word -> option byte) (md0 : Model)
(lyc : alayout) (Sc : astate) (k : Z) (fpos pt npt : Z) : world trasegs -> config -> Prop :=
fun W' c' => W' = W /\ exists regs' mem' md',
c' = mkCfg (mkst regs' (Z_to_bv 64 0x87870) mem' (seg_rom trasegs)) md' /\
ajournal trasegs B TFLUSH_STK sp0 FP ly S W0 mem0 md0 [(2, fpos)] lyc Sc W mem' md' k /\
(forall r : bv 5, reg_in r TIN_CLOB = false -> getr regs' r = getr regs r) /\
getr regs' 6 = Z_to_bv 64 SB /\
acall_kept trasegs B lyc Sc W memc W mem' (sp1 - TCMP_STK) sp1 (fun a => pt <= a < pt + npt).
Definition tin_ctx (W : world trasegs) (regs : bvmap 5 word) (memc : word -> option byte) (mdc : Model) (sp0 sp1 : Z) (FP : list (Z * Z))
(ly : alayout) (S : astate) (W0 : world trasegs) (mem0 : word -> option byte) (md0 : Model) (lyc : alayout) (Sc : astate) (k : Z) (fpos : Z)
(ch1 : list (Z * Z * Z)) (pt npt bimg Nb g cfp bfp tidx : Z) (gvals cvals bvals : list Z) (gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx : Z) : Prop :=
ajournal trasegs B TFLUSH_STK sp0 FP ly S W0 mem0 md0 [(2, fpos)] lyc Sc W memc mdc k /\
In (pt, npt) (ablocks B lyc Sc) /\
(forall blc lyq ownq a, In (pt, npt) blc -> pt <= a < pt + npt -> awr_byte TFLUSH_STK sp0 FP (ablocks B ly S) blc lyq ownq a) /\
In (bimg, Nb) (ablocks B lyc Sc) /\ Nb < 2 ^ 32 /\ (pt + req_size npt <= bimg \/ bimg + req_size Nb <= pt) /\
In (g, CGIF_SIZE) (ablocks B lyc Sc) /\ In (cfp, FRAME_SIZE) (ablocks B lyc Sc) /\ In (bfp, FRAME_SIZE) (ablocks B lyc Sc) /\ cfp <> bfp /\
(pt + req_size npt <= g \/ g + 96 <= pt) /\ (pt + req_size npt <= cfp \/ cfp + 40 <= pt) /\ (pt + req_size npt <= bfp \/ bfp + 40 <= pt) /\
obj_at trasegs (mrestrict (w_H W) memc) g LAY_CGIF gvals /\ nth_error gvals CG_pal = Some gpal /\ nth_error gvals CG_ngp = Some ngp /\
obj_at trasegs (mrestrict (w_H W) memc) cfp LAY_Frame cvals /\ nth_error cvals FR_lpal = Some cpal /\ nth_error cvals FR_attr = Some cattr /\
nth_error cvals FR_nlp = Some cnlp /\ nth_error cvals FR_ctidx = Some ctidx /\
obj_at trasegs (mrestrict (w_H W) memc) bfp LAY_Frame bvals /\ nth_error bvals FR_lpal = Some bpal /\ nth_error bvals FR_attr = Some battr /\
nth_error bvals FR_nlp = Some bnlp /\ nth_error bvals FR_ctidx = Some btidx /\
(Z.land cattr 1 <> 0 -> exists Nl, In (cpal, Nl) (ablocks B lyc Sc) /\ 3 * cnlp <= Nl) /\
(Z.land battr 1 <> 0 -> exists Nl, In (bpal, Nl) (ablocks B lyc Sc) /\ 3 * bnlp <= Nl) /\
(Z.land cattr 1 = 0 \/ Z.land battr 1 = 0 -> exists Np, In (gpal, Np) (ablocks B lyc Sc) /\ 3 * ngp <= Np) /\
spZ regs = sp1 /\ sp0 - 400 <= sp1 <= sp0 - 384 /\ sp1 mod 16 = 0 /\
getr regs 9 = Z_to_bv 64 sp1 /\ getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\
achain lyc (aview trasegs (w_H W) memc) sp1 (s0Z regs) ch1 /\ s0Z regs = sp0 /\
val_mem trasegs (mrestrict (w_H W) memc) (sp1 + 232) 8 tidx /\ 0 <= tidx < 2 ^ 64 /\
val_mem trasegs (mrestrict (w_H W) memc) (sp1 + 240) 8 SB /\
val_mem trasegs (mrestrict (w_H W) memc) (sp1 + 248) 8 bfp /\
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
SRr trasegs W (mkCfg (mkst regs (Z_to_bv 64 0x877dc) memc (seg_rom trasegs)) mdc)
(tin_post W regs memc sp0 sp1 FP ly S W0 mem0 md0 lyc Sc k fpos pt npt).
Ltac tin_prelude HJ :=
pose proof Hwx_tfa as Hwx; pose proof tra_segs_low as Hsegs;
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
ajournal trasegs B TFLUSH_STK sp0 FP ly S W0 mem0 md0 [(2, fpos)] lyc Sc W memN mdN k ->
acall_kept trasegs B lyc Sc W memc W memN slo shi (fun a => pt <= a < pt + npt) -> sp1 <= shi <= sp1 + 232 ->
(forall r : bv 5, In r TCTX_REGS -> getr regsN r = getr regs r) ->
tin_ctx W regsN memN mdN sp0 sp1 FP ly S W0 mem0 md0 lyc Sc k fpos ch1 pt npt bimg Nb g cfp bfp tidx gvals cvals bvals gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx.
Proof.
intros W regs regsN memc mdc memN mdN sp0 sp1 FP ly S W0 mem0 md0 lyc Sc k fpos ch1
pt npt bimg Nb g cfp bfp tidx gvals cvals bvals gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx slo shi HCTX HJN K Hband HK.
tin_ctx_names HCTX. tin_prelude HJ.
destruct (al_blocks _ _ LAWS lyc Sc W memc mdc pt npt HAR Hpt) as (Hq16 & Hq4096 & Hqceil & Hqh_ia & _ & _ & Hnpt & _). pose proof (proj1 Hqh_ia) as Hqh.
pose proof (blk_off_img _ _ _ _ _ _ pt npt HAR Hpt) as Hqh_img.
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
Lemma fl_tin_tail : forall m, tin_stmt m ->
forall (c : Z) W (regs regsN : bvmap 5 word) memc mdc memN mdN sp0 sp1 FP ly S W0 mem0 md0 lyc Sc k fpos ch1
(pt npt p bimg Nb idx g cfp bfp tidx : Z) (gvals cvals bvals : list Z) (gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx : Z),
c - 1 <= Z.of_nat m -> 1 <= c <= 65535 ->
tin_ctx W regs memc mdc sp0 sp1 FP ly S W0 mem0 md0 lyc Sc k fpos ch1 pt npt bimg Nb g cfp bfp tidx gvals cvals bvals gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx ->
pt <= p -> p + c <= pt + npt -> 0 <= idx -> idx + c <= Nb ->
ajournal trasegs B TFLUSH_STK sp0 FP ly S W0 mem0 md0 [(2, fpos)] lyc Sc W memN mdN k ->
acall_kept trasegs B lyc Sc W memc W memN (sp1 - TCMP_STK) sp1 (fun a => pt <= a < pt + npt) ->
(forall r : bv 5, reg_in r TIN_CLOB = false -> getr regsN r = getr regs r) ->
getr regsN 23 = Z_to_bv 64 p -> getr regsN 18 = Z_to_bv 64 p -> getr regsN 20 = Z_to_bv 64 c -> getr regsN 24 = Z_to_bv 64 idx ->
SRr trasegs W (mkCfg (mkst regsN (Z_to_bv 64 0x87830) memN (seg_rom trasegs)) mdN)
(tin_post W regs memc sp0 sp1 FP ly S W0 mem0 md0 lyc Sc k fpos pt npt).
Proof.
intros m IH c W regs regsN memc mdc memN mdN sp0 sp1 FP ly S W0 mem0 md0 lyc Sc k fpos ch1
pt npt p bimg Nb idx g cfp bfp tidx gvals cvals bvals gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx
Hm Hcnt HCTX Hp1 Hp2 Hidx1 Hidx2 HJN K HK N23 N24 N20 N18.
pose proof HCTX as HCTX0. tin_ctx_names HCTX.
tin_prelude HJN. pose proof HJN as HJN0.
assert (HSpresN : forall a, sp1 - TCMP_STK <= a < sp1 -> apresent (w_H W) memN a) by (intros a Ha; apply HSpres; lia).
destruct (al_blocks _ _ LAWS lyc Sc W memN mdN pt npt HAR Hpt) as (Hq16 & Hq4096 & Hqceil & Hqh_ia & Hqpres & _ & Hnpt & _). pose proof (proj1 Hqh_ia) as Hqh.
pose proof (blk_off_img _ _ _ _ _ _ pt npt HAR Hpt) as Hqh_img.
pose proof (req_size_pos' npt ltac:(lia)) as [_ Hrnp]. pose proof (req_size_pos' Nb ltac:(lia)) as [_ HrNb].
assert (N9 : getr regsN 9 = Z_to_bv 64 sp1) by (rewrite (HK 9%bv eq_refl); exact H9).
assert (N2 : spZ regsN = sp1) by (unfold spZ; rewrite (HK 2%bv eq_refl); exact Hsp).
pose proof (val_mem_keptK _ _ _ _ _ _ _ _ (sp1 + 240) 8 SB K ltac:(lia) ltac:(cbn [Z.of_nat]; lia) ltac:(left; lia) Vsb) as VsbN.
remember (Ereg regsN [Z_to_bv 64 SB]) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regsN [Z_to_bv 64 SB]) E) by (rewrite HE; apply env_agree_refl).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regsN r) by (intros n r Hn; subst E; apply ew_Ereg_nat; exact Hn).
pose proof (EE 9%nat 9%bv eq_refl) as E9. rewrite N9 in E9. pose proof (EE 23%nat 23%bv eq_refl) as E23. rewrite N23 in E23.
pose proof (EE 20%nat 20%bv eq_refl) as E20. rewrite N20 in E20. pose proof (EE 24%nat 24%bv eq_refl) as E18. rewrite N18 in E18.
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; exact (ew_Ereg_extra regsN _ 0)).
assert (HS : st_ok trasegs E ss_ttl (restrict (w_H W) (mkst regsN (Z_to_bv 64 0x87830) memN (seg_rom trasegs)))).
{ rewrite restrict_mkst_fx. unfold ss_ttl.
apply (rn_st_ok_any E 0x87830 _ regsN _ _ (mrestrict (w_H W) memN)).
- subst E. apply regs_ok_pin; [apply regs_ok_Ereg | intros X; discriminate X | rewrite N24; cbn [sv_denot]; rewrite (ew_Ereg_nat regsN _ 23 23%bv eq_refl), N23, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity].
- reflexivity.
- apply Forall_cons; [|apply Forall_nil]. unfold region_ok, ttl_loc; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val].
rewrite E9, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil]. apply (chunk_ok_val trasegs E _ sp1 240 8 _ SB); [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | unfold SB; zside | exact VsbN].
- cbn [pairwise_disjoint all_disjoint]. repeat split.
- split; [|split; exact I]. cbn [ttl_facts f_atoms atoms_ok]. unfold afact_ok, HPTR. cbn [af_lo af_hi af_al2].
rewrite E20, E23, E18, E32, !unsigned_lit_small by (unfold SB; lia). rewrite !Z.pow_0_r, !Z.mod_1_r.
rewrite ?C3 in *. unfold SB. repeat match goal with |- _ /\ _ => split end; lia. }
clear HE. pose proof HS as HS0.
shok_auto SHOK (SOff 6 0) E (mrestrict (w_H W) memN).
aj_run_tok tratbl_lib_ok HS HJN SHOK FLBspan.
1: { apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
rename HFr into HFra. rename HG into HGa. clear HF.
pose proof (acall_kept_of_run E _ lyc Sc W memN _ mdN (sp1 - TCMP_STK) sp1 (fun a => pt <= a < pt + npt) (proj1 HJN0) HFra HGa
ltac:(unfold ss_ttl, ttl_loc; cbn [ss_mem]; intros a (r & Hr & Hw); cbn [In] in Hr; destruct Hr as [<- | []]; cbn [YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi base_val] in Hw; lia)
ltac:(intros a Ha; cbn beta in Ha; split; [lia | pose proof (req_size_pos0 npt ltac:(lia)) as [_ Hrqa]; clear - Ha Hqh_img Hrqa; unfold off_img in *; lia]) ltac:(lia) ltac:(intros a Ha; apply HSpresN; lia)) as Ka.
srr_branch_tok tratbl_lib_ok HS SHOK FLBspan.
-
rewrite branch_eq_U in Hc. rewrite (U_atom_off _ 20 c (-1)) in Hc by (first [exact E20 | lia]). rewrite U_lit in Hc by lia. apply Z.eqb_eq in Hc.
reshok_bx HS 6%nat. pose proof (proj1 HJN) as HARb.
aj_run_to_tok tratbl_lib_ok HS HJN SHOK FLBspan 0x87870.
1: { apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
rename HFr into HFrc. rename HG into HGc. clear HF.
pose proof (acall_kept_of_run _ _ lyc Sc W _ _ _ (sp1 - TCMP_STK) sp1 (fun a => pt <= a < pt + npt) HARb HFrc HGc
ltac:(unfold ss_ttl, ttl_loc; cbn [ss_mem]; intros a (r & Hr & Hw); cbn [In] in Hr; destruct Hr as [<- | []]; cbn [YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi base_val] in Hw; lia)
ltac:(intros a Ha; cbn beta in Ha; split; [lia | pose proof (req_size_pos0 npt ltac:(lia)) as [_ Hrqa]; clear - Ha Hqh_img Hrqa; unfold off_img in *; lia]) ltac:(lia) ltac:(intros a Ha; pose proof Ka as (_ & _ & _ & _ & _ & K6); apply K6; lia)) as Kc.
pose proof (regs_kept_of_st_ok trasegs _ _ _ regsN _ TIN_KEPT27 HS ltac:(env_agree32 HAE) ltac:(vm_compute; reflexivity)) as HKr. cbn [ms_regs restrict] in HKr.
rreg HS (6%bv : bv 5) R6. rewrite ?ew_ewset_other in R6 by lia. rewrite E32 in R6.
rewrite (st_ok_restrict_mkst trasegs _ _ _ _ HS eq_refl). cbn [ss_pc].
apply SRr_ret. split; [reflexivity|].
lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] => exists (ms_regs msx), (ms_mem msx), mdx end.
split; [reflexivity|]. split; [exact HJN|].
split; [intros r Hr; transitivity (getr regsN r); [destruct (tin_clob_cases r Hr) as [-> | Hr']; [cbn [ms_regs]; rewrite (st_ok_reg trasegs _ _ _ 0%bv HS), (st_ok_reg trasegs _ _ _ 0%bv HS0); reflexivity | exact (HKr r Hr')] | exact (HK r Hr)]|].
split; [exact R6|].
eapply acall_kept_trans; [exact K | eapply acall_kept_trans; [exact Ka | exact Kc]].
-
rewrite branch_eq_U in Hc. rewrite (U_atom_off _ 20 c (-1)) in Hc by (first [exact E20 | lia]). rewrite U_lit in Hc by lia. apply Z.eqb_neq in Hc.
reshok_bx HS 6%nat. pose proof (proj1 HJN) as HARb.
aj_run_to_tok tratbl_lib_ok HS HJN SHOK FLBspan 0x877dc.
1: { apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
rename HFr into HFrb. rename HG into HGb. clear HF.
pose proof (acall_kept_of_run _ _ lyc Sc W _ _ _ (sp1 - TCMP_STK) sp1 (fun a => pt <= a < pt + npt) HARb HFrb HGb
ltac:(unfold ss_ttl, ttl_loc; cbn [ss_mem]; intros a (r & Hr & Hw); cbn [In] in Hr; destruct Hr as [<- | []]; cbn [YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi base_val] in Hw; lia)
ltac:(intros a Ha; cbn beta in Ha; split; [lia | pose proof (req_size_pos0 npt ltac:(lia)) as [_ Hrqa]; clear - Ha Hqh_img Hrqa; unfold off_img in *; lia]) ltac:(lia) ltac:(intros a Ha; pose proof Ka as (_ & _ & _ & _ & _ & K6); apply K6; lia)) as Kb.
pose proof (acall_kept_trans _ _ _ _ _ _ _ _ _ K (acall_kept_trans _ _ _ _ _ _ _ _ _ Ka Kb)) as Kab.
pose proof (regs_kept_of_st_ok trasegs _ _ _ regsN _ TIN_KEPT27 HS ltac:(env_agree32 HAE) ltac:(vm_compute; reflexivity)) as HKr. cbn [ms_regs restrict] in HKr.
assert (HK2 : forall r : bv 5, reg_in r TIN_CLOB = false -> getr (ms_regs ms0) r = getr regs r).
{ intros r Hr. transitivity (getr regsN r); [|exact (HK r Hr)].
destruct (tin_clob_cases r Hr) as [-> | Hr']; [rewrite (st_ok_reg trasegs _ _ _ 0%bv HS), (st_ok_reg trasegs _ _ _ 0%bv HS0); reflexivity | exact (HKr r Hr')]. }
rreg HS (6%bv : bv 5) R6. rreg HS (23%bv : bv 5) R23. rreg HS (18%bv : bv 5) R24. rreg HS (20%bv : bv 5) R20. rreg HS (24%bv : bv 5) R18.
rewrite (st_ok_restrict_mkst trasegs _ _ _ _ HS eq_refl). cbn [ss_pc].
lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem _) _) ?mdX) _ =>
pose proof (tin_ctx_kept W regs (ms_regs msX) memc mdc (ms_mem msX) mdX sp0 sp1 FP ly S W0 mem0 md0 lyc Sc k fpos ch1
pt npt bimg Nb g cfp bfp tidx gvals cvals bvals gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx _ _ HCTX0 HJN Kab ltac:(lia) ltac:(tctx_regs_of HK2)) as HCTX2 end.
eapply SRr_mono.
{ unfold tin_stmt in IH. eapply (IH (c - 1) _ _ _ _ sp0 sp1 FP ly S W0 mem0 md0 lyc Sc k fpos ch1 pt npt (p + 1) bimg Nb (idx + 1) g cfp bfp tidx);
[ lia | lia | exact HCTX2 | lia | lia | lia | lia
| rewrite R6, ?ew_ewset_other by lia; exact E32
| rewrite R23, ?ew_ewset_other by lia; rewrite E23, unsigned_lit_small by lia; reflexivity
| rewrite R24, ?ew_ewset_other by lia; rewrite E23, unsigned_lit_small by lia; reflexivity
| rewrite R20, ?ew_ewset_other by lia; rewrite E20, unsigned_lit_small by lia; f_equal; lia
| rewrite R18, ?ew_ewset_other by lia; rewrite E18, unsigned_lit_small by lia; reflexivity ]. }
cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HK3 & H63 & K3).
split; [reflexivity|]. exists regs3, mem3, md3. split; [reflexivity|]. split; [exact HJ3|].
split; [intros r Hr; rewrite (HK3 r Hr); exact (HK2 r Hr)|]. split; [exact H63|].
eapply acall_kept_trans; [exact Kab | exact K3].
Qed.
Lemma fl_tin_step : forall m, tin_stmt m -> tin_stmt (S m).
Proof.
intros m IH. unfold tin_stmt.
intros c W regs memc mdc sp0 sp1 FP ly S W0 mem0 md0 lyc Sc k fpos ch1
pt npt p bimg Nb idx g cfp bfp tidx gvals cvals bvals gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx
Hm Hcnt HCTX Hp1 Hp2 Hidx1 Hidx2 H6 H23 H24 H20 H18.
pose proof HCTX as HCTX0. tin_ctx_names HCTX.
tin_prelude HJ. pose proof HJ as HJ0.
assert (HSpres1 : forall a, sp1 - TCMP_STK <= a < sp1 -> apresent (w_H W) memc a) by (intros a Ha; apply HSpres; lia).
destruct (al_blocks _ _ LAWS lyc Sc W memc mdc pt npt HAR Hpt) as (Hq16 & Hq4096 & Hqceil & Hqh_ia & Hqpres & _ & Hnpt & _). pose proof (proj1 Hqh_ia) as Hqh.
pose proof (blk_off_img _ _ _ _ _ _ pt npt HAR Hpt) as Hqh_img.
destruct (al_blocks _ _ LAWS lyc Sc W memc mdc bimg Nb HAR Hbi) as (Hi16 & Hi4096 & Hiceil & Hih_ia & Hipres & _). pose proof (proj1 Hih_ia) as Hih.
pose proof (blk_off_img _ _ _ _ _ _ bimg Nb HAR Hbi) as Hih_img.
destruct (al_blocks _ _ LAWS lyc Sc W memc mdc g CGIF_SIZE HAR Hg) as (Hg16 & Hg4096 & Hgceil & Hgh_ia & Hgpres & _). pose proof (proj1 Hgh_ia) as Hgh.
pose proof (blk_off_img _ _ _ _ _ _ g CGIF_SIZE HAR Hg) as Hgh_img.
destruct (al_blocks _ _ LAWS lyc Sc W memc mdc cfp FRAME_SIZE HAR Hcf) as (Hc16 & Hc4096 & Hcceil & Hcfh_ia & Hcpres & _). pose proof (proj1 Hcfh_ia) as Hcfh.
pose proof (blk_off_img _ _ _ _ _ _ cfp FRAME_SIZE HAR Hcf) as Hcfh_img.
destruct (al_blocks _ _ LAWS lyc Sc W memc mdc bfp FRAME_SIZE HAR Hbf) as (Hb16 & Hb4096 & Hbceil & Hbfh_ia & Hbpres & _). pose proof (proj1 Hbfh_ia) as Hbfh.
pose proof (blk_off_img _ _ _ _ _ _ bfp FRAME_SIZE HAR Hbf) as Hbfh_img.
change (req_size CGIF_SIZE) with 96 in *. change (req_size FRAME_SIZE) with 40 in *.
pose proof (req_size_pos' npt ltac:(lia)) as [_ Hrnp]. pose proof (req_size_pos' Nb ltac:(lia)) as [_ HrNb].
pose proof (proj1 (proj2 HJ)) as HLY. destruct HLY as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
destruct (val_mem_byte1 (w_H W) memc p (proj1 (Hqpres p ltac:(lia)))) as (vb & Rvb & Vvb).
remember (Ereg regs [Z_to_bv 64 tidx; Z_to_bv 64 bfp; Z_to_bv 64 vb]) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs [Z_to_bv 64 tidx; Z_to_bv 64 bfp; Z_to_bv 64 vb]) E) by (rewrite HE; apply env_agree_refl).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r) by (intros n r Hn; subst E; apply ew_Ereg_nat; exact Hn).
pose proof (EE 9%nat 9%bv eq_refl) as E9. rewrite H9 in E9. pose proof (EE 6%nat 6%bv eq_refl) as E6. rewrite H6 in E6.
pose proof (EE 23%nat 23%bv eq_refl) as E23. rewrite H23 in E23. pose proof (EE 20%nat 20%bv eq_refl) as E20. rewrite H20 in E20.
pose proof (EE 24%nat 24%bv eq_refl) as E18. rewrite H18 in E18. pose proof (EE 26%nat 26%bv eq_refl) as E26. rewrite H26 in E26.
pose proof (EE 21%nat 21%bv eq_refl) as E21. rewrite H21 in E21. pose proof (EE 22%nat 22%bv eq_refl) as E22. rewrite H22 in E22.
pose proof (EE 1%nat 1%bv eq_refl) as E1. pose proof (EE 2%nat 2%bv eq_refl) as E2. pose proof (EE 3%nat 3%bv eq_refl) as E3.
pose proof (EE 4%nat 4%bv eq_refl) as E4. pose proof (EE 8%nat 8%bv eq_refl) as E8.
assert (E32 : ew E 32 = Z_to_bv 64 tidx) by (subst E; exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 bfp) by (subst E; exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 vb) by (subst E; exact (ew_Ereg_extra regs _ 2)).
assert (Usp : bv_unsigned (ew E 2) = sp1) by (rewrite E2; exact Hsp).
assert (HS : st_ok trasegs E ss_tin (restrict (w_H W) (mkst regs (Z_to_bv 64 0x877dc) memc (seg_rom trasegs)))).
{ rewrite restrict_mkst_fx. unfold ss_tin, tin_regs.
apply (rn_st_ok_any E 0x877dc _ regs _ _ (mrestrict (w_H W) memc)).
- subst E. apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_Ereg | intros X; discriminate X | rewrite H24; cbn [sv_denot]; rewrite (ew_Ereg_nat regs _ 23 23%bv eq_refl), H23, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity] | intros X; discriminate X |].
rewrite H27. cbn [sv_denot]. reflexivity.
- reflexivity.
- apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold region_ok, tin_loc, tin_tmp; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val].
+ rewrite E9, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [apply (chunk_ok_val trasegs E _ sp1 232 8 _ tidx); [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Vtidx]|].
apply Forall_cons; [apply (chunk_ok_val trasegs E _ sp1 240 8 _ SB); [cbn [sv_denot]; rewrite E6, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | unfold SB; zside | exact Vsb]|].
apply Forall_cons; [apply (chunk_ok_val trasegs E _ sp1 248 8 _ bfp); [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Vbfp]|].
apply Forall_nil.
+ rewrite E23, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; apply (apresent_writable trasegs); apply (proj1 (Hqpres (p + o) ltac:(lia)))|].
apply Forall_cons; [|apply Forall_nil]. apply (chunk_ok_val trasegs E _ p 0 1 _ vb); [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | rewrite Z.add_0_r; exact Vvb].
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint, tin_loc, tin_tmp. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val].
rewrite E9, E23, !unsigned_lit_small by lia. repeat split. lia.
- split; [|split; exact I]. cbn [tin_facts f_atoms atoms_ok]. unfold afact_ok, HPTR. cbn [af_lo af_hi af_al2].
rewrite E9, E6, E23, E20, E18, E26, E21, E22, E33, E34, !unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
rewrite ?C3 in *. unfold SB. repeat match goal with |- _ /\ _ => split end; try (apply mod16_mod8; assumption);
first [lia | match goal with |- ?g => idtac "FACT-LEFT" g end]. }
clear HE. pose proof HS as HS0.
shok_auto SHOK (SOff 6 0) E (mrestrict (w_H W) memc).
aj_run_to_tok tratbl_lib_ok HS HJ SHOK FLBspan 0x877f4.
all: try (lazymatch goal with |- range_addressable _ (U ?Ex _) (U _ (SOff 23 ?cc)) ?len =>
first [rewrite (U_atom_off Ex 23 p cc E23) by lia | rewrite (U_atom Ex 23 p E23) by lia];
eapply (obl_of_block trasegs _ LAWS _ _ _ _ _ Ex (SOff 6 0) _ len pt npt (proj1 HJ) Hpt); [rewrite (U_atom Ex 6 SB E6); [reflexivity | unfold SB; lia] | lia | lia] end).
1: { apply awr_ok_cons_ro; [cbn; lia|].
eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 23%nat); [reflexivity | rewrite E23; apply unsigned_lit_small; lia | intros a Ha; unfold tin_tmp in Ha; cbn [YQ0b.r_wlo YQ0b.r_whi] in Ha; apply (Hpawr (ablocks B lyc Sc)); [exact Hpt | clear - Ha Hp1 Hp2 Hcnt; lia] | apply awr_ok_nil]. }
rename HFr into HFr1. rename HG into HG1. clear HF.
pose proof (acall_kept_of_run E _ lyc Sc W memc _ mdc (sp1 - TCMP_STK) sp1 (fun a => pt <= a < pt + npt) HAR HFr1 HG1
ltac:(unfold ss_tin, tin_loc, tin_tmp; cbn [ss_mem]; intros a (r & Hr & Hw); cbn [In] in Hr; destruct Hr as [<- | [<- | []]]; cbn [YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi base_val] in Hw;
[lia | rewrite E23, unsigned_lit_small in Hw by lia; left; lia])
ltac:(intros a Ha; cbn beta in Ha; split; [lia | pose proof (req_size_pos0 npt ltac:(lia)) as [_ Hrqa]; clear - Ha Hqh_img Hrqa; unfold off_img in *; lia]) ltac:(lia) HSpres1) as K1.
assert (Hbx : bimg <= bimg + idx < bimg + req_size Nb) by lia.
destruct (val_mem_byte1 (w_H W) _ (bimg + idx) (proj1 (Hipres (bimg + idx) Hbx))) as (vbb & Rvbb & Vvbb0).
lazymatch type of HS with st_ok _ ?E1 ?ssv ?msv =>
assert (F26 : ew E1 26 = Z_to_bv 64 bimg) by (cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E26);
assert (F18 : ew E1 24 = Z_to_bv 64 idx) by (cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E18);
rreg_by HS (10%bv : bv 5) (Z_to_bv 64 (bimg + idx)) (denot_add_and32 E1 26 24 bimg idx F26 F18 ltac:(lia) ltac:(lia) ltac:(lia)) Ra0;
pose proof (st_ok_agree trasegs 37 E1 (havoc E1 37 [Z_to_bv 64 (bimg + idx); Z_to_bv 64 vbb]) ssv msv HS
(env_agree_havoc_ge 37 37 E1 E1 _ ltac:(lia) (env_agree_refl 37 E1)) ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS end.
lazymatch type of HS with st_ok _ ?E3 ?ssv ?msv =>
lazymatch E3 with havoc ?E1 _ ?ws =>
assert (E37 : ew E3 37 = Z_to_bv 64 (bimg + idx)) by (exact (ew_havoc_new E1 37 ws 0 (Z_to_bv 64 0) ltac:(cbn; lia)));
assert (E38 : ew E3 38 = Z_to_bv 64 vbb) by (exact (ew_havoc_new E1 37 ws 1 (Z_to_bv 64 0) ltac:(cbn; lia))) end;
assert (Vvbb : val_mem trasegs (ms_mem msv) (bimg + idx) 1 vbb)
by (cbn [ms_mem restrict mkst]; apply (val_mem_frame E _ _ _ _ 1 vbb HFr1); [| lia | cbn [Z.of_nat]; lia | exact Vvbb0];
intros kk Hkk; unfold ss_tin, tin_loc, tin_tmp; cbn [ss_mem]; intros (r & Hr & Hw); cbn [In] in Hr;
destruct Hr as [<- | [<- | []]]; cbn [YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi base_val] in Hw; [lia | rewrite E23, unsigned_lit_small in Hw by lia; lia]);
pose proof (st_ok_pin_rege E3 ssv msv 10%bv (SOff 37 0) HS ltac:(intros X; discriminate X)
ltac:(cbn [ms_regs restrict mkst]; rewrite Ra0; cbn [sv_denot]; rewrite E37, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS.
lazymatch type of HS with st_ok _ ?E3 ?ssv ?msv =>
pose proof (st_ok_add_fact trasegs E3 ssv msv 37 (HPTR 0) HS
ltac:(unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite E37, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia)) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS.
lazymatch type of HS with st_ok _ ?E3 ?ssv ?msv =>
pose proof (st_ok_add_fact trasegs E3 ssv msv 38 (mkAF 0 255 0) HS
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E38, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia)) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS.
lazymatch type of HS with st_ok _ ?E3 ?ssv ?msv =>
pose proof (ast_ok_add_region trasegs E3 ssv msv (YQ0b.mkRegion (Some 37%nat) 0 1 0 0 [YQ0b.mkChunk 0 (CVal 1 (SOff 38 0))]) HS eq_refl
ltac:(unfold region_ok; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val ms_mem restrict mkst];
rewrite E37, unsigned_lit_small by lia; split; [lia|]; split; [lia|]; split; [intros o Ho; lia|];
apply Forall_cons; [|apply Forall_nil];
apply (chunk_ok_val trasegs E3 _ (bimg + idx) 0 1 _ vbb); [cbn [sv_denot]; rewrite E38, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | rewrite Z.add_0_r; exact Vvbb])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val];
cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E9, E23, !unsigned_lit_small by lia;
repeat split; lia)) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS.
lazymatch type of HS with st_ok _ ?E3 _ _ =>
assert (F6 : ew E3 6 = Z_to_bv 64 SB) by (rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E6);
assert (F23 : ew E3 23 = Z_to_bv 64 p) by (rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E23) end.
reshok_bx HS 6%nat.
pose proof (proj1 HJ) as HAR2.
aj_run_to_tok tratbl_lib_ok HS HJ SHOK FLBspan A_cmpPixel.
all: try (lazymatch goal with |- range_addressable _ (U ?Ex _) (U _ (SOff 37 ?cc)) ?len =>
first [rewrite (U_atom_off Ex 37 (bimg + idx) cc E37) by lia | rewrite (U_atom Ex 37 (bimg + idx) E37) by lia];
eapply (obl_of_block trasegs _ LAWS _ _ _ _ _ Ex (SOff 6 0) _ len bimg Nb HAR2 Hbi); [rewrite (U_atom Ex 6 SB F6); [reflexivity | unfold SB; lia] | lia | lia] end).
1: { apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|].
eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 23%nat); [reflexivity | rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E23; apply unsigned_lit_small; lia
| intros a Ha; cbn [YQ0b.r_wlo YQ0b.r_whi] in Ha; apply (Hpawr (ablocks B lyc Sc)); [exact Hpt | clear - Ha Hp1 Hp2 Hcnt; lia] | apply awr_ok_nil]. }
rename HFr into HFr2. rename HG into HG2. clear HF.
lazymatch type of HS with st_ok _ ?Ecur _ _ =>
pose proof (acall_kept_of_run _ _ lyc Sc W _ _ _ (sp1 - TCMP_STK) sp1 (fun a => pt <= a < pt + npt) HAR2 HFr2 HG2
ltac:(intros a (r & Hr & Hw); cbn [In] in Hr; destruct Hr as [<- | [<- | [<- | []]]]; cbn [YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi base_val] in Hw;
[lia | lia | rewrite ?ew_havoc_old in Hw by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub] in Hw; rewrite ?ew_ewset_other in Hw by lia; rewrite E23, unsigned_lit_small in Hw by lia; left; lia])
ltac:(intros a Ha; cbn beta in Ha; split; [lia | pose proof (req_size_pos0 npt ltac:(lia)) as [_ Hrqa]; clear - Ha Hqh_img Hrqa; unfold off_img in *; lia]) ltac:(lia) ltac:(pose proof K1 as (_ & _ & _ & _ & _ & K6); exact K6)) as K2 end.
pose proof (acall_kept_trans _ _ _ _ _ _ _ _ _ K1 K2) as K12.
rreg HS (10%bv : bv 5) Qa0. rreg HS (11%bv : bv 5) Qa1. rreg HS (12%bv : bv 5) Qa2. rreg HS (13%bv : bv 5) Qa3. rreg HS (14%bv : bv 5) Qa4.
rreg HS (1%bv : bv 5) Qra. rreg HS (2%bv : bv 5) Qsp. rreg HS (3%bv : bv 5) Qgp. rreg HS (4%bv : bv 5) Qtp. rreg HS (8%bv : bv 5) Qs0.
pose proof (regs_kept_of_st_ok trasegs _ _ _ regs _ TIN_KEPT HS ltac:(env_agree32 HAE) ltac:(vm_compute; reflexivity)) as HKrX. cbn [ms_regs restrict] in HKrX.
pose proof (proj1 HJ) as HARX.
rewrite (st_ok_restrict_mkst trasegs _ _ _ _ HS eq_refl). cbn [ss_pc].
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) ?pcX (ms_mem _) _) ?mdX) _ =>
eapply (aj_call_sp W (ms_regs msX) (ms_mem msX) pcX TFLUSH_STK sp0 FP ly S W0 mem0 md0 [(2, fpos)] lyc Sc mdX k TCMP_STK [] 0 (sp1 - sp0) (Z_to_bv 64 555036) ch1
(fun ly2 S2 W2 regs2 mem2 md2 => ly2 = lyc /\ S2 = Sc /\ W2 = W /\ exists v : word, getr regs2 10 = v /\
(v = w64 0 <-> tcmp_zero (aview trasegs (w_H W) (ms_mem msX)) gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx vb vbb)) HJ) end.
- unfold spZ. rewrite Qsp. rewrite Usp. lia.
- rewrite Zminus_mod, Hsp1al, Hal16. reflexivity.
- lia. - rewrite WS. lia. - rewrite WS, FFS. lia.
- rewrite Qgp, E3. exact Hgp. - rewrite Qtp, E4. exact Htp.
- exact Qra. - apply ret_ok_even. vm_compute. reflexivity. - rewrite unsigned_lit_small by lia. lia.
- unfold s0Z. rewrite Qs0, E8. replace (sp0 + (sp1 - sp0)) with sp1 by lia. eapply achain_keptK; [exact K12 | exact Hch | lia | lia | lia].
- intros HPRE1. eapply SRr_mono.
+ eapply (TCMP lyc Sc W _ _ _ ch1 g cfp bfp vb vbb gvals cvals bvals gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx HPRE1).
* rewrite Qa0, E21. reflexivity. * rewrite Qa1, E22. reflexivity. * rewrite Qa2, E33. reflexivity.
* rewrite Qa3, E34. reflexivity. * first [exact Qa4 | rewrite Qa4, E38; reflexivity | rewrite Qa4; reflexivity]. * lia. * lia.
* exact Hg. * exact Hcf. * exact Hbf. * exact Hcb.
* eapply obj_at_keptK; [exact K12 | exact Hg | vm_compute; reflexivity | change (req_size CGIF_SIZE) with 96; intros i Hi Hn; lia | exact Og].
* exact Ogpal. * exact Ongp.
* eapply obj_at_keptK; [exact K12 | exact Hcf | vm_compute; reflexivity | change (req_size FRAME_SIZE) with 40; intros i Hi Hn; lia | exact Oc].
* exact Ocpal. * exact Ocattr. * exact Ocnlp. * exact Octidx.
* eapply obj_at_keptK; [exact K12 | exact Hbf | vm_compute; reflexivity | change (req_size FRAME_SIZE) with 40; intros i Hi Hn; lia | exact Ob].
* exact Obpal. * exact Obattr. * exact Obnlp. * exact Obtidx.
* exact HLc. * exact HLb. * exact HGp.
+ cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & v & -> & HJc & HPc & Hv & Hz).
exists lyc, Sc, regs2, mem2, md2. split; [rewrite Qra; reflexivity|]. split; [exact HJc|]. split; [exact HPc|].
split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. exists v. split; [exact Hv | exact Hz].
- intros a (r & Hr & _). destruct Hr. }
cbv beta. intros W2 c2 Hwle2 (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJc & HP2 & -> & -> & -> & v & Hv & Hz).
rewrite Z.add_0_r in HJ2. replace (sp0 + (sp1 - sp0)) with sp1 in HJc by lia.
clear Qa0 Qa1 Qa2 Qa3 Qa4 Qra Qsp Qgp Qtp Qs0.
pose proof (acall_kept_of_journal trasegs B tra_segs_low TCMP_STK sp1 [] [] lyc Sc W _ _ lyc Sc W mem2 md2 0 (fun _ => False) HJc HARX
ltac:(intros a (r & Hr & _); destruct Hr) ltac:(intros b mm i Hb _ _; exact Hb)) as Kc0.
pose proof (acall_kept_mono_E trasegs B _ _ _ _ _ _ _ _ _ (fun a => pt <= a < pt + npt) Kc0 ltac:(intros a HF; destruct HF)) as Kc.
pose proof (acall_kept_trans _ _ _ _ _ _ _ _ _ K12 Kc) as K12c.
lazymatch type of HS with st_ok _ ?Ev ?ssx _ =>
let kk := eval vm_compute in (run_K 0 (SOff 6 0) [] ssx) in
jafter_call_keep HS kk regs2 (mrestrict (w_H W) mem2) HP2 [1; 2]%nat HS2 end.
match type of HS2 with ?Q -> _ =>
assert (HQ : Q);
[ cbn [ms_mem restrict]; apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]
| specialize (HS2 HQ); clear HQ ] end.
{ eapply (region_kept_stack_aj trasegs _); [exact Kc0 | exact HJ2
| rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E9; apply unsigned_lit_small; lia
| lia | rewrite FFS; lia | lia | lia | lia]. }
{ eapply (region_kept_sub_ajw _ lyc Sc W _ W mem2 _ _ _ 23 0 1 0 1 _ p pt npt lyc Sc md2);
[ exact Kc0 | exact (proj1 HJ2) | exact Hpt
| rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E23; apply unsigned_lit_small; lia
| exact Hpt | lia | lia | lia | lia | intros a Ha Hn; exact Hn ]. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
lazymatch type of HS with st_ok _ ?Ecur _ _ =>
assert (G23 : ew Ecur 23 = Z_to_bv 64 p) by (rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E23);
assert (G6 : ew Ecur 6 = Z_to_bv 64 SB) by (rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E6) end.
reshok_bx HS 6%nat.
pose proof (proj1 HJ2) as HAR3.
aj_run_tok tratbl_lib_ok HS HJ2 SHOK FLBspan.
1: { apply awr_ok_cons_ro; [cbn; lia|].
eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 23%nat); [reflexivity | rewrite G23; apply unsigned_lit_small; lia
| intros a Ha; cbn [YQ0b.r_wlo YQ0b.r_whi] in Ha; apply (Hpawr (ablocks B lyc Sc)); [exact Hpt | clear - Ha Hp1 Hp2 Hcnt; lia] | apply awr_ok_nil]. }
rename HFr into HFr3. rename HG into HG3. clear HF.
pose proof (acall_kept_of_run _ _ lyc Sc W _ _ _ (sp1 - TCMP_STK) sp1 (fun a => pt <= a < pt + npt) HAR3 HFr3 HG3
ltac:(intros a (r & Hr & Hw); cbn [In] in Hr; destruct Hr as [<- | [<- | []]]; cbn [YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi base_val] in Hw;
[lia | rewrite G23, unsigned_lit_small in Hw by lia; left; lia])
ltac:(intros a Ha; cbn beta in Ha; split; [lia | pose proof (req_size_pos0 npt ltac:(lia)) as [_ Hrqa]; clear - Ha Hqh_img Hrqa; unfold off_img in *; lia]) ltac:(lia) ltac:(pose proof Kc as (_ & _ & _ & _ & _ & K6); exact K6)) as K3.
pose proof (acall_kept_trans _ _ _ _ _ _ _ _ _ K12c K3) as K123.
assert (TAIL : forall Ex ssx msx mdx, st_ok trasegs Ex ssx (restrict (w_H W) msx) -> ss_pc ssx = 0x87830 -> ss_resv ssx = None ->
env_agree 32 (Ereg regs [Z_to_bv 64 tidx; Z_to_bv 64 bfp; Z_to_bv 64 vb]) Ex ->
forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ssx) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) TIN_KEPT = true ->
sr_get (ss_regs ssx) 0%bv = SLit 0 -> sr_get (ss_regs ssx) 27%bv = SLit 4294967295 ->
sr_get (ss_regs ssx) 23%bv = SOff 23 0 -> sr_get (ss_regs ssx) 18%bv = SOff 23 0 -> sr_get (ss_regs ssx) 20%bv = SOff 20 0 -> sr_get (ss_regs ssx) 24%bv = SOff 24 0 ->
ew Ex 23 = Z_to_bv 64 p -> ew Ex 20 = Z_to_bv 64 c -> ew Ex 24 = Z_to_bv 64 idx ->
ajournal trasegs B TFLUSH_STK sp0 FP ly S W0 mem0 md0 [(2, fpos)] lyc Sc W (ms_mem msx) mdx k ->
acall_kept trasegs B lyc Sc W memc W (ms_mem msx) (sp1 - TCMP_STK) sp1 (fun a => pt <= a < pt + npt) ->
SRr trasegs W (mkCfg msx mdx) (tin_post W regs memc sp0 sp1 FP ly S W0 mem0 md0 lyc Sc k fpos pt npt)).
{ intros Ex ssx msx mdx HSx Hpc Hrv HAEx Hkept H0 H27x H23x H24x H20x H18x X23 X20 X18 HJx Kx.
pose proof (regs_kept_of_st_ok trasegs _ _ _ regs _ TIN_KEPT HSx HAEx Hkept) as HKx. cbn [ms_regs restrict] in HKx.
rewrite (st_ok_restrict_mkst trasegs _ _ _ _ HSx Hrv). rewrite Hpc.
eapply (fl_tin_tail m IH c W regs (ms_regs msx) memc mdc (ms_mem msx) mdx sp0 sp1 FP ly S W0 mem0 md0 lyc Sc k fpos ch1
pt npt p bimg Nb idx g cfp bfp tidx gvals cvals bvals gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx);
[ lia | exact Hcnt | exact HCTX0 | exact Hp1 | exact Hp2 | exact Hidx1 | exact Hidx2 | exact HJx | exact Kx | | | | | ].
- intros r Hr. destruct (tin_clob_cases3 r Hr) as [-> | [-> | Hr']].
+ rewrite (st_ok_restrict_reg trasegs _ _ _ _ 0%bv HSx), H0. rewrite (st_ok_restrict_reg trasegs _ _ _ _ 0%bv HS0). reflexivity.
+ rewrite (st_ok_restrict_reg trasegs _ _ _ _ 27%bv HSx), H27x, H27. reflexivity.
+ exact (HKx r Hr').
- rewrite (st_ok_restrict_reg trasegs _ _ _ _ 23%bv HSx), H23x. cbn [sv_denot]. rewrite X23, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
- rewrite (st_ok_restrict_reg trasegs _ _ _ _ 18%bv HSx), H24x. cbn [sv_denot]. rewrite X23, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
- rewrite (st_ok_restrict_reg trasegs _ _ _ _ 20%bv HSx), H20x. cbn [sv_denot]. rewrite X20, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
- rewrite (st_ok_restrict_reg trasegs _ _ _ _ 24%bv HSx), H18x. cbn [sv_denot]. rewrite X18, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
srr_branch_tok tratbl_lib_ok HS SHOK FLBspan.
-
reshok_bx HS 6%nat. pose proof (proj1 HJ2) as HAR4.
aj_run_to_tok tratbl_lib_ok HS HJ2 SHOK FLBspan 0x87830.
1: { apply awr_ok_cons_ro; [cbn; lia|].
eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 23%nat); [reflexivity | rewrite G23; apply unsigned_lit_small; lia
| intros a Ha; cbn [YQ0b.r_wlo YQ0b.r_whi] in Ha; apply (Hpawr (ablocks B lyc Sc)); [exact Hpt | clear - Ha Hp1 Hp2 Hcnt; lia] | apply awr_ok_nil]. }
rename HFr into HFr4. rename HG into HG4. clear HF.
pose proof (acall_kept_of_run _ _ lyc Sc W _ _ _ (sp1 - TCMP_STK) sp1 (fun a => pt <= a < pt + npt) HAR4 HFr4 HG4
ltac:(intros a (r & Hr & Hw); cbn [In] in Hr; destruct Hr as [<- | [<- | []]]; cbn [YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi base_val] in Hw;
[lia | rewrite G23, unsigned_lit_small in Hw by lia; left; lia])
ltac:(intros a Ha; cbn beta in Ha; split; [lia | pose proof (req_size_pos0 npt ltac:(lia)) as [_ Hrqa]; clear - Ha Hqh_img Hrqa; unfold off_img in *; lia]) ltac:(lia) ltac:(pose proof K3 as (_ & _ & _ & _ & _ & K6); exact K6)) as K4.
eapply (TAIL _ _ _ _ HS); [reflexivity | reflexivity | env_agree32 HAE | vm_compute; reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
| rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E23
| rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E20
| rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E18
| exact HJ2 | exact (acall_kept_trans _ _ _ _ _ _ _ _ _ K123 K4) ].
-
reshok_bx HS 6%nat. pose proof (proj1 HJ2) as HAR4.
aj_run_to_tok tratbl_lib_ok HS HJ2 SHOK FLBspan 0x87830.
all: try (lazymatch goal with |- range_addressable _ (U ?Ex _) (U _ (SOff 23 ?cc)) ?len =>
first [rewrite (U_atom_off Ex 23 p cc G23) by lia | rewrite (U_atom Ex 23 p G23) by lia];
eapply (obl_of_block trasegs _ LAWS _ _ _ _ _ Ex (SOff 6 0) _ len pt npt HAR4 Hpt); [rewrite (U_atom Ex 6 SB G6); [reflexivity | unfold SB; lia] | lia | lia] end).
1: { apply awr_ok_cons_ro; [cbn; lia|].
eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 23%nat); [reflexivity | rewrite G23; apply unsigned_lit_small; lia
| intros a Ha; cbn [YQ0b.r_wlo YQ0b.r_whi] in Ha; apply (Hpawr (ablocks B lyc Sc)); [exact Hpt | clear - Ha Hp1 Hp2 Hcnt; lia] | apply awr_ok_nil]. }
rename HFr into HFr4. rename HG into HG4. clear HF.
pose proof (acall_kept_of_run _ _ lyc Sc W _ _ _ (sp1 - TCMP_STK) sp1 (fun a => pt <= a < pt + npt) HAR4 HFr4 HG4
ltac:(intros a (r & Hr & Hw); cbn [In] in Hr; destruct Hr as [<- | [<- | []]]; cbn [YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi base_val] in Hw;
[lia | rewrite G23, unsigned_lit_small in Hw by lia; left; lia])
ltac:(intros a Ha; cbn beta in Ha; split; [lia | pose proof (req_size_pos0 npt ltac:(lia)) as [_ Hrqa]; clear - Ha Hqh_img Hrqa; unfold off_img in *; lia]) ltac:(lia) ltac:(pose proof K3 as (_ & _ & _ & _ & _ & K6); exact K6)) as K4.
eapply (TAIL _ _ _ _ HS); [reflexivity | reflexivity | env_agree32 HAE | vm_compute; reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
| rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E23
| rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E20
| rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E18
| exact HJ2 | exact (acall_kept_trans _ _ _ _ _ _ _ _ _ K123 K4) ].
Qed.
Lemma fl_tin : forall m, tin_stmt m.
Proof.
induction m as [|m IH]; [|exact (fl_tin_step m IH)].
unfold tin_stmt. intros. exfalso. lia.
Qed.
End TL.
End d.
