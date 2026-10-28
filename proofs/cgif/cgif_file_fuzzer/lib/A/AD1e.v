(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.cgif.cgif_file_fuzzer.images Require Import Asan.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YP09 YK00 YK04 YA0i YA0n YK0g YK0c YK0d YK0e YK0f YK09 YA01 YA0c YA0e YA0d YA02 YA0j.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB12 AB1h AB13 AB01.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG00 YG01 YG0f YG0v YG0n YG0r YG0b.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AF0m.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05 YD1h.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AD1g AD2i AD1d.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Import AX2. Import AX2B. Import AX2S. Import APC. Import APG. Import APSG.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.
Section b. Context {fx : YK11.FPState}.
Section c.
Variable B : asyms.
Hypothesis HB : TfibSyms B.
Variables (sp : word) (rdraw : EntryDraw) (brk : word) (inp : ProcInput).
Hypothesis Hsp : valid_sp sp.
Hypothesis Hva : valid_argv (in_argv inp).
Hypothesis Hve : valid_envp (in_envp inp).
Hypothesis Hfit : entry_stack_fits sp (in_argv inp) (in_envp inp).
Variable h : nat.
Variables (ch : acs) (E : env) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model).
Hypothesis Hch : HS_tfib h = Some ch.
#[local] Notation argv := (in_argv inp).
#[local] Notation envp := (in_envp inp).
#[local] Notation uid := (in_uid inp).
#[local] Notation hw := (in_hwcap inp).
#[local] Notation SINV := (YA02.SINV0 TPH sp rdraw brk argv envp uid hw).
#[local] Notation argH := (YA02.argH0 TPH sp rdraw argv envp uid hw).
#[local] Notation TOP := (YA02.TOP sp).
#[local] Notation LIM := YA02.LIMIT.
Hypothesis HC : cs_ok TSEGS TFIB LIM TOP SINV argH (in_fs inp) E ch R FULL model.
Hypothesis HE : forall n, (n < NX0G)%nat -> ev E n = ev (YA02.E0 TPH sp rdraw brk argv envp uid hw) n.
Hypothesis HM : forall a, argH E a = true -> FULL a = wrap_mem TPH sp argv envp uid hw rdraw a.
Context {rc : YM05.RunCeil}.
Hypothesis Hceil : YM05.ceil_of_top (bv_unsigned sp - stack_max_size).
#[local] Notation HID := (hid TFIB TOP argH E ch model).
#[local] Notation u := (uE E).
#[local] Notation usp := (bv_unsigned sp).
#[local] Notation V n := (bv_unsigned (ev E n)).
#[local] Notation vm := (vm_maps (m_vmmaps model)).
#[local] Notation ly0 := (AD1g.ly0 ch E model).
Ltac inst H := try specialize (H B); try specialize (H HB); try specialize (H sp); try specialize (H rdraw); try specialize (H brk); try specialize (H inp);
try specialize (H Hsp); try specialize (H Hva); try specialize (H Hve); try specialize (H Hfit); try specialize (H h); try specialize (H ch);
try specialize (H E); try specialize (H R); try specialize (H FULL); try specialize (H model); try specialize (H Hch); try specialize (H HC);
try specialize (H HE); try specialize (H HM); try specialize (H rc); try specialize (H Hceil).
Ltac get L := let H := fresh "L" in pose proof L as H; inst H; exact H.
#[local] Definition dm_vals := ltac:(get @AD1g.dm_vals).
#[local] Definition vm_bound := ltac:(get @AD1g.vm_bound).
#[local] Definition vm_In' := ltac:(get @AD1g.vm_In').
#[local] Definition vm_nth := ltac:(get @AD1g.vm_nth).
#[local] Definition nth_ALLMAPS_tail := ltac:(get @AD1g.nth_ALLMAPS_tail).
#[local] Definition statics_eq := ltac:(get @AD1g.statics_eq).
#[local] Definition VZ_facts := ltac:(get @AD1g.VZ_facts).
#[local] Definition avis_sound := ltac:(get @AD1g.avis_sound).
#[local] Definition rinfo_val := ltac:(get @AD1g.rinfo_val).
#[local] Definition stk_val := ltac:(get @AD1g.stk_val).
#[local] Definition hole_facts := ltac:(get @AD1g.hole_facts).
#[local] Definition uT := ltac:(get @AD1g.uT).   #[local] Definition uC := ltac:(get @AD1g.uC).   #[local] Definition uD := ltac:(get @AD1g.uD).
#[local] Definition uF := ltac:(get @AD1g.uF).   #[local] Definition uNB := ltac:(get @AD1g.uNB). #[local] Definition uSB := ltac:(get @AD1g.uSB).
#[local] Definition uGV := ltac:(get @AD1g.uGV). #[local] Definition u292 := ltac:(get @AD1g.u292). #[local] Definition u254 := ltac:(get @AD1g.u254).
#[local] Definition u109 := ltac:(get @AD1g.u109). #[local] Definition uSp := ltac:(get @AD1g.uSp). #[local] Definition uP := ltac:(get @AD1g.uP).
#[local] Definition ceil_le_TOP := ltac:(get @AD1g.ceil_le_TOP). #[local] Definition usp_range := ltac:(get @AD1g.usp_range).
#[local] Definition band_facts := ltac:(get @AD1d.band_facts).
#[local] Definition band_hidden_zero := ltac:(get @AD1d.band_hidden_zero).
#[local] Definition avis_cases := ltac:(get @AD1d.avis_cases).
#[local] Definition musl_extra := ltac:(get @AD1d.musl_extra).
#[local] Definition Hseps := ho_seps TSEGS TFIB LIM TOP SINV argH (in_fs inp) E ch R FULL model HC.
#[local] Ltac vin := apply vm_In'; cbn; tauto.
Lemma distinct_at : forall i j mi mj, nth_error (ALLMAPS ch) i = Some mi -> nth_error (ALLMAPS ch) j = Some mj -> i <> j -> dmm E mi <> dmm E mj.
Proof.
intros i j mi mj Hi Hj Hij Heq.
pose proof (vm_nth _ _ Hi) as Vi. pose proof (vm_nth _ _ Hj) as Vj.
pose proof (vm_bound (dmm E mi) (nth_error_In _ _ Vi)) as (P0 & _).
destruct (Nat.lt_ge_cases i j) as [L|L].
- pose proof (seps_pair _ Hseps i j _ _ L Vi Vj) as D. rewrite <- Heq in D. unfold iv_disjoint in D. lia.
- pose proof (seps_pair _ Hseps j i _ _ ltac:(lia) Vj Vi) as D. rewrite <- Heq in D. unfold iv_disjoint in D. lia.
Qed.
Lemma unknown_at : forall i m, nth_error (ALLMAPS ch) i = Some m ->
(i <> 1)%nat -> (i <> 2)%nat ->
(forall t, (t = 0 \/ t = 1 \/ t = 3 \/ t = 4 \/ t = 5 \/ t = 6 \/ t = 9 \/ t = 10 \/ t = 11)%nat -> i <> (3 + length (musl_maps ch) + t)%nat) ->
known E (dmm E m) = false.
Proof.
intros i m Hi N1 N2 NT. destruct (known E (dmm E m)) eqn:Hk; [|reflexivity]. exfalso.
unfold known in Hk. apply existsb_exists in Hk as (k & HkK & Hkeq). apply iv_eqb_eq in Hkeq.
rewrite KNOWN_eq in HkK.
assert (TL : forall t e len knd, nth_error TFIB_TAIL12 t = Some (mk e len knd) ->
(t = 0 \/ t = 1 \/ t = 3 \/ t = 4 \/ t = 5 \/ t = 6 \/ t = 9 \/ t = 10 \/ t = 11)%nat -> dmm E m = dm E e len knd -> False).
{ intros t e len knd Ht Htt Hx. exact (distinct_at i _ m (mk e len knd) Hi (nth_ALLMAPS_tail t _ Ht) (NT t Htt) Hx). }
assert (HDx : forall j e len knd, nth_error (ALLMAPS ch) j = Some (mk e len knd) -> i <> j -> dmm E m = dm E e len knd -> False).
{ intros j e len knd Hj Hij Hx. exact (distinct_at i j m (mk e len knd) Hi Hj Hij Hx). }
destruct HkK as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]].
- exact (TL 6%nat _ _ _ eq_refl ltac:(lia) Hkeq).
- exact (TL 5%nat _ _ _ eq_refl ltac:(lia) Hkeq).
- exact (TL 4%nat _ _ _ eq_refl ltac:(lia) Hkeq).
- exact (TL 0%nat _ _ _ eq_refl ltac:(lia) Hkeq).
- exact (HDx 2%nat _ _ _ eq_refl N2 Hkeq).
- exact (HDx 1%nat _ _ _ eq_refl N1 Hkeq).
- exact (TL 11%nat _ _ _ eq_refl ltac:(lia) Hkeq).
- exact (TL 9%nat _ _ _ eq_refl ltac:(lia) Hkeq).
- exact (TL 10%nat _ _ _ eq_refl ltac:(lia) Hkeq).
- exact (TL 3%nat _ _ _ eq_refl ltac:(lia) Hkeq).
- exact (TL 1%nat _ _ _ eq_refl ltac:(lia) Hkeq).
Qed.
Lemma extra_of : forall i m, nth_error (ALLMAPS ch) i = Some m -> known E (dmm E m) = false -> In (wzp (dmm E m)) (extra E model).
Proof.
intros i m Hi Hk. unfold extra. apply in_map. apply List.filter_In. split; [exact (nth_error_In _ _ (vm_nth _ _ Hi))|]. rewrite Hk. reflexivity.
Qed.
Lemma GV_extra : In (wzp (dGV E)) (extra E model).
Proof.
change (dGV E) with (dmm E (mk eGV 4096 KRW)). apply (extra_of 0%nat); [reflexivity|].
apply (unknown_at 0%nat); [reflexivity | lia | lia | intros t _; lia].
Qed.
Lemma e292_extra : In (wzp (d292 E)) (extra E model).
Proof.
change (d292 E) with (dmm E (mk e292 4096 KRW)). apply (extra_of (3 + length (musl_maps ch) + 2)%nat); [exact (nth_ALLMAPS_tail 2 _ eq_refl)|].
apply (unknown_at (3 + length (musl_maps ch) + 2)%nat); [exact (nth_ALLMAPS_tail 2 _ eq_refl) | lia | lia | intros t Ht; lia].
Qed.
Lemma e254_extra : In (wzp (d254 E)) (extra E model).
Proof.
change (d254 E) with (dmm E (mk e254 3727360 KRW)). apply (extra_of (3 + length (musl_maps ch) + 7)%nat); [exact (nth_ALLMAPS_tail 7 _ eq_refl)|].
apply (unknown_at (3 + length (musl_maps ch) + 7)%nat); [exact (nth_ALLMAPS_tail 7 _ eq_refl) | lia | lia | intros t Ht; lia].
Qed.
Lemma e109_extra : In (wzp (d109 E)) (extra E model).
Proof.
change (d109 E) with (dmm E (mk e109 65536 KRW)). apply (extra_of (3 + length (musl_maps ch) + 8)%nat); [exact (nth_ALLMAPS_tail 8 _ eq_refl)|].
apply (unknown_at (3 + length (musl_maps ch) + 8)%nat); [exact (nth_ALLMAPS_tail 8 _ eq_refl) | lia | lia | intros t Ht; lia].
Qed.
Lemma shz_granule : forall g lo len, g mod 8 = 0 -> lo mod 8 = 0 -> 0 <= lo -> 0 <= g ->
SHADOW_OFF + lo / 8 <= shadow_addr g < SHADOW_OFF + (lo + len) / 8 -> lo <= g < lo + len.
Proof.
intros g lo len Hg Hl H0 Hg0 Ha. unfold shadow_addr in Ha.
apply Z.mod_divide in Hg as [q Hq]; [|lia]. apply Z.mod_divide in Hl as [p Hp]; [|lia]. subst g lo.
rewrite !Z.div_mul in Ha by lia. replace (p * 8 + len) with (len + p * 8) in Ha by lia. rewrite Z.div_add in Ha by lia.
pose proof (Z.mul_div_le len 8 ltac:(lia)). pose proof (Z.div_mod len 8 ltac:(lia)). pose proof (Z.mod_pos_bound len 8 ltac:(lia)). lia.
Qed.
Lemma hfree_hit : forall g lo len, hfree ly0 init_state g -> In (lo, len) (static_extents ly0 ++ vis0_zones ly0) -> lo <= g < lo + len -> False.
Proof.
intros g lo len HF Hin Hg. unfold hfree in HF.
assert (Hin' : In (lo, len) (static_extents ly0 ++ vis0_zones ly0 ++ sec_extents ly0 init_state)).
{ apply in_app_iff in Hin as [Hin|Hin]; apply in_app_iff; [left; exact Hin | right; apply in_app_iff; left; exact Hin]. }
pose proof (proj1 (Forall_forall _ _) HF (lo, len) Hin') as X. cbn [fst snd] in X. lia.
Qed.
Lemma band_allow : forall a : word, in_band_rw (bv_unsigned a) -> HID a = false -> in_allow TFIB E ch (bv_unsigned a) = true.
Proof.
intros a Ha Hh. destruct (band_facts a Ha) as (Hna & Hlz & Hm).
unfold hid in Hh. apply orb_false_iff in Hh as [_ Hv]. apply negb_false_iff in Hv. unfold vis in Hv.
rewrite Hm, Hna, Hlz in Hv. cbn [negb andb orb] in Hv.
replace (in_hull TFIB (bv_unsigned a)) with false in Hv
by (symmetry; unfold in_hull; change (img_hi TFIB) with 0x5fb000; apply andb_false_iff; right; apply Z.ltb_ge;
unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in Ha; lia).
replace (TOP <=? bv_unsigned a) with false in Hv
by (symmetry; apply Z.leb_gt; pose proof usp_range as [UR _]; unfold YA02.TOP; change stack_max_size with 8388608;
unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in Ha; lia).
exact Hv.
Qed.
Theorem tfib_ahz : ahz ly0 init_state FULL.
Proof.
intros g Hg Happ HF. pose proof (shadow_addr_band_rw g Happ) as Ha. set (a := shadow_addr g) in *.
assert (BND : kLowShadowBeg <= a < kHighShadowEnd) by (unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in Ha |- *; lia).
assert (Ua : bv_unsigned (w64 a) = a) by (unfold w64; apply u64_lit; unfold kLowShadowBeg, kHighShadowEnd in BND; lia).
rewrite <- Ua in Ha.
destruct (HID (w64 a)) eqn:Hh.
{   exact (band_hidden_zero (w64 a) Ha Hh). }
exfalso.
pose proof (band_allow (w64 a) Ha Hh) as AL. rewrite Ua in AL, Ha.
destruct Happ as [G4 GR]. pose proof (proj1 (@ASAN_CEIL_range rc)) as CR. pose proof ceil_le_TOP as CT. unfold YA02.TOP in CT.
pose proof usp_range as [UR _].
assert (G0 : 0 <= g) by lia.
assert (L8 : forall lo, lo mod 8 = 0 -> lo <= g -> lo / 8 <= g / 8) by (intros lo _ Hl; apply Z.div_le_mono; lia).
assert (ZONE : forall (p : expr * expr) lo len, sh_lo TFIB E p <= a < sh_hi TFIB E p ->
In (lo, len) (static_extents ly0 ++ vis0_zones ly0) -> lo mod 8 = 0 -> 0 <= lo ->
lo <= u (fst p) -> u (fst p) + u (snd p) <= lo + len -> False).
{ intros p lo len [B1 B2] Hin Hl8 Hl0 Hlo Hhi. unfold sh_lo, sh_hi in B1, B2. change (shadow_off TFIB) with SHADOW_OFF in B1, B2.
apply (hfree_hit g lo len HF Hin). apply shz_granule; [exact Hg | exact Hl8 | exact Hl0 | exact G0 |].
assert (D1 : lo / 8 <= u (fst p) / 8) by (apply Z.div_le_mono; lia).
assert (D2 : (u (fst p) + u (snd p)) / 8 <= (lo + len) / 8) by (apply Z.div_le_mono; lia).
subst a. lia. }
assert (AL8 : forall n, u (epg n) = 4096 * V n -> u (epg n) mod 8 = 0).
{ intros n ->. replace (4096 * V n) with ((512 * V n) * 8) by lia. apply Z_mod_mult. }
assert (STATIC : forall z, In z [wzp (dP E); wzp (dQ E); wzp (dT E); wzp (dF E); wzp (dNB E); wzp (dSB E); (u eC, 256); wzp (dD E); (ASAN_CEIL, 2 ^ 47 - ASAN_CEIL); TFIB_IMG] ->
In z (static_extents ly0 ++ vis0_zones ly0)).
{ intros z Hz. apply in_app_iff. left. rewrite statics_eq. cbn [map app]. exact Hz. }
assert (VIS0 : forall z, In z (VZ E model) -> In z (static_extents ly0 ++ vis0_zones ly0)).
{ intros z Hz. apply in_app_iff. right. exact (proj1 (VZ_facts z Hz)). }
assert (EXTRA : forall z, In z (extra E model) -> In z (static_extents ly0 ++ vis0_zones ly0)).
{ intros z Hz. apply VIS0. unfold VZ. apply in_app_iff. right. exact Hz. }
pose proof dm_vals as (VP & VQ & VT & VF & VNB & VSB & VLow & VHigh & VGap & VGV & VD & V292 & VC & V254 & V109).
pose proof uT as [HT HTr]. pose proof uC as [HCc HCr]. pose proof uD as [HD HDr]. pose proof uF as [HFv HFr].
pose proof uNB as [HNB HNBr]. pose proof uSB as [HSBv HSBr]. pose proof uGV as [HGV HGVr]. pose proof u292 as [H292 H292r].
pose proof u254 as [H254 H254r]. pose proof u109 as [H109 H109r]. pose proof uSp as (S1 & S2 & S3 & S4). pose proof uP as [_ HPr].
unfold in_allow in AL. apply orb_prop in AL as [AV|ASH].
-
unfold in_vis in AV. apply existsb_exists in AV as (p & Hp & Hb). apply andb_prop in Hb as [B1 B2]. apply Z.leb_le in B1. apply Z.ltb_lt in B2.
destruct (avis_sound p Hp) as [(i & m & L & Hi & Hb & HL & HLL & R1 & R2 & R3 & R4 & R5) | [-> | [-> | ->]]].
+ unfold kHighMemBeg, kLowShadowBeg, kHighShadowEnd in *. clear - B1 B2 R1 R2 R3 R4 BND CR. lia.
+ pose proof rinfo_val as (F1 & F2 & F3 & F4 & F5). rewrite F1 in B1, B2. rewrite F2 in B2. unfold kHighMemBeg, kLowShadowBeg, kHighShadowEnd in *. clear - B1 B2 F3 F4 F5 BND. lia.
+ unfold IMG_P in B1, B2. cbn [fst snd] in B1, B2. rewrite !uE_litv in B2 by lia. unfold kLowShadowBeg in BND. clear - B2 BND. lia.
+ pose proof stk_val as [F1 F2]. rewrite F1 in B1. unfold kHighShadowEnd in BND. clear - B1 BND CT CR UR. lia.
-
unfold in_sh in ASH. apply existsb_exists in ASH as (p & Hp & Hb). apply andb_prop in Hb as [B1 B2]. apply Z.leb_le in B1. apply Z.ltb_lt in B2.
pose proof (conj B1 B2) as B12.
destruct (avis_cases p Hp) as [H13 | (m & Hm & Hsub)].
+ unfold AVIS13 in H13. cbn [In] in H13.
assert (PG : forall n len (z : Z * Z), p = (epg n, ELit len) -> u (epg n) = 4096 * V n -> 0 <= len < 2 ^ 64 ->
In z (static_extents ly0 ++ vis0_zones ly0) -> fst z = u (epg n) -> len <= snd z -> False).
{ intros n len [zl zn] Hpe Hu Hlen Hin Hz1 Hz2. cbn [fst snd] in Hz1, Hz2. subst zl.
apply (ZONE p (u (epg n)) zn B12 Hin (AL8 n Hu) ltac:(pose proof (uE_bound E (epg n)); lia)); rewrite Hpe; cbn [fst snd]; [lia|]. rewrite uE_litv by lia. lia. }
destruct H13 as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]].
*   eapply (PG 518%nat 4096 (wzp (dGV E)) eq_refl HGV ltac:(lia) (EXTRA _ GV_extra)); rewrite VGV; cbn [fst snd]; [reflexivity | lia].
*   eapply (PG 501%nat 8388608 (wzp (dSB E)) eq_refl HSBv ltac:(lia)); [apply STATIC; cbn; tauto | rewrite VSB; reflexivity | rewrite VSB; cbn [snd]; lia].
*   eapply (PG 500%nat 1048576 (wzp (dNB E)) eq_refl HNB ltac:(lia)); [apply STATIC; cbn; tauto | rewrite VNB; reflexivity | rewrite VNB; cbn [snd]; lia].
*   eapply (PG 424%nat 11571200 (wzp (dF E)) eq_refl HFv ltac:(lia)); [apply STATIC; cbn; tauto | rewrite VF; reflexivity | rewrite VF; cbn [snd]; lia].
*   eapply (PG 357%nat 4096 (u eD, 4096) eq_refl HD ltac:(lia)); [apply VIS0; unfold VZ; cbn; tauto | reflexivity | cbn [snd]; lia].
*   eapply (PG 292%nat 4096 (wzp (d292 E)) eq_refl H292 ltac:(lia) (EXTRA _ e292_extra)); rewrite V292; cbn [fst snd]; [reflexivity | lia].
*   eapply (PG 275%nat 65536 (u eC, 65536) eq_refl HCc ltac:(lia)); [apply VIS0; unfold VZ; cbn; tauto | reflexivity | cbn [snd]; lia].
*   eapply (PG 274%nat 4096 (u eT, 4096) eq_refl HT ltac:(lia)); [apply VIS0; unfold VZ; cbn; tauto | reflexivity | cbn [snd]; lia].
*   pose proof rinfo_val as (F1 & F2 & F3 & F4 & F5).
apply (ZONE RINFO_P (u eSp + kRegionInfoOff) 4096 B12); [apply VIS0; unfold VZ; cbn; tauto | | unfold kRegionInfoOff; lia | rewrite F1; unfold kRegionInfoOff; lia | rewrite F1, F2; unfold kRegionInfoOff; lia].
unfold kRegionInfoOff. apply Z.mod_divide in S2 as [q Hq]; [|lia]. rewrite Hq. replace (q * 65536 + 2 ^ 37) with ((8192 * q + 2 ^ 34) * 8) by lia. apply Z_mod_mult.
*   eapply (PG 254%nat 3727360 (wzp (d254 E)) eq_refl H254 ltac:(lia) (EXTRA _ e254_extra)); rewrite V254; cbn [fst snd]; [reflexivity | lia].
*   eapply (PG 109%nat 65536 (wzp (d109 E)) eq_refl H109 ltac:(lia) (EXTRA _ e109_extra)); rewrite V109; cbn [fst snd]; [reflexivity | lia].
*   apply (ZONE IMG_P 0x10000 0x5eb000 B12); [apply STATIC; cbn; tauto | reflexivity | lia | |];
unfold IMG_P; cbn [fst snd]; rewrite ?uE_litv by lia; lia.
*   pose proof stk_val as [F1 F2]. unfold sh_lo in B1. change (shadow_off TFIB) with SHADOW_OFF in B1. rewrite F1 in B1.
subst a. unfold shadow_addr in B1.
assert (X : g / 8 + 1 <= (usp - 8388608) / 8).
{ replace (g / 8 + 1) with ((g + 8) / 8) by (rewrite <- Z.div_add by lia; reflexivity). apply Z.div_le_mono; [lia|].
unfold kLowShadowBeg, kHighMemBeg in GR. lia. }
lia.
+
destruct (sub_of_map_sound p m Hsub) as (Hbm & L & HL & HLL & Hpp).
pose proof (musl_extra m Hm) as HX.
pose proof hole_facts as (_ & _ & MOK & _).
destruct (musl_map_sound ch m (proj1 (Forall_forall _ _) MOK m Hm)) as (v & n & o & Hbase & Hlen & Hn & Hr & Ho).
apply In_nth_error in Hm as (j & Hj).
assert (HA : nth_error (ALLMAPS ch) (3 + j) = Some m).
{ assert (Hjl : (j < length (musl_maps ch))%nat) by (apply (proj1 (nth_error_Some _ _)); rewrite Hj; discriminate).
unfold ALLMAPS. rewrite nth_error_app2 by (cbn; lia). change (length TFIB_HEAD3) with 3%nat.
rewrite nth_error_app1 by lia. replace (3 + j - 3)%nat with j by lia. exact Hj. }
pose proof (vm_bound (dmm E m) (nth_error_In _ _ (vm_nth _ _ HA))) as (P0 & P1 & P2 & P3 & P4).
assert (LEN : bv_unsigned (snd (dmm E m)) = L) by (unfold dmm, amap_den; cbn [snd]; rewrite HL; cbn [edenot]; apply u64_lit; lia).
assert (BASE : bv_unsigned (fst (dmm E m)) = u (am_base m)) by reflexivity.
apply (ZONE p (u (am_base m)) L B12).
* unfold wzp in HX. rewrite LEN, BASE in HX. exact (EXTRA _ HX).
* rewrite <- BASE. apply Z.mod_divide in P1 as [q Hq]; [|lia]. rewrite Hq. replace (q * 4096) with ((512 * q) * 8) by lia. apply Z_mod_mult.
* pose proof (uE_bound E (am_base m)). lia.
* destruct Hpp as [-> | (k & n' & -> & Hk & Hn' & Hkn)]; cbn [fst snd]; [lia|]. rewrite uE_add; rewrite (uE_litv E k) by lia; lia.
* destruct Hpp as [-> | (k & n' & -> & Hk & Hn' & Hkn)]; cbn [fst snd]; [rewrite (uE_litv E L) by lia; lia|].
rewrite (uE_litv E n') by lia. rewrite uE_add; rewrite (uE_litv E k) by lia; lia.
Qed.
End c.
End b.
