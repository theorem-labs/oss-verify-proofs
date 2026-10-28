(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.cgif.cgif_file_fuzzer.images Require Import Asan.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AD1v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YP09 YK00 YK04 YA0i YA0n YK0g YK0c YK0d YK0e YK0f YK09 YA01 YA0c YA0e YA0d YA02 YA0j.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB12 AB1h AB13 AB01.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG00 YG01 YG0f YG0v YG0n YG0r YG0b.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AF0m.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05 YD1h.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AD1g AD2i AD1d AD1e.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Import AX2. Import AX2B. Import AX2S. Import APC. Import APG. Import APSG.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.
Lemma tfib_holes_imgsh : forallb (fun ch => kn_vis TFIB ch (ELit 0) 0x7fffa000 0xbd600) HS_tfib_list = true.
Proof. vm_compute. reflexivity. Qed.
Section c. Context {fx : YK11.FPState}.
Section d.
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
#[local] Notation MR := (Mr TFIB TOP argH E ch model FULL).
#[local] Notation HID := (hid TFIB TOP argH E ch model).
#[local] Notation u := (uE E).
#[local] Notation usp := (bv_unsigned sp).
#[local] Notation V n := (bv_unsigned (ev E n)).
#[local] Notation vm := (vm_maps (m_vmmaps model)).
#[local] Notation ly0 := (AD1g.ly0 ch E model).
#[local] Notation rdS := (AD1g.rdS sp rdraw inp ch E FULL model).
#[local] Notation HS0 := (AD1g.HS0 sp rdraw inp ch E model).
#[local] Notation W0 := (AD2i.W1 sp rdraw inp Hsp Hva ch E model).
#[local] Notation H1 := (AD2i.H1 sp rdraw inp ch E model).
Ltac inst H := try specialize (H B); try specialize (H HB); try specialize (H sp); try specialize (H rdraw); try specialize (H brk); try specialize (H inp);
try specialize (H Hsp); try specialize (H Hva); try specialize (H Hve); try specialize (H Hfit); try specialize (H h); try specialize (H ch);
try specialize (H E); try specialize (H R); try specialize (H FULL); try specialize (H model); try specialize (H Hch); try specialize (H HC);
try specialize (H HE); try specialize (H HM); try specialize (H rc); try specialize (H Hceil).
Ltac get L := let H := fresh "L" in pose proof L as H; inst H; exact H.
#[local] Definition dm_vals := ltac:(get @AD1g.dm_vals).
#[local] Definition vm_bound := ltac:(get @AD1g.vm_bound).
#[local] Definition vm_nth := ltac:(get @AD1g.vm_nth).
#[local] Definition VZ_facts := ltac:(get @AD1g.VZ_facts).
#[local] Definition avis_sound := ltac:(get @AD1g.avis_sound).
#[local] Definition rinfo_val := ltac:(get @AD1g.rinfo_val).
#[local] Definition stk_val := ltac:(get @AD1g.stk_val).
#[local] Definition hole_facts := ltac:(get @AD1g.hole_facts).
#[local] Definition uT := ltac:(get @AD1g.uT).   #[local] Definition uC := ltac:(get @AD1g.uC).   #[local] Definition uD := ltac:(get @AD1g.uD).
#[local] Definition uF := ltac:(get @AD1g.uF).   #[local] Definition uNB := ltac:(get @AD1g.uNB). #[local] Definition uSB := ltac:(get @AD1g.uSB).
#[local] Definition uSp := ltac:(get @AD1g.uSp). #[local] Definition uP := ltac:(get @AD1g.uP).   #[local] Definition uTop := ltac:(get @AD1g.uTop).
#[local] Definition uTopRel := ltac:(get @AD1g.uTopRel).
#[local] Definition ceil_le_TOP := ltac:(get @AD1g.ceil_le_TOP). #[local] Definition ceil_ge_TOP := ltac:(get @AD1g.ceil_ge_TOP).
#[local] Definition usp_range := ltac:(get @AD1g.usp_range).
#[local] Definition stack_zero := ltac:(get @AD1g.stack_zero).
#[local] Definition tfib_ARm := ltac:(get @AD1g.tfib_ARm).
#[local] Definition tfib_ALedger := ltac:(get @AD1d.tfib_ALedger).
#[local] Definition tfib_abudget := ltac:(get @AD1d.tfib_abudget).
#[local] Definition tfib_amwf := ltac:(get @AD1d.tfib_amwf).
#[local] Definition rdW_ext := ltac:(get @AD1d.rdW_ext).
#[local] Definition band_hidden_zero := ltac:(get @AD1d.band_hidden_zero).
#[local] Definition MR_full := ltac:(get @AD1d.MR_full).
#[local] Definition avis_cases := ltac:(get @AD1d.avis_cases).
#[local] Definition kz_facts := ltac:(get @AD1d.kz_facts).
#[local] Definition musl_extra := ltac:(get @AD1d.musl_extra).
#[local] Definition tfib_ahz := ltac:(get @AD1e.tfib_ahz).
#[local] Definition band_allow := ltac:(get @AD1e.band_allow).
#[local] Definition GV_extra := ltac:(get @AD1e.GV_extra).     #[local] Definition e292_extra := ltac:(get @AD1e.e292_extra).
#[local] Definition e254_extra := ltac:(get @AD1e.e254_extra). #[local] Definition e109_extra := ltac:(get @AD1e.e109_extra).
Lemma band_rom_none : forall z, in_band_rw z -> seg_rom TSEGS (Z_to_bv 64 z) = None.
Proof.
intros z Hz. unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in Hz.
assert (U : bv_unsigned (Z_to_bv 64 z) = z) by (apply u64_lit; lia).
unfold seg_rom, memory_read. change (Z.of_N 1) with 1. rewrite (tfib_in_hull (Z_to_bv 64 z)); [reflexivity|].
rewrite U. unfold in_hull. apply andb_false_iff. right. apply Z.ltb_ge. change (img_hi TFIB) with 0x5fb000. lia.
Qed.
Lemma MR_present : forall z, in_band_rw z -> hreader TSEGS MR z <> None -> FULL (w64 z) <> None.
Proof.
intros z Hz H. unfold hreader, mbyte in H. unfold w64. destruct (MR (Z_to_bv 64 z)) as [b|] eqn:Em.
- rewrite (MR_full _ _ Em). discriminate.
- rewrite (band_rom_none z Hz) in H. exfalso. exact (H eq_refl).
Qed.
Lemma rdS_present : forall z, in_band_rw z -> rdS z <> None -> FULL (w64 z) <> None.
Proof.
intros z Hz H. unfold AD1g.rdS, aview, mbyte, mrestrict in H. unfold w64.
destruct (HS0 (Z_to_bv 64 z)).
- rewrite (band_rom_none z Hz) in H. exfalso. exact (H eq_refl).
- destruct (FULL (Z_to_bv 64 z)); [discriminate|]. rewrite (band_rom_none z Hz) in H. exfalso. exact (H eq_refl).
Qed.
Lemma kz_present : forall rb rk len i z, kn_zero ch rb rk len = true -> 0 <= len < 2 ^ 62 -> 0 <= i < len -> z = u rb + rk + i ->
in_band_rw z -> FULL (w64 z) <> None.
Proof.
intros rb rk len i z Hk Hlen Hi -> Hb. apply (MR_present _ Hb).
rewrite (ho_zero_range TSEGS TFIB LIM TOP SINV argH (in_fs inp) E ch R FULL model HC rb rk len ltac:(lia) Hk i Hi). discriminate.
Qed.
Lemma IMGSH : kn_vis TFIB ch (ELit 0) 0x7fffa000 0xbd600 = true.
Proof. pose proof (proj1 (forallb_forall _ _) tfib_holes_imgsh ch (HS_tfib_In h ch Hch)) as H. exact H. Qed.
Lemma img_sh_present : forall z, 0x7fffa000 <= z < 0x7fffa000 + 0xbd600 -> FULL (w64 z) <> None.
Proof.
intros z Hz. apply MR_present; [unfold in_band_rw, kLowShadowBeg, kLowShadowEnd; left; lia|].
replace z with (u (ELit 0) + 0x7fffa000 + (z - 0x7fffa000)) by (rewrite uE_litv by lia; lia).
exact (ho_vis_range TSEGS TFIB LIM TOP SINV argH (in_fs inp) tfib_in_hull tfib_hull_ok E ch R FULL model HC (ELit 0) 0x7fffa000 0xbd600 IMGSH (z - 0x7fffa000) ltac:(lia)).
Qed.
Lemma vz_vis0 : forall a z, In z (VZ E model) -> SHADOW_OFF + fst z / 8 <= a -> a < SHADOW_OFF + (fst z + snd z) / 8 -> in_vis0 ly0 a.
Proof.
intros a [b len] Hz B1 B2. destruct (VZ_facts (b, len) Hz) as (_ & M1 & M2 & P1 & P2). cbn [fst snd] in M1, M2, P1, P2, B1, B2.
unfold in_vis0. cbn [ly_vis0 AD1g.ly0]. unfold VIS0. apply Exists_exists. exists (shz (b, len)). split; [apply in_map; exact Hz|].
unfold in_zr, shz, shadow_addr. cbn [fst snd].
apply Z.mod_divide in M1 as [q Hq]; [|lia]. apply Z.mod_divide in M2 as [r Hr]; [|lia]. subst b len.
rewrite !Z.div_mul by lia. replace (q * 8 + r * 8) with ((q + r) * 8) in B2 by lia. rewrite Z.div_mul in B1, B2 by lia. lia.
Qed.
Theorem tfib_ahs_pres_hid : ahs_pres B ly0 init_state HID FULL.
Proof.
intros a Ha _ Hc.
assert (BND : kLowShadowBeg <= a < kHighShadowEnd) by (unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in Ha |- *; lia).
assert (Ua : bv_unsigned (w64 a) = a) by (unfold w64; apply u64_lit; unfold kLowShadowBeg, kHighShadowEnd in BND; lia).
destruct (HID (w64 a)) eqn:Hh.
{   rewrite <- Ua in Ha. rewrite (band_hidden_zero (w64 a) Ha Hh). discriminate. }
destruct Hc as [Hc|Hnv]; [discriminate Hc|].
pose proof (band_allow (w64 a) ltac:(rewrite Ua; exact Ha) Hh) as AL. rewrite Ua in AL.
pose proof (proj1 (@ASAN_CEIL_range rc)) as CR. pose proof ceil_le_TOP as CT. unfold YA02.TOP in CT. pose proof usp_range as [UR U16].
assert (VISZ : forall (p : expr * expr) (z : Z * Z), sh_lo TFIB E p <= a < sh_hi TFIB E p -> In z (VZ E model) ->
fst z <= u (fst p) -> u (fst p) + u (snd p) <= fst z + snd z -> False).
{ intros p z [B1 B2] Hz Hlo Hhi. unfold sh_lo, sh_hi in B1, B2. change (shadow_off TFIB) with SHADOW_OFF in B1, B2.
apply Hnv. apply (vz_vis0 a z Hz).
- assert (D1 : fst z / 8 <= u (fst p) / 8) by (apply Z.div_le_mono; lia). lia.
- assert (D2 : (u (fst p) + u (snd p)) / 8 <= (fst z + snd z) / 8) by (apply Z.div_le_mono; lia). lia. }
assert (KZ : forall (p : expr * expr) n len L, sh_lo TFIB E p <= a < sh_hi TFIB E p -> p = (epg n, ELit len) -> u (epg n) = 4096 * V n ->
0 <= len < 2 ^ 62 -> kn_zero ch (EMd M_MUL (ELit 512) (EVar n)) 2147450880 L = true -> L = len / 8 -> FULL (w64 a) <> None).
{ intros p n len L [B1 B2] -> Hu Hl Hk ->. unfold sh_lo, sh_hi in B1, B2. change (shadow_off TFIB) with SHADOW_OFF in B1, B2. cbn [fst snd] in B1, B2.
rewrite (uE_litv E len) in B2 by lia. pose proof (uE_bound E (epg n)) as UB. rewrite Hu in B1, B2, UB.
assert (U512 : u (EMd M_MUL (ELit 512) (EVar n)) = 512 * V n) by (rewrite uE_mul_lit; rewrite ?uE_var; lia).
replace (4096 * V n) with ((512 * V n) * 8) in B1 by lia. rewrite Z.div_mul in B1 by lia.
replace (4096 * V n + len) with (len + (512 * V n) * 8) in B2 by lia. rewrite Z.div_add in B2 by lia.
apply (kz_present (EMd M_MUL (ELit 512) (EVar n)) 2147450880 (len / 8) (a - SHADOW_OFF - 512 * V n) a Hk).
- split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
- unfold SHADOW_OFF in *. lia.
- rewrite U512. unfold SHADOW_OFF. lia.
- exact Ha. }
unfold in_allow in AL. apply orb_prop in AL as [AV|ASH].
-   exfalso.
unfold in_vis in AV. apply existsb_exists in AV as (p & Hp & Hb). apply andb_prop in Hb as [B1 B2]. apply Z.leb_le in B1. apply Z.ltb_lt in B2.
destruct (avis_sound p Hp) as [(i & m & L & Hi & Hb & HL & HLL & R1 & R2 & R3 & R4 & R5) | [-> | [-> | ->]]].
+ unfold kHighMemBeg, kLowShadowBeg, kHighShadowEnd in *. clear - B1 B2 R1 R2 R3 R4 BND CR. lia.
+ pose proof rinfo_val as (F1 & F2 & F3 & F4 & F5). rewrite F1 in B1, B2. rewrite F2 in B2. unfold kHighMemBeg, kLowShadowBeg, kHighShadowEnd in *. clear - B1 B2 F3 F4 F5 BND. lia.
+ unfold IMG_P in B1, B2. cbn [fst snd] in B1, B2. rewrite !uE_litv in B2 by lia. unfold kLowShadowBeg in BND. clear - B2 BND. lia.
+ pose proof stk_val as [F1 F2]. rewrite F1 in B1. unfold kHighShadowEnd in BND. clear - B1 BND CT CR UR. lia.
-
unfold in_sh in ASH. apply existsb_exists in ASH as (p & Hp & Hb). apply andb_prop in Hb as [B1 B2]. apply Z.leb_le in B1. apply Z.ltb_lt in B2.
pose proof (conj B1 B2) as B12.
pose proof dm_vals as (VP & VQ & VT & VF & VNB & VSB & VLow & VHigh & VGap & VGV & VD & V292 & VC & V254 & V109).
pose proof uT as [HT HTr]. pose proof uC as [HCc HCr]. pose proof uD as [HD HDr]. pose proof uF as [HFv HFr].
pose proof uNB as [HNB HNBr]. pose proof uSB as [HSBv HSBr]. pose proof uSp as (S1 & S2 & S3 & S4). pose proof uP as [_ HPr].
destruct (avis_cases p Hp) as [H13 | (m & Hm & Hsub)].
+ unfold AVIS13 in H13. cbn [In] in H13.
assert (PG : forall n len (z : Z * Z), p = (epg n, ELit len) -> 0 <= len < 2 ^ 64 -> In z (VZ E model) -> fst z = u (epg n) -> len <= snd z -> False).
{ intros n len [zl zn] Hpe Hlen Hz Hz1 Hz2. cbn [fst snd] in Hz1, Hz2. subst zl.
apply (VISZ p (u (epg n), zn) B12 Hz); rewrite Hpe; cbn [fst snd]; [lia|]. rewrite (uE_litv E len) by lia. lia. }
destruct H13 as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]].
*   exfalso.
eapply (PG 518%nat 4096 (wzp (dGV E)) eq_refl ltac:(lia)); [unfold VZ; apply in_app_iff; right; exact GV_extra | rewrite VGV; reflexivity | rewrite VGV; cbn [snd]; lia].
*
eapply (KZ _ 501%nat 8388608 1048576 B12 eq_refl HSBv ltac:(lia) (proj1 kz_facts)). reflexivity.
*
eapply (KZ _ 500%nat 1048576 131072 B12 eq_refl HNB ltac:(lia) (proj1 (proj2 kz_facts))). reflexivity.
*
eapply (KZ _ 424%nat 11571200 1446400 B12 eq_refl HFv ltac:(lia) (proj2 (proj2 kz_facts))). reflexivity.
*   exfalso. eapply (PG 357%nat 4096 (u eD, 4096) eq_refl ltac:(lia)); [unfold VZ; cbn; tauto | reflexivity | cbn [snd]; lia].
*   exfalso.
eapply (PG 292%nat 4096 (wzp (d292 E)) eq_refl ltac:(lia)); [unfold VZ; apply in_app_iff; right; exact e292_extra | rewrite V292; reflexivity | rewrite V292; cbn [snd]; lia].
*   exfalso. eapply (PG 275%nat 65536 (u eC, 65536) eq_refl ltac:(lia)); [unfold VZ; cbn; tauto | reflexivity | cbn [snd]; lia].
*   exfalso. eapply (PG 274%nat 4096 (u eT, 4096) eq_refl ltac:(lia)); [unfold VZ; cbn; tauto | reflexivity | cbn [snd]; lia].
*   exfalso. pose proof rinfo_val as (F1 & F2 & F3 & F4 & F5).
apply (VISZ RINFO_P (u eSp + kRegionInfoOff, 4096) B12); [unfold VZ; cbn; tauto | cbn [fst snd]; rewrite F1; unfold kRegionInfoOff; lia | cbn [fst snd]; rewrite F1, F2; unfold kRegionInfoOff; lia].
*   exfalso.
eapply (PG 254%nat 3727360 (wzp (d254 E)) eq_refl ltac:(lia)); [unfold VZ; apply in_app_iff; right; exact e254_extra | rewrite V254; reflexivity | rewrite V254; cbn [snd]; lia].
*   exfalso.
eapply (PG 109%nat 65536 (wzp (d109 E)) eq_refl ltac:(lia)); [unfold VZ; apply in_app_iff; right; exact e109_extra | rewrite V109; reflexivity | rewrite V109; cbn [snd]; lia].
*
unfold sh_lo, sh_hi, IMG_P in B1, B2. change (shadow_off TFIB) with SHADOW_OFF in B1, B2. cbn [fst snd] in B1, B2.
rewrite !uE_litv in B1 by lia. rewrite !uE_litv in B2 by lia. apply img_sh_present. unfold SHADOW_OFF in B1, B2.
change (65536 / 8) with 8192 in B1. change ((65536 + 6205440) / 8) with 783872 in B2. clear - B1 B2. lia.
*
unfold sh_lo in B1. change (shadow_off TFIB) with SHADOW_OFF in B1. pose proof stk_val as [F1 F2]. rewrite F1 in B1.
pose proof ceil_ge_TOP as [CG CA].
pose proof (stack_zero (a - (SHADOW_OFF + ASAN_CEIL / 8))) as SZ. unfold shadow_of_addr in SZ.
replace (SHADOW_OFF + ASAN_CEIL / 8 + (a - (SHADOW_OFF + ASAN_CEIL / 8))) with a in SZ by lia.
apply (rdS_present a Ha). rewrite SZ; [discriminate|]. unfold SHADOW_OFF, kLowShadowBeg, kHighShadowEnd in *. clear - B1 BND CT CA CR. lia.
+   exfalso.
destruct (sub_of_map_sound p m Hsub) as (Hbm & L & HL & HLL & Hpp).
pose proof (musl_extra m Hm) as HX.
apply In_nth_error in Hm as (j & Hj).
assert (HA : nth_error (ALLMAPS ch) (3 + j) = Some m).
{ assert (Hjl : (j < length (musl_maps ch))%nat) by (apply (proj1 (nth_error_Some _ _)); rewrite Hj; discriminate).
unfold ALLMAPS. rewrite nth_error_app2 by (cbn; lia). change (length TFIB_HEAD3) with 3%nat.
rewrite nth_error_app1 by lia. replace (3 + j - 3)%nat with j by lia. exact Hj. }
pose proof (vm_bound (dmm E m) (nth_error_In _ _ (vm_nth _ _ HA))) as (P0 & P1 & P2 & P3 & P4).
assert (LEN : bv_unsigned (snd (dmm E m)) = L) by (unfold dmm, amap_den; cbn [snd]; rewrite HL; cbn [edenot]; apply u64_lit; lia).
assert (BASE : bv_unsigned (fst (dmm E m)) = u (am_base m)) by reflexivity.
apply (VISZ p (u (am_base m), L) B12).
* unfold VZ. apply in_app_iff. right. unfold wzp in HX. rewrite LEN, BASE in HX. exact HX.
* destruct Hpp as [-> | (k & n' & -> & Hk & Hn' & Hkn)]; cbn [fst snd]; [lia|]. rewrite uE_add; rewrite (uE_litv E k) by lia; lia.
* destruct Hpp as [-> | (k & n' & -> & Hk & Hn' & Hkn)]; cbn [fst snd]; [rewrite (uE_litv E L) by lia; lia|].
rewrite (uE_litv E n') by lia. rewrite uE_add; rewrite (uE_litv E k) by lia; lia.
Qed.
Lemma H1_sub_HID : hsub H1 HID.
Proof. intros w Hw. unfold AD2i.H1 in Hw. apply andb_prop in Hw as [Hw _]. apply andb_prop in Hw as [Hw _]. exact Hw. Qed.
Theorem tfib_ahs : ahs B ly0 init_state (w_H W0) FULL.
Proof.
split.
- eapply ahs_pres_hsub; [exact H1_sub_HID | exact tfib_ahs_pres_hid].
- exact tfib_ahz.
Qed.
Theorem tfib_AR : AR TSEGS B ly0 init_state W0 FULL model.
Proof.
split; [| split; [| split; [| split]]].
- exact (ARm_ext B ly0 init_state _ _ rdW_ext tfib_ARm).
- exact tfib_ALedger.
- exact tfib_abudget.
- exact tfib_amwf.
- exact tfib_ahs.
Qed.
Lemma tfib_top_ok : AD1v.top_ok usp ly0.
Proof.
pose proof uTopRel as [T1 T2]. pose proof uTop as (_ & _ & _ & T4). pose proof usp_range as [UR U16].
unfold AD1v.top_ok. cbn [ly_top ly_stk_lo ly_stk_hi AD1g.ly0].
split; [lia|]. split; [reflexivity|]. split; [reflexivity | exact Hceil].
Qed.
End d.
Theorem tfib_AR_init : forall (B : asyms) (HB : TfibSyms B) (sp : word) (rdraw : EntryDraw) (brk : word) (inp : ProcInput)
(Hsp : valid_sp sp) (Hva : valid_argv (in_argv inp)),
valid_envp (in_envp inp) -> entry_stack_fits sp (in_argv inp) (in_envp inp) ->
forall (h : nat) (ch : acs) (E : env) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model),
HS_tfib h = Some ch ->
cs_ok TSEGS TFIB YA02.LIMIT (YA02.TOP sp)
(YA02.SINV0 TPH sp rdraw brk (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp))
(YA02.argH0 TPH sp rdraw (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) (in_fs inp) E ch R FULL model ->
(forall n, (n < NX0G)%nat -> ev E n = ev (YA02.E0 TPH sp rdraw brk (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) n) ->
(forall a, YA02.argH0 TPH sp rdraw (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) E a = true ->
FULL a = wrap_mem TPH sp (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) rdraw a) ->
forall {rc : YM05.RunCeil}, YM05.ceil_of_top (bv_unsigned sp - stack_max_size) ->
exists ly, AR TSEGS B ly init_state (AD2i.W1 sp rdraw inp Hsp Hva ch E model) FULL model /\ AD1v.top_ok (bv_unsigned sp) ly.
Proof.
intros B HB sp rdraw brk inp Hsp Hva Hve Hfit h ch E R FULL model Hch HC HE HM rc Hceil.
exists (AD1g.ly0 ch E model). split.
- eapply (tfib_AR B HB); eassumption.
- eapply tfib_top_ok; eassumption.
Qed.
End c.
