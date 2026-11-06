(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the proofs of the interceptor site results stated in lib/A/PresetD1preAx.v
(* Theorem Labs, 2026-10-29: relocated image A (asan d83eb25d, twin f0d2e8d4) -> A' (#102 1be0f53d, twin bff8519b) by alreloc frozen-0474699fc83547e0 (a working branch 83209f9d9cd8): zero-shadow end 0x20f40 -> 0x20f60 (A' AF0m Tfib_zero_shadow), its decimal twin 134976 -> 135008; BY HAND the derived quotient (135008 - 65536) / 8 = 8684 (was 8680); the hull bound 0x20e00 KEPT (a chosen bound below the zero-shadow end, 0x20e00 <= 0x20f60, every caller's p + n <= 0x20cc4 on A': AE3i.v img_ro_chunks), so its quotient 16831 stays. *)
   (fuzz_preset, asan image), ported from the core's lib/A (relocated from proofs/cgif/cgif_file_fuzzer/lib/A):
     icpt_pre_facts_cf / icpt_pre_room_cf                     from AD1k.v:191-206;
     rodata_zero_shadow_cf / rodata_hull_zero_cf / rodata_shadow_facts_cf   from AD1k.v:207-234 (over the regenerated
       core's first zero-shadow range (YImgTop.IMG_LO, 0x20f60 - YImgTop.IMG_LO), lib/A/AF0m.v Tfib_zero_shadow);
     stderr_not_owned_cf                                      replaces AD1k.v:148-170 (tfib_img_not_owned, which reads
       cgif's ALedger): ARcf's AR_owned_image_law_cf and AD1k's tfib_not_owned_static give it directly;
     band_zero_shadow_cf / band_hull_zero_cf / band_shadow_facts_cf   from AD1l.v:54-98;
     tfib_fwrite_site_cf_A_holds / tfib_refused_site_cf_A_holds        from AD1k.v:273-345;
     tfib_fprintf_{open,rderr,usage}_site_cf_A_holds                   from AD1l.v:99-161.
   The interceptor walks are the ARcf copies AE2xcf / AE2tcf / AE2ucf / AE2vcf / AE2wcf (port/cfcopy.py, rule 24: a
   port of the released walks) at a8's AR_laws_ok_cf. The AR-free image facts are AD1k.v's / AD1l.v's, cited.
   Rule 24: no function is proved here (composition / driver layer of a port). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0i YK15 YK18 YP0n YM02 YP0m YP09 YP0l
YP06 YP08 YP03 YN3q YN3v YI04 YK04 YA0i YA0n YA0e YG00 YG01 YG0f YG0v YG0n YG0s YG0d YCe5 YL02.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AF0m AD2j AD2i AD1t AD20 AD1v AD2h AD2f AD1w AD1x
AD1y AE3i AE23.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AD1k AD1l.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AE2pcf AE39cf AE3hcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require AE2xcf AE2tcf AE2ucf AE2vcf AE2wcf AE3jcf AE3kcf AE3lcf AE3ncf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO05 YO09 YO06 YO01 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YGcfNames YG01cf YG00cf YG0ncf YG0dcf YG0lawscf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PresetD1sitesAPf PresetD1preA PresetD1preAx.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Section P.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Variable B : asyms.
Hypothesis HB : TfibSyms B.
Let ARL : AR_laws_cf tfibsegs B := AR_laws_ok_cf tfibsegs B.
Variable est : (word -> bool) -> (word -> option byte) -> Prop.

(* The copied walks keep the donor's Section hypotheses (B, LAWS, TB, TL; LAWS now AR_laws_cf), each abstracted
   only where its proof uses it: instantiate with the longest application that type-checks. *)
Local Ltac walk X WK :=
first [ pose proof (X B ARL HB HB) as WK | pose proof (X B ARL HB) as WK | pose proof (X B HB HB) as WK
| pose proof (X B HB) as WK | pose proof (X B ARL) as WK | pose proof (X B) as WK ].

(* AD1k.v:191-201. *)
Lemma icpt_pre_facts_cf : forall ly S W regs mem md, icpt_pre_cf B ly S W regs mem md ->
ecall_pre_cf tfibsegs B ly S [] W regs mem md /\ ly_stk_lo ly = ASAN_CEIL /\ sp_window_lo - 128 <= spZ regs <= sp_window_hi /\
(forall a, spZ regs - DIAG_STK <= a < spZ regs -> apresent (w_H W) mem a).
Proof.
intros ly S W regs mem md (HAR & Hret & Hra & Hal & Hwin & Htop & Hslo & Hshi & Hpres & Hgp & Htp).
split; [|split; [exact Hslo | split; [exact Hwin | exact Hpres]]].
split; [exact HAR|]. split; [exact Hret|]. split; [exact Hal|].
split; [pose proof (layout_of_ARcf B _ _ _ _ _ _ HAR) as LO; pose proof (lo_top _ LO) as (T1 & _); unfold ly_bot, kStackSpan, ESTACK in *; lia|].
split; [rewrite Hshi; unfold kHighMemEnd, sp_window_hi in *; lia|].
split; [intros a Ha; apply Hpres; unfold ESTACK, DIAG_STK in *; lia|]. exact (conj Hgp Htp).
Qed.

(* AD1k.v:202-206. *)
Lemma icpt_pre_room_cf : forall ly S W regs mem md, icpt_pre_cf B ly S W regs mem md -> ly_stk_lo ly + 2 ^ 23 - 4112 <= spZ regs.
Proof.
intros ly S W regs mem md (HAR & Hret & Hra & Hal & Hwin & Htop & Hslo & Hshi & Hpres & Hgp & Htp).
pose proof (layout_of_ARcf B _ _ _ _ _ _ HAR) as LO. pose proof (lo_top _ LO) as (T1 & _). unfold ly_bot, kStackSpan in *. lia.
Qed.

(* AD1k.v:207-213, over the regenerated core's first zero-shadow range (lib/A/AF0m.v Tfib_zero_shadow:
   (YImgTop.IMG_LO, 0x20f60 - YImgTop.IMG_LO)). *)
Lemma rodata_zero_shadow_cf : forall ly S W mem md, ARcf tfibsegs B ly S [] W mem md ->
zero_shadow (aview tfibsegs (w_H W) mem) SHADOW_OFF YImgTop.IMG_LO (0x20f60 - YImgTop.IMG_LO).
Proof.
intros ly S W mem md HAR.
exact (alc_zshadow _ _ ARL ly S [] W mem md (YImgTop.IMG_LO, 0x20f60 - YImgTop.IMG_LO) HAR
ltac:(unfold zero_shadow_ranges; right; rewrite (ts_zsh B HB); first [unfold Tfib_zero_shadow; left; reflexivity | cbn; tauto])).
Qed.

(* AD1k.v:214-227, with the zero-shadow range's low end YImgTop.IMG_LO as the window's. *)
Lemma rodata_hull_zero_cf : forall ly S W mem md p n, ARcf tfibsegs B ly S [] W mem md -> YImgTop.IMG_LO <= p -> p + n <= 0x20e00 -> 0 < n ->
AE2tcf.hull_zero (aview tfibsegs (w_H W) mem) p n.
Proof.
intros ly S W mem md p n HAR Hp Hn Hn0. pose proof (rodata_zero_shadow_cf ly S W mem md HAR) as HZ.
unfold YImgTop.IMG_LO in *.
intros s Hs. unfold shadow_addr in Hs.
assert (L1 : 0x10000 / 8 <= p / 8) by (apply Z.div_le_mono; lia).
assert (L2 : (p + n - 1) / 8 <= (0x20e00 - 1) / 8) by (apply Z.div_le_mono; lia).
change (0x10000 / 8) with 8192 in L1. change ((0x20e00 - 1) / 8) with 16831 in L2.
pose proof (Z.div_mod (SHADOW_OFF + p / 8) 8 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound (SHADOW_OFF + p / 8) 8 ltac:(lia)) as D1'.
pose proof (Z.div_mod (SHADOW_OFF + (p + n - 1) / 8) 8 ltac:(lia)) as D2. pose proof (Z.mod_pos_bound (SHADOW_OFF + (p + n - 1) / 8) 8 ltac:(lia)) as D2'.
replace s with (shadow_of_addr SHADOW_OFF 0x10000 + (s - shadow_of_addr SHADOW_OFF 0x10000)) by lia.
apply (HZ (s - shadow_of_addr SHADOW_OFF 0x10000)).
unfold shadow_of_addr, SHADOW_OFF in *. change (65536 / 8) with 8192. change ((135008 - 65536) / 8) with 8684. lia.
Qed.

(* AD1k.v:228-234. *)
Lemma rodata_shadow_facts_cf : forall ly S W mem md p n, ARcf tfibsegs B ly S [] W mem md -> YImgTop.IMG_LO <= p -> p + n <= 0x20e00 -> 0 < n ->
range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF p n /\ shadow_hull_vis (aview tfibsegs (w_H W) mem) p n.
Proof.
intros ly S W mem md p n HAR Hp Hn Hn0. split.
- intros x Hx. apply (zero_shadow_range _ SHADOW_OFF YImgTop.IMG_LO (0x20f60 - YImgTop.IMG_LO) eq_refl eq_refl (rodata_zero_shadow_cf ly S W mem md HAR) x).
unfold YImgTop.IMG_LO in *. lia.
- intros s Hs. rewrite (rodata_hull_zero_cf ly S W mem md p n HAR Hp Hn Hn0 s Hs). discriminate.
Qed.

(* The stderr FILE is not allocator-owned: replaces AD1k.v:148-170 (tfib_img_not_owned over cgif's ALedger). *)
Lemma stderr_not_owned_cf : forall ly S W mem md a, ARcf tfibsegs B ly S [] W mem md ->
F_STDERR <= a < F_STDERR + FILE_SZ -> ~ aowned B ly S a.
Proof.
intros ly S W mem md a HAR Ha HO.
assert (Hi : in_img tfibsegs a) by (apply in_img_rw; unfold F_STDERR, FILE_SZ in Ha; lia).
apply (tfib_not_owned_static B F_STDERR (F_STDERR + FILE_SZ) a HB ltac:(vm_compute; reflexivity) Ha).
exact (proj1 (alc_owned_image _ _ ARL ly S [] W mem md a HAR Hi) HO).
Qed.

(* AD1l.v:54-59. *)
Lemma band_zero_shadow_cf : forall ly S W mem md, ARcf tfibsegs B ly S [] W mem md -> ly_stk_lo ly = ASAN_CEIL -> ly_stk_hi ly = kHighMemEnd ->
zero_shadow (aview tfibsegs (w_H W) mem) SHADOW_OFF ASAN_CEIL (kHighMemEnd - ASAN_CEIL).
Proof.
intros ly S W mem md HAR Hlo Hhi. rewrite <- Hlo, <- Hhi.
exact (alc_zshadow _ _ ARL ly S [] W mem md (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly) HAR ltac:(unfold zero_shadow_ranges; left; reflexivity)).
Qed.

(* AD1l.v:60-81. *)
Lemma band_hull_zero_cf : forall ly S W mem md p n, ARcf tfibsegs B ly S [] W mem md -> ly_stk_lo ly = ASAN_CEIL -> ly_stk_hi ly = kHighMemEnd ->
ASAN_CEIL <= p -> p + n <= kHighMemEnd -> 0 < n ->
forall s, shadow_addr p / 8 * 8 <= s < shadow_addr (p + n - 1) / 8 * 8 + 8 -> aview tfibsegs (w_H W) mem s = Some 0.
Proof.
intros ly S W mem md p n HAR Hlo Hhi Hp Hn Hn0 s Hs. pose proof (band_zero_shadow_cf ly S W mem md HAR Hlo Hhi) as HZ.
unfold shadow_addr in Hs. pose proof alloc_ceiling_val as [CR CM]. unfold ASAN_CEIL, kHighMemEnd in *.
set (C := alloc_ceiling) in *.
assert (HC : C = 4096 * (C / 4096)) by (pose proof (Z.div_mod C 4096 ltac:(lia)); lia).
set (q := C / 4096) in *.
assert (HC8 : C / 8 = 512 * q) by (rewrite HC; replace (4096 * q) with (512 * q * 8) by lia; rewrite Z.div_mul by lia; reflexivity).
assert (HL8 : (140737488355328 - C) / 8 = 17592186044416 - 512 * q)
by (rewrite HC; replace (140737488355328 - 4096 * q) with ((17592186044416 - 512 * q) * 8) by lia; rewrite Z.div_mul by lia; reflexivity).
assert (L1 : C / 8 <= p / 8) by (apply Z.div_le_mono; lia).
assert (L2 : (p + n - 1) / 8 <= (140737488355328 - 1) / 8) by (apply Z.div_le_mono; lia).
change ((140737488355328 - 1) / 8) with 17592186044415 in L2.
assert (L3 : p / 8 <= (p + n - 1) / 8) by (apply Z.div_le_mono; lia).
pose proof (Z.div_mod (SHADOW_OFF + p / 8) 8 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound (SHADOW_OFF + p / 8) 8 ltac:(lia)) as D1'.
pose proof (Z.div_mod (SHADOW_OFF + (p + n - 1) / 8) 8 ltac:(lia)) as D2. pose proof (Z.mod_pos_bound (SHADOW_OFF + (p + n - 1) / 8) 8 ltac:(lia)) as D2'.
replace s with (shadow_of_addr SHADOW_OFF C + (s - shadow_of_addr SHADOW_OFF C)) by lia.
apply (HZ (s - shadow_of_addr SHADOW_OFF C)).
unfold shadow_of_addr, SHADOW_OFF in *. rewrite HC8, HL8. lia.
Qed.

(* AD1l.v:82-98. *)
Lemma band_shadow_facts_cf : forall ly S W mem md p n, ARcf tfibsegs B ly S [] W mem md -> ly_stk_lo ly = ASAN_CEIL -> ly_stk_hi ly = kHighMemEnd ->
ASAN_CEIL <= p -> p + n <= kHighMemEnd -> 0 < n ->
range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF p n /\ shadow_hull_vis (aview tfibsegs (w_H W) mem) p n.
Proof.
intros ly S W mem md p n HAR Hlo Hhi Hp Hn Hn0.
pose proof alloc_ceiling_val as [CR CM].
assert (HC : alloc_ceiling = 4096 * (alloc_ceiling / 4096)) by (pose proof (Z.div_mod alloc_ceiling 4096 ltac:(lia)); lia).
assert (M1 : ASAN_CEIL mod 8 = 0).
{ unfold ASAN_CEIL. rewrite HC. replace (4096 * (alloc_ceiling / 4096)) with ((512 * (alloc_ceiling / 4096)) * 8) by lia. apply Z_mod_mult. }
assert (M2 : (kHighMemEnd - ASAN_CEIL) mod 8 = 0).
{ unfold ASAN_CEIL, kHighMemEnd. rewrite HC.
replace (140737488355328 - 4096 * (alloc_ceiling / 4096)) with ((17592186044416 - 512 * (alloc_ceiling / 4096)) * 8) by lia. apply Z_mod_mult. }
split.
- intros x Hx. apply (zero_shadow_range _ SHADOW_OFF ASAN_CEIL (kHighMemEnd - ASAN_CEIL) M1 M2 (band_zero_shadow_cf ly S W mem md HAR Hlo Hhi) x).
unfold ASAN_CEIL, kHighMemEnd in *; lia.
- intros s Hs. rewrite (band_hull_zero_cf ly S W mem md p n HAR Hlo Hhi Hp Hn Hn0 s Hs). discriminate.
Qed.

(* AD1k.v:273-311. *)
Lemma tfib_fwrite_site_cf_sec : (forall H m, AE2p.stderr_written (mrestrict H m) -> est H m) -> fwrite_site_tfa_cf B est.
Proof.
intros ESTW ly S W regs mem md E p len msg T HPRE G10 G11 G12 G13 Hlen Hlen1 Hp1 Hp2 Hhole Himg HIMG Hfd HAI HPOST.
pose proof (icpt_pre_facts_cf ly S W regs mem md HPRE) as (HEPRE & Hslo & Hwin & Hpres). pose proof (proj1 HEPRE) as HAR.
pose proof (img_facts E _ HIMG) as ([IR1a IR1b] & IR2 & IR3 & Vcan).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HFWI : AE2xcf.FWI_STK = 6224) by reflexivity. assert (HDS : DIAG_STK = 16384) by reflexivity.
assert (HFE : F_STDERR = 0xa6628) by reflexivity. assert (HFS : FILE_SZ = 232) by reflexivity.
unfold wr. change (cfg_at tfibsegs A_icpt_fwrite regs mem md) with (cfg_at tfibsegs AE2xcf.FW_ENTRY regs mem md).
walk AE2xcf.tfib_fwrite_icpt WALK.
apply (WALK ly S W regs mem md ch_stderr p len (bv_unsigned (sv_denot E (SOff 41 0))) msg T HEPRE).
- pose proof (icpt_pre_room_cf ly S W regs mem md HPRE); unfold AE2xcf.FWI_STK in *; lia.
- intros a Ha. apply Hpres. lia.
- exact G10. - exact G11. - exact G12. - exact G13.
- lia. - lia. - lia. - unfold kHighMemEnd. lia.
- left. unfold sp_window_lo in Hwin. lia.
- left. rewrite HFE. lia.
-
apply (proj2 (rdn_mbytes tfibsegs (mrestrict (w_H W) mem) (Z.to_nat len) p msg)). split; [lia|].
intros i Hi. destruct Hhole as [Hh|Hh]; [rewrite (IR1a (p + Z.of_nat i)) by lia | rewrite (IR1b (p + Z.of_nat i)) by lia];
unfold img_byte; rewrite (Himg i) by lia; symmetry; apply nth_error_nth'; lia.
- eapply (file_is_img _ _ _); [exact IR3 | exact stderr_img_chk |].
unfold stderr_fields, AE2p.stderr_fields, AE2p.F_STDERR, AE2pcf.F_STDERR. repeat (apply Forall_cons; [cbn; lia|]). apply Forall_nil.
- intros a Ha. exact (stderr_not_owned_cf ly S W mem md a HAR Ha).
- eapply val_mem_img; [exact IR2 | unfold A_GOT_canary; lia | unfold A_GOT_canary; cbn; lia | exact got_canary_chk].
- exact Vcan.
- exact (u64_range (sv_denot E (SOff 41 0))).
- left. unfold kLowMemEnd. lia.
- exact (proj1 (rodata_shadow_facts_cf ly S W mem md p len HAR ltac:(unfold YImgTop.IMG_LO; lia) ltac:(lia) ltac:(lia))).
- exact (proj2 (rodata_shadow_facts_cf ly S W mem md p len HAR ltac:(unfold YImgTop.IMG_LO; lia) ltac:(lia) ltac:(lia))).
- split; [exact Hfd | reflexivity].
- exact HAI.
- intros regs' mem' md' HAR' HP' Hsbm' Ha0' HFW' Hfr' Hpr' HAI'.
apply (HPOST regs' mem' md' HAR' HP' Hsbm' Ha0').
+ apply ESTW. exact HFW'.
+ intros a Ha Hb Hf. apply (Hfr' a Ha); [lia|]. unfold STDERR_MUT, F_STDERR_LO, F_STDERR_HI in Hf. rewrite HFE, HFS. exact Hf.
+ intros a Ha Hf Hp. apply (Hpr' a Ha); [|exact Hp]. unfold STDERR_MUT, F_STDERR_LO, F_STDERR_HI in Hf. rewrite HFE, HFS. exact Hf.
+ exact HAI'.
Qed.

(* AD1k.v:314-345. *)
Lemma tfib_refused_site_cf_sec : (forall H m, AE3h.stderr_after_vfprintf (mrestrict H m) -> est H m) -> refused_site_tfa_cf B est.
Proof.
intros ESTV ly S W regs mem md E T HPRE G10 G11 G12 HIMG Hfd HAI HPOST.
pose proof (icpt_pre_facts_cf ly S W regs mem md HPRE) as (HEPRE & Hslo & Hwin & Hpres). pose proof (proj1 HEPRE) as HAR.
pose proof (img_facts E _ HIMG) as (IR1 & IR2 & IR3 & Vcan).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof msg_refused_eq as [ME ML].
assert (HFPI : AE2vcf.FPI_STK = 9216) by reflexivity. assert (HDS : DIAG_STK = 16384) by reflexivity.
assert (HFE : F_STDERR = 0xa6628) by reflexivity. assert (HFS : FILE_SZ = 232) by reflexivity.
unfold wr. rewrite <- ME. change (cfg_at tfibsegs A_icpt_fprintf regs mem md) with (cfg_at tfibsegs AE2vcf.FP_ENTRY regs mem md).
walk AE2vcf.tfib_fprintf_icpt_refused WALK.
apply (WALK ly S W regs mem md ch_stderr (bv_unsigned (sv_denot E (SOff 41 0))) T HEPRE).
- pose proof (icpt_pre_room_cf ly S W regs mem md HPRE); unfold AE2vcf.FPI_STK in *; lia.
- intros a Ha. apply Hpres. lia.
- exact G10. - exact G11. - exact G12.
- eapply (file_is_img _ _ _); [exact IR3 | exact stderr_img_chk |].
unfold stderr_fields, AE2p.stderr_fields, AE2p.F_STDERR, AE2pcf.F_STDERR. repeat (apply Forall_cons; [cbn; lia|]). apply Forall_nil.
- intros a Ha. unfold vf_file in Ha. exact (stderr_not_owned_cf ly S W mem md a HAR Ha).
- eapply val_mem_img; [exact IR2 | unfold A_GOT_canary; lia | unfold A_GOT_canary; cbn; lia | exact got_canary_chk].
- exact Vcan.
- exact (u64_range (sv_denot E (SOff 41 0))).
- exact (ro_img_of_IMG E _ HIMG).
- apply (rodata_hull_zero_cf ly S W mem md); [exact HAR | unfold YImgTop.IMG_LO, AE3lcf.FMT_refused; lia | unfold AE3lcf.FMT_refused; lia | lia].
- split; [exact Hfd | reflexivity].
- exact HAI.
- intros regs' mem' md' HAR' HP' Hsbm' Ha0' HFW' Hfr' Hpr' HAI'.
apply (HPOST regs' mem' md' HAR' HP' Hsbm').
+ rewrite ML. exact Ha0'.
+ apply ESTV. exact HFW'.
+ intros a Ha Hb Hf. apply (Hfr' a Ha); [lia|]. unfold vf_file. unfold STDERR_MUT, F_STDERR_LO, F_STDERR_HI in Hf. rewrite HFE, HFS. exact Hf.
+ intros a Ha Hf Hp. apply (Hpr' a Ha); [|exact Hp]. unfold vf_file. unfold STDERR_MUT, F_STDERR_LO, F_STDERR_HI in Hf. rewrite HFE, HFS. exact Hf.
+ exact HAI'.
Qed.

(* AD1l.v:99-146: the common body of the three fprintf %s sites. *)
Local Ltac fps_site_cf ESTV FPE THM LITS FMTV :=
intros ly S W regs mem md E s str T HPRE G10 G11 G12 Hlen Hnn Hs1 Hs2 HBr Htail HIMG Hfd HAI HPOST;
change (cfg_at tfibsegs A_icpt_fprintf regs mem md) with (cfg_at tfibsegs FPE regs mem md);
pose proof (icpt_pre_facts_cf ly S W regs mem md HPRE) as (HEPRE & Hslo & Hwin & Hpres); pose proof (proj1 HEPRE) as HAR;
pose proof HPRE as (_ & _ & _ & _ & _ & _ & _ & Hshi & _);
pose proof (img_facts E _ HIMG) as (IR1 & IR2 & IR3 & Vcan);
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5); pose proof LITS as [ME1 ME2]; pose proof lens_lits as (N1 & N2 & N3 & N4 & N5);
assert (HFPI1 : AE2tcf.FPI_STK = 9216) by reflexivity; assert (HFPI2 : AE2ucf.FPI_STK = 9216) by reflexivity;
assert (HFPI3 : AE2wcf.FPI_STK = 9216) by reflexivity; assert (HDS : DIAG_STK = 16384) by reflexivity;
assert (HFE : F_STDERR = 0xa6628) by reflexivity; assert (HFS : FILE_SZ = 232) by reflexivity;
assert (KHI : kHighMemEnd = 2 ^ 47) by reflexivity; pose proof (icpt_pre_room_cf ly S W regs mem md HPRE) as Hroom;
pose proof (band_shadow_facts_cf ly S W mem md s (Z.of_nat (length str) + 1) HAR Hslo Hshi
ltac:(rewrite <- Hslo; lia) ltac:(lia) ltac:(lia)) as [HRA HHV];
unfold wr; rewrite <- ME1, <- ME2;
apply (THM ly S W regs mem md ch_stderr s str (Z.of_nat (length str)) (bv_unsigned (sv_denot E (SOff 41 0))) T HEPRE);
[ unfold AE2tcf.FPI_STK, AE2ucf.FPI_STK, AE2wcf.FPI_STK in *; lia
| intros a Ha; apply Hpres; lia
| exact G10 | exact G11 | exact G12
| reflexivity
| lia
| unfold sp_window_lo in Hwin; lia
| rewrite <- KHI; lia
| right; lia
| right; rewrite HFE, HFS; unfold sp_window_lo in Hwin; lia
| right; unfold kHighMemBeg, kHighMemEnd; unfold kHighMemEnd in Hs2; unfold sp_window_lo in Hwin; lia
| apply vf_tail_of_site; exact Htail
| exact (mconsts_of_IMG E W mem HIMG)
| exact (vf_str_of_bytes W mem s str HBr Hnn)
| exact HRA
| exact HHV
| eapply (file_is_img _ _ _); [exact IR3 | exact stderr_img_chk |];
unfold stderr_fields, AE2p.stderr_fields, AE2p.F_STDERR, AE2pcf.F_STDERR; repeat (apply Forall_cons; [cbn; lia|]); apply Forall_nil
| intros a Ha; unfold vf_file in Ha; exact (stderr_not_owned_cf ly S W mem md a HAR Ha)
| eapply val_mem_img; [exact IR2 | unfold A_GOT_canary; lia | unfold A_GOT_canary; cbn; lia | exact got_canary_chk]
| exact Vcan
| exact (u64_range (sv_denot E (SOff 41 0)))
| exact (ro_img_of_IMG E _ HIMG)
| apply (rodata_hull_zero_cf ly S W mem md); [exact HAR | unfold YImgTop.IMG_LO, FMTV; lia | unfold FMTV; lia | lia]
| split; [exact Hfd | reflexivity]
| exact HAI
| intros regs' mem' md' HAR' HP' Hsbm' Ha0' HFW' Hfr' Hpr' HAI';
apply (HPOST regs' mem' md' HAR' HP' Hsbm');
[ etransitivity; [exact Ha0' | f_equal; rewrite ?N1, ?N2, ?N3, ?N4, ?N5; lia]
| apply ESTV; exact HFW'
| intros a Ha Hb Hf; apply (Hfr' a Ha); [lia|]; unfold vf_file; unfold STDERR_MUT, F_STDERR_LO, F_STDERR_HI in Hf; rewrite HFE, HFS; exact Hf
| intros a Ha Hf Hp; apply (Hpr' a Ha); [|exact Hp]; unfold vf_file; unfold STDERR_MUT, F_STDERR_LO, F_STDERR_HI in Hf; rewrite HFE, HFS; exact Hf
| exact HAI' ] ].

(* AD1l.v:147-151. *)
Lemma tfib_fprintf_open_site_cf_sec : (forall H m, AE3h.stderr_after_vfprintf (mrestrict H m) -> est H m) ->
fprintf_s_site_tfa_cf B est 0x1d845 (strB "cli: cannot open "%string) nlB.
Proof.
intros ESTV. change 0x1d845 with AE3jcf.FMT_open. unfold fprintf_s_site_tfa_cf.
walk AE2tcf.tfib_fprintf_icpt_open WALK.
fps_site_cf ESTV AE2tcf.FP_ENTRY WALK lits_open AE3jcf.FMT_open.
Qed.

(* AD1l.v:152-156. *)
Lemma tfib_fprintf_rderr_site_cf_sec : (forall H m, AE3h.stderr_after_vfprintf (mrestrict H m) -> est H m) ->
fprintf_s_site_tfa_cf B est 0x1d85a (strB "cli: read error on "%string) nlB.
Proof.
intros ESTV. change 0x1d85a with AE3kcf.FMT_rderr. unfold fprintf_s_site_tfa_cf.
walk AE2ucf.tfib_fprintf_icpt_rderr WALK.
fps_site_cf ESTV AE2ucf.FP_ENTRY WALK lits_rderr AE3kcf.FMT_rderr.
Qed.

(* AD1l.v:157-161. *)
Lemma tfib_fprintf_usage_site_cf_sec : (forall H m, AE3h.stderr_after_vfprintf (mrestrict H m) -> est H m) ->
fprintf_s_site_tfa_cf B est 0x158b3 (strB "usage: "%string) (strB " INPUT"%string ++ nlB).
Proof.
intros ESTV. change 0x158b3 with AE3ncf.FMT_usage. unfold fprintf_s_site_tfa_cf.
walk AE2wcf.tfib_fprintf_icpt_usage WALK.
fps_site_cf ESTV AE2wcf.FP_ENTRY WALK lits_usage AE3ncf.FMT_usage.
Qed.
End P.

(* ---------------------------------------------------------------------- *)
(* The closed results. *)
Theorem tfib_fwrite_site_cf_A_holds : tfib_fwrite_site_cf_A.
Proof. intros fx rc ci cp B est HB ESTW. eapply tfib_fwrite_site_cf_sec; eassumption. Qed.

Theorem tfib_refused_site_cf_A_holds : tfib_refused_site_cf_A.
Proof. intros fx rc ci cp B est HB ESTV. eapply tfib_refused_site_cf_sec; eassumption. Qed.

Theorem tfib_fprintf_open_site_cf_A_holds : tfib_fprintf_open_site_cf_A.
Proof. intros fx rc ci cp B est HB ESTV. eapply tfib_fprintf_open_site_cf_sec; eassumption. Qed.

Theorem tfib_fprintf_rderr_site_cf_A_holds : tfib_fprintf_rderr_site_cf_A.
Proof. intros fx rc ci cp B est HB ESTV. eapply tfib_fprintf_rderr_site_cf_sec; eassumption. Qed.

Theorem tfib_fprintf_usage_site_cf_A_holds : tfib_fprintf_usage_site_cf_A.
Proof. intros fx rc ci cp B est HB ESTV. eapply tfib_fprintf_usage_site_cf_sec; eassumption. Qed.
