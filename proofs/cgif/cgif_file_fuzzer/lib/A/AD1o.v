(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YK0i YK15 YK18 YP0n YM02 YP0m YP09 YP0l YP06 YP08 YP03 YN3q YN3v YI04 YK04 YA0i YA0n YA0e YG00 YG01 YG0f YG0v YG0n YG0s YG0d YCe5 YL02.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v AF0m AD2j AD2i AD1t AD20 AD1v AD2h AD2f AD1w AD1x AE22 ACeg.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AE3f AE2p AE3i AE39 AE3h AE3m AF0x AE2y AE31 AE32 AE36 AE2v AE35 AD1k.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO05 YO09 YO06 YO01.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AE2k AD1u.
Section e. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Lemma rom_seg1 : forall a, 0x10000 <= a < 0x30000 -> in_ro_tfa a.
Proof.
intros a Ha. left.
assert (P : nth_error (map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s), seg_writable s)) tfibsegs) 0 = Some (65536, 131072, false)) by (vm_compute; reflexivity).
destruct tfibsegs as [|s1 rest]; [discriminate|]. cbn [map nth_error] in P. injection P as P1 P2 P3.
exists s1. split; [left; reflexivity|]. split; [exact P3|]. lia.
Qed.
Lemma img_rd_of_arodata : forall (B : asyms) (H : word -> bool) m lo hi, TfibSyms B ->
arodata_ok B (aview tfibsegs H m) -> (forall a, lo <= a < hi -> in_ro_tfa a) ->
forallb (fun r => (fst r + snd r <=? lo) || (hi <=? fst r)) Tfib_owned_static = true -> img_rd (mrestrict H m) lo hi.
Proof.
intros B H m lo hi TB HRO Hro Hst. apply img_rd_of_aview. intros a Ha. apply HRO; [apply Hro; exact Ha | exact (tfib_not_owned_static B lo hi a TB Hst Ha) |].
rewrite (ts_errno B TB). unfold TFIB_ERRNO. pose proof (Hro a Ha) as Hr.
destruct Hr as [Hr|Hr]; [pose proof (tfib_rom_low a Hr); lia | lia].
Qed.
Lemma img_ro_chunks_unowned :
forallb (fun c => forallb (fun r => (fst r + snd r <=? YP09.c_off c) || (YP09.c_off c + c_len c <=? fst r)) Tfib_owned_static) img_ro_chunks = true.
Proof. vm_compute. reflexivity. Qed.
Lemma ro_img_of_arodata : forall (B : asyms) (H : word -> bool) m, TfibSyms B -> arodata_ok B (aview tfibsegs H m) -> ro_img (mrestrict H m).
Proof.
intros B H m TB HRO E. unfold img_ro_region.
split; [cbn; unfold IMG_RO_LO; lia|]. split; [cbn; unfold IMG_RO_HI; lia|]. split; [intros o Ho; cbn in Ho; lia|].
cbn [YP09.r_chunks YP09.r_base base_val]. apply Forall_forall. intros c Hc i Hi.
pose proof (proj1 (Forall_forall _ _) img_ro_chunks_inside c Hc) as (Hlo & Hhi & n & Hv).
pose proof (proj1 (forallb_forall _ _) img_ro_chunks_unowned c Hc) as Hown. cbn beta in Hown.
pose proof (proj1 (forallb_forall _ _) img_ro_bytes_ok c Hc) as Hz. cbn beta in Hz.
destruct c as [co cv]. cbn [YP09.c_off YP09.c_val] in Hv. subst cv. cbn [YP09.c_off YP09.c_val c_len cv_len] in *. cbn [cbyte]. rewrite !Z.add_0_l.
pose proof (zallb_sound _ _ _ (co + i) Hz ltac:(lia)) as Hb.
rewrite (img_rd_of_arodata B H m co (co + n) TB HRO ltac:(intros a Ha; apply rom_seg1; unfold IMG_RO_LO, IMG_RO_HI in *; lia) Hown (co + i)) by lia.
unfold img_byte_ok in Hb. destruct (img_byte tfibsegs (co + i)) as [b|]; [|discriminate]. exists b. split; reflexivity.
Qed.
Lemma got_canary_of_arodata : forall (B : asyms) ly S (W : world tfibsegs) mem md, TfibSyms B -> AR tfibsegs B ly S W mem md ->
val_mem tfibsegs (mrestrict (w_H W) mem) A_GOT_canary 8 A_canary.
Proof. intros B ly S W mem md TB HAR. exact (got_canary_of_AR B TB ly S W mem md HAR). Qed.
Lemma canary_readable : forall (H : word -> bool) m, exists cval, val_mem tfibsegs (mrestrict H m) A_canary 8 cval /\ 0 <= cval < 2 ^ 64.
Proof.
intros H m. destruct (rdword_img_some H m A_canary ltac:(vm_compute; reflexivity)) as (v & Hv & Hr).
exists v. split; [exact (val_mem_of_rdword H m A_canary v Hv) | exact Hr].
Qed.
Lemma stdout_img_chk : img_cells_chk F_STDOUT stdout_fields0 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma stdout_pristine_img : forall H m, stdout_img H m -> stdout_pristine (mrestrict H m).
Proof.
intros H m Hi. apply (ofile_is_img _ STDOUT_LO STDOUT_HI); [apply img_rd_of_aview; exact Hi | exact stdout_img_chk |].
unfold stdout_fields0, F_STDOUT, STDOUT_LO, STDOUT_HI. repeat (apply Forall_cons; [cbn; lia|]). apply Forall_nil.
Qed.
Section f.
Variable B : asyms.
Hypothesis HB : TfibSyms B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis TL : TfibSyms B.
Lemma ocpy_of_icpt : aintrin_realizes tfibsegs B OCpy (pc_wrap_memcpy (as_code B)).
Proof. rewrite (ts_code B HB). exact (memcpy_icpt_realizes B LAWS HB). Qed.
Lemma oset_of_icpt : aintrin_realizes tfibsegs B OSet (pc_wrap_memset (as_code B)).
Proof.
rewrite (ts_code B HB). intros ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn Hdst Ham Hra Hhull _.
exact (memset_icpt_realizes B LAWS HB ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn Hdst Hra Hhull Ham).
Qed.
Lemma bss_zero_shadow : forall ly S W mem md, AR tfibsegs B ly S W mem md ->
zero_shadow (aview tfibsegs (w_H W) mem) SHADOW_OFF 0xa2930 (0x5fb000 - 0xa2930).
Proof.
intros ly S W mem md HAR.
exact (al_zshadow _ _ LAWS ly S W mem md (0xa2930, 0x5fb000 - 0xa2930) HAR
ltac:(unfold zero_shadow_ranges; right; rewrite (ts_zsh B HB); cbn; tauto)).
Qed.
Lemma bss_shadow_facts : forall ly S W mem md p n, AR tfibsegs B ly S W mem md -> 0xa2960 <= p -> p + n <= 0x5fb000 -> 0 < n ->
range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF p n /\ shadow_hull_vis (aview tfibsegs (w_H W) mem) p n.
Proof.
intros ly S W mem md p n HAR Hp Hn Hn0. pose proof (bss_zero_shadow ly S W mem md HAR) as HZ. split.
- intros x Hx. apply (zero_shadow_range _ SHADOW_OFF 0xa2930 (0x5fb000 - 0xa2930) eq_refl eq_refl HZ x). lia.
- intros s Hs. unfold shadow_addr in Hs.
assert (L1 : 0xa2960 / 8 <= p / 8) by (apply Z.div_le_mono; lia).
assert (L2 : (p + n - 1) / 8 <= (0x5fb000 - 1) / 8) by (apply Z.div_le_mono; lia).
change (0xa2960 / 8) with 83244 in L1. change ((0x5fb000 - 1) / 8) with 783871 in L2.
pose proof (Z.div_mod (SHADOW_OFF + p / 8) 8 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound (SHADOW_OFF + p / 8) 8 ltac:(lia)) as D1'.
pose proof (Z.div_mod (SHADOW_OFF + (p + n - 1) / 8) 8 ltac:(lia)) as D2. pose proof (Z.mod_pos_bound (SHADOW_OFF + (p + n - 1) / 8) 8 ltac:(lia)) as D2'.
replace s with (shadow_of_addr SHADOW_OFF 0xa2930 + (s - shadow_of_addr SHADOW_OFF 0xa2930)) by lia.
rewrite (HZ (s - shadow_of_addr SHADOW_OFF 0xa2930)); [discriminate|].
unfold shadow_of_addr, SHADOW_OFF in *. change (665904 / 8) with 83238. change ((6270976 - 665904) / 8) with 700634. lia.
Qed.
Lemma fdchan_stdout : forall md, (forall k, fd_lookup (m_fds md) k = fd_lookup APSG.fds_std k) -> fdchan (Z_to_bv 64 1) ch_stdout md.
Proof. intros md Hf. unfold fdchan. rewrite (Hf (Z_to_bv 64 1)). split; [vm_compute; reflexivity | reflexivity]. Qed.
Lemma printf_pre_facts : forall ly S W regs mem md, printf_pre B ly S W regs mem md ->
ecall_pre tfibsegs B ly S W regs mem md /\
sp_window_lo - 2400 <= spZ regs /\ spZ regs + 32 <= 2 ^ 47 /\ ly_stk_lo ly + VPI_STK <= spZ regs /\ spZ regs mod 16 = 0 /\ YK0s.ret_ok (getr regs 1) /\
raZ regs = RA_EMIT /\ (forall a, spZ regs - PF_STK <= a < spZ regs -> apresent (w_H W) mem a) /\
arodata_ok B (aview tfibsegs (w_H W) mem) /\
getr regs 10 = w64 FMT /\ getr regs 11 = w64 (spZ regs + 24) /\
val_mem tfibsegs (mrestrict (w_H W) mem) (spZ regs + 24) 8 0.
Proof.
intros ly S W regs mem md (HAR & Hra & Hal & Hwlo & Htop & Hsphi & Hslo & Hshi & HRO & Hpres & Hgp & Htp & G10 & G11 & Hrd).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HPF : PF_STK = 9216) by reflexivity. assert (HVP : VPI_STK = 9200) by reflexivity.
assert (Hret : YK0s.ret_ok (getr regs 1)).
{ rewrite <- (Z_to_bv_bv_unsigned 64 (getr regs 1)). change (bv_unsigned (getr regs 1)) with (raZ regs). rewrite Hra. apply ret_ok_lit; [unfold RA_EMIT; lia | reflexivity]. }
pose proof (am_layout _ _ _ _ (proj1 HAR)) as LO. pose proof (lo_top _ LO) as (T1 & _).
split.
{ split; [exact HAR|]. split; [exact Hret|]. split; [exact Hal|].
split; [unfold ly_bot, kStackSpan, ESTACK in *; lia|].
split; [rewrite Hshi; unfold kHighMemEnd, sp_window_hi in *; lia|].
split; [intros a Ha; apply Hpres; unfold ESTACK in Ha; lia|]. exact (conj Hgp Htp). }
split; [unfold sp_window_lo in *; lia|]. split; [unfold sp_window_hi in *; lia|].
split; [rewrite HVP; unfold ly_bot, kStackSpan in *; lia|]. split; [exact Hal|]. split; [exact Hret|]. split; [exact Hra|].
split; [exact Hpres|]. split; [exact HRO|]. split; [exact G10|]. split; [exact G11|].
exact (val_mem_of_rdword (w_H W) mem _ 0 Hrd).
Qed.
Lemma regs_back : forall (regs regs1 regs2 regs3 : bvmap 5 word),
getr regs1 3 = getr regs 3 -> getr regs1 4 = getr regs 4 ->
(forall (r : bv 5) i, Z.of_nat i = bv_unsigned r -> In (Z.of_nat i) KEPTA -> getr regs1 r = getr regs r) ->
aregs_preserved regs1 regs2 ->
getr regs3 2 = getr regs 2 -> getr regs3 1 = getr regs 1 -> getr regs3 8 = getr regs 8 -> getr regs3 9 = getr regs 9 -> getr regs3 18 = getr regs 18 ->
(forall (r : bv 5) i, Z.of_nat i = bv_unsigned r -> In (Z.of_nat i) [3; 4; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31] ->
getr regs3 r = getr regs2 r) ->
aregs_preserved regs regs3 /\ getr regs3 10 = getr regs2 10.
Proof.
intros regs regs1 regs2 regs3 Q3 Q4 RK HP P2 P1 P8 P9 P18 PK. split; [| exact (PK 10%bv 10%nat eq_refl ltac:(cbn; tauto))].
intros r Hr. unfold acallee_saved in Hr.
assert (T : forall z (rr : bv 5) i, rr = Z_to_bv 5 z -> Z.of_nat i = bv_unsigned rr ->
In (Z.of_nat i) [3; 4; 19; 20; 21; 22; 23; 24; 25; 26; 27] -> acallee_saved z -> getr regs3 rr = getr regs rr).
{ intros z rr i Hrr Hi Hin Hcs. rewrite (PK rr i Hi) by (cbn; cbn in Hin; tauto).
rewrite Hrr, (HP z Hcs), <- Hrr. destruct Hin as [Hi3|[Hi4|Hin]].
- assert (rr = 3%bv) by (subst rr; apply bv_eq; rewrite <- Hi, <- Hi3; reflexivity). subst rr. rewrite H. rewrite H in *. exact Q3.
- assert (rr = 4%bv) by (subst rr; apply bv_eq; rewrite <- Hi, <- Hi4; reflexivity). rewrite H in *. exact Q4.
- apply (RK rr i Hi). cbn. cbn in Hin. tauto. }
destruct Hr as [-> | [-> | [-> | [-> | [-> | Hr]]]]].
- replace (Z_to_bv 5 2) with (2%bv : bv 5) by (apply bv_eq; reflexivity). exact P2.
- exact (T 3 (Z_to_bv 5 3) 3%nat eq_refl eq_refl ltac:(cbn; tauto) ltac:(unfold acallee_saved; lia)).
- exact (T 4 (Z_to_bv 5 4) 4%nat eq_refl eq_refl ltac:(cbn; tauto) ltac:(unfold acallee_saved; lia)).
- replace (Z_to_bv 5 8) with (8%bv : bv 5) by (apply bv_eq; reflexivity). exact P8.
- replace (Z_to_bv 5 9) with (9%bv : bv 5) by (apply bv_eq; reflexivity). exact P9.
- assert (Hc : r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
destruct Hc as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]].
+ replace (Z_to_bv 5 18) with (18%bv : bv 5) by (apply bv_eq; reflexivity). exact P18.
+ exact (T 19 (Z_to_bv 5 19) 19%nat eq_refl eq_refl ltac:(cbn; tauto) ltac:(unfold acallee_saved; lia)).
+ exact (T 20 (Z_to_bv 5 20) 20%nat eq_refl eq_refl ltac:(cbn; tauto) ltac:(unfold acallee_saved; lia)).
+ exact (T 21 (Z_to_bv 5 21) 21%nat eq_refl eq_refl ltac:(cbn; tauto) ltac:(unfold acallee_saved; lia)).
+ exact (T 22 (Z_to_bv 5 22) 22%nat eq_refl eq_refl ltac:(cbn; tauto) ltac:(unfold acallee_saved; lia)).
+ exact (T 23 (Z_to_bv 5 23) 23%nat eq_refl eq_refl ltac:(cbn; tauto) ltac:(unfold acallee_saved; lia)).
+ exact (T 24 (Z_to_bv 5 24) 24%nat eq_refl eq_refl ltac:(cbn; tauto) ltac:(unfold acallee_saved; lia)).
+ exact (T 25 (Z_to_bv 5 25) 25%nat eq_refl eq_refl ltac:(cbn; tauto) ltac:(unfold acallee_saved; lia)).
+ exact (T 26 (Z_to_bv 5 26) 26%nat eq_refl eq_refl ltac:(cbn; tauto) ltac:(unfold acallee_saved; lia)).
+ exact (T 27 (Z_to_bv 5 27) 27%nat eq_refl eq_refl ltac:(cbn; tauto) ltac:(unfold acallee_saved; lia)).
Qed.
Lemma printf_site : forall ly S W regs mem md T (k' : nat) (TT : TSet)
(REAL : forall regs1 mem1 md1,
ecall_pre tfibsegs B ly S W regs1 mem1 md1 ->
spZ regs1 = spZ regs - 96 ->
getr regs1 10 = w64 F_STDOUT -> getr regs1 11 = w64 FMT_d -> getr regs1 12 = w64 (spZ regs + 24) ->
(forall a, vf_band (spZ regs1) a -> apresent (w_H W) mem1 a) ->
val_mem tfibsegs (mrestrict (w_H W) mem1) (spZ regs + 24) 8 0 ->
(forall a, vo_file a \/ STDOUT_BUFA <= a < STDOUT_BUFA + STDOUT_BSZ -> ~ aowned B ly S a) ->
val_mem tfibsegs (mrestrict (w_H W) mem1) A_GOT_canary 8 A_canary ->
ro_img (mrestrict (w_H W) mem1) ->
range_addressable (aview tfibsegs (w_H W) mem1) SHADOW_OFF STDOUT_BUFA STDOUT_BSZ -> shadow_hull_vis (aview tfibsegs (w_H W) mem1) STDOUT_BUFA STDOUT_BSZ ->
range_addressable (aview tfibsegs (w_H W) mem1) SHADOW_OFF FMT_d 4 -> shadow_hull_vis (aview tfibsegs (w_H W) mem1) FMT_d 4 ->
fdchan (Z_to_bv 64 1) ch_stdout md1 -> AI tfibsegs (w_H W) (w_A W) md1 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - VP_WIN <= a < spZ regs) -> aview tfibsegs (w_H W) mem1 a = aview tfibsegs (w_H W) mem a) ->
(forall regs2 mem2 md2 (wp : Z),
AR tfibsegs B ly S W mem2 md2 -> aregs_preserved regs1 regs2 -> same_but_materialized md1 md2 -> getr regs2 10 = w64 2 ->
xst k' (w_H W) mem2 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ vf_band (spZ regs1) a -> ~ STDOUT_MUT a -> aview tfibsegs (w_H W) mem2 a = aview tfibsegs (w_H W) mem1 a) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ STDOUT_MUT a -> apresent (w_H W) mem1 a -> apresent (w_H W) mem2 a) ->
AI tfibsegs (w_H W) (w_A W) md2 ->
srealizes tfibsegs (cfg_at tfibsegs (raZ regs1) regs2 mem2 md2) T) ->
srealizes tfibsegs (cfg_at tfibsegs A_vfprintf regs1 mem1 md1) TT),
printf_pre B ly S W regs mem md -> (forall k, fd_lookup (m_fds md) k = fd_lookup APSG.fds_std k) -> AI tfibsegs (w_H W) (w_A W) md ->
printf_post B xst ly S W regs mem md k' T ->
srealizes tfibsegs (cfg_at tfibsegs A_icpt_vprintf regs mem md) TT.
Proof.
intros ly S W regs mem md T k' TT REAL HPRE Hfds HAI HPOST.
pose proof (printf_pre_facts ly S W regs mem md HPRE) as (HEPRE & Hsp44 & Hsphi & Hstk & Hal & Hret & Hra & Hpres & HRO & G10 & G11 & Harg).
pose proof (proj1 HEPRE) as HAR. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). unfold sp_window_lo in Hsp44.
assert (HPF : PF_STK = 9216) by reflexivity. assert (HVP : VPI_STK = 9200) by reflexivity. assert (HVF : VF_STK = 9104) by reflexivity.
assert (HVW : VP_WIN = 2432) by reflexivity.
assert (HFO : F_STDOUT = 0xa2668) by reflexivity. assert (HFS : FILE_SZ = 232) by reflexivity.
assert (HBA : STDOUT_BUFA = 0x5f96a0) by reflexivity. assert (HBS : STDOUT_BSZ = 1024) by reflexivity.
change (cfg_at tfibsegs A_icpt_vprintf regs mem md) with (cfg_at tfibsegs VP_ENTRY regs mem md).
apply (tfib_vprintf_icpt_A B LAWS HB ly S W regs mem md _ HEPRE Hstk ltac:(intros a Ha; apply Hpres; lia) Hsphi G10 G11 Harg
(ro_img_of_arodata B (w_H W) mem HB HRO)
(rodata_hull_zero B HB LAWS ly S W mem md FMT 4 HAR ltac:(unfold FMT; lia) ltac:(unfold FMT; lia) ltac:(lia)) HAI).
intros regs1 mem1 md1 HPRE1 R1sp R1ra Q10 Q11 Q12 Q3 Q4 RK MF1 MEQ1 AV1 PM1 SAVED HAI1.
pose proof (proj1 HPRE1) as HAR1.
apply (REAL regs1 mem1 md1 HPRE1 R1sp Q10 Q11 Q12).
- intros a Ha. unfold vf_band in Ha. rewrite R1sp in Ha. apply PM1. apply Hpres. lia.
- eapply val_mem_keptA; [|exact Harg]. intros b Hb. apply AV1; [lia | cbn in Hb; lia].
- intros a Ha. apply (tfib_low_not_owned B ly S W mem md a HAR); [unfold vo_file, AF0x.TFIB_IMG_LO, AF0x.TFIB_IMG_END in *; lia|].
destruct Ha as [Ha|Ha].
+ apply (tfib_not_owned_static B F_STDOUT (F_STDOUT + FILE_SZ) a HB); [vm_compute; reflexivity | unfold vo_file in Ha; exact Ha].
+ apply (tfib_not_owned_static B STDOUT_BUFA (STDOUT_BUFA + STDOUT_BSZ) a HB); [vm_compute; reflexivity | exact Ha].
- eapply val_mem_keptA; [|exact (got_canary_of_arodata B ly S W mem md HB HAR)]. intros b Hb. apply AV1; [unfold A_GOT_canary in Hb; cbn in Hb; lia | unfold A_GOT_canary in Hb; cbn in Hb; lia].
- apply (ro_img_kept _ mem mem1); [| exact (ro_img_of_arodata B (w_H W) mem HB HRO)].
intros x Hx. apply MEQ1. unfold IMG_RO_LO, IMG_RO_HI, VP_WIN in *. lia.
- exact (proj1 (bss_shadow_facts ly S W mem1 md1 STDOUT_BUFA STDOUT_BSZ HAR1 ltac:(lia) ltac:(lia) ltac:(lia))).
- exact (proj2 (bss_shadow_facts ly S W mem1 md1 STDOUT_BUFA STDOUT_BSZ HAR1 ltac:(lia) ltac:(lia) ltac:(lia))).
- exact (proj1 (rodata_shadow_facts B HB LAWS ly S W mem1 md1 FMT_d 4 HAR1 ltac:(unfold FMT_d; lia) ltac:(unfold FMT_d; lia) ltac:(lia))).
- exact (proj2 (rodata_shadow_facts B HB LAWS ly S W mem1 md1 FMT_d 4 HAR1 ltac:(unfold FMT_d; lia) ltac:(unfold FMT_d; lia) ltac:(lia))).
- eapply fdchan_sbm; [exact (fdchan_stdout md Hfds) | exact MF1].
- exact HAI1.
- exact AV1.
-
intros regs2 mem2 md2 wp HAR2 HP2 Hsbm2 Ha02 HX2 Hfr2 Hpm2 HAI2.
rewrite R1ra.
assert (R2sp : getr regs2 2 = w64 (spZ regs - 96)).
{ replace (2%bv : bv 5) with (Z_to_bv 5 2) by (apply bv_eq; reflexivity). rewrite (HP2 2 ltac:(unfold acallee_saved; lia)).
unfold w64. rewrite <- R1sp. unfold spZ. rewrite Z_to_bv_bv_unsigned. reflexivity. }
apply (tfib_vprintf_icpt_E W regs regs2 mem2 md2 T ltac:(lia) Hsphi Hal Hret R2sp).
+ apply (vpf_saved_kept regs (w_H W) mem1 mem2); [exact SAVED|]. intros b Hb. apply Hfr2; [lia | unfold vf_band; rewrite R1sp; lia |].
unfold STDOUT_MUT, STDOUT_LO, STDOUT_HI, SOBUF_LO, SOBUF_HI. lia.
+ exact HAI2.
+ intros regs3 mem3 md3 MEQ3 P2 P1 P8 P9 P18 PK Hsbm3 HAI3.
destruct (regs_back regs regs1 regs2 regs3 Q3 Q4 RK HP2 P2 P1 P8 P9 P18 PK) as [HP3 Ha03].
assert (AV3 : forall a, aview tfibsegs (w_H W) mem3 a = aview tfibsegs (w_H W) mem2 a) by (intros a; apply aview_same; apply MEQ3).
apply (HPOST regs3 mem3 md3).
* apply (al_frame _ _ LAWS ly S W mem2 md2 mem3 _ HAR2); [intros; apply AV3 | intros a Hv; rewrite AV3; exact Hv | | | | exact (AE2y.hs_kept_eq _ _ _ MEQ3)];
apply (same_but_materialized_frame md2 _ Hsbm3).
* exact HP3.
* eapply same_but_materialized_trans; [exact MF1|]. eapply same_but_materialized_trans; [exact Hsbm2 | exact Hsbm3].
* rewrite Ha03. exact Ha02.
* apply (tfib_xst_frame k' (w_H W) (w_H W) mem2 mem3); [exact HX2 | intros a _; apply AV3].
* intros a Hr Hb Hm. rewrite AV3. rewrite HPF in Hb. rewrite Hfr2; [apply AV1; [exact Hr | rewrite HVW; lia] | exact Hr | unfold vf_band; rewrite R1sp, HVF; lia | exact Hm].
* intros a Hr Hm Hp. apply (apresent_same (w_H W) mem2 mem3 a (MEQ3 _)). apply Hpm2; [exact Hr | exact Hm | apply PM1; exact Hp].
* exact HAI3.
Qed.
Theorem tfib_printf_first : printf_first_tfa B xst.
Proof.
intros ly S W regs mem md T HPRE Hnev Himg Hfds HAI HPOST.
assert (HFO : F_STDOUT = 0xa2668) by reflexivity. assert (HFS : FILE_SZ = 232) by reflexivity.
assert (HBA : STDOUT_BUFA = 0x5f96a0) by reflexivity. assert (HBS : STDOUT_BSZ = 1024) by reflexivity. assert (HVW : VP_WIN = 2432) by reflexivity.
assert (LN : line0 = map (Z_to_bv 8) [48; 10]) by (vm_compute; reflexivity). rewrite LN.
refine (printf_site ly S W regs mem md T 1%nat _ _ HPRE Hfds HAI HPOST).
intros regs1 mem1 md1 HPRE1 R1sp Q10 Q11 Q12 Hband Harg Hown Hgot Hro Hra_b Hhull_b Hra_f Hhull_f Hch HAI1 AV1 HK.
pose proof (printf_pre_facts ly S W regs mem md HPRE) as (_ & Hsp44 & Hsphi & Hstk & Hal & _).
destruct (canary_readable (w_H W) mem1) as (cval & Hcan & Hcv).
unfold wr.
apply (tfib_vfprintf_stdout_first B TL LAWS ocpy_of_icpt oset_of_icpt ly S W regs1 mem1 md1 ch_stdout (spZ regs + 24) cval T HPRE1).
- rewrite R1sp. unfold sp_window_lo in Hsp44. lia.
- rewrite R1sp. unfold VF_STK, ESTACK. unfold VPI_STK in Hstk. lia.
- exact Hband.
- exact Q10. - exact Q11. - exact Q12.
- rewrite R1sp. lia. - lia.
- pose proof (Z.div_mod (spZ regs) 16 ltac:(lia)) as Dm. rewrite Hal in Dm. replace (spZ regs + 24) with ((2 * (spZ regs / 16) + 3) * 8) by lia. apply Z_mod_mult.
- exact Harg.
-
pose proof (stdout_pristine_img (w_H W) mem Himg) as HP0. unfold stdout_pristine, ofile_is in *.
apply Forall_forall. intros [[o n] v] Hf. pose proof (proj1 (Forall_forall _ _) HP0 _ Hf) as Hv. cbn beta in Hv.
assert (Ho : 0 <= o /\ o + Z.of_nat (N.to_nat n) <= FILE_SZ).
{ clear - Hf HFS. unfold stdout_fields0 in Hf. cbn in Hf. rewrite HFS.
repeat (destruct Hf as [Hq | Hf]; [injection Hq as <- <- <-; cbn; lia|]). destruct Hf. }
eapply val_mem_keptA; [|exact Hv]. intros b Hb. apply AV1; unfold sp_window_lo, F_STDOUT, FILE_SZ, VP_WIN in *; lia.
- exact Hown. - exact Hgot. - exact Hcan. - exact Hcv. - exact Hro.
- exact Hra_b. - exact Hhull_b. - exact Hch. - exact HAI1.
- intros regs2 mem2 md2 HAR2 HP2 Hsbm2 Ha02 HMID Hfr2 Hpm2 HAI2.
apply (HK regs2 mem2 md2 STDOUT_BUFA HAR2 HP2 Hsbm2 Ha02).
+   split; [lia|]. split; [lia|]. split; [| intros i Hi; cbn in Hi; lia].
replace (STDOUT_BUFA + 2 * (Z.of_nat 1 - 1)) with STDOUT_BUFA by lia. exact HMID.
+ intros a Hr Hb Hm. apply Hfr2; [exact Hr | exact Hb |]. unfold vo_mut, vo_file. unfold STDOUT_MUT, STDOUT_LO, STDOUT_HI, SOBUF_LO, SOBUF_HI in Hm. lia.
+ intros a Hr Hm Hp. apply Hpm2; [exact Hr | | exact Hp]. unfold vo_mut, vo_file. unfold STDOUT_MUT, STDOUT_LO, STDOUT_HI, SOBUF_LO, SOBUF_HI in Hm. lia.
+ exact HAI2.
Qed.
Theorem tfib_printf_next : printf_next_tfa B xst.
Proof.
intros ly S W regs mem md T k HPRE Hnev (Hk1 & Hkb & HMID & HPEND) Hk Hfds HAI HPOST.
assert (HFO : F_STDOUT = 0xa2668) by reflexivity. assert (HFS : FILE_SZ = 232) by reflexivity.
assert (HBA : STDOUT_BUFA = 0x5f96a0) by reflexivity. assert (HBS : STDOUT_BSZ = 1024) by reflexivity. assert (HVW : VP_WIN = 2432) by reflexivity.
refine (printf_site ly S W regs mem md T (Datatypes.S k) T _ HPRE Hfds HAI HPOST).
intros regs1 mem1 md1 HPRE1 R1sp Q10 Q11 Q12 Hband Harg Hown Hgot Hro Hra_b Hhull_b Hra_f Hhull_f Hch HAI1 AV1 HK.
pose proof (printf_pre_facts ly S W regs mem md HPRE) as (_ & Hsp44 & Hsphi & Hstk & Hal & _).
destruct (canary_readable (w_H W) mem1) as (cval & Hcan & Hcv).
set (wp := STDOUT_BUFA + 2 * (Z.of_nat k - 1)) in *.
apply (tfib_vfprintf_stdout_next B TL LAWS ocpy_of_icpt oset_of_icpt ly S W regs1 mem1 md1 (spZ regs + 24) cval wp T HPRE1).
- rewrite R1sp. unfold sp_window_lo in Hsp44. lia.
- rewrite R1sp. unfold VF_STK, ESTACK. unfold VPI_STK in Hstk. lia.
- exact Hband.
- exact Q10. - exact Q11. - exact Q12.
- rewrite R1sp. lia. - lia.
- pose proof (Z.div_mod (spZ regs) 16 ltac:(lia)) as Dm. rewrite Hal in Dm. replace (spZ regs + 24) with ((2 * (spZ regs / 16) + 3) * 8) by lia. apply Z_mod_mult.
- exact Harg.
-
destruct HMID as [HF1 Hwp]. split.
+ unfold ofile_is in *. apply Forall_forall. intros [[o n] v] Hf. pose proof (proj1 (Forall_forall _ _) HF1 _ Hf) as Hv. cbn beta in Hv.
assert (Ho : 0 <= o /\ o + Z.of_nat (N.to_nat n) <= FILE_SZ).
{ clear - Hf HFS. unfold stdout_fields1 in Hf. cbn in Hf. rewrite HFS.
repeat (destruct Hf as [Hq | Hf]; [injection Hq as <- <- <-; cbn; lia|]). destruct Hf. }
eapply val_mem_keptA; [|exact Hv]. intros b Hb. apply AV1; unfold sp_window_lo, F_STDOUT, FILE_SZ, VP_WIN in *; lia.
+ eapply val_mem_keptA; [|exact Hwp]. intros b Hb. cbn in Hb. apply AV1; unfold sp_window_lo, F_STDOUT, FILE_SZ, VP_WIN in *; lia.
- subst wp. lia. - subst wp. lia.
- exact Hown. - exact Hgot. - exact Hcan. - exact Hcv. - exact Hro.
- exact Hra_b. - exact Hhull_b. - exact Hra_f. - exact Hhull_f. - exact HAI1.
- intros regs2 mem2 md2 HAR2 HP2 Hsbm2 Ha02 HMID2 Hb0 Hb1 Hfr2 Hpm2 HAI2.
apply (HK regs2 mem2 md2 wp HAR2 HP2 Hsbm2 Ha02).
+
split; [lia|]. split; [lia|]. split.
* replace (STDOUT_BUFA + 2 * (Z.of_nat (Datatypes.S k) - 1)) with (wp + 2) by (subst wp; lia). exact HMID2.
* intros i Hi. replace (Datatypes.S k - 1)%nat with k in * by lia.
assert (RK' : repeat line0 k = repeat line0 (k - 1) ++ [line0]) by (replace k with ((k - 1) + 1)%nat at 1 by lia; rewrite repeat_app; reflexivity).
rewrite RK', concat_app in *. cbn [concat] in *. rewrite app_nil_r in *.
assert (LL0 : length line0 = 2%nat) by (vm_compute; reflexivity).
rewrite length_app, length_pend, LL0 in Hi.
destruct (Nat.lt_ge_cases i (2 * (k - 1))) as [Hlt|Hge].
-- rewrite app_nth1 by (rewrite length_pend; exact Hlt). rewrite <- (HPEND i ltac:(rewrite length_pend; exact Hlt)).
unfold sp_window_lo in Hsp44.
rewrite Hfr2; [| subst wp; lia | unfold vf_band, VF_STK, ESTACK; rewrite R1sp; subst wp; lia | unfold vo_mut, vo_file; subst wp; lia].
apply AV1; unfold VP_WIN; subst wp; lia.
-- rewrite app_nth2 by (rewrite length_pend; exact Hge). rewrite length_pend.
assert (Hi2 : (i = 2 * (k - 1) \/ i = 2 * (k - 1) + 1)%nat) by lia.
destruct Hi2 as [-> | ->].
++ replace (2 * (k - 1) - 2 * (k - 1))%nat with 0%nat by lia. replace (STDOUT_BUFA + Z.of_nat (2 * (k - 1))) with wp by (subst wp; lia).
rewrite Hb0. vm_compute. reflexivity.
++ replace (2 * (k - 1) + 1 - 2 * (k - 1))%nat with 1%nat by lia. replace (STDOUT_BUFA + Z.of_nat (2 * (k - 1) + 1)) with (wp + 1) by (subst wp; lia).
rewrite Hb1. vm_compute. reflexivity.
+ intros a Hr Hb Hm. apply Hfr2; [exact Hr | exact Hb |]. unfold vo_mut, vo_file. unfold STDOUT_MUT, STDOUT_LO, STDOUT_HI, SOBUF_LO, SOBUF_HI in Hm. subst wp. lia.
+ intros a Hr Hm Hp. apply Hpm2; [exact Hr | | exact Hp]. unfold vo_mut, vo_file. unfold STDOUT_MUT, STDOUT_LO, STDOUT_HI, SOBUF_LO, SOBUF_HI in Hm. subst wp. lia.
+ exact HAI2.
Qed.
End f.
End e.
