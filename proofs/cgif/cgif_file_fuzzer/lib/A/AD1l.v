(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YK15 YK18 YP0n YM02 YP0m YP09 YP0l YP06 YP08 YP03 YN3q YN3v YI04 YK04 YA0i YA0n YA0e YG00 YG01 YG0f YG0v YG0n YG0s YG0d YCe5 YL02.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v AF0m AD2j AD2i AD1t AD20 AD1v AD2h AD2f AD1w AD1x.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AE2p AE3i AE39 AE3h AE3j AE3k AE3n AE2t AE2u AE2w AD1k.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO05 YO09 YO06 YO01.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AE2k AD1u.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Lemma vf_str_of_bytes : forall (W : world tfibsegs) mem s (str : list byte),
YP03.bytes_at (mrestrict (w_H W) mem) s (str ++ [NUL]) -> ~ In NUL str -> vf_str W mem s str.
Proof.
intros W mem s str HB Hnn. unfold vf_str, aview.
assert (RB : forall j, (j <= length str)%nat -> YP09.mbyte tfibsegs (mrestrict (w_H W) mem) (s + Z.of_nat j) = Some (nth j (str ++ [NUL]) NUL)).
{ intros j Hj. rewrite (YP03.bytes_at_mbyte tfibsegs _ _ _ j HB) by (rewrite length_app; cbn; lia).
apply nth_error_nth'. rewrite length_app; cbn; lia. }
split; [|split].
- intros i Hi. rewrite (RB i) by lia. rewrite app_nth1 by exact Hi. cbn. rewrite (nth_indep _ NUL 0%bv) by exact Hi. reflexivity.
- rewrite (RB (length str)) by lia. rewrite app_nth2 by lia. rewrite Nat.sub_diag. reflexivity.
- apply Forall_forall. intros b Hb Hz. apply Hnn. replace NUL with b; [exact Hb|].
apply bv_eq. rewrite Hz. reflexivity.
Qed.
Lemma vf_tail_of_site : forall (W : world tfibsegs) mem s L,
(forall a, s + L < a < s + L - (s + L) mod 8 + 8 -> mrestrict (w_H W) mem (Z_to_bv 64 a) <> None) -> vf_tail W mem s L.
Proof.
intros W mem s L HT a Ha. unfold aview, YP09.mbyte. pose proof (HT a Ha) as Hm.
destruct (mrestrict (w_H W) mem (Z_to_bv 64 a)) as [b|]; [cbn; discriminate | exfalso; apply Hm; reflexivity].
Qed.
Lemma lits_open : map (Z_to_bv 8) lit_open1 = strB "cli: cannot open "%string /\ map (Z_to_bv 8) lit_open2 = nlB.
Proof. vm_compute. split; reflexivity. Qed.
Lemma lits_rderr : map (Z_to_bv 8) lit_rderr1 = strB "cli: read error on "%string /\ map (Z_to_bv 8) lit_rderr2 = nlB.
Proof. vm_compute. split; reflexivity. Qed.
Lemma lits_usage : map (Z_to_bv 8) lit_usage1 = strB "usage: "%string /\ map (Z_to_bv 8) lit_usage2 = (strB " INPUT"%string ++ nlB).
Proof. vm_compute. split; reflexivity. Qed.
Lemma lens_lits : length (strB "cli: cannot open "%string) = 17%nat /\ length (strB "cli: read error on "%string) = 19%nat /\
length (strB "usage: "%string) = 7%nat /\ length (strB " INPUT"%string ++ nlB) = 7%nat /\ length nlB = 1%nat.
Proof. vm_compute. repeat split; reflexivity. Qed.
Section d.
Variable B : asyms.
Hypothesis HB : TfibSyms B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis TL : TfibSyms B.
Lemma band_zero_shadow : forall ly S W mem md, AR tfibsegs B ly S W mem md -> ly_stk_lo ly = ASAN_CEIL -> ly_stk_hi ly = kHighMemEnd ->
zero_shadow (aview tfibsegs (w_H W) mem) SHADOW_OFF ASAN_CEIL (kHighMemEnd - ASAN_CEIL).
Proof.
intros ly S W mem md HAR Hlo Hhi. rewrite <- Hlo, <- Hhi.
exact (al_zshadow _ _ LAWS ly S W mem md (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly) HAR ltac:(unfold zero_shadow_ranges; left; reflexivity)).
Qed.
Lemma band_hull_zero : forall ly S W mem md p n, AR tfibsegs B ly S W mem md -> ly_stk_lo ly = ASAN_CEIL -> ly_stk_hi ly = kHighMemEnd ->
ASAN_CEIL <= p -> p + n <= kHighMemEnd -> 0 < n ->
forall s, shadow_addr p / 8 * 8 <= s < shadow_addr (p + n - 1) / 8 * 8 + 8 -> aview tfibsegs (w_H W) mem s = Some 0.
Proof.
intros ly S W mem md p n HAR Hlo Hhi Hp Hn Hn0 s Hs. pose proof (band_zero_shadow ly S W mem md HAR Hlo Hhi) as HZ.
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
Lemma band_shadow_facts : forall ly S W mem md p n, AR tfibsegs B ly S W mem md -> ly_stk_lo ly = ASAN_CEIL -> ly_stk_hi ly = kHighMemEnd ->
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
- intros x Hx. apply (zero_shadow_range _ SHADOW_OFF ASAN_CEIL (kHighMemEnd - ASAN_CEIL) M1 M2 (band_zero_shadow ly S W mem md HAR Hlo Hhi) x).
unfold ASAN_CEIL, kHighMemEnd in *; lia.
- intros s Hs. rewrite (band_hull_zero ly S W mem md p n HAR Hlo Hhi Hp Hn Hn0 s Hs). discriminate.
Qed.
Local Ltac fps_site FPE THM LITS :=
intros ly S W regs mem md E s str T HPRE G10 G11 G12 Hlen Hnn Hs1 Hs2 HBr Htail HIMG Hfd HAI HPOST;
change (cfg_at tfibsegs A_icpt_fprintf regs mem md) with (cfg_at tfibsegs FPE regs mem md);
pose proof (icpt_pre_facts B ly S W regs mem md HPRE) as (HEPRE & Hslo & Hwin & Hpres); pose proof (proj1 HEPRE) as HAR;
pose proof HPRE as (_ & _ & _ & _ & _ & _ & _ & Hshi & _);
pose proof (img_facts E _ HIMG) as (IR1 & IR2 & IR3 & Vcan);
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5); pose proof LITS as [ME1 ME2]; pose proof lens_lits as (N1 & N2 & N3 & N4 & N5);
assert (HFPI1 : AE2t.FPI_STK = 9216) by reflexivity; assert (HFPI2 : AE2u.FPI_STK = 9216) by reflexivity;
assert (HFPI3 : AE2w.FPI_STK = 9216) by reflexivity; assert (HDS : DIAG_STK = 16384) by reflexivity;
assert (HFE : F_STDERR = 0xa2578) by reflexivity; assert (HFS : FILE_SZ = 232) by reflexivity;
assert (KHI : kHighMemEnd = 2 ^ 47) by reflexivity; pose proof (icpt_pre_room B ly S W regs mem md HPRE) as Hroom;
pose proof (band_shadow_facts ly S W mem md s (Z.of_nat (length str) + 1) HAR Hslo Hshi
ltac:(rewrite <- Hslo; lia) ltac:(lia) ltac:(lia)) as [HRA HHV];
unfold wr; rewrite <- ME1, <- ME2;
apply (THM ly S W regs mem md ch_stderr s str (Z.of_nat (length str)) (bv_unsigned (sv_denot E (SOff 41 0))) T HEPRE);
[ unfold AE2t.FPI_STK, AE2u.FPI_STK, AE2w.FPI_STK in *; lia
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
| apply (file_is_img _ 664880 665712); [exact IR3 | exact stderr_img_chk |];
unfold stderr_fields; rewrite HFE; repeat (apply Forall_cons; [cbn; lia|]); apply Forall_nil
| intros a Ha; unfold vf_file in Ha; apply (tfib_low_not_owned B ly S W mem md a HAR); [unfold AF0x.TFIB_IMG_LO, AF0x.TFIB_IMG_END; lia|];
apply (tfib_not_owned_static B F_STDERR (F_STDERR + FILE_SZ) a HB); [vm_compute; reflexivity | exact Ha]
| eapply val_mem_img; [exact IR2 | unfold A_GOT_canary; lia | unfold A_GOT_canary; cbn; lia | exact got_canary_chk]
| exact Vcan
| exact (u64_range (sv_denot E (SOff 41 0)))
| exact (ro_img_of_IMG E _ HIMG)
| apply (rodata_hull_zero B HB LAWS ly S W mem md); [exact HAR | unfold FMT_open, FMT_rderr, FMT_usage; lia | unfold FMT_open, FMT_rderr, FMT_usage; lia | lia]
| split; [exact Hfd | reflexivity]
| exact HAI
| intros regs' mem' md' HAR' HP' Hsbm' Ha0' HFW' Hfr' Hpr' HAI';
apply (HPOST regs' mem' md' HAR' HP' Hsbm');
[ etransitivity; [exact Ha0' | f_equal; rewrite ?N1, ?N2, ?N3, ?N4, ?N5; lia]
| apply est_after_vf; exact HFW'
| intros a Ha Hb Hf; apply (Hfr' a Ha); [lia|]; unfold vf_file; unfold STDERR_MUT, F_STDERR_LO, F_STDERR_HI in Hf; rewrite HFE, HFS; exact Hf
| intros a Ha Hf Hp; apply (Hpr' a Ha); [|exact Hp]; unfold vf_file; unfold STDERR_MUT, F_STDERR_LO, F_STDERR_HI in Hf; rewrite HFE, HFS; exact Hf
| exact HAI' ] ].
Theorem tfib_fprintf_open_site : fprintf_s_site_tfa B est 0x1d727 (strB "cli: cannot open "%string) nlB.
Proof.
change 0x1d727 with FMT_open. unfold fprintf_s_site_tfa.
fps_site AE2t.FP_ENTRY (tfib_fprintf_icpt_open B LAWS HB TL) lits_open.
Qed.
Theorem tfib_fprintf_rderr_site : fprintf_s_site_tfa B est 0x1d73c (strB "cli: read error on "%string) nlB.
Proof.
change 0x1d73c with FMT_rderr. unfold fprintf_s_site_tfa.
fps_site AE2u.FP_ENTRY (tfib_fprintf_icpt_rderr B LAWS HB TL) lits_rderr.
Qed.
Theorem tfib_fprintf_usage_site : fprintf_s_site_tfa B est 0x15859 (strB "usage: "%string) (strB " INPUT"%string ++ nlB).
Proof.
change 0x15859 with FMT_usage. unfold fprintf_s_site_tfa.
fps_site AE2w.FP_ENTRY (tfib_fprintf_icpt_usage B LAWS HB TL) lits_usage.
Qed.
End d.
End c.
