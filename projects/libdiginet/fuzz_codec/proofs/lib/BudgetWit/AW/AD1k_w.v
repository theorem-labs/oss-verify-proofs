(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: generated for libdiginet/fuzz_codec image A (asan) by tools/startup/gen_ad1k.py (frozen a93a5ff60645, the start-up tool set) from fuzz_codec.asan, the regions of its generated A/AD2j.v and the owned statics of its generated A/AF0m.v; the donor A/AD1k.v gives the text only *)
(* Modified by Theorem Labs, 2026-11: made from A/AD1k.v for the ASan run at the 16 GiB limit (lib/BudgetWit/AW), with the modules it imports from that set renamed to their twins (suffix _w). *)
(* Modified by Theorem Labs, 2026-11: internal commit ids in comments replaced by public commits or removed. *)
(* Read from: fuzz_codec.asan (libdiginet/fuzz_codec asan) sha256 7d470194ffdbde8b30a9810840f8e81d620ba1c555d510c475daeff37548a422; unstripped twin sha256 b28356da1a6547814e3a3c56e2d9e065e4f5b45715ccb5a236942cda3471fe1d *)
(* Theorem Labs, 2026-11: cut to the declarations the usage path at 16 GiB uses. *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YK15.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.BudgetWit.AW Require Import YK18_w.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YP0n YM02 YP0m YP09 YP0l YP06 YP08 YP03 YN3q YN3v YI04 YK04 YA0i.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.BudgetWit.AW Require Import YA0n_w YA0e_w.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG00 YG01 YG0f YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.BudgetWit.AW Require Import YG0n_w YG0s_w YG0d_w YCe5_w.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YL02.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AB1v AF0m AD2j.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.BudgetWit.AW Require Import AD2i_w AD1t_w AD20_w AD1v_w AD2h_w AD2f_w AD1w_w AD1x_w.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.BudgetWit.AW Require Import AE2p_w.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AE3i.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.BudgetWit.AW Require Import AE39_w AE3h_w AE3m_w AE23_w AE2v_w.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YO05 YO09 YO06 YO01.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.BudgetWit.AW Require Import AE2k_w AD1u_w.
Section c. Context {rc : YM05.RunCeil}.
Definition img_rd (m : word -> option byte) (lo hi : Z) : Prop :=
forall x, lo <= x < hi -> mbyte tfibsegs m x = img_byte tfibsegs x.
Definition img_cell_chk (a : Z) (n : nat) (v : Z) : bool :=
forallb (fun k => match img_byte tfibsegs (a + Z.of_nat k) with
| Some b => Z.eqb (bv_unsigned b) (bv_unsigned (Z_to_bv 8 (le_byte v n k)))
| None => false end) (seq 0 n).
Lemma val_mem_img : forall m lo hi a n v,
img_rd m lo hi -> lo <= a -> a + Z.of_nat n <= hi -> img_cell_chk a n v = true -> val_mem tfibsegs m a n v.
Proof.
intros m lo hi a n v Hrd Hlo Hhi Hc k Hk.
pose proof (proj1 (forallb_forall _ _) Hc k ltac:(apply in_seq; lia)) as Hb. cbn beta in Hb.
rewrite (Hrd (a + Z.of_nat k)) by lia.
destruct (img_byte tfibsegs (a + Z.of_nat k)) as [b|]; [|discriminate]. f_equal. apply bv_eq. apply Z.eqb_eq. exact Hb.
Qed.
Definition img_cells_chk (base : Z) (l : list (Z * N * Z)) : bool :=
forallb (fun f => match f with (o, n, v) => img_cell_chk (base + o) (N.to_nat n) v end) l.
Lemma file_is_img : forall m lo hi flds,
img_rd m lo hi -> img_cells_chk F_STDERR flds = true ->
Forall (fun f => match f with (o, n, _) => lo <= F_STDERR + o /\ F_STDERR + o + Z.of_nat (N.to_nat n) <= hi end) flds ->
file_is flds m.
Proof.
intros m lo hi flds Hrd Hc Hin. unfold file_is. apply Forall_forall. intros [[o n] v] Hf.
pose proof (proj1 (forallb_forall _ _) Hc _ Hf) as H1. cbn beta in H1.
pose proof (proj1 (Forall_forall _ _) Hin _ Hf) as [H2 H3].
eapply val_mem_img; [exact Hrd | exact H2 | exact H3 | exact H1].
Qed.
Lemma ofile_is_img : forall m lo hi flds,
img_rd m lo hi -> img_cells_chk F_STDOUT flds = true ->
Forall (fun f => match f with (o, n, _) => lo <= F_STDOUT + o /\ F_STDOUT + o + Z.of_nat (N.to_nat n) <= hi end) flds ->
ofile_is flds m.
Proof.
intros m lo hi flds Hrd Hc Hin. unfold ofile_is. apply Forall_forall. intros [[o n] v] Hf.
pose proof (proj1 (forallb_forall _ _) Hc _ Hf) as H1. cbn beta in H1.
pose proof (proj1 (Forall_forall _ _) Hin _ Hf) as [H2 H3].
eapply val_mem_img; [exact Hrd | exact H2 | exact H3 | exact H1].
Qed.
Lemma img_rd_of_aview : forall (H : word -> bool) (m : word -> option byte) lo hi,
(forall a, lo <= a < hi -> aview tfibsegs H m a = option_map (fun b : byte => bv_unsigned b) (seg_rom tfibsegs (Z_to_bv 64 a))) ->
img_rd (mrestrict H m) lo hi.
Proof.
intros H m lo hi Hi x Hx. specialize (Hi x Hx). unfold aview in Hi. unfold img_byte.
destruct (mbyte tfibsegs (mrestrict H m) x) as [b|]; destruct (seg_rom tfibsegs (Z_to_bv 64 x)) as [b'|]; cbn in Hi;
[f_equal; apply bv_eq; injection Hi as Hi; exact Hi | discriminate | discriminate | reflexivity].
Qed.
Lemma img_rd_of_region : forall E m r a len,
region_ok tfibsegs E m r -> YP09.r_base r = None -> In (YP09.mkChunk a (CImg len)) (YP09.r_chunks r) ->
img_rd m a (a + len).
Proof.
intros E m r a len (_ & _ & _ & Hcs) Hb Hin x Hx.
pose proof (proj1 (Forall_forall _ _) Hcs _ Hin (x - a) ltac:(cbn; lia)) as (b & Hcb & Hmb).
revert Hcb Hmb. rewrite Hb. cbn [base_val YP09.c_off YP09.c_val cbyte]. rewrite !Z.add_0_l.
replace (a + (x - a)) with x by lia. intros -> ->. reflexivity.
Qed.
Lemma img_rd_of_mem_ok : forall E m rs r a len,
mem_ok tfibsegs E m rs -> In r rs -> YP09.r_base r = None -> In (YP09.mkChunk a (CImg len)) (YP09.r_chunks r) ->
img_rd m a (a + len).
Proof.
intros E m rs r a len (_ & Hrs & _) Hr Hb Hin. eapply img_rd_of_region; [exact (proj1 (Forall_forall _ _) Hrs r Hr) | exact Hb | exact Hin].
Qed.
Lemma val_mem_keptA : forall (H H' : word -> bool) (m m' : word -> option byte) a n v,
(forall b, a <= b < a + Z.of_nat n -> aview tfibsegs H' m' b = aview tfibsegs H m b) ->
val_mem tfibsegs (mrestrict H m) a n v -> val_mem tfibsegs (mrestrict H' m') a n v.
Proof. intros H H' m m' a n v Hk Hv. eapply val_mem_kept; [|exact Hv]. intros k Hk'. apply Hk. lia. Qed.
Definition est (H : word -> bool) (m : word -> option byte) : Prop :=
exists sew, 0 <= sew < 2 ^ 64 /\
val_mem tfibsegs (mrestrict H m) (F_STDERR + 8) 8 0 /\ val_mem tfibsegs (mrestrict H m) (F_STDERR + 16) 8 0 /\
val_mem tfibsegs (mrestrict H m) (F_STDERR + 40) 8 sew /\ val_mem tfibsegs (mrestrict H m) (F_STDERR + 56) 8 sew /\
val_mem tfibsegs (mrestrict H m) (F_STDERR + 140) 4 0xffffffff.
Lemma est_of_fields : forall H m flds v40,
file_is flds (mrestrict H m) ->
In (8, 8%N, 0) flds -> In (16, 8%N, 0) flds -> In (40, 8%N, v40) flds -> In (56, 8%N, v40) flds -> In (140, 4%N, 0xffffffff) flds ->
0 <= v40 < 2 ^ 64 -> est H m.
Proof.
intros H m flds v40 HF I8 I16 I40 I56 I140 Hv. unfold file_is in HF.
pose proof (fun f Hf => proj1 (Forall_forall _ _) HF f Hf) as X.
exists v40. split; [exact Hv|].
split; [exact (X _ I8)|]. split; [exact (X _ I16)|]. split; [exact (X _ I40)|]. split; [exact (X _ I56) | exact (X _ I140)].
Qed.
Lemma est_after_vf : forall H m, stderr_after_vfprintf (mrestrict H m) -> est H m.
Proof. intros H m HF. eapply (est_of_fields H m stderr_fields_after_vf 0 HF); [cbn; tauto .. | lia]. Qed.
Lemma stderr_img_chk : img_cells_chk F_STDERR stderr_fields = true.
Proof. vm_compute. reflexivity. Qed.
Theorem tfib_est_frame : est_frame_tfa est.
Proof.
intros H H' m m' (sew & Hsew & V8 & V16 & V40 & V56 & V140) Heq. exists sew. split; [exact Hsew|].
assert (T : forall a n v, F_STDERR <= a -> a + Z.of_nat n <= F_STDERR + FILE_SZ ->
val_mem tfibsegs (mrestrict H m) a n v -> val_mem tfibsegs (mrestrict H' m') a n v).
{ intros a n v Ha Hn Hv. eapply val_mem_keptA; [|exact Hv]. intros b Hb. apply Heq. unfold STDERR_MUT, F_STDERR_LO, F_STDERR_HI. unfold F_STDERR, FILE_SZ in Ha, Hn. lia. }
unfold F_STDERR, FILE_SZ in T.
repeat split; (apply T; [cbn; unfold F_STDERR; lia | cbn; unfold F_STDERR; lia | assumption]).
Qed.
Definition xst (k : nat) (H : word -> bool) (m : word -> option byte) : Prop :=
(1 <= k)%nat /\ 2 * (Z.of_nat k - 1) + 2 <= STDOUT_BSZ /\
stdout_mid (STDOUT_BUFA + 2 * (Z.of_nat k - 1)) (mrestrict H m) /\
(forall i, (i < length (concat (repeat line0 (k - 1))))%nat ->
aview tfibsegs H m (STDOUT_BUFA + Z.of_nat i) = Some (bv_unsigned (nth i (concat (repeat line0 (k - 1))) (Z_to_bv 8 0)))).
Lemma length_line0 : length line0 = 2%nat. Proof. vm_compute. reflexivity. Qed.
Lemma length_pend : forall k, length (concat (repeat line0 k)) = (2 * k)%nat.
Proof. induction k as [|k IH]; [reflexivity|]. cbn [repeat concat]. rewrite length_app, IH, length_line0. lia. Qed.
Theorem tfib_xst_frame : xst_frame_tfa xst.
Proof.
intros k H H' m m' (Hk & Hb & Hmid & Hpend) Heq. split; [exact Hk|]. split; [exact Hb|].
assert (HBF : STDOUT_BUFA = 6265632) by reflexivity. assert (HBS : STDOUT_BSZ = 1024) by reflexivity. assert (HFF : F_STDOUT = 663992) by reflexivity.
split.
- destruct Hmid as [HF Hwp]. split.
+ unfold ofile_is in *. apply Forall_forall. intros [[o n] v] Hf. pose proof (proj1 (Forall_forall _ _) HF _ Hf) as Hv. cbn beta in Hv.
assert (Ho : 0 <= o /\ o + Z.of_nat (N.to_nat n) <= FILE_SZ).
{ clear - Hf. unfold stdout_fields1 in Hf. cbn in Hf. unfold FILE_SZ.
repeat (destruct Hf as [Hq | Hf]; [injection Hq as <- <- <-; cbn; lia|]). destruct Hf. }
eapply val_mem_keptA; [|exact Hv]. intros b Hb'. apply Heq. unfold STDOUT_MUT, STDOUT_LO, STDOUT_HI. unfold FILE_SZ in Ho. lia.
+ eapply val_mem_keptA; [|exact Hwp]. intros b Hb'. apply Heq. unfold STDOUT_MUT, STDOUT_LO, STDOUT_HI. cbn in Hb'. lia.
- intros i Hi. rewrite <- (Hpend i Hi). apply Heq. unfold STDOUT_MUT, SOBUF_LO, SOBUF_HI.
rewrite length_pend in Hi. lia.
Qed.
Lemma tfib_img_not_owned : forall (B : asyms) ly S (W : world tfibsegs) mem md a,
AR tfibsegs B ly S W mem md -> AF0x_w.TFIB_IMG_LO <= a < AF0x_w.TFIB_IMG_END -> ~ Exists (in_zr a) (as_owned_static B) -> ~ aowned B ly S a.
Proof.
intros B ly S W mem md a (M & L & _) Ha Hst [OW _]. pose proof (am_layout _ _ _ _ M) as LO.
pose proof (AF0x_w.img_cover_of_ledger _ _ _ L) as [I1 I2]. unfold AF0x_w.TFIB_IMG_LO, AF0x_w.TFIB_IMG_END in *.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct OW as [O|[O|[O|[O|O]]]].
- exact (Hst O).
- pose proof (owned_extents_bound ly a LO O) as (_ & _ & X). apply X. unfold in_zr. cbn [fst snd]. lia.
- pose proof (owned_extents_bound ly a LO ltac:(apply Exists_exists; exists (ly_C ly, 256); split; [unfold owned_extents; cbn; tauto | exact O])) as (_ & _ & X).
apply X. unfold in_zr. cbn [fst snd]. lia.
- pose proof (owned_sec_bound B ly S _ a M O) as (_ & _ & X). apply X. unfold in_zr. cbn [fst snd]. lia.
- pose proof (owned_shadow_bound B ly S _ a M O) as X. unfold SHADOW_OFF in X. lia.
Qed.
Lemma tfib_low_not_owned : forall (B : asyms) ly S (W : world tfibsegs) mem md a,
AR tfibsegs B ly S W mem md -> AF0x_w.TFIB_IMG_LO <= a < AF0x_w.TFIB_IMG_END -> ~ Exists (in_zr a) (as_owned_static B) -> ~ aowned B ly S a.
Proof. exact tfib_img_not_owned. Qed.
Lemma tfib_not_owned_static : forall (B : asyms) lo hi a, TfibSyms B ->
forallb (fun r => (fst r + snd r <=? lo) || (hi <=? fst r)) Tfib_owned_static = true -> lo <= a < hi -> ~ Exists (in_zr a) (as_owned_static B).
Proof.
intros B lo hi a TB Hc Ha HE. rewrite (ts_owned B TB) in HE. apply Exists_exists in HE as (r & Hr & [H1 H2]).
pose proof (proj1 (forallb_forall _ _) Hc r Hr) as Hb. cbn beta in Hb. apply Bool.orb_prop in Hb as [Hb|Hb]; apply Z.leb_le in Hb; lia.
Qed.
Lemma img_facts : forall E m, mem_ok tfibsegs E m IMG_REGIONS ->
(img_rd m 0x10560 0x1cdad /\ img_rd m 0x1cdc2 0x20c44) /\ img_rd m 649112 649120 /\ img_rd m 663680 664512 /\ val_mem tfibsegs m A_canary 8 (bv_unsigned (sv_denot E (SOff 41 0))).
Proof.
intros E m HM. split; [split|split; [|split]].
- eapply (img_rd_of_mem_ok E m IMG_REGIONS R_A1h 66912 51277 HM); [cbn; tauto | reflexivity | cbn; tauto].
- eapply (img_rd_of_mem_ok E m IMG_REGIONS R_A1i 118210 16002 HM); [cbn; tauto | reflexivity | cbn; tauto].
- eapply (img_rd_of_mem_ok E m IMG_REGIONS R_A2j 649112 8 HM); [cbn; tauto | reflexivity | cbn; tauto].
- eapply (img_rd_of_mem_ok E m IMG_REGIONS R_A3 663680 832 HM); [cbn; tauto | reflexivity | cbn; tauto].
- destruct HM as (_ & Hrs & _). pose proof (proj1 (Forall_forall _ _) Hrs R_A7b ltac:(cbn; tauto)) as (_ & _ & _ & Hcs).
pose proof (proj1 (Forall_forall _ _) Hcs (YP09.mkChunk 6263888 (CVal 8 (SOff 41 0))) ltac:(cbn; tauto)) as Hck. cbn [YP09.r_base base_val] in Hck.
change A_canary with (0 + 6263888). change 8%nat with (N.to_nat 8).
apply (val_of_chunk_ok tfibsegs E m 0 6263888 8 (SOff 41 0) (bv_unsigned (sv_denot E (SOff 41 0))) Hck); [symmetry; apply Z_to_bv_bv_unsigned | pose proof (u64_range (sv_denot E (SOff 41 0))) as UR; change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); exact UR | cbn; lia].
Qed.
Lemma got_canary_chk : img_cell_chk A_GOT_canary 8 A_canary = true.
Proof. vm_compute. reflexivity. Qed.
Section d.
Variable B : asyms.
Hypothesis HB : TfibSyms B.
Hypothesis LAWS : AR_laws tfibsegs B.
Lemma icpt_pre_facts : forall ly S W regs mem md, icpt_pre B ly S W regs mem md ->
ecall_pre tfibsegs B ly S W regs mem md /\ ly_stk_lo ly = ASAN_CEIL /\ sp_window_lo - 128 <= spZ regs <= sp_window_hi /\
(forall a, spZ regs - DIAG_STK <= a < spZ regs -> apresent (w_H W) mem a).
Proof.
intros ly S W regs mem md (HAR & Hret & Hra & Hal & Hwin & Htop & Hslo & Hshi & Hpres & Hgp & Htp).
split; [|split; [exact Hslo | split; [exact Hwin | exact Hpres]]].
split; [exact HAR|]. split; [exact Hret|]. split; [exact Hal|].
split; [pose proof (am_layout _ _ _ _ (proj1 HAR)) as LO; pose proof (lo_top _ LO) as (T1 & _); unfold ly_bot, kStackSpan, ESTACK in *; lia|].
split; [rewrite Hshi; unfold kHighMemEnd, sp_window_hi in *; lia|].
split; [intros a Ha; apply Hpres; unfold ESTACK, DIAG_STK in *; lia|]. exact (conj Hgp Htp).
Qed.
Lemma icpt_pre_room : forall ly S W regs mem md, icpt_pre B ly S W regs mem md -> ly_stk_lo ly + 2 ^ 23 - 4112 <= spZ regs.
Proof.
intros ly S W regs mem md (HAR & Hret & Hra & Hal & Hwin & Htop & Hslo & Hshi & Hpres & Hgp & Htp).
pose proof (am_layout _ _ _ _ (proj1 HAR)) as LO. pose proof (lo_top _ LO) as (T1 & _). unfold ly_bot, kStackSpan in *. lia.
Qed.
Lemma rodata_zero_shadow : forall ly S W mem md, AR tfibsegs B ly S W mem md ->
zero_shadow (aview tfibsegs (w_H W) mem) SHADOW_OFF 0x10000 (0x20f48 - 0x10000).
Proof.
intros ly S W mem md HAR.
exact (al_zshadow _ _ LAWS ly S W mem md (0x10000, 0x20f48 - 0x10000) HAR
ltac:(unfold zero_shadow_ranges; right; rewrite (ts_zsh B HB); cbn; tauto)).
Qed.
Lemma rodata_hull_zero : forall ly S W mem md p n, AR tfibsegs B ly S W mem md -> 0x10560 <= p -> p + n <= 0x20f40 -> 0 < n ->
hull_zero (aview tfibsegs (w_H W) mem) p n.
Proof.
intros ly S W mem md p n HAR Hp Hn Hn0. pose proof (rodata_zero_shadow ly S W mem md HAR) as HZ.
intros s Hs. unfold shadow_addr in Hs.
assert (L1 : 0x10560 / 8 <= p / 8) by (apply Z.div_le_mono; lia).
assert (L2 : (p + n - 1) / 8 <= (0x20f40 - 1) / 8) by (apply Z.div_le_mono; lia).
change (0x10560 / 8) with 8364 in L1. change ((0x20f40 - 1) / 8) with 16871 in L2.
pose proof (Z.div_mod (SHADOW_OFF + p / 8) 8 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound (SHADOW_OFF + p / 8) 8 ltac:(lia)) as D1'.
pose proof (Z.div_mod (SHADOW_OFF + (p + n - 1) / 8) 8 ltac:(lia)) as D2. pose proof (Z.mod_pos_bound (SHADOW_OFF + (p + n - 1) / 8) 8 ltac:(lia)) as D2'.
replace s with (shadow_of_addr SHADOW_OFF 0x10000 + (s - shadow_of_addr SHADOW_OFF 0x10000)) by lia.
apply (HZ (s - shadow_of_addr SHADOW_OFF 0x10000)).
unfold shadow_of_addr, SHADOW_OFF in *. change (65536 / 8) with 8192. change ((134984 - 65536) / 8) with 8681. lia.
Qed.
Lemma ro_img_of_IMG : forall E m, mem_ok tfibsegs E m IMG_REGIONS -> ro_img m.
Proof.
intros E m HM E'. unfold img_ro_region.
split; [cbn; unfold IMG_RO_LO; lia|]. split; [cbn; unfold IMG_RO_HI; lia|]. split; [intros o Ho; cbn in Ho; lia|].
cbn [YP09.r_chunks YP09.r_base base_val].
assert (CH : forall r a len a' len', In r IMG_REGIONS -> YP09.r_base r = None -> In (YP09.mkChunk a (CImg len)) (YP09.r_chunks r) ->
a <= a' -> a' + len' <= a + len -> YP09.chunk_ok tfibsegs E' m 0 (YP09.mkChunk a' (CImg len'))).
{ intros r a len a' len' Hr Hb Hc H1 H2 i Hi. cbn [YP09.c_off YP09.c_val c_len cv_len cbyte] in Hi |- *. rewrite !Z.add_0_l.
pose proof (img_rd_of_mem_ok E m IMG_REGIONS r a len HM Hr Hb Hc (a' + i) ltac:(lia)) as Hm. rewrite Hm.
destruct HM as (_ & Hrs & _). pose proof (proj1 (Forall_forall _ _) Hrs r Hr) as (_ & _ & _ & Hcs).
pose proof (proj1 (Forall_forall _ _) Hcs _ Hc (a' + i - a) ltac:(cbn; lia)) as (b & Hcb & _).
revert Hcb. rewrite Hb. cbn [base_val YP09.c_off YP09.c_val cbyte]. rewrite !Z.add_0_l. replace (a + (a' + i - a)) with (a' + i) by lia.
intros ->. exists b. split; reflexivity. }
unfold img_ro_chunks, IMG_RO_HI.
repeat (apply Forall_cons;
[ first [ apply (CH R_A1a 65536 744); [cbn; tauto | reflexivity | cbn; tauto | cbn; lia | cbn; lia]
| apply (CH R_A1b 66288 24); [cbn; tauto | reflexivity | cbn; tauto | cbn; lia | cbn; lia]
| apply (CH R_A1c 66320 24); [cbn; tauto | reflexivity | cbn; tauto | cbn; lia | cbn; lia]
| apply (CH R_A1d 66352 104); [cbn; tauto | reflexivity | cbn; tauto | cbn; lia | cbn; lia]
| apply (CH R_A1e 66472 8); [cbn; tauto | reflexivity | cbn; tauto | cbn; lia | cbn; lia]
| apply (CH R_A1f 66488 104); [cbn; tauto | reflexivity | cbn; tauto | cbn; lia | cbn; lia]
| apply (CH R_A1g 66656 192); [cbn; tauto | reflexivity | cbn; tauto | cbn; lia | cbn; lia]
| apply (CH R_A1h 66912 51277); [cbn; tauto | reflexivity | cbn; tauto | cbn; lia | cbn; lia]
| apply (CH R_A1i 118210 16002); [cbn; tauto | reflexivity | cbn; tauto | cbn; lia | cbn; lia]
| apply (CH R_A1j 134216 772); [cbn; tauto | reflexivity | cbn; tauto | cbn; lia | cbn; lia]
| apply (CH R_A1k 135008 9); [cbn; tauto | reflexivity | cbn; tauto | cbn; lia | cbn; lia]
| apply (CH R_A1l 135040 9); [cbn; tauto | reflexivity | cbn; tauto | cbn; lia | cbn; lia]
| apply (CH R_A1m 135072 8); [cbn; tauto | reflexivity | cbn; tauto | cbn; lia | cbn; lia]
| apply (CH R_A1n 135104 10); [cbn; tauto | reflexivity | cbn; tauto | cbn; lia | cbn; lia]
| apply (CH R_A1o 135136 1); [cbn; tauto | reflexivity | cbn; tauto | cbn; lia | cbn; lia]
| apply (CH R_A1p 135168 7); [cbn; tauto | reflexivity | cbn; tauto | cbn; lia | cbn; lia]
| apply (CH R_A1q 135200 3); [cbn; tauto | reflexivity | cbn; tauto | cbn; lia | cbn; lia]
| apply (CH R_A1r 135232 6); [cbn; tauto | reflexivity | cbn; tauto | cbn; lia | cbn; lia]
| apply (CH R_A1s 135264 6); [cbn; tauto | reflexivity | cbn; tauto | cbn; lia | cbn; lia]
| apply (CH R_A1t 135296 5); [cbn; tauto | reflexivity | cbn; tauto | cbn; lia | cbn; lia]
| apply (CH R_A1u 135328 6); [cbn; tauto | reflexivity | cbn; tauto | cbn; lia | cbn; lia]
| apply (CH R_A1v 135360 7); [cbn; tauto | reflexivity | cbn; tauto | cbn; lia | cbn; lia]
| apply (CH R_A1w 135392 4); [cbn; tauto | reflexivity | cbn; tauto | cbn; lia | cbn; lia]
| apply (CH R_A1x 135424 8); [cbn; tauto | reflexivity | cbn; tauto | cbn; lia | cbn; lia]
| apply (CH R_A1y 135456 7); [cbn; tauto | reflexivity | cbn; tauto | cbn; lia | cbn; lia]
| apply (CH R_A1z 135488 7); [cbn; tauto | reflexivity | cbn; tauto | cbn; lia | cbn; lia]
| apply (CH R_A1aa 135520 6); [cbn; tauto | reflexivity | cbn; tauto | cbn; lia | cbn; lia]
| apply (CH R_A1ab 135552 5); [cbn; tauto | reflexivity | cbn; tauto | cbn; lia | cbn; lia]
| apply (CH R_A1ac 135584 6); [cbn; tauto | reflexivity | cbn; tauto | cbn; lia | cbn; lia]
| apply (CH R_A1ad 135616 6); [cbn; tauto | reflexivity | cbn; tauto | cbn; lia | cbn; lia]
| apply (CH R_A1ae 135648 5); [cbn; tauto | reflexivity | cbn; tauto | cbn; lia | cbn; lia]
| apply (CH R_A1af 135680 6); [cbn; tauto | reflexivity | cbn; tauto | cbn; lia | cbn; lia]
| apply (CH R_A1ag 135712 5); [cbn; tauto | reflexivity | cbn; tauto | cbn; lia | cbn; lia]
| apply (CH R_A1ah 135744 5); [cbn; tauto | reflexivity | cbn; tauto | cbn; lia | cbn; lia]
| apply (CH R_A1ai 135776 4); [cbn; tauto | reflexivity | cbn; tauto | cbn; lia | cbn; lia]
| apply (CH R_A1aj 135808 5); [cbn; tauto | reflexivity | cbn; tauto | cbn; lia | cbn; lia]
| apply (CH R_A1ak 135840 6); [cbn; tauto | reflexivity | cbn; tauto | cbn; lia | cbn; lia]
| apply (CH R_A1al 135872 3); [cbn; tauto | reflexivity | cbn; tauto | cbn; lia | cbn; lia]
| apply (CH R_A1am 135904 6); [cbn; tauto | reflexivity | cbn; tauto | cbn; lia | cbn; lia]
| apply (CH R_A1an 135936 6); [cbn; tauto | reflexivity | cbn; tauto | cbn; lia | cbn; lia]
| apply (CH R_A1ao 135968 2); [cbn; tauto | reflexivity | cbn; tauto | cbn; lia | cbn; lia]
| apply (CH R_A1ap 136000 41); [cbn; tauto | reflexivity | cbn; tauto | cbn; lia | cbn; lia]
| apply (CH R_A1aq 136064 9); [cbn; tauto | reflexivity | cbn; tauto | cbn; lia | cbn; lia]
| apply (CH R_A1ar 136096 364); [cbn; tauto | reflexivity | cbn; tauto | cbn; lia | cbn; lia]
| apply (CH R_A1as 136544 1412); [cbn; tauto | reflexivity | cbn; tauto | cbn; lia | cbn; lia]
| apply (CH R_A1at 137960 96); [cbn; tauto | reflexivity | cbn; tauto | cbn; lia | cbn; lia]
| apply (CH R_A1au 138058 505014); [cbn; tauto | reflexivity | cbn; tauto | cbn; lia | cbn; lia] ] |]).
apply Forall_nil.
Qed.
Lemma mconsts_of_IMG : forall E W mem, mem_ok tfibsegs E (mrestrict (w_H W) mem) IMG_REGIONS -> mconsts_view W mem.
Proof.
intros E W mem HM a Ha. pose proof mc_bounds as [B1 B2].
pose proof (img_rd_of_mem_ok E _ IMG_REGIONS R_A1d 66352 104 HM ltac:(cbn; tauto) eq_refl ltac:(cbn; tauto) a ltac:(lia)) as Hm.
unfold aview. rewrite Hm. unfold img_byte. reflexivity.
Qed.
End d.
End c.
