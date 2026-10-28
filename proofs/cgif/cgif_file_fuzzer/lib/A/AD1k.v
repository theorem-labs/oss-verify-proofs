(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YK15 YK18 YP0n YM02 YP0m YP09 YP0l YP06 YP08 YP03 YN3q YN3v YI04 YK04 YA0i YA0n YA0e YG00 YG01 YG0f YG0v YG0n YG0s YG0d YCe5 YL02.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v AF0m AD2j AD2i AD1t AD20 AD1v AD2h AD2f AD1w AD1x.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AE2p AE3i AE39 AE3h AE3m AE3l AE23 AE2x AE2v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO05 YO09 YO06 YO01.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AE2k AD1u.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
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
Lemma img_rd_sub : forall m lo hi lo' hi', img_rd m lo hi -> lo <= lo' -> hi' <= hi -> img_rd m lo' hi'.
Proof. intros m lo hi lo' hi' H H1 H2 x Hx. apply H. lia. Qed.
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
Lemma est_pristine : forall H m, stderr_pristine (mrestrict H m) -> est H m.
Proof. intros H m HF. eapply (est_of_fields H m stderr_fields 0 HF); [cbn; tauto .. | lia]. Qed.
Lemma est_written : forall H m, stderr_written (mrestrict H m) -> est H m.
Proof. intros H m HF. eapply (est_of_fields H m stderr_fields_after STDERR_BUF HF); [cbn; tauto .. | unfold STDERR_BUF; lia]. Qed.
Lemma est_after_vf : forall H m, stderr_after_vfprintf (mrestrict H m) -> est H m.
Proof. intros H m HF. eapply (est_of_fields H m stderr_fields_after_vf 0 HF); [cbn; tauto .. | lia]. Qed.
Lemma stderr_img_chk : img_cells_chk F_STDERR stderr_fields = true.
Proof. vm_compute. reflexivity. Qed.
Lemma stderr_pristine_img : forall H m, img_at H m F_STDERR_LO F_STDERR_HI -> stderr_pristine (mrestrict H m).
Proof.
intros H m Hi. apply (file_is_img _ F_STDERR_LO F_STDERR_HI); [apply img_rd_of_aview; exact Hi | exact stderr_img_chk |].
unfold stderr_fields, F_STDERR, F_STDERR_LO, F_STDERR_HI. repeat (apply Forall_cons; [cbn; lia|]). apply Forall_nil.
Qed.
Theorem tfib_est_img : est_img_tfa est.
Proof. intros H m Hi. apply est_pristine. apply stderr_pristine_img. exact Hi. Qed.
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
assert (HBF : STDOUT_BUFA = 6264480) by reflexivity. assert (HBS : STDOUT_BSZ = 1024) by reflexivity. assert (HFF : F_STDOUT = 665192) by reflexivity.
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
AR tfibsegs B ly S W mem md -> AF0x.TFIB_IMG_LO <= a < AF0x.TFIB_IMG_END -> ~ Exists (in_zr a) (as_owned_static B) -> ~ aowned B ly S a.
Proof.
intros B ly S W mem md a (M & L & _) Ha Hst [OW _]. pose proof (am_layout _ _ _ _ M) as LO.
pose proof (AF0x.img_cover_of_ledger _ _ _ L) as [I1 I2]. unfold AF0x.TFIB_IMG_LO, AF0x.TFIB_IMG_END in *.
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
AR tfibsegs B ly S W mem md -> AF0x.TFIB_IMG_LO <= a < AF0x.TFIB_IMG_END -> ~ Exists (in_zr a) (as_owned_static B) -> ~ aowned B ly S a.
Proof. exact tfib_img_not_owned. Qed.
Lemma tfib_not_owned_static : forall (B : asyms) lo hi a, TfibSyms B ->
forallb (fun r => (fst r + snd r <=? lo) || (hi <=? fst r)) Tfib_owned_static = true -> lo <= a < hi -> ~ Exists (in_zr a) (as_owned_static B).
Proof.
intros B lo hi a TB Hc Ha HE. rewrite (ts_owned B TB) in HE. apply Exists_exists in HE as (r & Hr & [H1 H2]).
pose proof (proj1 (forallb_forall _ _) Hc r Hr) as Hb. cbn beta in Hb. apply Bool.orb_prop in Hb as [Hb|Hb]; apply Z.leb_le in Hb; lia.
Qed.
Lemma img_facts : forall E m, mem_ok tfibsegs E m IMG_REGIONS ->
(img_rd m 0x10568 0x1cd09 /\ img_rd m 0x1cd1e 0x20b7c) /\ img_rd m 650296 650304 /\ img_rd m 664880 665712 /\ val_mem tfibsegs m A_canary 8 (bv_unsigned (sv_denot E (SOff 41 0))).
Proof.
intros E m HM. split; [split|split; [|split]].
- eapply (img_rd_of_mem_ok E m IMG_REGIONS R_A1h 66920 51105 HM); [cbn; tauto | reflexivity | cbn; tauto].
- eapply (img_rd_of_mem_ok E m IMG_REGIONS R_A1i 118046 15966 HM); [cbn; tauto | reflexivity | cbn; tauto].
- eapply (img_rd_of_mem_ok E m IMG_REGIONS R_A2e 650296 8 HM); [cbn; tauto | reflexivity | cbn; tauto].
- eapply (img_rd_of_mem_ok E m IMG_REGIONS R_A3 664880 832 HM); [cbn; tauto | reflexivity | cbn; tauto].
- destruct HM as (_ & Hrs & _). pose proof (proj1 (Forall_forall _ _) Hrs R_A7b ltac:(cbn; tauto)) as (_ & _ & _ & Hcs).
pose proof (proj1 (Forall_forall _ _) Hcs (YP09.mkChunk 6262736 (CVal 8 (SOff 41 0))) ltac:(cbn; tauto)) as Hck. cbn [YP09.r_base base_val] in Hck.
change A_canary with (0 + 6262736). change 8%nat with (N.to_nat 8).
apply (val_of_chunk_ok tfibsegs E m 0 6262736 8 (SOff 41 0) (bv_unsigned (sv_denot E (SOff 41 0))) Hck); [symmetry; apply Z_to_bv_bv_unsigned | pose proof (u64_range (sv_denot E (SOff 41 0))) as UR; change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); exact UR | cbn; lia].
Qed.
Lemma got_canary_chk : img_cell_chk A_GOT_canary 8 A_canary = true.
Proof. vm_compute. reflexivity. Qed.
Section d.
Variable B : asyms.
Hypothesis HB : TfibSyms B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis TL : TfibSyms B.
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
zero_shadow (aview tfibsegs (w_H W) mem) SHADOW_OFF 0x10000 (0x20e08 - 0x10000).
Proof.
intros ly S W mem md HAR.
exact (al_zshadow _ _ LAWS ly S W mem md (0x10000, 0x20e08 - 0x10000) HAR
ltac:(unfold zero_shadow_ranges; right; rewrite (ts_zsh B HB); cbn; tauto)).
Qed.
Lemma rodata_hull_zero : forall ly S W mem md p n, AR tfibsegs B ly S W mem md -> 0x10568 <= p -> p + n <= 0x20e00 -> 0 < n ->
hull_zero (aview tfibsegs (w_H W) mem) p n.
Proof.
intros ly S W mem md p n HAR Hp Hn Hn0. pose proof (rodata_zero_shadow ly S W mem md HAR) as HZ.
intros s Hs. unfold shadow_addr in Hs.
assert (L1 : 0x10568 / 8 <= p / 8) by (apply Z.div_le_mono; lia).
assert (L2 : (p + n - 1) / 8 <= (0x20e00 - 1) / 8) by (apply Z.div_le_mono; lia).
change (0x10568 / 8) with 8365 in L1. change ((0x20e00 - 1) / 8) with 16831 in L2.
pose proof (Z.div_mod (SHADOW_OFF + p / 8) 8 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound (SHADOW_OFF + p / 8) 8 ltac:(lia)) as D1'.
pose proof (Z.div_mod (SHADOW_OFF + (p + n - 1) / 8) 8 ltac:(lia)) as D2. pose proof (Z.mod_pos_bound (SHADOW_OFF + (p + n - 1) / 8) 8 ltac:(lia)) as D2'.
replace s with (shadow_of_addr SHADOW_OFF 0x10000 + (s - shadow_of_addr SHADOW_OFF 0x10000)) by lia.
apply (HZ (s - shadow_of_addr SHADOW_OFF 0x10000)).
unfold shadow_of_addr, SHADOW_OFF in *. change (65536 / 8) with 8192. change ((134664 - 65536) / 8) with 8641. lia.
Qed.
Lemma rodata_shadow_facts : forall ly S W mem md p n, AR tfibsegs B ly S W mem md -> 0x10568 <= p -> p + n <= 0x20e00 -> 0 < n ->
range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF p n /\ shadow_hull_vis (aview tfibsegs (w_H W) mem) p n.
Proof.
intros ly S W mem md p n HAR Hp Hn Hn0. split.
- intros x Hx. apply (zero_shadow_range _ SHADOW_OFF 0x10000 (0x20e08 - 0x10000) eq_refl eq_refl (rodata_zero_shadow ly S W mem md HAR) x). lia.
- intros s Hs. rewrite (rodata_hull_zero ly S W mem md p n HAR Hp Hn Hn0 s Hs). discriminate.
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
| apply (CH R_A1e 66472 16); [cbn; tauto | reflexivity | cbn; tauto | cbn; lia | cbn; lia]
| apply (CH R_A1f 66496 104); [cbn; tauto | reflexivity | cbn; tauto | cbn; lia | cbn; lia]
| apply (CH R_A1g 66664 192); [cbn; tauto | reflexivity | cbn; tauto | cbn; lia | cbn; lia]
| apply (CH R_A1h 66920 51105); [cbn; tauto | reflexivity | cbn; tauto | cbn; lia | cbn; lia]
| apply (CH R_A1i 118046 15966); [cbn; tauto | reflexivity | cbn; tauto | cbn; lia | cbn; lia]
| apply (CH R_A1j 134016 653); [cbn; tauto | reflexivity | cbn; tauto | cbn; lia | cbn; lia]
| apply (CH R_A1k 134688 67); [cbn; tauto | reflexivity | cbn; tauto | cbn; lia | cbn; lia]
| apply (CH R_A1l 134784 34); [cbn; tauto | reflexivity | cbn; tauto | cbn; lia | cbn; lia]
| apply (CH R_A1m 134848 1416); [cbn; tauto | reflexivity | cbn; tauto | cbn; lia | cbn; lia]
| apply (CH R_A1n 136268 96); [cbn; tauto | reflexivity | cbn; tauto | cbn; lia | cbn; lia]
| apply (CH R_A1o 136366 506706); [cbn; tauto | reflexivity | cbn; tauto | cbn; lia | cbn; lia] ] |]).
apply Forall_nil.
Qed.
Lemma mconsts_of_IMG : forall E W mem, mem_ok tfibsegs E (mrestrict (w_H W) mem) IMG_REGIONS -> mconsts_view W mem.
Proof.
intros E W mem HM a Ha. pose proof mc_bounds as [B1 B2].
pose proof (img_rd_of_mem_ok E _ IMG_REGIONS R_A1d 66352 104 HM ltac:(cbn; tauto) eq_refl ltac:(cbn; tauto) a ltac:(lia)) as Hm.
unfold aview. rewrite Hm. unfold img_byte. reflexivity.
Qed.
Theorem tfib_fwrite_site : fwrite_site_tfa B est.
Proof.
intros ly S W regs mem md E p len msg T HPRE G10 G11 G12 G13 Hlen Hlen1 Hp1 Hp2 Hhole Himg HIMG Hfd HAI HPOST.
pose proof (icpt_pre_facts ly S W regs mem md HPRE) as (HEPRE & Hslo & Hwin & Hpres). pose proof (proj1 HEPRE) as HAR.
pose proof (img_facts E _ HIMG) as ([IR1a IR1b] & IR2 & IR3 & Vcan).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HFWI : FWI_STK = 6224) by reflexivity. assert (HDS : DIAG_STK = 16384) by reflexivity.
assert (HFE : F_STDERR = 0xa2578) by reflexivity. assert (HFS : FILE_SZ = 232) by reflexivity.
unfold wr. change (cfg_at tfibsegs A_icpt_fwrite regs mem md) with (cfg_at tfibsegs FW_ENTRY regs mem md).
apply (tfib_fwrite_icpt B LAWS HB ly S W regs mem md ch_stderr p len (bv_unsigned (sv_denot E (SOff 41 0))) msg T HEPRE).
- pose proof (icpt_pre_room ly S W regs mem md HPRE); unfold FWI_STK, FPI_STK in *; lia.
- intros a Ha. apply Hpres. lia.
- exact G10. - exact G11. - exact G12. - exact G13.
- lia. - lia. - lia. - unfold kHighMemEnd. lia.
- left. unfold sp_window_lo in Hwin. lia.
- left. rewrite HFE. lia.
-
apply (proj2 (rdn_mbytes tfibsegs (mrestrict (w_H W) mem) (Z.to_nat len) p msg)). split; [lia|].
intros i Hi. destruct Hhole as [Hh|Hh]; [rewrite (IR1a (p + Z.of_nat i)) by lia | rewrite (IR1b (p + Z.of_nat i)) by lia];
unfold img_byte; rewrite (Himg i) by lia; symmetry; apply nth_error_nth'; lia.
- apply (file_is_img _ 664880 665712); [exact IR3 | exact stderr_img_chk |].
unfold stderr_fields. rewrite HFE. repeat (apply Forall_cons; [cbn; lia|]). apply Forall_nil.
- intros a Ha. apply (tfib_low_not_owned B ly S W mem md a HAR); [unfold AF0x.TFIB_IMG_LO, AF0x.TFIB_IMG_END; lia|].
apply (tfib_not_owned_static B F_STDERR (F_STDERR + FILE_SZ) a HB); [vm_compute; reflexivity | exact Ha].
- eapply val_mem_img; [exact IR2 | unfold A_GOT_canary; lia | unfold A_GOT_canary; cbn; lia | exact got_canary_chk].
- exact Vcan.
- exact (u64_range (sv_denot E (SOff 41 0))).
- left. unfold kLowMemEnd. lia.
- exact (proj1 (rodata_shadow_facts ly S W mem md p len HAR Hp1 ltac:(lia) ltac:(lia))).
- exact (proj2 (rodata_shadow_facts ly S W mem md p len HAR Hp1 ltac:(lia) ltac:(lia))).
- split; [exact Hfd | reflexivity].
- exact HAI.
- intros regs' mem' md' HAR' HP' Hsbm' Ha0' HFW' Hfr' Hpr' HAI'.
apply (HPOST regs' mem' md' HAR' HP' Hsbm' Ha0').
+ apply est_written. exact HFW'.
+ intros a Ha Hb Hf. apply (Hfr' a Ha); [lia|]. unfold STDERR_MUT, F_STDERR_LO, F_STDERR_HI in Hf. rewrite HFE, HFS. exact Hf.
+ intros a Ha Hf Hp. apply (Hpr' a Ha); [|exact Hp]. unfold STDERR_MUT, F_STDERR_LO, F_STDERR_HI in Hf. rewrite HFE, HFS. exact Hf.
+ exact HAI'.
Qed.
Lemma msg_refused_eq : map (Z_to_bv 8) AE3l.msg_refused = YO05.msg_refused /\ Z.of_nat (length YO05.msg_refused) = 38.
Proof. vm_compute. split; reflexivity. Qed.
Theorem tfib_refused_site : refused_site_tfa B est.
Proof.
intros ly S W regs mem md E T HPRE G10 G11 G12 HIMG Hfd HAI HPOST.
pose proof (icpt_pre_facts ly S W regs mem md HPRE) as (HEPRE & Hslo & Hwin & Hpres). pose proof (proj1 HEPRE) as HAR.
pose proof (img_facts E _ HIMG) as (IR1 & IR2 & IR3 & Vcan).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof msg_refused_eq as [ME ML].
assert (HFPI : FPI_STK = 9216) by reflexivity. assert (HDS : DIAG_STK = 16384) by reflexivity.
assert (HFE : F_STDERR = 0xa2578) by reflexivity. assert (HFS : FILE_SZ = 232) by reflexivity.
unfold wr. rewrite <- ME. change (cfg_at tfibsegs A_icpt_fprintf regs mem md) with (cfg_at tfibsegs AE2v.FP_ENTRY regs mem md).
apply (tfib_fprintf_icpt_refused B LAWS HB TL ly S W regs mem md ch_stderr (bv_unsigned (sv_denot E (SOff 41 0))) T HEPRE).
- pose proof (icpt_pre_room ly S W regs mem md HPRE); unfold FWI_STK, FPI_STK in *; lia.
- intros a Ha. apply Hpres. lia.
- exact G10. - exact G11. - exact G12.
- apply (file_is_img _ 664880 665712); [exact IR3 | exact stderr_img_chk |].
unfold stderr_fields. rewrite HFE. repeat (apply Forall_cons; [cbn; lia|]). apply Forall_nil.
- intros a Ha. unfold vf_file in Ha. apply (tfib_low_not_owned B ly S W mem md a HAR); [unfold AF0x.TFIB_IMG_LO, AF0x.TFIB_IMG_END; lia|].
apply (tfib_not_owned_static B F_STDERR (F_STDERR + FILE_SZ) a HB); [vm_compute; reflexivity | exact Ha].
- eapply val_mem_img; [exact IR2 | unfold A_GOT_canary; lia | unfold A_GOT_canary; cbn; lia | exact got_canary_chk].
- exact Vcan.
- exact (u64_range (sv_denot E (SOff 41 0))).
- exact (ro_img_of_IMG E _ HIMG).
- apply (rodata_hull_zero ly S W mem md); [exact HAR | unfold FMT_refused; lia | unfold FMT_refused; lia | lia].
- split; [exact Hfd | reflexivity].
- exact HAI.
- intros regs' mem' md' HAR' HP' Hsbm' Ha0' HFW' Hfr' Hpr' HAI'.
apply (HPOST regs' mem' md' HAR' HP' Hsbm').
+ rewrite ML. exact Ha0'.
+ apply est_after_vf. exact HFW'.
+ intros a Ha Hb Hf. apply (Hfr' a Ha); [lia|]. unfold vf_file. unfold STDERR_MUT, F_STDERR_LO, F_STDERR_HI in Hf. rewrite HFE, HFS. exact Hf.
+ intros a Ha Hf Hp. apply (Hpr' a Ha); [|exact Hp]. unfold vf_file. unfold STDERR_MUT, F_STDERR_LO, F_STDERR_HI in Hf. rewrite HFE, HFS. exact Hf.
+ exact HAI'.
Qed.
End d.
End c.
