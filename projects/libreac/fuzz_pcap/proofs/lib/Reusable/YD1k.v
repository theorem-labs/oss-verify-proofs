(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: generated from proofs/cgif/cgif_file_fuzzer/lib/YD1k.v (origin/ossv/recipes c8557374ad2e) for libreac/fuzz_pcap's asan-ubsan image (sha256 9e66f771f22a...) by a Theorem Labs lane's FROZEN gen_ad1k.py (frozen-a476b896d2e3, sha256 a476b896d2e3fbd7af8937ac114af7b8f02cf4dbcc61ed45ed2423ce64ccdf15), with its module paths changed and only its image literals regenerated: the YD2j chunk restatements from the generated lib/Reusable/YD2j.v, the zero-shadow and rodata-hull bounds from lib/Reusable/YF0m.v and the image's asan_globals, the stdio FILE addresses from the unstripped twin (c969d83cdd59...) *)
(* DONOR CONTROL, MEASURED (ad2-frozen.md (sha256 a9a284ae32a9; internal record) section 2): with the same frozen tool, cgif_file_fuzzer's own AD1k.v / YD1k.v come out BYTE-EQUAL to the released donor files of origin/ossv/recipes c8557374ad2e, rc 0.  The raw output for fuzz_pcap is YD1k.raw.v (345 lines, sha256 23422a3b8c77952f...; internal record). *)
(* Modified by Theorem Labs, 2026-10: the donor's `Require Import YE2k YD1u` drops YE2k, which libreac/fuzz_pcap does not carry; YD1u stays. YE2k is only required, never named in the body. *)
(* Modified by Theorem Labs, 2026-10-29: the `unfold ...TFIB_IMG_LO, ...TFIB_IMG_END in *.` step of tfib_img_not_owned also opens PcapImgEnd.pcap_img_end and YImgTop.IMG_TOP, the image-end unfold class a Theorem Labs lane uses in lib/A/AD1g.v: TFIB_IMG_END is now pcap_img_end, so without them the lia steps below it have an opaque image end and fail.  PcapImgEnd / YImgTop are Required, as lib/A/AD2i.v and lib/A/AD2j.v on this branch already do.  No statement changes. *)
(* Modified by Theorem Labs, 2026-10-29: every post-edit is SCRIPTED in postedit_ad1k.py (sha256 1986896eeb84; internal record), which run_pcap_frozen.sh calls, so a re-run reproduces this text.  Besides the two lines above: the PROOF HALF is cut -- the file ends after the Qed. of mconsts_of_IMG and then carries only End d. and End c.; the three site items belong to a Theorem Labs lane's AD1kSites lane, 345 lines -> 275.  And the UNIT RENAME TfibSyms -> PcapSyms, with the pair list IMPORTED from assemble.py (sha256 32e4cec27d2a; internal record) UNIT_RENAME (commit d4691bce0fe: TfibB_syms -> PcapB_syms, TfibB_ok -> PcapB_ok, TfibSyms -> PcapSyms, TfibB -> PcapB).  MEASURED: the rename changes 3 lines and every changed line is a rename. *)
(* gated: a Theorem Labs lane PASS A+B at c061542723f / 731386609e0.  Gates on this exact text, all rc 0: gate_check.py GATE ok 33 regions 4 with gaps 0 NEW gaps 0 failures (on the YD2j it restates); kimg_local.py overlapping write bytes 0, contradicting bytes 0, 0 conflicts; codeptr c0ce606ed1fa (startup-set 2026-10-29): 0 findings / 0 stale on every file, with 20 declarations carrying their measured reasons in declarations-20.sh (sha256 880286aef98b; internal record); AB1m / YB1m UNMEASURED (no address literal; BFUEL is %nat); logs final20.txt (sha256 b2b70d12a063; internal record) / final20.no-b1m.txt (sha256 be056cbfc3b7; internal record) (a Theorem Labs lane); independent run by a Theorem Labs lane agrees *)
(* Requires YD1t, YD1u, YD1v, YD20, YD24, YD2f, YD2h, YD1w, YD1x, YF0l, YB13 and YE2v. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import SymAddr.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK11 YK15 YK18 YP0n YM02 YP0m YP09 YP0l YP06 YP08 YP03 YN3q YN3v YI04 YK04 YA0i YA0n YA0e YG00 YG01 YG0f YG0v YG0n YG0s YG0d YCe5 YL02 YB1v YF0m YD2j YD2i YD1t YD20 YD1v YD2h YD2f YD1w YD1x.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YE2p YE3i YE39 YE3h YE3m YE3l YE23 YE2x YE2v.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YO05 YO09 YO06 YO01.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import PcapImgEnd YImgTop.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YD1u.
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
assert (HBF : STDOUT_BUFA = (symaddr (Symbols.AsanUbsan.Sec.s_bss + 5598624)%Z)) by reflexivity. assert (HBS : STDOUT_BSZ = 1024) by reflexivity. assert (HFF : F_STDOUT = (symaddr Symbols.AsanUbsan.s___stdout_FILE)) by reflexivity.
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
AR tfibsegs B ly S W mem md -> YF0x.TFIB_IMG_LO <= a < YF0x.TFIB_IMG_END -> ~ Exists (in_zr a) (as_owned_static B) -> ~ aowned B ly S a.
Proof.
intros B ly S W mem md a (M & L & _) Ha Hst [OW _]. pose proof (am_layout _ _ _ _ M) as LO.
pose proof (YF0x.img_cover_of_ledger _ _ _ L) as [I1 I2]. unfold YF0x.TFIB_IMG_LO, YF0x.TFIB_IMG_END, PcapImgEnd.pcap_img_end, YImgTop.IMG_TOP in *.
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
AR tfibsegs B ly S W mem md -> YF0x.TFIB_IMG_LO <= a < YF0x.TFIB_IMG_END -> ~ Exists (in_zr a) (as_owned_static B) -> ~ aowned B ly S a.
Proof. exact tfib_img_not_owned. Qed.
Lemma tfib_not_owned_static : forall (B : asyms) lo hi a, PcapSyms B ->
forallb (fun r => (fst r + snd r <=? lo) || (hi <=? fst r)) Tfib_owned_static = true -> lo <= a < hi -> ~ Exists (in_zr a) (as_owned_static B).
Proof.
intros B lo hi a TB Hc Ha HE. rewrite (ts_owned B TB) in HE. apply Exists_exists in HE as (r & Hr & [H1 H2]).
pose proof (proj1 (forallb_forall _ _) Hc r Hr) as Hb. cbn beta in Hb. apply Bool.orb_prop in Hb as [Hb|Hb]; apply Z.leb_le in Hb; lia.
Qed.
Lemma img_facts : forall E m, mem_ok tfibsegs E m IMG_REGIONS ->
(img_rd m (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 0x280)%Z) (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 0xc978)%Z) /\ img_rd m (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 0xc98d)%Z) (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 67488)%Z)) /\ img_rd m (symaddr (Symbols.AsanUbsan.Sec.s_got + 0xce8)%Z) (symaddr (Symbols.AsanUbsan.Sec.s_got + 0xcf0)%Z) /\ img_rd m (symaddr Symbols.AsanUbsan.s_oft_arg0) (symaddr Symbols.AsanUbsan.Sec.s_asan_globals) /\ val_mem tfibsegs m A_canary 8 (bv_unsigned (sv_denot E (SOff 41 0))).
Proof.
intros E m HM. split; [split|split; [|split]].
- eapply (img_rd_of_mem_ok E m IMG_REGIONS R_A1h (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 0x280)%Z) 50936 HM); [cbn; tauto | reflexivity | cbn; tauto].
- eapply (img_rd_of_mem_ok E m IMG_REGIONS R_A1i (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 0xc98d)%Z) 15891 HM); [cbn; tauto | reflexivity | cbn; tauto].
- eapply (img_rd_of_mem_ok E m IMG_REGIONS R_A2e (symaddr (Symbols.AsanUbsan.Sec.s_got + 0xce8)%Z) 8 HM); [cbn; tauto | reflexivity | cbn; tauto].
- eapply (img_rd_of_mem_ok E m IMG_REGIONS R_A3 (symaddr Symbols.AsanUbsan.s_oft_arg0) 840 HM); [cbn; tauto | reflexivity | cbn; tauto].
- destruct HM as (_ & Hrs & _). pose proof (proj1 (Forall_forall _ _) Hrs R_A7b ltac:(cbn; tauto)) as (_ & _ & _ & Hcs).
pose proof (proj1 (Forall_forall _ _) Hcs (YP09.mkChunk (symaddr Symbols.AsanUbsan.s___stack_chk_guard) (CVal 8 (SOff 41 0))) ltac:(cbn; tauto)) as Hck. cbn [YP09.r_base base_val] in Hck.
change A_canary with (0 + (symaddr Symbols.AsanUbsan.s___stack_chk_guard)). change 8%nat with (N.to_nat 8).
apply (val_of_chunk_ok tfibsegs E m 0 (symaddr Symbols.AsanUbsan.s___stack_chk_guard) 8 (SOff 41 0) (bv_unsigned (sv_denot E (SOff 41 0))) Hck); [symmetry; apply Z_to_bv_bv_unsigned | pose proof (u64_range (sv_denot E (SOff 41 0))) as UR; change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); exact UR | cbn; lia].
Qed.
Lemma got_canary_chk : img_cell_chk A_GOT_canary 8 A_canary = true.
Proof. vm_compute. reflexivity. Qed.
Section d.
Variable B : asyms.
Hypothesis HB : PcapSyms B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis TL : PcapSyms B.
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
zero_shadow (aview tfibsegs (w_H W) mem) SHADOW_OFF 0x10000 ((symaddr (Symbols.AsanUbsan.Sec.s_rodata + 68136)%Z) - 0x10000).
Proof.
intros ly S W mem md HAR.
exact (al_zshadow _ _ LAWS ly S W mem md (0x10000, (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 68136)%Z) - 0x10000) HAR
ltac:(unfold zero_shadow_ranges; right; rewrite (ts_zsh B HB); cbn; tauto)).
Qed.
Lemma rodata_hull_zero : forall ly S W mem md p n, AR tfibsegs B ly S W mem md -> (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 0x280)%Z) <= p -> p + n <= (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 68128)%Z) -> 0 < n ->
hull_zero (aview tfibsegs (w_H W) mem) p n.
Proof.
intros ly S W mem md p n HAR Hp Hn Hn0. pose proof (rodata_zero_shadow ly S W mem md HAR) as HZ.
intros s Hs. unfold shadow_addr in Hs.
assert (L1 : (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 0x280)%Z) / 8 <= p / 8) by (apply Z.div_le_mono; lia).
assert (L2 : (p + n - 1) / 8 <= ((symaddr (Symbols.AsanUbsan.Sec.s_rodata + 68128)%Z) - 1) / 8) by (apply Z.div_le_mono; lia).
change ((symaddr (Symbols.AsanUbsan.Sec.s_rodata + 0x280)%Z) / 8) with 8364 in L1. change (((symaddr (Symbols.AsanUbsan.Sec.s_rodata + 68128)%Z) - 1) / 8) with 16799 in L2.
pose proof (Z.div_mod (SHADOW_OFF + p / 8) 8 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound (SHADOW_OFF + p / 8) 8 ltac:(lia)) as D1'.
pose proof (Z.div_mod (SHADOW_OFF + (p + n - 1) / 8) 8 ltac:(lia)) as D2. pose proof (Z.mod_pos_bound (SHADOW_OFF + (p + n - 1) / 8) 8 ltac:(lia)) as D2'.
replace s with (shadow_of_addr SHADOW_OFF 0x10000 + (s - shadow_of_addr SHADOW_OFF 0x10000)) by lia.
apply (HZ (s - shadow_of_addr SHADOW_OFF 0x10000)).
unfold shadow_of_addr, SHADOW_OFF in *. change (65536 / 8) with 8192. change (((symaddr (Symbols.AsanUbsan.Sec.s_rodata + 68136)%Z) - 65536) / 8) with 8609. lia.
Qed.
Lemma rodata_shadow_facts : forall ly S W mem md p n, AR tfibsegs B ly S W mem md -> (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 0x280)%Z) <= p -> p + n <= (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 68128)%Z) -> 0 < n ->
range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF p n /\ shadow_hull_vis (aview tfibsegs (w_H W) mem) p n.
Proof.
intros ly S W mem md p n HAR Hp Hn Hn0. split.
- intros x Hx. apply (zero_shadow_range _ SHADOW_OFF 0x10000 ((symaddr (Symbols.AsanUbsan.Sec.s_rodata + 68136)%Z) - 0x10000) eq_refl eq_refl (rodata_zero_shadow ly S W mem md HAR) x). lia.
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
[ first [ apply (CH R_A1a 65536 (symaddr ((Symbols.AsanUbsan.Sec.s_rodata + 0x8) - (65536))%Z)); [cbn; tauto | reflexivity | cbn; tauto | cbn; lia | cbn; lia]
| apply (CH R_A1b (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 0x10)%Z) 24); [cbn; tauto | reflexivity | cbn; tauto | cbn; lia | cbn; lia]
| apply (CH R_A1c (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 0x30)%Z) 24); [cbn; tauto | reflexivity | cbn; tauto | cbn; lia | cbn; lia]
| apply (CH R_A1d (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 0x50)%Z) 104); [cbn; tauto | reflexivity | cbn; tauto | cbn; lia | cbn; lia]
| apply (CH R_A1e (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 0xc8)%Z) 8); [cbn; tauto | reflexivity | cbn; tauto | cbn; lia | cbn; lia]
| apply (CH R_A1f (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 0xd8)%Z) 104); [cbn; tauto | reflexivity | cbn; tauto | cbn; lia | cbn; lia]
| apply (CH R_A1g (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 0x180)%Z) 192); [cbn; tauto | reflexivity | cbn; tauto | cbn; lia | cbn; lia]
| apply (CH R_A1h (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 0x280)%Z) 50936); [cbn; tauto | reflexivity | cbn; tauto | cbn; lia | cbn; lia]
| apply (CH R_A1i (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 0xc98d)%Z) 15891); [cbn; tauto | reflexivity | cbn; tauto | cbn; lia | cbn; lia]
| apply (CH R_A1j (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 67492)%Z) 649); [cbn; tauto | reflexivity | cbn; tauto | cbn; lia | cbn; lia]
| apply (CH R_A1k (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 68160)%Z) 35); [cbn; tauto | reflexivity | cbn; tauto | cbn; lia | cbn; lia]
| apply (CH R_A1l (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 68224)%Z) 1412); [cbn; tauto | reflexivity | cbn; tauto | cbn; lia | cbn; lia]
| apply (CH R_A1m (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 69640)%Z) 96); [cbn; tauto | reflexivity | cbn; tauto | cbn; lia | cbn; lia]
| apply (CH R_A1n (symaddr (Symbols.AsanUbsan.s_sysconf_values + 0x3e)%Z) (symaddr ((626688) - (Symbols.AsanUbsan.s_sysconf_values + 0x3e))%Z)); [cbn; tauto | reflexivity | cbn; tauto | cbn; lia | cbn; lia] ] |]).
apply Forall_nil.
Qed.
Lemma mconsts_of_IMG : forall E W mem, mem_ok tfibsegs E (mrestrict (w_H W) mem) IMG_REGIONS -> mconsts_view W mem.
Proof.
intros E W mem HM a Ha. pose proof mc_bounds as [B1 B2].
pose proof (img_rd_of_mem_ok E _ IMG_REGIONS R_A1d (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 0x50)%Z) 104 HM ltac:(cbn; tauto) eq_refl ltac:(cbn; tauto) a ltac:(lia)) as Hm.
unfold aview. rewrite Hm. unfold img_byte. reflexivity.
Qed.
End d.
End c.
