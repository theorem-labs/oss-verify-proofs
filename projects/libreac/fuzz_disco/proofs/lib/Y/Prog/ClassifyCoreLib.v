(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the generic part of proofs/cgif/cgif_file_fuzzer/lib/YC1i.v for libreac/fuzz_disco's program walk (ceil, alias_srlw_sll, req_size_pos', PTR, Bspan, region_kept_at1) over fuzz_disco's listing; cgif's create_byte_list_block walk is left out; module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/YC1i.v, with its module names changed; 851 of its 884 lines of code are new or changed and 36 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/ClassifyCoreM2.v; 599 of its 683 lines of code are new or changed and 800 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/ClassifyCoreLib.v, with its module paths changed; 5 of its 661 lines of code are new or changed and 27 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP09 YI04 YI09 YI08 YI00 YN3v YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YG0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP0b YP0a YP0c YP0d YP07 YC80 YI0w YI0z YI12 YC4a YC1f YC44 YC8g YC8i.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YC1g YC1h YC81 YC4b YC45 YC85 YCkd.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import ReacPortsParse ClassifyCore ClassifyCoreSeg.
Import ListNotations.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Lemma clib_fs2 : fs_frame_bytes 2 = 256.
Proof. reflexivity. Qed.

Lemma clib_stk_pos : 0 <= CLS_STK.
Proof. unfold CLS_STK, CLS_OWN_BCMP, CLS_VIA_PARSE, CLS_PARSE_NEED, CLS_FRAME, ESTACK. lia. Qed.

Lemma clib_mod8 : forall x, x mod 64 = 0 -> x mod 8 = 0.
Proof.
intros x H. pose proof (Z.div_mod x 64 ltac:(lia)). pose proof (Z.div_mod x 8 ltac:(lia)).
pose proof (Z.mod_pos_bound x 8 ltac:(lia)). lia.
Qed.

Lemma clib_mod16 : forall x, x mod 16 = 0 -> x mod 8 = 0.
Proof.
intros x H. pose proof (Z.div_mod x 16 ltac:(lia)). pose proof (Z.div_mod x 8 ltac:(lia)).
pose proof (Z.mod_pos_bound x 8 ltac:(lia)). lia.
Qed.

Lemma clib_sh8 : forall a, (SHADOW_OFF + a / 8) / 8 = 268431360 + a / 64.
Proof.
intros a. unfold SHADOW_OFF. replace 2147450880 with (268431360 * 8) by reflexivity.
rewrite Z.div_add_l by lia. rewrite Z.div_div by lia. reflexivity.
Qed.

Lemma clib_stk_ra : forall lo hi x, lo mod 4096 = 0 -> hi mod 4096 = 0 -> lo <= x < hi ->
0 <= x / 8 - lo / 8 < (hi - lo) / 8.
Proof.
intros lo hi x Hl Hh Hx.
apply Z.mod_divide in Hl as [k1 Hk1]; [|lia]. apply Z.mod_divide in Hh as [k2 Hk2]; [|lia]. subst lo hi.
assert (E1 : k1 * 4096 / 8 = k1 * 512) by (replace (k1 * 4096) with (k1 * 512 * 8) by lia; apply Z.div_mul; lia).
assert (E2 : (k2 * 4096 - k1 * 4096) / 8 = (k2 - k1) * 512)
  by (replace (k2 * 4096 - k1 * 4096) with ((k2 - k1) * 512 * 8) by lia; apply Z.div_mul; lia).
rewrite E1, E2.
pose proof (Z.div_mod x 8 ltac:(lia)). pose proof (Z.mod_pos_bound x 8 ltac:(lia)). lia.
Qed.

Lemma clib_stk_shv : forall lo hi p n s, lo mod 4096 = 0 -> hi mod 4096 = 0 -> lo <= p -> p + n <= hi -> 0 < n ->
(268431360 + p / 64) * 8 <= s < (268431360 + (p + n - 1) / 64) * 8 + 8 ->
0 <= s - (SHADOW_OFF + lo / 8) < (hi - lo) / 8.
Proof.
intros lo hi p n s Hl Hh Hp Hpn Hn Hs.
apply Z.mod_divide in Hl as [k1 Hk1]; [|lia]. apply Z.mod_divide in Hh as [k2 Hk2]; [|lia]. subst lo hi.
replace (k2 * 4096 - k1 * 4096) with ((k2 - k1) * 512 * 8) by lia.
replace (k1 * 4096 / 8) with (k1 * 512) by (replace (k1 * 4096) with (k1 * 512 * 8) by lia; rewrite Z.div_mul by lia; reflexivity).
rewrite Z.div_mul by lia.
pose proof (Z.div_mod p 64 ltac:(lia)). pose proof (Z.mod_pos_bound p 64 ltac:(lia)).
pose proof (Z.div_mod (p + n - 1) 64 ltac:(lia)). pose proof (Z.mod_pos_bound (p + n - 1) 64 ltac:(lia)).
unfold SHADOW_OFF. lia.
Qed.

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

Lemma clib_amem_band : forall p n a, amem_range p n -> kLowMemEnd <= a < kHighShadowEnd -> ~ (p <= a < p + n).
Proof. intros p n a H Ha Hp. zlia. Qed.

Lemma clib_app_nband : forall a, app_addr a -> ~ (kLowMemEnd <= a < kHighShadowEnd).
Proof. intros a [H0 H] Hb. zlia. Qed.

Lemma clib_app_band : forall x, app_addr x -> kLowMemEnd <= shadow_addr x < kHighShadowEnd.
Proof.
intros x Hx. pose proof (app_addr_below_ceil x Hx) as Hc. pose proof ASAN_CEIL_range as [[_ CR] _].
unfold app_addr, shadow_addr, SHADOW_OFF in *. pose proof (Z.div_mod x 8 ltac:(lia)).
pose proof (Z.mod_pos_bound x 8 ltac:(lia)). zlia.
Qed.

Lemma clib_sh_band : forall G N a, in_app G N -> 0 <= N -> SHADOW_OFF + G / 8 <= a < SHADOW_OFF + G / 8 + N / 8 ->
kLowMemEnd <= a < kHighShadowEnd.
Proof.
intros G N a [H0 H] HN Ha. pose proof ASAN_CEIL_range as [[_ CR] _].
pose proof (Z.div_mod G 8 ltac:(lia)). pose proof (Z.mod_pos_bound G 8 ltac:(lia)).
pose proof (Z.div_mod N 8 ltac:(lia)). pose proof (Z.mod_pos_bound N 8 ltac:(lia)).
unfold SHADOW_OFF in Ha. zlia.
Qed.

Lemma clib_shadow_in : forall G N x, G mod 8 = 0 -> N mod 8 = 0 -> G <= x < G + N ->
G / 8 <= x / 8 < G / 8 + N / 8.
Proof.
intros G N x HG HN Hx.
pose proof (Z.div_mod G 8 ltac:(lia)). pose proof (Z.div_mod N 8 ltac:(lia)).
pose proof (Z.div_mod x 8 ltac:(lia)). pose proof (Z.mod_pos_bound x 8 ltac:(lia)). lia.
Qed.

Lemma clib_sh_sep : forall F G N, 0 <= N -> F + 256 <= G \/ G + N <= F ->
shadow_addr F + 32 <= shadow_addr G \/ shadow_addr G + N / 8 <= shadow_addr F.
Proof.
intros F G N HN [H|H].
- left. pose proof (shadow_mono (F + 256) G H) as M. unfold shadow_addr in *.
  replace ((F + 256) / 8) with (F / 8 + 32) in M by (rewrite <- (Z.div_add F 32 8) by lia; f_equal; lia). lia.
- right. pose proof (shadow_range_end G N HN). pose proof (shadow_mono (G + N) F H). lia.
Qed.

Lemma clib_app_range : forall p n, 0 < n -> (forall a, p <= a < p + n -> app_addr a) ->
4096 <= p /\ (p + n <= kLowShadowBeg \/ kHighMemBeg <= p).
Proof.
intros p n Hn H. pose proof (H p ltac:(lia)) as H1. split; [unfold app_addr in H1; lia|].
destruct (Z_le_gt_dec (p + n) kLowShadowBeg) as [|Hc]; [left; lia|]. right.
destruct (Z_le_gt_dec kHighMemBeg p) as [|Hc2]; [lia|]. exfalso.
destruct H1 as [_ [H1|H1]]; [|lia].
pose proof (H kLowShadowBeg ltac:(lia)) as H3. unfold app_addr in H3. zlia.
Qed.

Lemma clib_off_range : forall p n, 0 < n -> (forall a, p <= a < p + n -> off_img a 1) -> off_img p n.
Proof.
intros p n Hn H. pose proof (H p ltac:(lia)) as H1. unfold off_img in *.
destruct (Z_le_gt_dec (p + n) IMG_LO) as [|Hc]; [left; lia|]. right.
destruct H1 as [H1|H1]; [|lia]. pose proof (H IMG_LO ltac:(lia)) as H3. unfold IMG_LO, IMG_TOP in *. lia.
Qed.

Lemma clib_sep_range : forall p n F N, 0 < n -> 0 < N -> (forall a, p <= a < p + n -> ~ (F <= a < F + N)) ->
p + n <= F \/ F + N <= p.
Proof.
intros p n F N Hn HN H. destruct (Z_le_gt_dec (p + n) F); [left; lia|].
destruct (Z_le_gt_dec (F + N) p); [right; lia|]. exfalso.
destruct (Z_le_gt_dec p F); [apply (H F); lia | apply (H p); lia].
Qed.

Lemma clib_shv_range : forall (rd : reader) x n, 0 < n ->
(forall a, x <= a < x + n -> shadow_hull_vis rd a 1) -> shadow_hull_vis rd x n.
Proof.
intros rd x n Hn H s Hs. unfold shadow_hull_vis, shadow_addr in *.
rewrite !clib_sh8 in Hs.
pose proof (Z.div_mod s 8 ltac:(lia)) as Ds. pose proof (Z.mod_pos_bound s 8 ltac:(lia)) as Bs.
pose proof (Z.div_mod x 64 ltac:(lia)) as Dx. pose proof (Z.mod_pos_bound x 64 ltac:(lia)) as Bx.
pose proof (Z.div_mod (x + n - 1) 64 ltac:(lia)) as Dy. pose proof (Z.mod_pos_bound (x + n - 1) 64 ltac:(lia)) as By.
remember (s / 8 - 268431360) as u eqn:Eu.
assert (Hu : x / 64 <= u <= (x + n - 1) / 64) by lia.
assert (Hex : exists a, x <= a < x + n /\ 64 * u <= a < 64 * u + 64).
{ destruct (Z_le_gt_dec (64 * u) x); [exists x | exists (64 * u)]; lia. }
destruct Hex as (a & Ha & Ha64).
assert (Hq : a / 64 = u) by (symmetry; apply (Z.div_unique_pos a 64 u (a - 64 * u)); lia).
specialize (H a Ha s). rewrite !clib_sh8 in H. replace (a + 1 - 1) with a in H by lia. rewrite Hq in H.
apply H. lia.
Qed.

Lemma clib_nwr : forall lk o (L : option (list byte)) p n,
(o + 24 <= p \/ p + n <= o) ->
(match L with None => True | Some _ => lk + 12 <= p \/ p + n <= lk end) ->
forall a, p <= a < p + n -> ~ cls_wr lk o L a.
Proof. intros lk o L p n Ho HL a Ha [H|H]; [lia|]. destruct L; [lia | exact H]. Qed.

Lemma clib_awr_cut : forall STK sp0 FP bl0 blc blc' lyc ly' own x a,
awr_byte STK sp0 FP bl0 blc lyc own a ->
(forall b n, In (b, n) blc -> In (b, n) blc') ->
(forall c p, frame_addr ly' c p = frame_addr lyc c p) ->
awr_byte STK sp0 FP bl0 blc' ly' (x :: own) a.
Proof.
intros STK sp0 FP bl0 blc blc' lyc ly' own x a
  [H|[(Hfp & b & n & Hin & Hr)|[(b & n & Hin & Hn & Hr)|(cid & pos & Hin & Hr)]]] Hb Hf.
- left. exact H.
- right; left. split; [exact Hfp|]. exists b, n. split; [exact (Hb b n Hin) | exact Hr].
- right; right; left. exists b, n. split; [exact (Hb b n Hin)|]. split; [exact Hn | exact Hr].
- right; right; right. exists cid, pos. split; [right; exact Hin|]. rewrite !Hf. exact Hr.
Qed.

Section f.
Context {PI : PAImg lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).

Lemma clib_garr8_kept : forall H H' (m m' : word -> option byte) p l,
(forall a, p <= a < p + Z.of_nat (length l) -> aview SEGS H' m' a = aview SEGS H m a) ->
garr8 SEGS (mrestrict H m) p l -> garr8 SEGS (mrestrict H' m') p l.
Proof.
intros H H' m m' p l Hk Hg. eapply garr8_frame; [exact Hg|]. intros a Ha. apply mbyte_of_aview. exact (Hk a Ha).
Qed.

Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.

Lemma clib_flag_off : forall ly S (W : world SEGS) mem md cid pos, AR SEGS B ly S W mem md -> In (cid, pos) (frames S) ->
off_img (flag_addr ly cid pos) 1.
Proof.
intros ly S W mem md cid pos (M & LG & _) Hin. pose proof (pa_img_cover ly S md LG) as [C1 C2].
destruct (frame_facts B ly S _ cid pos M Hin) as (_ & _ & _ & Hni & _ & _ & _ & _ & _ & _ & Hfl).
unfold off_img, flag_addr in *.
destruct (Z_le_gt_dec (ly_F ly + fs_flag_off cid pos + 1) IMG_LO) as [|H1]; [left; lia|].
destruct (Z_le_gt_dec IMG_TOP (ly_F ly + fs_flag_off cid pos)) as [|H2]; [right; lia|].
exfalso. apply Hni. exists (ly_F ly + fs_flag_off cid pos). split.
- unfold in_zr; cbn [fst snd]. unfold kFakeFlagsOff, kFakeFramesOff, kFakeStackSize in *. lia.
- left. unfold in_zr. lia.
Qed.

Lemma clib_wloc : forall STK sp0 FP ly S (W0 : world SEGS) mem0 md0 own lyc Sc (W : world SEGS) memc mdc k p n,
ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
cls_write B STK sp0 FP ly S lyc Sc own p n -> amem_range p n ->
(p + n <= ly_stk_lo lyc \/ ly_stk_hi lyc <= p) ->
forall a, p <= a < p + n ->
app_addr a /\ ~ aowned B lyc Sc a /\
((exists b m, In (b, m) (ablocks B lyc Sc) /\ b <= a < b + req_size m) \/
 (exists cid pos, In (cid, pos) own /\ frame_addr lyc cid pos <= a < frame_addr lyc cid pos + fs_frame_bytes cid)).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k p n HJ Hw Ham Hst a Ha.
pose proof HJ as (_ & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & _ & Hlo & Hhi & _) & _).
destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Elo & Ehi & _).
destruct (awr_byte_cases SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ (Hw a Ha)) as
  (Hno & [[_ Hs] | [(Happ & b & m & Hin & Hr & _) | (cid & pos & Hown & [[Happ Hr] | [Hband _]])]]).
- exfalso. rewrite Elo, Ehi in Hst. lia.
- split; [exact Happ|]. split; [exact Hno|]. left. exists b, m. auto.
- split; [exact Happ|]. split; [exact Hno|]. right. exists cid, pos.
  unfold in_zr, frame_rng in Hr. cbn [fst snd] in Hr. auto.
- exfalso. exact (clib_amem_band p n a Ham Hband Ha).
Qed.

Definition cls_core (cx : ccx) (fpos : Z) (W3 : world SEGS) (ly3 : alayout) (S3 : astate)
(mem3 : word -> option byte) (md3 : Model) : Prop :=
AR SEGS B ly3 S3 W3 mem3 md3 /\
frames S3 = (2, fpos) :: frames (x_Sc cx) /\ ~ In (2, fpos) (frames (x_Sc cx)) /\
Permutation (ablocks B ly3 S3) (ablocks B (x_lyc cx) (x_Sc cx)) /\
frame_addr ly3 2 fpos = cF cx fpos /\ flag_addr ly3 2 fpos = cFL cx fpos /\
tcls_kept B (x_lyc cx) (x_Sc cx) (x_W cx) (x_memc cx) W3 mem3 (cSP cx) (x_lk cx) (x_o cx) (x_L cx).

Section p.
Variable cx : ccx.
Hypothesis HPRE : cls_pre B cx.

Lemma cp_J : ajournal SEGS B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx)
  (x_own cx) (x_lyc cx) (x_Sc cx) (x_W cx) (x_memc cx) (x_mdc cx) (x_k cx).
Proof using LAWS HPRE. pose proof HPRE as (HJ & _). exact HJ. Qed.

Lemma cp_ARc : AR SEGS B (x_lyc cx) (x_Sc cx) (x_W cx) (x_memc cx) (x_mdc cx).
Proof using LAWS HPRE. exact (proj1 cp_J). Qed.

Lemma cp_own : forall c q, In (c, q) (x_own cx) -> In (c, q) (frames (x_Sc cx)).
Proof using LAWS HPRE.
pose proof cp_J as (_ & _ & _ & _ & _ & Hfrs & _). intros c q H. rewrite Hfrs. apply in_or_app. left. exact H.
Qed.

Lemma cp_stk : alloc_ceiling <= ly_stk_lo (x_lyc cx) /\ ly_stk_lo (x_lyc cx) + x_STK cx <= x_sp0 cx /\
  x_sp0 cx <= ly_stk_hi (x_lyc cx) /\ ly_top (x_lyc cx) <= 2 ^ 47 /\
  alloc_ceiling <= cSP cx - CLS_STK /\ cSP cx mod 16 = 0 /\ cSP cx + 32 <= ly_top (x_lyc cx) /\
  ly_top (x_lyc cx) = ly_top (x_ly cx) /\ ly_stk_lo (x_lyc cx) = ly_stk_lo (x_ly cx) /\
  ly_stk_hi (x_lyc cx) = ly_stk_hi (x_ly cx).
Proof using LAWS HPRE.
pose proof HPRE as (HJ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hal & Hstk & Hsp0 & Htop & _).
pose proof HJ as (_ & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & H2 & H3 & H4 & H5 & _ & _ & H8) & _).
destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Elo & Ehi & _).
unfold cSP. rewrite Etop, Elo, Ehi.
split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact Hal|].
split; [rewrite <- Etop; exact Htop|]. split; [reflexivity|]. split; reflexivity.
Qed.

Lemma cp_wloc : forall a, cls_wr (x_lk cx) (x_o cx) (x_L cx) a ->
  app_addr a /\ a < alloc_ceiling /\ ~ in_img SEGS a /\ off_img a 1 /\ ~ aowned B (x_lyc cx) (x_Sc cx) a /\
  ((exists b m, In (b, m) (ablocks B (x_lyc cx) (x_Sc cx)) /\ b <= a < b + req_size m) \/
   (exists cid pos, In (cid, pos) (x_own cx) /\
     frame_addr (x_lyc cx) cid pos <= a < frame_addr (x_lyc cx) cid pos + fs_frame_bytes cid)).
Proof using LAWS HPRE.
intros a Ha. pose proof cp_J as HJ. pose proof cp_ARc as HARc.
assert (Hloc : app_addr a /\ ~ aowned B (x_lyc cx) (x_Sc cx) a /\
  ((exists b m, In (b, m) (ablocks B (x_lyc cx) (x_Sc cx)) /\ b <= a < b + req_size m) \/
   (exists cid pos, In (cid, pos) (x_own cx) /\
     frame_addr (x_lyc cx) cid pos <= a < frame_addr (x_lyc cx) cid pos + fs_frame_bytes cid))).
{ pose proof HPRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
    _ & _ & Hord & _ & Howr & Hostk & HL & _).
  destruct Ha as [Ha | Ha].
  - exact (clib_wloc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ Howr (proj1 (proj2 (proj2 Hord))) Hostk a Ha).
  - revert Ha HL. destruct (x_L cx) as [Lb|]; intros Ha HL; [|destruct Ha].
    destruct HL as (_ & _ & _ & Hlrd & _ & Hlwr & Hlstk).
    exact (clib_wloc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ Hlwr (proj1 (proj2 (proj2 Hlrd))) Hlstk a Ha). }
destruct Hloc as (Happ & Hno & [(b & m & Hin & Hr) | (cid & pos & Hin & Hr)]).
- destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HARc Hin) as (_ & _ & Hce & _).
  pose proof (blk_off_imgP B _ _ _ _ _ _ _ HARc Hin) as Hoi.
  pose proof (blk_img SEGS B LAWS _ _ _ _ _ _ _ a HARc Hin Hr) as Hni.
  split; [exact Happ|]. split; [lia|]. split; [exact Hni|]. split; [unfold off_img in *; lia|].
  split; [exact Hno|]. left. exists b, m. auto.
- pose proof (cp_own cid pos Hin) as HinS.
  destruct (frames_bounds SEGS B LAWS _ _ _ _ _ _ _ HARc HinS) as (_ & Hce & _).
  pose proof (frm_off_imgP B _ _ _ _ _ _ _ HARc HinS) as Hoi.
  pose proof (frm_img SEGS B LAWS _ _ _ _ _ _ _ a HARc HinS Hr) as Hni.
  split; [exact Happ|]. split; [lia|]. split; [exact Hni|]. split; [unfold off_img in *; lia|].
  split; [exact Hno|]. right. exists cid, pos. auto.
Qed.

Lemma cp_wr_band : forall a, kLowMemEnd <= a < kHighShadowEnd -> ~ cls_wr (x_lk cx) (x_o cx) (x_L cx) a.
Proof using LAWS HPRE. intros a Ha Hw. destruct (cp_wloc a Hw) as (Happ & _). exact (clib_app_nband a Happ Ha). Qed.

Lemma cp_wr_hi : forall a, alloc_ceiling <= a -> ~ cls_wr (x_lk cx) (x_o cx) (x_L cx) a.
Proof using LAWS HPRE. intros a Ha Hw. destruct (cp_wloc a Hw) as (_ & Hlt & _). lia. Qed.

Section c.
Variable fpos : Z.
Variable W3 : world SEGS.
Variable ly3 : alayout.
Variable S3 : astate.
Variable mem3 : word -> option byte.
Variable md3 : Model.
Hypothesis HCORE : cls_core cx fpos W3 ly3 S3 mem3 md3.

Lemma cc_Fly : forall c p, frame_addr ly3 c p = frame_addr (x_lyc cx) c p.
Proof using LAWS HPRE HCORE.
pose proof HCORE as (_ & _ & _ & _ & HF & _). unfold cF, frame_addr in *. intros c p. lia.
Qed.

Lemma cc_in3 : forall c p, In (c, p) (frames (x_Sc cx)) -> In (c, p) (frames S3).
Proof using LAWS HPRE HCORE. pose proof HCORE as (_ & Hfr & _). intros c p H. rewrite Hfr. right. exact H. Qed.

Lemma cc_in3F : In (2, fpos) (frames S3).
Proof using LAWS HPRE HCORE. pose proof HCORE as (_ & Hfr & _). rewrite Hfr. left. reflexivity. Qed.

Lemma cc_blk3 : forall b m, In (b, m) (ablocks B (x_lyc cx) (x_Sc cx)) -> In (b, m) (ablocks B ly3 S3).
Proof using LAWS HPRE HCORE.
pose proof HCORE as (_ & _ & _ & Hp & _). intros b m H.
eapply Permutation_in; [apply Permutation_sym; exact Hp | exact H].
Qed.

Lemma cc_F : 4096 <= cF cx fpos /\ cF cx fpos + 256 <= alloc_ceiling /\ in_app (cF cx fpos) 256 /\
  cF cx fpos mod 64 = 0 /\ off_img (cF cx fpos) 256 /\
  (forall a, cF cx fpos <= a < cF cx fpos + 256 -> apresent (w_H W3) mem3 a /\ ~ aowned B ly3 S3 a) /\
  (forall i, 0 <= i < 32 ->
    apresent (w_H W3) mem3 (SHADOW_OFF + cF cx fpos / 8 + i) /\ ~ aowned B ly3 S3 (SHADOW_OFF + cF cx fpos / 8 + i)) /\
  cF cx fpos mod 32 = 0.
Proof using LAWS HPRE HCORE.
pose proof HCORE as (HAR & _ & _ & _ & HF & _).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ _ _ HAR cc_in3F) as (H1 & H2 & H3).
destruct (frame_al64 SEGS B _ _ _ _ _ _ _ HAR cc_in3F) as (H4 & _).
pose proof (frm_off_imgP B _ _ _ _ _ _ _ HAR cc_in3F) as H5.
destruct (al_frames _ _ LAWS _ _ _ _ _ _ _ HAR cc_in3F) as (H6 & _ & H7 & H8).
rewrite HF, clib_fs2 in *. unfold shadow_addr in H8. change (256 / 8) with 32 in H8.
split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|].
split; [exact H7|]. split; [exact H8|]. exact H6.
Qed.

Lemma cc_FL : 4096 <= cFL cx fpos /\ zone2 (cFL cx fpos) 1 /\ cFL cx fpos < alloc_ceiling /\
  apresent (w_H W3) mem3 (cFL cx fpos) /\ aowned B ly3 S3 (cFL cx fpos) /\ ~ in_img SEGS (cFL cx fpos).
Proof using LAWS HPRE HCORE.
pose proof HCORE as (HAR & _ & _ & _ & _ & HFL & _).
destruct (al_flag _ _ LAWS _ _ _ _ _ _ _ HAR cc_in3F) as (H1 & H2 & H3 & H4).
pose proof (clib_flag_off _ _ _ _ _ _ _ HAR cc_in3F) as H5.
pose proof (al_client_img _ _ LAWS _ _ _ _ _ (flag_addr ly3 2 fpos) HAR
  (or_intror (or_intror (ex_intro _ 2 (ex_intro _ fpos (conj cc_in3F eq_refl)))))) as [_ H6].
rewrite HFL in *.
split; [destruct H3 as [H3 _]; lia|]. split; [exact (zone2_of_app _ _ H3 H5)|].
split; [exact H4|]. split; [exact H1|]. split; [exact H2|]. exact H6.
Qed.

Lemma cc_sepF : forall cid pos, In (cid, pos) (frames (x_Sc cx)) ->
  frame_addr (x_lyc cx) cid pos + fs_frame_bytes cid <= cF cx fpos \/
  cF cx fpos + 256 <= frame_addr (x_lyc cx) cid pos.
Proof using LAWS HPRE HCORE.
intros cid pos Hin. pose proof HCORE as (HAR & Hfr3 & _ & _ & HF3 & _).
apply in_split in Hin as (l1 & l2 & El).
assert (Hd : zdisjoint (frame_rng ly3 (2, fpos)) (frame_rng ly3 (cid, pos))).
{ apply (sep_frames_pos SEGS B LAWS _ _ _ _ _ _ _ [] l1 l2 HAR). rewrite Hfr3, El. reflexivity. }
unfold zdisjoint, frame_rng in Hd. cbn [fst snd] in Hd. rewrite HF3, cc_Fly, clib_fs2 in Hd. lia.
Qed.

Lemma cc_sepB : forall b m, In (b, m) (ablocks B (x_lyc cx) (x_Sc cx)) ->
  b + req_size m <= cF cx fpos \/ cF cx fpos + 256 <= b.
Proof using LAWS HPRE HCORE.
intros b m Hin. pose proof HCORE as (HAR & _ & _ & _ & HF3 & _).
pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ _ _ _ _ HAR (cc_blk3 b m Hin) cc_in3F) as Hd.
rewrite HF3, clib_fs2 in Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd. exact Hd.
Qed.

Lemma cc_ra_frame : forall cid pos x, In (cid, pos) (frames (x_Sc cx)) ->
frame_addr (x_lyc cx) cid pos <= x < frame_addr (x_lyc cx) cid pos + fs_frame_bytes cid ->
(exists s, aview SEGS (w_H (x_W cx)) (x_memc cx) (shadow_of_addr SHADOW_OFF x) = Some s /\ saddr_ok x s) ->
exists s, aview SEGS (w_H W3) mem3 (shadow_of_addr SHADOW_OFF x) = Some s /\ saddr_ok x s.
Proof using LAWS HPRE HCORE.
intros cid pos x Hin Hx (s & Hs & Hok). exists s. split; [|exact Hok].
pose proof HCORE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & K4 & _).
pose proof cp_ARc as HARc.
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ _ _ HARc Hin) as (G0 & Gc & Gapp).
destruct (frame_al64 SEGS B _ _ _ _ _ _ _ HARc Hin) as (Ga & Nb & N64).
pose proof (clib_app_band x (in_app_addr _ _ x Gapp Hx)) as Hb.
unfold shadow_of_addr in *. unfold shadow_addr in Hb.
rewrite (K4 cid pos (SHADOW_OFF + x / 8) Hin); [exact Hs | right | apply cp_wr_band; exact Hb].
unfold in_zr, shadow_addr. cbn [fst snd].
pose proof (clib_shadow_in _ _ x (clib_mod8 _ Ga) (clib_mod8 _ Nb) Hx). lia.
Qed.

Lemma cc_kept_step : forall (mem4 : word -> option byte) (Wr : Z -> Prop),
(forall a, 0 <= a < 2 ^ 64 -> ~ Wr a -> aview SEGS (w_H W3) mem4 a = aview SEGS (w_H W3) mem3 a) ->
(forall a, apresent (w_H W3) mem3 a -> apresent (w_H W3) mem4 a) ->
(forall a, Wr a ->
  (cSP cx - CLS_STK <= a < cSP cx) \/ cls_wr (x_lk cx) (x_o cx) (x_L cx) a \/
  (cF cx fpos <= a < cF cx fpos + 256) \/
  (SHADOW_OFF + cF cx fpos / 8 <= a < SHADOW_OFF + cF cx fpos / 8 + 32) \/ a = cFL cx fpos) ->
tcls_kept B (x_lyc cx) (x_Sc cx) (x_W cx) (x_memc cx) W3 mem4 (cSP cx) (x_lk cx) (x_o cx) (x_L cx).
Proof using LAWS HPRE HCORE.
intros mem4 Wr Heq Hpr HWr.
pose proof HCORE as (HAR & Hfr3 & Hnin & Hperm & HF3 & HFL3 & K1 & K2 & K3 & K4 & K5 & K6).
pose proof cp_ARc as HARc.
pose proof cp_stk as (_ & _ & _ & _ & Hwin & _).
pose proof cc_F as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & _).
pose proof cc_FL as (L1 & L2 & L3 & L4 & L5 & L6).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HshF : forall a, SHADOW_OFF + cF cx fpos / 8 <= a < SHADOW_OFF + cF cx fpos / 8 + 32 ->
  kLowMemEnd <= a < kHighShadowEnd).
{ intros a Ha. apply (clib_sh_band (cF cx fpos) 256 a F3 ltac:(lia)). change (256 / 8) with 32. exact Ha. }
split.
{ intros a Ha Hw Hc. rewrite <- (K1 a Ha Hw Hc). apply Heq; [lia|]. intros HW.
  destruct (HWr a HW) as [H|[H|[H|[H|H]]]]; [exact (Hw H) | exact (Hc H) | lia | pose proof (HshF a H); zlia | lia]. }
split.
{ intros b m i Hin Hi Hc. rewrite <- (K2 b m i Hin Hi Hc).
  pose proof (cc_blk3 b m Hin) as Hin3.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin3) as (_ & Hb0 & Hbc & Happ & Hbo & _).
  pose proof (cc_sepB b m Hin) as Hd.
  pose proof (in_app_addr _ _ (b + i) Happ ltac:(lia)) as Happ'.
  apply Heq; [lia|]. intros HW.
  destruct (HWr _ HW) as [H|[H|[H|[H|H]]]].
  - lia.
  - exact (Hc H).
  - lia.
  - exact (clib_app_nband _ Happ' (HshF _ H)).
  - pose proof (proj2 (Hbo (b + i) ltac:(lia))) as Hn. rewrite H in Hn. exact (Hn L5). }
split.
{ intros a Hi Hns He. rewrite <- (K3 a Hi Hns He).
  pose proof (pa_segs_low a Hi) as Hl. pose proof (pa_img_range a Hi) as Hr.
  apply Heq; [zlia|]. intros HW.
  destruct (HWr _ HW) as [H|[H|[H|[H|H]]]].
  - zlia.
  - exact (proj1 (proj2 (proj2 (cp_wloc a H))) Hi).
  - unfold off_img, IMG_LO, IMG_TOP in F5, Hr. lia.
  - pose proof (HshF _ H). zlia.
  - rewrite H in Hi. exact (L6 Hi). }
split.
{ intros cid pos a Hin Hr Hc. rewrite <- (K4 cid pos a Hin Hr Hc).
  pose proof (cc_in3 cid pos Hin) as Hin3.
  destruct (frames_bounds SEGS B LAWS _ _ _ _ _ _ _ HARc Hin) as (G0 & Gc & Gapp).
  destruct (al_frames _ _ LAWS _ _ _ _ _ _ _ HAR Hin3) as (_ & _ & Hfo & Hso).
  rewrite cc_Fly in Hfo, Hso.
  pose proof (cc_sepF cid pos Hin) as Hd.
  pose proof (fs_frame_bytes_nonneg cid) as Nn.
  unfold in_zr, frame_rng in Hr. cbn [fst snd] in Hr.
  destruct Hr as [Hr | Hr].
  - pose proof (in_app_addr _ _ a Gapp Hr) as Happ.
    apply Heq; [lia|]. intros HW.
    destruct (HWr _ HW) as [H|[H|[H|[H|H]]]].
    + lia.
    + exact (Hc H).
    + lia.
    + exact (clib_app_nband _ Happ (HshF _ H)).
    + pose proof (proj2 (Hfo a Hr)) as Hn. rewrite H in Hn. exact (Hn L5).
  - unfold shadow_addr in Hr, Hso.
    pose proof (clib_sh_band _ _ a Gapp Nn Hr) as Hb.
    apply Heq; [zlia|]. intros HW.
    destruct (HWr _ HW) as [H|[H|[H|[H|H]]]].
    + zlia.
    + exact (Hc H).
    + exact (clib_app_nband _ (in_app_addr _ _ a F3 H) Hb).
    + pose proof (clib_sh_sep (cF cx fpos) (frame_addr (x_lyc cx) cid pos) (fs_frame_bytes cid) Nn ltac:(lia)) as Hs.
      unfold shadow_addr in Hs. lia.
    + pose proof (proj2 (Hso (a - (SHADOW_OFF + frame_addr (x_lyc cx) cid pos / 8)) ltac:(lia))) as Hn.
      replace (SHADOW_OFF + frame_addr (x_lyc cx) cid pos / 8 + (a - (SHADOW_OFF + frame_addr (x_lyc cx) cid pos / 8)))
        with a in Hn by lia.
      rewrite H in Hn. exact (Hn L5). }
split.
{ intros a Ha Hw Hp. apply Hpr. exact (K5 a Ha Hw Hp). }
intros a Ha. apply Hpr. exact (K6 a Ha).
Qed.

Lemma cc_sep_obj : forall p n, 0 < n ->
cls_read (x_W cx) (x_memc cx) (cSP cx) p n -> cls_sep B (x_lyc cx) (x_Sc cx) p n ->
(forall a, p <= a < p + n -> ~ cls_wr (x_lk cx) (x_o cx) (x_L cx) a) ->
ly_stk_lo ly3 = ly_stk_lo (x_lyc cx) -> ly_stk_hi ly3 = ly_stk_hi (x_lyc cx) ->
cls_obj_ok cx fpos W3 mem3 p n /\
(forall a, p <= a < p + n -> aview SEGS (w_H W3) mem3 a = aview SEGS (w_H (x_W cx)) (x_memc cx) a).
Proof using LAWS HPRE HCORE.
intros p n Hn (Hp0 & Hp63 & Ham & Hsw & Hpres & Hra & Hshv) Hsep Hnw Elo Ehi.
pose proof HCORE as (HAR & Hfr3 & Hnin & Hperm & HF3 & HFL3 & K1 & K2 & K3 & K4 & K5 & K6).
pose proof cp_ARc as HARc.
pose proof cp_stk as (Hce & _ & _ & _ & Hwin & _).
pose proof cc_F as (F1 & F2 & F3 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold cls_obj_ok, cls_addr, cls_live. cbv zeta.
assert (H47 : p + n <= 2 ^ 47) by zlia.
destruct Hsep as [(cid & pos & Hin & H1 & H2) | [(b & m & Hin & H1 & H2) | (H1 & H2)]].
- pose proof (cc_in3 cid pos Hin) as Hin3.
  destruct (frames_bounds SEGS B LAWS _ _ _ _ _ _ _ HARc Hin) as (G0 & Gc & Gapp).
  pose proof (frm_off_imgP B _ _ _ _ _ _ _ HARc Hin) as Goi.
  destruct (al_frames _ _ LAWS _ _ _ _ _ _ _ HAR Hin3) as (_ & _ & Hfo & _). rewrite cc_Fly in Hfo.
  pose proof (shadow_hull_vis_of_frame SEGS B LAWS _ _ _ _ _ _ _ p n HAR Hin3) as Hsv. rewrite !cc_Fly in Hsv.
  pose proof (cc_sepF cid pos Hin) as Hd.
  assert (Hkept : forall a, p <= a < p + n -> aview SEGS (w_H W3) mem3 a = aview SEGS (w_H (x_W cx)) (x_memc cx) a).
  { intros a Ha. apply (K4 cid pos a Hin); [left; unfold in_zr, frame_rng; cbn [fst snd]; lia | apply Hnw; exact Ha]. }
  split; [|exact Hkept].
  split.
  { split; [lia|]. split; [exact H47|]. split; [exact Ham|]. split; [unfold off_img in *; lia|].
    unfold in_app in Gapp. lia. }
  split.
  { split; [intros a Ha; exact (proj1 (Hfo a ltac:(lia)))|].
    split; [intros x Hx; exact (cc_ra_frame cid pos x Hin ltac:(lia) (Hra x Hx))|].
    exact (Hsv ltac:(lia) ltac:(lia) Hn). }
  split; [lia | exact Hsw].
- pose proof (cc_blk3 b m Hin) as Hin3.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HARc Hin) as (_ & B0 & Bc & Bapp & _).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin3) as (_ & _ & _ & _ & Bo3 & _).
  pose proof (blk_off_imgP B _ _ _ _ _ _ _ HARc Hin) as Boi.
  pose proof (cc_sepB b m Hin) as Hd.
  assert (Hkept : forall a, p <= a < p + n -> aview SEGS (w_H W3) mem3 a = aview SEGS (w_H (x_W cx)) (x_memc cx) a).
  { intros a Ha. replace a with (b + (a - b)) by lia. apply (K2 b m (a - b) Hin); [lia|].
    replace (b + (a - b)) with a by lia. apply Hnw; exact Ha. }
  split; [|exact Hkept].
  split.
  { split; [lia|]. split; [exact H47|]. split; [exact Ham|]. split; [unfold off_img in *; lia|].
    unfold in_app in Bapp. lia. }
  split.
  { split; [intros a Ha; exact (proj1 (Bo3 a ltac:(lia)))|].
    split; [exact (range_addressable_of_block SEGS B LAWS _ _ _ _ _ _ _ p n HAR Hin3 ltac:(lia) ltac:(lia))|].
    exact (shadow_hull_vis_of_block SEGS B LAWS _ _ _ _ _ _ _ p n HAR Hin3 ltac:(lia) ltac:(lia) Hn). }
  split; [lia | exact Hsw].
- pose proof HAR as (M3 & _). pose proof (am_layout _ _ _ _ M3) as LO.
  destruct (lo_top _ LO) as (_ & _ & _ & _ & Hpa1 & Hpa2 & _).
  pose proof (al_zshadow _ _ LAWS _ _ _ _ _ (ly_stk_lo ly3, ly_stk_hi ly3 - ly_stk_lo ly3) HAR (or_introl eq_refl)) as Hz.
  unfold zero_shadow, page_aligned in *. cbn [fst snd] in Hz. rewrite Elo, Ehi in Hz. rewrite Elo in Hpa1. rewrite Ehi in Hpa2.
  set (lo := ly_stk_lo (x_lyc cx)) in *. set (hi := ly_stk_hi (x_lyc cx)) in *.
  assert (Hkept : forall a, p <= a < p + n -> aview SEGS (w_H W3) mem3 a = aview SEGS (w_H (x_W cx)) (x_memc cx) a).
  { intros a Ha. apply K1; [lia | lia | apply Hnw; exact Ha]. }
  split; [|exact Hkept].
  split.
  { split; [lia|]. split; [exact H47|]. split; [exact Ham|]. split; [unfold off_img, IMG_TOP; right; lia|].
    right. unfold kHighMemBeg. lia. }
  split.
  { split; [intros a Ha; apply K5; [lia | lia | apply Hpres; exact Ha]|].
    split.
    { intros x Hx. exists 0. split; [| left; reflexivity].
      pose proof (clib_stk_ra lo hi x Hpa1 Hpa2 ltac:(lia)) as Hi.
      replace (shadow_of_addr SHADOW_OFF x) with (shadow_of_addr SHADOW_OFF lo + (x / 8 - lo / 8))
        by (unfold shadow_of_addr; lia).
      apply Hz. exact Hi. }
    intros s Hs. unfold shadow_addr in Hs. rewrite !clib_sh8 in Hs.
    pose proof (clib_stk_shv lo hi p n s Hpa1 Hpa2 H1 H2 Hn Hs) as Hi.
    replace s with (shadow_of_addr SHADOW_OFF lo + (s - shadow_of_addr SHADOW_OFF lo)) by lia.
    rewrite Hz; [discriminate|]. unfold shadow_of_addr. exact Hi. }
  split; [lia | exact Hsw].
Qed.

Lemma cc_wobj : forall p n, 0 < n ->
cls_read (x_W cx) (x_memc cx) (cSP cx) p n ->
cls_write B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_lyc cx) (x_Sc cx) (x_own cx) p n ->
(p + n <= ly_stk_lo (x_lyc cx) \/ ly_stk_hi (x_lyc cx) <= p) ->
cls_obj_ok cx fpos W3 mem3 p n /\ 4096 <= p /\ p + n <= alloc_ceiling /\
(forall a, p <= a < p + n ->
  awr_byte (x_STK cx) (x_sp0 cx) (x_FP cx) (ablocks B (x_ly cx) (x_S cx)) (ablocks B ly3 S3) ly3 ((2, fpos) :: x_own cx) a).
Proof using LAWS HPRE HCORE.
intros p n Hn Hrd Hw Hst. pose proof Hrd as (Hp0 & Hp63 & Ham & Hsw & Hpres & Hra & Hshv).
pose proof cp_J as HJ. pose proof cp_ARc as HARc.
pose proof HCORE as (HAR & Hfr3 & Hnin & Hperm & HF3 & HFL3 & K1 & K2 & K3 & K4 & K5 & K6).
pose proof (clib_wloc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ Hw Ham Hst) as Hloc.
assert (Hbyte : forall a, p <= a < p + n ->
  app_addr a /\ a < alloc_ceiling /\ off_img a 1 /\ apresent (w_H W3) mem3 a /\
  (exists s, aview SEGS (w_H W3) mem3 (shadow_of_addr SHADOW_OFF a) = Some s /\ saddr_ok a s) /\
  shadow_hull_vis (aview SEGS (w_H W3) mem3) a 1 /\ ~ (cF cx fpos <= a < cF cx fpos + 256)).
{ intros a Ha. destruct (Hloc a Ha) as (Happ & _ & [(b & m & Hin & Hr) | (cid & pos & Hin & Hr)]).
  - pose proof (cc_blk3 b m Hin) as Hin3.
    destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HARc Hin) as (_ & _ & Bc & _).
    pose proof (blk_off_imgP B _ _ _ _ _ _ _ HARc Hin) as Boi.
    destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin3) as (_ & _ & _ & _ & Bo3 & _).
    pose proof (cc_sepB b m Hin) as Hd.
    split; [exact Happ|]. split; [lia|]. split; [unfold off_img in *; lia|]. split; [exact (proj1 (Bo3 a Hr))|].
    split; [exact (range_addressable_of_block SEGS B LAWS _ _ _ _ _ _ _ a 1 HAR Hin3 ltac:(lia) ltac:(lia) a ltac:(lia))|].
    split; [exact (shadow_hull_vis_of_block SEGS B LAWS _ _ _ _ _ _ _ a 1 HAR Hin3 ltac:(lia) ltac:(lia) ltac:(lia))|].
    lia.
  - pose proof (cp_own cid pos Hin) as HinS. pose proof (cc_in3 cid pos HinS) as Hin3.
    destruct (frames_bounds SEGS B LAWS _ _ _ _ _ _ _ HARc HinS) as (_ & Gc & _).
    pose proof (frm_off_imgP B _ _ _ _ _ _ _ HARc HinS) as Goi.
    destruct (al_frames _ _ LAWS _ _ _ _ _ _ _ HAR Hin3) as (_ & _ & Hfo & _). rewrite cc_Fly in Hfo.
    pose proof (shadow_hull_vis_of_frame SEGS B LAWS _ _ _ _ _ _ _ a 1 HAR Hin3) as Hsv. rewrite !cc_Fly in Hsv.
    pose proof (cc_sepF cid pos HinS) as Hd.
    split; [exact Happ|]. split; [lia|]. split; [unfold off_img in *; lia|]. split; [exact (proj1 (Hfo a Hr))|].
    split; [exact (cc_ra_frame cid pos a HinS Hr (Hra a Ha))|].
    split; [exact (Hsv ltac:(lia) ltac:(lia) ltac:(lia))|].
    lia. }
assert (Happ : 4096 <= p /\ (p + n <= kLowShadowBeg \/ kHighMemBeg <= p)).
{ apply clib_app_range; [lia|]. intros a Ha. destruct (Hbyte a Ha) as (H & _). exact H. }
split.
{ unfold cls_obj_ok, cls_addr, cls_live. cbv zeta.
  split.
  { split; [lia|]. split; [zlia|]. split; [exact Ham|].
    split; [apply clib_off_range; [lia|]; intros a Ha; destruct (Hbyte a Ha) as (_ & _ & H & _); exact H|].
    exact (proj2 Happ). }
  split.
  { split; [intros a Ha; destruct (Hbyte a Ha) as (_ & _ & _ & H & _); exact H|].
    split; [intros x Hx; destruct (Hbyte x Hx) as (_ & _ & _ & _ & H & _); exact H|].
    apply clib_shv_range; [lia|]. intros a Ha. destruct (Hbyte a Ha) as (_ & _ & _ & _ & _ & H & _). exact H. }
  split; [|exact Hsw].
  apply clib_sep_range; [lia | lia |]. intros a Ha. destruct (Hbyte a Ha) as (_ & _ & _ & _ & _ & _ & H). exact H. }
split; [exact (proj1 Happ)|].
split; [destruct (Hbyte (p + n - 1) ltac:(lia)) as (_ & H & _); lia|].
intros a Ha. apply (clib_awr_cut _ _ _ _ (ablocks B (x_lyc cx) (x_Sc cx)) _ (x_lyc cx));
  [exact (Hw a Ha) | exact cc_blk3 | exact cc_Fly].
Qed.

End c.
End p.

Lemma cls_kept_step : cls_kept_step_ok B.
Proof.
intros cx fpos W3 ly3 S3 mem3 md3 mem4 Wr Hpre HAR Hfr Hnin Hperm HF HFL HK.
exact (cc_kept_step cx Hpre fpos W3 ly3 S3 mem3 md3
  (conj HAR (conj Hfr (conj Hnin (conj Hperm (conj HF (conj HFL HK)))))) mem4 Wr).
Qed.

Lemma cls_achain : cls_achain_ok B.
Proof.
intros cx fpos pc RV O3 L3 SHP PS LS W3 ly3 S3 regs3 mem3 md3 Hpre Hcut.
pose proof Hcut as (HJ3 & Hfr & Hnin & Hperm & HF & HFL & HK & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hsp & _).
pose proof Hpre as (HJ & _ & _ & Hra & _ & _ & _ & _ & _ & _ & _ & Hch & _).
pose proof (cp_stk cx Hpre) as (_ & _ & _ & Ht47 & Hwin & Hal & Htop & Etopc & _).
pose proof HJ3 as (_ & Hly3 & _). destruct Hly3 as (_ & _ & _ & _ & _ & _ & _ & _ & Etop3 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold cls_spills in Hsp.
pose proof (Forall_inv Hsp) as Hs1. pose proof (Forall_inv (Forall_inv_tail Hsp)) as Hs8.
cbn [fst snd] in Hs1, Hs8.
pose proof clib_stk_pos as Hsp0.
pose proof (rdword_of_val_mem SEGS (w_H W3) mem3 _ _ Hs1
  ltac:(pose proof (bv_unsigned_in_range 64 (getr (x_regs cx) (Z_to_bv 5 1))) as Hu;
        change (bv_modulus 64) with (2 ^ 64) in Hu; exact Hu)) as Hr1.
pose proof (rdword_of_val_mem SEGS (w_H W3) mem3 _ _ Hs8
  ltac:(pose proof (bv_unsigned_in_range 64 (getr (x_regs cx) (Z_to_bv 5 8))) as Hu;
        change (bv_modulus 64) with (2 ^ 64) in Hu; exact Hu)) as Hr8.
change (bv_unsigned (getr (x_regs cx) (Z_to_bv 5 1))) with (raZ (x_regs cx)) in Hr1.
change (bv_unsigned (getr (x_regs cx) (Z_to_bv 5 8))) with (s0Z (x_regs cx)) in Hr8.
replace (cSP cx + -8) with (cSP cx - 8) in Hr1 by lia.
replace (cSP cx + -16) with (cSP cx - 16) in Hr8 by lia.
assert (HS1 : cS1 cx + 16 <= cSP cx).
{ unfold cS1, cls_S1. pose proof (Z.mul_div_le (cSP cx - 160) 32 ltac:(lia)). lia. }
exists ((cSP cx, raZ (x_regs cx), s0Z (x_regs cx)) :: x_ch cx).
apply (achain_ly_top (x_lyc cx)); [rewrite Etop3, Etopc; reflexivity|].
apply (achain_push (x_lyc cx) (aview SEGS (w_H (x_W cx)) (x_memc cx)) (aview SEGS (w_H W3) mem3)
  (cSP cx) (s0Z (x_regs cx)) (raZ (x_regs cx)) (x_ch cx) (cS1 cx) Hch).
- lia.
- intros a Ha. destruct HK as (K1 & _). apply K1; [lia | lia | apply (cp_wr_hi cx Hpre); lia].
- exact Hr1.
- exact Hr8.
- exact Hra.
- lia.
- exact (clib_mod16 _ Hal).
- lia.
- exact HS1.
Qed.

Lemma cls_now : cls_now_ok B.
Proof.
intros cx fpos pc RV O3 L3 SHP PS LS W3 ly3 S3 regs3 mem3 md3 Hpre Hcut.
pose proof Hcut as (HJ3 & Hfr & Hnin & Hperm & HF & HFL & HK & _).
assert (HC : cls_core cx fpos W3 ly3 S3 mem3 md3)
  by exact (conj (proj1 HJ3) (conj Hfr (conj Hnin (conj Hperm (conj HF (conj HFL HK)))))).
pose proof (proj1 HJ3) as HAR3.
pose proof HJ3 as (_ & Hly3 & _). destruct Hly3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Elo3 & Ehi3 & _).
pose proof (cp_stk cx Hpre) as (_ & _ & _ & _ & _ & _ & _ & _ & Eloc & Ehic).
assert (Elo : ly_stk_lo ly3 = ly_stk_lo (x_lyc cx)) by (rewrite Elo3, Eloc; reflexivity).
assert (Ehi : ly_stk_hi ly3 = ly_stk_hi (x_lyc cx)) by (rewrite Ehi3, Ehic; reflexivity).
pose proof Hpre as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HlFB & HlU & _ &
  Hf & Hurd & Husep & Hug & _ & _ & Hord & _ & Howr & Hostk & HL & Hou & Hof & HLs).
pose proof (cc_F cx Hpre fpos W3 ly3 S3 mem3 md3 HC) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8).
pose proof (cc_FL cx Hpre fpos W3 ly3 S3 mem3 md3 HC) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6).
cbv zeta.
split.
{ split; [exact F1|]. split; [exact F2|]. split; [exact F8|]. split; [exact (zone2_of_app _ _ F3 F5)|].
  split; [exact F3|].
  split; [intros a Ha; exact (proj1 (F6 a Ha))|]. split; [intros i Hi; exact (proj1 (F7 i Hi))|].
  split; [exact Q1|]. split; [exact Q2|]. split; [exact Q3|]. split; [exact Q4|]. split; [exact Q5|].
  split; [intros Hx; exact (proj2 (F6 _ Hx) Q5)|].
  split.
  - intros b n Hin.
    pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ _ _ _ _ HAR3 Hin (cc_in3F cx Hpre fpos W3 ly3 S3 mem3 md3 HC)) as Hd.
    rewrite HF, clib_fs2 in Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd. exact Hd.
  - intros c p Hin. rewrite (cc_Fly cx Hpre fpos W3 ly3 S3 mem3 md3 HC). exact (cc_sepF cx Hpre fpos W3 ly3 S3 mem3 md3 HC c p Hin). }
split.
{ intros Hl. destruct (Hf Hl) as (Hf0 & Hfrd & Hfsep & Hfg).
  assert (HLf : match x_L cx with None => True | Some _ => x_lk cx + 12 <= x_f cx \/ x_f cx + 50 <= x_lk cx end).
  { revert HLs. destruct (x_L cx); intros HLs; [destruct HLs as (_ & _ & Hx); exact (Hx Hl) | exact I]. }
  destruct (cc_sep_obj cx Hpre fpos W3 ly3 S3 mem3 md3 HC (x_f cx) 50 ltac:(lia) Hfrd Hfsep
    (clib_nwr _ _ _ _ _ (Hof Hl) HLf) Elo Ehi) as (Hok & Hkept).
  split; [|exact Hok]. apply (clib_garr8_kept (w_H (x_W cx)) (w_H W3) (x_memc cx) mem3 _ _); [|exact Hfg].
  intros a Ha. apply Hkept. unfold cls_bytes in Ha. rewrite length_map, HlFB in Ha. lia. }
assert (HLu : match x_L cx with None => True | Some _ => x_lk cx + 12 <= x_u cx \/ x_u cx + 6 <= x_lk cx end).
{ revert HLs. destruct (x_L cx); intros HLs; [destruct HLs as (_ & Hx & _); exact Hx | exact I]. }
destruct (cc_sep_obj cx Hpre fpos W3 ly3 S3 mem3 md3 HC (x_u cx) 6 ltac:(lia) Hurd Husep
  (clib_nwr _ _ _ _ _ Hou HLu) Elo Ehi) as (Huok & Hukept).
split.
{ apply (clib_garr8_kept (w_H (x_W cx)) (w_H W3) (x_memc cx) mem3 _ _); [|exact Hug].
  intros a Ha. apply Hukept. unfold cls_bytes in Ha. rewrite length_map, HlU in Ha. lia. }
split; [exact Huok|].
destruct (cc_wobj cx Hpre fpos W3 ly3 S3 mem3 md3 HC (x_o cx) 24 ltac:(lia) Hord Howr Hostk) as (Hook & Ho4 & Hoc & Hoaw).
split; [exact Hook|]. split; [exact Ho4|]. split; [exact Hoc|]. split; [exact Hoaw|].
revert HL. destruct (x_L cx) as [Lb|]; intros HL; [|exact I].
destruct HL as (_ & _ & _ & Hlrd & _ & Hlwr & Hlstk).
exact (cc_wobj cx Hpre fpos W3 ly3 S3 mem3 md3 HC (x_lk cx) 12 ltac:(lia) Hlrd Hlwr Hlstk).
Qed.

End h.
End f.
End d.
