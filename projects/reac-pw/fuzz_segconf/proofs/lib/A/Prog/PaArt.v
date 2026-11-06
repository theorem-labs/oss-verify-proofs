(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the step of a program walk through a runtime entry whose contract is art_post (lib/A/Rt/RtDefs.v), after cgif_file_fuzzer's aj_memcmp_at (lib/YCbq.v) and aj_intrin_atS (lib/A/Prog/PaCall.v); the facts a walk reads at such a call, carried from the entry to a state whose memory differs only in the stack window; the runtime entries' call pre-state at a point of the walk; and small list and arithmetic lemmas these steps use. Written for plugin-hostd/fuzz_command's sup_reply_code walk. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/plugin-hostd/fuzz_command/lib/A/Prog/PaArt.v (origin/ossv/recipes 501c0d516c69) for reac-pw/fuzz_segconf's image A (fuzz_segconf.asan): module paths. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaCall.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require Import RtDefs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Lemma nth_skipn_add : forall {A} (l : list A) j i d, nth i (skipn j l) d = nth (j + i) l d.
Proof.
induction l as [|a l IH]; intros [|j] i d; cbn; [destruct i; reflexivity | destruct i; reflexivity | reflexivity | apply IH].
Qed.
(* the tail of a C string from its j-th byte is a C string *)
Lemma astr_atR_skipn : forall rd p s j, astr_atR rd p s -> (j <= length s)%nat -> astr_atR rd (p + Z.of_nat j) (skipn j s).
Proof.
intros rd p s j [H1 H2] Hj. split.
- intros i Hi. rewrite length_app, length_skipn in Hi. cbn [length] in Hi.
replace (p + Z.of_nat j + Z.of_nat i) with (p + Z.of_nat (j + i)) by lia.
rewrite (H1 (j + i)%nat) by (rewrite length_app; cbn [length]; lia).
replace (skipn j s ++ [Z_to_bv 8 0]) with (skipn j (s ++ [Z_to_bv 8 0])).
+ rewrite nth_skipn_add. reflexivity.
+ rewrite skipn_app. replace (j - length s)%nat with 0%nat by lia. reflexivity.
- intros Hin. apply H2. rewrite <- (firstn_skipn j s). apply in_or_app. right. exact Hin.
Qed.
(* the 8-byte word that holds a byte below a 4096-aligned bound ends at or below it *)
Lemma tail_below : forall e c, 0 <= e < c -> c mod 4096 = 0 -> e - e mod 8 + 8 <= c.
Proof.
intros e c He Hc. pose proof (Z.div_mod e 8 ltac:(lia)). pose proof (Z.mod_pos_bound e 8 ltac:(lia)).
pose proof (Z.div_mod c 4096 ltac:(lia)). rewrite Hc in H1. lia.
Qed.
Lemma In_of_existsb : forall x l, existsb (Z.eqb x) l = true -> In x l.
Proof. intros x l H. apply existsb_exists in H as (y & Hy & E). apply Z.eqb_eq in E. subst. exact Hy. Qed.
(* every read-only word the runtime entries read lies in the low image *)
Lemma rt_rom_ranges_low : forall l n a, In (l, n) RT_ROM_RANGES -> l <= a < l + n -> 0 <= a < 0x30000.
Proof.
intros l n a Hin Ha.
assert (Hall : forallb (fun r => (0 <=? fst r) && (fst r + snd r <=? 0x30000)) RT_ROM_RANGES = true) by (vm_compute; reflexivity).
rewrite forallb_forall in Hall. specialize (Hall (l, n) Hin). cbn [fst snd] in Hall.
apply andb_true_iff in Hall as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. lia.
Qed.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
(* The step through a runtime entry whose contract is art_post (lib/A/Rt/RtDefs.v): the entry writes its
   scratch window below the current sp and the cells [Eb], all of them inside the errno cell. The journal of the
   walk goes on through it with the same footprint and event budget, by cgif's call_effect_journal and
   ajournal_sub (lib/YCbq.v), as aj_memcmp_at and aj_intrin_atS do for cgif's own entries. *)
Section j.
Variable segs : list Segment.
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.
Hypothesis errno_low : api_env segs B.
Lemma aj_art_at : forall stk (Eb : Z -> Prop) pc W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k (o : Z) raw
(Qr : bvmap 5 word -> (word -> option byte) -> Prop),
ajournal segs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 0 <= stk -> stk - o <= STK ->
getr regsT 1 = raw ->
(forall a, Eb a -> as_errno B <= a < as_errno B + 4) ->
SRr segs W (cfg_at segs pc regsT memT mdc) (art_post segs B stk lyc Sc W regsT memT mdc Eb Qr) ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom segs)) mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal segs B STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\
aregs_preserved regsT regs2 /\ Qr regs2 mem2 /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + o - stk <= a < sp0 + o) -> ~ Eb a ->
aview segs (w_H W) mem2 a = aview segs (w_H W) memT a)).
Proof.
intros stk Eb pc W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k o raw Qr
HJ Hsp Hal Hneg Hstk Hbud Hraw HEb HC.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & _ & _ & _ & _ & _ & Hpres & Hstatic & F5 & HQT).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
assert (ASTACK = 16384) as Has by reflexivity.
eapply SRr_mono; [exact HC|].
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsame & HQ & Hfr & Hpres2 & Hscr).
split; [reflexivity|]. exists regs2, mem2, md2.
split; [unfold cfg_at, raZ, w64; rewrite Hraw, Z_to_bv_bv_unsigned; reflexivity|].
split.
{ assert (HJ1 : ajournal segs B stk (spZ regsT) [] lyc Sc W memT mdc [] lyc Sc W mem2 md2 0).
{ eapply (call_effect_journal segs B LAWS segs_low errno_low stk lyc Sc W regsT memT mdc lyc Sc W mem2 md2
(fun _ => False) [] [] 0);
[exact HAR2 | apply layout_le_refl | apply wle_refl | apply same_io_materialized; exact Hsame | | exact Hscr | exact HAR
| | reflexivity | lia | lia | lia | intros a [] | intros p n i H1 H2; exfalso; exact (H2 H1) | exact HQT].
- intros a H0 _ _ H3 _. apply (Hfr a H0).
+ intros Hs. apply H3. left. exact Hs.
+ intros He. apply H3. right. exact (HEb a He).
- unfold astk_ok, ly_bot in *. rewrite Etop, Eslo, Eshi. rewrite Hsp.
repeat split; first [rewrite Z.add_mod, Hal16, Hal by lia; reflexivity | lia]. }
pose proof (ajournal_sub_tok segs B LAWS segs_low STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k stk (spZ regsT) []
[] lyc Sc W mem2 md2 0 HJ HJ1 ltac:(lia) ltac:(lia) ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha))) as HJ2.
rewrite app_nil_l, Z.add_0_r in HJ2. exact HJ2. }
split; [exact HP|]. split; [exact HQ|].
intros a Ha Hw He. apply (Hfr a Ha); [|exact He]. unfold ascratch_stk. rewrite Hsp. exact Hw.
Qed.

(* The facts the walk reads at a call, carried from the entry to a state whose memory agrees with the entry's outside
   the stack window [lo, hi): every address they name lies below lo. *)
Definition kept_out (rd rd' : reader) (lo hi : Z) : Prop :=
forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> rd' a = rd a.
Lemma kept_out_trans : forall rd1 rd2 rd3 lo hi lo' hi',
kept_out rd1 rd2 lo hi -> kept_out rd2 rd3 lo' hi' -> lo <= lo' -> hi' <= hi -> kept_out rd1 rd3 lo hi.
Proof. intros rd1 rd2 rd3 lo hi lo' hi' H12 H23 Hl Hh a Ha Hn. rewrite (H23 a Ha) by lia. exact (H12 a Ha Hn). Qed.
Lemma abytes_atR_kept : forall rd rd' lo hi p l, kept_out rd rd' lo hi -> abytes_atR rd p l ->
0 <= p -> p + Z.of_nat (length l) <= lo -> lo < 2 ^ 64 -> abytes_atR rd' p l.
Proof. intros rd rd' lo hi p l HK H Hp Hl Hlo i Hi. rewrite (HK (p + Z.of_nat i)) by lia. exact (H i Hi). Qed.
Lemma astr_atR_kept : forall rd rd' lo hi p s, kept_out rd rd' lo hi -> astr_atR rd p s ->
0 <= p -> p + Z.of_nat (length s) + 1 <= lo -> lo < 2 ^ 64 -> astr_atR rd' p s.
Proof.
intros rd rd' lo hi p s HK [H1 H2] Hp Hl Hlo. split; [|exact H2].
apply (abytes_atR_kept rd rd' lo hi p _ HK H1 Hp); [rewrite length_app; cbn [length]; lia | exact Hlo].
Qed.
Lemma rdword_kept : forall rd rd' lo hi a v, kept_out rd rd' lo hi -> rdword rd a = Some v ->
0 <= a -> a + 8 <= lo -> lo < 2 ^ 64 -> rdword rd' a = Some v.
Proof. intros rd rd' lo hi a v HK H Ha Hl Hlo. rewrite (rdword_ext rd rd' a); [exact H|]. intros k Hk. apply HK; lia. Qed.
Lemma rd32_kept : forall rd rd' lo hi a v, kept_out rd rd' lo hi -> rd32 rd a v ->
0 <= a -> a + 4 <= lo -> lo < 2 ^ 64 -> rd32 rd' a v.
Proof. intros rd rd' lo hi a v HK H Ha Hl Hlo k Hk. rewrite (HK (a + Z.of_nat k)) by lia. exact (H k Hk). Qed.
Lemma aguard_ok_kept : forall W mem mem' lo hi g gd,
kept_out (aview segs (w_H W) mem) (aview segs (w_H W) mem') lo hi -> aguard_ok segs W mem g gd ->
0 <= g -> g + 8 <= lo -> 0 <= gd -> gd + 8 <= lo -> lo < 2 ^ 64 -> aguard_ok segs W mem' g gd.
Proof.
intros W mem mem' lo hi g gd HK [H1 [c H2]] Hg Hg8 Hd Hd8 Hlo.
split; [exact (rdword_kept _ _ lo hi g gd HK H1 Hg Hg8 Hlo) | exists c; exact (rdword_kept _ _ lo hi gd c HK H2 Hd Hd8 Hlo)].
Qed.
Lemma atail_vis_kept : forall W mem mem' lo hi e,
kept_out (aview segs (w_H W) mem) (aview segs (w_H W) mem') lo hi -> atail_vis segs W mem e ->
0 <= e -> e - e mod 8 + 8 <= lo -> lo < 2 ^ 64 -> atail_vis segs W mem' e.
Proof.
intros W mem mem' lo hi e HK H He Hl Hlo a Ha. pose proof (Z.mod_pos_bound e 8 ltac:(lia)).
rewrite (HK a) by lia. exact (H a Ha).
Qed.
Lemma rconsts_view_kept : forall W mem mem' lo hi rr,
kept_out (aview segs (w_H W) mem) (aview segs (w_H W) mem') lo hi -> rconsts_view segs W mem rr ->
(forall l n a, In (l, n) rr -> l <= a < l + n -> 0 <= a < lo) -> lo < 2 ^ 64 -> rconsts_view segs W mem' rr.
Proof.
intros W mem mem' lo hi rr HK H Hb Hlo l n a Hin Ha. pose proof (Hb l n a Hin Ha). rewrite (HK a) by lia. exact (H l n a Hin Ha).
Qed.
Lemma aread_ok_kept : forall stk stk' W regs regs' mem mem' lo hi x n,
kept_out (aview segs (w_H W) mem) (aview segs (w_H W) mem') lo hi -> aread_ok segs stk W regs mem x n ->
x + n <= lo -> kHighShadowEnd <= lo -> x + n <= 2 ^ 47 -> lo <= spZ regs' - stk' -> lo < 2 ^ 64 ->
aread_ok segs stk' W regs' mem' x n.
Proof.
intros stk stk' W regs regs' mem mem' lo hi x n HK (H0 & H1 & H2 & H3 & H4 & H5 & H6) Hx Hk Hx47 Hs Hlo.
split; [exact H0|]. split; [exact H1|]. split; [exact H2|]. split.
{ intros a Ha. split; [rewrite (HK a) by lia; exact (proj1 (H3 a Ha)) | unfold ascratch_stk; lia]. }
split; [exact H4|]. split.
- exact (range_addressable_kept_win _ _ lo hi x n HK Hk H0 Hx47 H5).
- intros Hn. exact (shadow_hull_vis_kept_win _ _ lo hi x n HK Hk H0 Hx47 Hn (H6 Hn)).
Qed.
(* a range inside a live block is one the entries may read, at a state whose sp lies above the heap *)
Lemma aread_ok_of_block : forall stk ly S W regs mem md p k x n,
AR segs B ly S W mem md -> In (p, k) (ablocks B ly S) -> p <= x -> x + n <= p + k -> 0 <= n ->
alloc_ceiling <= spZ regs - stk -> aread_ok segs stk W regs mem x n.
Proof.
intros stk ly S W regs mem md p k x n HAR Hin Hx Hxn Hn Hs.
destruct (al_blocks _ _ LAWS ly S W mem md p k HAR Hin) as (Hp16 & Hp4096 & Hpceil & Hpapp & Hpres & _ & Hk).
pose proof (req_size_pos k ltac:(lia)) as [_ Hreq].
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). unfold MALLOC_MAX in Hk.
split; [lia|]. split; [lia|]. split; [lia|]. split.
{ intros a Ha. split; [apply (aview_some_of_apresent segs); exact (proj1 (Hpres a ltac:(lia))) | unfold ascratch_stk; lia]. }
split; [exact (amem_range_of_block segs B LAWS ly S W mem md p k x n HAR Hin Hx ltac:(lia))|]. split.
- exact (range_addressable_of_block segs B LAWS ly S W mem md p k x n HAR Hin Hx ltac:(lia)).
- intros Hn0. exact (shadow_hull_vis_of_block segs B LAWS ly S W mem md p k x n HAR Hin Hx ltac:(lia) Hn0).
Qed.
(* the runtime-call pre-state of the runtime entries (ecall_pre with a window), at a point of the walk *)
Lemma ecall_pre_stk_at : forall stk STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k regsc (o : Z),
ajournal segs B STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k ->
spZ regsc = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK <= stk -> stk - o <= STK ->
YK0s.ret_ok (getr regsc 1) -> getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
ecall_pre_stk segs B stk lyc Sc W regsc memc mdc.
Proof.
intros stk STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k regsc o HJ Hsp Hal Hneg Hes Hbud Hra Hgp Htp.
split; [eapply (ecall_pre_at segs B STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k regsc o HJ Hsp Hal Hneg); 
  [lia | exact Hra | exact Hgp | exact Htp]|].
pose proof HJ as (_ & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstatic & _ & _).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
split; [rewrite Eslo, Hsp; lia|]. intros a Ha. unfold ascratch_stk in Ha. apply Hpres. lia.
Qed.
End j.
End d.
