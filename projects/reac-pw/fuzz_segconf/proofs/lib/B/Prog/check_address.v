(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8h.v:104-108;
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACbk.v:76-79; projects/cgif/cgif_file_fuzzer/proofs/lib/A/AChd.v:200-203, 358-361,
   386-392, 532-535, for libreac/fuzz_identity's ASan build (lib/A). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/reac_box_family_stem.v, with its module paths and module names changed; 95 of its 123 lines of code are new or changed and 244 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/fuzz_catalogue_rowA.v, with its module paths and module names changed; 335 of its 377 lines of code are new or changed and 81 lines of the source are left out. *)
(* the image-B port of lib/A/Prog/check_address.v (commit 254b4716bf4f, walk text of
   9ba251f91a3c): the walk of check_address on fuzz_segconf.asan-ubsan (image B, entry BASE + AF_check_address =
   0x84dc0 + 0x26ac = 0x8746c, 84 bytes, 21 instructions, a 32-byte frame, no instrumented check, no side-stack frame),
   against lib/B/Prog/check_address_c.v's check_address_contract (image B's copy of lib/A/Prog/check_address_c.v,
   FINAL 6f783602b5e3).
   RELOCATION: image B's code is image A's 20 instructions word for word except the four pc-relative `jal` words
   (wrapper_strlen 0x43a98 at 0x87488, wrapper_strncmp 0x43aa4 at 0x87498, the no-return hook 0x5df0c at 0x874b4,
   abort 0x910c4 at 0x874b8), which the listing states as the slots PCall SS_<callee>; UBSan adds one word, the trap
   `unimp` at 0x874bc, after `jal abort`. No branch targets 0x874bc (the one branch, `bnez a0` at 0x8749c, targets
   0x874b4) and the only way to fall into it is through `jal abort`, on the arm refuted below, and abort does not
   return: no path of the walk reaches the trap.
   The run: the symbolic executor over the position-abstract listing (lib/B/Prog/SegList.v) runs from the entry to
   each wrapper call; each call applies the wrapper's contract (Section hypotheses STRLEN, STRNCMP:
   lib/B/Rt/RtString.v, image A's theorem names) through PaArt.aj_art_at; the state after a call is rebuilt with
   jafter_call_keep_hi; the branch at 0x8749c is split with paj_branch, its taken arm (0x874b4 the no-return hook,
   0x874b8 abort) refuted by the contract's model premise SegModel.strncmp gs ws (SegModel.strlen ws) = 0, and the
   fall-through ends at the `ret` 0x874b0 with paj_ret_at.
   Memory: the function and both wrappers write only the stack window [sp0 - 32 - 2 * ESTACK, sp0), above the
   allocation ceiling, and both strings lie in live heap blocks below it, so every fact of the strings holds at
   each call site ([ca_kw]); the same writes give the post's sa_kept ([ca_kwin]).
   Image-B numbers, image B's instance file lib/B/Prog/SegInstB.v: the stack window SegInstB.STK_check_address
   (32 + 2 * ESTACK) and the read-only window SegInstB.RLO_A / RHI_A (the B listing's SegGlob.SEG_RLO / SEG_RHI,
   0xa1c60 .data.rel.ro start, 0xa3f08 .got end); the entry stays the listing term BASE + AF_check_address.
   Step plan: the unit record's Bwalks-G45-plans/plan-check_address.md. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YP0j YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI04 YI08.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05 YI00 YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList SegPa SegPaLib PaDenot PaLibG PaLibF PaLibH PaCallRun PaCall PaArt.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require SegModel StrFun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require RtString.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import check_address_lem check_address_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require SegGlob SegInstB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* the entry state: registers as atoms, the 32-byte frame below sp writable *)
Definition ss_ca0 : sstate := mkSS AF_check_address sr_atoms [stack_region 32] None (mkFacts [] [] []).

(* image B's stack window of this call, SegInstB.STK_check_address: the 32-byte frame (`addi sp,sp,-32` at 0x8746c)
   and the strncmp wrapper's window 2 * ESTACK (0x87498), the deeper of the two wrapper windows (strlen at 0x87488
   asks ESTACK) *)
#[local] Notation CA_STK := SegInstB.STK_check_address.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ seg_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* the memory below the allocation ceiling is the same in m and m' *)
Definition ca_kw (W : world SEGS) (m m' : word -> option byte) : Prop :=
forall a, 0 <= a < alloc_ceiling -> aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a.
Lemma ca_kw_refl : forall W m, ca_kw W m m.
Proof. intros W m a _. reflexivity. Qed.
Lemma ca_kw_trans : forall W m1 m2 m3, ca_kw W m1 m2 -> ca_kw W m2 m3 -> ca_kw W m1 m3.
Proof. intros W m1 m2 m3 K1 K2 a Ha. rewrite (K2 a Ha). exact (K1 a Ha). Qed.
Lemma ca_kw_of_win : forall W m m' lo hi, alloc_ceiling <= lo ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a) -> ca_kw W m m'.
Proof. intros W m m' lo hi Hlo H a Ha. pose proof asan_consts as (C1 & _). apply H; lia. Qed.
(* the memory outside the stack window [lo, hi) is the same in m and m' *)
Definition ca_kwin (W : world SEGS) (lo hi : Z) (m m' : word -> option byte) : Prop :=
forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a.
Lemma ca_kwin_refl : forall W lo hi m, ca_kwin W lo hi m m.
Proof. intros W lo hi m a _ _. reflexivity. Qed.
Lemma ca_kwin_trans : forall W lo hi m1 m2 m3, ca_kwin W lo hi m1 m2 -> ca_kwin W lo hi m2 m3 -> ca_kwin W lo hi m1 m3.
Proof. intros W lo hi m1 m2 m3 K1 K2 a Ha Hn. rewrite (K2 a Ha Hn). exact (K1 a Ha Hn). Qed.
Lemma ca_kwin_sub : forall W lo hi lo' hi' m m', ca_kwin W lo' hi' m m' -> lo <= lo' -> hi' <= hi -> ca_kwin W lo hi m m'.
Proof. intros W lo hi lo' hi' m m' K H1 H2 a Ha Hn. apply K; [exact Ha | lia]. Qed.
Lemma ca_astr_at_kw : forall W m m' x s, astr_at SEGS W m x s -> 0 <= x ->
x + Z.of_nat (length s) + 1 <= alloc_ceiling -> ca_kw W m m' -> astr_at SEGS W m' x s.
Proof.
intros W m m' x s [H1 H2] Hx Hl K. split; [|exact H2].
intros i Hi. rewrite length_app in Hi. cbn [length] in Hi. rewrite K by lia. exact (H1 i ltac:(rewrite length_app; cbn [length]; lia)).
Qed.
Lemma ca_atail_vis_kw : forall W m m' e, atail_vis SEGS W m e -> 0 <= e < alloc_ceiling -> ca_kw W m m' -> atail_vis SEGS W m' e.
Proof.
intros W m m' e H He K a Ha. pose proof (proj2 (@YG0f.ASAN_CEIL_range _)) as CM. unfold YG0f.ASAN_CEIL in CM.
pose proof (Z.div_mod e 8 ltac:(lia)) as D. pose proof (Z.mod_pos_bound e 8 ltac:(lia)) as M.
pose proof (Z.div_mod alloc_ceiling 4096 ltac:(lia)) as D2.
rewrite K by lia. exact (H a Ha).
Qed.
Lemma ca_rom_kw : forall B W m m', rt_rom_view SEGS B W m -> ca_kw W m m' -> rt_rom_view SEGS B W m'.
Proof.
intros B W m m' H K a Hr Ho He. pose proof asan_consts as (C1 & _ & _ & _ & C5).
assert (Hi : in_img SEGS a) by (destruct Hr as (sg & Hs & _ & Hsr); exists sg; split; [exact Hs | exact Hsr]).
pose proof (pa_segs_low _ Hi) as R. rewrite C5 in R.
rewrite K by lia. exact (H a Hr Ho He).
Qed.

(* the range facts a wrapper checks of [x, x + n), all below the allocation ceiling: RtDefs.aread_ok without its
   window part *)
Definition ca_rdf (W : world SEGS) (m : word -> option byte) (x n : Z) : Prop :=
0 < x /\ 0 <= n < 2 ^ 32 /\ x + n <= alloc_ceiling /\
(forall a, x <= a < x + n -> aview SEGS (w_H W) m a <> None) /\ amem_range x n /\
range_addressable (aview SEGS (w_H W) m) SHADOW_OFF x n /\ (0 < n -> shadow_hull_vis (aview SEGS (w_H W) m) x n).
Lemma ca_rdf_kw : forall W m m' x n, ca_rdf W m x n -> ca_kw W m m' -> ca_rdf W m' x n.
Proof.
intros W m m' x n (Hx & Hn & Hc & Hv & Ham & Hra & Hh) K. pose proof asan_consts as (C1 & C2 & _).
assert (HK : forall s, 0 <= s < 2 ^ 64 -> ~ (alloc_ceiling <= s < 2 ^ 64) -> aview SEGS (w_H W) m' s = aview SEGS (w_H W) m s)
by (intros s Hs Hns; apply K; lia).
split; [exact Hx|]. split; [exact Hn|]. split; [exact Hc|].
split; [intros a Ha; rewrite K by lia; apply Hv; exact Ha|]. split; [exact Ham|].
split; [exact (range_addressable_kept_win _ _ alloc_ceiling (2 ^ 64) x n HK ltac:(lia) ltac:(lia) ltac:(lia) Hra)|].
intros Hn0. exact (shadow_hull_vis_kept_win _ _ alloc_ceiling (2 ^ 64) x n HK ltac:(lia) ltac:(lia) ltac:(lia) Hn0 (Hh Hn0)).
Qed.
Lemma ca_rdf_sub : forall W m x n k, ca_rdf W m x n -> 0 <= k <= n -> ca_rdf W m x k.
Proof.
intros W m x n k (Hx & Hn & Hc & Hv & Ham & Hra & Hh) Hk.
split; [exact Hx|]. split; [lia|]. split; [lia|]. split; [intros a Ha; apply Hv; lia|].
split; [unfold amem_range in *; lia|]. split; [unfold range_addressable in *; intros y Hy; apply Hra; lia|].
intros Hk0. specialize (Hh ltac:(lia)). unfold shadow_hull_vis in *. intros s Hs. apply Hh.
assert (A1 : shadow_addr (x + k - 1) <= shadow_addr (x + n - 1)) by (unfold shadow_addr; apply Z.add_le_mono_l; apply Z.div_le_mono; lia).
assert (A2 : shadow_addr (x + k - 1) / 8 <= shadow_addr (x + n - 1) / 8) by (apply Z.div_le_mono; lia).
lia.
Qed.
Lemma ca_rdf_aread : forall W m (regs : bvmap 5 word) stk x n, ca_rdf W m x n -> alloc_ceiling <= spZ regs - stk ->
aread_ok SEGS stk W regs m x n.
Proof.
intros W m regs stk x n (Hx & Hn & Hc & Hv & Ham & Hra & Hh) Hs. pose proof asan_consts as (C1 & _).
unfold aread_ok. split; [lia|]. split; [lia|]. split; [lia|].
split; [intros a Ha; split; [apply Hv; lia | unfold ascratch_stk; lia]|].
split; [exact Ham|]. split; [exact Hra | exact Hh].
Qed.

Lemma ca_region_kept_win : forall E n lo hi wlo whi cs sp H (m m' : word -> option byte) wl wh,
bv_unsigned (ew E n) = sp ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (wl <= a < wh) -> aview SEGS H m' a = aview SEGS H m a) ->
wh <= sp + lo -> 0 <= sp + lo -> sp + hi <= 2 ^ 64 ->
(forall a, sp + wlo <= a < sp + whi -> apresent H m' a) ->
region_kept SEGS E (mrestrict H m) (mrestrict H m') (YP09.mkRegion (Some n) lo hi wlo whi cs).
Proof.
intros E n lo hi wlo whi cs sp H m m' wl wh Hn Hfr Hwh H0 H64 Hp.
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Hn; intros a Ha.
- apply (mbyte_of_aview SEGS). apply Hfr; lia.
- intros _. apply (apresent_writable SEGS). apply Hp. lia.
Qed.

(* every write of a stretch lands in the frame [sp0 - 32, sp0), above the allocation ceiling *)
Ltac ca_kw_run HFr Uspx KW0 KWn :=
lazymatch type of HFr with frame_of ?Ex ?rsx (mrestrict ?Hx ?m0) (mrestrict _ ?m1) =>
let KR := fresh "KR" in
assert (KR : forall a, 0 <= a < 2 ^ 64 -> ~ (alloc_ceiling <= a < 2 ^ 64) -> aview SEGS Hx m1 a = aview SEGS Hx m0 a)
by (apply (kept_of_frame (segs := SEGS) Ex rsx Hx m0 m1 (fun x => alloc_ceiling <= x < 2 ^ 64) HFr);
let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let x := fresh "x" in
let Hin := fresh "Hin" in let Hrr := fresh "Hrr" in let Hq := fresh "Hq" in
intros b wlo whi x Hin Hrr; vm_compute in Hin; destruct Hin as [Hq | []]; injection Hq as <- <- <-;
cbn [base_val] in Hrr; rewrite Uspx in Hrr; split; lia);
pose proof (ca_kw_trans _ _ _ _ KW0 (ca_kw_of_win _ m0 m1 alloc_ceiling (2 ^ 64) (Z.le_refl _) KR)) as KWn; clear KR
end.

(* the same stretch, kept outside the call's window [lo, hi): its only writes are its frame slots *)
Ltac ca_kin_run HFr Uspx K0 Kn lo hi :=
lazymatch type of HFr with frame_of ?Ex ?rsx (mrestrict (w_H ?Wx) ?m0) (mrestrict _ ?m1) =>
let KR := fresh "KR" in
assert (KR : ca_kwin Wx lo hi m0 m1)
by (unfold ca_kwin; apply (kept_of_frame (segs := SEGS) Ex rsx (w_H Wx) m0 m1 (fun x => lo <= x < hi) HFr);
let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let x := fresh "x" in
let Hin := fresh "Hin" in let Hrr := fresh "Hrr" in let Hq := fresh "Hq" in
intros b wlo whi x Hin Hrr; vm_compute in Hin; destruct Hin as [Hq | []]; injection Hq as <- <- <-;
cbn [base_val] in Hrr; rewrite Uspx in Hrr; split; lia);
pose proof (ca_kwin_trans _ _ _ _ _ _ K0 KR) as Kn; clear KR
end.

(* the state after a wrapper call: st_ok_pi over fresh atoms from K for the clobbered registers, the frame kept *)
Ltac ca_after HS K W regs2 mem2 HP2 HFR2 HJ2 Uspx HS2 :=
jafter_call_keep_hi HS K regs2 (mrestrict (w_H W) mem2) HP2 [0%nat] HS2;
let HRK := fresh "HRK" in
match type of HS2 with ?P -> _ => assert (HRK : P) end;
[ cbn [ms_mem restrict]; constructor; [|constructor];
eapply ca_region_kept_win; [exact Uspx | exact HFR2 | lia | lia | lia |];
let a := fresh "a" in let Ha := fresh "Ha" in let Hp := fresh "Hp" in
intros a Ha; pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hp & _); apply Hp; lia
| specialize (HS2 HRK); clear HRK; rewrite <- restrict_mkst_fx in HS2 ].

Section e.
Variable B : asyms.
Hypothesis STRLEN : forall fx0 : YK11.FPState, @RtString.astrlen_realizes fx0 rc SEGS B (SIGMA SS___interceptor_trampoline_strlen).
Hypothesis STRNCMP : forall fx0 : YK11.FPState, @RtString.astrncmp_realizes fx0 rc SEGS B (SIGMA SS___interceptor_trampoline_strncmp).
Hypothesis TL : PALib B.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUNP := SRr_run_pi_AJ B LAWS.
Let RUNC := SRr_run_pi_AJ_call B LAWS.
Let BR := paj_branch (L := seg_listing) (PI := PI).
Let RET := paj_ret_at (L := seg_listing) (PI := PI).
Let ART := aj_art_at SEGS B LAWS pa_segs_low (pal_env B TL).

(* a string of a live heap block, as the facts the two wrappers ask of it *)
Lemma ca_heap_str : forall ly S W mem md p s,
AR SEGS B ly S W mem md ->
sa_heap B ly S p (Z.of_nat (length s) + 1) -> astr_at SEGS W mem p s ->
ca_rdf W mem p (Z.of_nat (length s) + 1) /\ amem_range p (astr_len s + 8).
Proof.
intros ly S W mem md p s HAR (q & k & Hin & Hq & Hqk) Hst. pose proof asan_consts as (C1 & _).
assert (Hvis : forall a, p <= a < p + (Z.of_nat (length s) + 1) -> aview SEGS (w_H W) mem a <> None).
{ intros a Ha. destruct Hst as [Hb _]. specialize (Hb (Z.to_nat (a - p)) ltac:(rewrite length_app; cbn [length]; lia)).
  rewrite Z2Nat.id in Hb by lia. replace (p + (a - p)) with a in Hb by lia. rewrite Hb. discriminate. }
destruct (al_blocks SEGS B LAWS ly S W mem md q k HAR Hin) as (_ & Hq4096 & Hqc & _ & _ & _ & Hk).
pose proof (req_size_pos k ltac:(lia)) as [_ Hrk]. unfold MALLOC_MAX in Hk.
split.
- split; [lia|]. split; [lia|]. split; [lia|]. split; [exact Hvis|].
  split; [apply (amem_range_of_block SEGS B LAWS ly S W mem md q k); [exact HAR | exact Hin | lia | lia]|].
  split; [apply (range_addressable_of_block SEGS B LAWS ly S W mem md q k); [exact HAR | exact Hin | lia | lia]|].
  intros Hn0. apply (shadow_hull_vis_of_block SEGS B LAWS ly S W mem md q k); [exact HAR | exact Hin | lia | lia | lia].
- apply (amem8_of_blockA SEGS B LAWS ly S W mem md p (astr_len s) HAR); [|unfold astr_len; lia].
  exists q, k. unfold astr_len. split; [exact Hin|]. split; lia.
Qed.

(* the runtime entries' read-only premise is the in-segment half of arodata_okP *)
Lemma ca_rom_of_aro : forall rlo rhi W mem, arodata_okP SEGS rlo rhi B (rdW W mem) -> rt_rom_view SEGS B W mem.
Proof. intros rlo rhi W mem H a Hr Ho He. exact (H a (or_introl Hr) Ho He). Qed.

Definition ca_post (W : world SEGS) (mem : word -> option byte) (regs : bvmap 5 word) (ly : alayout) (S : astate) :=
fun (ly' : alayout) (S' : astate) (W' : world SEGS) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) =>
sa_kept SEGS W mem W' mem' regs CA_STK (fun _ => False) /\
Permutation (ablocks B ly' S') (ablocks B ly S) /\ ly' = ly /\ S' = S.

Lemma check_address_core : forall ly S W (regs : bvmap 5 word) mem md ch (got want : Z) (gb wb : list byte),
afn_pre SEGS B CA_STK ly S W regs mem md ch ->
getr regs 10 = w64 got -> getr regs 11 = w64 want ->
astr_at SEGS W mem got gb -> ca_rdf W mem got (Z.of_nat (length gb) + 1) -> amem_range got (astr_len gb + 8) ->
atail_vis SEGS W mem (got + Z.of_nat (length gb)) ->
astr_at SEGS W mem want wb -> ca_rdf W mem want (Z.of_nat (length wb) + 1) -> amem_range want (astr_len wb + 8) ->
atail_vis SEGS W mem (want + Z.of_nat (length wb)) ->
rt_rom_view SEGS B W mem ->
StrFun.strncmp_model (gb ++ [Z_to_bv 8 0]) (wb ++ [Z_to_bv 8 0]) (Z.of_nat (length wb)) = Some 0 ->
SRr SEGS W (cfg_at SEGS (BASE + AF_check_address) regs mem md)
(apost_base SEGS B CA_STK [] regs ly S W mem md 0 (ca_post W mem regs ly S)).
Proof.
intros ly S W regs mem md ch got want gb wb HPRE H10 H11 STg RDg AMg TLg STw RDw AMw TLw ROMV CMP.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & _ & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (HSTK : CA_STK = 8224) by reflexivity. assert (HE4 : ESTACK = 4096) by reflexivity.
set (sp0 := spZ regs) in *.
pose proof RDg as (Hg0 & Hgn & Hgc & _). pose proof RDw as (Hw0 & Hwn & Hwc & _).
(* the entry state *)
remember (Eimg (Ereg regs [])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs []) E) by (rewrite HE; split; [intros kk Hkk; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r).
{ intros n r Hn. subst E. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
assert (Usp : bv_unsigned (ew E 2) = sp0) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
assert (HS : st_ok_pi SEGS VAL E ss_ca0 (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_check_address)) mem (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_ca0. apply pa_entry_st_ok_full.
  - rewrite HE. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - unfold stack_region. apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
  - cbn. tauto.
  - split; [exact I | split; exact I]. }
clear HE.
pose proof (ajournal_init SEGS B CA_STK [] ly S W regs mem md ch HPRE) as HJ.
unfold cfg_at. change (w64 (BASE + AF_check_address)) with (Z_to_bv 64 (BASE + AF_check_address)).
(* 0x8746c .. 0x87484: the frame, ra s0 s1 saved, s0 = want, s1 = got, a0 = want *)
paj_run_shc RUNP RUNC HS HJ.
{ awr_ok_tac. exact Usp. }
ca_kw_run HFr Usp (ca_kw_refl W mem) KWa.
ca_kin_run HFr Usp (ca_kwin_refl W (sp0 - CA_STK) sp0 mem) KIa (sp0 - CA_STK) sp0. clear HF HFr HG.
(* 0x87488: strlen(want) *)
lazymatch type of HS with st_ok _ _ ?ssx (restrict _ ?msA) =>
prreg HS (10%bv : bv 5) R10; prreg HS (2%bv : bv 5) R2;
prreg HS (1%bv : bv 5) R1; prreg HS (3%bv : bv 5) R3; prreg HS (4%bv : bv 5) R4;
assert (Hsp1 : spZ (ms_regs msA) = sp0 - 32) by (unfold spZ; rewrite R2, Usp; apply unsigned_lit_small; lia);
pose proof (ecall_pre_stk_at SEGS B ESTACK CA_STK sp0 [] ly S W mem md [] ly S W (ms_mem msA) _ 0 (ms_regs msA) (-32) HJ
ltac:(rewrite Hsp1; lia) eq_refl ltac:(lia) ltac:(lia) ltac:(lia) ltac:(rewrite R1; apply ret_ok_codeptr_v; [lia | reflexivity])
ltac:(rewrite R3, (EE 3%nat 3%bv eq_refl); exact Hgp) ltac:(rewrite R4, (EE 4%nat 4%bv eq_refl); exact Htp)) as HPRE1;
pmkst HS;
eapply SRr_bind;
[ eapply (ART ESTACK (fun _ => False) _ W (ms_regs msA) (ms_mem msA) CA_STK sp0 [] ly S W mem md [] ly S _ 0 (-32) _
(fun regs' _ => getr regs' 10 = w64 (astr_len wb)) HJ);
[ rewrite Hsp1; lia | reflexivity | lia | lia | lia | exact R1 | intros a [] | ]
| ] end.
{ cbn [ss_pc setpc].
apply (STRLEN fx ly S W _ _ _ want wb).
- exact HPRE1.
- rewrite R10, (EE 11%nat 11%bv eq_refl). exact H11.
- lia.
- apply (ca_astr_at_kw W mem _ want wb STw); [lia | lia | exact KWa].
- apply ca_rdf_aread; [exact (ca_rdf_kw _ _ _ _ _ RDw KWa) | lia].
- apply (ca_atail_vis_kw W mem _ _ TLw); [lia | exact KWa].
- exact (ca_rom_kw B W mem _ ROMV KWa). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & HQ2 & HFR2').
pose proof (fun a Ha Hn => HFR2' a Ha Hn (fun x : False => x)) as HFR2. clear HFR2'.
pose proof (ca_kw_trans _ _ _ _ KWa (ca_kw_of_win _ _ _ (sp0 + -32 - ESTACK) (sp0 + -32) ltac:(lia) HFR2)) as KWb.
pose proof (ca_kwin_trans _ _ _ _ _ _ KIa (ca_kwin_sub W (sp0 - CA_STK) sp0 _ _ _ _ HFR2 ltac:(lia) ltac:(lia))) as KIb.
ca_after HS 1024%nat W regs2 mem2 HP2 HFR2 HJ2 Usp HS2. clear HS HP2 HFR2 HPRE1 KWa KIa R10 R2 R3 R4 R1 Hsp1.
remember (havoc E 1024 (map (getr regs2) CLOB)) as E1 eqn:HE1 in HS2.
assert (HEI1 : img_env VAL A_LIM E1) by (rewrite HE1; apply img_env_havoc_hi; [exact HEI | cbv; lia]).
assert (HAE1 : env_agree 32 (Ereg regs []) E1) by (rewrite HE1; apply env_agree_havoc_ge; [cbv; lia | exact HAE]).
assert (EO1 : forall n, (n < 1024)%nat -> ew E1 n = ew E n) by (intros n Hn; rewrite HE1; apply ew_havoc_old; exact Hn).
assert (A1 : ew E1 1028 = w64 (astr_len wb)).
{ rewrite HE1. change 1028%nat with (1024 + 4)%nat. rewrite (ew_havoc_new E 1024 _ 4 (Z_to_bv 64 0)) by (cbn; lia).
  unfold CLOB. cbn [map nth]. exact HQ2. }
assert (Usp1 : bv_unsigned (ew E1 2) = sp0) by (rewrite EO1 by lia; exact Usp).
clear HE1.
(* 0x8748c .. 0x87494: a2 = n, a0 = got, a1 = want *)
paj_run_shc RUNP RUNC HS2 HJ2.
{ awr_ok_tac. exact Usp1. }
ca_kw_run HFr Usp1 KWb KWc.
ca_kin_run HFr Usp1 KIb KIc (sp0 - CA_STK) sp0. clear HF HFr HG.
set (n1 := Z.of_nat (length wb)) in *.
(* 0x87498: strncmp(got, want, n) *)
lazymatch type of HS2 with st_ok _ _ ?ssx (restrict _ ?msB) =>
prreg HS2 (10%bv : bv 5) R10; prreg HS2 (11%bv : bv 5) R11; prreg HS2 (12%bv : bv 5) Ra2; prreg HS2 (2%bv : bv 5) R2;
prreg HS2 (1%bv : bv 5) R1; prreg HS2 (3%bv : bv 5) R3; prreg HS2 (4%bv : bv 5) R4;
assert (Hsp1 : spZ (ms_regs msB) = sp0 - 32) by (unfold spZ; rewrite R2, Usp1; apply unsigned_lit_small; lia);
pose proof (ecall_pre_stk_at SEGS B (2 * ESTACK) CA_STK sp0 [] ly S W mem md [] ly S W (ms_mem msB) _ 0 (ms_regs msB) (-32) HJ2
ltac:(rewrite Hsp1; lia) eq_refl ltac:(lia) ltac:(lia) ltac:(lia) ltac:(rewrite R1; apply ret_ok_codeptr_v; [lia | reflexivity])
ltac:(rewrite R3, EO1, (EE 3%nat 3%bv eq_refl) by lia; exact Hgp)
ltac:(rewrite R4, EO1, (EE 4%nat 4%bv eq_refl) by lia; exact Htp)) as HPRE1;
pmkst HS2;
eapply SRr_bind;
[ eapply (ART (2 * ESTACK) (fun _ => False) _ W (ms_regs msB) (ms_mem msB) CA_STK sp0 [] ly S W mem md [] ly S _ 0 (-32) _
(fun regs' _ => getr regs' 10 = w64 0 <->
StrFun.strncmp_model (gb ++ [Z_to_bv 8 0]) (wb ++ [Z_to_bv 8 0]) n1 = Some 0) HJ2);
[ rewrite Hsp1; lia | reflexivity | lia | lia | lia | exact R1 | intros a [] | ]
| ] end.
{ cbn [ss_pc setpc].
apply (STRNCMP fx ly S W _ _ _ got want n1 gb wb).
- exact HPRE1.
- rewrite R10, EO1, (EE 10%nat 10%bv eq_refl) by lia. exact H10.
- rewrite R11, EO1, (EE 11%nat 11%bv eq_refl) by lia. exact H11.
- rewrite Ra2. exact A1.
- unfold n1. lia. - lia. - lia.
- apply (ca_astr_at_kw W mem _ got gb STg); [lia | lia | exact KWc].
- apply (ca_astr_at_kw W mem _ want wb STw); [lia | lia | exact KWc].
- apply ca_rdf_aread; [| lia]. apply (ca_rdf_sub _ _ _ (Z.of_nat (length gb) + 1)); [exact (ca_rdf_kw _ _ _ _ _ RDg KWc) | unfold astr_len, n1; lia].
- exact AMg.
- apply ca_rdf_aread; [| lia]. apply (ca_rdf_sub _ _ _ (Z.of_nat (length wb) + 1)); [exact (ca_rdf_kw _ _ _ _ _ RDw KWc) | unfold astr_len, n1; lia].
- exact AMw.
- apply (ca_atail_vis_kw W mem _ _ TLg); [lia | exact KWc].
- apply (ca_atail_vis_kw W mem _ _ TLw); [lia | exact KWc].
- exact (ca_rom_kw B W mem _ ROMV KWc). }
cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & HQ3 & HFR3').
pose proof (fun a Ha Hn => HFR3' a Ha Hn (fun x : False => x)) as HFR3. clear HFR3'.
pose proof (ca_kwin_trans _ _ _ _ _ _ KIc (ca_kwin_sub W (sp0 - CA_STK) sp0 _ _ _ _ HFR3 ltac:(lia) ltac:(lia))) as KId.
ca_after HS2 1040%nat W regs3 mem3 HP3 HFR3 HJ3 Usp1 HS3. clear HS2 HP3 HFR3 HPRE1 KWb KWc KIc R10 R11 Ra2 R2 R3 R4 R1 Hsp1.
remember (havoc E1 1040 (map (getr regs3) CLOB)) as E2 eqn:HE2 in HS3.
assert (HEI2 : img_env VAL A_LIM E2) by (rewrite HE2; apply img_env_havoc_hi; [exact HEI1 | cbv; lia]).
assert (HAE2 : env_agree 32 (Ereg regs []) E2) by (rewrite HE2; apply env_agree_havoc_ge; [cbv; lia | exact HAE1]).
assert (EO2 : forall n, (n < 1040)%nat -> ew E2 n = ew E1 n) by (intros n Hn; rewrite HE2; apply ew_havoc_old; exact Hn).
assert (A2 : ew E2 1044 = getr regs3 10).
{ rewrite HE2. change 1044%nat with (1040 + 4)%nat. rewrite (ew_havoc_new E1 1040 _ 4 (Z_to_bv 64 0)) by (cbn; lia).
  unfold CLOB. cbn [map nth]. reflexivity. }
assert (Usp2 : bv_unsigned (ew E2 2) = sp0) by (rewrite EO2 by lia; exact Usp1).
clear HE2.
(* strncmp returned 0: the model premise *)
assert (Hz : getr regs3 10 = w64 0) by (apply HQ3; exact CMP).
(* 0x8749c: bnez a0, 0x874b4 *)
psrr_branch_pi RUNP BR HS3.
- (* the arm to the no-return hook (0x874b4) and abort (0x874b8), with the trap `unimp` 0x874bc after it: a0 = 0,
     so not taken *)
  exfalso. rewrite branch_ne_U in Hc. apply negb_true_iff in Hc. apply Z.eqb_neq in Hc. apply Hc.
  unfold U. cbn [sv_denot]. rewrite A2, Hz. vm_compute. reflexivity.
- (* 0x874a0 .. 0x874b0: ra s0 s1 reloaded, the frame freed, ret *)
  paj_run_sh RUNP HS3 HJ3.
  { awr_ok_tac. exact Usp2. }
  ca_kin_run HFr Usp2 KId KIe (sp0 - CA_STK) sp0. clear HF HFr HG.
  prreg HS3 (1%bv : bv 5) Q1.
  eapply (RET W _ _ _ _ _ HS3 eq_refl ltac:(vm_compute; reflexivity)).
  intros mat'. unfold apost_base.
  lazymatch goal with |- exists _ _ _ _ _, mkCfg (mkst ?rg _ ?m _) ?d = _ /\ _ => exists ly, S, rg, m, d end.
  split; [cbn [ms_regs]; rewrite Q1, EO2, EO1, (EE 1%nat 1%bv eq_refl), Hra by lia; reflexivity|].
  split; [cbn [ms_mem]; apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ3|].
  split; [eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs [] HS3); [exact HAE2 | vm_compute; reflexivity]|].
  unfold ca_post. split; [|split; [apply Permutation_refl | split; reflexivity]].
  intros a Ha Hw _. exact (KIe a Ha Hw).
Qed.

(* a string argument as the contract states it (a SegModel text with its tail, in a live heap block), as the facts
   the core lemma takes of its byte list *)
Lemma ca_arg : forall ly S W mem md p s,
AR SEGS B ly S W mem md ->
sa_heap B ly S p (Z.of_nat (length s) + 1) -> sa_str (rdW W mem) p s ->
astr_at SEGS W mem p (seg_spec.zb s) /\ ca_rdf W mem p (Z.of_nat (length (seg_spec.zb s)) + 1) /\
amem_range p (astr_len (seg_spec.zb s) + 8) /\ atail_vis SEGS W mem (p + Z.of_nat (length (seg_spec.zb s))) /\
Forall (fun z => 0 <= z < 256) s /\ ~ In 0 s.
Proof.
intros ly S W mem md p s HAR HH [HZ HT].
destruct (ca_strz_bytes SEGS (w_H W) mem p s HZ) as (HB & HN & HE & HL).
assert (HST : astr_at SEGS W mem p (seg_spec.zb s)) by (split; [exact HB | exact HN]).
rewrite <- HL in HH.
destruct (ca_heap_str ly S W mem md p _ HAR HH HST) as [HR HA].
split; [exact HST|]. split; [exact HR|]. split; [exact HA|].
split; [rewrite HL; exact HT|].
destruct HZ as [HZ HN0].
pose proof (ca_zs_range SEGS (w_H W) mem p _ HZ) as R. apply Forall_app in R as [R _].
split; [exact R | exact HN0].
Qed.

Lemma ca_noalloc : forall ly S, sa_noalloc B ly S ly S.
Proof. intros ly S. split; [apply Permutation_refl|]. split; [reflexivity|]. exists (st_fs S). destruct S; reflexivity. Qed.

Theorem check_address_walk :
  check_address_contract SEGS B (BASE + AF_check_address) SegInstB.STK_check_address SegInstB.RLO_A SegInstB.RHI_A.
Proof.
intros ly S W regs mem md ch got want gs ws HPRE HROD H10 _ H11 _
  (G0 & SG & LG & HG & _ & _ & W0 & SW & LW & HW & _ & _ & CMP) _.
pose proof HPRE as (HAR & _).
destruct (ca_arg ly S W mem md got gs HAR HG SG) as (STg & RDg & AMg & TLg & Rg & Ng).
destruct (ca_arg ly S W mem md want ws HAR HW SW) as (STw & RDw & AMw & TLw & Rw & Nw).
eapply SRr_mono.
- exact (check_address_core ly S W regs mem md ch got want (seg_spec.zb gs) (seg_spec.zb ws) HPRE H10 H11
    STg RDg AMg TLg STw RDw AMw TLw (ca_rom_of_aro _ _ W mem HROD) (ca_cmp_zero gs ws Rg Rw Ng Nw CMP)).
- cbv beta. unfold apost_base. intros W' c' _ (ly' & S' & regs' & mem' & md' & Hc & HJ' & HP' & (Hkept & Hperm & -> & ->)).
  exists ly, S, regs', mem', md'. split; [exact Hc|]. split; [exact HJ'|]. split; [exact HP'|].
  split; [exact Hkept | apply ca_noalloc].
Qed.

End e.
End f.
End d.
