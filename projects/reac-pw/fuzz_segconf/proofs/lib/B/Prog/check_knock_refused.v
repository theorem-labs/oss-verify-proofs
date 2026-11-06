(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8h.v:104-108;
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACbk.v:76-79; projects/cgif/cgif_file_fuzzer/proofs/lib/A/AChd.v:200-203, 358-361,
   386-392, 532-535, for libreac/fuzz_identity's ASan build (lib/A). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/reac_box_family_stem.v, with its module paths and module names changed; 95 of its 123 lines of code are new or changed and 244 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/fuzz_catalogue_rowA.v, with its module paths and module names changed; 331 of its 372 lines of code are new or changed and 82 lines of the source are left out. *)
(* The image-B port of lib/A/Prog/check_knock_refused.v (commit 38b2a0dc4f6b): the walk of
   check_knock_refused on reac-pw/fuzz_segconf's ASan+UBSan build, image B (fuzz_segconf.asan-ubsan, 0x874c0, 52 bytes,
   13 instructions), against check_knock_refused_contract (image B's copy lib/B/Prog/check_knock_refused_c.v of the
   FINAL contract text). RELOCATION: B's words are A's up to the pc-relative offsets of the auipc/addi pair (a1 = 0x21300 in
   both images) and of the three jal, plus one UBSan trap word `unimp` at 0x874f0 after `jal abort`. The listing
   slots are the same position-abstract terms in both images (lib/B/Prog/SegList.v), so the A walk runs here with
   image B's module paths and image B's numbers.

   The symbolic executor runs the prologue to the branch on a1 (0x874c8); the arm a1 = 0 runs the epilogue to the
   `ret`; the arm a1 <> 0 runs to the wrapper call (0x874d4), the call applies the strstr wrapper's contract
   (Section hypothesis STRSTR, image B's lib/B/Rt/RtSeg.v row 8) through aj_art_at, the state after the call is
   rebuilt with jafter_call_keep_hi, the branch on the wrapper's answer (0x874d8) is split with paj_branch, and the
   path that returns ends at the `ret` with paj_ret_at.

   The arm to the no-return hook and abort (0x874e8 `jal before_abort`, 0x874ec `jal abort`) is the branch at
   0x874d8, taken when the answer is 0. On that path k = true, so the contract's premise
   (negb k || strstr_found gs TNP) = true gives an occurrence of the needle in the NUL-free haystack
   (check_knock_refused_lem.v, ckr_found_occ); the wrapper's post then says the answer is got + j, not 0, so the
   branch is not taken. The UBSan trap word at 0x874f0 is the target of no branch and follows only `jal abort`, so
   no path reaches it once the abort arm is refuted.

   Image B's numbers are image B's instance file's (lib/B/Prog/SegInstB.v): SegInstB.STK_check_knock_refused (the
   16-byte frame and the wrapper's window 2 * ESTACK), the read-only window SegInstB.RLO_A / RHI_A (SegGlob.SEG_RLO /
   SEG_RHI, image B's .data.rel.ro start and .got end), SegInstB.gotwA / guardA (the .got word twoway_strstr loads,
   and __stack_chk_guard). The walk is stated for every literal map with lit TNP = SegInstB.seg_litA_fz TNP (0x21300,
   .str.23, the address `auipc a1; addi a1,a1,-460` forms: the listing's object A_OBJ 26, by seg_val_objs). The entry
   and the call target stay listing terms: BASE + AF_check_knock_refused and SIGMA SS___interceptor_trampoline_strstr. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase SegObj SegAddr.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require SegGlob SegInstB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require RtSeg.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import check_knock_refused_lem check_knock_refused_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* the symbolic state at the entry: the registers as atoms, the 16-byte frame below sp writable *)
Definition ss_ckr0 : sstate := mkSS AF_check_knock_refused sr_atoms [stack_region 16] None (mkFacts [] [] []).

(* image B's numbers of the contract's parameters, SegInstB's, under the names the proofs below use *)
(* the stack below the entry sp: the 16-byte frame (`addi sp,sp,-16` 0x874c0) and the strstr row's window 2 * ESTACK
   (8,208) *)
#[local] Notation STK_check_knock_refused_B := SegInstB.STK_check_knock_refused (only parsing).
(* the stack-protector cells the strstr row reads: the .got word 0xa3e98, which holds 0x5ff838 in the pin and which
   twoway_strstr (0x9b99c) loads at 0x9b9e0 / 0x9b9e4, and __stack_chk_guard (twin .symtab 0x5ff838, 8 bytes) *)
#[local] Notation gotwB := SegInstB.gotwA (only parsing).
#[local] Notation guardB := SegInstB.guardA (only parsing).

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ seg_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* memory below the allocation ceiling unchanged: every write of check_knock_refused and of the wrapper it calls
   lands in the real stack, which is above it (fuzz_command's verb_is.v kw) *)
Definition kw (W : world SEGS) (m m' : word -> option byte) : Prop :=
forall a, 0 <= a < alloc_ceiling -> aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a.
Lemma kw_refl : forall W m, kw W m m.
Proof using. intros W m a _. reflexivity. Qed.
Lemma kw_trans : forall W m1 m2 m3, kw W m1 m2 -> kw W m2 m3 -> kw W m1 m3.
Proof using. intros W m1 m2 m3 K1 K2 a Ha. rewrite (K2 a Ha). exact (K1 a Ha). Qed.
Lemma kw_of_win : forall W m m' lo hi, alloc_ceiling <= lo ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a) -> kw W m m'.
Proof using. intros W m m' lo hi Hlo H a Ha. pose proof asan_consts as (C1 & _). apply H; lia. Qed.
(* memory outside a window [lo, hi) unchanged: the call's own stack window, for the contract's sa_kept *)
Definition kp (W : world SEGS) (lo hi : Z) (m m' : word -> option byte) : Prop :=
forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a.
Lemma kp_refl : forall W lo hi m, kp W lo hi m m.
Proof using. intros W lo hi m a _ _. reflexivity. Qed.
Lemma kp_trans : forall W lo hi m1 m2 m3, kp W lo hi m1 m2 -> kp W lo hi m2 m3 -> kp W lo hi m1 m3.
Proof using. intros W lo hi m1 m2 m3 K1 K2 a Ha Hn. rewrite (K2 a Ha Hn). exact (K1 a Ha Hn). Qed.
Lemma kp_sub : forall W lo hi lo' hi' m m', lo <= lo' -> hi' <= hi -> kp W lo' hi' m m' -> kp W lo hi m m'.
Proof using. intros W lo hi lo' hi' m m' H1 H2 K a Ha Hn. apply K; [exact Ha | lia]. Qed.
Lemma abytes_at_kw : forall W m m' x l, abytes_at SEGS W m x l -> 0 <= x ->
x + Z.of_nat (length l) <= alloc_ceiling -> kw W m m' -> abytes_at SEGS W m' x l.
Proof using. intros W m m' x l H Hx Hl K i Hi. rewrite K by lia. exact (H i Hi). Qed.
Lemma astr_at_kw : forall W m m' x s, astr_at SEGS W m x s -> 0 <= x ->
x + Z.of_nat (length s) + 1 <= alloc_ceiling -> kw W m m' -> astr_at SEGS W m' x s.
Proof using.
intros W m m' x s [H1 H2] Hx Hl K. split; [|exact H2].
apply (abytes_at_kw W m m' x _ H1 Hx); [rewrite length_app; cbn [length]; lia | exact K].
Qed.
Lemma atail_vis_kw : forall W m m' e, atail_vis SEGS W m e -> 0 <= e < alloc_ceiling -> kw W m m' -> atail_vis SEGS W m' e.
Proof using.
intros W m m' e H He K a Ha. pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as CR. pose proof (proj2 (@YG0f.ASAN_CEIL_range _)) as CM.
unfold YG0f.ASAN_CEIL in CR, CM.
pose proof (Z.div_mod e 8 ltac:(lia)) as D. pose proof (Z.mod_pos_bound e 8 ltac:(lia)) as M.
pose proof (Z.div_mod alloc_ceiling 4096 ltac:(lia)) as D2.
rewrite K by lia. exact (H a Ha).
Qed.
Lemma aguard_ok_kw : forall W m m' g gd, aguard_ok SEGS W m g gd -> 0 <= g -> g + 8 <= alloc_ceiling ->
0 <= gd -> gd + 8 <= alloc_ceiling -> kw W m m' -> aguard_ok SEGS W m' g gd.
Proof using.
intros W m m' g gd [H1 (c & H2)] Hg1 Hg2 Hd1 Hd2 K. split.
- rewrite (rdword_ext (aview SEGS (w_H W) m) (aview SEGS (w_H W) m') g); [exact H1|]. intros k Hk. apply K. lia.
- exists c. rewrite (rdword_ext (aview SEGS (w_H W) m) (aview SEGS (w_H W) m') gd); [exact H2|]. intros k Hk. apply K. lia.
Qed.
Lemma rt_rom_view_kw : forall B W m m', rt_rom_view SEGS B W m -> kw W m m' -> rt_rom_view SEGS B W m'.
Proof using.
intros B W m m' H K a Hr Ho He. pose proof asan_consts as (C1 & _).
assert (Hi : in_img SEGS a) by (destruct Hr as (sg & Hs & _ & Hsr); exists sg; split; [exact Hs | exact Hsr]).
pose proof (pa_img_range _ Hi) as R. unfold kImgEnd in R.
rewrite K by lia. exact (H a Hr Ho He).
Qed.

(* the range facts a wrapper checks, below the allocation ceiling (RtDefs.v's aread_ok without its window part) *)
Definition rdf (W : world SEGS) (m : word -> option byte) (x n : Z) : Prop :=
0 < x /\ 0 <= n < 2 ^ 32 /\ x + n <= alloc_ceiling /\
(forall a, x <= a < x + n -> aview SEGS (w_H W) m a <> None) /\ amem_range x n /\
range_addressable (aview SEGS (w_H W) m) SHADOW_OFF x n /\ (0 < n -> shadow_hull_vis (aview SEGS (w_H W) m) x n).
Lemma rdf_kw : forall W m m' x n, rdf W m x n -> kw W m m' -> rdf W m' x n.
Proof using.
intros W m m' x n (Hx & Hn & Hc & Hv & Ham & Hra & Hh) K. pose proof asan_consts as (C1 & C2 & _).
assert (HK : forall s, 0 <= s < 2 ^ 64 -> ~ (alloc_ceiling <= s < 2 ^ 64) -> aview SEGS (w_H W) m' s = aview SEGS (w_H W) m s)
by (intros s Hs Hns; apply K; lia).
split; [exact Hx|]. split; [exact Hn|]. split; [exact Hc|].
split; [intros a Ha; rewrite K by lia; apply Hv; exact Ha|]. split; [exact Ham|].
split; [exact (range_addressable_kept_win _ _ alloc_ceiling (2 ^ 64) x n HK ltac:(lia) ltac:(lia) ltac:(lia) Hra)|].
intros Hn0. exact (shadow_hull_vis_kept_win _ _ alloc_ceiling (2 ^ 64) x n HK ltac:(lia) ltac:(lia) ltac:(lia) Hn0 (Hh Hn0)).
Qed.
Lemma rdf_aread : forall W m (regs : bvmap 5 word) stk x n, rdf W m x n -> alloc_ceiling <= spZ regs - stk ->
aread_ok SEGS stk W regs m x n.
Proof using.
intros W m regs stk x n (Hx & Hn & Hc & Hv & Ham & Hra & Hh) Hs. pose proof asan_consts as (C1 & _).
unfold aread_ok. split; [lia|]. split; [lia|]. split; [lia|].
split; [intros a Ha; split; [apply Hv; lia | unfold ascratch_stk; lia]|].
split; [exact Ham|]. split; [exact Hra | exact Hh].
Qed.
(* the contract's string facts give the range facts: the bytes and NUL are mapped (sa_strz), the shadow part is
   sa_addr *)
Lemma rdf_of_sa : forall W mem x s, sa_strz (rdW W mem) x s -> sa_addr (rdW W mem) x (Z.of_nat (length s) + 1) ->
0 < x -> Z.of_nat (length s) + 1 < 2 ^ 32 -> x + Z.of_nat (length s) + 1 <= alloc_ceiling ->
rdf W mem x (Z.of_nat (length s) + 1).
Proof using.
intros W mem x s [HZ _] (_ & _ & Ham & Hra & Hh) Hx Hn Hc.
split; [exact Hx|]. split; [lia|]. split; [lia|]. split; [|split; [exact Ham | split; [exact Hra | exact Hh]]].
intros a Ha. assert (Hi : (Z.to_nat (a - x) < length (s ++ [0%Z]))%nat) by (rewrite length_app; cbn [length]; lia).
pose proof (HZ _ Hi) as Hv. rewrite Z2Nat.id in Hv by lia. replace (x + (a - x)) with a in Hv by lia.
rewrite Hv. discriminate.
Qed.

Lemma region_kept_win : forall E n lo hi wlo whi cs sp H (m m' : word -> option byte) wl wh,
bv_unsigned (ew E n) = sp ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (wl <= a < wh) -> aview SEGS H m' a = aview SEGS H m a) ->
wh <= sp + lo -> 0 <= sp + lo -> sp + hi <= 2 ^ 64 ->
(forall a, sp + wlo <= a < sp + whi -> apresent H m' a) ->
region_kept SEGS E (mrestrict H m) (mrestrict H m') (YP09.mkRegion (Some n) lo hi wlo whi cs).
Proof using.
intros E n lo hi wlo whi cs sp H m m' wl wh Hn Hfr Hwh H0 H64 Hp.
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Hn; intros a Ha.
- apply (mbyte_of_aview SEGS). apply Hfr; lia.
- intros _. apply (apresent_writable SEGS). apply Hp. lia.
Qed.

(* the runtime entries' ROM premise is the in-segment half of arodata_okP *)
Lemma rom_view_of_aro : forall B rlo rhi W mem, arodata_okP SEGS rlo rhi B (rdW W mem) -> rt_rom_view SEGS B W mem.
Proof using. intros B rlo rhi W mem H a Hr Ho He. exact (H a (or_introl Hr) Ho He). Qed.

(* the memory a run leaves: it writes only the frame [sp0 - 16, sp0), inside the call's window [lo, hi) *)
Ltac ckr_kp_run HFr Uspx lo hi KP0 KPn :=
lazymatch type of HFr with frame_of ?Ex ?rsx (mrestrict ?Hx ?m0) (mrestrict _ ?m1) =>
let KR := fresh "KR" in
assert (KR : forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> aview SEGS Hx m1 a = aview SEGS Hx m0 a)
by (apply (kept_of_frame (segs := SEGS) Ex rsx Hx m0 m1 (fun x => lo <= x < hi) HFr);
let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let x := fresh "x" in
let Hin := fresh "Hin" in let Hrr := fresh "Hrr" in let Hq := fresh "Hq" in
intros b wlo whi x Hin Hrr; vm_compute in Hin; destruct Hin as [Hq | []]; injection Hq as <- <- <-;
cbn [base_val] in Hrr; rewrite Uspx in Hrr; split; lia);
pose proof (kp_trans _ _ _ _ _ _ KP0 KR) as KPn; clear KR
end.

(* the state after the wrapper call: st_ok_pi rebuilt over a fresh band of atoms for the clobbered registers, the
   frame (and so the stored ra) kept *)
Ltac ckr_after HS K W regs2 mem2 HP2 HFR2 HJ2 Uspx HS2 :=
jafter_call_keep_hi HS K regs2 (mrestrict (w_H W) mem2) HP2 [0%nat] HS2;
let HRK := fresh "HRK" in
match type of HS2 with ?P -> _ => assert (HRK : P) end;
[ cbn [ms_mem restrict]; constructor; [|constructor];
eapply region_kept_win; [exact Uspx | exact HFR2 | lia | lia | lia |];
let a := fresh "a" in let Ha := fresh "Ha" in let Hp := fresh "Hp" in
intros a Ha; pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hp & _); apply Hp; lia
| specialize (HS2 HRK); clear HRK; rewrite <- restrict_mkst_fx in HS2 ].

Section e.
Variable B : asyms.
(* the wrapper it calls: the strstr interceptor's contract at the listing's call target (row 8, image B's copy
   lib/B/Rt/RtSeg.v astrstr_realizes, with image A's theorem name; the contract file's head names it) *)
Hypothesis STRSTR : forall fx0 : YK11.FPState,
  @RtSeg.astrstr_realizes fx0 rc SEGS B (SIGMA SS___interceptor_trampoline_strstr) SegInstB.gotwA SegInstB.guardA.
(* the walk's record hypothesis (fuzz_command's verb_is.v takes the same): the runtime library's facts, of which
   aj_art_at uses the errno cell's placement (pal_env) *)
Hypothesis TL : PALib B.
(* the listing's objects at the image's addresses (the image instance gives it): a1's value at 0x874d0 *)
Hypothesis HVO : seg_val_objs.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUNP := SRr_run_pi_AJ B LAWS.
Let RUNC := SRr_run_pi_AJ_call B LAWS.
Let BR := paj_branch (L := seg_listing) (PI := PI).
Let RET := paj_ret_at (L := seg_listing) (PI := PI).
Let ART := aj_art_at SEGS B LAWS pa_segs_low (pal_env B TL).

(* a range inside a live heap block lies below the allocation ceiling *)
Lemma heap_below : forall ly S W mem md q n, AR SEGS B ly S W mem md -> sa_heap B ly S q n -> 0 < n ->
4096 <= q /\ q + n <= alloc_ceiling.
Proof using.
intros ly S W mem md q n HAR (p & k & Hin & H1 & H2) Hn.
destruct (al_blocks SEGS B LAWS ly S W mem md p k HAR Hin) as (_ & Hp4096 & Hpc & _).
pose proof (req_size_pos k ltac:(lia)) as [_ Hrk]. lia.
Qed.

(* the walk, from the facts the contract's premises give; the needle's address is the listing's object atom
   A_OBJ 26 *)
Lemma ckr_core : forall ly S W (regs : bvmap 5 word) mem md ch (got : Z) (k : bool) (hb nb : list byte),
afn_pre SEGS B STK_check_knock_refused_B ly S W regs mem md ch ->
getr regs 10 = w64 got -> getr regs 11 = w64 (seg_spec.b2z k) ->
astr_at SEGS W mem got hb -> rdf W mem got (Z.of_nat (length hb) + 1) -> amem_range got (Z.of_nat (length hb) + 8) ->
atail_vis SEGS W mem (got + Z.of_nat (length hb)) ->
astr_at SEGS W mem (VAL (A_OBJ 26)) nb -> rdf W mem (VAL (A_OBJ 26)) (Z.of_nat (length nb) + 1) ->
amem_range (VAL (A_OBJ 26)) (Z.of_nat (length nb) + 8) ->
atail_vis SEGS W mem (VAL (A_OBJ 26) + Z.of_nat (length nb)) ->
rt_rom_view SEGS B W mem -> aguard_ok SEGS W mem gotwB guardB ->
(k = true -> exists j, (j + length nb <= length hb)%nat /\
  firstn (length nb) (skipn j (map bv_unsigned hb)) = map bv_unsigned nb) ->
SRr SEGS W (cfg_at SEGS (BASE + AF_check_knock_refused) regs mem md)
(apost_base SEGS B STK_check_knock_refused_B [] regs ly S W mem md 0
  (fun ly' S' W' regs' mem' md' =>
   sa_kept SEGS W mem W' mem' regs STK_check_knock_refused_B (fun _ => False) /\ sa_noalloc B ly S ly' S')).
Proof using ART STRSTR.
intros ly S W regs mem md ch got k hb nb HPRE H10 H11 STh RDh AMh TLh STn RDn AMn TLn ROMV HAG KF.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (HSTK : STK_check_knock_refused_B = 8208) by reflexivity. assert (HE4 : ESTACK = 4096) by reflexivity.
assert (HG1 : gotwB = 0xa3e98) by reflexivity. assert (HG2 : guardB = 0x5ff838) by reflexivity.
set (sp0 := spZ regs) in *.
set (y := VAL (A_OBJ 26)) in *.
pose proof RDh as (Hh0 & Hhn & Hhc & _). pose proof RDn as (Hn0 & Hnn & Hnc & _).
(* the symbolic state at the entry *)
remember (Eimg (Ereg regs [])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs []) E) by (rewrite HE; split; [intros kk Hkk; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r).
{ intros n r Hn. subst E. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
assert (Usp : bv_unsigned (ew E 2) = sp0) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
assert (HS : st_ok_pi SEGS VAL E ss_ckr0 (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_check_knock_refused)) mem (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_ckr0. apply pa_entry_st_ok_full.
- rewrite HE. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold stack_region. apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
- cbn. tauto.
- split; [exact I | split; exact I]. }
assert (EOBJ : ew E (A_OBJ 26) = Z_to_bv 64 y)
  by (apply (img_env_atomP E (A_OBJ 26) HEI); unfold A_OBJ, A_TEXT, A_LIM; lia).
clear HE.
pose proof (ajournal_init SEGS B STK_check_knock_refused_B [] ly S W regs mem md ch HPRE) as HJ.
unfold cfg_at. change (w64 (BASE + AF_check_knock_refused)) with (Z_to_bv 64 (BASE + AF_check_knock_refused)).
(* 0x874c0 .. 0x874c8: the frame, ra stored at sp0 - 8, then beqz a1 *)
paj_run_shc RUNP RUNC HS HJ.
{ awr_ok_tac. exact Usp. }
ckr_kp_run HFr Usp (sp0 - STK_check_knock_refused_B) sp0 (kp_refl W (sp0 - STK_check_knock_refused_B) sp0 mem) KPa.
clear HF HFr HG.
assert (E11 : ew E 11 = Z_to_bv 64 (seg_spec.b2z k)) by (rewrite (EE 11%nat 11%bv eq_refl); exact H11).
psrr_branch_pi RUNP BR HS.
- (* a1 = 0: 0x874dc .. 0x874e4, the epilogue and ret *)
  clear Hc. paj_run_sh RUNP HS HJ.
  { awr_ok_tac. exact Usp. }
  ckr_kp_run HFr Usp (sp0 - STK_check_knock_refused_B) sp0 KPa KPe. clear HF HFr HG.
  prreg HS (1%bv : bv 5) Q1.
  eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
  intros mat'. unfold apost_base.
  lazymatch goal with |- exists _ _ _ _ _, mkCfg (mkst ?rg _ ?m _) ?d = _ /\ _ => exists ly, S, rg, m, d end.
  split; [cbn [ms_regs]; rewrite Q1, (EE 1%nat 1%bv eq_refl), Hra; reflexivity|].
  split; [cbn [ms_mem]; apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ|].
  split; [eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs [] HS); [exact HAE | vm_compute; reflexivity]|].
  split; [intros a Ha Hn _; exact (KPe a Ha Hn) |].
  split; [apply Permutation_refl | split; [reflexivity | exists (st_fs S); destruct S; reflexivity]].
- (* a1 <> 0, so k = true: 0x874cc .. 0x874d4, a1 := the needle's address, then the strstr wrapper *)
  assert (Hk : k = true).
  { rewrite branch_eq_U in Hc.
    rewrite (U_atom E 11 (seg_spec.b2z k) E11 ltac:(destruct k; cbn; lia)), U_lit in Hc by lia.
    destruct k; [reflexivity | cbn in Hc; discriminate Hc]. }
  clear Hc. subst k.
  destruct (KF eq_refl) as (j0 & Hj0 & Hocc).
  paj_run_shc RUNP RUNC HS HJ.
  { awr_ok_tac. exact Usp. }
  ckr_kp_run HFr Usp (sp0 - STK_check_knock_refused_B) sp0 KPa KPb. clear HF HFr HG.
  pose proof (kw_of_win W mem _ (sp0 - STK_check_knock_refused_B) sp0 ltac:(lia) KPb) as KWb.
  lazymatch type of HS with st_ok _ _ ?ssx (restrict _ ?msA) =>
  prreg HS (10%bv : bv 5) R10; prreg HS (11%bv : bv 5) R11; prreg HS (2%bv : bv 5) R2;
  prreg HS (1%bv : bv 5) R1; prreg HS (3%bv : bv 5) R3; prreg HS (4%bv : bv 5) R4;
  assert (Hsp1 : spZ (ms_regs msA) = sp0 - 16) by (unfold spZ; rewrite R2, Usp; apply unsigned_lit_small; lia);
  pose proof (ecall_pre_stk_at SEGS B (2 * ESTACK) STK_check_knock_refused_B sp0 [] ly S W mem md [] ly S W (ms_mem msA) _ 0
    (ms_regs msA) (-16) HJ
    ltac:(rewrite Hsp1; lia) eq_refl ltac:(lia) ltac:(lia) ltac:(lia) ltac:(rewrite R1; apply ret_ok_codeptr_v; [lia | reflexivity])
    ltac:(rewrite R3, (EE 3%nat 3%bv eq_refl); exact Hgp) ltac:(rewrite R4, (EE 4%nat 4%bv eq_refl); exact Htp)) as HPRE1;
  pmkst HS;
  eapply SRr_bind;
  [ eapply (ART (2 * ESTACK) (fun _ => False) _ W (ms_regs msA) (ms_mem msA) STK_check_knock_refused_B sp0 [] ly S W mem md
      [] ly S _ 0 (-16) _
      (fun regs' _ => (getr regs' 10 = w64 0 /\ RtSeg.no_occ (map bv_unsigned hb) (map bv_unsigned nb)) \/
         (exists j, RtSeg.first_occ (map bv_unsigned hb) (map bv_unsigned nb) j /\ getr regs' 10 = w64 (got + Z.of_nat j)))
      HJ);
    [ rewrite Hsp1; lia | reflexivity | lia | lia | lia | exact R1 | intros a [] | ]
  | ] end.
  { cbn [ss_pc setpc].
    apply (STRSTR fx ly S W _ _ _ got y hb nb).
    - apply (aguard_ok_kw W mem _ _ _ HAG); [lia | lia | lia | lia | exact KWb].
    - exact HPRE1.
    - rewrite R10, (EE 10%nat 10%bv eq_refl). exact H10.
    - rewrite R11. exact EOBJ.
    - lia. - lia.
    - apply (astr_at_kw W mem _ got hb STh); [lia | lia | exact KWb].
    - apply (astr_at_kw W mem _ y nb STn); [lia | lia | exact KWb].
    - apply rdf_aread; [exact (rdf_kw _ _ _ _ _ RDh KWb) | lia].
    - exact AMh.
    - apply rdf_aread; [exact (rdf_kw _ _ _ _ _ RDn KWb) | lia].
    - exact AMn.
    - apply (atail_vis_kw W mem _ _ TLh); [lia | exact KWb].
    - apply (atail_vis_kw W mem _ _ TLn); [lia | exact KWb].
    - exact (rt_rom_view_kw B W mem _ ROMV KWb). }
  cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & HQ2 & HFR2').
  pose proof (fun a Ha Hn => HFR2' a Ha Hn (fun x : False => x)) as HFR2. clear HFR2'.
  pose proof (kp_trans _ _ _ _ _ _ KPb (kp_sub W (sp0 - STK_check_knock_refused_B) sp0 (sp0 + -16 - 2 * ESTACK) (sp0 + -16)
    _ _ ltac:(lia) ltac:(lia) HFR2)) as KPc.
  ckr_after HS 1024%nat W regs2 mem2 HP2 HFR2 HJ2 Usp HS2. clear HS HP2 HFR2 HPRE1 R10 R11 R2 R3 R4 R1 Hsp1.
  remember (havoc E 1024 (map (getr regs2) CLOB)) as E1 eqn:HE1 in HS2.
  assert (HEI1 : img_env VAL A_LIM E1) by (rewrite HE1; apply img_env_havoc_hi; [exact HEI | cbv; lia]).
  assert (HAE1 : env_agree 32 (Ereg regs []) E1) by (rewrite HE1; apply env_agree_havoc_ge; [cbv; lia | exact HAE]).
  assert (EO1 : forall n, (n < 1024)%nat -> ew E1 n = ew E n) by (intros n Hn; rewrite HE1; apply ew_havoc_old; exact Hn).
  assert (A1 : ew E1 1028 = getr regs2 10).
  { rewrite HE1. change 1028%nat with (1024 + 4)%nat. rewrite (ew_havoc_new E 1024 _ 4 (Z_to_bv 64 0)) by (cbn; lia).
    unfold CLOB. cbn [map nth]. reflexivity. }
  assert (Usp1 : bv_unsigned (ew E1 2) = sp0) by (rewrite EO1 by lia; exact Usp).
  clear HE1.
  pose proof (bv_unsigned_in_range 64 (getr regs2 10)) as HR. change (bv_modulus 64) with (2 ^ 64) in HR.
  assert (A1' : ew E1 1028 = Z_to_bv 64 (bv_unsigned (getr regs2 10))) by (rewrite A1; symmetry; apply Z_to_bv_bv_unsigned).
  (* 0x874d8: beqz a0 *)
  psrr_branch_pi RUNP BR HS2.
  + (* a0 = 0: the arm to the no-return hook (0x874e8) and abort (0x874ec), and the UBSan trap word after it
       (0x874f0); not taken: the needle occurs at j0 *)
    exfalso. rewrite branch_eq_U in Hc. rewrite (U_atom E1 1028 _ A1' HR), U_lit in Hc by lia.
    apply Z.eqb_eq in Hc.
    destruct HQ2 as [[_ Hno] | (j & [[Hjl _] _] & Hvj)].
    * apply (Hno j0). split; [rewrite !length_map; exact Hj0 | rewrite length_map; exact Hocc].
    * rewrite !length_map in Hjl.
      rewrite Hvj in Hc. unfold w64 in Hc. rewrite unsigned_lit_small in Hc by lia. lia.
  + (* a0 <> 0: 0x874dc .. 0x874e4, the epilogue and ret *)
    clear Hc. paj_run_sh RUNP HS2 HJ2.
    { awr_ok_tac. exact Usp1. }
    ckr_kp_run HFr Usp1 (sp0 - STK_check_knock_refused_B) sp0 KPc KPd. clear HF HFr HG.
    prreg HS2 (1%bv : bv 5) Q1.
    eapply (RET W _ _ _ _ _ HS2 eq_refl ltac:(vm_compute; reflexivity)).
    intros mat'. unfold apost_base.
    lazymatch goal with |- exists _ _ _ _ _, mkCfg (mkst ?rg _ ?m _) ?d = _ /\ _ => exists ly, S, rg, m, d end.
    split; [cbn [ms_regs]; rewrite Q1, EO1, (EE 1%nat 1%bv eq_refl), Hra by lia; reflexivity|].
    split; [cbn [ms_mem]; apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ2|].
    split; [eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs [] HS2); [exact HAE1 | vm_compute; reflexivity]|].
    split; [intros a Ha Hn _; exact (KPd a Ha Hn) |].
    split; [apply Permutation_refl | split; [reflexivity | exists (st_fs S); destruct S; reflexivity]].
Qed.

(* the contract at image B's numbers, for every literal map that puts TNP where SegInstB's map does (0x21300) *)
Theorem check_knock_refused_walk : forall lit : list Z -> Z, lit TNP = SegInstB.seg_litA_fz TNP ->
  check_knock_refused_contract SEGS B (BASE + AF_check_knock_refused) SegInstB.STK_check_knock_refused
    SegInstB.RLO_A SegInstB.RHI_A lit SegInstB.gotwA SegInstB.guardA.
Proof using ART HVO STRSTR.
intros lit HLB. unfold check_knock_refused_contract.
intros ly S W regs mem md ch got kn gs k HPRE HROD H10 Rgot H11 Rkn HCP HEV.
destruct HCP as (Hg0 & [SZh TLh] & Hlen & HHP & HAD & Hkn & HKF & HLIT & HSSP).
assert (LT0 : sa_lit SEGS B (rdW W mem) (lit TNP) TNP) by (apply HLIT; left; reflexivity).
(* the map's address of TNP is the listing's object A_OBJ 26 (image B's seg_objs index 26 is 0x21300) *)
assert (HL : lit TNP = VAL (A_OBJ 26)).
{ rewrite HLB, (HVO 26%nat ltac:(apply Nat.ltb_lt; vm_compute; reflexivity)). vm_compute. reflexivity. }
rewrite HL in LT0. destruct LT0 as (_ & [SZn _] & PNn & RTn & IMn).
pose proof HPRE as (HAR & _).
(* the needle's shadow at the entry state (sa_pinned holds at every AR state) and its slack (a ROM range, mapped
   at every state) *)
pose proof (PNn ly S W mem md HAR) as ADn.
pose proof (sa_tail_of_romtail SEGS (w_H W) mem _ RTn) as TLn.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (LT : length TNP = 13%nat) by (vm_compute; reflexivity).
(* the haystack: a string in a live heap block *)
pose proof (heap_below ly S W mem md got _ HAR HHP ltac:(lia)) as [Hq1 Hq2].
pose proof (ckr_rd_bytes_view SEGS (w_H W) mem) as RB.
(* the needle: an image literal *)
assert (Hy : 0x10000 <= VAL (A_OBJ 26) /\ VAL (A_OBJ 26) + 14 <= kImgEnd).
{ pose proof (pa_img_range _ (proj1 (IMn (VAL (A_OBJ 26)) ltac:(rewrite LT; lia)))) as R1.
  pose proof (pa_img_range _ (proj1 (IMn (VAL (A_OBJ 26) + 13) ltac:(rewrite LT; lia)))) as R2. lia. }
unfold kImgEnd in Hy.
subst kn.
apply (ckr_core ly S W regs mem md ch got k (map (Z_to_bv 8) gs) (map (Z_to_bv 8) TNP) HPRE H10 H11).
- exact (ckr_strz_bytes _ got gs RB SZh).
- rewrite length_map. apply rdf_of_sa; [exact SZh | exact HAD | lia | exact Hlen | lia].
- rewrite length_map. exact (amem8_of_blockA SEGS B LAWS ly S W mem md got _ HAR HHP ltac:(lia)).
- rewrite length_map. exact TLh.
- exact (ckr_strz_bytes _ _ TNP RB SZn).
- rewrite length_map. apply rdf_of_sa; [exact SZn | exact ADn | lia | rewrite LT; lia | rewrite LT; lia].
- rewrite length_map, LT. apply amem8_of_low; [lia | unfold kLowMemEnd; lia].
- rewrite length_map. exact TLn.
- exact (rom_view_of_aro B _ _ W mem HROD).
- exact HSSP.
- intros ->. cbn [negb orb] in HKF.
  destruct SZh as [HZh HNh].
  destruct (ckr_found_occ gs TNP HNh HKF) as (j & Hj & Hoc). exists j.
  rewrite !length_map.
  rewrite (ckr_unsigned_map gs (ckr_zs_range _ got _ RB (ckr_zs_app_l _ _ _ _ HZh))).
  rewrite (ckr_unsigned_map TNP (ckr_zs_range _ _ _ RB (ckr_zs_app_l _ _ _ _ (proj1 SZn)))).
  split; [exact Hj | exact Hoc].
Qed.
End e.
End f.
End d.
