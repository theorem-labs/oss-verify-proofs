(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_qdisc/lib/A/QPgMain3.v (reseatQ) at 160c9b4d5750 and
   proofs/libreac/fuzz_knock/lib/A/APgRt.v (rt_chain) and APgMain4.v (the region and frame-chain steps) at
   6ebe35ba632; adapted to reac_box_pin_parse's calls of the strcspn wrapper and reac_box_catalogue. *)
(* reac-pw/fuzz_pin, image A (fuzz_pin.asan): reac_box_pin_parse 0x80b44, the segment 0x80c70 -> 0x80cc0 (pp_seg2)
   and the call-site lemmas of its three calls 0x80c84 (the strcspn wrapper), 0x80c94 (reac_box_catalogue) and
   0x80ce4 (the strncmp wrapper).

   This file proves no function (kind: segment lemma of reac_box_pin_parse's walk, and call-site lemmas).

   THE CALL-SITE LEMMAS are stated over memory facts at the call, not over the walk state, so that the walk files
   that reach a call (this one for 0x80c84 and 0x80c94, the loop file for 0x80ce4) apply them at their own state:
   - pp_spec_now carries the spec string's premise from the entry memory to the memory of a call (the string lies
     in a heap block of the caller, tpin_parse_specX's clause for sa <> 0);
   - pin_strcspn_site and pin_strncmp_site give every premise of astrcspn_realizes at (sa, colonp) and of
     astrncmp_realizes at (sa, TP i, toklen) that is a fact of memory: the awrap_str facts (lib/A/PPgWrap.v), the
     one-byte set, the len + 8 ranges, the bound of the count, and the strncmp_model equation when
     strlen (TP i) = toklen;
   - pin_cat_site gives tpin_catalogue_specX's premises on the count cell F + 0x20 of the function's own frame;
     pin_chain gives the callee's frame chain from sp1 (s0 = the entry sp, ra / s0 saved at entry sp - 8 / - 16).

   THE SEGMENT (PPgParseCx.PP_seg2: pp_from ss_PL (INV_PL .. 0) -> pp_from ss_P2 INV_P2), the code of the neutral
   excerpt of 0x80c70-0x80cbc:
   - 0x80c70-0x80c80: SB spilled at sp1 + 0x18, s6 = F + 0x20, a1 = 0x20d80 (the ':' set), a0 = sa;
   - 0x80c84: the strcspn wrapper (PPgParseLib.aj_strcspn_at with pin_strcspn_site; the spec string from
     pp_spec_now, the ':' set from pin_ro_law_at at the call's memory, the read-only fact from pp_aro_kept); the
     re-seat puts the result, cspn_len [':'] s = colon_idx s (pp_cspn_colon_bytes), in the junk atom 404;
   - 0x80c88-0x80c90: s9 = toklen, `sb zero,4(s4)` makes the count cell's shadow byte 0 (the frame's shadow
     region re-windowed writable for the store, read-only again after), a0 = F + 0x20;
   - 0x80c94: reac_box_catalogue through CATALOGUE (tpin_catalogue_specX at cat) with SRr_bind: pin_pre_kit from the
     carried journal with own = (0, fpos) :: own and the window T_leaf_STK, the chain pin_chain, the cell premises
     pin_cat_site; its post gives a0 = cat (junk atom 444), the count cell = 11, every byte outside [sp1 - 16, sp1)
     and the cell unchanged; the frame region is re-added with the count 11 and the flag pointer;
   - 0x80c98-0x80cbc: s3 = 11 (`ld s3,0(s6)` from the frame region), `beqz s3` decided not taken, s7 = s8 = cat,
     mo and lb spilled at sp1 + 8 / + 0x10, s6 = SB + cat/8; the join into ss_PL at row 0 (toklen 100, row 102,
     rows left 103), and the hand-off to pp_from ss_PL (INV_PL .. 0) (no earlier row: vacuous).
   After every run, call and store the kept-memory fact is rebuilt with PPgParseLib.pp_KE_step. *)
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YG0b YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YI16 YM05 YCeo.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.A Require Import AWalkFw0 ACef AF0l ACej ACeh ACem ACep AWalkFw1 AWalkFw2 ACfm.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Prog Require Import pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.A.Rt Require Import WrapRo.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.A Require Import PPgBase PPgCSpec PPgWrap PPgParseLib.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.A.Prog Require Import PinBlkTail.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.A Require Import PPgParseCx.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Local Open Scope Z_scope.

Section m. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable segs : list Segment.

(* A window of the callee inside the caller's window. *)
Lemma pin_off_window : forall (lo hi lo' hi' x y : Z),
lo <= lo' -> hi' <= hi ->
(forall a, x <= a <= y -> ~ (lo <= a < hi)) ->
(forall a, x <= a <= y -> ~ (lo' <= a < hi')).
Proof. intros lo hi lo' hi' x y H1 H2 H a Ha Hw. apply (H a Ha). lia. Qed.

Section t.
Variable TP : nat -> Z.

(* ============================== the call site 0x80ce4: the strncmp wrapper ==============================
   a0 = sa, a1 = TP i, a2 = toklen = colon_idx s, reached only when the strlen of TP i is toklen. Both strings
   are facts of the memory of the call; the wrapper's window [sp - 2 * ESTACK, sp) misses both. pin_ro_str
   carries the len + 8 application range the wrapper asks for. *)
Lemma pin_strncmp_site : forall (W : world segs) (mem : word -> option byte) (regs : bvmap 5 word)
(sa : Z) (s : list byte) (i : nat),
pin_ro_str segs (mrestrict (w_H W) mem) (aview segs (w_H W) mem) sa s ->
~ In NUL s ->
(forall a, sa <= a <= sa + Z.of_nat (length s) -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs)) ->
(i < CAT_N)%nat ->
pin_ro_str segs (mrestrict (w_H W) mem) (aview segs (w_H W) mem) (TP i) (tok_bytes i) ->
(forall a, TP i <= a <= TP i + pin_tokn i -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs)) ->
length (tok_bytes i) = colon_idx s ->
awrap_str segs W mem regs sa s /\ awrap_str segs W mem regs (TP i) (tok_bytes i) /\
amem_range sa (Z.of_nat (length s) + 8) /\ amem_range (TP i) (Z.of_nat (length (tok_bytes i)) + 8) /\
0 <= Z.of_nat (colon_idx s) < 2 ^ 32 /\
exists d, strncmp_model (s ++ [Z_to_bv 8 0]) (tok_bytes i ++ [Z_to_bv 8 0]) (Z.of_nat (colon_idx s)) = Some d.
Proof.
intros W mem regs sa s i HS HN HW Hi HT HWT HL.
split; [exact (pp_awrap_of_ro segs W mem regs sa s HS HN HW)|].
split.
{ apply (pp_awrap_of_ro segs W mem regs (TP i) (tok_bytes i) HT); [| exact HWT].
  intros Hin. exact (tokens_no_nul i NUL Hi Hin eq_refl). }
split; [exact (proj1 (proj2 (proj2 (proj2 HS))))|]. split; [exact (proj1 (proj2 (proj2 (proj2 HT))))|].
split.
{ pose proof (colon_idx_le s) as Hle. destruct HS as (_ & _ & H2 & _). lia. }
destruct (pp_strncmp_tok i s (colon_idx s) Hi HN eq_refl ltac:(rewrite HL; reflexivity)) as (d & Hd & _).
exists d. exact Hd.
Qed.

End t.

(* ============================== the call site 0x80c84: the strcspn wrapper ==============================
   a0 = sa (the spec string s), a1 = colonp (the ':' set and its NUL). The set has exactly one byte, which is
   the form astrcspn_realizes asks for. *)
Lemma pin_colon_no_nul : ~ In NUL pin_colon_bytes.
Proof. unfold pin_colon_bytes, NUL. intros [H|H]; [discriminate H | exact H]. Qed.

Lemma pin_strcspn_site : forall (W : world segs) (mem : word -> option byte) (regs : bvmap 5 word)
(sa : Z) (s : list byte) (colonp : Z),
pin_ro_str segs (mrestrict (w_H W) mem) (aview segs (w_H W) mem) sa s ->
~ In NUL s ->
(forall a, sa <= a <= sa + Z.of_nat (length s) -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs)) ->
pin_ro_str segs (mrestrict (w_H W) mem) (aview segs (w_H W) mem) colonp pin_colon_bytes ->
(forall a, colonp <= a <= colonp + 1 -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs)) ->
awrap_str segs W mem regs sa s /\ awrap_str segs W mem regs colonp pin_colon_bytes /\
(length pin_colon_bytes = 1)%nat.
Proof.
intros W mem regs sa s colonp HS HN HW HC HWC.
split; [exact (pp_awrap_of_ro segs W mem regs sa s HS HN HW)|].
split; [|reflexivity].
exact (pp_awrap_of_ro segs W mem regs colonp pin_colon_bytes HC pin_colon_no_nul HWC).
Qed.

(* ============================ the call site 0x80c94: reac_box_catalogue ============================
   a0 = c = F + 0x20, the count cell of the function's own class-0 frame F (64 bytes, 8-aligned): 0x80c8c
   `sb zero,4(s4)` made the cell's shadow byte SHADOW_OFF + F / 8 + 4 zero. The frame lies below
   alloc_ceiling and the callee's window [sp - 16, sp) lies above it. *)
Lemma pin_cat_site : forall (B : asyms) (ly : alayout) (S : astate) (W : world segs) (mem : word -> option byte)
(regs : bvmap 5 word) (own : list (Z * Z)) (fpos F : Z),
In (0, fpos) (frames S) -> frame_addr ly 0 fpos = F -> F mod 8 = 0 -> 4096 <= F ->
F + 64 <= alloc_ceiling -> alloc_ceiling <= spZ regs - T_leaf_STK ->
aview segs (w_H W) mem (SHADOW_OFF + F / 8 + 4) = Some 0 ->
F + 32 <> 0 /\ (F + 32) mod 8 = 0 /\
In (0, fpos) ((0, fpos) :: own) /\ 0 <= 0 /\ frame_addr ly 0 fpos mod 8 = 0 /\
frame_addr ly 0 fpos <= F + 32 /\ F + 32 + 8 <= frame_addr ly 0 fpos + fs_frame_bytes 0 /\
(spZ regs <= F + 32 \/ F + 32 + 8 <= spZ regs - T_leaf_STK) /\
afobj segs B ly S W mem (F + 32) 8.
Proof.
intros B ly S W mem regs own fpos F Hin EF HF8 HF0 HFc Hsp Hsh.
assert (Hc8 : (F + 32) mod 8 = 0) by (rewrite <- Zplus_mod_idemp_l, HF8; reflexivity).
change (fs_frame_bytes 0) with 64. rewrite EF.
split; [lia|]. split; [exact Hc8|]. split; [left; reflexivity|]. split; [lia|]. split; [exact HF8|].
split; [lia|]. split; [lia|]. split; [right; lia|].
unfold afobj. split; [|split; [exact Hc8|]].
- exists 0, fpos. split; [exact Hin|]. split; [lia|]. rewrite EF. split; [exact HF8|].
  change (fs_frame_bytes 0) with 64. lia.
- unfold range_addressable. intros x Hx. exists 0. split; [|left; reflexivity].
  assert (Ex : x / 8 = F / 8 + 4).
  { pose proof (Z.div_mod F 8 ltac:(lia)) as DF. rewrite HF8, Z.add_0_r in DF.
    symmetry. apply Z.div_unique with (r := x - (F + 32)); [left; lia | lia]. }
  unfold shadow_of_addr. rewrite Ex, Z.add_assoc. exact Hsh.
Qed.

(* ============================ the frame chain at the call of reac_box_catalogue ============================
   The function keeps s0 = its entry sp and saved ra / s0 at entry sp - 8 / - 16, so the callee's chain from
   sp1 is the entry chain with one more link (knock's lib/A/APgRt.v rt_chain, with the entry chain ch). *)
Definition pin_ch (ly : alayout) (regs : bvmap 5 word) (ch : list (Z * Z * Z)) : list (Z * Z * Z) :=
if spZ regs + 16 <? ly_top ly then (spZ regs, raZ regs, s0Z regs) :: ch else [].
(* [knock A/APgRt.v:142-156 rt_chain, over the entry chain ch] *)
Lemma pin_chain : forall ly (rd rd' : reader) (regs : bvmap 5 word) ch sp',
achain ly rd (spZ regs) (s0Z regs) ch -> ly_top ly <= 2 ^ 64 ->
(forall a, spZ regs <= a < 2 ^ 64 -> rd' a = rd a) ->
rdword rd' (spZ regs - 8) = Some (raZ regs) -> rdword rd' (spZ regs - 16) = Some (s0Z regs) -> 4096 <= raZ regs ->
alloc_ceiling <= spZ regs -> spZ regs mod 8 = 0 -> sp' + 16 <= spZ regs ->
achain ly rd' sp' (spZ regs) (pin_ch ly regs ch).
Proof.
intros ly rd rd' regs ch sp' Hch Htop64 Hk H8 H16 Hra Hceil Hal Hsp'.
unfold pin_ch. destruct (Z.ltb_spec (spZ regs + 16) (ly_top ly)) as [Hlt | Hge].
- apply (achain_push ly rd rd' (spZ regs) (s0Z regs) (raZ regs) ch sp' Hch Htop64 Hk H8 H16 Hra Hceil Hal);
  lia.
- left. split; [right; left; lia | reflexivity].
Qed.

(* ========================= the spec string at the memory of a call =========================
   The string and its NUL lie in one heap block (b, m) of the caller (tpin_parse_specX's clause for sa <> 0).
   Along a kept fact (acall_kept) whose changed cells miss the string, its bytes are the entry's (the block
   clause); its shadow bytes and their hull come from the allocator relation of the current state
   (AR_shadow_law over the same block, which the permutation of the blocks keeps); the rest of the NUL's 8-byte
   word is present (blk_tail_present); the block's place gives the len + 8 application range
   (PPgParseLib.pp_amem_blk). *)
Section s.
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.
Lemma pp_spec_now : forall (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte)
(lyN : alayout) (SN : astate) (WN : world segs) (memN : word -> option byte) (mdN : Model)
(slo shi : Z) (Eo : Z -> Prop) (regs : bvmap 5 word) (STK_f sa : Z) (s : list byte) (b m : Z),
AR segs B lyN SN WN memN mdN ->
Permutation (ablocks B lyN SN) (ablocks B lyc Sc) ->
acall_kept segs B lyc Sc W memc WN memN slo shi Eo ->
(forall x, Eo x -> ~ (sa <= x <= sa + Z.of_nat (length s))) ->
In (b, m) (ablocks B lyc Sc) -> b <= sa -> sa + Z.of_nat (length s) + 1 <= b + req_size m ->
pin_spec_str segs (mrestrict (w_H W) memc) (aview segs (w_H W) memc) regs STK_f sa s ->
pin_ro_str segs (mrestrict (w_H WN) memN) (aview segs (w_H WN) memN) sa s.
Proof.
intros lyc Sc W memc lyN SN WN memN mdN slo shi Eo regs STK_f sa s b m HAR HPerm KE HEo Hin Hb Hbe HSS.
assert (HinN : In (b, m) (ablocks B lyN SN)) by exact (Permutation_in _ (Permutation_sym HPerm) Hin).
pose proof KE as (_ & K2 & _).
destruct HSS as (HN & H0 & H1 & H2 & HG & HRA & HHV & HT & HM & HW).
assert (KB : forall a, sa <= a <= sa + Z.of_nat (length s) ->
  aview segs (w_H WN) memN a = aview segs (w_H W) memc a).
{ intros a Ha. replace a with (b + (a - b)) by lia.
  apply (K2 b m (a - b) Hin); [lia|].
  replace (b + (a - b)) with a by lia. intros He. exact (HEo a He Ha). }
destruct (al_shadow _ _ LAWS lyN SN WN memN mdN b m HAR HinN) as [Hbs _].
split; [exact H0|]. split; [exact H1|]. split; [exact H2|].
split; [exact (pp_amem_blk segs B LAWS lyN SN WN memN mdN b m sa (Z.of_nat (length s)) HAR HinN Hb Hbe)|].
split.
{ intros j Hj. destruct (HG j Hj) as [Hv Hr]. split; [|exact Hr].
  assert (Hjl : (j <= length s)%nat).
  { unfold pin_zbytes in Hj. rewrite length_app, length_map in Hj. cbn [length] in Hj. lia. }
  apply (val_mem_kept segs (w_H W) (w_H WN) memc memN (sa + Z.of_nat j) 1 (nth j (pin_zbytes s ++ [0]) 0)); [|exact Hv].
  intros k Hk. apply KB. lia. }
split.
{ exact (block_shadow_range _ SHADOW_OFF b (req_size m) sa (Z.of_nat (length s) + 1) Hbs Hb ltac:(lia)). }
split.
{ exact (shadow_hull_vis_of_block segs B LAWS lyN SN WN memN mdN b m sa (Z.of_nat (length s) + 1) HAR HinN Hb
    ltac:(lia) ltac:(lia)). }
intros a Ha.
apply (blk_tail_present segs B LAWS lyN SN WN memN mdN b m (sa + Z.of_nat (length s) - b) a HAR HinN); [lia|].
replace (b + (sa + Z.of_nat (length s) - b)) with (sa + Z.of_nat (length s)) by lia. exact Ha.
Qed.
End s.
End m.

(* [qdisc A/QPgMain3.v:95-120 reseatQ (knock A/APgMain4.v:149-178 reseatK)]: the re-seat after a call, the junk-atom
   floor K a parameter and the equation of the re-seated valuation kept as HEv. *)
Ltac reseatQ HS K HJ2 HP2 keep AG kept_tac HEv :=
let HS2 := fresh "HS2" in
lazymatch type of HJ2 with ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ ?W2 ?mem2 _ _ =>
lazymatch type of HP2 with aregs_preserved _ ?regs2 =>
jafter_call_keep HS K regs2 (mrestrict (w_H W2) mem2) HP2 keep HS2 end end;
match type of HS2 with ?Q -> _ =>
let HQ := fresh "HQ" in
assert (HQ : Q); [ cbn [ms_mem restrict]; repeat apply Forall_cons; try apply Forall_nil; kept_tac | specialize (HS2 HQ); clear HQ ] end;
clear HS; rewrite <- restrict_mkst_fx in HS2; rename HS2 into HS;
let AG2 := fresh "AG" in let Ev := fresh "E" in
lazymatch type of AG with forall n, _ -> _ = ew ?E0 n =>
lazymatch type of HS with st_ok _ ?Enew _ _ =>
remember Enew as Ev eqn:HEv in HS;
assert (AG2 : forall n, (n < 33)%nat -> ew Ev n = ew E0 n)
by (intros nn Hnn; rewrite HEv; rewrite ?ew_havoc_old by (clear - Hnn; lia); rewrite ?ew_ewset_other by (clear - Hnn; lia); apply AG; exact Hnn);
repeat match goal with H : ew ?Eo ?n = ?v |- _ =>
lazymatch Eo with
| Ev => fail
| _ => lazymatch (eval cbv in (Nat.leb 33 n)) with
| true => let H2 := fresh H in
assert (H2 : ew Ev n = v) by (rewrite HEv; rewrite ?ew_havoc_old by nat_side; rewrite ?ew_ewset_other by nat_side; exact H);
clear H; rename H2 into H
end end end;
clear AG; rename AG2 into AG end end.

(* the region based at atom n of the state HS, as a region_ok fact HR [knock A/APgMain4.v:249-253] *)
Ltac p2_region HS n HR :=
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs n in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rs got_region) in
pose proof (st_ok_region_nth Ex ssx msx i r HS ltac:(vm_compute; reflexivity)) as HR; cbn [ms_mem restrict] in HR end.

(* a byte off the image that two memories read alike is present in the second when it is in the first *)
Lemma p2_apresent_of_aview : forall (H H' : word -> bool) (m m' : word -> option byte) a,
0 <= a < 2 ^ 64 -> ~ in_img tfibsegs a ->
aview tfibsegs H' m' a = aview tfibsegs H m a -> apresent H m a -> apresent H' m' a.
Proof.
intros H H' m m' a Ha Hi E [Hh [b Hb]].
pose proof (mbyte_of_aview tfibsegs _ _ _ _ _ E) as Em.
unfold mbyte, mrestrict in Em. rewrite Hh, Hb in Em.
destruct (H' (Z_to_bv 64 a)) eqn:Eh'.
- rewrite (seg_rom_none tfibsegs a Ha Hi) in Em. discriminate.
- split; [exact Eh'|]. destruct (m' (Z_to_bv 64 a)) as [b'|] eqn:Em'; [exists b'; reflexivity|].
  rewrite (seg_rom_none tfibsegs a Ha Hi) in Em. discriminate.
Qed.

(* ================================ the segment 0x80c70 -> 0x80cc0 ================================
   The Section hypotheses are PLAN section 3's names (a Section keeps only the ones the proof uses), with RELRO, the
   read-only range in the image, which PPgParseCx.pp_arodata_kept asks for to carry arodata_okP to a later state. *)
Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis FFL : frame_flag_lawP tfibsegs B.
Hypothesis ASTRCSPN : astrcspn_realizes tfibsegs B 0x4191c.
Variables RLO RHI cat : Z.
Variables TP DP : nat -> Z.
Hypothesis RELRO : forall a, RLO <= a < RHI -> in_img tfibsegs a.
Hypothesis CATALOGUE : tpin_catalogue_specX tfibsegs B MT 0x80f7c cat.

Lemma pp_seg2 : PP_seg2 B MT RLO RHI cat TP DP.
Proof.
unfold PP_seg2. intros RL. pp_prelude.
destruct HINV as (HLV & Hsnil).
destruct (proj1 (pp_live_iff sa mo lb) HLV) as (Hsa0 & Hmo0 & Hlb0).
destruct (Hstr Hsa0) as (HSTR & bq & mq & Hbq & Hbq0 & Hbq1).
pose proof HSTR as (HNs & _ & _ & _ & _ & _ & _ & _ & _ & HWs).
destruct (Hlive HLV) as (Hmo8 & Hlb8 & Hmolb & Hinm & Hcm & Hfam & Hmo1 & Hmo2 & Hinl & Hcl & Hfal & Hlb1 & Hlb2 & HAFm & HAFl & HOCw & HOCs).
assert (HlyF : ly_F lyN = ly_F lyc) by (eapply pp_lyF; [exact HJ0 | exact HJ]).
pose proof HJ0 as (_ & _ & _ & _ & _ & Hfr0 & _).
assert (HOCF : pp_oc_frames lyc Sc (pin_parse_live sa mo lb) mo lb cidm posm cidl posl).
{ intros _. rewrite Hfr0. repeat split; try (apply in_or_app; left; assumption); lia. }
destruct (pp_oc_sep tfibsegs B LAWS lyc Sc W memc mdc _ _ _ _ _ _ _ HAR0 HOCF) as (HEc & HEb).
pose proof (pp_oc_img B lyc Sc W memc mdc _ _ _ _ _ _ _ HAR0 HOCF) as HEi.
(* 0x80c70 .. 0x80c80: to the strcspn wrapper *)
reshok HS.
aj_run_tok tfibtbl_lib_ok HS HJ SHOK PPBspan.
{ ppAWR AG fpos F EFA ltac:(fail). }
lazymatch type of HJ with ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mdx _ =>
  assert (HIO1 : same_io mdc mdx) by (eapply same_io_trans; [exact HIO | apply same_io_with_vm_backing]) end.
clear HIO.
(* the memory the run changed: the caller's stack window and the own frame *)
assert (Hw1 : forall b0 wlo whi a, In (b0, wlo, whi) (windows (ss_mem ss_P2)) ->
  base_val E b0 + wlo <= a < base_val E b0 + whi ->
  (fun a => (spZ regs - 176 <= a < spZ regs) \/ pp_nf F FL a) a).
{ intros b0 wlo whi a Hin Ha.
  lazymatch type of Hin with In _ ?l => let l' := eval vm_compute in l in change (In (b0, wlo, whi) l') in Hin end.
  cbn [In] in Hin.
  repeat (destruct Hin as [Hq | Hin];
    [injection Hq as <- <- <-; cbn [base_val] in Ha; revert Ha; evalE AG; intros Ha; cbv beta; unfold pp_nf; lia |]).
  destruct Hin. }
pose proof (pz_kept_own B LAWS lyc lyN Sc SN W memc mdc WN (ms_mem msN) mdN WN (ms_mem msN) WN (ms_mem ms)
  (spZ regs - T_parse_STK) (spZ regs) fpos F FL _ (fun a => (spZ regs - 176 <= a < spZ regs) \/ pp_nf F FL a)
  HAR0 HARN Hfrs HPERM HlyF eq_refl eq_refl FFL ltac:(change T_parse_STK with 8400; lia) ltac:(lia) HEc HEi
  ltac:(intros a [Ha|Ha]; [left; change T_parse_STK with 8400; lia | right; right; exact Ha]) HKE
  (kept_of_frame _ _ _ _ _ _ HFr Hw1) (fun a _ Ha => apresent_grows _ _ _ a HG Ha)) as HKE1.
clear HKE Hw1 HF HFr. rename HKE1 into HKE.
rreg HS (1%bv : bv 5) Rra. rreg HS (2%bv : bv 5) Rsp. rreg HS (3%bv : bv 5) Rgp. rreg HS (4%bv : bv 5) Rtp.
rreg HS (10%bv : bv 5) Ra0. rreg HS (11%bv : bv 5) Ra1.
pose proof HJ0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hsp0al & _) & _).
assert (Usp1 : bv_unsigned (ew E 70) = sp1)
  by (rewrite E70; apply unsigned_lit_small; clear - Hsp1 HspLo HspHi Hceil Hslo Hshi H47 C1; lia).
assert (Esp : spZ (ms_regs ms) = sp1) by (unfold spZ; rewrite Rsp; exact Usp1).
(* the two strings at the memory of the call *)
pose proof (proj1 HJ) as HART.
assert (HEos : forall x, (pin_parse_live sa mo lb = true /\ pin_out_cell mo lb x) ->
  ~ (sa <= x <= sa + Z.of_nat (length s))) by (intros x [_ Hx]; exact (HOCs x Hx)).
pose proof (pp_spec_now tfibsegs B LAWS lyc Sc W memc lyN SN WN (ms_mem ms) _ _ _ _ regs T_parse_STK sa s bq mq
  HART HPERM HKE HEos Hbq Hbq0 Hbq1 HSTR) as HROs.
pose proof (pp_arodata_kept B RLO RHI lyc Sc W memc WN (ms_mem ms) _ _ _ RELRO HKE HROD) as HRODT.
destruct (pin_ro_law_at tfibsegs B RLO RHI cat TP DP PP_COLON STK sp0 FP ly S W0 mem0 md0 ((0, fpos) :: own)
  lyN SN WN (ms_mem ms) _ k Hrolaw HJ HRODT) as (HcatT & HcolT).
assert (HWsT : forall a, sa <= a <= sa + Z.of_nat (length s) ->
  ~ (spZ (ms_regs ms) - 2 * ESTACK <= a < spZ (ms_regs ms))).
{ rewrite Esp, Hes. intros a Ha Hw. apply (HWs a Ha). change T_parse_STK with 8400. clear - Hw Hsp1. lia. }
assert (HWcT : forall a, PP_COLON <= a <= PP_COLON + 1 ->
  ~ (spZ (ms_regs ms) - 2 * ESTACK <= a < spZ (ms_regs ms))).
{ rewrite Esp, Hes. intros a Ha Hw. apply (Hcolst a Ha). change T_parse_STK with 8400. clear - Hw Hsp1. lia. }
destruct (pin_strcspn_site tfibsegs WN (ms_mem ms) (ms_regs ms) sa s PP_COLON HROs HNs HWsT HcolT HWcT)
  as (Haws & Hawc & Hlen1).
pose proof (pp_aro_kept tfibsegs B lyc Sc W memc WN (ms_mem ms) _ _ _
  (aro_unowned_of_arodataP tfibsegs B RLO RHI _ HROD) HKE) as HaroT.
(* 0x80c84: the strcspn wrapper *)
rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
eapply SRr_bind.
{ eapply (aj_strcspn_at tfibsegs B LAWS tfib_segs_low 268572 ASTRCSPN WN (ms_regs ms) (ms_mem ms) STK sp0 FP ly S
    W0 mem0 md0 ((0, fpos) :: own) lyN SN _ k sa PP_COLON s pin_colon_bytes (sp1 - sp0) _ HJ).
  - rewrite Ra0, (AG 10%nat) by lia. exact E10.
  - rewrite Ra1. reflexivity.
  - rewrite Esp. lia.
  - rewrite Zminus_mod, Hsp1al16, Hsp0al. reflexivity.
  - lia.
  - rewrite Hes. clear - Hsp1 HspLo. lia.
  - rewrite Rgp, (AG 3%nat) by lia. rewrite (EE 3%nat 3%bv eq_refl). exact Hgp.
  - rewrite Rtp, (AG 4%nat) by lia. rewrite (EE 4%nat 4%bv eq_refl). exact Htp.
  - exact Rra.
  - apply ret_ok_even; vm_compute; reflexivity.
  - exact Haws.
  - exact Hawc.
  - exact Hlen1.
  - exact HaroT. }
cbv beta. intros W2 c2 Hwle2 (-> & regs2 & mem2 & md2 & -> & HJ2 & HIO2 & HP2 & Ha02 & Hfr2 & Hpres2).
pose proof (same_io_trans _ _ _ HIO1 HIO2) as HIO. clear HIO1 HIO2.
replace (sp0 + (sp1 - sp0)) with sp1 in Hfr2 by lia.
(* the caller's memory after the wrapper: only its window [sp1 - 2 * ESTACK, sp1) changed *)
pose proof (pp_KE_step B LAWS lyc Sc W memc mdc lyN SN WN (ms_mem msN) mdN WN (ms_mem ms) WN mem2 fpos F FL
  sa mo lb regs cidm posm cidl posl (fun a => sp1 - 2 * ESTACK <= a < sp1) HAR0 HARN Hfrs HPERM HlyF eq_refl eq_refl
  FFL ltac:(change T_parse_STK with 8400; lia) ltac:(lia) HOCF
  ltac:(intros a Ha; left; change T_parse_STK with 8400; rewrite Hes in Ha; lia) HKE
  ltac:(intros a Ha Hn; exact (Hfr2 a Ha Hn)) ltac:(intros a _ Ha; exact (Hpres2 a Ha))) as HKE2.
clear HKE. rename HKE2 into HKE.
pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HpresT2 & _).
(* the re-seat: the four regions are kept; the clobbered registers get the junk atoms 400.. *)
reseatQ HS 400%nat HJ2 HP2 [0; 1; 2; 3]%nat AG
  ltac:(idtac; ppKEPTO Hfr2 AG ltac:(idtac; fail)
    ltac:(idtac; first [ apply HpresT2; lia
                | apply Hpres2; apply (apresent_grows _ _ _ _ HG);
                  match goal with |- apresent _ _ ?x => apply (proj1 (HFpres x ltac:(lia))) end ])) HE2.
lazymatch type of HE2 with ?Ev = havoc ?Eo _ _ =>
  assert (Etl : ew Ev 404 = Z_to_bv 64 (Z.of_nat (colon_idx s)))
  by (rewrite HE2; change 404%nat with (400 + 4)%nat; rewrite (ew_havoc_new Eo 400 _ 4 (Z_to_bv 64 0)) by (cbn; lia);
      cbn [nth map CLOB]; rewrite Ha02, pp_cspn_colon_bytes; reflexivity) end.
clear HE2 Ha02 Rra Rsp Rgp Rtp Ra0 Ra1 Esp Usp1 HROs HRODT HcatT HcolT HWsT HWcT Haws Hawc Hlen1 HaroT.
(* 0x80c88 .. 0x80c94: s9 = toklen, the count cell's shadow byte := 0 (`sb zero,4(s4)`), a0 = F + 0x20 *)
assert (HpS2 : forall i, 0 <= i < 8 -> apresent (w_H WN) mem2 (shadow_addr F + i) /\ True).
{ intros i Hi. split; [|exact I]. apply Hpres2. apply (apresent_grows _ _ _ _ HG). exact (proj1 (HFSpres i Hi)). }
clear HG HpresT2.
pp_fs_rw HS E88 HpS2.
aj_run_to_sh tfibtbl_lib_ok HS HJ2 0x80f7c.
{ ppAWR AG fpos F EFA ltac:(fail). }
lazymatch type of HJ2 with ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mdx _ =>
  assert (HIO1 : same_io mdc mdx) by (eapply same_io_trans; [exact HIO | apply same_io_with_vm_backing]) end.
clear HIO.
lazymatch type of HFr with frame_of ?Ef ?rsf _ _ =>
assert (Hw2 : forall b0 wlo whi a, In (b0, wlo, whi) (windows rsf) ->
  base_val Ef b0 + wlo <= a < base_val Ef b0 + whi ->
  (fun a => (spZ regs - 176 <= a < spZ regs) \/ pp_nf F FL a) a)
by (intros b0 wlo whi a Hin Ha;
  lazymatch type of Hin with In _ ?l => let l' := eval vm_compute in l in change (In (b0, wlo, whi) l') in Hin end;
  cbn [In] in Hin;
  repeat (destruct Hin as [Hq | Hin];
    [injection Hq as <- <- <-; cbn [base_val] in Ha; revert Ha; evalE AG; intros Ha; cbv beta; unfold pp_nf, SHADOW_OFF; lia |]);
  destruct Hin) end.
lazymatch type of HG with mem_grows (mrestrict _ ?mA) (mrestrict _ ?mB) =>
pose proof (pp_KE_step B LAWS lyc Sc W memc mdc lyN SN WN (ms_mem msN) mdN WN mA WN mB fpos F FL
  sa mo lb regs cidm posm cidl posl (fun a => (spZ regs - 176 <= a < spZ regs) \/ pp_nf F FL a) HAR0 HARN Hfrs HPERM
  HlyF eq_refl eq_refl FFL ltac:(change T_parse_STK with 8400; lia) ltac:(lia) HOCF
  ltac:(intros a [Ha|Ha]; [left; change T_parse_STK with 8400; lia | right; right; exact Ha]) HKE
  (kept_of_frame _ _ _ _ _ _ HFr Hw2) (fun a _ Ha => apresent_grows _ _ _ a HG Ha)) as HKE2 end.
clear HKE Hw2 HF HFr. rename HKE2 into HKE.
pp_fs_ro HS.
(* 0x80c94: reac_box_catalogue at c = F + 0x20 *)
lazymatch type of HS with st_ok _ ?e _ (restrict _ ?m) => rename e into EC; rename m into msC end.
rreg HS (1%bv : bv 5) Rra. rreg HS (2%bv : bv 5) Rsp. rreg HS (3%bv : bv 5) Rgp. rreg HS (4%bv : bv 5) Rtp.
rreg HS (8%bv : bv 5) Rs0. rreg HS (10%bv : bv 5) Ra0.
clear HG.
assert (Esp : spZ (ms_regs msC) = sp1)
  by (unfold spZ; rewrite Rsp, E70; apply unsigned_lit_small; clear - Hsp1 HspLo HspHi Hceil Hslo Hshi H47 C1; lia).
assert (Es0 : s0Z (ms_regs msC) = spZ regs) by (unfold s0Z; rewrite Rs0, (AG 2%nat) by lia; exact Usp).
assert (HF8m : F mod 8 = 0).
{ rewrite (Z.div_mod F 32) by lia. rewrite HFal, Z.add_0_r. replace (32 * (F / 32)) with ((4 * (F / 32)) * 8) by lia.
  apply Z_mod_mult. }
assert (EF32 : getr (ms_regs msC) 10 = w64 (F + 32)).
{ rewrite Ra0, E75, unsigned_lit_small by (clear - HF4096 HFceil C1; lia). reflexivity. }
(* the caller's saved ra and s0 at entry sp - 8 / - 16, for the callee's frame chain [knock A/APgMain4.v:248-265] *)
assert (Usp3 : bv_unsigned (ew EC 2) = spZ regs) by (rewrite (AG 2%nat) by lia; exact Usp).
p2_region HS 2%nat HRstk.
lazymatch type of HRstk with region_ok _ _ _ (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region EC _ 2 (spZ regs) cs lo hi wlo whi (-8) 8%N (SOff 1 0) (raZ regs) HRstk Usp3
  ltac:(cbn; tauto)
  ltac:(rewrite sv_denot_SOff0, (AG 1%nat) by lia; rewrite (EE 1%nat 1%bv eq_refl); unfold raZ; symmetry; apply Z_to_bv_bv_unsigned)
  ltac:(unfold raZ; pose proof (bv_unsigned_in_range 64 (getr regs 1)) as Hq; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Hq; exact Hq)
  ltac:(cbn; lia)) as Vra;
pose proof (field_of_region EC _ 2 (spZ regs) cs lo hi wlo whi (-16) 8%N (SOff 8 0) (s0Z regs) HRstk Usp3
  ltac:(cbn; tauto)
  ltac:(rewrite sv_denot_SOff0, (AG 8%nat) by lia; rewrite (EE 8%nat 8%bv eq_refl); unfold s0Z; symmetry; apply Z_to_bv_bv_unsigned)
  ltac:(unfold s0Z; pose proof (bv_unsigned_in_range 64 (getr regs 8)) as Hq; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Hq; exact Hq)
  ltac:(cbn; lia)) as Vs0 end.
clear HRstk.
pose proof HLY0 as (_ & _ & _ & _ & _ & _ & _ & _ & Etop0 & _).
pose proof (proj1 (proj2 HJ2)) as HLYN. pose proof HLYN as (_ & _ & _ & _ & _ & _ & _ & _ & EtopN & _).
pose proof HJ0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & _ & _ & _ & _ & Htopl) & _).
assert (Hch1 : achain lyN (aview tfibsegs (w_H WN) (ms_mem msC)) sp1 (spZ regs) (pin_ch lyN regs ch)).
{ apply (pin_chain lyN (aview tfibsegs (w_H W) memc) _ regs ch sp1).
  - apply (achain_ly_top lyc); [rewrite EtopN, Etop0; reflexivity | exact Hch].
  - rewrite EtopN. clear - Htopl Hshi H47. lia.
  - intros a Ha. pose proof HKE as (K1 & _). apply K1.
    + clear - Ha Hceil Hslo HspLo C1. lia.
    + change T_parse_STK with 8400. clear - Ha. lia.
  - exact (rdword_of_val_mem tfibsegs _ _ _ _ Vra
      ltac:(unfold raZ; pose proof (bv_unsigned_in_range 64 (getr regs 1)) as Hq; change (bv_modulus 64) with (2 ^ 64) in Hq; exact Hq)).
  - exact (rdword_of_val_mem tfibsegs _ _ _ _ Vs0
      ltac:(unfold s0Z; pose proof (bv_unsigned_in_range 64 (getr regs 8)) as Hq; change (bv_modulus 64) with (2 ^ 64) in Hq; exact Hq)).
  - exact Hra4.
  - clear - Hceil Hslo HspLo C1. lia.
  - rewrite (Z.div_mod (spZ regs) 16) by lia. rewrite Hal16, Z.add_0_r.
    replace (16 * (spZ regs / 16)) with ((2 * (spZ regs / 16)) * 8) by lia. apply Z_mod_mult.
  - clear - Hsp1. lia. }
clear Vra Vs0.
(* the count cell's shadow byte is 0 (region 88, byte 4) *)
p2_region HS 88%nat HRS.
assert (Hsh0 : aview tfibsegs (w_H WN) (ms_mem msC) (SHADOW_OFF + F / 8 + 4) = Some 0).
{ lazymatch type of HRS with region_ok _ _ _ (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
  pose proof (field_of_region EC _ 88 (SB + F / 8) cs lo hi wlo whi 4 1%N (SLit 0) 0 HRS
    ltac:(rewrite E88; apply unsigned_lit_small; unfold SB; clear - HF8lo HF8hi; lia)
    ltac:(cbn; tauto) ltac:(reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Vz end.
  pose proof (Vz 0%nat ltac:(lia)) as Vz0. cbn [Z.of_nat] in Vz0. rewrite Z.add_0_r in Vz0.
  unfold aview. rewrite <- SB_SHADOW_OFF, Vz0. reflexivity. }
clear HRS.
destruct (pin_cat_site tfibsegs B lyN SN WN (ms_mem msC) (ms_regs msC) own fpos F Hfin (EFA 0 fpos) HF8m HF4096 HFceil
  ltac:(rewrite Esp; unfold T_leaf_STK; clear - Hsp1 Hceil Hslo HspLo C1; lia) Hsh0)
  as (Hc0 & Hc8 & Hcin & Hcid & Hcal & Hclo & Hchi & Hcst & Hcaf).
rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
change (Z_to_bv 64 528252) with (w64 528252).
eapply SRr_bind.
{ eapply (CATALOGUE STK sp0 FP ly S W0 mem0 md0 ((0, fpos) :: own) lyN SN WN (ms_mem msC) _ k (ms_regs msC)
    (pin_ch lyN regs ch) (F + 32) 0 fpos).
  - split; [exact HJ2|]. split; [rewrite Rra; apply ret_ok_even; vm_compute; reflexivity|].
    split; [unfold raZ; rewrite Rra, unsigned_lit_small by lia; lia|].
    split; [rewrite Rgp, (AG 3%nat) by lia; rewrite (EE 3%nat 3%bv eq_refl); exact Hgp|].
    split; [rewrite Rtp, (AG 4%nat) by lia; rewrite (EE 4%nat 4%bv eq_refl); exact Htp|].
    split; [rewrite Esp, Es0; exact Hch1|].
    split; [rewrite Esp; exact Hsp1al16|].
    split; [rewrite Esp; unfold T_leaf_STK; clear - Hsp1 HspLo; lia|].
    split; [rewrite Esp; clear - Hsp1 HspHi; lia|].
    unfold EV_leaf, EV_parse in *. lia.
  - exact EF32.
  - exact Hc0.
  - exact Hc8.
  - exact Hcin.
  - exact Hcid.
  - exact Hcal.
  - exact Hclo.
  - exact Hchi.
  - exact Hcst.
  - exact Hcaf. }
cbv beta. intros W3 c3 Hwle3 (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & HP3 & Hfrs3 & HPerm3 & HIO3 & HMLE3 & Hmem3 & (Ha03 & Hcnt3)).
rewrite Rra.
rewrite Esp in Hmem3. unfold T_leaf_STK in Hmem3.
replace (k + EV_leaf) with k in HJ3 by (unfold EV_leaf; lia).
assert (Hfrs3' : frames S3 = (0, fpos) :: frames Sc) by (rewrite Hfrs3; exact Hfrs).
pose proof (Permutation_trans HPerm3 HPERM) as HPERM3.
pose proof (mle_station MT Sc SN S3 0 0 MTL HMLE HMLE3) as HMLE3c. rewrite Z.add_0_r in HMLE3c.
pose proof (same_io_trans _ _ _ HIO1 HIO3) as HIO.
pose proof (wle_trans _ _ _ _ HWLE Hwle3) as HWLE3.
assert (HlyF3 : ly_F ly3 = ly_F lyc) by (eapply pp_lyF; [exact HJ0 | exact HJ3]).
pose proof HJ3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HpresT3 & _).
(* the caller's memory after reac_box_catalogue: its window [sp1 - 16, sp1) and the count cell changed *)
assert (Hgr3 : forall a, alloc_ceiling <= a < 2 ^ 64 -> apresent (w_H WN) (ms_mem msC) a -> apresent (w_H W3) mem3 a).
{ intros a Ha Hp. destruct (Z_lt_le_dec a (sp1 - 16)) as [Hlo | Hlo]; [|destruct (Z_lt_le_dec a sp1) as [Hhi | Hhi]].
  - apply (p2_apresent_of_aview (w_H WN) (w_H W3) (ms_mem msC) mem3 a); [lia | | | exact Hp].
    + intros Hi. pose proof (tfib_segs_low a Hi). clear - Ha H C1 C5. lia.
    + apply Hmem3; [lia | lia | clear - Ha HFceil; lia].
  - apply HpresT3. clear - Hlo Hhi Hsp1 HspLo HspHi. lia.
  - apply (p2_apresent_of_aview (w_H WN) (w_H W3) (ms_mem msC) mem3 a); [lia | | | exact Hp].
    + intros Hi. pose proof (tfib_segs_low a Hi). clear - Ha H C1 C5. lia.
    + apply Hmem3; [lia | lia | clear - Ha HFceil; lia]. }
pose proof (pp_KE_step B LAWS lyc Sc W memc mdc lyN SN WN (ms_mem msN) mdN WN (ms_mem msC) W3 mem3 fpos F FL
  sa mo lb regs cidm posm cidl posl (fun a => (sp1 - 16 <= a < sp1) \/ (F + 32 <= a < F + 32 + 8)) HAR0 HARN Hfrs HPERM
  HlyF eq_refl eq_refl FFL ltac:(change T_parse_STK with 8400; lia) ltac:(lia) HOCF
  ltac:(intros a [Ha|Ha]; [left; change T_parse_STK with 8400; lia | right; right; left; lia]) HKE
  ltac:(intros a Ha Hn; apply Hmem3; [exact Ha | intros Hx; apply Hn; left; exact Hx | intros Hx; apply Hn; right; exact Hx])
  Hgr3) as HKE3.
clear HKE. rename HKE3 into HKE.
(* the flag pointer at F + 56, read before the call (region 75's chunk), kept by the callee *)
p2_region HS 75%nat HRF.
destruct (pz_frame0 B LAWS lyc lyN SN WN (ms_mem msN) mdN fpos HARN Hfin HlyF FFL)
  as (_ & _ & _ & _ & _ & _ & _ & HFL4096 & HFLce & _).
fold F FL in HFL4096, HFLce.
lazymatch type of HRF with region_ok _ _ _ (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region EC _ 75 F cs lo hi wlo whi 56 8%N (SOff 87 0) FL HRF
  ltac:(rewrite E75; apply unsigned_lit_small; clear - HF4096 HFceil C1; lia)
  ltac:(cbn; tauto) ltac:(rewrite sv_denot_SOff0; exact E87)
  ltac:(cbn; clear - HFL4096 HFLce C1; lia) ltac:(cbn; lia)) as VFL end.
clear HRF.
assert (VFL3 : val_mem tfibsegs (mrestrict (w_H W3) mem3) (F + 56) 8 FL).
{ apply (val_mem_kept tfibsegs (w_H WN) (w_H W3) (ms_mem msC) mem3 (F + 56) 8 FL); [|exact VFL].
  intros k0 Hk0. apply Hmem3; [clear - Hk0 HF4096 HFceil C1; lia | clear - Hk0 HFceil Hsp1 Hceil Hslo HspLo C1; lia | lia]. }
clear VFL.
(* the re-seat: the frame's shadow, the spills and the save area are kept; the frame is re-added below *)
reseatQ HS 440%nat HJ3 HP3 [0; 2; 3]%nat AG
  ltac:(idtac; ppKEPTO Hmem3 AG
    ltac:(idtac; pose proof HFhigh as Hh; unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hh;
          lazymatch goal with Ha : _ <= ?a < _ |- ~ (_ <= ?a < _) => clear - Ha Hh HF8hi HF8lo; lia end)
    ltac:(idtac; first [ apply HpresT3; lia ])) HE3.
lazymatch type of HE3 with ?Ev = havoc ?Eo _ _ =>
  assert (Ecat : ew Ev 444 = Z_to_bv 64 cat)
  by (rewrite HE3; change 444%nat with (440 + 4)%nat; rewrite (ew_havoc_new Eo 440 _ 4 (Z_to_bv 64 0)) by (cbn; lia);
      cbn [nth map CLOB]; rewrite Ha03; reflexivity) end.
clear HE3 Ha03.
(* the frame region again, with the count 11 at F + 0x20 (CA1.6) and the flag pointer at F + 56 *)
pose proof (proj1 HJ3) as HAR3.
assert (Hfin3 : In (0, fpos) (frames S3)) by (rewrite Hfrs3'; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ 0 fpos HAR3 Hfin3) as (_ & _ & HFpres3 & _).
rewrite (proj1 (pp_frame_addr_lyF ly3 lyc 0 fpos HlyF3)) in HFpres3. change (fs_frame_bytes 0) with 64 in HFpres3.
fold F in HFpres3.
(* the cut state PL lists the frame's shadow first and the frame second: take the shadow region out, add the frame,
   put the shadow region back in front *)
p2_region HS 88%nat HR88.
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
  let rs' := eval vm_compute in
    (List.filter (fun r => match YP09.r_base r with Some 88%nat => false | _ => true end) (ss_mem ssx)) in
  let HS3 := fresh "HS3" in
  pose proof (st_ok_submem tfibsegs Ex ssx msx rs' HS ltac:(cbn [ss_mem]; submem_to) ltac:(vm_compute; reflexivity)) as HS3;
  clear HS; rename HS3 into HS end.
norm_ss HS.
lazymatch type of HS with st_ok _ ?Ev ?ssv ?msv =>
let HS3 := fresh "HS3" in
pose proof (ast_ok_add_region tfibsegs Ev ssv msv
  (YP09.mkRegion (Some 75%nat) 0 64 0 64 [YP09.mkChunk 32 (CVal 8 (SLit 11)); YP09.mkChunk 56 (CVal 8 (SOff 87 0))])
  HS eq_refl) as HS3;
specialize (HS3 ltac:(
  unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
  rewrite E75, unsigned_lit_small by (clear - HF4096 HFceil C1; lia);
  split; [clear - HF4096; lia|]; split; [clear - HFceil C1; lia|];
  split; [intros oo Hoo; apply (apresent_writable tfibsegs); apply (proj1 (HFpres3 (F + oo) ltac:(clear - Hoo; lia)))|];
  apply Forall_cons; [apply (chunk_ok_val tfibsegs _ _ _ 32 8%N (SLit 11) 11); [reflexivity | cbn; lia | cbn; lia | exact Hcnt3] |];
  apply Forall_cons; [apply (chunk_ok_val tfibsegs _ _ _ 56 8%N (SOff 87 0) FL);
    [rewrite sv_denot_SOff0; exact E87 | cbn; clear - HFL4096 HFLce C1; lia | cbn; lia | exact VFL3] |];
  apply Forall_nil));
specialize (HS3 ltac:(
  lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy =>
    let ry2 := eval vm_compute in ry in let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry2 rs2) end;
  cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
  evalE AG; pose proof HFhigh as Hh; unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hh;
  assert (HF8u : F < 8 * (F / 8) + 8) by (pose proof (Z.mod_pos_bound F 8 ltac:(lia)); pose proof (Z.div_mod F 8 ltac:(lia)); lia);
  repeat split; try exact I;
  clear - Hh HF4096 HFceil HF8lo HF8hi HF8c HF8u Hsp1 Hceil Hslo HspLo HspHi C1; lia));
clear HS; rename HS3 into HS; norm_ss HS end.
lazymatch type of HR88 with region_ok _ _ _ ?r88 =>
lazymatch type of HS with st_ok _ ?Ev ?ssv ?msv =>
let HS3 := fresh "HS3" in
pose proof (ast_ok_add_region tfibsegs Ev ssv msv r88 HS eq_refl HR88) as HS3;
specialize (HS3 ltac:(
  lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy =>
    let ry2 := eval vm_compute in ry in let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry2 rs2) end;
  cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
  evalE AG; pose proof HFhigh as Hh; unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hh;
  assert (HF8u : F < 8 * (F / 8) + 8) by (pose proof (Z.mod_pos_bound F 8 ltac:(lia)); pose proof (Z.div_mod F 8 ltac:(lia)); lia);
  repeat split; try exact I;
  clear - Hh HF4096 HFceil HF8lo HF8hi HF8c HF8u Hsp1 Hceil Hslo HspLo HspHi C1; lia));
clear HS; rename HS3 into HS; norm_ss HS end end.
clear VFL3 Hcnt3 HFpres3 HR88.
assert (EFA3 : forall c p, frame_addr ly3 c p = frame_addr lyc c p)
  by (intros c p; exact (proj1 (pp_frame_addr_lyF ly3 lyc c p HlyF3))).
(* 0x80c98 .. 0x80cbc: s3 = 11, a3 = -1, `beqz s3` not taken, s7 = cat, the spills of mo and lb, s6 = SB + cat/8, s8 = s7 *)
aj_run_to_sh tfibtbl_lib_ok HS HJ3 0x80cc0.
{ ppAWR AG fpos F EFA3 ltac:(fail). }
lazymatch type of HJ3 with ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mdx _ =>
  assert (HIO4 : same_io mdc mdx) by (eapply same_io_trans; [exact HIO | apply same_io_with_vm_backing]) end.
clear HIO. rename HIO4 into HIO.
lazymatch type of HFr with frame_of ?Ef ?rsf _ _ =>
assert (Hw3 : forall b0 wlo whi a, In (b0, wlo, whi) (windows rsf) ->
  base_val Ef b0 + wlo <= a < base_val Ef b0 + whi ->
  (fun a => (spZ regs - 176 <= a < spZ regs) \/ pp_nf F FL a) a)
by (intros b0 wlo whi a Hin Ha;
  lazymatch type of Hin with In _ ?l => let l' := eval vm_compute in l in change (In (b0, wlo, whi) l') in Hin end;
  cbn [In] in Hin;
  repeat (destruct Hin as [Hq | Hin];
    [injection Hq as <- <- <-; cbn [base_val] in Ha; revert Ha; evalE AG; intros Ha; cbv beta; unfold pp_nf, SHADOW_OFF; lia |]);
  destruct Hin) end.
lazymatch type of HG with mem_grows (mrestrict _ ?mA) (mrestrict _ ?mB) =>
pose proof (pp_KE_step B LAWS lyc Sc W memc mdc lyN SN WN (ms_mem msN) mdN W3 mA W3 mB fpos F FL
  sa mo lb regs cidm posm cidl posl (fun a => (spZ regs - 176 <= a < spZ regs) \/ pp_nf F FL a) HAR0 HARN Hfrs HPERM
  HlyF eq_refl eq_refl FFL ltac:(change T_parse_STK with 8400; lia) ltac:(lia) HOCF
  ltac:(intros a [Ha|Ha]; [left; change T_parse_STK with 8400; lia | right; right; exact Ha]) HKE
  (kept_of_frame _ _ _ _ _ _ HFr Hw3) (fun a _ Ha => apresent_grows _ _ _ a HG Ha)) as HKE4 end.
clear HKE Hw3 HF HFr HG. rename HKE4 into HKE.
(* the join into PL at row 0: toklen (100), the row address cat (102), the rows left 11 (103) *)
assert (Hcat47 : 0 < cat /\ cat mod 8 = 0 /\ cat <= 2 ^ 47 - 16).
{ destruct Hcat as (H1 & H2 & _ & H4 & _). split; [exact H1|]. split; [exact H2|].
  unfold amem_range, CAT_BYTES in H4. rewrite C3, C4, C5 in H4. lia. }
assert (Htl32 : Z.of_nat (colon_idx s) <= 2 ^ 32 - 1).
{ pose proof (colon_idx_le s). pose proof HSTR as (_ & _ & _ & Hl32 & _). lia. }
ra_join_win HS ss_PL PW_PL pp_deads_PL_bv ltac:(idtac;
  add_atom_win HS 100%nat (Z_to_bv 64 (Z.of_nat (colon_idx s))) E100;
  pin_by HS (25%bv : bv 5) (SOff 100 0)
    ltac:(rewrite !sv_denot_SOff0, E100;
          rewrite (ew_havoc_above _ 100%nat _ 404%nat) by (cbn; lia); rewrite (ew_havoc_above _ PW_PL _ 404%nat) by (unfold PW_PL; cbn; lia);
          rewrite Etl; reflexivity);
  add_atom_win HS 102%nat (Z_to_bv 64 (row_addr cat 0)) E102;
  pin_by HS (23%bv : bv 5) (SOff 102 0)
    ltac:(rewrite !sv_denot_SOff0, E102;
          rewrite (ew_havoc_above _ 102%nat _ 444%nat) by (cbn; lia); rewrite (ew_havoc_above _ 100%nat _ 444%nat) by (cbn; lia); rewrite (ew_havoc_above _ PW_PL _ 444%nat) by (unfold PW_PL; cbn; lia); rewrite Ecat;
          unfold row_addr; f_equal; lia);
  pin_by HS (24%bv : bv 5) (SOff 102 0)
    ltac:(rewrite !sv_denot_SOff0, E102;
          rewrite (ew_havoc_above _ 102%nat _ 444%nat) by (cbn; lia); rewrite (ew_havoc_above _ 100%nat _ 444%nat) by (cbn; lia); rewrite (ew_havoc_above _ PW_PL _ 444%nat) by (unfold PW_PL; cbn; lia); rewrite Ecat;
          unfold row_addr; f_equal; lia);
  pin_by HS (22%bv : bv 5) pp_s6row
    ltac:(unfold pp_s6row, PN_row; cbn [sv_denot]; rewrite E102;
          rewrite (ew_havoc_above _ 102%nat _ 444%nat) by (cbn; lia); rewrite (ew_havoc_above _ 100%nat _ 444%nat) by (cbn; lia); rewrite (ew_havoc_above _ PW_PL _ 444%nat) by (unfold PW_PL; cbn; lia); rewrite Ecat;
          replace (row_addr cat 0) with cat by (unfold row_addr; lia); reflexivity);
  add_atom_win HS 103%nat (Z_to_bv 64 11) E103;
  pin_by HS (19%bv : bv 5) (SOff 103 0) ltac:(rewrite sv_denot_SOff0, E103; reflexivity);
  add_fact HS 102%nat (mkAF 0 (2 ^ 47 - 16) 3)
    ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite (ew_havoc_old _ 103%nat _ 102%nat) by (cbn; lia); rewrite E102;
          rewrite unsigned_lit_small by (unfold row_addr; lia); unfold row_addr; change (2 ^ 3) with 8;
          replace (cat + CAT_ROW * Z.of_nat 0) with cat by lia; lia);
  add_fact HS 100%nat (mkAF 0 (2 ^ 32 - 1) 0)
    ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2];
          rewrite (ew_havoc_old _ 103%nat _ 100%nat) by (cbn; lia); rewrite (ew_havoc_old _ 102%nat _ 100%nat) by (cbn; lia); rewrite E100;
          rewrite unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia);
  add_fact HS 103%nat (mkAF 1 11 0)
    ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E103;
          rewrite unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia)).
unfold PW_PL in HS, E100, E102, E103.
pp_hand RL HS.
split; [exact HLV|]. split; [exact Hsnil|]. split; [unfold CAT_N; lia|].
split.
{ unfold PN_tl. rewrite (ew_havoc_old _ 103%nat _ 100%nat) by (cbn; lia).
  rewrite (ew_havoc_old _ 102%nat _ 100%nat) by (cbn; lia). exact E100. }
split.
{ unfold PN_row. rewrite (ew_havoc_old _ 103%nat _ 102%nat) by (cbn; lia). exact E102. }
split.
{ unfold PN_cnt. rewrite E103. reflexivity. }
intros j Hj. exfalso. lia.
Qed.
End w.

Print Assumptions pp_seg2.
Print Assumptions pin_strncmp_site.
Print Assumptions pin_strcspn_site.
Print Assumptions pin_cat_site.
Print Assumptions pp_spec_now.
