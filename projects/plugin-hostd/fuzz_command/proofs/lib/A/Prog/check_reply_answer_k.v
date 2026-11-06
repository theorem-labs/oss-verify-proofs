(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the kit of check_reply_answer's ASan walk (plugin-hostd/fuzz_command), in the form of proofs/cgif/cgif_file_fuzzer/lib/A/AChc.v (the walk's kit: regions, facts, register files, seed lemma cl_seed) over fuzz_command's listing (lib/A/Prog/CmdList.v). *)
(* The pieces of the walk that are not the run itself: the call rule of a runtime string entry in the journal form
   the walk uses (acall_rule, the conclusion of PaArt.v's aj_art_at with the entry's premise and post as parameters,
   for an entry stated in the form of lib/A/Rt/RtDefs.v's ecall_pre_stk / art_post), the facts the walk takes from
   the recorder representation, the symbolic entry state and its seed lemma. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04 YI00 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaDenot PaSB PaCall.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtString RtAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv CommandModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo
  CmdAddr CmdZsh PaArt PaNoChain sup_reply_code_c check_reply_answer_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Lemma val_mem_of_aval : forall segs H (mem : word -> option byte) a n v,
aval_mem (aview segs H mem) a n v -> val_mem segs (mrestrict H mem) a n v.
Proof.
intros segs H mem a n v Hv k Hk. specialize (Hv k Hk). unfold aview in Hv.
destruct (mbyte segs (mrestrict H mem) (a + Z.of_nat k)) as [b|] eqn:Eb; [|discriminate].
cbn in Hv. injection Hv as Hv. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned.
try unfold YG0f.le_byte in *; try unfold YO0f.le_byte in *. rewrite <- Hv.
symmetry. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.
Lemma aval_mem_ext : forall (rd rd' : reader) a n v,
(forall k, 0 <= k < Z.of_nat n -> rd' (a + k) = rd (a + k)) -> aval_mem rd a n v -> aval_mem rd' a n v.
Proof. intros rd rd' a n v Hk H k Hkn. rewrite Hk by lia. exact (H k Hkn). Qed.
Lemma abytes_atR_ext : forall (rd rd' : reader) a l,
(forall k, 0 <= k < Z.of_nat (length l) -> rd' (a + k) = rd (a + k)) -> abytes_atR rd a l -> abytes_atR rd' a l.
Proof. intros rd rd' a l Hk H i Hi. rewrite Hk by lia. exact (H i Hi). Qed.
Lemma astr_atR_ext : forall (rd rd' : reader) a s,
(forall k, 0 <= k <= Z.of_nat (length s) -> rd' (a + k) = rd (a + k)) -> astr_atR rd a s -> astr_atR rd' a s.
Proof.
intros rd rd' a s Hk [H1 H2]. split; [|exact H2]. apply (abytes_atR_ext rd); [|exact H1].
intros k Hkk. rewrite length_app in Hkk. cbn in Hkk. apply Hk. lia.
Qed.
Lemma abytes_atR_ext_lo : forall (rd rd' : reader) a l, (forall k, 0 <= k < 0x100000 -> rd' k = rd k) ->
0 <= a -> a + Z.of_nat (length l) <= 0x100000 -> abytes_atR rd a l -> abytes_atR rd' a l.
Proof. intros rd rd' a l Hk Ha Hl H i Hi. rewrite Hk by lia. exact (H i Hi). Qed.
(* the image's read-only objects and the tails after the literals' terminators all lie below 0x100000 *)
Lemma cmd_ro_ok_ext : forall (rd rd' : reader), (forall k, 0 <= k < 0x100000 -> rd' k = rd k) ->
cmd_ro_ok rd -> cmd_ro_ok rd'.
Proof.
intros rd rd' Hag [Hb Ht]. split.
- unfold cmd_ro_bytes in *. repeat match goal with H : _ /\ _ |- _ => destruct H end.
  repeat split; (apply (abytes_atR_ext_lo rd rd' _ _ Hag); [lia | apply Z.leb_le; vm_compute; reflexivity | assumption]).
- unfold cmd_ro_tails in *. intros e He a Ha.
  assert (Hall : forallb (fun e => (0 <=? e) && (e + 8 <=? 0x100000)) cmd_ro_ends = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in Hall. specialize (Hall e He). apply andb_true_iff in Hall as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2. pose proof (Z.mod_pos_bound e 8 ltac:(lia)).
  rewrite Hag by lia. exact (Ht e He a Ha).
Qed.
Lemma aval_mem_mod64 : forall (rd : reader) a v, aval_mem rd a 8 v -> aval_mem rd a 8 (v mod 2 ^ 64).
Proof.
intros rd a v H k Hk. rewrite (H k Hk). f_equal.
try unfold YG0f.le_byte; try unfold YO0f.le_byte. change (8 * Z.of_nat 8) with 64. rewrite Zmod_mod. reflexivity.
Qed.
Lemma branch_lt_S : forall E a b, branch_taken BC_LT (sv_denot E a) (sv_denot E b) = (Sg E a <? Sg E b).
Proof. intros E a b. reflexivity. Qed.
Lemma Sg_atom : forall E n z, ew E n = Z_to_bv 64 z -> - 2 ^ 63 <= z < 2 ^ 63 -> Sg E (SOff n 0) = z.
Proof.
intros E n z H Hz. rewrite S_SOff, H, Z.add_0_r. rewrite Z_to_bv_unsigned.
unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64). change (2 ^ 64 / 2) with (2 ^ 63).
rewrite <- Zplus_mod_idemp_l, Zmod_mod, Zplus_mod_idemp_l.
destruct (Z_lt_le_dec z 0).
- replace (z + 2 ^ 63) with ((z + 2 ^ 63)) by lia. rewrite Z.mod_small by lia. lia.
- rewrite Z.mod_small by lia. lia.
Qed.
Lemma swrap32_range : forall z, - 2 ^ 31 <= bv_swrap 32 z < 2 ^ 31.
Proof.
intros z. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32) with (2 ^ 32).
change (2 ^ 32 / 2) with (2 ^ 31). pose proof (Z.mod_pos_bound (z + 2 ^ 31) (2 ^ 32) ltac:(lia)). lia.
Qed.
Lemma reply_code_a_range : forall x, - 2 ^ 31 <= reply_code_a x < 2 ^ 31.
Proof.
intros x. unfold reply_code_a, atoi_a.
destruct (list_eq_dec Z.eq_dec _ _); [apply swrap32_range | lia].
Qed.
(* a 32-bit load of a word below 2^31, sign-extended (cgif lib/A/AChc.v cl_U_sext32, the small case) *)
Lemma U_sext32_small : forall E a r, U E a = r -> 0 <= r < 2 ^ 31 -> U E (SExt true 32 a) = r.
Proof.
intros E a r Ha Hr. rewrite U_SExt, Ha. change (2 ^ Z.of_N 32) with (2 ^ 32). rewrite (Z.mod_small r) by lia.
unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32) with (2 ^ 32). change (2 ^ 32 / 2) with (2 ^ 31).
rewrite (Z.mod_small (r + 2 ^ 31)) by lia. replace (r + 2 ^ 31 - 2 ^ 31) with r by lia. apply zcanon_id. unfold M64. lia.
Qed.
(* the two literals check_reply_answer hands to the string entries, from the read-only bytes *)
Lemma cmd_ro_lits : forall rd, cmd_ro_ok rd -> abytes_atR rd 0x210a0 RO_lit_210a0 /\ abytes_atR rd 0x21100 RO_lit_21100.
Proof.
intros rd [Hb _]. unfold cmd_ro_bytes in Hb. repeat match goal with H : _ /\ _ |- _ => destruct H end.
split; assumption.
Qed.
(* g_rec's GOT word (0xa7068), from the read-only bytes (CmdRo.v RO_ptr_a7068) *)
Lemma cra_got_of_ro : forall rd, cmd_ro_ok rd -> aval_mem rd 0xa7068 8 A_G_REC.
Proof.
intros rd [Hb _]. unfold cmd_ro_bytes in Hb. repeat match goal with H : _ /\ _ |- _ => destruct H end.
match goal with H : abytes_atR rd 0xa7068 RO_ptr_a7068 |- _ => rename H into Hg end.
intros k Hk. rewrite (Hg k ltac:(unfold RO_ptr_a7068; rewrite length_map; cbn [length]; lia)).
f_equal. do 8 (destruct k as [|k]; [vm_compute; reflexivity|]). lia.
Qed.

Section k. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section a.
Variable segs : list Segment.
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.

(* what a journal without footprint keeps, for the three kinds of memory the walk reads after a call *)
Lemma aj_heap_kept : forall STK sp0 ly S W mem md own lyc Sc Wc memc mdc k p n a,
ajournal segs B STK sp0 [] ly S W mem md own lyc Sc Wc memc mdc k ->
In (p, n) (ablocks B ly S) -> In (p, n) (ablocks B lyc Sc) -> p <= a < p + req_size n ->
aview segs (w_H Wc) memc a = aview segs (w_H W) mem a.
Proof.
intros STK sp0 ly S W mem md own lyc Sc Wc memc mdc k p n a HJ H1 H2 Ha.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
replace a with (p + (a - p)) by lia. apply (F2 p n (a - p)); [exact H1 | exact H2 | lia | apply inFP_nil].
Qed.
Lemma aj_stack_kept : forall STK sp0 ly S W mem md own lyc Sc Wc memc mdc k a,
ajournal segs B STK sp0 [] ly S W mem md own lyc Sc Wc memc mdc k ->
alloc_ceiling <= a < 2 ^ 64 -> ~ (sp0 - STK <= a < sp0) ->
aview segs (w_H Wc) memc a = aview segs (w_H W) mem a.
Proof.
intros STK sp0 ly S W mem md own lyc Sc Wc memc mdc k a HJ Ha Hn.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _).
apply F1; [exact Ha | exact Hn | apply inFP_nil].
Qed.
Lemma aj_img_kept : forall STK sp0 ly S W mem md own lyc Sc Wc memc mdc k a,
ajournal segs B STK sp0 [] ly S W mem md own lyc Sc Wc memc mdc k ->
in_img segs a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
aview segs (w_H Wc) memc a = aview segs (w_H W) mem a.
Proof.
intros STK sp0 ly S W mem md own lyc Sc Wc memc mdc k a HJ Hi Ho He.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
apply F3; [exact Hi | exact Ho | exact He |].
apply fp_spares_closed; [intros (r & Hr & _); destruct Hr | apply inFP_nil].
Qed.
Lemma arodata_keep : forall rlo rhi STK sp0 ly S W mem md own lyc Sc Wc memc mdc k,
(forall a, rlo <= a < rhi -> in_img segs a) ->
ajournal segs B STK sp0 [] ly S W mem md own lyc Sc Wc memc mdc k ->
arodata_okP segs rlo rhi B (aview segs (w_H W) mem) -> arodata_okP segs rlo rhi B (aview segs (w_H Wc) memc).
Proof.
intros rlo rhi STK sp0 ly S W mem md own lyc Sc Wc memc mdc k Hrel HJ HR a Hro Ho He.
rewrite (aj_img_kept STK sp0 ly S W mem md own lyc Sc Wc memc mdc k a HJ); [exact (HR a Hro Ho He) | | exact Ho | exact He].
destruct Hro as [(s & Hs & _ & Hr) | Hgot]; [exists s; split; [exact Hs | exact Hr]|]. exact (Hrel a Hgot).
Qed.

(* the caller's real stack is at zero shadow (AR's zshadow_ok on [ly_stk_lo, ly_stk_hi)), cgif's vf_stack_shadow
   (lib/A/AE3h.v:169-190) *)
Lemma stack_addressable : forall ly S W mem md a n,
AR segs B ly S W mem md -> ly_stk_lo ly <= a -> a + n <= ly_stk_hi ly -> 0 <= n ->
range_addressable (aview segs (w_H W) mem) SHADOW_OFF a n.
Proof.
intros ly S W mem md a n HAR Hlo Hhi Hn.
pose proof (am_layout B ly S _ (proj1 HAR)) as HLY.
pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & Lplo & Lphi & Lbeg). unfold page_aligned in Lplo, Lphi.
pose proof (al_zshadow _ _ LAWS ly S W mem md (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly) HAR ltac:(left; reflexivity)) as Hz.
cbn [fst snd] in Hz. unfold zero_shadow in Hz.
intros y Hy. exists 0. split; [|left; reflexivity].
replace (shadow_of_addr SHADOW_OFF y) with (shadow_of_addr SHADOW_OFF (ly_stk_lo ly) + (y / 8 - ly_stk_lo ly / 8))
by (unfold shadow_of_addr; lia).
apply Hz. clear - Hy Lplo Lphi Hlo Hhi Hn. Z.div_mod_to_equations. lia.
Qed.
(* a region kept by a step that changes no byte of it and leaves its writable window present (YCbq.v
   region_kept_stack_sub's two halves, from the step's own facts) *)
Lemma region_kept_win : forall E H (m m2 : word -> option byte) n b lo hi wlo whi cs,
bv_unsigned (ew E n) = b ->
(forall a, b + lo <= a < b + hi -> aview segs H m2 a = aview segs H m a) ->
(forall a, b + wlo <= a < b + whi -> apresent H m2 a) ->
region_kept segs E (mrestrict H m) (mrestrict H m2) (YP09.mkRegion (Some n) lo hi wlo whi cs).
Proof.
intros E H m m2 n b lo hi wlo whi cs Hn Hav Hp.
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Hn; intros a Ha.
- apply (mbyte_of_aview segs). apply Hav. exact Ha.
- intros _. apply (apresent_writable segs). apply Hp. exact Ha.
Qed.
(* a shorter read at the same start has a smaller shadow hull *)
Lemma shadow_hull_vis_le : forall (rd : reader) x n n', 0 <= x -> 0 < n' <= n -> shadow_hull_vis rd x n -> shadow_hull_vis rd x n'.
Proof.
intros rd x n n' Hx Hn H s Hs. apply H.
pose proof (shadow_mono (x + n' - 1) (x + n - 1) ltac:(lia)).
assert (R8 : forall u v, u <= v -> u / 8 * 8 <= v / 8 * 8) by (intros u v Huv; apply Z.mul_le_mono_nonneg_r; [lia|]; apply Z.div_le_mono; lia).
pose proof (R8 _ _ H0). lia.
Qed.
(* a literal of .rodata as a runtime entry reads it: its bytes readable, its shadow addressable and visible *)
Lemma lit_aread : forall W mem (regs : bvmap 5 word) stk x n,
0x21000 <= x -> x + n <= 0x22000 -> 0 < n ->
range_addressable (aview segs (w_H W) mem) SHADOW_OFF x n -> shadow_hull_vis (aview segs (w_H W) mem) x n ->
(forall i, 0 <= i < n -> aview segs (w_H W) mem (x + i) <> None) ->
alloc_ceiling <= spZ regs - stk ->
aread_ok segs stk W regs mem x n.
Proof.
intros W mem regs stk x n Hx Hn Hn0 HRA HHV Hrd Hsc.
pose proof asan_consts as (C1 & _).
split; [lia|]. split; [lia|]. split; [lia|].
split; [intros a Ha; split; [replace a with (x + (a - x)) by lia; apply Hrd; lia | unfold ascratch_stk; lia]|].
split; [apply amem_range_high; lia|]. split; [exact HRA | intros _; exact HHV].
Qed.
End a.

(* The symbolic state of the walk (cgif lib/A/AChc.v:39-63 in this function's shape). Atoms: 0..31 the registers at
   entry; 32 the shadow base SB; 33 g_rec.answer; 34 g_rec.reply; 35 w->w; 36 w->n; 37 w->w[0] (the extras, in this
   order); A_OBJ i the listing's objects (A_OBJ 0 the shadow-base GOT word, A_OBJ 2 g_rec's GOT word, A_OBJ 12 the
   shadow-base cell, A_OBJ 44 g_rec). *)
Definition CRA_WLO : Z := 0x7fff7f800000.
Definition CRA_WHI : Z := 2 ^ 47 - 32.
Definition Bxc : sv := SOff 32 0.
Definition RBspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition cra_grec_got : YP09.region :=
YP09.mkRegion (Some (A_OBJ 2)) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff (A_OBJ 44) 0))].
Definition cra_grec : YP09.region :=
YP09.mkRegion (Some (A_OBJ 44)) 912 936 0 0 [YP09.mkChunk 912 (CVal 8 (SOff 33 0)); YP09.mkChunk 928 (CVal 8 (SOff 34 0))].
Definition cra_regions : smem := [stack_region 32; got_regionP; bcell_regionP 32; cra_grec_got; cra_grec].
Definition cra_facts : facts :=
mkFacts [(2%nat, mkAF (2^46) (2^47) 4); (10%nat, mkAF CRA_WLO CRA_WHI 3); (32%nat, mkAF SB SB 0);
(A_OBJ 44, mkAF A_G_REC A_G_REC 3)] [] [].
Definition ss_cra : sstate := mkSS AF_check_reply_answer sr_atoms cra_regions None cra_facts.
Definition cra_extra (ansv repv wwv nv p0v : Z) : list word := map (Z_to_bv 64) [SB; ansv; repv; wwv; nv; p0v].
(* the caller's struct words (w->w, w->n) and the first slot of its word array, added after the sup_reply_code call *)
Definition cra_words : YP09.region :=
YP09.mkRegion (Some 10%nat) 16 28 0 0 [YP09.mkChunk 16 (CVal 8 (SOff 35 0)); YP09.mkChunk 24 (CVal 4 (SOff 36 0))].
Definition cra_warr : YP09.region := YP09.mkRegion (Some 35%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 37 0))].

Section p.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Variable B : asyms.
Variables RLO RHI : Z.

(* The call of a runtime entry at pc with window stk, entry premise P and post Q, in the journal form a walk applies
   (YCbq.v aj_bcmp_at's conclusion). arodata_okP at the call is the fact the entry's read-only view comes from. *)
Definition acall_rule (pc stk : Z) (P : world SEGS -> bvmap 5 word -> (word -> option byte) -> Prop)
(Q : bvmap 5 word -> (word -> option byte) -> Prop) : Prop :=
forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k (o : Z) raw,
ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
arodata_okP SEGS RLO RHI B (rdW W memT) ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> stk - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
P W regsT memT ->
SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom SEGS)) mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
 c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
 ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\
 aregs_preserved regsT regs2 /\ Q regs2 mem2 /\
 (forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + o - stk <= a < sp0 + o) -> rdW W mem2 a = rdW W memT a)).
(* the premises of the strcmp, strcspn and strncmp entries (lib/A/Rt/RtString.v:108-173), without the
   read-only view; strcspn and strncmp also take the `+ 8` band room past each string (RtString.v:128, :131, :165,
   :168), in the contract's order *)
Definition P_strcmp (x y : Z) (sx sy : list byte) (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte) : Prop :=
getr regs 10 = w64 x /\ getr regs 11 = w64 y /\ 0 < x /\ 0 < y /\
astr_at SEGS W mem x sx /\ astr_at SEGS W mem y sy /\
aread_ok SEGS (2 * ESTACK) W regs mem x (astr_len sx + 1) /\ aread_ok SEGS (2 * ESTACK) W regs mem y (astr_len sy + 1) /\
atail_vis SEGS W mem (x + astr_len sx) /\ atail_vis SEGS W mem (y + astr_len sy).
Definition P_strcspn (x y : Z) (str set : list byte) (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte) : Prop :=
aguard_ok SEGS W mem A_SSP_GOT A_SSP_GUARD /\
getr regs 10 = w64 x /\ getr regs 11 = w64 y /\ 0 < x /\ 0 < y /\
astr_at SEGS W mem x str /\ astr_at SEGS W mem y set /\
aread_ok SEGS (2 * ESTACK) W regs mem x (astr_len str + 1) /\ amem_range x (astr_len str + 8) /\
aread_ok SEGS (2 * ESTACK) W regs mem y (astr_len set + 1) /\ amem_range y (astr_len set + 8) /\
atail_vis SEGS W mem (x + astr_len str) /\ atail_vis SEGS W mem (y + astr_len set).
Definition P_strncmp (x y n : Z) (sx sy : list byte) (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte) : Prop :=
getr regs 10 = w64 x /\ getr regs 11 = w64 y /\ getr regs 12 = w64 n /\ 0 <= n < 2 ^ 32 /\ 0 < x /\ 0 < y /\
astr_at SEGS W mem x sx /\ astr_at SEGS W mem y sy /\
aread_ok SEGS (2 * ESTACK) W regs mem x (Z.min n (astr_len sx + 1)) /\ amem_range x (astr_len sx + 8) /\
aread_ok SEGS (2 * ESTACK) W regs mem y (Z.min n (astr_len sy + 1)) /\ amem_range y (astr_len sy + 8) /\
atail_vis SEGS W mem (x + astr_len sx) /\ atail_vis SEGS W mem (y + astr_len sy).
Definition CALL_STRCMP : Prop := forall x y sx sy,
acall_rule (SIGMA CS___interceptor_trampoline_strcmp) (2 * ESTACK) (P_strcmp x y sx sy)
(fun regs' _ => getr regs' 10 = w64 0 <-> sx = sy).
Definition CALL_STRCSPN : Prop := forall x y str set,
acall_rule (SIGMA CS___interceptor_trampoline_strcspn) (2 * ESTACK) (P_strcspn x y str set)
(fun regs' _ => getr regs' 10 = w64 (Z.of_nat (PCspn.cspn_len set str))).
Definition CALL_STRNCMP : Prop := forall x y n sx sy,
acall_rule (SIGMA CS___interceptor_trampoline_strncmp) (2 * ESTACK) (P_strncmp x y n sx sy)
(fun regs' _ => getr regs' 10 = w64 0 <-> PStrFun.strncmp_model (sx ++ [Z_to_bv 8 0]) (sy ++ [Z_to_bv 8 0]) n = Some 0).

Section q.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL.

(* the read-only view a runtime entry asks (RtDefs.v rt_rom_view: every unowned byte of a read-only segment reads
   as the image has it) is the in-segment half of arodata_okP *)
Lemma rt_rom_view_of_aro : forall (W : world SEGS) mem, arodata_okP SEGS RLO RHI B (rdW W mem) -> rt_rom_view SEGS B W mem.
Proof. intros W mem HR a Hrom Ho He. apply HR; [left; exact Hrom | exact Ho | exact He]. Qed.
Lemma acall_of_art : forall pc stk P Q, ESTACK <= stk ->
(forall ly S W regs mem md, ecall_pre_stk SEGS B stk ly S W regs mem md -> P W regs mem -> rt_rom_view SEGS B W mem ->
 SRr SEGS W (cfg_at SEGS pc regs mem md) (art_post SEGS B stk ly S W regs mem md (fun _ => False) Q)) ->
acall_rule pc stk P Q.
Proof.
intros pc stk P Q Hes AE W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k o raw HJ HRO Hsp Hal Hneg Hbud Hgp Htp Hra Hraw HP.
assert (HPS : ecall_pre_stk SEGS B stk lyc Sc W regsT memT mdc)
by (apply (ecall_pre_stk_at SEGS B stk STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k regsT o HJ Hsp Hal Hneg Hes Hbud);
    [rewrite Hra; exact Hraw | exact Hgp | exact Htp]).
assert (Hst : 0 <= stk) by (unfold ESTACK in Hes; lia).
eapply SRr_mono.
{ exact (aj_art_at SEGS B LAWS pa_segs_low (pal_env B TL) stk (fun _ => False) pc W regsT memT STK sp0 FP ly S W0 mem md own
  lyc Sc mdc k o raw Q HJ Hsp Hal Hneg Hst Hbud Hra (fun a (H : False) => match H with end)
  (AE lyc Sc W regsT memT mdc HPS HP (rt_rom_view_of_aro W memT HRO))). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & HQ & HK).
split; [reflexivity|]. exists regs2, mem2, md2. split; [reflexivity|]. split; [exact HJ2|]. split; [exact HP2|].
split; [exact HQ|]. intros a Ha Hn. exact (HK a Ha Hn (fun H => H)).
Qed.
Lemma call_strcmp_of : astrcmp_realizes SEGS B (SIGMA CS___interceptor_trampoline_strcmp) -> CALL_STRCMP.
Proof.
intros AS x y sx sy. apply acall_of_art; [unfold ESTACK; lia|].
intros ly S W regs mem md HPS (H10 & H11 & Hx & Hy & Hsx & Hsy & Rx & Ry & Tx & Ty) HRV.
exact (AS ly S W regs mem md x y sx sy HPS H10 H11 Hx Hy Hsx Hsy Rx Ry Tx Ty HRV).
Qed.
Lemma call_strcspn_of : astrcspn_realizes SEGS B (SIGMA CS___interceptor_trampoline_strcspn) A_SSP_GOT A_SSP_GUARD ->
CALL_STRCSPN.
Proof.
intros AS x y str set. apply acall_of_art; [unfold ESTACK; lia|].
intros ly S W regs mem md HPS (Hg & H10 & H11 & Hx & Hy & Hsx & Hsy & Rx & Mx & Ry & My & Tx & Ty) HRV.
exact (AS ly S W regs mem md x y str set Hg HPS H10 H11 Hx Hy Hsx Hsy Rx Mx Ry My Tx Ty HRV).
Qed.
Lemma call_strncmp_of : astrncmp_realizes SEGS B (SIGMA CS___interceptor_trampoline_strncmp) -> CALL_STRNCMP.
Proof.
intros AS x y n sx sy. apply acall_of_art; [unfold ESTACK; lia|].
intros ly S W regs mem md HPS (H10 & H11 & H12 & Hn & Hx & Hy & Hsx & Hsy & Rx & Mx & Ry & My & Tx & Ty) HRV.
exact (AS ly S W regs mem md x y n sx sy HPS H10 H11 H12 Hn Hx Hy Hsx Hsy Rx Mx Ry My Tx Ty HRV).
Qed.

(* what the walk takes from the recorder representation (CmdRep.v rec_repA, areply_at / aanswer_at) *)
Lemma cra_rec : forall ly S W mem md R O xr,
AR SEGS B ly S W mem md -> rec_repA B ly S (rdW W mem) R O -> r_reply R = Some (xr ++ [Z_to_bv 8 0]) -> no0 xr ->
(exists repv nr, aval_mem (rdW W mem) (A_G_REC + OFF_REPLY) 8 repv /\ In (repv, nr) (ablocks B ly S) /\
   Z.of_nat (length xr) + 1 <= nr /\ astr_atR (rdW W mem) repv xr /\ 4096 <= repv /\ repv + nr <= alloc_ceiling) /\
(exists ansv, aval_mem (rdW W mem) (A_G_REC + OFF_ANSWER) 8 ansv /\ 0 <= ansv < 2 ^ 64 /\
   (r_answer R = None -> ansv = 0) /\
   (forall xa, r_answer R = Some xa -> exists na, In (ansv, na) (ablocks B ly S) /\ Z.of_nat (length xa) + 1 <= na /\
      astr_atR (rdW W mem) ansv xa /\ 4096 <= ansv /\ ansv + na <= alloc_ceiling)).
Proof.
intros ly S W mem md R O xr HAR (Q & (Hgr & Hsc & Hap & Hcalls & Hans & Hrep & Hsca & Hown) & HO) Hry Hno0.
pose proof asan_consts as (C1 & _).
split.
- unfold areply_at in Hrep. rewrite Hry in Hrep. destruct (l_reply Q) as [[rp rn]|]; [|destruct Hrep].
  destruct Hrep as (V & _ & _ & _ & Hin & Hsz & Hb & _). cbn [fst snd] in *.
  rewrite length_app in Hsz. cbn [length] in Hsz.
  destruct (al_blocks _ _ LAWS ly S W mem md rp rn HAR Hin) as (_ & H4096 & Hceil & _).
  assert (Hrq : req_size rn = rn) by (unfold req_size; destruct (Z.eqb_spec rn 0); lia).
  exists rp, rn. split; [exact V|]. split; [exact Hin|]. split; [lia|]. split; [exact (conj Hb Hno0)|]. lia.
- unfold aanswer_at in Hans. destruct (r_answer R) as [xa|] eqn:Ea; destruct (l_answer Q) as [[ap an]|]; try contradiction.
  + destruct Hans as (V & _ & Hin & Hsz & Hb & _). cbn [fst snd] in *.
    destruct (al_blocks _ _ LAWS ly S W mem md ap an HAR Hin) as (_ & H4096 & Hceil & _).
    assert (Hrq : req_size an = an) by (unfold req_size; destruct (Z.eqb_spec an 0); lia).
    exists ap. split; [exact V|]. split; [lia|]. split; [discriminate|].
    intros xa' Hxa. injection Hxa as <-. exists an. split; [exact Hin|]. split; [lia|]. split; [exact Hb|]. lia.
  + exists 0. split; [exact Hans|]. split; [lia|]. split; [reflexivity|]. intros xa' Hxa. discriminate.
Qed.

Lemma cra_vals : cmd_val_objs -> VAL (A_OBJ 0) = 0xa63f0 /\ VAL (A_OBJ 2) = 0xa7068 /\ VAL (A_OBJ 12) = 0xb10b8 /\
VAL (A_OBJ 44) = A_G_REC /\ VAL (A_OBJ 5) = 0x210a0 /\ VAL (A_OBJ 28) = 0x21100.
Proof.
intros HV.
assert (G : forall i v, (i < length cmd_objs)%nat -> nth i cmd_objs 0 = v -> VAL (A_OBJ i) = v)
by (intros i v Hi Hv; rewrite (HV i Hi); exact Hv).
unfold A_G_REC. repeat split; apply G; vm_compute; first [reflexivity | lia].
Qed.

Lemma cra_entry : forall W ly S regs mem md w ansv repv wwv nv p0v,
afn_pre_na SEGS B CHECK_REPLY_ANSWER_STK ly S W regs mem md ->
cmd_val_objs -> cmd_ro_ok (rdW W mem) ->
getr regs 10 = w64 w -> w mod 8 = 0 -> spZ regs <= w -> w + 28 <= ly_stk_hi ly ->
aval_mem (rdW W mem) (A_G_REC + OFF_ANSWER) 8 ansv -> 0 <= ansv < 2 ^ 64 ->
aval_mem (rdW W mem) (A_G_REC + OFF_REPLY) 8 repv -> 0 <= repv < 2 ^ 64 ->
st_ok_pi SEGS VAL (Eimg (Ereg regs (cra_extra ansv repv wwv nv p0v))) ss_cra
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_check_reply_answer)) mem (seg_rom SEGS)))
/\ sh_ok SEGS Bxc [] (Eimg (Ereg regs (cra_extra ansv repv wwv nv p0v))) (mrestrict (w_H W) mem).
Proof.
intros W ly S regs mem md w ansv repv wwv nv p0v HPRE HV HROK H10 Hw8 Hwlo Hwhi Hans Hansr Hrep Hrepr.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (HSTK : CHECK_REPLY_ANSWER_STK = 12320) by reflexivity.
destruct (cra_vals HV) as (V0 & V2 & V12 & V44 & V5 & V28).
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & _ & Kgot & _). rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
rewrite V0, V12 in Kgot. rewrite V12 in Kcell.
pose proof (cra_got_of_ro _ HROK) as Ggrec.
assert (Hw47 : w + 32 <= 2 ^ 47) by (pose proof (Z.div_mod w 8 ltac:(lia)) as Hd; rewrite Hw8 in Hd; lia).
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs (cra_extra ansv repv wwv nv p0v))). pose proof pa_B_ok as HBASE.
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 w) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 ansv) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 repv) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E241 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E243 : ew E (A_OBJ 2) = Z_to_bv 64 (VAL (A_OBJ 2))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E253 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E285 : ew E (A_OBJ 44) = Z_to_bv 64 (VAL (A_OBJ 44))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
rewrite V0 in E241. rewrite V2 in E243. rewrite V12 in E253. rewrite V44 in E285.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
unfold A_G_REC in *.
split.
- unfold ss_cra. apply pa_entry_st_ok_full.
+ apply regs_ok_Eimg_Ereg.
+ vm_compute. reflexivity.
+ unfold cra_regions, stack_region, got_regionP, bcell_regionP, cra_grec_got, cra_grec.
repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
* cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
* rewrite (VB (A_OBJ 0) _ E241) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ 0xa63f0 0 8 (SOff (A_OBJ 12) 0) 0xb10b8);
[cbn [sv_denot]; rewrite E253, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
* rewrite (VB (A_OBJ 12) _ E253) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ 0xb10b8 0 8 (SOff 32 0) SB);
[cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
* rewrite (VB (A_OBJ 2) _ E243) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ 0xa7068 0 8 (SOff (A_OBJ 44) 0) 0x5e3740);
[cbn [sv_denot]; rewrite E285, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_aval SEGS (w_H W) mem _ _ _ Ggrec).
* rewrite (VB (A_OBJ 44) _ E285) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor; [|constructor]].
-- apply (chunk_ok_val SEGS E _ 0x5e3740 912 8 (SOff 33 0) ansv);
[cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
exact (val_mem_of_aval SEGS (w_H W) mem _ _ _ Hans).
-- apply (chunk_ok_val SEGS E _ 0x5e3740 928 8 (SOff 34 0) repv);
[cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
exact (val_mem_of_aval SEGS (w_H W) mem _ _ _ Hrep).
+ apply pairwise_disjoint_of_extents. unfold cra_regions, stack_region, got_regionP, bcell_regionP, cra_grec_got, cra_grec, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
rewrite (VB (A_OBJ 0) _ E241), (VB (A_OBJ 12) _ E253), (VB (A_OBJ 2) _ E243), (VB (A_OBJ 44) _ E285) by lia.
cbn [base_val]. rewrite Usp.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
revert Hslo Hshi H47 Hceil C1 HSTK Hstk0. clear. intros. unfold kLowMemEnd in *. repeat split; lia.
+ split; [|split; [exact I | exact I]].
cbn [cra_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite Usp, E10, E32, E285, !unsigned_lit_small by (unfold SB, CRA_WHI; lia).
change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
unfold CRA_WLO, CRA_WHI, SB.
revert Hslo Hshi H47 Hceil Hal16 C1 HSTK Hstk0 Hwlo Hwhi Hw47 Hw8. clear. unfold spZ. intros.
repeat match goal with |- _ /\ _ => split end; try lia; reflexivity.
- unfold sh_ok. constructor.
Qed.
End q.
End p.
End k.
