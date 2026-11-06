(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: segment 3 of the walk of chain_words (0x8dfd4) on the ASan build of
   plugin-hostd/fuzz_command (interface chain_words_d.v): one pass of the member loop, from the loop head KL
   (0x8e234) at pass j: the inline load8 check of &tok[2 + j] (0x8e234-0x8e238), the call of number at 0x8e244
   (through cl_callS_wide, PaNoChain.v) that writes ids[j] in this walk's class-3 side-stack frame, the refusal edge
   `beqz a0` at 0x8e248 (to KR, 0x8e278), the advance 0x8e24c-0x8e25c and `bnez s11` at 0x8e260, which re-enters
   KL at pass j + 1 or falls through to KD (0x8e264). The symbolic machinery (the cut-point seed, the call, the
   re-seat after it) is the one of the sibling segment chain_words_s2.v (KC -> KL 0), which walks the same inline
   check and the same call once, for the first word; its lemmas are copied here with the prefix cw3_ and generalised
   over the pass index. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI00 YI04 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YG0q YN01.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaCall PaDenot PaSB PaNoChain.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Verbs VerbsRun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
number_c sup_chain_c sup_resp_c chain_words_c chain_words_d.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* the return point of the call of number at 0x8e244 *)
Definition CW3_RET : Z := AF_chain_words + 0x274.

(* copied from chain_words_s2.v (cw2_val_mem, cw2_afact) *)
Lemma cw3_val_mem : forall segs H mem a n v,
aval_mem (aview segs H mem) a n v -> val_mem segs (mrestrict H mem) a n v.
Proof.
intros segs H mem a n v Hv k Hk. pose proof (Hv k Hk) as Hb. unfold aview in Hb.
unfold val_mem.
destruct (mbyte segs (mrestrict H mem) (a + Z.of_nat k)) as [b|] eqn:Eb;
  cbn [option_map] in Hb; [|discriminate Hb].
injection Hb as Hb. f_equal. apply bv_eq.
rewrite Z_to_bv_unsigned, Hb. unfold bv_wrap, bv_modulus. cbn [Z.of_N].
cbv [YO0f.le_byte YG0f.le_byte]. symmetry. apply Z.mod_mod. lia.
Qed.
Lemma cw3_afact : forall E m v lo hi al,
ew E m = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> lo <= v <= hi -> v mod 2 ^ al = 0 -> 0 <= al <= 64 ->
afact_ok E m (mkAF lo hi al).
Proof.
intros E m v lo hi al Hm Hv Hlh Hal Hal2. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite Hm, unsigned_lit_small by exact Hv. split; [exact Hlh | split; [exact Hal | exact Hal2]].
Qed.

(* the member words' values: numbers_m over an append, its length, a refused member *)
Lemma cw3_numbers_app : forall a b, Verbs.numbers_m (a ++ b) =
  match Verbs.numbers_m a, Verbs.numbers_m b with Some x, Some y => Some (x ++ y) | _, _ => None end.
Proof.
induction a as [|w a IH]; intros b; cbn [app Verbs.numbers_m].
- destruct (Verbs.numbers_m b); reflexivity.
- rewrite IH. destruct (Verbs.number_m w); destruct (Verbs.numbers_m a); destruct (Verbs.numbers_m b); reflexivity.
Qed.
Lemma cw3_numbers_len : forall ws vs, Verbs.numbers_m ws = Some vs -> length vs = length ws.
Proof.
induction ws as [|w ws IH]; intros vs H; cbn [Verbs.numbers_m] in H.
- injection H as <-. reflexivity.
- destruct (Verbs.number_m w) as [v|]; [|discriminate].
  destruct (Verbs.numbers_m ws) as [vs'|] eqn:E; [|discriminate].
  injection H as <-. cbn [length]. f_equal. exact (IH vs' eq_refl).
Qed.
Lemma cw3_numbers_none : forall l j w, nth_error l j = Some w -> Verbs.number_m w = None -> Verbs.numbers_m l = None.
Proof.
induction l as [|x l IH]; intros j w H Hw; [destruct j; discriminate|].
destruct j as [|j]; cbn [nth_error] in H; cbn [Verbs.numbers_m].
- injection H as ->. rewrite Hw. reflexivity.
- rewrite (IH j w H Hw). destruct (Verbs.number_m x); reflexivity.
Qed.
Lemma cw3_firstn_S : forall {A} (l : list A) n x, nth_error l n = Some x -> firstn (S n) l = firstn n l ++ [x].
Proof.
intros A l. induction l as [|y l IH]; intros n x H; [destruct n; discriminate|].
destruct n as [|n]; cbn [nth_error] in H.
- injection H as ->. reflexivity.
- cbn [firstn app]. rewrite (IH n x H). reflexivity.
Qed.
Lemma cw3_nth_skipn : forall {A} (l : list A) n i, nth_error (skipn n l) i = nth_error l (n + i).
Proof.
intros A l n. revert l. induction n as [|n IH]; intros l i; [reflexivity|].
destruct l as [|x l]; [destruct i; reflexivity|]. cbn [skipn]. rewrite IH. reflexivity.
Qed.
(* a refused member makes chain_words_m refuse: the recorder answers err_invalid_operation *)
Lemma cw3_chain_none : forall R tks j w, (3 <= length tks)%nat -> nth_error tks (2 + j) = Some w ->
  Verbs.number_m w = None -> VerbsRun.chain_run R (tl tks) = sup_resp_m R Verbs.err_invalid_operation.
Proof.
intros R tks j w Hl Hn Hw. destruct tks as [|t0 [|t1 [|t2 tks]]]; cbn [length] in Hl; try lia.
cbn [tl]. unfold VerbsRun.chain_run, Verbs.chain_words_m.
rewrite (cw3_numbers_none (t2 :: tks) j w Hn Hw).
destruct (Verbs.number_m t1); reflexivity.
Qed.
(* the 4 little-endian bytes number stores are le32 of the value *)
Lemma cw3_byte_mod : forall v s, 0 <= s -> s + 8 <= 32 ->
  (Z.shiftr (v mod 2 ^ 64) s) mod 256 = (Z.shiftr (v mod 2 ^ 32) s) mod 256.
Proof.
intros v s Hs Hs8. change 256 with (2 ^ 8). apply Z.bits_inj'. intros n Hn.
destruct (Z.lt_ge_cases n 8) as [Hl|Hg].
- rewrite !Z.mod_pow2_bits_low by lia. rewrite !Z.shiftr_spec by lia. rewrite !Z.mod_pow2_bits_low by lia. reflexivity.
- rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.
Lemma cw3_le32 : forall (rd : reader) a v, aval_mem rd a 4 v -> abytes_atR rd a (le32 v).
Proof.
intros rd a v H i Hi. unfold le32, OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib.Mem.le4 in Hi |- *.
rewrite length_Z_to_le_bytes in Hi.
rewrite (H i Hi). f_equal.
rewrite (nth_error_nth _ _ _ (YN01.nth_error_Z_to_le_bytes 4 _ i Hi)).
rewrite Z_to_bv_unsigned, unsigned_lit. unfold YG0f.le_byte, bv_wrap, bv_modulus, zcanon, M64.
change (2 ^ Z.of_N 8) with 256. change (8 * Z.of_nat 4) with 32.
symmetry. apply cw3_byte_mod; lia.
Qed.
Lemma cw3_abytes_app : forall (rd : reader) a l1 l2, abytes_atR rd a l1 ->
  abytes_atR rd (a + Z.of_nat (length l1)) l2 -> abytes_atR rd a (l1 ++ l2).
Proof.
intros rd a l1 l2 H1 H2 i Hi. rewrite length_app in Hi.
destruct (Nat.lt_ge_cases i (length l1)) as [Hl|Hg].
- rewrite app_nth1 by exact Hl. exact (H1 i Hl).
- rewrite app_nth2 by exact Hg.
  replace (a + Z.of_nat i) with (a + Z.of_nat (length l1) + Z.of_nat (i - length l1)) by lia.
  apply H2. lia.
Qed.
Lemma cw3_len_ids : forall vs, length (concat (map le32 vs)) = (4 * length vs)%nat.
Proof.
induction vs as [|x vs IH]; [reflexivity|]. cbn [map concat]. rewrite length_app, IH.
unfold le32, OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib.Mem.le4. rewrite length_Z_to_le_bytes.
cbn [length]. lia.
Qed.
Lemma cw3_abytes_ext : forall (rd rd' : reader) a l, abytes_atR rd a l ->
  (forall i, 0 <= i < Z.of_nat (length l) -> rd' (a + i) = rd (a + i)) -> abytes_atR rd' a l.
Proof. intros rd rd' a l H He i Hi. rewrite He by lia. exact (H i Hi). Qed.
Lemma cw3_aval_ext : forall (rd rd' : reader) a n v, aval_mem rd a n v ->
  (forall i, 0 <= i < Z.of_nat n -> rd' (a + i) = rd (a + i)) -> aval_mem rd' a n v.
Proof. intros rd rd' a n v H He k Hk. rewrite He by lia. exact (H k Hk). Qed.
(* the shadow address the loop keeps in s10 *)
Lemma cw3_shadow_denot : forall E n m x, ew E n = Z_to_bv 64 x -> ew E m = Z_to_bv 64 SB -> 0 <= x < 2 ^ 64 ->
  sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff n 0) (SLit 3)) (SOff m 0)) = Z_to_bv 64 (SB + x / 8).
Proof.
intros E n m x Hn Hm Hx. cbn [sv_denot]. rewrite Hn, Hm, !unsigned_lit_small by (unfold SB; lia). rewrite !Z.add_0_r.
rewrite !zalu64_sound. unfold zalu64. rewrite Z_to_bv64_canon. cbn [zalu_raw].
rewrite (zcanon_id x) by (unfold M64; lia). change (zcanon 3) with 3. change (Z.land 3 63) with 3.
rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
assert (Hx8 : 0 <= x / 8 < M64) by (unfold M64; split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
rewrite !(zcanon_id (x / 8) Hx8).
rewrite !(zcanon_id SB) by (unfold SB, M64; lia). f_equal. lia.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
(* app memory and the shadow of a side-stack frame are apart *)
Lemma cw3_app_shadow : forall x lo len g m i, in_app lo len -> lo <= x < lo + len ->
  4096 <= g -> g + m <= alloc_ceiling -> 0 <= i < m / 8 -> x <> shadow_addr g + i.
Proof.
intros x lo len g m i Happ Hx Hg Hgm Hi. pose proof asan_consts as (C1 & _).
unfold in_app, kLowShadowBeg, kHighMemBeg, shadow_addr, SHADOW_OFF in *.
assert (D : 0 <= g / 8 /\ g / 8 + i <= (g + m) / 8) by (split; [apply Z.div_pos; lia|]; Z.div_mod_to_equations; lia).
assert (D2 : (g + m) / 8 <= 0x7fffff800000 / 8) by (apply Z.div_le_mono; lia).
change (0x7fffff800000 / 8) with 0xffffff00000 in D2. lia.
Qed.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
(* RLO / RHI are the statement's fixed CMD_RLO / CMD_RHI, not variables: number asks arodata_okP at them
   (number_c.v:71-72, :87), so this segment is proved at them, as chain_words_s2.v is; chain_words_a.v takes
   cw_S3P at CMD_RLO CMD_RHI *)
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
Hypothesis NUMBER : forall fx0 : YK11.FPState, @tnumber_spec fx0 rc SK PI B MT.
Hypothesis TL : PALib B.
Hypothesis MTFL : ameter_fs_laws MT.
Hypothesis SIGP : cmd_sig_prog.
Hypothesis TRANSP : cw_transportP B MT RLO RHI.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

(* copied from chain_words_s2.v: cw2_frame_addr_le .. cw2_fi_ext *)
Lemma cw3_frame_addr_le : forall n ly ly' cid pos, layout_le n ly ly' -> frame_addr ly' cid pos = frame_addr ly cid pos.
Proof. intros n ly ly' cid pos (_ & _ & _ & _ & _ & EF & _). unfold frame_addr. rewrite EF. reflexivity. Qed.
Lemma cw3_frame_ro : forall E rs (m m' : word -> option byte),
Forall (fun r => YP09.r_whi r <= YP09.r_wlo r) rs -> frame_of E rs m m' -> forall x, m' x = m x.
Proof.
intros E rs m m' Hro H x. apply H. intros (r & Hr & Ha).
pose proof (proj1 (Forall_forall _ _) Hro r Hr) as Hw. cbn beta in Hw. lia.
Qed.
Lemma cw3_aview_ext : forall H (m m' : word -> option byte), (forall x, m' x = m x) ->
forall a, aview SEGS H m' a = aview SEGS H m a.
Proof. intros H m m' He a. unfold aview, mbyte, mrestrict. cbv beta. rewrite (He (Z_to_bv 64 a)). reflexivity. Qed.
Lemma cw3_pres : forall regs regs' (r : bv 5), aregs_preserved regs regs' -> acallee_saved (bv_unsigned r) ->
getr regs' r = getr regs r.
Proof. intros regs regs' r H Hr. pose proof (H _ Hr) as E. rewrite Z_to_bv_bv_unsigned in E. exact E. Qed.
(* the blocks the recorder owns are live blocks *)
Lemma cw3_O_blocks : forall ly S (rd : reader) R O pn, rec_repA B ly S rd R O -> In pn O -> In pn (ablocks B ly S).
Proof.
intros ly S rd R O pn (Q & HA & HO) Hin. apply HO in Hin.
destruct HA as (_ & _ & _ & (Hn & HlQ & _ & Hcalls & Hsp & _) & Hans & Hrep & _ & _).
unfold lay_blocks in Hin. apply in_app_or in Hin as [Hin | Hin].
- apply in_concat in Hin as (P & HP & Hin). apply In_nth_error in HP as (i & HPi).
  destruct (nth_error (r_calls R) i) as [cc|] eqn:Hci.
  + destruct (Hcalls i cc P Hci HPi) as ((_ & _ & HlP & _ & _ & _ & Hargs) & _).
    apply In_nth_error in Hin as (kk & Hk).
    destruct (nth_error (snd cc) kk) as [s|] eqn:Hs.
    * exact (proj1 (proj2 (proj2 (Hargs kk s pn Hs Hk)))).
    * exfalso. apply nth_error_None in Hs. assert (Hx : nth_error P kk <> None) by congruence.
      apply nth_error_Some in Hx. lia.
  + exfalso. apply nth_error_None in Hci. assert (Hx : nth_error (l_calls Q) i <> None) by congruence.
    apply nth_error_Some in Hx. lia.
- apply in_app_or in Hin as [Hin | Hin].
  + destruct Hsp as (_ & _ & HlP & _ & _ & _ & Hargs).
    apply In_nth_error in Hin as (kk & Hk).
    destruct (nth_error (snd (r_spill R)) kk) as [s|] eqn:Hs.
    * exact (proj1 (proj2 (proj2 (Hargs kk s pn Hs Hk)))).
    * exfalso. apply nth_error_None in Hs. assert (Hx : nth_error (l_spill Q) kk <> None) by congruence.
      apply nth_error_Some in Hx. lia.
  + apply in_app_or in Hin as [Hin | Hin].
    * unfold aanswer_at in Hans. destruct (l_answer Q) as [q|]; cbn [oblk In] in Hin; [|contradiction].
      destruct Hin as [<- | []]. destruct (r_answer R); [|contradiction]. exact (proj1 (proj2 (proj2 Hans))).
    * unfold areply_at in Hrep. destruct (l_reply Q) as [q|]; cbn [oblk In] in Hin; [|contradiction].
      destruct Hin as [<- | []]. destruct (r_reply R); [|contradiction].
      exact (proj1 (proj2 (proj2 (proj2 (proj2 Hrep))))).
Qed.
(* the walk's footprint lies below the allocator's ceiling: the recorder statics and the recorder's blocks *)
Lemma cw3_FP_low : forall c a, cw_pre B MT RLO RHI c -> inFP (cw_FP c) a -> a < alloc_ceiling.
Proof.
intros c a HP (r & Hr & Ha). pose proof asan_consts as (C1 & _).
unfold cw_FP, CHAIN_WORDS_PG in Hr. apply in_app_or in Hr as [Hr | Hr].
- cbn in Hr. destruct Hr as [<- | [<- | []]]; cbn [fst snd] in Ha; unfold A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE in Ha; lia.
- unfold ablocks_fp in Hr. apply in_map_iff in Hr as ([p n] & <- & Hin). cbn [fst snd] in Ha.
  pose proof (cw3_O_blocks _ _ _ _ _ _ (cp_rec _ _ _ _ _ HP) Hin) as Hb.
  pose proof (cp_afn _ _ _ _ _ HP) as (HAR & _).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hb) as (_ & _ & Hc & _). lia.
Qed.
(* the frame record the prologue wrote (ra at sp0 - 8, s0 at sp0 - 16) extends the caller's chain *)
Lemma cw3_chain : forall c ly3 S3 W3 (m : word -> option byte) md3 k,
cw_pre B MT RLO RHI c ->
ajournal SEGS B CHAIN_WORDS_STK (cw_sp0 c) (cw_FP c) (x_ly c) (x_S c) (x_W c) (x_mem c) (x_md c) [(3, x_fpos c)]
  ly3 S3 W3 m md3 k ->
(forall j r, nth_error cw_saved j = Some r ->
  rdword (rdW W3 m) (cw_sp0 c - 8 - 8 * Z.of_nat j) = Some (bv_unsigned (getr (x_regs c) (Z_to_bv 5 r)))) ->
exists ch1, achain ly3 (rdW W3 m) (cw_s1 c) (cw_sp0 c) ch1.
Proof.
intros c ly3 S3 W3 m md3 k HP HJ HSV.
pose proof (cp_afn _ _ _ _ _ HP) as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof HJ as (_ & Hly & _ & _ & _ & _ & _ & _ & G1 & _).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & _).
assert (FS : 144 <= CHAIN_WORDS_STK) by (unfold CHAIN_WORDS_STK, NUMBER_STK, ESTACK; lia).
destruct (cw_s1_facts c Hal16) as (Hs1m & Hs1).
unfold cw_sp0 in *.
destruct (Z_lt_le_dec (spZ (x_regs c)) (ly_top (x_ly c) - 16)) as [Hlt | Hge].
- exists ((spZ (x_regs c), raZ (x_regs c), s0Z (x_regs c)) :: x_ch c).
  apply (achain_ly_top (x_ly c) ly3 _ _ _ _ Etop).
  pose proof (HSV 0%nat 1 eq_refl) as H0. pose proof (HSV 1%nat 8 eq_refl) as H1.
  change (Z.of_nat 0) with 0 in H0. change (Z.of_nat 1) with 1 in H1.
  replace (spZ (x_regs c) - 8 - 8 * 0) with (spZ (x_regs c) - 8) in H0 by lia.
  replace (spZ (x_regs c) - 8 - 8 * 1) with (spZ (x_regs c) - 16) in H1 by lia.
  assert (Q1 : getr (x_regs c) (Z_to_bv 5 1) = getr (x_regs c) 1) by (f_equal; apply bv_eq; reflexivity).
  assert (Q8 : getr (x_regs c) (Z_to_bv 5 8) = getr (x_regs c) 8) by (f_equal; apply bv_eq; reflexivity).
  rewrite Q1 in H0. rewrite Q8 in H1.
  apply (achain_push (x_ly c) (rdW (x_W c) (x_mem c)) (rdW W3 m) (spZ (x_regs c)) (s0Z (x_regs c)) (raZ (x_regs c))
    (x_ch c) (cw_s1 c) Hch).
  + lia.
  + intros a Ha. apply G1; [lia | lia | intros HF; pose proof (cw3_FP_low c a HP HF); lia].
  + exact H0.
  + exact H1.
  + exact Hra4.
  + lia.
  + Z.div_mod_to_equations. lia.
  + lia.
  + lia.
- exists []. left. split; [right; left; rewrite Etop; lia | reflexivity].
Qed.
(* a run that writes nothing keeps the frame part and the untouched part of a cut *)
Lemma cw3_un_ext : forall c ly S W (m m' : word -> option byte), (forall x, m' x = m x) ->
cw_un B MT c ly S W m -> cw_un B MT c ly S W m'.
Proof.
intros c ly S W m m' He [U1 U2 U3 U4 U5 U6 U7 U8]. constructor; try assumption.
- intros a Ha Hb Hc. rewrite (cw3_aview_ext (w_H W) m m' He). exact (U1 a Ha Hb Hc).
- intros p n i Hp Hi. rewrite (cw3_aview_ext (w_H W) m m' He). exact (U2 p n i Hp Hi).
- intros cid pos a Hin Ha. rewrite (cw3_aview_ext (w_H W) m m' He). exact (U3 cid pos a Hin Ha).
- intros i Hi. rewrite (cw3_aview_ext (w_H W) m m' He). exact (U8 i Hi).
Qed.
Lemma cw3_fi_ext : forall c k ly S W regs (m : word -> option byte) md regs' m' md',
cw_fi B c k ly S W regs m md ->
ajournal SEGS B CHAIN_WORDS_STK (cw_sp0 c) (cw_FP c) (x_ly c) (x_S c) (x_W c) (x_mem c) (x_md c) [(3, x_fpos c)]
  ly S W m' md' k ->
(forall x, m' x = m x) ->
getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 -> getr regs' 8 = getr regs 8 ->
getr regs' 9 = getr regs 9 -> getr regs' 18 = getr regs 18 -> getr regs' 19 = getr regs 19 ->
getr regs' 24 = getr regs 24 ->
cw_fi B c k ly S W regs' m' md'.
Proof.
intros c k ly S W regs m md regs' m' md' [J1 G2 G3 G4 G8 G9 G18 G19 G24 GSV GFL] HJ He E2 E3 E4 E8 E9 E18 E19 E24.
constructor.
- exact HJ.
- rewrite E2; exact G2.
- rewrite E3; exact G3.
- rewrite E4; exact G4.
- rewrite E8; exact G8.
- rewrite E9; exact G9.
- rewrite E18; exact G18.
- rewrite E19; exact G19.
- rewrite E24; exact G24.
- intros j r Hj. rewrite <- (GSV j r Hj). apply rdword_ext. intros kk Hk. apply (cw3_aview_ext (w_H W) m m' He).
- rewrite <- GFL. apply rdword_ext. intros kk Hk. apply (cw3_aview_ext (w_H W) m m' He).
Qed.
(* the frame part of a cut carried across a program call whose footprint lies below the allocator's ceiling and
   misses the frame's flag word: copied from chain_words_s5.v (cw5_fi_call) *)
Lemma cw3_fi_call : forall c k k1 ly3 S3 W3 regs3 mem3 md3 ly4 S4 W4 regs4 mem4 md4 STK1 sp1 FP1,
cw_pre B MT RLO RHI c -> cw_fi B c k ly3 S3 W3 regs3 mem3 md3 ->
ajournal SEGS B CHAIN_WORDS_STK (cw_sp0 c) (cw_FP c) (x_ly c) (x_S c) (x_W c) (x_mem c) (x_md c)
  [(3, x_fpos c)] ly4 S4 W4 mem4 md4 (k + k1) ->
ajournal SEGS B STK1 sp1 FP1 ly3 S3 W3 mem3 md3 [] ly4 S4 W4 mem4 md4 k1 ->
sp1 <= cw_sp0 c - 128 ->
(forall a, inFP FP1 a -> a < alloc_ceiling) ->
(forall a, cw_F c + 504 <= a < cw_F c + 512 -> ~ inFP FP1 a) ->
aregs_preserved regs3 regs4 ->
cw_fi B c (k + k1) ly4 S4 W4 regs4 mem4 md4.
Proof.
intros c k k1 ly3 S3 W3 regs3 mem3 md3 ly4 S4 W4 regs4 mem4 md4 STK1 sp1 FP1 HP HF HJ HJc Hsp1 HFPlo HFPfl HPR.
pose proof (cp_afn _ _ _ _ _ HP) as (_ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (H16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & _).
assert (FS : 144 <= CHAIN_WORDS_STK) by (unfold CHAIN_WORDS_STK, NUMBER_STK, ESTACK; lia).
destruct HF as [HJ0 Hsp Hgp Htp Hs0 Hs1 Hs2 Hs3 Hs8 Hsaved Hflag].
pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & K9 & _ & _ & K12 & _).
pose proof HJ0 as (_ & Hly3 & _ & _ & _ & Hfr3 & _).
pose proof Hly3 as (_ & _ & _ & _ & _ & EF & _).
assert (CS : forall z, acallee_saved z -> forall r : bv 5, bv_unsigned r = z -> getr regs4 r = getr regs3 r).
{ intros z Hz r Hr. subst z. exact (cw3_pres regs3 regs4 r HPR Hz). }
constructor.
- exact HJ.
- rewrite (CS 2 ltac:(unfold acallee_saved; lia) 2%bv eq_refl). exact Hsp.
- rewrite (CS 3 ltac:(unfold acallee_saved; lia) 3%bv eq_refl). exact Hgp.
- rewrite (CS 4 ltac:(unfold acallee_saved; lia) 4%bv eq_refl). exact Htp.
- rewrite (CS 8 ltac:(unfold acallee_saved; lia) 8%bv eq_refl). exact Hs0.
- rewrite (CS 9 ltac:(unfold acallee_saved; lia) 9%bv eq_refl). exact Hs1.
- rewrite (CS 18 ltac:(unfold acallee_saved; lia) 18%bv eq_refl). exact Hs2.
- rewrite (CS 19 ltac:(unfold acallee_saved; lia) 19%bv eq_refl). exact Hs3.
- rewrite (CS 24 ltac:(unfold acallee_saved; lia) 24%bv eq_refl). exact Hs8.
- intros j r Hj. rewrite <- (Hsaved j r Hj). apply rdword_ext. intros i Hi.
  assert (Hj13 : (j < 13)%nat).
  { pose proof (proj1 (nth_error_Some cw_saved j) ltac:(rewrite Hj; discriminate)) as Hl. exact Hl. }
  unfold cw_sp0 in *.
  apply K9; [lia | lia | intros Hf; pose proof (HFPlo _ Hf); lia].
- rewrite <- Hflag. apply rdword_ext. intros i Hi.
  apply (K12 3 (x_fpos c)).
  + rewrite Hfr3. left. reflexivity.
  + left. unfold in_zr, frame_rng, cw_F, frame_addr in *. cbn [fst snd]. rewrite EF.
    change (fs_frame_bytes 3) with 512. lia.
  + apply HFPfl. lia.
Qed.
(* ids[j] is addressable: the shadow of ids[64] (frame + 32 .. frame + 288) says "usable" (cw_un's un_ids_sh) *)
Lemma cw3_ids_ra : forall (rd : reader) F j, F mod 8 = 0 -> 0 <= j <= 61 ->
  (forall i, 4 <= i < 36 -> rd (SB + F / 8 + i) = Some 0) ->
  range_addressable rd SHADOW_OFF (F + 32 + 4 * j) 4.
Proof.
intros rd F j HF Hj H x Hx. exists 0. split; [|left; reflexivity].
unfold shadow_of_addr. replace (SHADOW_OFF + x / 8) with (SB + F / 8 + (x / 8 - F / 8)) by (unfold SB, SHADOW_OFF; lia).
apply H. Z.div_mod_to_equations. lia.
Qed.
(* errno is an image cell, a side-stack frame is not *)
Lemma cw3_apart_errno : forall ly S (W : world SEGS) mem md cid pos out,
  AR SEGS B ly S W mem md -> In (cid, pos) (frames S) ->
  frame_addr ly cid pos <= out -> out + 4 <= frame_addr ly cid pos + fs_frame_bytes cid ->
  iv_apart out 4 (as_errno B) 4.
Proof.
intros ly S W mem md cid pos out HAR Hin Hlo Hhi. unfold iv_apart.
destruct (Z_le_gt_dec (out + 4) (as_errno B)) as [H1|H1]; [left; exact H1|].
destruct (Z_le_gt_dec (as_errno B + 4) out) as [H2|H2]; [right; exact H2|].
exfalso. pose proof (pal_env B TL) as (_ & Himg & _).
assert (Ha1 : as_errno B <= Z.max out (as_errno B) < as_errno B + 4) by lia.
assert (Ha2 : frame_addr ly cid pos <= Z.max out (as_errno B) < frame_addr ly cid pos + fs_frame_bytes cid) by lia.
destruct (al_client_img _ _ LAWS ly S W mem md (Z.max out (as_errno B)) HAR
  (or_intror (or_introl (ex_intro _ cid (ex_intro _ pos (conj Hin Ha2)))))) as [_ Hni].
exact (Hni (Himg _ Ha1)).
Qed.
(* the untouched part of a cut after the call of number, whose footprint is a 4-byte cell of the walk's own frame
   and which changes only the side-stack frame state *)
Lemma cw3_un_call : forall c ly3 S3 W3 m3 md3 STK1 sp1 S2 W2 m2 md2 k1 k f out,
ajournal SEGS B CHAIN_WORDS_STK (cw_sp0 c) (cw_FP c) (x_ly c) (x_S c) (x_W c) (x_mem c) (x_md c) [(3, x_fpos c)]
  ly3 S3 W3 m3 md3 k ->
cw_un B MT c ly3 S3 W3 m3 ->
ajournal SEGS B STK1 sp1 [(out, out + 4)] ly3 S3 W3 m3 md3 [] ly3 S2 W2 m2 md2 k1 ->
cw_F c <= out -> out + 4 <= cw_F c + 512 ->
Permutation (ablocks B ly3 S2) (ablocks B ly3 S3) -> S2 = set_fs f S3 ->
cw_un B MT c ly3 S2 W2 m2.
Proof.
intros c ly3 S3 W3 m3 md3 STK1 sp1 S2 W2 m2 md2 k1 k f out HJ [U1 U2 U3 U4 U5 U6 U7 U8] HJc Hlo Hhi HPERM HS2.
pose proof HJ as (HAR3 & Hly & _ & _ & _ & Hfrs & _).
pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & K1 & K2 & K3 & K4 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hin3 : In (3, x_fpos c) (frames S3)) by (rewrite Hfrs; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ _ _ HAR3 Hin3) as (Hal32 & Happ & _).
destruct (frames_bounds SEGS B LAWS ly3 S3 W3 m3 md3 3 (x_fpos c) HAR3 Hin3) as (Hf0 & Hfc & _).
assert (EF3 : frame_addr ly3 3 (x_fpos c) = cw_F c) by (unfold cw_F; exact (cw3_frame_addr_le _ _ _ 3 (x_fpos c) Hly)).
assert (F512 : fs_frame_bytes 3 = 512) by (vm_compute; reflexivity).
rewrite EF3 in Happ, Hf0, Hfc. rewrite F512 in Happ, Hfc.
assert (HFP : forall a, inFP [(out, out + 4)] a -> cw_F c <= a < cw_F c + 512).
{ intros a Ha. apply inFP_cons in Ha as [Ha | Ha]; [lia | exfalso; exact (inFP_nil a Ha)]. }
constructor.
- intros a Ha Hno Her. rewrite <- (U1 a Ha Hno Her). apply K3; [exact Ha | exact Hno | exact Her |].
  split.
  + intros (r & Hr & H0). exfalso.
    assert (HF0 : inFP [(out, out + 4)] 0) by (exists r; split; [exact Hr | exact H0]).
    specialize (HFP 0 HF0). lia.
  + intros HF. specialize (HFP a HF).
    assert (Ha2 : frame_addr ly3 3 (x_fpos c) <= a < frame_addr ly3 3 (x_fpos c) + fs_frame_bytes 3)
      by (rewrite EF3, F512; lia).
    destruct (al_client_img _ _ LAWS ly3 S3 W3 m3 md3 a HAR3
      (or_intror (or_introl (ex_intro _ 3 (ex_intro _ (x_fpos c) (conj Hin3 Ha2)))))) as [_ Hni].
    exact (Hni Ha).
- intros p n i Hin Hi. rewrite <- (U2 p n i Hin Hi).
  assert (Hin3b : In (p, n) (ablocks B ly3 S3)) by (apply (Permutation_in _ (Permutation_sym U4)); exact Hin).
  assert (Hin2 : In (p, n) (ablocks B ly3 S2)) by (apply (Permutation_in _ (Permutation_sym HPERM)); exact Hin3b).
  apply (K2 p n i Hin3b Hin2 Hi). intros HF. specialize (HFP _ HF).
  pose proof (sep_block_frame SEGS B LAWS ly3 S3 W3 m3 md3 p n 3 (x_fpos c) HAR3 Hin3b Hin3) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite EF3, F512 in Hd. lia.
- intros cid pos a Hin Ha. rewrite <- (U3 cid pos a Hin Ha).
  assert (Hin3c : In (cid, pos) (frames S3)) by (rewrite Hfrs; right; exact Hin).
  destruct (frames_bounds SEGS B LAWS ly3 S3 W3 m3 md3 cid pos HAR3 Hin3c) as (Hg0 & Hgc & _).
  pose proof (cw3_frame_addr_le _ _ _ cid pos Hly) as EFg.
  pose proof (fs_frame_bytes_nonneg cid) as Hfb.
  apply (K4 cid pos a Hin3c).
  + unfold frame_rng in *. cbn [fst snd] in *. rewrite EFg. exact Ha.
  + intros HF. specialize (HFP a HF). unfold frame_rng in Ha. cbn [fst snd] in Ha. rewrite <- EFg in Ha.
    destruct Ha as [Ha | Ha].
    * apply in_split in Hin as (l2 & l3 & El).
      assert (Ef : frames S3 = [] ++ (3, x_fpos c) :: l2 ++ (cid, pos) :: l3) by (rewrite Hfrs, El; reflexivity).
      pose proof (sep_frames_pos SEGS B LAWS ly3 S3 W3 m3 md3 (3, x_fpos c) (cid, pos) [] l2 l3 HAR3 Ef) as Hd.
      unfold zdisjoint, frame_rng in Hd. cbn [fst snd] in Hd. rewrite EF3, F512 in Hd.
      unfold in_zr in Ha. cbn [fst snd] in Ha. lia.
    * unfold in_zr in Ha. cbn [fst snd] in Ha.
      apply (cw3_app_shadow a (cw_F c) 512 (frame_addr ly3 cid pos) (fs_frame_bytes cid)
        (a - shadow_addr (frame_addr ly3 cid pos)) Happ ltac:(lia) Hg0 Hgc ltac:(lia)). lia.
- exact (Permutation_trans HPERM U4).
- subst S2. exact U5.
- subst S2. exact U6.
- subst S2. exact (mo_le_set_fs_r MT MTFL _ _ _ _ U7).
- intros i Hi. rewrite <- (U8 i Hi).
  assert (Hsh : in_zr (SB + cw_F c / 8 + i) (shadow_addr (frame_addr ly3 3 (x_fpos c)), fs_frame_bytes 3 / 8)).
  { unfold in_zr, shadow_addr, SB, SHADOW_OFF. cbn [fst snd]. rewrite EF3, F512. change (512 / 8) with 64. lia. }
  apply (K4 3 (x_fpos c) _ Hin3); [right; exact Hsh|].
  intros HF. specialize (HFP _ HF).
  apply (cw3_app_shadow (SB + cw_F c / 8 + i) (cw_F c) 512 (cw_F c) 512 i Happ ltac:(lia) Hf0 Hfc
    ltac:(change (512 / 8) with 64; lia)).
  unfold shadow_addr, SB, SHADOW_OFF. lia.
Qed.

(* the symbolic state at KL: s9 = &tok[2 + j] (atom 25) in the one region, tok[2 + j] (atom 32), the shadow base
   (atom 33), s10 = the shadow byte of s9 written as (s9 >> 3) + base, so that the inline check of 0x8e234 reads
   a shadow entry *)
Definition cw3_tokR : YP09.region := YP09.mkRegion (Some 25%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 32 0))].
Definition cw3_factsL : facts := mkFacts [(25%nat, mkAF 4096 (2 ^ 47 - 32) 3); (33%nat, mkAF SB SB 0)] [] [].
Definition cw3_shx : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff 25 0) (SLit 3)) (SOff 33 0).
Definition ss_cw3L : sstate := mkSS CW_KL (sr_set sr_atoms 26 cw3_shx) [cw3_tokR] None cw3_factsL.
Definition cw3_Bx : sv := SOff 33 0.
Definition cw3_SH : list shent := [mkSHE 25 0 8].
Definition cw3_Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition cw3_EL (regs : bvmap 5 word) (p : Z) : env := Eimg (Ereg regs [w64 p; w64 SB]).
Lemma cw3_seedL : forall ly S (W : world SEGS) mem md (regs : bvmap 5 word) tok ntok X p,
AR SEGS B ly S W mem md ->
getr regs 25 = w64 X -> getr regs 26 = w64 (SB + X / 8) ->
afobj SEGS B ly S W mem tok (8 * ntok) -> tok + 16 <= X -> X + 8 <= tok + 8 * ntok -> X mod 8 = 0 ->
aval_mem (rdW W mem) X 8 p -> 0 <= p < 2 ^ 64 ->
st_ok_pi SEGS VAL (cw3_EL regs p) ss_cw3L
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + CW_KL)) mem (seg_rom SEGS))) /\
sh_ok SEGS cw3_Bx cw3_SH (cw3_EL regs p) (mrestrict (w_H W) mem).
Proof.
intros ly S W mem md regs tok ntok X p HAR H25 H26 ((cid & pos & Hfr & Hcid & Hfa8 & Hlo & Hhi) & Htok8 & Hra)
  HX1 HX2 HX8 HP Hp.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (frames_bounds SEGS B LAWS ly S W mem md cid pos HAR Hfr) as (Hf0 & Hfc & Happ).
set (E := cw3_EL regs p).
assert (EEo : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew E m = getr regs rr).
{ intros m rr Hm. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  subst E. unfold cw3_EL. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hm. }
assert (X32 : ew E 32 = w64 p) by (subst E; unfold cw3_EL; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (X33 : ew E 33 = w64 SB) by (subst E; unfold cw3_EL; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E25 : ew E 25 = Z_to_bv 64 X) by (rewrite (EEo 25%nat 25%bv eq_refl); exact H25).
assert (U25 : base_val E (Some 25%nat) = X).
{ cbn [base_val]. rewrite E25. apply unsigned_lit_small. lia. }
split.
- rewrite restrict_mkst_fx. unfold ss_cw3L. apply pa_entry_st_ok_full.
  + apply regs_ok_rereg; [subst E; unfold cw3_EL; apply regs_ok_Eimg_Ereg | reflexivity |].
    rewrite H26. unfold cw3_shx. symmetry. apply (cw3_shadow_denot E 25 33 X E25 X33). lia.
  + vm_compute. reflexivity.
  + unfold cw3_tokR. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    rewrite U25. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    apply (chunk_ok_val SEGS E _ X 0 8 (SOff 32 0) p);
      [cbn [sv_denot]; rewrite X32, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity
      | cbn; lia | lia | rewrite Z.add_0_r; exact (cw3_val_mem SEGS (w_H W) mem _ 8%nat p HP)].
  + apply pairwise_disjoint_of_extents. unfold cw3_tokR, extent_of_region.
    cbn. repeat constructor.
  + split; [|split; [exact I | exact I]].
    cbn [cw3_factsL f_atoms atoms_ok].
    split; [apply (cw3_afact E 25%nat X); [exact E25 | lia | lia | change (2 ^ 3) with 8; exact HX8 | lia]|].
    split; [apply (cw3_afact E 33%nat SB); [exact X33 | unfold SB; lia | lia | rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | lia]|].
    exact I.
- unfold sh_ok, cw3_SH. constructor; [|constructor].
  apply (shent_ok_of_range SEGS (w_H W) mem E cw3_Bx 25 tok (8 * ntok) X 0 8 Hra).
  + unfold cw3_Bx. apply U_atom; [exact X33 | cbv [SB SHADOW_OFF]; lia].
  + apply U_atom; [exact E25 | lia].
  + lia.
  + lia.
  + intros x Hx. cbn [Z.min Z.max] in Hx.
    unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ. unfold SHADOW_OFF. lia.
Qed.
(* after the call: the registers only, a0 pinned to number's result: copied from chain_words_s2.v (cw2_seedR) *)
Definition cw3_ER (regs : bvmap 5 word) : env := Eimg (Ereg regs []).
Definition ss_cw3R : sstate := mkSS CW3_RET sr_atoms [] None (mkFacts [] [] []).
Definition ss_cw3A (a0 : Z) : sstate := mkSS CW3_RET (sr_set sr_atoms 10 (SLit a0)) [] None (mkFacts [] [] []).
Lemma cw3_seedR : forall (W : world SEGS) mem (regs : bvmap 5 word) a0, getr regs 10 = Z_to_bv 64 a0 ->
st_ok_pi SEGS VAL (cw3_ER regs) (ss_cw3A a0)
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + CW3_RET)) mem (seg_rom SEGS))) /\
sh_ok SEGS cw3_Bx [] (cw3_ER regs) (mrestrict (w_H W) mem).
Proof.
intros W mem regs a0 H10. split; [|constructor].
assert (HS : st_ok_pi SEGS VAL (cw3_ER regs) ss_cw3R
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + CW3_RET)) mem (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_cw3R. apply pa_entry_st_ok_full.
  - unfold cw3_ER. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - constructor.
  - apply pairwise_disjoint_of_extents. cbn. exact I.
  - split; [exact I | split; exact I]. }
exact (st_ok_pi_pin_reg' _ _ _ 10%bv a0 HS H10 eq_refl).
Qed.

(* number's post (number_c.v:107-114) at a call with word wd and result cell out *)
Definition cw3_numQ (wd : list byte) (out : Z) (W : world SEGS) (mem : word -> option byte) (ly : alayout) (S : astate)
  : alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
fun ly' S' W' regs' mem' md' =>
 match Verbs.number_m wd with
 | Some v => getr regs' 10 = w64 1 /\ aval_mem (rdW W' mem') out 4 v
 | None => getr regs' 10 = w64 0 /\ (forall i, 0 <= i < 4 -> rdW W' mem' (out + i) = rdW W mem (out + i))
 end /\
 Permutation (ablocks B ly' S') (ablocks B ly S) /\
 ly' = ly /\ (exists f, S' = set_fs f S).
Ltac cw3_q HP2 r :=
  apply (cw3_pres _ _ r HP2); cbv [acallee_saved];
  match goal with |- context [bv_unsigned ?x] => let z := eval vm_compute in (bv_unsigned x) in change (bv_unsigned x) with z end;
  lia.
Ltac cw3_mdv nm := lazymatch goal with |- context [with_vm_backing (m_vm_lazy ?md) ?mt ?md] =>
  set (nm := with_vm_backing (m_vm_lazy md) mt md) in *; clearbody nm end.
(* copied from chain_words_s2.v (cw2_ER_reg, cw2_regU, cw2_rr) *)
Lemma cw3_ER_reg : forall (regs : bvmap 5 word) m (rr : bv 5), Z.of_nat m = bv_unsigned rr ->
ew (cw3_ER regs) m = getr regs rr.
Proof.
intros regs m rr Hm. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
unfold cw3_ER. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hm.
Qed.
Lemma cw3_regU : forall (H : word -> bool) E ss ms r, st_ok_pi SEGS VAL E ss (restrict H ms) ->
getr (ms_regs ms) r = Z_to_bv 64 (U E (sr_get (ss_regs ss) r)).
Proof. intros H E ss ms r HS. rewrite (st_ok_pi_restrict_reg H E ss ms r HS). unfold U. symmetry. apply Z_to_bv_bv_unsigned. Qed.
Ltac cw3_rr HS r Hr :=
  lazymatch type of HS with
  | st_ok_pi _ _ ?E ?ss (restrict ?H ?ms) =>
    pose proof (cw3_regU H E ss ms r HS) as Hr;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr
  end.

Lemma cw_S3 : cw_S3P B MT RLO RHI.
Proof.
intros c j HPRE HKR HKD HKL1. unfold from_KL, cw_from.
intros ly3 S3 W3 regs3 mem3 md3
  ((HFI & HUN) & Hj & R20 & R21 & R22 & R23 & R25 & R26 & R27 & (id & vs & Hid & Hvs & Hidm & Hvsm)).
pose proof (TRANSP c 0 ly3 S3 W3 regs3 mem3 md3 HPRE HFI HUN) as (HTOK & HTOKS & HCB & HREC & HROD & HRO).
pose proof HFI as [HJ F2 F3 F4 F8 F9 F18 F19 F24 FSV FFL].
pose proof (proj1 HJ) as HAR3.
pose proof (cp_ntok _ _ _ _ _ HPRE) as HN. pose proof (cp_ntokr _ _ _ _ _ HPRE) as HNR.
pose proof (cp_tok64 _ _ _ _ _ HPRE) as HT64.
pose proof HTOKS as (Htk8 & Hlen & Hptr & Hwd).
destruct (nth_error (x_ptrs c) (2 + Z.to_nat j)) as [p|] eqn:Hpn;
  [| exfalso; apply nth_error_None in Hpn; rewrite Hlen in Hpn; lia].
destruct (nth_error (x_tks c) (2 + Z.to_nat j)) as [wd|] eqn:Hwdn;
  [| exfalso; apply nth_error_None in Hwdn; lia].
pose proof (Hptr _ p Hpn) as HP.
replace (x_tok c + 8 * Z.of_nat (2 + Z.to_nat j)) with (x_tok c + 16 + 8 * j) in HP by lia.
destruct (Hwd _ p wd Hpn Hwdn) as (HSTR & HWL & HCBP & HPCB).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 HCB) as (_ & Hcb4096 & Hcbc & _ & _ & _ & Hncb).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (req_size_pos (x_ncb c) (proj1 Hncb)) as Hreqcb.
assert (Hp64 : 0 <= p < 2 ^ 64) by lia.
pose proof HJ as (_ & Hly & _ & _ & _ & Hfrs & _).
assert (Hin3 : In (3, x_fpos c) (frames S3)) by (rewrite Hfrs; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ _ _ HAR3 Hin3) as (Hal32 & Happ & _).
destruct (frames_bounds SEGS B LAWS ly3 S3 W3 mem3 md3 3 (x_fpos c) HAR3 Hin3) as (Hf0 & Hfc & _).
assert (EF3 : frame_addr ly3 3 (x_fpos c) = cw_F c) by (unfold cw_F; exact (cw3_frame_addr_le _ _ _ 3 (x_fpos c) Hly)).
assert (F512 : fs_frame_bytes 3 = 512) by (vm_compute; reflexivity).
rewrite EF3 in Happ, Hf0, Hfc, Hal32. rewrite F512 in Happ, Hfc.
pose proof HTOK as ((tcid & tpos & Htfr & _ & _ & Htlo & Hthi) & _ & _).
destruct (frames_bounds SEGS B LAWS ly3 S3 W3 mem3 md3 tcid tpos HAR3 Htfr) as (Ht0 & Htc & _).
assert (HTR : 4096 <= x_tok c /\ x_tok c + 8 * x_ntok c <= alloc_ceiling) by lia.
clear tcid tpos Htfr Htlo Hthi Ht0 Htc.
set (out := cw_F c + 32 + 4 * j).
destruct (cw3_seedL ly3 S3 W3 mem3 md3 regs3 (x_tok c) (x_ntok c) (x_tok c + 16 + 8 * j) p HAR3 R25 R26 HTOK
  ltac:(lia) ltac:(lia) ltac:(Z.div_mod_to_equations; lia) HP Hp64) as [HS SHOK].
assert (HEI : img_env VAL A_LIM (cw3_EL regs3 p)) by (unfold cw3_EL; apply Eimg_env).
unfold cfg_at, w64.
paj_run_tok RUN HS HJ SHOK cw3_Bspan.
{ unfold ss_cw3L, cw3_tokR. cbn [ss_mem]. apply (awr_ok_cons_ro SEGS B); [cbn; lia|]. apply (awr_ok_nil SEGS B). }
pmkst HS.
cw3_mdv mdv.
assert (EEo : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew (cw3_EL regs3 p) m = getr regs3 rr).
{ intros m rr Hm. unfold cw3_EL. rewrite Eimg_low by (pose proof (bv_unsigned_in_range 5 rr) as Hr5;
    change (bv_modulus 5) with 32 in Hr5; unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hm. }
assert (X32 : ew (cw3_EL regs3 p) 32 = w64 p)
  by (unfold cw3_EL; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs3 _ 0)).
assert (X33 : ew (cw3_EL regs3 p) 33 = w64 SB)
  by (unfold cw3_EL; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs3 _ 1)).
prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9. prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11.
prreg HS (18%bv : bv 5) P18. prreg HS (19%bv : bv 5) P19. prreg HS (20%bv : bv 5) P20. prreg HS (21%bv : bv 5) P21.
prreg HS (22%bv : bv 5) P22. prreg HS (23%bv : bv 5) P23. prreg HS (24%bv : bv 5) P24. prreg HS (25%bv : bv 5) P25.
prreg HS (27%bv : bv 5) P27.
assert (P26 : getr (ms_regs ms) 26 = getr regs3 26).
{ lazymatch type of HS with st_ok _ _ ?ss _ =>
    pose proof (st_ok_restrict_reg SEGS (w_H W3) (cw3_EL regs3 p) ss ms (26%bv : bv 5) HS) as Q;
    let e := eval vm_compute in (sr_get (ss_regs ss) (26%bv : bv 5)) in
    change (sr_get (ss_regs ss) (26%bv : bv 5)) with e in Q end.
  cbn [ms_regs restrict] in Q. rewrite Q, R26.
  apply (cw3_shadow_denot _ 25 33 (x_tok c + 16 + 8 * j)); [rewrite (EEo 25%nat 25%bv eq_refl); exact R25 | exact X33 | lia]. }
rewrite (EEo 2%nat 2%bv eq_refl) in P2. rewrite (EEo 3%nat 3%bv eq_refl) in P3. rewrite (EEo 4%nat 4%bv eq_refl) in P4.
rewrite (EEo 8%nat 8%bv eq_refl) in P8. rewrite (EEo 9%nat 9%bv eq_refl) in P9.
rewrite X32 in P10. rewrite (EEo 21%nat 21%bv eq_refl), R21 in P11.
rewrite (EEo 18%nat 18%bv eq_refl) in P18. rewrite (EEo 19%nat 19%bv eq_refl) in P19.
rewrite (EEo 20%nat 20%bv eq_refl) in P20. rewrite (EEo 21%nat 21%bv eq_refl) in P21.
rewrite (EEo 22%nat 22%bv eq_refl) in P22. rewrite (EEo 23%nat 23%bv eq_refl) in P23.
rewrite (EEo 24%nat 24%bv eq_refl) in P24. rewrite (EEo 25%nat 25%bv eq_refl) in P25.
rewrite (EEo 27%nat 27%bv eq_refl) in P27.
pose proof HJ as (HARc & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
destruct (cw_s1_facts c Hal16) as (Hs1m & Hs1).
assert (FS : 144 + NUMBER_STK <= CHAIN_WORDS_STK) by (unfold CHAIN_WORDS_STK; lia).
assert (FN : 0 <= NUMBER_STK) by (unfold NUMBER_STK, ESTACK; lia).
pose proof pa_B_ok as HBASE. pose proof (pa_base_lo (PL := PL_cmd)) as HBLO.
pose proof (cw3_frame_ro (cw3_EL regs3 p) (ss_mem ss_cw3L) mem3 (ms_mem ms)
  ltac:(unfold ss_cw3L, cw3_tokR; cbn [ss_mem]; constructor; [cbn; lia | constructor]) HF) as HEQ.
pose proof (cw3_fi_ext c 0 ly3 S3 W3 regs3 mem3 md3 (ms_regs ms) (ms_mem ms) mdv HFI HJ HEQ P2 P3 P4 P8 P9 P18 P19 P24)
  as HFIc.
pose proof (cw3_un_ext c ly3 S3 W3 mem3 (ms_mem ms) HEQ HUN) as HUNc.
destruct (TRANSP c 0 ly3 S3 W3 (ms_regs ms) (ms_mem ms) mdv HPRE HFIc HUNc) as
  (HTOKc & HTOKSc & HCBc & HRECc & HRODc & HROc).
pose proof HTOKSc as (_ & _ & _ & Hwdc).
destruct (Hwdc _ p wd Hpn Hwdn) as (HSTRc & _ & _ & _).
pose proof HFIc as [_ _ _ _ _ _ _ _ _ FSVc _].
pose proof HUN as [U1 U2 U3 U4 U5 U6 U7 U8].
pose proof HUNc as [_ _ _ _ _ _ _ U8c].
(* number's premises at the call *)
assert (Ho16 : (cw_s1 c - cw_sp0 c) mod 16 = 0).
{ destruct Hs1 as [-> | ->]; [replace (cw_sp0 c - 128 - cw_sp0 c) with (-128) by lia
  | replace (cw_sp0 c - 144 - cw_sp0 c) with (-144) by lia]; reflexivity. }
assert (HSPc : spZ (ms_regs ms) = cw_sp0 c + (cw_s1 c - cw_sp0 c)).
{ unfold spZ. rewrite P2, F2. unfold w64. rewrite unsigned_lit_small by lia. lia. }
destruct (cw3_chain c ly3 S3 W3 (ms_mem ms) mdv 0 HPRE HJ FSVc) as (ch1 & HCH).
assert (HCH' : achain ly3 (rdW W3 (ms_mem ms)) (cw_sp0 c + (cw_s1 c - cw_sp0 c)) (s0Z (ms_regs ms)) ch1).
{ replace (cw_sp0 c + (cw_s1 c - cw_sp0 c)) with (cw_s1 c) by lia.
  replace (s0Z (ms_regs ms)) with (cw_sp0 c) by (unfold s0Z; rewrite P8, F8; unfold w64; rewrite unsigned_lit_small by lia; reflexivity).
  exact HCH. }
assert (P3' : getr (ms_regs ms) 3 = w64 (as_gp B)) by (rewrite P3; exact F3).
assert (P4' : getr (ms_regs ms) 4 = w64 (as_tp B)) by (rewrite P4; exact F4).
assert (HRA : YK0s.ret_ok (getr (ms_regs ms) 1)) by (rewrite P1; apply ret_ok_codeptr_v; [lia | reflexivity]).
assert (HRA4 : 4096 <= bv_unsigned (getr (ms_regs ms) 1)) by (rewrite P1, unsigned_lit_small by lia; lia).
assert (Hout64 : 0 <= out < 2 ^ 64) by (unfold out; lia).
assert (HINB : in_blockA (ablocks B ly3 S3) p (Z.of_nat (length wd) + 1)).
{ exists (x_cb c), (x_ncb c). split; [exact HCB | lia]. }
assert (HWL' : Z.of_nat (length wd) + 1 <= LMAX + 1) by (unfold LMAX; lia).
assert (Hout4 : out mod 4 = 0) by (unfold out; clear - Hal32; Z.div_mod_to_equations; lia).
assert (HOUT : ((exists cid pos, In (cid, pos) (frames S3) /\
   frame_addr ly3 cid pos <= out /\ out + 4 <= frame_addr ly3 cid pos + fs_frame_bytes cid) /\
  range_addressable (rdW W3 (ms_mem ms)) SHADOW_OFF out 4) \/
  (spZ (ms_regs ms) <= out /\ out + 4 <= ly_top ly3 /\ (forall i, 0 <= i < 4 -> apresent (w_H W3) (ms_mem ms) (out + i)))).
{ left. split.
  - exists 3, (x_fpos c). split; [exact Hin3|]. rewrite EF3, F512. unfold out. lia.
  - apply (cw3_ids_ra _ (cw_F c) j); [clear - Hal32; Z.div_mod_to_equations; lia | lia | exact U8c]. }
assert (HAPART : iv_apart out 4 (as_errno B) 4).
{ apply (cw3_apart_errno ly3 S3 W3 (ms_mem ms) mdv 3 (x_fpos c) out HARc Hin3);
  rewrite ?EF3, ?F512; unfold out; lia. }
assert (HFR6 : Z.of_nat (length (frames S3)) <= 6).
{ rewrite Hfrs. cbn [app length]. pose proof (cp_frames _ _ _ _ _ HPRE). lia. }
assert (EVR : 0 <= EV_SUP_RESP) by (apply Z.leb_le; vm_compute; reflexivity).
assert (HNEV0 : st_nev S3 + EV_NUMBER <= EV_MAX).
{ pose proof (cp_nev _ _ _ _ _ HPRE). unfold EV_CHAIN_WORDS, EV_NUMBER in *. lia. }
assert (HFPlo : forall a, inFP [(out, out + 4)] a -> cw_F c + 32 + 4 * j <= a < cw_F c + 32 + 4 * j + 4).
{ intros a Ha. apply inFP_cons in Ha as [Ha | Ha]; [unfold out in Ha; lia | exfalso; exact (inFP_nil a Ha)]. }
(* the call of number at 0x8e244 *)
rewrite (proj1 (cw_sig_of SIGP)).
eapply SRr_bind.
{ refine (cl_callS_wide B LAWS W3 (ms_regs ms) (ms_mem ms) (Z_to_bv 64 (BASE + AF_number)) CHAIN_WORDS_STK (cw_sp0 c)
    (cw_FP c) (x_ly c) (x_S c) (x_W c) (x_mem c) (x_md c) [(3, x_fpos c)] ly3 S3 mdv 0 NUMBER_STK
    [(out, out + 4)] EV_NUMBER (cw_s1 c - cw_sp0 c) (getr (ms_regs ms) 1) ch1
    (cw3_numQ wd out W3 (ms_mem ms) ly3 S3)
    HJ HSPc Ho16 ltac:(lia) FN ltac:(lia) P3' P4' eq_refl HRA HRA4 HCH' _ _ _).
  - intros HPRE1. exact (NUMBER fx ly3 S3 W3 (ms_regs ms) (ms_mem ms) mdv ch1 p out wd HPRE1 HRODc P10 Hp64 P11
      Hout64 HINB HSTRc HWL' Hout4 HOUT HAPART HFR6 HNEV0).
  - intros a Ha. right; right; right; left. exists 3, (x_fpos c). split; [left; reflexivity|]. left.
    pose proof (HFPlo a Ha). unfold in_zr. cbn [fst snd]. rewrite EF3, F512. lia.
  - intros ly2' S2' W2' regs2' mem2' md2' _ a Ha Hw _. exfalso. pose proof (HFPlo a Ha). lia. }
cbv beta. intros W2 c2 Hwle2 (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJc2 & HP2 & HK2).
replace (cw_sp0 c + (cw_s1 c - cw_sp0 c)) with (cw_s1 c) in HJc2 by lia.
rewrite P1.
unfold cw3_numQ in HK2. destruct HK2 as (HNUM & HPERM2 & -> & (f & ->)).
assert (Q2 : getr regs2 2 = getr (ms_regs ms) 2) by cw3_q HP2 (2%bv : bv 5).
assert (Q3 : getr regs2 3 = getr (ms_regs ms) 3) by cw3_q HP2 (3%bv : bv 5).
assert (Q4 : getr regs2 4 = getr (ms_regs ms) 4) by cw3_q HP2 (4%bv : bv 5).
assert (Q8 : getr regs2 8 = getr (ms_regs ms) 8) by cw3_q HP2 (8%bv : bv 5).
assert (Q9 : getr regs2 9 = getr (ms_regs ms) 9) by cw3_q HP2 (9%bv : bv 5).
assert (Q18 : getr regs2 18 = getr (ms_regs ms) 18) by cw3_q HP2 (18%bv : bv 5).
assert (Q19 : getr regs2 19 = getr (ms_regs ms) 19) by cw3_q HP2 (19%bv : bv 5).
assert (Q20 : getr regs2 20 = getr (ms_regs ms) 20) by cw3_q HP2 (20%bv : bv 5).
assert (Q21 : getr regs2 21 = getr (ms_regs ms) 21) by cw3_q HP2 (21%bv : bv 5).
assert (Q22 : getr regs2 22 = getr (ms_regs ms) 22) by cw3_q HP2 (22%bv : bv 5).
assert (Q23 : getr regs2 23 = getr (ms_regs ms) 23) by cw3_q HP2 (23%bv : bv 5).
assert (Q24 : getr regs2 24 = getr (ms_regs ms) 24) by cw3_q HP2 (24%bv : bv 5).
assert (Q25 : getr regs2 25 = getr (ms_regs ms) 25) by cw3_q HP2 (25%bv : bv 5).
assert (Q26 : getr regs2 26 = getr (ms_regs ms) 26) by cw3_q HP2 (26%bv : bv 5).
assert (Q27 : getr regs2 27 = getr (ms_regs ms) 27) by cw3_q HP2 (27%bv : bv 5).
assert (HFP1 : forall a, inFP [(out, out + 4)] a -> a < alloc_ceiling) by (intros a Ha; pose proof (HFPlo a Ha); lia).
assert (HFP2 : forall a, cw_F c + 504 <= a < cw_F c + 512 -> ~ inFP [(out, out + 4)] a)
  by (intros a Ha Hf; pose proof (HFPlo a Hf); lia).
pose proof (cw3_fi_call c 0 EV_NUMBER ly3 S3 W3 (ms_regs ms) (ms_mem ms) mdv ly3 (set_fs f S3) W2 regs2 mem2 md2
  NUMBER_STK (cw_s1 c) [(out, out + 4)] HPRE HFIc HJ2 HJc2 ltac:(lia) HFP1 HFP2 HP2) as HFI2.
pose proof (cw3_un_call c ly3 S3 W3 (ms_mem ms) mdv NUMBER_STK (cw_s1 c) (set_fs f S3) W2 mem2 md2 EV_NUMBER 0 f out
  HJ HUNc HJc2 ltac:(unfold out; lia) ltac:(unfold out; lia) HPERM2 eq_refl) as HUN2.
change (0 + EV_NUMBER) with 0 in HFI2, HJ2.
change (Z_to_bv 64 (BASE + 32100)) with (Z_to_bv 64 (BASE + CW3_RET)).
(* what number kept: the id cell (real stack, above its window) and ids[0..j) (the frame, below ids[j]) *)
pose proof HJc2 as (_ & _ & _ & _ & _ & _ & _ & _ & K1c & _ & _ & K4c & _).
assert (HKid : forall i, 0 <= i < 4 -> rdW W2 mem2 (cw_s1 c + 20 + i) = rdW W3 mem3 (cw_s1 c + 20 + i)).
{ intros i Hi. rewrite K1c; [exact (cw3_aview_ext (w_H W3) mem3 (ms_mem ms) HEQ _) | lia | lia |].
  intros HF0. pose proof (HFP1 _ HF0). lia. }
assert (HKvs : forall i, 0 <= i < 4 * j -> rdW W2 mem2 (cw_F c + 32 + i) = rdW W3 mem3 (cw_F c + 32 + i)).
{ intros i Hi. rewrite (K4c 3 (x_fpos c)); [exact (cw3_aview_ext (w_H W3) mem3 (ms_mem ms) HEQ _) | exact Hin3 | |].
  - left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite EF3, F512. lia.
  - intros HF0. pose proof (HFPlo _ HF0). lia. }
assert (Hlvs : length vs = Z.to_nat j).
{ rewrite (cw3_numbers_len _ _ Hvs), firstn_length_le; [reflexivity|]. rewrite length_skipn. lia. }
assert (Hidm2 : aval_mem (rdW W2 mem2) (cw_s1 c + 20) 4 id).
{ apply (cw3_aval_ext _ _ _ _ _ Hidm). intros i Hi. apply HKid. lia. }
assert (Hvsm2 : abytes_atR (rdW W2 mem2) (cw_F c + 32) (concat (map le32 vs))).
{ apply (cw3_abytes_ext _ _ _ _ Hvsm). intros i Hi. rewrite cw3_len_ids, Hlvs in Hi. apply HKvs. lia. }
assert (Hwds : nth_error (skipn 2 (x_tks c)) (Z.to_nat j) = Some wd) by (rewrite cw3_nth_skipn; exact Hwdn).
clear HS SHOK HF HFr HG HEI0.
(* the loop registers at the return, through number (callee-saved) and the first run *)
assert (V20 : ew (cw3_ER regs2) 20 = w64 (x_ntok c)) by (rewrite (cw3_ER_reg regs2 20 20%bv eq_refl), Q20, P20; exact R20).
assert (V21 : ew (cw3_ER regs2) 21 = w64 out) by (rewrite (cw3_ER_reg regs2 21 21%bv eq_refl), Q21, P21; exact R21).
assert (V22 : ew (cw3_ER regs2) 22 = w64 (cw_F c + 32))
  by (rewrite (cw3_ER_reg regs2 22 22%bv eq_refl), Q22, P22; exact R22).
assert (V23 : ew (cw3_ER regs2) 23 = w64 (x_tok c + 16 + 8 * j))
  by (rewrite (cw3_ER_reg regs2 23 23%bv eq_refl), Q23, P23; exact R23).
assert (V25 : ew (cw3_ER regs2) 25 = w64 (x_tok c + 16 + 8 * j))
  by (rewrite (cw3_ER_reg regs2 25 25%bv eq_refl), Q25, P25; exact R25).
assert (V26 : ew (cw3_ER regs2) 26 = w64 (SB + (x_tok c + 16 + 8 * j) / 8))
  by (rewrite (cw3_ER_reg regs2 26 26%bv eq_refl), Q26, P26; exact R26).
assert (V27 : ew (cw3_ER regs2) 27 = w64 (x_ntok c - 2 - j))
  by (rewrite (cw3_ER_reg regs2 27 27%bv eq_refl), Q27, P27; exact R27).
assert (HSB : SB = 0x7fff8000) by reflexivity.
assert (HX8 : 0 <= (x_tok c + 16 + 8 * j) / 8 <= x_tok c + 16 + 8 * j)
  by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
destruct (Verbs.number_m wd) as [v|] eqn:Hnum.
- (* number accepted tok[2 + j]: the advance and the loop branch *)
  destruct HNUM as (HA1 & HVAL).
  assert (Hvs1 : Verbs.numbers_m (firstn (S (Z.to_nat j)) (skipn 2 (x_tks c))) = Some (vs ++ [v])).
  { rewrite (cw3_firstn_S _ _ _ Hwds), cw3_numbers_app, Hvs. cbn [Verbs.numbers_m]. rewrite Hnum. reflexivity. }
  assert (Hidm3 : forall m', (forall x, m' x = mem2 x) -> aval_mem (rdW W2 m') (cw_s1 c + 20) 4 id).
  { intros m' Hm'. apply (cw3_aval_ext _ _ _ _ _ Hidm2). intros i Hi. exact (cw3_aview_ext (w_H W2) mem2 m' Hm' _). }
  assert (Hvsm3 : forall m', (forall x, m' x = mem2 x) ->
    abytes_atR (rdW W2 m') (cw_F c + 32) (concat (map le32 (vs ++ [v])))).
  { intros m' Hm'. rewrite map_app, concat_app. cbn [map concat]. rewrite app_nil_r.
    apply (cw3_abytes_ext (rdW W2 mem2)); [| intros i Hi; exact (cw3_aview_ext (w_H W2) mem2 m' Hm' _)].
    apply cw3_abytes_app; [exact Hvsm2|].
    replace (cw_F c + 32 + Z.of_nat (length (concat (map le32 vs)))) with out
      by (rewrite cw3_len_ids, Hlvs; unfold out; lia).
    exact (cw3_le32 _ _ _ HVAL). }
  destruct (cw3_seedR W2 mem2 regs2 1 HA1) as [HS2 SHOK2].
  assert (HEI2 : img_env VAL A_LIM (cw3_ER regs2)) by (unfold cw3_ER; apply Eimg_env).
  (* 0x8e248 .. 0x8e260: beqz a0 not taken, the advance, to bnez s11 *)
  paj_run_tok RUN HS2 HJ2 SHOK2 cw3_Bspan.
  { apply (awr_ok_nil SEGS B). }
  cw3_mdv mdk.
  pose proof (cw3_frame_ro (cw3_ER regs2) (ss_mem (ss_cw3A 1)) mem2 _ ltac:(constructor) HF) as HEQa.
  clear HF HFr HG.
  lazymatch type of HS2 with context [restrict _ ?m] => rename m into msa end.
  psrr_branch_tok RUN BR HS2 SHOK2 cw3_Bspan.
  + (* bnez s11 taken: KL at pass j + 1 *)
    rename Hc into Hbr.
    paj_run_to_tok RUNTO HS2 HJ2 SHOK2 cw3_Bspan CW_KL.
    { apply (awr_ok_nil SEGS B). }
    pmkst HS2. cw3_mdv mdk2.
    lazymatch type of HS2 with context [restrict _ ?m] => rename m into msb end.
    pose proof (cw3_frame_ro (cw3_ER regs2) _ (ms_mem msa) (ms_mem msb) ltac:(constructor) HF) as HEQb.
    assert (HEQ2 : forall x, ms_mem msb x = mem2 x) by (intros x; rewrite HEQb; exact (HEQa x)).
    prreg HS2 (2%bv : bv 5) T2. prreg HS2 (3%bv : bv 5) T3. prreg HS2 (4%bv : bv 5) T4. prreg HS2 (8%bv : bv 5) T8.
    prreg HS2 (9%bv : bv 5) T9. prreg HS2 (18%bv : bv 5) T18. prreg HS2 (19%bv : bv 5) T19. prreg HS2 (24%bv : bv 5) T24.
    rewrite (cw3_ER_reg regs2 2 2%bv eq_refl) in T2. rewrite (cw3_ER_reg regs2 3 3%bv eq_refl) in T3.
    rewrite (cw3_ER_reg regs2 4 4%bv eq_refl) in T4. rewrite (cw3_ER_reg regs2 8 8%bv eq_refl) in T8.
    rewrite (cw3_ER_reg regs2 9 9%bv eq_refl) in T9. rewrite (cw3_ER_reg regs2 18 18%bv eq_refl) in T18.
    rewrite (cw3_ER_reg regs2 19 19%bv eq_refl) in T19. rewrite (cw3_ER_reg regs2 24 24%bv eq_refl) in T24.
    pose proof (cw3_fi_ext c 0 ly3 (set_fs f S3) W2 regs2 mem2 md2 _ _ mdk2 HFI2 HJ2 HEQ2 T2 T3 T4 T8 T9 T18 T19 T24)
      as HFIk.
    pose proof (cw3_un_ext c ly3 (set_fs f S3) W2 mem2 _ HEQ2 HUN2) as HUNk.
    cw3_rr HS2 (20%bv : bv 5) T20. cw3_rr HS2 (21%bv : bv 5) T21. cw3_rr HS2 (22%bv : bv 5) T22.
    cw3_rr HS2 (23%bv : bv 5) T23. cw3_rr HS2 (25%bv : bv 5) T25. cw3_rr HS2 (26%bv : bv 5) T26.
    cw3_rr HS2 (27%bv : bv 5) T27.
    rewrite branch_ne_U, U_SOff, U_SLit, V27 in Hbr. unfold w64 in Hbr.
    rewrite unsigned_lit_small in Hbr by lia. rewrite (zcanon_small (x_ntok c - 2 - j + -1)) in Hbr by lia.
    change (zcanon 0) with 0 in Hbr. apply negb_true_iff, Z.eqb_neq in Hbr.
    assert (HXd : (x_tok c + 16 + 8 * (j + 1)) / 8 = (x_tok c + 16 + 8 * j) / 8 + 1).
    { replace (x_tok c + 16 + 8 * (j + 1)) with (x_tok c + 16 + 8 * j + 1 * 8) by lia. apply Z.div_add. lia. }
    unfold from_KL, cw_from in HKL1.
    apply (HKL1 ly3 (set_fs f S3) W2 (ms_regs msb) (ms_mem msb) mdk2). unfold INV_KL.
    split; [exact (conj HFIk HUNk)|]. split; [lia|].
    split; [rewrite T20; unfold w64; f_equal; rewrite U_SOff, V20; unfold w64;
      rewrite unsigned_lit_small, zcanon_small by lia; lia|].
    split; [rewrite T21; unfold w64; f_equal; rewrite U_SOff, V21; unfold w64, out;
      rewrite unsigned_lit_small, zcanon_small by lia; lia|].
    split; [rewrite T22; unfold w64; f_equal; rewrite U_SOff, V22; unfold w64;
      rewrite unsigned_lit_small, zcanon_small by lia; lia|].
    split; [rewrite T23; unfold w64; f_equal; rewrite U_SOff, V23; unfold w64;
      rewrite unsigned_lit_small, zcanon_small by lia; lia|].
    split; [rewrite T25; unfold w64; f_equal; rewrite U_SOff, V25; unfold w64;
      rewrite unsigned_lit_small, zcanon_small by lia; lia|].
    split; [rewrite T26; unfold w64; f_equal; rewrite U_SOff, V26, HXd; unfold w64;
      rewrite unsigned_lit_small, zcanon_small by lia; lia|].
    split; [rewrite T27; unfold w64; f_equal; rewrite U_SOff, V27; unfold w64;
      rewrite unsigned_lit_small, zcanon_small by lia; lia|].
    exists id, (vs ++ [v]). split; [exact Hid|].
    split; [replace (Z.to_nat (j + 1)) with (S (Z.to_nat j)) by lia; exact Hvs1|].
    split; [exact (Hidm3 _ HEQ2) | exact (Hvsm3 _ HEQ2)].
  + (* bnez s11 not taken: KD, every member parsed *)
    rename Hc into Hbr.
    paj_run_to_tok RUNTO HS2 HJ2 SHOK2 cw3_Bspan CW_KD.
    { apply (awr_ok_nil SEGS B). }
    pmkst HS2. cw3_mdv mdk2.
    lazymatch type of HS2 with context [restrict _ ?m] => rename m into msb end.
    pose proof (cw3_frame_ro (cw3_ER regs2) _ (ms_mem msa) (ms_mem msb) ltac:(constructor) HF) as HEQb.
    assert (HEQ2 : forall x, ms_mem msb x = mem2 x) by (intros x; rewrite HEQb; exact (HEQa x)).
    prreg HS2 (2%bv : bv 5) T2. prreg HS2 (3%bv : bv 5) T3. prreg HS2 (4%bv : bv 5) T4. prreg HS2 (8%bv : bv 5) T8.
    prreg HS2 (9%bv : bv 5) T9. prreg HS2 (18%bv : bv 5) T18. prreg HS2 (19%bv : bv 5) T19. prreg HS2 (24%bv : bv 5) T24.
    rewrite (cw3_ER_reg regs2 2 2%bv eq_refl) in T2. rewrite (cw3_ER_reg regs2 3 3%bv eq_refl) in T3.
    rewrite (cw3_ER_reg regs2 4 4%bv eq_refl) in T4. rewrite (cw3_ER_reg regs2 8 8%bv eq_refl) in T8.
    rewrite (cw3_ER_reg regs2 9 9%bv eq_refl) in T9. rewrite (cw3_ER_reg regs2 18 18%bv eq_refl) in T18.
    rewrite (cw3_ER_reg regs2 19 19%bv eq_refl) in T19. rewrite (cw3_ER_reg regs2 24 24%bv eq_refl) in T24.
    pose proof (cw3_fi_ext c 0 ly3 (set_fs f S3) W2 regs2 mem2 md2 _ _ mdk2 HFI2 HJ2 HEQ2 T2 T3 T4 T8 T9 T18 T19 T24)
      as HFIk.
    pose proof (cw3_un_ext c ly3 (set_fs f S3) W2 mem2 _ HEQ2 HUN2) as HUNk.
    cw3_rr HS2 (20%bv : bv 5) T20. cw3_rr HS2 (22%bv : bv 5) T22.
    rewrite branch_ne_U, U_SOff, U_SLit, V27 in Hbr. unfold w64 in Hbr.
    rewrite unsigned_lit_small in Hbr by lia. rewrite (zcanon_small (x_ntok c - 2 - j + -1)) in Hbr by lia.
    change (zcanon 0) with 0 in Hbr. apply negb_false_iff, Z.eqb_eq in Hbr.
    assert (Hvs2 : Verbs.numbers_m (skipn 2 (x_tks c)) = Some (vs ++ [v])).
    { assert (E : firstn (S (Z.to_nat j)) (skipn 2 (x_tks c)) = skipn 2 (x_tks c))
        by (apply firstn_all2; rewrite length_skipn; lia).
      rewrite <- E. exact Hvs1. }
    unfold from_KD, cw_from in HKD.
    apply (HKD ly3 (set_fs f S3) W2 (ms_regs msb) (ms_mem msb) mdk2). unfold INV_KD.
    split; [exact (conj HFIk HUNk)|].
    split; [rewrite T20; unfold w64; f_equal; rewrite U_SOff, V20; unfold w64;
      rewrite unsigned_lit_small, zcanon_small by lia; lia|].
    split; [rewrite T22; unfold w64; f_equal; rewrite U_SOff, V22; unfold w64;
      rewrite unsigned_lit_small, zcanon_small by lia; lia|].
    split; [lia|].
    exists id, (vs ++ [v]). split; [exact Hid|]. split; [exact Hvs2|].
    split; [exact (Hidm3 _ HEQ2) | exact (Hvsm3 _ HEQ2)].
- (* number refused tok[2 + j]: beqz a0 to KR *)
  destruct HNUM as (HA0 & _).
  destruct (cw3_seedR W2 mem2 regs2 0 HA0) as [HS2 SHOK2].
  assert (HEI2 : img_env VAL A_LIM (cw3_ER regs2)) by (unfold cw3_ER; apply Eimg_env).
  paj_run_to_tok RUNTO HS2 HJ2 SHOK2 cw3_Bspan CW_KR.
  { apply (awr_ok_nil SEGS B). }
  pmkst HS2. cw3_mdv mdk.
  lazymatch type of HS2 with context [restrict _ ?m] => rename m into msb end.
  pose proof (cw3_frame_ro (cw3_ER regs2) (ss_mem (ss_cw3A 0)) mem2 _ ltac:(constructor) HF) as HEQ2.
  prreg HS2 (2%bv : bv 5) T2. prreg HS2 (3%bv : bv 5) T3. prreg HS2 (4%bv : bv 5) T4. prreg HS2 (8%bv : bv 5) T8.
  prreg HS2 (9%bv : bv 5) T9. prreg HS2 (18%bv : bv 5) T18. prreg HS2 (19%bv : bv 5) T19. prreg HS2 (24%bv : bv 5) T24.
  rewrite (cw3_ER_reg regs2 2 2%bv eq_refl) in T2. rewrite (cw3_ER_reg regs2 3 3%bv eq_refl) in T3.
  rewrite (cw3_ER_reg regs2 4 4%bv eq_refl) in T4. rewrite (cw3_ER_reg regs2 8 8%bv eq_refl) in T8.
  rewrite (cw3_ER_reg regs2 9 9%bv eq_refl) in T9. rewrite (cw3_ER_reg regs2 18 18%bv eq_refl) in T18.
  rewrite (cw3_ER_reg regs2 19 19%bv eq_refl) in T19. rewrite (cw3_ER_reg regs2 24 24%bv eq_refl) in T24.
  pose proof (cw3_fi_ext c 0 ly3 (set_fs f S3) W2 regs2 mem2 md2 _ _ mdk HFI2 HJ2 HEQ2 T2 T3 T4 T8 T9 T18 T19 T24)
    as HFIk.
  pose proof (cw3_un_ext c ly3 (set_fs f S3) W2 mem2 _ HEQ2 HUN2) as HUNk.
  (* number refused a member: chain_words_m rejects, chain_run answers err_invalid_operation *)
  pose proof (cw3_chain_none (x_R c) (x_tks c) (Z.to_nat j) wd ltac:(lia) Hwdn Hnum) as HCR.
  unfold from_KR, cw_from in HKR.
  apply (HKR ly3 (set_fs f S3) W2 (ms_regs msb) (ms_mem msb) mdk). unfold INV_KR. exact (conj (conj HFIk HUNk) HCR).
Qed.


End e.
End f.
End d.
