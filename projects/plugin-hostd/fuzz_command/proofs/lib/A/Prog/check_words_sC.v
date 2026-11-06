(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: segment D of check_words' ASan walk (plugin-hostd/fuzz_command, 0x87c90 .. 0x87d64), in the form of lib/A/Prog/sup_reply_code.v and proofs/cgif/cgif_file_fuzzer/lib/A/AChc.v (seeds, symbolic runs, calls). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_words_sD.v, with its module names changed; 404 of its 602 lines of code are new or changed and 1462 lines of the source are left out. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaCall PaCallRun PaDenot PaSB PaLibF PaLibG PaLibH.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtString RtNumber RtFormat RtAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo CmdAddr PaArt.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv CommandModel printf_facts_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
joined_c check_words_add_c check_words_chain_c check_words_pin_set_c sup_reply_code_c HarnessPropsA check_words_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import check_words_d.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the statement's hypotheses (check_words_c.v:88-104), word for word *)
Hypothesis HJOINED : tjoined_spec B MT.
Hypothesis HADD : tcheck_words_add_spec B MT.
Hypothesis HCHAIN : tcheck_words_chain_spec B MT.
Hypothesis HPIN : tcwps_spec B MT.
Hypothesis AFREE4 : afree04_rule SEGS B MT.
Hypothesis ASMALLOC0 : astack_malloc_realizes SEGS B 0.
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis ASTRSPN : astrspn_realizes SEGS B (SIG CS___interceptor_trampoline_strspn) 0xa7098 0x6045d8.
Hypothesis ASTRCSPN : astrcspn_realizes SEGS B (SIG CS___interceptor_trampoline_strcspn) 0xa7098 0x6045d8.
Hypothesis ASTRCMP : astrcmp_realizes SEGS B (SIG CS___interceptor_trampoline_strcmp).
Hypothesis AATOI : aatoi_realizes SEGS B (SIG CS___interceptor_trampoline_atoi) 0xae8d5 0xa7098 0x6045d8.
Hypothesis ASNPRINTF : asnprintf_realizes SEGS B (SIG CS___interceptor_trampoline_snprintf) 0xa7098 0x6045d8.
(* the per-binary walk facts *)
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis MTL : ameter_laws MT.
Hypothesis MTFL : ameter_fs_laws MT.
Hypothesis RRO : RRO_P.
Hypothesis SIGP : cmd_sig_prog.
(* the record facts of lib/A/Prog/CmdRecFacts.v, carried until that file lands *)
Hypothesis cmd_rec_cells : cmd_rec_cells_P B.
Hypothesis cmd_rom_view_on : cmd_rom_view_on_P B.
Hypothesis cmd_heap_tail_vis : cmd_heap_tail_vis_P B.
Hypothesis cmd_prog_unowned : cmd_prog_unowned_P B.
Hypothesis ZSH_cw : CW_ZSH_P B.
Hypothesis cw_ro_unowned : cw_ro_unowned_P B.
Hypothesis cmd_tail_vis : cmd_tail_vis_P B.
Hypothesis cmd_got_rec : cmd_got_rec_P B.
Let errno_low := pal_env B TL.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_cmd) (PI := PI).

(* ---------------------------------------------------------------------------------------------------------- *)
(* Segment C (0x87a7c .. 0x87b00; listing 0x1598 .. 0x161c), the head of the call loop at call c, with
   X = A_G_REC + 56 c (call c's record starts at X + 16): c is stored at s1 + 80; s11 = &call->nargs = X + 20 and
   its inline check; call->nargs is loaded; cp = X + 16 and cp / 8 are stored at s1 + 120 and s1 + 112; `blez nargs`
   (0x87ab8) goes to D (0x87c90) when the call has no argument. Otherwise the inline check of cp, call->fn is loaded,
   the table slot g_call_words[fn] = 0xa5dc0 + 8 fn and its inline check, the template pointer is loaded into s2,
   s10 = 0, s4 = s9 = &call->args[0], and the item loop's head IH (0x87b00) follows. Every inline check is removed by
   the token engine (call c's record lies in g_rec, the slot in the table, both in CW_ZSH).
   Seed: atoms 9 = sp1, 19 = A_G_REC, 20 = c, 23 = SB; extra atoms 32 = X, 33 = fn, 34 = nargs,
   35 = 0xa5dc0 + 8 fn, 36 = cw_tptr fn; the two aliases resolve the engine's forms of X and of the slot. *)
Definition cBx : sv := SOff 23 0.
Definition cBspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition c_regions : smem :=
[ YP09.mkRegion (Some 9%nat) 56 64 0 0 [YP09.mkChunk 56 (CVal 8 (SLit 0xa5dc0))];
  YP09.mkRegion (Some 9%nat) 80 88 80 88 [];
  YP09.mkRegion (Some 9%nat) 112 128 112 128 [];
  YP09.mkRegion (Some 9%nat) 128 144 0 0 [YP09.mkChunk 128 (CVal 8 (SOff 32 24)); YP09.mkChunk 136 (CVal 8 (SOff 32 24))];
  YP09.mkRegion (Some 32%nat) 16 24 0 0 [YP09.mkChunk 16 (CVal 4 (SOff 33 0)); YP09.mkChunk 20 (CVal 4 (SOff 34 0))];
  YP09.mkRegion (Some 35%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 36 0))] ].
Definition c_atoms : list (nat * afact) :=
[ (9%nat, mkAF (2^46) (2^47) 5); (19%nat, mkAF A_G_REC A_G_REC 3); (20%nat, mkAF 0 15 0); (23%nat, mkAF SB SB 0);
  (32%nat, mkAF A_G_REC (A_G_REC + 56 * 15) 3); (33%nat, mkAF 0 25 0); (34%nat, mkAF 0 6 0);
  (35%nat, mkAF 0xa5dc0 (0xa5dc0 + 200) 3); (36%nat, mkAF 0x21280 0x21aa0 0) ].
Definition c_alias : list (sv * sv) :=
[ (SAlu ALU_ADD (SOff 19 0) (SMd M_MUL (SOff 20 0) (SLit 56)), SOff 32 0);
  (SAlu ALU_ADD (SAlu ALU_SLL (SOff 33 0) (SLit 3)) (SLit 0xa5dc0), SOff 35 0) ].
Definition ssC : sstate := mkSS CW_PC_LH sr_atoms c_regions None (mkFacts c_atoms [] c_alias).
Definition c_SH : list shent := [mkSHE 32 16 72; mkSHE 35 0 8].
Definition c_extra (c fn nargs : Z) : list word :=
[Z_to_bv 64 (A_G_REC + 56 * c); Z_to_bv 64 fn; Z_to_bv 64 nargs; Z_to_bv 64 (0xa5dc0 + 8 * fn); Z_to_bv 64 (cw_tptr fn)].
(* the two stack windows the segment writes: s1 + 80 (c) and s1 + 112 .. s1 + 128 (cp / 8, cp) *)
Definition cwZ (sp1 a : Z) : Prop := (sp1 + 80 <= a < sp1 + 88) \/ (sp1 + 112 <= a < sp1 + 128).
Definition cwc_wok (ws : list (option nat * Z * Z)) : bool :=
forallb (fun w => match w with (b, lo, hi) =>
  (hi <=? lo) || (match b with Some n => Nat.eqb n 9 | None => false end &&
    (((80 <=? lo) && (hi <=? 88)) || ((112 <=? lo) && (hi <=? 128)))) end) ws.

(* ---------------------------------------------------------------------------------------------------------- *)
(* the template table, per recorded function *)
Lemma cwc_fn_cases : forall fn, 0 <= fn < 26 ->
  fn = 0 \/ fn = 1 \/ fn = 2 \/ fn = 3 \/ fn = 4 \/ fn = 5 \/ fn = 6 \/ fn = 7 \/ fn = 8 \/ fn = 9 \/ fn = 10 \/
  fn = 11 \/ fn = 12 \/ fn = 13 \/ fn = 14 \/ fn = 15 \/ fn = 16 \/ fn = 17 \/ fn = 18 \/ fn = 19 \/ fn = 20 \/
  fn = 21 \/ fn = 22 \/ fn = 23 \/ fn = 24 \/ fn = 25.
Proof. intros fn H. lia. Qed.
Ltac cwc_fn_split H := repeat (destruct H as [H|H]; [subst; vm_compute; reflexivity|]); subst; vm_compute; reflexivity.

(* the code's parse of each template is the model's item list *)
Lemma cw_parse_tpl : forall fn, 0 <= fn < 26 -> cw_parse (cw_tpl fn) = PCW.call_items fn.
Proof. intros fn H. apply cwc_fn_cases in H. cwc_fn_split H. Qed.

Lemma cwc_tptr_b : forall fn, 0 <= fn < 26 -> (0x21280 <=? cw_tptr fn) && (cw_tptr fn <=? 0x21aa0) = true.
Proof. intros fn H. apply cwc_fn_cases in H. cwc_fn_split H. Qed.
Lemma cwc_tptr_rng : forall fn, 0 <= fn < 26 -> 0x21280 <= cw_tptr fn <= 0x21aa0.
Proof.
intros fn H. pose proof (cwc_tptr_b fn H) as Hb. apply andb_prop in Hb as [H1 H2].
apply Z.leb_le in H1. apply Z.leb_le in H2. lia.
Qed.
Lemma cwc_tbl_b : forall fn, 0 <= fn < 26 ->
  forallb (fun k => bv_unsigned (nth (Z.to_nat (8 * fn) + k) RO_g_call_words (Z_to_bv 8 0)) =? YG0f.le_byte (cw_tptr fn) 8 k)
    (seq 0 8) = true.
Proof. intros fn H. apply cwc_fn_cases in H. cwc_fn_split H. Qed.
Lemma cwc_tbl : forall (rd : reader) fn, abytes_atR rd 0xa5dc0 RO_g_call_words -> 0 <= fn < 26 ->
  aval_mem rd (0xa5dc0 + 8 * fn) 8 (cw_tptr fn).
Proof.
intros rd fn H Hfn k Hk.
pose proof (cwc_tbl_b fn Hfn) as Hb. rewrite forallb_forall in Hb.
assert (Hin : In k (seq 0 8)) by (apply in_seq; lia).
specialize (Hb k Hin). apply Z.eqb_eq in Hb. rewrite <- Hb.
assert (Hlen : length RO_g_call_words = 208%nat) by (vm_compute; reflexivity).
replace (0xa5dc0 + 8 * fn + Z.of_nat k) with (0xa5dc0 + Z.of_nat (Z.to_nat (8 * fn) + k)) by lia.
apply H. lia.
Qed.
Lemma cwc_tbl_of_ro : forall rd, cmd_ro_bytes rd -> abytes_atR rd 0xa5dc0 RO_g_call_words.
Proof.
intros rd H. unfold cmd_ro_bytes in H.
repeat lazymatch type of H with
| abytes_atR _ 0xa5dc0 _ /\ _ => exact (proj1 H)
| _ /\ _ => apply proj2 in H
end.
Qed.

(* ---------------------------------------------------------------------------------------------------------- *)
(* small facts *)
Lemma cwc_aval_eq : forall (rd rd' : reader) a n v,
  (forall k, (k < n)%nat -> rd' (a + Z.of_nat k) = rd (a + Z.of_nat k)) -> aval_mem rd a n v -> aval_mem rd' a n v.
Proof. intros rd rd' a n v Hk H k Hk'. rewrite (Hk k Hk'). exact (H k Hk'). Qed.
Lemma cwc_aval_keep : forall (rd rd' : reader) sp1 a n v,
  (forall x, 0 <= x < 2 ^ 64 -> ~ cwZ sp1 x -> rd' x = rd x) -> 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  (a + Z.of_nat n <= sp1 + 80 \/ (sp1 + 88 <= a /\ a + Z.of_nat n <= sp1 + 112) \/ sp1 + 128 <= a) ->
  aval_mem rd a n v -> aval_mem rd' a n v.
Proof. intros rd rd' sp1 a n v K H0 H1 H2 H k Hk. rewrite K; [exact (H k Hk) | lia | unfold cwZ; lia]. Qed.
Lemma cwc_val_of_aval : forall H (mem : word -> option byte) a (n : nat) v,
  aval_mem (aview SEGS H mem) a n v -> val_mem SEGS (mrestrict H mem) a n v.
Proof.
intros H mem a n v Hv k Hk. specialize (Hv k Hk). unfold aview in Hv.
destruct (mbyte SEGS (mrestrict H mem) (a + Z.of_nat k)) as [b|] eqn:Hb; [|discriminate].
cbn in Hv. injection Hv as Hv. rewrite <- (Z_to_bv_bv_unsigned _ b) at 1. do 2 f_equal. exact Hv.
Qed.
Lemma cwc_aval_of_val : forall H (m : word -> option byte) a n v,
  val_mem SEGS (mrestrict H m) a n v -> aval_mem (aview SEGS H m) a n v.
Proof.
intros H m a n v Hv k Hk. unfold aview. rewrite (Hv k Hk). cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 8) with 256. apply Z.mod_pos_bound. lia.
Qed.
Lemma cwc_DO : forall E n v off, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + off < 2 ^ 64 ->
  sv_denot E (SOff n off) = Z_to_bv 64 (v + off).
Proof.
intros E n v off Hn Hv Hvo.
rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E (SOff n off))). f_equal.
change (U E (SOff n off) = v + off). apply U_atom_off; [exact Hn | lia | lia].
Qed.
Lemma cwc_srl3 : forall E n c v, ew E n = Z_to_bv 64 v -> 0 <= v -> 0 <= c -> v + c < 2 ^ 63 ->
  sv_denot E (SAlu ALU_SRL (SOff n c) (SLit 3)) = Z_to_bv 64 ((v + c) / 8).
Proof.
intros E n c v Hn Hv Hc Hvc.
rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E (SAlu ALU_SRL (SOff n c) (SLit 3)))). f_equal.
change (U E (SAlu ALU_SRL (SOff n c) (SLit 3)) = (v + c) / 8).
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SOff, Hn. rewrite unsigned_lit_small by lia.
change (Z.land (U E (SLit 3)) 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
pose proof (Z.div_pos (v + c) 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_lt_upper_bound (v + c) 8 (2 ^ 60) ltac:(lia) ltac:(lia)).
rewrite (zcanon_small (v + c)) by lia. rewrite zcanon_small by lia. reflexivity.
Qed.
Lemma cwc_ge0 : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 63 ->
  branch_taken BC_GE (sv_denot E (SLit 0)) (sv_denot E (SOff n 0)) = negb (0 <? v).
Proof.
intros E n v Hn Hv. cbn [branch_taken]. rewrite bv_lts_signed.
change (bv_signed (sv_denot E (SLit 0))) with (Sg E (SLit 0)).
change (bv_signed (sv_denot E (SOff n 0))) with (Sg E (SOff n 0)).
rewrite S_SLit, S_SOff, Hn, Z.add_0_r, unsigned_lit_small by lia. rewrite !swrap64_id by (unfold half64; lia). reflexivity.
Qed.
Lemma cwc_join_len : forall ws, Z.of_nat (length (join_sp ws)) <= PJn.join_need ws.
Proof.
induction ws as [|w ws IH].
- unfold PJn.join_need. cbn [length fold_right]. apply Z.le_refl.
- assert (E : join_sp (w :: ws) = match ws with [] => w | _ :: _ => w ++ SPACE :: join_sp ws end) by reflexivity.
  rewrite E. unfold PJn.join_need in *. cbn [fold_right].
  assert (0 <= fold_right (fun w acc => Z.of_nat (length w) + 1 + acc) 0 ws).
  { clear IH E. induction ws as [|w1 ws1 IH1]; cbn [fold_right]; [apply Z.le_refl|].
    pose proof (Nat2Z.is_nonneg (length w1)). lia. }
  destruct ws as [|w2 ws2]; cbv beta iota; [lia|]. rewrite length_app. cbn [length]. lia.
Qed.
Lemma cwc_kept : forall E rs H (m m' : word -> option byte) sp1,
  frame_of E rs (mrestrict H m) (mrestrict H m') -> bv_unsigned (ew E 9) = sp1 -> cwc_wok (windows rs) = true ->
  forall a, 0 <= a < 2 ^ 64 -> ~ cwZ sp1 a -> aview SEGS H m' a = aview SEGS H m a.
Proof.
intros E rs H m m' sp1 HF H9 Hw. apply (kept_of_frame E rs H m m' (cwZ sp1) HF).
intros b wlo whi a Hin Ha. unfold cwc_wok in Hw. rewrite forallb_forall in Hw. specialize (Hw _ Hin). cbn beta iota in Hw.
apply orb_prop in Hw as [Hw|Hw]; [apply Z.leb_le in Hw; lia|].
apply andb_prop in Hw as [Hb Hw].
destruct b as [n|]; cbn beta iota in Hb; [|discriminate Hb]. apply Nat.eqb_eq in Hb. subst n.
cbn [base_val] in Ha. rewrite H9 in Ha. unfold cwZ.
apply orb_prop in Hw as [Hw|Hw]; apply andb_prop in Hw as [H1 H2]; apply Z.leb_le in H1; apply Z.leb_le in H2; lia.
Qed.

(* ---------------------------------------------------------------------------------------------------------- *)
(* memory the walk never writes, at the current state: g_rec and the table *)
Lemma cwc_img_kept : forall STK sp0 ly S W0 mem md own lyc Sc (W : world SEGS) memc mdc k a,
  ajournal SEGS B STK sp0 [] ly S W0 mem md own lyc Sc W memc mdc k ->
  in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  rdW W memc a = rdW W0 mem a.
Proof.
intros STK sp0 ly S W0 mem md own lyc Sc W memc mdc k a HJ Hi Ho He.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Kimg & _).
apply Kimg; [exact Hi | exact Ho | exact He | exact (fp_spares_closed [] a sink_closed_nil (inFP_nil a))].
Qed.
Lemma cwc_grec_kept : forall STK sp0 ly S W0 mem md own lyc Sc (W : world SEGS) memc mdc k a,
  ajournal SEGS B STK sp0 [] ly S W0 mem md own lyc Sc W memc mdc k ->
  A_G_REC <= a < A_G_REC + 960 -> rdW W memc a = rdW W0 mem a.
Proof.
intros STK sp0 ly S W0 mem md own lyc Sc W memc mdc k a HJ Ha.
assert (Hpg : inFP cmd_PG a) by (exists (A_G_REC, A_G_REC + 960); split; [unfold cmd_PG; left; reflexivity | cbn [fst snd]; lia]).
destruct (cmd_prog_unowned a Hpg) as (Hi & Ho & He).
exact (cwc_img_kept STK sp0 ly S W0 mem md own lyc Sc W memc mdc k a HJ Hi Ho He).
Qed.
Lemma cwc_tbl_kept : forall STK sp0 ly S W0 mem md own lyc Sc (W : world SEGS) memc mdc k i,
  ajournal SEGS B STK sp0 [] ly S W0 mem md own lyc Sc W memc mdc k ->
  0 <= i < 208 -> rdW W memc (0xa5dc0 + i) = rdW W0 mem (0xa5dc0 + i).
Proof.
intros STK sp0 ly S W0 mem md own lyc Sc W memc mdc k i HJ Hi.
destruct (cw_ro_unowned 0xa5dc0 208 i ltac:(unfold CW_ZSH; right; left; reflexivity) ltac:(unfold A_G_REC; lia) Hi)
  as (Hin & Ho & He).
exact (cwc_img_kept STK sp0 ly S W0 mem md own lyc Sc W memc mdc k _ HJ Hin Ho He).
Qed.

(* call c's function, argument count and template pointer, at the current state *)
Lemma cwc_vals : forall e lyc Sc Wc memc mdc pos k c,
  cw_ent B MT e ->
  ajournal SEGS B CHECK_WORDS_STK (cw_sp0 e) [] (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) [(0, pos)]
    lyc Sc Wc memc mdc k ->
  0 <= c < cw_ncalls e ->
  exists fn args, nth_error (r_calls (e_R e)) (Z.to_nat c) = Some (fn, args) /\
    0 <= fn < 26 /\ (length args <= 6)%nat /\ c <= 15 /\
    aval_mem (rdW Wc memc) (A_G_REC + 56 * c + 16) 4 fn /\
    aval_mem (rdW Wc memc) (A_G_REC + 56 * c + 20) 4 (Z.of_nat (length args)) /\
    aval_mem (rdW Wc memc) (0xa5dc0 + 8 * fn) 8 (cw_tptr fn).
Proof.
intros e lyc Sc Wc memc mdc pos k c Hent HJ Hc.
unfold cw_ent in Hent. cbv zeta in Hent.
destruct Hent as (_ & _ & _ & _ & HRO & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hrec & _).
destruct Hrec as (Q & (_ & _ & _ & (Hl & HlQ & _ & Hcalls & _) & _) & _).
unfold cw_ncalls in Hc.
destruct (nth_error (r_calls (e_R e)) (Z.to_nat c)) as [[fn args]|] eqn:Hn;
  [| exfalso; apply nth_error_None in Hn; lia].
destruct (nth_error (l_calls Q) (Z.to_nat c)) as [P|] eqn:HP;
  [| exfalso; apply nth_error_None in HP; lia].
destruct (Hcalls _ _ _ Hn HP) as ((Hfn & Hla & _ & Hvfn & Hvna & _) & _).
cbn [fst snd] in Hfn, Hla, Hvfn, Hvna. unfold REC_FN_COUNT in Hfn.
replace (A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat (Z.to_nat c) + CALL_OFF_FN) with (A_G_REC + 56 * c + 16) in Hvfn
  by (unfold OFF_CALLS, CALL_SIZE, CALL_OFF_FN; lia).
replace (A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat (Z.to_nat c) + CALL_OFF_NARGS) with (A_G_REC + 56 * c + 20) in Hvna
  by (unfold OFF_CALLS, CALL_SIZE, CALL_OFF_NARGS; lia).
destruct HRO as [HB _]. pose proof (cwc_tbl _ fn (cwc_tbl_of_ro _ HB) Hfn) as Htb.
exists fn, args. split; [reflexivity|]. split; [exact Hfn|]. split; [exact Hla|]. split; [lia|].
split; [apply (cwc_aval_eq (cw_rd0 e)); [intros kk Hk; apply (cwc_grec_kept _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ); lia | exact Hvfn]|].
split; [apply (cwc_aval_eq (cw_rd0 e)); [intros kk Hk; apply (cwc_grec_kept _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ); lia | exact Hvna]|].
apply (cwc_aval_eq (cw_rd0 e)); [|exact Htb].
intros kk Hk. replace (0xa5dc0 + 8 * fn + Z.of_nat kk) with (0xa5dc0 + (8 * fn + Z.of_nat kk)) by lia.
apply (cwc_tbl_kept _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ). lia.
Qed.

(* ---------------------------------------------------------------------------------------------------------- *)
(* the seed at LH *)
Lemma cwc_seed : forall (W : world SEGS) (regsc : bvmap 5 word) memc sp1 c fn nargs,
  getr regsc 9 = w64 sp1 -> 2 ^ 46 <= sp1 <= 2 ^ 47 -> sp1 mod 32 = 0 -> getr regsc 23 = w64 CW_SB ->
  getr regsc 19 = w64 A_G_REC -> getr regsc 20 = w64 c -> 0 <= c <= 15 -> 0 <= fn <= 25 -> 0 <= nargs <= 6 ->
  aval_mem (rdW W memc) (sp1 + 56) 8 0xa5dc0 ->
  aval_mem (rdW W memc) (sp1 + 128) 8 (A_G_REC + 24 + 56 * c) ->
  aval_mem (rdW W memc) (sp1 + 136) 8 (A_G_REC + 24 + 56 * c) ->
  aval_mem (rdW W memc) (A_G_REC + 56 * c + 16) 4 fn ->
  aval_mem (rdW W memc) (A_G_REC + 56 * c + 20) 4 nargs ->
  aval_mem (rdW W memc) (0xa5dc0 + 8 * fn) 8 (cw_tptr fn) ->
  (forall a, sp1 + 80 <= a < sp1 + 128 -> apresent (w_H W) memc a) ->
  range_addressable (rdW W memc) SHADOW_OFF A_G_REC 960 ->
  range_addressable (rdW W memc) SHADOW_OFF 0xa5dc0 208 ->
  st_ok_pi SEGS VAL (Eimg (Ereg regsc (c_extra c fn nargs))) ssC
    (restrict (w_H W) (mkst regsc (Z_to_bv 64 (BASE + CW_PC_LH)) memc (seg_rom SEGS))) /\
  sh_ok SEGS cBx c_SH (Eimg (Ereg regsc (c_extra c fn nargs))) (mrestrict (w_H W) memc).
Proof.
intros W regsc memc sp1 c fn nargs H9 Hsp Hsp32 H23 H19 H20 Hc Hfn Hna V56 V128 V136 VFN VNA VTB HPR RA1 RA2.
assert (HG : A_G_REC = 6174528) by reflexivity.
pose proof (cwc_tptr_rng fn ltac:(lia)) as Htp.
set (E := Eimg (Ereg regsc (c_extra c fn nargs))).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regsc r).
{ intros n r Hn. unfold E. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
assert (ES : forall m, (32 <= m < A_TEXT)%nat -> ew E m = nth (m - 32) (c_extra c fn nargs) (Z_to_bv 64 0)).
{ intros m Hm. replace m with (32 + (m - 32))%nat at 1 by lia. unfold E. rewrite Eimg_low by lia. apply ew_Ereg_extra. }
assert (E9 : ew E 9 = Z_to_bv 64 sp1) by (rewrite (EE 9%nat 9%bv eq_refl); exact H9).
assert (E19 : ew E 19 = Z_to_bv 64 A_G_REC) by (rewrite (EE 19%nat 19%bv eq_refl); exact H19).
assert (E20 : ew E 20 = Z_to_bv 64 c) by (rewrite (EE 20%nat 20%bv eq_refl); exact H20).
assert (E23 : ew E 23 = Z_to_bv 64 2147450880) by (rewrite (EE 23%nat 23%bv eq_refl); exact H23).
pose proof (ES 32%nat ltac:(unfold A_TEXT; lia)) as E32. pose proof (ES 33%nat ltac:(unfold A_TEXT; lia)) as E33.
pose proof (ES 34%nat ltac:(unfold A_TEXT; lia)) as E34. pose proof (ES 35%nat ltac:(unfold A_TEXT; lia)) as E35.
pose proof (ES 36%nat ltac:(unfold A_TEXT; lia)) as E36.
cbn [Nat.sub nth c_extra] in E32, E33, E34, E35, E36.
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
assert (Hx8 : (A_G_REC + 56 * c) mod 8 = 0).
{ replace (A_G_REC + 56 * c) with ((771816 + 7 * c) * 8) by lia. apply Z_mod_mult. }
assert (Hs8 : (0xa5dc0 + 8 * fn) mod 8 = 0).
{ replace (0xa5dc0 + 8 * fn) with ((84920 + fn) * 8) by lia. apply Z_mod_mult. }
split.
- unfold ssC. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  + unfold E. apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold c_regions.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    * rewrite (VB 9%nat sp1 E9) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS E _ sp1 56 8 _ 0xa5dc0); [cbn [sv_denot]; reflexivity | zside | zside |].
      exact (cwc_val_of_aval _ _ _ _ _ V56).
    * rewrite (VB 9%nat sp1 E9) by lia. split; [lia|]. split; [lia|].
      split; [intros o Ho; apply (apresent_writable SEGS); apply HPR; lia|]. apply Forall_nil.
    * rewrite (VB 9%nat sp1 E9) by lia. split; [lia|]. split; [lia|].
      split; [intros o Ho; apply (apresent_writable SEGS); apply HPR; lia|]. apply Forall_nil.
    * rewrite (VB 9%nat sp1 E9) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      -- apply (chunk_ok_val SEGS E _ sp1 128 8 _ (A_G_REC + 24 + 56 * c));
           [rewrite (cwc_DO E 32 _ 24 E32) by lia; f_equal; lia | zside | zside |].
         exact (cwc_val_of_aval _ _ _ _ _ V128).
      -- apply (chunk_ok_val SEGS E _ sp1 136 8 _ (A_G_REC + 24 + 56 * c));
           [rewrite (cwc_DO E 32 _ 24 E32) by lia; f_equal; lia | zside | zside |].
         exact (cwc_val_of_aval _ _ _ _ _ V136).
    * rewrite (VB 32%nat (A_G_REC + 56 * c) E32) by lia. split; [lia|]. split; [lia|].
      split; [intros o Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      -- apply (chunk_ok_val SEGS E _ (A_G_REC + 56 * c) 16 4 _ fn);
           [rewrite (cwc_DO E 33 fn 0 E33) by lia; f_equal; lia | zside | zside |].
         exact (cwc_val_of_aval _ _ _ _ _ VFN).
      -- apply (chunk_ok_val SEGS E _ (A_G_REC + 56 * c) 20 4 _ nargs);
           [rewrite (cwc_DO E 34 nargs 0 E34) by lia; f_equal; lia | zside | zside |].
         exact (cwc_val_of_aval _ _ _ _ _ VNA).
    * rewrite (VB 35%nat (0xa5dc0 + 8 * fn) E35) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS E _ (0xa5dc0 + 8 * fn) 0 8 _ (cw_tptr fn));
        [rewrite (cwc_DO E 36 _ 0 E36) by lia; f_equal; lia | zside | zside |].
      rewrite Z.add_0_r. exact (cwc_val_of_aval _ _ _ _ _ VTB).
  + apply pairwise_disjoint_of_extents. unfold c_regions, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (VB 9%nat sp1 E9) by lia. rewrite (VB 32%nat (A_G_REC + 56 * c) E32) by lia.
    rewrite (VB 35%nat (0xa5dc0 + 8 * fn) E35) by lia.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
  + unfold facts_ok. cbn [f_atoms f_conds f_alias]. split; [|split; [exact I|]].
    * unfold c_atoms. cbn [atoms_ok]. unfold afact_ok; cbn [af_lo af_hi af_al2].
      rewrite E9, E19, E20, E23, E32, E33, E34, E35, E36.
      rewrite !unsigned_lit_small by (rewrite ?HG; lia).
      rewrite ?Z.pow_0_r, ?Z.mod_1_r. change (2 ^ 5) with 32. change (2 ^ 3) with 8.
      unfold SB.
      repeat match goal with |- _ /\ _ => split end;
        first [exact I | lia | exact Hsp32 | exact Hx8 | exact Hs8 | reflexivity].
    * unfold c_alias. cbn [alias_ok]. split; [|split; [|exact I]]; apply U_inj.
      -- rewrite U_SAlu, U_SMd. cbn [zalu_raw zmd_raw].
         rewrite (U_atom E 19 A_G_REC E19) by lia. rewrite (U_atom E 20 c E20) by lia.
         rewrite (U_atom E 32 _ E32) by lia. rewrite U_SLit.
         change (zcanon 56) with 56. rewrite (zcanon_small (c * 56)) by lia.
         rewrite zcanon_small by lia. lia.
      -- rewrite !U_SAlu. cbn [zalu_raw].
         rewrite (U_atom E 33 fn E33) by lia. rewrite (U_atom E 35 _ E35) by lia. rewrite !U_SLit.
         change (Z.land (zcanon 3) 63) with 3. change (zcanon 0xa5dc0) with 0xa5dc0.
         rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8.
         rewrite (zcanon_small (fn * 8)) by lia. rewrite zcanon_small by lia. lia.
- unfold sh_ok, c_SH. repeat apply Forall_cons; try apply Forall_nil.
  + apply (shent_ok_of_range SEGS (w_H W) memc E cBx 32 A_G_REC 960 (A_G_REC + 56 * c) 16 72 RA1).
    * unfold cBx. rewrite (U_atom E 23 _ E23) by lia. reflexivity.
    * apply (U_atom E 32 _ E32). lia.
    * lia.
    * lia.
    * intros x Hx. cbn [Z.min Z.max] in Hx. unfold SHADOW_OFF. lia.
  + apply (shent_ok_of_range SEGS (w_H W) memc E cBx 35 0xa5dc0 208 (0xa5dc0 + 8 * fn) 0 8 RA2).
    * unfold cBx. rewrite (U_atom E 23 _ E23) by lia. reflexivity.
    * apply (U_atom E 35 _ E35). lia.
    * lia.
    * lia.
    * intros x Hx. cbn [Z.min Z.max] in Hx. unfold SHADOW_OFF. lia.
Qed.

(* ---------------------------------------------------------------------------------------------------------- *)
(* the parts of the invariant the segment does not change, at the state after its runs *)
Lemma cwc_common : forall e lyc Sc Wc regsc memc mdc regs2 mem2 mdc2 pos sp1 line c,
  cw_core B e lyc Sc Wc regsc memc mdc pos sp1 EV_JOINED ->
  cw_line B MT e lyc Sc (rdW Wc memc) line ->
  cw_lscr e (rdW Wc memc) sp1 (frame_addr (e_ly e) 0 pos) line c ->
  ajournal SEGS B CHECK_WORDS_STK (cw_sp0 e) [] (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) [(0, pos)]
    lyc Sc Wc mem2 mdc2 EV_JOINED ->
  getr regs2 2 = getr regsc 2 -> getr regs2 3 = getr regsc 3 -> getr regs2 4 = getr regsc 4 ->
  getr regs2 8 = getr regsc 8 -> getr regs2 9 = getr regsc 9 -> getr regs2 23 = getr regsc 23 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ cwZ sp1 a -> rdW Wc mem2 a = rdW Wc memc a) ->
  cw_core B e lyc Sc Wc regs2 mem2 mdc2 pos sp1 EV_JOINED /\ cw_line B MT e lyc Sc (rdW Wc mem2) line /\
  cw_lscr e (rdW Wc mem2) sp1 (frame_addr (e_ly e) 0 pos) line c.
Proof.
intros e lyc Sc Wc regsc memc mdc regs2 mem2 mdc2 pos sp1 line c HC HL HS HJ2 R2 R3 R4 R8 R9 R23 KEEP.
destruct HC as (HJ & Hsp & Hsp32 & Hspr & H3 & H4 & H8 & H9 & H23 & Hsav & V16 & V24 & V32 & V152 & V56F & SB4 & SB5).
pose proof HJ2 as (HAR & Hly & _ & _ & _ & Hfr & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _ & _).
destruct Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & _).
assert (HSTK : CHECK_WORDS_STK = 16800) by (vm_compute; reflexivity).
assert (HF : 4096 <= frame_addr (e_ly e) 0 pos /\ frame_addr (e_ly e) 0 pos + 64 <= alloc_ceiling).
{ assert (Hin : In (0, pos) (frames Sc)) by (rewrite Hfr; apply in_or_app; left; left; reflexivity).
  destruct (frames_bounds SEGS B LAWS lyc Sc Wc mem2 mdc2 0 pos HAR Hin) as (Hf1 & Hf2 & _).
  assert (Hfa : frame_addr lyc 0 pos = frame_addr (e_ly e) 0 pos).
  { unfold frame_addr. destruct Hly as (_ & _ & _ & _ & _ & HlyF & _). rewrite HlyF. reflexivity. }
  assert (Hfb : fs_frame_bytes 0 = 64) by (vm_compute; reflexivity).
  rewrite Hfa, Hfb in *. lia. }
pose proof (Z.div_pos (frame_addr (e_ly e) 0 pos) 8 ltac:(lia) ltac:(lia)) as HF8a.
pose proof (Z.div_le_upper_bound (frame_addr (e_ly e) 0 pos) 8 (2 ^ 44) ltac:(lia) ltac:(lia)) as HF8b.
split; [|split].
- split; [exact HJ2|]. split; [unfold spZ in *; rewrite R2; exact Hsp|]. split; [exact Hsp32|]. split; [exact Hspr|].
  split; [rewrite R3; exact H3|]. split; [rewrite R4; exact H4|]. split; [rewrite R8; exact H8|].
  split; [rewrite R9; exact H9|]. split; [rewrite R23; exact H23|].
  split.
  { intros j r Hj. assert (Hj13 : (j < length cw_saved)%nat) by (apply nth_error_Some; rewrite Hj; discriminate).
    cbn [length cw_saved] in Hj13.
    apply (cwc_aval_keep _ _ sp1 _ _ _ KEEP); [lia | lia | lia | exact (Hsav j r Hj)]. }
  split; [apply (cwc_aval_keep _ _ sp1 _ _ _ KEEP); [lia | lia | lia | exact V16]|].
  split; [apply (cwc_aval_keep _ _ sp1 _ _ _ KEEP); [lia | lia | lia | exact V24]|].
  split; [apply (cwc_aval_keep _ _ sp1 _ _ _ KEEP); [lia | lia | lia | exact V32]|].
  split; [apply (cwc_aval_keep _ _ sp1 _ _ _ KEEP); [lia | lia | lia | exact V152]|].
  split; [apply (cwc_aval_keep _ _ sp1 _ _ _ KEEP); [lia | lia | lia | exact V56F]|].
  split; (rewrite KEEP; [assumption | unfold CW_SB; lia | unfold cwZ, CW_SB; lia]).
- destruct HL as (Hperm & H4096 & Hfa & Hbytes & Hmo).
  split; [exact Hperm|]. split; [exact H4096|]. split; [exact Hfa|]. split; [|exact Hmo].
  assert (Hin : In (line, cw_JN e) (ablocks B lyc Sc)) by (apply (Permutation_in _ (Permutation_sym Hperm)); left; reflexivity).
  destruct (al_blocks _ _ LAWS lyc Sc Wc mem2 mdc2 line (cw_JN e) HAR Hin) as (_ & Hl4096 & Hlceil & _).
  pose proof (cwc_join_len (e_ws e)) as HJL.
  assert (HRS : req_size (cw_JN e) = cw_JN e) by (unfold req_size, cw_JN in *; destruct (Z.eqb_spec (PJn.join_need (e_ws e) + 1) 0); lia).
  rewrite HRS in Hlceil. unfold cw_JN in Hlceil.
  intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
  rewrite KEEP; [exact (Hbytes i ltac:(rewrite length_app; cbn [length]; lia)) | lia | unfold cwZ; lia].
- destruct HS as (V144 & V8 & V40 & V48 & V56 & V64 & V72 & V88 & V96 & V104 & V128 & V136).
  repeat split; apply (cwc_aval_keep _ _ sp1 _ _ _ KEEP); first [lia | assumption].
Qed.

(* ---------------------------------------------------------------------------------------------------------- *)
(* the walk's tactics *)
Ltac cwc_awr sp1 sp0 U9 :=
  lazymatch goal with |- awr_ok ?sg ?bb ?E ?rs ?stk ?s0 ?fp ?b0 ?bc ?fr ?ly ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sg bb E rs' stk s0 fp b0 bc fr ly own) end;
  repeat first
  [ apply awr_ok_nil
  | apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]
  | eapply awr_ok_cons_stack_off with (n := 9%nat) (d := sp1 - sp0);
    [reflexivity | rewrite U9; lia | cbn [YP09.r_wlo YP09.r_whi]; lia | cbn [YP09.r_wlo YP09.r_whi]; lia |] ].
Ltac cwc_keep sp1 U9 K :=
  lazymatch goal with HFr : frame_of ?E _ (mrestrict ?H ?m0) (mrestrict _ ?m1) |- _ =>
    pose proof (cwc_kept E _ H m0 m1 sp1 HFr U9 ltac:(vm_compute; reflexivity)) as K; clear HFr end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
Ltac cwc_reg HS r Hr :=
  lazymatch type of HS with st_ok_pi _ _ ?E ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr end.

(* ---------------------------------------------------------------------------------------------------------- *)
(* the segment *)
Lemma seg_C : forall c, ST_IH B MT c 0 -> ST_D B MT c -> ST_LH B MT c.
Proof.
intros c HIH HD. unfold ST_IH, cw_at in HIH. unfold ST_D, cw_at in HD.
unfold ST_LH. intros e lyc Sc Wc regsc memc mdc pos sp1 line Hent HI.
destruct HI as (HC & HL & HS0 & H19 & H20 & H24 & Hcr).
pose proof HC as (HJ & Hsp & Hsp32 & Hspr & _ & _ & _ & H9 & H23 & _).
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _ & _).
pose proof Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & _).
assert (HSTK : CHECK_WORDS_STK = 16800) by (vm_compute; reflexivity).
assert (HG : A_G_REC = 6174528) by reflexivity.
destruct (cwc_vals e lyc Sc Wc memc mdc pos EV_JOINED c Hent HJ Hcr)
  as (fn & args & Hnth & Hfn & Hla & Hc15 & VFN & VNA & VTB).
pose proof (cwc_tptr_rng fn Hfn) as Htp.
pose proof (Z.div_pos (A_G_REC + 16 + 56 * c) 8 ltac:(lia) ltac:(lia)) as Hd1.
pose proof (Z.div_le_upper_bound (A_G_REC + 16 + 56 * c) 8 (2 ^ 60) ltac:(lia) ltac:(lia)) as Hd2.
pose proof HS0 as (_ & _ & _ & _ & V56 & _ & _ & _ & _ & _ & V128 & V136).
destruct (ZSH_cw lyc Sc Wc memc mdc A_G_REC 960 HAR ltac:(unfold CW_ZSH; left; reflexivity)) as [RA1 _].
destruct (ZSH_cw lyc Sc Wc memc mdc 0xa5dc0 208 HAR ltac:(unfold CW_ZSH; right; left; reflexivity)) as [RA2 _].
assert (Hsp1 : 2 ^ 46 <= sp1 <= 2 ^ 47) by lia.
destruct (cwc_seed Wc regsc memc sp1 c fn (Z.of_nat (length args)) H9 Hsp1 Hsp32 H23 H19 H20 ltac:(lia) ltac:(lia)
  ltac:(lia) V56 V128 V136 VFN VNA VTB ltac:(intros a Ha; apply Hpres; lia) RA1 RA2) as [HS SHOK].
remember (Eimg (Ereg regsc (c_extra c fn (Z.of_nat (length args))))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regsc (c_extra c fn (Z.of_nat (length args)))) E)
  by (split; [intros n Hn; rewrite HE; apply Eimg_low; unfold A_TEXT; lia | rewrite HE; reflexivity]).
assert (EX : forall m, (32 <= m < A_TEXT)%nat -> ew E m = nth (m - 32) (c_extra c fn (Z.of_nat (length args))) (Z_to_bv 64 0)).
{ intros m Hm. replace m with (32 + (m - 32))%nat at 1 by lia. rewrite HE, Eimg_low by lia. apply ew_Ereg_extra. }
assert (E9 : ew E 9 = Z_to_bv 64 sp1).
{ rewrite HE, Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regsc _ 9 9%bv eq_refl). exact H9. }
assert (E20 : ew E 20 = Z_to_bv 64 c).
{ rewrite HE, Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regsc _ 20 20%bv eq_refl). exact H20. }
assert (E23 : ew E 23 = Z_to_bv 64 2147450880).
{ rewrite HE, Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regsc _ 23 23%bv eq_refl). exact H23. }
pose proof (EX 32%nat ltac:(unfold A_TEXT; lia)) as E32. pose proof (EX 34%nat ltac:(unfold A_TEXT; lia)) as E34.
pose proof (EX 36%nat ltac:(unfold A_TEXT; lia)) as E36.
cbn [Nat.sub nth c_extra] in E32, E34, E36.
clear HE EX.
assert (U9 : bv_unsigned (ew E 9) = sp1) by (rewrite E9; apply unsigned_lit_small; lia).
(* the stores of c, cp / 8 and cp, the nargs check, to `blez nargs` *)
unfold cw_at.
paj_run_tok RUN HS HJ SHOK cBspan; [cwc_awr sp1 (cw_sp0 e) U9 |].
set (mdv := with_vm_backing _ _ _) in *; clearbody mdv.
cwc_keep sp1 U9 K1.
lazymatch goal with HS : st_ok_pi _ _ _ _ (restrict _ ?m) |- _ => rename m into ms1 end.
psrr_branch_tok RUN BR HS SHOK cBspan.
- (* nargs <= 0: on to D *)
  paj_run_to_tok RUNTO HS HJ SHOK cBspan CW_PC_D; [cwc_awr sp1 (cw_sp0 e) U9 |].
  set (mdv2 := with_vm_backing _ _ _) in *; clearbody mdv2.
  cwc_keep sp1 U9 K2.
  lazymatch goal with HS : st_ok_pi _ _ _ _ (restrict _ ?m) |- _ => rename m into ms2 end.
  assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ cwZ sp1 a -> rdW Wc (ms_mem ms2) a = rdW Wc memc a)
    by (intros a Ha Hz; rewrite (K2 a Ha Hz); exact (K1 a Ha Hz)).
  pose proof (regs_kept_of_st_ok_pi E _ _ regsc _
    [(2%bv : bv 5); (3%bv : bv 5); (4%bv : bv 5); (8%bv : bv 5); (9%bv : bv 5); (23%bv : bv 5); (24%bv : bv 5)]
    HS HAE ltac:(vm_compute; reflexivity)) as RK.
  pose proof (RK (2%bv : bv 5) ltac:(repeat (first [left; reflexivity | right]))) as R2.
  pose proof (RK (3%bv : bv 5) ltac:(repeat (first [left; reflexivity | right]))) as R3.
  pose proof (RK (4%bv : bv 5) ltac:(repeat (first [left; reflexivity | right]))) as R4.
  pose proof (RK (8%bv : bv 5) ltac:(repeat (first [left; reflexivity | right]))) as R8.
  pose proof (RK (9%bv : bv 5) ltac:(repeat (first [left; reflexivity | right]))) as R9.
  pose proof (RK (23%bv : bv 5) ltac:(repeat (first [left; reflexivity | right]))) as R23.
  pose proof (RK (24%bv : bv 5) ltac:(repeat (first [left; reflexivity | right]))) as R24.
  cbn [ms_regs restrict] in R2, R3, R4, R8, R9, R23, R24.
  destruct (cwc_common e lyc Sc Wc regsc memc mdc (ms_regs ms2) (ms_mem ms2) mdv2 pos sp1 line c HC HL HS0 HJ
    R2 R3 R4 R8 R9 R23 KEEP) as (HC2 & HL2 & HS2).
  pose proof (st_ok_region_nth E _ _ 1 (YP09.mkRegion (Some 9%nat) 80 88 80 88 [YP09.mkChunk 80 (CVal 8 (SOff 20 0))])
    HS ltac:(vm_compute; reflexivity)) as RG1.
  pose proof (st_ok_region_nth E _ _ 2 (YP09.mkRegion (Some 9%nat) 112 128 112 128
    [YP09.mkChunk 112 (CVal 8 (SAlu ALU_SRL (SOff 32 16) (SLit 3))); YP09.mkChunk 120 (CVal 8 (SOff 32 16))])
    HS ltac:(vm_compute; reflexivity)) as RG2.
  cbn [ms_mem restrict] in RG1, RG2.
  assert (CS : cw_cscr (rdW Wc (ms_mem ms2)) sp1 c).
  { split; [|split].
    - apply cwc_aval_of_val. apply (field_of_region E _ 9%nat sp1 _ 80 88 80 88 80 8 (SOff 20 0) c RG1 U9);
        [left; reflexivity | rewrite (cwc_DO E 20 c 0 E20) by lia; f_equal; lia | zside | zside].
    - apply cwc_aval_of_val.
      apply (field_of_region E _ 9%nat sp1 _ 112 128 112 128 112 8 (SAlu ALU_SRL (SOff 32 16) (SLit 3))
        ((A_G_REC + 16 + 56 * c) / 8) RG2 U9);
        [left; reflexivity | rewrite (cwc_srl3 E 32 16 _ E32) by lia; do 2 f_equal; lia | zside | zside].
    - apply cwc_aval_of_val.
      apply (field_of_region E _ 9%nat sp1 _ 112 128 112 128 120 8 (SOff 32 16) (A_G_REC + 16 + 56 * c) RG2 U9);
        [right; left; reflexivity | rewrite (cwc_DO E 32 _ 16 E32) by lia; f_equal; lia | zside | zside]. }
  pmkst HS. change (BASE + 6060) with (BASE + CW_PC_D).
  apply (HD e lyc Sc Wc (ms_regs ms2) (ms_mem ms2) mdv2 pos sp1 line Hent).
  exact (conj HC2 (conj HL2 (conj HS2 (conj CS (conj (eq_trans R24 H24) Hcr))))).
- (* 0 < nargs: on to the item loop's head, item 0, cursor 0 *)
  lazymatch goal with Hb : branch_taken _ _ _ = false |- _ => rename Hb into Hgt end.
  rewrite (cwc_ge0 E 34 _ E34) in Hgt by lia. apply negb_false_iff in Hgt. apply Z.ltb_lt in Hgt.
  paj_run_to_tok RUNTO HS HJ SHOK cBspan CW_PC_IH; [cwc_awr sp1 (cw_sp0 e) U9 |].
  set (mdv2 := with_vm_backing _ _ _) in *; clearbody mdv2.
  cwc_keep sp1 U9 K2.
  lazymatch goal with HS : st_ok_pi _ _ _ _ (restrict _ ?m) |- _ => rename m into ms2 end.
  assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ cwZ sp1 a -> rdW Wc (ms_mem ms2) a = rdW Wc memc a)
    by (intros a Ha Hz; rewrite (K2 a Ha Hz); exact (K1 a Ha Hz)).
  pose proof (regs_kept_of_st_ok_pi E _ _ regsc _
    [(2%bv : bv 5); (3%bv : bv 5); (4%bv : bv 5); (8%bv : bv 5); (9%bv : bv 5); (23%bv : bv 5); (24%bv : bv 5)]
    HS HAE ltac:(vm_compute; reflexivity)) as RK.
  pose proof (RK (2%bv : bv 5) ltac:(repeat (first [left; reflexivity | right]))) as R2.
  pose proof (RK (3%bv : bv 5) ltac:(repeat (first [left; reflexivity | right]))) as R3.
  pose proof (RK (4%bv : bv 5) ltac:(repeat (first [left; reflexivity | right]))) as R4.
  pose proof (RK (8%bv : bv 5) ltac:(repeat (first [left; reflexivity | right]))) as R8.
  pose proof (RK (9%bv : bv 5) ltac:(repeat (first [left; reflexivity | right]))) as R9.
  pose proof (RK (23%bv : bv 5) ltac:(repeat (first [left; reflexivity | right]))) as R23.
  pose proof (RK (24%bv : bv 5) ltac:(repeat (first [left; reflexivity | right]))) as R24.
  cbn [ms_regs restrict] in R2, R3, R4, R8, R9, R23, R24.
  destruct (cwc_common e lyc Sc Wc regsc memc mdc (ms_regs ms2) (ms_mem ms2) mdv2 pos sp1 line c HC HL HS0 HJ
    R2 R3 R4 R8 R9 R23 KEEP) as (HC2 & HL2 & HS2).
  pose proof (st_ok_region_nth E _ _ 1 (YP09.mkRegion (Some 9%nat) 80 88 80 88 [YP09.mkChunk 80 (CVal 8 (SOff 20 0))])
    HS ltac:(vm_compute; reflexivity)) as RG1.
  pose proof (st_ok_region_nth E _ _ 2 (YP09.mkRegion (Some 9%nat) 112 128 112 128
    [YP09.mkChunk 112 (CVal 8 (SAlu ALU_SRL (SOff 32 16) (SLit 3))); YP09.mkChunk 120 (CVal 8 (SOff 32 16))])
    HS ltac:(vm_compute; reflexivity)) as RG2.
  cbn [ms_mem restrict] in RG1, RG2.
  assert (CS : cw_cscr (rdW Wc (ms_mem ms2)) sp1 c).
  { split; [|split].
    - apply cwc_aval_of_val. apply (field_of_region E _ 9%nat sp1 _ 80 88 80 88 80 8 (SOff 20 0) c RG1 U9);
        [left; reflexivity | rewrite (cwc_DO E 20 c 0 E20) by lia; f_equal; lia | zside | zside].
    - apply cwc_aval_of_val.
      apply (field_of_region E _ 9%nat sp1 _ 112 128 112 128 112 8 (SAlu ALU_SRL (SOff 32 16) (SLit 3))
        ((A_G_REC + 16 + 56 * c) / 8) RG2 U9);
        [left; reflexivity | rewrite (cwc_srl3 E 32 16 _ E32) by lia; do 2 f_equal; lia | zside | zside].
    - apply cwc_aval_of_val.
      apply (field_of_region E _ 9%nat sp1 _ 112 128 112 128 120 8 (SOff 32 16) (A_G_REC + 16 + 56 * c) RG2 U9);
        [right; left; reflexivity | rewrite (cwc_DO E 32 _ 16 E32) by lia; f_equal; lia | zside | zside]. }
  cwc_reg HS (18%bv : bv 5) R18. cwc_reg HS (19%bv : bv 5) R19. cwc_reg HS (20%bv : bv 5) Q20.
  cwc_reg HS (25%bv : bv 5) R25. cwc_reg HS (26%bv : bv 5) R26. cwc_reg HS (27%bv : bv 5) R27.
  assert (IR : cw_iregs (ms_regs ms2) c 0).
  { unfold cw_iregs. cbv zeta. split; [|split; [|split; [|split; [|split]]]].
    - rewrite R19, (denot_shx E 32 23 20 (A_G_REC + 56 * c) 2147450880 E32 E23) by lia.
      unfold w64, CW_SB. replace (A_G_REC + 16 + 56 * c + 4) with (A_G_REC + 56 * c + 20) by lia. reflexivity.
    - rewrite Q20, (cwc_DO E 32 _ 24 E32) by lia. unfold w64. f_equal. lia.
    - rewrite R25, (cwc_DO E 32 _ 24 E32) by lia. unfold w64. f_equal. lia.
    - rewrite R26. reflexivity.
    - rewrite R27, (cwc_DO E 32 _ 20 E32) by lia. unfold w64. f_equal. lia.
    - rewrite R24. exact H24. }
  assert (X18 : getr (ms_regs ms2) 18 = w64 (cw_tptr fn + Z.of_nat 0)).
  { rewrite R18, (cwc_DO E 36 _ 0 E36) by lia. reflexivity. }
  pmkst HS. change (BASE + 5660) with (BASE + CW_PC_IH).
  apply (HIH e lyc Sc Wc (ms_regs ms2) (ms_mem ms2) mdv2 pos sp1 line 0%nat Hent).
  exists fn, args.
  assert (Ha0 : 0 <= 0 < Z.of_nat (length args)) by lia.
  split; [exact (conj HC2 (conj HL2 (conj HS2 (conj CS (conj IR (conj Hcr (conj Hnth Ha0))))))) |].
  split; [lia|]. split; [exact X18|].
  cbn [skipn Z.to_nat]. exact (cw_parse_tpl fn Hfn).
Qed.
End e.
End f.
End d.
