(* check_words_add's walk on the ASan+UBSan build of plugin-hostd/fuzz_command (fuzz_command.asan-ubsan), part 1:
   the facts about this binary that the walk needs beyond `tcheck_words_add_spec`'s premises
   (lib/B/Prog/check_words_add_c.v), and what the walk reads off them. The B twin of
   lib/A/Prog/check_words_add_s1.v (a working branch 1aea12cabb8), re-derived on B's image.

   The statement quantifies over an arbitrary allocator record `B`, and its only premises about `B` are AR (inside
   afn_pre_na, lib/B/Prog/PaNoChain.v:33-38) and arodata_okP (lib/B/Prog/CmdBase.v:21-23). Neither ties `B`'s
   shadow cell, its GOT word, its errno cell, its trace universe, its zero-shadow ranges or its const cells to the
   pinned image (AR's const law, lib/Reusable/YG0d.v:469-475, gives the words AT `as_shadow_cell B` and
   `as_got_shadow B`, not where those are). The six facts the walk uses about them are the fields of the record
   `CwaFacts` below, each as narrow as the walk uses it; the walk (lib/B/Prog/check_words_add_s2.v .. _s4.v) uses
   nothing else about `B`. check_words_add.v builds the record by exact from a Theorem Labs lane's shared record lemmas
   (lib/B/Prog/CmdRecFacts.v, a working branch 6830f0bf032) under the walk hypotheses `HB : CmdBSyms B` and
   `IMG : cmd_img_facts SEGS B`; this file proves no fact about the record.

   `AR_laws SEGS B` is NOT among them: it is a theorem (lib/Reusable/YG0q.v:804, `AR_laws_ok`). The bytes a
   word-at-a-time musl loop may touch after a string argument's NUL are not among them either: every string
   argument is a live block (in_blockA), and lib/Reusable/YG0d_tail.v:57 (`AR_block_word_vis`) gives that tail
   from AR. After a literal's NUL they are cf_tail (CmdRecRest's cmd_tail_vis) from the statement's `cmd_ro_ok`,
   whose end list lib/B/Prog/CmdRo.v:448 `cmd_ro_ends` (206 ends) holds the four literals' ends 0x21b01, 0x21b23,
   0x21b47, 0x21b65. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YG0q YG0d_tail YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtString.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv CommandModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable CmdSyms CmdList CmdAddr CmdPa CmdBase CmdRep CmdObj CmdRo.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

(* the four image literals check_words_add reads, with the byte count through the NUL (M: lib/B/Prog/CmdRo.v:88-91
   RO_lit_21b00 "-", RO_lit_21b20 "own", RO_lit_21b40 "default", RO_lit_21b60 "pool:") *)
Definition CWA_LITS : list (Z * Z) := [(0x21b00, 2); (0x21b20, 4); (0x21b40, 8); (0x21b60, 6)].

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* The six facts about this binary that the walk needs and `tcheck_words_add_spec` does not give, as one record;
   check_words_add.v builds it from CmdRecFacts.v's lemmas, and the walk uses nothing else about `B`. *)
Record CwaFacts (B : asyms) : Prop := mkCwaFacts {
(* 1-3. The shadow base and the runtime's own cells. The code loads the word at 0xa5f50 (the GOT word
   VAL (A_OBJ 0), 0x88ed8 auipc / 0x88edc ld) and then the word at the address it holds, 0xb0c38 (VAL (A_OBJ 12),
   0x88ee0 ld), and uses that as the base of every one of the seven inline checks. `AR`'s const law
   (lib/Reusable/YG0d.v:469-475) gives the word at `as_shadow_cell B` and the word at `as_got_shadow B`; the two
   equations say those are the image's cells. `api_env` is what the step through a runtime entry asks
   (lib/B/Prog/PaArt.v, aj_art_at). They are CmdRecCells' cmd_cf_cell, cmd_cf_got and cmd_cf_env
   (cgif's `PALib` fields pal_cell, pal_got_shadow and pal_env, lib/B/Prog/CmdPaLib.v:306-309). *)
cf_cell : as_shadow_cell B = VAL (A_OBJ 12);
cf_got : as_got_shadow B = VAL (A_OBJ 0);
cf_env : api_env SEGS B;
(* 4. g_rec's body is marked usable (CmdRecCells' cmd_cf_grec). Checks 5, 6 and 7 (0x88ff4, 0x89020, 0x8904c) read
   the shadow bytes of cp + 4, cp + 24 and cp + 32, and the statement bounds those inside
   [A_G_REC, A_G_REC + REC_SIZE) only. *)
cf_grec : forall ly S W mem md, AR SEGS B ly S W mem md ->
  range_addressable (rdW W mem) SHADOW_OFF A_G_REC REC_SIZE;
(* 5. The four literals are marked usable through their NUL (CmdRecCells' cmd_cf_lit). Checks 2 and 3 (0x88f64,
   0x88f80) read the shadow byte of the 2-byte literal "-" at 0x21b00, whose granule is partial (metadata byte
   0x02), and each wrapper call reads one literal through its NUL. *)
cf_lit : forall ly S W mem md, AR SEGS B ly S W mem md ->
  Forall (fun an => range_addressable (rdW W mem) SHADOW_OFF (fst an) (snd an)
                 /\ shadow_hull_vis (rdW W mem) (fst an) (snd an)) CWA_LITS;
(* 6. The bytes a word-at-a-time musl loop may touch after a literal's NUL, from the statement's cmd_ro_ok
   (CmdRecRest's cmd_tail_vis) *)
cf_tail : forall (W : world SEGS) mem e, cmd_ro_ok (rdW W mem) -> In e cmd_ro_ends -> atail_vis SEGS W mem e
}.

Section e.
Variable B : asyms.
Variables RLO RHI : Z.
Hypothesis HF : CwaFacts B.

Definition cwa_laws : AR_laws SEGS B := AR_laws_ok SEGS B.
#[local] Notation CWA_LIT := (cf_lit B HF).
#[local] Notation CWA_TAIL := (cf_tail B HF).

(* A string argument of the statement: a live block holds it through its NUL (every caller passes the recorded
   call's arguments, blocks by acall_at, or harness words in words_of's `copy` block, fuzz_command.c:120). This is
   the statement's text (lib/B/Prog/check_words_add_c.v:89-102) after its `aval_mem` conjunct. *)
Definition cwa_str (ly : alayout) (S : astate) (rd : reader) (p : Z) (x : list byte) : Prop :=
0 <= p < 2 ^ 64 /\ in_blockA (ablocks B ly S) p (Z.of_nat (length x) + 1) /\ astr_atR rd p x.

(* ---- what the walk reads off them ---------------------------------------------------------------- *)

(* The read-only words the runtime entries read, at any point of the walk: the statement's arodata_okP at the
   entry, carried by the journal's image clause (the walk writes no image byte). With rt_rom_view
   (lib/B/Rt/RtDefs.v) this needs no fact about the record. *)
Lemma cwa_rom_at : forall STK sp0 ly S W mem md (W' : world SEGS) mem' md' lyc Sc k,
arodata_okP SEGS RLO RHI B (rdW W mem) ->
ajournal SEGS B STK sp0 [] ly S W mem md [] lyc Sc W' mem' md' k ->
rt_rom_view SEGS B W' mem'.
Proof.
intros STK sp0 ly S W mem md W' mem' md' lyc Sc k HRO HJ a Hrom Ho He.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
rewrite (F3 a).
- apply HRO; [left; exact Hrom | exact Ho | exact He].
- destruct Hrom as (sg & Hin & _ & Hr). exists sg. split; [exact Hin | exact Hr].
- exact Ho.
- exact He.
- apply fp_spares_closed; [intros (x & [] & _) | intros X; exact (inFP_nil a X)].
Qed.

(* A string argument of the statement, in the form a Theorem Labs lane's wrapper contracts take it. The bytes after its NUL
   are in the 8-byte word of its block's chunk (lib/Reusable/YG0d_tail.v:57). *)
Lemma cwa_str_facts : forall ly S W (regs : bvmap 5 word) mem md p x,
AR SEGS B ly S W mem md ->
cwa_str ly S (rdW W mem) p x ->
alloc_ceiling <= spZ regs - 2 * ESTACK ->
0 < p /\ astr_at SEGS W mem p x
/\ aread_ok SEGS (2 * ESTACK) W regs mem p (astr_len x + 1)
/\ atail_vis SEGS W mem (p + astr_len x)
/\ p + astr_len x + 1 <= alloc_ceiling /\ p < 2 ^ 64.
Proof.
intros ly S W regs mem md p x HAR HSTR Hsp.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct HSTR as (Hp64 & Hblk & HstrR).
assert (HS : astr_at SEGS W mem p x) by (apply astr_atR_view; exact HstrR).
assert (Hvis : forall a, p <= a < p + (astr_len x + 1) -> rdW W mem a <> None).
{ intros a Ha. destruct HstrR as [Hbytes _].
specialize (Hbytes (Z.to_nat (a - p)) ltac:(rewrite length_app; cbn [length]; unfold astr_len in Ha; lia)).
replace (p + Z.of_nat (Z.to_nat (a - p))) with a in Hbytes by lia. rewrite Hbytes. discriminate. }
unfold astr_len in *.
destruct Hblk as (q & k & Hin & Hq1 & Hq2).
destruct (al_blocks _ _ cwa_laws _ _ _ _ _ q k HAR Hin) as (H16 & H4096 & Hceil & Hia & Hpres & Hnd & Hk).
pose proof (req_size_pos k ltac:(lia)) as [Hr1 Hr2]. unfold MALLOC_MAX in Hk.
assert (Htail : atail_vis SEGS W mem (p + Z.of_nat (length x))).
{ intros a Ha. apply (AR_block_word_vis SEGS B ly S W mem md q k (p + Z.of_nat (length x)) a HAR Hin); lia. }
split; [lia|]. split; [exact HS|]. split; [|split; [exact Htail|]; split; lia].
unfold aread_ok. split; [lia|]. split; [lia|]. split; [lia|]. split.
{ intros a Ha. split; [apply Hvis; exact Ha|]. unfold ascratch_stk. lia. }
split; [exact (amem_range_of_block SEGS B cwa_laws ly S W mem md q k p (Z.of_nat (length x) + 1) HAR Hin ltac:(lia) ltac:(lia))|].
split; [exact (range_addressable_of_block SEGS B cwa_laws ly S W mem md q k p (Z.of_nat (length x) + 1) HAR Hin ltac:(lia) ltac:(lia))|].
intros Hpos. exact (shadow_hull_vis_of_block SEGS B cwa_laws ly S W mem md q k p (Z.of_nat (length x) + 1) HAR Hin ltac:(lia) ltac:(lia) Hpos).
Qed.

(* An image literal, in the same form: its bytes from the statement's cmd_ro_ok, its tail word from cf_tail, its
   shadow from cf_lit. *)
Lemma cwa_lit_facts : forall ly S W (regs : bvmap 5 word) mem md a n l,
AR SEGS B ly S W mem md -> In (a, n) CWA_LITS ->
abytes_atR (rdW W mem) a l -> Z.of_nat (length l) = n ->
cmd_ro_ok (rdW W mem) -> In (a + n - 1) cmd_ro_ends ->
alloc_ceiling <= spZ regs - 2 * ESTACK ->
aread_ok SEGS (2 * ESTACK) W regs mem a n /\ atail_vis SEGS W mem (a + n - 1).
Proof.
intros ly S W regs mem md a n l HAR Hin Hbytes Hlen HRO HE Hsp.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (CWA_LIT ly S W mem md HAR) as HL.
rewrite Forall_forall in HL. destruct (HL (a, n) Hin) as (Hra & Hhull). cbn [fst snd] in Hra, Hhull.
pose proof (CWA_TAIL W mem (a + n - 1) HRO HE) as Htail.
assert (Hrange : 0x21b00 <= a /\ a + n <= 0x21b66)
by (cbv [CWA_LITS In] in Hin; repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]); destruct Hin).
split; [|exact Htail].
unfold aread_ok. split; [lia|]. split; [lia|]. split; [lia|]. split.
{ intros b Hb. split.
  - specialize (Hbytes (Z.to_nat (b - a)) ltac:(lia)).
    replace (a + Z.of_nat (Z.to_nat (b - a))) with b in Hbytes by lia. rewrite Hbytes. discriminate.
  - unfold ascratch_stk. lia. }
split; [unfold amem_range, kLowMemEnd; left; lia|].
split; [exact Hra|]. intros _. exact Hhull.
Qed.

(* The wrapper calls go out through `aj_art_at` (lib/B/Prog/PaArt.v), the step of a walk through a
   runtime entry whose contract is a Theorem Labs lane's `art_post`; the walk applies ASTRCMP / ASTRNCMP under it. *)


End e.
End f.
End d.
