(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the helper layer of sup_instance_verb's ASan+UBSan walk (plugin-hostd/
   fuzz_command, image fuzz_command.asan-ubsan, entry 0x8b8f8, 141 instructions): the model step, the two read-only
   literals the call hands to a runtime entry (the format "%d" at 0x21f40 of the inlined arg_i, the separators
   " \t" at 0x21da0 of the strspn and strcspn wrappers) with their bytes, their shadow from the allocator record
   and their word tails, the snprintf entry in a walk's journal form, the arithmetic of the realignment
   `andi sp,sp,-32` (0x8b930), the two UBSan trap branches (0x8ba50, 0x8ba60), the symbolic entry state with its
   seed, and the recorder-representation lemmas a frame write keeps.
   TAKEN FROM: lib/A/Prog/arg_i_s0.v and arg_i_s1.v of a working branch 12dc52bfe84 (aj_snprintf_atS,
   ai_fmt_*, ai_dec_*, sp1_facts, land_m32, denot_and_m32, ai_entry); lib/A/Prog/answer_code.v of
   a working branch 2ba4488ce71 (preg, norm_ssp, nwin_tac, region_kept_hi, region_kept_hi2,
   aview_frame_pt, aval_mem_kept .. rec_repA_kept, ablocks_nodup, FFL, SMP); lib/A/Prog/sup_instance_verb_s6.v and
   _s8.v of a working branch 2beecf4cd76 (siv_spn_le, siv_cspn_le, siv_verb_first_word,
   siv_slice_bytes, the siv_set facts); at B's addresses (fuzz_command.asan-ubsan .symtab, lib/B/Prog/CmdRo.v and
   lib/B/YF0m.v of a working branch 917ca7ac6b1). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04 YI09 YI0s YG0s YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YG0q YG05 YCbq YC5d YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
CmdSyms CmdList CmdAddr CmdPa CmdPaLib PaLibG PaDenot PaLibF PaLibH.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaSB PaCallRun PaCall PaArt PaFx.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo CmdZsh.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtFormat RtString.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
(* the plain proofs' facts on "%d" (lib/Prog/arg_i.v:36-54) and on " \t" (lib/Prog/sup_instance_verb.v:210-263);
   their modules share base names with walks, so they are named by their full paths *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require arg_i sup_instance_verb strspn_c strcspn_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Module PAI := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.arg_i.
Module PSIV := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.sup_instance_verb.
Module PSpnB := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.strspn_c.
Module PCspnB := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.strcspn_c.

(* --- the program's writable statics, base and length (lib/B/Prog/CmdGlob.v cmd_PG as `in_zr` reads it) ------- *)
Definition recb_PG : list (Z * Z) := [(A_G_REC, REC_SIZE); (A_REC_SPILL, SC_SIZE); (A_G_QUITTING, 4)].

(* --- the model step: record(7), arg_line(line), arg_s(dec ledger), rec_shape_of(first word), answer(changes = 1)
   compose to sup_instance_verb_m (lib/Prog/RecModel.v:135-136, :73-75) ---------------------------------------- *)
Lemma sivb_model : forall R line ledger,
sup_instance_verb_m R line ledger =
rec_answer (rec_record R REC_INSTANCE_VERB [canon line; dec ledger])
  (REC_INSTANCE_VERB, [canon line; dec ledger]) (shape_of (first_word line)) true.
Proof. intros R line ledger. reflexivity. Qed.
Lemma sivb_args1 : forall (x : list byte), ([] ++ [x])%list = [x].
Proof. reflexivity. Qed.
Lemma sivb_args2 : forall (x y : list byte), ([x] ++ [y])%list = [x; y].
Proof. reflexivity. Qed.
Lemma sivb_sarg : forall x, sarg (Some x) = x.
Proof. reflexivity. Qed.
Lemma sivb_fn_range : 0 <= REC_INSTANCE_VERB < REC_FN_COUNT.
Proof. unfold REC_INSTANCE_VERB, REC_FN_COUNT. lia. Qed.

(* --- the format "%d" (.str at 0x21f40, the listing's object A_OBJ 51) and the text snprintf writes ----------- *)
Lemma sivb_fmt_bytes : PF.pf_bytes PAI.AI_FMT ++ [Z_to_bv 8 0] = RO_lit_21f40.
Proof. vm_compute. reflexivity. Qed.
Lemma sivb_fmt_nz : ~ In (Z_to_bv 8 0) (PF.pf_bytes PAI.AI_FMT).
Proof. cbn. intros H. repeat (destruct H as [H|H]; [vm_compute in H; discriminate H|]). exact H. Qed.
Lemma sivb_fmt_len : Z.of_nat (length PAI.AI_FMT) = 2.
Proof. vm_compute. reflexivity. Qed.
Lemma sivb_dec_len : forall v, -2^31 <= v < 2^31 -> length (PF.pf_dec v) = length (dec v).
Proof. intros v Hv. rewrite <- (PAI.ai_pf_dec v Hv). unfold PF.pf_bytes. rewrite length_map. reflexivity. Qed.
(* snprintf(b, 16, "%d", ledger) writes dec ledger and its terminator: the text is at most 11 bytes *)
Lemma sivb_dec_text : forall v, -2^31 <= v < 2^31 ->
PF.pf_bytes (firstn (Z.to_nat (16 - 1)) (PF.pf_dec v) ++ [0]) = dec v ++ [Z_to_bv 8 0].
Proof.
intros v Hv. pose proof (dec_length v Hv) as Hl. pose proof (sivb_dec_len v Hv) as Hl2.
rewrite firstn_all2 by (rewrite Hl2; change (Z.to_nat (16 - 1)) with 15%nat; lia).
unfold PF.pf_bytes in *. rewrite map_app. rewrite <- (PAI.ai_pf_dec v Hv). reflexivity.
Qed.
Lemma sivb_dec_text_len : forall v, -2^31 <= v < 2^31 -> Z.of_nat (length (PF.pf_dec v)) < 2 ^ 31 - 1.
Proof.
intros v Hv. pose proof (dec_length v Hv) as Hl. rewrite (sivb_dec_len v Hv). lia.
Qed.
Lemma sivb_dec_no0 : forall v, no0 (dec v).
Proof. intros v. exact (dec_no0 v). Qed.

(* --- the separators " \t" (.str at 0x21da0, the listing's object A_OBJ 65) ---------------------------------- *)
Definition sivb_set : list byte := PSIV.siv_set.
Lemma sivb_set_lit : sivb_set ++ [Z_to_bv 8 0] = RO_lit_21da0.
Proof. vm_compute. reflexivity. Qed.
Lemma sivb_set_nz : ~ In (Z_to_bv 8 0) sivb_set.
Proof. unfold sivb_set, PSIV.siv_set. cbn [In]. intros H. repeat (destruct H as [H|H]; [vm_compute in H; discriminate H|]). exact H. Qed.
Lemma sivb_set_len : Z.of_nat (length sivb_set) = 2.
Proof. vm_compute. reflexivity. Qed.

(* --- the strspn / strcspn results (recorder.c:386-387) ------------------------------------------------------ *)
Definition sivb_spn (line : list byte) : nat := PSpnB.spn_len sivb_set line.
Definition sivb_cspn (line : list byte) : nat := PCspnB.cspn_len sivb_set (skipn (sivb_spn line) line).
Lemma sivb_verb_first_word : forall line,
firstn (sivb_cspn line) (skipn (sivb_spn line) line) = first_word line.
Proof. intros line. exact (PSIV.siv_first_word line). Qed.
Lemma sivb_spn_le : forall line, (sivb_spn line <= length line)%nat.
Proof. intros line. exact (PSIV.siv_spn_le line). Qed.
Lemma sivb_cspn_le : forall line, (sivb_cspn line <= length (skipn (sivb_spn line) line))%nat.
Proof. intros line. exact (PSIV.siv_cspn_le _). Qed.
(* the bytes of a slice of a C string *)
Lemma sivb_slice_bytes : forall rd p (s : list byte) j k, astr_atR rd p s -> (j + k <= length s)%nat ->
abytes_atR rd (p + Z.of_nat j) (firstn k (skipn j s)).
Proof.
intros rd p s j k [H1 _] Hjk i Hi. rewrite length_firstn, length_skipn in Hi.
replace (p + Z.of_nat j + Z.of_nat i) with (p + Z.of_nat (j + i)) by lia.
rewrite (H1 (j + i)%nat) by (rewrite length_app; cbn [length]; lia). f_equal. f_equal.
rewrite nth_firstn. replace (i <? k)%nat with true by (symmetry; apply Nat.ltb_lt; lia).
rewrite nth_skipn. rewrite app_nth1 by lia. reflexivity.
Qed.
Lemma sivb_slice_no0 : forall (s : list byte) j k, ~ In (Z_to_bv 8 0) s -> ~ In (Z_to_bv 8 0) (firstn k (skipn j s)).
Proof.
intros s j k Hn Hin. apply Hn. rewrite <- (firstn_skipn j s). apply in_or_app. right.
rewrite <- (firstn_skipn k (skipn j s)). apply in_or_app. left. exact Hin.
Qed.

(* --- projection out of the read-only conjunctions (CmdRo.v cmd_ro_bytes, cmd_ro_in, cmd_ro_tails) ----------- *)
Ltac sivb_projz H a :=
  repeat lazymatch type of H with
  | ?A /\ _ => lazymatch A with context [a] => fail | _ => destruct H as [_ H] end
  end;
  lazymatch type of H with
  | _ /\ _ => exact (proj1 H)
  | _ => exact H
  end.

(* --- the allocator record's constant shadow cells -------------------------------------------------------- *)
Definition sivb_cell_is (a v : Z) (c : acell) : bool :=
  match c with
  | ACell (ANum a') (S O) (AV (ANum v')) => (a' =? a) && (v' =? v)
  | _ => false
  end.
Lemma sivb_cell_in : forall a v l, existsb (sivb_cell_is a v) l = true -> In (z1 (ANum a) v) l.
Proof.
intros a v l. induction l as [|c l IH]; cbn [existsb In]; [discriminate|].
intros H. apply orb_true_iff in H as [H|H]; [left | right; exact (IH H)].
destruct c as [ca cw cv]. unfold sivb_cell_is in H.
destruct ca; try discriminate H. destruct cw as [|[|cw]]; try discriminate H.
destruct cv as [e|m w]; try discriminate H. destruct e; try discriminate H.
apply andb_true_iff in H as [H1 H2]. apply Z.eqb_eq in H1, H2. subst. reflexivity.
Qed.
Lemma sivb_unowned_rng : forall a n (l : list (Z * Z)),
forallb (fun r => (a + n <=? fst r) || (fst r + snd r <=? a)) l = true ->
forall i, 0 <= i < n -> ~ Exists (in_zr (a + i)) l.
Proof.
intros a n l Hb i Hi Hex. apply Exists_exists in Hex as (r & Hr & Hz). unfold in_zr in Hz.
rewrite forallb_forall in Hb. specialize (Hb r Hr). apply orb_true_iff in Hb as [Hb | Hb];
apply Z.leb_le in Hb; lia.
Qed.
Lemma sivb_Z_mod_16_8 : forall x, x mod 16 = 0 -> x mod 8 = 0.
Proof. intros x H. pose proof (Z.div_mod x 16 ltac:(lia)). replace x with (2 * (x / 16) * 8) by lia. apply Z_mod_mult. Qed.
Lemma sivb_not_in_ranges : forall (L : list (Z * Z)) lo hi,
forallb (fun r => (hi <=? fst r) || (fst r + snd r <=? lo)) L = true ->
forall a, lo <= a < hi -> ~ Exists (in_zr a) L.
Proof.
intros L lo hi Hb a Ha Hex. apply Exists_exists in Hex as (r & Hr & Hz). unfold in_zr in Hz.
rewrite forallb_forall in Hb. specialize (Hb r Hr). apply orb_true_iff in Hb as [Hb | Hb];
apply Z.leb_le in Hb; lia.
Qed.

(* the realignment `andi sp,sp,-32` (0x8b930): the kit's CmdSnText.snt_sp1_facts, snt_land_m32 and
   snt_denot_and_m32 (b-helper-kit-map.md, 'The appendix's four Section-free helpers') *)
Lemma sivb_denot_off0 : forall E n, sv_denot E (SOff n 0) = ew E n.
Proof. intros E n. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. Qed.
Lemma sivb_denot_add0 : forall E e, sv_denot E (SAlu ALU_ADD e (SLit 0)) = sv_denot E e.
Proof.
intros E e. rewrite denot_lit_U, U_SAlu. cbn [zalu_raw]. rewrite U_SLit. change (zcanon 0) with 0.
rewrite Z.add_0_r. unfold U. rewrite zcanon_id by apply u64_range. apply Z_to_bv_bv_unsigned.
Qed.

(* --- the two UBSan pointer-overflow checks of `line += strspn(line, " \t")` (recorder.c:386), both branching to
   the `unimp` at 0x8bb28. With s3 = line = pl and s4 = line + k (k the strspn wrapper's answer, 0x8ba4c):
   0x8ba50 `bltu s4,s3` is taken iff (pl + k) mod 2^64 < pl (unsigned);
   0x8ba60 `beqz a0` is taken iff a0 = (snez s3) xor (seqz s4) is 0.
   Neither is taken when 0 < pl and pl + k < 2^64. ------------------------------------------------------------ *)
Lemma sivb_ubsan_8ba50 : forall pl k, 0 < pl -> 0 <= k -> pl + k < 2 ^ 64 -> ((pl + k) mod 2 ^ 64 <? pl) = false.
Proof. intros pl k H0 Hk H64. rewrite Z.mod_small by lia. apply Z.ltb_ge. lia. Qed.
Lemma sivb_ubsan_8ba60 : forall pl k, 0 < pl -> 0 <= k -> pl + k < 2 ^ 64 ->
Z.lxor (if 0 <? pl mod 2 ^ 64 then 1 else 0) (if (pl + k) mod 2 ^ 64 <? 1 then 1 else 0) = 1.
Proof.
intros pl k H0 Hk H64. rewrite (Z.mod_small pl) by lia. rewrite (Z.mod_small (pl + k)) by lia.
replace (0 <? pl) with true by (symmetry; apply Z.ltb_lt; lia).
replace (pl + k <? 1) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.
(* the two checks as the executor states them at their branches (PaCallRun's psrr_branch_pi): 0x8ba50 is
   `bltu s4,s3` with s4 = s3 + a0 (0x8ba4c), s3 the line and a0 strspn's count; it is not taken *)
Lemma sivb_br_8ba50 : forall E n m (x y : Z), ew E n = Z_to_bv 64 x -> ew E m = Z_to_bv 64 y ->
  0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> x + y < 2 ^ 64 ->
  branch_taken BC_LTU (sv_denot E (SAlu ALU_ADD (SOff n 0) (SOff m 0))) (sv_denot E (SOff n 0)) = false.
Proof.
intros E n m x y Hn Hm Hx Hy Hxy. cbn [branch_taken].
rewrite (denot_lit_U E (SAlu _ _ _)), (denot_lit_U E (SOff n 0)).
rewrite U_SAlu. cbn [zalu_raw].
rewrite (U_atom_off E n x 0 Hn) by lia. rewrite (U_atom_off E m y 0 Hm) by lia.
rewrite !Z.add_0_r. rewrite zcanon_id by (unfold M64; lia).
unfold bv_ltu. rewrite !unsigned_lit_small by lia. apply Z.ltb_ge. lia.
Qed.
(* 0x8ba60 is `beqz a0` with a0 = (snez s3) xor (seqz s4) (0x8ba54 .. 0x8ba5c); it is not taken *)
Lemma sivb_br_8ba60 : forall E n m (x y : Z), ew E n = Z_to_bv 64 x -> ew E m = Z_to_bv 64 y ->
  0 < x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> x + y < 2 ^ 64 ->
  branch_taken BC_EQ
    (sv_denot E (SAlu ALU_XOR (SAlu ALU_SLTU (SLit 0) (SOff n 0)) (SAlu ALU_SLTU (SAlu ALU_ADD (SOff n 0) (SOff m 0)) (SLit 1))))
    (sv_denot E (SLit 0)) = false.
Proof.
intros E n m x y Hn Hm Hx Hy Hxy. cbn [branch_taken]. rewrite bv_eqb_unsigned.
assert (HA : U E (SAlu ALU_XOR (SAlu ALU_SLTU (SLit 0) (SOff n 0)) (SAlu ALU_SLTU (SAlu ALU_ADD (SOff n 0) (SOff m 0)) (SLit 1))) = 1).
{ rewrite !U_SAlu, !U_SLit. cbn [zalu_raw].
  rewrite (U_atom_off E n x 0 Hn) by lia. rewrite (U_atom_off E m y 0 Hm) by lia. rewrite !Z.add_0_r.
  rewrite (zcanon_id (x + y)) by (unfold M64; lia).
  change (zcanon 0) with 0. change (zcanon 1) with 1.
  replace (0 <? x) with true by (symmetry; apply Z.ltb_lt; lia).
  replace (x + y <? 1) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. }
assert (HB : U E (SLit 0) = 0) by (rewrite U_SLit; reflexivity).
unfold U in HA, HB. rewrite HA, HB. reflexivity.
Qed.
(* s4 = s3 + a0 as a value, below 2 ^ 64 *)
Lemma sivb_denot_add_atoms : forall E n m (x y : Z), ew E n = Z_to_bv 64 x -> ew E m = Z_to_bv 64 y ->
  0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> x + y < 2 ^ 64 ->
  sv_denot E (SAlu ALU_ADD (SOff n 0) (SOff m 0)) = Z_to_bv 64 (x + y).
Proof.
intros E n m x y Hn Hm Hx Hy Hxy. rewrite denot_lit_U, U_SAlu. cbn [zalu_raw].
rewrite (U_atom_off E n x 0 Hn) by lia. rewrite (U_atom_off E m y 0 Hm) by lia. rewrite !Z.add_0_r.
rewrite zcanon_id by (unfold M64; lia). reflexivity.
Qed.
(* the tail of a C string is a C string *)
Lemma sivb_str_skipn : forall rd p (s : list byte) j, astr_atR rd p s -> (j <= length s)%nat ->
  astr_atR rd (p + Z.of_nat j) (skipn j s).
Proof.
intros rd p s j [H1 H2] Hj. split.
- intros i Hi. rewrite length_app, length_skipn in Hi. cbn [length] in Hi.
  replace (p + Z.of_nat j + Z.of_nat i) with (p + Z.of_nat (j + i)) by lia.
  rewrite (H1 (j + i)%nat) by (rewrite length_app; cbn [length]; lia). f_equal. f_equal.
  assert (E : s ++ [Z_to_bv 8 0] = firstn j s ++ (skipn j s ++ [Z_to_bv 8 0])) by (rewrite app_assoc, firstn_skipn; reflexivity).
  rewrite E, app_nth2 by (rewrite length_firstn; lia). rewrite length_firstn.
  replace (j + i - Nat.min j (length s))%nat with i by lia. reflexivity.
- intros Hin. apply H2. rewrite <- (firstn_skipn j s). apply in_or_app. right. exact Hin.
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

(* the snprintf entry in a walk's journal form moved to lib/B/Prog/sup_instance_verb_snp.v when the pass-4b
   shared contract (lib/B/Rt/RtPFShared.v) replaced the local one. *)

Section b.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* --- region bookkeeping across a call or a run (answer_code's region_kept_hi / region_kept_hi2 /
   aview_frame_pt) ------------------------------------------------------------------------------------------- *)
Lemma sivb_region_kept_hi : forall E H (m m2 : word -> option byte) n b lo hi wlo whi cs,
bv_unsigned (ew E n) = b ->
(forall a, b + lo <= a < b + hi -> aview SEGS H m2 a = aview SEGS H m a) ->
(forall a, b + wlo <= a < b + whi -> apresent H m2 a) ->
region_kept SEGS E (mrestrict H m) (mrestrict H m2) (YP09.mkRegion (Some n) lo hi wlo whi cs).
Proof.
intros E H m m2 n b lo hi wlo whi cs Hn Hav Hp.
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Hn; intros a Ha.
- apply (mbyte_of_aview SEGS). apply Hav. exact Ha.
- intros _. apply (apresent_writable SEGS). apply Hp. exact Ha.
Qed.
Lemma sivb_region_kept_hi2 : forall E H H2 (m m2 : word -> option byte) n b lo hi wlo whi cs,
bv_unsigned (ew E n) = b ->
(forall a, b + lo <= a < b + hi -> aview SEGS H2 m2 a = aview SEGS H m a) ->
(forall a, b + wlo <= a < b + whi -> apresent H2 m2 a) ->
region_kept SEGS E (mrestrict H m) (mrestrict H2 m2) (YP09.mkRegion (Some n) lo hi wlo whi cs).
Proof.
intros E H H2 m m2 n b lo hi wlo whi cs Hn Hav Hp.
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Hn; intros a Ha.
- apply (mbyte_of_aview SEGS). apply Hav. exact Ha.
- intros _. apply (apresent_writable SEGS). apply Hp. exact Ha.
Qed.
Lemma sivb_aview_frame_pt : forall E rs H (m m' : word -> option byte) a,
frame_of E rs (mrestrict H m) (mrestrict H m') -> 0 <= a < 2 ^ 64 -> ~ in_wrange E rs a ->
aview SEGS H m' a = aview SEGS H m a.
Proof.
intros E rs H m m' a HF Ha Hn. apply (aview_eq_of SEGS). apply HF. rewrite unsigned_lit_small by lia. exact Hn.
Qed.

Section z.
Variable B : asyms.
(* the per-binary allocator record (a Theorem Labs lane's lib/B/YF0m.v), under its canonical name (RECB-NAMED-HYPS.md) *)
Hypothesis HB : CmdBSyms B.
(* the statement's bridge from the listing's object atoms to the image's addresses (lib/B/Prog/CmdObj.v:39-40) *)
Hypothesis VOBJS : cmd_val_objs.
(* the call targets of the program functions (lib/B/Prog/CmdObj.v:44-45) *)
Hypothesis SIGP : cmd_sig_prog.

(* --- the call targets: record (0x8b9f8), arg_line (0x8ba04), arg_s (0x8ba30), rec_shape_of (0x8ba7c),
   answer (0x8ba8c) ------------------------------------------------------------------------------------------- *)
Local Ltac sivb_in := repeat (first [left; reflexivity | right]).
(* record's call target: the kit's CmdRecAns.rca_sig_record *)
Lemma sivb_sig_arg_line : SIG CS_arg_line = BASE + AF_arg_line.
Proof. rewrite (SIGP CS_arg_line) by (cbv [cmd_prog_syms]; sivb_in). f_equal; vm_compute; reflexivity. Qed.
Lemma sivb_sig_arg_s : SIG CS_arg_s = BASE + AF_arg_s.
Proof. rewrite (SIGP CS_arg_s) by (cbv [cmd_prog_syms]; sivb_in). f_equal; vm_compute; reflexivity. Qed.
Lemma sivb_sig_rec_shape_of : SIG CS_rec_shape_of = BASE + AF_rec_shape_of.
Proof. rewrite (SIGP CS_rec_shape_of) by (cbv [cmd_prog_syms]; sivb_in). f_equal; vm_compute; reflexivity. Qed.
Lemma sivb_sig_answer : SIG CS_answer = BASE + AF_answer.
Proof. rewrite (SIGP CS_answer) by (cbv [cmd_prog_syms]; sivb_in). f_equal; vm_compute; reflexivity. Qed.

(* --- the objects the walk's auipc pairs name (0, 1, 51, 59, 64, 65). Every auipc of this function is consumed by
   a PLdHi or a PAddHi on an object atom; nothing is loaded or stored through an A_HI value, so the walk needs no
   cmd_val_his ------------------------------------------------------------------------------------------------- *)
Lemma sivb_obj0 : VAL (A_OBJ 0) = 0xa5f50.
Proof. rewrite (VOBJS 0%nat ltac:(vm_compute; lia)). vm_compute. reflexivity. Qed.
Lemma sivb_obj1 : VAL (A_OBJ 1) = 0xa5fa8.
Proof. rewrite (VOBJS 1%nat ltac:(vm_compute; lia)). vm_compute. reflexivity. Qed.
Lemma sivb_obj51 : VAL (A_OBJ 51) = 0x21f40.
Proof. rewrite (VOBJS 51%nat ltac:(vm_compute; lia)). vm_compute. reflexivity. Qed.
Lemma sivb_obj59 : VAL (A_OBJ 59) = 0x15923.
Proof. rewrite (VOBJS 59%nat ltac:(vm_compute; lia)). vm_compute. reflexivity. Qed.
Lemma sivb_obj64 : VAL (A_OBJ 64) = 0x8b8f8.
Proof. rewrite (VOBJS 64%nat ltac:(vm_compute; lia)). vm_compute. reflexivity. Qed.
Lemma sivb_obj65 : VAL (A_OBJ 65) = 0x21da0.
Proof. rewrite (VOBJS 65%nat ltac:(vm_compute; lia)). vm_compute. reflexivity. Qed.

(* a one-byte cell of the record's constant shadow holds under AR *)
Lemma sivb_cshadow : forall ly S (W : world SEGS) mem md a v,
AR SEGS B ly S W mem md -> In (z1 (ANum a) v) Tfib_const_shadow -> 0 <= v < 256 ->
rdW W mem a = Some v.
Proof.
intros ly S W mem md a v HAR Hin Hv. destruct HAR as (M & _).
pose proof (am_const _ _ _ _ M) as C. rewrite (ts_const B HB ly) in C. rewrite Forall_forall in C.
specialize (C (z1 (ANum a) v) ltac:(unfold Tfib_const; apply in_or_app; right; apply in_or_app; right; exact Hin)).
unfold cell_holds in C. cbn [c_at c_val c_w z1 c1 aeval] in C.
specialize (C 0%nat ltac:(lia)). change (Z.of_nat 0) with 0 in C. rewrite Z.add_0_r in C. rewrite C. f_equal.
unfold le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
rewrite Z.shiftr_0_r. change (2 ^ 8) with 256. rewrite Z.mod_mod by lia. apply Z.mod_small. exact Hv.
Qed.
Lemma sivb_cshadow_b : forall ly S (W : world SEGS) mem md a v,
AR SEGS B ly S W mem md -> existsb (sivb_cell_is a v) Tfib_const_shadow = true -> 0 <= v < 256 ->
rdW W mem a = Some v.
Proof.
intros ly S W mem md a v HAR Hb Hv. exact (sivb_cshadow ly S W mem md a v HAR (sivb_cell_in a v _ Hb) Hv).
Qed.

(* the format's 3 bytes ("%d" and its terminator) are addressable: the partial granule 0x21f40 at shadow 3 *)
Lemma sivb_fmt_addressable : forall ly S (W : world SEGS) mem md,
AR SEGS B ly S W mem md -> range_addressable (rdW W mem) SHADOW_OFF 0x21f40 3.
Proof.
intros ly S W mem md HAR x Hx. unfold shadow_of_addr.
assert (Hq : x / 8 = 0x21f40 / 8) by (Z.div_mod_to_equations; lia). rewrite Hq.
exists 3. split.
- replace (SHADOW_OFF + 0x21f40 / 8) with 0x7fffc3e8 by (vm_compute; reflexivity).
  exact (sivb_cshadow_b ly S W mem md 0x7fffc3e8 3 HAR ltac:(vm_compute; reflexivity) ltac:(lia)).
- right. split; [Z.div_mod_to_equations; lia | lia].
Qed.
Lemma sivb_fmt_hull : forall ly S (W : world SEGS) mem md,
AR SEGS B ly S W mem md -> shadow_hull_vis (rdW W mem) 0x21f40 3.
Proof.
intros ly S W mem md HAR s Hs.
assert (E1 : shadow_addr 0x21f40 / 8 * 8 = 0x7fffc3e8) by (vm_compute; reflexivity).
assert (E2 : shadow_addr (0x21f40 + 3 - 1) / 8 * 8 + 8 = 0x7fffc3f0) by (vm_compute; reflexivity).
rewrite E1, E2 in Hs.
assert (Hs8 : s = 0x7fffc3e8 \/ s = 0x7fffc3e9 \/ s = 0x7fffc3ea \/ s = 0x7fffc3eb \/ s = 0x7fffc3ec \/
  s = 0x7fffc3ed \/ s = 0x7fffc3ee \/ s = 0x7fffc3ef) by lia.
destruct Hs8 as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]].
- rewrite (sivb_cshadow_b ly S W mem md 0x7fffc3e8 3 HAR ltac:(vm_compute; reflexivity) ltac:(lia)). discriminate.
- rewrite (sivb_cshadow_b ly S W mem md 0x7fffc3e9 0xf9 HAR ltac:(vm_compute; reflexivity) ltac:(lia)). discriminate.
- rewrite (sivb_cshadow_b ly S W mem md 0x7fffc3ea 0xf9 HAR ltac:(vm_compute; reflexivity) ltac:(lia)). discriminate.
- rewrite (sivb_cshadow_b ly S W mem md 0x7fffc3eb 0xf9 HAR ltac:(vm_compute; reflexivity) ltac:(lia)). discriminate.
- rewrite (sivb_cshadow_b ly S W mem md 0x7fffc3ec 0x6 HAR ltac:(vm_compute; reflexivity) ltac:(lia)). discriminate.
- rewrite (sivb_cshadow_b ly S W mem md 0x7fffc3ed 0xf9 HAR ltac:(vm_compute; reflexivity) ltac:(lia)). discriminate.
- rewrite (sivb_cshadow_b ly S W mem md 0x7fffc3ee 0xf9 HAR ltac:(vm_compute; reflexivity) ltac:(lia)). discriminate.
- rewrite (sivb_cshadow_b ly S W mem md 0x7fffc3ef 0xf9 HAR ltac:(vm_compute; reflexivity) ltac:(lia)). discriminate.
Qed.
(* the separators' 3 bytes (" \t" and its terminator): the partial granule 0x21da0 at shadow 3 *)
Lemma sivb_set_addressable : forall ly S (W : world SEGS) mem md,
AR SEGS B ly S W mem md -> range_addressable (rdW W mem) SHADOW_OFF 0x21da0 3.
Proof.
intros ly S W mem md HAR x Hx. unfold shadow_of_addr.
assert (Hq : x / 8 = 0x21da0 / 8) by (Z.div_mod_to_equations; lia). rewrite Hq.
exists 3. split.
- replace (SHADOW_OFF + 0x21da0 / 8) with 0x7fffc3b4 by (vm_compute; reflexivity).
  exact (sivb_cshadow_b ly S W mem md 0x7fffc3b4 3 HAR ltac:(vm_compute; reflexivity) ltac:(lia)).
- right. split; [Z.div_mod_to_equations; lia | lia].
Qed.
Lemma sivb_set_hull : forall ly S (W : world SEGS) mem md,
AR SEGS B ly S W mem md -> shadow_hull_vis (rdW W mem) 0x21da0 3.
Proof.
intros ly S W mem md HAR s Hs.
assert (E1 : shadow_addr 0x21da0 / 8 * 8 = 0x7fffc3b0) by (vm_compute; reflexivity).
assert (E2 : shadow_addr (0x21da0 + 3 - 1) / 8 * 8 + 8 = 0x7fffc3b8) by (vm_compute; reflexivity).
rewrite E1, E2 in Hs.
assert (Hs8 : s = 0x7fffc3b0 \/ s = 0x7fffc3b1 \/ s = 0x7fffc3b2 \/ s = 0x7fffc3b3 \/ s = 0x7fffc3b4 \/
  s = 0x7fffc3b5 \/ s = 0x7fffc3b6 \/ s = 0x7fffc3b7) by lia.
destruct Hs8 as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]].
- rewrite (sivb_cshadow_b ly S W mem md 0x7fffc3b0 0x2 HAR ltac:(vm_compute; reflexivity) ltac:(lia)). discriminate.
- rewrite (sivb_cshadow_b ly S W mem md 0x7fffc3b1 0xf9 HAR ltac:(vm_compute; reflexivity) ltac:(lia)). discriminate.
- rewrite (sivb_cshadow_b ly S W mem md 0x7fffc3b2 0xf9 HAR ltac:(vm_compute; reflexivity) ltac:(lia)). discriminate.
- rewrite (sivb_cshadow_b ly S W mem md 0x7fffc3b3 0xf9 HAR ltac:(vm_compute; reflexivity) ltac:(lia)). discriminate.
- rewrite (sivb_cshadow_b ly S W mem md 0x7fffc3b4 0x3 HAR ltac:(vm_compute; reflexivity) ltac:(lia)). discriminate.
- rewrite (sivb_cshadow_b ly S W mem md 0x7fffc3b5 0xf9 HAR ltac:(vm_compute; reflexivity) ltac:(lia)). discriminate.
- rewrite (sivb_cshadow_b ly S W mem md 0x7fffc3b6 0xf9 HAR ltac:(vm_compute; reflexivity) ltac:(lia)). discriminate.
- rewrite (sivb_cshadow_b ly S W mem md 0x7fffc3b7 0xf9 HAR ltac:(vm_compute; reflexivity) ltac:(lia)). discriminate.
Qed.
(* neither literal is the record's: no owned static, not the errno cell *)
Lemma sivb_fmt_unowned : forall a, 0x21f40 <= a < 0x21f43 ->
~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros a Ha. rewrite (ts_owned B HB), (ts_errno B HB). unfold TFIB_ERRNO. split; [|lia].
replace a with (0x21f40 + (a - 0x21f40)) by lia.
apply (sivb_unowned_rng 0x21f40 3); [vm_compute; reflexivity | lia].
Qed.
Lemma sivb_set_unowned : forall a, 0x21da0 <= a < 0x21da3 ->
~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros a Ha. rewrite (ts_owned B HB), (ts_errno B HB). unfold TFIB_ERRNO. split; [|lia].
replace a with (0x21da0 + (a - 0x21da0)) by lia.
apply (sivb_unowned_rng 0x21da0 3); [vm_compute; reflexivity | lia].
Qed.
(* the program's statics, as `in_zr` reads them *)
Lemma sivb_prog_static : as_prog_static B = recb_PG.
Proof. rewrite (ts_prog B HB). vm_compute. reflexivity. Qed.
End z.

(* --- the two literals' bytes and word tails, from the statement's cmd_ro_ok --------------------------------- *)
Lemma sivb_ro_fmt : forall rd, cmd_ro_ok rd -> abytes_atR rd 0x21f40 RO_lit_21f40.
Proof. intros rd [H _]. unfold cmd_ro_bytes in H. sivb_projz H 0x21f40. Qed.
Lemma sivb_ro_set : forall rd, cmd_ro_ok rd -> abytes_atR rd 0x21da0 RO_lit_21da0.
Proof. intros rd [H _]. unfold cmd_ro_bytes in H. sivb_projz H 0x21da0. Qed.
Lemma sivb_ro_in_fmt : forall P, cmd_ro_in P -> forall i, 0 <= i < 3 -> P (0x21f40 + i).
Proof. intros P H. unfold cmd_ro_in in H. sivb_projz H 0x21f40. Qed.
Lemma sivb_ro_in_set : forall P, cmd_ro_in P -> forall i, 0 <= i < 3 -> P (0x21da0 + i).
Proof. intros P H. unfold cmd_ro_in in H. sivb_projz H 0x21da0. Qed.
(* the word tails CmdRo's cmd_ro_ends lists: 0x21f42 for "%d", 0x21da2 for " \t" *)
Lemma sivb_tail_fmt : forall (W : world SEGS) mem, cmd_ro_ok (rdW W mem) -> atail_vis SEGS W mem 0x21f42.
Proof.
intros W mem [_ HT] a Ha. apply (HT 0x21f42); [apply In_of_existsb; vm_compute; reflexivity | exact Ha].
Qed.
Lemma sivb_tail_set : forall (W : world SEGS) mem, cmd_ro_ok (rdW W mem) -> atail_vis SEGS W mem 0x21da2.
Proof.
intros W mem [_ HT] a Ha. apply (HT 0x21da2); [apply In_of_existsb; vm_compute; reflexivity | exact Ha].
Qed.
(* the two literals as C strings *)
Lemma sivb_fmt_str : forall (W : world SEGS) mem, cmd_ro_ok (rdW W mem) ->
astr_at SEGS W mem 0x21f40 (PF.pf_bytes PAI.AI_FMT).
Proof.
intros W mem HRO. split; [|exact sivb_fmt_nz]. unfold abytes_at. rewrite sivb_fmt_bytes.
intros i Hi. exact (sivb_ro_fmt _ HRO i Hi).
Qed.
Lemma sivb_set_str : forall (W : world SEGS) mem, cmd_ro_ok (rdW W mem) ->
astr_at SEGS W mem 0x21da0 sivb_set.
Proof.
intros W mem HRO. split; [|exact sivb_set_nz]. unfold abytes_at. rewrite sivb_set_lit.
intros i Hi. exact (sivb_ro_set _ HRO i Hi).
Qed.
Lemma sivb_set_strR : forall rd, cmd_ro_ok rd -> astr_atR rd 0x21da0 sivb_set.
Proof.
intros rd HRO. split; [|exact sivb_set_nz]. rewrite sivb_set_lit. exact (sivb_ro_set rd HRO).
Qed.

Section y.
Variable B : asyms.
Hypothesis HB : CmdBSyms B.
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.

(* the read window the strspn and strcspn wrappers need on the separators *)
Lemma sivb_set_read : forall ly S (W : world SEGS) mem md (regs : bvmap 5 word) stk,
AR SEGS B ly S W mem md -> cmd_ro_ok (rdW W mem) -> cmd_val_objs ->
0 <= stk -> 0x21da3 <= spZ regs - stk ->
aread_ok SEGS stk W regs mem 0x21da0 3.
Proof.
intros ly S W mem md regs stk HAR HRO VOBJS Hstk Hsp.
split; [lia|]. split; [lia|]. split; [lia|]. split.
- intros a Ha. split.
  + replace a with (0x21da0 + Z.of_nat (Z.to_nat (a - 0x21da0))) by lia.
    rewrite (sivb_ro_set _ HRO (Z.to_nat (a - 0x21da0))) by (change (length RO_lit_21da0) with 3%nat; lia).
    discriminate.
  + unfold ascratch_stk. lia.
- pose proof alloc_ceiling_value as (Hcm & _).
  split; [apply amem_range_high; [lia | left; lia | lia]|].
  split; [exact (sivb_set_addressable B HB ly S W mem md HAR) | intros _; exact (sivb_set_hull B HB ly S W mem md HAR)].
Qed.
(* the read window the snprintf wrapper needs on the format *)
Lemma sivb_fmt_read : forall ly S (W : world SEGS) mem md (regs : bvmap 5 word) stk,
AR SEGS B ly S W mem md -> cmd_ro_ok (rdW W mem) -> 0 <= stk -> 0x21f43 <= spZ regs - stk ->
aread_ok SEGS stk W regs mem 0x21f40 3.
Proof.
intros ly S W mem md regs stk HAR HRO Hstk Hsp.
split; [lia|]. split; [lia|]. split; [lia|]. split.
- intros a Ha. split.
  + replace a with (0x21f40 + Z.of_nat (Z.to_nat (a - 0x21f40))) by lia.
    rewrite (sivb_ro_fmt _ HRO (Z.to_nat (a - 0x21f40))) by (change (length RO_lit_21f40) with 3%nat; lia).
    discriminate.
  + unfold ascratch_stk. lia.
- pose proof alloc_ceiling_value as (Hcm & _).
  split; [apply amem_range_high; [lia | left; lia | lia]|].
  split; [exact (sivb_fmt_addressable B HB ly S W mem md HAR) | intros _; exact (sivb_fmt_hull B HB ly S W mem md HAR)].
Qed.

(* --- the line's block: a Theorem Labs lane's premise puts it in a live block, so 4096 <= pl and pl + |line| + 1 <= the
   allocator's ceiling (AR's block law) ------------------------------------------------------------------------ *)
Lemma sivb_line_block : forall ly S (W : world SEGS) mem md pl n,
AR SEGS B ly S W mem md -> in_blockA (ablocks B ly S) pl n -> 0 <= n ->
4096 <= pl /\ pl + n <= alloc_ceiling.
Proof.
intros ly S W mem md pl n HAR (p & k & Hpk & Hpx & Hxk) Hn.
destruct (al_blocks _ _ LAWS ly S W mem md p k HAR Hpk) as (Hp16 & Hp4096 & Hpceil & _).
pose proof (req_size_pos k ltac:(lia)) as [_ Hreq]. lia.
Qed.
(* the line's tail from its j-th byte, as a range a string entry may read *)
Lemma sivb_line_rd :
forall lyc Sc (Wc : world SEGS) memT mdT (regsT : bvmap 5 word) pl (line : list byte) j stk,
AR SEGS B lyc Sc Wc memT mdT ->
in_blockA (ablocks B lyc Sc) pl (Z.of_nat (length line) + 1) ->
(j <= length line)%nat -> alloc_ceiling <= spZ regsT - stk ->
aread_ok SEGS stk Wc regsT memT (pl + Z.of_nat j) (astr_len (skipn j line) + 1).
Proof.
intros lyc Sc Wc memT mdT regsT pl line j stk HARc (p & k & Hpk & Hp1 & Hp2) Hj Hstk.
unfold astr_len. rewrite length_skipn.
apply (aread_ok_of_block SEGS B LAWS stk lyc Sc Wc regsT memT mdT p k);
  [exact HARc | exact Hpk | lia | lia | lia | exact Hstk].
Qed.
(* the two trap branches, refuted from the line premise and the strspn wrapper's answer k <= |line| *)
Lemma sivb_traps_not_taken : forall ly S (W : world SEGS) mem md pl (line : list byte) k,
AR SEGS B ly S W mem md -> in_blockA (ablocks B ly S) pl (Z.of_nat (length line) + 1) ->
0 <= k <= Z.of_nat (length line) ->
0 < pl /\ pl + k < 2 ^ 64.
Proof.
intros ly S W mem md pl line k HAR HB1 Hk.
destruct (sivb_line_block ly S W mem md pl _ HAR HB1 ltac:(lia)) as [H4096 Hceil].
pose proof alloc_ceiling_lt as Hlt. lia.
Qed.
End y.

(* --- the symbolic entry state: the stack below the entry sp (the 96-byte frame and the realignment's 16), the
   shadow GOT word and cell, the use-after-return GOT word and flag (the record's const cell 0xb0c40 = 1, read
   through AR's al_const) ---------------------------------------------------------------------------------- *)
(* the two stack regions are split at the zero slot [sp - 96, sp - 88) the prologue writes (`sd zero,0(sp)`,
   0x8b8fc): the realigned slot the frame pointer goes to (`sd s8,0(s1)`, 0x8b994) is [sp1, sp1 + 8) with
   sp1 = 32 * ((sp - 96) / 32), which IS the zero slot when sp is 32-aligned, so the walk drops the zero slot's
   region (it is never read) before it seats the realigned one on the atom 34 *)
Definition sivb_regions0 : smem :=
[ YP09.mkRegion (Some 2%nat) (-96) (-88) (-96) (-88) []; YP09.mkRegion (Some 2%nat) (-88) 0 (-88) 0 [];
  got_regionP; bcell_regionP 32; uar_got_regionP 33; uar_cell_regionP 33 ].
Definition sivb_atoms0 : list (nat * afact) :=
[ (2%nat, mkAF (2^46) (2^47) 4); (32%nat, mkAF SB SB 0); (33%nat, mkAF 0x10000 0x606000 2);
  (34%nat, mkAF (2^46) (2^47) 5) ].
Definition ss_sivb0 : sstate := mkSS AF_sup_instance_verb sr_atoms sivb_regions0 None (mkFacts sivb_atoms0 [] []).
(* the atoms above the 32 registers: 32 the shadow base, 33 the use-after-return flag's cell, 34 the realigned
   stack pointer `andi sp,sp,-32` gives (0x8b930) *)
Definition sivb_extra0 (uar sp1 : Z) : list word := map (Z_to_bv 64) [SB; uar; sp1].

Section c2.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Lemma sivb_entry : forall STK W ly S regs mem md ch sp1,
112 <= STK ->
afn_pre SEGS B STK ly S W regs mem md ch ->
spZ regs - 112 <= sp1 <= spZ regs -> sp1 mod 32 = 0 ->
st_ok_pi SEGS VAL (Eimg (Ereg regs (sivb_extra0 (as_uar_cell B) sp1))) ss_sivb0
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_sup_instance_verb)) mem (seg_rom SEGS))).
Proof.
intros STK W ly S regs mem md ch sp1 HSTK HPRE Hsp1 Hsp1a.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & Kuar & Kgot & Kguar).
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot. rewrite (pal_cell B TL) in Kcell. rewrite (palf_got_uar B TLF) in Kguar.
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs (sivb_extra0 (as_uar_cell B) sp1))). pose proof pa_B_ok as HBASE.
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (as_uar_cell B)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 sp1) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E241 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E242 : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E253 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
pose proof (pa_obj_img 0 ltac:(lia)) as Hob0. pose proof (pa_obj_img 1 ltac:(lia)) as Hob1. pose proof (pa_obj_img 12 ltac:(lia)) as Hob12.
pose proof (palf_uar_img B TLF) as Huar. pose proof (palf_uar_al B TLF) as Huar4.
pose proof (palf_sep B TLF) as Hsep. cbn [zseps zseps_from fst snd] in Hsep.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
unfold ss_sivb0. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold sivb_regions0, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP.
repeat apply Forall_cons; try apply Forall_nil.
  + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Usp.
  split; [lia|]. split; [lia|]. split; [|constructor]. intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
  + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Usp.
  split; [lia|]. split; [lia|]. split; [|constructor]. intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
  + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  constructor; [|constructor].
  apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
  [cbn [sv_denot]; rewrite E253, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | pose proof (pa_val_range (A_OBJ 12)); zside | zside |].
  rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
  + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E253) by (pose proof (pa_val_range (A_OBJ 12)); lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  constructor; [|constructor].
  apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 (SOff 32 0) SB);
  [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
  rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
  + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) E242) by (pose proof (pa_val_range (A_OBJ 1)); lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  constructor; [|constructor].
  apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 1)) 0 8 (SOff 33 0) (as_uar_cell B));
  [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
  rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kguar).
  + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  rewrite (VB 33%nat (as_uar_cell B) E33) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  constructor; [|constructor].
  apply (chunk_ok_val SEGS E _ (as_uar_cell B) 0 4 (SLit 1) 1); [reflexivity | zside | zside |].
  rewrite Z.add_0_r. exact (val_mem_of_rd32 SEGS (w_H W) mem _ _ Kuar).
- apply pairwise_disjoint_of_extents.
unfold sivb_regions0, stack_region, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite (VB 33%nat (as_uar_cell B) E33) by lia.
rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia).
rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E253) by (pose proof (pa_val_range (A_OBJ 12)); lia).
rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) E242) by (pose proof (pa_val_range (A_OBJ 1)); lia).
cbn [base_val]. rewrite Usp.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
revert Hslo Hshi H47 Hceil C1 C3 HSTK Hstk0 Hob0 Hob1 Hob12 Huar Hsep. clear.
unfold ASAN_CEIL. intros.
rewrite !Z.add_0_r. repeat match goal with H : _ /\ _ |- _ => destruct H as [? ?] end.
repeat split; first [ assumption | (apply or_comm; assumption)
| (repeat match goal with H : _ \/ _ |- _ => clear H end; lia) ].
- split; [|split; [exact I | exact I]].
cbn [f_atoms atoms_ok sivb_atoms0]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite Usp, E32, E33, E34.
rewrite !unsigned_lit_small by (unfold SB in *; lia).
change (2 ^ 4) with 16. change (2 ^ 2) with 4. change (2 ^ 5) with 32. rewrite !Z.pow_0_r, !Z.mod_1_r.
repeat match goal with |- _ /\ _ => split end; unfold SB; try lia; exact Hsp1a.
Qed.
End c2.

(* the recorder-representation and allocator-law helpers that stood here are the kit's: CmdRecRest's
   cmd_stack_malloc_progress / cmd_frame_flag_law / cmd_model_laws, and the sivk_* layer of sup_instance_verb_kit.v *)
End b.
End a.

(* --- the walk's tactics (answer_code's preg / norm_ssp / nwin_tac) ----------------------------------------- *)
Ltac sivb_preg HS r Hr :=
lazymatch type of HS with
| st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
cbn [ms_regs restrict mkst] in Hr
| st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
pose proof (st_ok_restrict_reg segs H E ss ms r HS) as Hr;
let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
cbn [ms_regs restrict mkst] in Hr
end.
Ltac sivb_norm_ssp HS :=
lazymatch type of HS with
| st_ok_pi _ _ _ ?ss3 _ => let v := eval vm_compute in ss3 in change ss3 with v in HS
| st_ok _ _ ?ss3 _ => let v := eval vm_compute in ss3 in change ss3 with v in HS
end.
Ltac sivb_nwin_tac rwt :=
let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
intros (r & Hin & Hr);
lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end;
repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rwt Hr | ]);
destruct Hin.

(* --- the symbolic state across a call that returns at another FP state (the snprintf wrapper, answer): the
   kit's PaFx.st_ok_pi_restrict_xfx moves it to the returned FP state (PASS4-REFIT.md A.5, "in place") ---------- *)
Ltac sivb_move_fx HS fxo fxn :=
  let T := type of HS in
  let T1 := eval pattern fxo in T in
  lazymatch T1 with
  | ?F fxo => let T2 := eval cbv beta in (F fxn) in
      let HSn := fresh "HSn" in
      assert (HSn : T2) by exact (PaFx.st_ok_pi_restrict_xfx fxo fxn _ _ _ _ _ _ _ _ _ HS);
      clear HS; rename HSn into HS
  end.
