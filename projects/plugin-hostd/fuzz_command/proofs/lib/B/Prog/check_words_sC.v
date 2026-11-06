(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: check_words' walk segment C on fuzz_command's ASan+UBSan build, the B twin of
   lib/A/Prog/check_words_sC.v (the A walk, an earlier version); lxor_ones and U_not are copied from
   lib/B/YE2y.v:420-436 as cwc_lxor_ones and cwc_U_not. *)
(* check_words (plugin-hostd/fuzz_command.asan-ubsan, entry 0x87ae8), walk segment C (lib/B/Prog/check_words_d.v):
   the head of the call loop at call c, seg_C : ST_IH c 0 -> ST_D c -> ST_LH c.

   B code 0x87cb4 .. 0x87d74 (listing 0x1784 .. 0x1844), with s1 = sp1, s5 = c, s6 = the shadow base, and
   cp = &g_rec.calls[c].fn = A_G_REC + 16 + 56 c:
     0x87cb8  trap site (UBSan, `li a0,17; beq s5,a0`, to the `unimp` at 0x8816c): c = 17. Not reached: atom 21
              (c) is in [0, 15] (c < ncalls <= 16, rec_repA's ag1_calls).
     0x87cc0  104(s1) := c.
     0x87cd0  trap site (`bltu 72(s1), 56 c`): ~(g_rec + 16) < 56 c. Not reached: 72(s1) holds the literal
              2^64 - 1 - (g_rec + 16) and atom 37 (56 c, the alias of the engine's `SMd M_MUL c 56`) is in
              [0, 840].
     0x87ce4  the instrumented check of cp (lb of the shadow byte SB + cp / 8; the partial-granule path
              0x88060 .. 0x8806c back to 0x87cec, the error path 0x881f8). Not reached: the shadow entry of
              [cp, cp + 8) (atom 32 = cp, g_rec addressable by CW_ZSH_P).
     0x87cec  96(s1) := SB + cp / 8, 128(s1) := cp, fn := lw 0(cp).
     0x87cfc  trap site (`li a1,25; bltu a1,fn`): 25 < fn. Not reached: atom 33 (fn) is in [0, 25]
              (acall_at's 0 <= fn < REC_FN_COUNT).
     0x87d08  trap site (`bltu 56(s1), 8 fn`): ~0xa5920 < 8 fn. Not reached: 56(s1) holds 2^64 - 1 - 0xa5920 and
              atom 38 (8 fn, the alias of `SAlu ALU_SLL fn 3`) is in [0, 200].
     0x87d0c  s10 := cp + 4, 184(s1) := SB + (cp + 4) / 8 and the instrumented check of nargs (the partial path
              0x88070 .. 0x8807c back to 0x87d28, the error path 0x881fc). Not reached: the same shadow entry.
     0x87d28  nargs := lw 0(s10), 136(s1) := (Wd + 16) / 8, `blez nargs` (0x87d38) to D (0x87f80).
     0x87d3c  (nargs > 0) the table slot 0xa5920 + 8 fn (atom 35, the alias of 0xa5920 + atom 38) and its
              instrumented check (lbu; the error path 0x881d4). Not reached: the shadow entry of the slot (the
              table addressable by CW_ZSH_P). s9 := 0, s2 := 0, s4 := cw_tptr fn (cmd_ro_ok's RO_g_call_words,
              one closed check cwc_tbl_ok over the 26 slots), 168(s1) := ~(cp + 8), s8 := 120(s1) = cp + 8,
              s11 := 112(s1) = cp + 8, and the item loop's head IH (0x87d78) follows with item 0 and cursor 0.
   The token engine decides the four trap branches from the atom facts (lib/Reusable/YP0m.v decide_cond) and
   removes the three instrumented checks with their slow paths (lib/B/Prog/PaShadow.v tok_load / tok_branch_pi).
   Seed: atoms 9 = sp1, 21 = c, 22 = SB; extra atoms 32 = cp, 33 = fn, 34 = nargs, 35 = 0xa5920 + 8 fn,
   36 = cw_tptr fn, 37 = 56 c, 38 = 8 fn, 39 = Wd + 16. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaCall PaCallRun PaDenot PaSB PaLibF PaLibG PaLibH.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtString RtNumber RtFormat RtAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo CmdAddr PaArt.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv CommandModel printf_facts_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
joined_c check_words_add_c check_words_chain_c check_words_pin_set_c sup_reply_code_c HarnessPropsA check_words_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import check_words_d.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---------------------------------------------------------------------------------------------------------- *)
(* the seed at LH (closed terms; the run's forms of the four aliased values were read off the token engine) *)
Definition cBx : sv := SOff 22 0.
Definition cBspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition c_regions : smem :=
[ YP09.mkRegion (Some 9%nat) 40 80 0 0
    [YP09.mkChunk 40 (CVal 8 (SLit 0xa5920)); YP09.mkChunk 56 (CVal 8 (SLit (cw_not 0xa5920)));
     YP09.mkChunk 64 (CVal 8 (SLit (A_G_REC + 16))); YP09.mkChunk 72 (CVal 8 (SLit (cw_not (A_G_REC + 16))))];
  YP09.mkRegion (Some 9%nat) 96 112 96 112 [];
  YP09.mkRegion (Some 9%nat) 112 128 0 0 [YP09.mkChunk 112 (CVal 8 (SOff 32 8)); YP09.mkChunk 120 (CVal 8 (SOff 32 8))];
  YP09.mkRegion (Some 9%nat) 128 144 128 144 [];
  YP09.mkRegion (Some 9%nat) 144 152 0 0 [YP09.mkChunk 144 (CVal 8 (SOff 39 0))];
  YP09.mkRegion (Some 9%nat) 168 176 168 176 [];
  YP09.mkRegion (Some 9%nat) 184 192 184 192 [];
  YP09.mkRegion (Some 32%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 33 0)); YP09.mkChunk 4 (CVal 4 (SOff 34 0))];
  YP09.mkRegion (Some 35%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 36 0))] ].
Definition c_atoms : list (nat * afact) :=
[ (9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (21%nat, mkAF 0 15 0); (22%nat, mkAF SB SB 0);
  (32%nat, mkAF (A_G_REC + 16) (A_G_REC + 16 + 56 * 15) 3); (33%nat, mkAF 0 25 0); (34%nat, mkAF 0 6 0);
  (35%nat, mkAF 0xa5920 (0xa5920 + 200) 3); (36%nat, mkAF 0x212c0 0x21ae0 0);
  (37%nat, mkAF 0 (56 * 15) 3); (38%nat, mkAF 0 200 3) ].
Definition c_alias : list (sv * sv) :=
[ (SMd M_MUL (SOff 21 0) (SLit 56), SOff 37 0);
  (SOff 37 (A_G_REC + 16), SOff 32 0);
  (SAlu ALU_SLL (SOff 33 0) (SLit 3), SOff 38 0);
  (SOff 38 0xa5920, SOff 35 0) ].
Definition ssC : sstate := mkSS CW_PC_LH sr_atoms c_regions None (mkFacts c_atoms [] c_alias).
Definition c_SH : list shent := [mkSHE 32 0 8; mkSHE 35 0 8].
Definition c_extra (c fn nargs wd16 : Z) : list word :=
[Z_to_bv 64 (A_G_REC + 16 + 56 * c); Z_to_bv 64 fn; Z_to_bv 64 nargs; Z_to_bv 64 (0xa5920 + 8 * fn);
 Z_to_bv 64 (cw_tptr fn); Z_to_bv 64 (56 * c); Z_to_bv 64 (8 * fn); Z_to_bv 64 wd16].
(* the four stack windows the segment writes: s1 + 96 .. 112 (SB + cp / 8, c), s1 + 128 .. 144 (cp, (Wd + 16) / 8),
   s1 + 168 (~(cp + 8)) and s1 + 184 (SB + (cp + 4) / 8) *)
Definition cwZ (sp1 a : Z) : Prop :=
  (sp1 + 96 <= a < sp1 + 112) \/ (sp1 + 128 <= a < sp1 + 144) \/ (sp1 + 168 <= a < sp1 + 176) \/
  (sp1 + 184 <= a < sp1 + 192).
Definition cwc_wok (ws : list (option nat * Z * Z)) : bool :=
forallb (fun w => match w with (b, lo, hi) =>
  (hi <=? lo) || (match b with Some n => Nat.eqb n 9 | None => false end &&
    (((96 <=? lo) && (hi <=? 112)) || ((128 <=? lo) && (hi <=? 144)) || ((168 <=? lo) && (hi <=? 176)) ||
     ((184 <=? lo) && (hi <=? 192)))) end) ws.
(* a stack slot at s1 + o of n bytes that no window of the segment touches *)
Definition cwc_out (o n : Z) : bool :=
  ((o + n <=? 96) || (112 <=? o)) && ((o + n <=? 128) || (144 <=? o)) && ((o + n <=? 168) || (176 <=? o)) &&
  ((o + n <=? 184) || (192 <=? o)).

(* ---------------------------------------------------------------------------------------------------------- *)
(* the template table, per recorded function (closed checks) *)
Lemma cwc_fn_cases : forall fn, 0 <= fn < 26 ->
  fn = 0 \/ fn = 1 \/ fn = 2 \/ fn = 3 \/ fn = 4 \/ fn = 5 \/ fn = 6 \/ fn = 7 \/ fn = 8 \/ fn = 9 \/ fn = 10 \/
  fn = 11 \/ fn = 12 \/ fn = 13 \/ fn = 14 \/ fn = 15 \/ fn = 16 \/ fn = 17 \/ fn = 18 \/ fn = 19 \/ fn = 20 \/
  fn = 21 \/ fn = 22 \/ fn = 23 \/ fn = 24 \/ fn = 25.
Proof. intros fn H. lia. Qed.
Ltac cwc_fn_split H := repeat (destruct H as [H|H]; [subst; vm_compute; reflexivity|]); subst; vm_compute; reflexivity.

(* the code's parse of each template is the model's item list *)
Lemma cw_parse_tpl : forall fn, 0 <= fn < 26 -> cw_parse (cw_tpl fn) = PCW.call_items fn.
Proof. intros fn H. apply cwc_fn_cases in H. cwc_fn_split H. Qed.

Lemma cwc_tptr_b : forall fn, 0 <= fn < 26 -> (0x212c0 <=? cw_tptr fn) && (cw_tptr fn <=? 0x21ae0) = true.
Proof. intros fn H. apply cwc_fn_cases in H. cwc_fn_split H. Qed.
Lemma cwc_tptr_rng : forall fn, 0 <= fn < 26 -> 0x212c0 <= cw_tptr fn <= 0x21ae0.
Proof.
intros fn H. pose proof (cwc_tptr_b fn H) as Hb. apply andb_prop in Hb as [H1 H2].
apply Z.leb_le in H1. apply Z.leb_le in H2. lia.
Qed.
(* the 26 slots of g_call_words (0xa5920, RO_g_call_words) hold cw_tptr fn: one closed check *)
Definition cwc_tbl_ok : bool :=
  forallb (fun fn => forallb (fun k =>
    bv_unsigned (nth (Z.to_nat (8 * fn) + k) RO_g_call_words (Z_to_bv 8 0)) =? YG0f.le_byte (cw_tptr fn) 8 k)
    (seq 0 8)) (map Z.of_nat (seq 0 26)).
Lemma cwc_tbl_ok_true : cwc_tbl_ok = true.
Proof. vm_compute. reflexivity. Qed.
Lemma cwc_tbl_b : forall fn, 0 <= fn < 26 ->
  forallb (fun k => bv_unsigned (nth (Z.to_nat (8 * fn) + k) RO_g_call_words (Z_to_bv 8 0)) =? YG0f.le_byte (cw_tptr fn) 8 k)
    (seq 0 8) = true.
Proof.
intros fn H. pose proof cwc_tbl_ok_true as T. unfold cwc_tbl_ok in T. rewrite forallb_forall in T.
apply T. apply in_map_iff. exists (Z.to_nat fn). split; [lia | apply in_seq; lia].
Qed.
Lemma cwc_tbl_len : length RO_g_call_words = 208%nat.
Proof. vm_compute. reflexivity. Qed.
Lemma cwc_tbl : forall (rd : reader) fn, abytes_atR rd 0xa5920 RO_g_call_words -> 0 <= fn < 26 ->
  aval_mem rd (0xa5920 + 8 * fn) 8 (cw_tptr fn).
Proof.
intros rd fn H Hfn k Hk.
pose proof (cwc_tbl_b fn Hfn) as Hb. rewrite forallb_forall in Hb.
assert (Hin : In k (seq 0 8)) by (apply in_seq; lia).
specialize (Hb k Hin). apply Z.eqb_eq in Hb. rewrite <- Hb.
pose proof cwc_tbl_len as Hlen.
replace (0xa5920 + 8 * fn + Z.of_nat k) with (0xa5920 + Z.of_nat (Z.to_nat (8 * fn) + k)) by lia.
apply H. lia.
Qed.
Lemma cwc_tbl_of_ro : forall rd, cmd_ro_bytes rd -> abytes_atR rd 0xa5920 RO_g_call_words.
Proof.
intros rd H. unfold cmd_ro_bytes in H.
repeat lazymatch type of H with
| abytes_atR _ 0xa5920 _ /\ _ => exact (proj1 H)
| _ /\ _ => apply proj2 in H
end.
Qed.

(* ---------------------------------------------------------------------------------------------------------- *)
(* small facts *)
Lemma cwc_lxor_ones : forall a n, 0 < n -> 0 <= a < 2 ^ n -> Z.lxor a (Z.ones n) = Z.ones n - a.
Proof.
intros a n Hn Ha.
assert (Hlog : Z.log2 a < n).
{ destruct (Z.eq_dec a 0) as [->|Hz]; [rewrite Z.log2_nonpos; lia|]. apply (proj1 (Z.log2_lt_pow2 a n ltac:(lia))). lia. }
rewrite <- (Z.ldiff_ones_l_low a n) by lia.
rewrite Z.ldiff_land.
assert (E : Z.land (Z.ones n) (Z.lnot a) = Z.land (Z.lnot a) (Z.ones n)) by apply Z.land_comm. rewrite E.
rewrite Z.land_ones by lia. unfold Z.lnot, Z.ones. rewrite Z.shiftl_1_l.
replace (Z.pred (- a)) with ((2 ^ n - 1 - a) + (-1) * 2 ^ n) by lia. rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
Qed.
Lemma cwc_U_not : forall E v, U E (SAlu ALU_XOR v (SLit (-1))) = 2 ^ 64 - 1 - U E v.
Proof.
intros E v. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit. change (zcanon (-1)) with (Z.ones 64).
pose proof (U_range E v) as Hr. unfold M64 in Hr. rewrite cwc_lxor_ones by lia.
change (Z.ones 64) with (2 ^ 64 - 1). apply zcanon_small. lia.
Qed.
Lemma cwc_not_off : forall E n c v, ew E n = Z_to_bv 64 v -> 0 <= v -> 0 <= c -> v + c < 2 ^ 64 ->
  sv_denot E (SAlu ALU_XOR (SOff n c) (SLit (-1))) = Z_to_bv 64 (cw_not (v + c)).
Proof.
intros E n c v Hn Hv Hc Hvc.
rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E (SAlu ALU_XOR (SOff n c) (SLit (-1))))). f_equal.
change (U E (SAlu ALU_XOR (SOff n c) (SLit (-1))) = cw_not (v + c)).
rewrite cwc_U_not. rewrite (U_atom_off E n v c Hn) by lia. unfold cw_not. reflexivity.
Qed.
Lemma cwc_aval_eq : forall (rd rd' : reader) a n v,
  (forall k, (k < n)%nat -> rd' (a + Z.of_nat k) = rd (a + Z.of_nat k)) -> aval_mem rd a n v -> aval_mem rd' a n v.
Proof. intros rd rd' a n v Hk H k Hk'. rewrite (Hk k Hk'). exact (H k Hk'). Qed.
Lemma cwc_notZ : forall sp1 a, (a < sp1 + 96 \/ sp1 + 192 <= a) -> ~ cwZ sp1 a.
Proof. intros sp1 a H. unfold cwZ. lia. Qed.
Lemma cwc_notZ_out : forall sp1 o n i, cwc_out o n = true -> 0 <= i < n -> ~ cwZ sp1 (sp1 + o + i).
Proof.
intros sp1 o n i H Hi. unfold cwc_out in H.
apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
apply orb_prop in H1. apply orb_prop in H2. apply orb_prop in H3. apply orb_prop in H4.
rewrite !Z.leb_le in H1, H2, H3, H4. unfold cwZ. lia.
Qed.
Lemma cwc_keep_out : forall (rd rd' : reader) sp1 a n v,
  (forall x, 0 <= x < 2 ^ 64 -> ~ cwZ sp1 x -> rd' x = rd x) -> 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  (a + Z.of_nat n <= sp1 + 96 \/ sp1 + 192 <= a) -> aval_mem rd a n v -> aval_mem rd' a n v.
Proof.
intros rd rd' sp1 a n v K H0 H1 H2 H k Hk. rewrite K; [exact (H k Hk) | lia |]. apply cwc_notZ. lia.
Qed.
Lemma cwc_keep_slot : forall (rd rd' : reader) sp1 o n v,
  (forall x, 0 <= x < 2 ^ 64 -> ~ cwZ sp1 x -> rd' x = rd x) -> 0 <= sp1 + o -> sp1 + o + Z.of_nat n <= 2 ^ 64 ->
  cwc_out o (Z.of_nat n) = true -> aval_mem rd (sp1 + o) n v -> aval_mem rd' (sp1 + o) n v.
Proof.
intros rd rd' sp1 o n v K H0 H1 Ho H k Hk. rewrite K; [exact (H k Hk) | lia |].
apply (cwc_notZ_out sp1 o (Z.of_nat n) (Z.of_nat k) Ho). lia.
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
Lemma cwc_mod8 : forall x y, x = y * 8 -> x mod 8 = 0.
Proof. intros x y ->. apply Z_mod_mult. Qed.

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
(* the per-binary walk facts this segment uses *)
Hypothesis LAWS : AR_laws SEGS B.
(* the record facts of check_words_d.v (proved from lib/B/Prog/CmdRecFacts.v in check_words_rf.v) *)
Hypothesis cmd_prog_unowned : cmd_prog_unowned_P B.
Hypothesis ZSH_cw : CW_ZSH_P B.
Hypothesis cw_ro_unowned : cw_ro_unowned_P B.
Let RUN := paj_run (L := cmd_listing) (PL := PL_cmd) (PI := PI) B LAWS.
Let RUNTO := paj_run_to (L := cmd_listing) (PL := PL_cmd) (PI := PI) B LAWS.
Let BR := paj_branch (PI := PI).

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
apply orb_prop in Hw as [Hw|Hw]; [apply orb_prop in Hw as [Hw|Hw]; [apply orb_prop in Hw as [Hw|Hw]|]|];
  apply andb_prop in Hw as [H1 H2]; apply Z.leb_le in H1; apply Z.leb_le in H2; lia.
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
  0 <= i < 208 -> rdW W memc (0xa5920 + i) = rdW W0 mem (0xa5920 + i).
Proof.
intros STK sp0 ly S W0 mem md own lyc Sc W memc mdc k i HJ Hi.
destruct (cw_ro_unowned 0xa5920 208 i ltac:(unfold CW_ZSH; right; left; reflexivity) ltac:(unfold A_G_REC; lia) Hi)
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
    aval_mem (rdW Wc memc) (A_G_REC + 16 + 56 * c) 4 fn /\
    aval_mem (rdW Wc memc) (A_G_REC + 16 + 56 * c + 4) 4 (Z.of_nat (length args)) /\
    aval_mem (rdW Wc memc) (0xa5920 + 8 * fn) 8 (cw_tptr fn).
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
replace (A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat (Z.to_nat c) + CALL_OFF_FN) with (A_G_REC + 16 + 56 * c) in Hvfn
  by (unfold OFF_CALLS, CALL_SIZE, CALL_OFF_FN; lia).
replace (A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat (Z.to_nat c) + CALL_OFF_NARGS) with (A_G_REC + 16 + 56 * c + 4) in Hvna
  by (unfold OFF_CALLS, CALL_SIZE, CALL_OFF_NARGS; lia).
destruct HRO as [HB _]. pose proof (cwc_tbl _ fn (cwc_tbl_of_ro _ HB) Hfn) as Htb.
exists fn, args. split; [reflexivity|]. split; [exact Hfn|]. split; [exact Hla|]. split; [lia|].
split; [apply (cwc_aval_eq (cw_rd0 e)); [intros kk Hk; apply (cwc_grec_kept _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ); lia | exact Hvfn]|].
split; [apply (cwc_aval_eq (cw_rd0 e)); [intros kk Hk; apply (cwc_grec_kept _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ); lia | exact Hvna]|].
apply (cwc_aval_eq (cw_rd0 e)); [|exact Htb].
intros kk Hk. replace (0xa5920 + 8 * fn + Z.of_nat kk) with (0xa5920 + (8 * fn + Z.of_nat kk)) by lia.
apply (cwc_tbl_kept _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ). lia.
Qed.

(* ---------------------------------------------------------------------------------------------------------- *)
(* the seed at LH *)
Lemma cwc_seed : forall (W : world SEGS) (regsc : bvmap 5 word) memc sp1 c fn nargs wd16,
  getr regsc 9 = w64 sp1 -> 2 ^ 46 <= sp1 <= 2 ^ 47 -> sp1 mod 32 = 0 -> getr regsc 22 = w64 CW_SB ->
  getr regsc 21 = w64 c -> 0 <= c <= 15 -> 0 <= fn <= 25 -> 0 <= nargs <= 6 -> 0 <= wd16 < 2 ^ 63 ->
  aval_mem (rdW W memc) (sp1 + 40) 8 0xa5920 ->
  aval_mem (rdW W memc) (sp1 + 56) 8 (cw_not 0xa5920) ->
  aval_mem (rdW W memc) (sp1 + 64) 8 (A_G_REC + 16) ->
  aval_mem (rdW W memc) (sp1 + 72) 8 (cw_not (A_G_REC + 16)) ->
  aval_mem (rdW W memc) (sp1 + 112) 8 (A_G_REC + 24 + 56 * c) ->
  aval_mem (rdW W memc) (sp1 + 120) 8 (A_G_REC + 24 + 56 * c) ->
  aval_mem (rdW W memc) (sp1 + 144) 8 wd16 ->
  aval_mem (rdW W memc) (A_G_REC + 16 + 56 * c) 4 fn ->
  aval_mem (rdW W memc) (A_G_REC + 16 + 56 * c + 4) 4 nargs ->
  aval_mem (rdW W memc) (0xa5920 + 8 * fn) 8 (cw_tptr fn) ->
  (forall a, sp1 + 96 <= a < sp1 + 192 -> apresent (w_H W) memc a) ->
  range_addressable (rdW W memc) SHADOW_OFF A_G_REC 960 ->
  range_addressable (rdW W memc) SHADOW_OFF 0xa5920 208 ->
  st_ok_pi SEGS VAL (Eimg (Ereg regsc (c_extra c fn nargs wd16))) ssC
    (restrict (w_H W) (mkst regsc (Z_to_bv 64 (BASE + CW_PC_LH)) memc (seg_rom SEGS))) /\
  sh_ok SEGS cBx c_SH (Eimg (Ereg regsc (c_extra c fn nargs wd16))) (mrestrict (w_H W) memc).
Proof.
intros W regsc memc sp1 c fn nargs wd16 H9 Hsp Hsp32 H22 H21 Hc Hfn Hna Hwd V40 V56 V64 V72 V112 V120 V144
  VFN VNA VTB HPR RA1 RA2.
assert (HG : A_G_REC = 6173376) by reflexivity.
pose proof (cwc_tptr_rng fn ltac:(lia)) as Htp.
set (E := Eimg (Ereg regsc (c_extra c fn nargs wd16))).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regsc r).
{ intros n r Hn. unfold E. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
assert (ES : forall m, (32 <= m < A_TEXT)%nat -> ew E m = nth (m - 32) (c_extra c fn nargs wd16) (Z_to_bv 64 0)).
{ intros m Hm. replace m with (32 + (m - 32))%nat at 1 by lia. unfold E. rewrite Eimg_low by lia. apply ew_Ereg_extra. }
assert (E9 : ew E 9 = Z_to_bv 64 sp1) by (rewrite (EE 9%nat 9%bv eq_refl); exact H9).
assert (E21 : ew E 21 = Z_to_bv 64 c) by (rewrite (EE 21%nat 21%bv eq_refl); exact H21).
assert (E22 : ew E 22 = Z_to_bv 64 2147450880) by (rewrite (EE 22%nat 22%bv eq_refl); exact H22).
pose proof (ES 32%nat ltac:(unfold A_TEXT; lia)) as E32. pose proof (ES 33%nat ltac:(unfold A_TEXT; lia)) as E33.
pose proof (ES 34%nat ltac:(unfold A_TEXT; lia)) as E34. pose proof (ES 35%nat ltac:(unfold A_TEXT; lia)) as E35.
pose proof (ES 36%nat ltac:(unfold A_TEXT; lia)) as E36. pose proof (ES 37%nat ltac:(unfold A_TEXT; lia)) as E37.
pose proof (ES 38%nat ltac:(unfold A_TEXT; lia)) as E38. pose proof (ES 39%nat ltac:(unfold A_TEXT; lia)) as E39.
cbn [Nat.sub nth c_extra] in E32, E33, E34, E35, E36, E37, E38, E39.
clear EE ES.
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
assert (Hx8 : (A_G_REC + 16 + 56 * c) mod 8 = 0) by (apply (cwc_mod8 _ (771674 + 7 * c)); lia).
assert (Hs8 : (0xa5920 + 8 * fn) mod 8 = 0) by (apply (cwc_mod8 _ (84772 + fn)); lia).
assert (Hm56 : (56 * c) mod 8 = 0) by (apply (cwc_mod8 _ (7 * c)); lia).
assert (Hm8 : (8 * fn) mod 8 = 0) by (apply (cwc_mod8 _ fn); lia).
split.
- unfold ssC. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  + unfold E. apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold c_regions.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    * rewrite (VB 9%nat sp1 E9) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      -- apply (chunk_ok_val SEGS E _ sp1 40 8 _ 0xa5920); [cbn [sv_denot]; reflexivity | zside | zside |].
         exact (cwc_val_of_aval _ _ _ _ _ V40).
      -- apply (chunk_ok_val SEGS E _ sp1 56 8 _ (cw_not 0xa5920)); [cbn [sv_denot]; reflexivity | unfold cw_not; zside | zside |].
         exact (cwc_val_of_aval _ _ _ _ _ V56).
      -- apply (chunk_ok_val SEGS E _ sp1 64 8 _ (A_G_REC + 16)); [cbn [sv_denot]; reflexivity | rewrite HG; zside | zside |].
         exact (cwc_val_of_aval _ _ _ _ _ V64).
      -- apply (chunk_ok_val SEGS E _ sp1 72 8 _ (cw_not (A_G_REC + 16)));
           [cbn [sv_denot]; reflexivity | unfold cw_not; rewrite HG; zside | zside |].
         exact (cwc_val_of_aval _ _ _ _ _ V72).
    * rewrite (VB 9%nat sp1 E9) by lia. split; [lia|]. split; [lia|].
      split; [intros o Ho; apply (apresent_writable SEGS); apply HPR; lia|]. apply Forall_nil.
    * rewrite (VB 9%nat sp1 E9) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      -- apply (chunk_ok_val SEGS E _ sp1 112 8 _ (A_G_REC + 24 + 56 * c));
           [rewrite (cwc_DO E 32 _ 8 E32) by lia; f_equal; lia | zside | zside |].
         exact (cwc_val_of_aval _ _ _ _ _ V112).
      -- apply (chunk_ok_val SEGS E _ sp1 120 8 _ (A_G_REC + 24 + 56 * c));
           [rewrite (cwc_DO E 32 _ 8 E32) by lia; f_equal; lia | zside | zside |].
         exact (cwc_val_of_aval _ _ _ _ _ V120).
    * rewrite (VB 9%nat sp1 E9) by lia. split; [lia|]. split; [lia|].
      split; [intros o Ho; apply (apresent_writable SEGS); apply HPR; lia|]. apply Forall_nil.
    * rewrite (VB 9%nat sp1 E9) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS E _ sp1 144 8 _ wd16); [rewrite (cwc_DO E 39 _ 0 E39) by lia; f_equal; lia | zside | zside |].
      exact (cwc_val_of_aval _ _ _ _ _ V144).
    * rewrite (VB 9%nat sp1 E9) by lia. split; [lia|]. split; [lia|].
      split; [intros o Ho; apply (apresent_writable SEGS); apply HPR; lia|]. apply Forall_nil.
    * rewrite (VB 9%nat sp1 E9) by lia. split; [lia|]. split; [lia|].
      split; [intros o Ho; apply (apresent_writable SEGS); apply HPR; lia|]. apply Forall_nil.
    * rewrite (VB 32%nat (A_G_REC + 16 + 56 * c) E32) by lia. split; [lia|]. split; [lia|].
      split; [intros o Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      -- apply (chunk_ok_val SEGS E _ (A_G_REC + 16 + 56 * c) 0 4 _ fn);
           [rewrite (cwc_DO E 33 fn 0 E33) by lia; f_equal; lia | zside | zside |].
         rewrite Z.add_0_r. exact (cwc_val_of_aval _ _ _ _ _ VFN).
      -- apply (chunk_ok_val SEGS E _ (A_G_REC + 16 + 56 * c) 4 4 _ nargs);
           [rewrite (cwc_DO E 34 nargs 0 E34) by lia; f_equal; lia | zside | zside |].
         exact (cwc_val_of_aval _ _ _ _ _ VNA).
    * rewrite (VB 35%nat (0xa5920 + 8 * fn) E35) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS E _ (0xa5920 + 8 * fn) 0 8 _ (cw_tptr fn));
        [rewrite (cwc_DO E 36 _ 0 E36) by lia; f_equal; lia | zside | zside |].
      rewrite Z.add_0_r. exact (cwc_val_of_aval _ _ _ _ _ VTB).
  + apply pairwise_disjoint_of_extents. unfold c_regions, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (VB 9%nat sp1 E9) by lia. rewrite (VB 32%nat (A_G_REC + 16 + 56 * c) E32) by lia.
    rewrite (VB 35%nat (0xa5920 + 8 * fn) E35) by lia.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
  + unfold facts_ok. cbn [f_atoms f_conds f_alias]. split; [|split; [exact I|]].
    * unfold c_atoms. cbn [atoms_ok]. unfold afact_ok; cbn [af_lo af_hi af_al2].
      rewrite E9, E21, E22, E32, E33, E34, E35, E36, E37, E38.
      rewrite !unsigned_lit_small by (rewrite ?HG; lia).
      rewrite ?Z.pow_0_r, ?Z.mod_1_r. change (2 ^ 5) with 32. change (2 ^ 3) with 8.
      unfold SB.
      repeat match goal with |- _ /\ _ => split end;
        first [exact I | lia | exact Hsp32 | exact Hx8 | exact Hs8 | exact Hm56 | exact Hm8 | reflexivity].
    * unfold c_alias. cbn [alias_ok]. split; [|split; [|split; [|split; [|exact I]]]]; apply U_inj.
      -- rewrite U_SMd. cbn [zmd_raw].
         rewrite (U_atom E 21 c E21) by lia. rewrite U_SLit. change (zcanon 56) with 56.
         rewrite (U_atom E 37 (56 * c) E37) by lia. rewrite zcanon_small by lia. lia.
      -- rewrite (U_atom_off E 37 (56 * c) (A_G_REC + 16) E37) by lia.
         rewrite (U_atom E 32 _ E32) by lia. lia.
      -- rewrite U_SAlu. cbn [zalu_raw].
         rewrite (U_atom E 33 fn E33) by lia. rewrite U_SLit.
         change (Z.land (zcanon 3) 63) with 3. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8.
         rewrite (U_atom E 38 (8 * fn) E38) by lia. rewrite zcanon_small by lia. lia.
      -- rewrite (U_atom_off E 38 (8 * fn) 0xa5920 E38) by lia.
         rewrite (U_atom E 35 _ E35) by lia. lia.
- unfold sh_ok, c_SH. repeat apply Forall_cons; try apply Forall_nil.
  + apply (shent_ok_of_range SEGS (w_H W) memc E cBx 32 A_G_REC 960 (A_G_REC + 16 + 56 * c) 0 8 RA1).
    * unfold cBx. rewrite (U_atom E 22 _ E22) by lia. reflexivity.
    * apply (U_atom E 32 _ E32). lia.
    * lia.
    * lia.
    * intros x Hx. cbn [Z.min Z.max] in Hx. unfold SHADOW_OFF. lia.
  + apply (shent_ok_of_range SEGS (w_H W) memc E cBx 35 0xa5920 208 (0xa5920 + 8 * fn) 0 8 RA2).
    * unfold cBx. rewrite (U_atom E 22 _ E22) by lia. reflexivity.
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
  getr regs2 8 = getr regsc 8 -> getr regs2 9 = getr regsc 9 -> getr regs2 22 = getr regsc 22 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ cwZ sp1 a -> rdW Wc mem2 a = rdW Wc memc a) ->
  cw_core B e lyc Sc Wc regs2 mem2 mdc2 pos sp1 EV_JOINED /\ cw_line B MT e lyc Sc (rdW Wc mem2) line /\
  cw_lscr e (rdW Wc mem2) sp1 (frame_addr (e_ly e) 0 pos) line c.
Proof.
intros e lyc Sc Wc regsc memc mdc regs2 mem2 mdc2 pos sp1 line c HC HL HS HJ2 R2 R3 R4 R8 R9 R22 KEEP.
destruct HC as (HJ & Hsp & Hsp32 & Hspr & H3 & H4 & H8 & H9 & H22 & Hsav & V16 & V24 & V32 & V56F & SB4 & SB5).
pose proof HJ2 as (HAR & Hly & _ & _ & _ & Hfr & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _ & _).
destruct Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & _).
assert (HSTK : CHECK_WORDS_STK = 16848) by (vm_compute; reflexivity).
assert (HF : 4096 <= frame_addr (e_ly e) 0 pos /\ frame_addr (e_ly e) 0 pos + 64 <= alloc_ceiling).
{ assert (Hin : In (0, pos) (frames Sc)) by (rewrite Hfr; apply in_or_app; left; left; reflexivity).
  destruct (frames_bounds SEGS B LAWS lyc Sc Wc mem2 mdc2 0 pos HAR Hin) as (Hf1 & Hf2 & _).
  assert (Hfa : frame_addr lyc 0 pos = frame_addr (e_ly e) 0 pos).
  { unfold frame_addr. destruct Hly as (_ & _ & _ & _ & _ & HlyF & _). rewrite HlyF. reflexivity. }
  assert (Hfb : fs_frame_bytes 0 = 64) by (vm_compute; reflexivity).
  rewrite Hfa, Hfb in *. lia. }
pose proof (Z.div_pos (frame_addr (e_ly e) 0 pos) 8 ltac:(lia) ltac:(lia)) as HF8a.
pose proof (Z.div_le_upper_bound (frame_addr (e_ly e) 0 pos) 8 (2 ^ 44) ltac:(lia) ltac:(lia)) as HF8b.
assert (Hsp1 : alloc_ceiling + 16000 <= sp1 /\ sp1 + 320 <= cw_sp0 e /\ cw_sp0 e <= 2 ^ 47) by lia.
clear Hceil Hslo Hshi H47.
split; [|split].
- split; [exact HJ2|]. split; [unfold spZ in *; rewrite R2; exact Hsp|]. split; [exact Hsp32|].
  split; [exact Hspr|].
  split; [rewrite R3; exact H3|]. split; [rewrite R4; exact H4|]. split; [rewrite R8; exact H8|].
  split; [rewrite R9; exact H9|]. split; [rewrite R22; exact H22|].
  split.
  { intros j r Hj. assert (Hj13 : (j < length cw_saved)%nat) by (apply nth_error_Some; rewrite Hj; discriminate).
    cbn [length cw_saved] in Hj13.
    apply (cwc_keep_out _ _ sp1 _ _ _ KEEP); [lia | lia | right; lia | exact (Hsav j r Hj)]. }
  split; [apply (cwc_keep_slot _ _ sp1 16 8 _ KEEP); [lia | lia | reflexivity | exact V16]|].
  split; [apply (cwc_keep_slot _ _ sp1 24 8 _ KEEP); [lia | lia | reflexivity | exact V24]|].
  split; [apply (cwc_keep_slot _ _ sp1 32 8 _ KEEP); [lia | lia | reflexivity | exact V32]|].
  split; [apply (cwc_keep_out _ _ sp1 _ _ _ KEEP); [lia | lia | left; lia | exact V56F]|].
  split; (rewrite KEEP; [assumption | unfold CW_SB; lia | apply cwc_notZ; unfold CW_SB; lia]).
- destruct HL as (Hperm & H4096 & Hfa & Hbytes & Hmo).
  split; [exact Hperm|]. split; [exact H4096|]. split; [exact Hfa|]. split; [|exact Hmo].
  assert (Hin : In (line, cw_JN e) (ablocks B lyc Sc)) by (apply (Permutation_in _ (Permutation_sym Hperm)); left; reflexivity).
  destruct (al_blocks _ _ LAWS lyc Sc Wc mem2 mdc2 line (cw_JN e) HAR Hin) as (_ & Hl4096 & Hlceil & _).
  pose proof (cwc_join_len (e_ws e)) as HJL.
  assert (HRS : req_size (cw_JN e) = cw_JN e) by (unfold req_size, cw_JN in *; destruct (Z.eqb_spec (PJn.join_need (e_ws e) + 1) 0); lia).
  rewrite HRS in Hlceil. unfold cw_JN in Hlceil.
  intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
  rewrite KEEP; [exact (Hbytes i ltac:(rewrite length_app; cbn [length]; lia)) | lia | apply cwc_notZ; lia].
- destruct HS as (V152 & V8 & V80 & V88 & V144 & V64 & V72 & V40 & V56 & V176 & V160 & V48 & V112 & V120).
  split; [apply (cwc_keep_slot _ _ sp1 152 8 _ KEEP); [lia | lia | reflexivity | exact V152]|].
  split; [apply (cwc_keep_slot _ _ sp1 8 8 _ KEEP); [lia | lia | reflexivity | exact V8]|].
  split; [apply (cwc_keep_slot _ _ sp1 80 8 _ KEEP); [lia | lia | reflexivity | exact V80]|].
  split; [apply (cwc_keep_slot _ _ sp1 88 8 _ KEEP); [lia | lia | reflexivity | exact V88]|].
  split; [apply (cwc_keep_slot _ _ sp1 144 8 _ KEEP); [lia | lia | reflexivity | exact V144]|].
  split; [apply (cwc_keep_slot _ _ sp1 64 8 _ KEEP); [lia | lia | reflexivity | exact V64]|].
  split; [apply (cwc_keep_slot _ _ sp1 72 8 _ KEEP); [lia | lia | reflexivity | exact V72]|].
  split; [apply (cwc_keep_slot _ _ sp1 40 8 _ KEEP); [lia | lia | reflexivity | exact V40]|].
  split; [apply (cwc_keep_slot _ _ sp1 56 8 _ KEEP); [lia | lia | reflexivity | exact V56]|].
  split; [apply (cwc_keep_slot _ _ sp1 176 8 _ KEEP); [lia | lia | reflexivity | exact V176]|].
  split; [apply (cwc_keep_slot _ _ sp1 160 8 _ KEEP); [lia | lia | reflexivity | exact V160]|].
  split; [apply (cwc_keep_slot _ _ sp1 48 8 _ KEEP); [lia | lia | reflexivity | exact V48]|].
  split; [apply (cwc_keep_slot _ _ sp1 112 8 _ KEEP); [lia | lia | reflexivity | exact V112]|].
  apply (cwc_keep_slot _ _ sp1 120 8 _ KEEP); [lia | lia | reflexivity | exact V120].
Qed.

(* call c's scratch slots from the final symbolic state's regions 1, 3 and 6 (s1 + 96 .. 112, 128 .. 144, 184) *)
Lemma cwc_cscr : forall e E (m : word -> option byte) H sp1 c wd16,
  region_ok SEGS E (mrestrict H m) (YP09.mkRegion (Some 9%nat) 96 112 96 112
    [YP09.mkChunk 96 (CVal 8 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 32 0) (SLit 3)) (SOff 22 0)));
     YP09.mkChunk 104 (CVal 8 (SOff 21 0))]) ->
  region_ok SEGS E (mrestrict H m) (YP09.mkRegion (Some 9%nat) 128 144 128 144
    [YP09.mkChunk 136 (CVal 8 (SAlu ALU_SRL (SOff 39 0) (SLit 3))); YP09.mkChunk 128 (CVal 8 (SOff 32 0))]) ->
  region_ok SEGS E (mrestrict H m) (YP09.mkRegion (Some 9%nat) 184 192 184 192
    [YP09.mkChunk 184 (CVal 8 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 32 4) (SLit 3)) (SOff 22 0)))]) ->
  bv_unsigned (ew E 9) = sp1 -> ew E 21 = Z_to_bv 64 c -> ew E 22 = Z_to_bv 64 2147450880 ->
  ew E 32 = Z_to_bv 64 (A_G_REC + 16 + 56 * c) -> ew E 39 = Z_to_bv 64 wd16 ->
  0 <= c <= 15 -> wd16 = e_Wd e + 16 -> 0 <= wd16 < 2 ^ 47 ->
  cw_cscr e (aview SEGS H m) sp1 c.
Proof.
intros e E m H sp1 c wd16 RG1 RG3 RG6 U9 E21 E22 E32 E39 Hc Hwd Hwr.
assert (HG : A_G_REC = 6173376) by reflexivity.
pose proof (Z.div_pos (A_G_REC + 16 + 56 * c) 8 ltac:(lia) ltac:(lia)) as Hd1.
pose proof (Z.div_le_upper_bound (A_G_REC + 16 + 56 * c + 4) 8 (2 ^ 60) ltac:(lia) ltac:(lia)) as Hd2.
pose proof (Z.div_pos wd16 8 ltac:(lia) ltac:(lia)) as Hw1.
pose proof (Z.div_le_upper_bound wd16 8 (2 ^ 60) ltac:(lia) ltac:(lia)) as Hw2.
pose proof (Z.div_pos (A_G_REC + 16 + 56 * c + 4) 8 ltac:(lia) ltac:(lia)) as Hd3.
pose proof (Z.div_le_upper_bound (A_G_REC + 16 + 56 * c) 8 (2 ^ 60) ltac:(lia) ltac:(lia)) as Hd4.
unfold cw_cscr. cbv zeta. split; [|split; [|split; [|split]]].
- apply cwc_aval_of_val. apply (field_of_region E _ 9%nat sp1 _ 96 112 96 112 104 8 (SOff 21 0) c RG1 U9);
    [right; left; reflexivity | rewrite (cwc_DO E 21 c 0 E21) by lia; f_equal; lia | zside | zside].
- apply cwc_aval_of_val.
  apply (field_of_region E _ 9%nat sp1 _ 96 112 96 112 96 8 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 32 0) (SLit 3)) (SOff 22 0))
    (CW_SB + (A_G_REC + 16 + 56 * c) / 8) RG1 U9);
    [left; reflexivity | rewrite (denot_shx E 32 22 0 _ 2147450880 E32 E22) by lia; rewrite Z.add_0_r; reflexivity
    | unfold CW_SB; zside | zside].
- apply cwc_aval_of_val.
  apply (field_of_region E _ 9%nat sp1 _ 128 144 128 144 128 8 (SOff 32 0) (A_G_REC + 16 + 56 * c) RG3 U9);
    [right; left; reflexivity | rewrite (cwc_DO E 32 _ 0 E32) by lia; f_equal; lia | zside | zside].
- apply cwc_aval_of_val.
  apply (field_of_region E _ 9%nat sp1 _ 184 192 184 192 184 8 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 32 4) (SLit 3)) (SOff 22 0))
    (CW_SB + (A_G_REC + 16 + 56 * c + 4) / 8) RG6 U9);
    [left; reflexivity | rewrite (denot_shx E 32 22 4 _ 2147450880 E32 E22) by lia; reflexivity
    | unfold CW_SB; zside | zside].
- apply cwc_aval_of_val. rewrite <- Hwd.
  apply (field_of_region E _ 9%nat sp1 _ 128 144 128 144 136 8 (SAlu ALU_SRL (SOff 39 0) (SLit 3)) (wd16 / 8) RG3 U9);
    [left; reflexivity | rewrite (cwc_srl3 E 39 0 _ E39) by lia; do 2 f_equal; lia | zside | zside].
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
Ltac cwc_regs_kept E HS HAE regsc :=
  pose proof (regs_kept_of_st_ok_pi E _ _ regsc _
    [(2%bv : bv 5); (3%bv : bv 5); (4%bv : bv 5); (8%bv : bv 5); (9%bv : bv 5); (22%bv : bv 5)]
    HS HAE ltac:(vm_compute; reflexivity)) as RK;
  pose proof (RK (2%bv : bv 5) ltac:(repeat (first [left; reflexivity | right]))) as R2;
  pose proof (RK (3%bv : bv 5) ltac:(repeat (first [left; reflexivity | right]))) as R3;
  pose proof (RK (4%bv : bv 5) ltac:(repeat (first [left; reflexivity | right]))) as R4;
  pose proof (RK (8%bv : bv 5) ltac:(repeat (first [left; reflexivity | right]))) as R8;
  pose proof (RK (9%bv : bv 5) ltac:(repeat (first [left; reflexivity | right]))) as R9;
  pose proof (RK (22%bv : bv 5) ltac:(repeat (first [left; reflexivity | right]))) as R22;
  clear RK; cbn [ms_regs restrict] in R2, R3, R4, R8, R9, R22.
(* a token run that removes an instrumented check adds fresh atoms (>= 1024) to the environment: carry the facts of
   atoms 9, 21, 22, 32, 34, 36, 39 and the agreement with the registers to the run's environment, named E1 *)
Ltac cwc_reenv E E1 HS U9 E21 E22 E32 E34 E36 E39 HAE :=
  lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
    let G := fresh "G" in
    set (E1 := Ex) in *;
    assert (G : forall n, (n < 1024)%nat -> ew E1 n = ew E n)
      by (intros n Hn; unfold E1; rewrite ?ew_ewset_other by lia; reflexivity);
    rewrite <- (G 9%nat ltac:(lia)) in U9; rewrite <- (G 21%nat ltac:(lia)) in E21;
    rewrite <- (G 22%nat ltac:(lia)) in E22; rewrite <- (G 32%nat ltac:(lia)) in E32;
    rewrite <- (G 34%nat ltac:(lia)) in E34; rewrite <- (G 36%nat ltac:(lia)) in E36;
    rewrite <- (G 39%nat ltac:(lia)) in E39;
    lazymatch type of HAE with env_agree 32 ?A _ =>
      let HA1 := fresh "HA" in let HA2 := fresh "HA" in destruct HAE as [HA1 HA2];
      assert (HAE : env_agree 32 A E1)
        by (split; [intros n Hn; rewrite (G n ltac:(lia)); exact (HA1 n Hn) | exact HA2]);
      clear HA1 HA2 G end;
    clearbody E1
  end.

(* ---------------------------------------------------------------------------------------------------------- *)
(* the segment *)
Lemma seg_C : forall c, ST_IH B MT c 0 -> ST_D B MT c -> ST_LH B MT c.
Proof.
intros c HIH HD. unfold ST_IH, cw_at in HIH. unfold ST_D, cw_at in HD.
unfold ST_LH. intros e lyc Sc Wc regsc memc mdc pos sp1 line Hent HI.
destruct HI as (HC & HL & HS0 & H21 & Hcr).
pose proof HC as (HJ & Hsp & Hsp32 & Hspr & _ & _ & _ & H9 & H22 & _).
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _ & _).
pose proof Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & _).
assert (HSTK : CHECK_WORDS_STK = 16848) by (vm_compute; reflexivity).
assert (HG : A_G_REC = 6173376) by reflexivity.
pose proof Hent as Hent0. unfold cw_ent in Hent0. cbv zeta in Hent0.
destruct Hent0 as (_ & _ & _ & _ & _ & _ & HWd1 & HWd2 & _).
assert (Hwd : 0 <= e_Wd e + 16 < 2 ^ 47).
{ clear - HWd1 HWd2 Hslo Hceil H47 C1 HSTK. unfold cw_sp0 in *. lia. }
clear HWd1 HWd2.
destruct (cwc_vals e lyc Sc Wc memc mdc pos EV_JOINED c Hent HJ Hcr)
  as (fn & args & Hnth & Hfn & Hla & Hc15 & VFN & VNA & VTB).
pose proof (cwc_tptr_rng fn Hfn) as Htp.
pose proof HS0 as (_ & _ & _ & _ & V144 & V64 & V72 & V40 & V56 & _ & _ & _ & V112 & V120).
destruct (ZSH_cw lyc Sc Wc memc mdc A_G_REC 960 HAR ltac:(unfold CW_ZSH; left; reflexivity)) as [RA1 _].
destruct (ZSH_cw lyc Sc Wc memc mdc 0xa5920 208 HAR ltac:(unfold CW_ZSH; right; left; reflexivity)) as [RA2 _].
assert (Hsp1 : 2 ^ 46 <= sp1 <= 2 ^ 47) by lia.
destruct (cwc_seed Wc regsc memc sp1 c fn (Z.of_nat (length args)) (e_Wd e + 16) H9 Hsp1 Hsp32 H22 H21
  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) V40 V56 V64 V72 V112 V120 V144 VFN VNA VTB
  ltac:(intros a Ha; apply Hpres; lia) RA1 RA2) as [HS SHOK].
remember (Eimg (Ereg regsc (c_extra c fn (Z.of_nat (length args)) (e_Wd e + 16)))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regsc (c_extra c fn (Z.of_nat (length args)) (e_Wd e + 16))) E)
  by (split; [intros n Hn; rewrite HE; apply Eimg_low; unfold A_TEXT; lia | rewrite HE; reflexivity]).
assert (EX : forall m, (32 <= m < A_TEXT)%nat ->
  ew E m = nth (m - 32) (c_extra c fn (Z.of_nat (length args)) (e_Wd e + 16)) (Z_to_bv 64 0)).
{ intros m Hm. replace m with (32 + (m - 32))%nat at 1 by lia. rewrite HE, Eimg_low by lia. apply ew_Ereg_extra. }
assert (E9 : ew E 9 = Z_to_bv 64 sp1).
{ rewrite HE, Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regsc _ 9 9%bv eq_refl). exact H9. }
assert (E21 : ew E 21 = Z_to_bv 64 c).
{ rewrite HE, Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regsc _ 21 21%bv eq_refl). exact H21. }
assert (E22 : ew E 22 = Z_to_bv 64 2147450880).
{ rewrite HE, Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regsc _ 22 22%bv eq_refl). exact H22. }
pose proof (EX 32%nat ltac:(unfold A_TEXT; lia)) as E32. pose proof (EX 34%nat ltac:(unfold A_TEXT; lia)) as E34.
pose proof (EX 36%nat ltac:(unfold A_TEXT; lia)) as E36. pose proof (EX 39%nat ltac:(unfold A_TEXT; lia)) as E39.
cbn [Nat.sub nth c_extra] in E32, E34, E36, E39.
clear HE EX.
assert (U9 : bv_unsigned (ew E 9) = sp1) by (rewrite E9; apply unsigned_lit_small; lia).
(* 0x87cb4 .. 0x87d38: the trap sites 0x87cb8, 0x87cd0, 0x87cfc, 0x87d08 decided not taken, the checks of cp and
   of nargs removed, the stores of c, SB + cp / 8, cp, SB + (cp + 4) / 8 and (Wd + 16) / 8, to `blez nargs` *)
unfold cw_at.
paj_run_tok RUN HS HJ SHOK cBspan; [cwc_awr sp1 (cw_sp0 e) U9 |].
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdq) _ => set (mdv := mdq) in *; clearbody mdv end.
cwc_keep sp1 U9 K1.
lazymatch goal with HS : st_ok_pi _ _ _ _ (restrict _ ?m) |- _ => rename m into ms1 end.
cwc_reenv E E1 HS U9 E21 E22 E32 E34 E36 E39 HAE.
psrr_branch_tok RUN BR HS SHOK cBspan.
- (* nargs <= 0: on to D *)
  paj_run_to_tok RUNTO HS HJ SHOK cBspan CW_PC_D; [cwc_awr sp1 (cw_sp0 e) U9 |].
  lazymatch goal with |- SRr _ _ (mkCfg _ ?mdq) _ => set (mdv2 := mdq) in *; clearbody mdv2 end.
  cwc_keep sp1 U9 K2.
  lazymatch goal with HS : st_ok_pi _ _ _ _ (restrict _ ?m) |- _ => rename m into ms2 end.
  assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ cwZ sp1 a -> rdW Wc (ms_mem ms2) a = rdW Wc memc a)
    by (intros a Ha Hz; rewrite (K2 a Ha Hz); exact (K1 a Ha Hz)).
  cwc_regs_kept E1 HS HAE regsc.
  destruct (cwc_common e lyc Sc Wc regsc memc mdc (ms_regs ms2) (ms_mem ms2) mdv2 pos sp1 line c HC HL HS0 HJ
    R2 R3 R4 R8 R9 R22 KEEP) as (HC2 & HL2 & HS2).
  pose proof (st_ok_region_nth E1 _ _ 1 (YP09.mkRegion (Some 9%nat) 96 112 96 112
    [YP09.mkChunk 96 (CVal 8 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 32 0) (SLit 3)) (SOff 22 0)));
     YP09.mkChunk 104 (CVal 8 (SOff 21 0))]) HS ltac:(vm_compute; reflexivity)) as RG1.
  pose proof (st_ok_region_nth E1 _ _ 3 (YP09.mkRegion (Some 9%nat) 128 144 128 144
    [YP09.mkChunk 136 (CVal 8 (SAlu ALU_SRL (SOff 39 0) (SLit 3))); YP09.mkChunk 128 (CVal 8 (SOff 32 0))])
    HS ltac:(vm_compute; reflexivity)) as RG3.
  pose proof (st_ok_region_nth E1 _ _ 6 (YP09.mkRegion (Some 9%nat) 184 192 184 192
    [YP09.mkChunk 184 (CVal 8 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 32 4) (SLit 3)) (SOff 22 0)))])
    HS ltac:(vm_compute; reflexivity)) as RG6.
  cbn [ms_mem restrict] in RG1, RG3, RG6.
  pose proof (cwc_cscr e E1 _ _ sp1 c (e_Wd e + 16) RG1 RG3 RG6 U9 E21 E22 E32 E39 ltac:(lia) eq_refl Hwd) as CS.
  pmkst HS. change (BASE + 6736) with (BASE + CW_PC_D).
  apply (HD e lyc Sc Wc (ms_regs ms2) (ms_mem ms2) mdv2 pos sp1 line Hent).
  exact (conj HC2 (conj HL2 (conj HS2 (conj CS Hcr)))).
- (* 0 < nargs: the table slot's check, s4 := cw_tptr fn, ~(cp + 8) at s1 + 168, on to the item loop's head with
     item 0 and cursor 0 *)
  lazymatch goal with Hb : branch_taken _ _ _ = false |- _ => rename Hb into Hgt end.
  rewrite (cwc_ge0 E1 34 _ E34) in Hgt by lia. apply negb_false_iff in Hgt. apply Z.ltb_lt in Hgt.
  paj_run_to_tok RUNTO HS HJ SHOK cBspan CW_PC_IH; [cwc_awr sp1 (cw_sp0 e) U9 |].
  lazymatch goal with |- SRr _ _ (mkCfg _ ?mdq) _ => set (mdv2 := mdq) in *; clearbody mdv2 end.
  cwc_keep sp1 U9 K2.
  lazymatch goal with HS : st_ok_pi _ _ _ _ (restrict _ ?m) |- _ => rename m into ms2 end.
  assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ cwZ sp1 a -> rdW Wc (ms_mem ms2) a = rdW Wc memc a)
    by (intros a Ha Hz; rewrite (K2 a Ha Hz); exact (K1 a Ha Hz)).
  cwc_regs_kept E1 HS HAE regsc.
  destruct (cwc_common e lyc Sc Wc regsc memc mdc (ms_regs ms2) (ms_mem ms2) mdv2 pos sp1 line c HC HL HS0 HJ
    R2 R3 R4 R8 R9 R22 KEEP) as (HC2 & HL2 & HS2).
  pose proof (st_ok_region_nth E1 _ _ 1 (YP09.mkRegion (Some 9%nat) 96 112 96 112
    [YP09.mkChunk 96 (CVal 8 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 32 0) (SLit 3)) (SOff 22 0)));
     YP09.mkChunk 104 (CVal 8 (SOff 21 0))]) HS ltac:(vm_compute; reflexivity)) as RG1.
  pose proof (st_ok_region_nth E1 _ _ 3 (YP09.mkRegion (Some 9%nat) 128 144 128 144
    [YP09.mkChunk 136 (CVal 8 (SAlu ALU_SRL (SOff 39 0) (SLit 3))); YP09.mkChunk 128 (CVal 8 (SOff 32 0))])
    HS ltac:(vm_compute; reflexivity)) as RG3.
  pose proof (st_ok_region_nth E1 _ _ 5 (YP09.mkRegion (Some 9%nat) 168 176 168 176
    [YP09.mkChunk 168 (CVal 8 (SAlu ALU_XOR (SOff 32 8) (SLit (-1))))])
    HS ltac:(vm_compute; reflexivity)) as RG5.
  pose proof (st_ok_region_nth E1 _ _ 6 (YP09.mkRegion (Some 9%nat) 184 192 184 192
    [YP09.mkChunk 184 (CVal 8 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 32 4) (SLit 3)) (SOff 22 0)))])
    HS ltac:(vm_compute; reflexivity)) as RG6.
  cbn [ms_mem restrict] in RG1, RG3, RG5, RG6.
  pose proof (cwc_cscr e E1 _ _ sp1 c (e_Wd e + 16) RG1 RG3 RG6 U9 E21 E22 E32 E39 ltac:(lia) eq_refl Hwd) as CS.
  assert (V168 : aval_mem (rdW Wc (ms_mem ms2)) (sp1 + 168) 8 (cw_not (A_G_REC + 16 + 56 * c + 8))).
  { apply cwc_aval_of_val.
    apply (field_of_region E1 _ 9%nat sp1 _ 168 176 168 176 168 8 (SAlu ALU_XOR (SOff 32 8) (SLit (-1)))
      (cw_not (A_G_REC + 16 + 56 * c + 8)) RG5 U9);
      [left; reflexivity | rewrite (cwc_not_off E1 32 8 _ E32) by lia; reflexivity | unfold cw_not; zside | zside]. }
  cwc_reg HS (18%bv : bv 5) R18. cwc_reg HS (20%bv : bv 5) R20. cwc_reg HS (24%bv : bv 5) R24.
  cwc_reg HS (25%bv : bv 5) R25. cwc_reg HS (26%bv : bv 5) R26. cwc_reg HS (27%bv : bv 5) R27.
  cbn [ms_regs restrict] in R18, R20, R24, R25, R26, R27.
  assert (IR : cw_iregs (ms_regs ms2) c 0).
  { unfold cw_iregs. cbv zeta. split; [|split; [|split; [|split]]].
    - rewrite R26, (cwc_DO E1 32 _ 4 E32) by lia. reflexivity.
    - rewrite R18. reflexivity.
    - rewrite R25. reflexivity.
    - rewrite R24, (cwc_DO E1 32 _ 8 E32) by lia. unfold w64. f_equal. lia.
    - rewrite R27, (cwc_DO E1 32 _ 8 E32) by lia. unfold w64. f_equal. lia. }
  assert (X20 : getr (ms_regs ms2) 20 = w64 (cw_tptr fn + Z.of_nat 0)).
  { rewrite R20, (cwc_DO E1 36 _ 0 E36) by lia. reflexivity. }
  pmkst HS. change (BASE + 6216) with (BASE + CW_PC_IH).
  apply (HIH e lyc Sc Wc (ms_regs ms2) (ms_mem ms2) mdv2 pos sp1 line 0%nat Hent).
  exists fn, args.
  assert (Ha0 : 0 <= 0 < Z.of_nat (length args)) by lia.
  split; [exact (conj HC2 (conj HL2 (conj HS2 (conj CS (conj V168 (conj IR (conj Hcr (conj Hnth Ha0)))))))) |].
  split; [lia|]. split; [exact X20|].
  cbn [skipn Z.to_nat]. exact (cw_parse_tpl fn Hfn).
Qed.
End e.
End f.
End d.
