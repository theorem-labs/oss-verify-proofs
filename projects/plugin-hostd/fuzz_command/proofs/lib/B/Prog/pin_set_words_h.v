(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: block P of sup_pin_accept's ASan walk (plugin-hostd/fuzz_command): the entry,
   the inlined record(13) with both of its arms (the call of rec_calls_free on record.spill when the table already
   holds 16 calls), the two instrumented checks on the slot and the `bnez s1` join, after
   proofs/cgif/cgif_file_fuzzer/lib/A/AChc.v (the seed of a walk segment, the run, the step through a program call)
   over fuzz_command's listing; it finishes the function by lib/A/Prog/sup_pin_accept_s2.v's `spa_from_B0`. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/sup_pin_accept_s4.v, with its module paths and module names changed; 630 of its 712 lines of code are new or changed and 1123 lines of the source are left out. *)
(* Segment H of the walk of pin_set_words on the ASan+UBSan build of plugin-hostd/fuzz_command (image B,
   fuzz_command.asan-ubsan; pin_set_words_s4.v): the instructions 0x8e17c .. 0x8e224 and the slow checks
   0x8e314/0x8e318, 0x8e324/0x8e328, from the entry to the cut point MID (0x8e228), and the three refusals on the
   way (R1 the arity test, R2 strlen(line) > 4096, R3 tok[3] = "-"), each through the epilogue (0x8e2ec) to the
   `ret` (0x8e30c). The B twin of a Theorem Labs lane's A segment (lib/A/Prog/pin_set_words_h.v on
   a working branch): B's code is A's with s1 and s2 swapped (B: s1 = tok[3], s2 = -902) and the two
   UBSan checks on tok before the load of tok[3], 0x8e1cc (tok + 24 wraps) and 0x8e1d8 (tok + 24 misaligned), both
   branching to the `unimp` at 0x8e310; the symbolic run decides both from the atom fact on tok (atom 11: in
   [4096, 0x7fffff800000], 8-aligned).

   The seed: the registers are the atoms 0..31; atom 32 is the shadow base SB, atom 33 the word tok[3] (p3), atoms
   34 and 35 the bytes tok[3][0] and tok[3][1] (c0, c1). The symbolic memory at the entry: the 48-byte frame
   below sp (writable), the GOT word of the shadow base and the shadow-base cell (cgif A/AChc.v cl_regions). After
   the 4096 test the walk adds the word tok[3] (a read-only region over tok, the atom 11) and the byte tok[3][0]
   (a read-only region over p3), and after the '-' test the byte tok[3][1]. The inline checks: load8 of tok[3]
   through the shadow entry [tok, tok + 32) (afobj), load1 of tok[3][0] and tok[3][1] through the shadow entries
   [p3, p3 + 1) and [p3, p3 + 2) of the block `copy` (the second only when tok[3][0] = '-', so the word is not
   empty); YCbn.v's tok_branch takes the two slow blocks. The strlen call goes through a Theorem Labs lane's contract STRLEN (at
   the ambient FP state) and PaArt.v's aj_art_at (errno fact CmdRecCells.v's cmd_cf_env), with the string's
   premises from pin_set_words_s4.v's psw_blk_ready and psw_rom_kept. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import String ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable PaSym PaStep PaSB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI00 YI04 YI08 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Verbs VerbsRun StrFun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require RtString.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob CmdChk.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdObj CmdRo CmdBase CmdRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdPaLib PaDenot PaLibG PaLibF PaLibH PaCall PaCallRun PaArt PaNoChain PaCallPg PaFx.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdRecBase CmdRecImg.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require CmdRecCells.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import pin_set_words_s1 pin_set_words_s2 pin_set_words_s3.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import pins_set_c lv2_refusals_forget_c pin_set_words_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import pin_set_words_s4.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* the symbolic state at the entry *)
Definition psw_h_regions0 : smem := [stack_region 48; got_regionP; bcell_regionP 32].
Definition psw_h_facts0 : facts :=
mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (11%nat, mkAF 4096 0x7fffff800000 3); (32%nat, mkAF SB SB 0);
(33%nat, mkAF 4096 0x7fffff800000 0); (34%nat, mkAF 0 255 0); (35%nat, mkAF 0 255 0)] [] [].
Definition ss_h0 : sstate := mkSS AF_pin_set_words sr_atoms psw_h_regions0 None psw_h_facts0.
Definition psw_h_extra (p3 c0 c1 : Z) : list word := map (Z_to_bv 64) [SB; p3; c0; c1].
Definition HBx : sv := SOff 32 0.
(* a one-chunk read-only region over the atom n: the w bytes at offset o hold the atom v (tok[3] is h_ro1 11 24 8 33,
   its two bytes h_ro1 33 0 1 34 and h_ro1 33 1 1 35) *)
Definition h_ro1 (n : nat) (o : Z) (w : N) (v : nat) : YP09.region :=
YP09.mkRegion (Some n) o (o + Z.of_N w) o o [YP09.mkChunk o (CVal w (SOff v 0))].
(* the registers at the `ret` of a refusal: ra and the callee-saved registers are the entry's, a0 = -902 *)
Definition h_leaf_ok (ss : sstate) : bool :=
forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) CALLEE_SAVED &&
sv_eqb (sr_get (ss_regs ss) (1%bv : bv 5)) (SOff 1 0) &&
match sr_get (ss_regs ss) (10%bv : bv 5) with SLit z => (z mod 2 ^ 64 =? (-902) mod 2 ^ 64) | _ => false end.
(* the six words the prologue saved, as chunks of the frame region over sp (the atom 2) *)
Definition h_saved_chunks : list (Z * nat) := [(-8, 1%nat); (-16, 8%nat); (-24, 9%nat); (-32, 18%nat); (-40, 19%nat); (-48, 20%nat)].
Definition h_has_word (r : YP09.region) (off : Z) (v : sv) : bool :=
existsb (fun c => (YP09.c_off c =? off) && match YP09.c_val c with CVal w v' => N.eqb w 8 && sv_eqb v' v | _ => false end)
(YP09.r_chunks r).
Definition h_saved_ok (rs : smem) : bool :=
existsb (fun r => match YP09.r_base r with
| Some n => Nat.eqb n 2 && forallb (fun p => h_has_word r (fst p) (SOff (snd p) 0)) h_saved_chunks
| None => false end) rs.
(* the registers at MID: sp = the entry sp - 48, s0 = tok, s1 = p3, s3 = ntok, s4 = SB, s2 = -902, and gp, tp,
   s5 .. s11 the entry's *)
Definition h_mid_sv : list (Z * sv) :=
[(2, SOff 2 (-48)); (3, SOff 3 0); (4, SOff 4 0); (8, SOff 11 0); (9, SOff 33 0); (19, SOff 12 0); (20, SOff 32 0);
 (21, SOff 21 0); (22, SOff 22 0); (23, SOff 23 0); (24, SOff 24 0); (25, SOff 25 0); (26, SOff 26 0); (27, SOff 27 0)].
Definition h_mid_ok (ss : sstate) : bool :=
forallb (fun p => sv_eqb (sr_get (ss_regs ss) (Z_to_bv 5 (fst p))) (snd p)) h_mid_sv &&
match sr_get (ss_regs ss) (18%bv : bv 5) with SLit z => (z mod 2 ^ 64 =? (-902) mod 2 ^ 64) | _ => false end &&
h_saved_ok (ss_mem ss).

Ltac h_in := cbn [h_mid_sv In]; repeat (first [left; reflexivity | right]).
Ltac h_inl := cbn [h_saved_chunks In]; repeat (first [left; reflexivity | right]).

(* the arity test `andi a1,a2,-2; li a2,4; bne a1,a2` on a token count of 1 .. 64 *)
Lemma h_cases64 : forall (P : Z -> Prop), (forall k, (k < 64)%nat -> P (Z.of_nat (S k))) -> forall n, 1 <= n <= 64 -> P n.
Proof. intros P H n Hn. replace n with (Z.of_nat (S (Z.to_nat (n - 1)))) by lia. apply H. lia. Qed.
Lemma h_land_num : forall n, 1 <= n <= 64 -> zcanon (zalu_raw 63 64 ALU_AND n (zcanon (-2))) = Z.land n (-2).
Proof. apply h_cases64. intros k Hk. do 64 (destruct k as [|k]; [vm_compute; reflexivity|]). lia. Qed.
(* a byte the reader holds is a one-byte value there *)
Lemma h_aval_byte : forall (rd : reader) a v, rd a = Some v -> 0 <= v < 256 -> aval_mem rd a 1 v.
Proof.
intros rd a v H Hv k Hk. assert (k = 0%nat) by lia. subst k. change (Z.of_nat 0) with 0. rewrite Z.add_0_r, H. f_equal.
unfold YG0f.le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r.
rewrite (Z.mod_small v (2 ^ 8)) by lia. symmetry. apply Z.mod_small. lia.
Qed.
(* the inlined strcmp(tok[3], "-") of the model *)
Lemma h_lu : Verbs.Lit.word_layout_unknown = [Z_to_bv 8 45].
Proof. vm_compute. reflexivity. Qed.
Lemma h_dash_ne : forall w : list byte, bv_unsigned (nth 0 (w ++ [Z_to_bv 8 0]) (Z_to_bv 8 0)) <> 45 ->
Verbs.list_eqb w Verbs.Lit.word_layout_unknown = false.
Proof.
intros w H. rewrite h_lu. destruct w as [|b [|b' w']]; [reflexivity | |].
- cbn [app nth] in H. cbn [Verbs.list_eqb]. change (bv_unsigned (Z_to_bv 8 45)) with 45.
  rewrite (proj2 (Z.eqb_neq _ _) H). reflexivity.
- cbn [Verbs.list_eqb]. rewrite andb_false_r. reflexivity.
Qed.
Lemma h_dash_ne2 : forall w : list byte, bv_unsigned (nth 1 (w ++ [Z_to_bv 8 0]) (Z_to_bv 8 0)) <> 0 ->
Verbs.list_eqb w Verbs.Lit.word_layout_unknown = false.
Proof.
intros w H. rewrite h_lu. destruct w as [|b [|b' w']]; [reflexivity | |].
- exfalso. apply H. reflexivity.
- cbn [Verbs.list_eqb]. rewrite andb_false_r. reflexivity.
Qed.
Lemma h_dash_eq : forall w : list byte, ~ In (Z_to_bv 8 0) w ->
bv_unsigned (nth 0 (w ++ [Z_to_bv 8 0]) (Z_to_bv 8 0)) = 45 -> bv_unsigned (nth 1 (w ++ [Z_to_bv 8 0]) (Z_to_bv 8 0)) = 0 ->
Verbs.list_eqb w Verbs.Lit.word_layout_unknown = true.
Proof.
intros w Hn H0 H1. rewrite h_lu. destruct w as [|b [|b' w']].
- vm_compute in H0. discriminate H0.
- cbn [app nth] in H0. cbn [Verbs.list_eqb]. change (bv_unsigned (Z_to_bv 8 45)) with 45. rewrite H0. reflexivity.
- exfalso. apply Hn. right. left. cbn [app nth] in H1. apply bv_eq. rewrite H1. reflexivity.
Qed.
Lemma h_m_dash : forall (ln : list byte) (tks : list (list byte)) w3, nth_error tks 3 = Some w3 ->
(length tks = 4 \/ length tks = 5)%nat -> Verbs.list_eqb w3 Verbs.Lit.word_layout_unknown = true ->
Verbs.pin_set_words_m ln (tl tks) = Verbs.reject.
Proof.
intros ln tks w3 H3 Hl Hd.
destruct tks as [|v [|u [|f [|l [|vd [|x r]]]]]]; cbn [length] in Hl; try lia; cbn in H3; injection H3 as <-; cbn [tl].
- apply psw_m_dash3. exact Hd.
- apply psw_m_dash4. exact Hd.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ cmd_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

Definition EH (regs : bvmap 5 word) (p3 c0 c1 : Z) : env :=
Eimg (L := cmd_listing) (PI := PI) (Ereg regs (psw_h_extra p3 c0 c1)).
Lemma h_br_arity : forall E n, ew E 12 = Z_to_bv 64 n -> 1 <= n <= 64 ->
branch_taken BC_NE (sv_denot E (SAlu ALU_AND (SOff 12 0) (SLit (-2)))) (sv_denot E (SLit 4)) = negb (Z.land n (-2) =? 4).
Proof.
intros E n H Hn. rewrite branch_ne_U, U_SAlu, !U_SLit, (U_atom E 12 n H) by lia. rewrite (h_land_num n Hn). reflexivity.
Qed.
(* the length test `lui a1,0x1; bltu a1,a0` on strlen's result in the atom 44 *)
Lemma h_br_len : forall E L, ew E 44 = Z_to_bv 64 L -> 0 <= L < 2 ^ 64 ->
branch_taken BC_LTU (sv_denot E (SLit 4096)) (sv_denot E (SOff 44 0)) = (4096 <? L).
Proof. intros E L H HL. rewrite branch_ltu_U, U_SLit, (U_atom E 44 L H HL). reflexivity. Qed.
(* what an environment that agrees with the seed's below the atom 40 holds *)
Lemma h_EH_at : forall regs p3 c0 c1 E, env_agree 40 (EH regs p3 c0 c1) E ->
ew E 32 = Z_to_bv 64 SB /\ ew E 33 = Z_to_bv 64 p3 /\ ew E 34 = Z_to_bv 64 c0 /\ ew E 35 = Z_to_bv 64 c1 /\
(forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r).
Proof.
intros regs p3 c0 c1 E [HA _].
assert (EX : forall j, (j < 4)%nat -> ew E (32 + j) = nth j (psw_h_extra p3 c0 c1) (Z_to_bv 64 0))
by (intros j Hj; rewrite (HA (32 + j)%nat) by lia; unfold EH; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
split; [exact (EX 0%nat ltac:(lia))|]. split; [exact (EX 1%nat ltac:(lia))|].
split; [exact (EX 2%nat ltac:(lia))|]. split; [exact (EX 3%nat ltac:(lia))|].
intros n r Hr. pose proof (bv_unsigned_in_range 5 r) as R5. change (bv_modulus 5) with 32 in R5.
rewrite (HA n) by lia. unfold EH. apply ew_Eimg_Ereg_nat. exact Hr.
Qed.
Lemma h_agree_ewset : forall k X E n v, (k <= n)%nat -> env_agree k X E -> env_agree k X (ewset E n v).
Proof.
intros k X E n v Hk [HA HD]. split; [intros i Hi; rewrite ew_ewset_other by lia; apply HA; exact Hi | rewrite ed_ewset; exact HD].
Qed.
Lemma h_agree32 : forall regs p3 c0 c1 E, env_agree 40 (EH regs p3 c0 c1) E ->
env_agree 32 (Ereg regs (psw_h_extra p3 c0 c1)) E.
Proof.
intros regs p3 c0 c1 E [HA HD]. split; [intros n Hn; rewrite (HA n) by lia; unfold EH; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity|].
rewrite HD. reflexivity.
Qed.

(* a val_mem fact over the restricted memory is the reader's aval_mem *)
Lemma h_aval_of_val_mem : forall H (mem : word -> option byte) a n v,
val_mem SEGS (mrestrict H mem) a n v -> aval_mem (aview SEGS H mem) a n v.
Proof.
intros H mem a n v Hv k Hk. specialize (Hv k Hk). unfold aview. rewrite Hv. cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
unfold YG0f.le_byte, YO0f.le_byte. apply Z.mod_mod. lia.
Qed.
(* a chunk of a region of the symbolic state holds in the memory *)
Lemma h_chunk_of_st : forall E ss H ms r c,
st_ok_pi SEGS VAL E ss (restrict H ms) -> In r (ss_mem ss) -> In c (YP09.r_chunks r) ->
YP09.chunk_ok SEGS E (mrestrict H (ms_mem ms)) (base_val E (YP09.r_base r)) c.
Proof.
intros E ss H ms r c HS Hr Hc.
pose proof (st_ok_mem_ok SEGS E (abs_ss VAL ss) (restrict H ms) HS) as (_ & Hok & _).
rewrite Forall_forall in Hok. specialize (Hok r Hr). destruct Hok as (_ & _ & _ & Hch).
rewrite Forall_forall in Hch. exact (Hch c Hc).
Qed.
Lemma h_has_word_in : forall r off v, h_has_word r off v = true -> In (YP09.mkChunk off (CVal 8 v)) (YP09.r_chunks r).
Proof.
intros r off v H. unfold h_has_word in H. apply existsb_exists in H as ([o cv] & Hin & Hb).
cbn [YP09.c_off YP09.c_val] in Hb. apply andb_prop in Hb as [Ho Hcv]. apply Z.eqb_eq in Ho. subst o.
destruct cv as [w v'| | |]; try discriminate Hcv. apply andb_prop in Hcv as [Hw Hv]. apply N.eqb_eq in Hw. subst w.
apply sv_eqb_eq in Hv. subst v'. exact Hin.
Qed.
(* the six saved words, read off the frame region of the symbolic state *)
Lemma h_saved_of_st : forall (regs : bvmap 5 word) E ss H ms extra,
st_ok_pi SEGS VAL E ss (restrict H ms) -> env_agree 32 (Ereg regs extra) E ->
bv_unsigned (ew E 2) = spZ regs -> h_saved_ok (ss_mem ss) = true ->
psw_saved regs (aview SEGS H (ms_mem ms)).
Proof.
intros regs E ss H ms extra HS [HA _] Usp Hok.
unfold h_saved_ok in Hok. apply existsb_exists in Hok as (r & Hr & Hb).
destruct (YP09.r_base r) as [n|] eqn:Eb; [|discriminate Hb].
apply andb_prop in Hb as [Hn Hall]. apply Nat.eqb_eq in Hn. subst n.
rewrite forallb_forall in Hall.
assert (G : forall off (k : nat) (rr : bv 5), In (off, k) h_saved_chunks -> Z.of_nat k = bv_unsigned rr ->
  aval_mem (aview SEGS H (ms_mem ms)) (spZ regs + off) 8 (bv_unsigned (getr regs rr))).
{ intros off k rr Hin Hk. specialize (Hall (off, k) Hin). cbn [fst snd] in Hall.
  pose proof (h_chunk_of_st E ss H ms r _ HS Hr (h_has_word_in r off (SOff k 0) Hall)) as Hc.
  rewrite Eb in Hc. cbn [base_val] in Hc. rewrite Usp in Hc.
  apply h_aval_of_val_mem.
  apply (val_of_chunk_ok SEGS E (mrestrict H (ms_mem ms)) (spZ regs) off 8 (SOff k 0) (bv_unsigned (getr regs rr)) Hc).
  - rewrite psw_denot_SOff, Z.add_0_r. rewrite (HA k) by (pose proof (bv_unsigned_in_range 5 rr) as R5;
      change (bv_modulus 5) with 32 in R5; lia).
    rewrite (ew_Ereg_nat regs extra k rr Hk). reflexivity.
  - pose proof (bv_unsigned_in_range 64 (getr regs rr)) as R. change (bv_modulus 64) with (2 ^ 64) in R.
    change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
  - lia. }
unfold psw_saved.
replace (spZ regs - 8) with (spZ regs + -8) by lia. replace (spZ regs - 16) with (spZ regs + -16) by lia.
replace (spZ regs - 24) with (spZ regs + -24) by lia. replace (spZ regs - 32) with (spZ regs + -32) by lia.
replace (spZ regs - 40) with (spZ regs + -40) by lia. replace (spZ regs - 48) with (spZ regs + -48) by lia.
split; [apply (G (-8) 1%nat 1%bv); [h_inl | reflexivity]|].
split; [apply (G (-16) 8%nat 8%bv); [h_inl | reflexivity]|].
split; [apply (G (-24) 9%nat 9%bv); [h_inl | reflexivity]|].
split; [apply (G (-32) 18%nat 18%bv); [h_inl | reflexivity]|].
split; [apply (G (-40) 19%nat 19%bv); [h_inl | reflexivity]|].
apply (G (-48) 20%nat 20%bv); [h_inl | reflexivity].
Qed.
(* a run writes only the windows of its regions *)
Lemma h_kept_run : forall E rs (W : world SEGS) mem m0 m1 lo hi,
kept_out (rdW W mem) (rdW W m0) lo hi ->
frame_of E rs (mrestrict (w_H W) m0) (mrestrict (w_H W) m1) ->
(forall b wlo whi a, In (b, wlo, whi) (windows rs) -> base_val E b + wlo <= a < base_val E b + whi -> lo <= a < hi) ->
kept_out (rdW W mem) (rdW W m1) lo hi.
Proof.
intros E rs W mem m0 m1 lo hi HK Hf Hw a Ha Hn.
rewrite (kept_of_frame (segs := SEGS) E rs (w_H W) m0 m1 (fun x => lo <= x < hi) Hf Hw a Ha Hn). exact (HK a Ha Hn).
Qed.
(* after PaDenot.v:76-86's region_kept_aview: a region's bytes are kept, and its writable range is present after *)
Lemma h_region_kept : forall E H (m m2 : word -> option byte) n b lo hi wlo whi cs,
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
(* one more read-only region of one chunk over an atom *)
Lemma h_add_ro1 : forall E ss ms (n : nat) (o : Z) (w : N) (v : nat) b x,
st_ok_pi SEGS VAL E ss ms -> YP09.region_wf (h_ro1 n o w v) = true ->
bv_unsigned (ew E n) = b -> ew E v = Z_to_bv 64 x -> 0 <= x < 2 ^ (8 * Z.of_N w) -> Z.of_N w <= 8 ->
0 <= b + o -> b + o + Z.of_N w <= 2 ^ 64 ->
val_mem SEGS (ms_mem ms) (b + o) (N.to_nat w) x ->
YP09.all_disjoint E (h_ro1 n o w v) (ss_mem ss) ->
st_ok_pi SEGS VAL E (mkSS (ss_pc ss) (ss_regs ss) (h_ro1 n o w v :: ss_mem ss) (ss_resv ss) (ss_facts ss)) ms.
Proof.
intros E ss ms n o w v b x HS Hwf Hb Hv Hx Hw8 H0 H1 Hm Hd.
apply st_ok_pi_add_region; [exact HS | exact Hwf | | exact Hd].
unfold YP09.region_ok, h_ro1. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite Hb. split; [lia|]. split; [lia|]. split; [intros q Hq; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ b o w (SOff v 0) x); [| lia | lia | exact Hm].
cbn [sv_denot]. rewrite Hv, Z.add_0_r. pose proof (Z.pow_le_mono_r 2 (8 * Z.of_N w) 64 ltac:(lia) ltac:(lia)).
rewrite unsigned_lit_small by lia. reflexivity.
Qed.
Lemma h_aj_pres : forall B STK sp0 FP ly S W0 mem md own lyc Sc (W : world SEGS) memc mdc k,
ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k ->
forall a, sp0 - STK <= a < sp0 -> apresent (w_H W) memc a.
Proof.
intros B STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k HJ.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _). exact Hpres.
Qed.
Lemma h_land_U : forall n, 1 <= n <= 64 -> (Z.land n (-2) = 4 <-> (n = 4 \/ n = 5)).
Proof. intros n Hn. apply psw_land_m2. lia. Qed.

Ltac h_win Usp :=
let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let x := fresh "x" in
let Hin := fresh "Hin" in let Hx := fresh "Hx" in
intros b wlo whi x Hin Hx;
lazymatch type of Hin with In _ (windows ?rs) => let w := eval vm_compute in (windows rs) in change (In (b, wlo, whi) w) in Hin end;
cbn [In] in Hin;
repeat (let Hq := fresh "Hq" in destruct Hin as [Hq | Hin];
  [injection Hq as <- <- <-; cbn [base_val] in Hx; rewrite ?Usp in Hx; lia |]);
destruct Hin.
Ltac h_keep Usp :=
lazymatch goal with
| KK : kept_out (aview _ (w_H ?W) ?mem) _ ?lo ?hi, HFr : frame_of ?E ?rs (mrestrict _ ?m0) (mrestrict _ ?m1) |- _ =>
  let KK2 := fresh "KK" in
  pose proof (h_kept_run E rs W mem m0 m1 lo hi KK HFr ltac:(h_win Usp)) as KK2; clear KK HFr; rename KK2 into KK
end;
repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
Ltac h_md := lazymatch goal with |- SRr _ _ (mkCfg _ ?mm) _ =>
let md' := fresh "mdv" in set (md' := mm) in *; clearbody md' end.

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Hypothesis TL : PALib B.
Hypothesis HB : CmdBSyms B.
Hypothesis IMG : cmd_img_facts SEGS B.
Hypothesis MTL : ameter_laws MT.
Hypothesis STRLEN : forall fx0 : YK11.FPState, @RtString.astrlen_realizes fx0 rc SEGS B (SIGMA CS___interceptor_trampoline_strlen).
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

(* the seed: the symbolic state of the walk holds at the entry *)
Lemma h_seed : forall ly S W (regs : bvmap 5 word) mem md (tok n p3 c0 c1 : Z),
AR SEGS B ly S W mem md -> astk_ok PIN_SET_WORDS_STK ly (spZ regs) ->
(forall a, spZ regs - PIN_SET_WORDS_STK <= a < spZ regs -> apresent (w_H W) mem a) ->
getr regs 11 = w64 tok -> afobj SEGS B ly S W mem tok n -> 0 <= n ->
4096 <= p3 <= 0x7fffff800000 -> 0 <= c0 < 256 -> 0 <= c1 < 256 ->
st_ok_pi SEGS VAL (EH regs p3 c0 c1) ss_h0
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_pin_set_words)) mem (seg_rom SEGS))).
Proof.
intros ly S W regs mem md tok n p3 c0 c1 HAR Hstk Hpres H11 HOBJ Hn Rp3 Rc0 Rc1.
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_B_ok as HBASE.
assert (HSTK48 : 48 + 2 * ESTACK <= PIN_SET_WORDS_STK).
{ unfold PIN_SET_WORDS_STK. pose proof (Z.le_max_l (2 * ESTACK) (Z.max PINS_SET_STK LV2_REFUSALS_FORGET_STK)). lia. }
assert (HES : ESTACK = 4096) by reflexivity.
pose proof HOBJ as ((cid & pos & Hfr & Hcid & Hfal & Hflo & Hfhi) & Htok8 & Hra).
destruct (frames_bounds SEGS B LAWS ly S W mem md cid pos HAR Hfr) as (Hf0 & Hfc & Hfapp).
destruct (al_const _ _ LAWS _ _ _ _ _ HAR) as (Kcell & _ & Kgot & _).
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot. rewrite (pal_cell B TL) in Kcell.
pose proof (pa_obj_img 12 ltac:(lia)) as HcellR. pose proof (pal_got_cell B TL) as HgcD. pose proof (pa_obj_img 0 ltac:(lia)) as HgotR.
set (E := EH regs p3 c0 c1).
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr regs r)
by (intros k r Hk; subst E; unfold EH; apply ew_Eimg_Ereg_nat; exact Hk).
assert (ES : forall j, (j < 4)%nat -> ew E (32 + j) = nth j (psw_h_extra p3 c0 c1) (Z_to_bv 64 0))
by (intros j Hj; subst E; unfold EH; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (ES 0%nat ltac:(lia)) as E32. pose proof (ES 1%nat ltac:(lia)) as E33.
pose proof (ES 2%nat ltac:(lia)) as E34. pose proof (ES 3%nat ltac:(lia)) as E35.
cbn [Nat.add nth psw_h_extra map] in E32, E33, E34, E35.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
assert (U11 : bv_unsigned (ew E 11) = tok) by (rewrite (EE 11%nat 11%bv eq_refl), H11; unfold w64; apply unsigned_lit_small; lia).
assert (E241 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (subst E; unfold EH; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E253 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12))) by (subst E; unfold EH; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (VB : forall k v, ew E k = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some k) = v).
{ intros k v Hk Hv. cbn [base_val]. rewrite Hk. apply unsigned_lit_small. exact Hv. }
rewrite restrict_mkst_fx. unfold ss_h0, psw_h_regions0. apply pa_entry_st_ok_full.
- subst E. unfold EH. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold stack_region, got_regionP, bcell_regionP.
  repeat apply Forall_cons; try apply Forall_nil; unfold YP09.region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  + cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
  + rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia).
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
    [cbn [sv_denot]; rewrite E253, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | pose proof (pa_val_range (A_OBJ 12)); lia | lia |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS _ _ _ _ Kgot).
  + rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E253) by (pose proof (pa_val_range (A_OBJ 12)); lia).
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 (SOff 32 0) SB);
    [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; lia | lia |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS _ _ _ _ Kcell).
- apply pairwise_disjoint_of_extents. unfold stack_region, got_regionP, bcell_regionP, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
  rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia).
  rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E253) by (pose proof (pa_val_range (A_OBJ 12)); lia).
  cbn [base_val]. rewrite Usp.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  revert Hslo Hshi H47 Hceil C1 C3 HcellR HgcD HgotR Hstk0 Hbot Htop Htop2 HSTK48 HES.
  clear. intros. repeat split; lia.
- split; [|split; exact I].
  cbn [f_atoms atoms_ok psw_h_facts0]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite Usp, U11, E32, E33, E34, E35, !unsigned_lit_small by (unfold SB; lia).
  change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
  pose proof (fs_frame_bytes_nonneg cid). unfold SB.
  repeat split; lia.
Qed.

(* a refusal: the epilogue (0x8e2ec) has run, the `ret` (0x8e30c) returns s2 = -902 with the entry's registers *)
Lemma h_leaf : forall c p3 c0 c1 E ss ms md,
psw_pre B MT c ->
env_agree 32 (Ereg (x_regs c) (psw_h_extra p3 c0 c1)) E ->
st_ok_pi SEGS VAL E ss (restrict (w_H (x_W c)) ms) -> ss_resv ss = None ->
ss_pc ss = AF_pin_set_words + 0x190 -> h_leaf_ok ss = true ->
ajournal SEGS B PIN_SET_WORDS_STK (psw_sp0 c) (psw_FP c) (x_ly c) (x_S c) (x_W c) (x_mem c) (x_md c)
  [] (x_ly c) (x_S c) (x_W c) (ms_mem ms) md 0 ->
kept_out (rdW (x_W c) (x_mem c)) (rdW (x_W c) (ms_mem ms)) (psw_sp0 c - PIN_SET_WORDS_STK) (psw_sp0 c) ->
Verbs.pin_set_words_m (x_T c) (tl (x_tks c)) = Verbs.reject ->
SRr SEGS (x_W c) (mkCfg ms md) (psw_post B MT c).
Proof.
intros c p3 c0 c1 E ss ms md HP HAE HS Hrv Hpc Hok HJ KEEP Hm.
unfold h_leaf_ok in Hok. apply andb_prop in Hok as [Hok H10b]. apply andb_prop in Hok as [Hcs Hra1b].
pose proof (pp_afn B MT c HP) as (HAR & Hra & _).
eapply (paj_ret_at (L := cmd_listing) (PI := PI) (PL := PL_cmd) _ _ _ _ _ _ HS Hrv); [rewrite Hpc; vm_compute; reflexivity|].
intros mat'.
assert (Hra1 : getr (ms_regs ms) 1 = getr (x_regs c) 1).
{ rewrite (st_ok_pi_restrict_reg (w_H (x_W c)) E ss ms (1%bv : bv 5) HS). apply sv_eqb_eq in Hra1b. rewrite Hra1b.
  rewrite psw_denot_SOff, Z.add_0_r, Z_to_bv_bv_unsigned. destruct HAE as [HA _]. rewrite (HA 1%nat) by lia.
  exact (ew_Ereg_nat (x_regs c) _ 1 1%bv eq_refl). }
assert (Haregs : aregs_preserved (x_regs c) (ms_regs ms))
by exact (aregs_preserved_of_st_ok SEGS (w_H (x_W c)) E (abs_ss VAL ss) ms (x_regs c) _ HS HAE Hcs).
assert (H10 : getr (ms_regs ms) 10 = w64 Verbs.err_invalid_operation).
{ rewrite (st_ok_pi_restrict_reg (w_H (x_W c)) E ss ms (10%bv : bv 5) HS).
  revert H10b. destruct (sr_get (ss_regs ss) (10%bv : bv 5)); intros H10b; try discriminate H10b. cbn [sv_denot].
  apply Z.eqb_eq in H10b. unfold w64, Verbs.err_invalid_operation. apply Z_to_bv64_eq_mod. exact H10b. }
assert (HEV0 : EV_PIN_SET_WORDS (x_R c) (x_T c) (tl (x_tks c)) = 0) by (unfold EV_PIN_SET_WORDS; rewrite Hm; reflexivity).
apply (psw_leaf_post B MT c (x_W c) (ms_regs ms) (ms_mem ms) md (x_ly c) (x_S c) 0 Hra Hra1 Haregs HJ
  ltac:(rewrite HEV0; lia) mat').
exact (psw_Q_reject B MT MTL c (ms_regs ms) (ms_mem ms) _ HP Hm KEEP H10).
Qed.

(* the cut MID: the state at 0x8e228 satisfies INV_MID, and from_MID takes the walk on *)
Lemma h_mid : forall c p3 c0 c1 w3 E ss ms md,
psw_pre B MT c -> from_MID B MT c ->
env_agree 40 (EH (x_regs c) p3 c0 c1) E -> 0 <= p3 < 2 ^ 64 ->
st_ok_pi SEGS VAL E ss (restrict (w_H (x_W c)) ms) -> ss_resv ss = None -> ss_pc ss = PSW_MID ->
h_mid_ok ss = true ->
ajournal SEGS B PIN_SET_WORDS_STK (psw_sp0 c) (psw_FP c) (x_ly c) (x_S c) (x_W c) (x_mem c) (x_md c)
  [] (x_ly c) (x_S c) (x_W c) (ms_mem ms) md 0 ->
kept_out (rdW (x_W c) (x_mem c)) (rdW (x_W c) (ms_mem ms)) (psw_sp0 c - PIN_SET_WORDS_STK) (psw_sp0 c) ->
Z.land (x_ntok c) (-2) = 4 -> nth_error (x_ptrs c) 3 = Some p3 -> nth_error (x_tks c) 3 = Some w3 ->
Z.of_nat (length (x_T c)) <= Verbs.line_max -> Verbs.list_eqb w3 Verbs.Lit.word_layout_unknown = false ->
SRr SEGS (x_W c) (mkCfg ms md) (psw_post B MT c).
Proof.
intros c p3 c0 c1 w3 E ss ms md HP FM HAG Rp3 HS Hrv Hpc Hok HJ KEEP Hland Hp3 Hw3 HlenT Hdash.
unfold h_mid_ok in Hok. apply andb_prop in Hok as [Hok Hsv]. apply andb_prop in Hok as [Hregs H18b].
pose proof (pp_a1 B MT c HP) as H11. pose proof (pp_a2 B MT c HP) as H12. pose proof (pp_tok64 B MT c HP) as Ht64.
pose proof (pp_afn B MT c HP) as (_ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HAE : env_agree 32 (Ereg (x_regs c) (psw_h_extra p3 c0 c1)) E).
{ destruct HAG as [HA HD]. split; [intros n Hn; rewrite (HA n) by lia; unfold EH; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity|].
  rewrite HD. reflexivity. }
assert (EL : forall n (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E n = getr (x_regs c) r).
{ intros n r Hn Hr. destruct HAE as [HA _]. rewrite (HA n) by lia. apply ew_Ereg_nat. exact Hr. }
assert (EX : forall j, (j < 4)%nat -> ew E (32 + j) = nth j (psw_h_extra p3 c0 c1) (Z_to_bv 64 0)).
{ intros j Hj. destruct HAG as [HA _]. rewrite (HA (32 + j)%nat) by lia. unfold EH.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. }
rewrite forallb_forall in Hregs.
assert (G : forall z s, In (z, s) h_mid_sv -> getr (ms_regs ms) (Z_to_bv 5 z) = sv_denot E s).
{ intros z s Hin. rewrite (st_ok_pi_restrict_reg (w_H (x_W c)) E ss ms _ HS).
  specialize (Hregs _ Hin). cbn [fst snd] in Hregs. apply sv_eqb_eq in Hregs. rewrite Hregs. reflexivity. }
assert (LT : forall (b : bv 5) z, bv_unsigned b = z -> Z_to_bv 5 z = b).
{ intros b z Hbz. apply bv_eq. rewrite <- Hbz, Z_to_bv_unsigned. unfold bv_wrap.
  apply Z.mod_small. exact (bv_unsigned_in_range 5 b). }
assert (SV : forall n (w : word), ew E n = w -> sv_denot E (SOff n 0) = w).
{ intros n w Hw. rewrite psw_denot_SOff, Hw, Z.add_0_r. apply Z_to_bv_bv_unsigned. }
assert (Usp : bv_unsigned (ew E 2) = spZ (x_regs c)) by (rewrite (EL 2%nat 2%bv ltac:(lia) eq_refl); reflexivity).
rewrite (st_ok_pi_restrict_mkst (w_H (x_W c)) E ss ms HS Hrv), Hpc.
unfold from_MID in FM. apply FM. unfold INV_MID. exists p3, w3.
split.
{ constructor.
  - exact HJ.
  - exact KEEP.
  - exact (h_saved_of_st (x_regs c) E ss (w_H (x_W c)) ms _ HS HAE Usp Hsv).
  - cbn [ms_regs]. rewrite <- (LT 2%bv 2 eq_refl), (G 2 (SOff 2 (-48)) ltac:(h_in)), psw_denot_SOff, Usp.
    unfold psw_sp0, w64. f_equal; lia.
  - cbn [ms_regs]. rewrite <- (LT 3%bv 3 eq_refl), (G 3 (SOff 3 0) ltac:(h_in)). apply SV.
    exact (EL 3%nat 3%bv ltac:(lia) eq_refl).
  - cbn [ms_regs]. rewrite <- (LT 4%bv 4 eq_refl), (G 4 (SOff 4 0) ltac:(h_in)). apply SV.
    exact (EL 4%nat 4%bv ltac:(lia) eq_refl).
  - cbn [ms_regs]. rewrite <- (LT 8%bv 8 eq_refl), (G 8 (SOff 11 0) ltac:(h_in)). apply SV.
    rewrite (EL 11%nat 11%bv ltac:(lia) eq_refl). exact H11.
  - cbn [ms_regs]. rewrite <- (LT 9%bv 9 eq_refl), (G 9 (SOff 33 0) ltac:(h_in)). apply SV.
    exact (EX 1%nat ltac:(lia)).
  - cbn [ms_regs]. rewrite <- (LT 20%bv 20 eq_refl), (G 20 (SOff 32 0) ltac:(h_in)). apply SV.
    exact (EX 0%nat ltac:(lia)).
  - intros r Hr. cbn [ms_regs].
    assert (Hc : r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
    assert (Hin : In (r, SOff (Z.to_nat r) 0) h_mid_sv) by (destruct Hc as [->|[->|[->|[->|[->|[->| ->]]]]]]; h_in).
    rewrite (G r _ Hin). apply SV. apply (EL (Z.to_nat r) (Z_to_bv 5 r)); [lia|].
    rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. rewrite Z.mod_small by lia. lia. }
split.
{ cbn [ms_regs]. rewrite (st_ok_pi_restrict_reg (w_H (x_W c)) E ss ms (18%bv : bv 5) HS).
  revert H18b. destruct (sr_get (ss_regs ss) (18%bv : bv 5)); intros H18b; try discriminate H18b. cbn [sv_denot].
  apply Z.eqb_eq in H18b. unfold w64, Verbs.err_invalid_operation. apply Z_to_bv64_eq_mod. exact H18b. }
split.
{ cbn [ms_regs]. rewrite <- (LT 19%bv 19 eq_refl), (G 19 (SOff 12 0) ltac:(h_in)). apply SV.
  rewrite (EL 12%nat 12%bv ltac:(lia) eq_refl). exact H12. }
split; [exact Hland|]. split; [exact Hp3|]. split; [exact Hw3|]. split; [exact HlenT | exact Hdash].
Qed.

Theorem psw_H : forall c, psw_pre B MT c -> from_MID B MT c ->
SRr SEGS (x_W c) (cfg_at SEGS (BASE + AF_pin_set_words) (x_regs c) (x_mem c) (x_md c)) (psw_post B MT c).
Proof.
intros c HP FM.
pose proof HP as HP0.
destruct HP0 as [HPRE HROD H10 Hl64 H11 Ht64 H12 Hlb HlO HlT HlN HOBJ HTOKS Hcb HcbO Hntk Hntok Hverb
  HREC Hdecl Hcalls HRO HVO Hfr5 HEV HLIVE HMO].
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HSTK : 48 + 2 * ESTACK <= PIN_SET_WORDS_STK).
{ unfold PIN_SET_WORDS_STK. pose proof (Z.le_max_l (2 * ESTACK) (Z.max PINS_SET_STK LV2_REFUSALS_FORGET_STK)). lia. }
assert (HES : ESTACK = 4096) by reflexivity.
(* the values the entry's environment names: tok[3] (4096 when the array is shorter), its first two bytes *)
remember (nth 3 (x_ptrs c) 4096) as p3 eqn:Ep3.
remember (nth 3 (x_tks c) []) as w3 eqn:Ew3.
remember (bv_unsigned (nth 0 (w3 ++ [Z_to_bv 8 0]) (Z_to_bv 8 0))) as c0 eqn:Ec0.
remember (bv_unsigned (nth 1 (w3 ++ [Z_to_bv 8 0]) (Z_to_bv 8 0))) as c1 eqn:Ec1.
assert (Rc0 : 0 <= c0 < 256) by (rewrite Ec0; pose proof (bv_unsigned_in_range 8 (nth 0 (w3 ++ [Z_to_bv 8 0]) (Z_to_bv 8 0))) as R;
  change (bv_modulus 8) with 256 in R; exact R).
assert (Rc1 : 0 <= c1 < 256) by (rewrite Ec1; pose proof (bv_unsigned_in_range 8 (nth 1 (w3 ++ [Z_to_bv 8 0]) (Z_to_bv 8 0))) as R;
  change (bv_modulus 8) with 256 in R; exact R).
destruct (al_blocks _ _ LAWS _ _ _ _ _ (x_cb c) (x_ncb c) HAR Hcb) as (_ & Hcb4096 & Hcbceil & _).
pose proof (psw3_req_ge (x_ncb c)) as Hcbreq.
assert (Rp3 : 4096 <= p3 <= 0x7fffff800000).
{ rewrite Ep3. destruct (nth_error (x_ptrs c) 3) as [p|] eqn:Ep.
  - rewrite (nth_error_nth _ _ _ Ep). pose proof HTOKS as (_ & Hlen & _ & Hw).
    destruct (nth_error (x_tks c) 3) as [w|] eqn:Ew.
    + destruct (Hw 3%nat p w Ep Ew) as (_ & _ & Hp1 & Hp2). lia.
    + exfalso. apply nth_error_None in Ew. assert (Hl : (3 < length (x_ptrs c))%nat) by (apply nth_error_Some; rewrite Ep; discriminate). lia.
  - rewrite nth_overflow by (apply nth_error_None; exact Ep). lia. }
(* the frame of tok, the line block, the copy block *)
pose proof HOBJ as ((cid & pos & Hfr & Hcid & Hfal & Hflo & Hfhi) & Htok8 & Hra_tok).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ cid pos HAR Hfr) as (Hf0 & Hfc & Hfapp).
pose proof (frm_off_imgP B _ _ _ _ _ cid pos HAR Hfr) as Hfoff.
pose proof (fs_frame_bytes_nonneg cid) as Hfb0.
destruct (al_blocks _ _ LAWS _ _ _ _ _ (x_line c) (x_nl c) HAR Hlb) as (_ & Hl4096 & Hlceil & _).
pose proof (psw3_req_ge (x_nl c)) as Hlreq.
destruct (al_blocks _ _ LAWS _ _ _ _ _ (x_cb c) (x_ncb c) HAR Hcb) as (_ & _ & _ & Hcbapp & _).
pose proof (blk_off_imgP B _ _ _ _ _ (x_cb c) (x_ncb c) HAR Hcb) as Hcboff.
pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ (x_cb c) (x_ncb c) cid pos HAR Hcb Hfr) as Hsepcf.
unfold zdisjoint in Hsepcf. cbn [fst snd] in Hsepcf.
assert (Hob0 : 0x10000 <= VAL 241 /\ VAL 241 + 8 <= 0x606000) by exact (pa_obj_img 0 ltac:(lia)).
assert (Hob12 : 0x10000 <= VAL 253 /\ VAL 253 + 8 <= 0x606000) by exact (pa_obj_img 12 ltac:(lia)).
pose proof (h_seed (x_ly c) (x_S c) (x_W c) (x_regs c) (x_mem c) (x_md c) (x_tok c) (8 * x_ntok c) p3 c0 c1
  HAR Hstk Hpres H11 HOBJ ltac:(lia) Rp3 Rc0 Rc1) as HS.
pose proof (ajournal_init SEGS B PIN_SET_WORDS_STK (psw_FP c) (x_ly c) (x_S c) (x_W c) (x_regs c) (x_mem c) (x_md c) (x_ch c) HPRE) as HJ.
set (sp0 := spZ (x_regs c)) in *.
assert (KK : kept_out (rdW (x_W c) (x_mem c)) (rdW (x_W c) (x_mem c)) (sp0 - PIN_SET_WORDS_STK) sp0)
by (intros a _ _; reflexivity).
remember (EH (x_regs c) p3 c0 c1) as E0 eqn:HE0.
assert (HEI : img_env VAL A_LIM E0) by (rewrite HE0; unfold EH; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg (x_regs c) (psw_h_extra p3 c0 c1)) E0)
by (rewrite HE0; split; [intros n Hn; unfold EH; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity | reflexivity]).
assert (HAG : env_agree 40 (EH (x_regs c) p3 c0 c1) E0) by (rewrite HE0; split; [intros; reflexivity | reflexivity]).
clear HE0.
destruct (h_EH_at _ _ _ _ _ HAG) as (E32 & E33 & E34 & E35 & EE).
assert (Usp0 : bv_unsigned (ew E0 2) = sp0) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
assert (E12 : ew E0 12 = Z_to_bv 64 (x_ntok c)) by (rewrite (EE 12%nat 12%bv eq_refl); exact H12).
assert (SHOK : sh_ok SEGS HBx (@nil shent) E0 (mrestrict (w_H (x_W c)) (x_mem c))) by constructor.
unfold cfg_at. change (w64 (BASE + AF_pin_set_words)) with (Z_to_bv 64 (BASE + AF_pin_set_words)).
(* 0x8e17c .. 0x8e1ac: the prologue, s3 = ntok, s0 = tok, s2 = -902, the arity test *)
paj_run_tok RUN HS HJ SHOK RBspanJ.
{ awr_ok_tac. exact Usp0. }
h_keep Usp0. h_md.
psrr_branch_tok RUN BR HS SHOK RBspanJ.
{ (* R1: ntok is neither 4 nor 5; the epilogue returns s2 = -902 *)
  rewrite (h_br_arity E0 (x_ntok c) E12 Hntok) in Hc. apply Bool.negb_true_iff, Z.eqb_neq in Hc.
  assert (Hm : Verbs.pin_set_words_m (x_T c) (tl (x_tks c)) = Verbs.reject).
  { assert (Hlentl : Z.of_nat (length (tl (x_tks c))) = x_ntok c - 1).
    { pose proof Hverb as Hv'. pose proof Hntk as Hn'. revert Hv' Hn'.
      destruct (x_tks c) as [|v l]; intros Hv' Hn'; [discriminate Hv' | cbn [tl length] in Hn' |- *; lia]. }
    apply psw_m_arity; intros Hq; apply Hc; apply (proj2 (h_land_U _ Hntok)); rewrite Hq in Hlentl; cbn in Hlentl; lia. }
  paj_run_tok RUN HS HJ SHOK RBspanJ.
  { awr_ok_tac. exact Usp0. }
  h_keep Usp0. h_md.
  exact (h_leaf c p3 c0 c1 E0 _ _ _ HP HAE HS eq_refl eq_refl ltac:(vm_compute; reflexivity) HJ KK Hm). }
rewrite (h_br_arity E0 (x_ntok c) E12 Hntok) in Hc. apply Bool.negb_false_iff, Z.eqb_eq in Hc. rename Hc into Hland.
pose proof (proj1 (h_land_U _ Hntok) Hland) as H45.
pose proof HTOKS as (_ & Hlenpt & Hptrs & Hwords).
assert (Hp3 : nth_error (x_ptrs c) 3 = Some p3) by (rewrite Ep3; apply nth_error_nth'; lia).
assert (Hw3 : nth_error (x_tks c) 3 = Some w3) by (rewrite Ew3; apply nth_error_nth'; lia).
destruct (Hwords 3%nat p3 w3 Hp3 Hw3) as (Hw3s & Hw3len & Hcbp3 & Hp3end).
pose proof (Hptrs 3%nat p3 Hp3) as Hp3m. change (x_tok c + 8 * Z.of_nat 3) with (x_tok c + 24) in Hp3m.
(* 0x8e1b0 .. 0x8e1bc: the GOT word, the shadow base in s4, the call of the strlen wrapper *)
paj_run_tok RUN HS HJ SHOK RBspanJ.
{ awr_ok_tac. exact Usp0. }
h_keep Usp0. h_md.
lazymatch goal with HSc : st_ok _ _ _ (restrict _ ?msc) |- SRr _ _ (mkCfg _ ?mdc) _ =>
  prreg HSc (10%bv : bv 5) Ra0; prreg HSc (1%bv : bv 5) Rra; prreg HSc (2%bv : bv 5) Qsp;
  prreg HSc (3%bv : bv 5) Qgp; prreg HSc (4%bv : bv 5) Qtp;
  pmkst HSc;
  assert (Qsp' : spZ (ms_regs msc) = sp0 + -48) by (unfold spZ at 1; rewrite Qsp, Usp0, unsigned_lit_small by lia; lia);
  pose proof (ecall_pre_stk_at SEGS B ESTACK PIN_SET_WORDS_STK sp0 (psw_FP c) (x_ly c) (x_S c) (x_W c) (x_mem c) (x_md c) []
    (x_ly c) (x_S c) (x_W c) (ms_mem msc) mdc 0 (ms_regs msc) (-48) HJ Qsp' eq_refl ltac:(lia) ltac:(lia) ltac:(lia)
    ltac:(rewrite Rra; apply ret_ok_codeptr_v; [lia | reflexivity])
    ltac:(rewrite Qgp, (EE 3%nat 3%bv eq_refl); exact Hgp) ltac:(rewrite Qtp, (EE 4%nat 4%bv eq_refl); exact Htp)) as HPRE1;
  destruct (psw_blk_ready B HB (x_ly c) (x_S c) (x_W c) (x_mem c) (ms_mem msc) mdc ESTACK
    (sp0 - PIN_SET_WORDS_STK) sp0 (ms_regs msc) (x_line c) (x_T c) (x_line c) (x_nl c) (proj1 HJ) KK
    ltac:(lia) ltac:(rewrite Qsp'; lia) ltac:(lia) Hlb ltac:(lia) ltac:(lia) HlT) as (Hl0 & HlS & HlR & HlTV);
  eapply SRr_bind;
  [ eapply (aj_art_at SEGS B LAWS pa_segs_low (CmdRecCells.cmd_cf_env SEGS B LAWS HB IMG) ESTACK (fun _ => False) _ (x_W c) (ms_regs msc) (ms_mem msc)
      PIN_SET_WORDS_STK sp0 (psw_FP c) (x_ly c) (x_S c) (x_W c) (x_mem c) (x_md c) [] (x_ly c) (x_S c) mdc 0 (-48) _
      (fun regs' _ => getr regs' 10 = w64 (astr_len (x_T c))) HJ Qsp' eq_refl ltac:(lia) ltac:(lia) ltac:(lia) Rra
      (fun a F => False_ind _ F));
    apply (STRLEN fx (x_ly c) (x_S c) (x_W c) (ms_regs msc) (ms_mem msc) mdc (x_line c) (x_T c) HPRE1);
    [ rewrite Ra0, (EE 10%nat 10%bv eq_refl); exact H10 | exact Hl0 | exact HlS | exact HlR | exact HlTV
    | exact (psw_rom_kept B (x_W c) (x_mem c) (ms_mem msc) (sp0 - PIN_SET_WORDS_STK) sp0 HROD KK ltac:(lia)) ]
  | ] end.
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md3 & -> & HJ2 & HP2 & Ha02 & HK2).
jafter_call_keep_pi HS 40%nat regs2 (mrestrict (w_H (x_W c)) mem2) HP2 [0; 1; 2]%nat HS2.
lazymatch type of HS2 with ?P -> _ => assert (HQ : P); [| specialize (HS2 HQ); clear HQ] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil;
  (eapply h_region_kept;
   [ first [ exact Usp0 | lazymatch goal with |- bv_unsigned (ew E0 ?n) = _ => exact (HEI n ltac:(cbv; lia)) end ]
   | intros a Ha; apply HK2; [lia | lia | tauto]
   | intros a Ha; first [lia | eapply h_aj_pres; [exact HJ2 | lia]] ]). }
rewrite <- restrict_mkst_fx in HS2.
assert (KK2 : kept_out (rdW (x_W c) (x_mem c)) (rdW (x_W c) mem2) (sp0 - PIN_SET_WORDS_STK) sp0).
{ apply (kept_out_trans _ _ _ _ _ (sp0 + -48 - ESTACK) (sp0 + -48) KK); [intros a Ha Hn; exact (HK2 a Ha Hn (fun x => x)) | lia | lia]. }
clear KK HK2 HS SHOK HJ HPRE1 Hl0 HlS HlR HlTV Ra0 Rra Qsp Qgp Qtp Qsp'.
rename KK2 into KK. rename HS2 into HS. rename HJ2 into HJ.
assert (HIE1 : img_env VAL A_LIM (havoc E0 40 (map (getr regs2) CLOB)))
by (apply img_env_havoc; [exact HEI | apply Nat.leb_le; vm_compute; reflexivity]).
assert (HAG1 : env_agree 40 (EH (x_regs c) p3 c0 c1) (havoc E0 40 (map (getr regs2) CLOB))) by (apply env_agree_havoc_ge; [lia | exact HAG]).
assert (HAE1 : env_agree 32 (Ereg (x_regs c) (psw_h_extra p3 c0 c1)) (havoc E0 40 (map (getr regs2) CLOB)))
by (apply env_agree_havoc_ge; [lia | exact HAE]).
assert (E44 : ew (havoc E0 40 (map (getr regs2) CLOB)) 44 = Z_to_bv 64 (Z.of_nat (length (x_T c)))).
{ change 44%nat with (40 + 4)%nat. rewrite (ew_havoc_new E0 40 _ 4 (Z_to_bv 64 0)) by (rewrite length_map; cbn; lia). exact Ha02. }
assert (Usp1 : bv_unsigned (ew (havoc E0 40 (map (getr regs2) CLOB)) 2) = sp0) by (rewrite ew_havoc_old by lia; exact Usp0).
remember (havoc E0 40 (map (getr regs2) CLOB)) as E1 eqn:HE1. clear HE1.
destruct (h_EH_at _ _ _ _ _ HAG1) as (F32 & F33 & F34 & F35 & FE).
assert (SHOK1 : sh_ok SEGS HBx (@nil shent) E1 (mrestrict (w_H (x_W c)) mem2)) by constructor.
(* 0x8e1c0 .. 0x8e1c4: the length test *)
paj_run_tok RUN HS HJ SHOK1 RBspanJ.
{ awr_ok_tac. exact Usp1. }
h_keep Usp1. h_md.
psrr_branch_tok RUN BR HS SHOK1 RBspanJ.
{ (* R2: strlen(line) > 4096 *)
  rewrite (h_br_len E1 (Z.of_nat (length (x_T c))) E44 ltac:(lia)) in Hc. apply Z.ltb_lt in Hc.
  assert (Hm : Verbs.pin_set_words_m (x_T c) (tl (x_tks c)) = Verbs.reject) by (apply psw_m_long; unfold Verbs.line_max; lia).
  paj_run_tok RUN HS HJ SHOK1 RBspanJ.
  { awr_ok_tac. exact Usp1. }
  h_keep Usp1. h_md.
  exact (h_leaf c p3 c0 c1 E1 _ _ _ HP HAE1 HS eq_refl eq_refl ltac:(vm_compute; reflexivity) HJ KK Hm). }
rewrite (h_br_len E1 (Z.of_nat (length (x_T c))) E44 ltac:(lia)) in Hc. apply Z.ltb_ge in Hc. rename Hc into HlenT.
(* the word tok[3] (over tok, the atom 11) and its first byte (over p3, the atom 33) join the symbolic memory *)
assert (U11 : bv_unsigned (ew E1 11) = x_tok c) by (rewrite (FE 11%nat 11%bv eq_refl), H11; unfold w64; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew E1 33) = p3) by (rewrite F33; apply unsigned_lit_small; lia).
lazymatch goal with HSx : st_ok_pi _ _ _ _ (restrict _ ?msx) |- _ =>
  assert (Vtok : val_mem SEGS (mrestrict (w_H (x_W c)) (ms_mem msx)) (x_tok c + 24) 8 p3);
  [ apply psw_val_mem_of_aval; apply (aval_mem_agree _ _ _ 8 p3 Hp3m); intros k Hk; change (Z.of_nat 8) with 8 in Hk;
    apply (KK (x_tok c + 24 + k)); lia | ];
  assert (Vc0 : val_mem SEGS (mrestrict (w_H (x_W c)) (ms_mem msx)) (p3 + 0) 1 c0);
  [ apply psw_val_mem_of_aval; apply h_aval_byte; [| exact Rc0];
    rewrite (KK (p3 + 0)) by lia; rewrite Ec0; destruct Hw3s as [Hb _]; exact (Hb 0%nat ltac:(rewrite length_app; cbn; lia)) | ]
end.
pose proof (h_add_ro1 E1 _ _ 11 24 8 33 (x_tok c) p3 HS eq_refl U11 F33 ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia) Vtok) as HS3.
lazymatch type of HS3 with ?Hd -> _ => assert (HD : Hd) end.
{ lazymatch goal with |- YP09.all_disjoint ?Ex ?r ?rs => let rs' := eval vm_compute in rs in change (YP09.all_disjoint Ex r rs') end.
  unfold h_ro1. cbn [YP09.all_disjoint]. unfold YP09.extent_disjoint. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite U11, Usp1, (HIE1 241%nat ltac:(cbv; lia)), (HIE1 253%nat ltac:(cbv; lia)).
  unfold off_img in *. repeat split; lia. }
specialize (HS3 HD). clear HD HS. rename HS3 into HS.
pose proof (h_add_ro1 E1 _ _ 33 0 1 34 p3 c0 HS eq_refl U33 F34 ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia) Vc0) as HS3.
lazymatch type of HS3 with ?Hd -> _ => assert (HD : Hd) end.
{ lazymatch goal with |- YP09.all_disjoint ?Ex ?r ?rs => let rs' := eval vm_compute in rs in change (YP09.all_disjoint Ex r rs') end.
  unfold h_ro1. cbn [YP09.all_disjoint]. unfold YP09.extent_disjoint. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite U33, U11, Usp1, (HIE1 241%nat ltac:(cbv; lia)), (HIE1 253%nat ltac:(cbv; lia)).
  unfold off_img in *. repeat split; lia. }
specialize (HS3 HD). clear HD HS. rename HS3 into HS.
lazymatch type of HS with st_ok_pi ?a ?b ?cc ?ssx ?d => let v := eval vm_compute in ssx in change ssx with v in HS end.
(* the shadow entries of the two checks: [tok, tok + 32) in the frame object, [p3, p3 + 1) in the block copy *)
assert (UB1 : U E1 HBx = SHADOW_OFF) by (unfold HBx; rewrite (U_atom E1 32 SB F32) by (unfold SB; lia); reflexivity).
lazymatch goal with HSx : st_ok_pi _ _ _ _ (restrict _ ?msx) |- SRr _ _ (mkCfg _ ?mdx) _ =>
  assert (SHOK3 : sh_ok SEGS HBx [mkSHE 11 0 32; mkSHE 33 0 1] E1 (mrestrict (w_H (x_W c)) (ms_mem msx)));
  [ unfold sh_ok; constructor; [|constructor; [|constructor]];
    [ apply (shent_ok_of_range SEGS (w_H (x_W c)) (ms_mem msx) E1 HBx 11 (x_tok c) (8 * x_ntok c) (x_tok c) 0 32);
      [ apply (range_addressable_kept_win (rdW (x_W c) (x_mem c)) _ (sp0 - PIN_SET_WORDS_STK) sp0 (x_tok c) (8 * x_ntok c));
        [exact KK | lia | lia | lia | exact Hra_tok]
      | exact UB1 | apply U_atom; [rewrite (FE 11%nat 11%bv eq_refl); exact H11 | lia] | lia | lia
      | intros x Hx; cbn [Z.min Z.max] in Hx; unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *; lia ]
    | apply (shent_ok_of_range SEGS (w_H (x_W c)) (ms_mem msx) E1 HBx 33 p3 1 p3 0 1);
      [ apply (range_addressable_of_block SEGS B LAWS (x_ly c) (x_S c) (x_W c) (ms_mem msx) mdx (x_cb c) (x_ncb c) p3 1 (proj1 HJ) Hcb); lia
      | exact UB1 | apply U_atom; [exact F33 | lia] | lia | lia
      | intros x Hx; cbn [Z.min Z.max] in Hx; unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *; lia ] ]
  | ] end.
(* 0x8e1c8 .. 0x8e208 and the slow check 0x8e314: the UBSan checks 0x8e1cc (tok + 24 wraps) and 0x8e1d8 (tok + 24
   misaligned), decided by the run from the fact on tok (atom 11), tok[3] (load8), tok[3][0] (load1), the '-' test *)
paj_run_tok RUN HS HJ SHOK3 RBspanJ.
{ awr_ok_tac. exact Usp1. }
h_keep Usp1. h_md.
lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ => remember Ex as E2 eqn:HE2 end.
assert (HAG2 : env_agree 40 (EH (x_regs c) p3 c0 c1) E2)
by (rewrite HE2; apply h_agree_ewset; [lia|]; apply h_agree_ewset; [lia | exact HAG1]).
assert (HIE2 : img_env VAL A_LIM E2)
by (rewrite HE2; apply img_env_ewset_hi; [apply img_env_ewset_hi; [exact HIE1 | unfold A_LIM; lia] | unfold A_LIM; lia]).
clear HE2.
destruct (h_EH_at _ _ _ _ _ HAG2) as (G32 & G33 & G34 & G35 & GE).
assert (Usp2 : bv_unsigned (ew E2 2) = sp0) by (rewrite (GE 2%nat 2%bv eq_refl); reflexivity).
assert (U34 : U E2 (SOff 34 0) = c0) by (apply U_atom; [exact G34 | lia]).
psrr_branch_tok RUN BR HS SHOK3 RBspanJ.
{ (* tok[3][0] is not '-': the cut MID *)
  rewrite branch_ne_U, U34, U_SLit in Hc. change (zcanon 45) with 45 in Hc. apply Bool.negb_true_iff, Z.eqb_neq in Hc.
  assert (Hdash : Verbs.list_eqb w3 Verbs.Lit.word_layout_unknown = false) by (apply h_dash_ne; rewrite <- Ec0; exact Hc).
  paj_run_to_tok RUNTO HS HJ SHOK3 RBspanJ PSW_MID.
  { awr_ok_tac. exact Usp2. }
  h_keep Usp2. h_md.
  exact (h_mid c p3 c0 c1 w3 E2 _ _ _ HP FM HAG2 ltac:(lia) HS eq_refl eq_refl ltac:(vm_compute; reflexivity) HJ KK Hland Hp3 Hw3
    ltac:(unfold Verbs.line_max; lia) Hdash). }
rewrite branch_ne_U, U34, U_SLit in Hc. change (zcanon 45) with 45 in Hc. apply Bool.negb_false_iff, Z.eqb_eq in Hc.
rename Hc into Hc045.
(* tok[3][0] = '-': the word is not empty, so its second byte is in the block too *)
assert (Hw3ne : (1 <= length w3)%nat).
{ destruct w3 as [|b w']; [|cbn [length]; lia]. exfalso. rewrite Ec0 in Hc045. vm_compute in Hc045. discriminate Hc045. }
assert (U33b : bv_unsigned (ew E2 33) = p3) by (rewrite G33; apply unsigned_lit_small; lia).
assert (U11b : bv_unsigned (ew E2 11) = x_tok c) by (rewrite (GE 11%nat 11%bv eq_refl), H11; unfold w64; apply unsigned_lit_small; lia).
lazymatch goal with HSx : st_ok_pi _ _ _ _ (restrict _ ?msx) |- _ =>
  assert (Vc1 : val_mem SEGS (mrestrict (w_H (x_W c)) (ms_mem msx)) (p3 + 1) 1 c1);
  [ apply psw_val_mem_of_aval; apply h_aval_byte; [| exact Rc1];
    rewrite (KK (p3 + 1)) by lia; rewrite Ec1; destruct Hw3s as [Hb _]; exact (Hb 1%nat ltac:(rewrite length_app; cbn; lia)) | ]
end.
pose proof (h_add_ro1 E2 _ _ 33 1 1 35 p3 c1 HS eq_refl U33b G35 ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia) Vc1) as HS4.
lazymatch type of HS4 with ?Hd -> _ => assert (HD : Hd) end.
{ lazymatch goal with |- YP09.all_disjoint ?Ex ?r ?rs => let rs' := eval vm_compute in rs in change (YP09.all_disjoint Ex r rs') end.
  unfold h_ro1. cbn [YP09.all_disjoint]. unfold YP09.extent_disjoint. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite U33b, U11b, Usp2, (HIE2 241%nat ltac:(cbv; lia)), (HIE2 253%nat ltac:(cbv; lia)).
  unfold off_img in *. repeat split; lia. }
specialize (HS4 HD). clear HD HS. rename HS4 into HS.
lazymatch type of HS with st_ok_pi ?a ?b ?cc ?ssx ?d => let v := eval vm_compute in ssx in change ssx with v in HS end.
assert (UB2 : U E2 HBx = SHADOW_OFF) by (unfold HBx; rewrite (U_atom E2 32 SB G32) by (unfold SB; lia); reflexivity).
lazymatch goal with HSx : st_ok_pi _ _ _ _ (restrict _ ?msx) |- SRr _ _ (mkCfg _ ?mdx) _ =>
  assert (SHOK4 : sh_ok SEGS HBx [mkSHE 33 0 2] E2 (mrestrict (w_H (x_W c)) (ms_mem msx)));
  [ unfold sh_ok; constructor; [|constructor];
    apply (shent_ok_of_range SEGS (w_H (x_W c)) (ms_mem msx) E2 HBx 33 p3 2 p3 0 2);
    [ apply (range_addressable_of_block SEGS B LAWS (x_ly c) (x_S c) (x_W c) (ms_mem msx) mdx (x_cb c) (x_ncb c) p3 2 (proj1 HJ) Hcb); lia
    | exact UB2 | apply U_atom; [exact G33 | lia] | lia | lia
    | intros x Hx; cbn [Z.min Z.max] in Hx; unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *; lia ]
  | ] end.
(* 0x8e20c .. 0x8e224 and the slow check 0x8e324: tok[3][1] (load1), the NUL test *)
paj_run_tok RUN HS HJ SHOK4 RBspanJ.
{ awr_ok_tac. exact Usp2. }
h_keep Usp2. h_md.
lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ => remember Ex as E3 eqn:HE3 end.
assert (HAG3 : env_agree 40 (EH (x_regs c) p3 c0 c1) E3)
by (rewrite HE3; apply h_agree_ewset; [lia|]; apply h_agree_ewset; [lia | exact HAG2]).
clear HE3.
destruct (h_EH_at _ _ _ _ _ HAG3) as (J32 & J33 & J34 & J35 & JE).
assert (Usp3 : bv_unsigned (ew E3 2) = sp0) by (rewrite (JE 2%nat 2%bv eq_refl); reflexivity).
assert (U35 : U E3 (SOff 35 0) = c1) by (apply U_atom; [exact J35 | lia]).
psrr_branch_tok RUN BR HS SHOK4 RBspanJ.
{ (* R3: tok[3] is "-" *)
  rewrite branch_eq_U, U35, U_SLit in Hc. change (zcanon 0) with 0 in Hc. apply Z.eqb_eq in Hc.
  assert (Hm : Verbs.pin_set_words_m (x_T c) (tl (x_tks c)) = Verbs.reject).
  { apply (h_m_dash (x_T c) (x_tks c) w3 Hw3); [lia |].
    apply h_dash_eq; [exact (proj2 Hw3s) | rewrite <- Ec0; exact Hc045 | rewrite <- Ec1; exact Hc]. }
  paj_run_tok RUN HS HJ SHOK4 RBspanJ.
  { awr_ok_tac. exact Usp3. }
  h_keep Usp3. h_md.
  exact (h_leaf c p3 c0 c1 E3 _ _ _ HP (h_agree32 _ _ _ _ _ HAG3) HS eq_refl eq_refl ltac:(vm_compute; reflexivity) HJ KK Hm). }
rewrite branch_eq_U, U35, U_SLit in Hc. change (zcanon 0) with 0 in Hc. apply Z.eqb_neq in Hc.
assert (Hdash : Verbs.list_eqb w3 Verbs.Lit.word_layout_unknown = false) by (apply h_dash_ne2; rewrite <- Ec1; exact Hc).
paj_run_to_tok RUNTO HS HJ SHOK4 RBspanJ PSW_MID.
{ awr_ok_tac. exact Usp3. }
h_keep Usp3. h_md.
exact (h_mid c p3 c0 c1 w3 E3 _ _ _ HP FM HAG3 ltac:(lia) HS eq_refl eq_refl ltac:(vm_compute; reflexivity) HJ KK Hland Hp3 Hw3
  ltac:(unfold Verbs.line_max; lia) Hdash).
Qed.

End e.
End f.
End d.
