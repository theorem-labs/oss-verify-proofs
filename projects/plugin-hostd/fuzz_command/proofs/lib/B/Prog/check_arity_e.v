(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACes.v:275-277
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/A/AFhg.v:439 [Apache-2.0];
   projects/cgif/cgif_file_fuzzer/proofs/lib/YC1f.v:361-366 [Apache-2.0 OR MIT];
   projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:707-710, 1570-1572 [Apache-2.0 OR MIT], for libreac/fuzz_identity's
   asan-ubsan build (lib/B). The [Apache-2.0 OR MIT] text is used under Apache-2.0. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/reac_box_name_seg_mid.v, with its module paths and module names changed; 3261 of its 3422 lines of code are new or changed and 2622 lines of the source are left out. *)
(* check_arity on the ASan+UBSan build of plugin-hostd/fuzz_command (image fuzz_command.asan-ubsan, pin bbe55d24):
   the entry walk (0x87268 to the scan head 0x87448, and every return before it), the scan of g_parsed (22 passes,
   each a call of the strcmp wrapper, run concretely), the dispatch into the matched row's lemma at 0x87478
   (check_arity_s3.v's ca_row_pre), the no-match return, and the assembled proof of the B statement
   tcheck_arity_spec (lib/B/Prog/check_arity_c.v).

   Port of a Theorem Labs lane's A walk (lib/A/Prog/check_arity_e.v, a working branch 5519f6fa753)
   to image B. What changes from A:
   - the frame is 144 bytes (A: 112): the saved registers are at entry sp - 8 - 8 j as on A, the walk's own stack
     window is [sp0 - 144, sp0), and the frame's write window in the rows is [sp, sp + 40) (A: [sp, sp + 8));
   - B keeps read = min(t, 64) in s3 at the scan head and at 0x87478 (A: read - 1; B computes read - 1 only at the
     arity test 0x87950), so ca_lpre carries s3v = read in [1, 64] and the arity bound ca_aok v (s3v - 1);
   - the addresses: GOT words 0xa5f50 / 0xa6bc8 / 0xa6be0, the shadow cell 0xb0c38, g_parsed 0xa5680, the
     literals " \t" 0x210e0, "pin_layout" 0x21180, "pin_expect" 0x211a0, "connect %s %s" 0x211c0,
     "disconnect %s %s" 0x211e0 (all A + 0x40), strcspn's stack-protector cells 0xa6bf8 / 0x604158, the wrapper
     calls' return points BASE + 3672 / 3692 (strcmp), 3712 (strcspn), 3764 (strncmp), 3888 (the scan's strcmp);
   - the three facts of CmdRecFacts that A took as hypotheses (cmd_aread_ok_chk, cmd_heap_tail_vis, the
     stack-protector conjunct of cmd_rec_cells) are a Theorem Labs lane's lemmas here;
   - the UBSan trap sites of this range, all branching to the `unimp` at 0x87a2c.

   UBSan trap sites in this file's range (0x87268 .. 0x87478 and the scan 0x87448 .. 0x87474), each refuted at its
   branch inside the symbolic run of ce_walk: the token executor decides the branch from the seed's atom facts
   (lib/Reusable/YK0c.v decide_branch, sound by lib/Reusable/YK0e.v decide_branch_sound), so no trap edge is taken;
   the facts are ce_facts below, proved in ce_seed (FACT):
   - 0x872a8 (`andi a0,a0,7; bnez`, alignment of w): refuted by atom 10's fact (wp, alignment 2 ^ 3), from the
     statement's premise `wp mod 8 = 0` (lib/B/Prog/check_arity_c.v:126);
   - 0x87358 and 0x8740c (`beqz w->w`): refuted by atom 37's fact (ww >= 4096), from the 0 < t arm's
     `in_blockA (ablocks B ly S) ww 8` (check_arity_c.v:136) through AR's block bounds (al_blocks);
   - 0x87360 and 0x87414 (`andi w->w,7; bnez`): refuted by atom 37's fact (ww, alignment 2 ^ 3), from the 0 < t
     arm's `ww mod 8 = 0` (check_arity_c.v:136).
   No other trap site lies in this range: the scan loop (0x87448 .. 0x87474) has none, and the 19 others and
   0x87954 lie in the rows (check_arity_s4.v, check_arity_r*.v).

   Method (as on A). The entry runs on the token executor of lib/B/Prog/PaShadow.v with the shadow base as the atom
   32: the inline checks of the harness's struct words (wp + 16, wp + 24, in the stack window) and of the first
   word's slot (a live block) are shadow entries; the checks of g_quitting and g_rec read their shadow bytes from two
   seeded regions at the shadow base (check_arity_s2.v's ca_shadow_byte). The four wrapper calls of passed_on
   (strcmp twice, strcspn, strncmp) are taken as the statement's contracts (ASTRCMP, ASTRCSPN, ASTRNCMP at the walk's
   FP state fx: check_arity reaches no printf, so fx never changes) through PaArtStr.v's aj_strcmp_at /
   aj_strcspn_at / aj_strncmp_at; their results decide the plain model's passed_on_m
   (lib/Prog/check_arity_c.v:93-99). At the scan head the walk hands over a machine state (ca_lpre 0); each pass k
   is then one concrete run from a fresh seed (ca_lss k): the shadow check of row k (zero), the row's name pointer,
   the strcmp call (its result is the contract's, `getr a0 = 0 <-> v = name_k`), and the `beqz a0` (0x87460).
   Equal: the state at 0x87478 is ca_row_pre of row k with the arity bounds the plain model's row_find gives for
   v = name_k (check_arity_s0.v's ca_find_k), from arity_ok. Not equal: the state at 0x87448 is ca_lpre (k + 1), or
   after pass 21 the epilogue (0x87960) and `ret` (0x87998). No libc or ASan runtime code is walked.

   Template (read only, not a source): a working branch fd8e07f77cd lib/B/Prog/check_arity.v, an
   old-route B walk in the lib/Lib MState framework against the old check_arity_contract. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04 YI00 YG0s YA0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YG0q YG0t YC5d YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtString.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
CmdSyms CmdList CmdPa CmdPaLib PaCall PaCallRun PaDenot PaLibF PaLibG PaLibH PaSB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
CmdGlob CmdBase CmdRep CmdObj CmdAddr CmdRo CmdZsh CmdChk.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaArt PaArtStr PaNoChain.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require CmdRecFacts.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv CommandModel.
(* the plain model (parsed_rows, row_find, passed_on_m, arity_ok) and cspn_len; the plain contract file shares the
   B statement file's base name, so it is named by its full path *)
Require Import OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.check_arity_c.
Require Import OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.strcspn_c.
Require Import OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.check_reply_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import check_arity_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
check_arity_s0 check_arity_s1 check_arity_s2 check_arity_s3 check_arity_s5 check_arity_s6.
(* the row lemmas: rows 1 2 4-7 9-13 15-21 of check_arity_s4.v, rows 0 3 8 14 of check_arity_r0/r3/r8/r14.v *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
check_arity_s4 check_arity_s7 check_arity_r0 check_arity_r3 check_arity_r8 check_arity_r14.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
(* the imported check_arity_s* files turn lia's division handling off; the shadow arithmetic here needs it (local to
   this file) *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

(** * The plain model at the scan *)

(* what the abort test of the matched row needs: row_find's arity pair bounds the argument count *)
Definition ca_aok (v : list byte) (s : Z) : Prop :=
match row_find v parsed_rows with None => True | Some (mn, mx) => mn <= s <= mx end.

(* a box hnf does not open: the walk's arithmetic tactics reduce every hypothesis to head normal form, and
   ca_aok's head normal form computes the plain model's parsed_rows from the image (40 s per tactic call) *)
Inductive ce_box (P : Prop) : Prop := ce_boxed : P -> ce_box P.
Definition ce_unbox (P : Prop) (h : ce_box P) : P := match h with ce_boxed _ x => x end.
(* a fact kept out of lia's sight: lia case-splits every disjunction and disequation it sees, and zify adds a
   disjunctive spec for every Z.min anywhere in the context *)
Definition ce_hide (P : Prop) : Prop := P.

Lemma ce_arity : forall t v q nc fn0, arity_ok t v q nc fn0 -> 0 < t ->
(q <> 0 \/ nc <> 0) -> (nc <= 0 \/ fn0 <> 5 \/ passed_on_m v = false) -> ca_aok v (Z.min t 64 - 1).
Proof.
intros t v q nc fn0 H Ht Hq Hp. unfold arity_ok in H. unfold ca_aok.
destruct H as [H | [H | [H | H]]]; [lia | lia | | exact H].
destruct H as (H1 & H2 & H3). unfold REC_BROADCAST in H2. exfalso.
destruct Hp as [Hp | [Hp | Hp]]; [lia | lia | congruence].
Qed.

(* the literals passed_on compares with (their bytes without the terminator) *)
Definition ce_set : list byte := removelast RO_lit_210e0.
Definition ce_s14 : list byte := removelast RO_lit_21180.
Definition ce_s15 : list byte := removelast RO_lit_211a0.
Definition ce_s16 : list byte := removelast RO_lit_211c0.
Definition ce_s17 : list byte := removelast RO_lit_211e0.
Definition ce_k16 : list byte := str [99; 111; 110; 110; 101; 99; 116].
Definition ce_k17 : list byte := str [100; 105; 115; 99; 111; 110; 110; 101; 99; 116].

Lemma ce_notin_cons : forall b l, ~ In NUL (b :: l) -> bv_unsigned b <> 0 /\ ~ In NUL l.
Proof.
intros b l H. split.
- intros E. apply H. left. apply bv_eq. rewrite E. reflexivity.
- intros Hi. apply H. right. exact Hi.
Qed.
(* check_words_pin_set.v's cw_walk_prefix with any tail after the compared prefix *)
Lemma ce_walk_prefix : forall k s r, ~ In NUL s -> ~ In NUL k -> k <> [] ->
exists v, strncmp_walk (s ++ [NUL]) (k ++ r) (length k - 1) = Some v /\ (v = 0 <-> firstn (length k) s = k).
Proof.
induction k as [|c k IH]; intros s r Hs Hk Hne; [congruence|].
destruct (ce_notin_cons c k Hk) as [Hc Hk'].
destruct s as [|a s'].
- cbn [app strncmp_walk]. unfold NUL. rewrite Z_to_bv_unsigned. cbn [bv_wrap].
  eexists. split; [reflexivity|]. split; [intros E; exfalso; change (bv_wrap 8 0) with 0 in E; lia | intros E; discriminate].
- destruct (ce_notin_cons a s' Hs) as [Ha Hs'].
  cbn [app length].
  destruct k as [|c2 k2].
  + cbn [strncmp_walk Nat.sub Nat.eqb]. rewrite (proj2 (Z.eqb_neq _ _) Ha), (proj2 (Z.eqb_neq _ _) Hc).
    cbn [orb]. replace (0 - 0)%nat with 0%nat by reflexivity.
    destruct (Z.eqb_spec (bv_unsigned a) (bv_unsigned c)) as [E|NE]; cbn [negb orb].
    * eexists. split; [reflexivity|]. split; [intros _; cbn; f_equal; apply bv_eq; exact E | intros _; lia].
    * eexists. split; [reflexivity|]. split; [intros E; lia | intros E; cbn in E; injection E as E; subst; lia].
  + replace (S (length (c2 :: k2)) - 1)%nat with (S (length (c2 :: k2) - 1)) by (cbn; lia).
    cbn [strncmp_walk]. rewrite (proj2 (Z.eqb_neq _ _) Ha), (proj2 (Z.eqb_neq _ _) Hc).
    cbn [orb Nat.eqb].
    destruct (Z.eqb_spec (bv_unsigned a) (bv_unsigned c)) as [E|NE]; cbn [negb orb].
    * destruct (IH s' r Hs' Hk' ltac:(discriminate)) as (v & Hw & Hv).
      exists v. split; [exact Hw|]. rewrite Hv. cbn [firstn length].
      replace a with c by (apply bv_eq; symmetry; exact E).
      split; [intros H; rewrite H; reflexivity | intros H; injection H as H; exact H].
    * eexists. split; [reflexivity|]. split; [intros E; lia | intros E; cbn in E; injection E as E1 _; subst; lia].
Qed.
Lemma ce_strncmp_prefix : forall s k r, ~ In NUL s -> ~ In NUL k -> k <> [] ->
exists v, strncmp_model (s ++ [NUL]) (k ++ r) (Z.of_nat (length k)) = Some v /\ (v = 0 <-> firstn (length k) s = k).
Proof.
intros s k r Hs Hk Hne. unfold strncmp_model.
destruct k as [|c k']; [congruence|].
replace (Z.of_nat (length (c :: k')) =? 0) with false by (cbn [length]; symmetry; apply Z.eqb_neq; lia).
replace (Z.to_nat (Z.of_nat (length (c :: k')) - 1)) with (length (c :: k') - 1)%nat by lia.
apply ce_walk_prefix; assumption.
Qed.
Lemma ce_prefixb_iff : forall s k, prefixb s k = true <-> firstn (length k) s = k.
Proof.
intros s k. unfold prefixb, bytes_eqb.
destruct (list_eq_dec Z.eq_dec _ _) as [E|NE].
- split; [intros _; apply map_unsigned_inj; exact E | reflexivity].
- split; [discriminate | intros H; exfalso; apply NE; rewrite H; reflexivity].
Qed.
Lemma ce_notin0 : forall l : list byte, forallb (fun b => negb (bv_unsigned b =? 0)) l = true -> ~ In (Z_to_bv 8 0) l.
Proof. intros l H Hin. rewrite forallb_forall in H. specialize (H _ Hin). vm_compute in H. discriminate. Qed.

(* strncmp(v, lit, n) is 0 exactly when v starts with lit's first n bytes, for the two literals of passed_on *)
Lemma ce_strncmp16 : forall v, ~ In NUL v ->
(StrFun.strncmp_model (v ++ [Z_to_bv 8 0]) (ce_s16 ++ [Z_to_bv 8 0]) 7 = Some 0 <-> firstn 7 v = ce_k16).
Proof.
intros v Hv.
assert (E : ce_s16 ++ [Z_to_bv 8 0] = ce_k16 ++ (skipn 7 ce_s16 ++ [Z_to_bv 8 0])).
{ rewrite app_assoc. f_equal; apply map_unsigned_inj; vm_compute; reflexivity. }
rewrite E.
destruct (ce_strncmp_prefix v ce_k16 (skipn 7 ce_s16 ++ [Z_to_bv 8 0]) Hv
  ltac:(apply ce_notin0; vm_compute; reflexivity) ltac:(unfold ce_k16, str; cbn; discriminate)) as (w & Hw & Hwi).
change (Z.of_nat (length ce_k16)) with 7 in Hw. change (length ce_k16) with 7%nat in Hwi. unfold NUL in Hw.
rewrite Hw, <- Hwi. split; [intros H; injection H as H; exact H | intros ->; reflexivity].
Qed.
Lemma ce_strncmp17 : forall v, ~ In NUL v ->
(StrFun.strncmp_model (v ++ [Z_to_bv 8 0]) (ce_s17 ++ [Z_to_bv 8 0]) 10 = Some 0 <-> firstn 10 v = ce_k17).
Proof.
intros v Hv.
assert (E : ce_s17 ++ [Z_to_bv 8 0] = ce_k17 ++ (skipn 10 ce_s17 ++ [Z_to_bv 8 0])).
{ rewrite app_assoc. f_equal; apply map_unsigned_inj; vm_compute; reflexivity. }
rewrite E.
destruct (ce_strncmp_prefix v ce_k17 (skipn 10 ce_s17 ++ [Z_to_bv 8 0]) Hv
  ltac:(apply ce_notin0; vm_compute; reflexivity) ltac:(unfold ce_k17, str; cbn; discriminate)) as (w & Hw & Hwi).
change (Z.of_nat (length ce_k17)) with 10 in Hw. change (length ce_k17) with 10%nat in Hwi. unfold NUL in Hw.
rewrite Hw, <- Hwi. split; [intros H; injection H as H; exact H | intros ->; reflexivity].
Qed.

(* passed_on_m from the four results: not pin_layout, not pin_expect, and neither verb prefix *)
Lemma ce_po_false : forall v,
v <> ce_s14 -> v <> ce_s15 ->
(cspn_len ce_set v = 10%nat -> firstn 10 v <> ce_k17) -> (cspn_len ce_set v = 7%nat -> firstn 7 v <> ce_k16) ->
passed_on_m v = false.
Proof.
intros v H14 H15 H17 H16. unfold passed_on_m, verb_prefix.
assert (E14 : bytes_eqb v (img_str 0x1067c) = false).
{ unfold bytes_eqb. destruct (list_eq_dec Z.eq_dec _ _) as [E|E]; [|reflexivity]. exfalso. apply H14.
  apply map_unsigned_inj. rewrite E. vm_compute. reflexivity. }
assert (E15 : bytes_eqb v (img_str 0x104e2) = false).
{ unfold bytes_eqb. destruct (list_eq_dec Z.eq_dec _ _) as [E|E]; [|reflexivity]. exfalso. apply H15.
  apply map_unsigned_inj. rewrite E. vm_compute. reflexivity. }
assert (Hset : str [32; 9] = ce_set) by (apply map_unsigned_inj; vm_compute; reflexivity).
rewrite E14, E15, Hset. change (str [99; 111; 110; 110; 101; 99; 116]) with ce_k16.
change (str [100; 105; 115; 99; 111; 110; 110; 101; 99; 116]) with ce_k17.
change (length ce_k16) with 7%nat. change (length ce_k17) with 10%nat. cbn [orb].
destruct (Nat.eqb_spec (cspn_len ce_set v) 7) as [C7|C7]; destruct (Nat.eqb_spec (cspn_len ce_set v) 10) as [C10|C10];
cbn [andb orb]; try reflexivity.
- lia.
- destruct (prefixb v ce_k16) eqn:P; [|reflexivity]. exfalso. apply (H16 C7). apply ce_prefixb_iff in P. exact P.
- destruct (prefixb v ce_k17) eqn:P; [|reflexivity]. exfalso. apply (H17 C10). apply ce_prefixb_iff in P. exact P.
Qed.

(** * The entry seed (token executor; atoms 32 = the shadow base SB, 33 = t, 34 = q, 35 = nc, 36 = fn0,
    37 = ww, 38 = p0) *)
Definition CBx : sv := SOff 32 0.
Definition CBspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition CE_LOOP : Z := 0xF18.
Definition ce_words : YP09.region := YP09.mkRegion (Some 10%nat) 16 28 0 0
  [YP09.mkChunk 16 (CVal 8 (SOff 37 0)); YP09.mkChunk 24 (CVal 4 (SOff 33 0))].
Definition ce_gotq : YP09.region := YP09.mkRegion (Some (A_OBJ 6)) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SLit A_G_QUITTING))].
Definition ce_gotr : YP09.region := YP09.mkRegion (Some (A_OBJ 2)) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SLit A_G_REC))].
Definition ce_quit : YP09.region := YP09.mkRegion None A_G_QUITTING (A_G_QUITTING + 4) 0 0
  [YP09.mkChunk A_G_QUITTING (CVal 4 (SOff 34 0))].
Definition ce_rec (np : bool) : YP09.region := YP09.mkRegion None (A_G_REC + 8) (A_G_REC + 20) 0 0
  (YP09.mkChunk (A_G_REC + 8) (CVal 4 (SOff 35 0)) ::
   if np then [YP09.mkChunk (A_G_REC + 16) (CVal 4 (SOff 36 0))] else []).
(* the shadow bytes of g_quitting (one 4-byte object: 04) and of g_rec's two 8-byte granules at +8 and +16 (0) *)
Definition ce_qsh : YP09.region := YP09.mkRegion (Some 32%nat) (A_G_QUITTING / 8) (A_G_QUITTING / 8 + 1) 0 0
  [YP09.mkChunk (A_G_QUITTING / 8) (CVal 1 (SLit 4))].
Definition ce_rsh : YP09.region := YP09.mkRegion (Some 32%nat) ((A_G_REC + 8) / 8) ((A_G_REC + 8) / 8 + 2) 0 0
  [YP09.mkChunk ((A_G_REC + 8) / 8) (CZero 2)].
Definition ce_slot : YP09.region := YP09.mkRegion (Some 37%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 38 0))].
Definition ce_regions (tp np : bool) : smem :=
  [stack_region 144; got_regionP; bcell_regionP 32; ce_words; ce_gotq; ce_gotr; ce_quit; ce_rec np; ce_qsh; ce_rsh] ++
  (if tp then [ce_slot] else []).
Definition ce_facts (tp np : bool) : facts := mkFacts
  ([(2%nat, mkAF (2^46) (2^47) 4); (10%nat, mkAF (2^46) (2^47 - 28) 3); (32%nat, mkAF SB SB 0);
    (33%nat, if tp then mkAF 1 4096 0 else mkAF 0 0 0); (34%nat, mkAF 0 (2^32 - 1) 0);
    (35%nat, if np then mkAF 1 16 0 else mkAF 0 0 0)] ++
   (if np then [(36%nat, mkAF 0 25 0)] else []) ++
   (if tp then [(37%nat, mkAF 4096 (2^47 - 8) 3); (38%nat, mkAF 0 (2^64 - 1) 0)] else [])) [] [].
Definition ce_SH (tp : bool) : list shent := mkSHE 10 16 28 :: (if tp then [mkSHE 37 0 8] else []).
Definition ss_ce (tp np : bool) : sstate := mkSS AF_check_arity sr_atoms (ce_regions tp np) None (ce_facts tp np).
Definition ce_extra (t q nc fn0 ww p0 : Z) : list word := map (Z_to_bv 64) [SB; t; q; nc; fn0; ww; p0].

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

Definition EC (regs : bvmap 5 word) (t q nc fn0 ww p0 : Z) : env := Eimg (Ereg regs (ce_extra t q nc fn0 ww p0)).

(** ** Memory facts the walk carries (after check_words_pin_set.v:160-285, at this call's stack) *)
(* the memory outside this call's stack window is the entry memory *)
Definition ce_kept (W : world SEGS) (mem m : word -> option byte) (sp0 : Z) : Prop :=
forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - CHECK_ARITY_STK <= a < sp0) -> aview SEGS (w_H W) m a = aview SEGS (w_H W) mem a.
(* a string a wrapper may read, at the entry memory; the last conjunct is the 8 bytes of band room past the string
   that the strcspn and strncmp contracts ask (lib/B/Rt/RtString.v:129, :132, :166, :169) *)
Definition ce_ready (W : world SEGS) (mem : word -> option byte) (p : Z) (s : list byte) : Prop :=
0 < p /\ p + Z.of_nat (length s) + 1 <= alloc_ceiling /\ Z.of_nat (length s) + 1 < 2 ^ 32 /\
astr_atR (aview SEGS (w_H W) mem) p s /\
range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF p (Z.of_nat (length s) + 1) /\
shadow_hull_vis (aview SEGS (w_H W) mem) p (Z.of_nat (length s) + 1) /\
amem_range p (Z.of_nat (length s) + 1) /\
atail_vis SEGS W mem (p + Z.of_nat (length s)) /\
amem_range p (Z.of_nat (length s) + 8).
(* every write window of a seed is a stack window [sp + lo, sp + hi) *)
Definition ce_wr (lo hi : Z) (rs : smem) : bool :=
forallb (fun r => (YP09.r_whi r <=? YP09.r_wlo r) ||
(match YP09.r_base r with Some n => Nat.eqb n 2 | None => false end && (lo <=? YP09.r_wlo r) && (YP09.r_whi r <=? hi))) rs.

Lemma ce_not_wrange : forall E rs lo hi a, ce_wr lo hi rs = true ->
~ (bv_unsigned (ew E 2) + lo <= a < bv_unsigned (ew E 2) + hi) -> ~ in_wrange E rs a.
Proof.
intros E rs lo hi a Hw Ha (r & Hin & Hr). unfold ce_wr in Hw. rewrite forallb_forall in Hw. specialize (Hw r Hin).
apply orb_prop in Hw as [Hw | Hw]; [apply Z.leb_le in Hw; lia|].
apply andb_prop in Hw as [Hw Hhi]. apply andb_prop in Hw as [Hb Hlo]. apply Z.leb_le in Hlo. apply Z.leb_le in Hhi.
destruct (YP09.r_base r) as [n|] eqn:Eb; [|discriminate]. apply Nat.eqb_eq in Hb. subst n.
cbn [base_val] in Hr. lia.
Qed.
Lemma ce_aview_frame : forall E rs H (m m' : word -> option byte) a,
frame_of E rs (mrestrict H m) (mrestrict H m') -> 0 <= a < 2 ^ 64 -> ~ in_wrange E rs a ->
aview SEGS H m' a = aview SEGS H m a.
Proof.
intros E rs H m m' a Hf Ha Hw. unfold aview, mbyte.
rewrite (Hf (Z_to_bv 64 a)); [reflexivity|]. rewrite unsigned_lit_small by lia. exact Hw.
Qed.
Lemma ce_kept_refl : forall W mem sp0, ce_kept W mem mem sp0.
Proof. intros W mem sp0 a _ _. reflexivity. Qed.
Lemma ce_kept_run : forall W mem m0 m1 E rs sp0 lo hi, ce_kept W mem m0 sp0 ->
frame_of E rs (mrestrict (w_H W) m0) (mrestrict (w_H W) m1) -> ce_wr lo hi rs = true ->
sp0 - CHECK_ARITY_STK <= bv_unsigned (ew E 2) + lo -> bv_unsigned (ew E 2) + hi <= sp0 ->
ce_kept W mem m1 sp0.
Proof.
intros W mem m0 m1 E rs sp0 lo hi HK Hf Hw H1 H2 a Ha Hn.
rewrite (ce_aview_frame E rs (w_H W) m0 m1 a Hf Ha); [exact (HK a Ha Hn)|].
apply (ce_not_wrange E rs lo hi a Hw). lia.
Qed.
Lemma ce_kept_call : forall W mem m0 m1 sp0 lo hi, ce_kept W mem m0 sp0 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> ~ False -> aview SEGS (w_H W) m1 a = aview SEGS (w_H W) m0 a) ->
sp0 - CHECK_ARITY_STK <= lo -> hi <= sp0 -> ce_kept W mem m1 sp0.
Proof. intros W mem m0 m1 sp0 lo hi HK Hf Hlo Hhi a Ha Hn. rewrite (Hf a Ha); [exact (HK a Ha Hn) | lia | tauto]. Qed.
(* the saved registers stay in the frame: no write of the walk reaches [sp + 40, sp + 144) (B writes the frame
   only in [sp, sp + 40), A only in [sp, sp + 8)) *)
Lemma ce_frame_keep : forall (W : world SEGS) m m' sp regs0, ca_frame_at W m sp regs0 ->
(forall a, sp + 40 <= a < sp + 144 -> aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a) -> ca_frame_at W m' sp regs0.
Proof.
intros W m m' sp regs0 HF HK j Hj k Hk.
assert (Ha : sp + 40 <= sp + 136 - 8 * Z.of_nat j + Z.of_nat k < sp + 144) by lia.
rewrite (mbyte_of_aview SEGS (w_H W) (w_H W) m m' _ (HK _ Ha)).
exact (HF j Hj k Hk).
Qed.
Lemma ce_hull_sub : forall (rd : reader) x n x' n', shadow_hull_vis rd x n -> x <= x' -> x' + n' <= x + n -> 0 < n' ->
shadow_hull_vis rd x' n'.
Proof.
intros rd x n x' n' H H1 H2 H3 s Hs. apply H.
pose proof (shadow_mono x x' H1) as M1. pose proof (shadow_mono (x' + n' - 1) (x + n - 1) ltac:(lia)) as M2.
assert (R8 : forall u v, u <= v -> u / 8 * 8 <= v / 8 * 8) by (intros u v Huv; apply Z.mul_le_mono_nonneg_r; [lia|]; apply Z.div_le_mono; lia).
pose proof (R8 _ _ M1). pose proof (R8 _ _ M2). lia.
Qed.
Lemma ce_aread_prefix : forall stk W regs mem x n n', aread_ok SEGS stk W regs mem x n -> 0 <= n' <= n ->
aread_ok SEGS stk W regs mem x n'.
Proof.
intros stk W regs mem x n n' (H0 & H1 & H2 & H3 & H4 & H5 & H6) Hn.
split; [lia|]. split; [lia|]. split; [lia|]. split; [intros a Ha; apply H3; lia|].
split; [unfold amem_range in *; lia|]. split; [eapply range_addressable_sub; [exact H5 | lia | lia]|].
intros Hp. apply (ce_hull_sub _ x n x n'); [apply H6; lia | lia | lia | lia].
Qed.
Lemma ce_ready_call : forall W mem memT p s sp0 regsT,
ce_ready W mem p s -> alloc_ceiling <= sp0 - CHECK_ARITY_STK -> ce_kept W mem memT sp0 ->
(forall a, sp0 - CHECK_ARITY_STK <= a < sp0 -> apresent (w_H W) memT a) ->
sp0 - CHECK_ARITY_STK <= spZ regsT - 2 * ESTACK ->
0 < p /\ astr_at SEGS W memT p s /\ aread_ok SEGS (2 * ESTACK) W regsT memT p (astr_len s + 1) /\
atail_vis SEGS W memT (p + astr_len s) /\ amem_range p (astr_len s + 8).
Proof.
intros W mem memT p s sp0 regsT (Hp & Hpn & Hn32 & [Hb Hnul] & Hra & Hhv & Ham & Htl & Ham8) Hce HK Hpr Hsp.
unfold ce_kept in HK.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). assert (ESTACK = 4096) as Hes by reflexivity.
unfold astr_len.
assert (KEEP : forall a, 0 <= a < alloc_ceiling -> aview SEGS (w_H W) memT a = aview SEGS (w_H W) mem a)
by (intros a Ha; apply HK; lia).
assert (HB : abytes_at SEGS W memT p (s ++ [Z_to_bv 8 0])).
{ intros i Hi. rewrite length_app in Hi. cbn [length] in Hi. rewrite KEEP by lia. apply Hb. rewrite length_app. cbn [length]. lia. }
split; [exact Hp|]. split; [split; [exact HB | exact Hnul]|]. split.
- unfold aread_ok. split; [lia|]. split; [lia|]. split; [lia|]. split.
  { intros a Ha. split.
  - replace a with (p + Z.of_nat (Z.to_nat (a - p))) by lia.
    rewrite (HB (Z.to_nat (a - p))) by (rewrite length_app; cbn [length]; lia). discriminate.
  - unfold ascratch_stk. lia. }
  split; [exact Ham|]. split.
  { intros x Hx. destruct (Hra x Hx) as (sh & Hsh & Hok). exists sh. split; [|exact Hok].
    rewrite KEEP; [exact Hsh|]. unfold shadow_of_addr, SHADOW_OFF in *. lia. }
  { intros _ s0 Hs0. rewrite KEEP; [exact (Hhv s0 Hs0)|]. unfold shadow_addr, SHADOW_OFF in Hs0. lia. }
- split; [|exact Ham8]. intros a Ha. destruct (Z_lt_le_dec a (sp0 - CHECK_ARITY_STK)) as [Hlt|Hge].
  + rewrite (HK a ltac:(lia) ltac:(lia)). exact (Htl a Ha).
  + pose proof (Z.mod_pos_bound (p + Z.of_nat (length s)) 8 ltac:(lia)) as M8.
    apply (aview_some_of_apresent SEGS). apply Hpr. unfold CHECK_ARITY_STK in *. lia.
Qed.
Lemma ce_aj_pres : forall B STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k,
ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k ->
forall a, sp0 - STK <= a < sp0 -> apresent (w_H W) memc a.
Proof. intros B STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k HJ. pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _). exact Hpres. Qed.
(* an 8-byte word of the read-only image *)
Lemma ce_word_of_bytes : forall (W : world SEGS) mem a L, abytes_atR (aview SEGS (w_H W) mem) a L -> length L = 8%nat ->
YI04.val_mem SEGS (mrestrict (w_H W) mem) a 8 (bytes_le_to_Z L).
Proof.
intros W mem a L H HL.
destruct L as [|b0 [|b1 [|b2 [|b3 [|b4 [|b5 [|b6 [|b7 [|b8 L]]]]]]]]]; cbn [length] in HL; try discriminate.
apply ca_word_val. intros i Hi. apply (ca_bytes_mbyte W mem a _ H). cbn [length]. lia.
Qed.

Section e.
Variable B : asyms.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
Hypothesis HB : CmdBSyms B.
Hypothesis TL : PALib B.
(* the image facts CmdRecFacts' cmd_rec_cells reads (closed at the pinned image by CmdRecImg.cmd_img_facts_tfib) *)
Hypothesis IMG : CmdRecBase.cmd_img_facts SEGS B.
(* the statement's runtime entries, in its fx-generic form; the walk applies them at its own FP state fx *)
Hypothesis ASTRCMP : forall fx0 : YK11.FPState, @astrcmp_realizes fx0 rc SEGS B (SIGMA CS___interceptor_trampoline_strcmp).
Hypothesis ASTRCSPN : forall fx0 : YK11.FPState, @astrcspn_realizes fx0 rc SEGS B (SIGMA CS___interceptor_trampoline_strcspn) 0xa6bf8 0x604158.
Hypothesis ASTRNCMP : forall fx0 : YK11.FPState, @astrncmp_realizes fx0 rc SEGS B (SIGMA CS___interceptor_trampoline_strncmp).
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL.
(* a Theorem Labs lane's CmdRecFacts (A took these three as hypotheses) *)
Let cmd_aread_ok_chk := CmdRecBase.cmd_aread_ok_chk SEGS B LAWS HB.
Let cmd_heap_tail_vis := CmdRecImg.cmd_heap_tail_vis SEGS B LAWS HB.
Let cmd_rec_guard : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md -> aguard_ok SEGS W mem 0xa6bf8 0x604158 :=
fun ly S W mem md HAR => proj1 (proj2 (CmdRecCells.cmd_rec_cells SEGS B LAWS HB IMG ly S W mem md HAR)).
Lemma ce_ready_of_blk : forall ly S W mem md p s,
AR SEGS B ly S W mem md -> in_blockA (ablocks B ly S) p (Z.of_nat (length s) + 1) -> astr_atR (rdW W mem) p s ->
ce_ready W mem p s.
Proof.
intros ly S W mem md p s HAR (b & k & Hin & Hb & He) Hstr.
pose proof asan_consts as (C1 & _).
destruct (al_blocks _ _ LAWS ly S W mem md b k HAR Hin) as (Hb16 & Hb4096 & Hbceil & Happ & Hbpres & _ & Hk).
pose proof (req_size_pos0 k ltac:(lia)) as [Hr0 Hrk].
unfold ce_ready. split; [lia|]. split; [lia|]. split; [unfold MALLOC_MAX in Hk; lia|]. split; [exact Hstr|]. split.
{ apply (range_addressable_of_block SEGS B LAWS ly S W mem md b k); [exact HAR | exact Hin | lia | lia]. }
split. { apply (shadow_hull_vis_of_block SEGS B LAWS ly S W mem md b k); [exact HAR | exact Hin | lia | lia | lia]. }
split. { apply (amem_range_of_block SEGS B LAWS ly S W mem md b k); [exact HAR | exact Hin | lia | lia]. }
split; [apply (cmd_heap_tail_vis ly S W mem md b k); [exact HAR | exact Hin | lia]|].
(* the band room past the string: PaLibH.amem8_of_blockA from the block the string lies in *)
apply (amem8_of_blockA SEGS B LAWS ly S W mem md p (Z.of_nat (length s)) HAR); [exists b, k; split; [exact Hin | lia] | lia].
Qed.
(* a read-only literal L of CmdRo.v (its bytes, then its terminator) as a string a wrapper reads *)
Lemma ce_ready_lit : forall ly S W mem md a L, AR SEGS B ly S W mem md -> cmd_ro_ok (rdW W mem) ->
abytes_atR (rdW W mem) a L ->
map bv_unsigned L = map bv_unsigned (removelast L ++ [Z_to_bv 8 0]) ->
forallb (fun b => negb (bv_unsigned b =? 0)) (removelast L) = true ->
existsb (Z.eqb (a + Z.of_nat (length (removelast L)))) cmd_ro_ends = true ->
cmd_addr_b a (Z.of_nat (length (removelast L)) + 1) = true -> cmd_hull_b a (Z.of_nat (length (removelast L)) + 1) = true ->
0 < a -> a + Z.of_nat (length (removelast L)) + 8 <= 0x7fff7fff ->
ce_ready W mem a (removelast L).
Proof.
intros ly S W mem md a L HAR [_ HT] HL EL HN HE HA HH Ha Hhi.
apply map_unsigned_inj in EL.
destruct (cmd_aread_ok_chk ly S W mem md a _ HAR HA HH) as [RA HV].
pose proof asan_consts as (C1 & _).
unfold ce_ready. split; [lia|]. split; [lia|]. split; [lia|].
split; [split; [rewrite <- EL; exact HL | apply ce_notin0; exact HN]|].
split; [exact RA|]. split; [exact HV|]. split; [unfold amem_range, kLowMemEnd; left; lia|].
split.
{ intros x Hx. apply (HT (a + Z.of_nat (length (removelast L)))); [|exact Hx].
  apply existsb_exists in HE as (y & Hy & Hey). apply Z.eqb_eq in Hey. rewrite Hey. exact Hy. }
(* the band room past the literal: PaLibH.amem8_of_low (.rodata, in the low band) *)
apply amem8_of_low; [lia | unfold kLowMemEnd; lia].
Qed.
Lemma ce_rom_view : forall W mem memT sp0, arodata_okP SEGS RLO RHI B (rdW W mem) ->
alloc_ceiling <= sp0 - CHECK_ARITY_STK -> ce_kept W mem memT sp0 -> rt_rom_view SEGS B W memT.
Proof.
intros W mem memT sp0 HRO Hce HK a Ha Ho He. unfold ce_kept in HK.
assert (Himg : in_img SEGS a) by (destruct Ha as (sg & Hsg & _ & Hr); exists sg; split; [exact Hsg | exact Hr]).
pose proof (pa_img_range _ Himg) as Hr. pose proof asan_consts as (C1 & _).
rewrite HK by lia. apply HRO; [left; exact Ha | exact Ho | exact He].
Qed.

(** ** The wrapper calls, with the contracts' premises discharged from the strings' readiness *)
(* the three calls at this function's sites: the caller's frame is 144 bytes, the return address BASE + retk *)
Lemma ce_strcmp_at : forall ly S W sp0 mem md (ms : machine_state) md' x sx y sy retk,
ajournal SEGS B CHECK_ARITY_STK sp0 [] ly S W mem md [] ly S W (ms_mem ms) md' 0 ->
arodata_okP SEGS RLO RHI B (rdW W mem) -> alloc_ceiling <= sp0 - CHECK_ARITY_STK -> ce_kept W mem (ms_mem ms) sp0 ->
getr (ms_regs ms) 10 = w64 x -> getr (ms_regs ms) 11 = w64 y ->
spZ (ms_regs ms) = sp0 - 144 -> getr (ms_regs ms) 3 = w64 (as_gp B) -> getr (ms_regs ms) 4 = w64 (as_tp B) ->
getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + retk) -> 0 <= retk < 2 ^ 40 -> retk mod 2 = 0 ->
ce_ready W mem x sx -> ce_ready W mem y sy ->
SRr SEGS W (mkCfg (mkst (ms_regs ms) (Z_to_bv 64 (SIGMA CS___interceptor_trampoline_strcmp)) (ms_mem ms) (seg_rom SEGS)) md')
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
c2 = mkCfg (mkst regs2 (Z_to_bv 64 (BASE + retk)) mem2 (seg_rom SEGS)) md2 /\
ajournal SEGS B CHECK_ARITY_STK sp0 [] ly S W mem md [] ly S W mem2 md2 0 /\
aregs_preserved (ms_regs ms) regs2 /\ (getr regs2 10 = w64 0 <-> sx = sy) /\
ce_kept W mem mem2 sp0 /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + -144 - 2 * ESTACK <= a < sp0 + -144) -> ~ False ->
aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) (ms_mem ms) a)).
Proof.
intros ly S W sp0 mem md ms md' x sx y sy retk HJ HRO HCE HK Ha0 Ha1 Hsp Hgp Htp Hra Hrk Hrk2 RX RY.
pose proof (ce_aj_pres _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as Hpr.
assert (Hes : ESTACK = 4096) by reflexivity.
destruct (ce_ready_call W mem (ms_mem ms) x sx sp0 (ms_regs ms) RX HCE HK Hpr ltac:(rewrite Hsp; unfold CHECK_ARITY_STK; lia))
as (Hx0 & Hsx & Hrx & Htx & Hmx).
destruct (ce_ready_call W mem (ms_mem ms) y sy sp0 (ms_regs ms) RY HCE HK Hpr ltac:(rewrite Hsp; unfold CHECK_ARITY_STK; lia))
as (Hy0 & Hsy & Hry & Hty & Hmy).
eapply SRr_mono.
{ apply (aj_strcmp_at SEGS B LAWS pa_segs_low (pal_env B TL) (SIGMA CS___interceptor_trampoline_strcmp) (ASTRCMP fx) W (ms_regs ms) (ms_mem ms)
CHECK_ARITY_STK sp0 [] ly S W mem md [] ly S md' 0 x y sx sy (-144) (Z_to_bv 64 (BASE + retk)) HJ Ha0 Ha1 Hx0 Hy0); try assumption.
all: first [ rewrite Hsp; lia | reflexivity | lia | (unfold CHECK_ARITY_STK; lia) | (apply ret_ok_codeptr_v; [lia | exact Hrk2])
| exact (ce_rom_view W mem (ms_mem ms) sp0 HRO HCE HK) ]. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hcmp & Hfr).
split; [reflexivity|]. exists regs2, mem2, md2. split; [reflexivity|]. split; [exact HJ2|]. split; [exact HP2|]. split; [exact Hcmp|].
split; [apply (ce_kept_call W mem (ms_mem ms) mem2 sp0 (sp0 + -144 - 2 * ESTACK) (sp0 + -144) HK Hfr); unfold CHECK_ARITY_STK; lia|].
exact Hfr.
Qed.
Lemma ce_strncmp_at : forall ly S W sp0 mem md (ms : machine_state) md' x sx y sy n retk,
ajournal SEGS B CHECK_ARITY_STK sp0 [] ly S W mem md [] ly S W (ms_mem ms) md' 0 ->
arodata_okP SEGS RLO RHI B (rdW W mem) -> alloc_ceiling <= sp0 - CHECK_ARITY_STK -> ce_kept W mem (ms_mem ms) sp0 ->
getr (ms_regs ms) 10 = w64 x -> getr (ms_regs ms) 11 = w64 y -> getr (ms_regs ms) 12 = w64 n -> 0 <= n < 2 ^ 32 ->
spZ (ms_regs ms) = sp0 - 144 -> getr (ms_regs ms) 3 = w64 (as_gp B) -> getr (ms_regs ms) 4 = w64 (as_tp B) ->
getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + retk) -> 0 <= retk < 2 ^ 40 -> retk mod 2 = 0 ->
ce_ready W mem x sx -> ce_ready W mem y sy ->
SRr SEGS W (mkCfg (mkst (ms_regs ms) (Z_to_bv 64 (SIGMA CS___interceptor_trampoline_strncmp)) (ms_mem ms) (seg_rom SEGS)) md')
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
c2 = mkCfg (mkst regs2 (Z_to_bv 64 (BASE + retk)) mem2 (seg_rom SEGS)) md2 /\
ajournal SEGS B CHECK_ARITY_STK sp0 [] ly S W mem md [] ly S W mem2 md2 0 /\
aregs_preserved (ms_regs ms) regs2 /\
(getr regs2 10 = w64 0 <-> StrFun.strncmp_model (sx ++ [Z_to_bv 8 0]) (sy ++ [Z_to_bv 8 0]) n = Some 0) /\
ce_kept W mem mem2 sp0 /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + -144 - 2 * ESTACK <= a < sp0 + -144) -> ~ False ->
aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) (ms_mem ms) a)).
Proof.
intros ly S W sp0 mem md ms md' x sx y sy n retk HJ HRO HCE HK Ha0 Ha1 Ha2 Hn Hsp Hgp Htp Hra Hrk Hrk2 RX RY.
pose proof (ce_aj_pres _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as Hpr.
assert (Hes : ESTACK = 4096) by reflexivity.
destruct (ce_ready_call W mem (ms_mem ms) x sx sp0 (ms_regs ms) RX HCE HK Hpr ltac:(rewrite Hsp; unfold CHECK_ARITY_STK; lia))
as (Hx0 & Hsx & Hrx & Htx & Hmx).
destruct (ce_ready_call W mem (ms_mem ms) y sy sp0 (ms_regs ms) RY HCE HK Hpr ltac:(rewrite Hsp; unfold CHECK_ARITY_STK; lia))
as (Hy0 & Hsy & Hry & Hty & Hmy).
eapply SRr_mono.
{ apply (aj_strncmp_at SEGS B LAWS pa_segs_low (pal_env B TL) (SIGMA CS___interceptor_trampoline_strncmp) (ASTRNCMP fx) W (ms_regs ms) (ms_mem ms)
CHECK_ARITY_STK sp0 [] ly S W mem md [] ly S md' 0 x y n sx sy (-144) (Z_to_bv 64 (BASE + retk)) HJ Ha0 Ha1 Ha2
Hn Hx0 Hy0); try assumption.
all: first [ rewrite Hsp; lia | reflexivity | lia | (unfold CHECK_ARITY_STK; lia) | (apply ret_ok_codeptr_v; [lia | exact Hrk2])
| (apply (ce_aread_prefix _ _ _ _ _ _ _ Hrx); unfold astr_len; lia) | (apply (ce_aread_prefix _ _ _ _ _ _ _ Hry); unfold astr_len; lia)
| exact (ce_rom_view W mem (ms_mem ms) sp0 HRO HCE HK) ]. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hcmp & Hfr).
split; [reflexivity|]. exists regs2, mem2, md2. split; [reflexivity|]. split; [exact HJ2|]. split; [exact HP2|]. split; [exact Hcmp|].
split; [apply (ce_kept_call W mem (ms_mem ms) mem2 sp0 (sp0 + -144 - 2 * ESTACK) (sp0 + -144) HK Hfr); unfold CHECK_ARITY_STK; lia|].
exact Hfr.
Qed.
Lemma ce_strcspn_at : forall ly S W sp0 mem md (ms : machine_state) md' x sx y sy retk,
ajournal SEGS B CHECK_ARITY_STK sp0 [] ly S W mem md [] ly S W (ms_mem ms) md' 0 ->
arodata_okP SEGS RLO RHI B (rdW W mem) -> alloc_ceiling <= sp0 - CHECK_ARITY_STK -> ce_kept W mem (ms_mem ms) sp0 ->
getr (ms_regs ms) 10 = w64 x -> getr (ms_regs ms) 11 = w64 y ->
spZ (ms_regs ms) = sp0 - 144 -> getr (ms_regs ms) 3 = w64 (as_gp B) -> getr (ms_regs ms) 4 = w64 (as_tp B) ->
getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + retk) -> 0 <= retk < 2 ^ 40 -> retk mod 2 = 0 ->
ce_ready W mem x sx -> ce_ready W mem y sy ->
SRr SEGS W (mkCfg (mkst (ms_regs ms) (Z_to_bv 64 (SIGMA CS___interceptor_trampoline_strcspn)) (ms_mem ms) (seg_rom SEGS)) md')
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
c2 = mkCfg (mkst regs2 (Z_to_bv 64 (BASE + retk)) mem2 (seg_rom SEGS)) md2 /\
ajournal SEGS B CHECK_ARITY_STK sp0 [] ly S W mem md [] ly S W mem2 md2 0 /\
aregs_preserved (ms_regs ms) regs2 /\ getr regs2 10 = w64 (Z.of_nat (cspn_len sy sx)) /\
ce_kept W mem mem2 sp0 /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + -144 - 2 * ESTACK <= a < sp0 + -144) -> ~ False ->
aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) (ms_mem ms) a)).
Proof.
intros ly S W sp0 mem md ms md' x sx y sy retk HJ HRO HCE HK Ha0 Ha1 Hsp Hgp Htp Hra Hrk Hrk2 RX RY.
pose proof (ce_aj_pres _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as Hpr.
assert (Hes : ESTACK = 4096) by reflexivity.
destruct (ce_ready_call W mem (ms_mem ms) x sx sp0 (ms_regs ms) RX HCE HK Hpr ltac:(rewrite Hsp; unfold CHECK_ARITY_STK; lia))
as (Hx0 & Hsx & Hrx & Htx & Hmx).
destruct (ce_ready_call W mem (ms_mem ms) y sy sp0 (ms_regs ms) RY HCE HK Hpr ltac:(rewrite Hsp; unfold CHECK_ARITY_STK; lia))
as (Hy0 & Hsy & Hry & Hty & Hmy).
eapply SRr_mono.
{ apply (aj_strcspn_at SEGS B LAWS pa_segs_low (pal_env B TL) (SIGMA CS___interceptor_trampoline_strcspn) 0xa6bf8 0x604158
(ASTRCSPN fx) W (ms_regs ms) (ms_mem ms) CHECK_ARITY_STK sp0 [] ly S W mem md [] ly S md' 0 x y sx sy (-144)
(Z_to_bv 64 (BASE + retk)) HJ Ha0 Ha1 Hx0 Hy0); try assumption.
all: first [ rewrite Hsp; lia | reflexivity | lia | (unfold CHECK_ARITY_STK; lia) | (apply ret_ok_codeptr_v; [lia | exact Hrk2])
| exact (cmd_rec_guard ly S W (ms_mem ms) md' (proj1 HJ))
| exact (ce_rom_view W mem (ms_mem ms) sp0 HRO HCE HK) ]. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hcmp & Hfr).
split; [reflexivity|]. exists regs2, mem2, md2. split; [reflexivity|]. split; [exact HJ2|]. split; [exact HP2|]. split; [exact Hcmp|].
split; [apply (ce_kept_call W mem (ms_mem ms) mem2 sp0 (sp0 + -144 - 2 * ESTACK) (sp0 + -144) HK Hfr); unfold CHECK_ARITY_STK; lia|].
exact Hfr.
Qed.

(** ** The entry seed *)
(* the stack window's shadow is zero (AR's zshadow_ok, YG0n.v:188-191; the window is page-aligned, YG0f.v:327-328) *)
Lemma ce_stack_ra : forall ly S W mem md a n, AR SEGS B ly S W mem md -> ly_stk_lo ly <= a -> a + n <= ly_stk_hi ly ->
range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF a n.
Proof.
intros ly S W mem md a n HAR Hlo Hhi.
set (z := (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly)).
assert (Hin : In z (zero_shadow_ranges B ly)) by (left; reflexivity).
pose proof (al_zshadow _ _ LAWS ly S W mem md z HAR Hin) as Hzs.
destruct (zshadow_range_facts B ly S _ z (proj1 HAR) Hin) as (Hal & H0 & Hl & _).
pose proof (lo_top _ (am_layout _ _ _ _ (proj1 HAR))) as (_ & _ & _ & _ & Hpl & Hph & _).
unfold YG0f.page_aligned in Hpl, Hph.
assert (E8 : snd z / 8 * 8 = snd z).
{ subst z; cbn [snd]. pose proof (Z.div_mod (ly_stk_lo ly) 4096 ltac:(lia)) as D1.
  pose proof (Z.div_mod (ly_stk_hi ly) 4096 ltac:(lia)) as D2. rewrite Hpl in D1. rewrite Hph in D2.
  replace (ly_stk_hi ly - ly_stk_lo ly) with ((512 * (ly_stk_hi ly / 4096 - ly_stk_lo ly / 4096)) * 8) by lia.
  rewrite Z.div_mul by lia. reflexivity. }
assert (RA : range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF (fst z) (snd z / 8 * 8)).
{ apply zero_shadow_range; [exact Hal | rewrite Z.mod_mul by lia; reflexivity |].
  intros i Hi. apply Hzs. rewrite Z.div_mul in Hi by lia. exact Hi. }
destruct (Z_le_gt_dec n 0) as [Hn|Hn]; [intros x Hx; lia|].
eapply range_addressable_sub; [exact RA | subst z; cbn [fst]; lia | rewrite E8; subst z; cbn [fst snd]; lia].
Qed.
Lemma ce_shok : forall (tp : bool) ly S W mem md E wp ww, AR SEGS B ly S W mem md ->
ew E 32 = Z_to_bv 64 SB -> ew E 10 = Z_to_bv 64 wp -> ew E 37 = Z_to_bv 64 ww ->
ly_stk_lo ly <= wp + 16 -> wp + 28 <= ly_stk_hi ly -> 2 ^ 46 <= wp ->
(tp = true -> in_blockA (ablocks B ly S) ww 8 /\ 0 <= ww < 2 ^ 64) ->
sh_ok SEGS CBx (ce_SH tp) E (mrestrict (w_H W) mem).
Proof.
intros tp ly S W mem md E wp ww HAR E32 E10 E37 Hlo Hhi Hw46 Hw.
pose proof (lo_top _ (am_layout _ _ _ _ (proj1 HAR))) as (_ & _ & _ & Hk & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (UB : U E CBx = SHADOW_OFF) by (unfold CBx; rewrite (U_atom E 32 SB E32) by (unfold SB; lia); reflexivity).
assert (U10 : U E (SOff 10 0) = wp) by (apply U_atom; [exact E10 | lia]).
assert (G : shent_ok SEGS CBx E (mrestrict (w_H W) mem) (mkSHE 10 16 28)).
{ apply (shent_ok_of_range SEGS (w_H W) mem E CBx 10 (wp + 16) 12 wp 16 28
    (ce_stack_ra ly S W mem md (wp + 16) 12 HAR Hlo ltac:(lia)) UB U10); [lia | lia |].
  intros x Hx. unfold SHADOW_OFF. lia. }
unfold sh_ok, ce_SH. destruct tp.
- destruct (Hw eq_refl) as [(b & k & Hin & Hb & He) Rw].
  destruct (al_blocks _ _ LAWS ly S W mem md b k HAR Hin) as (Hb16 & Hb4096 & Hbceil & Happ & _ & _ & Hk').
  pose proof (req_size_pos0 k ltac:(lia)) as [Hr0 Hrk].
  assert (U37 : U E (SOff 37 0) = ww) by (apply U_atom; [exact E37 | lia]).
  constructor; [exact G|]. constructor; [|constructor].
  apply (shent_ok_of_range SEGS (w_H W) mem E CBx 37 ww 8 ww 0 8); [| exact UB | exact U37 | lia | lia |].
  + apply (range_addressable_of_block SEGS B LAWS ly S W mem md b k); [exact HAR | exact Hin | lia | lia].
  + intros x Hx. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *. lia.
- constructor; [exact G | constructor].
Qed.

Lemma ce_seed : forall (tp np : bool) ly S W (regs : bvmap 5 word) mem md (wp t ww p0 q nc fn0 : Z),
afn_pre_na SEGS B CHECK_ARITY_STK ly S W regs mem md -> cmd_val_objs -> cmd_ro_ok (rdW W mem) ->
getr regs 10 = w64 wp -> wp mod 8 = 0 -> spZ regs <= wp -> wp + WORDS_W + 12 <= ly_stk_hi ly ->
aval_mem (rdW W mem) (wp + WORDS_N) 4 t -> (if tp then 1 <= t <= 4096 else t = 0) ->
aval_mem (rdW W mem) (wp + WORDS_W) 8 ww -> 0 <= ww < 2 ^ 64 ->
(tp = true -> in_blockA (ablocks B ly S) ww 8 /\ ww mod 8 = 0 /\ aval_mem (rdW W mem) ww 8 p0 /\ 0 <= p0 < 2 ^ 64) ->
aval_mem (rdW W mem) A_G_QUITTING 4 q -> 0 <= q < 2 ^ 32 ->
aval_mem (rdW W mem) (A_G_REC + OFF_NCALLS) 4 nc -> (if np then 1 <= nc <= 16 else nc = 0) ->
(np = true -> aval_mem (rdW W mem) (A_G_REC + OFF_CALLS + CALL_OFF_FN) 4 fn0 /\ 0 <= fn0 < REC_FN_COUNT) ->
st_ok_pi SEGS VAL (EC regs t q nc fn0 ww p0) (ss_ce tp np)
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_check_arity)) mem (seg_rom SEGS)))
/\ sh_ok SEGS CBx (ce_SH tp) (EC regs t q nc fn0 ww p0) (mrestrict (w_H W) mem).
Proof.
intros tp np ly S W regs mem md wp t ww p0 q nc fn0 HPRE HOBJ HRO H10 Hwp8 Hwp1 Hwp2 Ht Htr Hww Rww Hslot Hq Rq Hnc Rnc Hfn.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : CHECK_ARITY_STK = 8336) by reflexivity.
unfold WORDS_W, WORDS_N in *.
destruct HRO as [HROB HROT].
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & _ & Kgot & _). rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
pose proof (pa_obj_img 12 ltac:(lia)) as HcellR. pose proof (pa_obj_img 0 ltac:(lia)) as HgotR.
assert (V0 : VAL (A_OBJ 0) = 0xa5f50) by (rewrite HOBJ by (vm_compute; lia); vm_compute; reflexivity).
assert (V2 : VAL (A_OBJ 2) = 0xa6bc8) by (rewrite HOBJ by (vm_compute; lia); vm_compute; reflexivity).
assert (V6 : VAL (A_OBJ 6) = 0xa6be0) by (rewrite HOBJ by (vm_compute; lia); vm_compute; reflexivity).
assert (V12 : VAL (A_OBJ 12) = 0xb0c38) by (rewrite HOBJ by (vm_compute; lia); vm_compute; reflexivity).
rewrite restrict_mkst_fx.
set (E := EC regs t q nc fn0 ww p0).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (ce_extra t q nc fn0 ww p0)) n)
by (intros n Hn; subst E; unfold EC; apply Eimg_low; exact Hn).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 wp) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 t) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 q) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 nc) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (E36 : ew E 36 = Z_to_bv 64 fn0) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 4)).
assert (E37 : ew E 37 = Z_to_bv 64 ww) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 5)).
assert (E38 : ew E 38 = Z_to_bv 64 p0) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 6)).
assert (EI : forall i, (i < 100)%nat -> ew E (A_OBJ i) = Z_to_bv 64 (VAL (A_OBJ i)))
by (intros i Hi; subst E; unfold EC; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
assert (B2 : base_val E (Some 2%nat) = spZ regs) by (cbn [base_val]; exact Usp).
assert (B10 : base_val E (Some 10%nat) = wp) by (apply VB; [exact E10 | lia]).
assert (B32 : base_val E (Some 32%nat) = SB) by (apply VB; [exact E32 | unfold SB; lia]).
assert (B37 : base_val E (Some 37%nat) = ww) by (apply VB; [exact E37 | lia]).
assert (B241 : base_val E (Some (A_OBJ 0)) = 0xa5f50) by (rewrite <- V0; apply VB; [exact (EI 0%nat ltac:(lia)) | pose proof (pa_val_range (A_OBJ 0)); lia]).
assert (B243 : base_val E (Some (A_OBJ 2)) = 0xa6bc8) by (rewrite <- V2; apply VB; [exact (EI 2%nat ltac:(lia)) | pose proof (pa_val_range (A_OBJ 2)); lia]).
assert (B247 : base_val E (Some (A_OBJ 6)) = 0xa6be0) by (rewrite <- V6; apply VB; [exact (EI 6%nat ltac:(lia)) | pose proof (pa_val_range (A_OBJ 6)); lia]).
assert (B253 : base_val E (Some (A_OBJ 12)) = 0xb0c38) by (rewrite <- V12; apply VB; [exact (EI 12%nat ltac:(lia)) | pose proof (pa_val_range (A_OBJ 12)); lia]).
assert (RS : region_ok SEGS E (mrestrict (w_H W) mem) (stack_region 144)).
{ unfold stack_region, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite B2.
  split; [lia|]. split; [lia|]. split; [|constructor].
  intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia. }
assert (RG : region_ok SEGS E (mrestrict (w_H W) mem) got_regionP).
{ unfold got_regionP, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  rewrite B241. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  constructor; [|constructor].
  apply (chunk_ok_val SEGS E _ 0xa5f50 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
  [cbn [sv_denot]; rewrite (EI 12%nat ltac:(lia)), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
  | pose proof (pa_val_range (A_OBJ 12)); zside | zside |].
  rewrite <- V0, Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot). }
assert (RB : region_ok SEGS E (mrestrict (w_H W) mem) (bcell_regionP 32)).
{ unfold bcell_regionP, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  rewrite B253. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  constructor; [|constructor].
  apply (chunk_ok_val SEGS E _ 0xb0c38 0 8 (SOff 32 0) SB);
  [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
  rewrite <- V12, Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell). }
assert (RW : region_ok SEGS E (mrestrict (w_H W) mem) ce_words).
{ unfold ce_words, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite B10.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  constructor; [|constructor; [|constructor]].
  - apply (chunk_ok_val SEGS E _ wp 16 8 (SOff 37 0) ww);
    [cbn [sv_denot]; rewrite E37, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
    exact (CmdRecRest.val_mem_of_aval SEGS _ _ _ _ _ Hww).
  - apply (chunk_ok_val SEGS E _ wp 24 4 (SOff 33 0) t);
    [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | destruct tp; zside | zside |].
    exact (CmdRecRest.val_mem_of_aval SEGS _ _ _ _ _ Ht). }
assert (RGQ : region_ok SEGS E (mrestrict (w_H W) mem) ce_gotq).
{ unfold ce_gotq, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite B247.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  constructor; [|constructor].
  apply (chunk_ok_val SEGS E _ 0xa6be0 0 8 (SLit A_G_QUITTING) A_G_QUITTING); [reflexivity | unfold A_G_QUITTING; zside | zside |].
  rewrite Z.add_0_r. replace A_G_QUITTING with (bytes_le_to_Z RO_ptr_a6be0) by (vm_compute; reflexivity).
  apply ce_word_of_bytes; [unfold cmd_ro_bytes in HROB; ca_pick HROB | reflexivity]. }
assert (RGR : region_ok SEGS E (mrestrict (w_H W) mem) ce_gotr).
{ unfold ce_gotr, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite B243.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  constructor; [|constructor].
  apply (chunk_ok_val SEGS E _ 0xa6bc8 0 8 (SLit A_G_REC) A_G_REC); [reflexivity | unfold A_G_REC; zside | zside |].
  rewrite Z.add_0_r. replace A_G_REC with (bytes_le_to_Z RO_ptr_a6bc8) by (vm_compute; reflexivity).
  apply ce_word_of_bytes; [unfold cmd_ro_bytes in HROB; ca_pick HROB | reflexivity]. }
assert (RQ : region_ok SEGS E (mrestrict (w_H W) mem) ce_quit).
{ unfold ce_quit, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  split; [unfold A_G_QUITTING; lia|]. split; [unfold A_G_QUITTING; lia|]. split; [intros o Ho; lia|].
  constructor; [|constructor].
  apply (chunk_ok_val SEGS E _ 0 A_G_QUITTING 4 (SOff 34 0) q);
  [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
  rewrite Z.add_0_l. exact (CmdRecRest.val_mem_of_aval SEGS _ _ _ _ _ Hq). }
assert (RR : region_ok SEGS E (mrestrict (w_H W) mem) (ce_rec np)).
{ unfold ce_rec, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  split; [unfold A_G_REC; lia|]. split; [unfold A_G_REC; lia|]. split; [intros o Ho; lia|].
  assert (C8 : YP09.chunk_ok SEGS E (mrestrict (w_H W) mem) 0 (YP09.mkChunk (A_G_REC + 8) (CVal 4 (SOff 35 0)))).
  { apply (chunk_ok_val SEGS E _ 0 (A_G_REC + 8) 4 (SOff 35 0) nc);
    [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | destruct np; zside | zside |].
    rewrite Z.add_0_l. exact (CmdRecRest.val_mem_of_aval SEGS _ _ _ _ _ Hnc). }
  destruct np; constructor; try exact C8; [|constructor].
  destruct (Hfn eq_refl) as [Hf Rf]. constructor; [|constructor].
  apply (chunk_ok_val SEGS E _ 0 (A_G_REC + 16) 4 (SOff 36 0) fn0);
  [cbn [sv_denot]; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold REC_FN_COUNT in Rf; zside | zside |].
  rewrite Z.add_0_l. exact (CmdRecRest.val_mem_of_aval SEGS _ _ _ _ _ Hf). }
assert (RQS : region_ok SEGS E (mrestrict (w_H W) mem) ce_qsh).
{ unfold ce_qsh, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite B32.
  split; [unfold SB, A_G_QUITTING; lia|]. split; [unfold SB, A_G_QUITTING; lia|]. split; [intros o Ho; lia|].
  constructor; [|constructor].
  apply (chunk_ok_val SEGS E _ SB (A_G_QUITTING / 8) 1 (SLit 4) 4); [reflexivity | zside | zside |].
  apply ca_zbyte_val; [lia|]. replace SB with SHADOW_OFF by reflexivity.
  exact (ca_shadow_byte B HB ly S W mem md A_G_QUITTING 4 HAR ltac:(vm_compute; reflexivity)
    ltac:(unfold A_G_QUITTING; lia) ltac:(lia) ltac:(vm_compute; reflexivity)). }
assert (RRS : region_ok SEGS E (mrestrict (w_H W) mem) ce_rsh).
{ unfold ce_rsh, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite B32.
  split; [unfold SB, A_G_REC; lia|]. split; [unfold SB, A_G_REC; lia|]. split; [intros o Ho; lia|].
  constructor; [|constructor].
  apply chunk_ok_zero. intros i Hi. assert (Hi2 : i = 0 \/ i = 1) by lia.
  destruct Hi2 as [-> | ->].
  - replace (SB + (A_G_REC + 8) / 8 + 0) with (SHADOW_OFF + (A_G_REC + 8) / 8) by (vm_compute; reflexivity).
    exact (ca_shadow_byte B HB ly S W mem md (A_G_REC + 8) 0 HAR ltac:(vm_compute; reflexivity)
      ltac:(unfold A_G_REC; lia) ltac:(lia) ltac:(vm_compute; reflexivity)).
  - replace (SB + (A_G_REC + 8) / 8 + 1) with (SHADOW_OFF + (A_G_REC + 16) / 8) by (vm_compute; reflexivity).
    exact (ca_shadow_byte B HB ly S W mem md (A_G_REC + 16) 0 HAR ltac:(vm_compute; reflexivity)
      ltac:(unfold A_G_REC; lia) ltac:(lia) ltac:(vm_compute; reflexivity)). }
assert (FACT : facts_ok E (ce_facts tp np)).
{ split; [|split; exact I].
  assert (U33 : bv_unsigned (ew E 33) = t) by (rewrite E33; apply unsigned_lit_small; destruct tp; lia).
  assert (U35 : bv_unsigned (ew E 35) = nc) by (rewrite E35; apply unsigned_lit_small; destruct np; lia).
  destruct tp, np; cbn [ce_facts f_atoms app atoms_ok]; unfold afact_ok; cbn [af_lo af_hi af_al2];
  rewrite ?Usp, ?E10, ?E32, ?U33, ?E34, ?U35, ?E36, ?E37, ?E38, ?unsigned_lit_small
    by (first [unfold SB; lia | lia | destruct (Hfn eq_refl); unfold REC_FN_COUNT in *; lia]);
  change (2 ^ 4) with 16; change (2 ^ 3) with 8; rewrite ?Z.pow_0_r, ?Z.mod_1_r;
  repeat split; try lia; try exact (proj1 (proj2 (Hslot eq_refl)));
  try (destruct (Hfn eq_refl); unfold REC_FN_COUNT in *; lia);
  try (destruct (Hslot eq_refl) as ((b & k & Hin & Hb & He) & _ & _);
       destruct (al_blocks _ _ LAWS ly S W mem md b k HAR Hin) as (_ & Hb4096 & Hbceil & _ & _ & _ & Hk);
       pose proof (req_size_pos0 k ltac:(lia)) as [Hr0 Hrk]; pose proof alloc_ceiling_lt; lia). }
assert (SH : sh_ok SEGS CBx (ce_SH tp) E (mrestrict (w_H W) mem)).
{ apply (ce_shok tp ly S W mem md E wp ww HAR E32 E10 E37); [lia | lia | lia |].
  intros Ht'. destruct (Hslot Ht') as (Hb & _ & _). split; [exact Hb | lia]. }
split; [|exact SH].
unfold ss_ce. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- destruct tp, np; vm_compute; reflexivity.
- unfold ce_regions. destruct tp; cbn [app]; repeat apply Forall_cons; try apply Forall_nil; try assumption.
  destruct (Hslot eq_refl) as ((b & k & Hin & Hbb & He) & _ & Hs & Rs).
  destruct (al_blocks _ _ LAWS ly S W mem md b k HAR Hin) as (_ & Hb4096 & Hbceil & _ & _ & _ & Hk).
  pose proof (req_size_pos0 k ltac:(lia)) as [Hr0 Hrk]. pose proof alloc_ceiling_lt.
  unfold ce_slot, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite B37.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  constructor; [|constructor].
  apply (chunk_ok_val SEGS E _ ww 0 8 (SOff 38 0) p0);
  [cbn [sv_denot]; rewrite E38, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
  rewrite Z.add_0_r. exact (CmdRecRest.val_mem_of_aval SEGS _ _ _ _ _ Hs).
- apply pairwise_disjoint_of_extents.
  unfold ce_regions, stack_region, got_regionP, bcell_regionP, ce_words, ce_gotq, ce_gotr, ce_quit, ce_rec, ce_qsh, ce_rsh,
    ce_slot, extent_of_region.
  destruct tp; cbn [app map YP09.r_base YP09.r_lo YP09.r_hi];
  rewrite ?B2, ?B10, ?B32, ?B37, ?B241, ?B243, ?B247, ?B253; cbn [base_val];
  cbn [zpairwise_disjoint zall_disjoint]; unfold zdisj; cbn [fst snd].
  + destruct (Hslot eq_refl) as ((b & k & Hin & Hb & He) & _ & _).
    destruct (al_blocks _ _ LAWS ly S W mem md b k HAR Hin) as (Hb16 & Hb4096 & Hbceil & Happ & _ & _ & Hk).
    pose proof (req_size_pos0 k ltac:(lia)) as [Hr0 Hrk].
    pose proof (blk_off_imgP B ly S W mem md b k HAR Hin) as Hoff. unfold off_img in Hoff.
    unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ.
    revert Hslo Hceil H47 Hshi Hwp1 Hwp2 Hb Hb4096 He Hbceil Hrk Hoff Happ C1 WS Hstk0. clear.
    unfold SB, A_G_QUITTING, A_G_REC, SHADOW_OFF. intros. repeat split; lia.
  + revert Hslo Hceil H47 Hshi Hwp1 Hwp2 C1 WS Hstk0. clear.
    unfold SB, A_G_QUITTING, A_G_REC. intros. repeat split; lia.
- exact FACT.
Qed.

(** ** Helpers of the walk *)
Lemma ce_ew_agree : forall k E0 E n, env_agree k E0 E -> (n < k)%nat -> ew E n = ew E0 n.
Proof. intros k E0 E n [HA _] Hn. exact (HA n Hn). Qed.
Lemma ce_agree32 : forall E1 E0 E, env_agree 32 E1 E0 -> env_agree 40 E0 E -> env_agree 32 E1 E.
Proof. intros E1 E0 E [A1 D1] [A2 D2]. split; [intros n Hn; rewrite A2 by lia; apply A1; lia | congruence]. Qed.
Lemma ce_agree_ewset : forall E0 E T w, env_agree 40 E0 E -> (40 <= T)%nat -> env_agree 40 E0 (ewset E T w).
Proof. intros E0 E T w [A D] HT. split; [intros n Hn; rewrite ew_ewset_other by lia; apply A; lia | rewrite ed_ewset; exact D]. Qed.
Lemma ce_img_atom : forall E a, img_env VAL A_LIM E -> (A_TEXT <= a < A_LIM)%nat -> ew E a = Z_to_bv 64 (VAL a).
Proof. intros E a HE Ha. rewrite <- (HE a Ha). symmetry. apply Z_to_bv_bv_unsigned. Qed.
Lemma ce_havoc_a0 : forall E k (regs2 : bvmap 5 word), ew (havoc E k (map (getr regs2) CLOB)) (k + 4) = getr regs2 10.
Proof. intros E k regs2. rewrite (ew_havoc_new E k _ 4 (Z_to_bv 64 0)) by (rewrite length_map; cbn; lia). reflexivity. Qed.
Lemma ce_U_w : forall E n (w : word), ew E n = w -> U E (SOff n 0) = bv_unsigned w.
Proof. intros E n w H. rewrite U_SOff, H, Z.add_0_r. apply zcanon_unsigned. Qed.
Lemma ce_br_eq : forall E a v z, U E a = v -> branch_taken BC_EQ (sv_denot E a) (sv_denot E (SLit z)) = (v =? zcanon z).
Proof. intros E a v z H. rewrite branch_eq_U, H, U_SLit. reflexivity. Qed.
Lemma ce_br_ne : forall E a v z, U E a = v -> branch_taken BC_NE (sv_denot E a) (sv_denot E (SLit z)) = negb (v =? zcanon z).
Proof. intros E a v z H. rewrite branch_ne_U, H, U_SLit. reflexivity. Qed.
Lemma ce_lt_atom : forall E n v z, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 63 -> 0 <= z < 2 ^ 63 ->
branch_taken BC_LT (sv_denot E (SOff n 0)) (sv_denot E (SLit z)) = (v <? z).
Proof.
intros E n v z Hn Hv Hz. cbn [branch_taken]. rewrite bv_lts_signed.
change (bv_signed (sv_denot E (SOff n 0))) with (Sg E (SOff n 0)). change (bv_signed (sv_denot E (SLit z))) with (Sg E (SLit z)).
rewrite S_SOff, S_SLit, Hn, Z.add_0_r, unsigned_lit_small by lia. rewrite !swrap64_id by (unfold half64; lia). reflexivity.
Qed.
(* the read-only image facts at a later memory that agrees below 2 ^ 40 *)
Lemma ce_abytes_low : forall (rd rd' : reader) a L, abytes_atR rd a L ->
(forall x, 0 <= x < 2 ^ 40 -> rd' x = rd x) -> 0 <= a -> a + Z.of_nat (length L) <= 2 ^ 40 -> abytes_atR rd' a L.
Proof. intros rd rd' a L H Hag Ha HL i Hi. rewrite Hag by lia. exact (H i Hi). Qed.
Ltac ce_ro_tr H Hag :=
lazymatch type of H with
| _ /\ _ => let H1 := fresh "H" in let H2 := fresh "H" in destruct H as [H1 H2];
  split; [ce_ro_tr H1 Hag | ce_ro_tr H2 Hag]
| abytes_atR _ ?a ?L => apply (ce_abytes_low _ _ a L H Hag); [lia | apply Z.leb_le; vm_compute; reflexivity]
end.
Lemma ce_ro_ok_low : forall (rd rd' : reader), cmd_ro_ok rd -> (forall x, 0 <= x < 2 ^ 40 -> rd' x = rd x) -> cmd_ro_ok rd'.
Proof.
intros rd rd' [HRB HRT] Hag. split.
- unfold cmd_ro_bytes in *. ce_ro_tr HRB Hag.
- intros e He a Ha. rewrite Hag; [exact (HRT e He a Ha)|].
  assert (Hb : forallb (fun e => (0 <=? e) && (e + 8 <=? 2 ^ 40)) cmd_ro_ends = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in Hb. specialize (Hb e He). apply andb_true_iff in Hb as [H1 H2]. apply Z.leb_le in H1.
  apply Z.leb_le in H2. pose proof (Z.mod_pos_bound e 8 ltac:(lia)). lia.
Qed.
Lemma ce_ro_kept : forall W mem m sp0, cmd_ro_ok (rdW W mem) -> ce_kept W mem m sp0 ->
alloc_ceiling <= sp0 - CHECK_ARITY_STK -> cmd_ro_ok (rdW W m).
Proof.
intros W mem m sp0 HRO HK HCE. apply (ce_ro_ok_low _ _ HRO). intros x Hx.
pose proof asan_consts as (C1 & _). apply HK; lia.
Qed.
(* the 22 row names, as strings the strcmp wrapper reads *)
Lemma ce_names_ready : forall ly S W mem md, AR SEGS B ly S W mem md -> cmd_ro_ok (rdW W mem) ->
forall j, (j < 22)%nat -> ce_ready W mem (ca_name_addr j) (ca_nm j).
Proof.
intros ly S W mem md HAR HRO j Hj.
assert (E : ca_nm j = removelast (ca_name_bytes j)) by (do 22 (destruct j as [|j]; [reflexivity|]); lia).
rewrite E. pose proof (ca_ro_name _ (proj1 HRO) j Hj) as HNB.
do 22 (destruct j as [|j];
  [ apply (ce_ready_lit ly S W mem md _ _ HAR HRO HNB); vm_compute; first [reflexivity | intros; discriminate] |]).
lia.
Qed.
(* the saved registers' chunks of the frame region (atom 2 = the entry sp), as the prologue stores them *)
Definition ce_saved : list nat := [1; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat.
Definition ce_chunk_is (c : YP09.chunk) (off : Z) (e : sv) : bool :=
(YP09.c_off c =? off) && match YP09.c_val c with CVal n e' => N.eqb n 8 && sv_eqb e' e | _ => false end.
Lemma ce_chunk_isE : forall c off e, ce_chunk_is c off e = true -> c = YP09.mkChunk off (CVal 8 e).
Proof.
intros [o cv] off e H. unfold ce_chunk_is in H. cbn [YP09.c_off YP09.c_val] in H.
apply andb_true_iff in H as [H1 H2]. apply Z.eqb_eq in H1. subst o.
destruct cv; try discriminate. apply andb_true_iff in H2 as [H2 H3]. apply N.eqb_eq in H2. apply sv_eqb_eq in H3. subst. reflexivity.
Qed.
Definition ce_frame_b (rs : smem) : bool :=
match rs with
| r :: _ => match YP09.r_base r with Some 2%nat => true | _ => false end &&
   forallb (fun j => existsb (fun c => ce_chunk_is c (-8 - 8 * Z.of_nat j) (SOff (nth j ce_saved 0%nat) 0)) (YP09.r_chunks r))
     (seq 0 13)
| [] => false
end.
Lemma ce_frame_from : forall E ss ms (W : world SEGS) regs extra,
st_ok_pi SEGS VAL E ss (restrict (w_H W) ms) ->
(forall n, (n < 32)%nat -> ew E n = ew (Ereg regs extra) n) ->
ce_frame_b (ss_mem ss) = true ->
ca_frame_at W (ms_mem ms) (spZ regs - 144) regs.
Proof.
intros E ss ms W regs extra HS HE Hb.
assert (Hv : forall jj, (jj < 13)%nat -> sv_denot E (SOff (nth jj ce_saved 0%nat) 0) =
  Z_to_bv 64 (bv_unsigned (nth jj (ca_sv regs) (Z_to_bv 64 0)))).
{ intros jj Hjj.
  do 13 (destruct jj as [|jj]; [cbn [nth ce_saved ca_sv sv_denot]; rewrite Z.add_0_r, !Z_to_bv_bv_unsigned, HE by lia;
    apply ew_Ereg_nat; reflexivity|]).
  lia. }
pose proof (st_ok_mem_ok SEGS E (abs_ss VAL ss) _ HS) as (_ & Hok & _).
change (ss_mem (abs_ss VAL ss)) with (ss_mem ss) in Hok. cbn [ms_mem restrict] in Hok.
unfold ce_frame_b in Hb. destruct (ss_mem ss) as [|r rs]; [discriminate|].
inversion Hok as [|r' rs' Hr Hrs]; subst.
apply andb_true_iff in Hb as [Hb1 Hb2].
destruct (YP09.r_base r) as [[|[|[|n]]]|] eqn:Hbase; try discriminate.
pose proof Hr as (_ & _ & _ & Hch). rewrite Hbase in Hch. cbn [base_val] in Hch.
rewrite (HE 2%nat ltac:(lia)), (ew_Ereg_nat regs extra 2 2%bv eq_refl) in Hch.
intros j Hj.
rewrite forallb_forall in Hb2. pose proof (Hb2 j (proj2 (in_seq 13 0 j) (conj (Nat.le_0_l j) Hj))) as Hx.
apply existsb_exists in Hx as (c & Hc & Hce). apply ce_chunk_isE in Hce. subst c.
rewrite Forall_forall in Hch. pose proof (Hch _ Hc) as Hck.
replace (spZ regs - 144 + 136 - 8 * Z.of_nat j) with (bv_unsigned (getr regs 2) + (-8 - 8 * Z.of_nat j)) by (unfold spZ; lia).
apply (val_of_chunk_ok SEGS E _ _ _ 8 _ _ Hck (Hv j Hj)); [| cbn; lia].
pose proof (bv_unsigned_in_range 64 (nth j (ca_sv regs) (Z_to_bv 64 0))) as R. change (bv_modulus 64) with (2 ^ 64) in R.
change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
Qed.

(** ** The machine state at the scan head 0x87448 before pass k *)
Definition ca_lpre (k : nat) ly S (W : world SEGS) (regs0 : bvmap 5 word) mem0 md0 (p0 : Z) (v : list byte) (s3v : Z)
(regs : bvmap 5 word) memc mdc : Prop :=
ajournal SEGS B CHECK_ARITY_STK (spZ regs0) [] ly S W mem0 md0 [] ly S W memc mdc 0 /\
YK0s.ret_ok (getr regs0 1) /\ getr regs0 3 = w64 (as_gp B) /\ getr regs0 4 = w64 (as_tp B) /\
arodata_okP SEGS RLO RHI B (rdW W mem0) /\ cmd_ro_ok (rdW W mem0) /\
alloc_ceiling <= spZ regs0 - CHECK_ARITY_STK /\ 2 ^ 46 <= spZ regs0 <= 2 ^ 47 /\
ce_kept W mem0 memc (spZ regs0) /\
spZ regs = spZ regs0 - 144 /\ ca_frame_at W memc (spZ regs) regs0 /\
getr regs 3 = getr regs0 3 /\ getr regs 4 = getr regs0 4 /\
getr regs 8 = w64 p0 /\ getr regs 18 = w64 SHADOW_OFF /\ getr regs 19 = w64 s3v /\
getr regs 20 = w64 (24 * Z.of_nat k) /\ getr regs 21 = w64 (zcanon (- SHADOW_OFF - 3 * Z.of_nat k)) /\
getr regs 22 = w64 CA_GP /\ getr regs 23 = w64 (SHADOW_OFF + CA_GP / 8 + 3 * Z.of_nat k) /\
getr regs 24 = w64 0x210 /\
1 <= s3v <= 64 /\ ce_ready W mem0 p0 v /\ ca_aok v (s3v - 1) /\
(forall j, (j < 22)%nat -> ce_ready W mem0 (ca_name_addr j) (ca_nm j)).

(* the entry walk's symbolic registers at the scan head (probe of the run, every scan-bound path) *)
Definition ce_head_ok (sr : list sv) : bool :=
sv_eqb (sr_get sr 2) (SOff 2 (-144)) && sv_eqb (sr_get sr 3) (SOff 3 0) && sv_eqb (sr_get sr 4) (SOff 4 0) &&
sv_eqb (sr_get sr 8) (SOff 38 0) && sv_eqb (sr_get sr 18) (SOff 32 0) && sv_eqb (sr_get sr 20) (SLit 0) &&
sv_eqb (sr_get sr 21) (SAlu ALU_SUB (SLit 0) (SOff 32 0)) && sv_eqb (sr_get sr 22) (SOff 259 0) &&
sv_eqb (sr_get sr 23) (SAlu ALU_ADD (SOff 32 0) (SAlu ALU_SRL (SOff 259 0) (SLit 3))) && sv_eqb (sr_get sr 24) (SLit 528).

Lemma ce_close : forall E ss ms ly S W regs mem md md' E0 extra p0 v s3v,
st_ok_pi SEGS VAL E ss (restrict (w_H W) ms) -> img_env VAL A_LIM E ->
env_agree 40 E0 E -> (forall n, (n < 32)%nat -> ew E0 n = ew (Ereg regs extra) n) ->
ew E0 32 = Z_to_bv 64 SB -> ew E0 38 = Z_to_bv 64 p0 -> cmd_val_objs ->
ce_head_ok (ss_regs ss) = true -> ce_frame_b (ss_mem ss) = true ->
sv_denot E (sr_get (ss_regs ss) 19) = w64 s3v -> 1 <= s3v <= 64 ->
ajournal SEGS B CHECK_ARITY_STK (spZ regs) [] ly S W mem md [] ly S W (ms_mem ms) md' 0 ->
YK0s.ret_ok (getr regs 1) -> getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
arodata_okP SEGS RLO RHI B (rdW W mem) -> cmd_ro_ok (rdW W mem) ->
alloc_ceiling <= spZ regs - CHECK_ARITY_STK -> 2 ^ 46 <= spZ regs <= 2 ^ 47 ->
ce_kept W mem (ms_mem ms) (spZ regs) ->
ce_ready W mem p0 v -> ca_aok v (s3v - 1) -> (forall j, (j < 22)%nat -> ce_ready W mem (ca_name_addr j) (ca_nm j)) ->
ca_lpre 0 ly S W regs mem md p0 v s3v (ms_regs ms) (ms_mem ms) md'.
Proof.
intros E ss ms ly S W regs mem md md' E0 extra p0 v s3v HS HEI HAG EL32 F32 F38 HOBJ Hh Hf H19 Hs3 HJ Hra Hgp Htp HRO HROK HCE Hsp
  HK RP RA RN.
assert (GR : forall r, getr (ms_regs ms) r = sv_denot E (sr_get (ss_regs ss) r))
by (intros r; exact (st_ok_pi_restrict_reg (w_H W) E ss ms r HS)).
unfold ce_head_ok in Hh. repeat rewrite andb_true_iff in Hh.
destruct Hh as (((((((((H2 & H3) & H4) & H8) & H18) & H20) & H21) & H22) & H23) & H24).
apply sv_eqb_eq in H2, H3, H4, H8, H18, H20, H21, H22, H23, H24.
assert (EA : forall n, (n < 32)%nat -> ew E n = ew (Ereg regs extra) n).
{ intros n Hn. rewrite (ce_ew_agree 40 _ E n HAG ltac:(lia)). exact (EL32 n Hn). }
assert (ER : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r).
{ intros n r Hn. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite (EA n ltac:(lia)). apply ew_Ereg_nat. exact Hn. }
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (rewrite (ce_ew_agree 40 _ E 32 HAG ltac:(lia)); exact F32).
assert (E38 : ew E 38 = Z_to_bv 64 p0) by (rewrite (ce_ew_agree 40 _ E 38 HAG ltac:(lia)); exact F38).
assert (E259 : ew E 259%nat = Z_to_bv 64 CA_GP).
{ rewrite (ce_img_atom E 259%nat HEI ltac:(unfold A_TEXT, A_LIM; lia)).
  change 259%nat with (A_OBJ 18). rewrite HOBJ by (vm_compute; lia). reflexivity. }
assert (SP : spZ (ms_regs ms) = spZ regs - 144).
{ unfold spZ at 1. rewrite GR, H2. cbn [sv_denot]. rewrite (ER 2%nat 2%bv eq_refl).
  change (bv_unsigned (getr regs 2)) with (spZ regs). rewrite unsigned_lit_small by lia. lia. }
unfold ca_lpre.
split; [exact HJ|]. split; [exact Hra|]. split; [exact Hgp|]. split; [exact Htp|]. split; [exact HRO|].
split; [exact HROK|]. split; [exact HCE|]. split; [exact Hsp|]. split; [exact HK|]. split; [exact SP|].
split; [rewrite SP; exact (ce_frame_from E ss ms W regs _ HS EA Hf)|].
split; [rewrite GR, H3; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact (ER 3%nat 3%bv eq_refl)|].
split; [rewrite GR, H4; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact (ER 4%nat 4%bv eq_refl)|].
split; [rewrite GR, H8; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, E38; reflexivity|].
split; [rewrite GR, H18; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, E32; reflexivity|].
split; [rewrite GR; exact H19|].
split; [rewrite GR, H20; reflexivity|].
split; [rewrite GR, H21; cbn [sv_denot]; rewrite E32; apply bv_eq; vm_compute; reflexivity|].
split; [rewrite GR, H22; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, E259; reflexivity|].
split; [rewrite GR, H23; cbn [sv_denot]; rewrite E32, E259; apply bv_eq; vm_compute; reflexivity|].
split; [rewrite GR, H24; reflexivity|].
split; [exact Hs3|]. split; [exact RP|]. split; [exact RA | exact RN].
Qed.

(** ** The entry walk: 0x87268 to the scan head 0x87448, and every return before it *)
Lemma ce_cspn_le : forall set s, (cspn_len set s <= length s)%nat.
Proof. intros set s. induction s as [|x s IH]; cbn [cspn_len length]; [lia|]. destruct (existsb _ set); lia. Qed.
Lemma ce_U_atom0 : forall E0 E n v, env_agree 40 E0 E -> (n < 40)%nat -> ew E0 n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
U E (SOff n 0) = v.
Proof.
intros E0 E n v HA Hn Hv R. rewrite U_SOff, (ce_ew_agree 40 E0 E n HA Hn), Hv, Z.add_0_r, unsigned_lit_small by lia.
apply zcanon_id. unfold M64. lia.
Qed.
Lemma ce_region_kept : forall E H (m m2 : word -> option byte) n b lo hi wlo whi cs,
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

Let RUN := paj_run B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_cmd) (PI := PI).

Ltac ce_usp := lazymatch goal with |- bv_unsigned (ew ?E 2) = _ =>
lazymatch goal with HAG : env_agree 40 ?E0 E, U0 : bv_unsigned (ew ?E0 2) = _ |- _ =>
first [exact U0 | rewrite (ce_ew_agree 40 E0 E 2 HAG ltac:(lia)); exact U0] end end.
Ltac ce_keep := lazymatch goal with
| HK : ce_kept ?W ?mem ?m0 ?sp0, HFr : frame_of ?E ?rs (mrestrict _ _) (mrestrict _ ?m1) |- _ =>
  let HK2 := fresh "HK" in let Hs := fresh "Hs" in
  assert (Hs : bv_unsigned (ew E 2) = sp0) by ce_usp;
  pose proof (ce_kept_run W mem m0 m1 E rs sp0 (-144) 0 HK HFr ltac:(vm_compute; reflexivity)
    ltac:(rewrite Hs; unfold CHECK_ARITY_STK, ESTACK; lia) ltac:(rewrite Hs; lia)) as HK2;
  clear HK HFr Hs; rename HK2 into HK end;
repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
Ltac ce_reagree := lazymatch goal with HAG : env_agree 40 ?E0 ?E |- _ =>
let E' := lazymatch goal with
  | HS : st_ok_pi _ _ ?E' _ (restrict _ _) |- _ => E'
  | HS : st_ok _ ?E' _ (restrict _ _) |- _ => E' end in
tryif constr_eq E E' then idtac else
(let H := fresh "HAG" in assert (H : env_agree 40 E0 E') by (repeat (apply ce_agree_ewset; [|lia]); exact HAG);
 clear HAG; rename H into HAG) end.
Ltac ce_mdv := repeat (let mdv := fresh "mdv" in set (mdv := with_vm_backing _ _ _) in *; clearbody mdv).
Ltac ce_run := lazymatch goal with HS : st_ok_pi _ _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
SHOK : sh_ok _ _ _ _ _ |- _ =>
paj_run_tok RUN HS HJ SHOK CBspan; [awr_ok_tac; ce_usp |]; ce_keep; ce_reagree; ce_mdv end.
Ltac ce_br := lazymatch goal with HS : st_ok_pi _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
psrr_branch_tok RUN BR HS SHOK CBspan end.
Ltac ce_leaf := lazymatch goal with HS : st_ok_pi _ _ ?E _ (restrict _ ?ms), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
HAG : env_agree 40 ?E0 ?E, HAE : env_agree 32 _ ?E0, F1 : ew ?E0 1 = _, Hra : YK0s.ret_ok _ |- _ =>
eapply (RET _ _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity));
let mat' := fresh "mat" in intros mat';
let R1 := fresh "R1" in prreg HS (1%bv : bv 5) R1;
unfold ca_post, apost_base; eexists _, _, _, _, _;
split; [cbn [ms_regs]; rewrite R1; first [rewrite F1 | rewrite (ce_ew_agree 40 E0 E 1 HAG ltac:(lia)), F1];
  unfold YK0s.ret_ok in Hra; rewrite Hra; reflexivity|];
split; [apply (ajournal_materialize SEGS B LAWS pa_segs_low); exact HJ|];
split; [eapply (aregs_preserved_of_st_ok SEGS _ E _ _ _ _ HS); [exact (ce_agree32 _ _ _ HAE HAG) | vm_compute; reflexivity]|];
split; reflexivity end.
(* the base of a kept region: an atom of the entry (sp, wp, SB, ww) or an object of the listing *)
Ltac ce_base := first
[ eassumption
| lazymatch goal with HAG : env_agree 40 ?E0 ?E |- bv_unsigned (ew ?E ?n) = _ =>
    rewrite (ce_ew_agree 40 E0 E n HAG ltac:(lia)); eassumption end
| lazymatch goal with HEI : img_env _ _ ?E |- bv_unsigned (ew ?E ?n) = _ =>
    rewrite (HEI n ltac:(cbv; lia)); eassumption end ].
Ltac ce_kept_regions HS2 Hfr2 HJ2 :=
match type of HS2 with ?tt -> _ => let HRK := fresh "HRK" in assert (HRK : tt); [|specialize (HS2 HRK); clear HRK] end;
[ cbn [ms_mem restrict]; repeat apply Forall_cons; try apply Forall_nil;
  first
  [ eapply ce_region_kept; [ce_base | intros a Ha; apply Hfr2; [lia | lia | tauto]
    | intros a Ha; first [lia | apply (ce_aj_pres _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2); unfold CHECK_ARITY_STK; lia]]
  | apply region_kept_aview_none; [intros a Ha; apply Hfr2; [lia | lia | tauto] | lia] ] |].
(* a call's result is not zero: the branch `beqz a0` fell through *)
Ltac ce_ne0 pre := lazymatch goal with Hc : branch_taken BC_EQ _ (sv_denot _ (SLit 0)) = false,
UA : U _ _ = bv_unsigned (getr ?r 10), Hcmp : getr ?r 10 = w64 0 <-> _ |- _ =>
let Heq := fresh "Heq" in intro Heq; pre Heq; apply Hcmp in Heq;
rewrite (ce_br_eq _ _ _ 0 UA), Heq in Hc; vm_compute in Hc; discriminate Hc end.
Ltac ce_pre_id H := idtac.

Lemma ce_walk : forall ly St W (regs : bvmap 5 word) mem md (wp t ww p0 q nc fn0 : Z) (v : list byte),
afn_pre_na SEGS B CHECK_ARITY_STK ly St W regs mem md ->
arodata_okP SEGS RLO RHI B (rdW W mem) -> cmd_ro_ok (rdW W mem) -> cmd_val_objs ->
getr regs 10 = w64 wp -> 0 <= wp < 2 ^ 64 -> wp mod 8 = 0 -> spZ regs <= wp -> wp + WORDS_W + 12 <= ly_stk_hi ly ->
aval_mem (rdW W mem) (wp + WORDS_N) 4 t -> 0 <= t <= 4096 ->
aval_mem (rdW W mem) (wp + WORDS_W) 8 ww -> 0 <= ww < 2 ^ 64 ->
(0 < t -> in_blockA (ablocks B ly St) ww 8 /\ ww mod 8 = 0 /\ aval_mem (rdW W mem) ww 8 p0 /\
 0 <= p0 < 2 ^ 64 /\ in_blockA (ablocks B ly St) p0 (Z.of_nat (length v) + 1) /\ astr_atR (rdW W mem) p0 v) ->
aval_mem (rdW W mem) A_G_QUITTING 4 q -> 0 <= q < 2 ^ 32 ->
aval_mem (rdW W mem) (A_G_REC + OFF_NCALLS) 4 nc -> 0 <= nc <= 16 ->
(0 < nc -> aval_mem (rdW W mem) (A_G_REC + OFF_CALLS + CALL_OFF_FN) 4 fn0 /\ 0 <= fn0 < REC_FN_COUNT) ->
arity_ok t v q nc fn0 ->
(forall regsc memc mdc, ca_lpre 0 ly St W regs mem md p0 v (Z.min t 64) regsc memc mdc ->
  SRr SEGS W (cfg_at SEGS (BASE + CE_LOOP) regsc memc mdc) (ca_post B regs ly St W mem md)) ->
SRr SEGS W (cfg_at SEGS (BASE + AF_check_arity) regs mem md) (ca_post B regs ly St W mem md).
Proof.
intros ly St W regs mem md wp t ww p0 q nc fn0 v HPRE HRO HROK HOBJ H10 Rwp Hwp8 Hwp1 Hwp2 Ht Rt Hww Rww H4 Hq Rq Hnc Rnc Hfn
  Har HSCAN.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hes : ESTACK = 4096) by reflexivity. assert (WS : CHECK_ARITY_STK = 8336) by reflexivity.
assert (HCE : alloc_ceiling <= spZ regs - CHECK_ARITY_STK) by lia.
assert (Hsp46 : 2 ^ 46 <= spZ regs <= 2 ^ 47) by lia.
unfold WORDS_W, WORDS_N in *.
pose proof (ce_names_ready ly St W mem md HAR HROK) as RNAMES.
assert (V0 : VAL (A_OBJ 0) = 0xa5f50) by (rewrite HOBJ by (vm_compute; lia); vm_compute; reflexivity).
assert (V2 : VAL (A_OBJ 2) = 0xa6bc8) by (rewrite HOBJ by (vm_compute; lia); vm_compute; reflexivity).
assert (V5 : VAL (A_OBJ 5) = 0x210e0) by (rewrite HOBJ by (vm_compute; lia); vm_compute; reflexivity).
assert (V6 : VAL (A_OBJ 6) = 0xa6be0) by (rewrite HOBJ by (vm_compute; lia); vm_compute; reflexivity).
assert (V12 : VAL (A_OBJ 12) = 0xb0c38) by (rewrite HOBJ by (vm_compute; lia); vm_compute; reflexivity).
assert (V14 : VAL (A_OBJ 14) = 0x21180) by (rewrite HOBJ by (vm_compute; lia); vm_compute; reflexivity).
assert (V15 : VAL (A_OBJ 15) = 0x211a0) by (rewrite HOBJ by (vm_compute; lia); vm_compute; reflexivity).
assert (V16 : VAL (A_OBJ 16) = 0x211c0) by (rewrite HOBJ by (vm_compute; lia); vm_compute; reflexivity).
assert (V17 : VAL (A_OBJ 17) = 0x211e0) by (rewrite HOBJ by (vm_compute; lia); vm_compute; reflexivity).
assert (R14 : ce_ready W mem 0x21180 ce_s14).
{ assert (HL : abytes_atR (rdW W mem) 0x21180 RO_lit_21180) by (ca_pick (proj1 HROK)).
  apply (ce_ready_lit ly St W mem md 0x21180 RO_lit_21180 HAR HROK HL); vm_compute; first [reflexivity | intros; discriminate]. }
assert (R15 : ce_ready W mem 0x211a0 ce_s15).
{ assert (HL : abytes_atR (rdW W mem) 0x211a0 RO_lit_211a0) by (ca_pick (proj1 HROK)).
  apply (ce_ready_lit ly St W mem md 0x211a0 RO_lit_211a0 HAR HROK HL); vm_compute; first [reflexivity | intros; discriminate]. }
assert (R16 : ce_ready W mem 0x211c0 ce_s16).
{ assert (HL : abytes_atR (rdW W mem) 0x211c0 RO_lit_211c0) by (ca_pick (proj1 HROK)).
  apply (ce_ready_lit ly St W mem md 0x211c0 RO_lit_211c0 HAR HROK HL); vm_compute; first [reflexivity | intros; discriminate]. }
assert (R17 : ce_ready W mem 0x211e0 ce_s17).
{ assert (HL : abytes_atR (rdW W mem) 0x211e0 RO_lit_211e0) by (ca_pick (proj1 HROK)).
  apply (ce_ready_lit ly St W mem md 0x211e0 RO_lit_211e0 HAR HROK HL); vm_compute; first [reflexivity | intros; discriminate]. }
assert (RSET : ce_ready W mem 0x210e0 ce_set).
{ assert (HL : abytes_atR (rdW W mem) 0x210e0 RO_lit_210e0) by (ca_pick (proj1 HROK)).
  apply (ce_ready_lit ly St W mem md 0x210e0 RO_lit_210e0 HAR HROK HL); vm_compute; first [reflexivity | intros; discriminate]. }
(* the seed *)
assert (HTR : if (0 <? t) then 1 <= t <= 4096 else t = 0) by (destruct (Z.ltb_spec 0 t); lia).
assert (HNR : if (0 <? nc) then 1 <= nc <= 16 else nc = 0) by (destruct (Z.ltb_spec 0 nc); lia).
assert (HSL : (0 <? t) = true -> in_blockA (ablocks B ly St) ww 8 /\ ww mod 8 = 0 /\ aval_mem (rdW W mem) ww 8 p0 /\
  0 <= p0 < 2 ^ 64)
by (intros Hb; apply Z.ltb_lt in Hb; destruct (H4 Hb) as (A1 & A8 & A2 & A3 & _); auto).
assert (HFN : (0 <? nc) = true -> aval_mem (rdW W mem) (A_G_REC + OFF_CALLS + CALL_OFF_FN) 4 fn0 /\ 0 <= fn0 < REC_FN_COUNT)
by (intros Hb; apply Z.ltb_lt in Hb; exact (Hfn Hb)).
destruct (ce_seed (0 <? t) (0 <? nc) ly St W regs mem md wp t ww p0 q nc fn0 HPRE HOBJ HROK H10 Hwp8 Hwp1 Hwp2 Ht HTR Hww Rww
  HSL Hq Rq Hnc HNR HFN) as [HS SHOK].
pose proof (ajournal_init_na SEGS B CHECK_ARITY_STK [] ly St W regs mem md HPRE) as HJ.
pose proof (ce_kept_refl W mem (spZ regs)) as HK.
remember (EC regs t q nc fn0 ww p0) as E0 eqn:HE0.
assert (HEIE0 : img_env VAL A_LIM E0) by (rewrite HE0; unfold EC; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E0 n = ew (Ereg regs (ce_extra t q nc fn0 ww p0)) n)
by (intros n Hn; rewrite HE0; unfold EC; apply Eimg_low; exact Hn).
assert (EL32 : forall n, (n < 32)%nat -> ew E0 n = ew (Ereg regs (ce_extra t q nc fn0 ww p0)) n)
by (intros n Hn; apply EL; unfold A_TEXT; lia).
assert (F1 : ew E0 1 = getr regs 1) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (F3 : ew E0 3 = getr regs 3) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (F4 : ew E0 4 = getr regs 4) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (F2 : ew E0 2 = Z_to_bv 64 (spZ regs))
by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); unfold spZ; rewrite Z_to_bv_bv_unsigned; reflexivity).
assert (F10 : ew E0 10 = Z_to_bv 64 wp) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (F32 : ew E0 32 = Z_to_bv 64 SB) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (F33 : ew E0 33 = Z_to_bv 64 t) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (F34 : ew E0 34 = Z_to_bv 64 q) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (F35 : ew E0 35 = Z_to_bv 64 nc) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (F36 : ew E0 36 = Z_to_bv 64 fn0) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 4)).
assert (F37 : ew E0 37 = Z_to_bv 64 ww) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 5)).
assert (F38 : ew E0 38 = Z_to_bv 64 p0) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 6)).
assert (HAE : env_agree 32 (Ereg regs (ce_extra t q nc fn0 ww p0)) E0)
by (split; [intros n Hn; apply EL; unfold A_TEXT; lia | rewrite HE0; reflexivity]).
assert (HAG : env_agree 40 E0 E0) by (split; [intros; reflexivity | reflexivity]).
assert (Usp0 : bv_unsigned (ew E0 2) = spZ regs) by (rewrite F2; apply unsigned_lit_small; lia).
assert (U10 : bv_unsigned (ew E0 10) = wp) by (rewrite F10; apply unsigned_lit_small; lia).
(* the shadow base as a numeral, so that lia bounds the shadow regions based at atom 32 *)
assert (U32 : bv_unsigned (ew E0 32) = 0x7fff8000) by (rewrite F32; apply unsigned_lit_small; unfold SB; lia).
assert (U37 : bv_unsigned (ew E0 37) = ww) by (rewrite F37; apply unsigned_lit_small; lia).
clear HE0 EL.
unfold cfg_at. change (w64 (BASE + AF_check_arity)) with (Z_to_bv 64 (BASE + AF_check_arity)).
revert HS SHOK HTR HSL. destruct (Z.ltb_spec 0 t) as [Ht0|Ht0]; intros HS SHOK HTR HSL.
2:{ (* t = 0: the message has no words, return (0x872d0); both values of `0 <? nc` are made literal first, so
     that no run sees a variable *)
  revert HS SHOK HNR HFN. destruct (Z.ltb_spec 0 nc) as [Hn0|Hn0]; intros HS SHOK HNR HFN.
  all: ce_run; ce_br;
  [ ce_run; ce_leaf
  | exfalso; lazymatch goal with Hc : branch_taken BC_EQ _ _ = false |- _ =>
      rewrite (ce_br_eq _ _ t 0 (ce_U_atom0 E0 _ 33 t HAG ltac:(lia) F33 ltac:(lia))) in Hc;
      assert (t = 0) by lia; subst t; vm_compute in Hc; discriminate Hc end ]. }
(* t > 0: the first word, its slot and the heap block it lies in *)
destruct (H4 Ht0) as (HWW & _ & Hslot & Rp0 & Hpb & Hps).
pose proof (ce_ready_of_blk ly St W mem md p0 v HAR Hpb Hps) as RP0.
pose proof RP0 as (_ & _ & _ & [_ HNUL] & _).
pose proof HWW as (bw & kw & Hinw & Hbw & Hew).
destruct (al_blocks _ _ LAWS ly St W mem md bw kw HAR Hinw) as (_ & Hbw4096 & Hbwceil & Happw & _ & _ & Hkw).
pose proof (req_size_pos0 kw ltac:(lia)) as [Hrw0 Hrwk].
pose proof (blk_off_imgP B ly St W mem md bw kw HAR Hinw) as Hoffw. unfold off_img in Hoffw.
revert HS SHOK HNR HFN. destruct (Z.ltb_spec 0 nc) as [Hn0|Hn0]; intros HS SHOK HNR HFN.
- (* a recorded call: q's branch (0x87310) merges at the first call's function (0x87320) *)
  ce_run; ce_br.
  all: ce_run; ce_br.
  1,3: (        assert (HQN : q <> 0 \/ nc <> 0) by (right; lia);
        assert (HPO : nc <= 0 \/ fn0 <> 5 \/ passed_on_m v = false)
          by (right; left; intro Hf5; subst fn0;
              lazymatch goal with Hc : branch_taken BC_NE _ _ = true |- _ =>
                rewrite (ce_br_ne _ _ 5 5 (ce_U_atom0 E0 _ 36 5 HAG ltac:(lia) F36 ltac:(lia))) in Hc;
                vm_compute in Hc; discriminate Hc end);
        (let HAOK := fresh "HAOK" in
assert (HAOK : ce_box (ca_aok v (Z.min t 64 - 1))) by (constructor; apply (ce_arity t v q nc fn0 Har ltac:(lia) HQN HPO));
(* lia sees every hypothesis: drop the disjunctions before the runs *)
clear HQN HPO;
ce_run; ce_br;
[ lazymatch goal with Hc : branch_taken BC_LT _ _ = true |- _ =>
    rewrite (ce_lt_atom _ 33 t 64 (eq_trans (ce_ew_agree 40 E0 _ 33 HAG ltac:(lia)) F33) ltac:(lia) ltac:(lia)) in Hc;
    apply Z.ltb_lt in Hc end;
  ce_run; (lazymatch goal with HS : st_ok_pi _ _ ?E ?ss (restrict _ ?ms), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
HAG : env_agree 40 ?E0 ?E, HK : ce_kept _ _ _ _ |- SRr _ _ (mkCfg _ ?mdx) _ =>
pmkst HS;
refine (HSCAN (ms_regs ms) (ms_mem ms) mdx _);
apply (ce_close E ss ms ly St W regs mem md mdx E0 (ce_extra t q nc fn0 ww p0) p0 v (Z.min t 64) HS ltac:(assumption)
  HAG EL32 F32 F38 HOBJ ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity));
[ let e := eval vm_compute in (sr_get (ss_regs ss) (19%bv : bv 5)) in change (sr_get (ss_regs ss) (19%bv : bv 5)) with e; (cbn [sv_denot]; rewrite (ce_ew_agree 40 E0 _ 33 HAG) by lia; rewrite F33, unsigned_lit_small by lia;
  replace (Z.min t 64) with (t + 0) by lia; reflexivity)
| lia | exact HJ | exact Hra | exact Hgp | exact Htp | exact HRO | exact HROK | exact HCE | exact Hsp46 | exact HK
| exact RP0 | exact (ce_unbox _ HAOK) | exact RNAMES ] end)
| lazymatch goal with Hc : branch_taken BC_LT _ _ = false |- _ =>
    rewrite (ce_lt_atom _ 33 t 64 (eq_trans (ce_ew_agree 40 E0 _ 33 HAG ltac:(lia)) F33) ltac:(lia) ltac:(lia)) in Hc;
    apply Z.ltb_ge in Hc end;
  ce_run; (lazymatch goal with HS : st_ok_pi _ _ ?E ?ss (restrict _ ?ms), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
HAG : env_agree 40 ?E0 ?E, HK : ce_kept _ _ _ _ |- SRr _ _ (mkCfg _ ?mdx) _ =>
pmkst HS;
refine (HSCAN (ms_regs ms) (ms_mem ms) mdx _);
apply (ce_close E ss ms ly St W regs mem md mdx E0 (ce_extra t q nc fn0 ww p0) p0 v (Z.min t 64) HS ltac:(assumption)
  HAG EL32 F32 F38 HOBJ ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity));
[ let e := eval vm_compute in (sr_get (ss_regs ss) (19%bv : bv 5)) in change (sr_get (ss_regs ss) (19%bv : bv 5)) with e; (cbn [sv_denot]; replace (Z.min t 64) with 64 by lia; reflexivity)
| lia | exact HJ | exact Hra | exact Hgp | exact Htp | exact HRO | exact HROK | exact HCE | exact Hsp46 | exact HK
| exact RP0 | exact (ce_unbox _ HAOK) | exact RNAMES ] end) ])).
  all: (ce_run; (lazymatch goal with HS : st_ok _ ?E _ (restrict _ ?ms), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, HK : ce_kept _ _ _ _ |- _ =>
let Ra0 := fresh "Ra0" in let Ra1 := fresh "Ra1" in let Ra2 := fresh "Ra2" in let Rra := fresh "Rra" in
let Qsp := fresh "Qsp" in let Qgp := fresh "Qgp" in let Qtp := fresh "Qtp" in
prreg HS (10%bv : bv 5) Ra0; prreg HS (11%bv : bv 5) Ra1; prreg HS (12%bv : bv 5) Ra2; prreg HS (1%bv : bv 5) Rra;
prreg HS (2%bv : bv 5) Qsp; prreg HS (3%bv : bv 5) Qgp; prreg HS (4%bv : bv 5) Qtp;
pmkst HS;
eapply SRr_bind;
[ apply (ce_strcmp_at ly St W (spZ regs) mem md ms _ p0 v 0x21180 ce_s14 3672 HJ HRO HCE HK);
  [ (rewrite Ra0; first [rewrite F38 | rewrite (ce_ew_agree 40 E0 _ 38 HAG) by lia; rewrite F38]; reflexivity) | (rewrite Ra1, (ce_img_atom E0 255%nat HEIE0 ltac:(cbv; lia)); change 255%nat with (A_OBJ 14%nat); rewrite V14; reflexivity) | (unfold spZ at 1; rewrite Qsp; first [rewrite Usp0 | rewrite (ce_ew_agree 40 E0 _ 2 HAG) by lia; rewrite Usp0];
    rewrite unsigned_lit_small by lia; lia) | (rewrite Qgp; first [rewrite F3 | rewrite (ce_ew_agree 40 E0 _ 3 HAG) by lia; rewrite F3]; exact Hgp) | (rewrite Qtp; first [rewrite F4 | rewrite (ce_ew_agree 40 E0 _ 4 HAG) by lia; rewrite F4]; exact Htp) | exact Rra | lia | reflexivity
  | exact RP0 | exact R14 ]
| ];
clear Ra0 Ra1 Ra2 Rra Qsp Qgp Qtp; cbv beta;
let W2 := fresh "W2" in let c2 := fresh "c2" in let regs2 := fresh "regs" in let mem2 := fresh "mem" in
let md2 := fresh "md" in let HJ2 := fresh "HJ" in let HP2 := fresh "HP" in let Hcmp := fresh "Hcmp" in
let HK2 := fresh "HK" in let Hfr2 := fresh "Hfr" in
intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hcmp & HK2 & Hfr2);
((* HJ and HK are the caller's (bound before the intros): a fresh match would take the new ones *)
lazymatch goal with HS : st_ok _ ?E _ _, SHOK : sh_ok _ _ _ _ _, HAG : env_agree 40 ?E0 ?E |- _ =>
let HS2 := fresh "HS" in
jafter_call_keep_pi HS 40%nat regs2 (mrestrict (w_H W) mem2) HP2 [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10]%nat HS2;
ce_kept_regions HS2 Hfr2 HJ2;
clear HS SHOK HK HJ; rewrite <- restrict_mkst_fx in HS2;
let HEIx := fresh "HEI" in let HAGx := fresh "HAG" in let SH := fresh "SHOK" in let UA := fresh "UA" in
assert (HEIx : img_env VAL A_LIM (havoc E 40%nat (map (getr regs2) CLOB)))
  by (apply img_env_havoc; [assumption | apply Nat.leb_le; vm_compute; reflexivity]);
assert (HAGx : env_agree 40 E0 (havoc E 40%nat (map (getr regs2) CLOB))) by (apply env_agree_havoc_ge; [lia | exact HAG]);
clear HAG;
assert (SH : sh_ok SEGS CBx (ce_SH true) (havoc E 40%nat (map (getr regs2) CLOB)) (mrestrict (w_H W) mem2))
  by (apply (ce_shok true ly St W mem2 md2 _ wp ww (proj1 HJ2));
      [ rewrite (ce_ew_agree 40 E0 _ 32 HAGx) by lia; exact F32 | rewrite (ce_ew_agree 40 E0 _ 10 HAGx) by lia; exact F10
      | rewrite (ce_ew_agree 40 E0 _ 37 HAGx) by lia; exact F37 | lia | lia | lia | intros _; split; [exact HWW | lia]]);
pose proof (ce_U_w _ _ _ (ce_havoc_a0 E 40%nat regs2)) as UA; cbn [Nat.add] in UA;
rename HS2 into HS; rename HK2 into HK; rename HJ2 into HJ; rename HAGx into HAG; rename SH into SHOK
end)
end);
ce_run; ce_br;
[ ce_run; ce_leaf
| let H14 := fresh "H14" in assert (H14 : v <> ce_s14) by ce_ne0 ce_pre_id;
  ce_run; (lazymatch goal with HS : st_ok _ ?E _ (restrict _ ?ms), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, HK : ce_kept _ _ _ _ |- _ =>
let Ra0 := fresh "Ra0" in let Ra1 := fresh "Ra1" in let Ra2 := fresh "Ra2" in let Rra := fresh "Rra" in
let Qsp := fresh "Qsp" in let Qgp := fresh "Qgp" in let Qtp := fresh "Qtp" in
prreg HS (10%bv : bv 5) Ra0; prreg HS (11%bv : bv 5) Ra1; prreg HS (12%bv : bv 5) Ra2; prreg HS (1%bv : bv 5) Rra;
prreg HS (2%bv : bv 5) Qsp; prreg HS (3%bv : bv 5) Qgp; prreg HS (4%bv : bv 5) Qtp;
pmkst HS;
eapply SRr_bind;
[ apply (ce_strcmp_at ly St W (spZ regs) mem md ms _ p0 v 0x211a0 ce_s15 3692 HJ HRO HCE HK);
  [ (rewrite Ra0; first [rewrite F38 | rewrite (ce_ew_agree 40 E0 _ 38 HAG) by lia; rewrite F38]; reflexivity) | (rewrite Ra1, (ce_img_atom E0 256%nat HEIE0 ltac:(cbv; lia)); change 256%nat with (A_OBJ 15%nat); rewrite V15; reflexivity) | (unfold spZ at 1; rewrite Qsp; first [rewrite Usp0 | rewrite (ce_ew_agree 40 E0 _ 2 HAG) by lia; rewrite Usp0];
    rewrite unsigned_lit_small by lia; lia) | (rewrite Qgp; first [rewrite F3 | rewrite (ce_ew_agree 40 E0 _ 3 HAG) by lia; rewrite F3]; exact Hgp) | (rewrite Qtp; first [rewrite F4 | rewrite (ce_ew_agree 40 E0 _ 4 HAG) by lia; rewrite F4]; exact Htp) | exact Rra | lia | reflexivity
  | exact RP0 | exact R15 ]
| ];
clear Ra0 Ra1 Ra2 Rra Qsp Qgp Qtp; cbv beta;
let W2 := fresh "W2" in let c2 := fresh "c2" in let regs2 := fresh "regs" in let mem2 := fresh "mem" in
let md2 := fresh "md" in let HJ2 := fresh "HJ" in let HP2 := fresh "HP" in let Hcmp := fresh "Hcmp" in
let HK2 := fresh "HK" in let Hfr2 := fresh "Hfr" in
intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hcmp & HK2 & Hfr2);
((* HJ and HK are the caller's (bound before the intros): a fresh match would take the new ones *)
lazymatch goal with HS : st_ok _ ?E _ _, SHOK : sh_ok _ _ _ _ _, HAG : env_agree 40 ?E0 ?E |- _ =>
let HS2 := fresh "HS" in
jafter_call_keep_pi HS 56%nat regs2 (mrestrict (w_H W) mem2) HP2 [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10]%nat HS2;
ce_kept_regions HS2 Hfr2 HJ2;
clear HS SHOK HK HJ; rewrite <- restrict_mkst_fx in HS2;
let HEIx := fresh "HEI" in let HAGx := fresh "HAG" in let SH := fresh "SHOK" in let UA := fresh "UA" in
assert (HEIx : img_env VAL A_LIM (havoc E 56%nat (map (getr regs2) CLOB)))
  by (apply img_env_havoc; [assumption | apply Nat.leb_le; vm_compute; reflexivity]);
assert (HAGx : env_agree 40 E0 (havoc E 56%nat (map (getr regs2) CLOB))) by (apply env_agree_havoc_ge; [lia | exact HAG]);
clear HAG;
assert (SH : sh_ok SEGS CBx (ce_SH true) (havoc E 56%nat (map (getr regs2) CLOB)) (mrestrict (w_H W) mem2))
  by (apply (ce_shok true ly St W mem2 md2 _ wp ww (proj1 HJ2));
      [ rewrite (ce_ew_agree 40 E0 _ 32 HAGx) by lia; exact F32 | rewrite (ce_ew_agree 40 E0 _ 10 HAGx) by lia; exact F10
      | rewrite (ce_ew_agree 40 E0 _ 37 HAGx) by lia; exact F37 | lia | lia | lia | intros _; split; [exact HWW | lia]]);
pose proof (ce_U_w _ _ _ (ce_havoc_a0 E 56%nat regs2)) as UA; cbn [Nat.add] in UA;
rename HS2 into HS; rename HK2 into HK; rename HJ2 into HJ; rename HAGx into HAG; rename SH into SHOK
end)
end);
  ce_run; ce_br;
  [ ce_run; ce_leaf
  | let H15 := fresh "H15" in assert (H15 : v <> ce_s15) by ce_ne0 ce_pre_id;
    ce_run; (lazymatch goal with HS : st_ok _ ?E _ (restrict _ ?ms), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, HK : ce_kept _ _ _ _ |- _ =>
let Ra0 := fresh "Ra0" in let Ra1 := fresh "Ra1" in let Ra2 := fresh "Ra2" in let Rra := fresh "Rra" in
let Qsp := fresh "Qsp" in let Qgp := fresh "Qgp" in let Qtp := fresh "Qtp" in
prreg HS (10%bv : bv 5) Ra0; prreg HS (11%bv : bv 5) Ra1; prreg HS (12%bv : bv 5) Ra2; prreg HS (1%bv : bv 5) Rra;
prreg HS (2%bv : bv 5) Qsp; prreg HS (3%bv : bv 5) Qgp; prreg HS (4%bv : bv 5) Qtp;
pmkst HS;
eapply SRr_bind;
[ apply (ce_strcspn_at ly St W (spZ regs) mem md ms _ p0 v 0x210e0 ce_set 3712 HJ HRO HCE HK);
  [ (rewrite Ra0; first [rewrite F38 | rewrite (ce_ew_agree 40 E0 _ 38 HAG) by lia; rewrite F38]; reflexivity) | (rewrite Ra1, (ce_img_atom E0 246%nat HEIE0 ltac:(cbv; lia)); change 246%nat with (A_OBJ 5%nat); rewrite V5; reflexivity) | (unfold spZ at 1; rewrite Qsp; first [rewrite Usp0 | rewrite (ce_ew_agree 40 E0 _ 2 HAG) by lia; rewrite Usp0];
    rewrite unsigned_lit_small by lia; lia) | (rewrite Qgp; first [rewrite F3 | rewrite (ce_ew_agree 40 E0 _ 3 HAG) by lia; rewrite F3]; exact Hgp) | (rewrite Qtp; first [rewrite F4 | rewrite (ce_ew_agree 40 E0 _ 4 HAG) by lia; rewrite F4]; exact Htp) | exact Rra | lia | reflexivity
  | exact RP0 | exact RSET ]
| ];
clear Ra0 Ra1 Ra2 Rra Qsp Qgp Qtp; cbv beta;
let W2 := fresh "W2" in let c2 := fresh "c2" in let regs2 := fresh "regs" in let mem2 := fresh "mem" in
let md2 := fresh "md" in let HJ2 := fresh "HJ" in let HP2 := fresh "HP" in let Hcmp := fresh "Hcmp" in
let HK2 := fresh "HK" in let Hfr2 := fresh "Hfr" in
intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hcmp & HK2 & Hfr2);
((* HJ and HK are the caller's (bound before the intros): a fresh match would take the new ones *)
lazymatch goal with HS : st_ok _ ?E _ _, SHOK : sh_ok _ _ _ _ _, HAG : env_agree 40 ?E0 ?E |- _ =>
let HS2 := fresh "HS" in
jafter_call_keep_pi HS 72%nat regs2 (mrestrict (w_H W) mem2) HP2 [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10]%nat HS2;
ce_kept_regions HS2 Hfr2 HJ2;
clear HS SHOK HK HJ; rewrite <- restrict_mkst_fx in HS2;
let HEIx := fresh "HEI" in let HAGx := fresh "HAG" in let SH := fresh "SHOK" in let UA := fresh "UA" in
assert (HEIx : img_env VAL A_LIM (havoc E 72%nat (map (getr regs2) CLOB)))
  by (apply img_env_havoc; [assumption | apply Nat.leb_le; vm_compute; reflexivity]);
assert (HAGx : env_agree 40 E0 (havoc E 72%nat (map (getr regs2) CLOB))) by (apply env_agree_havoc_ge; [lia | exact HAG]);
clear HAG;
assert (SH : sh_ok SEGS CBx (ce_SH true) (havoc E 72%nat (map (getr regs2) CLOB)) (mrestrict (w_H W) mem2))
  by (apply (ce_shok true ly St W mem2 md2 _ wp ww (proj1 HJ2));
      [ rewrite (ce_ew_agree 40 E0 _ 32 HAGx) by lia; exact F32 | rewrite (ce_ew_agree 40 E0 _ 10 HAGx) by lia; exact F10
      | rewrite (ce_ew_agree 40 E0 _ 37 HAGx) by lia; exact F37 | lia | lia | lia | intros _; split; [exact HWW | lia]]);
pose proof (ce_U_w _ _ _ (ce_havoc_a0 E 72%nat regs2)) as UA; cbn [Nat.add] in UA;
rename HS2 into HS; rename HK2 into HK; rename HJ2 into HJ; rename HAGx into HAG; rename SH into SHOK
end)
end); (lazymatch goal with UA : U ?E ?a = bv_unsigned (getr ?r 10), Hcmp : getr ?r 10 = w64 (Z.of_nat ?c) |- _ =>
let UC := fresh "UC" in
assert (UC : U E a = Z.of_nat c) by (rewrite UA, Hcmp; apply unsigned_lit_small;
  pose proof (ce_cspn_le ce_set v); pose proof RP0 as (_ & _ & Hn32 & _); lia); clear UA end);
    ce_run; ce_br;
    [ (* the length of the first word is 10: strncmp(v, "disconnect %s %s", 10) *)
      lazymatch goal with Hc : branch_taken BC_EQ _ _ = true, UC : U _ _ = Z.of_nat _ |- _ =>
        rewrite (ce_br_eq _ _ _ 10 UC) in Hc; apply Z.eqb_eq in Hc; change (zcanon 10) with 10 in Hc end;
      ce_run; (lazymatch goal with HS : st_ok _ ?E _ (restrict _ ?ms), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, HK : ce_kept _ _ _ _ |- _ =>
let Ra0 := fresh "Ra0" in let Ra1 := fresh "Ra1" in let Ra2 := fresh "Ra2" in let Rra := fresh "Rra" in
let Qsp := fresh "Qsp" in let Qgp := fresh "Qgp" in let Qtp := fresh "Qtp" in
prreg HS (10%bv : bv 5) Ra0; prreg HS (11%bv : bv 5) Ra1; prreg HS (12%bv : bv 5) Ra2; prreg HS (1%bv : bv 5) Rra;
prreg HS (2%bv : bv 5) Qsp; prreg HS (3%bv : bv 5) Qgp; prreg HS (4%bv : bv 5) Qtp;
pmkst HS;
eapply SRr_bind;
[ apply (ce_strncmp_at ly St W (spZ regs) mem md ms _ p0 v 0x211e0 ce_s17 10 3764 HJ HRO HCE HK);
  [ (rewrite Ra0; first [rewrite F38 | rewrite (ce_ew_agree 40 E0 _ 38 HAG) by lia; rewrite F38]; reflexivity) | (rewrite Ra1, (ce_img_atom E0 258%nat HEIE0 ltac:(cbv; lia)); change 258%nat with (A_OBJ 17%nat); rewrite V17; reflexivity) | rewrite Ra2; reflexivity | lia | (unfold spZ at 1; rewrite Qsp; first [rewrite Usp0 | rewrite (ce_ew_agree 40 E0 _ 2 HAG) by lia; rewrite Usp0];
    rewrite unsigned_lit_small by lia; lia) | (rewrite Qgp; first [rewrite F3 | rewrite (ce_ew_agree 40 E0 _ 3 HAG) by lia; rewrite F3]; exact Hgp) | (rewrite Qtp; first [rewrite F4 | rewrite (ce_ew_agree 40 E0 _ 4 HAG) by lia; rewrite F4]; exact Htp)
  | exact Rra | lia | reflexivity | exact RP0 | exact R17 ]
| ];
clear Ra0 Ra1 Ra2 Rra Qsp Qgp Qtp; cbv beta;
let W2 := fresh "W2" in let c2 := fresh "c2" in let regs2 := fresh "regs" in let mem2 := fresh "mem" in
let md2 := fresh "md" in let HJ2 := fresh "HJ" in let HP2 := fresh "HP" in let Hcmp := fresh "Hcmp" in
let HK2 := fresh "HK" in let Hfr2 := fresh "Hfr" in
intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hcmp & HK2 & Hfr2);
((* HJ and HK are the caller's (bound before the intros): a fresh match would take the new ones *)
lazymatch goal with HS : st_ok _ ?E _ _, SHOK : sh_ok _ _ _ _ _, HAG : env_agree 40 ?E0 ?E |- _ =>
let HS2 := fresh "HS" in
jafter_call_keep_pi HS 88%nat regs2 (mrestrict (w_H W) mem2) HP2 [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10]%nat HS2;
ce_kept_regions HS2 Hfr2 HJ2;
clear HS SHOK HK HJ; rewrite <- restrict_mkst_fx in HS2;
let HEIx := fresh "HEI" in let HAGx := fresh "HAG" in let SH := fresh "SHOK" in let UA := fresh "UA" in
assert (HEIx : img_env VAL A_LIM (havoc E 88%nat (map (getr regs2) CLOB)))
  by (apply img_env_havoc; [assumption | apply Nat.leb_le; vm_compute; reflexivity]);
assert (HAGx : env_agree 40 E0 (havoc E 88%nat (map (getr regs2) CLOB))) by (apply env_agree_havoc_ge; [lia | exact HAG]);
clear HAG;
assert (SH : sh_ok SEGS CBx (ce_SH true) (havoc E 88%nat (map (getr regs2) CLOB)) (mrestrict (w_H W) mem2))
  by (apply (ce_shok true ly St W mem2 md2 _ wp ww (proj1 HJ2));
      [ rewrite (ce_ew_agree 40 E0 _ 32 HAGx) by lia; exact F32 | rewrite (ce_ew_agree 40 E0 _ 10 HAGx) by lia; exact F10
      | rewrite (ce_ew_agree 40 E0 _ 37 HAGx) by lia; exact F37 | lia | lia | lia | intros _; split; [exact HWW | lia]]);
pose proof (ce_U_w _ _ _ (ce_havoc_a0 E 88%nat regs2)) as UA; cbn [Nat.add] in UA;
rename HS2 into HS; rename HK2 into HK; rename HJ2 into HJ; rename HAGx into HAG; rename SH into SHOK
end)
end);
      ce_run; ce_br;
      [ ce_run; ce_leaf
      | let H17 := fresh "H17" in
        assert (H17 : firstn 10 v <> ce_k17)
          by ce_ne0 ltac:(fun H => apply (ce_strncmp17 v HNUL) in H);
        (assert (HQN : q <> 0 \/ nc <> 0) by (right; lia);
assert (HPO : nc <= 0 \/ fn0 <> 5 \/ passed_on_m v = false)
  by (right; right; apply ce_po_false; [assumption | assumption | intros C | intros C];
      first [assumption | exfalso; unfold ce_hide in *; lia]);
(let HAOK := fresh "HAOK" in
assert (HAOK : ce_box (ca_aok v (Z.min t 64 - 1))) by (constructor; apply (ce_arity t v q nc fn0 Har ltac:(lia) HQN HPO));
(* lia sees every hypothesis: drop the disjunctions before the runs *)
clear HQN HPO;
ce_run; ce_br;
[ lazymatch goal with Hc : branch_taken BC_LT _ _ = true |- _ =>
    rewrite (ce_lt_atom _ 33 t 64 (eq_trans (ce_ew_agree 40 E0 _ 33 HAG ltac:(lia)) F33) ltac:(lia) ltac:(lia)) in Hc;
    apply Z.ltb_lt in Hc end;
  ce_run; (lazymatch goal with HS : st_ok_pi _ _ ?E ?ss (restrict _ ?ms), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
HAG : env_agree 40 ?E0 ?E, HK : ce_kept _ _ _ _ |- SRr _ _ (mkCfg _ ?mdx) _ =>
pmkst HS;
refine (HSCAN (ms_regs ms) (ms_mem ms) mdx _);
apply (ce_close E ss ms ly St W regs mem md mdx E0 (ce_extra t q nc fn0 ww p0) p0 v (Z.min t 64) HS ltac:(assumption)
  HAG EL32 F32 F38 HOBJ ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity));
[ let e := eval vm_compute in (sr_get (ss_regs ss) (19%bv : bv 5)) in change (sr_get (ss_regs ss) (19%bv : bv 5)) with e; (cbn [sv_denot]; rewrite (ce_ew_agree 40 E0 _ 33 HAG) by lia; rewrite F33, unsigned_lit_small by lia;
  replace (Z.min t 64) with (t + 0) by lia; reflexivity)
| lia | exact HJ | exact Hra | exact Hgp | exact Htp | exact HRO | exact HROK | exact HCE | exact Hsp46 | exact HK
| exact RP0 | exact (ce_unbox _ HAOK) | exact RNAMES ] end)
| lazymatch goal with Hc : branch_taken BC_LT _ _ = false |- _ =>
    rewrite (ce_lt_atom _ 33 t 64 (eq_trans (ce_ew_agree 40 E0 _ 33 HAG ltac:(lia)) F33) ltac:(lia) ltac:(lia)) in Hc;
    apply Z.ltb_ge in Hc end;
  ce_run; (lazymatch goal with HS : st_ok_pi _ _ ?E ?ss (restrict _ ?ms), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
HAG : env_agree 40 ?E0 ?E, HK : ce_kept _ _ _ _ |- SRr _ _ (mkCfg _ ?mdx) _ =>
pmkst HS;
refine (HSCAN (ms_regs ms) (ms_mem ms) mdx _);
apply (ce_close E ss ms ly St W regs mem md mdx E0 (ce_extra t q nc fn0 ww p0) p0 v (Z.min t 64) HS ltac:(assumption)
  HAG EL32 F32 F38 HOBJ ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity));
[ let e := eval vm_compute in (sr_get (ss_regs ss) (19%bv : bv 5)) in change (sr_get (ss_regs ss) (19%bv : bv 5)) with e; (cbn [sv_denot]; replace (Z.min t 64) with 64 by lia; reflexivity)
| lia | exact HJ | exact Hra | exact Hgp | exact Htp | exact HRO | exact HROK | exact HCE | exact Hsp46 | exact HK
| exact RP0 | exact (ce_unbox _ HAOK) | exact RNAMES ] end) ])) ]
    | lazymatch goal with Hc : branch_taken BC_EQ _ _ = false, UC : U _ _ = Z.of_nat _ |- _ =>
        rewrite (ce_br_eq _ _ _ 10 UC) in Hc; apply Z.eqb_neq in Hc; change (zcanon 10) with 10 in Hc; lazymatch type of Hc with ?T => change (ce_hide T) in Hc end end;
      ce_run; ce_br;
      [ (* neither length: not passed on *)
        lazymatch goal with Hc : branch_taken BC_NE _ _ = true, UC : U _ _ = Z.of_nat _ |- _ =>
          rewrite (ce_br_ne _ _ _ 7 UC) in Hc; apply negb_true_iff, Z.eqb_neq in Hc; change (zcanon 7) with 7 in Hc; lazymatch type of Hc with ?T => change (ce_hide T) in Hc end end;
        (assert (HQN : q <> 0 \/ nc <> 0) by (right; lia);
assert (HPO : nc <= 0 \/ fn0 <> 5 \/ passed_on_m v = false)
  by (right; right; apply ce_po_false; [assumption | assumption | intros C | intros C];
      first [assumption | exfalso; unfold ce_hide in *; lia]);
(let HAOK := fresh "HAOK" in
assert (HAOK : ce_box (ca_aok v (Z.min t 64 - 1))) by (constructor; apply (ce_arity t v q nc fn0 Har ltac:(lia) HQN HPO));
(* lia sees every hypothesis: drop the disjunctions before the runs *)
clear HQN HPO;
ce_run; ce_br;
[ lazymatch goal with Hc : branch_taken BC_LT _ _ = true |- _ =>
    rewrite (ce_lt_atom _ 33 t 64 (eq_trans (ce_ew_agree 40 E0 _ 33 HAG ltac:(lia)) F33) ltac:(lia) ltac:(lia)) in Hc;
    apply Z.ltb_lt in Hc end;
  ce_run; (lazymatch goal with HS : st_ok_pi _ _ ?E ?ss (restrict _ ?ms), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
HAG : env_agree 40 ?E0 ?E, HK : ce_kept _ _ _ _ |- SRr _ _ (mkCfg _ ?mdx) _ =>
pmkst HS;
refine (HSCAN (ms_regs ms) (ms_mem ms) mdx _);
apply (ce_close E ss ms ly St W regs mem md mdx E0 (ce_extra t q nc fn0 ww p0) p0 v (Z.min t 64) HS ltac:(assumption)
  HAG EL32 F32 F38 HOBJ ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity));
[ let e := eval vm_compute in (sr_get (ss_regs ss) (19%bv : bv 5)) in change (sr_get (ss_regs ss) (19%bv : bv 5)) with e; (cbn [sv_denot]; rewrite (ce_ew_agree 40 E0 _ 33 HAG) by lia; rewrite F33, unsigned_lit_small by lia;
  replace (Z.min t 64) with (t + 0) by lia; reflexivity)
| lia | exact HJ | exact Hra | exact Hgp | exact Htp | exact HRO | exact HROK | exact HCE | exact Hsp46 | exact HK
| exact RP0 | exact (ce_unbox _ HAOK) | exact RNAMES ] end)
| lazymatch goal with Hc : branch_taken BC_LT _ _ = false |- _ =>
    rewrite (ce_lt_atom _ 33 t 64 (eq_trans (ce_ew_agree 40 E0 _ 33 HAG ltac:(lia)) F33) ltac:(lia) ltac:(lia)) in Hc;
    apply Z.ltb_ge in Hc end;
  ce_run; (lazymatch goal with HS : st_ok_pi _ _ ?E ?ss (restrict _ ?ms), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
HAG : env_agree 40 ?E0 ?E, HK : ce_kept _ _ _ _ |- SRr _ _ (mkCfg _ ?mdx) _ =>
pmkst HS;
refine (HSCAN (ms_regs ms) (ms_mem ms) mdx _);
apply (ce_close E ss ms ly St W regs mem md mdx E0 (ce_extra t q nc fn0 ww p0) p0 v (Z.min t 64) HS ltac:(assumption)
  HAG EL32 F32 F38 HOBJ ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity));
[ let e := eval vm_compute in (sr_get (ss_regs ss) (19%bv : bv 5)) in change (sr_get (ss_regs ss) (19%bv : bv 5)) with e; (cbn [sv_denot]; replace (Z.min t 64) with 64 by lia; reflexivity)
| lia | exact HJ | exact Hra | exact Hgp | exact Htp | exact HRO | exact HROK | exact HCE | exact Hsp46 | exact HK
| exact RP0 | exact (ce_unbox _ HAOK) | exact RNAMES ] end) ]))
      | (* the length is 7: strncmp(v, "connect %s %s", 7) *)
        lazymatch goal with Hc : branch_taken BC_NE _ _ = false, UC : U _ _ = Z.of_nat _ |- _ =>
          rewrite (ce_br_ne _ _ _ 7 UC) in Hc; apply negb_false_iff, Z.eqb_eq in Hc; change (zcanon 7) with 7 in Hc end;
        ce_run; (lazymatch goal with HS : st_ok _ ?E _ (restrict _ ?ms), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, HK : ce_kept _ _ _ _ |- _ =>
let Ra0 := fresh "Ra0" in let Ra1 := fresh "Ra1" in let Ra2 := fresh "Ra2" in let Rra := fresh "Rra" in
let Qsp := fresh "Qsp" in let Qgp := fresh "Qgp" in let Qtp := fresh "Qtp" in
prreg HS (10%bv : bv 5) Ra0; prreg HS (11%bv : bv 5) Ra1; prreg HS (12%bv : bv 5) Ra2; prreg HS (1%bv : bv 5) Rra;
prreg HS (2%bv : bv 5) Qsp; prreg HS (3%bv : bv 5) Qgp; prreg HS (4%bv : bv 5) Qtp;
pmkst HS;
eapply SRr_bind;
[ apply (ce_strncmp_at ly St W (spZ regs) mem md ms _ p0 v 0x211c0 ce_s16 7 3764 HJ HRO HCE HK);
  [ (rewrite Ra0; first [rewrite F38 | rewrite (ce_ew_agree 40 E0 _ 38 HAG) by lia; rewrite F38]; reflexivity) | (rewrite Ra1, (ce_img_atom E0 257%nat HEIE0 ltac:(cbv; lia)); change 257%nat with (A_OBJ 16%nat); rewrite V16; reflexivity) | rewrite Ra2; reflexivity | lia | (unfold spZ at 1; rewrite Qsp; first [rewrite Usp0 | rewrite (ce_ew_agree 40 E0 _ 2 HAG) by lia; rewrite Usp0];
    rewrite unsigned_lit_small by lia; lia) | (rewrite Qgp; first [rewrite F3 | rewrite (ce_ew_agree 40 E0 _ 3 HAG) by lia; rewrite F3]; exact Hgp) | (rewrite Qtp; first [rewrite F4 | rewrite (ce_ew_agree 40 E0 _ 4 HAG) by lia; rewrite F4]; exact Htp)
  | exact Rra | lia | reflexivity | exact RP0 | exact R16 ]
| ];
clear Ra0 Ra1 Ra2 Rra Qsp Qgp Qtp; cbv beta;
let W2 := fresh "W2" in let c2 := fresh "c2" in let regs2 := fresh "regs" in let mem2 := fresh "mem" in
let md2 := fresh "md" in let HJ2 := fresh "HJ" in let HP2 := fresh "HP" in let Hcmp := fresh "Hcmp" in
let HK2 := fresh "HK" in let Hfr2 := fresh "Hfr" in
intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hcmp & HK2 & Hfr2);
((* HJ and HK are the caller's (bound before the intros): a fresh match would take the new ones *)
lazymatch goal with HS : st_ok _ ?E _ _, SHOK : sh_ok _ _ _ _ _, HAG : env_agree 40 ?E0 ?E |- _ =>
let HS2 := fresh "HS" in
jafter_call_keep_pi HS 88%nat regs2 (mrestrict (w_H W) mem2) HP2 [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10]%nat HS2;
ce_kept_regions HS2 Hfr2 HJ2;
clear HS SHOK HK HJ; rewrite <- restrict_mkst_fx in HS2;
let HEIx := fresh "HEI" in let HAGx := fresh "HAG" in let SH := fresh "SHOK" in let UA := fresh "UA" in
assert (HEIx : img_env VAL A_LIM (havoc E 88%nat (map (getr regs2) CLOB)))
  by (apply img_env_havoc; [assumption | apply Nat.leb_le; vm_compute; reflexivity]);
assert (HAGx : env_agree 40 E0 (havoc E 88%nat (map (getr regs2) CLOB))) by (apply env_agree_havoc_ge; [lia | exact HAG]);
clear HAG;
assert (SH : sh_ok SEGS CBx (ce_SH true) (havoc E 88%nat (map (getr regs2) CLOB)) (mrestrict (w_H W) mem2))
  by (apply (ce_shok true ly St W mem2 md2 _ wp ww (proj1 HJ2));
      [ rewrite (ce_ew_agree 40 E0 _ 32 HAGx) by lia; exact F32 | rewrite (ce_ew_agree 40 E0 _ 10 HAGx) by lia; exact F10
      | rewrite (ce_ew_agree 40 E0 _ 37 HAGx) by lia; exact F37 | lia | lia | lia | intros _; split; [exact HWW | lia]]);
pose proof (ce_U_w _ _ _ (ce_havoc_a0 E 88%nat regs2)) as UA; cbn [Nat.add] in UA;
rename HS2 into HS; rename HK2 into HK; rename HJ2 into HJ; rename HAGx into HAG; rename SH into SHOK
end)
end);
        ce_run; ce_br;
        [ ce_run; ce_leaf
        | let H16 := fresh "H16" in
          assert (H16 : firstn 7 v <> ce_k16)
            by ce_ne0 ltac:(fun H => apply (ce_strncmp16 v HNUL) in H);
          (assert (HQN : q <> 0 \/ nc <> 0) by (right; lia);
assert (HPO : nc <= 0 \/ fn0 <> 5 \/ passed_on_m v = false)
  by (right; right; apply ce_po_false; [assumption | assumption | intros C | intros C];
      first [assumption | exfalso; unfold ce_hide in *; lia]);
(let HAOK := fresh "HAOK" in
assert (HAOK : ce_box (ca_aok v (Z.min t 64 - 1))) by (constructor; apply (ce_arity t v q nc fn0 Har ltac:(lia) HQN HPO));
(* lia sees every hypothesis: drop the disjunctions before the runs *)
clear HQN HPO;
ce_run; ce_br;
[ lazymatch goal with Hc : branch_taken BC_LT _ _ = true |- _ =>
    rewrite (ce_lt_atom _ 33 t 64 (eq_trans (ce_ew_agree 40 E0 _ 33 HAG ltac:(lia)) F33) ltac:(lia) ltac:(lia)) in Hc;
    apply Z.ltb_lt in Hc end;
  ce_run; (lazymatch goal with HS : st_ok_pi _ _ ?E ?ss (restrict _ ?ms), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
HAG : env_agree 40 ?E0 ?E, HK : ce_kept _ _ _ _ |- SRr _ _ (mkCfg _ ?mdx) _ =>
pmkst HS;
refine (HSCAN (ms_regs ms) (ms_mem ms) mdx _);
apply (ce_close E ss ms ly St W regs mem md mdx E0 (ce_extra t q nc fn0 ww p0) p0 v (Z.min t 64) HS ltac:(assumption)
  HAG EL32 F32 F38 HOBJ ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity));
[ let e := eval vm_compute in (sr_get (ss_regs ss) (19%bv : bv 5)) in change (sr_get (ss_regs ss) (19%bv : bv 5)) with e; (cbn [sv_denot]; rewrite (ce_ew_agree 40 E0 _ 33 HAG) by lia; rewrite F33, unsigned_lit_small by lia;
  replace (Z.min t 64) with (t + 0) by lia; reflexivity)
| lia | exact HJ | exact Hra | exact Hgp | exact Htp | exact HRO | exact HROK | exact HCE | exact Hsp46 | exact HK
| exact RP0 | exact (ce_unbox _ HAOK) | exact RNAMES ] end)
| lazymatch goal with Hc : branch_taken BC_LT _ _ = false |- _ =>
    rewrite (ce_lt_atom _ 33 t 64 (eq_trans (ce_ew_agree 40 E0 _ 33 HAG ltac:(lia)) F33) ltac:(lia) ltac:(lia)) in Hc;
    apply Z.ltb_ge in Hc end;
  ce_run; (lazymatch goal with HS : st_ok_pi _ _ ?E ?ss (restrict _ ?ms), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
HAG : env_agree 40 ?E0 ?E, HK : ce_kept _ _ _ _ |- SRr _ _ (mkCfg _ ?mdx) _ =>
pmkst HS;
refine (HSCAN (ms_regs ms) (ms_mem ms) mdx _);
apply (ce_close E ss ms ly St W regs mem md mdx E0 (ce_extra t q nc fn0 ww p0) p0 v (Z.min t 64) HS ltac:(assumption)
  HAG EL32 F32 F38 HOBJ ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity));
[ let e := eval vm_compute in (sr_get (ss_regs ss) (19%bv : bv 5)) in change (sr_get (ss_regs ss) (19%bv : bv 5)) with e; (cbn [sv_denot]; replace (Z.min t 64) with 64 by lia; reflexivity)
| lia | exact HJ | exact Hra | exact Hgp | exact Htp | exact HRO | exact HROK | exact HCE | exact Hsp46 | exact HK
| exact RP0 | exact (ce_unbox _ HAOK) | exact RNAMES ] end) ])) ] ] ] ] ]).
- (* no recorded call *)
  ce_run; ce_br.
  + (* q = 0: the daemon did not act, return *) ce_run; ce_leaf.
  +     assert (HQN : q <> 0 \/ nc <> 0)
      by (left; intro Hq0; subst q;
          lazymatch goal with Hc : branch_taken BC_EQ _ _ = false |- _ =>
            rewrite branch_eq_U, U_SExt, U_SOff, (ce_ew_agree 40 E0 _ 34 HAG ltac:(lia)), F34, U_SLit in Hc;
            vm_compute in Hc; discriminate Hc end);
    assert (HPO : nc <= 0 \/ fn0 <> 5 \/ passed_on_m v = false) by (left; lia);
    (let HAOK := fresh "HAOK" in
assert (HAOK : ce_box (ca_aok v (Z.min t 64 - 1))) by (constructor; apply (ce_arity t v q nc fn0 Har ltac:(lia) HQN HPO));
(* lia sees every hypothesis: drop the disjunctions before the runs *)
clear HQN HPO;
ce_run; ce_br;
[ lazymatch goal with Hc : branch_taken BC_LT _ _ = true |- _ =>
    rewrite (ce_lt_atom _ 33 t 64 (eq_trans (ce_ew_agree 40 E0 _ 33 HAG ltac:(lia)) F33) ltac:(lia) ltac:(lia)) in Hc;
    apply Z.ltb_lt in Hc end;
  ce_run; (lazymatch goal with HS : st_ok_pi _ _ ?E ?ss (restrict _ ?ms), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
HAG : env_agree 40 ?E0 ?E, HK : ce_kept _ _ _ _ |- SRr _ _ (mkCfg _ ?mdx) _ =>
pmkst HS;
refine (HSCAN (ms_regs ms) (ms_mem ms) mdx _);
apply (ce_close E ss ms ly St W regs mem md mdx E0 (ce_extra t q nc fn0 ww p0) p0 v (Z.min t 64) HS ltac:(assumption)
  HAG EL32 F32 F38 HOBJ ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity));
[ let e := eval vm_compute in (sr_get (ss_regs ss) (19%bv : bv 5)) in change (sr_get (ss_regs ss) (19%bv : bv 5)) with e; (cbn [sv_denot]; rewrite (ce_ew_agree 40 E0 _ 33 HAG) by lia; rewrite F33, unsigned_lit_small by lia;
  replace (Z.min t 64) with (t + 0) by lia; reflexivity)
| lia | exact HJ | exact Hra | exact Hgp | exact Htp | exact HRO | exact HROK | exact HCE | exact Hsp46 | exact HK
| exact RP0 | exact (ce_unbox _ HAOK) | exact RNAMES ] end)
| lazymatch goal with Hc : branch_taken BC_LT _ _ = false |- _ =>
    rewrite (ce_lt_atom _ 33 t 64 (eq_trans (ce_ew_agree 40 E0 _ 33 HAG ltac:(lia)) F33) ltac:(lia) ltac:(lia)) in Hc;
    apply Z.ltb_ge in Hc end;
  ce_run; (lazymatch goal with HS : st_ok_pi _ _ ?E ?ss (restrict _ ?ms), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
HAG : env_agree 40 ?E0 ?E, HK : ce_kept _ _ _ _ |- SRr _ _ (mkCfg _ ?mdx) _ =>
pmkst HS;
refine (HSCAN (ms_regs ms) (ms_mem ms) mdx _);
apply (ce_close E ss ms ly St W regs mem md mdx E0 (ce_extra t q nc fn0 ww p0) p0 v (Z.min t 64) HS ltac:(assumption)
  HAG EL32 F32 F38 HOBJ ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity));
[ let e := eval vm_compute in (sr_get (ss_regs ss) (19%bv : bv 5)) in change (sr_get (ss_regs ss) (19%bv : bv 5)) with e; (cbn [sv_denot]; replace (Z.min t 64) with 64 by lia; reflexivity)
| lia | exact HJ | exact Hra | exact Hgp | exact Htp | exact HRO | exact HROK | exact HCE | exact Hsp46 | exact HK
| exact RP0 | exact (ce_unbox _ HAOK) | exact RNAMES ] end) ]).
Qed.

(** ** The scan of g_parsed: one concrete run per pass k, from a fresh seed (as check_arity_s3.v's ca_seed) *)
Definition ca_lregs (k : nat) : list sv :=
sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set sr_atoms
 18 (SLit SHADOW_OFF)) 19 (SOff 32 0)) 20 (SLit (24 * Z.of_nat k)))
 21 (SLit (zcanon (- SHADOW_OFF - 3 * Z.of_nat k)))) 22 (SLit CA_GP))
 23 (SLit (SHADOW_OFF + CA_GP / 8 + 3 * Z.of_nat k))) 24 (SLit 528).
Definition ca_lss (k : nat) : sstate := mkSS CE_LOOP (ca_lregs k) [ca_frame; ca_gparsed; ca_gpsh] None (ca_facts 0 63).

Lemma ca_lseed : forall (k : nat) ly St (W : world SEGS) regs0 mem0 md0 p0 v s3v regs memc mdc,
ca_lpre k ly St W regs0 mem0 md0 p0 v s3v regs memc mdc ->
st_ok_pi SEGS VAL (Eimg (Ereg regs (ca_extra s3v regs0))) (ca_lss k)
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + CE_LOOP)) memc (seg_rom SEGS))).
Proof.
intros k ly St W regs0 mem0 md0 p0 v s3v regs memc mdc HP.
destruct HP as (HJ & Hra & Hgp0 & Htp0 & HRO & HROK & HCE & Hsp46 & HK & Hsp & HFR & R3 & R4 & R8 & R18 & R19 & R20 & R21
  & R22 & R23 & R24 & Hs3 & _).
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _ & _).
pose proof Hstk as (Hal16 & _ & Hceil & Hslo & Hshi & H47 & _).
pose proof (ce_ro_kept W mem0 memc (spZ regs0) HROK HK HCE) as [HROB _].
pose proof asan_consts as (C1 & _).
assert (WS : CHECK_ARITY_STK = 8336) by reflexivity.
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs (ca_extra s3v regs0))).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r).
{ intros n r Hn. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  subst E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
assert (EX : forall j, (j < 14)%nat -> ew E (32 + j) = nth j (ca_extra s3v regs0) (Z_to_bv 64 0)).
{ intros j Hj. subst E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. }
assert (E32 : ew E 32 = Z_to_bv 64 s3v) by exact (EX 0%nat ltac:(lia)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
assert (U32 : bv_unsigned (ew E 32) = s3v) by (rewrite E32; apply unsigned_lit_small; lia).
unfold ca_lss. apply pa_entry_st_ok_full.
- apply regs_ok_by_cases. intros r Hr. cbv [YP01.all_regs In] in Hr.
  repeat (destruct Hr as [<- | Hr];
   [ lazymatch goal with |- getr _ ?rr = sv_denot _ (sr_get ?a ?rr) =>
       let vv := eval cbv -[Z.mul Z.add Z.sub Z.opp Z.div zcanon Z.of_nat CA_GP SHADOW_OFF] in (sr_get a rr) in
       change (sr_get a rr) with vv end;
     cbn [sv_denot];
     first [ exact R18 | exact R20 | exact R21 | exact R22 | exact R23 | exact R24 | apply getr_zero
           | rewrite Z.add_0_r, Z_to_bv_bv_unsigned;
             first [ rewrite E32; exact R19 | symmetry; apply EE; reflexivity ] ]
   | ]); try (destruct Hr; fail).
- vm_compute. reflexivity.
- repeat apply Forall_cons; [ | | | apply Forall_nil ]; unfold region_ok.
  + unfold ca_frame. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Usp.
    split; [lia|]. split; [lia|]. split.
    { intros o Ho. apply (apresent_writable SEGS). apply Hpres. unfold CHECK_ARITY_STK, ESTACK. lia. }
    rewrite Forall_map. apply Forall_forall. intros j Hj. apply in_seq in Hj.
    apply (YI04.chunk_ok_val SEGS E _ (spZ regs) (136 - 8 * Z.of_nat j) 8 (SOff (33 + j) 0)
      (bv_unsigned (nth j (ca_sv regs0) (Z_to_bv 64 0)))).
    * cbn [sv_denot]. replace (33 + j)%nat with (32 + (1 + j))%nat by lia. rewrite (EX (1 + j)%nat ltac:(lia)).
      cbn [ca_extra nth Nat.add]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
    * pose proof (bv_unsigned_in_range 64 (nth j (ca_sv regs0) (Z_to_bv 64 0))) as HR.
      change (bv_modulus 64) with (2 ^ 64) in HR. change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
    * cbn. lia.
    * replace (spZ regs + (136 - 8 * Z.of_nat j)) with (spZ regs + 136 - 8 * Z.of_nat j) by lia. apply HFR. lia.
  + unfold ca_gparsed. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    split; [unfold CA_GP; lia|]. split; [unfold CA_GP; lia|]. split; [intros o Ho; lia|].
    apply ca_wchunks_ok. apply (ca_bytes_mbyte W memc CA_GP RO_g_parsed (ca_ro_gp _ HROB)).
  + unfold ca_gpsh. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    split; [unfold SHADOW_OFF; lia|]. split; [unfold SHADOW_OFF; lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor]. apply YI04.chunk_ok_zero. intros i Hi.
    rewrite Z.add_0_l. exact (ca_gpsh_mbyte B HB ly St W memc mdc HAR i Hi).
- apply pairwise_disjoint_of_extents. unfold ca_frame, ca_gparsed, ca_gpsh, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Usp.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  unfold CA_GP, SHADOW_OFF. repeat split; lia.
- split; [|split; exact I]. cbn [ca_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite Usp, U32.
  refine (conj (conj _ (conj _ _)) (conj (conj _ (conj _ _)) I)).
  + lia.
  + change (2 ^ 4) with 16. rewrite Hsp. replace (spZ regs0 - 144) with (spZ regs0 + (-9) * 16) by lia.
    rewrite Z_mod_plus_full. exact Hal16.
  + lia.
  + lia.
  + rewrite Z.pow_0_r, Z.mod_1_r. reflexivity.
  + lia.
Qed.

(* the frame keeps the saved registers through a run of the scan (write window [sp, sp + 8)) and through a call *)
Lemma ce_frame_run : forall E rs (W : world SEGS) m m' sp regs0,
frame_of E rs (mrestrict (w_H W) m) (mrestrict (w_H W) m') -> ce_wr 0 40 rs = true -> bv_unsigned (ew E 2) = sp ->
0 <= sp -> sp + 144 < 2 ^ 64 -> ca_frame_at W m sp regs0 -> ca_frame_at W m' sp regs0.
Proof.
intros E rs W m m' sp regs0 Hf Hw Hsp H0 H1 HF. apply (ce_frame_keep W m m' sp regs0 HF). intros a Ha.
apply (ce_aview_frame E rs (w_H W) m m' a Hf); [lia|]. apply (ce_not_wrange E rs 0 40 a Hw). lia.
Qed.
Lemma ce_frame_call : forall (W : world SEGS) m m' sp regs0 lo hi, ca_frame_at W m sp regs0 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> ~ False -> aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a) ->
hi <= sp + 40 -> 0 <= sp -> sp + 144 < 2 ^ 64 -> ca_frame_at W m' sp regs0.
Proof.
intros W m m' sp regs0 lo hi HF Hf Hhi H0 H1. apply (ce_frame_keep W m m' sp regs0 HF). intros a Ha.
apply Hf; [lia | lia | tauto].
Qed.

(* the matched row: the state at 0x87478 is check_arity_s3.v's ca_row_pre *)
Definition ca_rowregs_ok (k : nat) (sr : list sv) : bool :=
sv_eqb (sr_get sr 2) (SOff 2 0) && sv_eqb (sr_get sr 3) (SOff 3 0) && sv_eqb (sr_get sr 4) (SOff 4 0) &&
sv_eqb (sr_get sr 9) (SLit (CA_GP + 24 * Z.of_nat k)) && sv_eqb (sr_get sr 18) (SLit SHADOW_OFF) &&
sv_eqb (sr_get sr 19) (SOff 32 0) && sv_eqb (sr_get sr 21) (SLit (zcanon (- SHADOW_OFF - 3 * Z.of_nat k))) &&
sv_eqb (sr_get sr 22) (SLit CA_GP).
Lemma ca_close_row : forall k mn mx E ss ms ly St W regs0 mem0 md0 mdc s3v (regs : bvmap 5 word),
st_ok_pi SEGS VAL E ss (restrict (w_H W) ms) ->
(forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (ca_extra s3v regs0)) n) ->
ca_rowregs_ok k (ss_regs ss) = true ->
ajournal SEGS B CHECK_ARITY_STK (spZ regs0) [] ly St W mem0 md0 [] ly St W (ms_mem ms) mdc 0 ->
YK0s.ret_ok (getr regs0 1) -> cmd_ro_ok (rdW W (ms_mem ms)) ->
spZ regs = spZ regs0 - 144 -> ca_frame_at W (ms_mem ms) (spZ regs) regs0 ->
getr regs 3 = getr regs0 3 -> getr regs 4 = getr regs0 4 ->
mn <= s3v - 1 <= mx -> 1 <= s3v <= 64 ->
ca_row_pre B k mn mx ly St W regs0 mem0 md0 W (ms_regs ms) (ms_mem ms) mdc s3v.
Proof.
intros k mn mx E ss ms ly St W regs0 mem0 md0 mdc s3v regs HS EA Hh HJ Hra HRO Hsp HFR R3 R4 Hmm Hs63.
assert (GR : forall r, getr (ms_regs ms) r = sv_denot E (sr_get (ss_regs ss) r))
by (intros r; exact (st_ok_pi_restrict_reg (w_H W) E ss ms r HS)).
unfold ca_rowregs_ok in Hh. repeat rewrite andb_true_iff in Hh.
destruct Hh as (((((((H2 & H3) & H4) & H9) & H18) & H19) & H21) & H22).
apply sv_eqb_eq in H2, H3, H4, H9, H18, H19, H21, H22.
assert (ER : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r).
{ intros n r Hn. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite (EA n ltac:(unfold A_TEXT; lia)). apply ew_Ereg_nat. exact Hn. }
assert (E32 : ew E 32 = Z_to_bv 64 s3v) by (rewrite (EA 32%nat ltac:(unfold A_TEXT; lia)); exact (ew_Ereg_extra regs _ 0)).
assert (SP : spZ (ms_regs ms) = spZ regs).
{ unfold spZ at 1. rewrite GR, H2. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (ER 2%nat 2%bv eq_refl). reflexivity. }
unfold ca_row_pre.
split; [exact HJ|]. split; [exact Hra|]. split; [exact HRO|]. split; [rewrite SP; exact Hsp|].
split; [rewrite SP; exact HFR|].
split; [rewrite GR, H3; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (ER 3%nat 3%bv eq_refl); exact R3|].
split; [rewrite GR, H4; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (ER 4%nat 4%bv eq_refl); exact R4|].
split; [rewrite GR, H9; reflexivity|].
split; [rewrite GR, H18; reflexivity|].
split; [rewrite GR, H19; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, E32; reflexivity|].
split; [rewrite GR, H21; reflexivity|].
split; [rewrite GR, H22; reflexivity|].
split; [exact Hmm | exact Hs63].
Qed.

(* no match at row k: the state at 0x87448 is ca_lpre (k + 1) *)
Definition ca_nextregs_ok (k : nat) (sr : list sv) : bool :=
sv_eqb (sr_get sr 2) (SOff 2 0) && sv_eqb (sr_get sr 3) (SOff 3 0) && sv_eqb (sr_get sr 4) (SOff 4 0) &&
sv_eqb (sr_get sr 8) (SOff 8 0) && sv_eqb (sr_get sr 18) (SLit SHADOW_OFF) && sv_eqb (sr_get sr 19) (SOff 32 0) &&
sv_eqb (sr_get sr 20) (SLit (24 * Z.of_nat (Nat.succ k))) &&
sv_eqb (sr_get sr 21) (SLit (zcanon (- SHADOW_OFF - 3 * Z.of_nat (Nat.succ k)))) &&
sv_eqb (sr_get sr 22) (SLit CA_GP) && sv_eqb (sr_get sr 23) (SLit (SHADOW_OFF + CA_GP / 8 + 3 * Z.of_nat (Nat.succ k))) &&
sv_eqb (sr_get sr 24) (SLit 528).
Lemma ca_close_next : forall k E ss ms ly St W regs0 mem0 md0 mdc p0 v s3v (regs : bvmap 5 word),
st_ok_pi SEGS VAL E ss (restrict (w_H W) ms) ->
(forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (ca_extra s3v regs0)) n) ->
ca_nextregs_ok k (ss_regs ss) = true ->
ajournal SEGS B CHECK_ARITY_STK (spZ regs0) [] ly St W mem0 md0 [] ly St W (ms_mem ms) mdc 0 ->
YK0s.ret_ok (getr regs0 1) -> getr regs0 3 = w64 (as_gp B) -> getr regs0 4 = w64 (as_tp B) ->
arodata_okP SEGS RLO RHI B (rdW W mem0) -> cmd_ro_ok (rdW W mem0) ->
alloc_ceiling <= spZ regs0 - CHECK_ARITY_STK -> 2 ^ 46 <= spZ regs0 <= 2 ^ 47 ->
ce_kept W mem0 (ms_mem ms) (spZ regs0) ->
spZ regs = spZ regs0 - 144 -> ca_frame_at W (ms_mem ms) (spZ regs) regs0 ->
getr regs 3 = getr regs0 3 -> getr regs 4 = getr regs0 4 -> getr regs 8 = w64 p0 ->
1 <= s3v <= 64 -> ce_ready W mem0 p0 v -> ca_aok v (s3v - 1) ->
(forall j, (j < 22)%nat -> ce_ready W mem0 (ca_name_addr j) (ca_nm j)) ->
ca_lpre (Nat.succ k) ly St W regs0 mem0 md0 p0 v s3v (ms_regs ms) (ms_mem ms) mdc.
Proof.
intros k E ss ms ly St W regs0 mem0 md0 mdc p0 v s3v regs HS EA Hh HJ Hra Hgp0 Htp0 HRO HROK HCE Hsp46 HK Hsp HFR R3 R4 R8
  Hs3 RP HA RN.
assert (GR : forall r, getr (ms_regs ms) r = sv_denot E (sr_get (ss_regs ss) r))
by (intros r; exact (st_ok_pi_restrict_reg (w_H W) E ss ms r HS)).
unfold ca_nextregs_ok in Hh. repeat rewrite andb_true_iff in Hh.
destruct Hh as ((((((((((H2 & H3) & H4) & H8) & H18) & H19) & H20) & H21) & H22) & H23) & H24).
apply sv_eqb_eq in H2, H3, H4, H8, H18, H19, H20, H21, H22, H23, H24.
assert (ER : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r).
{ intros n r Hn. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite (EA n ltac:(unfold A_TEXT; lia)). apply ew_Ereg_nat. exact Hn. }
assert (E32 : ew E 32 = Z_to_bv 64 s3v) by (rewrite (EA 32%nat ltac:(unfold A_TEXT; lia)); exact (ew_Ereg_extra regs _ 0)).
assert (SP : spZ (ms_regs ms) = spZ regs).
{ unfold spZ at 1. rewrite GR, H2. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (ER 2%nat 2%bv eq_refl). reflexivity. }
unfold ca_lpre.
split; [exact HJ|]. split; [exact Hra|]. split; [exact Hgp0|]. split; [exact Htp0|]. split; [exact HRO|].
split; [exact HROK|]. split; [exact HCE|]. split; [exact Hsp46|]. split; [exact HK|].
split; [rewrite SP; exact Hsp|]. split; [rewrite SP; exact HFR|].
split; [rewrite GR, H3; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (ER 3%nat 3%bv eq_refl); exact R3|].
split; [rewrite GR, H4; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (ER 4%nat 4%bv eq_refl); exact R4|].
split; [rewrite GR, H8; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (ER 8%nat 8%bv eq_refl); exact R8|].
split; [rewrite GR, H18; reflexivity|].
split; [rewrite GR, H19; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, E32; reflexivity|].
split; [rewrite GR, H20; reflexivity|].
split; [rewrite GR, H21; reflexivity|].
split; [rewrite GR, H22; reflexivity|].
split; [rewrite GR, H23; reflexivity|].
split; [rewrite GR, H24; reflexivity|].
split; [exact Hs3|]. split; [exact RP|]. split; [exact HA | exact RN].
Qed.

(* the rows' arity pairs, as row_find gives them for each row's own name (check_arity_s0.v's ca_find_k) *)
Definition ca_ar (k : nat) : Z * Z := nth k [(2, 4); (0, 0); (1, 1); (0, 1); (1, 1); (2, 2); (2, 2); (3, 3); (3, 4); (1, 1);
  (2, 2); (1, 1); (1, 1); (2, 2); (2, UNB); (1, 1); (1, 1); (1, 1); (1, 1); (2, 2); (2, 2); (0, 0)] (0, 0).
Lemma ca_find_all : forall k, (k < 22)%nat -> row_find (ca_nm k) parsed_rows = Some (ca_ar k).
Proof. intros k Hk. do 22 (destruct k as [|k]; [vm_compute; reflexivity|]). lia. Qed.

(* the row lemmas' shape (check_arity_s4.v's ca_row_1 with the gp / tp facts of check_arity_r3.v's ca_row_3) *)
Definition ca_row_ok (k : nat) (mn mx : Z) : Prop :=
forall ly St W0 regs0 mem0 md0 W regs memc mdc s3v,
ca_row_pre B k mn mx ly St W0 regs0 mem0 md0 W regs memc mdc s3v ->
getr regs0 3 = w64 (as_gp B) -> getr regs0 4 = w64 (as_tp B) ->
SRr SEGS W (cfg_at SEGS (BASE + CA_SEG) regs memc mdc) (ca_post B regs0 ly St W0 mem0 md0).
Definition ca_iter_stmt (k : nat) : Prop :=
ca_row_ok k (fst (ca_ar k)) (snd (ca_ar k)) ->
forall ly St W regs0 mem0 md0 p0 v s3v regs memc mdc,
ca_lpre k ly St W regs0 mem0 md0 p0 v s3v regs memc mdc ->
((Nat.succ k < 22)%nat -> forall regs' memc' mdc', ca_lpre (Nat.succ k) ly St W regs0 mem0 md0 p0 v s3v regs' memc' mdc' ->
  SRr SEGS W (cfg_at SEGS (BASE + CE_LOOP) regs' memc' mdc') (ca_post B regs0 ly St W mem0 md0)) ->
SRr SEGS W (cfg_at SEGS (BASE + CE_LOOP) regs memc mdc) (ca_post B regs0 ly St W mem0 md0).

Let RUNP := SRr_run_pi_AJ (L := cmd_listing) B LAWS.
Let RUNC := SRr_run_pi_AJ_call (L := cmd_listing) B LAWS.
Let RUNTOP := SRr_run_to_pi_AJ (L := cmd_listing) B LAWS.

Ltac cl_awr := lazymatch goal with |- awr_ok _ _ ?E ?rs _ _ _ _ _ _ _ _ =>
apply ca_awr_sh; [vm_compute; reflexivity |
  lazymatch goal with Usp : bv_unsigned (ew E 2) = _, Hsp : spZ _ = _ |- _ => rewrite Usp, Hsp; lia end] end.
Ltac cl_keep_run := lazymatch goal with
| HK : ce_kept ?W ?mem0 ?m0 ?sp0, HFR : ca_frame_at ?W ?m0 ?sp ?r0,
  HFr : frame_of ?E ?rs (mrestrict _ _) (mrestrict _ ?m1), Usp : bv_unsigned (ew ?E 2) = _ |- _ =>
  let HK2 := fresh "HK" in let HFR2 := fresh "HFR" in
  pose proof (ce_kept_run W mem0 m0 m1 E rs sp0 0 40 HK HFr ltac:(vm_compute; reflexivity)
    ltac:(rewrite Usp; unfold CHECK_ARITY_STK, ESTACK; lia) ltac:(rewrite Usp; lia)) as HK2;
  pose proof (ce_frame_run E rs W m0 m1 sp r0 HFr ltac:(vm_compute; reflexivity) ltac:(rewrite Usp; lia) ltac:(lia) ltac:(lia)
    HFR) as HFR2;
  clear HK HFR HFr; rename HK2 into HK; rename HFR2 into HFR end;
repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.

Lemma ca_iter_0 : ca_iter_stmt 0.
Proof.
unfold ca_iter_stmt.
intros ROW ly St W regs0 mem0 md0 p0 v s3v regs memc mdc HP NEXT.
pose proof (ca_lseed 0%nat ly St W regs0 mem0 md0 p0 v s3v regs memc mdc HP) as HS.
destruct HP as (HJ & Hra & Hgp0 & Htp0 & HRO & HROK & HCE & Hsp46 & HK & Hsp & HFR & R3 & R4 & R8 & R18 & R19 & R20 & R21
  & R22 & R23 & R24 & Hs3 & RP0 & HAOK & RNAMES).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hes : ESTACK = 4096) by reflexivity.
unfold cfg_at. change (w64 (BASE + CE_LOOP)) with (Z_to_bv 64 (BASE + CE_LOOP)).
set (E := Eimg (Ereg regs (ca_extra s3v regs0))) in HS.
assert (HEI : img_env VAL A_LIM E) by apply Eimg_env.
assert (EA : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (ca_extra s3v regs0)) n)
  by (intros n Hn; apply Eimg_low; exact Hn).
assert (Usp : bv_unsigned (ew E 2) = spZ regs)
  by (rewrite (EA 2%nat ltac:(unfold A_TEXT; lia)), (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
(* the shadow check of row k (zero), its name pointer, the strcmp call *)
paj_run_shc RUNP RUNC HS HJ; [cl_awr |].
cl_keep_run.
(lazymatch goal with HS : st_ok _ ?E _ (restrict _ ?ms), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
  HK : ce_kept _ _ _ _ |- _ =>
let Ra0 := fresh "Ra0" in let Ra1 := fresh "Ra1" in let Rra := fresh "Rra" in
let Qsp := fresh "Qsp" in let Qgp := fresh "Qgp" in let Qtp := fresh "Qtp" in
prreg HS (10%bv : bv 5) Ra0; prreg HS (11%bv : bv 5) Ra1; prreg HS (1%bv : bv 5) Rra;
prreg HS (2%bv : bv 5) Qsp; prreg HS (3%bv : bv 5) Qgp; prreg HS (4%bv : bv 5) Qtp;
pmkst HS;
eapply SRr_bind;
[ apply (ce_strcmp_at ly St W (spZ regs0) mem0 md0 ms _ p0 v (ca_name_addr 0%nat) (ca_nm 0%nat) 3888 HJ HRO HCE HK);
  [ rewrite Ra0, (EA 8%nat ltac:(unfold A_TEXT; lia)), (ew_Ereg_nat regs _ 8 8%bv eq_refl); exact R8
  | rewrite Ra1; apply bv_eq; vm_compute; reflexivity
  | unfold spZ at 1; rewrite Qsp, Usp; exact Hsp
  | rewrite Qgp, (EA 3%nat ltac:(unfold A_TEXT; lia)), (ew_Ereg_nat regs _ 3 3%bv eq_refl), R3; exact Hgp0
  | rewrite Qtp, (EA 4%nat ltac:(unfold A_TEXT; lia)), (ew_Ereg_nat regs _ 4 4%bv eq_refl), R4; exact Htp0
  | exact Rra | lia | reflexivity | exact RP0 | exact (RNAMES 0%nat ltac:(lia)) ]
| ];
clear Ra0 Ra1 Rra Qsp Qgp Qtp; cbv beta;
intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hcmp & HK2 & Hfr2);
let HS2 := fresh "HS" in
jafter_call_keep_hi HS 1024%nat regs2 (mrestrict (w_H W) mem2) HP2 [0; 1; 2]%nat HS2;
ce_kept_regions HS2 Hfr2 HJ2;
rewrite <- restrict_mkst_fx in HS2;
lazymatch goal with HFR : ca_frame_at _ _ _ _ |- _ =>
  let HFR2 := fresh "HFR" in
  pose proof (ce_frame_call W (ms_mem ms) mem2 (spZ regs) regs0 _ _ HFR Hfr2 ltac:(lia) ltac:(lia) ltac:(lia)) as HFR2;
  clear HFR; rename HFR2 into HFR end;
clear HS HJ HK; rename HS2 into HS; rename HJ2 into HJ; rename HK2 into HK;
assert (HEI2 : img_env VAL A_LIM (havoc E 1024 (map (getr regs2) CLOB))) by (apply img_env_havoc_hi; [exact HEI | unfold A_LIM; lia]);
assert (Usp2 : bv_unsigned (ew (havoc E 1024 (map (getr regs2) CLOB)) 2) = spZ regs) by (rewrite ew_havoc_old by lia; exact Usp);
assert (EA2 : forall n, (n < A_TEXT)%nat -> ew (havoc E 1024 (map (getr regs2) CLOB)) n = ew (Ereg regs (ca_extra s3v regs0)) n)
  by (intros n Hn; rewrite ew_havoc_old by (unfold A_TEXT in Hn; lia); apply EA; exact Hn);
pose proof (ce_U_w _ _ _ (ce_havoc_a0 E 1024 regs2)) as UA; cbn [Nat.add] in UA;
clear Usp EA; rename Usp2 into Usp; rename EA2 into EA
end).
(* beqz a0 (0x87460) *)
psrr_branch_pi RUNP BR HS.
- (lazymatch goal with Hc : branch_taken _ _ _ = true, UA : U _ _ = bv_unsigned (getr ?r2 10), Hcmp : getr ?r2 10 = w64 0 <-> _ |- _ =>
  let Hv := fresh "Hv" in
  assert (Hv : v = ca_nm 0%nat) by (apply Hcmp; apply bv_eq; rewrite (ce_br_eq _ _ _ 0 UA) in Hc; apply Z.eqb_eq in Hc;
    rewrite Hc; reflexivity);
  let Hmm := fresh "Hmm" in
  assert (Hmm : fst (ca_ar 0%nat) <= s3v - 1 <= snd (ca_ar 0%nat))
    by (unfold ca_aok in HAOK; rewrite Hv, (ca_find_all 0%nat ltac:(lia)) in HAOK; exact HAOK);
  paj_run_to_shc RUNTOP HS HJ CA_SEG; [cl_awr |]; cl_keep_run;
  lazymatch goal with HS : st_ok_pi _ _ ?E3 ?ss3 (restrict _ ?ms3), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
    HK : ce_kept _ _ _ _, HFR : ca_frame_at _ _ _ _ |- SRr _ _ (mkCfg _ ?md3) _ =>
    pmkst HS;
    refine (ROW ly St W regs0 mem0 md0 W (ms_regs ms3) (ms_mem ms3) md3 s3v _ Hgp0 Htp0);
    exact (ca_close_row 0%nat _ _ E3 ss3 ms3 ly St W regs0 mem0 md0 md3 s3v regs HS EA ltac:(vm_compute; reflexivity) HJ Hra
      (ce_ro_kept W mem0 (ms_mem ms3) (spZ regs0) HROK HK HCE) Hsp HFR R3 R4 Hmm Hs3) end end).
- (paj_run_to_shc RUNTOP HS HJ CE_LOOP; [cl_awr |]; cl_keep_run;
lazymatch goal with HS : st_ok_pi _ _ ?E3 ?ss3 (restrict _ ?ms3), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
  HK : ce_kept _ _ _ _, HFR : ca_frame_at _ _ _ _ |- SRr _ _ (mkCfg _ ?md3) _ =>
  pmkst HS;
  refine (NEXT ltac:(apply Nat.ltb_lt; reflexivity) (ms_regs ms3) (ms_mem ms3) md3 _);
  exact (ca_close_next 0%nat E3 ss3 ms3 ly St W regs0 mem0 md0 md3 p0 v s3v regs HS EA ltac:(vm_compute; reflexivity) HJ Hra
    Hgp0 Htp0 HRO HROK HCE Hsp46 HK Hsp HFR R3 R4 R8 Hs3 RP0 HAOK RNAMES) end).
Qed.
Lemma ca_iter_1 : ca_iter_stmt 1.
Proof.
unfold ca_iter_stmt.
intros ROW ly St W regs0 mem0 md0 p0 v s3v regs memc mdc HP NEXT.
pose proof (ca_lseed 1%nat ly St W regs0 mem0 md0 p0 v s3v regs memc mdc HP) as HS.
destruct HP as (HJ & Hra & Hgp0 & Htp0 & HRO & HROK & HCE & Hsp46 & HK & Hsp & HFR & R3 & R4 & R8 & R18 & R19 & R20 & R21
  & R22 & R23 & R24 & Hs3 & RP0 & HAOK & RNAMES).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hes : ESTACK = 4096) by reflexivity.
unfold cfg_at. change (w64 (BASE + CE_LOOP)) with (Z_to_bv 64 (BASE + CE_LOOP)).
set (E := Eimg (Ereg regs (ca_extra s3v regs0))) in HS.
assert (HEI : img_env VAL A_LIM E) by apply Eimg_env.
assert (EA : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (ca_extra s3v regs0)) n)
  by (intros n Hn; apply Eimg_low; exact Hn).
assert (Usp : bv_unsigned (ew E 2) = spZ regs)
  by (rewrite (EA 2%nat ltac:(unfold A_TEXT; lia)), (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
(* the shadow check of row k (zero), its name pointer, the strcmp call *)
paj_run_shc RUNP RUNC HS HJ; [cl_awr |].
cl_keep_run.
(lazymatch goal with HS : st_ok _ ?E _ (restrict _ ?ms), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
  HK : ce_kept _ _ _ _ |- _ =>
let Ra0 := fresh "Ra0" in let Ra1 := fresh "Ra1" in let Rra := fresh "Rra" in
let Qsp := fresh "Qsp" in let Qgp := fresh "Qgp" in let Qtp := fresh "Qtp" in
prreg HS (10%bv : bv 5) Ra0; prreg HS (11%bv : bv 5) Ra1; prreg HS (1%bv : bv 5) Rra;
prreg HS (2%bv : bv 5) Qsp; prreg HS (3%bv : bv 5) Qgp; prreg HS (4%bv : bv 5) Qtp;
pmkst HS;
eapply SRr_bind;
[ apply (ce_strcmp_at ly St W (spZ regs0) mem0 md0 ms _ p0 v (ca_name_addr 1%nat) (ca_nm 1%nat) 3888 HJ HRO HCE HK);
  [ rewrite Ra0, (EA 8%nat ltac:(unfold A_TEXT; lia)), (ew_Ereg_nat regs _ 8 8%bv eq_refl); exact R8
  | rewrite Ra1; apply bv_eq; vm_compute; reflexivity
  | unfold spZ at 1; rewrite Qsp, Usp; exact Hsp
  | rewrite Qgp, (EA 3%nat ltac:(unfold A_TEXT; lia)), (ew_Ereg_nat regs _ 3 3%bv eq_refl), R3; exact Hgp0
  | rewrite Qtp, (EA 4%nat ltac:(unfold A_TEXT; lia)), (ew_Ereg_nat regs _ 4 4%bv eq_refl), R4; exact Htp0
  | exact Rra | lia | reflexivity | exact RP0 | exact (RNAMES 1%nat ltac:(lia)) ]
| ];
clear Ra0 Ra1 Rra Qsp Qgp Qtp; cbv beta;
intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hcmp & HK2 & Hfr2);
let HS2 := fresh "HS" in
jafter_call_keep_hi HS 1024%nat regs2 (mrestrict (w_H W) mem2) HP2 [0; 1; 2]%nat HS2;
ce_kept_regions HS2 Hfr2 HJ2;
rewrite <- restrict_mkst_fx in HS2;
lazymatch goal with HFR : ca_frame_at _ _ _ _ |- _ =>
  let HFR2 := fresh "HFR" in
  pose proof (ce_frame_call W (ms_mem ms) mem2 (spZ regs) regs0 _ _ HFR Hfr2 ltac:(lia) ltac:(lia) ltac:(lia)) as HFR2;
  clear HFR; rename HFR2 into HFR end;
clear HS HJ HK; rename HS2 into HS; rename HJ2 into HJ; rename HK2 into HK;
assert (HEI2 : img_env VAL A_LIM (havoc E 1024 (map (getr regs2) CLOB))) by (apply img_env_havoc_hi; [exact HEI | unfold A_LIM; lia]);
assert (Usp2 : bv_unsigned (ew (havoc E 1024 (map (getr regs2) CLOB)) 2) = spZ regs) by (rewrite ew_havoc_old by lia; exact Usp);
assert (EA2 : forall n, (n < A_TEXT)%nat -> ew (havoc E 1024 (map (getr regs2) CLOB)) n = ew (Ereg regs (ca_extra s3v regs0)) n)
  by (intros n Hn; rewrite ew_havoc_old by (unfold A_TEXT in Hn; lia); apply EA; exact Hn);
pose proof (ce_U_w _ _ _ (ce_havoc_a0 E 1024 regs2)) as UA; cbn [Nat.add] in UA;
clear Usp EA; rename Usp2 into Usp; rename EA2 into EA
end).
(* beqz a0 (0x87460) *)
psrr_branch_pi RUNP BR HS.
- (lazymatch goal with Hc : branch_taken _ _ _ = true, UA : U _ _ = bv_unsigned (getr ?r2 10), Hcmp : getr ?r2 10 = w64 0 <-> _ |- _ =>
  let Hv := fresh "Hv" in
  assert (Hv : v = ca_nm 1%nat) by (apply Hcmp; apply bv_eq; rewrite (ce_br_eq _ _ _ 0 UA) in Hc; apply Z.eqb_eq in Hc;
    rewrite Hc; reflexivity);
  let Hmm := fresh "Hmm" in
  assert (Hmm : fst (ca_ar 1%nat) <= s3v - 1 <= snd (ca_ar 1%nat))
    by (unfold ca_aok in HAOK; rewrite Hv, (ca_find_all 1%nat ltac:(lia)) in HAOK; exact HAOK);
  paj_run_to_shc RUNTOP HS HJ CA_SEG; [cl_awr |]; cl_keep_run;
  lazymatch goal with HS : st_ok_pi _ _ ?E3 ?ss3 (restrict _ ?ms3), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
    HK : ce_kept _ _ _ _, HFR : ca_frame_at _ _ _ _ |- SRr _ _ (mkCfg _ ?md3) _ =>
    pmkst HS;
    refine (ROW ly St W regs0 mem0 md0 W (ms_regs ms3) (ms_mem ms3) md3 s3v _ Hgp0 Htp0);
    exact (ca_close_row 1%nat _ _ E3 ss3 ms3 ly St W regs0 mem0 md0 md3 s3v regs HS EA ltac:(vm_compute; reflexivity) HJ Hra
      (ce_ro_kept W mem0 (ms_mem ms3) (spZ regs0) HROK HK HCE) Hsp HFR R3 R4 Hmm Hs3) end end).
- (paj_run_to_shc RUNTOP HS HJ CE_LOOP; [cl_awr |]; cl_keep_run;
lazymatch goal with HS : st_ok_pi _ _ ?E3 ?ss3 (restrict _ ?ms3), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
  HK : ce_kept _ _ _ _, HFR : ca_frame_at _ _ _ _ |- SRr _ _ (mkCfg _ ?md3) _ =>
  pmkst HS;
  refine (NEXT ltac:(apply Nat.ltb_lt; reflexivity) (ms_regs ms3) (ms_mem ms3) md3 _);
  exact (ca_close_next 1%nat E3 ss3 ms3 ly St W regs0 mem0 md0 md3 p0 v s3v regs HS EA ltac:(vm_compute; reflexivity) HJ Hra
    Hgp0 Htp0 HRO HROK HCE Hsp46 HK Hsp HFR R3 R4 R8 Hs3 RP0 HAOK RNAMES) end).
Qed.
Lemma ca_iter_2 : ca_iter_stmt 2.
Proof.
unfold ca_iter_stmt.
intros ROW ly St W regs0 mem0 md0 p0 v s3v regs memc mdc HP NEXT.
pose proof (ca_lseed 2%nat ly St W regs0 mem0 md0 p0 v s3v regs memc mdc HP) as HS.
destruct HP as (HJ & Hra & Hgp0 & Htp0 & HRO & HROK & HCE & Hsp46 & HK & Hsp & HFR & R3 & R4 & R8 & R18 & R19 & R20 & R21
  & R22 & R23 & R24 & Hs3 & RP0 & HAOK & RNAMES).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hes : ESTACK = 4096) by reflexivity.
unfold cfg_at. change (w64 (BASE + CE_LOOP)) with (Z_to_bv 64 (BASE + CE_LOOP)).
set (E := Eimg (Ereg regs (ca_extra s3v regs0))) in HS.
assert (HEI : img_env VAL A_LIM E) by apply Eimg_env.
assert (EA : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (ca_extra s3v regs0)) n)
  by (intros n Hn; apply Eimg_low; exact Hn).
assert (Usp : bv_unsigned (ew E 2) = spZ regs)
  by (rewrite (EA 2%nat ltac:(unfold A_TEXT; lia)), (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
(* the shadow check of row k (zero), its name pointer, the strcmp call *)
paj_run_shc RUNP RUNC HS HJ; [cl_awr |].
cl_keep_run.
(lazymatch goal with HS : st_ok _ ?E _ (restrict _ ?ms), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
  HK : ce_kept _ _ _ _ |- _ =>
let Ra0 := fresh "Ra0" in let Ra1 := fresh "Ra1" in let Rra := fresh "Rra" in
let Qsp := fresh "Qsp" in let Qgp := fresh "Qgp" in let Qtp := fresh "Qtp" in
prreg HS (10%bv : bv 5) Ra0; prreg HS (11%bv : bv 5) Ra1; prreg HS (1%bv : bv 5) Rra;
prreg HS (2%bv : bv 5) Qsp; prreg HS (3%bv : bv 5) Qgp; prreg HS (4%bv : bv 5) Qtp;
pmkst HS;
eapply SRr_bind;
[ apply (ce_strcmp_at ly St W (spZ regs0) mem0 md0 ms _ p0 v (ca_name_addr 2%nat) (ca_nm 2%nat) 3888 HJ HRO HCE HK);
  [ rewrite Ra0, (EA 8%nat ltac:(unfold A_TEXT; lia)), (ew_Ereg_nat regs _ 8 8%bv eq_refl); exact R8
  | rewrite Ra1; apply bv_eq; vm_compute; reflexivity
  | unfold spZ at 1; rewrite Qsp, Usp; exact Hsp
  | rewrite Qgp, (EA 3%nat ltac:(unfold A_TEXT; lia)), (ew_Ereg_nat regs _ 3 3%bv eq_refl), R3; exact Hgp0
  | rewrite Qtp, (EA 4%nat ltac:(unfold A_TEXT; lia)), (ew_Ereg_nat regs _ 4 4%bv eq_refl), R4; exact Htp0
  | exact Rra | lia | reflexivity | exact RP0 | exact (RNAMES 2%nat ltac:(lia)) ]
| ];
clear Ra0 Ra1 Rra Qsp Qgp Qtp; cbv beta;
intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hcmp & HK2 & Hfr2);
let HS2 := fresh "HS" in
jafter_call_keep_hi HS 1024%nat regs2 (mrestrict (w_H W) mem2) HP2 [0; 1; 2]%nat HS2;
ce_kept_regions HS2 Hfr2 HJ2;
rewrite <- restrict_mkst_fx in HS2;
lazymatch goal with HFR : ca_frame_at _ _ _ _ |- _ =>
  let HFR2 := fresh "HFR" in
  pose proof (ce_frame_call W (ms_mem ms) mem2 (spZ regs) regs0 _ _ HFR Hfr2 ltac:(lia) ltac:(lia) ltac:(lia)) as HFR2;
  clear HFR; rename HFR2 into HFR end;
clear HS HJ HK; rename HS2 into HS; rename HJ2 into HJ; rename HK2 into HK;
assert (HEI2 : img_env VAL A_LIM (havoc E 1024 (map (getr regs2) CLOB))) by (apply img_env_havoc_hi; [exact HEI | unfold A_LIM; lia]);
assert (Usp2 : bv_unsigned (ew (havoc E 1024 (map (getr regs2) CLOB)) 2) = spZ regs) by (rewrite ew_havoc_old by lia; exact Usp);
assert (EA2 : forall n, (n < A_TEXT)%nat -> ew (havoc E 1024 (map (getr regs2) CLOB)) n = ew (Ereg regs (ca_extra s3v regs0)) n)
  by (intros n Hn; rewrite ew_havoc_old by (unfold A_TEXT in Hn; lia); apply EA; exact Hn);
pose proof (ce_U_w _ _ _ (ce_havoc_a0 E 1024 regs2)) as UA; cbn [Nat.add] in UA;
clear Usp EA; rename Usp2 into Usp; rename EA2 into EA
end).
(* beqz a0 (0x87460) *)
psrr_branch_pi RUNP BR HS.
- (lazymatch goal with Hc : branch_taken _ _ _ = true, UA : U _ _ = bv_unsigned (getr ?r2 10), Hcmp : getr ?r2 10 = w64 0 <-> _ |- _ =>
  let Hv := fresh "Hv" in
  assert (Hv : v = ca_nm 2%nat) by (apply Hcmp; apply bv_eq; rewrite (ce_br_eq _ _ _ 0 UA) in Hc; apply Z.eqb_eq in Hc;
    rewrite Hc; reflexivity);
  let Hmm := fresh "Hmm" in
  assert (Hmm : fst (ca_ar 2%nat) <= s3v - 1 <= snd (ca_ar 2%nat))
    by (unfold ca_aok in HAOK; rewrite Hv, (ca_find_all 2%nat ltac:(lia)) in HAOK; exact HAOK);
  paj_run_to_shc RUNTOP HS HJ CA_SEG; [cl_awr |]; cl_keep_run;
  lazymatch goal with HS : st_ok_pi _ _ ?E3 ?ss3 (restrict _ ?ms3), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
    HK : ce_kept _ _ _ _, HFR : ca_frame_at _ _ _ _ |- SRr _ _ (mkCfg _ ?md3) _ =>
    pmkst HS;
    refine (ROW ly St W regs0 mem0 md0 W (ms_regs ms3) (ms_mem ms3) md3 s3v _ Hgp0 Htp0);
    exact (ca_close_row 2%nat _ _ E3 ss3 ms3 ly St W regs0 mem0 md0 md3 s3v regs HS EA ltac:(vm_compute; reflexivity) HJ Hra
      (ce_ro_kept W mem0 (ms_mem ms3) (spZ regs0) HROK HK HCE) Hsp HFR R3 R4 Hmm Hs3) end end).
- (paj_run_to_shc RUNTOP HS HJ CE_LOOP; [cl_awr |]; cl_keep_run;
lazymatch goal with HS : st_ok_pi _ _ ?E3 ?ss3 (restrict _ ?ms3), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
  HK : ce_kept _ _ _ _, HFR : ca_frame_at _ _ _ _ |- SRr _ _ (mkCfg _ ?md3) _ =>
  pmkst HS;
  refine (NEXT ltac:(apply Nat.ltb_lt; reflexivity) (ms_regs ms3) (ms_mem ms3) md3 _);
  exact (ca_close_next 2%nat E3 ss3 ms3 ly St W regs0 mem0 md0 md3 p0 v s3v regs HS EA ltac:(vm_compute; reflexivity) HJ Hra
    Hgp0 Htp0 HRO HROK HCE Hsp46 HK Hsp HFR R3 R4 R8 Hs3 RP0 HAOK RNAMES) end).
Qed.
Lemma ca_iter_3 : ca_iter_stmt 3.
Proof.
unfold ca_iter_stmt.
intros ROW ly St W regs0 mem0 md0 p0 v s3v regs memc mdc HP NEXT.
pose proof (ca_lseed 3%nat ly St W regs0 mem0 md0 p0 v s3v regs memc mdc HP) as HS.
destruct HP as (HJ & Hra & Hgp0 & Htp0 & HRO & HROK & HCE & Hsp46 & HK & Hsp & HFR & R3 & R4 & R8 & R18 & R19 & R20 & R21
  & R22 & R23 & R24 & Hs3 & RP0 & HAOK & RNAMES).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hes : ESTACK = 4096) by reflexivity.
unfold cfg_at. change (w64 (BASE + CE_LOOP)) with (Z_to_bv 64 (BASE + CE_LOOP)).
set (E := Eimg (Ereg regs (ca_extra s3v regs0))) in HS.
assert (HEI : img_env VAL A_LIM E) by apply Eimg_env.
assert (EA : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (ca_extra s3v regs0)) n)
  by (intros n Hn; apply Eimg_low; exact Hn).
assert (Usp : bv_unsigned (ew E 2) = spZ regs)
  by (rewrite (EA 2%nat ltac:(unfold A_TEXT; lia)), (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
(* the shadow check of row k (zero), its name pointer, the strcmp call *)
paj_run_shc RUNP RUNC HS HJ; [cl_awr |].
cl_keep_run.
(lazymatch goal with HS : st_ok _ ?E _ (restrict _ ?ms), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
  HK : ce_kept _ _ _ _ |- _ =>
let Ra0 := fresh "Ra0" in let Ra1 := fresh "Ra1" in let Rra := fresh "Rra" in
let Qsp := fresh "Qsp" in let Qgp := fresh "Qgp" in let Qtp := fresh "Qtp" in
prreg HS (10%bv : bv 5) Ra0; prreg HS (11%bv : bv 5) Ra1; prreg HS (1%bv : bv 5) Rra;
prreg HS (2%bv : bv 5) Qsp; prreg HS (3%bv : bv 5) Qgp; prreg HS (4%bv : bv 5) Qtp;
pmkst HS;
eapply SRr_bind;
[ apply (ce_strcmp_at ly St W (spZ regs0) mem0 md0 ms _ p0 v (ca_name_addr 3%nat) (ca_nm 3%nat) 3888 HJ HRO HCE HK);
  [ rewrite Ra0, (EA 8%nat ltac:(unfold A_TEXT; lia)), (ew_Ereg_nat regs _ 8 8%bv eq_refl); exact R8
  | rewrite Ra1; apply bv_eq; vm_compute; reflexivity
  | unfold spZ at 1; rewrite Qsp, Usp; exact Hsp
  | rewrite Qgp, (EA 3%nat ltac:(unfold A_TEXT; lia)), (ew_Ereg_nat regs _ 3 3%bv eq_refl), R3; exact Hgp0
  | rewrite Qtp, (EA 4%nat ltac:(unfold A_TEXT; lia)), (ew_Ereg_nat regs _ 4 4%bv eq_refl), R4; exact Htp0
  | exact Rra | lia | reflexivity | exact RP0 | exact (RNAMES 3%nat ltac:(lia)) ]
| ];
clear Ra0 Ra1 Rra Qsp Qgp Qtp; cbv beta;
intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hcmp & HK2 & Hfr2);
let HS2 := fresh "HS" in
jafter_call_keep_hi HS 1024%nat regs2 (mrestrict (w_H W) mem2) HP2 [0; 1; 2]%nat HS2;
ce_kept_regions HS2 Hfr2 HJ2;
rewrite <- restrict_mkst_fx in HS2;
lazymatch goal with HFR : ca_frame_at _ _ _ _ |- _ =>
  let HFR2 := fresh "HFR" in
  pose proof (ce_frame_call W (ms_mem ms) mem2 (spZ regs) regs0 _ _ HFR Hfr2 ltac:(lia) ltac:(lia) ltac:(lia)) as HFR2;
  clear HFR; rename HFR2 into HFR end;
clear HS HJ HK; rename HS2 into HS; rename HJ2 into HJ; rename HK2 into HK;
assert (HEI2 : img_env VAL A_LIM (havoc E 1024 (map (getr regs2) CLOB))) by (apply img_env_havoc_hi; [exact HEI | unfold A_LIM; lia]);
assert (Usp2 : bv_unsigned (ew (havoc E 1024 (map (getr regs2) CLOB)) 2) = spZ regs) by (rewrite ew_havoc_old by lia; exact Usp);
assert (EA2 : forall n, (n < A_TEXT)%nat -> ew (havoc E 1024 (map (getr regs2) CLOB)) n = ew (Ereg regs (ca_extra s3v regs0)) n)
  by (intros n Hn; rewrite ew_havoc_old by (unfold A_TEXT in Hn; lia); apply EA; exact Hn);
pose proof (ce_U_w _ _ _ (ce_havoc_a0 E 1024 regs2)) as UA; cbn [Nat.add] in UA;
clear Usp EA; rename Usp2 into Usp; rename EA2 into EA
end).
(* beqz a0 (0x87460) *)
psrr_branch_pi RUNP BR HS.
- (lazymatch goal with Hc : branch_taken _ _ _ = true, UA : U _ _ = bv_unsigned (getr ?r2 10), Hcmp : getr ?r2 10 = w64 0 <-> _ |- _ =>
  let Hv := fresh "Hv" in
  assert (Hv : v = ca_nm 3%nat) by (apply Hcmp; apply bv_eq; rewrite (ce_br_eq _ _ _ 0 UA) in Hc; apply Z.eqb_eq in Hc;
    rewrite Hc; reflexivity);
  let Hmm := fresh "Hmm" in
  assert (Hmm : fst (ca_ar 3%nat) <= s3v - 1 <= snd (ca_ar 3%nat))
    by (unfold ca_aok in HAOK; rewrite Hv, (ca_find_all 3%nat ltac:(lia)) in HAOK; exact HAOK);
  paj_run_to_shc RUNTOP HS HJ CA_SEG; [cl_awr |]; cl_keep_run;
  lazymatch goal with HS : st_ok_pi _ _ ?E3 ?ss3 (restrict _ ?ms3), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
    HK : ce_kept _ _ _ _, HFR : ca_frame_at _ _ _ _ |- SRr _ _ (mkCfg _ ?md3) _ =>
    pmkst HS;
    refine (ROW ly St W regs0 mem0 md0 W (ms_regs ms3) (ms_mem ms3) md3 s3v _ Hgp0 Htp0);
    exact (ca_close_row 3%nat _ _ E3 ss3 ms3 ly St W regs0 mem0 md0 md3 s3v regs HS EA ltac:(vm_compute; reflexivity) HJ Hra
      (ce_ro_kept W mem0 (ms_mem ms3) (spZ regs0) HROK HK HCE) Hsp HFR R3 R4 Hmm Hs3) end end).
- (paj_run_to_shc RUNTOP HS HJ CE_LOOP; [cl_awr |]; cl_keep_run;
lazymatch goal with HS : st_ok_pi _ _ ?E3 ?ss3 (restrict _ ?ms3), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
  HK : ce_kept _ _ _ _, HFR : ca_frame_at _ _ _ _ |- SRr _ _ (mkCfg _ ?md3) _ =>
  pmkst HS;
  refine (NEXT ltac:(apply Nat.ltb_lt; reflexivity) (ms_regs ms3) (ms_mem ms3) md3 _);
  exact (ca_close_next 3%nat E3 ss3 ms3 ly St W regs0 mem0 md0 md3 p0 v s3v regs HS EA ltac:(vm_compute; reflexivity) HJ Hra
    Hgp0 Htp0 HRO HROK HCE Hsp46 HK Hsp HFR R3 R4 R8 Hs3 RP0 HAOK RNAMES) end).
Qed.
Lemma ca_iter_4 : ca_iter_stmt 4.
Proof.
unfold ca_iter_stmt.
intros ROW ly St W regs0 mem0 md0 p0 v s3v regs memc mdc HP NEXT.
pose proof (ca_lseed 4%nat ly St W regs0 mem0 md0 p0 v s3v regs memc mdc HP) as HS.
destruct HP as (HJ & Hra & Hgp0 & Htp0 & HRO & HROK & HCE & Hsp46 & HK & Hsp & HFR & R3 & R4 & R8 & R18 & R19 & R20 & R21
  & R22 & R23 & R24 & Hs3 & RP0 & HAOK & RNAMES).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hes : ESTACK = 4096) by reflexivity.
unfold cfg_at. change (w64 (BASE + CE_LOOP)) with (Z_to_bv 64 (BASE + CE_LOOP)).
set (E := Eimg (Ereg regs (ca_extra s3v regs0))) in HS.
assert (HEI : img_env VAL A_LIM E) by apply Eimg_env.
assert (EA : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (ca_extra s3v regs0)) n)
  by (intros n Hn; apply Eimg_low; exact Hn).
assert (Usp : bv_unsigned (ew E 2) = spZ regs)
  by (rewrite (EA 2%nat ltac:(unfold A_TEXT; lia)), (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
(* the shadow check of row k (zero), its name pointer, the strcmp call *)
paj_run_shc RUNP RUNC HS HJ; [cl_awr |].
cl_keep_run.
(lazymatch goal with HS : st_ok _ ?E _ (restrict _ ?ms), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
  HK : ce_kept _ _ _ _ |- _ =>
let Ra0 := fresh "Ra0" in let Ra1 := fresh "Ra1" in let Rra := fresh "Rra" in
let Qsp := fresh "Qsp" in let Qgp := fresh "Qgp" in let Qtp := fresh "Qtp" in
prreg HS (10%bv : bv 5) Ra0; prreg HS (11%bv : bv 5) Ra1; prreg HS (1%bv : bv 5) Rra;
prreg HS (2%bv : bv 5) Qsp; prreg HS (3%bv : bv 5) Qgp; prreg HS (4%bv : bv 5) Qtp;
pmkst HS;
eapply SRr_bind;
[ apply (ce_strcmp_at ly St W (spZ regs0) mem0 md0 ms _ p0 v (ca_name_addr 4%nat) (ca_nm 4%nat) 3888 HJ HRO HCE HK);
  [ rewrite Ra0, (EA 8%nat ltac:(unfold A_TEXT; lia)), (ew_Ereg_nat regs _ 8 8%bv eq_refl); exact R8
  | rewrite Ra1; apply bv_eq; vm_compute; reflexivity
  | unfold spZ at 1; rewrite Qsp, Usp; exact Hsp
  | rewrite Qgp, (EA 3%nat ltac:(unfold A_TEXT; lia)), (ew_Ereg_nat regs _ 3 3%bv eq_refl), R3; exact Hgp0
  | rewrite Qtp, (EA 4%nat ltac:(unfold A_TEXT; lia)), (ew_Ereg_nat regs _ 4 4%bv eq_refl), R4; exact Htp0
  | exact Rra | lia | reflexivity | exact RP0 | exact (RNAMES 4%nat ltac:(lia)) ]
| ];
clear Ra0 Ra1 Rra Qsp Qgp Qtp; cbv beta;
intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hcmp & HK2 & Hfr2);
let HS2 := fresh "HS" in
jafter_call_keep_hi HS 1024%nat regs2 (mrestrict (w_H W) mem2) HP2 [0; 1; 2]%nat HS2;
ce_kept_regions HS2 Hfr2 HJ2;
rewrite <- restrict_mkst_fx in HS2;
lazymatch goal with HFR : ca_frame_at _ _ _ _ |- _ =>
  let HFR2 := fresh "HFR" in
  pose proof (ce_frame_call W (ms_mem ms) mem2 (spZ regs) regs0 _ _ HFR Hfr2 ltac:(lia) ltac:(lia) ltac:(lia)) as HFR2;
  clear HFR; rename HFR2 into HFR end;
clear HS HJ HK; rename HS2 into HS; rename HJ2 into HJ; rename HK2 into HK;
assert (HEI2 : img_env VAL A_LIM (havoc E 1024 (map (getr regs2) CLOB))) by (apply img_env_havoc_hi; [exact HEI | unfold A_LIM; lia]);
assert (Usp2 : bv_unsigned (ew (havoc E 1024 (map (getr regs2) CLOB)) 2) = spZ regs) by (rewrite ew_havoc_old by lia; exact Usp);
assert (EA2 : forall n, (n < A_TEXT)%nat -> ew (havoc E 1024 (map (getr regs2) CLOB)) n = ew (Ereg regs (ca_extra s3v regs0)) n)
  by (intros n Hn; rewrite ew_havoc_old by (unfold A_TEXT in Hn; lia); apply EA; exact Hn);
pose proof (ce_U_w _ _ _ (ce_havoc_a0 E 1024 regs2)) as UA; cbn [Nat.add] in UA;
clear Usp EA; rename Usp2 into Usp; rename EA2 into EA
end).
(* beqz a0 (0x87460) *)
psrr_branch_pi RUNP BR HS.
- (lazymatch goal with Hc : branch_taken _ _ _ = true, UA : U _ _ = bv_unsigned (getr ?r2 10), Hcmp : getr ?r2 10 = w64 0 <-> _ |- _ =>
  let Hv := fresh "Hv" in
  assert (Hv : v = ca_nm 4%nat) by (apply Hcmp; apply bv_eq; rewrite (ce_br_eq _ _ _ 0 UA) in Hc; apply Z.eqb_eq in Hc;
    rewrite Hc; reflexivity);
  let Hmm := fresh "Hmm" in
  assert (Hmm : fst (ca_ar 4%nat) <= s3v - 1 <= snd (ca_ar 4%nat))
    by (unfold ca_aok in HAOK; rewrite Hv, (ca_find_all 4%nat ltac:(lia)) in HAOK; exact HAOK);
  paj_run_to_shc RUNTOP HS HJ CA_SEG; [cl_awr |]; cl_keep_run;
  lazymatch goal with HS : st_ok_pi _ _ ?E3 ?ss3 (restrict _ ?ms3), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
    HK : ce_kept _ _ _ _, HFR : ca_frame_at _ _ _ _ |- SRr _ _ (mkCfg _ ?md3) _ =>
    pmkst HS;
    refine (ROW ly St W regs0 mem0 md0 W (ms_regs ms3) (ms_mem ms3) md3 s3v _ Hgp0 Htp0);
    exact (ca_close_row 4%nat _ _ E3 ss3 ms3 ly St W regs0 mem0 md0 md3 s3v regs HS EA ltac:(vm_compute; reflexivity) HJ Hra
      (ce_ro_kept W mem0 (ms_mem ms3) (spZ regs0) HROK HK HCE) Hsp HFR R3 R4 Hmm Hs3) end end).
- (paj_run_to_shc RUNTOP HS HJ CE_LOOP; [cl_awr |]; cl_keep_run;
lazymatch goal with HS : st_ok_pi _ _ ?E3 ?ss3 (restrict _ ?ms3), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
  HK : ce_kept _ _ _ _, HFR : ca_frame_at _ _ _ _ |- SRr _ _ (mkCfg _ ?md3) _ =>
  pmkst HS;
  refine (NEXT ltac:(apply Nat.ltb_lt; reflexivity) (ms_regs ms3) (ms_mem ms3) md3 _);
  exact (ca_close_next 4%nat E3 ss3 ms3 ly St W regs0 mem0 md0 md3 p0 v s3v regs HS EA ltac:(vm_compute; reflexivity) HJ Hra
    Hgp0 Htp0 HRO HROK HCE Hsp46 HK Hsp HFR R3 R4 R8 Hs3 RP0 HAOK RNAMES) end).
Qed.
Lemma ca_iter_5 : ca_iter_stmt 5.
Proof.
unfold ca_iter_stmt.
intros ROW ly St W regs0 mem0 md0 p0 v s3v regs memc mdc HP NEXT.
pose proof (ca_lseed 5%nat ly St W regs0 mem0 md0 p0 v s3v regs memc mdc HP) as HS.
destruct HP as (HJ & Hra & Hgp0 & Htp0 & HRO & HROK & HCE & Hsp46 & HK & Hsp & HFR & R3 & R4 & R8 & R18 & R19 & R20 & R21
  & R22 & R23 & R24 & Hs3 & RP0 & HAOK & RNAMES).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hes : ESTACK = 4096) by reflexivity.
unfold cfg_at. change (w64 (BASE + CE_LOOP)) with (Z_to_bv 64 (BASE + CE_LOOP)).
set (E := Eimg (Ereg regs (ca_extra s3v regs0))) in HS.
assert (HEI : img_env VAL A_LIM E) by apply Eimg_env.
assert (EA : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (ca_extra s3v regs0)) n)
  by (intros n Hn; apply Eimg_low; exact Hn).
assert (Usp : bv_unsigned (ew E 2) = spZ regs)
  by (rewrite (EA 2%nat ltac:(unfold A_TEXT; lia)), (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
(* the shadow check of row k (zero), its name pointer, the strcmp call *)
paj_run_shc RUNP RUNC HS HJ; [cl_awr |].
cl_keep_run.
(lazymatch goal with HS : st_ok _ ?E _ (restrict _ ?ms), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
  HK : ce_kept _ _ _ _ |- _ =>
let Ra0 := fresh "Ra0" in let Ra1 := fresh "Ra1" in let Rra := fresh "Rra" in
let Qsp := fresh "Qsp" in let Qgp := fresh "Qgp" in let Qtp := fresh "Qtp" in
prreg HS (10%bv : bv 5) Ra0; prreg HS (11%bv : bv 5) Ra1; prreg HS (1%bv : bv 5) Rra;
prreg HS (2%bv : bv 5) Qsp; prreg HS (3%bv : bv 5) Qgp; prreg HS (4%bv : bv 5) Qtp;
pmkst HS;
eapply SRr_bind;
[ apply (ce_strcmp_at ly St W (spZ regs0) mem0 md0 ms _ p0 v (ca_name_addr 5%nat) (ca_nm 5%nat) 3888 HJ HRO HCE HK);
  [ rewrite Ra0, (EA 8%nat ltac:(unfold A_TEXT; lia)), (ew_Ereg_nat regs _ 8 8%bv eq_refl); exact R8
  | rewrite Ra1; apply bv_eq; vm_compute; reflexivity
  | unfold spZ at 1; rewrite Qsp, Usp; exact Hsp
  | rewrite Qgp, (EA 3%nat ltac:(unfold A_TEXT; lia)), (ew_Ereg_nat regs _ 3 3%bv eq_refl), R3; exact Hgp0
  | rewrite Qtp, (EA 4%nat ltac:(unfold A_TEXT; lia)), (ew_Ereg_nat regs _ 4 4%bv eq_refl), R4; exact Htp0
  | exact Rra | lia | reflexivity | exact RP0 | exact (RNAMES 5%nat ltac:(lia)) ]
| ];
clear Ra0 Ra1 Rra Qsp Qgp Qtp; cbv beta;
intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hcmp & HK2 & Hfr2);
let HS2 := fresh "HS" in
jafter_call_keep_hi HS 1024%nat regs2 (mrestrict (w_H W) mem2) HP2 [0; 1; 2]%nat HS2;
ce_kept_regions HS2 Hfr2 HJ2;
rewrite <- restrict_mkst_fx in HS2;
lazymatch goal with HFR : ca_frame_at _ _ _ _ |- _ =>
  let HFR2 := fresh "HFR" in
  pose proof (ce_frame_call W (ms_mem ms) mem2 (spZ regs) regs0 _ _ HFR Hfr2 ltac:(lia) ltac:(lia) ltac:(lia)) as HFR2;
  clear HFR; rename HFR2 into HFR end;
clear HS HJ HK; rename HS2 into HS; rename HJ2 into HJ; rename HK2 into HK;
assert (HEI2 : img_env VAL A_LIM (havoc E 1024 (map (getr regs2) CLOB))) by (apply img_env_havoc_hi; [exact HEI | unfold A_LIM; lia]);
assert (Usp2 : bv_unsigned (ew (havoc E 1024 (map (getr regs2) CLOB)) 2) = spZ regs) by (rewrite ew_havoc_old by lia; exact Usp);
assert (EA2 : forall n, (n < A_TEXT)%nat -> ew (havoc E 1024 (map (getr regs2) CLOB)) n = ew (Ereg regs (ca_extra s3v regs0)) n)
  by (intros n Hn; rewrite ew_havoc_old by (unfold A_TEXT in Hn; lia); apply EA; exact Hn);
pose proof (ce_U_w _ _ _ (ce_havoc_a0 E 1024 regs2)) as UA; cbn [Nat.add] in UA;
clear Usp EA; rename Usp2 into Usp; rename EA2 into EA
end).
(* beqz a0 (0x87460) *)
psrr_branch_pi RUNP BR HS.
- (lazymatch goal with Hc : branch_taken _ _ _ = true, UA : U _ _ = bv_unsigned (getr ?r2 10), Hcmp : getr ?r2 10 = w64 0 <-> _ |- _ =>
  let Hv := fresh "Hv" in
  assert (Hv : v = ca_nm 5%nat) by (apply Hcmp; apply bv_eq; rewrite (ce_br_eq _ _ _ 0 UA) in Hc; apply Z.eqb_eq in Hc;
    rewrite Hc; reflexivity);
  let Hmm := fresh "Hmm" in
  assert (Hmm : fst (ca_ar 5%nat) <= s3v - 1 <= snd (ca_ar 5%nat))
    by (unfold ca_aok in HAOK; rewrite Hv, (ca_find_all 5%nat ltac:(lia)) in HAOK; exact HAOK);
  paj_run_to_shc RUNTOP HS HJ CA_SEG; [cl_awr |]; cl_keep_run;
  lazymatch goal with HS : st_ok_pi _ _ ?E3 ?ss3 (restrict _ ?ms3), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
    HK : ce_kept _ _ _ _, HFR : ca_frame_at _ _ _ _ |- SRr _ _ (mkCfg _ ?md3) _ =>
    pmkst HS;
    refine (ROW ly St W regs0 mem0 md0 W (ms_regs ms3) (ms_mem ms3) md3 s3v _ Hgp0 Htp0);
    exact (ca_close_row 5%nat _ _ E3 ss3 ms3 ly St W regs0 mem0 md0 md3 s3v regs HS EA ltac:(vm_compute; reflexivity) HJ Hra
      (ce_ro_kept W mem0 (ms_mem ms3) (spZ regs0) HROK HK HCE) Hsp HFR R3 R4 Hmm Hs3) end end).
- (paj_run_to_shc RUNTOP HS HJ CE_LOOP; [cl_awr |]; cl_keep_run;
lazymatch goal with HS : st_ok_pi _ _ ?E3 ?ss3 (restrict _ ?ms3), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
  HK : ce_kept _ _ _ _, HFR : ca_frame_at _ _ _ _ |- SRr _ _ (mkCfg _ ?md3) _ =>
  pmkst HS;
  refine (NEXT ltac:(apply Nat.ltb_lt; reflexivity) (ms_regs ms3) (ms_mem ms3) md3 _);
  exact (ca_close_next 5%nat E3 ss3 ms3 ly St W regs0 mem0 md0 md3 p0 v s3v regs HS EA ltac:(vm_compute; reflexivity) HJ Hra
    Hgp0 Htp0 HRO HROK HCE Hsp46 HK Hsp HFR R3 R4 R8 Hs3 RP0 HAOK RNAMES) end).
Qed.
Lemma ca_iter_6 : ca_iter_stmt 6.
Proof.
unfold ca_iter_stmt.
intros ROW ly St W regs0 mem0 md0 p0 v s3v regs memc mdc HP NEXT.
pose proof (ca_lseed 6%nat ly St W regs0 mem0 md0 p0 v s3v regs memc mdc HP) as HS.
destruct HP as (HJ & Hra & Hgp0 & Htp0 & HRO & HROK & HCE & Hsp46 & HK & Hsp & HFR & R3 & R4 & R8 & R18 & R19 & R20 & R21
  & R22 & R23 & R24 & Hs3 & RP0 & HAOK & RNAMES).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hes : ESTACK = 4096) by reflexivity.
unfold cfg_at. change (w64 (BASE + CE_LOOP)) with (Z_to_bv 64 (BASE + CE_LOOP)).
set (E := Eimg (Ereg regs (ca_extra s3v regs0))) in HS.
assert (HEI : img_env VAL A_LIM E) by apply Eimg_env.
assert (EA : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (ca_extra s3v regs0)) n)
  by (intros n Hn; apply Eimg_low; exact Hn).
assert (Usp : bv_unsigned (ew E 2) = spZ regs)
  by (rewrite (EA 2%nat ltac:(unfold A_TEXT; lia)), (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
(* the shadow check of row k (zero), its name pointer, the strcmp call *)
paj_run_shc RUNP RUNC HS HJ; [cl_awr |].
cl_keep_run.
(lazymatch goal with HS : st_ok _ ?E _ (restrict _ ?ms), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
  HK : ce_kept _ _ _ _ |- _ =>
let Ra0 := fresh "Ra0" in let Ra1 := fresh "Ra1" in let Rra := fresh "Rra" in
let Qsp := fresh "Qsp" in let Qgp := fresh "Qgp" in let Qtp := fresh "Qtp" in
prreg HS (10%bv : bv 5) Ra0; prreg HS (11%bv : bv 5) Ra1; prreg HS (1%bv : bv 5) Rra;
prreg HS (2%bv : bv 5) Qsp; prreg HS (3%bv : bv 5) Qgp; prreg HS (4%bv : bv 5) Qtp;
pmkst HS;
eapply SRr_bind;
[ apply (ce_strcmp_at ly St W (spZ regs0) mem0 md0 ms _ p0 v (ca_name_addr 6%nat) (ca_nm 6%nat) 3888 HJ HRO HCE HK);
  [ rewrite Ra0, (EA 8%nat ltac:(unfold A_TEXT; lia)), (ew_Ereg_nat regs _ 8 8%bv eq_refl); exact R8
  | rewrite Ra1; apply bv_eq; vm_compute; reflexivity
  | unfold spZ at 1; rewrite Qsp, Usp; exact Hsp
  | rewrite Qgp, (EA 3%nat ltac:(unfold A_TEXT; lia)), (ew_Ereg_nat regs _ 3 3%bv eq_refl), R3; exact Hgp0
  | rewrite Qtp, (EA 4%nat ltac:(unfold A_TEXT; lia)), (ew_Ereg_nat regs _ 4 4%bv eq_refl), R4; exact Htp0
  | exact Rra | lia | reflexivity | exact RP0 | exact (RNAMES 6%nat ltac:(lia)) ]
| ];
clear Ra0 Ra1 Rra Qsp Qgp Qtp; cbv beta;
intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hcmp & HK2 & Hfr2);
let HS2 := fresh "HS" in
jafter_call_keep_hi HS 1024%nat regs2 (mrestrict (w_H W) mem2) HP2 [0; 1; 2]%nat HS2;
ce_kept_regions HS2 Hfr2 HJ2;
rewrite <- restrict_mkst_fx in HS2;
lazymatch goal with HFR : ca_frame_at _ _ _ _ |- _ =>
  let HFR2 := fresh "HFR" in
  pose proof (ce_frame_call W (ms_mem ms) mem2 (spZ regs) regs0 _ _ HFR Hfr2 ltac:(lia) ltac:(lia) ltac:(lia)) as HFR2;
  clear HFR; rename HFR2 into HFR end;
clear HS HJ HK; rename HS2 into HS; rename HJ2 into HJ; rename HK2 into HK;
assert (HEI2 : img_env VAL A_LIM (havoc E 1024 (map (getr regs2) CLOB))) by (apply img_env_havoc_hi; [exact HEI | unfold A_LIM; lia]);
assert (Usp2 : bv_unsigned (ew (havoc E 1024 (map (getr regs2) CLOB)) 2) = spZ regs) by (rewrite ew_havoc_old by lia; exact Usp);
assert (EA2 : forall n, (n < A_TEXT)%nat -> ew (havoc E 1024 (map (getr regs2) CLOB)) n = ew (Ereg regs (ca_extra s3v regs0)) n)
  by (intros n Hn; rewrite ew_havoc_old by (unfold A_TEXT in Hn; lia); apply EA; exact Hn);
pose proof (ce_U_w _ _ _ (ce_havoc_a0 E 1024 regs2)) as UA; cbn [Nat.add] in UA;
clear Usp EA; rename Usp2 into Usp; rename EA2 into EA
end).
(* beqz a0 (0x87460) *)
psrr_branch_pi RUNP BR HS.
- (lazymatch goal with Hc : branch_taken _ _ _ = true, UA : U _ _ = bv_unsigned (getr ?r2 10), Hcmp : getr ?r2 10 = w64 0 <-> _ |- _ =>
  let Hv := fresh "Hv" in
  assert (Hv : v = ca_nm 6%nat) by (apply Hcmp; apply bv_eq; rewrite (ce_br_eq _ _ _ 0 UA) in Hc; apply Z.eqb_eq in Hc;
    rewrite Hc; reflexivity);
  let Hmm := fresh "Hmm" in
  assert (Hmm : fst (ca_ar 6%nat) <= s3v - 1 <= snd (ca_ar 6%nat))
    by (unfold ca_aok in HAOK; rewrite Hv, (ca_find_all 6%nat ltac:(lia)) in HAOK; exact HAOK);
  paj_run_to_shc RUNTOP HS HJ CA_SEG; [cl_awr |]; cl_keep_run;
  lazymatch goal with HS : st_ok_pi _ _ ?E3 ?ss3 (restrict _ ?ms3), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
    HK : ce_kept _ _ _ _, HFR : ca_frame_at _ _ _ _ |- SRr _ _ (mkCfg _ ?md3) _ =>
    pmkst HS;
    refine (ROW ly St W regs0 mem0 md0 W (ms_regs ms3) (ms_mem ms3) md3 s3v _ Hgp0 Htp0);
    exact (ca_close_row 6%nat _ _ E3 ss3 ms3 ly St W regs0 mem0 md0 md3 s3v regs HS EA ltac:(vm_compute; reflexivity) HJ Hra
      (ce_ro_kept W mem0 (ms_mem ms3) (spZ regs0) HROK HK HCE) Hsp HFR R3 R4 Hmm Hs3) end end).
- (paj_run_to_shc RUNTOP HS HJ CE_LOOP; [cl_awr |]; cl_keep_run;
lazymatch goal with HS : st_ok_pi _ _ ?E3 ?ss3 (restrict _ ?ms3), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
  HK : ce_kept _ _ _ _, HFR : ca_frame_at _ _ _ _ |- SRr _ _ (mkCfg _ ?md3) _ =>
  pmkst HS;
  refine (NEXT ltac:(apply Nat.ltb_lt; reflexivity) (ms_regs ms3) (ms_mem ms3) md3 _);
  exact (ca_close_next 6%nat E3 ss3 ms3 ly St W regs0 mem0 md0 md3 p0 v s3v regs HS EA ltac:(vm_compute; reflexivity) HJ Hra
    Hgp0 Htp0 HRO HROK HCE Hsp46 HK Hsp HFR R3 R4 R8 Hs3 RP0 HAOK RNAMES) end).
Qed.
Lemma ca_iter_7 : ca_iter_stmt 7.
Proof.
unfold ca_iter_stmt.
intros ROW ly St W regs0 mem0 md0 p0 v s3v regs memc mdc HP NEXT.
pose proof (ca_lseed 7%nat ly St W regs0 mem0 md0 p0 v s3v regs memc mdc HP) as HS.
destruct HP as (HJ & Hra & Hgp0 & Htp0 & HRO & HROK & HCE & Hsp46 & HK & Hsp & HFR & R3 & R4 & R8 & R18 & R19 & R20 & R21
  & R22 & R23 & R24 & Hs3 & RP0 & HAOK & RNAMES).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hes : ESTACK = 4096) by reflexivity.
unfold cfg_at. change (w64 (BASE + CE_LOOP)) with (Z_to_bv 64 (BASE + CE_LOOP)).
set (E := Eimg (Ereg regs (ca_extra s3v regs0))) in HS.
assert (HEI : img_env VAL A_LIM E) by apply Eimg_env.
assert (EA : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (ca_extra s3v regs0)) n)
  by (intros n Hn; apply Eimg_low; exact Hn).
assert (Usp : bv_unsigned (ew E 2) = spZ regs)
  by (rewrite (EA 2%nat ltac:(unfold A_TEXT; lia)), (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
(* the shadow check of row k (zero), its name pointer, the strcmp call *)
paj_run_shc RUNP RUNC HS HJ; [cl_awr |].
cl_keep_run.
(lazymatch goal with HS : st_ok _ ?E _ (restrict _ ?ms), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
  HK : ce_kept _ _ _ _ |- _ =>
let Ra0 := fresh "Ra0" in let Ra1 := fresh "Ra1" in let Rra := fresh "Rra" in
let Qsp := fresh "Qsp" in let Qgp := fresh "Qgp" in let Qtp := fresh "Qtp" in
prreg HS (10%bv : bv 5) Ra0; prreg HS (11%bv : bv 5) Ra1; prreg HS (1%bv : bv 5) Rra;
prreg HS (2%bv : bv 5) Qsp; prreg HS (3%bv : bv 5) Qgp; prreg HS (4%bv : bv 5) Qtp;
pmkst HS;
eapply SRr_bind;
[ apply (ce_strcmp_at ly St W (spZ regs0) mem0 md0 ms _ p0 v (ca_name_addr 7%nat) (ca_nm 7%nat) 3888 HJ HRO HCE HK);
  [ rewrite Ra0, (EA 8%nat ltac:(unfold A_TEXT; lia)), (ew_Ereg_nat regs _ 8 8%bv eq_refl); exact R8
  | rewrite Ra1; apply bv_eq; vm_compute; reflexivity
  | unfold spZ at 1; rewrite Qsp, Usp; exact Hsp
  | rewrite Qgp, (EA 3%nat ltac:(unfold A_TEXT; lia)), (ew_Ereg_nat regs _ 3 3%bv eq_refl), R3; exact Hgp0
  | rewrite Qtp, (EA 4%nat ltac:(unfold A_TEXT; lia)), (ew_Ereg_nat regs _ 4 4%bv eq_refl), R4; exact Htp0
  | exact Rra | lia | reflexivity | exact RP0 | exact (RNAMES 7%nat ltac:(lia)) ]
| ];
clear Ra0 Ra1 Rra Qsp Qgp Qtp; cbv beta;
intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hcmp & HK2 & Hfr2);
let HS2 := fresh "HS" in
jafter_call_keep_hi HS 1024%nat regs2 (mrestrict (w_H W) mem2) HP2 [0; 1; 2]%nat HS2;
ce_kept_regions HS2 Hfr2 HJ2;
rewrite <- restrict_mkst_fx in HS2;
lazymatch goal with HFR : ca_frame_at _ _ _ _ |- _ =>
  let HFR2 := fresh "HFR" in
  pose proof (ce_frame_call W (ms_mem ms) mem2 (spZ regs) regs0 _ _ HFR Hfr2 ltac:(lia) ltac:(lia) ltac:(lia)) as HFR2;
  clear HFR; rename HFR2 into HFR end;
clear HS HJ HK; rename HS2 into HS; rename HJ2 into HJ; rename HK2 into HK;
assert (HEI2 : img_env VAL A_LIM (havoc E 1024 (map (getr regs2) CLOB))) by (apply img_env_havoc_hi; [exact HEI | unfold A_LIM; lia]);
assert (Usp2 : bv_unsigned (ew (havoc E 1024 (map (getr regs2) CLOB)) 2) = spZ regs) by (rewrite ew_havoc_old by lia; exact Usp);
assert (EA2 : forall n, (n < A_TEXT)%nat -> ew (havoc E 1024 (map (getr regs2) CLOB)) n = ew (Ereg regs (ca_extra s3v regs0)) n)
  by (intros n Hn; rewrite ew_havoc_old by (unfold A_TEXT in Hn; lia); apply EA; exact Hn);
pose proof (ce_U_w _ _ _ (ce_havoc_a0 E 1024 regs2)) as UA; cbn [Nat.add] in UA;
clear Usp EA; rename Usp2 into Usp; rename EA2 into EA
end).
(* beqz a0 (0x87460) *)
psrr_branch_pi RUNP BR HS.
- (lazymatch goal with Hc : branch_taken _ _ _ = true, UA : U _ _ = bv_unsigned (getr ?r2 10), Hcmp : getr ?r2 10 = w64 0 <-> _ |- _ =>
  let Hv := fresh "Hv" in
  assert (Hv : v = ca_nm 7%nat) by (apply Hcmp; apply bv_eq; rewrite (ce_br_eq _ _ _ 0 UA) in Hc; apply Z.eqb_eq in Hc;
    rewrite Hc; reflexivity);
  let Hmm := fresh "Hmm" in
  assert (Hmm : fst (ca_ar 7%nat) <= s3v - 1 <= snd (ca_ar 7%nat))
    by (unfold ca_aok in HAOK; rewrite Hv, (ca_find_all 7%nat ltac:(lia)) in HAOK; exact HAOK);
  paj_run_to_shc RUNTOP HS HJ CA_SEG; [cl_awr |]; cl_keep_run;
  lazymatch goal with HS : st_ok_pi _ _ ?E3 ?ss3 (restrict _ ?ms3), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
    HK : ce_kept _ _ _ _, HFR : ca_frame_at _ _ _ _ |- SRr _ _ (mkCfg _ ?md3) _ =>
    pmkst HS;
    refine (ROW ly St W regs0 mem0 md0 W (ms_regs ms3) (ms_mem ms3) md3 s3v _ Hgp0 Htp0);
    exact (ca_close_row 7%nat _ _ E3 ss3 ms3 ly St W regs0 mem0 md0 md3 s3v regs HS EA ltac:(vm_compute; reflexivity) HJ Hra
      (ce_ro_kept W mem0 (ms_mem ms3) (spZ regs0) HROK HK HCE) Hsp HFR R3 R4 Hmm Hs3) end end).
- (paj_run_to_shc RUNTOP HS HJ CE_LOOP; [cl_awr |]; cl_keep_run;
lazymatch goal with HS : st_ok_pi _ _ ?E3 ?ss3 (restrict _ ?ms3), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
  HK : ce_kept _ _ _ _, HFR : ca_frame_at _ _ _ _ |- SRr _ _ (mkCfg _ ?md3) _ =>
  pmkst HS;
  refine (NEXT ltac:(apply Nat.ltb_lt; reflexivity) (ms_regs ms3) (ms_mem ms3) md3 _);
  exact (ca_close_next 7%nat E3 ss3 ms3 ly St W regs0 mem0 md0 md3 p0 v s3v regs HS EA ltac:(vm_compute; reflexivity) HJ Hra
    Hgp0 Htp0 HRO HROK HCE Hsp46 HK Hsp HFR R3 R4 R8 Hs3 RP0 HAOK RNAMES) end).
Qed.
Lemma ca_iter_8 : ca_iter_stmt 8.
Proof.
unfold ca_iter_stmt.
intros ROW ly St W regs0 mem0 md0 p0 v s3v regs memc mdc HP NEXT.
pose proof (ca_lseed 8%nat ly St W regs0 mem0 md0 p0 v s3v regs memc mdc HP) as HS.
destruct HP as (HJ & Hra & Hgp0 & Htp0 & HRO & HROK & HCE & Hsp46 & HK & Hsp & HFR & R3 & R4 & R8 & R18 & R19 & R20 & R21
  & R22 & R23 & R24 & Hs3 & RP0 & HAOK & RNAMES).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hes : ESTACK = 4096) by reflexivity.
unfold cfg_at. change (w64 (BASE + CE_LOOP)) with (Z_to_bv 64 (BASE + CE_LOOP)).
set (E := Eimg (Ereg regs (ca_extra s3v regs0))) in HS.
assert (HEI : img_env VAL A_LIM E) by apply Eimg_env.
assert (EA : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (ca_extra s3v regs0)) n)
  by (intros n Hn; apply Eimg_low; exact Hn).
assert (Usp : bv_unsigned (ew E 2) = spZ regs)
  by (rewrite (EA 2%nat ltac:(unfold A_TEXT; lia)), (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
(* the shadow check of row k (zero), its name pointer, the strcmp call *)
paj_run_shc RUNP RUNC HS HJ; [cl_awr |].
cl_keep_run.
(lazymatch goal with HS : st_ok _ ?E _ (restrict _ ?ms), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
  HK : ce_kept _ _ _ _ |- _ =>
let Ra0 := fresh "Ra0" in let Ra1 := fresh "Ra1" in let Rra := fresh "Rra" in
let Qsp := fresh "Qsp" in let Qgp := fresh "Qgp" in let Qtp := fresh "Qtp" in
prreg HS (10%bv : bv 5) Ra0; prreg HS (11%bv : bv 5) Ra1; prreg HS (1%bv : bv 5) Rra;
prreg HS (2%bv : bv 5) Qsp; prreg HS (3%bv : bv 5) Qgp; prreg HS (4%bv : bv 5) Qtp;
pmkst HS;
eapply SRr_bind;
[ apply (ce_strcmp_at ly St W (spZ regs0) mem0 md0 ms _ p0 v (ca_name_addr 8%nat) (ca_nm 8%nat) 3888 HJ HRO HCE HK);
  [ rewrite Ra0, (EA 8%nat ltac:(unfold A_TEXT; lia)), (ew_Ereg_nat regs _ 8 8%bv eq_refl); exact R8
  | rewrite Ra1; apply bv_eq; vm_compute; reflexivity
  | unfold spZ at 1; rewrite Qsp, Usp; exact Hsp
  | rewrite Qgp, (EA 3%nat ltac:(unfold A_TEXT; lia)), (ew_Ereg_nat regs _ 3 3%bv eq_refl), R3; exact Hgp0
  | rewrite Qtp, (EA 4%nat ltac:(unfold A_TEXT; lia)), (ew_Ereg_nat regs _ 4 4%bv eq_refl), R4; exact Htp0
  | exact Rra | lia | reflexivity | exact RP0 | exact (RNAMES 8%nat ltac:(lia)) ]
| ];
clear Ra0 Ra1 Rra Qsp Qgp Qtp; cbv beta;
intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hcmp & HK2 & Hfr2);
let HS2 := fresh "HS" in
jafter_call_keep_hi HS 1024%nat regs2 (mrestrict (w_H W) mem2) HP2 [0; 1; 2]%nat HS2;
ce_kept_regions HS2 Hfr2 HJ2;
rewrite <- restrict_mkst_fx in HS2;
lazymatch goal with HFR : ca_frame_at _ _ _ _ |- _ =>
  let HFR2 := fresh "HFR" in
  pose proof (ce_frame_call W (ms_mem ms) mem2 (spZ regs) regs0 _ _ HFR Hfr2 ltac:(lia) ltac:(lia) ltac:(lia)) as HFR2;
  clear HFR; rename HFR2 into HFR end;
clear HS HJ HK; rename HS2 into HS; rename HJ2 into HJ; rename HK2 into HK;
assert (HEI2 : img_env VAL A_LIM (havoc E 1024 (map (getr regs2) CLOB))) by (apply img_env_havoc_hi; [exact HEI | unfold A_LIM; lia]);
assert (Usp2 : bv_unsigned (ew (havoc E 1024 (map (getr regs2) CLOB)) 2) = spZ regs) by (rewrite ew_havoc_old by lia; exact Usp);
assert (EA2 : forall n, (n < A_TEXT)%nat -> ew (havoc E 1024 (map (getr regs2) CLOB)) n = ew (Ereg regs (ca_extra s3v regs0)) n)
  by (intros n Hn; rewrite ew_havoc_old by (unfold A_TEXT in Hn; lia); apply EA; exact Hn);
pose proof (ce_U_w _ _ _ (ce_havoc_a0 E 1024 regs2)) as UA; cbn [Nat.add] in UA;
clear Usp EA; rename Usp2 into Usp; rename EA2 into EA
end).
(* beqz a0 (0x87460) *)
psrr_branch_pi RUNP BR HS.
- (lazymatch goal with Hc : branch_taken _ _ _ = true, UA : U _ _ = bv_unsigned (getr ?r2 10), Hcmp : getr ?r2 10 = w64 0 <-> _ |- _ =>
  let Hv := fresh "Hv" in
  assert (Hv : v = ca_nm 8%nat) by (apply Hcmp; apply bv_eq; rewrite (ce_br_eq _ _ _ 0 UA) in Hc; apply Z.eqb_eq in Hc;
    rewrite Hc; reflexivity);
  let Hmm := fresh "Hmm" in
  assert (Hmm : fst (ca_ar 8%nat) <= s3v - 1 <= snd (ca_ar 8%nat))
    by (unfold ca_aok in HAOK; rewrite Hv, (ca_find_all 8%nat ltac:(lia)) in HAOK; exact HAOK);
  paj_run_to_shc RUNTOP HS HJ CA_SEG; [cl_awr |]; cl_keep_run;
  lazymatch goal with HS : st_ok_pi _ _ ?E3 ?ss3 (restrict _ ?ms3), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
    HK : ce_kept _ _ _ _, HFR : ca_frame_at _ _ _ _ |- SRr _ _ (mkCfg _ ?md3) _ =>
    pmkst HS;
    refine (ROW ly St W regs0 mem0 md0 W (ms_regs ms3) (ms_mem ms3) md3 s3v _ Hgp0 Htp0);
    exact (ca_close_row 8%nat _ _ E3 ss3 ms3 ly St W regs0 mem0 md0 md3 s3v regs HS EA ltac:(vm_compute; reflexivity) HJ Hra
      (ce_ro_kept W mem0 (ms_mem ms3) (spZ regs0) HROK HK HCE) Hsp HFR R3 R4 Hmm Hs3) end end).
- (paj_run_to_shc RUNTOP HS HJ CE_LOOP; [cl_awr |]; cl_keep_run;
lazymatch goal with HS : st_ok_pi _ _ ?E3 ?ss3 (restrict _ ?ms3), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
  HK : ce_kept _ _ _ _, HFR : ca_frame_at _ _ _ _ |- SRr _ _ (mkCfg _ ?md3) _ =>
  pmkst HS;
  refine (NEXT ltac:(apply Nat.ltb_lt; reflexivity) (ms_regs ms3) (ms_mem ms3) md3 _);
  exact (ca_close_next 8%nat E3 ss3 ms3 ly St W regs0 mem0 md0 md3 p0 v s3v regs HS EA ltac:(vm_compute; reflexivity) HJ Hra
    Hgp0 Htp0 HRO HROK HCE Hsp46 HK Hsp HFR R3 R4 R8 Hs3 RP0 HAOK RNAMES) end).
Qed.
Lemma ca_iter_9 : ca_iter_stmt 9.
Proof.
unfold ca_iter_stmt.
intros ROW ly St W regs0 mem0 md0 p0 v s3v regs memc mdc HP NEXT.
pose proof (ca_lseed 9%nat ly St W regs0 mem0 md0 p0 v s3v regs memc mdc HP) as HS.
destruct HP as (HJ & Hra & Hgp0 & Htp0 & HRO & HROK & HCE & Hsp46 & HK & Hsp & HFR & R3 & R4 & R8 & R18 & R19 & R20 & R21
  & R22 & R23 & R24 & Hs3 & RP0 & HAOK & RNAMES).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hes : ESTACK = 4096) by reflexivity.
unfold cfg_at. change (w64 (BASE + CE_LOOP)) with (Z_to_bv 64 (BASE + CE_LOOP)).
set (E := Eimg (Ereg regs (ca_extra s3v regs0))) in HS.
assert (HEI : img_env VAL A_LIM E) by apply Eimg_env.
assert (EA : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (ca_extra s3v regs0)) n)
  by (intros n Hn; apply Eimg_low; exact Hn).
assert (Usp : bv_unsigned (ew E 2) = spZ regs)
  by (rewrite (EA 2%nat ltac:(unfold A_TEXT; lia)), (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
(* the shadow check of row k (zero), its name pointer, the strcmp call *)
paj_run_shc RUNP RUNC HS HJ; [cl_awr |].
cl_keep_run.
(lazymatch goal with HS : st_ok _ ?E _ (restrict _ ?ms), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
  HK : ce_kept _ _ _ _ |- _ =>
let Ra0 := fresh "Ra0" in let Ra1 := fresh "Ra1" in let Rra := fresh "Rra" in
let Qsp := fresh "Qsp" in let Qgp := fresh "Qgp" in let Qtp := fresh "Qtp" in
prreg HS (10%bv : bv 5) Ra0; prreg HS (11%bv : bv 5) Ra1; prreg HS (1%bv : bv 5) Rra;
prreg HS (2%bv : bv 5) Qsp; prreg HS (3%bv : bv 5) Qgp; prreg HS (4%bv : bv 5) Qtp;
pmkst HS;
eapply SRr_bind;
[ apply (ce_strcmp_at ly St W (spZ regs0) mem0 md0 ms _ p0 v (ca_name_addr 9%nat) (ca_nm 9%nat) 3888 HJ HRO HCE HK);
  [ rewrite Ra0, (EA 8%nat ltac:(unfold A_TEXT; lia)), (ew_Ereg_nat regs _ 8 8%bv eq_refl); exact R8
  | rewrite Ra1; apply bv_eq; vm_compute; reflexivity
  | unfold spZ at 1; rewrite Qsp, Usp; exact Hsp
  | rewrite Qgp, (EA 3%nat ltac:(unfold A_TEXT; lia)), (ew_Ereg_nat regs _ 3 3%bv eq_refl), R3; exact Hgp0
  | rewrite Qtp, (EA 4%nat ltac:(unfold A_TEXT; lia)), (ew_Ereg_nat regs _ 4 4%bv eq_refl), R4; exact Htp0
  | exact Rra | lia | reflexivity | exact RP0 | exact (RNAMES 9%nat ltac:(lia)) ]
| ];
clear Ra0 Ra1 Rra Qsp Qgp Qtp; cbv beta;
intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hcmp & HK2 & Hfr2);
let HS2 := fresh "HS" in
jafter_call_keep_hi HS 1024%nat regs2 (mrestrict (w_H W) mem2) HP2 [0; 1; 2]%nat HS2;
ce_kept_regions HS2 Hfr2 HJ2;
rewrite <- restrict_mkst_fx in HS2;
lazymatch goal with HFR : ca_frame_at _ _ _ _ |- _ =>
  let HFR2 := fresh "HFR" in
  pose proof (ce_frame_call W (ms_mem ms) mem2 (spZ regs) regs0 _ _ HFR Hfr2 ltac:(lia) ltac:(lia) ltac:(lia)) as HFR2;
  clear HFR; rename HFR2 into HFR end;
clear HS HJ HK; rename HS2 into HS; rename HJ2 into HJ; rename HK2 into HK;
assert (HEI2 : img_env VAL A_LIM (havoc E 1024 (map (getr regs2) CLOB))) by (apply img_env_havoc_hi; [exact HEI | unfold A_LIM; lia]);
assert (Usp2 : bv_unsigned (ew (havoc E 1024 (map (getr regs2) CLOB)) 2) = spZ regs) by (rewrite ew_havoc_old by lia; exact Usp);
assert (EA2 : forall n, (n < A_TEXT)%nat -> ew (havoc E 1024 (map (getr regs2) CLOB)) n = ew (Ereg regs (ca_extra s3v regs0)) n)
  by (intros n Hn; rewrite ew_havoc_old by (unfold A_TEXT in Hn; lia); apply EA; exact Hn);
pose proof (ce_U_w _ _ _ (ce_havoc_a0 E 1024 regs2)) as UA; cbn [Nat.add] in UA;
clear Usp EA; rename Usp2 into Usp; rename EA2 into EA
end).
(* beqz a0 (0x87460) *)
psrr_branch_pi RUNP BR HS.
- (lazymatch goal with Hc : branch_taken _ _ _ = true, UA : U _ _ = bv_unsigned (getr ?r2 10), Hcmp : getr ?r2 10 = w64 0 <-> _ |- _ =>
  let Hv := fresh "Hv" in
  assert (Hv : v = ca_nm 9%nat) by (apply Hcmp; apply bv_eq; rewrite (ce_br_eq _ _ _ 0 UA) in Hc; apply Z.eqb_eq in Hc;
    rewrite Hc; reflexivity);
  let Hmm := fresh "Hmm" in
  assert (Hmm : fst (ca_ar 9%nat) <= s3v - 1 <= snd (ca_ar 9%nat))
    by (unfold ca_aok in HAOK; rewrite Hv, (ca_find_all 9%nat ltac:(lia)) in HAOK; exact HAOK);
  paj_run_to_shc RUNTOP HS HJ CA_SEG; [cl_awr |]; cl_keep_run;
  lazymatch goal with HS : st_ok_pi _ _ ?E3 ?ss3 (restrict _ ?ms3), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
    HK : ce_kept _ _ _ _, HFR : ca_frame_at _ _ _ _ |- SRr _ _ (mkCfg _ ?md3) _ =>
    pmkst HS;
    refine (ROW ly St W regs0 mem0 md0 W (ms_regs ms3) (ms_mem ms3) md3 s3v _ Hgp0 Htp0);
    exact (ca_close_row 9%nat _ _ E3 ss3 ms3 ly St W regs0 mem0 md0 md3 s3v regs HS EA ltac:(vm_compute; reflexivity) HJ Hra
      (ce_ro_kept W mem0 (ms_mem ms3) (spZ regs0) HROK HK HCE) Hsp HFR R3 R4 Hmm Hs3) end end).
- (paj_run_to_shc RUNTOP HS HJ CE_LOOP; [cl_awr |]; cl_keep_run;
lazymatch goal with HS : st_ok_pi _ _ ?E3 ?ss3 (restrict _ ?ms3), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
  HK : ce_kept _ _ _ _, HFR : ca_frame_at _ _ _ _ |- SRr _ _ (mkCfg _ ?md3) _ =>
  pmkst HS;
  refine (NEXT ltac:(apply Nat.ltb_lt; reflexivity) (ms_regs ms3) (ms_mem ms3) md3 _);
  exact (ca_close_next 9%nat E3 ss3 ms3 ly St W regs0 mem0 md0 md3 p0 v s3v regs HS EA ltac:(vm_compute; reflexivity) HJ Hra
    Hgp0 Htp0 HRO HROK HCE Hsp46 HK Hsp HFR R3 R4 R8 Hs3 RP0 HAOK RNAMES) end).
Qed.
Lemma ca_iter_10 : ca_iter_stmt 10.
Proof.
unfold ca_iter_stmt.
intros ROW ly St W regs0 mem0 md0 p0 v s3v regs memc mdc HP NEXT.
pose proof (ca_lseed 10%nat ly St W regs0 mem0 md0 p0 v s3v regs memc mdc HP) as HS.
destruct HP as (HJ & Hra & Hgp0 & Htp0 & HRO & HROK & HCE & Hsp46 & HK & Hsp & HFR & R3 & R4 & R8 & R18 & R19 & R20 & R21
  & R22 & R23 & R24 & Hs3 & RP0 & HAOK & RNAMES).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hes : ESTACK = 4096) by reflexivity.
unfold cfg_at. change (w64 (BASE + CE_LOOP)) with (Z_to_bv 64 (BASE + CE_LOOP)).
set (E := Eimg (Ereg regs (ca_extra s3v regs0))) in HS.
assert (HEI : img_env VAL A_LIM E) by apply Eimg_env.
assert (EA : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (ca_extra s3v regs0)) n)
  by (intros n Hn; apply Eimg_low; exact Hn).
assert (Usp : bv_unsigned (ew E 2) = spZ regs)
  by (rewrite (EA 2%nat ltac:(unfold A_TEXT; lia)), (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
(* the shadow check of row k (zero), its name pointer, the strcmp call *)
paj_run_shc RUNP RUNC HS HJ; [cl_awr |].
cl_keep_run.
(lazymatch goal with HS : st_ok _ ?E _ (restrict _ ?ms), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
  HK : ce_kept _ _ _ _ |- _ =>
let Ra0 := fresh "Ra0" in let Ra1 := fresh "Ra1" in let Rra := fresh "Rra" in
let Qsp := fresh "Qsp" in let Qgp := fresh "Qgp" in let Qtp := fresh "Qtp" in
prreg HS (10%bv : bv 5) Ra0; prreg HS (11%bv : bv 5) Ra1; prreg HS (1%bv : bv 5) Rra;
prreg HS (2%bv : bv 5) Qsp; prreg HS (3%bv : bv 5) Qgp; prreg HS (4%bv : bv 5) Qtp;
pmkst HS;
eapply SRr_bind;
[ apply (ce_strcmp_at ly St W (spZ regs0) mem0 md0 ms _ p0 v (ca_name_addr 10%nat) (ca_nm 10%nat) 3888 HJ HRO HCE HK);
  [ rewrite Ra0, (EA 8%nat ltac:(unfold A_TEXT; lia)), (ew_Ereg_nat regs _ 8 8%bv eq_refl); exact R8
  | rewrite Ra1; apply bv_eq; vm_compute; reflexivity
  | unfold spZ at 1; rewrite Qsp, Usp; exact Hsp
  | rewrite Qgp, (EA 3%nat ltac:(unfold A_TEXT; lia)), (ew_Ereg_nat regs _ 3 3%bv eq_refl), R3; exact Hgp0
  | rewrite Qtp, (EA 4%nat ltac:(unfold A_TEXT; lia)), (ew_Ereg_nat regs _ 4 4%bv eq_refl), R4; exact Htp0
  | exact Rra | lia | reflexivity | exact RP0 | exact (RNAMES 10%nat ltac:(lia)) ]
| ];
clear Ra0 Ra1 Rra Qsp Qgp Qtp; cbv beta;
intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hcmp & HK2 & Hfr2);
let HS2 := fresh "HS" in
jafter_call_keep_hi HS 1024%nat regs2 (mrestrict (w_H W) mem2) HP2 [0; 1; 2]%nat HS2;
ce_kept_regions HS2 Hfr2 HJ2;
rewrite <- restrict_mkst_fx in HS2;
lazymatch goal with HFR : ca_frame_at _ _ _ _ |- _ =>
  let HFR2 := fresh "HFR" in
  pose proof (ce_frame_call W (ms_mem ms) mem2 (spZ regs) regs0 _ _ HFR Hfr2 ltac:(lia) ltac:(lia) ltac:(lia)) as HFR2;
  clear HFR; rename HFR2 into HFR end;
clear HS HJ HK; rename HS2 into HS; rename HJ2 into HJ; rename HK2 into HK;
assert (HEI2 : img_env VAL A_LIM (havoc E 1024 (map (getr regs2) CLOB))) by (apply img_env_havoc_hi; [exact HEI | unfold A_LIM; lia]);
assert (Usp2 : bv_unsigned (ew (havoc E 1024 (map (getr regs2) CLOB)) 2) = spZ regs) by (rewrite ew_havoc_old by lia; exact Usp);
assert (EA2 : forall n, (n < A_TEXT)%nat -> ew (havoc E 1024 (map (getr regs2) CLOB)) n = ew (Ereg regs (ca_extra s3v regs0)) n)
  by (intros n Hn; rewrite ew_havoc_old by (unfold A_TEXT in Hn; lia); apply EA; exact Hn);
pose proof (ce_U_w _ _ _ (ce_havoc_a0 E 1024 regs2)) as UA; cbn [Nat.add] in UA;
clear Usp EA; rename Usp2 into Usp; rename EA2 into EA
end).
(* beqz a0 (0x87460) *)
psrr_branch_pi RUNP BR HS.
- (lazymatch goal with Hc : branch_taken _ _ _ = true, UA : U _ _ = bv_unsigned (getr ?r2 10), Hcmp : getr ?r2 10 = w64 0 <-> _ |- _ =>
  let Hv := fresh "Hv" in
  assert (Hv : v = ca_nm 10%nat) by (apply Hcmp; apply bv_eq; rewrite (ce_br_eq _ _ _ 0 UA) in Hc; apply Z.eqb_eq in Hc;
    rewrite Hc; reflexivity);
  let Hmm := fresh "Hmm" in
  assert (Hmm : fst (ca_ar 10%nat) <= s3v - 1 <= snd (ca_ar 10%nat))
    by (unfold ca_aok in HAOK; rewrite Hv, (ca_find_all 10%nat ltac:(lia)) in HAOK; exact HAOK);
  paj_run_to_shc RUNTOP HS HJ CA_SEG; [cl_awr |]; cl_keep_run;
  lazymatch goal with HS : st_ok_pi _ _ ?E3 ?ss3 (restrict _ ?ms3), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
    HK : ce_kept _ _ _ _, HFR : ca_frame_at _ _ _ _ |- SRr _ _ (mkCfg _ ?md3) _ =>
    pmkst HS;
    refine (ROW ly St W regs0 mem0 md0 W (ms_regs ms3) (ms_mem ms3) md3 s3v _ Hgp0 Htp0);
    exact (ca_close_row 10%nat _ _ E3 ss3 ms3 ly St W regs0 mem0 md0 md3 s3v regs HS EA ltac:(vm_compute; reflexivity) HJ Hra
      (ce_ro_kept W mem0 (ms_mem ms3) (spZ regs0) HROK HK HCE) Hsp HFR R3 R4 Hmm Hs3) end end).
- (paj_run_to_shc RUNTOP HS HJ CE_LOOP; [cl_awr |]; cl_keep_run;
lazymatch goal with HS : st_ok_pi _ _ ?E3 ?ss3 (restrict _ ?ms3), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
  HK : ce_kept _ _ _ _, HFR : ca_frame_at _ _ _ _ |- SRr _ _ (mkCfg _ ?md3) _ =>
  pmkst HS;
  refine (NEXT ltac:(apply Nat.ltb_lt; reflexivity) (ms_regs ms3) (ms_mem ms3) md3 _);
  exact (ca_close_next 10%nat E3 ss3 ms3 ly St W regs0 mem0 md0 md3 p0 v s3v regs HS EA ltac:(vm_compute; reflexivity) HJ Hra
    Hgp0 Htp0 HRO HROK HCE Hsp46 HK Hsp HFR R3 R4 R8 Hs3 RP0 HAOK RNAMES) end).
Qed.
Lemma ca_iter_11 : ca_iter_stmt 11.
Proof.
unfold ca_iter_stmt.
intros ROW ly St W regs0 mem0 md0 p0 v s3v regs memc mdc HP NEXT.
pose proof (ca_lseed 11%nat ly St W regs0 mem0 md0 p0 v s3v regs memc mdc HP) as HS.
destruct HP as (HJ & Hra & Hgp0 & Htp0 & HRO & HROK & HCE & Hsp46 & HK & Hsp & HFR & R3 & R4 & R8 & R18 & R19 & R20 & R21
  & R22 & R23 & R24 & Hs3 & RP0 & HAOK & RNAMES).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hes : ESTACK = 4096) by reflexivity.
unfold cfg_at. change (w64 (BASE + CE_LOOP)) with (Z_to_bv 64 (BASE + CE_LOOP)).
set (E := Eimg (Ereg regs (ca_extra s3v regs0))) in HS.
assert (HEI : img_env VAL A_LIM E) by apply Eimg_env.
assert (EA : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (ca_extra s3v regs0)) n)
  by (intros n Hn; apply Eimg_low; exact Hn).
assert (Usp : bv_unsigned (ew E 2) = spZ regs)
  by (rewrite (EA 2%nat ltac:(unfold A_TEXT; lia)), (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
(* the shadow check of row k (zero), its name pointer, the strcmp call *)
paj_run_shc RUNP RUNC HS HJ; [cl_awr |].
cl_keep_run.
(lazymatch goal with HS : st_ok _ ?E _ (restrict _ ?ms), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
  HK : ce_kept _ _ _ _ |- _ =>
let Ra0 := fresh "Ra0" in let Ra1 := fresh "Ra1" in let Rra := fresh "Rra" in
let Qsp := fresh "Qsp" in let Qgp := fresh "Qgp" in let Qtp := fresh "Qtp" in
prreg HS (10%bv : bv 5) Ra0; prreg HS (11%bv : bv 5) Ra1; prreg HS (1%bv : bv 5) Rra;
prreg HS (2%bv : bv 5) Qsp; prreg HS (3%bv : bv 5) Qgp; prreg HS (4%bv : bv 5) Qtp;
pmkst HS;
eapply SRr_bind;
[ apply (ce_strcmp_at ly St W (spZ regs0) mem0 md0 ms _ p0 v (ca_name_addr 11%nat) (ca_nm 11%nat) 3888 HJ HRO HCE HK);
  [ rewrite Ra0, (EA 8%nat ltac:(unfold A_TEXT; lia)), (ew_Ereg_nat regs _ 8 8%bv eq_refl); exact R8
  | rewrite Ra1; apply bv_eq; vm_compute; reflexivity
  | unfold spZ at 1; rewrite Qsp, Usp; exact Hsp
  | rewrite Qgp, (EA 3%nat ltac:(unfold A_TEXT; lia)), (ew_Ereg_nat regs _ 3 3%bv eq_refl), R3; exact Hgp0
  | rewrite Qtp, (EA 4%nat ltac:(unfold A_TEXT; lia)), (ew_Ereg_nat regs _ 4 4%bv eq_refl), R4; exact Htp0
  | exact Rra | lia | reflexivity | exact RP0 | exact (RNAMES 11%nat ltac:(lia)) ]
| ];
clear Ra0 Ra1 Rra Qsp Qgp Qtp; cbv beta;
intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hcmp & HK2 & Hfr2);
let HS2 := fresh "HS" in
jafter_call_keep_hi HS 1024%nat regs2 (mrestrict (w_H W) mem2) HP2 [0; 1; 2]%nat HS2;
ce_kept_regions HS2 Hfr2 HJ2;
rewrite <- restrict_mkst_fx in HS2;
lazymatch goal with HFR : ca_frame_at _ _ _ _ |- _ =>
  let HFR2 := fresh "HFR" in
  pose proof (ce_frame_call W (ms_mem ms) mem2 (spZ regs) regs0 _ _ HFR Hfr2 ltac:(lia) ltac:(lia) ltac:(lia)) as HFR2;
  clear HFR; rename HFR2 into HFR end;
clear HS HJ HK; rename HS2 into HS; rename HJ2 into HJ; rename HK2 into HK;
assert (HEI2 : img_env VAL A_LIM (havoc E 1024 (map (getr regs2) CLOB))) by (apply img_env_havoc_hi; [exact HEI | unfold A_LIM; lia]);
assert (Usp2 : bv_unsigned (ew (havoc E 1024 (map (getr regs2) CLOB)) 2) = spZ regs) by (rewrite ew_havoc_old by lia; exact Usp);
assert (EA2 : forall n, (n < A_TEXT)%nat -> ew (havoc E 1024 (map (getr regs2) CLOB)) n = ew (Ereg regs (ca_extra s3v regs0)) n)
  by (intros n Hn; rewrite ew_havoc_old by (unfold A_TEXT in Hn; lia); apply EA; exact Hn);
pose proof (ce_U_w _ _ _ (ce_havoc_a0 E 1024 regs2)) as UA; cbn [Nat.add] in UA;
clear Usp EA; rename Usp2 into Usp; rename EA2 into EA
end).
(* beqz a0 (0x87460) *)
psrr_branch_pi RUNP BR HS.
- (lazymatch goal with Hc : branch_taken _ _ _ = true, UA : U _ _ = bv_unsigned (getr ?r2 10), Hcmp : getr ?r2 10 = w64 0 <-> _ |- _ =>
  let Hv := fresh "Hv" in
  assert (Hv : v = ca_nm 11%nat) by (apply Hcmp; apply bv_eq; rewrite (ce_br_eq _ _ _ 0 UA) in Hc; apply Z.eqb_eq in Hc;
    rewrite Hc; reflexivity);
  let Hmm := fresh "Hmm" in
  assert (Hmm : fst (ca_ar 11%nat) <= s3v - 1 <= snd (ca_ar 11%nat))
    by (unfold ca_aok in HAOK; rewrite Hv, (ca_find_all 11%nat ltac:(lia)) in HAOK; exact HAOK);
  paj_run_to_shc RUNTOP HS HJ CA_SEG; [cl_awr |]; cl_keep_run;
  lazymatch goal with HS : st_ok_pi _ _ ?E3 ?ss3 (restrict _ ?ms3), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
    HK : ce_kept _ _ _ _, HFR : ca_frame_at _ _ _ _ |- SRr _ _ (mkCfg _ ?md3) _ =>
    pmkst HS;
    refine (ROW ly St W regs0 mem0 md0 W (ms_regs ms3) (ms_mem ms3) md3 s3v _ Hgp0 Htp0);
    exact (ca_close_row 11%nat _ _ E3 ss3 ms3 ly St W regs0 mem0 md0 md3 s3v regs HS EA ltac:(vm_compute; reflexivity) HJ Hra
      (ce_ro_kept W mem0 (ms_mem ms3) (spZ regs0) HROK HK HCE) Hsp HFR R3 R4 Hmm Hs3) end end).
- (paj_run_to_shc RUNTOP HS HJ CE_LOOP; [cl_awr |]; cl_keep_run;
lazymatch goal with HS : st_ok_pi _ _ ?E3 ?ss3 (restrict _ ?ms3), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
  HK : ce_kept _ _ _ _, HFR : ca_frame_at _ _ _ _ |- SRr _ _ (mkCfg _ ?md3) _ =>
  pmkst HS;
  refine (NEXT ltac:(apply Nat.ltb_lt; reflexivity) (ms_regs ms3) (ms_mem ms3) md3 _);
  exact (ca_close_next 11%nat E3 ss3 ms3 ly St W regs0 mem0 md0 md3 p0 v s3v regs HS EA ltac:(vm_compute; reflexivity) HJ Hra
    Hgp0 Htp0 HRO HROK HCE Hsp46 HK Hsp HFR R3 R4 R8 Hs3 RP0 HAOK RNAMES) end).
Qed.
Lemma ca_iter_12 : ca_iter_stmt 12.
Proof.
unfold ca_iter_stmt.
intros ROW ly St W regs0 mem0 md0 p0 v s3v regs memc mdc HP NEXT.
pose proof (ca_lseed 12%nat ly St W regs0 mem0 md0 p0 v s3v regs memc mdc HP) as HS.
destruct HP as (HJ & Hra & Hgp0 & Htp0 & HRO & HROK & HCE & Hsp46 & HK & Hsp & HFR & R3 & R4 & R8 & R18 & R19 & R20 & R21
  & R22 & R23 & R24 & Hs3 & RP0 & HAOK & RNAMES).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hes : ESTACK = 4096) by reflexivity.
unfold cfg_at. change (w64 (BASE + CE_LOOP)) with (Z_to_bv 64 (BASE + CE_LOOP)).
set (E := Eimg (Ereg regs (ca_extra s3v regs0))) in HS.
assert (HEI : img_env VAL A_LIM E) by apply Eimg_env.
assert (EA : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (ca_extra s3v regs0)) n)
  by (intros n Hn; apply Eimg_low; exact Hn).
assert (Usp : bv_unsigned (ew E 2) = spZ regs)
  by (rewrite (EA 2%nat ltac:(unfold A_TEXT; lia)), (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
(* the shadow check of row k (zero), its name pointer, the strcmp call *)
paj_run_shc RUNP RUNC HS HJ; [cl_awr |].
cl_keep_run.
(lazymatch goal with HS : st_ok _ ?E _ (restrict _ ?ms), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
  HK : ce_kept _ _ _ _ |- _ =>
let Ra0 := fresh "Ra0" in let Ra1 := fresh "Ra1" in let Rra := fresh "Rra" in
let Qsp := fresh "Qsp" in let Qgp := fresh "Qgp" in let Qtp := fresh "Qtp" in
prreg HS (10%bv : bv 5) Ra0; prreg HS (11%bv : bv 5) Ra1; prreg HS (1%bv : bv 5) Rra;
prreg HS (2%bv : bv 5) Qsp; prreg HS (3%bv : bv 5) Qgp; prreg HS (4%bv : bv 5) Qtp;
pmkst HS;
eapply SRr_bind;
[ apply (ce_strcmp_at ly St W (spZ regs0) mem0 md0 ms _ p0 v (ca_name_addr 12%nat) (ca_nm 12%nat) 3888 HJ HRO HCE HK);
  [ rewrite Ra0, (EA 8%nat ltac:(unfold A_TEXT; lia)), (ew_Ereg_nat regs _ 8 8%bv eq_refl); exact R8
  | rewrite Ra1; apply bv_eq; vm_compute; reflexivity
  | unfold spZ at 1; rewrite Qsp, Usp; exact Hsp
  | rewrite Qgp, (EA 3%nat ltac:(unfold A_TEXT; lia)), (ew_Ereg_nat regs _ 3 3%bv eq_refl), R3; exact Hgp0
  | rewrite Qtp, (EA 4%nat ltac:(unfold A_TEXT; lia)), (ew_Ereg_nat regs _ 4 4%bv eq_refl), R4; exact Htp0
  | exact Rra | lia | reflexivity | exact RP0 | exact (RNAMES 12%nat ltac:(lia)) ]
| ];
clear Ra0 Ra1 Rra Qsp Qgp Qtp; cbv beta;
intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hcmp & HK2 & Hfr2);
let HS2 := fresh "HS" in
jafter_call_keep_hi HS 1024%nat regs2 (mrestrict (w_H W) mem2) HP2 [0; 1; 2]%nat HS2;
ce_kept_regions HS2 Hfr2 HJ2;
rewrite <- restrict_mkst_fx in HS2;
lazymatch goal with HFR : ca_frame_at _ _ _ _ |- _ =>
  let HFR2 := fresh "HFR" in
  pose proof (ce_frame_call W (ms_mem ms) mem2 (spZ regs) regs0 _ _ HFR Hfr2 ltac:(lia) ltac:(lia) ltac:(lia)) as HFR2;
  clear HFR; rename HFR2 into HFR end;
clear HS HJ HK; rename HS2 into HS; rename HJ2 into HJ; rename HK2 into HK;
assert (HEI2 : img_env VAL A_LIM (havoc E 1024 (map (getr regs2) CLOB))) by (apply img_env_havoc_hi; [exact HEI | unfold A_LIM; lia]);
assert (Usp2 : bv_unsigned (ew (havoc E 1024 (map (getr regs2) CLOB)) 2) = spZ regs) by (rewrite ew_havoc_old by lia; exact Usp);
assert (EA2 : forall n, (n < A_TEXT)%nat -> ew (havoc E 1024 (map (getr regs2) CLOB)) n = ew (Ereg regs (ca_extra s3v regs0)) n)
  by (intros n Hn; rewrite ew_havoc_old by (unfold A_TEXT in Hn; lia); apply EA; exact Hn);
pose proof (ce_U_w _ _ _ (ce_havoc_a0 E 1024 regs2)) as UA; cbn [Nat.add] in UA;
clear Usp EA; rename Usp2 into Usp; rename EA2 into EA
end).
(* beqz a0 (0x87460) *)
psrr_branch_pi RUNP BR HS.
- (lazymatch goal with Hc : branch_taken _ _ _ = true, UA : U _ _ = bv_unsigned (getr ?r2 10), Hcmp : getr ?r2 10 = w64 0 <-> _ |- _ =>
  let Hv := fresh "Hv" in
  assert (Hv : v = ca_nm 12%nat) by (apply Hcmp; apply bv_eq; rewrite (ce_br_eq _ _ _ 0 UA) in Hc; apply Z.eqb_eq in Hc;
    rewrite Hc; reflexivity);
  let Hmm := fresh "Hmm" in
  assert (Hmm : fst (ca_ar 12%nat) <= s3v - 1 <= snd (ca_ar 12%nat))
    by (unfold ca_aok in HAOK; rewrite Hv, (ca_find_all 12%nat ltac:(lia)) in HAOK; exact HAOK);
  paj_run_to_shc RUNTOP HS HJ CA_SEG; [cl_awr |]; cl_keep_run;
  lazymatch goal with HS : st_ok_pi _ _ ?E3 ?ss3 (restrict _ ?ms3), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
    HK : ce_kept _ _ _ _, HFR : ca_frame_at _ _ _ _ |- SRr _ _ (mkCfg _ ?md3) _ =>
    pmkst HS;
    refine (ROW ly St W regs0 mem0 md0 W (ms_regs ms3) (ms_mem ms3) md3 s3v _ Hgp0 Htp0);
    exact (ca_close_row 12%nat _ _ E3 ss3 ms3 ly St W regs0 mem0 md0 md3 s3v regs HS EA ltac:(vm_compute; reflexivity) HJ Hra
      (ce_ro_kept W mem0 (ms_mem ms3) (spZ regs0) HROK HK HCE) Hsp HFR R3 R4 Hmm Hs3) end end).
- (paj_run_to_shc RUNTOP HS HJ CE_LOOP; [cl_awr |]; cl_keep_run;
lazymatch goal with HS : st_ok_pi _ _ ?E3 ?ss3 (restrict _ ?ms3), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
  HK : ce_kept _ _ _ _, HFR : ca_frame_at _ _ _ _ |- SRr _ _ (mkCfg _ ?md3) _ =>
  pmkst HS;
  refine (NEXT ltac:(apply Nat.ltb_lt; reflexivity) (ms_regs ms3) (ms_mem ms3) md3 _);
  exact (ca_close_next 12%nat E3 ss3 ms3 ly St W regs0 mem0 md0 md3 p0 v s3v regs HS EA ltac:(vm_compute; reflexivity) HJ Hra
    Hgp0 Htp0 HRO HROK HCE Hsp46 HK Hsp HFR R3 R4 R8 Hs3 RP0 HAOK RNAMES) end).
Qed.
Lemma ca_iter_13 : ca_iter_stmt 13.
Proof.
unfold ca_iter_stmt.
intros ROW ly St W regs0 mem0 md0 p0 v s3v regs memc mdc HP NEXT.
pose proof (ca_lseed 13%nat ly St W regs0 mem0 md0 p0 v s3v regs memc mdc HP) as HS.
destruct HP as (HJ & Hra & Hgp0 & Htp0 & HRO & HROK & HCE & Hsp46 & HK & Hsp & HFR & R3 & R4 & R8 & R18 & R19 & R20 & R21
  & R22 & R23 & R24 & Hs3 & RP0 & HAOK & RNAMES).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hes : ESTACK = 4096) by reflexivity.
unfold cfg_at. change (w64 (BASE + CE_LOOP)) with (Z_to_bv 64 (BASE + CE_LOOP)).
set (E := Eimg (Ereg regs (ca_extra s3v regs0))) in HS.
assert (HEI : img_env VAL A_LIM E) by apply Eimg_env.
assert (EA : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (ca_extra s3v regs0)) n)
  by (intros n Hn; apply Eimg_low; exact Hn).
assert (Usp : bv_unsigned (ew E 2) = spZ regs)
  by (rewrite (EA 2%nat ltac:(unfold A_TEXT; lia)), (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
(* the shadow check of row k (zero), its name pointer, the strcmp call *)
paj_run_shc RUNP RUNC HS HJ; [cl_awr |].
cl_keep_run.
(lazymatch goal with HS : st_ok _ ?E _ (restrict _ ?ms), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
  HK : ce_kept _ _ _ _ |- _ =>
let Ra0 := fresh "Ra0" in let Ra1 := fresh "Ra1" in let Rra := fresh "Rra" in
let Qsp := fresh "Qsp" in let Qgp := fresh "Qgp" in let Qtp := fresh "Qtp" in
prreg HS (10%bv : bv 5) Ra0; prreg HS (11%bv : bv 5) Ra1; prreg HS (1%bv : bv 5) Rra;
prreg HS (2%bv : bv 5) Qsp; prreg HS (3%bv : bv 5) Qgp; prreg HS (4%bv : bv 5) Qtp;
pmkst HS;
eapply SRr_bind;
[ apply (ce_strcmp_at ly St W (spZ regs0) mem0 md0 ms _ p0 v (ca_name_addr 13%nat) (ca_nm 13%nat) 3888 HJ HRO HCE HK);
  [ rewrite Ra0, (EA 8%nat ltac:(unfold A_TEXT; lia)), (ew_Ereg_nat regs _ 8 8%bv eq_refl); exact R8
  | rewrite Ra1; apply bv_eq; vm_compute; reflexivity
  | unfold spZ at 1; rewrite Qsp, Usp; exact Hsp
  | rewrite Qgp, (EA 3%nat ltac:(unfold A_TEXT; lia)), (ew_Ereg_nat regs _ 3 3%bv eq_refl), R3; exact Hgp0
  | rewrite Qtp, (EA 4%nat ltac:(unfold A_TEXT; lia)), (ew_Ereg_nat regs _ 4 4%bv eq_refl), R4; exact Htp0
  | exact Rra | lia | reflexivity | exact RP0 | exact (RNAMES 13%nat ltac:(lia)) ]
| ];
clear Ra0 Ra1 Rra Qsp Qgp Qtp; cbv beta;
intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hcmp & HK2 & Hfr2);
let HS2 := fresh "HS" in
jafter_call_keep_hi HS 1024%nat regs2 (mrestrict (w_H W) mem2) HP2 [0; 1; 2]%nat HS2;
ce_kept_regions HS2 Hfr2 HJ2;
rewrite <- restrict_mkst_fx in HS2;
lazymatch goal with HFR : ca_frame_at _ _ _ _ |- _ =>
  let HFR2 := fresh "HFR" in
  pose proof (ce_frame_call W (ms_mem ms) mem2 (spZ regs) regs0 _ _ HFR Hfr2 ltac:(lia) ltac:(lia) ltac:(lia)) as HFR2;
  clear HFR; rename HFR2 into HFR end;
clear HS HJ HK; rename HS2 into HS; rename HJ2 into HJ; rename HK2 into HK;
assert (HEI2 : img_env VAL A_LIM (havoc E 1024 (map (getr regs2) CLOB))) by (apply img_env_havoc_hi; [exact HEI | unfold A_LIM; lia]);
assert (Usp2 : bv_unsigned (ew (havoc E 1024 (map (getr regs2) CLOB)) 2) = spZ regs) by (rewrite ew_havoc_old by lia; exact Usp);
assert (EA2 : forall n, (n < A_TEXT)%nat -> ew (havoc E 1024 (map (getr regs2) CLOB)) n = ew (Ereg regs (ca_extra s3v regs0)) n)
  by (intros n Hn; rewrite ew_havoc_old by (unfold A_TEXT in Hn; lia); apply EA; exact Hn);
pose proof (ce_U_w _ _ _ (ce_havoc_a0 E 1024 regs2)) as UA; cbn [Nat.add] in UA;
clear Usp EA; rename Usp2 into Usp; rename EA2 into EA
end).
(* beqz a0 (0x87460) *)
psrr_branch_pi RUNP BR HS.
- (lazymatch goal with Hc : branch_taken _ _ _ = true, UA : U _ _ = bv_unsigned (getr ?r2 10), Hcmp : getr ?r2 10 = w64 0 <-> _ |- _ =>
  let Hv := fresh "Hv" in
  assert (Hv : v = ca_nm 13%nat) by (apply Hcmp; apply bv_eq; rewrite (ce_br_eq _ _ _ 0 UA) in Hc; apply Z.eqb_eq in Hc;
    rewrite Hc; reflexivity);
  let Hmm := fresh "Hmm" in
  assert (Hmm : fst (ca_ar 13%nat) <= s3v - 1 <= snd (ca_ar 13%nat))
    by (unfold ca_aok in HAOK; rewrite Hv, (ca_find_all 13%nat ltac:(lia)) in HAOK; exact HAOK);
  paj_run_to_shc RUNTOP HS HJ CA_SEG; [cl_awr |]; cl_keep_run;
  lazymatch goal with HS : st_ok_pi _ _ ?E3 ?ss3 (restrict _ ?ms3), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
    HK : ce_kept _ _ _ _, HFR : ca_frame_at _ _ _ _ |- SRr _ _ (mkCfg _ ?md3) _ =>
    pmkst HS;
    refine (ROW ly St W regs0 mem0 md0 W (ms_regs ms3) (ms_mem ms3) md3 s3v _ Hgp0 Htp0);
    exact (ca_close_row 13%nat _ _ E3 ss3 ms3 ly St W regs0 mem0 md0 md3 s3v regs HS EA ltac:(vm_compute; reflexivity) HJ Hra
      (ce_ro_kept W mem0 (ms_mem ms3) (spZ regs0) HROK HK HCE) Hsp HFR R3 R4 Hmm Hs3) end end).
- (paj_run_to_shc RUNTOP HS HJ CE_LOOP; [cl_awr |]; cl_keep_run;
lazymatch goal with HS : st_ok_pi _ _ ?E3 ?ss3 (restrict _ ?ms3), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
  HK : ce_kept _ _ _ _, HFR : ca_frame_at _ _ _ _ |- SRr _ _ (mkCfg _ ?md3) _ =>
  pmkst HS;
  refine (NEXT ltac:(apply Nat.ltb_lt; reflexivity) (ms_regs ms3) (ms_mem ms3) md3 _);
  exact (ca_close_next 13%nat E3 ss3 ms3 ly St W regs0 mem0 md0 md3 p0 v s3v regs HS EA ltac:(vm_compute; reflexivity) HJ Hra
    Hgp0 Htp0 HRO HROK HCE Hsp46 HK Hsp HFR R3 R4 R8 Hs3 RP0 HAOK RNAMES) end).
Qed.
Lemma ca_iter_14 : ca_iter_stmt 14.
Proof.
unfold ca_iter_stmt.
intros ROW ly St W regs0 mem0 md0 p0 v s3v regs memc mdc HP NEXT.
pose proof (ca_lseed 14%nat ly St W regs0 mem0 md0 p0 v s3v regs memc mdc HP) as HS.
destruct HP as (HJ & Hra & Hgp0 & Htp0 & HRO & HROK & HCE & Hsp46 & HK & Hsp & HFR & R3 & R4 & R8 & R18 & R19 & R20 & R21
  & R22 & R23 & R24 & Hs3 & RP0 & HAOK & RNAMES).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hes : ESTACK = 4096) by reflexivity.
unfold cfg_at. change (w64 (BASE + CE_LOOP)) with (Z_to_bv 64 (BASE + CE_LOOP)).
set (E := Eimg (Ereg regs (ca_extra s3v regs0))) in HS.
assert (HEI : img_env VAL A_LIM E) by apply Eimg_env.
assert (EA : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (ca_extra s3v regs0)) n)
  by (intros n Hn; apply Eimg_low; exact Hn).
assert (Usp : bv_unsigned (ew E 2) = spZ regs)
  by (rewrite (EA 2%nat ltac:(unfold A_TEXT; lia)), (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
(* the shadow check of row k (zero), its name pointer, the strcmp call *)
paj_run_shc RUNP RUNC HS HJ; [cl_awr |].
cl_keep_run.
(lazymatch goal with HS : st_ok _ ?E _ (restrict _ ?ms), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
  HK : ce_kept _ _ _ _ |- _ =>
let Ra0 := fresh "Ra0" in let Ra1 := fresh "Ra1" in let Rra := fresh "Rra" in
let Qsp := fresh "Qsp" in let Qgp := fresh "Qgp" in let Qtp := fresh "Qtp" in
prreg HS (10%bv : bv 5) Ra0; prreg HS (11%bv : bv 5) Ra1; prreg HS (1%bv : bv 5) Rra;
prreg HS (2%bv : bv 5) Qsp; prreg HS (3%bv : bv 5) Qgp; prreg HS (4%bv : bv 5) Qtp;
pmkst HS;
eapply SRr_bind;
[ apply (ce_strcmp_at ly St W (spZ regs0) mem0 md0 ms _ p0 v (ca_name_addr 14%nat) (ca_nm 14%nat) 3888 HJ HRO HCE HK);
  [ rewrite Ra0, (EA 8%nat ltac:(unfold A_TEXT; lia)), (ew_Ereg_nat regs _ 8 8%bv eq_refl); exact R8
  | rewrite Ra1; apply bv_eq; vm_compute; reflexivity
  | unfold spZ at 1; rewrite Qsp, Usp; exact Hsp
  | rewrite Qgp, (EA 3%nat ltac:(unfold A_TEXT; lia)), (ew_Ereg_nat regs _ 3 3%bv eq_refl), R3; exact Hgp0
  | rewrite Qtp, (EA 4%nat ltac:(unfold A_TEXT; lia)), (ew_Ereg_nat regs _ 4 4%bv eq_refl), R4; exact Htp0
  | exact Rra | lia | reflexivity | exact RP0 | exact (RNAMES 14%nat ltac:(lia)) ]
| ];
clear Ra0 Ra1 Rra Qsp Qgp Qtp; cbv beta;
intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hcmp & HK2 & Hfr2);
let HS2 := fresh "HS" in
jafter_call_keep_hi HS 1024%nat regs2 (mrestrict (w_H W) mem2) HP2 [0; 1; 2]%nat HS2;
ce_kept_regions HS2 Hfr2 HJ2;
rewrite <- restrict_mkst_fx in HS2;
lazymatch goal with HFR : ca_frame_at _ _ _ _ |- _ =>
  let HFR2 := fresh "HFR" in
  pose proof (ce_frame_call W (ms_mem ms) mem2 (spZ regs) regs0 _ _ HFR Hfr2 ltac:(lia) ltac:(lia) ltac:(lia)) as HFR2;
  clear HFR; rename HFR2 into HFR end;
clear HS HJ HK; rename HS2 into HS; rename HJ2 into HJ; rename HK2 into HK;
assert (HEI2 : img_env VAL A_LIM (havoc E 1024 (map (getr regs2) CLOB))) by (apply img_env_havoc_hi; [exact HEI | unfold A_LIM; lia]);
assert (Usp2 : bv_unsigned (ew (havoc E 1024 (map (getr regs2) CLOB)) 2) = spZ regs) by (rewrite ew_havoc_old by lia; exact Usp);
assert (EA2 : forall n, (n < A_TEXT)%nat -> ew (havoc E 1024 (map (getr regs2) CLOB)) n = ew (Ereg regs (ca_extra s3v regs0)) n)
  by (intros n Hn; rewrite ew_havoc_old by (unfold A_TEXT in Hn; lia); apply EA; exact Hn);
pose proof (ce_U_w _ _ _ (ce_havoc_a0 E 1024 regs2)) as UA; cbn [Nat.add] in UA;
clear Usp EA; rename Usp2 into Usp; rename EA2 into EA
end).
(* beqz a0 (0x87460) *)
psrr_branch_pi RUNP BR HS.
- (lazymatch goal with Hc : branch_taken _ _ _ = true, UA : U _ _ = bv_unsigned (getr ?r2 10), Hcmp : getr ?r2 10 = w64 0 <-> _ |- _ =>
  let Hv := fresh "Hv" in
  assert (Hv : v = ca_nm 14%nat) by (apply Hcmp; apply bv_eq; rewrite (ce_br_eq _ _ _ 0 UA) in Hc; apply Z.eqb_eq in Hc;
    rewrite Hc; reflexivity);
  let Hmm := fresh "Hmm" in
  assert (Hmm : fst (ca_ar 14%nat) <= s3v - 1 <= snd (ca_ar 14%nat))
    by (unfold ca_aok in HAOK; rewrite Hv, (ca_find_all 14%nat ltac:(lia)) in HAOK; exact HAOK);
  paj_run_to_shc RUNTOP HS HJ CA_SEG; [cl_awr |]; cl_keep_run;
  lazymatch goal with HS : st_ok_pi _ _ ?E3 ?ss3 (restrict _ ?ms3), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
    HK : ce_kept _ _ _ _, HFR : ca_frame_at _ _ _ _ |- SRr _ _ (mkCfg _ ?md3) _ =>
    pmkst HS;
    refine (ROW ly St W regs0 mem0 md0 W (ms_regs ms3) (ms_mem ms3) md3 s3v _ Hgp0 Htp0);
    exact (ca_close_row 14%nat _ _ E3 ss3 ms3 ly St W regs0 mem0 md0 md3 s3v regs HS EA ltac:(vm_compute; reflexivity) HJ Hra
      (ce_ro_kept W mem0 (ms_mem ms3) (spZ regs0) HROK HK HCE) Hsp HFR R3 R4 Hmm Hs3) end end).
- (paj_run_to_shc RUNTOP HS HJ CE_LOOP; [cl_awr |]; cl_keep_run;
lazymatch goal with HS : st_ok_pi _ _ ?E3 ?ss3 (restrict _ ?ms3), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
  HK : ce_kept _ _ _ _, HFR : ca_frame_at _ _ _ _ |- SRr _ _ (mkCfg _ ?md3) _ =>
  pmkst HS;
  refine (NEXT ltac:(apply Nat.ltb_lt; reflexivity) (ms_regs ms3) (ms_mem ms3) md3 _);
  exact (ca_close_next 14%nat E3 ss3 ms3 ly St W regs0 mem0 md0 md3 p0 v s3v regs HS EA ltac:(vm_compute; reflexivity) HJ Hra
    Hgp0 Htp0 HRO HROK HCE Hsp46 HK Hsp HFR R3 R4 R8 Hs3 RP0 HAOK RNAMES) end).
Qed.
Lemma ca_iter_15 : ca_iter_stmt 15.
Proof.
unfold ca_iter_stmt.
intros ROW ly St W regs0 mem0 md0 p0 v s3v regs memc mdc HP NEXT.
pose proof (ca_lseed 15%nat ly St W regs0 mem0 md0 p0 v s3v regs memc mdc HP) as HS.
destruct HP as (HJ & Hra & Hgp0 & Htp0 & HRO & HROK & HCE & Hsp46 & HK & Hsp & HFR & R3 & R4 & R8 & R18 & R19 & R20 & R21
  & R22 & R23 & R24 & Hs3 & RP0 & HAOK & RNAMES).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hes : ESTACK = 4096) by reflexivity.
unfold cfg_at. change (w64 (BASE + CE_LOOP)) with (Z_to_bv 64 (BASE + CE_LOOP)).
set (E := Eimg (Ereg regs (ca_extra s3v regs0))) in HS.
assert (HEI : img_env VAL A_LIM E) by apply Eimg_env.
assert (EA : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (ca_extra s3v regs0)) n)
  by (intros n Hn; apply Eimg_low; exact Hn).
assert (Usp : bv_unsigned (ew E 2) = spZ regs)
  by (rewrite (EA 2%nat ltac:(unfold A_TEXT; lia)), (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
(* the shadow check of row k (zero), its name pointer, the strcmp call *)
paj_run_shc RUNP RUNC HS HJ; [cl_awr |].
cl_keep_run.
(lazymatch goal with HS : st_ok _ ?E _ (restrict _ ?ms), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
  HK : ce_kept _ _ _ _ |- _ =>
let Ra0 := fresh "Ra0" in let Ra1 := fresh "Ra1" in let Rra := fresh "Rra" in
let Qsp := fresh "Qsp" in let Qgp := fresh "Qgp" in let Qtp := fresh "Qtp" in
prreg HS (10%bv : bv 5) Ra0; prreg HS (11%bv : bv 5) Ra1; prreg HS (1%bv : bv 5) Rra;
prreg HS (2%bv : bv 5) Qsp; prreg HS (3%bv : bv 5) Qgp; prreg HS (4%bv : bv 5) Qtp;
pmkst HS;
eapply SRr_bind;
[ apply (ce_strcmp_at ly St W (spZ regs0) mem0 md0 ms _ p0 v (ca_name_addr 15%nat) (ca_nm 15%nat) 3888 HJ HRO HCE HK);
  [ rewrite Ra0, (EA 8%nat ltac:(unfold A_TEXT; lia)), (ew_Ereg_nat regs _ 8 8%bv eq_refl); exact R8
  | rewrite Ra1; apply bv_eq; vm_compute; reflexivity
  | unfold spZ at 1; rewrite Qsp, Usp; exact Hsp
  | rewrite Qgp, (EA 3%nat ltac:(unfold A_TEXT; lia)), (ew_Ereg_nat regs _ 3 3%bv eq_refl), R3; exact Hgp0
  | rewrite Qtp, (EA 4%nat ltac:(unfold A_TEXT; lia)), (ew_Ereg_nat regs _ 4 4%bv eq_refl), R4; exact Htp0
  | exact Rra | lia | reflexivity | exact RP0 | exact (RNAMES 15%nat ltac:(lia)) ]
| ];
clear Ra0 Ra1 Rra Qsp Qgp Qtp; cbv beta;
intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hcmp & HK2 & Hfr2);
let HS2 := fresh "HS" in
jafter_call_keep_hi HS 1024%nat regs2 (mrestrict (w_H W) mem2) HP2 [0; 1; 2]%nat HS2;
ce_kept_regions HS2 Hfr2 HJ2;
rewrite <- restrict_mkst_fx in HS2;
lazymatch goal with HFR : ca_frame_at _ _ _ _ |- _ =>
  let HFR2 := fresh "HFR" in
  pose proof (ce_frame_call W (ms_mem ms) mem2 (spZ regs) regs0 _ _ HFR Hfr2 ltac:(lia) ltac:(lia) ltac:(lia)) as HFR2;
  clear HFR; rename HFR2 into HFR end;
clear HS HJ HK; rename HS2 into HS; rename HJ2 into HJ; rename HK2 into HK;
assert (HEI2 : img_env VAL A_LIM (havoc E 1024 (map (getr regs2) CLOB))) by (apply img_env_havoc_hi; [exact HEI | unfold A_LIM; lia]);
assert (Usp2 : bv_unsigned (ew (havoc E 1024 (map (getr regs2) CLOB)) 2) = spZ regs) by (rewrite ew_havoc_old by lia; exact Usp);
assert (EA2 : forall n, (n < A_TEXT)%nat -> ew (havoc E 1024 (map (getr regs2) CLOB)) n = ew (Ereg regs (ca_extra s3v regs0)) n)
  by (intros n Hn; rewrite ew_havoc_old by (unfold A_TEXT in Hn; lia); apply EA; exact Hn);
pose proof (ce_U_w _ _ _ (ce_havoc_a0 E 1024 regs2)) as UA; cbn [Nat.add] in UA;
clear Usp EA; rename Usp2 into Usp; rename EA2 into EA
end).
(* beqz a0 (0x87460) *)
psrr_branch_pi RUNP BR HS.
- (lazymatch goal with Hc : branch_taken _ _ _ = true, UA : U _ _ = bv_unsigned (getr ?r2 10), Hcmp : getr ?r2 10 = w64 0 <-> _ |- _ =>
  let Hv := fresh "Hv" in
  assert (Hv : v = ca_nm 15%nat) by (apply Hcmp; apply bv_eq; rewrite (ce_br_eq _ _ _ 0 UA) in Hc; apply Z.eqb_eq in Hc;
    rewrite Hc; reflexivity);
  let Hmm := fresh "Hmm" in
  assert (Hmm : fst (ca_ar 15%nat) <= s3v - 1 <= snd (ca_ar 15%nat))
    by (unfold ca_aok in HAOK; rewrite Hv, (ca_find_all 15%nat ltac:(lia)) in HAOK; exact HAOK);
  paj_run_to_shc RUNTOP HS HJ CA_SEG; [cl_awr |]; cl_keep_run;
  lazymatch goal with HS : st_ok_pi _ _ ?E3 ?ss3 (restrict _ ?ms3), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
    HK : ce_kept _ _ _ _, HFR : ca_frame_at _ _ _ _ |- SRr _ _ (mkCfg _ ?md3) _ =>
    pmkst HS;
    refine (ROW ly St W regs0 mem0 md0 W (ms_regs ms3) (ms_mem ms3) md3 s3v _ Hgp0 Htp0);
    exact (ca_close_row 15%nat _ _ E3 ss3 ms3 ly St W regs0 mem0 md0 md3 s3v regs HS EA ltac:(vm_compute; reflexivity) HJ Hra
      (ce_ro_kept W mem0 (ms_mem ms3) (spZ regs0) HROK HK HCE) Hsp HFR R3 R4 Hmm Hs3) end end).
- (paj_run_to_shc RUNTOP HS HJ CE_LOOP; [cl_awr |]; cl_keep_run;
lazymatch goal with HS : st_ok_pi _ _ ?E3 ?ss3 (restrict _ ?ms3), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
  HK : ce_kept _ _ _ _, HFR : ca_frame_at _ _ _ _ |- SRr _ _ (mkCfg _ ?md3) _ =>
  pmkst HS;
  refine (NEXT ltac:(apply Nat.ltb_lt; reflexivity) (ms_regs ms3) (ms_mem ms3) md3 _);
  exact (ca_close_next 15%nat E3 ss3 ms3 ly St W regs0 mem0 md0 md3 p0 v s3v regs HS EA ltac:(vm_compute; reflexivity) HJ Hra
    Hgp0 Htp0 HRO HROK HCE Hsp46 HK Hsp HFR R3 R4 R8 Hs3 RP0 HAOK RNAMES) end).
Qed.
Lemma ca_iter_16 : ca_iter_stmt 16.
Proof.
unfold ca_iter_stmt.
intros ROW ly St W regs0 mem0 md0 p0 v s3v regs memc mdc HP NEXT.
pose proof (ca_lseed 16%nat ly St W regs0 mem0 md0 p0 v s3v regs memc mdc HP) as HS.
destruct HP as (HJ & Hra & Hgp0 & Htp0 & HRO & HROK & HCE & Hsp46 & HK & Hsp & HFR & R3 & R4 & R8 & R18 & R19 & R20 & R21
  & R22 & R23 & R24 & Hs3 & RP0 & HAOK & RNAMES).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hes : ESTACK = 4096) by reflexivity.
unfold cfg_at. change (w64 (BASE + CE_LOOP)) with (Z_to_bv 64 (BASE + CE_LOOP)).
set (E := Eimg (Ereg regs (ca_extra s3v regs0))) in HS.
assert (HEI : img_env VAL A_LIM E) by apply Eimg_env.
assert (EA : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (ca_extra s3v regs0)) n)
  by (intros n Hn; apply Eimg_low; exact Hn).
assert (Usp : bv_unsigned (ew E 2) = spZ regs)
  by (rewrite (EA 2%nat ltac:(unfold A_TEXT; lia)), (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
(* the shadow check of row k (zero), its name pointer, the strcmp call *)
paj_run_shc RUNP RUNC HS HJ; [cl_awr |].
cl_keep_run.
(lazymatch goal with HS : st_ok _ ?E _ (restrict _ ?ms), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
  HK : ce_kept _ _ _ _ |- _ =>
let Ra0 := fresh "Ra0" in let Ra1 := fresh "Ra1" in let Rra := fresh "Rra" in
let Qsp := fresh "Qsp" in let Qgp := fresh "Qgp" in let Qtp := fresh "Qtp" in
prreg HS (10%bv : bv 5) Ra0; prreg HS (11%bv : bv 5) Ra1; prreg HS (1%bv : bv 5) Rra;
prreg HS (2%bv : bv 5) Qsp; prreg HS (3%bv : bv 5) Qgp; prreg HS (4%bv : bv 5) Qtp;
pmkst HS;
eapply SRr_bind;
[ apply (ce_strcmp_at ly St W (spZ regs0) mem0 md0 ms _ p0 v (ca_name_addr 16%nat) (ca_nm 16%nat) 3888 HJ HRO HCE HK);
  [ rewrite Ra0, (EA 8%nat ltac:(unfold A_TEXT; lia)), (ew_Ereg_nat regs _ 8 8%bv eq_refl); exact R8
  | rewrite Ra1; apply bv_eq; vm_compute; reflexivity
  | unfold spZ at 1; rewrite Qsp, Usp; exact Hsp
  | rewrite Qgp, (EA 3%nat ltac:(unfold A_TEXT; lia)), (ew_Ereg_nat regs _ 3 3%bv eq_refl), R3; exact Hgp0
  | rewrite Qtp, (EA 4%nat ltac:(unfold A_TEXT; lia)), (ew_Ereg_nat regs _ 4 4%bv eq_refl), R4; exact Htp0
  | exact Rra | lia | reflexivity | exact RP0 | exact (RNAMES 16%nat ltac:(lia)) ]
| ];
clear Ra0 Ra1 Rra Qsp Qgp Qtp; cbv beta;
intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hcmp & HK2 & Hfr2);
let HS2 := fresh "HS" in
jafter_call_keep_hi HS 1024%nat regs2 (mrestrict (w_H W) mem2) HP2 [0; 1; 2]%nat HS2;
ce_kept_regions HS2 Hfr2 HJ2;
rewrite <- restrict_mkst_fx in HS2;
lazymatch goal with HFR : ca_frame_at _ _ _ _ |- _ =>
  let HFR2 := fresh "HFR" in
  pose proof (ce_frame_call W (ms_mem ms) mem2 (spZ regs) regs0 _ _ HFR Hfr2 ltac:(lia) ltac:(lia) ltac:(lia)) as HFR2;
  clear HFR; rename HFR2 into HFR end;
clear HS HJ HK; rename HS2 into HS; rename HJ2 into HJ; rename HK2 into HK;
assert (HEI2 : img_env VAL A_LIM (havoc E 1024 (map (getr regs2) CLOB))) by (apply img_env_havoc_hi; [exact HEI | unfold A_LIM; lia]);
assert (Usp2 : bv_unsigned (ew (havoc E 1024 (map (getr regs2) CLOB)) 2) = spZ regs) by (rewrite ew_havoc_old by lia; exact Usp);
assert (EA2 : forall n, (n < A_TEXT)%nat -> ew (havoc E 1024 (map (getr regs2) CLOB)) n = ew (Ereg regs (ca_extra s3v regs0)) n)
  by (intros n Hn; rewrite ew_havoc_old by (unfold A_TEXT in Hn; lia); apply EA; exact Hn);
pose proof (ce_U_w _ _ _ (ce_havoc_a0 E 1024 regs2)) as UA; cbn [Nat.add] in UA;
clear Usp EA; rename Usp2 into Usp; rename EA2 into EA
end).
(* beqz a0 (0x87460) *)
psrr_branch_pi RUNP BR HS.
- (lazymatch goal with Hc : branch_taken _ _ _ = true, UA : U _ _ = bv_unsigned (getr ?r2 10), Hcmp : getr ?r2 10 = w64 0 <-> _ |- _ =>
  let Hv := fresh "Hv" in
  assert (Hv : v = ca_nm 16%nat) by (apply Hcmp; apply bv_eq; rewrite (ce_br_eq _ _ _ 0 UA) in Hc; apply Z.eqb_eq in Hc;
    rewrite Hc; reflexivity);
  let Hmm := fresh "Hmm" in
  assert (Hmm : fst (ca_ar 16%nat) <= s3v - 1 <= snd (ca_ar 16%nat))
    by (unfold ca_aok in HAOK; rewrite Hv, (ca_find_all 16%nat ltac:(lia)) in HAOK; exact HAOK);
  paj_run_to_shc RUNTOP HS HJ CA_SEG; [cl_awr |]; cl_keep_run;
  lazymatch goal with HS : st_ok_pi _ _ ?E3 ?ss3 (restrict _ ?ms3), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
    HK : ce_kept _ _ _ _, HFR : ca_frame_at _ _ _ _ |- SRr _ _ (mkCfg _ ?md3) _ =>
    pmkst HS;
    refine (ROW ly St W regs0 mem0 md0 W (ms_regs ms3) (ms_mem ms3) md3 s3v _ Hgp0 Htp0);
    exact (ca_close_row 16%nat _ _ E3 ss3 ms3 ly St W regs0 mem0 md0 md3 s3v regs HS EA ltac:(vm_compute; reflexivity) HJ Hra
      (ce_ro_kept W mem0 (ms_mem ms3) (spZ regs0) HROK HK HCE) Hsp HFR R3 R4 Hmm Hs3) end end).
- (paj_run_to_shc RUNTOP HS HJ CE_LOOP; [cl_awr |]; cl_keep_run;
lazymatch goal with HS : st_ok_pi _ _ ?E3 ?ss3 (restrict _ ?ms3), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
  HK : ce_kept _ _ _ _, HFR : ca_frame_at _ _ _ _ |- SRr _ _ (mkCfg _ ?md3) _ =>
  pmkst HS;
  refine (NEXT ltac:(apply Nat.ltb_lt; reflexivity) (ms_regs ms3) (ms_mem ms3) md3 _);
  exact (ca_close_next 16%nat E3 ss3 ms3 ly St W regs0 mem0 md0 md3 p0 v s3v regs HS EA ltac:(vm_compute; reflexivity) HJ Hra
    Hgp0 Htp0 HRO HROK HCE Hsp46 HK Hsp HFR R3 R4 R8 Hs3 RP0 HAOK RNAMES) end).
Qed.
Lemma ca_iter_17 : ca_iter_stmt 17.
Proof.
unfold ca_iter_stmt.
intros ROW ly St W regs0 mem0 md0 p0 v s3v regs memc mdc HP NEXT.
pose proof (ca_lseed 17%nat ly St W regs0 mem0 md0 p0 v s3v regs memc mdc HP) as HS.
destruct HP as (HJ & Hra & Hgp0 & Htp0 & HRO & HROK & HCE & Hsp46 & HK & Hsp & HFR & R3 & R4 & R8 & R18 & R19 & R20 & R21
  & R22 & R23 & R24 & Hs3 & RP0 & HAOK & RNAMES).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hes : ESTACK = 4096) by reflexivity.
unfold cfg_at. change (w64 (BASE + CE_LOOP)) with (Z_to_bv 64 (BASE + CE_LOOP)).
set (E := Eimg (Ereg regs (ca_extra s3v regs0))) in HS.
assert (HEI : img_env VAL A_LIM E) by apply Eimg_env.
assert (EA : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (ca_extra s3v regs0)) n)
  by (intros n Hn; apply Eimg_low; exact Hn).
assert (Usp : bv_unsigned (ew E 2) = spZ regs)
  by (rewrite (EA 2%nat ltac:(unfold A_TEXT; lia)), (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
(* the shadow check of row k (zero), its name pointer, the strcmp call *)
paj_run_shc RUNP RUNC HS HJ; [cl_awr |].
cl_keep_run.
(lazymatch goal with HS : st_ok _ ?E _ (restrict _ ?ms), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
  HK : ce_kept _ _ _ _ |- _ =>
let Ra0 := fresh "Ra0" in let Ra1 := fresh "Ra1" in let Rra := fresh "Rra" in
let Qsp := fresh "Qsp" in let Qgp := fresh "Qgp" in let Qtp := fresh "Qtp" in
prreg HS (10%bv : bv 5) Ra0; prreg HS (11%bv : bv 5) Ra1; prreg HS (1%bv : bv 5) Rra;
prreg HS (2%bv : bv 5) Qsp; prreg HS (3%bv : bv 5) Qgp; prreg HS (4%bv : bv 5) Qtp;
pmkst HS;
eapply SRr_bind;
[ apply (ce_strcmp_at ly St W (spZ regs0) mem0 md0 ms _ p0 v (ca_name_addr 17%nat) (ca_nm 17%nat) 3888 HJ HRO HCE HK);
  [ rewrite Ra0, (EA 8%nat ltac:(unfold A_TEXT; lia)), (ew_Ereg_nat regs _ 8 8%bv eq_refl); exact R8
  | rewrite Ra1; apply bv_eq; vm_compute; reflexivity
  | unfold spZ at 1; rewrite Qsp, Usp; exact Hsp
  | rewrite Qgp, (EA 3%nat ltac:(unfold A_TEXT; lia)), (ew_Ereg_nat regs _ 3 3%bv eq_refl), R3; exact Hgp0
  | rewrite Qtp, (EA 4%nat ltac:(unfold A_TEXT; lia)), (ew_Ereg_nat regs _ 4 4%bv eq_refl), R4; exact Htp0
  | exact Rra | lia | reflexivity | exact RP0 | exact (RNAMES 17%nat ltac:(lia)) ]
| ];
clear Ra0 Ra1 Rra Qsp Qgp Qtp; cbv beta;
intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hcmp & HK2 & Hfr2);
let HS2 := fresh "HS" in
jafter_call_keep_hi HS 1024%nat regs2 (mrestrict (w_H W) mem2) HP2 [0; 1; 2]%nat HS2;
ce_kept_regions HS2 Hfr2 HJ2;
rewrite <- restrict_mkst_fx in HS2;
lazymatch goal with HFR : ca_frame_at _ _ _ _ |- _ =>
  let HFR2 := fresh "HFR" in
  pose proof (ce_frame_call W (ms_mem ms) mem2 (spZ regs) regs0 _ _ HFR Hfr2 ltac:(lia) ltac:(lia) ltac:(lia)) as HFR2;
  clear HFR; rename HFR2 into HFR end;
clear HS HJ HK; rename HS2 into HS; rename HJ2 into HJ; rename HK2 into HK;
assert (HEI2 : img_env VAL A_LIM (havoc E 1024 (map (getr regs2) CLOB))) by (apply img_env_havoc_hi; [exact HEI | unfold A_LIM; lia]);
assert (Usp2 : bv_unsigned (ew (havoc E 1024 (map (getr regs2) CLOB)) 2) = spZ regs) by (rewrite ew_havoc_old by lia; exact Usp);
assert (EA2 : forall n, (n < A_TEXT)%nat -> ew (havoc E 1024 (map (getr regs2) CLOB)) n = ew (Ereg regs (ca_extra s3v regs0)) n)
  by (intros n Hn; rewrite ew_havoc_old by (unfold A_TEXT in Hn; lia); apply EA; exact Hn);
pose proof (ce_U_w _ _ _ (ce_havoc_a0 E 1024 regs2)) as UA; cbn [Nat.add] in UA;
clear Usp EA; rename Usp2 into Usp; rename EA2 into EA
end).
(* beqz a0 (0x87460) *)
psrr_branch_pi RUNP BR HS.
- (lazymatch goal with Hc : branch_taken _ _ _ = true, UA : U _ _ = bv_unsigned (getr ?r2 10), Hcmp : getr ?r2 10 = w64 0 <-> _ |- _ =>
  let Hv := fresh "Hv" in
  assert (Hv : v = ca_nm 17%nat) by (apply Hcmp; apply bv_eq; rewrite (ce_br_eq _ _ _ 0 UA) in Hc; apply Z.eqb_eq in Hc;
    rewrite Hc; reflexivity);
  let Hmm := fresh "Hmm" in
  assert (Hmm : fst (ca_ar 17%nat) <= s3v - 1 <= snd (ca_ar 17%nat))
    by (unfold ca_aok in HAOK; rewrite Hv, (ca_find_all 17%nat ltac:(lia)) in HAOK; exact HAOK);
  paj_run_to_shc RUNTOP HS HJ CA_SEG; [cl_awr |]; cl_keep_run;
  lazymatch goal with HS : st_ok_pi _ _ ?E3 ?ss3 (restrict _ ?ms3), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
    HK : ce_kept _ _ _ _, HFR : ca_frame_at _ _ _ _ |- SRr _ _ (mkCfg _ ?md3) _ =>
    pmkst HS;
    refine (ROW ly St W regs0 mem0 md0 W (ms_regs ms3) (ms_mem ms3) md3 s3v _ Hgp0 Htp0);
    exact (ca_close_row 17%nat _ _ E3 ss3 ms3 ly St W regs0 mem0 md0 md3 s3v regs HS EA ltac:(vm_compute; reflexivity) HJ Hra
      (ce_ro_kept W mem0 (ms_mem ms3) (spZ regs0) HROK HK HCE) Hsp HFR R3 R4 Hmm Hs3) end end).
- (paj_run_to_shc RUNTOP HS HJ CE_LOOP; [cl_awr |]; cl_keep_run;
lazymatch goal with HS : st_ok_pi _ _ ?E3 ?ss3 (restrict _ ?ms3), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
  HK : ce_kept _ _ _ _, HFR : ca_frame_at _ _ _ _ |- SRr _ _ (mkCfg _ ?md3) _ =>
  pmkst HS;
  refine (NEXT ltac:(apply Nat.ltb_lt; reflexivity) (ms_regs ms3) (ms_mem ms3) md3 _);
  exact (ca_close_next 17%nat E3 ss3 ms3 ly St W regs0 mem0 md0 md3 p0 v s3v regs HS EA ltac:(vm_compute; reflexivity) HJ Hra
    Hgp0 Htp0 HRO HROK HCE Hsp46 HK Hsp HFR R3 R4 R8 Hs3 RP0 HAOK RNAMES) end).
Qed.
Lemma ca_iter_18 : ca_iter_stmt 18.
Proof.
unfold ca_iter_stmt.
intros ROW ly St W regs0 mem0 md0 p0 v s3v regs memc mdc HP NEXT.
pose proof (ca_lseed 18%nat ly St W regs0 mem0 md0 p0 v s3v regs memc mdc HP) as HS.
destruct HP as (HJ & Hra & Hgp0 & Htp0 & HRO & HROK & HCE & Hsp46 & HK & Hsp & HFR & R3 & R4 & R8 & R18 & R19 & R20 & R21
  & R22 & R23 & R24 & Hs3 & RP0 & HAOK & RNAMES).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hes : ESTACK = 4096) by reflexivity.
unfold cfg_at. change (w64 (BASE + CE_LOOP)) with (Z_to_bv 64 (BASE + CE_LOOP)).
set (E := Eimg (Ereg regs (ca_extra s3v regs0))) in HS.
assert (HEI : img_env VAL A_LIM E) by apply Eimg_env.
assert (EA : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (ca_extra s3v regs0)) n)
  by (intros n Hn; apply Eimg_low; exact Hn).
assert (Usp : bv_unsigned (ew E 2) = spZ regs)
  by (rewrite (EA 2%nat ltac:(unfold A_TEXT; lia)), (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
(* the shadow check of row k (zero), its name pointer, the strcmp call *)
paj_run_shc RUNP RUNC HS HJ; [cl_awr |].
cl_keep_run.
(lazymatch goal with HS : st_ok _ ?E _ (restrict _ ?ms), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
  HK : ce_kept _ _ _ _ |- _ =>
let Ra0 := fresh "Ra0" in let Ra1 := fresh "Ra1" in let Rra := fresh "Rra" in
let Qsp := fresh "Qsp" in let Qgp := fresh "Qgp" in let Qtp := fresh "Qtp" in
prreg HS (10%bv : bv 5) Ra0; prreg HS (11%bv : bv 5) Ra1; prreg HS (1%bv : bv 5) Rra;
prreg HS (2%bv : bv 5) Qsp; prreg HS (3%bv : bv 5) Qgp; prreg HS (4%bv : bv 5) Qtp;
pmkst HS;
eapply SRr_bind;
[ apply (ce_strcmp_at ly St W (spZ regs0) mem0 md0 ms _ p0 v (ca_name_addr 18%nat) (ca_nm 18%nat) 3888 HJ HRO HCE HK);
  [ rewrite Ra0, (EA 8%nat ltac:(unfold A_TEXT; lia)), (ew_Ereg_nat regs _ 8 8%bv eq_refl); exact R8
  | rewrite Ra1; apply bv_eq; vm_compute; reflexivity
  | unfold spZ at 1; rewrite Qsp, Usp; exact Hsp
  | rewrite Qgp, (EA 3%nat ltac:(unfold A_TEXT; lia)), (ew_Ereg_nat regs _ 3 3%bv eq_refl), R3; exact Hgp0
  | rewrite Qtp, (EA 4%nat ltac:(unfold A_TEXT; lia)), (ew_Ereg_nat regs _ 4 4%bv eq_refl), R4; exact Htp0
  | exact Rra | lia | reflexivity | exact RP0 | exact (RNAMES 18%nat ltac:(lia)) ]
| ];
clear Ra0 Ra1 Rra Qsp Qgp Qtp; cbv beta;
intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hcmp & HK2 & Hfr2);
let HS2 := fresh "HS" in
jafter_call_keep_hi HS 1024%nat regs2 (mrestrict (w_H W) mem2) HP2 [0; 1; 2]%nat HS2;
ce_kept_regions HS2 Hfr2 HJ2;
rewrite <- restrict_mkst_fx in HS2;
lazymatch goal with HFR : ca_frame_at _ _ _ _ |- _ =>
  let HFR2 := fresh "HFR" in
  pose proof (ce_frame_call W (ms_mem ms) mem2 (spZ regs) regs0 _ _ HFR Hfr2 ltac:(lia) ltac:(lia) ltac:(lia)) as HFR2;
  clear HFR; rename HFR2 into HFR end;
clear HS HJ HK; rename HS2 into HS; rename HJ2 into HJ; rename HK2 into HK;
assert (HEI2 : img_env VAL A_LIM (havoc E 1024 (map (getr regs2) CLOB))) by (apply img_env_havoc_hi; [exact HEI | unfold A_LIM; lia]);
assert (Usp2 : bv_unsigned (ew (havoc E 1024 (map (getr regs2) CLOB)) 2) = spZ regs) by (rewrite ew_havoc_old by lia; exact Usp);
assert (EA2 : forall n, (n < A_TEXT)%nat -> ew (havoc E 1024 (map (getr regs2) CLOB)) n = ew (Ereg regs (ca_extra s3v regs0)) n)
  by (intros n Hn; rewrite ew_havoc_old by (unfold A_TEXT in Hn; lia); apply EA; exact Hn);
pose proof (ce_U_w _ _ _ (ce_havoc_a0 E 1024 regs2)) as UA; cbn [Nat.add] in UA;
clear Usp EA; rename Usp2 into Usp; rename EA2 into EA
end).
(* beqz a0 (0x87460) *)
psrr_branch_pi RUNP BR HS.
- (lazymatch goal with Hc : branch_taken _ _ _ = true, UA : U _ _ = bv_unsigned (getr ?r2 10), Hcmp : getr ?r2 10 = w64 0 <-> _ |- _ =>
  let Hv := fresh "Hv" in
  assert (Hv : v = ca_nm 18%nat) by (apply Hcmp; apply bv_eq; rewrite (ce_br_eq _ _ _ 0 UA) in Hc; apply Z.eqb_eq in Hc;
    rewrite Hc; reflexivity);
  let Hmm := fresh "Hmm" in
  assert (Hmm : fst (ca_ar 18%nat) <= s3v - 1 <= snd (ca_ar 18%nat))
    by (unfold ca_aok in HAOK; rewrite Hv, (ca_find_all 18%nat ltac:(lia)) in HAOK; exact HAOK);
  paj_run_to_shc RUNTOP HS HJ CA_SEG; [cl_awr |]; cl_keep_run;
  lazymatch goal with HS : st_ok_pi _ _ ?E3 ?ss3 (restrict _ ?ms3), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
    HK : ce_kept _ _ _ _, HFR : ca_frame_at _ _ _ _ |- SRr _ _ (mkCfg _ ?md3) _ =>
    pmkst HS;
    refine (ROW ly St W regs0 mem0 md0 W (ms_regs ms3) (ms_mem ms3) md3 s3v _ Hgp0 Htp0);
    exact (ca_close_row 18%nat _ _ E3 ss3 ms3 ly St W regs0 mem0 md0 md3 s3v regs HS EA ltac:(vm_compute; reflexivity) HJ Hra
      (ce_ro_kept W mem0 (ms_mem ms3) (spZ regs0) HROK HK HCE) Hsp HFR R3 R4 Hmm Hs3) end end).
- (paj_run_to_shc RUNTOP HS HJ CE_LOOP; [cl_awr |]; cl_keep_run;
lazymatch goal with HS : st_ok_pi _ _ ?E3 ?ss3 (restrict _ ?ms3), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
  HK : ce_kept _ _ _ _, HFR : ca_frame_at _ _ _ _ |- SRr _ _ (mkCfg _ ?md3) _ =>
  pmkst HS;
  refine (NEXT ltac:(apply Nat.ltb_lt; reflexivity) (ms_regs ms3) (ms_mem ms3) md3 _);
  exact (ca_close_next 18%nat E3 ss3 ms3 ly St W regs0 mem0 md0 md3 p0 v s3v regs HS EA ltac:(vm_compute; reflexivity) HJ Hra
    Hgp0 Htp0 HRO HROK HCE Hsp46 HK Hsp HFR R3 R4 R8 Hs3 RP0 HAOK RNAMES) end).
Qed.
Lemma ca_iter_19 : ca_iter_stmt 19.
Proof.
unfold ca_iter_stmt.
intros ROW ly St W regs0 mem0 md0 p0 v s3v regs memc mdc HP NEXT.
pose proof (ca_lseed 19%nat ly St W regs0 mem0 md0 p0 v s3v regs memc mdc HP) as HS.
destruct HP as (HJ & Hra & Hgp0 & Htp0 & HRO & HROK & HCE & Hsp46 & HK & Hsp & HFR & R3 & R4 & R8 & R18 & R19 & R20 & R21
  & R22 & R23 & R24 & Hs3 & RP0 & HAOK & RNAMES).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hes : ESTACK = 4096) by reflexivity.
unfold cfg_at. change (w64 (BASE + CE_LOOP)) with (Z_to_bv 64 (BASE + CE_LOOP)).
set (E := Eimg (Ereg regs (ca_extra s3v regs0))) in HS.
assert (HEI : img_env VAL A_LIM E) by apply Eimg_env.
assert (EA : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (ca_extra s3v regs0)) n)
  by (intros n Hn; apply Eimg_low; exact Hn).
assert (Usp : bv_unsigned (ew E 2) = spZ regs)
  by (rewrite (EA 2%nat ltac:(unfold A_TEXT; lia)), (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
(* the shadow check of row k (zero), its name pointer, the strcmp call *)
paj_run_shc RUNP RUNC HS HJ; [cl_awr |].
cl_keep_run.
(lazymatch goal with HS : st_ok _ ?E _ (restrict _ ?ms), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
  HK : ce_kept _ _ _ _ |- _ =>
let Ra0 := fresh "Ra0" in let Ra1 := fresh "Ra1" in let Rra := fresh "Rra" in
let Qsp := fresh "Qsp" in let Qgp := fresh "Qgp" in let Qtp := fresh "Qtp" in
prreg HS (10%bv : bv 5) Ra0; prreg HS (11%bv : bv 5) Ra1; prreg HS (1%bv : bv 5) Rra;
prreg HS (2%bv : bv 5) Qsp; prreg HS (3%bv : bv 5) Qgp; prreg HS (4%bv : bv 5) Qtp;
pmkst HS;
eapply SRr_bind;
[ apply (ce_strcmp_at ly St W (spZ regs0) mem0 md0 ms _ p0 v (ca_name_addr 19%nat) (ca_nm 19%nat) 3888 HJ HRO HCE HK);
  [ rewrite Ra0, (EA 8%nat ltac:(unfold A_TEXT; lia)), (ew_Ereg_nat regs _ 8 8%bv eq_refl); exact R8
  | rewrite Ra1; apply bv_eq; vm_compute; reflexivity
  | unfold spZ at 1; rewrite Qsp, Usp; exact Hsp
  | rewrite Qgp, (EA 3%nat ltac:(unfold A_TEXT; lia)), (ew_Ereg_nat regs _ 3 3%bv eq_refl), R3; exact Hgp0
  | rewrite Qtp, (EA 4%nat ltac:(unfold A_TEXT; lia)), (ew_Ereg_nat regs _ 4 4%bv eq_refl), R4; exact Htp0
  | exact Rra | lia | reflexivity | exact RP0 | exact (RNAMES 19%nat ltac:(lia)) ]
| ];
clear Ra0 Ra1 Rra Qsp Qgp Qtp; cbv beta;
intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hcmp & HK2 & Hfr2);
let HS2 := fresh "HS" in
jafter_call_keep_hi HS 1024%nat regs2 (mrestrict (w_H W) mem2) HP2 [0; 1; 2]%nat HS2;
ce_kept_regions HS2 Hfr2 HJ2;
rewrite <- restrict_mkst_fx in HS2;
lazymatch goal with HFR : ca_frame_at _ _ _ _ |- _ =>
  let HFR2 := fresh "HFR" in
  pose proof (ce_frame_call W (ms_mem ms) mem2 (spZ regs) regs0 _ _ HFR Hfr2 ltac:(lia) ltac:(lia) ltac:(lia)) as HFR2;
  clear HFR; rename HFR2 into HFR end;
clear HS HJ HK; rename HS2 into HS; rename HJ2 into HJ; rename HK2 into HK;
assert (HEI2 : img_env VAL A_LIM (havoc E 1024 (map (getr regs2) CLOB))) by (apply img_env_havoc_hi; [exact HEI | unfold A_LIM; lia]);
assert (Usp2 : bv_unsigned (ew (havoc E 1024 (map (getr regs2) CLOB)) 2) = spZ regs) by (rewrite ew_havoc_old by lia; exact Usp);
assert (EA2 : forall n, (n < A_TEXT)%nat -> ew (havoc E 1024 (map (getr regs2) CLOB)) n = ew (Ereg regs (ca_extra s3v regs0)) n)
  by (intros n Hn; rewrite ew_havoc_old by (unfold A_TEXT in Hn; lia); apply EA; exact Hn);
pose proof (ce_U_w _ _ _ (ce_havoc_a0 E 1024 regs2)) as UA; cbn [Nat.add] in UA;
clear Usp EA; rename Usp2 into Usp; rename EA2 into EA
end).
(* beqz a0 (0x87460) *)
psrr_branch_pi RUNP BR HS.
- (lazymatch goal with Hc : branch_taken _ _ _ = true, UA : U _ _ = bv_unsigned (getr ?r2 10), Hcmp : getr ?r2 10 = w64 0 <-> _ |- _ =>
  let Hv := fresh "Hv" in
  assert (Hv : v = ca_nm 19%nat) by (apply Hcmp; apply bv_eq; rewrite (ce_br_eq _ _ _ 0 UA) in Hc; apply Z.eqb_eq in Hc;
    rewrite Hc; reflexivity);
  let Hmm := fresh "Hmm" in
  assert (Hmm : fst (ca_ar 19%nat) <= s3v - 1 <= snd (ca_ar 19%nat))
    by (unfold ca_aok in HAOK; rewrite Hv, (ca_find_all 19%nat ltac:(lia)) in HAOK; exact HAOK);
  paj_run_to_shc RUNTOP HS HJ CA_SEG; [cl_awr |]; cl_keep_run;
  lazymatch goal with HS : st_ok_pi _ _ ?E3 ?ss3 (restrict _ ?ms3), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
    HK : ce_kept _ _ _ _, HFR : ca_frame_at _ _ _ _ |- SRr _ _ (mkCfg _ ?md3) _ =>
    pmkst HS;
    refine (ROW ly St W regs0 mem0 md0 W (ms_regs ms3) (ms_mem ms3) md3 s3v _ Hgp0 Htp0);
    exact (ca_close_row 19%nat _ _ E3 ss3 ms3 ly St W regs0 mem0 md0 md3 s3v regs HS EA ltac:(vm_compute; reflexivity) HJ Hra
      (ce_ro_kept W mem0 (ms_mem ms3) (spZ regs0) HROK HK HCE) Hsp HFR R3 R4 Hmm Hs3) end end).
- (paj_run_to_shc RUNTOP HS HJ CE_LOOP; [cl_awr |]; cl_keep_run;
lazymatch goal with HS : st_ok_pi _ _ ?E3 ?ss3 (restrict _ ?ms3), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
  HK : ce_kept _ _ _ _, HFR : ca_frame_at _ _ _ _ |- SRr _ _ (mkCfg _ ?md3) _ =>
  pmkst HS;
  refine (NEXT ltac:(apply Nat.ltb_lt; reflexivity) (ms_regs ms3) (ms_mem ms3) md3 _);
  exact (ca_close_next 19%nat E3 ss3 ms3 ly St W regs0 mem0 md0 md3 p0 v s3v regs HS EA ltac:(vm_compute; reflexivity) HJ Hra
    Hgp0 Htp0 HRO HROK HCE Hsp46 HK Hsp HFR R3 R4 R8 Hs3 RP0 HAOK RNAMES) end).
Qed.
Lemma ca_iter_20 : ca_iter_stmt 20.
Proof.
unfold ca_iter_stmt.
intros ROW ly St W regs0 mem0 md0 p0 v s3v regs memc mdc HP NEXT.
pose proof (ca_lseed 20%nat ly St W regs0 mem0 md0 p0 v s3v regs memc mdc HP) as HS.
destruct HP as (HJ & Hra & Hgp0 & Htp0 & HRO & HROK & HCE & Hsp46 & HK & Hsp & HFR & R3 & R4 & R8 & R18 & R19 & R20 & R21
  & R22 & R23 & R24 & Hs3 & RP0 & HAOK & RNAMES).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hes : ESTACK = 4096) by reflexivity.
unfold cfg_at. change (w64 (BASE + CE_LOOP)) with (Z_to_bv 64 (BASE + CE_LOOP)).
set (E := Eimg (Ereg regs (ca_extra s3v regs0))) in HS.
assert (HEI : img_env VAL A_LIM E) by apply Eimg_env.
assert (EA : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (ca_extra s3v regs0)) n)
  by (intros n Hn; apply Eimg_low; exact Hn).
assert (Usp : bv_unsigned (ew E 2) = spZ regs)
  by (rewrite (EA 2%nat ltac:(unfold A_TEXT; lia)), (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
(* the shadow check of row k (zero), its name pointer, the strcmp call *)
paj_run_shc RUNP RUNC HS HJ; [cl_awr |].
cl_keep_run.
(lazymatch goal with HS : st_ok _ ?E _ (restrict _ ?ms), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
  HK : ce_kept _ _ _ _ |- _ =>
let Ra0 := fresh "Ra0" in let Ra1 := fresh "Ra1" in let Rra := fresh "Rra" in
let Qsp := fresh "Qsp" in let Qgp := fresh "Qgp" in let Qtp := fresh "Qtp" in
prreg HS (10%bv : bv 5) Ra0; prreg HS (11%bv : bv 5) Ra1; prreg HS (1%bv : bv 5) Rra;
prreg HS (2%bv : bv 5) Qsp; prreg HS (3%bv : bv 5) Qgp; prreg HS (4%bv : bv 5) Qtp;
pmkst HS;
eapply SRr_bind;
[ apply (ce_strcmp_at ly St W (spZ regs0) mem0 md0 ms _ p0 v (ca_name_addr 20%nat) (ca_nm 20%nat) 3888 HJ HRO HCE HK);
  [ rewrite Ra0, (EA 8%nat ltac:(unfold A_TEXT; lia)), (ew_Ereg_nat regs _ 8 8%bv eq_refl); exact R8
  | rewrite Ra1; apply bv_eq; vm_compute; reflexivity
  | unfold spZ at 1; rewrite Qsp, Usp; exact Hsp
  | rewrite Qgp, (EA 3%nat ltac:(unfold A_TEXT; lia)), (ew_Ereg_nat regs _ 3 3%bv eq_refl), R3; exact Hgp0
  | rewrite Qtp, (EA 4%nat ltac:(unfold A_TEXT; lia)), (ew_Ereg_nat regs _ 4 4%bv eq_refl), R4; exact Htp0
  | exact Rra | lia | reflexivity | exact RP0 | exact (RNAMES 20%nat ltac:(lia)) ]
| ];
clear Ra0 Ra1 Rra Qsp Qgp Qtp; cbv beta;
intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hcmp & HK2 & Hfr2);
let HS2 := fresh "HS" in
jafter_call_keep_hi HS 1024%nat regs2 (mrestrict (w_H W) mem2) HP2 [0; 1; 2]%nat HS2;
ce_kept_regions HS2 Hfr2 HJ2;
rewrite <- restrict_mkst_fx in HS2;
lazymatch goal with HFR : ca_frame_at _ _ _ _ |- _ =>
  let HFR2 := fresh "HFR" in
  pose proof (ce_frame_call W (ms_mem ms) mem2 (spZ regs) regs0 _ _ HFR Hfr2 ltac:(lia) ltac:(lia) ltac:(lia)) as HFR2;
  clear HFR; rename HFR2 into HFR end;
clear HS HJ HK; rename HS2 into HS; rename HJ2 into HJ; rename HK2 into HK;
assert (HEI2 : img_env VAL A_LIM (havoc E 1024 (map (getr regs2) CLOB))) by (apply img_env_havoc_hi; [exact HEI | unfold A_LIM; lia]);
assert (Usp2 : bv_unsigned (ew (havoc E 1024 (map (getr regs2) CLOB)) 2) = spZ regs) by (rewrite ew_havoc_old by lia; exact Usp);
assert (EA2 : forall n, (n < A_TEXT)%nat -> ew (havoc E 1024 (map (getr regs2) CLOB)) n = ew (Ereg regs (ca_extra s3v regs0)) n)
  by (intros n Hn; rewrite ew_havoc_old by (unfold A_TEXT in Hn; lia); apply EA; exact Hn);
pose proof (ce_U_w _ _ _ (ce_havoc_a0 E 1024 regs2)) as UA; cbn [Nat.add] in UA;
clear Usp EA; rename Usp2 into Usp; rename EA2 into EA
end).
(* beqz a0 (0x87460) *)
psrr_branch_pi RUNP BR HS.
- (lazymatch goal with Hc : branch_taken _ _ _ = true, UA : U _ _ = bv_unsigned (getr ?r2 10), Hcmp : getr ?r2 10 = w64 0 <-> _ |- _ =>
  let Hv := fresh "Hv" in
  assert (Hv : v = ca_nm 20%nat) by (apply Hcmp; apply bv_eq; rewrite (ce_br_eq _ _ _ 0 UA) in Hc; apply Z.eqb_eq in Hc;
    rewrite Hc; reflexivity);
  let Hmm := fresh "Hmm" in
  assert (Hmm : fst (ca_ar 20%nat) <= s3v - 1 <= snd (ca_ar 20%nat))
    by (unfold ca_aok in HAOK; rewrite Hv, (ca_find_all 20%nat ltac:(lia)) in HAOK; exact HAOK);
  paj_run_to_shc RUNTOP HS HJ CA_SEG; [cl_awr |]; cl_keep_run;
  lazymatch goal with HS : st_ok_pi _ _ ?E3 ?ss3 (restrict _ ?ms3), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
    HK : ce_kept _ _ _ _, HFR : ca_frame_at _ _ _ _ |- SRr _ _ (mkCfg _ ?md3) _ =>
    pmkst HS;
    refine (ROW ly St W regs0 mem0 md0 W (ms_regs ms3) (ms_mem ms3) md3 s3v _ Hgp0 Htp0);
    exact (ca_close_row 20%nat _ _ E3 ss3 ms3 ly St W regs0 mem0 md0 md3 s3v regs HS EA ltac:(vm_compute; reflexivity) HJ Hra
      (ce_ro_kept W mem0 (ms_mem ms3) (spZ regs0) HROK HK HCE) Hsp HFR R3 R4 Hmm Hs3) end end).
- (paj_run_to_shc RUNTOP HS HJ CE_LOOP; [cl_awr |]; cl_keep_run;
lazymatch goal with HS : st_ok_pi _ _ ?E3 ?ss3 (restrict _ ?ms3), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
  HK : ce_kept _ _ _ _, HFR : ca_frame_at _ _ _ _ |- SRr _ _ (mkCfg _ ?md3) _ =>
  pmkst HS;
  refine (NEXT ltac:(apply Nat.ltb_lt; reflexivity) (ms_regs ms3) (ms_mem ms3) md3 _);
  exact (ca_close_next 20%nat E3 ss3 ms3 ly St W regs0 mem0 md0 md3 p0 v s3v regs HS EA ltac:(vm_compute; reflexivity) HJ Hra
    Hgp0 Htp0 HRO HROK HCE Hsp46 HK Hsp HFR R3 R4 R8 Hs3 RP0 HAOK RNAMES) end).
Qed.
Lemma ca_iter_21 : ca_iter_stmt 21.
Proof.
unfold ca_iter_stmt.
intros ROW ly St W regs0 mem0 md0 p0 v s3v regs memc mdc HP NEXT.
pose proof (ca_lseed 21%nat ly St W regs0 mem0 md0 p0 v s3v regs memc mdc HP) as HS.
destruct HP as (HJ & Hra & Hgp0 & Htp0 & HRO & HROK & HCE & Hsp46 & HK & Hsp & HFR & R3 & R4 & R8 & R18 & R19 & R20 & R21
  & R22 & R23 & R24 & Hs3 & RP0 & HAOK & RNAMES).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hes : ESTACK = 4096) by reflexivity.
unfold cfg_at. change (w64 (BASE + CE_LOOP)) with (Z_to_bv 64 (BASE + CE_LOOP)).
set (E := Eimg (Ereg regs (ca_extra s3v regs0))) in HS.
assert (HEI : img_env VAL A_LIM E) by apply Eimg_env.
assert (EA : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (ca_extra s3v regs0)) n)
  by (intros n Hn; apply Eimg_low; exact Hn).
assert (Usp : bv_unsigned (ew E 2) = spZ regs)
  by (rewrite (EA 2%nat ltac:(unfold A_TEXT; lia)), (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
(* the shadow check of row k (zero), its name pointer, the strcmp call *)
paj_run_shc RUNP RUNC HS HJ; [cl_awr |].
cl_keep_run.
(lazymatch goal with HS : st_ok _ ?E _ (restrict _ ?ms), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
  HK : ce_kept _ _ _ _ |- _ =>
let Ra0 := fresh "Ra0" in let Ra1 := fresh "Ra1" in let Rra := fresh "Rra" in
let Qsp := fresh "Qsp" in let Qgp := fresh "Qgp" in let Qtp := fresh "Qtp" in
prreg HS (10%bv : bv 5) Ra0; prreg HS (11%bv : bv 5) Ra1; prreg HS (1%bv : bv 5) Rra;
prreg HS (2%bv : bv 5) Qsp; prreg HS (3%bv : bv 5) Qgp; prreg HS (4%bv : bv 5) Qtp;
pmkst HS;
eapply SRr_bind;
[ apply (ce_strcmp_at ly St W (spZ regs0) mem0 md0 ms _ p0 v (ca_name_addr 21%nat) (ca_nm 21%nat) 3888 HJ HRO HCE HK);
  [ rewrite Ra0, (EA 8%nat ltac:(unfold A_TEXT; lia)), (ew_Ereg_nat regs _ 8 8%bv eq_refl); exact R8
  | rewrite Ra1; apply bv_eq; vm_compute; reflexivity
  | unfold spZ at 1; rewrite Qsp, Usp; exact Hsp
  | rewrite Qgp, (EA 3%nat ltac:(unfold A_TEXT; lia)), (ew_Ereg_nat regs _ 3 3%bv eq_refl), R3; exact Hgp0
  | rewrite Qtp, (EA 4%nat ltac:(unfold A_TEXT; lia)), (ew_Ereg_nat regs _ 4 4%bv eq_refl), R4; exact Htp0
  | exact Rra | lia | reflexivity | exact RP0 | exact (RNAMES 21%nat ltac:(lia)) ]
| ];
clear Ra0 Ra1 Rra Qsp Qgp Qtp; cbv beta;
intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hcmp & HK2 & Hfr2);
let HS2 := fresh "HS" in
jafter_call_keep_hi HS 1024%nat regs2 (mrestrict (w_H W) mem2) HP2 [0; 1; 2]%nat HS2;
ce_kept_regions HS2 Hfr2 HJ2;
rewrite <- restrict_mkst_fx in HS2;
lazymatch goal with HFR : ca_frame_at _ _ _ _ |- _ =>
  let HFR2 := fresh "HFR" in
  pose proof (ce_frame_call W (ms_mem ms) mem2 (spZ regs) regs0 _ _ HFR Hfr2 ltac:(lia) ltac:(lia) ltac:(lia)) as HFR2;
  clear HFR; rename HFR2 into HFR end;
clear HS HJ HK; rename HS2 into HS; rename HJ2 into HJ; rename HK2 into HK;
assert (HEI2 : img_env VAL A_LIM (havoc E 1024 (map (getr regs2) CLOB))) by (apply img_env_havoc_hi; [exact HEI | unfold A_LIM; lia]);
assert (Usp2 : bv_unsigned (ew (havoc E 1024 (map (getr regs2) CLOB)) 2) = spZ regs) by (rewrite ew_havoc_old by lia; exact Usp);
assert (EA2 : forall n, (n < A_TEXT)%nat -> ew (havoc E 1024 (map (getr regs2) CLOB)) n = ew (Ereg regs (ca_extra s3v regs0)) n)
  by (intros n Hn; rewrite ew_havoc_old by (unfold A_TEXT in Hn; lia); apply EA; exact Hn);
pose proof (ce_U_w _ _ _ (ce_havoc_a0 E 1024 regs2)) as UA; cbn [Nat.add] in UA;
clear Usp EA; rename Usp2 into Usp; rename EA2 into EA
end).
(* beqz a0 (0x87460) *)
psrr_branch_pi RUNP BR HS.
- (lazymatch goal with Hc : branch_taken _ _ _ = true, UA : U _ _ = bv_unsigned (getr ?r2 10), Hcmp : getr ?r2 10 = w64 0 <-> _ |- _ =>
  let Hv := fresh "Hv" in
  assert (Hv : v = ca_nm 21%nat) by (apply Hcmp; apply bv_eq; rewrite (ce_br_eq _ _ _ 0 UA) in Hc; apply Z.eqb_eq in Hc;
    rewrite Hc; reflexivity);
  let Hmm := fresh "Hmm" in
  assert (Hmm : fst (ca_ar 21%nat) <= s3v - 1 <= snd (ca_ar 21%nat))
    by (unfold ca_aok in HAOK; rewrite Hv, (ca_find_all 21%nat ltac:(lia)) in HAOK; exact HAOK);
  paj_run_to_shc RUNTOP HS HJ CA_SEG; [cl_awr |]; cl_keep_run;
  lazymatch goal with HS : st_ok_pi _ _ ?E3 ?ss3 (restrict _ ?ms3), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
    HK : ce_kept _ _ _ _, HFR : ca_frame_at _ _ _ _ |- SRr _ _ (mkCfg _ ?md3) _ =>
    pmkst HS;
    refine (ROW ly St W regs0 mem0 md0 W (ms_regs ms3) (ms_mem ms3) md3 s3v _ Hgp0 Htp0);
    exact (ca_close_row 21%nat _ _ E3 ss3 ms3 ly St W regs0 mem0 md0 md3 s3v regs HS EA ltac:(vm_compute; reflexivity) HJ Hra
      (ce_ro_kept W mem0 (ms_mem ms3) (spZ regs0) HROK HK HCE) Hsp HFR R3 R4 Hmm Hs3) end end).
- (paj_run_shc RUNP RUNC HS HJ; [cl_awr |];
lazymatch goal with HS : st_ok_pi _ _ ?E3 ?ss3 (restrict _ ?ms3), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
  destruct (ca_regs_back_g (w_H W) E3 ss3 ms3 regs regs0 s3v HS (fun n Hn => eq_trans (EA n Hn)
    (eq_sym (Eimg_low (Ereg regs (ca_extra s3v regs0)) n Hn))) ltac:(vm_compute; reflexivity) R3 R4 ltac:(lia)) as [HPR Hra'];
  eapply (paj_ret_at (L := cmd_listing) (PL := PL_cmd) (PI := PI) W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity));
  let mat' := fresh "mat" in intros mat'; unfold ca_post, apost_base;
  lazymatch goal with |- exists _ _ _ _ _, mkCfg (mkst ?rg _ ?m _) ?d = _ /\ _ => exists ly, St, rg, m, d end;
  split; [rewrite Hra'; unfold YK0s.ret_ok in Hra; rewrite Hra; reflexivity|];
  split; [|split; [exact HPR | split; reflexivity]];
  unfold EV_CHECK_ARITY; apply (ajournal_materialize SEGS B LAWS pa_segs_low); exact HJ end).
Qed.

(* the scan: pass 0, then each pass hands over to the next, to a row lemma, or to the return *)
Lemma ca_scan : (forall k, (k < 22)%nat -> ca_row_ok k (fst (ca_ar k)) (snd (ca_ar k))) ->
forall ly St W regs0 mem0 md0 p0 v s3v regs memc mdc,
ca_lpre 0 ly St W regs0 mem0 md0 p0 v s3v regs memc mdc ->
SRr SEGS W (cfg_at SEGS (BASE + CE_LOOP) regs memc mdc) (ca_post B regs0 ly St W mem0 md0).
Proof.
intros ROWS ly St W regs0 mem0 md0 p0 v s3v.
assert (P21 : forall regs memc mdc, ca_lpre 21 ly St W regs0 mem0 md0 p0 v s3v regs memc mdc ->
  SRr SEGS W (cfg_at SEGS (BASE + CE_LOOP) regs memc mdc) (ca_post B regs0 ly St W mem0 md0))
  by (intros regs memc mdc HP; apply (ca_iter_21 (ROWS 21%nat ltac:(lia)) _ _ _ _ _ _ _ _ _ _ _ _ HP); intros Hk; exfalso; exact (Nat.lt_irrefl 22 Hk)).
assert (P20 : forall regs memc mdc, ca_lpre 20 ly St W regs0 mem0 md0 p0 v s3v regs memc mdc ->
  SRr SEGS W (cfg_at SEGS (BASE + CE_LOOP) regs memc mdc) (ca_post B regs0 ly St W mem0 md0))
  by (intros regs memc mdc HP; apply (ca_iter_20 (ROWS 20%nat ltac:(lia)) _ _ _ _ _ _ _ _ _ _ _ _ HP); intros _; exact P21).
assert (P19 : forall regs memc mdc, ca_lpre 19 ly St W regs0 mem0 md0 p0 v s3v regs memc mdc ->
  SRr SEGS W (cfg_at SEGS (BASE + CE_LOOP) regs memc mdc) (ca_post B regs0 ly St W mem0 md0))
  by (intros regs memc mdc HP; apply (ca_iter_19 (ROWS 19%nat ltac:(lia)) _ _ _ _ _ _ _ _ _ _ _ _ HP); intros _; exact P20).
assert (P18 : forall regs memc mdc, ca_lpre 18 ly St W regs0 mem0 md0 p0 v s3v regs memc mdc ->
  SRr SEGS W (cfg_at SEGS (BASE + CE_LOOP) regs memc mdc) (ca_post B regs0 ly St W mem0 md0))
  by (intros regs memc mdc HP; apply (ca_iter_18 (ROWS 18%nat ltac:(lia)) _ _ _ _ _ _ _ _ _ _ _ _ HP); intros _; exact P19).
assert (P17 : forall regs memc mdc, ca_lpre 17 ly St W regs0 mem0 md0 p0 v s3v regs memc mdc ->
  SRr SEGS W (cfg_at SEGS (BASE + CE_LOOP) regs memc mdc) (ca_post B regs0 ly St W mem0 md0))
  by (intros regs memc mdc HP; apply (ca_iter_17 (ROWS 17%nat ltac:(lia)) _ _ _ _ _ _ _ _ _ _ _ _ HP); intros _; exact P18).
assert (P16 : forall regs memc mdc, ca_lpre 16 ly St W regs0 mem0 md0 p0 v s3v regs memc mdc ->
  SRr SEGS W (cfg_at SEGS (BASE + CE_LOOP) regs memc mdc) (ca_post B regs0 ly St W mem0 md0))
  by (intros regs memc mdc HP; apply (ca_iter_16 (ROWS 16%nat ltac:(lia)) _ _ _ _ _ _ _ _ _ _ _ _ HP); intros _; exact P17).
assert (P15 : forall regs memc mdc, ca_lpre 15 ly St W regs0 mem0 md0 p0 v s3v regs memc mdc ->
  SRr SEGS W (cfg_at SEGS (BASE + CE_LOOP) regs memc mdc) (ca_post B regs0 ly St W mem0 md0))
  by (intros regs memc mdc HP; apply (ca_iter_15 (ROWS 15%nat ltac:(lia)) _ _ _ _ _ _ _ _ _ _ _ _ HP); intros _; exact P16).
assert (P14 : forall regs memc mdc, ca_lpre 14 ly St W regs0 mem0 md0 p0 v s3v regs memc mdc ->
  SRr SEGS W (cfg_at SEGS (BASE + CE_LOOP) regs memc mdc) (ca_post B regs0 ly St W mem0 md0))
  by (intros regs memc mdc HP; apply (ca_iter_14 (ROWS 14%nat ltac:(lia)) _ _ _ _ _ _ _ _ _ _ _ _ HP); intros _; exact P15).
assert (P13 : forall regs memc mdc, ca_lpre 13 ly St W regs0 mem0 md0 p0 v s3v regs memc mdc ->
  SRr SEGS W (cfg_at SEGS (BASE + CE_LOOP) regs memc mdc) (ca_post B regs0 ly St W mem0 md0))
  by (intros regs memc mdc HP; apply (ca_iter_13 (ROWS 13%nat ltac:(lia)) _ _ _ _ _ _ _ _ _ _ _ _ HP); intros _; exact P14).
assert (P12 : forall regs memc mdc, ca_lpre 12 ly St W regs0 mem0 md0 p0 v s3v regs memc mdc ->
  SRr SEGS W (cfg_at SEGS (BASE + CE_LOOP) regs memc mdc) (ca_post B regs0 ly St W mem0 md0))
  by (intros regs memc mdc HP; apply (ca_iter_12 (ROWS 12%nat ltac:(lia)) _ _ _ _ _ _ _ _ _ _ _ _ HP); intros _; exact P13).
assert (P11 : forall regs memc mdc, ca_lpre 11 ly St W regs0 mem0 md0 p0 v s3v regs memc mdc ->
  SRr SEGS W (cfg_at SEGS (BASE + CE_LOOP) regs memc mdc) (ca_post B regs0 ly St W mem0 md0))
  by (intros regs memc mdc HP; apply (ca_iter_11 (ROWS 11%nat ltac:(lia)) _ _ _ _ _ _ _ _ _ _ _ _ HP); intros _; exact P12).
assert (P10 : forall regs memc mdc, ca_lpre 10 ly St W regs0 mem0 md0 p0 v s3v regs memc mdc ->
  SRr SEGS W (cfg_at SEGS (BASE + CE_LOOP) regs memc mdc) (ca_post B regs0 ly St W mem0 md0))
  by (intros regs memc mdc HP; apply (ca_iter_10 (ROWS 10%nat ltac:(lia)) _ _ _ _ _ _ _ _ _ _ _ _ HP); intros _; exact P11).
assert (P9 : forall regs memc mdc, ca_lpre 9 ly St W regs0 mem0 md0 p0 v s3v regs memc mdc ->
  SRr SEGS W (cfg_at SEGS (BASE + CE_LOOP) regs memc mdc) (ca_post B regs0 ly St W mem0 md0))
  by (intros regs memc mdc HP; apply (ca_iter_9 (ROWS 9%nat ltac:(lia)) _ _ _ _ _ _ _ _ _ _ _ _ HP); intros _; exact P10).
assert (P8 : forall regs memc mdc, ca_lpre 8 ly St W regs0 mem0 md0 p0 v s3v regs memc mdc ->
  SRr SEGS W (cfg_at SEGS (BASE + CE_LOOP) regs memc mdc) (ca_post B regs0 ly St W mem0 md0))
  by (intros regs memc mdc HP; apply (ca_iter_8 (ROWS 8%nat ltac:(lia)) _ _ _ _ _ _ _ _ _ _ _ _ HP); intros _; exact P9).
assert (P7 : forall regs memc mdc, ca_lpre 7 ly St W regs0 mem0 md0 p0 v s3v regs memc mdc ->
  SRr SEGS W (cfg_at SEGS (BASE + CE_LOOP) regs memc mdc) (ca_post B regs0 ly St W mem0 md0))
  by (intros regs memc mdc HP; apply (ca_iter_7 (ROWS 7%nat ltac:(lia)) _ _ _ _ _ _ _ _ _ _ _ _ HP); intros _; exact P8).
assert (P6 : forall regs memc mdc, ca_lpre 6 ly St W regs0 mem0 md0 p0 v s3v regs memc mdc ->
  SRr SEGS W (cfg_at SEGS (BASE + CE_LOOP) regs memc mdc) (ca_post B regs0 ly St W mem0 md0))
  by (intros regs memc mdc HP; apply (ca_iter_6 (ROWS 6%nat ltac:(lia)) _ _ _ _ _ _ _ _ _ _ _ _ HP); intros _; exact P7).
assert (P5 : forall regs memc mdc, ca_lpre 5 ly St W regs0 mem0 md0 p0 v s3v regs memc mdc ->
  SRr SEGS W (cfg_at SEGS (BASE + CE_LOOP) regs memc mdc) (ca_post B regs0 ly St W mem0 md0))
  by (intros regs memc mdc HP; apply (ca_iter_5 (ROWS 5%nat ltac:(lia)) _ _ _ _ _ _ _ _ _ _ _ _ HP); intros _; exact P6).
assert (P4 : forall regs memc mdc, ca_lpre 4 ly St W regs0 mem0 md0 p0 v s3v regs memc mdc ->
  SRr SEGS W (cfg_at SEGS (BASE + CE_LOOP) regs memc mdc) (ca_post B regs0 ly St W mem0 md0))
  by (intros regs memc mdc HP; apply (ca_iter_4 (ROWS 4%nat ltac:(lia)) _ _ _ _ _ _ _ _ _ _ _ _ HP); intros _; exact P5).
assert (P3 : forall regs memc mdc, ca_lpre 3 ly St W regs0 mem0 md0 p0 v s3v regs memc mdc ->
  SRr SEGS W (cfg_at SEGS (BASE + CE_LOOP) regs memc mdc) (ca_post B regs0 ly St W mem0 md0))
  by (intros regs memc mdc HP; apply (ca_iter_3 (ROWS 3%nat ltac:(lia)) _ _ _ _ _ _ _ _ _ _ _ _ HP); intros _; exact P4).
assert (P2 : forall regs memc mdc, ca_lpre 2 ly St W regs0 mem0 md0 p0 v s3v regs memc mdc ->
  SRr SEGS W (cfg_at SEGS (BASE + CE_LOOP) regs memc mdc) (ca_post B regs0 ly St W mem0 md0))
  by (intros regs memc mdc HP; apply (ca_iter_2 (ROWS 2%nat ltac:(lia)) _ _ _ _ _ _ _ _ _ _ _ _ HP); intros _; exact P3).
assert (P1 : forall regs memc mdc, ca_lpre 1 ly St W regs0 mem0 md0 p0 v s3v regs memc mdc ->
  SRr SEGS W (cfg_at SEGS (BASE + CE_LOOP) regs memc mdc) (ca_post B regs0 ly St W mem0 md0))
  by (intros regs memc mdc HP; apply (ca_iter_1 (ROWS 1%nat ltac:(lia)) _ _ _ _ _ _ _ _ _ _ _ _ HP); intros _; exact P2).
assert (P0 : forall regs memc mdc, ca_lpre 0 ly St W regs0 mem0 md0 p0 v s3v regs memc mdc ->
  SRr SEGS W (cfg_at SEGS (BASE + CE_LOOP) regs memc mdc) (ca_post B regs0 ly St W mem0 md0))
  by (intros regs memc mdc HP; apply (ca_iter_0 (ROWS 0%nat ltac:(lia)) _ _ _ _ _ _ _ _ _ _ _ _ HP); intros _; exact P1).
exact P0.
Qed.
(** ** The assembled proof of tcheck_arity_spec (lib/B/Prog/check_arity_c.v) *)
Hypothesis ABCMP : forall fx0 : YK11.FPState, @abcmp_realizes fx0 rc SEGS B (SIGMA CS___interceptor_trampoline_bcmp).
Variable MT : ameter_ops.

(* the 22 row lemmas in one shape: check_arity_s4.v (rows 1 2 4-7 9-13 15-21) and check_arity_r0/r3/r8/r14.v *)
Lemma ca_rows : cmd_val_objs -> forall k, (k < 22)%nat -> ca_row_ok k (fst (ca_ar k)) (snd (ca_ar k)).
Proof.
intros HVO k Hk.
destruct k as [|k]; [exact (ca_row_0 B HB ABCMP HVO)|].
destruct k as [|k]; [intros ly St W0 regs0 mem0 md0 W regs memc mdc s3v HP _ _; exact (ca_row_1 B HB ly St W0 regs0 mem0 md0 W regs memc mdc s3v HP)|].
destruct k as [|k]; [intros ly St W0 regs0 mem0 md0 W regs memc mdc s3v HP _ _; exact (ca_row_2 B HB ly St W0 regs0 mem0 md0 W regs memc mdc s3v HP)|].
destruct k as [|k]; [exact (ca_row_3 B HB ABCMP HVO)|].
destruct k as [|k]; [intros ly St W0 regs0 mem0 md0 W regs memc mdc s3v HP _ _; exact (ca_row_4 B HB ly St W0 regs0 mem0 md0 W regs memc mdc s3v HP)|].
destruct k as [|k]; [intros ly St W0 regs0 mem0 md0 W regs memc mdc s3v HP _ _; exact (ca_row_5 B HB ly St W0 regs0 mem0 md0 W regs memc mdc s3v HP)|].
destruct k as [|k]; [intros ly St W0 regs0 mem0 md0 W regs memc mdc s3v HP _ _; exact (ca_row_6 B HB ly St W0 regs0 mem0 md0 W regs memc mdc s3v HP)|].
destruct k as [|k]; [intros ly St W0 regs0 mem0 md0 W regs memc mdc s3v HP _ _; exact (ca_row_7 B HB ly St W0 regs0 mem0 md0 W regs memc mdc s3v HP)|].
destruct k as [|k]; [exact (ca_row_8 B HB ABCMP HVO)|].
destruct k as [|k]; [intros ly St W0 regs0 mem0 md0 W regs memc mdc s3v HP _ _; exact (ca_row_9 B HB ly St W0 regs0 mem0 md0 W regs memc mdc s3v HP)|].
destruct k as [|k]; [intros ly St W0 regs0 mem0 md0 W regs memc mdc s3v HP _ _; exact (ca_row_10 B HB ly St W0 regs0 mem0 md0 W regs memc mdc s3v HP)|].
destruct k as [|k]; [intros ly St W0 regs0 mem0 md0 W regs memc mdc s3v HP _ _; exact (ca_row_11 B HB ly St W0 regs0 mem0 md0 W regs memc mdc s3v HP)|].
destruct k as [|k]; [intros ly St W0 regs0 mem0 md0 W regs memc mdc s3v HP _ _; exact (ca_row_12 B HB ly St W0 regs0 mem0 md0 W regs memc mdc s3v HP)|].
destruct k as [|k]; [intros ly St W0 regs0 mem0 md0 W regs memc mdc s3v HP _ _; exact (ca_row_13 B HB ly St W0 regs0 mem0 md0 W regs memc mdc s3v HP)|].
destruct k as [|k]; [exact (ca_row_14 B HB ABCMP HVO)|].
destruct k as [|k]; [intros ly St W0 regs0 mem0 md0 W regs memc mdc s3v HP _ _; exact (ca_row_15 B HB ly St W0 regs0 mem0 md0 W regs memc mdc s3v HP)|].
destruct k as [|k]; [intros ly St W0 regs0 mem0 md0 W regs memc mdc s3v HP _ _; exact (ca_row_16 B HB ly St W0 regs0 mem0 md0 W regs memc mdc s3v HP)|].
destruct k as [|k]; [intros ly St W0 regs0 mem0 md0 W regs memc mdc s3v HP _ _; exact (ca_row_17 B HB ly St W0 regs0 mem0 md0 W regs memc mdc s3v HP)|].
destruct k as [|k]; [intros ly St W0 regs0 mem0 md0 W regs memc mdc s3v HP _ _; exact (ca_row_18 B HB ly St W0 regs0 mem0 md0 W regs memc mdc s3v HP)|].
destruct k as [|k]; [intros ly St W0 regs0 mem0 md0 W regs memc mdc s3v HP _ _; exact (ca_row_19 B HB ly St W0 regs0 mem0 md0 W regs memc mdc s3v HP)|].
destruct k as [|k]; [intros ly St W0 regs0 mem0 md0 W regs memc mdc s3v HP _ _; exact (ca_row_20 B HB ly St W0 regs0 mem0 md0 W regs memc mdc s3v HP)|].
destruct k as [|k]; [intros ly St W0 regs0 mem0 md0 W regs memc mdc s3v HP _ _; exact (ca_row_21 B HB ly St W0 regs0 mem0 md0 W regs memc mdc s3v HP)|].
lia.
Qed.

Theorem pb_check_arity : tcheck_arity_spec B MT.
Proof.
unfold tcheck_arity_spec.
intros ly St W regs mem md wp t ww p0 q nc fn0 v HPRE HRO HROK HOBJ H10 Rwp Hwp8 Hwp1 Hwp2 Ht Rt Hww Rww H4 Hq Rq Hnc Rnc Hfn
  Har Hev.
eapply SRr_mono.
{ apply (ce_walk ly St W regs mem md wp t ww p0 q nc fn0 v HPRE HRO HROK HOBJ H10 Rwp Hwp8 Hwp1 Hwp2 Ht Rt Hww Rww H4 Hq Rq
    Hnc Rnc Hfn Har).
  intros regsc memc mdc HP.
  exact (ca_scan (ca_rows HOBJ) ly St W regs mem md p0 v (Z.min t 64) regsc memc mdc HP). }
cbv beta. intros W' c' _ Hpost.
unfold ca_post, apost_base in Hpost. unfold apost_base.
destruct Hpost as (ly' & St' & rg & m & d & Hc & HJ & HP & Hly & HSt). subst ly' St'.
exists ly, St, rg, m, d. split; [exact Hc|]. split; [exact HJ|]. split; [exact HP|].
split; [apply Permutation_refl | split; reflexivity].
Qed.

End e.
End f.
End d.
