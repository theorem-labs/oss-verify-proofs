(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the program walk of rec_canonical on the ASan build of
   plugin-hostd/fuzz_command, in the shape of cgif_file_fuzzer's walks (lib/A/AC8b.v: a loop walked by the
   symbolic executor over the position-abstract listing, its inline shadow checks removed by tok_load/tok_branch)
   and of this unit's xstrdup walk (the malloc call through amalloc04_sub of PaCall.v).
   The walk is cut at six points: the malloc return (0x89338: the null check, decided by the executor, and the
   empty-line check), the outer head (0x89354), the word-scan head (0x89364), the word start (0x893a0), the copy
   head (0x893e8) and the tail (0x89474); the model of the output is lib/Prog/RecFacts.v's
   canon T = join_sp (words T), and the word lemmas below are the Words section of fuzz_command's own released
   plain proof lib/Prog/rec_canonical.v, copied so that the walk stands on RecFacts alone. The walk's hypotheses are
   the statement's AMALLOC4 and TL (CmdPaLib.v: the malloc trampoline is the rule's entry, the GOT shadow cell). *)
(* Modified by Theorem Labs, 2026-10: re-walked from lib/A/Prog/rec_canonical.v (a working branch 1d526f2e737) for
   fuzz_command.asan-ubsan (entry 0x897e8, 115 instructions). The malloc wrapper call and its null/abort edge are one
   program call of xmalloc here (0x89814, PCall CS_xmalloc), taken through cl_callS (PaCall.v) with the statement's
   HXMALLOC at the walk's own fx and HSIG (cmd_sig_prog, CmdObj.v: the call target); s0 holds len there, below
   alloc_ceiling, so achain_low gives xmalloc's frame chain, and xmalloc's journal keeps the frame. The copy loop
   keeps i (a4) and o (a3) and recomputes text + i and out + o per byte; ~out (a2), ~text (a5) and text != 0 (a6)
   feed the UBSan checks. The walk is cut at the xmalloc return (0x89818: the empty-line check), the outer head
   (0x8983c), the word-scan head (0x8984c), the word start (0x8989c), the copy head (0x898d0), the tail (0x89954) and
   the store of the terminator (0x8995c, where the empty line enters). Of the seven UBSan trap branches (to the unimp
   at 0x89988) the executor decides six from the seeds' facts: 0x8985c and 0x89860 from text, text + i >= 4096 (the
   block law), 0x898a4, 0x898d0, 0x898f4 and 0x89954 from ~out, ~text >= 2^64 - 1 - CEIL_MAX and o, i <= LMAX; the
   walk refutes 0x89850 (text + i < text) at the branch, since text + i < 2^64. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaStep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YI16 YG0p YC5d YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YI08.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaDenot PaSB PaLibG PaLibH PaLibF PaCallRun PaCall.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdBase CmdRep CmdObj xmalloc_c rec_canonical_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ------------------------------------------------------------------ *)
(* The word model.  These are the lemmas of the Words section of fuzz_command's released plain proof
   lib/Prog/rec_canonical.v, over RecFacts.v's words / join_sp / canon. *)
Local Open Scope Z_scope.

Definition rcn_sep_start (S : list byte) : Prop := S = [] \/ exists b S', S = b :: S' /\ is_sep b = true.

Lemma rcn_words_go_app_sep : forall A cur S, rcn_sep_start S ->
  words_go cur (A ++ S) = words_go cur A ++ words_go [] S.
Proof.
  induction A as [|a A IH]; intros cur S HS.
  - cbn [app]. destruct HS as [-> | (b & S' & -> & Hb)].
    + destruct cur; reflexivity.
    + cbn [words_go]. rewrite Hb. destruct cur as [|c cur]; reflexivity.
  - cbn [app words_go]. destruct (is_sep a).
    + destruct cur as [|c cur]; [apply IH; exact HS|]. rewrite IH by exact HS. reflexivity.
    + apply IH. exact HS.
Qed.

Lemma rcn_words_go_skip : forall S X, Forall (fun b => is_sep b = true) S -> words_go [] (S ++ X) = words_go [] X.
Proof.
  induction S as [|b S IH]; intros X H; [reflexivity|].
  inversion H as [|? ? Hb HS]; subst. cbn [app words_go]. rewrite Hb. apply IH. exact HS.
Qed.

Lemma rcn_words_go_nonsep : forall w cur, Forall (fun b => is_sep b = false) w ->
  words_go cur w = match rev w ++ cur with [] => [] | _ :: _ => [rev (rev w ++ cur)] end.
Proof.
  induction w as [|b w IH]; intros cur H.
  - destruct cur; reflexivity.
  - inversion H as [|? ? Hb Hw]; subst. cbn [words_go]. rewrite Hb. rewrite IH by exact Hw.
    cbn [rev]. rewrite <- app_assoc. reflexivity.
Qed.

Lemma rcn_words_go_word : forall w, w <> [] -> Forall (fun b => is_sep b = false) w -> words_go [] w = [w].
Proof.
  intros w Hne H. rewrite rcn_words_go_nonsep by exact H. rewrite app_nil_r.
  destruct (rev w) as [|x r] eqn:E.
  - exfalso. apply Hne. apply (f_equal (@rev byte)) in E. rewrite rev_involutive in E. exact E.
  - rewrite <- E, rev_involutive. reflexivity.
Qed.

Lemma rcn_rev_cons_ne : forall (c : byte) cur, rev (c :: cur) <> [].
Proof. intros c cur E. apply (f_equal (@length byte)) in E. rewrite length_rev in E. discriminate. Qed.

Lemma rcn_words_go_ne : forall T cur, Forall (fun w => w <> []) (words_go cur T).
Proof.
  induction T as [|b T IH]; intros cur.
  - destruct cur as [|c cur]; cbn [words_go]; [constructor|]. constructor; [apply rcn_rev_cons_ne | constructor].
  - cbn [words_go]. destruct (is_sep b); [|apply IH].
    destruct cur as [|c cur]; [apply IH|]. constructor; [apply rcn_rev_cons_ne | apply IH].
Qed.

Lemma rcn_join_sp_cons2 : forall x y X, join_sp (x :: y :: X) = x ++ SPACE :: join_sp (y :: X).
Proof. reflexivity. Qed.

Lemma rcn_join_sp_snoc : forall X w,
  join_sp (X ++ [w]) = match X with [] => w | _ :: _ => join_sp X ++ SPACE :: w end.
Proof.
  induction X as [|x X IH]; intros w; [reflexivity|].
  destruct X as [|y X']; [reflexivity|].
  change ((x :: y :: X') ++ [w]) with (x :: y :: (X' ++ [w])).
  rewrite rcn_join_sp_cons2. change (y :: (X' ++ [w])) with ((y :: X') ++ [w]). rewrite IH.
  rewrite rcn_join_sp_cons2. rewrite <- app_assoc. reflexivity.
Qed.

Lemma rcn_join_sp_nil : forall X, Forall (fun w => w <> []) X -> join_sp X = [] -> X = [].
Proof.
  intros X HF E. destruct X as [|x X]; [reflexivity|]. exfalso.
  inversion HF as [|? ? Hx _]; subst.
  destruct X as [|y X]; cbn [join_sp] in E; [exact (Hx E)|].
  destruct x; discriminate.
Qed.

Lemma rcn_firstn_add : forall (T : list byte) i d, firstn (i + d) T = firstn i T ++ firstn d (skipn i T).
Proof.
  intros T i. revert T. induction i as [|i IH]; intros T d; [reflexivity|].
  destruct T as [|t T]; [destruct d; reflexivity|]. cbn [Nat.add firstn skipn app]. rewrite IH. reflexivity.
Qed.

Lemma rcn_skipn_nth : forall (T : list byte) i b, nth_error T i = Some b -> skipn i T = b :: skipn (S i) T.
Proof.
  induction T as [|t T IH]; intros i b H; [destruct i; discriminate|].
  destruct i as [|i]; cbn in H |- *; [injection H as ->; reflexivity|]. apply IH. exact H.
Qed.

Lemma rcn_Forall_seg : forall (P : byte -> Prop) T i d,
  (forall t b, (i <= t < i + d)%nat -> nth_error T t = Some b -> P b) -> Forall P (firstn d (skipn i T)).
Proof.
  intros P T. induction T as [|x T IH]; intros i d H.
  - rewrite skipn_nil, firstn_nil. constructor.
  - destruct i as [|i].
    + destruct d as [|d]; cbn [skipn firstn]; [constructor|]. constructor.
      * apply (H 0%nat); [lia | reflexivity].
      * apply (IH 0%nat d). intros t b Ht Hb. apply (H (S t)); [lia | exact Hb].
    + cbn [skipn]. apply IH. intros t b Ht Hb. apply (H (S t)); [lia | exact Hb].
Qed.

Lemma rcn_seg_ne : forall (T : list byte) j d, (j < length T)%nat -> (0 < d)%nat -> firstn d (skipn j T) <> [].
Proof.
  intros T j d Hj Hd. destruct (nth_error T j) as [b|] eqn:E; [|apply nth_error_None in E; lia].
  rewrite (rcn_skipn_nth T j b E). destruct d; [lia|]. discriminate.
Qed.

Definition rcn_bndry (T : list byte) (i : nat) : Prop :=
  i = 0%nat \/ exists b, nth_error T i = Some b /\ is_sep b = true.

Lemma rcn_pass_words : forall T i j k, rcn_bndry T i -> (i <= j < k)%nat -> (k <= length T)%nat ->
  (forall t b, (i <= t < j)%nat -> nth_error T t = Some b -> is_sep b = true) ->
  (forall t b, (j <= t < k)%nat -> nth_error T t = Some b -> is_sep b = false) ->
  words (firstn k T) = words (firstn i T) ++ [firstn (k - j) (skipn j T)].
Proof.
  intros T i j k HB Hij Hk HS HW.
  assert (E : firstn k T = firstn i T ++ (firstn (j - i) (skipn i T) ++ firstn (k - j) (skipn j T))).
  { replace k with (i + ((j - i) + (k - j)))%nat at 1 by lia. rewrite rcn_firstn_add. f_equal.
    rewrite rcn_firstn_add, skipn_skipn. replace (j - i + i)%nat with j by lia. reflexivity. }
  assert (FS : Forall (fun b => is_sep b = true) (firstn (j - i) (skipn i T))).
  { apply rcn_Forall_seg. intros t b Ht Hb. apply (HS t b); [lia | exact Hb]. }
  assert (FW : Forall (fun b => is_sep b = false) (firstn (k - j) (skipn j T))).
  { apply rcn_Forall_seg. intros t b Ht Hb. apply (HW t b); [lia | exact Hb]. }
  assert (NE : firstn (k - j) (skipn j T) <> []) by (apply rcn_seg_ne; lia).
  unfold words. rewrite E. destruct HB as [-> | (b & Eb & Sb)].
  - change (firstn 0 T) with (@nil byte). rewrite app_nil_l. cbn [words_go app].
    rewrite rcn_words_go_skip by exact FS. apply rcn_words_go_word; assumption.
  - assert (Hji : (i < j)%nat).
    { destruct (Nat.eq_dec i j) as [Eij|]; [|lia]. exfalso. rewrite <- Eij in HW.
      pose proof (HW i b ltac:(lia) Eb) as C. rewrite Sb in C. discriminate. }
    rewrite rcn_words_go_app_sep.
    + f_equal. rewrite rcn_words_go_skip by exact FS. apply rcn_words_go_word; assumption.
    + right. rewrite (rcn_skipn_nth T i b Eb). destruct (j - i)%nat as [|d] eqn:Ed; [lia|].
      exists b, (firstn d (skipn (S i) T) ++ firstn (k - j) (skipn j T)). split; [reflexivity | exact Sb].
Qed.

Lemma rcn_end_words : forall T i, rcn_bndry T i -> (i <= length T)%nat ->
  (forall t b, (i <= t < length T)%nat -> nth_error T t = Some b -> is_sep b = true) ->
  words T = words (firstn i T).
Proof.
  intros T i HB Hi HS.
  assert (FS : Forall (fun b => is_sep b = true) (skipn i T)).
  { assert (E2 : firstn (length T - i) (skipn i T) = skipn i T) by (apply firstn_all2; rewrite length_skipn; lia).
    rewrite <- E2.
    apply rcn_Forall_seg. intros t b Ht Hb. apply (HS t b); [lia | exact Hb]. }
  unfold words. rewrite <- (firstn_skipn i T) at 1. destruct HB as [-> | (b & Eb & Sb)].
  - change (firstn 0 T) with (@nil byte). change (skipn 0 T) with T in *. rewrite app_nil_l.
    rewrite <- (app_nil_r T) at 1. rewrite rcn_words_go_skip by exact FS. reflexivity.
  - rewrite rcn_words_go_app_sep.
    + rewrite <- (app_nil_r (skipn i T)). rewrite rcn_words_go_skip by exact FS. apply app_nil_r.
    + right. rewrite (rcn_skipn_nth T i b Eb). exists b, (skipn (S i) T). split; [reflexivity | exact Sb].
Qed.

Lemma rcn_canon_snoc : forall X w,
  join_sp (words X ++ [w]) = match canon X with [] => w | _ :: _ => canon X ++ SPACE :: w end.
Proof.
  intros X w. rewrite rcn_join_sp_snoc. unfold canon.
  destruct (words X) as [|x Y] eqn:E; [reflexivity|].
  destruct (join_sp (x :: Y)) as [|c r] eqn:J; [|reflexivity].
  exfalso. assert (HF : Forall (fun w0 => w0 <> []) (x :: Y)) by (rewrite <- E; apply rcn_words_go_ne).
  pose proof (rcn_join_sp_nil _ HF J). discriminate.
Qed.

Lemma rcn_canon_step : forall T i j k out out0, rcn_bndry T i -> (i <= j < k)%nat ->
  (k <= length T)%nat ->
  (forall t b, (i <= t < j)%nat -> nth_error T t = Some b -> is_sep b = true) ->
  (forall t b, (j <= t < k)%nat -> nth_error T t = Some b -> is_sep b = false) ->
  out = canon (firstn i T) ->
  out0 = match out with [] => [] | _ :: _ => out ++ [SPACE] end ->
  canon (firstn k T) = out0 ++ firstn (k - j) (skipn j T).
Proof.
  intros T i j k out out0 HB Hij Hk HS HW Ho Ho0. unfold canon at 1.
  rewrite (rcn_pass_words T i j k) by assumption.
  rewrite rcn_canon_snoc. subst out out0.
  destruct (canon (firstn i T)); [reflexivity|]. rewrite <- app_assoc. reflexivity.
Qed.

Lemma rcn_firstn_snoc : forall (X : list byte) a b, nth_error X a = Some b -> firstn (S a) X = firstn a X ++ [b].
Proof.
  intros X a b E. replace (S a) with (a + 1)%nat by lia. rewrite rcn_firstn_add.
  rewrite (rcn_skipn_nth X a b E). reflexivity.
Qed.

Lemma rcn_canon_len_firstn : forall T i, (Z.of_nat (length (canon (firstn i T))) <= Z.of_nat i)%Z.
Proof.
  intros T i. pose proof (canon_length (firstn i T)) as H. rewrite length_firstn in H. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* bit-vector helpers *)

Lemma rcn_byte_range : forall b : byte, 0 <= bv_unsigned b < 256.
Proof.
  intros b. pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R.
  change (2 ^ Z.of_N 8) with 256 in R. exact R.
Qed.

Lemma rcn_alu_add : forall x y, alu64 ALU_ADD (Z_to_bv 64 x) (Z_to_bv 64 y) = Z_to_bv 64 (x + y).
Proof.
  intros x y. apply bv_eq. rewrite alu64_unsigned. cbn [zalu_raw]. rewrite !Z_to_bv_unsigned.
  unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite <- Zplus_mod. reflexivity.
Qed.

Lemma rcn_le_byte1 : forall v, 0 <= v < 256 -> le_byte v 1 0 = v.
Proof.
  intros v Hv. unfold le_byte. change (2 ^ (8 * Z.of_nat 1)) with 256. change (8 * Z.of_nat 0) with 0.
  rewrite Z.shiftr_0_r, (Z.mod_small v 256) by lia. apply Z.mod_small. lia.
Qed.

Lemma rcn_bytes_prefix : forall rd a l (x : byte), abytes_atR rd a (l ++ [x]) -> abytes_atR rd a l.
Proof.
  intros rd a l x H i Hi. rewrite (H i) by (rewrite length_app; cbn [length]; lia).
  rewrite app_nth1 by exact Hi. reflexivity.
Qed.

Lemma rcn_bytes_nth : forall rd a l i (b : byte), abytes_atR rd a l -> nth_error l i = Some b ->
  rd (a + Z.of_nat i) = Some (bv_unsigned b).
Proof.
  intros rd a l i b H E. assert (Hi : (i < length l)%nat) by (apply nth_error_Some; rewrite E; discriminate).
  rewrite (H i Hi). f_equal. f_equal. apply nth_error_nth. exact E.
Qed.

Lemma rcn_bytes_snoc : forall rd a l (x : byte),
  abytes_atR rd a l -> rd (a + Z.of_nat (length l)) = Some (bv_unsigned x) -> abytes_atR rd a (l ++ [x]).
Proof.
  intros rd a l x H Hx i Hi. rewrite length_app in Hi. cbn [length] in Hi.
  destruct (Nat.lt_ge_cases i (length l)) as [Hlt|Hge].
  - rewrite app_nth1 by exact Hlt. exact (H i Hlt).
  - assert (i = length l) by lia. subst i. rewrite nth_middle. exact Hx.
Qed.

Lemma rcn_bytes_ext : forall (rd rd' : reader) a l,
  (forall i, 0 <= i < Z.of_nat (length l) -> rd' (a + i) = rd (a + i)) -> abytes_atR rd a l -> abytes_atR rd' a l.
Proof. intros rd rd' a l He H i Hi. rewrite He by lia. exact (H i Hi). Qed.


(* the bitwise complement the UBSan checks compare against (`not a2,a0`, `not a5,s1`) *)
Definition NOTW (v : Z) : Z := 2 ^ 64 - 1 - v.

Lemma rcn_den_not : forall (E : env) m v x, ew E m = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  Z_to_bv 64 x = Z_to_bv 64 (-1) ->
  sv_denot E (SAlu ALU_XOR (SOff m 0) (SLit x)) = Z_to_bv 64 (NOTW v).
Proof.
  intros E m v x Hm Hv Hx. cbn [sv_denot]. rewrite Hm, Hx. rewrite unsigned_lit_small by lia. rewrite Z.add_0_r.
  apply bv_eq. rewrite alu64_unsigned. cbn [zalu_raw]. rewrite !Z_to_bv_unsigned.
  unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite (Z.mod_small v) by lia.
  change ((-1) mod 2 ^ 64) with (2 ^ 64 - 1). rewrite YI08.lxor_allones by lia. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* the cut points of the walk, and the symbolic state the executor is seeded with at each of them *)
Definition K_ENTRY : Z := AF_rec_canonical.
Definition K_MALLOCRET : Z := 0x32e8.
Definition K_OUTER : Z := 0x330c.
Definition K_SKIP : Z := 0x331c.
Definition K_WORD : Z := 0x336c.
Definition K_COPY : Z := 0x33a0.
Definition K_FIN : Z := 0x3424.
Definition K_FIN0 : Z := 0x342c.

(* ~p for a block or text pointer p <= CEIL_MAX (alloc_ceiling's upper bound, YM05.v) *)
Definition NOTF : afact := mkAF (2 ^ 64 - 1 - 140737479966720) (2 ^ 64 - 1) 0.

Definition rcn_ss_entry : sstate :=
  mkSS K_ENTRY sr_atoms [stack_region 32; got_regionP; bcell_regionP 32] None
    (mkFacts [(2%nat, mkAF (2^46) (2^47) 4); (32%nat, mkAF SB SB 0)] [] []).

Definition rcn_ss_mret : sstate :=
  mkSS K_MALLOCRET sr_atoms [] None
    (mkFacts [(2%nat, mkAF (2^46) (2^47) 4); (8%nat, mkAF 0 8192 0); (9%nat, PTR 0); (10%nat, PTR 0);
              (18%nat, mkAF SB SB 0)] [] []).

Definition rcn_ss_outer : sstate :=
  mkSS K_OUTER sr_atoms [] None
    (mkFacts [(2%nat, mkAF (2^46) (2^47) 4); (8%nat, mkAF 1 8192 0); (14%nat, mkAF 0 8191 0);
              (18%nat, mkAF SB SB 0)] [] []).

Definition rcn_ss_skip : sstate :=
  mkSS K_SKIP (sr_set (sr_set (sr_set (sr_set sr_atoms 17%bv (SLit 32)) 5%bv (SLit 9)) 16%bv (SLit 1)) 6%bv (SOff 8 0))
    [YP09.mkRegion (Some 32%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 33 0))]] None
    (mkFacts [(2%nat, mkAF (2^46) (2^47) 4); (8%nat, mkAF 1 8192 0); (9%nat, PTR 0); (10%nat, PTR 0);
              (13%nat, mkAF 0 8192 0); (14%nat, mkAF 0 8191 0); (18%nat, mkAF SB SB 0);
              (32%nat, PTR 0); (33%nat, mkAF 0 255 0)] []
       [(SAlu ALU_ADD (SOff 9 0) (SOff 14 0), SOff 32 0)]).

Definition rcn_ss_word : sstate :=
  mkSS K_WORD (sr_set (sr_set (sr_set sr_atoms 17%bv (SLit 32)) 5%bv (SLit 9)) 16%bv (SLit 1))
    [YP09.mkRegion (Some 32%nat) 0 1 0 1 []] None
    (mkFacts [(2%nat, mkAF (2^46) (2^47) 4); (8%nat, mkAF 1 8192 0); (9%nat, PTR 0); (10%nat, PTR 0);
              (12%nat, NOTF); (13%nat, mkAF 0 8192 0); (14%nat, mkAF 0 8192 0); (18%nat, mkAF SB SB 0);
              (32%nat, PTR 0)] []
       [(SAlu ALU_ADD (SOff 10 0) (SOff 13 0), SOff 32 0)]).
Definition rcn_sh_word : list shent := [mkSHE 32 1 0].

Definition rcn_ss_copy : sstate :=
  mkSS K_COPY (sr_set (sr_set (sr_set sr_atoms 17%bv (SLit 32)) 5%bv (SLit 9)) 16%bv (SLit 1))
    [YP09.mkRegion (Some 32%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 33 0))];
     YP09.mkRegion (Some 34%nat) 0 1 0 1 []] None
    (mkFacts [(2%nat, mkAF (2^46) (2^47) 4); (6%nat, mkAF 0 16384 0); (8%nat, mkAF 1 8192 0); (9%nat, PTR 0);
              (10%nat, PTR 0); (12%nat, NOTF); (13%nat, mkAF 0 8192 0); (14%nat, mkAF 0 8192 0);
              (15%nat, NOTF); (18%nat, mkAF SB SB 0); (32%nat, PTR 0); (33%nat, mkAF 0 255 0);
              (34%nat, PTR 0)] []
       [(SAlu ALU_ADD (SOff 9 0) (SOff 14 0), SOff 32 0); (SAlu ALU_ADD (SOff 10 0) (SOff 13 0), SOff 34 0)]).
Definition rcn_sh_copy : list shent := [mkSHE 34 1 0].

Definition rcn_ss_fin : sstate :=
  mkSS K_FIN sr_atoms [] None
    (mkFacts [(2%nat, mkAF (2^46) (2^47) 4); (10%nat, PTR 0); (12%nat, NOTF); (13%nat, mkAF 0 8192 0);
              (18%nat, mkAF SB SB 0)] [] []).

Definition rcn_ss_fin0 : sstate :=
  mkSS K_FIN0 sr_atoms
    [YP09.mkRegion (Some 11%nat) 0 1 0 1 [];
     YP09.mkRegion (Some 2%nat) 0 32 0 0
       [YP09.mkChunk 0 (CVal 8 (SOff 32 0)); YP09.mkChunk 8 (CVal 8 (SOff 33 0));
        YP09.mkChunk 16 (CVal 8 (SOff 34 0)); YP09.mkChunk 24 (CVal 8 (SOff 35 0))]] None
    (mkFacts [(2%nat, mkAF (2^46) (2^47) 4); (10%nat, PTR 0); (11%nat, PTR 0); (18%nat, mkAF SB SB 0)] [] []).
Definition rcn_sh_fin0 : list shent := [mkSHE 11 1 0].

(* the registers the walk never writes and hands back untouched *)
Definition rcn_kept : list (bv 5) := [3; 4; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
(* the registers each run leaves at their seeded atom *)
Definition rcn_ckeptall : list (bv 5) :=
  [2; 3; 4; 6; 8; 9; 10; 12; 15; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
Definition rcn_keptall : list (bv 5) :=
  [2; 3; 4; 8; 9; 10; 12; 13; 15; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
Definition rcn_wkeptall : list (bv 5) :=
  [2; 3; 4; 8; 9; 10; 12; 14; 15; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
Definition rcn_okeptall : list (bv 5) :=
  [2; 3; 4; 5; 8; 9; 10; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
Definition rcn_mkeptall : list (bv 5) :=
  [2; 3; 4; 8; 9; 10; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
Definition rcn_fkeptall : list (bv 5) :=
  [2; 3; 4; 8; 9; 10; 12; 13; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
Variable MT : ameter_ops.
(* the statement's program callee, at every FP state *)
Hypothesis HXMALLOC : forall fx0 : YK11.FPState, @txmalloc_spec fx0 rc SK PI B MT.
(* the GOT's shadow-base cell (CmdPaLib.v pal_got_shadow, pal_cell) *)
Hypothesis TL : PALib B.
(* the call target of xmalloc (CmdObj.v) *)
Hypothesis HSIG : cmd_sig_prog.

Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI). Let RET := paj_ret_at (PL := PL_cmd) (PI := PI).

Lemma rcn_val_mem1 : forall (W : world SEGS) (mem : word -> option byte) a (b : byte),
  rdW W mem a = Some (bv_unsigned b) -> val_mem SEGS (mrestrict (w_H W) mem) a 1 (bv_unsigned b).
Proof.
  intros W mem a b H k Hk. assert (k = 0%nat) as -> by lia. rewrite Z.add_0_r.
  pose proof (rcn_byte_range b) as HB.
  unfold aview in H. destruct (mbyte SEGS (mrestrict (w_H W) mem) a) as [b'|] eqn:Eb; [|discriminate H].
  cbn [option_map] in H. injection H as H.
  rewrite rcn_le_byte1 by lia. rewrite <- H, Z_to_bv_bv_unsigned. reflexivity.
Qed.

Lemma rcn_zero_chunk : forall (Ex : env), bv_unsigned (sv_denot Ex (SLit 0)) mod 2 ^ (8 * Z.of_N 1) = 0.
Proof. intros Ex. cbn [sv_denot]. vm_compute. reflexivity. Qed.

Lemma rcn_rd_of_val_mem1 : forall (W : world SEGS) (mem : word -> option byte) a v,
  0 <= v < 256 -> val_mem SEGS (mrestrict (w_H W) mem) a 1 v -> rdW W mem a = Some v.
Proof.
  intros W mem a v Hv H. pose proof (H 0%nat ltac:(lia)) as H0. rewrite Z.add_0_r in H0.
  unfold aview. rewrite H0. cbn [option_map]. rewrite rcn_le_byte1 by lia.
  rewrite byte_unsigned by lia. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* The loops.  What the xmalloc call left of the state is fixed here; the loops move only the bytes of the fresh
   block and the registers the C code uses as cursors. *)
Section R.
Variable sp0 : Z.
Variables (ly0 : alayout) (S0 : astate) (W0 : world SEGS) (mem0 : word -> option byte) (md0 : Model).
Variables (ly1 : alayout) (S1 : astate) (W : world SEGS) (memM : word -> option byte).
Variable regs0 : bvmap 5 word.
Variables (p text : Z) (T : list byte).

#[local] Notation NN := (Z.of_nat (length T)).

Hypothesis HTN : NN <= LMAX.
Hypothesis HPIN : In (p, NN + 1) (ablocks B ly1 S1).
Hypothesis HNIN : ~ In (p, NN + 1) (ablocks B ly0 S0).
Hypothesis HSEP : p + NN + 1 <= text \/ text + NN <= p.
Hypothesis HTXB : 4096 <= text /\ text + NN <= alloc_ceiling.
Hypothesis HTADDR : forall mem' md', AR SEGS B ly1 S1 W mem' md' ->
  range_addressable (rdW W mem') SHADOW_OFF text NN.
Hypothesis HSTK0 : astk_ok REC_CANONICAL_STK ly0 sp0.
Hypothesis HTXTM : abytes_atR (rdW W memM) text T.
Hypothesis HSV2 : rdword (rdW W memM) (sp0 - 32) = Some (bv_unsigned (getr regs0 18)).
Hypothesis HSV1 : rdword (rdW W memM) (sp0 - 24) = Some (bv_unsigned (getr regs0 9)).
Hypothesis HSV0 : rdword (rdW W memM) (sp0 - 16) = Some (bv_unsigned (getr regs0 8)).
Hypothesis HSVR : rdword (rdW W memM) (sp0 - 8) = Some (raZ regs0).
Hypothesis HRAOK : YK0s.ret_ok (getr regs0 1).
Hypothesis HPERM : Permutation (ablocks B ly1 S1) ((p, LIVE_REC_CANONICAL T) :: ablocks B ly0 S0).
Hypothesis HBB : blocks_bytes S1 <= blocks_bytes S0 + LIVE_REC_CANONICAL T.
Hypothesis HAPART : Forall (fun qk => iv_apart p (LIVE_REC_CANONICAL T) (fst qk) (snd qk)) (ablocks B ly0 S0).
Hypothesis HMLE : mo_le MT S0 S1 (XM_REC_CANONICAL MT T).
Hypothesis HSP0 : spZ regs0 = sp0.

(* the post of the whole walk: the statement's own, with the block xmalloc returned *)
Definition RPOST : world SEGS -> config -> Prop :=
  apost_base SEGS B REC_CANONICAL_STK [] regs0 ly0 S0 W0 mem0 md0 EV_REC_CANONICAL
    (fun ly' S' W' regs' mem' md' => exists q : Z,
       getr regs' 10 = w64 q /\ 4096 <= q < 2 ^ 64 /\
       Permutation (ablocks B ly' S') ((q, LIVE_REC_CANONICAL T) :: ablocks B ly0 S0) /\
       Forall (fun qk => iv_apart q (LIVE_REC_CANONICAL T) (fst qk) (snd qk)) (ablocks B ly0 S0) /\
       abytes_atR (rdW W' mem') q (canon T ++ [Z_to_bv 8 0]) /\ abytes_atR (rdW W' mem') text T /\
       blocks_bytes S' <= blocks_bytes S0 + LIVE_REC_CANONICAL T /\
       mo_le MT S0 S' (XM_REC_CANONICAL MT T)).

(* what holds at every cut point: the journal of the one xmalloc call, the bytes written into the fresh block so
   far, and that nothing outside the fresh block has moved since xmalloc returned *)
Definition RINV (mem : word -> option byte) (md : Model) (out : list byte) : Prop :=
  ajournal SEGS B REC_CANONICAL_STK sp0 [] ly0 S0 W0 mem0 md0 [] ly1 S1 W mem md EV_REC_CANONICAL /\
  (forall a, 0 <= a < 2 ^ 64 -> ~ (p <= a < p + NN + 1) -> rdW W mem a = rdW W memM a) /\
  abytes_atR (rdW W mem) p out /\ Z.of_nat (length out) <= NN + 1.

Lemma rcn_ar : forall mem md out, RINV mem md out -> AR SEGS B ly1 S1 W mem md.
Proof. intros mem md out (HJ & _). exact (proj1 HJ). Qed.

Lemma rcn_rq : req_size (NN + 1) = NN + 1.
Proof. unfold req_size. destruct (Z.eqb_spec (NN + 1) 0); [lia | reflexivity]. Qed.

Lemma rcn_blk : forall mem md out, RINV mem md out ->
  p mod 16 = 0 /\ 4096 <= p /\ p + NN + 1 <= alloc_ceiling /\ p + NN + 1 <= sp0 - 32.
Proof.
  intros mem md out HI.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ p (NN + 1) (rcn_ar mem md out HI) HPIN) as (H16 & H4096 & Hceil & _).
  rewrite rcn_rq in Hceil.
  pose proof HSTK0 as (Hsp16 & Hstk0 & Hcl & Hslo & Hshi & H47 & _).
  assert (HS : REC_CANONICAL_STK = 16432) by reflexivity.
  repeat split; lia.
Qed.

(* a byte of the fresh block is one the walk may write: a block that was not live at the entry *)
Lemma rcn_awr_new : forall (i : Z) lyq ownq, 0 <= i < NN + 1 ->
  awr_byte SEGS B REC_CANONICAL_STK sp0 [] (ablocks B ly0 S0) (ablocks B ly1 S1) (frames S0) lyq ownq (p + i).
Proof.
  intros i lyq ownq Hi. right. right. left. exists p, (NN + 1).
  split; [exact HPIN|]. split; [exact HNIN|]. rewrite rcn_rq. lia.
Qed.

Lemma rcn_paddr : forall mem md out, RINV mem md out ->
  range_addressable (rdW W mem) SHADOW_OFF p (NN + 1).
Proof.
  intros mem md out HI.
  apply (range_addressable_of_block SEGS B LAWS ly1 S1 W mem md p (NN + 1) p (NN + 1) (rcn_ar _ _ _ HI) HPIN);
    rewrite ?rcn_rq; lia.
Qed.

Lemma rcn_txt : forall mem md out, RINV mem md out -> abytes_atR (rdW W mem) text T.
Proof.
  intros mem md out HI. pose proof HI as (_ & HK & _).
  pose proof HTXB as (Ht1 & Ht2). pose proof (rcn_blk _ _ _ HI) as (_ & Hp1 & Hp2 & _).
  pose proof alloc_ceiling_val as HAC.
  apply (rcn_bytes_ext (rdW W memM)); [|exact HTXTM].
  intros i Hi. apply HK; [lia | destruct HSEP; lia].
Qed.

Lemma rcn_stk : forall mem md out a v, RINV mem md out ->
  sp0 - 32 <= a <= sp0 - 8 -> rdword (rdW W memM) a = Some v -> rdword (rdW W mem) a = Some v.
Proof.
  intros mem md out a v HI Ha Hv. pose proof HI as (_ & HK & _).
  pose proof (rcn_blk _ _ _ HI) as (_ & Hp1 & Hp2 & Hp3).
  pose proof HSTK0 as (Hsp16 & Hstk0 & Hcl & Hslo & Hshi & H47 & _).
  pose proof alloc_ceiling_val as HAC.
  rewrite (rdword_ext (rdW W memM) (rdW W mem)); [exact Hv|].
  intros i Hi. apply HK; lia.
Qed.

(* the registers the tail runs on (0x89954): a3 = o, a2 = ~out *)
Definition rcn_fregs (regs : bvmap 5 word) (loo : Z) : Prop :=
  (forall r, In r rcn_kept -> getr regs r = getr regs0 r) /\ spZ regs = sp0 - 32 /\
  getr regs 10 = w64 p /\ getr regs 13 = w64 loo /\ getr regs 18 = w64 SHADOW_OFF /\
  getr regs 12 = w64 (NOTW p).

(* the registers the store of the terminator runs on (0x8995c): a1 = out + o *)
Definition rcn_f0regs (regs : bvmap 5 word) (loo : Z) : Prop :=
  (forall r, In r rcn_kept -> getr regs r = getr regs0 r) /\ spZ regs = sp0 - 32 /\
  getr regs 10 = w64 p /\ getr regs 11 = w64 (p + loo) /\ getr regs 18 = w64 SHADOW_OFF.

(* the registers the three loop heads run on: a4 = i, a5 = ~text, a6 = (text != 0), a7 = ' ', t0 = '\t' *)
Definition rcn_regs (regs : bvmap 5 word) (j : nat) (loo : Z) : Prop :=
  rcn_fregs regs loo /\
  getr regs 8 = w64 NN /\ getr regs 9 = w64 text /\ getr regs 14 = w64 (Z.of_nat j) /\
  getr regs 15 = w64 (NOTW text) /\ getr regs 17 = w64 32 /\ getr regs 5 = w64 9 /\ getr regs 16 = w64 1.

(* the copy loop's: t1 = len + o - i, the o the copy ends at *)
Definition rcn_cregs (regs : bvmap 5 word) (j : nat) (loo : Z) : Prop :=
  rcn_regs regs j loo /\ getr regs 6 = w64 (NN + loo - Z.of_nat j).

(* The store of the terminator (0x8995c): the terminator is written, the frame is popped and the block is handed
   back. The empty line enters here straight from the xmalloc return. *)
Lemma rcn_fin0 : forall regs mem md,
  RINV mem md (canon T) -> rcn_f0regs regs (Z.of_nat (length (canon T))) ->
  SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + K_FIN0)) mem (seg_rom SEGS)) md) RPOST.
Proof.
intros regs mem md HI (HK & Hsp & R10 & R11 & R18).
pose proof HI as (HJ & HKEEP & HOUT & HLEN).
pose proof (rcn_blk _ _ _ HI) as (Hp16 & Hp4096 & Hpceil & Hpstk).
pose proof HSTK0 as (Hsp16 & Hstk0 & Hcl & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof alloc_ceiling_val as HAC.
assert (HAR : AR SEGS B ly1 S1 W mem md) by exact (rcn_ar _ _ _ HI).
set (lo := Z.of_nat (length (canon T))) in *.
pose proof (canon_length T) as HCL.
assert (Hlo : 0 <= lo <= NN) by (unfold lo; lia).
pose proof (rcn_stk mem md _ (sp0 - 32) _ HI ltac:(lia) HSV2) as Q2.
pose proof (rcn_stk mem md _ (sp0 - 24) _ HI ltac:(lia) HSV1) as Q1.
pose proof (rcn_stk mem md _ (sp0 - 16) _ HI ltac:(lia) HSV0) as Q0.
pose proof (rcn_stk mem md _ (sp0 - 8) _ HI ltac:(lia) HSVR) as QR.
pose proof (u64_range (getr regs0 18)) as B18. pose proof (u64_range (getr regs0 9)) as B9.
pose proof (u64_range (getr regs0 8)) as B8. pose proof (u64_range (getr regs0 1)) as B1.
destruct (al_blocks _ _ LAWS _ _ _ _ _ p (NN + 1) HAR HPIN) as (_ & _ & _ & _ & Hpres & _).
rewrite rcn_rq in Hpres.
set (E := Eimg (Ereg regs [w64 (bv_unsigned (getr regs0 18)); w64 (bv_unsigned (getr regs0 9));
                           w64 (bv_unsigned (getr regs0 8)); w64 (raZ regs0)])).
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr regs r)
  by (intros k r Hk; subst E; apply ew_Eimg_Ereg_nat; exact Hk).
assert (E32 : ew E 32 = w64 (bv_unsigned (getr regs0 18)))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = w64 (bv_unsigned (getr regs0 9)))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = w64 (bv_unsigned (getr regs0 8)))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = w64 (raZ regs0))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (Usp : bv_unsigned (ew E 2) = sp0 - 32) by (rewrite (EE 2%nat 2%bv eq_refl); exact Hsp).
assert (U11 : bv_unsigned (ew E 11) = p + lo)
  by (rewrite (EE 11%nat 11%bv eq_refl), R11; apply unsigned_lit_small; lia).
assert (HS : st_ok_pi SEGS VAL E rcn_ss_fin0
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + K_FIN0)) mem (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold rcn_ss_fin0. apply pa_entry_st_ok_full.
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    + rewrite U11. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply (proj1 (Hpres (p + lo + o) ltac:(lia))).
    + rewrite Usp. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      * apply (chunk_ok_val SEGS E _ (sp0 - 32) 0 8 (SOff 32 0) (bv_unsigned (getr regs0 18)));
        [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | lia |].
        rewrite Z.add_0_r. apply (val_mem_of_rdword SEGS (w_H W) mem). exact Q2.
      * apply (chunk_ok_val SEGS E _ (sp0 - 32) 8 8 (SOff 33 0) (bv_unsigned (getr regs0 9)));
        [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | lia |].
        replace (sp0 - 32 + 8) with (sp0 - 24) by lia. apply (val_mem_of_rdword SEGS (w_H W) mem). exact Q1.
      * apply (chunk_ok_val SEGS E _ (sp0 - 32) 16 8 (SOff 34 0) (bv_unsigned (getr regs0 8)));
        [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | lia |].
        replace (sp0 - 32 + 16) with (sp0 - 16) by lia. apply (val_mem_of_rdword SEGS (w_H W) mem). exact Q0.
      * apply (chunk_ok_val SEGS E _ (sp0 - 32) 24 8 (SOff 35 0) (raZ regs0));
        [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; unfold raZ; lia | lia |].
        replace (sp0 - 32 + 24) with (sp0 - 8) by lia. apply (val_mem_of_rdword SEGS (w_H W) mem). exact QR.
  - cbn [pairwise_disjoint all_disjoint]. repeat split; try exact I.
    unfold extent_disjoint. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U11, Usp. lia.
  - split; [|split; exact I].
    cbn [f_atoms atoms_ok]. unfold afact_ok, PTR; cbn [af_lo af_hi af_al2].
    rewrite Usp, U11, (EE 10%nat 10%bv eq_refl), (EE 18%nat 18%bv eq_refl).
    rewrite R10, R18. rewrite !unsigned_lit_small by (unfold SHADOW_OFF; lia).
    change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
    assert (Hm16 : (sp0 - 32) mod 16 = 0) by (rewrite Zminus_mod, Hsp16; reflexivity).
    assert (HL8 : NN <= 8192) by (unfold LMAX in HTN; lia).
    repeat split; try (unfold SB, SHADOW_OFF in * ); try lia. }
assert (SHOK : sh_ok SEGS (SOff 18 0) rcn_sh_fin0 E (mrestrict (w_H W) mem)).
{ unfold rcn_sh_fin0, sh_ok. apply Forall_cons; [|apply Forall_nil].
  apply (shent_app_of_block SEGS B LAWS ly1 S1 W mem md E (SOff 18 0) 11 (p + lo) p (NN + 1) 0 1 _ HAR HPIN).
  - apply U_atom; [rewrite (EE 18%nat 18%bv eq_refl), R18; reflexivity | unfold SHADOW_OFF; lia].
  - apply U_atom; [rewrite (EE 11%nat 11%bv eq_refl); exact R11 | lia].
  - lia.
  - lia.
  - rewrite rcn_rq. lia. }
paj_run_tok RUN HS HJ SHOK Bspan.
{ srr_obls. rewrite (U_atom E 18 SHADOW_OFF ltac:(rewrite (EE 18%nat 18%bv eq_refl), R18; reflexivity)
    ltac:(unfold SHADOW_OFF; lia)).
  rewrite (U_atom E 11 (p + lo) ltac:(rewrite (EE 11%nat 11%bv eq_refl); exact R11) ltac:(lia)).
  apply (range_addressable_sub (rdW W mem) SHADOW_OFF p (NN + 1)); [apply (rcn_paddr mem md (canon T) HI) | lia | lia]. }
{ eapply (awr_ok_cons_gen B E _ _ _ _ _ _ _ _ _ _ 11 (p + lo));
  [reflexivity | exact U11 | | eapply (awr_ok_cons_gen B E _ _ _ _ _ _ _ _ _ _ 2 (sp0 - 32));
     [reflexivity | exact Usp | | apply awr_ok_nil]].
  - cbn [YP09.r_wlo YP09.r_whi]. intros a Ha.
    replace a with (p + (a - p)) by lia. apply rcn_awr_new. lia.
  - cbn [YP09.r_wlo YP09.r_whi]. intros a Ha. left. unfold REC_CANONICAL_STK. lia. }
prreg HS (1%bv : bv 5) F1. prreg HS (2%bv : bv 5) F2. prreg HS (8%bv : bv 5) F8.
prreg HS (9%bv : bv 5) F9. prreg HS (10%bv : bv 5) F10. prreg HS (18%bv : bv 5) F18.
prreg HS (3%bv : bv 5) K3. prreg HS (4%bv : bv 5) K4. prreg HS (19%bv : bv 5) K19.
prreg HS (20%bv : bv 5) K20. prreg HS (21%bv : bv 5) K21. prreg HS (22%bv : bv 5) K22.
prreg HS (23%bv : bv 5) K23. prreg HS (24%bv : bv 5) K24. prreg HS (25%bv : bv 5) K25.
prreg HS (26%bv : bv 5) K26. prreg HS (27%bv : bv 5) K27.
lazymatch type of HS with
| st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msx) =>
  let r := eval vm_compute in (nth 0 (ss_mem ssx) got_regionP) in
  pose proof (st_ok_pi_region_nth Ex ssx (restrict (w_H W) msx) 0 r HS ltac:(vm_compute; reflexivity)) as HRo;
  assert (U11x : bv_unsigned (ew Ex 11) = p + lo) by (rewrite !ew_ewset_other by lia; exact U11);
  pose proof (field_of_region_any Ex (mrestrict (w_H W) (ms_mem msx)) 11 (p + lo) _ _ _ _ _ 0 1%N (SLit 0)
                HRo U11x ltac:(cbn; tauto) ltac:(cbn; lia)) as HV
end.
cbn [ms_mem restrict mkst] in HRo, HV. rewrite rcn_zero_chunk in HV.
assert (HZ : rdW W (ms_mem ms) (p + lo) = Some 0).
{ apply rcn_rd_of_val_mem1; [lia|]. rewrite <- (Z.add_0_r (p + lo)). exact HV. }
pose proof (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun a => p + lo <= a < p + lo + 1) HFr
  ltac:(intros bq wlo whi aq Hin Hrr; vm_compute in Hin;
        repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr;
                                             rewrite ?U11, ?Usp in Hrr; lia|]); destruct Hin)) as KEEPF.
assert (HI2 : RINV (ms_mem ms) (with_vm_backing (m_vm_lazy md) mat md) (canon T ++ [Z_to_bv 8 0])).
{ split; [exact HJ|]. split.
  - intros a Ha Hn. rewrite (KEEPF a Ha); [exact (HKEEP a Ha Hn)|].
    cbv beta. intros [HA HB]. apply Hn. lia.
  - split.
    + apply rcn_bytes_snoc.
      * apply (rcn_bytes_ext (rdW W mem)); [|exact HOUT]. intros i Hi. apply KEEPF; [lia|].
        cbv beta. intros [HA HB]. lia.
      * fold lo. rewrite HZ. reflexivity.
    + rewrite length_app. cbn [length]. lia. }
eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. unfold RPOST, apost_base.
lazymatch goal with |- exists _ _ _ _ _, mkCfg (mkst ?r _ ?m _) ?d = _ /\ _ => exists ly1, S1, r, m, d end.
split.
{ rewrite F1, E35. unfold w64, raZ. rewrite Z_to_bv_bv_unsigned.
  unfold YK0s.ret_ok in HRAOK. rewrite HRAOK. reflexivity. }
split.
{ rewrite HSP0. eapply (ajournal_mono_k SEGS B);
  [apply (ajournal_materialize SEGS B LAWS pa_segs_low); exact HJ | unfold EV_REC_CANONICAL; lia]. }
split.
{ unfold aregs_preserved. intros r Hr.
  assert (Hc : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
    r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by (unfold acallee_saved in Hr; lia).
  repeat (destruct Hc as [-> | Hc]); [ .. | subst r ].
  - replace (Z_to_bv 5 2) with (2%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity). rewrite F2, Usp. unfold spZ in HSP0.
    replace (sp0 - 32 + 32) with sp0 by lia. rewrite <- HSP0, Z_to_bv_bv_unsigned. reflexivity.
  - replace (Z_to_bv 5 3) with (3%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity). rewrite K3, (EE 3%nat 3%bv eq_refl). apply HK; cbv; tauto.
  - replace (Z_to_bv 5 4) with (4%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity). rewrite K4, (EE 4%nat 4%bv eq_refl). apply HK; cbv; tauto.
  - replace (Z_to_bv 5 8) with (8%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity). rewrite F8, E34. unfold w64. rewrite Z_to_bv_bv_unsigned. reflexivity.
  - replace (Z_to_bv 5 9) with (9%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity). rewrite F9, E33. unfold w64. rewrite Z_to_bv_bv_unsigned. reflexivity.
  - replace (Z_to_bv 5 18) with (18%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity). rewrite F18, E32. unfold w64. rewrite Z_to_bv_bv_unsigned. reflexivity.
  - replace (Z_to_bv 5 19) with (19%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity). rewrite K19, (EE 19%nat 19%bv eq_refl). apply HK; cbv; tauto.
  - replace (Z_to_bv 5 20) with (20%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity). rewrite K20, (EE 20%nat 20%bv eq_refl). apply HK; cbv; tauto.
  - replace (Z_to_bv 5 21) with (21%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity). rewrite K21, (EE 21%nat 21%bv eq_refl). apply HK; cbv; tauto.
  - replace (Z_to_bv 5 22) with (22%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity). rewrite K22, (EE 22%nat 22%bv eq_refl). apply HK; cbv; tauto.
  - replace (Z_to_bv 5 23) with (23%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity). rewrite K23, (EE 23%nat 23%bv eq_refl). apply HK; cbv; tauto.
  - replace (Z_to_bv 5 24) with (24%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity). rewrite K24, (EE 24%nat 24%bv eq_refl). apply HK; cbv; tauto.
  - replace (Z_to_bv 5 25) with (25%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity). rewrite K25, (EE 25%nat 25%bv eq_refl). apply HK; cbv; tauto.
  - replace (Z_to_bv 5 26) with (26%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity). rewrite K26, (EE 26%nat 26%bv eq_refl). apply HK; cbv; tauto.
  - replace (Z_to_bv 5 27) with (27%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity). rewrite K27, (EE 27%nat 27%bv eq_refl). apply HK; cbv; tauto. }
exists p.
split.
{ rewrite F10, (EE 10%nat 10%bv eq_refl), R10. reflexivity. }
split; [lia|].
split; [exact HPERM|].
split; [exact HAPART|].
split; [exact (proj1 (proj2 (proj2 HI2)))|].
split; [exact (rcn_txt _ _ _ HI2)|].
split; [exact HBB|].
exact HMLE.
Qed.

(* After a symbolic run the model is `with_vm_backing (m_vm_lazy md) mat md`; naming it (and forgetting the body)
   keeps the next run from nesting two copies of it. *)
Local Ltac clear_md := repeat match goal with |- context [with_vm_backing (m_vm_lazy ?m) ?x ?m] =>
  let mdv := fresh "mdv" in set (mdv := with_vm_backing (m_vm_lazy m) x m) in *; clearbody mdv end.

Local Ltac rcn_keepf nm :=
  lazymatch goal with
  | HFrx : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ =>
    pose proof (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun _ : Z => False) HFrx
      ltac:(intros bq wlo whi aq Hin Hrr; vm_compute in Hin;
            repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; lia|]);
            destruct Hin)) as nm;
    clear HFrx
  end;
  lazymatch goal with
  | HFx : frame_of _ _ ?m1 ?m2 |- _ => clear HFx
  | _ => idtac
  end;
  lazymatch goal with
  | HGx : mem_grows _ _ |- _ => clear HGx
  | _ => idtac
  end;
  clear_md.

Lemma rcn_keep_step : forall (out : list byte) mem1 md1 mem2 md2,
  RINV mem1 md1 out ->
  ajournal SEGS B REC_CANONICAL_STK sp0 [] ly0 S0 W0 mem0 md0 [] ly1 S1 W mem2 md2 EV_REC_CANONICAL ->
  (forall a, 0 <= a < 2 ^ 64 -> rdW W mem2 a = rdW W mem1 a) ->
  RINV mem2 md2 out.
Proof.
  intros out mem1 md1 mem2 md2 HI1 HJ2 HEQ.
  pose proof (rcn_blk _ _ _ HI1) as (_ & Hp1 & Hp2 & _).
  pose proof alloc_ceiling_val as HAC.
  pose proof HI1 as (HJ1 & HK1 & HO1 & HL1).
  split; [exact HJ2|]. split.
  - intros a Ha Hn. rewrite (HEQ a Ha). exact (HK1 a Ha Hn).
  - split; [|exact HL1]. apply (rcn_bytes_ext (rdW W mem1)); [|exact HO1].
    intros k Hk. apply HEQ. lia.
Qed.

(* a register of the current state, as the symbolic value the state gives it *)
Local Ltac rcn_rreg HS :=
  lazymatch goal with |- getr (ms_regs ?ms) ?r = _ =>
  lazymatch type of HS with
  | st_ok_pi _ _ ?E ?ss (restrict ?Hh ms) =>
    rewrite (st_ok_pi_restrict_reg Hh E ss ms r HS);
    let v := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with v
  end end.

Lemma rcn_den_off : forall (E : env) n v k, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  sv_denot E (SOff n k) = Z_to_bv 64 (v + k).
Proof. intros E n v k H Hv. cbn [sv_denot]. rewrite H, unsigned_lit_small by lia. reflexivity. Qed.

(* the denotation of the sum a1 = a0 + a3 the tail builds *)
Lemma rcn_den_add : forall (E : env) m n a b, ew E m = Z_to_bv 64 a -> ew E n = Z_to_bv 64 b ->
  0 <= a < 2 ^ 63 -> 0 <= b < 2 ^ 63 ->
  sv_denot E (SAlu ALU_ADD (SOff m 0) (SOff n 0)) = Z_to_bv 64 (a + b).
Proof.
  intros E m n a b Hm Hn Ha Hb. cbn [sv_denot]. rewrite Hm, Hn, !unsigned_lit_small by lia.
  rewrite !Z.add_0_r. apply rcn_alu_add.
Qed.

(* the goal `sv_denot Ex v = _` for v an atom plus a constant, or a sum of two atoms; Hv gives the atom in the seed
   env *)
Local Ltac rcn_off n v c Hv :=
  lazymatch goal with |- sv_denot ?Ex _ = _ =>
    rewrite (rcn_den_off Ex n v c ltac:(rewrite ?ew_ewset_other by lia; exact Hv) ltac:(lia)) end.
Local Ltac rcn_add m n a b Hm Hn :=
  lazymatch goal with |- sv_denot ?Ex _ = _ =>
    rewrite (rcn_den_add Ex m n a b ltac:(rewrite ?ew_ewset_other by lia; exact Hm)
      ltac:(rewrite ?ew_ewset_other by lia; exact Hn) ltac:(lia) ltac:(lia)) end.
Local Ltac rcn_not m v Hv :=
  lazymatch goal with |- sv_denot ?Ex (SAlu ALU_XOR (SOff _ 0) (SLit ?x)) = _ =>
    rewrite (rcn_den_not Ex m v x ltac:(rewrite ?ew_ewset_other by lia; exact Hv) ltac:(lia)
      ltac:(apply bv_eq; vm_compute; reflexivity)) end.

(* The tail (0x89954): the UBSan check of out + o (decided by the facts on ~out and o), then a1 = out + o. *)
Lemma rcn_fin : forall regs mem md,
  RINV mem md (canon T) -> rcn_fregs regs (Z.of_nat (length (canon T))) ->
  SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + K_FIN)) mem (seg_rom SEGS)) md) RPOST.
Proof.
intros regs mem md HI (HK & Hsp & R10 & R13 & R18 & R12).
pose proof HI as (HJ & HKEEP & HOUT & HLEN).
pose proof (rcn_blk _ _ _ HI) as (Hp16 & Hp4096 & Hpceil & Hpstk).
pose proof HSTK0 as (Hsp16 & Hstk0 & Hcl & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof alloc_ceiling_val as HAC.
assert (HL8 : NN <= 8192) by (unfold LMAX in HTN; lia).
set (lo := Z.of_nat (length (canon T))) in *.
pose proof (canon_length T) as HCL.
assert (Hlo : 0 <= lo <= NN) by (unfold lo; lia).
set (E := Eimg (Ereg regs [])).
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr regs r)
  by (intros k r Hk; subst E; apply ew_Eimg_Ereg_nat; exact Hk).
assert (Usp : bv_unsigned (ew E 2) = sp0 - 32) by (rewrite (EE 2%nat 2%bv eq_refl); exact Hsp).
assert (HAE : env_agree 32 (Ereg regs []) E)
  by (subst E; split; [intros k Hk; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (HS : st_ok_pi SEGS VAL E rcn_ss_fin
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + K_FIN)) mem (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold rcn_ss_fin. apply pa_entry_st_ok_full.
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - cbn [pairwise_disjoint all_disjoint]. tauto.
  - split; [|split; exact I].
    cbn [f_atoms atoms_ok]. unfold afact_ok, PTR, NOTF; cbn [af_lo af_hi af_al2].
    rewrite Usp, (EE 10%nat 10%bv eq_refl), (EE 12%nat 12%bv eq_refl), (EE 13%nat 13%bv eq_refl),
      (EE 18%nat 18%bv eq_refl).
    rewrite R10, R12, R13, R18. unfold w64, NOTW. rewrite !unsigned_lit_small by (unfold SHADOW_OFF; lia).
    change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
    assert (Hm16 : (sp0 - 32) mod 16 = 0) by (rewrite Zminus_mod, Hsp16; reflexivity).
    repeat split; try (unfold SB, SHADOW_OFF in * ); try lia. }
assert (SHOK : sh_ok SEGS (SOff 18 0) (@nil shent) E (mrestrict (w_H W) mem)) by apply Forall_nil.
paj_run_to_tok RUNTO HS HJ SHOK Bspan K_FIN0.
{ awr_ok_tac. }
rcn_keepf KF1.
pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ rcn_fkeptall HS ltac:(env_agree_chain HAE)
             ltac:(vm_compute; reflexivity)) as HKEPT.
cbn [ms_regs restrict mkst] in HKEPT.
pmkst HS.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rr _ ?mm _) ?dd) _ =>
  assert (HI2 : RINV mm dd (canon T));
  [ apply (rcn_keep_step _ mem md _ _ HI HJ); intros a Ha;
    rewrite (KF1 a Ha ltac:(cbv beta; tauto)); reflexivity
  | apply (rcn_fin0 rr mm dd HI2) ] end.
unfold rcn_f0regs. repeat match goal with |- _ /\ _ => split end.
- intros r Hr. rewrite (HKEPT r ltac:(revert Hr; cbv [rcn_kept rcn_fkeptall In]; tauto)). apply HK. exact Hr.
- unfold spZ. rewrite (HKEPT 2%bv ltac:(cbv; tauto)). exact Hsp.
- rewrite (HKEPT 10%bv ltac:(cbv; tauto)). exact R10.
- rcn_rreg HS. rcn_add 10%nat 13%nat p lo (eq_trans (EE 10%nat 10%bv eq_refl) R10)
    (eq_trans (EE 13%nat 13%bv eq_refl) R13). reflexivity.
- rewrite (HKEPT 18%bv ltac:(cbv; tauto)). exact R18.
Qed.

Local Ltac rcn_byte_branch lem v bb E33x Hc :=
  lazymatch type of Hc with context [sv_denot ?Ex _] =>
    let G := fresh "G33" in
    assert (G : ew Ex 33 = w64 (bv_unsigned bb)) by (rewrite ?ew_ewset_other by lia; exact E33x);
    rewrite lem, (U_atom Ex 33 (bv_unsigned bb) G ltac:(lia)) in Hc;
    change (U Ex (SLit v)) with v in Hc; clear G
  end.

(* the `bltu a4,s0` of the word-scan loop (0x89884), after `addi a4,a4,1` *)
Local Ltac rcn_ltu_branch ii nn EEx R14x R8x Hc :=
  lazymatch type of Hc with context [sv_denot ?Ex _] =>
    let G1 := fresh "G14" in let G2 := fresh "G8" in
    assert (G1 : ew Ex 14 = w64 (Z.of_nat ii))
      by (rewrite ?ew_ewset_other by lia; rewrite (EEx 14%nat 14%bv eq_refl); exact R14x);
    assert (G2 : ew Ex 8 = w64 nn)
      by (rewrite ?ew_ewset_other by lia; rewrite (EEx 8%nat 8%bv eq_refl); exact R8x);
    rewrite branch_ltu_U, (U_atom_off Ex 14 (Z.of_nat ii) 1 G1 ltac:(lia) ltac:(lia)),
      (U_atom Ex 8 nn G2 ltac:(lia)) in Hc;
    clear G1 G2
  end.

(* the `bltu a4,s0` after a separator in the copy loop (0x89938) *)
Local Ltac rcn_sep_branch jj nn EEx R14x R8x Hc :=
  lazymatch type of Hc with context [sv_denot ?Ex _] =>
    let G1 := fresh "G14" in let G2 := fresh "G8" in
    assert (G1 : ew Ex 14 = w64 (Z.of_nat jj))
      by (rewrite ?ew_ewset_other by lia; rewrite (EEx 14%nat 14%bv eq_refl); exact R14x);
    assert (G2 : ew Ex 8 = w64 nn)
      by (rewrite ?ew_ewset_other by lia; rewrite (EEx 8%nat 8%bv eq_refl); exact R8x);
    rewrite branch_ltu_U, (U_atom Ex 14 (Z.of_nat jj) G1 ltac:(lia)), (U_atom Ex 8 nn G2 ltac:(lia)) in Hc;
    clear G1 G2
  end.

Lemma rcn_keep_hole : forall (out : list byte) mem1 md1 mem2 md2 k,
  RINV mem1 md1 out ->
  ajournal SEGS B REC_CANONICAL_STK sp0 [] ly0 S0 W0 mem0 md0 [] ly1 S1 W mem2 md2 EV_REC_CANONICAL ->
  Z.of_nat (length out) <= k <= NN ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (p + k <= a < p + k + 1) -> rdW W mem2 a = rdW W mem1 a) ->
  RINV mem2 md2 out.
Proof.
  intros out mem1 md1 mem2 md2 k HI1 HJ2 Hk HEQ.
  pose proof (rcn_blk _ _ _ HI1) as (_ & Hp1 & Hp2 & _). pose proof alloc_ceiling_val as HAC.
  pose proof HI1 as (HJ1 & HK1 & HO1 & HL1).
  split; [exact HJ2|]. split.
  - intros a Ha Hn. rewrite (HEQ a Ha ltac:(lia)). exact (HK1 a Ha Hn).
  - split; [|exact HL1]. apply (rcn_bytes_ext (rdW W mem1)); [|exact HO1].
    intros n Hn. apply HEQ; lia.
Qed.

Lemma rcn_store_step : forall (out : list byte) (c : byte) mem1 md1 mem2 md2,
  RINV mem1 md1 out ->
  ajournal SEGS B REC_CANONICAL_STK sp0 [] ly0 S0 W0 mem0 md0 [] ly1 S1 W mem2 md2 EV_REC_CANONICAL ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (p + Z.of_nat (length out) <= a < p + Z.of_nat (length out) + 1) ->
     rdW W mem2 a = rdW W mem1 a) ->
  rdW W mem2 (p + Z.of_nat (length out)) = Some (bv_unsigned c) ->
  Z.of_nat (length out) < NN + 1 ->
  RINV mem2 md2 (out ++ [c]).
Proof.
  intros out c mem1 md1 mem2 md2 HI1 HJ2 HKP HC HLT.
  pose proof (rcn_blk _ _ _ HI1) as (_ & Hp1 & Hp2 & _). pose proof alloc_ceiling_val as HAC.
  pose proof HI1 as (HJ1 & HK1 & HO1 & HL1).
  split; [exact HJ2|]. split.
  - intros a Ha Hn. rewrite (HKP a Ha ltac:(lia)). exact (HK1 a Ha Hn).
  - split.
    + apply rcn_bytes_snoc.
      * apply (rcn_bytes_ext (rdW W mem1)); [|exact HO1]. intros k Hk. apply HKP; lia.
      * exact HC.
    + rewrite length_app. cbn [length]. lia.
Qed.

Local Ltac rcn_copy_keep nm U32x U34x oo2 :=
  lazymatch goal with
  | HFrx : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ =>
    pose proof (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun a => p + oo2 <= a < p + oo2 + 1) HFrx
      ltac:(intros bq wlo whi aq Hin Hrr; vm_compute in Hin;
            repeat (destruct Hin as [Hq | Hin];
                    [injection Hq as <- <- <-; cbn [base_val] in Hrr;
                     rewrite ?ew_ewset_other in Hrr by lia; rewrite ?U32x, ?U34x in Hrr; lia|]);
            destruct Hin)) as nm;
    clear HFrx
  end;
  lazymatch goal with HFx : frame_of _ _ ?m1 ?m2 |- _ => clear HFx | _ => idtac end;
  lazymatch goal with HGx : mem_grows _ _ |- _ => clear HGx | _ => idtac end;
  clear_md.

Local Ltac rcn_copy_awr jj oo2 U32x U34x :=
  eapply (awr_ok_cons_gen B _ _ _ _ _ _ _ _ _ _ _ 32 (text + Z.of_nat jj));
  [ reflexivity
  | rewrite ?ew_ewset_other by lia; exact U32x
  | cbn [YP09.r_wlo YP09.r_whi]; intros aq Haq; exfalso; lia
  | eapply (awr_ok_cons_gen B _ _ _ _ _ _ _ _ _ _ _ 34 (p + oo2));
    [ reflexivity
    | rewrite ?ew_ewset_other by lia; exact U34x
    | cbn [YP09.r_wlo YP09.r_whi]; intros aq Haq;
      replace aq with (p + (aq - p)) by lia; apply rcn_awr_new; lia
    | apply awr_ok_nil ] ].


(* the byte the store of the copy loop left at p + oo2: region 1 of the state (the fresh block at atom 34) holds the
   byte of atom 33 *)
Local Ltac rcn_stored HZ bb oo2 U34x E33x :=
  lazymatch goal with
  | HSx : st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msx) |- _ =>
    let r := eval vm_compute in (nth 1 (ss_mem ssx) got_regionP) in
    let HRo := fresh "HRo" in let U34y := fresh "U34y" in let HVB := fresh "HVB" in let HV := fresh "HV" in
    pose proof (st_ok_pi_region_nth Ex ssx (restrict (w_H W) msx) 1 r HSx ltac:(vm_compute; reflexivity)) as HRo;
    assert (U34y : bv_unsigned (ew Ex 34) = p + oo2) by (rewrite ?ew_ewset_other by lia; exact U34x);
    assert (HVB : bv_unsigned (sv_denot Ex (SOff 33 0)) mod 2 ^ (8 * Z.of_N 1) = bv_unsigned bb)
      by (change (bv_unsigned (sv_denot Ex (SOff 33 0))) with (U Ex (SOff 33 0));
          rewrite (U_atom Ex 33 (bv_unsigned bb) ltac:(rewrite ?ew_ewset_other by lia; exact E33x) ltac:(lia));
          apply Z.mod_small; cbn; lia);
    pose proof (field_of_region_any Ex (mrestrict (w_H W) (ms_mem msx)) 34 (p + oo2) _ _ _ _ _ 0 1%N (SOff 33 0)
                  HRo U34y ltac:(cbn; tauto) ltac:(cbn; lia)) as HV;
    cbn [ms_mem restrict mkst] in HRo, HV; rewrite HVB in HV;
    assert (HZ : rdW W (ms_mem msx) (p + oo2) = Some (bv_unsigned bb))
      by (apply rcn_rd_of_val_mem1; [lia | rewrite <- (Z.add_0_r (p + oo2)); exact HV]);
    clear HRo U34y HVB HV
  end.

(* The copy loop (0x898d0): the word that began at i is copied to the fresh block, byte by byte. The two UBSan
   checks of an iteration (0x898d0: ~text < i; 0x898f4: ~out < o) are decided by the executor from the seed's facts
   (~text, ~out >= 2^64 - 1 - CEIL; i, o <= LMAX). *)
Lemma rcn_copy : forall (d i j : nat) (out0 : list byte) regs mem md,
  (length T - j <= d)%nat -> (i <= j < length T)%nat ->
  Z.of_nat (length out0) + Z.of_nat (length T - i) <= NN ->
  RINV mem md (out0 ++ firstn (j - i) (skipn i T)) ->
  rcn_cregs regs j (Z.of_nat (length out0) + Z.of_nat (j - i)) ->
  (forall t b, (i <= t < j)%nat -> nth_error T t = Some b -> is_sep b = false) ->
  (forall (k : nat) regs' mem' md',
     (j <= k < length T)%nat ->
     (forall t b, (i <= t < k)%nat -> nth_error T t = Some b -> is_sep b = false) ->
     (exists b, nth_error T k = Some b /\ is_sep b = true) ->
     RINV mem' md' (out0 ++ firstn (k - i) (skipn i T)) ->
     rcn_regs regs' k (Z.of_nat (length out0) + Z.of_nat (k - i)) ->
     SRr SEGS W (mkCfg (mkst regs' (Z_to_bv 64 (BASE + K_OUTER)) mem' (seg_rom SEGS)) md') RPOST) ->
  (forall regs' mem' md',
     (forall t b, (i <= t < length T)%nat -> nth_error T t = Some b -> is_sep b = false) ->
     RINV mem' md' (out0 ++ skipn i T) ->
     rcn_fregs regs' (Z.of_nat (length out0) + Z.of_nat (length T - i)) ->
     SRr SEGS W (mkCfg (mkst regs' (Z_to_bv 64 (BASE + K_FIN)) mem' (seg_rom SEGS)) md') RPOST) ->
  SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + K_COPY)) mem (seg_rom SEGS)) md) RPOST.
Proof.
induction d as [|d IH]; intros i j out0 regs mem md Hd Hij HOB HI HR HNS KS KE; [lia|].
pose proof HI as (HJ & HKEEP & HOUT & HLEN).
pose proof HR as (((HK & Hsp & R10 & R13 & R18 & R12) & R8 & R9 & R14 & R15 & R17 & R5 & R16) & R6).
destruct (nth_error T j) as [b|] eqn:Eb; [|exfalso; apply nth_error_None in Eb; lia].
pose proof (rcn_txt _ _ _ HI) as HTX.
pose proof (rcn_bytes_nth _ _ _ _ _ HTX Eb) as HBj.
pose proof (rcn_byte_range b) as HBR.
pose proof (rcn_blk _ _ _ HI) as (Hp16 & Hp4096 & Hpceil & Hpstk).
pose proof HSTK0 as (Hsp16 & Hstk0 & Hcl & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof alloc_ceiling_val as HAC. pose proof HTXB as (Htx1 & Htx2).
assert (HL8 : NN <= 8192) by (unfold LMAX in HTN; lia).
assert (HAR : AR SEGS B ly1 S1 W mem md) by exact (rcn_ar _ _ _ HI).
set (oo := Z.of_nat (length out0) + Z.of_nat (j - i)) in *.
assert (Hoo : 0 <= oo <= NN) by (unfold oo; lia).
assert (Hlenj : Z.of_nat (length (out0 ++ firstn (j - i) (skipn i T))) = oo).
{ unfold oo. rewrite length_app, length_firstn, length_skipn. lia. }
set (E := Eimg (Ereg regs [w64 (text + Z.of_nat j); w64 (bv_unsigned b); w64 (p + oo)])).
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr regs r)
  by (intros k r Hk; subst E; apply ew_Eimg_Ereg_nat; exact Hk).
assert (E32 : ew E 32 = w64 (text + Z.of_nat j))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = w64 (bv_unsigned b))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = w64 (p + oo))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (Usp : bv_unsigned (ew E 2) = sp0 - 32) by (rewrite (EE 2%nat 2%bv eq_refl); exact Hsp).
assert (U32 : bv_unsigned (ew E 32) = text + Z.of_nat j) by (rewrite E32; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew E 34) = p + oo) by (rewrite E34; apply unsigned_lit_small; lia).
assert (HAE : env_agree 32 (Ereg regs [w64 (text + Z.of_nat j); w64 (bv_unsigned b); w64 (p + oo)]) E)
  by (subst E; split; [intros k Hk; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (HS : st_ok_pi SEGS VAL E rcn_ss_copy
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + K_COPY)) mem (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold rcn_ss_copy. apply pa_entry_st_ok_full.
  - apply regs_ok_pin;
    [ apply regs_ok_pin;
      [ apply regs_ok_pin; [apply regs_ok_Eimg_Ereg | intros X; discriminate X | cbn [sv_denot]; exact R17]
      | intros X; discriminate X | cbn [sv_denot]; exact R5]
    | intros X; discriminate X | cbn [sv_denot]; exact R16].
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    + rewrite U32. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      apply (chunk_ok_val SEGS E _ (text + Z.of_nat j) 0 1 (SOff 33 0) (bv_unsigned b));
      [cbn [sv_denot]; rewrite E33; unfold w64; rewrite unsigned_lit_small by lia;
       rewrite Z.add_0_r; reflexivity | cbn; lia | lia |].
      rewrite Z.add_0_r. apply rcn_val_mem1. exact HBj.
    + rewrite U34. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS).
      destruct (al_blocks _ _ LAWS _ _ _ _ _ p (NN + 1) HAR HPIN) as (_ & _ & _ & _ & Hpres & _).
      rewrite rcn_rq in Hpres. apply (proj1 (Hpres (p + oo + o) ltac:(lia))).
  - cbn [pairwise_disjoint all_disjoint]. repeat split; try exact I.
    unfold extent_disjoint. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U32, U34.
    destruct HSEP; [right|left]; lia.
  - split; [|split; [exact I|]].
    + cbn [f_atoms atoms_ok]. unfold afact_ok, PTR, NOTF; cbn [af_lo af_hi af_al2].
      rewrite Usp, U32, U34, E33, (EE 6%nat 6%bv eq_refl), (EE 8%nat 8%bv eq_refl),
        (EE 9%nat 9%bv eq_refl), (EE 10%nat 10%bv eq_refl), (EE 12%nat 12%bv eq_refl),
        (EE 13%nat 13%bv eq_refl), (EE 14%nat 14%bv eq_refl), (EE 15%nat 15%bv eq_refl),
        (EE 18%nat 18%bv eq_refl).
      rewrite R6, R8, R9, R10, R12, R13, R14, R15, R18. unfold w64, NOTW.
      rewrite !unsigned_lit_small by (unfold SHADOW_OFF; lia).
      change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
      assert (Hm16 : (sp0 - 32) mod 16 = 0) by (rewrite Zminus_mod, Hsp16; reflexivity).
      repeat split; try (unfold SB, SHADOW_OFF in * ); try lia.
    + cbn [f_alias alias_ok]. split; [|split; [|exact I]]; cbn [sv_denot].
      * rewrite (EE 9%nat 9%bv eq_refl), (EE 14%nat 14%bv eq_refl), R9, R14, E32. unfold w64.
        rewrite !unsigned_lit_small by lia. rewrite !Z.add_0_r. apply rcn_alu_add.
      * rewrite (EE 10%nat 10%bv eq_refl), (EE 13%nat 13%bv eq_refl), R10, R13, E34. unfold w64.
        rewrite !unsigned_lit_small by lia. rewrite !Z.add_0_r. apply rcn_alu_add. }
assert (SHOK : sh_ok SEGS (SOff 18 0) rcn_sh_copy E (mrestrict (w_H W) mem)).
{ unfold rcn_sh_copy, sh_ok. apply Forall_cons; [|apply Forall_nil].
  apply (shent_app_of_block SEGS B LAWS ly1 S1 W mem md E (SOff 18 0) 34 (p + oo) p (NN + 1) 0 1 _ HAR HPIN).
  - apply U_atom; [rewrite (EE 18%nat 18%bv eq_refl), R18; reflexivity | unfold SHADOW_OFF; lia].
  - apply U_atom; [exact E34 | lia].
  - lia.
  - lia.
  - rewrite rcn_rq. lia. }
(* 0x898d0 .. 0x898ec: the wrap check of text + j (decided), the byte's shadow check, the byte, `beq t2,t0` *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ srr_obls.
  rewrite (U_atom E 18 SHADOW_OFF ltac:(rewrite (EE 18%nat 18%bv eq_refl), R18; reflexivity)
    ltac:(unfold SHADOW_OFF; lia)).
  rewrite (U_atom E 32 (text + Z.of_nat j) E32 ltac:(lia)).
  apply (range_addressable_sub (rdW W mem) SHADOW_OFF text NN); [exact (HTADDR mem md HAR) | lia | lia]. }
{ rcn_copy_awr j oo U32 U34. }
rcn_copy_keep KF1 U32 U34 oo.
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* the byte is a tab: the word ends *)
  rcn_byte_branch branch_eq_U 9 b E33 Hc.
  assert (HSEPB : is_sep b = true)
    by (apply Z.eqb_eq in Hc; unfold is_sep; rewrite Hc; apply orb_true_r).
  clear Hc.
    paj_run_tok RUN HS HJ SHOK Bspan.
    { rcn_copy_awr j oo U32 U34. }
    rcn_copy_keep KFs U32 U34 oo.
    psrr_branch_tok RUN BR HS SHOK Bspan.
    * (* another word follows *)
      paj_run_to_tok RUNTO HS HJ SHOK Bspan K_OUTER.
      { rcn_copy_awr j oo U32 U34. }
      rcn_copy_keep KFs2 U32 U34 oo.
      pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ rcn_ckeptall HS ltac:(env_agree_chain HAE)
                   ltac:(vm_compute; reflexivity)) as HKEPT.
      cbn [ms_regs restrict mkst] in HKEPT.
      prreg HS (13%bv : bv 5) N13. prreg HS (14%bv : bv 5) N14. prreg HS (17%bv : bv 5) N17.
      prreg HS (5%bv : bv 5) N5. prreg HS (16%bv : bv 5) N16.
      pmkst HS.
      lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rr _ ?mm _) ?dd) _ =>
        assert (HIs : RINV mm dd (out0 ++ firstn (j - i) (skipn i T)));
        [ apply (rcn_keep_hole _ mem md _ _ oo HI HJ ltac:(rewrite Hlenj; lia)); intros a Ha Hn;
          rewrite (KFs2 a Ha Hn), (KFs a Ha Hn), (KF1 a Ha Hn); reflexivity
        | apply (KS j rr mm dd) ] end.
      -- lia.
      -- exact HNS.
      -- exists b. split; [exact Eb | exact HSEPB].
      -- exact HIs.
      -- unfold rcn_regs, rcn_fregs. repeat match goal with |- _ /\ _ => split end.
         ++ intros r Hr. rewrite (HKEPT r ltac:(revert Hr; cbv [rcn_kept rcn_ckeptall In]; tauto)).
            apply HK. exact Hr.
         ++ unfold spZ. rewrite (HKEPT 2%bv ltac:(cbv; tauto)). exact Hsp.
         ++ rewrite (HKEPT 10%bv ltac:(cbv; tauto)). exact R10.
         ++ rewrite N13, (EE 13%nat 13%bv eq_refl). exact R13.
         ++ rewrite (HKEPT 18%bv ltac:(cbv; tauto)). exact R18.
         ++ rewrite (HKEPT 12%bv ltac:(cbv; tauto)). exact R12.
         ++ rewrite (HKEPT 8%bv ltac:(cbv; tauto)). exact R8.
         ++ rewrite (HKEPT 9%bv ltac:(cbv; tauto)). exact R9.
         ++ rewrite N14, (EE 14%nat 14%bv eq_refl). exact R14.
         ++ rewrite (HKEPT 15%bv ltac:(cbv; tauto)). exact R15.
         ++ exact N17.
         ++ exact N5.
         ++ exact N16.
    * (* the line ended at this separator: impossible, j < |T| *)
      exfalso. rcn_sep_branch j (Z.of_nat (length T)) EE R14 R8 Hc. apply Z.ltb_ge in Hc. lia.

- (* not a tab *)
  rcn_byte_branch branch_eq_U 9 b E33 Hc.
  assert (HN9 : bv_unsigned b <> 9) by (apply Z.eqb_neq in Hc; exact Hc). clear Hc.
  paj_run_tok RUN HS HJ SHOK Bspan.
  { rcn_copy_awr j oo U32 U34. }
  rcn_copy_keep KF1b U32 U34 oo.
  psrr_branch_tok RUN BR HS SHOK Bspan.
  + (* a space: the word ends *)
    rcn_byte_branch branch_eq_U 32 b E33 Hc.
    assert (HSEPB : is_sep b = true)
      by (apply Z.eqb_eq in Hc; unfold is_sep; rewrite Hc; reflexivity).
    clear Hc.
    paj_run_tok RUN HS HJ SHOK Bspan.
    { rcn_copy_awr j oo U32 U34. }
    rcn_copy_keep KFt U32 U34 oo.
    psrr_branch_tok RUN BR HS SHOK Bspan.
    * (* another word follows *)
      paj_run_to_tok RUNTO HS HJ SHOK Bspan K_OUTER.
      { rcn_copy_awr j oo U32 U34. }
      rcn_copy_keep KFt2 U32 U34 oo.
      pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ rcn_ckeptall HS ltac:(env_agree_chain HAE)
                   ltac:(vm_compute; reflexivity)) as HKEPT.
      cbn [ms_regs restrict mkst] in HKEPT.
      prreg HS (13%bv : bv 5) N13. prreg HS (14%bv : bv 5) N14. prreg HS (17%bv : bv 5) N17.
      prreg HS (5%bv : bv 5) N5. prreg HS (16%bv : bv 5) N16.
      pmkst HS.
      lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rr _ ?mm _) ?dd) _ =>
        assert (HIs : RINV mm dd (out0 ++ firstn (j - i) (skipn i T)));
        [ apply (rcn_keep_hole _ mem md _ _ oo HI HJ ltac:(rewrite Hlenj; lia)); intros a Ha Hn;
          rewrite (KFt2 a Ha Hn), (KFt a Ha Hn), (KF1b a Ha Hn), (KF1 a Ha Hn); reflexivity
        | apply (KS j rr mm dd) ] end.
      -- lia.
      -- exact HNS.
      -- exists b. split; [exact Eb | exact HSEPB].
      -- exact HIs.
      -- unfold rcn_regs, rcn_fregs. repeat match goal with |- _ /\ _ => split end.
         ++ intros r Hr. rewrite (HKEPT r ltac:(revert Hr; cbv [rcn_kept rcn_ckeptall In]; tauto)).
            apply HK. exact Hr.
         ++ unfold spZ. rewrite (HKEPT 2%bv ltac:(cbv; tauto)). exact Hsp.
         ++ rewrite (HKEPT 10%bv ltac:(cbv; tauto)). exact R10.
         ++ rewrite N13, (EE 13%nat 13%bv eq_refl). exact R13.
         ++ rewrite (HKEPT 18%bv ltac:(cbv; tauto)). exact R18.
         ++ rewrite (HKEPT 12%bv ltac:(cbv; tauto)). exact R12.
         ++ rewrite (HKEPT 8%bv ltac:(cbv; tauto)). exact R8.
         ++ rewrite (HKEPT 9%bv ltac:(cbv; tauto)). exact R9.
         ++ rewrite N14, (EE 14%nat 14%bv eq_refl). exact R14.
         ++ rewrite (HKEPT 15%bv ltac:(cbv; tauto)). exact R15.
         ++ exact N17.
         ++ exact N5.
         ++ exact N16.
    * (* the line ended at this separator: impossible, j < |T| *)
      exfalso. rcn_sep_branch j (Z.of_nat (length T)) EE R14 R8 Hc. apply Z.ltb_ge in Hc. lia.

  + (* a word byte: copy it *)
    rcn_byte_branch branch_eq_U 32 b E33 Hc.
    assert (HNS2 : is_sep b = false).
    { apply Z.eqb_neq in Hc. unfold is_sep. apply orb_false_intro; apply Z.eqb_neq; assumption. }
    clear Hc.
    (* 0x898f4 .. 0x89918: the wrap check of out + o (decided), the shadow check of out[o], the store, i++, o++ *)
    paj_run_tok RUN HS HJ SHOK Bspan.
    { srr_obls.
      lazymatch goal with |- range_addressable _ (U ?Ex _) _ _ =>
        rewrite (U_atom Ex 18 SHADOW_OFF
          ltac:(rewrite ?ew_ewset_other by lia; rewrite (EE 18%nat 18%bv eq_refl), R18; reflexivity)
          ltac:(unfold SHADOW_OFF; lia));
        rewrite (U_atom Ex 34 (p + oo) ltac:(rewrite ?ew_ewset_other by lia; exact E34) ltac:(lia))
      end.
      apply (range_addressable_sub _ SHADOW_OFF p (NN + 1));
        [ apply (range_addressable_of_block SEGS B LAWS ly1 S1 W _ _ p (NN + 1) p (NN + 1) (proj1 HJ) HPIN);
          rewrite ?rcn_rq; lia | lia | lia]. }
    { rcn_copy_awr j oo U32 U34. }
    rcn_copy_keep KF2 U32 U34 oo. clear_md.
    assert (Hlt1 : Z.of_nat (length (out0 ++ firstn (j - i) (skipn i T))) < NN + 1) by (rewrite Hlenj; lia).
    assert (Hsnoc : (out0 ++ firstn (j - i) (skipn i T)) ++ [b] = out0 ++ firstn (S j - i) (skipn i T)).
    { rewrite <- app_assoc. f_equal. replace (S j - i)%nat with (S (j - i)) by lia.
      symmetry. apply (rcn_firstn_snoc (skipn i T) (j - i) b).
      rewrite nth_error_skipn. replace (i + (j - i))%nat with j by lia. exact Eb. }
    psrr_branch_tok RUN BR HS SHOK Bspan.
    * (* more of the line to copy *)
      lazymatch type of Hc with context [sv_denot ?Ex _] =>
        assert (G14 : ew Ex 14 = w64 (Z.of_nat j))
          by (rewrite ?ew_ewset_other by lia; rewrite (EE 14%nat 14%bv eq_refl); exact R14);
        assert (G8 : ew Ex 8 = w64 NN)
          by (rewrite ?ew_ewset_other by lia; rewrite (EE 8%nat 8%bv eq_refl); exact R8);
        rewrite branch_ne_U, (U_atom Ex 8 NN G8 ltac:(lia)),
          (U_atom_off Ex 14 (Z.of_nat j) 1 G14 ltac:(lia) ltac:(lia)) in Hc
      end.
      assert (Hne : (S j < length T)%nat).
      { apply negb_true_iff, Z.eqb_neq in Hc. lia. }
      clear Hc.
      paj_run_to_tok RUNTO HS HJ SHOK Bspan K_COPY.
      { rcn_copy_awr j oo U32 U34. }
      rcn_copy_keep KF3 U32 U34 oo. clear_md.
      rcn_stored HZ b oo U34 E33.
      pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ rcn_ckeptall HS ltac:(env_agree_chain HAE)
                   ltac:(vm_compute; reflexivity)) as HKEPT.
      cbn [ms_regs restrict mkst] in HKEPT.
      pmkst HS.
      lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rr _ ?mm _) ?dd) _ =>
        assert (HId : RINV mm dd (out0 ++ firstn (S j - i) (skipn i T)));
        [ rewrite <- Hsnoc; apply (rcn_store_step _ b mem md _ _ HI HJ);
          [ rewrite Hlenj; intros a Ha Hn;
            rewrite (KF3 a Ha Hn), (KF2 a Ha Hn), (KF1b a Ha Hn), (KF1 a Ha Hn); reflexivity
          | rewrite Hlenj; exact HZ
          | exact Hlt1 ]
        | apply (IH i (S j) out0 rr mm dd) ] end.
      -- lia.
      -- lia.
      -- exact HOB.
      -- exact HId.
      -- unfold rcn_cregs, rcn_regs, rcn_fregs. repeat match goal with |- _ /\ _ => split end.
         ++ intros r Hr. rewrite (HKEPT r ltac:(revert Hr; cbv [rcn_kept rcn_ckeptall In]; tauto)).
            apply HK. exact Hr.
         ++ unfold spZ. rewrite (HKEPT 2%bv ltac:(cbv; tauto)). exact Hsp.
         ++ rewrite (HKEPT 10%bv ltac:(cbv; tauto)). exact R10.
         ++ rcn_rreg HS. rcn_off 13%nat oo 1 (eq_trans (EE 13%nat 13%bv eq_refl) R13).
            unfold w64. f_equal. unfold oo. lia.
         ++ rewrite (HKEPT 18%bv ltac:(cbv; tauto)). exact R18.
         ++ rewrite (HKEPT 12%bv ltac:(cbv; tauto)). exact R12.
         ++ rewrite (HKEPT 8%bv ltac:(cbv; tauto)). exact R8.
         ++ rewrite (HKEPT 9%bv ltac:(cbv; tauto)). exact R9.
         ++ rcn_rreg HS. rcn_off 14%nat (Z.of_nat j) 1 (eq_trans (EE 14%nat 14%bv eq_refl) R14).
            unfold w64. f_equal. lia.
         ++ rewrite (HKEPT 15%bv ltac:(cbv; tauto)). exact R15.
         ++ rcn_rreg HS. reflexivity.
         ++ rcn_rreg HS. reflexivity.
         ++ rcn_rreg HS. reflexivity.
         ++ rewrite (HKEPT 6%bv ltac:(cbv; tauto)), R6. unfold w64. f_equal. unfold oo. lia.
      -- intros t bt Ht Et. destruct (Nat.eq_dec t j) as [->|Hne2].
         ++ rewrite Eb in Et. injection Et as <-. exact HNS2.
         ++ apply (HNS t bt); [lia | exact Et].
      -- intros k regs' mem' md' Hk HNSk Hsepk HIk HRk.
         apply (KS k regs' mem' md'); try assumption. lia.
      -- exact KE.
    * (* the line ends with this word: `j 0x89950; mv a3,t1` *)
      lazymatch type of Hc with context [sv_denot ?Ex _] =>
        assert (G14 : ew Ex 14 = w64 (Z.of_nat j))
          by (rewrite ?ew_ewset_other by lia; rewrite (EE 14%nat 14%bv eq_refl); exact R14);
        assert (G8 : ew Ex 8 = w64 NN)
          by (rewrite ?ew_ewset_other by lia; rewrite (EE 8%nat 8%bv eq_refl); exact R8);
        rewrite branch_ne_U, (U_atom Ex 8 NN G8 ltac:(lia)),
          (U_atom_off Ex 14 (Z.of_nat j) 1 G14 ltac:(lia) ltac:(lia)) in Hc
      end.
      assert (Hfin : (S j = length T)%nat).
      { apply negb_false_iff, Z.eqb_eq in Hc. lia. }
      clear Hc.
      paj_run_to_tok RUNTO HS HJ SHOK Bspan K_FIN.
      { rcn_copy_awr j oo U32 U34. }
      rcn_copy_keep KF3 U32 U34 oo. clear_md.
      rcn_stored HZ b oo U34 E33.
      pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ rcn_ckeptall HS ltac:(env_agree_chain HAE)
                   ltac:(vm_compute; reflexivity)) as HKEPT.
      cbn [ms_regs restrict mkst] in HKEPT.
      pmkst HS.
      assert (Hskip : firstn (S j - i) (skipn i T) = skipn i T)
        by (apply firstn_all2; rewrite length_skipn; lia).
      lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rr _ ?mm _) ?dd) _ =>
        assert (HId : RINV mm dd (out0 ++ skipn i T));
        [ rewrite <- Hskip, <- Hsnoc; apply (rcn_store_step _ b mem md _ _ HI HJ);
          [ rewrite Hlenj; intros a Ha Hn;
            rewrite (KF3 a Ha Hn), (KF2 a Ha Hn), (KF1b a Ha Hn), (KF1 a Ha Hn); reflexivity
          | rewrite Hlenj; exact HZ
          | exact Hlt1 ]
        | apply (KE rr mm dd) ] end.
      -- intros t bt Ht Et. destruct (Nat.eq_dec t j) as [->|Hne2].
         ++ rewrite Eb in Et. injection Et as <-. exact HNS2.
         ++ apply (HNS t bt); [lia | exact Et].
      -- exact HId.
      -- unfold rcn_fregs. repeat match goal with |- _ /\ _ => split end.
         ++ intros r Hr. rewrite (HKEPT r ltac:(revert Hr; cbv [rcn_kept rcn_ckeptall In]; tauto)).
            apply HK. exact Hr.
         ++ unfold spZ. rewrite (HKEPT 2%bv ltac:(cbv; tauto)). exact Hsp.
         ++ rewrite (HKEPT 10%bv ltac:(cbv; tauto)). exact R10.
         ++ rcn_rreg HS. rcn_off 6%nat (NN + oo - Z.of_nat j) 0 (eq_trans (EE 6%nat 6%bv eq_refl) R6).
            unfold w64. f_equal. unfold oo. lia.
         ++ rewrite (HKEPT 18%bv ltac:(cbv; tauto)). exact R18.
         ++ rewrite (HKEPT 12%bv ltac:(cbv; tauto)). exact R12.
Qed.

(* The word-scan loop (0x8984c): separators are skipped until a word byte or the end of the line. The UBSan check
   0x89850 (text + i < text: the sum wraps) is refuted at the branch; 0x8985c ((text != 0) xor (text + i == 0)) and
   0x89860 (text null) are decided by the executor from text, text + i >= 4096. *)
Lemma rcn_skip : forall (d i : nat) regs mem md out,
  (length T - i <= d)%nat -> (i < length T)%nat -> Z.of_nat (length out) <= NN ->
  RINV mem md out -> rcn_regs regs i (Z.of_nat (length out)) -> getr regs 6 = w64 NN ->
  (forall (j : nat) regs' mem' md',
     (i <= j <= length T)%nat ->
     (forall t b, (i <= t < j)%nat -> nth_error T t = Some b -> is_sep b = true) ->
     (j = length T \/ exists b, nth_error T j = Some b /\ is_sep b = false) ->
     RINV mem' md' out -> rcn_regs regs' j (Z.of_nat (length out)) -> getr regs' 6 = w64 NN ->
     SRr SEGS W (mkCfg (mkst regs' (Z_to_bv 64 (BASE + K_WORD)) mem' (seg_rom SEGS)) md') RPOST) ->
  SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + K_SKIP)) mem (seg_rom SEGS)) md) RPOST.
Proof.
induction d as [|d IH]; intros i regs mem md out Hd Hi HOL HI HR R6 KW; [lia|].
pose proof HI as (HJ & HKEEP & HOUT & HLEN).
pose proof HR as ((HK & Hsp & R10 & R13 & R18 & R12) & R8 & R9 & R14 & R15 & R17 & R5 & R16).
destruct (nth_error T i) as [b|] eqn:Eb; [|exfalso; apply nth_error_None in Eb; lia].
pose proof (rcn_txt _ _ _ HI) as HTX.
pose proof (rcn_bytes_nth _ _ _ _ _ HTX Eb) as HBi.
pose proof (rcn_byte_range b) as HBR.
pose proof (rcn_blk _ _ _ HI) as (Hp16 & Hp4096 & Hpceil & Hpstk).
pose proof HSTK0 as (Hsp16 & Hstk0 & Hcl & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof alloc_ceiling_val as HAC. pose proof HTXB as (Htx1 & Htx2).
assert (HL8 : NN <= 8192) by (unfold LMAX in HTN; lia).
assert (HAR : AR SEGS B ly1 S1 W mem md) by exact (rcn_ar _ _ _ HI).
set (E := Eimg (Ereg regs [w64 (text + Z.of_nat i); w64 (bv_unsigned b)])).
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr regs r)
  by (intros k r Hk; subst E; apply ew_Eimg_Ereg_nat; exact Hk).
assert (E32 : ew E 32 = w64 (text + Z.of_nat i))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = w64 (bv_unsigned b))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (Usp : bv_unsigned (ew E 2) = sp0 - 32) by (rewrite (EE 2%nat 2%bv eq_refl); exact Hsp).
assert (U32 : bv_unsigned (ew E 32) = text + Z.of_nat i) by (rewrite E32; apply unsigned_lit_small; lia).
assert (HS : st_ok_pi SEGS VAL E rcn_ss_skip
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + K_SKIP)) mem (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold rcn_ss_skip. apply pa_entry_st_ok_full.
  - apply regs_ok_pin;
    [ apply regs_ok_pin;
      [ apply regs_ok_pin;
        [ apply regs_ok_pin; [apply regs_ok_Eimg_Ereg | intros X; discriminate X | cbn [sv_denot]; exact R17]
        | intros X; discriminate X | cbn [sv_denot]; exact R5]
      | intros X; discriminate X | cbn [sv_denot]; exact R16]
    | intros X; discriminate X | ].
    cbn [sv_denot]. rewrite (EE 8%nat 8%bv eq_refl), R8. unfold w64.
    rewrite unsigned_lit_small by lia. rewrite Z.add_0_r. exact R6.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U32. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    apply (chunk_ok_val SEGS E _ (text + Z.of_nat i) 0 1 (SOff 33 0) (bv_unsigned b));
    [cbn [sv_denot]; rewrite E33; unfold w64; rewrite unsigned_lit_small by lia;
     rewrite Z.add_0_r; reflexivity | cbn; lia | lia |].
    rewrite Z.add_0_r. apply rcn_val_mem1. exact HBi.
  - cbn [pairwise_disjoint all_disjoint]. tauto.
  - split; [|split; [exact I|]].
    + cbn [f_atoms atoms_ok]. unfold afact_ok, PTR; cbn [af_lo af_hi af_al2].
      rewrite Usp, U32, (EE 8%nat 8%bv eq_refl), (EE 9%nat 9%bv eq_refl), (EE 10%nat 10%bv eq_refl),
        (EE 13%nat 13%bv eq_refl), (EE 14%nat 14%bv eq_refl), (EE 18%nat 18%bv eq_refl), E33.
      rewrite R8, R9, R10, R13, R14, R18. unfold w64.
      rewrite !unsigned_lit_small by (unfold SHADOW_OFF; lia).
      change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
      assert (Hm16 : (sp0 - 32) mod 16 = 0) by (rewrite Zminus_mod, Hsp16; reflexivity).
      repeat split; try (unfold SB, SHADOW_OFF in * ); try lia.
    + cbn [f_alias alias_ok]. split; [|exact I]. cbn [sv_denot].
      rewrite (EE 9%nat 9%bv eq_refl), (EE 14%nat 14%bv eq_refl), R9, R14, E32. unfold w64.
      rewrite !unsigned_lit_small by lia. rewrite !Z.add_0_r. apply rcn_alu_add. }
assert (SHOK : sh_ok SEGS (SOff 18 0) (@nil shent) E (mrestrict (w_H W) mem)) by apply Forall_nil.
assert (OBT : forall (Ex : env) mem' md', AR SEGS B ly1 S1 W mem' md' -> ew Ex 18 = ew E 18 -> ew Ex 32 = ew E 32 ->
  range_addressable (aview SEGS (w_H W) mem') (U Ex (SOff 18 0)) (U Ex (SOff 32 0)) 1).
{ intros Ex mem' md' HAR' H18 H32. rewrite (U_atom Ex 18 SHADOW_OFF ltac:(rewrite H18, (EE 18%nat 18%bv eq_refl), R18; reflexivity)
    ltac:(unfold SHADOW_OFF; lia)).
  rewrite (U_atom Ex 32 (text + Z.of_nat i) ltac:(rewrite H32; exact E32) ltac:(lia)).
  apply (range_addressable_sub (rdW W mem') SHADOW_OFF text NN); [exact (HTADDR mem' md' HAR') | lia | lia]. }
assert (HAE : env_agree 32 (Ereg regs [w64 (text + Z.of_nat i); w64 (bv_unsigned b)]) E)
  by (subst E; split; [intros k Hk; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
(* 0x8984c .. 0x89850: text + i and its UBSan wrap check *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ awr_ok_tac. }
rcn_keepf KF0.
psrr_branch_tok RUN BR HS SHOK Bspan.
{ (* the trap 0x89850 (text + i < text unsigned): text + i < 2 ^ 64, so the sum does not wrap *)
  exfalso.
  lazymatch type of Hc with context [sv_denot ?Ex _] =>
    assert (G32 : ew Ex 32 = w64 (text + Z.of_nat i)) by (rewrite ?ew_ewset_other by lia; exact E32);
    assert (G9 : ew Ex 9 = w64 text)
      by (rewrite ?ew_ewset_other by lia; rewrite (EE 9%nat 9%bv eq_refl); exact R9);
    rewrite branch_ltu_U, (U_atom Ex 32 (text + Z.of_nat i) G32 ltac:(lia)), (U_atom Ex 9 text G9 ltac:(lia)) in Hc
  end.
  apply Z.ltb_lt in Hc. lia. }
clear Hc.
(* 0x89854 .. 0x89878: the two other checks (decided), the byte's shadow check, the byte, `beq a1,a7` *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ srr_obls. apply (OBT _ _ _ (proj1 HJ)); rewrite ?ew_ewset_other by lia; reflexivity. }
{ awr_ok_tac. }
rcn_keepf KF1.
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* the byte is a space *)
  rcn_byte_branch branch_eq_U 32 b E33 Hc.
  assert (HSEPB : is_sep b = true)
    by (apply Z.eqb_eq in Hc; unfold is_sep; rewrite Hc; reflexivity).
  clear Hc.
  paj_run_tok RUN HS HJ SHOK Bspan.
  { awr_ok_tac. }
  rcn_keepf KF2.
  psrr_branch_tok RUN BR HS SHOK Bspan.
  * (* another byte to scan *)
    rcn_ltu_branch i (Z.of_nat (length T)) EE R14 R8 Hc.
    assert (Hlt : (S i < length T)%nat) by (apply Z.ltb_lt in Hc; lia). clear Hc.
    paj_run_to_tok RUNTO HS HJ SHOK Bspan K_SKIP.
    { awr_ok_tac. }
    rcn_keepf KF3.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ rcn_keptall HS ltac:(env_agree_chain HAE)
                 ltac:(vm_compute; reflexivity)) as HKEPT.
    cbn [ms_regs restrict mkst] in HKEPT.
    prreg HS (17%bv : bv 5) N17. prreg HS (5%bv : bv 5) N5.
    prreg HS (16%bv : bv 5) N16. prreg HS (6%bv : bv 5) N6. prreg HS (14%bv : bv 5) N14.
    pmkst HS.
    lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rr _ ?mm _) ?dd) _ =>
      assert (HI2 : RINV mm dd out);
      [ apply (rcn_keep_step out mem md _ _ HI HJ); intros a Ha;
        rewrite (KF3 a Ha ltac:(cbv beta; tauto)), (KF2 a Ha ltac:(cbv beta; tauto)),
                (KF1 a Ha ltac:(cbv beta; tauto)), (KF0 a Ha ltac:(cbv beta; tauto)); reflexivity
      | apply (IH (S i) rr mm dd out) ] end.
    -- lia.
    -- lia.
    -- exact HOL.
    -- exact HI2.
    -- unfold rcn_regs, rcn_fregs. repeat match goal with |- _ /\ _ => split end.
       ++ intros r Hr. rewrite (HKEPT r ltac:(revert Hr; cbv [rcn_kept rcn_keptall In]; tauto)).
          apply HK. exact Hr.
       ++ unfold spZ. rewrite (HKEPT 2%bv ltac:(cbv; tauto)). exact Hsp.
       ++ rewrite (HKEPT 10%bv ltac:(cbv; tauto)). exact R10.
       ++ rewrite (HKEPT 13%bv ltac:(cbv; tauto)). exact R13.
       ++ rewrite (HKEPT 18%bv ltac:(cbv; tauto)). exact R18.
       ++ rewrite (HKEPT 12%bv ltac:(cbv; tauto)). exact R12.
       ++ rewrite (HKEPT 8%bv ltac:(cbv; tauto)). exact R8.
       ++ rewrite (HKEPT 9%bv ltac:(cbv; tauto)). exact R9.
       ++ rewrite N14, (EE 14%nat 14%bv eq_refl), R14; unfold w64;
          rewrite unsigned_lit_small by lia; f_equal; lia.
       ++ rewrite (HKEPT 15%bv ltac:(cbv; tauto)). exact R15.
       ++ exact N17.
       ++ exact N5.
       ++ exact N16.
    -- rewrite N6, (EE 8%nat 8%bv eq_refl). exact R8.
    -- intros j regs' mem' md' Hj HSEPS Hend HI' HR' R6'.
       apply (KW j regs' mem' md'); try assumption; [lia|].
       intros t bt Ht Et. destruct (Nat.eq_dec t i) as [->|Hne].
       ++ rewrite Eb in Et. injection Et as <-. exact HSEPB.
       ++ apply (HSEPS t bt); [lia | exact Et].
  * (* the line ends here: `mv a4,t1` *)
    rcn_ltu_branch i (Z.of_nat (length T)) EE R14 R8 Hc.
    assert (Hend : (S i = length T)%nat) by (apply Z.ltb_ge in Hc; lia). clear Hc.
    paj_run_to_tok RUNTO HS HJ SHOK Bspan K_WORD.
    { awr_ok_tac. }
    rcn_keepf KF3.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ rcn_keptall HS ltac:(env_agree_chain HAE)
                 ltac:(vm_compute; reflexivity)) as HKEPT.
    cbn [ms_regs restrict mkst] in HKEPT.
    prreg HS (17%bv : bv 5) N17. prreg HS (5%bv : bv 5) N5.
    prreg HS (16%bv : bv 5) N16. prreg HS (6%bv : bv 5) N6. prreg HS (14%bv : bv 5) N14.
    pmkst HS.
    lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rr _ ?mm _) ?dd) _ =>
      assert (HI2 : RINV mm dd out);
      [ apply (rcn_keep_step out mem md _ _ HI HJ); intros a Ha;
        rewrite (KF3 a Ha ltac:(cbv beta; tauto)), (KF2 a Ha ltac:(cbv beta; tauto)),
                (KF1 a Ha ltac:(cbv beta; tauto)), (KF0 a Ha ltac:(cbv beta; tauto)); reflexivity
      | apply (KW (length T) rr mm dd) ] end.
    -- lia.
    -- intros t bt Ht Et. assert (t = i) by lia. subst t. rewrite Eb in Et. injection Et as <-. exact HSEPB.
    -- left. reflexivity.
    -- exact HI2.
    -- unfold rcn_regs, rcn_fregs. repeat match goal with |- _ /\ _ => split end.
       ++ intros r Hr. rewrite (HKEPT r ltac:(revert Hr; cbv [rcn_kept rcn_keptall In]; tauto)).
          apply HK. exact Hr.
       ++ unfold spZ. rewrite (HKEPT 2%bv ltac:(cbv; tauto)). exact Hsp.
       ++ rewrite (HKEPT 10%bv ltac:(cbv; tauto)). exact R10.
       ++ rewrite (HKEPT 13%bv ltac:(cbv; tauto)). exact R13.
       ++ rewrite (HKEPT 18%bv ltac:(cbv; tauto)). exact R18.
       ++ rewrite (HKEPT 12%bv ltac:(cbv; tauto)). exact R12.
       ++ rewrite (HKEPT 8%bv ltac:(cbv; tauto)). exact R8.
       ++ rewrite (HKEPT 9%bv ltac:(cbv; tauto)). exact R9.
       ++ rewrite N14, (EE 8%nat 8%bv eq_refl). exact R8.
       ++ rewrite (HKEPT 15%bv ltac:(cbv; tauto)). exact R15.
       ++ exact N17.
       ++ exact N5.
       ++ exact N16.
    -- rewrite N6, (EE 8%nat 8%bv eq_refl). exact R8.

- (* not a space *)
  rcn_byte_branch branch_eq_U 32 b E33 Hc.
  assert (HN32 : bv_unsigned b <> 32) by (apply Z.eqb_neq in Hc; exact Hc).
  clear Hc.
  paj_run_tok RUN HS HJ SHOK Bspan.
  { awr_ok_tac. }
  rcn_keepf KF1b.
  psrr_branch_tok RUN BR HS SHOK Bspan.
  + (* not a tab either: the word starts here *)
    rcn_byte_branch branch_ne_U 9 b E33 Hc.
    assert (HNS : is_sep b = false).
    { apply negb_true_iff, Z.eqb_neq in Hc. unfold is_sep.
      apply orb_false_intro; apply Z.eqb_neq; assumption. }
    clear Hc.
    paj_run_to_tok RUNTO HS HJ SHOK Bspan K_WORD.
    { awr_ok_tac. }
    rcn_keepf KF2b.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ rcn_keptall HS ltac:(env_agree_chain HAE)
                 ltac:(vm_compute; reflexivity)) as HKEPT.
    cbn [ms_regs restrict mkst] in HKEPT.
    prreg HS (17%bv : bv 5) N17. prreg HS (5%bv : bv 5) N5.
    prreg HS (16%bv : bv 5) N16. prreg HS (6%bv : bv 5) N6. prreg HS (14%bv : bv 5) N14.
    pmkst HS.
    lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rr _ ?mm _) ?dd) _ =>
      assert (HI2 : RINV mm dd out);
      [ apply (rcn_keep_step out mem md _ _ HI HJ); intros a Ha;
        rewrite (KF2b a Ha ltac:(cbv beta; tauto)), (KF1b a Ha ltac:(cbv beta; tauto)),
                (KF1 a Ha ltac:(cbv beta; tauto)), (KF0 a Ha ltac:(cbv beta; tauto)); reflexivity
      | apply (KW i rr mm dd) ] end.
    * lia.
    * intros t bt Ht Et. lia.
    * right. exists b. split; [exact Eb | exact HNS].
    * exact HI2.
    * unfold rcn_regs, rcn_fregs. repeat match goal with |- _ /\ _ => split end.
      -- intros r Hr. rewrite (HKEPT r ltac:(revert Hr; cbv [rcn_kept rcn_keptall In]; tauto)).
         apply HK. exact Hr.
      -- unfold spZ. rewrite (HKEPT 2%bv ltac:(cbv; tauto)). exact Hsp.
      -- rewrite (HKEPT 10%bv ltac:(cbv; tauto)). exact R10.
      -- rewrite (HKEPT 13%bv ltac:(cbv; tauto)). exact R13.
      -- rewrite (HKEPT 18%bv ltac:(cbv; tauto)). exact R18.
      -- rewrite (HKEPT 12%bv ltac:(cbv; tauto)). exact R12.
      -- rewrite (HKEPT 8%bv ltac:(cbv; tauto)). exact R8.
      -- rewrite (HKEPT 9%bv ltac:(cbv; tauto)). exact R9.
      -- rewrite N14, (EE 14%nat 14%bv eq_refl). exact R14.
      -- rewrite (HKEPT 15%bv ltac:(cbv; tauto)). exact R15.
      -- exact N17.
      -- exact N5.
      -- exact N16.
    * rewrite N6, (EE 8%nat 8%bv eq_refl). exact R8.
  + (* a tab *)
    rcn_byte_branch branch_ne_U 9 b E33 Hc.
    assert (HSEPB : is_sep b = true).
    { apply negb_false_iff, Z.eqb_eq in Hc. unfold is_sep. rewrite Hc. apply orb_true_r. }
    clear Hc.
  paj_run_tok RUN HS HJ SHOK Bspan.
  { awr_ok_tac. }
  rcn_keepf KF2c.
  psrr_branch_tok RUN BR HS SHOK Bspan.
  * (* another byte to scan *)
    rcn_ltu_branch i (Z.of_nat (length T)) EE R14 R8 Hc.
    assert (Hlt : (S i < length T)%nat) by (apply Z.ltb_lt in Hc; lia). clear Hc.
    paj_run_to_tok RUNTO HS HJ SHOK Bspan K_SKIP.
    { awr_ok_tac. }
    rcn_keepf KF3c.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ rcn_keptall HS ltac:(env_agree_chain HAE)
                 ltac:(vm_compute; reflexivity)) as HKEPT.
    cbn [ms_regs restrict mkst] in HKEPT.
    prreg HS (17%bv : bv 5) N17. prreg HS (5%bv : bv 5) N5.
    prreg HS (16%bv : bv 5) N16. prreg HS (6%bv : bv 5) N6. prreg HS (14%bv : bv 5) N14.
    pmkst HS.
    lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rr _ ?mm _) ?dd) _ =>
      assert (HI2 : RINV mm dd out);
      [ apply (rcn_keep_step out mem md _ _ HI HJ); intros a Ha;
        rewrite (KF3c a Ha ltac:(cbv beta; tauto)), (KF2c a Ha ltac:(cbv beta; tauto)),
                (KF1b a Ha ltac:(cbv beta; tauto)), (KF1 a Ha ltac:(cbv beta; tauto)),
                (KF0 a Ha ltac:(cbv beta; tauto)); reflexivity
      | apply (IH (S i) rr mm dd out) ] end.
    -- lia.
    -- lia.
    -- exact HOL.
    -- exact HI2.
    -- unfold rcn_regs, rcn_fregs. repeat match goal with |- _ /\ _ => split end.
       ++ intros r Hr. rewrite (HKEPT r ltac:(revert Hr; cbv [rcn_kept rcn_keptall In]; tauto)).
          apply HK. exact Hr.
       ++ unfold spZ. rewrite (HKEPT 2%bv ltac:(cbv; tauto)). exact Hsp.
       ++ rewrite (HKEPT 10%bv ltac:(cbv; tauto)). exact R10.
       ++ rewrite (HKEPT 13%bv ltac:(cbv; tauto)). exact R13.
       ++ rewrite (HKEPT 18%bv ltac:(cbv; tauto)). exact R18.
       ++ rewrite (HKEPT 12%bv ltac:(cbv; tauto)). exact R12.
       ++ rewrite (HKEPT 8%bv ltac:(cbv; tauto)). exact R8.
       ++ rewrite (HKEPT 9%bv ltac:(cbv; tauto)). exact R9.
       ++ rewrite N14, (EE 14%nat 14%bv eq_refl), R14; unfold w64;
          rewrite unsigned_lit_small by lia; f_equal; lia.
       ++ rewrite (HKEPT 15%bv ltac:(cbv; tauto)). exact R15.
       ++ exact N17.
       ++ exact N5.
       ++ exact N16.
    -- rewrite N6, (EE 8%nat 8%bv eq_refl). exact R8.
    -- intros j regs' mem' md' Hj HSEPS Hend HI' HR' R6'.
       apply (KW j regs' mem' md'); try assumption; [lia|].
       intros t bt Ht Et. destruct (Nat.eq_dec t i) as [->|Hne].
       ++ rewrite Eb in Et. injection Et as <-. exact HSEPB.
       ++ apply (HSEPS t bt); [lia | exact Et].
  * (* the line ends here: `mv a4,t1` *)
    rcn_ltu_branch i (Z.of_nat (length T)) EE R14 R8 Hc.
    assert (Hend : (S i = length T)%nat) by (apply Z.ltb_ge in Hc; lia). clear Hc.
    paj_run_to_tok RUNTO HS HJ SHOK Bspan K_WORD.
    { awr_ok_tac. }
    rcn_keepf KF3c.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ rcn_keptall HS ltac:(env_agree_chain HAE)
                 ltac:(vm_compute; reflexivity)) as HKEPT.
    cbn [ms_regs restrict mkst] in HKEPT.
    prreg HS (17%bv : bv 5) N17. prreg HS (5%bv : bv 5) N5.
    prreg HS (16%bv : bv 5) N16. prreg HS (6%bv : bv 5) N6. prreg HS (14%bv : bv 5) N14.
    pmkst HS.
    lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rr _ ?mm _) ?dd) _ =>
      assert (HI2 : RINV mm dd out);
      [ apply (rcn_keep_step out mem md _ _ HI HJ); intros a Ha;
        rewrite (KF3c a Ha ltac:(cbv beta; tauto)), (KF2c a Ha ltac:(cbv beta; tauto)),
                (KF1b a Ha ltac:(cbv beta; tauto)), (KF1 a Ha ltac:(cbv beta; tauto)),
                (KF0 a Ha ltac:(cbv beta; tauto)); reflexivity
      | apply (KW (length T) rr mm dd) ] end.
    -- lia.
    -- intros t bt Ht Et. assert (t = i) by lia. subst t. rewrite Eb in Et. injection Et as <-. exact HSEPB.
    -- left. reflexivity.
    -- exact HI2.
    -- unfold rcn_regs, rcn_fregs. repeat match goal with |- _ /\ _ => split end.
       ++ intros r Hr. rewrite (HKEPT r ltac:(revert Hr; cbv [rcn_kept rcn_keptall In]; tauto)).
          apply HK. exact Hr.
       ++ unfold spZ. rewrite (HKEPT 2%bv ltac:(cbv; tauto)). exact Hsp.
       ++ rewrite (HKEPT 10%bv ltac:(cbv; tauto)). exact R10.
       ++ rewrite (HKEPT 13%bv ltac:(cbv; tauto)). exact R13.
       ++ rewrite (HKEPT 18%bv ltac:(cbv; tauto)). exact R18.
       ++ rewrite (HKEPT 12%bv ltac:(cbv; tauto)). exact R12.
       ++ rewrite (HKEPT 8%bv ltac:(cbv; tauto)). exact R8.
       ++ rewrite (HKEPT 9%bv ltac:(cbv; tauto)). exact R9.
       ++ rewrite N14, (EE 8%nat 8%bv eq_refl). exact R8.
       ++ rewrite (HKEPT 15%bv ltac:(cbv; tauto)). exact R15.
       ++ exact N17.
       ++ exact N5.
       ++ exact N16.
    -- rewrite N6, (EE 8%nat 8%bv eq_refl). exact R8.
Qed.

(* the count the word head builds for t1: (s0 + c) + a3 - a4 *)
Lemma rcn_den_t1 : forall (E : env) (m n k : nat) am an ak c,
  ew E m = Z_to_bv 64 am -> ew E n = Z_to_bv 64 an -> ew E k = Z_to_bv 64 ak ->
  0 <= am < 2 ^ 62 -> 0 <= c <= 1 -> 0 <= an < 2 ^ 62 -> 0 <= ak <= am + c + an ->
  sv_denot E (SAlu ALU_ADD (SAlu ALU_ADD (SOff m c) (SOff n 0)) (SMd M_MUL (SOff k 0) (SLit (-1))))
  = Z_to_bv 64 (am + c + an - ak).
Proof.
  intros E m n k am an ak c Hm Hn Hk Ham Hc Han Hak.
  rewrite denot_lit_U. f_equal.
  rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SMd. cbn [zmd_raw]. rewrite U_SLit.
  rewrite (U_atom_off E m am c Hm ltac:(lia) ltac:(lia)), (U_atom E n an Hn ltac:(lia)),
    (U_atom E k ak Hk ltac:(lia)).
  change (zcanon (-1)) with (2 ^ 64 - 1). unfold zcanon, M64.
  rewrite Zplus_mod_idemp_l, Zplus_mod_idemp_r.
  replace (am + c + an + ak * (2 ^ 64 - 1)) with ((am + c + an - ak) + ak * 2 ^ 64) by lia.
  rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.

Local Ltac rcn_t1 am an ak c Hm Hn Hk :=
  lazymatch goal with |- sv_denot ?Ex _ = _ =>
    rewrite (rcn_den_t1 Ex 8 13 14 am an ak c ltac:(rewrite ?ew_ewset_other by lia; exact Hm)
      ltac:(rewrite ?ew_ewset_other by lia; exact Hn) ltac:(rewrite ?ew_ewset_other by lia; exact Hk)
      ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) end.

(* the write window of the word head: the one byte at p + lo of the fresh block *)
Local Ltac rcn_word_awr lo2 U32x :=
  eapply (awr_ok_cons_gen B _ _ _ _ _ _ _ _ _ _ _ 32 (p + lo2));
  [ reflexivity
  | rewrite ?ew_ewset_other by lia; exact U32x
  | cbn [YP09.r_wlo YP09.r_whi]; intros aq Haq;
    replace aq with (p + (aq - p)) by lia; apply rcn_awr_new; lia
  | apply awr_ok_nil ].

Local Ltac rcn_word_keep nm lo2 U32x :=
  lazymatch goal with
  | HFrx : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ =>
    pose proof (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun a => p + lo2 <= a < p + lo2 + 1) HFrx
      ltac:(intros bq wlo whi aq Hin Hrr; vm_compute in Hin;
            repeat (destruct Hin as [Hq | Hin];
                    [injection Hq as <- <- <-; cbn [base_val] in Hrr;
                     rewrite ?ew_ewset_other in Hrr by lia; rewrite ?U32x in Hrr; lia|]);
            destruct Hin)) as nm;
    clear HFrx
  end;
  lazymatch goal with HFx : frame_of _ _ ?m1 ?m2 |- _ => clear HFx | _ => idtac end;
  lazymatch goal with HGx : mem_grows _ _ |- _ => clear HGx | _ => idtac end;
  clear_md.

(* the SPACE the word head stores at p + lo (region 0 of the state, the fresh block at atom 32) *)
Local Ltac rcn_word_stored HZ lo2 U32x :=
  lazymatch goal with
  | HSx : st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msx) |- _ =>
    let r := eval vm_compute in (nth 0 (ss_mem ssx) got_regionP) in
    let HRo := fresh "HRo" in let U32y := fresh "U32y" in let HV := fresh "HV" in
    pose proof (st_ok_pi_region_nth Ex ssx (restrict (w_H W) msx) 0 r HSx ltac:(vm_compute; reflexivity)) as HRo;
    assert (U32y : bv_unsigned (ew Ex 32) = p + lo2) by (rewrite ?ew_ewset_other by lia; exact U32x);
    pose proof (field_of_region_any Ex (mrestrict (w_H W) (ms_mem msx)) 32 (p + lo2) _ _ _ _ _ 0 1%N (SLit 32)
                  HRo U32y ltac:(cbn; tauto) ltac:(cbn; lia)) as HV;
    cbn [ms_mem restrict mkst] in HRo, HV;
    replace (bv_unsigned (sv_denot Ex (SLit 32)) mod 2 ^ (8 * Z.of_N 1)) with 32 in HV
      by (cbn [sv_denot]; vm_compute; reflexivity);
    assert (HZ : rdW W (ms_mem msx) (p + lo2) = Some (bv_unsigned SPACE))
      by (replace (bv_unsigned SPACE) with 32 by (vm_compute; reflexivity);
          apply rcn_rd_of_val_mem1; [lia | rewrite <- (Z.add_0_r (p + lo2)); exact HV]);
    clear HRo U32y HV
  end.

(* the two continuations of the copy loop, as the word head hands them over: `out0` is what the block holds when the
   copy of the word at j begins. *)
Lemma rcn_word_KS : forall (i j : nat) out out0,
  rcn_bndry T i -> (i <= j < length T)%nat -> out = canon (firstn i T) ->
  out0 = match out with [] => [] | _ :: _ => out ++ [SPACE] end ->
  (forall t b, (i <= t < j)%nat -> nth_error T t = Some b -> is_sep b = true) ->
  (forall b, nth_error T j = Some b -> is_sep b = false) ->
  forall (k : nat) regs' mem' md',
    (j <= k < length T)%nat ->
    (forall t b, (j <= t < k)%nat -> nth_error T t = Some b -> is_sep b = false) ->
    (exists b, nth_error T k = Some b /\ is_sep b = true) ->
    RINV mem' md' (out0 ++ firstn (k - j) (skipn j T)) ->
    rcn_regs regs' k (Z.of_nat (length out0) + Z.of_nat (k - j)) ->
    (forall (i2 : nat) regs2 mem2 md2, (i2 < length T)%nat -> (i < i2)%nat -> rcn_bndry T i2 ->
       RINV mem2 md2 (canon (firstn i2 T)) ->
       rcn_regs regs2 i2 (Z.of_nat (length (canon (firstn i2 T)))) ->
       SRr SEGS W (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + K_OUTER)) mem2 (seg_rom SEGS)) md2) RPOST) ->
    SRr SEGS W (mkCfg (mkst regs' (Z_to_bv 64 (BASE + K_OUTER)) mem' (seg_rom SEGS)) md') RPOST.
Proof.
  intros i j out out0 HB Hij Hout Hout0 HSEPS HNSj k regs' mem' md' Hk HNSk (bk & Ebk & Hbk) HI' HR' KO.
  assert (Hjk : (j < k)%nat).
  { destruct (Nat.eq_dec j k) as [->|Hne]; [|lia]. exfalso.
    pose proof (HNSj bk Ebk) as Hn. rewrite Hbk in Hn. discriminate. }
  assert (ESTEP : canon (firstn k T) = out0 ++ firstn (k - j) (skipn j T)).
  { apply (rcn_canon_step T i j k out out0 HB ltac:(lia) ltac:(lia) HSEPS); [| exact Hout | exact Hout0].
    intros t b Ht Et. destruct (Nat.eq_dec t j) as [->|Hne]; [exact (HNSj b Et) | apply (HNSk t b); [lia|exact Et]]. }
  assert (Hlen : Z.of_nat (length (canon (firstn k T))) = Z.of_nat (length out0) + Z.of_nat (k - j)).
  { rewrite ESTEP, length_app, length_firstn, length_skipn. lia. }
  apply (KO k regs' mem' md'); [lia | lia | | rewrite ESTEP; exact HI' | rewrite Hlen; exact HR'].
  right. exists bk. split; [exact Ebk | exact Hbk].
Qed.

Lemma rcn_word_KE : forall (i j : nat) out out0,
  rcn_bndry T i -> (i <= j < length T)%nat -> out = canon (firstn i T) ->
  out0 = match out with [] => [] | _ :: _ => out ++ [SPACE] end ->
  (forall t b, (i <= t < j)%nat -> nth_error T t = Some b -> is_sep b = true) ->
  forall regs' mem' md',
    (forall t b, (j <= t < length T)%nat -> nth_error T t = Some b -> is_sep b = false) ->
    RINV mem' md' (out0 ++ skipn j T) ->
    rcn_fregs regs' (Z.of_nat (length out0) + Z.of_nat (length T - j)) ->
    SRr SEGS W (mkCfg (mkst regs' (Z_to_bv 64 (BASE + K_FIN)) mem' (seg_rom SEGS)) md') RPOST.
Proof.
  intros i j out out0 HB Hij Hout Hout0 HSEPS regs' mem' md' HNSk HI' HR'.
  assert (ESTEP : canon (firstn (length T) T) = out0 ++ firstn (length T - j) (skipn j T)).
  { apply (rcn_canon_step T i j (length T) out out0 HB ltac:(lia) ltac:(lia) HSEPS); [| exact Hout | exact Hout0].
    intros t b Ht Et. apply (HNSk t b); [lia | exact Et]. }
  assert (Hall : firstn (length T) T = T) by apply firstn_all.
  assert (Hsk : firstn (length T - j) (skipn j T) = skipn j T)
    by (apply firstn_all2; rewrite length_skipn; lia).
  rewrite Hall, Hsk in ESTEP.
  assert (Hlen : Z.of_nat (length (canon T)) = Z.of_nat (length out0) + Z.of_nat (length T - j)).
  { rewrite ESTEP, length_app, length_skipn. lia. }
  apply (rcn_fin regs' mem' md'); [rewrite ESTEP; exact HI' | rewrite Hlen; exact HR'].
Qed.

(* The word head (0x8989c): the word that starts at j is copied, with one space before it when the block already
   holds a word. The UBSan check 0x898a4 (~out < o) is decided by the executor. *)
Lemma rcn_word : forall (i j : nat) regs mem md,
  rcn_bndry T i -> (i <= j <= length T)%nat -> (i < length T)%nat ->
  (forall t b, (i <= t < j)%nat -> nth_error T t = Some b -> is_sep b = true) ->
  (j = length T \/ exists b, nth_error T j = Some b /\ is_sep b = false) ->
  RINV mem md (canon (firstn i T)) ->
  rcn_regs regs j (Z.of_nat (length (canon (firstn i T)))) ->
  (forall (i2 : nat) regs2 mem2 md2, (i2 < length T)%nat -> (i < i2)%nat -> rcn_bndry T i2 ->
     RINV mem2 md2 (canon (firstn i2 T)) ->
     rcn_regs regs2 i2 (Z.of_nat (length (canon (firstn i2 T)))) ->
     SRr SEGS W (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + K_OUTER)) mem2 (seg_rom SEGS)) md2) RPOST) ->
  SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + K_WORD)) mem (seg_rom SEGS)) md) RPOST.
Proof.
intros i j regs mem md HB Hij HiT HSEPS Hend HI HR KO.
pose proof HI as (HJ & HKEEP & HOUT & HLEN).
pose proof HR as ((HK & Hsp & R10 & R13 & R18 & R12) & R8 & R9 & R14 & R15 & R17 & R5 & R16).
pose proof (rcn_blk _ _ _ HI) as (Hp16 & Hp4096 & Hpceil & Hpstk).
pose proof HSTK0 as (Hsp16 & Hstk0 & Hcl & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof alloc_ceiling_val as HAC. pose proof HTXB as (Htx1 & Htx2).
assert (HL8 : NN <= 8192) by (unfold LMAX in HTN; lia).
assert (HAR : AR SEGS B ly1 S1 W mem md) by exact (rcn_ar _ _ _ HI).
pose proof (rcn_canon_len_firstn T i) as HCLi.
assert (Hlo : 0 <= Z.of_nat (length (canon (firstn i T))) <= Z.of_nat i) by lia.
assert (HloN : 0 <= Z.of_nat (length (canon (firstn i T))) <= NN) by lia.
destruct (al_blocks _ _ LAWS _ _ _ _ _ p (NN + 1) HAR HPIN) as (_ & _ & _ & _ & Hpres & _).
rewrite rcn_rq in Hpres.
set (lo := Z.of_nat (length (canon (firstn i T)))) in *.
assert (Hlo' : lo = Z.of_nat (length (canon (firstn i T)))) by reflexivity.
set (E := Eimg (Ereg regs [w64 (p + lo)])).
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr regs r)
  by (intros k r Hk; subst E; apply ew_Eimg_Ereg_nat; exact Hk).
assert (E32 : ew E 32 = w64 (p + lo))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (Usp : bv_unsigned (ew E 2) = sp0 - 32) by (rewrite (EE 2%nat 2%bv eq_refl); exact Hsp).
assert (U32 : bv_unsigned (ew E 32) = p + lo) by (rewrite E32; apply unsigned_lit_small; lia).
assert (HAE : env_agree 32 (Ereg regs [w64 (p + lo)]) E)
  by (subst E; split; [intros k Hk; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (HS : st_ok_pi SEGS VAL E rcn_ss_word
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + K_WORD)) mem (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold rcn_ss_word. apply pa_entry_st_ok_full.
  - apply regs_ok_pin;
    [ apply regs_ok_pin;
      [ apply regs_ok_pin; [apply regs_ok_Eimg_Ereg | intros X; discriminate X | cbn [sv_denot]; exact R17]
      | intros X; discriminate X | cbn [sv_denot]; exact R5]
    | intros X; discriminate X | cbn [sv_denot]; exact R16].
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U32. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). apply (proj1 (Hpres (p + lo + o) ltac:(lia))).
  - cbn [pairwise_disjoint all_disjoint]. tauto.
  - split; [|split; [exact I|]].
    + cbn [f_atoms atoms_ok]. unfold afact_ok, PTR, NOTF; cbn [af_lo af_hi af_al2].
      rewrite Usp, U32, (EE 8%nat 8%bv eq_refl), (EE 9%nat 9%bv eq_refl), (EE 10%nat 10%bv eq_refl),
        (EE 12%nat 12%bv eq_refl), (EE 13%nat 13%bv eq_refl), (EE 14%nat 14%bv eq_refl),
        (EE 18%nat 18%bv eq_refl).
      rewrite R8, R9, R10, R12, R13, R14, R18. unfold w64, NOTW.
      rewrite !unsigned_lit_small by (unfold SHADOW_OFF; lia).
      change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
      assert (Hm16 : (sp0 - 32) mod 16 = 0) by (rewrite Zminus_mod, Hsp16; reflexivity).
      repeat split; try (unfold SB, SHADOW_OFF in * ); try lia.
    + cbn [f_alias alias_ok]. split; [|exact I]. cbn [sv_denot].
      rewrite (EE 10%nat 10%bv eq_refl), (EE 13%nat 13%bv eq_refl), R10, R13, E32. unfold w64.
      rewrite !unsigned_lit_small by lia. rewrite !Z.add_0_r. apply rcn_alu_add. }
assert (SHOK : sh_ok SEGS (SOff 18 0) rcn_sh_word E (mrestrict (w_H W) mem)).
{ unfold rcn_sh_word, sh_ok. apply Forall_cons; [|apply Forall_nil].
  apply (shent_app_of_block SEGS B LAWS ly1 S1 W mem md E (SOff 18 0) 32 (p + lo) p (NN + 1) 0 1 _ HAR HPIN).
  - apply U_atom; [rewrite (EE 18%nat 18%bv eq_refl), R18; reflexivity | unfold SHADOW_OFF; lia].
  - apply U_atom; [exact E32 | lia].
  - lia.
  - lia.
  - rewrite rcn_rq. lia. }
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* a4 = s0: the line ends here *)
  lazymatch type of Hc with context [sv_denot ?Ex _] =>
    assert (G14 : ew Ex 14 = w64 (Z.of_nat j))
      by (rewrite ?ew_ewset_other by lia; rewrite (EE 14%nat 14%bv eq_refl); exact R14);
    assert (G8 : ew Ex 8 = w64 NN)
      by (rewrite ?ew_ewset_other by lia; rewrite (EE 8%nat 8%bv eq_refl); exact R8);
    rewrite branch_eq_U, (U_atom Ex 14 (Z.of_nat j) G14 ltac:(lia)), (U_atom Ex 8 NN G8 ltac:(lia)) in Hc
  end.
  assert (Hjn : (j = length T)%nat) by (apply Z.eqb_eq in Hc; lia). clear Hc.
  assert (HSEPT : forall t b, (i <= t < length T)%nat -> nth_error T t = Some b -> is_sep b = true)
    by (rewrite <- Hjn; exact HSEPS).
  assert (ECAN : canon T = canon (firstn i T))
    by (unfold canon; rewrite (rcn_end_words T i HB ltac:(lia) HSEPT); reflexivity).
  paj_run_to_tok RUNTO HS HJ SHOK Bspan K_FIN.
  { rcn_word_awr lo U32. }
  rcn_word_keep KF1 lo U32.
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ rcn_fkeptall HS ltac:(env_agree_chain HAE)
               ltac:(vm_compute; reflexivity)) as HKEPT.
  cbn [ms_regs restrict mkst] in HKEPT.
  pmkst HS.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rr _ ?mm _) ?dd) _ =>
    assert (HI2 : RINV mm dd (canon T));
    [ rewrite ECAN; apply (rcn_keep_hole _ mem md _ _ lo HI HJ ltac:(rewrite <- Hlo'; lia));
      intros a Ha Hn; rewrite (KF1 a Ha Hn); reflexivity
    | apply (rcn_fin rr mm dd); [exact HI2|] ] end.
  rewrite ECAN. unfold rcn_fregs. repeat match goal with |- _ /\ _ => split end.
  + intros r Hr. rewrite (HKEPT r ltac:(revert Hr; cbv [rcn_kept rcn_fkeptall In]; tauto)). apply HK. exact Hr.
  + unfold spZ. rewrite (HKEPT 2%bv ltac:(cbv; tauto)). exact Hsp.
  + rewrite (HKEPT 10%bv ltac:(cbv; tauto)). exact R10.
  + rewrite (HKEPT 13%bv ltac:(cbv; tauto)). exact R13.
  + rewrite (HKEPT 18%bv ltac:(cbv; tauto)). exact R18.
  + rewrite (HKEPT 12%bv ltac:(cbv; tauto)). exact R12.
- (* a4 <> s0: a word starts at j *)
  lazymatch type of Hc with context [sv_denot ?Ex _] =>
    assert (G14 : ew Ex 14 = w64 (Z.of_nat j))
      by (rewrite ?ew_ewset_other by lia; rewrite (EE 14%nat 14%bv eq_refl); exact R14);
    assert (G8 : ew Ex 8 = w64 NN)
      by (rewrite ?ew_ewset_other by lia; rewrite (EE 8%nat 8%bv eq_refl); exact R8);
    rewrite branch_eq_U, (U_atom Ex 14 (Z.of_nat j) G14 ltac:(lia)), (U_atom Ex 8 NN G8 ltac:(lia)) in Hc
  end.
  assert (Hjn : (j < length T)%nat) by (apply Z.eqb_neq in Hc; lia). clear Hc. clear G14 G8.
  assert (HNSj : forall b, nth_error T j = Some b -> is_sep b = false).
  { intros b Eb. destruct Hend as [Hx | (b' & Eb' & Hb')]; [lia|]. rewrite Eb' in Eb. injection Eb as <-. exact Hb'. }
  (* the length of the word's prefix: i < j once the block already holds a word *)
  assert (Hiltj : lo > 0 -> (i < j)%nat).
  { intros Hl. destruct (Nat.eq_dec i j) as [Eij|]; [|lia]. exfalso.
    destruct HB as [Hi0 | (bb & Ebb & Hbb)].
    - unfold lo in Hl. rewrite Hi0 in Hl. change (firstn 0 T) with (@nil byte) in Hl. cbn in Hl. lia.
    - rewrite Eij in Ebb. rewrite (HNSj bb Ebb) in Hbb. discriminate. }
  paj_run_tok RUN HS HJ SHOK Bspan.
  { rcn_word_awr lo U32. }
  rcn_word_keep KF1 lo U32.
  psrr_branch_tok RUN BR HS SHOK Bspan.
  + (* a3 = 0: the block is empty, no space to store *)
    lazymatch type of Hc with context [sv_denot ?Ex _] =>
      assert (G13 : ew Ex 13 = w64 lo)
        by (rewrite ?ew_ewset_other by lia; rewrite (EE 13%nat 13%bv eq_refl); rewrite R13; reflexivity);
      rewrite branch_eq_U, (U_atom Ex 13 lo G13 ltac:(lia)), U_SLit in Hc
    end.
    change (zcanon 0) with 0 in Hc.
    assert (Hlo0 : lo = 0) by (apply Z.eqb_eq in Hc; lia). clear Hc.
    assert (Hout0 : canon (firstn i T) = []).
    { apply length_zero_iff_nil. unfold lo in Hlo0. lia. }
    paj_run_tok RUN HS HJ SHOK Bspan.
    { rcn_word_awr lo U32. }
    rcn_word_keep KF1b lo U32.
    psrr_branch_tok RUN BR HS SHOK Bspan.
    * (* bgeu taken: impossible, j < |T| *)
      exfalso.
      lazymatch type of Hc with context [sv_denot ?Ex _] =>
        assert (G14 : ew Ex 14 = w64 (Z.of_nat j))
          by (rewrite ?ew_ewset_other by lia; rewrite (EE 14%nat 14%bv eq_refl); exact R14);
        assert (G8 : ew Ex 8 = w64 NN)
          by (rewrite ?ew_ewset_other by lia; rewrite (EE 8%nat 8%bv eq_refl); exact R8);
        rewrite branch_geu_U, (U_atom Ex 14 (Z.of_nat j) G14 ltac:(lia)), (U_atom Ex 8 NN G8 ltac:(lia)) in Hc
      end.
      apply negb_true_iff, Z.ltb_ge in Hc. lia.
    * (* the copy of the word begins *)
      lazymatch type of Hc with context [sv_denot ?Ex _] =>
        assert (G14 : ew Ex 14 = w64 (Z.of_nat j))
          by (rewrite ?ew_ewset_other by lia; rewrite (EE 14%nat 14%bv eq_refl); exact R14);
        assert (G8 : ew Ex 8 = w64 NN)
          by (rewrite ?ew_ewset_other by lia; rewrite (EE 8%nat 8%bv eq_refl); exact R8);
        rewrite branch_geu_U, (U_atom Ex 14 (Z.of_nat j) G14 ltac:(lia)), (U_atom Ex 8 NN G8 ltac:(lia)) in Hc
      end. clear Hc.
      paj_run_to_tok RUNTO HS HJ SHOK Bspan K_COPY.
      { rcn_word_awr lo U32. }
      rcn_word_keep KF2 lo U32.
      pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ rcn_wkeptall HS ltac:(env_agree_chain HAE)
                   ltac:(vm_compute; reflexivity)) as HKEPT.
      cbn [ms_regs restrict mkst] in HKEPT.
      pmkst HS.
      lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rr _ ?mm _) ?dd) _ =>
        assert (HI2 : RINV mm dd (canon (firstn i T)));
        [ apply (rcn_keep_hole _ mem md _ _ lo HI HJ ltac:(rewrite <- Hlo'; lia));
          intros a Ha Hn; rewrite (KF2 a Ha Hn), (KF1b a Ha Hn), (KF1 a Ha Hn); reflexivity
        | apply (rcn_copy (length T - j) j j [] rr mm dd) ] end.
      -- lia.
      -- lia.
      -- cbn [length]. lia.
      -- rewrite Nat.sub_diag. cbn [firstn app]. rewrite Hout0 in HI2. exact HI2.
      -- unfold rcn_cregs, rcn_regs, rcn_fregs. repeat match goal with |- _ /\ _ => split end.
         ++ intros r Hr. rewrite (HKEPT r ltac:(revert Hr; cbv [rcn_kept rcn_wkeptall In]; tauto)).
            apply HK. exact Hr.
         ++ unfold spZ. rewrite (HKEPT 2%bv ltac:(cbv; tauto)). exact Hsp.
         ++ rewrite (HKEPT 10%bv ltac:(cbv; tauto)). exact R10.
         ++ rcn_rreg HS. rcn_off 13%nat lo 0 (eq_trans (EE 13%nat 13%bv eq_refl) R13).
            unfold w64. f_equal. cbn [length]. lia.
         ++ rewrite (HKEPT 18%bv ltac:(cbv; tauto)). exact R18.
         ++ rewrite (HKEPT 12%bv ltac:(cbv; tauto)). exact R12.
         ++ rewrite (HKEPT 8%bv ltac:(cbv; tauto)). exact R8.
         ++ rewrite (HKEPT 9%bv ltac:(cbv; tauto)). exact R9.
         ++ rewrite (HKEPT 14%bv ltac:(cbv; tauto)). exact R14.
         ++ rewrite (HKEPT 15%bv ltac:(cbv; tauto)). exact R15.
         ++ rcn_rreg HS. reflexivity.
         ++ rcn_rreg HS. reflexivity.
         ++ rcn_rreg HS. reflexivity.
         ++ rcn_rreg HS. rcn_t1 (Z.of_nat (length T)) lo (Z.of_nat j) 0
              (eq_trans (EE 8%nat 8%bv eq_refl) R8) (eq_trans (EE 13%nat 13%bv eq_refl) R13)
              (eq_trans (EE 14%nat 14%bv eq_refl) R14).
            unfold w64. f_equal. cbn [length]. lia.
      -- intros t bt Ht Et. lia.
      -- intros k regs2 mem2 md2 Hk HNSk Hsepk HIk HRk.
         apply (rcn_word_KS i j (canon (firstn i T)) [] HB ltac:(lia) eq_refl
                  ltac:(rewrite Hout0; reflexivity) HSEPS HNSj k regs2 mem2 md2 Hk HNSk Hsepk);
         [exact HIk | exact HRk | exact KO].
      -- intros regs2 mem2 md2 HNSk HIk HRk.
         apply (rcn_word_KE i j (canon (firstn i T)) [] HB ltac:(lia) eq_refl
                  ltac:(rewrite Hout0; reflexivity) HSEPS regs2 mem2 md2);
         [intros t bt Ht Et; apply (HNSk t bt); [lia | exact Et] | exact HIk | exact HRk].
  + (* a3 <> 0: one SPACE is stored at p + lo first; the UBSan check 0x898a4 of out + o is decided *)
    lazymatch type of Hc with context [sv_denot ?Ex _] =>
      assert (G13 : ew Ex 13 = w64 lo)
        by (rewrite ?ew_ewset_other by lia; rewrite (EE 13%nat 13%bv eq_refl); rewrite R13; reflexivity);
      rewrite branch_eq_U, (U_atom Ex 13 lo G13 ltac:(lia)), U_SLit in Hc
    end.
    change (zcanon 0) with 0 in Hc.
    assert (Hlo0 : lo > 0) by (apply Z.eqb_neq in Hc; lia). clear Hc.
    assert (Hltj : (i < j)%nat) by (apply Hiltj; exact Hlo0).
    assert (Hout0 : canon (firstn i T) <> []).
    { intros Ec. unfold lo in Hlo0. rewrite Ec in Hlo0. cbn [length] in Hlo0. lia. }
    paj_run_tok RUN HS HJ SHOK Bspan.
    { srr_obls.
      lazymatch goal with |- range_addressable _ (U ?Ex _) _ _ =>
        rewrite (U_atom Ex 18 SHADOW_OFF
          ltac:(rewrite ?ew_ewset_other by lia; rewrite (EE 18%nat 18%bv eq_refl), R18; reflexivity)
          ltac:(unfold SHADOW_OFF; lia));
        rewrite (U_atom Ex 32 (p + lo) ltac:(rewrite ?ew_ewset_other by lia; exact E32) ltac:(lia))
      end.
      apply (range_addressable_sub _ SHADOW_OFF p (NN + 1));
        [ apply (range_addressable_of_block SEGS B LAWS ly1 S1 W _ _ p (NN + 1) p (NN + 1) (proj1 HJ) HPIN);
          rewrite ?rcn_rq; lia | lia | lia]. }
    { rcn_word_awr lo U32. }
    rcn_word_keep KF2 lo U32.
    assert (Hlen0 : Z.of_nat (length (canon (firstn i T))) = lo) by reflexivity.
    psrr_branch_tok RUN BR HS SHOK Bspan.
    * (* bgeu taken: impossible, j < |T| *)
      exfalso.
      lazymatch type of Hc with context [sv_denot ?Ex _] =>
        assert (G14 : ew Ex 14 = w64 (Z.of_nat j))
          by (rewrite ?ew_ewset_other by lia; rewrite (EE 14%nat 14%bv eq_refl); exact R14);
        assert (G8 : ew Ex 8 = w64 NN)
          by (rewrite ?ew_ewset_other by lia; rewrite (EE 8%nat 8%bv eq_refl); exact R8);
        rewrite branch_geu_U, (U_atom Ex 14 (Z.of_nat j) G14 ltac:(lia)), (U_atom Ex 8 NN G8 ltac:(lia)) in Hc
      end.
      apply negb_true_iff, Z.ltb_ge in Hc. lia.
    * (* the copy of the word begins *)
      lazymatch type of Hc with context [sv_denot ?Ex _] =>
        assert (G14 : ew Ex 14 = w64 (Z.of_nat j))
          by (rewrite ?ew_ewset_other by lia; rewrite (EE 14%nat 14%bv eq_refl); exact R14);
        assert (G8 : ew Ex 8 = w64 NN)
          by (rewrite ?ew_ewset_other by lia; rewrite (EE 8%nat 8%bv eq_refl); exact R8);
        rewrite branch_geu_U, (U_atom Ex 14 (Z.of_nat j) G14 ltac:(lia)), (U_atom Ex 8 NN G8 ltac:(lia)) in Hc
      end. clear Hc.
      paj_run_to_tok RUNTO HS HJ SHOK Bspan K_COPY.
      { rcn_word_awr lo U32. }
      rcn_word_keep KF3 lo U32. rcn_word_stored HZ lo U32.
      pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ rcn_wkeptall HS ltac:(env_agree_chain HAE)
                   ltac:(vm_compute; reflexivity)) as HKEPT.
      cbn [ms_regs restrict mkst] in HKEPT.
      pmkst HS.
      lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rr _ ?mm _) ?dd) _ =>
        assert (HI2 : RINV mm dd (canon (firstn i T) ++ [SPACE]));
        [ apply (rcn_store_step _ SPACE mem md _ _ HI HJ);
          [ rewrite Hlen0; intros a Ha Hn;
            rewrite (KF3 a Ha Hn), (KF2 a Ha Hn), (KF1 a Ha Hn); reflexivity
          | rewrite Hlen0; exact HZ
          | rewrite Hlen0; lia ]
        | apply (rcn_copy (length T - j) j j (canon (firstn i T) ++ [SPACE]) rr mm dd) ] end.
      -- lia.
      -- lia.
      -- rewrite length_app. cbn [length]. lia.
      -- rewrite Nat.sub_diag. cbn [firstn]. rewrite app_nil_r. exact HI2.
      -- unfold rcn_cregs, rcn_regs, rcn_fregs. rewrite length_app. cbn [length].
         repeat match goal with |- _ /\ _ => split end.
         ++ intros r Hr. rewrite (HKEPT r ltac:(revert Hr; cbv [rcn_kept rcn_wkeptall In]; tauto)).
            apply HK. exact Hr.
         ++ unfold spZ. rewrite (HKEPT 2%bv ltac:(cbv; tauto)). exact Hsp.
         ++ rewrite (HKEPT 10%bv ltac:(cbv; tauto)). exact R10.
         ++ rcn_rreg HS. rcn_off 13%nat lo 1 (eq_trans (EE 13%nat 13%bv eq_refl) R13).
            unfold w64. f_equal. lia.
         ++ rewrite (HKEPT 18%bv ltac:(cbv; tauto)). exact R18.
         ++ rewrite (HKEPT 12%bv ltac:(cbv; tauto)). exact R12.
         ++ rewrite (HKEPT 8%bv ltac:(cbv; tauto)). exact R8.
         ++ rewrite (HKEPT 9%bv ltac:(cbv; tauto)). exact R9.
         ++ rewrite (HKEPT 14%bv ltac:(cbv; tauto)). exact R14.
         ++ rewrite (HKEPT 15%bv ltac:(cbv; tauto)). exact R15.
         ++ rcn_rreg HS. reflexivity.
         ++ rcn_rreg HS. reflexivity.
         ++ rcn_rreg HS. reflexivity.
         ++ rcn_rreg HS. rcn_t1 (Z.of_nat (length T)) lo (Z.of_nat j) 1
              (eq_trans (EE 8%nat 8%bv eq_refl) R8) (eq_trans (EE 13%nat 13%bv eq_refl) R13)
              (eq_trans (EE 14%nat 14%bv eq_refl) R14).
            unfold w64. f_equal. lia.
      -- intros t bt Ht Et. lia.
      -- intros k regs2 mem2 md2 Hk HNSk Hsepk HIk HRk.
         apply (rcn_word_KS i j (canon (firstn i T)) (canon (firstn i T) ++ [SPACE]) HB ltac:(lia) eq_refl
                  ltac:(destruct (canon (firstn i T)); [exfalso; apply Hout0; reflexivity | reflexivity])
                  HSEPS HNSj k regs2 mem2 md2 Hk HNSk Hsepk);
         [exact HIk | exact HRk | exact KO].
      -- intros regs2 mem2 md2 HNSk HIk HRk.
         apply (rcn_word_KE i j (canon (firstn i T)) (canon (firstn i T) ++ [SPACE]) HB ltac:(lia) eq_refl
                  ltac:(destruct (canon (firstn i T)); [exfalso; apply Hout0; reflexivity | reflexivity])
                  HSEPS regs2 mem2 md2);
         [intros t bt Ht Et; apply (HNSk t bt); [lia | exact Et] | exact HIk | exact HRk].
Qed.

(* The outer loop (0x8983c): one word of the line per turn, with the canonical prefix already written. *)
Lemma rcn_outer : forall (d i : nat) regs mem md,
  (length T - i <= d)%nat -> (i < length T)%nat -> rcn_bndry T i ->
  RINV mem md (canon (firstn i T)) ->
  rcn_regs regs i (Z.of_nat (length (canon (firstn i T)))) ->
  SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + K_OUTER)) mem (seg_rom SEGS)) md) RPOST.
Proof.
induction d as [|d IH]; intros i regs mem md Hd Hi HB HI HR; [lia|].
pose proof HI as (HJ & HKEEP & HOUT & HLEN).
pose proof HR as ((HK & Hsp & R10 & R13 & R18 & R12) & R8 & R9 & R14 & R15 & R17 & R5 & R16).
pose proof (rcn_blk _ _ _ HI) as (Hp16 & Hp4096 & Hpceil & Hpstk).
pose proof HSTK0 as (Hsp16 & Hstk0 & Hcl & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof alloc_ceiling_val as HAC.
assert (HL8 : NN <= 8192) by (unfold LMAX in HTN; lia).
pose proof (rcn_canon_len_firstn T i) as HCLi.
assert (HloN : 0 <= Z.of_nat (length (canon (firstn i T))) <= NN) by lia.
set (lo := Z.of_nat (length (canon (firstn i T)))) in *.
set (E := Eimg (Ereg regs [])).
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr regs r)
  by (intros k r Hk; subst E; apply ew_Eimg_Ereg_nat; exact Hk).
assert (Usp : bv_unsigned (ew E 2) = sp0 - 32) by (rewrite (EE 2%nat 2%bv eq_refl); exact Hsp).
assert (HAE : env_agree 32 (Ereg regs []) E)
  by (subst E; split; [intros k Hk; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (HS : st_ok_pi SEGS VAL E rcn_ss_outer
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + K_OUTER)) mem (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold rcn_ss_outer. apply pa_entry_st_ok_full.
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - cbn [pairwise_disjoint all_disjoint]. tauto.
  - split; [|split; exact I].
    cbn [f_atoms atoms_ok]. unfold afact_ok; cbn [af_lo af_hi af_al2].
    rewrite Usp, (EE 8%nat 8%bv eq_refl), (EE 14%nat 14%bv eq_refl), (EE 18%nat 18%bv eq_refl).
    rewrite R8, R14, R18. unfold w64. rewrite !unsigned_lit_small by (unfold SHADOW_OFF; lia).
    change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
    assert (Hm16 : (sp0 - 32) mod 16 = 0) by (rewrite Zminus_mod, Hsp16; reflexivity).
    repeat split; try (unfold SB, SHADOW_OFF in * ); try lia. }
assert (SHOK : sh_ok SEGS (SOff 18 0) (@nil shent) E (mrestrict (w_H W) mem)) by apply Forall_nil.
paj_run_tok RUN HS HJ SHOK Bspan.
{ awr_ok_tac. }
rcn_keepf KF1.
assert (KW : forall regs' mem' md',
  RINV mem' md' (canon (firstn i T)) -> rcn_regs regs' i lo -> getr regs' 6 = w64 NN ->
  SRr SEGS W (mkCfg (mkst regs' (Z_to_bv 64 (BASE + K_SKIP)) mem' (seg_rom SEGS)) md') RPOST).
{ intros regs' mem' md' HI' HR' R6'.
  apply (rcn_skip (length T - i) i regs' mem' md' (canon (firstn i T)));
  [lia | lia | unfold lo in HloN; lia | exact HI' | exact HR' | exact R6' |].
  intros j regs2 mem2 md2 Hj HSEPS Hend HI2 HR2 R62.
  apply (rcn_word i j regs2 mem2 md2 HB ltac:(lia) Hi HSEPS Hend HI2 HR2).
  intros i2 regs3 mem3 md3 Hi2 Hii2 HB2 HI3 HR3.
  apply (IH i2 regs3 mem3 md3); [lia | exact Hi2 | exact HB2 | exact HI3 | exact HR3]. }
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* bltu taken: t1 keeps s0 *)
  paj_run_to_tok RUNTO HS HJ SHOK Bspan K_SKIP.
  { awr_ok_tac. }
  rcn_keepf KF2.
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ rcn_okeptall HS ltac:(env_agree_chain HAE)
               ltac:(vm_compute; reflexivity)) as HKEPT.
  cbn [ms_regs restrict mkst] in HKEPT.
  pmkst HS.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rr _ ?mm _) ?dd) _ =>
    assert (HI2 : RINV mm dd (canon (firstn i T)));
    [ apply (rcn_keep_step _ mem md _ _ HI HJ); intros a Ha;
      rewrite (KF2 a Ha ltac:(cbv beta; tauto)), (KF1 a Ha ltac:(cbv beta; tauto)); reflexivity
    | apply (KW rr mm dd); [exact HI2 | | ] ] end.
  + unfold rcn_regs, rcn_fregs. repeat match goal with |- _ /\ _ => split end.
    * intros r Hr. rewrite (HKEPT r ltac:(revert Hr; cbv [rcn_kept rcn_okeptall In]; tauto)). apply HK. exact Hr.
    * unfold spZ. rewrite (HKEPT 2%bv ltac:(cbv; tauto)). exact Hsp.
    * rewrite (HKEPT 10%bv ltac:(cbv; tauto)). exact R10.
    * rewrite (HKEPT 13%bv ltac:(cbv; tauto)). exact R13.
    * rewrite (HKEPT 18%bv ltac:(cbv; tauto)). exact R18.
    * rewrite (HKEPT 12%bv ltac:(cbv; tauto)). exact R12.
    * rewrite (HKEPT 8%bv ltac:(cbv; tauto)). exact R8.
    * rewrite (HKEPT 9%bv ltac:(cbv; tauto)). exact R9.
    * rewrite (HKEPT 14%bv ltac:(cbv; tauto)). exact R14.
    * rewrite (HKEPT 15%bv ltac:(cbv; tauto)). exact R15.
    * rewrite (HKEPT 17%bv ltac:(cbv; tauto)). exact R17.
    * rewrite (HKEPT 5%bv ltac:(cbv; tauto)). exact R5.
    * rewrite (HKEPT 16%bv ltac:(cbv; tauto)). exact R16.
  + rcn_rreg HS. rcn_off 8%nat (Z.of_nat (length T)) 0 (eq_trans (EE 8%nat 8%bv eq_refl) R8). unfold w64. f_equal. lia.
- (* bltu not taken: t1 takes a4 + 1, which is s0 *)
  lazymatch type of Hc with context [sv_denot ?Ex _] =>
    assert (G14 : ew Ex 14 = w64 (Z.of_nat i))
      by (rewrite ?ew_ewset_other by lia; rewrite (EE 14%nat 14%bv eq_refl); exact R14);
    assert (G8 : ew Ex 8 = w64 NN)
      by (rewrite ?ew_ewset_other by lia; rewrite (EE 8%nat 8%bv eq_refl); exact R8);
    rewrite branch_ltu_U, (U_atom_off Ex 14 (Z.of_nat i) 1 G14 ltac:(lia) ltac:(lia)),
      (U_atom Ex 8 NN G8 ltac:(lia)) in Hc
  end.
  assert (Hsi : (S i = length T)%nat) by (apply Z.ltb_ge in Hc; lia). clear Hc.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan K_SKIP.
  { awr_ok_tac. }
  rcn_keepf KF2.
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ rcn_okeptall HS ltac:(env_agree_chain HAE)
               ltac:(vm_compute; reflexivity)) as HKEPT.
  cbn [ms_regs restrict mkst] in HKEPT.
  pmkst HS.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rr _ ?mm _) ?dd) _ =>
    assert (HI2 : RINV mm dd (canon (firstn i T)));
    [ apply (rcn_keep_step _ mem md _ _ HI HJ); intros a Ha;
      rewrite (KF2 a Ha ltac:(cbv beta; tauto)), (KF1 a Ha ltac:(cbv beta; tauto)); reflexivity
    | apply (KW rr mm dd); [exact HI2 | | ] ] end.
  + unfold rcn_regs, rcn_fregs. repeat match goal with |- _ /\ _ => split end.
    * intros r Hr. rewrite (HKEPT r ltac:(revert Hr; cbv [rcn_kept rcn_okeptall In]; tauto)). apply HK. exact Hr.
    * unfold spZ. rewrite (HKEPT 2%bv ltac:(cbv; tauto)). exact Hsp.
    * rewrite (HKEPT 10%bv ltac:(cbv; tauto)). exact R10.
    * rewrite (HKEPT 13%bv ltac:(cbv; tauto)). exact R13.
    * rewrite (HKEPT 18%bv ltac:(cbv; tauto)). exact R18.
    * rewrite (HKEPT 12%bv ltac:(cbv; tauto)). exact R12.
    * rewrite (HKEPT 8%bv ltac:(cbv; tauto)). exact R8.
    * rewrite (HKEPT 9%bv ltac:(cbv; tauto)). exact R9.
    * rewrite (HKEPT 14%bv ltac:(cbv; tauto)). exact R14.
    * rewrite (HKEPT 15%bv ltac:(cbv; tauto)). exact R15.
    * rewrite (HKEPT 17%bv ltac:(cbv; tauto)). exact R17.
    * rewrite (HKEPT 5%bv ltac:(cbv; tauto)). exact R5.
    * rewrite (HKEPT 16%bv ltac:(cbv; tauto)). exact R16.
  + rcn_rreg HS. rcn_off 14%nat (Z.of_nat i) 1 (eq_trans (EE 14%nat 14%bv eq_refl) R14).
    unfold w64. f_equal. lia.
Qed.

(* The return of the xmalloc call (0x89818): the empty-line check, and the set-up of the outer loop (o = i = 0,
   a2 = ~out, a5 = ~text, a6 = (text != 0), decided 1 by text >= 4096). *)
Lemma rcn_mret : forall md regs,
  ajournal SEGS B REC_CANONICAL_STK sp0 [] ly0 S0 W0 mem0 md0 [] ly1 S1 W memM md EV_REC_CANONICAL ->
  (forall r, In r rcn_kept -> getr regs r = getr regs0 r) -> spZ regs = sp0 - 32 ->
  getr regs 10 = w64 p -> getr regs 8 = w64 NN -> getr regs 9 = w64 text -> getr regs 18 = w64 SHADOW_OFF ->
  SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + K_MALLOCRET)) memM (seg_rom SEGS)) md) RPOST.
Proof.
intros md regs HJM HK Hsp R10 R8 R9 R18.
assert (HI : RINV memM md []).
{ split; [exact HJM|]. split; [intros a _ _; reflexivity|].
  split; [intros i Hi; cbn [length] in Hi; lia | cbn [length]; lia]. }
pose proof HI as (HJ & HKEEP & HOUT & HLEN).
pose proof (rcn_blk _ _ _ HI) as (Hp16 & Hp4096 & Hpceil & Hpstk).
pose proof HSTK0 as (Hsp16 & Hstk0 & Hcl & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof alloc_ceiling_val as HAC. pose proof HTXB as (Htx1 & Htx2).
assert (HL8 : NN <= 8192) by (unfold LMAX in HTN; lia).
set (E := Eimg (Ereg regs [])).
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr regs r)
  by (intros k r Hk; subst E; apply ew_Eimg_Ereg_nat; exact Hk).
assert (Usp : bv_unsigned (ew E 2) = sp0 - 32) by (rewrite (EE 2%nat 2%bv eq_refl); exact Hsp).
assert (HAE : env_agree 32 (Ereg regs []) E)
  by (subst E; split; [intros k Hk; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (HS : st_ok_pi SEGS VAL E rcn_ss_mret
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + K_MALLOCRET)) memM (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold rcn_ss_mret. apply pa_entry_st_ok_full.
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - cbn [pairwise_disjoint all_disjoint]. tauto.
  - split; [|split; exact I].
    cbn [f_atoms atoms_ok]. unfold afact_ok, PTR; cbn [af_lo af_hi af_al2].
    rewrite Usp, (EE 8%nat 8%bv eq_refl), (EE 9%nat 9%bv eq_refl), (EE 10%nat 10%bv eq_refl),
      (EE 18%nat 18%bv eq_refl).
    rewrite R8, R9, R10, R18. unfold w64. rewrite !unsigned_lit_small by (unfold SHADOW_OFF; lia).
    change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
    assert (Hm16 : (sp0 - 32) mod 16 = 0) by (rewrite Zminus_mod, Hsp16; reflexivity).
    repeat split; try (unfold SB, SHADOW_OFF in * ); try lia. }
assert (SHOK : sh_ok SEGS (SOff 18 0) (@nil shent) E (mrestrict (w_H W) memM)) by apply Forall_nil.
(* 0x89818 .. 0x8981c: a1 = out, `beqz s0` *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ awr_ok_tac. }
rcn_keepf KF1.
psrr_branch_tok RUN BR HS SHOK Bspan.
+ (* the line is empty: straight to the store of the terminator, a1 = out *)
  lazymatch type of Hc with context [sv_denot ?Ex _] =>
    assert (G8 : ew Ex 8 = w64 NN)
      by (rewrite ?ew_ewset_other by lia; rewrite (EE 8%nat 8%bv eq_refl); exact R8);
    rewrite branch_eq_U, (U_atom Ex 8 NN G8 ltac:(lia)), U_SLit in Hc
  end.
  change (zcanon 0) with 0 in Hc.
  assert (HNN0 : NN = 0) by (apply Z.eqb_eq in Hc; lia). clear Hc.
  assert (HT0 : T = []) by (apply length_zero_iff_nil; lia).
  assert (HCT : canon T = []) by (rewrite HT0; reflexivity).
  paj_run_to_tok RUNTO HS HJ SHOK Bspan K_FIN0.
  { awr_ok_tac. }
  rcn_keepf KF2.
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ rcn_mkeptall HS ltac:(env_agree_chain HAE)
               ltac:(vm_compute; reflexivity)) as HKEPT.
  cbn [ms_regs restrict mkst] in HKEPT.
  pmkst HS.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rr _ ?mm _) ?dd) _ =>
    assert (HI2 : RINV mm dd (canon T));
    [ rewrite HCT; apply (rcn_keep_step _ memM md _ _ HI HJ); intros a Ha;
      rewrite (KF2 a Ha ltac:(cbv beta; tauto)), (KF1 a Ha ltac:(cbv beta; tauto)); reflexivity
    | apply (rcn_fin0 rr mm dd); [exact HI2|] ] end.
  rewrite HCT. cbn [length]. change (Z.of_nat 0) with 0.
  unfold rcn_f0regs. repeat match goal with |- _ /\ _ => split end.
  * intros r Hr. rewrite (HKEPT r ltac:(revert Hr; cbv [rcn_kept rcn_mkeptall In]; tauto)). apply HK. exact Hr.
  * unfold spZ. rewrite (HKEPT 2%bv ltac:(cbv; tauto)). exact Hsp.
  * rewrite (HKEPT 10%bv ltac:(cbv; tauto)). exact R10.
  * rcn_rreg HS. rcn_off 10%nat p 0 (eq_trans (EE 10%nat 10%bv eq_refl) R10). reflexivity.
  * rewrite (HKEPT 18%bv ltac:(cbv; tauto)). exact R18.
+ (* the line has at least one byte: the outer loop *)
  lazymatch type of Hc with context [sv_denot ?Ex _] =>
    assert (G8 : ew Ex 8 = w64 NN)
      by (rewrite ?ew_ewset_other by lia; rewrite (EE 8%nat 8%bv eq_refl); exact R8);
    rewrite branch_eq_U, (U_atom Ex 8 NN G8 ltac:(lia)), U_SLit in Hc
  end.
  change (zcanon 0) with 0 in Hc.
  assert (HNN1 : 0 < NN) by (apply Z.eqb_neq in Hc; lia). clear Hc.
  assert (HC0 : canon (firstn 0 T) = []) by reflexivity.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan K_OUTER.
  { awr_ok_tac. }
  rcn_keepf KF2.
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ rcn_mkeptall HS ltac:(env_agree_chain HAE)
               ltac:(vm_compute; reflexivity)) as HKEPT.
  cbn [ms_regs restrict mkst] in HKEPT.
  pmkst HS.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rr _ ?mm _) ?dd) _ =>
    assert (HI2 : RINV mm dd (canon (firstn 0 T)));
    [ rewrite HC0; apply (rcn_keep_step _ memM md _ _ HI HJ); intros a Ha;
      rewrite (KF2 a Ha ltac:(cbv beta; tauto)), (KF1 a Ha ltac:(cbv beta; tauto)); reflexivity
    | apply (rcn_outer (length T) 0 rr mm dd) ] end.
  * lia.
  * lia.
  * left. reflexivity.
  * exact HI2.
  * rewrite HC0. cbn [length]. change (Z.of_nat 0) with 0.
    unfold rcn_regs, rcn_fregs. repeat match goal with |- _ /\ _ => split end.
    -- intros r Hr. rewrite (HKEPT r ltac:(revert Hr; cbv [rcn_kept rcn_mkeptall In]; tauto)). apply HK. exact Hr.
    -- unfold spZ. rewrite (HKEPT 2%bv ltac:(cbv; tauto)). exact Hsp.
    -- rewrite (HKEPT 10%bv ltac:(cbv; tauto)). exact R10.
    -- rcn_rreg HS. reflexivity.
    -- rewrite (HKEPT 18%bv ltac:(cbv; tauto)). exact R18.
    -- rcn_rreg HS. rcn_not 10%nat p (eq_trans (EE 10%nat 10%bv eq_refl) R10). reflexivity.
    -- rewrite (HKEPT 8%bv ltac:(cbv; tauto)). exact R8.
    -- rewrite (HKEPT 9%bv ltac:(cbv; tauto)). exact R9.
    -- rcn_rreg HS. reflexivity.
    -- rcn_rreg HS. rcn_not 9%nat text (eq_trans (EE 9%nat 9%bv eq_refl) R9). reflexivity.
    -- rcn_rreg HS. reflexivity.
    -- rcn_rreg HS. reflexivity.
    -- rcn_rreg HS. reflexivity.
Qed.

End R.

(* ---------------------------------------------------------------- *)
(* The entry walk: the frame, the shadow base from the GOT, the xmalloc call, and the loops. *)

Lemma rcn_not_inFP_nil : forall a, ~ inFP [] a.
Proof. intros a (r & Hr & _). destruct Hr. Qed.

(* the model after a symbolic run, named (as clear_md in Section R) *)
Local Ltac rcn_clear_md := repeat match goal with |- context [with_vm_backing (m_vm_lazy ?m) ?x ?m] =>
  let mdv := fresh "mdv" in set (mdv := with_vm_backing (m_vm_lazy m) x m) in *; clearbody mdv end.

(* a register index is one the callee keeps (YG0d.v acallee_saved), for a concrete register *)
Local Ltac rcn_cs := unfold acallee_saved;
  repeat match goal with |- context [bv_unsigned ?x] =>
    let v := eval vm_compute in (bv_unsigned x) in change (bv_unsigned x) with v end; lia.

Theorem trec_canonical_spec_holds : trec_canonical_spec B MT.
Proof.
unfold trec_canonical_spec.
intros ly S W regs mem md ch text T HPRE HROD H10 Htx H11 HBLK HSTR HLM HEV HLIVE HMOK.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof alloc_ceiling_val as HAC.
assert (HRS : REC_CANONICAL_STK = 16432) by reflexivity.
assert (Has : ASTACK = 16384) by reflexivity.
assert (HXS : XMALLOC_STK = 16400) by reflexivity.
pose proof (@pa_B_ok _ _ PI) as HBASE. pose proof (pa_base_lo (L := cmd_listing)) as HBLO.
set (NN := Z.of_nat (length T)) in *.
assert (HNN : 0 <= NN) by (unfold NN; lia).
(* the line: its bytes, its length, and the live block it lies in *)
assert (HTB : abytes_atR (rdW W mem) text T) by exact (rcn_bytes_prefix _ _ _ _ (proj1 HSTR)).
assert (HTN : NN <= LMAX) by lia.
assert (HL8 : NN <= 8192) by (unfold LMAX in HTN; lia).
destruct HBLK as (tb & tm & Htin & Htb1 & Htb2).
destruct (al_blocks _ _ LAWS _ _ _ _ _ tb tm HAR Htin) as (_ & Htb4096 & Htbceil & _ & _ & _ & Htm).
pose proof (req_size_pos tm (proj1 Htm)) as [Htq1 Htq2].
pose proof (ajournal_init SEGS B REC_CANONICAL_STK [] ly S W regs mem md ch HPRE) as HJ0.
(* the entry state *)
destruct (al_const _ _ LAWS _ _ _ _ _ HAR) as (Kcell & _ & Kgot & _).
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot. rewrite (pal_cell B TL) in Kcell.
set (E := Eimg (Ereg regs [w64 SB])).
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
  by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E32 : ew E 32 = w64 SB)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E241 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0)))
  by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E253 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12)))
  by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
pose proof (pa_val_range (A_OBJ 0)) as Rg0. pose proof (pa_val_range (A_OBJ 12)) as Rg12.
assert (U241 : bv_unsigned (ew E (A_OBJ 0)) = VAL (A_OBJ 0)) by (rewrite E241; apply unsigned_lit_small; lia).
assert (U253 : bv_unsigned (ew E (A_OBJ 12)) = VAL (A_OBJ 12)) by (rewrite E253; apply unsigned_lit_small; lia).
pose proof (pa_obj_img 12 ltac:(lia)) as HcellR. pose proof (pa_obj_img 0 ltac:(lia)) as HgotR.
pose proof (pal_got_cell B TL) as HgcD.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
assert (HS : st_ok_pi SEGS VAL E rcn_ss_entry
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + K_ENTRY)) mem (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold rcn_ss_entry. apply pa_entry_st_ok_full.
  - subst E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - unfold stack_region, got_regionP, bcell_regionP.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    + rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply Hpres. rewrite HRS. lia.
    + rewrite U241. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
        [cbn [sv_denot]; rewrite E253, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS _ _ _ _ Kgot).
    + rewrite U253. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 (SOff 32 0) SB);
        [cbn [sv_denot]; rewrite E32, Z.add_0_r; unfold w64; rewrite unsigned_lit_small by (unfold SB; lia);
         reflexivity | unfold SB; cbn; lia | cbn; lia |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS _ _ _ _ Kcell).
  - apply pairwise_disjoint_of_extents. unfold stack_region, got_regionP, bcell_regionP, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Usp, U241, U253.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
  - split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, E32. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia).
    change (2 ^ 4) with 16. rewrite Z.pow_0_r, Z.mod_1_r.
    repeat split; try lia; exact Hal16. }
assert (SHOK : sh_ok SEGS (SOff 32 0) (@nil shent) E (mrestrict (w_H W) mem)) by apply Forall_nil.
assert (HAE : env_agree 32 (Ereg regs [w64 SB]) E)
  by (subst E; split; [intros k Hk; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
pose proof HJ0 as HJI.
unfold cfg_at. change (w64 (BASE + AF_rec_canonical)) with (Z_to_bv 64 (BASE + K_ENTRY)).
(* 0x897e8 .. 0x89814: the frame, the shadow base, the size, and the xmalloc call *)
paj_run_tok RUN HS HJ0 SHOK Bspan.
{ awr_ok_tac; exact Usp. }
lazymatch goal with Hfr : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ =>
pose proof (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun a => spZ regs - 32 <= a < spZ regs) Hfr
  ltac:(intros bq wlo whi aq Hin Hrr; vm_compute in Hin;
        repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr;
                                             rewrite ?Usp, ?U241, ?U253 in Hrr; lia|]); destruct Hin)) as KE1 end.
rcn_clear_md.
(* the frame the prologue wrote, and the registers at the call *)
lazymatch type of HS with
| st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msx) =>
  let r := eval vm_compute in (nth 0 (ss_mem ssx) got_regionP) in
  pose proof (st_ok_pi_region_nth Ex ssx (restrict (w_H W) msx) 0 r HS ltac:(vm_compute; reflexivity)) as HRg;
  cbn [ms_mem restrict mkst] in HRg
| st_ok _ ?Ex ?ssx (restrict _ ?msx) =>
  let r := eval vm_compute in (nth 0 (ss_mem ssx) got_regionP) in
  pose proof (st_ok_region_nth Ex ssx (restrict (w_H W) msx) 0 r HS ltac:(vm_compute; reflexivity)) as HRg;
  cbn [ms_mem restrict mkst] in HRg
end.
assert (HQ18 : rdword (rdW W (ms_mem ms)) (spZ regs - 32) = Some (bv_unsigned (getr regs 18))).
{ apply (rdword_of_val_mem SEGS).
  - replace (spZ regs - 32) with (spZ regs + (-32)) by lia.
    replace (bv_unsigned (getr regs 18)) with
      (bv_unsigned (sv_denot E (SOff 18 0)) mod 2 ^ (8 * Z.of_N 8))
      by (cbn [sv_denot]; rewrite (EE 18%nat 18%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
          change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); apply Z.mod_small; apply u64_range).
    exact (field_of_region_any E _ 2 (spZ regs) _ _ _ _ _ (-32) 8%N (SOff 18 0) HRg Usp
             ltac:(cbn; tauto) ltac:(cbn; lia)).
  - apply u64_range. }
assert (HQ9 : rdword (rdW W (ms_mem ms)) (spZ regs - 24) = Some (bv_unsigned (getr regs 9))).
{ apply (rdword_of_val_mem SEGS).
  - replace (spZ regs - 24) with (spZ regs + (-24)) by lia.
    replace (bv_unsigned (getr regs 9)) with
      (bv_unsigned (sv_denot E (SOff 9 0)) mod 2 ^ (8 * Z.of_N 8))
      by (cbn [sv_denot]; rewrite (EE 9%nat 9%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
          change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); apply Z.mod_small; apply u64_range).
    exact (field_of_region_any E _ 2 (spZ regs) _ _ _ _ _ (-24) 8%N (SOff 9 0) HRg Usp
             ltac:(cbn; tauto) ltac:(cbn; lia)).
  - apply u64_range. }
assert (HQ8 : rdword (rdW W (ms_mem ms)) (spZ regs - 16) = Some (bv_unsigned (getr regs 8))).
{ apply (rdword_of_val_mem SEGS).
  - replace (spZ regs - 16) with (spZ regs + (-16)) by lia.
    replace (bv_unsigned (getr regs 8)) with
      (bv_unsigned (sv_denot E (SOff 8 0)) mod 2 ^ (8 * Z.of_N 8))
      by (cbn [sv_denot]; rewrite (EE 8%nat 8%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
          change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); apply Z.mod_small; apply u64_range).
    exact (field_of_region_any E _ 2 (spZ regs) _ _ _ _ _ (-16) 8%N (SOff 8 0) HRg Usp
             ltac:(cbn; tauto) ltac:(cbn; lia)).
  - apply u64_range. }
assert (HQ1 : rdword (rdW W (ms_mem ms)) (spZ regs - 8) = Some (raZ regs)).
{ apply (rdword_of_val_mem SEGS).
  - replace (spZ regs - 8) with (spZ regs + (-8)) by lia.
    replace (raZ regs) with (bv_unsigned (sv_denot E (SOff 1 0)) mod 2 ^ (8 * Z.of_N 8))
      by (cbn [sv_denot]; rewrite (EE 1%nat 1%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
          change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); unfold raZ; apply Z.mod_small; apply u64_range).
    exact (field_of_region_any E _ 2 (spZ regs) _ _ _ _ _ (-8) 8%N (SOff 1 0) HRg Usp
             ltac:(cbn; tauto) ltac:(cbn; lia)).
  - unfold raZ. apply u64_range. }
pmkst HS.
prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3.
prreg HS (4%bv : bv 5) P4. prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9.
prreg HS (10%bv : bv 5) P10. prreg HS (18%bv : bv 5) P18.
(* the call target: xmalloc's entry *)
rewrite (HSIG CS_xmalloc ltac:(vm_compute; tauto)).
replace (VAL A_TEXT + cmd_af CS_xmalloc) with (BASE + AF_xmalloc) by (unfold cmd_af, AF_xmalloc; vm_compute; reflexivity).
assert (Q1 : getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + K_MALLOCRET)) by (rewrite P1; reflexivity).
assert (Q2 : spZ (ms_regs ms) = spZ regs + -32)
  by (unfold spZ at 1; rewrite P2, Usp; apply unsigned_lit_small; lia).
assert (Q3 : getr (ms_regs ms) 3 = w64 (as_gp B)) by (rewrite P3, (EE 3%nat 3%bv eq_refl); exact Hgp).
assert (Q4 : getr (ms_regs ms) 4 = w64 (as_tp B)) by (rewrite P4, (EE 4%nat 4%bv eq_refl); exact Htp).
assert (Q8 : getr (ms_regs ms) 8 = w64 NN)
  by (rewrite P8, (EE 11%nat 11%bv eq_refl); exact H11).
assert (Q9 : getr (ms_regs ms) 9 = w64 text) by (rewrite P9, (EE 10%nat 10%bv eq_refl); exact H10).
assert (Q18 : getr (ms_regs ms) 18 = w64 SHADOW_OFF) by (rewrite P18, E32; reflexivity).
assert (Q10 : getr (ms_regs ms) 10 = w64 (NN + 1)).
{ rewrite P10. rewrite (EE 11%nat 11%bv eq_refl), H11. unfold w64.
  rewrite unsigned_lit_small by lia. reflexivity. }
assert (HraT : YK0s.ret_ok (getr (ms_regs ms) 1))
  by (rewrite Q1; apply ret_ok_codeptr_v; [unfold K_MALLOCRET; lia | reflexivity]).
assert (Hra4T : 4096 <= bv_unsigned (getr (ms_regs ms) 1))
  by (rewrite Q1; rewrite unsigned_lit_small; unfold K_MALLOCRET; lia).
first [ pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ rcn_kept HS ltac:(env_agree_chain HAE)
                     ltac:(vm_compute; reflexivity)) as HKEPT
      | pose proof (regs_kept_of_st_ok SEGS _ _ _ regs _ rcn_kept HS ltac:(env_agree_chain HAE)
                     ltac:(vm_compute; reflexivity)) as HKEPT ].
cbn [ms_regs restrict mkst] in HKEPT.
assert (Q2' : spZ (ms_regs ms) = spZ regs - 32) by lia.
rename HJ0 into HJT.
(* xmalloc's frame chain: s0 holds len, at most LMAX and so below alloc_ceiling (achain_low) *)
assert (Hs0 : achain ly (rdW W (ms_mem ms)) (spZ regs + -32) (s0Z (ms_regs ms)) []).
{ apply achain_low. unfold s0Z. rewrite Q8. unfold w64. rewrite unsigned_lit_small by lia. lia. }
assert (Hn : 0 <= NN + 1 < MALLOC_MAX) by (unfold MALLOC_MAX; lia).
assert (HEVc : st_nev S + EV_XMALLOC <= EV_MAX) by exact HEV.
assert (HLX : LIVE_XMALLOC (NN + 1) = NN + 1) by (unfold LIVE_XMALLOC; lia).
assert (HLIVEc : blocks_bytes S + LIVE_XMALLOC (NN + 1) <= LIVE_MAX).
{ rewrite HLX. unfold LIVE_REC_CANONICAL in HLIVE. fold NN in HLIVE. lia. }
assert (HMOKc : mo_ok MT S (XM_XMALLOC MT (NN + 1))) by exact HMOK.
(* the xmalloc call of len + 1 bytes *)
eapply SRr_bind.
{ eapply (cl_callS B LAWS W (ms_regs ms) (ms_mem ms) _ REC_CANONICAL_STK (spZ regs) [] ly S W mem md [] ly S _ _
    XMALLOC_STK [] EV_XMALLOC (-32) (getr (ms_regs ms) 1) []
    (fun ly2 S2 W2 regs2 mem2 md2 => exists q : Z,
      getr regs2 10 = w64 q /\ 4096 <= q < 2 ^ 64 /\
      Permutation (ablocks B ly2 S2) ((q, LIVE_XMALLOC (NN + 1)) :: ablocks B ly S) /\
      Forall (fun qk => iv_apart q (LIVE_XMALLOC (NN + 1)) (fst qk) (snd qk)) (ablocks B ly S) /\
      in_blockA (ablocks B ly2 S2) q (LIVE_XMALLOC (NN + 1)) /\
      blocks_bytes S2 <= blocks_bytes S + LIVE_XMALLOC (NN + 1) /\
      mo_le MT S S2 (XM_XMALLOC MT (NN + 1))));
  [ exact HJT
  | exact Q2 | reflexivity | lia | rewrite HXS; lia | rewrite HRS, HXS; lia
  | exact Q3 | exact Q4 | reflexivity | exact HraT | exact Hra4T | exact Hs0
  | | intros x Hx; exfalso; exact (rcn_not_inFP_nil x Hx) ].
  intros HPRE1.
  exact (HXMALLOC fx ly S W (ms_regs ms) (ms_mem ms) _ [] (NN + 1) HPRE1 Q10 Hn HEVc HLIVEc HMOKc). }
cbv beta. intros W2 c2 Hwle2 (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJc2 & HP2 & q & Hq10 & Hq4096 & HPm
  & HAPn & HINBn & HBB2 & MLE).
rewrite Q1.
rcn_clear_md.
rewrite HLX in HPm, HAPn, HBB2.
assert (HJ2E : ajournal SEGS B REC_CANONICAL_STK (spZ regs) [] ly S W mem md [] ly2 S2 W2 mem2 md2 EV_REC_CANONICAL)
  by exact HJ2.
assert (HAR2 : AR SEGS B ly2 S2 W2 mem2 md2) by exact (proj1 HJ2).
pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
pose proof HJc2 as (_ & _ & _ & _ & _ & _ & _ & _ & F1c & _).
(* the line and the fresh block, at the state the call returned *)
assert (Htin2 : In (tb, tm) (ablocks B ly2 S2))
  by (eapply Permutation_in; [apply Permutation_sym; exact HPm | right; exact Htin]).
assert (HPINB : In (q, NN + 1) (ablocks B ly2 S2))
  by (eapply Permutation_in; [apply Permutation_sym; exact HPm | left; reflexivity]).
assert (HNIN : ~ In (q, NN + 1) (ablocks B ly S)).
{ intros Hin. pose proof (proj1 (Forall_forall _ _) HAPn _ Hin) as Hap. cbn [fst snd] in Hap.
  unfold iv_apart in Hap. lia. }
assert (HSEPB : q + NN + 1 <= text \/ text + NN <= q).
{ pose proof (proj1 (Forall_forall _ _) HAPn _ Htin) as Hap. cbn [fst snd] in Hap.
  unfold iv_apart in Hap. lia. }
assert (HAPART : Forall (fun qk => iv_apart q (LIVE_REC_CANONICAL T) (fst qk) (snd qk)) (ablocks B ly S))
  by (unfold LIVE_REC_CANONICAL; fold NN; exact HAPn).
assert (HPERM : Permutation (ablocks B ly2 S2) ((q, LIVE_REC_CANONICAL T) :: ablocks B ly S))
  by (unfold LIVE_REC_CANONICAL; fold NN; exact HPm).
assert (HBB : blocks_bytes S2 <= blocks_bytes S + LIVE_REC_CANONICAL T)
  by (unfold LIVE_REC_CANONICAL; fold NN; exact HBB2).
assert (HTXTM : abytes_atR (rdW W2 mem2) text T).
{ apply (rcn_bytes_ext (rdW W mem)); [|exact HTB]. intros i Hi.
  replace (text + i) with (tb + (text + i - tb)) by lia.
  apply (F2 tb tm (text + i - tb) Htin Htin2); [lia | apply rcn_not_inFP_nil]. }
assert (HTADDR : forall mem' md', AR SEGS B ly2 S2 W2 mem' md' ->
  range_addressable (rdW W2 mem') SHADOW_OFF text NN).
{ intros mem' md' HAR'.
  apply (range_addressable_of_block SEGS B LAWS ly2 S2 W2 mem' md' tb tm text NN HAR' Htin2); lia. }
(* the frame, across the call: xmalloc's journal keeps every stack byte above its own window *)
assert (HSVa : forall a v, spZ regs - 32 <= a <= spZ regs - 8 ->
  rdword (rdW W (ms_mem ms)) a = Some v -> rdword (rdW W2 mem2) a = Some v).
{ intros a v Ha Hv. rewrite (rdword_ext (rdW W (ms_mem ms)) (rdW W2 mem2)); [exact Hv|].
  intros i Hi. apply F1c; [lia | rewrite HXS; lia | apply rcn_not_inFP_nil]. }
(* the registers the call preserved *)
assert (RP : forall (r : bv 5), acallee_saved (bv_unsigned r) -> getr regs2 r = getr (ms_regs ms) r).
{ intros r Hr. rewrite <- (Z_to_bv_bv_unsigned 5 r). rewrite (HP2 (bv_unsigned r) Hr).
  rewrite Z_to_bv_bv_unsigned. reflexivity. }
assert (RK : forall r, In r rcn_kept -> getr regs2 r = getr regs r).
{ intros r Hr. rewrite (RP r ltac:(revert Hr; cbv [rcn_kept In]; unfold acallee_saved;
    intros [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]; rcn_cs)).
  exact (HKEPT r Hr). }
assert (RS2 : spZ regs2 = spZ regs - 32) by (unfold spZ; rewrite (RP 2%bv ltac:(rcn_cs)); exact Q2').
assert (R8 : getr regs2 8 = w64 NN) by (rewrite (RP 8%bv ltac:(rcn_cs)); exact Q8).
assert (R9 : getr regs2 9 = w64 text) by (rewrite (RP 9%bv ltac:(rcn_cs)); exact Q9).
assert (R18 : getr regs2 18 = w64 SHADOW_OFF) by (rewrite (RP 18%bv ltac:(rcn_cs)); exact Q18).
assert (HMLE : mo_le MT S S2 (XM_REC_CANONICAL MT T)) by exact MLE.
assert (HTXB : 4096 <= text /\ text + NN <= alloc_ceiling) by lia.
pose proof (HSVa (spZ regs - 32) _ ltac:(lia) HQ18) as HV18.
pose proof (HSVa (spZ regs - 24) _ ltac:(lia) HQ9) as HV9.
pose proof (HSVa (spZ regs - 16) _ ltac:(lia) HQ8) as HV8.
pose proof (HSVa (spZ regs - 8) _ ltac:(lia) HQ1) as HV1.
apply (rcn_mret (spZ regs) ly S W mem md ly2 S2 W2 mem2 regs q text T); try eassumption; try reflexivity.
Qed.

End e.
End d.
End b.
