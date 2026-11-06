(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_headamp/lib/A/HPgKcCut.v at f9c9fcf89aea; the same split of
   the piece "the key and the channel" for image B: B's pcs, B's registers and B's three sub-cuts (B reads the
   sign and the first digit inside its digits loop, so its DG cut does not know that a digit is next and its DOT
   cut also covers the case of no digit). *)
(* reac-pw/fuzz_headamp image B (fuzz_headamp.asan-ubsan, pinned sha256
   53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94; every address below is measured on the
   unstripped twin 1674e30a0698f381704e66d2398d7906c881f4ba8fc619cb41b89fb97ad112ff, whose loaded sections are
   byte-equal to the pin's except .note.gnu.build-id): the sub-cuts of the piece "the key and the channel" of the walk of
   LLVMFuzzerTestOneInput (lib/AU/HPgSegM.v hqu_piece_M3c_key_stmt, KEY 0x83260 -> VAL 0x83490 / RF 0x836a0 /
   LATCH 0x836b4 / RC 0x83850), the statements of its four parts, and the theorem that chains the four into
   hqu_piece_M3c_key_stmt, closing read_channel's two loops by induction on the loop index. Statement text and
   that chaining only: no instruction is walked here. Proves no function (kind: segment lemma).

   THE CODE (fuzz_headamp.c:120-138; s7 = the key, the body of entry m inside the pp block; s2 = m + 1)
     part 1, KEY 0x83260 .. BL 0x832e8: a0 := m + 2 (`addiw`), the trap test of that increment (0x83264, never:
       m + 1 < 33) and the at < 0 test (`bltz a2` 0x83268 -> RC, never: a2 = m + 1); the seven saves of the
       entry table and of the next index (R+0xd8 := m + 2, R+0xe0 .. R+0x100, R+0x108 := t6, R+0x110 := t5); the
       strncmp wrapper at 0x8329c (`jal` 0x41c24) with a0 = s7, a1 = 0x20f40 (the harness's "reac.headamp."),
       a2 = 13; the reload of t6 and t5 (0x832a0, 0x832a4); a key without the prefix goes to LATCH with m + 2
       (`bnez a0` 0x832a8), else x->keys++ (`lw` / `addiw` / the trap test 0x832b8 / `sw` at x+0x80, x from
       R+0x138), the constants a6 := 5, a7 := 0x20, t2 := 9, t3 := 10, t4 := R+0xd0 (1000000), the trap test
       `bgeu s7,-13` 0x832d8 (never: the key lies below 2^64 - 13), a1 := 0, a0 := s7 + 13 (rest),
       a2 := not a0, to BL.
     part 2, one turn of the blanks loop BL 0x832e8 (fuzz_headamp.c:70-75): a3 := a0 + a1, the instrumented
       1-byte read of rest[i] (slow block 0x8331c); (c - 9) <u 5 or c = 0x20: a1++, the cursor's trap test
       `bgeu a2,a1` 0x8330c, back to BL; else the sign 0x83328 .. 0x83348 ('+' or '-': a1++,
       a3 := (c != '-'), else a3 := 1), the cursor's trap test 0x8334c, a4 := 0, ra := 0, s5 := 0,
       a5 := s7 + a1, a6 := a5 + 13, to DG with j = 0.
     part 3, one turn of the digits loop DG 0x83364 (fuzz_headamp.c:79-85): the instrumented 1-byte read of
       rest[d + j] (slow block 0x833bc); not a digit: to DOT with nd = j; else the big rule against
       t4 = 1000000 (`bge t4,s5` 0x83388: else ra := 1), s5 := s5 * 10 + digit with the multiply's trap test
       0x833a0, a4++, the cursor's trap test 0x833b4, back to DG.
     part 4, DOT 0x833c8 (fuzz_headamp.c:86-138): a5 := 4; no digit: RF (BAD_KEY); the sign (`neg s5`); a1 :=
       d + nd (`beqz a1` 0x833dc: never); the trap tests 0x833e4, 0x833f0, 0x83400; the byte after the digits is
       not '.': RF (BAD_KEY); R+0x90 := ra (big); s7 := the name; the strcmp chain (`jal` 0x41c20 at 0x83418,
       0x8342c, 0x83440) against the harness's "phantom" 0x21380, "pad" 0x213a0, "sens" 0x213c0 (no name: RF
       with BAD_KEY); (a6, s7) := (0, 1) / (1, 1) / (2, 0x37); the reload of t5 and t6; a5 := 5; big
       (R+0x90 <> 0) or ch >u 47: RF (OUT_OF_RANGE); else VAL.

   THE MODEL. rest = hku_rest k = skipn 13 k is read_channel's string (Pod/Headamp.v); its blanks are
   rc_blanks rest, the bytes the blanks and the sign take are hku_d rest and the sign is hku_neg rest; the digits
   loop runs rc_digits from 0 / false over skipn (hku_d rest) rest, and the cut DG keeps the equation that says
   the digits read so far and the state (acc, big) give the same result as rc_digits from the start; DOT keeps
   rc_digits' whole answer (acc, big, nd) with the byte that stopped it. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK14 YK0s YK15 YK18 YP09 YI04 YI08 YN3v YI00 YI0m YI09.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YE00 YE01.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YK0o.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Cursor Model Layout Accessors.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Headamp.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Spec Require Import HeadBytes.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog.HeadCheck Require KeyFacts.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase HPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import HPgImgB HPgSeg HPgSegM.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* the three sub-cuts *)
Definition HKU_BL : Z := 0x832e8.   (* read_channel's blanks loop head (fuzz_headamp.c:70) *)
Definition HKU_DG : Z := 0x83364.   (* the digits loop head (fuzz_headamp.c:79) *)
Definition HKU_DOT : Z := 0x833c8.  (* the digits are read: the used / '.' tests (fuzz_headamp.c:86, 128) *)

(* read_channel's string: the key after the prefix (fuzz_headamp.c:123, rest = k + 13) *)
Definition hku_rest (k : list byte) : list byte := skipn (length HA_PREFIX) k.
(* the bytes the blanks and the sign take, and the sign (fuzz_headamp.c:70-75) *)
Definition hku_d (rest : list byte) : nat :=
  (rc_blanks rest + snd (rc_sign (skipn (rc_blanks rest) rest)))%nat.
Definition hku_neg (rest : list byte) : bool := fst (rc_sign (skipn (rc_blanks rest) rest)).

(* the bounds the two loops close by: a key is at most 45 bytes (Model.ent_wf) *)
Lemma hku_key_len : forall (r : Model.pod_rec) m k, Model.pod_rec_wf r -> (m < length (Model.ents r))%nat ->
Accessors.key_of (nth m (Model.ents r) (Model.Ent 0 0 [])) = Some k -> (length k <= 45)%nat.
Proof.
intros r m k Hw Hm Hk.
destruct (Model.ents_wf r Hw) as [_ Hall].
pose proof (proj1 (Forall_forall _ _) Hall _ (nth_In _ (Model.Ent 0 0 []) Hm)) as (_ & Hbl & Hsz).
unfold Accessors.key_of in Hk.
destruct (_ && _ && _) in Hk; [|discriminate Hk]. injection Hk as <-.
unfold Cursor.cstr. rewrite length_firstn. lia.
Qed.

Lemma hku_rest_len : forall k, (length (hku_rest k) <= length k)%nat.
Proof. intros k. unfold hku_rest. rewrite length_skipn. lia. Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section c.
Variable segs : list Segment.
Section d.
Variable B : asyms.
Variable MT : ameter_ops.

(* the key's address: the body of entry m inside the pp block (pod.h:92, s7 at KEY; hqu_cut_KEY's LReg 23) *)
Definition hku_kaddr (cx : hsu_scx segs) (m : nat) : Z :=
  e_pp (x_e segs cx) + Layout.OFF_ENT + 8 + Layout.ENT_SIZE * Z.of_nat m.

(* the registers and cells fixed from the strncmp's return to the piece's exits: the segment's, the loop's
   constants, the params-struct word and its shadow address (t5, t6, reloaded after every call), the pair body's
   seven saved words with the next index m + 2, s2 = m + 1 and s8 = 104 (m + 1) *)
Definition hku_L (cx : hsu_scx segs) (m : nat) : list (hd_loc * Z) :=
  hqu_L_seg segs cx ++ hqu_L_loopc segs cx ++ hqu_L_t56 segs cx ++ hqu_L_body segs cx (Z.of_nat m + 2) ++
  [(LReg 18, Z.of_nat m + 1); (LReg 24, Layout.ENT_SIZE * (Z.of_nat m + 1))].

(* what holds from x->keys++ (0x832bc) to the piece's exits: KEY's facts with the pair in front of the fold
   (hqu_pair_inv), x->keys one more, and KEY's bound of the cells written by the keys counted before this one *)
Definition hku_inv (cx : hsu_scx segs) (fx2 : YK11.FPState) (r : Model.pod_rec) (at0 m : nat) (k : list byte)
(cs : list cell) (keys rf : Z) ly2 S2 W2 regs2 mem2 md2 : Prop :=
@hqu_base3 fx rc SK segs B MT cx fx2 r hqu_shX ly2 S2 W2 regs2 mem2 md2 /\
hsu_at_cx segs cx W2 mem2 regs2 (hku_L cx m) /\
hqu_fs fx2 9 HQU_F32_M1 /\ hqu_fs fx2 18 HQU_F32_256 /\ hqu_fs fx2 19 HQU_F32_2P63 /\
hqu_live segs cx r /\ (at0 <= m)%nat /\
Accessors.key_of (nth m (Model.ents r) (Model.Ent 0 0 [])) = Some k /\
hqu_pair_inv segs cx r m k (nth (S m) (Model.ents r) (Model.Ent 0 0 [])) cs keys rf /\
hqu_x_at segs cx W2 mem2 cs (keys + 1) rf /\ Z.of_nat (length cs) <= keys.

(* ---------------- BL 0x832e8: the blanks loop's head at index i ----------------
   s7 = the key, a0 = rest = s7 + 13, a1 = i, a2 = the one's complement of rest (the cursor's trap bound),
   a6 = 5 and a7 = 0x20 (the isspace bounds), t2 = 9, t3 = 10 and t4 = 1000000 (the digits loop's constants) *)
Definition hku_cut_BL (cx : hsu_scx segs) (fx2 : YK11.FPState) (r : Model.pod_rec) (at0 m : nat) (k : list byte)
(cs : list cell) (keys rf : Z) (i : nat) ly2 S2 W2 regs2 mem2 md2 : Prop :=
hku_inv cx fx2 r at0 m k cs keys rf ly2 S2 W2 regs2 mem2 md2 /\
hsu_at_cx segs cx W2 mem2 regs2
  [(LReg 23, hku_kaddr cx m); (LReg 10, hku_kaddr cx m + 13); (LReg 11, Z.of_nat i);
   (LReg 12, hqu_not (hku_kaddr cx m + 13)); (LReg 16, 5); (LReg 17, 32);
   (LReg 7, 9); (LReg 28, 10); (LReg 29, HQU_RC_BIG)] /\
(i <= rc_blanks (hku_rest k))%nat.

(* ---------------- DG 0x83364: the digits loop's head with j digits read ----------------
   s7 = the key, a0 = rest, a2 = the one's complement of rest, a1 = d (the blanks and the sign), a3 = the sign
   flag (0 for '-'), a4 = j, ra = big, s5 = acc, a5 = s7 + d, a6 = s7 + d + 13, t2 = 9, t3 = 10,
   t4 = 1000000. The bytes d .. d + j - 1 of rest were digits: d + j <= |rest|. *)
Definition hku_cut_DG (cx : hsu_scx segs) (fx2 : YK11.FPState) (r : Model.pod_rec) (at0 m : nat) (k : list byte)
(cs : list cell) (keys rf : Z) (j : nat) (acc : Z) (big : bool) ly2 S2 W2 regs2 mem2 md2 : Prop :=
hku_inv cx fx2 r at0 m k cs keys rf ly2 S2 W2 regs2 mem2 md2 /\
hsu_at_cx segs cx W2 mem2 regs2
  [(LReg 23, hku_kaddr cx m); (LReg 10, hku_kaddr cx m + 13); (LReg 12, hqu_not (hku_kaddr cx m + 13));
   (LReg 11, Z.of_nat (hku_d (hku_rest k)));
   (LReg 13, if hku_neg (hku_rest k) then 0 else 1);
   (LReg 14, Z.of_nat j); (LReg 1, Z.b2z big); (LReg 21, acc);
   (LReg 15, hku_kaddr cx m + Z.of_nat (hku_d (hku_rest k)));
   (LReg 16, hku_kaddr cx m + Z.of_nat (hku_d (hku_rest k)) + 13);
   (LReg 7, 9); (LReg 28, 10); (LReg 29, HQU_RC_BIG)] /\
(hku_d (hku_rest k) + j <= length (hku_rest k))%nat /\
rc_digits 0 false (skipn (hku_d (hku_rest k)) (hku_rest k)) =
  (fst (fst (rc_digits acc big (skipn (hku_d (hku_rest k) + j) (hku_rest k)))),
   snd (fst (rc_digits acc big (skipn (hku_d (hku_rest k) + j) (hku_rest k)))),
   (j + snd (rc_digits acc big (skipn (hku_d (hku_rest k) + j) (hku_rest k))))%nat) /\
0 <= acc <= 10000009.

(* ---------------- DOT 0x833c8: nd >= 0 digits were read ----------------
   s7 = the key, a0 = rest, a2 = the one's complement of rest, a1 = d, a3 = the sign flag, a4 = nd, ra = big,
   s5 = acc, a7 = s7 + d + nd and t0 = the byte after the digits (not a digit); rc_digits' whole answer from d is
   (acc, big, nd). *)
Definition hku_cut_DOT (cx : hsu_scx segs) (fx2 : YK11.FPState) (r : Model.pod_rec) (at0 m : nat) (k : list byte)
(cs : list cell) (keys rf : Z) (nd : nat) (acc : Z) (big : bool) ly2 S2 W2 regs2 mem2 md2 : Prop :=
hku_inv cx fx2 r at0 m k cs keys rf ly2 S2 W2 regs2 mem2 md2 /\
hsu_at_cx segs cx W2 mem2 regs2
  [(LReg 23, hku_kaddr cx m); (LReg 10, hku_kaddr cx m + 13); (LReg 12, hqu_not (hku_kaddr cx m + 13));
   (LReg 11, Z.of_nat (hku_d (hku_rest k)));
   (LReg 13, if hku_neg (hku_rest k) then 0 else 1);
   (LReg 14, Z.of_nat nd); (LReg 1, Z.b2z big); (LReg 21, acc);
   (LReg 17, hku_kaddr cx m + Z.of_nat (hku_d (hku_rest k)) + Z.of_nat nd);
   (LReg 5, bv_unsigned (nth (hku_d (hku_rest k) + nd) (hku_rest k) Cursor.NUL))] /\
(hku_d (hku_rest k) + nd <= length (hku_rest k))%nat /\
rc_digit (nth (hku_d (hku_rest k) + nd) (hku_rest k) Cursor.NUL) = false /\
rc_digits 0 false (skipn (hku_d (hku_rest k)) (hku_rest k)) = (acc, big, nd) /\
0 <= acc <= 10000009.

(* ---------------- the continuations ---------------- *)
Section f.
Variable cx : hsu_scx segs.
Variable r : Model.pod_rec.
Variable POST : world segs -> config -> Prop.

Definition hku_from_BL (at0 m i : nat) : Prop :=
forall fx2 ly2 S2 W2 regs2 mem2 md2 k cs keys rf,
hku_cut_BL cx fx2 r at0 m k cs keys rf i ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (@cfg_at fx2 segs HKU_BL regs2 mem2 md2) POST.
Definition hku_from_DG (at0 m j : nat) : Prop :=
forall fx2 ly2 S2 W2 regs2 mem2 md2 k cs keys rf acc big,
hku_cut_DG cx fx2 r at0 m k cs keys rf j acc big ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (@cfg_at fx2 segs HKU_DG regs2 mem2 md2) POST.
Definition hku_from_DOT (at0 m : nat) : Prop :=
forall fx2 ly2 S2 W2 regs2 mem2 md2 k cs keys rf nd acc big,
hku_cut_DOT cx fx2 r at0 m k cs keys rf nd acc big ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (@cfg_at fx2 segs HKU_DOT regs2 mem2 md2) POST.
End f.

(* ---------------- the four parts ---------------- *)
(* part 1: KEY -> LATCH (no prefix) / BL at i = 0 *)
Definition hku_P1_stmt : Prop :=
forall cx POST r ev at0 m,
hqu_start_M03 segs B cx r ev -> hqu_from_LATCH segs B MT cx r POST (S (S m)) -> hku_from_BL cx r POST at0 m 0 ->
hqu_from_KEY segs B MT cx r POST at0 m.
(* part 2: one turn of the blanks loop, then the sign: BL i -> BL (i + 1) / DG at j = 0 *)
Definition hku_P2_stmt : Prop :=
forall cx POST r ev at0 m i,
hqu_start_M03 segs B cx r ev -> hku_from_BL cx r POST at0 m (S i) -> hku_from_DG cx r POST at0 m 0 ->
hku_from_BL cx r POST at0 m i.
(* part 3: one turn of the digits loop: DG j -> DG (j + 1) / DOT *)
Definition hku_P3_stmt : Prop :=
forall cx POST r ev at0 m j,
hqu_start_M03 segs B cx r ev -> hku_from_DG cx r POST at0 m (S j) -> hku_from_DOT cx r POST at0 m ->
hku_from_DG cx r POST at0 m j.
(* part 4: no digit, the '.' test, the strcmp chain and the channel's range: DOT -> RF / VAL *)
Definition hku_P4_stmt : Prop :=
forall cx POST r ev at0 m,
hqu_start_M03 segs B cx r ev -> hqu_from_VAL segs B MT cx r POST at0 m -> hqu_from_RF segs B MT cx r POST at0 m ->
hku_from_DOT cx r POST at0 m.

(* ---------------- the chaining ---------------- *)
(* the record is well formed: hqu_start_M03's third conjunct *)
Lemma hku_start_wf : forall cx r ev, hqu_start_M03 segs B cx r ev -> Model.pod_rec_wf r.
Proof. intros cx r ev HS. destruct HS as (_ & _ & Hw & _). exact Hw. Qed.

(* the key of a cut is at most 45 bytes *)
Lemma hku_inv_key_len : forall cx fx2 r at0 m k cs keys rf ly2 S2 W2 regs2 mem2 md2,
Model.pod_rec_wf r -> hku_inv cx fx2 r at0 m k cs keys rf ly2 S2 W2 regs2 mem2 md2 -> (length k <= 45)%nat.
Proof.
intros cx fx2 r at0 m k cs keys rf ly2 S2 W2 regs2 mem2 md2 Hw HI.
destruct HI as (_ & _ & _ & _ & _ & _ & _ & Hk & Hp & _).
destruct Hp as (_ & _ & Hm & _).
exact (hku_key_len r m k Hw ltac:(lia) Hk).
Qed.

Lemma hku_cut_BL_bound : forall cx fx2 r at0 m k cs keys rf i ly2 S2 W2 regs2 mem2 md2,
Model.pod_rec_wf r -> hku_cut_BL cx fx2 r at0 m k cs keys rf i ly2 S2 W2 regs2 mem2 md2 -> (i <= 45)%nat.
Proof.
intros cx fx2 r at0 m k cs keys rf i ly2 S2 W2 regs2 mem2 md2 Hw HC.
destruct HC as (HI & _ & Hi).
pose proof (hku_inv_key_len cx fx2 r at0 m k cs keys rf ly2 S2 W2 regs2 mem2 md2 Hw HI) as Hk.
pose proof (KeyFacts.rc_blanks_le (hku_rest k)) as H1. pose proof (hku_rest_len k) as H2. lia.
Qed.

Lemma hku_cut_DG_bound : forall cx fx2 r at0 m k cs keys rf j acc big ly2 S2 W2 regs2 mem2 md2,
Model.pod_rec_wf r -> hku_cut_DG cx fx2 r at0 m k cs keys rf j acc big ly2 S2 W2 regs2 mem2 md2 -> (j <= 45)%nat.
Proof.
intros cx fx2 r at0 m k cs keys rf j acc big ly2 S2 W2 regs2 mem2 md2 Hw HC.
destruct HC as (HI & _ & Hj & _).
pose proof (hku_inv_key_len cx fx2 r at0 m k cs keys rf ly2 S2 W2 regs2 mem2 md2 Hw HI) as Hk.
pose proof (hku_rest_len k) as H2. lia.
Qed.

Section close.
Hypothesis P1 : hku_P1_stmt.
Hypothesis P2 : hku_P2_stmt.
Hypothesis P3 : hku_P3_stmt.
Hypothesis P4 : hku_P4_stmt.

Theorem hku_key_holds : hqu_piece_M3c_key_stmt segs B MT.
Proof.
intros cx POST r ev at0 m HS HVAL HRF HLATCH HRC.
pose proof (hku_start_wf cx r ev HS) as Hw.
assert (HDOT : hku_from_DOT cx r POST at0 m) by exact (P4 cx POST r ev at0 m HS HVAL HRF).
assert (HDG : forall j, hku_from_DG cx r POST at0 m j).
{ assert (H : forall f j, (46 - j <= f)%nat -> hku_from_DG cx r POST at0 m j).
  { induction f as [|f IH]; intros j Hj.
    - intros fx2 ly2 S2 W2 regs2 mem2 md2 k cs keys rf acc big HC. exfalso.
      pose proof (hku_cut_DG_bound cx fx2 r at0 m k cs keys rf j acc big ly2 S2 W2 regs2 mem2 md2 Hw HC). lia.
    - apply (P3 cx POST r ev at0 m j HS); [apply IH; lia | exact HDOT]. }
  intros j. exact (H (46 - j)%nat j (le_n _)). }
assert (HBL : forall i, hku_from_BL cx r POST at0 m i).
{ assert (H : forall f i, (46 - i <= f)%nat -> hku_from_BL cx r POST at0 m i).
  { induction f as [|f IH]; intros i Hi.
    - intros fx2 ly2 S2 W2 regs2 mem2 md2 k cs keys rf HC. exfalso.
      pose proof (hku_cut_BL_bound cx fx2 r at0 m k cs keys rf i ly2 S2 W2 regs2 mem2 md2 Hw HC). lia.
    - apply (P2 cx POST r ev at0 m i HS); [apply IH; lia | exact (HDG 0%nat)]. }
  intros i. exact (H (46 - i)%nat i (le_n _)). }
exact (P1 cx POST r ev at0 m HS HLATCH (HBL 0%nat)).
Qed.
End close.

End d.
End c.
End b.

Print Assumptions hku_key_holds.
