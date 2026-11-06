(* reac-pw/fuzz_headamp image A (fuzz_headamp.asan, pinned sha256
   f3e0669d2819724922df0556b11c2dcd22d1e16fe7e0fe1535ce784b34436c47; every address below is measured on the
   unstripped twin b5f352154c54a97c66fd92dfa228e8a854498f6cd313dba0107900546b043f9a, whose loaded sections are
   byte-equal to the pin's except .note.gnu.build-id): the sub-cuts of the piece "the key and the channel" of the walk of
   LLVMFuzzerTestOneInput (lib/A/HPgSegM.v hq_piece_M3c_key_stmt, KEY 0x83168 -> VAL 0x83364 / RF 0x83460 /
   LATCH 0x83474 / RC 0x83694), the statements of its four parts, and the theorem that chains the four into
   hq_piece_M3c_key_stmt, closing read_channel's two loops by induction on the loop index. Statement text and that
   chaining only: no instruction is walked here. Proves no function (kind: segment lemma).

   THE CODE (fuzz_headamp.c:120-138; s2 = the key, the body of entry m inside the pp block)
     part 1, KEY 0x83168 .. BL 0x831c0: the dead `blt` (m >= 0), the four saves at R+0xc8 .. R+0xe0, the strncmp
       wrapper at 0x83190 against the harness's "reac.headamp." (13 bytes), the reload of t6 and t2; a key without
       the prefix goes to LATCH with m + 2, else x->keys++ (`lw` / `sw` at x+0x80) and a0 := s2 + 13 (rest),
       a1 := 0 (the index i), a5 := 5, a6 := 0x20, to BL.
     part 2, one turn of the blanks loop BL 0x831c0 (fuzz_headamp.c:70-72): the instrumented 1-byte read of
       rest[i]; a blank goes back to BL with i + 1; else the sign (fuzz_headamp.c:74-75, a2 := the sign flag),
       the instrumented read of the first digit and its test: no digit goes to RF with t3 = BAD_KEY, a digit to
       DG with j = 0, acc = 0, big = 0.
     part 3, one turn of the digits loop DG 0x83264 (fuzz_headamp.c:79-85): the big rule against 1000000
       (R+0xc0, in t0), acc := acc * 10 + digit, the instrumented read of the next byte; a digit goes back to DG
       with j + 1, else to DOT.
     part 4, DOT 0x832b0 (fuzz_headamp.c:86-138): the dead `beqz` (a digit was read), the sign, the dead `beq`,
       the '.' test (no '.': RF with BAD_KEY), the saves of big and ch at R+0x98 / R+0xa0, the strcmp chain
       against the harness's "phantom" 0x21340, "pad" 0x21360, "sens" 0x21380 (no name: RF with BAD_KEY), then
       big or ch >= 48 (RF with OUT_OF_RANGE), else VAL.

   THE MODEL. rest = hk_rest k = skipn 13 k is read_channel's string (Pod/Headamp.v); its blanks are
   rc_blanks rest, the bytes the blanks and the sign take are hk_d rest and the sign is hk_neg rest; the digits
   loop runs rc_digits from 0 / false over skipn (hk_d rest) rest, and the cut DG keeps the equation that says
   the digits read so far and the state (acc, big) give the same result as rc_digits from the start. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase HPgCSpec HPgImgA HPgSeg HPgSegM.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* the three sub-cuts *)
Definition HK_BL : Z := 0x831c0.   (* read_channel's blanks loop head (fuzz_headamp.c:70) *)
Definition HK_DG : Z := 0x83264.   (* the digits loop head (fuzz_headamp.c:80) *)
Definition HK_DOT : Z := 0x832b0.  (* the digits are read: the used / '.' tests (fuzz_headamp.c:86, 128) *)

(* read_channel's string: the key after the prefix (fuzz_headamp.c:123, rest = k + 13) *)
Definition hk_rest (k : list byte) : list byte := skipn (length HA_PREFIX) k.
(* the bytes the blanks and the sign take, and the sign (fuzz_headamp.c:70-75) *)
Definition hk_d (rest : list byte) : nat :=
  (rc_blanks rest + snd (rc_sign (skipn (rc_blanks rest) rest)))%nat.
Definition hk_neg (rest : list byte) : bool := fst (rc_sign (skipn (rc_blanks rest) rest)).

(* the bounds the two loops close by: a key is at most 45 bytes (Model.ent_wf) *)
Lemma hk_rc_blanks_le : forall s, (rc_blanks s <= length s)%nat.
Proof. induction s as [|b s IH]; cbn [rc_blanks length]; [lia|]. destruct (rc_blank b); lia. Qed.

Lemma hk_digit_lt : forall (s : list byte) i, rc_digit (nth i s Cursor.NUL) = true -> (i < length s)%nat.
Proof.
intros s i H. destruct (Nat.lt_ge_cases i (length s)) as [L|L]; [exact L|].
rewrite nth_overflow in H by exact L. vm_compute in H. discriminate H.
Qed.

Lemma hk_key_len : forall (r : Model.pod_rec) m k, Model.pod_rec_wf r -> (m < length (Model.ents r))%nat ->
Accessors.key_of (nth m (Model.ents r) (Model.Ent 0 0 [])) = Some k -> (length k <= 45)%nat.
Proof.
intros r m k Hw Hm Hk.
destruct (Model.ents_wf r Hw) as [_ Hall].
pose proof (proj1 (Forall_forall _ _) Hall _ (nth_In _ (Model.Ent 0 0 []) Hm)) as (_ & Hbl & Hsz).
unfold Accessors.key_of in Hk.
destruct (_ && _ && _) in Hk; [|discriminate Hk]. injection Hk as <-.
unfold Cursor.cstr. rewrite length_firstn. lia.
Qed.

Lemma hk_rest_len : forall k, (length (hk_rest k) <= length k)%nat.
Proof. intros k. unfold hk_rest. rewrite length_skipn. lia. Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section c.
Variable segs : list Segment.
Section d.
Variable B : asyms.
Variable MT : ameter_ops.

(* the key's address: the body of entry m inside the pp block (pod.h:92, s2 at KEY) *)
Definition hk_kaddr (cx : hs_scx segs) (m : nat) : Z :=
  e_pp (x_e segs cx) + HQ_ENT_BODY + 104 * Z.of_nat m.

(* the registers and cells fixed from the strncmp's return on: the segment's, the loop's constants, the pair
   body's four saved words, t6 = &ent[0], t2 = n_ent, s4 = m + 1 and s5 = m + 2 *)
Definition hk_L (cx : hs_scx segs) (r : Model.pod_rec) (m : nat) : list (hd_loc * Z) :=
  hq_L_seg segs cx ++ hq_L_loopc segs cx ++ hq_L_body segs cx r ++
  [(LReg 31, e_pp (x_e segs cx) + HQ_ENT0); (LReg 7, hq_nent r);
   (LReg 20, Z.of_nat m + 1); (LReg 21, Z.of_nat m + 2)].

(* what holds from x->keys++ (0x831b0) to the piece's exits: KEY's facts with the pair in front of the fold
   (hq_pair_inv), x->keys one more, and KEY's bound |cs| <= keys (VAL and CELL carry it). hq_base3 is named with the Section's float state fx: written without `@`,
   its implicit FPState would resolve to the binder fx2 and its float clause would compare fx2 with itself. *)
Definition hk_inv (cx : hs_scx segs) (fx2 : YK11.FPState) (r : Model.pod_rec) (at0 m : nat) (k : list byte)
(cs : list cell) (keys rf : Z) ly2 S2 W2 regs2 mem2 md2 : Prop :=
@hq_base3 fx rc SK segs B MT cx fx2 r hq_shX ly2 S2 W2 regs2 mem2 md2 /\
hs_at_cx segs cx W2 mem2 regs2 (hk_L cx r m) /\
hq_fs fx2 9 HQ_F32_M1 /\ hq_fs fx2 18 HQ_F32_256 /\
hq_live segs cx r /\ (at0 <= m)%nat /\
Accessors.key_of (nth m (Model.ents r) (Model.Ent 0 0 [])) = Some k /\
hq_pair_inv segs cx r m k (nth (S m) (Model.ents r) (Model.Ent 0 0 [])) cs keys rf /\
hq_x_at segs cx W2 mem2 cs (keys + 1) rf /\
Z.of_nat (length cs) <= keys.

(* ---------------- BL 0x831c0: the blanks loop's head at index i ----------------
   s2 = the key, a0 = rest = s2 + 13, a1 = i, a5 = 5 and a6 = 0x20 (the isspace bounds) *)
Definition hk_cut_BL (cx : hs_scx segs) (fx2 : YK11.FPState) (r : Model.pod_rec) (at0 m : nat) (k : list byte)
(cs : list cell) (keys rf : Z) (i : nat) ly2 S2 W2 regs2 mem2 md2 : Prop :=
hk_inv cx fx2 r at0 m k cs keys rf ly2 S2 W2 regs2 mem2 md2 /\
hs_at_cx segs cx W2 mem2 regs2
  [(LReg 18, hk_kaddr cx m); (LReg 10, hk_kaddr cx m + 13); (LReg 11, Z.of_nat i);
   (LReg 15, 5); (LReg 16, 32)] /\
(i <= rc_blanks (hk_rest k))%nat.

(* ---------------- DG 0x83264: the digits loop's head with j digits read before this one ----------------
   s2 = the key + d, a4 = s2 + 14 (rest + d + 1), a0 = j, a1 = d, a2 = the sign flag (0 for '-'), a3 = the digit
   at d + j, a7 = 10, t0 = 1000000 (R+0xc0), t1 = acc, t4 = big, t3 = BAD_KEY (0x83244). *)
Definition hk_cut_DG (cx : hs_scx segs) (fx2 : YK11.FPState) (r : Model.pod_rec) (at0 m : nat) (k : list byte)
(cs : list cell) (keys rf : Z) (j : nat) (acc : Z) (big : bool) ly2 S2 W2 regs2 mem2 md2 : Prop :=
hk_inv cx fx2 r at0 m k cs keys rf ly2 S2 W2 regs2 mem2 md2 /\
hs_at_cx segs cx W2 mem2 regs2
  [(LReg 18, hk_kaddr cx m + Z.of_nat (hk_d (hk_rest k)));
   (LReg 14, hk_kaddr cx m + Z.of_nat (hk_d (hk_rest k)) + 14);
   (LReg 10, Z.of_nat j); (LReg 11, Z.of_nat (hk_d (hk_rest k)));
   (LReg 12, if hk_neg (hk_rest k) then 0 else 1);
   (LReg 13, bv_unsigned (nth (hk_d (hk_rest k) + j) (hk_rest k) Cursor.NUL));
   (LReg 17, 10); (LReg 5, HQ_RC_BIG); (LReg 6, acc); (LReg 29, Z.b2z big);
   (LReg 28, REFUSE_BAD_KEY)] /\
rc_digit (nth (hk_d (hk_rest k) + j) (hk_rest k) Cursor.NUL) = true /\
rc_digits 0 false (skipn (hk_d (hk_rest k)) (hk_rest k)) =
  (fst (fst (rc_digits acc big (skipn (hk_d (hk_rest k) + j) (hk_rest k)))),
   snd (fst (rc_digits acc big (skipn (hk_d (hk_rest k) + j) (hk_rest k)))),
   (j + snd (rc_digits acc big (skipn (hk_d (hk_rest k) + j) (hk_rest k))))%nat) /\
0 <= acc <= 10000009.

(* ---------------- DOT 0x832b0: nd >= 1 digits were read ----------------
   s2 = the key + d, a0 = nd, a1 = d, a2 = the sign flag, a3 = the byte after the digits, t1 = acc, t4 = big,
   t3 = BAD_KEY; read_channel's answer is (d + nd, +-acc, big). *)
Definition hk_cut_DOT (cx : hs_scx segs) (fx2 : YK11.FPState) (r : Model.pod_rec) (at0 m : nat) (k : list byte)
(cs : list cell) (keys rf : Z) (nd : nat) (acc : Z) (big : bool) ly2 S2 W2 regs2 mem2 md2 : Prop :=
hk_inv cx fx2 r at0 m k cs keys rf ly2 S2 W2 regs2 mem2 md2 /\
hs_at_cx segs cx W2 mem2 regs2
  [(LReg 18, hk_kaddr cx m + Z.of_nat (hk_d (hk_rest k)));
   (LReg 10, Z.of_nat nd); (LReg 11, Z.of_nat (hk_d (hk_rest k)));
   (LReg 12, if hk_neg (hk_rest k) then 0 else 1);
   (LReg 13, bv_unsigned (nth (hk_d (hk_rest k) + nd) (hk_rest k) Cursor.NUL));
   (LReg 6, acc); (LReg 29, Z.b2z big); (LReg 28, REFUSE_BAD_KEY)] /\
(1 <= nd)%nat /\
read_channel (hk_rest k) =
  ((hk_d (hk_rest k) + nd)%nat, (if hk_neg (hk_rest k) then - acc else acc), big) /\
0 <= acc <= 10000009.

(* ---------------- the continuations ---------------- *)
Section f.
Variable cx : hs_scx segs.
Variable r : Model.pod_rec.
Variable POST : world segs -> config -> Prop.

Definition hk_from_BL (at0 m i : nat) : Prop :=
forall fx2 ly2 S2 W2 regs2 mem2 md2 k cs keys rf,
hk_cut_BL cx fx2 r at0 m k cs keys rf i ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (@cfg_at fx2 segs HK_BL regs2 mem2 md2) POST.
Definition hk_from_DG (at0 m j : nat) : Prop :=
forall fx2 ly2 S2 W2 regs2 mem2 md2 k cs keys rf acc big,
hk_cut_DG cx fx2 r at0 m k cs keys rf j acc big ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (@cfg_at fx2 segs HK_DG regs2 mem2 md2) POST.
Definition hk_from_DOT (at0 m : nat) : Prop :=
forall fx2 ly2 S2 W2 regs2 mem2 md2 k cs keys rf nd acc big,
hk_cut_DOT cx fx2 r at0 m k cs keys rf nd acc big ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (@cfg_at fx2 segs HK_DOT regs2 mem2 md2) POST.
End f.

(* ---------------- the four parts ---------------- *)
(* part 1: KEY -> LATCH (no prefix) / BL at i = 0 *)
Definition hk_P1_stmt : Prop :=
forall cx POST r ev at0 m,
hq_start_M03 segs B cx r ev -> hq_from_LATCH segs B MT cx r POST (S (S m)) -> hk_from_BL cx r POST at0 m 0 ->
hq_from_KEY segs B MT cx r POST at0 m.
(* part 2: one turn of the blanks loop, the sign and the first digit: BL i -> BL (i + 1) / RF / DG at j = 0 *)
Definition hk_P2_stmt : Prop :=
forall cx POST r ev at0 m i,
hq_start_M03 segs B cx r ev -> hk_from_BL cx r POST at0 m (S i) -> hq_from_RF segs B MT cx r POST at0 m ->
hk_from_DG cx r POST at0 m 0 -> hk_from_BL cx r POST at0 m i.
(* part 3: one turn of the digits loop: DG j -> DG (j + 1) / DOT *)
Definition hk_P3_stmt : Prop :=
forall cx POST r ev at0 m j,
hq_start_M03 segs B cx r ev -> hk_from_DG cx r POST at0 m (S j) -> hk_from_DOT cx r POST at0 m ->
hk_from_DG cx r POST at0 m j.
(* part 4: the '.' test, the strcmp chain and the channel's range: DOT -> RF / VAL *)
Definition hk_P4_stmt : Prop :=
forall cx POST r ev at0 m,
hq_start_M03 segs B cx r ev -> hq_from_VAL segs B MT cx r POST at0 m -> hq_from_RF segs B MT cx r POST at0 m ->
hk_from_DOT cx r POST at0 m.

(* ---------------- the chaining ---------------- *)
(* the record is well formed: hq_start_M03's third conjunct *)
Lemma hk_start_wf : forall cx r ev, hq_start_M03 segs B cx r ev -> Model.pod_rec_wf r.
Proof. intros cx r ev HS. destruct HS as (_ & _ & Hw & _). exact Hw. Qed.

(* the key of a cut is at most 45 bytes *)
Lemma hk_inv_key_len : forall cx fx2 r at0 m k cs keys rf ly2 S2 W2 regs2 mem2 md2,
Model.pod_rec_wf r -> hk_inv cx fx2 r at0 m k cs keys rf ly2 S2 W2 regs2 mem2 md2 -> (length k <= 45)%nat.
Proof.
intros cx fx2 r at0 m k cs keys rf ly2 S2 W2 regs2 mem2 md2 Hw HI.
destruct HI as (_ & _ & _ & _ & _ & _ & Hk & Hp & _).
destruct Hp as (_ & _ & Hm & _).
exact (hk_key_len r m k Hw ltac:(lia) Hk).
Qed.

Lemma hk_cut_BL_bound : forall cx fx2 r at0 m k cs keys rf i ly2 S2 W2 regs2 mem2 md2,
Model.pod_rec_wf r -> hk_cut_BL cx fx2 r at0 m k cs keys rf i ly2 S2 W2 regs2 mem2 md2 -> (i <= 45)%nat.
Proof.
intros cx fx2 r at0 m k cs keys rf i ly2 S2 W2 regs2 mem2 md2 Hw HC.
destruct HC as (HI & _ & Hi).
pose proof (hk_inv_key_len cx fx2 r at0 m k cs keys rf ly2 S2 W2 regs2 mem2 md2 Hw HI) as Hk.
pose proof (hk_rc_blanks_le (hk_rest k)) as H1. pose proof (hk_rest_len k) as H2. lia.
Qed.

Lemma hk_cut_DG_bound : forall cx fx2 r at0 m k cs keys rf j acc big ly2 S2 W2 regs2 mem2 md2,
Model.pod_rec_wf r -> hk_cut_DG cx fx2 r at0 m k cs keys rf j acc big ly2 S2 W2 regs2 mem2 md2 -> (j < 45)%nat.
Proof.
intros cx fx2 r at0 m k cs keys rf j acc big ly2 S2 W2 regs2 mem2 md2 Hw HC.
destruct HC as (HI & _ & Hdig & _).
pose proof (hk_inv_key_len cx fx2 r at0 m k cs keys rf ly2 S2 W2 regs2 mem2 md2 Hw HI) as Hk.
pose proof (hk_digit_lt _ _ Hdig) as Hl. pose proof (hk_rest_len k) as H2. lia.
Qed.

Section close.
Hypothesis P1 : hk_P1_stmt.
Hypothesis P2 : hk_P2_stmt.
Hypothesis P3 : hk_P3_stmt.
Hypothesis P4 : hk_P4_stmt.

Theorem hk_key_holds : hq_piece_M3c_key_stmt segs B MT.
Proof.
intros cx POST r ev at0 m HS HVAL HRF HLATCH HRC.
pose proof (hk_start_wf cx r ev HS) as Hw.
assert (HDOT : hk_from_DOT cx r POST at0 m) by exact (P4 cx POST r ev at0 m HS HVAL HRF).
assert (HDG : forall j, hk_from_DG cx r POST at0 m j).
{ assert (H : forall f j, (45 - j <= f)%nat -> hk_from_DG cx r POST at0 m j).
  { induction f as [|f IH]; intros j Hj.
    - intros fx2 ly2 S2 W2 regs2 mem2 md2 k cs keys rf acc big HC. exfalso.
      pose proof (hk_cut_DG_bound cx fx2 r at0 m k cs keys rf j acc big ly2 S2 W2 regs2 mem2 md2 Hw HC). lia.
    - apply (P3 cx POST r ev at0 m j HS); [apply IH; lia | exact HDOT]. }
  intros j. exact (H (45 - j)%nat j (le_n _)). }
assert (HBL : forall i, hk_from_BL cx r POST at0 m i).
{ assert (H : forall f i, (46 - i <= f)%nat -> hk_from_BL cx r POST at0 m i).
  { induction f as [|f IH]; intros i Hi.
    - intros fx2 ly2 S2 W2 regs2 mem2 md2 k cs keys rf HC. exfalso.
      pose proof (hk_cut_BL_bound cx fx2 r at0 m k cs keys rf i ly2 S2 W2 regs2 mem2 md2 Hw HC). lia.
    - apply (P2 cx POST r ev at0 m i HS); [apply IH; lia | exact HRF | exact (HDG 0%nat)]. }
  intros i. exact (H (46 - i)%nat i (le_n _)). }
exact (P1 cx POST r ev at0 m HS HLATCH (HBL 0%nat)).
Qed.
End close.

End d.
End c.
End b.

Print Assumptions hk_key_holds.
