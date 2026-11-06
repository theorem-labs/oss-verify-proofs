(* The boundary layer of diginet_scribble_text's walk in image B (fuzz_codec.asan-ubsan 0x86500, 113 instructions,
   frame 16, no call): the state at each segment boundary, the statement of each segment, and their composition into
   cdcU_scribble_text_specX (proved here, by induction over the two loops). The segments are proved against these
   statements in diginet_scribble_text_B_<seg>.v.

   The code (a0 = q the text, a1 = o the output, a2 = n its length):
   S0  0x86500 .. 0x86544: sp -= 16, ra at sp + 8, s0 at sp; o = 0 (to 0x8663c) and q = 0 (to 0x86644) are not
       taken; a5 := the shadow offset through the 8-byte cell at 0x9e430; a6 := ~o; a3 := q; a0 = i := 0,
       a7 = j := 0, t5 := 0, t0 := q + 1, t1 := 46, t2 := 49, t3 := 57; to the loop head 0x86544.
   Ha  0x86544 .. : one pass of the first loop up to its store. The instrumented check of q + i (a4), lbu t4 := q[i];
       t4 = 0 or j >= n go to 0x8664c. Else the UBSan check on t5 (0x86568, not taken: t5 = 0); for t4 = '.' the
       checks of q + i + 1 (0x86574, 0x86594, not taken) and the instrumented check and load of q[i + 1] = t5; a
       digit 1..9 stores t5 - 26 at o + j (the UBSan check of o + j at 0x8659c and the instrumented check at
       0x865a4) and uses 2 text bytes, then i, j advance, t5 := (q + i == 0) and the UBSan check of q + i (0x86600)
       leads back to 0x86544; any other byte goes to 0x865c4 with t4 = the byte.
   Hb  0x865c4 .. : the UBSan check of o + j, the byte itself when below 0x80, else 0x3f, at o + j (the instrumented
       check at 0x865e4); it uses 1 text byte; then the advance of i and j and back to 0x86544 as in Ha.
   P   0x8664c: j >= n goes to the return 0x86698; else a3 = a1 := o + j, a4 := 32, to the padding loop 0x8665c.
   L   0x8665c .. : the UBSan check of o + j, the instrumented check of a1, j += 1, ' ' at a3, a1 and a3 one on;
       j = n goes to the return, else back to 0x8665c.
   X   0x86698 .. ret: ra and s0 back from the frame, sp += 16.
   Every UBSan check branches to the trap at 0x866a8 and every instrumented check to an error report
   (0x866ac .. 0x866c0, 0x86634, 0x86690); none of them is reached.

   A boundary is a predicate on the configuration: the caller's journal at the current memory, the model's input
   and output as at entry, the registers and memory every boundary carries (sc_common) and the boundary's own
   facts. A segment builds its own symbolic state from these facts. *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YK14 YK0s YK15 YK18 YP09 YI04 YI08 YN3v YI00 YI0m YI09.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YI16 YE00 YE01.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import CPgBaseU CPgChkU.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw0.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* The boundaries' addresses. *)
Definition B_ST : Z := 0x86500.     (* diginet_scribble_text *)
Definition PC_H : Z := 0x86544.     (* add a4,a3,a0: the loop head *)
Definition PC_P : Z := 0x8664c.     (* bgeu a7,a2: the padding *)
Definition PC_O : Z := 0x865c4.     (* bltu a6,a7: the store of a byte that is not '.' and a digit *)
Definition PC_L : Z := 0x8665c.     (* bltu a6,a7: the padding loop *)
Definition PC_X : Z := 0x86698.     (* ld ra,8(sp): the return *)

(* The registers the walk never writes, which every boundary keeps at their entry values: ra, gp, tp, s1..s11. *)
Definition sc_kregs : list (bv 5) := [1; 3; 4; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
(* ... and the four of the loops: sp, a2 = n, a5 = the shadow offset, a6 = ~o. *)
Definition sc_lregs : list (bv 5) := [2; 12; 15; 16]%bv.

(* ======================= the Gallina model ======================= *)
Lemma sc_lib_0 : forall l, scr_lib l 0 = ([], 0).
Proof. intros [|x l]; reflexivity. Qed.
Lemma sc_lib_zero : forall l k, scr_lib (0 :: l) k = (repeat 0x20 k, 0).
Proof. intros l [|k]; reflexivity. Qed.
Lemma sc_skipn_cons : forall {X} (l : list X) i d, (i < length l)%nat -> skipn i l = nth i l d :: skipn (S i) l.
Proof. intros X l. induction l as [|x l IH]; intros [|i] d H; cbn in *; try lia; [reflexivity|]. apply IH. lia. Qed.
Lemma sc_in_skipn_lt : forall {X} (x : X) l k, In x (skipn k l) -> (k < length l)%nat.
Proof.
intros X x l k H. destruct (Nat.lt_ge_cases k (length l)) as [Hl|Hl]; [exact Hl|].
rewrite skipn_all2 in H by lia. destruct H.
Qed.
(* the terminator is still ahead after a byte that is not 0 *)
Lemma sc_in0_S : forall l k, In 0 (skipn k l) -> nth k l 0 <> 0 -> In 0 (skipn (S k) l).
Proof.
intros l k Hin Hnz. pose proof (sc_in_skipn_lt 0 l k Hin) as Hk.
rewrite (sc_skipn_cons l k 0 Hk) in Hin. destruct Hin as [He | Hin]; [exfalso; exact (Hnz He) | exact Hin].
Qed.
Lemma sc_u64 : forall x : word, 0 <= bv_unsigned x < 2 ^ 64.
Proof.
intros x. pose proof (bv_unsigned_in_range 64 x) as H. change (bv_modulus 64) with (2 ^ 64) in H. exact H.
Qed.
(* the first loop and the padding give exactly k output bytes *)
Lemma sc_lib_len : forall k t, length (fst (scr_lib t k)) = k.
Proof.
induction k as [|k IH]; intros t; [destruct t; reflexivity|].
destruct t as [|x t']; [apply repeat_length|].
change (scr_lib (x :: t') (S k)) with
  (if x =? 0 then (repeat 0x20 (S k), 0) else
   match t' with
   | y :: t'' => if (x =? 0x2e) && (0x31 <=? y) && (y <=? 0x39)
                 then let '(ou, u) := scr_lib t'' k in ((y - 26) :: ou, u + 2)
                 else let '(ou, u) := scr_lib t' k in ((if x <? 0x80 then x else 0x3f) :: ou, u + 1)
   | [] => let '(ou, u) := scr_lib t' k in ((if x <? 0x80 then x else 0x3f) :: ou, u + 1)
   end).
destruct (x =? 0); [apply repeat_length|].
destruct t' as [|y t''].
- pose proof (IH []) as H. destruct (scr_lib [] k) as [ou u]. cbn [fst length] in *. lia.
- destruct ((x =? 0x2e) && (0x31 <=? y) && (y <=? 0x39)).
  + pose proof (IH t'') as H. destruct (scr_lib t'' k) as [ou u]. cbn [fst length] in *. lia.
  + pose proof (IH (y :: t'')) as H. destruct (scr_lib (y :: t'') k) as [ou u]. cbn [fst length] in *. lia.
Qed.
(* the text from byte i when byte i is 0, or when no output byte is left *)
Lemma sc_lib_at_zero : forall tb i k, (i < length tb)%nat -> nth i tb 0 = 0 ->
  scr_lib (skipn i tb) k = (repeat 0x20 k, 0).
Proof. intros tb i k Hi H0. rewrite (sc_skipn_cons tb i 0 Hi), H0. apply sc_lib_zero. Qed.
(* one step of the first loop: byte i is not 0, so byte i + 1 exists *)
Lemma sc_lib_next : forall tb i k, (S i < length tb)%nat -> nth i tb 0 <> 0 ->
  scr_lib (skipn i tb) (S k) =
  (if (nth i tb 0 =? 0x2e) && (0x31 <=? nth (S i) tb 0) && (nth (S i) tb 0 <=? 0x39)
   then ((nth (S i) tb 0 - 26) :: fst (scr_lib (skipn (S (S i)) tb) k), snd (scr_lib (skipn (S (S i)) tb) k) + 2)
   else ((if nth i tb 0 <? 0x80 then nth i tb 0 else 0x3f) :: fst (scr_lib (skipn (S i) tb) k),
         snd (scr_lib (skipn (S i) tb) k) + 1)).
Proof.
intros tb i k Hi Hx.
rewrite (sc_skipn_cons tb i 0 ltac:(lia)), (sc_skipn_cons tb (S i) 0 Hi).
set (x := nth i tb 0) in *. set (y := nth (S i) tb 0). set (l := skipn (S (S i)) tb).
change (scr_lib (x :: y :: l) (S k)) with
(if x =? 0 then (repeat 0x20 (S k), 0)
 else if (x =? 0x2e) && (0x31 <=? y) && (y <=? 0x39)
 then let '(ou, u) := scr_lib l k in ((y - 26) :: ou, u + 2)
 else let '(ou, u) := scr_lib (y :: l) k in ((if x <? 0x80 then x else 0x3f) :: ou, u + 1)).
rewrite (proj2 (Z.eqb_neq x 0) Hx).
destruct ((x =? 0x2e) && (0x31 <=? y) && (y <=? 0x39)).
- destruct (scr_lib l k); reflexivity.
- destruct (scr_lib (y :: l) k); reflexivity.
Qed.

(* ======================= bytes of memory ======================= *)
Section m. Context {fx : YK11.FPState}.
Lemma sc_garr8_kept : forall (m m' : word -> option byte) q l,
  (forall x, q <= x < q + Z.of_nat (length l) -> mbyte tfibsegs m' x = mbyte tfibsegs m x) ->
  garr8 tfibsegs m q l -> garr8 tfibsegs m' q l.
Proof.
intros m m' q l Hk Hg j Hj. destruct (Hg j Hj) as (Hv & Hr). split; [|exact Hr].
intros k Hk'. assert (k = 0%nat) by lia. subst k. rewrite Hk by lia. exact (Hv 0%nat Hk').
Qed.
Lemma sc_garr8_snoc : forall (m : word -> option byte) q l v,
  garr8 tfibsegs m q l -> val_mem tfibsegs m (q + Z.of_nat (length l)) 1 v -> 0 <= v < 256 ->
  garr8 tfibsegs m q (l ++ [v]).
Proof.
intros m q l v Hg Hv Hr j Hj. rewrite length_app in Hj. cbn [length] in Hj.
destruct (Nat.lt_ge_cases j (length l)) as [Hlt | Hge].
- rewrite app_nth1 by exact Hlt. exact (Hg j Hlt).
- assert (j = length l) by lia. subst j. rewrite app_nth2 by lia. rewrite Nat.sub_diag. cbn [nth].
  split; [exact Hv | exact Hr].
Qed.
Lemma sc_val_mem_kept : forall (m m' : word -> option byte) a n v,
  (forall x, a <= x < a + Z.of_nat n -> mbyte tfibsegs m' x = mbyte tfibsegs m x) ->
  val_mem tfibsegs m a n v -> val_mem tfibsegs m' a n v.
Proof. intros m m' a n v Hk Hv k Hkn. rewrite Hk by lia. exact (Hv k Hkn). Qed.
End m.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Local Notation rd W mem := (mrestrict (w_H W) mem).
Section h.
Variable B : asyms.
Variable MT : ameter_ops.

(* ---- the call: cdcU_scribble_text_specX's variables ---------------------------------------------------------- *)
Record sc_ctx : Type := mkSc {
  sg_STK : Z; sg_sp0 : Z; sg_FP : list (Z * Z); sg_ly : alayout; sg_S : astate; sg_W0 : world tfibsegs;
  sg_mem0 : word -> option byte; sg_md0 : Model; sg_own : list (Z * Z);
  sg_lyc : alayout; sg_Sc : astate; sg_W : world tfibsegs; sg_memc : word -> option byte; sg_mdc : Model; sg_k : Z;
  sg_regs : bvmap 5 word; sg_q : Z; sg_o : Z; sg_n : Z; sg_tb : list Z; sg_oj : list Z }.
(* The entry sp, the text's length, ~o as the register holds it, the write set, the zone of the walk's writes. *)
Definition sg_sp (g : sc_ctx) : Z := spZ (sg_regs g).
Definition sg_len (g : sc_ctx) : Z := Z.of_nat (length (sg_tb g)).
Definition sg_noto (g : sc_ctx) : Z := 2 ^ 64 - 1 - sg_o g.
Definition sc_wr (g : sc_ctx) : Z -> Prop := fun x => sg_o g <= x < sg_o g + sg_n g.
Definition sc_zone (g : sc_ctx) (a : Z) : Prop := (sg_sp g - 16 <= a < sg_sp g) \/ (sg_o g <= a < sg_o g + sg_n g).
Definition sc_res (g : sc_ctx) : list Z * Z := scribble_text_spec (sg_tb g) (sg_n g).

(* The contract's premises, in the contract's order. *)
Definition sc_pre (g : sc_ctx) : Prop :=
  cdc_entry tfibsegs B (sg_STK g) (sg_sp0 g) (sg_FP g) (sg_ly g) (sg_S g) (sg_W0 g) (sg_mem0 g) (sg_md0 g)
    (sg_own g) (sg_lyc g) (sg_Sc g) (sg_W g) (sg_memc g) (sg_mdc g) (sg_k g) (sg_regs g) TB_scribble_text /\
  getr (sg_regs g) 10 = w64 (sg_q g) /\
  cstr_rd tfibsegs (sg_W g) (sg_memc g) (sg_sp g) TB_scribble_text (sg_q g) (sg_tb g) /\
  getr (sg_regs g) 11 = w64 (sg_o g) /\ getr (sg_regs g) 12 = w64 (sg_n g) /\
  (0 <= sg_n g < 2 ^ 32 /\ sg_n g = Z.of_nat (length (sg_oj g))) /\
  cdst_ok tfibsegs B (sg_STK g) (sg_sp0 g) (sg_FP g) (sg_ly g) (sg_S g) (sg_lyc g) (sg_Sc g) (sg_own g)
    (sg_W g) (sg_memc g) (sg_sp g) TB_scribble_text (sg_o g) (sg_n g) /\
  garr8 tfibsegs (rd (sg_W g) (sg_memc g)) (sg_o g) (sg_oj g) /\
  (sg_q g + sg_len g <= sg_o g \/ sg_o g + sg_n g <= sg_q g).

(* ---- what every boundary carries --------------------------------------------------------------------------------
   ra, gp, tp, s1 .. s11 as at entry (the walk writes none of them; s0 it writes on the error path of one check
   only, and restores at the return); sp = entry sp - 16; a2 = n, a5 = the shadow offset, a6 = ~o; the two saves
   at entry sp - 8 (ra) and entry sp - 16 (s0); every byte outside the frame and [o, o + n) as at entry; every byte
   present at entry still present. *)
Definition sc_common (g : sc_ctx) (regs2 : bvmap 5 word) (mem2 : word -> option byte) : Prop :=
  Forall (fun r => getr regs2 r = getr (sg_regs g) r) sc_kregs /\
  getr regs2 2 = w64 (sg_sp g - 16) /\ getr regs2 12 = w64 (sg_n g) /\ getr regs2 15 = w64 SHADOW_OFF /\
  getr regs2 16 = w64 (sg_noto g) /\
  val_mem tfibsegs (rd (sg_W g) mem2) (sg_sp g - 8) 8 (raZ (sg_regs g)) /\
  val_mem tfibsegs (rd (sg_W g) mem2) (sg_sp g - 16) 8 (bv_unsigned (getr (sg_regs g) 8)) /\
  (forall a, 0 <= a < 2 ^ 64 -> ~ sc_zone g a ->
     aview tfibsegs (w_H (sg_W g)) mem2 a = aview tfibsegs (w_H (sg_W g)) (sg_memc g) a) /\
  (forall a, apresent (w_H (sg_W g)) (sg_memc g) a -> apresent (w_H (sg_W g)) mem2 a).

(* A boundary: at pc in the call's world, the caller's journal at the current memory, the model's input and output
   as at entry, the common part and P. *)
Definition sc_cut (g : sc_ctx) (pc : Z) (P : bvmap 5 word -> (word -> option byte) -> Prop)
  : world tfibsegs -> config -> Prop :=
  fun W2 c2 => W2 = sg_W g /\ exists regs2 mem2 md2,
    c2 = cfg_at tfibsegs pc regs2 mem2 md2 /\
    ajournal tfibsegs B (sg_STK g) (sg_sp0 g) (sg_FP g) (sg_ly g) (sg_S g) (sg_W0 g) (sg_mem0 g) (sg_md0 g)
      (sg_own g) (sg_lyc g) (sg_Sc g) (sg_W g) mem2 md2 (sg_k g) /\
    same_io (sg_mdc g) md2 /\ sc_common g regs2 mem2 /\ P regs2 mem2.

(* The loop head 0x86544: a0 = i, a7 = j, a1 = o, a3 = q, t0 = q + 1, t1 = 46, t2 = 49, t3 = 57, t5 = 0. The
   terminator lies at or after byte i; outs, the j bytes written, are at o; the rest of the first loop from
   (i, j) and the padding give the result. fuel bounds the text bytes left. *)
Definition P_H (g : sc_ctx) (fuel : nat) : bvmap 5 word -> (word -> option byte) -> Prop :=
  fun regs2 mem2 => exists (i j : Z) (outs : list Z),
    getr regs2 10 = w64 i /\ getr regs2 17 = w64 j /\ getr regs2 11 = w64 (sg_o g) /\
    getr regs2 13 = w64 (sg_q g) /\ getr regs2 5 = w64 (sg_q g + 1) /\
    getr regs2 6 = w64 46 /\ getr regs2 7 = w64 49 /\ getr regs2 28 = w64 57 /\ getr regs2 30 = w64 0 /\
    0 <= i /\ In 0 (skipn (Z.to_nat i) (sg_tb g)) /\ (Z.to_nat (sg_len g - i) <= fuel)%nat /\
    0 <= j <= sg_n g /\ Z.of_nat (length outs) = j /\ garr8 tfibsegs (rd (sg_W g) mem2) (sg_o g) outs /\
    sc_res g = (outs ++ fst (scr_lib (skipn (Z.to_nat i) (sg_tb g)) (Z.to_nat (sg_n g - j))),
                i + snd (scr_lib (skipn (Z.to_nat i) (sg_tb g)) (Z.to_nat (sg_n g - j)))).

(* 0x865c4, a byte that is not '.' followed by a digit 1..9: a0 = i, a7 = j < n, a1 = o, a3 = q, t0 = q + 1,
   t1 = 46, t2 = 49, t3 = 57, t4 = b = q[i], not 0; the output gets b below 0x80, else 0x3f, and the text from byte
   i + 1 gives the rest. *)
Definition P_O (g : sc_ctx) (fuel : nat) : bvmap 5 word -> (word -> option byte) -> Prop :=
  fun regs2 mem2 => exists (i j b : Z) (outs : list Z),
    getr regs2 10 = w64 i /\ getr regs2 17 = w64 j /\ getr regs2 11 = w64 (sg_o g) /\
    getr regs2 13 = w64 (sg_q g) /\ getr regs2 5 = w64 (sg_q g + 1) /\
    getr regs2 6 = w64 46 /\ getr regs2 7 = w64 49 /\ getr regs2 28 = w64 57 /\ getr regs2 29 = w64 b /\
    0 <= i /\ nth (Z.to_nat i) (sg_tb g) 0 = b /\ b <> 0 /\ In 0 (skipn (Z.to_nat i + 1) (sg_tb g)) /\
    (Z.to_nat (sg_len g - (i + 1)) <= fuel)%nat /\
    0 <= j < sg_n g /\ Z.of_nat (length outs) = j /\ garr8 tfibsegs (rd (sg_W g) mem2) (sg_o g) outs /\
    sc_res g = ((outs ++ [if b <? 0x80 then b else 0x3f]) ++
                  fst (scr_lib (skipn (Z.to_nat i + 1) (sg_tb g)) (Z.to_nat (sg_n g - (j + 1)))),
                (i + 1) + snd (scr_lib (skipn (Z.to_nat i + 1) (sg_tb g)) (Z.to_nat (sg_n g - (j + 1))))).

(* The padding 0x8664c: a0 = r the result, a7 = j, a1 = o; the rest of the output is n - j spaces. *)
Definition P_P (g : sc_ctx) : bvmap 5 word -> (word -> option byte) -> Prop :=
  fun regs2 mem2 => exists (r j : Z) (outs : list Z),
    getr regs2 10 = w64 r /\ getr regs2 17 = w64 j /\ getr regs2 11 = w64 (sg_o g) /\
    0 <= j <= sg_n g /\ Z.of_nat (length outs) = j /\ garr8 tfibsegs (rd (sg_W g) mem2) (sg_o g) outs /\
    sc_res g = (outs ++ repeat 0x20 (Z.to_nat (sg_n g - j)), r).

(* The padding loop 0x8665c, kk = n - j spaces left: a0 = r, a7 = j, a1 = a3 = o + j, a4 = 32. *)
Definition P_L (g : sc_ctx) (kk : nat) : bvmap 5 word -> (word -> option byte) -> Prop :=
  fun regs2 mem2 => exists (r j : Z) (outs : list Z),
    getr regs2 10 = w64 r /\ getr regs2 17 = w64 j /\
    getr regs2 11 = w64 (sg_o g + j) /\ getr regs2 13 = w64 (sg_o g + j) /\ getr regs2 14 = w64 32 /\
    0 <= j < sg_n g /\ Z.of_nat kk = sg_n g - j /\
    Z.of_nat (length outs) = j /\ garr8 tfibsegs (rd (sg_W g) mem2) (sg_o g) outs /\
    sc_res g = (outs ++ repeat 0x20 (Z.to_nat (sg_n g - j)), r).

(* The return 0x86698: a0 is the result, the n bytes at o the output. *)
Definition P_X (g : sc_ctx) : bvmap 5 word -> (word -> option byte) -> Prop :=
  fun regs2 mem2 =>
    getr regs2 10 = w64 (snd (sc_res g)) /\ garr8 tfibsegs (rd (sg_W g) mem2) (sg_o g) (fst (sc_res g)).

(* The contract's post. *)
Definition sc_post (g : sc_ctx) : world tfibsegs -> config -> Prop :=
  cdc_post tfibsegs B MT (sg_STK g) (sg_sp0 g) (sg_FP g) (sg_ly g) (sg_S g) (sg_W0 g) (sg_mem0 g) (sg_md0 g)
    (sg_own g) (sg_k g) (sg_regs g) TB_scribble_text (sc_wr g) (sg_lyc g) (sg_Sc g) (sg_W g) (sg_memc g) (sg_mdc g)
    (fun W2 mem2 regs2 => getr regs2 10 = w64 (snd (sc_res g)) /\
                          garr8 tfibsegs (rd W2 mem2) (sg_o g) (fst (sc_res g))).

(* ---- the segments ------------------------------------------------------------------------------------------------ *)
(* S0: entry -> the loop head with i = j = 0. *)
Definition sc_seg_S0 : Prop :=
  forall g, sc_pre g ->
  SRr tfibsegs (sg_W g) (cfg_at tfibsegs B_ST (sg_regs g) (sg_memc g) (sg_mdc g))
    (sc_cut g PC_H (P_H g (length (sg_tb g)))).
(* Ha: one pass of the first loop, up to the store of a byte that is not '.' and a digit. *)
Definition sc_seg_Ha : Prop :=
  forall g fuel W2 c2, sc_pre g -> sc_cut g PC_H (P_H g (S fuel)) W2 c2 ->
  SRr tfibsegs W2 c2 (fun W3 c3 => sc_cut g PC_H (P_H g fuel) W3 c3 \/ sc_cut g PC_P (P_P g) W3 c3 \/
                                   sc_cut g PC_O (P_O g fuel) W3 c3).
(* Hb: the store of a byte that is not '.' and a digit, back to the loop head. *)
Definition sc_seg_Hb : Prop :=
  forall g fuel W2 c2, sc_pre g -> sc_cut g PC_O (P_O g fuel) W2 c2 ->
  SRr tfibsegs W2 c2 (sc_cut g PC_H (P_H g fuel)).
(* P: the test of the padding. *)
Definition sc_seg_P : Prop :=
  forall g W2 c2, sc_pre g -> sc_cut g PC_P (P_P g) W2 c2 ->
  SRr tfibsegs W2 c2 (fun W3 c3 => (exists kk, sc_cut g PC_L (P_L g kk) W3 c3) \/ sc_cut g PC_X (P_X g) W3 c3).
(* L: one space of the padding loop. *)
Definition sc_seg_L : Prop :=
  forall g kk W2 c2, sc_pre g -> sc_cut g PC_L (P_L g (S kk)) W2 c2 ->
  SRr tfibsegs W2 c2 (fun W3 c3 => sc_cut g PC_L (P_L g kk) W3 c3 \/ sc_cut g PC_X (P_X g) W3 c3).
(* X: the epilogue, the post. *)
Definition sc_seg_X : Prop :=
  forall g W2 c2, sc_pre g -> sc_cut g PC_X (P_X g) W2 c2 -> SRr tfibsegs W2 c2 (sc_post g).

(* ---- the composition --------------------------------------------------------------------------------------------- *)
Lemma P_H_zero : forall g regs2 mem2, P_H g 0 regs2 mem2 -> False.
Proof.
intros g regs2 mem2 (i & j & outs & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hi & Hin & Hf & _).
pose proof (sc_in_skipn_lt 0 (sg_tb g) (Z.to_nat i) Hin) as Hl. unfold sg_len in Hf. lia.
Qed.
Lemma P_L_zero : forall g regs2 mem2, P_L g 0 regs2 mem2 -> False.
Proof. intros g regs2 mem2 (r & j & outs & _ & _ & _ & _ & _ & Hj & Hk & _). cbn in Hk. lia. Qed.
Lemma sc_cut_P : forall g pc (P : bvmap 5 word -> (word -> option byte) -> Prop) W2 c2,
  sc_cut g pc P W2 c2 -> exists regs2 mem2, P regs2 mem2.
Proof. intros g pc P W2 c2 (_ & regs2 & mem2 & md2 & _ & _ & _ & _ & HP). exists regs2, mem2. exact HP. Qed.

Section comp.
Hypothesis HS0 : sc_seg_S0.
Hypothesis HHa : sc_seg_Ha.
Hypothesis HHb : sc_seg_Hb.
Hypothesis HP : sc_seg_P.
Hypothesis HL : sc_seg_L.
Hypothesis HX : sc_seg_X.
Lemma sc_L_closed : forall kk g W2 c2, sc_pre g -> sc_cut g PC_L (P_L g kk) W2 c2 -> SRr tfibsegs W2 c2 (sc_post g).
Proof.
induction kk as [|kk IH]; intros g W2 c2 Hpre Hc.
- exfalso. destruct (sc_cut_P g PC_L _ W2 c2 Hc) as (regs2 & mem2 & H). exact (P_L_zero g regs2 mem2 H).
- apply (SRr_bind tfibsegs _ _ _ _ (HL g kk W2 c2 Hpre Hc)). intros W3 c3 _ [H | H].
  + exact (IH g W3 c3 Hpre H).
  + exact (HX g W3 c3 Hpre H).
Qed.
Lemma sc_P_closed : forall g W2 c2, sc_pre g -> sc_cut g PC_P (P_P g) W2 c2 -> SRr tfibsegs W2 c2 (sc_post g).
Proof.
intros g W2 c2 Hpre Hc.
apply (SRr_bind tfibsegs _ _ _ _ (HP g W2 c2 Hpre Hc)). intros W3 c3 _ [(kk & H) | H].
- exact (sc_L_closed kk g W3 c3 Hpre H).
- exact (HX g W3 c3 Hpre H).
Qed.
Lemma sc_H_closed : forall fuel g W2 c2, sc_pre g -> sc_cut g PC_H (P_H g fuel) W2 c2 ->
  SRr tfibsegs W2 c2 (sc_post g).
Proof.
induction fuel as [|fuel IH]; intros g W2 c2 Hpre Hc.
- exfalso. destruct (sc_cut_P g PC_H _ W2 c2 Hc) as (regs2 & mem2 & H). exact (P_H_zero g regs2 mem2 H).
- apply (SRr_bind tfibsegs _ _ _ _ (HHa g fuel W2 c2 Hpre Hc)). intros W3 c3 _ [H | [H | H]].
  + exact (IH g W3 c3 Hpre H).
  + exact (sc_P_closed g W3 c3 Hpre H).
  + apply (SRr_bind tfibsegs _ _ _ _ (HHb g fuel W3 c3 Hpre H)). intros W4 c4 _ H4.
    exact (IH g W4 c4 Hpre H4).
Qed.
Theorem sc_spec_of_segs : cdcU_scribble_text_specX tfibsegs B MT B_ST.
Proof.
unfold cdcU_scribble_text_specX.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs q o n tb oj
  HE H10 HSTR H11 H12 HN HDST HOJ HDJ.
set (g := mkSc STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs q o n tb oj).
assert (Hpre : sc_pre g)
  by exact (conj HE (conj H10 (conj HSTR (conj H11 (conj H12 (conj HN (conj HDST (conj HOJ HDJ)))))))).
apply (SRr_bind tfibsegs _ _ _ _ (HS0 g Hpre)). intros W2 c2 _ Hc.
exact (sc_H_closed (length tb) g W2 c2 Hpre Hc).
Qed.
End comp.

(* ---- what a segment reads off the contract ------------------------------------------------------------------------- *)
Lemma sc_stack : forall g, sc_pre g ->
  alloc_ceiling <= sg_sp g - 16 /\ sg_sp g <= 2 ^ 47 /\ 2 ^ 46 + 16 <= sg_sp g /\ sg_sp g mod 16 = 0 /\
  sg_sp0 g - sg_STK g <= sg_sp g - 16 /\ sg_sp g <= sg_sp0 g /\
  (forall a, sg_sp g - 16 <= a < sg_sp g -> apresent (w_H (sg_W g)) (sg_memc g) a).
Proof.
intros g ((HJ & _ & _ & _ & _ & Hal16 & Hwlo & Hwhi & _) & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (_ & HSTK & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold TB_scribble_text in *. unfold sg_sp.
split; [lia|]. split; [lia|]. split; [lia|]. split; [exact Hal16|]. split; [lia|]. split; [lia|].
intros a Ha. apply Hpres. lia.
Qed.

(* The text: its bytes, its terminator, its range below 2 ^ 63 and off the frame and the output. *)
Lemma sc_text : forall g, sc_pre g ->
  0 < sg_q g /\ sg_q g + sg_len g <= 2 ^ 63 /\ In 0 (sg_tb g) /\ 0 < sg_len g /\
  garr8 tfibsegs (rd (sg_W g) (sg_memc g)) (sg_q g) (sg_tb g) /\
  range_addressable (aview tfibsegs (w_H (sg_W g)) (sg_memc g)) SHADOW_OFF (sg_q g) (sg_len g) /\
  amem_range (sg_q g) (sg_len g) /\
  (forall a, sg_q g <= a < sg_q g + sg_len g -> ~ sc_zone g a).
Proof.
intros g (HE & _ & (Hq0 & HG & Hin & (_ & Hql & _ & HRA & _ & Ham & Hoff)) & _ & _ & _ &
  (Ho0 & Hon & _) & _ & HDJ).
unfold coff_win, TB_scribble_text in Hoff. fold (sg_len g) in *.
assert (Hlen : 0 < sg_len g).
{ unfold sg_len. destruct (sg_tb g); [destruct Hin | cbn [length]; lia]. }
split; [exact Hq0|]. split; [exact Hql|]. split; [exact Hin|]. split; [exact Hlen|].
split; [exact HG|]. split; [exact HRA|]. split; [exact Ham|].
intros a Ha Hz. unfold sc_zone in Hz. lia.
Qed.

(* The output: its range below 2 ^ 63, off the frame, writable and marked usable, n < 2 ^ 32. *)
Lemma sc_out : forall g, sc_pre g ->
  0 < sg_o g /\ sg_o g + sg_n g <= 2 ^ 63 /\ 0 <= sg_n g < 2 ^ 32 /\
  (sg_o g + sg_n g <= sg_sp g - 16 \/ sg_sp g <= sg_o g) /\
  tdst_ok B (sg_lyc g) (sg_Sc g) (sg_o g) (sg_n g) /\
  twr_ok tfibsegs B (sg_STK g) (sg_sp0 g) (sg_FP g) (sg_ly g) (sg_S g) (sg_lyc g) (sg_Sc g) (sg_own g)
    (sg_W g) (sg_memc g) (sg_sp g) (sg_o g) (sg_n g) /\
  range_addressable (aview tfibsegs (w_H (sg_W g)) (sg_memc g)) SHADOW_OFF (sg_o g) (sg_n g) /\
  amem_range (sg_o g) (sg_n g) /\
  (sg_q g + sg_len g <= sg_o g \/ sg_o g + sg_n g <= sg_q g).
Proof.
intros g (_ & _ & _ & _ & _ & (Hn & _) & (Ho0 & Hon & Htd & Htw & HRA & _ & Ham & Hoff) & _ & HDJ).
unfold coff_win, TB_scribble_text in Hoff.
repeat (split; [assumption|]). exact HDJ.
Qed.

(* A boundary at the end of a run of a loop segment: the run kept the journal's layout and state, wrote only bytes
   of [o, o + n) and kept the registers of sc_common; P holds of the new state. *)
Lemma sc_cut_close : forall g pc (P : bvmap 5 word -> (word -> option byte) -> Prop) regs2 mem2 md2 ms md3,
  sc_pre g -> same_io (sg_mdc g) md2 -> sc_common g regs2 mem2 ->
  ajournal tfibsegs B (sg_STK g) (sg_sp0 g) (sg_FP g) (sg_ly g) (sg_S g) (sg_W0 g) (sg_mem0 g) (sg_md0 g)
    (sg_own g) (sg_lyc g) (sg_Sc g) (sg_W g) (ms_mem ms) md3 (sg_k g) ->
  same_io md2 md3 ->
  ms = mkst (ms_regs ms) (Z_to_bv 64 pc) (ms_mem ms) (seg_rom tfibsegs) ->
  Forall (fun r => getr (ms_regs ms) r = getr regs2 r) (sc_kregs ++ sc_lregs) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (sg_o g <= a < sg_o g + sg_n g) ->
     aview tfibsegs (w_H (sg_W g)) (ms_mem ms) a = aview tfibsegs (w_H (sg_W g)) mem2 a) ->
  (forall a, apresent (w_H (sg_W g)) mem2 a -> apresent (w_H (sg_W g)) (ms_mem ms) a) ->
  P (ms_regs ms) (ms_mem ms) ->
  sc_cut g pc P (sg_W g) (mkCfg ms md3).
Proof.
intros g pc P regs2 mem2 md2 ms md3 Hpre Hio HC HJ3 Hio3 Hms HR KE KP HPk.
destruct (sc_stack g Hpre) as (Hceil & H47 & H46 & Hal & Hwin & Hsp0 & _).
destruct (sc_out g Hpre) as (Ho0 & Hon & Hn & Hoff & _).
destruct HC as (HK & R2 & R12 & R15 & R16 & Vra & Vs0 & KC & PC).
apply Forall_app in HR as (HRk & HRl).
unfold sc_lregs in HRl. repeat (apply Forall_cons_iff in HRl as (? & HRl)).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (KM : forall x, sg_sp g - 16 <= x < sg_sp g ->
  mbyte tfibsegs (rd (sg_W g) (ms_mem ms)) x = mbyte tfibsegs (rd (sg_W g) mem2) x).
{ intros x Hx. apply (mbyte_of_aview tfibsegs). apply KE; lia. }
split; [reflexivity|]. exists (ms_regs ms), (ms_mem ms), md3.
split; [unfold cfg_at, w64; rewrite Hms at 1; reflexivity|].
split; [exact HJ3|]. split; [exact (same_io_trans _ _ _ Hio Hio3)|].
split; [|exact HPk].
split.
{ rewrite Forall_forall in HK, HRk |- *. intros r Hr. rewrite (HRk r Hr). exact (HK r Hr). }
split; [congruence|]. split; [congruence|]. split; [congruence|]. split; [congruence|].
split; [apply (sc_val_mem_kept (rd (sg_W g) mem2)); [intros x Hx; apply KM; cbn in Hx; lia | exact Vra]|].
split; [apply (sc_val_mem_kept (rd (sg_W g) mem2)); [intros x Hx; apply KM; cbn in Hx; lia | exact Vs0]|].
split.
- intros a Ha Hz. rewrite (KE a Ha); [exact (KC a Ha Hz)|]. intros Hx. apply Hz. right. exact Hx.
- intros a Ha. apply KP. apply PC. exact Ha.
Qed.

(* ---- the memory a boundary reads, from the kept fact ---------------------------------------------------------- *)
Definition sc_kept (g : sc_ctx) (m2 : word -> option byte) : Prop :=
  forall a, 0 <= a < 2 ^ 64 -> ~ sc_zone g a ->
    aview tfibsegs (w_H (sg_W g)) m2 a = aview tfibsegs (w_H (sg_W g)) (sg_memc g) a.

(* Both ranges lie in application memory below 2 ^ 47. *)
Lemma sc_amem47 : forall a len, 0 <= a -> 0 <= len -> amem_range a len -> a + len <= 2 ^ 47 - 1.
Proof.
intros a len Ha Hl Ham. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold amem_range in Ham. rewrite C3, C4, C5 in Ham. lia.
Qed.

(* A shadow byte of a range in application memory is off the walk's zone. *)
Lemma sc_shadow_off_zone : forall g x, sc_pre g -> 0 <= x < 2 ^ 47 ->
  0 <= SHADOW_OFF + x / 8 < 2 ^ 64 /\ ~ sc_zone g (SHADOW_OFF + x / 8).
Proof.
intros g x Hpre Hx.
destruct (sc_stack g Hpre) as (Hceil & H47 & H46 & _).
destruct (sc_out g Hpre) as (Ho0 & Hon & Hn & _ & _ & _ & _ & Ham & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold amem_range in Ham. rewrite C3, C4, C5 in Ham.
assert (D0 : 0 <= x / 8) by (apply Z.div_pos; lia).
assert (D1 : x / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia).
unfold SHADOW_OFF, sc_zone. split; [lia|]. intros [Hz | Hz]; lia.
Qed.

(* The usable marks of a range in application memory, at a memory that kept everything off the zone. *)
Lemma sc_ra_kept : forall g m2, sc_pre g -> sc_kept g m2 ->
  forall a len, 0 <= a -> 0 <= len -> amem_range a len ->
  range_addressable (aview tfibsegs (w_H (sg_W g)) (sg_memc g)) SHADOW_OFF a len ->
  range_addressable (aview tfibsegs (w_H (sg_W g)) m2) SHADOW_OFF a len.
Proof.
intros g m2 Hpre KE a len Ha Hl Ham HRA x Hx.
destruct (HRA x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok].
pose proof (sc_amem47 a len Ha Hl Ham) as H47.
destruct (sc_shadow_off_zone g x Hpre ltac:(lia)) as (Hb & Hz).
unfold shadow_of_addr in *. rewrite (KE _ Hb Hz). exact Hs.
Qed.

(* Byte k of the text, at a memory that kept everything off the zone. *)
Lemma sc_text_val : forall g m2, sc_pre g -> sc_kept g m2 ->
  forall k, (k < length (sg_tb g))%nat ->
  val_mem tfibsegs (rd (sg_W g) m2) (sg_q g + Z.of_nat k) 1 (nth k (sg_tb g) 0) /\ 0 <= nth k (sg_tb g) 0 < 256.
Proof.
intros g m2 Hpre KE k Hk.
destruct (sc_text g Hpre) as (Hq0 & Hql & _ & _ & HG & _ & _ & Hoff).
destruct (HG k Hk) as (Hv & Hr). split; [|exact Hr].
apply (sc_val_mem_kept (rd (sg_W g) (sg_memc g))); [|exact Hv].
intros x Hx. apply (mbyte_of_aview tfibsegs). unfold sg_len in *.
apply KE; [lia | apply Hoff; cbn in Hx; lia].
Qed.

(* A byte of [o, o + n) is present at a memory where every byte present at entry is. *)
Lemma sc_out_present : forall g m2, sc_pre g ->
  (forall a, apresent (w_H (sg_W g)) (sg_memc g) a -> apresent (w_H (sg_W g)) m2 a) ->
  forall a, sg_o g <= a < sg_o g + sg_n g -> apresent (w_H (sg_W g)) m2 a.
Proof.
intros g m2 Hpre KP a Ha. destruct (sc_out g Hpre) as (_ & _ & _ & _ & _ & Htw & _).
apply KP. exact (proj1 (proj2 (Htw a Ha))).
Qed.
End h.
End d.
