(* The boundary layer of diginet_scribble_text's walk in image A (fuzz_codec.asan 0x85cc4, 88 instructions, frame
   16, one call: __asan_memset): the state at each segment boundary, the statement of each segment, and their
   composition into cdc_scribble_text_specX (proved here, by induction over the loop). The segments are proved
   against these statements in diginet_scribble_text_A_<seg>.v.

   The code (a0 = q the text, a1 = o the output, a2 = n its length):
   S0  0x85cc4 .. 0x85d1c: sp -= 16, ra at sp + 8, s0 at sp; o = 0 (to 0x85dd0) and q = 0 (to 0x85dd8) are not
       taken; a4 := the shadow offset through the 8-byte cell at 0x9db10; the instrumented check of q (0x85cec),
       t1 := q[0], s0 := 0, a5 := 0; t1 = 0 or n = 0 go to 0x85de0; else s0 = i := 0, a5 = j := 0, a6 := q + 1,
       a7 := 46, t0 := 8, to the loop head 0x85d1c.
   H   0x85d1c .. 0x85d64: t1 = q[i] is not 0 and j < n. For t1 = '.' the instrumented check of q + i + 1
       (0x85d28) and lbu a3 := q[i + 1]; a digit 1..9 sets t1 := a3 - 26, t2 := 2. Any other case goes to 0x85d54:
       t1 stays below 0x80, else t1 := 0x3f; t2 := 1.
   T   0x85d64 .. : the instrumented check of o + j (0x85d68), t1 at o + j, s0 += t2, the instrumented check of
       q + s0 (0x85d84), t1 := q[s0], a5 += 1; t1 = 0 goes to 0x85de0, j < n back to 0x85d1c, else to 0x85de0.
   P   0x85de0: j >= n goes to 0x85df4; else __asan_memset(o + j, 0x20, n - j) at 0x85df0.
   X   0x85df4 .. ret: a0 := s0, ra and s0 back from the frame, sp += 16.
   Every instrumented check branches to an error report (0x85dc0 .. 0x85dcc, 0x85da8, 0x85db4, 0x85e08 ..); none of
   them is reached.

   A boundary is a predicate on the configuration: the caller's journal at the current memory, the model's input
   and output as at entry, the registers and memory every boundary carries (sc_common) and the boundary's own
   facts. A segment builds its own symbolic state from these facts. *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0m.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YCeo.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YC85.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw0 ACef AF0l ACej ACeh ACem ACep.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw1 AWalkFw2 ACfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase CPgChkC CPgWalk.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* The function and its boundaries. *)
Definition A_ST : Z := 0x85cc4.     (* diginet_scribble_text *)
Definition PC_H : Z := 0x85d1c.     (* zext.b a3,t1: the loop head *)
Definition PC_T : Z := 0x85d64.     (* add a3,a1,a5: the store of an output byte *)
Definition PC_P : Z := 0x85de0.     (* bgeu a5,a2: the padding *)
Definition PC_X : Z := 0x85df4.     (* mv a0,s0: the return *)

(* The registers every boundary keeps at their entry values: gp, tp, s1..s11 (the walk writes none of them and the
   runtime call keeps them; ra the call writes, and the return takes it back from the frame). *)
Definition sc_kregs : list (bv 5) := [3; 4; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.

(* every register a boundary keeps, and sp, is callee-saved *)
Lemma sc_kregs_cs : forall rr, In rr (sc_kregs ++ [2%bv]) -> acallee_saved (bv_unsigned rr).
Proof.
intros rr H. unfold sc_kregs in H. cbn in H. unfold acallee_saved.
destruct H as [E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[]]]]]]]]]]]]]]]; rewrite <- E;
match goal with |- context [bv_unsigned ?x] =>
  let z := eval vm_compute in (bv_unsigned x) in
  replace (bv_unsigned x) with z by (vm_compute; reflexivity) end; lia.
Qed.

(* the obligation of one instrumented check, from a range the contract marks usable *)
Lemma sc_obl_of : forall (W : world tfibsegs) mem2 (E : env) x len a m,
  range_addressable (aview tfibsegs (w_H W) mem2) SHADOW_OFF a m ->
  ew E 32 = Z_to_bv 64 SB -> a <= x -> x + len <= a + m ->
  range_addressable (rd_of tfibsegs (mrestrict (w_H W) mem2)) (U E CW_Bx) x len.
Proof.
intros W mem2 E x len a m HRA E32 H1 H2. rewrite (cw_U_Bx E E32). rewrite <- (aview_rd_of tfibsegs).
eapply range_addressable_sub; [exact HRA | lia | lia].
Qed.

Lemma sc_app_snoc : forall (l : list Z) (x : Z) (m : list Z), (l ++ [x]) ++ m = l ++ x :: m.
Proof. intros l x m. induction l as [|a l IH]; [reflexivity | cbn; rewrite IH; reflexivity]. Qed.

Lemma sc_denot_add3l : forall (E : env) a b c x y z,
  ew E a = Z_to_bv 64 x -> ew E b = Z_to_bv 64 y -> ew E c = Z_to_bv 64 z ->
  0 <= x -> 0 <= y -> 0 <= z -> x + y + z < 2 ^ 64 ->
  sv_denot E (SAlu ALU_ADD (SAlu ALU_ADD (SOff a 0) (SOff b 0)) (SOff c 0)) = Z_to_bv 64 (x + y + z).
Proof.
intros E a b c x y z Ha Hb Hc H1 H2 H3 H4. rewrite denot_lit_U. f_equal.
rewrite !U_SAlu. cbn [zalu_raw].
rewrite (U_atom E a x Ha ltac:(lia)), (U_atom E b y Hb ltac:(lia)), (U_atom E c z Hc ltac:(lia)).
unfold zcanon, M64. rewrite Z.add_mod_idemp_l by lia. apply Z.mod_small. lia.
Qed.

(* a callee-saved register of a call, at its bv index *)
Lemma sc_pres_at : forall (regs regs' : bvmap 5 word) (rr : bv 5),
  aregs_preserved regs regs' -> acallee_saved (bv_unsigned rr) -> getr regs' rr = getr regs rr.
Proof.
intros regs regs' rr HP Hcs. pose proof (HP (bv_unsigned rr) Hcs) as H.
rewrite Z_to_bv_bv_unsigned in H. exact H.
Qed.

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
(* the loop and the padding give exactly k output bytes *)
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
(* the text from byte i when byte i is 0 *)
Lemma sc_lib_at_zero : forall tb i k, (i < length tb)%nat -> nth i tb 0 = 0 ->
  scr_lib (skipn i tb) k = (repeat 0x20 k, 0).
Proof. intros tb i k Hi H0. rewrite (sc_skipn_cons tb i 0 Hi), H0. apply sc_lib_zero. Qed.
(* one step of the loop: byte i is not 0, so byte i + 1 exists *)
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


(* ======================= one byte, as the walk reads and writes it ======================= *)
Section av. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma sc_val_of_aview : forall H m a v, aview tfibsegs H m a = Some v -> val_mem tfibsegs (mrestrict H m) a 1 v.
Proof.
intros H m a v Hv j Hj. assert (j = 0%nat) as -> by lia. change (Z.of_nat 0) with 0. rewrite Z.add_0_r.
destruct (aview_byte tfibsegs H m a v Hv) as (b & Hb & -> & Hr). rewrite Hb. f_equal.
unfold YO0f.le_byte. change (2 ^ (8 * Z.of_nat 1)) with 256. change (8 * Z.of_nat 0) with 0.
rewrite Z.shiftr_0_r, (Z.mod_small (bv_unsigned b) 256) by lia.
rewrite (Z.mod_small (bv_unsigned b) 256) by lia. symmetry. apply Z_to_bv_bv_unsigned.
Qed.
Lemma sc_aview_of_val : forall H m a v, 0 <= v < 256 -> val_mem tfibsegs (mrestrict H m) a 1 v ->
aview tfibsegs H m a = Some v.
Proof.
intros H m a v Hv Hm. pose proof (Hm 0%nat ltac:(lia)) as H0. change (Z.of_nat 0) with 0 in H0.
rewrite Z.add_0_r in H0. unfold aview. rewrite H0. cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
unfold YO0f.le_byte. change (2 ^ (8 * Z.of_nat 1)) with 256. change (8 * Z.of_nat 0) with 0.
rewrite Z.shiftr_0_r. rewrite !Z.mod_mod by lia. apply Z.mod_small. exact Hv.
Qed.
Lemma sc_grow_of_apresent : forall (H : word -> bool) m1 m2,
(forall a, apresent H m1 a -> apresent H m2 a) ->
mem_grows (mrestrict H m1) (mrestrict H m2).
Proof.
intros H m1 m2 HP x Hx. unfold mrestrict in *.
destruct (H x) eqn:EH; [exfalso; apply Hx; reflexivity|].
destruct (m1 x) as [b|] eqn:E1; [|exfalso; apply Hx; reflexivity].
destruct (HP (bv_unsigned x)) as [_ [b' Hb']].
- split; [rewrite Z_to_bv_bv_unsigned; exact EH | exists b; rewrite Z_to_bv_bv_unsigned; exact E1].
- rewrite Z_to_bv_bv_unsigned in Hb'. rewrite Hb'. discriminate.
Qed.
Lemma sc_nth_rep : forall (v : Z) m j, (j < m)%nat -> nth j (repeat v m) 0 = v.
Proof. intros v m. induction m as [|m IH]; intros j Hj; [lia|]. destruct j; [reflexivity|]. cbn. apply IH. lia. Qed.
(* a row kept, then k spaces written after it *)
Lemma sc_garr8_snoc_rep : forall (W : world tfibsegs) m m' q l k,
  garr8 tfibsegs (mrestrict (w_H W) m) q l ->
  (forall x, q <= x < q + Z.of_nat (length l) ->
     mbyte tfibsegs (mrestrict (w_H W) m') x = mbyte tfibsegs (mrestrict (w_H W) m) x) ->
  (forall i : nat, (i < k)%nat -> aview tfibsegs (w_H W) m' (q + (Z.of_nat (length l) + Z.of_nat i)) = Some 32) ->
  garr8 tfibsegs (mrestrict (w_H W) m') q (l ++ repeat 32 k).
Proof.
intros W m m' q l k Hg Hk Hp jj Hjj. rewrite length_app, repeat_length in Hjj.
destruct (Nat.lt_ge_cases jj (length l)) as [Hlt | Hge].
- rewrite app_nth1 by exact Hlt. destruct (Hg jj Hlt) as (Hv & Hr). split; [|exact Hr].
  intros t Ht. assert (t = 0%nat) by lia. subst t. rewrite Hk by lia. exact (Hv 0%nat Ht).
- rewrite app_nth2 by lia. rewrite (sc_nth_rep 32 k (jj - length l) ltac:(lia)). split; [|lia].
  apply sc_val_of_aview.
  replace (q + Z.of_nat jj) with (q + (Z.of_nat (length l) + Z.of_nat (jj - length l))) by lia.
  apply Hp. lia.
Qed.
End av.

(* ======================= the walk's arithmetic ======================= *)
(* `sub a2,a2,a5` as the image writes it: a2 + a5 * (-1) *)
Lemma sc_denot_sub : forall E a b x y, ew E a = Z_to_bv 64 x -> ew E b = Z_to_bv 64 y ->
0 <= y <= x -> x < 2 ^ 64 ->
sv_denot E (SAlu ALU_ADD (SOff a 0) (SMd M_MUL (SOff b 0) (SLit (-1)))) = Z_to_bv 64 (x - y).
Proof.
intros E a b x y Ha Hb H1 H2. rewrite denot_lit_U. f_equal.
rewrite U_SAlu, U_SMd, (U_atom E a x Ha ltac:(lia)), (U_atom E b y Hb ltac:(lia)), U_SLit.
cbn [zalu_raw zmd_raw]. unfold zcanon, M64. change ((-1) mod 2 ^ 64) with 18446744073709551615.
rewrite Z.add_mod_idemp_r by lia. replace (x + y * 18446744073709551615) with ((x - y) + y * 2 ^ 64) by lia.
rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.
(* the shadow hull of a subrange lies inside the hull of the range *)
Lemma sc_hull_sub : forall rd a m a' m', shadow_hull_vis rd a m -> a <= a' -> 0 < m' -> a' + m' <= a + m ->
shadow_hull_vis rd a' m'.
Proof.
intros rd a m a' m' HH Ha Hm Hs s Hsin. apply HH. unfold shadow_addr in *.
assert (D0 : a / 8 <= a' / 8) by (apply Z.div_le_mono; lia).
assert (D1 : (SHADOW_OFF + a / 8) / 8 <= (SHADOW_OFF + a' / 8) / 8) by (apply Z.div_le_mono; lia).
assert (D2 : (a' + m' - 1) / 8 <= (a + m - 1) / 8) by (apply Z.div_le_mono; lia).
assert (D3 : (SHADOW_OFF + (a' + m' - 1) / 8) / 8 <= (SHADOW_OFF + (a + m - 1) / 8) / 8)
  by (apply Z.div_le_mono; lia).
lia.
Qed.
(* the byte test the code makes: (y - 49) mod 256 <= 8 is exactly 0x31 <= y <= 0x39 *)
Lemma sc_digit : forall y, 0 <= y < 256 -> ((y - 49) mod 256 <=? 8) = ((0x31 <=? y) && (y <=? 0x39)).
Proof.
intros y Hy.
destruct (Z.leb_spec 0x31 y) as [H1|H1]; cbn [andb].
- destruct (Z.leb_spec y 0x39) as [H2|H2].
  + rewrite (Z.mod_small (y - 49) 256) by lia. apply Z.leb_le. lia.
  + rewrite (Z.mod_small (y - 49) 256) by lia. apply Z.leb_gt. lia.
- replace (y - 49) with ((y + 207) + (-1) * 256) by lia. rewrite Z.mod_add by lia.
  rewrite (Z.mod_small (y + 207) 256) by lia. apply Z.leb_gt. lia.
Qed.
Lemma sc_and255 : forall x, 0 <= x -> Z.land x 255 = x mod 256.
Proof. intros x Hx. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma sc_mod_sub : forall y, 0 <= y < 256 -> ((y - 49) mod 2 ^ 64) mod 256 = (y - 49) mod 256.
Proof.
intros y Hy. destruct (Z.le_gt_cases 49 y) as [H|H].
- rewrite (Z.mod_small (y - 49) (2 ^ 64)) by lia. reflexivity.
- replace ((y - 49) mod 2 ^ 64) with (y - 49 + 2 ^ 64)
    by (rewrite <- (Z.mod_add (y - 49) 1 (2 ^ 64)) by lia; rewrite Z.mod_small by lia; lia).
  replace (y - 49 + 2 ^ 64) with ((y - 49) + 72057594037927936 * 256) by lia.
  apply Z.mod_add. lia.
Qed.
(* `slli a3,t1,0x38; bgez a3` is the test t1 < 0x80 on a byte *)
Lemma sc_br_sign : forall (E : env) m v, ew E m = Z_to_bv 64 v -> 0 <= v < 256 ->
branch_taken BC_GE (sv_denot E (SAlu ALU_SLL (SOff m 0) (SLit 56))) (sv_denot E (SLit 0)) = (v <? 128).
Proof.
intros E m v Hm Hv.
assert (HU : U E (SAlu ALU_SLL (SOff m 0) (SLit 56)) = v * 2 ^ 56).
{ rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E m v Hm ltac:(lia)), U_SLit.
  change (Z.land (zcanon 56) 63) with 56. rewrite Z.shiftl_mul_pow2 by lia.
  apply zcanon_id. unfold M64. lia. }
rewrite (denot_lit_U E (SAlu ALU_SLL (SOff m 0) (SLit 56))), (denot_lit_U E (SLit 0)), HU, U_SLit.
change (zcanon 0) with 0.
cbn [branch_taken]. unfold bv_lts. rewrite !Z_to_bv_signed.
rewrite (bv_swrap_small 64 0) by (change (bv_half_modulus 64) with (2 ^ 63); lia).
destruct (Z.ltb_spec v 128) as [Hlt | Hge].
- rewrite bv_swrap_small by (change (bv_half_modulus 64) with (2 ^ 63); nia).
  apply negb_true_iff. apply Z.ltb_ge. nia.
- unfold bv_swrap, bv_wrap. change (bv_half_modulus 64) with (2 ^ 63). change (bv_modulus 64) with (2 ^ 64).
  replace ((v * 2 ^ 56 + 2 ^ 63) mod 2 ^ 64) with (v * 2 ^ 56 - 2 ^ 63)
    by (replace (v * 2 ^ 56 + 2 ^ 63) with ((v * 2 ^ 56 - 2 ^ 63) + 1 * 2 ^ 64) by lia;
        rewrite Z.mod_add by lia; rewrite Z.mod_small by nia; lia).
  apply negb_false_iff. apply Z.ltb_lt. nia.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Local Notation rd W mem := (mrestrict (w_H W) mem).
Section h.
Variable B : asyms.
Variable MT : ameter_ops.

(* ---- the call: cdc_scribble_text_specX's variables ------------------------------------------------------------ *)
Record sc_ctx : Type := mkSc {
  sg_STK : Z; sg_sp0 : Z; sg_FP : list (Z * Z); sg_ly : alayout; sg_S : astate; sg_W0 : world tfibsegs;
  sg_mem0 : word -> option byte; sg_md0 : Model; sg_own : list (Z * Z);
  sg_lyc : alayout; sg_Sc : astate; sg_W : world tfibsegs; sg_memc : word -> option byte; sg_mdc : Model; sg_k : Z;
  sg_regs : bvmap 5 word; sg_q : Z; sg_o : Z; sg_n : Z; sg_tb : list Z; sg_oj : list Z }.
(* The entry sp, the text's length, the write set, the zone of the walk's writes, the result. *)
Definition sg_sp (g : sc_ctx) : Z := spZ (sg_regs g).
Definition sg_len (g : sc_ctx) : Z := Z.of_nat (length (sg_tb g)).
Definition sc_wr (g : sc_ctx) : Z -> Prop := fun x => sg_o g <= x < sg_o g + sg_n g.
(* the call's window and the output, which the post lets the call change *)
Definition sc_zone (g : sc_ctx) (a : Z) : Prop :=
  (sg_sp g - T_scribble_text <= a < sg_sp g) \/ (sg_o g <= a < sg_o g + sg_n g).
(* the bytes a segment may change: the zone but the two saves at entry sp - 16 *)
Definition sc_wz (g : sc_ctx) (a : Z) : Prop :=
  (sg_sp g - T_scribble_text <= a < sg_sp g - 16) \/ (sg_o g <= a < sg_o g + sg_n g).
Definition sc_res (g : sc_ctx) : list Z * Z := scribble_text_spec (sg_tb g) (sg_n g).

(* The contract's premises, in the contract's order. *)
Definition sc_pre (g : sc_ctx) : Prop :=
  cdc_entry tfibsegs B (sg_STK g) (sg_sp0 g) (sg_FP g) (sg_ly g) (sg_S g) (sg_W0 g) (sg_mem0 g) (sg_md0 g)
    (sg_own g) (sg_lyc g) (sg_Sc g) (sg_W g) (sg_memc g) (sg_mdc g) (sg_k g) (sg_regs g) T_scribble_text /\
  getr (sg_regs g) 10 = w64 (sg_q g) /\
  cstr_rd tfibsegs (sg_W g) (sg_memc g) (sg_sp g) T_scribble_text (sg_q g) (sg_tb g) /\
  getr (sg_regs g) 11 = w64 (sg_o g) /\ getr (sg_regs g) 12 = w64 (sg_n g) /\
  (0 <= sg_n g < 2 ^ 32 /\ sg_n g = Z.of_nat (length (sg_oj g))) /\
  cdst_ok tfibsegs B (sg_STK g) (sg_sp0 g) (sg_FP g) (sg_ly g) (sg_S g) (sg_lyc g) (sg_Sc g) (sg_own g)
    (sg_W g) (sg_memc g) (sg_sp g) T_scribble_text (sg_o g) (sg_n g) /\
  garr8 tfibsegs (rd (sg_W g) (sg_memc g)) (sg_o g) (sg_oj g) /\
  (sg_q g + sg_len g <= sg_o g \/ sg_o g + sg_n g <= sg_q g).

(* ---- what every boundary carries --------------------------------------------------------------------------------
   gp, tp, s1 .. s11 as at entry (the walk writes none of them, and the runtime call keeps them); sp = entry
   sp - 16; the two saves at entry sp - 8 (ra) and entry sp - 16 (s0); every byte outside the frame and [o, o + n)
   as at entry; every byte present at entry still present. *)
Definition sc_common (g : sc_ctx) (regs2 : bvmap 5 word) (mem2 : word -> option byte) : Prop :=
  Forall (fun r => getr regs2 r = getr (sg_regs g) r) sc_kregs /\
  getr regs2 2 = w64 (sg_sp g - 16) /\
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

(* The registers the loop keeps: a0 = q, a1 = o, a2 = n, a4 = the shadow offset, a6 = q + 1, a7 = 46, t0 = 8. *)
Definition sc_lregs_ok (g : sc_ctx) (regs2 : bvmap 5 word) : Prop :=
  getr regs2 10 = w64 (sg_q g) /\ getr regs2 11 = w64 (sg_o g) /\ getr regs2 12 = w64 (sg_n g) /\
  getr regs2 14 = w64 SB /\ getr regs2 16 = w64 (sg_q g + 1) /\ getr regs2 17 = w64 46 /\ getr regs2 5 = w64 8.

(* The loop head 0x85d1c: s0 = i, a5 = j < n, t1 = b = q[i], not 0. The terminator lies after byte i; outs, the j
   bytes written, are at o; the rest of the loop from (i, j) and the padding give the result. fuel bounds the text
   bytes left. *)
Definition P_H (g : sc_ctx) (fuel : nat) : bvmap 5 word -> (word -> option byte) -> Prop :=
  fun regs2 mem2 => exists (i j b : Z) (outs : list Z),
    getr regs2 8 = w64 i /\ getr regs2 15 = w64 j /\ getr regs2 6 = w64 b /\ sc_lregs_ok g regs2 /\
    0 <= i /\ nth (Z.to_nat i) (sg_tb g) 0 = b /\ b <> 0 /\ In 0 (skipn (Z.to_nat i + 1) (sg_tb g)) /\
    (Z.to_nat (sg_len g - i) <= fuel)%nat /\
    0 <= j < sg_n g /\ Z.of_nat (length outs) = j /\ garr8 tfibsegs (rd (sg_W g) mem2) (sg_o g) outs /\
    sc_res g = (outs ++ fst (scr_lib (skipn (Z.to_nat i) (sg_tb g)) (Z.to_nat (sg_n g - j))),
                i + snd (scr_lib (skipn (Z.to_nat i) (sg_tb g)) (Z.to_nat (sg_n g - j)))).

(* The store 0x85d64: s0 = i, a5 = j < n, t1 = v the output byte, t2 = d the text bytes it uses (1 or 2). The
   terminator lies at or after byte i + d; the text from byte i + d gives the rest. *)
Definition P_T (g : sc_ctx) (fuel : nat) : bvmap 5 word -> (word -> option byte) -> Prop :=
  fun regs2 mem2 => exists (i j v d : Z) (outs : list Z),
    getr regs2 8 = w64 i /\ getr regs2 15 = w64 j /\ getr regs2 6 = w64 v /\ getr regs2 7 = w64 d /\
    sc_lregs_ok g regs2 /\
    0 <= i /\ 1 <= d <= 2 /\ 0 <= v < 256 /\ In 0 (skipn (Z.to_nat (i + d)) (sg_tb g)) /\
    (Z.to_nat (sg_len g - (i + d)) <= fuel)%nat /\
    0 <= j < sg_n g /\ Z.of_nat (length outs) = j /\ garr8 tfibsegs (rd (sg_W g) mem2) (sg_o g) outs /\
    sc_res g = ((outs ++ [v]) ++ fst (scr_lib (skipn (Z.to_nat (i + d)) (sg_tb g)) (Z.to_nat (sg_n g - (j + 1)))),
                (i + d) + snd (scr_lib (skipn (Z.to_nat (i + d)) (sg_tb g)) (Z.to_nat (sg_n g - (j + 1))))).

(* The padding 0x85de0: s0 = r the result, a5 = j, a1 = o, a2 = n; the rest of the output is n - j spaces. *)
Definition P_P (g : sc_ctx) : bvmap 5 word -> (word -> option byte) -> Prop :=
  fun regs2 mem2 => exists (r j : Z) (outs : list Z),
    getr regs2 8 = w64 r /\ getr regs2 15 = w64 j /\ getr regs2 11 = w64 (sg_o g) /\ getr regs2 12 = w64 (sg_n g) /\
    0 <= r < 2 ^ 47 /\ 0 <= j <= sg_n g /\ Z.of_nat (length outs) = j /\
    garr8 tfibsegs (rd (sg_W g) mem2) (sg_o g) outs /\
    sc_res g = (outs ++ repeat 0x20 (Z.to_nat (sg_n g - j)), r).

(* The return 0x85df4: s0 is the result, the n bytes at o the output. *)
Definition P_X (g : sc_ctx) : bvmap 5 word -> (word -> option byte) -> Prop :=
  fun regs2 mem2 =>
    getr regs2 8 = w64 (snd (sc_res g)) /\ garr8 tfibsegs (rd (sg_W g) mem2) (sg_o g) (fst (sc_res g)).

(* The contract's post. *)
Definition sc_post (g : sc_ctx) : world tfibsegs -> config -> Prop :=
  cdc_post tfibsegs B MT (sg_STK g) (sg_sp0 g) (sg_FP g) (sg_ly g) (sg_S g) (sg_W0 g) (sg_mem0 g) (sg_md0 g)
    (sg_own g) (sg_k g) (sg_regs g) T_scribble_text (sc_wr g) (sg_lyc g) (sg_Sc g) (sg_W g) (sg_memc g) (sg_mdc g)
    (fun W2 mem2 regs2 => getr regs2 10 = w64 (snd (sc_res g)) /\
                          garr8 tfibsegs (rd W2 mem2) (sg_o g) (fst (sc_res g))).

(* ---- the segments ------------------------------------------------------------------------------------------------ *)
(* S0: entry -> the loop head with i = j = 0, or the padding with r = j = 0. *)
Definition sc_seg_S0 : Prop :=
  forall g, sc_pre g ->
  SRr tfibsegs (sg_W g) (cfg_at tfibsegs A_ST (sg_regs g) (sg_memc g) (sg_mdc g))
    (fun W2 c2 => sc_cut g PC_H (P_H g (length (sg_tb g))) W2 c2 \/ sc_cut g PC_P (P_P g) W2 c2).
(* H: from the loop head to the store, the output byte and the text bytes it uses chosen. *)
Definition sc_seg_H : Prop :=
  forall g fuel W2 c2, sc_pre g -> sc_cut g PC_H (P_H g (S fuel)) W2 c2 ->
  SRr tfibsegs W2 c2 (sc_cut g PC_T (P_T g fuel)).
(* T: the store, the next text byte, back to the loop head or on to the padding. *)
Definition sc_seg_T : Prop :=
  forall g fuel W2 c2, sc_pre g -> sc_cut g PC_T (P_T g fuel) W2 c2 ->
  SRr tfibsegs W2 c2 (fun W3 c3 => sc_cut g PC_H (P_H g fuel) W3 c3 \/ sc_cut g PC_P (P_P g) W3 c3).
(* P: the padding, by the runtime's memset when j < n. *)
Definition sc_seg_P : Prop :=
  forall g W2 c2, sc_pre g -> sc_cut g PC_P (P_P g) W2 c2 -> SRr tfibsegs W2 c2 (sc_cut g PC_X (P_X g)).
(* X: the result, the epilogue, the post. *)
Definition sc_seg_X : Prop :=
  forall g W2 c2, sc_pre g -> sc_cut g PC_X (P_X g) W2 c2 -> SRr tfibsegs W2 c2 (sc_post g).

(* ---- the composition --------------------------------------------------------------------------------------------- *)
Lemma P_H_zero : forall g regs2 mem2, P_H g 0 regs2 mem2 -> False.
Proof.
intros g regs2 mem2 (i & j & b & outs & _ & _ & _ & _ & Hi & _ & _ & Hin & Hf & _).
pose proof (sc_in_skipn_lt 0 (sg_tb g) (Z.to_nat i + 1) Hin) as Hl. unfold sg_len in Hf. lia.
Qed.
Lemma sc_cut_P : forall g pc (P : bvmap 5 word -> (word -> option byte) -> Prop) W2 c2,
  sc_cut g pc P W2 c2 -> exists regs2 mem2, P regs2 mem2.
Proof. intros g pc P W2 c2 (_ & regs2 & mem2 & md2 & _ & _ & _ & _ & HP). exists regs2, mem2. exact HP. Qed.

Section comp.
Hypothesis HS0 : sc_seg_S0.
Hypothesis HH : sc_seg_H.
Hypothesis HT : sc_seg_T.
Hypothesis HP : sc_seg_P.
Hypothesis HX : sc_seg_X.
Lemma sc_P_closed : forall g W2 c2, sc_pre g -> sc_cut g PC_P (P_P g) W2 c2 -> SRr tfibsegs W2 c2 (sc_post g).
Proof.
intros g W2 c2 Hpre Hc.
apply (SRr_bind tfibsegs _ _ _ _ (HP g W2 c2 Hpre Hc)). intros W3 c3 _ H.
exact (HX g W3 c3 Hpre H).
Qed.
Lemma sc_H_closed : forall fuel g W2 c2, sc_pre g -> sc_cut g PC_H (P_H g fuel) W2 c2 ->
  SRr tfibsegs W2 c2 (sc_post g).
Proof.
induction fuel as [|fuel IH]; intros g W2 c2 Hpre Hc.
- exfalso. destruct (sc_cut_P g PC_H _ W2 c2 Hc) as (regs2 & mem2 & H). exact (P_H_zero g regs2 mem2 H).
- apply (SRr_bind tfibsegs _ _ _ _ (HH g fuel W2 c2 Hpre Hc)). intros W3 c3 _ H3.
  apply (SRr_bind tfibsegs _ _ _ _ (HT g fuel W3 c3 Hpre H3)). intros W4 c4 _ [H4 | H4].
  + exact (IH g W4 c4 Hpre H4).
  + exact (sc_P_closed g W4 c4 Hpre H4).
Qed.
Theorem sc_spec_of_segs : cdc_scribble_text_specX tfibsegs B MT A_ST.
Proof.
unfold cdc_scribble_text_specX.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs q o n tb oj
  HE H10 HSTR H11 H12 HN HDST HOJ HDJ.
set (g := mkSc STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs q o n tb oj).
assert (Hpre : sc_pre g)
  by exact (conj HE (conj H10 (conj HSTR (conj H11 (conj H12 (conj HN (conj HDST (conj HOJ HDJ)))))))).
apply (SRr_bind tfibsegs _ _ _ _ (HS0 g Hpre)). intros W2 c2 _ [Hc | Hc].
- exact (sc_H_closed (length tb) g W2 c2 Hpre Hc).
- exact (sc_P_closed g W2 c2 Hpre Hc).
Qed.
End comp.

(* ---- what a segment reads off the contract ------------------------------------------------------------------------- *)
Lemma sc_stack : forall g, sc_pre g ->
  alloc_ceiling <= sg_sp g - T_scribble_text /\ sg_sp g <= 2 ^ 47 /\ 2 ^ 46 + T_scribble_text <= sg_sp g /\
  sg_sp g mod 16 = 0 /\ sg_sp0 g - sg_STK g <= sg_sp g - T_scribble_text /\ sg_sp g <= sg_sp0 g /\
  (forall a, sg_sp g - T_scribble_text <= a < sg_sp g -> apresent (w_H (sg_W g)) (sg_memc g) a).
Proof.
intros g ((HJ & _ & _ & _ & _ & Hal16 & Hwlo & Hwhi & _) & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (_ & HSTK & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold T_scribble_text, ESTACK in *. unfold sg_sp.
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
unfold coff_win, T_scribble_text, ESTACK in Hoff. fold (sg_len g) in *.
assert (Hlen : 0 < sg_len g).
{ unfold sg_len. destruct (sg_tb g); [destruct Hin | cbn [length]; lia]. }
split; [exact Hq0|]. split; [exact Hql|]. split; [exact Hin|]. split; [exact Hlen|].
split; [exact HG|]. split; [exact HRA|]. split; [exact Ham|].
intros a Ha Hz. unfold sc_zone, T_scribble_text, ESTACK in Hz. lia.
Qed.

(* The output: its range below 2 ^ 63, off the frame, writable and marked usable, n < 2 ^ 32. *)
Lemma sc_out : forall g, sc_pre g ->
  0 < sg_o g /\ sg_o g + sg_n g <= 2 ^ 63 /\ 0 <= sg_n g < 2 ^ 32 /\
  (sg_o g + sg_n g <= sg_sp g - T_scribble_text \/ sg_sp g <= sg_o g) /\
  tdst_ok B (sg_lyc g) (sg_Sc g) (sg_o g) (sg_n g) /\
  twr_ok tfibsegs B (sg_STK g) (sg_sp0 g) (sg_FP g) (sg_ly g) (sg_S g) (sg_lyc g) (sg_Sc g) (sg_own g)
    (sg_W g) (sg_memc g) (sg_sp g) (sg_o g) (sg_n g) /\
  range_addressable (aview tfibsegs (w_H (sg_W g)) (sg_memc g)) SHADOW_OFF (sg_o g) (sg_n g) /\
  (0 < sg_n g -> shadow_hull_vis (aview tfibsegs (w_H (sg_W g)) (sg_memc g)) (sg_o g) (sg_n g)) /\
  amem_range (sg_o g) (sg_n g) /\
  (sg_q g + sg_len g <= sg_o g \/ sg_o g + sg_n g <= sg_q g).
Proof.
intros g (_ & _ & _ & _ & _ & (Hn & _) & (Ho0 & Hon & Htd & Htw & HRA & Hhull & Ham & Hoff) & _ & HDJ).
unfold coff_win, T_scribble_text, ESTACK in Hoff.
split; [exact Ho0|]. split; [exact Hon|]. split; [exact Hn|]. split; [unfold T_scribble_text, ESTACK; lia|].
repeat (split; [assumption|]). exact HDJ.
Qed.

(* A boundary at the end of a run: the run kept the journal's layout and state, wrote only bytes of [o, o + n)
   and kept the registers of sc_common; P holds of the new state. *)
Lemma sc_cut_close : forall g pc (P : bvmap 5 word -> (word -> option byte) -> Prop) regs2 mem2 md2 ms md3,
  sc_pre g -> same_io (sg_mdc g) md2 -> sc_common g regs2 mem2 ->
  ajournal tfibsegs B (sg_STK g) (sg_sp0 g) (sg_FP g) (sg_ly g) (sg_S g) (sg_W0 g) (sg_mem0 g) (sg_md0 g)
    (sg_own g) (sg_lyc g) (sg_Sc g) (sg_W g) (ms_mem ms) md3 (sg_k g) ->
  same_io md2 md3 ->
  ms = mkst (ms_regs ms) (Z_to_bv 64 pc) (ms_mem ms) (seg_rom tfibsegs) ->
  Forall (fun r => getr (ms_regs ms) r = getr regs2 r) (sc_kregs ++ [2%bv]) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ sc_wz g a ->
     aview tfibsegs (w_H (sg_W g)) (ms_mem ms) a = aview tfibsegs (w_H (sg_W g)) mem2 a) ->
  (forall a, apresent (w_H (sg_W g)) mem2 a -> apresent (w_H (sg_W g)) (ms_mem ms) a) ->
  P (ms_regs ms) (ms_mem ms) ->
  sc_cut g pc P (sg_W g) (mkCfg ms md3).
Proof.
intros g pc P regs2 mem2 md2 ms md3 Hpre Hio HC HJ3 Hio3 Hms HR KE KP HPk.
destruct (sc_stack g Hpre) as (Hceil & H47 & H46 & Hal & Hwin & Hsp0 & _).
destruct (sc_out g Hpre) as (Ho0 & Hon & Hn & Hoff & _).
destruct HC as (HK & R2 & Vra & Vs0 & KC & PC).
apply Forall_app in HR as (HRk & HRl).
repeat (apply Forall_cons_iff in HRl as (? & HRl)).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). unfold T_scribble_text, ESTACK in *.
assert (KM : forall x, sg_sp g - 16 <= x < sg_sp g ->
  mbyte tfibsegs (rd (sg_W g) (ms_mem ms)) x = mbyte tfibsegs (rd (sg_W g) mem2) x).
{ intros x Hx. apply (mbyte_of_aview tfibsegs). apply KE; [lia|]. unfold sc_wz, T_scribble_text, ESTACK in *. lia. }
split; [reflexivity|]. exists (ms_regs ms), (ms_mem ms), md3.
split; [unfold cfg_at, w64; rewrite Hms at 1; reflexivity|].
split; [exact HJ3|]. split; [exact (same_io_trans _ _ _ Hio Hio3)|].
split; [|exact HPk].
split.
{ rewrite Forall_forall in HK, HRk |- *. intros r Hr. rewrite (HRk r Hr). exact (HK r Hr). }
split; [congruence|].
split; [apply (sc_val_mem_kept (rd (sg_W g) mem2)); [intros x Hx; apply KM; cbn in Hx; lia | exact Vra]|].
split; [apply (sc_val_mem_kept (rd (sg_W g) mem2)); [intros x Hx; apply KM; cbn in Hx; lia | exact Vs0]|].
split.
- intros a Ha Hz. rewrite (KE a Ha); [exact (KC a Ha Hz)|]. intros Hx. apply Hz. unfold sc_wz, sc_zone in *. lia.
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
destruct (sc_out g Hpre) as (Ho0 & Hon & Hn & _ & _ & _ & _ & _ & Ham & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold amem_range in Ham. rewrite C3, C4, C5 in Ham.
assert (D0 : 0 <= x / 8) by (apply Z.div_pos; lia).
assert (D1 : x / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia).
unfold SHADOW_OFF, sc_zone, T_scribble_text, ESTACK in *. split; [lia|]. intros [Hz | Hz]; lia.
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
