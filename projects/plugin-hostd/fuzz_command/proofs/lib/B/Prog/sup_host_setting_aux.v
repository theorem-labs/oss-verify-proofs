(* Helper lemmas of sup_host_setting's ASan+UBSan walk (plugin-hostd/fuzz_command, fuzz_command.asan-ubsan, entry
   0x8b53c) that need no callee statement (a Theorem Labs lane's lib/B/Prog/sup_host_setting_c.v on a working branch 92195a003c6):

   - the four UBSan checks of the pointer &tok[n] (tok + 8n, computed by repeated `addi 8`), each as its
     instructions compute it; every one branches to the `unimp` at 0x8b8c0:
       0x8b6bc `bltu s6,s8`   s6 = tok + 8n, s8 = tok (hsb_ub_6bc)
       0x8b6c8 `beqz a0`      a0 = (snez tok) xor (seqz (tok + 8n)) (0x8b6a0, 0x8b6c0, 0x8b6c4; hsb_ub_6c8)
       0x8b6cc `beqz s7`      s7 = (seqz (tok & 7)) & (snez tok) (0x8b6a0 .. 0x8b6ac; hsb_ub_6cc)
       0x8b774 `bltu s5,s7`   s5 = not tok (0x8b72c `xori s5,s8,-1`), s7 = 8n (hsb_ub_774)
     and all four at once from the statement's premises (ptok <> 0, ptok mod 8 = 0, the token array in a live
     side-stack frame object or a live block: hsb_ubsan_tok);
   - 0x8b68c `blez s5` (s5 = ntok) is not taken for 1 <= ntok (hsb_blez_ntok); loop 2's bound
     s2 = ntok zero-extended (0x8b728 `slli a0,s5,32`, 0x8b730 `srli s2,a0,32`; hsb_zext32);
   - the token array's addresses: 4096 <= ptok and ptok + 8 ntok <= alloc_ceiling (hsb_arr_bound, as A's
     hs4_ptok_range, lib/A/Prog/sup_host_setting_s4.v:88-99 on a working branch e323bbe76d2);
   - join_sp's length along the join loop (A's hs6_join_snoc, hs6_firstn_S, sup_host_setting_s6.v:62-104). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import String ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YG0q YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05 YI16 YP0m YP03.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable CmdSyms CmdList CmdPa CmdBase CmdRep.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* ---- 64-bit words ---- *)

Lemma hsb_sltu : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 ->
  alu64 ALU_SLTU (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (if a <? b then 1 else 0).
Proof.
intros a b Ha Hb. apply bv_eq. rewrite alu64_unsigned. cbn [zalu_raw].
rewrite (unsigned_lit_small a), (unsigned_lit_small b) by lia.
destruct (a <? b); vm_compute; reflexivity.
Qed.

Lemma hsb_and7 : forall t, 0 <= t < 2 ^ 64 -> alu64 ALU_AND (Z_to_bv 64 t) (Z_to_bv 64 7) = Z_to_bv 64 (t mod 8).
Proof.
intros t Ht. pose proof (Z.mod_pos_bound t 8 ltac:(lia)) as Hm.
apply bv_eq. rewrite alu64_unsigned. cbn [zalu_raw].
rewrite (unsigned_lit_small t), (unsigned_lit_small 7), (unsigned_lit_small (t mod 8)) by lia.
change 7 with (Z.ones 3). rewrite Z.land_ones by lia. change (2 ^ 3) with 8.
unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). apply Z.mod_small. lia.
Qed.

Lemma hsb_lxor_ones : forall x, 0 <= x < 2 ^ 64 -> Z.lxor x (2 ^ 64 - 1) = 2 ^ 64 - 1 - x.
Proof.
intros x Hx.
pose proof (Z.sub_lxor_2rlandn (2 ^ 64 - 1) x) as H.
assert (H0 : Z.land (Z.lnot (2 ^ 64 - 1)) x = 0).
{ replace (Z.lnot (2 ^ 64 - 1)) with (- (2 ^ 64)) by reflexivity.
  apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0.
  destruct (Z_lt_dec n 64).
  - replace (- (2 ^ 64)) with (Z.shiftl (-1) 64) by reflexivity. rewrite Z.shiftl_spec_low by lia. reflexivity.
  - rewrite (Z.bits_above_log2 x); [apply Bool.andb_false_r | lia |].
    destruct (Z.eq_dec x 0); [subst; cbn; lia|].
    apply Z.lt_le_trans with 64; [apply Z.log2_lt_pow2; lia | lia]. }
rewrite Z.lxor_comm. lia.
Qed.

(* the 64-bit zero extension of a 32-bit count (0x8b728 `slli a0,s5,32`, 0x8b730 `srli s2,a0,32`) *)
Lemma hsb_zext32 : forall v, 0 <= v < 2 ^ 32 ->
  alu64 ALU_SRL (alu64 ALU_SLL (Z_to_bv 64 v) (Z_to_bv 64 32)) (Z_to_bv 64 32) = Z_to_bv 64 v.
Proof.
intros v Hv. apply bv_eq. rewrite !alu64_unsigned. cbn [zalu_raw].
rewrite (unsigned_lit_small v), (unsigned_lit_small 32) by lia. change (Z.land 32 63) with 32.
rewrite Z.shiftl_mul_pow2 by lia.
unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite (Z.mod_small (v * 2 ^ 32)) by lia.
rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_mul by lia.
apply Z.mod_small. lia.
Qed.

(* ---- the branches of the token loops ---- *)

(* 0x8b68c `blez s5` (`bge zero,s5`, s5 = ntok): with 1 <= ntok the ntok <= 0 arm (0x8b7d8, xmalloc(1) and the
   store1 check 0x8b7f0 / report 0x8b8e0) is not reached *)
Lemma hsb_blez_ntok : forall v, 1 <= v < 2 ^ 63 -> branch_taken BC_GE (Z_to_bv 64 0) (Z_to_bv 64 v) = false.
Proof.
intros v Hv. cbn [branch_taken]. apply Bool.negb_false_iff. rewrite bv_lts_signed.
rewrite (signed_of_small (Z_to_bv 64 0)), (signed_of_small (Z_to_bv 64 v));
  rewrite ?(unsigned_lit_small 0), ?(unsigned_lit_small v) by lia; try (unfold half64; lia).
Qed.

(* 0x8b6bc `bltu s6,s8`: tok + 8n does not wrap below tok *)
Lemma hsb_ub_6bc : forall t k, 0 <= t -> 0 <= k -> t + k < 2 ^ 64 ->
  branch_taken BC_LTU (Z_to_bv 64 (t + k)) (Z_to_bv 64 t) = false.
Proof.
intros t k H0 H1 H2. cbn [branch_taken]. rewrite bv_ltu_unsigned.
rewrite (unsigned_lit_small (t + k)), (unsigned_lit_small t) by lia. apply Z.ltb_ge. lia.
Qed.

(* 0x8b6c8 `beqz a0`, a0 = (snez tok) xor (seqz (tok + 8n)): tok and tok + 8n are both non-null *)
Lemma hsb_ub_6c8 : forall t k, 0 < t -> 0 <= k -> t + k < 2 ^ 64 ->
  branch_taken BC_EQ
    (alu64 ALU_XOR (alu64 ALU_SLTU (Z_to_bv 64 0) (Z_to_bv 64 t)) (alu64 ALU_SLTU (Z_to_bv 64 (t + k)) (Z_to_bv 64 1)))
    (Z_to_bv 64 0) = false.
Proof.
intros t k H0 H1 H2. rewrite (hsb_sltu 0 t), (hsb_sltu (t + k) 1) by lia.
replace (0 <? t) with true by (symmetry; apply Z.ltb_lt; lia).
replace (t + k <? 1) with false by (symmetry; apply Z.ltb_ge; lia).
vm_compute. reflexivity.
Qed.

(* 0x8b6cc `beqz s7`, s7 = (seqz (tok & 7)) & (snez tok): tok is non-null and 8-aligned *)
Lemma hsb_ub_6cc : forall t, 0 < t < 2 ^ 64 -> t mod 8 = 0 ->
  branch_taken BC_EQ
    (alu64 ALU_AND (alu64 ALU_SLTU (alu64 ALU_AND (Z_to_bv 64 t) (Z_to_bv 64 7)) (Z_to_bv 64 1))
       (alu64 ALU_SLTU (Z_to_bv 64 0) (Z_to_bv 64 t)))
    (Z_to_bv 64 0) = false.
Proof.
intros t Ht H8. rewrite (hsb_and7 t) by lia. rewrite H8. rewrite (hsb_sltu 0 t) by lia.
replace (0 <? t) with true by (symmetry; apply Z.ltb_lt; lia).
vm_compute. reflexivity.
Qed.

(* 0x8b774 `bltu s5,s7`, s5 = not tok, s7 = 8n: tok + 8n does not wrap *)
Lemma hsb_ub_774 : forall t k, 0 <= t -> 0 <= k -> t + k < 2 ^ 64 ->
  branch_taken BC_LTU (alu64 ALU_XOR (Z_to_bv 64 t) (Z_to_bv 64 (-1))) (Z_to_bv 64 k) = false.
Proof.
intros t k H0 H1 H2. cbn [branch_taken]. rewrite bv_ltu_unsigned, alu64_unsigned. cbn [zalu_raw].
rewrite (unsigned_lit_small t), (unsigned_lit_small k) by lia.
replace (bv_unsigned (Z_to_bv 64 (-1))) with (2 ^ 64 - 1) by (vm_compute; reflexivity).
rewrite hsb_lxor_ones by lia.
unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_small by lia.
apply Z.ltb_ge. lia.
Qed.

(* ---- join_sp along the join loop ---- *)

Lemma hsb_firstn_S : forall {X : Type} (l : list X) n d, (n < length l)%nat ->
  firstn (S n) l = firstn n l ++ [nth n l d].
Proof.
intros X l. induction l as [|a l IH]; intros n d Hn; [cbn in Hn; lia|].
destruct n as [|n]; [reflexivity|]. cbn [firstn nth app]. rewrite (IH n d) by (cbn in Hn; lia). reflexivity.
Qed.

Lemma hsb_join_cons : forall w X, X <> [] -> join_sp (w :: X) = w ++ SPACE :: join_sp X.
Proof. intros w [|x X] H; [contradiction | reflexivity]. Qed.

Lemma hsb_join_snoc : forall X w, X <> [] -> join_sp (X ++ [w]) = join_sp X ++ SPACE :: w.
Proof.
induction X as [|a X IH]; intros w HX; [contradiction|].
destruct X as [|b X].
- reflexivity.
- change ((a :: b :: X) ++ [w]) with (a :: ((b :: X) ++ [w])).
  rewrite (hsb_join_cons a ((b :: X) ++ [w])) by discriminate.
  rewrite (hsb_join_cons a (b :: X)) by discriminate.
  rewrite IH by discriminate. rewrite <- app_assoc. reflexivity.
Qed.

(* the separator of the join loop's pass n >= 1 lands inside the joined text: its two bytes, at
   |join_sp (firstn n toks)| and one past it, lie below |join_sp toks| + 1 *)
Lemma hsb_join_firstn_len : forall (l : list (list byte)) n, (1 <= n)%nat -> (n < length l)%nat ->
  length (join_sp (firstn (S n) l)) = (length (join_sp (firstn n l)) + 1 + length (nth n l []))%nat.
Proof.
intros l n H1 H2. rewrite (hsb_firstn_S l n []) by lia.
rewrite hsb_join_snoc.
- rewrite length_app. cbn [length]. lia.
- destruct l as [|a l]; [cbn in H2; lia|]. destruct n as [|n]; [lia|]. cbn. discriminate.
Qed.

Lemma hsb_join_firstn_mono : forall (l : list (list byte)) n m, (1 <= n)%nat -> (n <= m)%nat -> (m <= length l)%nat ->
  (length (join_sp (firstn n l)) <= length (join_sp (firstn m l)))%nat.
Proof.
intros l n m H1 Hnm. induction Hnm as [|m Hnm IH]; intros Hm; [lia|].
rewrite (hsb_join_firstn_len l m) by lia. specialize (IH ltac:(lia)). lia.
Qed.

Lemma hsb_join_sep_in : forall (l : list (list byte)) n, (1 <= n)%nat -> (n < length l)%nat ->
  (length (join_sp (firstn n l)) + 1 <= length (join_sp l))%nat.
Proof.
intros l n H1 H2.
pose proof (hsb_join_firstn_len l n H1 H2) as E.
pose proof (hsb_join_firstn_mono l (S n) (length l) ltac:(lia) ltac:(lia) ltac:(lia)) as M.
rewrite firstn_all in M. lia.
Qed.

(* ---- the token array ---- *)
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
Variable B : asyms.

(* the array lies in a live side-stack frame object or in a live block, so above 4096 and below the allocator's
   ceiling (A's hs4_ptok_range) *)
Lemma hsb_arr_bound : forall ly S (W : world SEGS) mem md p N, 0 <= N ->
  AR SEGS B ly S W mem md ->
  afobj SEGS B ly S W mem p N \/ in_blockA (ablocks B ly S) p N ->
  4096 <= p /\ p + N <= alloc_ceiling.
Proof.
intros ly S W mem md p N HN HAR [((cid & pos & Hin & _ & _ & Hlo & Hhi) & _) | (q & m & Hin & Hlo & Hhi)].
- destruct (frames_bounds SEGS B (AR_laws_ok SEGS B) ly S W mem md cid pos HAR Hin) as (F1 & F2 & _). lia.
- destruct (al_blocks _ _ (AR_laws_ok SEGS B) ly S W mem md q m HAR Hin) as (_ & B1 & B2 & _ & _ & _ & B3).
  pose proof (req_size_pos m ltac:(lia)) as [_ Hq]. lia.
Qed.

(* the four UBSan checks of &tok[n], n < ntok, are not taken, from the statement's premises: ptok <> 0,
   ptok mod 8 = 0 and the token array premise *)
Lemma hsb_ubsan_tok : forall ly S (W : world SEGS) mem md (O : list (Z * Z)) ptok N n,
  AR SEGS B ly S W mem md -> ptok <> 0 -> ptok mod 8 = 0 ->
  (afobj SEGS B ly S W mem ptok (8 * N) \/
   (in_blockA (ablocks B ly S) ptok (8 * N) /\ Forall (fun qk => iv_apart ptok (8 * N) (fst qk) (snd qk)) O)) ->
  0 <= n < N ->
  branch_taken BC_LTU (Z_to_bv 64 (ptok + 8 * n)) (Z_to_bv 64 ptok) = false /\
  branch_taken BC_EQ
    (alu64 ALU_XOR (alu64 ALU_SLTU (Z_to_bv 64 0) (Z_to_bv 64 ptok))
       (alu64 ALU_SLTU (Z_to_bv 64 (ptok + 8 * n)) (Z_to_bv 64 1))) (Z_to_bv 64 0) = false /\
  branch_taken BC_EQ
    (alu64 ALU_AND (alu64 ALU_SLTU (alu64 ALU_AND (Z_to_bv 64 ptok) (Z_to_bv 64 7)) (Z_to_bv 64 1))
       (alu64 ALU_SLTU (Z_to_bv 64 0) (Z_to_bv 64 ptok))) (Z_to_bv 64 0) = false /\
  branch_taken BC_LTU (alu64 ALU_XOR (Z_to_bv 64 ptok) (Z_to_bv 64 (-1))) (Z_to_bv 64 (8 * n)) = false.
Proof.
intros ly S W mem md O ptok N n HAR Hp0 Hp8 HARR Hn.
assert (HB : 4096 <= ptok /\ ptok + 8 * N <= alloc_ceiling).
{ apply (hsb_arr_bound ly S W mem md ptok (8 * N) ltac:(lia) HAR).
  destruct HARR as [H | [H _]]; [left | right]; exact H. }
pose proof asan_consts as (C1 & _).
split; [apply hsb_ub_6bc; lia|].
split; [apply hsb_ub_6c8; lia|].
split; [apply hsb_ub_6cc; lia|].
apply hsb_ub_774; lia.
Qed.
End f.
End d.
