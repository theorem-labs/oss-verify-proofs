(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the entry segment of the image-A walk of libreac/fuzz_decode's LLVMFuzzerTestOneInput, with proof steps adapted from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v (pb_reac_ctrl_stamp_headamp's prologue and its class-0 stack malloc, a working branch), proofs/libreac/fuzz_grant/lib/A/Prog/GrantACja.v (land_m32, denot_and_m32, sp1_facts), proofs/libreac/fuzz_grant/lib/A/Prog/GrantFrame.v (val_mem_of_rd32, rdword_of_val_mem, val_mem_moved), lib/Reusable/YCbq.v (call_effect_journal) and lib/A/Prog/YC85.v (aj_stack_malloc_atS); module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_decode/lib/A/Prog/LLVMFuzzerTestOneInput_seg_entry.v, with its module paths changed; 672 of its 728 lines of code are new or changed and 525 lines of the source are left out. *)
(* check_text_scribble (fuzz_codec.c:431-452) at image A 0x83798, 211 instructions, real frame 128 and a
   side-stack frame of class 0 requested at 0x83808, against lib/A/Prog/CPgChkC.v's
   cdc_check_text_scribble_specX. a0 = q (the text), a1 = ch (the 24 character bytes of the record),
   a2 = n (the personality's scribble_chars, 0 <= n <= 8).

   The walk:
   - 0x83798-0x83804 the prologue (the 128-byte frame, the twelve saves, sp realigned to 32 in s1 = SP1),
     the two .got loads (the shadow offset SB, the use-after-return cell, whose value 1 decides the test at
     0x83800), a0 = 64, jal 0x3d0fc.
   - the class-0 side-stack frame request (CPgWalkFrame.cpg_stack_malloc_keep): F in a0, its 8 shadow bytes
     zero, the flag address at F + 56.
   - 0x8383c-0x8389c the frame header (0x41B58AB3, the frame description, the function's own address), the
     eight shadow bytes f1 x4 | f3 x4 (want[8] at F + 32 is the one variable), and the check of the text's
     first byte.
   - 0x838d0-0x83980 the inlined owed_scribble_text loop: one output byte per turn, three instrumented
     checks (the text byte at q + i, the dot's digit at q + i + 1, the store into want[o]).
   - 0x83984-0x839a4 the pad of want[o..n) with ' ' and the memset of the record's 24 bytes to 0xa5
     (aj_intrin_atS, OSet).
   - 0x839b4 diginet_scribble_text through its contract, 0x839c8 the bcmp wrapper (aj_bcmp_at): the two
     aborts at 0x83ac4 are refuted by the premise owed_scribble_text_spec tb n = scribble_text_spec tb n.
   - 0x83a30-0x83a58 the inlined fuzz_all over the record's bytes [n, 24), each 0xa5 by the memset.
   - 0x839d8-0x83a88 the frame's shadow set to f8 / f5, the retire word, the flag cleared (aj_flag_store)
     and the epilogue. *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe codec_text.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YC85.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw0 ACef AF0l ACej ACeh ACem ACep.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw1 AWalkFw2 ACfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require AE36 AF0x.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import
CodecCJ CPgBase CPgChkC CPgWalk CPgWalkKept CPgWalkFrame CPgWalkCall CPgWalkIntr.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Definition A_CHECK_TEXT_SCRIBBLE : Z := 0x83798.
Definition A_SCRIBBLE_TEXT : Z := 0x85cc4.
Definition A_MEMSET : Z := 0x51e34.
Definition A_BCMP : Z := 0x422e0.
(* the use-after-return cell's .got slot and the cell: the walk reads them in the prologue *)
Definition cts_rs0 : smem := [uar_got_region; uar_cell_region].
(* a2 = n, 0 <= n <= 8 *)
Definition cts_af0 : list (nat * afact) := [(12%nat, mkAF 0 8 0)].

Lemma cts_U_add0 : forall E e, U E (SAlu ALU_ADD e (SLit 0)) = U E e.
Proof.
intros E e. rewrite U_SAlu, U_SLit. cbn [zalu_raw]. rewrite (zcanon_id 0) by (unfold M64; lia).
rewrite Z.add_0_r. apply zcanon_id. apply U_range.
Qed.
Lemma cts_denot_and_m32 : forall E n v c, ew E n = Z_to_bv 64 v -> 0 <= v + c -> v + c < 2 ^ 64 -> 0 <= v < 2 ^ 64 ->
sv_denot E (SAlu ALU_AND (SOff n c) (SLit (-32))) = Z_to_bv 64 (32 * ((v + c) / 32)).
Proof.
intros E n v c Hn H0 H1 Hv. rewrite denot_lit_U. f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit, (U_atom_off E n v c Hn) by lia.
change (zcanon (-32)) with (2 ^ 64 - 32). rewrite land_m32 by lia. apply zcanon_id. unfold M64.
split; [apply Z.mul_nonneg_nonneg; [lia | apply Z.div_pos; lia]|].
pose proof (Z.mul_div_le (v + c) 32 ltac:(lia)). lia.
Qed.
Lemma cts_count_le : forall cid l, count_cid cid l <= Z.of_nat (length l).
Proof.
intros cid l. induction l as [|[c p] t IH]; cbn [count_cid length]; [lia|]. destruct (c =? cid); lia.
Qed.

(* ---- the Z-level model of the inlined owed_scribble_text (lib/Prog's walk of the same function) ---- *)
(* the text bytes before the first 0 *)
Fixpoint cts_cstr (l : list Z) : list Z :=
match l with [] => [] | x :: l' => if x =? 0 then [] else x :: cts_cstr l' end.
Lemma cts_cstring : forall l, In 0 l ->
(length (cts_cstr l) < length l)%nat /\ nth (length (cts_cstr l)) l 0 = 0 /\
forall j, (j < length (cts_cstr l))%nat -> nth j l 0 <> 0.
Proof.
induction l as [|x l IH]; cbn; intros H; [contradiction|].
destruct (Z.eqb_spec x 0) as [E|E].
- subst x. cbn. split; [lia|]. split; [reflexivity|]. intros; lia.
- destruct H as [H|H]; [congruence|]. destruct (IH H) as (A & B & C). cbn.
  split; [lia|]. split; [exact B|]. intros [|j] Hj; [exact E|]. apply C. lia.
Qed.
Lemma cts_skipn_cons : forall (l : list Z) k, (k < length l)%nat -> skipn k l = nth k l 0 :: skipn (S k) l.
Proof. induction l as [|x l IH]; intros [|k] Hk; cbn in *; try lia; [reflexivity|]. apply IH. lia. Qed.
Lemma cts_hd_skipn : forall (l : list Z) k, match skipn k l with y :: _ => y | [] => 0 end = nth k l 0.
Proof. induction l as [|x l IH]; intros [|k]; cbn; try reflexivity. apply IH. Qed.
Lemma cts_tl_skipn : forall (l : list Z) k, tl (skipn k l) = skipn (S k) l.
Proof. induction l as [|x l IH]; intros [|k]; cbn; try reflexivity. apply IH. Qed.
Lemma cts_owe_0 : forall t, scr_owe t 0 = ([], 0).
Proof. intros [|x t]; reflexivity. Qed.
Lemma cts_owe_len : forall k t, length (fst (scr_owe t k)) = k.
Proof.
induction k as [|k IH]; intros t; [rewrite cts_owe_0; reflexivity|].
destruct t as [|x t']; cbn [scr_owe]; [cbn [fst]; apply repeat_length|].
destruct (x =? 0); [cbn [fst]; apply repeat_length|].
cbv iota.
match goal with |- context [if ?c then _ else _] => destruct c end.
- destruct (scr_owe (tl t') k) as [o u] eqn:E. cbn [fst length]. specialize (IH (tl t')). rewrite E in IH. cbn [fst] in IH. lia.
- destruct (scr_owe t' k) as [o u] eqn:E. cbn [fst length]. specialize (IH t'). rewrite E in IH. cbn [fst] in IH. lia.
Qed.
Lemma cts_owe_step : forall t j k, (j < length t)%nat -> nth j t 0 <> 0 ->
scr_owe (skipn j t) (S k) =
 (if (nth j t 0 =? 46) && (49 <=? nth (S j) t 0) && (nth (S j) t 0 <=? 57)
  then ((nth (S j) t 0 - 26) :: fst (scr_owe (skipn (S (S j)) t) k), snd (scr_owe (skipn (S (S j)) t) k) + 2)
  else ((if nth j t 0 <? 128 then nth j t 0 else 63) :: fst (scr_owe (skipn (S j) t) k),
        snd (scr_owe (skipn (S j) t) k) + 1)).
Proof.
intros t j k Hj Hx. rewrite (cts_skipn_cons t j Hj). cbn [scr_owe].
rewrite (proj2 (Z.eqb_neq _ _) Hx). rewrite cts_hd_skipn, cts_tl_skipn.
destruct ((nth j t 0 =? 46) && (49 <=? nth (S j) t 0) && (nth (S j) t 0 <=? 57)).
- destruct (scr_owe (skipn (S (S j)) t) k); reflexivity.
- destruct (scr_owe (skipn (S j) t) k); reflexivity.
Qed.
Lemma cts_owe_zero : forall t j k, (j < length t)%nat -> nth j t 0 = 0 ->
scr_owe (skipn j t) k = (repeat 32 k, 0).
Proof.
intros t j k Hj Hx. rewrite (cts_skipn_cons t j Hj), Hx. destruct k as [|k]; reflexivity.
Qed.
Lemma cts_cond_true : forall y, 49 <= y <= 57 -> (46 =? 46) && (49 <=? y) && (y <=? 57) = true.
Proof. intros y Hy. rewrite (proj2 (Z.leb_le 49 y)), (proj2 (Z.leb_le y 57)) by lia. reflexivity. Qed.
Lemma cts_cond_false : forall x y, ~ (x = 46 /\ 49 <= y <= 57) -> (x =? 46) && (49 <=? y) && (y <=? 57) = false.
Proof.
intros x y H. destruct (Z.eqb_spec x 46); destruct (Z.leb_spec 49 y); destruct (Z.leb_spec y 57); cbn; try reflexivity.
exfalso. apply H. split; [assumption | lia].
Qed.
(* o output slots and i text bytes done, pre the output bytes owed so far *)
Definition cts_MODEL (tb : list Z) (nn : nat) (o i : Z) (pre : list Z) : Prop :=
fst (scr_owe tb nn) = pre ++ fst (scr_owe (skipn (Z.to_nat i) tb) (nn - Z.to_nat o)) /\
snd (scr_owe tb nn) = i + snd (scr_owe (skipn (Z.to_nat i) tb) (nn - Z.to_nat o)).
Lemma cts_model_init : forall tb nn, cts_MODEL tb nn 0 0 [].
Proof. intros tb nn. unfold cts_MODEL. cbn [Z.to_nat skipn app]. rewrite Nat.sub_0_r. split; reflexivity. Qed.
Lemma cts_model_dot : forall tb nn o i pre, In 0 tb -> cts_MODEL tb nn o i pre ->
0 <= o < Z.of_nat nn -> 0 <= i < Z.of_nat (length (cts_cstr tb)) ->
nth (Z.to_nat i) tb 0 = 46 -> 49 <= nth (Z.to_nat (i + 1)) tb 0 <= 57 ->
cts_MODEL tb nn (o + 1) (2 + i) (pre ++ [nth (Z.to_nat (i + 1)) tb 0 + -26]).
Proof.
intros tb nn o i pre Hin [H1 H2] Ho Hi Hx Hy.
destruct (cts_cstring tb Hin) as (Hzl & _ & _).
assert (Hlen : (Z.to_nat i < length tb)%nat) by lia.
assert (Hn0 : nth (Z.to_nat i) tb 0 <> 0) by lia.
assert (Ek : (nn - Z.to_nat o)%nat = S (nn - Z.to_nat (o + 1))) by lia.
unfold cts_MODEL.
rewrite Ek, (cts_owe_step tb (Z.to_nat i) _ Hlen Hn0) in H1, H2.
replace (S (Z.to_nat i)) with (Z.to_nat (i + 1)) in H1, H2 by lia.
rewrite Hx in H1, H2. rewrite (cts_cond_true _ Hy) in H1, H2.
replace (S (Z.to_nat (i + 1))) with (Z.to_nat (2 + i)) in H1, H2 by lia.
cbn [fst snd] in H1, H2. split.
- rewrite H1, <- app_assoc. reflexivity.
- rewrite H2. lia.
Qed.
Lemma cts_model_one : forall tb nn o i pre, In 0 tb -> cts_MODEL tb nn o i pre ->
0 <= o < Z.of_nat nn -> 0 <= i < Z.of_nat (length (cts_cstr tb)) ->
~ (nth (Z.to_nat i) tb 0 = 46 /\ 49 <= nth (Z.to_nat (i + 1)) tb 0 <= 57) ->
cts_MODEL tb nn (o + 1) (1 + i)
  (pre ++ [if nth (Z.to_nat i) tb 0 <? 128 then nth (Z.to_nat i) tb 0 else 63]).
Proof.
intros tb nn o i pre Hin [H1 H2] Ho Hi Hnd.
destruct (cts_cstring tb Hin) as (Hzl & _ & Hnz).
assert (Hlen : (Z.to_nat i < length tb)%nat) by lia.
assert (Hn0 : nth (Z.to_nat i) tb 0 <> 0) by (apply Hnz; lia).
assert (Ek : (nn - Z.to_nat o)%nat = S (nn - Z.to_nat (o + 1))) by lia.
unfold cts_MODEL.
rewrite Ek, (cts_owe_step tb (Z.to_nat i) _ Hlen Hn0) in H1, H2.
replace (S (Z.to_nat i)) with (Z.to_nat (i + 1)) in H1, H2 by lia.
rewrite (cts_cond_false _ _ Hnd) in H1, H2.
replace (Z.to_nat (i + 1)) with (Z.to_nat (1 + i)) in H1, H2 by lia.
cbn [fst snd] in H1, H2. split.
- rewrite H1, <- app_assoc. reflexivity.
- rewrite H2. lia.
Qed.
Lemma cts_model_end : forall tb nn o i pre, In 0 tb -> cts_MODEL tb nn o i pre ->
0 <= o <= Z.of_nat nn -> 0 <= i <= Z.of_nat (length (cts_cstr tb)) ->
(o = Z.of_nat nn \/ i = Z.of_nat (length (cts_cstr tb))) ->
fst (scr_owe tb nn) = pre ++ repeat 32 (nn - Z.to_nat o) /\ snd (scr_owe tb nn) = i.
Proof.
intros tb nn o i pre Hin [H1 H2] Ho Hi Hend.
destruct (cts_cstring tb Hin) as (Hzl & Hz0 & _).
destruct Hend as [E|E].
- subst o. replace (nn - Z.to_nat (Z.of_nat nn))%nat with 0%nat in * by lia.
  rewrite cts_owe_0 in H1, H2. cbn [fst snd repeat] in H1, H2 |- *. rewrite ?app_nil_r in H1 |- *.
  split; [exact H1 | lia].
- subst i. rewrite Nat2Z.id in H1, H2.
  rewrite (cts_owe_zero tb (length (cts_cstr tb))) in H1, H2 by (first [lia | exact Hz0]).
  cbn [fst snd] in H1, H2. split; [exact H1 | lia].
Qed.


(* the awr_ok of a state that holds the walk's own frame (atom 38), its shadow (61) and its flag (60, a closed
   window), the realigned sp (33) and the entry sp (2) *)
Ltac cts_awr :=
idtac; lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0' ?fp ?b0 ?bc ?ly ?own =>
let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0' fp b0 bc ly own) end;
repeat first
[ apply awr_ok_nil
| apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]
| lazymatch goal with
  | HU : bv_unsigned (ew _ 38) = _, HO : In (0, _) _ |- _ =>
    eapply (cw_awr_ok_cons_frame _ _ _ _ _ _ _ _ _ _ 0 _ 38%nat);
    [reflexivity | exact HU | exact HO | cbn [YP09.r_wlo]; lia
    | cbn [YP09.r_whi]; change (fs_frame_bytes 0) with 64; lia |] end
| lazymatch goal with
  | HU : bv_unsigned (ew _ 61) = _, HO : In (0, _) _ |- _ =>
    eapply (cw_awr_ok_cons_fshadow _ _ _ _ _ _ _ _ _ _ 0 _ 61%nat);
    [reflexivity | exact HU | exact HO | cbn [YP09.r_wlo]; lia
    | cbn [YP09.r_whi]; change (fs_frame_bytes 0 / 8) with 8; lia |] end
| lazymatch goal with
  | HU : bv_unsigned (ew _ 33) = ?v |- awr_ok _ _ _ ?s0 _ _ _ _ _ =>
    eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 33%nat (v - s0));
    [reflexivity | rewrite HU; lia | cbn [YP09.r_wlo YP09.r_whi]; lia
    | cbn [YP09.r_wlo YP09.r_whi]; lia |] end
| lazymatch goal with
  | HU : bv_unsigned (ew _ 2) = ?v |- awr_ok _ _ _ ?s0 _ _ _ _ _ =>
    eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (v - s0));
    [reflexivity | rewrite HU; lia | cbn [YP09.r_wlo YP09.r_whi]; lia
    | cbn [YP09.r_wlo YP09.r_whi]; lia |] end ].
(* the write windows of such a state: the walk's window, the frame, its shadow, its flag *)
Ltac cts_kwr :=
idtac; let a := fresh "a" in let r := fresh "r" in let Hr := fresh "Hr" in let Hb := fresh "Hb" in
intros a (r & Hr & Hb); cbv beta;
lazymatch type of Hr with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hr end;
repeat (destruct Hr as [<- | Hr]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb; lia |]); destruct Hr.
(* fold a run into the walk's tcj_kept KT: the run writes only the walk's window, its own frame, that
   frame's shadow or its flag byte, and the last three are fresh (HZfr) *)
Ltac cts_keep Fv FLv KTh HARh HZh :=
lazymatch goal with
| HFr1 : frame_of ?Ev ?rs (mrestrict _ ?m1) (mrestrict _ ?m2), HG1 : mem_grows _ _ |- _ =>
  lazymatch type of KTh with
  | tcj_kept tfibsegs ?Bv ?T ?lycv ?Scv ?Wc ?memcv _ _ ?sp ?Ew =>
    lazymatch goal with Lw : AR_laws tfibsegs Bv |- _ =>
    let KR := fresh "KR" in let KT2 := fresh "KT2" in
    pose proof (cw_kept_run (fun a => (sp - T <= a < sp) \/
        ((Fv <= a < Fv + 64) \/ (shadow_addr Fv <= a < shadow_addr Fv + 8) \/ a = FLv))
      Ev rs (w_H Wc) m1 m1 m2 (fun _ _ _ => eq_refl) HFr1 ltac:(cts_kwr)) as KR;
    pose proof (cw_kept_step Bv Lw T lycv Scv Wc memcv _ Wc m1 m2 sp Ew
      (fun a => (sp - T <= a < sp) \/
        ((Fv <= a < Fv + 64) \/ (shadow_addr Fv <= a < shadow_addr Fv + 8) \/ a = FLv))
      ltac:(lia) HARh KTh KR
      ltac:(intros a [Ha | Ha]; [left; exact Ha | right; right; exact (HZh a Ha)])
      ltac:(intros a Hp; exact (apresent_grows _ _ _ a HG1 Hp))) as KT2;
    clear KTh KR; rename KT2 into KT end
  end
end;
repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end;
cw_norm_model.

(* the unsigned values of the walk's atoms in the state's current environment (a run's ewset makes the
   earlier ones stale); cts_awr and the disjointness goals read them *)
Ltac cts_ufacts Fv FLv SP1v spv E38h E60h E61h E33h AGh B2h :=
lazymatch goal with HS : st_ok _ ?Ev _ _ |- _ =>
let n38 := fresh "U38" in let n60 := fresh "U60" in let n61 := fresh "U61" in
let n33 := fresh "U33w" in let n2 := fresh "B2w" in
assert (n38 : bv_unsigned (ew Ev 38) = Fv) by (rewrite E38h; apply unsigned_lit_small; lia);
assert (n60 : bv_unsigned (ew Ev 60) = FLv) by (rewrite E60h; apply unsigned_lit_small; lia);
assert (n61 : bv_unsigned (ew Ev 61) = shadow_addr Fv)
  by (rewrite E61h; apply unsigned_lit_small; unfold shadow_addr, SHADOW_OFF; lia);
assert (n33 : bv_unsigned (ew Ev 33) = SP1v) by (rewrite E33h; apply unsigned_lit_small; lia);
assert (n2 : bv_unsigned (ew Ev 2) = spv) by (rewrite (AGh 2%nat) by lia; exact B2h)
end.


(* one atom fact carried down to the walk's base environment *)
Ltac cts_ebase H :=
repeat first [ rewrite ew_ewset_other in H by lia | rewrite ew_havoc_old in H by (cbn; lia) ].
(* a run that makes tokens extends the environment with ewset; carry the walk's agreement and its atom facts *)
Ltac cts_rebase :=
lazymatch goal with
| AG : forall nn, (nn < 33)%nat -> ew _ nn = ew ?Eb nn, HS : st_ok _ ?Ev _ _ |- _ =>
  let AG2 := fresh "AG2" in
  assert (AG2 : forall nn, (nn < 33)%nat -> ew Ev nn = ew Eb nn)
    by (intros nn Hnn; repeat rewrite ew_ewset_other by lia;
        first [ apply AG; lia
              | reflexivity
              | rewrite <- (AG nn ltac:(lia)); repeat rewrite ew_ewset_other by lia; reflexivity
              | lazymatch goal with |- ew (extK ?E1 ?K ?ws) nn = _ =>
                  rewrite (proj1 (env_agree_extK E1 K ws) nn ltac:(lia)); apply AG; lia end
              | repeat rewrite ew_havoc_old by (cbn; lia); apply AG; lia
              | lazymatch goal with |- ?g => idtac "REBASEFAIL" g; fail end ]);
  clear AG; rename AG2 into AG
end;
repeat match goal with
| H : ew ?Eold ?nn = ?v, HS : st_ok _ ?Ev _ _ |- _ =>
  lazymatch Eold with
  | Ev => fail
  | _ => let H2 := fresh "Eh" in
         assert (H2 : ew Ev nn = v)
           by (repeat first [ rewrite ew_ewset_other by lia | rewrite ew_havoc_old by (cbn; lia) ];
               repeat first [ rewrite ew_ewset_other in H by lia | rewrite ew_havoc_old in H by (cbn; lia) ];
               exact H);
         clear H; rename H2 into H
  end
end.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
(* The shadow byte of an application address is never an application byte: the band sits between the two
   application zones, and the high zone's shadow ends where the high zone starts. *)
Lemma cts_shadow_apart : forall x c m, 0 <= x -> amem_range x 1 -> amem_range c m -> 0 <= m ->
~ (c <= shadow_of_addr SHADOW_OFF x < c + m).
Proof.
intros x c m Hx0 Hx Hc Hm Hin.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold amem_range in Hx, Hc. unfold shadow_of_addr, SHADOW_OFF in Hin.
assert (D0 : 0 <= x / 8) by (apply Z.div_pos; lia).
destruct Hx as [Hx | [Hx1 Hx2]].
- assert (D1 : x / 8 <= 2147450878 / 8) by (apply Z.div_le_mono; lia).
  change (2147450878 / 8) with 268431359 in D1. lia.
- assert (D2 : 17594333495296 / 8 <= x / 8) by (apply Z.div_le_mono; lia).
  assert (D3 : x / 8 <= 140737488355326 / 8) by (apply Z.div_le_mono; lia).
  change (17594333495296 / 8) with 2199291686912 in D2.
  change (140737488355326 / 8) with 17592186044415 in D3. lia.
Qed.

Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis MTF : ameter_fs_laws MT.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.

Hypothesis ML : model_laws (as_universe B).

(* One byte a region's chunk declares, read back from the state. *)
Lemma cts_chunk1 : forall (H : word -> bool) E ss ms i r j off e v,
st_ok tfibsegs E ss (restrict H ms) -> nth_error (ss_mem ss) i = Some r ->
nth_error (YP09.r_chunks r) j = Some (YP09.mkChunk off (CVal 1 e)) ->
YP09.byte_of_word (sv_denot E e) 0 = Z_to_bv 8 (YO0f.le_byte v 1 0) ->
val_mem tfibsegs (mrestrict H (ms_mem ms)) (base_val E (YP09.r_base r) + off) 1 v.
Proof.
intros H E ss ms i r j off e v HS Hi Hj Hb kk Hkk.
replace kk with 0%nat by lia. change (Z.of_nat 0) with 0. rewrite Z.add_0_r.
pose proof (st_ok_mem_ok tfibsegs E ss _ HS) as (_ & Hrs & _). cbn [ms_mem restrict] in Hrs.
pose proof (proj1 (Forall_forall _ _) Hrs r (nth_error_In _ _ Hi)) as (_ & _ & _ & Hcs).
pose proof (proj1 (Forall_forall _ _) Hcs _ (nth_error_In _ _ Hj)) as Hc.
destruct (Hc 0 ltac:(cbn [YP09.c_len YP09.c_val YP09.cv_len Z.of_N]; lia)) as (bb & Hb1 & Hb2).
cbn [YP09.cbyte YP09.c_off YP09.c_val] in Hb1. injection Hb1 as <-.
cbn [YP09.c_off] in Hb2. rewrite Z.add_0_r in Hb2. rewrite Hb2. f_equal. exact Hb.
Qed.
(* A caller object stays in one object of the walk's own state (its blocks are the call state's and its
   frames hold the call state's). *)
Lemma cts_obj_up : forall lyc Sc S2 q n,
(forall b m, In (b, m) (ablocks B lyc Sc) -> In (b, m) (ablocks B lyc S2)) ->
(forall cid pos, In (cid, pos) (frames Sc) -> In (cid, pos) (frames S2)) ->
cobj_ok B lyc Sc q n -> cobj_ok B lyc S2 q n.
Proof.
intros lyc Sc S2 q n Hbl Hfr [(b & m & Hin & Hlo & Hhi) | (cid & pos & Hin & Hlo & Hhi)].
- left. exists b, m. split; [exact (Hbl b m Hin) | split; [exact Hlo | exact Hhi]].
- right. exists cid, pos. split; [exact (Hfr cid pos Hin) | split; [exact Hlo | exact Hhi]].
Qed.
Lemma cts_obj_sub : forall lyc Sc q n n', cobj_ok B lyc Sc q n -> 0 <= n' <= n -> cobj_ok B lyc Sc q n'.
Proof.
intros lyc Sc q n n' [(b & m & Hin & Hlo & Hhi) | (cid & pos & Hin & Hlo & Hhi)] Hn'.
- left. exists b, m. split; [exact Hin | split; lia].
- right. exists cid, pos. split; [exact Hin | split; lia].
Qed.
(* The bytes of a caller object are present and are not the memory-checking runtime's own, in every
   state the walk reaches (from the laws of AR there). *)
Lemma cts_obj_pres : forall ly2 S2 (W2 : world tfibsegs) mem2 md2 q n a,
AR tfibsegs B ly2 S2 W2 mem2 md2 -> cobj_ok B ly2 S2 q n -> q <= a < q + n ->
apresent (w_H W2) mem2 a /\ ~ aowned B ly2 S2 a.
Proof.
intros ly2 S2 W2 mem2 md2 q n a HAR2 Hobj Ha.
destruct Hobj as [(b & m & Hin & Hlo & Hhi) | (cid & pos & Hin & Hlo & Hhi)].
- destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 b m HAR2 Hin) as (_ & _ & _ & _ & Hb & _).
  exact (Hb a ltac:(lia)).
- destruct (al_frames _ _ LAWS ly2 S2 W2 mem2 md2 cid pos HAR2 Hin) as (_ & _ & Hb & _).
  exact (Hb a ltac:(lia)).
Qed.
(* A caller object (cobj_ok: one heap block or one live frame of the call state) keeps its usable marks at a
   later state of the walk: a block's from AR there, a frame's from what the call has kept (tcj_kept's frame
   clause, which keeps the frame's shadow bytes too). *)
Lemma cts_obj_ra : forall lyc Sc (W : world tfibsegs) memc mdc ly2 S2 (W2 : world tfibsegs) mem2 md2 T sp
(Ew : Z -> Prop) q n,
AR tfibsegs B lyc Sc W memc mdc -> AR tfibsegs B ly2 S2 W2 mem2 md2 ->
(forall b m, In (b, m) (ablocks B lyc Sc) -> In (b, m) (ablocks B ly2 S2)) ->
(forall cid pos, frame_addr ly2 cid pos = frame_addr lyc cid pos) ->
cobj_ok B lyc Sc q n -> 0 <= q -> 0 <= n ->
range_addressable (aview tfibsegs (w_H W) memc) SHADOW_OFF q n ->
tcj_kept tfibsegs B T lyc Sc W memc W2 mem2 sp Ew ->
(forall x, q <= x < q + n -> ~ Ew (shadow_of_addr SHADOW_OFF x)) ->
range_addressable (aview tfibsegs (w_H W2) mem2) SHADOW_OFF q n.
Proof.
intros lyc Sc W memc mdc ly2 S2 W2 mem2 md2 T sp Ew q n HAR HAR2 Hbl Hfa Hobj Hq Hn HRA (_ & _ & _ & K4 & _) HE.
destruct Hobj as [(b & m & Hin & Hlo & Hhi) | (cid & pos & Hin & Hlo & Hhi)].
- exact (range_addressable_of_block tfibsegs B LAWS ly2 S2 W2 mem2 md2 b m q n HAR2 (Hbl b m Hin) Hlo Hhi).
- intros x Hx. destruct (HRA x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok].
  rewrite <- Hs.
  destruct (frame_al64 tfibsegs B lyc Sc W memc mdc cid pos HAR Hin) as (HA64 & HB64 & HBpos).
  set (FA := frame_addr lyc cid pos) in *. set (bs := fs_frame_bytes cid) in *.
  assert (HAq : FA = 64 * (FA / 64)) by (pose proof (Z.div_mod FA 64 ltac:(lia)); lia).
  assert (HBq : bs = 64 * (bs / 64)) by (pose proof (Z.div_mod bs 64 ltac:(lia)); lia).
  assert (HA8 : FA / 8 = 8 * (FA / 64))
    by (rewrite HAq at 1; replace (64 * (FA / 64)) with ((8 * (FA / 64)) * 8) by lia; apply Z.div_mul; lia).
  assert (HB8 : bs / 8 = 8 * (bs / 64))
    by (rewrite HBq at 1; replace (64 * (bs / 64)) with ((8 * (bs / 64)) * 8) by lia; apply Z.div_mul; lia).
  assert (Hxs : FA / 8 <= x / 8 < FA / 8 + bs / 8).
  { split; [apply Z.div_le_mono; lia|]. rewrite HA8, HB8. apply Z.div_lt_upper_bound; lia. }
  apply (K4 cid pos (shadow_of_addr SHADOW_OFF x) Hin).
  + right. unfold in_zr, shadow_of_addr, shadow_addr. cbn [fst snd]. fold FA bs. lia.
  + apply HE. exact Hx.
Qed.
(* The bytes of a caller object are kept: a block's by tcj_kept's block clause, a frame's by its frame clause. *)
Lemma cts_obj_keep : forall lyc Sc (W : world tfibsegs) memc (W2 : world tfibsegs) mem2 T sp
(Ew : Z -> Prop) q n x,
cobj_ok B lyc Sc q n -> q <= x < q + n -> ~ Ew x ->
tcj_kept tfibsegs B T lyc Sc W memc W2 mem2 sp Ew ->
aview tfibsegs (w_H W2) mem2 x = aview tfibsegs (w_H W) memc x.
Proof.
intros lyc Sc W memc W2 mem2 T sp Ew q n x Hobj Hx HE (_ & K2 & _ & K4 & _).
destruct Hobj as [(b & m & Hin & Hlo & Hhi) | (cid & pos & Hin & Hlo & Hhi)].
- replace x with (b + (x - b)) by lia. apply (K2 b m (x - b) Hin); [lia|].
  replace (b + (x - b)) with x by lia. exact HE.
- apply (K4 cid pos x Hin); [|exact HE].
  left. unfold in_zr, frame_rng. cbn [fst snd]. lia.
Qed.
(* and so are their values. *)
Lemma cts_obj_val : forall lyc Sc (W : world tfibsegs) memc (W2 : world tfibsegs) mem2 T sp
(Ew : Z -> Prop) q n x (w : nat) v,
cobj_ok B lyc Sc q n -> q <= x -> x + Z.of_nat w <= q + n -> (forall y, x <= y < x + Z.of_nat w -> ~ Ew y) ->
tcj_kept tfibsegs B T lyc Sc W memc W2 mem2 sp Ew ->
val_mem tfibsegs (mrestrict (w_H W) memc) x w v ->
val_mem tfibsegs (mrestrict (w_H W2) mem2) x w v.
Proof.
intros lyc Sc W memc W2 mem2 T sp Ew q n x w v Hobj Hlo Hhi HE HK Hv.
apply (cw_val_mem_kept (w_H W) (w_H W2) memc mem2 x w v); [|exact Hv].
intros y Hy. exact (cts_obj_keep lyc Sc W memc W2 mem2 T sp Ew q n y Hobj ltac:(lia) (HE y Hy) HK).
Qed.
(* The caller's right to let a call write a byte survives the walk taking a frame of its own. *)
Lemma cts_awr_own : forall STK sp0 FP bl0 blc ly cp own a,
awr_byte STK sp0 FP bl0 blc ly own a -> awr_byte STK sp0 FP bl0 blc ly (cp :: own) a.
Proof.
intros STK sp0 FP bl0 blc ly cp own a [H | [H | [H | (cid & pos & Hin & Hz)]]].
- left. exact H.
- right. left. exact H.
- right. right. left. exact H.
- right. right. right. exists cid, pos. split; [right; exact Hin | exact Hz].
Qed.
(* The shadow bytes of a caller object's 8-byte window are readable at any state of the walk: a block's
   and a frame's by the laws of AR there. *)
Lemma cts_obj_hull : forall lyc Sc S2 (W2 : world tfibsegs) mem2 md2 q n,
AR tfibsegs B lyc S2 W2 mem2 md2 ->
(forall b m, In (b, m) (ablocks B lyc Sc) -> In (b, m) (ablocks B lyc S2)) ->
(forall cid pos, In (cid, pos) (frames Sc) -> In (cid, pos) (frames S2)) ->
cobj_ok B lyc Sc q n -> 0 < n -> shadow_hull_vis (aview tfibsegs (w_H W2) mem2) q n.
Proof.
intros lyc Sc S2 W2 mem2 md2 q n HAR Hbl Hfr Hobj Hn.
destruct Hobj as [(b & m & Hin & Hlo & Hhi) | (cid & pos & Hin & Hlo & Hhi)].
- exact (shadow_hull_vis_of_block tfibsegs B LAWS lyc S2 W2 mem2 md2 b m q n HAR (Hbl b m Hin) Hlo Hhi Hn).
- exact (shadow_hull_vis_of_frame tfibsegs B LAWS lyc S2 W2 mem2 md2 cid pos q n HAR (Hfr cid pos Hin) Hlo Hhi Hn).
Qed.



(* ===================== the cut at 0x839b8, the return of diginet_scribble_text =====================
   The walk of 0x83798-0x839b4 delivers this state; the tail (the test of the used count, the bcmp
   wrapper, the inlined fuzz_all over the record's bytes [n, 24), the class-0 release and the leaf)
   takes it. F is the walk's own frame and fpos its position. *)
Definition A_CTS_RET : Z := 0x839b8.
(* the twelve saves of the prologue, at [sp - 96, sp) of the entry stack pointer *)
Definition cts_saves (m : word -> option byte) (sp : Z) (regs : bvmap 5 word) : Prop :=
val_mem tfibsegs m (sp - 8) 8 (bv_unsigned (getr regs 1)) /\
val_mem tfibsegs m (sp - 16) 8 (bv_unsigned (getr regs 8)) /\
val_mem tfibsegs m (sp - 24) 8 (bv_unsigned (getr regs 9)) /\
val_mem tfibsegs m (sp - 32) 8 (bv_unsigned (getr regs 18)) /\
val_mem tfibsegs m (sp - 40) 8 (bv_unsigned (getr regs 19)) /\
val_mem tfibsegs m (sp - 48) 8 (bv_unsigned (getr regs 20)) /\
val_mem tfibsegs m (sp - 56) 8 (bv_unsigned (getr regs 21)) /\
val_mem tfibsegs m (sp - 64) 8 (bv_unsigned (getr regs 22)) /\
val_mem tfibsegs m (sp - 72) 8 (bv_unsigned (getr regs 23)) /\
val_mem tfibsegs m (sp - 80) 8 (bv_unsigned (getr regs 24)) /\
val_mem tfibsegs m (sp - 88) 8 (bv_unsigned (getr regs 25)) /\
val_mem tfibsegs m (sp - 96) 8 (bv_unsigned (getr regs 26)).
(* the eight shadow bytes of a class-0 frame while want is in scope: f1 x4 | 00 | f3 x3 *)
Definition cts_shm_live : list Z := [241; 241; 241; 241; 0; 243; 243; 243].
(* The five regions the walk carries at the record memset 0x83998: the frame's flag byte, the frame's
   eight shadow bytes, the frame with its flag pointer at F + 56, the spill of F at 24(s1) and the
   twelve saved words of the prologue. *)
Definition cts_rec_regions : smem :=
[ YP09.mkRegion (Some 60%nat) 0 1 0 0 [];
  YP09.mkRegion (Some 61%nat) 0 8 0 0
    [YP09.mkChunk 3 (CVal 1 (SLit 18446744073709551601));
     YP09.mkChunk 2 (CVal 1 (SLit 18446744073709551601));
     YP09.mkChunk 1 (CVal 1 (SLit 18446744073709551601));
     YP09.mkChunk 0 (CVal 1 (SLit 18446744073709551601));
     YP09.mkChunk 7 (CVal 1 (SLit 18446744073709551603));
     YP09.mkChunk 6 (CVal 1 (SLit 18446744073709551603));
     YP09.mkChunk 5 (CVal 1 (SLit 18446744073709551603));
     YP09.mkChunk 4 (CVal 1 (SLit 0))];
  YP09.mkRegion (Some 38%nat) 40 64 40 40 [YP09.mkChunk 56 (CVal 8 (SOff 60 0))];
  YP09.mkRegion (Some 33%nat) 24 32 24 32 [YP09.mkChunk 24 (CVal 8 (SOff 38 0))];
  YP09.mkRegion (Some 2%nat) (-96) 0 (-96) 0
    [YP09.mkChunk (-96) (CVal 8 (SOff 26 0)); YP09.mkChunk (-88) (CVal 8 (SOff 25 0));
     YP09.mkChunk (-80) (CVal 8 (SOff 24 0)); YP09.mkChunk (-72) (CVal 8 (SOff 23 0));
     YP09.mkChunk (-64) (CVal 8 (SOff 22 0)); YP09.mkChunk (-56) (CVal 8 (SOff 21 0));
     YP09.mkChunk (-48) (CVal 8 (SOff 20 0)); YP09.mkChunk (-40) (CVal 8 (SOff 19 0));
     YP09.mkChunk (-32) (CVal 8 (SOff 18 0)); YP09.mkChunk (-24) (CVal 8 (SOff 9 0));
     YP09.mkChunk (-16) (CVal 8 (SOff 8 0)); YP09.mkChunk (-8) (CVal 8 (SOff 1 0))] ].
(* Every memory fact the cut needs, read off the five regions in one place (the walk's own proof
   context is far too large to read them one chunk at a time there). *)
Lemma cts_mem_at_rec : forall (H : word -> bool) E ss ms (regs : bvmap 5 word) sp Fv FLv,
st_ok tfibsegs E ss (restrict H ms) -> ss_mem ss = cts_rec_regions ->
bv_unsigned (ew E 2) = sp -> bv_unsigned (ew E 38) = Fv ->
bv_unsigned (ew E 60) = FLv -> bv_unsigned (ew E 61) = shadow_addr Fv ->
(forall nn (r : bv 5), (nn < 33)%nat -> Z.of_nat nn = bv_unsigned r -> ew E nn = getr regs r) ->
cts_saves (mrestrict H (ms_mem ms)) sp regs /\
val_mem tfibsegs (mrestrict H (ms_mem ms)) (Fv + 56) 8 FLv /\
YI00.garr8 tfibsegs (mrestrict H (ms_mem ms)) (shadow_addr Fv) cts_shm_live.
Proof.
intros H E ss ms regs sp Fv FLv HS Hm Hsp HF HFL HSh HE.
assert (CV8 : forall i r j off nn (rr : bv 5), nth_error (ss_mem ss) i = Some r ->
  nth_error (YP09.r_chunks r) j = Some (YP09.mkChunk off (CVal 8 (SOff nn 0))) ->
  (nn < 33)%nat -> Z.of_nat nn = bv_unsigned rr ->
  val_mem tfibsegs (mrestrict H (ms_mem ms)) (base_val E (YP09.r_base r) + off) 8
    (bv_unsigned (getr regs rr))).
{ intros i r j off nn rr Hi Hj Hlt Hnr. rewrite <- (HE nn rr Hlt Hnr).
  exact (AF0x.st_ok_chunk_val H E ss ms i r j off 8%N (SOff nn 0) (bv_unsigned (ew E nn)) HS Hi Hj
    ltac:(cbn [sv_denot]; rewrite Z.add_0_r; reflexivity)
    ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); apply u64_range)
    ltac:(cbn; lia)). }
assert (CV1 : forall i r j off z v, nth_error (ss_mem ss) i = Some r ->
  nth_error (YP09.r_chunks r) j = Some (YP09.mkChunk off (CVal 1 (SLit z))) ->
  YP09.byte_of_word (sv_denot E (SLit z)) 0 = Z_to_bv 8 (YO0f.le_byte v 1 0) ->
  val_mem tfibsegs (mrestrict H (ms_mem ms)) (base_val E (YP09.r_base r) + off) 1 v).
{ intros i r j off z v Hi Hj Hb. exact (cts_chunk1 H E ss ms i r j off (SLit z) v HS Hi Hj Hb). }
pose proof (CV8 4%nat _ 11%nat _ 1%nat (1%bv) ltac:(rewrite Hm; reflexivity)
  ltac:(reflexivity) ltac:(cbv; lia) ltac:(reflexivity)) as Vs1;
  cbn [base_val YP09.r_base] in Vs1; rewrite Hsp in Vs1.
pose proof (CV8 4%nat _ 10%nat _ 8%nat (8%bv) ltac:(rewrite Hm; reflexivity)
  ltac:(reflexivity) ltac:(cbv; lia) ltac:(reflexivity)) as Vs8;
  cbn [base_val YP09.r_base] in Vs8; rewrite Hsp in Vs8.
pose proof (CV8 4%nat _ 9%nat _ 9%nat (9%bv) ltac:(rewrite Hm; reflexivity)
  ltac:(reflexivity) ltac:(cbv; lia) ltac:(reflexivity)) as Vs9;
  cbn [base_val YP09.r_base] in Vs9; rewrite Hsp in Vs9.
pose proof (CV8 4%nat _ 8%nat _ 18%nat (18%bv) ltac:(rewrite Hm; reflexivity)
  ltac:(reflexivity) ltac:(cbv; lia) ltac:(reflexivity)) as Vs18;
  cbn [base_val YP09.r_base] in Vs18; rewrite Hsp in Vs18.
pose proof (CV8 4%nat _ 7%nat _ 19%nat (19%bv) ltac:(rewrite Hm; reflexivity)
  ltac:(reflexivity) ltac:(cbv; lia) ltac:(reflexivity)) as Vs19;
  cbn [base_val YP09.r_base] in Vs19; rewrite Hsp in Vs19.
pose proof (CV8 4%nat _ 6%nat _ 20%nat (20%bv) ltac:(rewrite Hm; reflexivity)
  ltac:(reflexivity) ltac:(cbv; lia) ltac:(reflexivity)) as Vs20;
  cbn [base_val YP09.r_base] in Vs20; rewrite Hsp in Vs20.
pose proof (CV8 4%nat _ 5%nat _ 21%nat (21%bv) ltac:(rewrite Hm; reflexivity)
  ltac:(reflexivity) ltac:(cbv; lia) ltac:(reflexivity)) as Vs21;
  cbn [base_val YP09.r_base] in Vs21; rewrite Hsp in Vs21.
pose proof (CV8 4%nat _ 4%nat _ 22%nat (22%bv) ltac:(rewrite Hm; reflexivity)
  ltac:(reflexivity) ltac:(cbv; lia) ltac:(reflexivity)) as Vs22;
  cbn [base_val YP09.r_base] in Vs22; rewrite Hsp in Vs22.
pose proof (CV8 4%nat _ 3%nat _ 23%nat (23%bv) ltac:(rewrite Hm; reflexivity)
  ltac:(reflexivity) ltac:(cbv; lia) ltac:(reflexivity)) as Vs23;
  cbn [base_val YP09.r_base] in Vs23; rewrite Hsp in Vs23.
pose proof (CV8 4%nat _ 2%nat _ 24%nat (24%bv) ltac:(rewrite Hm; reflexivity)
  ltac:(reflexivity) ltac:(cbv; lia) ltac:(reflexivity)) as Vs24;
  cbn [base_val YP09.r_base] in Vs24; rewrite Hsp in Vs24.
pose proof (CV8 4%nat _ 1%nat _ 25%nat (25%bv) ltac:(rewrite Hm; reflexivity)
  ltac:(reflexivity) ltac:(cbv; lia) ltac:(reflexivity)) as Vs25;
  cbn [base_val YP09.r_base] in Vs25; rewrite Hsp in Vs25.
pose proof (CV8 4%nat _ 0%nat _ 26%nat (26%bv) ltac:(rewrite Hm; reflexivity)
  ltac:(reflexivity) ltac:(cbv; lia) ltac:(reflexivity)) as Vs26;
  cbn [base_val YP09.r_base] in Vs26; rewrite Hsp in Vs26.
pose proof (AF0x.st_ok_chunk_val H E ss ms 2%nat
  (YP09.mkRegion (Some 38%nat) 40 64 40 40 [YP09.mkChunk 56 (CVal 8 (SOff 60 0))])
  0%nat 56 8%N (SOff 60 0) FLv HS ltac:(rewrite Hm; reflexivity) ltac:(reflexivity)
  ltac:(cbn [sv_denot]; rewrite Z.add_0_r, HFL; reflexivity)
  ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); rewrite <- HFL; apply u64_range)
  ltac:(cbn; lia)) as VFL.
cbn [base_val YP09.r_base] in VFL. rewrite HF in VFL.
pose proof (CV1 1%nat _ 0%nat _ _ 241 ltac:(rewrite Hm; reflexivity) ltac:(reflexivity)
  ltac:(cbn [sv_denot]; apply bv_eq; vm_compute; reflexivity)) as Vh3;
  cbn [base_val YP09.r_base] in Vh3; rewrite HSh in Vh3.
pose proof (CV1 1%nat _ 1%nat _ _ 241 ltac:(rewrite Hm; reflexivity) ltac:(reflexivity)
  ltac:(cbn [sv_denot]; apply bv_eq; vm_compute; reflexivity)) as Vh2;
  cbn [base_val YP09.r_base] in Vh2; rewrite HSh in Vh2.
pose proof (CV1 1%nat _ 2%nat _ _ 241 ltac:(rewrite Hm; reflexivity) ltac:(reflexivity)
  ltac:(cbn [sv_denot]; apply bv_eq; vm_compute; reflexivity)) as Vh1;
  cbn [base_val YP09.r_base] in Vh1; rewrite HSh in Vh1.
pose proof (CV1 1%nat _ 3%nat _ _ 241 ltac:(rewrite Hm; reflexivity) ltac:(reflexivity)
  ltac:(cbn [sv_denot]; apply bv_eq; vm_compute; reflexivity)) as Vh0;
  cbn [base_val YP09.r_base] in Vh0; rewrite HSh in Vh0.
pose proof (CV1 1%nat _ 4%nat _ _ 243 ltac:(rewrite Hm; reflexivity) ltac:(reflexivity)
  ltac:(cbn [sv_denot]; apply bv_eq; vm_compute; reflexivity)) as Vh7;
  cbn [base_val YP09.r_base] in Vh7; rewrite HSh in Vh7.
pose proof (CV1 1%nat _ 5%nat _ _ 243 ltac:(rewrite Hm; reflexivity) ltac:(reflexivity)
  ltac:(cbn [sv_denot]; apply bv_eq; vm_compute; reflexivity)) as Vh6;
  cbn [base_val YP09.r_base] in Vh6; rewrite HSh in Vh6.
pose proof (CV1 1%nat _ 6%nat _ _ 243 ltac:(rewrite Hm; reflexivity) ltac:(reflexivity)
  ltac:(cbn [sv_denot]; apply bv_eq; vm_compute; reflexivity)) as Vh5;
  cbn [base_val YP09.r_base] in Vh5; rewrite HSh in Vh5.
pose proof (CV1 1%nat _ 7%nat _ _ 0 ltac:(rewrite Hm; reflexivity) ltac:(reflexivity)
  ltac:(cbn [sv_denot]; apply bv_eq; vm_compute; reflexivity)) as Vh4;
  cbn [base_val YP09.r_base] in Vh4; rewrite HSh in Vh4.
split.
{ unfold cts_saves. repeat split;
  [ exact Vs1 | exact Vs8 | exact Vs9 | exact Vs18 | exact Vs19 | exact Vs20
  | exact Vs21 | exact Vs22 | exact Vs23 | exact Vs24 | exact Vs25 | exact Vs26 ]. }
split; [exact VFL|].
intros jj Hjj. cbn [length cts_shm_live] in Hjj.
destruct jj as [|[|[|[|[|[|[|[|jj]]]]]]]]; cbn [nth cts_shm_live Z.of_nat];
  try (exfalso; cbn in Hjj; lia).
- split; [exact Vh0 | lia].
- split; [exact Vh1 | lia].
- split; [exact Vh2 | lia].
- split; [exact Vh3 | lia].
- split; [exact Vh4 | lia].
- split; [exact Vh5 | lia].
- split; [exact Vh6 | lia].
- split; [exact Vh7 | lia].
Qed.
(* The state at the record's memset 0x83998, where the n = 0 arm and the pad of want join: the frame
   and the text in the callee-saved registers, the used count in the join's own atom, the dead
   registers in the join window from 400. *)
Definition cts_deadR : list nat := [1;5;6;7;10;11;12;13;14;15;16;17;28;29;30;31;26]%nat.
Definition cts_deadR_bv : list (bv 5) := [1;5;6;7;10;11;12;13;14;15;16;17;28;29;30;31;26]%bv.
Definition cts_rec_atoms : list (nat * afact) :=
[(10%nat, mkAF 1 140737488355326 0);
 (61%nat, mkAF 2147451392 17594333495296 3);
 (60%nat, mkAF 4096 140737479966720 0);
 (38%nat, mkAF 4096 140737479966720 6);
 (33%nat, mkAF 70368744177408 140737488355328 5);
 (2%nat, mkAF 70368744177664 140737488355328 4);
 (32%nat, mkAF 2147450880 2147450880 0);
 (12%nat, mkAF 0 8 0)].
Definition cts_ss_rec_0 : sstate :=
mkSS 0x83998
[SLit 0; SOff 1 0; SOff 33 0; SOff 3 0; SOff 4 0; SOff 5 0; SOff 6 0; SOff 7 0;
 SOff 2 0; SOff 33 0; SOff 10 0; SOff 11 0; SOff 12 0; SOff 13 0; SOff 14 0; SOff 15 0;
 SOff 16 0; SOff 17 0; SOff 38 0; SOff 12 0; SOff 11 0; SOff 10 0; SOff 38 32; SOff 32 0;
 SOff 61 0; SOff 38 0; SOff 26 0; SOff 27 0; SOff 28 0; SOff 29 0; SOff 30 0; SOff 31 0]
cts_rec_regions None (mkFacts cts_rec_atoms [] []).
Definition cts_ss_rec : sstate := Eval vm_compute in ss_havoc_regs cts_ss_rec_0 400%nat cts_deadR.
(* The state at the pad of want, 0x83984, where the three exits of the inlined owed_scribble_text
   join: the output slots done in atom 417, the text bytes used in atom 418. *)
Definition cts_deadP : list nat := [1;5;6;7;10;12;13;14;15;16;17;28;29;30;31]%nat.
Definition cts_deadP_bv : list (bv 5) := [1;5;6;7;10;12;13;14;15;16;17;28;29;30;31]%bv.
Definition cts_ss_pad_0 : sstate :=
mkSS 0x83984
[SLit 0; SOff 1 0; SOff 33 0; SOff 3 0; SOff 4 0; SOff 5 0; SOff 6 0; SOff 7 0;
 SOff 2 0; SOff 33 0; SOff 10 0; SOff 417 0; SOff 12 0; SOff 13 0; SOff 14 0; SOff 15 0;
 SOff 16 0; SOff 17 0; SOff 38 0; SOff 12 0; SOff 11 0; SOff 10 0; SOff 38 32; SOff 32 0;
 SOff 61 0; SOff 38 0; SOff 418 0; SOff 27 0; SOff 28 0; SOff 29 0; SOff 30 0; SOff 31 0]
cts_rec_regions None (mkFacts cts_rec_atoms [] []).
Definition cts_ss_pad : sstate := Eval vm_compute in ss_havoc_regs cts_ss_pad_0 420%nat cts_deadP.
(* The head of the inlined owed_scribble_text loop, 0x838d0: a1 = the output slots done (atom 417),
   s10 = the text bytes used (atom 418), a5 = the text byte at that index (atom 419), a2 = q + 1,
   a3 = 46 and a4 = 8 the two constants the body compares against. *)
Definition cts_deadL : list nat := [1;5;6;7;10;16;17;28;29;30;31]%nat.
Definition cts_deadL_bv : list (bv 5) := [1;5;6;7;10;16;17;28;29;30;31]%bv.
Definition cts_lp_atoms : list (nat * afact) :=
(419%nat, mkAF 0 255 0) :: (417%nat, mkAF 0 8 0) :: cts_rec_atoms.
Definition cts_ss_lp_0 : sstate :=
mkSS 0x838d0
[SLit 0; SOff 1 0; SOff 33 0; SOff 3 0; SOff 4 0; SOff 5 0; SOff 6 0; SOff 7 0;
 SOff 2 0; SOff 33 0; SOff 10 0; SOff 417 0; SOff 10 1; SLit 46; SLit 8; SOff 419 0;
 SOff 16 0; SOff 17 0; SOff 38 0; SOff 12 0; SOff 11 0; SOff 10 0; SOff 38 32; SOff 32 0;
 SOff 61 0; SOff 38 0; SOff 418 0; SOff 27 0; SOff 28 0; SOff 29 0; SOff 30 0; SOff 31 0]
cts_rec_regions None (mkFacts cts_lp_atoms [] []).
Definition cts_ss_lp : sstate := Eval vm_compute in ss_havoc_regs cts_ss_lp_0 440%nat cts_deadL.

(* What the walk hands the pad of want at 0x83984, and what the loop must deliver to it. o output
   slots are done, i text bytes are used, pre is what want already holds. *)
Definition cts_pad_cont
(STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world tfibsegs)
(mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (lyc : alayout) (Sc : astate)
(W : world tfibsegs) (memc : word -> option byte) (mdc : Model) (k : Z) (regs : bvmap 5 word)
(ch n : Z) (tb : list Z) (S2 : astate) (fpos SP1 : Z) (E0 : env)
(Q : world tfibsegs -> config -> Prop) : Prop :=
forall (EZ : env) (msZ : machine_state) (mdZ : Model) (o i : Z) (pre : list Z),
st_ok tfibsegs EZ cts_ss_pad (restrict (w_H W) msZ) ->
sh_ok tfibsegs CW_Bx [] EZ (mrestrict (w_H W) (ms_mem msZ)) ->
(forall nn, (nn < 33)%nat -> ew EZ nn = ew E0 nn) ->
ew EZ 33 = Z_to_bv 64 SP1 -> ew EZ 38 = Z_to_bv 64 (frame_addr lyc 0 fpos) ->
ew EZ 60 = Z_to_bv 64 (flag_addr lyc 0 fpos) ->
ew EZ 61 = Z_to_bv 64 (shadow_addr (frame_addr lyc 0 fpos)) ->
ew EZ 417 = Z_to_bv 64 o -> ew EZ 418 = Z_to_bv 64 i ->
ajournal tfibsegs B STK sp0 FP ly S W0 mem0 md0 ((0, fpos) :: own) lyc S2 W (ms_mem msZ) mdZ k ->
tcj_kept tfibsegs B T_check_text_scribble lyc Sc W memc W (ms_mem msZ) (spZ regs)
  (fun x => ch <= x < ch + 24) ->
same_io mdc mdZ ->
0 <= o <= n -> 0 <= i < 2 ^ 46 -> length pre = Z.to_nat o ->
fst (owed_scribble_text_spec tb n) = pre ++ repeat 32 (Z.to_nat n - Z.to_nat o) ->
snd (owed_scribble_text_spec tb n) = i ->
YI00.garr8 tfibsegs (mrestrict (w_H W) (ms_mem msZ)) (frame_addr lyc 0 fpos + 32) pre ->
SRr tfibsegs W (mkCfg msZ mdZ) Q.

(* The inlined owed_scribble_text loop 0x838d0-0x83958, from its head to the pad of want: one output
   byte a turn, three instrumented checks a turn, and at most n - o turns. *)
Definition cts_loop_goal
(STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world tfibsegs)
(mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (lyc : alayout) (Sc : astate)
(W : world tfibsegs) (memc : word -> option byte) (mdc : Model) (k : Z) (regs : bvmap 5 word)
(q ch n : Z) (tb cj : list Z) (S2 : astate) (fpos SP1 : Z) (E0 : env)
(Q : world tfibsegs -> config -> Prop) : Prop :=
(* what the walk has proved before the loop *)
cdc_entry tfibsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs T_check_text_scribble ->
getr regs 10 = w64 q -> getr regs 11 = w64 ch -> getr regs 12 = w64 n -> 0 <= n <= 8 ->
cstr_rd tfibsegs W memc (spZ regs) T_check_text_scribble q tb ->
cobj_ok B lyc Sc q (Z.of_nat (length tb)) -> cobj_ok B lyc Sc ch 24 ->
cdst_ok tfibsegs B STK sp0 FP ly S lyc Sc own W memc (spZ regs) T_check_text_scribble ch 24 ->
(q + Z.of_nat (length tb) <= ch \/ ch + 24 <= q) ->
(forall nn (r : bv 5), Z.of_nat nn = bv_unsigned r -> ew E0 nn = getr regs r) ->
ew E0 32 = Z_to_bv 64 SB ->
In (0, fpos) (frames S2) -> frames S2 = (0, fpos) :: frames Sc ->
ablocks B lyc S2 = ablocks B lyc Sc ->
spZ regs - 144 <= SP1 <= spZ regs - 128 -> SP1 mod 32 = 0 ->
(* the pad of want takes the loop's result *)
cts_pad_cont STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ch n tb S2 fpos SP1 E0 Q ->
(* the loop head *)
forall (EZ : env) (msZ : machine_state) (mdZ : Model) (o i : Z) (pre : list Z),
st_ok tfibsegs EZ cts_ss_lp (restrict (w_H W) msZ) ->
sh_ok tfibsegs CW_Bx [] EZ (mrestrict (w_H W) (ms_mem msZ)) ->
(forall nn, (nn < 33)%nat -> ew EZ nn = ew E0 nn) ->
ew EZ 33 = Z_to_bv 64 SP1 -> ew EZ 38 = Z_to_bv 64 (frame_addr lyc 0 fpos) ->
ew EZ 60 = Z_to_bv 64 (flag_addr lyc 0 fpos) ->
ew EZ 61 = Z_to_bv 64 (shadow_addr (frame_addr lyc 0 fpos)) ->
ew EZ 417 = Z_to_bv 64 o -> ew EZ 418 = Z_to_bv 64 i ->
ew EZ 419 = Z_to_bv 64 (nth (Z.to_nat i) tb 0) ->
ajournal tfibsegs B STK sp0 FP ly S W0 mem0 md0 ((0, fpos) :: own) lyc S2 W (ms_mem msZ) mdZ k ->
tcj_kept tfibsegs B T_check_text_scribble lyc Sc W memc W (ms_mem msZ) (spZ regs)
  (fun x => ch <= x < ch + 24) ->
same_io mdc mdZ ->
0 <= o < n -> 0 <= i < Z.of_nat (length (cts_cstr tb)) ->
length pre = Z.to_nat o -> cts_MODEL tb (Z.to_nat n) o i pre ->
YI00.garr8 tfibsegs (mrestrict (w_H W) (ms_mem msZ)) (frame_addr lyc 0 fpos + 32) pre ->
YI00.garr8 tfibsegs (mrestrict (w_H W) (ms_mem msZ)) q tb ->
range_addressable (aview tfibsegs (w_H W) (ms_mem msZ)) SHADOW_OFF q (Z.of_nat (length tb)) ->
SRr tfibsegs W (mkCfg msZ mdZ) Q.
Definition cts_cut_ret
(STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world tfibsegs)
(mem0 : word -> option byte) md0 (own : list (Z * Z)) (lyc : alayout) (Sc : astate)
(W : world tfibsegs) (memc : word -> option byte) mdc (k : Z) (regs : bvmap 5 word)
(q ch n : Z) (tb cj : list Z)
(ly3 : alayout) (S3 : astate) (W3 : world tfibsegs) (regs3 : bvmap 5 word)
(mem3 : word -> option byte) md3 (fpos : Z) : Prop :=
let F := frame_addr ly3 0 fpos in
(* what the caller gave, and what the walk still owes its contract *)
cdc_entry tfibsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs T_check_text_scribble /\
getr regs 10 = w64 q /\ getr regs 11 = w64 ch /\ getr regs 12 = w64 n /\ 0 <= n <= 8 /\
cobj_ok B lyc Sc ch 24 /\
cdst_ok tfibsegs B STK sp0 FP ly S lyc Sc own W memc (spZ regs) T_check_text_scribble ch 24 /\
length cj = 24%nat /\
owed_scribble_text_spec tb n = scribble_text_spec tb n /\
(* the text part of the record is exactly n bytes long, so the bytes from n on are the fill byte *)
length (fst (scribble_text_spec tb n)) = Z.to_nat n /\
(* the walk's state at the return: its own frame on top of the call state's, the blocks a permutation *)
ajournal tfibsegs B STK sp0 FP ly S W0 mem0 md0 ((0, fpos) :: own) ly3 S3 W3 mem3 md3 k /\
In (0, fpos) (frames S3) /\ frames S3 = (0, fpos) :: frames Sc /\
Permutation (ablocks B ly3 S3) (ablocks B lyc Sc) /\
same_io mdc md3 /\ mo_le MT Sc S3 0 /\
tcj_kept tfibsegs B T_check_text_scribble lyc Sc W memc W3 mem3 (spZ regs)
  (fun x => ch <= x < ch + 24) /\
(* the realigned stack pointer, and the registers the tail reads *)
spZ regs - 144 <= spZ regs3 <= spZ regs - 128 /\ spZ regs3 mod 32 = 0 /\
getr regs3 3 = w64 (as_gp B) /\ getr regs3 4 = w64 (as_tp B) /\
getr regs3 8 = getr regs 2 /\ getr regs3 9 = getr regs3 2 /\
getr regs3 10 = w64 (snd (scribble_text_spec tb n)) /\
getr regs3 18 = w64 F /\ getr regs3 25 = w64 F /\
getr regs3 19 = w64 n /\ getr regs3 20 = w64 ch /\ getr regs3 21 = w64 q /\
getr regs3 22 = w64 (F + 32) /\ getr regs3 23 = w64 SB /\
getr regs3 24 = w64 (shadow_addr F) /\
getr regs3 26 = w64 (snd (owed_scribble_text_spec tb n)) /\
(* s11 is never saved nor written by this function, so the leaf's aregs_preserved reads it here *)
getr regs3 27 = getr regs 27 /\
(* the memory the tail reads: the record as the memset and the callee left it, want as the inlined
   owed_scribble_text left it, the frame's flag pointer at F + 56, its eight shadow bytes, the saves *)
YI00.garr8 tfibsegs (mrestrict (w_H W3) mem3) ch
  (fst (scribble_text_spec tb n) ++ repeat 165 (Z.to_nat (24 - n))) /\
YI00.garr8 tfibsegs (mrestrict (w_H W3) mem3) (F + 32) (fst (owed_scribble_text_spec tb n)) /\
val_mem tfibsegs (mrestrict (w_H W3) mem3) (F + 56) 8 (flag_addr ly3 0 fpos) /\
YI00.garr8 tfibsegs (mrestrict (w_H W3) mem3) (shadow_addr F) cts_shm_live /\
cts_saves (mrestrict (w_H W3) mem3) (spZ regs) regs.
(* What the tail must prove from that cut. *)
Definition cts_tail_goal
(STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world tfibsegs)
(mem0 : word -> option byte) md0 (own : list (Z * Z)) (lyc : alayout) (Sc : astate)
(W : world tfibsegs) (memc : word -> option byte) mdc (k : Z) (regs : bvmap 5 word)
(ch n : Z) (tb : list Z)
(W3 : world tfibsegs) (regs3 : bvmap 5 word) (mem3 : word -> option byte) md3 : Prop :=
SRr tfibsegs W3 (cfg_at tfibsegs A_CTS_RET regs3 mem3 md3)
(cdc_post tfibsegs B MT STK sp0 FP ly S W0 mem0 md0 own k regs T_check_text_scribble
   (fun x => ch <= x < ch + 24) lyc Sc W memc mdc
   (fun W2 mem2 (regs2 : bvmap 5 word) =>
      YI00.garr8 tfibsegs (mrestrict (w_H W2) mem2) ch (scribble_bytes tb n))).
(* What the walk has established when it reaches the record point or the pad of want: the caller's premises
   (the contract's, less the record's old bytes and the frame count), the walk's base environment E0, its
   class-0 frame (0, fpos) on top of the call state's frames, and the realigned stack pointer SP1. *)
Definition cts_fctx
(STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world tfibsegs)
(mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (lyc : alayout) (Sc : astate)
(W : world tfibsegs) (memc : word -> option byte) (mdc : Model) (k : Z) (regs : bvmap 5 word)
(q ch n : Z) (tb cj : list Z) (S2 : astate) (fpos SP1 : Z) (E0 : env) : Prop :=
cdc_entry tfibsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs T_check_text_scribble /\
getr regs 10 = w64 q /\ cstr_rd tfibsegs W memc (spZ regs) T_check_text_scribble q tb /\
cobj_ok B lyc Sc q (Z.of_nat (length tb)) /\ cobj_ok B lyc Sc ch 24 /\
getr regs 11 = w64 ch /\
cdst_ok tfibsegs B STK sp0 FP ly S lyc Sc own W memc (spZ regs) T_check_text_scribble ch 24 /\
length cj = 24%nat /\ getr regs 12 = w64 n /\ 0 <= n <= 8 /\
(q + Z.of_nat (length tb) <= ch \/ ch + 24 <= q) /\
owed_scribble_text_spec tb n = scribble_text_spec tb n /\
(forall nn (r : bv 5), Z.of_nat nn = bv_unsigned r -> ew E0 nn = getr regs r) /\
ew E0 32 = Z_to_bv 64 SB /\
frames S2 = (0, fpos) :: frames Sc /\ ablocks B lyc S2 = ablocks B lyc Sc /\ mo_le MT Sc S2 0 /\
spZ regs - 144 <= SP1 <= spZ regs - 128 /\ SP1 mod 32 = 0.
(* The continuation at the record point 0x83998 (cts_ss_rec): the used count in atom 416, want complete. *)
Definition cts_rec_cont
(STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world tfibsegs)
(mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (lyc : alayout) (Sc : astate)
(W : world tfibsegs) (memc : word -> option byte) (mdc : Model) (k : Z) (regs : bvmap 5 word)
(ch n : Z) (tb : list Z) (S2 : astate) (fpos SP1 : Z) (E0 : env)
(Q : world tfibsegs -> config -> Prop) : Prop :=
forall (EZ : env) (msZ : machine_state) (mdZ : Model),
st_ok tfibsegs EZ cts_ss_rec (restrict (w_H W) msZ) ->
sh_ok tfibsegs CW_Bx [] EZ (mrestrict (w_H W) (ms_mem msZ)) ->
(forall nn, (nn < 33)%nat -> ew EZ nn = ew E0 nn) ->
ew EZ 33 = Z_to_bv 64 SP1 -> ew EZ 38 = Z_to_bv 64 (frame_addr lyc 0 fpos) ->
ew EZ 60 = Z_to_bv 64 (flag_addr lyc 0 fpos) ->
ew EZ 61 = Z_to_bv 64 (shadow_addr (frame_addr lyc 0 fpos)) ->
ew EZ 416 = w64 (snd (owed_scribble_text_spec tb n)) ->
ajournal tfibsegs B STK sp0 FP ly S W0 mem0 md0 ((0, fpos) :: own) lyc S2 W (ms_mem msZ) mdZ k ->
tcj_kept tfibsegs B T_check_text_scribble lyc Sc W memc W (ms_mem msZ) (spZ regs)
  (fun x => ch <= x < ch + 24) ->
same_io mdc mdZ ->
YI00.garr8 tfibsegs (mrestrict (w_H W) (ms_mem msZ)) (frame_addr lyc 0 fpos + 32)
  (fst (owed_scribble_text_spec tb n)) ->
SRr tfibsegs W (mkCfg msZ mdZ) Q.
End d.
End b.
