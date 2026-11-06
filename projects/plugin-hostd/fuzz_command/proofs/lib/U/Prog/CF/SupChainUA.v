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
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/rec_canonical.v, with its module paths and module names changed; 696 of its 835 lines of code are new or changed and 2224 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/U/Prog/CF/rec_canonical.v, with its module paths, module names, addresses and numbers changed; 1240 of its 1322 lines of code are new or changed and 753 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/U/Prog/CF/sup_instance_verb.v, with its module paths and module names changed; 1234 of its 1368 lines of code are new or changed and 1188 lines of the source are left out. *)
From Stdlib Require Import String ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import Tac Arr Bytes FP Image.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Img0 AllocSlots.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import printf_facts_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import RecKindB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YM06 YL01.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Contract.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import RecAnsB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require RecAns.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition sc_piece (k : nat) (v : Z) : list byte := if Nat.eqb k 0 then dec v else SPACE :: dec v.

Lemma sc_dec_list_snoc : forall l v,
  dec_list (l ++ [v]) = dec_list l ++ (match l with [] => dec v | _ :: _ => SPACE :: dec v end).
Proof.
  intros [|i r] v; cbn [app dec_list].
  - cbn. rewrite !app_nil_r. reflexivity.
  - rewrite map_app, concat_app. cbn [map concat]. rewrite app_nil_r, app_assoc. reflexivity.
Qed.

Lemma sc_firstn_S : forall (ids : list Z) k v, nth_error ids k = Some v ->
  firstn (S k) ids = firstn k ids ++ [v].
Proof.
  induction ids as [|x ids IH]; intros k v E; [destruct k; discriminate|].
  destruct k as [|k]; cbn in E.
  - injection E as <-. reflexivity.
  - change (firstn (S (S k)) (x :: ids)) with (x :: firstn (S k) ids).
    rewrite (IH k v E). reflexivity.
Qed.

Lemma sc_firstn_nil : forall (ids : list Z) k, (k < length ids)%nat -> firstn k ids = [] -> k = 0%nat.
Proof.
  intros ids k Hk E. pose proof (length_firstn k ids) as L. rewrite E in L. cbn in L. lia.
Qed.

Lemma sc_dec_list_step : forall ids k v, nth_error ids k = Some v ->
  dec_list (firstn (S k) ids) = dec_list (firstn k ids) ++ sc_piece k v.
Proof.
  intros ids k v E. rewrite (sc_firstn_S ids k v E), sc_dec_list_snoc. f_equal.
  unfold sc_piece. assert (Hk : (k < length ids)%nat) by (apply nth_error_Some; congruence).
  destruct (firstn k ids) as [|y r] eqn:F.
  - rewrite (sc_firstn_nil ids k Hk F). reflexivity.
  - destruct k as [|k]; [discriminate|]. reflexivity.
Qed.

Lemma sc_piece_length : forall k v, -2^31 <= v < 2^31 -> (1 <= length (sc_piece k v) <= 12)%nat.
Proof.
  intros k v Hv. pose proof (dec_length v Hv) as D. unfold sc_piece.
  destruct (Nat.eqb k 0); cbn [length]; lia.
Qed.

Lemma sc_concat_len : forall r, Forall (fun v => -2^31 <= v < 2^31) r ->
  (length (concat (map (fun j => SPACE :: dec j) r)) <= 12 * length r)%nat.
Proof.
  induction r as [|v r IH]; intros HF; cbn [map concat length]; [lia|].
  inversion HF as [|? ? Hv Hr]; subst. rewrite length_app. cbn [length].
  pose proof (dec_length v Hv). specialize (IH Hr). lia.
Qed.

Lemma sc_dec_list_len : forall l, l <> [] -> Forall (fun v => -2^31 <= v < 2^31) l ->
  (length (dec_list l) + 1 <= 12 * length l)%nat.
Proof.
  intros [|i r] NE HF; [congruence|]. cbn [dec_list length].
  inversion HF as [|? ? Hi Hr]; subst. rewrite length_app.
  pose proof (dec_length i Hi). pose proof (sc_concat_len r Hr). lia.
Qed.

Lemma sc_forall_firstn : forall (P : Z -> Prop) l k, Forall P l -> Forall P (firstn k l).
Proof.
  intros P l. induction l as [|x l IH]; intros k HF; destruct k as [|k]; cbn; try constructor.
  - inversion HF; assumption.
  - inversion HF as [|? ? Hx Hl]; subst. exact (IH k Hl).
Qed.

Lemma sc_pref_len : forall ids k, Forall (fun v => -2^31 <= v < 2^31) ids ->
  (length (dec_list (firstn k ids)) <= 12 * k)%nat.
Proof.
  intros ids k HF. destruct (firstn k ids) as [|y r] eqn:F; [cbn; lia|].
  assert (NE : firstn k ids <> []) by (rewrite F; discriminate).
  pose proof (sc_dec_list_len (firstn k ids) NE (sc_forall_firstn _ ids k HF)) as H.
  rewrite F in H. pose proof (firstn_le_length k ids) as L. rewrite F in L. lia.
Qed.

Lemma sc_le_mallocs : forall ns b, Forall (fun n => 0 <= n) ns -> sb_le b (sb_mallocs b ns).
Proof.
  induction ns as [|n ns IH]; intros b HF; [apply sb_le_refl|].
  inversion HF as [|? ? Hn Hr]; subst. unfold sb_mallocs. cbn [fold_left].
  eapply sb_le_trans; [apply (sb_le_malloc b n Hn)|]. exact (IH (sb_malloc b n) Hr).
Qed.

Definition SC_FMT1 : list Z := [32; 37; 100].
Definition SC_PS1 : list pf_piece := [PLit 32; Pd].

Lemma sc_parse1 : pf_parse SC_FMT1 = Some SC_PS1.
Proof. reflexivity. Qed.

Lemma sc_text1 : forall v, pf_text SC_PS1 [AInt v] = Some (32 :: pf_dec v).
Proof. intros v. cbn. rewrite app_nil_r. reflexivity. Qed.

Lemma sc_fmt1_at : forall m, mem_inv rsegs m -> bytes_at rsegs m 0x10738 (pf_bytes (SC_FMT1 ++ [0])).
Proof.
  intros m MI. apply ro_bytes_at; [exact MI | lia | cbn; lia |].
  apply ro_bytes_b_sound. vm_compute. reflexivity.
Qed.

Lemma scu_pf_dec : forall v, -2^31 <= v < 2^31 -> pf_bytes (pf_dec v) = dec v.
Proof.
  intros c Hc. unfold pf_dec, dec. unfold pf_bytes.
  assert (P : 10 ^ Z.of_nat (S 9) = 10000000000) by reflexivity.
  destruct (Z.ltb_spec c 0) as [N|N].
  - cbn [map app]. f_equal. replace (Z.abs c) with (- c) by lia.
    exact (CF.RecAns.pf_digits_digits 9 11 (- c) [] ltac:(rewrite P; lia) ltac:(lia)).
  - cbn [app]. replace (Z.abs c) with c by lia.
    exact (CF.RecAns.pf_digits_digits 9 11 c [] ltac:(rewrite P; lia) ltac:(lia)).
Qed.

Lemma sc_piece_pf : forall k v, -2^31 <= v < 2^31 ->
  sc_piece k v = pf_bytes (if Nat.eqb k 0 then pf_dec v else 32 :: pf_dec v).
Proof.
  intros k v Hv. unfold sc_piece. rewrite <- (scu_pf_dec v Hv).
  destruct (Nat.eqb k 0); reflexivity.
Qed.

Lemma sc_off_bound : forall ids k v, Forall (fun v => -2^31 <= v < 2^31) ids -> nth_error ids k = Some v ->
  (length (dec_list (firstn k ids)) + length (sc_piece k v) + 1 <= 12 * length ids + 1)%nat.
Proof.
  intros ids k v HF E. pose proof (sc_pref_len ids (S k) HF) as P. rewrite (sc_dec_list_step ids k v E) in P.
  rewrite length_app in P. assert (Hk : (k < length ids)%nat) by (apply nth_error_Some; congruence). lia.
Qed.

Lemma scu_sx32 : forall z, -2^31 <= z < 2^31 -> sx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold sx32. f_equal. rewrite unsigned_lit_wrap.
  unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with 2147483648. change (bv_modulus 32) with 4294967296.
  change (2^64) with 18446744073709551616. change (2^31) with 2147483648 in Hz.
  Z.div_mod_to_equations. lia.
Qed.

Lemma scu_rd4 : forall m a v, bytes_at rsegs m a (le4 v) -> ov_read_bytes rsegs m (wa (a + 0)) 4 = Some (le4 v).
Proof.
  intros m a v H. rewrite (bytes_at_read rsegs m a _ 0 4 H) by (rewrite ?length_le4; lia).
  f_equal.
Qed.

Definition SCU_FMT0 : list Z := [37; 100].
Definition SCU_PS0 : list pf_piece := [Pd].

Lemma scu_text0 : forall v, pf_text SCU_PS0 [AInt v] = Some (pf_dec v).
Proof. intros v. cbn. rewrite app_nil_r. reflexivity. Qed.

Lemma scu_fmt0_at : forall m, mem_inv rsegs m -> bytes_at rsegs m 0x10828 (pf_bytes (SCU_FMT0 ++ [0])).
Proof.
  intros m MI. apply ro_bytes_at; [exact MI | lia | cbn; lia |].
  apply ro_bytes_b_sound. vm_compute. reflexivity.
Qed.

Lemma scu_lxor : forall x, 0 <= x < 2 ^ 64 -> Z.lxor x (2 ^ 64 - 1) = 2 ^ 64 - 1 - x.
Proof.
  intros x Hx.
  assert (E : Z.lxor x (Z.ones 64) = Z.land (Z.lnot x) (Z.ones 64)).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.lxor_spec, Z.land_spec, Z.lnot_spec by lia.
    destruct (Z.lt_ge_cases i 64) as [H|H].
    - rewrite Z.ones_spec_low by lia. destruct (Z.testbit x i); reflexivity.
    - rewrite Z.ones_spec_high by lia. rewrite <- (Z.mod_small x (2 ^ 64)) by lia.
      rewrite Z.mod_pow2_bits_high by lia. reflexivity. }
  replace (2 ^ 64 - 1) with (Z.ones 64) by reflexivity. rewrite E, Z.land_ones by lia.
  rewrite Z.lnot_eq_pred_opp. change (Z.ones 64) with (2 ^ 64 - 1).
  Z.div_mod_to_equations. lia.
Qed.

From Stdlib Require Import Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs Monad Specs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step ZBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YM05 YL0i YL01.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Contract FrameAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import RecInv RecInvU.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import RecSeq RecStep RecGlue RecAnsB RecTail RecStubU.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import xmalloc_c record_c arg_s_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YO10.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require hand_back.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require sprintf_c snprintf_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require RecAns.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require MemNorm.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import SRCF.

Lemma sc_eqb : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 ->
  bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = Z.eqb x y.
Proof. intros x y Hx Hy. unfold bv_eqb. rewrite !unsigned_lit by lia. reflexivity. Qed.

Definition sc_fmt (k : nat) : list Z := if Nat.eqb k 0 then SCU_FMT0 else SC_FMT1.
Definition sc_ps (k : nat) : list pf_piece := if Nat.eqb k 0 then SCU_PS0 else SC_PS1.
Definition sc_txt (k : nat) (v : Z) : list Z := if Nat.eqb k 0 then pf_dec v else 32 :: pf_dec v.
Definition sc_fa (k : nat) : Z := if Nat.eqb k 0 then 0x10828 else 0x10738.

Definition scu_after (sp gp tp : word) (F : bvmap 5 word)
    (lo lst pids o n v : Z) (k : nat) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s2 s5 s6 s11 pc : word) (Ft : bvmap 5 word)
                    (fc' : bv 32) (m' : word -> option byte),
    ms' = MS (mkR (Z_to_bv 64 0x16f34) sp gp tp t0 t1 t2 (Z_to_bv 64 pids) (Z_to_bv 64 n) a0 a1 a2 a3 a4 a5 a6 a7
                  s2 (Z_to_bv 64 lst) (Z_to_bv 64 0x10828) s5 s6 (Z_to_bv 64 (2 ^ 64 - 1 - lst)) (Z_to_bv 64 1)
                  (Z_to_bv 64 1) (Z_to_bv 64 0x10738) s11 t3 t4 t5 t6)
             Ft pc fc' None m' (seg_rom rsegs) /\
    s2 = Z_to_bv 64 (pids + 4 * Z.of_nat (S k)) /\ s11 = Z_to_bv 64 (pids + 4 * Z.of_nat (S k)) /\
    s5 = Z_to_bv 64 (Z.of_nat (S k)) /\
    s6 = Z_to_bv 64 (o + Z.of_nat (length (sc_piece k v))) /\
    pc = Z_to_bv 64 (if Z.of_nat (S k) =? n then 0x16f48 else 0x16f04) /\
    munch [(lo, bv_unsigned sp); (lst + o, lst + o + Z.of_nat (length (sc_piece k v)) + 1)] m m' /\
    wmono rsegs m m' /\ mem_inv rsegs m' /\ MemNorm.task_mem rsegs m' /\ frm0 fc' /\
    (forall r : reg, bv_unsigned r <> 10 -> reg_get Ft r = reg_get F r) /\
    stk rsegs m' lo (bv_unsigned sp) /\
    bytes_at rsegs m' (lst + o) (sc_piece k v ++ [Z_to_bv 8 0]).

Ltac scu_cond :=
  unfold bv_ltu, bv_eqb, bv_lts, bv_leu, v_sltiu, v_xor, v_and, v_sltu, c_ltu, c_eq;
  repeat match goal with |- context [bv_unsigned (Z_to_bv 64 ?x)] => rewrite (unsigned_lit x) by lia end;
  repeat match goal with |- context [?x <? ?y] => destruct (Z.ltb_spec x y); try lia end;
  first [ reflexivity | vm_compute; reflexivity | apply Z.ltb_ge; lia | apply Z.eqb_neq; lia ].

Ltac scu_nb :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) =>
      replace c with false; [cbv iota | symmetry; scu_cond]
  end.

Lemma scu_seqz : forall x, 1 <= x < 2 ^ 64 -> v_sltiu (Z_to_bv 64 x) 1 = Z_to_bv 64 0.
Proof.
  intros x Hx. unfold v_sltiu. rewrite unsigned_lit by lia. change (bv_wrap 64 1) with 1.
  destruct (Z.ltb_spec x 1); [lia | reflexivity].
Qed.

Lemma sc_ids_len : forall ids, length (concat (map le32 ids)) = (4 * length ids)%nat.
Proof.
  induction ids as [|x ids IH]; [reflexivity|]. cbn [map concat length]. rewrite length_app, IH.
  unfold le32. rewrite length_le4. lia.
Qed.

Lemma sc_ids_at : forall ids m pids k v, bytes_at rsegs m pids (concat (map le32 ids)) -> nth_error ids k = Some v ->
  bytes_at rsegs m (pids + 4 * Z.of_nat k) (le4 (Z_to_bv 64 v)).
Proof.
  induction ids as [|x ids IH]; intros m pids k v H E; [destruct k; discriminate|].
  cbn [map concat] in H. apply bytes_at_app in H as [H1 H2].
  assert (L4 : length (le32 x) = 4%nat) by (unfold le32; apply length_le4). rewrite L4 in H2.
  destruct k as [|k]; cbn [nth_error] in E.
  - injection E as <-. replace (pids + 4 * Z.of_nat 0) with pids by lia. exact H1.
  - replace (pids + 4 * Z.of_nat (S k)) with (pids + Z.of_nat 4 + 4 * Z.of_nat k) by lia. exact (IH m _ k v H2 E).
Qed.

Lemma scu_iter : sprintf_c.sprintf_contract ->
  forall ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo lst pids o n v : Z) (k : nat) (canary : word)
    (junk : list byte),
  -2^31 <= v < 2^31 -> Z.of_nat k < n <= 62 -> 0 < pids -> pids + 4 * n <= 2 ^ 63 ->
  0 <= lst -> 0 <= o -> 0 < lst + o -> lst + o + Z.of_nat (length (sc_piece k v)) + 1 <= lo ->
  bytes_at rsegs m (pids + 4 * Z.of_nat k) (le4 (Z_to_bv 64 v)) ->
  rw_cells rsegs m (lst + o) [CB (S (length (sc_piece k v))) junk] ->
  pf_img_free (lst + o) (Z.of_nat (length (sc_piece k v)) + 1) ->
  stk rsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - sprintf_c.SPRINTF_K -> snprintf_c.IMG_END <= lo ->
  bv_unsigned sp < 2^63 ->
  frm0 fc -> mem_inv rsegs m -> MemNorm.task_mem rsegs m ->
  bytes_at rsegs m snprintf_c.GOT_GUARD (le8 (Z_to_bv 64 snprintf_c.GUARD)) ->
  bytes_at rsegs m snprintf_c.GUARD (le8 canary) ->
  evt rsegs (scu_after sp gp tp F lo lst pids o n v k m)
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 pids) (Z_to_bv 64 n) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 (pids + 4 * Z.of_nat k)) (Z_to_bv 64 lst) (Z_to_bv 64 0x10828) (Z_to_bv 64 (Z.of_nat k))
             (Z_to_bv 64 o) (Z_to_bv 64 (2 ^ 64 - 1 - lst)) (Z_to_bv 64 1) (Z_to_bv 64 1) (Z_to_bv 64 0x10738)
             (Z_to_bv 64 (pids + 4 * Z.of_nat k)) t3 t4 t5 t6) F (Z_to_bv 64 0x16f04) fc None m (seg_rom rsegs)).
Proof.
  intros SPR ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m lo lst pids o n v k
    canary junk HV HK HP0 HP1 HL0 HO0 HD0 HDL HR BUF IMGF ST LO IE S63 FRM MI TM GG GW.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  unfold sprintf_c.SPRINTF_K, snprintf_c.IMG_END in *.
  pose proof (dec_length v HV) as DL.
  pose proof (sc_piece_pf k v HV) as PP.
  assert (TL : length (sc_piece k v) = length (sc_txt k v)).
  { rewrite PP. unfold pf_bytes, sc_txt. rewrite length_map. reflexivity. }
  pose proof (sc_piece_length k v HV) as PL.
  pose proof (scu_rd4 m (pids + 4 * Z.of_nat k) _ HR) as RD.
  step. scu_nb.
  step. step. rewrite sc_eqb by lia.
  assert (TAIL : forall a1',
    a1' = Z_to_bv 64 (sc_fa k) ->
    evt rsegs (scu_after sp gp tp F lo lst pids o n v k m)
      (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 pids) (Z_to_bv 64 n) a0 a1' a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 (pids + 4 * Z.of_nat k)) (Z_to_bv 64 lst) (Z_to_bv 64 0x10828) (Z_to_bv 64 (Z.of_nat k))
             (Z_to_bv 64 o) (Z_to_bv 64 (2 ^ 64 - 1 - lst)) (Z_to_bv 64 1) (Z_to_bv 64 1) (Z_to_bv 64 0x10738)
             (Z_to_bv 64 (pids + 4 * Z.of_nat k)) t3 t4 t5 t6) F (Z_to_bv 64 0x16f14) fc None m (seg_rom rsegs))).
  { intros a1' ->.
    assert (FA : 0x10738 <= sc_fa k <= 0x10828) by (unfold sc_fa; destruct (Nat.eqb k 0); lia).
    step. scu_nb. step. step. step. rewrite scu_seqz by lia. if_false. step. if_false.
    step. rewrite scu_sx32 by lia. step. step.
    eapply evt_cut.
    { eapply (SPR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo canary (sc_fmt k) (sc_ps k)
                [AInt v] (sc_txt k v) junk).
      - rewrite unsigned_lit by lia. unfold sc_fa, sc_fmt. destruct (Nat.eqb k 0); [apply scu_fmt0_at | apply sc_fmt1_at];
          exact MI.
      - rewrite unsigned_lit by lia. unfold snprintf_c.RO_LO. lia.
      - rewrite unsigned_lit by lia. unfold snprintf_c.RO_END, sc_fa, sc_fmt, SCU_FMT0, SC_FMT1.
        destruct (Nat.eqb k 0); cbn [length]; lia.
      - unfold sc_fmt, sc_ps. destruct (Nat.eqb k 0); reflexivity.
      - cbn [pf_args_ok pf_arg_ok]. split; [|exact I]. split; [exact HV | apply CF.RecAns.lit_mod32].
      - unfold sc_ps, sc_txt. destruct (Nat.eqb k 0); [exact (scu_text0 v) | exact (sc_text1 v)].
      - rewrite unsigned_lit by lia.
        replace (Z.to_nat (Z.of_nat (length (sc_txt k v)) + 1)) with (S (length (sc_piece k v))) by lia. exact BUF.
      - lia.
      - rewrite unsigned_lit by lia. lia.
      - rewrite unsigned_lit by lia. left. lia.
      - rewrite unsigned_lit by lia. rewrite <- TL. exact IMGF.
      - exact ST.
      - unfold sprintf_c.SPRINTF_K. lia.
      - unfold snprintf_c.IMG_END. lia.
      - lia.
      - exact FRM.
      - exact MI.
      - exact TM.
      - exact GG.
      - exact GW. }
    intros ms' PO. unfold printf_post in PO.
    destruct PO as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & Ft & fc' & m2
      & -> & MU2 & WM2 & MI2 & TM2 & FRM2 & FK & ST2 & BT).
    rewrite unsigned_lit in MU2, BT by lia.
    replace (ret_pc (Z_to_bv 64 0x16f34)) with (Z_to_bv 64 0x16f34) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
    step. step. step. step. step.
    apply evt_done. unfold scu_after.
    do 20 eexists. exists Ft, fc', m2.
    split; [reflexivity|].
    split; [apply bv_eq; rewrite !unsigned_lit by lia; lia|].
    split; [apply bv_eq; rewrite !unsigned_lit by lia; lia|].
    split; [apply bv_eq; rewrite !unsigned_lit by lia; lia|].
    split; [apply bv_eq; rewrite !unsigned_lit by lia; lia|].
    split.
    { rewrite sc_eqb by lia.
      repeat match goal with |- context [Z.eqb ?x ?y] => destruct (Z.eqb_spec x y) end; cbn [negb];
        first [reflexivity | exfalso; lia]. }
    rewrite TL. split; [exact MU2|]. split; [exact WM2|]. split; [exact MI2|]. split; [exact TM2|].
    split; [exact FRM2|]. split; [exact FK|]. split; [exact ST2|].
    rewrite PP. unfold pf_bytes in BT |- *. rewrite map_app in BT. exact BT. }
  destruct (Z.eqb_spec (Z.of_nat k) 0) as [K0|K0]; cbv iota.
  - apply TAIL. unfold sc_fa. replace k with 0%nat by lia. reflexivity.
  - step. apply TAIL. unfold sc_fa. destruct (Nat.eqb_spec k 0); [lia | reflexivity].
Qed.

Lemma scu_loop : sprintf_c.sprintf_contract ->
  forall (Q : machine_state -> Prop) (ids : list Z) sp gp tp (F0 : bvmap 5 word)
    (m0 : word -> option byte) (lo lst pids : Z) (canary : word) (d : nat)
    ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : word -> option byte) (k : nat) (w2 : word),
  d = (length ids - k)%nat -> (k < length ids)%nat -> (length ids <= 62)%nat ->
  Forall (fun v => -2^31 <= v < 2^31) ids ->
  0 < pids -> pids + 4 * Z.of_nat (length ids) <= 2 ^ 63 ->
  (pids + 4 * Z.of_nat (length ids) <= lo \/ bv_unsigned sp <= pids) ->
  (pids + 4 * Z.of_nat (length ids) <= lst \/ lst + 12 * Z.of_nat (length ids) + 1 <= pids) ->
  0 < lst -> lst + 12 * Z.of_nat (length ids) + 1 <= lo ->
  pf_img_free lst (12 * Z.of_nat (length ids) + 1) ->
  (forall m', wmono rsegs m0 m' -> forall i, 0 <= i < 12 * Z.of_nat (length ids) + 1 -> present m' (lst + i)) ->
  (snprintf_c.GOT_GUARD + 8 <= lst \/ lst + 12 * Z.of_nat (length ids) + 1 <= snprintf_c.GOT_GUARD) ->
  (snprintf_c.GUARD + 8 <= lst \/ lst + 12 * Z.of_nat (length ids) + 1 <= snprintf_c.GUARD) ->
  lo <= bv_unsigned sp - sprintf_c.SPRINTF_K -> snprintf_c.IMG_END <= lo -> bv_unsigned sp < 2^63 ->
  (forall r : reg, bv_unsigned r <> 10 -> reg_get F r = reg_get F0 r) ->
  munch [(lo, bv_unsigned sp); (lst, lst + 12 * Z.of_nat (length ids) + 1)] m0 m -> wmono rsegs m0 m ->
  stk rsegs m lo (bv_unsigned sp) -> frm0 fc -> mem_inv rsegs m -> MemNorm.task_mem rsegs m ->
  bytes_at rsegs m snprintf_c.GOT_GUARD (le8 (Z_to_bv 64 snprintf_c.GUARD)) ->
  bytes_at rsegs m snprintf_c.GUARD (le8 canary) ->
  bytes_at rsegs m pids (concat (map le32 ids)) ->
  bytes_at rsegs m lst (dec_list (firstn k ids) ++ [Z_to_bv 8 0]) ->
  w2 = Z_to_bv 64 (pids + 4 * Z.of_nat k) ->
  (forall t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (Ft : bvmap 5 word) (fc' : bv 32) (m' : word -> option byte),
     munch [(lo, bv_unsigned sp); (lst, lst + 12 * Z.of_nat (length ids) + 1)] m0 m' -> wmono rsegs m0 m' ->
     stk rsegs m' lo (bv_unsigned sp) -> frm0 fc' -> mem_inv rsegs m' -> MemNorm.task_mem rsegs m' ->
     (forall r : reg, bv_unsigned r <> 10 -> reg_get Ft r = reg_get F0 r) ->
     bytes_at rsegs m' pids (concat (map le32 ids)) ->
     bytes_at rsegs m' lst (dec_list ids ++ [Z_to_bv 8 0]) ->
     evt rsegs Q (MS (mkR (Z_to_bv 64 0x16f34) sp gp tp t0 t1 t2 (Z_to_bv 64 pids) (Z_to_bv 64 (Z.of_nat (length ids)))
                        a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (pids + 4 * Z.of_nat (length ids))) (Z_to_bv 64 lst)
                        (Z_to_bv 64 0x10828) (Z_to_bv 64 (Z.of_nat (length ids)))
                        (Z_to_bv 64 (Z.of_nat (length (dec_list ids)))) (Z_to_bv 64 (2 ^ 64 - 1 - lst))
                        (Z_to_bv 64 1) (Z_to_bv 64 1) (Z_to_bv 64 0x10738)
                        (Z_to_bv 64 (pids + 4 * Z.of_nat (length ids))) t3 t4 t5 t6)
                     Ft (Z_to_bv 64 0x16f48) fc' None m' (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 pids) (Z_to_bv 64 (Z.of_nat (length ids))) a0 a1 a2 a3 a4 a5 a6 a7
                     w2 (Z_to_bv 64 lst) (Z_to_bv 64 0x10828) (Z_to_bv 64 (Z.of_nat k))
                     (Z_to_bv 64 (Z.of_nat (length (dec_list (firstn k ids))))) (Z_to_bv 64 (2 ^ 64 - 1 - lst))
                     (Z_to_bv 64 1) (Z_to_bv 64 1) (Z_to_bv 64 0x10738) w2 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x16f04) fc None m (seg_rom rsegs)).
Proof.
  intros SPR Q ids sp gp tp F0 m0 lo lst pids canary d.
  induction d as [|d IH];
    intros ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m k w2 Hd Hk HN HF HP0 HP1 HPS HPL HL0 HLlo IMG PRES
      GD1 GD2 LO IE S63 FF MU0 WM0 ST FRM MI TM GG GW HIDS BL W2 K; [lia|].
  subst w2.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  unfold sprintf_c.SPRINTF_K, snprintf_c.IMG_END, snprintf_c.GOT_GUARD, snprintf_c.GUARD in *.
  destruct (nth_error ids k) as [v|] eqn:E; [|apply nth_error_None in E; lia].
  pose proof (proj1 (Forall_forall _ _) HF v (nth_error_In ids k E)) as HV. cbv beta in HV.
  pose proof (sc_off_bound ids k v HF E) as OB.
  pose proof (sc_piece_length k v HV) as PL.
  pose proof (sc_ids_len ids) as IL.
  remember (Z.of_nat (length (dec_list (firstn k ids)))) as o eqn:Ho.
  destruct (present_rw_cells rsegs m (lst + o) (S (length (sc_piece k v)))) as [junk BUF]; [lia | lia | |].
  { intros i Hi. replace (lst + o + i) with (lst + (o + i)) by ring. apply (PRES m WM0). lia. }
  eapply evt_cut.
  { eapply (scu_iter SPR ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m lo lst pids o
              (Z.of_nat (length ids)) v k canary junk HV ltac:(lia) HP0 HP1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
              (sc_ids_at ids m pids k v HIDS E) BUF).
    - intros i Hi s Hs. replace (lst + o + i) with (lst + (o + i)) by ring. apply (IMG (o + i)); [lia | exact Hs].
    - exact ST.
    - unfold sprintf_c.SPRINTF_K. lia.
    - unfold snprintf_c.IMG_END. lia.
    - exact S63.
    - exact FRM.
    - exact MI.
    - exact TM.
    - exact GG.
    - exact GW. }
  intros ms' (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & s2' & s5' & s6'
    & s11' & pc' & Ft & fc' & m' & -> & -> & -> & -> & -> & -> & MU & WM & MI' & TM' & FRM' & FK & ST' & BT).
  assert (MU' : munch [(lo, bv_unsigned sp); (lst, lst + 12 * Z.of_nat (length ids) + 1)] m0 m').
  { eapply munch_trans; [exact MU0|]. eapply munch_weaken; [|exact MU].
    unfold sub_fp. cbn [outside]. intros x (H1 & H2 & _). split; [lia | split; [lia | exact I]]. }
  assert (WM' : wmono rsegs m0 m') by (eapply wmono_trans; eassumption).
  assert (FK' : forall r : reg, bv_unsigned r <> 10 -> reg_get Ft r = reg_get F0 r).
  { intros r Hr. rewrite (FK r Hr). exact (FF r Hr). }
  assert (HIDS' : bytes_at rsegs m' pids (concat (map le32 ids))).
  { apply (bytes_at_transport rsegs _ m m' _ _ HIDS MU). cbn [disjoint_from]. rewrite IL.
    repeat (split; [lia|]); try exact I. }
  assert (GG' : bytes_at rsegs m' 0x22d40 (le8 (Z_to_bv 64 0x54730))).
  { apply (bytes_at_transport rsegs _ m m' _ _ GG MU). cbn [disjoint_from]. rewrite length_le8.
    repeat (split; [lia|]); try exact I. }
  assert (GW' : bytes_at rsegs m' 0x54730 (le8 canary)).
  { apply (bytes_at_transport rsegs _ m m' _ _ GW MU). cbn [disjoint_from]. rewrite length_le8.
    repeat (split; [lia|]); try exact I. }
  apply bytes_at_app in BL as [BP _].
  assert (BP' : bytes_at rsegs m' lst (dec_list (firstn k ids))).
  { apply (bytes_at_transport rsegs _ m m' _ _ BP MU). cbn [disjoint_from].
    repeat (split; [lia|]); try exact I. }
  assert (BL' : bytes_at rsegs m' lst (dec_list (firstn (S k) ids) ++ [Z_to_bv 8 0])).
  { rewrite (sc_dec_list_step ids k v E), <- app_assoc. apply bytes_at_app. split; [exact BP'|]. rewrite <- Ho.
    exact BT. }
  assert (LS : o + Z.of_nat (length (sc_piece k v)) = Z.of_nat (length (dec_list (firstn (S k) ids)))).
  { rewrite Ho, (sc_dec_list_step ids k v E), length_app. lia. }
  rewrite LS.
  destruct (Nat.eq_dec (S k) (length ids)) as [Ek|Ek].
  - replace (Z_to_bv 64 (if Z.of_nat (S k) =? Z.of_nat (length ids) then 0x16f48 else 0x16f04)) with (Z_to_bv 64 0x16f48)
      by (replace (Z.of_nat (S k) =? Z.of_nat (length ids)) with true by (symmetry; apply Z.eqb_eq; lia); reflexivity).
    rewrite Ek, firstn_all. rewrite Ek, firstn_all in BL'.
    exact (K t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' Ft fc' m' MU' WM' ST' FRM' MI' TM' FK' HIDS' BL').
  - replace (Z_to_bv 64 (if Z.of_nat (S k) =? Z.of_nat (length ids) then 0x16f48 else 0x16f04)) with (Z_to_bv 64 0x16f04)
      by (replace (Z.of_nat (S k) =? Z.of_nat (length ids)) with false by (symmetry; apply Z.eqb_neq; lia); reflexivity).
    apply (IH _ t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' Ft fc' m' (S k) _ ltac:(lia) ltac:(lia) HN HF
             HP0 HP1 HPS HPL HL0 HLlo IMG PRES GD1 GD2 LO IE S63 FK' MU' WM' ST' FRM' MI' TM' GG' GW' HIDS' BL' eq_refl K).
Qed.

Lemma scu_lts : forall x y, -2^63 <= x < 2^63 -> -2^63 <= y < 2^63 ->
  bv_lts (Z_to_bv 64 x) (Z_to_bv 64 y) = Z.ltb x y.
Proof.
  intros x y Hx Hy. unfold bv_lts. rewrite !Z_to_bv_signed.
  unfold bv_swrap, bv_wrap. change (bv_half_modulus 64) with 9223372036854775808.
  change (bv_modulus 64) with 18446744073709551616.
  change (2^63) with 9223372036854775808 in Hx, Hy.
  rewrite !Z.mod_small by lia.
  all: f_equal; lia.
Qed.

Lemma scu_andi3 : forall p, 0 <= p -> p mod 4 = 0 -> Z.land p 3 = 0.
Proof.
  intros p Hp H. change 3 with (Z.ones 2). rewrite Z.land_ones by lia. exact H.
Qed.

Lemma scu_pre : sprintf_c.sprintf_contract ->
  forall (Q : machine_state -> Prop) (ids : list Z) ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s5 s6 s7 s8 s9 s10 s11
    t3 t4 t5 t6 (F : bvmap 5 word) fc (m0 m : word -> option byte) (lo lst pids : Z) (canary : word),
  (1 <= length ids <= 62)%nat -> Forall (fun v => -2^31 <= v < 2^31) ids ->
  0 < pids -> pids mod 4 = 0 -> pids + 4 * Z.of_nat (length ids) <= 2 ^ 63 ->
  (pids + 4 * Z.of_nat (length ids) <= lo \/ bv_unsigned sp <= pids) ->
  (pids + 4 * Z.of_nat (length ids) <= lst \/ lst + 12 * Z.of_nat (length ids) + 1 <= pids) ->
  0 < lst -> lst + 12 * Z.of_nat (length ids) + 1 <= lo ->
  pf_img_free lst (12 * Z.of_nat (length ids) + 1) ->
  (forall m', wmono rsegs m0 m' -> forall i, 0 <= i < 12 * Z.of_nat (length ids) + 1 -> present m' (lst + i)) ->
  (snprintf_c.GOT_GUARD + 8 <= lst \/ lst + 12 * Z.of_nat (length ids) + 1 <= snprintf_c.GOT_GUARD) ->
  (snprintf_c.GUARD + 8 <= lst \/ lst + 12 * Z.of_nat (length ids) + 1 <= snprintf_c.GUARD) ->
  lo <= bv_unsigned sp - sprintf_c.SPRINTF_K -> snprintf_c.IMG_END <= lo -> bv_unsigned sp < 2^63 ->
  bv_unsigned sp <= TASK_SIZE ->
  munch [(lo, bv_unsigned sp); (lst, lst + 12 * Z.of_nat (length ids) + 1)] m0 m -> wmono rsegs m0 m ->
  wr_at rsegs m lst 1 ->
  stk rsegs m lo (bv_unsigned sp) -> frm0 fc -> mem_inv rsegs m -> MemNorm.task_mem rsegs m ->
  bytes_at rsegs m snprintf_c.GOT_GUARD (le8 (Z_to_bv 64 snprintf_c.GUARD)) ->
  bytes_at rsegs m snprintf_c.GUARD (le8 canary) ->
  bytes_at rsegs m pids (concat (map le32 ids)) ->
  (forall t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (Ft : bvmap 5 word) (fc' : bv 32) (m' : word -> option byte),
     munch [(lo, bv_unsigned sp); (lst, lst + 12 * Z.of_nat (length ids) + 1)] m0 m' -> wmono rsegs m0 m' ->
     stk rsegs m' lo (bv_unsigned sp) -> frm0 fc' -> mem_inv rsegs m' -> MemNorm.task_mem rsegs m' ->
     (forall r : reg, bv_unsigned r <> 10 -> reg_get Ft r = reg_get F r) ->
     bytes_at rsegs m' pids (concat (map le32 ids)) ->
     bytes_at rsegs m' lst (dec_list ids ++ [Z_to_bv 8 0]) ->
     evt rsegs Q (MS (mkR (Z_to_bv 64 0x16f34) sp gp tp t0 t1 t2 (Z_to_bv 64 pids) (Z_to_bv 64 (Z.of_nat (length ids)))
                        a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (pids + 4 * Z.of_nat (length ids))) (Z_to_bv 64 lst)
                        (Z_to_bv 64 0x10828) (Z_to_bv 64 (Z.of_nat (length ids)))
                        (Z_to_bv 64 (Z.of_nat (length (dec_list ids)))) (Z_to_bv 64 (2 ^ 64 - 1 - lst))
                        (Z_to_bv 64 1) (Z_to_bv 64 1) (Z_to_bv 64 0x10738)
                        (Z_to_bv 64 (pids + 4 * Z.of_nat (length ids))) t3 t4 t5 t6)
                     Ft (Z_to_bv 64 0x16f48) fc' None m' (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 pids) (Z_to_bv 64 (Z.of_nat (length ids))) a0 a1 a2 a3 a4 a5 a6 a7
                     s2 (Z_to_bv 64 lst) (Z_to_bv 64 0x10828) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x16ed0) fc None m (seg_rom rsegs)).
Proof.
  intros SPR Q ids ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m0 m
    lo lst pids canary HN HF HP0 HP4 HP1 HPS HPL HL0 HLlo IMG PRES GD1 GD2 LO IE S63 HTS MU0 WM0 WR ST FRM MI TM GG GW
    HIDS K.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  unfold sprintf_c.SPRINTF_K, snprintf_c.IMG_END, snprintf_c.GOT_GUARD, snprintf_c.GUARD in *.
  pose proof (sc_ids_len ids) as IL.
  assert (SO : store_ok rsegs m (wa (lst + 0)) 1 = true) by (apply (wr_at_store_ok rsegs m lst 1 0 1 WR); lia).
  step.
  match goal with |- context [write_to_mem m ?aa ?bs] =>
    replace (write_to_mem m aa bs) with (write_to_mem m (wa lst) [Z_to_bv 8 0])
      by (f_equal; try (unfold wa; f_equal; lia); try lia; try reflexivity; try (vm_compute; reflexivity)) end.
  step. rewrite ?scu_lts by lia.
  match goal with |- context [Z.ltb ?x ?y] => destruct (Z.ltb_spec x y) end; cbn [negb]; try (exfalso; lia).
  do 11 step.
  assert (E7 : Z_to_bv 64 (Z.lxor (bv_unsigned (Z_to_bv 64 lst)) 18446744073709551615) = Z_to_bv 64 (2 ^ 64 - 1 - lst)).
  { rewrite unsigned_lit by lia. change 18446744073709551615 with (2 ^ 64 - 1). rewrite scu_lxor by lia. reflexivity. }
  assert (E8 : PropExec.v_sltu (Z_to_bv 64 0) (Z_to_bv 64 pids) = Z_to_bv 64 1).
  { unfold PropExec.v_sltu, PropExec.c_ltu, bv_ltu. rewrite !unsigned_lit by lia.
    destruct (Z.ltb_spec 0 pids); [reflexivity | lia]. }
  assert (E3 : PropExec.v_sltiu (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 pids)) 3)) 1 = Z_to_bv 64 1).
  { rewrite unsigned_lit by lia. rewrite (scu_andi3 pids) by lia. unfold PropExec.v_sltiu.
    rewrite unsigned_lit by lia. reflexivity. }
  assert (E9 : Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 1)) (bv_unsigned (Z_to_bv 64 1))) = Z_to_bv 64 1)
    by reflexivity.
  rewrite E7, E8, E3, E9.
  assert (WL : 0 <= lst /\ lst + Z.of_nat (length [Z_to_bv 8 0]) <= 2 ^ 64) by (cbn [length]; lia).
  eapply (scu_loop SPR Q ids sp gp tp F m0 lo lst pids canary (length ids)) with (k := 0%nat).
  all: try assumption; try lia; try (intros; reflexivity).
  - apply munch_write; [exact MU0 | lia | cbn [length]; lia | cbn [inside]; right; left; cbn [length]; lia].
  - apply wmono_write. exact WM0.
  - apply stk_write; [exact ST | lia | cbn [length]; lia].
  - apply mem_inv_store; [exact MI|]. rewrite Z.add_0_r in SO. exact SO.
  - apply (CF.RecAns.task_mem_munch1 m _ lst (lst + 1) TM); [|lia].
    apply munch_write; [apply munch_refl | lia | cbn [length]; lia | cbn [inside]; left; cbn [length]; lia].
  - apply bytes_at_write_other; [exact GG | lia | cbn [length]; lia |].
    rewrite length_le8. cbn [length]. unfold snprintf_c.GOT_GUARD, snprintf_c.GUARD. lia.
  - apply bytes_at_write_other; [exact GW | lia | cbn [length]; lia |].
    rewrite length_le8. cbn [length]. unfold snprintf_c.GOT_GUARD, snprintf_c.GUARD. lia.
  - apply bytes_at_write_other; [exact HIDS | lia | cbn [length]; lia | rewrite IL; cbn [length]; lia].
  - change (dec_list (firstn 0 ids) ++ [Z_to_bv 8 0]) with [Z_to_bv 8 0].
    apply bytes_at_write_same; [lia | cbn [length]; lia].
  - f_equal. lia.
Qed.

Section X.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis SEGS : ms_segs B = rsegs.
Hypothesis ERRNO_LOW : errno_addr B + 4 <= alloc_ceiling.
Hypothesis GFACT : forall a, in_globals frame_G a -> in_img B a /\ ~ static_owned B a /\
  ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\ ~ (errno_addr B <= a < errno_addr B + 4).
Hypothesis GOWN : forall L A mem md a, aa_MR API L A mem md -> in_globals frame_G a -> ~ owned B L A a.
Hypothesis AX : AllocExtra B (aa_MR API).

Definition sinvx (K S : Z) (L : layout) (A : astate) (mem : word -> option byte) (md : Model) (O : list (Z * Z))
    (Lc : layout) (Ac : astate) (mc : word -> option byte) (mdc : Model) (Rc : rstate) (Oc : list (Z * Z))
    (bc : sbound) (lb : Z * Z) : Prop :=
  rjr B (aa_MR API) K S rec_area (fun pn => In pn O) L A mem md Lc Ac mc mdc /\
  g_rec_rep rsegs Lc Ac mc Rc Oc /\ owns_new L A O Oc /\
  (forall pn, In pn (blocks Lc Ac) -> (In pn (blocks L A) /\ ~ In pn O) \/ In pn Oc \/ pn = lb) /\
  (forall pn, In pn (blocks L A) -> ~ In pn (blocks Lc Ac) -> In pn O) /\
  ro_agree rsegs mc /\ f18_words rsegs mc /\ res_ok_slots Ac (sb_shift bc A Ac) /\
  In lb (blocks Lc Ac) /\ (In lb (blocks L A) -> In lb O) /\ ~ In lb Oc.

Lemma sinvx_arg : forall K S L A mem md O Lc Ac mc mdc Rp fn As Oc bc lb Kc regs_c Ec L' A' regs' m' md' x p k,
  sinvx K S L A mem md O Lc Ac mc mdc (rec_record Rp fn As) Oc bc lb ->
  (length As < 6)%nat ->
  S - K <= spZ regs_c - Kc -> spZ regs_c <= S ->
  call_post_k B (aa_MR API) Kc Lc Ac regs_c mc mdc Ec L' A' regs' m' md' ->
  (forall a, Ec a ->
     rec_entry G_REC REC_SC Rp + CALL_OFF_NARGS <= a < rec_entry G_REC REC_SC Rp + CALL_OFF_NARGS + 4 \/
     rec_entry G_REC REC_SC Rp + CALL_OFF_ARGS + 8 * Z.of_nat (length As) <= a <
       rec_entry G_REC REC_SC Rp + CALL_OFF_ARGS + 8 * Z.of_nat (length As) + 8 \/
     p <= a < p + k) ->
  p <> 0 -> fresh_block B p k ->
  (exists b1 b2, blocks L' A' = b1 ++ (p, k) :: b2 /\ blocks Lc Ac = b1 ++ b2) ->
  (forall q n, In (q, n) (user_blocks Ac) -> In (q, n) (user_blocks A')) ->
  blocks_kept B Lc Ac mc m' (fun _ => False) ->
  (length (st_regions Ac) <= length (st_regions A'))%nat ->
  bytes_at rsegs m' (rec_entry G_REC REC_SC Rp + CALL_OFF_NARGS) (le4 (Z_to_bv 64 (Z.of_nat (length As) + 1))) ->
  bytes_at rsegs m' (rec_entry G_REC REC_SC Rp + CALL_OFF_ARGS + 8 * Z.of_nat (length As)) (le8 (Z_to_bv 64 p)) ->
  bytes_at rsegs m' p (x ++ [Z_to_bv 8 0]) ->
  no0 x -> Z.of_nat (length x) <= LMAX -> Z.of_nat (length x) + 1 <= k <= LMAX + 2 ->
  st_init_done A' = true ->
  res_ok_slots A' (sb_malloc (sb_shift bc A Ac) k) ->
  ro_agree rsegs m' -> f18_words rsegs m' ->
  sinvx K S L A mem md O L' A' m' md' (rec_record Rp fn (As ++ [x])) (Oc ++ [(p, k)]) bc lb.
Proof using SEGS AX GOWN GFACT ERRNO_LOW.
  intros K S L A mem md O Lc Ac mc mdc Rp fn As Oc bc lb Kc regs_c Ec L' A' regs' m' md' x p k
    SI H6 HLO HHI POST HEc Hp0 FB (b1 & b2 & EB' & EB) UB BK RGN BN BS BX Hno Hlx Hsz INI RS' RA' F18'.
  pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_val as AC.
  pose proof SI as (RJ & GR & ON & B1 & B2 & RA & F18 & RS & LIN & LNO & LOC).
  destruct (rjr_bounds B _ K S rec_area _ L A mem md Lc Ac mc mdc RJ) as (HK1 & HK2 & HK3).
  pose proof RJ as (HM & _).
  pose proof POST as (PM & PW & PB & PL & PA & PR & PV & PF & PK & PS).
  unfold blocks_kept in BK. rewrite SEGS in BK, PF.
  pose proof FB as (FB1 & FB2 & FB3).
  assert (ER : REC_SC <= rec_entry G_REC REC_SC Rp /\ rec_entry G_REC REC_SC Rp + CALL_SIZE <= G_REC + REC_SIZE).
  { unfold rec_entry. destruct (Nat.ltb (length (r_calls Rp)) 16) eqn:E.
    - apply Nat.ltb_lt in E. unfold REC_SC, G_REC, OFF_CALLS, CALL_SIZE, REC_SIZE. lia.
    - unfold REC_SC, G_REC, CALL_SIZE, REC_SIZE. lia. }
  set (e := rec_entry G_REC REC_SC Rp) in *.
  assert (Hk : 0 < k) by lia.
  assert (PIN : In (p, k) (blocks L' A')) by (rewrite EB'; apply in_elt).
  assert (PERM : Permutation (blocks L' A') ((b1 ++ b2) ++ [(p, k)])).
  { rewrite EB'. eapply Permutation_trans; [apply Permutation_sym, Permutation_middle | apply Permutation_cons_append]. }
  assert (NOTC : ~ In (p, k) (blocks Lc Ac)).
  { rewrite EB. intros H. exact (perm_not_both _ _ _ (p, k) PERM (mr_blocks_disjoint B _ LAWS L' A' m' md' PM)
                                   Hk H (or_introl eq_refl)). }
  assert (CUR : forall pn, In pn (blocks Lc Ac) -> In pn (blocks L' A')).
  { intros pn Hpn. rewrite EB'. rewrite EB in Hpn. exact (in_mid_inv b1 b2 (p, k) pn Hpn). }
  assert (APT : forall lo n, 0 < n -> (forall a, lo <= a < lo + n -> in_img B a) -> iv_apart p k lo n).
  { intros lo n Hn HI. unfold iv_apart. destruct (Z_le_gt_dec (p + k) lo) as [H|H]; [left; exact H|].
    destruct (Z_le_gt_dec (lo + n) p) as [H'|H']; [right; exact H'|]. exfalso.
    apply (FB3 (Z.max p lo - p)); [lia|]. replace (p + (Z.max p lo - p)) with (Z.max p lo) by lia. apply HI. lia. }
  assert (RIMG' : forall a, REC_SC <= a < G_REC + REC_SIZE -> GLOB_LO <= a < GLOB_LO + Z.of_nat GLOB_N)
    by (intros a Ha; unfold REC_SC, G_REC, REC_SIZE, GLOB_LO, GLOB_N in *; lia).
  assert (RJ' : rjr B (aa_MR API) K S rec_area (fun pn => In pn O) L A mem md L' A' m' md').
  { apply (rjr_post B _ SEGS LAWS AX ERRNO_LOW K S rec_area _ L A mem md Lc Ac mc mdc Kc regs_c Ec (fun _ => False)
             L' A' regs' m' md' RJ (call_post_k_rec B _ _ _ _ _ _ _ _ _ _ _ _ _ POST) HLO HHI).
    - intros a Ha Hf. destruct (HEc a Ha) as [H|[H|H]].
      + unfold rec_area, G_REC, REC_SC, REC_SIZE, SC_SIZE, CALL_SIZE, CALL_OFF_NARGS in *. split; lia.
      + unfold rec_area, G_REC, REC_SC, REC_SIZE, SC_SIZE, CALL_SIZE, CALL_OFF_ARGS in *. split; lia.
      + exfalso. destruct Hf as [Hf|(Hi & _)]; [lia|].
        apply (FB3 (a - p)); [lia|]. replace (p + (a - p)) with a by ring. exact Hi.
    - intros p0 n0 _ _ _ [].
    - intros p0 n0 _ Hc Hn. exfalso. exact (Hn (UB p0 n0 Hc)).
    - exact RGN.
    - intros Hf. rewrite INI in Hf. discriminate. }
  assert (NQ : ~ In p (map fst Oc)).
  { intros Hq. apply in_map_iff in Hq as ([q k'] & Eq & Hq). cbn in Eq. subst q.
    pose proof (rec_rep_O_in _ _ _ _ _ _ _ _ _ GR Hq) as Hb.
    pose proof (rec_rep_pos _ _ _ _ _ _ _ _ _ GR Hq) as Hk'. cbn in Hk'.
    pose proof (blocks_same_addr B _ LAWS L' A' m' md' p k k' PM PIN (CUR _ Hb) Hk Hk') as <-.
    exact (NOTC Hb). }
  assert (GR' : g_rec_rep rsegs L' A' m' (rec_record Rp fn (As ++ [x])) (Oc ++ [(p, k)])).
  { unfold g_rec_rep in *.
    apply (rec_rep_arg rsegs G_REC REC_SC Lc Ac mc L' A' m' Rp fn As Oc x p k GR H6 BN BS).
    - intros a Ha N1 N2.
      assert (Hg : GLOB_LO <= a < GLOB_LO + Z.of_nat GLOB_N)
        by (apply RIMG'; unfold G_REC, REC_SC, REC_SIZE, SC_SIZE in *; lia).
      destruct (GFACT a (glob_in a Hg)) as (Gi & _ & _ & Ge).
      assert (NS : ~ scratch_k B Kc regs_c a).
      { unfold scratch_k. intros [H|H]; [unfold GLOB_LO, GLOB_N in Hg; lia | exact (Ge H)]. }
      assert (NE : ~ Ec a).
      { intros HE. destruct (HEc a HE) as [H|[H|H]]; [contradiction | contradiction |].
        apply (FB3 (a - p)); [lia|]. replace (p + (a - p)) with a by ring. exact Gi. }
      exact (proj1 (PF a (or_intror Gi) (GOWN Lc Ac mc mdc a HM (glob_in a Hg)) (GOWN L' A' m' md' a PM (glob_in a Hg))
                       NS NE)).
    - intros a Ha _. apply glob_writable. unfold G_REC, REC_SC, REC_SIZE, SC_SIZE, GLOB_LO, GLOB_N in *. lia.
    - intros pn Hpn. pose proof (rec_rep_O_in _ _ _ _ _ _ _ _ _ GR Hpn) as Hb.
      split; [exact (CUR pn Hb)|]. intros i Hi. destruct pn as [q n]. cbn [fst snd] in *.
      exact (BK q n i Hb (fun H => H) Hi).
    - exact NQ.
    - exact Hp0.
    - exact PIN.
    - exact Hno.
    - exact Hlx.
    - exact Hsz.
    - exact BX.
    - apply APT; [unfold REC_SIZE; lia|]. intros a Ha. apply (glob_in_img B SEGS).
      unfold G_REC, REC_SIZE, GLOB_LO, GLOB_N in *. lia.
    - apply APT; [unfold SC_SIZE; lia|]. intros a Ha. apply (glob_in_img B SEGS).
      unfold REC_SC, SC_SIZE, GLOB_LO, GLOB_N in *. lia. }
  split; [exact RJ'|]. split; [exact GR'|].
  split.
  { intros pn Hpn. apply in_app_or in Hpn as [H|[<-|[]]]; [exact (ON pn H)|].
    destruct (in_dec pair_dec (p, k) O) as [H|H]; [left; exact H | right; intros Hb].
    destruct (in_dec pair_dec (p, k) (blocks Lc Ac)) as [Hc|Hc]; [exact (NOTC Hc) | exact (H (B2 _ Hb Hc))]. }
  split.
  { intros pn Hpn. rewrite EB' in Hpn. apply in_app_or in Hpn as [H|[H|H]].
    - destruct (B1 pn ltac:(rewrite EB; apply in_or_app; left; exact H)) as [X|[X|X]];
        [left; exact X | right; left; apply in_or_app; left; exact X | right; right; exact X].
    - subst pn. right. left. apply in_or_app. right. left. reflexivity.
    - destruct (B1 pn ltac:(rewrite EB; apply in_or_app; right; exact H)) as [X|[X|X]];
        [left; exact X | right; left; apply in_or_app; left; exact X | right; right; exact X]. }
  split.
  { intros pn H1 H2. apply B2; [exact H1|]. intros Hc. exact (H2 (CUR pn Hc)). }
  split; [exact RA'|]. split; [exact F18'|].
  split.
  { rewrite <- (sb_shift_trans bc A Ac A'). rewrite <- (sb_shift_add (sb_shift bc A Ac) Lc Ac L' A' b1 b2 p k EB' EB).
    exact RS'. }
  split; [exact (CUR lb LIN)|]. split; [exact LNO|].
  intros Hl. apply in_app_or in Hl as [Hl|[Hl|[]]]; [exact (LOC Hl)|]. rewrite <- Hl in LIN. exact (NOTC LIN).
Qed.

Lemma sinvx_blk_out : forall K S L A mem md O Lc Ac mc mdc Rc Oc bc lb W,
  sinvx K S L A mem md O Lc Ac mc mdc Rc Oc bc lb ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ outside W a -> S - K <= a < S \/ rec_area a) ->
  forall q k i, In (q, k) (blocks Lc Ac) -> 0 <= i < k -> 0 <= q + i < 2 ^ 64 /\ outside W (q + i).
Proof using SEGS AX.
  intros K S L A mem md O Lc Ac mc mdc Rc Oc bc lb W SI HW q k i Hin Hi.
  pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_val as AC.
  pose proof SI as (RJ & _).
  destruct (rjr_bounds B _ K S rec_area _ L A mem md Lc Ac mc mdc RJ) as (HK1 & HK2 & HK3).
  pose proof RJ as (HM & _).
  destruct (block_facts B _ LAWS Lc Ac mc mdc q k i HM Hin Hi) as (_ & H4 & H5 & _).
  split; [lia|]. destruct (outside_dec W (q + i)) as [Ho|Ho]; [exact Ho|]. exfalso.
  destruct (HW (q + i) ltac:(lia) Ho) as [Hs|Hr]; [lia|].
  unfold blocks in Hin. apply in_map_iff in Hin as ([p k'] & E & Hp). cbn in E. injection E as <- <-.
  apply (ax_blocks_img AX Lc Ac mc mdc p k' i HM Hp Hi). apply (glob_in_img B SEGS). exact (rec_area_glob _ Hr).
Qed.

Lemma sinvx_sarg : forall K S L A mem md O Lc Ac mc mdc Rp fn As Oc bc lb Kc regs_c L' A' regs' m' md' m'' W x p k,
  sinvx K S L A mem md O Lc Ac mc mdc (rec_record Rp fn As) Oc bc lb ->
  (length As < 6)%nat ->
  S - K <= spZ regs_c - Kc -> spZ regs_c <= S ->
  call_post_k B (aa_MR API) Kc Lc Ac regs_c mc mdc (fun a => p <= a < p + k) L' A' regs' m' md' ->
  munch W m' m'' -> wmono rsegs m' m'' ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ outside W a ->
     rec_entry G_REC REC_SC Rp + CALL_OFF_NARGS <= a < rec_entry G_REC REC_SC Rp + CALL_OFF_NARGS + 4 \/
     rec_entry G_REC REC_SC Rp + CALL_OFF_ARGS + 8 * Z.of_nat (length As) <= a <
       rec_entry G_REC REC_SC Rp + CALL_OFF_ARGS + 8 * Z.of_nat (length As) + 8) ->
  p <> 0 -> fresh_block B p k ->
  (exists b1 b2, blocks L' A' = b1 ++ (p, k) :: b2 /\ blocks Lc Ac = b1 ++ b2) ->
  (forall q n, In (q, n) (user_blocks Ac) -> In (q, n) (user_blocks A')) ->
  blocks_kept B Lc Ac mc m' (fun _ => False) ->
  (length (st_regions Ac) <= length (st_regions A'))%nat ->
  bytes_at rsegs m'' (rec_entry G_REC REC_SC Rp + CALL_OFF_NARGS) (le4 (Z_to_bv 64 (Z.of_nat (length As) + 1))) ->
  bytes_at rsegs m'' (rec_entry G_REC REC_SC Rp + CALL_OFF_ARGS + 8 * Z.of_nat (length As)) (le8 (Z_to_bv 64 p)) ->
  bytes_at rsegs m' p (x ++ [Z_to_bv 8 0]) ->
  no0 x -> Z.of_nat (length x) <= LMAX -> Z.of_nat (length x) + 1 <= k <= LMAX + 2 ->
  st_init_done A' = true ->
  res_ok_slots A' (sb_malloc (sb_shift bc A Ac) k) ->
  ro_agree rsegs m' -> f18_words rsegs m' ->
  sinvx K S L A mem md O L' A' m'' md' (rec_record Rp fn (As ++ [x])) (Oc ++ [(p, k)]) bc lb.
Proof using SEGS AX GOWN GFACT ERRNO_LOW.
  intros K S L A mem md O Lc Ac mc mdc Rp fn As Oc bc lb Kc regs_c L' A' regs' m' md' m'' W x p k
    SI H6 HLO HHI POST MU WM HW Hp0 FB EBS UB BK RGN BN BS BX Hno Hlx Hsz INI RS' RA' F18'.
  pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_val as AC.
  pose proof SI as (RJ & GR & _).
  assert (ER : REC_SC <= rec_entry G_REC REC_SC Rp /\ rec_entry G_REC REC_SC Rp + CALL_SIZE <= G_REC + REC_SIZE).
  { unfold rec_entry. destruct (Nat.ltb (length (r_calls Rp)) 16) eqn:E.
    - apply Nat.ltb_lt in E. unfold REC_SC, G_REC, OFF_CALLS, CALL_SIZE, REC_SIZE. lia.
    - unfold REC_SC, G_REC, CALL_SIZE, REC_SIZE. lia. }
  assert (HWR : forall a, 0 <= a < 2 ^ 64 -> ~ outside W a -> rec_area a).
  { intros a Ra Hn. destruct (HW a Ra Hn) as [H|H];
      unfold rec_area, G_REC, REC_SC, REC_SIZE, SC_SIZE, CALL_SIZE, CALL_OFF_NARGS, CALL_OFF_ARGS in *; lia. }
  assert (OUTW : forall a, 0 <= a < 2 ^ 64 -> ~ rec_area a -> outside W a).
  { intros a Ra Hr. destruct (outside_dec W a) as [H|H]; [exact H|]. exfalso. exact (Hr (HWR a Ra H)). }
  pose proof POST as (PM & PW & PB & PL & PA & PR & PV & PF & PK & PS).
  rewrite SEGS in PF, PK, PS.
  assert (BLW : forall q n i, In (q, n) (user_blocks A') -> 0 <= i < n ->
            0 <= ptr_addr L' q + i < 2 ^ 64 /\ outside W (ptr_addr L' q + i)).
  { intros q n i Hin Hi. destruct (mr_blocks B _ LAWS L' A' m' md' q n i PM Hin Hi) as (Q1 & Q2 & Q3 & _).
    split; [lia|]. apply OUTW; [lia|]. intros Hr. apply (ax_blocks_img AX L' A' m' md' q n i PM Hin Hi).
    apply (glob_in_img B SEGS). exact (rec_area_glob _ Hr). }
  assert (PM2 : aa_MR API L' A' m'' md').
  { apply (mr_keep B _ LAWS L' A' m' m'' md' W PM MU).
    - intros a Ho. destruct (owned_low B _ LAWS _ _ _ _ a PM Ho) as [Hl1 Hl2].
      apply OUTW; [lia|]. intros Hr. exact (GOWN L' A' m' md' a PM (glob_in a (rec_area_glob a Hr)) Ho).
    - intros q n i Hin Hi. exact (proj2 (BLW q n i Hin Hi)). }
  assert (POST2 : call_post_k B (aa_MR API) Kc Lc Ac regs_c mc mdc
                    (fun a => p <= a < p + k \/ (0 <= a < 2 ^ 64 /\ ~ outside W a)) L' A' regs' m'' md').
  { split; [exact PM2|]. split; [exact PW|]. split; [exact PB|]. split; [exact PL|]. split; [exact PA|].
    split; [exact PR|]. split; [exact PV|]. rewrite SEGS.
    split.
    { intros a Hr Hn1 Hn2 Hs He.
      assert (Ra : 0 <= a < 2 ^ 64) by (destruct Hr as [Hr|Hr]; [lia | pose proof (in_img_low B SEGS a Hr); lia]).
      assert (Oa : outside W a).
      { destruct (outside_dec W a) as [H|H]; [exact H|]. exfalso. apply He. right. split; assumption. }
      destruct (PF a Hr Hn1 Hn2 Hs (fun H => He (or_introl H))) as [E1 E2].
      rewrite (munch_mbyte rsegs W m' m'' a MU Ra Oa). split; [exact E1|].
      rewrite E2. exact (munch_writable rsegs W m' m'' a MU Ra Oa). }
    split.
    { intros q n i H1 H2 Hi. rewrite <- (PK q n i H1 H2 Hi). rewrite <- (PA q n H1 H2).
      destruct (BLW q n i H2 Hi) as [Rr Oo]. exact (munch_mbyte rsegs W m' m'' _ MU Rr Oo). }
    intros a Hs. exact (WM _ (PS a Hs)). }
  pose proof FB as (FB1 & FB2 & FB3).
  pose proof (bytes_at_bound _ _ _ _ BX) as BXB. rewrite length_app in BXB. cbn [length] in BXB.
  apply (sinvx_arg K S L A mem md O Lc Ac mc mdc Rp fn As Oc bc lb Kc regs_c _ L' A' regs' m'' md' x p k
           SI H6 HLO HHI POST2).
  - intros a [Ha|(Ra & Ha)]; [right; right; exact Ha|].
    destruct (HW a Ra Ha) as [H|H]; [left; exact H | right; left; exact H].
  - exact Hp0.
  - exact FB.
  - exact EBS.
  - exact UB.
  - unfold blocks_kept in *. rewrite SEGS in BK |- *. intros a0 k0 i Hin Hg Hi.
    rewrite <- (BK a0 k0 i Hin Hg Hi).
    destruct (sinvx_blk_out K S L A mem md O Lc Ac mc mdc _ Oc bc lb W SI
                (fun a Ra Hn => or_intror (HWR a Ra Hn)) a0 k0 i Hin Hi) as [Rr Oo].
    exact (munch_mbyte rsegs W m' m'' _ MU Rr Oo).
  - exact RGN.
  - exact BN.
  - exact BS.
  - apply (bytes_at_transfer rsegs m' m'' p _ BX). intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
    apply (munch_mbyte rsegs W m' m'' _ MU); [lia|]. apply OUTW; [lia|]. intros Hr.
    apply (FB3 i); [lia|]. apply (glob_in_img B SEGS). exact (rec_area_glob _ Hr).
  - exact Hno.
  - exact Hlx.
  - exact Hsz.
  - exact INI.
  - exact RS'.
  - apply (ro_out W m' m'' RA' MU). intros a Ha Hro. apply OUTW; [lia|].
    intros Hr. rewrite glob_ro_false in Hro by exact (rec_area_glob a Hr). discriminate.
  - apply (f18_out W m' m'' F18' MU). intros i Hi.
    split; (apply OUTW; unfold rec_area, REC_SC, SC_SIZE, G_REC, REC_SIZE, snprintf_c.GOT_GUARD, snprintf_c.GUARD; lia).
Qed.

Lemma sinvx_malloc : forall K S L A mem md O Lc Ac mc mdc Rc Oc bc Kc regs_c L' A' regs' m' md' p z,
  sinv B API K S L A mem md O Lc Ac mc mdc Rc Oc bc ->
  S - K <= spZ regs_c - Kc -> spZ regs_c <= S ->
  call_post_k B (aa_MR API) Kc Lc Ac regs_c mc mdc (fun _ => False) L' A' regs' m' md' ->
  0 < z -> fresh_block B p z ->
  (exists b1 b2, blocks L' A' = b1 ++ (p, z) :: b2 /\ blocks Lc Ac = b1 ++ b2) ->
  (forall q n, In (q, n) (user_blocks Ac) -> In (q, n) (user_blocks A')) ->
  blocks_kept B Lc Ac mc m' (fun _ => False) ->
  (length (st_regions Ac) <= length (st_regions A'))%nat ->
  st_init_done A' = true ->
  res_ok_slots A' (sb_malloc (sb_shift bc A Ac) z) ->
  ro_agree rsegs m' -> f18_words rsegs m' ->
  sinvx K S L A mem md O L' A' m' md' Rc Oc bc (p, z).
Proof using SEGS AX GOWN GFACT ERRNO_LOW.
  intros K S L A mem md O Lc Ac mc mdc Rc Oc bc Kc regs_c L' A' regs' m' md' p z
    SI HLO HHI POST Hk FB (b1 & b2 & EB' & EB) UB BK RGN INI RS' RA' F18'.
  pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_val as AC.
  pose proof SI as (RJ & GR & ON & B1 & B2 & RA & F18 & RS).
  pose proof RJ as (HM & _).
  destruct (rjr_bounds B _ K S rec_area _ L A mem md Lc Ac mc mdc RJ) as (HK1 & HK2 & HK3).
  pose proof POST as (PM & PW & PB & PL & PA & PR & PV & PF & PK & PS).
  unfold blocks_kept in BK. rewrite SEGS in BK, PF.
  assert (PIN : In (p, z) (blocks L' A')) by (rewrite EB'; apply in_elt).
  assert (PERM : Permutation (blocks L' A') ((b1 ++ b2) ++ [(p, z)])).
  { rewrite EB'. eapply Permutation_trans; [apply Permutation_sym, Permutation_middle | apply Permutation_cons_append]. }
  assert (NOTC : ~ In (p, z) (blocks Lc Ac)).
  { rewrite EB. intros H. exact (perm_not_both _ _ _ (p, z) PERM (mr_blocks_disjoint B _ LAWS L' A' m' md' PM)
                                   Hk H (or_introl eq_refl)). }
  assert (CUR : forall pn, In pn (blocks Lc Ac) -> In pn (blocks L' A')).
  { intros pn Hpn. rewrite EB'. rewrite EB in Hpn. exact (in_mid_inv b1 b2 (p, z) pn Hpn). }
  assert (RIMG' : forall a, REC_SC <= a < G_REC + REC_SIZE -> GLOB_LO <= a < GLOB_LO + Z.of_nat GLOB_N)
    by (intros a Ha; unfold REC_SC, G_REC, REC_SIZE, GLOB_LO, GLOB_N in *; lia).
  assert (RJ' : rjr B (aa_MR API) K S rec_area (fun pn => In pn O) L A mem md L' A' m' md').
  { apply (rjr_post B _ SEGS LAWS AX ERRNO_LOW K S rec_area _ L A mem md Lc Ac mc mdc Kc regs_c (fun _ => False)
             (fun _ => False) L' A' regs' m' md' RJ (call_post_k_rec B _ _ _ _ _ _ _ _ _ _ _ _ _ POST) HLO HHI).
    - intros a [].
    - intros p0 n0 _ _ _ [].
    - intros p0 n0 _ Hc Hn. exfalso. exact (Hn (UB p0 n0 Hc)).
    - exact RGN.
    - intros Hf. rewrite INI in Hf. discriminate. }
  assert (GR' : g_rec_rep rsegs L' A' m' Rc Oc).
  { unfold g_rec_rep in *.
    apply (rec_rep_frame rsegs G_REC REC_SC Lc Ac mc Rc Oc L' A' m' GR).
    - intros a Ha.
      assert (Hg : GLOB_LO <= a < GLOB_LO + Z.of_nat GLOB_N)
        by (apply RIMG'; unfold G_REC, REC_SC, REC_SIZE, SC_SIZE in *; lia).
      destruct (GFACT a (glob_in a Hg)) as (Gi & _ & _ & Ge).
      assert (NS : ~ scratch_k B Kc regs_c a).
      { unfold scratch_k. intros [H|H]; [unfold GLOB_LO, GLOB_N in Hg; lia | exact (Ge H)]. }
      destruct (PF a (or_intror Gi) (GOWN Lc Ac mc mdc a HM (glob_in a Hg)) (GOWN L' A' m' md' a PM (glob_in a Hg))
                  NS (fun H => H)) as [E1 E2].
      split; [exact E1 | intros W; apply E2; exact W].
    - intros q n i Hq Hi. exact (BK q n i (rec_rep_O_in _ _ _ _ _ _ _ _ _ GR Hq) (fun H => H) Hi).
    - intros pn Hpn. exact (CUR pn (rec_rep_O_in _ _ _ _ _ _ _ _ _ GR Hpn)). }
  split; [exact RJ'|]. split; [exact GR'|]. split; [exact ON|].
  split.
  { intros pn Hpn. rewrite EB' in Hpn. apply in_app_or in Hpn as [H|[H|H]].
    - destruct (B1 pn ltac:(rewrite EB; apply in_or_app; left; exact H)) as [X|X];
        [left; exact X | right; left; exact X].
    - subst pn. right. right. reflexivity.
    - destruct (B1 pn ltac:(rewrite EB; apply in_or_app; right; exact H)) as [X|X];
        [left; exact X | right; left; exact X]. }
  split.
  { intros pn H1 H2. apply B2; [exact H1|]. intros Hc. exact (H2 (CUR pn Hc)). }
  split; [exact RA'|]. split; [exact F18'|].
  split.
  { rewrite <- (sb_shift_trans bc A Ac A'). rewrite <- (sb_shift_add (sb_shift bc A Ac) Lc Ac L' A' b1 b2 p z EB' EB).
    exact RS'. }
  split; [exact PIN|]. split; [intros HL; exact (B2 _ HL NOTC)|].
  intros Hq. exact (NOTC (rec_rep_O_in _ _ _ _ _ _ _ _ _ GR Hq)).
Qed.

Lemma sinvx_free : forall K S L A mem md O Lc Ac mc mdc Rc Oc bc q lp z Kc regs_c L' A' regs' m' md',
  sinvx K S L A mem md O Lc Ac mc mdc Rc Oc bc (lp, z) ->
  S - K <= spZ regs_c - Kc -> spZ regs_c <= S -> 0 < z ->
  In (q, z) (user_blocks Ac) -> ptr_addr Lc q = lp ->
  call_post_k B (aa_MR API) Kc Lc Ac regs_c mc mdc (fun a => lp <= a < lp + z) L' A' regs' m' md' ->
  (exists b1 b2, blocks Lc Ac = b1 ++ (lp, z) :: b2 /\ blocks L' A' = b1 ++ b2) ->
  blocks_kept B Lc Ac mc m' (fun a => a = lp) ->
  (forall q' k, In (q', k) (user_blocks Ac) -> q' <> q -> In (q', k) (user_blocks A')) ->
  st_init_done A' = true ->
  (length (st_regions Ac) <= length (st_regions A'))%nat ->
  res_ok_slots A' (sb_free (sb_shift bc A Ac) z) ->
  ro_agree rsegs m' -> f18_words rsegs m' ->
  sinv B API K S L A mem md O L' A' m' md' Rc Oc bc.
Proof using SEGS AX GOWN GFACT ERRNO_LOW.
  intros K S L A mem md O Lc Ac mc mdc Rc Oc bc q lp z Kc regs_c L' A' regs' m' md'
    SI HLO HHI Hz HQ HLP POST (b1 & b2 & EB & EB') BK UB INI RGN RS' RA' F18'.
  pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_val as AC.
  pose proof SI as (RJ & GR & ON & B1 & B2 & RA & F18 & RS & LIN & LNO & LOC).
  pose proof RJ as (HM & HWA & HWc & _ & HLc & _).
  destruct (rjr_bounds B _ K S rec_area _ L A mem md Lc Ac mc mdc RJ) as (HK1 & HK2 & HK3).
  pose proof POST as (PM & PW & PB & PL & PA & PR & PV & PF & PK & PS).
  unfold blocks_kept in BK. rewrite SEGS in BK, PF.
  assert (NIMG : forall i, 0 <= i < z -> ~ in_img B (lp + i)).
  { intros i Hi. rewrite <- HLP. exact (ax_blocks_img AX Lc Ac mc mdc q z i HM HQ Hi). }
  assert (SAME : forall n, In (lp, n) (blocks Lc Ac) -> 0 < n -> n = z).
  { intros n Hn Hp. exact (blocks_same_addr B _ LAWS Lc Ac mc mdc lp n z HM Hn LIN Hp Hz). }
  assert (RIMG' : forall a, REC_SC <= a < G_REC + REC_SIZE -> GLOB_LO <= a < GLOB_LO + Z.of_nat GLOB_N)
    by (intros a Ha; unfold REC_SC, G_REC, REC_SIZE, GLOB_LO, GLOB_N in *; lia).
  assert (RJ' : rjr B (aa_MR API) K S rec_area (fun pn => In pn O) L A mem md L' A' m' md').
  { apply (rjr_post B _ SEGS LAWS AX ERRNO_LOW K S rec_area _ L A mem md Lc Ac mc mdc Kc regs_c _
             (fun _ => False) L' A' regs' m' md' RJ (call_post_k_rec B _ _ _ _ _ _ _ _ _ _ _ _ _ POST) HLO HHI).
    - intros a Ha Hf. exfalso.
      destruct (block_facts B _ LAWS Lc Ac mc mdc lp z (a - lp) HM LIN ltac:(lia)) as (_ & _ & BND & _).
      destruct Hf as [Hf|(Hi & _)]; [lia|].
      apply (NIMG (a - lp)); [lia|]. replace (lp + (a - lp)) with a by ring. exact Hi.
    - intros p0 n0 _ _ _ [].
    - intros p0 n0 HA HAc HA'.
      destruct (in_dec pair_dec (ptr_addr L p0, n0) O) as [H|H]; [exact H|]. exfalso. apply HA'.
      apply UB; [exact HAc|]. intros ->.
      assert (En : n0 = z).
      { exact (CF.hand_back.hb_assoc_nd (user_blocks Ac) q n0 z (user_block_ptrs_NoDup Ac HWc) HAc HQ). }
      subst n0. apply H. rewrite <- (CF.hand_back.hb_ptr_le A L Lc q z HWA HA HLc), HLP. apply LNO.
      unfold blocks. apply in_map_iff. exists (q, z). split; [|exact HA]. cbn.
      rewrite <- HLP, (CF.hand_back.hb_ptr_le A L Lc q z HWA HA HLc). reflexivity.
    - exact RGN.
    - intros Hf. rewrite INI in Hf. discriminate. }
  assert (OCB : forall pn, In pn Oc -> In pn (blocks L' A')).
  { intros pn Hpn. pose proof (rec_rep_O_in _ _ _ _ _ _ _ _ _ GR Hpn) as Hb. rewrite EB in Hb. rewrite EB'.
    apply in_app_or in Hb as [Hb|[Hb|Hb]]; [apply in_or_app; left; exact Hb | | apply in_or_app; right; exact Hb].
    exfalso. subst pn. exact (LOC Hpn). }
  assert (GR' : g_rec_rep rsegs L' A' m' Rc Oc).
  { unfold g_rec_rep in *.
    apply (rec_rep_frame rsegs G_REC REC_SC Lc Ac mc Rc Oc L' A' m' GR).
    - intros a Ha.
      assert (Hg : GLOB_LO <= a < GLOB_LO + Z.of_nat GLOB_N)
        by (apply RIMG'; unfold G_REC, REC_SC, REC_SIZE, SC_SIZE in *; lia).
      destruct (GFACT a (glob_in a Hg)) as (Gi & _ & _ & Ge).
      assert (NS : ~ scratch_k B Kc regs_c a).
      { unfold scratch_k. intros [H|H]; [unfold GLOB_LO, GLOB_N in Hg; lia | exact (Ge H)]. }
      assert (NE : ~ (lp <= a < lp + z)).
      { intros H. apply (NIMG (a - lp)); [lia|]. replace (lp + (a - lp)) with a by ring. exact Gi. }
      destruct (PF a (or_intror Gi) (GOWN Lc Ac mc mdc a HM (glob_in a Hg)) (GOWN L' A' m' md' a PM (glob_in a Hg))
                  NS NE) as [E1 E2].
      split; [exact E1 | intros W; apply E2; exact W].
    - intros q0 n i Hq Hi. pose proof (rec_rep_O_in _ _ _ _ _ _ _ _ _ GR Hq) as Hb.
      apply (BK q0 n i Hb); [|exact Hi]. intros ->.
      pose proof (rec_rep_pos _ _ _ _ _ _ _ _ _ GR Hq) as Hn. cbn in Hn.
      pose proof (SAME n Hb Hn) as ->. exact (LOC Hq).
    - exact OCB. }
  split; [exact RJ'|]. split; [exact GR'|]. split; [exact ON|].
  split.
  { intros pn Hpn. assert (Hc : In pn (blocks Lc Ac)).
    { rewrite EB. rewrite EB' in Hpn. exact (in_mid_inv b1 b2 (lp, z) pn Hpn). }
    destruct (B1 pn Hc) as [X|[X|X]]; [left; exact X | right; exact X |].
    exfalso. subst pn. rewrite EB' in Hpn.
    destruct (blocks_mid_disjoint B _ LAWS Lc Ac mc mdc b1 b2 lp z lp z HM EB Hpn); lia. }
  split.
  { intros pn H1 H2. destruct (in_dec pair_dec pn (blocks Lc Ac)) as [Hc|Hc]; [|exact (B2 pn H1 Hc)].
    rewrite EB in Hc. apply in_app_or in Hc as [Hc|[Hc|Hc]].
    - exfalso. apply H2. rewrite EB'. apply in_or_app. left. exact Hc.
    - subst pn. exact (LNO H1).
    - exfalso. apply H2. rewrite EB'. apply in_or_app. right. exact Hc. }
  split; [exact RA'|]. split; [exact F18'|].
  rewrite <- (sb_shift_trans bc A Ac A'). rewrite <- (sb_shift_del (sb_shift bc A Ac) Lc Ac L' A' b1 b2 lp z EB EB').
  exact RS'.
Qed.

Lemma sc_f18_img : forall i, 0 <= i < 8 -> in_img B (snprintf_c.GOT_GUARD + i) /\ in_img B (snprintf_c.GUARD + i).
Proof using SEGS.
  intros i Hi. unfold snprintf_c.GOT_GUARD, snprintf_c.GUARD.
  assert (C : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7) by lia.
  destruct C as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]];
    split; apply (in_img_found B SEGS); try lia; vm_compute; discriminate.
Qed.

Lemma sinvx_heap : forall K S L A mem md O Lc Ac mc mdc Rc Oc bc lp z m' W,
  sinvx K S L A mem md O Lc Ac mc mdc Rc Oc bc (lp, z) ->
  munch W mc m' -> wmono rsegs mc m' ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ outside W a -> S - K <= a < S \/ lp <= a < lp + z) ->
  sinvx K S L A mem md O Lc Ac m' mdc Rc Oc bc (lp, z).
Proof using SEGS AX GOWN.
  intros K S L A mem md O Lc Ac mc mdc Rc Oc bc lp z m' W SI MU WM HW.
  pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_val as AC.
  pose proof SI as (RJ & GR & ON & B1 & B2 & RA & F18 & RS & LIN & LNO & LOC).
  destruct (rjr_bounds B _ K S rec_area _ L A mem md Lc Ac mc mdc RJ) as (HK1 & HK2 & HK3).
  pose proof RJ as (HM & HWA & _ & _ & HL & _).
  pose proof LIN as LIN'. unfold blocks in LIN'. apply in_map_iff in LIN' as ([q z'] & Eq & HQ).
  cbn in Eq. injection Eq as HLP ->.
  assert (LBF : forall i, 0 <= i < z -> ~ in_img B (lp + i) /\ lp + z <= alloc_ceiling /\ ~ owned B Lc Ac (lp + i)).
  { intros i Hi. destruct (block_facts B _ LAWS Lc Ac mc mdc lp z i HM LIN Hi) as (_ & _ & H5 & H6).
    split; [rewrite <- HLP; exact (ax_blocks_img AX Lc Ac mc mdc q z i HM HQ Hi) | split; assumption]. }
  assert (Hz0 : forall a, lp <= a < lp + z -> lp + z <= alloc_ceiling /\ ~ in_img B a /\ ~ owned B Lc Ac a).
  { intros a Ha. destruct (LBF (a - lp) ltac:(lia)) as (H1 & H2 & H3).
    replace (lp + (a - lp)) with a in H1, H3 by ring. tauto. }
  assert (PRES : forall p n i, In (p, n) (user_blocks Ac) -> 0 <= i < n -> present m' (ptr_addr Lc p + i)).
  { intros p n i Hc Hi.
    assert (Hb : In (ptr_addr Lc p, n) (blocks Lc Ac)) by (unfold blocks; apply in_map_iff; exists (p, n); auto).
    destruct (block_facts B _ LAWS Lc Ac mc mdc _ n i HM Hb Hi) as (Hp & H2 & H3 & _).
    pose proof (ax_blocks_img AX Lc Ac mc mdc p n i HM Hc Hi) as NI.
    apply (present_of_writable_out B SEGS); [lia | exact NI |]. apply WM. apply present_writable. exact Hp. }
  assert (RJ' : rjr B (aa_MR API) K S rec_area (fun pn => In pn O) L A mem md Lc Ac m' mdc).
  { apply (rjr_munch B (aa_MR API) SEGS LAWS K S rec_area (fun pn => In pn O) L A mem md Lc Ac mc mdc m' W RJ MU);
      [rewrite SEGS; exact WM | | | | | exact PRES].
    - intros a Ra Hn Hf. destruct (HW a Ra Hn) as [H|H]; [left; exact H|]. exfalso.
      destruct (Hz0 a H) as (H1 & H2 & _). destruct Hf as [Hf|(Hi & _)]; [lia | exact (H2 Hi)].
    - intros a Ra Hn Ho. destruct (HW a Ra Hn) as [H|H].
      + pose proof (mr_owned_low B _ LAWS Lc Ac mc mdc a HM Ho). lia.
      + exact (proj2 (proj2 (Hz0 a H)) Ho).
    - intros a Ha. destruct (outside_dec W a) as [H|H]; [exact H|]. exfalso.
      destruct (HW a ltac:(lia) H) as [H'|H']; [lia | destruct (Hz0 a H'); lia].
    - intros p n i Hin Hg Hi.
      pose proof (rjr_in_cur B _ K S rec_area _ L A mem md Lc Ac mc mdc p n RJ Hin Hg) as Hc.
      rewrite <- (ptr_addr_stable A L Lc p n HWA Hin HL).
      assert (Hb : In (ptr_addr Lc p, n) (blocks Lc Ac)) by (unfold blocks; apply in_map_iff; exists (p, n); auto).
      destruct (block_facts B _ LAWS Lc Ac mc mdc _ n i HM Hb Hi) as (_ & H2 & H3 & _).
      destruct (outside_dec W (ptr_addr Lc p + i)) as [H|H]; [exact H|]. exfalso.
      destruct (HW (ptr_addr Lc p + i) ltac:(lia) H) as [H'|H']; [lia|].
      destruct (pair_dec (ptr_addr Lc p, n) (lp, z)) as [E|NE].
      + apply Hg. rewrite <- (ptr_addr_stable A L Lc p n HWA Hin HL), E. apply LNO.
        rewrite <- E, (ptr_addr_stable A L Lc p n HWA Hin HL). unfold blocks. apply in_map_iff.
        exists (p, n). split; [reflexivity | exact Hin].
      + destruct (CF.hand_back.hb_pw_in2 _ _ _ _ (mr_blocks_disjoint B _ LAWS Lc Ac mc mdc HM) Hb LIN NE) as [D|D];
          hnf in D; cbn [fst snd] in D; lia. }
  assert (GR' : g_rec_rep rsegs Lc Ac m' Rc Oc).
  { unfold g_rec_rep in *. apply (rec_rep_keep rsegs G_REC REC_SC Lc Ac mc m' Rc Oc GR).
    - intros a Ha. apply (munch_mbyte rsegs W mc m'); [exact MU | unfold G_REC, REC_SC, REC_SIZE, SC_SIZE in Ha; lia|].
      destruct (outside_dec W a) as [H|H]; [exact H|]. exfalso.
      destruct (HW a ltac:(unfold G_REC, REC_SC, REC_SIZE, SC_SIZE in Ha; lia) H) as [H'|H'];
        [unfold G_REC, REC_SC, REC_SIZE, SC_SIZE in Ha; lia|].
      destruct (Hz0 a H') as (_ & H2 & _). apply H2. apply (glob_in_img B SEGS).
      unfold G_REC, REC_SC, REC_SIZE, SC_SIZE, GLOB_LO, GLOB_N in *. lia.
    - intros a Ha _. apply glob_writable. unfold G_REC, REC_SC, REC_SIZE, SC_SIZE, GLOB_LO, GLOB_N in *. lia.
    - intros p k i Hin Hi. pose proof (rec_rep_O_in _ _ _ _ _ _ _ _ _ GR Hin) as Hb.
      destruct (block_facts B _ LAWS Lc Ac mc mdc p k i HM Hb Hi) as (_ & H4 & H5 & _).
      apply (munch_mbyte rsegs W mc m'); [exact MU | lia |].
      destruct (outside_dec W (p + i)) as [H|H]; [exact H|]. exfalso.
      destruct (HW (p + i) ltac:(lia) H) as [H'|H']; [lia|].
      assert (NE : (p, k) <> (lp, z)) by (intros E; rewrite E in Hin; exact (LOC Hin)).
      destruct (CF.hand_back.hb_pw_in2 _ _ _ _ (mr_blocks_disjoint B _ LAWS Lc Ac mc mdc HM) Hb LIN NE) as [D|D];
        hnf in D; cbn [fst snd] in D; lia. }
  assert (OUT : forall a, 0 <= a < 2 ^ 64 -> ~ (S - K <= a < S) -> in_img B a -> outside W a).
  { intros a Ra Hs Hi. destruct (outside_dec W a) as [H|H]; [exact H|]. exfalso.
    destruct (HW a Ra H) as [H'|H']; [exact (Hs H') | exact (proj1 (proj2 (Hz0 a H')) Hi)]. }
  split; [exact RJ'|]. split; [exact GR'|]. split; [exact ON|]. split; [exact B1|]. split; [exact B2|].
  split.
  { apply (ro_out W mc m' RA MU). intros a Ha Hro. apply OUT; [lia | lia |].
    exact (ro_in_img B SEGS a ltac:(lia) Hro). }
  split.
  { apply (f18_out W mc m' F18 MU). intros i Hi.
    destruct (sc_f18_img i Hi) as [I1 I2].
    split; apply OUT; unfold snprintf_c.GOT_GUARD, snprintf_c.GUARD in *; try lia; assumption. }
  split; [exact RS|]. split; [exact LIN|]. split; [exact LNO | exact LOC].
Qed.

Lemma sc_disj : forall lp z G, 0 < z -> (forall i, 0 <= i < z -> ~ in_img B (lp + i)) ->
  (forall i, 0 <= i < 8 -> in_img B (G + i)) -> G + 8 <= lp \/ lp + z <= G.
Proof using.
  intros lp z G Hz N I. destruct (Z_le_gt_dec (G + 8) lp) as [H|H]; [left; exact H|].
  destruct (Z_le_gt_dec (lp + z) G) as [H'|H']; [right; exact H'|]. exfalso.
  remember (Z.max lp G) as a eqn:Ea.
  assert (R1 : 0 <= a - lp < z) by lia. assert (R2 : 0 <= a - G < 8) by lia.
  pose proof (N (a - lp) R1) as N1. pose proof (I (a - G) R2) as I1.
  replace (lp + (a - lp)) with a in N1 by ring. replace (G + (a - G)) with a in I1 by ring. exact (N1 I1).
Qed.

Lemma sc_blk : forall K S L A mem md O Lc Ac mc mdc Rc Oc bc lp z,
  sinvx K S L A mem md O Lc Ac mc mdc Rc Oc bc (lp, z) -> 0 < z ->
  pf_img_free lp z /\
  (forall m', wmono rsegs mc m' -> forall i, 0 <= i < z -> present m' (lp + i)) /\
  (snprintf_c.GOT_GUARD + 8 <= lp \/ lp + z <= snprintf_c.GOT_GUARD) /\
  (snprintf_c.GUARD + 8 <= lp \/ lp + z <= snprintf_c.GUARD) /\
  0 <= lp /\ lp + z <= alloc_ceiling.
Proof using SEGS AX.
  intros K S L A mem md O Lc Ac mc mdc Rc Oc bc lp z SI Hz.
  pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_val as AC.
  pose proof SI as (RJ & GR & ON & B1 & B2 & RA & F18 & RS & LIN & LNO & LOC).
  pose proof RJ as (HM & _).
  pose proof LIN as LIN'. unfold blocks in LIN'. apply in_map_iff in LIN' as ([q z'] & Eq & HQ).
  cbn in Eq. injection Eq as HLP ->.
  assert (NI : forall i, 0 <= i < z -> ~ in_img B (lp + i)).
  { intros i Hi. rewrite <- HLP. exact (ax_blocks_img AX Lc Ac mc mdc q z i HM HQ Hi). }
  destruct (block_facts B _ LAWS Lc Ac mc mdc lp z 0 HM LIN ltac:(lia)) as (_ & _ & H5 & _).
  destruct (block_facts B _ LAWS Lc Ac mc mdc lp z (z - 1) HM LIN ltac:(lia)) as (_ & Hb2 & Hb3 & _).
  split; [|split; [|split; [|split; [|split]]]].
  - intros i Hi s Hs Hr. apply (NI i Hi). apply (in_img_of_reserved B s); [rewrite SEGS; exact Hs | exact Hr |].
    rewrite SEGS. intros E. unfold segments_reserved in Hs. rewrite E in Hs. destruct Hs.
  - intros m' WM i Hi.
    destruct (block_facts B _ LAWS Lc Ac mc mdc lp z i HM LIN Hi) as (Hp & H2 & H3 & _).
    apply (present_of_writable_out B SEGS); [lia | exact (NI i Hi) |]. apply WM. apply present_writable. exact Hp.
  - apply (sc_disj lp z _ Hz NI). intros i Hi. exact (proj1 (sc_f18_img i Hi)).
  - apply (sc_disj lp z _ Hz NI). intros i Hi. exact (proj2 (sc_f18_img i Hi)).
  - lia.
  - lia.
Qed.

Hypothesis GOTG : ms_got_guard B = 0x22d40.
Hypothesis GRD : ms_guard B = 0x54730.
Hypothesis XM : xmalloc_contract B API.

Lemma sch_xmalloc : forall K S L A mem md O Lc Ac mc mdc Rc Oc bc regs_c z (P : config -> Prop),
  sinv B API K S L A mem md O Lc Ac mc mdc Rc Oc bc ->
  call_pre_k B (aa_MR API) XMALLOC_K Lc Ac regs_c mc mdc ->
  S - K <= spZ regs_c - XMALLOC_K -> spZ regs_c <= S ->
  getr regs_c 10 = Z_to_bv 64 z -> 0 < z <= LMAX + 2 -> room_ag (sb_malloc (sb_shift bc A Ac) z) z ->
  (forall L' A' regs' m' md' p,
     sinvx K S L A mem md O L' A' m' md' Rc Oc bc (p, z) ->
     call_post_k B (aa_MR API) XMALLOC_K Lc Ac regs_c mc mdc (fun _ => False) L' A' regs' m' md' ->
     getr regs' 10 = Z_to_bv 64 p -> p <> 0 -> fresh_block B p z ->
     sb_shift bc A A' = sb_malloc (sb_shift bc A Ac) z ->
     SR rsegs (mkCfg (mkst regs' (getr regs_c 1) m' (seg_rom rsegs)) md') P) ->
  SR rsegs (mkCfg (mkst regs_c (Z_to_bv 64 XMALLOC) mc (seg_rom rsegs)) mdc) P.
Proof using SEGS AX GOWN GFACT ERRNO_LOW GOTG GRD XM.
  intros K S L A mem md O Lc Ac mc mdc Rc Oc bc regs_c z P SI CP HLO HHI E10 Hz ROOM KC.
  pose proof SI as (RJ & GR & ON & B1 & B2 & RA & F18 & RS).
  pose proof XM as XMC. unfold xmalloc_contract in XMC. rewrite SEGS in XMC.
  assert (XS : xmalloc_size z = z) by (unfold xmalloc_size; destruct (Z.eqb_spec z 0); lia).
  eapply SR_bind.
  { apply (XMC Lc Ac regs_c mc mdc z (sb_shift bc A Ac));
      [exact CP | exact E10 | lia | exact RS | rewrite XS; exact ROOM | exact RA]. }
  rewrite XS.
  intros c' (L2 & A2 & R2 & m2 & md2 & p & -> & POST & A0' & NZ & AL16 & FB & BLK & BK & RA2 & GK & UB & INI & RGN & RS2).
  rewrite SEGS in RA2 |- *.
  pose proof POST as (PM2 & _).
  destruct (ax_statics AX L2 A2 m2 md2 PM2) as (_ & (g & Hg & HWg) & _).
  rewrite GRD, SEGS in HWg.
  assert (F182 : f18_words rsegs m2).
  { apply (f18_words_after mc m2 g F18); [|exact Hg | exact HWg].
    intros i Hi. pose proof (GK i Hi) as G. rewrite GOTG, SEGS in G. exact G. }
  assert (SH : sb_shift bc A A2 = sb_malloc (sb_shift bc A Ac) z).
  { pose proof BLK as (l1 & l2 & E1 & E2).
    rewrite (sb_shift_add (sb_shift bc A Ac) Lc Ac L2 A2 l1 l2 p z E1 E2). symmetry. apply sb_shift_trans. }
  apply (KC L2 A2 R2 m2 md2 p); [| exact POST | exact A0' | exact NZ | exact FB | exact SH].
  exact (sinvx_malloc K S L A mem md O Lc Ac mc mdc Rc Oc bc XMALLOC_K regs_c L2 A2 R2 m2 md2 p z SI HLO HHI POST
           ltac:(lia) FB BLK UB BK RGN INI RS2 RA2 F182).
Qed.

Hypothesis FREE_PC : ms_free B = 0x18ad0.
Hypothesis FREE : free_contract B API.

Lemma sch_free : forall K S L A mem md O Lc Ac mc mdc Rc Oc bc q lp z regs_c (P : config -> Prop),
  sinvx K S L A mem md O Lc Ac mc mdc Rc Oc bc (lp, z) ->
  call_pre B (aa_MR API) Lc Ac regs_c mc mdc ->
  S - K <= spZ regs_c - ALLOC_STACK -> spZ regs_c <= S -> 0 < z ->
  In (q, z) (user_blocks Ac) -> ptr_addr Lc q = lp -> getr regs_c 10 = Z_to_bv 64 lp ->
  st_init_done Ac = true ->
  (forall L' A' regs' m' md',
     sinv B API K S L A mem md O L' A' m' md' Rc Oc bc ->
     call_post_k B (aa_MR API) ALLOC_STACK Lc Ac regs_c mc mdc (fun a => lp <= a < lp + z) L' A' regs' m' md' ->
     sb_shift bc A A' = sb_free (sb_shift bc A Ac) z ->
     SR rsegs (mkCfg (mkst regs' (getr regs_c 1) m' (seg_rom rsegs)) md') P) ->
  SR rsegs (mkCfg (mkst regs_c (Z_to_bv 64 0x18ad0) mc (seg_rom rsegs)) mdc) P.
Proof using SEGS AX GOWN GFACT ERRNO_LOW GOTG GRD FREE_PC FREE.
  intros K S L A mem md O Lc Ac mc mdc Rc Oc bc q lp z regs_c P SI CP HLO HHI Hz HQ HLP E10 INIc KC.
  pose proof SI as (RJ & GR & ON & B1 & B2 & RA & F18 & RS & LIN & LNO & LOC).
  pose proof FREE as FRC. unfold free_contract in FRC. rewrite SEGS, FREE_PC in FRC.
  eapply SR_bind.
  { apply (FRC Lc Ac regs_c mc mdc q z (sb_shift bc A Ac));
      [exact CP | exact RA | exact HQ | rewrite HLP; exact E10 | exact RS]. }
  intros c' (L2 & A2 & R2 & m2 & md2 & -> & POST & BLK & BK & RA2 & GK & UB & INI & RGN & RS2).
  rewrite ?SEGS in RA2.
  rewrite HLP in POST, BLK, BK.
  pose proof (proj1 (call_post_k_alloc B (aa_MR API) Lc Ac regs_c mc mdc _ L2 A2 R2 m2 md2) POST) as POSTk.
  pose proof POSTk as (PM2 & _).
  destruct (ax_statics AX L2 A2 m2 md2 PM2) as (_ & (g & Hg & HWg) & _).
  rewrite GRD, SEGS in HWg.
  assert (F182 : f18_words rsegs m2).
  { apply (f18_words_after mc m2 g F18); [|exact Hg | exact HWg].
    intros i Hi. pose proof (GK i Hi) as G. rewrite GOTG, SEGS in G. exact G. }
  assert (SH : sb_shift bc A A2 = sb_free (sb_shift bc A Ac) z).
  { pose proof BLK as (l1 & l2 & E1 & E2).
    rewrite (sb_shift_del (sb_shift bc A Ac) Lc Ac L2 A2 l1 l2 lp z E1 E2). symmetry. apply sb_shift_trans. }
  apply (KC L2 A2 R2 m2 md2); [| exact POSTk | exact SH].
  exact (sinvx_free K S L A mem md O Lc Ac mc mdc Rc Oc bc q lp z ALLOC_STACK regs_c L2 A2 R2 m2 md2 SI HLO HHI Hz HQ HLP
           POSTk BLK BK UB (INI INIc) RGN RS2 RA2 F182).
Qed.

Hypothesis ARGS : arg_s_contract B API.

Lemma sinvx_arg_sn : forall K S L A mem md O Lc Ac mc mdc Rp fn As Oc bc lb regs_c s v (P : config -> Prop),
  sinvx K S L A mem md O Lc Ac mc mdc (rec_record Rp fn As) Oc bc lb -> (length As < 6)%nat ->
  YK0s.ret_ok (getr regs_c 1) -> spZ regs_c mod 16 = 0 -> S - K <= spZ regs_c - ARG_S_K -> spZ regs_c <= S ->
  getr regs_c 4 = Z_to_bv 64 (ms_tp B) ->
  getr regs_c 10 = Z_to_bv 64 (rec_entry G_REC REC_SC Rp) -> getr regs_c 11 = Z_to_bv 64 s ->
  arg_s_src B Lc Ac (spZ regs_c) mc s v ->
  room_ag (sb_malloc (sb_shift bc A Ac) (Z.of_nat (length (sarg v)) + 1)) (Z.of_nat (length (sarg v)) + 1) ->
  (forall L2 A2 regs2 m2 md2 p,
     sinvx K S L A mem md O L2 A2 m2 md2 (rec_record Rp fn (As ++ [sarg v]))
       (Oc ++ [(p, Z.of_nat (length (sarg v)) + 1)]) bc lb ->
     sb_shift bc A A2 = sb_malloc (sb_shift bc A Ac) (Z.of_nat (length (sarg v)) + 1) ->
     st_init_done A2 = true -> regs_preserved regs_c regs2 ->
     (forall a, spZ regs_c <= a < S ->
        mbyte rsegs m2 a = mbyte rsegs mc a /\ (writable_at rsegs mc a <-> writable_at rsegs m2 a)) ->
     SR rsegs (mkCfg (mkst regs2 (getr regs_c 1) m2 (seg_rom rsegs)) md2) P) ->
  SR rsegs (mkCfg (mkst regs_c (Z_to_bv 64 ARG_S) mc (seg_rom rsegs)) mdc) P.
Proof using SEGS AX GOWN GFACT ERRNO_LOW ARGS.
  intros K S L A mem md O Lc Ac mc mdc Rp fn As Oc bc lb regs_c s v P SI H6 Hra Hal Hlo Hhi Htp H10 H11 SRC ROOM KONT.
  pose proof alloc_ceiling_val as AC.
  pose proof SI as (RJ & GR & _ & _ & _ & RA & F18 & RS & _).
  destruct (rjr_bounds B _ K S rec_area _ L A mem md Lc Ac mc mdc RJ) as (HK1 & HK2 & HK3).
  assert (HN : (length (r_calls Rp) <= 16)%nat)
    by exact (rec_record_calls Rp fn As (rec_rep_calls_le _ _ _ _ _ _ _ _ GR)).
  destruct (rec_entry_bounds Rp HN) as (ER1 & ER2 & ER3).
  destruct (rec_entry_at rsegs Lc Ac mc Rp fn As Oc GR) as (P0 & CA).
  pose proof CA as (_ & _ & _ & _ & NA0 & _).
  destruct (sarg_facts B Lc Ac (spZ regs_c) mc s v SRC) as (NO & LX).
  set (e := rec_entry G_REC REC_SC Rp) in *.
  pose proof ARGS as ASC. unfold arg_s_contract in ASC. rewrite SEGS in ASC.
  eapply SR_bind.
  { apply (ASC Lc Ac regs_c mc mdc e s (Z.of_nat (length As)) v (sb_shift bc A Ac)).
    - apply (call_pre_k_of_rjr B _ K S rec_area _ L A mem md Lc Ac mc mdc ARG_S_K regs_c RJ Hra Hal);
        [unfold ARG_S_K, XMALLOC_K, ALLOC_STACK; lia | exact Hlo | exact Hhi | exact Htp].
    - exact H10.
    - exact H11.
    - exact ER3.
    - exact ER1.
    - exact ER2.
    - apply glob_wr_at; unfold GLOB_LO, GLOB_N, REC_SC, G_REC, REC_SIZE, CALL_SIZE in *; lia.
    - exact NA0.
    - lia.
    - exact SRC.
    - exact F18.
    - exact RS.
    - exact ROOM.
    - exact RA. }
  intros c2 (L2 & A2 & regs2 & m2 & md2 & -> & BK & UB & RA2 & GK & F182 & RGN &
    [(M6 & _) | (_ & p & POST & Hp0 & PAL & FB & BLK & NA2 & AS2 & BP & INI & RES2)]); [lia|].
  rewrite SEGS in NA2, AS2, BP, RA2, F182.
  pose proof POST as (PM & _ & _ & _ & _ & PR & _ & PF & _). rewrite SEGS in PF.
  assert (FK : forall a, spZ regs_c <= a < S ->
            mbyte rsegs m2 a = mbyte rsegs mc a /\ (writable_at rsegs mc a <-> writable_at rsegs m2 a)).
  { intros a Ha. pose proof (aa_laws API) as LAWS. pose proof RJ as (HM & _).
    pose proof FB as (FB1 & FB2 & _).
    unfold ARG_S_K, XMALLOC_K, ALLOC_STACK in Hlo.
    apply PF.
    - left. lia.
    - intros Ho. pose proof (mr_owned_low B _ LAWS Lc Ac mc mdc a HM Ho). lia.
    - intros Ho. pose proof (mr_owned_low B _ LAWS L2 A2 m2 md2 a PM Ho). lia.
    - unfold scratch_k. intros [H|H]; lia.
    - cbv beta. unfold CALL_OFF_NARGS, CALL_OFF_ARGS, REC_SC, G_REC, REC_SIZE, CALL_SIZE in *. lia. }
  pose proof BLK as (b1 & b2 & EB' & EB).
  assert (SI2 : sinvx K S L A mem md O L2 A2 m2 md2 (rec_record Rp fn (As ++ [sarg v]))
                  (Oc ++ [(p, Z.of_nat (length (sarg v)) + 1)]) bc lb).
  { apply (sinvx_arg K S L A mem md O Lc Ac mc mdc Rp fn As Oc bc lb ARG_S_K regs_c _ L2 A2 regs2 m2 md2 (sarg v) p
             (Z.of_nat (length (sarg v)) + 1) SI H6 Hlo Hhi POST).
    - intros a Ha. unfold CALL_OFF_NARGS, CALL_OFF_ARGS in *. lia.
    - exact Hp0.
    - exact FB.
    - exact BLK.
    - exact UB.
    - exact BK.
    - exact RGN.
    - exact NA2.
    - exact AS2.
    - exact BP.
    - exact NO.
    - exact LX.
    - lia.
    - exact INI.
    - exact RES2.
    - exact RA2.
    - exact F182. }
  rewrite SEGS. apply (KONT L2 A2 regs2 m2 md2 p SI2); [| exact INI | exact PR | exact FK].
  rewrite <- (sb_shift_trans bc A Ac A2). rewrite <- (sb_shift_add (sb_shift bc A Ac) Lc Ac L2 A2 b1 b2 p _ EB' EB).
  reflexivity.
Qed.

End X.

From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require sup_chain_c.

Lemma sch_bpre : forall b b1 k0 k1 k2 k3, sb_le b1 b -> 0 <= k0 ->
  sb_le (sb_free (sb_malloc (sb_malloc (sb_malloc (sb_malloc b1 k0) k1) k2) k3) k0) (sb_mallocs b [k0; k1; k2; k3]).
Proof.
  intros b b1 k0 k1 k2 k3 HB Hk. unfold sb_mallocs. cbn [fold_left].
  eapply sb_le_trans; [apply sb_free_le; exact Hk|].
  repeat apply sb_malloc_mono. exact HB.
Qed.

Lemma sch_mallocs_split : forall b id ids t,
  sb_mallocs b (CF.sup_chain_c.sup_chain_sizes id ids t) =
  sb_malloc (sb_malloc (sb_mallocs b [12 * Z.of_nat (length ids) + 1; Z.of_nat (length (dec id)) + 1;
                                      Z.of_nat (length (dec (Z.of_nat (length ids)))) + 1;
                                      Z.of_nat (length (dec_list ids)) + 1])
    (Z.of_nat (length t) + 1)) (Z.of_nat (length t) + 1).
Proof. intros b id ids t. reflexivity. Qed.

Section F.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis SEGS : ms_segs B = rsegs.
Hypothesis GOWN : forall L A mem md a, aa_MR API L A mem md -> in_globals frame_G a -> ~ owned B L A a.
Hypothesis AX : AllocExtra B (aa_MR API).

Lemma scu_list : sprintf_c.sprintf_contract ->
  forall K S L A mem md O Lc Ac mc mdc Rc Oc bc lp ids pids regs_c (P : config -> Prop),
  sinvx B API K S L A mem md O Lc Ac mc mdc Rc Oc bc (lp, 12 * Z.of_nat (length ids) + 1) ->
  m_halted mdc = None -> m_vm_lazy mdc = [] ->
  (1 <= length ids <= 62)%nat -> Forall (fun v => -2^31 <= v < 2^31) ids ->
  0 < pids -> pids mod 4 = 0 -> pids + 4 * Z.of_nat (length ids) <= TASK_SIZE ->
  (pids + 4 * Z.of_nat (length ids) <= S - K \/ spZ regs_c <= pids) ->
  (pids + 4 * Z.of_nat (length ids) <= lp \/ lp + 12 * Z.of_nat (length ids) + 1 <= pids) ->
  S - K <= spZ regs_c - sprintf_c.SPRINTF_K -> spZ regs_c <= S -> spZ regs_c <= TASK_SIZE ->
  (forall a, S - K <= a < spZ regs_c -> writable_at rsegs mc a) ->
  frm_zero fp_csr ->
  bytes_at rsegs mc pids (concat (map le32 ids)) ->
  getr regs_c 8 = Z_to_bv 64 pids -> getr regs_c 9 = Z_to_bv 64 (Z.of_nat (length ids)) ->
  getr regs_c 19 = Z_to_bv 64 lp -> getr regs_c 20 = Z_to_bv 64 0x10828 ->
  (forall (fx' : YK11.FPState) R' m', fp_kept fx fx' ->
     sinvx B API K S L A mem md O Lc Ac m' mdc Rc Oc bc (lp, 12 * Z.of_nat (length ids) + 1) ->
     bytes_at rsegs m' lp (dec_list ids ++ [Z_to_bv 8 0]) ->
     bytes_at rsegs m' pids (concat (map le32 ids)) ->
     munch [(S - K, spZ regs_c); (lp, lp + (12 * Z.of_nat (length ids) + 1))] mc m' -> wmono rsegs mc m' ->
     ro_agree rsegs m' ->
     getr R' 2 = getr regs_c 2 -> getr R' 3 = getr regs_c 3 -> getr R' 4 = getr regs_c 4 ->
     getr R' 19 = Z_to_bv 64 lp ->
     SR rsegs (mkCfg (@mkst fx' R' (Z_to_bv 64 0x16f48) m' (seg_rom rsegs)) mdc) P) ->
  SR rsegs (mkCfg (mkst regs_c (Z_to_bv 64 0x16ed0) mc (seg_rom rsegs)) mdc) P.
Proof using SEGS GOWN AX.
  intros SPR K S L A mem md O Lc Ac mc mdc Rc Oc bc lp ids pids regs_c P SI Hh Hl HN HF HP0 HP4 HP1 HPS HPL HLO HHI HTS
    HWS FZ HIDS A8 A9 A19 A20 KC.
  pose proof (aa_laws API) as LAWS. pose proof wx_apart_rsegs as WX.
  pose proof alloc_ceiling_value as (ACr & _). pose proof alloc_ceiling_lt as ACl.
  set (z := 12 * Z.of_nat (length ids) + 1) in *.
  pose proof SI as (RJ & GR & ON & B1 & B2 & RA & F18 & RS & LIN & LNO & LOC).
  pose proof RJ as (HM & _).
  destruct (rjr_bounds B _ K S rec_area _ L A mem md Lc Ac mc mdc RJ) as (HK1 & HK2 & HK3).
  destruct (sc_blk B API SEGS AX K S L A mem md O Lc Ac mc mdc Rc Oc bc lp z SI ltac:(unfold z; lia))
    as (IMG & _ & GD1 & GD2 & L0 & LC).
  pose proof LIN as LIN'. unfold blocks in LIN'. apply in_map_iff in LIN' as ([q z'] & Eq & HQ).
  cbn in Eq. injection Eq as HLP HZ'. subst z'.
  pose proof (block_facts B _ LAWS Lc Ac mc mdc lp z 0 HM LIN ltac:(unfold z; lia)) as (_ & LP4 & _).
  assert (NI : forall i, 0 <= i < z -> ~ in_img B (lp + i)).
  { intros i Hi. rewrite <- HLP. exact (ax_blocks_img AX Lc Ac mc mdc q z i HM HQ Hi). }
  assert (KEEP : forall i, 0 <= i < z -> cj_drop rsegs (Z_to_bv 64 (lp + i)) = false).
  { intros i Hi. destruct (cj_drop rsegs (Z_to_bv 64 (lp + i))) eqn:E; [|reflexivity]. exfalso.
    destruct (cj_drop_true rsegs _ E) as [Er | [_ Et]].
    - exact (NI i Hi (ro_in_img B SEGS (lp + i) ltac:(lia) Er)).
    - rewrite unsigned_lit in Et by lia. unfold TASK_SIZE in *. lia. }
  assert (PR : forall i, 0 <= i < z -> present mc (lp + i))
    by (intros i Hi; exact (proj1 (block_facts B _ LAWS Lc Ac mc mdc lp z i HM LIN Hi))).
  assert (MR0 : mem_rel_cj rsegs mc (normalize_cj rsegs mc)) by exact (mem_rel_cj_normalize rsegs mc RA).
  assert (WV : forall i, 0 <= i < z -> wview rsegs (normalize_cj rsegs mc) (Z_to_bv 64 (lp + i)) <> None).
  { intros i Hi. rewrite (wview_rel_cj rsegs mc _ _ MR0 (KEEP i Hi)). exact (present_writable rsegs mc _ (PR i Hi)). }
  assert (WR : wr_at rsegs (normalize_cj rsegs mc) lp 1).
  { split; [lia|]. split; [lia|]. intros i Hi. exact (WV i ltac:(unfold z; lia)). }
  assert (PRES : forall m', wmono rsegs (normalize_cj rsegs mc) m' -> forall i, 0 <= i < z -> present m' (lp + i)).
  { intros m' WM i Hi. apply (present_of_writable_out B SEGS); [lia | exact (NI i Hi) |]. apply WM. exact (WV i Hi). }
  pose proof F18 as (GG & canary & GW).
  assert (GGb : bytes_at rsegs mc snprintf_c.GOT_GUARD (le8 (Z_to_bv 64 snprintf_c.GUARD))).
  { destruct GG as [[_ Hb] _]. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb. }
  assert (GWb : bytes_at rsegs mc snprintf_c.GUARD (le8 canary)).
  { destruct GW as [[_ Hb] _]. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb. }
  pose proof (bytes_at_normalize_cj_low rsegs mc snprintf_c.GOT_GUARD (le8 (Z_to_bv 64 snprintf_c.GUARD)) RA
    ltac:(rewrite length_le8; unfold snprintf_c.GOT_GUARD, TASK_SIZE; lia) GGb) as GGn.
  pose proof (bytes_at_normalize_cj_low rsegs mc snprintf_c.GUARD (le8 canary) RA
    ltac:(rewrite length_le8; unfold snprintf_c.GUARD, TASK_SIZE; lia) GWb) as GWn.
  pose proof (bytes_at_normalize_cj_low rsegs mc pids (concat (map le32 ids)) RA
    ltac:(rewrite sc_ids_len; lia) HIDS) as HIDSn.
  set (sp := reg_get regs_c 2) in *.
  change (spZ regs_c) with (bv_unsigned sp) in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
  assert (ST0 : stk rsegs (normalize_cj rsegs mc) (S - K) (bv_unsigned sp))
    by (apply CF.RecAns.stk_normalize_cj; [unfold TASK_SIZE in *; lia | exact HTS | exact HWS]).
  set (Q := fun ms : machine_state => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (Ft : bvmap 5 word)
      (fc' : bv 32) (m' : word -> option byte),
      ms = MS (mkR (Z_to_bv 64 0x16f34) sp (reg_get regs_c 3) (reg_get regs_c 4) t0 t1 t2 (Z_to_bv 64 pids)
                   (Z_to_bv 64 (Z.of_nat (length ids))) a0 a1 a2 a3 a4 a5 a6 a7
                   (Z_to_bv 64 (pids + 4 * Z.of_nat (length ids))) (Z_to_bv 64 lp) (Z_to_bv 64 0x10828)
                   (Z_to_bv 64 (Z.of_nat (length ids))) (Z_to_bv 64 (Z.of_nat (length (dec_list ids))))
                   (Z_to_bv 64 (2 ^ 64 - 1 - lp)) (Z_to_bv 64 1) (Z_to_bv 64 1) (Z_to_bv 64 0x10738)
                   (Z_to_bv 64 (pids + 4 * Z.of_nat (length ids))) t3 t4 t5 t6)
              Ft (Z_to_bv 64 0x16f48) fc' None m' (seg_rom rsegs) /\
      munch [(S - K, bv_unsigned sp); (lp, lp + z)] (normalize_cj rsegs mc) m' /\
      wmono rsegs (normalize_cj rsegs mc) m' /\ frm0 fc' /\
      (forall r : reg, bv_unsigned r <> 10 -> reg_get Ft r = reg_get fp_regs r) /\
      bytes_at rsegs m' pids (concat (map le32 ids)) /\ bytes_at rsegs m' lp (dec_list ids ++ [Z_to_bv 8 0])).
  eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of. fold sp.
    assert (R8 : reg_get regs_c 8 = Z_to_bv 64 pids) by exact A8.
    assert (R9 : reg_get regs_c 9 = Z_to_bv 64 (Z.of_nat (length ids))) by exact A9.
    assert (R19 : reg_get regs_c 19 = Z_to_bv 64 lp) by exact A19.
    assert (R20 : reg_get regs_c 20 = Z_to_bv 64 0x10828) by exact A20.
    rewrite R8, R9, R19, R20.
    eapply (evt_normalize_cj rsegs); [exact WX | exact RA |].
    apply (scu_pre SPR Q ids) with (m0 := normalize_cj rsegs mc) (lo := S - K) (lst := lp) (pids := pids)
      (canary := canary);
      [exact HN | exact HF | exact HP0 | exact HP4 | unfold TASK_SIZE in *; lia | exact HPS | exact HPL | lia | unfold z in LC; lia
      | exact IMG | exact PRES | destruct GD1 as [G|G]; [left | right]; unfold z in G; lia
      | destruct GD2 as [G|G]; [left | right]; unfold z in G; lia
      | exact HLO | unfold snprintf_c.IMG_END; lia | lia | exact HTS
      | apply munch_refl | apply wmono_refl | exact WR | exact ST0 | exact FZ
      | exact (mem_inv_cj_inv rsegs _ (mem_inv_cj_normalize rsegs mc))
      | exact (mem_inv_cj_task rsegs _ (mem_inv_cj_normalize rsegs mc)) | exact GGn | exact GWn | exact HIDSn |].
    intros t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 Ft fc' m' MU WM ST' FRM' MI' TM' FK HI HL.
    apply evt_done. exists t0, t1, t2, a0, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, Ft, fc', m'.
    split; [reflexivity|].
    split; [replace (lp + z) with (lp + 12 * Z.of_nat (length ids) + 1) by (unfold z; ring); exact MU|].
    split; [exact WM|]. split; [exact FRM'|]. split; [exact FK|].
    split; [exact HI | exact HL]. }
  intros ms1 (can1 & (s1n & Q1 & REL1 & RO1) & EQ1).
  destruct Q1 as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & Ft & fc1 & m1n
    & -> & MU1n & WM1n & FRM1 & FK1 & HI1n & HL1n).
  destruct (CF.RecAns.ms_rel_cj_MS _ _ _ _ _ _ _ _ REL1) as [EC1 MR1r].
  revert EC1 MR1r RO1 EQ1. generalize (ms_mem can1) as m1. intros m1 EC1 MR1r RO1 EQ1. subst can1.
  pose proof (munch_rel_cj rsegs _ _ _ _ _ MR0 MR1r RO1 MU1n) as MU1.
  pose proof (wmono_rel_cj rsegs _ _ _ _ MR0 MR1r RO1 WM1n) as WM1.
  pose proof (ro_agree_same_cj rsegs _ _ RA RO1) as RA1.
  pose proof (bytes_at_rel_cj rsegs _ _ _ _ MR1r HI1n) as HI1.
  pose proof (bytes_at_rel_cj rsegs _ _ _ _ MR1r HL1n) as HL1.
  destruct (eqv_mkst_fx _ _ _ _ _ _ _ EQ1) as (R1 & -> & X1).
  pose proof (sinvx_heap B API SEGS GOWN AX K S L A mem md O Lc Ac mc mdc Rc Oc bc lp z m1 _ SI MU1 WM1
                ltac:(intros a Ra Hm; cbn in Hm; lia)) as SI1.
  apply (KC (mkFP Ft fc1) R1 m1); [| exact SI1 | exact HL1 | exact HI1 | exact MU1 | exact WM1 | exact RA1
    | rewrite (getr_of_eqv _ _ 2 X1 eq_refl); simp_regs; reflexivity
    | rewrite (getr_of_eqv _ _ 3 X1 eq_refl); simp_regs; reflexivity
    | rewrite (getr_of_eqv _ _ 4 X1 eq_refl); simp_regs; reflexivity
    | rewrite (getr_of_eqv _ _ 19 X1 eq_refl); simp_regs; reflexivity].
  unfold fp_kept. cbn [fp_regs fp_csr]. split; [exact FRM1|].
  intros r Hr. apply FK1. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32.
  unfold fs_saved in Hr. rewrite Z.mod_small by lia. lia.
Qed.

End F.
