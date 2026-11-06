(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/boost-beast/http_request/lib/Lib/Tac.v; 237 of its 261 lines of code are new or changed and 298 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/Prog/mread.v, with its module paths and numbers changed; 1088 of its 1116 lines of code are new or changed and 233 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/U/Prog/chain_words.v, with its module paths, addresses and numbers changed; 2641 of its 2742 lines of code are new or changed and 1015 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/Prog/sup_host_setting.v, with its module paths, module names, addresses and numbers changed; 1506 of its 1825 lines of code are new or changed and 2423 lines of the source are left out. *)
From Stdlib Require Import String ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import Tac Arr Bytes FP Image.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import Img0 AllocSlots.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel printf_facts_c arg_i RecKindB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM06 YL01.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import Contract.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecAnsB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import arg_i_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import xstrdup_c rec_calls_free_c answer_c rec_shape_of_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Regs6ss RegisterBridge.
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

Lemma sc_piece_pf : forall k v, -2^31 <= v < 2^31 ->
  sc_piece k v = pf_bytes (if Nat.eqb k 0 then pf_dec v else 32 :: pf_dec v).
Proof.
  intros k v Hv. unfold sc_piece. rewrite <- (ai_pf_dec v Hv).
  destruct (Nat.eqb k 0); reflexivity.
Qed.

Lemma sc_off_bound : forall ids k v, Forall (fun v => -2^31 <= v < 2^31) ids -> nth_error ids k = Some v ->
  (length (dec_list (firstn k ids)) + length (sc_piece k v) + 1 <= 12 * length ids + 1)%nat.
Proof.
  intros ids k v HF E. pose proof (sc_pref_len ids (S k) HF) as P. rewrite (sc_dec_list_step ids k v E) in P.
  rewrite length_app in P. assert (Hk : (k < length ids)%nat) by (apply nth_error_Some; congruence). lia.
Qed.

From Stdlib Require Import Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs Monad Specs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step ZBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05 YL0i YL01.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import Contract FrameAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecInv RecInvP.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecSeq RecStep RecGlue RecAnsB RecTail RecStub.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YO10.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require hand_back.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require sprintf_c snprintf_c RecAns.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require MemNorm.

Lemma sc_eqb : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 ->
  bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = Z.eqb x y.
Proof. intros x y Hx Hy. unfold bv_eqb. rewrite !unsigned_lit by lia. reflexivity. Qed.

Definition sc_fmt (k : nat) : list Z := if Nat.eqb k 0 then AI_FMT else SC_FMT1.
Definition sc_ps (k : nat) : list pf_piece := if Nat.eqb k 0 then AI_PS else SC_PS1.
Definition sc_txt (k : nat) (v : Z) : list Z := if Nat.eqb k 0 then pf_dec v else 32 :: pf_dec v.
Definition sc_fa (k : nat) : Z := if Nat.eqb k 0 then 0x10828 else 0x10738.

Definition sc_after (sp gp tp s0 s8 s9 s10 s11 : word) (F : bvmap 5 word)
    (lo lst pids o n v : Z) (k : nat) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s2 s4 s5 pc : word) (Ft : bvmap 5 word)
                    (fc' : bv 32) (m' : word -> option byte),
    ms' = MS (mkR (Z_to_bv 64 0x16c2c) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 n) a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 lst)
                  s4 s5 (Z_to_bv 64 0x10738) (Z_to_bv 64 0x10828) s8 s9 s10 s11 t3 t4 t5 t6)
             Ft pc fc' None m' (seg_rom rsegs) /\
    s2 = Z_to_bv 64 (pids + 4 * Z.of_nat (S k)) /\ s4 = Z_to_bv 64 (Z.of_nat (S k)) /\
    s5 = Z_to_bv 64 (o + Z.of_nat (length (sc_piece k v))) /\
    pc = Z_to_bv 64 (if Z.of_nat (S k) =? n then 0x16c3c else 0x16c14) /\
    munch [(lo, bv_unsigned sp); (lst + o, lst + o + Z.of_nat (length (sc_piece k v)) + 1)] m m' /\
    wmono rsegs m m' /\ mem_inv rsegs m' /\ MemNorm.task_mem rsegs m' /\ frm0 fc' /\
    (forall r : reg, bv_unsigned r <> 10 -> reg_get Ft r = reg_get F r) /\
    stk rsegs m' lo (bv_unsigned sp) /\
    bytes_at rsegs m' (lst + o) (sc_piece k v ++ [Z_to_bv 8 0]).

Lemma sc_call : sprintf_c.sprintf_contract ->
  forall ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo lst pids o n v : Z) (k : nat) (canary : word)
    (junk : list byte),
  -2^31 <= v < 2^31 -> Z.of_nat k < n <= 62 -> 0 <= pids -> pids + 4 * n <= 2 ^ 63 ->
  0 <= lst -> 0 <= o -> 0 < lst + o -> lst + o + Z.of_nat (length (sc_piece k v)) + 1 <= lo ->
  a1 = Z_to_bv 64 (sc_fa k) ->
  bytes_at rsegs m (pids + 4 * Z.of_nat k) (le4 (Z_to_bv 64 v)) ->
  rw_cells rsegs m (lst + o) [CB (S (length (sc_piece k v))) junk] ->
  pf_img_free (lst + o) (Z.of_nat (length (sc_piece k v)) + 1) ->
  stk rsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - sprintf_c.SPRINTF_K -> snprintf_c.IMG_END <= lo ->
  bv_unsigned sp < 2^63 ->
  frm0 fc -> mem_inv rsegs m -> MemNorm.task_mem rsegs m ->
  bytes_at rsegs m snprintf_c.GOT_GUARD (le8 (Z_to_bv 64 snprintf_c.GUARD)) ->
  bytes_at rsegs m snprintf_c.GUARD (le8 canary) ->
  evt rsegs (sc_after sp gp tp s0 s8 s9 s10 s11 F lo lst pids o n v k m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 n) a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (pids + 4 * Z.of_nat k))
             (Z_to_bv 64 lst) (Z_to_bv 64 (Z.of_nat k)) (Z_to_bv 64 o) (Z_to_bv 64 0x10738) (Z_to_bv 64 0x10828)
             s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x16c20) fc None m (seg_rom rsegs)).
Proof.
  intros SPR ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo lst pids o n v k
    canary junk HV HK HP0 HP1 HL0 HO0 HD0 HDL -> HR BUF IMGF ST LO IE S63 FRM MI TM GG GW.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  unfold sprintf_c.SPRINTF_K, snprintf_c.IMG_END in *.
  pose proof (dec_length v HV) as DL.
  pose proof (sc_piece_pf k v HV) as PP.
  assert (TL : length (sc_piece k v) = length (sc_txt k v)).
  { rewrite PP. unfold pf_bytes, sc_txt. rewrite length_map. reflexivity. }
  pose proof (sc_piece_length k v HV) as PL.
  assert (FA : 0x10738 <= sc_fa k <= 0x10828) by (unfold sc_fa; destruct (Nat.eqb k 0); lia).
  pose proof (ai_rd4 m (pids + 4 * Z.of_nat k) _ HR) as RD.
  step. rewrite ai_sx32 by lia. step. step.
  eapply evt_cut.
  { eapply (SPR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo canary (sc_fmt k) (sc_ps k)
              [AInt v] (sc_txt k v) junk).
    - rewrite unsigned_lit by lia. unfold sc_fa, sc_fmt. destruct (Nat.eqb k 0); [apply ai_fmt_at | apply sc_fmt1_at];
        exact MI.
    - rewrite unsigned_lit by lia. unfold snprintf_c.RO_LO. lia.
    - rewrite unsigned_lit by lia. unfold snprintf_c.RO_END, sc_fa, sc_fmt, AI_FMT, SC_FMT1.
      destruct (Nat.eqb k 0); cbn [length]; lia.
    - unfold sc_fmt, sc_ps. destruct (Nat.eqb k 0); reflexivity.
    - cbn [pf_args_ok pf_arg_ok]. split; [|exact I]. split; [exact HV | apply RecAns.lit_mod32].
    - unfold sc_ps, sc_txt. destruct (Nat.eqb k 0); [exact (ai_text v) | exact (sc_text1 v)].
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
  replace (ret_pc (Z_to_bv 64 0x16c2c)) with (Z_to_bv 64 0x16c2c) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  step. step. step. step.
  apply evt_done. unfold sc_after.
  do 19 eexists. exists Ft, fc', m2.
  split; [reflexivity|].
  split; [apply bv_eq; rewrite !unsigned_lit by lia; lia|].
  split; [apply bv_eq; rewrite !unsigned_lit by lia; lia|].
  split; [apply bv_eq; rewrite !unsigned_lit by lia; lia|].
  split.
  { rewrite sc_eqb by lia.
    repeat match goal with |- context [Z.eqb ?x ?y] => destruct (Z.eqb_spec x y) end; cbn [negb];
      first [reflexivity | exfalso; lia]. }
  rewrite TL. split; [exact MU2|]. split; [exact WM2|]. split; [exact MI2|]. split; [exact TM2|].
  split; [exact FRM2|]. split; [exact FK|]. split; [exact ST2|].
  rewrite PP. unfold pf_bytes in BT |- *. rewrite map_app in BT. exact BT.
Qed.

Lemma sc_body : sprintf_c.sprintf_contract ->
  forall ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo lst pids o n v : Z) (k : nat) (canary : word)
    (junk : list byte),
  -2^31 <= v < 2^31 -> Z.of_nat k < n <= 62 -> 0 <= pids -> pids + 4 * n <= 2 ^ 63 ->
  0 <= lst -> 0 <= o -> 0 < lst + o -> lst + o + Z.of_nat (length (sc_piece k v)) + 1 <= lo ->
  bytes_at rsegs m (pids + 4 * Z.of_nat k) (le4 (Z_to_bv 64 v)) ->
  rw_cells rsegs m (lst + o) [CB (S (length (sc_piece k v))) junk] ->
  pf_img_free (lst + o) (Z.of_nat (length (sc_piece k v)) + 1) ->
  stk rsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - sprintf_c.SPRINTF_K -> snprintf_c.IMG_END <= lo ->
  bv_unsigned sp < 2^63 ->
  frm0 fc -> mem_inv rsegs m -> MemNorm.task_mem rsegs m ->
  bytes_at rsegs m snprintf_c.GOT_GUARD (le8 (Z_to_bv 64 snprintf_c.GUARD)) ->
  bytes_at rsegs m snprintf_c.GUARD (le8 canary) ->
  evt rsegs (sc_after sp gp tp s0 s8 s9 s10 s11 F lo lst pids o n v k m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 n) a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (pids + 4 * Z.of_nat k))
             (Z_to_bv 64 lst) (Z_to_bv 64 (Z.of_nat k)) (Z_to_bv 64 o) (Z_to_bv 64 0x10738) (Z_to_bv 64 0x10828)
             s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x16c14) fc None m (seg_rom rsegs)).
Proof.
  intros SPR ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo lst pids o n v k
    canary junk HV HK HP0 HP1 HL0 HO0 HD0 HDL HR BUF IMGF ST LO IE S63 FRM MI TM GG GW.
  step. step.
  rewrite sc_eqb by lia.
  destruct (Z.eqb_spec (Z.of_nat k) 0) as [K0|K0]; cbv iota.
  - eapply sc_call; try eassumption. unfold sc_fa. replace k with 0%nat by lia. reflexivity.
  - step. eapply sc_call; try eassumption. unfold sc_fa. destruct (Nat.eqb_spec k 0); [lia | reflexivity].
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

Lemma sc_loop : sprintf_c.sprintf_contract ->
  forall (Q : machine_state -> Prop) (ids : list Z) sp gp tp s0 s8 s9 s10 s11 (F0 : bvmap 5 word)
    (m0 : word -> option byte) (lo lst pids : Z) (canary : word) (d : nat)
    ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : word -> option byte) (k : nat),
  d = (length ids - k)%nat -> (k < length ids)%nat -> (length ids <= 62)%nat ->
  Forall (fun v => -2^31 <= v < 2^31) ids ->
  0 <= pids -> pids + 4 * Z.of_nat (length ids) <= 2 ^ 63 ->
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
  (forall t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (Ft : bvmap 5 word) (fc' : bv 32) (m' : word -> option byte),
     munch [(lo, bv_unsigned sp); (lst, lst + 12 * Z.of_nat (length ids) + 1)] m0 m' -> wmono rsegs m0 m' ->
     stk rsegs m' lo (bv_unsigned sp) -> frm0 fc' -> mem_inv rsegs m' -> MemNorm.task_mem rsegs m' ->
     (forall r : reg, bv_unsigned r <> 10 -> reg_get Ft r = reg_get F0 r) ->
     bytes_at rsegs m' pids (concat (map le32 ids)) ->
     bytes_at rsegs m' lst (dec_list ids ++ [Z_to_bv 8 0]) ->
     evt rsegs Q (MS (mkR (Z_to_bv 64 0x16c2c) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 (Z.of_nat (length ids)))
                        a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (pids + 4 * Z.of_nat (length ids))) (Z_to_bv 64 lst)
                        (Z_to_bv 64 (Z.of_nat (length ids))) (Z_to_bv 64 (Z.of_nat (length (dec_list ids))))
                        (Z_to_bv 64 0x10738) (Z_to_bv 64 0x10828) s8 s9 s10 s11 t3 t4 t5 t6)
                     Ft (Z_to_bv 64 0x16c3c) fc' None m' (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 (Z.of_nat (length ids))) a0 a1 a2 a3 a4 a5 a6 a7
                     (Z_to_bv 64 (pids + 4 * Z.of_nat k)) (Z_to_bv 64 lst) (Z_to_bv 64 (Z.of_nat k))
                     (Z_to_bv 64 (Z.of_nat (length (dec_list (firstn k ids))))) (Z_to_bv 64 0x10738)
                     (Z_to_bv 64 0x10828) s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x16c14) fc None m (seg_rom rsegs)).
Proof.
  intros SPR Q ids sp gp tp s0 s8 s9 s10 s11 F0 m0 lo lst pids canary d.
  induction d as [|d IH];
    intros ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m k Hd Hk HN HF HP0 HP1 HPS HPL HL0 HLlo IMG PRES
      GD1 GD2 LO IE S63 FF MU0 WM0 ST FRM MI TM GG GW HIDS BL K; [lia|].
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
  { eapply (sc_body SPR ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo lst pids o
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
  intros ms' (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & s2' & s4' & s5'
    & pc' & Ft & fc' & m' & -> & -> & -> & -> & -> & MU & WM & MI' & TM' & FRM' & FK & ST' & BT).
  assert (MU' : munch [(lo, bv_unsigned sp); (lst, lst + 12 * Z.of_nat (length ids) + 1)] m0 m').
  { eapply munch_trans; [exact MU0|]. eapply munch_weaken; [|exact MU].
    unfold sub_fp. cbn [outside]. intros x (H1 & H2 & _). split; [lia | split; [lia | exact I]]. }
  assert (WM' : wmono rsegs m0 m') by (eapply wmono_trans; eassumption).
  assert (FK' : forall r : reg, bv_unsigned r <> 10 -> reg_get Ft r = reg_get F0 r).
  { intros r Hr. rewrite (FK r Hr). exact (FF r Hr). }
  assert (HIDS' : bytes_at rsegs m' pids (concat (map le32 ids))).
  { apply (bytes_at_transport rsegs _ m m' _ _ HIDS MU). cbn [disjoint_from]. rewrite IL.
    repeat (split; [lia|]); try exact I. }
  assert (GG' : bytes_at rsegs m' 0x22a68 (le8 (Z_to_bv 64 0x54450))).
  { apply (bytes_at_transport rsegs _ m m' _ _ GG MU). cbn [disjoint_from]. rewrite length_le8.
    repeat (split; [lia|]); try exact I. }
  assert (GW' : bytes_at rsegs m' 0x54450 (le8 canary)).
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
  - replace (Z_to_bv 64 (if Z.of_nat (S k) =? Z.of_nat (length ids) then 0x16c3c else 0x16c14)) with (Z_to_bv 64 0x16c3c)
      by (replace (Z.of_nat (S k) =? Z.of_nat (length ids)) with true by (symmetry; apply Z.eqb_eq; lia); reflexivity).
    rewrite Ek, firstn_all. rewrite Ek, firstn_all in BL'.
    exact (K t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' Ft fc' m' MU' WM' ST' FRM' MI' TM' FK' HIDS' BL').
  - replace (Z_to_bv 64 (if Z.of_nat (S k) =? Z.of_nat (length ids) then 0x16c3c else 0x16c14)) with (Z_to_bv 64 0x16c14)
      by (replace (Z.of_nat (S k) =? Z.of_nat (length ids)) with false by (symmetry; apply Z.eqb_neq; lia); reflexivity).
    apply (IH _ t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' Ft fc' m' (S k) ltac:(lia) ltac:(lia) HN HF
             HP0 HP1 HPS HPL HL0 HLlo IMG PRES GD1 GD2 LO IE S63 FK' MU' WM' ST' FRM' MI' TM' GG' GW' HIDS' BL' K).
Qed.

Lemma sc_pre : sprintf_c.sprintf_contract ->
  forall (Q : machine_state -> Prop) (ids : list Z) ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11
    t3 t4 t5 t6 (F : bvmap 5 word) fc (m0 m : word -> option byte) (lo lst pids : Z) (canary : word),
  (1 <= length ids <= 62)%nat -> Forall (fun v => -2^31 <= v < 2^31) ids ->
  0 <= pids -> pids + 4 * Z.of_nat (length ids) <= 2 ^ 63 ->
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
     evt rsegs Q (MS (mkR (Z_to_bv 64 0x16c2c) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 (Z.of_nat (length ids)))
                        a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (pids + 4 * Z.of_nat (length ids))) (Z_to_bv 64 lst)
                        (Z_to_bv 64 (Z.of_nat (length ids))) (Z_to_bv 64 (Z.of_nat (length (dec_list ids))))
                        (Z_to_bv 64 0x10738) (Z_to_bv 64 0x10828) s8 s9 s10 s11 t3 t4 t5 t6)
                     Ft (Z_to_bv 64 0x16c3c) fc' None m' (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 (Z.of_nat (length ids))) a0 a1 a2 a3 a4 a5 a6 a7
                     (Z_to_bv 64 pids) (Z_to_bv 64 lst) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x16bf4) fc None m (seg_rom rsegs)).
Proof.
  intros SPR Q ids ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m0 m
    lo lst pids canary HN HF HP0 HP1 HPS HPL HL0 HLlo IMG PRES GD1 GD2 LO IE S63 HTS MU0 WM0 WR ST FRM MI TM GG GW HIDS K.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  unfold sprintf_c.SPRINTF_K, snprintf_c.IMG_END, snprintf_c.GOT_GUARD, snprintf_c.GUARD in *.
  pose proof (sc_ids_len ids) as IL.
  assert (SO : store_ok rsegs m (wa (lst + 0)) 1 = true) by (apply (wr_at_store_ok rsegs m lst 1 0 1 WR); lia).
  step.
  match goal with |- context [write_to_mem m ?aa ?bs] =>
    replace (write_to_mem m aa bs) with (write_to_mem m (wa lst) [Z_to_bv 8 0])
      by (f_equal; try (unfold wa; f_equal; lia); try lia; try reflexivity; try (vm_compute; reflexivity)) end.
  step. rewrite ?ai_lts by lia.
  match goal with |- context [Z.ltb ?x ?y] => destruct (Z.ltb_spec x y) end; cbn [negb]; try (exfalso; lia).
  do 6 step.
  replace (Z_to_bv 64 pids) with (Z_to_bv 64 (pids + 4 * Z.of_nat 0)) by (f_equal; lia).
  assert (WL : 0 <= lst /\ lst + Z.of_nat (length [Z_to_bv 8 0]) <= 2 ^ 64) by (cbn [length]; lia).
  eapply (sc_loop SPR Q ids sp gp tp s0 s8 s9 s10 s11 F m0 lo lst pids canary (length ids)) with (k := 0%nat).
  all: try assumption; try lia; try (intros; reflexivity).
  - apply munch_write; [exact MU0 | lia | cbn [length]; lia | cbn [inside]; right; left; cbn [length]; lia].
  - apply wmono_write. exact WM0.
  - apply stk_write; [exact ST | lia | cbn [length]; lia].
  - apply mem_inv_store; [exact MI|]. rewrite Z.add_0_r in SO. exact SO.
  - apply (RecAns.task_mem_munch1 m _ lst (lst + 1) TM); [|lia].
    apply munch_write; [apply munch_refl | lia | cbn [length]; lia | cbn [inside]; left; cbn [length]; lia].
  - apply bytes_at_write_other; [exact GG | lia | cbn [length]; lia |].
    rewrite length_le8. cbn [length]. unfold snprintf_c.GOT_GUARD, snprintf_c.GUARD. lia.
  - apply bytes_at_write_other; [exact GW | lia | cbn [length]; lia |].
    rewrite length_le8. cbn [length]. unfold snprintf_c.GOT_GUARD, snprintf_c.GUARD. lia.
  - apply bytes_at_write_other; [exact HIDS | lia | cbn [length]; lia | rewrite IL; cbn [length]; lia].
  - change (dec_list (firstn 0 ids) ++ [Z_to_bv 8 0]) with [Z_to_bv 8 0].
    apply bytes_at_write_same; [lia | cbn [length]; lia].
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
      { exact (hand_back.hb_assoc_nd (user_blocks Ac) q n0 z (user_block_ptrs_NoDup Ac HWc) HAc HQ). }
      subst n0. apply H. rewrite <- (hand_back.hb_ptr_le A L Lc q z HWA HA HLc), HLP. apply LNO.
      unfold blocks. apply in_map_iff. exists (q, z). split; [|exact HA]. cbn.
      rewrite <- HLP, (hand_back.hb_ptr_le A L Lc q z HWA HA HLc). reflexivity.
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
      + destruct (hand_back.hb_pw_in2 _ _ _ _ (mr_blocks_disjoint B _ LAWS Lc Ac mc mdc HM) Hb LIN NE) as [D|D];
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
      destruct (hand_back.hb_pw_in2 _ _ _ _ (mr_blocks_disjoint B _ LAWS Lc Ac mc mdc HM) Hb LIN NE) as [D|D];
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

Hypothesis MALLOC_PC : ms_malloc B = 0x18a0c.
Hypothesis GOTG : ms_got_guard B = 0x22a68.
Hypothesis GRD : ms_guard B = 0x54450.
Hypothesis MALLOC : malloc_contract B API.

Lemma sch_malloc : forall K S L A mem md O Lc Ac mc mdc Rc Oc bc regs_c z (P : config -> Prop),
  sinv B API K S L A mem md O Lc Ac mc mdc Rc Oc bc ->
  call_pre B (aa_MR API) Lc Ac regs_c mc mdc ->
  S - K <= spZ regs_c - ALLOC_STACK -> spZ regs_c <= S ->
  getr regs_c 10 = Z_to_bv 64 z -> 0 < z -> room_slots (sb_shift bc A Ac) z ->
  (forall L' A' regs' m' md' p,
     sinvx K S L A mem md O L' A' m' md' Rc Oc bc (p, z) ->
     call_post_k B (aa_MR API) ALLOC_STACK Lc Ac regs_c mc mdc (fun _ => False) L' A' regs' m' md' ->
     getr regs' 10 = Z_to_bv 64 p -> p <> 0 -> fresh_block B p z ->
     sb_shift bc A A' = sb_malloc (sb_shift bc A Ac) z ->
     SR rsegs (mkCfg (mkst regs' (getr regs_c 1) m' (seg_rom rsegs)) md') P) ->
  SR rsegs (mkCfg (mkst regs_c (Z_to_bv 64 0x18a0c) mc (seg_rom rsegs)) mdc) P.
Proof using SEGS AX GOWN GFACT ERRNO_LOW MALLOC_PC GOTG GRD MALLOC.
  intros K S L A mem md O Lc Ac mc mdc Rc Oc bc regs_c z P SI CP HLO HHI E10 Hz ROOM KC.
  pose proof SI as (RJ & GR & ON & B1 & B2 & RA & F18 & RS).
  pose proof MALLOC as MAL. unfold malloc_contract in MAL. rewrite SEGS, MALLOC_PC in MAL.
  eapply SR_bind.
  { apply (MAL Lc Ac regs_c mc mdc z (sb_shift bc A Ac)); [exact CP | exact RA | exact E10 | exact RS | exact ROOM]. }
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
  exact (sinvx_malloc K S L A mem md O Lc Ac mc mdc Rc Oc bc ALLOC_STACK regs_c L2 A2 R2 m2 md2 p z SI HLO HHI POST Hz FB
           BLK UB BK RGN INI RS2 RA2 F182).
Qed.

Hypothesis FREE_PC : ms_free B = 0x188cc.
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
  SR rsegs (mkCfg (mkst regs_c (Z_to_bv 64 0x188cc) mc (seg_rom rsegs)) mdc) P.
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

Hypothesis ARGI : arg_i_contract B API.

Lemma sch_argi : forall K S L A mem md O Lc Ac mc mdc Rp fn As Oc bc lb regs_c v (P : config -> Prop),
  sinvx K S L A mem md O Lc Ac mc mdc (rec_record Rp fn As) Oc bc lb ->
  (length As < 6)%nat ->
  call_pre_t B API ARG_I_K Lc Ac regs_c mc mdc ->
  S - K <= spZ regs_c - ARG_I_K -> spZ regs_c <= S ->
  getr regs_c 10 = Z_to_bv 64 (rec_entry G_REC REC_SC Rp) -> getr regs_c 11 = Z_to_bv 64 v -> -2^31 <= v < 2^31 ->
  rec_entry G_REC REC_SC Rp mod 8 = 0 -> REC_SC <= rec_entry G_REC REC_SC Rp ->
  rec_entry G_REC REC_SC Rp + CALL_SIZE <= G_REC + REC_SIZE ->
  wr_at rsegs mc (rec_entry G_REC REC_SC Rp) CALL_SIZE ->
  bytes_at rsegs mc (rec_entry G_REC REC_SC Rp + CALL_OFF_NARGS) (le4 (Z_to_bv 64 (Z.of_nat (length As)))) ->
  frm_zero fp_csr ->
  room_slots (sb_malloc (sb_shift bc A Ac) (Z.of_nat (length (dec v)) + 1)) (Z.of_nat (length (dec v)) + 1) ->
  (forall (fx' : YK11.FPState) L' A' regs' m' md' p, fp_kept fx fx' ->
     sinvx K S L A mem md O L' A' m' md' (rec_record Rp fn (As ++ [dec v]))
       (Oc ++ [(p, Z.of_nat (length (dec v)) + 1)]) bc lb ->
     call_post_k B (aa_MR API) ARG_I_K Lc Ac regs_c mc mdc
       (fun a => rec_entry G_REC REC_SC Rp + CALL_OFF_NARGS <= a < rec_entry G_REC REC_SC Rp + CALL_OFF_NARGS + 4 \/
                 rec_entry G_REC REC_SC Rp + CALL_OFF_ARGS + 8 * Z.of_nat (length As) <= a <
                   rec_entry G_REC REC_SC Rp + CALL_OFF_ARGS + 8 * Z.of_nat (length As) + 8 \/
                 p <= a < p + Z.of_nat (length (dec v)) + 1) L' A' regs' m' md' ->
     sb_shift bc A A' = sb_malloc (sb_shift bc A Ac) (Z.of_nat (length (dec v)) + 1) ->
     SR rsegs (mkCfg (@mkst fx' regs' (getr regs_c 1) m' (seg_rom rsegs)) md') P) ->
  SR rsegs (mkCfg (mkst regs_c (Z_to_bv 64 0x15b1c) mc (seg_rom rsegs)) mdc) P.
Proof using SEGS AX GOWN GFACT ERRNO_LOW ARGI.
  intros K S L A mem md O Lc Ac mc mdc Rp fn As Oc bc lb regs_c v P SI H6 CP HLO HHI E10 E11 HV EM ES EE WR NA FRM
    ROOM KC.
  pose proof SI as (RJ & GR & ON & B1 & B2 & RA & F18 & RS & LIN & LNO & LOC).
  pose proof (dec_length v HV) as DL.
  pose proof ARGI as AI. unfold arg_i_contract in AI. rewrite SEGS in AI.
  eapply SR_bind.
  { apply (AI Lc Ac regs_c mc mdc (rec_entry G_REC REC_SC Rp) v (Z.of_nat (length As)) (sb_shift bc A Ac));
      [exact CP | exact E10 | exact E11 | exact HV | exact EM | exact ES | exact EE | exact WR | exact NA | lia
      | exact F18 | exact FRM | exact RS | exact ROOM | exact RA]. }
  intros c' (fx' & L2 & A2 & R2 & m2 & md2 & -> & FK & BK & UB & BV & RA2 & GK & F182 & RGN & ALT).
  destruct ALT as [(H6' & _) | (_ & p & POST & NZ & AL16 & FB & BLK & BN & BS & BX & INI & RS2)]; [lia|].
  rewrite ?SEGS in RA2, F182, BN, BS, BX |- *.
  assert (SH : sb_shift bc A A2 = sb_malloc (sb_shift bc A Ac) (Z.of_nat (length (dec v)) + 1)).
  { pose proof BLK as (l1 & l2 & E1 & E2).
    rewrite (sb_shift_add (sb_shift bc A Ac) Lc Ac L2 A2 l1 l2 p _ E1 E2). symmetry. apply sb_shift_trans. }
  apply (KC fx' L2 A2 R2 m2 md2 p FK); [| exact POST | exact SH].
  apply (sinvx_arg K S L A mem md O Lc Ac mc mdc Rp fn As Oc bc lb ARG_I_K regs_c _ L2 A2 R2 m2 md2 (dec v) p
           (Z.of_nat (length (dec v)) + 1) SI H6 HLO HHI POST);
    [intros a [Ha|[Ha|Ha]]; [left; exact Ha | right; left; exact Ha | right; right; lia]
    | exact NZ | exact FB | exact BLK | exact UB | exact BK | exact RGN | exact BN | exact BS
    | exact BX | exact (dec_no0 v) | unfold LMAX; lia | unfold LMAX; lia | exact INI | exact RS2 | exact RA2 | exact F182].
Qed.

Hypothesis SLACK : block_slack_present B API.
Hypothesis XSD : xstrdup_contract B API.

Lemma sch_xsd : forall K S L A mem md O Lc Ac mc mdc Rc Oc bc lp z regs_c x (P : config -> Prop),
  sinvx K S L A mem md O Lc Ac mc mdc Rc Oc bc (lp, z) ->
  call_pre_k B (aa_MR API) XSTRDUP_K Lc Ac regs_c mc mdc ->
  S - K <= spZ regs_c - XSTRDUP_K -> spZ regs_c <= S ->
  getr regs_c 10 = Z_to_bv 64 lp ->
  bytes_at rsegs mc lp (x ++ [Z_to_bv 8 0]) -> no0 x -> Z.of_nat (length x) <= LMAX ->
  Z.of_nat (length x) + 1 <= z ->
  room_slots (sb_malloc (sb_shift bc A Ac) (Z.of_nat (length x) + 1)) (Z.of_nat (length x) + 1) ->
  (forall L' A' regs' m' md' p,
     call_post_k B (aa_MR API) XSTRDUP_K Lc Ac regs_c mc mdc (fun a => p <= a < p + Z.of_nat (length x) + 1)
       L' A' regs' m' md' ->
     getr regs' 10 = Z_to_bv 64 p -> p <> 0 -> fresh_block B p (Z.of_nat (length x) + 1) ->
     (exists b1 b2, blocks L' A' = b1 ++ (p, Z.of_nat (length x) + 1) :: b2 /\ blocks Lc Ac = b1 ++ b2) ->
     (forall q n, In (q, n) (user_blocks Ac) -> In (q, n) (user_blocks A')) ->
     blocks_kept B Lc Ac mc m' (fun _ => False) ->
     (length (st_regions Ac) <= length (st_regions A'))%nat ->
     bytes_at rsegs m' p (x ++ [Z_to_bv 8 0]) ->
     st_init_done A' = true ->
     res_ok_slots A' (sb_malloc (sb_shift bc A Ac) (Z.of_nat (length x) + 1)) ->
     ro_agree rsegs m' -> f18_words rsegs m' ->
     SR rsegs (mkCfg (mkst regs' (getr regs_c 1) m' (seg_rom rsegs)) md') P) ->
  SR rsegs (mkCfg (mkst regs_c (Z_to_bv 64 0x15780) mc (seg_rom rsegs)) mdc) P.
Proof using SEGS AX GOWN GFACT ERRNO_LOW GOTG GRD SLACK XSD.
  intros K S L A mem md O Lc Ac mc mdc Rc Oc bc lp z regs_c x P SI CP HLO HHI E10 BX N0 LX HZ ROOM KC.
  pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_val as AC.
  pose proof SI as (RJ & GR & ON & B1 & B2 & RA & F18 & RS & LIN & LNO & LOC).
  pose proof RJ as (HM & _).
  destruct (rjr_bounds B _ K S rec_area _ L A mem md Lc Ac mc mdc RJ) as (HK1 & HK2 & HK3).
  pose proof (block_facts B _ LAWS Lc Ac mc mdc lp z 0 HM LIN ltac:(lia)) as (_ & Q1 & Q2 & _).
  assert (PD : 0 <= (- (lp + Z.of_nat (length x) + 1)) mod 8 < 8) by (apply Z.mod_pos_bound; lia).
  assert (PB : lp + Z.of_nat (length x) + 1 + (- (lp + Z.of_nat (length x) + 1)) mod 8 <= 8 * ((lp + z + 7) / 8))
    by (Z.div_mod_to_equations; lia).
  assert (CB : 8 * ((lp + z + 7) / 8) <= alloc_ceiling).
  { pose proof alloc_ceiling_value as (_ & AM). Z.div_mod_to_equations. lia. }
  set (pad := (- (lp + Z.of_nat (length x) + 1)) mod 8) in *.
  destruct (rs_bytes_pad rsegs mc lp (x ++ [Z_to_bv 8 0]) (Z.to_nat pad) BX) as (sl & SL & BS').
  { rewrite length_app. cbn [length]. lia. }
  { intros j Hj. rewrite length_app. cbn [length].
    assert (PRc : present mc (lp + Z.of_nat (length x + 1) + Z.of_nat j)).
    { destruct (Z_lt_ge_dec (lp + Z.of_nat (length x + 1) + Z.of_nat j) (lp + z)) as [Hlt|Hge].
      - replace (lp + Z.of_nat (length x + 1) + Z.of_nat j) with (lp + (Z.of_nat (length x + 1) + Z.of_nat j)) by ring.
        exact (proj1 (block_facts B _ LAWS Lc Ac mc mdc lp z (Z.of_nat (length x + 1) + Z.of_nat j) HM LIN ltac:(lia))).
      - apply (SLACK Lc Ac mc mdc lp z _ HM LIN). lia. }
    destruct PRc as [bb E]. unfold mbyte. rewrite E. discriminate. }
  rewrite <- app_assoc in BS'. cbn [app] in BS'.
  pose proof XSD as XS. unfold xstrdup_contract in XS. rewrite SEGS in XS.
  eapply SR_bind.
  { apply (XS Lc Ac regs_c mc mdc lp x sl (sb_shift bc A Ac)).
    - exact CP.
    - exact E10.
    - exact BS'.
    - exact N0.
    - exact LX.
    - rewrite SL. fold pad. lia.
    - left. rewrite length_app. cbn [length]. rewrite SL. lia.
    - unfold str_home. right. left. exists lp, z. split; [exact LIN | lia].
    - exact RS.
    - exact ROOM.
    - exact RA. }
  intros c' (L2 & A2 & R2 & m2 & md2 & p & -> & POST & A0' & NZ & AL16 & FB & BLK & BK & UB & BP & BSRC & RA2 & GK & INI
    & RGN & RS2).
  rewrite ?SEGS in RA2, BP |- *.
  pose proof POST as (PM2 & _).
  destruct (ax_statics AX L2 A2 m2 md2 PM2) as (_ & (g & Hg & HWg) & _).
  rewrite GRD, SEGS in HWg.
  assert (F182 : f18_words rsegs m2).
  { apply (f18_words_after mc m2 g F18); [|exact Hg | exact HWg].
    intros i Hi. pose proof (GK i Hi) as G. rewrite GOTG, SEGS in G. exact G. }
  exact (KC L2 A2 R2 m2 md2 p POST A0' NZ FB BLK UB BK RGN BP INI RS2 RA2 F182).
Qed.

Hypothesis CTX : ctx_owned B API.
Hypothesis RCF : rec_calls_free_contract B API.
Hypothesis ANSF : forall fx0 : YK11.FPState, answer_contract (fx := fx0) B API.
Hypothesis RSO : rec_shape_of_contract.
Hypothesis SPRINTF : sprintf_c.sprintf_contract.
Hypothesis RIMG : forall a, in_globals frame_RELRO a ->
  in_img B a /\ ~ static_owned B a /\ ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\
  ~ (errno_addr B <= a < errno_addr B + 4).
Hypothesis RFREE : forall L A mem md a, aa_MR API L A mem md -> in_globals frame_RELRO a -> ~ owned B L A a.

End X.

From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require sup_chain_c.

Lemma sch_bpre : forall b b1 k0 k1 k2 k3, sb_le b1 b -> 0 <= k0 ->
  sb_le (sb_free (sb_malloc (sb_malloc (sb_malloc (sb_malloc b1 k0) k1) k2) k3) k0) (sb_mallocs b [k0; k1; k2; k3]).
Proof.
  intros b b1 k0 k1 k2 k3 HB Hk. unfold sb_mallocs. cbn [fold_left].
  eapply sb_le_trans; [apply sb_free_le; exact Hk|].
  repeat apply sb_malloc_mono. exact HB.
Qed.

Lemma sch_mallocs_split : forall b id ids t,
  sb_mallocs b (sup_chain_c.sup_chain_sizes id ids t) =
  sb_malloc (sb_malloc (sb_mallocs b [12 * Z.of_nat (length ids) + 1; Z.of_nat (length (dec id)) + 1;
                                      Z.of_nat (length (dec (Z.of_nat (length ids)))) + 1;
                                      Z.of_nat (length (dec_list ids)) + 1])
    (Z.of_nat (length t) + 1)) (Z.of_nat (length t) + 1).
Proof. intros b id ids t. reflexivity. Qed.

Lemma sch_ent :
  forall ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (e z : Z) (jk : list byte),
  0 <= z < 2 ^ 32 ->
  rw_cells rsegs m e [CB 8 jk] ->
  evt rsegs (fun ms' => exists b1 m',
       ms' = MS (mkR (Z_to_bv 64 0x16bd4) sp gp tp t0 t1 t2 (Z_to_bv 64 e) (Z_to_bv 64 z)
                     (Z_to_bv 64 (12 * z + 1)) b1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x18a0c) fc None m' (seg_rom rsegs)
       /\ munch [(e, e + 8)] m m' /\ wmono rsegs m m'
       /\ rw_cells rsegs m' e [C4 (Z_to_bv 64 17); C4 (Z_to_bv 64 0)])
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 e) (Z_to_bv 64 z) a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16bb8) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m e z jk HZ EW.
  pose proof (rw_cells_bound _ _ _ _ EW) as EB. cbn [cells_size csize Nat.add] in EB.
  pose proof (munch_refl [(e, e + 8)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  do 3 step.
  apply (rw_cells_same_bytes _ _ _ [C4 (Z_to_bv 64 17); C4 (Z_to_bv 64 0)]) in EW;
    [| cbn; tauto | vm_compute; reflexivity | reflexivity].
  do 4 step.
  match goal with |- context [Z_to_bv 64 (?x - ?y + 1)] =>
    replace (Z_to_bv 64 (x - y + 1)) with (Z_to_bv 64 (12 * z + 1))
      by (f_equal; rewrite (unsigned_lit z) by lia; rewrite !Z.shiftl_mul_pow2 by lia;
          replace (2 ^ 4) with 16 by reflexivity; replace (2 ^ 2) with 4 by reflexivity;
          rewrite !unsigned_lit by lia; lia) end.
  apply evt_done. do 2 eexists. split; [reflexivity|].
  split; [eassumption|]. split; eassumption.
Qed.

Lemma sch_pre_lt :
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo z : Z) (n : nat),
  stk rsegs m lo (bv_unsigned sp) -> lo + 80 <= bv_unsigned sp -> 0x34100 <= lo ->
  rw_cells rsegs m 0x33d50 [C4 (Z_to_bv 64 (Z.of_nat n))] -> (n < 16)%nat ->
  evt rsegs (fun ms' => exists b0 b1 m' j,
       ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp - 80)) gp tp t0 t1 t2 (Z_to_bv 64 (0x33d58 + 56 * Z.of_nat n))
                     (Z_to_bv 64 z) b0 b1 (Z_to_bv 64 16) a3 a4 a5 a6 a7 a1 s3 a0 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x16bb8) fc None m' (seg_rom rsegs)
       /\ munch [(bv_unsigned sp - 80, bv_unsigned sp); (0x33d50, 0x33d54)] m m' /\ wmono rsegs m m'
       /\ stk rsegs m' lo (bv_unsigned sp - 80)
       /\ rw_cells rsegs m' (bv_unsigned sp - 80)
            [CB 8 j; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
       /\ rw_cells rsegs m' 0x33d50 [C4 (Z_to_bv 64 (Z.of_nat n + 1))])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 (Z_to_bv 64 z) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16b44) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo z n ST LO LO2 NC Hn.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp); (0x33d50, 0x33d54)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 80%nat ST.
  apply (rw_cells_split_CB rsegs _ _ [] 80%nat junk [] [8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [|reflexivity].
  cbn [mk_CB_cells app firstn skipn] in FR.
  do 18 step.
  rewrite sx32_lit by lia.
  assert (C1 : negb (bv_eqb (Z_to_bv 64 (Z.of_nat n)) (Z_to_bv 64 16)) = true).
  { unfold bv_eqb. rewrite !unsigned_lit by lia. apply negb_true_iff, Z.eqb_neq. lia. }
  rewrite C1. cbv iota.
  do 7 step.
  rewrite da_addr by lia.
  apply evt_done.
  do 4 eexists. split; [reflexivity|].
  repeat (split; [eassumption|]). eassumption.
Qed.

Lemma sch_seg_lt :
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo z : Z) (n : nat) (jk : list byte),
  stk rsegs m lo (bv_unsigned sp) -> lo + 80 <= bv_unsigned sp -> 0x34100 <= lo -> 0 <= z < 2 ^ 32 ->
  rw_cells rsegs m 0x33d50 [C4 (Z_to_bv 64 (Z.of_nat n))] -> (n < 16)%nat ->
  rw_cells rsegs m (0x33d58 + 56 * Z.of_nat n) [CB 8 jk] ->
  evt rsegs (fun ms' => exists b1 m' j,
       ms' = MS (mkR (Z_to_bv 64 0x16bd4) (Z_to_bv 64 (bv_unsigned sp - 80)) gp tp t0 t1 t2
                     (Z_to_bv 64 (0x33d58 + 56 * Z.of_nat n)) (Z_to_bv 64 z) (Z_to_bv 64 (12 * z + 1)) b1
                     (Z_to_bv 64 16) a3 a4 a5 a6 a7 a1 s3 a0 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x18a0c) fc None m' (seg_rom rsegs)
       /\ munch [(bv_unsigned sp - 80, bv_unsigned sp); (0x33d50, 0x33d54);
                 (0x33d58 + 56 * Z.of_nat n, 0x33d58 + 56 * Z.of_nat n + 8)] m m'
       /\ wmono rsegs m m'
       /\ stk rsegs m' lo (bv_unsigned sp - 80)
       /\ rw_cells rsegs m' (bv_unsigned sp - 80)
            [CB 8 j; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
       /\ rw_cells rsegs m' 0x33d50 [C4 (Z_to_bv 64 (Z.of_nat n + 1))]
       /\ rw_cells rsegs m' (0x33d58 + 56 * Z.of_nat n) [C4 (Z_to_bv 64 17); C4 (Z_to_bv 64 0)])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 (Z_to_bv 64 z) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16b44) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo z n jk ST LO LO2 HZ NC Hn EW.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  eapply evt_cut; [eapply sch_pre_lt; [exact ST | exact LO | exact LO2 | exact NC | exact Hn] |].
  intros ms1 (b0 & b1 & m1 & j & -> & MU1 & WM1 & ST1 & FR1 & NC1).
  assert (EW1 : rw_cells rsegs m1 (0x33d58 + 56 * Z.of_nat n) [CB 8 jk]).
  { apply (rw_cells_transport rsegs [(bv_unsigned sp - 80, bv_unsigned sp); (0x33d50, 0x33d54)] m m1 _ _ EW MU1 WM1).
    cbn [disjoint_from cells_size csize Nat.add]. repeat split; lia. }
  eapply evt_cut; [eapply sch_ent; [exact HZ | exact EW1] |].
  intros ms2 (b2 & m2 & -> & MU2 & WM2 & EN2).
  apply evt_done. exists b2, m2, j. split; [reflexivity|].
  split.
  { apply (munch_trans _ m m1 m2).
    - apply (munch_weaken [(bv_unsigned sp - 80, bv_unsigned sp); (0x33d50, 0x33d54)]); [|exact MU1].
      intros x (H1 & H2 & H3 & _). split; [exact H1 | split; [exact H2 | exact I]].
    - apply (munch_weaken [(0x33d58 + 56 * Z.of_nat n, 0x33d58 + 56 * Z.of_nat n + 8)]); [|exact MU2].
      intros x (H1 & H2 & H3 & _). split; [exact H3 | exact I]. }
  split; [exact (wmono_trans rsegs _ _ _ WM1 WM2)|].
  split.
  { apply (stk_transport_disjoint rsegs _ m1 m2 _ _ ST1 MU2 WM2). cbn [disjoint_from]. repeat split; lia. }
  split.
  { apply (rw_cells_transport rsegs _ m1 m2 _ _ FR1 MU2 WM2). cbn [disjoint_from cells_size csize Nat.add].
    repeat split; lia. }
  split; [|exact EN2].
  apply (rw_cells_transport rsegs _ m1 m2 _ _ NC1 MU2 WM2). cbn [disjoint_from cells_size csize Nat.add].
  repeat split; lia.
Qed.

Lemma sch_seg_eq :
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo z : Z),
  stk rsegs m lo (bv_unsigned sp) -> lo + 80 <= bv_unsigned sp -> 0x34100 <= lo ->
  rw_cells rsegs m 0x33d50 [C4 (Z_to_bv 64 16)] ->
  evt rsegs (fun ms' => exists b2 m' j,
       ms' = MS (mkR (Z_to_bv 64 0x16b98) (Z_to_bv 64 (bv_unsigned sp - 80)) gp tp t0 t1 t2 (Z_to_bv 64 0x33d10)
                     (Z_to_bv 64 z) (Z_to_bv 64 0x33d10) (Z_to_bv 64 1) b2 a3 a4 a5 a6 a7
                     a1 s3 a0 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x155f0) fc None m' (seg_rom rsegs)
       /\ munch [(bv_unsigned sp - 80, bv_unsigned sp)] m m' /\ wmono rsegs m m'
       /\ stk rsegs m' lo (bv_unsigned sp - 80)
       /\ rw_cells rsegs m' (bv_unsigned sp - 80)
            [CB 8 j; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 (Z_to_bv 64 z) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16b44) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo z ST LO LO2 NC.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 80%nat ST.
  apply (rw_cells_split_CB rsegs _ _ [] 80%nat junk [] [8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [|reflexivity].
  cbn [mk_CB_cells app firstn skipn] in FR.
  do 18 step.
  rewrite sx32_lit by lia.
  if_false.
  do 3 step.
  apply evt_done.
  do 3 eexists. split; [reflexivity|].
  repeat (split; [eassumption|]). eassumption.
Qed.

Lemma sch_ret16 :
  forall ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (z : Z) (jk : list byte),
  0 <= z < 2 ^ 32 ->
  rw_cells rsegs m 0x33d10 [CB 8 jk] ->
  evt rsegs (fun ms' => exists b1 m',
       ms' = MS (mkR (Z_to_bv 64 0x16bd4) sp gp tp t0 t1 t2 (Z_to_bv 64 0x33d10) (Z_to_bv 64 z)
                     (Z_to_bv 64 (12 * z + 1)) b1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x18a0c) fc None m' (seg_rom rsegs)
       /\ munch [(0x33d10, 0x33d10 + 8)] m m' /\ wmono rsegs m m'
       /\ rw_cells rsegs m' 0x33d10 [C4 (Z_to_bv 64 17); C4 (Z_to_bv 64 0)])
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 0x33d10) (Z_to_bv 64 z) a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16b98) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m z jk HZ EW.
  step.
  eapply sch_ent; [exact HZ | exact EW].
Qed.

Lemma sch_m1 :
  forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (p : Z),
  0 < p < 2 ^ 64 ->
  evt rsegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x16be8) sp gp tp t0 t1 t2 s0 s1 s0 s4 a2 a3 a4 a5 a6 a7
                                    s2 (Z_to_bv 64 p) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                           F (Z_to_bv 64 0x15b1c) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16bd4) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p HP.
  step.
  assert (C : bv_eqb (Z_to_bv 64 p) (Z_to_bv 64 0) = false) by (rewrite sc_eqb by lia; apply Z.eqb_neq; lia).
  first [if_false | rewrite C; cbv iota].
  do 4 step.
  apply evt_done. reflexivity.
Qed.

Lemma sch_m2 :
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte),
  evt rsegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x16bf4) sp gp tp t0 t1 t2 s0 s1 s0 s1 a2 a3 a4 a5 a6 a7
                                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                           F (Z_to_bv 64 0x15b1c) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16be8) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m.
  do 3 step.
  apply evt_done. reflexivity.
Qed.

Lemma sch_cp :
  forall ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (e : Z),
  bytes_at rsegs m (e + 4) (le4 (Z_to_bv 64 2)) ->
  evt rsegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x16c50) sp gp tp t0 t1 t2 (Z_to_bv 64 e) s1 s3 (Z_to_bv 64 5)
                                    a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                           F (Z_to_bv 64 0x15780) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 e) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16c3c) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m e HE.
  pose proof (ai_rd4 m (e + 4) _ HE) as RD.
  step. rewrite ai_sx32 by lia.
  do 2 step.
  if_false.
  do 2 step.
  apply evt_done. reflexivity.
Qed.

Lemma sch_st :
  forall ra sp gp tp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (e p : Z),
  bytes_at rsegs m (e + 4) (le4 (Z_to_bv 64 2)) -> wr_at rsegs m e 56 ->
  0 <= e -> e + 56 <= 2 ^ 63 -> 0 <= p < 2 ^ 64 ->
  evt rsegs (fun ms' => exists a1' a2' m',
       ms' = MS (mkR (Z_to_bv 64 0x16c70) sp gp tp t0 t1 t2 (Z_to_bv 64 e) s1 s3 a1' a2' a3 a4 a5 a6 a7
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x188cc) fc None m' (seg_rom rsegs)
       /\ munch [(e + 4, e + 8); (e + 24, e + 32)] m m' /\ wmono rsegs m m'
       /\ bytes_at rsegs m' (e + 4) (le4 (Z_to_bv 64 3)) /\ bytes_at rsegs m' (e + 24) (le8 (Z_to_bv 64 p)))
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 e) s1 (Z_to_bv 64 p) a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16c50) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m e p
    HE HW E0 E1 HP.
  pose proof (ai_rd4 m (e + 4) _ HE) as RD.
  step. rewrite ai_sx32 by lia. do 3 step.
  match goal with |- context [Z_to_bv 64 (e + ?x)] =>
    replace (Z_to_bv 64 (e + x)) with (Z_to_bv 64 (e + 16))
      by (f_equal; rewrite ?unsigned_lit by lia; rewrite ?Z.shiftl_mul_pow2 by lia; reflexivity) end.
  pose proof (wr_at_store_ok rsegs m e 56 24 8 HW ltac:(lia) ltac:(lia)) as HS1.
  step.
  set (m1 := write_to_mem m _ (le8 (Z_to_bv 64 p))).
  assert (HW1 : wr_at rsegs m1 e 56) by (apply wr_at_write; exact HW).
  pose proof (wr_at_store_ok rsegs m1 e 56 4 4 HW1 ltac:(lia) ltac:(lia)) as HS2.
  step.
  assert (L4 : Z.of_nat (length (le4 (Z_to_bv 64 3))) = 4) by (rewrite length_le4; reflexivity).
  assert (L8 : Z.of_nat (length (le8 (Z_to_bv 64 p))) = 8) by (rewrite length_le8; reflexivity).
  assert (B1 : bytes_at rsegs m1 (e + 24) (le8 (Z_to_bv 64 p))) by (apply bytes_at_write_same; rewrite ?L8; lia).
  assert (MU1 : munch [(e + 4, e + 8); (e + 24, e + 32)] m m1).
  { apply munch_write; [apply munch_refl | lia | rewrite L8; lia | cbn [inside]; right; left; rewrite L8; lia]. }
  assert (WM1 : wmono rsegs m m1) by (apply wmono_write; apply wmono_refl).
  match goal with |- context [write_to_mem m1 ?aa ?bs] =>
    replace (write_to_mem m1 aa bs) with (write_to_mem m1 (wa (e + 4)) (le4 (Z_to_bv 64 3)))
      by (f_equal; try (unfold wa; f_equal; lia); try reflexivity; try (vm_compute; reflexivity)) end.
  set (m2 := write_to_mem m1 (wa (e + 4)) (le4 (Z_to_bv 64 3))).
  assert (B2 : bytes_at rsegs m2 (e + 24) (le8 (Z_to_bv 64 p)))
    by (apply bytes_at_write_other; [exact B1 | lia | rewrite L4; lia | rewrite L4, L8; lia]).
  assert (B3 : bytes_at rsegs m2 (e + 4) (le4 (Z_to_bv 64 3))) by (apply bytes_at_write_same; rewrite ?L4; lia).
  assert (MU2 : munch [(e + 4, e + 8); (e + 24, e + 32)] m m2).
  { apply munch_write; [exact MU1 | lia | rewrite L4; lia | cbn [inside]; left; rewrite L4; lia]. }
  assert (WM2 : wmono rsegs m m2) by (apply wmono_write; exact WM1).
  clearbody m2. clear HS1 HS2.
  do 2 step.
  apply evt_done. do 3 eexists. split; [reflexivity|].
  split; [exact MU2|]. split; [exact WM2|]. split; [exact B3 | exact B2].
Qed.

Lemma sch_tail :
  forall ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (sp0 qr q0 q1 q2 q3 q4 q5 q6 q7 : word) (j : list byte),
  rw_cells rsegs m (bv_unsigned sp0 - 80) [CB 8 j; C8 q7; C8 q6; C8 q5; C8 q4; C8 q3; C8 q2; C8 q1; C8 q0; C8 qr] ->
  80 <= bv_unsigned sp0 ->
  evt rsegs (fun ms' => ms' = MS (mkR qr sp0 gp tp t0 t1 t2 q0 q1 s0 a0 (Z_to_bv 64 1) a3 a4 a5 a6 a7
                                    q2 q3 q4 q5 q6 q7 s8 s9 s10 s11 t3 t4 t5 t6)
                           F (Z_to_bv 64 0x15bc8) fc None m (seg_rom rsegs))
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp0 - 80)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16c80) fc None m (seg_rom rsegs)).
Proof.
  intros ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m sp0 qr q0 q1 q2 q3 q4 q5 q6 q7 j FR SPR.
  pose proof (bv_unsigned_in_range 64 sp0) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  do 14 step.
  replace (Z_to_bv 64 (bv_unsigned sp0 - 80 + 80)) with sp0 by (rewrite Z.sub_add; symmetry; apply Z_to_bv_bv_unsigned).
  apply evt_done. reflexivity.
Qed.

Lemma sch_verb : forall m, mem_inv rsegs m -> bytes_at rsegs m 0x104fc (str_bytes "chain"%string).
Proof.
  intros m MI. apply rom_chk_bytes; [exact (ro_agree_of_inv m MI) | lia | cbn; lia | vm_compute; reflexivity].
Qed.

Lemma sch_shape : shape_find shape_rows (str_bytes "chain"%string) = 0x10417.
Proof. vm_compute. reflexivity. Qed.

Lemma sch_after : rec_shape_of_contract ->
  forall ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (sp0 qr q0 q1 q2 q3 q4 q5 q6 q7 : word) (j : list byte),
  rw_cells rsegs m (bv_unsigned sp0 - 80) [CB 8 j; C8 q7; C8 q6; C8 q5; C8 q4; C8 q3; C8 q2; C8 q1; C8 q0; C8 qr] ->
  stk rsegs m lo (bv_unsigned sp0 - 80) -> lo + 144 <= bv_unsigned sp0 -> 0x34100 <= lo ->
  bytes_at rsegs m G_SHAPES g_shapes_bytes -> mem_inv rsegs m ->
  evt rsegs (fun ms' => exists m' (t0' t1' t2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
       ms' = MS (mkR qr sp0 gp tp t0' t1' t2' q0 q1 s0 (Z_to_bv 64 0x10417) (Z_to_bv 64 1)
                     a3' a4' a5' a6' a7' q2 q3 q4 q5 q6 q7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (Z_to_bv 64 0x15bc8) fc None m' (seg_rom rsegs)
       /\ munch [(bv_unsigned sp0 - 144, bv_unsigned sp0 - 80)] m m' /\ wmono rsegs m m')
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp0 - 80)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16c70) fc None m (seg_rom rsegs)).
Proof.
  intros RSO ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo sp0 qr q0 q1 q2 q3 q4 q5 q6 q7 j FR ST LO LO2 GS MI.
  pose proof (bv_unsigned_in_range 64 sp0) as RSP. unfold bv_modulus in RSP.
  assert (GL : length g_shapes_bytes = 448%nat) by (vm_compute; reflexivity).
  assert (SPU : bv_unsigned (Z_to_bv 64 (bv_unsigned sp0 - 80)) = bv_unsigned sp0 - 80) by (apply unsigned_lit; lia).
  do 4 step.
  eapply evt_cut.
  { eapply RSO with (lo := lo) (v := str_bytes "chain"%string).
    - exact MI.
    - rewrite SPU. exact ST.
    - rewrite SPU. unfold REC_SHAPE_OF_FRAME. lia.
    - exact GS.
    - left. rewrite SPU. unfold REC_SHAPE_OF_FRAME, G_SHAPES. lia.
    - rewrite unsigned_lit by lia. reflexivity.
    - intros _. rewrite unsigned_lit by lia. split; [exact (sch_verb m MI)|].
      left. rewrite SPU. unfold REC_SHAPE_OF_FRAME. rewrite ?unsigned_lit by lia. lia. }
  intros ms2 (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & -> & MU2 & WM2
    & MI2 & ST2).
  rewrite SPU in MU2. unfold REC_SHAPE_OF_FRAME in MU2.
  rewrite (ret_pc_even 0x16c80) by lia. rewrite sch_shape.
  assert (FR2 : rw_cells rsegs m2 (bv_unsigned sp0 - 80)
                  [CB 8 j; C8 q7; C8 q6; C8 q5; C8 q4; C8 q3; C8 q2; C8 q1; C8 q0; C8 qr]).
  { apply (rw_cells_transport rsegs _ m m2 _ _ FR MU2 WM2). cbn [disjoint_from cells_size csize Nat.add].
    repeat split; lia. }
  eapply evt_cut; [eapply sch_tail; [exact FR2 | lia] |].
  intros ms3 ->. apply evt_done.
  exists m2, t0', t1', t2', a3', a4', a5', a6', a7', t3', t4', t5', t6'.
  split; [reflexivity|].
  split; [|exact WM2].
  replace (bv_unsigned sp0 - 144) with (bv_unsigned sp0 - 80 - 64) by ring. exact MU2.
Qed.

From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecGlue.

Section F.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis SEGS : ms_segs B = rsegs.
Hypothesis GOWN : forall L A mem md a, aa_MR API L A mem md -> in_globals frame_G a -> ~ owned B L A a.
Hypothesis AX : AllocExtra B (aa_MR API).

Lemma sch_front_lt : forall L A regs mem md R O b n0 jk (P : config -> Prop),
  sinv B API 12384 (spZ regs) L A mem md O L A mem md R O b ->
  m_halted md = None -> m_vm_lazy md = [] ->
  stk rsegs mem (spZ regs - 12384) (spZ regs) -> 0x34100 <= spZ regs - 12384 ->
  rw_cells rsegs mem 0x33d50 [C4 (Z_to_bv 64 (Z.of_nat (length (r_calls R))))] ->
  rw_cells rsegs mem (0x33d58 + 56 * Z.of_nat (length (r_calls R))) [CB 8 jk] ->
  getr regs 12 = Z_to_bv 64 n0 -> 0 <= n0 < 2 ^ 32 ->
  (length (r_calls R) < 16)%nat ->
  (forall R1 m1 b1 j,
     sinv B API 12384 (spZ regs) L A mem md O L A m1 md (rec_record R REC_CHAIN []) O b ->
     Regs6ss.xregs_eqv
       (mkR (Z_to_bv 64 0x16bd4) (Z_to_bv 64 (spZ regs - 80)) (reg_get regs 3) (reg_get regs 4) (reg_get regs 5)
            (reg_get regs 6) (reg_get regs 7) (Z_to_bv 64 (0x33d58 + 56 * Z.of_nat (length (r_calls R))))
            (Z_to_bv 64 n0) (Z_to_bv 64 (12 * n0 + 1)) b1 (Z_to_bv 64 16) (reg_get regs 13) (reg_get regs 14)
            (reg_get regs 15) (reg_get regs 16) (reg_get regs 17) (reg_get regs 11) (reg_get regs 19) (reg_get regs 10)
            (reg_get regs 21) (reg_get regs 22) (reg_get regs 23) (reg_get regs 24) (reg_get regs 25) (reg_get regs 26)
            (reg_get regs 27) (reg_get regs 28) (reg_get regs 29) (reg_get regs 30) (reg_get regs 31)) R1 ->
     rw_cells rsegs m1 (spZ regs - 80)
       [CB 8 j; C8 (reg_get regs 23); C8 (reg_get regs 22); C8 (reg_get regs 21); C8 (reg_get regs 20);
        C8 (reg_get regs 19); C8 (reg_get regs 18); C8 (reg_get regs 9); C8 (reg_get regs 8); C8 (reg_get regs 1)] ->
     stk rsegs m1 (spZ regs - 12384) (spZ regs - 80) ->
     SR rsegs (mkCfg (mkst R1 (Z_to_bv 64 0x18a0c) m1 (seg_rom rsegs)) md) P) ->
  SR rsegs (mkCfg (mkst regs (Z_to_bv 64 0x16b44) mem (seg_rom rsegs)) md) P.
Proof using SEGS GOWN AX.
  intros L A regs mem md R O b n0 jk P SI Hh Hl ST LO2 NC EW A12 HN0 Hn KC.
  set (sp := reg_get regs 2) in *.
  change (spZ regs) with (bv_unsigned sp) in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
  assert (A12' : reg_get regs 12 = Z_to_bv 64 n0) by (rewrite <- A12; reflexivity).
  eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of. fold sp. rewrite A12'.
    eapply sch_seg_lt; [exact ST | lia | exact LO2 | exact HN0 | exact NC | exact Hn | exact EW]. }
  intros ms1 (can1 & (b1 & m1 & j & -> & MU1 & WM1 & ST1 & FR1 & NC1 & EN1) & EQ1).
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ1 eq_refl eq_refl) as (R1 & -> & X1).
  pose proof (sinv_record_lt B API SEGS GOWN AX 12384 (bv_unsigned sp) L A mem md O L A mem md R O b m1 _
                REC_CHAIN SI Hn ltac:(unfold REC_FN_COUNT, REC_CHAIN; lia) MU1 WM1
                ltac:(intros a Ra Hm; cbn in Hm; lia) NC1 EN1) as SI1.
  exact (KC R1 m1 b1 j SI1 X1 FR1 ST1).
Qed.

Hypothesis ERRNO_LOW : errno_addr B + 4 <= alloc_ceiling.
Hypothesis GOTG : ms_got_guard B = 0x22a68.
Hypothesis GRD : ms_guard B = 0x54450.
Hypothesis RCF : rec_calls_free_contract B API.

Lemma sch_front_eq : forall L A regs mem md R O b n0 (P : config -> Prop),
  sinv B API 12384 (spZ regs) L A mem md O L A mem md R O b ->
  m_halted md = None -> m_vm_lazy md = [] ->
  stk rsegs mem (spZ regs - 12384) (spZ regs) -> 0x34100 <= spZ regs - 12384 -> spZ regs mod 16 = 0 ->
  getr regs 4 = Z_to_bv 64 (ms_tp B) ->
  rw_cells rsegs mem 0x33d50 [C4 (Z_to_bv 64 16)] ->
  getr regs 12 = Z_to_bv 64 n0 -> 0 <= n0 < 2 ^ 32 ->
  length (r_calls R) = 16%nat ->
  (forall L' A' R2 m2 md' Oc' j,
     sinv B API 12384 (spZ regs) L A mem md O L' A' m2 md' (rec_record R REC_CHAIN []) Oc' b ->
     sb_le (sb_shift b A A') b ->
     getr R2 1 = Z_to_bv 64 0x16bd4 -> getr R2 2 = Z_to_bv 64 (spZ regs - 80) -> getr R2 4 = getr regs 4 ->
     getr R2 8 = Z_to_bv 64 0x33d10 -> getr R2 9 = Z_to_bv 64 n0 -> getr R2 10 = Z_to_bv 64 (12 * n0 + 1) ->
     getr R2 18 = getr regs 11 -> getr R2 20 = getr regs 10 ->
     getr R2 3 = getr regs 3 -> getr R2 24 = getr regs 24 -> getr R2 25 = getr regs 25 ->
     getr R2 26 = getr regs 26 -> getr R2 27 = getr regs 27 ->
     rw_cells rsegs m2 (spZ regs - 80)
       [CB 8 j; C8 (reg_get regs 23); C8 (reg_get regs 22); C8 (reg_get regs 21); C8 (reg_get regs 20);
        C8 (reg_get regs 19); C8 (reg_get regs 18); C8 (reg_get regs 9); C8 (reg_get regs 8); C8 (reg_get regs 1)] ->
     SR rsegs (mkCfg (mkst R2 (Z_to_bv 64 0x18a0c) m2 (seg_rom rsegs)) md') P) ->
  SR rsegs (mkCfg (mkst regs (Z_to_bv 64 0x16b44) mem (seg_rom rsegs)) md) P.
Proof using SEGS GOWN AX ERRNO_LOW GOTG GRD RCF.
  intros L A regs mem md R O b n0 P SI Hh Hl ST LO2 HAL HTP NC A12 HN0 H16 KC.
  pose proof (aa_laws API) as LAWS.
  set (sp := reg_get regs 2) in *.
  change (spZ regs) with (bv_unsigned sp) in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
  assert (A12' : reg_get regs 12 = Z_to_bv 64 n0) by (rewrite <- A12; reflexivity).
  assert (NC16 : rw_cells rsegs mem 0x33d50 [C4 (Z_to_bv 64 16)]) by exact NC.
  eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of. fold sp. rewrite A12'.
    eapply sch_seg_eq; [exact ST | lia | exact LO2 | exact NC16]. }
  intros ms1 (can1 & (b2 & m1 & j & -> & MU1 & WM1 & ST1 & FR1) & EQ1).
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ1 eq_refl eq_refl) as (R1 & -> & X1).
  assert (E1_1 : getr R1 1 = Z_to_bv 64 0x16b98) by (rewrite (getr_of_eqv _ _ 1 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_2 : getr R1 2 = Z_to_bv 64 (bv_unsigned sp - 80))
    by (rewrite (getr_of_eqv _ _ 2 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_4 : getr R1 4 = getr regs 4) by (rewrite (getr_of_eqv _ _ 4 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_8 : getr R1 8 = Z_to_bv 64 0x33d10) by (rewrite (getr_of_eqv _ _ 8 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_9 : getr R1 9 = Z_to_bv 64 n0) by (rewrite (getr_of_eqv _ _ 9 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_10 : getr R1 10 = Z_to_bv 64 0x33d10)
    by (rewrite (getr_of_eqv _ _ 10 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_11 : getr R1 11 = Z_to_bv 64 1) by (rewrite (getr_of_eqv _ _ 11 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_18 : getr R1 18 = getr regs 11) by (rewrite (getr_of_eqv _ _ 18 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_20 : getr R1 20 = getr regs 10) by (rewrite (getr_of_eqv _ _ 20 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_3 : getr R1 3 = getr regs 3) by (rewrite (getr_of_eqv _ _ 3 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_24 : getr R1 24 = getr regs 24) by (rewrite (getr_of_eqv _ _ 24 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_25 : getr R1 25 = getr regs 25) by (rewrite (getr_of_eqv _ _ 25 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_26 : getr R1 26 = getr regs 26) by (rewrite (getr_of_eqv _ _ 26 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_27 : getr R1 27 = getr regs 27) by (rewrite (getr_of_eqv _ _ 27 X1 eq_refl); simp_regs; reflexivity).
  assert (SP1 : spZ R1 = bv_unsigned sp - 80) by (unfold spZ; rewrite E1_2; apply unsigned_lit; lia).
  pose proof (sinv_stack B API SEGS GOWN AX 12384 (bv_unsigned sp) L A mem md O L A mem md R O b m1 _ SI MU1 WM1
                ltac:(intros a Ra Hm; cbn in Hm; lia)) as SI1.
  apply (sinv_rcf B API SEGS ERRNO_LOW GOTG GRD GOWN AX RCF 12384 (bv_unsigned sp) L A mem md O L A m1 md R O b R1 _
           SI1 H16 E1_10 E1_11).
  - rewrite E1_1. apply bv_eq. vm_compute. reflexivity.
  - rewrite SP1. replace (bv_unsigned sp - 80) with (bv_unsigned sp + (-5) * 16) by ring.
    rewrite Z.mod_add by lia. exact HAL.
  - rewrite SP1. unfold RCF_K, ALLOC_STACK. lia.
  - rewrite SP1. lia.
  - rewrite E1_4. exact HTP.
  - intros L' A' regs' m' md' RP' POST FRK.
    rewrite E1_1.
    pose proof POST as (RJ' & _ & _ & _ & _ & RA' & _ & _ & BLE & _).
    destruct (mr_model B _ LAWS L' A' m' md' (proj1 RJ')) as (Hh' & Hl' & _).
    assert (R8' : getr regs' 8 = Z_to_bv 64 0x33d10) by exact (eq_trans (RP' 8 ltac:(unfold callee_saved; lia)) E1_8).
    assert (R9' : getr regs' 9 = Z_to_bv 64 n0) by exact (eq_trans (RP' 9 ltac:(unfold callee_saved; lia)) E1_9).
    assert (FR' : rw_cells rsegs m' (bv_unsigned sp - 80)
                    [CB 8 j; C8 (reg_get regs 23); C8 (reg_get regs 22); C8 (reg_get regs 21); C8 (reg_get regs 20);
                     C8 (reg_get regs 19); C8 (reg_get regs 18); C8 (reg_get regs 9); C8 (reg_get regs 8);
                     C8 (reg_get regs 1)]).
    { apply (rw_cells_transfer rsegs m1); [exact FR1|]. intros i Hi. cbn in Hi.
      apply FRK. rewrite SP1. lia. }
    destruct (glob_rw_cells m' 0x33d10 8 ltac:(unfold GLOB_LO; lia) ltac:(unfold GLOB_LO, GLOB_N; lia)) as [junk EW].
    eapply evt_SR_canon; [ | exact Hh' | exact Hl' | ].
    { rewrite canon_mkst. unfold Regs6ss.mkR_of.
      assert (Q8 : reg_get regs' 8 = Z_to_bv 64 0x33d10) by exact R8'.
      assert (Q9 : reg_get regs' 9 = Z_to_bv 64 n0) by exact R9'.
      rewrite Q8, Q9.
      eapply sch_ret16; [exact HN0 | exact EW]. }
    intros ms2 (can2 & (b3 & m2 & -> & MU2 & WM2 & EN2) & EQ2).
    destruct (eqv_mkst _ _ _ _ _ _ _ EQ2 eq_refl eq_refl) as (R2 & -> & X2).
    destruct (sinv_record_full B API SEGS GOWN AX 12384 (bv_unsigned sp) L A mem md O L A m1 R O b L' A' m' md' m2
                _ REC_CHAIN POST ltac:(unfold REC_FN_COUNT, REC_CHAIN; lia) MU2 WM2
                ltac:(intros a Ra Hm; cbn in Hm; unfold REC_SC; lia) EN2) as (Oc' & SI2).
    assert (FR2 : rw_cells rsegs m2 (bv_unsigned sp - 80)
                    [CB 8 j; C8 (reg_get regs 23); C8 (reg_get regs 22); C8 (reg_get regs 21); C8 (reg_get regs 20);
                     C8 (reg_get regs 19); C8 (reg_get regs 18); C8 (reg_get regs 9); C8 (reg_get regs 8);
                     C8 (reg_get regs 1)]).
    { apply (rw_cells_transport rsegs _ m' m2 _ _ FR' MU2 WM2). cbn [disjoint_from cells_size csize Nat.add].
      repeat split; lia. }
    rewrite sb_shift_refl in BLE.
    apply (KC L' A' R2 m2 md' Oc' j SI2 BLE).
    + rewrite (getr_of_eqv _ _ 1 X2 eq_refl). simp_regs. reflexivity.
    + rewrite (getr_of_eqv _ _ 2 X2 eq_refl). simp_regs.
      exact (eq_trans (RP' 2 ltac:(unfold callee_saved; lia)) E1_2).
    + rewrite (getr_of_eqv _ _ 4 X2 eq_refl). simp_regs.
      exact (eq_trans (RP' 4 ltac:(unfold callee_saved; lia)) E1_4).
    + rewrite (getr_of_eqv _ _ 8 X2 eq_refl). simp_regs. reflexivity.
    + rewrite (getr_of_eqv _ _ 9 X2 eq_refl). simp_regs. reflexivity.
    + rewrite (getr_of_eqv _ _ 10 X2 eq_refl). simp_regs. reflexivity.
    + rewrite (getr_of_eqv _ _ 18 X2 eq_refl). simp_regs.
      exact (eq_trans (RP' 18 ltac:(unfold callee_saved; lia)) E1_18).
    + rewrite (getr_of_eqv _ _ 20 X2 eq_refl). simp_regs.
      exact (eq_trans (RP' 20 ltac:(unfold callee_saved; lia)) E1_20).
    + rewrite (getr_of_eqv _ _ 3 X2 eq_refl). simp_regs.
      exact (eq_trans (RP' 3 ltac:(unfold callee_saved; lia)) E1_3).
    + rewrite (getr_of_eqv _ _ 24 X2 eq_refl). simp_regs.
      exact (eq_trans (RP' 24 ltac:(unfold callee_saved; lia)) E1_24).
    + rewrite (getr_of_eqv _ _ 25 X2 eq_refl). simp_regs.
      exact (eq_trans (RP' 25 ltac:(unfold callee_saved; lia)) E1_25).
    + rewrite (getr_of_eqv _ _ 26 X2 eq_refl). simp_regs.
      exact (eq_trans (RP' 26 ltac:(unfold callee_saved; lia)) E1_26).
    + rewrite (getr_of_eqv _ _ 27 X2 eq_refl). simp_regs.
      exact (eq_trans (RP' 27 ltac:(unfold callee_saved; lia)) E1_27).
    + exact FR2.
Qed.

Lemma sch_list : sprintf_c.sprintf_contract ->
  forall K S L A mem md O Lc Ac mc mdc Rc Oc bc lp ids pids regs_c (P : config -> Prop),
  sinvx B API K S L A mem md O Lc Ac mc mdc Rc Oc bc (lp, 12 * Z.of_nat (length ids) + 1) ->
  m_halted mdc = None -> m_vm_lazy mdc = [] ->
  (1 <= length ids <= 62)%nat -> Forall (fun v => -2^31 <= v < 2^31) ids ->
  0 <= pids -> pids + 4 * Z.of_nat (length ids) <= TASK_SIZE ->
  (pids + 4 * Z.of_nat (length ids) <= S - K \/ spZ regs_c <= pids) ->
  (pids + 4 * Z.of_nat (length ids) <= lp \/ lp + 12 * Z.of_nat (length ids) + 1 <= pids) ->
  S - K <= spZ regs_c - sprintf_c.SPRINTF_K -> spZ regs_c <= S -> spZ regs_c <= TASK_SIZE ->
  (forall a, S - K <= a < spZ regs_c -> writable_at rsegs mc a) ->
  frm_zero fp_csr ->
  bytes_at rsegs mc pids (concat (map le32 ids)) ->
  getr regs_c 9 = Z_to_bv 64 (Z.of_nat (length ids)) -> getr regs_c 18 = Z_to_bv 64 pids ->
  getr regs_c 19 = Z_to_bv 64 lp ->
  (forall (fx' : YK11.FPState) R' m', fp_kept fx fx' ->
     sinvx B API K S L A mem md O Lc Ac m' mdc Rc Oc bc (lp, 12 * Z.of_nat (length ids) + 1) ->
     bytes_at rsegs m' lp (dec_list ids ++ [Z_to_bv 8 0]) ->
     bytes_at rsegs m' pids (concat (map le32 ids)) ->
     munch [(S - K, spZ regs_c); (lp, lp + (12 * Z.of_nat (length ids) + 1))] mc m' -> wmono rsegs mc m' ->
     ro_agree rsegs m' ->
     getr R' 2 = getr regs_c 2 -> getr R' 3 = getr regs_c 3 -> getr R' 4 = getr regs_c 4 ->
     getr R' 8 = getr regs_c 8 -> getr R' 19 = Z_to_bv 64 lp ->
     getr R' 24 = getr regs_c 24 -> getr R' 25 = getr regs_c 25 -> getr R' 26 = getr regs_c 26 ->
     getr R' 27 = getr regs_c 27 ->
     SR rsegs (mkCfg (@mkst fx' R' (Z_to_bv 64 0x16c3c) m' (seg_rom rsegs)) mdc) P) ->
  SR rsegs (mkCfg (mkst regs_c (Z_to_bv 64 0x16bf4) mc (seg_rom rsegs)) mdc) P.
Proof using SEGS GOWN AX.
  intros SPR K S L A mem md O Lc Ac mc mdc Rc Oc bc lp ids pids regs_c P SI Hh Hl HN HF HP0 HP1 HPS HPL HLO HHI HTS
    HWS FZ HIDS A9 A18 A19 KC.
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
    by (apply RecAns.stk_normalize_cj; [unfold TASK_SIZE in *; lia | exact HTS | exact HWS]).
  set (Q := fun ms : machine_state => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (Ft : bvmap 5 word)
      (fc' : bv 32) (m' : word -> option byte),
      ms = MS (mkR (Z_to_bv 64 0x16c2c) sp (reg_get regs_c 3) (reg_get regs_c 4) t0 t1 t2 (reg_get regs_c 8)
                   (Z_to_bv 64 (Z.of_nat (length ids))) a0 a1 a2 a3 a4 a5 a6 a7
                   (Z_to_bv 64 (pids + 4 * Z.of_nat (length ids))) (Z_to_bv 64 lp) (Z_to_bv 64 (Z.of_nat (length ids)))
                   (Z_to_bv 64 (Z.of_nat (length (dec_list ids)))) (Z_to_bv 64 0x10738) (Z_to_bv 64 0x10828)
                   (reg_get regs_c 24) (reg_get regs_c 25) (reg_get regs_c 26) (reg_get regs_c 27) t3 t4 t5 t6)
              Ft (Z_to_bv 64 0x16c3c) fc' None m' (seg_rom rsegs) /\
      munch [(S - K, bv_unsigned sp); (lp, lp + z)] (normalize_cj rsegs mc) m' /\
      wmono rsegs (normalize_cj rsegs mc) m' /\ frm0 fc' /\
      (forall r : reg, bv_unsigned r <> 10 -> reg_get Ft r = reg_get fp_regs r) /\
      bytes_at rsegs m' pids (concat (map le32 ids)) /\ bytes_at rsegs m' lp (dec_list ids ++ [Z_to_bv 8 0])).
  eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of. fold sp.
    assert (R9 : reg_get regs_c 9 = Z_to_bv 64 (Z.of_nat (length ids))) by exact A9.
    assert (R18 : reg_get regs_c 18 = Z_to_bv 64 pids) by exact A18.
    assert (R19 : reg_get regs_c 19 = Z_to_bv 64 lp) by exact A19.
    rewrite R9, R18, R19.
    eapply (evt_normalize_cj rsegs); [exact WX | exact RA |].
    apply (sc_pre SPR Q ids) with (m0 := normalize_cj rsegs mc) (lo := S - K) (lst := lp) (pids := pids)
      (canary := canary);
      [exact HN | exact HF | exact HP0 | unfold TASK_SIZE in *; lia | exact HPS | exact HPL | lia | unfold z in LC; lia
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
  destruct (RecAns.ms_rel_cj_MS _ _ _ _ _ _ _ _ REL1) as [EC1 MR1r].
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
    | rewrite (getr_of_eqv _ _ 8 X1 eq_refl); simp_regs; reflexivity
    | rewrite (getr_of_eqv _ _ 19 X1 eq_refl); simp_regs; reflexivity
    | rewrite (getr_of_eqv _ _ 24 X1 eq_refl); simp_regs; reflexivity
    | rewrite (getr_of_eqv _ _ 25 X1 eq_refl); simp_regs; reflexivity
    | rewrite (getr_of_eqv _ _ 26 X1 eq_refl); simp_regs; reflexivity
    | rewrite (getr_of_eqv _ _ 27 X1 eq_refl); simp_regs; reflexivity].
  unfold fp_kept. cbn [fp_regs fp_csr]. split; [exact FRM1|].
  intros r Hr. apply FK1. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32.
  unfold fs_saved in Hr. rewrite Z.mod_small by lia. lia.
Qed.

End F.
