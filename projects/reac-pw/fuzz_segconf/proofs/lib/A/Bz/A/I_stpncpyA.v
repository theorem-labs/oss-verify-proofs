(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/pupnp/FuzzHttp/lib/A0/ICP/M_stpncpy.v, with its module paths, module names and addresses changed; 616 of its 693 lines of code are new or changed and 435 lines of the source are left out. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Bz Require BvWfKernel.
(* The walk of musl's strncpy (0x9ad50) and __stpncpy (0x9ad78) of reac-pw/fuzz_segconf's ASan image A, whose padding
   runs through the memset trampoline 0x558d8 into the memset wrapper 0x55fbc (I_imemset.v imemset_spec).  It proves
   I_ncpyspec.v's strncpyA_stmt, which states the source as ncpy_src: either the string, its NUL and the slack to the
   end of the NUL's word, or, when the string is at least n bytes long, its first n bytes alone.
   Adapted into the Bz kit from proofs/pupnp/FuzzHttp/lib/A0/ICP/M_stpncpy.v (origin/ossv/recipes), whose proof
   structure (INV, sp_store, sp_tail, src_byte, byte_step, sp_bytes, sp_bentry, src_word, word_step, sp_words, sp_mid,
   sp_head, sp_body) this file keeps; the list and array helpers below are re-proved from
   proofs/reac-pw/fuzz_segconf/lib/P0/F_stpncpy.v (commit 04999cdbc8ea).
   For the case with no NUL in the first n bytes: adapted proofs/coturn/FuzzStunClient/lib/VBothMuslStrncpy.v:1304
   (origin/ossv/recipes) - its one-src form (every read named by its index in a single src, the stop index given by a
   predicate) is what the two cases of ncpy_src are reduced to here, by src_byte / src_room / src_in_str /
   src_slice_str; its own walk (rdn / wbytes / core_run over coturn's library) has no counterpart in the Bz kit. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Bz.Lib Require Import Tac ImageA SysStep StoreFast Bytes.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Bz.Spec Require Import StrFun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Bz.P Require Import Str_tac.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Bz.A Require Import Shadow R_small R_m2s I_consts I_qck D_kit
  F_memset I_memsetw I_imemset I_ncpyspec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

(* ------------------------------------------------------------------ list helpers *)

Lemma nth_error_firstn_lt : forall (X : Type) (l : list X) k i, (i < k)%nat -> nth_error (firstn k l) i = nth_error l i.
Proof.
  intros X l. induction l as [|a l IH]; intros [|k] [|i] H; cbn in *; try lia; try reflexivity.
  apply IH. lia.
Qed.

Lemma nth_error_skipn' : forall (X : Type) (l : list X) k i, nth_error (skipn k l) i = nth_error l (k + i)%nat.
Proof.
  intros X l. induction l as [|a l IH]; intros [|k] i; cbn; try reflexivity.
  - destruct i; reflexivity.
  - apply IH.
Qed.


Lemma len_firstn_le : forall {X : Type} (l : list X) k, (k <= length l)%nat -> length (firstn k l) = k.
Proof. intros X l k H. rewrite length_firstn. lia. Qed.
(* the 8-byte window the aligned loop reads *)
Definition ncsl (l : list byte) (o k : nat) : list byte := firstn k (skipn o l).

Lemma ncsl_length : forall l o k, (o + k <= length l)%nat -> length (ncsl l o k) = k.
Proof. intros. unfold ncsl. rewrite firstn_length, skipn_length. lia. Qed.

Lemma ncsl_app_l : forall (a b : list byte) i k, (i + k <= length a)%nat -> ncsl (a ++ b) i k = ncsl a i k.
Proof.
  intros a b i k H. unfold ncsl. rewrite skipn_app. replace (i - length a)%nat with 0%nat by lia. cbn [skipn].
  rewrite firstn_app. replace (k - length (skipn i a))%nat with 0%nat by (rewrite skipn_length; lia). cbn [firstn].
  apply app_nil_r.
Qed.

Lemma ncsl_firstn : forall (l : list byte) p i k, (i + k <= p)%nat -> ncsl (firstn p l) i k = ncsl l i k.
Proof.
  intros l p i k H. unfold ncsl. rewrite skipn_firstn_comm, firstn_firstn. f_equal. lia.
Qed.

Lemma firstn_app_ncsl : forall (l : list byte) i k, firstn i l ++ ncsl l i k = firstn (i + k) l.
Proof.
  intros l i k. unfold ncsl.
  replace (firstn i l) with (firstn i (firstn (i + k) l)) by (rewrite firstn_firstn; f_equal; lia).
  rewrite firstn_skipn_comm. apply firstn_skipn.
Qed.

Lemma firstn_slice_succ : forall (str : list byte) i b, nth_error str i = Some b ->
  firstn i str ++ [b] = firstn (i + 1) str.
Proof. intros. rewrite Nat.add_1_r. symmetry. apply firstn_S_nth. assumption. Qed.

Lemma upd_bytes_at_prefix : forall (pre rest xs : list byte), (length xs <= length rest)%nat ->
  upd_bytes (pre ++ rest) (length pre) xs = pre ++ xs ++ skipn (length xs) rest.
Proof.
  intros pre rest xs H. unfold upd_bytes. rewrite firstn_app, firstn_all, Nat.sub_diag. cbn.
  rewrite app_nil_r. rewrite skipn_app. replace (length pre + length xs - length pre)%nat with (length xs) by lia.
  rewrite (skipn_all2 pre) by lia. reflexivity.
Qed.

Lemma le8_surj : forall bs : list byte, length bs = 8%nat -> exists v : word, bs = le8 v.
Proof.
  intros bs Hl. exists (Z_to_bv 64 (bytes_le_to_Z bs)).
  rewrite <- store_bytes_8. change (width_bytes 64) with 8%nat.
  pose proof (le_val_range (map bv_unsigned bs) (bytes_ok_map bs)) as Hr. rewrite length_map, Hl in Hr.
  change (256 ^ Z.of_nat 8) with (2^64) in Hr.
  rewrite Z_to_bv_unsigned, bv_wrap_small.
  2:{ rewrite bytes_le_to_Z_le_val. change (bv_modulus 64) with (2^64). lia. }
  rewrite <- Hl. symmetry. apply Z_to_le_bytes_to_Z.
Qed.

Lemma le8_of_load8 : forall bs : list byte, length bs = 8%nat ->
  le8 (bv_extract 0 64 (le_bytes_to_word bs)) = bs.
Proof. intros bs Hl. destruct (le8_surj bs Hl) as [v ->]. rewrite load_u64. reflexivity. Qed.

Lemma b2z_zero_iff : forall t : bool, bv_unsigned (Z_to_bv 64 (Z.b2z t)) = 0 <-> t = false.
Proof.
  intros [|]; cbn [Z.b2z]; rewrite unsigned_lit by lia; split; intros H;
    first [ reflexivity | discriminate | exfalso; lia ].
Qed.

Lemma u8arr_app_inv : forall m A xs ys, u8arr asegs m A (xs ++ ys) ->
  u8arr asegs m A xs /\ u8arr asegs m (A + Z.of_nat (length xs)) ys.
Proof.
  intros m A xs ys [Hb Hw]. apply bytes_at_app in Hb. destruct Hb as [H1 H2].
  destruct Hw as (HA & HL & Hw). rewrite app_length in HL. split; split; try assumption.
  - split; [lia|]. split; [lia|]. intros i Hi. apply Hw. rewrite app_length. lia.
  - split; [lia|]. split; [lia|]. intros i Hi.
    replace (A + Z.of_nat (length xs) + i) with (A + (Z.of_nat (length xs) + i)) by lia.
    apply Hw. rewrite app_length. lia.
Qed.

Lemma u8arr_app : forall m A xs ys, u8arr asegs m A xs -> u8arr asegs m (A + Z.of_nat (length xs)) ys ->
  u8arr asegs m A (xs ++ ys).
Proof.
  intros m A xs ys [H1 W1] [H2 W2]. split. { apply bytes_at_app. split; assumption. }
  destruct W1 as (HA & HL & W1). destruct W2 as (HA2 & HL2 & W2). rewrite app_length. split; [lia|]. split; [lia|].
  intros i Hi. destruct (Z.lt_ge_cases i (Z.of_nat (length xs))).
  - apply W1. lia.
  - replace (A + i) with (A + Z.of_nat (length xs) + (i - Z.of_nat (length xs))) by lia. apply W2. lia.
Qed.

(* ------------------------------------------------------------------ what the memset wrapper reads *)

(* The copy writes only [d, d + n) and the stack window [k1, k2) with k1 above the shadow; the runtime cells the
   memset wrapper reads (NCPY_CELLS) and every shadow byte it looks at therefore keep their values. *)
Lemma ncpy_carry : forall (m m1 : mem) (d n k1 k2 : Z),
  0 <= d -> 0 <= n -> d + n <= 2^47 -> 17594333495295 < k1 ->
  chk_tails m d n -> ncpy_cells_apart d n -> m2s_cells m -> icells_ms m ->
  munch [(d, d + n); (k1, k2)] m m1 -> wmono asegs m m1 ->
  chk_tails m1 d n /\ m2s_cells m1 /\ icells_ms m1.
Proof.
  intros m m1 d n k1 k2 D0 N0 DH K1 CHK CAP M2S ICM MU WM.
  assert (RNG : n = 0 \/ region_in_mem d n).
  { destruct (Z.eq_dec n 0) as [E|NZ]; [left; exact E| right].
    destruct (CHK 0 ltac:(lia)) as (_ & _ & RO). destruct (RO ltac:(lia)) as (RIM & _).
    replace (d + 0) with d in RIM by lia. replace (n - 0) with n in RIM by lia. exact RIM. }
  assert (OUTC : forall A k x, (n = 0 \/ (d + n <= A \/ A + k <= d)) -> A + k <= 0xad000 -> 0 <= k ->
                 A <= x < A + k -> outside [(d, d + n); (k1, k2)] x).
  { intros A k x HA HB Hk Hx. cbn [outside]. repeat split; try exact I; lia. }
  assert (OUTS : forall x, 0x7fff8000 <= x < 0x10007fff8000 -> outside [(d, d + n); (k1, k2)] x).
  { intros x Hx. cbn [outside]. unfold region_in_mem, kLowMemEnd, kHighShadowEnd, kHighMemEnd in RNG.
    repeat split; try exact I; lia. }
  assert (CL : (n = 0 \/ (d + n <= 0xa2a50 \/ 0xa2a50 + 32 <= d)) /\
               (n = 0 \/ (d + n <= 0xa35b8 \/ 0xa35b8 + 8 <= d)) /\
               (n = 0 \/ (d + n <= 0xa48e8 \/ 0xa48e8 + 8 <= d)) /\
               (n = 0 \/ (d + n <= 0xabff8 \/ 0xabff8 + 8 <= d)) /\
               (n = 0 \/ (d + n <= 0xaccd9 \/ 0xaccd9 + 1 <= d)) /\
               (n = 0 \/ (d + n <= 0xacce0 \/ 0xacce0 + 24 <= d))).
  { destruct CAP as [CZ|CF]; [repeat split; left; exact CZ|].
    unfold NCPY_CELLS in CF.
    pose proof (Forall_inv CF) as F1. pose proof (Forall_inv_tail CF) as CF1. cbn [fst snd] in F1.
    pose proof (Forall_inv CF1) as F2. pose proof (Forall_inv_tail CF1) as CF2. cbn [fst snd] in F2.
    pose proof (Forall_inv CF2) as F3. pose proof (Forall_inv_tail CF2) as CF3. cbn [fst snd] in F3.
    pose proof (Forall_inv CF3) as F4. pose proof (Forall_inv_tail CF3) as CF4. cbn [fst snd] in F4.
    pose proof (Forall_inv CF4) as F5. pose proof (Forall_inv_tail CF4) as CF5. cbn [fst snd] in F5.
    pose proof (Forall_inv CF5) as F6. cbn [fst snd] in F6.
    repeat split; right; assumption. }
  destruct CL as (CL1 & CL2 & CL3 & CL4 & CL5 & CL6).
  assert (AGS : agree_on (fun x => 0x7fff8000 <= x < 0x10007fff8000) m m1)
    by (eapply agree_of_munch; [exact MU| exact OUTS]).
  split; [| split].
  - intros i Hi. eapply chk_ok_agree; [exact (CHK i Hi) | lia | lia | exact AGS].
  - destruct M2S as (M1 & M2 & M3). split; [| split].
    + eapply rw_cells_agree; [exact M1| | exact WM]. eapply agree_of_munch; [exact MU|].
      intros x Hx. cbn [cells_size csize Nat.add] in Hx. apply (OUTC 0xa2a50 32 x CL1); lia.
    + eapply rw_cells_agree; [exact M2| | exact WM]. eapply agree_of_munch; [exact MU|].
      intros x Hx. cbn [cells_size csize Nat.add] in Hx. apply (OUTC 0xabff8 8 x CL4); lia.
    + eapply rw_cells_agree; [exact M3| | exact WM]. eapply agree_of_munch; [exact MU|].
      intros x Hx. cbn [cells_size csize Nat.add] in Hx. apply (OUTC 0xacce0 24 x CL6); lia.
  - destruct ICM as (G1 & G2 & G3 & G4 & G5). split; [| split; [| split; [| split]]].
    + eapply ro_cells_agree; [exact G1|]. eapply agree_of_munch; [exact MU|].
      intros x Hx. cbn [cells_size csize Nat.add] in Hx. apply (OUTC 0xa2a50 32 x CL1); lia.
    + eapply ro_cells_agree; [exact G2|]. eapply agree_of_munch; [exact MU|].
      intros x Hx. cbn [cells_size csize Nat.add] in Hx. apply (OUTC 0xa35b8 8 x CL2); lia.
    + eapply ro_cells_agree; [exact G3|]. eapply agree_of_munch; [exact MU|].
      intros x Hx. cbn [cells_size csize Nat.add] in Hx. apply (OUTC 0xa48e8 8 x CL3); lia.
    + eapply ro_cells_agree; [exact G4|]. eapply agree_of_munch; [exact MU|].
      intros x Hx. cbn [cells_size csize Nat.add] in Hx. apply (OUTC 0xabff8 8 x CL4); lia.
    + eapply ro_cells_agree; [exact G5|]. eapply agree_of_munch; [exact MU|].
      intros x Hx. cbn [cells_size csize Nat.add] in Hx. apply (OUTC 0xaccd9 1 x CL5); lia.
Qed.

(* ------------------------------------------------------------------ what __stpncpy leaves behind *)

(* __stpncpy's own frame (16) and the memset wrapper below it (IMEMSET_DEPTH) *)
Notation ISTPN_DEPTH := 2240%Z (only parsing).

Definition stpnA_post (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (d n sp2 lo : Z) (str : list byte) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms' = MS (mkR ra (Z_to_bv 64 sp2) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(d, d + n); (sp2 - ISTPN_DEPTH, sp2)] m m'
    /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo sp2
    /\ rw_cells asegs m' d [CB (Z.to_nat n) (stpn_result str (Z.to_nat n))].

(* a register slot of a walk lemma, filled in by the step that set it *)
Ltac reg_eq := first [ reflexivity | f_equal; lia | etransitivity; [symmetry; apply Z_to_bv_bv_unsigned|]; f_equal; lia ].

Section WithRIP.
Hypothesis RIP : rip_stmt.
Hypothesis MSZ : memset_callZ_stmt.

(* ------------------------------------------------------------------ the tail when n = 0: memset(d, 0, 0) *)

Lemma tail0 : forall (ra0 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (t0 t1 t2 a0 a1 a2 xa3 a4 a5 a6 a7 t3 t4 t5 t6 xs0 : word)
    (F : bvmap 5 word) (fc : bv 32) (m m1 : mem) (d sp2 lo : Z) (str : list byte),
  0 <= d -> d <= 2^47 -> 17594333495295 < lo -> lo <= sp2 - ISTPN_DEPTH -> sp2 <= 2^47 ->
  chk_tails m d 0 -> ncpy_cells_apart d 0 -> m2s_cells m -> icells_ms m ->
  munch [(d, d + 0); (sp2 - ISTPN_DEPTH, sp2)] m m1 -> wmono asegs m m1 -> mem_inv asegs m1 ->
  stk asegs m1 lo (sp2 + -16) -> rw_cells asegs m1 (sp2 + -16) [C8 s0; C8 ra] ->
  xa3 = Z_to_bv 64 0 -> xs0 = Z_to_bv 64 d ->
  evt asegs (stpnA_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc d 0 sp2 lo str m)
    (MS (mkR ra0 (Z_to_bv 64 (sp2 + -16)) gp tp t0 t1 t2 xs0 s1 a0 a1 a2 xa3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x9ae5c) fc None m1 (seg_rom asegs)).
Proof using RIP MSZ.
  intros until str. intros D0 DH LO0 LOSP SPH CHK CAP M2S ICM MU WM MI STK FR -> ->.
  assert (EUSP : bv_unsigned (Z_to_bv 64 (sp2 + -16)) = sp2 + -16) by (apply unsigned_lit; lia).
  destruct (ncpy_carry m m1 d 0 (sp2 - ISTPN_DEPTH) sp2 D0 ltac:(lia) ltac:(lia) ltac:(lia) CHK CAP M2S ICM MU WM)
    as (CHK1 & M2S1 & IC1).
  pose proof (rw_cells_CB0 m1 d ltac:(lia)) as DST3.
  (* 0x9ae5c mv a0,s0 ; li a1,0 ; mv a2,a3 ; jal 0x558d8 (the memset trampoline), then its j to 0x55fbc *)
  do 5 lstep.
  setreg 10%Z (Z_to_bv 64 d) ltac:(f_equal; lia).
  setreg 11%Z (Z_to_bv 64 0) ltac:(f_equal; lia).
  setreg 12%Z (Z_to_bv 64 0) ltac:(f_equal; lia).
  eapply evt_cut.
  { eapply (imemset_spec RIP MSZ) with (lo := lo) (d := d) (C := 0) (n := 0) (junk := @nil byte);
      [ reflexivity | reflexivity | reflexivity
      | rewrite EUSP; exact STK | rewrite EUSP; lia | unfold kHighShadowEnd; lia | rewrite EUSP; lia
      | lia | lia | lia | lia | left; reflexivity
      | exact DST3
      | (pose proof (CHK1 0 ltac:(lia)) as CC0; rewrite Z.add_0_r, Z.sub_0_r in CC0; exact CC0)
      | exact M2S1 | exact IC1 | exact MI ]. }
  intros ms' PO. destruct_exs PO.
  destruct PO as (E & MUc & WMc & MIc & STc & RWc). subst ms'.
  rewrite EUSP in MUc, STc.
  lazymatch type of MUc with munch _ ?mA ?mB =>
    assert (MUe : munch [(sp2 + -16 - 2224, sp2 + -16)] mA mB)
      by (eapply munch_weaken; [| exact MUc]; unfold sub_fp; cbn [outside]; intros; repeat split; try exact I; lia);
    clear MUc; transport_after_call asegs mA mB MUe WMc; clear MUe WMc end.
  replace (ret_pc (Z_to_bv 64 0x9ae6c)) with (Z_to_bv 64 0x9ae6c) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  (* 0x9ae6c mv a0,s0 ; ld ra,8(sp) ; ld s0,0(sp) ; addi sp,sp,16 ; ret *)
  do 5 lstep.
  try replace (sp2 + -16 + 16) with sp2 by lia.
  release_frame FR STc sp2.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (RWF : rw_cells asegs mm d [CB (Z.to_nat 0) (stpn_result str (Z.to_nat 0))])
      by (change (Z.to_nat 0) with 0%nat;
          replace (stpn_result str 0) with (@nil byte)
            by (unfold stpn_result, stpn_k; rewrite Nat.min_0_r; reflexivity);
          apply rw_cells_CB0; lia) end.
  unfold stpnA_post. sys_finish.
  all: first
    [ assumption
    | (eapply munch_weaken; [| eassumption]; unfold sub_fp; cbn [outside]; intros; repeat split; try exact I; lia) ].
Qed.

(* ------------------------------------------------------------------ __stpncpy with n > 0 *)

Section Proofs.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word).
  Variables (F : bvmap 5 word) (fc : bv 32) (m : mem).
  Variables (d s n sp2 lo : Z) (str src : list byte).

  Local Notation nn := (Z.to_nat n).
  Local Notation WIN := [(d, d + n); (sp2 - ISTPN_DEPTH, sp2)].

  Hypothesis NPOS : 0 < n < 2^32.
  Hypothesis D0 : 0 <= d.
  Hypothesis DH : d + n <= 2^47.
  Hypothesis S0 : 0 <= s.
  Hypothesis SH : s + Z.of_nat (length src) <= 2^47.
  Hypothesis LO0 : 17594333495295 < lo.
  Hypothesis LOSP : lo <= sp2 - ISTPN_DEPTH.
  Hypothesis SPH : sp2 <= 2^47.
  Hypothesis SRCOK : ncpy_src s nn str src.
  Hypothesis SEP : d + n <= s \/ s + Z.of_nat (length src) <= d.
  Hypothesis SEPS : s + Z.of_nat (length src) <= lo \/ sp2 + 16 <= s.
  Hypothesis SEPD : d + n <= lo \/ sp2 + 16 <= d.
  Hypothesis CHK : chk_tails m d n.
  Hypothesis CAP : ncpy_cells_apart d n.
  Hypothesis M2S : m2s_cells m.
  Hypothesis ICM : icells_ms m.

  Local Notation POST := (stpnA_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc d n sp2 lo str m).

  Local Notation ST pc m1 x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (sp2 + -16)) gp tp x5 x6 x7 x8 s1 x10 x11 x12 x13 x14 x15 x16 x17
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None m1 (seg_rom asegs)).

  Notation CMAGIC := 72340172838076672%Z.
  Notation HIGHS := 9259542123273814144%Z.

  Definition INV (m1 : mem) (i : nat) (rest : list byte) : Prop :=
    u8arr asegs m1 d (firstn i str ++ rest) /\ length rest = (nn - i)%nat /\
    (i <= length str)%nat /\ (i <= nn)%nat /\
    bytes_at asegs m1 s src /\ mem_inv asegs m1 /\ munch WIN m m1 /\ wmono asegs m m1 /\
    stk asegs m1 lo (sp2 + -16) /\ rw_cells asegs m1 (sp2 + -16) [C8 s0; C8 ra].

  Ltac inv_open H := destruct H as (DST & LR & IL & IN & SRC & MI & MU & WM & STK & FR).

  (* reg_eq is defined before Section WithRIP *)

  Ltac st_gen xs bytes_tac :=
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m1 ?a ?bs0) _) =>
      replace bs0 with xs by bytes_tac;
      repeat match goal with
      | H : store_ok _ m1 _ _ = true |- _ => clear H
      | H : ov_read_bytes _ m1 _ _ = Some _ |- _ => clear H
      | H : u8arr _ m1 _ _ |- _ => clear H
      | H : bytes_at _ m1 _ _ |- _ => clear H
      | H : mem_inv _ m1 |- _ => clear H
      | H : munch _ _ m1 |- _ => clear H
      | H : wmono _ _ m1 |- _ => clear H
      | H : stk _ m1 _ _ |- _ => clear H
      | H : rw_cells _ m1 _ _ |- _ => clear H
      | H : INV m1 _ _ |- _ => clear H
      end;
      let m' := fresh "m" in remember (write_to_mem m1 a xs) as m' eqn:Egen; clear Egen; try clear m1
    end.

  Lemma prefix_length : forall i rest, (i <= length str)%nat -> length (firstn i str ++ rest) = (i + length rest)%nat.
  Proof. intros. rewrite app_length, firstn_length_le by lia. reflexivity. Qed.

  (* ---------- the source, from ncpy_src: one list src, each read named by its index ---------- *)

  Lemma src_byte : forall i, (i < nn)%nat -> (i <= length str)%nat ->
    exists b, nth_error src i = Some b /\ (bv_unsigned b = 0 <-> i = length str) /\
              ((i < length str)%nat -> nth_error str i = Some b).
  Proof.
    intros i Hi Hl. destruct SRCOK as (NONUL & [(slack & Esrc & PAD) | (HnL & Esrc)]).
    - destruct (Nat.eq_dec i (length str)) as [E|NE].
      + subst i. exists (Z_to_bv 8 0). rewrite Esrc, nth_error_app2, Nat.sub_diag by lia. cbn [nth_error].
        split; [reflexivity|]. split; [split; intros _; reflexivity| intros; lia].
      + assert (Hlt : (i < length str)%nat) by lia.
        destruct (nth_error str i) as [b|] eqn:Eb; [| apply nth_error_None in Eb; lia].
        exists b. rewrite Esrc, nth_error_app1 by lia. split; [exact Eb|].
        split; [| intros _; reflexivity].
        split; [intros H0 | intros H0; lia].
        exfalso. apply NONUL. replace (Z_to_bv 8 0) with b; [eapply nth_error_In; exact Eb|].
        apply bv_eq. rewrite H0. reflexivity.
    - assert (Hlt : (i < length str)%nat) by lia.
      destruct (nth_error str i) as [b|] eqn:Eb; [| apply nth_error_None in Eb; lia].
      exists b. rewrite Esrc, nth_error_firstn_lt by lia. split; [exact Eb|].
      split; [| intros _; reflexivity].
      split; [intros H0 | intros H0; lia].
      exfalso. apply NONUL. replace (Z_to_bv 8 0) with b; [eapply nth_error_In; exact Eb|].
      apply bv_eq. rewrite H0. reflexivity.
  Qed.

  Lemma src_room : forall i, (i + 8 <= nn)%nat -> (i <= length str)%nat -> ((s + Z.of_nat i) mod 8 = 0) ->
    (i + 8 <= length src)%nat.
  Proof.
    intros i Hi Hl Hal. destruct SRCOK as (NONUL & [(slack & Esrc & PAD) | (HnL & Esrc)]).
    - subst src. rewrite app_length. cbn [length]. Z.div_mod_to_equations. lia.
    - subst src. rewrite firstn_length. lia.
  Qed.

  Lemma src_len_ge : forall i, (i + 8 <= nn)%nat -> (i + 8 <= length str)%nat -> (i + 8 <= length src)%nat.
  Proof.
    intros i H1 H2. destruct SRCOK as (_ & [(slack & Esrc & _) | (HnL & Esrc)]).
    - rewrite Esrc, app_length. cbn [length]. lia.
    - rewrite Esrc, firstn_length. lia.
  Qed.

  Lemma src_in_str : forall i, (i + 8 <= nn)%nat -> (i <= length str)%nat ->
    ~ In (Z_to_bv 8 0) (ncsl src i 8) -> (i + 8 <= length str)%nat.
  Proof.
    intros i Hi Hl HN. destruct SRCOK as (NONUL & [(slack & Esrc & PAD) | (HnL & Esrc)]); [| lia].
    destruct (Nat.lt_ge_cases (length str) (i + 8)) as [LT|GE]; [| exact GE].
    exfalso. apply HN. subst src. unfold ncsl.
    apply nth_error_In with (n := (length str - i)%nat).
    rewrite nth_error_firstn_lt by lia. rewrite nth_error_skipn'.
    replace (i + (length str - i))%nat with (length str) by lia.
    rewrite nth_error_app2, Nat.sub_diag by lia. reflexivity.
  Qed.

  Lemma src_slice_str : forall i, (i + 8 <= nn)%nat -> (i + 8 <= length str)%nat -> ncsl src i 8 = ncsl str i 8.
  Proof.
    intros i Hi Hl. destruct SRCOK as (NONUL & [(slack & Esrc & PAD) | (HnL & Esrc)]).
    - subst src. apply ncsl_app_l. lia.
    - subst src. apply ncsl_firstn. lia.
  Qed.

  (* ---------- one store into the destination ---------- *)

  Lemma sp_store : forall m1 i rest xs a,
    INV m1 i rest -> (length xs <= length rest)%nat -> a = wa (d + Z.of_nat i) ->
    store_ok asegs m1 a (length xs) = true /\
    (u8arr asegs (write_to_mem m1 a xs) d (firstn i str ++ xs ++ skipn (length xs) rest) /\
     bytes_at asegs (write_to_mem m1 a xs) s src /\ mem_inv asegs (write_to_mem m1 a xs) /\
     munch WIN m (write_to_mem m1 a xs) /\ wmono asegs m (write_to_mem m1 a xs) /\
     stk asegs (write_to_mem m1 a xs) lo (sp2 + -16) /\
     rw_cells asegs (write_to_mem m1 a xs) (sp2 + -16) [C8 s0; C8 ra]).
  Proof.
    intros m1 i rest xs a I Hl Ha; inv_open I.
    pose proof (prefix_length i rest IL) as PL.
    pose proof (bytes_at_bound asegs m1 s src SRC) as BS.
    assert (SOK : store_ok asegs m1 a (length xs) = true).
    { eapply (u8arr_store_ok_n asegs m1 d _ (Z.of_nat i) (length xs) a DST); [lia| rewrite PL; lia | rewrite Ha; reflexivity]. }
    split; [exact SOK|]. subst a. split; [|split; [|split; [|split; [|split; [|split]]]]].
    - pose proof (u8arr_write_bytes asegs m1 d _ (Z.of_nat i) xs DST ltac:(lia) ltac:(rewrite Nat2Z.id, PL; lia)) as U.
      rewrite Nat2Z.id in U. replace i with (length (firstn i str)) in U at 3 by (rewrite firstn_length_le; lia).
      rewrite upd_bytes_at_prefix in U by lia. exact U.
    - apply bytes_at_write_other; [exact SRC| lia| lia| lia].
    - apply mem_inv_store; [exact MI| exact SOK].
    - apply munch_write; [exact MU| lia| lia|]. cbn [inside]. left. lia.
    - apply wmono_write. exact WM.
    - apply stk_write; [exact STK| lia| lia].
    - apply rw_cells_frame; [exact FR| lia| lia|]. cbn [cells_size csize Nat.add]. lia.
  Qed.

  (* ---------- the tail: memset(d + i, 0, n - i) through the trampoline ---------- *)

  Lemma sp_tail : forall m1 i rest x1 x5 x6 x7 x10 x11 x12 xa3 x14 x15 x16 x17 xs0 x28 x29 x30 x31,
    INV m1 i rest -> (i = length str \/ i = nn)%nat ->
    xa3 = Z_to_bv 64 (n - Z.of_nat i) -> xs0 = Z_to_bv 64 (d + Z.of_nat i) ->
    evt asegs POST (ST 0x9ae5c m1 x1 x5 x6 x7 xs0 x10 x11 x12 xa3 x14 x15 x16 x17 x28 x29 x30 x31).
  Proof.
    intros m1 i rest x1 x5 x6 x7 x10 x11 x12 xa3 x14 x15 x16 x17 xs0 x28 x29 x30 x31 I Hi -> ->.
    pose proof I as I'; inv_open I'.
    pose proof (prefix_length i rest IL) as PL.
    destruct (u8arr_app_inv m1 d (firstn i str) rest DST) as [DST1 DST2].
    pose proof (len_firstn_le str i IL) as FL.
    rewrite FL in DST2.
    pose proof (rw_cells_of_u8arr asegs m1 _ _ DST2) as DST3. rewrite LR in DST3. clear DST DST2.
    assert (EUSP : bv_unsigned (Z_to_bv 64 (sp2 + -16)) = sp2 + -16) by (apply unsigned_lit; lia).
    destruct (ncpy_carry m m1 d n (sp2 - ISTPN_DEPTH) sp2 D0 ltac:(lia) DH ltac:(lia) CHK CAP M2S ICM MU WM)
      as (CHK1 & M2S1 & IC1).
    (* 0x9ae5c mv a0,s0 ; li a1,0 ; mv a2,a3 ; jal 0x558d8, then the trampoline's j to 0x55fbc *)
    do 5 lstep.
    setreg 10%Z (Z_to_bv 64 (d + Z.of_nat i)) ltac:(f_equal; lia).
    setreg 11%Z (Z_to_bv 64 0) ltac:(f_equal; lia).
    setreg 12%Z (Z_to_bv 64 (n - Z.of_nat i)) ltac:(f_equal; lia).
    eapply evt_cut.
    { eapply (imemset_spec RIP MSZ) with (lo := lo) (d := (d + Z.of_nat i)) (C := 0) (n := (n - Z.of_nat i));
      [ reflexivity | reflexivity | reflexivity
      | rewrite EUSP; exact STK | rewrite EUSP; lia | unfold kHighShadowEnd; lia | rewrite EUSP; lia
      | lia | lia | lia | lia | rewrite EUSP; lia
      | (lazymatch goal with |- rw_cells _ _ _ [CB ?k _] => replace k with (nn - i)%nat by lia end; exact DST3)
      | apply (CHK1 (Z.of_nat i)); lia | exact M2S1 | exact IC1 | exact MI ]. }
    intros ms' PO. destruct_exs PO.
    destruct PO as (E & MUc & WMc & MIc & STc & RWz). subst ms'.
    rewrite EUSP in MUc, STc.
    lazymatch type of MUc with munch _ ?mA ?mB =>
      transport_after_call asegs mA mB MUc WMc; clear MUc WMc end.
    replace (ret_pc (Z_to_bv 64 0x9ae6c)) with (Z_to_bv 64 0x9ae6c)
      by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    rename STc into STK2.
    apply u8arr_of_rw_cells in RWz.
    replace (Z_to_bv 8 (0 mod 256)) with (Z_to_bv 8 0) in RWz by reflexivity.
    replace (Z.to_nat (n - Z.of_nat i)) with (nn - i)%nat in RWz by lia.
    rewrite <- FL in RWz at 1.
    pose proof (u8arr_app _ d (firstn i str) _ DST1 RWz) as DSTF. clear DST1 RWz.
    assert (Ei : i = stpn_k str nn) by (unfold stpn_k; lia).
    replace (firstn i str ++ repeat (Z_to_bv 8 0) (nn - i)) with (stpn_result str nn) in DSTF
      by (unfold stpn_result; rewrite <- Ei; reflexivity).
    (* 0x9ae6c mv a0,s0 ; ld ra,8(sp) ; ld s0,0(sp) ; addi sp,sp,16 ; ret *)
    do 5 lstep.
    try replace (sp2 + -16 + 16) with sp2 by lia.
    release_frame FR STK2 sp2.
    apply rw_cells_of_u8arr in DSTF. rewrite stpn_result_length in DSTF.
    unfold stpnA_post. sys_finish.
  Qed.

  (* ---------- the byte loops ---------- *)

  Lemma byte_step : forall m1 i rest b,
    INV m1 i rest -> (i < nn)%nat -> nth_error src i = Some b -> (bv_unsigned b = 0 <-> i = length str) ->
    ((i < length str)%nat -> nth_error str i = Some b) ->
    store_ok asegs m1 (Z_to_bv 64 (d + Z.of_nat i)) 1 = true /\
    (bv_unsigned b <> 0 -> INV (write_to_mem m1 (Z_to_bv 64 (d + Z.of_nat i)) [b]) (i + 1) (skipn 1 rest)) /\
    (bv_unsigned b = 0 -> INV (write_to_mem m1 (Z_to_bv 64 (d + Z.of_nat i)) [b]) i (b :: skipn 1 rest)).
  Proof.
    intros m1 i rest b I Hi Hb Hz Hstr. pose proof I as I'; inv_open I'.
    destruct (sp_store m1 i rest [b] (Z_to_bv 64 (d + Z.of_nat i)) I ltac:(cbn; lia) ltac:(unfold wa; reflexivity))
      as (SOK & DST' & SRC' & MI' & MU' & WM' & STK' & FR').
    cbn [length] in SOK, DST'. split; [exact SOK|]. split; intros Hbz.
    - assert (Hil : (i < length str)%nat) by (destruct (Nat.eq_dec i (length str)); [exfalso; apply Hbz, Hz; assumption| lia]).
      split; [| split; [| split; [lia| split; [lia| split; [exact SRC'| split; [exact MI'| split; [exact MU'| split; [exact WM'| split; [exact STK'| exact FR']]]]]]]]].
      + change (b :: skipn 1 rest) with ([b] ++ skipn 1 rest) in DST'. rewrite app_assoc in DST'.
        rewrite (firstn_slice_succ str i b) in DST'; [exact DST'| exact (Hstr Hil)].
      + rewrite skipn_length. lia.
    - apply Hz in Hbz. subst i. split; [exact DST'|]. split; [cbn [length]; rewrite skipn_length; lia|].
      split; [lia|]. split; [lia|].
      split; [exact SRC'| split; [exact MI'| split; [exact MU'| split; [exact WM'| split; [exact STK'| exact FR']]]]].
  Qed.

  Lemma sp_bytes : forall (r : nat) (i : nat) m1 rest x1 x5 x6 x7 x10 xa1 x12 xa3 x14 x15 x16 x17 xs0 x28 x29 x30 x31,
    (r = nn - i)%nat -> (i < nn)%nat -> INV m1 i rest ->
    xa1 = Z_to_bv 64 (s + Z.of_nat i) -> xa3 = Z_to_bv 64 (n - Z.of_nat i) -> xs0 = Z_to_bv 64 (d + Z.of_nat i) ->
    evt asegs POST (ST 0x9ad9c m1 x1 x5 x6 x7 xs0 x10 xa1 x12 xa3 x14 x15 x16 x17 x28 x29 x30 x31).
  Proof.
    induction r as [|r IH]; intros i m1 rest x1 x5 x6 x7 x10 xa1 x12 xa3 x14 x15 x16 x17 xs0 x28 x29 x30 x31
      Hr Hi I -> -> ->; [lia|].
    pose proof I as I'; inv_open I'.
    destruct (src_byte i Hi IL) as (b & Hb & Hz & Hstr). pose proof (byte_range b).
    pose proof (u8ro_read asegs m1 s src (Z.of_nat i) b (Z_to_bv 64 (s + Z.of_nat i)) SRC
                  ltac:(rewrite Nat2Z.id; exact Hb) ltac:(lia) eq_refl) as RD.
    destruct (byte_step m1 i rest b I Hi Hb Hz Hstr) as (SOK & In0 & Iz).
    lstep. lstep. st_gen [b] by_byte.
    lstep. if_cases Kz; zify_cond Kz.
    - pose proof (Iz Kz) as I2. apply Hz in Kz.
      eapply (sp_tail _ i); [exact I2| lia| reg_eq| reg_eq].
    - pose proof (In0 Kz) as I2.
      lstep. lstep. lstep. lstep. if_cases Kr; zify_cond Kr.
      + replace (s + Z.of_nat i + 1) with (s + Z.of_nat (i + 1)) by lia.
        replace (d + Z.of_nat i + 1) with (d + Z.of_nat (i + 1)) by lia.
        replace (n - Z.of_nat i + -1) with (n - Z.of_nat (i + 1)) by lia.
        apply (IH (i + 1)%nat _ (skipn 1 rest)); try lia; try exact I2; reg_eq.
      + lstep. eapply (sp_tail _ (i + 1)%nat); [exact I2| lia| reg_eq| reg_eq].
  Qed.

  Lemma sp_bentry : forall (i : nat) m1 rest x1 x5 x6 x7 x10 xa1 xa2 x13 x14 x15 x16 x17 xs0 x28 x29 x30 x31,
    (i <= nn)%nat -> INV m1 i rest ->
    xa1 = Z_to_bv 64 (s + Z.of_nat i) -> xa2 = Z_to_bv 64 (n - Z.of_nat i) -> xs0 = Z_to_bv 64 (d + Z.of_nat i) ->
    evt asegs POST (ST 0x9ad94 m1 x1 x5 x6 x7 xs0 x10 xa1 xa2 x13 x14 x15 x16 x17 x28 x29 x30 x31).
  Proof.
    intros i m1 rest x1 x5 x6 x7 x10 xa1 xa2 x13 x14 x15 x16 x17 xs0 x28 x29 x30 x31 Hi I -> -> ->.
    pose proof I as I'; inv_open I'.
    lstep. if_cases K0; zify_cond K0.
    - lstep. eapply (sp_tail _ i); [exact I| lia| reg_eq| reg_eq].
    - lstep. apply (sp_bytes (nn - i) i _ rest); try lia; try exact I; reg_eq.
  Qed.

  (* ---------- the word loop ---------- *)

  Lemma word_step : forall m1 i rest (ch : list byte),
    INV m1 i rest -> (i + 8 <= nn)%nat -> (i + 8 <= length str)%nat -> ch = ncsl src i 8 ->
    store_ok asegs m1 (Z_to_bv 64 (d + Z.of_nat i)) 8 = true /\
    INV (write_to_mem m1 (Z_to_bv 64 (d + Z.of_nat i)) ch) (i + 8) (skipn 8 rest).
  Proof.
    intros m1 i rest ch I Hi Hl ->. pose proof I as I'; inv_open I'.
    pose proof (bytes_at_bound asegs m1 s src SRC) as BS.
    pose proof (src_len_ge i Hi Hl) as SLG.
    assert (CL : length (ncsl src i 8) = 8%nat) by (apply ncsl_length; lia).
    destruct (sp_store m1 i rest (ncsl src i 8) (Z_to_bv 64 (d + Z.of_nat i)) I ltac:(rewrite CL; lia)
                ltac:(unfold wa; reflexivity))
      as (SOK & DST' & SRC' & MI' & MU' & WM' & STK' & FR').
    rewrite CL in SOK, DST'. split; [exact SOK|].
    split; [| split; [rewrite skipn_length; lia| split; [lia| split; [lia| split; [exact SRC'| split; [exact MI'| split; [exact MU'| split; [exact WM'| split; [exact STK'| exact FR']]]]]]]]].
    replace (firstn (i + 8) str ++ skipn 8 rest) with (firstn i str ++ ncsl src i 8 ++ skipn 8 rest);
      [exact DST'|].
    rewrite (src_slice_str i ltac:(lia) ltac:(lia)), app_assoc, firstn_app_ncsl. reflexivity.
  Qed.

  Lemma sp_words : forall (r : nat) (i : nat) m1 rest x1 x5 x6 x7 x10 xa1 xa2 xa3 xa4 xa5 x16 x17 xs0 x28 x29 x30 x31,
    (r = nn - i)%nat -> (i + 8 <= nn)%nat -> ((s + Z.of_nat i) mod 8 = 0) -> INV m1 i rest ->
    xa1 = Z_to_bv 64 (s + Z.of_nat i) -> xa2 = Z_to_bv 64 (n - Z.of_nat i) ->
    xa3 = Z_to_bv 64 CMAGIC -> xa4 = Z_to_bv 64 HIGHS -> xa5 = Z_to_bv 64 7 ->
    xs0 = Z_to_bv 64 (d + Z.of_nat i) ->
    evt asegs POST (ST 0x9ae2c m1 x1 x5 x6 x7 xs0 x10 xa1 xa2 xa3 xa4 xa5 x16 x17 x28 x29 x30 x31).
  Proof.
    induction r as [r IH] using lt_wf_ind;
      intros i m1 rest x1 x5 x6 x7 x10 xa1 xa2 xa3 xa4 xa5 x16 x17 xs0 x28 x29 x30 x31 Hr Hi Hal I -> -> -> -> -> ->;
      subst r.
    pose proof I as I'; inv_open I'.
    pose proof (src_room i Hi IL Hal) as HW.
    pose proof (bytes_at_read asegs m1 s src (Z.of_nat i) 8 SRC ltac:(lia) ltac:(rewrite Nat2Z.id; exact HW)) as RD.
    rewrite Nat2Z.id in RD. change (firstn 8 (skipn i src)) with (ncsl src i 8) in RD.
    set (ch := ncsl src i 8) in RD.
    assert (CL : length ch = 8%nat) by (subst ch; apply ncsl_length; lia).
    pose proof (le_val_range _ (bytes_ok_map ch)) as WR. rewrite length_map, CL in WR.
    change (256 ^ Z.of_nat 8) with (2^64) in WR.
    lstep. lstep. lstep. lstep. rewrite (load8_le_val ch CL). lstep. if_cases K; zify_cond K.
    - lstep. apply (sp_bytes (nn - i) i _ rest); try lia; try exact I; reg_eq.
    - apply (haszero64_clang _ (bytes_ok_map ch) ltac:(rewrite length_map; exact CL)) in K.
      rewrite In0_map_unsigned in K.
      assert (Hi8 : (i + 8 <= length str)%nat) by (apply src_in_str; [lia| lia| exact K]).
      destruct (word_step m1 i rest ch I Hi Hi8 eq_refl) as [SOK I2].
      lstep. st_gen ch ltac:(symmetry; apply le8_of_load8; exact CL).
      lstep. lstep. lstep. lstep. if_cases K8; zify_cond K8.
      + replace (s + Z.of_nat i + 8) with (s + Z.of_nat (i + 8)) by lia.
        replace (d + Z.of_nat i + 8) with (d + Z.of_nat (i + 8)) by lia.
        replace (n - Z.of_nat i + -8) with (n - Z.of_nat (i + 8)) by lia.
        apply (IH (nn - (i + 8))%nat ltac:(lia) (i + 8)%nat _ (skipn 8 rest));
          first [exact I2 | lia | (Z.div_mod_to_equations; lia) | reg_eq].
      + lstep. eapply (sp_bentry (i + 8)%nat); [lia| exact I2| reg_eq| reg_eq| reg_eq].
  Qed.

  (* ---------- the aligned entry and the head bytes ---------- *)

  Lemma sp_mid : forall (i : nat) m1 rest (fl : word) x1 x5 x6 x7 x10 xa1 xa2 x13 x15 x16 x17 xs0 x28 x29 x30 x31,
    (i <= nn)%nat -> INV m1 i rest -> (bv_unsigned fl = 0 <-> i = nn) ->
    (bv_unsigned fl <> 0 -> ((s + Z.of_nat i) mod 8 = 0)) ->
    xa1 = Z_to_bv 64 (s + Z.of_nat i) -> xa2 = Z_to_bv 64 (n - Z.of_nat i) -> xs0 = Z_to_bv 64 (d + Z.of_nat i) ->
    evt asegs POST (ST 0x9ae04 m1 x1 x5 x6 x7 xs0 x10 xa1 xa2 x13 fl x15 x16 x17 x28 x29 x30 x31).
  Proof.
    intros i m1 rest fl x1 x5 x6 x7 x10 xa1 xa2 x13 x15 x16 x17 xs0 x28 x29 x30 x31 Hi I Hfl Hal -> -> ->.
    pose proof I as I'; inv_open I'.
    lstep. if_cases K0; zify_cond K0.
    - apply Hfl in K0. lstep. eapply (sp_tail _ i); [exact I| lia| reg_eq| reg_eq].
    - assert (Hin : (i < nn)%nat) by (destruct (Nat.eq_dec i nn); [exfalso; apply K0, Hfl; assumption| lia]).
      specialize (Hal K0).
      destruct (src_byte i Hin IL) as (b & Hb & Hz & Hstr). pose proof (byte_range b).
      pose proof (u8ro_read asegs m1 s src (Z.of_nat i) b (Z_to_bv 64 (s + Z.of_nat i)) SRC
                    ltac:(rewrite Nat2Z.id; exact Hb) ltac:(lia) eq_refl) as RD.
      lstep. lstep. if_cases Kz; zify_cond Kz.
      + apply Hz in Kz. lstep. lstep. eapply (sp_tail _ i); [exact I| lia| reg_eq| reg_eq].
      + lstep. lstep. if_cases K8; zify_cond K8.
        * eapply (sp_bentry i); [lia| exact I| reg_eq| reg_eq| reg_eq].
        * lstep. lstep. lstep. lstep. lstep.
          apply (sp_words (nn - i) i _ rest); try lia; try exact I; reg_eq.
  Qed.

  Lemma sp_head : forall (r : nat) (i : nat) m1 rest x1 x5 x6 x7 x10 xa1 xa2 x13 x14 xa5 xa6 x17 xs0 x28 x29 x30 x31,
    (r = nn - i)%nat -> (i < nn)%nat -> INV m1 i rest ->
    xa1 = Z_to_bv 64 (s + Z.of_nat i) -> xa2 = Z_to_bv 64 (n - Z.of_nat i) ->
    xa5 = Z_to_bv 64 (s + Z.of_nat i + 1) -> xa6 = Z_to_bv 64 1 -> xs0 = Z_to_bv 64 (d + Z.of_nat i) ->
    evt asegs POST (ST 0x9add4 m1 x1 x5 x6 x7 xs0 x10 xa1 xa2 x13 x14 xa5 xa6 x17 x28 x29 x30 x31).
  Proof.
    induction r as [|r IH]; intros i m1 rest x1 x5 x6 x7 x10 xa1 xa2 x13 x14 xa5 xa6 x17 xs0 x28 x29 x30 x31
      Hr Hi I -> -> -> -> ->; [lia|].
    pose proof I as I'; inv_open I'.
    destruct (src_byte i Hi IL) as (b & Hb & Hz & Hstr). pose proof (byte_range b).
    pose proof (u8ro_read asegs m1 s src (Z.of_nat i) b (Z_to_bv 64 (s + Z.of_nat i)) SRC
                  ltac:(rewrite Nat2Z.id; exact Hb) ltac:(lia) eq_refl) as RD.
    destruct (byte_step m1 i rest b I Hi Hb Hz Hstr) as (SOK & In0 & Iz).
    lstep. lstep. lstep. st_gen [b] by_byte.
    lstep. if_cases Kz; zify_cond Kz.
    - pose proof (Iz Kz) as I2. apply Hz in Kz. eapply (sp_tail _ i); [exact I2| lia| reg_eq| reg_eq].
    - pose proof (In0 Kz) as I2.
      lstep. lstep. lstep. lstep. lstep. lstep. if_cases Kal; zify_cond Kal.
      + eapply (sp_mid (i + 1)%nat _ (skipn 1 rest)); [lia| exact I2| | | reg_eq| reg_eq| reg_eq].
        * rewrite b2z_zero_iff, Z.ltb_ge. lia.
        * intros _. revert Kal. zb_masks. intros Kal. Z.div_mod_to_equations. lia.
      + lstep. lstep. if_cases K1; zify_cond K1.
        * replace (s + Z.of_nat i + 1) with (s + Z.of_nat (i + 1)) by lia.
          replace (s + Z.of_nat i + 2) with (s + Z.of_nat (i + 1) + 1) by lia.
          replace (d + Z.of_nat i + 1) with (d + Z.of_nat (i + 1)) by lia.
          replace (n - Z.of_nat i + -1) with (n - Z.of_nat (i + 1)) by lia.
          apply (IH (i + 1)%nat _ (skipn 1 rest)); try lia; try exact I2; reg_eq.
        * eapply (sp_mid (i + 1)%nat _ (skipn 1 rest)); [lia| exact I2| | | reg_eq| reg_eq| reg_eq].
          -- rewrite b2z_zero_iff, Z.ltb_ge. lia.
          -- rewrite b2z_zero_iff, Z.ltb_ge. intros. exfalso. lia.
  Qed.

  (* ---------- __stpncpy's entry ---------- *)

  Lemma sp_body : forall (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (junk : list byte),
    stk asegs m lo sp2 -> rw_cells asegs m d [CB nn junk] -> bytes_at asegs m s src -> mem_inv asegs m ->
    evt asegs POST
      (MS (mkR ra (Z_to_bv 64 sp2) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 d) (Z_to_bv 64 s) (Z_to_bv 64 n)
               a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x9ad78) fc None m (seg_rom asegs)).
  Proof.
    intros t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 junk STK0 DST0 SRC MI.
    pose proof (rw_cells_CB_length asegs m d nn junk DST0) as LJ.
    apply u8arr_of_rw_cells in DST0.
    pose proof (bytes_at_bound asegs m s src SRC) as BS.
    pose proof (munch_refl WIN m) as MU. pose proof (wmono_refl asegs m) as WM.
    carve_frame 16%nat STK0.
    (* 0x9ad78 addi sp,sp,-16 ; sd ra,8(sp) ; sd s0,0(sp) ; mv s0,a0 *)
    lstep. lstep. lstep. lstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => assert (I : INV mm 0 junk) end.
    { split; [exact DST0|]. split; [lia|]. split; [lia|]. split; [lia|].
      split; [exact SRC| split; [exact MI| split; [exact MU| split; [exact WM| split; [exact STK0| exact FR]]]]]. }
    (* 0x9ad88 xor a3,a1,a0 ; andi a3,a3,7 ; beqz a3 *)
    lstep. lstep. lstep. if_cases Kc; zify_cond Kc.
    - (* the aligned path: 0x9adbc andi a3,a1,7 ; snez a4,a2 ; beqz a3 *)
      lstep. lstep. lstep. if_cases Ksal; zify_cond Ksal.
      + eapply (sp_mid 0 _ junk); [lia| exact I| | | reg_eq| reg_eq| reg_eq].
        * rewrite b2z_zero_iff, Z.ltb_ge. lia.
        * intros _. revert Ksal. zb_masks. intros Ksal. rewrite Z.add_0_r. Z.div_mod_to_equations. lia.
      + lstep. if_cases Kn0; zify_cond Kn0.
        * exfalso. lia.
        * lstep. lstep.
          eapply (sp_head (nn - 0)%nat 0%nat _ junk);
            [lia| lia| exact I| reg_eq| reg_eq| reg_eq| reg_eq| reg_eq].
    - eapply (sp_bentry 0 _ junk); [lia| exact I| reg_eq| reg_eq| reg_eq].
  Qed.

End Proofs.

(* ------------------------------------------------------------------ __stpncpy, both cases *)

Lemma stpncpyA_core : forall (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (d s n sp2 lo : Z) (str src junk : list byte),
  0 <= n < 2^32 -> 0 <= d -> d + n <= 2^47 -> 0 <= s -> s + Z.of_nat (length src) <= 2^47 ->
  17594333495295 < lo -> lo <= sp2 - ISTPN_DEPTH -> sp2 <= 2^47 ->
  ncpy_src s (Z.to_nat n) str src ->
  (d + n <= s \/ s + Z.of_nat (length src) <= d) ->
  (n = 0 \/ s + Z.of_nat (length src) <= lo \/ sp2 + 16 <= s) ->
  (n = 0 \/ d + n <= lo \/ sp2 + 16 <= d) ->
  chk_tails m d n -> ncpy_cells_apart d n -> m2s_cells m -> icells_ms m ->
  stk asegs m lo sp2 -> (0 < n -> rw_cells asegs m d [CB (Z.to_nat n) junk]) ->
  (0 < n -> bytes_at asegs m s src) -> mem_inv asegs m ->
  evt asegs (stpnA_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc d n sp2 lo str m)
    (MS (mkR ra (Z_to_bv 64 sp2) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 d) (Z_to_bv 64 s) (Z_to_bv 64 n)
             a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x9ad78) fc None m (seg_rom asegs)).
Proof using RIP MSZ.
  intros ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6
    F fc m d s n sp2 lo str src junk
    HN HD HDN HS HSH LO0 LOSP SPH SRCOK SEP SEPS SEPD CHK CAP M2S ICM STK0 DST0 SRC MI.
  destruct (Z.eq_dec n 0) as [NZ|NNZ]; [| specialize (DST0 ltac:(lia)); specialize (SRC ltac:(lia))].
  - (* n = 0: no byte is read and none is stored; every path reaches memset(d, 0, 0) *)
    subst n.
    pose proof (munch_refl [(d, d + 0); (sp2 - ISTPN_DEPTH, sp2)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    carve_frame 16%nat STK0.
    (* 0x9ad78 addi sp,sp,-16 ; sd ra,8(sp) ; sd s0,0(sp) ; mv s0,a0 *)
    lstep. lstep. lstep. lstep.
    (* 0x9ad88 xor a3,a1,a0 ; 0x9ad8c andi a3,a3,7 ; 0x9ad90 beqz a3 *)
    lstep. lstep. lstep. if_cases Kc; zify_cond Kc.
    + (* s and d agree on the low 3 bits: 0x9adbc andi a3,a1,7 ; snez a4,a2 ; beqz a3 *)
      lstep. lstep. lstep. if_cases Ksal; zify_cond Ksal.
      * (* 0x9ae04 beqz a4 (a4 = 0) ; 0x9ae58 li a3,0 *)
        lstep. if_true. lstep.
        eapply tail0; try eassumption; try lia; reg_eq.
      * (* 0x9adc8 beqz a2 (n = 0) ; 0x9ae04 beqz a4 ; 0x9ae58 li a3,0 *)
        lstep. if_true. lstep. if_true. lstep.
        eapply tail0; try eassumption; try lia; reg_eq.
    + (* 0x9ad94 beqz a2 (n = 0) ; 0x9ae58 li a3,0 *)
      lstep. if_true. lstep.
      eapply tail0; try eassumption; try lia; reg_eq.
  - eapply sp_body with (src := src) (lo := lo); try eassumption; try lia.
Qed.

(* ------------------------------------------------------------------ strncpy *)

Theorem stpncpyA_proof : strncpyA_stmt.
Proof using RIP MSZ.
  unfold strncpyA_stmt.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m d s n str src junk lo.
  intros -> -> -> STK0 LOSP LOLO SPH HS HD HN HSH HDN SRC SRCOK DST0 SEP SEPS SEPD CHK CAP M2S ICM MI.
  unfold kHighShadowEnd in LOLO.
  set (SP := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 SP) by (symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  assert (RSP : 0 <= SP) by (destruct STK0 as (H1 & _); lia).
  pose proof (munch_refl [(d, d + n); (SP - ISTRNCPYA_DEPTH, SP)] m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 SP) = SP) by (apply unsigned_lit; lia).
  (* The callee's footprint names [d, d + n); with n = 0 that interval is empty but still hides this frame's cells
     from the automatic transport, so that case weakens it to the stack window first.  With n = 0 the destination
     and the source may also lie in this frame, so neither is carried over the frame's stores. *)
  destruct (Z.eq_dec n 0) as [NZ|NNZ].
  - subst n.
    carve_frame 16%nat STK0.
    (* 0x9ad50 addi sp,sp,-16 ; sd ra,8(sp) ; sd s0,0(sp) ; mv s0,a0 ; jal 0x9ad78 *)
    do 5 lstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      destruct (ncpy_carry m mm d 0 (SP - ISTRNCPYA_DEPTH) SP ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                  CHK CAP M2S ICM MU WM) as (CHK1 & M2S1 & IC1) end.
    eapply evt_cut;
    [ eapply stpncpyA_core with (src := src) (junk := junk) (str := str) (lo := lo) (s := s);
      [ lia | lia | lia | lia | lia | lia | lia | lia
      | exact SRCOK | lia | lia | lia
      | exact CHK1 | exact CAP | exact M2S1 | exact IC1
      | eassumption | intros; exfalso; lia | intros; exfalso; lia | eassumption ] |].
    intros ms' PO. destruct_exs PO.
    destruct PO as (E & MUc & WMc & MIc & STc & RWc). subst ms'.
    lazymatch type of MUc with munch _ ?mA ?mB =>
      assert (MUe : munch [(SP + -16 - ISTPN_DEPTH, SP + -16)] mA mB)
        by (eapply munch_weaken; [| exact MUc]; unfold sub_fp; cbn [outside]; intros; repeat split; try exact I; lia);
      clear MUc; transport_after_call asegs mA mB MUe WMc; clear MUe WMc end.
    replace (ret_pc (Z_to_bv 64 0x9ad64)) with (Z_to_bv 64 0x9ad64)
      by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    do 5 lstep.
    try replace (SP + -16 + 16) with SP by lia.
    release_frame FR STc SP.
    unfold strncpyA_post. sys_finish.
    all: rewrite ?EU;
         first [ assumption
               | (eapply munch_weaken; [| eassumption];
                  unfold sub_fp; cbn [outside]; intros; repeat split; try exact I; lia) ].
  - assert (SEPD' : d + n <= lo \/ SP <= d) by (destruct SEPD as [E|H]; [exfalso; lia| exact H]).
    assert (SEPS' : s + Z.of_nat (length src) <= lo \/ SP <= s)
      by (destruct SEPS as [E|H]; [exfalso; lia| exact H]).
    clear SEPD SEPS.
    carve_frame 16%nat STK0.
    (* 0x9ad50 addi sp,sp,-16 ; sd ra,8(sp) ; sd s0,0(sp) ; mv s0,a0 ; jal 0x9ad78 *)
    do 5 lstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      destruct (ncpy_carry m mm d n (SP - ISTRNCPYA_DEPTH) SP ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                  CHK CAP M2S ICM MU WM) as (CHK1 & M2S1 & IC1) end.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      eapply evt_cut;
      [ eapply stpncpyA_core with (src := src) (junk := junk) (str := str) (lo := lo) (s := s);
        first [ exact SRCOK | exact CHK1 | exact CAP | exact M2S1 | exact IC1
              | eassumption | (intros _; eassumption) | lia ]
      | post_call asegs mm ] end.
    (* 0x9ad64 mv a0,s0 ; ld ra,8(sp) ; ld s0,0(sp) ; addi sp,sp,16 ; ret *)
    do 5 lstep.
    try replace (SP + -16 + 16) with SP by lia.
    lazymatch goal with H : stk asegs _ lo (SP + -16) |- _ => release_frame FR H SP end.
    unfold strncpyA_post. sys_finish.
    all: rewrite ?EU;
         first [ assumption
               | (eapply munch_weaken; [| eassumption];
                  unfold sub_fp; cbn [outside]; intros; repeat split; try exact I; lia) ].
Qed.

End WithRIP.
