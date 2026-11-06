(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 3817 of its 3853 lines of code are new or changed and 212 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/ctrl_lay_block.v, with its module names changed; 85 of its 151 lines of code are new or changed and 3787 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/reac_box_catalogue_match_lib.v, with its module paths changed; 255 of its 299 lines of code are new or changed and 107 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_pin/lib/Prog/fuzz_catalogue_row.v, with its module names changed; 601 of its 675 lines of code are new or changed and 225 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_pin/lib/Prog/reac_box_pin_parse.v, with its module paths and numbers changed; 236 of its 280 lines of code are new or changed and 631 lines of the source are left out. *)
(** pod_write_ent (UBSan build, 0x14b5c, 91 instructions): proof of [pod_write_ent_contract]
    (U/Prog/pod_write_ent_c.v) from the contracts of its two callees, memcpy (U/Prog/memcpy_c.v) and memset
    (U/Prog/memset_c.v).

    Shape: one straight path. The prologue saves ra, s0, s1, s2 in the 32-byte frame; the alignment checks of e and
    pp fall through (e mod 4 = 0, pp mod 8 = 0); each of the four puts (size word, type word, body, pad) passes its
    capacity guard (len + n <= 16384) and its two bounds checks (offset < 16385, pp + offset does not wrap), stores
    its bytes at pp + len and adds its length to the len cell; memcpy copies the body and memset writes the pad;
    the epilogue restores the frame and returns. None of the ten branches to the trap at 0x14cc4 is taken.

    The buffer [pp + len, pp + len + n) is split into its four parts before the walk: the 8 header bytes (written by
    eight byte stores), the body (memcpy's destination) and the pad (memset's destination). The header bytes are the
    little-endian bytes of the loaded words, so they are le32 e_size ++ le32 e_type. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Cursor Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog Require Import memcpy_c memset_c pod_write_ent_c.
Import ListNotations.
Open Scope Z_scope.

(** ** Cells *)
Section WithSegs.
Variable segs : list Segment.

Lemma pw_rw_split : forall m A cs1 cs2, rw_cells segs m A (cs1 ++ cs2) ->
  rw_cells segs m A cs1 /\ rw_cells segs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros m A cs1 cs2 [[Hwf Hb] Hw]. apply cells_wf_app in Hwf as [W1 W2].
  rewrite cells_bytes_app in Hb. apply bytes_at_app in Hb as [B1 B2].
  rewrite cells_size_app in Hw. destruct Hw as (Ha & Hn & Hw).
  rewrite (cells_bytes_length cs1 W1) in B2.
  split.
  - split; [split; assumption|]. split; [lia|]. split; [lia|]. intros i Hi. apply Hw. lia.
  - split; [split; assumption|]. split; [lia|]. split; [lia|]. intros i Hi.
    replace (A + Z.of_nat (cells_size cs1) + i) with (A + (Z.of_nat (cells_size cs1) + i)) by lia.
    apply Hw. lia.
Qed.

(** The body bytes of a struct pod_ent held as cells. *)
Lemma pw_body_at : forall m A x y bs, ro_cells segs m A [C4 x; C4 y; CB 96 bs] -> bytes_at segs m (A + 8) bs.
Proof.
  intros m A x y bs [_ H]. cbn [cells_bytes cbytes] in H. rewrite app_nil_r in H.
  apply bytes_at_app in H as [_ H]. rewrite length_le4 in H.
  apply bytes_at_app in H as [_ H]. rewrite length_le4 in H.
  replace (A + Z.of_nat 4 + Z.of_nat 4) with (A + 8) in H by lia. exact H.
Qed.

End WithSegs.

(** ** Bytes and words *)
Lemma pw_le4 : forall v, le4 (Z_to_bv 64 v) = le32 v.
Proof. intros v. unfold le4, le32. rewrite unsigned_lit_wrap. apply Z_to_le_bytes_mod. cbn; lia. Qed.

Lemma pw_le1 : forall v : word, le1 v = [Z_to_bv 8 (bv_unsigned v)].
Proof. reflexivity. Qed.

Lemma pw_land3 : forall x, Z.land x 3 = x mod 4.
Proof. intros x. change 3 with (Z.ones 2). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma pw_land7 : forall x, Z.land x 7 = x mod 8.
Proof. intros x. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma pw_zx32 : forall x, 0 <= x < 2^32 -> zx32 (Z_to_bv 64 x) = Z_to_bv 64 x.
Proof. intros x Hx. unfold zx32. rewrite unsigned_lit by lia. rewrite Z.mod_small by lia. reflexivity. Qed.

Lemma pw_swrap32 : forall z, bv_swrap 32 z mod 2^32 = z mod 2^32.
Proof.
  intros z. unfold bv_swrap, bv_wrap. change (bv_modulus 32) with (2^32).
  rewrite Zminus_mod_idemp_l. f_equal. lia.
Qed.

Lemma pw_swrap_land7 : forall w, Z.land (bv_unsigned (Z_to_bv 64 (bv_swrap 32 w))) 7 = w mod 8.
Proof.
  intros w. rewrite unsigned_lit_wrap, pw_land7.
  rewrite Z.mod_mod_divide by (exists (2^61); reflexivity).
  rewrite <- (Z.mod_mod_divide (bv_swrap 32 w) (2^32) 8) by (exists (2^29); reflexivity).
  rewrite pw_swrap32. apply Z.mod_mod_divide. exists (2^29); reflexivity.
Qed.

Lemma pw_le4_eqm : forall x y, x mod 2^32 = y mod 2^32 -> Z_to_le_bytes 4 x = Z_to_le_bytes 4 y.
Proof.
  intros x y H. rewrite <- (Z_to_le_bytes_mod 4 x 32) by (cbn; lia).
  rewrite <- (Z_to_le_bytes_mod 4 y 32) by (cbn; lia). rewrite H. reflexivity.
Qed.

(** The four bytes a lw result is stored as, by sb of it and of its shifts right by 8, 16 and 24. *)
Lemma pw_word4 : forall z, 0 <= z < 2^64 ->
  [Z_to_bv 8 z; Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (Z.shiftr z 8)));
   Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (Z.shiftr z 16))); Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (Z.shiftr z 24)))]
  = Z_to_le_bytes 4 z.
Proof.
  intros z Hz. cbn [Z_to_le_bytes].
  replace (Z.shiftr (Z.shiftr z 8) 8) with (Z.shiftr z 16) by (rewrite Z.shiftr_shiftr by lia; reflexivity).
  replace (Z.shiftr (Z.shiftr z 16) 8) with (Z.shiftr z 24) by (rewrite Z.shiftr_shiftr by lia; reflexivity).
  rewrite !(unsigned_lit (Z.shiftr z _)) by (apply (zr_shiftr z); [exact Hz | lia]).
  reflexivity.
Qed.

Lemma pw_sx32_bytes : forall v, Z_to_le_bytes 4 (bv_unsigned (sx32 (Z_to_bv 64 v))) = le32 v.
Proof.
  intros v. unfold le32. apply pw_le4_eqm. unfold sx32. rewrite !unsigned_lit_wrap.
  rewrite Z.mod_mod_divide by (exists (2^32); reflexivity).
  rewrite pw_swrap32. apply Z.mod_mod_divide. exists (2^32); reflexivity.
Qed.

(** A struct pod_ent in memory, held as cells: type word, size word, the 96-byte body. *)
Lemma pw_ent_cells : forall segs m A T sz body, length body = sz -> (sz <= 96)%nat ->
  bytes_at segs m A (ent_mem (Ent T (Z.of_nat sz) body)) ->
  ro_cells segs m A [C4 (Z_to_bv 64 T); C4 (Z_to_bv 64 (Z.of_nat sz)); CB 96 (body ++ zeros (96 - sz))].
Proof.
  intros segs m A T sz body Hl H96 H. split.
  - cbn [cells_wf cell_wf]. rewrite length_app, length_zeros. repeat split; lia.
  - cbn [cells_bytes cbytes]. rewrite app_nil_r, !pw_le4. unfold ent_mem in H. cbn [e_type e_size e_body] in H.
    rewrite Hl in H. exact H.
Qed.

(** The bytes pod_write_ent leaves at pp + len, from its four parts. *)
Lemma pw_enc : forall segs m B T sz pd body cs zs,
  rw_cells segs m B cs -> cells_bytes cs = le32 (Z.of_nat sz) ++ le32 T ->
  rw_cells segs m (B + 8) [CB sz body] -> rw_cells segs m (B + 8 + Z.of_nat sz) [CB pd zs] ->
  zs = zeros pd -> Z.of_nat pd = pad8 (Z.of_nat sz) ->
  bytes_at segs m B (enc_pod (Ent T (Z.of_nat sz) body)).
Proof.
  intros segs m B T sz pd body cs zs H1 E1 H2 H3 E3 Hpd.
  destruct H1 as [[_ B1] _]. rewrite E1 in B1.
  destruct H2 as [[W2 B2] _]. cbn [cells_bytes cbytes] in B2. rewrite app_nil_r in B2.
  cbn [cells_wf cell_wf] in W2. destruct W2 as [W2 _].
  destruct H3 as [[_ B3] _]. cbn [cells_bytes cbytes] in B3. rewrite app_nil_r, E3 in B3.
  unfold enc_pod. cbn [e_size e_type e_body].
  rewrite <- Hpd, Nat2Z.id.
  rewrite app_assoc. apply bytes_at_app. split; [exact B1|].
  rewrite length_app, !length_le32.
  apply bytes_at_app. split.
  - replace (B + Z.of_nat (4 + 4)) with (B + 8) by lia. exact B2.
  - rewrite W2. replace (B + Z.of_nat (4 + 4) + Z.of_nat sz) with (B + 8 + Z.of_nat sz) by lia. exact B3.
Qed.

(** ** Branch conditions *)
Ltac pw_ul := repeat match goal with |- context [bv_unsigned (Z_to_bv 64 ?x)] => rewrite (unsigned_lit x) by lia end.
Ltac pw_base := first [ reflexivity | apply Z.ltb_ge; mlia | apply Z.ltb_lt; mlia
                      | apply Z.eqb_eq; mlia | apply Z.eqb_neq; mlia ].
Ltac pw_rec := lazymatch goal with
  | |- negb _ = true => apply (proj2 (Bool.negb_true_iff _)); pw_rec
  | |- negb _ = false => apply (proj2 (Bool.negb_false_iff _)); pw_rec
  | _ => pw_base
  end.
Ltac pw_cond := unfold bv_eqb, bv_ltu, bv_lts, bv_leu; cbn [negb]; fold_lit_ux;
  rewrite ?pw_land3, ?pw_land7; pw_ul; rewrite ?zb_lxor_ones by lia; pw_ul;
  rewrite ?unsigned_lit_wrap; change (2^64) with 18446744073709551616; pw_rec.
(** Every branch of this walk is not taken. *)
Ltac pw_go := lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      first [ replace c with false; [cbv iota | symmetry; pw_cond]
            | idtac "PW_GO_FAIL" c; fail 1 ]
  | |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PW_GO_NOIF" pc; fail 1
  end.
(** A byte store: its value is a word's low byte. *)
Ltac sb_step := step; rewrite pw_le1; mem_after_store.

(** ** The walk *)
Section Walk.
Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
  (T : Z) (body : list byte) (sz pd : nat) (len P Ea Sp lo : Z).

Definition pw_post (m0 : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                    (m' : word -> option byte),
    ms' = MS (mkR ra (Z_to_bv 64 Sp) gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom rsegs) /\
    munch [(Sp - 32, Sp); (P + len, P + len + Z.of_nat (8 + sz + pd)); (P + 16384, P + 16384 + 8)] m0 m' /\
    wmono rsegs m0 m' /\ mem_inv rsegs m' /\ stk rsegs m' lo Sp /\
    bytes_at rsegs m' (P + len) (enc_pod (Ent T (Z.of_nat sz) body)) /\
    bytes_at rsegs m' (P + 16384) (le8 (Z_to_bv 64 (len + Z.of_nat (8 + sz + pd)))).

Lemma walk : memcpy_contract -> memset_contract ->
  forall (m0 : word -> option byte) (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (j1 j2 j3 : list byte) (B : Z),
  B = P + len -> 0 <= len -> len mod 8 = 0 -> len + 8 + Z.of_nat sz + Z.of_nat pd <= 16384 ->
  (sz <= 96)%nat -> length body = sz -> Z.of_nat pd = pad8 (Z.of_nat sz) ->
  P mod 8 = 0 -> 0 <= P -> P + 16392 <= 2^64 ->
  Ea mod 4 = 0 -> 0 <= Ea -> Ea + 104 <= 2^64 ->
  (P + 16392 <= Ea \/ Ea + 104 <= P) -> (P + 16392 <= lo \/ Sp <= P) -> (Ea + 104 <= lo \/ Sp <= Ea) ->
  0 <= lo -> lo + 32 <= Sp -> Sp < 2^64 ->
  rw_cells rsegs m0 (P + 16384) [C8 (Z_to_bv 64 len)] ->
  rw_cells rsegs m0 B [CB 8 j1] -> rw_cells rsegs m0 (B + 8) [CB sz j2] ->
  rw_cells rsegs m0 (B + 8 + Z.of_nat sz) [CB pd j3] ->
  ro_cells rsegs m0 Ea [C4 (Z_to_bv 64 T); C4 (Z_to_bv 64 (Z.of_nat sz)); CB 96 (body ++ zeros (96 - sz))] ->
  stk rsegs m0 lo Sp -> mem_inv rsegs m0 ->
  evt rsegs (pw_post m0)
    (MS (mkR ra (Z_to_bv 64 Sp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 P) (Z_to_bv 64 Ea) a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x14b5c) fc None m0 (seg_rom rsegs)).
Proof.
  intros HMC HMS m0 t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 j1 j2 j3 B HB Hl0 Hl8 Hcap Hsz Hbody Hpd HP8 HP0 HPe HE4
    HE0 HEe HPE HPS HES Hlo HK HS HLEN H8 HBODY HPAD HE ST MI.
  pose proof (Nat2Z.is_nonneg sz) as Hsz0. pose proof (Nat2Z.is_nonneg pd) as Hpd0.
  carve_frame 32%nat ST.
  pose proof (munch_refl [(Sp - 32, Sp); (B, B + (8 + Z.of_nat sz + Z.of_nat pd)); (P + 16384, P + 16384 + 8)] m0)
    as MU.
  pose proof (wmono_refl rsegs m0) as WM.
  (* 0x14b5c-0x14b6c: the frame *)
  do 5 step.
  (* 0x14b70-0x14b74: e & 3 *)
  step. step. pw_go.
  (* 0x14b78-0x14b80: pp & 7 *)
  do 3 step. pw_go.
  clear HP8 HE4.
  (* 0x14b84-0x14b8c: s2 = pp + 0x4000, a0 = len *)
  do 3 step.
  (* 0x14b90-0x14ba0: the capacity guard of the size word *)
  do 5 step. pw_go.
  (* 0x14ba4-0x14bb0: len < 16385, pp + len does not wrap *)
  step. step. pw_go.
  step. step. pw_go.
  (* 0x14bb4-0x14bd4: the size word at pp + len *)
  step. step. rewrite <- HB.
  do 3 step.
  sb_step. sb_step. sb_step. sb_step.
  (* 0x14bd8-0x14bf0: len += 4, the capacity guard of the type word *)
  do 7 step. pw_go.
  (* 0x14bf4-0x14c00: the bounds checks at len + 4 *)
  do 3 step. pw_go.
  step. pw_go.
  (* 0x14c04-0x14c24: the type word at pp + len + 4 *)
  step. step. replace (P + (len + 4)) with (B + 4) by lia.
  do 3 step.
  sb_step. sb_step. sb_step. sb_step.
  (* 0x14c28-0x14c30: len += 4 *)
  do 3 step.
  (* 0x14c34: s1 = e->size *)
  step. rewrite (pw_zx32 (Z.of_nat sz)) by lia.
  (* 0x14c38-0x14c4c: the capacity guard of the body, the bounds checks at len + 8 *)
  step. step. pw_go.
  step. step. pw_go.
  step. step. pw_go.
  (* 0x14c50-0x14c5c: memcpy(pp + len + 8, e + 8, size) *)
  step. step. replace (P + (len + 8)) with (B + 8) by lia. step. step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mA end.
  pose proof (pw_body_at rsegs mA Ea _ _ _ HE) as HSRC. apply bytes_at_app in HSRC as [HSRC _].
  eapply evt_cut.
  { eapply HMC with (src := body); rewrite ?unsigned_lit by lia.
    - exact HSRC.
    - rewrite Nat2Z.id. exact Hbody.
    - rewrite Nat2Z.id. exact HBODY.
    - lia.
    - exact MI. }
  intros ms' PO. unfold memcpy_post in PO.
  destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & mB & -> &
                  MU1 & WM1 & MI1 & RW1 & _).
  rewrite !unsigned_lit in MU1, RW1 by lia. rewrite Nat2Z.id in RW1.
  rewrite ret_pc_even by (try lia; reflexivity).
  clear HE HSRC.
  transport_after_call rsegs mA mB MU1 WM1.
  clear MU1 WM1 MI. clear mA.
  (* 0x14c60-0x14c70: len += size, s1 = the pad *)
  do 5 step.
  match goal with |- context [Z.land (bv_unsigned (Z_to_bv 64 (bv_swrap 32 ?w))) 7] =>
    replace (Z.land (bv_unsigned (Z_to_bv 64 (bv_swrap 32 w))) 7) with (Z.of_nat pd)
      by (rewrite pw_swrap_land7; pw_ul; unfold pad8 in Hpd; mlia)
  end.
  clear Hl8.
  (* 0x14c74-0x14c8c: the capacity guard of the pad, the bounds checks at len + 8 + size *)
  do 3 step. pw_go.
  step. step. pw_go.
  step. step. pw_go.
  (* 0x14c90-0x14c9c: memset(pp + len + 8 + size, 0, pad) *)
  step. replace (P + (len + 8 + Z.of_nat sz)) with (B + 8 + Z.of_nat sz) by lia. do 3 step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mC end.
  eapply evt_cut.
  { eapply HMS; rewrite ?unsigned_lit by lia.
    - rewrite Nat2Z.id. exact HPAD.
    - exact MI1. }
  intros ms' PO. unfold memset_post in PO.
  destruct PO as (t0'' & t1'' & t2'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' &
                  mD & -> & MU2 & WM2 & MI2 & RW2).
  rewrite !unsigned_lit in MU2, RW2 by lia. rewrite Nat2Z.id in RW2.
  rewrite ret_pc_even by (try lia; reflexivity).
  transport_after_call rsegs mC mD MU2 WM2.
  clear MU2 WM2 MI1. clear mC.
  (* 0x14ca0-0x14ca8: len += pad; 0x14cac-0x14cc0: the epilogue *)
  do 9 step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mE end.
  apply evt_done. unfold pw_post. cbv beta.
  do 15 eexists. exists mE.
  split; [reflexivity|].
  replace (Z.of_nat (8 + sz + pd)) with (8 + Z.of_nat sz + Z.of_nat pd) by lia.
  subst B.
  split; [exact MU|]. split; [exact WM|]. split; [exact MI2|].
  split; [release_frame FR ST Sp; exact ST|].
  split.
  - eapply pw_enc; [exact H8 | | exact RW1 | exact RW2 | reflexivity | exact Hpd].
    cbn [cells_bytes cbytes app].
    rewrite <- (pw_sx32_bytes (Z.of_nat sz)), <- (pw_sx32_bytes T).
    rewrite <- !pw_word4 by (exact (zr_word _)).
    reflexivity.
  - destruct HLEN as [[_ HL] _]. cbn [cells_bytes cbytes] in HL. rewrite app_nil_r in HL.
    eapply bytes_at_ext; [exact HL|]. f_equal. f_equal. lia.
Qed.

End Walk.

(** ** The contract *)
Theorem pod_write_ent_holds : memcpy_contract -> memset_contract -> pod_write_ent_contract.
Proof.
  intros HMC HMS. unfold pod_write_ent_contract, PWE_LEN, PWE_REC, PWE_ENT, PWE_BODY, PWE_STACK.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m e len
    junk lo HP8 HLEN Hl0 Hl8 Hcap HBUF HE4 HE Hsz Hsz96 HPE ST HK HW HPS HES MI.
  clear HW.
  destruct e as [T S body]. cbn [e_size e_type e_body] in Hsz, Hsz96.
  remember (length body) as sz eqn:Esz. subst S.
  remember (Z.to_nat (pad8 (Z.of_nat sz))) as pd eqn:Epd.
  assert (Hpd : Z.of_nat pd = pad8 (Z.of_nat sz)).
  { subst pd. apply Z2Nat.id. unfold pad8. apply Z.mod_pos_bound. lia. }
  assert (HN : length (enc_pod (Ent T (Z.of_nat sz) body)) = (8 + sz + pd)%nat).
  { unfold enc_pod. cbn [e_size e_type e_body]. rewrite !length_app, !length_le32, length_zeros.
    rewrite <- Esz, <- Epd. lia. }
  rewrite HN in Hcap, HBUF |- *.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. pose proof (bv_unsigned_in_range 64 a0) as Ra0.
  pose proof (bv_unsigned_in_range 64 a1) as Ra1.
  change (bv_modulus 64) with (2^64) in Rsp, Ra0, Ra1.
  pose proof (Z_to_bv_lit_self sp) as Esp. pose proof (Z_to_bv_lit_self a0) as Ea0.
  pose proof (Z_to_bv_lit_self a1) as Ea1.
  set (Sp := bv_unsigned sp) in *. set (P := bv_unsigned a0) in *. set (Ea := bv_unsigned a1) in *.
  rewrite <- Esp, <- Ea0, <- Ea1. clearbody Sp P Ea. clear Esp Ea0 Ea1.
  pose proof (rw_cells_bound rsegs m _ _ HLEN) as BL. cbn [cells_size csize Nat.add] in BL.
  pose proof (bytes_at_bound rsegs m _ _ HE) as BE.
  rewrite length_ent_mem in BE by (cbn [e_body]; lia).
  pose proof (proj1 ST) as Hlo.
  apply (pw_ent_cells rsegs m Ea T sz body) in HE; [| symmetry; exact Esz | lia].
  apply (rw_cells_split_CB rsegs m _ [] _ junk [] [8; sz; pd]%nat) in HBUF; [| cbn [sum_nat]; lia].
  cbn [app mk_CB_cells] in HBUF.
  destruct (pw_rw_split rsegs m _ [CB 8 _] _ HBUF) as [H8 HR].
  cbn [cells_size csize Nat.add] in HR. change (Z.of_nat 8) with 8 in HR.
  destruct (pw_rw_split rsegs m _ [CB sz _] _ HR) as [HBD HPD].
  cbn [cells_size csize] in HPD. rewrite Nat.add_0_r in HPD.
  clear HBUF HR.
  eapply (walk ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc T body sz pd len P Ea Sp lo HMC HMS m
            t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 _ _ _ (P + len));
    [ reflexivity | exact Hl0 | exact Hl8 | lia | lia | symmetry; exact Esz | exact Hpd | exact HP8 | lia | lia
    | exact HE4 | lia | lia | exact HPE | exact HPS | exact HES | lia | lia | lia
    | exact HLEN | exact H8 | exact HBD | exact HPD | exact HE | exact ST | exact MI ].
Qed.
