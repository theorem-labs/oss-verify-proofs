(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib Require Import Tac ZBridge FP Image.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac vmc_refl := first [ lazymatch goal with |- _ = ?b => vm_cast_no_check (@eq_refl _ b) end | vm_compute; reflexivity ].
Definition rsegs := Ubsan.Ubsan_loaded_segments.

Definition PT_BASE : Z := 0x14f40.   Definition PE_BASE : Z := 0x164b8.   Definition KC_CONST : Z := 0x3fd34413509f79fe.
Definition NPOW : nat := 687.
Definition PT_BYTES : list byte := match image_bytes rsegs PT_BASE (8 * NPOW) with Some bs => bs | None => [] end.
Definition PE_BYTES : list byte := match image_bytes rsegs PE_BASE (4 * NPOW) with Some bs => bs | None => [] end.
Definition le_Z (bs : list byte) : Z := bytes_le_to_Z bs.
Definition PTZw (ptb : list byte) (i : Z) : Z := le_Z (firstn 8 (skipn (Z.to_nat (8 * i)) ptb)).
Definition PEZw (peb : list byte) (i : Z) : Z := bv_swrap 32 (le_Z (firstn 4 (skipn (Z.to_nat (4 * i)) peb))).
Definition PTZ (i : Z) : Z := PTZw PT_BYTES i.
Definition PEZ (i : Z) : Z := PEZw PE_BYTES i.

Definition KCW (x : Z) : word := fcvt_w_d RUP (fmul_d RNE (fcvt_d_w RNE (Z_to_bv 64 x)) (Z_to_bv 64 KC_CONST)).
Definition KCZ (x : Z) : Z := bv_signed (KCW x).

Definition kc_okw (peb : list byte) (ple : Z) : bool :=
  let k := KCZ (-50 - ple) in
  (Z.leb (-307) k && Z.leb k 325 && Z.leb (-59) (PEZw peb (k + 343) + ple + 54) && Z.leb (PEZw peb (k + 343) + ple + 54) (-56))%bool.
Definition kc_ok (ple : Z) : bool := kc_okw PE_BYTES ple.
Definition zseq (lo n : Z) : list Z := map (fun i => lo + Z.of_nat i) (seq 0 (Z.to_nat n)).
Lemma zseq_in : forall lo n x, lo <= x < lo + n -> In x (zseq lo n).
Proof.
  intros lo n x Hx. unfold zseq. apply in_map_iff. exists (Z.to_nat (x - lo)). split; [lia|]. apply in_seq. lia.
Qed.
Lemma kc_all : forallb kc_ok (zseq (-1127) 2099) = true.
Proof. change (forallb (kc_okw PE_BYTES) (zseq (-1127) 2099) = true). vm_compute. reflexivity. Qed.
Lemma kc_facts : forall ple, -1127 <= ple <= 971 ->
  -307 <= KCZ (-50 - ple) <= 325 /\ -59 <= PEZ (KCZ (-50 - ple) + 343) + ple + 54 <= -56.
Proof.
  intros ple Hp. pose proof (proj1 (forallb_forall _ _) kc_all ple (zseq_in (-1127) 2099 ple ltac:(lia))) as H.
  unfold kc_ok, kc_okw in H. unfold PEZ. cbv zeta in H. repeat (apply andb_prop in H as [H ?H]).
  repeat match goal with X : (_ <=? _) = true |- _ => apply Z.leb_le in X | X : (_ <? _) = true |- _ => apply Z.ltb_lt in X end. lia.
Qed.

Definition pt_okw (ptb : list byte) (i : Z) : bool := (Z.leb (2 ^ 63) (PTZw ptb i) && Z.ltb (PTZw ptb i) (2 ^ 64))%bool.
Definition pt_ok (i : Z) : bool := pt_okw PT_BYTES i.
Lemma pt_all : forallb pt_ok (zseq 0 687) = true.
Proof. change (forallb (pt_okw PT_BYTES) (zseq 0 687) = true). vm_compute. reflexivity. Qed.
Lemma pt_facts : forall i, 0 <= i < 687 -> 2 ^ 63 <= PTZ i < 2 ^ 64.
Proof.
  intros i Hi. pose proof (proj1 (forallb_forall _ _) pt_all i (zseq_in 0 687 i ltac:(lia))) as H.
  unfold pt_ok, pt_okw in H. unfold PTZ. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia.
Qed.

Lemma PT_len : length PT_BYTES = (8 * NPOW)%nat.
Proof. vmc_refl. Qed.
Lemma PE_len : length PE_BYTES = (4 * NPOW)%nat.
Proof. vmc_refl. Qed.
Lemma PT_ro : ro_bytes_b rsegs PT_BASE PT_BYTES = true.
Proof. vmc_refl. Qed.
Lemma PE_ro : ro_bytes_b rsegs PE_BASE PE_BYTES = true.
Proof. vmc_refl. Qed.
Lemma pt_read : forall m i, mem_inv rsegs m -> 0 <= i < 687 ->
  ov_read_bytes rsegs m (wa (PT_BASE + 8 * i)) 8 = Some (firstn 8 (skipn (Z.to_nat (8 * i)) PT_BYTES)).
Proof.
  intros m i MI Hi. pose proof (ro_cells_image rsegs m PT_BASE PT_BYTES MI PT_ro ltac:(unfold PT_BASE; lia) ltac:(rewrite PT_len; unfold PT_BASE, NPOW; lia)) as RO.
  destruct RO as [_ RO]. cbn [cells_bytes cbytes] in RO. rewrite app_nil_r in RO.
  apply bytes_at_read; [exact RO | lia | rewrite PT_len; unfold NPOW; lia].
Qed.
Lemma pe_read : forall m i, mem_inv rsegs m -> 0 <= i < 687 ->
  ov_read_bytes rsegs m (wa (PE_BASE + 4 * i)) 4 = Some (firstn 4 (skipn (Z.to_nat (4 * i)) PE_BYTES)).
Proof.
  intros m i MI Hi. pose proof (ro_cells_image rsegs m PE_BASE PE_BYTES MI PE_ro ltac:(unfold PE_BASE; lia) ltac:(rewrite PE_len; unfold PE_BASE, NPOW; lia)) as RO.
  destruct RO as [_ RO]. cbn [cells_bytes cbytes] in RO. rewrite app_nil_r in RO.
  apply bytes_at_read; [exact RO | lia | rewrite PE_len; unfold NPOW; lia].
Qed.

Lemma u_of_signed : forall w : word, bv_unsigned w = bv_signed w mod 2 ^ 64.
Proof.
  intros w. pose proof (bv_unsigned_in_range 64 w) as R. unfold bv_signed, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus in *. cbn -[Z.pow] in *.
  rewrite Zminus_mod_idemp_l. replace (bv_unsigned w + 2 ^ 64 / 2 - 2 ^ 64 / 2) with (bv_unsigned w) by lia.
  rewrite Z.mod_small by lia. reflexivity.
Qed.

Definition MULT (x c : Z) : Z := (x * c + 2 ^ 63) / 2 ^ 64.
Lemma mult_code : forall xh xl ch cl, 0 <= xh < 2 ^ 32 -> 0 <= xl < 2 ^ 32 -> 0 <= ch < 2 ^ 32 -> 0 <= cl < 2 ^ 32 ->
  ch * xh + (cl * xh) / 2 ^ 32 + (ch * xl) / 2 ^ 32 + ((cl * xh) mod 2 ^ 32 + (cl * xl) / 2 ^ 32 + (ch * xl) mod 2 ^ 32 + 2 ^ 31) / 2 ^ 32
  = MULT (xh * 2 ^ 32 + xl) (ch * 2 ^ 32 + cl).
Proof.
  intros xh xl ch cl Hxh Hxl Hch Hcl. unfold MULT.
  assert (E : (xh * 2 ^ 32 + xl) * (ch * 2 ^ 32 + cl) = (ch * xh) * 2 ^ 64 + (cl * xh) * 2 ^ 32 + (ch * xl) * 2 ^ 32 + cl * xl) by ring.
  rewrite E. clear E.
  set (ac := ch * xh). set (ad := cl * xh). set (bc := ch * xl). set (bd := cl * xl).
  assert (Rac : 0 <= ac) by (apply Z.mul_nonneg_nonneg; lia).
  assert (Rad : 0 <= ad) by (apply Z.mul_nonneg_nonneg; lia).
  assert (Rbc : 0 <= bc) by (apply Z.mul_nonneg_nonneg; lia).
  assert (Rbd : 0 <= bd) by (apply Z.mul_nonneg_nonneg; lia).
  pose proof (Z.div_mod ad (2 ^ 32) ltac:(lia)) as Dad. pose proof (Z.mod_pos_bound ad (2 ^ 32) ltac:(lia)) as Mad.
  pose proof (Z.div_mod bc (2 ^ 32) ltac:(lia)) as Dbc. pose proof (Z.mod_pos_bound bc (2 ^ 32) ltac:(lia)) as Mbc.
  pose proof (Z.div_mod bd (2 ^ 32) ltac:(lia)) as Dbd. pose proof (Z.mod_pos_bound bd (2 ^ 32) ltac:(lia)) as Mbd.
  set (T := ad mod 2 ^ 32 + bd / 2 ^ 32 + bc mod 2 ^ 32 + 2 ^ 31).
  assert (RT : 0 <= T) by (unfold T; pose proof (Z.div_pos bd (2 ^ 32) ltac:(lia) ltac:(lia)); lia).
  pose proof (Z.div_mod T (2 ^ 32) ltac:(lia)) as DT. pose proof (Z.mod_pos_bound T (2 ^ 32) ltac:(lia)) as MT.
  apply Z.div_unique with (r := (T mod 2 ^ 32) * 2 ^ 32 + bd mod 2 ^ 32); [lia|].
  unfold T in *. lia.
Qed.
Lemma mult_mono : forall x y c, 0 <= x <= y -> 0 <= c -> MULT x c <= MULT y c.
Proof. intros x y c Hx Hc. unfold MULT. apply Z.div_le_mono; [lia|]. pose proof (Z.mul_le_mono_nonneg_r x y c ltac:(lia) ltac:(lia)). lia. Qed.
Lemma mult_lo : forall x c, 2 ^ 61 <= x -> 2 ^ 63 <= c -> 2 ^ 60 <= MULT x c.
Proof.
  intros x c Hx Hc. unfold MULT. apply Z.div_le_lower_bound; [lia|].
  assert (2 ^ 61 * 2 ^ 63 <= x * c) by (apply Z.mul_le_mono_nonneg; lia). lia.
Qed.
Lemma mult_lo62 : forall x c, 2 ^ 63 <= x -> 2 ^ 63 <= c -> 2 ^ 62 <= MULT x c.
Proof.
  intros x c Hx Hc. unfold MULT. apply Z.div_le_lower_bound; [lia|].
  assert (2 ^ 63 * 2 ^ 63 <= x * c) by (apply Z.mul_le_mono_nonneg; lia). lia.
Qed.
Lemma mult_hi : forall x c, 0 <= x < 2 ^ 64 -> 0 <= c < 2 ^ 64 -> MULT x c <= 2 ^ 64 - 2.
Proof.
  intros x c Hx Hc. unfold MULT. assert (H : (x * c + 2 ^ 63) / 2 ^ 64 < 2 ^ 64 - 1); [|lia]. apply Z.div_lt_upper_bound; [lia|].
  assert (x * c <= (2 ^ 64 - 1) * (2 ^ 64 - 1)) by (apply Z.mul_le_mono_nonneg; lia). lia.
Qed.

