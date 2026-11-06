(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: relocated from the walk of the same function of libreac's fuzz_grant (the two are the same code at other addresses); the caller's memory is kept by pz_kept_run with the out struct's off_img premise in place of its caller frame. *)
(* Modified by Theorem Labs, 2026-10: the asan-ubsan twin, for fuzz_disco.asan-ubsan (lib_both3_0_listing, reac_ctrl_parse at 0x874a4): ported from a working branch edc3e948664 fuzz_grant/lib/B/Prog/CtrlParseTail1.v (fuzz_grant image B's walk of the same code, relocated: Y pc = grant B pc + 0x4d30; its extra UBSan guards are decided by the engine from the atom facts), on the fuzz_disco plumbing of lib/A/Prog/CtrlParseTail1.v (a working branch 9c6f061fccb) over lib/Y/Prog/CtrlParseCut.v. *)
(* reac_ctrl_parse, the walk from cut B (0x876a0) to cut J for the frames of class 1 (pz_P1):
   FILLER (1), MASTER_ANNOUNCE (4) and SPLIT_ANNOUNCE (8): frame type 00 00, cf ea or ce ea.
   From cut B the walk stores is_broadcast (out + 16), the counter (out + 20), link and segment (out + 22, 23),
   blk_len (out + 24) and the opcode (out + 26), each store after its shadow check and its UBSan pointer-overflow
   check, then compares the frame type bytes f[16] and f[17]: 0x878a0 (f[16] | f[17] <> 0), 0x879bc (f[16] <> 0xcf),
   0x879c4 (f[17] <> 0xea), 0x879e4 (f[16] <> 0xce), 0x879ec (f[17] <> 0xea). The three class-1 outcomes store the
   kind at 0x87a70 and jump to cut J (0x878c4); the outcomes 0x879c4 taken, 0x879e4 taken and 0x879ec taken
   contradict pz_P1. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YG0s YM05 YI16 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YO0a.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP0b YP0a YP0c YP0d YP07 YC80 YI0w YI0z YI12 YC4a YC1f YC44 YC8g YC8i.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YC1g YC1h YC81 YC4b YC45 YC85 YC88.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import RcKind RcParse.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YRo YCkd YCjr YCj1 YCja.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import CtrlParse CtrlParseLib KindOfLink1.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import CtrlParseCut.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
#[local] Ltac Zify.zify_pre_hook ::= try unfold YImgTop.IMG_TOP, YImgTop.IMG_LO in *.
(* The out struct at cut J on the three class-1 paths: the kind k (4 bytes), the two copies of the address
   bytes (cut B), is_broadcast (seqz of atom 640), the counter f14 f15, link f18, segment f19, blk_len f21 f20,
   the opcode f22 and zeros. *)
Definition pt1_out (k : Z) : list YP09.chunk :=
[YP09.mkChunk 0 (CVal 4 (SLit k)); YP09.mkChunk 26 (CVal 1 (SOff 62 0));
 YP09.mkChunk 24 (CVal 2 (SAlu ALU_OR (SAlu ALU_SLL (SOff 60 0) (SLit 8)) (SOff 61 0)));
 YP09.mkChunk 23 (CVal 1 (SOff 59 0)); YP09.mkChunk 22 (CVal 1 (SOff 58 0));
 YP09.mkChunk 20 (CVal 2 (SAlu ALU_OR (SAlu ALU_SLL (SOff 55 0) (SLit 8)) (SOff 54 0)));
 YP09.mkChunk 16 (CVal 4 (SAlu ALU_SLTU (SOff 640 0) (SLit 1)));
 YP09.mkChunk 4 (CVal 1 (SOff 46 0)); YP09.mkChunk 5 (CVal 1 (SOff 47 0)); YP09.mkChunk 6 (CVal 1 (SOff 48 0));
 YP09.mkChunk 7 (CVal 1 (SOff 49 0)); YP09.mkChunk 8 (CVal 1 (SOff 50 0)); YP09.mkChunk 9 (CVal 1 (SOff 51 0));
 YP09.mkChunk 10 (CVal 1 (SOff 40 0)); YP09.mkChunk 11 (CVal 1 (SOff 41 0)); YP09.mkChunk 12 (CVal 1 (SOff 42 0));
 YP09.mkChunk 13 (CVal 1 (SOff 43 0)); YP09.mkChunk 14 (CVal 1 (SOff 44 0)); YP09.mkChunk 15 (CVal 1 (SOff 45 0));
 YP09.mkChunk 27 (CZero 9)].
(* The chunk that covers an offset: its offset, its value and the index inside it. *)
Fixpoint pt1_find (cs : list YP09.chunk) (off : Z) : option (Z * cval * Z) :=
match cs with
| [] => None
| c :: t => if (YP09.c_off c <=? off) && (off <? YP09.c_off c + YP09.c_len c)
  then Some (YP09.c_off c, YP09.c_val c, off - YP09.c_off c) else pt1_find t off
end.
Lemma pt1_lor : forall a b, 0 <= a -> 0 <= b < 256 -> Z.lor (a * 256) b = a * 256 + b.
Proof.
intros a b Ha Hb.
assert (HL : Z.land (a * 256) b = 0).
{ apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
  destruct (Z.lt_ge_cases i 8) as [Hi8|Hi8].
  - change 256 with (2 ^ 8). rewrite Z.mul_pow2_bits_low by lia. reflexivity.
  - rewrite <- (Z.mod_small b (2 ^ 8)) by (cbn; lia). rewrite Z.mod_pow2_bits_high by lia. apply andb_false_r. }
rewrite <- (Z.lxor_lor _ _ HL). symmetry. apply Z.add_nocarry_lxor. exact HL.
Qed.
Lemma pt1_land255 : forall v, 0 <= v < 256 -> Z.land v 255 = v.
Proof. intros v Hv. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_small. change (2 ^ 8) with 256. lia. Qed.
Lemma pt1_bv8 : forall x (b : byte), x mod 256 = bv_unsigned b -> Z_to_bv 8 x = b.
Proof. intros x b H. apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. exact H. Qed.
Lemma pt1_byte0 : forall E e, byte_of_word (sv_denot E e) 0 = Z_to_bv 8 (U E e).
Proof. intros E e. unfold byte_of_word, U. rewrite Z.mul_0_r, Z.shiftr_0_r. reflexivity. Qed.
Lemma pt1_byte1 : forall E e, byte_of_word (sv_denot E e) 1 = Z_to_bv 8 (U E e / 256).
Proof. intros E e. unfold byte_of_word, U. rewrite Z.shiftr_div_pow2 by lia. reflexivity. Qed.
Lemma pt1_bytej : forall E e j, 0 <= U E e < 256 -> 1 <= j -> byte_of_word (sv_denot E e) j = cp_z.
Proof.
intros E e j HU Hj. unfold byte_of_word. change (bv_unsigned (sv_denot E e)) with (U E e).
rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_small; [reflexivity|].
assert (H8 : 2 ^ 8 <= 2 ^ (8 * j)) by (apply Z.pow_le_mono_r; lia). change (2 ^ 8) with 256 in H8. lia.
Qed.
Lemma pt1_bk0 : forall E k, 0 <= k < 256 -> byte_of_word (sv_denot E (SLit k)) 0 = Z_to_bv 8 k.
Proof. intros E k Hk. rewrite pt1_byte0, U_lit by lia. reflexivity. Qed.
Lemma pt1_bkj : forall E k j, 0 <= k < 256 -> 1 <= j -> byte_of_word (sv_denot E (SLit k)) j = cp_z.
Proof. intros E k j Hk Hj. apply pt1_bytej; [rewrite U_lit by lia; lia | lia]. Qed.
Lemma pt1_sltu : forall E fr, (ew E 640 = Z_to_bv 64 0 <-> cp_bcast fr = true) ->
U E (SAlu ALU_SLTU (SOff 640 0) (SLit 1)) = if cp_bcast fr then 1 else 0.
Proof.
intros E fr Hbc. rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_lit E 1) by lia.
unfold U at 1. rewrite sv_denot_SOff0.
destruct (cp_bcast fr) eqn:Hb.
- rewrite (proj2 Hbc eq_refl). reflexivity.
- assert (Hn : bv_unsigned (ew E 640) <> 0).
  { intros Hz. assert (Hw : ew E 640 = Z_to_bv 64 0) by (apply bv_eq; rewrite Hz; reflexivity).
    apply Hbc in Hw. congruence. }
  pose proof (bv_unsigned_in_range 64 (ew E 640)) as R.
  replace (bv_unsigned (ew E 640) <? 1) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.
Lemma pt1_bs0 : forall E fr, (ew E 640 = Z_to_bv 64 0 <-> cp_bcast fr = true) ->
byte_of_word (sv_denot E (SAlu ALU_SLTU (SOff 640 0) (SLit 1))) 0 = if cp_bcast fr then Z_to_bv 8 1 else cp_z.
Proof. intros E fr Hbc. rewrite pt1_byte0, (pt1_sltu E fr Hbc). destruct (cp_bcast fr); reflexivity. Qed.
Lemma pt1_bsj : forall E e1 e2 j, 1 <= j -> byte_of_word (sv_denot E (SAlu ALU_SLTU e1 e2)) j = cp_z.
Proof.
intros E e1 e2 j Hj. apply pt1_bytej; [|lia]. rewrite U_SAlu. cbn [zalu_raw].
destruct (U E e1 <? U E e2); unfold zcanon, M64; rewrite Z.mod_small by lia; lia.
Qed.
Lemma pt1_b1 : forall E n fr i, ew E n = Z_to_bv 64 (cp_v fr i) -> byte_of_word (sv_denot E (SOff n 0)) 0 = cp_b fr i.
Proof.
intros E n fr i H. pose proof (cp_v_range fr i). rewrite pt1_byte0, (U_atom E n (cp_v fr i) H) by lia.
unfold cp_v. apply Z_to_bv_bv_unsigned.
Qed.
Lemma pt1_b2v : forall E nh nl fr ih il, ew E nh = Z_to_bv 64 (cp_v fr ih) -> ew E nl = Z_to_bv 64 (cp_v fr il) ->
U E (SAlu ALU_OR (SAlu ALU_SLL (SOff nh 0) (SLit 8)) (SOff nl 0)) = cp_v fr ih * 256 + cp_v fr il.
Proof.
intros E nh nl fr ih il Hh Hl. pose proof (cp_v_range fr ih). pose proof (cp_v_range fr il).
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw].
rewrite (U_atom E nh _ Hh), (U_atom E nl _ Hl), (U_lit E 8) by lia.
change (Z.land 8 63) with 8. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 8) with 256.
rewrite (zcanon_id (cp_v fr ih * 256)) by (unfold M64; lia).
rewrite pt1_lor by lia. apply zcanon_id. unfold M64. lia.
Qed.
Lemma pt1_b2lo : forall E nh nl fr ih il, ew E nh = Z_to_bv 64 (cp_v fr ih) -> ew E nl = Z_to_bv 64 (cp_v fr il) ->
byte_of_word (sv_denot E (SAlu ALU_OR (SAlu ALU_SLL (SOff nh 0) (SLit 8)) (SOff nl 0))) 0 = cp_b fr il.
Proof.
intros E nh nl fr ih il Hh Hl. pose proof (cp_v_range fr ih). pose proof (cp_v_range fr il).
rewrite pt1_byte0, (pt1_b2v E nh nl fr ih il Hh Hl). apply pt1_bv8.
rewrite Z.add_comm, Z_mod_plus_full. unfold cp_v in *. apply Z.mod_small. lia.
Qed.
Lemma pt1_b2hi : forall E nh nl fr ih il, ew E nh = Z_to_bv 64 (cp_v fr ih) -> ew E nl = Z_to_bv 64 (cp_v fr il) ->
byte_of_word (sv_denot E (SAlu ALU_OR (SAlu ALU_SLL (SOff nh 0) (SLit 8)) (SOff nl 0))) 1 = cp_b fr ih.
Proof.
intros E nh nl fr ih il Hh Hl. pose proof (cp_v_range fr ih). pose proof (cp_v_range fr il).
rewrite pt1_byte1, (pt1_b2v E nh nl fr ih il Hh Hl). rewrite Z.div_add_l by lia.
rewrite (Z.div_small (cp_v fr il) 256) by lia. rewrite Z.add_0_r. apply pt1_bv8.
unfold cp_v in *. apply Z.mod_small. lia.
Qed.
(* The branch conditions on the frame type bytes f[16] (atom 56) and f[17] (atom 57). *)
Lemma pt1_or : forall E fr, ew E 56 = Z_to_bv 64 (cp_v fr 16) -> ew E 57 = Z_to_bv 64 (cp_v fr 17) ->
branch_taken BC_NE (sv_denot E (SAlu ALU_OR (SOff 56 0) (SAlu ALU_AND (SOff 57 0) (SLit 255)))) (sv_denot E (SLit 0))
= negb ((cp_v fr 16 =? 0) && (cp_v fr 17 =? 0)).
Proof.
intros E fr H6 H7. pose proof (cp_v_range fr 16) as R6. pose proof (cp_v_range fr 17) as R7.
rewrite branch_ne_U, U_SAlu. cbn [zalu_raw]. rewrite U_and_lit by lia.
rewrite (U_atom E 56 _ H6), (U_atom E 57 _ H7), (U_lit E 0) by lia. rewrite pt1_land255 by lia.
pose proof (YO0a.lor_range (cp_v fr 16) (cp_v fr 17) 8 ltac:(change (2 ^ 8) with 256; lia) ltac:(change (2 ^ 8) with 256; lia)) as HR.
change (2 ^ 8) with 256 in HR. rewrite zcanon_id by (unfold M64; lia). f_equal.
destruct (Z.eqb_spec (Z.lor (cp_v fr 16) (cp_v fr 17)) 0) as [Hz|Hz].
- apply Z.lor_eq_0_iff in Hz. destruct Hz as [-> ->]. reflexivity.
- symmetry. apply andb_false_iff. destruct (Z.eqb_spec (cp_v fr 16) 0) as [Ha|Ha]; [|left; reflexivity].
  right. apply Z.eqb_neq. intros Hb. apply Hz. rewrite Ha, Hb. reflexivity.
Qed.
Lemma pt1_ne16 : forall E fr x, 0 <= x < 2 ^ 64 -> ew E 56 = Z_to_bv 64 (cp_v fr 16) ->
branch_taken BC_NE (sv_denot E (SOff 56 0)) (sv_denot E (SLit x)) = negb (cp_v fr 16 =? x).
Proof.
intros E fr x Hx H. pose proof (cp_v_range fr 16).
rewrite branch_ne_U, (U_atom E 56 _ H), (U_lit E x) by lia. reflexivity.
Qed.
Lemma pt1_ne17 : forall E fr x, 0 <= x < 2 ^ 64 -> ew E 57 = Z_to_bv 64 (cp_v fr 17) ->
branch_taken BC_NE (sv_denot E (SAlu ALU_AND (SOff 57 0) (SLit 255))) (sv_denot E (SLit x)) = negb (cp_v fr 17 =? x).
Proof.
intros E fr x Hx H. pose proof (cp_v_range fr 17).
rewrite branch_ne_U, U_and_lit by lia. rewrite (U_atom E 57 _ H), (U_lit E x) by lia.
rewrite pt1_land255 by lia. reflexivity.
Qed.
(* One byte of the out struct against the model's cp_struct. *)
Ltac pt1_byte HA Hbc :=
lazymatch goal with
| |- Some (Z_to_bv 8 0) = Some cp_z => reflexivity
| |- Some (byte_of_word (sv_denot _ (SLit _)) 0) = Some _ => f_equal; apply pt1_bk0; lia
| |- Some (byte_of_word (sv_denot _ (SLit _)) _) = Some _ => f_equal; apply pt1_bkj; lia
| |- Some (byte_of_word (sv_denot ?E (SAlu ALU_SLTU _ _)) 0) = Some _ => f_equal; exact (pt1_bs0 E _ Hbc)
| |- Some (byte_of_word (sv_denot _ (SAlu ALU_SLTU _ _)) _) = Some _ => f_equal; apply pt1_bsj; lia
| |- Some (byte_of_word (sv_denot ?E (SOff ?n 0)) 0) = Some (cp_b ?fr ?i) =>
  f_equal; exact (pt1_b1 E n fr i (HA i ltac:(lia)))
| |- Some (byte_of_word (sv_denot ?E (SAlu ALU_OR (SAlu ALU_SLL (SOff ?nh 0) (SLit 8)) (SOff ?nl 0))) 0) = Some (cp_b ?fr ?il) =>
  let ih := eval vm_compute in (nh - 40)%nat in f_equal; exact (pt1_b2lo E nh nl fr ih il (HA ih ltac:(lia)) (HA il ltac:(lia)))
| |- Some (byte_of_word (sv_denot ?E (SAlu ALU_OR (SAlu ALU_SLL (SOff ?nh 0) (SLit 8)) (SOff ?nl 0))) 1) = Some (cp_b ?fr ?ih) =>
  let il := eval vm_compute in (nl - 40)%nat in f_equal; exact (pt1_b2hi E nh nl fr ih il (HA ih ltac:(lia)) (HA il ltac:(lia)))
| |- ?g => idtac "PT1-BYTE" g; fail
end.
(* After a run: the caller's memory kept, from the run's frame (its writable windows are the realigned stack
   [sp1, sp) and the out struct). *)
Ltac t1_keep B LAWS HAR KP AGX Usp B12 B33 Hoimg :=
lazymatch type of HAR with AR _ _ ?lyc ?Sc ?W ?memc ?mdc =>
lazymatch type of Usp with _ = ?sp =>
lazymatch type of B33 with _ = ?sp1 =>
lazymatch type of B12 with _ = ?o =>
lazymatch goal with HFr : frame_of ?Ef ?rsf (mrestrict _ ?mA) (mrestrict _ ?mB), HG : mem_grows _ _ |- _ =>
let Hw1 := fresh "Hw1" in let KP' := fresh "KP" in
assert (Hw1 : forall b wlo whi a, In (b, wlo, whi) (windows rsf) -> base_val Ef b + wlo <= a < base_val Ef b + whi ->
  (fun a => (sp1 <= a < sp) \/ (o <= a < o + 36)) a)
  by (pz_win_tac ltac:(fun H => rewrite ?(AGX 2%nat), ?(AGX 12%nat), ?(AGX 33%nat) in H by lia; rewrite ?Usp, ?B12, ?B33 in H));
pose proof (pz_kept_run B LAWS lyc Sc W memc mdc mA mB (sp - REAC_CTRL_PARSE_STK) sp o (fun _ => False)
  (fun a => (sp1 <= a < sp) \/ (o <= a < o + 36)) HAR ltac:(assumption) ltac:(assumption) Hoimg
  ltac:(intros; contradiction) ltac:(intros; contradiction) ltac:(intros; contradiction) ltac:(intros; contradiction)
  ltac:(intros a Ha; cbv beta in Ha; destruct Ha; [left | right; left]; lia) KP (kept_of_frame _ _ _ _ _ _ HFr Hw1) (fun a Ha => apresent_grows _ _ _ a HG Ha)) as KP';
clear KP Hw1; rename KP' into KP; clear_frames
end end end end end.
(* Make the window [0, hi) of the region based at atom n writable (Hp: its bytes are writable). *)
Ltac t1_rw HS n hi Hp :=
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs n in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rs got_regionP) in
let HS3 := fresh "HS3" in
pose proof (ast_ok_pi_set_region Ex ssx msx i r (set_window r 0 hi) HS ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity)
  (region_ok_rewindow _ Ex _ r 0 hi (st_ok_pi_region_nth Ex ssx msx i r HS ltac:(vm_compute; reflexivity)) Hp)) as HS3;
clear HS; rename HS3 into HS; pz_norm HS end.
(* lia over the walk's context: the disjunctive facts are boxed (lia would split on every one of them); a goal
   that needs one of them gets it destructed, one at a time. *)
Local Ltac t1_lia :=
first [ lia
| match goal with H : boxed (_ \/ _) |- _ => let X := fresh in pose proof H as X; unfold boxed in X; destruct X; lia end
| match goal with H : boxed (_ /\ (_ \/ _)) |- _ => let X := fresh in pose proof H as X; unfold boxed in X; destruct X as [? [?|?]]; lia end
| match goal with H : boxed (off_img _ _) |- _ => let X := fresh in pose proof H as X; unfold boxed, off_img in X; destruct X; lia end
| match goal with H : boxed (in_app _ _) |- _ => let X := fresh in pose proof H as X; unfold boxed, in_app in X; destruct X as [? [?|?]]; lia end
| unbox; lia ].
Section b. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Context {PI : PAImg lib_both3_0_listing}.
Context {RO : ro_below_ofl (@pa_segs _ lib_both3_0_listing PI) (@pa_relro_lo _ lib_both3_0_listing PI) (@pa_relro_hi _ lib_both3_0_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
Lemma pt1_find_ok : forall E base cs off, pz_chunk_at E base cs off =
match pt1_find cs off with Some (co, cv, j) => YP09.cbyte SEGS E (base + co) cv j | None => None end.
Proof.
intros E base cs off. induction cs as [|c t IH]; cbn [pz_chunk_at pt1_find]; [reflexivity|].
destruct (_ && _); [reflexivity | exact IH].
Qed.
(* The 36 bytes of the out struct at cut J are the model's cp_struct fr k. *)
Lemma pt1_out_bytes : forall E H mem o fr k,
region_ok SEGS E (mrestrict H mem) (YP09.mkRegion (Some 12%nat) 0 36 0 36 (pt1_out k)) ->
base_val E (Some 12%nat) = o ->
(forall i, (i < 23)%nat -> ew E (40 + i) = Z_to_bv 64 (cp_v fr i)) ->
(ew E 640 = Z_to_bv 64 0 <-> cp_bcast fr = true) ->
0 <= k < 256 -> cp_rec fr = false -> (k =? 6) = false ->
forall i, (i < 36)%nat -> aview SEGS H mem (o + Z.of_nat i) = Some (bv_unsigned (nth i (cp_struct fr k) cp_z)).
Proof.
intros E H mem o fr k Hr Hb HA Hbc Hk Hrec Hk6 i Hi. subst o.
apply (pz_region_byte E H mem _ (Z.of_nat i) _ Hr).
cbn [YP09.r_base YP09.r_chunks]. rewrite pt1_find_ok.
unfold cp_struct. rewrite Hrec, Hk6.
do 36 (destruct i as [|i]; [
  lazymatch goal with |- context [pt1_find ?cs ?off] => let v := eval vm_compute in (pt1_find cs off) in change (pt1_find cs off) with v end;
  cbn [YP09.cbyte nth app]; pt1_byte HA Hbc | ]).
lia.
Qed.
(* At cut J (0x878c4) on a class-1 path with kind k: read the out struct back, make the frame and its shadow
   writable, join to ss_cutJ (atoms 700..723) and apply the cut J hypothesis. *)
Ltac t1_join HS HJ2 AGX RF E529 HA Hbc B12 Hhdr Hkind Hrec LAWS Hfin2 HJc k :=
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict (w_H ?Wx) ?msx) =>
lazymatch type of B12 with _ = ?ov =>
lazymatch type of RF with _ = Z_to_bv 64 ?Fv =>
lazymatch type of Hhdr with cp_hdr ?nv ?frv = true =>
lazymatch type of Hfin2 with In (1, ?fpos) _ =>
let R12 := fresh "R12" in let OUT := fresh "OUT" in let Ra0 := fresh "Ra0" in
let HFp := fresh "HFp" in let HFSp := fresh "HFSp" in let W529 := fresh "W529" in let W516 := fresh "W516" in
let E700 := fresh "E700" in let q := fresh "q" in let Hq := fresh "Hq" in
pose proof (st_ok_pi_region_nth Ex ssx _ 0 _ HS eq_refl) as R12;
lazymatch type of R12 with region_ok ?sg _ ?mm _ =>
change (region_ok sg Ex mm (YP09.mkRegion (Some 12%nat) 0 36 0 36 (pt1_out k))) in R12;
pose proof (pt1_out_bytes Ex (w_H Wx) (ms_mem msx) ov frv k R12
  ltac:(cbn [base_val]; rewrite (AGX 12%nat) by lia; exact B12) HA Hbc ltac:(lia) Hrec eq_refl) as OUT;
prreg HS (10%bv : bv 5) Ra0;
destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos (proj1 HJ2) Hfin2) as (_ & _ & HFp & HFSp);
change (fs_frame_bytes 1) with 128 in HFp, HFSp; change (128 / 8) with 16 in HFSp;
assert (W529 : forall q, 0 <= q < 16 -> writable_at sg (mrestrict (w_H Wx) (ms_mem msx)) (base_val Ex (Some 529%nat) + q))
  by (intros q Hq; cbn [base_val]; rewrite E529, unsigned_lit_small by (unfold SB; lia); apply (apresent_writable sg);
      unfold shadow_addr in HFSp; rewrite <- SB_SHADOW_OFF in HFSp; apply (proj1 (HFSp q Hq)));
assert (W516 : forall q, 0 <= q < 128 -> writable_at sg (mrestrict (w_H Wx) (ms_mem msx)) (base_val Ex (Some 516%nat) + q))
  by (intros q Hq; cbn [base_val]; rewrite RF, unsigned_lit_small by lia; apply (apresent_writable sg);
      apply (proj1 (HFp (Fv + q) ltac:(lia))));
t1_rw HS 529%nat 16 W529; t1_rw HS 516%nat 128 W516; clear W529 W516 HFp HFSp R12;
ra_join HS ss_cutJ 700%nat pz_deadJ ltac:(idtac; ra_join_val HS 700%nat 0%nat Ra0 E700);
pz_rebase HS AGX;
refine (HJc _ _ _ _ HS _ _);
[ do 6 (split; [assumption|]); assumption
| rewrite E700; unfold ctrlparse; rewrite Hhdr, Hkind; reflexivity
| intros q Hq; unfold ctrlparse; rewrite Hhdr, Hkind; exact (OUT q Hq) ]
end end end end end end.
Lemma pz_tail1 : forall B G, pz_rt B G -> forall c, pz_ok B c -> pz_cutJ_spec B c -> pz_cutB_case B c pz_P1.
Proof.
intros B G RT c Hok HJc Hbig E ms md Hcur HS SHOK Hhdr Hbc HP.
pz_open c Hok. pz_open_rt RT. pz_open_cur Hcur; pz_open_f Hbig. pz_std.
pose proof (paj_run B LAWS) as RUN. pose proof (paj_run_to B LAWS) as RUNTO. pose proof (paj_branch (PI := PI)) as BR.
assert (HA : forall i, (i < 23)%nat -> ew E (40 + i) = Z_to_bv 64 (cp_v fr i)) by (intros i Hi; rewrite AGX by lia; apply EFB; lia).
pose proof (HA 16%nat ltac:(lia)) as H56. pose proof (HA 17%nat ltac:(lia)) as H57. cbn [Nat.add] in H56, H57.
assert (HP' : (cp_v fr 16 = 0 /\ cp_v fr 17 = 0) \/ (cp_v fr 16 = 207 /\ cp_v fr 17 = 234) \/ (cp_v fr 16 = 206 /\ cp_v fr 17 = 234)).
{ unfold pz_P1, cp_type in HP. rewrite !andb_true_iff, !Z.eqb_eq in HP. exact HP. }
repeat match goal with H : _ \/ _ |- _ => box H | H : off_img _ _ |- _ => box H | H : in_app _ _ |- _ => box H end.
assert (HKlo : alloc_ceiling <= sp - REAC_CTRL_PARSE_STK) by lia. assert (HKhi : sp <= 2 ^ 64) by lia.
(* Cut B to 0x878a0: the stores of is_broadcast, the counter, link, segment, blk_len and the opcode. *)
paj_run_tok RUN HS HJ2 SHOK PZspan; [awrFL_with ltac:(idtac; pz_awr_hd) AGX fpos F EF|].
t1_keep B LAWS HAR KP AGX Usp B12 B33 Hoimg.
psrr_branch_tok RUN BR HS SHOK PZspan.
- (* 0x878a0 taken: f[16] | f[17] <> 0 *)
  rewrite (pt1_or E fr H56 H57) in Hc.
  assert (NT0 : ~ (cp_v fr 16 = 0 /\ cp_v fr 17 = 0)) by (intros [X Y]; rewrite X, Y in Hc; cbn in Hc; discriminate).
  box NT0. clear Hc.
  paj_run_tok RUN HS HJ2 SHOK PZspan; [awrFL_with ltac:(idtac; pz_awr_hd) AGX fpos F EF|].
  t1_keep B LAWS HAR KP AGX Usp B12 B33 Hoimg.
  psrr_branch_tok RUN BR HS SHOK PZspan.
  + (* 0x879bc taken: f[16] <> 0xcf *)
    rewrite (pt1_ne16 E fr 207 ltac:(lia) H56) in Hc. apply negb_true_iff, Z.eqb_neq in Hc. rename Hc into NT1. box NT1.
    paj_run_tok RUN HS HJ2 SHOK PZspan; [awrFL_with ltac:(idtac; pz_awr_hd) AGX fpos F EF|].
    t1_keep B LAWS HAR KP AGX Usp B12 B33 Hoimg.
    psrr_branch_tok RUN BR HS SHOK PZspan.
    * (* 0x879e4 taken: f[16] <> 0xce, which pz_P1 excludes *)
      exfalso. rewrite (pt1_ne16 E fr 206 ltac:(lia) H56) in Hc. apply negb_true_iff, Z.eqb_neq in Hc. clear - HP' NT0 NT1 Hc; t1_lia.
    * (* 0x879e4 not taken: f[16] = 0xce *)
      rewrite (pt1_ne16 E fr 206 ltac:(lia) H56) in Hc. apply negb_false_iff, Z.eqb_eq in Hc. rename Hc into X.
      paj_run_tok RUN HS HJ2 SHOK PZspan; [awrFL_with ltac:(idtac; pz_awr_hd) AGX fpos F EF|].
      t1_keep B LAWS HAR KP AGX Usp B12 B33 Hoimg.
      psrr_branch_tok RUN BR HS SHOK PZspan.
      -- (* 0x879ec taken: f[17] <> 0xea, which pz_P1 excludes *)
         exfalso. rewrite (pt1_ne17 E fr 234 ltac:(lia) H57) in Hc. apply negb_true_iff, Z.eqb_neq in Hc. clear - HP' X Hc; t1_lia.
      -- (* 0x879ec not taken: SPLIT_ANNOUNCE, kind 8 *)
         rewrite (pt1_ne17 E fr 234 ltac:(lia) H57) in Hc. apply negb_false_iff, Z.eqb_eq in Hc. rename Hc into Y.
         paj_run_to_tok RUNTO HS HJ2 SHOK PZspan AF_JOIN; [awrFL_with ltac:(idtac; pz_awr_hd) AGX fpos F EF|].
         t1_keep B LAWS HAR KP AGX Usp B12 B33 Hoimg.
         assert (Hkind : cp_kind fr = 8) by (unfold cp_kind, cp_type; rewrite X, Y; reflexivity).
         assert (Hrec : cp_rec fr = false) by (unfold cp_rec, cp_type; rewrite X; reflexivity).
         t1_join HS HJ2 AGX RF E529 HA Hbc B12 Hhdr Hkind Hrec LAWS Hfin2 HJc 8.
  + (* 0x879bc not taken: f[16] = 0xcf *)
    rewrite (pt1_ne16 E fr 207 ltac:(lia) H56) in Hc. apply negb_false_iff, Z.eqb_eq in Hc. rename Hc into X.
    paj_run_tok RUN HS HJ2 SHOK PZspan; [awrFL_with ltac:(idtac; pz_awr_hd) AGX fpos F EF|].
    t1_keep B LAWS HAR KP AGX Usp B12 B33 Hoimg.
    psrr_branch_tok RUN BR HS SHOK PZspan.
    * (* 0x879c4 taken: f[17] <> 0xea, which pz_P1 excludes *)
      exfalso. rewrite (pt1_ne17 E fr 234 ltac:(lia) H57) in Hc. apply negb_true_iff, Z.eqb_neq in Hc. clear - HP' X Hc; t1_lia.
    * (* 0x879c4 not taken: MASTER_ANNOUNCE, kind 4 *)
      rewrite (pt1_ne17 E fr 234 ltac:(lia) H57) in Hc. apply negb_false_iff, Z.eqb_eq in Hc. rename Hc into Y.
      paj_run_to_tok RUNTO HS HJ2 SHOK PZspan AF_JOIN; [awrFL_with ltac:(idtac; pz_awr_hd) AGX fpos F EF|].
      t1_keep B LAWS HAR KP AGX Usp B12 B33 Hoimg.
      assert (Hkind : cp_kind fr = 4) by (unfold cp_kind, cp_type; rewrite X, Y; reflexivity).
      assert (Hrec : cp_rec fr = false) by (unfold cp_rec, cp_type; rewrite X; reflexivity).
      t1_join HS HJ2 AGX RF E529 HA Hbc B12 Hhdr Hkind Hrec LAWS Hfin2 HJc 4.
- (* 0x878a0 not taken: FILLER, kind 1 *)
  rewrite (pt1_or E fr H56 H57) in Hc. apply negb_false_iff, andb_true_iff in Hc. destruct Hc as [X Y].
  apply Z.eqb_eq in X, Y.
  paj_run_to_tok RUNTO HS HJ2 SHOK PZspan AF_JOIN; [awrFL_with ltac:(idtac; pz_awr_hd) AGX fpos F EF|].
  t1_keep B LAWS HAR KP AGX Usp B12 B33 Hoimg.
  assert (Hkind : cp_kind fr = 1) by (unfold cp_kind, cp_type; rewrite X, Y; reflexivity).
  assert (Hrec : cp_rec fr = false) by (unfold cp_rec, cp_type; rewrite X; reflexivity).
  t1_join HS HJ2 AGX RF E529 HA Hbc B12 Hhdr Hkind Hrec LAWS Hfin2 HJc 1.
Qed.
End d.
End b.
