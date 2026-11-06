(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: adapted from cgif's lib/A/ACgq.v and lib/A/ACk8.v (file header, walk tactic forms) for reac_ctrl_parse of libreac's fuzz_grant. *)
(* reac_ctrl_parse, the walk from cut B (0x821c8) to cut J for the class-4 frames of the head-amp record (seg = 3, cp_amp): HEADAMP (6), ch/param/value at out+30..32
   (pz_P4b; a second attack on CtrlParseTail4.v).
   From cut B the walk stores is_broadcast (out + 16), the counter (out + 20), link (out + 22), seg (out + 23),
   blk_len (out + 24) and the opcode (out + 26), each store after its shadow check. Ten branches follow, and on a
   pz_P4b frame each goes one way: 0x82388 taken (frame[16] | frame[17] <> 0), 0x824a0 and 0x824c8 taken
   (frame[16] <> 0xcf, 0xce), 0x824f0 and 0x824f8 not taken (frame[16] = 0xcd, frame[17] = 0xea), 0x82500
   taken (link frame[18] = 4), 0x82574 not taken (seg frame[19] = 3); the walk stores
   frame[34] << 8 | frame[35] at out + 28; 0x825f0, 0x82610 and 0x82618 not taken (frame[32] = frame[33] = 0x12,
   frame[34] << 8 | frame[35] = 0x101). Then it stores 6 at out + 0 and frame[36..38] at out + 30..32, reads
   out + 0 back into a0 (0x82740) and jumps to the join 0x823a8 (cut J). *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0s YM05.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import PaRun PaShadow PaJournal GrantSyms GrantList GrantPa GrantPaLib.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import GrantBase YC81 YC4b YC1g YC1h YC45 YC85 GrantFrame YC88.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import RcKind RcParse.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import CtrlParseLib KindOfLink1 GrantRo ACj1 GrantACja.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import CtrlParseCut.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
(* ---- The model on a pz_P4b frame (Pau's ctrlparse, lib/Prog/RcParse.v:45) ------------------------- *)
Lemma t4b_vals : forall fr, pz_P4b fr ->
cp_v fr 16 = 205 /\ cp_v fr 17 = 234 /\ cp_v fr 18 = 4 /\ cp_v fr 19 = 3 /\
cp_v fr 32 = 18 /\ cp_v fr 33 = 18 /\ cp_v fr 34 = 1 /\ cp_v fr 35 = 1.
Proof.
intros fr HP. unfold pz_P4b, pz_P4, cp_type, cp_amp in HP.
destruct HP as ((T & V18) & V19 & A).
apply andb_true_iff in T. destruct T as [T16 T17]. apply Z.eqb_eq in T16, T17.
apply andb_true_iff in A. destruct A as [A A35]. apply andb_true_iff in A. destruct A as [A A34].
apply andb_true_iff in A. destruct A as [A32 A33]. apply Z.eqb_eq in A32, A33, A34, A35.
repeat split; assumption.
Qed.
Lemma t4b_kind : forall n fr, cp_hdr n fr = true -> pz_P4b fr -> ctrlparse n fr = (6, cp_struct fr 6).
Proof.
intros n fr Hh HP. pose proof (t4b_vals fr HP) as (V16 & V17 & V18 & V19 & _).
unfold pz_P4b in HP. destruct HP as (_ & _ & A).
unfold ctrlparse, cp_kind, cp_type. rewrite Hh, V16, V17, V18, V19, A. reflexivity.
Qed.
Lemma t4b_rec : forall fr, pz_P4b fr -> cp_rec fr = true.
Proof.
intros fr HP. pose proof (t4b_vals fr HP) as (V16 & V17 & V18 & V19 & _).
unfold cp_rec, cp_type. rewrite V16, V17, V18, V19. reflexivity.
Qed.
(* ---- The bytes the walk stores, as the model's bytes --------------------------------------------- *)
Lemma t4b_lor : forall a b, 0 <= a -> 0 <= b < 256 -> Z.lor (a * 256) b = a * 256 + b.
Proof.
intros a b Ha Hb.
assert (HL : Z.land (a * 256) b = 0).
{ apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
  destruct (Z.lt_ge_cases i 8) as [Hi8|Hi8].
  - change 256 with (2 ^ 8). rewrite Z.mul_pow2_bits_low by lia. reflexivity.
  - rewrite <- (Z.mod_small b (2 ^ 8)) by (cbn; lia). rewrite Z.mod_pow2_bits_high by lia. apply andb_false_r. }
rewrite <- (Z.lxor_lor _ _ HL). symmetry. apply Z.add_nocarry_lxor. exact HL.
Qed.
Lemma t4b_bv8 : forall x (b : byte), x mod 256 = bv_unsigned b -> Z_to_bv 8 x = b.
Proof. intros x b H. apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. exact H. Qed.
Lemma t4b_byte0 : forall E e, byte_of_word (sv_denot E e) 0 = Z_to_bv 8 (U E e).
Proof. intros E e. unfold byte_of_word, U. rewrite Z.mul_0_r, Z.shiftr_0_r. reflexivity. Qed.
Lemma t4b_byte1 : forall E e, byte_of_word (sv_denot E e) 1 = Z_to_bv 8 (U E e / 256).
Proof. intros E e. unfold byte_of_word, U. rewrite Z.shiftr_div_pow2 by lia. reflexivity. Qed.
Lemma t4b_bytej : forall E e j, 0 <= U E e < 256 -> 1 <= j -> byte_of_word (sv_denot E e) j = cp_z.
Proof.
intros E e j HU Hj. unfold byte_of_word. change (bv_unsigned (sv_denot E e)) with (U E e).
rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_small; [reflexivity|].
assert (H8 : 2 ^ 8 <= 2 ^ (8 * j)) by (apply Z.pow_le_mono_r; lia). change (2 ^ 8) with 256 in H8. lia.
Qed.
Lemma t4b_bk0 : forall E k, 0 <= k < 256 -> byte_of_word (sv_denot E (SLit k)) 0 = Z_to_bv 8 k.
Proof. intros E k Hk. rewrite t4b_byte0, U_lit by lia. reflexivity. Qed.
Lemma t4b_bkj : forall E k j, 0 <= k < 256 -> 1 <= j -> byte_of_word (sv_denot E (SLit k)) j = cp_z.
Proof. intros E k j Hk Hj. apply t4b_bytej; [rewrite U_lit by lia; lia | lia]. Qed.
Lemma t4b_sltu : forall E fr, (ew E 640 = Z_to_bv 64 0 <-> cp_bcast fr = true) ->
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
Lemma t4b_bs0 : forall E fr, (ew E 640 = Z_to_bv 64 0 <-> cp_bcast fr = true) ->
byte_of_word (sv_denot E (SAlu ALU_SLTU (SOff 640 0) (SLit 1))) 0 = if cp_bcast fr then Z_to_bv 8 1 else cp_z.
Proof. intros E fr Hbc. rewrite t4b_byte0, (t4b_sltu E fr Hbc). destruct (cp_bcast fr); reflexivity. Qed.
Lemma t4b_bsj : forall E e1 e2 j, 1 <= j -> byte_of_word (sv_denot E (SAlu ALU_SLTU e1 e2)) j = cp_z.
Proof.
intros E e1 e2 j Hj. apply t4b_bytej; [|lia]. rewrite U_SAlu. cbn [zalu_raw].
destruct (U E e1 <? U E e2); unfold zcanon, M64; rewrite Z.mod_small by lia; lia.
Qed.
Lemma t4b_b1 : forall E n fr i, ew E n = Z_to_bv 64 (cp_v fr i) -> byte_of_word (sv_denot E (SOff n 0)) 0 = cp_b fr i.
Proof.
intros E n fr i H. pose proof (cp_v_range fr i). rewrite t4b_byte0, (U_atom E n (cp_v fr i) H) by lia.
unfold cp_v. apply Z_to_bv_bv_unsigned.
Qed.
Lemma t4b_b2v : forall E nh nl fr ih il, ew E nh = Z_to_bv 64 (cp_v fr ih) -> ew E nl = Z_to_bv 64 (cp_v fr il) ->
U E (SAlu ALU_OR (SAlu ALU_SLL (SOff nh 0) (SLit 8)) (SOff nl 0)) = cp_v fr ih * 256 + cp_v fr il.
Proof.
intros E nh nl fr ih il Hh Hl. pose proof (cp_v_range fr ih). pose proof (cp_v_range fr il).
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw].
rewrite (U_atom E nh _ Hh), (U_atom E nl _ Hl), (U_lit E 8) by lia.
change (Z.land 8 63) with 8. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 8) with 256.
rewrite (zcanon_id (cp_v fr ih * 256)) by (unfold M64; lia).
rewrite t4b_lor by lia. apply zcanon_id. unfold M64. lia.
Qed.
Lemma t4b_b2lo : forall E nh nl fr ih il, ew E nh = Z_to_bv 64 (cp_v fr ih) -> ew E nl = Z_to_bv 64 (cp_v fr il) ->
byte_of_word (sv_denot E (SAlu ALU_OR (SAlu ALU_SLL (SOff nh 0) (SLit 8)) (SOff nl 0))) 0 = cp_b fr il.
Proof.
intros E nh nl fr ih il Hh Hl. pose proof (cp_v_range fr ih). pose proof (cp_v_range fr il).
rewrite t4b_byte0, (t4b_b2v E nh nl fr ih il Hh Hl). apply t4b_bv8.
rewrite Z.add_comm, Z_mod_plus_full. unfold cp_v in *. apply Z.mod_small. lia.
Qed.
Lemma t4b_b2hi : forall E nh nl fr ih il, ew E nh = Z_to_bv 64 (cp_v fr ih) -> ew E nl = Z_to_bv 64 (cp_v fr il) ->
byte_of_word (sv_denot E (SAlu ALU_OR (SAlu ALU_SLL (SOff nh 0) (SLit 8)) (SOff nl 0))) 1 = cp_b fr ih.
Proof.
intros E nh nl fr ih il Hh Hl. pose proof (cp_v_range fr ih). pose proof (cp_v_range fr il).
rewrite t4b_byte1, (t4b_b2v E nh nl fr ih il Hh Hl). rewrite Z.div_add_l by lia.
rewrite (Z.div_small (cp_v fr il) 256) by lia. rewrite Z.add_0_r. apply t4b_bv8.
unfold cp_v in *. apply Z.mod_small. lia.
Qed.
(* The out struct's chunks at the join (0x823a8) on the head-amp path: the bytes of cut B, the six field
   stores, frame[34] << 8 | frame[35] at out + 28, the kind 6 at out + 0 and frame[36..38] at out + 30..32. *)
Definition t4b_out : list YP09.chunk :=
[YP09.mkChunk 32 (CVal 1 (SOff 78 0)); YP09.mkChunk 31 (CVal 1 (SOff 77 0)); YP09.mkChunk 30 (CVal 1 (SOff 76 0));
 YP09.mkChunk 0 (CVal 4 (SLit 6));
 YP09.mkChunk 28 (CVal 2 (SAlu ALU_OR (SAlu ALU_SLL (SOff 74 0) (SLit 8)) (SOff 75 0)));
 YP09.mkChunk 26 (CVal 1 (SOff 62 0));
 YP09.mkChunk 24 (CVal 2 (SAlu ALU_OR (SAlu ALU_SLL (SOff 60 0) (SLit 8)) (SOff 61 0)));
 YP09.mkChunk 23 (CVal 1 (SOff 59 0)); YP09.mkChunk 22 (CVal 1 (SOff 58 0));
 YP09.mkChunk 20 (CVal 2 (SAlu ALU_OR (SAlu ALU_SLL (SOff 55 0) (SLit 8)) (SOff 54 0)));
 YP09.mkChunk 16 (CVal 4 (SAlu ALU_SLTU (SOff 640 0) (SLit 1)));
 YP09.mkChunk 4 (CVal 1 (SOff 46 0)); YP09.mkChunk 5 (CVal 1 (SOff 47 0)); YP09.mkChunk 6 (CVal 1 (SOff 48 0));
 YP09.mkChunk 7 (CVal 1 (SOff 49 0)); YP09.mkChunk 8 (CVal 1 (SOff 50 0)); YP09.mkChunk 9 (CVal 1 (SOff 51 0));
 YP09.mkChunk 10 (CVal 1 (SOff 40 0)); YP09.mkChunk 11 (CVal 1 (SOff 41 0)); YP09.mkChunk 12 (CVal 1 (SOff 42 0));
 YP09.mkChunk 13 (CVal 1 (SOff 43 0)); YP09.mkChunk 14 (CVal 1 (SOff 44 0)); YP09.mkChunk 15 (CVal 1 (SOff 45 0));
 YP09.mkChunk 27 (CZero 1); YP09.mkChunk 33 (CZero 3)].
(* The chunk that covers an offset: its offset, its value and the index inside it. *)
Fixpoint t4b_find (cs : list YP09.chunk) (off : Z) : option (Z * cval * Z) :=
match cs with
| [] => None
| c :: t => if (YP09.c_off c <=? off) && (off <? YP09.c_off c + YP09.c_len c)
  then Some (YP09.c_off c, YP09.c_val c, off - YP09.c_off c) else t4b_find t off
end.
(* One byte of the out struct against the model's cp_struct. *)
Ltac t4b_byte HA Hbc :=
lazymatch goal with
| |- Some (Z_to_bv 8 0) = Some cp_z => reflexivity
| |- Some (byte_of_word (sv_denot _ (SLit _)) 0) = Some _ => f_equal; apply t4b_bk0; lia
| |- Some (byte_of_word (sv_denot _ (SLit _)) _) = Some _ => f_equal; apply t4b_bkj; lia
| |- Some (byte_of_word (sv_denot ?E (SAlu ALU_SLTU _ _)) 0) = Some _ => f_equal; exact (t4b_bs0 E _ Hbc)
| |- Some (byte_of_word (sv_denot _ (SAlu ALU_SLTU _ _)) _) = Some _ => f_equal; apply t4b_bsj; lia
| |- Some (byte_of_word (sv_denot ?E (SOff ?n 0)) 0) = Some (cp_b ?fr ?i) =>
  f_equal; exact (t4b_b1 E n fr i (HA i ltac:(lia)))
| |- Some (byte_of_word (sv_denot ?E (SAlu ALU_OR (SAlu ALU_SLL (SOff ?nh 0) (SLit 8)) (SOff ?nl 0))) 0) = Some (cp_b ?fr ?il) =>
  let ih := eval vm_compute in (nh - 40)%nat in f_equal; exact (t4b_b2lo E nh nl fr ih il (HA ih ltac:(lia)) (HA il ltac:(lia)))
| |- Some (byte_of_word (sv_denot ?E (SAlu ALU_OR (SAlu ALU_SLL (SOff ?nh 0) (SLit 8)) (SOff ?nl 0))) 1) = Some (cp_b ?fr ?ih) =>
  let il := eval vm_compute in (nl - 40)%nat in f_equal; exact (t4b_b2hi E nh nl fr ih il (HA ih ltac:(lia)) (HA il ltac:(lia)))
| |- ?g => idtac "T4B-BYTE" g; fail
end.
(* ---- The walk ------------------------------------------------------------------------------------
   The tactics below run inside pz_tail4b after pz_std; they find its standard facts (AGX, KP, HAR, LAWS, Usp,
   B12, B33, Hoin, Holo, Hohi) by their types and take the walk's own names as arguments. *)
(* After a run: the caller's memory kept, from the run's frame (its writable windows are the realigned stack
   [sp1, sp) and the out struct). *)
Ltac t4b_keep :=
lazymatch goal with HAR : AR _ _ ?lyc ?Sc ?W ?memc ?mdc, LAWS : AR_laws _ ?B, Usp : bv_unsigned (ew _ 2) = ?sp,
  B33 : bv_unsigned (ew _ 33) = ?sp1, B12 : bv_unsigned (ew _ 12) = ?o, Hoin : In (?co, ?po) (frames ?Sc),
  Holo : frame_addr _ ?co ?po <= ?o, Hohi : ?o + 36 <= _, AGX : forall n, (n < 512)%nat -> ew _ n = ew _ n,
  KP : acall_kept _ _ _ _ _ _ _ _ _ _ _ |- _ =>
lazymatch goal with HFr : frame_of ?Ef ?rsf (mrestrict _ ?mA) (mrestrict _ ?mB), HG : mem_grows _ _ |- _ =>
let Hw1 := fresh "Hw1" in let KP' := fresh "KP" in
assert (Hw1 : forall b wlo whi a, In (b, wlo, whi) (windows rsf) -> base_val Ef b + wlo <= a < base_val Ef b + whi ->
  (fun a => (sp1 <= a < sp) \/ (o <= a < o + 36)) a)
  by (pz_win_tac ltac:(fun H => rewrite ?(AGX 2%nat), ?(AGX 12%nat), ?(AGX 33%nat) in H by lia; rewrite ?Usp, ?B12, ?B33 in H));
pose proof (pz_kept_run B LAWS lyc Sc W memc mdc mA mB (sp - TPARSE_STK) sp o (fun _ => False)
  (fun a => (sp1 <= a < sp) \/ (o <= a < o + 36)) co po HAR ltac:(lia) ltac:(lia) Hoin Holo Hohi
  ltac:(intros; contradiction) ltac:(intros; contradiction) ltac:(intros; contradiction) ltac:(intros; contradiction)
  ltac:(intros a Ha; cbv beta in Ha; lia) KP (kept_of_frame _ _ _ _ _ _ HFr Hw1) (fun a Ha => apresent_grows _ _ _ a HG Ha)) as KP';
clear KP Hw1; rename KP' into KP; clear_frames
end end.
(* One run to the next branch or to the join, and the kept memory after it. *)
Ltac t4b_step RUNTO HS HJ2 SHOK AGX fpos F EF :=
paj_run_to_tok RUNTO HS HJ2 SHOK PZspan AF_JOIN; [awrFL_with ltac:(idtac; pz_awr_hd) AGX fpos F EF | t4b_keep].
(* A branch condition as arithmetic on the frame bytes (the facts U E x = v in the context); then each side
   either holds or contradicts pz_P4b. *)
Ltac t4b_hc Hc :=
rewrite ?branch_ne_U, ?branch_eq_U in Hc;
repeat match goal with H : U _ _ = _ |- _ => rewrite H in Hc end;
rewrite ?U_lit in Hc by lia;
lazymatch type of Hc with context [U _ _] => fail 1 "t4b_hc: an unresolved value in" Hc | _ => idtac end;
vm_compute in Hc.
Ltac t4b_side :=
lazymatch goal with Hc : branch_taken _ _ _ = _ |- _ =>
t4b_hc Hc;
lazymatch type of Hc with
| true = true => clear Hc
| false = false => clear Hc
| _ => discriminate Hc
end end.
Ltac t4b_br RUN BR HS SHOK := psrr_branch_tok RUN BR HS SHOK PZspan; t4b_side.
(* Make the window [0, hi) of the region based at atom n writable (Hp: its bytes are writable). *)
Ltac t4b_rw HS n hi Hp :=
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs n in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rs got_regionP) in
let HS3 := fresh "HS3" in
pose proof (ast_ok_pi_set_region Ex ssx msx i r (set_window r 0 hi) HS ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity)
  (region_ok_rewindow _ Ex _ r 0 hi (st_ok_pi_region_nth Ex ssx msx i r HS ltac:(vm_compute; reflexivity)) Hp)) as HS3;
clear HS; rename HS3 into HS; pz_norm HS end.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Context {PI : PAImg grant_listing}.
Context {RO : ro_below_ofl (@pa_segs _ grant_listing PI) (@pa_relro_lo _ grant_listing PI) (@pa_relro_hi _ grant_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ grant_listing PI).
#[local] Notation VAL := (@pa_val _ grant_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ grant_listing PI).
#[local] Notation BASE := (@pa_val _ grant_listing PI A_TEXT).
Lemma t4b_find_ok : forall E base cs off, pz_chunk_at E base cs off =
match t4b_find cs off with Some (co, cv, j) => YP09.cbyte SEGS E (base + co) cv j | None => None end.
Proof.
intros E base cs off. induction cs as [|c t IH]; cbn [pz_chunk_at t4b_find]; [reflexivity|].
destruct (_ && _); [reflexivity | exact IH].
Qed.
(* The 36 bytes of the out struct at cut J are the model's cp_struct fr 6. *)
Lemma t4b_out_bytes : forall E H mem o fr,
region_ok SEGS E (mrestrict H mem) (YP09.mkRegion (Some 12%nat) 0 36 0 36 t4b_out) ->
base_val E (Some 12%nat) = o ->
(forall i, (i < 39)%nat -> ew E (40 + i) = Z_to_bv 64 (cp_v fr i)) ->
(ew E 640 = Z_to_bv 64 0 <-> cp_bcast fr = true) -> cp_rec fr = true ->
forall i, (i < 36)%nat -> aview SEGS H mem (o + Z.of_nat i) = Some (bv_unsigned (nth i (cp_struct fr 6) cp_z)).
Proof.
intros E H mem o fr Hr Hb HA Hbc Hrec i Hi. subst o.
apply (pz_region_byte E H mem _ (Z.of_nat i) _ Hr).
cbn [YP09.r_base YP09.r_chunks]. rewrite t4b_find_ok.
unfold cp_struct. rewrite Hrec. change (6 =? 6) with true.
do 36 (destruct i as [|i]; [
  lazymatch goal with |- context [t4b_find ?cs ?off] => let v := eval vm_compute in (t4b_find cs off) in change (t4b_find cs off) with v end;
  cbn [YP09.cbyte nth app]; t4b_byte HA Hbc | ]).
lia.
Qed.
Lemma pz_tail4b : forall B G, pz_rt B G -> forall c, pz_ok B c -> pz_cutJ_spec B c -> pz_cutB_case B c pz_P4b.
Proof.
intros B G RT c Hok HJc E ms md Hcur HS SHOK Hhdr Hbc HP.
pz_open c Hok. pz_open_rt RT. pz_open_cur Hcur. pz_std.
pose proof (paj_run B LAWS) as RUN. pose proof (paj_run_to B LAWS) as RUNTO. pose proof (paj_branch (PI := PI)) as BR.
assert (HA : forall i, (i < 39)%nat -> ew E (40 + i) = Z_to_bv 64 (cp_v fr i)) by (intros i Hi; rewrite AGX by lia; apply EFB; lia).
pose proof (t4b_rec fr HP) as Hrec.
destruct (t4b_vals fr HP) as (V16 & V17 & V18 & V19 & V32 & V33 & V34 & V35).
assert (UA : forall i, (i < 39)%nat -> U E (SOff (40 + i) 0) = cp_v fr i)
  by (intros i Hi; apply (U_atom E (40 + i)); [apply HA; exact Hi | pose proof (cp_v_range fr i); lia]).
assert (U56 : U E (SOff 56 0) = 205) by exact (eq_trans (UA 16%nat ltac:(lia)) V16).
assert (U57a : U E (SOff 57 0) = 234) by exact (eq_trans (UA 17%nat ltac:(lia)) V17).
assert (U58 : U E (SOff 58 0) = 4) by exact (eq_trans (UA 18%nat ltac:(lia)) V18).
assert (U59 : U E (SOff 59 0) = 3) by exact (eq_trans (UA 19%nat ltac:(lia)) V19).
assert (U72 : U E (SOff 72 0) = 18) by exact (eq_trans (UA 32%nat ltac:(lia)) V32).
assert (U73 : U E (SOff 73 0) = 18) by exact (eq_trans (UA 33%nat ltac:(lia)) V33).
assert (U57 : U E (SAlu ALU_AND (SOff 57 0) (SLit 255)) = 234) by (rewrite U_and_lit by lia; rewrite U57a; reflexivity).
assert (Ua : U E (SAlu ALU_OR (SOff 56 0) (SAlu ALU_AND (SOff 57 0) (SLit 255))) = 239)
  by (rewrite (U_SAlu E ALU_OR (SOff 56 0) (SAlu ALU_AND (SOff 57 0) (SLit 255))), U56, U57; vm_compute; reflexivity).
assert (U7475 : U E (SAlu ALU_OR (SAlu ALU_SLL (SOff 74 0) (SLit 8)) (SOff 75 0)) = 257)
  by (rewrite (t4b_b2v E 74 75 fr 34 35 (HA 34%nat ltac:(lia)) (HA 35%nat ltac:(lia))), V34, V35; reflexivity).
clear UA U57a.
(* Cut B to the ten branches, each side either followed or refuted. *)
do 10 (t4b_step RUNTO HS HJ2 SHOK AGX fpos F EF; t4b_br RUN BR HS SHOK).
(* The last run, to the join (0x823a8); it adds atoms from 656 on. *)
t4b_step RUNTO HS HJ2 SHOK AGX fpos F EF.
(* Cut J: carry the facts to the valuation of the last run, read the out struct back, make the frame and its
   shadow writable, join to ss_cutJ (atoms 700..723) and apply the cut-J hypothesis. *)
lazymatch type of HS with st_ok_pi _ _ ?E1 _ _ =>
assert (AGE : forall nn, (nn < 656)%nat -> ew E1 nn = ew E nn) by (intros nn Hnn; rewrite ?ew_ewset_other by lia; reflexivity);
assert (HA1 : forall i, (i < 39)%nat -> ew E1 (40 + i) = Z_to_bv 64 (cp_v fr i)) by (intros i Hi; rewrite AGE by lia; apply HA; exact Hi);
assert (Hbc1 : ew E1 640 = Z_to_bv 64 0 <-> cp_bcast fr = true) by (rewrite AGE by lia; exact Hbc);
lazymatch type of AGX with forall n0, _ -> ew _ n0 = ew ?E0 n0 =>
assert (AGX1 : forall n0, (n0 < 512)%nat -> ew E1 n0 = ew E0 n0) by (intros n0 Hn0; rewrite AGE by lia; apply AGX; exact Hn0) end;
lazymatch type of RF with _ = ?v => assert (RF1 : ew E1 516 = v) by (rewrite AGE by lia; exact RF) end;
lazymatch type of E528 with _ = ?v => assert (E5281 : ew E1 528 = v) by (rewrite AGE by lia; exact E528) end;
lazymatch type of E529 with _ = ?v => assert (E5291 : ew E1 529 = v) by (rewrite AGE by lia; exact E529) end
end.
clear AGX RF E528 E529. rename AGX1 into AGX, RF1 into RF, E5281 into E528, E5291 into E529.
pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as R12.
lazymatch type of R12 with region_ok ?sg ?Ex ?mm _ => change (region_ok sg Ex mm (YP09.mkRegion (Some 12%nat) 0 36 0 36 t4b_out)) in R12 end.
lazymatch type of HS with st_ok_pi _ _ ?E1 _ (restrict (w_H ?Wx) ?msx) =>
pose proof (t4b_out_bytes E1 (w_H Wx) (ms_mem msx) o fr R12
  ltac:(cbn [base_val]; rewrite (AGX 12%nat) by lia; exact B12) HA1 Hbc1 Hrec) as OUT end.
prreg HS (10%bv : bv 5) Ra0.
destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos (proj1 HJ2) Hfin2) as (_ & _ & HFp & HFSp).
change (fs_frame_bytes 1) with 128 in HFp, HFSp. change (128 / 8) with 16 in HFSp.
lazymatch type of HS with st_ok_pi ?sg _ ?E1 _ (restrict (w_H ?Wx) ?msx) =>
assert (W529 : forall q, 0 <= q < 16 -> writable_at sg (mrestrict (w_H Wx) (ms_mem msx)) (base_val E1 (Some 529%nat) + q))
  by (intros q Hq; cbn [base_val]; rewrite E529, unsigned_lit_small by (unfold SB; lia); apply (apresent_writable sg);
      unfold shadow_addr in HFSp; rewrite <- SB_SHADOW_OFF in HFSp; apply (proj1 (HFSp q Hq)));
assert (W516 : forall q, 0 <= q < 128 -> writable_at sg (mrestrict (w_H Wx) (ms_mem msx)) (base_val E1 (Some 516%nat) + q))
  by (intros q Hq; cbn [base_val]; rewrite RF, unsigned_lit_small by lia; apply (apresent_writable sg);
      apply (proj1 (HFp (F + q) ltac:(lia)))) end.
t4b_rw HS 529%nat 16 W529. t4b_rw HS 516%nat 128 W516. clear W529 W516 HFp HFSp R12.
ra_join HS ss_cutJ 700%nat pz_deadJ idtac.
lazymatch type of HS with st_ok_pi _ _ _ ss_cutJ _ => idtac | _ => fail "the joined state is not ss_cutJ" end.
ra_join_val HS 700%nat 0%nat Ra0 E700.
pz_rebase HS AGX.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ (restrict _ ?msv) => apply (HJc Ev msv) end.
- do 6 (split; [assumption|]). assumption.
- exact HS.
- rewrite E700, (t4b_kind n fr Hhdr HP). reflexivity.
- intros q Hq. rewrite (t4b_kind n fr Hhdr HP). exact (OUT q Hq).
Qed.
End d.
End b.
