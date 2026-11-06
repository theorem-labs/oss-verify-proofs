(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: relocated to libreac/fuzz_disco (from the walk of the same function of libreac's fuzz_grant, the same code at other addresses; restated on fuzz_disco's cut specifications, whose memory clause is pz_kept). *)
(* reac_ctrl_parse, the walk from cut B (0x87570) to cut J for the class-4 frames of the other records (seg = 3, not cp_amp): GRANT (5)
   (pz_P4c; a second attack on CtrlParseTail4.v). *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YG0s YM05.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import PaRun PaShadow PaJournal DiscoSyms DiscoList DiscoPa DiscoPaLib.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import DiscoBase YC81 YC4b YC1g YC1h YC45 YC85 DiscoFrame YC88.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import RcKind RcParse.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import CtrlParseLib KindOfLink1 DiscoRo ACj1 DiscoACja.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import CtrlParseCut.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
#[local] Ltac Zify.zify_pre_hook ::= try unfold YImgTop.IMG_TOP, YImgTop.IMG_LO in *.
(* The out struct at cut J on the three paths (0x87ac0: kind 5): the kind (4 bytes), the record's two bytes
   f35 f34 (0x8797c), the opcode f22, blk_len f21 f20, segment f19, link f18, the counter f14 f15,
   is_broadcast (seqz of atom 640), the two copies of the address bytes (cut B) and zeros. *)
Definition t4c_outJ : list YP09.chunk :=
[YP09.mkChunk 0 (CVal 4 (SLit 5));
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
 YP09.mkChunk 27 (CZero 1); YP09.mkChunk 30 (CZero 6)].
(* The chunk that covers an offset: its offset, its value and the index inside it. *)
Fixpoint t4c_find (cs : list YP09.chunk) (off : Z) : option (Z * cval * Z) :=
match cs with
| [] => None
| c :: t => if (YP09.c_off c <=? off) && (off <? YP09.c_off c + YP09.c_len c)
  then Some (YP09.c_off c, YP09.c_val c, off - YP09.c_off c) else t4c_find t off
end.
Lemma t4c_lor : forall a b, 0 <= a -> 0 <= b < 256 -> Z.lor (a * 256) b = a * 256 + b.
Proof.
intros a b Ha Hb.
assert (HL : Z.land (a * 256) b = 0).
{ apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
  destruct (Z.lt_ge_cases i 8) as [Hi8|Hi8].
  - change 256 with (2 ^ 8). rewrite Z.mul_pow2_bits_low by lia. reflexivity.
  - rewrite <- (Z.mod_small b (2 ^ 8)) by (cbn; lia). rewrite Z.mod_pow2_bits_high by lia. apply andb_false_r. }
rewrite <- (Z.lxor_lor _ _ HL). symmetry. apply Z.add_nocarry_lxor. exact HL.
Qed.
Lemma t4c_land255 : forall v, 0 <= v < 256 -> Z.land v 255 = v.
Proof. intros v Hv. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_small. change (2 ^ 8) with 256. lia. Qed.
Lemma t4c_bv8 : forall x (b : byte), x mod 256 = bv_unsigned b -> Z_to_bv 8 x = b.
Proof. intros x b H. apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. exact H. Qed.
Lemma t4c_byte0 : forall E e, byte_of_word (sv_denot E e) 0 = Z_to_bv 8 (U E e).
Proof. intros E e. unfold byte_of_word, U. rewrite Z.mul_0_r, Z.shiftr_0_r. reflexivity. Qed.
Lemma t4c_byte1 : forall E e, byte_of_word (sv_denot E e) 1 = Z_to_bv 8 (U E e / 256).
Proof. intros E e. unfold byte_of_word, U. rewrite Z.shiftr_div_pow2 by lia. reflexivity. Qed.
Lemma t4c_bytej : forall E e j, 0 <= U E e < 256 -> 1 <= j -> byte_of_word (sv_denot E e) j = cp_z.
Proof.
intros E e j HU Hj. unfold byte_of_word. change (bv_unsigned (sv_denot E e)) with (U E e).
rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_small; [reflexivity|].
assert (H8 : 2 ^ 8 <= 2 ^ (8 * j)) by (apply Z.pow_le_mono_r; lia). change (2 ^ 8) with 256 in H8. lia.
Qed.
(* The value of the two-byte loads f[h] << 8 | f[l]. *)
Lemma t4c_U2 : forall E nh nl x y, ew E nh = Z_to_bv 64 x -> ew E nl = Z_to_bv 64 y -> 0 <= x < 256 -> 0 <= y < 256 ->
U E (SAlu ALU_OR (SAlu ALU_SLL (SOff nh 0) (SLit 8)) (SOff nl 0)) = x * 256 + y.
Proof.
intros E nh nl x y Hh Hl Rx Ry.
rewrite !U_SAlu. cbn [zalu_raw]. rewrite (U_atom E nh x Hh), (U_atom E nl y Hl), (U_lit E 8) by lia.
change (Z.land 8 63) with 8. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 8) with 256.
rewrite (zcanon_id (x * 256)) by (unfold M64; lia). rewrite t4c_lor by lia. apply zcanon_id. unfold M64. lia.
Qed.
Lemma t4c_b1 : forall E n fr i, ew E n = Z_to_bv 64 (cp_v fr i) -> byte_of_word (sv_denot E (SOff n 0)) 0 = cp_b fr i.
Proof.
intros E n fr i H. pose proof (cp_v_range fr i). rewrite t4c_byte0, (U_atom E n (cp_v fr i) H) by lia.
unfold cp_v. apply Z_to_bv_bv_unsigned.
Qed.
Lemma t4c_b2lo : forall E nh nl fr ih il, ew E nh = Z_to_bv 64 (cp_v fr ih) -> ew E nl = Z_to_bv 64 (cp_v fr il) ->
byte_of_word (sv_denot E (SAlu ALU_OR (SAlu ALU_SLL (SOff nh 0) (SLit 8)) (SOff nl 0))) 0 = cp_b fr il.
Proof.
intros E nh nl fr ih il Hh Hl. pose proof (cp_v_range fr ih) as Rh. pose proof (cp_v_range fr il) as Rl.
rewrite t4c_byte0, (t4c_U2 E nh nl _ _ Hh Hl Rh Rl). apply t4c_bv8.
rewrite Z.add_comm, Z_mod_plus_full. unfold cp_v in *. apply Z.mod_small. lia.
Qed.
Lemma t4c_b2hi : forall E nh nl fr ih il, ew E nh = Z_to_bv 64 (cp_v fr ih) -> ew E nl = Z_to_bv 64 (cp_v fr il) ->
byte_of_word (sv_denot E (SAlu ALU_OR (SAlu ALU_SLL (SOff nh 0) (SLit 8)) (SOff nl 0))) 1 = cp_b fr ih.
Proof.
intros E nh nl fr ih il Hh Hl. pose proof (cp_v_range fr ih) as Rh. pose proof (cp_v_range fr il) as Rl.
rewrite t4c_byte1, (t4c_U2 E nh nl _ _ Hh Hl Rh Rl). rewrite Z.div_add_l by lia.
rewrite (Z.div_small (cp_v fr il) 256) by lia. rewrite Z.add_0_r. apply t4c_bv8.
unfold cp_v in *. apply Z.mod_small. lia.
Qed.
(* is_broadcast: seqz of the bcmp wrapper's result (atom 640). *)
Lemma t4c_sltu : forall E fr, (ew E 640 = Z_to_bv 64 0 <-> cp_bcast fr = true) ->
U E (SAlu ALU_SLTU (SOff 640 0) (SLit 1)) = if cp_bcast fr then 1 else 0.
Proof.
intros E fr Hbc. rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_lit E 1) by lia. rewrite U_SOff, Z.add_0_r.
pose proof (bv_unsigned_in_range 64 (ew E 640)) as R. change (bv_modulus 64) with (2 ^ 64) in R.
rewrite (zcanon_id (bv_unsigned (ew E 640))) by (unfold M64; lia).
destruct (cp_bcast fr) eqn:Hb.
- rewrite (proj2 Hbc ltac:(first [exact Hb | reflexivity])). reflexivity.
- assert (Hn : bv_unsigned (ew E 640) <> 0).
  { intros Hz. assert (Hw : ew E 640 = Z_to_bv 64 0) by (apply bv_eq; rewrite Hz; reflexivity).
    apply Hbc in Hw. congruence. }
  replace (bv_unsigned (ew E 640) <? 1) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.
Lemma t4c_sltu0 : forall E fr, (ew E 640 = Z_to_bv 64 0 <-> cp_bcast fr = true) ->
byte_of_word (sv_denot E (SAlu ALU_SLTU (SOff 640 0) (SLit 1))) 0 = if cp_bcast fr then Z_to_bv 8 1 else cp_z.
Proof. intros E fr Hbc. rewrite t4c_byte0, (t4c_sltu E fr Hbc). destruct (cp_bcast fr); reflexivity. Qed.
Lemma t4c_sltuj : forall E e1 e2 j, 1 <= j -> byte_of_word (sv_denot E (SAlu ALU_SLTU e1 e2)) j = cp_z.
Proof.
intros E e1 e2 j Hj. apply t4c_bytej; [|lia]. rewrite U_SAlu. cbn [zalu_raw].
destruct (U E e1 <? U E e2); unfold zcanon, M64; rewrite Z.mod_small by lia; lia.
Qed.
(* The branch conditions of the walk. *)
Lemma t4c_or_ne0 : forall E fr, ew E 56 = Z_to_bv 64 (cp_v fr 16) -> ew E 57 = Z_to_bv 64 (cp_v fr 17) ->
cp_v fr 16 = 205 -> cp_v fr 17 = 234 ->
branch_taken BC_NE (sv_denot E (SAlu ALU_OR (SOff 56 0) (SAlu ALU_AND (SOff 57 0) (SLit 255)))) (sv_denot E (SLit 0)) = true.
Proof.
intros E fr H6 H7 T6 T7. rewrite T6 in H6. rewrite T7 in H7.
rewrite branch_ne_U, U_SAlu. cbn [zalu_raw]. rewrite U_and_lit by lia.
rewrite (U_atom E 56 205 H6), (U_atom E 57 234 H7), (U_lit E 0) by lia. reflexivity.
Qed.
Lemma t4c_ne_atom : forall E n v x, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= x < 2 ^ 64 ->
branch_taken BC_NE (sv_denot E (SOff n 0)) (sv_denot E (SLit x)) = negb (v =? x).
Proof. intros E n v x H Hv Hx. rewrite branch_ne_U, (U_atom E n v H Hv), (U_lit E x Hx). reflexivity. Qed.
Lemma t4c_eq_atom : forall E n v x, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= x < 2 ^ 64 ->
branch_taken BC_EQ (sv_denot E (SOff n 0)) (sv_denot E (SLit x)) = (v =? x).
Proof. intros E n v x H Hv Hx. rewrite branch_eq_U, (U_atom E n v H Hv), (U_lit E x Hx). reflexivity. Qed.
Lemma t4c_ne_and : forall E n v x, ew E n = Z_to_bv 64 v -> 0 <= v < 256 -> 0 <= x < 2 ^ 64 ->
branch_taken BC_NE (sv_denot E (SAlu ALU_AND (SOff n 0) (SLit 255))) (sv_denot E (SLit x)) = negb (v =? x).
Proof.
intros E n v x H Hv Hx. rewrite branch_ne_U, U_and_lit by lia.
rewrite (U_atom E n v H) by lia. rewrite (U_lit E x Hx). rewrite t4c_land255 by lia. reflexivity.
Qed.
(* One byte of the out struct against the model's cp_struct. *)
Local Ltac t4c_byte HA Hbc :=
lazymatch goal with
| |- Some (Z_to_bv 8 0) = Some cp_z => reflexivity
| |- Some (byte_of_word (sv_denot _ (SLit _)) _) = Some _ => reflexivity
| |- Some (byte_of_word (sv_denot ?E (SAlu ALU_SLTU _ _)) 0) = Some _ => f_equal; exact (t4c_sltu0 E _ Hbc)
| |- Some (byte_of_word (sv_denot _ (SAlu ALU_SLTU _ _)) _) = Some _ => f_equal; apply t4c_sltuj; lia
| |- Some (byte_of_word (sv_denot ?E (SOff ?n 0)) 0) = Some (cp_b ?fr ?i) =>
  f_equal; exact (t4c_b1 E n fr i (HA i ltac:(lia)))
| |- Some (byte_of_word (sv_denot ?E (SAlu ALU_OR (SAlu ALU_SLL (SOff ?nh 0) (SLit 8)) (SOff ?nl 0))) 0) = Some (cp_b ?fr ?il) =>
  let ih := eval vm_compute in (nh - 40)%nat in f_equal; exact (t4c_b2lo E nh nl fr ih il (HA ih ltac:(lia)) (HA il ltac:(lia)))
| |- Some (byte_of_word (sv_denot ?E (SAlu ALU_OR (SAlu ALU_SLL (SOff ?nh 0) (SLit 8)) (SOff ?nl 0))) 1) = Some (cp_b ?fr ?ih) =>
  let il := eval vm_compute in (nl - 40)%nat in f_equal; exact (t4c_b2hi E nh nl fr ih il (HA ih ltac:(lia)) (HA il ltac:(lia)))
| |- ?g => idtac "T4C-BYTE" g; fail
end.
(* The windows of a run lie in the stack below the entry sp, the out struct or the own frame. *)
Local Ltac t4c_win :=
let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let a := fresh "a" in
let Hin := fresh "Hin" in let Ha := fresh "Ha" in let Hq := fresh "Hq" in
intros b wlo whi a Hin Ha;
lazymatch type of Hin with In _ ?l => let l' := eval vm_compute in l in change (In (b, wlo, whi) l') in Hin end; cbn [In] in Hin;
repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Ha; revert Ha; pz_bases; intro Ha; cbv beta;
unfold pz_nf, SHADOW_OFF, SB in *; lia |]); destruct Hin.
Section b. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Context {PI : PAImg disco_listing}.
Context {RO : ro_below_ofl (@pa_segs _ disco_listing PI) (@pa_relro_lo _ disco_listing PI) (@pa_relro_hi _ disco_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation VAL := (@pa_val _ disco_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
Lemma t4c_find_ok : forall E base cs off, pz_chunk_at E base cs off =
match t4c_find cs off with Some (co, cv, j) => YP09.cbyte SEGS E (base + co) cv j | None => None end.
Proof.
intros E base cs off. induction cs as [|c t IH]; cbn [pz_chunk_at t4c_find]; [reflexivity|].
destruct (_ && _); [reflexivity | exact IH].
Qed.
(* The 36 bytes of the out struct at cut J are the model's cp_struct fr 5. *)
Lemma t4c_out_bytes : forall E H mem o fr,
region_ok SEGS E (mrestrict H mem) (YP09.mkRegion (Some 12%nat) 0 36 0 36 t4c_outJ) ->
base_val E (Some 12%nat) = o ->
(forall i, (i < 39)%nat -> ew E (40 + i) = Z_to_bv 64 (cp_v fr i)) ->
(ew E 640 = Z_to_bv 64 0 <-> cp_bcast fr = true) ->
cp_rec fr = true ->
forall i, (i < 36)%nat -> aview SEGS H mem (o + Z.of_nat i) = Some (bv_unsigned (nth i (cp_struct fr 5) cp_z)).
Proof.
intros E H mem o fr Hr Hb HA Hbc Hrec i Hi. subst o.
apply (pz_region_byte E H mem _ (Z.of_nat i) _ Hr).
cbn [YP09.r_base YP09.r_chunks]. rewrite t4c_find_ok.
unfold cp_struct. rewrite Hrec. replace (5 =? 6) with false by reflexivity.
do 36 (destruct i as [|i]; [
  lazymatch goal with |- context [t4c_find ?cs ?off] => let v := eval vm_compute in (t4c_find cs off) in change (t4c_find cs off) with v end;
  cbn [YP09.cbyte nth app]; t4c_byte HA Hbc | ]).
lia.
Qed.
(* The caller's memory after a run: the run wrote only its windows (the stack below sp, the out struct). *)
Local Ltac t4c_kp :=
lazymatch goal with
| HFr : frame_of ?Ef ?rsf (mrestrict _ ?mA) (mrestrict _ ?mB), HF : frame_of _ _ (ms_mem _) (ms_mem _), HG : mem_grows _ _,
  KP : pz_kept ?B ?lyc ?Sc ?W ?memc _ ?slo ?sp ?o,
  HAR : AR _ ?B ?lyc ?Sc ?W ?memc ?mdc,
  Hfrs2 : frames ?S2 = (1, ?fpos) :: frames ?Sc,
  HARc : AR _ ?B ?lyc ?S2 ?W _ _,
  Eab : ablocks ?B ?lyc ?S2 = ablocks ?B ?lyc ?Sc,
  EF : ?F = frame_addr ?lyc 1 ?fpos, EFL : ?FL = flag_addr ?lyc 1 ?fpos,
  FFL : frame_flag_lawP _ ?B, LAWS : AR_laws _ ?B,
  Hoimg : off_img ?o 36,
  B33 : bv_unsigned (ew _ 33) = ?sp1 |- _ =>
  let Hw := fresh "Hw" in let KP' := fresh "KP" in
  assert (Hw : forall b wlo whi a, In (b, wlo, whi) (windows rsf) -> base_val Ef b + wlo <= a < base_val Ef b + whi ->
  (fun a => (sp1 <= a < sp) \/ (o <= a < o + 36) \/ pz_nf F FL a) a) by t4c_win;
  pose proof (pz_kept_own B LAWS lyc Sc S2 W memc mdc _ _ mA mB slo sp o fpos F FL
  (fun a => (sp1 <= a < sp) \/ (o <= a < o + 36) \/ pz_nf F FL a) HAR HARc Hfrs2 Eab EF EFL FFL
  ltac:(lia) ltac:(lia) Hoimg ltac:(intros a [Ha|[Ha|Ha]]; [left; lia | right; left; exact Ha | right; right; exact Ha]) KP
  (kept_of_frame _ _ _ _ _ _ HFr Hw) (fun a Ha => apresent_grows _ _ _ a HG Ha)) as KP';
  clear KP Hw HF HFr HG; rename KP' into KP
end.
(* One run to the next branch or to cut J, and the caller's memory after it. *)
Local Ltac t4c_run :=
lazymatch goal with
| RUNTO : context [sym_run_toN_pi_tok _ _ _ _ _ _ _ _ _], HS : st_ok_pi _ _ _ _ _,
  HJ2 : ajournal _ _ _ _ _ _ _ _ _ _ ((1, ?fpos) :: _) _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _,
  AG : forall n0, (n0 < 33)%nat -> _, EF : ?F = frame_addr _ 1 ?fpos |- _ =>
  paj_run_to_tok RUNTO HS HJ2 SHOK PZspan AF_JOIN; [ awrFL_with ltac:(idtac; pz_awr_hd) AG fpos F I | t4c_kp ]
end.
(* The out struct at cut J: region 12 holds t4c_outJ, whose bytes are cp_struct fr 5. *)
Local Ltac t4c_out HO HA Hbc Hrec :=
lazymatch goal with
| HS : st_ok_pi _ _ ?Ex ?ssx (restrict (w_H ?W) ?msv), AGX : forall n0, (n0 < 512)%nat -> ew ?Ex n0 = _,
  B12 : bv_unsigned (ew _ 12) = ?o |- _ =>
  let rs := eval vm_compute in (ss_mem ssx) in
  let ix := idx_of_base rs 12%nat in let ix := eval vm_compute in ix in
  let r := eval vm_compute in (nth ix rs got_regionP) in
  let R12 := fresh "R12" in
  pose proof (st_ok_pi_region_nth Ex ssx (restrict (w_H W) msv) ix r HS ltac:(vm_compute; reflexivity)) as R12;
  cbn [ms_mem restrict] in R12;
  pose proof (t4c_out_bytes Ex (w_H W) (ms_mem msv) o _ R12
    ltac:(cbn [base_val]; rewrite (AGX 12%nat) by lia; exact B12) HA Hbc Hrec) as HO;
  clear R12
end.
(* The frame (516) and its shadow (529) become writable again (cut J's windows). *)
Local Ltac t4c_rw :=
lazymatch goal with
| HS : st_ok_pi _ _ ?Ex ?ssx ?msx, E529 : ew ?Ex 529 = _, HJ2 : ajournal _ _ _ _ _ _ _ _ _ _ ((1, _) :: _) _ _ _ _ _ _,
  HFSp : forall m md', AR _ _ _ _ _ m md' -> forall a, _ <= a < _ + 16 -> apresent _ m a |- _ =>
  let rs := eval vm_compute in (ss_mem ssx) in
  let ix := idx_of_base rs 529%nat in let ix := eval vm_compute in ix in
  let r := eval vm_compute in (nth ix rs got_regionP) in
  let HS' := fresh "HS" in
  pose proof (ast_ok_pi_set_region Ex ssx msx ix r (set_window r 0 16) HS ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity)
  (region_ok_rewindow _ Ex _ r 0 16 (st_ok_pi_region_nth Ex ssx msx ix r HS ltac:(vm_compute; reflexivity))
  ltac:(cbn [YP09.r_base base_val ms_mem restrict mkst]; rewrite E529, unsigned_lit_small by (unfold SB; lia);
  let o0 := fresh "o0" in let Ho0 := fresh "Ho0" in
  intros o0 Ho0; apply (apresent_writable _); apply (HFSp _ _ (proj1 HJ2)); lia))) as HS';
  clear HS; rename HS' into HS; pz_norm HS
end;
lazymatch goal with
| HS : st_ok_pi _ _ ?Ex ?ssx ?msx, RF : ew ?Ex 516 = _, HJ2 : ajournal _ _ _ _ _ _ _ _ _ _ ((1, _) :: _) _ _ _ _ _ _,
  HFp : forall m md', AR _ _ _ _ _ m md' -> forall a, _ <= a < _ + 128 -> apresent _ m a |- _ =>
  let rs := eval vm_compute in (ss_mem ssx) in
  let ix := idx_of_base rs 516%nat in let ix := eval vm_compute in ix in
  let r := eval vm_compute in (nth ix rs got_regionP) in
  let HS' := fresh "HS" in
  pose proof (ast_ok_pi_set_region Ex ssx msx ix r (set_window r 0 128) HS ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity)
  (region_ok_rewindow _ Ex _ r 0 128 (st_ok_pi_region_nth Ex ssx msx ix r HS ltac:(vm_compute; reflexivity))
  ltac:(cbn [YP09.r_base base_val ms_mem restrict mkst]; rewrite RF, unsigned_lit_small by lia;
  let o0 := fresh "o0" in let Ho0 := fresh "Ho0" in
  intros o0 Ho0; apply (apresent_writable _); apply (HFp _ _ (proj1 HJ2)); lia))) as HS';
  clear HS; rename HS' into HS; pz_norm HS
end.
(* At cut J (0x87750) with a0 = 5: read the out struct back, join to ss_cutJ and apply the cut J hypothesis. *)
Local Ltac t4c_join HA Hbc Hrec Hhdr Hkind :=
let HO := fresh "HO" in let R0 := fresh "R0" in let E700 := fresh "E700" in
t4c_out HO HA Hbc Hrec; t4c_rw;
lazymatch goal with HS : st_ok_pi _ _ _ _ _ |- _ =>
  prreg HS (10%bv : bv 5) R0;
  ra_join HS ss_cutJ 700%nat pz_deadJ ltac:(idtac);
  ra_join_val HS 700%nat 0%nat R0 E700;
  lazymatch goal with AGX : forall n0, (n0 < 512)%nat -> _ |- _ => pz_rebase HS AGX end
end;
lazymatch goal with
| HS : st_ok_pi _ _ ?Ev _ (restrict _ ?msv),
  HJc : forall (E : env) (ms : machine_state) (md : Model), _ -> st_ok_pi _ _ E ss_cutJ _ -> _,
  AGX : forall n0, (n0 < 512)%nat -> ew ?Ev n0 = _, RF : ew ?Ev 516 = _, E528 : ew ?Ev 528 = _, E529 : ew ?Ev 529 = _,
  HJ2 : ajournal _ _ _ _ _ _ _ _ _ _ ((1, _) :: _) _ _ _ (ms_mem ?msv) _ _,
  KP : pz_kept _ _ _ _ _ (ms_mem ?msv) _ _ _ |- _ =>
  apply (HJc Ev msv);
  [ split; [assumption|]; split; [exact AGX|]; split; [exact RF|]; split; [exact E528|]; split; [exact E529|];
    split; [exact HJ2 | exact KP]
  | exact HS
  | unfold ctrlparse; rewrite Hhdr, Hkind; cbn [fst]; exact E700
  | let j := fresh "j" in let Hj := fresh "Hj" in
    intros j Hj; unfold ctrlparse; rewrite Hhdr, Hkind; cbn [snd]; exact (HO j Hj) ]
end.
Lemma pz_tail4c : forall B G, pz_rt B G -> forall c, pz_ok B c -> pz_cutJ_spec B c -> pz_cutB_case B c pz_P4c.
Proof.
intros B G RT c Hok HJc Hbig E ms md Hcur HS SHOK Hhdr Hbc HP.
pz_open c Hok. pz_open_rt RT. pz_open_cur Hcur. pz_open_f Hbig. pz_std.
pose proof (paj_run_to (fx := fq) B LAWS) as RUNTO. pose proof (paj_run (fx := fq) B LAWS) as RUN.
pose proof (paj_branch (fx := fq) (PI := PI)) as BR.
lazymatch type of AGX with forall n0, _ -> ew _ n0 = ew ?E0 n0 =>
assert (AG : forall n0, (n0 < 33)%nat -> ew E n0 = ew E0 n0) by (intros; apply AGX; lia) end.
assert (HFp : forall m md', AR SEGS B lyc S2 W m md' -> forall a, F <= a < F + 128 -> apresent (w_H W) m a).
{ intros m md' HA a Ha. destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos HA Hfin2) as (_ & _ & Hp & _).
rewrite <- EF in Hp. change (fs_frame_bytes 1) with 128 in Hp. exact (proj1 (Hp a Ha)). }
assert (HFSp : forall m md', AR SEGS B lyc S2 W m md' -> forall a, SB + F / 8 <= a < SB + F / 8 + 16 -> apresent (w_H W) m a).
{ intros m md' HA a Ha. destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos HA Hfin2) as (_ & _ & _ & Hp).
rewrite <- EF in Hp. unfold shadow_addr in Hp. change (fs_frame_bytes 1 / 8) with 16 in Hp.
replace a with (SHADOW_OFF + F / 8 + (a - (SB + F / 8))) by (unfold SHADOW_OFF, SB; lia).
assert (Hi : 0 <= a - (SB + F / 8) < 16) by (unfold SB in *; lia).
apply (proj1 (Hp (a - (SB + F / 8)) Hi)). }
(* The frame bytes in the cut-B valuation, and pz_P4c as arithmetic. *)
assert (HA : forall i, (i < 39)%nat -> ew E (40 + i) = Z_to_bv 64 (cp_v fr i)) by (intros i Hi; rewrite AGX by lia; apply EFB; exact Hi).
unfold pz_P4c, pz_P4, cp_type in HP. destruct HP as ((QT & Q18) & Q19 & Qamp).
apply andb_true_iff in QT as [Q16 Q17]. apply Z.eqb_eq in Q16, Q17.
assert (A56 : ew E 56 = Z_to_bv 64 (cp_v fr 16)) by exact (HA 16%nat ltac:(lia)).
assert (A57 : ew E 57 = Z_to_bv 64 (cp_v fr 17)) by exact (HA 17%nat ltac:(lia)).
assert (A58 : ew E 58 = Z_to_bv 64 (cp_v fr 18)) by exact (HA 18%nat ltac:(lia)).
assert (A59 : ew E 59 = Z_to_bv 64 (cp_v fr 19)) by exact (HA 19%nat ltac:(lia)).
assert (A72 : ew E 72 = Z_to_bv 64 (cp_v fr 32)) by exact (HA 32%nat ltac:(lia)).
assert (A73 : ew E 73 = Z_to_bv 64 (cp_v fr 33)) by exact (HA 33%nat ltac:(lia)).
assert (A74 : ew E 74 = Z_to_bv 64 (cp_v fr 34)) by exact (HA 34%nat ltac:(lia)).
assert (A75 : ew E 75 = Z_to_bv 64 (cp_v fr 35)) by exact (HA 35%nat ltac:(lia)).
pose proof (cp_v_range fr 16) as R16. pose proof (cp_v_range fr 17) as R17.
pose proof (cp_v_range fr 18) as R18. pose proof (cp_v_range fr 19) as R19.
pose proof (cp_v_range fr 32) as R32. pose proof (cp_v_range fr 33) as R33.
pose proof (cp_v_range fr 34) as R34. pose proof (cp_v_range fr 35) as R35.
assert (Hkind : cp_kind fr = 5) by (unfold cp_kind, cp_type; rewrite Q16, Q17, Q18, Q19, Qamp; reflexivity).
assert (Hrec : cp_rec fr = true) by (unfold cp_rec, cp_type; rewrite Q16, Q17, Q18, Q19; reflexivity).
(* 1. Cut B to 0x87730 (the stores of is_broadcast, the counter, link, segment, blk_len and the opcode):
   bnez f[16] | f[17], taken (cd ea). *)
t4c_run.
psrr_branch_tok RUN BR HS SHOK PZspan;
[ clear Hc
| exfalso; rewrite (t4c_or_ne0 E fr A56 A57 Q16 Q17) in Hc; discriminate Hc ].
(* 2. 0x87848 bne f[16],0xcf: taken. *)
t4c_run.
psrr_branch_tok RUN BR HS SHOK PZspan;
[ clear Hc
| exfalso; rewrite (t4c_ne_atom E 56 (cp_v fr 16) 207 A56 ltac:(lia) ltac:(lia)) in Hc;
  apply negb_false_iff, Z.eqb_eq in Hc; lia ].
(* 3. 0x87870 bne f[16],0xce: taken. *)
t4c_run.
psrr_branch_tok RUN BR HS SHOK PZspan;
[ clear Hc
| exfalso; rewrite (t4c_ne_atom E 56 (cp_v fr 16) 206 A56 ltac:(lia) ltac:(lia)) in Hc;
  apply negb_false_iff, Z.eqb_eq in Hc; lia ].
(* 4. 0x87898 bne f[16],0xcd: not taken. *)
t4c_run.
psrr_branch_tok RUN BR HS SHOK PZspan;
[ exfalso; rewrite (t4c_ne_atom E 56 (cp_v fr 16) 205 A56 ltac:(lia) ltac:(lia)) in Hc;
  apply negb_true_iff, Z.eqb_neq in Hc; lia
| clear Hc ].
(* 5. 0x878a0 bne f[17],0xea: not taken. *)
t4c_run.
psrr_branch_tok RUN BR HS SHOK PZspan;
[ exfalso; rewrite (t4c_ne_and E 57 (cp_v fr 17) 234 A57 ltac:(lia) ltac:(lia)) in Hc;
  apply negb_true_iff, Z.eqb_neq in Hc; lia
| clear Hc ].
(* 6. 0x878a8 beq f[18],4 (link 4, the record container): taken. *)
t4c_run.
psrr_branch_tok RUN BR HS SHOK PZspan;
[ clear Hc
| exfalso; rewrite (t4c_eq_atom E 58 (cp_v fr 18) 4 A58 ltac:(lia) ltac:(lia)) in Hc;
  apply Z.eqb_neq in Hc; lia ].
(* 7. 0x8791c bne f[19],3 (segment 3, a record): not taken. *)
t4c_run.
psrr_branch_tok RUN BR HS SHOK PZspan;
[ exfalso; rewrite (t4c_ne_atom E 59 (cp_v fr 19) 3 A59 ltac:(lia) ltac:(lia)) in Hc;
  apply negb_true_iff, Z.eqb_neq in Hc; lia
| clear Hc ].
(* 8. 0x87998 bne f[32],0x12 (after the store of f35 f34 at o + 28). *)
t4c_run.
psrr_branch_tok RUN BR HS SHOK PZspan.
{ (* Path 1: f[32] <> 0x12: 0x87ac0, kind 5, to cut J. *)
clear Hc. t4c_run. t4c_join HA Hbc Hrec Hhdr Hkind. }
rewrite (t4c_ne_atom E 72 (cp_v fr 32) 18 A72 ltac:(lia) ltac:(lia)) in Hc.
apply negb_false_iff, Z.eqb_eq in Hc. rename Hc into C32.
(* 9. 0x879b8 bne f[33],0x12. *)
t4c_run.
psrr_branch_tok RUN BR HS SHOK PZspan.
{ (* Path 2: f[32] = 0x12, f[33] <> 0x12: 0x87ac0, kind 5, to cut J. *)
clear Hc. t4c_run. t4c_join HA Hbc Hrec Hhdr Hkind. }
rewrite (t4c_ne_atom E 73 (cp_v fr 33) 18 A73 ltac:(lia) ltac:(lia)) in Hc.
apply negb_false_iff, Z.eqb_eq in Hc. rename Hc into C33.
(* 10. 0x879c0 bne f[34] << 8 | f[35],0x101. *)
t4c_run.
psrr_branch_tok RUN BR HS SHOK PZspan.
{ (* Path 3: f[32] = f[33] = 0x12, f[34] f[35] <> 01 01: 0x87ac0, kind 5, to cut J. *)
clear Hc. t4c_run. t4c_join HA Hbc Hrec Hhdr Hkind. }
(* f[32] = f[33] = 0x12 and f[34] = f[35] = 1 is the head-amp record (cp_amp), which pz_P4c excludes. *)
exfalso.
rewrite branch_ne_U, (t4c_U2 E 74 75 (cp_v fr 34) (cp_v fr 35) A74 A75 R34 R35), (U_lit E 257) in Hc by lia.
apply negb_false_iff, Z.eqb_eq in Hc.
assert (C34 : cp_v fr 34 = 1) by lia. assert (C35 : cp_v fr 35 = 1) by lia.
unfold cp_amp in Qamp. rewrite C32, C33, C34, C35 in Qamp. vm_compute in Qamp. discriminate Qamp.
Qed.
End d.
End b.
