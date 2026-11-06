(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: relocated to libreac/fuzz_disco (the walk of the same function of libreac's fuzz_grant, the two being the same code at other addresses; the segment is restated over fuzz_disco's cut specifications of lib/A/Prog/CtrlParseCut.v). *)
(* reac_ctrl_parse, the walk from cut B (AF_CUTB = AF_reac_ctrl_parse + 0x1c8, image 0x87570) to cut J
   (AF_JOIN = AF_reac_ctrl_parse + 0x3a8, image 0x87750) for the frames of class 3 (pz_P3):
   frame type cd ea, link 1: the call of kind_of_link1 on the opcode frame[22]. *)
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
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import PaRun PaShadow PaJournal DiscoSyms DiscoList DiscoAddr DiscoPa DiscoPaLib.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import DiscoBase YC81 YC4b YC1g YC1h YC45 YC85 DiscoFrame YC88.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import RcKind RcParse.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import CtrlParse CtrlParseLib KindOfLink1 DiscoRo ACj1 DiscoACja.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import CtrlParseCut.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YL05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
#[local] Ltac Zify.zify_pre_hook ::= try unfold YImgTop.IMG_TOP, YImgTop.IMG_LO in *.
(* The write obligation of a run from cut B: the out struct, the realigned stack and the stack region are
   writable, every other region is read-only. *)
Ltac t3_awr :=
lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?lyx ?own' => let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk spx fp b0 bc lyx own') end;
repeat first [ apply awr_ok_nil | apply awr_ok_cons_ro; [apply Z.leb_le; vm_compute; reflexivity|] | pz_awr_hd ].
(* A branch the frame bytes decide: its condition is a closed term once the atoms are replaced. *)
Ltac t3_ref Hc :=
exfalso; revert Hc; cbn [sv_denot];
repeat match goal with H : ew ?Ex ?n = Z_to_bv 64 (Zpos _) |- context [ew ?Ex ?n] => rewrite H end;
first [ vm_compute; let HH := fresh in intros HH; discriminate HH | match goal with |- ?g => idtac "REFFAIL" g end; fail ].
(* Rebase after a run: the run's fresh atoms are set above every atom the walk names. *)
Ltac t3_rebase HS AGX :=
lazymatch type of AGX with forall n, (n < 512)%nat -> ew ?Eo n = ew ?E0 n =>
lazymatch type of HS with
| st_ok_pi _ _ Eo _ _ => idtac
| st_ok_pi _ _ ?Enew _ _ =>
let Ev := fresh "E" in let HEv := fresh "HEv" in
remember Enew as Ev eqn:HEv in *;
let AGX2 := fresh "AGX" in
assert (AGX2 : forall n, (n < 512)%nat -> ew Ev n = ew E0 n)
by (let nn := fresh "nn" in let Hnn := fresh "Hnn" in intros nn Hnn; rewrite HEv; rewrite ?ew_ewset_other, ?ew_havoc_old by lia; apply AGX; exact Hnn);
clear AGX; rename AGX2 into AGX;
repeat match goal with H : ew Eo ?n = ?v |- _ =>
let H2 := fresh in assert (H2 : ew Ev n = v) by (rewrite HEv; rewrite ?ew_ewset_other, ?ew_havoc_old by (cbv; lia); exact H); clear H; rename H2 into H end;
repeat match goal with H : img_env _ _ Eo |- _ => clear H end;
clear HEv
end end.
(* Carry pz_kept across a run whose windows are the realigned stack, the stack region and the out struct. *)
Ltac t3_keep AGX Usp B12 B33 HAR HARc Hfrs2 Eab EF EFL FFL Hoimg KP B LAWS lyc Sc S2 W memc mdc sp sp1 o fpos F FL :=
lazymatch goal with HFr : frame_of ?Ef ?rsf (mrestrict _ ?mA) (mrestrict _ ?mB), HG : mem_grows _ _ |- _ =>
let Hw1 := fresh "Hw1" in let KP' := fresh "KP" in
assert (Hw1 : forall b wlo whi a, In (b, wlo, whi) (windows rsf) -> base_val Ef b + wlo <= a < base_val Ef b + whi ->
  (fun a => (sp1 <= a < sp) \/ (o <= a < o + 36)) a)
  by (pz_win_tac ltac:(fun H => rewrite ?(AGX 2%nat), ?(AGX 12%nat), ?(AGX 33%nat) in H by lia; rewrite ?Usp, ?B12, ?B33 in H));
pose proof (pz_kept_own B LAWS lyc Sc S2 W memc mdc _ _ mA mB (sp - REAC_CTRL_PARSE_STK) sp o fpos F FL
  (fun a => (sp1 <= a < sp) \/ (o <= a < o + 36)) HAR HARc Hfrs2 Eab EF EFL FFL ltac:(assumption) ltac:(assumption) Hoimg
  ltac:(intros a Ha; cbv beta in Ha; destruct Ha; [left | right; left]; lia) KP (kept_of_frame _ _ _ _ _ _ HFr Hw1)
  (fun a Ha => apresent_grows _ _ _ a HG Ha)) as KP';
clear KP Hw1 HFr HG; rename KP' into KP;
repeat match goal with H : frame_of _ _ _ _ |- _ => clear H end end.
(* Make the window [0, hi) of the region based at atom n writable (Hp: its bytes are writable). *)
Ltac t3_rw HS n hi Hp :=
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs n in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rs got_regionP) in
let HS3 := fresh "HS3" in
pose proof (ast_ok_pi_set_region Ex ssx msx i r (set_window r 0 hi) HS ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity)
  (region_ok_rewindow _ Ex _ r 0 hi (st_ok_pi_region_nth Ex ssx msx i r HS ltac:(vm_compute; reflexivity)) Hp)) as HS3;
clear HS; rename HS3 into HS; pz_norm HS end.
Section b. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Context {PI : PAImg disco_listing}.
Context {RO : ro_below_ofl (@pa_segs _ disco_listing PI) (@pa_relro_lo _ disco_listing PI) (@pa_relro_hi _ disco_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation VAL := (@pa_val _ disco_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
(* The callee's call chain: the frame record (sp, ra, s0) of reac_ctrl_parse is pushed when it lies below
   the stack top, else the chain is empty (achain's first case). *)
Lemma t3_chain : forall ly (rd rd' : reader) sp v ra ch sp',
achain ly rd sp v ch -> ly_top ly <= 2 ^ 64 ->
(forall a, sp <= a < 2 ^ 64 -> rd' a = rd a) ->
rdword rd' (sp + -8) = Some ra -> rdword rd' (sp + -16) = Some v -> 4096 <= ra ->
alloc_ceiling <= sp -> sp mod 8 = 0 -> sp' + 16 <= sp ->
achain ly rd' sp' sp (if sp + 16 <? ly_top ly then (sp, ra, v) :: ch else []).
Proof.
intros ly rd rd' sp v ra ch sp' Hch Htop64 Hk H8 H16 Hra Hceil Hal Hsp'.
destruct (Z.ltb_spec (sp + 16) (ly_top ly)) as [Hlt | Hge].
- apply (achain_push ly rd rd' sp v ra ch sp' Hch Htop64 Hk);
[replace (sp - 8) with (sp + -8) by lia; exact H8 | replace (sp - 16) with (sp + -16) by lia; exact H16
| exact Hra | exact Hceil | exact Hal | lia | exact Hsp'].
- left. split; [right; left; lia | reflexivity].
Qed.
Lemma t3_aview_ext : forall H (m m2 : word -> option byte), (forall x, m2 x = m x) -> forall a, aview SEGS H m2 a = aview SEGS H m a.
Proof. intros H m m2 HM a. unfold aview, YP09.mbyte, mrestrict. rewrite HM. reflexivity. Qed.
Lemma t3_apresent_ext : forall H (m m2 : word -> option byte), (forall x, m2 x = m x) -> forall a, apresent H m a -> apresent H m2 a.
Proof. intros H m m2 HM a (Hh & b & Hb). split; [exact Hh|]. exists b. rewrite HM. exact Hb. Qed.
(* The shadow entries carry to a memory that is byte for byte the same and to a valuation that gives the
   shadow base and the two object atoms the same values: the call of kind_of_link1 writes nothing. *)
Lemma t3_U_eq : forall (Ea Eb : env) n, ew Eb n = ew Ea n -> U Eb (SOff n 0) = U Ea (SOff n 0).
Proof. intros Ea Eb n H. unfold U. cbn [sv_denot]. rewrite H. reflexivity. Qed.
Lemma t3_shent_ext : forall (Ea Eb : env) H (m m2 : word -> option byte) e,
(forall x, m2 x = m x) -> U Eb PZx = U Ea PZx -> U Eb (SOff (she_m e) 0) = U Ea (SOff (she_m e) 0) ->
shent_ok SEGS PZx Ea (mrestrict H m) e -> shent_ok SEGS PZx Eb (mrestrict H m2) e.
Proof.
intros Ea Eb H m m2 e HM HB He (HRA & HAP).
assert (Hrd : forall x, rd_of SEGS (mrestrict H m2) x = rd_of SEGS (mrestrict H m) x)
by (intros x; unfold rd_of, YP09.mbyte, mrestrict; rewrite HM; reflexivity).
unfold shent_ok, app_apart in *. rewrite HB, He. split; [|exact HAP].
intros x Hx. destruct (HRA x Hx) as (s & Hs & Hok). exists s. split; [rewrite Hrd; exact Hs | exact Hok].
Qed.
Lemma t3_shok_ext : forall (Ea Eb : env) H (m m2 : word -> option byte),
(forall x, m2 x = m x) -> U Eb PZx = U Ea PZx ->
(forall e, In e PZ_SH -> U Eb (SOff (she_m e) 0) = U Ea (SOff (she_m e) 0)) ->
sh_ok SEGS PZx PZ_SH Ea (mrestrict H m) -> sh_ok SEGS PZx PZ_SH Eb (mrestrict H m2).
Proof.
intros Ea Eb H m m2 HM HB He HS. unfold sh_ok in *. apply Forall_forall. intros e Hin.
apply (t3_shent_ext Ea Eb H m m2 e HM HB (He e Hin)).
revert e Hin. apply Forall_forall. exact HS.
Qed.
(* A saved register of the stack region, read back as a word. *)
Lemma t3_slot : forall E H m n b cs lo hi wlo whi od a v,
region_ok SEGS E (mrestrict H m) (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
bv_unsigned (ew E n) = b -> In (YP09.mkChunk od (CVal 8 (SOff a 0))) cs -> ew E a = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
rdword (aview SEGS H m) (b + od) = Some v.
Proof.
intros E H m n b cs lo hi wlo whi od a v HR Hb Hin Ha Hv.
apply (rdword_of_val_mem SEGS H m (b + od) v); [|exact Hv].
exact (field_of_region E (mrestrict H m) n b cs lo hi wlo whi od 8%N (SOff a 0) v HR Hb Hin
ltac:(cbn [sv_denot]; rewrite Ha, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); exact Hv) ltac:(cbn; lia)).
Qed.
(* The out struct at the join on the class-3 path: the kind (atom 764, kind_of_link1's result), the opcode f22,
   blk_len f21 f20, segment f19, link f18, the counter f14 f15, is_broadcast (seqz of atom 640), the two copies of
   the address bytes (cut B) and zeros. *)
Definition t3_out : list YP09.chunk :=
[YP09.mkChunk 0 (CVal 4 (SOff 764 0)); YP09.mkChunk 26 (CVal 1 (SOff 62 0));
 YP09.mkChunk 24 (CVal 2 (SAlu ALU_OR (SAlu ALU_SLL (SOff 60 0) (SLit 8)) (SOff 61 0)));
 YP09.mkChunk 23 (CVal 1 (SOff 59 0)); YP09.mkChunk 22 (CVal 1 (SOff 58 0));
 YP09.mkChunk 20 (CVal 2 (SAlu ALU_OR (SAlu ALU_SLL (SOff 55 0) (SLit 8)) (SOff 54 0)));
 YP09.mkChunk 16 (CVal 4 (SAlu ALU_SLTU (SOff 640 0) (SLit 1)));
 YP09.mkChunk 4 (CVal 1 (SOff 46 0)); YP09.mkChunk 5 (CVal 1 (SOff 47 0)); YP09.mkChunk 6 (CVal 1 (SOff 48 0));
 YP09.mkChunk 7 (CVal 1 (SOff 49 0)); YP09.mkChunk 8 (CVal 1 (SOff 50 0)); YP09.mkChunk 9 (CVal 1 (SOff 51 0));
 YP09.mkChunk 10 (CVal 1 (SOff 40 0)); YP09.mkChunk 11 (CVal 1 (SOff 41 0)); YP09.mkChunk 12 (CVal 1 (SOff 42 0));
 YP09.mkChunk 13 (CVal 1 (SOff 43 0)); YP09.mkChunk 14 (CVal 1 (SOff 44 0)); YP09.mkChunk 15 (CVal 1 (SOff 45 0));
 YP09.mkChunk 27 (CZero 9)].
(* The model's 36 bytes for a frame of class 3 (cp_struct fr (KL1 f22): no record part, no head-amp part). *)
Definition t3_bytes (fr : list byte) : list byte :=
[Z_to_bv 8 (KL1 (cp_v fr 22)); cp_z; cp_z; cp_z; cp_b fr 6; cp_b fr 7; cp_b fr 8; cp_b fr 9; cp_b fr 10; cp_b fr 11;
 cp_b fr 0; cp_b fr 1; cp_b fr 2; cp_b fr 3; cp_b fr 4; cp_b fr 5; (if cp_bcast fr then Z_to_bv 8 1 else cp_z); cp_z; cp_z; cp_z;
 cp_b fr 14; cp_b fr 15; cp_b fr 18; cp_b fr 19; cp_b fr 21; cp_b fr 20; cp_b fr 22; cp_z;
 cp_z; cp_z; cp_z; cp_z; cp_z; cp_z; cp_z; cp_z].
(* Pau's model on class 3: kind KL1 f22 (ctrlparse_link1, lib/Prog/RcParse.v:175; KL1_range :58 excludes 6). *)
Lemma t3_model : forall n fr, cp_hdr n fr = true -> pz_P3 fr -> ctrlparse n fr = (KL1 (cp_v fr 22), t3_bytes fr).
Proof.
intros n fr Hh (HT & HL).
assert (Hk : cp_kind fr = KL1 (cp_v fr 22)).
{ pose proof HT as HT'. unfold cp_type in HT'. apply andb_prop in HT' as [A B]. apply Z.eqb_eq in A, B.
unfold cp_kind, cp_type. rewrite A, B, HL. reflexivity. }
assert (Hr : cp_rec fr = false) by (unfold cp_rec; rewrite HT, HL; reflexivity).
assert (H6 : (KL1 (cp_v fr 22) =? 6) = false) by (apply Z.eqb_neq; pose proof (KL1_range (cp_v fr 22)); lia).
unfold ctrlparse. rewrite Hh, Hk. unfold cp_struct. rewrite Hr, H6. reflexivity.
Qed.
Lemma t3_KL1_cases : forall x, KL1 x = 2 \/ KL1 x = 3 \/ KL1 x = 10 \/ KL1 x = 9 \/ KL1 x = 7 \/ KL1 x = 13.
Proof. intros x. unfold KL1. repeat match goal with |- context [if ?c then _ else _] => destruct c end; tauto. Qed.
(* The chunk that covers an offset (the first, as pz_chunk_at reads it): its offset, value and index inside. *)
Fixpoint t3_find (cs : list YP09.chunk) (off : Z) : option (Z * cval * Z) :=
match cs with
| [] => None
| c :: t => if (YP09.c_off c <=? off) && (off <? YP09.c_off c + YP09.c_len c)
  then Some (YP09.c_off c, YP09.c_val c, off - YP09.c_off c) else t3_find t off
end.
Lemma t3_find_ok : forall E base cs off, pz_chunk_at E base cs off =
match t3_find cs off with Some (co, cv, j) => YP09.cbyte SEGS E (base + co) cv j | None => None end.
Proof.
intros E base cs off. induction cs as [|c t IH]; cbn [pz_chunk_at t3_find]; [reflexivity|].
destruct (_ && _); [reflexivity | exact IH].
Qed.
Lemma t3_bv8 : forall x (b : byte), x mod 256 = bv_unsigned b -> Z_to_bv 8 x = b.
Proof. intros x b H. apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. exact H. Qed.
Lemma t3_b0 : forall E e, byte_of_word (sv_denot E e) 0 = Z_to_bv 8 (U E e).
Proof. intros E e. unfold byte_of_word, U. rewrite Z.mul_0_r, Z.shiftr_0_r. reflexivity. Qed.
Lemma t3_bj : forall E e j, 0 <= U E e < 256 -> 1 <= j -> byte_of_word (sv_denot E e) j = cp_z.
Proof.
intros E e j HU Hj. unfold byte_of_word. change (bv_unsigned (sv_denot E e)) with (U E e).
rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_small; [reflexivity|].
assert (H8 : 2 ^ 8 <= 2 ^ (8 * j)) by (apply Z.pow_le_mono_r; lia). change (2 ^ 8) with 256 in H8. lia.
Qed.
Lemma t3_b_atom : forall E n fr i, ew E n = Z_to_bv 64 (cp_v fr i) -> byte_of_word (sv_denot E (SOff n 0)) 0 = cp_b fr i.
Proof.
intros E n fr i H. pose proof (cp_v_range fr i). rewrite t3_b0, (U_atom E n (cp_v fr i) H) by lia.
unfold cp_v. apply Z_to_bv_bv_unsigned.
Qed.
Lemma t3_b_k0 : forall E n k, ew E n = Z_to_bv 64 k -> 0 <= k < 256 -> byte_of_word (sv_denot E (SOff n 0)) 0 = Z_to_bv 8 k.
Proof. intros E n k H Hk. rewrite t3_b0, (U_atom E n k H) by lia. reflexivity. Qed.
Lemma t3_b_kj : forall E n k j, ew E n = Z_to_bv 64 k -> 0 <= k < 256 -> 1 <= j -> byte_of_word (sv_denot E (SOff n 0)) j = cp_z.
Proof. intros E n k j H Hk Hj. apply t3_bj; [rewrite (U_atom E n k H) by lia; lia | lia]. Qed.
Lemma t3_lor : forall a b, 0 <= a -> 0 <= b < 256 -> Z.lor (a * 256) b = a * 256 + b.
Proof.
intros a b Ha Hb.
assert (HL : Z.land (a * 256) b = 0).
{ apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
  destruct (Z.lt_ge_cases i 8) as [Hi8|Hi8].
  - change 256 with (2 ^ 8). rewrite Z.mul_pow2_bits_low by lia. reflexivity.
  - rewrite <- (Z.mod_small b (2 ^ 8)) by (cbn; lia). rewrite Z.mod_pow2_bits_high by lia. apply andb_false_r. }
rewrite <- (Z.lxor_lor _ _ HL). symmetry. apply Z.add_nocarry_lxor. exact HL.
Qed.
Lemma t3_U_pack : forall E nh nl fr ih il, ew E nh = Z_to_bv 64 (cp_v fr ih) -> ew E nl = Z_to_bv 64 (cp_v fr il) ->
U E (SAlu ALU_OR (SAlu ALU_SLL (SOff nh 0) (SLit 8)) (SOff nl 0)) = cp_v fr ih * 256 + cp_v fr il.
Proof.
intros E nh nl fr ih il Hh Hl. pose proof (cp_v_range fr ih). pose proof (cp_v_range fr il).
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw].
rewrite (U_atom E nh _ Hh), (U_atom E nl _ Hl), U_SLit by lia.
change (Z.land (zcanon 8) 63) with 8. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 8) with 256.
rewrite (zcanon_id (cp_v fr ih * 256)) by (unfold M64; lia).
rewrite t3_lor by lia. apply zcanon_id. unfold M64. lia.
Qed.
Lemma t3_b_lo : forall E nh nl fr ih il, ew E nh = Z_to_bv 64 (cp_v fr ih) -> ew E nl = Z_to_bv 64 (cp_v fr il) ->
byte_of_word (sv_denot E (SAlu ALU_OR (SAlu ALU_SLL (SOff nh 0) (SLit 8)) (SOff nl 0))) 0 = cp_b fr il.
Proof.
intros E nh nl fr ih il Hh Hl. pose proof (cp_v_range fr ih). pose proof (cp_v_range fr il).
rewrite t3_b0, (t3_U_pack E nh nl fr ih il Hh Hl). apply t3_bv8.
rewrite Z.add_comm, Z_mod_plus_full. unfold cp_v in *. apply Z.mod_small. lia.
Qed.
Lemma t3_b_hi : forall E nh nl fr ih il, ew E nh = Z_to_bv 64 (cp_v fr ih) -> ew E nl = Z_to_bv 64 (cp_v fr il) ->
byte_of_word (sv_denot E (SAlu ALU_OR (SAlu ALU_SLL (SOff nh 0) (SLit 8)) (SOff nl 0))) 1 = cp_b fr ih.
Proof.
intros E nh nl fr ih il Hh Hl. pose proof (cp_v_range fr ih). pose proof (cp_v_range fr il).
unfold byte_of_word. change (bv_unsigned (sv_denot E ?e)) with (U E e).
rewrite (t3_U_pack E nh nl fr ih il Hh Hl). rewrite Z.shiftr_div_pow2 by lia. change (2 ^ (8 * 1)) with 256.
rewrite Z.div_add_l by lia. rewrite (Z.div_small (cp_v fr il) 256) by lia. rewrite Z.add_0_r. apply t3_bv8.
unfold cp_v in *. apply Z.mod_small. lia.
Qed.
Lemma t3_U_sltu : forall E fr, (ew E 640 = Z_to_bv 64 0 <-> cp_bcast fr = true) ->
U E (SAlu ALU_SLTU (SOff 640 0) (SLit 1)) = if cp_bcast fr then 1 else 0.
Proof.
intros E fr Hbc. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit. change (zcanon 1) with 1.
unfold U at 1. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
destruct (cp_bcast fr) eqn:Hb.
- rewrite (proj2 Hbc eq_refl). reflexivity.
- assert (Hn : bv_unsigned (ew E 640) <> 0).
  { intros Hz. assert (Hw : ew E 640 = Z_to_bv 64 0) by (apply bv_eq; rewrite Hz; reflexivity).
    apply Hbc in Hw. congruence. }
  pose proof (bv_unsigned_in_range 64 (ew E 640)) as R.
  replace (bv_unsigned (ew E 640) <? 1) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.
Lemma t3_b_s0 : forall E fr, (ew E 640 = Z_to_bv 64 0 <-> cp_bcast fr = true) ->
byte_of_word (sv_denot E (SAlu ALU_SLTU (SOff 640 0) (SLit 1))) 0 = if cp_bcast fr then Z_to_bv 8 1 else cp_z.
Proof. intros E fr Hbc. rewrite t3_b0, (t3_U_sltu E fr Hbc). destruct (cp_bcast fr); reflexivity. Qed.
Lemma t3_b_sj : forall E fr j, (ew E 640 = Z_to_bv 64 0 <-> cp_bcast fr = true) -> 1 <= j ->
byte_of_word (sv_denot E (SAlu ALU_SLTU (SOff 640 0) (SLit 1))) j = cp_z.
Proof. intros E fr j Hbc Hj. apply t3_bj; [rewrite (t3_U_sltu E fr Hbc); destruct (cp_bcast fr); lia | lia]. Qed.
Ltac t3_bclose HA Hbc HK :=
lazymatch goal with
| |- Some (Z_to_bv 8 0) = Some cp_z => reflexivity
| |- Some (byte_of_word (sv_denot ?E (SOff 764 0)) 0) = Some _ =>
  f_equal; apply (t3_b_k0 E 764 _ HK); lazymatch goal with |- context [KL1 ?x] => pose proof (KL1_range x) end; lia
| |- Some (byte_of_word (sv_denot ?E (SOff 764 0)) _) = Some _ =>
  f_equal; apply (t3_b_kj E 764 _ _ HK); [lazymatch goal with |- context [KL1 ?x] => pose proof (KL1_range x) end; lia | lia]
| |- Some (byte_of_word (sv_denot ?E (SAlu ALU_SLTU _ _)) 0) = Some _ => f_equal; exact (t3_b_s0 E _ Hbc)
| |- Some (byte_of_word (sv_denot ?E (SAlu ALU_SLTU _ _)) _) = Some _ => f_equal; apply (t3_b_sj E _ _ Hbc); lia
| |- Some (byte_of_word (sv_denot ?E (SOff ?n 0)) 0) = Some (cp_b ?fr ?i) =>
  f_equal; exact (t3_b_atom E n fr i (HA i ltac:(lia)))
| |- Some (byte_of_word (sv_denot ?E (SAlu ALU_OR (SAlu ALU_SLL (SOff ?nh 0) (SLit 8)) (SOff ?nl 0))) 0) = Some (cp_b ?fr ?il) =>
  let ih := eval vm_compute in (nh - 40)%nat in f_equal; exact (t3_b_lo E nh nl fr ih il (HA ih ltac:(lia)) (HA il ltac:(lia)))
| |- Some (byte_of_word (sv_denot ?E (SAlu ALU_OR (SAlu ALU_SLL (SOff ?nh 0) (SLit 8)) (SOff ?nl 0))) 1) = Some (cp_b ?fr ?ih) =>
  let il := eval vm_compute in (nl - 40)%nat in f_equal; exact (t3_b_hi E nh nl fr ih il (HA ih ltac:(lia)) (HA il ltac:(lia)))
| |- ?g => idtac "T3-BYTE" g; fail
end.
(* The 36 bytes of the out struct at the join are the model's (t3_bytes fr). *)
Lemma t3_out_bytes : forall E H mem o fr,
region_ok SEGS E (mrestrict H mem) (YP09.mkRegion (Some 12%nat) 0 36 0 36 t3_out) ->
base_val E (Some 12%nat) = o ->
(forall i, (i < 23)%nat -> ew E (40 + i) = Z_to_bv 64 (cp_v fr i)) ->
(ew E 640 = Z_to_bv 64 0 <-> cp_bcast fr = true) ->
ew E 764 = Z_to_bv 64 (KL1 (cp_v fr 22)) ->
forall i, (i < 36)%nat -> aview SEGS H mem (o + Z.of_nat i) = Some (bv_unsigned (nth i (t3_bytes fr) cp_z)).
Proof.
intros E H mem o fr Hr Hb HA Hbc HK i Hi. subst o.
apply (pz_region_byte E H mem _ (Z.of_nat i) _ Hr).
cbn [YP09.r_base YP09.r_chunks]. rewrite t3_find_ok. unfold t3_bytes.
do 36 (destruct i as [|i]; [
  lazymatch goal with |- context [t3_find ?cs ?off] => let v := eval vm_compute in (t3_find cs off) in change (t3_find cs off) with v end;
  cbn [YP09.cbyte nth]; t3_bclose HA Hbc HK | ]).
lia.
Qed.
(* The call of kind_of_link1: cl_callS (YC85) for a callee whose post is FP-existential (apost_base's form:
   an fx' with every f-register but f10 kept and the fcsr kept or with its flags cleared); the caller runs on
   in that fx'. a Theorem Labs lane's ho_cl_callF (lib/A/Prog/ReacHuntObserveSC.v) with B and LAWS as arguments. *)
Lemma t3_callF : forall B, AR_laws SEGS B ->
forall (fx : YK11.FPState) W (regsc : bvmap 5 word) memc pc STK sp0 FP ly S W0 mem md own lyc Sc mdc k
STK1 FP1 EV1 (o : Z) raw ch1
(K : alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k ->
spZ regsc = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 0 <= STK1 -> STK1 - o <= STK ->
getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
getr regsc 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
achain lyc (aview SEGS (w_H W) memc) (sp0 + o) (s0Z regsc) ch1 ->
(afn_pre SEGS B STK1 lyc Sc W regsc memc mdc ch1 ->
 SRr SEGS W (mkCfg (@mkst fx regsc pc memc (seg_rom SEGS)) mdc)
   (fun W2 c2 => exists (fx' : YK11.FPState) ly2 S2 regs2 mem2 md2,
      c2 = mkCfg (@mkst fx' regs2 raw mem2 (seg_rom SEGS)) md2 /\
      (forall k : bv 5, bv_unsigned k <> 10 -> Sem.reg_get (@YK11.fp_regs fx') k = Sem.reg_get (@YK11.fp_regs fx) k) /\
      (@YK11.fp_csr fx' = @YK11.fp_csr fx \/ Z.land (Z.shiftr (bv_unsigned (@YK11.fp_csr fx')) 5) 7 = 0) /\
      ajournal SEGS B STK1 (spZ regsc) FP1 lyc Sc W memc mdc [] ly2 S2 W2 mem2 md2 EV1 /\
      aregs_preserved regsc regs2 /\ K ly2 S2 W2 regs2 mem2 md2)) ->
(forall a, inFP FP1 a -> inFP FP a \/ in_tmp_block (ablocks B ly S) (ablocks B lyc Sc) a) ->
SRr SEGS W (mkCfg (@mkst fx regsc pc memc (seg_rom SEGS)) mdc)
  (fun W2 c2 => exists (fx' : YK11.FPState) ly2 S2 regs2 mem2 md2,
     c2 = mkCfg (@mkst fx' regs2 raw mem2 (seg_rom SEGS)) md2 /\
     (forall k : bv 5, bv_unsigned k <> 10 -> Sem.reg_get (@YK11.fp_regs fx') k = Sem.reg_get (@YK11.fp_regs fx) k) /\
     (@YK11.fp_csr fx' = @YK11.fp_csr fx \/ Z.land (Z.shiftr (bv_unsigned (@YK11.fp_csr fx')) 5) 7 = 0) /\
     ajournal SEGS B STK sp0 FP ly S W0 mem md own ly2 S2 W2 mem2 md2 (k + EV1) /\
     ajournal SEGS B STK1 (sp0 + o) FP1 lyc Sc W memc mdc [] ly2 S2 W2 mem2 md2 EV1 /\
     aregs_preserved regsc regs2 /\ K ly2 S2 W2 regs2 mem2 md2).
Proof.
intros B LAWS fx W regsc memc pc STK sp0 FP ly S W0 mem md own lyc Sc mdc k STK1 FP1 EV1 o raw ch1 K
  HJ Hsp' Hal Hneg Hstk1 Hbud Hgp Htp Hra Hraw Hra4 Hch Hcallee HF.
eapply SRr_mono.
{ apply Hcallee. eapply (afn_pre_at SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k regsc STK1 o ch1);
  try eassumption. - rewrite Hra. exact Hraw. - unfold raZ. rewrite Hra. exact Hra4. - rewrite Hsp'. exact Hch. }
cbv beta. intros W2 c2 _ (fx' & ly2 & S2 & regs2 & mem2 & md2 & -> & Hfr & Hcs & HJ1 & HP & HK).
exists fx', ly2, S2, regs2, mem2, md2. split; [reflexivity|]. split; [exact Hfr|]. split; [exact Hcs|].
rewrite Hsp' in HJ1.
split; [| split; [exact HJ1 | split; [exact HP | exact HK]]].
change own with ([] ++ own). eapply (ajournal_sub_tok SEGS B LAWS pa_segs_low); [exact HJ | exact HJ1 | lia | lia | exact HF].
Qed.
(* The symbolic state does not name the floating-point state: it holds of the machine state in any fx. *)
Lemma t3_xfx : forall (fx1 fx2 : YK11.FPState) E ss (H : word -> bool) regs pc mem,
st_ok_pi (fx := fx1) SEGS VAL E ss (restrict H (@mkst fx1 regs pc mem (seg_rom SEGS))) ->
st_ok_pi (fx := fx2) SEGS VAL E ss (restrict H (@mkst fx2 regs pc mem (seg_rom SEGS))).
Proof.
intros fx1 fx2 E ss H regs pc mem HS. unfold st_ok_pi in *. rewrite restrict_mkst_fx in *.
exact (YL05.st_ok_xfx fx1 fx2 SEGS E _ _ _ _ HS).
Qed.
(* The post in the callee's state fx is the post in the entry state fq when fx keeps fq's f-registers other
   than f10 and fx's fcsr is fq's or has its flags cleared: each of the two relations is transitive
   (a Theorem Labs lane's ho_SRr_setfq, stated on treac_ctrl_parse_post). *)
Lemma t3_post_fx : forall B (fq fx : YK11.FPState) STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs o n fr
(Wx : world SEGS) cf,
(forall kk : bv 5, bv_unsigned kk <> 10 -> Sem.reg_get (@YK11.fp_regs fx) kk = Sem.reg_get (@YK11.fp_regs fq) kk) ->
(@YK11.fp_csr fx = @YK11.fp_csr fq \/ Z.land (Z.shiftr (bv_unsigned (@YK11.fp_csr fx)) 5) 7 = 0) ->
SRr SEGS Wx cf (treac_ctrl_parse_post B fx STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs o n fr) ->
SRr SEGS Wx cf (treac_ctrl_parse_post B fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs o n fr).
Proof.
intros B fq fx STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs o n fr Wx cf Hfr Hcs HR.
eapply SRr_mono; [exact HR|].
intros W5 c5 _ HP. unfold treac_ctrl_parse_post in HP |- *.
destruct HP as (fx' & ly5 & S5 & regs5 & mem5 & md5 & Hc5 & Hfr5 & Hcs5 & HR5).
exists fx', ly5, S5, regs5, mem5, md5. split; [exact Hc5|]. split.
- intros kk Hk. rewrite (Hfr5 kk Hk). exact (Hfr kk Hk).
- split; [|exact HR5]. destruct Hcs5 as [Hcs5|Hcs5]; [rewrite Hcs5; exact Hcs | right; exact Hcs5].
Qed.
(* The walk's cut J specification is taken for every context: after the call the walk reaches cut J in the
   callee's floating-point state, the context c with fx' in place of fq (pz_ok does not name fq). *)
Lemma pz_tail3 : forall B G, pz_rt B G -> forall c, pz_ok B c -> (forall c', pz_ok B c' -> pz_cutJ_spec B c') ->
pz_cutB_case B c pz_P3.
Proof.
intros B G RT c Hok HJall Hbig E ms md Hcur HS SHOK Hhdr H640 HP3.
assert (HJc : forall fx, pz_cutJ_spec B (mkPZ fx (cx_STK c) (cx_sp0 c) (cx_FP c) (cx_ly c) (cx_S c) (cx_W0 c)
  (cx_mem0 c) (cx_md0 c) (cx_own c) (cx_lyc c) (cx_Sc c) (cx_W c) (cx_memc c) (cx_mdc c) (cx_k c) (cx_regs c)
  (cx_ch c) (cx_f c) (cx_n c) (cx_o c) (cx_fr c) (cx_S2 c) (cx_fpos c)))
  by (intros fx; apply HJall; exact Hok).
clear HJall.
pz_open c Hok. pz_open_rt RT. pz_open_cur Hcur. pz_open_f Hbig. pz_std.
pose (RUN := paj_run (fx := fq) B LAWS). pose (RUNTO := paj_run_to (fx := fq) B LAWS).
pose (BR := paj_branch (fx := fq) (PI := PI)).
pose proof HP3 as HP3'. destruct HP3 as (HT3 & HL1).
assert (A640 : ew E 640 = Z_to_bv 64 (bv_unsigned (ew E 640))) by (symmetry; apply Z_to_bv_bv_unsigned).
unfold cp_type in HT3. apply andb_prop in HT3 as [F16 F17]. apply Z.eqb_eq in F16, F17.
assert (A56 : ew E 56 = Z_to_bv 64 205) by (rewrite (AGX 56%nat) by lia; change 56%nat with (40 + 16)%nat; rewrite (EFB 16%nat) by lia; rewrite F16; reflexivity).
assert (A57 : ew E 57 = Z_to_bv 64 234) by (rewrite (AGX 57%nat) by lia; change 57%nat with (40 + 17)%nat; rewrite (EFB 17%nat) by lia; rewrite F17; reflexivity).
assert (A58 : ew E 58 = Z_to_bv 64 1) by (rewrite (AGX 58%nat) by lia; change 58%nat with (40 + 18)%nat; rewrite (EFB 18%nat) by lia; rewrite HL1; reflexivity).
assert (A62 : ew E 62 = Z_to_bv 64 (cp_v fr 22)) by (rewrite (AGX 62%nat) by lia; change 62%nat with (40 + 22)%nat; apply EFB; lia).
repeat match goal with H : _ \/ _ |- _ => box H | H : off_img _ _ |- _ => box H | H : in_app _ _ |- _ => box H end.
assert (HKlo : alloc_ceiling <= sp - REAC_CTRL_PARSE_STK) by lia. assert (HKhi : sp <= 2 ^ 64) by lia.
(* run 1 *)
paj_run_tok RUN HS HJ2 SHOK PZspan; [t3_awr|].
t3_keep AGX Usp B12 B33 HAR HARc Hfrs2 Eab EF EFL FFL Hoimg KP B LAWS lyc Sc S2 W memc mdc sp sp1 o fpos F FL. t3_rebase HS AGX.
psrr_branch_tok RUN BR HS SHOK PZspan; [clear Hc | t3_ref Hc].
(* run 2 *)
paj_run_tok RUN HS HJ2 SHOK PZspan; [t3_awr|].
t3_keep AGX Usp B12 B33 HAR HARc Hfrs2 Eab EF EFL FFL Hoimg KP B LAWS lyc Sc S2 W memc mdc sp sp1 o fpos F FL. t3_rebase HS AGX.
psrr_branch_tok RUN BR HS SHOK PZspan; [clear Hc | t3_ref Hc].
(* run 3 *)
paj_run_tok RUN HS HJ2 SHOK PZspan; [t3_awr|].
t3_keep AGX Usp B12 B33 HAR HARc Hfrs2 Eab EF EFL FFL Hoimg KP B LAWS lyc Sc S2 W memc mdc sp sp1 o fpos F FL. t3_rebase HS AGX.
psrr_branch_tok RUN BR HS SHOK PZspan; [clear Hc | t3_ref Hc].
(* run 4 *)
paj_run_tok RUN HS HJ2 SHOK PZspan; [t3_awr|].
t3_keep AGX Usp B12 B33 HAR HARc Hfrs2 Eab EF EFL FFL Hoimg KP B LAWS lyc Sc S2 W memc mdc sp sp1 o fpos F FL. t3_rebase HS AGX.
psrr_branch_tok RUN BR HS SHOK PZspan; [t3_ref Hc | clear Hc].
(* run 5 *)
paj_run_tok RUN HS HJ2 SHOK PZspan; [t3_awr|].
t3_keep AGX Usp B12 B33 HAR HARc Hfrs2 Eab EF EFL FFL Hoimg KP B LAWS lyc Sc S2 W memc mdc sp sp1 o fpos F FL. t3_rebase HS AGX.
psrr_branch_tok RUN BR HS SHOK PZspan; [t3_ref Hc | clear Hc].
(* run 6 *)
paj_run_tok RUN HS HJ2 SHOK PZspan; [t3_awr|].
t3_keep AGX Usp B12 B33 HAR HARc Hfrs2 Eab EF EFL FFL Hoimg KP B LAWS lyc Sc S2 W memc mdc sp sp1 o fpos F FL. t3_rebase HS AGX.
psrr_branch_tok RUN BR HS SHOK PZspan; [t3_ref Hc | clear Hc].
(* run 7 *)
paj_run_tok RUN HS HJ2 SHOK PZspan; [t3_awr|].
t3_keep AGX Usp B12 B33 HAR HARc Hfrs2 Eab EF EFL FFL Hoimg KP B LAWS lyc Sc S2 W memc mdc sp sp1 o fpos F FL. t3_rebase HS AGX.
psrr_branch_tok RUN BR HS SHOK PZspan; [t3_ref Hc | clear Hc].
(* run 8 *)
paj_run_tok RUN HS HJ2 SHOK PZspan; [t3_awr|].
t3_keep AGX Usp B12 B33 HAR HARc Hfrs2 Eab EF EFL FFL Hoimg KP B LAWS lyc Sc S2 W memc mdc sp sp1 o fpos F FL. t3_rebase HS AGX.
psrr_branch_tok RUN BR HS SHOK PZspan; [t3_ref Hc | clear Hc].
(* run 9: to the call *)
paj_run_tok RUN HS HJ2 SHOK PZspan; [t3_awr|].
t3_keep AGX Usp B12 B33 HAR HARc Hfrs2 Eab EF EFL FFL Hoimg KP B LAWS lyc Sc S2 W memc mdc sp sp1 o fpos F FL.
(* The call of kind_of_link1 (AF_reac_ctrl_parse + 0x514, image 0x878bc) with a0 = frame[22]. *)
prreg HS (1%bv : bv 5) R1. prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4.
prreg HS (8%bv : bv 5) R8. prreg HS (10%bv : bv 5) R10.
rewrite (AGX 33%nat), E33 in R2 by lia.
rewrite (AGX 3%nat), (EE 3%nat 3%bv eq_refl) in R3 by lia. rewrite (AGX 4%nat), (EE 4%nat 4%bv eq_refl) in R4 by lia.
rewrite (AGX 2%nat), (EE 2%nat 2%bv eq_refl) in R8 by lia. rewrite A62 in R10.
pose proof (proj1 KP) as KP1.
assert (Qtop64 : ly_top lyc <= 2 ^ 64).
{ pose proof (proj1 (proj2 HJ)) as LY. destruct LY as (_ & _ & _ & _ & _ & _ & _ & _ & LT & _). rewrite LT. lia. }
assert (Qra : 0 <= raZ regs < 2 ^ 64) by (unfold raZ; pose proof (bv_unsigned_in_range 64 (getr regs 1)) as Hq; change (bv_modulus 64) with (2 ^ 64) in Hq; exact Hq).
assert (Qs0 : 0 <= s0Z regs < 2 ^ 64) by (unfold s0Z; pose proof (bv_unsigned_in_range 64 (getr regs 8)) as Hq; change (bv_modulus 64) with (2 ^ 64) in Hq; exact Hq).
assert (Qal8 : sp mod 8 = 0) by (pose proof (Z.div_mod sp 16 ltac:(lia)) as D; rewrite Hal16, Z.add_0_r in D; rewrite D; replace (16 * (sp / 16)) with ((2 * (sp / 16)) * 8) by lia; apply Z_mod_mult).
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let ih := idx_of_base rs 2%nat in let ih := eval vm_compute in ih in
let rh := eval vm_compute in (nth ih rs got_regionP) in
pose proof (st_ok_region_nth Ex ssx (restrict (w_H W) msX) ih rh HS ltac:(vm_compute; reflexivity)) as HRstk; cbn [ms_mem restrict] in HRstk;
pose proof (t3_slot Ex (w_H W) (ms_mem msX) 2 sp _ _ _ _ _ (-8) 1 (raZ regs) HRstk
ltac:(rewrite (AGX 2%nat) by lia; exact Usp) ltac:(cbn; tauto)
ltac:(rewrite (AGX 1%nat) by lia; rewrite (EE 1%nat 1%bv eq_refl); unfold raZ; symmetry; apply Z_to_bv_bv_unsigned) Qra) as Vra;
pose proof (t3_slot Ex (w_H W) (ms_mem msX) 2 sp _ _ _ _ _ (-16) 8 (s0Z regs) HRstk
ltac:(rewrite (AGX 2%nat) by lia; exact Usp) ltac:(cbn; tauto)
ltac:(rewrite (AGX 8%nat) by lia; rewrite (EE 8%nat 8%bv eq_refl); unfold s0Z; symmetry; apply Z_to_bv_bv_unsigned) Qs0) as Vs0;
clear HRstk;
assert (Hch1 : achain lyc (aview SEGS (w_H W) (ms_mem msX)) sp1 sp (if sp + 16 <? ly_top lyc then (sp, raZ regs, s0Z regs) :: ch else []))
by (apply (t3_chain lyc (aview SEGS (w_H W) memc) _ sp (s0Z regs) (raZ regs) ch sp1 Hch Qtop64);
[intros a Ha; apply KP1; lia | exact Vra | exact Vs0 | exact Hra4 | lia | exact Qal8 | lia]) end.
pmkst HS. rewrite pa_sigma_kind_of_link1.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (@mkst ?fxT ?rT ?pcT ?mT _) ?dT) _ =>
refine (t3_callF B LAWS fxT W rT mT pcT STK sp0 FP ly S W0 mem0 md0 ((1, fpos) :: own) lyc S2 dT k KIND_OF_LINK1_STK [] 0 (sp1 - sp0) (getr rT 1)
(if sp + 16 <? ly_top lyc then (sp, raZ regs, s0Z regs) :: ch else [])
(fun ly' S' W' regs' mem' md' => getr regs' 10 = w64 (KL1 (cp_v fr 22)) /\ ly' = lyc /\ S' = S2 /\ W' = W /\ (forall x, mem' x = mT x) /\
Permutation (ablocks B ly' S') (ablocks B lyc S2)) HJ2 _ _ _ _ _ _ _ eq_refl _ _ _ _ _) end.
- unfold spZ at 1. rewrite R2, unsigned_lit_small by lia. lia.
- rewrite Zminus_mod, Hsp1al16, Hsp0al. reflexivity.
- lia.
- unfold KIND_OF_LINK1_STK. lia.
- unfold KIND_OF_LINK1_STK. lia.
- rewrite R3. exact Hgp.
- rewrite R4. exact Htp.
- rewrite R1. apply ret_ok_codeptr_v; [lia | reflexivity].
- rewrite R1, unsigned_lit_small by lia. lia.
- replace (sp0 + (sp1 - sp0)) with sp1 by lia. unfold s0Z at 1. rewrite R8. exact Hch1.
- intros HPRE. exact (KIND _ lyc S2 W _ _ _ _ (cp_v fr 22) HPRE R10 ltac:(pose proof (cp_v_range fr 22); lia)).
- intros a Ha. exfalso. exact (inFP_nil a Ha). }
cbv beta. intros W2 c2 _ (fx' & ly2 & S3 & regs2 & mem2 & md2 & -> & Hfr & Hcs & HJ3 & HJk & HP2 & Ha0 & -> & -> & -> & HM & _).
(* kind_of_link1 returns in its own floating-point state fx': the post in fx' gives the post in fq. *)
apply (t3_post_fx B fq fx'); [exact Hfr | exact Hcs |].
jafter_call_keep_hi HS 760%nat regs2 (mrestrict (w_H W) mem2) HP2 [0; 1; 2; 3; 4; 5]%nat HS2.
match type of HS2 with ?Q -> _ => assert (HQ : Q); [| specialize (HS2 HQ); clear HQ] end.
{ cbn [ms_mem restrict]. apply regions_kept_all; [exact (t3_aview_ext _ _ _ HM) | exact (t3_apresent_ext _ _ _ HM)]. }
rewrite <- restrict_mkst_fx in HS2. clear HS.
pose proof (t3_xfx fq fx' _ _ _ _ _ _ HS2) as HS. clear HS2.
rewrite R1.
(* kind_of_link1 writes nothing, so the shadow entries hold at the same bytes and the new atoms are above
   the two the entries name. *)
lazymatch type of HS with st_ok_pi _ _ (havoc ?Eo 760 ?vs) _ _ =>
assert (EK : ew (havoc Eo 760 vs) 764 = Z_to_bv 64 (KL1 (cp_v fr 22)))
by (change 764%nat with (760 + 4)%nat; rewrite (ew_havoc_new _ 760 _ 4 (Z_to_bv 64 0)) by (cbn; lia); cbn [map nth CLOB]; exact Ha0);
pose proof (t3_shok_ext Eo (havoc Eo 760 vs) (w_H W) _ mem2 HM
  ltac:(unfold PZx; apply t3_U_eq; rewrite ew_havoc_old by (cbv; lia); reflexivity)
  ltac:(intros e He; unfold PZ_SH in He; cbn [In] in He; destruct He as [<- | [<- | []]];
        cbn [she_m]; apply t3_U_eq; rewrite ew_havoc_old by (cbv; lia); reflexivity)
  SHOK) as SHOK3 end.
pz_rebase HS AGX.
(* The caller's memory is what it was before the call: pz_kept carries over. *)
pose proof (pz_kept_own B LAWS lyc Sc S2 W memc mdc _ _ _ mem2 (sp - REAC_CTRL_PARSE_STK) sp o fpos F FL (fun _ : Z => False)
HAR HARc Hfrs2 Eab EF EFL FFL ltac:(assumption) ltac:(assumption) Hoimg ltac:(intros a Ha; destruct Ha) KP
(fun a _ _ => t3_aview_ext _ _ _ HM a) (fun a Ha => t3_apresent_ext _ _ _ HM a Ha)) as KP'.
clear KP KP1; rename KP' into KP.
rewrite Z.add_0_r in HJ3.
(* run 10: the kind is stored at out->kind, read back sign-extended, and the walk joins at AF_JOIN *)
clear RUNTO. pose (RUNTO := paj_run_to (fx := fx') B LAWS).
paj_run_to_tok RUNTO HS HJ3 SHOK3 PZspan AF_JOIN; [t3_awr|].
t3_keep AGX Usp B12 B33 HAR HARc Hfrs2 Eab EF EFL FFL Hoimg KP B LAWS lyc Sc S2 W memc mdc sp sp1 o fpos F FL. t3_rebase HS AGX.
(* At the join: the out struct holds the model's bytes; the frame and its shadow become writable;
   ra_join to cut J (atoms 700..723) and the cut J hypothesis. *)
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict (w_H ?Wx) ?msx) =>
assert (HA : forall i, (i < 23)%nat -> ew Ex (40 + i) = Z_to_bv 64 (cp_v fr i)) by (intros i Hi; rewrite AGX by lia; apply EFB; lia);
assert (Hbc : ew Ex 640 = Z_to_bv 64 0 <-> cp_bcast fr = true) by (rewrite A640, Z_to_bv_bv_unsigned; exact H640);
pose proof (st_ok_pi_region_nth Ex ssx _ 0 _ HS eq_refl) as R12;
lazymatch type of R12 with region_ok ?sg _ ?mm _ =>
change (region_ok sg Ex mm (YP09.mkRegion (Some 12%nat) 0 36 0 36 t3_out)) in R12 end;
pose proof (t3_out_bytes Ex (w_H Wx) (ms_mem msx) o fr R12 ltac:(cbn [base_val]; rewrite (AGX 12%nat) by lia; exact B12) HA Hbc EK) as OUT;
prreg HS (10%bv : bv 5) Ra0;
destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos (proj1 HJ3) Hfin2) as (_ & _ & HFp & HFSp);
change (fs_frame_bytes 1) with 128 in HFp, HFSp; change (128 / 8) with 16 in HFSp;
assert (W529 : forall q, 0 <= q < 16 -> writable_at SEGS (mrestrict (w_H Wx) (ms_mem msx)) (base_val Ex (Some 529%nat) + q))
  by (intros q Hq; cbn [base_val]; rewrite E529, unsigned_lit_small by (unfold SB; lia); apply (apresent_writable SEGS);
      unfold shadow_addr in HFSp; rewrite <- SB_SHADOW_OFF in HFSp; apply (proj1 (HFSp q Hq)));
assert (W516 : forall q, 0 <= q < 128 -> writable_at SEGS (mrestrict (w_H Wx) (ms_mem msx)) (base_val Ex (Some 516%nat) + q))
  by (intros q Hq; cbn [base_val]; rewrite RF, unsigned_lit_small by lia; apply (apresent_writable SEGS);
      apply (proj1 (HFp (F + q) ltac:(lia))))
end.
t3_rw HS 529%nat 16 W529. t3_rw HS 516%nat 128 W516. clear W529 W516 HFp HFSp R12.
ra_join HS ss_cutJ 700%nat pz_deadJ ltac:(idtac; ra_join_val HS 700%nat 0%nat Ra0 E700).
pz_rebase HS AGX.
refine (HJc fx' _ _ _ _ HS _ _).
- do 6 (split; [assumption|]); assumption.
- rewrite E700, (t3_model n fr Hhdr HP3'). cbn [fst]. rewrite EK.
  destruct (t3_KL1_cases (cp_v fr 22)) as [Q|[Q|[Q|[Q|[Q|Q]]]]]; rewrite Q; apply bv_eq; vm_compute; reflexivity.
- intros q Hq. rewrite (t3_model n fr Hhdr HP3'). exact (OUT q Hq).
Qed.
End d.
End b.
