(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: adapted from cgif's lib/A/ACgq.v and lib/A/ACk8.v (file header, walk tactic forms) for reac_ctrl_parse of libreac's fuzz_grant. *)
(* Modified by Theorem Labs, 2026-10: image B (fuzz_grant.asan-ubsan) segment of the reac_ctrl_parse 0x82774 walk, in the shape of lib/A/Prog/CtrlParseTail5.v at a working branch 603e40683a4 (image A 0x82000), over image B's listing and walk layer (lib/B/Prog), with image B's addresses and objects; image B's extra UBSan guards are decided by the engine from the atom facts. Source blob 33ccdd86f914 (lib/A/Prog/CtrlParseTail5.v at a working branch 603e40683a4; the same blob at 7e98c198edd). *)
(* reac_ctrl_parse, the walk from cut B (0x82970) to cut J for the frames of class 5 (pz_P5):
   frame type cd ea, a link other than 1 and 4: LINK2 (12) for link 2, UNKNOWN_CTRL (13) otherwise. *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import YCbq.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0s YM05.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import PaRun PaShadow.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import PaJournal.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import GrantSyms GrantList GrantPa GrantPaLib.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import PaBase.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import YC81 YC4b.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import YC1g YC1h YC45 YC85 GrantFrame.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import YC88.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import RcKind RcParse.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import CtrlParseLib KindOfLink1 GrantRo ACj1 GrantACja.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import CtrlParseCut.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Lib Require Bytes.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
(* The model: a frame of class 5 has kind 12 (link 2) or 13, and no record container (cp_rec). *)
Lemma t5_kind : forall n fr, cp_hdr n fr = true -> cp_v fr 16 = 205 -> cp_v fr 17 = 234 -> cp_v fr 18 <> 1 -> cp_v fr 18 <> 4 ->
ctrlparse n fr = (if cp_v fr 18 =? 2 then 12 else 13, cp_struct fr (if cp_v fr 18 =? 2 then 12 else 13)).
Proof.
intros n fr Hh H16 H17 H1 H4. unfold ctrlparse, cp_kind, cp_type. rewrite Hh, H16, H17.
apply Z.eqb_neq in H1, H4. rewrite H1, H4. reflexivity.
Qed.
Lemma t5_rec : forall fr, cp_v fr 18 <> 4 -> cp_rec fr = false.
Proof. intros fr H. unfold cp_rec. apply Z.eqb_neq in H. rewrite H, andb_false_r. reflexivity. Qed.
(* The values of the out struct's chunks. *)
Lemma t5_u8 : forall z, bv_unsigned (Z_to_bv 8 z) = z mod 256.
Proof. intros z. rewrite Z_to_bv_unsigned. reflexivity. Qed.
Lemma t5_bow : forall E e j, bv_unsigned (YP09.byte_of_word (sv_denot E e) j) = Z.shiftr (U E e) (8 * j) mod 256.
Proof. intros E e j. unfold YP09.byte_of_word, U. apply t5_u8. Qed.
Lemma t5_U_seqz : forall E n, U E (SAlu ALU_SLTU (SOff n 0) (SLit 1)) = if bv_unsigned (ew E n) =? 0 then 1 else 0.
Proof.
intros E n. rewrite U_SAlu, U_SLit, U_SOff. cbn [zalu_raw].
pose proof (bv_unsigned_in_range 64 (ew E n)) as R. change (bv_modulus 64) with (2 ^ 64) in R.
unfold zcanon, M64. rewrite Z.add_0_r, (Z.mod_small (bv_unsigned (ew E n))) by lia.
change (1 mod 2 ^ 64) with 1.
destruct (Z.eqb_spec (bv_unsigned (ew E n)) 0) as [H0|H0]; destruct (Z.ltb_spec (bv_unsigned (ew E n)) 1) as [H1|H1];
try lia; reflexivity.
Qed.
Lemma t5_U_pack : forall E a b va vb, U E (SOff a 0) = va -> U E (SOff b 0) = vb -> 0 <= va < 256 -> 0 <= vb < 256 ->
U E (SAlu ALU_OR (SAlu ALU_SLL (SOff a 0) (SLit 8)) (SOff b 0)) = va * 256 + vb.
Proof.
intros E a b va vb Ha Hb Hva Hvb. rewrite !U_SAlu, U_SLit, Ha, Hb. cbn [zalu_raw].
change (Z.land (zcanon 8) 63) with 8.
assert (Hs : Z.shiftl va 8 = va * 256) by (rewrite Z.shiftl_mul_pow2 by lia; reflexivity).
rewrite (zcanon_id (Z.shiftl va 8)) by (rewrite Hs; unfold M64; lia).
rewrite Z.lor_comm, (OSSVerify.Proofs.libreac.fuzz_grant.lib.Lib.Bytes.lor_shiftl8_add vb va) by lia.
rewrite zcanon_id by (unfold M64; lia). lia.
Qed.
(* The out struct at the two leaves (k = 12 or 13), as the symbolic run leaves it. *)
Definition t5_out (k : Z) : list YP09.chunk :=
[YP09.mkChunk 0 (CVal 4 (SLit k)); YP09.mkChunk 26 (CVal 1 (SOff 62 0));
 YP09.mkChunk 24 (CVal 2 (SAlu ALU_OR (SAlu ALU_SLL (SOff 60 0) (SLit 8)) (SOff 61 0)));
 YP09.mkChunk 23 (CVal 1 (SOff 59 0)); YP09.mkChunk 22 (CVal 1 (SOff 58 0));
 YP09.mkChunk 20 (CVal 2 (SAlu ALU_OR (SAlu ALU_SLL (SOff 55 0) (SLit 8)) (SOff 54 0)));
 YP09.mkChunk 16 (CVal 4 (SAlu ALU_SLTU (SOff 640 0) (SLit 1)))]
++ map (fun i => YP09.mkChunk (4 + Z.of_nat i) (CVal 1 (SOff (46 + i) 0))) (seq 0 6)
++ map (fun i => YP09.mkChunk (10 + Z.of_nat i) (CVal 1 (SOff (40 + i) 0))) (seq 0 6)
++ [YP09.mkChunk 27 (CZero 9)].
Ltac t5_fin :=
try (match goal with |- context [Z.shiftr _ (8 * ?e)] => let v := eval vm_compute in e in change e with v end);
try (rewrite Z.shiftr_div_pow2 by lia);
repeat match goal with |- context [2 ^ (8 * ?e)] => let v := eval vm_compute in (2 ^ (8 * e)) in change (2 ^ (8 * e)) with v end;
repeat match goal with |- context [if cp_bcast ?f then _ else _] => destruct (cp_bcast f) end;
cbv beta iota; try unfold cp_z; rewrite ?t5_u8;
repeat match goal with |- context [bv_unsigned (cp_b ?f ?j)] =>
let x := fresh "x" in let Hx := fresh "Hx" in
pose proof (cp_v_range f j) as Hx; unfold cp_v in Hx; set (x := bv_unsigned (cp_b f j)) in *; clearbody x end;
first [lia | (Z.to_euclidean_division_equations; lia)].
(* After a run with the windows of cut B: acall_kept from the entry memory to the new memory. *)
Ltac t5_kp :=
lazymatch goal with
| HFr : frame_of ?Ef ?rsf (mrestrict _ ?mA) (mrestrict _ ?mB), HG : mem_grows _ _, HF : frame_of _ _ (ms_mem _) (ms_mem _),
  KP : acall_kept _ ?B ?lyc ?Sc ?W ?memc _ _ (?spv - TPARSE_STK) ?spv (fun a => ?ov <= a < _),
  HAR : AR _ ?B ?lyc ?Sc ?W ?memc ?mdc, LAWS : AR_laws _ ?B,
  AGX : forall n, (n < 512)%nat -> ew _ n = ew _ n,
  B33 : bv_unsigned (ew _ 33) = ?sp1v, Usp : bv_unsigned (ew _ 2) = _, B12 : bv_unsigned (ew _ 12) = _,
  Hoin : In (?co, ?po) (frames ?Sc), Holo : frame_addr ?lyc ?co ?po <= ?ov, Hohi : ?ov + 36 <= _ |- _ =>
let Hw1 := fresh "Hw1" in let KP' := fresh "KP" in
assert (Hw1 : forall b wlo whi a, In (b, wlo, whi) (windows rsf) -> base_val Ef b + wlo <= a < base_val Ef b + whi ->
(fun a => (sp1v <= a < spv) \/ (ov <= a < ov + 36)) a)
by (pz_win_tac ltac:(fun H => rewrite ?(AGX 2%nat), ?(AGX 12%nat), ?(AGX 33%nat) in H by lia; rewrite ?Usp, ?B12, ?B33 in H));
pose proof (pz_kept_run B LAWS lyc Sc W memc mdc mA mB (spv - TPARSE_STK) spv ov (fun _ => False)
(fun a => (sp1v <= a < spv) \/ (ov <= a < ov + 36)) co po HAR ltac:(lia) ltac:(lia) Hoin Holo Hohi
ltac:(intros; contradiction) ltac:(intros; contradiction) ltac:(intros; contradiction) ltac:(intros; contradiction)
ltac:(intros a Ha; cbv beta in Ha; lia) KP
(kept_of_frame _ _ _ _ _ _ HFr Hw1)
(fun a Ha => apresent_grows _ _ _ a HG Ha)) as KP';
clear KP Hw1 HF HFr HG; rename KP' into KP end.
(* A refuted branch whose condition is closed once the type bytes are known. *)
Ltac t5_refc Hc U56 U57 :=
exfalso; rewrite ?branch_ne_U, ?branch_eq_U in Hc; rewrite ?U_SAlu, ?U_SLit, ?U56, ?U57 in Hc; vm_compute in Hc; discriminate Hc.
(* The region based at atom n writable again on [0, hi), from Hw (its bytes are writable). *)
Ltac t5_rw HS n hi Hw :=
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs n in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rs got_regionP) in
let HS3 := fresh "HS3" in
pose proof (ast_ok_pi_set_region Ex ssx msx i r (set_window r 0 hi) HS ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity)
(region_ok_rewindow _ Ex _ r 0 hi (st_ok_pi_region_nth Ex ssx msx i r HS ltac:(vm_compute; reflexivity)) Hw)) as HS3;
clear HS; rename HS3 into HS; pz_norm HS end.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Context {PI : PAImg grant_listing}.
#[local] Notation SEGS := (@pa_segs _ grant_listing PI).
#[local] Notation VAL := (@pa_val _ grant_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ grant_listing PI).
#[local] Notation BASE := (@pa_val _ grant_listing PI A_TEXT).
Lemma t5_rd : forall E H mem r o off v z,
region_ok SEGS E (mrestrict H mem) r -> base_val E (YP09.r_base r) = o ->
pz_chunk_at E o (YP09.r_chunks r) off = Some v -> bv_unsigned v = z ->
aview SEGS H mem (o + off) = Some z.
Proof.
intros E H mem r o off v z Hr Ho Hc Hz. subst o z.
exact (pz_region_byte E H mem r off v Hr Hc).
Qed.
Ltac t5_byte ROK Ho UA P0 P16 P20 P24 :=
lazymatch goal with |- context [Z.of_nat ?n] => let v := eval vm_compute in (Z.of_nat n) in change (Z.of_nat n) with v end;
eapply (t5_rd _ _ _ _ _ _ _ _ ROK Ho); [reflexivity |];
cbn [nth app];
try rewrite t5_bow;
rewrite ?P0, ?P16, ?P20, ?P24;
repeat match goal with |- context [U ?Ex (SOff ?a 0)] =>
let j := eval vm_compute in (a - 40)%nat in
change (U Ex (SOff a 0)) with (U Ex (SOff (40 + j) 0)); rewrite (UA j ltac:(lia)) end;
t5_fin.
(* The 36 bytes of the out struct at a leaf of kind k are cp_struct fr k. *)
Lemma t5_out_bytes : forall E H mem o fr k,
region_ok SEGS E (mrestrict H mem) (YP09.mkRegion (Some 12%nat) 0 36 0 36 (t5_out k)) ->
bv_unsigned (ew E 12) = o ->
(forall i, (i < 23)%nat -> ew E (40 + i) = Z_to_bv 64 (cp_v fr i)) ->
(bv_unsigned (ew E 640) =? 0) = cp_bcast fr ->
0 <= k < 256 -> (k =? 6) = false -> cp_rec fr = false ->
forall i, (i < 36)%nat -> aview SEGS H mem (o + Z.of_nat i) = Some (bv_unsigned (nth i (cp_struct fr k) cp_z)).
Proof.
intros E H mem o fr k ROK Ho EB H640 Hk Hk6 Hrec.
assert (UA : forall j, (j < 23)%nat -> U E (SOff (40 + j) 0) = bv_unsigned (cp_b fr j)).
{ intros j Hj. pose proof (cp_v_range fr j). rewrite (U_atom E (40 + j) (cp_v fr j) (EB j Hj)) by lia. reflexivity. }
assert (P0 : U E (SLit k) = k) by (apply U_lit; lia).
assert (P16 : U E (SAlu ALU_SLTU (SOff 640 0) (SLit 1)) = if cp_bcast fr then 1 else 0) by (rewrite t5_U_seqz, H640; reflexivity).
assert (P20 : U E (SAlu ALU_OR (SAlu ALU_SLL (SOff 55 0) (SLit 8)) (SOff 54 0)) = bv_unsigned (cp_b fr 15) * 256 + bv_unsigned (cp_b fr 14)).
{ apply t5_U_pack; [exact (UA 15%nat ltac:(lia)) | exact (UA 14%nat ltac:(lia)) | exact (cp_v_range fr 15) | exact (cp_v_range fr 14)]. }
assert (P24 : U E (SAlu ALU_OR (SAlu ALU_SLL (SOff 60 0) (SLit 8)) (SOff 61 0)) = bv_unsigned (cp_b fr 20) * 256 + bv_unsigned (cp_b fr 21)).
{ apply t5_U_pack; [exact (UA 20%nat ltac:(lia)) | exact (UA 21%nat ltac:(lia)) | exact (cp_v_range fr 20) | exact (cp_v_range fr 21)]. }
unfold cp_struct. rewrite Hrec, Hk6.
intros i Hi.
do 36 (destruct i as [|i]; [t5_byte ROK Ho UA P0 P16 P20 P24 |]). lia.
Qed.
Lemma pz_tail5 : forall B G, pz_rt B G -> forall c, pz_ok B c -> pz_cutJ_spec B c -> pz_cutB_case B c pz_P5.
Proof.
intros B G RT c Hok HJc E ms md Hcur HS SHOK Hhdr Hbc HP5.
pz_open c Hok. pz_open_rt RT. pz_open_cur Hcur. pz_std.
pose (RUN := paj_run B LAWS). pose (RUNTO := paj_run_to B LAWS). pose (BR := paj_branch (PI := PI)).
pose proof (fun n0 (Hn0 : (n0 < 33)%nat) => AGX n0 ltac:(lia)) as AG.
destruct HP5 as (HT & HL1 & HL4).
pose proof HT as HT'. unfold cp_type in HT'. apply andb_prop in HT' as [HT16 HT17]. apply Z.eqb_eq in HT16, HT17.
assert (EB : forall i, (i < 23)%nat -> ew E (40 + i) = Z_to_bv 64 (cp_v fr i))
by (intros i Hi; rewrite (AGX (40 + i)%nat) by lia; apply EFB; lia).
assert (U56 : U E (SOff 56 0) = 205)
by (rewrite <- HT16; pose proof (cp_v_range fr 16); exact (U_atom E 56 _ (EB 16%nat ltac:(lia)) ltac:(lia))).
assert (U57 : U E (SOff 57 0) = 234)
by (rewrite <- HT17; pose proof (cp_v_range fr 17); exact (U_atom E 57 _ (EB 17%nat ltac:(lia)) ltac:(lia))).
assert (U58 : U E (SOff 58 0) = cp_v fr 18)
by (pose proof (cp_v_range fr 18); exact (U_atom E 58 _ (EB 18%nat ltac:(lia)) ltac:(lia))).
assert (Ho12 : bv_unsigned (ew E 12) = o) by (rewrite (AGX 12%nat) by lia; exact B12).
assert (H640 : (bv_unsigned (ew E 640) =? 0) = cp_bcast fr).
{ destruct (cp_bcast fr) eqn:Hb.
- first [rewrite (proj2 Hbc eq_refl) | rewrite (proj2 Hbc Hb)]. reflexivity.
- apply Z.eqb_neq. intros H0. assert (Hz : ew E 640 = Z_to_bv 64 0) by (apply bv_eq; rewrite H0; reflexivity).
pose proof (proj1 Hbc Hz) as Hz'. rewrite ?Hb in Hz'. discriminate Hz'. }
pose proof (t5_rec fr HL4) as Hrec.
pose proof (t5_kind n fr Hhdr HT16 HT17 HL1 HL4) as Hkind.
(* The disjunctions and the facts the walk does not need slow every lia down: drop them. *)
clear Hdfo HFapp HsepF HsepO Hfapp Hoapp HBC_RNG Hob0 Hob1 Hob32 Hob33 HBASE HBLO Hroom Hflo Hfhi Hf4096 Hfceil Hf8 Ho8 Hra4
HFal HFq HF8 Hsp1al Hsp1al16 Hbot Htop2 Htop HFL4096 HFLce Hcfimg Hcoimg HFimg.
(* 1. To 0x82b70 (bnez: frame bytes 16 | 17 nonzero, i.e. not a FILLER frame); the fall-through is refuted. *)
paj_run_tok RUN HS HJ2 SHOK PZspan.
{ awrFL_with ltac:(idtac; pz_awr_hd) AG fpos F I. }
t5_kp.
psrr_branch_tok RUN BR HS SHOK PZspan.
2: { t5_refc Hc U56 U57. }
clear Hc.
(* 2. 0x82c8c (bne byte 16, 0xcf): taken; the fall-through (MASTER_ANNOUNCE) is refuted. *)
paj_run_tok RUN HS HJ2 SHOK PZspan.
{ awrFL_with ltac:(idtac; pz_awr_hd) AG fpos F I. }
t5_kp.
psrr_branch_tok RUN BR HS SHOK PZspan.
2: { t5_refc Hc U56 U57. }
clear Hc.
(* 3. 0x82cb4 (bne byte 16, 0xce): taken; the fall-through (SPLIT_ANNOUNCE) is refuted. *)
paj_run_tok RUN HS HJ2 SHOK PZspan.
{ awrFL_with ltac:(idtac; pz_awr_hd) AG fpos F I. }
t5_kp.
psrr_branch_tok RUN BR HS SHOK PZspan.
2: { t5_refc Hc U56 U57. }
clear Hc.
(* 4. 0x82cdc (bne byte 16, 0xcd): falls through; the taken side (another type) is refuted. *)
paj_run_tok RUN HS HJ2 SHOK PZspan.
{ awrFL_with ltac:(idtac; pz_awr_hd) AG fpos F I. }
t5_kp.
psrr_branch_tok RUN BR HS SHOK PZspan.
1: { t5_refc Hc U56 U57. }
clear Hc.
(* 5. 0x82ce4 (bne byte 17, 0xea): falls through; the taken side is refuted. *)
paj_run_tok RUN HS HJ2 SHOK PZspan.
{ awrFL_with ltac:(idtac; pz_awr_hd) AG fpos F I. }
t5_kp.
psrr_branch_tok RUN BR HS SHOK PZspan.
1: { t5_refc Hc U56 U57. }
clear Hc.
(* 6. 0x82cec (beq link, 4): falls through; the taken side (the record container, class 4) is refuted. *)
paj_run_tok RUN HS HJ2 SHOK PZspan.
{ awrFL_with ltac:(idtac; pz_awr_hd) AG fpos F I. }
t5_kp.
psrr_branch_tok RUN BR HS SHOK PZspan.
1: { exfalso. rewrite branch_eq_U, U58, U_SLit in Hc. change (zcanon 4) with 4 in Hc. apply Z.eqb_eq in Hc. exact (HL4 Hc). }
clear Hc.
(* 7. 0x82cf4 (beq link, 2). *)
paj_run_tok RUN HS HJ2 SHOK PZspan.
{ awrFL_with ltac:(idtac; pz_awr_hd) AG fpos F I. }
t5_kp.
psrr_branch_tok RUN BR HS SHOK PZspan.
- (* link 2: LINK2 (12), through 0x82d48 and the store at 0x82f54, to the join. *)
rewrite branch_eq_U, U58, U_SLit in Hc. change (zcanon 2) with 2 in Hc. apply Z.eqb_eq in Hc.
assert (Hk : ctrlparse n fr = (12, cp_struct fr 12)) by (rewrite Hkind, (proj2 (Z.eqb_eq _ _) Hc); reflexivity).
clear Hc.
paj_run_to_tok RUNTO HS HJ2 SHOK PZspan AF_JOIN.
{ awrFL_with ltac:(idtac; pz_awr_hd) AG fpos F I. }
t5_kp.
lazymatch goal with HSx : st_ok_pi _ _ ?Ex ?ssx (restrict (w_H ?Wx) ?msx) |- _ =>
pose proof (st_ok_pi_region_nth Ex ssx (restrict (w_H Wx) msx) 0 _ HSx eq_refl) as ROK;
pose proof (t5_out_bytes Ex (w_H Wx) (ms_mem msx) o fr 12 ROK Ho12 EB H640 ltac:(lia) eq_refl Hrec) as Hout end.
clear ROK.
prreg HS (10%bv : bv 5) R10.
destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos (proj1 HJ2) Hfin2) as (_ & _ & HFpJ & HFSJ).
change (fs_frame_bytes 1) with 128 in HFpJ, HFSJ. change (128 / 8) with 16 in HFSJ. rewrite <- EF in HFpJ, HFSJ.
lazymatch goal with HSx : st_ok_pi _ _ ?Ex _ (restrict (w_H ?Wx) ?msx) |- _ =>
assert (W529 : forall q, 0 <= q < 16 -> writable_at SEGS (mrestrict (w_H Wx) (ms_mem msx)) (base_val Ex (Some 529%nat) + q))
by (intros q Hq; cbn [base_val]; rewrite E529, unsigned_lit_small by (unfold SB; lia); apply (apresent_writable SEGS);
unfold shadow_addr in HFSJ; rewrite <- SB_SHADOW_OFF in HFSJ; apply (proj1 (HFSJ q Hq)));
assert (W516 : forall q, 0 <= q < 128 -> writable_at SEGS (mrestrict (w_H Wx) (ms_mem msx)) (base_val Ex (Some 516%nat) + q))
by (intros q Hq; cbn [base_val]; rewrite RF, unsigned_lit_small by lia; apply (apresent_writable SEGS); apply (proj1 (HFpJ (F + q) ltac:(lia)))) end.
t5_rw HS 529%nat 16 W529. t5_rw HS 516%nat 128 W516. clear W529 W516.
ra_join HS ss_cutJ 700%nat pz_deadJ idtac.
ra_join_val HS 700%nat 0%nat R10 E700.
pz_rebase HS AGX.
refine (HJc _ _ _ _ HS _ _).
+ split; [assumption|]. split; [exact AGX|]. split; [exact RF|]. split; [exact E528|]. split; [exact E529|]. split; [exact HJ2 | exact KP].
+ rewrite Hk. exact E700.
+ rewrite Hk. exact Hout.
- (* another link: UNKNOWN_CTRL (13). *)
rewrite branch_eq_U, U58, U_SLit in Hc. change (zcanon 2) with 2 in Hc. apply Z.eqb_neq in Hc.
assert (Hk : ctrlparse n fr = (13, cp_struct fr 13)) by (rewrite Hkind, (proj2 (Z.eqb_neq _ _) Hc); reflexivity).
clear Hc.
(* 8. 0x82cfc (bne link, 1): taken; the fall-through (the call of kind_of_link1, class 3) is refuted. *)
paj_run_tok RUN HS HJ2 SHOK PZspan.
{ awrFL_with ltac:(idtac; pz_awr_hd) AG fpos F I. }
t5_kp.
psrr_branch_tok RUN BR HS SHOK PZspan.
2: { exfalso. rewrite branch_ne_U, U58, U_SLit in Hc. change (zcanon 1) with 1 in Hc. apply negb_false_iff, Z.eqb_eq in Hc. exact (HL1 Hc). }
clear Hc.
(* Through 0x82f10 and the store at 0x82f54, to the join. *)
paj_run_to_tok RUNTO HS HJ2 SHOK PZspan AF_JOIN.
{ awrFL_with ltac:(idtac; pz_awr_hd) AG fpos F I. }
t5_kp.
lazymatch goal with HSx : st_ok_pi _ _ ?Ex ?ssx (restrict (w_H ?Wx) ?msx) |- _ =>
pose proof (st_ok_pi_region_nth Ex ssx (restrict (w_H Wx) msx) 0 _ HSx eq_refl) as ROK;
pose proof (t5_out_bytes Ex (w_H Wx) (ms_mem msx) o fr 13 ROK Ho12 EB H640 ltac:(lia) eq_refl Hrec) as Hout end.
clear ROK.
prreg HS (10%bv : bv 5) R10.
destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos (proj1 HJ2) Hfin2) as (_ & _ & HFpJ & HFSJ).
change (fs_frame_bytes 1) with 128 in HFpJ, HFSJ. change (128 / 8) with 16 in HFSJ. rewrite <- EF in HFpJ, HFSJ.
lazymatch goal with HSx : st_ok_pi _ _ ?Ex _ (restrict (w_H ?Wx) ?msx) |- _ =>
assert (W529 : forall q, 0 <= q < 16 -> writable_at SEGS (mrestrict (w_H Wx) (ms_mem msx)) (base_val Ex (Some 529%nat) + q))
by (intros q Hq; cbn [base_val]; rewrite E529, unsigned_lit_small by (unfold SB; lia); apply (apresent_writable SEGS);
unfold shadow_addr in HFSJ; rewrite <- SB_SHADOW_OFF in HFSJ; apply (proj1 (HFSJ q Hq)));
assert (W516 : forall q, 0 <= q < 128 -> writable_at SEGS (mrestrict (w_H Wx) (ms_mem msx)) (base_val Ex (Some 516%nat) + q))
by (intros q Hq; cbn [base_val]; rewrite RF, unsigned_lit_small by lia; apply (apresent_writable SEGS); apply (proj1 (HFpJ (F + q) ltac:(lia)))) end.
t5_rw HS 529%nat 16 W529. t5_rw HS 516%nat 128 W516. clear W529 W516.
ra_join HS ss_cutJ 700%nat pz_deadJ idtac.
ra_join_val HS 700%nat 0%nat R10 E700.
pz_rebase HS AGX.
refine (HJc _ _ _ _ HS _ _).
+ split; [assumption|]. split; [exact AGX|]. split; [exact RF|]. split; [exact E528|]. split; [exact E529|]. split; [exact HJ2 | exact KP].
+ rewrite Hk. exact E700.
+ rewrite Hk. exact Hout.
Qed.
End d.
End b.
