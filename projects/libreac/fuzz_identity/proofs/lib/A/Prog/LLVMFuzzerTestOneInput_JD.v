(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YC1f.v:361-370, for
   libreac/fuzz_identity's ASan build (lib/A). *)
(* Piece D of segment J of LLVMFuzzerTestOneInput's ASan walk, 0x81ab4 (BASE + 0x13a8) .. 0x81c34 (BASE + 0x1528):
   j_D_stmt of lib/A/Prog/LLVMFuzzerTestOneInput_Jcut.v.
     0x81ab4 .. 0x81ad0  a7 := the shadow base (mf+176), a0 := w4 + n4 (n4 = 4 at mf+208), its shadow test and
                         w4[4] = 0
     0x81ad4 .. 0x81aec  the shadow test of the stem and the load of stem[0]; an empty stem goes to 0x81b80
     0x81af0 .. 0x81afc  s9 := 0, a0 := exp_nm - 4, a2 := stem + 1, a1 := exp_nm
     0x81b00 .. 0x81b5c  the stem copy loop (j_stem_loop of _Jstem.v); s9 = |stem| at 0x81b60
     0x81b60 .. 0x81b7c  |stem| < 4 goes to 0x81b84; else bcmp(exp_nm + |stem| - 4, w4, 4) at 0x81b70, a7 is
                         reloaded, and an equal tail goes to 0x81c1c
     0x81b80 .. 0x81c18  exp_nm[ln] = '-' and the four bytes of w4 after it (the loop at 0x81bbc runs four times:
                         the digits of w4 are not 0 and w4[4] is)
     0x81c1c .. 0x81c30  exp_nm[ln] = 0
   Each chunk is a lemma in continuation form: from its first slot, with the facts it reads, every path reaches
   the next chunk's slot with that chunk's facts. Every shadow test is decided by the shadow of w4 and exp_nm
   (zero, from Pj2) or the stem's (range_addressable, jstem_at); no path reaches a report block. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation String Ascii.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YP0j YCbn.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YN3v YI04 YI08 YI09 YI00 YG0s YI16 YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YC5d YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
PaRun PaShadow PaJournal IdentSyms IdentList IdentPa IdentPaLib IdentBase IdentFrame IdentCJ IdentRo
IdentProgSig YC1g YC1h YC45 YC4b YC81 YC85.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Rt Require Import MemchrDef.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require put_dec.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
LLVMFuzzerTestOneInput LLVMFuzzerTestOneInput_inv.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require SlotModel RcIdentModel IdentSpec put_dec_c.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import LLVMFuzzerTestOneInput_Jcut.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require LLVMFuzzerTestOneInput_Jstem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
(* YC4b turns lia's division and modulo handling off; the address arithmetic here needs it. *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the symbolic states of the chunks ----------------------------------------------------------------------- *)
Definition JD_SB : Z := 0x7fff8000.
Definition jd_Bspan : Z * Z := (JD_SB, JD_SB + 2 ^ 44 - 1).
Definition jd_A47 : Z := 2 ^ 47 - 4096.
(* 0x81ab4: atom 33 = the shadow base (the word at mf+176, loaded into a7), atom 32 = stem[0]; the store of w4[4]
   is the window of atom 18 (s2 = w4), the stem byte the chunk of atom 23 (s7 = the stem). *)
Definition jd1_Bx : sv := SOff 33 0.
Definition jd1_regions : smem :=
  [ YP09.mkRegion (Some 9%nat) 176 216 216 216
      [YP09.mkChunk 176 (CVal 8 (SOff 33 0)); YP09.mkChunk 208 (CVal 8 (SLit 4))];
    YP09.mkRegion (Some 18%nat) 4 5 4 5 [];
    YP09.mkRegion (Some 23%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 32 0))] ].
Definition jd1_facts : facts :=
  mkFacts [ (33%nat, mkAF JD_SB JD_SB 0); (32%nat, mkAF 0 255 0);
            (18%nat, mkAF 4096 jd_A47 0); (23%nat, mkAF 4096 jd_A47 0); (26%nat, mkAF 4096 jd_A47 0) ] [] [].
Definition ss_jd1 : sstate := mkSS 0x13a8 sr_atoms jd1_regions None jd1_facts.
Definition SH_jd1 : list shent := [mkSHE 18 5 4].
Definition JD1_KEPT : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 26; 27]%bv.
(* 0x81b60: no region, no fact; the run stops at the bltu on |stem| and at the call of the bcmp wrapper. *)
Definition jd_Bx17 : sv := SOff 17 0.
Definition ss_jd2 : sstate := mkSS 0x1454 sr_atoms [] None (mkFacts [] [] []).
(* 0x81b74, the return of bcmp: atom 32 = the shadow base reloaded into a7 from mf+176. *)
Definition ss_jd3 : sstate :=
  mkSS 0x1468 sr_atoms [YP09.mkRegion (Some 9%nat) 176 184 184 184 [YP09.mkChunk 176 (CVal 8 (SOff 32 0))]] None
    (mkFacts [(32%nat, mkAF JD_SB JD_SB 0)] [] []).
Definition JD3_KEPT : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
Definition JD2_KEPT : list (bv 5) := [2; 3; 4; 8; 9; 10; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
(* 0x81b84: atom 32 = exp_nm + ln (the alias s10 + s9), atoms 33 .. 36 the four bytes of w4 (digits), w4[4] = 0;
   the five bytes written are the window of atom 32. *)
Definition jd4_regions : smem :=
  [ YP09.mkRegion (Some 32%nat) 0 5 0 5 [];
    YP09.mkRegion (Some 18%nat) 0 5 0 0
      [YP09.mkChunk 0 (CVal 1 (SOff 33 0)); YP09.mkChunk 1 (CVal 1 (SOff 34 0));
       YP09.mkChunk 2 (CVal 1 (SOff 35 0)); YP09.mkChunk 3 (CVal 1 (SOff 36 0));
       YP09.mkChunk 4 (CVal 1 (SLit 0))] ].
Definition jd4_facts : facts :=
  mkFacts [ (17%nat, mkAF JD_SB JD_SB 0); (26%nat, mkAF 4096 jd_A47 0); (25%nat, mkAF 0 16 0);
            (18%nat, mkAF 4096 jd_A47 0); (32%nat, mkAF 4096 jd_A47 0);
            (33%nat, mkAF 48 57 0); (34%nat, mkAF 48 57 0); (35%nat, mkAF 48 57 0); (36%nat, mkAF 48 57 0) ] []
    [ (SAlu ALU_ADD (SOff 26 0) (SOff 25 0), SOff 32 0) ].
Definition ss_jd4 : sstate := mkSS 0x1478 sr_atoms jd4_regions None jd4_facts.
Definition SH_jd4 : list shent := [mkSHE 32 5 0].
Definition JD4_KEPT : list (bv 5) := [2; 3; 4; 8; 9; 17; 19; 20; 21; 22; 23; 24; 26; 27]%bv.
(* 0x81c1c: atom 32 = exp_nm + s9 (the alias), the byte written. *)
Definition ss_jd5 : sstate :=
  mkSS 0x1510 sr_atoms [YP09.mkRegion (Some 32%nat) 0 1 0 1 []] None
    (mkFacts [ (17%nat, mkAF JD_SB JD_SB 0); (26%nat, mkAF 4096 jd_A47 0); (25%nat, mkAF 0 31 0);
               (32%nat, mkAF 4096 jd_A47 0) ] []
       [ (SAlu ALU_ADD (SOff 26 0) (SOff 25 0), SOff 32 0) ]).
Definition SH_jd5 : list shent := [mkSHE 32 1 0].
Definition JD5_KEPT : list (bv 5) := [2; 3; 4; 8; 9; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
(* The registers every chunk keeps (the ones jcut_mk and Pj3 read, but s9 and a7). *)
Definition JD_FK : list (bv 5) := [2; 3; 4; 8; 9; 19; 20; 21; 22; 24; 26; 27]%bv.

(* ---- the plain model of the expected name ------------------------------------------------------------------- *)
Module JDModel.
Import RcIdentModel SlotModel IdentSpec.
Lemma nthb_l : forall (l1 l2 : list byte) j, (j < length l1)%nat -> nthb (l1 ++ l2) j = nthb l1 j.
Proof. intros l1 l2 j H. unfold nthb. apply app_nth1. exact H. Qed.
Lemma nthb_r : forall (l1 l2 : list byte) j, (length l1 <= j)%nat -> nthb (l1 ++ l2) j = nthb l2 (j - length l1).
Proof. intros l1 l2 j H. unfold nthb. apply app_nth2. exact H. Qed.
Lemma nthb_skipn : forall (l : list byte) k i, nthb (skipn k l) i = nthb l (k + i).
Proof.
  unfold nthb. intros l k; revert l; induction k as [|k IH]; intros [|x l] i; cbn; try reflexivity;
    [destruct i; reflexivity | apply IH].
Qed.
Lemma beq_nth : forall xs ys, length xs = length ys ->
  (bytes_eqb xs ys = true <-> forall i, (i < length xs)%nat -> bz (nthb xs i) = bz (nthb ys i)).
Proof.
  induction xs as [|x xs IH]; intros [|y ys] Hl; cbn [length] in Hl; try discriminate.
  - cbn [bytes_eqb]. split; [intros _ i Hi; cbn [length] in Hi; lia | reflexivity].
  - cbn [bytes_eqb]. injection Hl as Hl. rewrite andb_true_iff, Z.eqb_eq, (IH ys Hl). split.
    + intros [H0 H1] [|i] Hi; [exact H0 | apply H1; cbn [length] in Hi; lia].
    + intros H. split; [exact (H 0%nat ltac:(cbn [length]; lia)) | intros i Hi; exact (H (S i) ltac:(cbn [length]; lia))].
Qed.
Lemma ends_iff : forall (s w : list byte), (4 <= length s)%nat -> length w = 4%nat ->
  (bytes_eqb (skipn (length s - 4) s) (firstn 4 w) = true <->
   forall i, (i < 4)%nat -> bz (nthb s (length s - 4 + i)) = bz (nthb w i)).
Proof.
  intros s w Hs Hw. rewrite firstn_all2 by lia.
  rewrite (beq_nth (skipn (length s - 4) s) w ltac:(rewrite length_skipn; lia)). rewrite length_skipn.
  replace (length s - (length s - 4))%nat with 4%nat by lia.
  split; intros H i Hi; specialize (H i Hi); rewrite nthb_skipn in *; exact H.
Qed.
Lemma okw_le : forall v, 0 <= v -> okw v = true -> v <= 40.
Proof.
  intros v H0 H. unfold okw in H. apply orb_true_iff in H as [H|H]; [apply Z.eqb_eq in H; lia|].
  apply andb_true_iff in H as [H _]. apply andb_true_iff in H as [_ H]. apply Z.leb_le in H. exact H.
Qed.
Lemma W4_props : forall inp, n_wok inp = true ->
  length (n_W4 inp) = 4%nat /\ forall j, (j < 4)%nat -> 48 <= bz (nthb (n_W4 inp) j) <= 57.
Proof.
  intros inp Hw. unfold n_wok in Hw. apply andb_true_iff in Hw as [Hw _]. apply andb_true_iff in Hw as [Hi Ho].
  pose proof (JModel.tin_range inp) as Ri. pose proof (JModel.tout_range inp) as Ro.
  pose proof (okw_le _ (proj1 Ri) Hi) as Hi4. pose proof (okw_le _ (proj1 Ro) Ho) as Ho4.
  assert (HL : z_all (fun x => Nat.eqb (length (DEC x 2)) 2) 41 0 = true) by (vm_compute; reflexivity).
  pose proof (z_all_spec _ 41 0 HL (t_in inp) ltac:(lia)) as L1.
  pose proof (z_all_spec _ 41 0 HL (t_out inp) ltac:(lia)) as L2.
  cbv beta in L1, L2. apply Nat.eqb_eq in L1, L2.
  pose proof (JModel.DEC_digits (t_in inp) 2 ltac:(lia) ltac:(right; reflexivity)) as D1.
  pose proof (JModel.DEC_digits (t_out inp) 2 ltac:(lia) ltac:(right; reflexivity)) as D2.
  unfold n_W4. split; [rewrite length_app, L1, L2; reflexivity|].
  intros j Hj.
  assert (Hd : forallb JModel.digit (DEC (t_in inp) 2 ++ DEC (t_out inp) 2) = true)
    by (rewrite forallb_app, D1, D2; reflexivity).
  rewrite forallb_forall in Hd.
  assert (Hjl : (j < length (DEC (t_in inp) 2 ++ DEC (t_out inp) 2))%nat) by (rewrite length_app, L1, L2; lia).
  specialize (Hd (nthb (DEC (t_in inp) 2 ++ DEC (t_out inp) 2) j) (nth_In _ _ Hjl)).
  unfold JModel.digit in Hd. apply andb_true_iff in Hd as [H1 H2]. apply Z.leb_le in H1, H2. lia.
Qed.
Lemma EXP_len : forall inp, (length (n_stem inp) <= 16)%nat -> length (n_W4 inp) = 4%nat ->
  (length (n_EXP_NM inp) <= 21)%nat.
Proof.
  intros inp Hs Hw. unfold n_EXP_NM. destruct (n_ends_w4 inp); [lia|].
  rewrite !length_app, Hw. cbn [length]. lia.
Qed.
(* The bytes of stem ++ "-" ++ w4 ++ NUL, and of stem ++ NUL. *)
Lemma nth_app5 : forall (s w : list byte) j, length w = 4%nat ->
  bz (nthb ((s ++ [dash] ++ w) ++ [zb 0]) j) =
  if (j <? length s)%nat then bz (nthb s j)
  else if (j =? length s)%nat then 45
  else if (j <? length s + 5)%nat then bz (nthb w (j - length s - 1))
  else 0.
Proof.
  intros s w j Hw. rewrite <- app_assoc.
  destruct (Nat.ltb_spec j (length s)) as [H1|H1]; [rewrite nthb_l by exact H1; reflexivity|].
  rewrite nthb_r by exact H1.
  destruct (Nat.eqb_spec j (length s)) as [H2|H2]; [subst j; rewrite Nat.sub_diag; reflexivity|].
  destruct (j - length s)%nat as [|i] eqn:Hi; [lia|].
  cbn [app]. change (nthb (dash :: (w ++ [zb 0])) (S i)) with (nthb (w ++ [zb 0]) i).
  destruct (Nat.ltb_spec j (length s + 5)) as [H3|H3].
  - rewrite nthb_l by lia. replace (S i - 1)%nat with i by lia. reflexivity.
  - rewrite nthb_r by lia. unfold nthb.
    destruct (i - length w)%nat as [|n]; [reflexivity | rewrite nth_overflow by (cbn [length]; lia); reflexivity].
Qed.
Lemma nth_app0 : forall (s : list byte) j, (j <= length s)%nat ->
  bz (nthb (s ++ [zb 0]) j) = if (j <? length s)%nat then bz (nthb s j) else 0.
Proof.
  intros s j Hj. destruct (Nat.ltb_spec j (length s)) as [H1|H1]; [rewrite nthb_l by exact H1; reflexivity|].
  rewrite nthb_r by exact H1. replace (j - length s)%nat with 0%nat by lia. reflexivity.
Qed.
End JDModel.

(* ---- tactics ------------------------------------------------------------------------------------------------- *)
(* Drop the hypotheses lia must not preprocess (the symbolic states, the journals, the quantified facts). *)
Ltac jd_clean :=
  repeat match goal with
  | H : st_ok_pi _ _ _ _ _ |- _ => clear H
  | H : st_ok _ _ _ _ |- _ => clear H
  | H : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => clear H
  | H : sh_ok _ _ _ _ _ |- _ => clear H
  | H : frame_of _ _ _ _ |- _ => clear H
  | H : mem_grows _ _ |- _ => clear H
  | H : img_env _ _ _ |- _ => clear H
  | H : env_agree _ _ _ |- _ => clear H
  | H : SRr _ _ _ _ |- _ => clear H
  | H : garr8 _ _ _ _ |- _ => clear H
  | H : val_mem _ _ _ _ _ |- _ => clear H
  | H : forall _ : Z, _ |- _ => clear H
  | H : forall _ : nat, _ |- _ => clear H
  | H : forall _ : word, _ |- _ => clear H
  | H : forall _ : bv 5, _ |- _ => clear H
  | H : forall _ : bvmap 5 word, _ |- _ => clear H
  end.
(* The bytes the piece writes: w4[4], exp_nm, and the window of the bcmp call below mf. *)
Definition jd_WS (SF mf a : Z) : Prop := a = SF + 692 \/ (SF + 528 <= a < SF + 560) \/ (mf - 8192 <= a < mf).
Ltac jd_lia := jd_clean; cbv beta; try unfold jd_WS in *; try unfold ESTACK in *; try unfold ASTACK in *; lia.
(* A register of a concrete list of registers. *)
Ltac jd_inl := try unfold JD_FK; try unfold JD1_KEPT; try unfold JD2_KEPT; try unfold JD3_KEPT;
  try unfold JD4_KEPT; try unfold JD5_KEPT; cbn [In]; repeat (first [left; reflexivity | right]).
Ltac jd_ewo := repeat rewrite ew_ewset_other by lia.
Ltac jd_ewo_in H := repeat rewrite ew_ewset_other in H by lia.
(* A register of the symbolic state, as the symbolic value's denotation. *)
Ltac jd_reg HS r Hr :=
  lazymatch type of HS with
  | st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
      pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
      let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
      cbn [ms_regs restrict mkst] in Hr
  end.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg ident_listing}.
#[local] Notation SEGS := (@pa_segs _ ident_listing PI).
#[local] Notation VAL := (@pa_val _ ident_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ ident_listing PI).
#[local] Notation BASE := (@pa_val _ ident_listing PI A_TEXT).
#[local] Notation bz := RcIdentModel.bz.
#[local] Notation nthb := RcIdentModel.nthb.
#[local] Notation zb := RcIdentModel.zb.

(* ---- generic facts ------------------------------------------------------------------------------------------- *)
Lemma jd_w64 : forall z, w64 z = Z_to_bv 64 z.
Proof. reflexivity. Qed.
Lemma jd_U : forall E n v c, ew E n = w64 v -> U E (SOff n c) = (v + c) mod 2 ^ 64.
Proof.
  intros E n v c H. rewrite U_SOff, H, jd_w64, Z_to_bv_unsigned. unfold zcanon, M64, bv_wrap.
  change (bv_modulus 64) with (2 ^ 64). apply Zplus_mod_idemp_l.
Qed.
Lemma jd_Ulit : forall E z, U E (SLit z) = z mod 2 ^ 64.
Proof. intros E z. rewrite U_SLit. reflexivity. Qed.
Lemma jd_sv : forall E e v, U E e = v mod 2 ^ 64 -> sv_denot E e = w64 v.
Proof.
  intros E e v H. apply bv_eq. unfold U in H. rewrite H, jd_w64, Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2 ^ 64). reflexivity.
Qed.
Lemma jd_unsigned : forall v, 0 <= v < 2 ^ 64 -> bv_unsigned (w64 v) = v.
Proof. intros v Hv. rewrite jd_w64. apply unsigned_lit_small. exact Hv. Qed.
Lemma jd_bz : forall b : byte, 0 <= bz b < 256.
Proof.
  intros b. unfold RcIdentModel.bz. pose proof (bv_unsigned_in_range 8 b) as Hb.
  change (bv_modulus 8) with 256 in Hb. exact Hb.
Qed.
Lemma jd_byte_of_bz : forall b : byte, Z_to_bv 8 (bz b) = b.
Proof. intros b. unfold RcIdentModel.bz. apply Z_to_bv_bv_unsigned. Qed.
(* A one-byte chunk of a region of the symbolic state is the byte in memory. *)
Lemma jd_val1 : forall E ss ms r n off e v,
  st_ok_pi SEGS VAL E ss ms -> In r (ss_mem ss) -> YP09.r_base r = Some n ->
  In (YP09.mkChunk off (CVal 1 e)) (YP09.r_chunks r) ->
  sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 8 ->
  mbyte SEGS (ms_mem ms) (bv_unsigned (ew E n) + off) = Some (Z_to_bv 8 v).
Proof.
  intros E ss ms r n off e v HS Hin Hb Hc He Hv.
  pose proof (st_ok_mem_ok SEGS E _ ms HS) as HM.
  pose proof (mem_ok_region SEGS E (ms_mem ms) _ r HM Hin) as (_ & _ & _ & Hcs).
  rewrite Hb in Hcs. cbn [base_val] in Hcs.
  pose proof (proj1 (Forall_forall _ _) Hcs _ Hc) as Hck.
  pose proof (val_of_chunk_ok SEGS E (ms_mem ms) _ off 1 e v Hck He Hv ltac:(lia) 0%nat ltac:(cbn; lia)) as Hvm.
  rewrite Z.add_0_r in Hvm. rewrite Hvm. f_equal.
  rewrite le_byte_small by (cbn; lia). change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r. reflexivity.
Qed.
(* An obligation of the token layer, from a range the caller knows addressable. *)
Lemma jd_ra : forall H (m : word -> option byte) E Bx x n a len p,
  U E Bx = SHADOW_OFF -> U E x = p ->
  range_addressable (aview SEGS H m) SHADOW_OFF a len -> a <= p -> p + n <= a + len ->
  range_addressable (rd_of SEGS (mrestrict H m)) (U E Bx) (U E x) n.
Proof.
  intros H m E Bx x n a len p HB Hx HR H1 H2. rewrite HB, Hx, <- (aview_rd_of SEGS).
  apply (range_addressable_sub _ _ a len); [exact HR | lia | lia].
Qed.
(* What the runs so far kept (KEEPI) and the presence they kept (GROWI). *)
Definition jd_kept (W : world SEGS) (Zs : Z -> Prop) (m0 m1 : word -> option byte) : Prop :=
  forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> aview SEGS (w_H W) m1 a = aview SEGS (w_H W) m0 a.
Definition jd_grown (W : world SEGS) (m0 m1 : word -> option byte) : Prop :=
  forall a, apresent (w_H W) m0 a -> apresent (w_H W) m1 a.
Lemma jd_keep_step : forall Ex rs (W : world SEGS) m0 m1 m2 (Zs : Z -> Prop),
  frame_of Ex rs (mrestrict (w_H W) m1) (mrestrict (w_H W) m2) ->
  mem_grows (mrestrict (w_H W) m1) (mrestrict (w_H W) m2) ->
  jd_kept W Zs m0 m1 -> jd_grown W m0 m1 ->
  (forall b wlo whi a, In (b, wlo, whi) (windows rs) -> base_val Ex b + wlo <= a < base_val Ex b + whi -> Zs a) ->
  jd_kept W Zs m0 m2 /\ jd_grown W m0 m2.
Proof.
  intros Ex rs W m0 m1 m2 Zs HFr HG K1 G1 Hw. split.
  - intros a Ha Hd. rewrite <- (K1 a Ha Hd).
    exact (kept_of_frame Ex rs (w_H W) m1 m2 Zs HFr Hw a Ha Hd).
  - intros a Hp. exact (apresent_grows _ _ _ a HG (G1 a Hp)).
Qed.
Lemma jd_agree_ext : forall regsL extra E E',
  env_agree 32 (Ereg regsL extra) E -> env_agree 32 E E' -> env_agree 32 (Ereg regsL extra) E'.
Proof.
  intros regsL extra E E' [H1 H2] [H3 H4]. split.
  - intros n Hn. rewrite (H3 n Hn). exact (H1 n Hn).
  - rewrite H4. exact H2.
Qed.
Lemma jd_consts : 0x7fff7f800000 <= alloc_ceiling <= 0x7fffff800000 /\ SHADOW_OFF = JD_SB.
Proof. pose proof asan_consts as (C1 & _). unfold SHADOW_OFF, JD_SB. lia. Qed.
(* A byte of the reader as a one-byte val_mem. *)
Lemma jd_vm_of_aview : forall H (m : word -> option byte) a v,
  aview SEGS H m a = Some v -> val_mem SEGS (mrestrict H m) a 1 v.
Proof.
  intros H m a v Hv. unfold aview in Hv.
  destruct (mbyte SEGS (mrestrict H m) a) as [b|] eqn:Hb; [|discriminate].
  cbn in Hv. injection Hv as <-.
  intros kk Hk. assert (kk = 0%nat) as -> by lia. rewrite Z.add_0_r, Hb. f_equal.
  pose proof (bv_unsigned_in_range 8 b) as Hr. change (bv_modulus 8) with 256 in Hr.
  rewrite le_byte_small by (cbn; lia). change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r.
  symmetry. apply Z_to_bv_bv_unsigned.
Qed.
(* Facts of a memory carried to one that agrees with it outside Zs. *)
Lemma jd_kept_trans : forall (W1 : world SEGS) (Z1 Z2 Z3 : Z -> Prop) m0 m1 m2,
  (forall a, Z1 a -> Z3 a) -> (forall a, Z2 a -> Z3 a) ->
  jd_kept W1 Z1 m0 m1 -> jd_kept W1 Z2 m1 m2 -> jd_kept W1 Z3 m0 m2.
Proof.
  intros W1 Z1 Z2 Z3 m0 m1 m2 H1 H2 K1 K2 a Ha Hn.
  rewrite (K2 a Ha (fun h => Hn (H2 a h))). exact (K1 a Ha (fun h => Hn (H1 a h))).
Qed.
Lemma jd_vm_kept : forall (W1 : world SEGS) (Zs : Z -> Prop) m0 m1 a n v, jd_kept W1 Zs m0 m1 ->
  (forall j, 0 <= j < Z.of_nat n -> 0 <= a + j < 2 ^ 64 /\ ~ Zs (a + j)) ->
  val_mem SEGS (mrestrict (w_H W1) m0) a n v -> val_mem SEGS (mrestrict (w_H W1) m1) a n v.
Proof.
  intros W1 Zs m0 m1 a n v HK HZ Hv. apply (val_mem_moved SEGS (w_H W1) (w_H W1) m0 m1 a a n v); [|exact Hv].
  intros j Hj. destruct (HZ j Hj) as [H1 H2]. exact (HK _ H1 H2).
Qed.
Lemma jd_ga_kept : forall (W1 : world SEGS) (Zs : Z -> Prop) m0 m1 a l, jd_kept W1 Zs m0 m1 ->
  (forall j, 0 <= j < Z.of_nat (length l) -> 0 <= a + j < 2 ^ 64 /\ ~ Zs (a + j)) ->
  garr8 SEGS (mrestrict (w_H W1) m0) a l -> garr8 SEGS (mrestrict (w_H W1) m1) a l.
Proof.
  intros W1 Zs m0 m1 a l HK HZ Hg. apply (j_garr8_moved SEGS (w_H W1) (w_H W1) m0 m1 a l); [|exact Hg].
  intros j Hj. destruct (HZ j Hj) as [H1 H2]. exact (HK _ H1 H2).
Qed.
Lemma jd_zs_kept : forall (W1 : world SEGS) (Zs : Z -> Prop) m0 m1 a n, jd_kept W1 Zs m0 m1 ->
  0 <= a -> 0 <= n -> a + n <= 2 ^ 47 -> (forall x, JD_SB <= x < JD_SB + 2 ^ 44 -> ~ Zs x) ->
  zero_shadow (aview SEGS (w_H W1) m0) SHADOW_OFF a n -> zero_shadow (aview SEGS (w_H W1) m1) SHADOW_OFF a n.
Proof.
  intros W1 Zs m0 m1 a n HK Ha Hn Han HZ Hz i Hi. unfold shadow_of_addr in *.
  rewrite HK; [exact (Hz i Hi) | unfold SHADOW_OFF; lia | apply HZ; unfold SHADOW_OFF, JD_SB; lia].
Qed.
Lemma jd_rad_kept : forall (W1 : world SEGS) (Zs : Z -> Prop) m0 m1 a n, jd_kept W1 Zs m0 m1 ->
  0 <= a -> a + n <= 2 ^ 47 -> (forall x, JD_SB <= x < JD_SB + 2 ^ 44 -> ~ Zs x) ->
  range_addressable (aview SEGS (w_H W1) m0) SHADOW_OFF a n ->
  range_addressable (aview SEGS (w_H W1) m1) SHADOW_OFF a n.
Proof.
  intros W1 Zs m0 m1 a n HK Ha Han HZ HR x Hx. destruct (HR x Hx) as (sv & Hs & Hok). exists sv.
  unfold shadow_of_addr in *.
  rewrite HK; [exact (conj Hs Hok) | unfold SHADOW_OFF; lia | apply HZ; unfold SHADOW_OFF, JD_SB; lia].
Qed.
(* A byte list written as reader bytes is bytes_at8's array. *)
Lemma jd_nth_map : forall (l : list byte) j, nth j (map (fun b : byte => bv_unsigned b) l) 0 = bz (nthb l j).
Proof.
  unfold RcIdentModel.nthb, RcIdentModel.bz.
  intros l; induction l as [|x l IH]; intros [|j]; cbn [map nth]; first [ apply IH | reflexivity ].
Qed.
Lemma jd_ga_of : forall H (m : word -> option byte) a (l : list byte),
  (forall j, (j < length l)%nat -> aview SEGS H m (a + Z.of_nat j) = Some (bz (nthb l j))) ->
  garr8 SEGS (mrestrict H m) a (map (fun b : byte => bv_unsigned b) l).
Proof.
  intros H m a l Hv j Hj. rewrite length_map in Hj. rewrite jd_nth_map.
  split; [apply jd_vm_of_aview; exact (Hv j Hj) | apply jd_bz].
Qed.
Lemma jd_ga_get : forall H (m : word -> option byte) a (l : list byte) j,
  garr8 SEGS (mrestrict H m) a (map (fun b : byte => bv_unsigned b) l) -> (j < length l)%nat ->
  aview SEGS H m (a + Z.of_nat j) = Some (bz (nthb l j)).
Proof.
  intros H m a l j Hg Hj. destruct (Hg j ltac:(rewrite length_map; exact Hj)) as [Hv _].
  rewrite jd_nth_map in Hv. pose proof (Hv 0%nat ltac:(lia)) as H0. rewrite Z.add_0_r in H0.
  unfold aview. rewrite H0. cbn [option_map]. f_equal.
  rewrite le_byte_small by (pose proof (jd_bz (nthb l j)); cbn; lia).
  change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r. rewrite jd_byte_of_bz. reflexivity.
Qed.
(* No shadow cell is a byte the piece writes. *)
Lemma jd_WS_sh : forall SF mf x, in_app SF 1024 -> alloc_ceiling + ASTACK <= mf ->
  JD_SB <= x < JD_SB + 2 ^ 44 -> ~ jd_WS SF mf x.
Proof.
  intros SF mf x [H0 H] Hmf Hx. pose proof jd_consts as (C1 & _).
  unfold jd_WS, ASTACK, JD_SB in *. unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in H. lia.
Qed.
End b.
End a.

(* After a run: chain its frame onto KEEPI / GROWI; every window of the run lies in the set KEEPI names. *)
Ltac jd_keep UH :=
  lazymatch goal with
  | HFr : frame_of _ _ (mrestrict _ _) (mrestrict _ _), HG : mem_grows _ _,
    KI : jd_kept _ _ _ _, GI : jd_grown _ _ _ |- _ =>
      let Hw := fresh "Hw" in
      pose proof (jd_keep_step _ _ _ _ _ _ _ HFr HG KI GI) as Hw;
      let K2 := fresh "K2" in let G2 := fresh "G2" in
      lazymatch type of Hw with ?P -> _ =>
        let HP := fresh "HP" in
        assert (HP : P);
        [ let bb := fresh "bb" in let wl := fresh "wl" in let wh := fresh "wh" in let aa := fresh "aa" in
          let Hin := fresh "Hin" in let Hr := fresh "Hr" in
          intros bb wl wh aa Hin Hr;
          lazymatch type of Hin with In _ (windows ?rs) =>
            let w := eval vm_compute in (windows rs) in change (windows rs) with w in Hin end;
          repeat (destruct Hin as [Hin | Hin];
                  [ injection Hin as <- <- <-; cbn [base_val] in Hr; jd_ewo_in Hr; rewrite ?UH in Hr; cbv beta; jd_lia | ]);
          destruct Hin
        | destruct (Hw HP) as [K2 G2]; clear HP Hw ] end;
      clear KI GI HFr HG; rename K2 into KEEPI; rename G2 into GROWI
  end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H end.
(* The writable windows of a run: the read-only regions have none, the one written region is in WR. *)
Ltac jd_awr UH WR :=
  lazymatch goal with |- awr_ok ?Ex ?rs ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?a7 =>
    let rs' := eval vm_compute in rs in change (awr_ok Ex rs' a1 a2 a3 a4 a5 a6 a7) end;
  repeat first
    [ apply awr_ok_nil
    | apply awr_ok_cons_ro; [cbn [YP09.r_whi YP09.r_wlo]; lia|]
    | eapply awr_ok_cons_gen;
        [ reflexivity | cbn [YP09.r_base]; jd_ewo; exact UH
        | cbn [YP09.r_wlo YP09.r_whi]; let a := fresh "a" in let Ha := fresh "Ha" in
          intros a Ha; apply (proj1 (WR a ltac:(jd_lia)))
        | ] ].
(* An obligation of the token layer: the range the run reads, from one the caller knows addressable. *)
Ltac jd_ob UB UX RA :=
  cbn [ms_mem mkst restrict]; eapply jd_ra; [exact UB | exact UX | exact RA | jd_lia | jd_lia].
(* The same, with the address U E (SOff n c) computed from the hypothesis ew E n = w64 v in the context. *)
Ltac jd_ux := erewrite jd_U by (jd_ewo; eassumption); rewrite Z.mod_small by jd_lia; reflexivity.
Ltac jd_ob2 UB RA :=
  cbn [ms_mem mkst restrict]; eapply jd_ra; [exact UB | jd_ux | exact RA | jd_lia | jd_lia].
(* sv_denot E e = w64 v for e a literal or an atom with offset 0. *)
Ltac jd_svv :=
  apply jd_sv; first [ rewrite jd_Ulit; reflexivity
                     | erewrite jd_U by (jd_ewo; eassumption); rewrite Z.add_0_r; reflexivity ].
(* The kept registers of the state a run stopped in, against the chunk's entry registers. *)
Ltac jd_kregs HS HAE regsL extra KL RK :=
  lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict _ ?ms) =>
    let HAE' := fresh "HAE'" in
    assert (HAE' : env_agree 32 (Ereg regsL extra) Ex)
      by (eapply jd_agree_ext; [exact HAE | split; [intros nn Hnn; jd_ewo; reflexivity | reflexivity]]);
    pose proof (regs_kept_of_st_ok_pi Ex ssx _ regsL extra KL HS HAE' ltac:(vm_compute; reflexivity)) as RK;
    cbn [ms_regs restrict] in RK; clear HAE'
  end.
(* The byte at offset off of the region of atom n in the state a run stopped in (a one-byte chunk), as v. *)
Ltac jd_byte HS n off v UH Md :=
  lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict _ ?ms) =>
    let rs := eval vm_compute in (ss_mem ssx) in
    lazymatch rs with context [YP09.mkRegion (Some n) ?lo ?hi ?wl ?wh ?cs] =>
      lazymatch cs with context [YP09.mkChunk off (CVal 1 ?e)] =>
        pose proof (jd_val1 Ex ssx _ (YP09.mkRegion (Some n) lo hi wl wh cs) n off e v HS
                      ltac:(change (ss_mem ssx) with rs; cbn [In]; repeat (first [left; reflexivity | right]))
                      eq_refl
                      ltac:(cbn [YP09.r_chunks In]; repeat (first [left; reflexivity | right]))
                      ltac:(jd_svv) ltac:(change (2 ^ 8) with 256; jd_lia)) as Md;
        cbn [ms_mem restrict] in Md; jd_ewo_in Md; rewrite UH in Md
      end
    end
  end.
(* A register of the state a run stopped in at a call (st_ok at the callee's address). *)
Ltac jd_reg2 HS r Hr :=
  lazymatch type of HS with
  | st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
      pose proof (st_ok_restrict_reg segs H E ss ms r HS) as Hr;
      let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
      cbn [ms_regs restrict mkst] in Hr
  end.
(* A register number is callee-saved. *)
Ltac jd_cs := unfold acallee_saved;
  lazymatch goal with |- context [bv_unsigned ?r] =>
    let z := eval vm_compute in (bv_unsigned r) in change (bv_unsigned r) with z end; lia.
(* A run whose regions write nothing. *)
Ltac jd_awr0 :=
  lazymatch goal with |- awr_ok ?Ex ?rs ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?a7 =>
    let rs' := eval vm_compute in rs in change (awr_ok Ex rs' a1 a2 a3 a4 a5 a6 a7) end;
  repeat first [ apply awr_ok_nil | apply awr_ok_cons_ro; [cbn [YP09.r_whi YP09.r_wlo]; lia|] ].

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Context {PI : PAImg ident_listing}.
#[local] Notation SEGS := (@pa_segs _ ident_listing PI).
#[local] Notation VAL := (@pa_val _ ident_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ ident_listing PI).
#[local] Notation BASE := (@pa_val _ ident_listing PI A_TEXT).
#[local] Notation bz := RcIdentModel.bz.
#[local] Notation nthb := RcIdentModel.nthb.
#[local] Notation zb := RcIdentModel.zb.
Section e.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis ABCMP : abcmp_realizes SEGS B (SIGMA IS___interceptor_trampoline_bcmp).
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

(* What the caller's journal allows at a byte: it is writable and there. *)
Lemma jd_wr_of : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W m md k q n,
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W m md k ->
  (forall a, q <= a < q + n -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a) ->
  jcut_wr B STK sp0 FP ly S lyc Sc own W m q n.
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W m md k q n HJm Hw a Ha.
  pose proof (Hw a Ha) as Hwa. split; [exact Hwa|].
  edestruct awr_byte_present as [Hp _].
  all: try exact Hp.
  all: first [exact HJm | exact Hwa | exact LAWS | exact pa_segs_low].
Qed.
Section g.
(* The caller's journal, fixed for the piece. *)
Variables (STK sp0 : Z) (FP own : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world SEGS)
  (mem0 : word -> option byte) (md0 : Model) (lyc : alayout) (Sc : astate) (W : world SEGS) (k : Z).
#[local] Notation AJ := (ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W).

Lemma jd_pres : forall (regs regs' : bvmap 5 word) (r : bv 5), aregs_preserved regs regs' ->
  acallee_saved (bv_unsigned r) -> getr regs' r = getr regs r.
Proof. intros regs regs' r H Hr. specialize (H _ Hr). rewrite Z_to_bv_bv_unsigned in H. exact H. Qed.
Lemma jd_br_ne : forall E n (v : word), ew E n = v ->
  branch_taken BC_NE (sv_denot E (SOff n 0)) (sv_denot E (SLit 0)) = true -> v <> w64 0.
Proof.
  intros E n v Hn Hb Hv. rewrite branch_ne_U in Hb. apply negb_true_iff, Z.eqb_neq in Hb. apply Hb.
  unfold U. cbn [sv_denot]. rewrite Hn, Z.add_0_r, Z_to_bv_bv_unsigned, Hv. reflexivity.
Qed.
Lemma jd_br_eq : forall E n (v : word), ew E n = v ->
  branch_taken BC_NE (sv_denot E (SOff n 0)) (sv_denot E (SLit 0)) = false -> v = w64 0.
Proof.
  intros E n v Hn Hb. rewrite branch_ne_U in Hb. apply negb_false_iff, Z.eqb_eq in Hb.
  unfold U in Hb. cbn [sv_denot] in Hb. rewrite Hn, Z.add_0_r, Z_to_bv_bv_unsigned in Hb.
  apply bv_eq. exact Hb.
Qed.
Lemma jd_kept_none : forall (W1 : world SEGS) (Zs : Z -> Prop) m0 m1,
  jd_kept W1 (fun _ => False) m0 m1 -> jd_kept W1 Zs m0 m1.
Proof. intros W1 Zs m0 m1 H a Ha _. exact (H a Ha (fun x => x)). Qed.
Lemma jd_amem : forall a n p m, in_app a n -> a <= p -> p + m <= a + n -> 0 <= m -> amem_range p m.
Proof.
  intros a n p m [H0 H] H1 H2 H3. pose proof jd_consts as (C1 & _).
  unfold amem_range, kLowMemEnd, kHighMemEnd, kHighMemBeg. unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in H. lia.
Qed.
Lemma jd_fk_cs : forall r, In r JD_FK -> acallee_saved (bv_unsigned r).
Proof.
  intros r Hr. unfold JD_FK in Hr. cbn [In] in Hr.
  repeat (destruct Hr as [Hr | Hr]; [subst r; jd_cs |]). destruct Hr.
Qed.
Lemma jd_fk_2 : forall r, In r JD_FK -> In r JD2_KEPT.
Proof. intros r Hr. unfold JD_FK, JD2_KEPT in *. cbn [In] in *. tauto. Qed.
Lemma jd_fk_3 : forall r, In r JD_FK -> In r JD3_KEPT.
Proof. intros r Hr. unfold JD_FK, JD3_KEPT in *. cbn [In] in *. tauto. Qed.
Lemma jd_fk_1 : forall r, In r JD_FK -> In r JD1_KEPT.
Proof. intros r Hr. unfold JD_FK, JD1_KEPT in *. cbn [In] in *. tauto. Qed.
Lemma jd_fk_4 : forall r, In r JD_FK -> In r JD4_KEPT.
Proof. intros r Hr. unfold JD_FK, JD4_KEPT in *. cbn [In] in *. tauto. Qed.
Lemma jd_fk_5 : forall r, In r JD_FK -> In r JD5_KEPT.
Proof. intros r Hr. unfold JD_FK, JD5_KEPT in *. cbn [In] in *. tauto. Qed.
Lemma jd_fk_s : forall r, In r JD_FK -> In r [2; 3; 4; 8; 9; 17; 18; 19; 20; 21; 22; 23; 24; 26; 27]%bv.
Proof. intros r Hr. unfold JD_FK in *. cbn [In] in *. tauto. Qed.
(* A shadow cell of an application byte below 2^47 lies in the shadow band. *)
Lemma jd_sh_band : forall x, 0 <= x < 2 ^ 47 -> JD_SB <= shadow_of_addr SHADOW_OFF x < JD_SB + 2 ^ 44.
Proof.
  intros x Hx. unfold shadow_of_addr, SHADOW_OFF, JD_SB.
  assert (0 <= x / 8 < 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]). lia.
Qed.

(* The memory after one store of the byte v at d. *)
Definition jd_mem1 (d v : Z) (m m' : word -> option byte) : Prop :=
  (forall a, 0 <= a < 2 ^ 64 -> a <> d -> aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a) /\
  aview SEGS (w_H W) m' d = Some v /\
  (forall a, apresent (w_H W) m a -> apresent (w_H W) m' a).

(* ---- 0x81ab4 .. 0x81b00 (or 0x81b84 for an empty stem) ------------------------------------------------------- *)
Lemma jd_d1 : forall (mf w4A stemA nmA b0 : Z) (regsL : bvmap 5 word) memL mdL (Q : world SEGS -> config -> Prop),
  AJ memL mdL k ->
  getr regsL 9 = w64 mf -> getr regsL 18 = w64 w4A -> getr regsL 23 = w64 stemA -> getr regsL 26 = w64 nmA ->
  alloc_ceiling + ASTACK <= mf <= 2 ^ 47 ->
  4096 <= w4A -> w4A + 8 <= alloc_ceiling -> in_app w4A 8 -> w4A mod 8 = 0 ->
  4096 <= stemA -> stemA + 1 <= alloc_ceiling -> (stemA + 1 <= w4A + 4 \/ w4A + 5 <= stemA) ->
  4096 <= nmA -> nmA + 32 <= alloc_ceiling -> 0 <= b0 < 256 ->
  val_mem SEGS (mrestrict (w_H W) memL) (mf + 176) 8 SHADOW_OFF ->
  val_mem SEGS (mrestrict (w_H W) memL) (mf + 208) 8 4 ->
  val_mem SEGS (mrestrict (w_H W) memL) stemA 1 b0 ->
  zero_shadow (aview SEGS (w_H W) memL) SHADOW_OFF w4A 8 ->
  range_addressable (aview SEGS (w_H W) memL) SHADOW_OFF stemA 1 ->
  jcut_wr B STK sp0 FP ly S lyc Sc own W memL (w4A + 4) 1 ->
  (forall regs' mem' md', AJ mem' md' k ->
     (forall r, In r JD1_KEPT -> getr regs' r = getr regsL r) -> jd_mem1 (w4A + 4) 0 memL mem' ->
     getr regs' 17 = w64 SHADOW_OFF -> getr regs' 25 = w64 0 -> b0 <> 0 ->
     getr regs' 11 = w64 nmA -> getr regs' 10 = w64 (nmA - 4) -> getr regs' 12 = w64 (stemA + 1) ->
     getr regs' 13 = w64 b0 ->
     SRr SEGS W (cfg_at SEGS (BASE + 0x13f4) regs' mem' md') Q) ->
  (forall regs' mem' md', AJ mem' md' k ->
     (forall r, In r JD1_KEPT -> getr regs' r = getr regsL r) -> jd_mem1 (w4A + 4) 0 memL mem' ->
     getr regs' 17 = w64 SHADOW_OFF -> getr regs' 25 = w64 0 -> b0 = 0 ->
     SRr SEGS W (cfg_at SEGS (BASE + 0x1478) regs' mem' md') Q) ->
  SRr SEGS W (cfg_at SEGS (BASE + 0x13a8) regsL memL mdL) Q.
Proof.
  intros mf w4A stemA nmA b0 regsL memL mdL Q HJ R9 R18 R23 R26 Hmf Hw0 Hw1 Hwapp Hw8 Hs0 Hs1 Hsw Hn0 Hn1 Hb0
    V176 V208 Vst ZW RAst WR K1 K2.
  pose proof jd_consts as (C1 & C2). unfold ASTACK in Hmf.
  remember (Eimg (Ereg regsL [w64 b0; w64 SHADOW_OFF])) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regsL [w64 b0; w64 SHADOW_OFF]) n)
    by (intros n Hn; subst E; apply Eimg_low; exact Hn).
  assert (E9 : ew E 9 = w64 mf)
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsL _ 9 9%bv eq_refl); exact R9).
  assert (E18 : ew E 18 = w64 w4A)
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsL _ 18 18%bv eq_refl); exact R18).
  assert (E23 : ew E 23 = w64 stemA)
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsL _ 23 23%bv eq_refl); exact R23).
  assert (E26 : ew E 26 = w64 nmA)
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsL _ 26 26%bv eq_refl); exact R26).
  assert (E32 : ew E 32 = w64 b0) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsL _ 0)).
  assert (E33 : ew E 33 = w64 SHADOW_OFF) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsL _ 1)).
  assert (HAE : env_agree 32 (Ereg regsL [w64 b0; w64 SHADOW_OFF]) E)
    by (split; [intros n Hn; apply EL; unfold A_TEXT; lia | subst E; reflexivity]).
  assert (VB : forall n v, ew E n = w64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v)
    by (intros n v Hn Hv; cbn [base_val]; rewrite Hn; apply jd_unsigned; exact Hv).
  assert (WRa : forall a, w4A + 4 <= a < w4A + 5 ->
            awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a /\ apresent (w_H W) memL a)
    by (intros a Ha; apply WR; lia).
  assert (HS : st_ok_pi SEGS VAL E ss_jd1
                 (restrict (w_H W) (mkst regsL (Z_to_bv 64 (BASE + 0x13a8)) memL (seg_rom SEGS)))).
  { rewrite restrict_mkst_fx. unfold ss_jd1. apply pa_entry_st_ok_full.
    - rewrite HE. apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - unfold jd1_regions. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
      + rewrite (VB 9%nat mf E9) by jd_lia.
        split; [jd_lia|]. split; [jd_lia|]. split; [intros o Ho; lia|].
        constructor; [|constructor; [|constructor]].
        * apply (chunk_ok_val SEGS E _ mf 176 8 (SOff 33 0) SHADOW_OFF).
          -- apply jd_sv. rewrite (jd_U E 33 _ 0 E33), Z.add_0_r. reflexivity.
          -- rewrite C2. unfold JD_SB. cbn. lia.
          -- cbn. lia.
          -- exact V176.
        * apply (chunk_ok_val SEGS E _ mf 208 8 (SLit 4) 4).
          -- apply jd_sv. rewrite jd_Ulit. reflexivity.
          -- cbn. lia.
          -- cbn. lia.
          -- exact V208.
      + rewrite (VB 18%nat w4A E18) by jd_lia.
        split; [jd_lia|]. split; [jd_lia|]. split; [|apply Forall_nil].
        intros o Ho. apply (apresent_writable SEGS). apply (proj2 (WRa (w4A + o) ltac:(jd_lia))).
      + rewrite (VB 23%nat stemA E23) by jd_lia.
        split; [jd_lia|]. split; [jd_lia|]. split; [intros o Ho; lia|].
        constructor; [|constructor].
        apply (chunk_ok_val SEGS E _ stemA 0 1 (SOff 32 0) b0).
        -- apply jd_sv. rewrite (jd_U E 32 _ 0 E32), Z.add_0_r. reflexivity.
        -- change (2 ^ (8 * Z.of_N 1)) with 256. lia.
        -- cbn. lia.
        -- rewrite Z.add_0_r. exact Vst.
    - apply pairwise_disjoint_of_extents. unfold jd1_regions, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
      rewrite (VB 9%nat mf E9) by (unfold ASTACK in *; jd_lia).
      rewrite (VB 18%nat w4A E18), (VB 23%nat stemA E23) by jd_lia.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. jd_clean.
      unfold ASTACK in *. repeat split; lia.
    - split; [|split; exact I].
      cbn [jd1_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite E33, E32, E18, E23, E26. rewrite !jd_unsigned by (rewrite ?C2; unfold JD_SB; jd_lia).
      rewrite !Z.pow_0_r, !Z.mod_1_r. rewrite C2. jd_clean. unfold JD_SB, jd_A47. repeat split; lia. }
  assert (UB : U E jd1_Bx = SHADOW_OFF).
  { unfold jd1_Bx. rewrite (jd_U E 33 SHADOW_OFF 0 E33), Z.add_0_r. apply Z.mod_small. rewrite C2. unfold JD_SB. lia. }
  assert (SHOK : sh_ok SEGS jd1_Bx SH_jd1 E (mrestrict (w_H W) memL)).
  { unfold sh_ok, SH_jd1. apply Forall_cons; [|apply Forall_nil].
    apply (shent_app_of_app SEGS E jd1_Bx 18%nat w4A 4 5).
    - exact UB.
    - rewrite (jd_U E 18 w4A 0 E18), Z.add_0_r. apply Z.mod_small. jd_lia.
    - destruct Hwapp as [Ha1 [Ha2 | [Ha2 Ha3]]]; [left | right]; unfold kLowShadowBeg, kHighMemBeg in *; lia.
    - lia. }
  assert (U18 : bv_unsigned (ew E 18) = w4A) by (rewrite E18; apply jd_unsigned; jd_lia).
  assert (UX18 : U E (SOff 18 4) = w4A + 4) by (rewrite (jd_U E 18 w4A 4 E18); apply Z.mod_small; jd_lia).
  assert (UX23 : U E (SOff 23 0) = stemA) by (rewrite (jd_U E 23 stemA 0 E23), Z.add_0_r; apply Z.mod_small; jd_lia).
  assert (RAw : range_addressable (aview SEGS (w_H W) memL) SHADOW_OFF w4A 8)
    by (apply zero_shadow_range; [exact Hw8 | reflexivity | exact ZW]).
  assert (KEEPI : jd_kept W (fun a => a = w4A + 4) memL memL) by (intros a _ _; reflexivity).
  assert (GROWI : jd_grown W memL memL) by (intros a Ha; exact Ha).
  clear HE EL.
  unfold cfg_at. rewrite jd_w64.
  (* 0x81ab4 .. 0x81aec: the two loads of mf, the shadow test of w4 + 4 and its store, the stem's shadow test and
     the load of stem[0]; the run stops at the beqz on it *)
  paj_run_tok RUN HS HJ SHOK jd_Bspan.
  all: try (jd_ob UB UX18 RAw).
  all: try (jd_ob UB UX23 RAst).
  all: try (jd_awr U18 WRa).
  jd_keep U18.
  psrr_branch_tok RUN BR HS SHOK jd_Bspan.
  - (* stem[0] = 0: 0x81b80 s9 := 0, to 0x81b84 *)
    assert (Hz : b0 = 0).
    { rewrite branch_eq_U in Hc. rewrite (jd_U _ 32%nat b0 0) in Hc by (jd_ewo; exact E32).
      rewrite jd_Ulit in Hc. apply Z.eqb_eq in Hc. rewrite Z.add_0_r, !Z.mod_small in Hc by jd_lia. exact Hc. }
    clear Hc.
    paj_run_to_tok RUNTO HS HJ SHOK jd_Bspan 0x1478; [jd_awr U18 WRa|].
    jd_keep U18.
    pmkst HS.
    jd_kregs HS HAE regsL [w64 b0; w64 SHADOW_OFF] JD1_KEPT RK.
    jd_reg HS (17%bv : bv 5) Q17. jd_reg HS (25%bv : bv 5) Q25.
    jd_byte HS 18%nat 4 0 U18 Md.
    apply K2; [assumption | exact RK | | | | exact Hz].
    + split; [intros a Ha Hne; exact (KEEPI a Ha Hne)|]. split; [|exact GROWI].
      unfold aview. rewrite Md. reflexivity.
    + rewrite Q17. apply jd_sv. rewrite (jd_U _ 33%nat SHADOW_OFF 0) by (jd_ewo; exact E33). reflexivity.
    + rewrite Q25. apply jd_sv. rewrite jd_Ulit. reflexivity.
  - (* stem[0] <> 0: on to the loop head 0x81b00 *)
    assert (Hz : b0 <> 0).
    { rewrite branch_eq_U in Hc. rewrite (jd_U _ 32%nat b0 0) in Hc by (jd_ewo; exact E32).
      rewrite jd_Ulit in Hc. apply Z.eqb_neq in Hc. rewrite Z.add_0_r, !Z.mod_small in Hc by jd_lia. exact Hc. }
    clear Hc.
    paj_run_to_tok RUNTO HS HJ SHOK jd_Bspan 0x13f4; [jd_awr U18 WRa|].
    jd_keep U18.
    pmkst HS.
    jd_kregs HS HAE regsL [w64 b0; w64 SHADOW_OFF] JD1_KEPT RK.
    jd_reg HS (17%bv : bv 5) Q17. jd_reg HS (25%bv : bv 5) Q25. jd_reg HS (11%bv : bv 5) Q11.
    jd_reg HS (10%bv : bv 5) Q10. jd_reg HS (12%bv : bv 5) Q12. jd_reg HS (13%bv : bv 5) Q13.
    jd_byte HS 18%nat 4 0 U18 Md.
    apply K1; [assumption | exact RK | | | | exact Hz | | | |].
    + split; [intros a Ha Hne; exact (KEEPI a Ha Hne)|]. split; [|exact GROWI].
      unfold aview. rewrite Md. reflexivity.
    + rewrite Q17. apply jd_sv. rewrite (jd_U _ 33%nat SHADOW_OFF 0) by (jd_ewo; exact E33). reflexivity.
    + rewrite Q25. apply jd_sv. rewrite jd_Ulit. reflexivity.
    + rewrite Q11. apply jd_sv. rewrite (jd_U _ 26%nat nmA 0) by (jd_ewo; exact E26). f_equal; lia.
    + rewrite Q10. apply jd_sv. rewrite (jd_U _ 26%nat nmA (-4)) by (jd_ewo; exact E26). f_equal; lia.
    + rewrite Q12. apply jd_sv. rewrite (jd_U _ 23%nat stemA 1) by (jd_ewo; exact E23). reflexivity.
    + rewrite Q13. apply jd_sv. rewrite (jd_U _ 32%nat b0 0) by (jd_ewo; exact E32). f_equal; lia.
Qed.

(* ---- 0x81c1c .. 0x81c34: exp_nm[s9] = 0 --------------------------------------------------------------------- *)
Lemma jd_d5 : forall (nmA L : Z) (regsL : bvmap 5 word) memL mdL (Q : world SEGS -> config -> Prop),
  AJ memL mdL k ->
  getr regsL 26 = w64 nmA -> getr regsL 25 = w64 L -> getr regsL 17 = w64 SHADOW_OFF ->
  4096 <= nmA -> nmA + 32 <= alloc_ceiling -> in_app nmA 32 -> nmA mod 8 = 0 -> 0 <= L < 32 ->
  zero_shadow (aview SEGS (w_H W) memL) SHADOW_OFF nmA 32 ->
  jcut_wr B STK sp0 FP ly S lyc Sc own W memL (nmA + L) 1 ->
  (forall regs' mem' md', AJ mem' md' k ->
     (forall r, In r JD5_KEPT -> getr regs' r = getr regsL r) -> jd_mem1 (nmA + L) 0 memL mem' ->
     SRr SEGS W (cfg_at SEGS (BASE + 0x1528) regs' mem' md') Q) ->
  SRr SEGS W (cfg_at SEGS (BASE + 0x1510) regsL memL mdL) Q.
Proof.
  intros nmA L regsL memL mdL Q HJ R26 R25 R17 Hn0 Hn1 Hnapp Hn8 HL ZN WR K.
  pose proof jd_consts as (C1 & C2).
  remember (Eimg (Ereg regsL [w64 (nmA + L)])) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regsL [w64 (nmA + L)]) n)
    by (intros n Hn; subst E; apply Eimg_low; exact Hn).
  assert (E17 : ew E 17 = w64 SHADOW_OFF)
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsL _ 17 17%bv eq_refl); exact R17).
  assert (E25 : ew E 25 = w64 L)
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsL _ 25 25%bv eq_refl); exact R25).
  assert (E26 : ew E 26 = w64 nmA)
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsL _ 26 26%bv eq_refl); exact R26).
  assert (E32 : ew E 32 = w64 (nmA + L)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsL _ 0)).
  assert (HAE : env_agree 32 (Ereg regsL [w64 (nmA + L)]) E)
    by (split; [intros n Hn; apply EL; unfold A_TEXT; lia | subst E; reflexivity]).
  assert (VB : forall n v, ew E n = w64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v)
    by (intros n v Hn Hv; cbn [base_val]; rewrite Hn; apply jd_unsigned; exact Hv).
  assert (WRa : forall a, nmA + L <= a < nmA + L + 1 ->
            awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a /\ apresent (w_H W) memL a)
    by (intros a Ha; apply WR; lia).
  assert (HS : st_ok_pi SEGS VAL E ss_jd5
                 (restrict (w_H W) (mkst regsL (Z_to_bv 64 (BASE + 0x1510)) memL (seg_rom SEGS)))).
  { rewrite restrict_mkst_fx. unfold ss_jd5. apply pa_entry_st_ok_full.
    - rewrite HE. apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
      rewrite (VB 32%nat (nmA + L) E32) by jd_lia.
      split; [jd_lia|]. split; [jd_lia|]. split; [|apply Forall_nil].
      intros o Ho. apply (apresent_writable SEGS). apply (proj2 (WRa (nmA + L + o) ltac:(jd_lia))).
    - cbn [pairwise_disjoint all_disjoint]. split; exact I.
    - split; [|split; [exact I|]].
      + cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
        rewrite E17, E26, E25, E32. rewrite !jd_unsigned by (rewrite ?C2; unfold JD_SB; jd_lia).
        rewrite !Z.pow_0_r, !Z.mod_1_r. rewrite C2. jd_clean. unfold JD_SB, jd_A47. repeat split; lia.
      + cbn [f_alias alias_ok]. split; [|exact I].
        rewrite (jd_sv E (SOff 32 0) (nmA + L)) by (rewrite (jd_U E 32 _ 0 E32), Z.add_0_r; reflexivity).
        apply jd_sv. rewrite U_SAlu. cbn [zalu_raw].
        rewrite (jd_U E 26 nmA 0 E26), (jd_U E 25 L 0 E25), !Z.add_0_r. unfold zcanon, M64.
        rewrite <- Zplus_mod. reflexivity. }
  assert (UB : U E jd_Bx17 = SHADOW_OFF).
  { unfold jd_Bx17. rewrite (jd_U E 17 SHADOW_OFF 0 E17), Z.add_0_r. apply Z.mod_small. rewrite C2. unfold JD_SB. lia. }
  assert (SHOK : sh_ok SEGS jd_Bx17 SH_jd5 E (mrestrict (w_H W) memL)).
  { unfold sh_ok, SH_jd5. apply Forall_cons; [|apply Forall_nil].
    apply (shent_app_of_app SEGS E jd_Bx17 32%nat (nmA + L) 0 1).
    - exact UB.
    - rewrite (jd_U E 32 _ 0 E32), Z.add_0_r. apply Z.mod_small. jd_lia.
    - destruct Hnapp as [Ha1 [Ha2 | [Ha2 Ha3]]]; [left | right]; unfold kLowShadowBeg, kHighMemBeg in *; lia.
    - lia. }
  assert (U32 : bv_unsigned (ew E 32) = nmA + L) by (rewrite E32; apply jd_unsigned; jd_lia).
  assert (RAn : range_addressable (aview SEGS (w_H W) memL) SHADOW_OFF nmA 32)
    by (apply zero_shadow_range; [exact Hn8 | reflexivity | exact ZN]).
  assert (KEEPI : jd_kept W (fun a => a = nmA + L) memL memL) by (intros a _ _; reflexivity).
  assert (GROWI : jd_grown W memL memL) by (intros a Ha; exact Ha).
  clear HE EL.
  unfold cfg_at. rewrite jd_w64.
  paj_run_to_tok RUNTO HS HJ SHOK jd_Bspan 0x1528.
  all: try (jd_ob2 UB RAn).
  all: try (jd_awr U32 WRa).
  jd_keep U32.
  pmkst HS.
  jd_kregs HS HAE regsL [w64 (nmA + L)] JD5_KEPT RK.
  jd_byte HS 32%nat 0 0 U32 Md. rewrite Z.add_0_r in Md.
  apply K; [assumption | exact RK |].
  split; [intros a Ha Hne; exact (KEEPI a Ha Hne)|]. split; [|exact GROWI].
  unfold aview. rewrite Md. reflexivity.
Qed.

(* ---- 0x81b84 .. 0x81c1c: exp_nm[ln] = '-' and the four bytes of w4 after it ------------------------------- *)
Lemma jd_d4 : forall (nmA w4A L : Z) (wl : list byte) (regsL : bvmap 5 word) memL mdL (Q : world SEGS -> config -> Prop),
  AJ memL mdL k ->
  getr regsL 26 = w64 nmA -> getr regsL 25 = w64 L -> getr regsL 17 = w64 SHADOW_OFF -> getr regsL 18 = w64 w4A ->
  4096 <= nmA -> nmA + 32 <= alloc_ceiling -> in_app nmA 32 -> nmA mod 8 = 0 -> 0 <= L <= 16 ->
  4096 <= w4A -> w4A + 8 <= alloc_ceiling -> w4A mod 8 = 0 -> (nmA + 32 <= w4A \/ w4A + 8 <= nmA) ->
  (forall j, (j < 4)%nat -> 48 <= bz (nthb wl j) <= 57) ->
  (forall j, (j < 4)%nat -> aview SEGS (w_H W) memL (w4A + Z.of_nat j) = Some (bz (nthb wl j))) ->
  aview SEGS (w_H W) memL (w4A + 4) = Some 0 ->
  zero_shadow (aview SEGS (w_H W) memL) SHADOW_OFF nmA 32 ->
  zero_shadow (aview SEGS (w_H W) memL) SHADOW_OFF w4A 8 ->
  jcut_wr B STK sp0 FP ly S lyc Sc own W memL (nmA + L) 5 ->
  (forall regs' mem' md', AJ mem' md' k ->
     (forall r, In r JD4_KEPT -> getr regs' r = getr regsL r) -> getr regs' 25 = w64 (L + 5) ->
     jd_kept W (fun a => nmA + L <= a < nmA + L + 5) memL mem' ->
     aview SEGS (w_H W) mem' (nmA + L) = Some 45 ->
     (forall j, (j < 4)%nat -> aview SEGS (w_H W) mem' (nmA + L + 1 + Z.of_nat j) = Some (bz (nthb wl j))) ->
     SRr SEGS W (cfg_at SEGS (BASE + 0x1510) regs' mem' md') Q) ->
  SRr SEGS W (cfg_at SEGS (BASE + 0x1478) regsL memL mdL) Q.
Proof.
  intros nmA w4A L wl regsL memL mdL Q HJ R26 R25 R17 R18 Hn0 Hn1 Hnapp Hn8 HL Hw0 Hw1 Hw8 Hnw HD WB W4z ZN ZW WR K.
  pose proof jd_consts as (C1 & C2).
  pose proof (HD 0%nat ltac:(lia)) as D0. pose proof (HD 1%nat ltac:(lia)) as D1.
  pose proof (HD 2%nat ltac:(lia)) as D2. pose proof (HD 3%nat ltac:(lia)) as D3.
  set (x := [w64 (nmA + L); w64 (bz (nthb wl 0)); w64 (bz (nthb wl 1)); w64 (bz (nthb wl 2)); w64 (bz (nthb wl 3))]).
  remember (Eimg (Ereg regsL x)) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regsL x) n)
    by (intros n Hn; subst E; apply Eimg_low; exact Hn).
  assert (E17 : ew E 17 = w64 SHADOW_OFF)
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsL _ 17 17%bv eq_refl); exact R17).
  assert (E18 : ew E 18 = w64 w4A)
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsL _ 18 18%bv eq_refl); exact R18).
  assert (E25 : ew E 25 = w64 L)
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsL _ 25 25%bv eq_refl); exact R25).
  assert (E26 : ew E 26 = w64 nmA)
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsL _ 26 26%bv eq_refl); exact R26).
  assert (E32 : ew E 32 = w64 (nmA + L)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsL _ 0)).
  assert (E33 : ew E 33 = w64 (bz (nthb wl 0))) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsL _ 1)).
  assert (E34 : ew E 34 = w64 (bz (nthb wl 1))) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsL _ 2)).
  assert (E35 : ew E 35 = w64 (bz (nthb wl 2))) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsL _ 3)).
  assert (E36 : ew E 36 = w64 (bz (nthb wl 3))) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsL _ 4)).
  assert (HAE : env_agree 32 (Ereg regsL x) E)
    by (split; [intros n Hn; apply EL; unfold A_TEXT; lia | subst E; reflexivity]).
  assert (VB : forall n v, ew E n = w64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v)
    by (intros n v Hn Hv; cbn [base_val]; rewrite Hn; apply jd_unsigned; exact Hv).
  assert (WRa : forall a, nmA + L <= a < nmA + L + 5 ->
            awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a /\ apresent (w_H W) memL a)
    by (intros a Ha; apply WR; lia).
  assert (HS : st_ok_pi SEGS VAL E ss_jd4
                 (restrict (w_H W) (mkst regsL (Z_to_bv 64 (BASE + 0x1478)) memL (seg_rom SEGS)))).
  { rewrite restrict_mkst_fx. unfold ss_jd4. apply pa_entry_st_ok_full.
    - rewrite HE. apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - unfold jd4_regions. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
      + rewrite (VB 32%nat (nmA + L) E32) by jd_lia.
        split; [jd_lia|]. split; [jd_lia|]. split; [|apply Forall_nil].
        intros o Ho. apply (apresent_writable SEGS). apply (proj2 (WRa (nmA + L + o) ltac:(jd_lia))).
      + rewrite (VB 18%nat w4A E18) by jd_lia.
        split; [jd_lia|]. split; [jd_lia|]. split; [intros o Ho; lia|].
        repeat apply Forall_cons; try apply Forall_nil.
        * apply (chunk_ok_val SEGS E _ w4A 0 1 (SOff 33 0) (bz (nthb wl 0))); [jd_svv | cbn; lia | cbn; lia |].
          apply jd_vm_of_aview. exact (WB 0%nat ltac:(lia)).
        * apply (chunk_ok_val SEGS E _ w4A 1 1 (SOff 34 0) (bz (nthb wl 1))); [jd_svv | cbn; lia | cbn; lia |].
          apply jd_vm_of_aview. exact (WB 1%nat ltac:(lia)).
        * apply (chunk_ok_val SEGS E _ w4A 2 1 (SOff 35 0) (bz (nthb wl 2))); [jd_svv | cbn; lia | cbn; lia |].
          apply jd_vm_of_aview. exact (WB 2%nat ltac:(lia)).
        * apply (chunk_ok_val SEGS E _ w4A 3 1 (SOff 36 0) (bz (nthb wl 3))); [jd_svv | cbn; lia | cbn; lia |].
          apply jd_vm_of_aview. exact (WB 3%nat ltac:(lia)).
        * apply (chunk_ok_val SEGS E _ w4A 4 1 (SLit 0) 0); [jd_svv | cbn; lia | cbn; lia |].
          apply jd_vm_of_aview. exact W4z.
    - apply pairwise_disjoint_of_extents. unfold jd4_regions, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
      rewrite (VB 32%nat (nmA + L) E32), (VB 18%nat w4A E18) by jd_lia.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. jd_clean. repeat split; lia.
    - split; [|split; [exact I|]].
      + cbn [jd4_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
        rewrite E17, E26, E25, E18, E32, E33, E34, E35, E36.
        rewrite !jd_unsigned by (rewrite ?C2; unfold JD_SB; jd_lia).
        rewrite !Z.pow_0_r, !Z.mod_1_r. rewrite C2. jd_clean. unfold JD_SB, jd_A47. repeat split; lia.
      + cbn [jd4_facts f_alias alias_ok]. split; [|exact I].
        rewrite (jd_sv E (SOff 32 0) (nmA + L)) by (rewrite (jd_U E 32 _ 0 E32), Z.add_0_r; reflexivity).
        apply jd_sv. rewrite U_SAlu. cbn [zalu_raw].
        rewrite (jd_U E 26 nmA 0 E26), (jd_U E 25 L 0 E25), !Z.add_0_r. unfold zcanon, M64.
        rewrite <- Zplus_mod. reflexivity. }
  assert (UB : U E jd_Bx17 = SHADOW_OFF).
  { unfold jd_Bx17. rewrite (jd_U E 17 SHADOW_OFF 0 E17), Z.add_0_r. apply Z.mod_small. rewrite C2. unfold JD_SB. lia. }
  assert (SHOK : sh_ok SEGS jd_Bx17 SH_jd4 E (mrestrict (w_H W) memL)).
  { unfold sh_ok, SH_jd4. apply Forall_cons; [|apply Forall_nil].
    apply (shent_app_of_app SEGS E jd_Bx17 32%nat (nmA + L) 0 5).
    - exact UB.
    - rewrite (jd_U E 32 _ 0 E32), Z.add_0_r. apply Z.mod_small. jd_lia.
    - destruct Hnapp as [Ha1 [Ha2 | [Ha2 Ha3]]]; [left | right]; unfold kLowShadowBeg, kHighMemBeg in *; lia.
    - lia. }
  assert (U32 : bv_unsigned (ew E 32) = nmA + L) by (rewrite E32; apply jd_unsigned; jd_lia).
  assert (RAn : range_addressable (aview SEGS (w_H W) memL) SHADOW_OFF nmA 32)
    by (apply zero_shadow_range; [exact Hn8 | reflexivity | exact ZN]).
  assert (RAw : range_addressable (aview SEGS (w_H W) memL) SHADOW_OFF w4A 8)
    by (apply zero_shadow_range; [exact Hw8 | reflexivity | exact ZW]).
  assert (KEEPI : jd_kept W (fun a => nmA + L <= a < nmA + L + 5) memL memL) by (intros a _ _; reflexivity).
  assert (GROWI : jd_grown W memL memL) by (intros a Ha; exact Ha).
  clear HE EL.
  unfold cfg_at. rewrite jd_w64.
  (* the whole append runs through: the branches on the digits of w4 and on w4[4] = 0 are decided by the facts *)
  paj_run_to_tok RUNTO HS HJ SHOK jd_Bspan 0x1510.
  all: try (jd_ob2 UB RAn).
  all: try (jd_ob2 UB RAw).
  all: try (jd_awr U32 WRa).
  jd_keep U32.
  pmkst HS.
  jd_kregs HS HAE regsL x JD4_KEPT RK.
  jd_reg HS (25%bv : bv 5) Q25.
  jd_byte HS 32%nat 0 45 U32 M0. jd_byte HS 32%nat 1 (bz (nthb wl 0)) U32 M1.
  jd_byte HS 32%nat 2 (bz (nthb wl 1)) U32 M2. jd_byte HS 32%nat 3 (bz (nthb wl 2)) U32 M3.
  jd_byte HS 32%nat 4 (bz (nthb wl 3)) U32 M4.
  apply K; [assumption | exact RK | | exact KEEPI | |].
  - rewrite Q25. apply jd_sv. rewrite (jd_U _ 25%nat L 5) by (jd_ewo; exact E25). reflexivity.
  - rewrite Z.add_0_r in M0. unfold aview. rewrite M0. reflexivity.
  - intros j Hj. destruct j as [|[|[|[|j]]]]; [| | | | lia].
    + replace (nmA + L + 1 + Z.of_nat 0) with (nmA + L + 1) by lia.
      unfold aview. rewrite M1. cbn [option_map]. rewrite jd_byte_of_bz. reflexivity.
    + replace (nmA + L + 1 + Z.of_nat 1) with (nmA + L + 2) by lia.
      unfold aview. rewrite M2. cbn [option_map]. rewrite jd_byte_of_bz. reflexivity.
    + replace (nmA + L + 1 + Z.of_nat 2) with (nmA + L + 3) by lia.
      unfold aview. rewrite M3. cbn [option_map]. rewrite jd_byte_of_bz. reflexivity.
    + replace (nmA + L + 1 + Z.of_nat 3) with (nmA + L + 4) by lia.
      unfold aview. rewrite M4. cbn [option_map]. rewrite jd_byte_of_bz. reflexivity.
Qed.

(* ---- 0x81b74 .. 0x81b7c: the return of bcmp, a7 reloaded, the branch on its result ------------------------- *)
Lemma jd_d3 : forall (mf : Z) (v : word) (regsL : bvmap 5 word) memL mdL (Q : world SEGS -> config -> Prop),
  AJ memL mdL k ->
  getr regsL 9 = w64 mf -> getr regsL 10 = v -> alloc_ceiling + ASTACK <= mf <= 2 ^ 47 ->
  val_mem SEGS (mrestrict (w_H W) memL) (mf + 176) 8 SHADOW_OFF ->
  (forall regs' mem' md', AJ mem' md' k ->
     (forall r, In r JD3_KEPT -> getr regs' r = getr regsL r) -> getr regs' 17 = w64 SHADOW_OFF ->
     jd_kept W (fun _ => False) memL mem' -> v <> w64 0 ->
     SRr SEGS W (cfg_at SEGS (BASE + 0x1478) regs' mem' md') Q) ->
  (forall regs' mem' md', AJ mem' md' k ->
     (forall r, In r JD3_KEPT -> getr regs' r = getr regsL r) -> getr regs' 17 = w64 SHADOW_OFF ->
     jd_kept W (fun _ => False) memL mem' -> v = w64 0 ->
     SRr SEGS W (cfg_at SEGS (BASE + 0x1510) regs' mem' md') Q) ->
  SRr SEGS W (cfg_at SEGS (BASE + 0x1468) regsL memL mdL) Q.
Proof.
  intros mf v regsL memL mdL Q HJ R9 R10 Hmf V176 K1 K2.
  pose proof jd_consts as (C1 & C2). unfold ASTACK in Hmf.
  remember (Eimg (Ereg regsL [w64 SHADOW_OFF])) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regsL [w64 SHADOW_OFF]) n)
    by (intros n Hn; subst E; apply Eimg_low; exact Hn).
  assert (E9 : ew E 9 = w64 mf)
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsL _ 9 9%bv eq_refl); exact R9).
  assert (E10 : ew E 10 = v)
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsL _ 10 10%bv eq_refl); exact R10).
  assert (E32 : ew E 32 = w64 SHADOW_OFF) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsL _ 0)).
  assert (HAE : env_agree 32 (Ereg regsL [w64 SHADOW_OFF]) E)
    by (split; [intros n Hn; apply EL; unfold A_TEXT; lia | subst E; reflexivity]).
  assert (VB : forall n v, ew E n = w64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v)
    by (intros n v' Hn Hv; cbn [base_val]; rewrite Hn; apply jd_unsigned; exact Hv).
  assert (HS : st_ok_pi SEGS VAL E ss_jd3
                 (restrict (w_H W) (mkst regsL (Z_to_bv 64 (BASE + 0x1468)) memL (seg_rom SEGS)))).
  { rewrite restrict_mkst_fx. unfold ss_jd3. apply pa_entry_st_ok_full.
    - rewrite HE. apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
      rewrite (VB 9%nat mf E9) by jd_lia.
      split; [jd_lia|]. split; [jd_lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ mf 176 8 (SOff 32 0) SHADOW_OFF);
        [jd_svv | rewrite C2; unfold JD_SB; cbn; lia | cbn; lia | exact V176].
    - cbn [pairwise_disjoint all_disjoint]. split; exact I.
    - split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite E32. rewrite !jd_unsigned by (rewrite ?C2; unfold JD_SB; jd_lia).
      rewrite !Z.pow_0_r, !Z.mod_1_r. rewrite C2. unfold JD_SB. repeat split; lia. }
  assert (SHOK : sh_ok SEGS (SOff 32 0) [] E (mrestrict (w_H W) memL)) by constructor.
  assert (U9 : bv_unsigned (ew E 9) = mf) by (rewrite E9; apply jd_unsigned; jd_lia).
  assert (KEEPI : jd_kept W (fun _ => False) memL memL) by (intros a _ _; reflexivity).
  assert (GROWI : jd_grown W memL memL) by (intros a Ha; exact Ha).
  clear HE EL.
  unfold cfg_at. rewrite jd_w64.
  paj_run_tok RUN HS HJ SHOK jd_Bspan.
  all: try jd_awr0.
  jd_keep U9.
  psrr_branch_tok RUN BR HS SHOK jd_Bspan.
  - (* the bytes differ: append, 0x81b84 *)
    pose proof (jd_br_ne _ 10%nat v ltac:(jd_ewo; exact E10) Hc) as Hv. clear Hc.
    paj_run_to_tok RUNTO HS HJ SHOK jd_Bspan 0x1478; [jd_awr0|].
    jd_keep U9. pmkst HS.
    jd_kregs HS HAE regsL [w64 SHADOW_OFF] JD3_KEPT RK.
    jd_reg HS (17%bv : bv 5) Q17.
    apply K1; [assumption | exact RK | | exact KEEPI | exact Hv].
    rewrite Q17. jd_svv.
  - (* exp_nm ends in w4: 0x81c1c *)
    pose proof (jd_br_eq _ 10%nat v ltac:(jd_ewo; exact E10) Hc) as Hv. clear Hc.
    paj_run_to_tok RUNTO HS HJ SHOK jd_Bspan 0x1510; [jd_awr0|].
    jd_keep U9. pmkst HS.
    jd_kregs HS HAE regsL [w64 SHADOW_OFF] JD3_KEPT RK.
    jd_reg HS (17%bv : bv 5) Q17.
    apply K2; [assumption | exact RK | | exact KEEPI | exact Hv].
    rewrite Q17. jd_svv.
Qed.

(* ---- 0x81b60 .. 0x81b70: |stem| < 4, or the call bcmp(exp_nm + |stem| - 4, w4, 4) --------------------------- *)
Lemma jd_d2 : forall (mf o nmA w4A L cid pos : Z) (regsL : bvmap 5 word) memL mdL (Q : world SEGS -> config -> Prop),
  AJ memL mdL k ->
  getr regsL 2 = w64 mf -> getr regsL 9 = w64 mf -> getr regsL 3 = w64 (as_gp B) -> getr regsL 4 = w64 (as_tp B) ->
  getr regsL 25 = w64 L -> getr regsL 10 = w64 (nmA + L - 4) -> getr regsL 18 = w64 w4A ->
  getr regsL 17 = w64 SHADOW_OFF ->
  mf = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 2 * ESTACK - o <= STK ->
  alloc_ceiling + ASTACK <= mf <= 2 ^ 47 ->
  4096 <= nmA -> nmA + 32 <= alloc_ceiling -> in_app nmA 32 -> nmA mod 8 = 0 ->
  4096 <= w4A -> w4A + 8 <= alloc_ceiling -> in_app w4A 8 -> w4A mod 8 = 0 -> 0 <= L <= 16 ->
  In (cid, pos) (frames Sc) ->
  frame_addr lyc cid pos <= nmA -> nmA + 32 <= frame_addr lyc cid pos + fs_frame_bytes cid ->
  frame_addr lyc cid pos <= w4A -> w4A + 8 <= frame_addr lyc cid pos + fs_frame_bytes cid ->
  val_mem SEGS (mrestrict (w_H W) memL) (mf + 176) 8 SHADOW_OFF ->
  zero_shadow (aview SEGS (w_H W) memL) SHADOW_OFF nmA 32 ->
  zero_shadow (aview SEGS (w_H W) memL) SHADOW_OFF w4A 8 ->
  (forall a, nmA <= a < nmA + 32 -> aview SEGS (w_H W) memL a <> None) ->
  (forall a, w4A <= a < w4A + 4 -> aview SEGS (w_H W) memL a <> None) ->
  (forall regs' mem' md', AJ mem' md' k ->
     (forall r, In r JD_FK -> getr regs' r = getr regsL r) ->
     getr regs' 17 = w64 SHADOW_OFF -> getr regs' 25 = w64 L -> getr regs' 18 = w64 w4A ->
     jd_kept W (fun a => mf - 2 * ESTACK <= a < mf) memL mem' ->
     (L < 4 \/ ~ (forall i, 0 <= i < 4 ->
                    aview SEGS (w_H W) memL (nmA + L - 4 + i) = aview SEGS (w_H W) memL (w4A + i))) ->
     SRr SEGS W (cfg_at SEGS (BASE + 0x1478) regs' mem' md') Q) ->
  (forall regs' mem' md', AJ mem' md' k ->
     (forall r, In r JD_FK -> getr regs' r = getr regsL r) ->
     getr regs' 17 = w64 SHADOW_OFF -> getr regs' 25 = w64 L ->
     jd_kept W (fun a => mf - 2 * ESTACK <= a < mf) memL mem' ->
     4 <= L -> (forall i, 0 <= i < 4 ->
                  aview SEGS (w_H W) memL (nmA + L - 4 + i) = aview SEGS (w_H W) memL (w4A + i)) ->
     SRr SEGS W (cfg_at SEGS (BASE + 0x1510) regs' mem' md') Q) ->
  SRr SEGS W (cfg_at SEGS (BASE + 0x1454) regsL memL mdL) Q.
Proof.
  intros mf o nmA w4A L cid pos regsL memL mdL Q HJ R2 R9 R3 R4 R25 R10 R18 R17 Hmo Ho16 Ho0 Hob Hmf
    Hn0 Hn1 Hnapp Hn8 Hw0 Hw1 Hwapp Hw8 HL Hfr HF0 HF1 HF2 HF3 V176 ZN ZW PN PW Kapp Kfin.
  pose proof jd_consts as (C1 & C2). unfold ASTACK in Hmf.
  remember (Eimg (Ereg regsL [])) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regsL []) n)
    by (intros n Hn; subst E; apply Eimg_low; exact Hn).
  assert (E9 : ew E 9 = w64 mf)
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsL _ 9 9%bv eq_refl); exact R9).
  assert (E18 : ew E 18 = w64 w4A)
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsL _ 18 18%bv eq_refl); exact R18).
  assert (E25 : ew E 25 = w64 L)
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsL _ 25 25%bv eq_refl); exact R25).
  assert (HAE : env_agree 32 (Ereg regsL []) E)
    by (split; [intros n Hn; apply EL; unfold A_TEXT; lia | subst E; reflexivity]).
  assert (HS : st_ok_pi SEGS VAL E ss_jd2
                 (restrict (w_H W) (mkst regsL (Z_to_bv 64 (BASE + 0x1454)) memL (seg_rom SEGS)))).
  { rewrite restrict_mkst_fx. unfold ss_jd2. apply pa_entry_st_ok_full.
    - rewrite HE. apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - apply Forall_nil.
    - exact I.
    - split; [exact I | split; exact I]. }
  assert (SHOK : sh_ok SEGS jd_Bx17 [] E (mrestrict (w_H W) memL)) by constructor.
  assert (U9 : bv_unsigned (ew E 9) = mf) by (rewrite E9; apply jd_unsigned; jd_lia).
  assert (KEEPI : jd_kept W (fun a => mf - 2 * ESTACK <= a < mf) memL memL) by (intros a _ _; reflexivity).
  assert (GROWI : jd_grown W memL memL) by (intros a Ha; exact Ha).
  clear HE EL.
  unfold cfg_at. rewrite jd_w64.
  paj_run_tok RUN HS HJ SHOK jd_Bspan.
  all: try jd_awr0.
  jd_keep U9.
  psrr_branch_tok RUN BR HS SHOK jd_Bspan.
  - (* |stem| < 4: on to 0x81b84 *)
    assert (HL4 : L < 4).
    { rewrite branch_ltu_U in Hc. rewrite (jd_U _ 25%nat L 0) in Hc by (jd_ewo; exact E25). rewrite jd_Ulit in Hc.
      apply Z.ltb_lt in Hc. rewrite Z.add_0_r, !Z.mod_small in Hc by jd_lia. exact Hc. }
    clear Hc.
    paj_run_to_tok RUNTO HS HJ SHOK jd_Bspan 0x1478; [jd_awr0|].
    jd_keep U9. pmkst HS.
    jd_kregs HS HAE regsL (@nil word) JD2_KEPT RK.
    apply Kapp; [assumption | intros r Hr; exact (RK r (jd_fk_2 r Hr))
                | rewrite RK by (cbn; tauto); exact R17 | rewrite RK by (cbn; tauto); exact R25
                | rewrite RK by (cbn; tauto); exact R18 | exact KEEPI | left; exact HL4].
  - (* |stem| >= 4: the call of the bcmp wrapper *)
    assert (HL4 : 4 <= L).
    { rewrite branch_ltu_U in Hc. rewrite (jd_U _ 25%nat L 0) in Hc by (jd_ewo; exact E25). rewrite jd_Ulit in Hc.
      apply Z.ltb_ge in Hc. rewrite Z.add_0_r, !Z.mod_small in Hc by jd_lia. exact Hc. }
    clear Hc.
    paj_run_tok RUN HS HJ SHOK jd_Bspan.
    all: try jd_awr0.
    jd_keep U9.
    lazymatch goal with HS : st_ok _ ?Ex ?ssx (restrict _ ?ms) |- _ =>
      assert (HAEc : env_agree 32 (Ereg regsL []) Ex)
        by (eapply jd_agree_ext; [exact HAE | split; [intros nn Hnn; jd_ewo; reflexivity | reflexivity]]);
      pose proof (regs_kept_of_st_ok SEGS Ex ssx _ regsL [] JD2_KEPT HS HAEc ltac:(vm_compute; reflexivity)) as RKc;
      cbn [ms_regs restrict] in RKc; rename ms into msc
    end.
    jd_reg2 HS (11%bv : bv 5) Q11. jd_reg2 HS (12%bv : bv 5) Q12. prreg HS (1%bv : bv 5) Q1.
    pmkst HS.
    pose proof HJ as (HARc & _).
    assert (KM : forall a, 0 <= a < 2 ^ 64 -> ~ (mf - 2 * ESTACK <= a < mf) ->
              aview SEGS (w_H W) (ms_mem msc) a = aview SEGS (w_H W) memL a) by exact KEEPI.
    assert (Hsp : spZ (ms_regs msc) = mf)
      by (unfold spZ; rewrite RKc by (cbn; tauto); rewrite R2; apply jd_unsigned; jd_lia).
    assert (ZNc : zero_shadow (aview SEGS (w_H W) (ms_mem msc)) SHADOW_OFF nmA 32).
    { intros i Hi. change (32 / 8) with 4 in Hi. pose proof (jd_sh_band nmA ltac:(jd_lia)) as Hb.
      rewrite KM; [exact (ZN i ltac:(change (32 / 8) with 4; lia)) | unfold JD_SB in Hb; lia | unfold ESTACK, JD_SB in *; lia]. }
    assert (ZWc : zero_shadow (aview SEGS (w_H W) (ms_mem msc)) SHADOW_OFF w4A 8).
    { intros i Hi. change (8 / 8) with 1 in Hi. pose proof (jd_sh_band w4A ltac:(jd_lia)) as Hb.
      rewrite KM; [exact (ZW i ltac:(change (8 / 8) with 1; lia)) | unfold JD_SB in Hb; lia | unfold ESTACK, JD_SB in *; lia]. }
    eapply SRr_bind.
    { eapply (aj_bcmp_at SEGS B LAWS pa_segs_low (SIGMA IS___interceptor_trampoline_bcmp) ABCMP W
        (ms_regs msc) (ms_mem msc) STK sp0 FP ly S W0 mem0 md0 own lyc Sc _ k (nmA + L - 4) w4A 4 o
        (Z_to_bv 64 (BASE + 0x1468)) HJ).
      - rewrite RKc by (cbn; tauto). exact R10.
      - rewrite Q11. jd_svv.
      - rewrite Q12. jd_svv.
      - lia.
      - jd_lia.
      - unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hnapp. jd_lia.
      - jd_lia.
      - unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hwapp. jd_lia.
      - rewrite Hsp. exact Hmo.
      - exact Ho16.
      - exact Ho0.
      - exact Hob.
      - rewrite RKc by (cbn; tauto). exact R3.
      - rewrite RKc by (cbn; tauto). exact R4.
      - rewrite Q1. reflexivity.
      - apply ret_ok_codeptr_v; [lia | reflexivity].
      - intros a Ha. rewrite Hsp. split; [rewrite KM by (unfold ESTACK; jd_lia); apply PN; lia | unfold ESTACK; jd_lia].
      - intros a Ha. rewrite Hsp. split; [rewrite KM by (unfold ESTACK; jd_lia); apply PW; lia | unfold ESTACK; jd_lia].
      - intros a Ha. rewrite <- Hmo. unfold ESTACK. jd_lia.
      - intros a Ha. rewrite <- Hmo. unfold ESTACK. jd_lia.
      - apply (jd_amem nmA 32); [exact Hnapp | lia | lia | lia].
      - apply (jd_amem w4A 8); [exact Hwapp | lia | lia | lia].
      - apply (range_addressable_sub _ _ nmA 32); [apply zero_shadow_range; [exact Hn8 | reflexivity | exact ZNc] | lia | lia].
      - intros _. eapply (shadow_hull_vis_of_frame SEGS B LAWS lyc Sc W (ms_mem msc)); [exact HARc | exact Hfr | lia | lia | lia].
      - apply (range_addressable_sub _ _ w4A 8); [apply zero_shadow_range; [exact Hw8 | reflexivity | exact ZWc] | lia | lia].
      - intros _. eapply (shadow_hull_vis_of_frame SEGS B LAWS lyc Sc W (ms_mem msc)); [exact HARc | exact Hfr | lia | lia | lia]. }
    intros W2 c2 _ (-> & regs2 & mem2 & md2 & v & -> & HJ2 & HP2 & Hv & Hcmp & Hfr2 & Hpres2).
    rewrite <- Hmo in Hfr2.
    assert (KM2 : forall a, 0 <= a < 2 ^ 64 -> ~ (mf - 2 * ESTACK <= a < mf) ->
              aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memL a)
      by (intros a Ha Hna; rewrite (Hfr2 a Ha Hna); exact (KM a Ha Hna)).
    assert (RP : forall r, In r JD_FK -> getr regs2 r = getr regsL r).
    { intros r Hr. rewrite (jd_pres _ _ r HP2 (jd_fk_cs r Hr)). exact (RKc r (jd_fk_2 r Hr)). }
    apply (jd_d3 mf v regs2 mem2 md2 Q HJ2).
    + rewrite (jd_pres _ _ 9%bv HP2) by jd_cs. rewrite RKc by (cbn; tauto). exact R9.
    + exact Hv.
    + unfold ASTACK. lia.
    + apply (val_mem_moved SEGS (w_H W) (w_H W) memL mem2 (mf + 176) (mf + 176) 8 SHADOW_OFF); [|exact V176].
      intros kk Hk. apply KM2; unfold ESTACK; jd_lia.
    + intros regs' mem' md' HJ' RK3 Q17 KP3 Hv0.
      apply Kapp; [exact HJ' | | exact Q17 | | | | right].
      * intros r Hr. rewrite (RK3 r (jd_fk_3 r Hr)). exact (RP r Hr).
      * rewrite (RK3 25%bv) by (cbn; tauto). rewrite (jd_pres _ _ 25%bv HP2) by jd_cs.
        rewrite RKc by (cbn; tauto). exact R25.
      * rewrite (RK3 18%bv) by (cbn; tauto). rewrite (jd_pres _ _ 18%bv HP2) by jd_cs.
        rewrite RKc by (cbn; tauto). exact R18.
      * intros a Ha Hna. rewrite (KP3 a Ha (fun x => x)). exact (KM2 a Ha Hna).
      * intros Hall. apply Hv0. apply Hcmp. intros i Hi.
        rewrite !KM by (unfold ESTACK; jd_lia). apply Hall. exact Hi.
    + intros regs' mem' md' HJ' RK3 Q17 KP3 Hv0.
      apply Kfin; [exact HJ' | | exact Q17 | | | exact HL4 |].
      * intros r Hr. rewrite (RK3 r (jd_fk_3 r Hr)). exact (RP r Hr).
      * rewrite (RK3 25%bv) by (cbn; tauto). rewrite (jd_pres _ _ 25%bv HP2) by jd_cs.
        rewrite RKc by (cbn; tauto). exact R25.
      * intros a Ha Hna. rewrite (KP3 a Ha (fun x => x)). exact (KM2 a Ha Hna).
      * intros i Hi. pose proof (proj1 Hcmp Hv0 i Hi) as Hq.
        rewrite !KM in Hq by (unfold ESTACK; jd_lia). exact Hq.
Qed.

End g.
End e.
End d.
End c.

(* ---- the piece ------------------------------------------------------------------------------------------------ *)
Section ma. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section mb.
Context {PI : PAImg ident_listing}.
#[local] Notation SEGS := (@pa_segs _ ident_listing PI).
#[local] Notation VAL := (@pa_val _ ident_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ ident_listing PI).
#[local] Notation bz := RcIdentModel.bz.
#[local] Notation nthb := RcIdentModel.nthb.
#[local] Notation zb := RcIdentModel.zb.
#[local] Notation BASE := (@pa_val _ ident_listing PI A_TEXT).
Section mc.
#[local] Notation rd W mem := (mrestrict (w_H W) mem).
(* The Section of LLVMFuzzerTestOneInput.v / _inv.v, in the same order. *)
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Variables RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB : Z.
Variable asink_syms_T : Type.
Variable KS : asink_syms_T.
Variable asink_none : list Segment -> asink_syms_T -> (word -> option byte) -> Model -> Prop.
Variable ameta_inv : list Segment -> asink_syms_T -> alayout -> (word -> option byte) -> Z -> Prop.
Variable arodata_okS : list Segment -> asyms -> Z -> Z -> reader -> Prop.
#[local] Notation ACUT := (acut B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS).
#[local] Notation ECOMMON := (ecommon B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS).
#[local] Notation HBLOCKS := (hblocks B).

(* ---- what the piece takes, each as the contract's Section states it (LLVMFuzzerTestOneInput.v) ------------- *)
Hypothesis HSTK : STK_LLVMF <= LLVMF_STK.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis MTL : ameter_laws MT.
Hypothesis HMT0 : forall s s' : astate, mo_le MT s s' 0.
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
Hypothesis HRO : forall rdr, arodata_okS SEGS B RLO RHI rdr -> arodata_okP SEGS pa_relro_lo pa_relro_hi B rdr.
Variable G : list (Z * Z).
Hypothesis GM : globs_marked SEGS B G.
Hypothesis G_IN : In (VAL (A_OBJ 9), 7) G.
Hypothesis G_OUT : In (VAL (A_OBJ 10), 6) G.
Hypothesis G_REAC : In (VAL (A_OBJ 8), 5) G.
Hypothesis HIMG : forall (W : world SEGS) mem,
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) -> llvmf_img B G W mem.
Hypothesis PSIG : ident_prog_sig_ok (PI := PI).
Hypothesis HPD : put_dec.tput_dec_spec B.
Hypothesis ABCMP : abcmp_realizes SEGS B (SIGMA IS___interceptor_trampoline_bcmp).
Hypothesis AMEMCHR : amemchr_realizes SEGS B (SIGMA IS___interceptor_trampoline_memchr).
Hypothesis AJ_NIL_IO : forall STK sp0 ly S (W : world SEGS) mem md own ly' S' W' mem' md' k,
  ajournal SEGS B STK sp0 [] ly S W mem md own ly' S' W' mem' md' k ->
  m_fds md' = m_fds md /\ m_fs md' = m_fs md.

(* ---- the shared layer of segment J (LLVMFuzzerTestOneInput_Jcut.v), at this Section's variables ------------ *)
#[local] Notation jcut := (LLVMFuzzerTestOneInput_Jcut.jcut B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB
  LIVE_LIB asink_syms_T KS asink_none ameta_inv arodata_okS).
#[local] Notation jc := (LLVMFuzzerTestOneInput_Jcut.jc B).
#[local] Notation jcut_mk := (LLVMFuzzerTestOneInput_Jcut.jcut_mk B MT XM_LIB XN_LIB RLO RHI RA_LLVMF A_EMPTY
  LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS asink_none ameta_inv arodata_okS MTL HMT0).
#[local] Notation AJg g pos ly2 S2 W2 m md := (ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g)
  (e_mem g) (e_md g) [(4, pos)] ly2 S2 W2 m md (4 * Z.of_nat (m_nrec g) + 7)).

(* 0x81ab4 .. 0x81c34: from the state after the two put_dec calls (Pj2) to exp_nm[ln] = 0 (Pj3). *)
Theorem j_D : j_D_stmt B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS asink_none
  ameta_inv arodata_okS.
Proof.
unfold j_D_stmt.
intros g pos mf nm tk dp W2 c2 Hc.
destruct Hc as (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ & Hfrs & HK & MLE & MOK & HC & HJC & HP).
pose proof HP as (Hwok & R27 & R26 & R24 & R18 & (stemA & R23 & Hst) & HW4 & Vn1 & Vn2 & ZN & ZD & ZW).
pose proof Hst as (Hs16 & Hsnz & Hsb & Hsra & Hsbey & Hsapp & Hs0 & Hs1 & HsWJ).
pose proof HC as (Rsp & Rs1 & Rs0 & Hmfb & Hmf32 & Rgp & Rtp & Rs3 & V80 & V192 & V176 & _).
pose proof (proj1 HJC) as (Hmf0 & Hsp47 & Hsp16 & HSF0 & HSF1 & HSFapp & HSF64 & _).
pose proof jd_consts as (C1 & C2).
pose proof HJ as (HAR2 & Hly2 & _).
pose proof Hly2 as (_ & _ & _ & _ & _ & EF & _).
assert (EFa : frame_addr ly2 4 pos = SFa g pos) by (unfold SFa, frame_addr; rewrite EF; reflexivity).
assert (Hin4 : In (4, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
destruct (JDModel.W4_props (e_pl g) Hwok) as (HW4l & HW4d).
unfold V_nm, V_dp, V_w4, M_n1, M_n2, N_nm, N_dp, N_w4, sh_zero, bytes_at8 in *.
unfold ASTACK in Hmf0.
set (SF := SFa g pos) in *. assert (HSFd : SF = SFa g pos) by reflexivity. clearbody SF.
set (s := SlotModel.n_stem (e_pl g)) in *. assert (Hs_def : s = SlotModel.n_stem (e_pl g)) by reflexivity.
clearbody s.
set (wl := SlotModel.n_W4 (e_pl g)) in *. assert (Hwl_def : wl = SlotModel.n_W4 (e_pl g)) by reflexivity.
clearbody wl.
set (K0 := 4 * Z.of_nat (m_nrec g) + 7) in *.
assert (Hnapp : in_app (SF + 528) 32) by (apply (in_app_sub SF 1024); [exact HSFapp | lia | lia | lia]).
assert (Hwapp : in_app (SF + 688) 8) by (apply (in_app_sub SF 1024); [exact HSFapp | lia | lia | lia]).
assert (Hsl : (0 <= Z.of_nat (length s) <= 16)) by lia.
(* the stem lies apart from exp_nm .. w4: segment J writes none of its bytes *)
assert (Hsep : stemA + Z.of_nat (length s) + 1 <= SF + 528 \/ SF + 696 <= stemA).
{ destruct (Z.le_gt_cases (stemA + Z.of_nat (length s) + 1) (SF + 528)) as [H|H]; [left; exact H|].
  destruct (Z.le_gt_cases (SF + 696) stemA) as [H'|H']; [right; exact H'|].
  exfalso. apply (HsWJ (Z.max stemA (SF + 528))); [lia|]. unfold WJ. rewrite <- HSFd. right; right; left; lia. }
(* the bytes of the side frame are the caller's own *)
assert (WRF : forall a, SF <= a < SF + 1024 ->
  awr_byte LLVMF_STK (e_sp0 g) [] (ablocks B (e_ly g) (e_S g)) (ablocks B ly2 S2) ly2 [(4, pos)] a).
{ intros a Ha. right; right; right. exists 4, pos. split; [left; reflexivity|]. left. unfold in_zr. cbn [fst snd].
  rewrite EFa. change (fs_frame_bytes 4) with 1024. lia. }
assert (HZS : forall x, JD_SB <= x < JD_SB + 2 ^ 44 -> ~ jd_WS SF mf x)
  by (intros x Hx; apply jd_WS_sh; [exact HSFapp | unfold ASTACK; lia | exact Hx]).
assert (WRJ : forall m md q n, AJg g pos ly2 S2 W2 m md -> SF <= q -> q + n <= SF + 1024 ->
  jcut_wr B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) ly2 S2 [(4, pos)] W2 m q n).
{ intros m md q n HJm Hq1 Hq2.
  apply (jd_wr_of B LAWS LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)] ly2 S2 W2
           m md K0 q n HJm).
  intros a Ha. apply WRF. lia. }
(* ---- the end: jcut_mk from the start state ---- *)
assert (KF : forall regsF memF mdF,
  AJg g pos ly2 S2 W2 memF mdF ->
  (forall r, In r JD_FK -> getr regsF r = getr regs2 r) ->
  getr regsF 25 = w64 (SlotModel.n_ln (e_pl g)) -> getr regsF 17 = w64 SHADOW_OFF ->
  jd_kept W2 (jd_WS SF mf) mem2 memF ->
  (forall j, (j < length (SlotModel.n_EXP_NM (e_pl g) ++ [zb 0]))%nat ->
     aview SEGS (w_H W2) memF (SF + 528 + Z.of_nat j) = Some (bz (nthb (SlotModel.n_EXP_NM (e_pl g) ++ [zb 0]) j))) ->
  SRr SEGS W2 (cfg_at SEGS (BASE + 0x1528) regsF memF mdF) (jcut g pos mf nm tk dp (BASE + 0x1528) (Pj3 g pos mf))).
{ intros regsF memF mdF HJF RKF R25F R17F KPF BYF.
  apply SRr_ret.
  destruct (AJ_NIL_IO _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as [D1 D2].
  destruct (AJ_NIL_IO _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJF) as [D3 D4].
  apply (jcut_mk g pos mf nm tk dp (BASE + 0x1528) (Pj3 g pos mf) ly2 S2 W2 regs2 mem2 md2 ly2 S2 W2 regsF memF mdF
    HJ Hfrs HK MLE MOK HC HJC HJF Hfrs (Permutation_refl _)).
  - intros a Ha HnW. apply KPF; [exact Ha|]. intros Hws. apply HnW. unfold WJ. rewrite <- HSFd.
    unfold jd_WS in Hws. destruct Hws as [Hw | [Hw | Hw]]; [right; right; left; lia | right; right; left; lia | left; lia].
  - intros r Hr. apply RKF. revert Hr. unfold JD_FK. cbn [In]. tauto.
  - intros fd. rewrite D3, D1. reflexivity.
  - rewrite D4, D2. reflexivity.
  - unfold Pj3. rewrite <- HSFd. unfold V_nm, V_dp, M_n2, N_nm, N_dp, sh_zero, bytes_at8.
    refine (conj Hwok _).
    split; [rewrite RKF by jd_inl; exact R27|].
    split; [rewrite RKF by jd_inl; exact R26|].
    split; [rewrite RKF by jd_inl; exact R24|].
    split; [exact R25F|]. split; [exact R17F|].
    split; [apply JDModel.EXP_len; [rewrite <- Hs_def; exact Hs16 | rewrite <- Hwl_def; exact HW4l]|].
    split; [apply jd_ga_of; exact BYF|].
    split.
    { apply (jd_vm_kept W2 (jd_WS SF mf) mem2 memF (mf + 200) 8 0 KPF); [|exact Vn2].
      intros j Hj. cbn [Z.of_nat Pos.of_succ_nat] in Hj. split; jd_lia. }
    split.
    { apply (jd_zs_kept W2 (jd_WS SF mf) mem2 memF (SF + 528) 32 KPF); [lia | lia | lia | exact HZS | exact ZN]. }
    apply (jd_zs_kept W2 (jd_WS SF mf) mem2 memF (SF + 592) 64 KPF); [lia | lia | lia | exact HZS | exact ZD]. }
(* ---- exp_nm ends in w4: exp_nm[ln] = 0 at once (0x81c1c) ---- *)
assert (KE : forall regs' mem' md',
  AJg g pos ly2 S2 W2 mem' md' ->
  (forall r, In r JD_FK -> getr regs' r = getr regs2 r) ->
  getr regs' 17 = w64 SHADOW_OFF -> getr regs' 25 = w64 (Z.of_nat (length s)) ->
  jd_kept W2 (jd_WS SF mf) mem2 mem' ->
  (forall j, (j < length s)%nat -> aview SEGS (w_H W2) mem' (SF + 528 + Z.of_nat j) = Some (bz (nthb s j))) ->
  SlotModel.n_ends_w4 (e_pl g) = true ->
  SRr SEGS W2 (cfg_at SEGS (BASE + 0x1510) regs' mem' md') (jcut g pos mf nm tk dp (BASE + 0x1528) (Pj3 g pos mf))).
{ intros regs' mem' md' HJ' RK Q17 Q25 KP BY Hend.
  assert (EXPe : SlotModel.n_EXP_NM (e_pl g) = s)
    by (unfold SlotModel.n_EXP_NM; rewrite Hend; exact (eq_sym Hs_def)).
  apply (jd_d5 B LAWS LLVMF_STK (e_sp0 g) [] [(4, pos)] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) ly2 S2 W2 K0
           (SF + 528) (Z.of_nat (length s)) regs' mem' md' _ HJ').
  - rewrite RK by jd_inl. exact R26.
  - exact Q25.
  - exact Q17.
  - lia.
  - lia.
  - exact Hnapp.
  - lia.
  - lia.
  - apply (jd_zs_kept W2 (jd_WS SF mf) mem2 mem' (SF + 528) 32 KP); [lia | lia | lia | exact HZS | exact ZN].
  - apply (WRJ _ md' _ _ HJ'); lia.
  - intros regsF memF mdF HJF RK5 KM5. apply KF; [exact HJF | | | | |].
    + intros r Hr. rewrite (RK5 r (jd_fk_5 r Hr)). exact (RK r Hr).
    + rewrite RK5 by jd_inl. rewrite Q25. unfold SlotModel.n_ln. rewrite EXPe. reflexivity.
    + rewrite RK5 by jd_inl. exact Q17.
    + apply (jd_kept_trans W2 (jd_WS SF mf) (fun a => a = SF + 528 + Z.of_nat (length s)) (jd_WS SF mf)
               mem2 mem' memF); [tauto | intros a Ha; unfold jd_WS; right; left; lia | exact KP | exact (proj1 KM5)].
    + rewrite EXPe. intros j Hj. rewrite length_app in Hj. cbn [length] in Hj.
      rewrite (JDModel.nth_app0 s j ltac:(lia)).
      destruct (Nat.ltb_spec j (length s)) as [H1|H1].
      * rewrite (proj1 KM5) by jd_lia. exact (BY j H1).
      * assert (j = length s) by lia. subst j. exact (proj1 (proj2 KM5)). }
(* ---- exp_nm[ln] = '-' and w4 appended, then exp_nm[ln] = 0 (0x81b84) ---- *)
assert (KA : forall regs' mem' md',
  AJg g pos ly2 S2 W2 mem' md' ->
  (forall r, In r JD_FK -> getr regs' r = getr regs2 r) ->
  getr regs' 17 = w64 SHADOW_OFF -> getr regs' 25 = w64 (Z.of_nat (length s)) -> getr regs' 18 = w64 (SF + 688) ->
  jd_kept W2 (jd_WS SF mf) mem2 mem' ->
  aview SEGS (w_H W2) mem' (SF + 688 + 4) = Some 0 ->
  (forall j, (j < length s)%nat -> aview SEGS (w_H W2) mem' (SF + 528 + Z.of_nat j) = Some (bz (nthb s j))) ->
  SlotModel.n_ends_w4 (e_pl g) = false ->
  SRr SEGS W2 (cfg_at SEGS (BASE + 0x1478) regs' mem' md') (jcut g pos mf nm tk dp (BASE + 0x1528) (Pj3 g pos mf))).
{ intros regs' mem' md' HJ' RK Q17 Q25 Q18 KP M4 BY Hend.
  assert (EXPe : SlotModel.n_EXP_NM (e_pl g) = s ++ [SlotModel.dash] ++ wl)
    by (unfold SlotModel.n_EXP_NM; rewrite Hend, <- Hs_def, <- Hwl_def; reflexivity).
  assert (W4m : forall j, (j < 4)%nat -> aview SEGS (w_H W2) mem' (SF + 688 + Z.of_nat j) = Some (bz (nthb wl j))).
  { intros j Hj. rewrite KP by jd_lia. apply jd_ga_get; [exact HW4 | rewrite HW4l; exact Hj]. }
  apply (jd_d4 B LAWS LLVMF_STK (e_sp0 g) [] [(4, pos)] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) ly2 S2 W2 K0
           (SF + 528) (SF + 688) (Z.of_nat (length s)) wl regs' mem' md' _ HJ').
  - rewrite RK by jd_inl. exact R26.
  - exact Q25.
  - exact Q17.
  - exact Q18.
  - lia.
  - lia.
  - exact Hnapp.
  - lia.
  - lia.
  - lia.
  - lia.
  - lia.
  - left. lia.
  - exact HW4d.
  - exact W4m.
  - exact M4.
  - apply (jd_zs_kept W2 (jd_WS SF mf) mem2 mem' (SF + 528) 32 KP); [lia | lia | lia | exact HZS | exact ZN].
  - apply (jd_zs_kept W2 (jd_WS SF mf) mem2 mem' (SF + 688) 8 KP); [lia | lia | lia | exact HZS | exact ZW].
  - apply (WRJ _ md' _ _ HJ'); lia.
  - intros regs'' mem'' md'' HJ'' RK4 Q25' KP4 M45 MW.
    assert (KP'' : jd_kept W2 (jd_WS SF mf) mem2 mem'')
      by (apply (jd_kept_trans W2 (jd_WS SF mf)
                  (fun a => SF + 528 + Z.of_nat (length s) <= a < SF + 528 + Z.of_nat (length s) + 5)
                  (jd_WS SF mf) mem2 mem' mem''); [tauto | intros a Ha; jd_lia | exact KP | exact KP4]).
    apply (jd_d5 B LAWS LLVMF_STK (e_sp0 g) [] [(4, pos)] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) ly2 S2 W2 K0
             (SF + 528) (Z.of_nat (length s) + 5) regs'' mem'' md'' _ HJ'').
    + rewrite RK4 by jd_inl. rewrite RK by jd_inl. exact R26.
    + exact Q25'.
    + rewrite RK4 by jd_inl. exact Q17.
    + lia.
    + lia.
    + exact Hnapp.
    + lia.
    + lia.
    + apply (jd_zs_kept W2 (jd_WS SF mf) mem2 mem'' (SF + 528) 32 KP''); [lia | lia | lia | exact HZS | exact ZN].
    + apply (WRJ _ md'' _ _ HJ''); lia.
    + intros regsF memF mdF HJF RK5 KM5. apply KF; [exact HJF | | | | |].
      * intros r Hr. rewrite (RK5 r (jd_fk_5 r Hr)). rewrite (RK4 r (jd_fk_4 r Hr)). exact (RK r Hr).
      * rewrite RK5 by jd_inl. rewrite Q25'. unfold SlotModel.n_ln. rewrite EXPe.
        rewrite !length_app, HW4l. cbn [length]. f_equal. lia.
      * rewrite RK5 by jd_inl. rewrite RK4 by jd_inl. exact Q17.
      * apply (jd_kept_trans W2 (jd_WS SF mf) (fun a => a = SF + 528 + (Z.of_nat (length s) + 5)) (jd_WS SF mf)
                 mem2 mem'' memF); [tauto | intros a Ha; jd_lia | exact KP'' | exact (proj1 KM5)].
      * rewrite EXPe. intros j Hj. rewrite !length_app, HW4l in Hj. cbn [length] in Hj.
        rewrite (JDModel.nth_app5 s wl j HW4l).
        destruct (Nat.ltb_spec j (length s)) as [H1|H1];
          [|destruct (Nat.eqb_spec j (length s)) as [H2|H2];
            [|destruct (Nat.ltb_spec j (length s + 5)) as [H3|H3]]].
        -- rewrite (proj1 KM5) by jd_lia. rewrite KP4 by jd_lia. exact (BY j H1).
        -- subst j. rewrite (proj1 KM5) by jd_lia. exact M45.
        -- rewrite (proj1 KM5) by jd_lia.
           replace (SF + 528 + Z.of_nat j) with (SF + 528 + Z.of_nat (length s) + 1 + Z.of_nat (j - length s - 1)) by lia.
           apply MW. lia.
        -- replace (SF + 528 + Z.of_nat j) with (SF + 528 + (Z.of_nat (length s) + 5)) by lia.
           exact (proj1 (proj2 KM5)). }
(* ---- 0x81ab4: w4[4] = 0, stem[0] ---- *)
assert (Hb0r : 0 <= bz (nthb (s ++ [zb 0]) 0) < 256) by apply jd_bz.
apply (jd_d1 B LAWS LLVMF_STK (e_sp0 g) [] [(4, pos)] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) ly2 S2 W2 K0
         mf (SF + 688) stemA (SF + 528) (bz (nthb (s ++ [zb 0]) 0)) regs2 mem2 md2 _ HJ).
- exact Rs1.
- exact R18.
- exact R23.
- exact R26.
- jd_lia.
- lia.
- lia.
- exact Hwapp.
- lia.
- exact Hs0.
- lia.
- lia.
- lia.
- lia.
- exact Hb0r.
- exact V176.
- exact Vn1.
- pose proof (jd_ga_get (w_H W2) mem2 stemA (s ++ [zb 0]) 0 Hsb ltac:(rewrite length_app; cbn [length]; lia)) as H0.
  rewrite Z.add_0_r in H0. apply jd_vm_of_aview. exact H0.
- exact ZW.
- apply (range_addressable_sub _ _ stemA (Z.of_nat (length s) + 1)); [exact Hsra | lia | lia].
- apply (WRJ _ md2 _ _ HJ); lia.
- (* the stem is not empty: the stem copy loop *)
  intros regs' mem' md' HJ' RK1 KM1 Q17 Q25 Hb0 Q11 Q10 Q12 Q13.
  assert (Hln : (0 < length s)%nat).
  { destruct s as [|x s']; [exfalso; apply Hb0; reflexivity | cbn [length]; lia]. }
  rewrite (JDModel.nthb_l s [zb 0] 0 Hln) in Q13.
  assert (KM1k : jd_kept W2 (fun a => a = SF + 688 + 4) mem2 mem') by exact (proj1 KM1).
  eapply SRr_bind.
  { apply (LLVMFuzzerTestOneInput_Jstem.j_stem_loop B LAWS LLVMF_STK (e_sp0 g) [] [(4, pos)] (e_ly g) (e_S g)
             (e_W g) (e_mem g) (e_md g) ly2 S2 W2 K0 (SF + 528) stemA s 0%nat regs' mem' md' HJ').
    - rewrite RK1 by jd_inl. exact Rgp.
    - rewrite RK1 by jd_inl. exact Rtp.
    - exact Q17.
    - replace (SF + 528 + Z.of_nat 0) with (SF + 528) by lia. exact Q11.
    - replace (SF + 528 + Z.of_nat 0 - 4) with (SF + 528 - 4) by lia. exact Q10.
    - exact Q12.
    - exact Q25.
    - exact Q13.
    - exact Hln.
    - exact Hs16.
    - exact Hsnz.
    - apply (jd_ga_kept W2 (fun a => a = SF + 688 + 4) mem2 mem' stemA _ KM1k); [|exact Hsb].
      intros j Hj. rewrite length_map, length_app in Hj. cbn [length] in Hj. split; jd_lia.
    - apply (jd_rad_kept W2 (fun a => a = SF + 688 + 4) mem2 mem' stemA _ KM1k); [lia | lia | | exact Hsra].
      intros x Hx Hq. unfold JD_SB in Hx. destruct HSFapp as [_ [HA | [HA1 HA2]]];
        unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; lia.
    - intros x Hx. destruct (Z.eq_dec x (SF + 688 + 4)) as [-> | Hne].
      + rewrite (proj1 (proj2 KM1)). discriminate.
      + rewrite KM1k by jd_lia. exact (Hsbey x Hx).
    - apply (jd_zs_kept W2 (fun a => a = SF + 688 + 4) mem2 mem' (SF + 528) 32 KM1k); [lia | lia | lia | | exact ZN].
      intros x Hx Hq. unfold JD_SB in Hx. destruct HSFapp as [_ [HA | [HA1 HA2]]];
        unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; lia.
    - apply (WRJ _ md' _ _ HJ'); lia.
    - intros j Hj. lia.
    - exact Hnapp.
    - exact Hsapp.
    - lia.
    - lia.
    - lia.
    - exact Hs0.
    - exact Hs1.
    - lia. }
  intros W' c' _ (-> & regsF & memF & mdF & -> & HJF & RKF & R25F & R10F & BYF & KPF & GRF).
  assert (KPFk : jd_kept W2 (fun a => SF + 528 <= a < SF + 528 + Z.of_nat (length s)) mem' memF) by exact KPF.
  assert (KF1 : jd_kept W2 (jd_WS SF mf) mem2 memF)
    by (apply (jd_kept_trans W2 (fun a => a = SF + 688 + 4) (fun a => SF + 528 <= a < SF + 528 + Z.of_nat (length s))
                (jd_WS SF mf) mem2 mem' memF); [intros a Ha; jd_lia | intros a Ha; jd_lia | exact KM1k | exact KPFk]).
  assert (W4F : forall j, (j < 4)%nat -> aview SEGS (w_H W2) memF (SF + 688 + Z.of_nat j) = Some (bz (nthb wl j))).
  { intros j Hj. rewrite KF1 by jd_lia. apply jd_ga_get; [exact HW4 | rewrite HW4l; exact Hj]. }
  assert (M4F : aview SEGS (w_H W2) memF (SF + 688 + 4) = Some 0)
    by (rewrite KPFk by jd_lia; exact (proj1 (proj2 KM1))).
  apply (jd_d2 B LAWS ABCMP LLVMF_STK (e_sp0 g) [] [(4, pos)] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) ly2 S2 W2 K0
           mf (mf - e_sp0 g) (SF + 528) (SF + 688) (Z.of_nat (length s)) 4 pos regsF memF mdF _ HJF).
  + rewrite RKF by jd_inl. rewrite RK1 by jd_inl. exact Rsp.
  + rewrite RKF by jd_inl. rewrite RK1 by jd_inl. exact Rs1.
  + rewrite RKF by jd_inl. rewrite RK1 by jd_inl. exact Rgp.
  + rewrite RKF by jd_inl. rewrite RK1 by jd_inl. exact Rtp.
  + exact R25F.
  + exact R10F.
  + rewrite RKF by jd_inl. rewrite RK1 by jd_inl. exact R18.
  + rewrite RKF by jd_inl. exact Q17.
  + lia.
  + lia.
  + lia.
  + unfold STK_LLVMF, ASTACK, ESTACK in *. lia.
  + unfold ASTACK. lia.
  + lia.
  + lia.
  + exact Hnapp.
  + lia.
  + lia.
  + lia.
  + exact Hwapp.
  + lia.
  + lia.
  + exact Hin4.
  + rewrite EFa. lia.
  + rewrite EFa. change (fs_frame_bytes 4) with 1024. lia.
  + rewrite EFa. lia.
  + rewrite EFa. change (fs_frame_bytes 4) with 1024. lia.
  + apply (jd_vm_kept W2 (jd_WS SF mf) mem2 memF (mf + 176) 8 SHADOW_OFF KF1); [|exact V176].
    intros j Hj. cbn [Z.of_nat Pos.of_succ_nat] in Hj. split; jd_lia.
  + apply (jd_zs_kept W2 (jd_WS SF mf) mem2 memF (SF + 528) 32 KF1); [lia | lia | lia | exact HZS | exact ZN].
  + apply (jd_zs_kept W2 (jd_WS SF mf) mem2 memF (SF + 688) 8 KF1); [lia | lia | lia | exact HZS | exact ZW].
  + intros a Ha. apply (aview_some_of_apresent SEGS).
    apply (proj2 (WRJ memF mdF (SF + 528) 32 HJF ltac:(lia) ltac:(lia) a Ha)).
  + intros a Ha. replace a with (SF + 688 + Z.of_nat (Z.to_nat (a - (SF + 688)))) by lia.
    rewrite W4F by lia. discriminate.
  + (* the stem is shorter than 4 bytes, or its tail is not w4: append *)
    intros regs3 mem3 md3 HJ3 RK2 Q17' Q25' Q18' KP2 Hdis.
    apply (KA regs3 mem3 md3 HJ3).
    * intros r Hr. rewrite (RK2 r Hr). rewrite (RKF r (jd_fk_s r Hr)). exact (RK1 r (jd_fk_1 r Hr)).
    * exact Q17'.
    * exact Q25'.
    * exact Q18'.
    * apply (jd_kept_trans W2 (jd_WS SF mf) (fun a => mf - 2 * ESTACK <= a < mf) (jd_WS SF mf) mem2 memF mem3);
        [tauto | intros a Ha; jd_lia | exact KF1 | exact KP2].
    * rewrite KP2 by jd_lia. exact M4F.
    * intros j Hj. rewrite KP2 by jd_lia. exact (BYF j Hj).
    * unfold SlotModel.n_ends_w4. rewrite <- Hs_def, <- Hwl_def.
      destruct Hdis as [HL4 | Hne]; [replace (4 <=? length s)%nat with false by (symmetry; apply Nat.leb_gt; lia); reflexivity|].
      destruct (Nat.leb_spec 4 (length s)) as [HL4 | HL4]; [cbn [andb] | reflexivity].
      destruct (IdentSpec.bytes_eqb (skipn (length s - 4) s) (firstn 4 wl)) eqn:Hq; [exfalso | reflexivity].
      apply Hne. intros i Hi. pose proof (proj1 (JDModel.ends_iff s wl HL4 HW4l) Hq (Z.to_nat i) ltac:(lia)) as Hi'.
      replace (SF + 528 + Z.of_nat (length s) - 4 + i) with (SF + 528 + Z.of_nat (length s - 4 + Z.to_nat i)) by lia.
      replace (SF + 688 + i) with (SF + 688 + Z.of_nat (Z.to_nat i)) by lia.
      rewrite BYF by lia. rewrite W4F by lia. rewrite Hi'. reflexivity.
  + (* the tail of the stem is w4 *)
    intros regs3 mem3 md3 HJ3 RK2 Q17' Q25' KP2 HL4 Heq.
    apply (KE regs3 mem3 md3 HJ3).
    * intros r Hr. rewrite (RK2 r Hr). rewrite (RKF r (jd_fk_s r Hr)). exact (RK1 r (jd_fk_1 r Hr)).
    * exact Q17'.
    * exact Q25'.
    * apply (jd_kept_trans W2 (jd_WS SF mf) (fun a => mf - 2 * ESTACK <= a < mf) (jd_WS SF mf) mem2 memF mem3);
        [tauto | intros a Ha; jd_lia | exact KF1 | exact KP2].
    * intros j Hj. rewrite KP2 by jd_lia. exact (BYF j Hj).
    * unfold SlotModel.n_ends_w4. rewrite <- Hs_def, <- Hwl_def.
      replace (4 <=? length s)%nat with true by (symmetry; apply Nat.leb_le; lia). cbn [andb].
      apply (JDModel.ends_iff s wl ltac:(lia) HW4l). intros i Hi.
      pose proof (Heq (Z.of_nat i) ltac:(lia)) as Hq.
      replace (SF + 528 + Z.of_nat (length s) - 4 + Z.of_nat i) with (SF + 528 + Z.of_nat (length s - 4 + i)) in Hq by lia.
      rewrite BYF in Hq by lia. rewrite W4F in Hq by lia. injection Hq as Hq. exact Hq.
- (* the stem is empty: s9 = 0, append *)
  intros regs' mem' md' HJ' RK1 KM1 Q17 Q25 Hb0.
  assert (Hln : length s = 0%nat).
  { destruct s as [|x s']; [reflexivity|]. exfalso. apply (Hsnz 0%nat ltac:(cbn [length]; lia)). exact Hb0. }
  apply (KA regs' mem' md' HJ').
  + intros r Hr. exact (RK1 r (jd_fk_1 r Hr)).
  + exact Q17.
  + rewrite Hln. exact Q25.
  + rewrite RK1 by jd_inl. exact R18.
  + apply (jd_kept_trans W2 (fun a => a = SF + 688 + 4) (fun _ => False) (jd_WS SF mf) mem2 mem' mem');
      [intros a Ha; unfold jd_WS; left; lia | intros a Ha; destruct Ha | exact (proj1 KM1) | intros a _ _; reflexivity].
  + exact (proj1 (proj2 KM1)).
  + intros j Hj. lia.
  + unfold SlotModel.n_ends_w4. rewrite <- Hs_def, Hln. reflexivity.
Qed.
Check (j_D : j_D_stmt B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS asink_none
  ameta_inv arodata_okS).
End mc.
End mb.
End ma.
