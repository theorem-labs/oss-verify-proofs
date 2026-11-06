(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8v.v:120-122
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:518-584, 622-634 [Apache-2.0 OR MIT];
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:110-141, 221-225, 227-235, 264-270 [Apache-2.0 OR MIT], for
   libreac/fuzz_identity's ASan build (lib/A). The [Apache-2.0 OR MIT] text is used under Apache-2.0. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/LLVMFuzzerTestOneInput_L.v, with its module paths and module names changed; 149 of its 218 lines of code are new or changed and 1011 lines of the source are left out. *)
(* The proofs of the two cuts of seg_I that LLVMFuzzerTestOneInput_Icut.v states: reac_box_name's premises at
   0x8196c, said / sd (I_rbn_said) and the three output buffers (I_rbn_bufs), in that file's Section.

   said: id.model_name is the C string at SF + 355, inside id (SF + 352, 38 bytes): its bytes are name_str of the
   decoded identity, ended by the first 0 of the 17-byte field, at most at id[19] (SlotModel.rec_id_b19). id_at
   gives the bytes and the shadow of id; the frame (4, pos) gives the presence of its bytes and of its shadow.
   bufs: the run's three heap blocks are blocks of the state, pairwise apart (AR_blocks_law). *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
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
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
LLVMFuzzerTestOneInput LLVMFuzzerTestOneInput_inv LLVMFuzzerTestOneInput_Icut.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require reac_box_name.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require SlotModel RcIdentModel.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

(* ---- the plain model's facts (address-free) ------------------------------------------------------------------ *)
(* The model name's string: copied from LLVMFuzzerTestOneInput_I.v IM (nth_first', nth_skipn', fz_nz, fz_term, fz_le,
   bz_zb0, name_facts), so this file does not load the segment file. *)
Module IRbn.
Import SlotModel RcIdentModel.

Lemma nth_first' : forall (A : Type) (l : list A) k i (d : A), (i < k)%nat -> nth i (firstn k l) d = nth i l d.
Proof.
intros A l. induction l as [|x l IH]; intros [|k] [|i] d H; cbn; try reflexivity; try lia. apply IH. lia.
Qed.

Lemma nth_skipn' : forall (A : Type) (l : list A) j i d, nth i (skipn j l) d = nth (j + i) l d.
Proof.
intros A l j. revert l. induction j as [|j IH]; intros l i d; [reflexivity|].
destruct l as [|x l]; cbn [skipn]; [destruct i; reflexivity|]. cbn [Nat.add nth]. apply IH.
Qed.

Lemma fz_nz : forall l, Forall (fun b => bz b <> 0) (firstn (first_zero l) l).
Proof.
induction l as [|b l IH]; cbn [first_zero]; [constructor|].
destruct (Z.eqb_spec (bz b) 0) as [E|E]; cbn [firstn]; [constructor | constructor; [exact E | exact IH]].
Qed.

Lemma fz_term : forall l, (first_zero l < length l)%nat -> bz (nth (first_zero l) l (zb 0)) = 0.
Proof.
induction l as [|b l IH]; cbn [first_zero length]; intros H; [lia|].
destruct (Z.eqb_spec (bz b) 0) as [E|E]; [exact E|]. cbn [nth]. apply IH. lia.
Qed.

Lemma fz_le : forall l, (first_zero l <= length l)%nat.
Proof. induction l as [|b l IH]; cbn [first_zero length]; [lia|]. destruct (bz b =? 0); lia. Qed.

Lemma bz_zb0 : bz (zb 0) = 0.
Proof. reflexivity. Qed.

Lemma name_facts : forall idb, length idb = ID_SIZE -> bz (nthb idb 19) = 0 ->
  (length (name_str idb) <= 16)%nat /\
  Forall (fun c => 0 < c < 256) (map bz (name_str idb)) /\
  (forall j, (j <= length (name_str idb))%nat ->
     nth j (map bz (name_str idb) ++ [0]) 0 = bz (nth (3 + j) idb (zb 0))).
Proof.
intros idb Hl H19. unfold ID_SIZE in Hl.
assert (Lm : length (model_name idb) = 17%nat)
  by (unfold model_name, get, OFF_NAME, NAME_CAP; rewrite length_firstn, length_skipn; lia).
assert (Hm : forall j, (j < 17)%nat -> nth j (model_name idb) (zb 0) = nth (3 + j) idb (zb 0)).
{ intros j Hj. unfold model_name, get, OFF_NAME, NAME_CAP. rewrite nth_first' by lia. apply nth_skipn'. }
pose proof (first_zero_le (model_name idb) 16 ltac:(lia)) as F.
rewrite (Hm 16%nat ltac:(lia)) in F. specialize (F H19).
assert (Ln : length (name_str idb) = first_zero (model_name idb))
  by (unfold name_str; rewrite length_firstn; pose proof (fz_le (model_name idb)); lia).
split; [lia|]. split.
- pose proof (fz_nz (model_name idb)) as N. unfold name_str.
  apply Forall_map. eapply Forall_impl; [|exact N]. intros b Hb. cbn beta in Hb.
  pose proof (bv_unsigned_in_range 8 b) as R. change (bv_modulus 8) with 256 in R. unfold bz in *. lia.
- intros j Hj. rewrite Ln in Hj. destruct (Nat.lt_ge_cases j (first_zero (model_name idb))) as [Hlt|Hge].
  + rewrite app_nth1 by (rewrite length_map, Ln; exact Hlt).
    rewrite <- bz_zb0 at 1. rewrite map_nth. unfold name_str. rewrite nth_first' by exact Hlt.
    rewrite Hm by lia. reflexivity.
  + assert (Ej : j = first_zero (model_name idb)) by lia. subst j.
    rewrite app_nth2 by (rewrite length_map, Ln; lia). rewrite length_map, Ln, Nat.sub_diag. cbn [nth].
    rewrite <- (Hm (first_zero (model_name idb))) by lia. symmetry. apply fz_term. lia.
Qed.

(* A byte of bytes_at8's list (map bv_unsigned) is bz of the byte. *)
Lemma nth_map_bz : forall (l : list byte) n,
  nth n (map (fun b : byte => bv_unsigned b) l) 0 = bz (nth n l (zb 0)).
Proof.
intros l n. revert l. induction n as [|n IH]; intros [|x l]; cbn [map nth]; try reflexivity. apply IH.
Qed.
End IRbn.

(* A pairwise relation that is symmetric holds of every permutation of the list. *)
Lemma Irbn_pw_perm : forall (X : Type) (R : X -> X -> Prop), (forall a b, R a b -> R b a) ->
  forall l l', Permutation l l' -> YG0f.pairwise R l -> YG0f.pairwise R l'.
Proof.
intros X R Hs l l' HP. induction HP as [| x l l' HP IH | x y l | l l' l'' H1 IH1 H2 IH2]; cbn [YG0f.pairwise];
  intros H.
- exact I.
- destruct H as [Hf Hp]. split; [|exact (IH Hp)].
  apply Forall_forall. intros z Hz. apply (proj1 (Forall_forall _ _) Hf).
  exact (Permutation_in _ (Permutation_sym HP) Hz).
- destruct H as [Hfy [Hfx Hp]]. split; [constructor; [exact (Hs _ _ (Forall_inv Hfy)) | exact Hfx]|].
  split; [exact (Forall_inv_tail Hfy) | exact Hp].
- exact (IH2 (IH1 H)).
Qed.

Lemma Irbn_zd_sym : forall a b, YG0f.zdisjoint a b -> YG0f.zdisjoint b a.
Proof. unfold YG0f.zdisjoint. intros a b H. lia. Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg ident_listing}.
#[local] Notation SEGS := (@pa_segs _ ident_listing PI).
#[local] Notation VAL := (@pa_val _ ident_listing PI).
#[local] Notation BASE := (@pa_val _ ident_listing PI A_TEXT).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
Section c.
(* The Section of LLVMFuzzerTestOneInput_Icut.v, in the same order. *)
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
#[local] Notation EPRE g := (e_pre B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS g).
#[local] Notation AJ g pos := (ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g)
  [(4, pos)]).
Hypothesis HSTK : STK_LLVMF <= LLVMF_STK.
Hypothesis LAWS : AR_laws SEGS B.

Lemma I_rbn_said : I_rbn_said_stmt B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS.
Proof.
intros g pos lyc Sc W mem md k _ HJ Hfrs Hid.
pose proof HJ as (HAR & Hly & _).
assert (Hin : In (4, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
assert (EFA : frame_addr lyc 4 pos = SFa g pos)
  by (unfold SFa, frame_addr; destruct Hly as (_ & _ & _ & _ & _ & EF & _); rewrite EF; reflexivity).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 4 pos HAR Hin) as (HF4096 & HFceil & HFapp).
destruct (al_frames _ _ LAWS _ _ _ _ _ 4 pos HAR Hin) as (_ & _ & HFpres & _).
rewrite EFA in HF4096, HFceil, HFapp, HFpres.
change (fs_frame_bytes 4) with 1024 in HFceil, HFapp, HFpres.
unfold I_said, I_sd.
change (SlotModel.n_said (e_pl g)) with (negb (RcIdentModel.has_model_name (m_id g (m_nrec g)) =? 0)).
change (SlotModel.idT (e_pl g)) with (m_id g (m_nrec g)).
destruct (RcIdentModel.has_model_name (m_id g (m_nrec g)) =? 0); cbn [negb]; unfold reac_box_name.rbn_said.
{ left. split; reflexivity. }
right.
destruct Hid as (Hb & _ & Hblk). unfold bytes_at8 in Hb. unfold sh_blk, N_id in Hblk.
assert (Hlen : length (m_id g (m_nrec g)) = 38%nat) by exact (SlotModel.rec_id_length (e_pl g) (m_nrec g)).
destruct (IRbn.name_facts (m_id g (m_nrec g)) Hlen (SlotModel.rec_id_b19 (e_pl g) (m_nrec g)))
  as (Hl16 & Hrng & Hnth).
set (idb := m_id g (m_nrec g)) in *.
assert (Ls : Z.of_nat (length (map RcIdentModel.bz (SlotModel.name_str idb))) <= 16)
  by (rewrite length_map; clear - Hl16; lia).
change V_id with 352 in *.
split; [clear - HF4096; lia|].
split.
- unfold reac_box_name.rbn_cstr.
  split; [exact Hrng|].
  split; [change (2 ^ 31) with 2147483648; clear - Ls; lia|].
  split; [clear - HF4096; lia|].
  split; [apply (amem_range_sub_app (SFa g pos) 1024);
    [exact HFapp | exact HFceil | clear; lia | clear - Ls; lia | clear; lia]|].
  split.
  { intros j Hj. rewrite length_app, length_map in Hj. cbn [length] in Hj.
    assert (Hj' : (j <= length (SlotModel.name_str idb))%nat) by (clear - Hj; lia).
    destruct (Hb (3 + j)%nat ltac:(rewrite length_map, Hlen; clear - Hj' Hl16; lia)) as [Hv Hr].
    rewrite IRbn.nth_map_bz in Hv, Hr. rewrite (Hnth j Hj').
    split; [|exact Hr].
    replace (SFa g pos + 352 + 3 + Z.of_nat j) with (SFa g pos + 352 + Z.of_nat (3 + j)) by (clear; lia).
    exact Hv. }
  split; [apply (block_shadow_range _ _ (SFa g pos + 352) 38); [exact Hblk | clear; lia | clear - Ls; lia]|].
  split.
  { apply (shadow_hull_vis_of_frame SEGS B LAWS lyc Sc W mem md 4 pos); [exact HAR | exact Hin | | | clear; lia].
    - rewrite EFA. clear; lia.
    - rewrite EFA. change (fs_frame_bytes 4) with 1024. clear - Ls; lia. }
  intros x Hx. apply (aview_some_of_apresent SEGS).
  pose proof (Z.mod_pos_bound (SFa g pos + 352 + 3 + Z.of_nat (length (map RcIdentModel.bz (SlotModel.name_str idb))))
    8 ltac:(clear; lia)) as Hm.
  exact (proj1 (HFpres x ltac:(clear - Hx Hm Ls; lia))).
- exists 4, pos. split; [exact Hin|]. rewrite EFA. change (fs_frame_bytes 4) with 1024.
  split; [clear; lia | clear - Ls; lia].
Qed.

(* Three blocks of the state, at three places of its block list: each holds its buffer, and they are apart. *)
Lemma Irbn_bufs_of : forall ly S (W : world SEGS) mem md nm cn tk ct dp cd E0,
  AR SEGS B ly S W mem md ->
  Permutation (ablocks B ly S) ([(nm, Z.max cn 1); (tk, Z.max ct 1); (dp, Z.max cd 1)] ++ E0) ->
  reac_box_name.rbn_bufs B ly S nm cn tk ct dp cd.
Proof.
intros ly S W mem md nm cn tk ct dp cd E0 HAR Hperm.
assert (Hi : forall x, In x [(nm, Z.max cn 1); (tk, Z.max ct 1); (dp, Z.max cd 1)] -> In x (ablocks B ly S)).
{ intros x Hx. apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app. left. exact Hx. }
destruct (al_blocks _ _ LAWS _ _ _ _ _ nm (Z.max cn 1) HAR (Hi _ ltac:(left; reflexivity)))
  as (_ & _ & _ & _ & _ & Hpw & _).
assert (Hpw2 : YG0f.pairwise YG0f.zdisjoint (map (fun b : Z * Z => (fst b, req_size (snd b)))
  ([(nm, Z.max cn 1); (tk, Z.max ct 1); (dp, Z.max cd 1)] ++ E0))).
{ apply (Irbn_pw_perm _ _ Irbn_zd_sym (map (fun b : Z * Z => (fst b, req_size (snd b))) (ablocks B ly S)));
    [|exact Hpw].
  apply Permutation_map. exact Hperm. }
cbn [map app YG0f.pairwise fst snd] in Hpw2.
destruct Hpw2 as (F1 & F2 & _).
pose proof (Forall_inv F1) as D12. pose proof (Forall_inv (Forall_inv_tail F1)) as D13.
pose proof (Forall_inv F2) as D23.
unfold YG0f.zdisjoint in D12, D13, D23. cbn [fst snd] in D12, D13, D23.
pose proof (proj2 (req_size_pos (Z.max cn 1) ltac:(clear; lia))) as R1.
pose proof (proj2 (req_size_pos (Z.max ct 1) ltac:(clear; lia))) as R2.
pose proof (proj2 (req_size_pos (Z.max cd 1) ltac:(clear; lia))) as R3.
unfold reac_box_name.rbn_bufs.
split; [exists nm, (Z.max cn 1); split; [apply Hi; left; reflexivity | clear; lia]|].
split; [exists tk, (Z.max ct 1); split; [apply Hi; right; left; reflexivity | clear; lia]|].
split; [exists dp, (Z.max cd 1); split; [apply Hi; right; right; left; reflexivity | clear; lia]|].
split; [clear - D12 R1 R2; lia|]. split; [clear - D13 R1 R3; lia|]. clear - D23 R2 R3; lia.
Qed.

Lemma I_rbn_bufs : I_rbn_bufs_stmt B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS.
Proof.
intros g pos lyc Sc W mem md k nm tk dp _ HJ _ [Hperm _].
exact (Irbn_bufs_of lyc Sc W mem md nm _ tk _ dp _ _ (proj1 HJ) Hperm).
Qed.

End c.
End b.
End a.
