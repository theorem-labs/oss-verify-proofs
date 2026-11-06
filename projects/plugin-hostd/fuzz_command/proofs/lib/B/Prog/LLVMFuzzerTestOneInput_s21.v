(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the kit of segment LH of LLVMFuzzerTestOneInput's ASan+UBSan walk (plugin-hostd/fuzz_command image B, 0x866bc .. the send), the B twin of lib/A/Prog/LLVMFuzzerTestOneInput_s21.v: the code table rec_codes (0x21be0) as a read-only region of 58 literal chunks, the code count rec_codes (0x21d00, 58) and its shadow cell (4), and the recorder's representation across the two g_rec stores, in the form of proofs/cgif/cgif_file_fuzzer/lib/A/AChc.v (the object facts a walk carries across a step). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI00 YI04 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv CommandModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YCfn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtString.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaCall PaDenot PaSB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
CmdGlob CmdBase CmdRep CmdObj CmdRo CmdAddr CmdChk.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
LLVMFuzzerTestOneInput_c LLVMFuzzerTestOneInput_defs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require SlotSpec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* the record's field offsets are Definitions, so an index goal needs them unfolded before lia *)
Ltac lh_off :=
  try unfold OFF_REFUSE in *; try unfold OFF_CODE in *; try unfold OFF_NCALLS in *; try unfold OFF_CALLS in *;
  try unfold CALL_SIZE in *; try unfold CALL_OFF_FN in *; try unfold CALL_OFF_NARGS in *;
  try unfold CALL_OFF_ARGS in *; try unfold OFF_ANSWER in *; try unfold OFF_NREPLIES in *;
  try unfold OFF_REPLY in *; try unfold OFF_REPLY_SIZE in *; try unfold OFF_STATE in *; try unfold OFF_HOST in *;
  try unfold REC_SIZE in *; try unfold SC_SIZE in *.
Ltac lh_lia := lh_off; lia.

(* ---- the code table rec_codes (0x21be0, 232 bytes), as the 58 four-byte words the image holds ---- *)
Definition lh_u32 : list Z := Eval vm_compute in
map (fun k => bytes_le_to_Z (firstn 4 (skipn (4 * k) RO_rec_codes))) (seq 0 58).
Definition lh_chunks : list YP09.chunk := Eval vm_compute in
map (fun k => YP09.mkChunk (4 * Z.of_nat k) (CVal 4 (SLit (nth k lh_u32 0)))) (seq 0 58).
Lemma lh_u32_range : forall k, (k < 58)%nat -> 0 <= nth k lh_u32 0 < 2 ^ 32.
Proof.
assert (H : forallb (fun v => (0 <=? v) && (v <? 2 ^ 32)) lh_u32 = true) by (vm_compute; reflexivity).
intros k Hk. rewrite forallb_forall in H.
assert (Hl : (k < length lh_u32)%nat) by (change (length lh_u32) with 58%nat; exact Hk).
specialize (H (nth k lh_u32 0) (nth_In lh_u32 0 Hl)).
apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia.
Qed.
Lemma lh_bytes : forall k j, (k < 58)%nat -> (j < 4)%nat ->
Z_to_bv 8 (le_byte (nth k lh_u32 0) 4 j) = nth (4 * k + j) RO_rec_codes (Z_to_bv 8 0).
Proof.
assert (H : forallb (fun k => forallb (fun j => Z.eqb (bv_unsigned (Z_to_bv 8 (le_byte (nth k lh_u32 0) 4 j)))
(bv_unsigned (nth (4 * k + j) RO_rec_codes (Z_to_bv 8 0)))) (seq 0 4)) (seq 0 58) = true) by (vm_compute; reflexivity).
intros k j Hk Hj. rewrite forallb_forall in H. specialize (H k ltac:(apply in_seq; lia)).
rewrite forallb_forall in H. specialize (H j ltac:(apply in_seq; lia)). apply Z.eqb_eq in H. apply bv_eq. exact H.
Qed.
(* the two read-only objects of the stretch, from cmd_ro_ok *)
Lemma lh_ro_codes : forall rd, cmd_ro_ok rd -> abytes_atR rd 0x21be0 RO_rec_codes.
Proof.
intros rd [HRO _]. unfold cmd_ro_bytes in HRO.
repeat match type of HRO with abytes_atR _ 0x21be0 _ /\ _ => exact (proj1 HRO) | _ /\ _ => apply proj2 in HRO end.
Qed.
Lemma lh_ro_ncodes : forall rd, cmd_ro_ok rd -> abytes_atR rd 0x21d00 RO_rec_ncodes.
Proof.
intros rd [HRO _]. unfold cmd_ro_bytes in HRO.
repeat match type of HRO with abytes_atR _ 0x21d00 _ /\ _ => exact (proj1 HRO) | _ /\ _ => apply proj2 in HRO end.
Qed.
Lemma lh_mbytes : forall segs H mem, cmd_ro_ok (aview segs H mem) -> forall i, (i < 232)%nat ->
mbyte segs (mrestrict H mem) (0x21be0 + Z.of_nat i) = Some (nth i RO_rec_codes (Z_to_bv 8 0)).
Proof.
intros segs H mem HRO i Hi.
pose proof (lh_ro_codes _ HRO) as HA.
specialize (HA i ltac:(apply Nat.lt_le_trans with 232%nat; [exact Hi | apply Nat.leb_le; vm_compute; reflexivity])).
unfold aview in HA.
destruct (mbyte segs (mrestrict H mem) (0x21be0 + Z.of_nat i)) as [b|]; cbn in HA; [|discriminate HA].
injection HA as Hb. f_equal. apply bv_eq. exact Hb.
Qed.
Lemma lh_chunks_ok : forall segs E m base,
(forall i, (i < 232)%nat -> mbyte segs m (base + Z.of_nat i) = Some (nth i RO_rec_codes (Z_to_bv 8 0))) ->
Forall (YP09.chunk_ok segs E m base) lh_chunks.
Proof.
intros segs E m base H.
assert (HC : lh_chunks = map (fun k => YP09.mkChunk (4 * Z.of_nat k) (CVal 4 (SLit (nth k lh_u32 0)))) (seq 0 58))
by (vm_compute; reflexivity).
rewrite HC. apply Forall_forall. intros ch Hin. apply in_map_iff in Hin as (k & <- & Hk). apply in_seq in Hk.
pose proof (lh_u32_range k ltac:(lia)) as Rk.
apply (chunk_ok_val segs E m base (4 * Z.of_nat k) 4 (SLit (nth k lh_u32 0)) (nth k lh_u32 0)).
- reflexivity.
- change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32). exact Rk.
- cbn. lia.
- intros j Hj. change (N.to_nat 4) with 4%nat in Hj |- *.
  replace (base + 4 * Z.of_nat k + Z.of_nat j) with (base + Z.of_nat (4 * k + j)) by lia.
  rewrite H by lia. rewrite <- (lh_bytes k j ltac:(lia) Hj). reflexivity.
Qed.
(* the table's entries as the code the pass sets: rec_codes[i] read by `lw`, i.e. the 32-bit word sign-extended *)
Lemma lh_code_of_u32 : forall i, (i < 58)%nat ->
nth i lh_u32 0 = nth i RecFacts.rec_codes 0 mod 2 ^ 32.
Proof.
assert (H : forallb (fun i => Z.eqb (nth i lh_u32 0) (nth i RecFacts.rec_codes 0 mod 2 ^ 32)) (seq 0 58) = true)
by (vm_compute; reflexivity).
intros i Hi. rewrite forallb_forall in H. specialize (H i ltac:(apply in_seq; lia)). apply Z.eqb_eq in H. exact H.
Qed.
(* rec_ncodes holds 58 (its four bytes) *)
Lemma lh_ncodes_val : forall rd, cmd_ro_ok rd -> aval_mem rd LT_NCODESA 4 LT_NCODES.
Proof.
intros rd HRO. pose proof (lh_ro_ncodes rd HRO) as HA. intros k Hk. unfold LT_NCODESA.
rewrite (HA k ltac:(cbn [length RO_rec_ncodes map]; lia)).
assert (k = 0 \/ k = 1 \/ k = 2 \/ k = 3)%nat as [-> | [-> | [-> | ->]]] by lia; vm_compute; reflexivity.
Qed.

(* ---- the recorder's representation across a write (lib/B/Prog/sup_worker_list_s2.v's transport lemmas) ---- *)
Lemma lh_aval_kept : forall (rd rd' : reader) a n v, aval_mem rd a n v ->
(forall k, (k < n)%nat -> rd' (a + Z.of_nat k) = rd (a + Z.of_nat k)) -> aval_mem rd' a n v.
Proof. intros rd rd' a n v H Hk k Hkn. rewrite (Hk k Hkn). exact (H k Hkn). Qed.
Lemma lh_abytes_kept : forall (rd rd' : reader) a l, abytes_atR rd a l ->
(forall i, 0 <= i < Z.of_nat (length l) -> rd' (a + i) = rd (a + i)) -> abytes_atR rd' a l.
Proof. intros rd rd' a l H Hk i Hi. rewrite (Hk (Z.of_nat i) ltac:(lia)). exact (H i Hi). Qed.
Lemma lh_astr_kept : forall (rd rd' : reader) a s, astr_atR rd a s ->
(forall i, 0 <= i < Z.of_nat (length s) + 1 -> rd' (a + i) = rd (a + i)) -> astr_atR rd' a s.
Proof.
intros rd rd' a s [H1 H2] Hk. split; [|exact H2]. apply (lh_abytes_kept rd); [exact H1|].
intros i Hi. rewrite length_app in Hi. cbn [length] in Hi. apply Hk. lia.
Qed.
Lemma lh_acall_kept : forall bl bl' (rd rd' : reader) a c P, acall_at bl rd a c P ->
(forall pn, In pn P -> In pn bl') ->
(forall i, 0 <= i < CALL_OFF_ARGS + 8 * Z.of_nat (length (snd c)) -> rd' (a + i) = rd (a + i)) ->
(forall pn i, In pn P -> 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i)) ->
acall_at bl' rd' a c P.
Proof.
intros bl bl' rd rd' a c P (H1 & H2 & H3 & H4 & H5 & H6 & H7) Hbl Ha Hp.
unfold acall_at. unfold CALL_OFF_ARGS, CALL_OFF_FN, CALL_OFF_NARGS in *.
pose proof (Nat2Z.is_nonneg (length (snd c))) as Hl0.
split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
split; [apply (lh_aval_kept rd); [exact H4 | intros k Hk; rewrite <- Z.add_assoc; apply Ha; lia]|].
split; [apply (lh_aval_kept rd); [exact H5 | intros k Hk; rewrite <- Z.add_assoc; apply Ha; lia]|].
split; [exact H6|].
intros k s pn Hs Hpn. destruct (H7 k s pn Hs Hpn) as (G1 & G2 & G3 & G4 & G5).
pose proof (proj1 (nth_error_Some (snd c) k) ltac:(rewrite Hs; discriminate)) as Hk.
split; [apply (lh_aval_kept rd); [exact G1 | intros j Hj; rewrite <- !Z.add_assoc; apply Ha; lia]|].
split; [exact G2|]. split; [apply Hbl; exact (nth_error_In _ _ Hpn)|]. split; [exact G4|].
apply (lh_astr_kept rd); [exact G5 | intros i Hi; apply Hp; [exact (nth_error_In _ _ Hpn) | lia]].
Qed.

Section m.
Variable B : asyms.

Lemma lh_lay_in_calls : forall Q P pn i, nth_error (l_calls Q) i = Some P -> In pn P -> In pn (lay_blocks Q).
Proof.
intros Q P pn i Hi Hpn. unfold lay_blocks. apply in_app_iff. left. apply in_concat. exists P.
split; [exact (nth_error_In _ _ Hi) | exact Hpn].
Qed.
Lemma lh_lay_in_spill : forall Q pn, In pn (l_spill Q) -> In pn (lay_blocks Q).
Proof. intros Q pn H. unfold lay_blocks. apply in_app_iff. right. apply in_app_iff. left. exact H. Qed.
Lemma lh_lay_in_answer : forall Q pn, l_answer Q = Some pn -> In pn (lay_blocks Q).
Proof.
intros Q pn H. unfold lay_blocks. rewrite H. apply in_app_iff. right. apply in_app_iff. right.
apply in_app_iff. left. left. reflexivity.
Qed.
Lemma lh_lay_in_reply : forall Q pn, l_reply Q = Some pn -> In pn (lay_blocks Q).
Proof.
intros Q pn H. unfold lay_blocks. rewrite H. apply in_app_iff. right. apply in_app_iff. right.
apply in_app_iff. right. left. reflexivity.
Qed.

(* g_rec.refuse and g_rec.code set, every other byte of g_rec, of record.spill and of the recorder's own blocks
   kept: the representation of rec_set_rc R rf cd over the same blocks *)
Lemma lh_arep_rc : forall bl bl' (rd rd' : reader) R Q rf cd,
arep_at bl rd A_G_REC A_REC_SPILL R Q ->
(forall pn, In pn (lay_blocks Q) -> In pn bl') ->
aval_mem rd' (A_G_REC + OFF_REFUSE) 4 rf -> aval_mem rd' (A_G_REC + OFF_CODE) 4 cd ->
-2^31 <= rf < 2^31 -> -2^31 <= cd < 2^31 ->
(forall a, A_G_REC + OFF_NCALLS <= a < A_G_REC + REC_SIZE -> rd' a = rd a) ->
(forall a, A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE -> rd' a = rd a) ->
(forall pn i, In pn (lay_blocks Q) -> 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i)) ->
arep_at bl' rd' A_G_REC A_REC_SPILL (rec_set_rc R rf cd) Q.
Proof.
intros bl bl' rd rd' R Q rf cd HA HblQ Hrf Hcd Rrf Rcd Hg Hs HbQ.
destruct HA as (G1 & G2 & G3 & (C1 & C2 & C3 & C4 & C5 & C6) & Ha & Hr & (S1 & S2 & S3 & S4 & S5 & S6) & Hown).
unfold OFF_NCALLS, OFF_ANSWER, OFF_REPLY, OFF_REPLY_SIZE, OFF_REFUSE, OFF_CODE, OFF_NREPLIES, OFF_STATE, OFF_HOST,
  REC_SIZE, OFF_CALLS, CALL_SIZE, CALL_OFF_ARGS, SC_SIZE in *.
split; [exact G1|]. split; [exact G2|]. split; [exact G3|].
split.
{ cbn [r_calls r_spill rec_set_rc].
  split; [exact C1|]. split; [exact C2|].
  split; [apply (lh_aval_kept rd); [exact C3 | intros k Hk; apply Hg; clear - Hk; lh_lia]|].
  split.
  - intros i c P Hc Hp. destruct (C4 i c P Hc Hp) as [HC HF]. split; [|exact HF].
    assert (Hi : (i < length (r_calls R))%nat)
      by (rewrite <- C2; apply nth_error_Some; rewrite Hp; discriminate).
    pose proof HC as (_ & HL6 & _).
    apply (lh_acall_kept bl _ rd); [exact HC | | |].
    + intros pn Hpn. apply HblQ. exact (lh_lay_in_calls Q P pn i Hp Hpn).
    + intros j Hj. rewrite <- !Z.add_assoc. apply Hg. clear - Hj Hi HL6 C1. lh_lia.
    + intros pn j Hpn Hj. apply HbQ; [exact (lh_lay_in_calls Q P pn i Hp Hpn) | exact Hj].
  - split; [|exact C6].
    pose proof C5 as (_ & HL6 & _).
    apply (lh_acall_kept bl _ rd); [exact C5 | | |].
    + intros pn Hpn. apply HblQ. exact (lh_lay_in_spill Q pn Hpn).
    + intros j Hj. apply Hs. lh_off. unfold rec_set_rc in Hj. cbn [r_spill] in Hj.
      pose proof (proj1 (Nat2Z.inj_le _ _) HL6) as HL6Z. change (Z.of_nat 6) with 6 in HL6Z.
      remember (Z.of_nat (length (snd (r_spill R)))) as nspill eqn:Enspill. clear Enspill.
      clear - Hj HL6Z. lia.
    + intros pn j Hpn Hj. apply HbQ; [exact (lh_lay_in_spill Q pn Hpn) | exact Hj]. }
split.
{ unfold aanswer_at in *. cbn [r_answer rec_set_rc].
  destruct (r_answer R) as [x|], (l_answer Q) as [q|] eqn:Eq; try contradiction.
  - destruct Ha as (A1 & A2 & A3 & A4 & A5 & A6).
    pose proof (lh_lay_in_answer Q q Eq) as Hq.
    split; [apply (lh_aval_kept rd); [exact A1 | intros k Hk; apply Hg; clear - Hk; lh_lia]|].
    split; [exact A2|]. split; [apply HblQ; exact Hq|]. split; [exact A4|].
    split; [apply (lh_astr_kept rd); [exact A5 | intros i Hi; apply HbQ; [exact Hq | clear - Hi A4; lh_lia]] | exact A6].
  - apply (lh_aval_kept rd); [exact Ha | intros k Hk; apply Hg; clear - Hk; lh_lia]. }
split.
{ unfold areply_at in *. cbn [r_reply rec_set_rc].
  destruct (r_reply R) as [x|], (l_reply Q) as [q|] eqn:Eq; try contradiction.
  - destruct Hr as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
    pose proof (lh_lay_in_reply Q q Eq) as Hq.
    split; [apply (lh_aval_kept rd); [exact A1 | intros k Hk; apply Hg; clear - Hk; lh_lia]|].
    split; [apply (lh_aval_kept rd); [exact A2 | intros k Hk; apply Hg; clear - Hk; lh_lia]|].
    split; [exact A3|]. split; [exact A4|]. split; [apply HblQ; exact Hq|]. split; [exact A6|].
    split; [apply (lh_abytes_kept rd); [exact A7 | intros i Hi; apply HbQ; [exact Hq | clear - Hi A6; lh_lia]] | exact A8].
  - destruct Hr as [A1 A2]. split; apply (lh_aval_kept rd);
      first [exact A1 | exact A2 | intros k Hk; apply Hg; clear - Hk; lh_lia]. }
split; [|exact Hown].
unfold ag1_scalars. cbn [r_refuse r_code r_nreplies r_state r_host rec_set_rc].
split; [exact Hrf|]. split; [exact Hcd|].
split; [apply (lh_aval_kept rd); [exact S3 | intros k Hk; apply Hg; clear - Hk; lh_lia]|].
split; [apply (lh_aval_kept rd); [exact S4 | intros k Hk; apply Hg; clear - Hk; lh_lia]|].
split; [apply (lh_aval_kept rd); [exact S5 | intros k Hk; apply Hg; clear - Hk; lh_lia]|].
split; [exact Rrf | split; [exact Rcd | exact (proj2 (proj2 S6))]].
Qed.

Lemma lh_rec_repA_rc : forall ly S rd ly' S' rd' R O rf cd, rec_repA B ly S rd R O ->
(forall pn, In pn O -> In pn (ablocks B ly' S')) ->
aval_mem rd' (A_G_REC + OFF_REFUSE) 4 rf -> aval_mem rd' (A_G_REC + OFF_CODE) 4 cd ->
-2^31 <= rf < 2^31 -> -2^31 <= cd < 2^31 ->
(forall a, A_G_REC + OFF_NCALLS <= a < A_G_REC + REC_SIZE -> rd' a = rd a) ->
(forall a, A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE -> rd' a = rd a) ->
(forall p n i, In (p, n) O -> 0 <= i < n -> rd' (p + i) = rd (p + i)) ->
rec_repA B ly' S' rd' (rec_set_rc R rf cd) O.
Proof.
intros ly S rd ly' S' rd' R O rf cd (Q & HA & HO) Hbl Hrf Hcd Rrf Rcd Hg Hs Hb. exists Q. split; [|exact HO].
apply (lh_arep_rc _ _ rd rd' R Q rf cd HA);
  [intros pn Hpn; apply Hbl, HO, Hpn | exact Hrf | exact Hcd | exact Rrf | exact Rcd | exact Hg | exact Hs |].
intros [p n] i Hpn Hi. apply (Hb p n i (proj2 (HO (p, n)) Hpn) Hi).
Qed.

End m.

(* ---- registers after a run (lib/A/Prog/LLVMFuzzerTestOneInput_s23.v's helpers, shared by the head, the zero exit
   and the mid stretch) ---- *)
Lemma lhh_reg_U : forall (regs : bvmap 5 word) (rr : bv 5) E e v,
  getr regs rr = sv_denot E e -> U E e = v -> getr regs rr = w64 v.
Proof. intros regs rr E e v H HU. rewrite H. unfold w64. rewrite <- HU. unfold U. symmetry. apply Z_to_bv_bv_unsigned. Qed.
Lemma lhh_reg_keep : forall (regs regs0 : bvmap 5 word) (rr : bv 5) E (n : nat),
  getr regs rr = sv_denot E (SOff n 0) -> ew E n = getr regs0 rr -> getr regs rr = getr regs0 rr.
Proof. intros regs regs0 rr E n H Hn. rewrite H. cbn [sv_denot]. rewrite Hn, Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.
(* a register of a state, as the symbolic state names it (prreg without the normalisation) *)
Ltac lhh_prraw HS r Hr :=
  lazymatch type of HS with
  | st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
    cbn [ms_regs restrict mkst] in Hr
  | st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_restrict_reg segs H E ss ms r HS) as Hr;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
    cbn [ms_regs restrict mkst] in Hr
  end.
(* an atom below the run's fresh ones *)
Ltac lhh_atom := repeat (rewrite ew_ewset_other by lia); assumption.
Ltac lhh_side := first [lhh_atom | lia].
(* the model a run leaves, named once *)
Ltac lhh_mdv := lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ =>
  let x := fresh "mdv" in set (x := d) in *; clearbody x end.
(* a register the run kept: EEo names every register atom of the seed's environment *)
Ltac lhh_kreg HS r :=
  let P := fresh "P" in lhh_prraw HS r P; apply (lhh_reg_keep _ _ _ _ _ P);
  repeat (rewrite ew_ewset_other by lia); match goal with EEo : forall (n : nat) (rr : bv 5), _ |- _ => apply EEo end;
  reflexivity.
Ltac lhh_vreg HS r := let P := fresh "P" in lhh_prraw HS r P; apply (lhh_reg_U _ _ _ _ _ P).
(* the run wrote nothing: none of its regions has a write window *)
Ltac lhh_keep HFr :=
  apply aview_eq_of; apply HFr;
  let rg := fresh "rg" in let Hin := fresh "Hin" in let Hrg := fresh "Hrg" in
  intros [rg [Hin Hrg]]; vm_compute in Hin;
  repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hrg; lia |]); destruct Hin.
