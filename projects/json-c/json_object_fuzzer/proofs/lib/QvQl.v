(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWTC Qt8n QWtD QZDE QvSK.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import QWTC Qt8n QWtD.

Import QvSK.Mq0.
Import ListNotations. Import AX2. Import AX2S. Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

Section Cells2.
Variable segs : list Segment.
Variables (E : env) (base : word -> option byte) (kn : list kentry).
Hypothesis KN : know_ok segs E base kn.

Definition img_range (lo hi : Z) : bool :=
existsb (fun K => match K with KImg l h => Z.leb l lo && Z.leb hi h | _ => false end) kn.

Lemma img_range_sound : forall lo hi, img_range lo hi = true -> forall a, lo <= a < hi -> base (Z_to_bv 64 a) = None.
Proof.
intros lo hi H a Ha. unfold img_range in H. apply existsb_exists in H as (K & HIn & HK).
pose proof (proj1 (Forall_forall _ _) KN K HIn) as OK.
destruct K; try discriminate. apply andb_prop in HK as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
cbn [kentry_ok] in OK. destruct OK as (_ & _ & OK). apply OK. lia.
Qed.

Definition img_ranges (l : list (Z * Z)) : bool := forallb (fun iv => img_range (fst iv) (snd iv)) l.
Lemma img_ranges_sound : forall l, img_ranges l = true ->
Forall (fun iv => forall a, fst iv <= a < snd iv -> base (Z_to_bv 64 a) = None) l.
Proof.
intros l H. apply Forall_forall. intros iv Hin. unfold img_ranges in H. rewrite forallb_forall in H.
exact (img_range_sound _ _ (H iv Hin)).
Qed.

Lemma mem_inv_of_img : forall rlo rhi,
img_range rlo rhi = true ->
(forall a : word, QZDE.ro_addr segs a = true -> rlo <= bv_unsigned a < rhi) ->
QZDE.mem_inv segs base.
Proof.
intros rlo rhi H RO a b Hab. destruct (QZDE.ro_addr segs a) eqn:R; [|reflexivity]. exfalso.
pose proof (img_range_sound rlo rhi H (bv_unsigned a) (RO a R)) as N. rewrite Z_to_bv_bv_unsigned in N. congruence.
Qed.
End Cells2.
End Mq0.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWTC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWTC. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QgpE.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QgpE. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qt8n.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qt8n. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWtD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWtD.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZDE. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbVh. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlEo_c1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QvSK.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QvSK.Mq0.
Import ListNotations. Import AX2. Import AX2S. Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

Section Match.
Variable segs : list Segment.

Fixpoint sc_match (E : env) (A : Z) (cs : list scell) (tcs : list QbVh.cell) : Prop :=
match cs, tcs with
| [], [] => True
| SCw w v :: r, c :: tr => word_to_le_bytes w (edenot E v) = QbVh.cbytes c /\ sc_match E (A + Z.of_nat w) r tr
| SCz n :: r, c :: tr => repeat (Z_to_bv 8 0) n = QbVh.cbytes c /\ sc_match E (A + Z.of_nat n) r tr
| SCi n :: r, c :: tr => rom_bytes segs A n = QbVh.cbytes c /\ sc_match E (A + Z.of_nat n) r tr
| _, _ => False
end.

Lemma sc_match_bytes : forall E cs A tcs, sc_match E A cs tcs -> sc_bytes segs E A cs = QbVh.cells_bytes tcs.
Proof.
intros E cs. induction cs as [|c r IH]; intros A [|t tr] H; cbn [sc_match] in H; try contradiction.
- reflexivity.
- destruct c; contradiction.
- destruct c as [w v|n|n]; destruct H as [H1 H2]; cbn [sc_bytes QbVh.cells_bytes]; rewrite H1, (IH _ _ H2); reflexivity.
Qed.

Lemma u64s_cells : forall ws, Q5Rg.u64s ws = QbVh.cells_bytes (map QbVh.C8 ws).
Proof. induction ws as [|w r IH]; [reflexivity|]. cbn [map QbVh.cells_bytes QbVh.cbytes]. rewrite <- IH. reflexivity. Qed.

Section Sound.
Variables (E : env) (base : word -> option byte) (kn : list kentry).
Hypothesis KN : know_ok segs E base kn.

Theorem check_cells_at : forall cs b off tcs,
cells_check segs kn b off cs = true ->
let A := bv_unsigned (edenot E b) + off in
0 <= A -> A + Z.of_nat (scs_len cs) <= 2^64 ->
sc_match E A cs tcs -> QbVh.cells_wf tcs ->
QbVh.cells_at segs base A tcs /\ Z.of_nat (QbVh.cells_size tcs) = Z.of_nat (scs_len cs).
Proof.
intros cs b off tcs C A H0 H1 M WF.
pose proof (cells_check_sound segs E base kn KN cs b off C H0 H1) as BA. fold A in BA.
pose proof (sc_match_bytes E cs A tcs M) as EQ. rewrite EQ in BA.
split; [split; [exact WF | exact BA]|].
rewrite <- (QbVh.cells_bytes_length tcs WF), <- EQ, sc_bytes_length. reflexivity.
Qed.

Theorem check_rw_cells : forall cs b off tcs,
cells_check segs kn b off cs = true ->
let A := bv_unsigned (edenot E b) + off in
0 <= A -> A + Z.of_nat (scs_len cs) <= 2^64 ->
sc_match E A cs tcs -> QbVh.cells_wf tcs ->
QZDE.wr_at segs base A (Z.of_nat (scs_len cs)) ->
QlEo_c1.rw_cells segs base A tcs.
Proof.
intros cs b off tcs C A H0 H1 M WF W.
destruct (check_cells_at cs b off tcs C H0 H1 M WF) as [CA SZ]. split; [exact CA|]. rewrite SZ. exact W.
Qed.

Theorem check_u64arr : forall cs b off ws,
cells_check segs kn b off cs = true ->
let A := bv_unsigned (edenot E b) + off in
0 <= A -> A + Z.of_nat (scs_len cs) <= 2^64 ->
sc_match E A cs (map QbVh.C8 ws) ->
QZDE.wr_at segs base A (Z.of_nat (scs_len cs)) ->
Q5Rg.u64arr segs base A ws.
Proof.
intros cs b off ws C A H0 H1 M W.
assert (WF : QbVh.cells_wf (map QbVh.C8 ws)) by (clear; induction ws; cbn; [exact I | split; [exact I | assumption]]).
destruct (check_cells_at cs b off _ C H0 H1 M WF) as [[_ BA] SZ].
split; [rewrite u64s_cells; exact BA|].
replace (8 * Z.of_nat (length ws)) with (Z.of_nat (scs_len cs)); [exact W|].
rewrite <- SZ. clear. induction ws as [|w r IH]; [reflexivity|]. cbn [map QbVh.cells_size QbVh.csize length]. lia.
Qed.

Theorem check_u8arr : forall cs b off bs,
cells_check segs kn b off cs = true ->
let A := bv_unsigned (edenot E b) + off in
0 <= A -> A + Z.of_nat (scs_len cs) <= 2^64 ->
sc_match E A cs [QbVh.CB (length bs) bs] ->
QZDE.wr_at segs base A (Z.of_nat (scs_len cs)) ->
Q5Rg.u8arr segs base A bs.
Proof.
intros cs b off bs C A H0 H1 M W.
assert (WF : QbVh.cells_wf [QbVh.CB (length bs) bs]) by (cbn; split; [reflexivity | exact I]).
destruct (check_cells_at cs b off _ C H0 H1 M WF) as [[_ BA] SZ].
cbn [QbVh.cells_bytes QbVh.cbytes] in BA. rewrite app_nil_r in BA. split; [exact BA|].
replace (Z.of_nat (length bs)) with (Z.of_nat (scs_len cs)); [exact W|]. rewrite <- SZ. cbn [QbVh.cells_size QbVh.csize]. lia.
Qed.
End Sound.
End Match.
