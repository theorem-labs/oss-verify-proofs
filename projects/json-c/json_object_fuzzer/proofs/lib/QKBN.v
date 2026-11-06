(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc27.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc27. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q13u.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q13u. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHig.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHig. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc6I.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc6I. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJFf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJFf.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCiC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCiC. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qpj5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qpj5.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QvDJ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QvDJ.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q67d.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q67d. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCiC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCiC.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6sh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6sh. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKTr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKTr.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJBH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJBH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZzg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZzg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QTVW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QTVW. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q61C.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q61C. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWRO.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWRO. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qu4g.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qu4g. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QFQR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QFQR. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QmP7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QmP7.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlES.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlES. Local Ltac QoSL.solve_load ::= Qqyb.mkr__solve_load_3. Local Ltac QoSL.solve_store ::= QoSL.mkr__solve_store_9. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Local Set Keyed Unification.

Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Notation mem := (word -> option byte) (only parsing).
Local Notation wz := (Z_to_bv 64).
Local Notation b8 := (Z_to_bv 8).

Definition rt_img_cells {BAND : Band} (RE : aentry) (X : rlay) : list (Z * list cell) :=
[
(0x0f2e98, [C1 (b8 1)]);
(0x0f2ea0, [C8 (wz 0x7fffffffffff); C8 (wz 0); C8 (wz 0); C1 (b8 1); CB 3 (repeat (b8 0) 3); C4 (wz 30)]);

(0x0f1a1c, [C1 (b8 1)]);
(0x0f1a20, [C1 (b8 1)]); (0x0f1a24, [C4 (wz 0)]);
(0x0f21b8, [C8 (wz 0x7fff8000)]);
(0x0f21c0, [C4 (wz 1)]);
(0x174421, [C1 (b8 1); C1 (b8 0)]);
(0x181c60, [C8 (wz 0x1000)]);
(0x181c58, [C4 (wz 0)]);
(0x183c80, [C8 (wz 0)]);
(0x183cdc, [C4 (wz 0)]);

(0x0ef9b8 + 44, [C4 (wz 0x1000); C4 (wz 0); C4 (wz 0xbe)]);
(0x0ef9b8 + 78, [C1 (b8 1)]); (0x0ef9b8 + 85, [C1 (b8 1)]);

(0x183ce8 + 34, [C1 (b8 1)]); (0x183ce8 + 120, [C8 (wz 0xffffffffffffffff)]); (0x183ce8 + 144, [C8 (wz 0)]);

(0x0e8198, [C8 (wz 0x181c60)]);
(0x0e81a8, [C8 (wz 0x183ce8); C8 (wz 0x0ef9b8); C8 (wz 0x0f21b8); C8 (wz 0x0f2ea8); C8 (wz 0x0f2eb0); C8 (wz 0x0f2ea0); C8 (wz 0x0ea1d0)]);
(0x0e81f0, [C8 (wz 0x0ea218); C8 (wz 1); C8 (wz 0x183cdc); C8 (wz 0x181c58); C8 (wz 0x0f21c0)]);
(0x0e8e18, [C8 (wz 0x10)]); (0x0e8d68, [C8 (wz 1)]);

(0x0ea1c8, [C8 (wz 0xdda10); C8 (wz 0xdde14)]);

(A_INSTANCE + 32, [C8 (wz (al_space_beg (ae_L RE))); C4 (wz 0xffffffff); C4 (wz 0); C8 (wz (region_info RE)); C1 (b8 0)]);
(A_INSTANCE + 64, [C8 (wz 0x1000); C8 (wz (ptrarr_lo RE))]);
(A_INSTANCE + 792, [C8 (wz 0x10000000); C8 (wz 0xe666661); C8 (wz 0x100000)]);
(A_INSTANCE + 3616, [C8 (wz (2^40)); C2 (wz 16); C2 (wz 2048); C1 (b8 1)]);

(A_TLS_TSD, [C8 (wz A_TSD_MAIN)]); (A_TSD_MAIN, [C8 (wz (rl_ctx X))]);
(A_TP, [C8 (wz (ae_fs_base RE))]); (A_TP + 0x8, [C8 (wz (rl_dtls X))]); (A_TP + 0x10, [C4 (wz 0)]);

(0x183ce8 + 260, [C1 (b8 0)]);
(0x0e8fe8, [C8 (wz 1); C8 (wz (2^64 - 0x800))]); (0x0e8ff8, [C8 (wz 0x8)]); (0x0ea0e0, [C8 (wz 0xdee24)]);
(0x183ce8 + 137, [C1 (b8 1)]); (A_TP - 8, [C8 (wz 0x625548)]); (A_TP + 0x30, [C8 (wz 0x625d20)]);    (0x0f2e99, [C1 (b8 1)]);

(0x183c88, [C8 (wz 0)]);

(0x0e8d28, [C8 (wz 0x0f2e99)]);

(A_INSTANCE + 80, [C8 (wz (ptrarr_lo RE)); C8 (wz 0x800000); C8 (wz 0x1a475)]);

(0x0e81a0, [C8 (wz 0x0ea208)]); (0x0ea208, [C8 (wz 0x1a475)]);

(0x0e4ab8, [C8 (wz 0x9b3cc); C8 (wz 0x3e10c)]);
(0x0e80b0, [C8 (wz 0x0ecd40)]);
(0x0e8188, [C8 (wz 0xcec58); C8 (wz 0)]);
(0x0e8f90, [C8 (wz 0x645560)]);
(0x0e8fc0, [C8 (wz 0x0e4ac8); C8 (wz 0x0e4ab8)]);

(0x645560, [C8 band_guard]); (0x6457e0, [C8 (wz 0x1000)]);

(0x183ce8 + 219, [C1 (b8 1)]); (0x183ce8 + 244, [C1 (b8 1)]);

(0x0ea178, [C8 (wz 0xde3d4)]); (0x0ea218, [C8 (wz 0x220a0)]);
(0x0ea068, [C8 (wz 0xdd914)]); (0x0ea078, [C8 (wz 0xe3934)]); (0x0ea080, [C8 (wz 0xd5bc4)]);
(0x0ea098, [C8 (wz 0xdb6ac); C8 (wz 0xd5f20)]);

(0x183ce8 + 84, [C1 (b8 1)]); (0x183ce8 + 251, [C1 (b8 1)]); (0x0ef9b8 + 24, [C4 (wz 1)]);

(0x0efab0, [C4 (wz 0)]); (0x0efa78, [C8 (wz 0); C8 (wz 0); C8 (wz 0)]);

(0x0ea020, [C8 (wz 0x0ea020)]);

(0x0ea020, [C8 (wz 0x0ea020)]); (0x0ea020, [C8 (wz 0x0ea020)]);

(0x0e8e20, [C8 (wz 0x0e80b0); C8 (wz 0)]); (0x0e8ec0, [C8 (wz 0x0ed040); C8 (wz 0x0eeb00)]);

(0x0ef9b8 + 29, [C1 (b8 1)]); (0x0e81e0, [C8 (wz 0x0ea1c8)]);

(0x0e81a0, [C8 (wz 0x0ea208)]); (0x0e8ea8, [C8 (wz 0x0a4110)]); (0x0ea028, [C8 (wz 0x0de074)]); (0x0ea0a8, [C8 (wz 0x0db6c8)]);
(0x0ea150, [C8 (wz 0x0cf4a0)]); (0x0ea1a0, [C8 (wz 0x0dceac)]); (0x183ddd, [C1 (b8 0)]); (0x183de2, [C1 (b8 1)]);

(0x0e8e58, [C8 (wz 0x09f854)]); (0x0e8e88, [C8 (wz 0x093a24)]);

(0x183de5, [C1 (b8 1)]); (0x0ea050, [C8 (wz 0x0ddf20)]); (0x0e8e38, [C8 (wz 0x09dd50)]); (0x0e8e40, [C8 (wz 0x09e4a0)]);
(0x0e8e48, [C8 (wz 0x09e8d8)]); (0x0e8e68, [C8 (wz 0x09f8e4)]); (0x0e8e98, [C8 (wz 0x0a6060)]); (0x0e8ea0, [C8 (wz 0x0a62ec)]);
(0x0e8eb0, [C8 (wz 0x0a53f4)]); (0x0e8e60, [C8 (wz 0x09f85c)]); (0x0e8e70, [C8 (wz 0x0a0a78)]); (0x0e8e78, [C8 (wz 0x0ec940)]);

(0x0e8050, [C8 (wz 0x01499c)]); (0x0e4ec8, [C8 (wz 0x09c508)]); (0x0e4ed0, [C8 (wz 0x09c600)]); (0x0e4ed8, [C8 (wz 0x09c60c)]);
(0x0e4ee0, [C8 (wz 0x09c878)]); (0x0e4ee8, [C8 (wz 0x09cd50)]); (0x0e4ef0, [C8 (wz 0x09d200)]);

(0x0e8e50, [C8 (wz 0x09edbc)]);

(0x0e8e80, [C8 (wz 0x093680)])
].

Definition rt_rw_cells : list (Z * list cell) :=
[ (0x0eeb00, [C8 (wz 1)]); (0x0efa70, [C8 (wz 0)]) ].

Definition rt_T_cells (RE : aentry) (X : rlay) : list cell :=
[ C8 (wz (rl_ctx X)); C8 (wz (ae_stack_top RE)); C8 (wz (ae_stack_bottom RE)); C8 (wz 0); C8 (wz 0);
C1 (b8 0); CB 7 (repeat (b8 0) 7); C8 (wz 0x625c58); C8 (wz 0x625d40); C8 (wz 0x625528); C8 (wz (ae_fs_base RE)) ].

Definition RTconst {BAND : Band} (RE : aentry) (X : rlay) (m : mem) : Prop :=
Forall (fun ac => ro_cells asegs m (fst ac) (snd ac)) (rt_img_cells RE X)
/\ ro_cells asegs m (rl_T X) (rt_T_cells RE X)
/\ ro_cells asegs m (rl_ctx X + 8) [C4 (wz 0)]
/\ ro_cells asegs m (rl_ctx X + 152) [C8 (wz (rl_T X))]
/\ ro_cells asegs m (rl_dtls X + 0x18) [C8 (wz A_TP)]
/\ Forall (fun ac => rw_cells asegs m (fst ac) (snd ac)) rt_rw_cells.

Definition iv_cover (l : list (Z * Z)) (a n : Z) : bool :=
existsb (fun iv => (fst iv <=? a) && (a + n <=? fst iv + snd iv)) l.

Local Lemma band0_range : 0x7fff7f800000 <= 0x7fff7f800000 <= 0x7fffff800000.
Proof. lia. Qed.
Local Definition band0 : Band := mkBand 0x7fff7f800000 band0_range (wz 0).
Definition rt_img_skel : list (Z * Z) :=
Eval vm_compute in (map (fun ac => (fst ac, Z.of_nat (cells_size (snd ac)))) (@rt_img_cells band0 (mkAE 0 0 0 (mkALay 0 0 [])) (mkRL 0 0 0 0 0) ++ rt_rw_cells)).
Lemma rt_img_skel_eq {BAND : Band} : forall RE X, map (fun ac => (fst ac, Z.of_nat (cells_size (snd ac)))) (rt_img_cells RE X ++ rt_rw_cells) = rt_img_skel.
Proof. intros. reflexivity. Qed.
Lemma rt_img_skel_cover : forallb (fun p => iv_cover rtconst_img (fst p) (snd p)) rt_img_skel = true.
Proof. vm_compute. reflexivity. Qed.

Lemma rt_img_cells_inside {BAND : Band} : forall RE X a cs, In (a, cs) (rt_img_cells RE X ++ rt_rw_cells) ->
exists iv, In iv rtconst_img /\ fst iv <= a /\ a + Z.of_nat (cells_size cs) <= fst iv + snd iv.
Proof.
intros RE X a cs Hin.
assert (Hs : In (a, Z.of_nat (cells_size cs)) rt_img_skel).
{ rewrite <- (rt_img_skel_eq RE X). apply (in_map (fun ac => (fst ac, Z.of_nat (cells_size (snd ac)))) _ _ Hin). }
pose proof rt_img_skel_cover as F. rewrite forallb_forall in F. specialize (F _ Hs). cbn [fst snd] in F.
unfold iv_cover in F. apply existsb_exists in F. destruct F as (iv & Hiv & F).
apply andb_prop in F as [F1 F2]. apply Z.leb_le in F1. apply Z.leb_le in F2. exists iv. repeat split; assumption.
Qed.

Lemma RTconst_frame {BAND : Band} : forall RE X m m', RTconst RE X m -> wmono asegs m m' -> agree_on asegs (fp_RTconst RE X) m m' -> RTconst RE X m'.
Proof.
intros RE X m m' (HI & HT & HC1 & HC2 & HD & HW) _ AG. split; [|split; [|split; [|split; [|split]]]].
- apply List.Forall_forall. intros [a cs] Hin. pose proof (proj1 (List.Forall_forall _ _) HI _ Hin) as RC. cbn [fst snd] in *.
destruct (rt_img_cells_inside RE X a cs ltac:(apply in_or_app; left; exact Hin)) as (iv & Hiv & B1 & B2).
eapply ro_cells_agree; [exact AG| exact RC|]. intros x Hx. left. exists iv. split; [exact Hiv|]. split; lia.
- eapply ro_cells_agree; [exact AG| exact HT|]. intros x Hx. right; left. cbn [rt_T_cells cells_size csize Nat.add] in Hx. split; cbn [fst snd]; lia.
- eapply ro_cells_agree; [exact AG| exact HC1|]. intros x Hx. right; right; left. cbn [cells_size csize Nat.add] in Hx. split; cbn [fst snd]; lia.
- eapply ro_cells_agree; [exact AG| exact HC2|]. intros x Hx. right; right; left. cbn [cells_size csize Nat.add] in Hx. split; cbn [fst snd]; lia.
- eapply ro_cells_agree; [exact AG| exact HD|]. intros x Hx. right; right; right. cbn [cells_size csize Nat.add] in Hx. split; cbn [fst snd]; lia.
- apply List.Forall_forall. intros [a cs] Hin. pose proof (proj1 (List.Forall_forall _ _) HW _ Hin) as RC. cbn [fst snd] in *.
destruct (rt_img_cells_inside RE X a cs ltac:(apply in_or_app; right; exact Hin)) as (iv & Hiv & B1 & B2).
eapply rw_cells_agree; [exact AG| exact RC|]. intros x Hx. left. exists iv. split; [exact Hiv|]. split; lia.
Qed.

Lemma RT_img {BAND : Band} : forall RE X m, RTconst RE X m -> forall k a cs, nth_error (rt_img_cells RE X) k = Some (a, cs) -> ro_cells asegs m a cs.
Proof.
intros RE X m (HI & _) k a cs Hk. apply nth_error_In in Hk. exact (proj1 (List.Forall_forall _ _) HI _ Hk).
Qed.
Lemma RT_T {BAND : Band} : forall RE X m, RTconst RE X m -> ro_cells asegs m (rl_T X) (rt_T_cells RE X).
Proof. intros RE X m (_ & H & _). exact H. Qed.
Lemma RT_ctx_tid {BAND : Band} : forall RE X m, RTconst RE X m -> ro_cells asegs m (rl_ctx X + 8) [C4 (wz 0)].
Proof. intros RE X m (_ & _ & H & _). exact H. Qed.
Lemma RT_ctx_thread {BAND : Band} : forall RE X m, RTconst RE X m -> ro_cells asegs m (rl_ctx X + 152) [C8 (wz (rl_T X))].
Proof. intros RE X m (_ & _ & _ & H & _). exact H. Qed.
Lemma RT_dtls {BAND : Band} : forall RE X m, RTconst RE X m -> ro_cells asegs m (rl_dtls X + 0x18) [C8 (wz A_TP)].
Proof. intros RE X m (_ & _ & _ & _ & H & _). exact H. Qed.
Lemma RT_rw {BAND : Band} : forall RE X m, RTconst RE X m -> forall k a cs, nth_error rt_rw_cells k = Some (a, cs) -> rw_cells asegs m a cs.
Proof.
intros RE X m (_ & _ & _ & _ & _ & HW) k a cs Hk. apply nth_error_In in Hk. exact (proj1 (List.Forall_forall _ _) HW _ Hk).
Qed.

Lemma RTconst_shadow {BAND : Band} : forall RE X m, RTconst RE X m -> shadow_base asegs m.
Proof.
intros RE X m RT. split.
- pose proof (RT_img _ _ _ RT 19%nat _ _ eq_refl) as H. cbn [fst snd] in H.
apply (proj1 (ro_cells_app asegs m 0x0e81a8 [C8 (wz 0x183ce8); C8 (wz 0x0ef9b8)] _)) in H as [_ H].
apply (proj1 (ro_cells_app asegs m _ [C8 (wz 0x0f21b8)] _)) in H as [H _]. exact H.
- exact (RT_img _ _ _ RT 5%nat _ _ eq_refl).
Qed.

Ltac rtc RT k H :=
pose proof (RT_img _ _ _ RT k _ _ eq_refl) as H; cbn [fst snd] in H;
lazymatch type of H with ro_cells _ _ ?a _ => let a' := eval vm_compute in a in change a with a' in H end.

Definition hjunk (m : mem) (lo hi : Z) : Prop :=
((0 <= lo /\ hi <= 0x10000) \/ 0x647000 <= lo) /\ hi <= 2^64 /\ forall a, lo <= a < hi -> exists b, m (wa a) = Some b.

Lemma hjunk_wmono : forall m m' lo hi, hjunk m lo hi -> wmono asegs m m' -> hjunk m' lo hi.
Proof.
intros m m' lo hi (H1 & H2 & H) WM. split; [exact H1|]. split; [exact H2|]. intros a Ha.
destruct (H a Ha) as [b Hb].
assert (W : wview asegs m (wa a) <> None) by (unfold wview; rewrite Hb; discriminate).
apply WM in W. rewrite a_wview_overlay in W by (rewrite wa_unsigned by lia; clear - H1 Ha; lia).
destruct (m' (wa a)) as [b'|]; [exists b'; reflexivity| exfalso; apply W; reflexivity].
Qed.

Lemma hjunk_split : forall m lo mid hi, hjunk m lo hi -> lo <= mid <= hi -> hjunk m lo mid /\ hjunk m mid hi.
Proof. intros m lo mid hi (H1 & H2 & H) Hm. split; (split; [lia|]; split; [lia|]); intros a Ha; apply H; lia. Qed.

Lemma hjunk_merge : forall m lo mid hi, hjunk m lo mid -> hjunk m mid hi -> hjunk m lo hi.
Proof.
intros m lo mid hi (A1 & A2 & A) (B1 & B2 & B). split; [clear - A1 B1; lia|]. split; [lia|].
intros a Ha. destruct (Z.lt_ge_cases a mid); [apply A| apply B]; lia.
Qed.

Lemma hjunk_nil : forall m lo, 0x647000 <= lo <= 2^64 -> hjunk m lo lo.
Proof. intros m lo H. split; [lia|]. split; [lia|]. intros a Ha. lia. Qed.

Lemma hjunk_stk : forall m lo hi, hjunk m lo hi -> stk asegs m lo hi.
Proof.
intros m lo hi (H1 & H2 & H). split; [lia|]. split; [lia|]. intros a Ha. destruct (H a Ha) as [b Hb].
split; [unfold wview; rewrite Hb; discriminate|]. exists b. unfold mrd. rewrite Hb. reflexivity.
Qed.

Lemma stk_hjunk : forall m lo hi, stk asegs m lo hi -> 0x647000 <= lo -> hjunk m lo hi.
Proof.
intros m lo hi (H1 & H2 & H) Hlo. split; [lia|]. split; [lia|]. intros a Ha. destruct (H a Ha) as [W (b & Hb)].
rewrite a_mrd_overlay in Hb by (rewrite wa_unsigned by lia; lia). exists b. exact Hb.
Qed.

Lemma stk_hjunk_oh : forall m lo hi, stk asegs m lo hi -> (0 <= lo /\ hi <= 0x10000) \/ 0x647000 <= lo -> hjunk m lo hi.
Proof.
intros m lo hi (H1 & H2 & H) Hlo. split; [exact Hlo|]. split; [lia|]. intros a Ha. destruct (H a Ha) as [W (b & Hb)].
rewrite a_mrd_overlay in Hb by (rewrite wa_unsigned by lia; clear - Hlo Ha; lia). exists b. exact Hb.
Qed.

Lemma hjunk_cells : forall m lo n, hjunk m lo (lo + Z.of_nat n) ->
exists junk, rw_cells asegs m lo [CB n junk].
Proof.
intros m lo n HJ. pose proof HJ as (H1 & H2 & _).
destruct (stk_carve asegs m lo (lo + Z.of_nat n) n (hjunk_stk _ _ _ HJ) ltac:(lia)) as (_ & junk & FR).
replace (lo + Z.of_nat n - Z.of_nat n) with lo in FR by lia. exists junk. exact FR.
Qed.

Lemma cells_hjunk : forall m lo cs, rw_cells asegs m lo cs -> 0x647000 <= lo -> hjunk m lo (lo + Z.of_nat (cells_size cs)).
Proof.
intros m lo cs RC Hlo. apply stk_hjunk; [|exact Hlo].
pose proof (stk_of_rw_cells asegs m lo cs RC) as ST. exact ST.
Qed.

Lemma cells_hjunk_oh : forall m lo cs, rw_cells asegs m lo cs ->
(0 <= lo /\ lo + Z.of_nat (cells_size cs) <= 0x10000) \/ 0x647000 <= lo -> hjunk m lo (lo + Z.of_nat (cells_size cs)).
Proof.
intros m lo cs RC Hlo. apply stk_hjunk_oh; [|exact Hlo].
pose proof (stk_of_rw_cells asegs m lo cs RC) as ST. exact ST.
Qed.

Definition RStats (RE : aentry) (X : rlay) (m : mem) : Prop :=
hjunk m (rl_T X + 2800) (rl_T X + 3168)
/\ (exists e, rw_cells asegs m A_ERRNO [C4 e])
/\ (exists b, rw_cells asegs m 0x174420 [C1 b]).

Lemma RStats_frame : forall RE X m m', RStats RE X m -> wmono asegs m m' -> agree_on asegs (fp_RStats RE X) m m' -> RStats RE X m'.
Proof.
intros RE X m m' (H1 & [e H2] & [b H3]) WM AG. split; [eapply hjunk_wmono; eassumption|]. split.
- exists e. eapply rw_cells_agree; [exact AG| exact H2|]. intros z Hz. right; left. cbn [cells_size csize Nat.add] in Hz. split; cbn [fst snd]; lia.
- exists b. eapply rw_cells_agree; [exact AG| exact H3|]. intros z Hz. right; right. cbn [cells_size csize Nat.add] in Hz. lia.
Qed.

Definition ri_addr (RE : aentry) (c : Z) : Z := region_info RE + 128 * c.
Definition pc_addr (X : rlay) (c : Z) : Z := rl_T X + 208 + 80 * c.

Definition coff (c i : Z) : Z := i * (class_size c / 16).

Record pcls : Type := mkPK { pk_fl : list Z; pk_ca : list Z }.

Definition ri_cells (x : cstate) (j1 j2 j3 j4 : list byte) : list cell :=
[ C8 (wz 0); CB 8 j1; C8 (wz (c_num_freed x)); C8 (wz (c_mapped_fa x)); C8 (wz (c_alloc_user x)); C8 (wz 0);
C8 (wz (c_mapped_user x)); C8 (wz 0); CB 4 j2; C1 (b8 0); CB 3 j3; CB 56 j4 ].

Definition bsize (c : Z) : Z := if c =? 31 then 64 else class_size c.
Definition bmax (c : Z) : Z := if c =? 31 then 16 else max_count c.
Lemma bsize_eq : forall c, c <> 31 -> bsize c = class_size c.
Proof. intros c H. unfold bsize. destruct (Z.eqb_spec c 31); [lia| reflexivity]. Qed.
Lemma bmax_eq : forall c, c <> 31 -> bmax c = max_count c.
Proof. intros c H. unfold bmax. destruct (Z.eqb_spec c 31); [lia| reflexivity]. Qed.

Definition pc_cells (inited : bool) (c : Z) (x : cstate) : list cell :=
[ C4 (wz (c_count x)); C4 (wz (if inited then bmax c else 0)); C8 (wz (if inited then bsize c else 0)) ].

Definition fa_byte : byte := b8 0xfa.

Section PerClass.
Variables (a : AState) (G : ghost) (RE : aentry) (X : rlay) (m : mem) (c : Z) (K : pcls).
Let x := cls a c.
Let sz := class_size c.
Let rb := reg_beg (ae_L RE) c.
Let FL := pk_fl K.
Let CA := pk_ca K.

Definition cr_cells : Prop :=
(exists j1 j2 j3 j4, rw_cells asegs m (ri_addr RE c) (ri_cells x j1 j2 j3 j4))
/\ rw_cells asegs m (pc_addr X c) (pc_cells (as_cache_inited a) c x)
/\ (exists CH, u32arr asegs m (pc_addr X c + 16) CH /\ length CH = 16%nat
/\ forall j, (j < length CA)%nat -> nth_error CH j = Some (wz (coff c (nth j CA 0)))).

Definition cr_pure : Prop :=
Z.of_nat (length FL) = c_num_freed x /\ Z.of_nat (length CA) = c_count x
/\ List.NoDup FL /\ List.NoDup CA
/\ (forall i, In i FL -> tag_at G c i = Some TFree) /\ (forall i, In i CA -> tag_at G c i = Some TCached)
/\ count_tag (stag_eqb TFree) (G c) = c_num_freed x /\ count_tag (stag_eqb TCached) (G c) = c_count x
/\ 0 <= c_count x <= max_count c /\ (as_cache_inited a = false -> c_count x = 0)
/\ 0 <= c_num_freed x /\ 4 * c_num_freed x <= c_mapped_fa x /\ c_mapped_fa x <= kFreeArraySize
/\ c_mapped_fa x mod kFreeArrayMapSize = 0
/\ (c = 0 -> x = cst0)
/\ Z.of_nat (length (G c)) * sz = c_alloc_user x /\ 0 <= c_alloc_user x /\ c_alloc_user x <= c_mapped_user x
/\ c_mapped_user x <= kFreeArrayOffset /\ c_mapped_user x mod kUserMapSize = 0.

Definition cr_region : Prop :=
1 <= c ->

u32arr asegs m (fa_beg (ae_L RE) c) (map (fun i => wz (coff c i)) FL)
/\ hjunk m (fa_beg (ae_L RE) c + 4 * c_num_freed x) (fa_beg (ae_L RE) c + c_mapped_fa x)

/\ (forall i t, tag_at G c i = Some t -> tag_prim t = true -> hjunk m (slot_beg RE c i) (slot_beg RE c i + sz))
/\ hjunk m (rb + c_alloc_user x) (rb + c_mapped_user x)

/\ (forall i t, tag_at G c i = Some t -> tag_prim t = true ->
rw_cells asegs m (SH (slot_beg RE c i)) [CB (Z.to_nat (sz / 8)) (repeat fa_byte (Z.to_nat (sz / 8)))])
/\ rw_cells asegs m (SH (rb + c_alloc_user x))
[CB (Z.to_nat ((c_mapped_user x - c_alloc_user x) / 8)) (repeat fa_byte (Z.to_nat ((c_mapped_user x - c_alloc_user x) / 8)))]
/\ hjunk m (SH (rb + c_mapped_user x)) (SH (rb + kFreeArrayOffset))
/\ hjunk m (SH (fa_beg (ae_L RE) c)) (SH (fa_beg (ae_L RE) c + kFreeArraySize)).

Definition class_rep : Prop := cr_cells /\ cr_pure /\ cr_region.
End PerClass.

Definition RPrim (a : AState) (G : ghost) (RE : aentry) (X : rlay) (m : mem) : Prop :=
exists K : Z -> pcls,
hjunk m (rl_T X + 2768) (rl_T X + 2800)
/\ (forall c, G c <> [] -> 1 <= c < kNumClasses)
/\ forall c, 0 <= c < kNumClasses -> class_rep a G RE X m c (K c).

Lemma hjunk_agree : forall (P : Z -> Prop) m m' lo hi,
agree_on asegs P m m' -> hjunk m lo hi -> (forall a, lo <= a < hi -> P a) -> hjunk m' lo hi.
Proof.
intros P m m' lo hi AG (H1 & H2 & H) HP. split; [exact H1|]. split; [exact H2|]. intros a Ha.
destruct (H a Ha) as [b Hb]. destruct (AG a ltac:(lia) (HP a Ha)) as [E _]. exists b. rewrite E. exact Hb.
Qed.

Lemma tag_at_lt : forall G c i t, tag_at G c i = Some t -> 0 <= i /\ i + 1 <= Z.of_nat (length (G c)).
Proof.
intros G c i t Ht. unfold tag_at in Ht. destruct (Z.ltb_spec i 0); [discriminate|].
assert (Hlen : (Z.to_nat i < length (G c))%nat) by (apply (proj1 (nth_error_Some (G c) (Z.to_nat i))); rewrite Ht; discriminate).
lia.
Qed.

Lemma tag_at_inj : forall G c i t t', tag_at G c i = Some t -> tag_at G c i = Some t' -> t = t'.
Proof. intros G c i t t' H1 H2. rewrite H1 in H2. inversion H2. reflexivity. Qed.

Lemma SH_plus8 : forall a k, SH (a + 8 * k) = SH a + k.
Proof. intros a k. unfold SH. rewrite (Z.mul_comm 8 k), Z.div_add by lia. lia. Qed.

Lemma SH_le : forall a b, a <= b -> SH a <= SH b.
Proof. intros a b H. unfold SH. Z.div_mod_to_equations. lia. Qed.

Lemma slots_apart : forall i i' sz, 0 < sz -> 0 <= i -> 0 <= i' -> i <> i' ->
i * sz + sz <= i' * sz \/ i' * sz + sz <= i * sz.
Proof. intros i i' sz Hs Hi Hi' NE. assert (i + 1 <= i' \/ i' + 1 <= i) as [D|D] by lia; [left|right]; nia. Qed.

Section RPrimFrame.
Variables (a : AState) (G : ghost) (RE : aentry) (X : rlay).

Lemma rprim_slot_geom : forall (K : Z -> pcls) m c i t,
(forall c, G c <> [] -> 1 <= c < kNumClasses) ->
(forall c, 0 <= c < kNumClasses -> class_rep a G RE X m c (K c)) ->
tag_at G c i = Some t ->
1 <= c <= 31 /\ 0 <= i /\ 32 <= class_size c /\ class_size c mod 32 = 0
/\ reg_beg (ae_L RE) c = al_space_beg (ae_L RE) + c * 2^32
/\ reg_beg (ae_L RE) c <= slot_beg RE c i
/\ slot_beg RE c i + class_size c <= reg_beg (ae_L RE) c + c_alloc_user (cls a c)
/\ c_alloc_user (cls a c) <= c_mapped_user (cls a c) /\ c_mapped_user (cls a c) <= kFreeArrayOffset
/\ slot_beg RE c i = reg_beg (ae_L RE) c + i * class_size c
/\ exists k, 0 <= k /\ i * class_size c = 8 * k /\ class_size c = 8 * (class_size c / 8) /\ (i + 1) * class_size c <= c_alloc_user (cls a c).
Proof.
intros K m c i t GNE HC Ht. pose proof (tag_at_lt G c i t Ht) as [I1 I2].
assert (NE : G c <> []) by (intros E; rewrite E in I2; cbn in I2; lia).
pose proof (GNE c NE) as Hc. pose proof kconsts as (KR & KO & KS & K32 & _). rewrite K32 in Hc.
destruct (HC c ltac:(rewrite K32; lia)) as (_ & PU & _).
destruct PU as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G1 & G2 & G3 & G4 & G5).
pose proof (class_size_facts c ltac:(lia)) as [S1 S2].
assert (E8 : class_size c = 8 * (class_size c / 8)) by (Z.div_mod_to_equations; lia).
assert (RB : reg_beg (ae_L RE) c = al_space_beg (ae_L RE) + c * 2^32) by (unfold reg_beg; rewrite KR; reflexivity).
assert (SB : slot_beg RE c i = reg_beg (ae_L RE) c + i * class_size c) by reflexivity.
assert (IL : (i + 1) * class_size c <= c_alloc_user (cls a c)) by (first [ clear - E8 S2 S1 G5 G4 G3 G2 G1 KO I2 I1 i c G a; nia | nia ]).
split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact RB|].
split; [rewrite SB; (first [ clear - IL E8 S2 S1 G5 G4 G3 G2 G1 KO I2 I1 i c RE G a; nia | nia ])|]. split; [rewrite SB; nia|]. split; [lia|]. split; [lia|]. split; [exact SB|].
exists (i * (class_size c / 8)). split; [(first [ clear - IL E8 S2 S1 G5 G4 G3 G2 G1 KO I2 I1 i c G a; nia | nia ])|]. split; [(first [ clear - E8 S1 i c G a; nia | nia ])|]. split; [exact E8| exact IL].
Qed.

Lemma RPrim_frame : forall m m', RPrim a G RE X m -> wmono asegs m m' -> agree_on asegs (fp_RPrim G RE X) m m' -> RPrim a G RE X m'.
Proof.
intros m m' (K & HJ & GNE & HCall) _ AG. exists K. pose proof kconsts as (KR & KO & KS & K32 & KP & KU & KM & KX).
split.
{ eapply hjunk_agree; [exact AG| exact HJ|]. intros z Hz. right; left. split; cbn [fst snd]; lia. }
split; [exact GNE|].
intros c Hc. pose proof (HCall c Hc) as HC. rewrite K32 in Hc.
destruct HC as (((j1 & j2 & j3 & j4 & RI) & PC & (CH & ACH & LCH & HCH)) & PU & REG).
pose proof PU as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15 & G1 & G2 & G3 & G4 & G5). rewrite KM in G5.
assert (INRI : forall z, ri_addr RE c <= z < ri_addr RE c + 128 -> fp_RPrim G RE X z).
{ intros z Hz. left. unfold ri_addr in Hz. split; cbn [fst snd]; lia. }
assert (INPC : forall z, pc_addr X c <= z < pc_addr X c + 80 -> fp_RPrim G RE X z).
{ intros z Hz. right; left. unfold pc_addr in Hz. split; cbn [fst snd]; lia. }
split; [split; [|split]|split].
- exists j1, j2, j3, j4. eapply rw_cells_agree; [exact AG| exact RI|]. intros z Hz. apply INRI. cbn [ri_cells cells_size csize Nat.add] in Hz. lia.
- eapply rw_cells_agree; [exact AG| exact PC|]. intros z Hz. apply INPC. cbn [pc_cells cells_size csize Nat.add] in Hz. lia.
- exists CH. split; [|split; [exact LCH| exact HCH]]. eapply u32arr_agree; [exact AG| exact ACH|]. intros z Hz. apply INPC. rewrite LCH in Hz. cbn in Hz. lia.
- exact PU.
- intros Hc1. specialize (REG Hc1). destruct REG as (FA & FJ & SL & UT & SS & US & UJ & FS).
assert (HCL : 1 <= c <= 31) by lia.
pose proof (class_size_facts c HCL) as [SZ1 SZ2].
assert (RB : reg_beg (ae_L RE) c = al_space_beg (ae_L RE) + c * 2^32) by (unfold reg_beg; rewrite KR; reflexivity).
assert (FB : fa_beg (ae_L RE) c = reg_beg (ae_L RE) c + kFreeArrayOffset) by reflexivity.
assert (INFA : forall z, fa_beg (ae_L RE) c <= z < fa_beg (ae_L RE) c + kFreeArraySize -> fp_RPrim G RE X z).
{ intros z Hz. right; right; left. exists c. rewrite K32. split; [lia| exact Hz]. }
assert (INFS : forall z, SH (fa_beg (ae_L RE) c) <= z < SH (fa_beg (ae_L RE) c) + kFreeArraySize / 8 -> fp_RPrim G RE X z).
{ intros z Hz. right; right; right; left. exists c. rewrite K32. split; [lia|]. split; cbn [fst snd]; lia. }

assert (NSU : forall z, reg_beg (ae_L RE) c <= z < reg_beg (ae_L RE) c + kFreeArrayOffset ->
(forall i' t', tag_at G c i' = Some t' -> tag_prim t' = false -> ~ (slot_beg RE c i' <= z < slot_beg RE c i' + class_size c)) ->
fp_RPrim G RE X z).
{ intros z Hz NS. do 4 right; left. split; [exists c; rewrite K32; split; [lia| exact Hz]|].
intros (c' & i' & t' & Ht' & Hf & [Hin1 Hin2]). cbn [fst snd] in Hin1, Hin2.
destruct (Z.eq_dec c' c) as [->|NE].
- apply (NS i' t' Ht'); [destruct (tag_prim t'); [discriminate| reflexivity]| lia].
- pose proof (rprim_slot_geom K m c' i' t' GNE HCall Ht') as (C1 & _ & S1 & _ & RB' & R1 & R2 & B1 & B2 & _).
rewrite RB' in R1, R2. rewrite RB in Hz. rewrite KO in *. clear - Hz Hin1 Hin2 NE C1 S1 R1 R2 B1 B2 HCL. lia. }
assert (NSS : forall z, in_sh (reg_beg (ae_L RE) c, kFreeArrayOffset) z ->
(forall i' t', tag_at G c i' = Some t' -> tag_prim t' = false -> ~ in_sh (slot_beg RE c i', class_size c) z) ->
fp_RPrim G RE X z).
{ intros z Hz NS. do 5 right. split; [exists c; rewrite K32; split; [lia| exact Hz]|].
intros (c' & i' & t' & Ht' & Hf & Hin).
destruct (Z.eq_dec c' c) as [->|NE].
- apply (NS i' t' Ht'); [destruct (tag_prim t'); [discriminate| reflexivity]| exact Hin].
- pose proof (rprim_slot_geom K m c' i' t' GNE HCall Ht') as (C1 & I1 & S1 & S2 & RB' & R1 & R2 & B1 & B2 & SB' & k' & K0 & K1 & K2 & K3).
destruct Hz as [Z1 Z2]. destruct Hin as [Y1 Y2]. cbn [fst snd] in Z1, Z2, Y1, Y2.
rewrite SB', RB' in Y1, Y2. rewrite RB in Z1, Z2. rewrite KO in *.
replace (al_space_beg (ae_L RE) + c' * 2^32 + i' * class_size c') with (al_space_beg (ae_L RE) + 8 * (c' * 2^29 + k')) in Y1, Y2 by lia.
replace (al_space_beg (ae_L RE) + c * 2^32) with (al_space_beg (ae_L RE) + 8 * (c * 2^29)) in Z1, Z2 by lia.
rewrite !SH_plus8 in Y1, Y2, Z1, Z2. rewrite K2 in Y2.
replace (8 * (class_size c' / 8) / 8) with (class_size c' / 8) in Y2 by (rewrite Z.mul_comm, Z.div_mul by lia; reflexivity).
change (3758096384 / 8) with 469762048 in Z2.
clear - Z1 Z2 Y1 Y2 NE C1 I1 S1 K0 K1 K2 K3 B1 B2 HCL. lia. }
assert (KO8 : kFreeArrayOffset = 8 * 469762048) by (rewrite KO; reflexivity).
assert (KS8 : kFreeArraySize = 8 * 67108864) by (rewrite KS; reflexivity).
assert (AU8 : exists q, 0 <= q /\ c_alloc_user (cls a c) = 8 * q).
{ exists (Z.of_nat (length (G c)) * (class_size c / 8)). split; [(first [ clear - KS8 SZ1 G3 G2 G1 LCH CH c K G a; nia | nia ])|]. rewrite <- G1. Z.div_mod_to_equations. (first [ clear - H26 H25 H19 q3 H14 q2 H5 H4 r0 H0 H r KS8 KO8 q0 SZ2 r2 SZ1 G5 r3 G4 G3 G2 G1 P14 r4 q LCH CH c K G a; nia | nia ]). }
destruct AU8 as (qa & QA0 & QA).
assert (MU8 : exists q, c_mapped_user (cls a c) = 8 * q) by (exists (c_mapped_user (cls a c) / 8); Z.div_mod_to_equations; (first [ clear - H31 H30 H24 q4 H0 H r q G5 r4 P14 r5 LCH CH c K G a; lia | lia ])).
destruct MU8 as (qm & QM).
split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]].
+
eapply u32arr_agree; [exact AG| exact FA|]. intros z Hz. rewrite map_length in Hz. apply INFA. lia.
+ eapply hjunk_agree; [exact AG| exact FJ|]. intros z Hz. apply INFA. lia.
+
intros i t Ht Hp. eapply hjunk_agree; [exact AG| exact (SL i t Ht Hp)|]. intros z Hz.
pose proof (rprim_slot_geom K m c i t GNE HCall Ht) as (_ & I1 & _ & _ & _ & R1 & R2 & _ & _ & SB & _).
apply NSU; [lia|]. intros i' t' Ht' Hf [Y1 Y2].
pose proof (rprim_slot_geom K m c i' t' GNE HCall Ht') as (_ & I1' & _ & _ & _ & R1' & R2' & _ & _ & SB' & _).
destruct (Z.eq_dec i i') as [->|NE]; [pose proof (tag_at_inj _ _ _ _ _ Ht Ht') as <-; rewrite Hp in Hf; discriminate|].
rewrite SB in Hz. rewrite SB' in Y1, Y2. pose proof (slots_apart i i' (class_size c) ltac:(lia) I1 I1' NE). clear - Hz Y1 Y2 H. lia.
+
eapply hjunk_agree; [exact AG| exact UT|]. intros z Hz. apply NSU; [lia|]. intros i' t' Ht' Hf [Y1 Y2].
pose proof (rprim_slot_geom K m c i' t' GNE HCall Ht') as (_ & _ & _ & _ & _ & R1' & R2' & _). lia.
+
intros i t Ht Hp. eapply rw_cells_agree; [exact AG| exact (SS i t Ht Hp)|]. intros z Hz.
cbn [cells_size csize] in Hz. rewrite Nat.add_0_r, Z2Nat.id in Hz by lia.
pose proof (rprim_slot_geom K m c i t GNE HCall Ht) as (_ & I1 & _ & _ & _ & R1 & R2 & _ & _ & SB & k & K0 & K1 & K2 & K3).
rewrite SB, K1, SH_plus8 in Hz.
apply NSS.
* split; cbn [fst snd]; [clear - Hz K0 K1 K2 K3 G3 G4; lia|]. rewrite KO8, Z.mul_comm, Z.div_mul by lia. clear - Hz K0 K1 K2 K3 G3 G4 SZ1 KO8. lia.
* intros i' t' Ht' Hf [Y1 Y2]. cbn [fst snd] in Y1, Y2.
pose proof (rprim_slot_geom K m c i' t' GNE HCall Ht') as (_ & I1' & _ & _ & _ & R1' & R2' & _ & _ & SB' & k' & K0' & K1' & K2' & K3').
destruct (Z.eq_dec i i') as [->|NE]; [pose proof (tag_at_inj _ _ _ _ _ Ht Ht') as <-; rewrite Hp in Hf; discriminate|].
rewrite SB', K1', SH_plus8 in Y1, Y2.
pose proof (slots_apart i i' (class_size c) ltac:(lia) I1 I1' NE) as D. clear - Hz Y1 Y2 D K1 K1' K2 SZ1. lia.
+
eapply rw_cells_agree; [exact AG| exact US|]. intros z Hz.
cbn [cells_size csize] in Hz. rewrite Nat.add_0_r, Z2Nat.id in Hz by (Z.div_mod_to_equations; lia).
rewrite QA, QM in Hz. replace (8 * qm - 8 * qa) with (8 * (qm - qa)) in Hz by lia.
rewrite SH_plus8 in Hz. rewrite (Z.mul_comm 8 (qm - qa)), Z.div_mul in Hz by lia.
apply NSS.
* split; cbn [fst snd]; [clear - Hz QA0 QA QM G3; lia|]. rewrite KO8, Z.mul_comm, Z.div_mul by lia. clear - Hz QA0 QA QM G3 G4 KO8; lia.
* intros i' t' Ht' Hf [Y1 Y2]. cbn [fst snd] in Y1, Y2.
pose proof (rprim_slot_geom K m c i' t' GNE HCall Ht') as (_ & I1' & _ & _ & _ & R1' & R2' & _ & _ & SB' & k' & K0' & K1' & K2' & K3').
rewrite SB', K1', SH_plus8 in Y1, Y2. clear - Hz Y1 Y2 K0' K1' K2' K3' QA QA0 SZ1. lia.
+
eapply hjunk_agree; [exact AG| exact UJ|]. intros z Hz. rewrite QM, KO8, !SH_plus8 in Hz.
apply NSS.
* split; cbn [fst snd]; [clear - Hz QM G3 G2; lia|]. rewrite KO8, Z.mul_comm, Z.div_mul by lia. clear - Hz QM G3 G2 G4 KO8; lia.
* intros i' t' Ht' Hf [Y1 Y2]. cbn [fst snd] in Y1, Y2.
pose proof (rprim_slot_geom K m c i' t' GNE HCall Ht') as (_ & I1' & _ & _ & _ & R1' & R2' & _ & _ & SB' & k' & K0' & K1' & K2' & K3').
rewrite SB', K1', SH_plus8 in Y1, Y2. clear - Hz Y1 Y2 K0' K1' K2' K3' QM G3 SZ1. lia.
+
eapply hjunk_agree; [exact AG| exact FS|]. intros z Hz. rewrite KS8, SH_plus8 in Hz. apply INFS. rewrite KS8, Z.mul_comm, Z.div_mul by lia. lia.
Qed.
End RPrimFrame.

Definition kMagic : Z := 0xCC6E96B9CC6E96B9.

Definition hdr_cells (b1 n' : Z) (id : word) : list cell :=
[C1 (b8 2); C1 (b8 b1); C2 (wz 0); C4 (wz n'); C8 id].

Definition ush (n' : Z) : list byte :=
repeat (b8 0) (Z.to_nat (n' / 8)) ++ (if n' mod 8 =? 0 then [] else [b8 (n' mod 8)]).
Definition ngran (n' : Z) : Z := (n' + 7) / 8.

Definition fas (k : Z) : list byte := repeat fa_byte (Z.to_nat k).

Definition chunk_cont (p : aptr) (A n : Z) : Z * Z :=
match p with
| APrim _ _ => (A - rz_size n, A - rz_size n + class_size (class_of n))
| ASec mb _ => (mb + kPage, mb + sec_map_size n)
end.

Section ChunkRep.
Context {BAND : Band}.
Variables (m : mem) (lo hi A n : Z).
Let n' := used_size n.
Let rz := A - lo.
Let up := A + round_up n' 8.

Definition chunk_mem : Prop :=
(16 < rz -> rw_cells asegs m lo [C8 (wz kMagic); C8 (wz (A - 16))] /\ hjunk m (lo + 16) (A - 16))
/\ (exists b1 id, (b1 = 0x11 \/ b1 = 0x91) /\ rw_cells asegs m (A - 16) (hdr_cells b1 n' id))
/\ wr_at asegs m A n'
/\ hjunk m (A + n) hi
/\ rw_cells asegs m (SH lo) [CB (Z.to_nat (rz / 8)) (fas (rz / 8)); CB (Z.to_nat (ngran n')) (ush n'); CB (Z.to_nat ((hi - up) / 8)) (fas ((hi - up) / 8))]

/\ lo mod 16 = 0 /\ A mod 16 = 0 /\ rz mod 16 = 0 /\ 16 <= rz /\ hi mod 8 = 0 /\ up <= hi /\ 0 <= n
/\ (lowhigh lo (hi - lo) /\ off_hull lo (hi - lo)) /\ hi <= band_lo.
End ChunkRep.

Definition chunk_rep {BAND : Band} (a : AState) (G : ghost) (RE : aentry) (m : mem) (p : aptr) (A n : Z) : Prop :=
match p with
| APrim _ n0 => n0 = n /\ exists i, tag_at G (class_of n) i = Some (TLive p)
/\ A = slot_beg RE (class_of n) i + rz_size n
/\ chunk_mem m (slot_beg RE (class_of n) i) (slot_beg RE (class_of n) i + class_size (class_of n)) A n
| ASec mb n0 => n0 = n /\ In (mkSec mb (sec_map_size n) n) (as_reg a) /\ A = mb + kSecUserOff
/\ chunk_mem m (mb + kPage) (mb + sec_map_size n) A n
end.

Definition RChunks {BAND : Band} (a : AState) (LB : list ablock) (G : ghost) (RE : aentry) (X : rlay) (m : mem) : Prop :=
(forall p A n, In (p, A, n) LB -> chunk_rep a G RE m p A n)
/\ (forall p A n p' A' n' z, In (p, A, n) LB -> In (p', A', n') LB -> (p, A, n) <> (p', A', n') ->
in_iv (fst (chunk_cont p A n), snd (chunk_cont p A n) - fst (chunk_cont p A n)) z ->
in_iv (fst (chunk_cont p' A' n'), snd (chunk_cont p' A' n') - fst (chunk_cont p' A' n')) z -> False).

Lemma RChunks_perm {BAND : Band} : forall a LB LB' G RE X m, RChunks a LB G RE X m -> Permutation LB LB' -> RChunks a LB' G RE X m.
Proof.
intros a LB LB' G RE X m [H1 H2] P. split.
- intros p A n Hin. apply H1. eapply Permutation_in; [apply Permutation_sym; exact P| exact Hin].
- intros p A n p' A' n' z I1 I2. apply H2; eapply Permutation_in; try (apply Permutation_sym; exact P); assumption.
Qed.

Lemma chunk_rep_cont {BAND : Band} : forall a G RE m p A n, chunk_rep a G RE m p A n ->
let lo := fst (chunk_cont p A n) in let hi := snd (chunk_cont p A n) in
chunk_mem m lo hi A n /\ lo + 16 <= A /\ A + Z.max n 1 <= hi /\ (lowhigh lo (hi - lo) /\ off_hull lo (hi - lo)) /\ hi <= band_lo.
Proof.
intros a G RE m p A n CR. destruct p as [id n0|mb n0]; cbn [chunk_rep chunk_cont fst snd] in *.
- destruct CR as (-> & i & Ht & HA & CM). replace (A - rz_size n) with (slot_beg RE (class_of n) i) by lia.
pose proof CM as (_ & _ & _ & _ & _ & M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9).
pose proof (round_up_ge (used_size n) 8 ltac:(lia)) as (U1 & _). unfold used_size in U1, M6.
cbv zeta. split; [exact CM|]. lia.
- destruct CR as (-> & Hin & HA & CM).
pose proof CM as (_ & _ & _ & _ & _ & M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9).
pose proof (round_up_ge (used_size n) 8 ltac:(lia)) as (U1 & _). unfold used_size in U1, M6.
cbv zeta. split; [exact CM|]. lia.
Qed.

Lemma bytes_at_repeat_nth : forall m A b N k, bytes_at asegs m A (repeat b N) -> (k < N)%nat ->
bytes_at asegs m (A + Z.of_nat k) [b].
Proof.
intros m A b N k H Hk. replace N with (k + (1 + (N - k - 1)))%nat in H by lia.
rewrite repeat_app in H. apply bytes_at_app in H as [_ H]. rewrite repeat_length in H.
rewrite repeat_app in H. apply bytes_at_app in H as [H _]. exact H.
Qed.

Lemma RChunks_shadow {BAND : Band} : forall a LB FS G RE X m p A n,
gcons a LB FS G RE X -> RChunks a LB G RE X m -> In (p, A, n) LB -> blk_shadow asegs m A n.
Proof.
intros a LB FS G RE X m p A n _ [H1 _] Hin.
destruct (chunk_rep_cont a G RE m p A n (H1 p A n Hin)) as (CM & C1 & C2 & C3 & C4).
set (lo := fst (chunk_cont p A n)) in *. set (hi := snd (chunk_cont p A n)) in *. clearbody lo hi.
destruct CM as (_ & _ & _ & _ & SHD & M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9).
assert (RZ8 : exists q, A - lo = 8 * q /\ 2 <= q) by (exists ((A - lo) / 16 * 2); Z.div_mod_to_equations; (first [ clear - H25 q4 H20 q3 H15 q2 H q C3 C2 C1 M8 M5 r2 M3 r M2 r3 M1 r4 hi lo n A BAND; lia | lia ])).
destruct RZ8 as (q & Q1 & Q2).
unfold blk_shadow. lits. split; [clear -C1 C3; lia|]. split; [clear -M2; Z.div_mod_to_equations; lia|]. split; [exact M7|]. split.
{ clear - C2 C4 M7. unfold SH, A_SHADOW_OFS. Z.div_mod_to_equations. lia. }
intros k Hk Hkn.

destruct SHD as [[WF BA] WR]. cbn [cells_bytes cbytes app] in BA. rewrite app_nil_r in BA.
apply bytes_at_app in BA as [_ BA]. rewrite repeat_length, Z2Nat.id in BA by lia.
replace (A - lo) with (8 * q) in BA by lia. rewrite Z.mul_comm, Z.div_mul in BA by lia.
replace (SH lo + q) with (SH A) in BA by (replace A with (lo + 8 * q) by lia; rewrite SH_plus8; lia).
apply bytes_at_app in BA as [BA _].
unfold ush in BA. unfold used_size in BA.
assert (NN : Z.max n 1 = n) by lia. rewrite NN in BA.
destruct (Z.le_gt_cases (8 * k + 8) n) as [FULL|PART].
-
apply bytes_at_app in BA as [BA _].
rewrite (gran_full n k FULL).
assert (HK : (Z.to_nat k < Z.to_nat (n / 8))%nat) by (Z.div_mod_to_equations; (first [ clear - H30 q6 H15 q3 H0 H r FULL NN Hk k Q1 C3 C2 C1 M8 M5 r2 M1 r5 q0 q hi lo n A BAND; lia | lia ])).
pose proof (bytes_at_repeat_nth m (SH A) (b8 0) _ _ BA HK) as RD. rewrite Z2Nat.id in RD by lia. exact RD.
-
assert (HK : k = n / 8) by (Z.div_mod_to_equations; (first [ clear - H30 q6 H15 q3 H0 H PART NN Hkn k Q1 C3 C2 C1 M8 M5 r2 M1 r5 r q0 q hi lo n A BAND; lia | lia ])).
assert (HM : n mod 8 <> 0) by (Z.div_mod_to_equations; lia).
destruct (Z.eqb_spec (n mod 8) 0) as [E|_]; [lia|].
apply bytes_at_app in BA as [_ BA]. rewrite repeat_length, Z2Nat.id in BA by lia. rewrite <- HK in BA.
unfold gran. destruct (Z.leb_spec (8 * k + 8) n); [lia|].
replace (n - 8 * k) with (n mod 8) by (Z.div_mod_to_equations; (first [ clear - H31 q6 H16 q3 H2 H0 HM HK q0 NN Q1 C3 C2 C1 M8 M5 r2 M1 r5 r k q hi lo n A BAND; lia | lia ])). exact BA.
Qed.

Lemma nonuser_not_live {BAND : Band} : forall a LB G RE X m p A n z,
RChunks a LB G RE X m -> In (p, A, n) LB ->
fst (chunk_cont p A n) <= z < snd (chunk_cont p A n) -> ~ (A <= z < A + n) -> ~ in_live_user LB z.
Proof.
intros a LB G RE X m p A n z [H1 H2] Hin Hz NU (b' & Hin' & Hz').
destruct b' as [[p' A'] n']. cbn [ablk_addr ablk_size fst snd] in Hz'.
destruct (decide ((p, A, n) = (p', A', n'))) as [E|NE].
- inversion E; subst. exact (NU Hz').
- destruct (chunk_rep_cont a G RE m p' A' n' (H1 _ _ _ Hin')) as (_ & C1 & C2 & C3 & C4).
eapply (H2 p A n p' A' n' z Hin Hin' NE); split; cbn [fst snd]; lia.
Qed.

Lemma ngran_eq : forall n', 0 <= n' -> ngran n' = round_up n' 8 / 8 /\ 0 <= ngran n' /\ round_up n' 8 = 8 * ngran n'.
Proof. intros n' H. unfold ngran, round_up. Z.div_mod_to_equations. nia. Qed.

Lemma RChunks_frame {BAND : Band} : forall a LB G RE X m m',
RChunks a LB G RE X m -> wmono asegs m m' -> agree_on asegs (fp_RChunks a LB G RE X) m m' -> RChunks a LB G RE X m'.
Proof.
intros a LB G RE X m m' RC WM AG. pose proof RC as [H1 H2]. split; [|exact H2].
intros p A n Hin. pose proof (H1 p A n Hin) as CR.
pose proof (chunk_rep_cont a G RE m p A n CR) as (CM & C1 & C2 & C3 & C4).

assert (INC : forall z, fst (chunk_cont p A n) <= z < snd (chunk_cont p A n) -> ~ (A <= z < A + n) -> fp_RChunks a LB G RE X z).
{ intros z Hz NU. left. split; [| eapply nonuser_not_live; eassumption].
destruct p as [id n0|mb n0]; cbn [chunk_rep chunk_cont fst snd] in CR, Hz |- *.
- destruct CR as (-> & i & Ht & HA & _). left. exists (class_of n), i, (TLive (APrim id n)).
split; [exact Ht|]. split; [reflexivity|]. split; cbn [fst snd]; lia.
- destruct CR as (-> & HR & HA & _). right. exists (mkSec mb (sec_map_size n) n). cbn [se_beg se_size se_req].
split; [exact HR|]. split; [exists A; exact Hin| lia]. }
assert (INS : forall z, in_sh (fst (chunk_cont p A n), snd (chunk_cont p A n) - fst (chunk_cont p A n)) z -> fp_RChunks a LB G RE X z).
{ intros z Hz. right.
destruct p as [id n0|mb n0]; cbn [chunk_rep chunk_cont fst snd] in CR, Hz |- *.
- destruct CR as (-> & i & Ht & HA & _). left. exists (class_of n), i, (TLive (APrim id n)).
split; [exact Ht|]. split; [reflexivity|]. replace (slot_beg RE (class_of n) i) with (A - rz_size n) by lia.
destruct Hz as [Z1 Z2]; cbn [fst snd] in Z1, Z2. split; cbn [fst snd]; lia.
- destruct CR as (-> & HR & HA & _). right. exists (mkSec mb (sec_map_size n) n). cbn [se_beg se_size se_req].
split; [exact HR|]. split; [exists A; exact Hin|].
destruct Hz as [Z1 Z2]; cbn [fst snd] in Z1, Z2. split; cbn [fst snd]; lia. }
set (lo := fst (chunk_cont p A n)) in *. set (hi := snd (chunk_cont p A n)) in *.
assert (TRANS : chunk_mem m' lo hi A n).
{ destruct CM as (LEFT & (b1 & id & B1 & HDR) & WR & RIGHT & SHD & PURE).
pose proof PURE as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9).
pose proof (round_up_ge (used_size n) 8 ltac:(lia)) as (U1 & U2 & U3). pose proof (ngran_eq (used_size n) ltac:(unfold used_size; lia)) as (N1 & N2 & N3).
split; [|split; [|split; [|split; [|split; [|exact PURE]]]]].
- intros Hrz. destruct (LEFT Hrz) as [L1 L2]. split.
+ eapply rw_cells_agree; [exact AG| exact L1|]. intros z Hz. cbn [cells_size csize Nat.add] in Hz. apply INC; clearbody lo hi; lia.
+ eapply hjunk_agree; [exact AG| exact L2|]. intros z Hz. apply INC; clearbody lo hi; lia.
- exists b1, id. split; [exact B1|]. eapply rw_cells_agree; [exact AG| exact HDR|]. intros z Hz. cbn [hdr_cells cells_size csize Nat.add] in Hz. apply INC; clearbody lo hi; lia.
- eapply wr_at_transport; [exact WR| exact WM].
- eapply hjunk_agree; [exact AG| exact RIGHT|]. intros z Hz. apply INC; clearbody lo hi; unfold used_size in *; lia.
- eapply rw_cells_agree; [exact AG| exact SHD|]. intros z Hz. apply INS.
cbn [cells_size csize] in Hz. unfold fas in Hz. rewrite !Nat.add_0_r in Hz.
rewrite !Nat2Z.inj_add, !Z2Nat.id in Hz by (clearbody lo hi; unfold used_size in *; Z.div_mod_to_equations; (first [ clear - H26 q4 H16 q2 H0 H r Hz z N3 N1 q1 U1 M8 M6 M5 M4 M2 C3 C2 PURE r5 r4 r3 r2 q0 q hi lo n A BAND N2 H31 q5 M1; lia | lia ])).
clearbody lo hi. unfold used_size in *. split; cbn [fst snd]; [lia|].
unfold SH in *. Z.div_mod_to_equations. (first [ clear - H41 q7 H36 q6 H26 q4 H17 H16 r2 H12 H11 r1 H7 H6 r0 q0 Hz z N3 M8 M5 M4 M2 M1 C3 C2 PURE r7 r6 r5 r4 q2 q1 q hi lo n A BAND; lia | lia ]). }
destruct p as [id n0|mb n0]; cbn [chunk_rep] in CR |- *.
- destruct CR as (-> & i & Ht & HA & _). split; [reflexivity|]. exists i. split; [exact Ht|]. split; [exact HA|].
subst lo hi. cbn [chunk_cont fst snd] in TRANS. replace (A - rz_size n) with (slot_beg RE (class_of n) i) in TRANS by lia. exact TRANS.
- destruct CR as (-> & HR & HA & _). split; [reflexivity|]. split; [exact HR|]. split; [exact HA|].
subst lo hi. cbn [chunk_cont fst snd] in TRANS. exact TRANS.
Qed.

Lemma rlay_obj_facts {BAND : Band} : forall RE X o, rlay_ok RE X -> In o (rlay_objs RE X) ->
fst o mod 4096 = 0 /\ (lowhigh (fst o) (snd o) /\ off_hull (fst o) (snd o)) /\ fst o + snd o <= band_lo
/\ iv_disjoint o (prim_lo RE, 2^37 + 0x1000) /\ iv_disjoint o (ptrarr_lo RE, 0x800000).
Proof.
intros RE X o RL Ho. destruct RL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F & _).
exact (proj1 (List.Forall_forall _ _) F o Ho).
Qed.

Lemma rlay_obj_facts_lia {BAND : Band} : forall RE X o, rlay_ok RE X -> In o (rlay_objs RE X) ->
fst o mod 4096 = 0 /\ appr_lia (fst o) (snd o) /\ fst o + snd o <= band_lo
/\ iv_disjoint o (prim_lo RE, 2^37 + 0x1000) /\ iv_disjoint o (ptrarr_lo RE, 0x800000).
Proof.
intros RE X o RL Ho. destruct (rlay_obj_facts RE X o RL Ho) as (A1 & A2 & A3 & A4 & A5).
assert (N : 0 <= snd o) by (clear - Ho; unfold rlay_objs in Ho; repeat destruct Ho as [Ho|Ho]; try destruct Ho; subst; cbn; unfold A_FS_MAP_SIZE; lia).
split; [exact A1|]. split; [apply appr_to_lia; [exact N| lia| exact A2]|]. split; [exact A3|]. split; assumption.
Qed.

Lemma fp_RTconst_lt_ceil {BAND : Band} : forall RE X x, rlay_ok RE X -> fp_RTconst RE X x -> x < band_lo.
Proof.
intros RE X x RL [H|[H|[H|H]]].
- destruct (rtconst_img_ok x H) as [H1 _]. idtac. lia.
- pose proof (rlay_obj_facts RE X _ RL (T_obj RE X)) as (_ & _ & B & _). destruct H; cbn [fst snd] in *. lia.
- pose proof (rlay_obj_facts RE X _ RL (ctx_obj RE X)) as (_ & _ & B & _). destruct H; cbn [fst snd] in *. lia.
- pose proof (rlay_obj_facts RE X _ RL (dtls_obj RE X)) as (_ & _ & B & _). destruct H; cbn [fst snd] in *. lia.
Qed.

Lemma RTconst_stack {BAND : Band} : forall RE X m m' W,
RTconst RE X m -> rlay_ok RE X -> munch W m m' -> wmono asegs m m' ->
Forall (fun iv => band_lo <= fst iv) W -> RTconst RE X m'.
Proof.
intros RE X m m' W RT RL MU WM FW. eapply RTconst_frame; [exact RT| exact WM|].
eapply agree_on_of_munch; [exact MU| exact WM|]. intros x Fx Hx. apply outside_intro.
intros lo hi Hin [H1 H2]. pose proof (proj1 (List.Forall_forall _ _) FW _ Hin) as C. cbn [fst] in C.
pose proof (fp_RTconst_lt_ceil RE X x RL Fx). lia.
Qed.
