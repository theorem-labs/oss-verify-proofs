(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:528-543, 616-634;
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:41-45, 208-214, 230-234, for libreac/fuzz_identity's asan-ubsan build
   (lib/B). The same text also appears in projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:420-423, 430-444, 447-448,
   453-455, 470-475, 477-486, 489-491, 502-505, 511-514, 1255-1258. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/reac_box_name_seg_rel.v, with its module paths, module names and numbers changed; 329 of its 374 lines of code are new or changed and 1879 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/TickEpi.v, with its module paths and module names changed; 1031 of its 1084 lines of code are new or changed and 321 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput_seg_op2b: the segment OP2B of the image-B walk of fuzz_transport.asan-ubsan's
   LLVMFuzzerTestOneInput, `Lemma lc_op2b_ok : lc_op2b_stmt` (lib/B/Prog/LLVMFuzzerTestOneInput_segs.v), from lc_st_ann
   (+0xdcc) to lc_st_bar2 (+0xe6c). The lemma takes the kit statements K1 (lc_rom_view_stmt), K2 (lc_src_ro_stmt) and
   K3 (lc_strlen_facts_stmt) as its own arguments, in that order.

   The code (listing slots +0xdcc .. +0xe68 of lib/B/Prog/DgnTransportBList.v, the report stub 0x82ebc (+0x1c1c), the
   UBSan trap word 0x82de4 (+0x1b44)):
     +0xdcc .. +0xe10  the UBSan test of body + 15 (`bltu` of -16 and s9 at +0xdd0, trap edge 0x82070; decided: s9 =
                       body is below 2 ^ 47), "1.37" stored at body + 15 .. 18, the UBSan test of body + 24 (`bltu` of
                       -25 and s9 at +0xdf8, trap edge 0x82098; decided the same way), a0 = 8 * s6 (s6 = name mod 3),
                       a1 = op_announce.NAME, a2 = ~a1, the UBSan test of NAME + 8 * (name mod 3) (`bltu a2, a0` at
                       +0xe0c, trap edge 0x820ac): the run stops there, the test is split (DgnTransportBPaLib.v
                       paj_branch) and its taken side is refuted at each of the three names; then a0 = NAME + 8 * name
                       (+0xe10);                                                                               run A
     +0xe14 .. +0xe2c  the checked 8-byte load of NAME[name] (shadow 0: transport_cells' zero-shadow row of
                       op_announce.NAME, so `bnez` to the report 0x82ebc is not taken), s6 = a0 = the string x, the
                       call of the strlen wrapper;                                                             run B
     strlen wrapper    TransportRtCg.v astrlen_realizes (lp_strlen), in the G journal through TransportGCg.v
                       aj_gx_entry_at (op2b_strlen_at): a0 = k = 8, 8 or 5;
     +0xe30 .. +0xe3c  a2 = k, a0 = 80(s1) = body + 24, a1 = s6, the call of __asan_memcpy;                    run C
     __asan_memcpy     TransportGCg.v gx_intrin_at (lp_memcpy): body + 24 .. holds the name;
     +0xe40 .. +0xe68  a5 = (sel | 224) & 225 = the command (sel in s5), a0 = SPEC_BCAST, a1 = DESK,
                       a2 = a3 = a4 = 0, a6 = body, a7 = 34.                                                   run D
   The runs are symbolic runs of lib/A/Prog/PaShadow.v over the G journal (TransportGRunB.v paj_run_x / paj_run_to_x),
   each from a fresh state whose atoms are the registers. Between the cuts o2_lcore_kept carries the loop's facts
   (lc_lcore): the memory changes only in body's 34 bytes and in the callees' stack window below sp1. The structure is
   image A's lib/A/Prog/LLVMFuzzerTestOneInput_seg_op2b.v; the pcs, the registers (sel in s5, the name index in s6, the
   operation number in s3), the spill slot 80(s1), the three UBSan tests and the image objects (NAME = object 16,
   SPEC_BCAST = object 17, DESK = object 7) are image B's. *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YN3v YI04 YI00 YI08 YG0s.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05 YImgTop.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c YO0f.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal YC4b.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
DgnTransportBSyms DgnTransportBList DgnTransportBAddr DgnTransportBPa DgnTransportBImg DgnTransportBPaLib YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v Img0 YCfn.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k AsanCells TransportGB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBCg TransportGRwB TransportGRunB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TransportGFrame TWorldG TransportRtCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB TImgB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
LLVMFuzzerTestOneInput_cg LLVMFuzzerTestOneInput_segs LLVMFuzzerTestOneInput_st.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TOps TWorldLemmas.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.TransportGB.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TOP := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TOps.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
Module FCells := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.AsanCells.

(* ------------------------------------------------------------------ *)
(* 0. The points, the symbolic states and the values the runs leave     *)
(* ------------------------------------------------------------------ *)

(* +0xe14 (the checked load of NAME[name]), +0xe30 (the strlen wrapper's return), +0xe40 (__asan_memcpy's return). *)
Definition LO_A1 : Z := 0xe14.
Definition LO_SL : Z := 0xe30.
Definition LO_MC : Z := 0xe40.

(* The shadow base s10 (atom 26) of the token engine and its span. *)
Definition o2_Bx : sv := SOff 26 0.
Definition o2_Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).

(* Run A: body + 15 .. body + 19 written (s9 = body, atom 25), with the shadow entry of that window (the stores are
   not instrumented; the entry makes the window safe for the engine, YCbn.v cells_safe_b). Atom 25's range decides the
   two UBSan tests of body + 15 and body + 24; atom 22 (s6, the name index) has no fact, so the test of
   NAME + 8 * name stops the run. *)
Definition o2a_rg : YP09.region := YP09.mkRegion (Some 25%nat) 15 19 15 19 [].
Definition o2a_G : facts := mkFacts [(26%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (25%nat, mkAF 4096 (2 ^ 47 - 4096) 0)] [] [].
Definition o2a_ss : sstate := mkSS LO_ANN sr_atoms [o2a_rg] None o2a_G.
Definition o2a_SH : list shent := [mkSHE 25 15 19].
(* Run B: NAME[name]'s word at a0 (atom 10) holds the string x (atom 32). *)
Definition o2b_rg : YP09.region := YP09.mkRegion (Some 10%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 32 0))].
Definition o2b_G : facts :=
  mkFacts [(26%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (10%nat, mkAF TRANS_NAME (TRANS_NAME + 16) 3)] [] [].
Definition o2b_ss : sstate := mkSS LO_A1 sr_atoms [o2b_rg] None o2b_G.
Definition o2b_SH : list shent := [mkSHE 10 0 8].
(* Run C: the spill slot 80(s1) holds body + 24 (s9 + 24). *)
Definition o2c_rg : YP09.region := YP09.mkRegion (Some 9%nat) 80 88 0 0 [YP09.mkChunk 80 (CVal 8 (SOff 25 24))].
Definition o2c_ss : sstate := mkSS LO_SL sr_atoms [o2c_rg] None (mkFacts [] [] []).
(* Run D: no region. *)
Definition o2d_ss : sstate := mkSS LO_MC sr_atoms [] None (mkFacts [] [] []).

(* a5 at +0xe6c (run D), as the engine leaves it: (s5 | 224) & 225. *)
Definition o2_eD : sv := SAlu ALU_AND (SAlu ALU_OR (SOff 21 0) (SLit 224)) (SLit 225).

(* A closed valuation with atom n = v. *)
Definition o2_envz (n : nat) (v : Z) : env :=
  mkEnv (fun i => if Nat.eqb i n then Z_to_bv 64 v else Z_to_bv 64 0) (fun _ => []).

Lemma o2_eD_dec : forallb (fun i : nat =>
  Z.eqb (bv_unsigned (sv_denot (o2_envz 21 (Z.of_nat i)) o2_eD)) (lc_acmd (Z.of_nat i))) (seq 0 256) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma o2_fin : forall (f : nat -> bool) z, forallb f (seq 0 256) = true -> 0 <= z < 256 -> f (Z.to_nat z) = true.
Proof. intros f z H Hz. rewrite forallb_forall in H. apply H. apply in_seq. lia. Qed.

Lemma o2_eD_val : forall E sel, ew E 21 = Z_to_bv 64 sel -> 0 <= sel < 256 ->
  sv_denot E o2_eD = Z_to_bv 64 (lc_acmd sel).
Proof.
intros E sel H21 Hs.
assert (EQ : sv_denot E o2_eD = sv_denot (o2_envz 21 sel) o2_eD).
{ unfold o2_eD. cbn [sv_denot]. cbn [ew o2_envz Nat.eqb]. rewrite H21. reflexivity. }
rewrite EQ. pose proof (o2_fin _ sel o2_eD_dec Hs) as D. cbv beta in D. rewrite Z2Nat.id in D by lia.
apply Z.eqb_eq in D. apply bv_eq. rewrite D. symmetry. apply unsigned_lit_small.
unfold lc_acmd, TC.SPEC_CMD_E0, TC.SPEC_CMD_E1. destruct (Z.land sel 1 =? 0); lia.
Qed.

(* ------------------------------------------------------------------ *)
(* 1. The model's values of op 2                                       *)
(* ------------------------------------------------------------------ *)

Definition o2_av (cx : lcx) (op : lop) : lav := lc_ann_vals (l_pl cx) (lc_oc (l_pl cx) (lo_c op)).
Definition o2_j (cx : lcx) (op : lop) : Z := av_nm (o2_av cx op) mod 3.
Definition o2_name (cx : lcx) (op : lop) : list byte := nth (Z.to_nat (o2_j cx op)) TOP.op_announce_NAME [].
Definition o2_x (cx : lcx) (op : lop) : Z := lc_name_a (av_nm (o2_av cx op)).
Definition o2_k (cx : lcx) (op : lop) : Z := Z.of_nat (length (o2_name cx op)).
Definition o2_body2 (cx : lcx) (op : lop) : list byte :=
  TW.upd (av_body1 (o2_av cx op)) TC.SPEC_ANN_VERSION TOP.ANN_VERSION_137.

Lemma o2_u8_range : forall D c, 0 <= snd (TOP.fuzz_u8_m D c) < 256.
Proof.
intros D c. unfold TOP.fuzz_u8_m. destruct (TOP.fi_n c =? 0); cbn [snd]; [lia|].
unfold DSpec.at8, DSpec.bz.
pose proof (bv_unsigned_in_range 8 (nth (Z.to_nat (TOP.fi_off c)) D (DSpec.b8 0))) as H.
change (bv_modulus 8) with 256 in H. exact H.
Qed.

Lemma o2_av_range : forall cx op, 0 <= av_sel (o2_av cx op) < 256 /\ 0 <= av_nm (o2_av cx op) < 256.
Proof.
intros cx op. unfold o2_av, lc_ann_vals.
pose proof (o2_u8_range (l_pl cx) (lc_oc (l_pl cx) (lo_c op))) as R1.
destruct (TOP.fuzz_u8_m (l_pl cx) (lc_oc (l_pl cx) (lo_c op))) as [c1' sel]. cbn [snd] in R1.
destruct (TOP.fuzz_u8_m (l_pl cx) c1') as [c2 m].
pose proof (o2_u8_range (l_pl cx) c2) as R3.
destruct (TOP.fuzz_u8_m (l_pl cx) c2) as [c3 nm]. cbn [snd] in R3.
cbn [av_sel av_nm]. split; [exact R1 | exact R3].
Qed.

Lemma o2_body1_len : forall cx op, length (av_body1 (o2_av cx op)) = 34%nat.
Proof.
intros cx op. unfold o2_av, lc_ann_vals.
destruct (TOP.fuzz_u8_m (l_pl cx) (lc_oc (l_pl cx) (lo_c op))) as [c1' sel].
destruct (TOP.fuzz_u8_m (l_pl cx) c1') as [c2 m].
destruct (TOP.fuzz_u8_m (l_pl cx) c2) as [c3 nm]. cbn [av_body1].
assert (L0 : length (repeat (DSpec.b8 0) (Z.to_nat (TC.SPEC_ANN_MIN + 1))) = 34%nat) by reflexivity.
assert (LH : length TC.HOST = 6%nat) by reflexivity.
assert (LO : length TC.OTHER = 6%nat) by reflexivity.
pose proof (Z.mod_pos_bound m 16 ltac:(lia)) as Hm.
destruct (m mod 16 <? 10) eqn:H1; [apply Z.ltb_lt in H1 | apply Z.ltb_ge in H1].
- rewrite TWL.length_upd; [exact L0 | lia | rewrite L0, LH; lia].
- destruct (m mod 16 <? 13) eqn:H2; [apply Z.ltb_lt in H2 | exact L0].
  rewrite TWL.length_upd; [exact L0 | lia | rewrite L0, LO; lia].
Qed.

Lemma o2_body3_eq : forall cx op,
  av_body3 (o2_av cx op) = TW.upd (o2_body2 cx op) TC.SPEC_ANN_NAME (o2_name cx op).
Proof.
intros cx op. unfold o2_body2, o2_name, o2_j, o2_av, lc_ann_vals.
destruct (TOP.fuzz_u8_m (l_pl cx) (lc_oc (l_pl cx) (lo_c op))) as [c1' sel].
destruct (TOP.fuzz_u8_m (l_pl cx) c1') as [c2 m].
destruct (TOP.fuzz_u8_m (l_pl cx) c2) as [c3 nm]. reflexivity.
Qed.

(* The name index is 0, 1 or 2. *)
Lemma o2_j_cases : forall cx op, o2_j cx op = 0 \/ o2_j cx op = 1 \/ o2_j cx op = 2.
Proof. intros cx op. assert (H : 0 <= o2_j cx op < 3) by (unfold o2_j; apply Z.mod_pos_bound; lia). lia. Qed.

(* The three cases of the name: its index j, the string's address x, its length k. *)
Lemma o2_cases : forall cx op,
  (o2_j cx op = 0 /\ o2_x cx op = TRANS_STR_C24 /\ o2_k cx op = 8) \/
  (o2_j cx op = 1 /\ o2_x cx op = TRANS_STR_PC /\ o2_k cx op = 8) \/
  (o2_j cx op = 2 /\ o2_x cx op = TRANS_STR4 /\ o2_k cx op = 5).
Proof.
intros cx op. unfold o2_k, o2_name, o2_x, lc_name_a. fold (o2_j cx op).
assert (Hj : 0 <= o2_j cx op < 3) by (unfold o2_j; apply Z.mod_pos_bound; lia).
destruct (Z.eq_dec (o2_j cx op) 0) as [-> | H0]; [left; repeat split; reflexivity|].
destruct (Z.eq_dec (o2_j cx op) 1) as [-> | H1]; [right; left; repeat split; reflexivity|].
assert (o2_j cx op = 2) as -> by lia. right; right; repeat split; reflexivity.
Qed.

(* A byte list read in the view, and its garr8 form. *)
Lemma o2_nth_zs : forall (l : list byte) j, (j < length l)%nat ->
  nth j (TW.zs l) 0 = bv_unsigned (nth j l (Z_to_bv 8 0)).
Proof.
intros l j Hj. unfold TW.zs.
rewrite (nth_indep (map (fun b : byte => bv_unsigned b) l) 0 (bv_unsigned (Z_to_bv 8 0))) by (rewrite length_map; exact Hj).
apply (map_nth (fun b : byte => bv_unsigned b)).
Qed.

Lemma o2_byte_lit : forall v, 0 <= v < 256 -> bv_unsigned (Z_to_bv 8 v) = v.
Proof. intros v Hv. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. apply Z.mod_small. exact Hv. Qed.

Lemma o2_garr8_view : forall (H : word -> bool) (m : word -> option byte) base (l : list byte),
  garr8 tfibsegs (mrestrict H m) base (TW.zs l) ->
  forall j, (j < length l)%nat -> aview tfibsegs H m (base + Z.of_nat j) = Some (bv_unsigned (nth j l (Z_to_bv 8 0))).
Proof.
intros H m base l HG j Hj.
assert (Hj' : (j < length (TW.zs l))%nat) by (unfold TW.zs; rewrite length_map; exact Hj).
destruct (HG j Hj') as [Hv Hr]. rewrite (o2_nth_zs l j Hj) in Hv, Hr.
specialize (Hv 0%nat ltac:(lia)). cbn [Z.of_nat] in Hv. rewrite Z.add_0_r in Hv.
unfold aview. rewrite Hv. cbn [option_map]. f_equal.
rewrite tw_le_byte1 by exact Hr. apply o2_byte_lit. exact Hr.
Qed.

Lemma o2_view_garr8 : forall (H : word -> bool) (m : word -> option byte) base (l : list byte),
  (forall j, (j < length l)%nat -> aview tfibsegs H m (base + Z.of_nat j) = Some (bv_unsigned (nth j l (Z_to_bv 8 0)))) ->
  garr8 tfibsegs (mrestrict H m) base (TW.zs l).
Proof.
intros H m base l HV j Hj.
assert (Hj' : (j < length l)%nat) by (unfold TW.zs in Hj; rewrite length_map in Hj; exact Hj).
rewrite (o2_nth_zs l j Hj').
pose proof (bv_unsigned_in_range 8 (nth j l (Z_to_bv 8 0))) as Hr. change (bv_modulus 8) with 256 in Hr.
split; [|exact Hr].
intros k Hk. assert (k = 0%nat) by lia. subst k. cbn [Z.of_nat]. rewrite Z.add_0_r.
specialize (HV j Hj'). unfold aview in HV.
destruct (mbyte tfibsegs (mrestrict H m) (base + Z.of_nat j)) as [b|] eqn:Eb; [|discriminate HV].
cbn [option_map] in HV. injection HV as HV. f_equal.
rewrite tw_le_byte1 by exact Hr. rewrite <- HV. symmetry. apply Z_to_bv_bv_unsigned.
Qed.

Lemma o2_rdword : forall (rd : reader) a (f : Z -> Z), (forall i, 0 <= i < 8 -> rd (a + i) = Some (f i)) ->
  rdword rd a = Some (f 0 + 256 * (f 1 + 256 * (f 2 + 256 * (f 3 + 256 * (f 4 + 256 * (f 5 + 256 * (f 6 + 256 * f 7))))))).
Proof.
intros rd a f H. unfold rdword.
pose proof (H 0 ltac:(lia)) as H0. rewrite Z.add_0_r in H0.
rewrite H0, (H 1 ltac:(lia)), (H 2 ltac:(lia)), (H 3 ltac:(lia)), (H 4 ltac:(lia)), (H 5 ltac:(lia)),
  (H 6 ltac:(lia)), (H 7 ltac:(lia)). reflexivity.
Qed.

Lemma o2_ro_rd : forall q n a, In (q, n) TRANS_RO_RD -> q <= a < q + n -> trans_in_ro_rd a.
Proof. intros q n a Hin Ha. unfold trans_in_ro_rd. apply Exists_exists. exists (q, n). split; [exact Hin | exact Ha]. Qed.

Ltac o2_in := repeat (first [left; reflexivity | right]).

(* A closed check: no atom of a valuation is left in the hypothesis H (so vm_compute may run on it). *)
Ltac o2_closed H :=
  lazymatch type of H with context [ew _ _] => fail 1 "o2_closed: an atom is left in" H | _ => idtac end.

(* ------------------------------------------------------------------ *)
(* 2. The segment's kit and the facts its cuts keep                    *)
(* ------------------------------------------------------------------ *)

Section op2b. Context {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XL : Z -> Z.
Variables RLO RHI : Z.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).

Lemma o2_base : BASE = transportb_text.
Proof. vm_compute. reflexivity. Qed.
Lemma o2_vals : VAL (A_OBJ 16) = TRANS_NAME /\ VAL (A_OBJ 17) = TRANS_SPEC_BCAST /\ VAL (A_OBJ 7) = TRANS_DESK.
Proof. vm_compute. repeat split. Qed.

(* The journal lc_core carries, read off lc_core itself (it does not depend on the registers). *)
Definition o2_jt (cx : lcx) (ly : alayout) (S : astate) (W : world segs) (regs : bvmap 5 word)
    (mem : word -> option byte) (md : Model) (e : Z) : Prop :=
  ltac:(let t := eval cbv beta delta [lc_core] in (@lc_core rc B cx ly S W regs mem md e) in
        lazymatch t with ?J /\ _ => exact J end).

(* The registers a cut of this segment keeps through every step, and what the memory keeps: every byte outside
   body's 34 bytes and outside the 2 * ESTACK bytes below sp1 (the strlen wrapper's and __asan_memcpy's window). *)
Definition o2_keep : list Z := [2; 3; 4; 8; 9; 18; 19; 26].
Definition o2_KA (cx : lcx) (W : world segs) (mem mem2 : word -> option byte) : Prop :=
  forall a, 0 <= a < 2 ^ 64 -> ~ (lc_sp1 cx - 2 * ESTACK <= a < lc_sp1 cx) -> ~ (lc_F cx + 96 <= a < lc_F cx + 130) ->
    aview segs (w_H W) mem2 a = aview segs (w_H W) mem a.
Definition o2_GA (W : world segs) (mem mem2 : word -> option byte) : Prop :=
  forall a, apresent (w_H W) mem a -> apresent (w_H W) mem2 a.

(* Where the stack, the frame and its shadow lie. *)
Lemma o2_geo : forall cx ly S W regs mem md e,
  AR_laws segs B -> @lc_base rc B MT XL RLO RHI cx -> @lc_core rc B cx ly S W regs mem md e ->
  0x7fff7f800000 <= alloc_ceiling <= 0x7fffff800000 /\
  alloc_ceiling + 32432 <= lc_sp1 cx /\ lc_sp1 cx + 320 <= lc_sp0 cx /\ lc_sp0 cx <= 2 ^ 47 /\ lc_sp1 cx mod 32 = 0 /\
  lc_sp0 cx mod 16 = 0 /\
  4096 <= lc_F cx /\ lc_F cx + 256 <= alloc_ceiling /\ lc_F cx mod 64 = 0 /\
  (lc_F cx + 256 <= 0x7fff7000 \/ 0x10007fff8000 <= lc_F cx) /\
  (lc_SH cx + 32 <= lc_F cx + 96 \/ lc_F cx + 256 <= lc_SH cx) /\ 2147450880 <= lc_SH cx /\
  lc_SH cx + 32 <= alloc_ceiling /\
  AR segs B ly S W mem md /\ frame_addr ly LF_CID (l_fpos cx) = lc_F cx /\ In (LF_CID, l_fpos cx) (frames S).
Proof.
intros cx ly S W regs mem md e LAWS HB HC.
pose proof (lc_geom B MT XL RLO RHI cx ly S W regs mem md e HB HC) as G.
destruct G as [HAR Hsp0al Hstk Hsp1c HFaddr HFin Hn HINg HLIVE].
pose proof HC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hsp1 & Hsp1al & _ & HF4096 & HFal & HFceil & _).
pose proof asan_consts as ((C1 & C2) & _).
destruct (frames_bounds segs B LAWS ly S W mem md LF_CID (l_fpos cx) HAR HFin) as (F1 & F2 & F3).
rewrite HFaddr in F1, F2, F3. rewrite lf_fbytes in F2, F3. unfold LF_FBYTES in F2, F3.
destruct Hstk as (Hs1 & Hs2 & Hs3 & H47).
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in F3.
unfold LF_FRAME, LF_FBYTES in *.
assert (HSH : lc_SH cx = SHADOW_OFF + lc_F cx / 8) by reflexivity.
unfold SHADOW_OFF in HSH.
split; [lia|]. split; [exact Hsp1c|]. split; [lia|]. split; [lia|]. split; [exact Hsp1al|]. split; [exact Hsp0al|].
split; [lia|]. split; [lia|]. split; [exact HFal|]. split; [lia|].
split; [rewrite HSH; lia|]. split; [rewrite HSH; lia|]. split; [rewrite HSH; lia|].
split; [exact HAR|]. split; [exact HFaddr | exact HFin].
Qed.

(* lc_lcore carried across a step of this segment. *)
Lemma o2_lcore_kept : forall cx op ly S W regs mem md e regs2 mem2 md2,
  AR_laws segs B -> @lc_base rc B MT XL RLO RHI cx ->
  @lc_lcore rc B MT cx op false true (lo_k op) ly S W regs mem md e ->
  o2_jt cx ly S W regs2 mem2 md2 e ->
  (forall r, In r o2_keep -> YK11.getr regs2 (Z_to_bv 5 r) = YK11.getr regs (Z_to_bv 5 r)) ->
  o2_KA cx W mem mem2 -> o2_GA W mem mem2 ->
  @lc_lcore rc B MT cx op false true (lo_k op) ly S W regs2 mem2 md2 e.
Proof.
intros cx op ly S W regs mem md e regs2 mem2 md2 LAWS HB HL HJ2 P KA GA.
destruct HL as (HC & HFR & HSP & HFSH & HOP & HE & HME & R19).
destruct (o2_geo cx ly S W regs mem md e LAWS HB HC) as (C1 & G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 &
  G12 & HAR & HFaddr & HFin).
pose proof (lc_geom B MT XL RLO RHI cx ly S W regs mem md e HB HC) as G.
destruct G as [_ _ _ _ _ _ Hn HINg _].
unfold lc_core in HC.
destruct HC as (HJ & Hfrs & HlyF & HPERM & Rsp & R8 & R9 & Rgp & Rtp & Hsp1 & Hsp1al & HSAV & HF4096 & HFal & HFceil &
  HFpres & HFL & HIN).
assert (EST : ESTACK = 4096) by reflexivity.
assert (KAhi : forall a, lc_sp1 cx <= a < 2 ^ 64 -> aview segs (w_H W) mem2 a = aview segs (w_H W) mem a)
  by (intros a Ha; apply KA; lia).
split; [split; [exact HJ2|]|].
- split; [exact Hfrs|]. split; [exact HlyF|]. split; [exact HPERM|].
  split; [exact (eq_trans (P 2 ltac:(unfold o2_keep; o2_in)) Rsp)|].
  split; [exact (eq_trans (P 8 ltac:(unfold o2_keep; o2_in)) R8)|].
  split; [exact (eq_trans (P 9 ltac:(unfold o2_keep; o2_in)) R9)|].
  split; [exact (eq_trans (P 3 ltac:(unfold o2_keep; o2_in)) Rgp)|].
  split; [exact (eq_trans (P 4 ltac:(unfold o2_keep; o2_in)) Rtp)|].
  split; [exact Hsp1|]. split; [exact Hsp1al|].
  split.
  { unfold lc_saved in HSAV |- *. rewrite Forall_forall in HSAV |- *. intros o Ho.
    assert (Hor : 8 <= fst o <= 104).
    { unfold LF_SAVED in Ho. repeat (destruct Ho as [<- | Ho]; [cbn; lia|]). destruct Ho. }
    rewrite (rdword_ext (aview segs (w_H W) mem) (aview segs (w_H W) mem2) (lc_sp0 cx - fst o))
      by (intros j Hj; apply KAhi; lia).
    exact (HSAV o Ho). }
  split; [exact HF4096|]. split; [exact HFal|]. split; [exact HFceil|].
  split; [intros a Ha; exact (GA a (HFpres a Ha))|].
  split.
  { rewrite (rdword_ext (aview segs (w_H W) mem) (aview segs (w_H W) mem2) (lc_F cx + LF_FBYTES - 8))
      by (intros j Hj; unfold LF_FBYTES; apply KA; lia).
    exact HFL. }
  destruct HIN as (HPAYg & HPAYv).
  assert (KB : forall i, 0 <= i < l_n cx -> aview segs (w_H W) mem2 (l_p cx + i) = aview segs (w_H W) mem (l_p cx + i)).
  { intros i Hi. pose proof (HINg ltac:(lia)) as Hin.
    destruct (al_blocks _ _ LAWS ly S W mem md (l_p cx) (l_n cx) HAR Hin) as (_ & Hb4 & Hbc & _).
    pose proof (req_size_pos (l_n cx) ltac:(lia)) as (Hq1 & Hq2).
    pose proof (sep_block_frame segs B LAWS ly S W mem md _ _ _ _ HAR Hin HFin) as Hd.
    rewrite HFaddr, lf_fbytes in Hd. unfold zdisjoint, LF_FBYTES in Hd. cbn [fst snd] in Hd.
    apply KA; lia. }
  split.
  + apply (lc_garr8_kept (w_H W) (w_H W) mem mem2 (l_p cx) _); [|exact HPAYg].
    intros j Hj. rewrite length_map in Hj. destruct Hn as (_ & Hnl). rewrite <- Hnl in Hj. apply KB. exact Hj.
  + intros i Hi. rewrite (KB i Hi). exact (HPAYv i Hi).
- split.
  { destruct HFR as (F18 & F26). unfold lc_fr.
    split; [exact (eq_trans (P 18 ltac:(unfold o2_keep; o2_in)) F18)|].
    exact (eq_trans (P 26 ltac:(unfold o2_keep; o2_in)) F26). }
  split.
  { apply (lc_spills_kept cx _ (aview segs (w_H W) mem) (aview segs (w_H W) mem2)); [|intros a Ha; apply KAhi; lia | exact HSP].
    intros o Ho. pose proof (lf_spill_vals (lc_F cx) ltac:(lia) ltac:(unfold LF_FBYTES; lia)) as V.
    rewrite Forall_forall in V. destruct (V o Ho) as (_ & _ & V3 & V4). lia. }
  split.
  { apply (lc_fsh_kept cx (aview segs (w_H W) mem) (aview segs (w_H W) mem2) false true); [|exact HFSH].
    intros a Ha. destruct G10 as [G10 | G10]; apply KA; lia. }
  split; [exact HOP|]. split; [exact HE|]. split; [exact HME|].
  exact (eq_trans (P 19 ltac:(unfold o2_keep; o2_in)) R19).
Qed.

(* A payload byte of the world table is a byte of G. *)
Lemma o2_tw_in_G : forall x, tw_in TMAP_B x -> inG TG.G_HARNESS_B x.
Proof.
intros x (o & b & n & Hin & Hx).
assert (HG : In (b, n) TG.G_HARNESS_B)
  by exact (tw_in_G_of TMAP_B TG.G_HARNESS_B ltac:(vm_compute; reflexivity) o b n Hin).
unfold inG. apply Exists_exists. exists (b, n). split; [exact HG | unfold in_zr; cbn [fst snd]; lia].
Qed.

(* The world relation carried across a step of this segment: G lies in the image, below the stack, and off the
   frame. *)
Lemma o2_tw_kept : forall cx op ly S W regs mem md e mem2 Bw,
  AR_laws segs B -> @lp_prem rc B MT XL RLO RHI -> @lc_base rc B MT XL RLO RHI cx ->
  @lc_lcore rc B MT cx op false true (lo_k op) ly S W regs mem md e ->
  o2_KA cx W mem mem2 -> lc_tw W mem Bw -> lc_tw W mem2 Bw.
Proof.
intros cx op ly S W regs mem md e mem2 Bw LAWS HP HB HL KA Htw.
destruct HL as (HC & _).
destruct (o2_geo cx ly S W regs mem md e LAWS HB HC) as (C1 & G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 &
  G12 & HAR & HFaddr & HFin).
pose proof (G_HARNESS_gx_ok B (lp_g_unowned B MT XL RLO RHI HP)) as HGX.
unfold lc_tw in *. apply (tw_kept TMAP_B (aview segs (w_H W) mem)); [exact Htw|].
intros x Hx. pose proof (o2_tw_in_G x Hx) as HGx.
destruct (HGX x HGx) as [Himg _].
pose proof (transportb_segs_low x Himg) as Hlow. unfold kLowMemEnd in Hlow.
assert (EST : ESTACK = 4096) by reflexivity.
apply KA; [lia | lia |].
intros Hb. apply (frm_img segs B LAWS ly S W mem md LF_CID (l_fpos cx) x HAR HFin); [|exact Himg].
rewrite HFaddr, lf_fbytes. unfold LF_FBYTES. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* 3. The cuts inside the segment and the runs' valuations             *)
(* ------------------------------------------------------------------ *)

(* A cut of this segment at offset off: lc_lcore (c out of scope, body in scope), the world, body's bytes bd, s5 = sel,
   s9 = body, s8 / s11 the cursor after the three bytes op 2 read, s4 = c, and the registers' facts R of the point. *)
Definition o2_st (cx : lcx) (op : lop) (off : Z) (bd : list byte) (R : bvmap 5 word -> Prop) :
    world segs -> config -> Prop :=
  fun W2 c2 => exists ly2 S2 regs2 mem2 md2 e2,
    c2 = lc_cfg cx off regs2 mem2 md2 /\
    @lc_lcore rc B MT cx op false true (lo_k op) ly2 S2 W2 regs2 mem2 md2 e2 /\
    lc_tw W2 mem2 (lo_B op) /\
    (forall j, (j < length bd)%nat ->
       aview segs (w_H W2) mem2 (lc_F cx + 96 + Z.of_nat j) = Some (bv_unsigned (nth j bd (Z_to_bv 8 0)))) /\
    YK11.getr regs2 21 = w64 (av_sel (o2_av cx op)) /\ YK11.getr regs2 25 = w64 (lc_F cx + 96) /\
    lc_cur cx regs2 24 27 (av_c (o2_av cx op)) /\ YK11.getr regs2 20 = w64 (lc_F cx + 32) /\ R regs2.

(* The valuation of a fresh state: the registers r as atoms 0 .. 31, the extra atoms ex from 32 on. *)
Definition o2_E (r : bvmap 5 word) (ex : list word) : env := Eimg (PI := PI_transportb) (Ereg r ex).
Lemma o2_ew_reg : forall (r : bvmap 5 word) ex n (x : bv 5) v, Z.of_nat n = bv_unsigned x -> YK11.getr r x = w64 v ->
  ew (o2_E r ex) n = Z_to_bv 64 v.
Proof. intros r ex n x v Hn H. unfold o2_E. rewrite (ew_Eimg_Ereg_nat r ex n x Hn). exact H. Qed.
Lemma o2_ew_ex : forall (r : bvmap 5 word) ex j, (32 + j < 240)%nat -> ew (o2_E r ex) (32 + j) = nth j ex (Z_to_bv 64 0).
Proof. intros r ex j Hj. unfold o2_E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. Qed.
Lemma o2_agree : forall (r : bvmap 5 word) ex, env_agree 32 (Ereg r ex) (o2_E r ex).
Proof. intros r ex. split; [intros n Hn; unfold o2_E; apply Eimg_low; unfold A_TEXT; lia | reflexivity]. Qed.
Lemma o2_img : forall (r : bvmap 5 word) ex, img_env VAL A_LIM (o2_E r ex).
Proof. intros r ex. unfold o2_E. apply Eimg_env. Qed.
Lemma o2_U : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> bv_unsigned (ew E n) = v.
Proof. intros E n v H Hv. rewrite H. apply unsigned_lit_small. exact Hv. Qed.

(* The registers every run of this segment leaves as they were (it writes a0 .. a7, s6 and ra only). *)
Definition o2_kl : list Z := [2; 3; 4; 8; 9; 18; 19; 20; 21; 24; 25; 26; 27].
Lemma o2_keep_kl : forall r, In r o2_keep -> In r o2_kl.
Proof. intros r Hr. unfold o2_keep in Hr. unfold o2_kl. cbn [In] in *. tauto. Qed.

(* A byte of a 1-byte val_mem, read in the view. *)
Lemma o2_vm1_view : forall (H : word -> bool) (m : word -> option byte) a v,
  val_mem tfibsegs (mrestrict H m) a 1 v -> 0 <= v < 256 -> aview tfibsegs H m a = Some v.
Proof.
intros H m a v Hv Hr. specialize (Hv 0%nat ltac:(lia)). cbn [Z.of_nat] in Hv. rewrite Z.add_0_r in Hv.
unfold aview. rewrite Hv. cbn [option_map]. f_equal. rewrite tw_le_byte1 by exact Hr. apply o2_byte_lit. exact Hr.
Qed.

Lemma o2_body2_len : forall cx op, length (o2_body2 cx op) = 34%nat.
Proof.
intros cx op. unfold o2_body2. rewrite TWL.length_upd; [apply o2_body1_len | unfold TC.SPEC_ANN_VERSION; lia |].
rewrite o2_body1_len. unfold TC.SPEC_ANN_VERSION. change (length TOP.ANN_VERSION_137) with 4%nat. lia.
Qed.

(* The value of register r in the machine state of a symbolic state HS: its symbolic value, computed, then tac. *)
Ltac o2_reg HS r v H tac :=
  lazymatch type of HS with
  | st_ok_pi ?segsx ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok ?segsx ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_restrict_reg segsx Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  end.
(* The registers of o2_kl a run kept, from the entry registers r0. *)
Ltac o2_kr HS r0 ex KR :=
  lazymatch type of HS with
  | st_ok_pi ?segsx ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      pose proof (regs_kept_of_st_ok_pi Ex ssx (restrict Hh msx) r0 ex (map (Z_to_bv 5) o2_kl) HS (o2_agree r0 ex)
        ltac:(vm_compute; reflexivity)) as KR
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok ?segsx ?Ex ?ssx (restrict ?Hh ?msx) =>
      pose proof (regs_kept_of_st_ok segsx Ex ssx (restrict Hh msx) r0 ex (map (Z_to_bv 5) o2_kl) HS (o2_agree r0 ex)
        ltac:(vm_compute; reflexivity)) as KR
  end.
(* The write right of run A's region (body + 15 .. body + 19, bytes of the owned class-2 frame). *)
Ltac o2a_awr U25 HFaddr cx :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end;
  apply (awr_ok_x_cons_own _ _ _ _ _ _ _ _ _ _ _ _ LF_CID (l_fpos cx)); [left; reflexivity | | apply awr_ok_x_nil];
  intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U25 in Ha;
  left; unfold in_zr; cbn [fst snd]; rewrite HFaddr, lf_fbytes; unfold LF_FBYTES; lia.

(* body's 34 bytes are addressable while it is in scope (shadow bytes 12 .. 16 = 0 0 0 0 2). *)
Lemma o2_body_ra : forall cx (rd : reader), lc_fsh cx rd false true -> lc_F cx mod 64 = 0 -> 0 <= lc_F cx ->
  range_addressable rd SHADOW_OFF (lc_F cx + 96) 34.
Proof.
intros cx rd HF H64 H0 x Hx.
set (i := x / 8 - lc_F cx / 8).
assert (Hi : shadow_of_addr SHADOW_OFF x = lc_SH cx + i) by (unfold shadow_of_addr, lc_SH, i; lia).
assert (Hr : 12 <= i <= 16) by (unfold i; lia).
rewrite Hi, (HF i ltac:(lia)).
assert (i = 12 \/ i = 13 \/ i = 14 \/ i = 15 \/ i = 16) as Hc by lia.
destruct Hc as [E | [E | [E | [E | E]]]]; rewrite E;
  [exists 0; split; [reflexivity | left; reflexivity] .. |].
exists 2. split; [reflexivity|]. right. unfold i in E. split; lia.
Qed.

(* The shadow hull of [body + 24, body + 32) is the frame's shadow bytes 8 .. 15. *)
Lemma o2_body_hull : forall cx (rd : reader) n, lc_fsh cx rd false true -> lc_F cx mod 64 = 0 -> 0 <= lc_F cx ->
  0 < n <= 8 -> shadow_hull_vis rd (lc_F cx + 120) n.
Proof.
intros cx rd n HF H64 H0 Hn s Hs. unfold shadow_addr, SHADOW_OFF in Hs.
assert (Hs2 : lc_SH cx <= s < lc_SH cx + 32) by (unfold lc_SH, SHADOW_OFF; lia).
replace s with (lc_SH cx + (s - lc_SH cx)) by lia. rewrite (HF (s - lc_SH cx) ltac:(lia)). discriminate.
Qed.

Lemma o2_nth_upd_in : forall (l v : list byte) k j d, 0 <= k -> k + Z.of_nat (length v) <= Z.of_nat (length l) ->
  k <= Z.of_nat j < k + Z.of_nat (length v) -> nth j (TW.upd l k v) d = nth (Z.to_nat (Z.of_nat j - k)) v d.
Proof. intros l v k j d H1 H2 H3. rewrite <- (Nat2Z.id j) at 1. apply tw_nth_upd_in; assumption. Qed.
Lemma o2_nth_upd_out : forall (l v : list byte) k j d, 0 <= k -> k + Z.of_nat (length v) <= Z.of_nat (length l) ->
  ~ (k <= Z.of_nat j < k + Z.of_nat (length v)) -> nth j (TW.upd l k v) d = nth j l d.
Proof.
intros l v k j d H1 H2 H3. rewrite <- (Nat2Z.id j) at 1. rewrite tw_nth_upd_out by (assumption || lia).
rewrite Nat2Z.id. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* 4. Run A, +0xdcc .. +0xe14: "1.37", the three UBSan tests and       *)
(*    NAME[name]'s address                                             *)
(* ------------------------------------------------------------------ *)

Lemma o2_stage_a : forall cx op W c,
  @lp_prem rc B MT XL RLO RHI -> @lc_base rc B MT XL RLO RHI cx ->
  o2_st cx op LO_ANN (av_body1 (o2_av cx op)) (fun r => YK11.getr r 22 = w64 (o2_j cx op)) W c ->
  SRr segs W c (o2_st cx op LO_A1 (o2_body2 cx op) (fun r => YK11.getr r 10 = w64 (TRANS_NAME + 8 * o2_j cx op))).
Proof.
intros cx op W c HP HB (ly & S & regs & mem & md & e & -> & HL & Htw & HBD & R21 & R25 & HCUR & R20 & R22).
pose proof (lp_laws B MT XL RLO RHI HP) as LAWS.
pose proof (G_HARNESS_gx_ok B (lp_g_unowned B MT XL RLO RHI HP)) as HGX.
pose proof HL as (HC & HFR & _ & HFSH & _).
destruct (o2_geo cx ly S W regs mem md e LAWS HB HC) as (C1 & G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 &
  G12 & HAR & HFaddr & HFin).
pose proof HC as (HJ & _).
pose proof HC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HFpres & _).
set (E0 := o2_E regs []).
assert (HEI : img_env VAL A_LIM E0) by apply o2_img.
assert (E25 : ew E0 25 = Z_to_bv 64 (lc_F cx + 96)) by exact (o2_ew_reg regs [] 25%nat 25%bv _ eq_refl R25).
assert (E26 : ew E0 26 = Z_to_bv 64 SHADOW_OFF) by exact (o2_ew_reg regs [] 26%nat 26%bv _ eq_refl (proj2 HFR)).
assert (E22 : ew E0 22 = Z_to_bv 64 (o2_j cx op)) by exact (o2_ew_reg regs [] 22%nat 22%bv _ eq_refl R22).
assert (U25 : bv_unsigned (ew E0 25) = lc_F cx + 96) by (apply o2_U; [exact E25 | lia]).
assert (U26 : bv_unsigned (ew E0 26) = SHADOW_OFF) by (apply o2_U; [exact E26 | unfold SHADOW_OFF; lia]).
assert (E257 : ew E0 257 = Z_to_bv 64 TRANS_NAME).
{ unfold E0, o2_E. rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia). destruct o2_vals as (V16 & _). rewrite <- V16.
  reflexivity. }
assert (SHOK : sh_ok segs o2_Bx o2a_SH E0 (mrestrict (w_H W) mem)).
{ apply Forall_cons; [|apply Forall_nil].
  apply (shent_ok_of_range segs (w_H W) mem E0 o2_Bx 25%nat (lc_F cx + 96) 34 (lc_F cx + 96) 15 19
    (o2_body_ra cx _ HFSH G8 ltac:(lia))).
  - unfold o2_Bx. apply U_atom; [exact E26 | unfold SHADOW_OFF; lia].
  - apply U_atom; [exact E25 | lia].
  - lia.
  - lia.
  - intros x Hx. cbn [Z.min Z.max] in Hx. unfold SHADOW_OFF. destruct G9 as [G9 | G9]; lia. }
assert (HS : st_ok_pi (fx := l_fx cx) segs VAL E0 o2a_ss
  (restrict (w_H W) (@YK11.mkst (l_fx cx) regs (Z_to_bv 64 (BASE + LO_ANN)) mem (YK11.seg_rom segs)))).
{ rewrite restrict_mkst_fx. unfold o2a_ss. apply (@pa_entry_st_ok_full (l_fx cx) rc transportb_listing PI_transportb).
  - unfold E0, o2_E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold o2a_rg, YP09.region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U25.
    split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
    intros o Ho. apply (apresent_writable segs). apply HFpres. unfold LF_FBYTES. lia.
  - exact (conj I I).
  - unfold o2a_G, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U26, U25. rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SHADOW_OFF.
    repeat split; try exact I; lia. }
pose proof (@paj_run_x (l_fx cx) rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B
  HGX 0 []) as RUN.
pose proof (@paj_run_to_x (l_fx cx) rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS
  TG.G_HARNESS_B HGX 0 []) as RUNTO.
pose proof (paj_branch (fx := l_fx cx) (PI := PI_transportb)) as BR.
unfold lc_cfg.
replace (w64 (transportb_text + LO_ANN)) with (Z_to_bv 64 (BASE + LO_ANN)) by (rewrite o2_base; reflexivity).
(* run A1, +0xdcc .. +0xe0c: the tests of body + 15 and body + 24 (decided by atom 25's range), the four stores,
   a0 = 8 * s6, a1 = NAME, a2 = ~NAME; it stops at `bltu a2, a0` (+0xe0c). *)
paj_run_tok RUN HS HJ SHOK o2_Bspan.
{ o2a_awr U25 HFaddr cx. }
set (md1 := with_vm_backing (m_vm_lazy md) mat md) in *. clearbody md1. clear mat.
assert (KRA : forall a, 0 <= a < 2 ^ 64 -> ~ (lc_F cx + 111 <= a < lc_F cx + 115) ->
  aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) mem a).
{ intros a Ha Hn.
  apply (YC4b.kept_of_frame _ _ _ _ _ (fun x => lc_F cx + 111 <= x < lc_F cx + 115) HFr); [| exact Ha | exact Hn].
  intros b wlo whi x Hin Hx.
  lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end.
  cbn [In] in Hin.
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hx; rewrite ?U25 in Hx; lia|]).
  destruct Hin. }
assert (GAA : o2_GA W mem (ms_mem ms)) by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
rename ms into msA. rename HG into HGA. rename HFr into HFrA. rename HF into HFA.
(* +0xe0c, `bltu a2, a0`: a2 = ~NAME, a0 = 8 * (name mod 3) <= 16, so the trap edge 0x820ac is not taken *)
psrr_branch_tok RUN BR HS SHOK o2_Bspan.
- exfalso.
  destruct (o2_j_cases cx op) as [Hj | [Hj | Hj]]; rewrite Hj in E22;
    cbn [sv_denot] in Hc; rewrite ?E22, ?E257 in Hc; o2_closed Hc; vm_compute in Hc; discriminate Hc.
- clear Hc.
  (* run A2, +0xe0c .. +0xe14: the test (now decided), a0 = NAME + 8 * (name mod 3) *)
  paj_run_to_tok RUNTO HS HJ SHOK o2_Bspan LO_A1.
  { o2a_awr U25 HFaddr cx. }
  set (md2 := with_vm_backing (m_vm_lazy md1) mat md1) in *. clearbody md2. clear mat.
  assert (KRB : forall a, 0 <= a < 2 ^ 64 -> ~ (lc_F cx + 111 <= a < lc_F cx + 115) ->
    aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) (ms_mem msA) a).
  { intros a Ha Hn.
    apply (YC4b.kept_of_frame _ _ _ _ _ (fun x => lc_F cx + 111 <= x < lc_F cx + 115) HFr); [| exact Ha | exact Hn].
    intros b wlo whi x Hin Hx.
    lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end.
    cbn [In] in Hin.
    repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hx; rewrite ?U25 in Hx; lia|]).
    destruct Hin. }
  assert (KR1 : forall a, 0 <= a < 2 ^ 64 -> ~ (lc_F cx + 111 <= a < lc_F cx + 115) ->
    aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) mem a).
  { intros a Ha Hn. rewrite (KRB a Ha Hn). exact (KRA a Ha Hn). }
  assert (KA1 : o2_KA cx W mem (ms_mem ms)) by (intros a Ha H1 H2; apply KR1; [exact Ha | lia]).
  assert (GA1 : o2_GA W mem (ms_mem ms)) by (intros a Ha; exact (apresent_grows _ _ _ a HG (GAA a Ha))).
  (* the four bytes run A stored *)
  pose proof (st_ok_pi_region_nth E0 _ (restrict (w_H W) ms) 0 _ HS eq_refl) as RG. cbn [ms_mem restrict] in RG.
  lazymatch type of RG with context [YP09.mkRegion _ _ _ _ _ ?cs] => pose (CS := cs) end.
  assert (BV : forall (od v : Z), In (YP09.mkChunk (15 + od) (CVal 1 (SLit v))) CS -> 0 <= v < 256 ->
    aview segs (w_H W) (ms_mem ms) (lc_F cx + 96 + (15 + od)) = Some v).
  { intros od v Hin Hv. apply o2_vm1_view; [|exact Hv].
    exact (YC4b.field_of_region E0 _ 25%nat (lc_F cx + 96) _ _ _ _ _ (15 + od) 1%N (SLit v) v RG U25 Hin eq_refl
      ltac:(cbn; lia) ltac:(cbn; lia)). }
  assert (B4 : forall i, 0 <= i < 4 -> aview segs (w_H W) (ms_mem ms) (lc_F cx + 96 + (15 + i)) =
    Some (bv_unsigned (nth (Z.to_nat i) TOP.ANN_VERSION_137 (Z_to_bv 8 0)))).
  { intros i Hi. assert (i = 0 \/ i = 1 \/ i = 2 \/ i = 3) as [-> | [-> | [-> | ->]]] by lia.
    - rewrite (BV 0 49); [vm_compute; reflexivity | unfold CS; cbn [In]; o2_in | lia].
    - rewrite (BV 1 46); [vm_compute; reflexivity | unfold CS; cbn [In]; o2_in | lia].
    - rewrite (BV 2 51); [vm_compute; reflexivity | unfold CS; cbn [In]; o2_in | lia].
    - rewrite (BV 3 55); [vm_compute; reflexivity | unfold CS; cbn [In]; o2_in | lia]. }
  assert (HBD2 : forall j, (j < length (o2_body2 cx op))%nat ->
    aview segs (w_H W) (ms_mem ms) (lc_F cx + 96 + Z.of_nat j) = Some (bv_unsigned (nth j (o2_body2 cx op) (Z_to_bv 8 0)))).
  { intros j Hj. rewrite o2_body2_len in Hj. pose proof (o2_body1_len cx op) as L1.
    assert (LV : length TOP.ANN_VERSION_137 = 4%nat) by reflexivity.
    unfold o2_body2, TC.SPEC_ANN_VERSION.
    destruct (Z_lt_le_dec (Z.of_nat j) 15) as [Hlo | Hlo]; [|destruct (Z_lt_le_dec (Z.of_nat j) 19) as [Hhi | Hhi]].
    - rewrite o2_nth_upd_out by (rewrite ?L1, ?LV; lia). rewrite KR1 by lia. apply HBD. lia.
    - rewrite o2_nth_upd_in by (rewrite ?L1, ?LV; lia).
      replace (lc_F cx + 96 + Z.of_nat j) with (lc_F cx + 96 + (15 + (Z.of_nat j - 15))) by lia. apply B4. lia.
    - rewrite o2_nth_upd_out by (rewrite ?L1, ?LV; lia). rewrite KR1 by lia. apply HBD. lia. }
  o2_kr HS regs (@nil word) KRg.
  assert (P : forall r, In r o2_keep -> YK11.getr (ms_regs ms) (Z_to_bv 5 r) = YK11.getr regs (Z_to_bv 5 r))
    by (intros r Hr; apply KRg; apply in_map; apply o2_keep_kl; exact Hr).
  assert (KK : forall r, In r o2_kl -> YK11.getr (ms_regs ms) (Z_to_bv 5 r) = YK11.getr regs (Z_to_bv 5 r))
    by (intros r Hr; apply KRg; apply in_map; exact Hr).
  o2_reg HS (Z_to_bv 5 10) (w64 (TRANS_NAME + 8 * o2_j cx op)) R10
    ltac:(destruct (o2_j_cases cx op) as [Hj | [Hj | Hj]]; rewrite Hj in E22 |- *;
          cbn [sv_denot]; rewrite ?E22, ?E257;
          lazymatch goal with |- context [ew _ _] => fail 1 "o2_stage_a: an atom is left in a0" | _ => idtac end;
          apply bv_eq; vm_compute; reflexivity).
  pmkst HS. apply SRr_ret.
  exists ly, S, (ms_regs ms), (ms_mem ms), md2, e.
  split; [unfold lc_cfg, w64, LO_A1; rewrite o2_base; reflexivity|].
  split; [exact (o2_lcore_kept cx op ly S W regs mem md e (ms_regs ms) (ms_mem ms) md2 LAWS HB HL HJ P KA1 GA1)|].
  split; [exact (o2_tw_kept cx op ly S W regs mem md e (ms_mem ms) (lo_B op) LAWS HP HB HL KA1 Htw)|].
  split; [exact HBD2|].
  split; [exact (eq_trans (KK 21 ltac:(unfold o2_kl; o2_in)) R21)|].
  split; [exact (eq_trans (KK 25 ltac:(unfold o2_kl; o2_in)) R25)|].
  split; [destruct HCUR as (C24 & C27); split;
    [exact (eq_trans (KK 24 ltac:(unfold o2_kl; o2_in)) C24) | exact (eq_trans (KK 27 ltac:(unfold o2_kl; o2_in)) C27)]|].
  split; [exact (eq_trans (KK 20 ltac:(unfold o2_kl; o2_in)) R20)|].
  exact R10.
Qed.

(* ------------------------------------------------------------------ *)
(* 5. The read-only bytes OP2B reads (K1) and their shadow             *)
(* ------------------------------------------------------------------ *)

(* op_announce.NAME[j] holds the address of the j-th string. *)
Lemma o2_name_word (K1 : @lc_rom_view_stmt rc B MT XL RLO RHI) : forall cx ly S (W : world segs) regs mem md e,
  @lp_prem rc B MT XL RLO RHI -> @lc_base rc B MT XL RLO RHI cx -> @lc_core rc B cx ly S W regs mem md e ->
  forall j, 0 <= j < 3 ->
  rdword (aview segs (w_H W) mem) (TRANS_NAME + 8 * j) = Some (nth (Z.to_nat j) [TRANS_STR_C24; TRANS_STR_PC; TRANS_STR4] 0).
Proof.
intros cx ly S W regs mem md e HP HB HC j Hj.
pose proof (K1 HP cx ly S W regs mem md e HB HC) as KR.
assert (LN : length (flat_map (TW.put 8) [TRANS_STR_C24; TRANS_STR_PC; TRANS_STR4]) = 24%nat) by reflexivity.
assert (HB8 : forall i, 0 <= i < 24 -> aview segs (w_H W) mem (TRANS_NAME + i) =
  Some (bv_unsigned (nth (Z.to_nat i) (flat_map (TW.put 8) [TRANS_STR_C24; TRANS_STR_PC; TRANS_STR4]) (Z_to_bv 8 0)))).
{ intros i Hi.
  rewrite (KR (TRANS_NAME + i) (o2_ro_rd TRANS_NAME 24 (TRANS_NAME + i)
    ltac:(unfold TRANS_RO_RD, TRANS_RO_GLOBALS; cbn [app]; o2_in) ltac:(lia))).
  replace (TRANS_NAME + i) with (TRANS_NAME + Z.of_nat (Z.to_nat i)) by lia.
  apply lc_rom_bytes; [unfold lc_rom_tab; o2_in | rewrite LN; lia]. }
rewrite (o2_rdword _ _ (fun i => bv_unsigned (nth (Z.to_nat (8 * j + i))
  (flat_map (TW.put 8) [TRANS_STR_C24; TRANS_STR_PC; TRANS_STR4]) (Z_to_bv 8 0)))).
- assert (j = 0 \/ j = 1 \/ j = 2) as [-> | [-> | ->]] by lia; vm_compute; reflexivity.
- intros i Hi. replace (TRANS_NAME + 8 * j + i) with (TRANS_NAME + (8 * j + i)) by lia. apply HB8. lia.
Qed.

(* A string of the table lc_rom_tab with its NUL, read in the view. *)
Lemma o2_str_bytes : forall (W : world segs) mem q (l : list byte) i, trans_rom_view_rd W mem ->
  In (q, Z.of_nat (length l) + 1) TRANS_RO_RD -> In (q, l ++ [DSpec.b8 0]) lc_rom_tab -> (i < length l)%nat ->
  aview segs (w_H W) mem (q + Z.of_nat i) = Some (bv_unsigned (nth i l (Z_to_bv 8 0))).
Proof.
intros W mem q l i KR Hro Htab Hi.
rewrite (KR (q + Z.of_nat i) (o2_ro_rd q (Z.of_nat (length l) + 1) (q + Z.of_nat i) Hro ltac:(lia))).
rewrite (lc_rom_bytes q (l ++ [DSpec.b8 0]) Htab i ltac:(rewrite length_app; cbn [length]; lia)).
rewrite app_nth1 by lia. reflexivity.
Qed.

(* The name's bytes. *)
Lemma o2_name_bytes (K1 : @lc_rom_view_stmt rc B MT XL RLO RHI) : forall cx op ly S (W : world segs) regs mem md e,
  @lp_prem rc B MT XL RLO RHI -> @lc_base rc B MT XL RLO RHI cx -> @lc_core rc B cx ly S W regs mem md e ->
  forall i, (i < length (o2_name cx op))%nat ->
  aview segs (w_H W) mem (o2_x cx op + Z.of_nat i) = Some (bv_unsigned (nth i (o2_name cx op) (Z_to_bv 8 0))).
Proof.
intros cx op ly S W regs mem md e HP HB HC i Hi.
pose proof (K1 HP cx ly S W regs mem md e HB HC) as KR.
assert (Hk := o2_cases cx op). unfold o2_name in *.
destruct Hk as [(Hj & Hx & _) | [(Hj & Hx & _) | (Hj & Hx & _)]]; rewrite Hj in *; rewrite Hx;
  (apply o2_str_bytes; [exact KR | unfold TRANS_RO_RD, TRANS_RO_GLOBALS; cbn [app]; o2_in | unfold lc_rom_tab; o2_in |
   exact Hi]).
Qed.

(* NAME's 24 bytes have zero shadow (transport_cells' row of op_announce.NAME). *)
Lemma o2_name_ra : forall ly S (W : world segs) mem md j, transport_cells B -> @AR rc segs B ly S W mem md -> 0 <= j < 3 ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF (TRANS_NAME + 8 * j) 8.
Proof.
intros ly S W mem md j HCELLS HAR Hj x Hx.
assert (HZN : decode_zshadow_at B TRANS_NAME (TRANS_NAME + 24))
  by (pose proof (HCELLS ly) as H; decompose [and] H; assumption).
exists 0. split; [|left; reflexivity].
pose proof (decode_zshadow_rd B ly S W mem md TRANS_NAME (TRANS_NAME + 24) (TRANS_NAME + 8 * j) HAR
  ltac:(unfold TRANS_NAME; lia) ltac:(lia) ltac:(lia) HZN) as HT.
replace (shadow_of_addr SHADOW_OFF x) with (FCells.shadow_addr (TRANS_NAME + 8 * j)); [exact HT|].
unfold FCells.shadow_addr, FCells.ASAN_K, shadow_of_addr, SHADOW_OFF, TRANS_NAME in *. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* 6. The strlen wrapper from the G journal                            *)
(* ------------------------------------------------------------------ *)

(* TransportRtCg.v astrlen_realizes called from a G-form walk: the form of libreac/fuzz_identity's aj_strlen_at
   (projects/libreac/fuzz_identity/proofs/lib/A/Prog/LLVMFuzzerTestOneInput_Klib.v:146), its journal carried by
   TransportGCg.v aj_gx_entry_at (the entry writes no byte outside its window), as gx_intrin_at carries
   aintrin_realizes; image A's op2b_strlen_at at image B's segments. *)
Lemma op2b_strlen_at : forall (fx : YK11.FPState) pc, @astrlen_realizes fx rc segs B pc ->
  forall G W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k x kk (o : Z) raw,
  AR_laws segs B -> gx_ok segs B G -> gx_rw segs G ->
  @W_journalG.ajournal_gx rc tfib_sink_head segs B G 0 [] STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
  YK11.getr regsT 10 = w64 x -> 0 < x -> 0 <= kk -> kk + 1 < 2 ^ 32 -> x + kk + 1 <= 2 ^ 63 ->
  spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 2 * ESTACK - o <= STK ->
  YK11.getr regsT 3 = w64 (as_gp B) -> YK11.getr regsT 4 = w64 (as_tp B) -> YK11.getr regsT 1 = raw ->
  YK0s.ret_ok raw ->
  first_byte segs W memT x (kk + 1) 0 kk ->
  src_ok segs W regsT memT x (kk + 1) ->
  (forall a, x <= a <= x + kk -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o)) ->
  amem_range x (kk + 1) ->
  range_addressable (aview segs (w_H W) memT) SHADOW_OFF x (kk + 1) ->
  shadow_hull_vis (aview segs (w_H W) memT) x (kk + 1) ->
  (forall a, x + kk < a < x + kk - (x + kk) mod 8 + 8 -> aview segs (w_H W) memT a <> None) ->
  aro_unowned segs B (aview segs (w_H W) memT) ->
  SRr segs W (mkCfg (@YK11.mkst fx regsT (Z_to_bv 64 pc) memT (YK11.seg_rom segs)) mdc)
  (fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
    c2 = mkCfg (@YK11.mkst fx regs2 raw mem2 (YK11.seg_rom segs)) md2 /\
    @W_journalG.ajournal_gx rc tfib_sink_head segs B G 0 [] STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\
    aregs_preserved regsT regs2 /\ YK11.getr regs2 10 = w64 kk /\
    (forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o) ->
       aview segs (w_H W) mem2 a = aview segs (w_H W) memT a) /\
    (forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a)).
Proof.
intros fx pc AS G W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k x kk o raw LAWS HG HRW HJ
  Ha0 Hx0 Hk0 Hk1 Hxk Hsp Hal Hneg Hbud Hgp Htp Hra Hraw Hfb Hsx Hbx Hmx Hrx Hhx Htl Hro.
assert (EST : ESTACK = 4096) by reflexivity.
eapply SRr_mono.
{ apply (@aj_gx_entry_at fx rc tfib_sink_head segs B LAWS transportb_segs_low G 0 [] (2 * ESTACK) pc (fun _ => False)
    (fun regs2 _ => YK11.getr regs2 10 = w64 kk)
    W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k o raw HG eq_refl HJ Hsp Hal Hneg ltac:(lia) Hbud
    Hgp Htp Hra Hraw HRW).
  - intros a Hf. exact (False_ind _ Hf).
  - intros HPRE (Hlo2 & Hpres2). eapply SRr_mono.
    { exact (AS lyc Sc W regsT memT mdc x kk HPRE Hlo2 Hpres2 Ha0 Hx0 Hk0 Hk1 Hxk Hfb Hsx
        ltac:(rewrite Hsp; exact Hbx) Hmx Hrx Hhx Htl Hro). }
    cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsame & Hres & Hfr & Hpres3).
    hnf. split; [reflexivity|]. exists regs2, mem2, md2.
    split; [reflexivity|]. split; [exact HAR2|]. split; [exact HP|]. split; [exact Hsame|].
    split; [exact Hres|]. split; [intros a Ha _ Hn; exact (Hfr a Ha Hn) | exact Hpres3]. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP & Hres & Hfr & Hpres2).
split; [reflexivity|]. exists regs2, mem2, md2.
split; [reflexivity|]. split; [exact HJ2|]. split; [exact HP|]. split; [exact Hres|].
split; [intros a Ha Hn; exact (Hfr a Ha (fun h => h) Hn) | exact Hpres2].
Qed.

(* ------------------------------------------------------------------ *)
(* 7. Run B and the strlen wrapper, +0xe14 .. +0xe2c, back at +0xe30    *)
(* ------------------------------------------------------------------ *)

Lemma o2_x_facts : forall cx op, 0 < o2_x cx op /\ o2_x cx op + o2_k cx op + 1 <= 0xa4000 /\
  0 < o2_k cx op <= 8 /\
  In (o2_x cx op, o2_k cx op + 1) [(TRANS_HOST, 6); (TRANS_DESK, 6); (TRANS_SPEC_BCAST, 6); (TRANS_OTHER, 6);
    (TRANS_DESK2, 6); (TRANS_NOTDD, 6); (TRANS_STR_C24, 8); (TRANS_STR_C24, 9); (TRANS_STR_PC, 8); (TRANS_STR_PC, 9);
    (TRANS_STR4, 5); (TRANS_STR4, 6); (TRANS_IO, 32)] /\
  In (o2_x cx op, o2_k cx op) [(TRANS_HOST, 6); (TRANS_DESK, 6); (TRANS_SPEC_BCAST, 6); (TRANS_OTHER, 6);
    (TRANS_DESK2, 6); (TRANS_NOTDD, 6); (TRANS_STR_C24, 8); (TRANS_STR_C24, 9); (TRANS_STR_PC, 8); (TRANS_STR_PC, 9);
    (TRANS_STR4, 5); (TRANS_STR4, 6); (TRANS_IO, 32)] /\
  (forall a, o2_x cx op <= a < o2_x cx op + o2_k cx op -> in_img segs a).
Proof.
intros cx op.
assert (IMG : forall q n a, In (q, n) TRANS_RO_RD -> q <= a < q + n -> q + n <= TRANS_RLO -> in_img segs a).
{ intros q n a Hin Ha Hlo. destruct (trans_ro_rd_rom_clean a (o2_ro_rd q n a Hin Ha)) as [[Hr | Hr] _].
  - destruct Hr as (sg & Hsg & _ & Hsr). exists sg. split; [exact Hsg | exact Hsr].
  - unfold TRANS_RLO in *. lia. }
destruct (o2_cases cx op) as [(_ & -> & ->) | [(_ & -> & ->) | (_ & -> & ->)]];
  (split; [unfold TRANS_STR_C24, TRANS_STR_PC, TRANS_STR4; lia|]);
  (split; [unfold TRANS_STR_C24, TRANS_STR_PC, TRANS_STR4; lia|]);
  (split; [lia|]);
  (split; [cbn [In]; o2_in|]); (split; [cbn [In]; o2_in|]);
  intros a Ha; (lazymatch type of Ha with ?q <= _ < ?q + ?k => apply (IMG q (k + 1) a) end;
    [unfold TRANS_RO_RD, TRANS_RO_GLOBALS; cbn [app]; o2_in | lia |
     unfold TRANS_STR_C24, TRANS_STR_PC, TRANS_STR4, TRANS_RLO; lia]).
Qed.

Lemma o2_stage_b (K1 : @lc_rom_view_stmt rc B MT XL RLO RHI) (K2 : @lc_src_ro_stmt rc B MT XL RLO RHI)
    (K3 : @lc_strlen_facts_stmt rc B MT XL RLO RHI) : forall cx op W c,
  @lp_prem rc B MT XL RLO RHI -> @lc_base rc B MT XL RLO RHI cx ->
  o2_st cx op LO_A1 (o2_body2 cx op) (fun r => YK11.getr r 10 = w64 (TRANS_NAME + 8 * o2_j cx op)) W c ->
  SRr segs W c (o2_st cx op LO_SL (o2_body2 cx op)
    (fun r => YK11.getr r 10 = w64 (o2_k cx op) /\ YK11.getr r 22 = w64 (o2_x cx op))).
Proof.
intros cx op W c HP HB (ly & S & regs & mem & md & e & -> & HL & Htw & HBD & R21 & R25 & HCUR & R20 & R10).
pose proof (lp_laws B MT XL RLO RHI HP) as LAWS.
pose proof (G_HARNESS_gx_ok B (lp_g_unowned B MT XL RLO RHI HP)) as HGX.
pose proof HL as (HC & HFR & _).
destruct (o2_geo cx ly S W regs mem md e LAWS HB HC) as (C1 & G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 &
  G12 & HAR & HFaddr & HFin).
pose proof HC as (HJ & _).
pose proof HC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hsp1b & _). unfold LF_FRAME in Hsp1b.
assert (Hj : 0 <= o2_j cx op < 3) by (unfold o2_j; apply Z.mod_pos_bound; lia).
destruct (o2_x_facts cx op) as (X0 & X1 & K0 & XIN1 & XIN & XIMG).
pose proof (o2_name_word K1 cx ly S W regs mem md e HP HB HC (o2_j cx op) Hj) as NW.
set (E1 := o2_E regs [w64 (o2_x cx op)]).
assert (HEI : img_env VAL A_LIM E1) by apply o2_img.
assert (E10 : ew E1 10 = Z_to_bv 64 (TRANS_NAME + 8 * o2_j cx op)) by exact (o2_ew_reg regs _ 10%nat 10%bv _ eq_refl R10).
assert (E26 : ew E1 26 = Z_to_bv 64 SHADOW_OFF) by exact (o2_ew_reg regs _ 26%nat 26%bv _ eq_refl (proj2 HFR)).
assert (E32 : ew E1 32 = w64 (o2_x cx op)) by exact (o2_ew_ex regs [w64 (o2_x cx op)] 0 ltac:(lia)).
assert (U10 : bv_unsigned (ew E1 10) = TRANS_NAME + 8 * o2_j cx op) by (apply o2_U; [exact E10 | unfold TRANS_NAME; lia]).
assert (U26 : bv_unsigned (ew E1 26) = SHADOW_OFF) by (apply o2_U; [exact E26 | unfold SHADOW_OFF; lia]).
assert (SHOK : sh_ok segs o2_Bx o2b_SH E1 (mrestrict (w_H W) mem)).
{ apply Forall_cons; [|apply Forall_nil].
  apply (shent_ok_of_range segs (w_H W) mem E1 o2_Bx 10%nat (TRANS_NAME + 8 * o2_j cx op) 8 (TRANS_NAME + 8 * o2_j cx op)
    0 8 (o2_name_ra ly S W mem md (o2_j cx op) (lp_cells B MT XL RLO RHI HP) HAR Hj)).
  - unfold o2_Bx. apply U_atom; [exact E26 | unfold SHADOW_OFF; lia].
  - apply U_atom; [exact E10 | unfold TRANS_NAME; lia].
  - lia.
  - lia.
  - intros y Hy. cbn [Z.min Z.max] in Hy. unfold SHADOW_OFF, TRANS_NAME in *. lia. }
assert (HS : st_ok_pi (fx := l_fx cx) segs VAL E1 o2b_ss
  (restrict (w_H W) (@YK11.mkst (l_fx cx) regs (Z_to_bv 64 (BASE + LO_A1)) mem (YK11.seg_rom segs)))).
{ rewrite restrict_mkst_fx. unfold o2b_ss. apply (@pa_entry_st_ok_full (l_fx cx) rc transportb_listing PI_transportb).
  - unfold E1, o2_E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold o2b_rg, YP09.region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U10.
    split; [unfold TRANS_NAME; lia|]. split; [unfold TRANS_NAME; lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val segs E1 _ (TRANS_NAME + 8 * o2_j cx op) 0 8 (SOff 32 0) (o2_x cx op)).
    + cbn [sv_denot]. rewrite E32, Z.add_0_r. apply Z_to_bv_bv_unsigned.
    + change (8 * Z.of_N 8) with 64. lia.
    + change (Z.of_N 8) with 8. lia.
    + rewrite Z.add_0_r. exact (val_mem_of_rdword segs (w_H W) mem _ _ NW).
  - exact (conj I I).
  - unfold o2b_G, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U26, U10. rewrite !Z.pow_0_r, !Z.mod_1_r. change (2 ^ 3) with 8. unfold SHADOW_OFF, TRANS_NAME.
    repeat split; try exact I; lia. }
pose proof (@paj_run_x (l_fx cx) rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B
  HGX 0 []) as RUN.
unfold lc_cfg.
replace (w64 (transportb_text + LO_A1)) with (Z_to_bv 64 (BASE + LO_A1)) by (rewrite o2_base; reflexivity).
paj_run_tok RUN HS HJ SHOK o2_Bspan.
{ lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
  apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia | apply awr_ok_x_nil]. }
set (md1 := with_vm_backing (m_vm_lazy md) mat md) in *. clearbody md1. clear mat.
assert (KR1 : forall a, 0 <= a < 2 ^ 64 -> aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) mem a).
{ intros a Ha.
  apply (YC4b.kept_of_frame _ _ _ _ _ (fun _ => False) HFr); [| exact Ha | intros []].
  intros b wlo whi y Hin Hy.
  lazymatch type of Hin with In ?z ?l => let l' := eval vm_compute in l in change (In z l') in Hin end.
  cbn [In] in Hin. repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hy; lia|]).
  destruct Hin. }
assert (KAc : o2_KA cx W mem (ms_mem ms)) by (intros a Ha _ _; exact (KR1 a Ha)).
assert (GAc : o2_GA W mem (ms_mem ms)) by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
o2_kr HS regs [w64 (o2_x cx op)] KR.
assert (KK : forall r, In r o2_kl -> YK11.getr (ms_regs ms) (Z_to_bv 5 r) = YK11.getr regs (Z_to_bv 5 r))
  by (intros r Hr; apply KR; apply in_map; exact Hr).
assert (P : forall r, In r o2_keep -> YK11.getr (ms_regs ms) (Z_to_bv 5 r) = YK11.getr regs (Z_to_bv 5 r))
  by (intros r Hr; apply KK; apply o2_keep_kl; exact Hr).
pose proof (o2_lcore_kept cx op ly S W regs mem md e (ms_regs ms) (ms_mem ms) md1 LAWS HB HL HJ P KAc GAc) as HLc.
pose proof (o2_tw_kept cx op ly S W regs mem md e (ms_mem ms) (lo_B op) LAWS HP HB HL KAc Htw) as Htwc.
pose proof HLc as (HCc & _).
pose proof HCc as (_ & _ & _ & _ & Rsp & _ & _ & Rgp & Rtp & _).
(* the strlen wrapper's facts at the call (K3, K2) *)
pose proof (K3 HP cx ly S W (ms_regs ms) (ms_mem ms) md1 e (av_nm (o2_av cx op)) HB HCc) as KS3.
cbv zeta in KS3. destruct KS3 as (FB & TAIL & ARO).
pose proof (K2 HP cx ly S W (ms_regs ms) (ms_mem ms) md1 e (o2_x cx op) (o2_k cx op + 1) HB HCc XIN1) as SRC.
destruct (o2_geo cx ly S W (ms_regs ms) (ms_mem ms) md1 e LAWS HB HCc)
  as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HARc & _ & _).
destruct (trans_src_ok_rd B LAWS ly S W (ms_mem ms) md1 (o2_x cx op) (o2_k cx op + 1) HARc SRC ltac:(lia))
  as (RV & RRA & RHULL & RAM & _ & _).
o2_reg HS (Z_to_bv 5 10) (w64 (o2_x cx op)) Ra0 ltac:(cbn [sv_denot]; rewrite E32, Z.add_0_r; apply Z_to_bv_bv_unsigned).
o2_reg HS (Z_to_bv 5 22) (w64 (o2_x cx op)) Rs6 ltac:(cbn [sv_denot]; rewrite E32, Z.add_0_r; apply Z_to_bv_bv_unsigned).
o2_reg HS (Z_to_bv 5 1) (Z_to_bv 64 (BASE + 3632)) Rra ltac:(apply codeptr_val; exact HEI).
assert (Usp : spZ (ms_regs ms) = lc_sp0 cx + (lc_sp1 cx - lc_sp0 cx)).
{ unfold spZ. rewrite Rsp. unfold w64. rewrite unsigned_lit_small by lia. lia. }
assert (EST : ESTACK = 4096) by reflexivity.
pmkst HS.
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (mkCfg (@YK11.mkst (l_fx cx) rg (Z_to_bv 64 (transportb_sigma TB___interceptor_trampoline_strlen))
    mm rom) mdx) Q) end.
eapply SRr_bind.
{ apply (op2b_strlen_at (l_fx cx) _ (lp_strlen B MT XL RLO RHI HP (l_fx cx)) TG.G_HARNESS_B W (ms_regs ms) (ms_mem ms)
    _ _ _ _ _ _ _ _ _ ly S md1 e (o2_x cx op) (o2_k cx op) (lc_sp1 cx - lc_sp0 cx) (Z_to_bv 64 (BASE + 3632))
    LAWS HGX G_HARNESS_B_rw HJ Ra0).
  - lia.
  - lia.
  - lia.
  - lia.
  - exact Usp.
  - lia.
  - lia.
  - unfold LLVMF_STK. lia.
  - exact Rgp.
  - exact Rtp.
  - exact Rra.
  - apply (ret_ok_codeptr_v (PI := PI_transportb)); [lia | reflexivity].
  - exact FB.
  - intros a Ha. split; [exact (RV a Ha) | rewrite Usp; lia].
  - intros a Ha. lia.
  - exact RAM.
  - exact RRA.
  - exact RHULL.
  - exact TAIL.
  - exact ARO. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hres & Hfr & Hpres2).
assert (KA2 : o2_KA cx W (ms_mem ms) mem2).
{ intros a Ha H1 H2. apply Hfr; [exact Ha | lia]. }
assert (GA2 : o2_GA W (ms_mem ms) mem2) by exact Hpres2.
assert (KS : forall r, acallee_saved r -> YK11.getr regs2 (Z_to_bv 5 r) = YK11.getr (ms_regs ms) (Z_to_bv 5 r))
  by exact HP2.
assert (P2 : forall r, In r o2_keep -> YK11.getr regs2 (Z_to_bv 5 r) = YK11.getr (ms_regs ms) (Z_to_bv 5 r)).
{ intros r Hr. apply KS. unfold o2_keep in Hr. unfold acallee_saved.
  repeat (destruct Hr as [<- | Hr]; [lia|]). destruct Hr. }
apply SRr_ret.
exists ly, S, regs2, mem2, md2, e.
split; [unfold lc_cfg, w64, LO_SL; rewrite o2_base; reflexivity|].
split; [exact (o2_lcore_kept cx op ly S W (ms_regs ms) (ms_mem ms) md1 e regs2 mem2 md2 LAWS HB HLc HJ2 P2 KA2 GA2)|].
split; [exact (o2_tw_kept cx op ly S W (ms_regs ms) (ms_mem ms) md1 e mem2 (lo_B op) LAWS HP HB HLc KA2 Htwc)|].
split.
{ intros jj Hjj. rewrite o2_body2_len in Hjj. rewrite Hfr by lia. rewrite KR1 by lia. apply HBD. rewrite o2_body2_len. exact Hjj. }
split; [exact (eq_trans (KS 21 ltac:(unfold acallee_saved; lia)) (eq_trans (KK 21 ltac:(unfold o2_kl; o2_in)) R21))|].
split; [exact (eq_trans (KS 25 ltac:(unfold acallee_saved; lia)) (eq_trans (KK 25 ltac:(unfold o2_kl; o2_in)) R25))|].
split; [destruct HCUR as (C24 & C27); split;
  [exact (eq_trans (KS 24 ltac:(unfold acallee_saved; lia)) (eq_trans (KK 24 ltac:(unfold o2_kl; o2_in)) C24)) |
   exact (eq_trans (KS 27 ltac:(unfold acallee_saved; lia)) (eq_trans (KK 27 ltac:(unfold o2_kl; o2_in)) C27))]|].
split; [exact (eq_trans (KS 20 ltac:(unfold acallee_saved; lia)) (eq_trans (KK 20 ltac:(unfold o2_kl; o2_in)) R20))|].
split; [exact Hres | exact (eq_trans (KS 22 ltac:(unfold acallee_saved; lia)) Rs6)].
Qed.

(* ------------------------------------------------------------------ *)
(* 8. Run C and __asan_memcpy, +0xe30 .. +0xe3c, back at +0xe40        *)
(* ------------------------------------------------------------------ *)

Lemma o2_stage_c (K1 : @lc_rom_view_stmt rc B MT XL RLO RHI) (K2 : @lc_src_ro_stmt rc B MT XL RLO RHI) :
  forall cx op W c,
  @lp_prem rc B MT XL RLO RHI -> @lc_base rc B MT XL RLO RHI cx ->
  o2_st cx op LO_SL (o2_body2 cx op)
    (fun r => YK11.getr r 10 = w64 (o2_k cx op) /\ YK11.getr r 22 = w64 (o2_x cx op)) W c ->
  SRr segs W c (o2_st cx op LO_MC (av_body3 (o2_av cx op)) (fun _ => True)).
Proof.
intros cx op W c HP HB (ly & S & regs & mem & md & e & -> & HL & Htw & HBD & R21 & R25 & HCUR & R20 & (R10 & R22)).
pose proof (lp_laws B MT XL RLO RHI HP) as LAWS.
pose proof (G_HARNESS_gx_ok B (lp_g_unowned B MT XL RLO RHI HP)) as HGX.
pose proof HL as (HC & HFR & HSP & _).
destruct (o2_geo cx ly S W regs mem md e LAWS HB HC) as (C1 & G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 &
  G12 & HAR & HFaddr & HFin).
pose proof HC as (HJ & _).
pose proof HC as (_ & _ & _ & _ & _ & _ & R9 & _ & _ & Hsp1b & _). unfold LF_FRAME in Hsp1b.
destruct (o2_x_facts cx op) as (X0 & X1 & K0 & XIN1 & XIN & XIMG).
set (E2 := o2_E regs []).
assert (HEI : img_env VAL A_LIM E2) by apply o2_img.
assert (E25 : ew E2 25 = Z_to_bv 64 (lc_F cx + 96)) by exact (o2_ew_reg regs [] 25%nat 25%bv _ eq_refl R25).
assert (E9 : ew E2 9 = Z_to_bv 64 (lc_sp1 cx)) by exact (o2_ew_reg regs [] 9%nat 9%bv _ eq_refl R9).
assert (E10 : ew E2 10 = Z_to_bv 64 (o2_k cx op)) by exact (o2_ew_reg regs [] 10%nat 10%bv _ eq_refl R10).
assert (E22 : ew E2 22 = Z_to_bv 64 (o2_x cx op)) by exact (o2_ew_reg regs [] 22%nat 22%bv _ eq_refl R22).
assert (U9 : bv_unsigned (ew E2 9) = lc_sp1 cx) by (apply o2_U; [exact E9 | lia]).
assert (SP80 : rdword (aview segs (w_H W) mem) (lc_sp1 cx + 80) = Some (lc_F cx + 120)).
{ unfold lc_spills in HSP. rewrite Forall_forall in HSP. apply (HSP (80, lc_F cx + 120)).
  unfold lf_spill_loop, lf_spill_init, lf_spill_scal, lf_spill_sm. cbn [app]. o2_in. }
assert (SHOK : sh_ok segs o2_Bx [] E2 (mrestrict (w_H W) mem)) by apply Forall_nil.
assert (HS : st_ok_pi (fx := l_fx cx) segs VAL E2 o2c_ss
  (restrict (w_H W) (@YK11.mkst (l_fx cx) regs (Z_to_bv 64 (BASE + LO_SL)) mem (YK11.seg_rom segs)))).
{ rewrite restrict_mkst_fx. unfold o2c_ss. apply (@pa_entry_st_ok_full (l_fx cx) rc transportb_listing PI_transportb).
  - unfold E2, o2_E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold o2c_rg, YP09.region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U9.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val segs E2 _ (lc_sp1 cx) 80 8 (SOff 25 24) (lc_F cx + 120)).
    + cbn [sv_denot]. rewrite E25. rewrite unsigned_lit_small by lia. f_equal. lia.
    + change (8 * Z.of_N 8) with 64. lia.
    + change (Z.of_N 8) with 8. lia.
    + exact (val_mem_of_rdword segs (w_H W) mem _ _ SP80).
  - exact (conj I I).
  - exact (conj I (conj I I)). }
pose proof (@paj_run_x (l_fx cx) rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B
  HGX 0 []) as RUN.
unfold lc_cfg.
replace (w64 (transportb_text + LO_SL)) with (Z_to_bv 64 (BASE + LO_SL)) by (rewrite o2_base; reflexivity).
paj_run_tok RUN HS HJ SHOK o2_Bspan.
{ lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
  apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia | apply awr_ok_x_nil]. }
set (md1 := with_vm_backing (m_vm_lazy md) mat md) in *. clearbody md1. clear mat.
assert (KR1 : forall a, 0 <= a < 2 ^ 64 -> aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) mem a).
{ intros a Ha.
  apply (YC4b.kept_of_frame _ _ _ _ _ (fun _ => False) HFr); [| exact Ha | intros []].
  intros b wlo whi y Hin Hy.
  lazymatch type of Hin with In ?z ?l => let l' := eval vm_compute in l in change (In z l') in Hin end.
  cbn [In] in Hin. repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hy; lia|]).
  destruct Hin. }
assert (KAc : o2_KA cx W mem (ms_mem ms)) by (intros a Ha _ _; exact (KR1 a Ha)).
assert (GAc : o2_GA W mem (ms_mem ms)) by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
o2_kr HS regs (@nil word) KR.
assert (KK : forall r, In r o2_kl -> YK11.getr (ms_regs ms) (Z_to_bv 5 r) = YK11.getr regs (Z_to_bv 5 r))
  by (intros r Hr; apply KR; apply in_map; exact Hr).
assert (P : forall r, In r o2_keep -> YK11.getr (ms_regs ms) (Z_to_bv 5 r) = YK11.getr regs (Z_to_bv 5 r))
  by (intros r Hr; apply KK; apply o2_keep_kl; exact Hr).
pose proof (o2_lcore_kept cx op ly S W regs mem md e (ms_regs ms) (ms_mem ms) md1 LAWS HB HL HJ P KAc GAc) as HLc.
pose proof (o2_tw_kept cx op ly S W regs mem md e (ms_mem ms) (lo_B op) LAWS HP HB HL KAc Htw) as Htwc.
pose proof HLc as (HCc & _ & _ & HFSHc & _).
pose proof HCc as (_ & _ & _ & _ & Rsp & _ & _ & Rgp & Rtp & _).
destruct (o2_geo cx ly S W (ms_regs ms) (ms_mem ms) md1 e LAWS HB HCc)
  as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HARc & _ & _).
pose proof (K2 HP cx ly S W (ms_regs ms) (ms_mem ms) md1 e (o2_x cx op) (o2_k cx op) HB HCc XIN) as SRC.
destruct (trans_src_ok_rd B LAWS ly S W (ms_mem ms) md1 (o2_x cx op) (o2_k cx op) HARc SRC ltac:(lia))
  as (RV & RRA & RHULL & RAM & _ & _).
pose proof (o2_name_bytes K1 cx op ly S W (ms_regs ms) (ms_mem ms) md1 e HP HB HCc) as NB.
o2_reg HS (Z_to_bv 5 10) (w64 (lc_F cx + 120)) Ra0
  ltac:(cbn [sv_denot]; rewrite E25; rewrite unsigned_lit_small by lia; unfold w64; f_equal; lia).
o2_reg HS (Z_to_bv 5 11) (w64 (o2_x cx op)) Ra1 ltac:(cbn [sv_denot]; rewrite E22, Z.add_0_r; apply Z_to_bv_bv_unsigned).
o2_reg HS (Z_to_bv 5 12) (w64 (o2_k cx op)) Ra2 ltac:(cbn [sv_denot]; rewrite E10, Z.add_0_r; apply Z_to_bv_bv_unsigned).
o2_reg HS (Z_to_bv 5 1) (Z_to_bv 64 (BASE + 3648)) Rra ltac:(apply codeptr_val; exact HEI).
assert (Usp : spZ (ms_regs ms) = lc_sp0 cx + (lc_sp1 cx - lc_sp0 cx)).
{ unfold spZ. rewrite Rsp. unfold w64. rewrite unsigned_lit_small by lia. lia. }
assert (EST : ESTACK = 4096) by reflexivity.
assert (DJ : lc_F cx + 120 + o2_k cx op <= o2_x cx op \/ o2_x cx op + o2_k cx op <= lc_F cx + 120).
{ destruct (Z_le_gt_dec (lc_F cx + 120 + o2_k cx op) (o2_x cx op)) as [H | H]; [left; exact H|].
  destruct (Z_le_gt_dec (o2_x cx op + o2_k cx op) (lc_F cx + 120)) as [H' | H']; [right; exact H'|].
  exfalso. apply (frm_img segs B LAWS ly S W mem md LF_CID (l_fpos cx) (Z.max (lc_F cx + 120) (o2_x cx op)) HAR HFin).
  - rewrite HFaddr, lf_fbytes. unfold LF_FBYTES. lia.
  - apply XIMG. lia. }
pmkst HS.
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (mkCfg (@YK11.mkst (l_fx cx) rg (Z_to_bv 64 (transportb_sigma TB___asan_memcpy)) mm rom) mdx) Q) end.
eapply SRr_bind.
{ apply (@gx_intrin_at (l_fx cx) rc tfib_sink_head segs B LAWS transportb_segs_low OCpy
    (transportb_sigma TB___asan_memcpy) (lp_memcpy B MT XL RLO RHI HP (l_fx cx)) TG.G_HARNESS_B W (ms_regs ms)
    (ms_mem ms) _ _ _ _ _ _ _ _ _ ly S md1 e (lc_F cx + 120) (o2_x cx op) (o2_k cx op) (lc_sp1 cx - lc_sp0 cx)
    (Z_to_bv 64 (BASE + 3648)) HGX G_HARNESS_B_rw HJ Ra0 Ra1 Ra2).
  - lia.
  - lia.
  - lia.
  - exact Usp.
  - lia.
  - lia.
  - unfold LLVMF_STK. lia.
  - exact Rgp.
  - exact Rtp.
  - exact Rra.
  - apply (ret_ok_codeptr_v (PI := PI_transportb)); [lia | reflexivity].
  - eapply (transport_twr_ok_g_intro segs B LAWS); [exact HJ|]. intros a Ha. left. split.
    + right; right; right. exists LF_CID, (l_fpos cx). split; [left; reflexivity|].
      left. unfold in_zr. cbn [fst snd]. rewrite HFaddr, lf_fbytes. unfold LF_FBYTES. lia.
    + rewrite Usp. lia.
  - unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd. destruct G9 as [G9 | G9]; [left | right]; lia.
  - apply (range_addressable_sub _ _ (lc_F cx + 96) 34); [exact (o2_body_ra cx _ HFSHc G8 ltac:(lia)) | lia | lia].
  - intros _. exact (o2_body_hull cx _ (o2_k cx op) HFSHc G8 ltac:(lia) ltac:(lia)).
  - cbv iota beta. split; [lia|]. split; [lia|].
    split; [intros a Ha; split; [exact (RV a Ha) | rewrite Usp; lia]|].
    split; [exact DJ|]. split; [exact RAM|]. split; [exact RRA|]. intros _. exact RHULL. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & _ & Hcopy & Heff & Hpres2).
cbv iota in Hcopy.
assert (KA2 : o2_KA cx W (ms_mem ms) mem2).
{ intros a Ha H1 H2. apply Heff; [exact Ha | lia | lia]. }
assert (GA2 : o2_GA W (ms_mem ms) mem2) by exact Hpres2.
assert (KS : forall r, acallee_saved r -> YK11.getr regs2 (Z_to_bv 5 r) = YK11.getr (ms_regs ms) (Z_to_bv 5 r))
  by exact HP2.
assert (P2 : forall r, In r o2_keep -> YK11.getr regs2 (Z_to_bv 5 r) = YK11.getr (ms_regs ms) (Z_to_bv 5 r)).
{ intros r Hr. apply KS. unfold o2_keep in Hr. unfold acallee_saved.
  repeat (destruct Hr as [<- | Hr]; [lia|]). destruct Hr. }
apply SRr_ret.
exists ly, S, regs2, mem2, md2, e.
split; [unfold lc_cfg, w64, LO_MC; rewrite o2_base; reflexivity|].
split; [exact (o2_lcore_kept cx op ly S W (ms_regs ms) (ms_mem ms) md1 e regs2 mem2 md2 LAWS HB HLc HJ2 P2 KA2 GA2)|].
split; [exact (o2_tw_kept cx op ly S W (ms_regs ms) (ms_mem ms) md1 e mem2 (lo_B op) LAWS HP HB HLc KA2 Htwc)|].
split.
{ intros jj Hjj. rewrite o2_body3_eq in *.
  pose proof (o2_body2_len cx op) as L2.
  assert (LN : Z.of_nat (length (o2_name cx op)) = o2_k cx op) by reflexivity.
  rewrite TWL.length_upd in Hjj by (rewrite ?L2, ?LN; unfold TC.SPEC_ANN_NAME; lia). rewrite L2 in Hjj.
  unfold TC.SPEC_ANN_NAME.
  destruct (Z_lt_le_dec (Z.of_nat jj) 24) as [Hlo | Hlo];
    [|destruct (Z_lt_le_dec (Z.of_nat jj) (24 + o2_k cx op)) as [Hhi | Hhi]].
  - rewrite o2_nth_upd_out by (rewrite ?L2, ?LN; lia).
    rewrite Heff by lia. rewrite KR1 by lia. apply HBD. rewrite L2. exact Hjj.
  - rewrite o2_nth_upd_in by (rewrite ?L2, ?LN; lia).
    replace (lc_F cx + 96 + Z.of_nat jj) with (lc_F cx + 120 + (Z.of_nat jj - 24)) by lia.
    rewrite Hcopy by lia.
    pose proof (NB (Z.to_nat (Z.of_nat jj - 24)) ltac:(lia)) as Hn. rewrite Z2Nat.id in Hn by lia. exact Hn.
  - rewrite o2_nth_upd_out by (rewrite ?L2, ?LN; lia).
    rewrite Heff by lia. rewrite KR1 by lia. apply HBD. rewrite L2. exact Hjj. }
split; [exact (eq_trans (KS 21 ltac:(unfold acallee_saved; lia)) (eq_trans (KK 21 ltac:(unfold o2_kl; o2_in)) R21))|].
split; [exact (eq_trans (KS 25 ltac:(unfold acallee_saved; lia)) (eq_trans (KK 25 ltac:(unfold o2_kl; o2_in)) R25))|].
split; [destruct HCUR as (C24 & C27); split;
  [exact (eq_trans (KS 24 ltac:(unfold acallee_saved; lia)) (eq_trans (KK 24 ltac:(unfold o2_kl; o2_in)) C24)) |
   exact (eq_trans (KS 27 ltac:(unfold acallee_saved; lia)) (eq_trans (KK 27 ltac:(unfold o2_kl; o2_in)) C27))]|].
split; [exact (eq_trans (KS 20 ltac:(unfold acallee_saved; lia)) (eq_trans (KK 20 ltac:(unfold o2_kl; o2_in)) R20))|].
exact I.
Qed.

(* ------------------------------------------------------------------ *)
(* 9. Run D, +0xe40 .. +0xe68: the arguments of build_and_receive      *)
(* ------------------------------------------------------------------ *)

Lemma o2_img_atom : forall (r : bvmap 5 word) ex a v, (A_TEXT <= a < A_LIM)%nat -> VAL a = v ->
  sv_denot (o2_E r ex) (SOff a 0) = Z_to_bv 64 v.
Proof.
intros r ex a v Ha Hv. cbn [sv_denot]. unfold o2_E. rewrite Eimg_img by exact Ha.
rewrite Z.add_0_r, Z_to_bv_bv_unsigned. rewrite Hv. reflexivity.
Qed.

Lemma o2_stage_d : forall cx op W c,
  @lp_prem rc B MT XL RLO RHI -> @lc_base rc B MT XL RLO RHI cx -> lc_opc (l_pl cx) (lo_c op) = 2 ->
  o2_st cx op LO_MC (av_body3 (o2_av cx op)) (fun _ => True) W c ->
  SRr segs W c (@lc_st_bar2 rc B MT cx op).
Proof.
intros cx op W c HP HB Hopc (ly & S & regs & mem & md & e & -> & HL & Htw & HBD & R21 & R25 & HCUR & R20 & _).
pose proof (lp_laws B MT XL RLO RHI HP) as LAWS.
pose proof (G_HARNESS_gx_ok B (lp_g_unowned B MT XL RLO RHI HP)) as HGX.
pose proof HL as (HC & _).
destruct (o2_geo cx ly S W regs mem md e LAWS HB HC) as (C1 & G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 &
  G12 & HAR & HFaddr & HFin).
pose proof HC as (HJ & _).
destruct (o2_av_range cx op) as (Rsel & Rnm).
set (E3 := o2_E regs []).
assert (HEI : img_env VAL A_LIM E3) by apply o2_img.
assert (E25 : ew E3 25 = Z_to_bv 64 (lc_F cx + 96)) by exact (o2_ew_reg regs [] 25%nat 25%bv _ eq_refl R25).
assert (E21 : ew E3 21 = Z_to_bv 64 (av_sel (o2_av cx op))) by exact (o2_ew_reg regs [] 21%nat 21%bv _ eq_refl R21).
assert (SHOK : sh_ok segs o2_Bx [] E3 (mrestrict (w_H W) mem)) by apply Forall_nil.
assert (HS : st_ok_pi (fx := l_fx cx) segs VAL E3 o2d_ss
  (restrict (w_H W) (@YK11.mkst (l_fx cx) regs (Z_to_bv 64 (BASE + LO_MC)) mem (YK11.seg_rom segs)))).
{ rewrite restrict_mkst_fx. unfold o2d_ss. apply (@pa_entry_st_ok_full (l_fx cx) rc transportb_listing PI_transportb).
  - unfold E3, o2_E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - exact I.
  - exact (conj I (conj I I)). }
pose proof (@paj_run_to_x (l_fx cx) rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS
  TG.G_HARNESS_B HGX 0 []) as RUNTO.
unfold lc_cfg.
replace (w64 (transportb_text + LO_MC)) with (Z_to_bv 64 (BASE + LO_MC)) by (rewrite o2_base; reflexivity).
paj_run_to_tok RUNTO HS HJ SHOK o2_Bspan LO_BAR2.
{ apply awr_ok_x_nil. }
set (md1 := with_vm_backing (m_vm_lazy md) mat md) in *. clearbody md1. clear mat.
assert (KR1 : forall a, 0 <= a < 2 ^ 64 -> aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) mem a).
{ intros a Ha.
  apply (YC4b.kept_of_frame _ _ _ _ _ (fun _ => False) HFr); [| exact Ha | intros []].
  intros b wlo whi y Hin Hy.
  lazymatch type of Hin with In ?z ?l => let l' := eval vm_compute in l in change (In z l') in Hin end.
  cbn [In] in Hin. destruct Hin. }
assert (KAc : o2_KA cx W mem (ms_mem ms)) by (intros a Ha _ _; exact (KR1 a Ha)).
assert (GAc : o2_GA W mem (ms_mem ms)) by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
o2_kr HS regs (@nil word) KR.
assert (KK : forall r, In r o2_kl -> YK11.getr (ms_regs ms) (Z_to_bv 5 r) = YK11.getr regs (Z_to_bv 5 r))
  by (intros r Hr; apply KR; apply in_map; exact Hr).
assert (P : forall r, In r o2_keep -> YK11.getr (ms_regs ms) (Z_to_bv 5 r) = YK11.getr regs (Z_to_bv 5 r))
  by (intros r Hr; apply KK; apply o2_keep_kl; exact Hr).
destruct o2_vals as (V16 & V17 & V7).
o2_reg HS (Z_to_bv 5 10) (w64 TRANS_SPEC_BCAST) Q10
  ltac:(exact (o2_img_atom regs [] 258 _ ltac:(unfold A_TEXT, A_LIM; lia) V17)).
o2_reg HS (Z_to_bv 5 11) (w64 TRANS_DESK) Q11 ltac:(exact (o2_img_atom regs [] 248 _ ltac:(unfold A_TEXT, A_LIM; lia) V7)).
o2_reg HS (Z_to_bv 5 12) (w64 0) Q12 ltac:(reflexivity).
o2_reg HS (Z_to_bv 5 13) (w64 0) Q13 ltac:(reflexivity).
o2_reg HS (Z_to_bv 5 14) (w64 0) Q14 ltac:(reflexivity).
o2_reg HS (Z_to_bv 5 15) (w64 (lc_acmd (av_sel (o2_av cx op)))) Q15 ltac:(exact (o2_eD_val E3 _ E21 Rsel)).
o2_reg HS (Z_to_bv 5 16) (w64 (lc_F cx + 96)) Q16 ltac:(cbn [sv_denot]; rewrite E25, Z.add_0_r; apply Z_to_bv_bv_unsigned).
o2_reg HS (Z_to_bv 5 17) (w64 34) Q17 ltac:(reflexivity).
pmkst HS. apply SRr_ret.
exists ly, S, (ms_regs ms), (ms_mem ms), md1, e. cbv zeta.
split; [unfold lc_cfg, w64, LO_BAR2; rewrite o2_base; reflexivity|].
split; [exact Hopc|].
split; [exact (o2_lcore_kept cx op ly S W regs mem md e (ms_regs ms) (ms_mem ms) md1 LAWS HB HL HJ P KAc GAc)|].
split; [exact (o2_tw_kept cx op ly S W regs mem md e (ms_mem ms) (lo_B op) LAWS HP HB HL KAc Htw)|].
split.
{ apply (o2_view_garr8 (w_H W) (ms_mem ms) (lc_F cx + 96) (av_body3 (o2_av cx op))).
  intros jj Hjj. rewrite KR1; [exact (HBD jj Hjj)|].
  destruct (o2_x_facts cx op) as (_ & _ & K0 & _). unfold o2_k in K0. rewrite o2_body3_eq in Hjj.
  rewrite TWL.length_upd in Hjj by (rewrite ?o2_body2_len; unfold TC.SPEC_ANN_NAME; lia).
  rewrite o2_body2_len in Hjj. lia. }
split; [exact Q10|]. split; [exact Q11|]. split; [exact Q12|]. split; [exact Q13|]. split; [exact Q14|].
split; [exact Q15|]. split; [exact Q16|]. split; [exact Q17|].
split; [destruct HCUR as (C24 & C27); split;
  [exact (eq_trans (KK 24 ltac:(unfold o2_kl; o2_in)) C24) | exact (eq_trans (KK 27 ltac:(unfold o2_kl; o2_in)) C27)]|].
exact (eq_trans (KK 20 ltac:(unfold o2_kl; o2_in)) R20).
Qed.

(* ------------------------------------------------------------------ *)
(* 10. The segment                                                     *)
(* ------------------------------------------------------------------ *)

Lemma o2_ann : forall cx op W c, @lc_st_ann rc B MT cx op W c ->
  lc_opc (l_pl cx) (lo_c op) = 2 /\
  o2_st cx op LO_ANN (av_body1 (o2_av cx op)) (fun r => YK11.getr r 22 = w64 (o2_j cx op)) W c.
Proof.
intros cx op W c (ly & S & regs & mem & md & e & H). cbv zeta in H.
destruct H as (Hc & Hopc & HL & Htw & HG & R21 & R22 & R25 & HCUR & R20).
split; [exact Hopc|].
exists ly, S, regs, mem, md, e. split; [exact Hc|]. split; [exact HL|]. split; [exact Htw|].
split; [exact (o2_garr8_view (w_H W) mem (lc_F cx + 96) _ HG)|].
split; [exact R21|]. split; [exact R25|]. split; [exact HCUR|]. split; [exact R20 | exact R22].
Qed.

Lemma lc_op2b_ok (K1 : @lc_rom_view_stmt rc B MT XL RLO RHI) (K2 : @lc_src_ro_stmt rc B MT XL RLO RHI)
    (K3 : @lc_strlen_facts_stmt rc B MT XL RLO RHI) : @lc_op2b_stmt rc B MT XL RLO RHI.
Proof.
unfold lc_op2b_stmt. intros HP cx op W c HB HANN.
destruct (o2_ann cx op W c HANN) as (Hopc & H0).
eapply SRr_bind; [exact (o2_stage_a cx op W c HP HB H0)|]. intros W1 c1 _ H1.
eapply SRr_bind; [exact (o2_stage_b K1 K2 K3 cx op W1 c1 HP HB H1)|]. intros W2 c2 _ H2.
eapply SRr_bind; [exact (o2_stage_c K1 K2 cx op W2 c2 HP HB H2)|]. intros W3 c3 _ H3.
exact (o2_stage_d cx op W3 c3 HP HB Hopc H3).
Qed.

End op2b.
