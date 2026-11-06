(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:528-543, 616-634;
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:41-45, 208-214, 230-234, for libreac/fuzz_identity's asan-ubsan build
   (lib/B). The same text also appears in projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:420-423, 430-444, 447-448,
   453-455, 470-475, 477-486, 489-491, 502-505, 511-514, 1255-1258. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/reac_box_name_seg_rel.v, with its module paths, module names and numbers changed; 706 of its 765 lines of code are new or changed and 1865 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/on_announce_seg_tail.v, with its module paths and module names changed; 1201 of its 1295 lines of code are new or changed and 671 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput_seg_op6a: Lemma lc_op6a_ok : lc_op6a_stmt B MT XL RLO RHI, the segment OP6A of the image-B
   walk of fuzz_transport.asan-ubsan's LLVMFuzzerTestOneInput (lib/B/Prog/LLVMFuzzerTestOneInput_segs.v): from the
   cut ARM6 (lc_st_arm cx op 6, +0x864) to the cut MSET (lc_st_mset, +0x8e8: the call of m_set, which this segment
   does not take), the offsets +0x864 .. +0x8e4 of the listing lib/B/Prog/DgnTransportBList.v.

   What the code does (TCb.v op_begin_m, then m_close_m up to its call of m_set: segs.v lc_close_w).
     +0x864 .. +0x878  s9 = OW, `jal __asan_memset` (OW, 0, 304);
     +0x87c .. +0x88c  `jal __asan_memset` (GOT, 0, 224);
     +0x890 .. +0x8ac  a0 = the page of g_fail_next (the spill slot 184(s1)), a0 = the byte g_fail_next (`lbu` at that
                       page + 0x678), a2 = M (the spill slot 168(s1)), a1 = M.desk_known, M.fail := a0,
                       OW.desk_off := -1: the world is op_begin's (lc6_B1); `beqz a1`;
     +0x8b0 .. +0x8c0  a0 = M.foreign and `bnez a0`, then a0 = M.state and `beq a0, 3`; the three taken branches go
                       to +0x8dc (the test of m_close is false);
     +0x8c4 .. +0x8d8  (desk known, not foreign, M.state <> S_CLOSED) a1 = OW.e3 (= 0: OW was zeroed), a0 = a1 + 1
                       (`addiw`), the UBSan overflow test `bge a0, a1` (its fall-through, `j` to the trap word +0x1b44
                       at 0x81b70, is not reached: the run decides 1 >= 0), OW.e3 := 1, M.fail := 0;
     +0x8dc .. +0x8e4  M.fly.on := 0, a0 = 3 (S_CLOSED), a1 = 8 (R_CLOSED).
   The walk. Each stretch between two calls or branches is one symbolic run of the token engine taken over the caller's
   G journal (lib/B/Prog/TransportGRunB.v paj_run_x / paj_run_to_x), from a symbolic state built at the stretch's first
   instruction from the machine facts there (its registers as atoms, the fields it reads or writes as regions); the
   two calls of __asan_memset are TransportGCg.v gx_intrin_at (destinations in G, their shadow and hulls from the
   record facts trans_recv_cells: lc6_sh_OW, lc6_sh_GOT). Every byte a stretch writes is a byte of G (awr_ok_x). The
   world is threaded by TWorldG.v tw_fill / tw_write (lc6_w_set .. lc6_w_fly), the model by lc6_close_w_eq. The core
   lc_core is carried by LLVMFuzzerTestOneInput_st.v lc_core_kept (the journal itself is never named: it is the
   hypothesis the engine and the call kit return); the rest of the cut by lc6_cut. *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Permutation Bool.
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YP09 YO09.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c YO0f.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal YC4b.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
DgnTransportBSyms DgnTransportBList DgnTransportBAddr DgnTransportBPa DgnTransportBImg DgnTransportBPaLib YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v YE2k YCfn Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require AsanCells TransportGB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
DgnTransportBCg TransportGRwB TransportGRunB CanKit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB TImgB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import receive_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import LLVMFuzzerTestOneInput_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
LLVMFuzzerTestOneInput_segs LLVMFuzzerTestOneInput_st.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TOps TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Mem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module FCells := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.AsanCells.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.TransportGB.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
Module LMem := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib.Mem.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* 1. The model: op_begin's world and m_close's world before m_set      *)
(* ------------------------------------------------------------------ *)

(* op_begin_m's worlds (TCb.v :340-344): the two memsets, OW.desk_off, M.fail. *)
Definition lc6_Bo (Bw : list byte) : list byte := TW.upd Bw TW.OFF_OW (repeat (DSpec.b8 0) (Z.to_nat TW.SZ_OW)).
Definition lc6_Bm (Bw : list byte) : list byte :=
  TW.upd (lc6_Bo Bw) TW.OFF_GOT (repeat (DSpec.b8 0) (Z.to_nat TW.SZ_GOT)).
Definition lc6_B3 (Bw : list byte) : list byte := TW.set_OW_desk_off (lc6_Bm Bw) (-1).
Definition lc6_B1 (Bw : list byte) : list byte := TW.set_M_fail (lc6_B3 Bw) (TW.g_fail_next (lc6_B3 Bw)).
(* m_close's world before M.fly.on when the desk is known, not foreign and not closed (segs.v lc_close_w). *)
Definition lc6_B1e (X : list byte) : list byte := TW.set_M_fail (TW.set_OW_e3 X 1) 0.

Lemma lc6_begin : forall Bw, TC.op_begin_m Bw = Some (lc6_B1 Bw, tt).
Proof. intros Bw. reflexivity. Qed.

Ltac lc6_num :=
  unfold TW.OFF_OW, TW.OFF_GOT, TW.OFF_M, TW.OFF_g_fail_next, TW.W_LEN, TW.SZ_OW, TW.SZ_GOT, TW.SZ_M in *.

Lemma lc6_len_upd : forall (bs v : list byte) k, Z.of_nat (length bs) = TW.W_LEN -> 0 <= k ->
  k + Z.of_nat (length v) <= TW.W_LEN -> Z.of_nat (length (TW.upd bs k v)) = TW.W_LEN.
Proof. intros bs v k HL Hk Hv. rewrite TWL.length_upd by lia. exact HL. Qed.

Lemma lc6_u_out : forall (bs v : list byte) k k' n, Z.of_nat (length bs) = TW.W_LEN -> 0 <= k -> 0 <= k' ->
  (k' + Z.of_nat n <= k \/ k + Z.of_nat (length v) <= k') -> k + Z.of_nat (length v) <= TW.W_LEN ->
  TW.u_at (TW.upd bs k v) k' n = TW.u_at bs k' n.
Proof. intros bs v k k' n HL Hk Hk' Hd Hv. apply TWL.u_at_upd_out; lia. Qed.

Lemma lc6_len_rep : forall n, Z.of_nat (length (repeat (DSpec.b8 0) (Z.to_nat n))) = Z.max 0 n.
Proof. intros n. rewrite repeat_length. lia. Qed.

Lemma lc6_len_put : forall n v, Z.of_nat (length (TW.put n v)) = Z.of_nat n.
Proof. intros n v. rewrite TWL.length_put. reflexivity. Qed.

Ltac lc6_lside := rewrite ?lc6_len_rep, ?lc6_len_put; lc6_num; cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in *; lia.

Lemma lc6_len_Bo : forall Bw, Z.of_nat (length Bw) = TW.W_LEN -> Z.of_nat (length (lc6_Bo Bw)) = TW.W_LEN.
Proof. intros Bw HL. unfold lc6_Bo. apply lc6_len_upd; [exact HL | lc6_lside | lc6_lside]. Qed.
Lemma lc6_len_Bm : forall Bw, Z.of_nat (length Bw) = TW.W_LEN -> Z.of_nat (length (lc6_Bm Bw)) = TW.W_LEN.
Proof. intros Bw HL. unfold lc6_Bm. apply lc6_len_upd; [exact (lc6_len_Bo Bw HL) | lc6_lside | lc6_lside]. Qed.
Lemma lc6_len_B3 : forall Bw, Z.of_nat (length Bw) = TW.W_LEN -> Z.of_nat (length (lc6_B3 Bw)) = TW.W_LEN.
Proof.
intros Bw HL. unfold lc6_B3, TW.set_OW_desk_off, TW.A_OW_desk_off.
apply lc6_len_upd; [exact (lc6_len_Bm Bw HL) | lc6_lside | lc6_lside].
Qed.

(* The fields the code reads, through the two stores of op_begin before them. *)
Lemma lc6_rd_B1 : forall Bw k n, Z.of_nat (length Bw) = TW.W_LEN -> 0 <= k ->
  (k + Z.of_nat n <= TW.OFF_M + 88 \/ TW.OFF_M + 92 <= k) ->
  (k + Z.of_nat n <= TW.OFF_OW + 232 \/ TW.OFF_OW + 236 <= k) ->
  TW.u_at (lc6_B1 Bw) k n = TW.u_at (lc6_Bm Bw) k n.
Proof.
intros Bw k n HL Hk H1 H2. unfold lc6_B1, TW.set_M_fail, TW.A_M_fail.
rewrite lc6_u_out by first [exact (lc6_len_B3 Bw HL) | lc6_lside].
unfold lc6_B3, TW.set_OW_desk_off, TW.A_OW_desk_off.
rewrite lc6_u_out by first [exact (lc6_len_Bm Bw HL) | lc6_lside].
reflexivity.
Qed.

Lemma lc6_gfn : forall Bw, Z.of_nat (length Bw) = TW.W_LEN ->
  TW.g_fail_next (lc6_B3 Bw) = TW.u_at (lc6_Bm Bw) TW.OFF_g_fail_next 1.
Proof.
intros Bw HL. unfold TW.g_fail_next, lc6_B3, TW.set_OW_desk_off, TW.A_OW_desk_off.
rewrite lc6_u_out by first [exact (lc6_len_Bm Bw HL) | lc6_lside].
reflexivity.
Qed.

(* The three fields m_close_m tests, at op_begin's world: as after the memsets. *)
Lemma lc6_fields_B1 : forall Bw, Z.of_nat (length Bw) = TW.W_LEN ->
  TW.M_desk_known (lc6_B1 Bw) = bv_swrap 32 (TW.u_at (lc6_Bm Bw) TW.A_M_desk_known 4) /\
  TW.M_foreign (lc6_B1 Bw) = bv_swrap 32 (TW.u_at (lc6_Bm Bw) TW.A_M_foreign 4) /\
  TW.M_state (lc6_B1 Bw) = bv_swrap 32 (TW.u_at (lc6_Bm Bw) TW.A_M_state 4).
Proof.
intros Bw HL. unfold TW.M_desk_known, TW.M_foreign, TW.M_state, TW.s32_at.
unfold TW.A_M_desk_known, TW.A_M_foreign, TW.A_M_state.
rewrite !lc6_rd_B1 by first [exact HL | lc6_lside]. repeat split; reflexivity.
Qed.

(* OW's zeros after the memset: OW.e3 at OW + 200. *)
Lemma lc6_zero_Bm : forall Bw k, Z.of_nat (length Bw) = TW.W_LEN -> k = 0 \/ k = 200 ->
  TW.u_at (lc6_Bm Bw) (TW.OFF_OW + k) 4 = 0.
Proof.
intros Bw k HL Hk. unfold lc6_Bm.
rewrite lc6_u_out by first [exact (lc6_len_Bo Bw HL) | lc6_lside].
unfold lc6_Bo, TW.u_at.
rewrite TWL.sub_upd_d by first [lc6_lside | rewrite HL; lc6_lside].
destruct Hk as [-> | ->]; reflexivity.
Qed.

Lemma lc6_zero_B1 : forall Bw k, Z.of_nat (length Bw) = TW.W_LEN -> k = 0 \/ k = 200 ->
  TW.u_at (lc6_B1 Bw) (TW.OFF_OW + k) 4 = 0.
Proof.
intros Bw k HL Hk. rewrite lc6_rd_B1 by (exact HL || (destruct Hk as [-> | ->]; lc6_lside)).
exact (lc6_zero_Bm Bw k HL Hk).
Qed.

(* lc_close_w at op_begin's world: OW.e3 is 0 there, so its increment is 1 (the overflow of int_inc, image B's
   UBSan trap edge 0x81b70, does not occur). *)
Lemma lc6_close_w_eq : forall Bw, Z.of_nat (length Bw) = TW.W_LEN ->
  lc_close_w (lc6_B1 Bw) =
  if TC.truth (TW.M_desk_known (lc6_B1 Bw)) && negb (TC.truth (TW.M_foreign (lc6_B1 Bw))) &&
     negb (TW.M_state (lc6_B1 Bw) =? TC.S_CLOSED)
  then Some (TW.set_M_fly_on (lc6_B1e (lc6_B1 Bw)) 0)
  else Some (TW.set_M_fly_on (lc6_B1 Bw) 0).
Proof.
intros Bw HL.
assert (E3 : TW.OW_e3 (lc6_B1 Bw) = 0).
{ unfold TW.OW_e3, TW.s32_at, TW.A_OW_e3. rewrite (lc6_zero_B1 Bw 200 HL (or_intror eq_refl)). reflexivity. }
unfold lc_close_w. rewrite E3. replace (TC.int_inc 0) with (Some 1) by reflexivity.
lazymatch goal with |- context [if ?c then _ else _] => destruct c end; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* 2. The world relation across the stretches                           *)
(* ------------------------------------------------------------------ *)

(* A view that is rdF on the bytes P marks and rd0 elsewhere (m_lost_cgW.v's ml_mix). *)
Definition lc6_in (lo n x : Z) : bool := (lo <=? x) && (x <? lo + n).
Definition lc6_mix (P : Z -> bool) (rdF rd0 : Z -> option Z) : Z -> option Z :=
  fun x => if P x then rdF x else rd0 x.

Lemma lc6_in_true : forall lo n x, lo <= x < lo + n -> lc6_in lo n x = true.
Proof. intros lo n x H. unfold lc6_in. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. Qed.
Lemma lc6_in_false' : forall lo n x, ~ (lo <= x < lo + n) -> lc6_in lo n x = false.
Proof.
intros lo n x H. unfold lc6_in. destruct (Z.leb_spec lo x); destruct (Z.ltb_spec x (lo + n)); cbn [andb];
  first [reflexivity | exfalso; lia].
Qed.
Lemma lc6_in_false : forall lo n x, lc6_in lo n x = false -> ~ (lo <= x < lo + n).
Proof. intros lo n x H Hx. rewrite (lc6_in_true lo n x Hx) in H. discriminate H. Qed.

Lemma lc6_tw_start : forall rdF rd0 Bw, tw_at TMAP_B rd0 Bw -> tw_at TMAP_B (lc6_mix (fun _ => false) rdF rd0) Bw.
Proof. intros rdF rd0 Bw H. apply (tw_kept TMAP_B rd0 _ Bw H). intros x _. reflexivity. Qed.

(* One 4-byte store of v at the world offset ko = o + k of the row (o, b, n). *)
Lemma lc6_tw_step : forall rdF rd0 P Bw o b n k ko v,
  tw_at TMAP_B (lc6_mix P rdF rd0) Bw -> In (o, b, n) TMAP_B -> ko = o + k -> 0 <= k -> k + 4 <= n ->
  (forall j, (j < 4)%nat -> rdF (b + k + Z.of_nat j) = Some (YO0f.le_byte v 4 j)) ->
  tw_at TMAP_B (lc6_mix (fun x => P x || lc6_in (b + k) 4 x) rdF rd0) (TW.upd Bw ko (TW.put 4 v)).
Proof.
intros rdF rd0 P Bw o b n k ko v H Hin Hko Hk Hkn HV. subst ko.
apply (tw_write TMAP_B (lc6_mix P rdF rd0) (lc6_mix (fun x => P x || lc6_in (b + k) 4 x) rdF rd0) Bw o b n k 4 v
  TMAP_B_ok H Hin Hk ltac:(change (Z.of_nat 4) with 4; lia)).
- intros j Hj. unfold lc6_mix. cbv beta.
  rewrite (lc6_in_true (b + k) 4 (b + k + Z.of_nat j)) by lia. rewrite orb_true_r. exact (HV j Hj).
- intros x Hx Hn. unfold lc6_mix. cbv beta. change (Z.of_nat 4) with 4 in Hn.
  rewrite (lc6_in_false' (b + k) 4 x) by lia. rewrite orb_false_r. reflexivity.
Qed.

Lemma lc6_tw_end : forall rdF rd0 P Bw, tw_at TMAP_B (lc6_mix P rdF rd0) Bw ->
  (forall x, tw_in TMAP_B x -> P x = false -> rdF x = rd0 x) -> tw_at TMAP_B rdF Bw.
Proof.
intros rdF rd0 P Bw H Hk. apply (tw_kept TMAP_B (lc6_mix P rdF rd0) rdF Bw H).
intros x Hx. unfold lc6_mix. destruct (P x) eqn:E; [reflexivity | exact (Hk x Hx E)].
Qed.

Ltac lc6_unP HP :=
  cbv beta in HP;
  repeat match type of HP with
  | orb _ _ = false =>
      let Hq := fresh "Hq" in apply orb_false_iff in HP; destruct HP as [HP Hq]; apply lc6_in_false in Hq
  end.

(* The memsets: OW's and GOT's payloads zeroed (op_begin_m :390-391). *)
Lemma lc6_w_set : forall rd0 rdF Bw o b n,
  tw_at TMAP_B rd0 Bw -> In (o, b, n) TMAP_B -> 0 <= n ->
  (forall i, 0 <= i < n -> rdF (b + i) = Some (0 mod 256)) ->
  (forall x, tw_in TMAP_B x -> ~ (b <= x < b + n) -> rdF x = rd0 x) ->
  tw_at TMAP_B rdF (TW.upd Bw o (repeat (DSpec.b8 0) (Z.to_nat n))).
Proof.
intros rd0 rdF Bw o b n Htw Hin Hn HV HK.
pose proof (tw_fill_set TMAP_B rd0 rdF Bw o b n 0 0 n TMAP_B_ok Htw Hin ltac:(lia) Hn ltac:(lia)) as H.
rewrite !Z.add_0_r in H. apply H.
- intros i Hi. exact (HV i Hi).
- intros x Hx Hnx. exact (HK x Hx Hnx).
Qed.

(* +0x8a0 and +0x8a8: M.fail := the byte g_fail_next and OW.desk_off := -1: op_begin's world. *)
Lemma lc6_w_c1 : forall Bw rd0 rdF,
  tw_at TMAP_B rd0 (lc6_Bm Bw) ->
  (forall j, (j < 4)%nat -> rdF (TB_OW + 232 + Z.of_nat j) = Some (YO0f.le_byte (-1) 4 j)) ->
  (forall j, (j < 4)%nat -> rdF (TB_M + 88 + Z.of_nat j) = Some (YO0f.le_byte (TW.g_fail_next (lc6_B3 Bw)) 4 j)) ->
  (forall x, tw_in TMAP_B x -> ~ (TB_OW + 232 <= x < TB_OW + 236) -> ~ (TB_M + 88 <= x < TB_M + 92) -> rdF x = rd0 x) ->
  tw_at TMAP_B rdF (lc6_B1 Bw).
Proof.
intros Bw rd0 rdF Htw VD VF Hk.
assert (SM : TW.SZ_M = 1648) by reflexivity. assert (SO : TW.SZ_OW = 304) by reflexivity.
unfold lc6_B1. set (g := TW.g_fail_next (lc6_B3 Bw)) in *.
unfold lc6_B3, TW.set_M_fail, TW.set_OW_desk_off, TW.A_M_fail, TW.A_OW_desk_off.
pose proof (lc6_tw_start rdF rd0 _ Htw) as H0.
pose proof (lc6_tw_step rdF rd0 _ _ TW.OFF_OW TB_OW TW.SZ_OW 232 (TW.OFF_OW + 232) (-1) H0 TMAP_B_OW
  ltac:(lia) ltac:(lia) ltac:(lia) VD) as H1.
pose proof (lc6_tw_step rdF rd0 _ _ TW.OFF_M TB_M TW.SZ_M 88 (TW.OFF_M + 88) g H1 TMAP_B_M
  ltac:(lia) ltac:(lia) ltac:(lia) VF) as H2.
apply (lc6_tw_end rdF rd0 _ _ H2).
intros x Hx HP. lc6_unP HP. apply Hk; [exact Hx | lia | lia].
Qed.

(* +0x8d4 .. +0x8d8: OW.e3 := 1, M.fail := 0. *)
Lemma lc6_w_c2e : forall X rd0 rdF,
  tw_at TMAP_B rd0 X ->
  (forall j, (j < 4)%nat -> rdF (TB_OW + 200 + Z.of_nat j) = Some (YO0f.le_byte 1 4 j)) ->
  (forall j, (j < 4)%nat -> rdF (TB_M + 88 + Z.of_nat j) = Some (YO0f.le_byte 0 4 j)) ->
  (forall x, tw_in TMAP_B x -> ~ (TB_OW + 200 <= x < TB_OW + 204) -> ~ (TB_M + 88 <= x < TB_M + 92) -> rdF x = rd0 x) ->
  tw_at TMAP_B rdF (lc6_B1e X).
Proof.
intros X rd0 rdF Htw VE VF Hk.
assert (SM : TW.SZ_M = 1648) by reflexivity. assert (SO : TW.SZ_OW = 304) by reflexivity.
unfold lc6_B1e, TW.set_M_fail, TW.set_OW_e3, TW.A_M_fail, TW.A_OW_e3.
pose proof (lc6_tw_start rdF rd0 _ Htw) as H0.
pose proof (lc6_tw_step rdF rd0 _ _ TW.OFF_OW TB_OW TW.SZ_OW 200 (TW.OFF_OW + 200) 1 H0 TMAP_B_OW
  ltac:(lia) ltac:(lia) ltac:(lia) VE) as H1.
pose proof (lc6_tw_step rdF rd0 _ _ TW.OFF_M TB_M TW.SZ_M 88 (TW.OFF_M + 88) 0 H1 TMAP_B_M
  ltac:(lia) ltac:(lia) ltac:(lia) VF) as H2.
apply (lc6_tw_end rdF rd0 _ _ H2).
intros x Hx HP. lc6_unP HP. apply Hk; [exact Hx | lia | lia].
Qed.

(* +0x8dc: M.fly.on := 0. *)
Lemma lc6_w_fly : forall X rd0 rdF,
  tw_at TMAP_B rd0 X ->
  (forall j, (j < 4)%nat -> rdF (TB_M + 96 + Z.of_nat j) = Some (YO0f.le_byte 0 4 j)) ->
  (forall x, tw_in TMAP_B x -> ~ (TB_M + 96 <= x < TB_M + 100) -> rdF x = rd0 x) ->
  tw_at TMAP_B rdF (TW.set_M_fly_on X 0).
Proof.
intros X rd0 rdF Htw VF Hk.
assert (SM : TW.SZ_M = 1648) by reflexivity.
unfold TW.set_M_fly_on, TW.A_M_fly_on.
pose proof (lc6_tw_start rdF rd0 _ Htw) as H0.
pose proof (lc6_tw_step rdF rd0 _ _ TW.OFF_M TB_M TW.SZ_M 96 (TW.OFF_M + 96 + 0) 0 H0 TMAP_B_M
  ltac:(lia) ltac:(lia) ltac:(lia) VF) as H1.
apply (lc6_tw_end rdF rd0 _ _ H1).
intros x Hx HP. lc6_unP HP. apply Hk; [exact Hx | lia].
Qed.

(* ------------------------------------------------------------------ *)
(* 3. The shadow of OW and GOT (the memsets' destinations)              *)
(* ------------------------------------------------------------------ *)

(* The record's cells of trans_recv_cells, as shadow cells: g_rx_len's granule and its three guards, OW's 38 granules
   and six guards, GOT's four leading guards (g_s's) and its 28 granules. *)
Definition lc6_cs : list (Z * Z) :=
  trans_zgran TB_g_rx_len (TB_g_rx_len + TW.SZ_g_rx_len) ++
  [(TB_g_rx_len + 8, 0xf9); (TB_g_rx_len + 16, 0xf9); (TB_g_rx_len + 24, 0xf9)] ++
  trans_zgran TB_OW (TB_OW + TW.SZ_OW) ++
  [(TB_OW + TW.SZ_OW, 0xf9); (TB_OW + TW.SZ_OW + 8, 0xf9); (TB_OW + TW.SZ_OW + 16, 0xf9);
   (TB_OW + TW.SZ_OW + 24, 0xf9); (TB_OW + TW.SZ_OW + 32, 0xf9); (TB_OW + TW.SZ_OW + 40, 0xf9)] ++
  [(TB_GOT - 32, 0xf9); (TB_GOT - 24, 0xf9); (TB_GOT - 16, 0xf9); (TB_GOT - 8, 0xf9)] ++
  trans_zgran TB_GOT (TB_GOT + TW.SZ_GOT).

Lemma lc6_cover : trans_cs_cover lc6_cs TB_OW 304 = true /\ trans_cs_cover lc6_cs TB_GOT 224 = true.
Proof. split; vm_compute; reflexivity. Qed.

Section sh. Context {rc : YM05.RunCeil}.
Variable B : asyms.

Lemma lc6_sh_cells : trans_recv_cells B -> trans_sh_cells B lc6_cs.
Proof.
intros (HZow & HZgot & HZrx & HC).
unfold lc6_cs.
apply trans_sh_cells_app; [apply trans_sh_cells_zshadow; [exact HZrx | reflexivity]|].
apply trans_sh_cells_app.
{ repeat apply trans_sh_cells_cons; try apply trans_sh_cells_nil.
  all: apply trans_sh_cell_const; [intro ly; pose proof (HC ly) as Hc; tauto | lia]. }
apply trans_sh_cells_app; [apply trans_sh_cells_zshadow; [exact HZow | reflexivity]|].
apply trans_sh_cells_app.
{ repeat apply trans_sh_cells_cons; try apply trans_sh_cells_nil.
  all: apply trans_sh_cell_const; [intro ly; pose proof (HC ly) as Hc; tauto | lia]. }
apply trans_sh_cells_app.
{ repeat apply trans_sh_cells_cons; try apply trans_sh_cells_nil.
  all: apply trans_sh_cell_const; [intro ly; pose proof (HC ly) as Hc; tauto | lia]. }
apply trans_sh_cells_zshadow; [exact HZgot | reflexivity].
Qed.

Lemma lc6_sh_OW : trans_recv_cells B -> trans_sh_any B TB_OW 304.
Proof. intros HR. exact (trans_sh_any_cells B lc6_cs TB_OW 304 (lc6_sh_cells HR) (proj1 lc6_cover)). Qed.
Lemma lc6_sh_GOT : trans_recv_cells B -> trans_sh_any B TB_GOT 224.
Proof. intros HR. exact (trans_sh_any_cells B lc6_cs TB_GOT 224 (lc6_sh_cells HR) (proj2 lc6_cover)). Qed.
End sh.

(* ------------------------------------------------------------------ *)
(* 4. The machine                                                       *)
(* ------------------------------------------------------------------ *)

(* The first offset of each stretch in the listing (AF_LLVMFuzzerTestOneInput = 0). *)
Definition LC6_A : Z := 0x864.
Definition LC6_B : Z := 0x87c.
Definition LC6_C1 : Z := 0x890.
Definition LC6_C2E : Z := 0x8c4.
Definition LC6_D1 : Z := 0x8dc.

Lemma lc6_arm6 : lo_arm 6 = LC6_A.
Proof. reflexivity. Qed.
Section pa. Context {rc : YM05.RunCeil}.
Lemma lc6_base : @pa_val _ transportb_listing PI_transportb A_TEXT = transportb_text.
Proof. vm_compute. reflexivity. Qed.
Lemma lc6_vals : @pa_val _ transportb_listing PI_transportb (A_OBJ 8) = TB_M /\
  @pa_val _ transportb_listing PI_transportb (A_OBJ 12) = TB_OW /\
  @pa_val _ transportb_listing PI_transportb (A_OBJ 13) = TB_GOT /\
  @pa_val _ transportb_listing PI_transportb (A_HI 10) = transportb_hi 10.
Proof. vm_compute. repeat split. Qed.
End pa.
(* The page of g_fail_next the spill slot 184(s1) holds (segs.v lf_spill_scal, lf_spill_globals). *)
Lemma lc6_hi : transportb_hi 10 = 6154024 /\ transportb_hi 10 + 0x678 = TB_g_fail_next.
Proof. split; reflexivity. Qed.

(* The registers the stretches keep: sp, gp, tp, s0, s1, s2, s3, s4, s6, s8, s10, s11. *)
Definition LC6_KEEPZ : list Z := [2; 3; 4; 8; 9; 18; 19; 20; 22; 24; 26; 27].
Definition LC6_KEEP : list (bv 5) := map (Z_to_bv 5) LC6_KEEPZ.
Definition lc6_rk (regs regsX : bvmap 5 word) : Prop :=
  forall r, In r LC6_KEEP -> YK11.getr regsX r = YK11.getr regs r.

Ltac lc6_inK := unfold LC6_KEEP, LC6_KEEPZ; cbn [map In]; repeat (first [left; reflexivity | right]).

Lemma lc6_rk_trans : forall r1 r2 r3, lc6_rk r1 r2 -> lc6_rk r2 r3 -> lc6_rk r1 r3.
Proof. intros r1 r2 r3 H1 H2 r Hr. rewrite (H2 r Hr). exact (H1 r Hr). Qed.
Lemma lc6_rk_pres : forall regsA regsB, aregs_preserved regsA regsB -> lc6_rk regsA regsB.
Proof.
intros regsA regsB HP r Hr. unfold LC6_KEEP in Hr. apply in_map_iff in Hr. destruct Hr as (z & <- & Hz).
apply HP. unfold LC6_KEEPZ in Hz. cbn [In] in Hz. unfold acallee_saved.
repeat (destruct Hz as [<- | Hz]; [lia |]). destruct Hz.
Qed.

(* What the walk keeps from one memory to the next: the view of every byte that is not a byte of G and not in the
   4096 bytes below sp1 (the memsets' ESTACK window), and the presence of every byte. *)
Definition lc6_km (cx : lcx) (W : world tfibsegs) (m m2 : word -> option byte) : Prop :=
  (forall a, 0 <= a < 2 ^ 64 -> ~ inG TG.G_HARNESS_B a -> ~ (lc_sp1 cx - 4096 <= a < lc_sp1 cx) ->
     aview tfibsegs (w_H W) m2 a = aview tfibsegs (w_H W) m a) /\
  (forall a, apresent (w_H W) m a -> apresent (w_H W) m2 a).
Lemma lc6_km_trans : forall cx W m1 m2 m3, lc6_km cx W m1 m2 -> lc6_km cx W m2 m3 -> lc6_km cx W m1 m3.
Proof.
intros cx W m1 m2 m3 [H1 P1] [H2 P2]. split.
- intros a Ha HG Hw. rewrite (H2 a Ha HG Hw). exact (H1 a Ha HG Hw).
- intros a Ha. exact (P2 a (P1 a Ha)).
Qed.

(* Byte j < 4 of a 64-bit word holding v is byte j of the 4-byte little-endian v (m_lost_cgW.v ml_bow). *)
Lemma lc6_bow : forall v j, (j < 4)%nat ->
  bv_unsigned (byte_of_word (Z_to_bv 64 v) (Z.of_nat j)) = YO0f.le_byte v 4 j.
Proof.
intros v j Hj. unfold byte_of_word, YO0f.le_byte. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
change (2 ^ Z.of_N 8) with (2 ^ 8). change (2 ^ Z.of_N 64) with (2 ^ 64). change (8 * Z.of_nat 4) with 32.
change 256 with (2 ^ 8).
apply Z.bits_inj'. intros m Hm.
destruct (Z_lt_le_dec m 8) as [Hl|Hl].
- rewrite !Z.mod_pow2_bits_low by lia. rewrite !Z.shiftr_spec by lia.
  rewrite !Z.mod_pow2_bits_low by lia. reflexivity.
- rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

(* The 4 bytes of a chunk of a region of the state, of value v, read through the view. *)
Lemma lc6_chunk : forall (E : env) (H : word -> bool) (mm : word -> option byte) nb lo hi wlo whi cs b off e v,
  YP09.region_ok tfibsegs E (mrestrict H mm) (YP09.mkRegion nb lo hi wlo whi cs) ->
  YP09.base_val E nb = b -> In (YP09.mkChunk off (CVal 4 e)) cs -> sv_denot E e = Z_to_bv 64 v ->
  forall j, (j < 4)%nat -> aview tfibsegs H mm (b + off + Z.of_nat j) = Some (YO0f.le_byte v 4 j).
Proof.
intros E H mm nb lo hi wlo whi cs b off e v HR Hb Hin He j Hj.
destruct HR as (_ & _ & _ & HC). cbn [YP09.r_base YP09.r_chunks] in HC. rewrite Hb in HC.
pose proof (proj1 (Forall_forall _ _) HC _ Hin) as HC1. unfold YP09.chunk_ok in HC1.
cbn [YP09.c_off YP09.c_val YP09.c_len YP09.cv_len] in HC1.
destruct (HC1 (Z.of_nat j) ltac:(cbn; lia)) as (bt & Hb1 & Hb2). cbn [YP09.cbyte] in Hb1. rewrite He in Hb1.
injection Hb1 as <-.
change (aview tfibsegs H mm (b + off + Z.of_nat j))
  with (option_map (fun b : byte => bv_unsigned b) (YP09.mbyte tfibsegs (mrestrict H mm) (b + off + Z.of_nat j))).
rewrite Hb2. cbn [option_map]. f_equal. apply lc6_bow. exact Hj.
Qed.

(* beqz / beq / bnez on sign-extended 32-bit values (m_lost_cgW.v ml_eqb0, close_seg_join.v cj_eqb). *)
Lemma lc6_eqb : forall v w, - 2 ^ 31 <= v < 2 ^ 31 -> - 2 ^ 31 <= w < 2 ^ 31 ->
  bv_eqb (Z_to_bv 64 v) (Z_to_bv 64 w) = (v =? w).
Proof.
intros v w Hv Hw. unfold bv_eqb. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 64) with (2 ^ 64).
assert (Em : forall x, - 2 ^ 31 <= x < 2 ^ 31 -> x mod 2 ^ 64 = if x <? 0 then x + 2 ^ 64 else x).
{ intros x Hx. destruct (Z.ltb_spec x 0) as [Hn | Hn].
  - symmetry. apply (Z.mod_unique x (2 ^ 64) (-1) (x + 2 ^ 64)); lia.
  - apply Z.mod_small. lia. }
rewrite (Em v Hv), (Em w Hw).
destruct (Z.ltb_spec v 0) as [V | V]; destruct (Z.ltb_spec w 0) as [Wq | Wq];
  apply Bool.eq_iff_eq_true; rewrite !Z.eqb_eq; split; intros HH; lia.
Qed.

(* The 4-byte signed load of an atom holding the unsigned int u (m_lost_cgW.v ml_sext_den). *)
Lemma lc6_sext_den : forall E n u, ew E n = Z_to_bv 64 u -> 0 <= u < 2 ^ 32 ->
  sv_denot E (SExt true 32 (SOff n 0)) = Z_to_bv 64 (bv_swrap 32 u).
Proof.
intros E n u Hn Hu. cbn [sv_denot]. rewrite Hn, Z.add_0_r, Z_to_bv_bv_unsigned.
change (sext 64 (bv_extract 0 32 (Z_to_bv 64 u))) with (Z_to_bv 64 (bv_signed (bv_extract 0 32 (Z_to_bv 64 u)))).
f_equal. rewrite (LMem.signed_of_extract 32 (Z_to_bv 64 u)) by lia.
rewrite unsigned_lit_small by lia. reflexivity.
Qed.

Ltac lc6_reg HS r v H tac :=
  lazymatch type of HS with
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok ?segsx ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_restrict_reg segsx Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | st_ok_pi ?segsx ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | ?T => idtac "lc6_reg: no match for" T; fail
  end.

(* The windows a run wrote, each inside the bytes Zs (m_lost_cgW.v ml_win). *)
Ltac lc6_win Hin Hx tac :=
  lazymatch type of Hin with In ?x ?l => let l' := eval vm_compute in l in change (In x l') in Hin end;
  cbn [In] in Hin;
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hx; tac |]);
  destruct Hin.

(* The symbolic states of the stretches. No access of the segment is instrumented: no shadow entry; atom 26 is s10,
   the shadow base. *)
Definition LC6_Bx : sv := SOff 26 0.
(* +0x8dc: M.fly.on, at a2 = M (atom 12). *)
Definition lc6_fly : YP09.region := YP09.mkRegion (Some 12%nat) 96 100 96 100 [].
Definition lc6_d1_ss : sstate := mkSS LC6_D1 sr_atoms [lc6_fly] None (mkFacts [(12%nat, mkAF TB_M TB_M 5)] [] []).
(* +0x8c4: OW.e3 at s9 = OW (atom 25; 0 since the memset), M.fail. *)
Definition lc6_e3 : YP09.region := YP09.mkRegion (Some 25%nat) 200 204 200 204 [YP09.mkChunk 200 (YP09.CVal 4 (SLit 0))].
Definition lc6_fail : YP09.region := YP09.mkRegion (Some 12%nat) 88 92 88 92 [].
Definition lc6_c2e_ss : sstate :=
  mkSS LC6_C2E sr_atoms [lc6_e3; lc6_fail] None (mkFacts [(12%nat, mkAF TB_M TB_M 5); (25%nat, mkAF TB_OW TB_OW 5)] [] []).
(* +0x890: the byte g_fail_next at the page hi 10 + 0x678 (atom 32), the spill slots 168(s1) and 184(s1) holding M
   (image object 8) and the page (the listing's hi 10), M's fields desk_known (atom 33), M.state (atom 35),
   M.foreign (atom 34) as the world holds them, and the two fields the stretch stores, M.fail and OW.desk_off. *)
Definition lc6_c1_gfn : YP09.region :=
  YP09.mkRegion (Some (A_HI 10)) 0x678 0x679 0 0 [YP09.mkChunk 0x678 (YP09.CVal 1 (SOff 32 0))].
Definition lc6_c1_sp : YP09.region :=
  YP09.mkRegion (Some 9%nat) 168 192 0 0
    [YP09.mkChunk 168 (YP09.CVal 8 (SOff (A_OBJ 8) 0)); YP09.mkChunk 184 (YP09.CVal 8 (SOff (A_HI 10) 0))].
Definition lc6_c1_dk : YP09.region := YP09.mkRegion (Some (A_OBJ 8)) 0 4 0 0 [YP09.mkChunk 0 (YP09.CVal 4 (SOff 33 0))].
Definition lc6_c1_st : YP09.region := YP09.mkRegion (Some (A_OBJ 8)) 12 16 0 0 [YP09.mkChunk 12 (YP09.CVal 4 (SOff 35 0))].
Definition lc6_c1_fr : YP09.region := YP09.mkRegion (Some (A_OBJ 8)) 24 28 0 0 [YP09.mkChunk 24 (YP09.CVal 4 (SOff 34 0))].
Definition lc6_c1_fail : YP09.region := YP09.mkRegion (Some (A_OBJ 8)) 88 92 88 92 [].
Definition lc6_c1_doff : YP09.region := YP09.mkRegion (Some 25%nat) 232 236 232 236 [].
Definition lc6_c1_facts : facts :=
  mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (25%nat, mkAF TB_OW TB_OW 5);
           (A_OBJ 8, mkAF TB_M TB_M 5); (32%nat, mkAF 0 255 0); (33%nat, mkAF 0 (2 ^ 32 - 1) 0);
           (34%nat, mkAF 0 (2 ^ 32 - 1) 0); (35%nat, mkAF 0 (2 ^ 32 - 1) 0)] [] [].
Definition lc6_c1_ss : sstate :=
  mkSS LC6_C1 sr_atoms [lc6_c1_gfn; lc6_c1_sp; lc6_c1_dk; lc6_c1_st; lc6_c1_fr; lc6_c1_fail; lc6_c1_doff] None
    lc6_c1_facts.
(* The values of atoms 32 .. 35 at the world X: the byte g_fail_next, M.desk_known, M.foreign, M.state (unsigned). *)
Definition lc6_c1_ex (X : list byte) : list word :=
  [Z_to_bv 64 (TW.u_at X TW.OFF_g_fail_next 1); Z_to_bv 64 (TW.u_at X TW.A_M_desk_known 4);
   Z_to_bv 64 (TW.u_at X TW.A_M_foreign 4); Z_to_bv 64 (TW.u_at X TW.A_M_state 4)].

Section seg. Context {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XL : Z -> Z.
Variables RLO RHI : Z.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).

(* The walk's valuation agrees with the registers below atom 32. *)
Lemma lc6_agree : forall regs extra E,
  (forall n, (n < 32)%nat -> ew E n = ew (Eimg (PI := PI_transportb) (Ereg regs extra)) n) ->
  ed E = ed (Eimg (PI := PI_transportb) (Ereg regs extra)) -> env_agree 32 (Ereg regs extra) E.
Proof.
intros regs extra E H1 H2. split.
- intros n Hn. rewrite (H1 n Hn). apply Eimg_low. unfold A_TEXT. lia.
- rewrite H2. reflexivity.
Qed.

(* A symbolic state with no region holds of any machine state at its pc (diginet_session_close_seg_join.v). *)
Lemma lc6_entry0 : forall {fx : YK11.FPState} (W : world tfibsegs) regs mem (pc : Z),
  st_ok_pi tfibsegs VAL (Eimg (PI := PI_transportb) (Ereg regs []))
    (mkSS pc sr_atoms [] None (mkFacts [] [] []))
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + pc)) mem (YK11.seg_rom tfibsegs))).
Proof.
intros fx W regs mem pc. rewrite restrict_mkst_fx.
apply (pa_entry_st_ok_full (PI := PI_transportb)).
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_nil.
- apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. exact I.
- unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. repeat split; exact I.
Qed.

(* A register atom's value in the walk's valuation. *)
Lemma lc6_U : forall (regs : bvmap 5 word) extra n (r : bv 5) v, Z.of_nat n = bv_unsigned r ->
  YK11.getr regs r = w64 v -> 0 <= v < 2 ^ 64 ->
  bv_unsigned (ew (Eimg (PI := PI_transportb) (Ereg regs extra)) n) = v.
Proof.
intros regs extra n r v Hn Hr Hv. rewrite (can_ew_Eimg_Ereg_nat regs extra n r Hn), Hr. unfold w64.
apply unsigned_lit_small. exact Hv.
Qed.

(* The registers lc_core fixes, moved to another register file that keeps them. *)
Lemma lc6_core_regs : forall cx ly S W regsA regsB m md e,
  lc_core B cx ly S W regsA m md e -> lc6_rk regsA regsB -> lc_core B cx ly S W regsB m md e.
Proof.
intros cx ly S W regsA regsB m md e HC HRK.
destruct HC as (HJ & Hfr & HlyF & Hperm & Rsp & R8 & R9 & Rgp & Rtp & Hrest).
refine (conj HJ (conj Hfr (conj HlyF (conj Hperm (conj _ (conj _ (conj _ (conj _ (conj _ Hrest))))))))).
- exact (eq_trans (HRK (Z_to_bv 5 2) ltac:(lc6_inK)) Rsp).
- exact (eq_trans (HRK (Z_to_bv 5 8) ltac:(lc6_inK)) R8).
- exact (eq_trans (HRK (Z_to_bv 5 9) ltac:(lc6_inK)) R9).
- exact (eq_trans (HRK (Z_to_bv 5 3) ltac:(lc6_inK)) Rgp).
- exact (eq_trans (HRK (Z_to_bv 5 4) ltac:(lc6_inK)) Rtp).
Qed.

(* What lc6_km gives lc_core_kept (X = 4096): the bytes at or above alloc_ceiling outside the window, the input's
   bytes (a block: not a byte of G, below alloc_ceiling), the frame's last word (the frame: not a byte of G, below
   alloc_ceiling) and the presence of the frame's bytes. *)
Lemma lc6_kabf : forall cx ly' S' (W' : world segs) regs' m1 md1 e m2,
  AR_laws segs B -> lc_base B MT XL RLO RHI cx -> lc_core B cx ly' S' W' regs' m1 md1 e -> lc6_km cx W' m1 m2 ->
  (forall a, YM05.alloc_ceiling <= a < 2 ^ 64 -> ~ (lc_sp1 cx - 4096 <= a < lc_sp1 cx) ->
     aview segs (w_H W') m2 a = aview segs (w_H W') m1 a) /\
  (forall i, 0 <= i < l_n cx -> aview segs (w_H W') m2 (l_p cx + i) = aview segs (w_H W') m1 (l_p cx + i)) /\
  (forall a, lc_F cx + LF_FBYTES - 8 <= a < lc_F cx + LF_FBYTES ->
     aview segs (w_H W') m2 a = aview segs (w_H W') m1 a) /\
  (forall a, lc_F cx <= a < lc_F cx + LF_FBYTES -> apresent (w_H W') m1 a -> apresent (w_H W') m2 a).
Proof.
intros cx ly' S' W' regs' m1 md1 e m2 LAWS HB HC [HKM HKP].
pose proof (lc_geom B MT XL RLO RHI cx ly' S' W' regs' m1 md1 e HB HC) as G.
destruct G as [HARg Hsp0al Hstk Hsp1c HFaddr HFin Hn HINg HLIVEg].
pose proof HC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hsp1 & Hsp1al & _ & HF4096 & HFal & HFceil & _).
pose proof asan_consts as ((CVlo & CVhi) & _).
assert (GHI : forall a, inG TG.G_HARNESS_B a -> a < TG.G_HARNESS_B_HI)
  by (intros a Ha; exact (proj2 (inG_G_HARNESS_hull a Ha))).
unfold TG.G_HARNESS_B_HI in GHI.
unfold LF_FBYTES in *.
split; [|split; [|split]].
- intros a Ha Hw. apply HKM; [lia | intros HG; pose proof (GHI a HG); lia | exact Hw].
- intros i Hi.
  assert (Hin : In (l_p cx, l_n cx) (ablocks B ly' S')) by (apply HINg; lia).
  destruct (al_blocks _ _ LAWS ly' S' W' m1 md1 (l_p cx) (l_n cx) HARg Hin) as (_ & H4096 & Hbc & _).
  assert (Hreq : req_size (l_n cx) = l_n cx) by (unfold req_size; destruct (Z.eqb_spec (l_n cx) 0); lia).
  rewrite Hreq in Hbc.
  apply HKM; [lia | | lia].
  intros HG. exact (blk_img segs B LAWS ly' S' W' m1 md1 (l_p cx) (l_n cx) (l_p cx + i) HARg Hin
    ltac:(rewrite Hreq; lia) (trans_g_img (l_p cx + i) HG)).
- intros a Ha. apply HKM; [lia | | lia].
  intros HG. apply (frm_img segs B LAWS ly' S' W' m1 md1 LF_CID (l_fpos cx) a HARg HFin);
    [rewrite HFaddr; change (fs_frame_bytes LF_CID) with 256; lia | exact (trans_g_img a HG)].
- intros a _ Ha. exact (HKP a Ha).
Qed.

(* The cut MSET from the walk's last facts: the core at the last memory, the kept registers, the kept view, the
   model's op_begin world and lc_close_w's world, a0 = S_CLOSED, a1 = R_CLOSED. *)
Lemma lc6_cut : forall cx op ly' S' (W' : world segs) regs' mem' md' e regsF memF mdF B2,
  lc_base B MT XL RLO RHI cx ->
  lc_lcore B MT cx op false false (lo_k op) ly' S' W' regs' mem' md' e ->
  lc_opc (l_pl cx) (lo_c op) = 6 ->
  lc_cur cx regs' 24 27 (lc_oc (l_pl cx) (lo_c op)) -> lc_s46 cx regs' ->
  lc_core B cx ly' S' W' regs' memF mdF e -> lc6_rk regs' regsF -> lc6_km cx W' mem' memF ->
  lc_close_w (lc6_B1 (lo_B op)) = Some B2 -> lc_tw W' memF B2 ->
  YK11.getr regsF (Z_to_bv 5 10) = w64 3 -> YK11.getr regsF (Z_to_bv 5 11) = w64 8 ->
  lc_st_mset B MT cx op W'
    (mkCfg (@YK11.mkst (l_fx cx) regsF (Z_to_bv 64 (BASE + LO_MSET)) memF (YK11.seg_rom segs)) mdF).
Proof.
intros cx op ly' S' W' regs' mem' md' e regsF memF mdF B2 HB HL Ho Hcur Hs46 HCF HRK HKM HMC HTW R10 R11.
destruct HL as (HC & HFR & HSP & HFSH & HOK & HEV & HMT & R19).
pose proof (lc_geom B MT XL RLO RHI cx ly' S' W' regs' mem' md' e HB HC) as G.
destruct G as [HARg Hsp0al Hstk Hsp1c HFaddr HFin Hn HINg HLIVEg].
pose proof HC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hsp1 & Hsp1al & _ & HF4096 & HFal & HFceil & _).
pose proof asan_consts as ((CVlo & CVhi) & _).
assert (GHI : forall a, inG TG.G_HARNESS_B a -> a < TG.G_HARNESS_B_HI)
  by (intros a Ha; exact (proj2 (inG_G_HARNESS_hull a Ha))).
unfold TG.G_HARNESS_B_HI in GHI.
assert (HF8 : 0 <= lc_F cx / 8 <= lc_F cx) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
assert (HSH : lc_SH cx = SHADOW_OFF + lc_F cx / 8) by reflexivity. unfold SHADOW_OFF in HSH.
destruct Hstk as (Hst1 & Hst2 & Hst3 & Hst4). destruct Hsp1 as [Hsp1a Hsp1b]. destruct HF8 as [HF8a HF8b].
change (2 ^ 47) with 140737488355328 in Hst4. unfold LF_FBYTES, LF_FRAME, LLVMF_STK in *.
destruct HKM as [HKV _].
exists ly', S', regsF, memF, mdF, e, (lc6_B1 (lo_B op)), B2.
split. { unfold lc_cfg. rewrite lc6_base. reflexivity. }
split; [exact Ho|].
split.
{ refine (conj (lc6_core_regs cx ly' S' W' regs' regsF memF mdF e HCF HRK)
    (conj _ (conj _ (conj _ (conj HOK (conj HEV (conj HMT _))))))).
  - destruct HFR as [R18 R26]. split.
    + exact (eq_trans (HRK (Z_to_bv 5 18) ltac:(lc6_inK)) R18).
    + exact (eq_trans (HRK (Z_to_bv 5 26) ltac:(lc6_inK)) R26).
  - apply (lc_spills_kept cx _ (aview segs (w_H W') mem')); [| | exact HSP].
    + intros o Ho'. pose proof (lf_spill_vals (lc_F cx) ltac:(lia) ltac:(unfold LF_FBYTES; lia)) as HV.
      rewrite Forall_forall in HV. destruct (HV o Ho') as (_ & _ & H8 & H192). lia.
    + intros a Ha. apply HKV; [lia | intros HG; pose proof (GHI a HG); lia | lia].
  - apply (lc_fsh_kept cx (aview segs (w_H W') mem')); [| exact HFSH].
    intros a Ha. apply HKV; [lia | intros HG; pose proof (GHI a HG); lia | lia].
  - exact (eq_trans (HRK (Z_to_bv 5 19) ltac:(lc6_inK)) R19). }
split; [exact (lc6_begin _)|]. split; [exact HMC|]. split; [exact HTW|].
split; [exact R10|]. split; [exact R11|].
split.
{ destruct Hcur as [C24 C27]. split.
  - exact (eq_trans (HRK (Z_to_bv 5 24) ltac:(lc6_inK)) C24).
  - exact (eq_trans (HRK (Z_to_bv 5 27) ltac:(lc6_inK)) C27). }
destruct Hs46 as [S20 S22]. split.
- exact (eq_trans (HRK (Z_to_bv 5 20) ltac:(lc6_inK)) S20).
- exact (eq_trans (HRK (Z_to_bv 5 22) ltac:(lc6_inK)) S22).
Qed.

(* A payload byte of a row of TMAP_B is a byte of G (io_send_seg_world.v ios_inG_row). *)
Lemma lc6_inG_row : forall o b n a, In (o, b, n) TMAP_B -> b <= a < b + n -> inG TG.G_HARNESS_B a.
Proof.
intros o b n a Hin Ha. unfold inG. apply Exists_exists. exists (b, n).
split; [exact (TMAP_B_in_G o b n Hin) | unfold in_zr; cbn [fst snd]; lia].
Qed.

(* The registers of LC6_KEEP a symbolic state still holds as their own atoms. *)
Lemma lc6_rk_st : forall {fx : YK11.FPState} E ss (H : word -> bool) ms regs0 extra,
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok segs E ss (restrict H ms) ->
  env_agree 32 (Ereg regs0 extra) E ->
  forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) LC6_KEEP = true ->
  lc6_rk regs0 (ms_regs ms).
Proof.
intros fx E ss H ms regs0 extra HS HA Hl r Hr.
exact (regs_kept_of_st_ok segs E ss (restrict H ms) regs0 extra LC6_KEEP HS HA Hl r Hr).
Qed.

(* The fields of OW and M are bytes of G. *)
Lemma lc6_inG_OW : forall a, TB_OW <= a < TB_OW + 304 -> inG TG.G_HARNESS_B a.
Proof. intros a Ha. apply (lc6_inG_row _ _ _ a TMAP_B_OW). unfold TW.SZ_OW. lia. Qed.
Lemma lc6_inG_M : forall a, TB_M <= a < TB_M + 1648 -> inG TG.G_HARNESS_B a.
Proof. intros a Ha. apply (lc6_inG_row _ _ _ a TMAP_B_M). unfold TW.SZ_M. lia. Qed.

(* The state at +0x890 holds of the machine state there. *)
Lemma lc6_c1_entry : forall {fx : YK11.FPState} (W : world segs) regs mem X s1,
  YK11.getr regs (Z_to_bv 5 9) = w64 s1 -> YK11.getr regs (Z_to_bv 5 25) = w64 TB_OW ->
  2 ^ 46 <= s1 -> s1 + 192 <= 2 ^ 47 -> s1 mod 32 = 0 ->
  rdword (aview segs (w_H W) mem) (s1 + 168) = Some TB_M ->
  rdword (aview segs (w_H W) mem) (s1 + 184) = Some (transportb_hi 10) ->
  tw_at TMAP_B (aview segs (w_H W) mem) X ->
  st_ok_pi segs VAL (Eimg (PI := PI_transportb) (Ereg regs (lc6_c1_ex X))) lc6_c1_ss
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + LC6_C1)) mem (YK11.seg_rom segs))).
Proof.
intros fx W regs mem X s1 R9 R25 Hs1a Hs1b Hs1c HSM HSG Htw.
set (E := Eimg (PI := PI_transportb) (Ereg regs (lc6_c1_ex X))).
destruct lc6_hi as [EH EGA].
assert (EM : TB_M = 6155744) by reflexivity. assert (EO : TB_OW = 6237408) by reflexivity.
assert (EG : TB_g_fail_next = 6155680) by reflexivity.
change (2 ^ 46) with 70368744177664 in Hs1a. change (2 ^ 47) with 140737488355328 in Hs1b.
assert (U9 : bv_unsigned (ew E 9%nat) = s1)
  by (unfold E; exact (lc6_U regs _ 9 (Z_to_bv 5 9) s1 eq_refl R9 ltac:(lia))).
assert (U25 : bv_unsigned (ew E 25%nat) = TB_OW)
  by (unfold E; exact (lc6_U regs _ 25 (Z_to_bv 5 25) TB_OW eq_refl R25 ltac:(lia))).
assert (U249 : bv_unsigned (ew E 249%nat) = TB_M).
{ unfold E. rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia). change 249%nat with (A_OBJ 8).
  rewrite (proj1 lc6_vals). first [reflexivity | apply unsigned_lit_small; lia]. }
assert (U8 : bv_unsigned (ew E (A_OBJ 8)) = TB_M) by exact U249.
assert (U410 : bv_unsigned (ew E 410%nat) = transportb_hi 10).
{ unfold E. rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia). change 410%nat with (A_HI 10).
  rewrite (proj2 (proj2 (proj2 lc6_vals))). first [reflexivity | apply unsigned_lit_small; lia]. }
assert (UH : bv_unsigned (ew E (A_HI 10)) = transportb_hi 10) by exact U410.
pose proof (TWL.u_at_range X TW.OFF_g_fail_next 1) as Rg. pose proof (TWL.u_at_range X TW.A_M_desk_known 4) as Rd.
pose proof (TWL.u_at_range X TW.A_M_foreign 4) as Rf. pose proof (TWL.u_at_range X TW.A_M_state 4) as Rs.
change (2 ^ (8 * Z.of_nat 1)) with 256 in Rg. change (2 ^ (8 * Z.of_nat 4)) with 4294967296 in Rd, Rf, Rs.
assert (E32 : ew E 32 = Z_to_bv 64 (TW.u_at X TW.OFF_g_fail_next 1))
  by (unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (TW.u_at X TW.A_M_desk_known 4))
  by (unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (TW.u_at X TW.A_M_foreign 4))
  by (unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 (TW.u_at X TW.A_M_state 4))
  by (unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
rewrite restrict_mkst_fx. unfold lc6_c1_ss.
apply (pa_entry_st_ok_full (PI := PI_transportb)).
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [lc6_c1_gfn lc6_c1_sp lc6_c1_dk lc6_c1_st lc6_c1_fr lc6_c1_fail lc6_c1_doff
      YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  + rewrite ?UH, ?U410. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val segs E _ (transportb_hi 10) 0x678 1 (SOff 32 0) (TW.u_at X TW.OFF_g_fail_next 1));
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | lia |].
    rewrite EGA. replace TB_g_fail_next with (TB_g_fail_next + 0) by lia.
    pose proof (tw_read_val segs (mrestrict (w_H W) mem) TMAP_B X TW.OFF_g_fail_next TB_g_fail_next 1 0 1 TMAP_B_ok
      Htw TMAP_B_g_fail_next ltac:(lia) ltac:(lia)) as HV.
    rewrite Z.add_0_r in HV. exact HV.
  + rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor; [|constructor]].
    * apply (chunk_ok_val segs E _ s1 168 8 (SOff (A_OBJ 8) 0) TB_M);
        [cbn [sv_denot]; rewrite ?U8, ?U249, Z.add_0_r; reflexivity | cbn; lia | lia |].
      exact (val_mem_of_rdword segs (w_H W) mem _ _ HSM).
    * apply (chunk_ok_val segs E _ s1 184 8 (SOff (A_HI 10) 0) (transportb_hi 10));
        [cbn [sv_denot]; rewrite ?UH, ?U410, Z.add_0_r; reflexivity | cbn; lia | lia |].
      exact (val_mem_of_rdword segs (w_H W) mem _ _ HSG).
  + rewrite ?U8, ?U249. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val segs E _ TB_M 0 4 (SOff 33 0) (TW.u_at X TW.A_M_desk_known 4));
      [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | lia |].
    exact (tw_read_val segs (mrestrict (w_H W) mem) TMAP_B X TW.OFF_M TB_M TW.SZ_M 0 4 TMAP_B_ok Htw TMAP_B_M
      ltac:(lia) ltac:(unfold TW.SZ_M; lia)).
  + rewrite ?U8, ?U249. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val segs E _ TB_M 12 4 (SOff 35 0) (TW.u_at X TW.A_M_state 4));
      [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | lia |].
    exact (tw_read_val segs (mrestrict (w_H W) mem) TMAP_B X TW.OFF_M TB_M TW.SZ_M 12 4 TMAP_B_ok Htw TMAP_B_M
      ltac:(lia) ltac:(unfold TW.SZ_M; lia)).
  + rewrite ?U8, ?U249. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val segs E _ TB_M 24 4 (SOff 34 0) (TW.u_at X TW.A_M_foreign 4));
      [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | lia |].
    exact (tw_read_val segs (mrestrict (w_H W) mem) TMAP_B X TW.OFF_M TB_M TW.SZ_M 24 4 TMAP_B_ok Htw TMAP_B_M
      ltac:(lia) ltac:(unfold TW.SZ_M; lia)).
  + rewrite ?U8, ?U249. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS_B (TB_M + o) G_HARNESS_B_rw). apply lc6_inG_M. lia.
  + rewrite U25. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS_B (TB_OW + o) G_HARNESS_B_rw). apply lc6_inG_OW. lia.
- apply pairwise_disjoint_of_extents.
  unfold lc6_c1_gfn, lc6_c1_sp, lc6_c1_dk, lc6_c1_st, lc6_c1_fr, lc6_c1_fail, lc6_c1_doff, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite U9, U25, ?U8, ?U249, ?UH, ?U410.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  repeat split; first [exact I | lia].
- unfold lc6_c1_facts, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite U9, U25, ?U8, ?U249, E32, E33, E34, E35, !unsigned_lit_small by lia.
  change (2 ^ 5) with 32. change (2 ^ 46) with 70368744177664. change (2 ^ 47) with 140737488355328.
  rewrite !Z.pow_0_r, !Z.mod_1_r.
  repeat match goal with |- _ /\ _ => split end; try exact I; rewrite ?EM, ?EO; first [lia | reflexivity].
Qed.

(* The state at +0x8dc holds of the machine state there. *)
Lemma lc6_d1_entry : forall {fx : YK11.FPState} (W : world segs) regs mem,
  YK11.getr regs (Z_to_bv 5 12) = w64 TB_M ->
  st_ok_pi segs VAL (Eimg (PI := PI_transportb) (Ereg regs [])) lc6_d1_ss
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + LC6_D1)) mem (YK11.seg_rom segs))).
Proof.
intros fx W regs mem R12.
set (E := Eimg (PI := PI_transportb) (Ereg regs [])).
assert (U12 : bv_unsigned (ew E 12%nat) = TB_M)
  by (unfold E; exact (lc6_U regs _ 12 (Z_to_bv 5 12) TB_M eq_refl R12 ltac:(unfold TB_M; lia))).
assert (EM : TB_M = 6155744) by reflexivity.
rewrite restrict_mkst_fx. unfold lc6_d1_ss.
apply (pa_entry_st_ok_full (PI := PI_transportb)).
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [lc6_fly YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite U12. split; [lia|]. split; [lia|]. split; [|constructor].
  intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS_B (TB_M + o) G_HARNESS_B_rw). apply lc6_inG_M. lia.
- apply pairwise_disjoint_of_extents.
  unfold lc6_fly, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
  cbn [zpairwise_disjoint zall_disjoint]. repeat split; exact I.
- unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite U12. change (2 ^ 5) with 32.
  repeat match goal with |- _ /\ _ => split end; try exact I; rewrite ?EM; first [lia | reflexivity].
Qed.

(* The state at +0x8c4 (OW.e3 is 0 at the world X). *)
Lemma lc6_c2e_entry : forall {fx : YK11.FPState} (W : world segs) regs mem X,
  YK11.getr regs (Z_to_bv 5 12) = w64 TB_M -> YK11.getr regs (Z_to_bv 5 25) = w64 TB_OW ->
  tw_at TMAP_B (aview segs (w_H W) mem) X -> TW.u_at X (TW.OFF_OW + 200) 4 = 0 ->
  st_ok_pi segs VAL (Eimg (PI := PI_transportb) (Ereg regs [])) lc6_c2e_ss
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + LC6_C2E)) mem (YK11.seg_rom segs))).
Proof.
intros fx W regs mem X R12 R25 Htw HZ.
set (E := Eimg (PI := PI_transportb) (Ereg regs [])).
assert (U12 : bv_unsigned (ew E 12%nat) = TB_M)
  by (unfold E; exact (lc6_U regs _ 12 (Z_to_bv 5 12) TB_M eq_refl R12 ltac:(unfold TB_M; lia))).
assert (U25 : bv_unsigned (ew E 25%nat) = TB_OW)
  by (unfold E; exact (lc6_U regs _ 25 (Z_to_bv 5 25) TB_OW eq_refl R25 ltac:(unfold TB_OW; lia))).
assert (EO : TB_OW = 6237408) by reflexivity. assert (EM : TB_M = 6155744) by reflexivity.
rewrite restrict_mkst_fx. unfold lc6_c2e_ss.
apply (pa_entry_st_ok_full (PI := PI_transportb)).
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [lc6_e3 lc6_fail YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  + rewrite U25. split; [lia|]. split; [lia|]. split.
    * intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS_B (TB_OW + o) G_HARNESS_B_rw). apply lc6_inG_OW. lia.
    * constructor; [|constructor].
      apply (chunk_ok_val segs E _ TB_OW 200 4 (SLit 0) 0); [reflexivity | cbn; lia | lia |].
      pose proof (tw_read_val segs (mrestrict (w_H W) mem) TMAP_B X TW.OFF_OW TB_OW TW.SZ_OW 200 4 TMAP_B_ok Htw
        TMAP_B_OW ltac:(lia) ltac:(unfold TW.SZ_OW; lia)) as HV.
      rewrite HZ in HV. exact HV.
  + rewrite U12. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS_B (TB_M + o) G_HARNESS_B_rw). apply lc6_inG_M. lia.
- apply pairwise_disjoint_of_extents.
  unfold lc6_e3, lc6_fail, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite U25, U12. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  repeat split; first [exact I | lia].
- unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite U12, U25. change (2 ^ 5) with 32.
  repeat match goal with |- _ /\ _ => split end; try exact I; rewrite ?EM, ?EO; first [lia | reflexivity].
Qed.

Section op6.
Variable cx : lcx.
Variable op : lop.
Variable ly' : alayout.
Variable S' : astate.
Variable W' : world segs.
Variable regs' : bvmap 5 word.
Variable mem' : word -> option byte.
Variable md' : Model.
Variable e : Z.
Hypothesis HP : lp_prem B MT XL RLO RHI.
Hypothesis HB : lc_base B MT XL RLO RHI cx.
Hypothesis HL : lc_lcore B MT cx op false false (lo_k op) ly' S' W' regs' mem' md' e.
Hypothesis Ho : lc_opc (l_pl cx) (lo_c op) = 6.
Hypothesis Hcur : lc_cur cx regs' 24 27 (lc_oc (l_pl cx) (lo_c op)).
Hypothesis Hs46 : lc_s46 cx regs'.
Hypothesis Htw0 : lc_tw W' mem' (lo_B op).

(* What every stretch carries: the core at the current memory (at the cut's registers), the kept registers and the
   kept view. *)
Definition lc6_st (regsX : bvmap 5 word) (memX : word -> option byte) (mdX : Model) : Prop :=
  lc_core B cx ly' S' W' regs' memX mdX e /\ lc6_rk regs' regsX /\ lc6_km cx W' mem' memX.

Local Abbreviation Q := (lc_st_mset B MT cx op).
Local Abbreviation cfgX regsX pc memX mdX :=
  (mkCfg (@YK11.mkst (l_fx cx) regsX (Z_to_bv 64 (BASE + pc)) memX (YK11.seg_rom segs)) mdX).

(* The stack: sp1, sp0 and the memsets' window. *)
Lemma lc6_sp : YM05.alloc_ceiling + 32432 <= lc_sp1 cx /\ lc_sp0 cx - 336 <= lc_sp1 cx <= lc_sp0 cx - 320 /\
  lc_sp0 cx <= 2 ^ 47 /\ (lc_sp1 cx - lc_sp0 cx) mod 16 = 0.
Proof.
pose proof HL as (HC & _).
pose proof (lc_geom B MT XL RLO RHI cx ly' S' W' regs' mem' md' e HB HC) as G.
destruct G as [HARg Hsp0al Hstk Hsp1c HFaddr HFin Hn HINg HLIVEg].
pose proof HC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hsp1 & Hsp1al & _).
destruct Hstk as (_ & _ & Hst3 & Hst4). unfold LF_FRAME in Hsp1.
split; [exact Hsp1c|]. split; [exact Hsp1|]. split; [lia|].
rewrite Zminus_mod. replace (lc_sp1 cx mod 16) with 0 by (Z.div_mod_to_equations; lia). rewrite Hsp0al. reflexivity.
Qed.

(* The step of the core over a memory the walk kept (lc_core_kept at X = 4096 and the cut's registers). *)
Ltac lc6_core HC HJ2 HKM HCn :=
  let KA := fresh "KA" in let KI := fresh "KI" in let KF := fresh "KF" in let GA := fresh "GA" in
  destruct (lc6_kabf _ _ _ _ _ _ _ _ _ (lp_laws _ _ _ _ _ HP) HB HC HKM) as (KA & KI & KF & GA);
  pose proof (lc_core_kept B MT XL RLO RHI cx ly' S' W' regs' _ _ e 4096 ly' S' W' regs' _ _ e
    HB HC HJ2 eq_refl (Permutation_refl _) (fun r _ => eq_refl) ltac:(unfold LLVMF_STK; lia) KA KI KF GA) as HCn;
  clear KA KI KF GA.

(* +0x8dc .. +0x8e4: M.fly.on := 0, a0 = 3, a1 = 8; the cut MSET. *)
Lemma lc6_D1 : forall X regsX memX mdX, lc6_st regsX memX mdX ->
  YK11.getr regsX (Z_to_bv 5 12) = w64 TB_M -> lc_tw W' memX X ->
  lc_close_w (lc6_B1 (lo_B op)) = Some (TW.set_M_fly_on X 0) ->
  SRr segs W' (cfgX regsX LC6_D1 memX mdX) Q.
Proof.
intros X regsX memX mdX (HC & HRK & HKM) R12 HTW HMC.
pose proof (lp_laws _ _ _ _ _ HP) as LAWS.
pose proof (G_HARNESS_gx_ok B (lp_g_unowned _ _ _ _ _ HP)) as HGX.
pose proof HC as (HJ & _).
pose proof (lc6_d1_entry (fx := l_fx cx) W' regsX memX R12) as HS.
set (E0 := Eimg (PI := PI_transportb) (Ereg regsX [])) in HS.
assert (HEI : img_env VAL A_LIM E0) by (unfold E0; apply Eimg_env).
assert (SHOK : sh_ok segs LC6_Bx (@nil shent) E0 (mrestrict (w_H W') memX)) by constructor.
assert (U12 : bv_unsigned (ew E0 12%nat) = TB_M)
  by (unfold E0; exact (lc6_U regsX [] 12 (Z_to_bv 5 12) TB_M eq_refl R12 ltac:(unfold TB_M; lia))).
pose proof (@paj_run_to_x (l_fx cx) rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS
  TG.G_HARNESS_B HGX 0 []) as RUNTO.
paj_run_to_tok RUNTO HS HJ SHOK (0, 0) LO_MSET.
{ lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
  apply awr_ok_x_cons_g;
    [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U12 in Ha; apply lc6_inG_M; lia |].
  apply awr_ok_x_nil. }
set (md1 := with_vm_backing (m_vm_lazy mdX) mat mdX) in *. clearbody md1. clear mat.
pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RG0. cbn [ms_mem restrict] in RG0.
pose proof (lc6_chunk _ _ _ _ _ _ _ _ _ TB_M 96 (SLit 0) 0 RG0 U12 ltac:(cbn [In]; tauto) eq_refl) as VF.
assert (KR : forall a, 0 <= a < 2 ^ 64 -> ~ (TB_M + 96 <= a < TB_M + 100) ->
  aview segs (w_H W') (ms_mem ms) a = aview segs (w_H W') memX a).
{ intros a Ha Hn. apply (kept_of_frame _ _ _ _ _ (fun x => TB_M + 96 <= x < TB_M + 100) HFr); [| exact Ha | exact Hn].
  intros b wlo whi x Hin Hx. lc6_win Hin Hx ltac:(rewrite ?U12 in Hx; lia). }
assert (GR : forall a, apresent (w_H W') memX a -> apresent (w_H W') (ms_mem ms) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
clear HF HFr HG RG0.
assert (HKMr : lc6_km cx W' memX (ms_mem ms)).
{ split; [|exact GR]. intros a Ha HnG _. apply KR; [exact Ha|]. intros H1. apply HnG. apply lc6_inG_M. lia. }
assert (HTWF : lc_tw W' (ms_mem ms) (TW.set_M_fly_on X 0)).
{ apply (lc6_w_fly _ (aview segs (w_H W') memX) _ HTW VF).
  intros x Hx N1. pose proof (TMAP_B_hull x Hx) as Hh. unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in Hh.
  exact (KR x ltac:(lia) N1). }
lc6_core HC HJ HKMr HCF.
assert (HRKr : lc6_rk regsX (ms_regs ms)).
{ apply (lc6_rk_st _ _ _ ms regsX [] HS); [apply lc6_agree; [intros n Hn; reflexivity | reflexivity] |].
  vm_compute. reflexivity. }
lc6_reg HS (Z_to_bv 5 10) (Z_to_bv 64 3) Q10 ltac:(reflexivity).
lc6_reg HS (Z_to_bv 5 11) (Z_to_bv 64 8) Q11 ltac:(reflexivity).
pmkst HS.
apply (SRr_ret segs).
exact (lc6_cut cx op ly' S' W' regs' mem' md' e (ms_regs ms) (ms_mem ms) md1 (TW.set_M_fly_on X 0)
  HB HL Ho Hcur Hs46 HCF (lc6_rk_trans _ _ _ HRK HRKr) (lc6_km_trans _ _ _ _ _ HKM HKMr) HMC HTWF Q10 Q11).
Qed.

(* The length of the operation's start world. *)
Lemma lc6_lenB : Z.of_nat (length (lo_B op)) = TW.W_LEN.
Proof. rewrite (tw_len _ _ _ Htw0). rewrite Z2Nat.id; [reflexivity | unfold TW.W_LEN; lia]. Qed.

(* +0x8c4 .. +0x8d8 (desk known, not foreign, not closed): a1 = OW.e3 = 0, a0 = 1, the UBSan test `bge a0, a1`
   (decided by the run: its fall-through, the trap edge 0x81b70, is not reached), OW.e3 := 1, M.fail := 0; on to
   +0x8dc (lc6_D1) at m_close's world before M.fly.on. *)
Lemma lc6_C2e : forall regsX memX mdX, lc6_st regsX memX mdX ->
  YK11.getr regsX (Z_to_bv 5 12) = w64 TB_M -> YK11.getr regsX (Z_to_bv 5 25) = w64 TB_OW ->
  lc_tw W' memX (lc6_B1 (lo_B op)) ->
  (TC.truth (TW.M_desk_known (lc6_B1 (lo_B op))) && negb (TC.truth (TW.M_foreign (lc6_B1 (lo_B op)))) &&
   negb (TW.M_state (lc6_B1 (lo_B op)) =? TC.S_CLOSED)) = true ->
  SRr segs W' (cfgX regsX LC6_C2E memX mdX) Q.
Proof.
intros regsX memX mdX (HC & HRK & HKM) R12 R25 HTW Hcnd.
pose proof (lp_laws _ _ _ _ _ HP) as LAWS.
pose proof (G_HARNESS_gx_ok B (lp_g_unowned _ _ _ _ _ HP)) as HGX.
pose proof HC as (HJ & _).
pose proof lc6_lenB as HLB.
pose proof (lc6_c2e_entry (fx := l_fx cx) W' regsX memX _ R12 R25 HTW (lc6_zero_B1 _ 200 HLB (or_intror eq_refl)))
  as HS.
set (E0 := Eimg (PI := PI_transportb) (Ereg regsX [])) in HS.
assert (HEI : img_env VAL A_LIM E0) by (unfold E0; apply Eimg_env).
assert (SHOK : sh_ok segs LC6_Bx (@nil shent) E0 (mrestrict (w_H W') memX)) by constructor.
assert (U12 : bv_unsigned (ew E0 12%nat) = TB_M)
  by (unfold E0; exact (lc6_U regsX _ 12 (Z_to_bv 5 12) TB_M eq_refl R12 ltac:(unfold TB_M; lia))).
assert (U25 : bv_unsigned (ew E0 25%nat) = TB_OW)
  by (unfold E0; exact (lc6_U regsX _ 25 (Z_to_bv 5 25) TB_OW eq_refl R25 ltac:(unfold TB_OW; lia))).
pose proof (@paj_run_to_x (l_fx cx) rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS
  TG.G_HARNESS_B HGX 0 []) as RUNTO.
paj_run_to_tok RUNTO HS HJ SHOK (0, 0) LC6_D1.
{ lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
  apply awr_ok_x_cons_g;
    [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U25 in Ha; apply lc6_inG_OW; lia |].
  apply awr_ok_x_cons_g;
    [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U12 in Ha; apply lc6_inG_M; lia |].
  apply awr_ok_x_nil. }
set (md1 := with_vm_backing (m_vm_lazy mdX) mat mdX) in *. clearbody md1. clear mat.
pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RG0. cbn [ms_mem restrict] in RG0.
pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS eq_refl) as RG1. cbn [ms_mem restrict] in RG1.
pose proof (lc6_chunk _ _ _ _ _ _ _ _ _ TB_OW 200 _ 1 RG0 U25 ltac:(cbn [In]; left; reflexivity)
  ltac:(reflexivity)) as VE.
pose proof (lc6_chunk _ _ _ _ _ _ _ _ _ TB_M 88 (SLit 0) 0 RG1 U12 ltac:(cbn [In]; tauto) eq_refl) as VF.
assert (KR : forall a, 0 <= a < 2 ^ 64 -> ~ ((TB_OW + 200 <= a < TB_OW + 204) \/ (TB_M + 88 <= a < TB_M + 92)) ->
  aview segs (w_H W') (ms_mem ms) a = aview segs (w_H W') memX a).
{ intros a Ha Hn.
  apply (kept_of_frame _ _ _ _ _ (fun x => (TB_OW + 200 <= x < TB_OW + 204) \/ (TB_M + 88 <= x < TB_M + 92)) HFr);
    [| exact Ha | exact Hn].
  intros b wlo whi x Hin Hx. lc6_win Hin Hx ltac:(rewrite ?U12, ?U25 in Hx; lia). }
assert (GR : forall a, apresent (w_H W') memX a -> apresent (w_H W') (ms_mem ms) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
clear HF HFr HG RG0 RG1.
assert (HKMr : lc6_km cx W' memX (ms_mem ms)).
{ split; [|exact GR]. intros a Ha HnG _. apply KR; [exact Ha|].
  intros [H1 | H1]; apply HnG; [apply lc6_inG_OW | apply lc6_inG_M]; lia. }
assert (HTWF : lc_tw W' (ms_mem ms) (lc6_B1e (lc6_B1 (lo_B op)))).
{ apply (lc6_w_c2e _ (aview segs (w_H W') memX) _ HTW VE VF).
  intros x Hx N1 N2. pose proof (TMAP_B_hull x Hx) as Hh. unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in Hh.
  apply KR; [lia | intros [H1 | H1]; [exact (N1 H1) | exact (N2 H1)]]. }
lc6_core HC HJ HKMr HCF.
assert (HRKr : lc6_rk regsX (ms_regs ms)).
{ apply (lc6_rk_st _ _ _ ms regsX [] HS); [apply lc6_agree; [intros n Hn; reflexivity | reflexivity] |].
  vm_compute. reflexivity. }
lc6_reg HS (Z_to_bv 5 12) (YK11.getr regsX (Z_to_bv 5 12)) Q12
  ltac:(cbn [sv_denot]; unfold E0; rewrite (can_ew_Eimg_Ereg_nat regsX _ 12 (Z_to_bv 5 12) eq_refl), Z.add_0_r,
        Z_to_bv_bv_unsigned; reflexivity).
(* the model: the test of m_close holds, OW.e3 + 1 = 1 and M.fail := 0 before M.fly.on *)
pose proof (lc6_close_w_eq _ HLB) as EC. rewrite Hcnd in EC. cbv beta iota in EC.
pmkst HS.
exact (lc6_D1 (lc6_B1e (lc6_B1 (lo_B op))) (ms_regs ms) (ms_mem ms) md1
  (conj HCF (conj (lc6_rk_trans _ _ _ HRK HRKr) (lc6_km_trans _ _ _ _ _ HKM HKMr)))
  (eq_trans Q12 R12) HTWF EC).
Qed.

(* The two stored fields and the registers at an exit of the stretch +0x890, from that state. *)
Ltac lc6_c1_exit HS HFr HG KRp GRp ms HJ HCF HKMr HTWF HRKr Q12 Q25 U249 U25 POST DG DM1 HC regsX E0 memX EX :=
  let RG5 := fresh "RG" in let RG6 := fresh "RG" in let VF := fresh "VF" in let VD := fresh "VD" in
  let KR2 := fresh "KR" in let GR2 := fresh "GR" in
  pose proof (st_ok_pi_region_nth _ _ _ 5 _ HS eq_refl) as RG5; cbn [ms_mem restrict] in RG5;
  pose proof (st_ok_pi_region_nth _ _ _ 6 _ HS eq_refl) as RG6; cbn [ms_mem restrict] in RG6;
  pose proof (lc6_chunk _ _ _ _ _ _ _ _ _ TB_M 88 (SOff 32 0) _ RG5 U249 ltac:(cbn [In]; tauto) DG) as VF;
  pose proof (lc6_chunk _ _ _ _ _ _ _ _ _ TB_OW 232 (SLit 18446744073709551615) (-1) RG6 U25
    ltac:(cbn [In]; tauto) DM1) as VD;
  assert (KR2 : forall a, 0 <= a < 2 ^ 64 -> ~ ((TB_OW + 232 <= a < TB_OW + 236) \/ (TB_M + 88 <= a < TB_M + 92)) ->
    aview segs (w_H W') (ms_mem ms) a = aview segs (w_H W') memX a)
  by (intros a Ha Hn; rewrite <- (KRp a Ha Hn);
      apply (kept_of_frame _ _ _ _ _ (fun x => (TB_OW + 232 <= x < TB_OW + 236) \/ (TB_M + 88 <= x < TB_M + 92)) HFr);
      [| exact Ha | exact Hn];
      intros b wlo whi x Hin Hx; lc6_win Hin Hx ltac:(rewrite ?U25, ?U249 in Hx; lia));
  assert (GR2 : forall a, apresent (w_H W') memX a -> apresent (w_H W') (ms_mem ms) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG (GRp a Ha)));
  destruct (POST (ms_mem ms) KR2 GR2 VD VF) as [HKMr HTWF];
  clear RG5 RG6 VF VD KR2 GR2;
  lc6_core HC HJ HKMr HCF;
  assert (HRKr : lc6_rk regsX (ms_regs ms))
  by (apply (lc6_rk_st _ _ _ ms regsX EX HS); [apply lc6_agree; [intros n Hn; reflexivity | reflexivity] |];
      vm_compute; reflexivity);
  lc6_reg HS (Z_to_bv 5 12) (w64 TB_M) Q12 ltac:(cbn [sv_denot]; rewrite U249, Z.add_0_r; reflexivity);
  lc6_reg HS (Z_to_bv 5 25) (YK11.getr regsX (Z_to_bv 5 25)) Q25
    ltac:(cbn [sv_denot]; unfold E0; rewrite (can_ew_Eimg_Ereg_nat regsX _ 25 (Z_to_bv 5 25) eq_refl), Z.add_0_r,
          Z_to_bv_bv_unsigned; reflexivity).
Ltac lc6_c1_awr U249 U25 :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end;
  do 5 (apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |]);
  apply awr_ok_x_cons_g;
    [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U249 in Ha; apply lc6_inG_M; lia |];
  apply awr_ok_x_cons_g;
    [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U25 in Ha; apply lc6_inG_OW; lia |];
  apply awr_ok_x_nil.

(* +0x890 .. +0x8c0: the page of g_fail_next and its byte, a2 = M, a1 = M.desk_known, M.fail := the byte,
   OW.desk_off := -1 (op_begin's world), then the tests of m_close: `beqz a1`, `bnez` M.foreign and `beq` M.state, 3
   to +0x8dc (lc6_D1: the test is false), else +0x8c4 (lc6_C2e). *)
Lemma lc6_C1 : forall regsX memX mdX, lc6_st regsX memX mdX ->
  YK11.getr regsX (Z_to_bv 5 25) = w64 TB_OW -> lc_tw W' memX (lc6_Bm (lo_B op)) ->
  SRr segs W' (cfgX regsX LC6_C1 memX mdX) Q.
Proof.
intros regsX memX mdX (HC & HRK & HKM) R25 HTW.
pose proof (lp_laws _ _ _ _ _ HP) as LAWS.
pose proof (G_HARNESS_gx_ok B (lp_g_unowned _ _ _ _ _ HP)) as HGX.
pose proof lc6_sp as (Hsp1c & Hsp1 & Hsp0 & Ho16). destruct Hsp1 as [Hsp1a Hsp1b].
change (2 ^ 47) with 140737488355328 in Hsp0.
pose proof asan_consts as ((CVlo & CVhi) & _).
pose proof HC as (HJ & _ & _ & _ & _ & _ & R9c & _ & _ & _ & Hsp1al & _).
pose proof HL as (_ & _ & HSP & _).
pose proof lc6_lenB as HLB.
assert (R9 : YK11.getr regsX (Z_to_bv 5 9) = w64 (lc_sp1 cx)) by exact (eq_trans (HRK (Z_to_bv 5 9) ltac:(lc6_inK)) R9c).
(* the spill slots of M and of g_fail_next's page, at this memory *)
assert (HSK : forall o v, In (o, v) (lf_spill_loop (lc_F cx)) -> 8 <= o -> o + 8 <= 192 ->
  rdword (aview segs (w_H W') memX) (lc_sp1 cx + o) = Some v).
{ intros o v Hin Ho1 Ho2. unfold lc_spills in HSP. rewrite Forall_forall in HSP.
  pose proof (HSP (o, v) Hin) as H1. cbn [fst snd] in H1. rewrite <- H1.
  apply rdword_ext. intros i Hi. apply (proj1 HKM); [lia | | lia].
  intros HG. pose proof (proj2 (inG_G_HARNESS_hull _ HG)) as Hh. unfold TG.G_HARNESS_B_HI in Hh. lia. }
assert (HSM : rdword (aview segs (w_H W') memX) (lc_sp1 cx + 168) = Some TB_M).
{ apply HSK; [|lia|lia]. unfold lf_spill_loop, lf_spill_init, lf_spill_scal, lf_spill_sm; cbn [In app].
  repeat (first [left; reflexivity | right]). }
assert (HSG : rdword (aview segs (w_H W') memX) (lc_sp1 cx + 184) = Some (transportb_hi 10)).
{ apply HSK; [|lia|lia]. unfold lf_spill_loop, lf_spill_init, lf_spill_scal, lf_spill_sm; cbn [In app].
  repeat (first [left; reflexivity | right]). }
clear HSK.
pose proof (lc6_c1_entry (fx := l_fx cx) W' regsX memX _ (lc_sp1 cx) R9 R25 ltac:(lia) ltac:(lia) Hsp1al HSM HSG HTW)
  as HS.
set (E0 := Eimg (PI := PI_transportb) (Ereg regsX (lc6_c1_ex (lc6_Bm (lo_B op))))) in HS.
assert (HEI : img_env VAL A_LIM E0) by (unfold E0; apply Eimg_env).
assert (SHOK : sh_ok segs LC6_Bx (@nil shent) E0 (mrestrict (w_H W') memX)) by constructor.
assert (U25 : bv_unsigned (ew E0 25%nat) = TB_OW)
  by (unfold E0; exact (lc6_U regsX _ 25 (Z_to_bv 5 25) TB_OW eq_refl R25 ltac:(unfold TB_OW; lia))).
assert (U249 : bv_unsigned (ew E0 249%nat) = TB_M).
{ unfold E0. rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia). change 249%nat with (A_OBJ 8).
  rewrite (proj1 lc6_vals). first [reflexivity | apply unsigned_lit_small; unfold TB_M; lia]. }
pose proof (@paj_run_x (l_fx cx) rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS
  TG.G_HARNESS_B HGX 0 []) as RUN.
pose proof (@paj_run_to_x (l_fx cx) rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS
  TG.G_HARNESS_B HGX 0 []) as RUNTO.
pose proof (paj_branch (fx := l_fx cx) (PI := PI_transportb)) as BR.
paj_run_tok RUN HS HJ SHOK (0, 0).
{ lc6_c1_awr U249 U25. }
set (md1 := with_vm_backing (m_vm_lazy mdX) mat mdX) in *. clearbody md1. clear mat. rename ms into ms1.
assert (KR1 : forall a, 0 <= a < 2 ^ 64 -> ~ ((TB_OW + 232 <= a < TB_OW + 236) \/ (TB_M + 88 <= a < TB_M + 92)) ->
  aview segs (w_H W') (ms_mem ms1) a = aview segs (w_H W') memX a).
{ intros a Ha Hn.
  apply (kept_of_frame _ _ _ _ _ (fun x => (TB_OW + 232 <= x < TB_OW + 236) \/ (TB_M + 88 <= x < TB_M + 92)) HFr);
    [| exact Ha | exact Hn].
  intros b wlo whi x Hin Hx. lc6_win Hin Hx ltac:(rewrite ?U25, ?U249 in Hx; lia). }
assert (GR1 : forall a, apresent (w_H W') memX a -> apresent (w_H W') (ms_mem ms1) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
clear HF HFr HG.
(* the values the stretch loads, and the model's view of them *)
set (Bm := lc6_Bm (lo_B op)) in *.
pose proof (TWL.u_at_range Bm TW.A_M_desk_known 4) as Rd. pose proof (TWL.u_at_range Bm TW.A_M_foreign 4) as Rf.
pose proof (TWL.u_at_range Bm TW.A_M_state 4) as Rs.
change (2 ^ (8 * Z.of_nat 4)) with 4294967296 in Rd, Rf, Rs.
assert (E32 : ew E0 32 = Z_to_bv 64 (TW.u_at Bm TW.OFF_g_fail_next 1))
  by (unfold E0; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsX _ 0)).
assert (E33 : ew E0 33 = Z_to_bv 64 (TW.u_at Bm TW.A_M_desk_known 4))
  by (unfold E0; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsX _ 1)).
assert (E34 : ew E0 34 = Z_to_bv 64 (TW.u_at Bm TW.A_M_foreign 4))
  by (unfold E0; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsX _ 2)).
assert (E35 : ew E0 35 = Z_to_bv 64 (TW.u_at Bm TW.A_M_state 4))
  by (unfold E0; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsX _ 3)).
pose proof (lc6_sext_den E0 33 _ E33 Rd) as D33. pose proof (lc6_sext_den E0 34 _ E34 Rf) as D34.
pose proof (lc6_sext_den E0 35 _ E35 Rs) as D35.
pose proof (TWL.s32_range Bm TW.A_M_desk_known) as S33. pose proof (TWL.s32_range Bm TW.A_M_foreign) as S34.
pose proof (TWL.s32_range Bm TW.A_M_state) as S35. unfold TW.s32_at in S33, S34, S35.
pose proof (lc6_fields_B1 _ HLB) as (EFd & EFf & EFs). fold Bm in EFd, EFf, EFs.
pose proof (lc6_close_w_eq _ HLB) as EC.
assert (DG : sv_denot E0 (SOff 32 0) = Z_to_bv 64 (TW.g_fail_next (lc6_B3 (lo_B op)))).
{ cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned, (lc6_gfn _ HLB). reflexivity. }
assert (DM1 : sv_denot E0 (SLit 18446744073709551615) = Z_to_bv 64 (-1)) by (apply bv_eq; reflexivity).
(* what a run from the first branch keeps, and op_begin's world *)
assert (POST : forall m2,
  (forall a, 0 <= a < 2 ^ 64 -> ~ ((TB_OW + 232 <= a < TB_OW + 236) \/ (TB_M + 88 <= a < TB_M + 92)) ->
     aview segs (w_H W') m2 a = aview segs (w_H W') memX a) ->
  (forall a, apresent (w_H W') memX a -> apresent (w_H W') m2 a) ->
  (forall j, (j < 4)%nat -> aview segs (w_H W') m2 (TB_OW + 232 + Z.of_nat j) = Some (YO0f.le_byte (-1) 4 j)) ->
  (forall j, (j < 4)%nat -> aview segs (w_H W') m2 (TB_M + 88 + Z.of_nat j) =
     Some (YO0f.le_byte (TW.g_fail_next (lc6_B3 (lo_B op))) 4 j)) ->
  lc6_km cx W' memX m2 /\ lc_tw W' m2 (lc6_B1 (lo_B op))).
{ intros m2 KR2 GR2 VD VF. split.
  - split; [|exact GR2].
    intros a Ha HnG _. apply KR2; [exact Ha|]. intros [H1 | H1]; apply HnG; [apply lc6_inG_OW | apply lc6_inG_M]; lia.
  - apply (lc6_w_c1 _ (aview segs (w_H W') memX) _ HTW VD VF).
    intros x Hx N1 N2. pose proof (TMAP_B_hull x Hx) as Hh. unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in Hh.
    apply KR2; [lia | intros [H1 | H1]; [exact (N1 H1) | exact (N2 H1)]]. }
psrr_branch_tok RUN BR HS SHOK (0, 0).
- (* M.desk_known = 0 (the test of m_close is false): +0x8dc *)
  rewrite D33 in Hc. change (sv_denot E0 (SLit 0)) with (Z_to_bv 64 0) in Hc. cbn [branch_taken] in Hc.
  rewrite (lc6_eqb _ 0 S33 ltac:(lia)) in Hc. apply Z.eqb_eq in Hc.
  assert (Ecnd : (TC.truth (TW.M_desk_known (lc6_B1 (lo_B op))) && negb (TC.truth (TW.M_foreign (lc6_B1 (lo_B op)))) &&
    negb (TW.M_state (lc6_B1 (lo_B op)) =? TC.S_CLOSED)) = false)
    by (unfold TC.truth; rewrite EFd, Hc; reflexivity).
  rewrite Ecnd in EC. cbv beta iota in EC.
  paj_run_to_tok RUNTO HS HJ SHOK (0, 0) LC6_D1.
  { lc6_c1_awr U249 U25. }
  set (md2 := with_vm_backing (m_vm_lazy md1) mat md1) in *. clearbody md2. clear mat.
  lc6_c1_exit HS HFr HG KR1 GR1 ms HJ HCF HKMr HTWF HRKr Q12 Q25 U249 U25 POST DG DM1 HC regsX E0 memX
    (lc6_c1_ex Bm).
  clear HF HFr HG.
  pmkst HS.
  exact (lc6_D1 (lc6_B1 (lo_B op)) (ms_regs ms) (ms_mem ms) md2
    (conj HCF (conj (lc6_rk_trans _ _ _ HRK HRKr) (lc6_km_trans _ _ _ _ _ HKM HKMr))) Q12 HTWF EC).
- (* desk known: M.foreign *)
  rewrite D33 in Hc. change (sv_denot E0 (SLit 0)) with (Z_to_bv 64 0) in Hc. cbn [branch_taken] in Hc.
  rewrite (lc6_eqb _ 0 S33 ltac:(lia)) in Hc. apply Z.eqb_neq in Hc. rename Hc into Hdk.
  paj_run_tok RUN HS HJ SHOK (0, 0).
  { lc6_c1_awr U249 U25. }
  set (md2 := with_vm_backing (m_vm_lazy md1) mat md1) in *. clearbody md2. clear mat. rename ms into ms2.
  assert (KR2 : forall a, 0 <= a < 2 ^ 64 -> ~ ((TB_OW + 232 <= a < TB_OW + 236) \/ (TB_M + 88 <= a < TB_M + 92)) ->
    aview segs (w_H W') (ms_mem ms2) a = aview segs (w_H W') memX a).
  { intros a Ha Hn. rewrite <- (KR1 a Ha Hn).
    apply (kept_of_frame _ _ _ _ _ (fun x => (TB_OW + 232 <= x < TB_OW + 236) \/ (TB_M + 88 <= x < TB_M + 92)) HFr);
      [| exact Ha | exact Hn].
    intros b wlo whi x Hin Hx. lc6_win Hin Hx ltac:(rewrite ?U25, ?U249 in Hx; lia). }
  assert (GR2 : forall a, apresent (w_H W') memX a -> apresent (w_H W') (ms_mem ms2) a)
    by (intros a Ha; exact (apresent_grows _ _ _ a HG (GR1 a Ha))).
  clear HF HFr HG.
  psrr_branch_tok RUN BR HS SHOK (0, 0).
  + (* M.foreign <> 0 (the test is false): +0x8dc *)
    rewrite D34 in Hc. change (sv_denot E0 (SLit 0)) with (Z_to_bv 64 0) in Hc. cbn [branch_taken] in Hc.
    rewrite (lc6_eqb _ 0 S34 ltac:(lia)) in Hc. apply negb_true_iff, Z.eqb_neq in Hc.
    assert (Ecnd : (TC.truth (TW.M_desk_known (lc6_B1 (lo_B op))) &&
      negb (TC.truth (TW.M_foreign (lc6_B1 (lo_B op)))) && negb (TW.M_state (lc6_B1 (lo_B op)) =? TC.S_CLOSED)) = false)
      by (unfold TC.truth; rewrite EFf, (proj2 (Z.eqb_neq _ _) Hc); cbn [negb]; rewrite andb_false_r; reflexivity).
    rewrite Ecnd in EC. cbv beta iota in EC.
    paj_run_to_tok RUNTO HS HJ SHOK (0, 0) LC6_D1.
    { lc6_c1_awr U249 U25. }
    set (md3 := with_vm_backing (m_vm_lazy md2) mat md2) in *. clearbody md3. clear mat.
    lc6_c1_exit HS HFr HG KR2 GR2 ms HJ HCF HKMr HTWF HRKr Q12 Q25 U249 U25 POST DG DM1 HC regsX E0 memX
      (lc6_c1_ex Bm).
    clear HF HFr HG.
    pmkst HS.
    exact (lc6_D1 (lc6_B1 (lo_B op)) (ms_regs ms) (ms_mem ms) md3
      (conj HCF (conj (lc6_rk_trans _ _ _ HRK HRKr) (lc6_km_trans _ _ _ _ _ HKM HKMr))) Q12 HTWF EC).
  + (* not foreign: M.state *)
    rewrite D34 in Hc. change (sv_denot E0 (SLit 0)) with (Z_to_bv 64 0) in Hc. cbn [branch_taken] in Hc.
    rewrite (lc6_eqb _ 0 S34 ltac:(lia)) in Hc. apply negb_false_iff, Z.eqb_eq in Hc. rename Hc into Hfr.
    paj_run_tok RUN HS HJ SHOK (0, 0).
    { lc6_c1_awr U249 U25. }
    set (md3 := with_vm_backing (m_vm_lazy md2) mat md2) in *. clearbody md3. clear mat. rename ms into ms3.
    assert (KR3 : forall a, 0 <= a < 2 ^ 64 -> ~ ((TB_OW + 232 <= a < TB_OW + 236) \/ (TB_M + 88 <= a < TB_M + 92)) ->
      aview segs (w_H W') (ms_mem ms3) a = aview segs (w_H W') memX a).
    { intros a Ha Hn. rewrite <- (KR2 a Ha Hn).
      apply (kept_of_frame _ _ _ _ _ (fun x => (TB_OW + 232 <= x < TB_OW + 236) \/ (TB_M + 88 <= x < TB_M + 92)) HFr);
        [| exact Ha | exact Hn].
      intros b wlo whi x Hin Hx. lc6_win Hin Hx ltac:(rewrite ?U25, ?U249 in Hx; lia). }
    assert (GR3 : forall a, apresent (w_H W') memX a -> apresent (w_H W') (ms_mem ms3) a)
      by (intros a Ha; exact (apresent_grows _ _ _ a HG (GR2 a Ha))).
    clear HF HFr HG.
    psrr_branch_tok RUN BR HS SHOK (0, 0).
    * (* M.state = S_CLOSED (the test is false): +0x8dc *)
      rewrite D35 in Hc. change (sv_denot E0 (SLit 3)) with (Z_to_bv 64 3) in Hc. cbn [branch_taken] in Hc.
      rewrite (lc6_eqb _ 3 S35 ltac:(lia)) in Hc. apply Z.eqb_eq in Hc.
      assert (Ecnd : (TC.truth (TW.M_desk_known (lc6_B1 (lo_B op))) &&
        negb (TC.truth (TW.M_foreign (lc6_B1 (lo_B op)))) && negb (TW.M_state (lc6_B1 (lo_B op)) =? TC.S_CLOSED)) =
        false)
        by (rewrite EFs, Hc; change (negb (3 =? TC.S_CLOSED)) with false; apply andb_false_r).
      rewrite Ecnd in EC. cbv beta iota in EC.
      paj_run_to_tok RUNTO HS HJ SHOK (0, 0) LC6_D1.
      { lc6_c1_awr U249 U25. }
      set (md4 := with_vm_backing (m_vm_lazy md3) mat md3) in *. clearbody md4. clear mat.
      lc6_c1_exit HS HFr HG KR3 GR3 ms HJ HCF HKMr HTWF HRKr Q12 Q25 U249 U25 POST DG DM1 HC regsX E0 memX
        (lc6_c1_ex Bm).
      clear HF HFr HG.
      pmkst HS.
      exact (lc6_D1 (lc6_B1 (lo_B op)) (ms_regs ms) (ms_mem ms) md4
        (conj HCF (conj (lc6_rk_trans _ _ _ HRK HRKr) (lc6_km_trans _ _ _ _ _ HKM HKMr))) Q12 HTWF EC).
    * (* M.state <> S_CLOSED (the test holds): +0x8c4 *)
      rewrite D35 in Hc. change (sv_denot E0 (SLit 3)) with (Z_to_bv 64 3) in Hc. cbn [branch_taken] in Hc.
      rewrite (lc6_eqb _ 3 S35 ltac:(lia)) in Hc. apply Z.eqb_neq in Hc.
      paj_run_to_tok RUNTO HS HJ SHOK (0, 0) LC6_C2E.
      { lc6_c1_awr U249 U25. }
      set (md4 := with_vm_backing (m_vm_lazy md3) mat md3) in *. clearbody md4. clear mat.
      lc6_c1_exit HS HFr HG KR3 GR3 ms HJ HCF HKMr HTWF HRKr Q12 Q25 U249 U25 POST DG DM1 HC regsX E0 memX
        (lc6_c1_ex Bm).
      clear HF HFr HG.
      pmkst HS.
      apply (lc6_C2e (ms_regs ms) (ms_mem ms) md4
        (conj HCF (conj (lc6_rk_trans _ _ _ HRK HRKr) (lc6_km_trans _ _ _ _ _ HKM HKMr)))
        Q12 (eq_trans Q25 R25) HTWF).
      unfold TC.truth. change TC.S_CLOSED with 3.
      rewrite EFd, EFf, EFs, (proj2 (Z.eqb_neq _ _) Hdk), Hfr, (proj2 (Z.eqb_neq _ _) Hc).
      reflexivity.
Qed.

(* +0x87c .. +0x88c: a0 = GOT, a2 = 224, a1 = 0, `jal __asan_memset`; then the memset (gx_intrin_at). *)
Lemma lc6_B : forall regsX memX mdX, lc6_st regsX memX mdX ->
  YK11.getr regsX (Z_to_bv 5 25) = w64 TB_OW -> lc_tw W' memX (lc6_Bo (lo_B op)) ->
  SRr segs W' (cfgX regsX LC6_B memX mdX) Q.
Proof.
intros regsX memX mdX (HC & HRK & HKM) R25 HTW.
pose proof (lp_laws _ _ _ _ _ HP) as LAWS.
pose proof (G_HARNESS_gx_ok B (lp_g_unowned _ _ _ _ _ HP)) as HGX.
pose proof lc6_sp as (Hsp1c & Hsp1 & Hsp0 & Ho16).
pose proof asan_consts as ((CVlo & CVhi) & _).
pose proof HC as (HJ & _ & _ & _ & Rsp & _ & _ & Rgp & Rtp & _).
set (E0 := Eimg (PI := PI_transportb) (Ereg regsX [])).
assert (HEI : img_env VAL A_LIM E0) by (unfold E0; apply Eimg_env).
pose proof (lc6_entry0 (fx := l_fx cx) W' regsX memX LC6_B) as HS. fold E0 in HS.
assert (SHOK : sh_ok segs (SOff 26 0) (@nil shent) E0 (mrestrict (w_H W') memX)) by constructor.
pose proof (@paj_run_x (l_fx cx) rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS
  TG.G_HARNESS_B HGX 0 []) as RUN.
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E0 n = YK11.getr regsX r)
  by (intros n r Hn; unfold E0; apply can_ew_Eimg_Ereg_nat; exact Hn).
destruct lc6_vals as (V8 & V12 & V13 & VH).
assert (UGOT : bv_unsigned (ew E0 254%nat) = TB_GOT).
{ unfold E0. rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia). change 254%nat with (A_OBJ 13). rewrite V13.
  first [reflexivity | apply unsigned_lit_small; unfold TB_GOT; lia]. }
paj_run_tok RUN HS HJ SHOK (0, 0).
{ lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
  apply awr_ok_x_nil. }
set (md1 := with_vm_backing (m_vm_lazy mdX) mat mdX) in *. clearbody md1. clear mat.
assert (KR1 : forall a, 0 <= a < 2 ^ 64 -> aview segs (w_H W') (ms_mem ms) a = aview segs (w_H W') memX a).
{ intros a Ha. apply (kept_of_frame _ _ _ _ _ (fun _ : Z => False) HFr); [| exact Ha | intros []].
  intros b wlo whi x Hin Hx. lc6_win Hin Hx ltac:(idtac). }
assert (GR1 : forall a, apresent (w_H W') memX a -> apresent (w_H W') (ms_mem ms) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
clear HF HFr HG.
pmkst HS.
lc6_reg HS (Z_to_bv 5 10) (Z_to_bv 64 TB_GOT) Q10 ltac:(cbn [sv_denot]; rewrite UGOT, Z.add_0_r; reflexivity).
lc6_reg HS (Z_to_bv 5 11) (Z_to_bv 64 0) Q11 ltac:(reflexivity).
lc6_reg HS (Z_to_bv 5 12) (Z_to_bv 64 224) Q12 ltac:(reflexivity).
lc6_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + LC6_C1)) R1 ltac:(apply codeptr_val; exact HEI).
assert (HRK1 : lc6_rk regsX (ms_regs ms)).
{ apply (lc6_rk_st _ _ _ ms regsX [] HS); [apply lc6_agree; [intros n Hn; reflexivity | reflexivity] |].
  vm_compute. reflexivity. }
assert (R25b : YK11.getr (ms_regs ms) (Z_to_bv 5 25) = w64 TB_OW).
{ lc6_reg HS (Z_to_bv 5 25) (YK11.getr regsX (Z_to_bv 5 25)) Q25
    ltac:(cbn [sv_denot]; rewrite (EE 25%nat (Z_to_bv 5 25) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  rewrite Q25. exact R25. }
assert (Rsp1 : YK11.getr (ms_regs ms) (Z_to_bv 5 2) = w64 (lc_sp1 cx))
  by exact (eq_trans (HRK1 (Z_to_bv 5 2) ltac:(lc6_inK)) (eq_trans (HRK (Z_to_bv 5 2) ltac:(lc6_inK)) Rsp)).
assert (R3 : YK11.getr (ms_regs ms) (Z_to_bv 5 3) = w64 (as_gp B))
  by exact (eq_trans (HRK1 (Z_to_bv 5 3) ltac:(lc6_inK)) (eq_trans (HRK (Z_to_bv 5 3) ltac:(lc6_inK)) Rgp)).
assert (R4 : YK11.getr (ms_regs ms) (Z_to_bv 5 4) = w64 (as_tp B))
  by exact (eq_trans (HRK1 (Z_to_bv 5 4) ltac:(lc6_inK)) (eq_trans (HRK (Z_to_bv 5 4) ltac:(lc6_inK)) Rtp)).
assert (HKM1 : lc6_km cx W' memX (ms_mem ms)) by (split; [intros a Ha _ _; exact (KR1 a Ha) | exact GR1]).
lc6_core HC HJ HKM1 HC1.
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR1.
destruct (lc6_sh_GOT B (lp_recv_cells _ _ _ _ _ HP) ly' S' W' (ms_mem ms) md1 HAR1) as [HRA HHULL].
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Qx =>
  change (SRr sg Wx (mkCfg (@YK11.mkst (l_fx cx) rg (Z_to_bv 64 (transportb_sigma TB___asan_memset)) mm rom) mdx) Qx)
end.
eapply SRr_bind.
{ apply (@gx_intrin_at (l_fx cx) rc tfib_sink_head segs B LAWS transportb_segs_low OSet
    (transportb_sigma TB___asan_memset) (lp_memset _ _ _ _ _ HP (l_fx cx)) TG.G_HARNESS_B W' (ms_regs ms) (ms_mem ms)
    _ _ _ _ _ _ _ _ _ ly' S' md1 e TB_GOT 0 224 (lc_sp1 cx - lc_sp0 cx) (Z_to_bv 64 (BASE + LC6_C1)) HGX
    G_HARNESS_B_rw HJ Q10 Q11 Q12).
  - lia.
  - unfold TB_GOT. lia.
  - unfold TB_GOT. lia.
  - unfold spZ. transitivity (bv_unsigned (w64 (lc_sp1 cx))); [f_equal; exact Rsp1|].
    unfold w64. rewrite unsigned_lit_small by lia. lia.
  - exact Ho16.
  - lia.
  - unfold ESTACK, LLVMF_STK. lia.
  - exact R3.
  - exact R4.
  - exact R1.
  - apply (ret_ok_codeptr_v (PI := PI_transportb)); [unfold LC6_C1; lia | reflexivity].
  - eapply (transport_twr_ok_g_intro segs B LAWS); [exact HJ|]. intros a Ha. right.
    apply (lc6_inG_row _ _ _ a TMAP_B_GOT). unfold TW.SZ_GOT. lia.
  - left. unfold kLowMemEnd, TB_GOT. lia.
  - exact HRA.
  - intros _. exact HHULL.
  - exact I. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & _ & Hset2 & Heff2 & Hgr2).
assert (HKM2 : lc6_km cx W' (ms_mem ms) mem2).
{ split; [|exact Hgr2]. intros a Ha HnG Hw. apply Heff2; [exact Ha | | unfold ESTACK; lia].
  intros Hd. apply HnG. apply (lc6_inG_row _ _ _ a TMAP_B_GOT). unfold TW.SZ_GOT. lia. }
lc6_core HC1 HJ2 HKM2 HC2.
apply (lc6_C1 regs2 mem2 md2).
- split; [exact HC2|]. split.
  + exact (lc6_rk_trans _ _ _ HRK (lc6_rk_trans _ _ _ HRK1 (lc6_rk_pres _ _ HP2))).
  + exact (lc6_km_trans _ _ _ _ _ HKM (lc6_km_trans _ _ _ _ _ HKM1 HKM2)).
- rewrite (HP2 25 ltac:(unfold acallee_saved; lia)). exact R25b.
- unfold lc_tw.
  apply (lc6_w_set (aview segs (w_H W') memX) _ (lc6_Bo (lo_B op)) TW.OFF_GOT TB_GOT TW.SZ_GOT HTW TMAP_B_GOT).
  + unfold TW.SZ_GOT. lia.
  + intros i Hi. exact (Hset2 i Hi).
  + intros x Hx Hn. pose proof (TMAP_B_hull x Hx) as Hh. unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in Hh.
    rewrite (Heff2 x ltac:(lia) Hn ltac:(unfold ESTACK; lia)). exact (KR1 x ltac:(lia)).
Qed.

(* +0x864 .. +0x878: s9 = OW, a2 = 304, a0 = s9, a1 = 0, `jal __asan_memset`; then the memset (gx_intrin_at). *)
Lemma lc6_A : SRr segs W' (cfgX regs' LC6_A mem' md') Q.
Proof.
pose proof HL as (HC & _).
pose proof (lp_laws _ _ _ _ _ HP) as LAWS.
pose proof (G_HARNESS_gx_ok B (lp_g_unowned _ _ _ _ _ HP)) as HGX.
pose proof lc6_sp as (Hsp1c & Hsp1 & Hsp0 & Ho16).
pose proof asan_consts as ((CVlo & CVhi) & _).
pose proof HC as (HJ & _ & _ & _ & Rsp & _ & _ & Rgp & Rtp & _).
set (E0 := Eimg (PI := PI_transportb) (Ereg regs' [])).
assert (HEI : img_env VAL A_LIM E0) by (unfold E0; apply Eimg_env).
pose proof (lc6_entry0 (fx := l_fx cx) W' regs' mem' LC6_A) as HS. fold E0 in HS.
assert (SHOK : sh_ok segs (SOff 26 0) (@nil shent) E0 (mrestrict (w_H W') mem')) by constructor.
pose proof (@paj_run_x (l_fx cx) rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS
  TG.G_HARNESS_B HGX 0 []) as RUN.
destruct lc6_vals as (V8 & V12 & V13 & VH).
assert (UOW : bv_unsigned (ew E0 253%nat) = TB_OW).
{ unfold E0. rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia). change 253%nat with (A_OBJ 12). rewrite V12.
  first [reflexivity | apply unsigned_lit_small; unfold TB_OW; lia]. }
paj_run_tok RUN HS HJ SHOK (0, 0).
{ lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
  apply awr_ok_x_nil. }
set (md1 := with_vm_backing (m_vm_lazy md') mat md') in *. clearbody md1. clear mat.
assert (KR1 : forall a, 0 <= a < 2 ^ 64 -> aview segs (w_H W') (ms_mem ms) a = aview segs (w_H W') mem' a).
{ intros a Ha. apply (kept_of_frame _ _ _ _ _ (fun _ : Z => False) HFr); [| exact Ha | intros []].
  intros b wlo whi x Hin Hx. lc6_win Hin Hx ltac:(idtac). }
assert (GR1 : forall a, apresent (w_H W') mem' a -> apresent (w_H W') (ms_mem ms) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
clear HF HFr HG.
pmkst HS.
lc6_reg HS (Z_to_bv 5 10) (Z_to_bv 64 TB_OW) Q10 ltac:(cbn [sv_denot]; rewrite UOW, Z.add_0_r; reflexivity).
lc6_reg HS (Z_to_bv 5 11) (Z_to_bv 64 0) Q11 ltac:(reflexivity).
lc6_reg HS (Z_to_bv 5 12) (Z_to_bv 64 304) Q12 ltac:(reflexivity).
lc6_reg HS (Z_to_bv 5 25) (Z_to_bv 64 TB_OW) Q25 ltac:(cbn [sv_denot]; rewrite UOW, Z.add_0_r; reflexivity).
lc6_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + LC6_B)) R1 ltac:(apply codeptr_val; exact HEI).
assert (HRK1 : lc6_rk regs' (ms_regs ms)).
{ apply (lc6_rk_st _ _ _ ms regs' [] HS); [apply lc6_agree; [intros n Hn; reflexivity | reflexivity] |].
  vm_compute. reflexivity. }
assert (Rsp1 : YK11.getr (ms_regs ms) (Z_to_bv 5 2) = w64 (lc_sp1 cx))
  by exact (eq_trans (HRK1 (Z_to_bv 5 2) ltac:(lc6_inK)) Rsp).
assert (R3 : YK11.getr (ms_regs ms) (Z_to_bv 5 3) = w64 (as_gp B))
  by exact (eq_trans (HRK1 (Z_to_bv 5 3) ltac:(lc6_inK)) Rgp).
assert (R4 : YK11.getr (ms_regs ms) (Z_to_bv 5 4) = w64 (as_tp B))
  by exact (eq_trans (HRK1 (Z_to_bv 5 4) ltac:(lc6_inK)) Rtp).
assert (HKM1 : lc6_km cx W' mem' (ms_mem ms)) by (split; [intros a Ha _ _; exact (KR1 a Ha) | exact GR1]).
lc6_core HC HJ HKM1 HC1.
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR1.
destruct (lc6_sh_OW B (lp_recv_cells _ _ _ _ _ HP) ly' S' W' (ms_mem ms) md1 HAR1) as [HRA HHULL].
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Qx =>
  change (SRr sg Wx (mkCfg (@YK11.mkst (l_fx cx) rg (Z_to_bv 64 (transportb_sigma TB___asan_memset)) mm rom) mdx) Qx)
end.
eapply SRr_bind.
{ apply (@gx_intrin_at (l_fx cx) rc tfib_sink_head segs B LAWS transportb_segs_low OSet
    (transportb_sigma TB___asan_memset) (lp_memset _ _ _ _ _ HP (l_fx cx)) TG.G_HARNESS_B W' (ms_regs ms) (ms_mem ms)
    _ _ _ _ _ _ _ _ _ ly' S' md1 e TB_OW 0 304 (lc_sp1 cx - lc_sp0 cx) (Z_to_bv 64 (BASE + LC6_B)) HGX
    G_HARNESS_B_rw HJ Q10 Q11 Q12).
  - lia.
  - unfold TB_OW. lia.
  - unfold TB_OW. lia.
  - unfold spZ. transitivity (bv_unsigned (w64 (lc_sp1 cx))); [f_equal; exact Rsp1|].
    unfold w64. rewrite unsigned_lit_small by lia. lia.
  - exact Ho16.
  - lia.
  - unfold ESTACK, LLVMF_STK. lia.
  - exact R3.
  - exact R4.
  - exact R1.
  - apply (ret_ok_codeptr_v (PI := PI_transportb)); [unfold LC6_B; lia | reflexivity].
  - eapply (transport_twr_ok_g_intro segs B LAWS); [exact HJ|]. intros a Ha. right.
    apply (lc6_inG_row _ _ _ a TMAP_B_OW). unfold TW.SZ_OW. lia.
  - left. unfold kLowMemEnd, TB_OW. lia.
  - exact HRA.
  - intros _. exact HHULL.
  - exact I. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & _ & Hset2 & Heff2 & Hgr2).
assert (HKM2 : lc6_km cx W' (ms_mem ms) mem2).
{ split; [|exact Hgr2]. intros a Ha HnG Hw. apply Heff2; [exact Ha | | unfold ESTACK; lia].
  intros Hd. apply HnG. apply (lc6_inG_row _ _ _ a TMAP_B_OW). unfold TW.SZ_OW. lia. }
lc6_core HC1 HJ2 HKM2 HC2.
apply (lc6_B regs2 mem2 md2).
- split; [exact HC2|]. split.
  + exact (lc6_rk_trans _ _ _ HRK1 (lc6_rk_pres _ _ HP2)).
  + exact (lc6_km_trans _ _ _ _ _ HKM1 HKM2).
- rewrite (HP2 25 ltac:(unfold acallee_saved; lia)). exact Q25.
- unfold lc_tw. apply (lc6_w_set (aview segs (w_H W') mem') _ (lo_B op) TW.OFF_OW TB_OW TW.SZ_OW Htw0 TMAP_B_OW).
  + unfold TW.SZ_OW. lia.
  + intros i Hi. exact (Hset2 i Hi).
  + intros x Hx Hn. pose proof (TMAP_B_hull x Hx) as Hh. unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in Hh.
    rewrite (Heff2 x ltac:(lia) Hn ltac:(unfold ESTACK; lia)). exact (KR1 x ltac:(lia)).
Qed.

End op6.

Lemma lc_op6a_ok : lc_op6a_stmt B MT XL RLO RHI.
Proof.
unfold lc_op6a_stmt. intros HP cx op W' c' HB HA.
destruct HA as (ly' & S' & regs' & mem' & md' & e & Hc & Ho6 & HL & Htw & _ & Hcur & Hs46).
subst c'.
assert (Ho : lc_opc (l_pl cx) (lo_c op) = 6) by (symmetry; exact Ho6).
unfold lc_cfg. rewrite lc6_arm6, <- lc6_base. unfold w64.
exact (lc6_A cx op ly' S' W' regs' mem' md' e HP HB HL Ho Hcur Hs46 Htw).
Qed.

End seg.
