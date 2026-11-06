(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8v.v:120-122
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:518-584, 622-634 [Apache-2.0 OR MIT];
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:110-141, 221-225, 227-235, 264-270 [Apache-2.0 OR MIT], for
   libreac/fuzz_identity's ASan build (lib/A). The [Apache-2.0 OR MIT] text is used under Apache-2.0. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/LLVMFuzzerTestOneInput_L.v, with its module paths and module names changed; 987 of its 1030 lines of code are new or changed and 1037 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/m_rx_seg_head.v, with its numbers changed; 1292 of its 1406 lines of code are new or changed and 916 lines of the source are left out. *)
(* m_rx_seg_desk: the segment DESK of the image-A walk of m_rx (statement lib/A/Prog/m_rx_cg.v, kit
   lib/A/Prog/m_rx_seg_kit.v): from the cut DESK (0x84b08) to the cuts BODY (0x84b70) and EPI (0x8496c). *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
DgnTransportSyms DgnTransportList DgnTransportAddr DgnTransportPa DgnTransportImg DgnTransportPaLib YC4b YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AE2k AsanCells TransportG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import DgnTransportCg TransportGCg TransportGRwA TransportGRunA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG TWorldA TImgA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
  m_lost_cg m_wake_cg m_maybe_online_cg m_tick_cg desk_named_cg check_state_data_cg m_rx_cg m_rx_seg_kit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TImg TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require m_rx_epi.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Mem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.TransportG.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
Module EPI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T.m_rx_epi.
Module ACells := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.AsanCells.
Module LMem := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib.Mem.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* The symbolic states                                                 *)
(* ------------------------------------------------------------------ *)

(* The state at the cut (offset 14500 = 0x84b08): atoms 0 .. 31 the registers, 32 the shadow base, 33 M.desk_known.
   Regions: the spill slot sp + 8 (the store of byte 18 at 0x84b08, writable) and M.desk_known (object 8, read
   only, its chunk the world's 4 bytes). *)
Definition desk_sp_region : YP09.region := YP09.mkRegion (Some 2%nat) 8 16 8 16 [].
Definition desk_m_region : YP09.region :=
  YP09.mkRegion (Some (A_OBJ 8)) 0 4 0 0 [YP09.mkChunk 0 (YP09.CVal 4 (SOff 33 0))].
Definition desk_facts0 : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
           (33%nat, mkAF 0 (2 ^ 32 - 1) 0); (A_OBJ 8, mkAF TA_M TA_M 5)] [] [].
Definition desk_ss0 : sstate := mkSS 14500 sr_atoms [desk_sp_region; desk_m_region] None desk_facts0.

(* A fresh state at offset pc with no region (the runs between the calls touch no memory). *)
Definition desk_factsf : facts := mkFacts [(32%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] [].
Definition desk_ssf (pc : Z) : sstate := mkSS pc sr_atoms [] None desk_factsf.

(* The state at the memcpy's return (offset 14596 = 0x84b68): M.desk_known writable, based on s3 (atom 19). *)
Definition desk_w_region : YP09.region := YP09.mkRegion (Some 19%nat) 0 4 0 4 [].
Definition desk_factsw : facts :=
  mkFacts [(19%nat, mkAF TA_M TA_M 5); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] [].
Definition desk_ssw : sstate := mkSS 14596 sr_atoms [desk_w_region] None desk_factsw.

Definition DESK_SH : list shent := [].
(* The callee-saved registers the first run keeps (all but s3). *)
Definition DESK_KEEP : list (bv 5) := map (Z_to_bv 5) [2; 3; 4; 8; 9; 18; 20; 21; 22; 23; 24; 25; 26; 27].
Definition DESK_Bx : sv := SOff 32 0.

Definition desk_E {rc : YM05.RunCeil} (regs : bvmap 5 word) (Bw : list byte) : env :=
  Eimg (PI := PI_transport) (Ereg regs [w64 SHADOW_OFF; Z_to_bv 64 (TW.u_at Bw TW.A_M_desk_known 4)]).
Definition desk_Ef {rc : YM05.RunCeil} (regs : bvmap 5 word) : env :=
  Eimg (PI := PI_transport) (Ereg regs [w64 SHADOW_OFF]).

(* The value of register r in the machine state of a symbolic state HS. *)
Ltac desk_reg HS r v H tac :=
  lazymatch type of HS with
  | st_ok_pi ?segsx ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok ?segsx ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_restrict_reg segsx Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | ?T => idtac "desk_reg: no match for" T; fail
  end.

(* The windows a run wrote, each closed by tac. *)
Ltac desk_win Hin Hx tac :=
  lazymatch type of Hin with In ?x ?l => let l' := eval vm_compute in l in change (In x l') in Hin end;
  cbn [In] in Hin;
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hx; tac |]);
  destruct Hin.

Lemma desk_inG : forall a, TA_M <= a < TA_M + 1648 -> inG TG.G_HARNESS a.
Proof.
intros a Ha. unfold inG. apply Exists_exists.
exists (TA_M, TW.SZ_M). split; [exact (TMAP_A_in_G _ _ _ TMAP_A_M) | unfold in_zr, TW.SZ_M; cbn [fst snd]; lia].
Qed.

(* The write rights of a run from a state with no region. *)
Ltac desk_awr0 :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end;
  apply awr_ok_x_nil.

(* The write rights of a run from the cut's state: only the spill slot, inside the walk's stack window. *)
Ltac desk_awr_sp UspE :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end;
  repeat (apply awr_ok_x_cons;
    [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
      first [ lia
            | rewrite UspE in Ha; left; split; [unfold awr_byte; left; lia | lia] ] |]);
  apply awr_ok_x_nil.

(* The write rights of the last run: M.desk_known, a byte of G. *)
Ltac desk_awr_m UME :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end;
  repeat (apply awr_ok_x_cons;
    [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
      rewrite UME in Ha; right; left; apply desk_inG; lia |]);
  apply awr_ok_x_nil.

(* The closed bounds of a shadow hull hypothesis lo <= s < hi, computed. *)
Ltac desk_hull Hs :=
  lazymatch type of Hs with ?lo <= ?s < ?hi =>
    let lo' := eval vm_compute in lo in let hi' := eval vm_compute in hi in change (lo' <= s < hi') in Hs end.

(* ------------------------------------------------------------------ *)
(* Bytes and lists                                                     *)
(* ------------------------------------------------------------------ *)

Lemma desk_some_inv : forall (x y : list byte) (a b : Z), Some (x, a) = Some (y, b) -> y = x /\ b = a.
Proof. intros x y a b H. injection H as H1 H2. split; symmetry; assumption. Qed.

Lemma desk_mbyte_of_aview : forall (H : word -> bool) (m m' : word -> option byte) a,
  aview tfibsegs H m' a = aview tfibsegs H m a -> mbyte tfibsegs (mrestrict H m') a = mbyte tfibsegs (mrestrict H m) a.
Proof.
  intros H m m' a E. unfold aview in E.
  destruct (mbyte tfibsegs (mrestrict H m') a) as [b1|]; destruct (mbyte tfibsegs (mrestrict H m) a) as [b2|];
    cbn [option_map] in E; try discriminate E; [|reflexivity].
  injection E as E. f_equal. apply bv_eq. exact E.
Qed.

(* The j-th byte of a garr8 array under the view. *)
Lemma desk_garr_view : forall (Wx : world tfibsegs) mem p (bs : list byte) j,
  garr8 tfibsegs (mrestrict (w_H Wx) mem) p (map DSpec.bz bs) -> (j < length bs)%nat ->
  aview tfibsegs (w_H Wx) mem (p + Z.of_nat j) = Some (bv_unsigned (nth j bs (Z_to_bv 8 0))).
Proof.
  intros Wx mem p bs j HG Hj.
  assert (Hj' : (j < length (map DSpec.bz bs))%nat) by (rewrite length_map; exact Hj).
  pose proof (garr8_mbyte tfibsegs _ p _ j HG Hj') as Hm.
  rewrite (nth_indep _ 0 (DSpec.bz (Z_to_bv 8 0))) in Hm by exact Hj'. rewrite map_nth in Hm.
  unfold aview. rewrite Hm. cbn [option_map]. f_equal. rewrite Z_to_bv_unsigned. unfold DSpec.bz.
  apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

(* Two lists of one length have the same values exactly when they agree byte by byte. *)
Lemma desk_zs_eq : forall (l1 l2 : list byte) (k : nat), length l1 = k -> length l2 = k ->
  (TW.zs l1 = TW.zs l2 <->
   forall i, 0 <= i < Z.of_nat k ->
     bv_unsigned (nth (Z.to_nat i) l1 (Z_to_bv 8 0)) = bv_unsigned (nth (Z.to_nat i) l2 (Z_to_bv 8 0))).
Proof.
  intros l1 l2 k L1 L2.
  assert (Z0 : bv_unsigned (Z_to_bv 8 0) = 0) by (vm_compute; reflexivity).
  unfold TW.zs. split.
  - intros E i Hi.
    assert (Hn : nth (Z.to_nat i) (map bv_unsigned l1) 0 = nth (Z.to_nat i) (map bv_unsigned l2) 0)
      by (rewrite E; reflexivity).
    rewrite <- Z0 in Hn at 1. rewrite <- Z0 in Hn. rewrite !map_nth in Hn. exact Hn.
  - intros H. apply (nth_ext _ _ 0 0); [rewrite !length_map; lia|].
    intros j Hj. rewrite length_map in Hj.
    specialize (H (Z.of_nat j) ltac:(lia)). rewrite Nat2Z.id in H.
    rewrite <- Z0 at 1. rewrite <- Z0 at 2. rewrite !map_nth. exact H.
Qed.

Lemma desk_mfb_range : forall (frx : TI.tframe) k, 0 <= mfb frx k < 256.
Proof.
  intros frx k. unfold mfb, DSpec.byte_at, TW.zs.
  destruct (Nat.lt_ge_cases (Z.to_nat k) (length (map (fun b : byte => bv_unsigned b) (TI.tf_bytes frx))))
    as [Hl|Hg].
  - rewrite (nth_indep _ 0 (bv_unsigned (Z_to_bv 8 0))) by exact Hl.
    rewrite map_nth.
    pose proof (bv_unsigned_in_range 8 (nth (Z.to_nat k) (TI.tf_bytes frx) (Z_to_bv 8 0))) as R.
    change (bv_modulus 8) with 256 in R. lia.
  - rewrite nth_overflow by exact Hg. lia.
Qed.

Lemma desk_sub_firstn : forall (l : list byte) k m n, (m <= n)%nat -> firstn m (TW.sub l k n) = TW.sub l k m.
Proof. intros l k m n H. unfold TW.sub. rewrite firstn_firstn. f_equal. lia. Qed.

(* Eight bytes of a value, read back as a word. *)
Lemma desk_rdword_of : forall (rd : Z -> option Z) a v, 0 <= v < 2 ^ 64 ->
  (forall j, (j < 8)%nat -> rd (a + Z.of_nat j) = Some (YO0f.le_byte v 8 j)) -> rdword rd a = Some v.
Proof.
  intros rd a v Hv H. unfold rdword.
  pose proof (H 0%nat ltac:(lia)) as H0. pose proof (H 1%nat ltac:(lia)) as H1.
  pose proof (H 2%nat ltac:(lia)) as H2. pose proof (H 3%nat ltac:(lia)) as H3.
  pose proof (H 4%nat ltac:(lia)) as H4. pose proof (H 5%nat ltac:(lia)) as H5.
  pose proof (H 6%nat ltac:(lia)) as H6. pose proof (H 7%nat ltac:(lia)) as H7.
  cbv [Z.of_nat Pos.of_succ_nat Pos.succ] in H0, H1, H2, H3, H4, H5, H6, H7.
  rewrite Z.add_0_r in H0.
  rewrite H0, H1, H2, H3, H4, H5, H6, H7. f_equal. apply le_bytes8. exact Hv.
Qed.

(* A one-byte constant cell of the record, read at an AR state. *)
Lemma desk_le1 : forall v, 0 <= v < 256 -> YG0f.le_byte v 1 0 = v.
Proof.
  intros v Hv. unfold YG0f.le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
  rewrite Z.shiftr_0_r. change (2 ^ 8) with 256. rewrite (Z.mod_small v 256 Hv). exact (Z.mod_small v 256 Hv).
Qed.
Lemma desk_const1 : forall {rc : YM05.RunCeil} (B : asyms) ly S (W : world tfibsegs) mem md a v s,
  @AR rc tfibsegs B ly S W mem md -> In (z1 (ANum a) v) (as_const B ly) -> 0 <= v < 256 -> a = s ->
  aview tfibsegs (w_H W) mem s = Some v.
Proof.
  intros rc B ly S W mem md a v s HAR Hin Hv <-.
  destruct HAR as (Mx & _).
  pose proof (proj1 (Forall_forall _ _) (am_const _ _ _ _ Mx) _ Hin) as Hc.
  unfold cell_holds in Hc. cbn [c_at c_w YG0f.c_val z1 c1 aeval] in Hc.
  specialize (Hc 0%nat ltac:(lia)). rewrite (desk_le1 v Hv) in Hc.
  replace a with (a + Z.of_nat 0) by lia. exact Hc.
Qed.
Lemma desk_const1_nn : forall {rc : YM05.RunCeil} (B : asyms) ly S (W : world tfibsegs) mem md a v s,
  @AR rc tfibsegs B ly S W mem md -> In (z1 (ANum a) v) (as_const B ly) -> 0 <= v < 256 -> a = s ->
  aview tfibsegs (w_H W) mem s <> None.
Proof.
  intros rc B ly S W mem md a v s H1 H2 H3 H4. rewrite (desk_const1 B ly S W mem md a v s H1 H2 H3 H4). discriminate.
Qed.

(* SPEC_OUI's three bytes in the image (spec.h:67; TCb.v SPEC_OUI), decided over the loaded segments. *)
Lemma desk_oui_rom : forall i, 0 <= i < 3 ->
  option_map (fun b : byte => bv_unsigned b) (YK11.seg_rom tfibsegs (Z_to_bv 64 (TRANS_SPEC_OUI + i)))
  = Some (bv_unsigned (nth (Z.to_nat i) TC.SPEC_OUI (Z_to_bv 8 0))).
Proof.
  intros i Hi. assert (Hc : i = 0 \/ i = 1 \/ i = 2) by lia.
  destruct Hc as [-> | [-> | ->]]; vm_compute; reflexivity.
Qed.
Lemma desk_oui_ro : forall i, 0 <= i < 3 -> trans_in_ro_rd (TRANS_SPEC_OUI + i).
Proof.
  intros i Hi. unfold trans_in_ro_rd, TRANS_RO_RD. apply Exists_exists. exists (TRANS_SPEC_OUI, 3). split.
  - apply in_or_app. right. unfold TRANS_RO_GLOBALS. right. right. right. right. left. reflexivity.
  - unfold in_zr. cbn [fst snd]. lia.
Qed.
Lemma desk_ro_low : forall a, trans_in_ro_rd a -> 0 <= a < 0xa5000.
Proof.
  intros a H. unfold trans_in_ro_rd in H. apply Exists_exists in H as (zr & Hin & Hz).
  destruct zr as (lo & len). unfold in_zr in Hz. cbn [fst snd] in Hz.
  unfold TRANS_RO_RD, TRANS_RO_GLOBALS in Hin. cbn [app] in Hin.
  repeat (destruct Hin as [Hin | Hin];
    [injection Hin as Hl Hn; subst lo len;
     lazymatch type of Hz with ?l <= _ < _ => let v := eval vm_compute in l in change l with v in Hz end; lia |]).
  destruct Hin.
Qed.

(* ------------------------------------------------------------------ *)
(* The model                                                           *)
(* ------------------------------------------------------------------ *)

(* mrx_desk_m's five cases (fuzz_transport.c:288-297). *)
Lemma desk_m_eq : forall I fr B B' r, TW.M_desk_known B <> 0 ->
  TC.beq_bytes (EPI.mrx_src fr) (TW.M_desk B) = true ->
  EPI.mrx_desk_m I fr B = Some (B', r) -> EPI.mrx_k I fr B = Some (B', r).
Proof.
  intros I fr B B' r HK HE H. unfold EPI.mrx_desk_m, TC.truth in H.
  rewrite (proj2 (Z.eqb_neq _ _) HK) in H. cbn [negb] in H. rewrite HE in H. exact H.
Qed.
Lemma desk_m_ne : forall I fr B B' r, TW.M_desk_known B <> 0 ->
  TC.beq_bytes (EPI.mrx_src fr) (TW.M_desk B) = false ->
  EPI.mrx_desk_m I fr B = Some (B', r) -> B' = B /\ r = 0.
Proof.
  intros I fr B B' r HK HE H. unfold EPI.mrx_desk_m, TC.truth in H.
  rewrite (proj2 (Z.eqb_neq _ _) HK) in H. cbn [negb] in H. rewrite HE in H. exact (desk_some_inv _ _ _ _ H).
Qed.
Lemma desk_m_cmd : forall I fr B B' r, TW.M_desk_known B = 0 ->
  ((EPI.mrx_fc fr =? TC.SPEC_CMD_E0) || (EPI.mrx_fc fr =? TC.SPEC_CMD_E1))%bool = false ->
  EPI.mrx_desk_m I fr B = Some (B', r) -> B' = B /\ r = 0.
Proof.
  intros I fr B B' r HK HC H. unfold EPI.mrx_desk_m, TC.truth in H.
  rewrite HK in H. cbn [Z.eqb negb] in H. rewrite HC in H. cbn [negb] in H. exact (desk_some_inv _ _ _ _ H).
Qed.
Lemma desk_m_oui_no : forall I fr B B' r, TW.M_desk_known B = 0 ->
  ((EPI.mrx_fc fr =? TC.SPEC_CMD_E0) || (EPI.mrx_fc fr =? TC.SPEC_CMD_E1))%bool = true ->
  TC.beq_bytes (firstn 3 (EPI.mrx_src fr)) TC.SPEC_OUI = false ->
  EPI.mrx_desk_m I fr B = Some (B', r) -> B' = B /\ r = 0.
Proof.
  intros I fr B B' r HK HC HO H. unfold EPI.mrx_desk_m, TC.truth in H.
  rewrite HK in H. cbn [Z.eqb negb] in H. rewrite HC in H. cbn [negb] in H. rewrite HO in H. cbn [negb] in H.
  exact (desk_some_inv _ _ _ _ H).
Qed.
Lemma desk_m_oui_yes : forall I fr B B' r, TW.M_desk_known B = 0 ->
  ((EPI.mrx_fc fr =? TC.SPEC_CMD_E0) || (EPI.mrx_fc fr =? TC.SPEC_CMD_E1))%bool = true ->
  TC.beq_bytes (firstn 3 (EPI.mrx_src fr)) TC.SPEC_OUI = true ->
  EPI.mrx_desk_m I fr B = Some (B', r) ->
  EPI.mrx_k I fr (TW.set_M_desk_known (TW.set_M_desk B (EPI.mrx_src fr)) 1) = Some (B', r).
Proof.
  intros I fr B B' r HK HC HO H. unfold EPI.mrx_desk_m, TC.truth in H.
  rewrite HK in H. cbn [Z.eqb negb] in H. rewrite HC in H. cbn [negb] in H. rewrite HO in H. cbn [negb] in H.
  exact H.
Qed.

(* The cmd test of the code: (c & 0xfe) = 0xe0 exactly when c is e0 or e1. *)
Lemma desk_cmd_mask : forall c, 0 <= c < 256 -> (Z.land c 254 =? 224) = ((c =? 224) || (c =? 225))%bool.
Proof.
  intros c Hc.
  assert (Hb : forall z, 0 <= z < 256 -> (Z.land z 254 =? 224) = ((z =? 224) || (z =? 225))%bool).
  { intros z Hz.
    assert (HF : forallb (fun k : nat => Bool.eqb (Z.land (Z.of_nat k) 254 =? 224)
                                                  ((Z.of_nat k =? 224) || (Z.of_nat k =? 225))%bool)
                   (seq 0 256) = true) by (vm_compute; reflexivity).
    rewrite forallb_forall in HF. specialize (HF (Z.to_nat z) ltac:(apply in_seq; lia)).
    rewrite Z2Nat.id in HF by lia. apply Bool.eqb_prop in HF. exact HF. }
  exact (Hb c Hc).
Qed.

(* bv_eqb against 0. *)
Lemma desk_eqb0 : forall a : word, bv_eqb a (Z_to_bv 64 0) = true <-> a = w64 0.
Proof.
  intros a. unfold bv_eqb. split.
  - intros H. apply Z.eqb_eq in H. apply bv_eq. exact H.
  - intros ->. apply Z.eqb_refl.
Qed.

(* ------------------------------------------------------------------ *)
(* The walk                                                            *)
(* ------------------------------------------------------------------ *)

Section seg. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis HCELLS : transport_cells B.
Hypothesis HMRX : trans_mrx_cells B.
Hypothesis HRO : trans_ro_rd_unowned B.
Hypothesis HNE : trans_rom_no_errno B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis MTL : ameter_laws MT.
Hypothesis HGX : gx_ok tfibsegs B TG.G_HARNESS.
Hypothesis HGNE : gx_noerrno B TG.G_HARNESS.
Hypothesis HBCMP : forall fx' : YK11.FPState, @abcmp_realizes fx' rc tfibsegs B (transport_sigma TS___interceptor_trampoline_bcmp).
Hypothesis HMCPY : forall fx' : YK11.FPState, @aintrin_realizes fx' rc tfibsegs B OCpy (transport_sigma TS___asan_memcpy).
Hypothesis HML : forall fx' : YK11.FPState, @transport_m_lost_cg fx' rc B MT (transport_sigma TS_m_lost).
Hypothesis HDN : forall fx' : YK11.FPState, @transport_desk_named_cg fx' rc B MT (transport_sigma TS_desk_named).
Hypothesis HMW : forall fx' : YK11.FPState, @transport_m_wake_cg fx' rc B MT (transport_sigma TS_m_wake).
Hypothesis HMO : forall fx' : YK11.FPState, @transport_m_maybe_online_cg fx' rc B MT (transport_sigma TS_m_maybe_online).
Hypothesis HMT : forall fx' : YK11.FPState, @transport_m_tick_cg fx' rc B MT (transport_sigma TS_m_tick).
Variable sp1 : Z.
Variable regs0 : bvmap 5 word.
Variable lyc : alayout.
Variable Sc : astate.
Variable W : world tfibsegs.
Variable memc : word -> option byte.
Variable mdc : Model.
Variable fr : TI.tframe.
Variable n : Z.
Variable Bw' : list byte.
Variable r : Z.
Hypothesis HST : mrx_static B sp1 regs0 lyc Sc W memc mdc fr n.
Local Notation K := (@mrx_K fx rc B MT sp1 regs0 lyc Sc W memc mdc Bw' r).

Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transport_listing PI_transport).
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).
Local Abbreviation IPOST := (@mrx_ipost fx rc B MT sp1 regs0 lyc Sc W memc mdc Bw' r).
Local Abbreviation fa := (TI.tf_addr fr).

(* The image objects and the pcs: object 8 is M, object 48 SPEC_OUI; DESK 0x84b08 = 14500, EPI 0x8496c = 14088,
   BODY 0x84b70 = 14604. *)
Lemma desk_vals : VAL (A_OBJ 8) = TA_M /\ VAL (A_OBJ 48) = TRANS_SPEC_OUI /\
  BASE + 14500 = MRX_PC OFF_DESK /\ BASE + 14088 = MRX_PC OFF_EPI /\ BASE + 14604 = MRX_PC OFF_BODY.
Proof. vm_compute. repeat split. Qed.

Lemma desk_img : forall regs Bw, img_env VAL A_LIM (desk_E regs Bw).
Proof. intros regs Bw. unfold desk_E. apply Eimg_env. Qed.
Lemma desk_imgf : forall regs, img_env VAL A_LIM (desk_Ef regs).
Proof. intros regs. unfold desk_Ef. apply Eimg_env. Qed.
Lemma desk_agree : forall regs Bw,
  env_agree 32 (Ereg regs [w64 SHADOW_OFF; Z_to_bv 64 (TW.u_at Bw TW.A_M_desk_known 4)]) (desk_E regs Bw).
Proof. intros regs Bw. split; [intros k Hk; unfold desk_E; apply Eimg_low; unfold A_TEXT; lia | reflexivity]. Qed.
Lemma desk_agreef : forall regs, env_agree 32 (Ereg regs [w64 SHADOW_OFF]) (desk_Ef regs).
Proof. intros regs. split; [intros k Hk; unfold desk_Ef; apply Eimg_low; unfold A_TEXT; lia | reflexivity]. Qed.

(* The fresh state at offset pc. *)
Lemma desk_entryf : forall (H : word -> bool) regs mem pc,
  st_ok_pi segs VAL (desk_Ef regs) (desk_ssf pc)
    (restrict H (@YK11.mkst fx regs (Z_to_bv 64 (BASE + pc)) mem (YK11.seg_rom segs))).
Proof.
  intros H regs mem pc.
  assert (E32 : ew (desk_Ef regs) 32 = Z_to_bv 64 SHADOW_OFF)
    by (unfold desk_Ef; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  rewrite restrict_mkst_fx. unfold desk_ssf.
  apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - cbn [pairwise_disjoint]. exact I.
  - unfold desk_factsf, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E32. rewrite (unsigned_lit_small SHADOW_OFF) by (unfold SHADOW_OFF; lia).
    rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; unfold SHADOW_OFF; lia.
Qed.

(* The state at the cut. *)
Lemma desk_entry0 : forall (Wc : world segs) regs mem Bw,
  (forall a, spZ regs + 8 <= a < spZ regs + 16 -> apresent (w_H Wc) mem a) ->
  2 ^ 46 <= spZ regs -> spZ regs <= 2 ^ 47 -> spZ regs mod 16 = 0 ->
  tw_at TMAP_A (aview segs (w_H Wc) mem) Bw ->
  st_ok_pi segs VAL (desk_E regs Bw) desk_ss0
    (restrict (w_H Wc) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + 14500)) mem (YK11.seg_rom segs))).
Proof.
  intros Wc regs mem Bw Hpres Hsp1 Hsp2 Hsp16 Htw.
  destruct desk_vals as (V8 & _ & _ & _ & _).
  set (E := desk_E regs Bw).
  assert (EM : TA_M = 6156640) by reflexivity.
  assert (E2 : ew E 2 = YK11.getr regs 2) by (unfold E, desk_E; apply ew_Eimg_Ereg_nat; reflexivity).
  assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
  assert (EOB : forall j, (j < 95)%nat -> ew E (A_OBJ j) = Z_to_bv 64 (VAL (A_OBJ j)))
    by (intros j Hj; unfold E, desk_E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
  assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF)
    by (unfold E, desk_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (E33 : ew E 33 = Z_to_bv 64 (TW.u_at Bw TW.A_M_desk_known 4))
    by (unfold E, desk_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
  pose proof (TWL.u_at_range Bw TW.A_M_desk_known 4) as R33. change (8 * Z.of_nat 4) with 32 in R33.
  assert (B8 : base_val E (Some (A_OBJ 8)) = TA_M).
  { cbn [base_val]. rewrite (EOB 8%nat ltac:(lia)), V8. apply unsigned_lit_small. lia. }
  assert (U8 : bv_unsigned (ew E (A_OBJ 8)) = TA_M) by exact B8.
  rewrite restrict_mkst_fx. unfold desk_ss0.
  apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    + unfold desk_sp_region, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable segs). apply Hpres. lia.
    + unfold desk_m_region, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
      rewrite B8. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val segs E _ TA_M 0 4 (SOff 33 0) (TW.u_at Bw TW.A_M_desk_known 4));
        [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | lia |].
      exact (tw_read_val segs _ TMAP_A Bw TW.OFF_M TA_M TW.SZ_M 0 4 TMAP_A_ok Htw TMAP_A_M
        ltac:(lia) ltac:(unfold TW.SZ_M; lia)).
  - apply pairwise_disjoint_of_extents.
    unfold desk_sp_region, desk_m_region, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite B8. cbn [base_val]. rewrite Usp.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    repeat split; first [exact I | lia].
  - unfold desk_facts0, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, U8, E32, E33, (unsigned_lit_small SHADOW_OFF) by (unfold SHADOW_OFF; lia).
    rewrite (unsigned_lit_small (TW.u_at Bw TW.A_M_desk_known 4)) by lia.
    change (2 ^ 4) with 16. change (2 ^ 5) with 32. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I;
      first [exact Hsp16 | lia | rewrite ?EM; reflexivity].
Qed.

(* The state at the memcpy's return: M.desk_known writable, based on s3. *)
Lemma desk_entryw : forall ly' S' (Wc : world segs) regs mem md',
  @AR rc segs B ly' S' Wc mem md' -> YK11.getr regs 19 = w64 TA_M ->
  st_ok_pi segs VAL (desk_Ef regs) desk_ssw
    (restrict (w_H Wc) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + 14596)) mem (YK11.seg_rom segs))).
Proof.
  intros ly' S' Wc regs mem md' HAR H19.
  assert (EM : TA_M = 6156640) by reflexivity.
  set (E := desk_Ef regs).
  assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF)
    by (unfold E, desk_Ef; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (E19 : ew E 19 = w64 TA_M)
    by (unfold E, desk_Ef; rewrite (ew_Eimg_Ereg_nat regs _ 19 (Z_to_bv 5 19) eq_refl); exact H19).
  assert (U19 : bv_unsigned (ew E 19) = TA_M) by (rewrite E19; apply unsigned_lit_small; lia).
  rewrite restrict_mkst_fx. unfold desk_ssw.
  apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil].
    unfold desk_w_region, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U19. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS (TA_M + o) G_HARNESS_rw). apply desk_inG. lia.
  - cbn [pairwise_disjoint all_disjoint]. repeat split; exact I.
  - unfold desk_factsw, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U19, E32, (unsigned_lit_small SHADOW_OFF) by (unfold SHADOW_OFF; lia).
    change (2 ^ 5) with 32. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; first [lia | rewrite ?EM; reflexivity].
Qed.

(* The denotations the runs leave. *)
Lemma desk_sv_off : forall (E : env) k c v, ew E k = w64 v -> 0 <= v < 2 ^ 64 ->
  sv_denot E (SOff k c) = Z_to_bv 64 (v + c).
Proof.
  intros E k c v Hk Hv. cbn [sv_denot]. rewrite Hk. unfold w64.
  rewrite unsigned_lit_small by lia. reflexivity.
Qed.

Lemma desk_sv_off0 : forall (E : env) k v, ew E k = w64 v -> 0 <= v < 2 ^ 64 ->
  sv_denot E (SOff k 0) = w64 v.
Proof. intros E k v Hk Hv. rewrite (desk_sv_off E k 0 v Hk Hv), Z.add_0_r. reflexivity. Qed.

(* The sign-extended 4-byte load of M.desk_known, and the branch on it. *)
Lemma desk_sext : forall (E : env) Bw, ew E 33 = Z_to_bv 64 (TW.u_at Bw TW.A_M_desk_known 4) ->
  sv_denot E (SExt true 32 (SOff 33 0)) = Z_to_bv 64 (TW.M_desk_known Bw).
Proof.
  intros E Bw H. pose proof (TWL.u_at_range Bw TW.A_M_desk_known 4) as R.
  change (8 * Z.of_nat 4) with 32 in R.
  cbn [sv_denot]. rewrite H. rewrite unsigned_lit_small by lia. rewrite Z.add_0_r.
  rewrite LMem.sext_small, LMem.signed_of_extract by lia.
  rewrite unsigned_lit_small by lia. reflexivity.
Qed.

Lemma desk_br_known : forall (E : env) Bw, ew E 33 = Z_to_bv 64 (TW.u_at Bw TW.A_M_desk_known 4) ->
  branch_taken BC_EQ (sv_denot E (SExt true 32 (SOff 33 0))) (sv_denot E (SLit 0))
  = (TW.M_desk_known Bw =? 0).
Proof.
  intros E Bw H. cbn [branch_taken]. rewrite (desk_sext E Bw H). cbn [sv_denot].
  pose proof (TWL.s32_range Bw TW.A_M_desk_known) as S.
  change (TW.s32_at Bw TW.A_M_desk_known) with (TW.M_desk_known Bw) in S.
  apply EPI.mrxk_eqb; lia.
Qed.

(* (s9 & 0xfe) <> 0xe0: the cmd is neither e0 nor e1. *)
Lemma desk_land_fact : forall c, 0 <= c < 256 ->
  0 <= Z.land c 254 <= 254 /\ (Z.land c 254 =? 224) = ((c =? 224) || (c =? 225))%bool.
Proof.
  intros c Hc.
  assert (HF : forallb (fun k : nat =>
      ((0 <=? Z.land (Z.of_nat k) 254) && (Z.land (Z.of_nat k) 254 <=? 254) &&
       Bool.eqb (Z.land (Z.of_nat k) 254 =? 224)
                ((Z.of_nat k =? 224) || (Z.of_nat k =? 225))))%bool (seq 0 256) = true)
    by (vm_compute; reflexivity).
  rewrite forallb_forall in HF. specialize (HF (Z.to_nat c) ltac:(apply in_seq; lia)).
  rewrite Z2Nat.id in HF by lia.
  apply andb_prop in HF as [HF HE]. apply andb_prop in HF as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2. apply Bool.eqb_prop in HE.
  split; [lia | exact HE].
Qed.

Lemma desk_br_cmd : forall (E : env) c, ew E 25 = w64 c -> 0 <= c < 256 ->
  branch_taken BC_NE (sv_denot E (SAlu ALU_AND (SOff 25 0) (SLit 254))) (sv_denot E (SLit 224))
  = negb ((c =? 224) || (c =? 225))%bool.
Proof.
  intros E c Hc Hr. destruct (desk_land_fact c Hr) as [Hb He].
  cbn [branch_taken].
  assert (D : sv_denot E (SAlu ALU_AND (SOff 25 0) (SLit 254)) = Z_to_bv 64 (Z.land c 254)).
  { change (sv_denot E (SAlu ALU_AND (SOff 25 0) (SLit 254)))
      with (alu64 ALU_AND (sv_denot E (SOff 25 0)) (sv_denot E (SLit 254))).
    rewrite (desk_sv_off E 25 0 c Hc ltac:(lia)). rewrite Z.add_0_r. cbn [sv_denot].
    apply bv_eq. cbn [alu64 alu]. rewrite bv_and_unsigned, !Z_to_bv_unsigned.
    unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
    rewrite (Z.mod_small c) by lia. rewrite (Z.mod_small 254) by lia.
    rewrite (Z.mod_small (Z.land c 254)) by lia. reflexivity. }
  rewrite D. cbn [sv_denot]. rewrite EPI.mrxk_eqb by lia. rewrite He. reflexivity.
Qed.

(* The branches on a bcmp result. *)
Lemma desk_br_eq : forall (E : env) regs, (forall k (q : bv 5), Z.of_nat k = bv_unsigned q -> ew E k = YK11.getr regs q) ->
  branch_taken BC_EQ (sv_denot E (SOff 10 0)) (sv_denot E (SLit 0)) = true <-> YK11.getr regs 10 = w64 0.
Proof.
  intros E regs HE. cbn [branch_taken sv_denot].
  rewrite (HE 10%nat (Z_to_bv 5 10) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned.
  exact (desk_eqb0 _).
Qed.
Lemma desk_br_ne : forall (E : env) regs, (forall k (q : bv 5), Z.of_nat k = bv_unsigned q -> ew E k = YK11.getr regs q) ->
  branch_taken BC_NE (sv_denot E (SOff 10 0)) (sv_denot E (SLit 0)) = true <-> YK11.getr regs 10 <> w64 0.
Proof.
  intros E regs HE. cbn [branch_taken sv_denot].
  rewrite (HE 10%nat (Z_to_bv 5 10) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned.
  rewrite negb_true_iff. pose proof (desk_eqb0 (YK11.getr regs (Z_to_bv 5 10))) as Q.
  destruct (bv_eqb (YK11.getr regs (Z_to_bv 5 10)) (Z_to_bv 64 0)).
  - split; [discriminate | intros N; exfalso; apply N; exact (proj1 Q eq_refl)].
  - split; [intros _ Z0; apply Q in Z0; discriminate Z0 | reflexivity].
Qed.

Lemma desk_Forall_nth : forall {A : Type} (P : A -> Prop) (l : list A) (m : nat) (x : A),
  Forall P l -> nth_error l m = Some x -> P x.
Proof. intros A P l m x HF Hn. rewrite Forall_forall in HF. apply HF. exact (nth_error_In l m Hn). Qed.

(* The static facts. *)
Lemma desk_sp : 2 ^ 46 <= sp1 - MRX_STK /\ sp1 <= 2 ^ 47 /\ MRX_STK = 8352 /\ MRX_FRAME = 144 /\
  sp1 mod 16 = 0 /\ YK0s.ret_ok (YK11.getr regs0 1) /\
  YK11.getr regs0 3 = w64 (as_gp B) /\ YK11.getr regs0 4 = w64 (as_tp B).
Proof.
  pose proof HST as (_ & Hm16 & _ & H46 & H47 & Hra & _ & Hgp & Htp & _).
  split; [exact H46|]. split; [exact H47|]. split; [reflexivity|]. split; [reflexivity|].
  split; [exact Hm16|]. split; [exact Hra|]. split; [exact Hgp | exact Htp].
Qed.

Section cut.
Variable Wc : world segs.
Variable Bwc : list byte.
Variable regs2 : bvmap 5 word.
Variable mem2 : word -> option byte.
Hypothesis KE : K (MRX_PC OFF_EPI) (R_EPI Bw' r).
Hypothesis KB : K (MRX_PC OFF_BODY) (R_BODY fr n sp1 lyc Sc Bw' r).
Hypothesis HMO2 : mo_le MT Sc Sc 0.
Hypothesis HSV : mrx_saved Wc mem2 sp1 regs0.
Hypothesis HTW : tw_at TMAP_A (aview segs (w_H Wc) mem2) Bwc.
Hypothesis HFRS : mrx_frs fr Wc mem2.
Hypothesis HHDR : mrx_hdr fr n.
Hypothesis H2 : YK11.getr regs2 2 = Z_to_bv 64 (sp1 - MRX_FRAME).
Hypothesis H3 : YK11.getr regs2 3 = YK11.getr regs0 3.
Hypothesis H4 : YK11.getr regs2 4 = YK11.getr regs0 4.
Hypothesis H8 : YK11.getr regs2 8 = w64 (TI.tf_addr fr).
Hypothesis H9 : YK11.getr regs2 9 = w64 (TI.tf_addr fr + 6).
Hypothesis H19 : YK11.getr regs2 19 = w64 (mfb fr 18).
Hypothesis H20 : YK11.getr regs2 20 = w64 (DSpec.spec_be16 (TW.zs (TI.tf_bytes fr)) 14).
Hypothesis HHR : mrx_hregs fr Wc sp1 regs2 mem2.
Hypothesis HM : EPI.mrx_desk_m timg_A fr Bwc = Some (Bw', r).

(* The bytes a step may change: the calls' scratch below the frame, the spill slot the first run writes, and the
   bytes of M the memcpy and the store write. *)
Definition desk_cwin (a : Z) : Prop := sp1 - MRX_STK <= a < sp1 - MRX_FRAME.
Definition desk_slot (a : Z) : Prop := sp1 - MRX_FRAME + 8 <= a < sp1 - MRX_FRAME + 16.
Definition desk_KV (P : Z -> Prop) (m : word -> option byte) : Prop :=
  forall a, 0 <= a < 2 ^ 64 -> ~ desk_cwin a -> ~ desk_slot a -> ~ P a ->
    aview segs (w_H Wc) m a = aview segs (w_H Wc) mem2 a.
Definition desk_PM (P : Z -> Prop) : Prop := forall a, P a -> TA_M <= a < TA_M + 10.
(* The callee-saved registers are the cut's, but s3 = &M. *)
Definition desk_rg (regs : bvmap 5 word) : Prop :=
  (forall q, acallee_saved q -> q <> 19 -> YK11.getr regs (Z_to_bv 5 q) = YK11.getr regs2 (Z_to_bv 5 q)) /\
  YK11.getr regs (Z_to_bv 5 19) = w64 TA_M.
(* A machine inside the segment. *)
Definition desk_mid (P : Z -> Prop) (regs : bvmap 5 word) (m : word -> option byte) (md : Model) : Prop :=
  @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS 0 [] MRX_STK sp1 [] lyc Sc W memc mdc [] lyc Sc Wc
    m md 0 /\
  desk_rg regs /\ desk_KV P m /\ mrx_spill Wc m sp1 8 fr 18.

Lemma desk_PM_false : desk_PM (fun _ => False).
Proof. intros a Ha. cbv beta in Ha. destruct Ha. Qed.

Ltac desk_lia := unfold desk_cwin, desk_slot, MRX_FRAME, ESTACK, TA_M in *; lia.

(* The frame: apart from the stack window, below 2 ^ 63, at least 30 bytes. *)
Lemma desk_fpl : 0 < fa /\ (fa + mlen fr <= sp1 - MRX_STK \/ sp1 <= fa) /\ fa + mlen fr <= 2 ^ 63 /\ 30 <= mlen fr.
Proof.
  pose proof HST as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hfa0 & _ & _ & Hpl & _).
  pose proof HFRS as (_ & (_ & _ & _ & _ & _ & H63) & _). pose proof HHDR as (Hn & _).
  split; [exact Hfa0|]. split; [exact Hpl|]. split; [exact H63 | lia].
Qed.

(* No byte of M the call writes is a frame byte. *)
Lemma desk_apart_M : forall a, TA_M <= a < TA_M + 10 -> ~ (fa <= a < fa + mlen fr).
Proof.
  intros a Ha. pose proof HST as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hap & _).
  intros Hf. apply (Hap a); [|exact Hf].
  unfold mrx_wr, twa_fld, TW.A_M_desk_known, TW.A_M_desk, TW.OFF_M.
  destruct (Z_lt_le_dec a (TA_M + 4)) as [Hl|Hl]; [left; lia | right; left; lia].
Qed.

(* A run from a state with no region keeps every byte. *)
Lemma desk_frame_kept : forall (E : env) rs (m m' : word -> option byte),
  frame_of E rs (mrestrict (w_H Wc) m) (mrestrict (w_H Wc) m') -> windows rs = [] ->
  forall a, 0 <= a < 2 ^ 64 -> aview segs (w_H Wc) m' a = aview segs (w_H Wc) m a.
Proof.
  intros E rs m m' HF Hw a Ha. apply (kept_of_frame E rs (w_H Wc) m m' (fun _ => False) HF); [|exact Ha | intros []].
  intros b wlo whi x Hin. rewrite Hw in Hin. destruct Hin.
Qed.

Lemma desk_mid_step : forall P P' regs m md regs' m' md',
  desk_mid P regs m md -> desk_PM P' -> (forall a, P a -> P' a) ->
  aregs_preserved regs regs' ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ desk_cwin a -> ~ P' a ->
     aview segs (w_H Wc) m' a = aview segs (w_H Wc) m a) ->
  @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS 0 [] MRX_STK sp1 [] lyc Sc W memc mdc [] lyc Sc Wc
    m' md' 0 ->
  desk_mid P' regs' m' md'.
Proof.
  intros P P' regs m md regs' m' md' (HJ & (RG & RG19) & KV & SPL) HPM HPP HP KEEP HJ'.
  pose proof desk_sp as (SP1 & SP2 & STK & FRM & _).
  split; [exact HJ'|]. split; [split|].
  - intros q Hq H19'. rewrite (HP q Hq). exact (RG q Hq H19').
  - rewrite (HP 19 ltac:(unfold acallee_saved; lia)). exact RG19.
  - split.
    + intros a Ha Hw1 Hw2 Hw3. rewrite (KEEP a Ha Hw1 Hw3).
      exact (KV a Ha Hw1 Hw2 ltac:(intros HPa; exact (Hw3 (HPP a HPa)))).
    + apply (mrx_spill_kept Wc Wc m m' sp1 8 fr 18 SPL). intros a Ha.
      apply KEEP; [desk_lia | desk_lia | intros HPa; pose proof (HPM a HPa); desk_lia].
Qed.

(* The same step with the registers and the spill slot given (the runs of the segment's own state, which may write
   the slot). *)
Lemma desk_mid_step2 : forall P P' regs m md regs' m' md',
  desk_mid P regs m md -> desk_PM P' -> (forall a, P a -> P' a) ->
  desk_rg regs' -> mrx_spill Wc m' sp1 8 fr 18 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ desk_cwin a -> ~ desk_slot a -> ~ P' a ->
     aview segs (w_H Wc) m' a = aview segs (w_H Wc) m a) ->
  @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS 0 [] MRX_STK sp1 [] lyc Sc W memc mdc [] lyc Sc Wc
    m' md' 0 ->
  desk_mid P' regs' m' md'.
Proof.
  intros P P' regs m md regs' m' md' (HJ & RG & KV & SPL) HPM HPP RG' SPL' KEEP HJ'.
  split; [exact HJ'|]. split; [exact RG'|]. split; [|exact SPL'].
  intros a Ha Hw1 Hw2 Hw3. rewrite (KEEP a Ha Hw1 Hw2 Hw3).
  exact (KV a Ha Hw1 Hw2 ltac:(intros HPa; exact (Hw3 (HPP a HPa)))).
Qed.

(* ---- what the view keeps ---- *)

Lemma desk_frs_kept : forall P m, desk_PM P -> desk_KV P m -> mrx_frs fr Wc m.
Proof.
  intros P m HPM KV. pose proof HFRS as (G & RD & ROM).
  pose proof desk_fpl as (F0 & FP & F63 & F30). pose proof desk_sp as (SP1 & SP2 & STK & FRM & _).
  split; [|split].
  - apply (garr8_frame segs _ _ _ _ G). intros a Ha. rewrite length_map in Ha. fold (mlen fr) in Ha.
    apply desk_mbyte_of_aview. apply KV;
      [desk_lia | desk_lia | desk_lia | intros HPa; exact (desk_apart_M a (HPM a HPa) Ha)].
  - apply (trans_rd_ok_view Wc Wc mem2 m _ _ RD).
    + intros a Ha. apply KV;
        [desk_lia | desk_lia | desk_lia | intros HPa; exact (desk_apart_M a (HPM a HPa) Ha)].
    + intros s Hs. apply KV; unfold kLowMemEnd, kHighShadowEnd in *;
        [desk_lia | desk_lia | desk_lia | intros HPa; pose proof (HPM s HPa); desk_lia].
  - intros a Ha. pose proof (desk_ro_low a Ha) as Hl.
    rewrite (KV a ltac:(lia) ltac:(desk_lia) ltac:(desk_lia)
      ltac:(intros HPa; pose proof (HPM a HPa); desk_lia)).
    exact (ROM a Ha).
Qed.

Lemma desk_saved_kept : forall P m, desk_PM P -> desk_KV P m -> mrx_saved Wc m sp1 regs0.
Proof.
  intros P m HPM KV. pose proof desk_sp as (SP1 & SP2 & STK & FRM & _).
  apply (mrx_saved_kept Wc Wc mem2 m sp1 regs0 HSV). intros a Ha.
  apply KV; [desk_lia | desk_lia | desk_lia | intros HPa; pose proof (HPM a HPa); desk_lia].
Qed.

Lemma desk_tw_kept : forall m, desk_KV (fun _ => False) m -> tw_at TMAP_A (aview segs (w_H Wc) m) Bwc.
Proof.
  intros m KV. pose proof desk_sp as (SP1 & SP2 & STK & FRM & _).
  apply (tw_kept TMAP_A (aview segs (w_H Wc) mem2)); [exact HTW|].
  intros x Hx. pose proof (TMAP_A_hull x Hx) as Hh.
  unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh.
  apply KV; [desk_lia | desk_lia | desk_lia | intros []].
Qed.

Lemma desk_hregs_kept : forall P regs m, desk_PM P -> desk_rg regs -> desk_KV P m ->
  mrx_hregs fr Wc sp1 regs m.
Proof.
  intros P regs m HPM (RG & _) KV. pose proof desk_sp as (SP1 & SP2 & STK & FRM & _).
  pose proof HHR as (S18 & S21 & S22 & S23 & S24 & S25 & S26 & S27 & P16 & P24 & P32).
  assert (CS : forall q, 18 <= q <= 27 -> acallee_saved q) by (intros q Hq; unfold acallee_saved; lia).
  assert (KP : forall o, 16 <= o <= 32 -> mrx_spill Wc mem2 sp1 o fr (if o =? 16 then 25 else if o =? 24 then 24 else 21) ->
    mrx_spill Wc m sp1 o fr (if o =? 16 then 25 else if o =? 24 then 24 else 21)).
  { intros o Ho HS'. apply (mrx_spill_kept Wc Wc mem2 m sp1 o fr _ HS'). intros a Ha.
    apply KV; [desk_lia | desk_lia | desk_lia | intros HPa; pose proof (HPM a HPa); desk_lia]. }
  split; [exact (eq_trans (RG 18 (CS 18 ltac:(lia)) ltac:(lia)) S18)|].
  split; [exact (eq_trans (RG 21 (CS 21 ltac:(lia)) ltac:(lia)) S21)|].
  split; [exact (eq_trans (RG 22 (CS 22 ltac:(lia)) ltac:(lia)) S22)|].
  split; [exact (eq_trans (RG 23 (CS 23 ltac:(lia)) ltac:(lia)) S23)|].
  split; [exact (eq_trans (RG 24 (CS 24 ltac:(lia)) ltac:(lia)) S24)|].
  split; [exact (eq_trans (RG 25 (CS 25 ltac:(lia)) ltac:(lia)) S25)|].
  split; [exact (eq_trans (RG 26 (CS 26 ltac:(lia)) ltac:(lia)) S26)|].
  split; [exact (eq_trans (RG 27 (CS 27 ltac:(lia)) ltac:(lia)) S27)|].
  split; [exact (KP 16 ltac:(lia) P16)|].
  split; [exact (KP 24 ltac:(lia) P24) | exact (KP 32 ltac:(lia) P32)].
Qed.

(* ---- the bytes the compares read ---- *)

Lemma desk_frame_view : forall P m, desk_PM P -> desk_KV P m -> forall j, 0 <= j < mlen fr ->
  aview segs (w_H Wc) m (fa + j) = Some (bv_unsigned (nth (Z.to_nat j) (TI.tf_bytes fr) (Z_to_bv 8 0))).
Proof.
  intros P m HPM KV j Hj. pose proof (desk_frs_kept P m HPM KV) as (G & _ & _).
  replace (fa + j) with (fa + Z.of_nat (Z.to_nat j)) by lia.
  apply (desk_garr_view Wc m fa (TI.tf_bytes fr) (Z.to_nat j) G). unfold mlen in Hj. lia.
Qed.

Lemma desk_oui_view : forall P m, desk_PM P -> desk_KV P m -> forall i, 0 <= i < 3 ->
  aview segs (w_H Wc) m (TRANS_SPEC_OUI + i) = Some (bv_unsigned (nth (Z.to_nat i) TC.SPEC_OUI (Z_to_bv 8 0))).
Proof.
  intros P m HPM KV i Hi. pose proof (desk_frs_kept P m HPM KV) as (_ & _ & ROM).
  rewrite (ROM _ (desk_oui_ro i Hi)). exact (desk_oui_rom i Hi).
Qed.

(* M.desk's six bytes at a memory holding the world Bcur. *)
Lemma desk_mdesk_view : forall m Bcur, tw_at TMAP_A (aview segs (w_H Wc) m) Bcur -> forall i, 0 <= i < 6 ->
  aview segs (w_H Wc) m (TA_M + 4 + i) = Some (bv_unsigned (nth (Z.to_nat i) (TW.M_desk Bcur) (Z_to_bv 8 0))).
Proof.
  intros m Bcur HW i Hi.
  pose proof (tw_garr8 segs (mrestrict (w_H Wc) m) TMAP_A Bcur TW.OFF_M TA_M TW.SZ_M 4 6 TMAP_A_ok HW
    TMAP_A_M ltac:(lia) ltac:(unfold TW.SZ_M; lia)) as G.
  replace (TA_M + 4 + i) with (TA_M + 4 + Z.of_nat (Z.to_nat i)) by lia.
  change (TW.zs (TW.sub Bcur (TW.OFF_M + 4) 6)) with (map DSpec.bz (TW.sub Bcur (TW.OFF_M + 4) 6)) in G.
  rewrite (desk_garr_view Wc m (TA_M + 4) (TW.sub Bcur (TW.OFF_M + 4) 6) (Z.to_nat i) G).
  - unfold TW.M_desk, TW.A_M_desk. reflexivity.
  - assert (L : length (TW.sub Bcur (TW.OFF_M + 4) 6) = 6%nat).
    { apply TWL.length_sub; [unfold TW.OFF_M; lia|].
      rewrite (tw_len TMAP_A _ Bcur HW), Z2Nat.id by (unfold TW.W_LEN; lia).
      unfold TW.OFF_M, TW.W_LEN. lia. }
    lia.
Qed.

(* The compare of [fa + k, + N) with [y, + N) holding l is the model's beq_bytes. *)
Lemma desk_cmp : forall P m y k (N : nat) (l : list byte), desk_PM P -> desk_KV P m ->
  0 <= k -> k + Z.of_nat N <= mlen fr -> length l = N ->
  (forall i, 0 <= i < Z.of_nat N ->
     aview segs (w_H Wc) m (y + i) = Some (bv_unsigned (nth (Z.to_nat i) l (Z_to_bv 8 0)))) ->
  ((forall i, 0 <= i < Z.of_nat N -> aview segs (w_H Wc) m (fa + k + i) = aview segs (w_H Wc) m (y + i)) <->
   TC.beq_bytes (TW.sub (TI.tf_bytes fr) k N) l = true).
Proof.
  intros P m y k N l HPM KV Hk HkN Hl HY.
  assert (LS : length (TW.sub (TI.tf_bytes fr) k N) = N) by (apply TWL.length_sub; unfold mlen in HkN; lia).
  assert (FV : forall i, 0 <= i < Z.of_nat N -> aview segs (w_H Wc) m (fa + k + i) =
    Some (bv_unsigned (nth (Z.to_nat i) (TW.sub (TI.tf_bytes fr) k N) (Z_to_bv 8 0)))).
  { intros i Hi. replace (fa + k + i) with (fa + (k + i)) by lia.
    rewrite (desk_frame_view P m HPM KV (k + i) ltac:(unfold mlen in *; lia)).
    rewrite (tw_nth_sub (TI.tf_bytes fr) k N (Z.to_nat i) (Z_to_bv 8 0)) by (unfold mlen in HkN; lia).
    do 3 f_equal. lia. }
  rewrite EPI.mrx_beq_iff, (desk_zs_eq _ _ N LS Hl).
  split; intros H i Hi.
  - specialize (H i Hi). rewrite (FV i Hi), (HY i Hi) in H. injection H as H. exact H.
  - rewrite (FV i Hi), (HY i Hi). f_equal. exact (H i Hi).
Qed.

(* ---- the ranges the compares read ---- *)

Lemma desk_rd_frame : forall P m x k, desk_PM P -> desk_KV P m -> x = fa + k -> 0 <= k -> k + 6 <= mlen fr ->
  decode_rd_ok Wc m x 6.
Proof.
  intros P m x k HPM KV -> Hk Hk6. pose proof (desk_frs_kept P m HPM KV) as (_ & RD & _).
  apply (trans_rd_ok_sub Wc m fa (mlen fr)); [exact RD | lia | lia | lia].
Qed.

Lemma desk_rd_oui : forall ly' S' P m md', @AR rc segs B ly' S' Wc m md' -> desk_PM P -> desk_KV P m ->
  decode_rd_ok Wc m TRANS_SPEC_OUI 3.
Proof.
  intros ly' S' P m md' HAR HPM KV.
  destruct (HCELLS ly') as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & RB & RO & _).
  destruct HMRX as (_ & _ & HC).
  destruct (HC ly') as (_ & _ & _ & _ & _ & _ & RB8 & RB16 & RB24 & RO8 & RO16 & RO24 & _).
  split; [|split; [|split; [|split; [|split]]]].
  - intros a Ha. replace a with (TRANS_SPEC_OUI + (a - TRANS_SPEC_OUI)) by lia.
    rewrite (desk_oui_view P m HPM KV (a - TRANS_SPEC_OUI) ltac:(lia)). discriminate.
  - intros x Hx. exists 3. split.
    + eapply (desk_const1 B ly' S' Wc m md'); [exact HAR | exact RO | lia |].
      unfold ACells.shadow_addr, ACells.ASAN_K, TRANS_SPEC_OUI, shadow_of_addr, SHADOW_OFF in *.
      Z.div_mod_to_equations. lia.
    + unfold saddr_ok, TRANS_SPEC_OUI in *. right. Z.div_mod_to_equations. lia.
  - intros s' Hs. desk_hull Hs.
    assert (Hc : s' = 0x7fffc210 \/ s' = 0x7fffc211 \/ s' = 0x7fffc212 \/ s' = 0x7fffc213 \/ s' = 0x7fffc214 \/
                 s' = 0x7fffc215 \/ s' = 0x7fffc216 \/ s' = 0x7fffc217) by lia.
    destruct Hc as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]];
      [ eapply desk_const1_nn; [exact HAR | exact RB | lia | reflexivity]
      | eapply desk_const1_nn; [exact HAR | exact RB8 | lia | reflexivity]
      | eapply desk_const1_nn; [exact HAR | exact RB16 | lia | reflexivity]
      | eapply desk_const1_nn; [exact HAR | exact RB24 | lia | reflexivity]
      | eapply desk_const1_nn; [exact HAR | exact RO | lia | reflexivity]
      | eapply desk_const1_nn; [exact HAR | exact RO8 | lia | reflexivity]
      | eapply desk_const1_nn; [exact HAR | exact RO16 | lia | reflexivity]
      | eapply desk_const1_nn; [exact HAR | exact RO24 | lia | reflexivity] ].
  - unfold amem_range, kLowMemEnd, TRANS_SPEC_OUI. lia.
  - unfold TRANS_SPEC_OUI. lia.
  - unfold TRANS_SPEC_OUI. lia.
Qed.

(* [M + 4, M + 10): its bytes are the world's, its shadow is M's zero shadow, its hull [0x800b3e28, 0x800b3e30)
   also holds g_last_counter's last granule and guard bytes. *)
Lemma desk_rd_m : forall ly' S' m md' Bcur, @AR rc segs B ly' S' Wc m md' ->
  tw_at TMAP_A (aview segs (w_H Wc) m) Bcur -> decode_rd_ok Wc m (TA_M + 4) 6.
Proof.
  intros ly' S' m md' Bcur HAR HW.
  assert (EM : TA_M = 6156640) by reflexivity.
  destruct HMRX as (_ & HZM & HC).
  destruct (HC ly') as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & RG0 & RG8 & RG16 & RG24).
  assert (ZS : forall T, T mod 8 = 0 -> TA_M <= T -> T + 8 <= TA_M + TW.SZ_M ->
    aview segs (w_H Wc) m (ACells.shadow_addr T) = Some 0)
    by (intros T Hz1 Hz2 Hz3; exact (decode_zshadow_rd B ly' S' Wc m md' TA_M (TA_M + TW.SZ_M) T HAR Hz1 Hz2 Hz3 HZM)).
  assert (ZSn : forall T s, T mod 8 = 0 -> TA_M <= T -> T + 8 <= TA_M + TW.SZ_M -> ACells.shadow_addr T = s ->
    aview segs (w_H Wc) m s <> None)
    by (intros T s Hz1 Hz2 Hz3 <-; rewrite (ZS T Hz1 Hz2 Hz3); discriminate).
  split; [|split; [|split; [|split; [|split]]]].
  - intros a Ha. replace a with (TA_M + 4 + (a - (TA_M + 4))) by lia.
    rewrite (desk_mdesk_view m Bcur HW (a - (TA_M + 4)) ltac:(lia)). discriminate.
  - intros x Hx. exists 0. split; [|left; reflexivity].
    assert (EQ : shadow_of_addr SHADOW_OFF x = ACells.shadow_addr (8 * (x / 8))).
    { unfold ACells.shadow_addr, ACells.ASAN_K, shadow_of_addr, SHADOW_OFF.
      rewrite Z.mul_comm, Z.div_mul by lia. lia. }
    rewrite EQ. apply ZS; [rewrite Z.mul_comm; apply Z_mod_mult | | ];
      unfold TW.SZ_M in *; Z.div_mod_to_equations; lia.
  - intros s' Hs. desk_hull Hs.
    assert (Hc : s' = 0x800b3e28 \/ s' = 0x800b3e29 \/ s' = 0x800b3e2a \/ s' = 0x800b3e2b \/ s' = 0x800b3e2c \/
                 s' = 0x800b3e2d \/ s' = 0x800b3e2e \/ s' = 0x800b3e2f) by lia.
    destruct Hc as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]];
      [ eapply desk_const1_nn; [exact HAR | exact RG0 | lia | reflexivity]
      | eapply desk_const1_nn; [exact HAR | exact RG8 | lia | reflexivity]
      | eapply desk_const1_nn; [exact HAR | exact RG16 | lia | reflexivity]
      | eapply desk_const1_nn; [exact HAR | exact RG24 | lia | reflexivity]
      | eapply (ZSn TA_M); [reflexivity | lia | unfold TW.SZ_M; lia | reflexivity]
      | eapply (ZSn (TA_M + 8)); [reflexivity | lia | unfold TW.SZ_M; lia | reflexivity]
      | eapply (ZSn (TA_M + 16)); [reflexivity | lia | unfold TW.SZ_M; lia | reflexivity]
      | eapply (ZSn (TA_M + 24)); [reflexivity | lia | unfold TW.SZ_M; lia | reflexivity] ].
  - unfold amem_range, kLowMemEnd. lia.
  - lia.
  - lia.
Qed.

(* ---- the exits ---- *)

Lemma desk_exit_epi : forall regs m md, desk_mid (fun _ => False) regs m md ->
  YK11.getr regs 10 = w64 0 -> Bw' = Bwc -> r = 0 ->
  SRr segs Wc (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (MRX_PC OFF_EPI)) m (YK11.seg_rom segs)) md) IPOST.
Proof.
  intros regs m md (HJ & (RGS & _) & KV & _) R10 EB Er.
  apply (KE Wc Bwc).
  apply (mrx_at_intro B MT sp1 regs0 lyc Sc W memc mdc (MRX_PC OFF_EPI) (R_EPI Bw' r) Wc Bwc lyc Sc regs m md HJ).
  - reflexivity.
  - apply Permutation_refl.
  - exact HMO2.
  - exact (eq_trans (RGS 2 ltac:(unfold acallee_saved; lia) ltac:(lia)) H2).
  - exact (eq_trans (RGS 3 ltac:(unfold acallee_saved; lia) ltac:(lia)) H3).
  - exact (eq_trans (RGS 4 ltac:(unfold acallee_saved; lia) ltac:(lia)) H4).
  - exact (desk_saved_kept _ m desk_PM_false KV).
  - exact (desk_tw_kept m KV).
  - unfold R_EPI. split; [symmetry; exact EB | rewrite Er; exact R10].
Qed.

Lemma desk_exit_body : forall P regs m md Bcur, desk_mid P regs m md -> desk_PM P ->
  tw_at TMAP_A (aview segs (w_H Wc) m) Bcur ->
  EPI.mrx_k timg_A fr Bcur = Some (Bw', r) ->
  SRr segs Wc (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (MRX_PC OFF_BODY)) m (YK11.seg_rom segs)) md) IPOST.
Proof.
  intros P regs m md Bcur (HJ & RG & KV & SPL) HPM HW HK.
  pose proof RG as (RGS & RG19).
  apply (KB Wc Bcur).
  apply (mrx_at_intro B MT sp1 regs0 lyc Sc W memc mdc (MRX_PC OFF_BODY) (R_BODY fr n sp1 lyc Sc Bw' r) Wc Bcur
    lyc Sc regs m md HJ).
  - reflexivity.
  - apply Permutation_refl.
  - exact HMO2.
  - exact (eq_trans (RGS 2 ltac:(unfold acallee_saved; lia) ltac:(lia)) H2).
  - exact (eq_trans (RGS 3 ltac:(unfold acallee_saved; lia) ltac:(lia)) H3).
  - exact (eq_trans (RGS 4 ltac:(unfold acallee_saved; lia) ltac:(lia)) H4).
  - exact (desk_saved_kept P m HPM KV).
  - exact HW.
  - unfold R_BODY. split; [reflexivity|]. split; [reflexivity|].
    split; [exact (desk_frs_kept P m HPM KV)|]. split; [exact HHDR|].
    split; [exact (eq_trans (RGS 8 ltac:(unfold acallee_saved; lia) ltac:(lia)) H8)|].
    split; [exact (eq_trans (RGS 9 ltac:(unfold acallee_saved; lia) ltac:(lia)) H9)|].
    split; [exact RG19|].
    split; [exact (eq_trans (RGS 20 ltac:(unfold acallee_saved; lia) ltac:(lia)) H20)|].
    split; [exact (desk_hregs_kept P regs m HPM RG KV) | split; [exact SPL | exact HK]].
Qed.

(* ---- one call of the bcmp wrapper ---- *)

Lemma desk_bcmp : forall P (regsT : bvmap 5 word) (memT : word -> option byte) (mdT : Model) (x y : Z) (N : Z)
    (raw : word) (Q : world segs -> config -> Prop),
  desk_mid P regsT memT mdT -> desk_PM P ->
  YK11.getr regsT 10 = w64 x -> YK11.getr regsT 11 = w64 y -> YK11.getr regsT 12 = w64 N ->
  0 <= N < 2 ^ 32 ->
  decode_rd_ok Wc memT x N -> decode_rd_ok Wc memT y N ->
  (x + N <= sp1 - MRX_STK \/ sp1 <= x) -> (y + N <= sp1 - MRX_STK \/ sp1 <= y) ->
  YK11.getr regsT 1 = raw -> YK0s.ret_ok raw ->
  (forall regs3 mem3 md3, desk_mid P regs3 mem3 md3 ->
     (YK11.getr regs3 10 = w64 0 <->
        forall i, 0 <= i < N -> aview segs (w_H Wc) memT (x + i) = aview segs (w_H Wc) memT (y + i)) ->
     SRr segs Wc (mkCfg (@YK11.mkst fx regs3 raw mem3 (YK11.seg_rom segs)) md3) Q) ->
  SRr segs Wc (mkCfg (@YK11.mkst fx regsT (Z_to_bv 64 (transport_sigma TS___interceptor_trampoline_bcmp)) memT
    (YK11.seg_rom segs)) mdT) Q.
Proof.
  intros P regsT memT mdT x y N raw Q MID HPM R10 R11 R12 HN RDX RDY OFX OFY R1 HRAW KK.
  pose proof MID as (HJ & (RG & RG19) & KV & SPL).
  pose proof desk_sp as (SP1 & SP2 & STK & FRM & _ & _ & Hg0 & Ht0).
  pose proof RDX as (HvX & HraX & HhX & HmX & H0X & H63X).
  pose proof RDY as (HvY & HraY & HhY & HmY & H0Y & H63Y).
  assert (R2 : YK11.getr regsT 2 = Z_to_bv 64 (sp1 - MRX_FRAME))
    by exact (eq_trans (RG 2 ltac:(unfold acallee_saved; lia) ltac:(lia)) H2).
  assert (HspT : spZ regsT = sp1 + -144)
    by (unfold spZ; rewrite R2; rewrite unsigned_lit_small; [unfold MRX_FRAME; lia | unfold MRX_FRAME; lia]).
  assert (R3 : YK11.getr regsT 3 = w64 (as_gp B)).
  { rewrite <- Hg0. exact (eq_trans (eq_trans (RG 3 ltac:(unfold acallee_saved; lia) ltac:(lia)) H3) eq_refl). }
  assert (R4 : YK11.getr regsT 4 = w64 (as_tp B)).
  { rewrite <- Ht0. exact (eq_trans (eq_trans (RG 4 ltac:(unfold acallee_saved; lia) ltac:(lia)) H4) eq_refl). }
  assert (SX : src_ok segs Wc regsT memT x N)
    by (intros a Ha; split; [exact (HvX a Ha) | rewrite HspT; unfold ESTACK; lia]).
  assert (SY : src_ok segs Wc regsT memT y N)
    by (intros a Ha; split; [exact (HvY a Ha) | rewrite HspT; unfold ESTACK; lia]).
  assert (BX : forall a, x <= a < x + N -> ~ (sp1 + -144 - 2 * ESTACK <= a < sp1 + -144))
    by (intros a Ha; unfold ESTACK; lia).
  assert (BY : forall a, y <= a < y + N -> ~ (sp1 + -144 - 2 * ESTACK <= a < sp1 + -144))
    by (intros a Ha; unfold ESTACK; lia).
  eapply SRr_bind.
  { exact (mrx_bcmp_gx B LAWS _ (HBCMP fx) Wc regsT memT MRX_STK sp1 [] lyc Sc W memc mdc [] lyc Sc mdT 0 x y N
      (-144) raw HJ R10 R11 R12 HN H0X H63X H0Y H63Y HspT eq_refl ltac:(lia)
      ltac:(rewrite STK; unfold ESTACK; lia) R3 R4 R1 HRAW SX SY BX BY HmX HmY HraX (fun _ => HhX) HraY
      (fun _ => HhY)). }
  cbv beta. intros W2 c2 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & Hiff & Hview & _).
  apply (KK regs3 mem3 md3); [|exact Hiff].
  apply (desk_mid_step P P regsT memT mdT regs3 mem3 md3 MID HPM (fun a h => h) HP3); [|exact HJ3].
  intros a Ha Hw _. apply Hview; [exact Ha|]. unfold desk_cwin in Hw. unfold ESTACK. lia.
Qed.

(* ---- the memcpy ---- *)

Definition desk_Pcpy (a : Z) : Prop := TA_M + 4 <= a < TA_M + 10.
Definition desk_Pall (a : Z) : Prop := TA_M <= a < TA_M + 10.

Lemma desk_memcpy : forall (regsT : bvmap 5 word) (memT : word -> option byte) (mdT : Model) (raw : word)
    (Q : world segs -> config -> Prop),
  desk_mid (fun _ => False) regsT memT mdT ->
  YK11.getr regsT 10 = w64 (TA_M + 4) -> YK11.getr regsT 11 = w64 (fa + 6) -> YK11.getr regsT 12 = w64 6 ->
  decode_rd_ok Wc memT (fa + 6) 6 -> decode_rd_ok Wc memT (TA_M + 4) 6 ->
  YK11.getr regsT 1 = raw -> YK0s.ret_ok raw ->
  (forall regs3 mem3 md3, desk_mid desk_Pcpy regs3 mem3 md3 ->
     (forall i, 0 <= i < 6 -> aview segs (w_H Wc) mem3 (TA_M + 4 + i) = aview segs (w_H Wc) memT (fa + 6 + i)) ->
     SRr segs Wc (mkCfg (@YK11.mkst fx regs3 raw mem3 (YK11.seg_rom segs)) md3) Q) ->
  SRr segs Wc (mkCfg (@YK11.mkst fx regsT (Z_to_bv 64 (transport_sigma TS___asan_memcpy)) memT
    (YK11.seg_rom segs)) mdT) Q.
Proof.
  intros regsT memT mdT raw Q MID R10 R11 R12 RDX RDD R1 HRAW KK.
  pose proof MID as (HJ & (RG & RG19) & KV & SPL).
  pose proof desk_sp as (SP1 & SP2 & STK & FRM & _ & _ & Hg0 & Ht0).
  pose proof desk_fpl as (F0 & FP & F63 & F30).
  pose proof RDX as (HvX & HraX & HhX & HmX & H0X & H63X).
  pose proof RDD as (HvD & HraD & HhD & HmD & H0D & H63D).
  assert (R2 : YK11.getr regsT 2 = Z_to_bv 64 (sp1 - MRX_FRAME))
    by exact (eq_trans (RG 2 ltac:(unfold acallee_saved; lia) ltac:(lia)) H2).
  assert (HspT : spZ regsT = sp1 + -144)
    by (unfold spZ; rewrite R2; rewrite unsigned_lit_small; [unfold MRX_FRAME; lia | unfold MRX_FRAME; lia]).
  assert (R3 : YK11.getr regsT 3 = w64 (as_gp B)).
  { rewrite <- Hg0. exact (eq_trans (RG 3 ltac:(unfold acallee_saved; lia) ltac:(lia)) H3). }
  assert (R4 : YK11.getr regsT 4 = w64 (as_tp B)).
  { rewrite <- Ht0. exact (eq_trans (RG 4 ltac:(unfold acallee_saved; lia) ltac:(lia)) H4). }
  assert (SX : src_ok segs Wc regsT memT (fa + 6) 6)
    by (intros a Ha; split; [exact (HvX a Ha) | rewrite HspT; unfold ESTACK; lia]).
  assert (DIS : TA_M + 4 + 6 <= fa + 6 \/ fa + 6 + 6 <= TA_M + 4).
  { destruct (Z_le_gt_dec (TA_M + 10) (fa + 6)) as [Hl|Hl]; [left; lia|].
    destruct (Z_le_gt_dec (fa + 12) (TA_M + 4)) as [Hr|Hr]; [right; lia|].
    exfalso. apply (desk_apart_M (Z.max (TA_M + 4) (fa + 6))); lia. }
  eapply SRr_bind.
  { apply (@gx_intrin_at fx rc tfib_sink_head segs B LAWS transport_segs_low OCpy
      (transport_sigma TS___asan_memcpy) (HMCPY fx) TG.G_HARNESS Wc regsT memT MRX_STK sp1 [] lyc Sc W memc mdc []
      lyc Sc mdT 0 (TA_M + 4) (fa + 6) 6 (-144) raw HGX G_HARNESS_rw HJ R10 R11 R12).
    - lia.
    - lia.
    - lia.
    - exact HspT.
    - reflexivity.
    - lia.
    - rewrite STK. unfold ESTACK. lia.
    - exact R3.
    - exact R4.
    - exact R1.
    - exact HRAW.
    - rewrite HspT. eapply (transport_twr_ok_g_intro segs B LAWS); [exact HJ|].
      intros a Ha. right. apply desk_inG. unfold TW.SZ_M, TA_M in *. lia.
    - exact HmD.
    - exact HraD.
    - intros _. exact HhD.
    - split; [lia|]. split; [lia|]. split; [exact SX|]. split; [exact DIS|].
      split; [exact HmX|]. split; [exact HraX | intros _; exact HhX]. }
  cbv beta. intros W2 c2 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & _ & Hset & Heff & _).
  apply (KK regs3 mem3 md3); [|exact Hset].
  apply (desk_mid_step (fun _ => False) desk_Pcpy regsT memT mdT regs3 mem3 md3 MID
    ltac:(intros a Ha; unfold desk_Pcpy in Ha; lia)
    ltac:(intros a Ha; cbv beta in Ha; destruct Ha) HP3); [|exact HJ3].
  intros a Ha Hw HP'. apply Heff; [exact Ha | unfold desk_Pcpy in HP'; lia |].
  unfold desk_cwin in Hw. unfold ESTACK. lia.
Qed.

(* ---- the world after the memcpy and the store ---- *)

Lemma desk_src_len : length (EPI.mrx_src fr) = 6%nat.
Proof.
  pose proof desk_fpl as (_ & _ & _ & F30). unfold EPI.mrx_src. apply TWL.length_sub; unfold mlen in F30; lia.
Qed.

Lemma desk_world2 : forall (rdF : Z -> option Z),
  (forall i, 0 <= i < 6 ->
     rdF (TA_M + 4 + i) = Some (bv_unsigned (nth (Z.to_nat i) (EPI.mrx_src fr) (Z_to_bv 8 0)))) ->
  (forall j, (j < 4)%nat -> rdF (TA_M + 0 + Z.of_nat j) = Some (YO0f.le_byte 1 4 j)) ->
  (forall x, tw_in TMAP_A x -> ~ (TA_M <= x < TA_M + 4) -> ~ (TA_M + 4 <= x < TA_M + 10) ->
     rdF x = aview segs (w_H Wc) mem2 x) ->
  tw_at TMAP_A rdF (TW.set_M_desk_known (TW.set_M_desk Bwc (EPI.mrx_src fr)) 1).
Proof.
  intros rdF VD VK HK.
  assert (SM : TW.SZ_M = 1648) by reflexivity.
  pose proof desk_src_len as LS.
  unfold TW.set_M_desk_known, TW.set_M_desk, TW.A_M_desk_known, TW.A_M_desk.
  pose proof (mrx_tw_start rdF (aview segs (w_H Wc) mem2) Bwc HTW) as HW0.
  pose proof (mrx_tw_span rdF (aview segs (w_H Wc) mem2) _ Bwc TW.OFF_M TA_M TW.SZ_M 4 (TW.OFF_M + 4)
    (EPI.mrx_src fr) HW0 TMAP_A_M ltac:(lia) ltac:(lia) ltac:(rewrite LS; lia) ltac:(rewrite LS; exact VD)) as HW1.
  rewrite LS in HW1.
  pose proof (mrx_tw_step rdF (aview segs (w_H Wc) mem2) _ _ TW.OFF_M TA_M TW.SZ_M 0 (TW.OFF_M + 0) 4 1 HW1
    TMAP_A_M ltac:(lia) ltac:(lia) ltac:(lia) VK) as HW2.
  apply (mrx_tw_end rdF (aview segs (w_H Wc) mem2) _ _ HW2).
  intros x Hx HP. mrx_unP HP. apply HK; [exact Hx | lia | lia].
Qed.

(* ---- the phases ---- *)

(* After the bcmp with M.desk (0x84b2c, bnez a0): a0 <> 0 returns 0; a0 = 0 goes to BODY. *)
Lemma desk_pA : forall regs m md, desk_mid (fun _ => False) regs m md ->
  TW.M_desk_known Bwc <> 0 ->
  (YK11.getr regs 10 = w64 0 <-> TC.beq_bytes (EPI.mrx_src fr) (TW.M_desk Bwc) = true) ->
  SRr segs Wc (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + 14536)) m (YK11.seg_rom segs)) md) IPOST.
Proof.
  intros regs m md MID HK IFF.
  pose proof MID as (HJ & RG & KV & SPL).
  destruct desk_vals as (_ & _ & _ & PEPI & PBODY).
  pose proof desk_PM_false as HPM0.
  pose proof (desk_imgf regs) as HEI. pose proof (desk_agreef regs) as AG.
  pose proof (desk_entryf (w_H Wc) regs m 14536) as HS.
  assert (EEf : forall k (q : bv 5), Z.of_nat k = bv_unsigned q -> ew (desk_Ef regs) k = YK11.getr regs q)
    by (intros k q Hk; unfold desk_Ef; apply ew_Eimg_Ereg_nat; exact Hk).
  assert (SHOK : sh_ok segs DESK_Bx DESK_SH (desk_Ef regs) (mrestrict (w_H Wc) m))
    by (unfold sh_ok, DESK_SH; apply Forall_nil).
  pose proof (@paj_run_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
    as RUN.
  pose proof (@paj_run_to_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX
    0 []) as RUNTO.
  pose proof (paj_branch (fx := fx) (PI := PI_transport)) as BR.
  psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
  - (* a0 <> 0: the desk differs; a0 = 0 and the epilogue *)
    apply (proj1 (desk_br_ne (desk_Ef regs) regs EEf)) in Hc.
    assert (EB : TC.beq_bytes (EPI.mrx_src fr) (TW.M_desk Bwc) = false).
    { destruct (TC.beq_bytes (EPI.mrx_src fr) (TW.M_desk Bwc)) eqn:E; [|reflexivity].
      exfalso. apply Hc. apply IFF. reflexivity. }
    destruct (desk_m_ne _ _ _ _ _ HK EB HM) as [EBw Er].
    paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan 14088.
    { desk_awr0. }
    set (md' := with_vm_backing (m_vm_lazy md) mat md) in *. clearbody md'. clear mat.
    assert (HP : aregs_preserved regs (ms_regs ms))
      by (apply (aregs_preserved_of_st_ok segs (w_H Wc) (desk_Ef regs) _ ms regs [w64 SHADOW_OFF] HS AG);
          vm_compute; reflexivity).
    pose proof (desk_mid_step _ _ regs m md (ms_regs ms) (ms_mem ms) md' MID HPM0 (fun a h => h) HP
      (fun a Ha _ _ => desk_frame_kept _ _ _ _ HFr eq_refl a Ha) HJ) as MID'.
    desk_reg HS (Z_to_bv 5 10) (w64 0) R10 ltac:(reflexivity).
    pmkst HS. rewrite PEPI.
    exact (desk_exit_epi (ms_regs ms) (ms_mem ms) md' MID' R10 EBw Er).
  - (* a0 = 0: the desk matches; BODY *)
    assert (Hc' : YK11.getr regs 10 = w64 0).
    { destruct (bv_eqb (YK11.getr regs 10) (Z_to_bv 64 0)) eqn:Q.
      - exact (proj1 (desk_eqb0 _) Q).
      - exfalso. assert (N : YK11.getr regs 10 <> w64 0)
          by (intros Z0; apply (proj2 (desk_eqb0 _)) in Z0; congruence).
        apply (proj2 (desk_br_ne (desk_Ef regs) regs EEf)) in N. rewrite N in Hc. discriminate Hc. }
    pose proof (desk_m_eq _ _ _ _ _ HK (proj1 IFF Hc') HM) as HMK.
    paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan 14604.
    { desk_awr0. }
    set (md' := with_vm_backing (m_vm_lazy md) mat md) in *. clearbody md'. clear mat.
    assert (HP : aregs_preserved regs (ms_regs ms))
      by (apply (aregs_preserved_of_st_ok segs (w_H Wc) (desk_Ef regs) _ ms regs [w64 SHADOW_OFF] HS AG);
          vm_compute; reflexivity).
    pose proof (desk_mid_step _ _ regs m md (ms_regs ms) (ms_mem ms) md' MID HPM0 (fun a h => h) HP
      (fun a Ha _ _ => desk_frame_kept _ _ _ _ HFr eq_refl a Ha) HJ) as MID'.
    pmkst HS. rewrite PBODY.
    pose proof MID' as (_ & _ & KV' & _).
    exact (desk_exit_body _ (ms_regs ms) (ms_mem ms) md' Bwc MID' HPM0 (desk_tw_kept _ KV') HMK).
Qed.

(* After the bcmp with SPEC_OUI (0x84b54, bnez a0): a0 <> 0 returns 0; a0 = 0 memcpies and stores. *)
Lemma desk_pB : forall regs m md, desk_mid (fun _ => False) regs m md ->
  TW.M_desk_known Bwc = 0 ->
  ((EPI.mrx_fc fr =? TC.SPEC_CMD_E0) || (EPI.mrx_fc fr =? TC.SPEC_CMD_E1))%bool = true ->
  (YK11.getr regs 10 = w64 0 <-> TC.beq_bytes (TW.sub (TI.tf_bytes fr) 6 3) TC.SPEC_OUI = true) ->
  SRr segs Wc (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + 14576)) m (YK11.seg_rom segs)) md) IPOST.
Proof.
  intros regs m md MID HK HCMD IFF.
  pose proof MID as (HJ & RG & KV & SPL).
  pose proof RG as (RGS & RG19).
  destruct desk_vals as (V8 & V48 & _ & PEPI & PBODY).
  pose proof desk_sp as (SP1 & SP2 & STK & FRM & _).
  pose proof desk_fpl as (F0 & FP & F63 & F30).
  pose proof desk_PM_false as HPM0.
  assert (EOU : firstn 3 (EPI.mrx_src fr) = TW.sub (TI.tf_bytes fr) 6 3)
    by (unfold EPI.mrx_src; apply desk_sub_firstn; lia).
  pose proof (desk_imgf regs) as HEI. pose proof (desk_agreef regs) as AG.
  pose proof (desk_entryf (w_H Wc) regs m 14576) as HS.
  assert (EEf : forall k (q : bv 5), Z.of_nat k = bv_unsigned q -> ew (desk_Ef regs) k = YK11.getr regs q)
    by (intros k q Hk; unfold desk_Ef; apply ew_Eimg_Ereg_nat; exact Hk).
  assert (SHOK : sh_ok segs DESK_Bx DESK_SH (desk_Ef regs) (mrestrict (w_H Wc) m))
    by (unfold sh_ok, DESK_SH; apply Forall_nil).
  pose proof (@paj_run_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
    as RUN.
  pose proof (@paj_run_to_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX
    0 []) as RUNTO.
  pose proof (paj_branch (fx := fx) (PI := PI_transport)) as BR.
  psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
  - (* a0 <> 0: the OUI differs; a0 = 0 and the epilogue *)
    apply (proj1 (desk_br_ne (desk_Ef regs) regs EEf)) in Hc.
    assert (EO : TC.beq_bytes (TW.sub (TI.tf_bytes fr) 6 3) TC.SPEC_OUI = false).
    { destruct (TC.beq_bytes (TW.sub (TI.tf_bytes fr) 6 3) TC.SPEC_OUI) eqn:E; [|reflexivity].
      exfalso. apply Hc. apply IFF. reflexivity. }
    destruct (desk_m_oui_no _ _ _ _ _ HK HCMD ltac:(rewrite EOU; exact EO) HM) as [EBw Er].
    paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan 14088.
    { desk_awr0. }
    set (md' := with_vm_backing (m_vm_lazy md) mat md) in *. clearbody md'. clear mat.
    assert (HP : aregs_preserved regs (ms_regs ms))
      by (apply (aregs_preserved_of_st_ok segs (w_H Wc) (desk_Ef regs) _ ms regs [w64 SHADOW_OFF] HS AG);
          vm_compute; reflexivity).
    pose proof (desk_mid_step _ _ regs m md (ms_regs ms) (ms_mem ms) md' MID HPM0 (fun a h => h) HP
      (fun a Ha _ _ => desk_frame_kept _ _ _ _ HFr eq_refl a Ha) HJ) as MID'.
    desk_reg HS (Z_to_bv 5 10) (w64 0) R10 ltac:(reflexivity).
    pmkst HS. rewrite PEPI.
    exact (desk_exit_epi (ms_regs ms) (ms_mem ms) md' MID' R10 EBw Er).
  - (* a0 = 0: the OUI matches; the memcpy, the store, BODY *)
    assert (Hc' : YK11.getr regs 10 = w64 0).
    { destruct (bv_eqb (YK11.getr regs 10) (Z_to_bv 64 0)) eqn:Q.
      - exact (proj1 (desk_eqb0 _) Q).
      - exfalso. assert (N : YK11.getr regs 10 <> w64 0)
          by (intros Z0; apply (proj2 (desk_eqb0 _)) in Z0; congruence).
        apply (proj2 (desk_br_ne (desk_Ef regs) regs EEf)) in N. rewrite N in Hc. discriminate Hc. }
    pose proof (desk_m_oui_yes _ _ _ _ _ HK HCMD ltac:(rewrite EOU; exact (proj1 IFF Hc')) HM) as HMK.
    (* 0x84b58 - 0x84b64: a0 = &M.desk, a1 = fa + 6, a2 = 6, the call *)
    paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
    { desk_awr0. }
    set (md1 := with_vm_backing (m_vm_lazy md) mat md) in *. clearbody md1. clear mat.
    assert (HP1 : aregs_preserved regs (ms_regs ms))
      by (apply (aregs_preserved_of_st_ok segs (w_H Wc) (desk_Ef regs) _ ms regs [w64 SHADOW_OFF] HS AG);
          vm_compute; reflexivity).
    pose proof (desk_mid_step _ _ regs m md (ms_regs ms) (ms_mem ms) md1 MID HPM0 (fun a h => h) HP1
      (fun a Ha _ _ => desk_frame_kept _ _ _ _ HFr eq_refl a Ha) HJ) as MID1.
    pose proof MID1 as (HJ1 & (RG1 & RG191) & KV1 & SPL1).
    desk_reg HS (Z_to_bv 5 10) (w64 (TA_M + 4)) Ra0
      ltac:(apply (desk_sv_off (desk_Ef regs) 19 4 TA_M);
            [rewrite (EEf 19%nat (Z_to_bv 5 19) eq_refl); exact RG19 | unfold TA_M; lia]).
    desk_reg HS (Z_to_bv 5 11) (w64 (fa + 6)) Ra1
      ltac:(apply (desk_sv_off0 (desk_Ef regs) 9 (fa + 6));
            [rewrite (EEf 9%nat (Z_to_bv 5 9) eq_refl);
             exact (eq_trans (RGS 9 ltac:(unfold acallee_saved; lia) ltac:(lia)) H9) | lia]).
    desk_reg HS (Z_to_bv 5 12) (w64 6) Ra2 ltac:(reflexivity).
    desk_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 14596)) Rra ltac:(apply codeptr_val; exact HEI).
    pmkst HS.
    lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
      change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (transport_sigma TS___asan_memcpy)) mm rom) mdx) Q) end.
    pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ1) as HAR1.
    apply (desk_memcpy (ms_regs ms) (ms_mem ms) md1 (Z_to_bv 64 (BASE + 14596)) _ MID1 Ra0 Ra1 Ra2
      (desk_rd_frame _ (ms_mem ms) (fa + 6) 6 HPM0 KV1 eq_refl ltac:(lia) ltac:(lia))
      (desk_rd_m _ _ (ms_mem ms) _ Bwc HAR1 (desk_tw_kept _ KV1)) Rra
      (ret_ok_codeptr_v (PI := PI_transport) 14596 ltac:(lia) eq_refl)).
    intros regs3 mem3 md3 MID3 HCPY.
    (* 0x84b68 - 0x84b6c: a0 = 1, the store of M.desk_known, then BODY *)
    assert (VD3 : forall i, 0 <= i < 6 -> aview segs (w_H Wc) mem3 (TA_M + 4 + i) =
      Some (bv_unsigned (nth (Z.to_nat i) (EPI.mrx_src fr) (Z_to_bv 8 0)))).
    { intros i Hi. rewrite (HCPY i Hi).
      replace (fa + 6 + i) with (fa + (6 + i)) by lia.
      rewrite (desk_frame_view _ _ HPM0 KV1 (6 + i) ltac:(unfold mlen in *; lia)).
      unfold EPI.mrx_src.
      rewrite (tw_nth_sub (TI.tf_bytes fr) 6 6 (Z.to_nat i) (Z_to_bv 8 0)) by (unfold mlen in F30; lia).
      do 3 f_equal. lia. }
    pose proof MID3 as (HJ3 & (RG3 & RG193) & KV3 & SPL3).
    assert (HPMc : desk_PM desk_Pcpy) by (intros a Ha; unfold desk_Pcpy in Ha; lia).
    pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as HAR3.
    pose proof (desk_imgf regs3) as HEI3. pose proof (desk_agreef regs3) as AG3.
    pose proof (desk_entryw lyc Sc Wc regs3 mem3 _ HAR3 RG193) as HS3.
    assert (U19 : bv_unsigned (ew (desk_Ef regs3) 19) = TA_M).
    { unfold desk_Ef. rewrite (ew_Eimg_Ereg_nat regs3 _ 19 (Z_to_bv 5 19) eq_refl), RG193.
      apply unsigned_lit_small. unfold TA_M. lia. }
    assert (SHOK3 : sh_ok segs DESK_Bx DESK_SH (desk_Ef regs3) (mrestrict (w_H Wc) mem3))
      by (unfold sh_ok, DESK_SH; apply Forall_nil).
    clear HS. clear dependent ms.
    rename HS3 into HS.
    paj_run_to_tok RUNTO HS HJ3 SHOK3 YC4b.Bspan 14604.
    { desk_awr_m U19. }
    set (mdF := with_vm_backing (m_vm_lazy md3) mat md3) in *. clearbody mdF. clear mat.
    assert (HPF : aregs_preserved regs3 (ms_regs ms))
      by (apply (aregs_preserved_of_st_ok segs (w_H Wc) (desk_Ef regs3) _ ms regs3 [w64 SHADOW_OFF] HS AG3);
          vm_compute; reflexivity).
    assert (KEEPF : forall a, 0 <= a < 2 ^ 64 -> ~ (TA_M <= a < TA_M + 4) ->
      aview segs (w_H Wc) (ms_mem ms) a = aview segs (w_H Wc) mem3 a).
    { intros a Ha Hn.
      apply (kept_of_frame _ _ (w_H Wc) mem3 (ms_mem ms) (fun x => TA_M <= x < TA_M + 4) HFr);
        [|exact Ha | exact Hn].
      intros b wlo whi x Hin Hx. desk_win Hin Hx ltac:(rewrite ?U19 in Hx; lia). }
    pose proof (desk_mid_step desk_Pcpy desk_Pall regs3 mem3 md3 (ms_regs ms) (ms_mem ms) mdF MID3
      ltac:(intros a Ha; unfold desk_Pall in Ha; lia)
      ltac:(intros a Ha; unfold desk_Pcpy in Ha; unfold desk_Pall; lia) HPF
      ltac:(intros a Ha _ Hn; apply KEEPF; [exact Ha | unfold desk_Pall in Hn; lia]) HJ3) as MIDF.
    assert (HPMa : desk_PM desk_Pall) by (intros a Ha; unfold desk_Pall in Ha; lia).
    (* the four bytes of 1 the store left *)
    pose proof (st_ok_pi_region_nth _ _ (restrict (w_H Wc) ms) 0 _ HS eq_refl) as RGN.
    cbn [ms_mem restrict] in RGN. destruct RGN as (_ & _ & _ & HCH).
    cbn [YP09.r_base YP09.r_chunks base_val] in HCH.
    rewrite U19 in HCH.
    pose proof (desk_Forall_nth _ _ 0%nat _ HCH eq_refl) as HC1.
    pose proof (mrx_chunk_rd (desk_Ef regs3) (w_H Wc) (ms_mem ms) TA_M 0 4 (SLit 1) 1 HC1 eq_refl ltac:(cbn; lia)) as VK.
    cbn [N.to_nat] in VK.
    (* the six bytes the memcpy left, still there *)
    assert (VD : forall i, 0 <= i < 6 -> aview segs (w_H Wc) (ms_mem ms) (TA_M + 4 + i) =
      Some (bv_unsigned (nth (Z.to_nat i) (EPI.mrx_src fr) (Z_to_bv 8 0)))).
    { intros i Hi. rewrite (KEEPF (TA_M + 4 + i) ltac:(unfold TA_M; lia) ltac:(lia)). exact (VD3 i Hi). }
    assert (HWF : tw_at TMAP_A (aview segs (w_H Wc) (ms_mem ms))
      (TW.set_M_desk_known (TW.set_M_desk Bwc (EPI.mrx_src fr)) 1)).
    { apply (desk_world2 _ VD VK).
      intros x Hx N1 N2. pose proof (TMAP_A_hull x Hx) as Hh.
      unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh.
      rewrite (KEEPF x ltac:(lia) N1).
      apply KV3; [lia | desk_lia | desk_lia | unfold desk_Pcpy; lia]. }
    pmkst HS. rewrite PBODY.
    exact (desk_exit_body desk_Pall (ms_regs ms) (ms_mem ms) mdF _ MIDF HPMa HWF HMK).
Qed.

(* The spill slot the first run wrote, read off the state's chunk, and the register invariant, at a state the run
   left (st_ok_pi) or at a call (st_ok). *)
Ltac desk_spill_of Ex Hh msx HS UspE DEN19 SPLn Hreg :=
  let RGN := fresh "RGN" in let HCH := fresh "HCH" in let HC1 := fresh "HC1" in let VSP := fresh "VSP" in
  pose proof Hreg as RGN;
  cbn [ms_mem restrict] in RGN; destruct RGN as (_ & _ & _ & HCH);
  cbn [YP09.r_base YP09.r_chunks base_val] in HCH; rewrite UspE in HCH;
  pose proof (desk_Forall_nth _ _ 0%nat _ HCH eq_refl) as HC1;
  pose proof (mrx_chunk_rd Ex Hh (ms_mem msx) (sp1 - 144) 8 8 (SOff 19 0) (mfb fr 18) HC1 DEN19
    ltac:(cbn; lia)) as VSP;
  cbn [N.to_nat] in VSP;
  assert (SPLn : mrx_spill Wc (ms_mem msx) sp1 8 fr 18);
  [ unfold mrx_spill, MRX_FRAME;
    apply (desk_rdword_of _ _ (mfb fr 18));
    [ pose proof (desk_mfb_range fr 18); lia
    | intros j Hj; exact (VSP j Hj) ]
  | clear HCH HC1 VSP ].

Ltac desk_spill HS UspE DEN19 SPLn :=
  lazymatch type of HS with
  | st_ok_pi _ _ ?Ex _ (restrict ?Hh ?msx) =>
      desk_spill_of Ex Hh msx HS UspE DEN19 SPLn (st_ok_pi_region_nth Ex _ (restrict Hh msx) 0 _ HS eq_refl)
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok ?sgx ?Ex ?ssx (restrict ?Hh ?msx) =>
      desk_spill_of Ex Hh msx HS UspE DEN19 SPLn (st_ok_region_nth Ex ssx (restrict Hh msx) 0 _ HS eq_refl)
  end.

Ltac desk_rgn_of msx KPn R19n RGn :=
  assert (RGn : desk_rg (ms_regs msx)) by
    (split; [intros q Hq Hq19; apply (KPn (Z_to_bv 5 q)); unfold DESK_KEEP; apply in_map;
             unfold acallee_saved in Hq; cbn [In]; lia | exact R19n]).

Ltac desk_rgn HS KPn R19n RGn :=
  lazymatch type of HS with
  | st_ok_pi _ _ _ _ (restrict _ ?msx) => desk_rgn_of msx KPn R19n RGn
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok _ _ _ (restrict _ ?msx) =>
      desk_rgn_of msx KPn R19n RGn
  end.

(* From the cut: run 1 (the spill, s3 = &M, M.desk_known), the branch, the two compares. *)
Lemma desk_walk : forall md2,
  @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS 0 [] MRX_STK sp1 [] lyc Sc W memc mdc [] lyc Sc Wc
    mem2 md2 0 ->
  SRr segs Wc (mkCfg (@YK11.mkst fx regs2 (Z_to_bv 64 (MRX_PC OFF_DESK)) mem2 (YK11.seg_rom segs)) md2) IPOST.
Proof using All.
  intros md2 HJ.
  destruct desk_vals as (V8 & V48 & PDESK & PEPI & PBODY).
  pose proof desk_sp as (SP1 & SP2 & STK & FRM & Hsp16 & _).
  pose proof desk_fpl as (F0 & FP & F63 & F30).
  pose proof desk_PM_false as HPM0.
  assert (Usp : spZ regs2 = sp1 - 144)
    by (unfold spZ; rewrite H2, FRM; apply unsigned_lit_small; lia).
  assert (Hsp16' : (sp1 - 144) mod 16 = 0)
    by (replace (sp1 - 144) with (sp1 + (-9) * 16) by lia; rewrite Z_mod_plus_full; exact Hsp16).
  pose proof HJ as (HSTK & _ & (memS & HJi & _) & _).
  rewrite !Z.add_0_r in HJi.
  pose proof HJi as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres0 & _).
  clear HJi memS.
  rewrite <- PDESK.
  set (E0 := desk_E regs2 Bwc).
  pose proof (desk_img regs2 Bwc) as HEI. fold E0 in HEI.
  assert (AG0 : env_agree 32 (Ereg regs2 [w64 SHADOW_OFF; Z_to_bv 64 (TW.u_at Bwc TW.A_M_desk_known 4)]) E0)
    by (unfold E0, desk_E; split;
        [intros k Hk; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (EE0 : forall k (q : bv 5), Z.of_nat k = bv_unsigned q -> ew E0 k = YK11.getr regs2 q)
    by (intros k q Hk; unfold E0, desk_E; apply ew_Eimg_Ereg_nat; exact Hk).
  assert (UspE : bv_unsigned (ew E0 2) = sp1 - 144)
    by (rewrite (EE0 2%nat (Z_to_bv 5 2) eq_refl); exact Usp).
  assert (E33 : ew E0 33 = Z_to_bv 64 (TW.u_at Bwc TW.A_M_desk_known 4))
    by (unfold E0, desk_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 1)).
  assert (UM : ew E0 249%nat = w64 TA_M).
  { unfold E0, desk_E. rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia).
    change (A_OBJ 8) with 249%nat in V8. rewrite V8. reflexivity. }
  assert (DEN19 : sv_denot E0 (SOff 19 0) = w64 (mfb fr 18))
    by (apply (desk_sv_off0 E0 19 (mfb fr 18));
        [rewrite (EE0 19%nat (Z_to_bv 5 19) eq_refl); exact H19
        | pose proof (desk_mfb_range fr 18); lia]).
  assert (RC : 0 <= mfb fr 28 < 256)
    by (pose proof (desk_mfb_range fr 28); lia).
  assert (FC : EPI.mrx_fc fr = mfb fr 28) by reflexivity.
  assert (R25 : ew E0 25%nat = w64 (mfb fr 28)).
  { rewrite (EE0 25%nat (Z_to_bv 5 25) eq_refl). pose proof HHR as (_ & _ & _ & _ & _ & S25 & _). exact S25. }
  pose proof (desk_entry0 Wc regs2 mem2 Bwc ltac:(intros a Ha; apply Hpres0; rewrite Usp in Ha; lia)
    ltac:(rewrite Usp; lia) ltac:(rewrite Usp; lia) ltac:(rewrite Usp; exact Hsp16') HTW) as HS.
  fold E0 in HS.
  assert (SHOK : sh_ok segs DESK_Bx DESK_SH E0 (mrestrict (w_H Wc) mem2))
    by (unfold sh_ok, DESK_SH; apply Forall_nil).
  pose proof (@paj_run_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
    as RUN.
  pose proof (@paj_run_to_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX
    0 []) as RUNTO.
  pose proof (paj_branch (fx := fx) (PI := PI_transport)) as BR.
  (* run 1, 0x84b08 .. 0x84b18: the spill, s3 = &M, M.desk_known *)
  paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
  { desk_awr_sp UspE. }
  set (md1 := with_vm_backing (m_vm_lazy md2) mat md2) in *. clearbody md1. clear mat.
  assert (KEEP1 : forall a, 0 <= a < 2 ^ 64 -> ~ desk_slot a ->
    aview segs (w_H Wc) (ms_mem ms) a = aview segs (w_H Wc) mem2 a).
  { intros a Ha Hn.
    apply (kept_of_frame _ _ (w_H Wc) mem2 (ms_mem ms) desk_slot HFr); [|exact Ha | exact Hn].
    intros b wlo whi x Hin Hx. desk_win Hin Hx ltac:(rewrite ?UspE in Hx; unfold desk_slot; desk_lia). }
  clear HF HFr HG.
  pose proof (regs_kept_of_st_ok segs E0 _ _ regs2
    [w64 SHADOW_OFF; Z_to_bv 64 (TW.u_at Bwc TW.A_M_desk_known 4)] DESK_KEEP HS AG0
    ltac:(vm_compute; reflexivity)) as KP1.
  desk_reg HS (Z_to_bv 5 19) (w64 TA_M) R191
    ltac:(apply (desk_sv_off0 E0 249%nat TA_M); [exact UM | unfold TA_M; lia]).
  desk_rgn HS KP1 R191 RG1.
  desk_spill HS UspE DEN19 SPL1.
  assert (MID1 : desk_mid (fun _ => False) (ms_regs ms) (ms_mem ms) md1).
  { split; [exact HJ|]. split; [exact RG1|].
    split; [intros a Ha _ Hs _; exact (KEEP1 a Ha Hs) | exact SPL1]. }
  clear KEEP1 SPL1 RG1 KP1 R191.
  (* the branch on M.desk_known *)
  psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
  - (* M.desk_known = 0: the cmd test *)
    rewrite (desk_br_known E0 Bwc E33) in Hc. apply Z.eqb_eq in Hc.
    paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
    { desk_awr_sp UspE. }
    set (md2' := with_vm_backing (m_vm_lazy md1) mat md1) in *. clearbody md2'. clear mat.
    pose proof (regs_kept_of_st_ok segs E0 _ _ regs2
      [w64 SHADOW_OFF; Z_to_bv 64 (TW.u_at Bwc TW.A_M_desk_known 4)] DESK_KEEP HS AG0
      ltac:(vm_compute; reflexivity)) as KP2.
    desk_reg HS (Z_to_bv 5 19) (w64 TA_M) R192
      ltac:(apply (desk_sv_off0 E0 249%nat TA_M); [exact UM | unfold TA_M; lia]).
    desk_rgn HS KP2 R192 RG2.
    desk_spill HS UspE DEN19 SPL2.
    pose proof (desk_mid_step2 _ _ _ _ _ _ _ _ MID1 HPM0 (fun a h => h) RG2 SPL2
      ltac:(intros a Ha Hw Hs _;
            apply (kept_of_frame _ _ (w_H Wc) _ _ desk_slot HFr);
            [ intros b wlo whi x Hin Hx; desk_win Hin Hx ltac:(rewrite ?UspE in Hx; unfold desk_slot; desk_lia)
            | exact Ha | exact Hs ]) HJ) as MID2.
    clear HF HFr HG. clear KP2 R192 RG2 SPL2.
    psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
    + (* the cmd is neither e0 nor e1: the epilogue *)
      rewrite (desk_br_cmd E0 (mfb fr 28) R25 RC) in Hc0. apply negb_true_iff in Hc0.
      destruct (desk_m_cmd _ _ _ _ _ Hc ltac:(rewrite FC; exact Hc0) HM) as [EBw Er].
      paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan 14088.
      { desk_awr_sp UspE. }
      set (md3 := with_vm_backing (m_vm_lazy md2') mat md2') in *. clearbody md3. clear mat.
      pose proof (regs_kept_of_st_ok segs E0 _ _ regs2
        [w64 SHADOW_OFF; Z_to_bv 64 (TW.u_at Bwc TW.A_M_desk_known 4)] DESK_KEEP HS AG0
        ltac:(vm_compute; reflexivity)) as KP3.
      desk_reg HS (Z_to_bv 5 19) (w64 TA_M) R193
        ltac:(apply (desk_sv_off0 E0 249%nat TA_M); [exact UM | unfold TA_M; lia]).
      desk_rgn HS KP3 R193 RG3.
      desk_spill HS UspE DEN19 SPL3.
      pose proof (desk_mid_step2 _ _ _ _ _ _ _ _ MID2 HPM0 (fun a h => h) RG3 SPL3
        ltac:(intros a Ha Hw Hs _;
              apply (kept_of_frame _ _ (w_H Wc) _ _ desk_slot HFr);
              [ intros b wlo whi x Hin Hx; desk_win Hin Hx ltac:(rewrite ?UspE in Hx; unfold desk_slot; desk_lia)
              | exact Ha | exact Hs ]) HJ) as MID3.
      clear HF HFr HG.
      desk_reg HS (Z_to_bv 5 10) (w64 0) R10 ltac:(reflexivity).
      pmkst HS. rewrite PEPI.
      exact (desk_exit_epi _ _ _ MID3 R10 EBw Er).
    + (* the cmd is e0 or e1: the OUI compare *)
      rewrite (desk_br_cmd E0 (mfb fr 28) R25 RC) in Hc0. apply negb_false_iff in Hc0.
      paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
      { desk_awr_sp UspE. }
      set (md3 := with_vm_backing (m_vm_lazy md2') mat md2') in *. clearbody md3. clear mat.
      pose proof (regs_kept_of_st_ok segs E0 _ _ regs2
        [w64 SHADOW_OFF; Z_to_bv 64 (TW.u_at Bwc TW.A_M_desk_known 4)] DESK_KEEP HS AG0
        ltac:(vm_compute; reflexivity)) as KP3.
      desk_reg HS (Z_to_bv 5 19) (w64 TA_M) R193
        ltac:(apply (desk_sv_off0 E0 249%nat TA_M); [exact UM | unfold TA_M; lia]).
      desk_rgn HS KP3 R193 RG3.
      desk_spill HS UspE DEN19 SPL3.
      pose proof (desk_mid_step2 _ _ _ _ _ _ _ _ MID2 HPM0 (fun a h => h) RG3 SPL3
        ltac:(intros a Ha Hw Hs _;
              apply (kept_of_frame _ _ (w_H Wc) _ _ desk_slot HFr);
              [ intros b wlo whi x Hin Hx; desk_win Hin Hx ltac:(rewrite ?UspE in Hx; unfold desk_slot; desk_lia)
              | exact Ha | exact Hs ]) HJ) as MID3.
      clear HF HFr HG.
      pose proof MID3 as (HJ3 & _ & KV3 & _).
      desk_reg HS (Z_to_bv 5 10) (w64 (fa + 6)) Ra0
        ltac:(apply (desk_sv_off0 E0 9%nat (fa + 6));
              [rewrite (EE0 9%nat (Z_to_bv 5 9) eq_refl); exact H9 | lia]).
      desk_reg HS (Z_to_bv 5 11) (w64 TRANS_SPEC_OUI) Ra1
        ltac:(apply (desk_sv_off0 E0 (A_OBJ 48) TRANS_SPEC_OUI);
              [unfold E0, desk_E; rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia); rewrite V48; reflexivity
              | unfold TRANS_SPEC_OUI; lia]).
      desk_reg HS (Z_to_bv 5 12) (w64 3) Ra2 ltac:(reflexivity).
      desk_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 14576)) Rra ltac:(apply codeptr_val; exact HEI).
      pmkst HS.
      lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
        change (SRr sg Wx (mkCfg (@YK11.mkst fx rg
          (Z_to_bv 64 (transport_sigma TS___interceptor_trampoline_bcmp)) mm rom) mdx) Q) end.
      pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as HAR3.
      apply (desk_bcmp _ _ _ _ (fa + 6) TRANS_SPEC_OUI 3
        (Z_to_bv 64 (BASE + 14576)) _ MID3 HPM0 Ra0 Ra1 Ra2 ltac:(lia)
        (trans_rd_ok_sub Wc _ (fa + 6) 6 (fa + 6) 3
          (desk_rd_frame _ _ (fa + 6) 6 HPM0 KV3 eq_refl ltac:(lia) ltac:(lia))
          ltac:(lia) ltac:(lia) ltac:(lia))
        (desk_rd_oui lyc Sc _ _ _ HAR3 HPM0 KV3)
        ltac:(lia) ltac:(left; unfold TRANS_SPEC_OUI; lia) Rra
        (ret_ok_codeptr_v (PI := PI_transport) 14576 ltac:(lia) eq_refl)).
      intros regs4 mem4 md4 MID4 IFF4.
      apply (desk_pB regs4 mem4 md4 MID4 Hc ltac:(rewrite <- FC in Hc0; exact Hc0)).
      exact (iff_trans IFF4
        (desk_cmp _ _ TRANS_SPEC_OUI 6 3 TC.SPEC_OUI HPM0 KV3 ltac:(lia) ltac:(lia) eq_refl
          (desk_oui_view _ _ HPM0 KV3))).
  - (* M.desk_known <> 0: the compare with M.desk *)
    rewrite (desk_br_known E0 Bwc E33) in Hc. apply Z.eqb_neq in Hc.
    paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
    { desk_awr_sp UspE. }
    set (md2' := with_vm_backing (m_vm_lazy md1) mat md1) in *. clearbody md2'. clear mat.
    pose proof (regs_kept_of_st_ok segs E0 _ _ regs2
      [w64 SHADOW_OFF; Z_to_bv 64 (TW.u_at Bwc TW.A_M_desk_known 4)] DESK_KEEP HS AG0
      ltac:(vm_compute; reflexivity)) as KP2.
    desk_reg HS (Z_to_bv 5 19) (w64 TA_M) R192
      ltac:(apply (desk_sv_off0 E0 249%nat TA_M); [exact UM | unfold TA_M; lia]).
    desk_rgn HS KP2 R192 RG2.
    desk_spill HS UspE DEN19 SPL2.
    pose proof (desk_mid_step2 _ _ _ _ _ _ _ _ MID1 HPM0 (fun a h => h) RG2 SPL2
      ltac:(intros a Ha Hw Hs _;
            apply (kept_of_frame _ _ (w_H Wc) _ _ desk_slot HFr);
            [ intros b wlo whi x Hin Hx; desk_win Hin Hx ltac:(rewrite ?UspE in Hx; unfold desk_slot; desk_lia)
            | exact Ha | exact Hs ]) HJ) as MID2.
    clear HF HFr HG.
    pose proof MID2 as (HJ2 & _ & KV2 & _).
    desk_reg HS (Z_to_bv 5 10) (w64 (fa + 6)) Ra0
      ltac:(apply (desk_sv_off0 E0 9%nat (fa + 6));
            [rewrite (EE0 9%nat (Z_to_bv 5 9) eq_refl); exact H9 | lia]).
    desk_reg HS (Z_to_bv 5 11) (w64 (TA_M + 4)) Ra1
      ltac:(apply (desk_sv_off E0 249%nat 4 TA_M); [exact UM | unfold TA_M; lia]).
    desk_reg HS (Z_to_bv 5 12) (w64 6) Ra2 ltac:(reflexivity).
    desk_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 14536)) Rra ltac:(apply codeptr_val; exact HEI).
    pmkst HS.
    lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
      change (SRr sg Wx (mkCfg (@YK11.mkst fx rg
        (Z_to_bv 64 (transport_sigma TS___interceptor_trampoline_bcmp)) mm rom) mdx) Q) end.
    pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HAR2.
    apply (desk_bcmp _ _ _ _ (fa + 6) (TA_M + 4) 6
      (Z_to_bv 64 (BASE + 14536)) _ MID2 HPM0 Ra0 Ra1 Ra2 ltac:(lia)
      (desk_rd_frame _ _ (fa + 6) 6 HPM0 KV2 eq_refl ltac:(lia) ltac:(lia))
      (desk_rd_m lyc Sc _ _ Bwc HAR2 (desk_tw_kept _ KV2))
      ltac:(lia) ltac:(left; unfold TA_M; lia) Rra
      (ret_ok_codeptr_v (PI := PI_transport) 14536 ltac:(lia) eq_refl)).
    intros regs4 mem4 md4 MID4 IFF4.
    apply (desk_pA regs4 mem4 md4 MID4 Hc).
    exact (iff_trans IFF4
      (desk_cmp _ _ (TA_M + 4) 6 6 (TW.M_desk Bwc) HPM0 KV2 ltac:(lia) ltac:(lia)
        ltac:(apply TWL.length_sub; [unfold TW.A_M_desk, TW.OFF_M; lia|];
              rewrite (tw_len TMAP_A _ Bwc HTW), Z2Nat.id by (unfold TW.W_LEN; lia);
              unfold TW.A_M_desk, TW.OFF_M, TW.W_LEN; lia)
        (desk_mdesk_view _ Bwc (desk_tw_kept _ KV2)))).
Qed.

End cut.

(* The segment DESK: from the cut DESK to the cuts EPI and BODY. *)
Lemma mrx_seg_desk :
  K (MRX_PC OFF_EPI) (R_EPI Bw' r) ->
  K (MRX_PC OFF_BODY) (R_BODY fr n sp1 lyc Sc Bw' r) ->
  K (MRX_PC OFF_DESK) (R_DESK fr n sp1 lyc Sc Bw' r).
Proof using All.
  intros KE KB Wc Bwc c HAT.
  destruct HAT as (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ & HFR & HPM & HMO2 & HSP & HGP & HTP & HSV & HTW & HR).
  destruct HR as (-> & -> & HFRS & HHDR & H8 & H9 & H19 & H20 & HHR & HM).
  exact (desk_walk Wc Bwc regs2 mem2 KE KB HMO2 HSV HTW HFRS HHDR HSP HGP HTP H8 H9 H19 H20 HHR HM md2 HJ).
Qed.

End seg.
