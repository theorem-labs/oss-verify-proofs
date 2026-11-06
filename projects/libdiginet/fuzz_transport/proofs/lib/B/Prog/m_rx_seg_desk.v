(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8v.v:120-122
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:518-584, 622-634 [Apache-2.0 OR MIT];
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:110-141, 221-225, 227-235, 264-270 [Apache-2.0 OR MIT], for
   libreac/fuzz_identity's ASan build (lib/A). The [Apache-2.0 OR MIT] text is used under Apache-2.0. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/LLVMFuzzerTestOneInput_L.v, with its module paths and module names changed; 987 of its 1030 lines of code are new or changed and 1037 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/m_rx_seg_head.v, with its module paths, module names and numbers changed; 1095 of its 1190 lines of code are new or changed and 935 lines of the source are left out. *)
(* m_rx_seg_desk: the segment DESK of the image-B walk of m_rx (statement lib/B/Prog/m_rx_cg.v, kit
   lib/B/Prog/m_rx_seg_kit.v): from the cut DESK (+0x098, 0x84cb4) to the cuts BODY (+0x100) and EPI (+0x030).
   The code (fuzz_transport.c:288-297; listing lib/B/Prog/DgnTransportBList.v, AF_m_rx = 0x397c):
     run 1    +0x098 .. +0x0a4  s1 = &M (A_OBJ 8 = TB_M), a0 = M.desk_known (the 4-byte signed load at M + 0, a chunk
                                of the world's bytes: tw_read_val), `beqz a0`;
     known    +0x0a8 .. +0x0b4  a1 = M + 4, a2 = 6, a0 = s0 = fa + 6, `jal` the bcmp wrapper (the kit's mrx_bcmp_gx):
                                M.desk against the source MAC; +0x0b8 `bnez a0` goes to +0x02c (a0 = 0) and EPI, else
                                +0x0bc `j` to BODY with the world unchanged;
     unknown  +0x0c0 .. +0x0cc  a0 = f.cmd (the byte at sp + 40 of the struct spec_read_frame filled: mrx_sf_cmd) &
                                0xfe; `bne a0, 0xe0` goes to EPI (UMR.mr_land254);
              +0x0d0 .. +0x0e0  a1 = SPEC_OUI (A_OBJ 51 = TRANS_SPEC_OUI), a2 = 3, a0 = s0, `jal` the bcmp wrapper;
                                +0x0e4 `bnez a0` goes to EPI;
              +0x0e8 .. +0x0f4  a0 = M + 4, a2 = 6, a1 = s0, `jal __asan_memcpy` (TransportGCg.v gx_intrin_at: the
                                destination [M + 4, M + 10) bytes of G, writable by TransportGRwB.v G_HARNESS_B_rw; the
                                source the frame's bytes [fa + 6, fa + 12), apart from it by mrx_apart);
              +0x0f8 .. +0x0fc  the 4-byte store of 1 at M + 0 (M.desk_known), then BODY at the world
                                set_M_desk_known (set_M_desk Bwc src) 1 (kit mrx_tw_span / mrx_tw_step).
   The ranges the calls read: the frame's from mrx_frs (trans_src_ok at the cut's state, DgnTransportBCg.v
   trans_src_ok_rd); M + 4's from the world and M's zero shadow, its shadow group [0x800b3db8, 0x800b3dc0) holding
   g_last_counter's last granule and guard bytes (trans_mrx_cells); SPEC_OUI's from trans_rom_view_rd, its shadow group
   [0x7fffc208, 0x7fffc210) from transport_cells (SPEC_OUI's 3, TRANS_STR_C24's 0 and 1) and trans_mrx_cells (the guard
   bytes). Every byte a step changes is a byte of the calls' windows below sp1 - 112 or of [M, M + 10), so the frame,
   the struct, the saved slots, the shadow band and the read-only bytes are kept (mrx_frs_view, mrx_sf_kept,
   mrx_saved_kept). The model is the kit's mrxb_desk (UMR.mr_beq_iff, UMR.mr_firstn3). The image-free lemmas and
   tactics (the desk_known branch, the bcmp-result branches, byte-list equality, desk_win, desk_hull) are image A's
   lib/A/Prog/m_rx_seg_desk.v (AD), used by name. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
DgnTransportBSyms DgnTransportBList DgnTransportBAddr DgnTransportBPa DgnTransportBImg DgnTransportBPaLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k AsanCells TransportGB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBCg TransportGRwB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB TImgB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
  m_set_cg m_wake_cg m_maybe_online_cg m_tick_cg spec_read_frame_cg host_offset_cg desk_named_cg check_state_data_cg
  m_rx_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TImg TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require m_rx_epi TContract.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require m_rx.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require m_rx_seg_kit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TransportGRunB TransportGFrameB CanKit
YC1g YC1h m_rx_seg_kit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import YC4b.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require m_rx_seg_desk.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.TransportGB.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
Module EPI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T.m_rx_epi.
Module TCt := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T.TContract.
Module UMR := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T.m_rx.
Module AK := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.m_rx_seg_kit.
Module BCells := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.AsanCells.
Module AD := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.m_rx_seg_desk.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* The symbolic states                                                 *)
(* ------------------------------------------------------------------ *)

(* Listing offsets (AF_m_rx = 14716): DESK +0x098 = 14868, the bcmp returns +0x0b8 = 14900 and +0x0e4 = 14944, the
   memcpy's return +0x0f8 = 14964, EPI +0x030 = 14764, BODY +0x100 = 14972. *)

(* The state at the cut: atoms 0 .. 31 the registers, 32 the shadow base, 33 the 4 bytes at M + 0 (M.desk_known,
   unsigned), 34 f.cmd. Regions: the byte f.cmd at sp + 40 and M.desk_known (object 8), both read only. *)
Definition desk_sp_region : YP09.region :=
  YP09.mkRegion (Some 2%nat) 40 41 0 0 [YP09.mkChunk 40 (YP09.CVal 1 (SOff 34 0))].
Definition desk_m_region : YP09.region :=
  YP09.mkRegion (Some (A_OBJ 8)) 0 4 0 0 [YP09.mkChunk 0 (YP09.CVal 4 (SOff 33 0))].
Definition desk_facts0 : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
           (33%nat, mkAF 0 (2 ^ 32 - 1) 0); (34%nat, mkAF 0 255 0); (A_OBJ 8, mkAF TB_M TB_M 5)] [] [].
Definition desk_ss0 : sstate := mkSS 14868 sr_atoms [desk_sp_region; desk_m_region] None desk_facts0.

(* A fresh state at offset pc with no region (the runs after a call touch no memory before the next call). *)
Definition desk_factsf : facts := mkFacts [(32%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] [].
Definition desk_ssf (pc : Z) : sstate := mkSS pc sr_atoms [] None desk_factsf.

(* The state at the memcpy's return (+0x0f8): M.desk_known writable, based on s1 (atom 9). *)
Definition desk_w_region : YP09.region := YP09.mkRegion (Some 9%nat) 0 4 0 4 [].
Definition desk_factsw : facts :=
  mkFacts [(9%nat, mkAF TB_M TB_M 5); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] [].
Definition desk_ssw : sstate := mkSS 14964 sr_atoms [desk_w_region] None desk_factsw.

Definition DESK_SH : list shent := [].
(* The callee-saved registers the runs from the cut's state keep (all but s1). *)
Definition DESK_KEEP : list (bv 5) := map (Z_to_bv 5) [2; 3; 4; 8; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27].
Definition DESK_Bx : sv := SOff 32 0.

Definition desk_E {rc : YM05.RunCeil} (regs : bvmap 5 word) (Bw : list byte) (c : Z) : env :=
  Eimg (PI := PI_transportb) (Ereg regs [w64 SHADOW_OFF; Z_to_bv 64 (TW.u_at Bw TW.A_M_desk_known 4); w64 c]).
Definition desk_Ef {rc : YM05.RunCeil} (regs : bvmap 5 word) : env :=
  Eimg (PI := PI_transportb) (Ereg regs [w64 SHADOW_OFF]).

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

(* The write rights of a run from a state whose regions are not writable. *)
Ltac desk_awr :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end;
  repeat (apply awr_ok_x_cons;
    [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; exfalso; lia |]);
  apply awr_ok_x_nil.

Lemma desk_inG : forall a, TB_M <= a < TB_M + TW.SZ_M -> inG TG.G_HARNESS_B a.
Proof.
intros a Ha. unfold inG. apply Exists_exists.
exists (TB_M, TW.SZ_M). split; [exact (TMAP_B_in_G _ _ _ TMAP_B_M) | unfold in_zr; cbn [fst snd]; lia].
Qed.

(* The write rights of the last run: M.desk_known, bytes of G. *)
Ltac desk_awr_m UME :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end;
  repeat (apply awr_ok_x_cons;
    [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
      rewrite UME in Ha; right; left; apply desk_inG; unfold TW.SZ_M; lia |]);
  apply awr_ok_x_nil.

(* ------------------------------------------------------------------ *)
(* Bytes and lists                                                     *)
(* ------------------------------------------------------------------ *)

(* The world's fields the segment reads and writes, at their numeral offsets. *)
Lemma desk_desk_eq : forall Bx, TW.M_desk Bx = TW.sub Bx (TW.OFF_M + 4) 6.
Proof. intros Bx. reflexivity. Qed.
Lemma desk_set_eq : forall Bx v, TW.set_M_desk_known (TW.set_M_desk Bx v) 1 =
  TW.upd (TW.upd Bx (TW.OFF_M + 4) v) (TW.OFF_M + 0) (TW.put 4 1).
Proof. intros Bx v. reflexivity. Qed.

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

(* A one-byte constant cell of the record, read at an AR state. *)
Lemma desk_const1 : forall {rc : YM05.RunCeil} (B : asyms) ly S (W : world tfibsegs) mem md a v s,
  @AR rc tfibsegs B ly S W mem md -> In (z1 (ANum a) v) (as_const B ly) -> 0 <= v < 256 -> a = s ->
  aview tfibsegs (w_H W) mem s = Some v.
Proof.
  intros rc B ly S W mem md a v s HAR Hin Hv <-.
  destruct HAR as (Mx & _).
  pose proof (proj1 (Forall_forall _ _) (am_const _ _ _ _ Mx) _ Hin) as Hc.
  unfold cell_holds in Hc. cbn [c_at c_w YG0f.c_val z1 c1 aeval] in Hc.
  specialize (Hc 0%nat ltac:(lia)). rewrite (AD.desk_le1 v Hv) in Hc.
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
  intros i Hi. unfold trans_in_ro_rd, TRANS_RO_RD, TRANS_RO_GLOBALS. apply Exists_exists.
  exists (TRANS_SPEC_OUI, 3). split; [cbn; tauto | unfold in_zr; cbn [fst snd]; lia].
Qed.

(* ------------------------------------------------------------------ *)
(* The model                                                           *)
(* ------------------------------------------------------------------ *)

(* mrxb_desk's five cases (fuzz_transport.c:288-297). *)
Lemma desk_m_eq : forall I fr n B B' r, TW.M_desk_known B <> 0 ->
  TC.beq_bytes (mrxb_src fr n) (TW.M_desk B) = true ->
  mrxb_desk I fr n B = Some (B', r) -> UMR.mr_k I fr n B = Some (B', r).
Proof.
  intros I fr n B B' r HK HE H. unfold mrxb_desk, TC.truth in H. cbv zeta in H.
  rewrite (proj2 (Z.eqb_neq _ _) HK) in H. cbn [negb] in H. rewrite HE in H. exact H.
Qed.
Lemma desk_m_ne : forall I fr n B B' r, TW.M_desk_known B <> 0 ->
  TC.beq_bytes (mrxb_src fr n) (TW.M_desk B) = false ->
  mrxb_desk I fr n B = Some (B', r) -> B' = B /\ r = 0.
Proof.
  intros I fr n B B' r HK HE H. unfold mrxb_desk, TC.truth in H. cbv zeta in H.
  rewrite (proj2 (Z.eqb_neq _ _) HK) in H. cbn [negb] in H. rewrite HE in H.
  destruct (mrx_some_inv _ _ _ _ _ _ H) as [E1 E2]. split; symmetry; assumption.
Qed.
Lemma desk_m_cmd : forall I fr n B B' r, TW.M_desk_known B = 0 ->
  ((DSpec.sf_cmd (mrx_f fr n) =? TC.SPEC_CMD_E0) || (DSpec.sf_cmd (mrx_f fr n) =? TC.SPEC_CMD_E1))%bool = false ->
  mrxb_desk I fr n B = Some (B', r) -> B' = B /\ r = 0.
Proof.
  intros I fr n B B' r HK HC H. unfold mrxb_desk, TC.truth in H. cbv zeta in H.
  rewrite HK in H. cbn [Z.eqb negb] in H. rewrite HC in H. cbn [negb] in H.
  destruct (mrx_some_inv _ _ _ _ _ _ H) as [E1 E2]. split; symmetry; assumption.
Qed.
Lemma desk_m_oui_no : forall I fr n B B' r, TW.M_desk_known B = 0 ->
  ((DSpec.sf_cmd (mrx_f fr n) =? TC.SPEC_CMD_E0) || (DSpec.sf_cmd (mrx_f fr n) =? TC.SPEC_CMD_E1))%bool = true ->
  TC.beq_bytes (firstn 3 (mrxb_src fr n)) TC.SPEC_OUI = false ->
  mrxb_desk I fr n B = Some (B', r) -> B' = B /\ r = 0.
Proof.
  intros I fr n B B' r HK HC HO H. unfold mrxb_desk, TC.truth in H. cbv zeta in H.
  rewrite HK in H. cbn [Z.eqb negb] in H. rewrite HC in H. cbn [negb] in H. rewrite HO in H. cbn [negb] in H.
  destruct (mrx_some_inv _ _ _ _ _ _ H) as [E1 E2]. split; symmetry; assumption.
Qed.
Lemma desk_m_oui_yes : forall I fr n B B' r, TW.M_desk_known B = 0 ->
  ((DSpec.sf_cmd (mrx_f fr n) =? TC.SPEC_CMD_E0) || (DSpec.sf_cmd (mrx_f fr n) =? TC.SPEC_CMD_E1))%bool = true ->
  TC.beq_bytes (firstn 3 (mrxb_src fr n)) TC.SPEC_OUI = true ->
  mrxb_desk I fr n B = Some (B', r) ->
  UMR.mr_k I fr n (TW.set_M_desk_known (TW.set_M_desk B (mrxb_src fr n)) 1) = Some (B', r).
Proof.
  intros I fr n B B' r HK HC HO H. unfold mrxb_desk, TC.truth in H. cbv zeta in H.
  rewrite HK in H. cbn [Z.eqb negb] in H. rewrite HC in H. cbn [negb] in H. rewrite HO in H. cbn [negb] in H.
  exact H.
Qed.

(* (cmd & 0xfe) <> 0xe0: the cmd is neither e0 nor e1. *)
Lemma desk_br_cmd : forall (E : env) c, ew E 34 = w64 c -> 0 <= c < 256 ->
  branch_taken BC_NE (sv_denot E (SAlu ALU_AND (SOff 34 0) (SLit 254))) (sv_denot E (SLit 224))
  = negb ((c =? 224) || (c =? 225))%bool.
Proof.
  intros E c Hc Hr. pose proof (UMR.mr_land254 c Hr) as He. pose proof (UMR.mr_land254r c Hr) as Hb.
  cbn [branch_taken].
  assert (D : sv_denot E (SAlu ALU_AND (SOff 34 0) (SLit 254)) = Z_to_bv 64 (Z.land c 254)).
  { change (sv_denot E (SAlu ALU_AND (SOff 34 0) (SLit 254)))
      with (alu64 ALU_AND (sv_denot E (SOff 34 0)) (sv_denot E (SLit 254))).
    rewrite (AD.desk_sv_off E 34 0 c Hc ltac:(lia)). rewrite Z.add_0_r. cbn [sv_denot].
    apply bv_eq. cbn [alu64 alu]. rewrite bv_and_unsigned, !Z_to_bv_unsigned.
    unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
    rewrite (Z.mod_small c) by lia. rewrite (Z.mod_small 254) by lia.
    rewrite (Z.mod_small (Z.land c 254)) by lia. reflexivity. }
  rewrite D. cbn [sv_denot]. rewrite EPI.mrxk_eqb by lia. rewrite He. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* The walk                                                            *)
(* ------------------------------------------------------------------ *)

Section seg. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis HCELLS : transport_cells B.
Hypothesis HMRX : trans_mrx_cells B.
Hypothesis HRO : trans_ro_rd_unowned B.
Hypothesis HNE : trans_rom_no_errno B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis MTL : ameter_laws MT.
Hypothesis HGX : gx_ok tfibsegs B TG.G_HARNESS_B.
Hypothesis HGNE : gx_noerrno B TG.G_HARNESS_B.
Hypothesis HSRF : forall fx' : YK11.FPState, @transport_spec_read_frame_cg fx' rc B MT (transportb_sigma TB_spec_read_frame).
Hypothesis HBCMP : forall fx' : YK11.FPState, @abcmp_realizes fx' rc tfibsegs B (transportb_sigma TB___interceptor_trampoline_bcmp).
Hypothesis HMCPY : forall fx' : YK11.FPState, @aintrin_realizes fx' rc tfibsegs B OCpy (transportb_sigma TB___asan_memcpy).
Hypothesis HHOFF : forall fx' : YK11.FPState, @transport_host_offset_cg fx' rc B MT (transportb_sigma TB_host_offset).
Hypothesis HMSET : forall fx' : YK11.FPState, @transport_m_set_cg fx' rc B MT (transportb_sigma TB_m_set).
Hypothesis HDN : forall fx' : YK11.FPState, @transport_desk_named_cg fx' rc B MT (transportb_sigma TB_desk_named).
Hypothesis HMW : forall fx' : YK11.FPState, @transport_m_wake_cg fx' rc B MT (transportb_sigma TB_m_wake).
Hypothesis HMO : forall fx' : YK11.FPState, @transport_m_maybe_online_cg fx' rc B MT (transportb_sigma TB_m_maybe_online).
Hypothesis HMT : forall fx' : YK11.FPState, @transport_m_tick_cg fx' rc B MT (transportb_sigma TB_m_tick).
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
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).
Local Abbreviation IPOST := (@mrx_ipost fx rc B MT sp1 regs0 lyc Sc W memc mdc Bw' r).
Local Abbreviation fa := (TI.tf_addr fr).

(* The image objects and the pcs: object 8 is M, object 51 SPEC_OUI; DESK, EPI and BODY at the listing's base. *)
Lemma desk_vals : VAL (A_OBJ 8) = TB_M /\ VAL (A_OBJ 51) = TRANS_SPEC_OUI /\
  BASE + 14868 = MRX_PC OFF_DESK /\ BASE + 14764 = MRX_PC OFF_EPI /\ BASE + 14972 = MRX_PC OFF_BODY.
Proof. vm_compute. repeat split. Qed.

Lemma desk_den_img : forall E k c w, img_env VAL A_LIM E -> (A_TEXT <= k < A_LIM)%nat -> VAL k + c = w ->
  sv_denot E (SOff k c) = Z_to_bv 64 w.
Proof. intros E k c w HE Hk Hw. cbn [sv_denot]. rewrite (HE k Hk). rewrite Hw. reflexivity. Qed.

Lemma desk_img : forall regs Bw c, img_env VAL A_LIM (desk_E regs Bw c).
Proof. intros regs Bw c. unfold desk_E. apply Eimg_env. Qed.
Lemma desk_imgf : forall regs, img_env VAL A_LIM (desk_Ef regs).
Proof. intros regs. unfold desk_Ef. apply Eimg_env. Qed.
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
  apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
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
Lemma desk_entry0 : forall (Wc : world segs) regs mem Bw c,
  2 ^ 46 <= spZ regs -> spZ regs <= 2 ^ 47 -> spZ regs mod 16 = 0 ->
  tw_at TMAP_B (aview segs (w_H Wc) mem) Bw ->
  val_mem segs (mrestrict (w_H Wc) mem) (spZ regs + 40) 1 c -> 0 <= c < 256 ->
  st_ok_pi segs VAL (desk_E regs Bw c) desk_ss0
    (restrict (w_H Wc) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + 14868)) mem (YK11.seg_rom segs))).
Proof.
  intros Wc regs mem Bw c Hsp1 Hsp2 Hsp16 Htw Hc Hcr.
  destruct desk_vals as (V8 & _ & _ & _ & _).
  set (E := desk_E regs Bw c).
  assert (EM : TB_M = 0x5dede0) by reflexivity.
  assert (E2 : ew E 2 = YK11.getr regs 2) by (unfold E, desk_E; apply ew_Eimg_Ereg_nat; reflexivity).
  assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
  assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF)
    by (unfold E, desk_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (E33 : ew E 33 = Z_to_bv 64 (TW.u_at Bw TW.A_M_desk_known 4))
    by (unfold E, desk_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
  assert (E34 : ew E 34 = Z_to_bv 64 c)
    by (unfold E, desk_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
  pose proof (TWL.u_at_range Bw TW.A_M_desk_known 4) as R33. change (8 * Z.of_nat 4) with 32 in R33.
  assert (U8 : bv_unsigned (ew E (A_OBJ 8)) = TB_M).
  { unfold E, desk_E. rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia). rewrite V8.
    apply unsigned_lit_small. lia. }
  assert (B8 : base_val E (Some (A_OBJ 8)) = TB_M) by exact U8.
  rewrite restrict_mkst_fx. unfold desk_ss0.
  apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    + unfold desk_sp_region, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite Usp. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val segs E _ (spZ regs) 40 1 (SOff 34 0) c);
        [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | lia | exact Hc].
    + unfold desk_m_region, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
      rewrite B8. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val segs E _ TB_M 0 4 (SOff 33 0) (TW.u_at Bw TW.A_M_desk_known 4));
        [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | lia |].
      exact (tw_read_val segs _ TMAP_B Bw TW.OFF_M TB_M TW.SZ_M 0 4 TMAP_B_ok Htw TMAP_B_M
        ltac:(lia) ltac:(unfold TW.SZ_M; lia)).
  - apply pairwise_disjoint_of_extents.
    unfold desk_sp_region, desk_m_region, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite B8. cbn [base_val]. rewrite Usp.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    repeat split; first [exact I | lia].
  - unfold desk_facts0, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, U8, E32, E33, E34, (unsigned_lit_small SHADOW_OFF) by (unfold SHADOW_OFF; lia).
    rewrite (unsigned_lit_small (TW.u_at Bw TW.A_M_desk_known 4)) by lia.
    rewrite (unsigned_lit_small c) by lia.
    change (2 ^ 4) with 16. change (2 ^ 5) with 32. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I;
      first [exact Hsp16 | lia | rewrite EM; reflexivity].
Qed.

(* The state at the memcpy's return: M.desk_known writable, based on s1. *)
Lemma desk_entryw : forall (Wc : world segs) regs mem, YK11.getr regs 9 = w64 TB_M ->
  st_ok_pi segs VAL (desk_Ef regs) desk_ssw
    (restrict (w_H Wc) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + 14964)) mem (YK11.seg_rom segs))).
Proof.
  intros Wc regs mem H9.
  assert (EM : TB_M = 0x5dede0) by reflexivity.
  set (E := desk_Ef regs).
  assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF)
    by (unfold E, desk_Ef; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (E9 : ew E 9 = w64 TB_M)
    by (unfold E, desk_Ef; rewrite (ew_Eimg_Ereg_nat regs _ 9 (Z_to_bv 5 9) eq_refl); exact H9).
  assert (U9 : bv_unsigned (ew E 9) = TB_M) by (rewrite E9; apply unsigned_lit_small; lia).
  rewrite restrict_mkst_fx. unfold desk_ssw.
  apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil].
    unfold desk_w_region, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U9. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS_B (TB_M + o) G_HARNESS_B_rw). apply desk_inG.
    unfold TW.SZ_M. lia.
  - cbn [pairwise_disjoint all_disjoint]. repeat split; exact I.
  - unfold desk_factsw, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U9, E32, (unsigned_lit_small SHADOW_OFF) by (unfold SHADOW_OFF; lia).
    change (2 ^ 5) with 32. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; first [lia | rewrite EM; reflexivity].
Qed.

(* The static facts. *)
Lemma desk_sp : 2 ^ 46 <= sp1 - MRX_STK /\ sp1 <= 2 ^ 47 /\ MRX_STK = 8384 /\ MRX_FRAME = 112 /\
  sp1 mod 16 = 0 /\ YK0s.ret_ok (YK11.getr regs0 1) /\
  YK11.getr regs0 3 = w64 (as_gp B) /\ YK11.getr regs0 4 = w64 (as_tp B).
Proof.
  pose proof HST as (_ & Hm16 & _ & H46 & H47 & Hra & _ & Hgp & Htp & _).
  split; [exact H46|]. split; [exact H47|]. split; [reflexivity|]. split; [reflexivity|].
  split; [exact Hm16|]. split; [exact Hra|]. split; [exact Hgp | exact Htp].
Qed.

(* No byte of M the segment writes is a frame byte. *)
Lemma desk_apart_M : forall a, TB_M <= a < TB_M + 10 -> ~ (fa <= a < fa + mlen fr).
Proof.
  intros a Ha. pose proof HST as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hap & _).
  intros Hf. apply (Hap a); [|exact Hf].
  unfold mrx_wr, twb_fld, TW.A_M_desk_known, TW.A_M_desk, TW.OFF_M.
  destruct (Z_lt_le_dec a (TB_M + 4)) as [Hl|Hl]; [left; lia | right; left; lia].
Qed.

Section cut.
Variable Wc : world segs.
Variable Bwc : list byte.
Variable ly2 : alayout.
Variable S2 : astate.
Variable regs2 : bvmap 5 word.
Variable mem2 : word -> option byte.
Hypothesis KE : K (MRX_PC OFF_EPI) (R_EPI Bw' r).
Hypothesis KB : K (MRX_PC OFF_BODY) (R_BODY B fr n sp1 Bw' r).
Hypothesis HFR2 : frames S2 = frames Sc.
Hypothesis HPM2 : Permutation (ablocks B ly2 S2) (ablocks B lyc Sc).
Hypothesis HMO2 : mo_le MT Sc S2 0.
Hypothesis H2 : YK11.getr regs2 2 = Z_to_bv 64 (sp1 - MRX_FRAME).
Hypothesis H3 : YK11.getr regs2 3 = YK11.getr regs0 3.
Hypothesis H4 : YK11.getr regs2 4 = YK11.getr regs0 4.
Hypothesis HHI : mrx_hi regs0 regs2.
Hypothesis HSV : mrx_saved Wc mem2 sp1 regs0.
Hypothesis HTW : tw_at TMAP_B (aview segs (w_H Wc) mem2) Bwc.
Hypothesis HCUR : mrx_cur B fr n sp1 ly2 S2 Wc mem2.
Hypothesis H8 : YK11.getr regs2 8 = w64 (fa + 6).
Hypothesis H18 : YK11.getr regs2 18 = w64 SHADOW_OFF.
Hypothesis HM : mrxb_desk timg_B fr n Bwc = Some (Bw', r).

(* The bytes a step may change: the calls' windows below the frame, and the bytes of M the memcpy and the store
   write. *)
Definition desk_cwin (a : Z) : Prop := sp1 - MRX_STK <= a < sp1 - MRX_FRAME.
Definition desk_KV (P : Z -> Prop) (m : word -> option byte) : Prop :=
  forall a, 0 <= a < 2 ^ 64 -> ~ desk_cwin a -> ~ P a ->
    aview segs (w_H Wc) m a = aview segs (w_H Wc) mem2 a.
Definition desk_PM (P : Z -> Prop) : Prop := forall a, P a -> TB_M <= a < TB_M + 10.
(* The callee-saved registers are the cut's, but s1 = &M. *)
Definition desk_rg (regs : bvmap 5 word) : Prop :=
  (forall q, acallee_saved q -> q <> 9 -> YK11.getr regs (Z_to_bv 5 q) = YK11.getr regs2 (Z_to_bv 5 q)) /\
  YK11.getr regs (Z_to_bv 5 9) = w64 TB_M.
(* A machine inside the segment. *)
Definition desk_mid (P : Z -> Prop) (regs : bvmap 5 word) (m : word -> option byte) (md : Model) : Prop :=
  @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS_B 0 [] MRX_STK sp1 [] lyc Sc W memc mdc [] ly2 S2 Wc
    m md 0 /\
  desk_rg regs /\ desk_KV P m.

Lemma desk_PM_false : desk_PM (fun _ => False).
Proof. intros a Ha. cbv beta in Ha. destruct Ha. Qed.

Ltac desk_lia := unfold desk_cwin, MRX_FRAME, ESTACK, TB_M in *; lia.

(* The frame: placed apart from the stack window, at least 30 bytes, n inside it. *)
Lemma desk_fpl : 0 < fa /\ (fa + mlen fr <= sp1 - MRX_STK \/ sp1 <= fa) /\ fa + mlen fr < 2 ^ 64 /\
  30 <= n <= mlen fr.
Proof.
  pose proof HST as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hfa0 & _ & Hfam & _ & Hpl & _).
  pose proof HCUR as ((Hn & Hok) & _).
  pose proof (mrx_ok_fields fr n (conj Hn Hok)) as (_ & _ & _ & H30 & _).
  split; [exact Hfa0|]. split; [exact Hpl|]. split; [exact Hfam | lia].
Qed.

Lemma desk_rg_of_keep : forall regs, (forall q, In q DESK_KEEP -> YK11.getr regs q = YK11.getr regs2 q) ->
  YK11.getr regs (Z_to_bv 5 9) = w64 TB_M -> desk_rg regs.
Proof.
  intros regs KP R9. split; [|exact R9].
  intros q Hq Hq9. apply KP. unfold DESK_KEEP. apply in_map. unfold acallee_saved in Hq. cbn [In]. lia.
Qed.

Lemma desk_mid_run : forall P regs m md regs' m' md',
  desk_mid P regs m md -> desk_rg regs' ->
  (forall a, 0 <= a < 2 ^ 64 -> aview segs (w_H Wc) m' a = aview segs (w_H Wc) m a) ->
  @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS_B 0 [] MRX_STK sp1 [] lyc Sc W memc mdc [] ly2 S2 Wc
    m' md' 0 ->
  desk_mid P regs' m' md'.
Proof.
  intros P regs m md regs' m' md' (_ & _ & KV) RG KEEP HJ'.
  split; [exact HJ'|]. split; [exact RG|].
  intros a Ha Hw Hp. rewrite (KEEP a Ha). exact (KV a Ha Hw Hp).
Qed.

Lemma desk_mid_step : forall P P' regs m md regs' m' md',
  desk_mid P regs m md -> desk_PM P' -> (forall a, P a -> P' a) ->
  aregs_preserved regs regs' ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ desk_cwin a -> ~ P' a ->
     aview segs (w_H Wc) m' a = aview segs (w_H Wc) m a) ->
  @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS_B 0 [] MRX_STK sp1 [] lyc Sc W memc mdc [] ly2 S2 Wc
    m' md' 0 ->
  desk_mid P' regs' m' md'.
Proof.
  intros P P' regs m md regs' m' md' (HJ & (RG & RG9) & KV) HPM HPP HP KEEP HJ'.
  split; [exact HJ'|]. split; [split|].
  - intros q Hq H9'. rewrite (HP q Hq). exact (RG q Hq H9').
  - rewrite (HP 9 ltac:(unfold acallee_saved; lia)). exact RG9.
  - intros a Ha Hw1 Hw3. rewrite (KEEP a Ha Hw1 Hw3).
    exact (KV a Ha Hw1 ltac:(intros HPa; exact (Hw3 (HPP a HPa)))).
Qed.

(* A run from a state with no region keeps every byte. *)
Lemma desk_frame_kept : forall (E : env) rs (m m' : word -> option byte),
  frame_of E rs (mrestrict (w_H Wc) m) (mrestrict (w_H Wc) m') -> windows rs = [] ->
  forall a, 0 <= a < 2 ^ 64 -> aview segs (w_H Wc) m' a = aview segs (w_H Wc) m a.
Proof.
  intros E rs m m' HF Hw a Ha.
  apply (YC4b.kept_of_frame E rs (w_H Wc) m m' (fun _ => False) HF); [|exact Ha | intros []].
  intros b wlo whi x Hin. rewrite Hw in Hin. destruct Hin.
Qed.

(* A run from a state whose regions are not writable keeps every byte. *)
Lemma desk_run_kept : forall (E : env) rs (m m' : word -> option byte),
  frame_of E rs (mrestrict (w_H Wc) m) (mrestrict (w_H Wc) m') ->
  (forall b wlo whi x, In (b, wlo, whi) (windows rs) -> base_val E b + wlo <= x < base_val E b + whi -> False) ->
  forall a, 0 <= a < 2 ^ 64 -> aview segs (w_H Wc) m' a = aview segs (w_H Wc) m a.
Proof.
  intros E rs m m' HF Hw a Ha.
  apply (YC4b.kept_of_frame E rs (w_H Wc) m m' (fun _ => False) HF); [|exact Ha | intros []].
  intros b wlo whi x Hin Hx. exact (Hw b wlo whi x Hin Hx).
Qed.

(* ---- what the view keeps ---- *)

Lemma desk_frs_kept : forall P m, desk_PM P -> desk_KV P m -> mrx_frs B fr ly2 S2 Wc m.
Proof.
  intros P m HPM KV. pose proof HCUR as (_ & HFRS & _).
  pose proof desk_fpl as (F0 & FP & F64 & Fn). pose proof desk_sp as (SP1 & SP2 & STK & FRM & _).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  apply (mrx_frs_view B fr ly2 S2 Wc Wc mem2 m HFRS).
  - intros a Ha. apply KV; [lia | desk_lia | intros HPa; exact (desk_apart_M a (HPM a HPa) Ha)].
  - intros s Hs. apply KV; [lia | desk_lia | intros HPa; pose proof (HPM s HPa); desk_lia].
  - intros a Ha. pose proof (trans_ro_rd_bounds a Ha) as Hl.
    apply KV; [lia | desk_lia | intros HPa; pose proof (HPM a HPa); desk_lia].
Qed.

Lemma desk_sf_kept : forall P m, desk_PM P -> desk_KV P m -> mrx_sf Wc m sp1 fr n.
Proof.
  intros P m HPM KV. pose proof HCUR as (_ & _ & HSF).
  pose proof desk_sp as (SP1 & SP2 & STK & FRM & _).
  apply (mrx_sf_kept Wc Wc mem2 m sp1 fr n HSF). intros a Ha.
  apply KV; [desk_lia | desk_lia | intros HPa; pose proof (HPM a HPa); desk_lia].
Qed.

Lemma desk_cur_kept : forall P m, desk_PM P -> desk_KV P m -> mrx_cur B fr n sp1 ly2 S2 Wc m.
Proof.
  intros P m HPM KV. pose proof HCUR as (HOK & _ & _).
  split; [exact HOK|]. split; [exact (desk_frs_kept P m HPM KV) | exact (desk_sf_kept P m HPM KV)].
Qed.

Lemma desk_saved_kept : forall P m, desk_PM P -> desk_KV P m -> mrx_saved Wc m sp1 regs0.
Proof.
  intros P m HPM KV. pose proof desk_sp as (SP1 & SP2 & STK & FRM & _).
  apply (mrx_saved_kept Wc Wc mem2 m sp1 regs0 HSV). intros a Ha.
  apply KV; [desk_lia | desk_lia | intros HPa; pose proof (HPM a HPa); desk_lia].
Qed.

Lemma desk_tw_kept : forall m, desk_KV (fun _ => False) m -> tw_at TMAP_B (aview segs (w_H Wc) m) Bwc.
Proof.
  intros m KV. pose proof desk_sp as (SP1 & SP2 & STK & FRM & _).
  apply (tw_kept TMAP_B (aview segs (w_H Wc) mem2)); [exact HTW|].
  intros x Hx. pose proof (TMAP_B_hull x Hx) as Hh.
  unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in Hh.
  apply KV; [lia | desk_lia | intros []].
Qed.

Lemma desk_hi : forall regs, desk_rg regs -> mrx_hi regs0 regs.
Proof.
  intros regs (RG & _) q Hq.
  rewrite (RG q ltac:(unfold acallee_saved; lia) ltac:(lia)). exact (HHI q Hq).
Qed.

(* ---- the bytes the compares read ---- *)

Lemma desk_frame_view : forall P m, desk_PM P -> desk_KV P m -> forall j, 0 <= j < mlen fr ->
  aview segs (w_H Wc) m (fa + j) = Some (bv_unsigned (nth (Z.to_nat j) (TI.tf_bytes fr) (Z_to_bv 8 0))).
Proof.
  intros P m HPM KV j Hj. pose proof (desk_frs_kept P m HPM KV) as (G & _ & _).
  replace (fa + j) with (fa + Z.of_nat (Z.to_nat j)) by lia.
  apply (desk_garr_view Wc m fa (TI.tf_bytes fr) (Z.to_nat j) G). unfold AK.mlen in Hj. lia.
Qed.

Lemma desk_oui_view : forall P m, desk_PM P -> desk_KV P m -> forall i, 0 <= i < 3 ->
  aview segs (w_H Wc) m (TRANS_SPEC_OUI + i) = Some (bv_unsigned (nth (Z.to_nat i) TC.SPEC_OUI (Z_to_bv 8 0))).
Proof.
  intros P m HPM KV i Hi. pose proof (desk_frs_kept P m HPM KV) as (_ & _ & ROM).
  rewrite (ROM _ (desk_oui_ro i Hi)). exact (desk_oui_rom i Hi).
Qed.

(* M.desk's six bytes at a memory holding the world Bcur. *)
Lemma desk_mdesk_view : forall m Bcur, tw_at TMAP_B (aview segs (w_H Wc) m) Bcur -> forall i, 0 <= i < 6 ->
  aview segs (w_H Wc) m (TB_M + 4 + i) = Some (bv_unsigned (nth (Z.to_nat i) (TW.M_desk Bcur) (Z_to_bv 8 0))).
Proof.
  intros m Bcur HW i Hi.
  pose proof (tw_garr8 segs (mrestrict (w_H Wc) m) TMAP_B Bcur TW.OFF_M TB_M TW.SZ_M 4 6 TMAP_B_ok HW
    TMAP_B_M ltac:(lia) ltac:(unfold TW.SZ_M; lia)) as G.
  replace (TB_M + 4 + i) with (TB_M + 4 + Z.of_nat (Z.to_nat i)) by lia.
  change (TW.zs (TW.sub Bcur (TW.OFF_M + 4) 6)) with (map DSpec.bz (TW.sub Bcur (TW.OFF_M + 4) 6)) in G.
  rewrite (desk_garr_view Wc m (TB_M + 4) (TW.sub Bcur (TW.OFF_M + 4) 6) (Z.to_nat i) G).
  - rewrite desk_desk_eq. reflexivity.
  - assert (L : length (TW.sub Bcur (TW.OFF_M + 4) 6) = 6%nat).
    { apply TWL.length_sub; [unfold TW.OFF_M; lia|].
      rewrite (tw_len TMAP_B _ Bcur HW), Z2Nat.id by (unfold TW.W_LEN; lia).
      unfold TW.OFF_M, TW.W_LEN. lia. }
    lia.
Qed.

Lemma desk_mdesk_len : forall m Bcur, tw_at TMAP_B (aview segs (w_H Wc) m) Bcur -> length (TW.M_desk Bcur) = 6%nat.
Proof.
  intros m Bcur HW. rewrite desk_desk_eq. apply TWL.length_sub; [unfold TW.OFF_M; lia|].
  rewrite (tw_len TMAP_B _ Bcur HW), Z2Nat.id by (unfold TW.W_LEN; lia).
  unfold TW.OFF_M, TW.W_LEN. lia.
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
  assert (LS : length (TW.sub (TI.tf_bytes fr) k N) = N) by (apply TWL.length_sub; unfold AK.mlen in HkN; lia).
  assert (FV : forall i, 0 <= i < Z.of_nat N -> aview segs (w_H Wc) m (fa + k + i) =
    Some (bv_unsigned (nth (Z.to_nat i) (TW.sub (TI.tf_bytes fr) k N) (Z_to_bv 8 0)))).
  { intros i Hi. replace (fa + k + i) with (fa + (k + i)) by lia.
    rewrite (desk_frame_view P m HPM KV (k + i) ltac:(unfold AK.mlen in *; lia)).
    rewrite (tw_nth_sub (TI.tf_bytes fr) k N (Z.to_nat i) (Z_to_bv 8 0)) by (unfold AK.mlen in HkN; lia).
    do 3 f_equal. lia. }
  rewrite UMR.mr_beq_iff, (AD.desk_zs_eq _ _ N LS Hl).
  split; intros H i Hi.
  - specialize (H i Hi). rewrite (FV i Hi), (HY i Hi) in H. injection H as H. exact H.
  - rewrite (FV i Hi), (HY i Hi). f_equal. exact (H i Hi).
Qed.

(* ---- the ranges the compares read ---- *)

Lemma desk_rd_frame : forall P m md' k N, desk_PM P -> desk_KV P m -> @AR rc segs B ly2 S2 Wc m md' ->
  0 <= k -> k + N <= mlen fr -> 0 <= N -> decode_rd_ok Wc m (fa + k) N.
Proof.
  intros P m md' k N HPM KV HAR Hk HkN HN.
  pose proof (desk_frs_kept P m HPM KV) as (_ & HSRC & _).
  pose proof desk_fpl as (F0 & FP & F64 & Fn).
  pose proof (trans_src_ok_rd B LAWS ly2 S2 Wc m md' fa (mlen fr) HAR HSRC ltac:(lia)) as RD.
  exact (trans_rd_ok_sub Wc m fa (mlen fr) (fa + k) N RD ltac:(lia) ltac:(lia) HN).
Qed.

(* SPEC_OUI: its bytes are the image's, its shadow group [0x7fffc208, 0x7fffc210) the record's. *)
Lemma desk_rd_oui : forall P m md', @AR rc segs B ly2 S2 Wc m md' -> desk_PM P -> desk_KV P m ->
  decode_rd_ok Wc m TRANS_SPEC_OUI 3.
Proof.
  intros P m md' HAR HPM KV.
  destruct (HCELLS ly2) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
    ROUI & ZC24 & RC24 & _).
  destruct HMRX as (_ & _ & HC).
  destruct (HC ly2) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & RO8 & RO16 & RO24 & RC16 & RC24b & _).
  split; [|split; [|split; [|split; [|split]]]].
  - intros a Ha. replace a with (TRANS_SPEC_OUI + (a - TRANS_SPEC_OUI)) by lia.
    rewrite (desk_oui_view P m HPM KV (a - TRANS_SPEC_OUI) ltac:(lia)). discriminate.
  - intros x Hx. exists 3. split.
    + eapply (desk_const1 B ly2 S2 Wc m md'); [exact HAR | exact ROUI | lia |].
      unfold BCells.shadow_addr, BCells.ASAN_K, TRANS_SPEC_OUI, shadow_of_addr, SHADOW_OFF in *.
      Z.div_mod_to_equations. lia.
    + unfold saddr_ok, TRANS_SPEC_OUI in *. right. Z.div_mod_to_equations. lia.
  - intros s' Hs. AD.desk_hull Hs.
    assert (Hc : s' = 0x7fffc208 \/ s' = 0x7fffc209 \/ s' = 0x7fffc20a \/ s' = 0x7fffc20b \/ s' = 0x7fffc20c \/
                 s' = 0x7fffc20d \/ s' = 0x7fffc20e \/ s' = 0x7fffc20f) by lia.
    destruct Hc as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]];
      [ eapply desk_const1_nn; [exact HAR | exact ROUI | lia | reflexivity]
      | eapply desk_const1_nn; [exact HAR | exact RO8 | lia | reflexivity]
      | eapply desk_const1_nn; [exact HAR | exact RO16 | lia | reflexivity]
      | eapply desk_const1_nn; [exact HAR | exact RO24 | lia | reflexivity]
      | replace 0x7fffc20c with (BCells.shadow_addr TRANS_STR_C24) by reflexivity;
        rewrite (decode_zshadow_rd B ly2 S2 Wc m md' TRANS_STR_C24 (TRANS_STR_C24 + 8) TRANS_STR_C24 HAR
          ltac:(reflexivity) ltac:(lia) ltac:(lia) ZC24); discriminate
      | eapply desk_const1_nn; [exact HAR | exact RC24 | lia | reflexivity]
      | eapply desk_const1_nn; [exact HAR | exact RC16 | lia | reflexivity]
      | eapply desk_const1_nn; [exact HAR | exact RC24b | lia | reflexivity] ].
  - unfold amem_range, kLowMemEnd, TRANS_SPEC_OUI. lia.
  - unfold TRANS_SPEC_OUI. lia.
  - unfold TRANS_SPEC_OUI. lia.
Qed.

(* [M + 4, M + 10): its bytes are the world's, its shadow is M's zero shadow, its hull [0x800b3db8, 0x800b3dc0)
   also holds g_last_counter's last granule and guard bytes. *)
Lemma desk_rd_m : forall m md' Bcur, @AR rc segs B ly2 S2 Wc m md' ->
  tw_at TMAP_B (aview segs (w_H Wc) m) Bcur -> decode_rd_ok Wc m (TB_M + 4) 6.
Proof.
  intros m md' Bcur HAR HW.
  assert (EM : TB_M = 0x5dede0) by reflexivity.
  destruct HMRX as (_ & HZM & HC).
  destruct (HC ly2) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & RG0 & RG8 & RG16 & RG24).
  assert (ZS : forall T, T mod 8 = 0 -> TB_M <= T -> T + 8 <= TB_M + TW.SZ_M ->
    aview segs (w_H Wc) m (BCells.shadow_addr T) = Some 0)
    by (intros T Hz1 Hz2 Hz3; exact (decode_zshadow_rd B ly2 S2 Wc m md' TB_M (TB_M + TW.SZ_M) T HAR Hz1 Hz2 Hz3 HZM)).
  assert (ZSn : forall T s, T mod 8 = 0 -> TB_M <= T -> T + 8 <= TB_M + TW.SZ_M -> BCells.shadow_addr T = s ->
    aview segs (w_H Wc) m s <> None)
    by (intros T s Hz1 Hz2 Hz3 <-; rewrite (ZS T Hz1 Hz2 Hz3); discriminate).
  split; [|split; [|split; [|split; [|split]]]].
  - intros a Ha. replace a with (TB_M + 4 + (a - (TB_M + 4))) by lia.
    rewrite (desk_mdesk_view m Bcur HW (a - (TB_M + 4)) ltac:(lia)). discriminate.
  - intros x Hx. exists 0. split; [|left; reflexivity].
    assert (EQ : shadow_of_addr SHADOW_OFF x = BCells.shadow_addr (8 * (x / 8))).
    { unfold BCells.shadow_addr, BCells.ASAN_K, shadow_of_addr, SHADOW_OFF.
      rewrite Z.mul_comm, Z.div_mul by lia. lia. }
    rewrite EQ. apply ZS; [rewrite Z.mul_comm; apply Z_mod_mult | | ];
      unfold TW.SZ_M in *; Z.div_mod_to_equations; lia.
  - intros s' Hs. AD.desk_hull Hs.
    assert (Hc : s' = 0x800b3db8 \/ s' = 0x800b3db9 \/ s' = 0x800b3dba \/ s' = 0x800b3dbb \/ s' = 0x800b3dbc \/
                 s' = 0x800b3dbd \/ s' = 0x800b3dbe \/ s' = 0x800b3dbf) by lia.
    destruct Hc as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]];
      [ eapply desk_const1_nn; [exact HAR | exact RG0 | lia | reflexivity]
      | eapply desk_const1_nn; [exact HAR | exact RG8 | lia | reflexivity]
      | eapply desk_const1_nn; [exact HAR | exact RG16 | lia | reflexivity]
      | eapply desk_const1_nn; [exact HAR | exact RG24 | lia | reflexivity]
      | eapply (ZSn TB_M); [reflexivity | lia | unfold TW.SZ_M; lia | reflexivity]
      | eapply (ZSn (TB_M + 8)); [reflexivity | lia | unfold TW.SZ_M; lia | reflexivity]
      | eapply (ZSn (TB_M + 16)); [reflexivity | lia | unfold TW.SZ_M; lia | reflexivity]
      | eapply (ZSn (TB_M + 24)); [reflexivity | lia | unfold TW.SZ_M; lia | reflexivity] ].
  - unfold amem_range, kLowMemEnd. lia.
  - lia.
  - lia.
Qed.

(* ---- the exits ---- *)

Lemma desk_exit_epi : forall regs m md, desk_mid (fun _ => False) regs m md ->
  YK11.getr regs 10 = w64 0 -> Bw' = Bwc -> r = 0 ->
  SRr segs Wc (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (MRX_PC OFF_EPI)) m (YK11.seg_rom segs)) md) IPOST.
Proof.
  intros regs m md (HJ & RG & KV) R10 EB Er. pose proof RG as (RGS & _).
  apply (KE Wc Bwc).
  apply (mrx_at_intro B MT sp1 regs0 lyc Sc W memc mdc (MRX_PC OFF_EPI) (R_EPI Bw' r) Wc Bwc ly2 S2 regs m md HJ
    HFR2 HPM2 HMO2).
  - exact (eq_trans (RGS 2 ltac:(unfold acallee_saved; lia) ltac:(lia)) H2).
  - exact (eq_trans (RGS 3 ltac:(unfold acallee_saved; lia) ltac:(lia)) H3).
  - exact (eq_trans (RGS 4 ltac:(unfold acallee_saved; lia) ltac:(lia)) H4).
  - exact (desk_hi regs RG).
  - exact (desk_saved_kept _ m desk_PM_false KV).
  - exact (desk_tw_kept m KV).
  - unfold R_EPI. split; [symmetry; exact EB | rewrite Er; exact R10].
Qed.

Lemma desk_exit_body : forall P regs m md Bcur, desk_mid P regs m md -> desk_PM P ->
  tw_at TMAP_B (aview segs (w_H Wc) m) Bcur ->
  UMR.mr_k timg_B fr n Bcur = Some (Bw', r) ->
  SRr segs Wc (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (MRX_PC OFF_BODY)) m (YK11.seg_rom segs)) md) IPOST.
Proof.
  intros P regs m md Bcur (HJ & RG & KV) HPM HW HK. pose proof RG as (RGS & RG9).
  apply (KB Wc Bcur).
  apply (mrx_at_intro B MT sp1 regs0 lyc Sc W memc mdc (MRX_PC OFF_BODY) (R_BODY B fr n sp1 Bw' r) Wc Bcur
    ly2 S2 regs m md HJ HFR2 HPM2 HMO2).
  - exact (eq_trans (RGS 2 ltac:(unfold acallee_saved; lia) ltac:(lia)) H2).
  - exact (eq_trans (RGS 3 ltac:(unfold acallee_saved; lia) ltac:(lia)) H3).
  - exact (eq_trans (RGS 4 ltac:(unfold acallee_saved; lia) ltac:(lia)) H4).
  - exact (desk_hi regs RG).
  - exact (desk_saved_kept P m HPM KV).
  - exact HW.
  - unfold R_BODY. split; [exact (desk_cur_kept P m HPM KV)|].
    split; [exact RG9|].
    split; [exact (eq_trans (RGS 18 ltac:(unfold acallee_saved; lia) ltac:(lia)) H18) | exact HK].
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
  SRr segs Wc (mkCfg (@YK11.mkst fx regsT (Z_to_bv 64 (transportb_sigma TB___interceptor_trampoline_bcmp)) memT
    (YK11.seg_rom segs)) mdT) Q.
Proof.
  intros P regsT memT mdT x y N raw Q MID HPM R10 R11 R12 HN RDX RDY OFX OFY R1 HRAW KK.
  pose proof MID as (HJ & (RG & RG9) & KV).
  pose proof desk_sp as (SP1 & SP2 & STK & FRM & _ & _ & Hg0 & Ht0).
  pose proof RDX as (HvX & HraX & HhX & HmX & H0X & H63X).
  pose proof RDY as (HvY & HraY & HhY & HmY & H0Y & H63Y).
  assert (R2 : YK11.getr regsT 2 = Z_to_bv 64 (sp1 - MRX_FRAME))
    by exact (eq_trans (RG 2 ltac:(unfold acallee_saved; lia) ltac:(lia)) H2).
  assert (HspT : spZ regsT = sp1 + -112)
    by (unfold spZ; rewrite R2; rewrite unsigned_lit_small; [unfold MRX_FRAME; lia | unfold MRX_FRAME; lia]).
  assert (R3 : YK11.getr regsT 3 = w64 (as_gp B)).
  { rewrite <- Hg0. exact (eq_trans (RG 3 ltac:(unfold acallee_saved; lia) ltac:(lia)) H3). }
  assert (R4 : YK11.getr regsT 4 = w64 (as_tp B)).
  { rewrite <- Ht0. exact (eq_trans (RG 4 ltac:(unfold acallee_saved; lia) ltac:(lia)) H4). }
  assert (SX : src_ok segs Wc regsT memT x N)
    by (intros a Ha; split; [exact (HvX a Ha) | rewrite HspT; unfold ESTACK; lia]).
  assert (SY : src_ok segs Wc regsT memT y N)
    by (intros a Ha; split; [exact (HvY a Ha) | rewrite HspT; unfold ESTACK; lia]).
  assert (BX : forall a, x <= a < x + N -> ~ (sp1 + -112 - 2 * ESTACK <= a < sp1 + -112))
    by (intros a Ha; unfold ESTACK; lia).
  assert (BY : forall a, y <= a < y + N -> ~ (sp1 + -112 - 2 * ESTACK <= a < sp1 + -112))
    by (intros a Ha; unfold ESTACK; lia).
  eapply SRr_bind.
  { exact (mrx_bcmp_gx B LAWS _ (HBCMP fx) Wc regsT memT MRX_STK sp1 [] lyc Sc W memc mdc [] ly2 S2 mdT 0 x y N
      (-112) raw HJ R10 R11 R12 HN H0X H63X H0Y H63Y HspT eq_refl ltac:(lia)
      ltac:(rewrite STK; unfold ESTACK; lia) R3 R4 R1 HRAW SX SY BX BY HmX HmY HraX (fun _ => HhX) HraY
      (fun _ => HhY)). }
  cbv beta. intros W2 c2 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & Hiff & Hview & _).
  apply (KK regs3 mem3 md3); [|exact Hiff].
  apply (desk_mid_step P P regsT memT mdT regs3 mem3 md3 MID HPM (fun a h => h) HP3); [|exact HJ3].
  intros a Ha Hw _. apply Hview; [exact Ha|]. unfold desk_cwin in Hw. unfold ESTACK. lia.
Qed.

(* ---- the memcpy ---- *)

Definition desk_Pcpy (a : Z) : Prop := TB_M + 4 <= a < TB_M + 10.
Definition desk_Pall (a : Z) : Prop := TB_M <= a < TB_M + 10.

Lemma desk_memcpy : forall (regsT : bvmap 5 word) (memT : word -> option byte) (mdT : Model) (raw : word)
    (Q : world segs -> config -> Prop),
  desk_mid (fun _ => False) regsT memT mdT ->
  YK11.getr regsT 10 = w64 (TB_M + 4) -> YK11.getr regsT 11 = w64 (fa + 6) -> YK11.getr regsT 12 = w64 6 ->
  decode_rd_ok Wc memT (fa + 6) 6 -> decode_rd_ok Wc memT (TB_M + 4) 6 ->
  YK11.getr regsT 1 = raw -> YK0s.ret_ok raw ->
  (forall regs3 mem3 md3, desk_mid desk_Pcpy regs3 mem3 md3 ->
     (forall i, 0 <= i < 6 -> aview segs (w_H Wc) mem3 (TB_M + 4 + i) = aview segs (w_H Wc) memT (fa + 6 + i)) ->
     SRr segs Wc (mkCfg (@YK11.mkst fx regs3 raw mem3 (YK11.seg_rom segs)) md3) Q) ->
  SRr segs Wc (mkCfg (@YK11.mkst fx regsT (Z_to_bv 64 (transportb_sigma TB___asan_memcpy)) memT
    (YK11.seg_rom segs)) mdT) Q.
Proof.
  intros regsT memT mdT raw Q MID R10 R11 R12 RDX RDD R1 HRAW KK.
  pose proof MID as (HJ & (RG & RG9) & KV).
  pose proof desk_sp as (SP1 & SP2 & STK & FRM & _ & _ & Hg0 & Ht0).
  pose proof desk_fpl as (F0 & FP & F64 & Fn).
  pose proof RDX as (HvX & HraX & HhX & HmX & H0X & H63X).
  pose proof RDD as (HvD & HraD & HhD & HmD & H0D & H63D).
  assert (EM : TB_M = 0x5dede0) by reflexivity.
  assert (R2 : YK11.getr regsT 2 = Z_to_bv 64 (sp1 - MRX_FRAME))
    by exact (eq_trans (RG 2 ltac:(unfold acallee_saved; lia) ltac:(lia)) H2).
  assert (HspT : spZ regsT = sp1 + -112)
    by (unfold spZ; rewrite R2; rewrite unsigned_lit_small; [unfold MRX_FRAME; lia | unfold MRX_FRAME; lia]).
  assert (R3 : YK11.getr regsT 3 = w64 (as_gp B)).
  { rewrite <- Hg0. exact (eq_trans (RG 3 ltac:(unfold acallee_saved; lia) ltac:(lia)) H3). }
  assert (R4 : YK11.getr regsT 4 = w64 (as_tp B)).
  { rewrite <- Ht0. exact (eq_trans (RG 4 ltac:(unfold acallee_saved; lia) ltac:(lia)) H4). }
  assert (SX : src_ok segs Wc regsT memT (fa + 6) 6)
    by (intros a Ha; split; [exact (HvX a Ha) | rewrite HspT; unfold ESTACK, AK.mlen in *; lia]).
  assert (DIS : TB_M + 4 + 6 <= fa + 6 \/ fa + 6 + 6 <= TB_M + 4).
  { destruct (Z_le_gt_dec (TB_M + 10) (fa + 6)) as [Hl|Hl]; [left; lia|].
    destruct (Z_le_gt_dec (fa + 12) (TB_M + 4)) as [Hr|Hr]; [right; lia|].
    exfalso. apply (desk_apart_M (Z.max (TB_M + 4) (fa + 6))); unfold AK.mlen in *; lia. }
  eapply SRr_bind.
  { apply (@gx_intrin_at fx rc tfib_sink_head segs B LAWS transportb_segs_low OCpy
      (transportb_sigma TB___asan_memcpy) (HMCPY fx) TG.G_HARNESS_B Wc regsT memT MRX_STK sp1 [] lyc Sc W memc mdc []
      ly2 S2 mdT 0 (TB_M + 4) (fa + 6) 6 (-112) raw HGX G_HARNESS_B_rw HJ R10 R11 R12).
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
      intros a Ha. right. apply desk_inG. unfold TW.SZ_M. lia.
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

Lemma desk_src_eq : mrxb_src fr n = TW.sub (TI.tf_bytes fr) 6 6.
Proof.
  pose proof HCUR as ((Hn & Hok) & _).
  pose proof (mrx_ok_fields fr n (conj Hn Hok)) as (_ & Hs6 & _).
  unfold mrxb_src. rewrite Hs6. reflexivity.
Qed.

Lemma desk_src_len : length (mrxb_src fr n) = 6%nat.
Proof.
  pose proof desk_fpl as (_ & _ & _ & Fn). rewrite desk_src_eq. apply TWL.length_sub; unfold AK.mlen in Fn; lia.
Qed.

Lemma desk_world2 : forall (rdF : Z -> option Z),
  (forall i, 0 <= i < 6 ->
     rdF (TB_M + 4 + i) = Some (bv_unsigned (nth (Z.to_nat i) (mrxb_src fr n) (Z_to_bv 8 0)))) ->
  (forall j, (j < 4)%nat -> rdF (TB_M + 0 + Z.of_nat j) = Some (YO0f.le_byte 1 4 j)) ->
  (forall x, tw_in TMAP_B x -> ~ (TB_M <= x < TB_M + 4) -> ~ (TB_M + 4 <= x < TB_M + 10) ->
     rdF x = aview segs (w_H Wc) mem2 x) ->
  tw_at TMAP_B rdF (TW.set_M_desk_known (TW.set_M_desk Bwc (mrxb_src fr n)) 1).
Proof.
  intros rdF VD VK HK.
  assert (SM : TW.SZ_M = 1648) by reflexivity.
  pose proof desk_src_len as LS.
  rewrite desk_set_eq.
  pose proof (mrx_tw_start rdF (aview segs (w_H Wc) mem2) Bwc HTW) as HW0.
  pose proof (mrx_tw_span rdF (aview segs (w_H Wc) mem2) _ Bwc TW.OFF_M TB_M TW.SZ_M 4 (TW.OFF_M + 4)
    (mrxb_src fr n) HW0 TMAP_B_M ltac:(lia) ltac:(lia) ltac:(rewrite LS; lia) ltac:(rewrite LS; exact VD)) as HW1.
  rewrite LS in HW1.
  pose proof (mrx_tw_step rdF (aview segs (w_H Wc) mem2) _ _ TW.OFF_M TB_M TW.SZ_M 0 (TW.OFF_M + 0) 4 1 HW1
    TMAP_B_M ltac:(lia) ltac:(lia) ltac:(lia) VK) as HW2.
  apply (mrx_tw_end rdF (aview segs (w_H Wc) mem2) _ _ HW2).
  intros x Hx HP. mrx_unP HP. apply HK; [exact Hx | lia | lia].
Qed.

(* ---- the phases ---- *)

(* After the bcmp with M.desk (+0x0b8, bnez a0): a0 <> 0 returns 0; a0 = 0 goes to BODY. *)
Lemma desk_pA : forall regs m md, desk_mid (fun _ => False) regs m md ->
  TW.M_desk_known Bwc <> 0 ->
  (YK11.getr regs 10 = w64 0 <-> TC.beq_bytes (mrxb_src fr n) (TW.M_desk Bwc) = true) ->
  SRr segs Wc (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + 14900)) m (YK11.seg_rom segs)) md) IPOST.
Proof.
  intros regs m md MID HK IFF.
  pose proof MID as (HJ & RG & KV).
  destruct desk_vals as (_ & _ & _ & PEPI & PBODY).
  pose proof desk_PM_false as HPM0.
  pose proof (desk_imgf regs) as HEI. pose proof (desk_agreef regs) as AG.
  pose proof (desk_entryf (w_H Wc) regs m 14900) as HS.
  assert (EEf : forall k (q : bv 5), Z.of_nat k = bv_unsigned q -> ew (desk_Ef regs) k = YK11.getr regs q)
    by (intros k q Hk; unfold desk_Ef; apply ew_Eimg_Ereg_nat; exact Hk).
  assert (SHOK : sh_ok segs DESK_Bx DESK_SH (desk_Ef regs) (mrestrict (w_H Wc) m))
    by (unfold sh_ok, DESK_SH; apply Forall_nil).
  pose proof (@paj_run_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B HGX
    0 []) as RUN.
  pose proof (@paj_run_to_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS
    TG.G_HARNESS_B HGX 0 []) as RUNTO.
  pose proof (paj_branch (fx := fx) (PI := PI_transportb)) as BR.
  psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
  - (* a0 <> 0: the desk differs; a0 = 0 and the epilogue *)
    apply (proj1 (AD.desk_br_ne (desk_Ef regs) regs EEf)) in Hc.
    assert (EB : TC.beq_bytes (mrxb_src fr n) (TW.M_desk Bwc) = false).
    { destruct (TC.beq_bytes (mrxb_src fr n) (TW.M_desk Bwc)) eqn:E; [|reflexivity].
      exfalso. apply Hc. apply IFF. reflexivity. }
    destruct (desk_m_ne _ _ _ _ _ _ HK EB HM) as [EBw Er].
    paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan 14764.
    { desk_awr. }
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
      - exact (proj1 (AD.desk_eqb0 _) Q).
      - exfalso. assert (N : YK11.getr regs 10 <> w64 0)
          by (intros Z0; apply (proj2 (AD.desk_eqb0 _)) in Z0; congruence).
        apply (proj2 (AD.desk_br_ne (desk_Ef regs) regs EEf)) in N. rewrite N in Hc. discriminate Hc. }
    pose proof (desk_m_eq _ _ _ _ _ _ HK (proj1 IFF Hc') HM) as HMK.
    paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan 14972.
    { desk_awr. }
    set (md' := with_vm_backing (m_vm_lazy md) mat md) in *. clearbody md'. clear mat.
    assert (HP : aregs_preserved regs (ms_regs ms))
      by (apply (aregs_preserved_of_st_ok segs (w_H Wc) (desk_Ef regs) _ ms regs [w64 SHADOW_OFF] HS AG);
          vm_compute; reflexivity).
    pose proof (desk_mid_step _ _ regs m md (ms_regs ms) (ms_mem ms) md' MID HPM0 (fun a h => h) HP
      (fun a Ha _ _ => desk_frame_kept _ _ _ _ HFr eq_refl a Ha) HJ) as MID'.
    pmkst HS. rewrite PBODY.
    pose proof MID' as (_ & _ & KV').
    exact (desk_exit_body _ (ms_regs ms) (ms_mem ms) md' Bwc MID' HPM0 (desk_tw_kept _ KV') HMK).
Qed.

(* After the bcmp with SPEC_OUI (+0x0e4, bnez a0): a0 <> 0 returns 0; a0 = 0 memcpies and stores. *)
Lemma desk_pB : forall regs m md, desk_mid (fun _ => False) regs m md ->
  TW.M_desk_known Bwc = 0 ->
  ((DSpec.sf_cmd (mrx_f fr n) =? TC.SPEC_CMD_E0) || (DSpec.sf_cmd (mrx_f fr n) =? TC.SPEC_CMD_E1))%bool = true ->
  (YK11.getr regs 10 = w64 0 <-> TC.beq_bytes (firstn 3 (mrxb_src fr n)) TC.SPEC_OUI = true) ->
  SRr segs Wc (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + 14944)) m (YK11.seg_rom segs)) md) IPOST.
Proof.
  intros regs m md MID HK HCMD IFF.
  pose proof MID as (HJ & RG & KV).
  pose proof RG as (RGS & RG9).
  destruct desk_vals as (_ & _ & _ & PEPI & PBODY).
  pose proof desk_sp as (SP1 & SP2 & STK & FRM & _).
  pose proof desk_fpl as (F0 & FP & F64 & Fn).
  pose proof desk_PM_false as HPM0.
  assert (EM : TB_M = 0x5dede0) by reflexivity.
  pose proof (desk_imgf regs) as HEI. pose proof (desk_agreef regs) as AG.
  pose proof (desk_entryf (w_H Wc) regs m 14944) as HS.
  assert (EEf : forall k (q : bv 5), Z.of_nat k = bv_unsigned q -> ew (desk_Ef regs) k = YK11.getr regs q)
    by (intros k q Hk; unfold desk_Ef; apply ew_Eimg_Ereg_nat; exact Hk).
  assert (SHOK : sh_ok segs DESK_Bx DESK_SH (desk_Ef regs) (mrestrict (w_H Wc) m))
    by (unfold sh_ok, DESK_SH; apply Forall_nil).
  pose proof (@paj_run_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B HGX
    0 []) as RUN.
  pose proof (@paj_run_to_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS
    TG.G_HARNESS_B HGX 0 []) as RUNTO.
  pose proof (paj_branch (fx := fx) (PI := PI_transportb)) as BR.
  psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
  - (* a0 <> 0: the OUI differs; a0 = 0 and the epilogue *)
    apply (proj1 (AD.desk_br_ne (desk_Ef regs) regs EEf)) in Hc.
    assert (EO : TC.beq_bytes (firstn 3 (mrxb_src fr n)) TC.SPEC_OUI = false).
    { destruct (TC.beq_bytes (firstn 3 (mrxb_src fr n)) TC.SPEC_OUI) eqn:E; [|reflexivity].
      exfalso. apply Hc. apply IFF. reflexivity. }
    destruct (desk_m_oui_no _ _ _ _ _ _ HK HCMD EO HM) as [EBw Er].
    paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan 14764.
    { desk_awr. }
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
      - exact (proj1 (AD.desk_eqb0 _) Q).
      - exfalso. assert (N : YK11.getr regs 10 <> w64 0)
          by (intros Z0; apply (proj2 (AD.desk_eqb0 _)) in Z0; congruence).
        apply (proj2 (AD.desk_br_ne (desk_Ef regs) regs EEf)) in N. rewrite N in Hc. discriminate Hc. }
    pose proof (desk_m_oui_yes _ _ _ _ _ _ HK HCMD (proj1 IFF Hc') HM) as HMK.
    (* +0x0e8 .. +0x0f4: a0 = M + 4, a2 = 6, a1 = s0 = fa + 6, the call *)
    paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
    { desk_awr. }
    set (md1 := with_vm_backing (m_vm_lazy md) mat md) in *. clearbody md1. clear mat.
    assert (HP1 : aregs_preserved regs (ms_regs ms))
      by (apply (aregs_preserved_of_st_ok segs (w_H Wc) (desk_Ef regs) _ ms regs [w64 SHADOW_OFF] HS AG);
          vm_compute; reflexivity).
    pose proof (desk_mid_step _ _ regs m md (ms_regs ms) (ms_mem ms) md1 MID HPM0 (fun a h => h) HP1
      (fun a Ha _ _ => desk_frame_kept _ _ _ _ HFr eq_refl a Ha) HJ) as MID1.
    pose proof MID1 as (HJ1 & (RG1 & RG91) & KV1).
    desk_reg HS (Z_to_bv 5 10) (w64 (TB_M + 4)) Ra0
      ltac:(apply (AD.desk_sv_off (desk_Ef regs) 9 4 TB_M);
            [rewrite (EEf 9%nat (Z_to_bv 5 9) eq_refl); exact RG9 | lia]).
    desk_reg HS (Z_to_bv 5 11) (w64 (fa + 6)) Ra1
      ltac:(apply (AD.desk_sv_off0 (desk_Ef regs) 8 (fa + 6));
            [rewrite (EEf 8%nat (Z_to_bv 5 8) eq_refl);
             exact (eq_trans (RGS 8 ltac:(unfold acallee_saved; lia) ltac:(lia)) H8) | unfold AK.mlen in *; lia]).
    desk_reg HS (Z_to_bv 5 12) (w64 6) Ra2 ltac:(reflexivity).
    desk_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 14964)) Rra ltac:(apply codeptr_val; exact HEI).
    pmkst HS.
    lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
      change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (transportb_sigma TB___asan_memcpy)) mm rom) mdx) Q) end.
    pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ1) as HAR1.
    apply (desk_memcpy (ms_regs ms) (ms_mem ms) md1 (Z_to_bv 64 (BASE + 14964)) _ MID1 Ra0 Ra1 Ra2
      (desk_rd_frame _ (ms_mem ms) md1 6 6 HPM0 KV1 HAR1 ltac:(lia) ltac:(lia) ltac:(lia))
      (desk_rd_m (ms_mem ms) _ Bwc HAR1 (desk_tw_kept _ KV1)) Rra
      (ret_ok_codeptr_v (PI := PI_transportb) 14964 ltac:(lia) eq_refl)).
    intros regs3 mem3 md3 MID3 HCPY.
    (* +0x0f8 .. +0x0fc: a0 = 1, the store of M.desk_known, then BODY *)
    assert (VD3 : forall i, 0 <= i < 6 -> aview segs (w_H Wc) mem3 (TB_M + 4 + i) =
      Some (bv_unsigned (nth (Z.to_nat i) (mrxb_src fr n) (Z_to_bv 8 0)))).
    { intros i Hi. rewrite (HCPY i Hi).
      replace (fa + 6 + i) with (fa + (6 + i)) by lia.
      rewrite (desk_frame_view _ _ HPM0 KV1 (6 + i) ltac:(unfold AK.mlen in *; lia)).
      rewrite desk_src_eq.
      rewrite (tw_nth_sub (TI.tf_bytes fr) 6 6 (Z.to_nat i) (Z_to_bv 8 0)) by (unfold AK.mlen in Fn; lia).
      do 3 f_equal. lia. }
    pose proof MID3 as (HJ3 & (RG3 & RG93) & KV3).
    assert (HPMc : desk_PM desk_Pcpy) by (intros a Ha; unfold desk_Pcpy in Ha; lia).
    pose proof (desk_imgf regs3) as HEI3. pose proof (desk_agreef regs3) as AG3.
    pose proof (desk_entryw Wc regs3 mem3 RG93) as HS3.
    assert (U9 : bv_unsigned (ew (desk_Ef regs3) 9) = TB_M).
    { unfold desk_Ef. rewrite (ew_Eimg_Ereg_nat regs3 _ 9 (Z_to_bv 5 9) eq_refl), RG93.
      apply unsigned_lit_small. lia. }
    assert (SHOK3 : sh_ok segs DESK_Bx DESK_SH (desk_Ef regs3) (mrestrict (w_H Wc) mem3))
      by (unfold sh_ok, DESK_SH; apply Forall_nil).
    clear HS. clear dependent ms.
    rename HS3 into HS.
    paj_run_to_tok RUNTO HS HJ3 SHOK3 YC4b.Bspan 14972.
    { desk_awr_m U9. }
    set (mdF := with_vm_backing (m_vm_lazy md3) mat md3) in *. clearbody mdF. clear mat.
    assert (HPF : aregs_preserved regs3 (ms_regs ms))
      by (apply (aregs_preserved_of_st_ok segs (w_H Wc) (desk_Ef regs3) _ ms regs3 [w64 SHADOW_OFF] HS AG3);
          vm_compute; reflexivity).
    assert (KEEPF : forall a, 0 <= a < 2 ^ 64 -> ~ (TB_M <= a < TB_M + 4) ->
      aview segs (w_H Wc) (ms_mem ms) a = aview segs (w_H Wc) mem3 a).
    { intros a Ha Hn.
      apply (YC4b.kept_of_frame _ _ (w_H Wc) mem3 (ms_mem ms) (fun x => TB_M <= x < TB_M + 4) HFr);
        [|exact Ha | exact Hn].
      intros b wlo whi x Hin Hx. AD.desk_win Hin Hx ltac:(rewrite ?U9 in Hx; lia). }
    pose proof (desk_mid_step desk_Pcpy desk_Pall regs3 mem3 md3 (ms_regs ms) (ms_mem ms) mdF MID3
      ltac:(intros a Ha; unfold desk_Pall in Ha; lia)
      ltac:(intros a Ha; unfold desk_Pcpy in Ha; unfold desk_Pall; lia) HPF
      ltac:(intros a Ha _ Hn; apply KEEPF; [exact Ha | unfold desk_Pall in Hn; lia]) HJ3) as MIDF.
    assert (HPMa : desk_PM desk_Pall) by (intros a Ha; unfold desk_Pall in Ha; lia).
    (* the four bytes of 1 the store left *)
    pose proof (st_ok_pi_region_nth _ _ (restrict (w_H Wc) ms) 0 _ HS eq_refl) as RGN.
    cbn [ms_mem restrict] in RGN. destruct RGN as (_ & _ & _ & HCH).
    cbn [YP09.r_base YP09.r_chunks base_val] in HCH.
    rewrite U9 in HCH.
    pose proof (AD.desk_Forall_nth _ _ 0%nat _ HCH eq_refl) as HC1.
    pose proof (mrx_chunk_rd (desk_Ef regs3) (w_H Wc) (ms_mem ms) TB_M 0 4 (SLit 1) 1 HC1 eq_refl ltac:(cbn; lia))
      as VK.
    cbn [N.to_nat] in VK.
    (* the six bytes the memcpy left, still there *)
    assert (VD : forall i, 0 <= i < 6 -> aview segs (w_H Wc) (ms_mem ms) (TB_M + 4 + i) =
      Some (bv_unsigned (nth (Z.to_nat i) (mrxb_src fr n) (Z_to_bv 8 0)))).
    { intros i Hi. rewrite (KEEPF (TB_M + 4 + i) ltac:(lia) ltac:(lia)). exact (VD3 i Hi). }
    assert (HWF : tw_at TMAP_B (aview segs (w_H Wc) (ms_mem ms))
      (TW.set_M_desk_known (TW.set_M_desk Bwc (mrxb_src fr n)) 1)).
    { apply (desk_world2 _ VD VK).
      intros x Hx N1 N2. pose proof (TMAP_B_hull x Hx) as Hh.
      unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in Hh.
      rewrite (KEEPF x ltac:(lia) N1).
      apply KV3; [lia | desk_lia | unfold desk_Pcpy; lia]. }
    pmkst HS. rewrite PBODY.
    exact (desk_exit_body desk_Pall (ms_regs ms) (ms_mem ms) mdF _ MIDF HPMa HWF HMK).
Qed.

(* After a run from the cut's state (its regions not writable): the bytes kept, the callee-saved registers but s1
   the cut's, s1 = &M. *)
Ltac desk_run0 HS HJ HF HFr HG E0 AG0 HEI MIDo MIDn :=
  let KP := fresh "KP" in let R9 := fresh "R9" in let KEEP := fresh "KEEP" in
  pose proof (desk_run_kept _ _ _ _ HFr ltac:(intros b wlo whi x Hin Hx; AD.desk_win Hin Hx ltac:(lia))) as KEEP;
  clear HF HFr HG;
  lazymatch type of AG0 with env_agree _ (Ereg ?rg ?ex) _ =>
    pose proof (regs_kept_of_st_ok segs E0 _ _ rg ex DESK_KEEP HS AG0 ltac:(vm_compute; reflexivity)) as KP end;
  desk_reg HS (Z_to_bv 5 9) (w64 TB_M) R9
    ltac:(apply desk_den_img; [exact HEI | unfold A_TEXT, A_LIM; lia | vm_compute; reflexivity]);
  pose proof (desk_mid_run _ _ _ _ _ _ _ MIDo
    (desk_rg_of_keep _ ltac:(intros q Hq; exact (KP q Hq)) R9) KEEP HJ) as MIDn;
  clear KEEP KP R9 MIDo.

(* From the cut: run 1 (s1 = &M, M.desk_known), the branch, the cmd test, the two compares. *)
Lemma desk_walk : forall md2,
  @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS_B 0 [] MRX_STK sp1 [] lyc Sc W memc mdc [] ly2 S2 Wc
    mem2 md2 0 ->
  SRr segs Wc (mkCfg (@YK11.mkst fx regs2 (Z_to_bv 64 (MRX_PC OFF_DESK)) mem2 (YK11.seg_rom segs)) md2) IPOST.
Proof using All.
  intros md2 HJ.
  destruct desk_vals as (V8 & V51 & PDESK & PEPI & PBODY).
  pose proof desk_sp as (SP1 & SP2 & STK & FRM & Hsp16 & _).
  pose proof desk_fpl as (F0 & FP & F64 & Fn).
  pose proof desk_PM_false as HPM0.
  pose proof HCUR as (HOK & HFRS & HSF).
  assert (EM : TB_M = 0x5dede0) by reflexivity.
  assert (Usp : spZ regs2 = sp1 - 112)
    by (unfold spZ; rewrite H2, FRM; apply unsigned_lit_small; lia).
  assert (Hsp16' : (sp1 - 112) mod 16 = 0)
    by (replace (sp1 - 112) with (sp1 + (-7) * 16) by lia; rewrite Z_mod_plus_full; exact Hsp16).
  pose proof (mrx_ok_fields fr n HOK) as (_ & _ & _ & _ & _ & _ & HCR & _).
  set (cmd := DSpec.sf_cmd (mrx_f fr n)) in *.
  pose proof (mrx_sf_cmd (sg := segs) (mrestrict (w_H Wc) mem2) (sp1 - MRX_FRAME) fa (mrx_f fr n) HSF) as VC.
  replace (sp1 - MRX_FRAME + 40) with (spZ regs2 + 40) in VC by (rewrite Usp, FRM; lia).
  rewrite <- PDESK.
  set (E0 := desk_E regs2 Bwc cmd).
  pose proof (desk_img regs2 Bwc cmd) as HEI. fold E0 in HEI.
  assert (AG0 : env_agree 32
      (Ereg regs2 [w64 SHADOW_OFF; Z_to_bv 64 (TW.u_at Bwc TW.A_M_desk_known 4); w64 cmd]) E0)
    by (unfold E0, desk_E; split; [intros k Hk; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (EE0 : forall k (q : bv 5), Z.of_nat k = bv_unsigned q -> ew E0 k = YK11.getr regs2 q)
    by (intros k q Hk; unfold E0, desk_E; apply ew_Eimg_Ereg_nat; exact Hk).
  assert (E33 : ew E0 33 = Z_to_bv 64 (TW.u_at Bwc TW.A_M_desk_known 4))
    by (unfold E0, desk_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 1)).
  assert (E34 : ew E0 34 = w64 cmd)
    by (unfold E0, desk_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 2)).
  pose proof (desk_entry0 Wc regs2 mem2 Bwc cmd ltac:(rewrite Usp; lia) ltac:(rewrite Usp; lia)
    ltac:(rewrite Usp; exact Hsp16') HTW VC HCR) as HS.
  fold E0 in HS.
  assert (SHOK : sh_ok segs DESK_Bx DESK_SH E0 (mrestrict (w_H Wc) mem2))
    by (unfold sh_ok, DESK_SH; apply Forall_nil).
  pose proof (@paj_run_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B HGX
    0 []) as RUN.
  pose proof (@paj_run_to_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS
    TG.G_HARNESS_B HGX 0 []) as RUNTO.
  pose proof (paj_branch (fx := fx) (PI := PI_transportb)) as BR.
  (* run 1, +0x098 .. +0x0a4: s1 = &M, a0 = M.desk_known *)
  paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
  { desk_awr. }
  set (md1 := with_vm_backing (m_vm_lazy md2) mat md2) in *. clearbody md1. clear mat.
  pose proof (desk_run_kept _ _ _ _ HFr ltac:(intros b wlo whi x Hin Hx; AD.desk_win Hin Hx ltac:(lia))) as KEEP1.
  clear HF HFr HG.
  pose proof (regs_kept_of_st_ok segs E0 _ _ regs2
    [w64 SHADOW_OFF; Z_to_bv 64 (TW.u_at Bwc TW.A_M_desk_known 4); w64 cmd] DESK_KEEP HS AG0
    ltac:(vm_compute; reflexivity)) as KP1.
  desk_reg HS (Z_to_bv 5 9) (w64 TB_M) R91
    ltac:(apply desk_den_img; [exact HEI | unfold A_TEXT, A_LIM; lia | vm_compute; reflexivity]).
  assert (MID1 : desk_mid (fun _ => False) (ms_regs ms) (ms_mem ms) md1).
  { split; [exact HJ|]. split; [apply desk_rg_of_keep; [intros q Hq; exact (KP1 q Hq) | exact R91]|].
    intros a Ha _ _. exact (KEEP1 a Ha). }
  clear KEEP1 KP1 R91.
  (* the branch on M.desk_known *)
  psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
  - (* M.desk_known = 0: +0x0c0 .. +0x0cc, the cmd test *)
    rewrite (AD.desk_br_known E0 Bwc E33) in Hc. apply Z.eqb_eq in Hc.
    paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
    { desk_awr. }
    set (md2' := with_vm_backing (m_vm_lazy md1) mat md1) in *. clearbody md2'. clear mat.
    desk_run0 HS HJ HF HFr HG E0 AG0 HEI MID1 MID2.
    psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
    + (* the cmd is neither e0 nor e1: the epilogue *)
      rewrite (desk_br_cmd E0 cmd E34 HCR) in Hc0. apply negb_true_iff in Hc0.
      destruct (desk_m_cmd _ _ _ _ _ _ Hc Hc0 HM) as [EBw Er].
      paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan 14764.
      { desk_awr. }
      set (md3 := with_vm_backing (m_vm_lazy md2') mat md2') in *. clearbody md3. clear mat.
      desk_run0 HS HJ HF HFr HG E0 AG0 HEI MID2 MID3.
      desk_reg HS (Z_to_bv 5 10) (w64 0) R10 ltac:(reflexivity).
      pmkst HS. rewrite PEPI.
      exact (desk_exit_epi _ _ _ MID3 R10 EBw Er).
    + (* the cmd is e0 or e1: +0x0d0 .. +0x0e0, the OUI compare *)
      rewrite (desk_br_cmd E0 cmd E34 HCR) in Hc0. apply negb_false_iff in Hc0.
      paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
      { desk_awr. }
      set (md3 := with_vm_backing (m_vm_lazy md2') mat md2') in *. clearbody md3. clear mat.
      desk_run0 HS HJ HF HFr HG E0 AG0 HEI MID2 MID3.
      pose proof MID3 as (HJ3 & _ & KV3).
      desk_reg HS (Z_to_bv 5 10) (w64 (fa + 6)) Ra0
        ltac:(apply (AD.desk_sv_off0 E0 8 (fa + 6));
              [rewrite (EE0 8%nat (Z_to_bv 5 8) eq_refl); exact H8 | unfold AK.mlen in *; lia]).
      desk_reg HS (Z_to_bv 5 11) (w64 TRANS_SPEC_OUI) Ra1
        ltac:(apply desk_den_img; [exact HEI | unfold A_TEXT, A_LIM; lia | vm_compute; reflexivity]).
      desk_reg HS (Z_to_bv 5 12) (w64 3) Ra2 ltac:(reflexivity).
      desk_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 14944)) Rra ltac:(apply codeptr_val; exact HEI).
      pmkst HS.
      lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
        change (SRr sg Wx (mkCfg (@YK11.mkst fx rg
          (Z_to_bv 64 (transportb_sigma TB___interceptor_trampoline_bcmp)) mm rom) mdx) Q) end.
      pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as HAR3.
      apply (desk_bcmp _ _ _ _ (fa + 6) TRANS_SPEC_OUI 3 (Z_to_bv 64 (BASE + 14944)) _ MID3 HPM0 Ra0 Ra1 Ra2
        ltac:(lia)
        (desk_rd_frame _ _ _ 6 3 HPM0 KV3 HAR3 ltac:(lia) ltac:(unfold AK.mlen in *; lia) ltac:(lia))
        (desk_rd_oui _ _ _ HAR3 HPM0 KV3)
        ltac:(unfold AK.mlen in *; lia) ltac:(left; unfold TRANS_SPEC_OUI; lia) Rra
        (ret_ok_codeptr_v (PI := PI_transportb) 14944 ltac:(lia) eq_refl)).
      intros regs4 mem4 md4 MID4 IFF4.
      apply (desk_pB regs4 mem4 md4 MID4 Hc Hc0).
      assert (EOU : firstn 3 (mrxb_src fr n) = TW.sub (TI.tf_bytes fr) 6 3)
        by (rewrite desk_src_eq; apply UMR.mr_firstn3).
      rewrite EOU.
      exact (iff_trans IFF4
        (desk_cmp _ _ TRANS_SPEC_OUI 6 3 TC.SPEC_OUI HPM0 KV3 ltac:(lia) ltac:(unfold AK.mlen in *; lia) eq_refl
          (desk_oui_view _ _ HPM0 KV3))).
  - (* M.desk_known <> 0: +0x0a8 .. +0x0b4, the compare with M.desk *)
    rewrite (AD.desk_br_known E0 Bwc E33) in Hc. apply Z.eqb_neq in Hc.
    paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
    { desk_awr. }
    set (md2' := with_vm_backing (m_vm_lazy md1) mat md1) in *. clearbody md2'. clear mat.
    desk_run0 HS HJ HF HFr HG E0 AG0 HEI MID1 MID2.
    pose proof MID2 as (HJ2 & _ & KV2).
    desk_reg HS (Z_to_bv 5 10) (w64 (fa + 6)) Ra0
      ltac:(apply (AD.desk_sv_off0 E0 8 (fa + 6));
            [rewrite (EE0 8%nat (Z_to_bv 5 8) eq_refl); exact H8 | unfold AK.mlen in *; lia]).
    desk_reg HS (Z_to_bv 5 11) (w64 (TB_M + 4)) Ra1
      ltac:(apply desk_den_img; [exact HEI | unfold A_TEXT, A_LIM; lia | vm_compute; reflexivity]).
    desk_reg HS (Z_to_bv 5 12) (w64 6) Ra2 ltac:(reflexivity).
    desk_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 14900)) Rra ltac:(apply codeptr_val; exact HEI).
    pmkst HS.
    lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
      change (SRr sg Wx (mkCfg (@YK11.mkst fx rg
        (Z_to_bv 64 (transportb_sigma TB___interceptor_trampoline_bcmp)) mm rom) mdx) Q) end.
    pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HAR2.
    apply (desk_bcmp _ _ _ _ (fa + 6) (TB_M + 4) 6 (Z_to_bv 64 (BASE + 14900)) _ MID2 HPM0 Ra0 Ra1 Ra2 ltac:(lia)
      (desk_rd_frame _ _ _ 6 6 HPM0 KV2 HAR2 ltac:(lia) ltac:(unfold AK.mlen in *; lia) ltac:(lia))
      (desk_rd_m _ _ Bwc HAR2 (desk_tw_kept _ KV2))
      ltac:(unfold AK.mlen in *; lia) ltac:(left; lia) Rra
      (ret_ok_codeptr_v (PI := PI_transportb) 14900 ltac:(lia) eq_refl)).
    intros regs4 mem4 md4 MID4 IFF4.
    apply (desk_pA regs4 mem4 md4 MID4 Hc).
    rewrite desk_src_eq.
    exact (iff_trans IFF4
      (desk_cmp _ _ (TB_M + 4) 6 6 (TW.M_desk Bwc) HPM0 KV2 ltac:(lia) ltac:(unfold AK.mlen in *; lia)
        (desk_mdesk_len _ Bwc (desk_tw_kept _ KV2))
        (desk_mdesk_view _ Bwc (desk_tw_kept _ KV2)))).
Qed.

End cut.

(* The segment DESK: from the cut DESK to the cuts EPI and BODY. *)
Lemma mrx_seg_desk :
  K (MRX_PC OFF_EPI) (R_EPI Bw' r) ->
  K (MRX_PC OFF_BODY) (R_BODY B fr n sp1 Bw' r) ->
  K (MRX_PC OFF_DESK) (R_DESK B fr n sp1 Bw' r).
Proof using All.
  intros KE KB Wc Bwc c HAT.
  destruct HAT as (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ & HFR & HPM & HMO2 & HSP & HGP & HTP & HHI & HSV & HTW & HR).
  destruct HR as (HCUR & H8 & H18 & HM).
  exact (desk_walk Wc Bwc ly2 S2 regs2 mem2 KE KB HFR HPM HMO2 HSP HGP HTP HHI HSV HTW HCUR H8 H18 HM md2 HJ).
Qed.

End seg.
