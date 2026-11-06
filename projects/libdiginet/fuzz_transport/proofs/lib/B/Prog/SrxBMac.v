(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the entry segment of the image-A walk of libreac/fuzz_decode's LLVMFuzzerTestOneInput, with proof steps adapted from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v (pb_reac_ctrl_stamp_headamp's prologue and its class-0 stack malloc, origin/cold/pg-prog), proofs/libreac/fuzz_grant/lib/A/Prog/GrantACja.v (land_m32, denot_and_m32, sp1_facts), proofs/libreac/fuzz_grant/lib/A/Prog/GrantFrame.v (val_mem_of_rd32, rdword_of_val_mem, val_mem_moved), lib/Reusable/YCbq.v (call_effect_journal) and lib/A/Prog/YC85.v (aj_stack_malloc_atS); module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/CanKit.v, with its module names changed; 492 of its 559 lines of code are new or changed and 457 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/SrxDeskKit.v, with its module paths and module names changed; 829 of its 922 lines of code are new or changed and 466 lines of the source are left out. *)
(* SrxBMac: Theorem srxb_mac_ok : srxb_mac_stmt (lib/B/Prog/SrxBCut.v), the mac piece of the walk of
   diginet_session_rx on fuzz_transport.asan-ubsan, code +0x17c .. +0x1d0 (0x87900 .. 0x87954): the three MAC tests
   of transport/src/diginet_session.c:273-277. The code is image A's (lib/A/Prog/SrxMac.v) 12 bytes later and the
   proof is that file's at image B's names: the walk holds the caller's G journal (lib/A/W_journalG.v ajournal_gx
   G_HARNESS_B 0 []) with the class-1 frame owned; the runs are lib/B/Prog/TransportGRunB.v paj_run_x / paj_run_to_x
   from a state whose registers are the machine's (atoms), s5 and s11 pinned to s + 18152 and the shadow base, and one
   region: the shadow byte of s + 18184 (0: g_s's zero shadow, trans_srx_cells), which the check at +0x1c0 .. +0x1d0
   loads.
     run 1   +0x17c .. +0x188  s7 = f + 6, a2 = 6, a0 = f + 6, a1 = s, `jal` the bcmp wrapper;
     call 1  +0x18c            bcmp (f + 6, s, 6): the source MAC (fr_src b) against g_s.cfg.host_mac;
     +0x190                    `beq a0, zero`: equal (srx_mac_bad) runs through the checked access at s + 18184
                               (+0x1c0 .. +0x1d0) to the ignored cut with a0 = 0; else
     run 2   +0x194 .. +0x19c  a2 = 6, a0 = f, a1 = s, `jal` the bcmp wrapper;
     call 2  +0x1a0            bcmp (f, s, 6): the destination MAC (fr_dst b) against host_mac;
     +0x1a4                    `beq a0, zero`: equal goes to the desk cut (+0x2e4); else
     run 3   +0x1a8 .. +0x1b4  a1 = BROADCAST (0x21160, `auipc` / `addi` of A_OBJ 78), a2 = 6, a0 = f, `jal`;
     call 3  +0x1b8            bcmp (f, BROADCAST, 6);
     +0x1bc                    `beq a0, zero`: equal goes to the desk cut, else through the checked access at
                               s + 18184 to the ignored cut with a0 = 0.
   Each call is the statement's abcmp_realizes read at the walk's G journal (smb_bcmp_leaf: TransportGCg.v
   gx_call_leaf over YCbq.v aj_bcmp_at, image A's check_latest_sent_seg_cj.v cls_bcmp at image B's bcmp wrapper and
   G; smb_bcmp); it changes no byte outside its window [sp1 - 2 * ESTACK, sp1) and keeps every byte present (smb_mid),
   so every fact the cuts carry holds at the memory after it (smb_carry: acall_kept_g by TransportGFrame.v
   dk_kept_step_gw, the bytes at buf, TF, the read-only bytes and the OW.dn body range by DgnTransportBCg.v
   trans_src_ok_view, f's facts by trans_rd_ok_view and garr8_frame, the world relation by tw_kept). The bytes each
   call compares: f and f + 6 hold fr_dst b and fr_src b (cells 0 and 6 of frame_f_bytes buf b fj at fr_code b = 0),
   s holds S_cfg_host_mac Bw (tw_read_bytes), 0x21160 holds TSess.v BROADCAST (trans_rom_view_rd and the image's six
   bytes 0xff); their shadow: f's from decode_rd_ok of f, s's from g_s's zero shadow, BROADCAST's byte 6
   (transport_cells) and the rest of its group of 8 shadow bytes [0x7fffc228, 0x7fffc230): the zero shadow of
   [0x21140, 0x21160) before it and the three 0xf9 guard bytes 0x7fffc22d .. 0x7fffc22f after it (trans_srx_cells;
   BROADCAST is not 64-aligned). A result 0 is exactly the memeq of :273-277 (smb_memeq), so the path the code takes
   is srx_mac_bad Bw b: true ends at the ignored cut (srxb_m_mac: the model's world srx_ign Bw and result
   DIGINET_OK), false at the desk cut.
   Error path: __asan_report_load8 at +0x530 (0x87cb4), reached by `bne` at +0x1d0 when the shadow byte of s + 18184
   is not 0; it is 0 (trans_srx_cells), so the run passes to +0x1d4. No UBSan trap branch lies in +0x17c .. +0x1d0:
   both tests of s & 7 (+0x158, +0x178) are before the mac cut. *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YN3v YI04 YI00 YI08.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YG0s YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YImgTop.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c YO0f.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal YC4b.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
DgnTransportBSyms DgnTransportBList DgnTransportBAddr DgnTransportBPa DgnTransportBImg DgnTransportBPaLib YC1g.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k AsanCells TransportGB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TransportGRwB TransportGRunB TWorldB TImgB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import check_state_data_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_session_rx_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGFrame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import CanKit SrxBCut.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TImg TSess0 TSess.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Cells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog Require diginet_frame_parse_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module FCells := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.AsanCells.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.TransportGB.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
Module TSS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
Module DLib := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnLib.
Module SmLC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib.Cells.
Module SmPP := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.diginet_frame_parse_c.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* The symbolic states                                                 *)
(* ------------------------------------------------------------------ *)

(* The return addresses of the three calls: each is the `beq a0, zero` on the call's result. *)
Definition SMB_RET1 : Z := AF_diginet_session_rx + 0x190.
Definition SMB_RET2 : Z := AF_diginet_session_rx + 0x1a4.
Definition SMB_RET3 : Z := AF_diginet_session_rx + 0x1bc.
(* The shadow byte of g_s.stats.rx_ignored (s + 18184), the byte the check at +0x1c0 .. +0x1d0 loads. *)
Definition SMB_SH : Z := SHADOW_OFF + SRXB_RXIGN / 8.
Lemma SMB_SH_eq : SMB_SH = 2148222889.
Proof. reflexivity. Qed.
Definition SMB_R_sh : YP09.region :=
  YP09.mkRegion None SMB_SH (SMB_SH + 1) 0 0 [YP09.mkChunk SMB_SH (YP09.CVal 1 (SLit 0))].
(* The registers: the machine's (atoms 1 .. 31), s5 = s + 18152 and s11 = the shadow base as literals. *)
Definition SMB_REGS : list sv :=
  sr_set (sr_set sr_atoms (Z_to_bv 5 21) (SLit (SRX_S + 18152))) (Z_to_bv 5 27) (SLit SHADOW_OFF).
Definition ss_smb (pc : Z) : sstate := mkSS pc SMB_REGS [SMB_R_sh] None (mkFacts [] [] []).
Definition SMB_Bx : sv := SLit 0.
Definition SMB_B0 : Z * Z := (0, 0).
(* The registers no run of the piece writes (sp, gp, tp, s0, s1, s2, s3, s4, s6, s9, s10). *)
Definition SMB_KL : list (bv 5) :=
  [Z_to_bv 5 2; Z_to_bv 5 3; Z_to_bv 5 4; Z_to_bv 5 8; Z_to_bv 5 9; Z_to_bv 5 18; Z_to_bv 5 19; Z_to_bv 5 20;
   Z_to_bv 5 22; Z_to_bv 5 25; Z_to_bv 5 26].

(* The value of register r in the machine state of a symbolic state HS: its symbolic value, computed, then tac. *)
Ltac smb_reg HS r v H tac :=
  lazymatch type of HS with
  | st_ok_pi ?segsx ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok ?segsx ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_restrict_reg segsx Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | ?T => idtac "smb_reg: no match for" T; fail
  end.

(* The write obligation of a run from a state whose one region (the shadow byte) is not writable. *)
Ltac smb_awr :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end;
  repeat (apply awr_ok_x_cons;
    [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |]);
  apply awr_ok_x_nil.

(* ------------------------------------------------------------------ *)
(* The model facts: f's bytes, the MAC comparisons                     *)
(* ------------------------------------------------------------------ *)

(* memcmp (x, y, 6) == 0 as six byte equalities. *)
Lemma smb_memeq_iff : forall l1 l2, TS0.memeq 6 l1 l2 = true <->
  (forall i, 0 <= i < 6 -> DSpec.at8 l1 (Z.to_nat i) = DSpec.at8 l2 (Z.to_nat i)).
Proof.
  intros l1 l2. unfold TS0.memeq. rewrite forallb_forall. split.
  - intros H i Hi. apply Z.eqb_eq. apply H. apply in_seq. lia.
  - intros H n Hn. apply in_seq in Hn. apply Z.eqb_eq. replace n with (Z.to_nat (Z.of_nat n)) by lia. apply H. lia.
Qed.

(* Two 6-byte ranges read as the bytes of l1 and l2 agree byte by byte exactly when memeq says so. *)
Lemma smb_memeq : forall (rd : Z -> option Z) x y l1 l2,
  (forall i, 0 <= i < 6 -> rd (x + i) = Some (DSpec.at8 l1 (Z.to_nat i))) ->
  (forall i, 0 <= i < 6 -> rd (y + i) = Some (DSpec.at8 l2 (Z.to_nat i))) ->
  ((forall i, 0 <= i < 6 -> rd (x + i) = rd (y + i)) <-> TS0.memeq 6 l1 l2 = true).
Proof.
  intros rd x y l1 l2 H1 H2. rewrite smb_memeq_iff. split.
  - intros H i Hi. pose proof (H i Hi) as E. rewrite (H1 i Hi), (H2 i Hi) in E. injection E as E. exact E.
  - intros H i Hi. rewrite (H1 i Hi), (H2 i Hi), (H i Hi). reflexivity.
Qed.

(* A frame parsed with code 0 has at least 30 bytes. *)
Lemma smb_len30 : forall b, DSpec.fr_code b = 0 -> (30 <= length b)%nat.
Proof.
  intros b H. revert H. unfold DSpec.fr_code.
  destruct (Nat.ltb_spec (length b) 30) as [Hl | Hl]; intros H; [discriminate H | exact Hl].
Qed.

(* The byte values of a byte list. *)
Lemma smb_nth_map : forall (l : list byte) j, nth j (map (fun x : byte => bv_unsigned x) l) 0 = DSpec.at8 l j.
Proof.
  intros l j. unfold DSpec.at8, DSpec.bz. revert j.
  induction l as [|x l IH]; intros [|j]; cbn [map nth]; try reflexivity. apply IH.
Qed.

(* f's 64 bytes after a parse with code 0: the destination MAC, the source MAC, then the rest of parse_cells. *)
Lemma smb_ffb_split : forall buf b fj, DSpec.fr_code b = 0 ->
  frame_f_bytes buf b fj = map (fun x : byte => bv_unsigned x)
    (DSpec.fr_dst b ++ DSpec.fr_src b ++ SmLC.cells_bytes (skipn 2 (SmPP.parse_cells buf b fj))).
Proof.
  intros buf b fj H0. unfold frame_f_bytes, frame_f_cells. rewrite (proj2 (Z.eqb_eq _ _) H0). reflexivity.
Qed.

Lemma smb_ffb_len : forall buf b fj, DSpec.fr_code b = 0 -> length fj = 64%nat ->
  length (frame_f_bytes buf b fj) = 64%nat.
Proof.
  intros buf b fj H0 Hfj. pose proof (smb_len30 b H0) as L30.
  rewrite (smb_ffb_split buf b fj H0), length_map, !length_app.
  rewrite SmLC.cells_bytes_length.
  - cbn [skipn SmPP.parse_cells SmLC.cells_size SmLC.csize]. unfold DSpec.fr_dst, DSpec.fr_src.
    rewrite !length_firstn, length_skipn. lia.
  - cbn [skipn SmPP.parse_cells SmLC.cells_wf SmLC.cell_wf]. rewrite length_firstn, !length_skipn, Hfj.
    repeat split; lia.
Qed.

Lemma smb_ffb_dst : forall buf b fj j, DSpec.fr_code b = 0 -> (j < 6)%nat ->
  nth j (frame_f_bytes buf b fj) 0 = DSpec.at8 (DSpec.fr_dst b) j.
Proof.
  intros buf b fj j H0 Hj. pose proof (smb_len30 b H0) as L30.
  assert (L1 : length (DSpec.fr_dst b) = 6%nat) by (unfold DSpec.fr_dst; rewrite length_firstn; lia).
  rewrite (smb_ffb_split buf b fj H0), map_app, app_nth1 by (rewrite length_map; lia).
  apply smb_nth_map.
Qed.

Lemma smb_ffb_src : forall buf b fj j, DSpec.fr_code b = 0 -> (j < 6)%nat ->
  nth (6 + j) (frame_f_bytes buf b fj) 0 = DSpec.at8 (DSpec.fr_src b) j.
Proof.
  intros buf b fj j H0 Hj. pose proof (smb_len30 b H0) as L30.
  assert (L1 : length (DSpec.fr_dst b) = 6%nat) by (unfold DSpec.fr_dst; rewrite length_firstn; lia).
  assert (L2 : length (DSpec.fr_src b) = 6%nat)
    by (unfold DSpec.fr_src; rewrite length_firstn, length_skipn; lia).
  rewrite (smb_ffb_split buf b fj H0), map_app, app_nth2 by (rewrite length_map; lia).
  rewrite length_map, L1. replace (6 + j - 6)%nat with j by lia.
  rewrite map_app, app_nth1 by (rewrite length_map; lia).
  apply smb_nth_map.
Qed.

(* g_s.cfg.host_mac is the 6 bytes at g_s's world offset. *)
Lemma smb_host_sub : forall Bx, TW.S_cfg_host_mac Bx = TW.sub Bx (TW.OFF_g_s + 0) 6.
Proof. intros Bx. reflexivity. Qed.

(* The six bytes of BROADCAST (0x21160) in the image, decided over the loaded segments, are TSess.v BROADCAST. *)
Lemma smb_bc_rom : forall i, 0 <= i < 6 ->
  option_map (fun x : byte => bv_unsigned x) (YK11.seg_rom tfibsegs (Z_to_bv 64 (TRANS_BROADCAST + i))) =
  Some (DSpec.at8 TSS.BROADCAST (Z.to_nat i)).
Proof.
  intros i Hi. assert (Hc : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5) by lia.
  destruct Hc as [-> | [-> | [-> | [-> | [-> | ->]]]]]; vm_compute; reflexivity.
Qed.

(* BROADCAST lies in TRANS_RO_RD (its registered global's payload). *)
Lemma smb_bc_ro : forall i, 0 <= i < 6 -> trans_in_ro_rd (TRANS_BROADCAST + i).
Proof.
  intros i Hi. unfold trans_in_ro_rd, TRANS_RO_RD, TRANS_RO_GLOBALS. apply Exists_exists.
  exists (TRANS_BROADCAST, 6). split; [cbn; tauto|]. unfold in_zr. cbn [fst snd]. lia.
Qed.

(* A byte read 0 is a stored 0. *)
Lemma smb_vm0 : forall (H : word -> bool) (m : word -> option byte) a,
  aview tfibsegs H m a = Some 0 -> val_mem tfibsegs (mrestrict H m) a 1 0.
Proof.
  intros H m a Hv k Hk. assert (k = 0%nat) by lia. subst k. cbn [Z.of_nat]. rewrite Z.add_0_r.
  unfold aview in Hv. destruct (YP09.mbyte tfibsegs (mrestrict H m) a) as [x|] eqn:Eb; [|discriminate Hv].
  cbn in Hv. injection Hv as Hx. change (YO0f.le_byte 0 1 0) with 0.
  f_equal. apply bv_eq. rewrite Hx. reflexivity.
Qed.

(* The value of the j-th byte of a garr8 array under the view. *)
Lemma smb_garr_view : forall (H : word -> bool) (m : word -> option byte) p (l : list Z) j,
  garr8 tfibsegs (mrestrict H m) p l -> (j < length l)%nat ->
  aview tfibsegs H m (p + Z.of_nat j) = Some (nth j l 0).
Proof.
  intros H m p l j G Hj. pose proof (garr8_mbyte tfibsegs _ p l j G Hj) as Hm.
  destruct (G j Hj) as [_ Hr]. unfold aview. rewrite Hm. cbn [option_map]. f_equal.
  rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256. apply Z.mod_small. exact Hr.
Qed.

(* A memory equal pointwise to another has the same view and the same present bytes. *)
Lemma smb_view_eq : forall (H : word -> bool) (m m' : word -> option byte) a,
  (forall x, m' x = m x) -> aview tfibsegs H m' a = aview tfibsegs H m a.
Proof. intros H m m' a E. apply aview_eq_of. unfold mrestrict. rewrite E. reflexivity. Qed.

Lemma smb_pres_eq : forall (H : word -> bool) (m m' : word -> option byte) a,
  (forall x, m' x = m x) -> apresent H m a -> apresent H m' a.
Proof. intros H m m' a E (Hh & y & Hy). split; [exact Hh|]. exists y. rewrite E. exact Hy. Qed.

(* A run from a state whose one region is not writable leaves the memory as it was. *)
Lemma smb_frame0 : forall E (m m' : word -> option byte), frame_of E [SMB_R_sh] m m' -> forall x, m' x = m x.
Proof.
  intros E m m' HF x. apply HF. intros (rg & Hr & Ha). destruct Hr as [<- | []].
  unfold SMB_R_sh in Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. lia.
Qed.

(* A one-byte constant cell of the record, read at an AR state (image A's check_sent_frame_cgW.v cw_const1). *)
Lemma smb_const1 : forall {rc : YM05.RunCeil} (B : asyms) ly S (W : world tfibsegs) mem md a v s,
  @AR rc tfibsegs B ly S W mem md -> In (z1 (ANum a) v) (as_const B ly) -> 0 <= v < 256 -> a = s ->
  aview tfibsegs (w_H W) mem s = Some v.
Proof.
  intros rc B ly S W mem md a v s HAR Hin Hv <-.
  pose proof (am_const _ _ _ _ (proj1 HAR)) as HC.
  pose proof (proj1 (Forall_forall _ _) HC _ Hin) as Hc. unfold z1, c1, cell_holds in Hc.
  cbn [c_at c_w c_val aeval] in Hc. specialize (Hc 0%nat ltac:(lia)). rewrite Z.add_0_r in Hc.
  change (aeval B ly (ANum v)) with v in Hc.
  rewrite Hc. f_equal. unfold le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
  rewrite Z.shiftr_0_r. change (2 ^ 8) with 256.
  rewrite (Z.mod_small v 256) by lia. rewrite (Z.mod_small v 256) by lia. reflexivity.
Qed.

Lemma smb_const1_nn : forall {rc : YM05.RunCeil} (B : asyms) ly S (W : world tfibsegs) mem md a v s,
  @AR rc tfibsegs B ly S W mem md -> In (z1 (ANum a) v) (as_const B ly) -> 0 <= v < 256 -> a = s ->
  aview tfibsegs (w_H W) mem s <> None.
Proof.
  intros rc B ly S W mem md a v s H1 H2 H3 H4. rewrite (smb_const1 B ly S W mem md a v s H1 H2 H3 H4). discriminate.
Qed.

Section sm. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).
Local Abbreviation ajournal_gx := (@W_journalG.ajournal_gx rc tfib_sink_head segs B).

(* The bcmp wrapper's contract, read at the walk's own G journal (TransportGCg.v gx_call_leaf over YCbq.v
   aj_bcmp_at): image A's check_latest_sent_seg_cj.v cls_bcmp at image B's wrapper and G. *)
Lemma smb_bcmp_leaf : AR_laws segs B ->
  forall (STK sp0 : Z) FP ly S (W0 : world segs) mem0 md0 own lyc Sc (W : world segs)
         (memT : word -> option byte) mdc k (regsT : bvmap 5 word) (x y n o : Z) (raw : word),
  @abcmp_realizes fx rc segs B (transportb_sigma TB___interceptor_trampoline_bcmp) ->
  ajournal_gx TG.G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memT mdc k ->
  YK11.getr regsT 10 = w64 x -> YK11.getr regsT 11 = w64 y -> YK11.getr regsT 12 = w64 n ->
  0 <= n < 2 ^ 32 -> 0 <= x -> x + n <= 2 ^ 63 -> 0 <= y -> y + n <= 2 ^ 63 ->
  spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 2 * ESTACK - o <= STK ->
  YK11.getr regsT 3 = w64 (as_gp B) -> YK11.getr regsT 4 = w64 (as_tp B) ->
  YK11.getr regsT 1 = raw -> YK0s.ret_ok raw ->
  src_ok segs W regsT memT x n -> src_ok segs W regsT memT y n ->
  (forall a, x <= a < x + n -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o)) ->
  (forall a, y <= a < y + n -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o)) ->
  amem_range x n -> amem_range y n ->
  range_addressable (aview segs (w_H W) memT) SHADOW_OFF x n ->
  (0 < n -> shadow_hull_vis (aview segs (w_H W) memT) x n) ->
  range_addressable (aview segs (w_H W) memT) SHADOW_OFF y n ->
  (0 < n -> shadow_hull_vis (aview segs (w_H W) memT) y n) ->
  SRr segs W
    (mkCfg (@YK11.mkst fx regsT (Z_to_bv 64 (transportb_sigma TB___interceptor_trampoline_bcmp)) memT
              (YK11.seg_rom segs)) mdc)
    (fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
       c2 = mkCfg (@YK11.mkst fx regs2 raw mem2 (YK11.seg_rom segs)) md2 /\
       ajournal_gx TG.G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k /\
       (exists v : word, aregs_preserved regsT regs2 /\ YK11.getr regs2 10 = v /\
          (v = w64 0 <-> forall i, 0 <= i < n ->
             aview segs (w_H W) memT (x + i) = aview segs (w_H W) memT (y + i)) /\
          (forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o) ->
             aview segs (w_H W) mem2 a = aview segs (w_H W) memT a) /\
          (forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a))).
Proof.
  intros LAWS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memT mdc k regsT x y n o raw
    AM HJ H10 H11 H12 Hn Hx0 Hxn Hy0 Hyn Hsp Hal Hneg Hbud Hgp Htp Hra Hraw
    Hsx Hsy Hbx Hby Hmx Hmy Hrx Hhx Hry Hhy.
  apply (@gx_call_leaf fx rc tfib_sink_head segs B TG.G_HARNESS_B STK sp0 FP ly S W0 mem0 md0 own
           lyc Sc W memT mdc k _ raw _ HJ).
  intros memS HJi.
  eapply SRr_mono.
  { exact (@aj_bcmp_at fx rc tfib_sink_head segs B LAWS transportb_segs_low
             (transportb_sigma TB___interceptor_trampoline_bcmp) AM W regsT memT STK sp0 FP ly S W0 memS md0 own
             lyc Sc mdc k x y n o raw HJi H10 H11 H12 Hn Hx0 Hxn Hy0 Hyn Hsp Hal Hneg Hbud Hgp Htp Hra Hraw
             Hsx Hsy Hbx Hby Hmx Hmy Hrx Hhx Hry Hhy). }
  cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & v & Hc & HJ2 & HP & Hres & Hcmp & Hfr2 & Hpres2).
  split; [reflexivity|]. exists regs2, mem2, md2. split; [exact Hc|]. split; [exact HJ2|].
  exists v. split; [exact HP|]. split; [exact Hres|]. split; [exact Hcmp|]. split; [exact Hfr2 | exact Hpres2].
Qed.

(* The valuation of a run: the 32 registers at its start. *)
Definition smb_E (regs : bvmap 5 word) : env := Eimg (PI := PI_transportb) (Ereg regs []).

Lemma smb_ew : forall regs n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (smb_E regs) n = YK11.getr regs r.
Proof. intros regs n r Hn. unfold smb_E. apply can_ew_Eimg_Ereg_nat. exact Hn. Qed.
Lemma smb_den_reg : forall regs n (r : bv 5), Z.of_nat n = bv_unsigned r ->
  sv_denot (smb_E regs) (SOff n 0) = YK11.getr regs r.
Proof.
  intros regs n r Hn. cbn [sv_denot]. rewrite (smb_ew regs n r Hn), Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
Qed.
Lemma smb_env_img : forall regs, img_env VAL A_LIM (smb_E regs).
Proof. intros regs. unfold smb_E. apply Eimg_env. Qed.
Lemma smb_agree : forall regs, env_agree 32 (Ereg regs []) (smb_E regs).
Proof. intros regs. split; [intros n Hn; unfold smb_E; apply Eimg_low; unfold A_TEXT; lia | reflexivity]. Qed.

(* The state at pc with the shadow byte of s + 18184 as its one region (0 at every AR state). *)
Lemma smb_entry0 : forall ly S (W : world segs) regs mem md pc,
  trans_srx_cells B -> @AR rc segs B ly S W mem md ->
  st_ok_pi segs VAL (smb_E regs) (mkSS pc sr_atoms [SMB_R_sh] None (mkFacts [] [] []))
    (@YK11.mkst fx regs (Z_to_bv 64 (BASE + pc)) (mrestrict (w_H W) mem) (YK11.seg_rom segs)).
Proof.
  intros ly S W regs mem md pc HSC HAR.
  assert (Z0 : aview segs (w_H W) mem SMB_SH = Some 0).
  { replace SMB_SH with (FCells.shadow_addr SRXB_RXIGN) by reflexivity.
    apply (decode_zshadow_rd B ly S W mem md SRX_S (SRX_S + TW.SZ_g_s) SRXB_RXIGN HAR);
      [reflexivity | unfold SRXB_RXIGN; lia | unfold SRXB_RXIGN, SRX_S, TB_g_s, TW.SZ_g_s; lia | exact (proj1 HSC)]. }
  pose proof SMB_SH_eq as ESH.
  apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold region_ok, SMB_R_sh.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite ESH in Z0 |- *.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val segs (smb_E regs) _ 0 2148222889 1 (SLit 0) 0); [reflexivity | lia | lia |].
    rewrite Z.add_0_l. apply smb_vm0. exact Z0.
  - apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. repeat split.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. repeat split; exact I.
Qed.

Lemma smb_entry : forall ly S (W : world segs) regs mem md pc,
  trans_srx_cells B -> @AR rc segs B ly S W mem md ->
  YK11.getr regs (Z_to_bv 5 21) = w64 (SRX_S + 18152) -> YK11.getr regs (Z_to_bv 5 27) = w64 SHADOW_OFF ->
  st_ok_pi segs VAL (smb_E regs) (ss_smb pc)
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + pc)) mem (YK11.seg_rom segs))).
Proof.
  intros ly S W regs mem md pc HSC HAR R21 R27. rewrite restrict_mkst_fx.
  pose proof (smb_entry0 ly S W regs mem md pc HSC HAR) as H0.
  pose proof (st_ok_pi_pin_reg' _ _ _ (Z_to_bv 5 21) (SRX_S + 18152) H0 R21 eq_refl) as H1.
  pose proof (st_ok_pi_pin_reg' _ _ _ (Z_to_bv 5 27) SHADOW_OFF H1 R27 eq_refl) as H2.
  exact H2.
Qed.

(* ------------------------------------------------------------------ *)
(* The piece, at the mac cut's state                                   *)
(* ------------------------------------------------------------------ *)

Section walk.
Variables (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
  (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (lyc : alayout) (Sc : astate)
  (W : world segs) (memc : word -> option byte) (mdc : Model) (k : Z) (regs : bvmap 5 word)
  (buf now r : Z) (b fj : list byte) (TF : option TI.tframe) (Bw Bw' : list byte) (pos sp1 F : Z)
  (ly2 : alayout) (S2 : astate) (W2 : world segs) (mem2 : word -> option byte) (md2 : Model) (e : Z).
Hypothesis LAWS0 : srxb_laws B MT.
Hypothesis CALLS : srxb_calls B MT.
Hypothesis HFIX : srxb_fix B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf now r b TF Bw Bw' pos sp1 F.
Hypothesis HCUR : srxb_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b pos F ly2 S2 W2 mem2 md2 e.
Hypothesis HRD : srxb_rd B ly2 S2 W2 mem2 regs buf b TF Bw.
Hypothesis HDRD : decode_rd_ok W2 mem2 (F + SRX_F) FRAME_F_SIZE.
Hypothesis HFB : srxb_fbytes W2 mem2 F buf b fj.
Hypothesis HTW : tw_at TMAP_B (aview segs (w_H W2) mem2) Bw.
Hypothesis HCODE : DSpec.fr_code b = 0.
Hypothesis IGN : @srxb_ign_at fx rc B MT.
Hypothesis DESK : @srxb_desk_at fx rc B MT.

(* The stack and the frame: the entry journal's window, the realigned sp1, the own frame F below alloc_ceiling. *)
Lemma smb_stk : alloc_ceiling + STK <= sp0 /\ sp0 mod 16 = 0 /\ sp0 <= 2 ^ 47 /\
  sp0 - STK <= spZ regs - SRX_STK /\ spZ regs <= sp0 /\ spZ regs mod 16 = 0 /\
  spZ regs - 176 <= sp1 <= spZ regs - 160 /\ sp1 mod 32 = 0 /\
  4096 <= F /\ F mod 64 = 0 /\ F + 128 <= alloc_ceiling.
Proof.
  pose proof HFIX as (HJ0 & _ & _ & _ & _ & _ & _ & _ & _ & Hsp16 & Hlo & Hhi & _ & _ & _ & _ & _ & _ & _ & _ & _ &
    _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Esp1 & _ & HF0 & HF64 & HFc & _).
  pose proof HJ0 as (_ & _ & (memS & HJi & _) & _). rewrite !Z.add_0_r in HJi.
  pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
  pose proof Hstk as (Hsp0a & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
  unfold SRXB_FBYTES in HFc.
  assert (Hsp1 : spZ regs - 176 <= sp1 <= spZ regs - 160 /\ sp1 mod 32 = 0).
  { rewrite Esp1. unfold SRX_FRAME.
    pose proof (Z.div_mod (spZ regs - 160) 32 ltac:(lia)) as D.
    pose proof (Z.mod_pos_bound (spZ regs - 160) 32 ltac:(lia)) as M.
    pose proof (Z.div_mod (spZ regs) 16 ltac:(lia)) as D16. rewrite Hsp16, Z.add_0_r in D16.
    set (q := (spZ regs - 160) / 32) in *. set (r0 := (spZ regs - 160) mod 32) in *. set (t := spZ regs / 16) in *.
    split; [lia|]. rewrite Z.mul_comm, Z.mod_mul by lia. reflexivity. }
  destruct Hsp1 as [Hsp1 Hsp1a].
  repeat split; lia.
Qed.

(* The memory after a part of the piece: the journal there, every byte outside the bcmp wrapper's window
   [sp1 - 2 * ESTACK, sp1) as at the cut, every present byte still present. *)
Definition smb_mid (memX : word -> option byte) (mdX : Model) : Prop :=
  ajournal_gx TG.G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem0 md0 ((SRX_CID, pos) :: own) ly2 S2 W2 memX mdX (k + e) /\
  (forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 - 2 * ESTACK <= a < sp1) ->
     aview segs (w_H W2) memX a = aview segs (w_H W2) mem2 a) /\
  (forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) memX a).

Lemma smb_mid0 : smb_mid mem2 md2.
Proof.
  pose proof HCUR as (HJ2 & _). refine (conj HJ2 (conj _ _)); [intros a _ _; reflexivity | intros a Ha; exact Ha].
Qed.

Lemma smb_mid_AR : forall memX mdX, smb_mid memX mdX -> @AR rc segs B ly2 S2 W2 memX mdX.
Proof.
  intros memX mdX (HJ & _). exact (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ).
Qed.

Lemma smb_mid_run : forall memA mdA memB mdB, smb_mid memA mdA ->
  ajournal_gx TG.G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem0 md0 ((SRX_CID, pos) :: own) ly2 S2 W2 memB mdB (k + e) ->
  (forall x, memB x = memA x) -> smb_mid memB mdB.
Proof.
  intros memA mdA memB mdB (_ & KA & GA) HJ E. refine (conj HJ (conj _ _)).
  - intros a Ha Hn. rewrite (smb_view_eq _ memA memB a E). exact (KA a Ha Hn).
  - intros a Ha. apply (smb_pres_eq _ memA memB a E). exact (GA a Ha).
Qed.

(* A range of the caller's (at the call's entry state) outside the statement's window keeps its bytes. *)
Lemma smb_kv_rng : forall memX mdX q n, smb_mid memX mdX ->
  trans_src_ok B lyc Sc W memc q n -> decode_off_win regs SRX_STK q n ->
  forall a, q <= a < q + n -> aview segs (w_H W2) memX a = aview segs (w_H W2) mem2 a.
Proof.
  intros memX mdX q n (_ & KX & _) HS HO a Ha.
  pose proof LAWS0 as (_ & _ & _ & _ & _ & _ & _ & LAWS & _).
  pose proof HFIX as (HJ0 & _).
  pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ0) as HARc.
  pose proof smb_stk as (Hac & Hsp0a & H47 & Hlo & Hhi & Hsp16 & Hsp1 & Hsp1a & HF0 & HF64 & HFc).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (EST : ESTACK = 4096) by reflexivity. assert (ESTK : 8368 <= SRX_STK) by (vm_compute; congruence).
  destruct (trans_src_ok_place B LAWS lyc Sc W memc mdc q n HARc HS ltac:(lia)) as [P | P];
    unfold decode_off_win in HO; apply KX; lia.
Qed.

(* The shadow band lies below every stack. *)
Lemma smb_kv_band : forall memX mdX, smb_mid memX mdX ->
  forall s, kLowMemEnd <= s < kHighShadowEnd -> aview segs (w_H W2) memX s = aview segs (w_H W2) mem2 s.
Proof.
  intros memX mdX (_ & KX & _) s Hs.
  pose proof smb_stk as (Hac & Hsp0a & H47 & Hlo & Hhi & Hsp16 & Hsp1 & Hsp1a & HF0 & HF64 & HFc).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (EST : ESTACK = 4096) by reflexivity. assert (ESTK : 8368 <= SRX_STK) by (vm_compute; congruence).
  apply KX; lia.
Qed.

(* Every fact the two cuts after the piece carry, at a memory smb_mid relates to the cut's. *)
Lemma smb_carry : forall memX mdX, smb_mid memX mdX ->
  srxb_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b pos F ly2 S2 W2 memX mdX e /\
  srxb_rd B ly2 S2 W2 memX regs buf b TF Bw /\
  decode_rd_ok W2 memX (F + SRX_F) FRAME_F_SIZE /\
  srxb_fbytes W2 memX F buf b fj /\
  tw_at TMAP_B (aview segs (w_H W2) memX) Bw.
Proof.
  intros memX mdX HM. pose proof HM as (HJX & KX & GX).
  pose proof LAWS0 as (HSM & HCELLS & HSC & HGU & HGE & HRU & HRE & LAWS & MTL & MTF & SMP & ASF & FFL & HGX & HGNE).
  pose proof HFIX as (HJ0 & Hret & Hra & Hgp & Htp & H10 & H11 & H12 & H13 & Hsp16 & Hlo & Hhi & Hnow & Hbuf & Hgb &
    Hsrc & Hoff & Hbog & Htw0 & Hgf & Hm & HTF & HTFG & Hrom0 & Hap & Hinv & Hnd & Hc1 & Hc4 & Hc5 & Hc0 & Hc2 & Hev &
    Esp1 & EF & HF0 & HF64 & HFc & HFapp).
  pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ0) as HARc.
  pose proof smb_stk as (Hac & Hsp0a & H47 & Hlo' & Hhi' & Hsp16' & Hsp1 & Hsp1a & HF0' & HF64' & HFc').
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (EST : ESTACK = 4096) by reflexivity. assert (ESTK : 8368 <= SRX_STK) by (vm_compute; congruence).
  pose proof (smb_kv_band memX mdX HM) as KB.
  pose proof (smb_kv_rng memX mdX) as KVR.
  assert (KF : forall a, F <= a < F + 128 -> aview segs (w_H W2) memX a = aview segs (w_H W2) mem2 a)
    by (intros a Ha; apply KX; lia).
  pose proof HFB as (Hfj & Hgf2).
  pose proof (smb_ffb_len buf b fj HCODE Hfj) as LFF.
  refine (conj _ (conj _ (conj _ (conj _ _)))).
  - (* srxb_cur *)
    pose proof HCUR as (HJ2 & He & Hfrs & Hperm & HlyF & Hmo & HK & Hsaved & HFLw).
    refine (conj HJX (conj He (conj Hfrs (conj Hperm (conj HlyF (conj Hmo (conj _ (conj _ _)))))))).
    + apply (dk_kept_step_gw segs B LAWS transportb_segs_low TG.G_HARNESS_B lyc Sc W memc mdc W2 mem2 memX
        (spZ regs - SRX_STK) (spZ regs) (srx_wr b) (fun a => sp1 - 2 * ESTACK <= a < sp1) HARc HK KX GX).
      * intros a Ha _. cbv beta in Ha. lia.
      * intros bb m i Hb Hi Ha. exfalso. cbv beta in Ha.
        destruct (al_blocks _ _ LAWS lyc Sc W memc mdc bb m HARc Hb) as (_ & H4096 & Hbc & _). lia.
      * intros a Ha Hi _ _ _. exfalso. cbv beta in Ha. pose proof (transportb_segs_low a Hi) as Hl.
        unfold kLowMemEnd in Hl. lia.
      * intros cid pos' a Hin Hr Ha. exfalso. cbv beta in Ha.
        destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cid pos' HARc Hin) as (G4096 & Gce & _).
        pose proof (fs_frame_bytes_nonneg cid) as Hfs.
        destruct Hr as [Hr | Hr]; unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr; [lia|].
        pose proof (shadow_range_end (frame_addr lyc cid pos') (fs_frame_bytes cid) Hfs) as Hse.
        assert (Hd : (frame_addr lyc cid pos' + fs_frame_bytes cid) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia).
        unfold shadow_addr, SHADOW_OFF in *. change (2 ^ 47 / 8) with (2 ^ 44) in Hd. lia.
    + rewrite Forall_forall in Hsaved |- *. intros o Ho. rewrite <- (Hsaved o Ho).
      assert (Hob : 8 <= fst o <= 104).
      { unfold SRXB_SAVED in Ho. cbn [In] in Ho.
        repeat (destruct Ho as [<- | Ho]; [cbn [fst]; lia|]). destruct Ho. }
      apply rdword_ext. intros i Hi. apply KX; lia.
    + rewrite <- HFLw. unfold SRXB_FBYTES. apply rdword_ext. intros i Hi. apply KF. lia.
  - (* srxb_rd *)
    pose proof HRD as (Hgb2 & Hsrc2 & Htf2 & Hrom2 & Hnd2).
    refine (conj _ (conj _ (conj _ (conj _ _)))).
    + apply (garr8_frame segs (mrestrict (w_H W2) mem2) (mrestrict (w_H W2) memX) buf (TW.zs b) Hgb2).
      intros a Ha. apply (mbyte_of_aview segs). unfold TW.zs in Ha. rewrite length_map in Ha.
      exact (KVR buf _ HM Hsrc Hoff a Ha).
    + apply (trans_src_ok_view B ly2 S2 W2 W2 mem2 memX buf _ Hsrc2); [| exact KB].
      exact (KVR buf _ HM Hsrc Hoff).
    + destruct TF as [fr|]; [|exact I].
      destruct Htf2 as (Ha0 & Hg & Hs & Ho). destruct HTF as (_ & _ & Hs0 & Ho0).
      refine (conj Ha0 (conj _ (conj _ Ho))).
      * apply (garr8_frame segs (mrestrict (w_H W2) mem2) (mrestrict (w_H W2) memX) _ _ Hg).
        intros a Ha. apply (mbyte_of_aview segs). rewrite length_map in Ha.
        exact (KVR _ _ HM Hs0 Ho0 a Ha).
      * apply (trans_src_ok_view B ly2 S2 W2 W2 mem2 memX _ _ Hs); [| exact KB].
        exact (KVR _ _ HM Hs0 Ho0).
    + intros a Ha. pose proof (trans_ro_rd_bounds a Ha) as Hb. rewrite <- (Hrom2 a Ha). apply KX; lia.
    + intros G1 G2 G3 G4 G5 G6 G7 G8.
      destruct (Hnd2 G1 G2 G3 G4 G5 G6 G7 G8) as (Hs & Ho).
      destruct (Hnd G1 G2 G3 G4 G5 G6 G7 G8) as (Hs0 & Ho0).
      split; [|exact Ho].
      apply (trans_src_ok_view B ly2 S2 W2 W2 mem2 memX _ _ Hs); [| exact KB].
      exact (KVR _ _ HM Hs0 Ho0).
  - (* f's 64 bytes, usable *)
    apply (trans_rd_ok_view W2 W2 mem2 memX _ _ HDRD); [| exact KB].
    intros a Ha. unfold SRX_F, FRAME_F_SIZE in Ha. apply KF. lia.
  - (* f's 64 bytes, their values *)
    split; [exact Hfj|].
    apply (garr8_frame segs (mrestrict (w_H W2) mem2) (mrestrict (w_H W2) memX) _ _ Hgf2).
    intros a Ha. apply (mbyte_of_aview segs). rewrite LFF in Ha. unfold SRX_F in Ha. apply KF. lia.
  - (* the world relation *)
    apply (tw_kept TMAP_B (aview segs (w_H W2) mem2)); [exact HTW|].
    intros x Hx. pose proof (TMAP_B_hull x Hx) as Hh. unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in Hh.
    apply KX; lia.
Qed.

(* ---- the three pairs of ranges the calls compare, at a memory smb_mid relates to the cut's ---- *)

Lemma smb_rng_f : forall memX mdX j, smb_mid memX mdX -> 0 <= j <= 6 ->
  decode_rd_ok W2 memX (F + SRX_F + j) 6.
Proof.
  intros memX mdX j HM Hj. destruct (smb_carry memX mdX HM) as (_ & _ & HD & _).
  apply (trans_rd_ok_sub W2 memX (F + SRX_F) FRAME_F_SIZE); [exact HD | lia | unfold FRAME_F_SIZE; lia | lia].
Qed.

Lemma smb_val_f : forall memX mdX i, smb_mid memX mdX -> 0 <= i < 64 ->
  aview segs (w_H W2) memX (F + SRX_F + i) = Some (nth (Z.to_nat i) (frame_f_bytes buf b fj) 0).
Proof.
  intros memX mdX i HM Hi. destruct (smb_carry memX mdX HM) as (_ & _ & _ & (Hfj & HG) & _).
  replace (F + SRX_F + i) with (F + SRX_F + Z.of_nat (Z.to_nat i)) by lia.
  apply smb_garr_view; [exact HG|]. rewrite (smb_ffb_len buf b fj HCODE Hfj). lia.
Qed.

Lemma smb_val_dst : forall memX mdX, smb_mid memX mdX -> forall i, 0 <= i < 6 ->
  aview segs (w_H W2) memX (F + SRX_F + i) = Some (DSpec.at8 (DSpec.fr_dst b) (Z.to_nat i)).
Proof.
  intros memX mdX HM i Hi. rewrite (smb_val_f memX mdX i HM ltac:(lia)).
  rewrite (smb_ffb_dst buf b fj (Z.to_nat i) HCODE ltac:(lia)). reflexivity.
Qed.

Lemma smb_val_src : forall memX mdX, smb_mid memX mdX -> forall i, 0 <= i < 6 ->
  aview segs (w_H W2) memX (F + SRX_F + 6 + i) = Some (DSpec.at8 (DSpec.fr_src b) (Z.to_nat i)).
Proof.
  intros memX mdX HM i Hi. replace (F + SRX_F + 6 + i) with (F + SRX_F + (6 + i)) by lia.
  rewrite (smb_val_f memX mdX (6 + i) HM ltac:(lia)).
  replace (Z.to_nat (6 + i)) with (6 + Z.to_nat i)%nat by lia.
  rewrite (smb_ffb_src buf b fj (Z.to_nat i) HCODE ltac:(lia)). reflexivity.
Qed.

Lemma smb_rng_s : forall memX mdX, smb_mid memX mdX -> decode_rd_ok W2 memX SRX_S 6.
Proof.
  intros memX mdX HM. pose proof (smb_mid_AR memX mdX HM) as HAR.
  pose proof LAWS0 as (_ & _ & HSC & _).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  destruct (decode_zshadow_ra B ly2 S2 W2 memX mdX SRX_S (SRX_S + TW.SZ_g_s) SRX_S 6 HAR (proj1 HSC) ltac:(lia)
    ltac:(vm_compute; congruence) ltac:(vm_compute; congruence)) as [RA HH].
  split; [|split; [exact RA|split; [exact HH|split; [|split]]]].
  - intros a Ha. apply (gx_rw_vis segs TG.G_HARNESS_B a G_HARNESS_B_rw).
    unfold inG. apply Exists_exists. exists (TB_g_s, TW.SZ_g_s).
    split; [exact (TMAP_B_in_G _ _ _ TMAP_B_g_s) | unfold in_zr, SRX_S, TB_g_s, TW.SZ_g_s in *; cbn [fst snd]; lia].
  - unfold amem_range, SRX_S, TB_g_s. lia.
  - unfold SRX_S, TB_g_s. lia.
  - unfold SRX_S, TB_g_s. lia.
Qed.

Lemma smb_val_s : forall memX mdX, smb_mid memX mdX -> forall i, 0 <= i < 6 ->
  aview segs (w_H W2) memX (SRX_S + i) = Some (DSpec.at8 (TW.S_cfg_host_mac Bw) (Z.to_nat i)).
Proof.
  intros memX mdX HM i Hi. destruct (smb_carry memX mdX HM) as (_ & _ & _ & _ & HTX).
  pose proof (tw_read_bytes TMAP_B (aview segs (w_H W2) memX) Bw TW.OFF_g_s TB_g_s TW.SZ_g_s 0 6 (Z.to_nat i)
    TMAP_B_ok HTX TMAP_B_g_s ltac:(lia) ltac:(unfold TW.SZ_g_s; lia) ltac:(lia)) as R.
  replace (TB_g_s + 0 + Z.of_nat (Z.to_nat i)) with (SRX_S + i) in R by (unfold SRX_S; lia).
  rewrite R, smb_host_sub. reflexivity.
Qed.

Lemma smb_rng_bc : forall memX mdX, smb_mid memX mdX -> decode_rd_ok W2 memX TRANS_BROADCAST 6.
Proof.
  intros memX mdX HM. pose proof (smb_mid_AR memX mdX HM) as HAR.
  pose proof LAWS0 as (_ & HCELLS & HSC & _).
  destruct (smb_carry memX mdX HM) as (_ & (_ & _ & _ & HROM & _) & _).
  destruct (HCELLS ly2) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
    _ & _ & _ & _ & _ & _ & _ & _ & _ & RB & _).
  destruct HSC as (_ & HZ & HF9). destruct (HF9 ly2) as (R8 & R16 & R24).
  assert (ZS : forall T s, T mod 8 = 0 -> TRANS_BROADCAST - 32 <= T -> T + 8 <= TRANS_BROADCAST ->
            FCells.shadow_addr T = s -> aview segs (w_H W2) memX s = Some 0).
  { intros T s' H1 H2 H3 <-.
    exact (decode_zshadow_rd B ly2 S2 W2 memX mdX (TRANS_BROADCAST - 32) TRANS_BROADCAST T HAR H1 H2 H3 HZ). }
  split; [|split; [|split; [|split; [|split]]]].
  - intros a Ha. replace a with (TRANS_BROADCAST + (a - TRANS_BROADCAST)) by lia.
    rewrite (HROM _ (smb_bc_ro (a - TRANS_BROADCAST) ltac:(lia))), (smb_bc_rom (a - TRANS_BROADCAST) ltac:(lia)).
    discriminate.
  - intros x Hx. exists 6. split.
    + eapply (smb_const1 B ly2 S2 W2 memX mdX); [exact HAR | exact RB | lia |].
      unfold FCells.shadow_addr, FCells.ASAN_K, TRANS_BROADCAST, shadow_of_addr, SHADOW_OFF in *.
      Z.div_mod_to_equations. lia.
    + unfold saddr_ok, TRANS_BROADCAST in *. right. Z.div_mod_to_equations. lia.
  - intros s' Hs.
    assert (E1 : shadow_addr TRANS_BROADCAST / 8 * 8 = 0x7fffc228) by (vm_compute; reflexivity).
    assert (E2 : shadow_addr (TRANS_BROADCAST + 6 - 1) / 8 * 8 + 8 = 0x7fffc230) by (vm_compute; reflexivity).
    rewrite E1, E2 in Hs.
    assert (Hc : s' = 0x7fffc228 \/ s' = 0x7fffc229 \/ s' = 0x7fffc22a \/ s' = 0x7fffc22b \/ s' = 0x7fffc22c \/
                 s' = 0x7fffc22d \/ s' = 0x7fffc22e \/ s' = 0x7fffc22f) by lia.
    destruct Hc as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]];
      [ rewrite (ZS (TRANS_BROADCAST - 32)); [discriminate | reflexivity | lia | lia | reflexivity]
      | rewrite (ZS (TRANS_BROADCAST - 24)); [discriminate | reflexivity | lia | lia | reflexivity]
      | rewrite (ZS (TRANS_BROADCAST - 16)); [discriminate | reflexivity | lia | lia | reflexivity]
      | rewrite (ZS (TRANS_BROADCAST - 8)); [discriminate | reflexivity | lia | lia | reflexivity]
      | eapply smb_const1_nn; [exact HAR | exact RB | lia | reflexivity]
      | eapply smb_const1_nn; [exact HAR | exact R8 | lia | reflexivity]
      | eapply smb_const1_nn; [exact HAR | exact R16 | lia | reflexivity]
      | eapply smb_const1_nn; [exact HAR | exact R24 | lia | reflexivity] ].
  - unfold amem_range, kLowMemEnd, TRANS_BROADCAST. lia.
  - unfold TRANS_BROADCAST. lia.
  - unfold TRANS_BROADCAST. lia.
Qed.

Lemma smb_val_bc : forall memX mdX, smb_mid memX mdX -> forall i, 0 <= i < 6 ->
  aview segs (w_H W2) memX (TRANS_BROADCAST + i) = Some (DSpec.at8 TSS.BROADCAST (Z.to_nat i)).
Proof.
  intros memX mdX HM i Hi. destruct (smb_carry memX mdX HM) as (_ & (_ & _ & _ & HROM & _) & _).
  rewrite (HROM _ (smb_bc_ro i Hi)). exact (smb_bc_rom i Hi).
Qed.

(* ---- one call of the bcmp wrapper ---- *)

Lemma smb_bcmp : forall (memT : word -> option byte) (mdT : Model) (regsT : bvmap 5 word) (x y : Z)
    (l1 l2 : list byte) (raw : word) (Q : world segs -> config -> Prop),
  smb_mid memT mdT ->
  YK11.getr regsT (Z_to_bv 5 10) = w64 x -> YK11.getr regsT (Z_to_bv 5 11) = w64 y ->
  YK11.getr regsT (Z_to_bv 5 12) = w64 6 ->
  YK11.getr regsT (Z_to_bv 5 2) = w64 sp1 -> YK11.getr regsT (Z_to_bv 5 3) = w64 (as_gp B) ->
  YK11.getr regsT (Z_to_bv 5 4) = w64 (as_tp B) ->
  YK11.getr regsT (Z_to_bv 5 1) = raw -> YK0s.ret_ok raw ->
  decode_rd_ok W2 memT x 6 -> decode_rd_ok W2 memT y 6 -> x + 6 <= alloc_ceiling -> y + 6 <= alloc_ceiling ->
  (forall i, 0 <= i < 6 -> aview segs (w_H W2) memT (x + i) = Some (DSpec.at8 l1 (Z.to_nat i))) ->
  (forall i, 0 <= i < 6 -> aview segs (w_H W2) memT (y + i) = Some (DSpec.at8 l2 (Z.to_nat i))) ->
  (forall regsR memR mdR, smb_mid memR mdR -> aregs_preserved regsT regsR ->
     (YK11.getr regsR (Z_to_bv 5 10) = w64 0 <-> TS0.memeq 6 l1 l2 = true) ->
     SRr segs W2 (mkCfg (@YK11.mkst fx regsR raw memR (YK11.seg_rom segs)) mdR) Q) ->
  SRr segs W2 (mkCfg (@YK11.mkst fx regsT (Z_to_bv 64 (transportb_sigma TB___interceptor_trampoline_bcmp)) memT
    (YK11.seg_rom segs)) mdT) Q.
Proof.
  intros memT mdT regsT x y l1 l2 raw Q (HJT & KT & GT) R10 R11 R12 R2 R3 R4 R1 Hraw
    (VX & RAX & HHX & AMX & X0 & X63) (VY & RAY & HHY & AMY & Y0 & Y63) BX BY EX EY K.
  pose proof LAWS0 as (_ & _ & _ & _ & _ & _ & _ & LAWS & _).
  pose proof CALLS as (_ & _ & ABCMP & _).
  pose proof smb_stk as (Hac & Hsp0a & H47 & Hlo & Hhi & Hsp16 & Hsp1 & Hsp1a & HF0 & HF64 & HFc).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (EST : ESTACK = 4096) by reflexivity. assert (ESTK : 8368 <= SRX_STK) by (vm_compute; congruence).
  assert (USP : spZ regsT = sp1)
    by (change (bv_unsigned (YK11.getr regsT (Z_to_bv 5 2)) = sp1); rewrite R2; unfold w64;
        apply unsigned_lit_small; lia).
  assert (Hal : (sp1 - sp0) mod 16 = 0).
  { pose proof (Z.div_mod sp1 32 ltac:(lia)) as D1. pose proof (Z.div_mod sp0 16 ltac:(lia)) as D2.
    rewrite Hsp1a, Z.add_0_r in D1. rewrite Hsp0a, Z.add_0_r in D2.
    rewrite D1, D2. replace (32 * (sp1 / 32) - 16 * (sp0 / 16)) with ((2 * (sp1 / 32) - sp0 / 16) * 16) by ring.
    apply Z.mod_mul. lia. }
  eapply SRr_bind.
  { exact (smb_bcmp_leaf LAWS STK sp0 FP ly S W0 mem0 md0 ((SRX_CID, pos) :: own) ly2 S2 W2 memT mdT
      (k + e) regsT x y 6 (sp1 - sp0) raw (ABCMP fx) HJT R10 R11 R12 ltac:(lia) X0 X63 Y0 Y63
      ltac:(rewrite USP; lia) Hal ltac:(lia) ltac:(lia) R3 R4 R1 Hraw
      ltac:(intros a Ha; split; [exact (VX a Ha) | rewrite USP; lia])
      ltac:(intros a Ha; split; [exact (VY a Ha) | rewrite USP; lia])
      ltac:(intros a Ha; lia) ltac:(intros a Ha; lia) AMX AMY RAX (fun _ => HHX) RAY (fun _ => HHY)). }
  cbv beta. intros W3 c3 _ (-> & regsR & memR & mdR & -> & HJR & v & HP & Hres & Hcmp & Hfr & Hpres).
  apply (K regsR memR mdR).
  - refine (conj HJR (conj _ _)).
    + intros a Ha Hn. rewrite (Hfr a Ha ltac:(lia)). exact (KT a Ha Hn).
    + intros a Ha. exact (Hpres a (GT a Ha)).
  - exact HP.
  - subst v. etransitivity; [exact Hcmp | exact (smb_memeq _ x y l1 l2 EX EY)].
Qed.

(* ---- the registers ---- *)

Lemma smb_regs_mk : forall rg rg', srxb_regs_base regs rg now sp1 F ->
  (forall r0, In r0 SMB_KL -> YK11.getr rg' r0 = YK11.getr rg r0) ->
  YK11.getr rg' (Z_to_bv 5 21) = w64 (SRX_S + 18152) -> YK11.getr rg' (Z_to_bv 5 27) = w64 SHADOW_OFF ->
  YK11.getr rg' (Z_to_bv 5 23) = w64 (F + SRX_F + 6) ->
  srxb_regs_desk regs rg' now sp1 F.
Proof.
  intros rg rg' ((R2 & R3 & R4 & R8 & R9 & R18 & R19 & R20 & R25 & R26 & R27) & R21 & R22) KR Q21 Q27 Q23.
  assert (IN : forall n, In (Z_to_bv 5 n) SMB_KL -> YK11.getr rg' (Z_to_bv 5 n) = YK11.getr rg (Z_to_bv 5 n))
    by (intros n Hn; exact (KR _ Hn)).
  refine (conj (conj (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))))))
    (conj Q21 _)) Q23).
  - exact (eq_trans (IN 2 ltac:(unfold SMB_KL; cbn [In]; repeat (first [left; reflexivity | right]))) R2).
  - exact (eq_trans (IN 3 ltac:(unfold SMB_KL; cbn [In]; repeat (first [left; reflexivity | right]))) R3).
  - exact (eq_trans (IN 4 ltac:(unfold SMB_KL; cbn [In]; repeat (first [left; reflexivity | right]))) R4).
  - exact (eq_trans (IN 8 ltac:(unfold SMB_KL; cbn [In]; repeat (first [left; reflexivity | right]))) R8).
  - exact (eq_trans (IN 9 ltac:(unfold SMB_KL; cbn [In]; repeat (first [left; reflexivity | right]))) R9).
  - exact (eq_trans (IN 18 ltac:(unfold SMB_KL; cbn [In]; repeat (first [left; reflexivity | right]))) R18).
  - exact (eq_trans (IN 19 ltac:(unfold SMB_KL; cbn [In]; repeat (first [left; reflexivity | right]))) R19).
  - exact (eq_trans (IN 20 ltac:(unfold SMB_KL; cbn [In]; repeat (first [left; reflexivity | right]))) R20).
  - exact (eq_trans (IN 25 ltac:(unfold SMB_KL; cbn [In]; repeat (first [left; reflexivity | right]))) R25).
  - exact (eq_trans (IN 26 ltac:(unfold SMB_KL; cbn [In]; repeat (first [left; reflexivity | right]))) R26).
  - exact Q27.
  - exact (eq_trans (IN 22 ltac:(unfold SMB_KL; cbn [In]; repeat (first [left; reflexivity | right]))) R22).
Qed.

Lemma smb_regs_pres : forall rg rg', srxb_regs_desk regs rg now sp1 F -> aregs_preserved rg rg' ->
  srxb_regs_desk regs rg' now sp1 F.
Proof.
  intros rg rg' (((R2 & R3 & R4 & R8 & R9 & R18 & R19 & R20 & R25 & R26 & R27) & R21 & R22) & R23) HP.
  assert (P : forall n, acallee_saved n -> YK11.getr rg' (Z_to_bv 5 n) = YK11.getr rg (Z_to_bv 5 n)) by exact HP.
  refine (conj (conj (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))))))
    (conj _ _)) _).
  - exact (eq_trans (P 2 ltac:(hnf; lia)) R2).
  - exact (eq_trans (P 3 ltac:(hnf; lia)) R3).
  - exact (eq_trans (P 4 ltac:(hnf; lia)) R4).
  - exact (eq_trans (P 8 ltac:(hnf; lia)) R8).
  - exact (eq_trans (P 9 ltac:(hnf; lia)) R9).
  - exact (eq_trans (P 18 ltac:(hnf; lia)) R18).
  - exact (eq_trans (P 19 ltac:(hnf; lia)) R19).
  - exact (eq_trans (P 20 ltac:(hnf; lia)) R20).
  - exact (eq_trans (P 25 ltac:(hnf; lia)) R25).
  - exact (eq_trans (P 26 ltac:(hnf; lia)) R26).
  - exact (eq_trans (P 27 ltac:(hnf; lia)) R27).
  - exact (eq_trans (P 21 ltac:(hnf; lia)) R21).
  - exact (eq_trans (P 22 ltac:(hnf; lia)) R22).
  - exact (eq_trans (P 23 ltac:(hnf; lia)) R23).
Qed.

(* ---- the two exits ---- *)

(* The ignored cut, +0x1d4: srx_mac_bad Bw b, so the model's world is srx_ign Bw and its result DIGINET_OK = 0, the
   value a0 holds (the shadow byte the check loaded). *)
Lemma smb_exit_ign : forall memX mdX regsX, smb_mid memX mdX ->
  srxb_regs_base regs regsX now sp1 F -> YK11.getr regsX (Z_to_bv 5 10) = w64 0 ->
  YK11.getr regsX (Z_to_bv 5 11) = w64 SRXB_RXIGN -> srx_mac_bad Bw b = true ->
  SRr segs W2 (mkCfg (@YK11.mkst fx regsX (Z_to_bv 64 (BASE + SRXB_IGN)) memX (YK11.seg_rom segs)) mdX)
    (@transport_srx_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' b r).
Proof.
  intros memX mdX regsX HM RB R10 R11 HMB.
  pose proof HFIX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hgf & Hm & _).
  pose proof (srxb_m_mac timg_B TF Bw b now HCODE HMB) as Hm'. rewrite Hm in Hm'.
  destruct (srxb_some_inv _ _ _ _ Hm') as [EBw Er].
  destruct (smb_carry memX mdX HM) as (CUR & _ & _ & _ & TWX).
  apply (IGN LAWS0 CALLS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf now r b TF Bw Bw' Bw pos sp1 F
    ly2 S2 W2 memX mdX e regsX HFIX CUR TWX Hgf EBw).
  refine (conj RB (conj _ R11)). rewrite Er. exact R10.
Qed.

(* The desk cut, +0x2e4: the MACs not refused. *)
Lemma smb_exit_desk : forall memX mdX regsX, smb_mid memX mdX ->
  srxb_regs_desk regs regsX now sp1 F -> srx_mac_bad Bw b = false ->
  SRr segs W2 (mkCfg (@YK11.mkst fx regsX (Z_to_bv 64 (BASE + SRXB_DESK)) memX (YK11.seg_rom segs)) mdX)
    (@transport_srx_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' b r).
Proof.
  intros memX mdX regsX HM RD HMB.
  destruct (smb_carry memX mdX HM) as (CUR & RDX & DRX & FBX & TWX).
  exact (DESK LAWS0 CALLS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf now r b fj TF Bw Bw' pos sp1 F
    ly2 S2 W2 memX mdX e regsX HFIX CUR RDX DRX FBX TWX HCODE HMB RD).
Qed.

(* ---- the walk ---- *)

(* A register the run did not write: its value at the run's start. *)
Ltac smb_kept rg n r G :=
  cbn [sv_denot]; rewrite (smb_ew rg n r eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact G.

(* The registers the cuts read, at the state HS a run from the registers rg reached (rg's s7 is already f + 6). *)
Ltac smb_regs_at HS rg RGp RG :=
  let Q21 := fresh "Q21" in let Q27 := fresh "Q27" in let Q23 := fresh "Q23" in let KR := fresh "KR" in
  smb_reg HS (21%bv : bv 5) (w64 (SRX_S + 18152)) Q21 ltac:(reflexivity);
  smb_reg HS (27%bv : bv 5) (w64 SHADOW_OFF) Q27 ltac:(reflexivity);
  smb_reg HS (23%bv : bv 5) (w64 (F + SRX_F + 6)) Q23 ltac:(smb_kept rg 23%nat (23%bv : bv 5) (proj2 RGp));
  first [ pose proof (regs_kept_of_st_ok_pi _ _ _ rg [] SMB_KL HS (smb_agree rg) ltac:(vm_compute; reflexivity)) as KR
        | pose proof (regs_kept_of_st_ok tfibsegs _ _ _ rg [] SMB_KL HS (smb_agree rg) ltac:(vm_compute; reflexivity))
            as KR ];
  pose proof (smb_regs_mk rg _ (proj1 RGp) KR Q21 Q27 Q23) as RG;
  clear Q21 Q27 Q23 KR.

Lemma smb_walk : forall regs2, srxb_regs_base regs regs2 now sp1 F ->
  SRr segs W2 (mkCfg (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + SRXB_MAC)) mem2 (YK11.seg_rom segs)) md2)
    (@transport_srx_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' b r).
Proof.
intros regs2 HREGS.
pose proof LAWS0 as (HSM & HCELLS & HSC & HGU & HGE & HRU & HRE & LAWS & MTL & MTF & SMP & ASF & FFL & HGX & HGNE).
pose proof HFIX as (_ & _ & _ & Hgp & Htp & _).
pose proof smb_stk as (Hac & Hsp0a & H47 & Hlo & Hhi & Hsp16 & Hsp1 & Hsp1a & HF0 & HF64 & HFc).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
set (Q := @transport_srx_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' b r).
pose proof (@paj_run_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B HGX 0 [])
  as RUN.
pose proof (@paj_run_to_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B HGX 0
  []) as RUNTO.
pose proof (paj_branch (fx := fx) (PI := PI_transportb)) as BR.
pose proof smb_mid0 as MID0.
pose proof HREGS as ((R2 & R3 & R4 & R8 & R9 & R18 & R19 & R20 & R25 & R26 & R27) & R21 & R22).
(* ---- run 1, +0x17c .. +0x18c: s7 = f + 6, a2 = 6, a0 = f + 6, a1 = s, `jal` the bcmp wrapper ---- *)
pose proof (smb_entry ly2 S2 W2 regs2 mem2 md2 SRXB_MAC HSC (smb_mid_AR mem2 md2 MID0) R21 R27) as HS.
assert (HEI : img_env VAL A_LIM (smb_E regs2)) by apply smb_env_img.
assert (SHOK : sh_ok segs SMB_Bx (@nil shent) (smb_E regs2) (mrestrict (w_H W2) mem2)) by constructor.
pose proof MID0 as (HJ & _).
paj_run_tok RUN HS HJ SHOK SMB_B0.
{ smb_awr. }
set (md1 := with_vm_backing (m_vm_lazy md2) mat md2) in *. clearbody md1. clear mat.
pose proof (smb_mid_run mem2 md2 (ms_mem ms) md1 MID0 HJ (smb_frame0 _ _ _ HF)) as MID1.
smb_reg HS (10%bv : bv 5) (w64 (F + SRX_F + 6)) Q10
  ltac:(cbn [sv_denot]; rewrite (smb_ew regs2 22 (22%bv : bv 5) eq_refl), R22; unfold w64;
        rewrite unsigned_lit_small by (unfold SRX_F; lia); reflexivity).
smb_reg HS (23%bv : bv 5) (w64 (F + SRX_F + 6)) Q23
  ltac:(cbn [sv_denot]; rewrite (smb_ew regs2 22 (22%bv : bv 5) eq_refl), R22; unfold w64;
        rewrite unsigned_lit_small by (unfold SRX_F; lia); reflexivity).
smb_reg HS (11%bv : bv 5) (w64 SRX_S) Q11 ltac:(smb_kept regs2 20%nat (20%bv : bv 5) R20).
smb_reg HS (12%bv : bv 5) (w64 6) Q12 ltac:(reflexivity).
smb_reg HS (2%bv : bv 5) (w64 sp1) Q2 ltac:(smb_kept regs2 2%nat (2%bv : bv 5) R2).
smb_reg HS (3%bv : bv 5) (w64 (as_gp B)) Q3 ltac:(smb_kept regs2 3%nat (3%bv : bv 5) (eq_trans R3 Hgp)).
smb_reg HS (4%bv : bv 5) (w64 (as_tp B)) Q4 ltac:(smb_kept regs2 4%nat (4%bv : bv 5) (eq_trans R4 Htp)).
smb_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 26228)) Q1 ltac:(apply codeptr_val; exact HEI).
smb_reg HS (21%bv : bv 5) (w64 (SRX_S + 18152)) Q21 ltac:(reflexivity).
smb_reg HS (27%bv : bv 5) (w64 SHADOW_OFF) Q27 ltac:(reflexivity).
pose proof (regs_kept_of_st_ok tfibsegs _ _ _ regs2 [] SMB_KL HS (smb_agree regs2) ltac:(vm_compute; reflexivity)) as KR.
pose proof (smb_regs_mk regs2 _ HREGS KR Q21 Q27 Q23) as RG1.
clear KR Q21 Q27 Q23.
pmkst HS.
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Qx =>
  change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (transportb_sigma TB___interceptor_trampoline_bcmp)) mm rom)
    mdx) Qx) end.
(* ---- call 1, +0x18c: bcmp (f + 6, s, 6) ---- *)
apply (smb_bcmp (ms_mem ms) md1 (ms_regs ms) (F + SRX_F + 6) SRX_S (DSpec.fr_src b) (TW.S_cfg_host_mac Bw)
  (Z_to_bv 64 (BASE + 26228)) Q MID1 Q10 Q11 Q12 Q2 Q3 Q4 Q1
  (ret_ok_codeptr_v (PI := PI_transportb) 26228 ltac:(lia) eq_refl)
  (smb_rng_f (ms_mem ms) md1 6 MID1 ltac:(lia)) (smb_rng_s (ms_mem ms) md1 MID1)
  ltac:(unfold SRX_F; lia) ltac:(unfold SRX_S, TB_g_s; lia)
  (smb_val_src (ms_mem ms) md1 MID1) (smb_val_s (ms_mem ms) md1 MID1)).
intros regsR memR mdR MIDR HPR HRES.
pose proof (smb_regs_pres _ _ RG1 HPR) as RGR.
clear dependent ms.
(* ---- +0x190: `beq a0, zero` ---- *)
pose proof RGR as (((G2 & G3 & G4 & G8 & G9 & G18 & G19 & G20 & G25 & G26 & G27) & G21 & G22) & G23).
change (Z_to_bv 64 (BASE + 26228)) with (Z_to_bv 64 (BASE + SMB_RET1)).
pose proof (smb_entry ly2 S2 W2 regsR memR mdR SMB_RET1 HSC (smb_mid_AR memR mdR MIDR) G21 G27) as HS1.
assert (HEIR : img_env VAL A_LIM (smb_E regsR)) by apply smb_env_img.
assert (SHOK1 : sh_ok segs SMB_Bx (@nil shent) (smb_E regsR) (mrestrict (w_H W2) memR)) by constructor.
pose proof MIDR as (HJ1 & _).
psrr_branch_tok RUN BR HS1 SHOK1 SMB_B0.
- (* equal: the source MAC is the host's (srx_mac_bad); +0x1c0 .. +0x1d0, the ignored cut *)
  cbn [branch_taken] in Hc. rewrite (smb_den_reg regsR 10 (10%bv : bv 5) eq_refl) in Hc.
  change (sv_denot (smb_E regsR) (SLit 0)) with (w64 0) in Hc.
  rewrite bv_eqb_true_iff in Hc. pose proof (proj1 HRES Hc) as M1.
  assert (HMB : srx_mac_bad Bw b = true) by (unfold srx_mac_bad; rewrite M1; reflexivity).
  paj_run_to_tok RUNTO HS1 HJ1 SHOK1 SMB_B0 SRXB_IGN.
  { smb_awr. }
  set (mdI := with_vm_backing (m_vm_lazy mdR) mat mdR) in *. clearbody mdI. clear mat.
  pose proof (smb_mid_run memR mdR (ms_mem ms) mdI MIDR HJ1 (smb_frame0 _ _ _ HF)) as MIDI.
  smb_reg HS1 (10%bv : bv 5) (w64 0) I10 ltac:(reflexivity).
  smb_reg HS1 (11%bv : bv 5) (w64 SRXB_RXIGN) I11 ltac:(reflexivity).
  smb_regs_at HS1 regsR RGR RGI.
  pmkst HS1.
  lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Qx =>
    change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + SRXB_IGN)) mm rom) mdx) Qx) end.
  exact (smb_exit_ign (ms_mem ms) mdI (ms_regs ms) MIDI (proj1 RGI) I10 I11 HMB).
- (* not equal: run 2, +0x194 .. +0x1a0 *)
  cbn [branch_taken] in Hc. rewrite (smb_den_reg regsR 10 (10%bv : bv 5) eq_refl) in Hc.
  change (sv_denot (smb_E regsR) (SLit 0)) with (w64 0) in Hc.
  assert (M1 : TS0.memeq 6 (DSpec.fr_src b) (TW.S_cfg_host_mac Bw) = false).
  { destruct (TS0.memeq 6 (DSpec.fr_src b) (TW.S_cfg_host_mac Bw)) eqn:EM; [|reflexivity].
    assert (E0 : YK11.getr regsR (10%bv : bv 5) = w64 0) by exact (proj2 HRES eq_refl).
    rewrite E0 in Hc. vm_compute in Hc. discriminate Hc. }
  paj_run_tok RUN HS1 HJ1 SHOK1 SMB_B0.
  { smb_awr. }
  set (md3 := with_vm_backing (m_vm_lazy mdR) mat mdR) in *. clearbody md3. clear mat.
  pose proof (smb_mid_run memR mdR (ms_mem ms) md3 MIDR HJ1 (smb_frame0 _ _ _ HF)) as MID3.
  smb_reg HS1 (10%bv : bv 5) (w64 (F + SRX_F)) T10 ltac:(smb_kept regsR 22%nat (22%bv : bv 5) G22).
  smb_reg HS1 (11%bv : bv 5) (w64 SRX_S) T11 ltac:(smb_kept regsR 20%nat (20%bv : bv 5) G20).
  smb_reg HS1 (12%bv : bv 5) (w64 6) T12 ltac:(reflexivity).
  smb_reg HS1 (2%bv : bv 5) (w64 sp1) T2 ltac:(smb_kept regsR 2%nat (2%bv : bv 5) G2).
  smb_reg HS1 (3%bv : bv 5) (w64 (as_gp B)) T3 ltac:(smb_kept regsR 3%nat (3%bv : bv 5) (eq_trans G3 Hgp)).
  smb_reg HS1 (4%bv : bv 5) (w64 (as_tp B)) T4 ltac:(smb_kept regsR 4%nat (4%bv : bv 5) (eq_trans G4 Htp)).
  smb_reg HS1 (1%bv : bv 5) (Z_to_bv 64 (BASE + 26248)) T1 ltac:(apply codeptr_val; exact HEIR).
  smb_regs_at HS1 regsR RGR RG2.
  pmkst HS1.
  lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Qx =>
    change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (transportb_sigma TB___interceptor_trampoline_bcmp)) mm rom)
      mdx) Qx) end.
  (* ---- call 2, +0x1a0: bcmp (f, s, 6) ---- *)
  assert (RF0 : decode_rd_ok W2 (ms_mem ms) (F + SRX_F) 6)
    by (pose proof (smb_rng_f (ms_mem ms) md3 0 MID3 ltac:(lia)) as X; rewrite Z.add_0_r in X; exact X).
  apply (smb_bcmp (ms_mem ms) md3 (ms_regs ms) (F + SRX_F) SRX_S (DSpec.fr_dst b) (TW.S_cfg_host_mac Bw)
    (Z_to_bv 64 (BASE + 26248)) Q MID3 T10 T11 T12 T2 T3 T4 T1
    (ret_ok_codeptr_v (PI := PI_transportb) 26248 ltac:(lia) eq_refl)
    RF0 (smb_rng_s (ms_mem ms) md3 MID3)
    ltac:(unfold SRX_F; lia) ltac:(unfold SRX_S, TB_g_s; lia)
    (smb_val_dst (ms_mem ms) md3 MID3) (smb_val_s (ms_mem ms) md3 MID3)).
  intros regsS memS mdS MIDS HPS HRES2.
  pose proof (smb_regs_pres _ _ RG2 HPS) as RGS.
  clear dependent ms. clear HEIR.
  (* ---- +0x1a4: `beq a0, zero` ---- *)
  pose proof RGS as (((H2 & H3 & H4 & H8 & H9 & H18 & H19 & H20 & H25 & H26 & H27) & H21 & H22) & H23).
  change (Z_to_bv 64 (BASE + 26248)) with (Z_to_bv 64 (BASE + SMB_RET2)).
  pose proof (smb_entry ly2 S2 W2 regsS memS mdS SMB_RET2 HSC (smb_mid_AR memS mdS MIDS) H21 H27) as HS2.
  assert (HEIS : img_env VAL A_LIM (smb_E regsS)) by apply smb_env_img.
  assert (SHOK2 : sh_ok segs SMB_Bx (@nil shent) (smb_E regsS) (mrestrict (w_H W2) memS)) by constructor.
  pose proof MIDS as (HJ2 & _).
  psrr_branch_tok RUN BR HS2 SHOK2 SMB_B0.
  + (* equal: the frame is for this host; the desk cut *)
    cbn [branch_taken] in Hc0. rewrite (smb_den_reg regsS 10 (10%bv : bv 5) eq_refl) in Hc0.
    change (sv_denot (smb_E regsS) (SLit 0)) with (w64 0) in Hc0.
    rewrite bv_eqb_true_iff in Hc0. pose proof (proj1 HRES2 Hc0) as M2.
    assert (HMB : srx_mac_bad Bw b = false) by (unfold srx_mac_bad; rewrite M1, M2; reflexivity).
    paj_run_to_tok RUNTO HS2 HJ2 SHOK2 SMB_B0 SRXB_DESK.
    { smb_awr. }
    set (mdD := with_vm_backing (m_vm_lazy mdS) mat mdS) in *. clearbody mdD. clear mat.
    pose proof (smb_mid_run memS mdS (ms_mem ms) mdD MIDS HJ2 (smb_frame0 _ _ _ HF)) as MIDD.
    smb_regs_at HS2 regsS RGS RGD.
    pmkst HS2.
    lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Qx =>
      change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + SRXB_DESK)) mm rom) mdx) Qx) end.
    exact (smb_exit_desk (ms_mem ms) mdD (ms_regs ms) MIDD RGD HMB).
  + (* not equal: run 3, +0x1a8 .. +0x1b8 *)
    cbn [branch_taken] in Hc0. rewrite (smb_den_reg regsS 10 (10%bv : bv 5) eq_refl) in Hc0.
    change (sv_denot (smb_E regsS) (SLit 0)) with (w64 0) in Hc0.
    assert (M2 : TS0.memeq 6 (DSpec.fr_dst b) (TW.S_cfg_host_mac Bw) = false).
    { destruct (TS0.memeq 6 (DSpec.fr_dst b) (TW.S_cfg_host_mac Bw)) eqn:EM; [|reflexivity].
      assert (E0 : YK11.getr regsS (10%bv : bv 5) = w64 0) by exact (proj2 HRES2 eq_refl).
      rewrite E0 in Hc0. vm_compute in Hc0. discriminate Hc0. }
    paj_run_tok RUN HS2 HJ2 SHOK2 SMB_B0.
    { smb_awr. }
    set (md5 := with_vm_backing (m_vm_lazy mdS) mat mdS) in *. clearbody md5. clear mat.
    pose proof (smb_mid_run memS mdS (ms_mem ms) md5 MIDS HJ2 (smb_frame0 _ _ _ HF)) as MID5.
    smb_reg HS2 (10%bv : bv 5) (w64 (F + SRX_F)) U10 ltac:(smb_kept regsS 22%nat (22%bv : bv 5) H22).
    smb_reg HS2 (11%bv : bv 5) (w64 TRANS_BROADCAST) U11
      ltac:(cbn [sv_denot]; unfold smb_E; rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia); vm_compute; reflexivity).
    smb_reg HS2 (12%bv : bv 5) (w64 6) U12 ltac:(reflexivity).
    smb_reg HS2 (2%bv : bv 5) (w64 sp1) U2 ltac:(smb_kept regsS 2%nat (2%bv : bv 5) H2).
    smb_reg HS2 (3%bv : bv 5) (w64 (as_gp B)) U3 ltac:(smb_kept regsS 3%nat (3%bv : bv 5) (eq_trans H3 Hgp)).
    smb_reg HS2 (4%bv : bv 5) (w64 (as_tp B)) U4 ltac:(smb_kept regsS 4%nat (4%bv : bv 5) (eq_trans H4 Htp)).
    smb_reg HS2 (1%bv : bv 5) (Z_to_bv 64 (BASE + 26272)) U1 ltac:(apply codeptr_val; exact HEIS).
    smb_regs_at HS2 regsS RGS RG3.
    pmkst HS2.
    lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Qx =>
      change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (transportb_sigma TB___interceptor_trampoline_bcmp)) mm
        rom) mdx) Qx) end.
    (* ---- call 3, +0x1b8: bcmp (f, BROADCAST, 6) ---- *)
    assert (RF0 : decode_rd_ok W2 (ms_mem ms) (F + SRX_F) 6)
      by (pose proof (smb_rng_f (ms_mem ms) md5 0 MID5 ltac:(lia)) as X; rewrite Z.add_0_r in X; exact X).
    apply (smb_bcmp (ms_mem ms) md5 (ms_regs ms) (F + SRX_F) TRANS_BROADCAST (DSpec.fr_dst b) TSS.BROADCAST
      (Z_to_bv 64 (BASE + 26272)) Q MID5 U10 U11 U12 U2 U3 U4 U1
      (ret_ok_codeptr_v (PI := PI_transportb) 26272 ltac:(lia) eq_refl)
      RF0 (smb_rng_bc (ms_mem ms) md5 MID5)
      ltac:(unfold SRX_F; lia) ltac:(unfold TRANS_BROADCAST; lia)
      (smb_val_dst (ms_mem ms) md5 MID5) (smb_val_bc (ms_mem ms) md5 MID5)).
    intros regsT memT mdT MIDT HPT HRES3.
    pose proof (smb_regs_pres _ _ RG3 HPT) as RGT.
    clear dependent ms. clear HEIS.
    (* ---- +0x1bc: `beq a0, zero` ---- *)
    pose proof RGT as (((J2 & J3 & J4 & J8 & J9 & J18 & J19 & J20 & J25 & J26 & J27) & J21 & J22) & J23).
    change (Z_to_bv 64 (BASE + 26272)) with (Z_to_bv 64 (BASE + SMB_RET3)).
    pose proof (smb_entry ly2 S2 W2 regsT memT mdT SMB_RET3 HSC (smb_mid_AR memT mdT MIDT) J21 J27) as HS3.
    assert (HEIT : img_env VAL A_LIM (smb_E regsT)) by apply smb_env_img.
    assert (SHOK3 : sh_ok segs SMB_Bx (@nil shent) (smb_E regsT) (mrestrict (w_H W2) memT)) by constructor.
    pose proof MIDT as (HJ3 & _).
    psrr_branch_tok RUN BR HS3 SHOK3 SMB_B0.
    * (* equal: a broadcast; the desk cut *)
      cbn [branch_taken] in Hc1. rewrite (smb_den_reg regsT 10 (10%bv : bv 5) eq_refl) in Hc1.
      change (sv_denot (smb_E regsT) (SLit 0)) with (w64 0) in Hc1.
      rewrite bv_eqb_true_iff in Hc1. pose proof (proj1 HRES3 Hc1) as M3.
      assert (HMB : srx_mac_bad Bw b = false) by (unfold srx_mac_bad; rewrite M1, M2, M3; reflexivity).
      paj_run_to_tok RUNTO HS3 HJ3 SHOK3 SMB_B0 SRXB_DESK.
      { smb_awr. }
      set (mdD := with_vm_backing (m_vm_lazy mdT) mat mdT) in *. clearbody mdD. clear mat.
      pose proof (smb_mid_run memT mdT (ms_mem ms) mdD MIDT HJ3 (smb_frame0 _ _ _ HF)) as MIDD.
      smb_regs_at HS3 regsT RGT RGD.
      pmkst HS3.
      lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Qx =>
        change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + SRXB_DESK)) mm rom) mdx) Qx) end.
      exact (smb_exit_desk (ms_mem ms) mdD (ms_regs ms) MIDD RGD HMB).
    * (* not equal: neither the host's nor a broadcast (srx_mac_bad); +0x1c0 .. +0x1d0, the ignored cut *)
      cbn [branch_taken] in Hc1. rewrite (smb_den_reg regsT 10 (10%bv : bv 5) eq_refl) in Hc1.
      change (sv_denot (smb_E regsT) (SLit 0)) with (w64 0) in Hc1.
      assert (M3 : TS0.memeq 6 (DSpec.fr_dst b) TSS.BROADCAST = false).
      { destruct (TS0.memeq 6 (DSpec.fr_dst b) TSS.BROADCAST) eqn:EM; [|reflexivity].
        assert (E0 : YK11.getr regsT (10%bv : bv 5) = w64 0) by exact (proj2 HRES3 eq_refl).
        rewrite E0 in Hc1. vm_compute in Hc1. discriminate Hc1. }
      assert (HMB : srx_mac_bad Bw b = true) by (unfold srx_mac_bad; rewrite M1, M2, M3; reflexivity).
      paj_run_to_tok RUNTO HS3 HJ3 SHOK3 SMB_B0 SRXB_IGN.
      { smb_awr. }
      set (mdI := with_vm_backing (m_vm_lazy mdT) mat mdT) in *. clearbody mdI. clear mat.
      pose proof (smb_mid_run memT mdT (ms_mem ms) mdI MIDT HJ3 (smb_frame0 _ _ _ HF)) as MIDI.
      smb_reg HS3 (10%bv : bv 5) (w64 0) I10 ltac:(reflexivity).
      smb_reg HS3 (11%bv : bv 5) (w64 SRXB_RXIGN) I11 ltac:(reflexivity).
      smb_regs_at HS3 regsT RGT RGI.
      pmkst HS3.
      lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Qx =>
        change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + SRXB_IGN)) mm rom) mdx) Qx) end.
      exact (smb_exit_ign (ms_mem ms) mdI (ms_regs ms) MIDI (proj1 RGI) I10 I11 HMB).
Qed.

End walk.

(* The piece: from the ignored and the desk cuts, the mac cut. *)
Lemma smb_holds : @srxb_mac_stmt fx rc B MT.
Proof.
  unfold srxb_mac_stmt. intros IGN DESK. unfold srxb_mac_at.
  intros LAWS0 CALLS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf now r b fj TF Bw Bw' pos sp1 F
    ly2 S2 W2 mem2 md2 e regs2 HFIX HCUR HRD HDRD HFB HTW HCODE HREGS.
  exact (smb_walk STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf now r b fj TF Bw Bw' pos sp1 F
    ly2 S2 W2 mem2 md2 e LAWS0 CALLS HFIX HCUR HRD HDRD HFB HTW HCODE IGN DESK regs2 HREGS).
Qed.
End sm.

(* The mac piece of the image-B walk of diginet_session_rx (SrxBCut.v srxb_mac_stmt), at every machine, run ceiling,
   record and meter. *)
Theorem srxb_mac_ok : forall fx rc B MT, @srxb_mac_stmt fx rc B MT.
Proof. intros fx rc B MT. exact (@smb_holds fx rc B MT). Qed.
