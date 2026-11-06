(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:528-543, 616-634;
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:41-45, 208-214, 230-234, for libreac/fuzz_identity's asan-ubsan build
   (lib/B). The same text also appears in projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:420-423, 430-444, 447-448,
   453-455, 470-475, 477-486, 489-491, 502-505, 511-514, 1255-1258. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/reac_box_name_seg_rel.v, with its module paths, module names and numbers changed; 706 of its 765 lines of code are new or changed and 1865 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/on_announce_seg_tail.v, with its module paths and module names changed; 590 of its 674 lines of code are new or changed and 681 lines of the source are left out. *)
(* receive_seg_rf: Lemma recv_rf : recv_rf_stmt (lib/B/Prog/receive_seg_cut.v), the rf piece of the image-B ASan walk
   of receive (fuzz_transport.asan-ubsan 0x836a8 = transportb_sigma TB_receive, statement lib/B/Prog/receive_cg.v),
   from the rf cut RECV_RF (+0x098, 0x83740) to the poll cut RECV_POLL (+0x0b8, by_poll <> 0) or the mrx cut RECV_MRX
   (+0x12c, by_poll = 0). The walk holds the caller's G journal (lib/A/W_journalG.v ajournal_gx G_HARNESS_B 0 []) at
   k + 1 events; the runs are lib/B/Prog/TransportGRunB.v paj_run_x / paj_run_to_x. The code
   (fuzz_transport.c:1002-1003):
     +0x098 .. +0x0a4  `mv a2, sp`, `mv a0, s0`, `mv a1, s1`, `jal spec_read_frame` (return address +0x0a8): run 1
                       (paj_run_tok) to the callee's entry, then the cut file's recv_srf_at with len = n at the world
                       recv_w1 Bw: a0 = a, a1 = n, a2 = sp (recv_regs_opb), ra = BASE + RECV_RF + 0x10
                       (DgnTransportBPaLib.v ret_ok_codeptr_v), the cut facts carried to the run's memory (rf_cur_step);
                       the rest of the piece is its continuation;
     +0x0a8            `lw a0, 0x20(sp)`: run 2 (paj_run_to_tok to +0x0ac) from a state whose only region is the
                       struct's send field (the 4 bytes at sp + 32, read-only, chunk value atom 32): recv_srf_at gives
                       the 80 struct bytes TContract.sf_bytes a (srf_f bytes n), whose bytes 32 .. 35 are put 4 of the
                       send field (rf_sf_send_val), which is receive_cg.v recv_send bytes (lib/U/Prog/T/receive.v
                       r_srf_send at k = n, with firstn_all: rf_srf_send); a0 = its sign extension
                       (lib/A/Prog/m_rx_seg_annt.v annt_sext);
     +0x0ac .. +0x0b0  s4 = the PHi of g_rx_send (A_HI 82 = atom 482, whose value is RECV_RXS_HI), `sw a0, -0x6f4(s4)`:
                       run 3 (rf_store) from a state whose only region is g_rx_send's four bytes (bytes of G:
                       W_journalG.v awr_ok_x_cons_g); the stored bytes are the low four bytes of a0, which are those of
                       recv_send bytes (rf_le_byte_lo32, rf_swrap_lo32), so TWorldG.v tw_write gives the world relation
                       at recv_w2 Bw bytes;
     +0x0b4            `beqz s3` (s3 = by_poll, sign-extended, -2^31 <= by_poll < 2^31: lib/Prog/T/m_rx_epi.v
                       mrxk_eqb): by_poll = 0 goes to +0x12c (RECV_MRX: recv_regs_mrx), else falls to +0x0b8
                       (RECV_POLL: recv_regs_poll, s4 = RECV_RXS_HI).
   No instrumented check, no branch to the trap and no error path is on this stretch. What the call kept (acall_kept_g
   over recv_wr bytes) is carried across the runs by lib/A/Prog/TransportGFrame.v dk_kept_step_gw (g_rx_send's four
   bytes are in recv_wr bytes and in G; runs 1 and 2 write nothing), and the six saved words and the frame's bytes lie
   outside them (rf_cur_step); across the call recv_srf_at carries them. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import YC4b.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k AsanCells TransportGB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TransportRtCg TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBCg TransportGRwB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB TImgB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import m_set_cg check_state_data_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import send_control_cg send_data_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_body_check_cg set_state_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_session_wake_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import on_ack_cg on_data_cg on_announce_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_frame_parse_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_session_tick_cg diginet_session_rx_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import m_tick_cg m_rx_cg io_recv_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import spec_read_frame_cg settle_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_session_poll_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import receive_cg receive_seg_cut.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TransportGRunB CanKit YC1g.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TImg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require m_rx_epi TContract.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require receive.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require TransportGFrame m_rx_seg_annt receive_seg_rf.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.TransportGB.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
Module TCt := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T.TContract.
Module EPI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T.m_rx_epi.
Module URC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T.receive.
Module TGF := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.TransportGFrame.
Module AAN := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.m_rx_seg_annt.
Module ARF := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.receive_seg_rf.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* The symbolic states                                                 *)
(* ------------------------------------------------------------------ *)

(* g_rx_send's four bytes, the only bytes the piece stores. *)
Definition rf_rxs (x : Z) : Prop := TB_g_rx_send <= x < TB_g_rx_send + 4.
(* The registers the piece never writes and the cuts read: sp, gp, tp, s0 .. s3, s5 .. s11. *)
Definition rf_keepl : list Z := [2; 3; 4; 8; 9; 18; 19; 21; 22; 23; 24; 25; 26; 27].

(* A state with no region (+0x098, the branch at +0x0b4). *)
Definition rf_ss0 (pc : Z) : sstate := mkSS pc sr_atoms [] None (mkFacts [] [] []).
(* The state at +0x0a8 (the return of spec_read_frame): the struct's send field, the 4 bytes at sp + 32, read-only,
   holding atom 32; sp (atom 2) is 16-aligned and in the high stack, atom 32 an unsigned int. *)
Definition rf_send_region : YP09.region := YP09.mkRegion (Some 2%nat) 32 36 0 0 [YP09.mkChunk 32 (CVal 4 (SOff 32 0))].
Definition rf_factsL : facts := mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF 0 (2 ^ 32 - 1) 0)] [] [].
Definition rf_ssL : sstate := mkSS (RECV_RF + 16) sr_atoms [rf_send_region] None rf_factsL.
(* The state at +0x0ac: g_rx_send's four bytes, based at the PHi atom of A_OBJ 82 (A_HI 82 = atom 482, s4 after
   +0x0ac), writable; the atom's value is RECV_RXS_HI. *)
Definition rf_rxs_region : YP09.region := YP09.mkRegion (Some 482%nat) (-1780) (-1776) (-1780) (-1776) [].
Definition rf_ssS : sstate :=
  mkSS (RECV_RF + 20) sr_atoms [rf_rxs_region] None (mkFacts [(482%nat, mkAF RECV_RXS_HI RECV_RXS_HI 0)] [] []).

(* ------------------------------------------------------------------ *)
(* Facts of the model, of the bytes and of the values                  *)
(* ------------------------------------------------------------------ *)

Lemma rf_rxs_G : forall x, rf_rxs x -> inG TG.G_HARNESS_B x.
Proof.
intros x Hx. unfold inG. apply Exists_exists. exists (TB_g_rx_send, TW.SZ_g_rx_send). split.
- exact (TMAP_B_in_G _ _ _ TMAP_B_g_rx_send).
- unfold in_zr, rf_rxs, TW.SZ_g_rx_send in *. cbn [fst snd]. lia.
Qed.

Lemma rf_rxs_wr : forall bytes x, rf_rxs x -> recv_wr bytes x.
Proof.
intros bytes x Hx. unfold recv_wr. right; right; right; left. unfold twb_fld, rf_rxs, TW.SZ_g_rx_send in *. lia.
Qed.

Lemma rf_keepl_saved : forall r, In r rf_keepl -> acallee_saved r.
Proof.
intros r Hr. cbn [rf_keepl In] in Hr.
repeat (destruct Hr as [<- | Hr]; [unfold acallee_saved; lia |]). destruct Hr.
Qed.

(* spec_read_frame's send field at len = n is the model's send value (lib/U/Prog/T/receive.v r_srf_send). *)
Lemma rf_srf_send : forall bytes, DSpec.sf_send (srf_f bytes (Z.of_nat (length bytes))) = recv_send bytes.
Proof.
intros bytes. unfold srf_f.
refine (eq_trans (URC.r_srf_send bytes (length bytes) (Nat.le_refl _)) _).
rewrite firstn_all. reflexivity.
Qed.

(* The low four bytes of a value depend on it modulo 2 ^ 32 only; a 32-bit sign extension keeps them. *)
Lemma rf_le_byte_lo32 : forall x v j, x mod 2 ^ 32 = v mod 2 ^ 32 -> YO0f.le_byte x 4 j = YO0f.le_byte v 4 j.
Proof. intros x v j H. unfold YO0f.le_byte. change (8 * Z.of_nat 4) with 32. rewrite H. reflexivity. Qed.

Lemma rf_swrap_lo32 : forall s, bv_swrap 32 s mod 2 ^ 32 = s mod 2 ^ 32.
Proof. intros s. rewrite URC.r_swrap32_eq. Z.div_mod_to_equations. lia. Qed.

(* A chunk of a region, read byte by byte through the view. *)
Lemma rf_field : forall (sg : list Segment) E H (m : word -> option byte) n bb cs lo hi wlo whi od (w : N) e x,
  region_ok sg E (mrestrict H m) (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
  bv_unsigned (ew E n) = bb -> In (YP09.mkChunk od (CVal w e)) cs -> sv_denot E e = Z_to_bv 64 x ->
  Z.of_N w <= 8 ->
  forall j, (j < N.to_nat w)%nat ->
    aview sg H m (bb + od + Z.of_nat j) = Some (YO0f.le_byte x (N.to_nat w) j).
Proof.
intros sg E H m n bb cs lo hi wlo whi od w e x (_ & _ & _ & Hcs) Hn Hc He Hw j Hj.
pose proof (N_nat_Z w) as Hnw.
pose proof (proj1 (Forall_forall _ _) Hcs _ Hc) as Hck. cbn [YP09.r_base base_val] in Hck. rewrite Hn in Hck.
destruct (Hck (Z.of_nat j) ltac:(unfold YP09.c_len; cbn [YP09.cv_len YP09.c_val]; lia)) as (b & Hb1 & Hb2).
cbn [YP09.cbyte YP09.c_val YP09.c_off] in Hb1, Hb2. rewrite He in Hb1. injection Hb1 as <-.
unfold aview. rewrite Hb2. cbn [option_map]. f_equal.
unfold YP09.byte_of_word. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
change (2 ^ Z.of_N 8) with 256. change (2 ^ Z.of_N 64) with (2 ^ 64). unfold YO0f.le_byte.
rewrite (ARF.rf_byte_mod x 64 (8 * Z.of_nat j)) by lia.
rewrite (ARF.rf_byte_mod x (8 * Z.of_nat (N.to_nat w)) (8 * Z.of_nat j)) by lia.
reflexivity.
Qed.

(* nth through firstn, skipn and TW.zs; the w bytes at offset o of a garr8 array of a byte list l whose bytes there
   are put w v: the w-byte value v. *)
Lemma rf_nth_firstn : forall (A : Type) (l : list A) w k d, (k < w)%nat -> nth k (firstn w l) d = nth k l d.
Proof.
intros A l. induction l as [|x l IH]; intros w k d Hk.
- destruct w as [|w]; [lia|]. destruct k; reflexivity.
- destruct w as [|w]; [lia|]. destruct k as [|k]; [reflexivity|]. cbn [firstn nth]. apply IH. lia.
Qed.
Lemma rf_nth_skipn : forall (A : Type) (l : list A) o k d, nth k (skipn o l) d = nth (o + k) l d.
Proof.
intros A l o. revert l. induction o as [|o IH]; intros l k d; [reflexivity|].
destruct l as [|x l]; [destruct k; reflexivity | cbn [skipn]; apply IH].
Qed.
Lemma rf_nth_zs : forall (l : list byte) j, (j < length l)%nat ->
  nth j (TW.zs l) 0 = bv_unsigned (nth j l (Z_to_bv 8 0)).
Proof.
intros l j Hj. unfold TW.zs.
rewrite (nth_indep _ 0 (bv_unsigned (Z_to_bv 8 0))) by (rewrite length_map; exact Hj). apply map_nth.
Qed.
Lemma rf_le_byte1 : forall x, 0 <= x < 256 -> YO0f.le_byte x 1 0 = x.
Proof.
intros x Hx. unfold YO0f.le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
rewrite Z.shiftr_0_r. change (2 ^ 8) with 256. rewrite (Z.mod_small x 256) by lia. apply Z.mod_small. lia.
Qed.
Lemma rf_garr8_val : forall (sg : list Segment) (mm : word -> option byte) (base : Z) (l : list byte) (o w : nat) (v : Z),
  garr8 sg mm base (TW.zs l) -> (o + w <= length l)%nat -> firstn w (skipn o l) = TW.put w v ->
  val_mem sg mm (base + Z.of_nat o) w v.
Proof.
intros sg mm base l o w v HG Hlen Hsub k Hk.
assert (Hj : (o + k < length (TW.zs l))%nat) by (unfold TW.zs; rewrite length_map; lia).
destruct (HG (o + k)%nat Hj) as [Hv Hr]. specialize (Hv 0%nat ltac:(lia)).
replace (base + Z.of_nat (o + k) + Z.of_nat 0) with (base + Z.of_nat o + Z.of_nat k) in Hv by lia.
rewrite Hv. do 2 f_equal.
assert (Hn : nth (o + k) l (Z_to_bv 8 0) = nth k (TW.put w v) (Z_to_bv 8 0)).
{ rewrite <- Hsub. rewrite (rf_nth_firstn _ _ w k _ Hk). rewrite rf_nth_skipn. reflexivity. }
rewrite (rf_nth_zs l (o + k) ltac:(lia)), Hn, (tw_le_byte_put w v k (Z_to_bv 8 0) Hk).
apply rf_le_byte1. unfold YO0f.le_byte. apply Z.mod_pos_bound. lia.
Qed.

(* The struct's send field: the 4 bytes at offset 32 of TContract.sf_bytes. *)
Lemma rf_sf_send_val : forall (sg : list Segment) (mm : word -> option byte) (base fa : Z) (f : DSpec.spec_frame),
  garr8 sg mm base (TW.zs (TCt.sf_bytes fa f)) -> val_mem sg mm (base + 32) 4 (DSpec.sf_send f).
Proof.
intros sg mm base fa f HG. change (base + 32) with (base + Z.of_nat 32).
apply (rf_garr8_val sg mm base (TCt.sf_bytes fa f) 32 4 _ HG).
- change (length (TCt.sf_bytes fa f)) with 80%nat. lia.
- reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* Tactics                                                             *)
(* ------------------------------------------------------------------ *)

(* The value of register r in the machine state of a symbolic state HS (st_ok_pi at a listing pc, st_ok at a callee's
   entry). *)
Ltac rf_reg HS r v H tac :=
  lazymatch type of HS with
  | st_ok_pi ?segsx ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok ?segsx ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_restrict_reg segsx Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | ?T => idtac "rf_reg: no match for" T; fail
  end.
Ltac rf_in := cbn [rf_keepl In]; repeat (first [left; reflexivity | right]).
(* The windows a run wrote, each closed by tac. *)
Ltac rf_win Hin Hx tac :=
  lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end;
  cbn [In] in Hin;
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hx; tac |]);
  destruct Hin.
(* A run from a state whose regions have no writable byte wrote nothing. *)
Ltac rf_nowin :=
  let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let x := fresh "x" in
  let Hin := fresh "Hin" in let Hx := fresh "Hx" in
  intros b wlo whi x Hin Hx; rf_win Hin Hx ltac:(lia).
Ltac rf_kept HFr :=
  let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx;
  apply (YC4b.kept_of_frame _ _ _ _ _ (fun _ : Z => False) HFr); [rf_nowin | exact Hx | intros []].
(* The write right of a run whose regions have no writable byte. *)
Ltac rf_awr0 :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end;
  repeat (apply awr_ok_x_cons; [let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
          cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |]);
  apply awr_ok_x_nil.
(* The write right of the run at +0x0ac: g_rx_send's four bytes, bytes of G. *)
Ltac rf_awr_rxs U :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end;
  apply awr_ok_x_cons_g;
  [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U in Ha; apply rf_rxs_G;
    unfold rf_rxs, RECV_RXS_HI in *; lia |];
  apply awr_ok_x_nil.
(* The model of the goal after a run, named md. *)
Ltac rf_md md :=
  lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (md := mdx) in *; clearbody md end.
(* The kept registers: their symbolic values are their atoms, whose values are those of regs2. *)
Ltac rf_srget :=
  let r := fresh "r" in let Hr := fresh "Hr" in
  intros r Hr; cbn [rf_keepl In] in Hr;
  repeat (destruct Hr as [<- | Hr]; [vm_compute; reflexivity |]); destruct Hr.
Ltac rf_ewlo Elo EE :=
  let r := fresh "r" in let Hr := fresh "Hr" in
  intros r Hr; cbn [rf_keepl In] in Hr;
  repeat (destruct Hr as [<- | Hr]; [rewrite Elo by lia; apply EE; reflexivity |]); destruct Hr.

(* ------------------------------------------------------------------ *)
(* The registers at the cuts                                           *)
(* ------------------------------------------------------------------ *)

Lemma rf_opb_of : forall regs regs2 regsF by_poll a bytes,
  recv_regs_opb regs regs2 by_poll a bytes ->
  (forall r, In r rf_keepl -> YK11.getr regsF (Z_to_bv 5 r) = YK11.getr regs2 (Z_to_bv 5 r)) ->
  recv_regs_opb regs regsF by_poll a bytes.
Proof.
intros regs regs2 regsF by_poll a bytes ((Q2 & Q3 & Q4 & Q21 & Q22 & Q23 & Q24 & Q25 & Q26 & Q27) & Q8 & Q9 & Q18 & Q19)
  HK.
refine (conj (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))))
  (conj _ (conj _ (conj _ _)))).
- exact (eq_trans (HK 2 ltac:(rf_in)) Q2).
- exact (eq_trans (HK 3 ltac:(rf_in)) Q3).
- exact (eq_trans (HK 4 ltac:(rf_in)) Q4).
- exact (eq_trans (HK 21 ltac:(rf_in)) Q21).
- exact (eq_trans (HK 22 ltac:(rf_in)) Q22).
- exact (eq_trans (HK 23 ltac:(rf_in)) Q23).
- exact (eq_trans (HK 24 ltac:(rf_in)) Q24).
- exact (eq_trans (HK 25 ltac:(rf_in)) Q25).
- exact (eq_trans (HK 26 ltac:(rf_in)) Q26).
- exact (eq_trans (HK 27 ltac:(rf_in)) Q27).
- exact (eq_trans (HK 8 ltac:(rf_in)) Q8).
- exact (eq_trans (HK 9 ltac:(rf_in)) Q9).
- exact (eq_trans (HK 18 ltac:(rf_in)) Q18).
- exact (eq_trans (HK 19 ltac:(rf_in)) Q19).
Qed.

Lemma rf_mrx_of : forall regs regs2 regsF by_poll a bytes,
  recv_regs_opb regs regs2 by_poll a bytes ->
  (forall r, In r rf_keepl -> YK11.getr regsF (Z_to_bv 5 r) = YK11.getr regs2 (Z_to_bv 5 r)) ->
  recv_regs_mrx regs regsF a bytes.
Proof.
intros regs regs2 regsF by_poll a bytes HO HK.
destruct (rf_opb_of regs regs2 regsF by_poll a bytes HO HK) as (HKP & Q8 & Q9 & _).
exact (conj HKP (conj Q8 Q9)).
Qed.

Lemma rf_poll_of : forall regs regs2 regsF by_poll a bytes,
  recv_regs_opb regs regs2 by_poll a bytes ->
  (forall r, In r rf_keepl -> YK11.getr regsF (Z_to_bv 5 r) = YK11.getr regs2 (Z_to_bv 5 r)) ->
  YK11.getr regsF 20 = w64 RECV_RXS_HI ->
  recv_regs_poll regs regsF a bytes.
Proof.
intros regs regs2 regsF by_poll a bytes HO HK H20.
destruct (rf_opb_of regs regs2 regsF by_poll a bytes HO HK) as (HKP & Q8 & Q9 & Q18 & _).
exact (conj HKP (conj Q8 (conj Q9 (conj Q18 H20)))).
Qed.

Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).
Local Abbreviation ajournal_gx := (@W_journalG.ajournal_gx rc tfib_sink_head segs B).

(* The machine state of a goal moved to the cut pc's name. *)
Ltac rf_pc pc :=
  lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
    change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + pc)) mm rom) mdx) Q) end.

Lemma rf_base : BASE = 0x83740 - RECV_RF.
Proof. pose proof recv_cut_pcs as (_ & _ & _ & E & _). lia. Qed.

Definition rf_E0 (regs : bvmap 5 word) : env := Eimg (PI := PI_transportb) (Ereg regs []).
Definition rf_EL (regs : bvmap 5 word) (v : Z) : env := Eimg (PI := PI_transportb) (Ereg regs [w64 v]).

Lemma rf_u482 : forall regs extra, bv_unsigned (ew (Eimg (PI := PI_transportb) (Ereg regs extra)) 482) = RECV_RXS_HI.
Proof. intros regs extra. rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia). vm_compute. reflexivity. Qed.

(* A state with no region, at any pc. *)
Lemma rf_entry0 : forall (Wx : world segs) regs mem pc,
  st_ok_pi segs VAL (rf_E0 regs) (rf_ss0 pc)
    (restrict (w_H Wx) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + pc)) mem (YK11.seg_rom segs))).
Proof.
intros Wx regs mem pc. rewrite restrict_mkst_fx. unfold rf_ss0.
apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_nil.
- apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. repeat split.
- unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. repeat split.
Qed.

(* The state at +0x0a8 with the struct's send field. *)
Lemma rf_entryL : forall (Wx : world segs) regs mem (spf v : Z),
  YK11.getr regs 2 = w64 spf -> 2 ^ 46 <= spf -> spf <= 2 ^ 47 -> spf mod 16 = 0 -> 0 <= v < 2 ^ 32 ->
  val_mem segs (mrestrict (w_H Wx) mem) (spf + 32) 4 v ->
  st_ok_pi segs VAL (rf_EL regs v) rf_ssL
    (restrict (w_H Wx) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + (RECV_RF + 16))) mem (YK11.seg_rom segs))).
Proof.
intros Wx regs mem spf v H2 Hlo Hhi Hal Hv HVM.
set (E := rf_EL regs v).
assert (E2 : ew E 2 = w64 spf)
  by (unfold E, rf_EL; rewrite (can_ew_Eimg_Ereg_nat regs _ 2 (Z_to_bv 5 2) eq_refl); exact H2).
assert (U2 : bv_unsigned (ew E 2) = spf) by (rewrite E2; unfold w64; apply unsigned_lit_small; lia).
assert (E32 : ew E 32 = w64 v)
  by (unfold E, rf_EL; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0%nat)).
assert (U32 : bv_unsigned (ew E 32) = v) by (rewrite E32; unfold w64; apply unsigned_lit_small; lia).
rewrite restrict_mkst_fx. unfold rf_ssL.
apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil].
  unfold rf_send_region, region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite U2. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val segs E _ spf 32 4 (SOff 32 0) v).
  + apply ARF.rf_den_atom; [exact E32 | lia].
  + change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32). lia.
  + cbn. lia.
  + exact HVM.
- apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. repeat split.
- unfold rf_factsL, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite U2, U32. change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
  repeat match goal with |- _ /\ _ => split end; try exact I; first [lia | exact Hal].
Qed.

(* The state at +0x0ac with g_rx_send's region. *)
Lemma rf_entryS : forall (Wx : world segs) regs mem,
  st_ok_pi segs VAL (rf_E0 regs) rf_ssS
    (restrict (w_H Wx) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + (RECV_RF + 20))) mem (YK11.seg_rom segs))).
Proof.
intros Wx regs mem. rewrite restrict_mkst_fx. unfold rf_ssS.
assert (U : bv_unsigned (ew (rf_E0 regs) 482) = RECV_RXS_HI) by exact (rf_u482 regs []).
apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil].
  unfold rf_rxs_region, region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite U. unfold RECV_RXS_HI.
  split; [unfold TB_g_rx_send; lia|]. split; [unfold TB_g_rx_send; lia|]. split; [|constructor].
  intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS_B (TB_g_rx_send + 1780 + o) G_HARNESS_B_rw).
  apply rf_rxs_G. unfold rf_rxs. lia.
- apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. repeat split.
- unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U, Z.pow_0_r, Z.mod_1_r.
  repeat split; first [exact I | lia].
Qed.

(* The value of a kept register at the machine state of a symbolic state: its atom's. *)
Lemma rf_keep_regs : forall (L : list Z) (E : env) ss (Hh : word -> bool) ms (regs2 : bvmap 5 word),
  st_ok_pi segs VAL E ss (restrict Hh ms) ->
  (forall r, In r L -> sr_get (ss_regs ss) (Z_to_bv 5 r) = SOff (Z.to_nat r) 0) ->
  (forall r, In r L -> ew E (Z.to_nat r) = YK11.getr regs2 (Z_to_bv 5 r)) ->
  forall r, In r L -> YK11.getr (ms_regs ms) (Z_to_bv 5 r) = YK11.getr regs2 (Z_to_bv 5 r).
Proof.
intros L E ss Hh ms regs2 HS HR HE r Hr.
rewrite (st_ok_pi_restrict_reg Hh E ss ms (Z_to_bv 5 r) HS), (HR r Hr).
cbn [sv_denot]. rewrite (HE r Hr), Z.add_0_r. apply Z_to_bv_bv_unsigned.
Qed.

(* ------------------------------------------------------------------ *)
(* The cut facts carried across a step                                 *)
(* ------------------------------------------------------------------ *)

(* The stack pointer of the call: above the allocation ceiling by the statement's window, 16-aligned. *)
Lemma rf_fix_sp : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
    (p by_poll pf T : Z) (bytes Bw : list byte) ch,
  recv_fix B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p by_poll pf T bytes Bw ch ->
  0x7fff7f800000 + RECV_STK <= spZ regs /\ spZ regs <= 2 ^ 47 /\ spZ regs mod 16 = 0.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p by_poll pf T bytes Bw ch HFIX.
pose proof HFIX as (HJ0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hal & Hwlo & Hwhi & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HJ0 as (_ & _ & (memS & HJi & _) & _). rewrite !Z.add_0_r in HJi.
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
split; [lia|]. split; [lia | exact Hal].
Qed.

(* A step that changes at most g_rx_send's four bytes keeps recv_cur (TransportGFrame.v dk_kept_step_gw: those bytes
   are in recv_wr bytes and in G; the saved words lie above the allocation ceiling) and the frame's bytes (a block
   byte is not an image byte). *)
Lemma rf_cur_step : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
    (p by_poll pf T : Z) (bytes Bw : list byte) ch (a : Z) ly2 S2 (W2 : world segs) mX mdX mY mdY,
  AR_laws segs B -> gx_ok segs B TG.G_HARNESS_B ->
  recv_fix B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p by_poll pf T bytes Bw ch ->
  recv_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs bytes a ly2 S2 W2 mX mdX ->
  recv_blk W2 mX a bytes ->
  ajournal_gx TG.G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mY mdY (k + 1) ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ rf_rxs x -> aview segs (w_H W2) mY x = aview segs (w_H W2) mX x) ->
  (forall x, apresent (w_H W2) mX x -> apresent (w_H W2) mY x) ->
  recv_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs bytes a ly2 S2 W2 mY mdY /\
  recv_blk W2 mY a bytes.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p by_poll pf T bytes Bw ch a ly2 S2 W2 mX mdX mY mdY
  LAWS HGX HFIX HCUR HBLK HJY KD GR.
pose proof HFIX as (HJ0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hwlo & Hwhi & _).
pose proof HCUR as (HJX & Hfrs & Hperm & HMO & HK & HSV & H4096).
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ0) as HAR.
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJX) as HAR2.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HJ0 as (_ & _ & (memS & HJi & _) & _). rewrite !Z.add_0_r in HJi.
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
clear HJi memS.
assert (RSv : 0 <= RECV_STK) by (apply Z.leb_le; vm_compute; reflexivity).
assert (CT : TB_g_rx_send = 6180960) by reflexivity.
split.
- refine (conj HJY (conj Hfrs (conj Hperm (conj HMO (conj _ (conj _ H4096)))))).
  + apply (TGF.dk_kept_step_gw segs B LAWS transportb_segs_low TG.G_HARNESS_B lyc Sc W memc mdc W2 mX mY
      (spZ regs - RECV_STK) (spZ regs) (recv_wr bytes) rf_rxs HAR HK KD GR).
    * intros x Hx Hc. exfalso. unfold rf_rxs in Hx. lia.
    * intros b m i _ _ Hx. exact (rf_rxs_wr bytes _ Hx).
    * intros x Hx _ HnG _ _. exact (HnG (rf_rxs_G x Hx)).
    * intros cid pos x _ _ Hx. exact (rf_rxs_wr bytes x Hx).
  + apply Forall_forall. intros o Ho. pose proof (proj1 (Forall_forall _ _) HSV o Ho) as Hv.
    assert (Hob : 8 <= fst o <= 48).
    { unfold RECV_SAVED in Ho. cbn [In] in Ho.
      repeat (destruct Ho as [Ho|Ho]; [subst o; cbn [fst]; lia|]). destruct Ho. }
    rewrite <- Hv. apply rdword_ext. intros i Hi. apply KD; [lia | unfold rf_rxs; lia].
- assert (Hin2 : In (a, Z.max 1 (Z.of_nat (length bytes))) (ablocks B ly2 S2))
    by exact (Permutation_in _ (Permutation_sym Hperm) (or_introl eq_refl)).
  destruct (al_blocks _ _ LAWS ly2 S2 W2 mX mdX _ _ HAR2 Hin2) as (_ & Hb4096 & Hbc & _).
  pose proof (ARF.rf_req_ge (Z.max 1 (Z.of_nat (length bytes)))) as Hq.
  unfold recv_blk in *. apply (garr8_frame segs (mrestrict (w_H W2) mX) _ _ _ HBLK).
  intros x Hx. apply can_mbyte_of_aview. unfold TW.zs in Hx. rewrite length_map in Hx.
  apply KD; [lia|].
  intros Hr. apply (blk_img segs B LAWS ly2 S2 W2 mX mdX a (Z.max 1 (Z.of_nat (length bytes))) x HAR2 Hin2
    ltac:(lia)).
  destruct (HGX x (rf_rxs_G x Hr)) as [Hi _]. exact Hi.
Qed.

(* ------------------------------------------------------------------ *)
(* +0x0ac .. +0x0b4: the store of the send value, `beqz s3`, the cuts   *)
(* ------------------------------------------------------------------ *)

Lemma rf_store : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
    (p by_poll pf T : Z) (bytes Bw : list byte) ch (a : Z) (Bw' : list byte)
    ly2 S2 (W2 : world segs) (mF : word -> option byte) (mdF : Model) (regs3 : bvmap 5 word),
  @recv_poll_at fx rc B MT -> @recv_mrx_at fx rc B MT -> recv_laws B MT -> recv_calls B MT ->
  recv_fix B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p by_poll pf T bytes Bw ch ->
  recv_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs bytes a ly2 S2 W2 mF mdF ->
  recv_res Bw bytes by_poll pf a Bw' -> recv_blk W2 mF a bytes ->
  tw_at TMAP_B (aview segs (w_H W2) mF) (recv_w1 Bw) ->
  recv_regs_opb regs regs3 by_poll a bytes ->
  YK11.getr regs3 10 = Z_to_bv 64 (bv_swrap 32 (recv_send bytes)) ->
  SRr segs W2 (mkCfg (@YK11.mkst fx regs3 (Z_to_bv 64 (BASE + (RECV_RF + 20))) mF (YK11.seg_rom segs)) mdF)
    (@transport_recv_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw bytes by_poll pf).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p by_poll pf T bytes Bw ch a Bw' ly2 S2 W2 mF mdF regs3
  HPOLL HMRX HL HC HFIX HCUR HRES HBLK HTW HREGS H10.
pose proof HL as (_ & _ & _ & _ & _ & _ & _ & _ & LAWS & MTL & HGX & HGNE).
pose proof HCUR as (HJ & _).
pose proof HFIX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hbp & _).
assert (RSV : 0 <= recv_send bytes < 2 ^ 32) by exact (ARF.rf_send_range bytes).
pose proof (rf_entryS W2 regs3 mF) as HS.
set (E0 := rf_E0 regs3) in HS.
assert (HEI : img_env VAL A_LIM E0) by (unfold E0, rf_E0; apply Eimg_env).
assert (SHOK : sh_ok segs (SLit 0) (@nil shent) E0 (mrestrict (w_H W2) mF)) by constructor.
assert (U482 : bv_unsigned (ew E0 482) = RECV_RXS_HI) by (unfold E0, rf_E0; apply rf_u482).
assert (EE0 : forall nn (rr : bv 5), Z.of_nat nn = bv_unsigned rr -> ew E0 nn = YK11.getr regs3 rr)
  by (intros nn rr Hnn; unfold E0, rf_E0; apply can_ew_Eimg_Ereg_nat; exact Hnn).
pose proof (@paj_run_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B
  HGX 0 []) as RUN.
pose proof (@paj_run_to_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B
  HGX 0 []) as RUNTO.
pose proof (paj_branch (fx := fx) (PI := PI_transportb)) as BR.
(* run 3, +0x0ac .. +0x0b0: s4 = the PHi of g_rx_send, `sw a0, -0x6f4(s4)`; it stops at `beqz s3` *)
paj_run_tok RUN HS HJ SHOK (0, 0).
{ rf_awr_rxs U482. }
rf_md md1.
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?mz) => rename mz into ms1 end.
assert (K1 : forall x, 0 <= x < 2 ^ 64 -> ~ rf_rxs x ->
  aview segs (w_H W2) (ms_mem ms1) x = aview segs (w_H W2) mF x).
{ intros x Hx Hn. apply (YC4b.kept_of_frame _ _ _ _ _ rf_rxs HFr); [| exact Hx | exact Hn].
  intros b wlo whi y Hin Hy. rf_win Hin Hy ltac:(rewrite ?U482 in Hy; unfold rf_rxs, RECV_RXS_HI in *; lia). }
assert (G1 : forall x, apresent (w_H W2) mF x -> apresent (w_H W2) (ms_mem ms1) x)
  by (intros x Hx; exact (apresent_grows _ _ _ x HG Hx)).
clear HF HFr HG.
lazymatch type of HS with st_ok_pi _ _ ?EF _ _ => set (E1 := EF) in HS end.
assert (E1lo : forall nn, (nn < 1024)%nat -> ew E1 nn = ew E0 nn)
  by (intros nn Hnn; unfold E1; repeat rewrite ew_ewset_other by lia; reflexivity).
assert (U482b : bv_unsigned (ew E1 482) = RECV_RXS_HI) by (rewrite E1lo by lia; exact U482).
(* the stored bytes, read back from the region *)
pose proof (st_ok_pi_region_nth E1 _ (restrict (w_H W2) ms1) 0 _ HS eq_refl) as RG0. cbn [ms_mem restrict] in RG0.
assert (D10 : sv_denot E1 (SOff 10 0) = Z_to_bv 64 (bv_swrap 32 (recv_send bytes))).
{ cbn [sv_denot]. rewrite (E1lo 10%nat ltac:(lia)), (EE0 10%nat (Z_to_bv 5 10) eq_refl), Z.add_0_r.
  rewrite Z_to_bv_bv_unsigned. exact H10. }
pose proof (rf_field _ _ _ _ _ _ _ _ _ _ _ (-1780) 4%N (SOff 10 0) _ RG0 U482b
  ltac:(cbn [In]; left; reflexivity) D10 ltac:(cbn; lia)) as VS.
clear RG0.
(* the registers at +0x0b4 *)
assert (KR1 : forall r, In r rf_keepl -> YK11.getr (ms_regs ms1) (Z_to_bv 5 r) = YK11.getr regs3 (Z_to_bv 5 r)).
{ apply (rf_keep_regs rf_keepl E1 _ (w_H W2) ms1 regs3 HS); [rf_srget | rf_ewlo E1lo EE0]. }
rf_reg HS (Z_to_bv 5 20) (w64 RECV_RXS_HI) Ys4 ltac:(cbn [sv_denot]; rewrite U482b, Z.add_0_r; reflexivity).
(* the facts at the memory after the store; the machine state named *)
pmkst HS.
clear HS SHOK HEI.
set (m1 := ms_mem ms1) in *.
destruct (rf_cur_step STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p by_poll pf T bytes Bw ch a ly2 S2 W2
  mF mdF m1 _ LAWS HGX HFIX HCUR HBLK HJ K1 G1) as [CUR1 BLK1].
assert (TW1 : tw_at TMAP_B (aview segs (w_H W2) m1) (recv_w2 Bw bytes)).
{ unfold recv_w2, TW.set_g_rx_send.
  replace TW.OFF_g_rx_send with (TW.OFF_g_rx_send + 0) by lia.
  apply (tw_write TMAP_B (aview segs (w_H W2) mF) (aview segs (w_H W2) m1) (recv_w1 Bw) TW.OFF_g_rx_send
    TB_g_rx_send TW.SZ_g_rx_send 0 4 (recv_send bytes) TMAP_B_ok HTW TMAP_B_g_rx_send ltac:(lia)
    ltac:(unfold TW.SZ_g_rx_send; lia)).
  - intros j Hj. pose proof (VS j Hj) as V.
    replace (RECV_RXS_HI + -1780) with (TB_g_rx_send + 0) in V by (unfold RECV_RXS_HI; lia).
    refine (eq_trans V _). apply (f_equal Some). apply rf_le_byte_lo32. apply rf_swrap_lo32.
  - intros x Hx Hn. apply K1.
    + pose proof (TMAP_B_hull x Hx) as Hh. unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in Hh. lia.
    + intros Hr. apply Hn. unfold rf_rxs in Hr. lia. }
(* +0x0b4: `beqz s3`, from a state with no region *)
rf_pc (RECV_RF + 28).
pose proof (rf_entry0 W2 (ms_regs ms1) m1 (RECV_RF + 28)) as HS.
set (E2 := rf_E0 (ms_regs ms1)) in HS.
assert (HEI : img_env VAL A_LIM E2) by (unfold E2, rf_E0; apply Eimg_env).
assert (SHOK : sh_ok segs (SLit 0) (@nil shent) E2 (mrestrict (w_H W2) m1)) by constructor.
assert (EE2 : forall nn (rr : bv 5), Z.of_nat nn = bv_unsigned rr -> ew E2 nn = YK11.getr (ms_regs ms1) rr)
  by (intros nn rr Hnn; unfold E2, rf_E0; apply can_ew_Eimg_Ereg_nat; exact Hnn).
pose proof HREGS as (_ & _ & _ & _ & Q19).
assert (Y19 : YK11.getr (ms_regs ms1) (Z_to_bv 5 19) = w64 by_poll) by exact (eq_trans (KR1 19 ltac:(rf_in)) Q19).
assert (D19 : sv_denot E2 (SOff 19 0) = Z_to_bv 64 by_poll).
{ cbn [sv_denot]. rewrite (EE2 19%nat (Z_to_bv 5 19) eq_refl), Y19. unfold w64.
  rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned. }
psrr_branch_tok RUN BR HS SHOK (0, 0).
- (* by_poll = 0: to the mrx cut +0x12c *)
  cbn [branch_taken] in Hc. rewrite D19 in Hc. change (sv_denot E2 (SLit 0)) with (Z_to_bv 64 0) in Hc.
  rewrite EPI.mrxk_eqb in Hc by lia. apply Z.eqb_eq in Hc.
  paj_run_to_tok RUNTO HS HJ SHOK (0, 0) RECV_MRX.
  { rf_awr0. }
  rf_md md2.
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?mz) => rename mz into ms2 end.
  assert (KD2 : forall x, 0 <= x < 2 ^ 64 -> aview segs (w_H W2) (ms_mem ms2) x = aview segs (w_H W2) m1 x)
    by (rf_kept HFr).
  assert (GR2 : forall x, apresent (w_H W2) m1 x -> apresent (w_H W2) (ms_mem ms2) x)
    by (intros x Hx; exact (apresent_grows _ _ _ x HG Hx)).
  clear HF HFr HG.
  lazymatch type of HS with st_ok_pi _ _ ?EF _ _ => set (E3 := EF) in HS end.
  assert (E3lo : forall nn, (nn < 1024)%nat -> ew E3 nn = ew E2 nn)
    by (intros nn Hnn; unfold E3; repeat rewrite ew_ewset_other by lia; reflexivity).
  assert (KRC : forall r, In r rf_keepl ->
    YK11.getr (ms_regs ms2) (Z_to_bv 5 r) = YK11.getr (ms_regs ms1) (Z_to_bv 5 r)).
  { apply (rf_keep_regs rf_keepl E3 _ (w_H W2) ms2 (ms_regs ms1) HS); [rf_srget | rf_ewlo E3lo EE2]. }
  destruct (rf_cur_step STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p by_poll pf T bytes Bw ch a ly2 S2
    W2 m1 _ (ms_mem ms2) _ LAWS HGX HFIX CUR1 BLK1 HJ (fun x Hx _ => KD2 x Hx) GR2) as [CURC BLKC].
  assert (TWC : tw_at TMAP_B (aview segs (w_H W2) (ms_mem ms2)) (recv_w2 Bw bytes)).
  { apply (tw_kept TMAP_B (aview segs (w_H W2) m1)); [exact TW1|]. intros x Hx. apply KD2.
    pose proof (TMAP_B_hull x Hx) as Hh. unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in Hh. lia. }
  pmkst HS.
  rf_pc RECV_MRX.
  apply (HMRX HL HC STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p by_poll pf T bytes Bw ch a Bw' ly2 S2
    W2 (ms_mem ms2) _ (ms_regs ms2) HFIX CURC HRES BLKC TWC Hc).
  exact (rf_mrx_of regs regs3 (ms_regs ms2) by_poll a bytes HREGS
    (fun r Hr => eq_trans (KRC r Hr) (KR1 r Hr))).
- (* by_poll <> 0: to the poll cut +0x0b8 *)
  cbn [branch_taken] in Hc. rewrite D19 in Hc. change (sv_denot E2 (SLit 0)) with (Z_to_bv 64 0) in Hc.
  rewrite EPI.mrxk_eqb in Hc by lia. apply Z.eqb_neq in Hc.
  paj_run_to_tok RUNTO HS HJ SHOK (0, 0) RECV_POLL.
  { rf_awr0. }
  rf_md md2.
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?mz) => rename mz into ms2 end.
  assert (KD2 : forall x, 0 <= x < 2 ^ 64 -> aview segs (w_H W2) (ms_mem ms2) x = aview segs (w_H W2) m1 x)
    by (rf_kept HFr).
  assert (GR2 : forall x, apresent (w_H W2) m1 x -> apresent (w_H W2) (ms_mem ms2) x)
    by (intros x Hx; exact (apresent_grows _ _ _ x HG Hx)).
  clear HF HFr HG.
  lazymatch type of HS with st_ok_pi _ _ ?EF _ _ => set (E3 := EF) in HS end.
  assert (E3lo : forall nn, (nn < 1024)%nat -> ew E3 nn = ew E2 nn)
    by (intros nn Hnn; unfold E3; repeat rewrite ew_ewset_other by lia; reflexivity).
  assert (KRC : forall r, In r (20 :: rf_keepl) ->
    YK11.getr (ms_regs ms2) (Z_to_bv 5 r) = YK11.getr (ms_regs ms1) (Z_to_bv 5 r)).
  { apply (rf_keep_regs (20 :: rf_keepl) E3 _ (w_H W2) ms2 (ms_regs ms1) HS); [rf_srget | rf_ewlo E3lo EE2]. }
  destruct (rf_cur_step STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p by_poll pf T bytes Bw ch a ly2 S2
    W2 m1 _ (ms_mem ms2) _ LAWS HGX HFIX CUR1 BLK1 HJ (fun x Hx _ => KD2 x Hx) GR2) as [CURC BLKC].
  assert (TWC : tw_at TMAP_B (aview segs (w_H W2) (ms_mem ms2)) (recv_w2 Bw bytes)).
  { apply (tw_kept TMAP_B (aview segs (w_H W2) m1)); [exact TW1|]. intros x Hx. apply KD2.
    pose proof (TMAP_B_hull x Hx) as Hh. unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in Hh. lia. }
  pmkst HS.
  rf_pc RECV_POLL.
  apply (HPOLL HL HC STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p by_poll pf T bytes Bw ch a Bw' ly2 S2
    W2 (ms_mem ms2) _ (ms_regs ms2) HFIX CURC HRES BLKC TWC Hc).
  exact (rf_poll_of regs regs3 (ms_regs ms2) by_poll a bytes HREGS
    (fun r Hr => eq_trans (KRC r (or_intror Hr)) (KR1 r Hr)) (eq_trans (KRC 20 (or_introl eq_refl)) Ys4)).
Qed.

(* ------------------------------------------------------------------ *)
(* The piece                                                           *)
(* ------------------------------------------------------------------ *)

Lemma recv_rf : @recv_rf_stmt fx rc B MT.
Proof.
unfold recv_rf_stmt. intros SRF HPOLL HMRX.
unfold recv_rf_at. intros HL HC STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p by_poll pf T bytes Bw ch a Bw'
  ly2 S2 W2 mem2 md2 regs2 HFIX HCUR HRES HBLK HTW HREGS.
pose proof HL as (_ & _ & _ & _ & _ & _ & _ & _ & LAWS & MTL & HGX & HGNE).
pose proof HCUR as (HJ & _).
pose proof HREGS as ((Q2 & _) & Q8 & Q9 & _).
pose proof HFIX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hn & _).
destruct (rf_fix_sp STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p by_poll pf T bytes Bw ch HFIX)
  as (Hsplo & Hsphi & Hsp16).
assert (RSv : 0 <= RECV_STK) by (apply Z.leb_le; vm_compute; reflexivity).
assert (FF : RECV_FRAME = 128) by reflexivity.
pose proof rf_base as EB.
pose proof (@paj_run_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B
  HGX 0 []) as RUN.
pose proof (@paj_run_to_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B
  HGX 0 []) as RUNTO.
(* run 1, +0x098 .. +0x0a4: `mv a2, sp`, `mv a0, s0`, `mv a1, s1`, `jal spec_read_frame` *)
pose proof (rf_entry0 W2 regs2 mem2 RECV_RF) as HS.
set (E0 := rf_E0 regs2) in HS.
assert (HEI : img_env VAL A_LIM E0) by (unfold E0, rf_E0; apply Eimg_env).
assert (SHOK : sh_ok segs (SLit 0) (@nil shent) E0 (mrestrict (w_H W2) mem2)) by constructor.
assert (EE0 : forall nn (rr : bv 5), Z.of_nat nn = bv_unsigned rr -> ew E0 nn = YK11.getr regs2 rr)
  by (intros nn rr Hnn; unfold E0, rf_E0; apply can_ew_Eimg_Ereg_nat; exact Hnn).
paj_run_tok RUN HS HJ SHOK (0, 0).
{ rf_awr0. }
rf_md md1.
lazymatch type of HS with context [restrict _ ?mz] => rename mz into ms1 end.
assert (KD1 : forall x, 0 <= x < 2 ^ 64 -> aview segs (w_H W2) (ms_mem ms1) x = aview segs (w_H W2) mem2 x)
  by (rf_kept HFr).
assert (GR1 : forall x, apresent (w_H W2) mem2 x -> apresent (w_H W2) (ms_mem ms1) x)
  by (intros x Hx; exact (apresent_grows _ _ _ x HG Hx)).
clear HF HFr HG.
lazymatch type of HS with
| st_ok_pi _ _ ?EF _ _ => set (E1 := EF) in HS
| OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok _ ?EF _ _ => set (E1 := EF) in HS
end.
assert (E1lo : forall nn, (nn < 1024)%nat -> ew E1 nn = ew E0 nn)
  by (intros nn Hnn; unfold E1; repeat rewrite ew_ewset_other by lia; reflexivity).
(* the registers at the call *)
rf_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + (RECV_RF + 16))) R1 ltac:(apply codeptr_val; exact HEI).
rf_reg HS (Z_to_bv 5 10) (w64 a) R10
  ltac:(cbn [sv_denot]; rewrite (E1lo 8%nat ltac:(lia)), (EE0 8%nat (Z_to_bv 5 8) eq_refl), Z.add_0_r,
        Z_to_bv_bv_unsigned; exact Q8).
rf_reg HS (Z_to_bv 5 11) (w64 (Z.of_nat (length bytes))) R11
  ltac:(cbn [sv_denot]; rewrite (E1lo 9%nat ltac:(lia)), (EE0 9%nat (Z_to_bv 5 9) eq_refl), Z.add_0_r,
        Z_to_bv_bv_unsigned; exact Q9).
rf_reg HS (Z_to_bv 5 12) (w64 (spZ regs - RECV_FRAME)) Ya2
  ltac:(cbn [sv_denot]; rewrite (E1lo 2%nat ltac:(lia)), (EE0 2%nat (Z_to_bv 5 2) eq_refl), Z.add_0_r,
        Z_to_bv_bv_unsigned; exact Q2).
assert (HP0 : aregs_preserved regs2 (ms_regs ms1)).
{ apply (aregs_preserved_of_st_ok segs (w_H W2) E1 _ ms1 regs2 [] HS); [|vm_compute; reflexivity].
  unfold E1, E0, rf_E0. split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]. }
assert (KR1 : forall r, In r rf_keepl -> YK11.getr (ms_regs ms1) (Z_to_bv 5 r) = YK11.getr regs2 (Z_to_bv 5 r))
  by (intros r Hr; exact (HP0 r (rf_keepl_saved r Hr))).
pose proof (rf_opb_of regs regs2 (ms_regs ms1) by_poll a bytes HREGS KR1) as HREGS1.
pmkst HS.
(* the cut facts at the call state *)
destruct (rf_cur_step STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p by_poll pf T bytes Bw ch a ly2 S2 W2
  mem2 md2 (ms_mem ms1) md1 LAWS HGX HFIX HCUR HBLK HJ (fun x Hx _ => KD1 x Hx) GR1) as [CUR1 BLK1].
assert (TW1 : tw_at TMAP_B (aview segs (w_H W2) (ms_mem ms1)) (recv_w1 Bw)).
{ apply (tw_kept TMAP_B (aview segs (w_H W2) mem2)); [exact HTW|]. intros x Hx. apply KD1.
  pose proof (TMAP_B_hull x Hx) as Hh. unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in Hh. lia. }
assert (HRO1 : YK0s.ret_ok (YK11.getr (ms_regs ms1) (1%bv : bv 5))).
{ rewrite R1. apply (ret_ok_codeptr_v (PI := PI_transportb)); [unfold RECV_RF, AF_receive; lia | reflexivity]. }
assert (HRA1 : 4096 <= raZ (ms_regs ms1)).
{ change (raZ (ms_regs ms1)) with (bv_unsigned (YK11.getr (ms_regs ms1) (1%bv : bv 5))).
  rewrite R1, unsigned_lit_small by (rewrite EB; unfold RECV_RF, AF_receive; lia).
  rewrite EB. unfold RECV_RF, AF_receive. lia. }
(* +0x0a4: the call of spec_read_frame, recv_srf_at with len = n at the world recv_w1 Bw *)
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdy) ?Qx =>
  change (SRr sg Wx (@cfg_at fx segs (transportb_sigma TB_spec_read_frame) rg mm mdy) Qx) end.
refine (SRF HL HC STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p by_poll pf T bytes Bw ch a
  ly2 S2 W2 (ms_mem ms1) md1 (ms_regs ms1) (Z.of_nat (length bytes)) (recv_w1 Bw) _ HFIX CUR1 BLK1 TW1
  (proj1 HREGS1) HRO1 HRA1 R10 R11 Ya2 ltac:(lia) _).
intros ly3 S3 W3 mem3 md3 regs3 CUR3 BLK3 TW3 HP3 HSF3.
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg ?pcx ?mm ?rom) ?mdy) ?Qx =>
  replace pcx with (Z_to_bv 64 (BASE + (RECV_RF + 16))) by first [exact (eq_sym R1) | exact R1] end.
(* the registers and the struct after the call *)
assert (KR3 : forall r, In r rf_keepl -> YK11.getr regs3 (Z_to_bv 5 r) = YK11.getr regs2 (Z_to_bv 5 r))
  by (intros r Hr; exact (eq_trans (HP3 r (rf_keepl_saved r Hr)) (KR1 r Hr))).
pose proof (rf_opb_of regs regs2 regs3 by_poll a bytes HREGS KR3) as HREGS3.
pose proof HREGS3 as ((T2 & _) & _).
assert (RSV : 0 <= recv_send bytes < 2 ^ 32) by exact (ARF.rf_send_range bytes).
assert (HVM3 : val_mem segs (mrestrict (w_H W3) mem3) (spZ regs - RECV_FRAME + 32) 4 (recv_send bytes)).
{ rewrite <- (rf_srf_send bytes). exact (rf_sf_send_val segs _ _ a _ HSF3). }
assert (Hsp128 : (spZ regs - RECV_FRAME) mod 16 = 0).
{ rewrite FF. replace (spZ regs - 128) with (spZ regs + (-8) * 16) by lia. rewrite Z_mod_plus_full. exact Hsp16. }
(* run 2, +0x0a8: `lw a0, 0x20(sp)`, the struct's send field; it stops at +0x0ac *)
clear HS SHOK.
pose proof (rf_entryL W3 regs3 mem3 (spZ regs - RECV_FRAME) (recv_send bytes) T2 ltac:(rewrite FF; lia)
  ltac:(rewrite FF; lia) Hsp128 RSV HVM3) as HS.
set (EA := rf_EL regs3 (recv_send bytes)) in HS.
assert (HEIA : img_env VAL A_LIM EA) by (unfold EA, rf_EL; apply Eimg_env).
assert (SHOKA : sh_ok segs (SLit 0) (@nil shent) EA (mrestrict (w_H W3) mem3)) by constructor.
assert (EEA : forall nn (rr : bv 5), Z.of_nat nn = bv_unsigned rr -> ew EA nn = YK11.getr regs3 rr)
  by (intros nn rr Hnn; unfold EA, rf_EL; apply can_ew_Eimg_Ereg_nat; exact Hnn).
assert (EA32 : ew EA 32 = Z_to_bv 64 (recv_send bytes))
  by (unfold EA, rf_EL; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs3 _ 0%nat)).
pose proof CUR3 as (HJ3 & _).
paj_run_to_tok RUNTO HS HJ3 SHOKA (0, 0) (RECV_RF + 20).
{ rf_awr0. }
rf_md md4.
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?mz) => rename mz into ms4 end.
assert (KD4 : forall x, 0 <= x < 2 ^ 64 -> aview segs (w_H W3) (ms_mem ms4) x = aview segs (w_H W3) mem3 x)
  by (rf_kept HFr).
assert (GR4 : forall x, apresent (w_H W3) mem3 x -> apresent (w_H W3) (ms_mem ms4) x)
  by (intros x Hx; exact (apresent_grows _ _ _ x HG Hx)).
clear HF HFr HG.
lazymatch type of HS with st_ok_pi _ _ ?EF _ _ => set (E4 := EF) in HS end.
assert (E4lo : forall nn, (nn < 1024)%nat -> ew E4 nn = ew EA nn)
  by (intros nn Hnn; unfold E4; repeat rewrite ew_ewset_other by lia; reflexivity).
assert (E4_32 : ew E4 32 = Z_to_bv 64 (recv_send bytes)) by (rewrite E4lo by lia; exact EA32).
rf_reg HS (Z_to_bv 5 10) (Z_to_bv 64 (bv_swrap 32 (recv_send bytes))) R10a
  ltac:(exact (AAN.annt_sext E4 32%nat (recv_send bytes) E4_32 RSV)).
assert (KR4 : forall r, In r rf_keepl -> YK11.getr (ms_regs ms4) (Z_to_bv 5 r) = YK11.getr regs3 (Z_to_bv 5 r)).
{ apply (rf_keep_regs rf_keepl E4 _ (w_H W3) ms4 regs3 HS); [rf_srget | rf_ewlo E4lo EEA]. }
pmkst HS.
rf_pc (RECV_RF + 20).
destruct (rf_cur_step STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p by_poll pf T bytes Bw ch a ly3 S3 W3
  mem3 md3 (ms_mem ms4) md4 LAWS HGX HFIX CUR3 BLK3 HJ3 (fun x Hx _ => KD4 x Hx) GR4) as [CUR4 BLK4].
assert (TW4 : tw_at TMAP_B (aview segs (w_H W3) (ms_mem ms4)) (recv_w1 Bw)).
{ apply (tw_kept TMAP_B (aview segs (w_H W3) mem3)); [exact TW3|]. intros x Hx. apply KD4.
  pose proof (TMAP_B_hull x Hx) as Hh. unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in Hh. lia. }
(* +0x0ac .. +0x0b4: the store and the branch *)
exact (rf_store STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p by_poll pf T bytes Bw ch a Bw' ly3 S3 W3
  (ms_mem ms4) md4 (ms_regs ms4) HPOLL HMRX HL HC HFIX CUR4 HRES BLK4 TW4
  (rf_opb_of regs regs3 (ms_regs ms4) by_poll a bytes HREGS3 KR4) R10a).
Qed.

End s.
