(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the entry segment of the image-A walk of libreac/fuzz_decode's LLVMFuzzerTestOneInput, with proof steps adapted from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v (pb_reac_ctrl_stamp_headamp's prologue and its class-0 stack malloc, origin/cold/pg-prog), proofs/libreac/fuzz_grant/lib/A/Prog/GrantACja.v (land_m32, denot_and_m32, sp1_facts), proofs/libreac/fuzz_grant/lib/A/Prog/GrantFrame.v (val_mem_of_rd32, rdword_of_val_mem, val_mem_moved), lib/Reusable/YCbq.v (call_effect_journal) and lib/A/Prog/YC85.v (aj_stack_malloc_atS); module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/CanKit.v, with its module names changed; 492 of its 559 lines of code are new or changed and 457 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/SrxDeskKit.v, with its module paths and module names changed; 505 of its 560 lines of code are new or changed and 504 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput_seg_recv: Lemma lc_recv_ok, the segment RECV of the image-A walk of LLVMFuzzerTestOneInput
   (lib/A/Prog/LLVMFuzzerTestOneInput_segs.v lc_recv_stmt), from the cut lc_st_recv (+0x908) to the loop tail
   lc_st_tail (+0x12ec). The code (pc = 0x81264 + offset):
     +0x908   jal receive (0x837d0), return address +0x90c: a0 = the record in the input, a1 = its length, a2 =
              by_poll, a3 = the poll flags (lc_recv_vals); receive is a G-form callee in the walk's own G journal
              (receive_cg.v transport_receive_cg at CTX_receive, the premise lp_recv);
     +0x90c   j +0x111c;
     +0x111c  mv s8, s3 (the cursor after the record);
     +0x1120  j +0x12ec, the tail.
   The kit statements the call needs are the lemma's arguments: K1 (lc_rom_view_stmt: the read-only view at the call
   memory), K5 (lc_dn_each_stmt: recv_dn_each), K6 (lc_runinv_stmt: the run invariants and g_fail_next <= 1 at the
   operation's start world) and K7 (lc_chain_stmt: the frame-pointer chain whose spine puts the call in
   CTX_receive).
   Two pieces are stated for any call site of the loop: lc_lcore_call (the loop's common facts across a G-form call
   that charges at most one receive budget and writes only bytes of G's hull) and lc_join_tail (from +0x90c or from
   +0x111c, the return of op 1's build_and_receive, through `mv s8, s3` and `j` to the tail cut). *)
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
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YG0p YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05 YImgTop YI16 YE00 YE01 YO09.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
DgnTransportSyms DgnTransportList DgnTransportAddr DgnTransportPa DgnTransportImg DgnTransportPaLib YC4b YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v Img0 AE2k ACfn.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AsanCells TransportG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
DgnTransportCg TransportGCg TransportGRwA TransportGRunA CanKit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG TWorldA TImgA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_session_tick_cg diginet_session_rx_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import send_data_cg on_announce_cg on_data_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_session_poll_cg receive_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
LLVMFuzzerTestOneInput_cg LLVMFuzzerTestOneInput_segs LLVMFuzzerTestOneInput_st.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TImg TSess0 TSess TCb TOps.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim Require Agree QueueFacts LoopOk LinksProof.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.TransportG.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
Module TOP := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TOps.
Module AG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim.Agree.
Module QF := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim.QueueFacts.
Module LOK := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim.LoopOk.
Module LP := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim.LinksProof.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* 1. The record receive is handed                                     *)
(* ------------------------------------------------------------------ *)

(* fuzz_record: the n <= 65535 bytes at off, inside D. *)
Lemma lc_record_ok : forall (D : list byte) c, QF.fuzz_in_ok D c ->
  exists c' off n, TOP.fuzz_record_m D c = (c', off, n) /\
    0 <= off /\ 0 <= n <= 65535 /\ off + n <= Z.of_nat (length D).
Proof.
intros D c Hc. unfold TOP.fuzz_record_m.
destruct (QF.fuzz_u16_ok D c Hc) as (c1 & w & E1 & Hc1 & Hw). rewrite E1.
destruct (QF.fuzz_take_ok D c1 w Hc1 ltac:(lia)) as (c2 & off & n & E2 & _ & Hn & Hoff & Hend & _).
exists c2, off, n. split; [exact E2 | lia].
Qed.

(* The values of lc_recv_vals: by_poll 0 with poll flags 0 (op 0) or by_poll 1 with a byte (op 8), and the record. *)
Lemma lc_recv_vals_ok : forall (D : list byte) c, QF.fuzz_in_ok D c ->
  ((rv_bp (lc_recv_vals D c) = 0 /\ rv_pf (lc_recv_vals D c) = 0) \/
   (rv_bp (lc_recv_vals D c) = 1 /\ 0 <= rv_pf (lc_recv_vals D c) < 256)) /\
  0 <= rv_off (lc_recv_vals D c) /\ 0 <= rv_n (lc_recv_vals D c) <= 65535 /\
  rv_off (lc_recv_vals D c) + rv_n (lc_recv_vals D c) <= Z.of_nat (length D).
Proof.
intros D c Hc. unfold lc_recv_vals.
destruct (QF.fuzz_u8_ok D c Hc) as (c1 & opb & E1 & Hc1 & _). rewrite E1. cbv beta iota zeta.
destruct (opb mod 9 =? 0).
- destruct (lc_record_ok D c1 Hc1) as (c2 & off & n & E2 & H1 & H2 & H3). rewrite E2.
  cbv beta iota zeta. cbn [rv_bp rv_pf rv_off rv_n].
  split; [left; split; reflexivity | lia].
- destruct (QF.fuzz_u8_ok D c1 Hc1) as (c2 & pf & E2 & Hc2 & Hpf). rewrite E2. cbv beta iota zeta.
  destruct (lc_record_ok D c2 Hc2) as (c3 & off & n & E3 & H1 & H2 & H3). rewrite E3.
  cbv beta iota zeta. cbn [rv_bp rv_pf rv_off rv_n].
  split; [right; split; [reflexivity | exact Hpf] | lia].
Qed.

(* The record's bytes, a sub-range of the input's garr8. *)
Lemma lc_garr8_sub : forall (m : word -> option byte) p (pl : list byte) off n,
  0 <= off -> 0 <= n -> off + n <= Z.of_nat (length pl) ->
  garr8 tfibsegs m p (map (fun b : byte => bv_unsigned b) pl) ->
  garr8 tfibsegs m (p + off) (TW.zs (TW.sub pl off (Z.to_nat n))).
Proof.
intros m p pl off n H0 H1 H2 HG.
rewrite <- (firstn_skipn (Z.to_nat off) pl) in HG. rewrite map_app in HG.
apply garr8_app in HG as [_ HG]. rewrite length_map, length_firstn in HG.
replace (Z.of_nat (Nat.min (Z.to_nat off) (length pl))) with off in HG by lia.
unfold TW.sub, TW.zs.
rewrite <- (firstn_skipn (Z.to_nat n) (skipn (Z.to_nat off) pl)) in HG. rewrite map_app in HG.
apply garr8_app in HG as [HG _]. exact HG.
Qed.

(* The operation's model equation from receive's answer, and receive's Some from the operation's. *)
Lemma lc_recv_op : forall (D : list byte) c (B0 : list byte) a (Bw' : list byte) k,
  lc_opc D c = 0 \/ lc_opc D c = 8 ->
  TOP.receive_m timg_A B0 a (TW.sub D (rv_off (lc_recv_vals D c)) (Z.to_nat (rv_n (lc_recv_vals D c))))
    (rv_bp (lc_recv_vals D c)) (rv_pf (lc_recv_vals D c)) = Some (Bw', tt) ->
  TOP.LLVMFuzzerTestOneInput_op_m timg_A B0 (fun _ => a) D c k = Some (Bw', (rv_c (lc_recv_vals D c), S k)).
Proof.
intros D c B0 a Bw' k Ho Hr. rewrite (lc_recv_eq timg_A B0 (fun _ => a) D c k Ho). cbv beta. rewrite Hr. reflexivity.
Qed.

Lemma lc_recv_some : forall (D : list byte) c (B0 : list byte) a k,
  lc_opc D c = 0 \/ lc_opc D c = 8 ->
  TOP.LLVMFuzzerTestOneInput_op_m timg_A B0 (fun _ => a) D c k <> None ->
  TOP.receive_m timg_A B0 a (TW.sub D (rv_off (lc_recv_vals D c)) (Z.to_nat (rv_n (lc_recv_vals D c))))
    (rv_bp (lc_recv_vals D c)) (rv_pf (lc_recv_vals D c)) <> None.
Proof.
intros D c B0 a k Ho Hs Hn. apply Hs. rewrite (lc_recv_eq timg_A B0 (fun _ => a) D c k Ho). cbv beta.
rewrite Hn. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* 2. receive's written range lies in G's hull                          *)
(* ------------------------------------------------------------------ *)

Local Abbreviation twa_fld := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.m_lost_cg.twa_fld.
(* The bounds of a byte of one row twa_fld o b A n: computed when the row is closed, else (an array entry at an index)
   the row's address unfolded to the index. *)
Ltac lr_fld H :=
  lazymatch type of H with
  | twa_fld _ _ (TW.A_OW_t_state _) _ _ => unfold twa_fld, TW.A_OW_t_state, TW.OW_t_ESZ, TW.OFF_OW, TA_OW in H
  | twa_fld _ _ (TC.A_OW_dn_body _) _ _ => unfold twa_fld, TC.A_OW_dn_body, TW.OFF_OW, TA_OW in H
  | twa_fld _ _ (TW.A_GOT_t_state _) _ _ => unfold twa_fld, TW.A_GOT_t_state, TW.GOT_t_ESZ, TW.OFF_GOT, TA_GOT in H
  | twa_fld _ _ (TW.A_Cmd_st _) _ _ => unfold twa_fld, TW.A_Cmd_st, TW.OFF_g_cmd, TA_g_cmd in H
  | twa_fld _ _ (TW.A_S_queue_bytes _) _ _ =>
      unfold twa_fld, TW.A_S_queue_bytes, TW.S_queue_ESZ, TW.OFF_g_s, TA_g_s in H
  | twa_fld ?o ?b ?A ?n ?x =>
      let lo := eval vm_compute in (b + (A - o)) in
      let ln := eval vm_compute in n in
      change (lo <= x < lo + ln) in H
  end.
(* Each written-range predicate unfolded down to its rows; any other predicate unfolded by its head (hnf). *)
Ltac lr_go H :=
  lazymatch type of H with
  | False => destruct H
  | _ \/ _ => let H1 := fresh "Hw" in let H2 := fresh "Hw" in destruct H as [H1 | H2]; [lr_go H1 | lr_go H2]
  | ex _ => let x := fresh "i" in let H1 := fresh "Hw" in destruct H as [x H1]; lr_go H1
  | (_ <= _ < _) /\ _ => let H1 := fresh "Hb" in let H2 := fresh "Hw" in destruct H as [H1 H2]; lr_go H2
  | _ /\ _ => let H2 := fresh "Hw" in destruct H as [_ H2]; lr_go H2
  | twa_fld _ _ _ _ _ =>
      lr_fld H; unfold TC.TRANS_MAX, TW.OW_dn_N, TC.CMDS_MAX, TW.S_queue_N, TG.G_HARNESS_LO, TG.G_HARNESS_HI in *;
      lia
  | ?T => first [progress (hnf in H) | idtac "lr_go: stuck at" T; fail 1]; lr_go H
  end.

(* Every byte some path of receive stores (receive_cg.v recv_wr) lies in G's hull. *)
Lemma lc_recv_wr_hull : forall (bytes : list byte) a, recv_wr bytes a -> TG.G_HARNESS_LO <= a < TG.G_HARNESS_HI.
Proof. intros bytes a H. unfold recv_wr in H. lr_go H. Qed.

(* G's hull lies inside one loaded segment of the image. *)
Lemma lc_hull_img : forall a, TG.G_HARNESS_LO <= a < TG.G_HARNESS_HI -> in_img tfibsegs a.
Proof.
intros a Ha.
apply (decode_seg_covers_img [(TG.G_HARNESS_LO, TG.G_HARNESS_HI - TG.G_HARNESS_LO)] a).
- vm_compute. reflexivity.
- apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* 3. The symbolic runs                                                 *)
(* ------------------------------------------------------------------ *)

Definition LR_B0 : Z * Z := (0, 0).

(* The value of register r in the machine state of a symbolic state HS. *)
Ltac lr_reg HS r v H tac :=
  lazymatch type of HS with
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok ?segsx ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_restrict_reg segsx Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | st_ok_pi ?segsx ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  end.
(* A register the run leaves as it found it (its symbolic value is its own atom n). *)
Ltac lr_keq HS EW regs r n H :=
  lr_reg HS r (YK11.getr regs r) H
    ltac:(cbn [sv_denot]; rewrite (EW n r eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
(* The write right of a run from a state with no region. *)
Ltac lr_awr :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end;
  apply awr_ok_x_nil.
(* A run from a state with no region writes no byte. *)
Ltac lr_kept HFr KR W mold msn :=
  assert (KR : forall a, 0 <= a < 2 ^ 64 -> aview tfibsegs (w_H W) (ms_mem msn) a = aview tfibsegs (w_H W) mold a);
  [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
    apply (kept_of_frame _ _ _ _ _ (fun _ : Z => False) HFr); [| exact Ha | intros []];
    let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let x := fresh "x" in
    let Hin := fresh "Hin" in let Hx := fresh "Hx" in
    intros b wlo whi x Hin Hx;
    lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end;
    cbn [In] in Hin; destruct Hin
  | ].

Section seg. Context {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XL : Z -> Z.
Variables RLO RHI : Z.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transport_listing PI_transport).
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).

Definition lr_E0 (regs : bvmap 5 word) : env := Eimg (PI := PI_transport) (Ereg regs []).

(* A state with no region, at any pc of the function. *)
Lemma lr_entry0 : forall (fx : YK11.FPState) (W : world segs) regs mem (pc : Z),
  st_ok_pi segs VAL (lr_E0 regs) (mkSS pc sr_atoms [] None (mkFacts [] [] []))
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + pc)) mem (YK11.seg_rom segs))).
Proof.
intros fx W regs mem pc. rewrite restrict_mkst_fx.
apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_nil.
- apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. exact I.
- unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. repeat split; exact I.
Qed.

(* ------------------------------------------------------------------ *)
(* 4. The loop's common facts across a run and across a call            *)
(* ------------------------------------------------------------------ *)

(* A run that writes no byte (only present bytes appear) and keeps sp, gp, tp, s0, s1, s2, s5 and s10 keeps the
   loop's common facts. *)
Lemma lc_lcore_run : forall cx op cin bin k ly' S' (W : world segs) regs' mem' md' e regs2 mem2 md2,
  @lc_lcore rc B MT cx op cin bin k ly' S' W regs' mem' md' e ->
  @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS 0 [] LLVMF_STK (lc_sp0 cx) []
    (l_ly cx) (l_S cx) (l_W cx) (l_mem cx) (l_md cx) [(LF_CID, l_fpos cx)] ly' S' W mem2 md2 e ->
  (forall a, 0 <= a < 2 ^ 64 -> aview segs (w_H W) mem2 a = aview segs (w_H W) mem' a) ->
  (forall a, apresent (w_H W) mem' a -> apresent (w_H W) mem2 a) ->
  YK11.getr regs2 2 = YK11.getr regs' 2 -> YK11.getr regs2 3 = YK11.getr regs' 3 ->
  YK11.getr regs2 4 = YK11.getr regs' 4 -> YK11.getr regs2 8 = YK11.getr regs' 8 ->
  YK11.getr regs2 9 = YK11.getr regs' 9 -> YK11.getr regs2 18 = YK11.getr regs' 18 ->
  YK11.getr regs2 21 = YK11.getr regs' 21 -> YK11.getr regs2 26 = YK11.getr regs' 26 ->
  @lc_lcore rc B MT cx op cin bin k ly' S' W regs2 mem2 md2 e.
Proof.
intros cx op cin bin k ly' S' W regs' mem' md' e regs2 mem2 md2 HL HJ2 KR GR E2 E3 E4 E8 E9 E18 E21 E26.
assert (KA : forall a, aview segs (w_H W) mem2 a = aview segs (w_H W) mem' a).
{ intros a. rewrite (aview_wrap64 segs (w_H W) mem2 a), (aview_wrap64 segs (w_H W) mem' a).
  apply KR. apply Z.mod_pos_bound. lia. }
destruct HL as (HC & (R18 & R26) & HSP & HFSH & HOPOK & He & HMET & R21).
destruct HC as (_ & Hfrs & HlyF & HPERM & Rsp & R8 & R9 & Rgp & Rtp & Hsp1 & Hsp1al & HSAV & HF4096 & HFal & HFceil &
  HFpres & HFL & HIN).
split.
{ split; [exact HJ2|]. split; [exact Hfrs|]. split; [exact HlyF|]. split; [exact HPERM|].
  split; [exact (eq_trans E2 Rsp)|]. split; [exact (eq_trans E8 R8)|]. split; [exact (eq_trans E9 R9)|].
  split; [exact (eq_trans E3 Rgp)|]. split; [exact (eq_trans E4 Rtp)|].
  split; [exact Hsp1|]. split; [exact Hsp1al|].
  split.
  { unfold lc_saved in HSAV |- *. rewrite Forall_forall in HSAV |- *. intros o Ho.
    rewrite (rdword_ext (aview segs (w_H W) mem') (aview segs (w_H W) mem2) (lc_sp0 cx - fst o))
      by (intros j _; apply KA).
    exact (HSAV o Ho). }
  split; [exact HF4096|]. split; [exact HFal|]. split; [exact HFceil|].
  split; [intros a Ha; exact (GR a (HFpres a Ha))|].
  split.
  { rewrite (rdword_ext (aview segs (w_H W) mem') (aview segs (w_H W) mem2) (lc_F cx + LF_FBYTES - 8))
      by (intros j _; apply KA).
    exact HFL. }
  destruct HIN as (HPAYg & HPAYv). split.
  - apply (lc_garr8_kept (w_H W) (w_H W) mem' mem2 (l_p cx) _ (fun j _ => KA _) HPAYg).
  - intros i Hi. rewrite KA. exact (HPAYv i Hi). }
split; [split; [exact (eq_trans E18 R18) | exact (eq_trans E26 R26)]|].
split.
{ unfold lc_spills in HSP |- *. rewrite Forall_forall in HSP |- *. intros o Ho.
  rewrite (rdword_ext (aview segs (w_H W) mem') (aview segs (w_H W) mem2) (lc_sp1 cx + fst o))
    by (intros j _; apply KA).
  exact (HSP o Ho). }
split; [exact (lc_fsh_kept cx (aview segs (w_H W) mem') (aview segs (w_H W) mem2) cin bin (fun a _ => KA a) HFSH)|].
split; [exact HOPOK|]. split; [exact He|]. split; [exact HMET|]. exact (eq_trans E21 R21).
Qed.

(* The loop's common facts across a G-form call from a cut of operation op (c and body out of scope), made at the
   realigned sp with a stack window of X bytes below it: the callee extends the walk's G journal by at most RECV_EV
   events, keeps the callee-saved registers, the frames and the blocks up to order, keeps what acall_kept_g keeps with a
   written range inside G's hull, and charges the meter at most one receive budget. The call is the operation's
   reception (S (lo_k op) receptions after it). *)
Lemma lc_lcore_call : forall cx op ly' S' (W : world segs) regs' mem' md' e (X : Z) (E : Z -> Prop) (COST : Z)
    ly2 S2 (W2 : world segs) regs2 mem2 md2 e2,
  @lp_prem rc B MT XL RLO RHI -> @lc_base rc B MT XL RLO RHI cx ->
  @lc_lcore rc B MT cx op false false (lo_k op) ly' S' W regs' mem' md' e ->
  @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS 0 [] LLVMF_STK (lc_sp0 cx) []
    (l_ly cx) (l_S cx) (l_W cx) (l_mem cx) (l_md cx) [(LF_CID, l_fpos cx)] ly2 S2 W2 mem2 md2 (e + e2) ->
  0 <= e2 <= RECV_EV ->
  aregs_preserved regs' regs2 -> frames S2 = frames S' -> Permutation (ablocks B ly2 S2) (ablocks B ly' S') ->
  acall_kept_g segs B TG.G_HARNESS ly' S' W mem' W2 mem2 (lc_sp1 cx - X) (lc_sp1 cx) E ->
  0 <= X <= LLVMF_STK - 336 ->
  (forall a, E a -> TG.G_HARNESS_LO <= a < TG.G_HARNESS_HI) ->
  mo_le MT S' S2 COST -> COST <= lf_rcost MT ->
  @lc_lcore rc B MT cx op false false (S (lo_k op)) ly2 S2 W2 regs2 mem2 md2 (e + e2).
Proof.
intros cx op ly' S' W regs' mem' md' e X E COST ly2 S2 W2 regs2 mem2 md2 e2 HP HB HL HJ2 He2 HPR Hfr2 Hperm2 HK HX
  HE Hmo Hcost.
pose proof (lp_laws _ _ _ _ _ HP) as LAWS. pose proof (lp_meter_laws _ _ _ _ _ HP) as MTL.
pose proof HL as (HC & (R18 & R26) & HSP & HFSH & HOPOK & He & HMET & R21).
pose proof HOPOK as (_ & Hops & _ & _ & Hk).
pose proof (lc_geom B MT XL RLO RHI cx ly' S' W regs' mem' md' e HB HC) as G.
destruct G as [HARg Hsp0al Hstk Hsp1c HFaddr HFin Hn HINg HLIVEg].
pose proof HC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hsp1 & _ & _ & HF4096 & _ & HFceil & _).
destruct Hstk as (Hceil & Hslo & Hshi & H47).
pose proof asan_consts as ((CVlo & CVhi) & _).
change (2 ^ 47) with 140737488355328 in H47.
unfold LF_FRAME, LF_FBYTES in *.
pose proof HK as (K1 & K2 & _ & K4 & _).
assert (KF : forall a, lc_F cx <= a < lc_F cx + 256 \/ lc_SH cx <= a < lc_SH cx + 32 ->
  aview segs (w_H W2) mem2 a = aview segs (w_H W) mem' a).
{ intros a Ha. apply (K4 LF_CID (l_fpos cx) a HFin).
  - unfold in_zr, frame_rng. cbn [fst snd]. rewrite HFaddr, lf_fbytes. unfold LF_FBYTES.
    change (256 / 8) with 32. unfold shadow_addr. unfold lc_SH in Ha. lia.
  - intros Hw. pose proof (HE a Hw) as Hh. destruct Ha as [Ha | Ha].
    + apply (frm_img segs B LAWS ly' S' W mem' md' LF_CID (l_fpos cx) a HARg HFin).
      * rewrite HFaddr, lf_fbytes. unfold LF_FBYTES. exact Ha.
      * exact (lc_hull_img a Hh).
    + unfold lc_SH, SHADOW_OFF, TG.G_HARNESS_LO, TG.G_HARNESS_HI in *.
      pose proof (Z.div_pos (lc_F cx) 8 ltac:(lia) ltac:(lia)). lia. }
assert (HC2 : @lc_core rc B cx ly2 S2 W2 regs2 mem2 md2 (e + e2)).
{ apply (lc_core_kept B MT XL RLO RHI cx ly' S' W regs' mem' md' e X ly2 S2 W2 regs2 mem2 md2 (e + e2) LAWS HB HC
    HJ2 Hfr2 Hperm2 HPR HX).
  - intros a Ha Hw. exact (K1 a Ha Hw).
  - intros b m i Hin Hi. apply (K2 b m i Hin Hi). intros Hw.
    apply (blk_img segs B LAWS ly' S' W mem' md' b m (b + i) HARg Hin ltac:(lia)).
    exact (lc_hull_img _ (HE _ Hw)).
  - intros a Ha. apply KF. unfold LF_FBYTES in Ha. exact Ha. }
split; [exact HC2|].
split; [split; [exact (lc_reg_kept regs' regs2 18 _ HPR ltac:(hnf; lia) R18)
              | exact (lc_reg_kept regs' regs2 26 _ HPR ltac:(hnf; lia) R26)]|].
split.
{ apply (lc_spills_kept cx _ (aview segs (w_H W) mem') (aview segs (w_H W2) mem2)); [| | exact HSP].
  - intros o Ho.
    pose proof (lf_spill_vals (lc_F cx) ltac:(lia) ltac:(unfold LF_FBYTES; change (2 ^ 63) with 9223372036854775808; lia))
      as SV.
    rewrite Forall_forall in SV. destruct (SV o Ho) as (_ & _ & H8 & H192). lia.
  - intros a Ha. apply K1; [change (2 ^ 64) with 18446744073709551616; unfold lc_sp0 in *; lia | lia]. }
split; [apply (lc_fsh_kept cx (aview segs (w_H W) mem')); [intros a Ha; apply KF; right; exact Ha | exact HFSH]|].
split; [exact HOPOK|].
split; [rewrite Nat2Z.inj_succ; change RECV_EV with 2 in *; lia|].
split.
{ destruct HMET as (Hle & Hok). unfold lc_meter.
  assert (R0 : 0 <= lf_rcost MT).
  { unfold lf_rcost. pose proof (mo_malloc_nonneg MT MTL 65535 ltac:(lia)). pose proof (mo_free_nonneg MT MTL). lia. }
  rewrite Nat2Z.inj_succ.
  set (K := Z.of_nat (lo_k op)) in *.
  assert (HK1 : K + 1 <= TC.OPS_MAX) by lia.
  split.
  - apply (mle_weaken MT (l_S cx) S2 (K * lf_rcost MT + COST)); [exact MTL | |].
    + exact (mle_station MT (l_S cx) S' S2 _ _ MTL Hle Hmo).
    + rewrite Z.mul_succ_l. lia.
  - apply (mok_station MT S' S2 ((TC.OPS_MAX - K) * lf_rcost MT) COST); [exact MTL | exact Hok | exact Hmo | |].
    + apply Z.mul_nonneg_nonneg; lia.
    + replace ((TC.OPS_MAX - K) * lf_rcost MT) with ((TC.OPS_MAX - Z.succ K) * lf_rcost MT + lf_rcost MT) by ring.
      lia. }
exact (lc_reg_kept regs' regs2 21 _ HPR ltac:(hnf; lia) R21).
Qed.

(* ------------------------------------------------------------------ *)
(* 5. The join: `mv s8, s3` and `j` to the tail                          *)
(* ------------------------------------------------------------------ *)

(* At +0x90c (the return of receive, then `j +0x111c`) or +0x111c (the return of op 1's build_and_receive): the tail
   cut's facts but for the cursor, which s3 / s7 hold. *)
Definition lc_st_join (cx : lcx) (op : lop) (o : Z) : world segs -> config -> Prop :=
  fun W' c' => exists ly' S' regs' mem' md' e a Bw cn k',
    c' = lc_cfg cx o regs' mem' md' /\
    @lc_lcore rc B MT cx op false false k' ly' S' W' regs' mem' md' e /\
    recv_addr_ok a /\
    TOP.LLVMFuzzerTestOneInput_op_m timg_A (lo_B op) (fun _ => a) (l_pl cx) (lo_c op) (lo_k op) = Some (Bw, (cn, k')) /\
    lc_tw W' mem' Bw /\
    lc_cur cx regs' 19 23 cn /\
    YK11.getr regs' 20 = w64 LF_S4 /\ YK11.getr regs' 22 = w64 7.

Lemma lc_join_tail : forall cx op o (W : world segs) c,
  @lp_prem rc B MT XL RLO RHI -> (o = 0x90c \/ o = 0x111c) -> lc_st_join cx op o W c ->
  SRr segs W c (@lc_st_tail rc B MT cx op).
Proof.
intros cx op o W c HP Ho HJN.
destruct HJN as (ly' & S' & regs' & mem' & md' & e & a & Bw & cn & k' & -> & HL & Ha & Hop & Htw & (R19 & R23) & R20 &
  R22).
pose proof HL as ((HJ & _) & _).
pose proof (lp_laws _ _ _ _ _ HP) as LAWS.
pose proof (G_HARNESS_gx_ok B (lp_g_unowned _ _ _ _ _ HP)) as HGX.
pose proof (@paj_run_to_x (l_fx cx) rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS
  HGX 0 []) as RUNTO.
assert (POST : forall regs2 mem2 md2,
  @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS 0 [] LLVMF_STK (lc_sp0 cx) []
    (l_ly cx) (l_S cx) (l_W cx) (l_mem cx) (l_md cx) [(LF_CID, l_fpos cx)] ly' S' W mem2 md2 e ->
  (forall x, 0 <= x < 2 ^ 64 -> aview segs (w_H W) mem2 x = aview segs (w_H W) mem' x) ->
  (forall x, apresent (w_H W) mem' x -> apresent (w_H W) mem2 x) ->
  YK11.getr regs2 2 = YK11.getr regs' 2 -> YK11.getr regs2 3 = YK11.getr regs' 3 ->
  YK11.getr regs2 4 = YK11.getr regs' 4 -> YK11.getr regs2 8 = YK11.getr regs' 8 ->
  YK11.getr regs2 9 = YK11.getr regs' 9 -> YK11.getr regs2 18 = YK11.getr regs' 18 ->
  YK11.getr regs2 21 = YK11.getr regs' 21 -> YK11.getr regs2 26 = YK11.getr regs' 26 ->
  YK11.getr regs2 20 = YK11.getr regs' 20 -> YK11.getr regs2 22 = YK11.getr regs' 22 ->
  YK11.getr regs2 23 = YK11.getr regs' 23 -> YK11.getr regs2 24 = YK11.getr regs' 19 ->
  @lc_st_tail rc B MT cx op W (lc_cfg cx LO_TAIL regs2 mem2 md2)).
{ intros regs2 mem2 md2 HJ2 KR GR E2 E3 E4 E8 E9 E18 E21 E26 E20 E22 E23 E24.
  exists ly', S', regs2, mem2, md2, e, a, Bw, cn, k'.
  split; [reflexivity|].
  split; [exact (lc_lcore_run cx op false false k' ly' S' W regs' mem' md' e regs2 mem2 md2 HL HJ2 KR GR
                  E2 E3 E4 E8 E9 E18 E21 E26)|].
  split; [exact Ha|]. split; [exact Hop|].
  split.
  { unfold lc_tw in *. apply (tw_kept TMAP_A (aview segs (w_H W) mem')); [exact Htw|].
    intros x Hx. pose proof (TMAP_A_hull x Hx) as Hh. unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh.
    apply KR. lia. }
  split; [split; [exact (eq_trans E24 R19) | exact (eq_trans E23 R23)]|].
  split; [exact (eq_trans E20 R20) | exact (eq_trans E22 R22)]. }
pose proof (lr_entry0 (l_fx cx) W regs' mem' o) as HS.
set (E := lr_E0 regs') in HS.
assert (HEI : img_env VAL A_LIM E) by (unfold E, lr_E0; apply Eimg_env).
assert (EW : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = YK11.getr regs' r)
  by (intros n r Hn; unfold E, lr_E0; apply can_ew_Eimg_Ereg_nat; exact Hn).
assert (SHOK : sh_ok segs (SLit 0) (@nil shent) E (mrestrict (w_H W) mem')) by constructor.
unfold lc_cfg.
lazymatch goal with |- SRr _ ?Wx _ ?Q =>
  change (SRr segs Wx (mkCfg (@YK11.mkst (l_fx cx) regs' (Z_to_bv 64 (BASE + o)) mem' (YK11.seg_rom segs)) md') Q) end.
destruct Ho as [-> | ->].
- paj_run_to_tok RUNTO HS HJ SHOK LR_B0 LO_TAIL.
  { lr_awr. }
  lr_kept HFr KR W mem' ms.
  assert (GR : forall x, apresent (w_H W) mem' x -> apresent (w_H W) (ms_mem ms) x)
    by (intros x Hx; exact (apresent_grows _ _ _ x HG Hx)).
  lr_keq HS EW regs' (2%bv : bv 5) 2%nat Q2. lr_keq HS EW regs' (3%bv : bv 5) 3%nat Q3.
  lr_keq HS EW regs' (4%bv : bv 5) 4%nat Q4. lr_keq HS EW regs' (8%bv : bv 5) 8%nat Q8.
  lr_keq HS EW regs' (9%bv : bv 5) 9%nat Q9. lr_keq HS EW regs' (18%bv : bv 5) 18%nat Q18.
  lr_keq HS EW regs' (21%bv : bv 5) 21%nat Q21. lr_keq HS EW regs' (26%bv : bv 5) 26%nat Q26.
  lr_keq HS EW regs' (20%bv : bv 5) 20%nat Q20. lr_keq HS EW regs' (22%bv : bv 5) 22%nat Q22.
  lr_keq HS EW regs' (23%bv : bv 5) 23%nat Q23.
  lr_reg HS (24%bv : bv 5) (YK11.getr regs' (19%bv : bv 5)) Q24
    ltac:(cbn [sv_denot]; rewrite (EW 19%nat 19%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  pmkst HS.
  apply SRr_ret.
  exact (POST (ms_regs ms) (ms_mem ms) _ HJ KR GR Q2 Q3 Q4 Q8 Q9 Q18 Q21 Q26 Q20 Q22 Q23 Q24).
- paj_run_to_tok RUNTO HS HJ SHOK LR_B0 LO_TAIL.
  { lr_awr. }
  lr_kept HFr KR W mem' ms.
  assert (GR : forall x, apresent (w_H W) mem' x -> apresent (w_H W) (ms_mem ms) x)
    by (intros x Hx; exact (apresent_grows _ _ _ x HG Hx)).
  lr_keq HS EW regs' (2%bv : bv 5) 2%nat Q2. lr_keq HS EW regs' (3%bv : bv 5) 3%nat Q3.
  lr_keq HS EW regs' (4%bv : bv 5) 4%nat Q4. lr_keq HS EW regs' (8%bv : bv 5) 8%nat Q8.
  lr_keq HS EW regs' (9%bv : bv 5) 9%nat Q9. lr_keq HS EW regs' (18%bv : bv 5) 18%nat Q18.
  lr_keq HS EW regs' (21%bv : bv 5) 21%nat Q21. lr_keq HS EW regs' (26%bv : bv 5) 26%nat Q26.
  lr_keq HS EW regs' (20%bv : bv 5) 20%nat Q20. lr_keq HS EW regs' (22%bv : bv 5) 22%nat Q22.
  lr_keq HS EW regs' (23%bv : bv 5) 23%nat Q23.
  lr_reg HS (24%bv : bv 5) (YK11.getr regs' (19%bv : bv 5)) Q24
    ltac:(cbn [sv_denot]; rewrite (EW 19%nat 19%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  pmkst HS.
  apply SRr_ret.
  exact (POST (ms_regs ms) (ms_mem ms) _ HJ KR GR Q2 Q3 Q4 Q8 Q9 Q18 Q21 Q26 Q20 Q22 Q23 Q24).
Qed.

(* ------------------------------------------------------------------ *)
(* 6. The segment                                                       *)
(* ------------------------------------------------------------------ *)

Lemma lc_recv_ok (K1 : @lc_rom_view_stmt rc B MT XL RLO RHI) (K5 : lc_dn_each_stmt) (K6 : lc_runinv_stmt)
    (K7 : @lc_chain_stmt rc B MT XL RLO RHI) : @lc_recv_stmt rc B MT XL RLO RHI.
Proof.
unfold lc_recv_stmt. intros HP cx op W c HB HST.
destruct HST as (ly' & S' & regs' & mem' & md' & e & HST). cbv zeta in HST.
destruct HST as (-> & Hopc & HL & Htw & R10 & R11 & R12 & R13 & (R19 & R23) & R20 & R22).
set (D := l_pl cx) in *.
pose proof HL as (HC & (R18 & R26) & HSP & HFSH & HOPOK & He & HMET & R21).
pose proof HOPOK as (HAG & Hops & Hcin & Hcn & Hk).
destruct (lc_recv_vals_ok D (lo_c op) Hcin) as (Hbp & Hoff & Hrn & Hend).
set (rv := lc_recv_vals D (lo_c op)) in *.
set (bytes := TW.sub D (rv_off rv) (Z.to_nat (rv_n rv))).
assert (Hlen : Z.of_nat (length bytes) = rv_n rv)
  by (unfold bytes; rewrite (QF.length_sub_D D (rv_off rv) (rv_n rv)) by lia; lia).
pose proof (lp_laws _ _ _ _ _ HP) as LAWS.
pose proof (lp_meter_laws _ _ _ _ _ HP) as MTL.
pose proof (G_HARNESS_gx_ok B (lp_g_unowned _ _ _ _ _ HP)) as HGX.
pose proof HC as (HJ & Hfrs & _ & _ & R2 & R8 & R9 & R3 & R4 & Hsp1 & Hsp1al & _).
pose proof (lc_geom B MT XL RLO RHI cx ly' S' W regs' mem' md' e HB HC) as G.
destruct G as [HARg Hsp0al Hstk Hsp1c HFaddr HFin Hn HINg HLIVEg].
destruct Hstk as (Hceil & Hslo & Hshi & H47).
pose proof asan_consts as ((CVlo & CVhi) & _).
change (2 ^ 47) with 140737488355328 in H47.
unfold LF_FRAME in Hsp1.
(* the model: receive answers at every address the malloc can return *)
assert (HMOD : forall a, recv_addr_ok a -> TOP.receive_m timg_A (lo_B op) a bytes (rv_bp rv) (rv_pf rv) <> None).
{ intros a (Ha1 & Ha2).
  destruct (LOK.op_ok LP.links_holds timg_A (lo_ops op) (lo_B op) (fun _ => a) D (lo_c op) (lo_k op) HAG Hops Hcin Hcn
    Ha1 Ha2) as (B' & c' & k'' & E' & _).
  exact (lc_recv_some D (lo_c op) (lo_B op) a (lo_k op) Hopc ltac:(rewrite E'; discriminate)). }
(* the run invariants and receive's invariant (3) at the operation's start world *)
destruct (K6 (lo_ops op) (lo_B op) HAG) as (I1 & I2 & I3 & I4 & I5 & I6 & I7 & Hgf).
assert (Hdn : recv_dn_each timg_A (lo_B op) bytes (rv_bp rv) (rv_pf rv))
  by (apply (K5 (lo_ops op) (lo_B op) bytes (rv_bp rv) (rv_pf rv) HAG Hops); lia).
(* the events, the live bytes and the meter *)
pose proof HB as HB2. unfold lc_base, tfib_lib_pre_x in HB2.
destruct HB2 as (_ & _ & _ & _ & _ & _ & _ & _ & Hev & _).
pose proof transport_llvmf_events_ok as HEV. unfold transport_llvmf_events in HEV.
assert (PEV : st_nev (l_S cx) + e + RECV_EV <= EV_MAX) by (change RECV_EV with 2 in *; lia).
assert (PLIVE : blocks_bytes S' + RECV_LIVE <= LIVE_MAX) by (unfold RECV_LIVE, LIVE_LIB in *; lia).
pose proof HMET as (Hmle & Hmok).
assert (R0 : 0 <= lf_rcost MT).
{ unfold lf_rcost. pose proof (mo_malloc_nonneg MT MTL 65535 ltac:(lia)). pose proof (mo_free_nonneg MT MTL). lia. }
assert (Hcost : recv_cost MT (Z.of_nat (length bytes)) <= lf_rcost MT).
{ unfold recv_cost, lf_rcost. rewrite Hlen.
  pose proof (mo_malloc_mono MT MTL (Z.max 1 (rv_n rv)) 65535 ltac:(lia)). lia. }
assert (PCOST : recv_cost MT (Z.of_nat (length bytes)) <= (TC.OPS_MAX - Z.of_nat (lo_k op)) * lf_rcost MT).
{ assert (H1 : 1 <= TC.OPS_MAX - Z.of_nat (lo_k op)) by lia.
  pose proof (Z.mul_le_mono_nonneg_r 1 (TC.OPS_MAX - Z.of_nat (lo_k op)) (lf_rcost MT) R0 H1). lia. }
(* ---- +0x908: jal receive ---- *)
pose proof (@paj_run_x (l_fx cx) rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS
  HGX 0 []) as RUN.
pose proof (lr_entry0 (l_fx cx) W regs' mem' LO_RECV) as HS.
set (E := lr_E0 regs') in HS.
assert (HEI : img_env VAL A_LIM E) by (unfold E, lr_E0; apply Eimg_env).
assert (EW : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = YK11.getr regs' r)
  by (intros n r Hn0; unfold E, lr_E0; apply can_ew_Eimg_Ereg_nat; exact Hn0).
assert (SHOK : sh_ok segs (SLit 0) (@nil shent) E (mrestrict (w_H W) mem')) by constructor.
unfold lc_cfg.
lazymatch goal with |- SRr _ ?Wx _ ?Q =>
  change (SRr segs Wx (mkCfg (@YK11.mkst (l_fx cx) regs' (Z_to_bv 64 (BASE + LO_RECV)) mem' (YK11.seg_rom segs)) md')
    Q) end.
paj_run_tok RUN HS HJ SHOK LR_B0.
{ lr_awr. }
lr_kept HFr KC W mem' ms.
assert (GC : forall x, apresent (w_H W) mem' x -> apresent (w_H W) (ms_mem ms) x)
  by (intros x Hx; exact (apresent_grows _ _ _ x HG Hx)).
lr_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 2316)) C1 ltac:(apply codeptr_val; exact HEI).
lr_keq HS EW regs' (2%bv : bv 5) 2%nat C2. lr_keq HS EW regs' (3%bv : bv 5) 3%nat C3.
lr_keq HS EW regs' (4%bv : bv 5) 4%nat C4. lr_keq HS EW regs' (8%bv : bv 5) 8%nat C8.
lr_keq HS EW regs' (9%bv : bv 5) 9%nat C9. lr_keq HS EW regs' (10%bv : bv 5) 10%nat C10.
lr_keq HS EW regs' (11%bv : bv 5) 11%nat C11. lr_keq HS EW regs' (12%bv : bv 5) 12%nat C12.
lr_keq HS EW regs' (13%bv : bv 5) 13%nat C13. lr_keq HS EW regs' (18%bv : bv 5) 18%nat C18.
lr_keq HS EW regs' (19%bv : bv 5) 19%nat C19. lr_keq HS EW regs' (20%bv : bv 5) 20%nat C20.
lr_keq HS EW regs' (21%bv : bv 5) 21%nat C21. lr_keq HS EW regs' (22%bv : bv 5) 22%nat C22.
lr_keq HS EW regs' (23%bv : bv 5) 23%nat C23. lr_keq HS EW regs' (26%bv : bv 5) 26%nat C26.
pmkst HS.
lazymatch goal with |- SRr _ _ (mkCfg (@YK11.mkst _ ?rg _ ?mm _) ?mdx) _ =>
  set (regsC := rg) in *; set (memC := mm) in *; set (mdC := mdx) in * end.
(* the loop's facts at the call *)
assert (HLC : @lc_lcore rc B MT cx op false false (lo_k op) ly' S' W regsC memC mdC e)
  by exact (lc_lcore_run cx op false false (lo_k op) ly' S' W regs' mem' md' e regsC memC mdC HL HJ KC GC
              C2 C3 C4 C8 C9 C18 C21 C26).
pose proof HLC as (HCC & _).
pose proof HCC as (HJC & _).
assert (USPC : spZ regsC = lc_sp1 cx)
  by (unfold spZ; rewrite C2, R2; unfold w64; apply unsigned_lit_small; lia).
assert (S0C : s0Z regsC = lc_sp0 cx)
  by (unfold s0Z; rewrite C8, R8; unfold w64; apply unsigned_lit_small; unfold lc_sp0 in *; lia).
assert (RAC : raZ regsC = 0x81b70) by (unfold raZ; rewrite C1; vm_compute; reflexivity).
pose proof (K1 HP cx ly' S' W regsC memC mdC e HB HCC) as PROM.
destruct (K7 HP cx ly' S' W regsC memC mdC e HB HCC) as (ch & Hch & Hspine).
assert (Pgarr : garr8 segs (mrestrict (w_H W) memC) (l_p cx + rv_off rv) (TW.zs bytes)).
{ pose proof HCC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (HPAYg & _)).
  exact (lc_garr8_sub (mrestrict (w_H W) memC) (l_p cx) D (rv_off rv) (rv_n rv) Hoff (proj1 Hrn) Hend HPAYg). }
assert (Psrc : (0 < length bytes)%nat ->
  trans_src_ok B ly' S' W memC (l_p cx + rv_off rv) (Z.of_nat (length bytes)) /\
  decode_off_win regsC RECV_STK (l_p cx + rv_off rv) (Z.of_nat (length bytes))).
{ intros Hpos. destruct Hn as (Hn1 & Hnl). fold D in Hnl.
  assert (Hn0 : 0 < l_n cx) by lia.
  pose proof (HINg Hn0) as Hin.
  destruct (al_blocks _ _ LAWS ly' S' W mem' md' (l_p cx) (l_n cx) HARg Hin) as (_ & H4096 & Hce & _ & _ & _ & Hnb).
  pose proof (req_size_pos (l_n cx) (proj1 Hnb)) as [_ Hreq].
  rewrite Hlen. split.
  - left. exists (l_p cx), (l_n cx). split; [exact Hin | lia].
  - left. rewrite USPC. change RECV_STK with 16448. lia. }
assert (Ptw : tw_at TMAP_A (aview segs (w_H W) memC) (lo_B op)).
{ unfold lc_tw in Htw. apply (tw_kept TMAP_A (aview segs (w_H W) mem')); [exact Htw|].
  intros x Hx. pose proof (TMAP_A_hull x Hx) as Hh. unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh. apply KC. lia. }
assert (PC5 : count_cid POLL_CID (frames S') + 1 < fs_frames POLL_CID) by (rewrite Hfrs; vm_compute; reflexivity).
assert (PC1 : count_cid SRX_CID (frames S') < fs_frames SRX_CID) by (rewrite Hfrs; vm_compute; reflexivity).
assert (PC4 : count_cid ONANN_CID (frames S') < fs_frames ONANN_CID) by (rewrite Hfrs; vm_compute; reflexivity).
assert (PC0 : count_cid SENDDATA_CID (frames S') < fs_frames SENDDATA_CID) by (rewrite Hfrs; vm_compute; reflexivity).
assert (PC2 : count_cid ONDATA_CID (frames S') + 2 < fs_frames ONDATA_CID) by (rewrite Hfrs; vm_compute; reflexivity).
(* +0x908: receive *)
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (mkCfg (@YK11.mkst (l_fx cx) rg (Z_to_bv 64 (transport_sigma TS_receive)) mm rom) mdx) Q) end.
eapply SRr_bind.
{ exact (lp_recv _ _ _ _ _ HP (l_fx cx) LLVMF_STK (lc_sp0 cx) _ (l_ly cx) (l_S cx) (l_W cx) (l_mem cx) (l_md cx)
    [(LF_CID, l_fpos cx)] ly' S' W memC mdC e regsC (l_p cx + rv_off rv) (rv_bp rv) (rv_pf rv)
    ((TC.OPS_MAX - Z.of_nat (lo_k op)) * lf_rcost MT) bytes (lo_B op) ch
    HJC
    ltac:(rewrite C1; apply (ret_ok_codeptr_v (PI := PI_transport)); [lia | reflexivity])
    ltac:(rewrite RAC; lia)
    (eq_trans C3 R3) (eq_trans C4 R4) (eq_trans C10 R10)
    ltac:(rewrite C11, R11, Hlen; reflexivity)
    (eq_trans C12 R12)
    ltac:(rewrite C13, R13; unfold w64; rewrite unsigned_lit_small by lia; apply Z.mod_small; lia)
    ltac:(rewrite USPC, S0C; exact Hch)
    ltac:(rewrite RAC, ctx_receive_at; destruct Hspine as [Hsp | Hsp]; rewrite Hsp;
          [left; reflexivity | right; left; reflexivity])
    ltac:(rewrite USPC; pose proof (Z.div_mod (lc_sp1 cx) 32 ltac:(lia)) as Dm;
          rewrite Hsp1al, Z.add_0_r in Dm; rewrite Dm;
          replace (32 * (lc_sp1 cx / 32)) with ((2 * (lc_sp1 cx / 32)) * 16) by ring; apply Z.mod_mul; lia)
    ltac:(rewrite USPC; change RECV_STK with 16448; unfold LLVMF_STK; lia)
    ltac:(rewrite USPC; lia)
    ltac:(lia) ltac:(lia) ltac:(rewrite Hlen; lia)
    Pgarr Psrc Ptw Hgf HMOD PROM I1 I2 I3 I4 I5 I6 I7 Hdn PC5 PC1 PC4 PC0 PC2 PEV PLIVE Hmok PCOST). }
cbv beta. intros W3 c3 _ HPOST.
unfold transport_recv_post, transport_cg_post in HPOST. cbv beta in HPOST.
destruct HPOST as (ly3 & S3 & regs3 & mem3 & md3 & e3 & -> & He3 & HJ3 & HP3 & Hfr3 & Hperm3 & HK3 & Hmo3 &
  (a & Bw' & Haok & Hrm & Htw3 & Hgf3)).
rewrite USPC in HK3.
assert (HL3 : @lc_lcore rc B MT cx op false false (S (lo_k op)) ly3 S3 W3 regs3 mem3 md3 (e + e3))
  by exact (lc_lcore_call cx op ly' S' W regsC memC mdC e RECV_STK (recv_wr bytes)
              (recv_cost MT (Z.of_nat (length bytes))) ly3 S3 W3 regs3 mem3 md3 e3 HP HB HLC HJ3 He3 HP3 Hfr3 Hperm3
              HK3 ltac:(change RECV_STK with 16448; unfold LLVMF_STK; lia) (lc_recv_wr_hull bytes) Hmo3 Hcost).
(* +0x90c .. +0x1120: the join *)
rewrite C1.
apply (lc_join_tail cx op 0x90c W3 _ HP (or_introl eq_refl)).
exists ly3, S3, regs3, mem3, md3, (e + e3), a, Bw', (rv_c rv), (S (lo_k op)).
split; [reflexivity|].
split; [exact HL3|].
split; [exact Haok|].
split; [exact (lc_recv_op D (lo_c op) (lo_B op) a Bw' (lo_k op) Hopc Hrm)|].
split; [exact Htw3|].
split; [split; [exact (lc_reg_kept regsC regs3 19 _ HP3 ltac:(hnf; lia) (eq_trans C19 R19))
              | exact (lc_reg_kept regsC regs3 23 _ HP3 ltac:(hnf; lia) (eq_trans C23 R23))]|].
split; [exact (lc_reg_kept regsC regs3 20 _ HP3 ltac:(hnf; lia) (eq_trans C20 R20))
      | exact (lc_reg_kept regsC regs3 22 _ HP3 ltac:(hnf; lia) (eq_trans C22 R22))].
Qed.

End seg.
